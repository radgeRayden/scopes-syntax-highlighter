using import enum
using import Array
using import itertools

inline sanitize-scope (scope prefix-patterns...)
    fold (scope = scope) for k v in scope
        k as:= Symbol
        key-name := (k as string)

        let new-name =
            va-lfold key-name
                inline (__ignore pattern computed-name)
                    let match? start count = ('match? pattern key-name)
                    if match?
                        # just remove the prefix (we assume pattern always matches start of line)
                        rslice key-name count
                    else
                        computed-name
                prefix-patterns...

        if (new-name == key-name)
            scope
        else
            'bind scope (Symbol new-name) v

# --------------------------------------------------------------------------------------------------
# let argc argv = (launch-args)
# let compiler-name = (argv @ i)
# for i in (range argc)
#     print (string (argv @ i))

load-library "libphysfs.so"
let physfs =
    do
        let scope = (sanitize-scope ((include "physfs.h") . extern) "PHYSFS_")
        'bind scope 'displayLastError
            spice-quote
                fn "displayLastError" ()
                    let physfs = [scope]
                    let code = (physfs.getLastErrorCode)
                    print (string (physfs.getErrorByCode code))
run-stage;

physfs.init "scopes"

# for now I'll just hardcode this very file, and worry about argparsing later.
let file-path = module-path
let has-dir match-start match-end = ('match? "(.+/)+" file-path)
let directory filename =
    if has-dir
        _ (lslice file-path match-end) (rslice file-path match-end)
    else
        _ "." file-path

physfs.mount directory
    "/"  # mount to "root" of virtual filesystem
    true # append to path

# TODO: error checking yadda yadda
let file-handle = (physfs.openRead filename)
let file-length = ((physfs.fileLength file-handle) as usize)
let text-buffer = (malloc-array i8 file-length)
physfs.readBytes file-handle text-buffer file-length

let text = (string text-buffer file-length)
free text-buffer

let code =
    (sc_parse_from_string text) as list


fn flatten-list (l)
    fn flatten-list (old-list new-list)
        returning list
        let at next = (decons old-list)
        atT := ('typeof at)
        next as:= list
        let new-list =
            if (atT == list)
                # go deeper
                this-function (at as list) new-list
            else
                cons at new-list
        if (not (empty? next))
            this-function next new-list
        else
            new-list

    'reverse (flatten-list l '())

let code =
    do
        # flat list -> ValueArray
        local code-array : (Array Value)
        let flattened-code = (flatten-list code)
        let at next = (decons flattened-code)
        loop (at next = at next)
            next as:= list
            'append code-array at
            if (empty? next)
                break;
            decons next
        code-array

inline lines (text-buffer)
    Generator
        inline "start" ()
            let match? start end = ('match? "^.*(\\n|$)" text-buffer)
            _ start end
        inline "valid?" (sol eol)
            sol < (countof text-buffer)
        inline "at" (sol eol)
            slice text-buffer sol eol
        inline "next" (sol eol)
            let str = (rslice text-buffer eol)
            let match? start end = ('match? "^.*(\\n|$)" str)
            # must add offset from previous line
            _ (eol + start) (eol + end)

enum HighlightingStyle plain
    Default
    Keyword
    Operator
    Function
    SugarMacro
    SpiceMacro
    Comment
    String
    Number
    Type
    SpecialConstant
    GlobalSymbol
    Symbol

using import struct
struct HighlightedText
    style : HighlightingStyle
    content : string

'define-symbols Anchor
    line = sc_anchor_lineno
    column = sc_anchor_column


struct CommentState plain
    mid-comment? : bool
    offset : i32

let number-regexp1 number-regexp2 number-regexp3 =
    do
        hex-digit := "[0-9a-fA-F]"
        bin-digit := "[01]"
        oct-digit := "[0-7]"
        fn re-or (...)
            let result =
            .. "("
                va-lifold ""
                    inline (index _. value computed-result)
                        if (index < ((va-countof ...) - 1))
                            .. computed-result value "|"
                        else
                            .. computed-result value
                    ...
                ")"

        fn number-dot-number (prefix class)
            let class+ = (class .. "+")
            .. prefix (re-or (class+ .. "\\.") ("\\." .. class+) (.. class+ "\\." class+))
        # had to split in three parts because it was too big for the engine
        let number-regexp1 =
            .. "^[+-]?"
                # no fractional part
                (..
                    (re-or
                        "\\d+"
                        (.. "0b" bin-digit "+")
                        (.. "0o" oct-digit "+")
                        (.. "0x" hex-digit "+"))
                    "(\\:"
                            (re-or
                                ("f" .. (re-or "32" "64"))
                                ("[ui]" .. (re-or "8" "16" "32" "64"))
                                "usize") ")?")
                # token interrupting characters
                "(?=[,'()\\[\\]{} \\n]|$)"
        # floats with fractional part
        let number-regexp2 =
            .. "^[+-]?"
                (..
                    (re-or
                       (number-dot-number "" "\\d")
                       (number-dot-number "0b" bin-digit))
                   "([eE][+-]\\d+)?"
                   (re-or ":f32" ":f64") "?")
                "(?=[,'()\\[\\]{} \\n]|$)"
        let number-regexp3 =
            .. "^[+-]?"
                (..
                    (re-or
                       (number-dot-number "0o" oct-digit)
                       (number-dot-number "0x" hex-digit))
                   "([eE][+-]\\d+)?"
                   (re-or ":f32" ":f64") "?")
                "(?=[,'()\\[\\]{} \\n]|$)"
        _ number-regexp1 number-regexp2 number-regexp3

fn symbol->style (symbol)
    let symbols = (import .scopes-std-symbols.symbols)
    imply symbol Symbol
    inline has-symbol? (scope)
        try
            ('@ scope symbol)
            true
        except (ex)
            false
    if (has-symbol? symbols.keywords)
        HighlightingStyle.Keyword
    elseif (has-symbol? symbols.functions)
        HighlightingStyle.Function
    elseif (has-symbol? symbols.operators)
        HighlightingStyle.Operator
    elseif (has-symbol? symbols.types)
        HighlightingStyle.Type
    elseif (has-symbol? symbols.sugar-macros)
        HighlightingStyle.SugarMacro
    elseif (has-symbol? symbols.spice-macros)
        HighlightingStyle.SpiceMacro
    elseif (has-symbol? symbols.global-symbols)
        HighlightingStyle.GlobalSymbol
    elseif (has-symbol? symbols.special-constants)
        HighlightingStyle.SpecialConstant
    else
        HighlightingStyle.Default

enum HighlightingMode
    Default
    Comment :
        offset = i32;
    MultilineString :
        offset = i32;
    OpenBracket # unused for now
    inline __typecall (cls)
        this-type.Default;

# now we walk through the actual text
local result : (Array HighlightedText)
fold (lines-highlighted tokens-highlighted mode = 0 0 (HighlightingMode.Default)) for line in (lines text)
    # check if we must break a comment or multiline string
    inline broke-indentation? (offset starter-pattern)
        imply starter-pattern string
        let regexp = (.. "^\\s*(?=[^\\s\\n])(?!" starter-pattern ")")
        let match? start end = ('match? regexp line)
        if match?
            end < offset
        else
            false

    :: skip-line
    dispatch mode
    case Comment (offset)
        if (not (broke-indentation? offset "#"))
            'append result
                HighlightedText
                    content = line
                    style = HighlightingStyle.Comment
            merge skip-line
                lines-highlighted + 1
                tokens-highlighted
                HighlightingMode.Comment offset
    case MultilineString (offset)
        if (not (broke-indentation? offset "\"{4}"))
            'append result
                HighlightedText
                    content = line
                    style = HighlightingStyle.String
            merge skip-line
                lines-highlighted + 1
                tokens-highlighted
                HighlightingMode.MultilineString offset
    default
        ;

    let tokens-this-line last-point =
        loop (tokens-this-line last-point = 0 1:usize)
            let index = (tokens-highlighted + tokens-this-line)
            if (index >= (countof code))
                break tokens-this-line last-point
            let current-token = (code @ index)
            anchor := ('anchor current-token)
            line-number := ('line anchor)
            column := ('column anchor)
            column-index := (column - 1)
            line-highlight-point := (lines-highlighted + 1)

            if (line-number > line-highlight-point)
                # continue on the next line
                break tokens-this-line last-point

            if ('none? current-token)
                # it seems empty function arg gets a weird anchor so lets just skip it.
                repeat (tokens-this-line + 1) last-point

            assert (line-highlight-point <= line-number) # did we skip too much outside this loop?
            # now that we know we're on the right line, we can slice away what we want
            # append whitespace or whatever else there is between last token and current
            if (column > last-point)
                'append result
                    HighlightedText
                        content = (slice line (last-point - 1) (column - 1))
                        style = HighlightingStyle.Default

            let tokenT = ('typeof current-token)
            if (tokenT == Symbol)
                switch (current-token as Symbol)
                case 'sugar-quote
                    if ((line @ column-index) == 39:i8) # ' character
                        # what if it's a quoted list?
                        if ((line @ (column-index + 1)) == 40:i8) # ( character
                            'append result
                                HighlightedText
                                    content = "'"
                                    style = HighlightingStyle.Keyword
                            _ (tokens-this-line + 1) ((column + 1) as usize)
                        else
                            # FIXME: caution! content could have ended with sugar quote!
                            assert ((index + 1) < (countof code))
                            let next-token = (code @ (index + 1))
                            'append result
                                HighlightedText
                                    content = (.. "'" (tostring next-token))
                                    style = HighlightingStyle.Symbol
                            _ (tokens-this-line + 2) (column + 1 + (countof (tostring next-token)))
                    else
                        'append result
                            HighlightedText
                                content = "sugar-quote"
                                style = (symbol->style (current-token as Symbol))
                        _ (tokens-this-line + 1) (column + (countof (tostring current-token)))

                pass 'spice-quote
                pass 'square-list
                pass 'curly-list
                do
                    let alias-character =
                        switch (current-token as Symbol)
                        case 'spice-quote 96:i8 # `
                        case 'square-list 91:i8 # [
                        case 'curly-list 123:i8 # {
                        default (assert false) 0:i8
                    # I wanted style to always be "keyword" but then I need to match brackets.
                    # Maybe next time!
                    let content style =
                        if ((line @ column-index) == alias-character)
                            _ (alias-character as string) HighlightingStyle.Default
                        else
                            _ (tostring current-token) HighlightingStyle.Keyword

                    'append result
                        HighlightedText
                            content = content
                            style = style
                    _ (tokens-this-line + 1) (column + (countof content))
                default
                    'append result
                        HighlightedText
                            content = (tostring current-token)
                            style = (symbol->style (current-token as Symbol))
                    _ (tokens-this-line + 1) (column + (countof (tostring current-token)))
            elseif ((tokenT < real) or (tokenT < integer))
                let line-remainder = (rslice line (column - 1))
                let match1? start1 end1 = ('match? number-regexp1 line-remainder)
                let match2? start2 end2 = ('match? number-regexp2 line-remainder)
                let match3? start3 end3 = ('match? number-regexp3 line-remainder)
                assert (or match1? match2? match3?)
                let number-length =
                    if match1?
                        end1
                    elseif match2?
                        end2
                    else
                        end3
                number-length as:= usize

                'append result
                    HighlightedText
                        content = (lslice line-remainder number-length)
                        style = HighlightingStyle.Number
                _ (tokens-this-line + 1) (column + number-length)
            elseif (tokenT == string)
                # if it's a multiline string, do nothing and let the code after the loop handle it.
                if ('match? "^\"{4}" (rslice line (column - 1)))
                    _ (tokens-this-line + 1) (column as usize)
                else
                    'append result
                        HighlightedText
                            content = (tostring current-token)
                            style = HighlightingStyle.String
                    _ (tokens-this-line + 1) (column + (countof (tostring current-token)))
            else
                # shouldn't happen
                assert false ("Unknown token type: " .. (tostring tokenT))
                _ 0 0:usize

    # should always have at least a \n remaining?
    assert (last-point <= (countof line))
    last-point-index := (last-point - 1)
    line-remainder := (rslice line last-point-index)
    # now we append the rest of the line.
    # check if we didn't start a comment or multiline string.
    let match-mlstring? __ end-mlstring-preamble = ('match? "\\s*(?=\"{4})" line-remainder)
    let match-comment? __ end-comment-preamble = ('match? "\\s*(?=#)" line-remainder)
    # first add the text between last point and comment/string, then those.
    if match-mlstring?
        'append result
            HighlightedText
                content = (lslice line-remainder end-mlstring-preamble)
                style = HighlightingStyle.Default
        'append result
            HighlightedText
                content = (rslice line-remainder end-mlstring-preamble)
                style = HighlightingStyle.String
        _
            lines-highlighted + 1
            tokens-highlighted + tokens-this-line
            # multiline string offset actually starts after the quotes.
            HighlightingMode.MultilineString
                offset =
                    (last-point-index + (end-mlstring-preamble + 4)) as i32
    elseif match-comment?
        'append result
            HighlightedText
                content = (lslice line-remainder end-comment-preamble)
                style = HighlightingStyle.Default
        'append result
            HighlightedText
                content = (rslice line-remainder end-comment-preamble)
                style = HighlightingStyle.Comment
        _
            lines-highlighted + 1
            tokens-highlighted + tokens-this-line
            HighlightingMode.Comment
                offset =
                    (last-point-index + end-comment-preamble + 1) as i32
    else
        'append result
            HighlightedText
                content = line-remainder
                style = HighlightingStyle.Default
        _ (lines-highlighted + 1) (tokens-highlighted + tokens-this-line) (HighlightingMode.Default)
    skip-line ::

fn string-replace (str pattern substitution)
    loop (lhs rhs = "" (deref str))
        let match? start end = ('match? pattern rhs)
        if (not match?)
            break (lhs .. rhs)
        let lhs = (.. lhs (lslice rhs start) substitution)
        let rhs = (rslice rhs end)
        _ lhs rhs

fn sanitize-string-html (str)
    -->
        string-replace str "&" "&amp;"
        string-replace __ "<" "&lt;"
        string-replace __ ">" "&gt;"
        string-replace __ "_" "&#95;"
        string-replace __ "`" "&#96;"
        string-replace __ "-" "&#45;"

inline export-html (tokens)
    io-write! "<pre class=\"language-scopes\"><code class=\"language-scopes\">"
    for token in tokens
        if (token.style != HighlightingStyle.Default)
            let class =
                switch token.style
                case HighlightingStyle.Comment
                    "comment"
                case HighlightingStyle.String
                    "string"
                case HighlightingStyle.Number
                    "number"
                case HighlightingStyle.Symbol
                    "symbol"
                case HighlightingStyle.Keyword
                    "keyword"
                case HighlightingStyle.Function
                    "function"
                case HighlightingStyle.Operator
                    "operator"
                case HighlightingStyle.Type
                    "type"
                case HighlightingStyle.SugarMacro
                    "keyword"
                case HighlightingStyle.SpiceMacro
                    "function"
                case HighlightingStyle.GlobalSymbol
                    "constant"
                case HighlightingStyle.SpecialConstant
                    "constant"
                default
                    ""
            io-write! (.. "<span class=\"token " class "\">" (sanitize-string-html token.content) "</span>")
        else
            io-write! (sanitize-string-html token.content)
    io-write! "</code></pre>"

export-html result;

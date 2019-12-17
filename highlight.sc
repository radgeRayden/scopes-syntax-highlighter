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

# now we walk through the actual text
local result : (Array HighlightedText)
fold (line-counter token-offset comment-state = 1 0 (CommentState)) for line in (lines text)
    let tokens-skipped comment-state =
        :: comment-test
        if comment-state.mid-comment?
            # skip empty lines
            if ('match? "^\\s*\\n" line)
                merge comment-test 0 comment-state
            # match first non blank character of line
            let match? start end = ('match? "^\\s*[^\\s]" line)
            assert match?
            # need to subtract one because we overmatch
            if ((end - 1) > comment-state.offset)
                merge comment-test 0 comment-state
            # it's another comment!
            if ((line @ (end - 1)) == 35:i8) # pound character
                merge comment-test 0
                    CommentState
                        mid-comment? = true
                        offset = (end - 1)
        else
            let match-comment? start end = ('match? "^\\s*#" line)
            if match-comment?
                merge comment-test 0
                    CommentState
                        mid-comment? = true
                        offset = (end - 1) # the pound doesn't count!

        # if we got here, no comment detected so far or comment ended!
        let comment-state = (CommentState)
        loop (tokens-walked last-point = 0 1:usize)
            # check comment
            let index = (token-offset + tokens-walked)
            if (index >= (countof code))
                break tokens-walked comment-state
            let current-token = (code @ index)
            anchor := ('anchor current-token)
            line-number := ('line anchor)
            column := ('column anchor)
            column-index := (column - 1)
            if (line-number > line-counter)
                let match-comment? start end = ('match? "^\\s*#" (rslice line last-point))
                if match-comment?
                    'append result
                        HighlightedText
                            content = (rslice line (last-point - 1))
                            style = HighlightingStyle.Comment
                    break tokens-walked
                        CommentState
                            mid-comment? = true
                            offset = ((last-point + (end - 1)) as i32)

                # append rest of line if adequate
                if (tokens-walked > 0)
                    # should always have at least a \n remaining!
                    assert (last-point <= (countof line))
                    'append result
                        HighlightedText
                            content = (rslice line (last-point - 1))
                            style = HighlightingStyle.Default
                # continue on the next line
                break tokens-walked comment-state
            if ('none? current-token)
                # it seems empty function arg gets a weird anchor so lets just skip it.
                repeat (tokens-walked + 1) last-point
            assert (line-counter <= line-number) # did we skip too much outside this loop?
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
                            _ (tokens-walked + 1) ((column + 1) as usize)
                        else
                            # FIXME: caution! content could have ended with sugar quote!
                            assert ((index + 1) < (countof code))
                            let next-token = (code @ (index + 1))
                            'append result
                                HighlightedText
                                    content = (.. "'" (tostring next-token))
                                    style = HighlightingStyle.Symbol
                            _ (tokens-walked + 2) (column + 1 + (countof (tostring next-token)))
                    else
                        'append result
                            HighlightedText
                                content = "sugar-quote"
                                style = (symbol->style (current-token as Symbol))
                        _ (tokens-walked + 1) (column + (countof (tostring current-token)))

                case 'spice-quote
                    # spice-quote's anchor is at the actual backtick
                    if ((line @ column-index) == 96:i8) # ` character
                        'append result
                            HighlightedText
                                content = "`"
                                style = HighlightingStyle.Keyword
                        _ (tokens-walked + 1) ((column + 1) as usize)
                    else
                        'append result
                            HighlightedText
                                content = "spice-quote"
                                style = HighlightingStyle.Keyword
                        _ (tokens-walked + 1) (column + (countof (tostring current-token)))
                pass 'square-list
                    # FIXME: handle case where "square-list" is spelled out instead of [].
                pass 'curly-list
                    # FIXME: handle case where "curly-list" is spelled out instead of {}.
                do
                    _ (tokens-walked + 1) (column as usize)
                default
                    'append result
                        HighlightedText
                            content = (tostring current-token)
                            style = (symbol->style (current-token as Symbol))
                    _ (tokens-walked + 1) (column + (countof (tostring current-token)))
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
                _ (tokens-walked + 1) (column + number-length)
            elseif (tokenT == string)
                'append result
                    HighlightedText
                        content = (tostring current-token)
                        style = HighlightingStyle.String
                _ (tokens-walked + 1) (column + (countof (tostring current-token)))
            else
                # shouldn't happen
                assert false ("Unknown token type: " .. (tostring tokenT))
                _ 0 0:usize

        comment-test ::

    if (tokens-skipped == 0)
        if comment-state.mid-comment?
            'append result
                HighlightedText
                    content = line
                    style = HighlightingStyle.Comment
        else
            'append result
                HighlightedText
                    content = line
                    style = HighlightingStyle.Default
    _ (line-counter + 1) (token-offset + tokens-skipped) comment-state

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

inline export-html ()
    io-write! "<pre class=\"language-scopes\"><code class=\"language-scopes\">"
    for token in result
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

`()
export-html;

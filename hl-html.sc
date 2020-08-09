using import itertools
using import chaining
using import .highlight
using import Array

let stdio =
    do
        stdio := (include "stdio.h")
        using stdio.extern
        using stdio.define # filter "^(stdin|stdout)$"
        using stdio.const
        locals;

# 1. argparse
let argc argv = (launch-args)
let help =
    """"hl-html.sc: outputs syntax highlighted scopes code as html.
        Usage: scopes hl-html.sc [-h] [<input> | --stdin] [<output> | --stdout]
        If no input file or --stdin is provided, reads from stdin.
        If no output file or --stdout is provided, outputs to stdout.
        -h,--help - Displays this help message.

let input-file output-file =
    # easier to just deal with all combinations of args that we care about.
    label argparse
        if (argc == 2)
            merge argparse "" "" # read from stdin, write to stdout
        assert (argc > 2)
        arg2 := (string (argv @ 2))
        let input-file =
            match arg2
            case (or "-h" "--help")
                io-write! help
                exit 0
            case "--stdin"
                ""
            case "--stdout"
                merge argparse "" ""
            default
                arg2
        if (argc == 3)
            merge argparse input-file ""
        arg3 := (string (argv @ 3))
        let output-file =
            if (arg3 == "--stdout")
                ""
            else
                arg3
        _ input-file output-file

stdin? := (input-file == "")
stdout? := (output-file == "")
# 2. load selected file as string
let code =
    if stdin?
        local buf : (Array i8)
        'reserve buf (1024 ** 2) # 1mb
        loop (c = (stdio.getc stdio.stdin))
            if (c == -1) # EOF
                break;
            'append buf (c as i8)

            stdio.getc stdio.stdin

        string (buf as pointer)
    else
        # read whole file
        file-handle := (stdio.fopen input-file "r")
        # we get size of file by seeking
        stdio.fseek file-handle 0 stdio.SEEK_END
        file-size := ((stdio.ftell file-handle) as u64)
        stdio.fseek file-handle 0 stdio.SEEK_SET
        # do the reading the make a string with count.
        # I'm pretty sure we don't get null terminator,
        # but the string constructor takes care of that.
        buf := (malloc-array i8 file-size)
        let read-result = (stdio.fread buf 1:usize file-size file-handle)
        assert (read-result == file-size)
        stdio.fclose file-handle

        string buf file-size

# 3. call highlight.sc to highlight text, returning an array of HighlightedText
let highlighted-code = (highlight code)
# 4. write to file or stdout depending on option
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

inline export-html (tokens writer-fn)
    writer-fn "<pre class=\"language-scopes\"><code class=\"language-scopes\">"
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
            writer-fn (.. "<span class=\"token " class "\">" (sanitize-string-html token.content) "</span>")
        else
            writer-fn (sanitize-string-html token.content)
    writer-fn "</code></pre>"

if stdout?
    export-html highlighted-code io-write!
else
    file-handle := (stdio.fopen output-file "w")
    export-html highlighted-code
        inline writer (str)
            let write-result =
                stdio.fwrite (str as rawstring) 1 (countof str) file-handle
            assert (write-result == (countof str))
    stdio.fclose file-handle

none

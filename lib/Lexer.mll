(* scaml/lib/lexer.mll *)
{
open Parser (* Needed to access the token type defined in parser.mly *)
(* Use Value directly *)

(* Helper to handle character escapes - Adapted for Elisp common escapes *)
let char_from_escape s =
  if String.length s = 1 then
    s.[0]
  else (* Starts with \ *)
    match s.[1] with
    | 'n' -> '\n'
    | 't' -> '\t'
    | 'r' -> '\r'
    | 'b' -> '\b'
    | 'f' -> '\012' (* Form feed *)
    | 'v' -> '\013' (* Vertical tab *)
    | '\\' -> '\\'
    | '"' -> '"' (* Needed for within strings *)
    | 's' -> ' ' (* Common Lisp space, Emacs might use just space *)
    | '0'..'7' ->
        (* Handle octal escape up to 3 digits, e.g. \177 *)
        let code = ref 0 in
        let len = min (String.length s) 4 in (* \ plus up to 3 digits *)
        for i = 1 to len - 1 do
          if s.[i] >= '0' && s.[i] <= '7' then
            code := (!code * 8) + (Char.code s.[i] - Char.code '0')
          else
            raise (Failure ("Invalid octal escape sequence in char: " ^ s))
        done;
        if !code > 255 then raise (Failure ("Invalid octal escape code (too large) in char: " ^ s));
        Char.chr !code
    (* Add more Emacs-specific escapes if needed: \C-x, \M-x etc. *)
    | _ -> s.[1] (* Treat \c as just c if not a special escape *)

let string_buffer = Buffer.create 1024

let unescape_string s =
  Buffer.clear string_buffer;
  let i = ref 0 in
  let len = String.length s in
  while !i < len do
    if s.[!i] = '\\' && !i + 1 < len then begin
      let escaped_char =
        match s.[!i+1] with
        | 'n' -> '\n' | 't' -> '\t' | 'r' -> '\r' | 'b' -> '\b'
        | 'f' -> '\012' | 'v' -> '\013'
        | '\\' -> '\\' | '"' -> '"'
        | '0'..'7' ->
            let start_oct = !i + 1 in
            let end_oct = ref start_oct in
            while !end_oct + 1 < len && !end_oct + 1 < start_oct + 3 && s.[!end_oct + 1] >= '0' && s.[!end_oct + 1] <= '7' do
              incr end_oct
            done;
            let oct_str = String.sub s start_oct (!end_oct - start_oct + 1) in
            let code = int_of_string ("0o" ^ oct_str) in
             if code > 255 then raise (Failure ("Invalid octal escape code (too large) in string: \\" ^ oct_str));
             i := !end_oct; (* Advance i past the octal digits *)
             Char.chr code
        (* Add \xNN, \uNNNN, \UNNNNNNNN if needed *)
        | c -> c (* Unknown escape: treat as literal character *)
      in
      Buffer.add_char string_buffer escaped_char;
      i := !i + 1 (* Already incremented i if needed (e.g., octal) *)
    end else begin
      Buffer.add_char string_buffer s.[!i];
    end;
    incr i
  done;
  Buffer.contents string_buffer

}

(* Define regexps for tokens *)
let digit = ['0'-'9']
let frac = '.' digit+
let exp = ['e' 'E'] ['-' '+']? digit+
let float_lit = ['-' '+']? (digit+ (frac exp? | exp) | frac exp?) (* Basic float *)
let int_lit = ['-' '+']? digit+
(* Add hex/octal/binary number literals if needed, e.g., #x... #o... #b... *)

(* Elisp symbols can contain almost anything not otherwise interpreted *)
(* More precise symbol def (avoid starting like numbers): *)
let initial_symbol_char = ['a'-'z' 'A'-'Z' '*' '+' '/' '<' '=' '>' '?' '!' '_' '$' '%' '&' '~' '^' '-'] (* Simplified *)
let subsequent_symbol_char = initial_symbol_char | digit | '.' | ':' (* Use | or list chars directly *)
let symbol_refined_lit = initial_symbol_char subsequent_symbol_char* (* Removed trailing | '+' | '-' *)


let keyword_lit = ':' subsequent_symbol_char+ (* Use subsequent for keywords *)

(* Elisp Character literals: ? followed by char or \escape sequence *)
let char_simple = [^ '\\'] (* Any char except backslash *)
let char_escape = '\\' ([ 'n' 't' 'r' 'b' 'f' 'v' '\\' '"' 's' ] | ['0'-'7'] ['0'-'7']? ['0'-'7']? | _ ) (* Use _ for any char *)
let char_lit = '?' (char_simple | char_escape)


rule token = parse
  | [' ' '\t' '\n' '\r']+ { token lexbuf } (* Skip whitespace *)
  | ';' [^'\n']* ('\n'|eof) { token lexbuf } (* Skip comments to EOL *)
  | "#|"           { comment (1) lexbuf }    (* Nested block comment start *)

  (* Delimiters and reader macros *)
  | '('            { LPAREN }
  | ')'            { RPAREN }
  | '['            { LBRACKET }
  | ']'            { RBRACKET }
  | '.'            { DOT }
  | '\''           { QUOTE }
  | '`'            { BACKQUOTE }
  | ','            { COMMA }
  | ",@"           { COMMA_AT }
  | "#'"           { HASH_QUOTE }

  (* Atoms *)
  | "nil"          { NIL_TOKEN } (* Distinguish 'nil' symbol from empty list '()' *)
  | "t"            { T_TOKEN }
  | int_lit as lxm {
      try INT (int_of_string lxm)
      with _ -> SYMBOL lxm (* If it looks like an int but fails, treat as symbol *)
    }
  | float_lit as lxm {
      try FLOAT (float_of_string lxm)
      with _ -> SYMBOL lxm (* If it looks like a float but fails, treat as symbol *)
    }
  (* ***** FIX HERE ***** *)
  | '"' ([^ '"' '\\'] | '\\' _)* '"' as lxm { (* Use '\\' _ to match escaped char *)
      (* Remove quotes and unescape content *)
      let content = String.sub lxm 1 (String.length lxm - 2) in
      STRING (unescape_string content)
    }
  | keyword_lit as lxm { KEYWORD (String.sub lxm 1 (String.length lxm - 1)) } (* Remove leading ':' *)
  | char_lit as lxm {
      let char_part = String.sub lxm 1 (String.length lxm - 1) in
      CHAR (char_from_escape char_part)
     }
   (* Important: Symbol must be tried *after* keywords, numbers, nil, t *)
  | symbol_refined_lit as lxm { SYMBOL lxm }

  (* End of file *)
  | eof            { EOF }

  (* Error *)
  | _ as c         { raise (Failure (Printf.sprintf "Lexer error: Unexpected character '%c' at position %d"
                                      c (Lexing.lexeme_start lexbuf))) }

(* Rule for nested block comments *)
and comment level = parse
  | "#|"           { comment (level + 1) lexbuf }
  | "|#"           { if level = 1 then token lexbuf else comment (level - 1) lexbuf }
  | eof            { raise (Failure "Unterminated block comment") }
  | [^ '#' '|']+   { comment level lexbuf } (* Consume chars efficiently *)
  | '#'            { (* Buffer.add_char Lexing.current_buffer '#'; *) comment level lexbuf } (* Consume '#' not part of delimiters *)
  | '|'            { (* Buffer.add_char Lexing.current_buffer '|'; *) comment level lexbuf } (* Consume '|' not part of delimiters *)
  | _              { comment level lexbuf } (* Consume single character *)


{
}

(* scaml/lib/parse.ml *)
open Lexing
open Value (* Use Value.t *)

exception SyntaxError of string

(* Function to parse from a lexbuf *)
let from_lexbuf (lexbuf : Lexing.lexbuf) : (Value.t, string) result =
  (* Set the filename in the lexbuf for better error messages *)
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = lexbuf.lex_curr_p.pos_fname };
  try
    let result = Parser.main Lexer.token lexbuf in
    Ok result
  with
  | SyntaxError msg -> Error msg (* Custom syntax error from parser actions if needed *)
  | Failure msg when String.is_prefix msg ~prefix:"Lexer error:" -> (* Catch known lexer errors *)
      let pos = lexbuf.lex_curr_p in
      Error (Printf.sprintf "Lexer error in '%s' at line %d, column %d: %s"
               pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) msg)
  | Parser.Error -> (* Catch Menhir parser errors *)
      let pos = lexbuf.lex_curr_p in
      Error (Printf.sprintf "Syntax error in '%s' near token '%s' at line %d, column %d"
               pos.pos_fname (Lexing.lexeme lexbuf) pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1))
  | e -> (* Catch other potential errors *)
      Error (Printf.sprintf "An unexpected error occurred during parsing: %s\n%s"
               (Exn.to_string e) (Printexc.get_backtrace ()))

(* Function to parse a string *)
let from_string ?(filename="<string>") (s : string) : (Value.t, string) result =
  let lexbuf = Lexing.from_string s in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  from_lexbuf lexbuf

(* Function to parse from an input channel *)
let from_channel ?(filename="<channel>") (ic : in_channel) : (Value.t, string) result =
  let lexbuf = Lexing.from_channel ic in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  from_lexbuf lexbuf

(* Function to parse multiple S-expressions from a string *)
(* This is tricky because the parser expects EOF after one sexp *)
(* A common approach is to wrap the parser or use a streaming API if menhir provides one *)
(* Simple version: Parse one, advance lexbuf, repeat. Needs careful handling of whitespace/errors *)
let multiple_from_string ?(filename="<string>") (s : string) : (Value.t list, string) result =
  let lexbuf = Lexing.from_string s in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let results = ref [] in
  let continue = ref true in
  while !continue do
      (* Attempt to skip whitespace/comments before next expression *)
      begin try
          while true do
              let pos = lexbuf.lex_curr_pos in
              match Lexer.token lexbuf with
              | Parser.EOF -> raise Exit (* Reached real EOF *)
              | _ -> (* Found a real token, rollback and break *)
                   lexbuf.lex_curr_pos <- pos;
                   lexbuf.lex_start_pos <- pos;
                   raise Exit
          done
      with Exit -> ()
      end;

      if lexbuf.lex_curr_pos >= String.length s then
          continue := false (* Reached end of string *)
      else
          match from_lexbuf lexbuf with
          | Ok value -> results := value :: !results
          | Error msg -> results := []; continue := false; (* Clear results on error *)
                            return (Error msg) (* Return error immediately *)
  done;
  Ok (List.rev !results)

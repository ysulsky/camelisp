(* scaml/lib/parse.ml *)
open Core
open Lexing
(* Removed open Value *)

exception SyntaxError of string
exception Found_non_whitespace (* Local exception for EOF check *)

(* Function to parse from a lexbuf *)
let from_lexbuf (lexbuf : Lexing.lexbuf) : (Value.t, string) result =
  (* Set the filename in the lexbuf for better error messages *)
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = lexbuf.lex_curr_p.pos_fname };
  try
    (* ***** FIX HERE: Call the correct generated function ***** *)
    let result = Parser.repl_entry Lexer.token lexbuf in
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
(* Corrected type annotation *)
let from_channel ?(filename="<channel>") (ic : In_channel.t) : (Value.t, string) result =
  let lexbuf = Lexing.from_channel ic in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  from_lexbuf lexbuf

(* Function to parse multiple S-expressions from a string *)
let multiple_from_string ?(filename="<string>") (s : string) : (Value.t list, string) result =
  let lexbuf = Lexing.from_string s in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let results = ref [] in
  let error_msg = ref None in (* Store potential error *)
  let at_end = ref false in

  (* Loop while no error has occurred and we are not at the end *)
  while Option.is_none !error_msg && not !at_end do
    (* Check if the buffer position is effectively at the end by peeking *)
    let is_at_end_of_input =
      let current_pos = lexbuf.lex_curr_pos in
       try
          (* Peek one token ahead. Lexer.token skips whitespace/comments *)
          match Lexer.token lexbuf with
          | Parser.EOF -> true (* Only EOF found *)
          | _ ->
              (* Found a non-EOF token, rollback and report not at end *)
              lexbuf.lex_curr_pos <- current_pos;
              lexbuf.lex_start_pos <- current_pos;
              false
       with
       (* Any exception during peeking means we couldn't confirm EOF *)
       | _ ->
           lexbuf.lex_curr_pos <- current_pos;
           lexbuf.lex_start_pos <- current_pos;
           false
    in

    if is_at_end_of_input then
      at_end := true
    else
      match from_lexbuf lexbuf with
      | Ok value -> results := value :: !results (* Append to list *)
      | Error msg ->
          (* Store the error message and stop *)
          error_msg := Some msg;
          at_end := true (* Ensure loop terminates *)
  done; (* Semicolon is optional here but harmless *)

  (* Check if an error occurred during the loop *)
  match !error_msg with
  | Some msg -> Error msg (* Return the captured error *)
  | None -> Ok (List.rev !results) (* No error, return the reversed list *)


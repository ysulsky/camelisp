(* bin/main.ml - REPL for Scaml *)

open! Core
(* open Sexplib - REMOVED *)
(* open! Sexplib.Std - REMOVED *)
(* open! Scaml - Using qualified names initially, now aliases *)

(* Module Aliases for convenience *)
module Sexp = Sexplib.Sexp
module Lexer = Sexplib.Lexer (* Still needed for refill function logic? No.*)
module Parser = Sexplib.Parser (* Still needed for token types in refill? No.*)
module Compiler = Scaml.Compiler
module Runtime = Scaml.Runtime
module Value = Scaml.Value
module Interpreter = Scaml.Interpreter
module Analyze = Scaml.Analyze
module Translate = Scaml.Translate
module Lexing = Lexing (* Add alias for Lexing *)


(* --- Compile Implementation (for 'compile' built-in) --- *)
(* This function encapsulates the pipeline previously attempted in Runtime *)
let scaml_compile_impl (sexps : Sexp.t list) : (string * Value.t) list =
  try
     (* 1. Analyze *)
     let typed_asts, final_env_types = Analyze.analyze_toplevel sexps in
     (* 2. Translate *)
     let ocaml_code = Translate.translate_toplevel typed_asts final_env_types in
     (* 3. Compile and Load *)
     let _, get_env_func = Compiler.compile_and_load_string ocaml_code in
     (* 4. Get environment *)
     get_env_func ()
  with
   (* Propagate errors, potentially wrapping them *)
   | Compiler.Compilation_error msg -> failwith ("Compilation Error: " ^ msg)
   | Failure msg -> failwith ("Analysis/Translation/Runtime Error: " ^ msg)
   | exn -> failwith ("Unexpected compilation pipeline error: " ^ Exn.to_string exn)

(* --- Interpret Implementation (for 'interpret' built-in) --- *)
let scaml_interpret_impl (sexps : Sexp.t list) : Value.t =
    try
        (* Evaluate using the interpreter's top-level function *)
        Interpreter.eval_toplevel sexps
    with
    | Failure msg -> failwith ("Interpretation Error: " ^ msg)
    | exn -> failwith ("Unexpected interpretation error: " ^ Exn.to_string exn)


(* --- REPL Implementation --- *)

let run_repl () =
  (* Initialize the REPL's lexical environment *)
  let repl_env : Interpreter.eval_env ref = ref [] in
  let continue = ref true in

  (* Register 'exit' *)
  Runtime.register_global "exit" (Value.Builtin (fun _ -> continue := false; Value.Nil));

  printf "Welcome to Scaml REPL!\n";
  printf "Handles multi-line input, comments, ' , and . notation.\n";
  printf "Use (exit) to quit.\n";

  (* --- Lexing State (Simplified) --- *)
  (* We only need to track paren level for the prompt now *)
  let paren_level = ref 0 in
  let line_buffer = ref "" in (* Buffer for the current line being fed *)
  let line_pos = ref 0 in (* Position within the current line_buffer *)
  let eof_reached = ref false in (* Track if stdin EOF occurred *)

  (* Refill function for Lexing.from_function *)
  let refill_lexbuf (buf : Bytes.t) (len : int) : int =
    if !eof_reached then 0 (* Don't try to read past EOF *)
    else if !line_pos >= String.length !line_buffer then begin
      (* Need a new line from stdin *)
      let prompt = if !paren_level <= 0 then "> " else "  " in
      printf "%s%!" prompt;
      match In_channel.input_line In_channel.stdin with
      | None -> eof_reached := true; 0 (* EOF *)
      | Some line ->
          (* Basic paren tracking for prompt - imperfect but better than nothing *)
          String.iter line ~f:(fun char ->
              match char with
              | '(' -> Int.incr paren_level
              | ')' -> Int.decr paren_level
              | _ -> ()
          );
          if !paren_level < 0 then paren_level := 0; (* Reset on likely error *)

          line_buffer := line ^ "\n"; (* Store new line with newline *)
          line_pos := 0;
          let bytes_to_copy = min len (String.length !line_buffer) in
          Bytes.From_string.blit
             ~src:!line_buffer ~src_pos:0
             ~dst:buf ~dst_pos:0
             ~len:bytes_to_copy;
          line_pos := bytes_to_copy; (* Update position in line_buffer *)
          bytes_to_copy
    end else begin
      (* Still data left in line_buffer *)
      let remaining_in_line = String.length !line_buffer - !line_pos in
      let bytes_to_copy = min len remaining_in_line in
       Bytes.From_string.blit
         ~src:!line_buffer ~src_pos:!line_pos
         ~dst:buf ~dst_pos:0
         ~len:bytes_to_copy;
      line_pos := !line_pos + bytes_to_copy;
      bytes_to_copy
    end
  in

  (* Create the lexbuf that reads from stdin via refill_lexbuf *)
  let lexbuf = Lexing.from_function refill_lexbuf in

  while !continue do
    try
      (* Use scan_sexp_opt which takes the lexbuf directly *)
      match Sexp.scan_sexp_opt lexbuf with
      | Some sexp ->
          (* Successfully parsed one S-expression *)
          paren_level := 0; (* Reset prompt level after successful parse *)
          begin try
            (* Evaluate *)
            let result = Interpreter.eval !repl_env sexp in
            (* Print *)
            printf "%s\n%!" ((!Value.to_string) result)
          with
          (* Handle runtime errors during evaluation *)
          | Failure msg -> printf "Error: %s\n%!" msg
          | exn -> printf "Unknown Error: %s\n%!" (Exn.to_string exn)
          end
      | None ->
          (* scan_sexp_opt returned None, meaning clean EOF *)
          continue := false

    with
    (* Catch specific parsing errors if scan_sexp_opt raises them *)
    | Sexp.Parse_error { err_msg; _ } ->
        printf "Parse Error: %s\n%!" err_msg;
        paren_level := 0; (* Reset prompt level *)
        Lexing.flush_input lexbuf; (* Attempt to clear lexbuf state *)
        line_buffer := ""; line_pos := 0; eof_reached := false (* Reset line buffer *)
    | Failure msg when String.is_prefix msg ~prefix:"Sexplib.Conv.of_sexp_error" ->
         printf "Parse Error: %s\n%!" msg;
         paren_level := 0; Lexing.flush_input lexbuf; line_buffer := ""; line_pos := 0; eof_reached := false
    (* Catch EOF if refill_lexbuf hits it unexpectedly (should be handled by None case) *)
    | End_of_file -> continue := false
    (* Catch other unexpected errors *)
    | Sys_error msg -> printf "System Error: %s\n%!" msg; continue := false
    | exn -> printf "Unexpected REPL Error: %s\n%!" (Exn.to_string exn); continue := false
  done;
  printf "Exiting Scaml REPL.\n%!"


let () =
  (* ***** REGISTER BUILTIN IMPLEMENTATIONS ***** *)
  Runtime.register_compile_impl scaml_compile_impl;
  Runtime.register_interpret_impl scaml_interpret_impl;
  (* ******************************************** *)

  (* Run the REPL *)
  run_repl ()


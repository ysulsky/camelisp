(* bin/main.ml - REPL for Scaml *)

open! Core
(* open! Scaml - REMOVED open! Scaml to use qualified names *)
open! Sexplib.Std

(* --- Compile Implementation (for 'compile' built-in) --- *)
(* This function encapsulates the pipeline previously attempted in Runtime *)
let scaml_compile_impl (sexps : Sexp.t list) : (string * Scaml.Value.t) list =
  try
     (* 1. Analyze *)
     (* Use qualified name Scaml.Analyze *)
     let typed_asts, final_env_types = Scaml.Analyze.analyze_toplevel sexps in

     (* 2. Translate *)
     (* Use qualified name Scaml.Translate *)
     let ocaml_code = Scaml.Translate.translate_toplevel typed_asts final_env_types in

     (* 3. Compile and Load *)
     (* Use qualified name Scaml.Compiler *)
     let _, get_env_func = Scaml.Compiler.compile_and_load_string ocaml_code in

     (* 4. Get environment *)
     get_env_func ()
  with
   (* Propagate errors, potentially wrapping them *)
   (* Use qualified name Scaml.Compiler *)
   | Scaml.Compiler.Compilation_error msg -> failwith ("Compilation Error: " ^ msg)
   | Failure msg -> failwith ("Analysis/Translation/Runtime Error: " ^ msg)
   | exn -> failwith ("Unexpected compilation pipeline error: " ^ Exn.to_string exn)

(* --- Interpret Implementation (for 'interpret' built-in) --- *)
let scaml_interpret_impl (sexps : Sexp.t list) : Scaml.Value.t =
    try
        (* Evaluate using the interpreter's top-level function *)
        (* Use qualified name Scaml.Interpreter *)
        Scaml.Interpreter.eval_toplevel sexps
    with
    | Failure msg -> failwith ("Interpretation Error: " ^ msg)
    | exn -> failwith ("Unexpected interpretation error: " ^ Exn.to_string exn)


(* --- REPL Implementation --- *)
let run_repl () =
  (* Initialize the REPL's lexical environment (starts empty) *)
  (* Use qualified name Scaml.Interpreter *)
  let repl_env : Scaml.Interpreter.eval_env ref = ref [] in
  let continue = ref true in

  (* Register 'exit' as a simple builtin for the REPL *)
  (* Use qualified name Scaml.Runtime and Scaml.Value *)
  Scaml.Runtime.register_global "exit" (Scaml.Value.Builtin (fun _ -> continue := false; Scaml.Value.Nil));

  printf "Welcome to Scaml REPL!\n";
  printf "Use (exit) to quit.\n";

  while !continue do
    try
      printf "> %!"; (* Print prompt *)
      (* Read *)
      match In_channel.input_line In_channel.stdin with
      | None -> continue := false (* End of file *)
      | Some line ->
          if not (String.is_empty line) then
            try
              (* Parse *)
              let sexp = Sexp.of_string line in
              (* Evaluate using the Interpreter for the REPL itself *)
              (* Use qualified name Scaml.Interpreter *)
              let result = Scaml.Interpreter.eval !repl_env sexp in
              (* Print *)
              (* Use Lisp-style printer from Runtime *)
              printf "%s\n%!" (Scaml.Runtime.value_to_string_lisp result)
            with
            (* Handle parsing errors *)
            | Sexp.Parse_error { err_msg; _ } -> printf "Parse Error: %s\n%!" err_msg
            | Failure msg when String.is_prefix msg ~prefix:"Sexplib.Conv.of_sexp_error" -> printf "Parse Error: %s\n%!" msg
            (* Handle runtime errors during evaluation (from Interpreter or builtins) *)
            | Failure msg -> printf "Error: %s\n%!" msg
            | exn -> printf "Unknown Error: %s\n%!" (Exn.to_string exn)
    with
    | End_of_file -> continue := false (* Handle Ctrl+D *)
    | Sys_error msg -> printf "System Error: %s\n%!" msg; continue := false (* Exit on system errors *)
    | exn -> printf "Unexpected REPL Error: %s\n%!" (Exn.to_string exn); continue := false (* Exit on other errors *)
  done;
  printf "Exiting Scaml REPL.\n%!"


let () =
  (* ***** REGISTER BUILTIN IMPLEMENTATIONS ***** *)
  (* Use qualified name Scaml.Runtime *)
  Scaml.Runtime.register_compile_impl scaml_compile_impl;
  Scaml.Runtime.register_interpret_impl scaml_interpret_impl;
  (* ******************************************** *)

  (* Run the REPL *)
  run_repl ()


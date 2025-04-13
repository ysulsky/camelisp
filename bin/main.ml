(* bin/main.ml - REPL for Scaml (Refactored for Value.t Parser) *)

open! Core
(* REMOVED: Sexplib related opens *)

(* Module Aliases for convenience *)
module Parse = Scaml.Parse (* Use the new parser module *)
module Compiler = Scaml.Compiler
module Runtime = Scaml.Runtime
module Value = Scaml.Value
module Interpreter = Scaml.Interpreter
module Analyze = Scaml.Analyze
module Translate = Scaml.Translate


(* --- Compile Implementation (for 'compile' built-in) --- *)
(* This function now takes Value.t list (representing quoted code) *)
let scaml_compile_impl (code_list : Value.t list) : (string * Value.t) list =
  try
     (* 1. Analyze - Needs to take Value.t list *)
     let typed_asts, final_env_types = Analyze.analyze_toplevel code_list in
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
(* This function now takes Value.t list *)
let scaml_interpret_impl (code_list : Value.t list) : Value.t =
    try
        (* Evaluate using the interpreter's top-level function *)
        Interpreter.eval_toplevel code_list
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
  printf "Using new Menhir/Ocamllex parser.\n";
  printf "Use (exit) to quit.\n";

  (* --- REPL Loop using Parse.from_channel --- *)
  (* No complex refill logic needed now *)

  printf "> %!"; (* Print initial prompt *)
  while !continue do
    try
      (* Parse directly from stdin channel *)
      match Parse.from_channel ~filename:"<stdin>" In_channel.stdin with
      | Ok value -> (* Successfully parsed one Value.t *)
          begin try
            (* Evaluate the parsed value *)
            let result = Interpreter.eval !repl_env value in
            (* Print result *)
            printf "%s\n%!" (!Value.to_string result);
            printf "> %!" (* Prompt for next input *)
          with
           (* Handle runtime errors during evaluation *)
           | Failure msg -> printf "Error: %s\n> %!" msg
           | exn -> printf "Unknown Error: %s\n> %!" (Exn.to_string exn)
          end
      | Error msg -> (* Handle parsing error from Parse.from_channel *)
           printf "%s\n" msg;
           (* Attempt to recover: Maybe flush stdin? Depends on OS/terminal. *)
           (* For simplicity, just print error and prompt again *)
           printf "> %!"

    with
     (* End_of_file is the expected way to exit the loop when stdin closes *)
     | End_of_file -> continue := false
     (* Catch other unexpected errors *)
     | Sys_error msg -> printf "System Error: %s\n%!" msg; continue := false
     | exn -> printf "Unexpected REPL Error: %s\n%!" (Exn.to_string exn); continue := false
  done;
  printf "\nExiting Scaml REPL.\n%!"


let () =
  (* ***** REGISTER BUILTIN IMPLEMENTATIONS ***** *)
  (* Register the adapted implementations that take Value.t list *)
  Runtime.register_compile_impl scaml_compile_impl;
  Runtime.register_interpret_impl scaml_interpret_impl;
  (* ******************************************** *)

  (* Run the REPL *)
  run_repl ()

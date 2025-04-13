(* bin/main.ml - REPL for Scaml with Readline Support *)

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


(* --- REPL Implementation with Readline --- *)

let run_repl () =
  (* Initialize the REPL's lexical environment *)
  let repl_env : Interpreter.eval_env ref = ref [] in
  let continue = ref true in

  (* Register 'exit' *)
  Runtime.register_global "exit" (Value.Builtin (fun _ -> continue := false; Value.Nil));

  printf "Welcome to Scaml REPL!\n";
  printf "Using Readline for input.\n";
  printf "Use (exit) or Ctrl+D to quit.\n%!";

  (* REPL Loop using Readline *)
  while !continue do
    match Readline.readline ~prompt:"> " () with
    | None -> (* EOF (Ctrl+D) *)
        continue := false;
        printf "\n%!" (* Print newline after Ctrl+D *)
    | Some line ->
        (* Add non-empty lines to history *)
        if not (String.is_empty (String.strip line)) then
          Readline.add_history line;

        (* Parse potentially multiple expressions from the line *)
        match Parse.multiple_from_string ~filename:"<stdin>" line with
        | Error msg ->
            (* Handle parsing error *)
            printf "Parse Error: %s\n%!" msg
        | Ok values ->
            (* Evaluate each parsed value sequentially *)
            let last_result = ref Value.Nil in (* Keep track of the last result *)
            begin try
              List.iter values ~f:(fun value ->
                let result = Interpreter.eval !repl_env value in
                last_result := result (* Update last result *)
              );
              (* Print the result of the *last* expression evaluated *)
              printf "%s\n%!" (!Value.to_string !last_result);
            with
            (* Handle runtime errors during evaluation *)
            | Failure msg -> printf "Runtime Error: %s\n%!" msg
            | exn -> printf "Unexpected Error: %s\n%!" (Exn.to_string exn)
            end
  done;
  printf "Exiting Scaml REPL.\n%!"


let () =
  (* ***** REGISTER BUILTIN IMPLEMENTATIONS ***** *)
  (* Register the adapted implementations that take Value.t list *)
  Runtime.register_compile_impl scaml_compile_impl;
  Runtime.register_interpret_impl scaml_interpret_impl;
  (* ******************************************** *)

  (* Run the REPL *)
  Readline.init ();
  run_repl ()


(* bin/main.ml - Main executable for Scaml *)

open! Core
open! Scaml (* OK here - this is the executable depending on the library *)
open! Sexplib.Std

let process_file filename =
  printf "Processing file: %s\n%!" filename;
  try
    (* 1. Read and Parse *)
    let sexps = Sexp.load_sexps filename in

    (* 2. Analyze *)
    printf "Analyzing...\n%!";
    let typed_asts, final_env_types = Analyze.analyze_toplevel sexps in (* Use Scaml.Analyze *)
    (* printf "TASTs:\n%s\n" (Sexp.to_string_hum ([%sexp_of: Analyze.TypedAst.t list] typed_asts)); *)
    (* printf "Final Env Types:\n%s\n" (Sexp.to_string_hum ([%sexp_of: (string * InferredType.t) list] final_env_types)); *)

    (* 3. Translate *)
    printf "Translating...\n%!";
    let ocaml_code = Translate.translate_toplevel typed_asts final_env_types in (* Use Scaml.Translate *)
    (* printf "Generated OCaml:\n%s\n" ocaml_code; *)


    (* REMOVED manual callback registration string concatenation *)
    let final_ocaml_code = ocaml_code in

    (* 4. Compile and Load *)
    printf "Compiling and loading...\n%!";
    (* Use the Compiler module from the Scaml library *)
    let run_func, get_env_func = Compiler.compile_and_load_string final_ocaml_code in (* Use Scaml.Compiler *)

    (* 5. Execute *)
    printf "Executing run function...\n%!";
    let result = run_func () in
    printf "Run Result: %s\n%!" (Value.to_string result); (* Use Scaml.Value *)

    (* 6. Get and Print Environment *)
    printf "Retrieving environment...\n%!";
    let exposed_env = get_env_func () in
    printf "Exposed Environment:\n";
    List.iter exposed_env ~f:(fun (name, value) ->
      printf "  %s: %s\n" name (Value.to_string value) (* Use Scaml.Value *)
    );
    printf "%!"

  with
  | Sexp.Parse_error { err_msg; _ } -> printf "Parse Error: %s\n%!" err_msg
  | Sys_error msg -> printf "System Error: %s\n%!" msg
  | Compiler.Compilation_error msg -> printf "Compilation Error: %s\n%!" msg (* Use Scaml.Compiler *)
  | Failure msg -> printf "Error: %s\n%!" msg (* Catch runtime errors *)
  | exn -> printf "Unknown Error: %s\n%!" (Exn.to_string exn)


let () =
  (* Use Core_unix.Command_unix explicitly *)
  Command_unix.run
    (Command.basic
       ~summary:"Transpile and Run Scaml Elisp Module"
       (* Use let%map_open provided by ppx_let *)
       (let%map_open.Command filename = anon ("filename" %: Filename_unix.arg_type) in
        fun () -> process_file filename)
    )


(* Compiler.ml - Compiles OCaml code strings and dynamically links them *)

open! Core
(* REMOVED: open! Core_unix *)

(* Use types from other library modules directly *)
module Value = Value

let ocamlopt_path = "ocamlopt" (* Or use `ocamlfind query ocamlopt` *)
let ocamlc_path = "ocamlc" (* Or use `ocamlfind query ocamlc` *)
(* These paths might need adjustment based on the build environment *)
(* Ensure these relative paths are correct from where dune build is run *)
let include_paths = ["_build/default/lib/"] (* Path to find scaml library internals like Value *)
let library_paths = ["_build/default/lib/"] (* Path to find scaml.cma *)


exception Compilation_error of string

(* --- Registration mechanism for loaded modules --- *)
(* These refs hold the functions from the *most recently* dynlinked module *)
let last_loaded_run_function : (unit -> Value.t) option ref = ref None
let last_loaded_get_environment : (unit -> (string * Value.t) list) option ref = ref None

(* These functions are registered with OCaml's Callback system and are called
   by the dynamically loaded code to pass its functions back to the compiler *)
let register_run_function (f : unit -> Value.t) : unit =
  (* Printf.printf "Compiler: Registering run function\n%!"; *)
  last_loaded_run_function := Some f

let register_get_environment (f : unit -> (string * Value.t) list) : unit =
  (* Printf.printf "Compiler: Registering get_environment function\n%!"; *)
   last_loaded_get_environment := Some f

(* Register these callback functions *once* when the Compiler module loads *)
let () =
  Callback.register "scaml_register_run" register_run_function;
  Callback.register "scaml_register_env" register_get_environment

(* --- End Registration --- *)


(** Compiles an OCaml source string to a .cma file and loads it *)
let compile_and_load_string (ocaml_code : string) : (unit -> Value.t) * (unit -> (string * Value.t) list) =
  let ml_filename = Filename_unix.temp_file "scaml_generated_" ".ml" in
  (* *** FIXED: Use Filename.chop_extension (from Core) *** *)
  let base_filename = Filename.chop_extension ml_filename in
  let cmo_filename = base_filename ^ ".cmo" in
  let cma_filename = base_filename ^ ".cma" in
  let cmi_filename = base_filename ^ ".cmi" in (* Define cmi for cleanup *)


  (* Reset registration refs before loading the new module *)
  last_loaded_run_function := None;
  last_loaded_get_environment := None;

  Exn.protect ~f:(fun () ->
    (* 1. Write the generated OCaml code to the temp .ml file *)
    Out_channel.write_all ml_filename ~data:ocaml_code;

    (* 2. Compile the .ml to .cmo (bytecode object file) *)
    let include_flags = List.map include_paths ~f:(sprintf "-I %s") |> String.concat ~sep:" " in
    let compile_byte_cmd = sprintf "%s -c %s -o %s %s" ocamlc_path include_flags cmo_filename ml_filename in
    (* Printf.printf "Executing: %s\n%!" compile_byte_cmd; *)
    if Sys_unix.command compile_byte_cmd <> 0 then
      raise (Compilation_error (sprintf "OCaml compilation failed for %s. Command: %s" ml_filename compile_byte_cmd));

    (* 3. Link the .cmo into a .cma (bytecode library archive) *)
    (* We link against the main scaml library (which should include Runtime, Value etc) *)
    let lib_flags = List.map library_paths ~f:(sprintf "-I %s") |> String.concat ~sep:" " in
    (* Link command needs the scaml library itself *)
    (* Ensure scaml.cma is available at link time *)
    let link_byte_cmd = sprintf "%s -a %s scaml.cma -o %s %s" ocamlc_path lib_flags cma_filename cmo_filename in
    (* Printf.printf "Executing: %s\n%!" link_byte_cmd; *)
    if Sys_unix.command link_byte_cmd <> 0 then
       raise (Compilation_error (sprintf "OCaml linking failed for %s. Command: %s" ml_filename link_byte_cmd));

    (* 4. Dynamically load the .cma library *)
    (* Printf.printf "Dynlinking: %s\n%!" cma_filename; *)
    begin try
      (* Dynlink.loadfile loads the code and executes its top-level definitions,
         which should include the calls to Callback.register via the lookup below. *)
      Dynlink.loadfile cma_filename
    with Dynlink.Error err ->
        raise (Compilation_error (sprintf "Dynlink error loading %s: %s" cma_filename (Dynlink.error_message err)))
    end;

    (* 5. Retrieve the functions registered via the callbacks *)
    let run_func = Option.value_exn !last_loaded_run_function
        ~message:"Dynamically linked module did not register its run function via scaml_register_run callback"
    in
    let get_env_func = Option.value_exn !last_loaded_get_environment
        ~message:"Dynamically linked module did not register its get_environment function via scaml_register_env callback"
    in
    (run_func, get_env_func)

  ) ~finally:(fun () ->
    (* Clean up temporary files *)
    (* Printf.printf "Cleaning up temp files for %s\n%!" base_filename; *)
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove ml_filename);
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cmo_filename);
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cmi_filename); (* Clean up .cmi *)
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cma_filename);
    ()
  )

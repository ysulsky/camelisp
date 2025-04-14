(* Compiler.ml - Compiles OCaml code strings and dynamically links them *)

open! Core
(* REMOVED: open! Core_unix *)

(* Use types from other library modules directly *)
module Value = Value

(* --- Compiler Paths --- *)
(* Use ocamlfind to handle package paths *)
let ocamlfind_path = "ocamlfind"
(* We still need the base compiler name for ocamlfind *)
let ocamlc_path = "ocamlc"
(* Keep include paths for project's own modules *)
let include_paths = ["_build/default/lib/"]
(* Library paths for linking against scaml.cma itself *)
let library_paths = ["_build/default/lib/"]


exception Compilation_error of string

(* --- Registration mechanism for loaded modules --- *)
(* This ref holds the function from the *most recently* dynlinked module *)
(* Renamed: Now holds the combined execute/get_env function *)
let last_loaded_execute_and_get_env_ref : (unit -> (string * Value.t) list) option ref = ref None

(* This function is registered with OCaml's Callback system and is called
   by the dynamically loaded code to pass its function back to the compiler *)
(* Renamed: Reflects the new combined function *)
let register_execute_and_get_env (f : unit -> (string * Value.t) list) : unit =
  (* Printf.printf "Compiler: Registering execute_and_get_env function\n%!"; *)
   last_loaded_execute_and_get_env_ref := Some f

(* Register this callback function *once* when the Compiler module loads *)
(* Use the new callback name used in Translate.ml *)
let () =
  Callback.register "scaml_register_compiled_module" register_execute_and_get_env
  (* Removed registration for "scaml_register_run" *)

(* --- End Registration --- *)


(** Compiles an OCaml source string to a .cma file and loads it *)
(* Modified: Returns only the single combined function *)
let compile_and_load_string (ocaml_code : string) : (unit -> (string * Value.t) list) =
  let ml_filename = Filename_unix.temp_file "scaml_generated_" ".ml" in
  let base_filename = Filename.chop_extension ml_filename in
  let cmo_filename = base_filename ^ ".cmo" in
  let cma_filename = base_filename ^ ".cma" in
  let cmi_filename = base_filename ^ ".cmi" in (* Define cmi for cleanup *)


  (* Reset registration ref before loading the new module *)
  last_loaded_execute_and_get_env_ref := None;
  (* Removed reset for last_loaded_run_function *)

  Exn.protect ~f:(fun () ->
    (* 1. Write the generated OCaml code to the temp .ml file *)
    Out_channel.write_all ml_filename ~data:ocaml_code;

    (* 2. Compile the .ml to .cmo (bytecode object file) *)
    (* Use ocamlfind to invoke ocamlc with package support *)
    let include_flags = List.map include_paths ~f:(sprintf "-I %s") |> String.concat ~sep:" " in
    (* Make sure scaml package is included for Value, Runtime etc. *)
    let compile_byte_cmd =
      sprintf "%s %s -package core,scaml -linkpkg -c %s -o %s %s"
        ocamlfind_path ocamlc_path include_flags cmo_filename ml_filename
    in
    (* Printf.printf "Executing: %s\n%!" compile_byte_cmd; *)
    if Sys_unix.command compile_byte_cmd <> 0 then
      raise (Compilation_error (sprintf "OCaml compilation failed for %s. Command: %s" ml_filename compile_byte_cmd));

    (* 3. Link the .cmo into a .cma (bytecode library archive) *)
    (* Use ocamlfind for linking as well *)
    let lib_flags = List.map library_paths ~f:(sprintf "-I %s") |> String.concat ~sep:" " in
    (* Ensure scaml.cma is linked *)
    let link_byte_cmd =
      sprintf "%s %s -package core,scaml -linkpkg -a %s %s -o %s %s" (* Added scaml package *)
        ocamlfind_path ocamlc_path lib_flags "scaml.cma" cma_filename cmo_filename
    in
    (* Printf.printf "Executing: %s\n%!" link_byte_cmd; *)
    if Sys_unix.command link_byte_cmd <> 0 then
       raise (Compilation_error (sprintf "OCaml linking failed for %s. Command: %s" ml_filename link_byte_cmd));

    (* 4. Dynamically load the .cma library *)
    (* Printf.printf "Dynlinking: %s\n%!" cma_filename; *)
    begin try
      (* Dynlink.loadfile loads the code and executes its top-level definitions,
         which should include the call to Callback.register via the lookup below. *)
      Dynlink.loadfile cma_filename
    with Dynlink.Error err ->
        raise (Compilation_error (sprintf "Dynlink error loading %s: %s" cma_filename (Dynlink.error_message err)))
    end;

    (* 5. Retrieve the single function registered via the callback *)
    let execute_and_get_env_func = Option.value_exn !last_loaded_execute_and_get_env_ref
        ~message:"Dynamically linked module did not register its function via scaml_register_compiled_module callback"
    in
    (* Removed retrieval of run_func *)
    execute_and_get_env_func (* Return the single function *)

  ) ~finally:(fun () ->
    (* Clean up temporary files *)
    (* Printf.printf "Cleaning up temp files for %s\n%!" base_filename; *)
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove ml_filename);
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cmo_filename);
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cmi_filename); (* Clean up .cmi *)
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cma_filename);
    ()
  )


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

(* --- Shared State for Loaded Modules --- *)
(* Define a shared ref accessible by both the compiler and dynamically loaded modules. *)
(* The loaded module will mutate this ref to pass back its environment. *)
let last_loaded_environment : (string * Value.t) list option ref = ref None

(* Removed Callback registration mechanism *)
(* --- End Shared State --- *)


(** Compiles an OCaml source string to a .cma file and loads it *)
(* Modified: Returns the environment list directly, retrieved from the shared ref *)
let compile_and_load_string (ocaml_code : string) : (string * Value.t) list =
  let ml_filename = Filename_unix.temp_file "scaml_generated_" ".ml" in
  let base_filename = Filename.chop_extension ml_filename in
  let cmo_filename = base_filename ^ ".cmo" in
  let cma_filename = base_filename ^ ".cma" in
  let cmi_filename = base_filename ^ ".cmi" in (* Define cmi for cleanup *)


  (* Reset shared ref before loading the new module *)
  last_loaded_environment := None;

  Exn.protect ~f:(fun () ->
    (* 1. Write the generated OCaml code to the temp .ml file *)
    Out_channel.write_all ml_filename ~data:ocaml_code;

    (* 2. Compile the .ml to .cmo (bytecode object file) *)
    let include_flags = List.map include_paths ~f:(sprintf "-I %s") |> String.concat ~sep:" " in
    (* Make sure scaml package is included for Value, Runtime etc. *)
    let compile_byte_cmd =
      sprintf "%s %s -package core,scaml -linkpkg -c %s -o %s %s"
        ocamlfind_path ocamlc_path include_flags cmo_filename ml_filename
    in
    if Sys_unix.command compile_byte_cmd <> 0 then
      raise (Compilation_error (sprintf "OCaml compilation failed for %s. Command: %s" ml_filename compile_byte_cmd));

    (* 3. Link the .cmo into a .cma (bytecode library archive) *)
    let lib_flags = List.map library_paths ~f:(sprintf "-I %s") |> String.concat ~sep:" " in
    (* Ensure scaml.cma is linked *)
    let link_byte_cmd =
      sprintf "%s %s -package core,scaml -linkpkg -a %s %s -o %s %s" (* Added scaml package *)
        ocamlfind_path ocamlc_path lib_flags "scaml.cma" cma_filename cmo_filename
    in
    if Sys_unix.command link_byte_cmd <> 0 then
       raise (Compilation_error (sprintf "OCaml linking failed for %s. Command: %s" ml_filename link_byte_cmd));

    (* 4. Dynamically load the .cma library *)
    (* Dynlink.loadfile executes the top-level code of the loaded module, *)
    (* which should now include the mutation of Compiler.last_loaded_environment *)
    begin try
      Dynlink.loadfile cma_filename
    with Dynlink.Error err ->
        raise (Compilation_error (sprintf "Dynlink error loading %s: %s" cma_filename (Dynlink.error_message err)))
    end;

    (* 5. Retrieve the environment from the shared ref *)
    match !last_loaded_environment with
     | None ->
         failwith "Dynamically loaded module failed to set the environment ref"
     | Some env_list ->
         env_list (* Return the environment list directly *)

  ) ~finally:(fun () ->
    (* Clean up temporary files *)
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove ml_filename);
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cmo_filename);
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cmi_filename);
    Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cma_filename);
    ()
  )


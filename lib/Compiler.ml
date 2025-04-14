(* Compiler.ml - Compiles OCaml code strings and dynamically links them *)

open! Core
(* REMOVED: open! Core_unix *)

(* Use types from other library modules directly *)
module Value = Value

(* --- Compiler Paths --- *)
(* Use ocamlfind to handle package paths *)
let ocamlfind_path = "ocamlfind"
(* Switch to ocamlopt for native code generation *)
let ocamlopt_path = "ocamlopt"
(* Keep include paths for project's own modules *)
let include_paths = ["_build/default/lib/"]
(* Library paths might still be needed for ocamlfind *)
let library_paths = ["_build/default/lib/"]


exception Compilation_error of string

(* --- Shared State for Loaded Modules --- *)
(* Define a shared ref accessible by both the compiler and dynamically loaded modules. *)
(* The loaded module will mutate this ref to pass back its environment. *)
let last_loaded_environment : (string * Value.t) list option ref = ref None
let unique_generated_module =
    let num_generated = ref 0 in
    fun () ->
      incr num_generated;
      sprintf "scaml_generated_%d" !num_generated

(* --- Compilation Flags --- *)
let keep_compile_artifacts_p = ref false
let keep_compile_artifacts () = !keep_compile_artifacts_p

let compile_verbose_p = ref false (* Moved from Runtime.ml *)
let is_compile_verbose () = !compile_verbose_p (* Accessor added *)


(* Removed Callback registration mechanism *)
(* --- End Shared State --- *)


(** Compiles an OCaml source string to a .cmxs file and loads it *)
(* Modified: Compiles to native code (.cmxs) and returns env list *)
let compile_and_load_string (ocaml_code : string) : (string * Value.t) list =
  let ml_filename = Filename_unix.temp_file (unique_generated_module ()) ".ml" in
  let base_filename = Filename.chop_extension ml_filename in
  (* Native compilation outputs *)
  let cmx_filename = base_filename ^ ".cmx" in
  let o_filename = base_filename ^ ".o" in
  let cmxs_filename = base_filename ^ ".cmxs" in (* Native shared library *)
  let cmi_filename = base_filename ^ ".cmi" in


  (* Reset shared ref before loading the new module *)
  last_loaded_environment := None;

  Exn.protect ~f:(fun () ->
    (* 1. Write the generated OCaml code to the temp .ml file *)
    Out_channel.write_all ml_filename ~data:ocaml_code;

    (* 2. Compile the .ml to .cmx/.o (native object file) *)
    let include_flags = List.map include_paths ~f:(sprintf "-I %s") |> String.concat ~sep:" " in
    (* Use ocamlopt -c. Ensure scaml package is included for interfaces. Keep -linkpkg here. *)
    let compile_native_cmd =
      sprintf "%s %s -package core,scaml -linkpkg -c %s %s"
        ocamlfind_path ocamlopt_path include_flags ml_filename
    in
    (* Print command if verbose *)
    if is_compile_verbose () then printf "Executing Compile: %s\n%!" compile_native_cmd;
    if Sys_unix.command compile_native_cmd <> 0 then
      raise (Compilation_error (sprintf "OCaml native compilation failed for %s. Command: %s" ml_filename compile_native_cmd));

    (* 3. Link the .cmx/.o into a .cmxs (native shared library) *)
    let lib_flags = List.map library_paths ~f:(sprintf "-I %s") |> String.concat ~sep:" " in
    (* Use ocamlopt -shared. Link against scaml package *)
    (* Corrected: Removed -linkpkg from the linking command *)
    let link_native_cmd =
      sprintf "%s %s -package core,scaml -shared %s -o %s %s"
        ocamlfind_path ocamlopt_path lib_flags cmxs_filename cmx_filename
        (* We provide the .cmx, ocamlopt finds the corresponding .o *)
    in
    (* Print command if verbose *)
    if is_compile_verbose () then printf "Executing Link: %s\n%!" link_native_cmd;
    if Sys_unix.command link_native_cmd <> 0 then
       raise (Compilation_error (sprintf "OCaml native linking failed for %s. Command: %s" ml_filename link_native_cmd));

    (* 4. Dynamically load the .cmxs native shared library *)
    (* Dynlink.loadfile works for .cmxs in native executables *)
    (* Printf.printf "Dynlinking: %s\n%!" cmxs_filename; *)
    begin try
      Dynlink.loadfile cmxs_filename
    with Dynlink.Error err ->
        raise (Compilation_error (sprintf "Dynlink error loading %s: %s" cmxs_filename (Dynlink.error_message err)))
    end;

    (* 5. Retrieve the environment from the shared ref *)
    match !last_loaded_environment with
     | None ->
         failwith "Dynamically loaded module failed to set the environment ref"
     | Some env_list ->
         env_list (* Return the environment list directly *)

  ) ~finally:(fun () ->
    (* Clean up temporary files only if keep_compile_artifacts is false *)
    if not (keep_compile_artifacts ()) then (
      (* Printf.printf "Cleaning up temp files for %s\n%!" base_filename; *)
      Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove ml_filename);
      Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cmi_filename);
      Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cmx_filename);
      Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove o_filename);
      Exn.handle_uncaught ~exit:false (fun () -> Sys_unix.remove cmxs_filename);
    ) else (
      Printf.printf "Keeping artifacts for %s: %s %s %s %s %s\n%!"
        base_filename ml_filename cmi_filename cmx_filename o_filename cmxs_filename;
    )
  )


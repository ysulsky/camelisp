(* lib/compiler.mli - Interface for the Compiler module *)

(** Exception raised during compilation or linking *)
exception Compilation_error of string

(** Shared state updated by dynamically loaded modules. *)
val last_loaded_environment : (string * Value.t) list option ref

(** Compiles and loads OCaml code string, returning the environment. *)
val compile_and_load_string : string -> (string * Value.t) list

(** Check if compilation artifacts should be kept. *)
val keep_compile_artifacts : unit -> bool
(** Reference holding the keep_compile_artifacts flag. *)
val keep_compile_artifacts_p : bool ref

(** Check if verbose compilation output is enabled. *)
val is_compile_verbose : unit -> bool
(** Reference holding the compile_verbose flag. *)
val compile_verbose_p : bool ref

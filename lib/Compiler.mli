(* lib/compiler.mli - Interface for the Compiler module *)

(** Exception raised during compilation or linking *)
exception Compilation_error of string

(** Shared state updated by dynamically loaded modules. *)
val last_loaded_environment : (string * Value.t) list option ref

(** Compiles and loads OCaml code string, returning the environment. *)
val compile_and_load_string : string -> (string * Value.t) list

(** Accessor for the flag determining whether to keep temporary compilation files. *)
val keep_compile_artifacts : unit -> bool
val keep_compile_artifacts_p : bool ref

(** Accessor for the flag determining whether to show verbose compilation output. *)
val is_compile_verbose : unit -> bool
val compile_verbose_p : bool ref
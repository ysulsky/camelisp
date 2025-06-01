(* Runtime.ml - Runtime support for translated Elisp code using Core *)

open! Core
(* open! Sexplib.Std - REMOVED *)

(* Use types/modules from the Camelisp library *)
module Value = Value
module InferredType = InferredType (* Keep if needed elsewhere, maybe not? Check usage... Value.t compare uses it implicitly. OK. *)
(* Need access to Compiler module's ref setter logic *)
module Compiler = Compiler


(* --- Error Handling Helpers --- *)
let value_type_to_string v = !Value.to_string v (* Use the ref *)
let type_error func_name expected_type actual_value =
  failwithf "Runtime Error in %s: Type error, expected %s but got %s"
    func_name expected_type (value_type_to_string actual_value) ()
let arity_error func_name message =
  failwithf "Runtime Error in %s: Arity error, %s" func_name message ()
let runtime_error func_name message =
  failwithf "Runtime Error in %s: %s" func_name message ()

(* --- Global Environment --- *)
(* Use String.Table.create as requested *)
let global_env : Value.t String.Table.t =
  String.Table.create ~size:64 ()
let register_global name (value: Value.t) =
  (* Use String.Table functions *)
  Hashtbl.set global_env ~key:name ~data:value
let set_global_variable name (value: Value.t) =
  (* Use String.Table functions *)
  Hashtbl.set global_env ~key:name ~data:value;
  value (* setq returns the value *)
let lookup_variable (name : string) : Value.t =
  (* Use String.Table functions *)
  match Hashtbl.find global_env name with
  | Some v -> v
  | None -> runtime_error "lookup_variable" (sprintf "Variable '%s' is void" name)

(* Function to get all globally defined symbols *)
let get_global_symbols () : string list =
  Hashtbl.keys global_env

(* --- Function Application --- *)
let apply_function (func : Value.t) (args : Value.t list) : Value.t =
  match func with
  | Value.Function f -> f args
  | Value.Builtin f -> f args
  | _ -> runtime_error "apply_function" (sprintf "Attempted to call a non-function value: %s" (value_type_to_string func))

(* --- Basic Helpers --- *)
let is_truthy = Value.is_truthy

(* --- Compile Verbose Flag --- *)
(* Moved flag definition to Compiler.ml *)
(* let compile_verbose_p = ref false *)
(* let is_compile_verbose () = !compile_verbose_p *) (* Accessor now in Compiler.ml *)

(* --- Built-in Function Implementations --- *)
(* Adapted for mutable cons cells *)

let builtin_cons args =
  match args with
  | [a; b] -> Value.Cons { car = a; cdr = b } (* No ref *)
  | _ -> arity_error "cons" (sprintf "expected 2 arguments, got %d" (List.length args))

let builtin_car args =
  match args with
  | [Value.Cons { car; _ }] -> car (* No deref *)
  | [Value.Nil] -> Value.Nil
  | [other] -> type_error "car" "cons cell or nil" other
  | _ -> arity_error "car" (sprintf "expected 1 argument, got %d" (List.length args))

let builtin_cdr args =
   match args with
  | [Value.Cons { cdr; _ }] -> cdr (* No deref *)
  | [Value.Nil] -> Value.Nil
  | [other] -> type_error "cdr" "cons cell or nil" other
  | _ -> arity_error "cdr" (sprintf "expected 1 argument, got %d" (List.length args))

let builtin_setcar args =
  match args with
  | [Value.Cons cell; new_val] -> cell.car <- new_val; new_val (* Use <- *)
  | [not_cons; _] -> type_error "setcar" "cons cell" not_cons
  | _ -> arity_error "setcar" (sprintf "expected 2 arguments, got %d" (List.length args))

let builtin_setcdr args =
   match args with
  | [Value.Cons cell; new_val] -> cell.cdr <- new_val; new_val (* Use <- *)
  | [not_cons; _] -> type_error "setcdr" "cons cell" not_cons
  | _ -> arity_error "setcdr" (sprintf "expected 2 arguments, got %d" (List.length args))

(* list function: takes any number of args and returns them as a list *)
(* Value.list_to_value needs to be adapted if it still uses refs *)
let builtin_list args = Value.list_to_value args


let to_float = function
| Value.Int i -> Float.of_int i
| Value.Float f -> f
| not_number -> type_error "cast_to_float" "number" not_number

let to_int = function
| Value.Int i -> i
| Value.Float f -> Int.of_float f
| not_number -> type_error "cast_to_int" "number" not_number

let with_coerce ~int_fn ~float_fn args =
  let rec any_float = function
  | [] -> false
  | Value.Float _ :: _ -> true
  | _ :: tl -> any_float tl
  in
  if any_float args then
    let args = List.map ~f:to_float args in
    float_fn args
  else
    let args = List.map ~f:to_int args in
    int_fn args

let builtin_plus =
  let int_fn = function
  | [] -> Value.Int 0
  | [i] -> Value.Int i
  | hd :: rest -> Value.Int (List.fold rest ~init:hd ~f:(+))
  in
  let float_fn = function
  | [] -> Value.Float 0.0
  | [f] -> Value.Float f
  | hd :: rest -> Value.Float (List.fold rest ~init:hd ~f:(+.))
  in
  with_coerce ~int_fn ~float_fn

let builtin_multiply =
  let int_fn = function
  | [] -> Value.Int 1
  | [i] -> Value.Int i
  | hd :: rest -> Value.Int (List.fold rest ~init:hd ~f:( * ))
  in
  let float_fn = function
  | [] -> Value.Float 1.0
  | [f] -> Value.Float f
  | hd :: rest -> Value.Float (List.fold rest ~init:hd ~f:( *. ))
  in
  with_coerce ~int_fn ~float_fn

let builtin_minus =
  let int_fn = function
  | [] -> arity_error "-" "requires at least one argument"
  | [i] -> Value.Int (-i)
  | hd :: rest -> Value.Int (List.fold rest ~init:hd ~f:( - ))
  in
  let float_fn = function
  | [] -> arity_error "-" "requires at least one argument"
  | [f] -> Value.Float (-. f)
  | hd :: rest -> Value.Float (List.fold rest ~init:hd ~f:( -. ))
  in
  with_coerce ~int_fn ~float_fn

let builtin_divide =
  let int_fn = function
  | [] -> arity_error "/" "requires at least one argument"
  | [0] -> runtime_error "/" "Arithmetic Error"
  | [_] -> Value.Int 0
  | hd :: rest -> Value.Int (List.fold rest ~init:hd ~f:( / ))
  in
  let float_fn = function
  | [] -> arity_error "/" "requires at least one argument"
  | [f] -> Value.Float (1.0 /. f)
  | hd :: rest -> Value.Float (List.fold rest ~init:hd ~f:( /. ))
  in
  with_coerce ~int_fn ~float_fn


let check_arity n name args =
  if List.length args <> n then
    arity_error name (sprintf "expected %d argument(s), got %d" n (List.length args))

let ret_bool = function true -> Value.T | false -> Value.Nil

let predicate name n p args =
  check_arity n name args;
  if p (List.hd_exn args) then Value.T else Value.Nil

let builtin_consp args = predicate "consp" 1 (function Value.Cons _ -> true | _ -> false) args
let builtin_atom args = predicate "atom" 1 (function Value.Cons _ -> false | _ -> true) args
let builtin_integerp args = predicate "integerp" 1 (function Value.Int _ -> true | _ -> false) args
let builtin_floatp args = predicate "floatp" 1 (function Value.Float _ -> true | _ -> false) args
let builtin_stringp args = predicate "stringp" 1 (function Value.String _ -> true | _ -> false) args
let builtin_symbolp args = predicate "symbolp" 1 (function Value.Symbol _ -> true | _ -> false) args (* Keywords are not symbols in ELisp *)
let builtin_keywordp args = predicate "keywordp" 1 (function Value.Keyword _ -> true | _ -> false) args (* Added Keyword type *)
let builtin_vectorp args = predicate "vectorp" 1 (function Value.Vector _ -> true | _ -> false) args
let builtin_functionp args = predicate "functionp" 1 (function Value.Function _ | Value.Builtin _ -> true | _ -> false) args
let builtin_null args = predicate "null" 1 (function Value.Nil -> true | _ -> false) args

let builtin_listp args =
  check_arity 1 "listp" args;
  let rec is_list l =
    match l with
    | Value.Nil -> true
    | Value.Cons { cdr; _ } -> is_list cdr (* No deref *)
    | _ -> false
  in ret_bool (is_list (List.hd_exn args))

let builtin_eq args =
  check_arity 2 "eq" args;
  let a = List.nth_exn args 0 in
  let b = List.nth_exn args 1 in
  match a, b with
  (* immediates *)
  | Value.Int i1   , Value.Int i2    -> ret_bool (i1 =  i2)
  | Value.Float f1 , Value.Float f2  -> ret_bool (Float.equal f1 f2)
  | Value.Char  c1 , Value.Char  c2  -> ret_bool (Char.equal  c1 c2)
  | Value.T        , Value.T
  | Value.Nil      , Value.Nil       -> Value.T
  (* symbols & keywords → compare their interned names *)
  | Value.Symbol  s1, Value.Symbol  s2 -> ret_bool (String.equal s1.name s2.name)
  | Value.Keyword k1, Value.Keyword k2 -> ret_bool (String.equal k1      k2)
  (* everything else → physical equality *)
  | _ -> ret_bool (phys_equal a b)


let builtin_equal args =
  check_arity 2 "equal" args;
  let a = List.nth_exn args 0 in
  let b = List.nth_exn args 1 in
  (* Custom compare function in Value handles mutable fields if needed *)
  ret_bool ([%compare.equal: Value.t] a b)


(* --- Value Printing (Lisp Style) --- *)
(* Mutually recursive functions for Lisp-style printing *)
let rec value_to_string_lisp_internal (v : Value.t) : string =
  match v with
  | Value.Nil -> "nil" | Value.T -> "t" | Value.Int i -> Int.to_string i
  | Value.Float f -> Float.to_string f | Value.String s -> Printf.sprintf "%S" s
  | Value.Symbol sd -> sd.name | Value.Keyword k -> ":" ^ k
  | Value.Cons { car; cdr } -> "(" ^ cons_to_string_helper car cdr ^ ")" (* No deref *)
  | Value.Vector v -> "[ " ^ String.concat ~sep:" " (Array.to_list (Array.map v ~f:value_to_string_lisp_internal)) ^ " ]"
  | Value.Function _ -> "#<function>" | Value.Builtin _ -> "#<builtin>"
  | Value.Char c -> Printf.sprintf "?%s" (char_to_lisp_string_representation c)

and cons_to_string_helper car cdr =
  let car_str = value_to_string_lisp_internal car in
  match cdr with
  | Value.Nil -> car_str
  | Value.Cons { car = next_car; cdr = next_cdr } -> car_str ^ " " ^ cons_to_string_helper next_car next_cdr (* No deref *)
  | _ -> car_str ^ " . " ^ value_to_string_lisp_internal cdr

and char_to_lisp_string_representation c =
 match c with
  | '\n' -> "\\n" | '\t' -> "\\t" | '\r' -> "\\r" | '\\' -> "\\\\" | ' ' -> " "
  | _ when Char.to_int c >= 32 && Char.to_int c <= 126 -> String.make 1 c
  | _ -> Printf.sprintf "\\%03o" (Char.to_int c)

(* Update the global printer function reference in Value.ml *)
let () = Value.to_string := value_to_string_lisp_internal

(* --- Removed Sexp Conversion Helpers --- *)


let alist_to_value (alist : (string * Value.t) list) : Value.t =
  let value_pairs = List.map alist ~f:(fun (name, v) ->
      (* Create (sym . val) pair *)
      Value.Cons { car = Value.Symbol {name = name}; cdr = v } (* No refs *)
    )
  in
  (* Convert list of pairs into a Value.t list *)
  Value.list_to_value value_pairs (* Assumes list_to_value is also updated *)

(* --- Compile Builtin Implementation --- *)

(* Type signature now uses Value.t list *)
type compile_impl_t = Value.t list -> (string * Value.t) list

(* Reference to hold the registered implementation *)
let compile_impl_ref : compile_impl_t option ref = ref None

(* Function to register the implementation (called from main application) *)
let register_compile_impl (f : compile_impl_t) : unit =
  compile_impl_ref := Some f

(* The 'compile' built-in function *)
let builtin_compile args = (* args has type Value.t list *)
  match args with
  | [ code_value ] -> (* code_value is a single Value.t *)
      begin
        match !compile_impl_ref with
        | None ->
            runtime_error "compile" "Compilation implementation not registered"
        | Some compile_fn -> (* compile_fn expects Value.t list *)
            try
              (* Convert the code_value (Value.t) into an OCaml list *)
              let code_list = match Value.value_to_list_opt code_value with
                | Some l -> l
                | None -> runtime_error "compile" "Argument must be a proper list of expressions"
              in
              let exposed_env_alist = compile_fn code_list in
              alist_to_value exposed_env_alist
            with
            (* Catch potential errors from the compilation pipeline *)
            | Failure msg -> runtime_error "compile" (sprintf "Failed during compilation pipeline: %s" msg)
            | exn -> runtime_error "compile" (sprintf "Unexpected error during compilation: %s" (Exn.to_string exn))
      end
  | _ -> arity_error "compile" (sprintf "expected 1 argument (a quoted list of expressions), got %d" (List.length args))


(* --- Interpret Builtin Implementation --- *)

(* Type signature now uses Value.t list *)
type interpret_impl_t = Value.t list -> Value.t

(* Reference to hold the registered implementation *)
let interpret_impl_ref : interpret_impl_t option ref = ref None

(* Function to register the implementation (called from main application) *)
let register_interpret_impl (f : interpret_impl_t) : unit =
  interpret_impl_ref := Some f

(* The 'interpret' built-in function *)
let builtin_interpret args = (* args has type Value.t list *)
  match args with
  | [ code_value ] -> (* code_value is a single Value.t *)
      begin
        match !interpret_impl_ref with
        | None ->
            runtime_error "interpret" "Interpretation implementation not registered"
        | Some interpret_fn -> (* interpret_fn expects Value.t list *)
            try
              (* Convert the code_value (Value.t) into an OCaml list *)
               let code_list = match Value.value_to_list_opt code_value with
                | Some l -> l
                | None -> runtime_error "interpret" "Argument must be a proper list of expressions"
              in
              let (_last_val : Value.t) = interpret_fn code_list in
              (* Side effects (like defun) modify global_env. *)
              (* Return the current global environment as an alist. *)
              alist_to_value (Hashtbl.to_alist global_env)
            with
            | Failure msg -> runtime_error "interpret" (sprintf "Failed during interpretation: %s" msg)
            | exn -> runtime_error "interpret" (sprintf "Unexpected error during interpretation: %s" (Exn.to_string exn))
      end
  | _ -> arity_error "interpret" (sprintf "expected 1 argument (a quoted list of expressions), got %d" (List.length args))

(* --- Assoc Builtin Implementation (Reverted) --- *)

(* Original implementation for (assoc KEY ALIST) *)
let builtin_assoc args =
  match args with
  | [ key; alist_val ] -> (* key is arg1, alist_val is arg2 *)
      let rec find_in_alist lst =
        match lst with
        | Value.Nil -> Value.Nil (* Not found *)
        | Value.Cons { car = pair; cdr = rest } ->
            (match pair with
             | Value.Cons { car = item_key; cdr = _ } ->
                 (* Compare the key we're looking for (key from outer scope) with the item's key *)
                 if [%compare.equal: Value.t] key item_key then
                   pair (* Found the pair *)
                 else
                   find_in_alist rest (* Check rest of the list *)
             | _ -> find_in_alist rest (* Skip malformed pair (element wasn't a cons cell) *)
            )
        | _ -> runtime_error "assoc" "Second argument must be a proper association list" (* Error if lst is not Nil or Cons *)
      in
      find_in_alist alist_val (* <<< Start search with the ALIST argument (alist_val) *)
  | _ -> arity_error "assoc" (sprintf "expected 2 arguments (key alist), got %d" (List.length args))

(* --- Funcall and Apply (Lisp-2) --- *)

(* Assumes args passed ARE ALREADY EVALUATED by the interpreter *)
let builtin_funcall args =
  match args with
  | [] -> arity_error "funcall" "requires at least 1 argument (function)"
  | func_val :: actual_args -> (* func_val is already evaluated Value.t *)
      let func_to_call =
        match func_val with
         | (Value.Function _ | Value.Builtin _) as f -> f
         (* In strict Elisp, funcall doesn't auto-lookup symbols. It expects a function object. *)
         (* However, many Lisps allow symbols if their function cell holds a function. *)
         (* Let's allow symbols here by looking up their GLOBAL value. *)
         | Value.Symbol { name } ->
              (match lookup_variable name with (* Check global var/fun env *)
                | (Value.Function _ | Value.Builtin _) as f -> f
                | _ -> type_error "funcall" (sprintf "function held by symbol '%s'" name) func_val)
         | other -> type_error "funcall" "function or symbol" other
      in
      apply_function func_to_call actual_args (* Apply to already evaluated args *)

let builtin_apply args =
    match args with
    | [func_val; args_list_val] -> (* Exactly 2 evaluated args *)
        let func_to_call =
             match func_val with
             | (Value.Function _ | Value.Builtin _) as f -> f
             (* Allow symbols similar to funcall *)
             | Value.Symbol { name } ->
                  (match lookup_variable name with (* Check global var/fun env *)
                    | (Value.Function _ | Value.Builtin _) as f -> f
                    | _ -> type_error "apply" (sprintf "function held by symbol '%s'" name) func_val)
             | other -> type_error "apply" "function or symbol" other
        in
        (* The args list itself needs to be evaluated, but value_to_list_opt operates on the Value.t *)
        let actual_args = match Value.value_to_list_opt args_list_val with
            | Some l -> l
            | None -> type_error "apply" "proper list for arguments" args_list_val
        in
        apply_function func_to_call actual_args
    | _ -> arity_error "apply" "takes exactly 2 arguments: function and list"


(* --- Setter for Compile Verbose Flag --- *)
let builtin_set_compile_verbose args =
  match args with
  | [ flag_val ] ->
      Compiler.compile_verbose_p := Value.is_truthy flag_val; (* Set the flag in Compiler module *)
      flag_val (* Return the flag value passed *)
  | _ -> arity_error "set-compile-verbose" "expected 1 argument (t or nil)"

(* --- Setter for Keep Artifacts Flag --- *)
let builtin_set_keep_compile_artifacts args =
  match args with
  | [ flag_val ] ->
      Compiler.keep_compile_artifacts_p := Value.is_truthy flag_val; (* Set the flag in Compiler module *)
      flag_val (* Return the flag value passed *)
  | _ -> arity_error "set-keep-compile-artifacts" "expected 1 argument (t or nil)"


(* --- Register Built-ins --- *)
let register name func = register_global name (Value.Builtin func)
let () =
  (* List Functions *)
  register "cons" builtin_cons; register "car" builtin_car; register "cdr" builtin_cdr;
  register "setcar" builtin_setcar; register "setcdr" builtin_setcdr;
  register "assoc" builtin_assoc;
  register "list" builtin_list; (* Added list *)
  (* Arithmetic Functions *)
  register "+" builtin_plus; register "-" builtin_minus; register "*" builtin_multiply; register "/" builtin_divide;
  (* Type Predicates *)
  register "consp" builtin_consp; register "atom" builtin_atom; register "integerp" builtin_integerp;
  register "floatp" builtin_floatp; register "stringp" builtin_stringp; register "symbolp" builtin_symbolp;
  register "keywordp" builtin_keywordp; register "vectorp" builtin_vectorp; register "functionp" builtin_functionp;
  register "null" builtin_null; register "listp" builtin_listp;
  (* Equality *)
  register "eq" builtin_eq; register "equal" builtin_equal;
  (* Execution Modes *)
  register "compile" builtin_compile; (* Uses registered implementation *)
  register "interpret" builtin_interpret; (* Uses registered implementation *)
  (* Settings *)
  register "set-compile-verbose" builtin_set_compile_verbose;
  register "set-keep-compile-artifacts" builtin_set_keep_compile_artifacts; (* Added *)
  (* Lisp-2 Functions *)
  register "funcall" builtin_funcall;
  register "apply" builtin_apply;
  (* Constants *)
  register_global "nil" Value.Nil; register_global "t" Value.T;
  ()


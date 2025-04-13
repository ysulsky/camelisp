(* Runtime.ml - Runtime support for translated Elisp code using Core *)

open! Core
(* REMOVED open! Scaml *)

(* Use types from other library modules directly *)
module Value = Value
module Analyze = Analyze
module InferredType = InferredType

(* --- Error Handling Helpers --- *)
let value_type_to_string v = Value.to_string v
let type_error func_name expected_type actual_value =
  failwithf "Runtime Error in %s: Type error, expected %s but got %s"
    func_name expected_type (value_type_to_string actual_value) ()
let arity_error func_name message =
  failwithf "Runtime Error in %s: Arity error, %s" func_name message ()
let runtime_error func_name message =
  failwithf "Runtime Error in %s: %s" func_name message ()

(* --- Global Environment --- *)
let global_env : Value.t Hashtbl.M(String).t =
  Hashtbl.create (module String) ~size:64
let register_global name (value: Value.t) =
  Hashtbl.set global_env ~key:name ~data:value
let set_global_variable name (value: Value.t) =
  Hashtbl.set global_env ~key:name ~data:value;
  value (* setq returns the value *)
let lookup_variable (name : string) : Value.t =
  match Hashtbl.find global_env name with
  | Some v -> v
  | None -> runtime_error "lookup_variable" (sprintf "Variable '%s' is void" name)

(* --- Function Application --- *)
let apply_function (func : Value.t) (args : Value.t list) : Value.t =
  match func with
  | Value.Function f -> f args
  | Value.Builtin f -> f args
  | _ -> runtime_error "apply_function" (sprintf "Attempted to call a non-function value: %s" (value_type_to_string func))

(* --- Basic Helpers --- *)
let is_truthy = Value.is_truthy

(* --- Built-in Function Implementations --- *)

let builtin_cons args =
  match args with
  | [a; b] -> Value.Cons { car = ref a; cdr = ref b } (* Use ref directly *)
  | _ -> arity_error "cons" (sprintf "expected 2 arguments, got %d" (List.length args))

let builtin_car args =
  match args with
  | [Value.Cons { car; _ }] -> !car
  | [Value.Nil] -> Value.Nil
  | [other] -> type_error "car" "cons cell or nil" other
  | _ -> arity_error "car" (sprintf "expected 1 argument, got %d" (List.length args))

let builtin_cdr args =
   match args with
  | [Value.Cons { cdr; _ }] -> !cdr
  | [Value.Nil] -> Value.Nil
  | [other] -> type_error "cdr" "cons cell or nil" other
  | _ -> arity_error "cdr" (sprintf "expected 1 argument, got %d" (List.length args))

let builtin_setcar args =
  match args with
  | [Value.Cons cell; new_val] -> cell.car := new_val; new_val (* Use record field *)
  | [not_cons; _] -> type_error "setcar" "cons cell" not_cons
  | _ -> arity_error "setcar" (sprintf "expected 2 arguments, got %d" (List.length args))

let builtin_setcdr args =
   match args with
  | [Value.Cons cell; new_val] -> cell.cdr := new_val; new_val (* Use record field *)
  | [not_cons; _] -> type_error "setcdr" "cons cell" not_cons
  | _ -> arity_error "setcdr" (sprintf "expected 2 arguments, got %d" (List.length args))


(* Simplified Arithmetic - Assume integers for now *)
let builtin_plus args =
  List.fold args ~init:(Value.Int 0) ~f:(fun acc v ->
    match acc, v with
    | Value.Int ia, Value.Int iv -> Value.Int (ia + iv)
    | _, other -> type_error "+" "integer" other
  )
let builtin_minus args =
  match args with
  | [] -> Value.Int 0 (* (-) -> 0 *)
  | [Value.Int i] -> Value.Int (-i) (* (- 5) -> -5 *)
  | Value.Int start :: rest ->
      List.fold rest ~init:(Value.Int start) ~f:(fun acc v ->
        match acc, v with
        | Value.Int ia, Value.Int iv -> Value.Int (ia - iv)
        | _, other -> type_error "-" "integer" other
      )
  | other :: _ -> type_error "-" "integer" other (* First arg not integer *)

let builtin_multiply args =
  List.fold args ~init:(Value.Int 1) ~f:(fun acc v ->
      match acc, v with
      | Value.Int ia, Value.Int iv -> Value.Int (ia * iv)
      | _, other -> type_error "*" "integer" other
    )

let builtin_divide args =
  match args with
  | [] -> runtime_error "/" "requires at least one argument"
  | [Value.Int i] -> (* (/ 5) -> 1/5 is 0 in integer division *)
      if i = 0 then runtime_error "/" "division by zero"
      else Value.Int (1 / i) (* Or maybe raise error for single arg? Emacs gives 0 *)
  | Value.Int start :: rest ->
      List.fold rest ~init:(Value.Int start) ~f:(fun acc v ->
        match acc, v with
        | Value.Int ia, Value.Int iv ->
            if iv = 0 then runtime_error "/" "division by zero"
            else Value.Int (ia / iv)
        | _, other -> type_error "/" "integer" other
      )
  | other :: _ -> type_error "/" "integer" other


let check_arity n name args =
  if List.length args <> n then
    arity_error name (sprintf "expected %d argument(s), got %d" n (List.length args))

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
    | Value.Cons { cdr; _ } -> is_list !cdr
    | _ -> false
  in
  if is_list (List.hd_exn args) then Value.T else Value.Nil


let builtin_eq args =
  check_arity 2 "eq" args;
  let a = List.nth_exn args 0 in
  let b = List.nth_exn args 1 in
  (* Physical equality for non-immediate types, value equality for immediate *)
   match a, b with
   | Value.Int i1, Value.Int i2 -> if i1 = i2 then Value.T else Value.Nil
   | Value.Float f1, Value.Float f2 -> if Float.equal f1 f2 then Value.T else Value.Nil (* Use Float.equal *)
   | Value.Char c1, Value.Char c2 -> if Char.equal c1 c2 then Value.T else Value.Nil (* Added Char *)
   | Value.Nil, Value.Nil -> Value.T
   | Value.T, Value.T -> Value.T
   | _, _ -> if phys_equal a b then Value.T else Value.Nil (* Reference equality for others *)

let builtin_equal args =
  check_arity 2 "equal" args;
  let a = List.nth_exn args 0 in
  let b = List.nth_exn args 1 in
  if [%compare.equal: Value.t] a b then Value.T else Value.Nil (* Use derived Core equality *)


(* --- Value <-> Sexp Conversion Helpers (Simplified) --- *)
(* These are needed for the 'compile' builtin if it handles Sexp directly *)
let rec sexp_to_value (s : Sexp.t) : Value.t =
  match s with
  | Sexp.Atom "nil" -> Value.Nil
  | Sexp.Atom "t" -> Value.T
  | Sexp.Atom str ->
      (try Value.Int (Int.of_string str) with _ ->
      try Value.Float (Float.of_string str) with _ ->
      if String.is_prefix str ~prefix:":"
      then Value.Keyword (String.drop_prefix str 1)
      else Value.Symbol { name = str }) (* Treat others as symbols *)
  | Sexp.List [] -> Value.Nil
  | Sexp.List l -> list_to_value (List.map l ~f:sexp_to_value)
and list_to_value = function (* Helper *)
  | [] -> Value.Nil
  | h :: t -> Value.Cons { car = ref h; cdr = ref (list_to_value t) }

let rec value_to_sexp (v : Value.t) : Sexp.t =
  match v with
  | Value.Nil -> Sexp.Atom "nil"
  | Value.T -> Sexp.Atom "t"
  | Value.Int i -> Sexp.Atom (Int.to_string i)
  | Value.Float f -> Sexp.Atom (Float.to_string f)
  | Value.String s -> Sexp.Atom s (* Represent string as atom for simplicity? *)
  | Value.Symbol sd -> Sexp.Atom sd.name
  | Value.Keyword k -> Sexp.Atom (":" ^ k)
  | Value.Cons { car; cdr } -> Sexp.List (value_to_sexp !car :: list_sexp !cdr)
  | Value.Vector arr -> Sexp.List (Sexp.Atom "vector" :: List.map (Array.to_list arr) ~f:value_to_sexp)
  | Value.Function _ -> Sexp.Atom "<function>"
  | Value.Builtin _ -> Sexp.Atom "<builtin>"
  | Value.Char c -> Sexp.Atom (String.of_char c) (* Added Char *)
and list_sexp v = match v with (* Helper for proper lists *)
    | Value.Nil -> []
    | Value.Cons {car; cdr} -> value_to_sexp !car :: list_sexp !cdr
    | other -> [Sexp.Atom "."; value_to_sexp other] (* Dotted pair *)


let value_list_to_sexp_list (code_value : Value.t) : Sexp.t list =
  match Value.value_to_list_opt code_value with
  | Some values -> List.map values ~f:value_to_sexp
  | None -> runtime_error "compile" "Argument must be a proper list of S-expressions"


let alist_to_value (alist : (string * Value.t) list) : Value.t =
  let value_pairs = List.map alist ~f:(fun (name, v) ->
      Value.Cons { car = ref (Value.Symbol {name = name}); cdr = ref v }
    )
  in
  list_to_value value_pairs


(** Compile Builtin: Simplified to break dependency cycle *)
let builtin_compile args =
  match args with
  | [ code_value ] ->
      begin
        try
          (* 1. Convert Value.t list back to Sexp.t list *)
          let sexps = value_list_to_sexp_list code_value in

          (* 2. Analyze *)
          let _typed_asts, _final_env_types = Analyze.analyze_toplevel sexps in

          (* 3. Translate - REMOVED to break cycle *)
          (* let ocaml_code = Translate.translate_toplevel typed_asts final_env_types in *)

          (* 4. Add registration code - REMOVED *)

          (* 5. Compile and Load - REMOVED *)
          (* let _, get_env_func = Compiler.compile_and_load_string final_ocaml_code in *)

          (* 6. Get environment and convert to Value.t - REMOVED *)
          (* let exposed_env = get_env_func () in *)
          (* alist_to_value exposed_env *)

          (* Simplification: Return Nil for now *)
          Value.Nil

        with
        | Failure msg -> runtime_error "compile" (sprintf "Failed during analysis: %s" msg)
        (* Compiler.Compilation_error removed *)
        | exn -> runtime_error "compile" (sprintf "Unexpected error during analysis: %s" (Exn.to_string exn))
      end
  | _ -> arity_error "compile" (sprintf "expected 1 argument (a quoted list of expressions), got %d" (List.length args))


(* --- Register Built-ins --- *)
let register name func = register_global name (Value.Builtin func)
let () =
  (* List Functions *)
  register "cons" builtin_cons; register "car" builtin_car; register "cdr" builtin_cdr;
  register "setcar" builtin_setcar; register "setcdr" builtin_setcdr;
  (* Arithmetic Functions *)
  register "+" builtin_plus; register "-" builtin_minus; register "*" builtin_multiply; register "/" builtin_divide;
  (* Type Predicates *)
  register "consp" builtin_consp; register "atom" builtin_atom; register "integerp" builtin_integerp;
  register "floatp" builtin_floatp; register "stringp" builtin_stringp; register "symbolp" builtin_symbolp;
  register "keywordp" builtin_keywordp; register "vectorp" builtin_vectorp; register "functionp" builtin_functionp;
  register "null" builtin_null; register "listp" builtin_listp;
  (* Equality *)
  register "eq" builtin_eq; register "equal" builtin_equal;
  (* Compilation *)
  register "compile" builtin_compile; (* Keep registration, but simplified behavior *)
  (* Constants *)
  register_global "nil" Value.Nil; register_global "t" Value.T;
  ()

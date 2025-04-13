(* Analyze.ml - Static Type Analysis for Elisp S-expressions *)

open! Core
open! Sexplib.Std

(* Use types from other library modules directly *)
module Value = Value
module InferredType = InferredType
(* REMOVED: module Runtime = Runtime *)

(* --- Typed Abstract Syntax Tree (TAST) --- *)
module TypedAst = struct
  type t =
    | Atom of { sexp: Sexp.t; inferred_type: InferredType.t }
    | Quote of { sexp: Sexp.t; inferred_type: InferredType.t }
    | If of {
        cond: t;
        then_branch: t;
        else_branch: t option;
        inferred_type: InferredType.t
      }
    | Progn of { forms: t list; inferred_type: InferredType.t }
    | Let of {
        bindings: (string * t) list;
        body: t list;
        inferred_type: InferredType.t
      }
    | LetStar of {
        bindings: (string * t) list;
        body: t list;
        inferred_type: InferredType.t
      }
    | Setq of { pairs: (string * t) list; inferred_type: InferredType.t }
    | Lambda of {
        args: InferredType.arg_spec;
        body: t list;
        inferred_type: InferredType.t
      }
    | Defun of {
        name: string;
        args: InferredType.arg_spec;
        body: t list;
        fun_type: InferredType.t; (* Type of the function itself *)
        inferred_type: InferredType.t (* Type of the defun expression (usually symbol) *)
      }
    | Cond of { clauses: (t * t list) list; inferred_type: InferredType.t }
    | Funcall of { func: t; args: t list; inferred_type: InferredType.t }
  [@@deriving sexp_of]

  (* Function to extract the inferred type from any TAST node *)
  let get_type (node : t) : InferredType.t =
    match node with
    | Atom { inferred_type=t; _ } -> t | Quote { inferred_type=t; _ } -> t
    | If { inferred_type=t; _ } -> t | Progn { inferred_type=t; _ } -> t
    | Let { inferred_type=t; _ } -> t | LetStar { inferred_type=t; _ } -> t
    | Setq { inferred_type=t; _ } -> t | Lambda { inferred_type=t; _ } -> t
    | Defun { inferred_type=t; _ } -> t | Cond { inferred_type=t; _ } -> t
    | Funcall { inferred_type=t; _ } -> t
end

(* --- Argument List Parsing --- *)
module ArgListParser = struct
  (* Re-expose the type for clarity within this module *)
  type arg_spec = InferredType.arg_spec = {
    required: string list;
    optional: (string * Sexp.t option) list;
    rest: string option;
  } [@@deriving sexp_of]

  (* Function to parse an S-expression representing a lambda list *)
  let parse (arg_list_sexp : Sexp.t) : arg_spec =
    match arg_list_sexp with
    | Sexp.List arg_list_ast ->
        (* Internal recursive helper function *)
        let rec parse_internal state rev_required rev_optional rest_opt ast =
          match state, ast with
          (* Transition states based on keywords *)
          | `Required, Sexp.Atom "&optional" :: rest_ast ->
              parse_internal `Optional rev_required rev_optional rest_opt rest_ast
          | `Required, Sexp.Atom "&rest" :: rest_ast ->
              parse_internal `Rest rev_required rev_optional rest_opt rest_ast
          | `Optional, Sexp.Atom "&rest" :: rest_ast ->
              parse_internal `Rest rev_required rev_optional rest_opt rest_ast

          (* Handle required arguments *)
          | `Required, Sexp.Atom name :: rest_ast ->
              parse_internal `Required (name :: rev_required) rev_optional rest_opt rest_ast
          | `Required, [] -> (* End of list while in required state *)
              { required = List.rev rev_required; optional = []; rest = None }

          (* Handle optional arguments *)
          | `Optional, Sexp.Atom name :: rest_ast -> (* Optional without default *)
              parse_internal `Optional rev_required ((name, None) :: rev_optional) rest_opt rest_ast
          | `Optional, Sexp.List [Sexp.Atom name; default_form] :: rest_ast -> (* Optional with default *)
              parse_internal `Optional rev_required ((name, Some default_form) :: rev_optional) rest_opt rest_ast
          | `Optional, [] -> (* End of list while in optional state *)
              { required = List.rev rev_required; optional = List.rev rev_optional; rest = None }

          (* Handle rest argument *)
          | `Rest, Sexp.Atom name :: [] -> (* &rest followed by one symbol *)
              { required = List.rev rev_required; optional = List.rev rev_optional; rest = Some name }
          | `Rest, _ -> (* Error: &rest not followed by exactly one symbol *)
              failwith "Malformed &rest argument: must be followed by exactly one symbol"

          (* Error handling for invalid elements *)
          | _, other :: _ ->
              failwithf "Invalid element in lambda list: %s" (Sexp.to_string_hum other) ()
        in
        (* Start parsing in the 'Required' state *)
        parse_internal `Required [] [] None arg_list_ast
    | _ -> failwith "Lambda list must be a list" (* Input wasn't a list *)
end


(* --- Analysis Environment --- *)
(* Environment maps Elisp variable names (string) to their inferred types *)
type analysis_env = (string * InferredType.t) list [@@deriving sexp_of]
let add_binding env name inferred_type = (name, inferred_type) :: env
let add_bindings env bindings = bindings @ env

(* --- Unification --- *)
(* Substitution maps type variable names (string) to inferred types *)
module Subst = String.Map
type substitution = InferredType.t Subst.t [@@deriving sexp_of]
exception Unification_error of string

(* Apply a substitution to a type, replacing variables bound in the substitution *)
let rec apply_subst (subst : substitution) (t : InferredType.t) : InferredType.t =
  match t with
  (* If it's a variable, look it up in the substitution *)
  | InferredType.T_Var v ->
      (match Map.find subst v with
       | Some bound_t -> apply_subst subst bound_t (* Recursively apply to the bound type *)
       | None -> t) (* Variable not in substitution, return it as is *)
  (* Recursively apply substitution to components of complex types *)
  | InferredType.T_Cons info ->
      InferredType.T_Cons { car_type = apply_subst subst info.car_type;
                            cdr_type = apply_subst subst info.cdr_type }
  | InferredType.T_Vector info ->
      InferredType.T_Vector { element_type = apply_subst subst info.element_type }
  | InferredType.T_Function info ->
      InferredType.T_Function {
        arg_types = Option.map info.arg_types
                      ~f:(List.map ~f:(apply_subst subst));
        return_type = apply_subst subst info.return_type
      }
  | InferredType.T_Union s ->
      (* Apply substitution to each type in the union set *)
      InferredType.normalize_union_set
        (InferredType.InferredTypeSet.map s ~f:(apply_subst subst))
  (* Base types are unaffected by substitution *)
  | InferredType.T_Unknown | InferredType.T_Any | InferredType.T_Nil
  | InferredType.T_Bool | InferredType.T_Int | InferredType.T_Float
  | InferredType.T_Char | InferredType.T_String | InferredType.T_Symbol
  | InferredType.T_Keyword as other -> other


(* Compose two substitutions. Apply s1 to the types in s2, then merge. *)
let compose_subst (s1 : substitution) (s2 : substitution) : substitution =
  let s2_mapped = Subst.map s2 ~f:(apply_subst s1) in
  (* Merge, preferring bindings from s1 in case of overlap (s1 is applied "first") *)
  Map.merge_skewed s1 s2_mapped ~combine:(fun ~key:_ v1 _ -> v1)

(* Check if a type variable `var_name` occurs within type `t` *)
let rec occurs_check (var_name : string) (t : InferredType.t) : bool =
  match t with
  | InferredType.T_Var v -> String.equal v var_name
  | InferredType.T_Cons { car_type; cdr_type } ->
      occurs_check var_name car_type || occurs_check var_name cdr_type
  | InferredType.T_Vector { element_type } -> occurs_check var_name element_type
  | InferredType.T_Function { arg_types; return_type } ->
      (match arg_types with
       | None -> false
       | Some types -> List.exists types ~f:(occurs_check var_name))
      || occurs_check var_name return_type
  | InferredType.T_Union s -> Set.exists s ~f:(occurs_check var_name)
  | InferredType.T_Unknown | InferredType.T_Any | InferredType.T_Nil
  | InferredType.T_Bool | InferredType.T_Int | InferredType.T_Float
  | InferredType.T_Char | InferredType.T_String | InferredType.T_Symbol
  | InferredType.T_Keyword -> false

(* Unify two types, returning a substitution that makes them equal, or raising Unification_error *)
let rec unify (t1 : InferredType.t) (t2 : InferredType.t) : substitution =
  (* If types are already equal, no substitution needed *)
  if [%compare.equal: InferredType.t] t1 t2 then Subst.empty
  else match (t1, t2) with
  (* Unifying a variable with a type (or vice versa) *)
  | (InferredType.T_Var v, t) | (t, InferredType.T_Var v) -> unify_var v t
  (* Unifying two cons cells: unify car and cdr types *)
  | (InferredType.T_Cons c1, InferredType.T_Cons c2) -> unify_cons c1 c2
  (* Unifying two vectors: unify element types *)
  | (InferredType.T_Vector v1, InferredType.T_Vector v2) -> unify_vector v1 v2
  (* Unifying two functions: unify return types and argument types *)
  | (InferredType.T_Function f1, InferredType.T_Function f2) -> unify_fun f1 f2
  (* Unifying unions: Simplified - return empty substitution. Could be more complex. *)
  | (InferredType.T_Union _, InferredType.T_Union _) -> Subst.empty
  | (InferredType.T_Union _, _) | (_, InferredType.T_Union _) -> Subst.empty
  (* Unifying with Any or Unknown always succeeds *)
  | (InferredType.T_Any, _) | (_, InferredType.T_Any) -> Subst.empty
  | (InferredType.T_Unknown, _) | (_, InferredType.T_Unknown) -> Subst.empty
  (* Cannot unify two different concrete types *)
  | _ ->
      let msg = sprintf "Cannot unify different concrete types: %s / %s"
                  (InferredType.to_string t1) (InferredType.to_string t2) in
      raise (Unification_error msg)

(* Helper for unifying a variable `var_name` with type `t` *)
and unify_var (var_name : string) (t : InferredType.t) : substitution =
  match t with
  (* If unifying variable with itself, return empty substitution *)
  | InferredType.T_Var v when String.equal v var_name -> Subst.empty
  (* Binding a variable to Any or Unknown is trivial *)
  | InferredType.T_Any | InferredType.T_Unknown -> Subst.empty
  (* Otherwise, check for recursive types (occurs check) *)
  | _ ->
      if occurs_check var_name t then
        let msg = sprintf "Recursive type error (occurs check): %s occurs in %s"
                    var_name (InferredType.to_string t) in
        raise (Unification_error msg)
      else
        (* Bind the variable to the type *)
        Subst.singleton var_name t

(* Helper for unifying two cons cells *)
and unify_cons (c1 : InferredType.cons_info) (c2 : InferredType.cons_info)
    : substitution =
  (* Unify car types *)
  let s1 = unify c1.car_type c2.car_type in
  (* Unify cdr types, applying the substitution from the car unification first *)
  let s2 = unify (apply_subst s1 c1.cdr_type) (apply_subst s1 c2.cdr_type) in
  (* Compose the substitutions *)
  compose_subst s1 s2

(* Helper for unifying two vectors *)
and unify_vector (v1 : InferredType.vector_info) (v2 : InferredType.vector_info)
    : substitution =
  (* Unify element types *)
  unify v1.element_type v2.element_type

(* Helper for unifying two function types *)
and unify_fun (f1 : InferredType.fun_info) (f2 : InferredType.fun_info)
    : substitution =
  (* Unify return types first *)
  let s1 = unify f1.return_type f2.return_type in
  (* Unify argument types *)
  match (f1.arg_types, f2.arg_types) with
  | (Some args1, Some args2) ->
      (* Check arity *)
      if List.length args1 <> List.length args2 then
         raise (Unification_error "Function types have different arity")
      else
        (* Unify argument types pairwise, accumulating substitutions *)
        List.fold2_exn args1 args2 ~init:s1
          ~f:(fun current_subst arg1 arg2 ->
            (* Apply current substitution before unifying next pair *)
            let s_arg = unify (apply_subst current_subst arg1)
                               (apply_subst current_subst arg2) in
            compose_subst current_subst s_arg
          )
  | (None, None) -> s1 (* Both unknown args, assume compatible *)
  | (Some _, None) | (None, Some _) ->
      (* One known, one unknown. Assume compatible for now. *)
      s1
      (* Could raise error: raise (Unification_error "Cannot unify functions with known vs. unknown argument lists") *)


(* --- Type Variable Instantiation --- *)
let type_var_instantiation_counter = ref 0

(* Generate a fresh type variable name *)
let generate_fresh_type_var () : InferredType.t =
  incr type_var_instantiation_counter;
  InferredType.T_Var (sprintf "a%d" !type_var_instantiation_counter)

(* Instantiate a type scheme by replacing all type variables with fresh ones *)
let instantiate_type (t : InferredType.t) : InferredType.t * substitution =
  let subst_ref = ref Subst.empty in (* Substitution map for this instantiation *)
  let rec inst ty = match ty with
    (* Use fully qualified constructors in pattern matching *)
    | InferredType.T_Var v ->
        (match Map.find !subst_ref v with
         | Some fresh_var -> fresh_var (* Already created a fresh var for this scope *)
         | None ->
             (* Create a new fresh variable and record it *)
             let fresh_var = generate_fresh_type_var() in
             subst_ref := Map.add_exn !subst_ref ~key:v ~data:fresh_var;
             fresh_var)
    | InferredType.T_Cons info ->
        InferredType.T_Cons { car_type = inst info.car_type;
                              cdr_type = inst info.cdr_type }
    | InferredType.T_Vector info ->
        InferredType.T_Vector { element_type = inst info.element_type }
    | InferredType.T_Function info ->
        InferredType.T_Function { arg_types = Option.map info.arg_types ~f:(List.map ~f:inst);
                                  return_type = inst info.return_type }
    | InferredType.T_Union s ->
        InferredType.normalize_union_set (InferredType.InferredTypeSet.map s ~f:inst)
    (* Base types remain the same *)
    | InferredType.T_Unknown | InferredType.T_Any | InferredType.T_Nil
    | InferredType.T_Bool | InferredType.T_Int | InferredType.T_Float
    | InferredType.T_Char | InferredType.T_String | InferredType.T_Symbol
    | InferredType.T_Keyword as other -> other
  in
  let instantiated_type = inst t in
  (instantiated_type, !subst_ref) (* Return the instantiated type and the substitution used *)


(* Instantiate a function signature (arg types and return type) *)
let instantiate_fun_sig (finfo : InferredType.fun_info)
    : (InferredType.t list option * InferredType.t) =
  (* Wrap in T_Function to use instantiate_type *)
  let temp_fun_type = InferredType.T_Function finfo in
  let instantiated_type, _ = instantiate_type temp_fun_type in
  match instantiated_type with
  | InferredType.T_Function finfo_inst -> (finfo_inst.arg_types, finfo_inst.return_type)
  | _ -> failwith "Internal error: Instantiation changed type structure"

(* --- Analysis of Quoted Data (from Sexp) --- *)
(* Determine the InferredType of a quoted S-expression *)
let rec type_of_quoted_data (sexp : Sexp.t) : InferredType.t =
  match sexp with
  | Sexp.Atom s ->
      (* Try parsing as Int, Float, check for nil/t, keyword, default to Symbol *)
      (try InferredType.T_Int with Failure _ ->
      try InferredType.T_Float with Failure _ ->
      if String.equal s "nil" then InferredType.T_Nil
      else if String.equal s "t" then InferredType.T_Bool (* Treat 't' as Bool in quotes *)
      else if String.is_prefix s ~prefix:":" then InferredType.T_Keyword
      else InferredType.T_Symbol)
  | Sexp.List [] -> InferredType.T_Nil (* Empty list is nil *)
  | Sexp.List (h :: t) ->
      (* Recursively determine car and cdr types *)
      let car_t = type_of_quoted_data h in
      let cdr_t = type_of_quoted_data (Sexp.List t) in
      InferredType.T_Cons { car_type = car_t; cdr_type = cdr_t }

(* --- Built-in Function Type Signatures --- *)
(* Define some common type variables *)
let tvar_a = InferredType.T_Var "a"
let tvar_b = InferredType.T_Var "b"
let tvar_list_a = InferredType.T_Cons { car_type = tvar_a; cdr_type = InferredType.T_Any } (* Simplified list type *)

(* Provide type signatures for known built-in functions *)
let get_builtin_signature (name : string) : InferredType.fun_info option =
  let open InferredType in (* Allow direct use of constructors T_Int, T_Any etc. *)
  match name with
  (* Arithmetic: Assume varargs Int -> Int for simplicity *)
  | "+" | "*" | "-" | "/" -> Some { arg_types = None; return_type = T_Int }
  (* List/Cons *)
  | "car" ->
      let input_type = type_union (T_Cons { car_type = tvar_a; cdr_type = T_Any }) T_Nil in
      Some { arg_types = Some [input_type]; return_type = type_union tvar_a T_Nil }
  | "cdr" ->
      let input_type = type_union (T_Cons { car_type = T_Any; cdr_type = tvar_b }) T_Nil in
      Some { arg_types = Some [input_type]; return_type = type_union tvar_b T_Nil }
  | "cons" ->
      Some { arg_types = Some [tvar_a; tvar_b];
             return_type = T_Cons { car_type = tvar_a; cdr_type = tvar_b } }
  (* Predicates: Any -> Bool *)
  | "integerp" | "stringp" | "symbolp" | "consp" | "listp" | "null"
  | "vectorp" | "floatp" | "keywordp" | "atom" | "functionp" ->
      Some { arg_types = Some [T_Any]; return_type = T_Bool }
  (* Equality: a -> a -> Bool *)
  | "eq" | "equal" ->
      Some { arg_types = Some [tvar_a; tvar_a]; return_type = T_Bool }
  (* Special forms / others *)
  | "compile" -> (* Simplified signature *)
      Some { arg_types = Some [T_Any]; return_type = T_Any }
  | _ -> None (* Unknown function *)


(* --- Helper to analyze progn-like body --- *)
(* Analyzes a sequence of expressions, returning list of TAST nodes, final substitution, and type of the last expression *)
let rec analyze_progn_body env body_sexps
    : TypedAst.t list * substitution * InferredType.t =
  (* Fold over expressions, accumulating TAST nodes and substitutions *)
  let typed_body, final_subst =
    List.fold body_sexps ~init:([], Subst.empty)
      ~f:(fun (acc_nodes, acc_subst) sexp ->
        (* Apply accumulated substitution to the environment for the next expression *)
        let current_env =
          List.map env ~f:(fun (name, ty) -> (name, apply_subst acc_subst ty)) in
        (* Analyze the current expression *)
        let typed_node, node_subst = analyze_expr current_env sexp in
        (* Add node and compose substitutions *)
        (acc_nodes @ [typed_node], compose_subst acc_subst node_subst)
      )
  in
  (* Result type is the type of the last expression, after applying final substitution *)
  let result_type =
    match List.last typed_body with
    | None -> InferredType.T_Nil (* Progn with no forms returns nil *)
    | Some last -> apply_subst final_subst (TypedAst.get_type last)
  in
  (typed_body, final_subst, result_type)

(* --- Core Analysis Function (Input: Sexp.t, Output: TypedAst.t * Substitution) --- *)
(* Analyzes a single S-expression in a given environment *)
and analyze_expr (env : analysis_env) (sexp : Sexp.t)
    : TypedAst.t * substitution =
  match sexp with
  | Sexp.Atom s as atom_sexp ->
      (* Determine type of atom: Int, Float, nil, t, Keyword, Symbol (lookup in env) *)
      let inferred_t =
        try InferredType.T_Int with Failure _ ->
        try InferredType.T_Float with Failure _ ->
        if String.equal s "nil" then InferredType.T_Nil
        else if String.equal s "t" then InferredType.T_Bool (* Treat 't' atom as Bool *)
        else match List.Assoc.find env s ~equal:String.equal with
             | Some t -> t (* Found in local environment *)
             | None -> (* Check if keyword, otherwise assume Symbol (could check builtins/globals here) *)
                 if String.is_prefix s ~prefix:":" then InferredType.T_Keyword
                 else InferredType.T_Symbol
      in
      (TypedAst.Atom { sexp = atom_sexp; inferred_type = inferred_t }, Subst.empty)

  | Sexp.List [] -> (* Empty list is nil *)
      (TypedAst.Atom { sexp = Sexp.Atom "nil"; inferred_type = InferredType.T_Nil }, Subst.empty)

  | Sexp.List (head :: args) ->
      (* Handle special forms and function calls *)
      begin match head with
        | Sexp.Atom "quote" ->
            (match args with
             | [data] ->
                 let inferred_type = type_of_quoted_data data in
                 (TypedAst.Quote { sexp = data; inferred_type }, Subst.empty)
             | _ -> failwith "Malformed quote: expected exactly one argument")

        | Sexp.Atom "if" ->
            (match args with
            | [c; t] -> analyze_if env c t None (* Two args: condition, then *)
            | [c; t; e] -> analyze_if env c t (Some e) (* Three args: condition, then, else *)
            | _ -> failwith "Malformed if: expected 2 or 3 arguments")

        | Sexp.Atom "progn" ->
            let typed_forms, final_subst, result_type = analyze_progn_body env args in
            (TypedAst.Progn { forms = typed_forms; inferred_type = result_type }, final_subst)

        | Sexp.Atom "let" ->
            (match args with
             | Sexp.List bindings_sexp :: body_sexps ->
                 analyze_let env bindings_sexp body_sexps
             | _ -> failwith "Malformed let: expected bindings list and body")

        | Sexp.Atom "let*" ->
             (match args with
             | Sexp.List bindings_sexp :: body_sexps ->
                 analyze_let_star env bindings_sexp body_sexps
             | _ -> failwith "Malformed let*: expected bindings list and body")

        | Sexp.Atom "setq" ->
            analyze_setq env args

        | Sexp.Atom "lambda" ->
            (match args with
            | arg_list_sexp :: body_sexps ->
                analyze_lambda env arg_list_sexp body_sexps
            | _ -> failwith "Malformed lambda: expected arg list and body")

        | Sexp.Atom "defun" ->
            (match args with
            | Sexp.Atom name :: arg_list_sexp :: body_sexps ->
                 analyze_defun env name arg_list_sexp body_sexps
            | _ -> failwith "Malformed defun: expected name, arg list, and body")

        | Sexp.Atom "cond" ->
            analyze_cond env args

        (* --- Default case: Assume Function Call --- *)
        | _ -> analyze_funcall env head args
      end (* End match head *)

(* Analyzes an 'if' expression *)
and analyze_if env c t e_opt : TypedAst.t * substitution =
  (* Analyze condition *)
  let typed_cond, s_cond = analyze_expr env c in
  (* Apply condition substitution to environment for branches *)
  let env_after_cond = List.map env ~f:(fun (n,ty) -> (n, apply_subst s_cond ty)) in

  (* Analyze 'then' branch *)
  let typed_then, s_then = analyze_expr env_after_cond t in
  let subst_after_then = compose_subst s_cond s_then in
  (* Apply 'then' substitution for 'else' branch analysis *)
  let env_after_then = List.map env ~f:(fun (n,ty) -> (n, apply_subst subst_after_then ty)) in

  (* Analyze 'else' branch (if present) *)
  let typed_else_opt, final_subst = match e_opt with
    | None -> (None, subst_after_then) (* No else branch, subst from 'then' is final *)
    | Some e ->
        let typed_else, s_else_branch = analyze_expr env_after_then e in
        let combined_subst = compose_subst subst_after_then s_else_branch in
        (Some typed_else, combined_subst)
  in

  (* Determine result type: union of 'then' and 'else' types (or nil if no else) *)
  let then_type = apply_subst final_subst (TypedAst.get_type typed_then) in
  let else_type = match typed_else_opt with
                  | None -> InferredType.T_Nil
                  | Some te -> apply_subst final_subst (TypedAst.get_type te) in
  let result_type = InferredType.type_union then_type else_type in

  let node = TypedAst.If { cond=typed_cond; then_branch=typed_then;
                           else_branch=typed_else_opt; inferred_type = result_type } in
  (node, final_subst)


(* Analyzes a 'let' expression (parallel binding) *)
and analyze_let env bindings_sexp body_sexps : TypedAst.t * substitution =
   (* Analyze initializers in the outer environment, accumulating substitutions *)
   let analyzed_bindings, init_subst =
     List.fold bindings_sexp ~init:([], Subst.empty)
       ~f:(fun (acc_b, acc_s) b_sexp ->
         let name, init_form = match b_sexp with
           | Sexp.Atom n -> (n, Sexp.Atom "nil") (* No initializer defaults to nil *)
           | Sexp.List [Sexp.Atom n; i] -> (n, i)
           | _ -> failwithf "Malformed let binding: %s" (Sexp.to_string_hum b_sexp) ()
         in
         (* Analyze initializer in outer env, applying accumulated subst *)
         let env_for_init = List.map env ~f:(fun (n,ty)->(n, apply_subst acc_s ty)) in
         let typed_init, init_s = analyze_expr env_for_init init_form in
         (acc_b @ [(name, typed_init)], compose_subst acc_s init_s)
       ) in
   (* Create inner environment with all new bindings added *)
   let inner_env_bindings = List.map analyzed_bindings ~f:(fun (n,ti) ->
       (n, apply_subst init_subst (TypedAst.get_type ti))) in
   let inner_env = add_bindings env inner_env_bindings in
   (* Analyze body in the inner environment *)
   let typed_body, body_subst, result_type =
     analyze_progn_body inner_env body_sexps in
   (* Combine substitutions *)
   let final_subst = compose_subst init_subst body_subst in
   (* Apply final substitution to the result type *)
   let final_result_type = apply_subst final_subst result_type in
   let node = TypedAst.Let { bindings = analyzed_bindings; body = typed_body;
                             inferred_type = final_result_type } in
   (node, final_subst)

(* Analyzes a 'let*' expression (sequential binding) *)
and analyze_let_star env bindings_sexp body_sexps : TypedAst.t * substitution =
  (* Fold through bindings, updating environment sequentially *)
  let bindings_env, analyzed_bindings, bindings_subst =
    List.fold bindings_sexp ~init:(env, [], Subst.empty)
      ~f:(fun (current_env, acc_b, acc_s) b_sexp ->
        let name, init_form = match b_sexp with
          | Sexp.Atom n -> (n, Sexp.Atom "nil")
          | Sexp.List [Sexp.Atom n; i] -> (n, i)
          | _ -> failwithf "Malformed let* binding: %s" (Sexp.to_string_hum b_sexp) ()
        in
        (* Analyze initializer in the *current* sequential env (with accumulated subst) *)
        let env_for_init = List.map current_env ~f:(fun (n,ty)->(n, apply_subst acc_s ty)) in
        let typed_init, init_s = analyze_expr env_for_init init_form in
        let combined_subst = compose_subst acc_s init_s in
        (* Add the new binding (with type updated by combined subst) to the env for the *next* initializer *)
        let binding_type = apply_subst combined_subst (TypedAst.get_type typed_init) in
        let next_env = add_binding current_env name binding_type in
        (next_env, acc_b @ [(name, typed_init)], combined_subst)
      ) in
  (* Analyze body in the final sequential environment *)
  let body_env = List.map bindings_env ~f:(fun (n,ty)->(n, apply_subst bindings_subst ty)) in
  let typed_body, body_subst, result_type =
    analyze_progn_body body_env body_sexps in
  (* Combine substitutions *)
  let final_subst = compose_subst bindings_subst body_subst in
  (* Apply final substitution to result type *)
  let final_result_type = apply_subst final_subst result_type in
  let node = TypedAst.LetStar { bindings = analyzed_bindings; body = typed_body;
                                inferred_type = final_result_type } in
  (node, final_subst)


(* Analyzes a 'setq' expression *)
and analyze_setq env args : TypedAst.t * substitution =
   (* Check for even number of arguments (var value pairs) *)
   if List.length args % 2 <> 0 then
     failwith "Malformed setq: must have an even number of arguments (var value pairs)";
   (* Process pairs sequentially *)
   let rec process_pairs pairs acc_typed_pairs acc_subst =
     match pairs with
     | [] -> (List.rev acc_typed_pairs, acc_subst) (* Base case *)
     | Sexp.Atom var_name :: value_sexp :: rest ->
         (* Analyze the value expression in the current env (applying accumulated subst) *)
         let env_for_value = List.map env ~f:(fun (n,ty)->(n, apply_subst acc_subst ty)) in
         let typed_value, value_subst = analyze_expr env_for_value value_sexp in
         let current_subst = compose_subst acc_subst value_subst in
         let value_type = apply_subst current_subst (TypedAst.get_type typed_value) in

         (* Unify the assigned value type with the variable's existing type (if known) *)
         let final_subst =
           match List.Assoc.find env var_name ~equal:String.equal with
           | Some existing_var_type ->
               (try
                  (* Unify the existing type (with current subst applied) and the new value type *)
                  let s_unify = unify (apply_subst current_subst existing_var_type) value_type in
                  compose_subst current_subst s_unify
                with Unification_error _msg ->
                  (* If unification fails, keep the current substitution. Could warn here. *)
                  (* Print.(eprintf "Warning: setq unification failed for %s: %s\n" var_name msg); *)
                  current_subst)
           | None -> (* Variable not found locally (assume global or new), no unification possible here *)
               current_subst
         in
         (* Continue processing remaining pairs *)
         process_pairs rest ((var_name, typed_value) :: acc_typed_pairs) final_subst
     | not_atom :: _ -> failwithf "Malformed setq: expected symbol, got %s" (Sexp.to_string_hum not_atom) ()
   in
   let typed_pairs, final_subst = process_pairs args [] Subst.empty in
   (* The result of setq is the value of the *last* assignment *)
   let result_type = match List.last typed_pairs with
                     | None-> InferredType.T_Nil (* (setq) evaluates to nil *)
                     | Some (_,v) -> apply_subst final_subst (TypedAst.get_type v) in
   (TypedAst.Setq({ pairs = typed_pairs; inferred_type = result_type }), final_subst)

(* Analyzes a 'lambda' expression *)
and analyze_lambda env arg_list_sexp body_sexps : TypedAst.t * substitution =
   let arg_spec = ArgListParser.parse arg_list_sexp in
   (* Create fresh type variables for all arguments *)
   let create_binding name = (name, generate_fresh_type_var()) in
   let arg_bindings =
     List.map arg_spec.required ~f:create_binding @
     List.map arg_spec.optional ~f:(fun (n,_) -> create_binding n) @
     (match arg_spec.rest with Some n -> [create_binding n] | None -> [])
   in
   (* Create inner environment for analyzing the body *)
   let inner_env = add_bindings env arg_bindings in
   (* Analyze body *)
   let typed_body, body_subst, body_return_type =
     analyze_progn_body inner_env body_sexps in

   (* Apply body substitution to argument types and return type to get final signature *)
   let final_arg_types = List.map arg_bindings ~f:(fun (_, ty) -> apply_subst body_subst ty) in
   let final_return_type = apply_subst body_subst body_return_type in
   let fun_info = { InferredType.arg_types = Some final_arg_types; return_type = final_return_type } in
   let inferred_type = InferredType.T_Function fun_info in
   let node = TypedAst.Lambda { args = arg_spec; body = typed_body; inferred_type } in
   (* Lambda analysis itself doesn't impose constraints outward; body subst is internal *)
   (node, Subst.empty)

(* Analyzes a 'defun' expression *)
and analyze_defun env name arg_list_sexp body_sexps : TypedAst.t * substitution =
   let arg_spec = ArgListParser.parse arg_list_sexp in
   (* Create fresh type variables for args and an initial one for return type *)
   let arg_bindings =
     List.map arg_spec.required ~f:(fun n->(n, generate_fresh_type_var())) @
     List.map arg_spec.optional ~f:(fun (n,_)->(n, generate_fresh_type_var())) @
     (match arg_spec.rest with Some n -> [(n, generate_fresh_type_var())] | None -> []) in
   let initial_ret_type_var = generate_fresh_type_var() in
   (* Initial guess for the function's type *)
   let initial_fun_type =
     InferredType.T_Function {
       arg_types = Some (List.map arg_bindings ~f:snd);
       return_type = initial_ret_type_var
     } in
   (* Add the function itself to the environment for recursion, along with args *)
   let env_for_body = add_bindings (add_binding env name initial_fun_type) arg_bindings in
   (* Analyze body *)
   let typed_body, body_subst, body_return_type =
     analyze_progn_body env_for_body body_sexps in

   (* Unify the initial guess for the return type with the actual analyzed body return type *)
   let final_subst =
     try
       let s_ret = unify (apply_subst body_subst initial_ret_type_var)
                        (apply_subst body_subst body_return_type) in
       compose_subst body_subst s_ret
     with Unification_error _msg ->
       (* If unification fails, keep body subst. Could warn. *)
       (* Print.(eprintf "Warning: defun return type unification failed for %s: %s\n" name msg); *)
       body_subst
   in

   (* Determine the final function signature after unification *)
   let final_arg_types = List.map arg_bindings ~f:(fun (_,ty) -> apply_subst final_subst ty) in
   let final_return_type = apply_subst final_subst body_return_type in
   let final_fun_info = { InferredType.arg_types = Some final_arg_types; return_type = final_return_type } in
   let final_fun_type = InferredType.T_Function final_fun_info in

   (* Defun expression itself evaluates to the function's symbol *)
   let node = TypedAst.Defun { name = name; args = arg_spec; body = typed_body;
                               fun_type = final_fun_type; (* Store the inferred fun type *)
                               inferred_type = InferredType.T_Symbol } in
   (* Defun defines a name globally; substitution affects the *type* associated
      with that name, not constraints flowing *out* of the defun expression itself.
      The main update happens in analyze_toplevel. *)
   (node, Subst.empty)


(* Analyzes a 'cond' expression *)
and analyze_cond env args : TypedAst.t * substitution =
  (* Fold over clauses, accumulating analyzed clauses, substitution, and result type *)
  let analyzed_clauses, final_subst, result_type =
    List.fold args ~init:([], Subst.empty, InferredType.T_Nil) (* Result starts as Nil *)
      ~f:(fun (acc_clauses, acc_subst, acc_type) clause_sexp ->
        match clause_sexp with
        | Sexp.List (test_sexp :: body_sexps) ->
            (* Analyze test in current env (with accumulated subst) *)
            let env_for_clause = List.map env ~f:(fun (n,ty) -> (n, apply_subst acc_subst ty)) in
            let typed_test, test_subst = analyze_expr env_for_clause test_sexp in
            let composed_subst = compose_subst acc_subst test_subst in
            let env_after_test = List.map env ~f:(fun (n,ty)->(n, apply_subst composed_subst ty)) in

            (* Analyze body (or use test result if body empty) *)
            let typed_body, body_subst, clause_result_type =
              if List.is_empty body_sexps then
                (* If no body, result is the test's value *)
                ([typed_test], Subst.empty, apply_subst composed_subst (TypedAst.get_type typed_test))
              else
                (* Analyze body using progn logic *)
                analyze_progn_body env_after_test body_sexps
            in
            (* Combine substitutions from test and body *)
            let final_clause_subst = compose_subst composed_subst body_subst in
            (* Determine clause result type after applying combined subst *)
            let final_clause_type = apply_subst final_clause_subst clause_result_type in

            (* Add clause, update final substitution, update overall result type (union) *)
            (acc_clauses @ [(typed_test, typed_body)],
             final_clause_subst,
             InferredType.type_union acc_type final_clause_type)
        | _ -> failwith "Malformed cond clause: must be a list"
      )
  in
  (TypedAst.Cond ({ clauses = analyzed_clauses; inferred_type = result_type }), final_subst)


(* Analyzes a function call *)
and analyze_funcall env head args_sexps : TypedAst.t * substitution =
  (* Analyze the function expression itself *)
  let typed_head, head_subst = analyze_expr env head in

  (* Analyze arguments sequentially, accumulating substitutions *)
  (* FIXED: Swapped variable names in let binding *)
  let args_subst, typed_args = List.fold_map args_sexps ~init:head_subst
    ~f:(fun acc_s arg_sexp ->
      let env_for_arg = List.map env ~f:(fun (n,ty)->(n, apply_subst acc_s ty)) in
      let typed_arg, arg_s = analyze_expr env_for_arg arg_sexp in
      (compose_subst acc_s arg_s, typed_arg) (* Returns (new_subst, typed_arg) *)
    )
  in

  (* Get the type of the function and arguments after all substitutions *)
  let func_type = apply_subst args_subst (TypedAst.get_type typed_head) in
  let actual_arg_types = List.map typed_args ~f:(fun ta ->
      apply_subst args_subst (TypedAst.get_type ta)) in

  (* Inner helper to perform unification based on a known function signature *)
  let unify_with_sig (finfo: InferredType.fun_info) : InferredType.t * substitution =
    try
      (* Instantiate the function signature to get fresh type variables for this call site *)
      let sig_arg_types_opt, sig_return_type = instantiate_fun_sig finfo in

      match sig_arg_types_opt with
      | None -> (* Function takes any args (e.g., varargs, no static check) *)
          (sig_return_type, args_subst) (* Return type is still known *)
      | Some sig_arg_types ->
          (* Arity check *)
          if List.length sig_arg_types <> List.length actual_arg_types then
            let msg = sprintf "Arity mismatch in call to %s: Expected %d args, got %d"
                        (Sexp.to_string head) (* Provide context *)
                        (List.length sig_arg_types) (List.length actual_arg_types) in
            raise (Unification_error msg)
          else
            (* Unify actual argument types with instantiated signature arg types *)
            let final_subst =
              List.fold2_exn sig_arg_types actual_arg_types ~init:args_subst
                ~f:(fun current_subst sig_arg actual_arg ->
                  (* Unify applied types *)
                  let s_arg = unify (apply_subst current_subst sig_arg)
                                     (apply_subst current_subst actual_arg) in
                  compose_subst current_subst s_arg
                )
            in
            (* Apply the final substitution (from arg unification) to the instantiated return type *)
            (apply_subst final_subst sig_return_type, final_subst)
    with Unification_error _msg ->
      (* Handle unification errors - return T_Unknown or re-raise? *)
      (* Print.(eprintf "Warning: Unification failed during call to %s: %s\n" (Sexp.to_string head) msg); *)
      (InferredType.T_Unknown, args_subst) (* Fallback to Unknown type *)
  in

  (* Determine the result type and final substitution based on the function's inferred type *)
  let result_type, final_subst = match func_type with
    (* If it's a known function type, unify with its signature *)
    | InferredType.T_Function finfo -> unify_with_sig finfo
    (* If it's a symbol/keyword, check if it's a known builtin *)
    | InferredType.T_Symbol | InferredType.T_Keyword ->
        (match head with
         | Sexp.Atom name ->
             (match get_builtin_signature name with
              | Some finfo -> unify_with_sig finfo (* Found builtin, unify *)
              | None -> (InferredType.T_Any, args_subst)) (* Unknown symbol/builtin -> Any *)
         | _ -> (InferredType.T_Any, args_subst)) (* Calling a non-atom symbol? -> Any *)
    (* Calling something of type Any results in Any *)
    | InferredType.T_Any -> (InferredType.T_Any, args_subst)
    (* Calling something Unknown results in Unknown *)
    | InferredType.T_Unknown -> (InferredType.T_Unknown, args_subst)
    (* Calling a Union: Simplified - assume Any. Could try unifying with each function in the union. *)
    | InferredType.T_Union _s -> (InferredType.T_Any, args_subst)
    (* Calling a non-function type (Int, String, etc.) *)
    | _ ->
        (* Print.(eprintf "Warning: Attempting to call non-function type %s for %s\n" (InferredType.to_string func_type) (Sexp.to_string head)); *)
        (InferredType.T_Unknown, args_subst) (* Error case -> Unknown *)
  in
  let node = TypedAst.Funcall { func = typed_head; args = typed_args;
                                inferred_type = result_type } in
  (node, final_subst)


(* --- Top Level Analysis --- *)
(* Analyzes a list of top-level S-expressions *)
let analyze_toplevel (sexps : Sexp.t list)
    : TypedAst.t list * (string * InferredType.t) list =
  (* Maintain the global environment and final substitution as refs *)
  let final_env_map = ref String.Map.empty in
  let final_subst = ref Subst.empty in

  (* Analyze each expression sequentially *)
  let typed_asts = List.map sexps ~f:(fun sexp ->
      (* Analyze using the *current* state of the global env & substitution *)
      let current_env = Map.to_alist !final_env_map in
      let typed_ast, subst = analyze_expr current_env sexp in
      (* Compose the substitution from this expression with the accumulated one *)
      final_subst := compose_subst !final_subst subst;

      (* Update global environment map for definitions (defun) *)
      (match typed_ast with
       | TypedAst.Defun { name; fun_type; _ } ->
           (* Add/Update the function's type, applying the final substitution *)
           final_env_map := Map.set !final_env_map ~key:name
                              ~data:(apply_subst !final_subst fun_type)
       | _ -> ()
      );
      (* Apply the latest substitution to *all* existing env map entries
         to ensure consistency before analyzing the next expression *)
      final_env_map := Map.map !final_env_map ~f:(apply_subst !final_subst);
      typed_ast
    )
  in
  (* Final pass: Apply the final overall substitution to all inferred types in the TAST *)
  let rec final_apply tast =
    let apply_t = apply_subst !final_subst in (* Helper to apply final subst *)
    (* Use fully qualified constructors in pattern matching *)
    match tast with
    | TypedAst.Atom ({ inferred_type=t; _ } as r) ->
        TypedAst.Atom { r with inferred_type = apply_t t }
    | TypedAst.Quote ({ inferred_type=t; _ } as r) ->
        TypedAst.Quote { r with inferred_type = apply_t t }
    | TypedAst.If ({ inferred_type=t; cond; then_branch; else_branch }) ->
        TypedAst.If { cond=final_apply cond;
                           then_branch=final_apply then_branch;
                           else_branch=Option.map else_branch ~f:final_apply;
                           inferred_type=apply_t t }
    | TypedAst.Progn ({ inferred_type=t; forms }) ->
        TypedAst.Progn { forms=List.map forms ~f:final_apply;
                              inferred_type=apply_t t }
    | TypedAst.Let ({ inferred_type=t; bindings; body }) ->
        TypedAst.Let { bindings=List.map bindings ~f:(fun (n,t)->(n, final_apply t));
                            body=List.map body ~f:final_apply;
                            inferred_type=apply_t t }
    | TypedAst.LetStar ({ inferred_type=t; bindings; body }) ->
        TypedAst.LetStar { bindings=List.map bindings ~f:(fun (n,t)->(n, final_apply t));
                                body=List.map body ~f:final_apply;
                                inferred_type=apply_t t }
    | TypedAst.Setq ({ inferred_type=t; pairs }) ->
        TypedAst.Setq { pairs=List.map pairs ~f:(fun (n,t)->(n, final_apply t));
                             inferred_type=apply_t t }
    | TypedAst.Lambda ({ inferred_type=t; body; _ } as r) ->
         (* Apply to the lambda's overall type and recursively to its body *)
        TypedAst.Lambda { r with body=List.map body ~f:final_apply;
                               inferred_type=apply_t t }
    | TypedAst.Defun ({ inferred_type=t; fun_type; body; _ } as r) ->
        (* Apply to the defun expression type, the function type, and the body *)
        TypedAst.Defun { r with body=List.map body ~f:final_apply;
                              fun_type=apply_t fun_type;
                              inferred_type=apply_t t }
    | TypedAst.Cond ({ inferred_type=t; clauses }) ->
        TypedAst.Cond { clauses=List.map clauses
                                  ~f:(fun (tst,bdy)->(final_apply tst, List.map bdy ~f:final_apply));
                              inferred_type=apply_t t }
    | TypedAst.Funcall ({ inferred_type=t; func; args }) ->
        TypedAst.Funcall { func=final_apply func;
                                args=List.map args ~f:final_apply;
                                inferred_type=apply_t t }
  in
  let final_tasts = List.map typed_asts ~f:final_apply in
  (* Return the finalized TASTs and the final global environment *)
  (final_tasts, Map.to_alist !final_env_map)

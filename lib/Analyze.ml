(* Analyze.ml - Static Type Analysis (Refactored for Value.t - PARTIAL) *)
(* !! WARNING: This is a complex refactoring. This is a partial attempt !! *)
(* !!          and likely contains errors or omissions.              !! *)

open! Core
(* REMOVED: open! Sexplib.Std *)

(* Use types/modules from the Scaml library *)
module Value = Value
module InferredType = InferredType
(* REMOVED: module Runtime = Runtime *)

(* --- Typed Abstract Syntax Tree (TAST) --- *)
module TypedAst = struct
  (* Added record to hold binding info, including mutation status *)
  type binding_info = {
    initializer_ast : t; (* The TAST node for the initializer *)
    is_mutated : bool; (* Flag: True if setq modifies this var in scope *)
    (* needs_boxing flag removed, analysis pass will return this info separately *)
  }
  (* TAST definition *)
  and t =
    | Atom of { value: Value.t; inferred_type: InferredType.t } (* Store Value.t atom *)
    | Quote of { value: Value.t; inferred_type: InferredType.t } (* Store quoted Value.t *)
    | If of {
        cond: t;
        then_branch: t;
        else_branch: t option;
        inferred_type: InferredType.t
      }
    | Progn of { forms: t list; inferred_type: InferredType.t }
    | Let of {
        bindings: (string * binding_info) list; (* MODIFIED: Use binding_info *)
        body: t list;
        inferred_type: InferredType.t
      }
    | LetStar of {
        bindings: (string * binding_info) list; (* MODIFIED: Use binding_info *)
        body: t list;
        inferred_type: InferredType.t
      }
    | Setq of { pairs: (string * t) list; inferred_type: InferredType.t } (* Value is TAST *)
    | Lambda of {
        args: InferredType.arg_spec; (* Parsed arg spec *)
        body: t list; (* Analyzed body *)
        inferred_type: InferredType.t (* Function type *)
      }
    | Defun of {
        name: string;
        args: InferredType.arg_spec;
        body: t list;
        fun_type: InferredType.t; (* Type of the function itself *)
        inferred_type: InferredType.t (* Type of the defun expression (symbol) *)
      }
    | Cond of { clauses: (t * t list) list; inferred_type: InferredType.t }
    | Funcall of { func: t; args: t list; inferred_type: InferredType.t }
  (* REMOVED: [@@deriving sexp_of] - Requires manual definition now *)

  (* Manual sexp_of functions *)
  let rec sexp_of_binding_info { initializer_ast; is_mutated } : Sexp.t =
      Sexp.List [ Sexp.Atom "BindingInfo";
                  sexp_of_t initializer_ast;
                  Sexp.Atom (sprintf "mutated=%b" is_mutated) ]

  and sexp_of_t (node : t) : Sexp.t =
    match node with
    | Atom { value; inferred_type } ->
        Sexp.List [Sexp.Atom "Atom"; Value.sexp_of_t value; InferredType.sexp_of_t inferred_type]
    | Quote { value; inferred_type } ->
        Sexp.List [Sexp.Atom "Quote"; Value.sexp_of_t value; InferredType.sexp_of_t inferred_type]
    | If { cond; then_branch; else_branch; inferred_type } ->
        Sexp.List [Sexp.Atom "If"; sexp_of_t cond; sexp_of_t then_branch;
                   Option.value_map else_branch ~default:(Sexp.Atom "None") ~f:(fun e -> Sexp.List [Sexp.Atom "Some"; sexp_of_t e]);
                   InferredType.sexp_of_t inferred_type]
    | Progn { forms; inferred_type } ->
        Sexp.List [Sexp.Atom "Progn"; Sexp.List (List.map forms ~f:sexp_of_t); InferredType.sexp_of_t inferred_type]
    | Let { bindings; body; inferred_type } ->
        (* MODIFIED: Use sexp_of_binding_info *)
        let sexp_of_binding (n, b_info) = Sexp.List [Sexp.Atom n; sexp_of_binding_info b_info] in
        Sexp.List [Sexp.Atom "Let"; Sexp.List (List.map bindings ~f:sexp_of_binding);
                   Sexp.List (List.map body ~f:sexp_of_t); InferredType.sexp_of_t inferred_type]
    | LetStar { bindings; body; inferred_type } ->
        (* MODIFIED: Use sexp_of_binding_info *)
         let sexp_of_binding (n, b_info) = Sexp.List [Sexp.Atom n; sexp_of_binding_info b_info] in
         Sexp.List [Sexp.Atom "LetStar"; Sexp.List (List.map bindings ~f:sexp_of_binding);
                   Sexp.List (List.map body ~f:sexp_of_t); InferredType.sexp_of_t inferred_type]
    | Setq { pairs; inferred_type } ->
         let sexp_of_pair (n, t) = Sexp.List [Sexp.Atom n; sexp_of_t t] in
         Sexp.List [Sexp.Atom "Setq"; Sexp.List (List.map pairs ~f:sexp_of_pair); InferredType.sexp_of_t inferred_type]
    | Lambda { args; body; inferred_type } ->
        Sexp.List [Sexp.Atom "Lambda"; InferredType.sexp_of_arg_spec args;
                   Sexp.List (List.map body ~f:sexp_of_t); InferredType.sexp_of_t inferred_type]
    | Defun { name; args; body; fun_type; inferred_type } ->
        Sexp.List [Sexp.Atom "Defun"; Sexp.Atom name; InferredType.sexp_of_arg_spec args;
                   Sexp.List (List.map body ~f:sexp_of_t); InferredType.sexp_of_t fun_type; InferredType.sexp_of_t inferred_type]
    | Cond { clauses; inferred_type } ->
        let sexp_of_clause (tst, bdy) = Sexp.List [sexp_of_t tst; Sexp.List (List.map bdy ~f:sexp_of_t)] in
        Sexp.List [Sexp.Atom "Cond"; Sexp.List (List.map clauses ~f:sexp_of_clause); InferredType.sexp_of_t inferred_type]
    | Funcall { func; args; inferred_type } ->
        Sexp.List [Sexp.Atom "Funcall"; sexp_of_t func; Sexp.List (List.map args ~f:sexp_of_t); InferredType.sexp_of_t inferred_type]


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

(* --- Argument List Parsing (from Value.t) --- *)
module ArgListParser = struct
  type arg_spec = InferredType.arg_spec = {
    required: string list;
    optional: (string * Value.t option) list; (* Store Value.t for default *)
    rest: string option;
  } [@@deriving sexp_of] (* Keep sexp_of for debugging *)

  let parse (arg_list_val : Value.t) : arg_spec =
    match Value.value_to_list_opt arg_list_val with
    | Some arg_list ->
        let rec parse_internal state rev_required rev_optional rest_opt ast =
          match state, ast with
          (* Keywords *)
          | _, Value.Symbol {name="&optional"} :: rest_ast ->
              parse_internal `Optional rev_required rev_optional rest_opt rest_ast
          | _, Value.Symbol {name="&rest"} :: rest_ast ->
              parse_internal `Rest rev_required rev_optional rest_opt rest_ast

          (* Required *)
          | `Required, Value.Symbol {name} :: rest_ast ->
              parse_internal `Required (name :: rev_required) rev_optional rest_opt rest_ast
          | `Required, [] -> { required = List.rev rev_required; optional = []; rest = None }

          (* Optional *)
          | `Optional, Value.Symbol {name} :: rest_ast -> (* Optional without default *)
              parse_internal `Optional rev_required ((name, None) :: rev_optional) rest_opt rest_ast
          | `Optional, Value.Cons { car = Value.Symbol {name}; cdr = default_list_val } :: rest_ast -> (* Optional with default *)
              (match Value.value_to_list_opt default_list_val with
               | Some [default_form] ->
                   parse_internal `Optional rev_required ((name, Some default_form) :: rev_optional) rest_opt rest_ast
               | _ -> failwithf "Malformed optional arg with default: %s" (!Value.to_string (Value.Cons { car = Value.Symbol {name}; cdr = default_list_val })) ())
          | `Optional, [] -> { required = List.rev rev_required; optional = List.rev rev_optional; rest = None }

          (* Rest *)
          | `Rest, Value.Symbol {name} :: [] -> (* &rest followed by one symbol *)
              { required = List.rev rev_required; optional = List.rev rev_optional; rest = Some name }
          | `Rest, _ -> failwith "Malformed &rest argument: must be followed by exactly one symbol"

          (* Errors *)
          | _, other :: _ -> failwithf "Invalid element in lambda list: %s" (!Value.to_string other) ()
        in
        parse_internal `Required [] [] None arg_list
    | None -> failwith "Lambda list must be a proper list"
end


(* --- Analysis Environment --- *)
type analysis_env = (string * InferredType.t) list [@@deriving sexp_of]
let add_binding env name inferred_type = (name, inferred_type) :: env
let add_bindings env bindings = bindings @ env

(* --- Unification & Type Variables (Keep as is) --- *)
module Subst = String.Map
type substitution = InferredType.t Subst.t [@@deriving sexp_of]
exception Unification_error of string
let rec apply_subst subst t = (* ... keep existing implementation ... *) InferredType.(
    match t with
    | InferredType.T_Var v -> (match Map.find subst v with Some bound_t -> apply_subst subst bound_t | None -> t)
    | InferredType.T_Cons info -> T_Cons { car_type = apply_subst subst info.car_type; cdr_type = apply_subst subst info.cdr_type }
    | InferredType.T_Vector info -> T_Vector { element_type = apply_subst subst info.element_type }
    | InferredType.T_Function info -> T_Function { arg_types = Option.map info.arg_types ~f:(List.map ~f:(apply_subst subst)); return_type = apply_subst subst info.return_type }
    | InferredType.T_Union s -> normalize_union_set (InferredTypeSet.map s ~f:(apply_subst subst))
    | InferredType.T_Unknown | T_Any | T_Nil | T_Bool | T_Int | T_Float | T_Char | T_String | T_Symbol | T_Keyword as other -> other
    )
let compose_subst s1 s2 = (* ... keep existing implementation ... *)
    let s2_mapped = Subst.map s2 ~f:(apply_subst s1) in
    Map.merge_skewed s1 s2_mapped ~combine:(fun ~key:_ v1 _ -> v1)
let rec occurs_check var_name t = (* ... keep existing implementation ... *) InferredType.(
    match t with
    | InferredType.T_Var v -> String.equal v var_name
    | InferredType.T_Cons { car_type; cdr_type } -> occurs_check var_name car_type || occurs_check var_name cdr_type
    | InferredType.T_Vector { element_type } -> occurs_check var_name element_type
    | InferredType.T_Function { arg_types; return_type } -> (Option.value_map arg_types ~default:false ~f:(List.exists ~f:(occurs_check var_name))) || occurs_check var_name return_type
    | InferredType.T_Union s -> Set.exists s ~f:(occurs_check var_name)
    | InferredType.T_Unknown | T_Any | T_Nil | T_Bool | T_Int | T_Float | T_Char | T_String | T_Symbol | T_Keyword -> false
    )
let rec unify t1 t2 = (* ... keep existing implementation ... *)
    if [%compare.equal: InferredType.t] t1 t2 then Subst.empty
    else match (t1, t2) with
    | (InferredType.T_Var v, t) | (t, InferredType.T_Var v) -> unify_var v t
    | (InferredType.T_Cons c1, InferredType.T_Cons c2) -> unify_cons c1 c2
    | (InferredType.T_Vector v1, InferredType.T_Vector v2) -> unify_vector v1 v2
    | (InferredType.T_Function f1, InferredType.T_Function f2) -> unify_fun f1 f2
    | (InferredType.T_Union _, InferredType.T_Union _) -> Subst.empty
    | (InferredType.T_Union _, _) | (_, InferredType.T_Union _) -> Subst.empty
    | (InferredType.T_Any, _) | (_, InferredType.T_Any) -> Subst.empty
    | (InferredType.T_Unknown, _) | (_, InferredType.T_Unknown) -> Subst.empty
    | _ -> let msg = sprintf "Cannot unify different concrete types: %s / %s" (InferredType.to_string t1) (InferredType.to_string t2) in raise (Unification_error msg)
and unify_var var_name t = (* ... keep existing implementation ... *)
    match t with
    | InferredType.T_Var v when String.equal v var_name -> Subst.empty
    | InferredType.T_Any | InferredType.T_Unknown -> Subst.empty
    | _ -> if occurs_check var_name t then let msg = sprintf "Recursive type error: %s occurs in %s" var_name (InferredType.to_string t) in raise (Unification_error msg) else Subst.singleton var_name t
and unify_cons c1 c2 = (* ... keep existing implementation ... *)
    let s1 = unify c1.InferredType.car_type c2.InferredType.car_type in
    let s2 = unify (apply_subst s1 c1.InferredType.cdr_type) (apply_subst s1 c2.InferredType.cdr_type) in
    compose_subst s1 s2
and unify_vector v1 v2 = (* ... keep existing implementation ... *)
    unify v1.InferredType.element_type v2.InferredType.element_type
and unify_fun f1 f2 = (* ... keep existing implementation ... *)
    let s1 = unify f1.InferredType.return_type f2.InferredType.return_type in
    match (f1.InferredType.arg_types, f2.InferredType.arg_types) with
    | (Some args1, Some args2) -> if List.length args1 <> List.length args2 then raise (Unification_error "Function types have different arity") else List.fold2_exn args1 args2 ~init:s1 ~f:(fun current_subst arg1 arg2 -> let s_arg = unify (apply_subst current_subst arg1) (apply_subst current_subst arg2) in compose_subst current_subst s_arg)
    | (None, None) -> s1 | (Some _, None) | (None, Some _) -> s1

(* --- Type Variable Instantiation (Keep as is) --- *)
let type_var_instantiation_counter = ref 0
let generate_fresh_type_var () = (* ... keep existing implementation ... *)
    incr type_var_instantiation_counter; InferredType.T_Var (sprintf "a%d" !type_var_instantiation_counter)
let instantiate_type t = (* ... keep existing implementation ... *)
    let subst_ref = ref Subst.empty in
    let rec inst ty = InferredType.(match ty with
        | InferredType.T_Var v -> (match Map.find !subst_ref v with Some fresh_var -> fresh_var | None -> let fresh_var = generate_fresh_type_var() in subst_ref := Map.add_exn !subst_ref ~key:v ~data:fresh_var; fresh_var)
        | InferredType.T_Cons info -> T_Cons { car_type = inst info.car_type; cdr_type = inst info.cdr_type }
        | InferredType.T_Vector info -> T_Vector { element_type = inst info.element_type }
        | InferredType.T_Function info -> T_Function { arg_types = Option.map info.arg_types ~f:(List.map ~f:inst); return_type = inst info.return_type }
        | InferredType.T_Union s -> normalize_union_set (InferredTypeSet.map s ~f:inst)
        | InferredType.T_Unknown | T_Any | T_Nil | T_Bool | T_Int | T_Float | T_Char | T_String | T_Symbol | T_Keyword as other -> other)
    in (inst t, !subst_ref)
let instantiate_fun_sig finfo = (* ... keep existing implementation ... *)
    let temp_fun_type = InferredType.T_Function finfo in
    let instantiated_type, _ = instantiate_type temp_fun_type in
    match instantiated_type with InferredType.T_Function finfo_inst -> (finfo_inst.arg_types, finfo_inst.return_type) | _ -> failwith "Internal error"


(* --- Analysis of Quoted Data (from Value.t) --- *)
(* Determine the InferredType of a quoted Value.t *)
let rec type_of_quoted_data (value : Value.t) : InferredType.t =
  let open InferredType in
  match value with
  | Value.Nil -> InferredType.T_Nil
  | Value.T -> InferredType.T_Bool (* Treat 't' as Bool in quotes *)
  | Value.Int _ -> InferredType.T_Int
  | Value.Float _ -> InferredType.T_Float
  | Value.String _ -> InferredType.T_String
  | Value.Symbol _ -> InferredType.T_Symbol
  | Value.Keyword _ -> InferredType.T_Keyword
  | Value.Char _ -> InferredType.T_Char
  | Value.Vector arr ->
      (* Infer vector type based on elements - simplified: union of element types *)
      let element_types = Array.map arr ~f:type_of_quoted_data |> Array.to_list in
      let union_type = List.fold element_types ~init:InferredType.T_Nil ~f:type_union in
      InferredType.T_Vector { element_type = union_type }
  | Value.Cons { car; cdr } ->
      (* Recursively determine car and cdr types *)
      let car_t = type_of_quoted_data car in
      let cdr_t = type_of_quoted_data cdr in
      InferredType.T_Cons { car_type = car_t; cdr_type = cdr_t }
  | Value.Function _ | Value.Builtin _ -> InferredType.T_Function { arg_types=None; return_type=T_Any } (* Quoted functions are opaque *)


(* --- Built-in Function Type Signatures (Keep as is) --- *)
let tvar_a = InferredType.T_Var "a"
let tvar_b = InferredType.T_Var "b"
let get_builtin_signature name = (* ... keep existing implementation ... *)
    let open InferredType in
    match name with
    | "+" | "*" | "-" | "/" -> Some { arg_types = None; return_type = InferredType.T_Int }
    | "car" -> let input_type = type_union (InferredType.T_Cons { car_type = tvar_a; cdr_type = T_Any }) T_Nil in Some { arg_types = Some [input_type]; return_type = type_union tvar_a T_Nil }
    | "cdr" -> let input_type = type_union (InferredType.T_Cons { car_type = T_Any; cdr_type = tvar_b }) T_Nil in Some { arg_types = Some [input_type]; return_type = type_union tvar_b T_Nil }
    | "cons" -> Some { arg_types = Some [tvar_a; tvar_b]; return_type = InferredType.T_Cons { car_type = tvar_a; cdr_type = tvar_b } }
    | "integerp" | "stringp" | "symbolp" | "consp" | "listp" | "null" | "vectorp" | "floatp" | "keywordp" | "atom" | "functionp" -> Some { arg_types = Some [InferredType.T_Any]; return_type = T_Bool }
    | "eq" | "equal" -> Some { arg_types = Some [tvar_a; tvar_a]; return_type = InferredType.T_Bool }
    | "compile" | "interpret" | "assoc" | "list" | "setcar" | "setcdr" -> Some { arg_types = None; return_type = InferredType.T_Any } (* Simplified *)
    | _ -> None

(* --- Mutation Analysis Helper --- *)

(** Recursively finds the set of variables from [candidates] that are assigned
    by `setq` within the given AST node [ast]. Handles shadowing introduced
    by `let`, `let*`, and `lambda`. *)
let rec check_mutations (ast: TypedAst.t) (candidates: String.Set.t) : String.Set.t =
  (* If no candidates, no mutations can be found *)
  if Set.is_empty candidates then String.Set.empty
  else match ast with
    | TypedAst.Atom _ | TypedAst.Quote _ -> String.Set.empty
    | TypedAst.Setq { pairs; _ } ->
        let assigned_vars = List.map pairs ~f:fst |> String.Set.of_list in
        Set.inter candidates assigned_vars
    | TypedAst.Progn { forms; _ } ->
        (* Union mutations found in each form *)
        List.fold forms ~init:String.Set.empty ~f:(fun acc form ->
          Set.union acc (check_mutations form candidates)
        )
    | TypedAst.If { cond; then_branch; else_branch; _ } ->
        let cond_mut = check_mutations cond candidates in
        let then_mut = check_mutations then_branch candidates in
        let else_mut = Option.value_map else_branch ~default:String.Set.empty ~f:(fun e -> check_mutations e candidates) in
        String.Set.union_list [cond_mut; then_mut; else_mut]
    | TypedAst.Let { bindings; body; _ } ->
        let bound_names = List.map bindings ~f:fst in
        let bound_vars_set = String.Set.of_list bound_names in
        (* Candidates for the body exclude newly bound vars (shadowing) *)
        let body_candidates = Set.diff candidates bound_vars_set in
        (* Mutations from initializers (use original candidates) *)
        let init_mutations = List.fold bindings ~init:String.Set.empty ~f:(fun acc (_, b_info) ->
             Set.union acc (check_mutations b_info.initializer_ast candidates)
           )
        in
        (* Mutations from body (use body_candidates) *)
        let body_mutations = List.fold body ~init:String.Set.empty ~f:(fun acc form ->
            Set.union acc (check_mutations form body_candidates)
          )
        in
        Set.union init_mutations body_mutations
    | TypedAst.LetStar { bindings; body; _ } ->
        (* Process sequentially, updating candidates *)
        let final_mutations, _ = List.fold bindings ~init:(String.Set.empty, candidates)
          ~f:(fun (acc_mutations, current_candidates) (name, b_info) ->
            (* Check initializer mutations with current candidates *)
            let init_mut = check_mutations b_info.initializer_ast current_candidates in
            (* Update candidates for next step (remove newly bound var) *)
            let next_candidates = Set.remove current_candidates name in
            (Set.union acc_mutations init_mut, next_candidates)
          )
        in
        (* Candidates for the body are the ones left after processing all bindings *)
        let _, body_candidates = List.fold bindings ~init:([], candidates) ~f:(fun (_, current_candidates) (name, _) -> ([], Set.remove current_candidates name)) in
        let body_mutations = List.fold body ~init:String.Set.empty ~f:(fun acc form ->
            Set.union acc (check_mutations form body_candidates)
          )
        in
        Set.union final_mutations body_mutations
    | TypedAst.Lambda { args; body; _ } ->
        (* Collect all argument names *)
        let arg_names = args.required @ (List.map args.optional ~f:fst) @ (Option.to_list args.rest) in
        let arg_vars_set = String.Set.of_list arg_names in
        (* Candidates for the body exclude arguments *)
        let body_candidates = Set.diff candidates arg_vars_set in
        (* Mutations only happen within the body *)
        List.fold body ~init:String.Set.empty ~f:(fun acc form ->
          Set.union acc (check_mutations form body_candidates)
        )
    | TypedAst.Cond { clauses; _ } ->
        List.fold clauses ~init:String.Set.empty ~f:(fun acc (test_expr, body_exprs) ->
            let test_mut = check_mutations test_expr candidates in
            let body_mut = List.fold body_exprs ~init:String.Set.empty ~f:(fun acc' expr ->
                Set.union acc' (check_mutations expr candidates)
              )
            in
            String.Set.union_list [acc; test_mut; body_mut]
          )
    | TypedAst.Funcall { func; args; _ } ->
        let func_mut = check_mutations func candidates in
        let args_mut = List.fold args ~init:String.Set.empty ~f:(fun acc arg ->
            Set.union acc (check_mutations arg candidates)
          )
        in
        Set.union func_mut args_mut
    | TypedAst.Defun _ ->
        (* Defun defines a function at top level; mutations inside it *)
        (* don't affect outer lexical scopes being checked. *)
        (* We could check for mutations of *global* variables here if needed, *)
        (* but the current `check_mutations` focuses on lexical `candidates`. *)
        String.Set.empty


(* --- Type Change Analysis Helpers --- *)

(** Checks if two inferred types are compatible for assignment without boxing.
    Uses a strict definition: must be same base type or involve Any/Unknown/Var.
    Unions are compatible if the assigned type is compatible with any member. *)
let rec are_types_compatible (t_var: InferredType.t) (t_assigned: InferredType.t) : bool =
  let open InferredType in
  match (t_var, t_assigned) with
  (* Allow Any/Unknown/Var to be compatible with anything *)
  | T_Any, _ | _, T_Any | T_Unknown, _ | _, T_Unknown | T_Var _, _ | _, T_Var _ -> true
  (* Check for same base type *)
  | T_Nil, T_Nil -> true
  | T_Bool, T_Bool -> true
  | T_Int, T_Int -> true
  | T_Float, T_Float -> true
  | T_Char, T_Char -> true
  | T_String, T_String -> true
  | T_Symbol, T_Symbol -> true
  | T_Keyword, T_Keyword -> true
  (* TODO: Refine structural type compatibility? *)
  | T_Cons _, T_Cons _ -> true (* Assume compatible for now *)
  | T_Vector _, T_Vector _ -> true (* Assume compatible for now *)
  | T_Function _, T_Function _ -> true (* Assume compatible for now *)
  (* Handle Unions *)
  (* If var is a union, assigned must be compatible with at least one member *)
  | T_Union s1, t2 -> Set.exists s1 ~f:(fun member_t1 -> are_types_compatible member_t1 t2)
  (* If assigned is a union, it must be compatible with the var type *)
  (* (which means all members of assigned union must be compatible if var is concrete, *)
  (* or at least one member if var is also a union - handled by previous case) *)
  | t1, T_Union s2 -> Set.for_all s2 ~f:(fun member_t2 -> are_types_compatible t1 member_t2)
  (* Otherwise, incompatible *)
  | _, _ -> false

(** Recursively traverses the AST to find variables that are assigned
    incompatible types, indicating they need boxing.
    [var_initial_types]: Map from var name to its initial inferred type in the current scope. *)
let rec find_boxing_violations (ast: TypedAst.t) (var_initial_types: InferredType.t String.Map.t) : String.Set.t =
  match ast with
  | TypedAst.Atom _ | TypedAst.Quote _ -> String.Set.empty
  | TypedAst.Setq { pairs; _ } ->
      List.fold pairs ~init:String.Set.empty ~f:(fun acc (name, value_ast) ->
          let violations_in_value = find_boxing_violations value_ast var_initial_types in
          let current_violation =
            match Map.find var_initial_types name with
            | None -> String.Set.empty (* Global or undefined, ignore for boxing violation *)
            | Some initial_type ->
                let assigned_type = TypedAst.get_type value_ast in
                if are_types_compatible initial_type assigned_type then
                  String.Set.empty
                else
                  ( (* Debug print *)
                    (* printf "Boxing violation: var=%s, initial=%s, assigned=%s\n%!" name (InferredType.to_string initial_type) (InferredType.to_string assigned_type); *)
                    String.Set.singleton name (* Type violation! *)
                  )
          in
          String.Set.union_list [acc; violations_in_value; current_violation]
        )
  | TypedAst.Progn { forms; _ } ->
      List.fold forms ~init:String.Set.empty ~f:(fun acc form ->
          Set.union acc (find_boxing_violations form var_initial_types)
        )
  | TypedAst.If { cond; then_branch; else_branch; _ } ->
      let cond_v = find_boxing_violations cond var_initial_types in
      let then_v = find_boxing_violations then_branch var_initial_types in
      let else_v = Option.value_map else_branch ~default:String.Set.empty ~f:(fun e -> find_boxing_violations e var_initial_types) in
      String.Set.union_list [cond_v; then_v; else_v]
  | TypedAst.Let { bindings; body; _ } ->
      (* Get initial types for new bindings *)
      let inner_var_types =
        List.fold bindings ~init:var_initial_types ~f:(fun acc_types (name, b_info) ->
            Map.set acc_types ~key:name ~data:(TypedAst.get_type b_info.initializer_ast)
          )
      in
      (* Check initializers (use outer scope's types) *)
      let init_violations = List.fold bindings ~init:String.Set.empty ~f:(fun acc (_, b_info) ->
            Set.union acc (find_boxing_violations b_info.initializer_ast var_initial_types)
          )
      in
      (* Check body (use inner scope's types) *)
      let body_violations = List.fold body ~init:String.Set.empty ~f:(fun acc form ->
            Set.union acc (find_boxing_violations form inner_var_types)
          )
      in
      Set.union init_violations body_violations
  | TypedAst.LetStar { bindings; body; _ } ->
      (* Process sequentially, updating initial types map *)
      let init_violations, final_var_types =
        List.fold bindings ~init:(String.Set.empty, var_initial_types)
          ~f:(fun (acc_violations, current_types) (name, b_info) ->
              (* Check initializer with current types *)
              let init_v = find_boxing_violations b_info.initializer_ast current_types in
              (* Add new binding's initial type for next step *)
              let next_types = Map.set current_types ~key:name ~data:(TypedAst.get_type b_info.initializer_ast) in
              (Set.union acc_violations init_v, next_types)
            )
      in
      (* Check body using types from end of bindings *)
      let body_violations = List.fold body ~init:String.Set.empty ~f:(fun acc form ->
            Set.union acc (find_boxing_violations form final_var_types)
          )
      in
      Set.union init_violations body_violations
  | TypedAst.Lambda { args; body; _ } ->
       (* Get initial types for arguments (treat as Any for now, or use inferred?) *)
       (* Using Any simplifies things, as we only care about violations *within* the body *)
       let inner_var_types =
         let arg_names = args.required @ (List.map args.optional ~f:fst) @ (Option.to_list args.rest) in
         List.fold arg_names ~init:var_initial_types ~f:(fun acc_types name ->
             Map.set acc_types ~key:name ~data:InferredType.T_Any (* Assume Any initial type for args *)
           )
       in
       (* Check body using inner scope's types *)
       List.fold body ~init:String.Set.empty ~f:(fun acc form ->
         Set.union acc (find_boxing_violations form inner_var_types)
       )
  | TypedAst.Cond { clauses; _ } ->
      List.fold clauses ~init:String.Set.empty ~f:(fun acc (test_expr, body_exprs) ->
          let test_v = find_boxing_violations test_expr var_initial_types in
          let body_v = List.fold body_exprs ~init:String.Set.empty ~f:(fun acc' expr ->
              Set.union acc' (find_boxing_violations expr var_initial_types)
            )
          in
          String.Set.union_list [acc; test_v; body_v]
        )
  | TypedAst.Funcall { func; args; _ } ->
      let func_v = find_boxing_violations func var_initial_types in
      let args_v = List.fold args ~init:String.Set.empty ~f:(fun acc arg ->
          Set.union acc (find_boxing_violations arg var_initial_types)
        )
      in
      Set.union func_v args_v
  | TypedAst.Defun { args; body; _ } ->
      (* Analyze body, similar to Lambda *)
      let inner_var_types =
        let arg_names = args.required @ (List.map args.optional ~f:fst) @ (Option.to_list args.rest) in
        List.fold arg_names ~init:var_initial_types ~f:(fun acc_types name ->
            Map.set acc_types ~key:name ~data:InferredType.T_Any
          )
      in
      List.fold body ~init:String.Set.empty ~f:(fun acc form ->
        Set.union acc (find_boxing_violations form inner_var_types)
      )


(* --- Helper to analyze progn-like body --- *)
(* This remains largely the same, but will be called by the updated analyze_let etc. *)
let rec analyze_progn_body env body_values
    : TypedAst.t list * substitution * InferredType.t =
  let typed_body, final_subst =
    List.fold body_values ~init:([], Subst.empty)
      ~f:(fun (acc_nodes, acc_subst) value ->
        let current_env = List.map env ~f:(fun (name, ty) -> (name, apply_subst acc_subst ty)) in
        let typed_node, node_subst = analyze_expr current_env value in (* Analyze Value.t *)
        (acc_nodes @ [typed_node], compose_subst acc_subst node_subst)
      )
  in
  let result_type = match List.last typed_body with
    | None -> InferredType.T_Nil
    | Some last -> apply_subst final_subst (TypedAst.get_type last)
  in
  (typed_body, final_subst, result_type)

(* --- Core Analysis Function (Input: Value.t, Output: TypedAst.t * Substitution) --- *)
and analyze_expr (env : analysis_env) (value : Value.t)
    : TypedAst.t * substitution =
  match value with
  (* Atoms *)
  | Value.Nil -> (TypedAst.Atom { value; inferred_type = InferredType.T_Nil }, Subst.empty)
  | Value.T -> (TypedAst.Atom { value; inferred_type = InferredType.T_Bool }, Subst.empty)
  | Value.Int _ -> (TypedAst.Atom { value; inferred_type = InferredType.T_Int }, Subst.empty)
  | Value.Float _ -> (TypedAst.Atom { value; inferred_type = InferredType.T_Float }, Subst.empty)
  | Value.String _ -> (TypedAst.Atom { value; inferred_type = InferredType.T_String }, Subst.empty)
  | Value.Keyword _ -> (TypedAst.Atom { value; inferred_type = InferredType.T_Keyword }, Subst.empty)
  | Value.Char _ -> (TypedAst.Atom { value; inferred_type = InferredType.T_Char }, Subst.empty)
  | Value.Vector _ -> (* Type vector based on elements? Simplified: Any *)
      (TypedAst.Atom { value; inferred_type = InferredType.T_Vector {element_type = T_Any} }, Subst.empty)
  | Value.Function _ | Value.Builtin _ -> (* Opaque function types *)
       (TypedAst.Atom { value; inferred_type = InferredType.T_Function {arg_types=None; return_type=T_Any} }, Subst.empty)

  | Value.Symbol {name} as atom_val ->
      (* Look up symbol in environment *)
      let inferred_t = match List.Assoc.find env name ~equal:String.equal with
                       | Some t -> t
                       | None -> InferredType.T_Symbol (* Assume global or undefined *)
      in
      (TypedAst.Atom { value = atom_val; inferred_type = inferred_t }, Subst.empty)

  (* Cons Cell: Potential special form or function call *)
  | Value.Cons { car; cdr } ->
      analyze_cons_cell env car cdr

(* Helper to analyze cons cells *)
and analyze_cons_cell env car_val cdr_val : TypedAst.t * substitution =
    match car_val with
    (* --- Special Forms --- *)
    | Value.Symbol {name="quote"} ->
        (match Value.value_to_list_opt cdr_val with
         | Some [data] ->
             let inferred_type = type_of_quoted_data data in
             (TypedAst.Quote { value = data; inferred_type }, Subst.empty)
         | _ -> failwith "Malformed quote: expected exactly one argument")

    | Value.Symbol {name="if"} ->
        (match Value.value_to_list_opt cdr_val with
         | Some [c; t] -> analyze_if env c t None
         | Some [c; t; e] -> analyze_if env c t (Some e)
         | _ -> failwith "Malformed if: expected 2 or 3 arguments")

    | Value.Symbol {name="progn"} ->
        let body_values = Value.value_to_list_opt cdr_val |> Option.value ~default:[] in
        let typed_forms, final_subst, result_type = analyze_progn_body env body_values in
        (TypedAst.Progn { forms = typed_forms; inferred_type = result_type }, final_subst)

    | Value.Symbol {name="let"} ->
        (match Value.value_to_list_opt cdr_val with
         | Some (bindings_val :: body_values) ->
             analyze_let env bindings_val body_values
         | _ -> failwith "Malformed let: expected bindings list and body")

    | Value.Symbol {name="let*"} ->
        (match Value.value_to_list_opt cdr_val with
         | Some (bindings_val :: body_values) ->
             analyze_let_star env bindings_val body_values
         | _ -> failwith "Malformed let*: expected bindings list and body")

    | Value.Symbol {name="setq"} ->
        let pairs = Value.value_to_list_opt cdr_val |> Option.value ~default:[] in
        analyze_setq env pairs

    | Value.Symbol {name="lambda"} ->
        (match Value.value_to_list_opt cdr_val with
         | Some (arg_list_val :: body_values) ->
             analyze_lambda env arg_list_val body_values
         | _ -> failwith "Malformed lambda: expected arg list and body")

    | Value.Symbol {name="defun"} ->
        (match Value.value_to_list_opt cdr_val with
         | Some (Value.Symbol {name} :: arg_list_val :: body_values) ->
             analyze_defun env name arg_list_val body_values
         | _ -> failwith "Malformed defun: expected name symbol, arg list, and body")

    | Value.Symbol {name="cond"} ->
        let clauses = Value.value_to_list_opt cdr_val |> Option.value ~default:[] in
        analyze_cond env clauses

    (* --- Default: Assume Function Call --- *)
    | _ ->
        let args_values = Value.value_to_list_opt cdr_val |> Option.value ~default:[] in
        analyze_funcall env car_val args_values (* Analyze car_val as the function *)


(* --- Special Form Handlers (Need full rewrite logic for Value.t) --- *)

and analyze_if env c_val t_val e_val_opt : TypedAst.t * substitution =
  (* Analyze condition (c_val) *)
  let typed_cond, s_cond = analyze_expr env c_val in
  let env_after_cond = List.map env ~f:(fun (n,ty) -> (n, apply_subst s_cond ty)) in
  (* Analyze then branch (t_val) *)
  let typed_then, s_then = analyze_expr env_after_cond t_val in
  let subst_after_then = compose_subst s_cond s_then in
  let env_after_then = List.map env ~f:(fun (n,ty) -> (n, apply_subst subst_after_then ty)) in
  (* Analyze else branch (e_val_opt) *)
  let typed_else_opt, final_subst = match e_val_opt with
    | None -> (None, subst_after_then)
    | Some e_val ->
        let typed_else, s_else = analyze_expr env_after_then e_val in
        (Some typed_else, compose_subst subst_after_then s_else)
  in
  (* Determine result type *)
  let then_type = apply_subst final_subst (TypedAst.get_type typed_then) in
  let else_type = match typed_else_opt with None -> InferredType.T_Nil | Some te -> apply_subst final_subst (TypedAst.get_type te) in
  let result_type = InferredType.type_union then_type else_type in
  (TypedAst.If { cond=typed_cond; then_branch=typed_then; else_branch=typed_else_opt; inferred_type = result_type }, final_subst)


and analyze_let env bindings_val body_values : TypedAst.t * substitution =
  let bindings_list = match Value.value_to_list_opt bindings_val with
    | Some l -> l | None -> failwith "Let bindings must be a proper list" in
  (* Analyze initializers in outer env *)
  let analyzed_bindings_tmp, init_subst =
    List.fold bindings_list ~init:([], Subst.empty)
      ~f:(fun (acc_b, acc_s) b_val ->
        let name, init_val = match b_val with
          | Value.Symbol {name=n} -> (n, Value.Nil)
          | Value.Cons {car= Value.Symbol {name=n}; cdr=init_list_val} ->
              (match Value.value_to_list_opt init_list_val with
               | Some [i] -> (n, i) | _ -> failwith "Malformed let binding (init list)")
          | _ -> failwith "Malformed let binding (structure)"
        in
        let env_for_init = List.map env ~f:(fun (n,ty)->(n, apply_subst acc_s ty)) in
        let typed_init, init_s = analyze_expr env_for_init init_val in
        (acc_b @ [(name, typed_init)], compose_subst acc_s init_s)
      ) in
  (* Create inner env *)
  let inner_env_bindings = List.map analyzed_bindings_tmp ~f:(fun (n,ti) -> (n, apply_subst init_subst (TypedAst.get_type ti))) in
  let inner_env = add_bindings env inner_env_bindings in
  (* Analyze body *)
  let typed_body, body_subst, result_type = analyze_progn_body inner_env body_values in
  let final_subst = compose_subst init_subst body_subst in
  let final_result_type = apply_subst final_subst result_type in

  (* Perform mutation analysis *)
  let bound_names = List.map analyzed_bindings_tmp ~f:fst in
  let bound_vars_set = String.Set.of_list bound_names in
  (* Check for mutations of the bound vars within the fully analyzed body *)
  let mutated_in_body = List.fold typed_body ~init:String.Set.empty ~f:(fun acc form ->
      Set.union acc (check_mutations form bound_vars_set)
    )
  in

  (* Construct final bindings with mutation info *)
  let final_bindings = List.map analyzed_bindings_tmp ~f:(fun (name, typed_init) ->
      let binding_info = {
          TypedAst.initializer_ast = typed_init;
          is_mutated = Set.mem mutated_in_body name; (* Set based on analysis *)
      } in
      (name, binding_info)
    ) in

  (TypedAst.Let { bindings = final_bindings; body = typed_body; inferred_type = final_result_type }, final_subst)


and analyze_let_star env bindings_val body_values : TypedAst.t * substitution =
   let bindings_list = match Value.value_to_list_opt bindings_val with
    | Some l -> l | None -> failwith "Let* bindings must be a proper list" in
   (* Fold through bindings sequentially to get typed initializers and final env *)
   let bindings_env, analyzed_bindings_tmp, bindings_subst =
     List.fold bindings_list ~init:(env, [], Subst.empty)
       ~f:(fun (current_env, acc_b, acc_s) b_val ->
         let name, init_val = match b_val with
           | Value.Symbol {name=n} -> (n, Value.Nil)
           | Value.Cons {car=Value.Symbol {name=n}; cdr=init_list_val} ->
              (match Value.value_to_list_opt init_list_val with
               | Some [i] -> (n, i) | _ -> failwith "Malformed let* binding (init list)")
           | _ -> failwith "Malformed let* binding (structure)"
         in
         let env_for_init = List.map current_env ~f:(fun (n,ty)->(n, apply_subst acc_s ty)) in
         let typed_init, init_s = analyze_expr env_for_init init_val in
         let combined_subst = compose_subst acc_s init_s in
         let binding_type = apply_subst combined_subst (TypedAst.get_type typed_init) in
         let next_env = add_binding current_env name binding_type in
         (next_env, acc_b @ [(name, typed_init)], combined_subst)
       ) in
   (* Analyze body *)
   let body_env = List.map bindings_env ~f:(fun (n,ty)->(n, apply_subst bindings_subst ty)) in
   let typed_body, body_subst, result_type = analyze_progn_body body_env body_values in
   let final_subst = compose_subst bindings_subst body_subst in
   let final_result_type = apply_subst final_subst result_type in

   (* Perform mutation analysis for let* *)
   let final_bindings =
     List.mapi analyzed_bindings_tmp ~f:(fun i (name_i, typed_init_i) ->
         (* Subsequent ASTs include initializers of later bindings and the body *)
         let subsequent_init_asts =
           List.map (List.drop analyzed_bindings_tmp (i + 1)) ~f:snd
         in
         let subsequent_asts = subsequent_init_asts @ typed_body in
         (* Check if name_i is mutated in any subsequent AST *)
         let is_mutated =
           List.exists subsequent_asts ~f:(fun ast ->
             not (Set.is_empty (check_mutations ast (String.Set.singleton name_i)))
           )
         in
         let binding_info = {
             TypedAst.initializer_ast = typed_init_i;
             is_mutated = is_mutated; (* Set based on sequential analysis *)
         } in
         (name_i, binding_info)
       )
   in

   (TypedAst.LetStar { bindings = final_bindings; body = typed_body; inferred_type = final_result_type }, final_subst)


and analyze_setq env pairs_values : TypedAst.t * substitution =
  if List.length pairs_values % 2 <> 0 then failwith "Setq needs even args";
  let rec process_pairs pairs acc_typed_pairs acc_subst =
    match pairs with
    | [] -> (List.rev acc_typed_pairs, acc_subst)
    | Value.Symbol {name=var_name} :: value_form :: rest ->
        let env_for_value = List.map env ~f:(fun (n,ty)->(n, apply_subst acc_subst ty)) in
        let typed_value, value_subst = analyze_expr env_for_value value_form in
        let current_subst = compose_subst acc_subst value_subst in
        let value_type = apply_subst current_subst (TypedAst.get_type typed_value) in
        (* Unify with existing type *)
        let final_subst = match List.Assoc.find env var_name ~equal:String.equal with
          | Some existing_type ->
              (try compose_subst current_subst (unify (apply_subst current_subst existing_type) value_type)
               with Unification_error _ -> current_subst (* Ignore unification error on setq *))
          | None -> current_subst
        in
        process_pairs rest ((var_name, typed_value) :: acc_typed_pairs) final_subst
    | not_symbol :: _ -> failwithf "Setq expected symbol, got %s" (!Value.to_string not_symbol) ()
  in
  let typed_pairs, final_subst = process_pairs pairs_values [] Subst.empty in
  let result_type = match List.last typed_pairs with None -> InferredType.T_Nil | Some (_,v) -> apply_subst final_subst (TypedAst.get_type v) in
  (TypedAst.Setq({ pairs = typed_pairs; inferred_type = result_type }), final_subst)


and analyze_lambda env arg_list_val body_values : TypedAst.t * substitution =
  let arg_spec = ArgListParser.parse arg_list_val in
  (* Create fresh vars for args *)
  let create_binding name = (name, generate_fresh_type_var()) in
  let arg_bindings =
     List.map arg_spec.required ~f:create_binding @
     List.map arg_spec.optional ~f:(fun (n,_) -> create_binding n) @
     (match arg_spec.rest with Some n -> [create_binding n] | None -> [])
   in
  let inner_env = add_bindings env arg_bindings in
  (* Analyze body *)
  let typed_body, body_subst, body_return_type = analyze_progn_body inner_env body_values in
  (* Determine final signature *)
  let final_arg_types = List.map arg_bindings ~f:(fun (_, ty) -> apply_subst body_subst ty) in
  let final_return_type = apply_subst body_subst body_return_type in
  let fun_info = { InferredType.arg_types = Some final_arg_types; return_type = final_return_type } in
  let inferred_type = InferredType.T_Function fun_info in
  (* Pass the *parsed* arg_spec, not the value *)
  (* Note: Mutation analysis for lambda arguments is implicitly handled by *)
  (* check_mutations when called on the lambda body from an outer scope, *)
  (* as it removes arg names from candidates passed down. *)
  let node = TypedAst.Lambda { args = arg_spec; body = typed_body; inferred_type } in
  (node, Subst.empty) (* Lambda subst is internal *)


and analyze_defun env name arg_list_val body_values : TypedAst.t * substitution =
  let arg_spec = ArgListParser.parse arg_list_val in
  (* Create fresh vars *)
  let arg_bindings =
     List.map arg_spec.required ~f:(fun n->(n, generate_fresh_type_var())) @
     List.map arg_spec.optional ~f:(fun (n,_)->(n, generate_fresh_type_var())) @
     (match arg_spec.rest with Some n -> [(n, generate_fresh_type_var())] | None -> []) in
   let initial_ret_type_var = generate_fresh_type_var() in
   let initial_fun_type = InferredType.T_Function { arg_types = Some (List.map arg_bindings ~f:snd); return_type = initial_ret_type_var } in
   (* Add function itself for recursion *)
   let env_for_body = add_bindings (add_binding env name initial_fun_type) arg_bindings in
   (* Analyze body *)
   let typed_body, body_subst, body_return_type = analyze_progn_body env_for_body body_values in
   (* Unify return types *)
   let final_subst = try compose_subst body_subst (unify (apply_subst body_subst initial_ret_type_var) (apply_subst body_subst body_return_type)) with Unification_error _ -> body_subst in
   (* Final signature *)
   let final_arg_types = List.map arg_bindings ~f:(fun (_,ty) -> apply_subst final_subst ty) in
   let final_return_type = apply_subst final_subst body_return_type in
   let final_fun_info = { InferredType.arg_types = Some final_arg_types; return_type = final_return_type } in
   let final_fun_type = InferredType.T_Function final_fun_info in
   (* Pass parsed arg_spec *)
   (* Defun implicitly creates a mutable binding at top level *)
   let node = TypedAst.Defun { name = name; args = arg_spec; body = typed_body; fun_type = final_fun_type; inferred_type = InferredType.T_Symbol } in
   (node, Subst.empty) (* Defun subst handled in toplevel *)


and analyze_cond env clause_values : TypedAst.t * substitution =
  let analyzed_clauses, final_subst, result_type =
    List.fold clause_values ~init:([], Subst.empty, InferredType.T_Nil)
      ~f:(fun (acc_clauses, acc_subst, acc_type) clause_val ->
        match Value.value_to_list_opt clause_val with
        | Some (test_val :: body_vals) ->
            let env_for_clause = List.map env ~f:(fun (n,ty) -> (n, apply_subst acc_subst ty)) in
            let typed_test, test_subst = analyze_expr env_for_clause test_val in
            let composed_subst = compose_subst acc_subst test_subst in
            let env_after_test = List.map env ~f:(fun (n,ty)->(n, apply_subst composed_subst ty)) in
            (* Analyze body *)
            let typed_body, body_subst, clause_result_type =
              if List.is_empty body_vals then
                 ([typed_test], Subst.empty, apply_subst composed_subst (TypedAst.get_type typed_test))
              else
                 analyze_progn_body env_after_test body_vals
            in
            let final_clause_subst = compose_subst composed_subst body_subst in
            let final_clause_type = apply_subst final_clause_subst clause_result_type in
            (acc_clauses @ [(typed_test, typed_body)], final_clause_subst, InferredType.type_union acc_type final_clause_type)
        | _ -> failwith "Malformed cond clause: must be a list"
      )
  in
  (TypedAst.Cond ({ clauses = analyzed_clauses; inferred_type = result_type }), final_subst)


and analyze_funcall env func_val args_values : TypedAst.t * substitution =
  (* Analyze function expression *)
  let typed_head, head_subst = analyze_expr env func_val in
  (* Analyze arguments sequentially *)
  let args_subst, typed_args = List.fold_map args_values ~init:head_subst
    ~f:(fun acc_s arg_val ->
      let env_for_arg = List.map env ~f:(fun (n,ty)->(n, apply_subst acc_s ty)) in
      let typed_arg, arg_s = analyze_expr env_for_arg arg_val in
      (compose_subst acc_s arg_s, typed_arg)
    )
  in
  (* Get types after substitutions *)
  let func_type = apply_subst args_subst (TypedAst.get_type typed_head) in
  let actual_arg_types = List.map typed_args ~f:(fun ta -> apply_subst args_subst (TypedAst.get_type ta)) in

  (* Unify with signature helper *)
  let unify_with_sig (finfo: InferredType.fun_info) : InferredType.t * substitution =
    try
      let sig_arg_types_opt, sig_return_type = instantiate_fun_sig finfo in
      match sig_arg_types_opt with
      | None -> (sig_return_type, args_subst) (* Varargs *)
      | Some sig_arg_types ->
          if List.length sig_arg_types <> List.length actual_arg_types then
            raise (Unification_error "Arity mismatch")
          else
            let final_subst = List.fold2_exn sig_arg_types actual_arg_types ~init:args_subst
              ~f:(fun current_subst sig_arg actual_arg ->
                  compose_subst current_subst (unify (apply_subst current_subst sig_arg) (apply_subst current_subst actual_arg)))
            in (apply_subst final_subst sig_return_type, final_subst)
    with Unification_error _ -> (InferredType.T_Unknown, args_subst) (* Fallback *)
  in

  (* Determine result type *)
  let result_type, final_subst = match func_type with
    | InferredType.T_Function finfo -> unify_with_sig finfo
    | InferredType.T_Symbol | T_Keyword -> (* Check builtins *)
        (match func_val with
         | Value.Symbol {name} | Value.Keyword name ->
             (match get_builtin_signature name with Some finfo -> unify_with_sig finfo | None -> (InferredType.T_Any, args_subst))
         | _ -> (InferredType.T_Any, args_subst))
    | InferredType.T_Any -> (T_Any, args_subst) | T_Unknown -> (T_Unknown, args_subst)
    | InferredType.T_Union _ -> (T_Any, args_subst) (* Simplified union call *)
    | _ -> (InferredType.T_Unknown, args_subst) (* Calling non-function *)
  in
  (TypedAst.Funcall { func = typed_head; args = typed_args; inferred_type = result_type }, final_subst)


(* --- Top Level Analysis --- *)
(* Modified return type to include set of vars needing boxing *)
let analyze_toplevel (values : Value.t list)
    : TypedAst.t list * (string * InferredType.t) list * String.Set.t =
  let final_env_map = ref String.Map.empty in
  let final_subst = ref Subst.empty in

  (* Pass 1: Type inference and substitution application *)
  let typed_asts = List.map values ~f:(fun value ->
      let current_env = Map.to_alist !final_env_map in
      let typed_ast, subst = analyze_expr current_env value in
      final_subst := compose_subst !final_subst subst;
      (* Update global env for defun *)
      (match typed_ast with
       | TypedAst.Defun { name; fun_type; _ } ->
           final_env_map := Map.set !final_env_map ~key:name ~data:(apply_subst !final_subst fun_type)
       | _ -> ()
      );
      final_env_map := Map.map !final_env_map ~f:(apply_subst !final_subst);
      typed_ast
    )
  in
  (* Final pass to apply substitution to TAST *)
  let rec final_apply tast =
    let apply_t = apply_subst !final_subst in
    match tast with
    | TypedAst.Atom ({ inferred_type=t; _ } as r) -> TypedAst.Atom { r with inferred_type = apply_t t }
    | TypedAst.Quote ({ inferred_type=t; _ } as r) -> TypedAst.Quote { r with inferred_type = apply_t t }
    | TypedAst.If ({ inferred_type=t; cond; then_branch; else_branch; _ }) -> TypedAst.If { cond=final_apply cond; then_branch=final_apply then_branch; else_branch=Option.map else_branch ~f:final_apply; inferred_type=apply_t t }
    | TypedAst.Progn ({ inferred_type=t; forms; _ }) -> TypedAst.Progn { forms=List.map forms ~f:final_apply; inferred_type=apply_t t }
    | TypedAst.Let ({ inferred_type=t; bindings; body; _ }) ->
        (* Apply to binding_info - Explicit record construction *)
        let final_apply_binding (name, b_info) =
            (* Apply user's requested syntax, although likely incorrect *)
            let new_init_ast = final_apply b_info.TypedAst.initializer_ast in
            (name, { TypedAst.initializer_ast = new_init_ast; is_mutated = b_info.is_mutated })
        in
        TypedAst.Let { bindings=List.map bindings ~f:final_apply_binding; body=List.map body ~f:final_apply; inferred_type=apply_t t }
    | TypedAst.LetStar ({ inferred_type=t; bindings; body; _ }) ->
        (* Apply to binding_info - Explicit record construction *)
         let final_apply_binding (name, b_info) =
             (* Apply user's requested syntax, although likely incorrect *)
             let new_init_ast = final_apply b_info.TypedAst.initializer_ast in
             (name, { TypedAst.initializer_ast = new_init_ast; is_mutated = b_info.is_mutated })
         in
        TypedAst.LetStar { bindings=List.map bindings ~f:final_apply_binding; body=List.map body ~f:final_apply; inferred_type=apply_t t }
    | TypedAst.Setq ({ inferred_type=t; pairs; _ }) -> TypedAst.Setq { pairs=List.map pairs ~f:(fun (n,t)->(n, final_apply t)); inferred_type=apply_t t }
    | TypedAst.Lambda ({ inferred_type=t; body; _ } as r) -> TypedAst.Lambda { r with body=List.map body ~f:final_apply; inferred_type=apply_t t }
    | TypedAst.Defun ({ inferred_type=t; fun_type; body; _ } as r) -> TypedAst.Defun { r with body=List.map body ~f:final_apply; fun_type=apply_t fun_type; inferred_type=apply_t t }
    | TypedAst.Cond ({ inferred_type=t; clauses; _ }) -> TypedAst.Cond { clauses=List.map clauses ~f:(fun (tst,bdy)->(final_apply tst, List.map bdy ~f:final_apply)); inferred_type=apply_t t }
    | TypedAst.Funcall ({ inferred_type=t; func; args; _ }) -> TypedAst.Funcall { func=final_apply func; args=List.map args ~f:final_apply; inferred_type=apply_t t }
  in
  let final_tasts = List.map typed_asts ~f:final_apply in
  let final_env_alist = Map.to_alist !final_env_map in

  (* Pass 2: Type Change Analysis *)
  let initial_var_types = String.Map.of_alist_exn final_env_alist in
  let needs_boxing_set = List.fold final_tasts ~init:String.Set.empty ~f:(fun acc tast ->
      Set.union acc (find_boxing_violations tast initial_var_types)
    )
  in

  (final_tasts, final_env_alist, needs_boxing_set) (* Return TASTs, final env types, and set of vars needing boxing *)


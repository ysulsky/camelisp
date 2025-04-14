(* Translate.ml - Translates Typed Elisp AST into OCaml code (Refactored) *)

open! Core
(* REMOVED: open! Sexplib.Std *)
(* REMOVED open! Scaml *)

(* Use types/modules directly *)
module Analyze = Analyze (* Keep Analyze for TypedAst reference below *)
module TypedAst = Analyze.TypedAst (* Use the definition from Analyze *)
module Value = Value
module InferredType = InferredType
module Runtime = Runtime (* Needed for generated code *)
module Compiler = Compiler (* Needed for generated code *)

(* --- Helper Module for Quoted Data Translation (from Value.t) --- *)
module Translate_quote = struct
  let rec translate_quoted_data (value : Value.t) : string =
    match value with
    | Value.Nil -> "Value.Nil"
    | Value.T -> "Value.T"
    | Value.Int i -> sprintf "(Value.Int %d)" i
    | Value.Float f -> sprintf "(Value.Float %F)" f (* Use %F *)
    | Value.String s -> sprintf "(Value.String %S)" s
    | Value.Symbol sd -> sprintf "(Value.Symbol { name = %S })" sd.name
    | Value.Keyword k -> sprintf "(Value.Keyword %S)" k
    | Value.Char c -> sprintf "(Value.Char %C)" c (* Use %C *)
    | Value.Vector arr ->
        let elements_code =
          Array.map arr ~f:translate_quoted_data |> Array.to_list
        in
        sprintf "(Value.Vector [|%s|])" (String.concat ~sep:"; " elements_code)
    | Value.Cons { car; cdr } ->
        sprintf "(Value.Cons { car = (%s); cdr = (%s) })"
          (translate_quoted_data car)
          (translate_quoted_data cdr)
    | Value.Function _ -> "\"(Value.Function <opaque>)\""
    | Value.Builtin _ -> "\"(Value.Builtin <opaque>)\""

end

(* --- Environment --- *)
type var_repr = R_Value | R_Int | R_Float | R_Bool [@@deriving sexp_of]

(* Modified: env_entry now includes is_mutated *)
type env_entry = {
  ocaml_name : string;
  repr : var_repr;
  is_mutated : bool; (* From analysis: Can this binding be modified by setq? *)
}

type translation_env = env_entry String.Map.t

let ocaml_var_counter = ref 0

let generate_ocaml_var prefix =
  let sanitized_prefix =
    Str.global_replace (Str.regexp "[^a-zA-Z0-9_]") "_" prefix
  in
  let safe_prefix =
    if String.is_empty sanitized_prefix
       || not (Char.is_alpha sanitized_prefix.[0])
    then "v_" ^ sanitized_prefix
    else sanitized_prefix
  in
  incr ocaml_var_counter;
  sprintf "%s_%d_" safe_prefix !ocaml_var_counter

let lookup_var_info env elisp_name = Map.find env elisp_name

(* Modified: add_binding now includes is_mutated *)
let add_binding env elisp_name ocaml_name repr is_mutated =
  Map.set env ~key:elisp_name ~data:{ ocaml_name; repr; is_mutated }

(* Modified: add_bindings expects entries with is_mutated *)
let add_bindings env bindings =
  List.fold bindings ~init:env ~f:(fun current_env (elisp_name, entry) ->
      Map.set current_env ~key:elisp_name ~data:entry)

(* --- Boxing/Unboxing Helpers (Keep as is) --- *)
let box_int int_code = sprintf "(Value.Int (%s))" int_code

let unbox_int value_code =
  sprintf
    "(match %s with \
     Value.Int i -> i | \
     v -> Runtime.type_error \"(unbox)\" \"integer\" v)"
    value_code

let box_float float_code = sprintf "(Value.Float (%s))" float_code

let unbox_float value_code =
  sprintf
    "(match %s with \
     Value.Float f -> f | \
     v -> Runtime.type_error \"(unbox)\" \"float\" v)"
    value_code

let box_bool bool_code = sprintf "(if %s then Value.T else Value.Nil)" bool_code

let unbox_bool value_code = sprintf "(Runtime.is_truthy (%s))" value_code

let manual_indent n s =
  String.split_lines s
  |> List.map ~f:(fun line -> String.make n ' ' ^ line)
  |> String.concat ~sep:"\n"

(* --- Core Translation Functions --- *)
let rec to_value env expr = translate_expr env expr R_Value

and to_int env expr = translate_expr env expr R_Int

and to_float env expr = translate_expr env expr R_Float

and to_bool env expr = translate_expr env expr R_Bool

and translate_expr env texpr target_repr =
  let node_type = TypedAst.get_type texpr in
  let generated_code = translate_node env texpr in
  let source_repr =
    match node_type with
    | InferredType.T_Int -> R_Int
    | InferredType.T_Float -> R_Float
    | InferredType.T_Nil | T_Bool -> R_Bool
    | _ -> R_Value
  in
  match (source_repr, target_repr) with
  (* Boxing *)
  | R_Int, R_Value -> box_int generated_code
  | R_Float, R_Value -> box_float generated_code
  | R_Bool, R_Value -> box_bool generated_code
  (* Unboxing *)
  | R_Value, R_Int -> unbox_int generated_code
  | R_Value, R_Float -> unbox_float generated_code
  | R_Value, R_Bool -> unbox_bool generated_code
  (* Native Conversions *)
  | R_Int, R_Float -> sprintf "(Float.of_int %s)" generated_code
  | R_Float, R_Int -> sprintf "(Int.of_float %s)" generated_code
  | R_Bool, R_Int -> sprintf "(if %s then 1 else 0)" generated_code
  | R_Bool, R_Float -> sprintf "(if %s then 1.0 else 0.0)" generated_code
  | R_Int, R_Bool -> sprintf "(%s <> 0)" generated_code
  | R_Float, R_Bool -> sprintf "(%s <> 0.0)" generated_code
  (* No conversion needed *)
  | R_Value, R_Value
  | R_Int, R_Int
  | R_Float, R_Float
  | R_Bool, R_Bool -> generated_code

and translate_node env texpr =
  match texpr with
  | TypedAst.Atom { value; inferred_type } -> begin
      match inferred_type with
      (* Literals of basic types *)
      | InferredType.T_Int -> (match value with Value.Int i -> Int.to_string i | _ -> failwith "Type mismatch")
      | InferredType.T_Float -> (match value with Value.Float f -> Float.to_string f | _ -> failwith "Type mismatch")
      | InferredType.T_Nil -> "false"
      | InferredType.T_Bool -> (match value with Value.T -> "true" | _ -> "false") (* Assume T=true, others=false *)
      | InferredType.T_Keyword -> (match value with Value.Keyword k -> sprintf "(Value.Keyword %S)" k | _ -> failwith "Type mismatch")
      | InferredType.T_String -> (match value with Value.String s -> sprintf "(Value.String %S)" s | _ -> failwith "Type mismatch")
      | InferredType.T_Char -> (match value with Value.Char c -> sprintf "(Value.Char %C)" c | _ -> failwith "Type mismatch")

      (* Symbol: Look up in environment *)
      | InferredType.T_Symbol -> (
          match value with
          | Value.Symbol { name } -> (
              match lookup_var_info env name with
              (* Local variables: access depends on mutation status *)
              | Some { ocaml_name; repr = R_Value; is_mutated=true } -> sprintf "!%s" ocaml_name (* Value.t ref *)
              | Some { ocaml_name; repr = R_Int; is_mutated=true } -> sprintf "!%s" ocaml_name (* int ref *)
              | Some { ocaml_name; repr = R_Float; is_mutated=true } -> sprintf "!%s" ocaml_name (* float ref *)
              | Some { ocaml_name; repr = R_Bool; is_mutated=true } -> sprintf "!%s" ocaml_name (* bool ref *)
              | Some { ocaml_name; repr = R_Value; is_mutated=false } -> ocaml_name (* Direct Value.t *)
              | Some { ocaml_name; repr = R_Int; is_mutated=false } -> ocaml_name (* Direct int *)
              | Some { ocaml_name; repr = R_Float; is_mutated=false } -> ocaml_name (* Direct float *)
              | Some { ocaml_name; repr = R_Bool; is_mutated=false } -> ocaml_name (* Direct bool *)
              (* Globals: lookup via runtime *)
              | None -> sprintf "(Runtime.lookup_variable %S)" name
              )
          | _ -> failwith "Type mismatch: T_Symbol but not Value.Symbol"
         )

      (* Other types are represented as Value.t *)
      | InferredType.T_Var _ | T_Cons _ | T_Vector _ | T_Function _ | T_Union _ | T_Any | T_Unknown -> (
          match value with
          | Value.Symbol { name } -> (
              (* Symbol representing a complex value - check local/global *)
              match lookup_var_info env name with
              (* Assume complex types are always Value.t, check mutation *)
              | Some { ocaml_name; is_mutated=true; _ } -> sprintf "!%s" ocaml_name (* Value.t ref *)
              | Some { ocaml_name; is_mutated=false; _ } -> ocaml_name (* Direct Value.t *)
              | None -> sprintf "(Runtime.lookup_variable %S)" name
             )
          (* Atom itself is the complex value (e.g., literal vector) *)
          | _ -> Translate_quote.translate_quoted_data value
          )
    end
  | TypedAst.Quote { value; inferred_type = _ } ->
      Translate_quote.translate_quoted_data value
  | TypedAst.If { cond; then_branch; else_branch; inferred_type } ->
      let cond_code = to_bool env cond in
      let target_repr =
        match inferred_type with
        | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
        | _ -> R_Value
      in
      let then_code = translate_expr env then_branch target_repr in
      let else_code =
        match else_branch with
        | None -> translate_expr env (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil }) target_repr
        | Some eb -> translate_expr env eb target_repr
      in
      sprintf "(if %s then\n   %s\n else\n   %s)" cond_code
        (manual_indent 3 then_code) (manual_indent 3 else_code)
  | TypedAst.Progn { forms; inferred_type } ->
      translate_progn env forms inferred_type
  | TypedAst.Let { bindings; body; inferred_type } ->
      translate_let env bindings body inferred_type
  | TypedAst.LetStar { bindings; body; inferred_type } ->
      translate_let_star env bindings body inferred_type
  | TypedAst.Setq { pairs; inferred_type } ->
      translate_setq env pairs inferred_type
  | TypedAst.Lambda { args; body; inferred_type } ->
      translate_lambda env args body inferred_type
  | TypedAst.Defun { name; _ } ->
      (* Defun expression evaluates to the symbol name *)
      sprintf "(Value.Symbol { name = %S })" name
  | TypedAst.Cond { clauses; inferred_type } ->
      translate_cond env clauses inferred_type
  | TypedAst.Funcall { func; args; inferred_type } ->
      translate_funcall env func args inferred_type

and translate_progn env forms inferred_type =
  match forms with
  | [] ->
      translate_expr env (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil })
        (match inferred_type with
         | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value)
  | [ last ] -> translate_node env last
  | _ ->
      let target_repr =
        match inferred_type with
        | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
        | _ -> R_Value
      in
      let translated_forms_side_effects = List.map (List.drop_last_exn forms) ~f:(fun expr -> to_value env expr) in
      let last_form = List.last_exn forms in
      let translated_last = translate_expr env last_form target_repr in
      let sequence_code = List.map translated_forms_side_effects ~f:(sprintf "let (_ : Value.t) = %s in") |> String.concat ~sep:"\n  " in
      if String.is_empty sequence_code then translated_last
      else sprintf "(%s\n  %s)" sequence_code translated_last

and translate_let env bindings body inferred_type =
  let inner_env_ref = ref env in
  let let_bindings_code_list =
    List.map bindings ~f:(fun (elisp_name, binding_info) ->
        let typed_init = binding_info.TypedAst.initializer_ast in
        let is_mutated = binding_info.TypedAst.is_mutated in
        let init_type = TypedAst.get_type typed_init in
        let ocaml_name = generate_ocaml_var elisp_name in

        (* Determine representation based on type (and later, type changes) *)
        (* TODO: Add type change analysis *)
        let repr, init_code =
          match init_type with
          | InferredType.T_Int -> (R_Int, to_int env typed_init)
          | InferredType.T_Float -> (R_Float, to_float env typed_init)
          | InferredType.T_Bool | T_Nil -> (R_Bool, to_bool env typed_init)
          | _ -> (R_Value, to_value env typed_init)
        in

        (* Add binding to the environment for the body *)
        inner_env_ref := add_binding !inner_env_ref elisp_name ocaml_name repr is_mutated;

        (* Generate OCaml let binding: use ref only if mutated *)
        let ocaml_type_annot, binding_keyword =
           match repr, is_mutated with
           | R_Int, true -> (": int ref", "ref")
           | R_Float, true -> (": float ref", "ref")
           | R_Bool, true -> (": bool ref", "ref")
           | R_Value, true -> (": Value.t ref", "ref")
           | R_Int, false -> (": int", "") (* Direct binding *)
           | R_Float, false -> (": float", "")
           | R_Bool, false -> (": bool", "")
           | R_Value, false -> (": Value.t", "")
        in
        (* Add space only if keyword is not empty *)
        let keyword_space = if String.is_empty binding_keyword then "" else " " in
        sprintf "let %s %s =%s%s (%s) in" ocaml_name ocaml_type_annot keyword_space binding_keyword init_code)
  in
  let let_bindings_code = String.concat ~sep:"\n  " let_bindings_code_list in
  (* Translate body using the inner environment *)
  let body_code = translate_progn !inner_env_ref body inferred_type in
  sprintf "(\n  %s\n  %s\n)"
    (manual_indent 2 let_bindings_code)
    (manual_indent 2 body_code)

and translate_let_star env bindings body inferred_type =
  let final_env, nested_lets_code =
    List.fold bindings ~init:(env, "")
      ~f:(fun (current_env, current_code) (elisp_name, binding_info) ->
        let typed_init = binding_info.TypedAst.initializer_ast in
        let is_mutated = binding_info.TypedAst.is_mutated in
        let init_type = TypedAst.get_type typed_init in
        let ocaml_name = generate_ocaml_var elisp_name in

        (* Evaluate initializer in the *current sequential* environment *)
         (* TODO: Add type change analysis *)
        let repr, init_code =
          match init_type with
          | InferredType.T_Int -> (R_Int, to_int current_env typed_init)
          | InferredType.T_Float -> (R_Float, to_float current_env typed_init)
          | InferredType.T_Bool | T_Nil -> (R_Bool, to_bool current_env typed_init)
          | _ -> (R_Value, to_value current_env typed_init)
        in

        (* Add binding for the *next* initializer/body *)
        let next_env = add_binding current_env elisp_name ocaml_name repr is_mutated in

        (* Generate OCaml let binding: use ref only if mutated *)
        let ocaml_type_annot, binding_keyword =
           match repr, is_mutated with
           | R_Int, true -> (": int ref", "ref")
           | R_Float, true -> (": float ref", "ref")
           | R_Bool, true -> (": bool ref", "ref")
           | R_Value, true -> (": Value.t ref", "ref")
           | R_Int, false -> (": int", "") (* Direct binding *)
           | R_Float, false -> (": float", "")
           | R_Bool, false -> (": bool", "")
           | R_Value, false -> (": Value.t", "")
        in
        let keyword_space = if String.is_empty binding_keyword then "" else " " in
        let new_let =
          sprintf "let %s %s =%s%s (%s) in" ocaml_name ocaml_type_annot keyword_space binding_keyword init_code
        in
        (next_env, sprintf "%s\n%s" current_code (manual_indent 2 new_let)))
  in
  (* Translate body using the final environment from the fold *)
  let body_code = translate_progn final_env body inferred_type in
  sprintf "(%s\n%s\n)" nested_lets_code (* Already indented *)
    (manual_indent 2 body_code)

and translate_setq env pairs inferred_type =
  let target_repr =
    match inferred_type with
    | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
    | _ -> R_Value
  in
  let assignments_code_list =
    List.map pairs ~f:(fun (sym_name, typed_value) ->
        let value_type = TypedAst.get_type typed_value in
        match lookup_var_info env sym_name with
        (* Local Variables: Check mutation flag *)
        | Some { ocaml_name; repr = R_Int; is_mutated = true } ->
            sprintf "%s := (%s);" ocaml_name (to_int env typed_value)
        | Some { ocaml_name; repr = R_Float; is_mutated = true } ->
            sprintf "%s := (%s);" ocaml_name (to_float env typed_value)
        | Some { ocaml_name; repr = R_Bool; is_mutated = true } ->
            sprintf "%s := (%s);" ocaml_name (to_bool env typed_value)
        | Some { ocaml_name; repr = R_Value; is_mutated = true } ->
            let value_code = match value_type with
              | T_Int -> to_int env typed_value |> box_int
              | T_Float -> to_float env typed_value |> box_float
              | T_Bool | T_Nil -> to_bool env typed_value |> box_bool
              | _ -> to_value env typed_value
            in
            sprintf "%s := (%s);" ocaml_name value_code
        | Some { ocaml_name=_; repr=_; is_mutated = false } ->
            (* Error: Assignment to non-mutable local variable *)
            failwithf "Translate Error: Attempt to setq non-mutable local variable '%s'" sym_name ()
        | None ->
            (* Global variable: use Runtime *)
            (* TODO: Change this for desired top-level native var generation *)
            sprintf "let (_ : Value.t) = Runtime.set_global_variable %S (%s) in ();"
              sym_name (to_value env typed_value))
  in
  let return_value_code =
    match List.last pairs with
    | None -> translate_expr env (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil }) target_repr
    | Some (_, v) -> translate_expr env v target_repr
  in
  let assignments_code = String.concat ~sep:"\n    " assignments_code_list in
  if String.is_empty assignments_code then return_value_code
  else sprintf "(let () = \n    %s\n  in\n  %s)" assignments_code return_value_code

and translate_lambda env arg_spec body fun_type =
  let open InferredType in
  (* Determine argument types and return type from the function type *)
  let inferred_arg_types_list, inferred_return_type =
    match fun_type with
    | InferredType.T_Function { arg_types = Some types; return_type } -> (types, return_type)
    | InferredType.T_Function { arg_types = None; return_type } ->
         Printf.eprintf "Warning: Lambda has varargs type, precise arg types lost.\n%!";
         let count = List.length arg_spec.required + List.length arg_spec.optional + (if Option.is_some arg_spec.rest then 1 else 0) in
         (List.init count ~f:(fun _ -> T_Any), return_type)
    | other ->
        Printf.eprintf "Warning: Lambda has non-function type %s. Using Any.\n%!" (to_string other);
        let count = List.length arg_spec.required + List.length arg_spec.optional + (if Option.is_some arg_spec.rest then 1 else 0) in
        (List.init count ~f:(fun _ -> T_Any), T_Any)
  in
  let inferred_arg_types = Array.of_list inferred_arg_types_list in

  let code = Buffer.create 256 in
  Buffer.add_string code "(Value.Function (fun runtime_args ->\n";
  Buffer.add_string code "   (* Lambda generated code *)\n";
  (* Arity Check *)
  let min_args = List.length arg_spec.required in
  let max_args_opt = if Option.is_some arg_spec.rest then None else Some (min_args + List.length arg_spec.optional) in
  Buffer.add_string code (sprintf "    let num_runtime_args = List.length runtime_args in\n");
  let arity_check_msg = sprintf "\"lambda\" \"Expected %d%s args, got %%d\"" min_args (match max_args_opt with None -> "+" | Some m when m = min_args -> "" | Some m -> sprintf "-%d" m) in
  Buffer.add_string code (sprintf "    if num_runtime_args < %d %s then Runtime.arity_error %s num_runtime_args;\n" min_args (match max_args_opt with None -> "" | Some m -> sprintf "|| num_runtime_args > %d" m) arity_check_msg);

  (* Argument Binding & Environment Setup *)
  let inner_env_ref = ref env in
  let arg_bindings_code = Buffer.create 128 in
  let arg_idx = ref 0 in

  (* TODO: Perform mutation analysis on lambda body w.r.t args *)
  let lambda_body_ast = TypedAst.Progn { forms = body; inferred_type = inferred_return_type } in
  let arg_names_set = String.Set.of_list (arg_spec.required @ List.map ~f:fst arg_spec.optional @ Option.to_list arg_spec.rest) in
  let mutated_args = Analyze.check_mutations lambda_body_ast arg_names_set in

  (* Required Args *)
  List.iter arg_spec.required ~f:(fun name ->
      let idx = !arg_idx in
      if idx >= Array.length inferred_arg_types then failwithf "Lambda arity mismatch (internal error): required arg %s index %d out of bounds %d" name idx (Array.length inferred_arg_types) ();
      let arg_type = inferred_arg_types.(idx) in
      let ocaml_name = generate_ocaml_var name in
      let runtime_arg = sprintf "(List.nth_exn runtime_args %d)" idx in
      let is_mutated = Set.mem mutated_args name in (* Use analysis result *)
      let repr, setup_code =
        match arg_type, is_mutated with
        | InferredType.T_Int, false -> (R_Int, sprintf "let %s : int = %s in" ocaml_name (unbox_int runtime_arg))
        | InferredType.T_Float, false -> (R_Float, sprintf "let %s : float = %s in" ocaml_name (unbox_float runtime_arg))
        | (InferredType.T_Bool | T_Nil), false -> (R_Bool, sprintf "let %s : bool = %s in" ocaml_name (unbox_bool runtime_arg))
        | _, false -> (R_Value, sprintf "let %s : Value.t = %s in" ocaml_name runtime_arg)
        | InferredType.T_Int, true -> (R_Int, sprintf "let %s : int ref = ref (%s) in" ocaml_name (unbox_int runtime_arg))
        | InferredType.T_Float, true -> (R_Float, sprintf "let %s : float ref = ref (%s) in" ocaml_name (unbox_float runtime_arg))
        | (InferredType.T_Bool | T_Nil), true -> (R_Bool, sprintf "let %s : bool ref = ref (%s) in" ocaml_name (unbox_bool runtime_arg))
        | _, true -> (R_Value, sprintf "let %s : Value.t ref = ref %s in" ocaml_name runtime_arg)
      in
      Buffer.add_string arg_bindings_code (sprintf "    %s\n" setup_code);
      inner_env_ref := add_binding !inner_env_ref name ocaml_name repr is_mutated;
      incr arg_idx);
  (* Optional Args *)
  List.iter arg_spec.optional ~f:(fun (name, default_val_opt) ->
      let idx = !arg_idx in
      if idx >= Array.length inferred_arg_types then failwithf "Lambda arity mismatch (internal error): optional arg %s index %d out of bounds %d" name idx (Array.length inferred_arg_types) ();
      let arg_type = inferred_arg_types.(idx) in
      let ocaml_name = generate_ocaml_var name in
      let default_value_expr = match default_val_opt with None -> "Value.Nil" | Some dv -> Translate_quote.translate_quoted_data dv in
      let runtime_arg_expr = sprintf "(List.nth_exn runtime_args %d)" idx in
      let condition = sprintf "(num_runtime_args > %d)" idx in
      let is_mutated = Set.mem mutated_args name in (* Use analysis result *)
      let repr, setup_code =
        match arg_type, is_mutated with
        | InferredType.T_Int, false -> ( R_Int, sprintf "let %s : int = (if %s then %s else %s) in" ocaml_name condition (unbox_int runtime_arg_expr) (unbox_int default_value_expr) )
        | InferredType.T_Float, false -> ( R_Float, sprintf "let %s : float = (if %s then %s else %s) in" ocaml_name condition (unbox_float runtime_arg_expr) (unbox_float default_value_expr) )
        | (InferredType.T_Bool | T_Nil), false -> ( R_Bool, sprintf "let %s : bool = (if %s then %s else %s) in" ocaml_name condition (unbox_bool runtime_arg_expr) (unbox_bool default_value_expr) )
        | _, false -> ( R_Value, sprintf "let %s : Value.t = (if %s then %s else %s) in" ocaml_name condition runtime_arg_expr default_value_expr )
        | InferredType.T_Int, true -> ( R_Int, sprintf "let %s : int ref = ref (if %s then %s else %s) in" ocaml_name condition (unbox_int runtime_arg_expr) (unbox_int default_value_expr) )
        | InferredType.T_Float, true -> ( R_Float, sprintf "let %s : float ref = ref (if %s then %s else %s) in" ocaml_name condition (unbox_float runtime_arg_expr) (unbox_float default_value_expr) )
        | (InferredType.T_Bool | T_Nil), true -> ( R_Bool, sprintf "let %s : bool ref = ref (if %s then %s else %s) in" ocaml_name condition (unbox_bool runtime_arg_expr) (unbox_bool default_value_expr) )
        | _, true -> ( R_Value, sprintf "let %s : Value.t ref = ref (if %s then %s else %s) in" ocaml_name condition runtime_arg_expr default_value_expr )
      in
      Buffer.add_string arg_bindings_code (sprintf "    %s\n" setup_code);
      inner_env_ref := add_binding !inner_env_ref name ocaml_name repr is_mutated;
      incr arg_idx);
  (* Rest Arg *)
  (match arg_spec.rest with
  | None -> ()
  | Some name ->
      let start_idx = !arg_idx in
      let ocaml_name = generate_ocaml_var name in
      let is_mutated = Set.mem mutated_args name in (* Use analysis result *)
      let repr, setup_code =
          let rest_list_code = sprintf "(Value.list_to_value (List.drop runtime_args %d))" start_idx in
          if is_mutated then
              (R_Value, sprintf "let %s : Value.t ref = ref %s in" ocaml_name rest_list_code)
          else
              (R_Value, sprintf "let %s : Value.t = %s in" ocaml_name rest_list_code)
      in
      Buffer.add_string arg_bindings_code (sprintf "    %s\n" setup_code);
      inner_env_ref := add_binding !inner_env_ref name ocaml_name repr is_mutated);

  Buffer.add_buffer code arg_bindings_code; (* Add bindings setup *)
  let body_code = translate_progn !inner_env_ref body inferred_return_type in
  Buffer.add_string code (sprintf "    %s\n))" body_code); (* Add body *)
  Buffer.contents code


and translate_cond env clauses inferred_type =
  let target_repr =
    match inferred_type with
    | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
    | _ -> R_Value
  in
  let rec build cls =
    match cls with
    | [] -> translate_expr env (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil }) target_repr
    | (typed_test, typed_body) :: rest ->
        let test_code = to_bool env typed_test in
        let result_code =
          let body_exprs = if List.is_empty typed_body then [ typed_test ] else typed_body in
          translate_progn env body_exprs inferred_type
        in
        sprintf "(if %s then begin\n%s\nend else begin\n%s\nend)" test_code
          (manual_indent 4 result_code) (build rest)
  in
  build clauses

and translate_funcall env func args inferred_type =
  (* Try optimized builtins first *)
  match func, args with
  (* Arithmetic (assuming integer result based on inferred_type) *)
  | TypedAst.Atom { value = Value.Symbol { name = "+"; _ }; _ }, [ a; b ] when [%compare.equal: InferredType.t] inferred_type InferredType.T_Int -> sprintf "(%s + %s)" (to_int env a) (to_int env b)
  | TypedAst.Atom { value = Value.Symbol { name = "-"; _ }; _ }, [ a; b ] when [%compare.equal: InferredType.t] inferred_type InferredType.T_Int -> sprintf "(%s - %s)" (to_int env a) (to_int env b)
  | TypedAst.Atom { value = Value.Symbol { name = "*"; _ }; _ }, [ a; b ] when [%compare.equal: InferredType.t] inferred_type InferredType.T_Int -> sprintf "(%s * %s)" (to_int env a) (to_int env b)
  | TypedAst.Atom { value = Value.Symbol { name = "/"; _ }; _ }, [ a; b ] when [%compare.equal: InferredType.t] inferred_type InferredType.T_Int -> sprintf "(%s / %s)" (to_int env a) (to_int env b)
  (* Predicates (result is bool) *)
   | TypedAst.Atom { value = Value.Symbol { name = "integerp"; _ }; _ }, [ a ] when [%compare.equal: InferredType.t] inferred_type InferredType.T_Bool -> sprintf "(match %s with Value.Int _ -> true | _ -> false)" (to_value env a)
   | TypedAst.Atom { value = Value.Symbol { name = "consp"; _ }; _ }, [ a ] when [%compare.equal: InferredType.t] inferred_type InferredType.T_Bool -> sprintf "(match %s with Value.Cons _ -> true | _ -> false)" (to_value env a)
  (* Equality (result is bool, needs Value.t comparison) *)
  | TypedAst.Atom { value = Value.Symbol { name = "eq"; _ }; _ }, [ a; b ] when [%compare.equal: InferredType.t] inferred_type InferredType.T_Bool -> sprintf "(Runtime.is_truthy (Runtime.builtin_eq [%s; %s]))" (to_value env a) (to_value env b)
  | TypedAst.Atom { value = Value.Symbol { name = "equal"; _ }; _ }, [ a; b ] when [%compare.equal: InferredType.t] inferred_type InferredType.T_Bool -> sprintf "(Runtime.is_truthy (Runtime.builtin_equal [%s; %s]))" (to_value env a) (to_value env b)
  (* List operations *)
  | TypedAst.Atom { value = Value.Symbol { name = "car"; _ }; _ }, [ a ] ->
      let target_repr = match inferred_type with | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value in
      let arg_code = to_value env a in
      let car_logic_code = sprintf "(match %s with | Value.Cons { car = c; _ } -> c | Value.Nil -> Value.Nil | other -> Runtime.type_error \"car\" \"cons cell or nil\" other)" arg_code in
      (match target_repr with | R_Int -> unbox_int car_logic_code | R_Float -> unbox_float car_logic_code | R_Bool -> unbox_bool car_logic_code | R_Value -> car_logic_code)
   | TypedAst.Atom { value = Value.Symbol { name = "cdr"; _ }; _ }, [ a ] ->
      let target_repr = match inferred_type with | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value in
      let arg_code = to_value env a in
      let cdr_logic_code = sprintf "(match %s with | Value.Cons { cdr = d; _ } -> d | Value.Nil -> Value.Nil | other -> Runtime.type_error \"cdr\" \"cons cell or nil\" other)" arg_code in
      (match target_repr with | R_Int -> unbox_int cdr_logic_code | R_Float -> unbox_float cdr_logic_code | R_Bool -> unbox_bool cdr_logic_code | R_Value -> cdr_logic_code)
   | TypedAst.Atom { value = Value.Symbol { name = "cons"; _ }; _ }, [ a; b ] -> sprintf "(Value.Cons { car = %s; cdr = %s })" (to_value env a) (to_value env b)
  | _ -> translate_generic_funcall env func args inferred_type

and translate_generic_funcall env func args inferred_type =
  let func_code = to_value env func in
  let arg_codes_value = List.map args ~f:(to_value env) in
  let call_code = sprintf "(Runtime.apply_function (%s) [%s])" func_code (String.concat ~sep:"; " arg_codes_value) in
  let target_repr = match inferred_type with | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value in
  match target_repr with | R_Int -> unbox_int call_code | R_Float -> unbox_float call_code | R_Bool -> unbox_bool call_code | R_Value -> call_code

(* --- Top Level Translation --- *)
let translate_toplevel texprs final_env_types =
  let definitions = ref [] in
  let run_expressions = ref [] in
  List.iter texprs ~f:(fun texpr -> match texpr with TypedAst.Defun _ -> definitions := !definitions @ [ texpr ] | _ -> run_expressions := !run_expressions @ [ texpr ]);

  (* Create the initial top-level environment map *)
  let top_env_map =
    String.Map.of_alist_exn
      (List.map final_env_types ~f:(fun (name, ty) ->
           let ocaml_name = generate_ocaml_var name in
           let repr = match ty with | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value in
           let is_mutated = true in (* Defun implies mutable binding *)
           (name, { ocaml_name; repr; is_mutated })))
  in
  let top_env = top_env_map in

  (* Translate definitions (defun) *)
  let def_codes =
    List.filter_map !definitions ~f:(fun def_texpr ->
        match def_texpr with
        | TypedAst.Defun { name; args; body; fun_type; _ } ->
            let entry = Map.find_exn top_env_map name in
            let ocaml_func_name = entry.ocaml_name in
            let lambda_code = translate_lambda top_env args body fun_type in
            (* Defun always creates a Value.t ref *)
            Some (sprintf "let %s : Value.t ref = ref (%s)" ocaml_func_name lambda_code)
        | _ -> None)
  in
  let definitions_code = match def_codes with | [] -> "" | hd :: tl -> "let rec " ^ hd ^ (List.map tl ~f:(sprintf "\nand %s") |> String.concat) in

  (* Translate the top-level expressions *)
  (* TODO: Major change needed here to generate local OCaml vars for top-level setq *)
  (* and build the environment list progressively. Using old logic for now. *)
  let run_body_code = translate_progn top_env !run_expressions InferredType.T_Any in

  (* Generate code to extract the environment *)
  (* Currently only includes defun'd variables *)
  let env_export_entries =
    Map.to_alist top_env_map
    |> List.filter_map ~f:(fun (elisp_name, entry) ->
           (* Defun is always Value.t ref *)
           let value_code = sprintf "!%s" entry.ocaml_name in
           Some (sprintf "(%S, %s)" elisp_name value_code))
  in
  let env_export_code = sprintf "[%s]" (String.concat ~sep:"; " env_export_entries) in

  (* Assemble the final OCaml module string *)
  sprintf
    "(* Generated by Scaml *)\n\n\
     open! Core\n\
     module Value = Scaml.Value \n\
     module Runtime = Scaml.Runtime \n\
     module Compiler = Scaml.Compiler\n\n\
     (* Definitions *)\n\
     %s\n\n\
     (* Function to execute top-level forms and return the defined environment *)\n\
     let execute_and_get_env () : (string * Value.t) list = \n\
    \  (* Execute top-level expressions for side-effects *)\n\
    \  let (_ : Value.t) = \n\
    \    %s\n\
    \  in\n\
    \  (* Construct and return the environment alist *)\n\
    \  (* TODO: Include top-level setq vars here *) \n\
    \  %s\n\n\
     (* Register the combined function with the Compiler module via Callback system *)\n\
     let () = try \n\
    \    let (register_module : (unit -> (string * Value.t) list) -> unit) = \n\
    \      Callback.lookup \"scaml_register_compiled_module\" in \n\
    \    register_module execute_and_get_env \n\
    \  with Not_found -> \n\
    \    Printf.eprintf \"Warning: scaml_register_compiled_module callback not found.\\n%%!;\""
    definitions_code
    (manual_indent 4 run_body_code)
    (manual_indent 2 env_export_code)

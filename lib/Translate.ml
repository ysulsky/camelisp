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

(* Modified: env_entry now includes is_mutated and needs_boxing *)
type env_entry = {
  ocaml_name : string;
  repr : var_repr; (* Base representation if not boxed *)
  is_mutated : bool; (* From mutation analysis *)
  needs_boxing : bool; (* From type change analysis *)
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

(* Modified: add_binding now includes is_mutated and needs_boxing *)
let add_binding env elisp_name ocaml_name repr is_mutated needs_boxing =
  Map.set env ~key:elisp_name ~data:{ ocaml_name; repr; is_mutated; needs_boxing }

(* Modified: add_bindings expects entries with new fields *)
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
(* Modified: Pass needs_boxing_set down *)
let rec to_value env needs_boxing_set expr = translate_expr env needs_boxing_set expr R_Value

and to_int env needs_boxing_set expr = translate_expr env needs_boxing_set expr R_Int

and to_float env needs_boxing_set expr = translate_expr env needs_boxing_set expr R_Float

and to_bool env needs_boxing_set expr = translate_expr env needs_boxing_set expr R_Bool

and translate_expr env needs_boxing_set texpr target_repr =
  (* Pass needs_boxing_set to translate_node *)
  let generated_code, source_repr = translate_node env needs_boxing_set texpr in

  (* Boxing/Unboxing logic based on source/target representations *)
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

(* Modified: Accepts needs_boxing_set, returns generated code and actual source representation *)
and translate_node env needs_boxing_set texpr : string * var_repr =
  match texpr with
  | TypedAst.Atom { value; inferred_type } -> begin
      match inferred_type with
      (* Literals of basic types *)
      | InferredType.T_Int -> ( (match value with Value.Int i -> Int.to_string i | _ -> failwith "Type mismatch"), R_Int )
      | InferredType.T_Float -> ( (match value with Value.Float f -> Float.to_string f | _ -> failwith "Type mismatch"), R_Float )
      | InferredType.T_Nil -> ( "false", R_Bool )
      | InferredType.T_Bool -> ( (match value with Value.T -> "true" | _ -> "false"), R_Bool )
      | InferredType.T_Keyword -> ( (match value with Value.Keyword k -> sprintf "(Value.Keyword %S)" k | _ -> failwith "Type mismatch"), R_Value )
      | InferredType.T_String -> ( (match value with Value.String s -> sprintf "(Value.String %S)" s | _ -> failwith "Type mismatch"), R_Value )
      | InferredType.T_Char -> ( (match value with Value.Char c -> sprintf "(Value.Char %C)" c | _ -> failwith "Type mismatch"), R_Value )

      (* Symbol: Look up in environment *)
      | InferredType.T_Symbol -> (
          match value with
          | Value.Symbol { name } -> (
              match lookup_var_info env name with
              (* Local variables: access depends on mutation and boxing status *)
              | Some { ocaml_name; repr; is_mutated; needs_boxing } ->
                  let use_ref = is_mutated || needs_boxing in
                  let access_code = if use_ref then sprintf "!%s" ocaml_name else ocaml_name in
                  let actual_repr = if needs_boxing then R_Value else repr in
                  (access_code, actual_repr)
              (* Globals: lookup via runtime, always R_Value *)
              | None -> (sprintf "(Runtime.lookup_variable %S)" name, R_Value)
              )
          | _ -> failwith "Type mismatch: T_Symbol but not Value.Symbol"
         )

      (* Other types are represented as Value.t *)
      | InferredType.T_Var _ | T_Cons _ | T_Vector _ | T_Function _ | T_Union _ | T_Any | T_Unknown -> (
          match value with
          | Value.Symbol { name } -> (
              (* Symbol representing a complex value - check local/global *)
              match lookup_var_info env name with
              (* Assume complex types are always Value.t, check mutation/boxing *)
              | Some { ocaml_name; is_mutated; needs_boxing; _ } ->
                  let use_ref = is_mutated || needs_boxing in
                  let access_code = if use_ref then sprintf "!%s" ocaml_name else ocaml_name in
                  (access_code, R_Value) (* Always R_Value *)
              | None -> (sprintf "(Runtime.lookup_variable %S)" name, R_Value)
             )
          (* Atom itself is the complex value (e.g., literal vector) *)
          | _ -> (Translate_quote.translate_quoted_data value, R_Value)
          )
    end
  | TypedAst.Quote { value; inferred_type = _ } ->
      (Translate_quote.translate_quoted_data value, R_Value) (* Quote always results in R_Value *)

  | TypedAst.If { cond; then_branch; else_branch; inferred_type } ->
      let cond_code = to_bool env needs_boxing_set cond in
      (* Determine the target representation based on the overall inferred type *)
      let target_repr =
        match inferred_type with
        | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
        | _ -> R_Value
      in
      let then_code = translate_expr env needs_boxing_set then_branch target_repr in
      let else_code =
        match else_branch with
        | None -> translate_expr env needs_boxing_set (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil }) target_repr
        | Some eb -> translate_expr env needs_boxing_set eb target_repr
      in
      (sprintf "(if %s then\n   %s\n else\n   %s)" cond_code (manual_indent 3 then_code) (manual_indent 3 else_code), target_repr)

  | TypedAst.Progn { forms; inferred_type } ->
      let code, repr = translate_progn env needs_boxing_set forms inferred_type in
      (code, repr)

  | TypedAst.Let { bindings; body; inferred_type } ->
       let code, repr = translate_let env needs_boxing_set bindings body inferred_type in
       (code, repr)

  | TypedAst.LetStar { bindings; body; inferred_type } ->
       let code, repr = translate_let_star env needs_boxing_set bindings body inferred_type in
       (code, repr)

  | TypedAst.Setq { pairs; inferred_type } ->
       let code, repr = translate_setq env needs_boxing_set pairs inferred_type in
       (code, repr)

  | TypedAst.Lambda { args; body; inferred_type } ->
       let code = translate_lambda env needs_boxing_set args body inferred_type in
       (code, R_Value) (* Lambda always results in Value.t *)

  | TypedAst.Defun { name; _ } ->
      (sprintf "(Value.Symbol { name = %S })" name, R_Value) (* Defun expression returns symbol *)

  | TypedAst.Cond { clauses; inferred_type } ->
       let code, repr = translate_cond env needs_boxing_set clauses inferred_type in
       (code, repr)

  | TypedAst.Funcall { func; args; inferred_type } ->
       let code, repr = translate_funcall env needs_boxing_set func args inferred_type in
       (code, repr)

(* Modified: Pass needs_boxing_set down, return resulting repr *)
and translate_progn env needs_boxing_set forms inferred_type : string * var_repr =
  match forms with
  | [] ->
      let target_repr = match inferred_type with | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value in
      let code = translate_expr env needs_boxing_set (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil }) target_repr in
      (code, target_repr)
  | [ last ] -> translate_node env needs_boxing_set last
  | _ ->
      let target_repr =
        match inferred_type with
        | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
        | _ -> R_Value
      in
      (* Translate all but the last form to Value.t for side effects *)
      let translated_forms_side_effects = List.map (List.drop_last_exn forms) ~f:(fun expr -> to_value env needs_boxing_set expr) in
      let last_form = List.last_exn forms in
      let translated_last = translate_expr env needs_boxing_set last_form target_repr in
      let sequence_code = List.map translated_forms_side_effects ~f:(sprintf "let (_ : Value.t) = %s in") |> String.concat ~sep:"\n  " in
      let final_code = if String.is_empty sequence_code then translated_last else sprintf "(%s\n  %s)" sequence_code translated_last in
      (final_code, target_repr)

(* Modified: Pass needs_boxing_set down, use it for bindings, return resulting repr *)
and translate_let env needs_boxing_set bindings body inferred_type : string * var_repr =
  let inner_env_ref = ref env in
  let let_bindings_code_list =
    List.map bindings ~f:(fun (elisp_name, binding_info) ->
        let typed_init = binding_info.TypedAst.initializer_ast in
        let is_mutated = binding_info.TypedAst.is_mutated in
        let init_type = TypedAst.get_type typed_init in
        let ocaml_name = generate_ocaml_var elisp_name in

        (* Determine if boxing is needed for this specific variable *)
        let needs_boxing = Set.mem needs_boxing_set elisp_name in

        (* Determine base representation *)
        let base_repr =
          match init_type with
          | InferredType.T_Int -> R_Int | InferredType.T_Float -> R_Float
          | InferredType.T_Bool | T_Nil -> R_Bool | _ -> R_Value
        in

        (* Final representation and OCaml type/keyword *)
        let final_repr = if needs_boxing then R_Value else base_repr in
        let use_ref = is_mutated || needs_boxing in
        let ocaml_type_annot, binding_keyword =
           match final_repr, use_ref with
           | R_Int, true   -> (": int ref", "ref")
           | R_Float, true -> (": float ref", "ref")
           | R_Bool, true  -> (": bool ref", "ref")
           | R_Value, true -> (": Value.t ref", "ref") (* Boxed ref *)
           | R_Int, false  -> (": int", "")
           | R_Float, false-> (": float", "")
           | R_Bool, false -> (": bool", "")
           | R_Value, false-> (": Value.t", "")      (* Boxed direct *)
        in

        (* Translate initializer code based on the representation needed *)
        let init_code =
            match final_repr with
            | R_Int -> to_int env needs_boxing_set typed_init
            | R_Float -> to_float env needs_boxing_set typed_init
            | R_Bool -> to_bool env needs_boxing_set typed_init
            | R_Value -> to_value env needs_boxing_set typed_init
        in

        (* Add binding to the environment for the body *)
        inner_env_ref := add_binding !inner_env_ref elisp_name ocaml_name base_repr is_mutated needs_boxing;

        let keyword_space = if String.is_empty binding_keyword then "" else " " in
        sprintf "let %s %s =%s%s (%s) in" ocaml_name ocaml_type_annot keyword_space binding_keyword init_code)
  in
  let let_bindings_code = String.concat ~sep:"\n  " let_bindings_code_list in
  (* Translate body using the inner environment *)
  let body_code, body_repr = translate_progn !inner_env_ref needs_boxing_set body inferred_type in
  (sprintf "(\n  %s\n  %s\n)" (manual_indent 2 let_bindings_code) (manual_indent 2 body_code), body_repr)

(* Modified: Pass needs_boxing_set down, use it for bindings, return resulting repr *)
and translate_let_star env needs_boxing_set bindings body inferred_type : string * var_repr =
  let final_env, nested_lets_code =
    List.fold bindings ~init:(env, "")
      ~f:(fun (current_env, current_code) (elisp_name, binding_info) ->
        let typed_init = binding_info.TypedAst.initializer_ast in
        let is_mutated = binding_info.TypedAst.is_mutated in
        let init_type = TypedAst.get_type typed_init in
        let ocaml_name = generate_ocaml_var elisp_name in

        let needs_boxing = Set.mem needs_boxing_set elisp_name in
        let base_repr = match init_type with | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value in
        let final_repr = if needs_boxing then R_Value else base_repr in
        let use_ref = is_mutated || needs_boxing in

        (* Translate initializer in the *current sequential* environment *)
        let init_code =
            match final_repr with
            | R_Int -> to_int current_env needs_boxing_set typed_init
            | R_Float -> to_float current_env needs_boxing_set typed_init
            | R_Bool -> to_bool current_env needs_boxing_set typed_init
            | R_Value -> to_value current_env needs_boxing_set typed_init
        in

        (* Add binding for the *next* initializer/body *)
        let next_env = add_binding current_env elisp_name ocaml_name base_repr is_mutated needs_boxing in

        (* Generate OCaml let binding *)
        let ocaml_type_annot, binding_keyword =
           match final_repr, use_ref with
           | R_Int, true   -> (": int ref", "ref") | R_Float, true -> (": float ref", "ref")
           | R_Bool, true  -> (": bool ref", "ref") | R_Value, true -> (": Value.t ref", "ref")
           | R_Int, false  -> (": int", "") | R_Float, false-> (": float", "")
           | R_Bool, false -> (": bool", "") | R_Value, false-> (": Value.t", "")
        in
        let keyword_space = if String.is_empty binding_keyword then "" else " " in
        let new_let = sprintf "let %s %s =%s%s (%s) in" ocaml_name ocaml_type_annot keyword_space binding_keyword init_code in
        (next_env, sprintf "%s\n%s" current_code (manual_indent 2 new_let)))
  in
  (* Translate body using the final environment from the fold *)
  let body_code, body_repr = translate_progn final_env needs_boxing_set body inferred_type in
  (sprintf "(%s\n%s\n)" nested_lets_code (manual_indent 2 body_code), body_repr)

(* Modified: Pass needs_boxing_set down, use it for checks, return resulting repr *)
and translate_setq env needs_boxing_set pairs inferred_type : string * var_repr =
  let target_repr = match inferred_type with | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value in
  let assignments_code_list =
    List.map pairs ~f:(fun (sym_name, typed_value) ->
        (* Introduce explicit binding for lookup result *)
        match lookup_var_info env sym_name with
        | Some { ocaml_name; repr; is_mutated; needs_boxing } ->
            if not is_mutated then
              (* Error: Assignment to non-mutable local variable *)
              failwithf "Translate Error: Attempt to setq non-mutable local variable '%s'" sym_name ()
            else if needs_boxing then
              (* Assigning to Value.t ref *)
              let value_code = to_value env needs_boxing_set typed_value in
              sprintf "%s := %s;" ocaml_name value_code
            else
              (* Assigning to native ref *)
              (match repr with
              | R_Int -> sprintf "%s := %s;" ocaml_name (to_int env needs_boxing_set typed_value)
              | R_Float -> sprintf "%s := %s;" ocaml_name (to_float env needs_boxing_set typed_value)
              | R_Bool -> sprintf "%s := %s;" ocaml_name (to_bool env needs_boxing_set typed_value)
              | R_Value -> (* This case means needs_boxing=false but repr=R_Value *)
                           (* This might occur for complex types that aren't boxed due to type changes *)
                           (* Treat as Value.t ref assignment *)
                  let value_code = to_value env needs_boxing_set typed_value in
                  sprintf "%s := %s;" ocaml_name value_code)
        | None ->
            (* Global variable: use Runtime *)
            sprintf "let (_ : Value.t) = Runtime.set_global_variable %S (%s) in ();"
              sym_name (to_value env needs_boxing_set typed_value))
  in
  let return_value_code =
    match List.last pairs with
    | None -> translate_expr env needs_boxing_set (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil }) target_repr
    | Some (_, v) -> translate_expr env needs_boxing_set v target_repr
  in
  let assignments_code = String.concat ~sep:"\n    " assignments_code_list in
  let final_code = if String.is_empty assignments_code then return_value_code else sprintf "(let () = \n    %s\n  in\n  %s)" assignments_code return_value_code in
  (final_code, target_repr)

(* Modified: Pass needs_boxing_set down, use it for lambda arg bindings *)
and translate_lambda env needs_boxing_set arg_spec body fun_type =
  let open InferredType in
  let inferred_arg_types_list, inferred_return_type =
    match fun_type with
    | T_Function { arg_types = Some types; return_type } -> (types, return_type)
    | T_Function { arg_types = None; return_type } ->
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

  (* Perform mutation analysis on lambda body w.r.t args *)
  let lambda_body_ast = TypedAst.Progn { forms = body; inferred_type = inferred_return_type } in
  let arg_names = arg_spec.required @ (List.map ~f:fst arg_spec.optional) @ (Option.to_list arg_spec.rest) in
  let arg_names_set = String.Set.of_list arg_names in
  let mutated_args = Analyze.check_mutations lambda_body_ast arg_names_set in
  (* Determine which args need boxing (check top-level set passed down) *)
  let args_needing_boxing = Set.inter needs_boxing_set arg_names_set in

  (* Required Args *)
  List.iter arg_spec.required ~f:(fun name ->
      let idx = !arg_idx in
      if idx >= Array.length inferred_arg_types then failwithf "Lambda arity mismatch (internal error): required arg %s index %d out of bounds %d" name idx (Array.length inferred_arg_types) ();
      let arg_type = inferred_arg_types.(idx) in
      let ocaml_name = generate_ocaml_var name in
      let runtime_arg = sprintf "(List.nth_exn runtime_args %d)" idx in
      let is_mutated = Set.mem mutated_args name in
      let needs_boxing = Set.mem args_needing_boxing name in
      let base_repr = match arg_type with | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value in
      let final_repr = if needs_boxing then R_Value else base_repr in
      let use_ref = is_mutated || needs_boxing in
      let setup_code =
        match final_repr, use_ref with
        | R_Int, false -> sprintf "let %s : int = %s in" ocaml_name (unbox_int runtime_arg)
        | R_Float, false -> sprintf "let %s : float = %s in" ocaml_name (unbox_float runtime_arg)
        | R_Bool, false -> sprintf "let %s : bool = %s in" ocaml_name (unbox_bool runtime_arg)
        | R_Value, false -> sprintf "let %s : Value.t = %s in" ocaml_name runtime_arg
        | R_Int, true -> sprintf "let %s : int ref = ref (%s) in" ocaml_name (unbox_int runtime_arg)
        | R_Float, true -> sprintf "let %s : float ref = ref (%s) in" ocaml_name (unbox_float runtime_arg)
        | R_Bool, true -> sprintf "let %s : bool ref = ref (%s) in" ocaml_name (unbox_bool runtime_arg)
        | R_Value, true -> sprintf "let %s : Value.t ref = ref %s in" ocaml_name runtime_arg
      in
      Buffer.add_string arg_bindings_code (sprintf "    %s\n" setup_code);
      inner_env_ref := add_binding !inner_env_ref name ocaml_name base_repr is_mutated needs_boxing;
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
      let is_mutated = Set.mem mutated_args name in
      let needs_boxing = Set.mem args_needing_boxing name in
      let base_repr = match arg_type with | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value in
      let final_repr = if needs_boxing then R_Value else base_repr in
      let use_ref = is_mutated || needs_boxing in
      let setup_code =
        match final_repr, use_ref with
         | R_Int, false -> sprintf "let %s : int = (if %s then %s else %s) in" ocaml_name condition (unbox_int runtime_arg_expr) (unbox_int default_value_expr)
         | R_Float, false -> sprintf "let %s : float = (if %s then %s else %s) in" ocaml_name condition (unbox_float runtime_arg_expr) (unbox_float default_value_expr)
         | R_Bool, false -> sprintf "let %s : bool = (if %s then %s else %s) in" ocaml_name condition (unbox_bool runtime_arg_expr) (unbox_bool default_value_expr)
         | R_Value, false -> sprintf "let %s : Value.t = (if %s then %s else %s) in" ocaml_name condition runtime_arg_expr default_value_expr
         | R_Int, true -> sprintf "let %s : int ref = ref (if %s then %s else %s) in" ocaml_name condition (unbox_int runtime_arg_expr) (unbox_int default_value_expr)
         | R_Float, true -> sprintf "let %s : float ref = ref (if %s then %s else %s) in" ocaml_name condition (unbox_float runtime_arg_expr) (unbox_float default_value_expr)
         | R_Bool, true -> sprintf "let %s : bool ref = ref (if %s then %s else %s) in" ocaml_name condition (unbox_bool runtime_arg_expr) (unbox_bool default_value_expr)
         | R_Value, true -> sprintf "let %s : Value.t ref = ref (if %s then %s else %s) in" ocaml_name condition runtime_arg_expr default_value_expr
      in
      Buffer.add_string arg_bindings_code (sprintf "    %s\n" setup_code);
      inner_env_ref := add_binding !inner_env_ref name ocaml_name base_repr is_mutated needs_boxing;
      incr arg_idx);
  (* Rest Arg *)
  (match arg_spec.rest with
  | None -> ()
  | Some name ->
      let start_idx = !arg_idx in
      let ocaml_name = generate_ocaml_var name in
      let is_mutated = Set.mem mutated_args name in
      let needs_boxing = Set.mem args_needing_boxing name in (* Rest arg is always Value.t *)
      let _repr, setup_code =
          let rest_list_code = sprintf "(Value.list_to_value (List.drop runtime_args %d))" start_idx in
          if is_mutated || needs_boxing then (* Boxed ref *)
              (R_Value, sprintf "let %s : Value.t ref = ref %s in" ocaml_name rest_list_code)
          else (* Boxed direct *)
              (R_Value, sprintf "let %s : Value.t = %s in" ocaml_name rest_list_code)
      in
      Buffer.add_string arg_bindings_code (sprintf "    %s\n" setup_code);
      inner_env_ref := add_binding !inner_env_ref name ocaml_name R_Value is_mutated needs_boxing); (* Base repr is R_Value *)

  Buffer.add_buffer code arg_bindings_code; (* Add bindings setup *)
  let body_code, _ = translate_progn !inner_env_ref needs_boxing_set body inferred_return_type in
  Buffer.add_string code (sprintf "    %s\n))" body_code); (* Add body *)
  Buffer.contents code


and translate_cond env needs_boxing_set clauses inferred_type : string * var_repr =
  let target_repr = match inferred_type with | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value in
  let rec build cls =
    match cls with
    | [] -> translate_expr env needs_boxing_set (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil }) target_repr
    | (typed_test, typed_body) :: rest ->
        let test_code = to_bool env needs_boxing_set typed_test in
        let result_code, _ = (* Ignore repr from body, use overall target_repr *)
          let body_exprs = if List.is_empty typed_body then [ typed_test ] else typed_body in
          translate_progn env needs_boxing_set body_exprs inferred_type
        in
        sprintf "(if %s then begin\n%s\nend else begin\n%s\nend)" test_code
          (manual_indent 4 result_code) (build rest)
  in
  (build clauses, target_repr)

and translate_funcall env needs_boxing_set func args inferred_type : string * var_repr =
  (* Determine target repr first *)
  let target_repr = match inferred_type with | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value in
  (* Translate function and args *)
  let func_code = to_value env needs_boxing_set func in
  let arg_codes_value = List.map args ~f:(to_value env needs_boxing_set) in
  (* Generate the Runtime call (always returns Value.t) *)
  let call_code = sprintf "(Runtime.apply_function (%s) [%s])" func_code (String.concat ~sep:"; " arg_codes_value) in
  (* Convert result to target representation *)
  let final_code =
      match target_repr with
      | R_Int -> unbox_int call_code
      | R_Float -> unbox_float call_code
      | R_Bool -> unbox_bool call_code
      | R_Value -> call_code
  in
  (final_code, target_repr)

(* --- Top Level Translation --- *)
(* Modified: Accept needs_boxing_set *)
let translate_toplevel texprs final_env_types needs_boxing_set =
  let definitions = ref [] in
  let run_expressions = ref [] in
  List.iter texprs ~f:(fun texpr -> match texpr with TypedAst.Defun _ -> definitions := !definitions @ [ texpr ] | _ -> run_expressions := !run_expressions @ [ texpr ]);

  (* Create the initial top-level environment map, including boxing info *)
  let top_env_map =
    String.Map.of_alist_exn
      (List.map final_env_types ~f:(fun (name, ty) ->
           let ocaml_name = generate_ocaml_var name in
           let repr = match ty with | InferredType.T_Int -> R_Int | InferredType.T_Float -> R_Float | InferredType.T_Bool | InferredType.T_Nil -> R_Bool | _ -> R_Value in
           let is_mutated = true in (* Defun implies mutable binding *)
           let needs_boxing = Set.mem needs_boxing_set name in (* Check if boxing needed *)
           (name, { ocaml_name; repr; is_mutated; needs_boxing })))
  in
  let top_env = top_env_map in

  (* Translate definitions (defun) *)
  let def_codes =
    List.filter_map !definitions ~f:(fun def_texpr ->
        match def_texpr with
        | TypedAst.Defun { name; args; body; fun_type; _ } ->
            let entry = Map.find_exn top_env_map name in
            let ocaml_func_name = entry.ocaml_name in
            (* Pass needs_boxing_set down to lambda translation *)
            let lambda_code = translate_lambda top_env needs_boxing_set args body fun_type in
            (* Defun always creates a Value.t ref *)
            Some (sprintf "let %s : Value.t ref = ref (%s)" ocaml_func_name lambda_code)
        | _ -> None)
  in
  let definitions_code = match def_codes with | [] -> "" | hd :: tl -> "let rec " ^ hd ^ (List.map tl ~f:(sprintf "\nand %s") |> String.concat) in

  (* Translate the top-level expressions *)
  (* TODO: Major change needed here to generate local OCaml vars for top-level setq *)
  let run_body_code, _ = translate_progn top_env needs_boxing_set !run_expressions InferredType.T_Any in

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

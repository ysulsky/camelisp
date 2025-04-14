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
type var_repr = R_Value | R_Int | R_Float | R_Bool [@@deriving sexp_of, equal]

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

(* --- Boxing/Unboxing Helpers --- *)
let box_int int_code = sprintf "(Value.Int (%s))" int_code
let box_float float_code = sprintf "(Value.Float (%s))" float_code
let box_bool bool_code = sprintf "(if %s then Value.T else Value.Nil)" bool_code

(* Helper to box based on representation *)
let box_value code repr =
    match repr with
    | R_Int -> box_int code
    | R_Float -> box_float code
    | R_Bool -> box_bool code
    | R_Value -> code (* Already Value.t *)

let unbox_int value_code =
  sprintf
    "(match %s with \
     Value.Int i -> i | \
     v -> Runtime.type_error \"(unbox)\" \"integer\" v)"
    value_code

let unbox_float value_code =
  sprintf
    "(match %s with \
     Value.Float f -> f | \
     v -> Runtime.type_error \"(unbox)\" \"float\" v)"
    value_code

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
      (* Qualify all T_* constructors *)
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
                  (* The representation of the *value obtained* depends on boxing *)
                  let actual_repr = if needs_boxing then R_Value else repr in
                  (access_code, actual_repr)
              (* Globals / Built-ins: Look up via Runtime *)
              (* Corrected: Fallback to runtime lookup instead of erroring *)
              | None -> (sprintf "(Runtime.lookup_variable %S)" name, R_Value)
              )
          | _ -> failwith "Type mismatch: T_Symbol but not Value.Symbol"
         )

      (* Other types are represented as Value.t *)
      | InferredType.T_Var _ | InferredType.T_Cons _ | InferredType.T_Vector _ | InferredType.T_Function _ | InferredType.T_Union _ | InferredType.T_Any | InferredType.T_Unknown -> (
          match value with
          | Value.Symbol { name } -> (
              (* Symbol representing a complex value - check local/global *)
              match lookup_var_info env name with
              (* Assume complex types are always Value.t, check mutation/boxing *)
              | Some { ocaml_name; is_mutated; needs_boxing; _ } ->
                  let use_ref = is_mutated || needs_boxing in
                  let access_code = if use_ref then sprintf "!%s" ocaml_name else ocaml_name in
                  (access_code, R_Value) (* Always R_Value *)
               (* Corrected: Fallback to runtime lookup instead of erroring *)
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
      (* Qualify all T_* constructors *)
      let target_repr =
        match inferred_type with
        | InferredType.T_Int -> R_Int | InferredType.T_Float -> R_Float | InferredType.T_Bool | InferredType.T_Nil -> R_Bool
        | _ -> R_Value
      in
      let then_code = translate_expr env needs_boxing_set then_branch target_repr in
      let else_code =
        match else_branch with
        | None -> translate_expr env needs_boxing_set (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil }) target_repr
        | Some eb -> translate_expr env needs_boxing_set eb target_repr
      in
      (sprintf "(if %s then\n   %s\n else\n   %s)" cond_code (manual_indent 3 then_code) (manual_indent 3 else_code), target_repr)

  (* Progn translation is handled contextually (e.g., in let, lambda, toplevel) *)
  | TypedAst.Progn _ -> failwith "Progn should be handled by parent translator"

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

(* Translates a sequence of forms, returning the code for the last one and its repr *)
and translate_progn_sequence env needs_boxing_set forms inferred_type : string * var_repr =
   match forms with
   | [] ->
       (* Qualify all T_* constructors *)
       let target_repr = match inferred_type with | InferredType.T_Int -> R_Int | InferredType.T_Float -> R_Float | InferredType.T_Bool | InferredType.T_Nil -> R_Bool | _ -> R_Value in
       let code = translate_expr env needs_boxing_set (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil }) target_repr in
       (code, target_repr)
   | [ last ] -> translate_node env needs_boxing_set last
   | _ ->
       (* Translate all but the last form for side effects only (target R_Value) *)
       let side_effect_forms = List.drop_last_exn forms in
       let side_effect_codes = List.map side_effect_forms ~f:(fun expr ->
           let code, _ = translate_node env needs_boxing_set expr in
           sprintf "let (_ : _) = %s in ()" code (* Evaluate and discard *)
         )
       in
       (* Translate the last form *)
       let last_form = List.last_exn forms in
       let last_code, last_repr = translate_node env needs_boxing_set last_form in
       (* Combine *)
       let final_code = String.concat ~sep:"\n  " (side_effect_codes @ [last_code]) in
       (final_code, last_repr) (* Return code and repr of the *last* expression *)


(* Modified: Pass needs_boxing_set down, use it for bindings, return resulting repr *)
and translate_let env needs_boxing_set bindings body inferred_type : string * var_repr =
  let inner_env_ref = ref env in
  let let_bindings_code_list =
    List.map bindings ~f:(fun (elisp_name, binding_info) ->
        let typed_init = binding_info.TypedAst.initializer_ast in
        let is_mutated = binding_info.TypedAst.is_mutated in
        let init_type = TypedAst.get_type typed_init in
        let ocaml_name = generate_ocaml_var elisp_name in
        let needs_boxing = Set.mem needs_boxing_set elisp_name in
        (* Qualify all T_* constructors *)
        let base_repr = match init_type with | InferredType.T_Int -> R_Int | InferredType.T_Float -> R_Float | InferredType.T_Bool | InferredType.T_Nil -> R_Bool | _ -> R_Value in
        let final_repr = if needs_boxing then R_Value else base_repr in
        let use_ref = is_mutated || needs_boxing in

        let init_code = match final_repr with
            | R_Int -> to_int env needs_boxing_set typed_init
            | R_Float -> to_float env needs_boxing_set typed_init
            | R_Bool -> to_bool env needs_boxing_set typed_init
            | R_Value -> to_value env needs_boxing_set typed_init
        in

        inner_env_ref := add_binding !inner_env_ref elisp_name ocaml_name base_repr is_mutated needs_boxing;

        let ocaml_type_annot, binding_keyword =
           match final_repr, use_ref with
           | R_Int, true   -> (": int ref", "ref") | R_Float, true -> (": float ref", "ref")
           | R_Bool, true  -> (": bool ref", "ref") | R_Value, true -> (": Value.t ref", "ref")
           | R_Int, false  -> (": int", "") | R_Float, false-> (": float", "")
           | R_Bool, false -> (": bool", "") | R_Value, false-> (": Value.t", "")
        in
        let keyword_space = if String.is_empty binding_keyword then "" else " " in
        sprintf "let %s %s =%s%s (%s) in" ocaml_name ocaml_type_annot keyword_space binding_keyword init_code)
  in
  let let_bindings_code = String.concat ~sep:"\n  " let_bindings_code_list in
  (* Translate body sequence *)
  let body_code, body_repr = translate_progn_sequence !inner_env_ref needs_boxing_set body inferred_type in
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
         (* Qualify all T_* constructors *)
        let base_repr = match init_type with | InferredType.T_Int -> R_Int | InferredType.T_Float -> R_Float | InferredType.T_Bool | InferredType.T_Nil -> R_Bool | _ -> R_Value in
        let final_repr = if needs_boxing then R_Value else base_repr in
        let use_ref = is_mutated || needs_boxing in

        let init_code = match final_repr with
            | R_Int -> to_int current_env needs_boxing_set typed_init
            | R_Float -> to_float current_env needs_boxing_set typed_init
            | R_Bool -> to_bool current_env needs_boxing_set typed_init
            | R_Value -> to_value current_env needs_boxing_set typed_init
        in

        let next_env = add_binding current_env elisp_name ocaml_name base_repr is_mutated needs_boxing in

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
  (* Translate body sequence *)
  let body_code, body_repr = translate_progn_sequence final_env needs_boxing_set body inferred_type in
  (sprintf "(%s\n%s\n)" nested_lets_code (manual_indent 2 body_code), body_repr)

(* Modified: Pass needs_boxing_set down, use it for checks, return resulting repr *)
and translate_setq env needs_boxing_set pairs inferred_type : string * var_repr =
   (* Qualify all T_* constructors *)
  let target_repr = match inferred_type with | InferredType.T_Int -> R_Int | InferredType.T_Float -> R_Float | InferredType.T_Bool | InferredType.T_Nil -> R_Bool | _ -> R_Value in
  let assignments_code_list =
    List.map pairs ~f:(fun (sym_name, typed_value) ->
        (* Use explicit binding for lookup result to potentially help typechecker *)
        let entry_opt = lookup_var_info env sym_name in
        match entry_opt with
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
              | R_Value -> (* Should be Value.t ref if needs_boxing=false? Error or treat as Value.t ref *)
                  let value_code = to_value env needs_boxing_set typed_value in
                  sprintf "%s := %s;" ocaml_name value_code)
        | None ->
             (* Assignment to undefined variable within compiled scope *)
             failwithf "Translate Error: Attempt to setq undefined variable '%s' in compiled scope." sym_name ()
        )
  in
  (* Setq returns the *last value assigned*, converted to the target representation *)
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
  (* Qualify all T_* constructors *)
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
  (* Corrected: Generate the complete format string for the error message first *)
  let expected_args_fmt_str =
    sprintf "Expected %d%s args, got %%d" min_args
      (match max_args_opt with
      | None -> "+"
      | Some m when m = min_args -> ""
      | Some m -> sprintf "-%d" m)
  in
  Buffer.add_string code
    (sprintf (* Corrected: Call Printf.sprintf inside to format the message before passing to arity_error *)
       "    if num_runtime_args < %d %s then Runtime.arity_error \"lambda\" (Printf.sprintf %S num_runtime_args);\n"
       min_args
       (match max_args_opt with
       | None -> ""
       | Some m -> sprintf "|| num_runtime_args > %d" m) (* This part generates the condition correctly *)
       expected_args_fmt_str); (* Pass the format string here *)

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
  (* Corrected: Translate body and box result if necessary *)
  let body_code_raw, body_repr = translate_progn_sequence !inner_env_ref needs_boxing_set body inferred_return_type in
  let final_body_code = box_value body_code_raw body_repr in (* Box if needed *)
  Buffer.add_string code (sprintf "    %s\n))" final_body_code); (* Add potentially boxed body code *)
  Buffer.contents code


and translate_cond env needs_boxing_set clauses inferred_type : string * var_repr =
   (* Qualify all T_* constructors *)
  let target_repr = match inferred_type with | InferredType.T_Int -> R_Int | InferredType.T_Float -> R_Float | InferredType.T_Bool | InferredType.T_Nil -> R_Bool | _ -> R_Value in
  let rec build cls =
    match cls with
    | [] -> translate_expr env needs_boxing_set (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil }) target_repr
    | (typed_test, typed_body) :: rest ->
        let test_code = to_bool env needs_boxing_set typed_test in
        let result_code, _ = (* Ignore repr from body, use overall target_repr *)
          let body_exprs = if List.is_empty typed_body then [ typed_test ] else typed_body in
          translate_progn_sequence env needs_boxing_set body_exprs inferred_type
        in
        sprintf "(if %s then begin\n%s\nend else begin\n%s\nend)" test_code
          (manual_indent 4 result_code) (build rest)
  in
  (build clauses, target_repr)

and translate_funcall env needs_boxing_set func args inferred_type : string * var_repr =
  (* Determine target repr first *)
   (* Qualify all T_* constructors *)
  let target_repr = match inferred_type with | InferredType.T_Int -> R_Int | InferredType.T_Float -> R_Float | InferredType.T_Bool | InferredType.T_Nil -> R_Bool | _ -> R_Value in

  (* --- Try Optimized Builtins First --- *)
  let ( = ) = equal_var_repr in (* Use the derived equality for var_repr *)
  let optimized_result =
      match func, args with
      (* Arithmetic: Check inferred type of the *call* *)
      | TypedAst.Atom { value = Value.Symbol { name = "+"; _ }; _ }, [ a; b ] when target_repr = R_Int ->
          Some (sprintf "(%s + %s)" (to_int env needs_boxing_set a) (to_int env needs_boxing_set b))
      | TypedAst.Atom { value = Value.Symbol { name = "-"; _ }; _ }, [ a; b ] when target_repr = R_Int ->
          Some (sprintf "(%s - %s)" (to_int env needs_boxing_set a) (to_int env needs_boxing_set b))
      | TypedAst.Atom { value = Value.Symbol { name = "*"; _ }; _ }, [ a; b ] when target_repr = R_Int ->
          Some (sprintf "(%s * %s)" (to_int env needs_boxing_set a) (to_int env needs_boxing_set b))
      | TypedAst.Atom { value = Value.Symbol { name = "/"; _ }; _ }, [ a; b ] when target_repr = R_Int ->
          Some (sprintf "(%s / %s)" (to_int env needs_boxing_set a) (to_int env needs_boxing_set b))
      (* Add Float versions if needed *)
      (* Predicates (target_repr is R_Bool) *)
      | TypedAst.Atom { value = Value.Symbol { name = "integerp"; _ }; _ }, [ a ] when target_repr = R_Bool ->
          Some (sprintf "(match %s with Value.Int _ -> true | _ -> false)" (to_value env needs_boxing_set a))
      | TypedAst.Atom { value = Value.Symbol { name = "consp"; _ }; _ }, [ a ] when target_repr = R_Bool ->
          Some (sprintf "(match %s with Value.Cons _ -> true | _ -> false)" (to_value env needs_boxing_set a))
      (* Add other predicates *)
      (* Equality (target_repr is R_Bool) *)
      | TypedAst.Atom { value = Value.Symbol { name = "eq"; _ }; _ }, [ a; b ] when target_repr = R_Bool ->
          Some (sprintf "(Runtime.is_truthy (Runtime.builtin_eq [%s; %s]))" (to_value env needs_boxing_set a) (to_value env needs_boxing_set b))
      | TypedAst.Atom { value = Value.Symbol { name = "equal"; _ }; _ }, [ a; b ] when target_repr = R_Bool ->
          Some (sprintf "(Runtime.is_truthy (Runtime.builtin_equal [%s; %s]))" (to_value env needs_boxing_set a) (to_value env needs_boxing_set b))
      (* List ops: cons always returns R_Value *)
      | TypedAst.Atom { value = Value.Symbol { name = "cons"; _ }; _ }, [ a; b ] when target_repr = R_Value ->
          Some (sprintf "(Value.Cons { car = %s; cdr = %s })" (to_value env needs_boxing_set a) (to_value env needs_boxing_set b))
      (* car/cdr are tricky: result type depends on analysis *)
      (* Keep car/cdr in generic path for now unless we add specific type checks *)
      | _ -> None
  in

  match optimized_result with
  | Some code -> (code, target_repr) (* Return optimized code and the target repr *)
  | None ->
      (* --- Generic Function Call --- *)
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
(* Modified: Refactored to handle top-level setq and build env *)
let translate_toplevel texprs final_env_types needs_boxing_set =
  let body_buffer = Buffer.create 1024 in (* Buffer for the generated function body *)
  (* Map to track OCaml names and info for locally defined top-level vars *)
  let top_level_var_map = ref String.Map.empty in
  (* Convert final_env_types list to map for efficient lookup *)
  let initial_types_map = String.Map.of_alist_exn final_env_types in

  (* Add definitions (defun) first *)
  let definitions = List.filter texprs ~f:(function TypedAst.Defun _ -> true | _ -> false) in
  List.iter definitions ~f:(fun def_texpr ->
      match def_texpr with
      | TypedAst.Defun { name; args; body; fun_type; _ } ->
          (* Corrected: Use initial_types_map *)
          let initial_type_opt = Map.find initial_types_map name in
          (* Qualify all T_* constructors *)
          let base_repr = match initial_type_opt with Some(InferredType.T_Int) -> R_Int | Some(InferredType.T_Float) -> R_Float | Some(InferredType.T_Bool | InferredType.T_Nil) -> R_Bool | _ -> R_Value in
          let is_mutated = true (* Defun is always mutable *) in
          let needs_boxing = Set.mem needs_boxing_set name in
          let ocaml_name = generate_ocaml_var name in

          (* Add to tracking map *)
          top_level_var_map := Map.set !top_level_var_map ~key:name ~data:{ ocaml_name; repr = base_repr; is_mutated; needs_boxing };

          (* Translate lambda body (pass current top_level_var_map as env) *)
          let lambda_code = translate_lambda !top_level_var_map needs_boxing_set args body fun_type in
          (* Generate OCaml code for the ref definition *)
          Buffer.add_string body_buffer (sprintf "let %s : Value.t ref = ref (%s) in\n" ocaml_name lambda_code)
      | _ -> () (* Should not happen *)
    );

  (* Initialize the mutable environment table within the generated code *)
  Buffer.add_string body_buffer "let module_env_tbl = String.Table.create () ~size:16 in\n";
  (* Add defined functions to the table *)
  Map.iteri !top_level_var_map ~f:(fun ~key:name ~data:{ ocaml_name; _ } ->
      Buffer.add_string body_buffer (sprintf "Hashtbl.set module_env_tbl ~key:%S ~data:!%s;\n" name ocaml_name)
    );

  (* Process run expressions sequentially *)
  let run_expressions = List.filter texprs ~f:(function TypedAst.Defun _ -> false | _ -> true) in
  List.iter run_expressions ~f:(fun expr ->
      (* Special handling for top-level Setq *)
      match expr with
      | TypedAst.Setq { pairs; inferred_type=_ } ->
          List.iter pairs ~f:(fun (sym_name, typed_value) ->
              let current_env = !top_level_var_map in
              let value_needs_boxing = Set.mem needs_boxing_set sym_name in
              let value_ast_type = TypedAst.get_type typed_value in
               (* Qualify all T_* constructors *)
              let value_base_repr = match value_ast_type with | InferredType.T_Int -> R_Int | InferredType.T_Float -> R_Float | InferredType.T_Bool | InferredType.T_Nil -> R_Bool | _ -> R_Value in
              let value_final_repr = if value_needs_boxing then R_Value else value_base_repr in

              (* Translate value using current top-level env *)
              let value_code = match value_final_repr with
                | R_Int -> to_int current_env needs_boxing_set typed_value
                | R_Float -> to_float current_env needs_boxing_set typed_value
                | R_Bool -> to_bool current_env needs_boxing_set typed_value
                | R_Value -> to_value current_env needs_boxing_set typed_value
              in

              match Map.find current_env sym_name with
              | Some { ocaml_name; is_mutated; needs_boxing; repr=base_repr } ->
                  (* Existing variable assignment *)
                  if not is_mutated then
                    failwithf "Translate Error: Attempt to setq non-mutable top-level variable '%s'" sym_name ()
                  else
                    let assign_code =
                      if needs_boxing then (* Assigning to Value.t ref *)
                         sprintf "%s := %s;" ocaml_name (to_value current_env needs_boxing_set typed_value)
                      else (* Assigning to native ref *)
                         match base_repr with
                         | R_Int -> sprintf "%s := %s;" ocaml_name (to_int current_env needs_boxing_set typed_value)
                         | R_Float -> sprintf "%s := %s;" ocaml_name (to_float current_env needs_boxing_set typed_value)
                         | R_Bool -> sprintf "%s := %s;" ocaml_name (to_bool current_env needs_boxing_set typed_value)
                         | R_Value -> sprintf "%s := %s;" ocaml_name (to_value current_env needs_boxing_set typed_value)
                    in
                    Buffer.add_string body_buffer assign_code;
                    (* Update the Hashtbl for the final environment *)
                    (* Need to get the updated value from the ref *)
                    let updated_ocaml_value = sprintf "!%s" ocaml_name in
                    let boxed_update_val = box_value updated_ocaml_value base_repr in
                    Buffer.add_string body_buffer (sprintf "\nHashtbl.set module_env_tbl ~key:%S ~data:%s;\n" sym_name boxed_update_val)

              | None ->
                  (* New variable definition *)
                  (* TODO: Mutation analysis for top-level vars needs lookahead. Assume immutable for now unless boxed. *)
                  let is_mutated = false in
                  let needs_boxing = value_needs_boxing in
                  let final_repr = value_final_repr in
                  let use_ref = is_mutated || needs_boxing in
                  let ocaml_name = generate_ocaml_var sym_name in

                  (* Add binding to tracking map for subsequent expressions *)
                  (* Corrected: Use value_base_repr *)
                  top_level_var_map := Map.set !top_level_var_map ~key:sym_name ~data:{ ocaml_name; repr=value_base_repr; is_mutated; needs_boxing };

                  (* Generate OCaml let binding *)
                  let ocaml_type_annot, binding_keyword =
                     match final_repr, use_ref with
                     | R_Int, true   -> (": int ref", "ref") | R_Float, true -> (": float ref", "ref")
                     | R_Bool, true  -> (": bool ref", "ref") | R_Value, true -> (": Value.t ref", "ref")
                     | R_Int, false  -> (": int", "") | R_Float, false-> (": float", "")
                     | R_Bool, false -> (": bool", "") | R_Value, false-> (": Value.t", "")
                  in
                  let keyword_space = if String.is_empty binding_keyword then "" else " " in
                  Buffer.add_string body_buffer (sprintf "let %s %s =%s%s (%s) in\n" ocaml_name ocaml_type_annot keyword_space binding_keyword value_code);
                  (* Add to the Hashtbl for the final environment *)
                  let value_to_box = if use_ref then sprintf "!%s" ocaml_name else ocaml_name in
                  (* Corrected: Use value_base_repr *)
                  let boxed_val = box_value value_to_box value_base_repr in
                  Buffer.add_string body_buffer (sprintf "Hashtbl.set module_env_tbl ~key:%S ~data:%s;\n" sym_name boxed_val)
            )
      | _ ->
          (* Other top-level expressions (e.g., function calls for side effects) *)
          let code, _ = translate_node !top_level_var_map needs_boxing_set expr in
          Buffer.add_string body_buffer (sprintf "let (_ : _) = %s in ()\n" code)
    );

  (* Add final return *)
  Buffer.add_string body_buffer "Hashtbl.to_alist module_env_tbl\n";

  (* Assemble the final OCaml module string *)
  sprintf
    "(* Generated by Scaml *)\n\n\
     open! Core\n\
     module Value = Scaml.Value \n\
     module Runtime = Scaml.Runtime \n\
     module Compiler = Scaml.Compiler\n\n\
     (* Function to execute top-level forms and return the defined environment *)\n\
     let execute_and_get_env () : (string * Value.t) list = \n\
    \ %s\n\
     (* Set the shared ref in the Compiler module *) \n\
     let () = \n\
    \   try \n\
    \     Compiler.last_loaded_environment := Some (execute_and_get_env ()) \n\
    \   with exn -> \n\
    \     (* Handle potential exceptions during environment creation or assignment *) \n\
    \     Printf.eprintf \"Error setting shared environment ref: %%s\\n%%!\" (Exn.to_string exn); \n\
    \     Compiler.last_loaded_environment := None \n\
    "
    (manual_indent 2 (Buffer.contents body_buffer)) (* Indent the whole body *)


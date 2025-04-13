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
    (* --- CORRECTION: Translate Cons --- *)
    (* Cons cells in Value.t are NOT refs directly, they contain refs *)
    (* The generated code should create the Value.t structure correctly *)
    | Value.Cons { car; cdr } ->
        (* Generate code that creates the Cons structure *)
        sprintf "(Value.Cons { car = (%s); cdr = (%s) })"
          (translate_quoted_data car)
          (translate_quoted_data cdr)
    (* Cannot translate closures or builtins directly *)
    | Value.Function _ -> "\"(Value.Function <opaque>)\"" (* Represent as string literal for now *)
    | Value.Builtin _ -> "\"(Value.Builtin <opaque>)\"" (* Represent as string literal for now *)

end

(* --- Environment (Keep as is) --- *)
type var_repr = R_Value | R_Int | R_Float | R_Bool [@@deriving sexp_of]

type env_entry = {
  ocaml_name : string;
  repr : var_repr;
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

let add_binding env elisp_name ocaml_name repr =
  Map.set env ~key:elisp_name ~data:{ ocaml_name; repr }

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
  (* Atom case now uses the Value.t stored *)
  | TypedAst.Atom { value; inferred_type } -> begin
      match inferred_type with
      | InferredType.T_Int -> (
          match value with
          | Value.Int i -> Int.to_string i
          | _ -> failwith "Type mismatch: InferredType.T_Int but not Value.Int")
      | InferredType.T_Float -> (
          match value with
          | Value.Float f -> Float.to_string f
          | _ -> failwith "Type mismatch: InferredType.T_Float but not Value.Float")
      | InferredType.T_Nil -> "false" (* Represent Nil as false for bool repr *)
      | InferredType.T_Bool -> (
          match value with
          | Value.T -> "true"
          | Value.Nil -> "false" (* Should not happen if type is Bool, but handle *)
          | _ -> failwith "Type mismatch: InferredType.T_Bool but not T/Nil")
      | InferredType.T_Keyword -> (
          match value with
          | Value.Keyword k -> sprintf "(Value.Keyword %S)" k
          | _ -> failwith "Type mismatch: InferredType.T_Keyword")
      | InferredType.T_String -> (
          match value with
          | Value.String s -> sprintf "(Value.String %S)" s
          | _ -> failwith "Type mismatch: InferredType.T_String")
      | InferredType.T_Char -> (
          match value with
          | Value.Char c -> sprintf "(Value.Char %C)" c
          | _ -> failwith "Type mismatch: InferredType.T_Char")
      | InferredType.T_Symbol -> (
          match value with
          | Value.Symbol { name } -> (
              match lookup_var_info env name with
              (* Local variables are refs *)
              | Some { ocaml_name; repr = R_Value } -> sprintf "!%s" ocaml_name
              | Some { ocaml_name; repr = R_Int } -> box_int (sprintf "!%s" ocaml_name)
              | Some { ocaml_name; repr = R_Float } -> box_float (sprintf "!%s" ocaml_name)
              | Some { ocaml_name; repr = R_Bool } -> box_bool (sprintf "!%s" ocaml_name)
              | None -> sprintf "(Runtime.lookup_variable %S)" name (* Global *)
              )
          | _ -> failwith "Type mismatch: InferredType.T_Symbol but not Value.Symbol")
      (* Other types are represented as Value.t *)
      | InferredType.T_Var _ | T_Cons _ | T_Vector _ | T_Function _ | T_Union _ | T_Any
      | InferredType.T_Unknown -> (
          match value with
          | Value.Symbol { name } -> (
              (* Symbol representing a complex value *)
              match lookup_var_info env name with
              | Some { ocaml_name; repr = R_Value } -> sprintf "!%s" ocaml_name
              | Some { ocaml_name; repr = R_Int } -> box_int (sprintf "!%s" ocaml_name)
              | Some { ocaml_name; repr = R_Float } -> box_float (sprintf "!%s" ocaml_name)
              | Some { ocaml_name; repr = R_Bool } -> box_bool (sprintf "!%s" ocaml_name)
              | None -> sprintf "(Runtime.lookup_variable %S)" name)
          (* Atom itself is the complex value (e.g., literal vector) *)
          | _ -> Translate_quote.translate_quoted_data value
          )
    end
  (* Quote case now uses the Value.t stored *)
  | TypedAst.Quote { value; inferred_type = _ } ->
      Translate_quote.translate_quoted_data value
  | TypedAst.If { cond; then_branch; else_branch; inferred_type } ->
      let cond_code = to_bool env cond in
      let target_repr =
        match inferred_type with
        | InferredType.T_Int -> R_Int
        | InferredType.T_Float -> R_Float
        | InferredType.T_Bool | T_Nil -> R_Bool
        | _ -> R_Value
      in
      let then_code = translate_expr env then_branch target_repr in
      let else_code =
        match else_branch with
        | None ->
            (* Elisp 'if' returns nil if else branch is missing and cond is false *)
            translate_expr env
              (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil })
              target_repr
        | Some eb -> translate_expr env eb target_repr
      in
      sprintf "(if %s then\n   %s\n else\n   %s)" cond_code
        (manual_indent 3 then_code)
        (manual_indent 3 else_code)
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
  | TypedAst.Defun { name; inferred_type = InferredType.T_Symbol; _ } ->
      (* Defun expression evaluates to the symbol name *)
      sprintf "(Value.Symbol { name = %S })" name
  | TypedAst.Defun { name; inferred_type = other_type; _ } ->
      (* This case should ideally not happen if analysis is correct *)
      Printf.eprintf
        "Warning: Defun '%s' has unexpected inferred type %s. \
         Generating symbol.\n%!" (* Added %! *)
        name (InferredType.to_string other_type);
      sprintf "(Value.Symbol { name = %S })" name
  | TypedAst.Cond { clauses; inferred_type } ->
      translate_cond env clauses inferred_type
  | TypedAst.Funcall { func; args; inferred_type } ->
      translate_funcall env func args inferred_type

and translate_progn env forms inferred_type =
  match forms with
  | [] ->
      (* Empty progn returns nil *)
      translate_expr env
        (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil })
        (match inferred_type with (* Match target repr based on overall type *)
         | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool | _ -> R_Value)
  | [ last ] -> translate_node env last (* Single form, translate directly *)
  | _ ->
      let target_repr =
        match inferred_type with
        | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
        | _ -> R_Value
      in
      (* Translate all but the last form to Value.t for side effects *)
      let translated_forms_side_effects =
          List.map (List.drop_last_exn forms) ~f:(fun expr -> to_value env expr) in
      (* Translate the last form to the target representation *)
      let last_form = List.last_exn forms in
      let translated_last = translate_expr env last_form target_repr in
      (* Combine them, ensuring side effects happen *)
      let sequence_code =
        translated_forms_side_effects
        |> List.map ~f:(sprintf "let (_ : Value.t) = %s in")
        |> String.concat ~sep:"\n  "
      in
      if String.is_empty sequence_code then translated_last
      else sprintf "(%s\n  %s)" sequence_code translated_last

and translate_let env bindings body inferred_type =
  let inner_env_ref = ref env in
  let let_bindings_code_list =
    List.map bindings ~f:(fun (elisp_name, typed_init) ->
        let init_type = TypedAst.get_type typed_init in
        let ocaml_name = generate_ocaml_var elisp_name in
        (* Evaluate initializer in the *outer* environment *)
        let repr, init_code =
          match init_type with
          | InferredType.T_Int -> (R_Int, to_int env typed_init)
          | InferredType.T_Float -> (R_Float, to_float env typed_init)
          | InferredType.T_Bool | T_Nil -> (R_Bool, to_bool env typed_init)
          | _ -> (R_Value, to_value env typed_init)
        in
        (* Add binding to the environment *for the body* *)
        inner_env_ref := add_binding !inner_env_ref elisp_name ocaml_name repr;
        (* Generate let binding code (creates refs) *)
        let ocaml_type_annot =
          match repr with
          | R_Int -> ": int ref" | R_Float -> ": float ref"
          | R_Bool -> ": bool ref" | R_Value -> ": Value.t ref"
        in
        sprintf "let %s %s = ref (%s) in" ocaml_name ocaml_type_annot init_code)
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
      ~f:(fun (current_env, current_code) (elisp_name, typed_init) ->
        let init_type = TypedAst.get_type typed_init in
        let ocaml_name = generate_ocaml_var elisp_name in
        (* Evaluate initializer in the *current sequential* environment *)
        let repr, init_code =
          match init_type with
          | InferredType.T_Int -> (R_Int, to_int current_env typed_init)
          | InferredType.T_Float -> (R_Float, to_float current_env typed_init)
          | InferredType.T_Bool | T_Nil -> (R_Bool, to_bool current_env typed_init)
          | _ -> (R_Value, to_value current_env typed_init)
        in
        (* Add binding for the *next* initializer/body *)
        let next_env = add_binding current_env elisp_name ocaml_name repr in
        let ocaml_type_annot =
          match repr with
          | R_Int -> ": int ref" | R_Float -> ": float ref"
          | R_Bool -> ": bool ref" | R_Value -> ": Value.t ref"
        in
        let new_let =
          sprintf "let %s %s = ref (%s) in" ocaml_name ocaml_type_annot init_code
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
        (* Evaluate the value expression *)
        let value_type = TypedAst.get_type typed_value in
        match lookup_var_info env sym_name with
        | Some { ocaml_name; repr = R_Int } ->
            sprintf "%s := (%s);" ocaml_name (to_int env typed_value)
        | Some { ocaml_name; repr = R_Float } ->
            sprintf "%s := (%s);" ocaml_name (to_float env typed_value)
        | Some { ocaml_name; repr = R_Bool } ->
            sprintf "%s := (%s);" ocaml_name (to_bool env typed_value)
        | Some { ocaml_name; repr = R_Value } ->
            (* If local var is Value.t, assign based on value's type *)
            let value_code = match value_type with
              | T_Int -> to_int env typed_value |> box_int
              | T_Float -> to_float env typed_value |> box_float
              | T_Bool | T_Nil -> to_bool env typed_value |> box_bool
              | _ -> to_value env typed_value
            in
            sprintf "%s := (%s);" ocaml_name value_code
        | None ->
            (* Global variable: always assign Value.t *)
            sprintf "let (_ : Value.t) = Runtime.set_global_variable %S (%s) \
                     in ();"
              sym_name (to_value env typed_value))
  in
  (* Setq returns the last value assigned *)
  let return_value_code =
    match List.last pairs with
    | None ->
        (* Empty setq returns nil *)
        translate_expr env
          (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil })
          target_repr
    | Some (_, v) -> translate_expr env v target_repr
  in
  let assignments_code = String.concat ~sep:"\n    " assignments_code_list in
  if String.is_empty assignments_code then return_value_code
  else sprintf "(let () = \n    %s\n  in\n  %s)" assignments_code
         return_value_code

and translate_lambda env arg_spec body fun_type =
  let open InferredType in
  (* Determine argument types and return type from the function type *)
  let inferred_arg_types_list, inferred_return_type =
    match fun_type with
    | InferredType.T_Function { arg_types = Some types; return_type } -> (types, return_type)
    | InferredType.T_Function { arg_types = None; return_type } ->
         Printf.eprintf "Warning: Lambda has varargs type, precise arg types lost.\n%!";
         (* Create dummy 'Any' types based on arg_spec *)
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
  let max_args_opt =
    if Option.is_some arg_spec.rest then None
    else Some (min_args + List.length arg_spec.optional)
  in
  Buffer.add_string code
    (sprintf "    let num_runtime_args = List.length runtime_args in\n");
  let arity_check_msg =
    sprintf "\"lambda\" \"Expected %d%s args, got %%d\"" min_args
      (match max_args_opt with
      | None -> "+"
      | Some m when m = min_args -> ""
      | Some m -> sprintf "-%d" m)
  in
  Buffer.add_string code
    (sprintf
       "    if num_runtime_args < %d %s then Runtime.arity_error %s \
        num_runtime_args;\n" (* Use %d format *)
       min_args
       (match max_args_opt with
       | None -> ""
       | Some m -> sprintf "|| num_runtime_args > %d" m)
       arity_check_msg);

  (* Argument Binding & Environment Setup *)
  let inner_env_ref = ref env in
  let arg_bindings_code = Buffer.create 128 in
  let arg_idx = ref 0 in
  (* Required Args *)
  List.iter arg_spec.required ~f:(fun name ->
      let idx = !arg_idx in
       if idx >= Array.length inferred_arg_types then failwithf "Lambda arity mismatch (internal error): required arg %s index %d out of bounds %d" name idx (Array.length inferred_arg_types) ();
      let arg_type = inferred_arg_types.(idx) in
      let ocaml_name = generate_ocaml_var name in
      let runtime_arg = sprintf "(List.nth_exn runtime_args %d)" idx in
      let repr, setup_code =
        match arg_type with
        | InferredType.T_Int ->
            (R_Int, sprintf "let %s : int ref = ref (%s) in" ocaml_name
                      (unbox_int runtime_arg))
        | InferredType.T_Float ->
            (R_Float, sprintf "let %s : float ref = ref (%s) in" ocaml_name
                        (unbox_float runtime_arg))
        | InferredType.T_Bool | T_Nil ->
            (R_Bool, sprintf "let %s : bool ref = ref (%s) in" ocaml_name
                       (unbox_bool runtime_arg))
        | _ -> (* T_Value, T_Any, T_Var, T_Cons, etc. *)
            (R_Value, sprintf "let %s : Value.t ref = ref %s in" ocaml_name
                        runtime_arg)
      in
      Buffer.add_string arg_bindings_code (sprintf "    %s\n" setup_code);
      inner_env_ref := add_binding !inner_env_ref name ocaml_name repr;
      incr arg_idx);
  (* Optional Args *)
  List.iter arg_spec.optional ~f:(fun (name, default_val_opt) ->
      let idx = !arg_idx in
      if idx >= Array.length inferred_arg_types then failwithf "Lambda arity mismatch (internal error): optional arg %s index %d out of bounds %d" name idx (Array.length inferred_arg_types) ();
      let arg_type = inferred_arg_types.(idx) in
      let ocaml_name = generate_ocaml_var name in
      (* Translate default value if present *)
      let default_value_expr =
        match default_val_opt with
        | None -> "Value.Nil" (* Elisp default is nil *)
        | Some dv -> Translate_quote.translate_quoted_data dv
      in
      let runtime_arg_expr = sprintf "(List.nth_exn runtime_args %d)" idx in
      let condition = sprintf "(num_runtime_args > %d)" idx in
      (* Generate code to get arg if present, else default *)
      let repr, setup_code =
        match arg_type with
        | InferredType.T_Int ->
            ( R_Int,
              sprintf
                "let %s : int ref = ref (if %s then %s else %s) in"
                ocaml_name condition (unbox_int runtime_arg_expr)
                (unbox_int default_value_expr) ) (* Unbox default too *)
        | InferredType.T_Float ->
            ( R_Float,
              sprintf
                "let %s : float ref = ref (if %s then %s else %s) in"
                ocaml_name condition (unbox_float runtime_arg_expr)
                (unbox_float default_value_expr) ) (* Unbox default too *)
        | InferredType.T_Bool | T_Nil ->
            ( R_Bool,
              sprintf
                "let %s : bool ref = ref (if %s then %s else %s) in"
                ocaml_name condition (unbox_bool runtime_arg_expr)
                (unbox_bool default_value_expr) ) (* Unbox default too *)
        | _ ->
            ( R_Value,
              sprintf
                "let %s : Value.t ref = ref (if %s then %s else %s) in"
                ocaml_name condition runtime_arg_expr default_value_expr )
      in
      Buffer.add_string arg_bindings_code (sprintf "    %s\n" setup_code);
      inner_env_ref := add_binding !inner_env_ref name ocaml_name repr;
      incr arg_idx);
  (* Rest Arg *)
  (match arg_spec.rest with
  | None -> ()
  | Some name ->
      let start_idx = !arg_idx in
      let ocaml_name = generate_ocaml_var name in
      (* Rest arg is always a Value.t list *)
      Buffer.add_string arg_bindings_code
        (sprintf
           "    let %s : Value.t ref = ref (Value.list_to_value \
            (List.drop runtime_args %d)) in"
           ocaml_name start_idx);
      inner_env_ref := add_binding !inner_env_ref name ocaml_name R_Value);

  Buffer.add_buffer code arg_bindings_code; (* Add bindings setup *)

  (* Translate Body *)
  (* The body's return value should be boxed according to the lambda's return type *)
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
    | [] ->
        (* Cond returns nil if no clauses match *)
        translate_expr env
          (TypedAst.Atom { value = Value.Nil; inferred_type = InferredType.T_Nil })
          target_repr
    | (typed_test, typed_body) :: rest ->
        let test_code = to_bool env typed_test in
        let result_code =
          (* If body is empty, result is the value of the test *)
          let body_exprs =
            if List.is_empty typed_body then [ typed_test ] else typed_body
          in
          (* Translate the effective body (test or actual body) *)
          translate_progn env body_exprs inferred_type
        in
        sprintf "(if %s then begin\n%s\nend else begin\n%s\nend)" test_code
          (manual_indent 4 result_code)
          (build rest) (* Recursively build else branch *)
  in
  build clauses

and translate_funcall env func args inferred_type =
  (* Try optimized builtins first *)
  match func, args with
  (* Arithmetic (assuming integer result based on inferred_type) *)
  | TypedAst.Atom { value = Value.Symbol { name = "+"; _ }; _ }, [ a; b ]
    when [%compare.equal: InferredType.t] inferred_type InferredType.T_Int ->
      sprintf "(%s + %s)" (to_int env a) (to_int env b)
  | TypedAst.Atom { value = Value.Symbol { name = "-"; _ }; _ }, [ a; b ]
    when [%compare.equal: InferredType.t] inferred_type InferredType.T_Int ->
      sprintf "(%s - %s)" (to_int env a) (to_int env b)
  | TypedAst.Atom { value = Value.Symbol { name = "*"; _ }; _ }, [ a; b ]
    when [%compare.equal: InferredType.t] inferred_type InferredType.T_Int ->
      sprintf "(%s * %s)" (to_int env a) (to_int env b)
  | TypedAst.Atom { value = Value.Symbol { name = "/"; _ }; _ }, [ a; b ]
    when [%compare.equal: InferredType.t] inferred_type InferredType.T_Int ->
      sprintf "(%s / %s)" (to_int env a) (to_int env b) (* Integer division *)

  (* Predicates (result is bool) *)
   | TypedAst.Atom { value = Value.Symbol { name = "integerp"; _ }; _ }, [ a ]
    when [%compare.equal: InferredType.t] inferred_type InferredType.T_Bool ->
      sprintf "(match %s with Value.Int _ -> true | _ -> false)" (to_value env a)
   | TypedAst.Atom { value = Value.Symbol { name = "consp"; _ }; _ }, [ a ]
    when [%compare.equal: InferredType.t] inferred_type InferredType.T_Bool ->
      sprintf "(match %s with Value.Cons _ -> true | _ -> false)" (to_value env a)
   (* Add other optimized predicates similarly *)

  (* Equality (result is bool, needs Value.t comparison) *)
  | TypedAst.Atom { value = Value.Symbol { name = "eq"; _ }; _ }, [ a; b ]
    when [%compare.equal: InferredType.t] inferred_type InferredType.T_Bool ->
      (* Eq needs Value.t representation *)
      sprintf "(Runtime.is_truthy (Runtime.builtin_eq [%s; %s]))"
        (to_value env a) (to_value env b)
  | TypedAst.Atom { value = Value.Symbol { name = "equal"; _ }; _ }, [ a; b ]
     when [%compare.equal: InferredType.t] inferred_type InferredType.T_Bool ->
      (* Equal needs Value.t representation *)
       sprintf "(Runtime.is_truthy (Runtime.builtin_equal [%s; %s]))"
         (to_value env a) (to_value env b)


  (* List operations *)
  | TypedAst.Atom { value = Value.Symbol { name = "car"; _ }; _ }, [ a ] ->
      let target_repr =
        match inferred_type with
        | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
        | _ -> R_Value
      in
      let arg_code = to_value env a in (* car operates on Value.t *)
      (* Generate code matching Runtime.builtin_car logic *)
      let car_logic_code =
        sprintf
          "(match %s with \
           | Value.Cons { car = c; _ } -> c \
           | Value.Nil -> Value.Nil \
           | other -> Runtime.type_error \"car\" \"cons cell or nil\" other)"
          arg_code
      in
      (* Convert result to target representation *)
      (match target_repr with
      | R_Int -> unbox_int car_logic_code
      | R_Float -> unbox_float car_logic_code
      | R_Bool -> unbox_bool car_logic_code
      | R_Value -> car_logic_code)

   | TypedAst.Atom { value = Value.Symbol { name = "cdr"; _ }; _ }, [ a ] ->
      let target_repr =
        match inferred_type with
        | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
        | _ -> R_Value
      in
      let arg_code = to_value env a in (* cdr operates on Value.t *)
      let cdr_logic_code =
         sprintf
           "(match %s with \
            | Value.Cons { cdr = d; _ } -> d \
            | Value.Nil -> Value.Nil \
            | other -> Runtime.type_error \"cdr\" \"cons cell or nil\" other)"
           arg_code
      in
      (match target_repr with
      | R_Int -> unbox_int cdr_logic_code
      | R_Float -> unbox_float cdr_logic_code
      | R_Bool -> unbox_bool cdr_logic_code
      | R_Value -> cdr_logic_code)

   | TypedAst.Atom { value = Value.Symbol { name = "cons"; _ }; _ }, [ a; b ] ->
       (* Cons always returns Value.t *)
       sprintf "(Value.Cons { car = %s; cdr = %s })" (to_value env a) (to_value env b)


  | _ -> (* Default: Generic function call *)
      translate_generic_funcall env func args inferred_type

and translate_generic_funcall env func args inferred_type =
  (* Translate the function expression itself to Value.t *)
  let func_code = to_value env func in
  (* Translate all arguments to Value.t *)
  let arg_codes_value = List.map args ~f:(to_value env) in
  (* Generate the Runtime.apply_function call *)
  let call_code =
    sprintf "(Runtime.apply_function (%s) [%s])" func_code
      (String.concat ~sep:"; " arg_codes_value)
  in
  (* Determine the target representation based on the call's inferred type *)
  let target_repr =
    match inferred_type with
    | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
    | _ -> R_Value
  in
  (* Convert the result (which is Value.t) to the target representation *)
  match target_repr with
  | R_Int -> unbox_int call_code
  | R_Float -> unbox_float call_code
  | R_Bool -> unbox_bool call_code
  | R_Value -> call_code

(* --- Top Level Translation --- *)
let translate_toplevel texprs final_env_types =
  let definitions = ref [] in
  let run_expressions = ref [] in
  (* Separate definitions (defun) from top-level expressions *)
  List.iter texprs ~f:(fun texpr ->
      match texpr with
      | TypedAst.Defun _ -> definitions := !definitions @ [ texpr ]
      | _ -> run_expressions := !run_expressions @ [ texpr ]);

  (* Create the initial top-level environment map for globals/functions *)
  let top_env_map =
    String.Map.of_alist_exn
      (List.map final_env_types ~f:(fun (name, ty) ->
           let ocaml_name = generate_ocaml_var name in
           let repr =
             match ty with
             | InferredType.T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
             | _ -> R_Value
           in
           (name, { ocaml_name; repr })))
  in
  let top_env = top_env_map in

  (* Translate definitions (currently only defun) *)
  let def_codes =
    List.filter_map !definitions ~f:(fun def_texpr ->
        match def_texpr with
        | TypedAst.Defun { name; args; body; fun_type; _ } ->
            let entry = Map.find_exn top_env_map name in
            let ocaml_func_name = entry.ocaml_name in
            (* Translate the lambda body using the top-level environment *)
            let lambda_code = translate_lambda top_env args body fun_type in
            (* Define the global function variable as a ref holding the lambda *)
            Some (sprintf "let %s : Value.t ref = ref (%s)" ocaml_func_name
                    lambda_code)
        | _ -> None) (* Should not happen due to filtering *)
  in
  (* Combine definitions with 'let rec ... and ...' *)
  let definitions_code =
    match def_codes with
    | [] -> ""
    | hd :: tl -> "let rec " ^ hd ^ (List.map tl ~f:(sprintf "\nand %s") |> String.concat)
  in

  (* Translate the top-level expressions to run *)
  let run_body_code = translate_progn top_env !run_expressions InferredType.T_Any in

  (* Generate code to export the environment *)
  let env_export_entries =
    Map.to_alist top_env_map
    |> List.filter_map ~f:(fun (elisp_name, entry) ->
           (* Get the current value from the ref *)
           let value_code =
             match entry.repr with
             | R_Value -> sprintf "!%s" entry.ocaml_name
             | R_Int -> box_int (sprintf "!%s" entry.ocaml_name)
             | R_Float -> box_float (sprintf "!%s" entry.ocaml_name)
             | R_Bool -> box_bool (sprintf "!%s" entry.ocaml_name)
           in
           Some (sprintf "(%S, %s)" elisp_name value_code))
  in
  let env_export_code = sprintf "[%s]" (String.concat ~sep:"; " env_export_entries) in

  (* Assemble the final OCaml module string *)
  (* *** MODIFIED HERE: Use Scaml.<Module> instead of Scaml__.<Module> *** *)
  sprintf
    "(* Generated by Scaml *)\n\n\
     open! Core\n\
     (* Bring required modules into scope locally using public names *)\n\
     module Value = Scaml.Value \n\
     module Runtime = Scaml.Runtime \n\
     module Compiler = Scaml.Compiler\n\n\
     (* Definitions *)\n\
     %s\n\n\
     (* Function to expose defined environment *)\n\
     let get_environment () : (string * Value.t) list = \n\
    \  %s\n\n\
     (* Top-level expressions to run *)\n\
     let run () : Value.t =\n\
    \  %s\n\n\
     (* Register functions with the Compiler module via Callback system *)\n\
     let () = try \n\
    \    let (register_run : (unit -> Value.t) -> unit) = \n\
    \      Callback.lookup \"scaml_register_run\" in \n\
    \    register_run run \n\
    \  with Not_found -> \n\
    \    Printf.eprintf \"Warning: scaml_register_run callback not found.\\n%%!;\"\n\n\
     let () = try \n\
    \    let (register_env : (unit -> (string * Value.t) list) -> unit) = \n\
    \      Callback.lookup \"scaml_register_env\" in \n\
    \    register_env get_environment \n\
    \  with Not_found -> \n\
    \    Printf.eprintf \"Warning: scaml_register_env callback not found.\\n%%!;\""
    definitions_code
    (manual_indent 2 env_export_code)
    (manual_indent 2 run_body_code)


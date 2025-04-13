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
        sprintf "(Value.Cons { car = ref (%s); cdr = ref (%s) })"
          (translate_quoted_data !car)
          (translate_quoted_data !cdr)
    (* Cannot translate closures or builtins directly *)
    | Value.Function _ -> "\"(Value.Function <opaque>)\""
    | Value.Builtin _ -> "\"(Value.Builtin <opaque>)\""
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
    | T_Int -> R_Int
    | T_Float -> R_Float
    | T_Nil | T_Bool -> R_Bool
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
      | T_Int -> (
          match value with
          | Value.Int i -> Int.to_string i
          | _ -> failwith "Type mismatch: T_Int but not Value.Int")
      | T_Float -> (
          match value with
          | Value.Float f -> Float.to_string f
          | _ -> failwith "Type mismatch: T_Float but not Value.Float")
      | T_Nil -> "false"
      | T_Bool -> (
          match value with
          | Value.T -> "true"
          | Value.Nil -> "false"
          | _ -> failwith "Type mismatch: T_Bool but not T/Nil")
      | T_Keyword -> (
          match value with
          | Value.Keyword k -> sprintf "(Value.Keyword %S)" k
          | _ -> failwith "Type mismatch: T_Keyword")
      | T_String -> (
          match value with
          | Value.String s -> sprintf "(Value.String %S)" s
          | _ -> failwith "Type mismatch: T_String")
      | T_Char -> (
          match value with
          | Value.Char c -> sprintf "(Value.Char %C)" c
          | _ -> failwith "Type mismatch: T_Char")
      | T_Symbol -> (
          match value with
          | Value.Symbol { name } -> (
              match lookup_var_info env name with
              | Some entry -> sprintf "!%s" entry.ocaml_name (* Access local ref *)
              | None -> sprintf "(Runtime.lookup_variable %S)" name (* Global *)
              )
          | _ -> failwith "Type mismatch: T_Symbol but not Value.Symbol")
      | T_Var _ | T_Cons _ | T_Vector _ | T_Function _ | T_Union _ | T_Any
      | T_Unknown -> (
          (* These complex types are represented as Value.t *)
          match value with
          | Value.Symbol { name } -> (
              (* If it's a symbol representing one of these... *)
              match lookup_var_info env name with
              | Some { ocaml_name; repr = R_Value } -> sprintf "!%s" ocaml_name
              | Some { ocaml_name; repr = R_Int } ->
                  box_int (sprintf "!%s" ocaml_name)
              | Some { ocaml_name; repr = R_Float } ->
                  box_float (sprintf "!%s" ocaml_name)
              | Some { ocaml_name; repr = R_Bool } ->
                  box_bool (sprintf "!%s" ocaml_name)
              | None -> sprintf "(Runtime.lookup_variable %S)" name)
          (* If the atom itself is the complex value *)
          | Value.Vector _ | Value.Cons _ | Value.Function _ | Value.Builtin _ ->
              Translate_quote.translate_quoted_data value (* Treat as quoted *)
          | _ ->
              failwithf "Cannot translate atom %s for complex type %s"
                (!Value.to_string value)
                (InferredType.to_string inferred_type)
                ())
    end
  (* Quote case now uses the Value.t stored *)
  | TypedAst.Quote { value; inferred_type = _ } ->
      Translate_quote.translate_quoted_data value
  | TypedAst.If { cond; then_branch; else_branch; inferred_type } ->
      let cond_code = to_bool env cond in
      let target_repr =
        match inferred_type with
        | T_Int -> R_Int
        | T_Float -> R_Float
        | T_Bool | T_Nil -> R_Bool
        | _ -> R_Value
      in
      let then_code = translate_expr env then_branch target_repr in
      let else_code =
        match else_branch with
        | None ->
            translate_expr env
              (TypedAst.Atom { value = Value.Nil; inferred_type = T_Nil })
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
  | TypedAst.Defun { name; inferred_type = T_Symbol; _ } ->
      sprintf "(Value.Symbol { name = %S })" name
  | TypedAst.Defun { name; inferred_type = other_type; _ } ->
      Printf.eprintf
        "Warning: Defun '%s' has unexpected inferred type %s. \
         Generating symbol.\n"
        name (InferredType.to_string other_type);
      sprintf "(Value.Symbol { name = %S })" name
  | TypedAst.Cond { clauses; inferred_type } ->
      translate_cond env clauses inferred_type
  | TypedAst.Funcall { func; args; inferred_type } ->
      translate_funcall env func args inferred_type

and translate_progn env forms inferred_type =
  match forms with
  | [] ->
      translate_expr env
        (TypedAst.Atom { value = Value.Nil; inferred_type = T_Nil })
        R_Value
  | [ last ] -> translate_node env last
  | _ ->
      let target_repr =
        match inferred_type with
        | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
        | _ -> R_Value
      in
      let translated_forms = List.map forms ~f:(fun expr -> to_value env expr) in
      let last_form = List.last_exn forms in
      let translated_last = translate_expr env last_form target_repr in
      let sequence_code =
        List.drop_last translated_forms
        |> Option.value ~default:[]
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
        let repr, init_code =
          match init_type with
          | T_Int -> (R_Int, to_int !inner_env_ref typed_init)
          | T_Float -> (R_Float, to_float !inner_env_ref typed_init)
          | T_Bool | T_Nil -> (R_Bool, to_bool !inner_env_ref typed_init)
          | _ -> (R_Value, to_value !inner_env_ref typed_init)
        in
        inner_env_ref := add_binding !inner_env_ref elisp_name ocaml_name repr;
        let ocaml_type_annot =
          match repr with
          | R_Int -> ": int ref" | R_Float -> ": float ref"
          | R_Bool -> ": bool ref" | R_Value -> ": Value.t ref"
        in
        sprintf "let %s %s = ref (%s) in" ocaml_name ocaml_type_annot init_code)
  in
  let let_bindings_code = String.concat ~sep:"\n  " let_bindings_code_list in
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
        let repr, init_code =
          match init_type with
          | T_Int -> (R_Int, to_int current_env typed_init)
          | T_Float -> (R_Float, to_float current_env typed_init)
          | T_Bool | T_Nil -> (R_Bool, to_bool current_env typed_init)
          | _ -> (R_Value, to_value current_env typed_init)
        in
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
  let body_code = translate_progn final_env body inferred_type in
  sprintf "(%s\n%s\n)" nested_lets_code (* Already indented *)
    (manual_indent 2 body_code)

and translate_setq env pairs inferred_type =
  let target_repr =
    match inferred_type with
    | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
    | _ -> R_Value
  in
  let assignments_code_list =
    List.map pairs ~f:(fun (sym_name, typed_value) ->
        match lookup_var_info env sym_name with
        | Some { ocaml_name; repr = R_Int } ->
            sprintf "%s := (%s);" ocaml_name (to_int env typed_value)
        | Some { ocaml_name; repr = R_Float } ->
            sprintf "%s := (%s);" ocaml_name (to_float env typed_value)
        | Some { ocaml_name; repr = R_Bool } ->
            sprintf "%s := (%s);" ocaml_name (to_bool env typed_value)
        | Some { ocaml_name; repr = R_Value } ->
            sprintf "%s := (%s);" ocaml_name (to_value env typed_value)
        | None ->
            (* Global variable *)
            sprintf "let (_ : Value.t) = Runtime.set_global_variable %S (%s) \
                     in ();"
              sym_name (to_value env typed_value))
  in
  let return_value_code =
    match List.last pairs with
    | None ->
        translate_expr env
          (TypedAst.Atom { value = Value.Nil; inferred_type = T_Nil })
          target_repr
    | Some (_, v) -> translate_expr env v target_repr
  in
  let assignments_code = String.concat ~sep:"\n    " assignments_code_list in
  if String.is_empty assignments_code then return_value_code
  else sprintf "(let () = \n    %s\n  in\n  %s)" assignments_code
         return_value_code

and translate_lambda env arg_spec body fun_type =
  let open InferredType in
  let inferred_arg_types_list =
    match fun_type with
    | T_Function { arg_types = Some types; _ } -> types
    | _ ->
        Printf.eprintf "Warning: Missing type info for lambda args\n";
        List.map
          (arg_spec.required @ List.map ~f:fst arg_spec.optional
          @ Option.to_list arg_spec.rest)
          ~f:(fun _ -> T_Any)
  in
  let inferred_arg_types = Array.of_list inferred_arg_types_list in
  let inferred_return_type =
    match fun_type with T_Function { return_type; _ } -> return_type | _ -> T_Any
  in
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
    sprintf "\"lambda\" \"Expected %d%s args\"" min_args
      (match max_args_opt with
      | None -> "+"
      | Some m when m = min_args -> ""
      | Some m -> sprintf "-%d" m)
  in
  Buffer.add_string code
    (sprintf
       "    if num_runtime_args < %d %s then Runtime.arity_error %s \
        (string_of_int num_runtime_args);\n"
       min_args
       (match max_args_opt with
       | None -> ""
       | Some m -> sprintf "|| num_runtime_args > %d" m)
       arity_check_msg);
  (* Argument Binding *)
  let inner_env_ref = ref env in
  let arg_bindings_code = Buffer.create 128 in
  let arg_idx = ref 0 in
  (* Required Args *)
  List.iter arg_spec.required ~f:(fun name ->
      let idx = !arg_idx in
      let arg_type = inferred_arg_types.(idx) in
      let ocaml_name = generate_ocaml_var name in
      let runtime_arg = sprintf "(List.nth_exn runtime_args %d)" idx in
      let repr, setup_code =
        match arg_type with
        | T_Int ->
            (R_Int, sprintf "let %s : int ref = ref (%s) in" ocaml_name
                      (unbox_int runtime_arg))
        | T_Float ->
            (R_Float, sprintf "let %s : float ref = ref (%s) in" ocaml_name
                        (unbox_float runtime_arg))
        | T_Bool | T_Nil ->
            (R_Bool, sprintf "let %s : bool ref = ref (%s) in" ocaml_name
                       (unbox_bool runtime_arg))
        | _ ->
            (R_Value, sprintf "let %s : Value.t ref = ref %s in" ocaml_name
                        runtime_arg)
      in
      Buffer.add_string arg_bindings_code (sprintf "    %s\n" setup_code);
      inner_env_ref := add_binding !inner_env_ref name ocaml_name repr;
      incr arg_idx);
  (* Optional Args *)
  List.iter arg_spec.optional ~f:(fun (name, default_val_opt) ->
      let idx = !arg_idx in
      let arg_type = inferred_arg_types.(idx) in
      let ocaml_name = generate_ocaml_var name in
      let default_value_expr =
        match default_val_opt with
        | None -> "Value.Nil"
        | Some dv -> Translate_quote.translate_quoted_data dv
      in
      let runtime_arg_expr = sprintf "(List.nth_exn runtime_args %d)" idx in
      let condition = sprintf "(num_runtime_args > %d)" idx in
      let repr, setup_code =
        match arg_type with
        | T_Int ->
            ( R_Int,
              sprintf
                "let %s : int ref = ref (if %s then %s else %s) in"
                ocaml_name condition (unbox_int runtime_arg_expr)
                (unbox_int default_value_expr) )
        | T_Float ->
            ( R_Float,
              sprintf
                "let %s : float ref = ref (if %s then %s else %s) in"
                ocaml_name condition (unbox_float runtime_arg_expr)
                (unbox_float default_value_expr) )
        | T_Bool | T_Nil ->
            ( R_Bool,
              sprintf
                "let %s : bool ref = ref (if %s then %s else %s) in"
                ocaml_name condition (unbox_bool runtime_arg_expr)
                (unbox_bool default_value_expr) )
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
      Buffer.add_string arg_bindings_code
        (sprintf
           "    let %s : Value.t ref = ref (Value.list_to_value \
            (List.drop runtime_args %d)) in"
           ocaml_name start_idx);
      inner_env_ref := add_binding !inner_env_ref name ocaml_name R_Value);

  Buffer.add_buffer code arg_bindings_code; (* Add bindings setup *)
  (* Translate Body *)
  let body_code = translate_progn !inner_env_ref body inferred_return_type in
  Buffer.add_string code (sprintf "    %s\n))" body_code); (* Add body *)
  Buffer.contents code

and translate_cond env clauses inferred_type =
  let target_repr =
    match inferred_type with
    | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
    | _ -> R_Value
  in
  let rec build cls =
    match cls with
    | [] ->
        translate_expr env
          (TypedAst.Atom { value = Value.Nil; inferred_type = T_Nil })
          target_repr
    | (typed_test, typed_body) :: rest ->
        let test_code = to_bool env typed_test in
        let result_code =
          let body_exprs =
            if List.is_empty typed_body then [ typed_test ] else typed_body
          in
          translate_progn env body_exprs inferred_type
        in
        sprintf "(if %s then begin\n%s\nend else begin\n%s\nend)" test_code
          (manual_indent 4 result_code)
          (build rest)
  in
  build clauses

and translate_funcall env func args inferred_type =
  (* Try optimized builtins first *)
  match func, args with
  | TypedAst.Atom { value = Value.Symbol { name = "+"; _ }; _ }, [ a; b ]
    when [%compare.equal: InferredType.t] inferred_type T_Int ->
      sprintf "(%s + %s)" (to_int env a) (to_int env b)
  | TypedAst.Atom { value = Value.Symbol { name = "-"; _ }; _ }, [ a; b ]
    when [%compare.equal: InferredType.t] inferred_type T_Int ->
      sprintf "(%s - %s)" (to_int env a) (to_int env b)
  | TypedAst.Atom { value = Value.Symbol { name = "*"; _ }; _ }, [ a; b ]
    when [%compare.equal: InferredType.t] inferred_type T_Int ->
      sprintf "(%s * %s)" (to_int env a) (to_int env b)
  | TypedAst.Atom { value = Value.Symbol { name = "/"; _ }; _ }, [ a; b ]
    when [%compare.equal: InferredType.t] inferred_type T_Int ->
      sprintf "(%s / %s)" (to_int env a) (to_int env b) (* Integer division *)
  | TypedAst.Atom { value = Value.Symbol { name = "eq"; _ }; _ }, [ a; b ]
    when [%compare.equal: InferredType.t] inferred_type T_Bool ->
      sprintf "(Runtime.is_truthy (Runtime.builtin_eq [%s; %s]))"
        (to_value env a) (to_value env b) (* Eq needs Value.t *)
  | TypedAst.Atom { value = Value.Symbol { name = "car"; _ }; _ }, [ a ] ->
      let target_repr =
        match inferred_type with
        | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
        | _ -> R_Value
      in
      let arg_code = to_value env a in
      let car_logic_code =
        sprintf
          "(match %s with | Value.Cons { car; _ } -> !car | Value.Nil -> \
           Value.Nil | other -> Runtime.type_error \"car\" \"cons cell or nil\" \
           other)"
          arg_code
      in
      (match target_repr with
      | R_Int -> unbox_int car_logic_code
      | R_Float -> unbox_float car_logic_code
      | R_Bool -> unbox_bool car_logic_code
      | R_Value -> car_logic_code)
  | _ -> (* Default: Generic function call *)
      translate_generic_funcall env func args inferred_type

and translate_generic_funcall env func args inferred_type =
  let func_code = to_value env func in
  let arg_codes_value = List.map args ~f:(to_value env) in
  let call_code =
    sprintf "(Runtime.apply_function (%s) [%s])" func_code
      (String.concat ~sep:"; " arg_codes_value)
  in
  let target_repr =
    match inferred_type with
    | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
    | _ -> R_Value
  in
  match target_repr with
  | R_Int -> unbox_int call_code
  | R_Float -> unbox_float call_code
  | R_Bool -> unbox_bool call_code
  | R_Value -> call_code

(* --- Top Level Translation --- *)
let translate_toplevel texprs final_env_types =
  let definitions = ref [] in
  let run_expressions = ref [] in
  List.iter texprs ~f:(fun texpr ->
      match texpr with
      | TypedAst.Defun _ -> definitions := !definitions @ [ texpr ]
      | _ -> run_expressions := !run_expressions @ [ texpr ]);

  let top_env_map =
    String.Map.of_alist_exn
      (List.map final_env_types ~f:(fun (name, ty) ->
           let ocaml_name = generate_ocaml_var name in
           let repr =
             match ty with
             | T_Int -> R_Int | T_Float -> R_Float | T_Bool | T_Nil -> R_Bool
             | _ -> R_Value
           in
           (name, { ocaml_name; repr })))
  in
  let top_env = top_env_map in

  let def_codes =
    List.filter_map !definitions ~f:(fun def_texpr ->
        match def_texpr with
        | TypedAst.Defun { name; args; body; fun_type; _ } ->
            let entry = Map.find_exn top_env_map name in
            let ocaml_func_name = entry.ocaml_name in
            let lambda_code = translate_lambda top_env args body fun_type in
            Some (sprintf "let %s : Value.t ref = ref (%s)" ocaml_func_name
                    lambda_code)
        | _ -> None)
  in
  let definitions_code =
    match def_codes with
    | [] -> ""
    | hd :: tl -> "let rec " ^ hd ^ (List.map tl ~f:(sprintf "\nand %s") |> String.concat)
  in

  let run_body_code = translate_progn top_env !run_expressions T_Any in

  let env_export_entries =
    Map.to_alist top_env_map
    |> List.filter_map ~f:(fun (elisp_name, entry) ->
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

  sprintf
    "(* Generated by Scaml *)\n\n\
     open! Core\n\
     (* Bring required modules into scope locally *)\n\
     module Value = Scaml__.Value \n\
     module Runtime = Scaml__.Runtime \n\
     module Compiler = Scaml__.Compiler\n\n\
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

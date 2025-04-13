    (* Interpreter.ml - Direct Value.t Evaluator (Refactored) *)

    open! Core
    (* REMOVED: Sexplib related opens *)

    (* Use types/modules from the Scaml library *)
    module Value = Value
    module Runtime = Runtime

    (* --- Evaluation Environment --- *)

    (* Environment is a list of frames (scopes). Each frame maps string names to mutable Value refs. *)
    type eval_env = (string * Value.t ref) list list

    (* Find the frame containing a variable and return its ref *)
    let rec find_var_ref (env : eval_env) (name : string) : Value.t ref option =
      match env with
      | [] -> None (* Reached end of env stack *)
      | frame :: parent_frames ->
          match List.Assoc.find frame name ~equal:String.equal with
          | Some value_ref -> Some value_ref (* Found in current frame *)
          | None -> find_var_ref parent_frames name (* Check parent scope *)

    (* Look up a variable's value. Checks local env first, then Runtime's global env. *)
    let lookup_variable (env : eval_env) (name : string) : Value.t =
      match find_var_ref env name with
      | Some value_ref -> !value_ref (* Found in local/lexical env *)
      | None -> Runtime.lookup_variable name (* Fallback to global lookup *)

    (* Add a new binding to the *first* frame *)
    let add_local_binding (env : eval_env) (name : string) (value : Value.t) : eval_env =
      let new_binding = (name, ref value) in
      match env with
      | [] -> [[new_binding]] (* Create first frame *)
      | frame :: parent_frames -> (new_binding :: frame) :: parent_frames (* Add to existing first frame *)


    (* Add multiple bindings to the first frame *)
    let add_local_bindings (env : eval_env) (bindings : (string * Value.t) list) : eval_env =
     List.fold bindings ~init:env ~f:(fun current_env (name, value) ->
        add_local_binding current_env name value
      )

    (* Set an existing variable. Checks local env first, then sets global. *)
    let set_variable (env : eval_env) (name : string) (value : Value.t) : Value.t =
      match find_var_ref env name with
      | Some value_ref ->
          value_ref := value; (* Set existing local/lexical variable *)
          value
      | None ->
          (* Variable not found locally, assume setting global *)
          Runtime.set_global_variable name value

    (* --- Evaluation Functions --- *)

    (* Helper to safely get arguments from a Value.t list (cdr of a call) *)
    let get_args_list (cdr_val : Value.t) (form_name : string) : Value.t list =
        match Value.value_to_list_opt cdr_val with
        | Some args -> args
        | None -> failwithf "Malformed %s: arguments form an improper list" form_name ()

    (* Mutually recursive evaluation functions defined using 'let rec ... and ...' *)
    let rec eval (env : eval_env) (value : Value.t) : Value.t =
      match value with
      (* Self-evaluating types *)
      | Value.Nil | Value.T | Value.Int _ | Value.Float _ | Value.String _
      | Value.Keyword _ | Value.Char _ | Value.Vector _ | Value.Function _
      | Value.Builtin _ -> value
      (* Symbol: Look it up *)
      | Value.Symbol {name} -> lookup_variable env name
      (* Cons cell: Evaluate as form or function call *)
      | Value.Cons { car; cdr } ->
          let head_val = eval env car in (* Evaluate the head *)
          eval_dispatch env head_val cdr (* Dispatch based on head and cdr *)

    and eval_dispatch (env : eval_env) (head_val : Value.t) (cdr_val : Value.t) : Value.t =
        match head_val with
        (* --- Special Forms --- *)
        | Value.Symbol {name="quote"} ->
            (match Value.value_to_list_opt cdr_val with
             | Some [data] -> data (* Quote prevents evaluation of the argument *)
             | _ -> failwith "Malformed quote: expected exactly one argument")

        | Value.Symbol {name="if"} ->
            (match get_args_list cdr_val "if" with
             | [c; t] -> if Value.is_truthy (eval env c) then eval env t else Value.Nil
             | [c; t; e] -> if Value.is_truthy (eval env c) then eval env t else eval env e
             | _ -> failwith "Malformed if: expected 2 or 3 arguments")

        | Value.Symbol {name="progn"} -> eval_progn env (get_args_list cdr_val "progn")

        | Value.Symbol {name="let"} ->
            (match get_args_list cdr_val "let" with
             | bindings_val :: body_forms when Value.(match bindings_val with Cons _ | Nil -> true | _ -> false) ->
                 eval_let env bindings_val body_forms
             | _ -> failwith "Malformed let: expected bindings list and body")

        | Value.Symbol {name="let*"} ->
             (match get_args_list cdr_val "let*" with
              | bindings_val :: body_forms when Value.(match bindings_val with Cons _ | Nil -> true | _ -> false) ->
                  eval_let_star env bindings_val body_forms
              | _ -> failwith "Malformed let*: expected bindings list and body")

        | Value.Symbol {name="setq"} -> eval_setq env (get_args_list cdr_val "setq")

        | Value.Symbol {name="lambda"} ->
            (match get_args_list cdr_val "lambda" with
             | arg_list_val :: body_forms -> eval_lambda env arg_list_val body_forms
             | _ -> failwith "Malformed lambda: expected arg list and body")

        | Value.Symbol {name="defun"} ->
            (match get_args_list cdr_val "defun" with
             | Value.Symbol {name} :: arg_list_val :: body_forms -> eval_defun env name arg_list_val body_forms
             | _ -> failwith "Malformed defun: expected name symbol, arg list, and body")

        | Value.Symbol {name="cond"} -> eval_cond env (get_args_list cdr_val "cond")

        (* --- Default: Function Call --- *)
        | (Value.Function _ | Value.Builtin _) as func_to_call ->
            let args = get_args_list cdr_val "function call" in
            (* Evaluate arguments *before* applying the function *)
            let evaluated_args = List.map args ~f:(eval env) in
            Runtime.apply_function func_to_call evaluated_args

        (* --- Error: Trying to call a non-callable --- *)
        | other_head ->
            failwithf "Invalid function call: Cannot apply %s" (!Value.to_string other_head) ()


    and eval_progn (env : eval_env) (forms : Value.t list) : Value.t =
      match forms with
      | [] -> Value.Nil
      | [last] -> eval env last
      | form :: rest ->
          let (_ : Value.t) = eval env form in (* Evaluate for side effects *)
          eval_progn env rest (* Evaluate the rest *)

    and eval_let (env : eval_env) (bindings_val : Value.t) (body_forms : Value.t list) : Value.t =
      let bindings_list = match Value.value_to_list_opt bindings_val with
        | Some l -> l
        | None -> failwith "Malformed let: bindings must be a proper list"
      in
      (* 1. Evaluate all initializers in the *outer* environment *)
      let evaluated_bindings_with_refs = List.map bindings_list ~f:(fun b_val ->
          match b_val with
          | Value.Symbol {name} -> (name, ref Value.Nil) (* Symbol only defaults to nil *)
          | Value.Cons {car = Value.Symbol {name=n};
                        cdr = init_list_val} ->
              (match Value.value_to_list_opt init_list_val with
               | Some [init_form] -> let value = eval env init_form in (n, ref value)
               | _ -> failwithf "Malformed let binding (init list): %s" (!Value.to_string b_val) ())
          | _ -> failwithf "Malformed let binding (structure): %s" (!Value.to_string b_val) ()
        ) in
      (* 2. Create the inner environment by adding all bindings to a *new* frame *)
      let inner_env = evaluated_bindings_with_refs :: env in (* Push new frame *)
      (* 3. Evaluate the body in the inner environment *)
      eval_progn inner_env body_forms

    and eval_let_star (env : eval_env) (bindings_val : Value.t) (body_forms : Value.t list) : Value.t =
       let bindings_list = match Value.value_to_list_opt bindings_val with
        | Some l -> l
        | None -> failwith "Malformed let*: bindings must be a proper list"
      in
      (* Evaluate bindings sequentially, updating the environment *)
      (* Start with a new empty frame for the let* bindings on top of the original env *)
      let env_with_let_star_frame = [] :: env in
      let final_inner_env = List.fold bindings_list ~init:env_with_let_star_frame ~f:(fun current_env b_val ->
          let name, init_form = match b_val with
            | Value.Symbol {name=n} -> (n, Value.Nil) (* Symbol only defaults to nil *)
            (* ***** CORRECT PATTERN HERE ***** *)
            | Value.Cons {car = Value.Symbol {name=n}; cdr = init_list_val} ->
                (match Value.value_to_list_opt init_list_val with
                | Some [i] -> (n, i)
                | _ -> failwithf "Malformed let* binding (init list): %s" (!Value.to_string b_val) ())
            | _ -> failwithf "Malformed let* binding (structure): %s" (!Value.to_string b_val) ()
          in
          (* Evaluate initializer in the *current* sequential environment *)
          let value = eval current_env init_form in
          (* Add the binding (as a ref) for the *next* iteration to the *current* frame *)
          add_local_binding current_env name value (* add_local_binding adds to the first frame *)
        ) in
      (* Evaluate body in the final environment *)
      eval_progn final_inner_env body_forms

    and eval_setq (env : eval_env) (pairs : Value.t list) : Value.t =
      if List.length pairs % 2 <> 0 then
        failwith "Malformed setq: must have an even number of arguments (var value pairs)";
      let rec process_pairs current_val pairs_left =
        match pairs_left with
        | [] -> current_val (* Return the last value assigned *)
        | Value.Symbol {name=var_name} :: value_form :: rest ->
            let value = eval env value_form in
            let (_ : Value.t) = set_variable env var_name value in (* Perform assignment *)
            process_pairs value rest (* Recurse with the assigned value *)
        | not_symbol :: _ -> failwithf "Malformed setq: expected symbol, got %s" (!Value.to_string not_symbol) ()
      in
      process_pairs Value.Nil pairs (* Start with Nil, process pairs *)


    and eval_lambda (outer_env : eval_env) (arg_list_val : Value.t) (body_forms : Value.t list) : Value.t =
      (* Parse the argument list value - requires a simple parser or assumptions *)
      (* Simplified: Assume just a list of required symbols for now *)
      let arg_names = match Value.value_to_list_opt arg_list_val with
        | Some name_vals -> List.map name_vals ~f:(function Value.Symbol {name} -> name | _ -> failwith "Invalid lambda arg list: contains non-symbols")
        | None -> failwith "Lambda arg list must be a proper list"
      in
      (* Create the closure: captures the outer environment *)
      Value.Function (fun arg_values ->
        (* Check arity *)
        if List.length arg_names <> List.length arg_values then
          Runtime.arity_error "lambda" (sprintf "expected %d args, got %d" (List.length arg_names) (List.length arg_values));
        (* Create the evaluation environment for the function body *)
        let bindings = List.zip_exn arg_names arg_values in
        (* Create the new frame containing args bound to refs of values *)
        let new_frame : (string * Value.t ref) list =
            List.map bindings ~f:(fun (name, value) -> (name, ref value))
        in
        (* Prepend the new frame to the captured outer environment *)
        let body_env : eval_env = new_frame :: outer_env
        in
        (* Evaluate the body in the new environment *)
        eval_progn body_env body_forms
      )

    and eval_defun (env : eval_env) (name : string) (arg_list_val : Value.t) (body_forms : Value.t list) : Value.t =
      (* 1. Create the function value (closure) using eval_lambda *)
      (* The closure needs to capture the *current* env for lexical scope *)
      let fun_value = eval_lambda env arg_list_val body_forms in
      (* 2. Register it in the global environment *)
      Runtime.register_global name fun_value;
      (* 3. Defun returns the function name as a symbol *)
      Value.Symbol { name = name }

    and eval_cond (env : eval_env) (clauses : Value.t list) : Value.t =
      match clauses with
      | [] -> Value.Nil (* No clauses, result is nil *)
      | clause_val :: rest_clauses ->
          match clause_val with
          | Value.Cons { car=test_form; cdr=body_list_val } ->
              let test_result = eval env test_form in
              if Value.is_truthy test_result then
                (* Condition is true *)
                match Value.value_to_list_opt body_list_val with
                | Some [] -> test_result (* No body, result is the test result *)
                | Some body_forms -> eval_progn env body_forms (* Evaluate body *)
                | None -> failwith "Malformed cond clause: body is improper list"
              else
                (* Condition is false, evaluate remaining clauses *)
                eval_cond env rest_clauses
          | Value.Nil -> failwith "Malformed cond clause: found nil" (* Should not happen with list input *)
          | _ -> failwith "Malformed cond clause: must be a list (cons cell)"


    (* --- Top-Level Evaluation --- *)

    (** Evaluate a list of Value.t forms sequentially, returning the last result.
        Uses the global environment implicitly via lookup_variable/set_variable. *)
    let eval_toplevel (values : Value.t list) : Value.t =
      (* Start with an empty local environment (only globals from Runtime) *)
      let initial_env : eval_env = [] in
      eval_progn initial_env values

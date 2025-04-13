(* Interpreter.ml - Direct Value.t Evaluator (Refactored) *)

open! Core

(* Use types/modules from the Scaml library *)
module Value = Value
module Runtime = Runtime

(* --- Evaluation Environment --- *)

(* Environment uses refs for bindings to allow mutation via setq *)
type eval_env = (string * Value.t ref) list list

(* Find the ref of a variable in the lexical environment *)
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
  | Some value_ref -> !value_ref (* Dereference local binding *)
  | None -> Runtime.lookup_variable name (* Fallback to global lookup *)

(* Add a new binding (as a ref) to the *first* frame *)
let add_local_binding (env : eval_env) (name : string) (value : Value.t) : eval_env =
  let new_binding = (name, ref value) in (* Store value in a ref *)
  match env with
  | [] -> [[new_binding]] (* Create first frame *)
  | frame :: parent_frames -> (new_binding :: frame) :: parent_frames (* Add to existing first frame *)


(* Add multiple bindings (as refs) to the first frame *)
let add_local_bindings (env : eval_env) (bindings : (string * Value.t) list) : eval_env =
 List.fold bindings ~init:env ~f:(fun current_env (name, value) ->
    add_local_binding current_env name value
  )

(* Set an existing variable. Checks local env first (uses :=), then sets global. *)
let set_variable (env : eval_env) (name : string) (value : Value.t) : Value.t =
  match find_var_ref env name with
  | Some value_ref ->
      value_ref := value; (* Assign to existing local ref *)
      value
  | None ->
      (* Variable not found locally, assume setting global *)
      Runtime.set_global_variable name value

(* --- Evaluation Functions --- *)

(* Helper to safely get arguments from a Value.t list (cdr of a call) *)
let get_args_list (cdr_val : Value.t) (form_name : string) : Value.t list =
    match Value.value_to_list_opt cdr_val with (* Assumes value_to_list_opt handles mutable fields *)
    | Some args -> args
    | None -> failwithf "Malformed %s: arguments form an improper list" form_name ()

(* Forward declaration for mutual recursion *)
let rec eval (env : eval_env) (value : Value.t) : Value.t =
  eval_internal env value

(* Main eval function *)
and eval_internal (env : eval_env) (value : Value.t) : Value.t =
  match value with
  (* Self-evaluating types *)
  | Value.Nil | Value.T | Value.Int _ | Value.Float _ | Value.String _
  | Value.Keyword _ | Value.Char _ | Value.Vector _ | Value.Function _
  | Value.Builtin _ -> value

  (* Symbol: Look it up *)
  | Value.Symbol {name} -> lookup_variable env name

  (* Cons cell: Check for special forms first, then function call *)
  | Value.Cons { car; cdr } -> begin (* car and cdr are Value.t (direct fields) *)
      match car with (* Check unevaluated car *)
      (* --- Special Forms --- *)
      | Value.Symbol {name="quote"} ->
          (match Value.value_to_list_opt cdr with (* Use direct cdr *)
           | Some [data] -> data (* Return data unevaluated *)
           | _ -> failwith "Malformed quote: expected exactly one argument")

      | Value.Symbol {name="quasiquote"} ->
          (match Value.value_to_list_opt cdr with
           | Some [template] -> eval_quasiquote_internal env template
           | _ -> failwith "Malformed quasiquote: expected exactly one argument")

      | Value.Symbol {name="if"} ->
          (match get_args_list cdr "if" with (* Use direct cdr *)
           | [c; t] -> if Value.is_truthy (eval env c) then eval env t else Value.Nil
           | [c; t; e] -> if Value.is_truthy (eval env c) then eval env t else eval env e
           | _ -> failwith "Malformed if: expected 2 or 3 arguments")

      | Value.Symbol {name="progn"} -> eval_progn env (get_args_list cdr "progn") (* Use direct cdr *)

      | Value.Symbol {name="let"} ->
          (match get_args_list cdr "let" with (* Use direct cdr *)
           | bindings_val :: body_forms when Value.(match bindings_val with Cons _ | Nil -> true | _ -> false) ->
               eval_let env bindings_val body_forms
           | _ -> failwith "Malformed let: expected bindings list and body")

      | Value.Symbol {name="let*"} ->
           (match get_args_list cdr "let*" with (* Use direct cdr *)
            | bindings_val :: body_forms when Value.(match bindings_val with Cons _ | Nil -> true | _ -> false) ->
                eval_let_star env bindings_val body_forms
            | _ -> failwith "Malformed let*: expected bindings list and body")

      | Value.Symbol {name="setq"} -> eval_setq env (get_args_list cdr "setq") (* Use direct cdr *)

      | Value.Symbol {name="lambda"} ->
          (match get_args_list cdr "lambda" with (* Use direct cdr *)
           | arg_list_val :: body_forms -> eval_lambda env arg_list_val body_forms
           | _ -> failwith "Malformed lambda: expected arg list and body")

      | Value.Symbol {name="defun"} ->
          (match get_args_list cdr "defun" with (* Use direct cdr *)
           | Value.Symbol {name} :: arg_list_val :: body_forms -> eval_defun env name arg_list_val body_forms
           | _ -> failwith "Malformed defun: expected name symbol, arg list, and body")

      | Value.Symbol {name="cond"} -> eval_cond env (get_args_list cdr "cond") (* Use direct cdr *)

      (* --- Default: Function Call --- *)
      | _ -> (* Not a special form symbol, evaluate car to get function *)
          let func_to_call = eval env car in (* Evaluate the actual car *)
          let args = get_args_list cdr "function call" in (* Use direct cdr *)
          (* Evaluate arguments *before* applying the function *)
          let evaluated_args = List.map args ~f:(eval env) in
          (match func_to_call with
            | Value.Function _ | Value.Builtin _ ->
                Runtime.apply_function func_to_call evaluated_args
            | other_head ->
                failwithf "Invalid function call: Cannot apply %s" (!Value.to_string other_head) ()
          )
     end (* End match car *)

(* --- Quasiquote Helper --- *)
(* ***** REVISED QUASIQUOTE LOGIC ***** *)
and eval_quasiquote_internal (env : eval_env) (template : Value.t) : Value.t =
  match template with
  (* Unquote evaluates its argument *)
  | Value.Cons { car = Value.Symbol {name="unquote"}; cdr = rest } ->
      (match Value.value_to_list_opt rest with
       | Some [expr_to_eval] -> eval env expr_to_eval
       | _ -> failwith "Malformed unquote: expected exactly one argument")

  (* Unquote-splicing is invalid unless inside a list context (handled below) *)
  | Value.Cons { car = Value.Symbol {name="unquote-splicing"}; cdr = _} ->
      failwith "Invalid unquote-splicing: ,@ must appear directly within a list"

  (* Recursively build lists *)
  | Value.Cons { car; cdr } -> begin
      match car with
      (* Handle splicing at the start of a list *)
      | Value.Cons { car = Value.Symbol {name="unquote-splicing"}; cdr = splice_rest } ->
          let list_to_splice =
            match Value.value_to_list_opt splice_rest with
            | Some [expr_to_eval] -> eval env expr_to_eval
            | _ -> failwith "Malformed unquote-splicing: expected exactly one argument"
          in
          let elements_to_splice = match Value.value_to_list_opt list_to_splice with
            | Some elements -> elements
            | None -> failwith "unquote-splicing: expression did not evaluate to a proper list"
          in
          (* Recursively process the rest of the template list *)
          let processed_cdr = eval_quasiquote_internal env cdr in
          (* Append the spliced elements to the processed rest *)
          Value.list_append elements_to_splice processed_cdr (* Assumes list_append exists *)

      (* Normal cons cell processing *)
      | _ ->
          let processed_car = eval_quasiquote_internal env car in
          let processed_cdr = eval_quasiquote_internal env cdr in
          (* Optimization: if car and cdr are physically identical to originals, *)
          (* reuse the original template cons cell? Only if immutable. *)
          (* Since using mutable cells, always create a new one. *)
          Value.Cons { car = processed_car; cdr = processed_cdr }
    end

  (* Recursively build vectors *)
  | Value.Vector arr ->
      let new_arr = Array.map arr ~f:(eval_quasiquote_internal env) in
      Value.Vector new_arr

  (* Atoms evaluate to themselves *)
  | other_atom -> other_atom

(* Removed eval_quasiquote_list helper - logic merged above *)

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
  let evaluated_bindings = List.map bindings_list ~f:(fun b_val ->
      match b_val with
      | Value.Symbol {name} -> (name, Value.Nil) (* Symbol only defaults to nil *)
      (* Match cons cell with direct fields *)
      | Value.Cons {car = Value.Symbol {name=n}; cdr = init_list_val} ->
          (match Value.value_to_list_opt init_list_val with
           | Some [init_form] -> let value = eval env init_form in (n, value)
           | _ -> failwithf "Malformed let binding (init list): %s" (!Value.to_string b_val) ())
      | _ -> failwithf "Malformed let binding (structure): %s" (!Value.to_string b_val) ()
    ) in
  (* 2. Create the inner environment by adding all bindings (as refs) to a *new* frame *)
  let inner_env = add_local_bindings env evaluated_bindings in (* Creates refs *)
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
        (* Match cons cell with direct fields *)
        | Value.Cons {car = Value.Symbol {name=n}; cdr = init_list_val} ->
            (match Value.value_to_list_opt init_list_val with
            | Some [i] -> (n, i)
            | _ -> failwithf "Malformed let* binding (init list): %s" (!Value.to_string b_val) ())
        | _ -> failwithf "Malformed let* binding (structure): %s" (!Value.to_string b_val) ()
      in
      (* Evaluate initializer in the *current* sequential environment *)
      let value = eval current_env init_form in
      (* Add the binding (as a ref) for the *next* iteration to the *current* frame *)
      add_local_binding current_env name value (* Creates ref *)
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
        (* Perform assignment using set_variable (handles local refs / globals) *)
        let (_ : Value.t) = set_variable env var_name value in
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
        List.map bindings ~f:(fun (name, value) -> (name, ref value)) (* Create refs *)
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
      (* Match cons cell with direct fields *)
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


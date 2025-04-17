(* lib/Interpreter.ml *)
(* Interpreter.ml - Direct Value.t Evaluator (Refactored for Lisp-2) *)

open! Core

(* Use types/modules from the Scaml library *)
module Value = Value
module Runtime = Runtime

(* --- Evaluation Environments --- *)

(* Environment for variables (uses refs for mutation) *)
type eval_env = (string * Value.t ref) list list

(* Environment for local function definitions (e.g., flet/labels - not implemented yet) *)
(* Currently only used to pass down for lambda capture *)
type funs_env = (string * Value.t) list list (* Functions themselves are immutable values *)


(* --- Variable Lookup --- *)

let rec find_var_ref (env : eval_env) (name : string) : Value.t ref option =
  match env with
  | [] -> None
  | frame :: parent_frames ->
      match List.Assoc.find frame name ~equal:String.equal with
      | Some value_ref -> Some value_ref
      | None -> find_var_ref parent_frames name

let lookup_variable (env : eval_env) (name : string) : Value.t =
  match find_var_ref env name with
  | Some value_ref -> !value_ref
  | None -> Runtime.lookup_variable name (* Fallback to global lookup *)


(* --- Function Lookup (Lisp-2) --- *)

let rec find_fun_def (fenv : funs_env) (name : string) : Value.t option =
  match fenv with
  | [] -> None (* Reached end of local function env stack *)
  | frame :: parent_frames ->
      match List.Assoc.find frame name ~equal:String.equal with
      | Some func_val -> Some func_val (* Found in current frame *)
      | None -> find_fun_def parent_frames name (* Check parent scope *)

(* Look up a function definition. Checks local funs_env first, then Runtime's global env. *)
let lookup_function (fenv : funs_env) (name : string) : Value.t =
    match find_fun_def fenv name with
    | Some func_val -> func_val (* Found local function (flet/labels) *)
    | None ->
        (* Not found locally, try global environment (which holds variables AND functions) *)
        let global_val = Runtime.lookup_variable name in (* Uses the standard global lookup *)
        match global_val with
        | Value.Function _ | Value.Builtin _ -> global_val (* Found global function *)
        (* If the global variable holds a non-function, it's an error for a function call *)
        | _ -> Runtime.runtime_error "lookup_function" (sprintf "Symbol '%s' names a variable which is not defined as a function" name)


(* --- Environment Manipulation --- *)
(* (Variable Environment Helpers - Unchanged) *)
let add_local_binding (env : eval_env) (name : string) (value : Value.t) : eval_env =
  let new_binding = (name, ref value) in
  match env with
  | [] -> [[new_binding]]
  | frame :: parent_frames -> (new_binding :: frame) :: parent_frames

let add_local_bindings (env : eval_env) (bindings : (string * Value.t) list) : eval_env =
 List.fold bindings ~init:env ~f:(fun current_env (name, value) ->
    add_local_binding current_env name value
  )

let set_variable (env : eval_env) (name : string) (value : Value.t) : Value.t =
  match find_var_ref env name with
  | Some value_ref ->
      value_ref := value; value
  | None -> Runtime.set_global_variable name value

(* --- Evaluation Functions --- *)

let get_args_list (cdr_val : Value.t) (form_name : string) : Value.t list =
    match Value.value_to_list_opt cdr_val with
    | Some args -> args
    | None -> failwithf "Malformed %s: arguments form an improper list" form_name ()

(* Forward declaration - ADDED funs_env parameter *)
let rec eval (env : eval_env) (fenv : funs_env) (value : Value.t) : Value.t =
  eval_internal env fenv value

(* Main eval function - ADDED funs_env parameter *)
and eval_internal (env : eval_env) (fenv : funs_env) (value : Value.t) : Value.t =
  match value with
  (* Self-evaluating types *)
  | Value.Nil | Value.T | Value.Int _ | Value.Float _ | Value.String _
  | Value.Keyword _ | Value.Char _ | Value.Vector _ | Value.Function _
  | Value.Builtin _ -> value

  (* Symbol: Look it up (variable namespace) *)
  | Value.Symbol {name} -> lookup_variable env name

  (* Cons cell: Check for special forms first, then function call *)
  | Value.Cons { car; cdr } -> begin
      match car with
      (* --- Special Forms (pass fenv down) --- *)
      | Value.Symbol {name="quote"} ->
          (match Value.value_to_list_opt cdr with
           | Some [data] -> data
           | _ -> failwith "Malformed quote: expected exactly one argument")

      | Value.Symbol {name="quasiquote"} ->
          (match Value.value_to_list_opt cdr with
           | Some [template] -> eval_quasiquote_internal env fenv template (* Pass fenv *)
           | _ -> failwith "Malformed quasiquote: expected exactly one argument")

      | Value.Symbol {name="if"} ->
          (match get_args_list cdr "if" with
           | [c; t] -> if Value.is_truthy (eval env fenv c) then eval env fenv t else Value.Nil (* Pass fenv *)
           | [c; t; e] -> if Value.is_truthy (eval env fenv c) then eval env fenv t else eval env fenv e (* Pass fenv *)
           | _ -> failwith "Malformed if: expected 2 or 3 arguments")

      | Value.Symbol {name="progn"} -> eval_progn env fenv (get_args_list cdr "progn") (* Pass fenv *)

      | Value.Symbol {name="let"} ->
          (match get_args_list cdr "let" with
           | bindings_val :: body_forms when Value.(match bindings_val with Cons _ | Nil -> true | _ -> false) ->
               eval_let env fenv bindings_val body_forms (* Pass fenv *)
           | _ -> failwith "Malformed let: expected bindings list and body")

      | Value.Symbol {name="let*"} ->
          (match get_args_list cdr "let*" with
           | bindings_val :: body_forms when Value.(match bindings_val with Cons _ | Nil -> true | _ -> false) ->
               eval_let_star env fenv bindings_val body_forms (* Pass fenv *)
           | _ -> failwith "Malformed let*: expected bindings list and body")

      | Value.Symbol {name="setq"} -> eval_setq env fenv (get_args_list cdr "setq") (* Pass fenv *)

      | Value.Symbol {name="lambda"} ->
          (match get_args_list cdr "lambda" with
           | arg_list_val :: body_forms -> eval_lambda env fenv arg_list_val body_forms (* Pass fenv *)
           | _ -> failwith "Malformed lambda: expected arg list and body")

      | Value.Symbol {name="defun"} ->
          (match get_args_list cdr "defun" with
           | Value.Symbol {name} :: arg_list_val :: body_forms -> eval_defun env fenv name arg_list_val body_forms (* Pass fenv *)
           | _ -> failwith "Malformed defun: expected name symbol, arg list, and body")

      | Value.Symbol {name="cond"} -> eval_cond env fenv (get_args_list cdr "cond") (* Pass fenv *)

      (* --- Default: Lisp-2 Function Call --- *)
      | Value.Symbol { name = fun_name } -> (* car is a symbol, potential function name *)
          (* Lisp-2: Lookup function first *)
          let func_to_call = lookup_function fenv fun_name in
          (* THEN evaluate arguments *)
          let args = get_args_list cdr "function call" in
          let evaluated_args = List.map args ~f:(eval env fenv) in (* Eval args using current envs *)
          (* Apply the function *)
          Runtime.apply_function func_to_call evaluated_args
     | _ -> (* car is NOT a symbol (e.g. ((lambda (x) x) 1) ) *)
          (* Evaluate the car expression itself *)
          let func_to_call = eval env fenv car in
          (* Check if the result is actually a function (like a lambda value) *)
          (match func_to_call with
             | Value.Function _ | Value.Builtin _ ->
                 (* Evaluate arguments *)
                 let args = get_args_list cdr "function call" in
                 let evaluated_args = List.map args ~f:(eval env fenv) in
                 (* Apply the evaluated function *)
                 Runtime.apply_function func_to_call evaluated_args
             (* If the evaluated car is NOT a function, it's an error in Elisp *)
             | other_head ->
                 (* Elisp signals invalid-function here *)
                 failwithf "Invalid function: %s" (!Value.to_string other_head) ()
          )
      end (* End match car *)


(* --- Quasiquote Helper (pass fenv down) --- *)
and eval_quasiquote_internal (env : eval_env) (fenv : funs_env) (template : Value.t) : Value.t =
  match template with
  | Value.Cons { car = Value.Symbol {name="unquote"}; cdr = rest } ->
      (match Value.value_to_list_opt rest with
       | Some [expr_to_eval] -> eval env fenv expr_to_eval (* Pass fenv *)
       | _ -> failwith "Malformed unquote: expected exactly one argument")
  | Value.Cons { car = Value.Symbol {name="unquote-splicing"}; cdr = _} ->
      failwith "Invalid unquote-splicing: ,@ must appear directly within a list"
  | Value.Cons { car; cdr } -> begin
      match car with
      | Value.Cons { car = Value.Symbol {name="unquote-splicing"}; cdr = splice_rest } ->
          let list_to_splice =
            match Value.value_to_list_opt splice_rest with
            | Some [expr_to_eval] -> eval env fenv expr_to_eval (* Pass fenv *)
            | _ -> failwith "Malformed unquote-splicing: expected exactly one argument"
          in
          let elements_to_splice = match Value.value_to_list_opt list_to_splice with
            | Some elements -> elements | None -> failwith "unquote-splicing: did not evaluate to list"
          in
          let processed_cdr = eval_quasiquote_internal env fenv cdr in (* Pass fenv *)
          Value.list_append elements_to_splice processed_cdr
      | _ ->
          let processed_car = eval_quasiquote_internal env fenv car in (* Pass fenv *)
          let processed_cdr = eval_quasiquote_internal env fenv cdr in (* Pass fenv *)
          Value.Cons { car = processed_car; cdr = processed_cdr }
    end
  | Value.Vector arr ->
      Value.Vector (Array.map arr ~f:(eval_quasiquote_internal env fenv)) (* Pass fenv *)
  | other_atom -> other_atom


and eval_progn (env : eval_env) (fenv : funs_env) (forms : Value.t list) : Value.t =
  match forms with
  | [] -> Value.Nil
  | [last] -> eval env fenv last (* Pass fenv *)
  | form :: rest ->
      let (_ : Value.t) = eval env fenv form in (* Pass fenv *)
      eval_progn env fenv rest (* Pass fenv *)

and eval_let (env : eval_env) (fenv : funs_env) (bindings_val : Value.t) (body_forms : Value.t list) : Value.t =
  let bindings_list = match Value.value_to_list_opt bindings_val with
    | Some l -> l | None -> failwith "Malformed let: bindings must be a proper list"
  in
  (* Evaluate initializers in the outer environment *)
  let evaluated_bindings = List.map bindings_list ~f:(fun b_val ->
      match b_val with
      | Value.Symbol {name} -> (name, Value.Nil)
      | Value.Cons {car = Value.Symbol {name=n}; cdr = init_list_val} ->
          (match Value.value_to_list_opt init_list_val with
           | Some [init_form] -> let value = eval env fenv init_form in (n, value) (* Pass fenv *)
           | _ -> failwithf "Malformed let binding (init list): %s" (!Value.to_string b_val) ())
      | _ -> failwithf "Malformed let binding (structure): %s" (!Value.to_string b_val) ()
    ) in
  (* Create the inner *variable* environment *)
  let inner_env : eval_env = add_local_bindings ([] :: env) evaluated_bindings in
  (* Evaluate the body in the inner variable env, outer function env *)
  eval_progn inner_env fenv body_forms (* Use inner_env, outer fenv *)

and eval_let_star (env : eval_env) (fenv : funs_env) (bindings_val : Value.t) (body_forms : Value.t list) : Value.t =
   let bindings_list = match Value.value_to_list_opt bindings_val with
    | Some l -> l | None -> failwith "Malformed let*: bindings must be a proper list"
   in
   (* Evaluate bindings sequentially, updating *variable* environment *)
   let env_with_let_star_frame = [] :: env in
   let final_inner_env = List.fold bindings_list ~init:env_with_let_star_frame ~f:(fun current_env b_val ->
      let name, init_form = match b_val with
        | Value.Symbol {name=n} -> (n, Value.Nil)
        | Value.Cons {car = Value.Symbol {name=n}; cdr = init_list_val} ->
            (match Value.value_to_list_opt init_list_val with
            | Some [i] -> (n, i)
            | _ -> failwithf "Malformed let* binding (init list): %s" (!Value.to_string b_val) ())
        | _ -> failwithf "Malformed let* binding (structure): %s" (!Value.to_string b_val) ()
      in
      (* Evaluate initializer in the *current* sequential env, outer fenv *)
      let value = eval current_env fenv init_form in (* Pass fenv *)
      (* Add binding to the current variable frame *)
      add_local_binding current_env name value
    ) in
  (* Evaluate body in the final variable env, outer function env *)
  eval_progn final_inner_env fenv body_forms (* Use final_inner_env, outer fenv *)

and eval_setq (env : eval_env) (fenv : funs_env) (pairs : Value.t list) : Value.t =
  if List.length pairs % 2 <> 0 then
    failwith "Malformed setq: must have an even number of arguments (var value pairs)";
  let rec process_pairs current_val pairs_left =
    match pairs_left with
    | [] -> current_val
    | Value.Symbol {name=var_name} :: value_form :: rest ->
        let value = eval env fenv value_form in (* Pass fenv *)
        let (_ : Value.t) = set_variable env var_name value in
        process_pairs value rest
    | not_symbol :: _ -> failwithf "Setq expected symbol, got %s" (!Value.to_string not_symbol) ()
  in
  process_pairs Value.Nil pairs

(* Lambda captures *both* environments *)
and eval_lambda (outer_env : eval_env) (outer_funs_env : funs_env) (arg_list_val : Value.t) (body_forms : Value.t list) : Value.t =
  let arg_names = match Value.value_to_list_opt arg_list_val with
    | Some name_vals -> List.map name_vals ~f:(function Value.Symbol {name} -> name | _ -> failwith "Invalid lambda arg list")
    | None -> failwith "Lambda arg list must be a proper list"
  in
  (* Create closure: captures *both* outer environments *)
  Value.Function (fun arg_values ->
    if List.length arg_names <> List.length arg_values then
      Runtime.arity_error "lambda" (sprintf "expected %d args, got %d" (List.length arg_names) (List.length arg_values));
    let bindings = List.zip_exn arg_names arg_values in
    (* Create the new variable frame *)
    let new_var_frame : (string * Value.t ref) list =
        List.map bindings ~f:(fun (name, value) -> (name, ref value))
    in
    (* Prepend the new frame to the captured outer variable environment *)
    let body_env : eval_env = new_var_frame :: outer_env
    in
    (* Evaluate the body in the new variable env and the captured function env *)
    eval_progn body_env outer_funs_env body_forms (* Use body_env and captured outer_funs_env *)
  )

(* Defun uses eval_lambda which captures both envs *)
and eval_defun (env : eval_env) (fenv : funs_env) (name : string) (arg_list_val : Value.t) (body_forms : Value.t list) : Value.t =
  (* Create the function value (closure) capturing current envs *)
  let fun_value = eval_lambda env fenv arg_list_val body_forms in
  (* Register it globally (available in both var and fun namespaces via lookup) *)
  Runtime.register_global name fun_value;
  (* Defun returns the function name as a symbol *)
  Value.Symbol { name = name }

and eval_cond (env : eval_env) (fenv : funs_env) (clauses : Value.t list) : Value.t =
  match clauses with
  | [] -> Value.Nil
  | clause_val :: rest_clauses ->
      match clause_val with
      | Value.Cons { car=test_form; cdr=body_list_val } ->
          let test_result = eval env fenv test_form in (* Pass fenv *)
          if Value.is_truthy test_result then
            match Value.value_to_list_opt body_list_val with
            | Some [] -> test_result
            | Some body_forms -> eval_progn env fenv body_forms (* Pass fenv *)
            | None -> failwith "Malformed cond clause: body is improper list"
          else
            eval_cond env fenv rest_clauses (* Pass fenv *)
      | Value.Nil -> failwith "Malformed cond clause: found nil"
      | _ -> failwith "Malformed cond clause: must be a list"


(* --- Top-Level Evaluation --- *)
let eval_toplevel (values : Value.t list) : Value.t =
  (* Start with empty local environments *)
  let initial_env : eval_env = [] in
  let initial_funs_env : funs_env = [] in
  eval_progn initial_env initial_funs_env values (* Start evaluation *)
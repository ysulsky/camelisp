(* Interpreter.ml - Direct S-expression Evaluator *)

open! Core
(* open! Sexplib.Std - Not needed here directly *)

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

(* Mutually recursive evaluation functions defined using 'let rec ... and ...' *)
let rec eval (env : eval_env) (sexp : Sexp.t) : Value.t =
  match sexp with
  (* Atoms *)
  | Sexp.Atom s ->
      (try Value.Int (Int.of_string s) with _ -> (* Catch any exception *)
      try Value.Float (Float.of_string s) with _ -> (* Catch any exception *)
      (* Check constants/keywords *after* attempting number parsing *)
      if String.equal s "nil" then Value.Nil
      else if String.equal s "t" then Value.T
      else if String.is_prefix s ~prefix:":" then Value.Keyword (String.drop_prefix s 1)
      (* Assume symbol otherwise, look it up *)
      else lookup_variable env s)
  (* Empty list is nil *)
  | Sexp.List [] -> Value.Nil
  (* Special forms & Function calls *)
  | Sexp.List (head :: args) ->
      begin match head with
      | Sexp.Atom "quote" ->
          (match args with
           | [data] -> Runtime.sexp_to_value data (* Use Runtime helper *)
           | _ -> failwith "Malformed quote: expected exactly one argument")
      | Sexp.Atom "if" ->
          (match args with
           | [c; t] -> if Value.is_truthy (eval env c) then eval env t else Value.Nil
           | [c; t; e] -> if Value.is_truthy (eval env c) then eval env t else eval env e
           | _ -> failwith "Malformed if: expected 2 or 3 arguments")
      | Sexp.Atom "progn" -> eval_progn env args
      | Sexp.Atom "let" ->
          (match args with
           | Sexp.List bindings_sexp :: body_sexps -> eval_let env bindings_sexp body_sexps
           | _ -> failwith "Malformed let: expected bindings list and body")
      | Sexp.Atom "let*" ->
           (match args with
           | Sexp.List bindings_sexp :: body_sexps -> eval_let_star env bindings_sexp body_sexps
           | _ -> failwith "Malformed let*: expected bindings list and body")
      | Sexp.Atom "setq" -> eval_setq env args
      | Sexp.Atom "lambda" ->
          (match args with
           | arg_list_sexp :: body_sexps -> eval_lambda env arg_list_sexp body_sexps
           | _ -> failwith "Malformed lambda: expected arg list and body")
      | Sexp.Atom "defun" ->
          (match args with
           | Sexp.Atom name :: arg_list_sexp :: body_sexps -> eval_defun env name arg_list_sexp body_sexps
           | _ -> failwith "Malformed defun: expected name, arg list, and body")
      | Sexp.Atom "cond" -> eval_cond env args
      (* Default case: Function Call *)
      | _ -> eval_funcall env head args
      end

and eval_progn (env : eval_env) (forms : Sexp.t list) : Value.t =
  match forms with
  | [] -> Value.Nil
  | [last] -> eval env last
  | form :: rest ->
      let (_ : Value.t) = eval env form in (* Evaluate for side effects *)
      eval_progn env rest (* Evaluate the rest *)

and eval_funcall (env : eval_env) (func_sexp : Sexp.t) (args_sexp : Sexp.t list) : Value.t =
  let func_val = eval env func_sexp in
  let arg_vals = List.map args_sexp ~f:(eval env) in
  Runtime.apply_function func_val arg_vals

and eval_let (env : eval_env) (bindings_sexp : Sexp.t list) (body_sexps : Sexp.t list) : Value.t =
  (* 1. Evaluate all initializers in the *outer* environment *)
  let evaluated_bindings_with_refs = List.map bindings_sexp ~f:(fun b_sexp ->
      match b_sexp with
      | Sexp.Atom name -> (name, ref Value.Nil) (* No initializer defaults to nil *)
      | Sexp.List [Sexp.Atom name; init_form] ->
          let value = eval env init_form in
          (name, ref value) (* <<< Store ref value *)
      | _ -> failwithf "Malformed let binding: %s" (Sexp.to_string_hum b_sexp) ()
    ) in
  (* 2. Create the inner environment by adding all bindings to a *new* frame *)
  let inner_env = evaluated_bindings_with_refs :: env in (* Push new frame *)
  (* 3. Evaluate the body in the inner environment *)
  eval_progn inner_env body_sexps

and eval_let_star (env : eval_env) (bindings_sexp : Sexp.t list) (body_sexps : Sexp.t list) : Value.t =
  (* Evaluate bindings sequentially, updating the environment *)
  (* Start with a new empty frame for the let* bindings on top of the original env *)
  let env_with_let_star_frame = [] :: env in
  let final_inner_env = List.fold bindings_sexp ~init:env_with_let_star_frame ~f:(fun current_env b_sexp ->
      let name, init_form = match b_sexp with
        | Sexp.Atom n -> (n, Sexp.Atom "nil")
        | Sexp.List [Sexp.Atom n; i] -> (n, i)
        | _ -> failwithf "Malformed let* binding: %s" (Sexp.to_string_hum b_sexp) ()
      in
      (* Evaluate initializer in the *current* sequential environment (which includes the let* frame) *)
      let value = eval current_env init_form in
      (* Add the binding (as a ref) for the *next* iteration to the *current* frame *)
      add_local_binding current_env name value (* add_local_binding adds to the first frame *)
    ) in
  (* Evaluate body in the final environment *)
  eval_progn final_inner_env body_sexps

and eval_setq (env : eval_env) (pairs : Sexp.t list) : Value.t =
  if List.length pairs % 2 <> 0 then
    failwith "Malformed setq: must have an even number of arguments (var value pairs)";
  let rec process_pairs current_val pairs_left =
    match pairs_left with
    | [] -> current_val (* Return the last value assigned *)
    | Sexp.Atom var_name :: value_sexp :: rest ->
        let value = eval env value_sexp in
        let _ = set_variable env var_name value in (* Perform assignment *)
        process_pairs value rest (* Recurse with the assigned value *)
    | not_atom :: _ -> failwithf "Malformed setq: expected symbol, got %s" (Sexp.to_string_hum not_atom) ()
  in
  process_pairs Value.Nil pairs (* Start with Nil, process pairs *)


and eval_lambda (outer_env : eval_env) (arg_list_sexp : Sexp.t) (body_sexps : Sexp.t list) : Value.t =
  (* Note: ArgListParser is in Analyze module, we might need a simpler parser here *)
  (* Simplified parsing for now: assume just list of symbols *)
  let arg_names = match arg_list_sexp with
    | Sexp.List names -> List.map names ~f:(function Sexp.Atom s -> s | _ -> failwith "Invalid lambda arg list")
    | _ -> failwith "Lambda list must be a list"
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
    eval_progn body_env body_sexps
  )

and eval_defun (env : eval_env) (name : string) (arg_list_sexp : Sexp.t) (body_sexps : Sexp.t list) : Value.t =
  (* 1. Create the function value (closure) using eval_lambda *)
  (* The closure needs to capture the *current* env for lexical scope *)
  let fun_value = eval_lambda env arg_list_sexp body_sexps in
  (* 2. Register it in the global environment *)
  Runtime.register_global name fun_value;
  (* 3. Defun returns the function name as a symbol *)
  Value.Symbol { name = name }

and eval_cond (env : eval_env) (clauses_sexp : Sexp.t list) : Value.t =
  match clauses_sexp with
  | [] -> Value.Nil (* No clauses, result is nil *)
  | clause :: rest_clauses ->
      match clause with
      | Sexp.List (test_sexp :: body_sexps) ->
          let test_result = eval env test_sexp in
          if Value.is_truthy test_result then
            (* Condition is true *)
            if List.is_empty body_sexps then
              test_result (* No body, result is the test result *)
            else
              eval_progn env body_sexps (* Evaluate body *)
          else
            (* Condition is false, evaluate remaining clauses *)
            eval_cond env rest_clauses
      | _ -> failwith "Malformed cond clause: must be a list"


(* --- Top-Level Evaluation --- *)

(** Evaluate a list of S-expressions sequentially, returning the last result.
    Uses the global environment implicitly via lookup_variable/set_variable. *)
let eval_toplevel (sexps : Sexp.t list) : Value.t =
  (* Start with an empty local environment (only globals from Runtime) *)
  let initial_env : eval_env = [] in
  eval_progn initial_env sexps

(* test/test_harness.ml *)
open Core
open Core_unix
open Stdio

module Value  = Camelisp.Value
module Parse  = Camelisp.Parse
module Interp = Camelisp.Interpreter
module Runtime = Camelisp.Runtime (* Added for registering compiler impl *)
module Compiler = Camelisp.Compiler (* Added for registering compiler impl *)
module Analyze = Camelisp.Analyze (* Added for compiler impl *)
module Translate = Camelisp.Translate (* Added for compiler impl *)


(* ---------- Compiler Implementation Registration (Needed for compile tests later) --- *)
(* Replicated from bin/main.ml for testing purposes *)
let camelisp_compile_impl (code_list : Value.t list) : (string * Value.t) list =
  try
    let typed_asts, final_env_types, needs_boxing_set = Analyze.analyze_toplevel code_list in
    let ocaml_code = Translate.translate_toplevel typed_asts final_env_types needs_boxing_set in
    Compiler.compile_and_load_string ocaml_code
  with
  | Compiler.Compilation_error msg -> failwith ("Compilation Error: " ^ msg)
  | Failure msg -> failwith ("Analysis/Translation/Runtime Error: " ^ msg)
  | exn -> failwith ("Unexpected compilation pipeline error: " ^ Exn.to_string exn)

let camelisp_interpret_impl (code_list : Value.t list) : Value.t =
   try
     Interp.eval_toplevel code_list
   with
   | Failure msg -> failwith ("Interpretation Error: " ^ msg)
   | exn -> failwith ("Unexpected interpretation error: " ^ Exn.to_string exn)

let () =
 Runtime.register_compile_impl camelisp_compile_impl;
 Runtime.register_interpret_impl camelisp_interpret_impl;
 ()

(* ---------- Helper to run a shell command and capture output ---------------- *)
let run_cmd (cmd : string) : (string, string) result =
  let proc =
    open_process_full ~env:(environment ()) cmd in
  let stdout = In_channel.input_all proc.stdout |> String.strip in
  let stderr = In_channel.input_all proc.stderr in
  match close_process_full proc with
  | Ok () -> Ok stdout
  | Error _      -> Error stderr (* Corrected: Return stderr on non-Ok status *)

(* ---------- One‑shot Emacs daemon ------------------------------------------- *)
let server_name = sprintf "camelisp-test-%d" (Pid.to_int (getpid ()))

let () =
  ignore (run_cmd (sprintf "emacs --daemon=%s" server_name));
  at_exit (fun () ->
    ignore (run_cmd (sprintf "emacsclient -n -s %s --eval '(kill-emacs)'" server_name)))

(* ---------- Camelisp runner (evaluate in‑process) ------------------------------ *)
let run_camelisp expr : (string, string) result =
  (* Use multiple_from_string to handle potential multi-expression tests *)
  match Parse.multiple_from_string ~filename:"<test>" expr with
  | Error msg -> Error ("parse error: " ^ msg)
  | Ok sexps ->
      (try
         let v = Interp.eval_toplevel sexps in (* Evaluate all expressions *)
         Ok (String.strip (!Value.to_string v)) (* Return result of last expr *)
       with exn -> Error ("runtime error: " ^ Exn.to_string exn))

(* ---------- Emacs runner ---------------------------------------------------- *)
let run_emacs expr : (string, string) result =
  (* Wrap expression in progn to handle multiple forms and print the last result *)
  let elisp = Printf.sprintf "(princ (eval (car (read-from-string %S))))" expr in
  match run_cmd (Printf.sprintf "emacsclient -n -s %s -e %S" server_name elisp) with
  | Ok out -> Ok out
  | Error stderr -> (* Fallback if client fails *)
    if String.is_prefix stderr ~prefix:"emacsclient: can't find socket" then
      run_cmd (Printf.sprintf "emacs --batch --eval %S" elisp)
    else
      Error stderr (* Return the original error *)

(* ---------- Comparison ------------------------------------------------------ *)
let compare_case expr =
  match run_camelisp expr, run_emacs expr with
  | Ok mine, Ok theirs when String.equal mine theirs -> ()
  | Ok mine, Ok theirs ->
      failwithf "%s mismatch:\n  camelisp → %S\n  emacs → %S" expr mine theirs ()
  | Error e, _ -> failwithf "camelisp error on %S: %s" expr e ()
  | _, Error e -> failwithf "emacs error on %S: %s" expr e ()

(* ---------- Alcotest boilerplate ------------------------------------------- *)
let () =
  let cases = [
    "(+ 1 2)";
    "(- 10 3)";
    "(* 2 3)";
    "(/ 1 2)";
    "(integerp (/ 8 2))";
    "(/ 8 2)";
    "(/ 1 2)";              (* integer division edge‑case *)
    "(+ 0.5 2)";            (* float + int mix *)
    "(list 1 2 3)";
    "(car '(a b c))";
    "(cdr '(a b c))";
    "(cons 1 '(2 3))";
    "(eq 'a 'a)";
    "(eq 1 1)";
    "(equal '(1 2) '(1 2))";
    "(equal '(1 . 2) '(1 . 2))";
    "(integerp 42)";
    "(floatp 3.14)";
    "(stringp \"hello\")";
    "(symbolp 'foo)";
    "(keywordp :bar)";
    "(vectorp [1 2 3])";
    "(null nil)";
    "(atom 'foo)";
    "(progn 1 2 3)";
    "(let ((x 2) (y 3)) (+ x y))";
    "(let* ((x 2) (y (+ x 1))) y)";
    "((lambda (a b) (* a b)) 3 4)";
    "(apply '+ '(1 2 3))"; (* Simple apply *)
    "(apply 'list '(1 2 3 4))";
    "(let ((a 1)) (setq a 2) a)"; (* setq modifies let var *)
    "(let* ((a 1) (b a)) (setq a 2) b)"; (* let* binding uses old value *)
    "(let* ((a 1) (b (progn (setq a 5) a))) b)"; (* setq affects subsequent let* binding *)
    "((lambda (x) (setq x (* x 2)) x) 5)"; (* setq modifies lambda arg *)
    "(let ((counter 0)) (defun inc () (setq counter (+ counter 1))) (inc) (inc) counter)"; (* defun closure modifies captured let var *)
    "(let ((a 10)) (defun get-a () a) (setq a 20) (get-a))"; (* closure sees external update before call *)
    "(let ((a 0)) (let ((f (lambda () (setq a (+ a 1))))) (funcall f) (funcall f) a))"; (* lambda closure modification persists *)
    "(let ((x 1)) (let ((f (lambda (y) (setq x (+ x y))))) (apply f '(10)) (apply f '(100)) x))"; (* lambda closure modification with args persists *)
    "(progn (setq x 1) (setq x \"hi\") x)"
  ] in
  let tests =
    List.map cases ~f:(fun ex -> ex, `Quick, fun () -> compare_case ex)
  in
  Alcotest.run "camelisp vs emacs" [ "golden", tests ]
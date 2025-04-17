open Core
open Core_unix
open Stdio

module Value  = Scaml.Value
module Parse  = Scaml.Parse
module Interp = Scaml.Interpreter

(* ---------- Helper to run a shell command and capture output ---------------- *)
let run_cmd (cmd : string) : (string, string) result =
  let proc =
    open_process_full ~env:(environment ()) cmd in
  let stdout = In_channel.input_all proc.stdout |> String.strip in
  let stderr = In_channel.input_all proc.stderr in
  match close_process_full proc with
  | Ok () -> Ok stdout
  | _     -> Error stderr

(* ---------- One‑shot Emacs daemon ------------------------------------------- *)
let server_name = sprintf "scaml-test-%d" (Pid.to_int (getpid ()))

let () =
  ignore (run_cmd (sprintf "emacs --daemon=%s" server_name));
  at_exit (fun () ->
    ignore (run_cmd (sprintf "emacsclient -n -s %s --eval '(kill-emacs)'" server_name)))

(* ---------- Scaml runner (evaluate in‑process) ------------------------------ *)
let run_scaml expr : (string, string) result =
  match Parse.from_string expr with
  | Error msg -> Error ("parse error: " ^ msg)
  | Ok sexp ->
      (try
         let v = Interp.eval_toplevel [ sexp ] in
         Ok (String.strip (!Value.to_string v))
       with exn -> Error ("runtime error: " ^ Exn.to_string exn))

(* ---------- Emacs runner ---------------------------------------------------- *)
let run_emacs expr : (string, string) result =
  let elisp = Printf.sprintf "(princ (eval (car (read-from-string %S))))" expr in
  match run_cmd (Printf.sprintf "emacsclient -n -s %s -e %S" server_name elisp) with
  | Ok out -> Ok out
  | Error _ ->
      run_cmd (Printf.sprintf "emacs --batch --eval %S" elisp)

(* ---------- Comparison ------------------------------------------------------ *)
let compare_case expr =
  match run_scaml expr, run_emacs expr with
  | Ok mine, Ok theirs when String.equal mine theirs -> ()
  | Ok mine, Ok theirs ->
      failwithf "%s mismatch:\n  scaml → %S\n  emacs → %S" expr mine theirs ()
  | Error e, _ -> failwithf "scaml error on %S: %s" expr e ()
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
    "(/ 1 2)";             (* integer division edge‑case *)
    "(+ 0.5 2)";           (* float + int mix *)
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
  ] in
  let tests =
    List.map cases ~f:(fun ex -> ex, `Quick, fun () -> compare_case ex)
  in
  Alcotest.run "scaml vs emacs" [ "golden", tests ]

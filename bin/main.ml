(* bin/main.ml - REPL for Camelisp with Readline Support *)

open! Core
(* REMOVED: Sexplib related opens *)

(* Module Aliases for convenience *)
module Parse = Camelisp.Parse (* Use the new parser module *)
module Compiler = Camelisp.Compiler
module Runtime = Camelisp.Runtime
module Value = Camelisp.Value
module Interpreter = Camelisp.Interpreter
module Analyze = Camelisp.Analyze
module Translate = Camelisp.Translate


(* --- Compile Implementation (for 'compile' built-in) --- *)
(* This function now takes Value.t list (representing quoted code) *)
let camelisp_compile_impl (code_list : Value.t list) : (string * Value.t) list =
  try
     (* 1. Analyze - Captures TASTs, final env types, and vars needing boxing *)
     let typed_asts, final_env_types, needs_boxing_set = Analyze.analyze_toplevel code_list in

     (* 2. Translate - Pass boxing information *)
     let ocaml_code = Translate.translate_toplevel typed_asts final_env_types needs_boxing_set in

     (* Check verbose flag and print generated code if enabled *)
     if Compiler.is_compile_verbose () then (
        printf "\n--- Generated OCaml Code ---\n%s\n--------------------------\n%!" ocaml_code;
     );

     (* 3. Compile and Load - Returns env list directly *)
     let env_alist = Compiler.compile_and_load_string ocaml_code in

     (* Register the compiled definitions in the Runtime global environment *)
     List.iter env_alist ~f:(fun (name, value) ->
         Runtime.register_global name value
     );

     env_alist
  with
   (* Propagate errors, potentially wrapping them *)
   | Compiler.Compilation_error msg -> failwith ("Compilation Error: " ^ msg)
   | Failure msg -> failwith ("Analysis/Translation/Runtime Error: " ^ msg)
   | exn -> failwith ("Unexpected compilation pipeline error: " ^ Exn.to_string exn)

(* --- Interpret Implementation (for 'interpret' built-in) --- *)
(* This function now takes Value.t list *)
let camelisp_interpret_impl (code_list : Value.t list) : Value.t =
    try
        (* Evaluate using the interpreter's top-level function *)
        Interpreter.eval_toplevel code_list
    with
    | Failure msg -> failwith ("Interpretation Error: " ^ msg)
    | exn -> failwith ("Unexpected interpretation error: " ^ Exn.to_string exn)


(* --- Readline Completion --- *)

(* List of language keywords and special forms for completion *)
let language_keywords = [
  "quote"; "quasiquote"; "unquote"; "unquote-splicing"; "function"; (* Reader macros *)
  "if"; "cond"; "progn"; "let"; "let*"; "setq"; "lambda"; "defun"; (* Special forms *)
  "nil"; "t"; (* Constants *)
  "compile"; "interpret"; (* Builtins that act like special forms *)
  "set-compile-verbose"; "set-keep-compile-artifacts"; "exit"; (* Other utility builtins *)
  (* Add core builtins manually if desired, though they are also in globals *)
  (* "cons"; "car"; "cdr"; "list"; "+"; "-"; "*"; "/"; "eq"; "equal"; ... *)
]

(* Helper to check if a character is a delimiter for completion *)
let is_delimiter c =
  String.contains " \t\n\r()[]'\",`" c

(* Helper to extract the atom fragment before the cursor *)
let get_atom_fragment (text : string) : string =
  match String.rfindi text ~f:(fun _ c -> is_delimiter c) with
  | None -> text (* No delimiter, whole string is the atom *)
  | Some last_delimiter_index ->
      (* Extract substring after the last delimiter *)
      String.sub text ~pos:(last_delimiter_index + 1) ~len:(String.length text - (last_delimiter_index + 1))

(* Completion generator function *)
(* Takes the word being completed (up to the cursor) *)
(* Returns a Readline.completion_result variant *)
let completion_generator (text_before_cursor : string) : Readline.completion_result =
  (* Extract the relevant atom fragment to complete *)
  let atom_fragment = get_atom_fragment text_before_cursor in

  (* If fragment is empty (e.g., user typed a space), offer no completions *)
   if String.is_empty atom_fragment && not (String.is_empty text_before_cursor) then
    Readline.Empty
   else
    (* Get all globally defined symbols *)
    let global_symbols = Runtime.get_global_symbols () in
    (* Combine globals and keywords, remove duplicates, and sort *)
    let all_candidates =
      List.dedup_and_sort ~compare:String.compare (language_keywords @ global_symbols)
    in
    (* Filter candidates that start with the atom fragment *)
    let matching_symbols =
      List.filter all_candidates ~f:(fun sym ->
        String.is_prefix sym ~prefix:atom_fragment (* Match against the extracted fragment *)
      )
    in
    (* If no matches, return Empty *)
    if List.is_empty matching_symbols then
      Readline.Empty (* Use constructor directly *)
    else
      (* Otherwise, map matches to (string * char) list and return Custom *)
      let custom_completions =
        List.map matching_symbols ~f:(fun sym -> (sym, ' ')) (* Use space as default type char *)
      in
      Readline.Custom custom_completions (* Use constructor directly *)


(* --- REPL Implementation with Readline --- *)
let run_repl () =
  (* Initialize the REPL's lexical environment *)
  let repl_env : Interpreter.eval_env ref = ref [] in
  (* No need for a mutable repl_funs_env unless we add local func defs to REPL *)
  let initial_funs_env : Interpreter.funs_env = [] in
  let continue = ref true in

  (* Register 'exit' *)
  Runtime.register_global "exit" (Value.Builtin (fun _ -> continue := false; Value.Nil));

  (* --- Setup Readline --- *)
  Readline.init ();
  (* Optional: Define characters that break words for completion *)
  (* Readline.set_completion_word_break_characters " \t\n\"\\'`@$><=;|&{()}"; *)

  printf "Welcome to Camelisp REPL!\n";
  printf "Using Readline for input and completion (TAB).\n";
  printf "Use (exit) or Ctrl+D to quit.\n";
  printf "Use (set-compile-verbose t) to see generated code during compilation.\n";
  printf "Use (set-keep-compile-artifacts t) to keep temporary files.\n%!"; (* Added hint *)

  (* Helper to check if input has balanced delimiters *)
  let has_balanced_delimiters s =
    let rec check chars paren_count bracket_count in_string in_char in_comment =
      match chars with
      | [] -> paren_count = 0 && bracket_count = 0 && not in_string && not in_char
      | ';' :: rest when not in_string && not in_char ->
          (* Skip line comment *)
            let rest' = List.drop_while rest ~f:(fun c -> not (Char.equal c '\n')) in
          check rest' paren_count bracket_count in_string in_char in_comment
      | '\\' :: _ :: rest when in_string || in_char ->
          (* Skip escaped character *)
          check rest paren_count bracket_count in_string in_char in_comment
      | '"' :: rest when not in_char && not in_comment ->
          check rest paren_count bracket_count (not in_string) in_char in_comment
      | '?' :: '\\' :: _ :: rest when not in_string && not in_comment ->
          (* Character literal with escape *)
          check rest paren_count bracket_count in_string false in_comment
      | '?' :: _ :: rest when not in_string && not in_comment ->
          (* Character literal *)
          check rest paren_count bracket_count in_string false in_comment
      | '(' :: rest when not in_string && not in_char && not in_comment ->
          check rest (paren_count + 1) bracket_count in_string in_char in_comment
      | ')' :: rest when not in_string && not in_char && not in_comment ->
          if paren_count <= 0 then false
          else check rest (paren_count - 1) bracket_count in_string in_char in_comment
      | '[' :: rest when not in_string && not in_char && not in_comment ->
          check rest paren_count (bracket_count + 1) in_string in_char in_comment
      | ']' :: rest when not in_string && not in_char && not in_comment ->
          if bracket_count <= 0 then false
          else check rest paren_count (bracket_count - 1) in_string in_char in_comment
      | _ :: rest ->
          check rest paren_count bracket_count in_string in_char in_comment
    in
    check (String.to_list s) 0 0 false false false
  in

  (* Buffer for accumulating multi-line input *)
  let input_buffer = Buffer.create 256 in
  let prompt_ref = ref "> " in

  (* REPL Loop using Readline *)
  while !continue do
    (* Pass the completion function to readline *)
    match Readline.readline ~prompt:!prompt_ref ~completion_fun:completion_generator () with
    | None -> (* EOF (Ctrl+D) *)
        continue := false;
        printf "\n%!" (* Print newline after Ctrl+D *)
    | Some line ->
        (* Add line to buffer *)
        Buffer.add_string input_buffer line;
        Buffer.add_char input_buffer '\n';

        let accumulated = Buffer.contents input_buffer in
        let trimmed = String.strip accumulated in

        (* If empty or just whitespace, reset and continue *)
        if String.is_empty trimmed then begin
          Buffer.clear input_buffer;
          prompt_ref := "> ";
          () (* Continue loop *)
        end else if not (has_balanced_delimiters accumulated) then begin
          (* Unbalanced - need more input *)
          prompt_ref := "... ";
          () (* Continue loop to read more *)
        end else begin
          (* Delimiters are balanced - try to parse *)
          match Parse.from_string ~filename:"<stdin>" accumulated with
          | Error msg ->
              (* Parse error even with balanced delimiters *)
              printf "Parse Error: %s\n%!" msg;
              Buffer.clear input_buffer;
              prompt_ref := "> "
          | Ok value ->
              (* Successfully parsed - add to history, evaluate, and reset *)
              if not (String.is_empty trimmed) then
                Readline.add_history trimmed;

              Buffer.clear input_buffer;
              prompt_ref := "> ";

              (* Evaluate the parsed expression *)
              begin try
                let result = Interpreter.eval !repl_env initial_funs_env value in
                (* Print the result *)
                printf "%s\n%!" (!Value.to_string result);
              with
              (* Handle runtime errors during evaluation *)
              | Failure msg -> printf "Runtime Error: %s\n%!" msg
              | exn -> printf "Unexpected Error: %s\n%!" (Exn.to_string exn)
              end
        end
  done;
  printf "Exiting Camelisp REPL.\n%!"


let () =
  (* ***** REGISTER BUILTIN IMPLEMENTATIONS ***** *)
  (* Register the adapted implementations that take Value.t list *)
  Runtime.register_compile_impl camelisp_compile_impl;
  Runtime.register_interpret_impl camelisp_interpret_impl;
  (* ******************************************** *)

  (* Run the REPL (Readline init is now inside run_repl) *)
  run_repl ()


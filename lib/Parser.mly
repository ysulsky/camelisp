/* camelisp/lib/parser.mly */
%{
open Value (* Use Value.t and helpers directly *)

(* Helper function to build reader macro expansions using Value.t *)
let make_reader_macro sym expr =
  (* list_to_value creates the mutable structure if needed *)
  list_to_value [ sym; expr ]

%}

/* Declare tokens produced by the lexer */
%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> SYMBOL
%token <string> KEYWORD
%token <char> CHAR
%token LPAREN RPAREN LBRACKET RBRACKET
%token DOT QUOTE BACKQUOTE COMMA COMMA_AT HASH_QUOTE
%token NIL_TOKEN T_TOKEN /* Specific tokens for nil and t */
%token EOF

/* Define start symbol and its type - CHANGED to repl_entry */
%start <Value.t> repl_entry
%type <Value.t> sexp atom list_content vector_content
%type <Value.t list> sexp_list /* For sequences inside lists/vectors */

%% /* Grammar rules */

/* New entry point for REPL - Parses one expression without requiring EOF */
repl_entry:
  | sexp { $1 }
  ;

/* Keep original main rule if needed for file parsing later, */
/* but it won't be the default entry point anymore.       */
/* main: sexp EOF { $1 } ; */


sexp:
  | atom                                     { $1 }
  | LPAREN list_content RPAREN               { $2 }
  | LBRACKET vector_content RBRACKET         { $2 }
  /* Reader Macros - Create symbols dynamically */
  | QUOTE sexp                               { make_reader_macro (mk_symbol "quote") $2 }
  | BACKQUOTE sexp                           { make_reader_macro (mk_symbol "quasiquote") $2 }
  | COMMA sexp                               { make_reader_macro (mk_symbol "unquote") $2 }
  | COMMA_AT sexp                            { make_reader_macro (mk_symbol "unquote-splicing") $2 }
  | HASH_QUOTE sexp                          { make_reader_macro (mk_symbol "function") $2 }
  ;

atom:
  | NIL_TOKEN                                { Nil }
  | T_TOKEN                                  { T }
  | INT                                      { Int $1 }
  | FLOAT                                    { Float $1 }
  | STRING                                   { String $1 }
  | SYMBOL                                   { mk_symbol $1 } (* Use mk_symbol helper *)
  | KEYWORD                                  { Keyword $1 }
  | CHAR                                     { Char $1 }
  ;

/* Content of a list: zero or more sexps, possibly ending with a dot */
list_content:
    /* empty list '()' -> Nil */
  | /* epsilon */                            { Nil }
    /* Proper list: (a b c) */
  | sexp_list                                { list_to_value $1 } (* Builds Cons *)
    /* Dotted list: (a b . c) */
  | sexp_list DOT sexp                       { list_to_value_dotted $1 $3 } (* Use helper *)
  ;

/* Content of a vector: zero or more sexps */
vector_content:
  | /* epsilon */                            { Vector [||] }
  | sexp_list                                { Vector (Array.of_list $1) }
  ;

/* Helper rule for a non-empty sequence of sexps */
sexp_list:
  | sexp                                     { [$1] }
  | sexp_list sexp                           { $1 @ [$2] } (* Append new sexp to the list *)
  ;

%%


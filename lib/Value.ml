    (* Value.ml - Defines the runtime representation of Elisp values in OCaml *)

    open! Core
    open! Sexplib.Std
    let builtin_compare = compare;;

    (* Define the mutually recursive types *)
    type t =
      | Nil | T | Int of int | Float of float | String of string
      | Symbol of symbol_data | Keyword of string | Cons of cons_cell
      | Vector of t Array.t | Function of elisp_fun | Builtin of builtin_fun
      | Char of char
    [@@deriving sexp] (* Keep sexp_of for now *)

    and cons_cell = {
      mutable car : t;
      mutable cdr : t;
    }
    [@@deriving sexp]

    and symbol_data = {
      name: string;
      (* Add other fields like properties if needed *)
    }
    [@@deriving sexp]

    and elisp_fun = t list -> t
    and builtin_fun = t list -> t

    let sexp_of_elisp_fun _ = Sexp.Atom "<elisp_fun>"
    let sexp_of_builtin_fun _ = Sexp.Atom "<builtin_fun>"

    (* --- Manual Comparison Function --- *)
    let rec compare v1 v2 =
        match (v1, v2) with
        | Nil, Nil -> 0 | T, T -> 0 | Int i1, Int i2 -> Int.compare i1 i2
        | Float f1, Float f2 -> Float.compare f1 f2 | String s1, String s2 -> String.compare s1 s2
        | Symbol sd1, Symbol sd2 -> String.compare sd1.name sd2.name
        | Keyword k1, Keyword k2 -> String.compare k1 k2
        | Cons c1, Cons c2 -> List.compare compare [c1.car; c1.cdr] [c2.car; c2.cdr]
        | Vector a1, Vector a2 -> Array.compare compare a1 a2
        | Function f1, Function f2 -> builtin_compare (Obj.magic f1) (Obj.magic f2)
        | Builtin f1, Builtin f2 -> builtin_compare (Obj.magic f1) (Obj.magic f2)
        | Char c1, Char c2 -> Char.compare c1 c2
        (* Order definitions *)
        | Nil, _ -> -1 | _, Nil -> 1 | T, _ -> -1 | _, T -> 1
        | Int _, _ -> -1 | _, Int _ -> 1 | Float _, _ -> -1 | _, Float _ -> 1
        | Char _, _ -> -1 | _, Char _ -> 1 | String _, _ -> -1 | _, String _ -> 1
        | Symbol _, _ -> -1 | _, Symbol _ -> 1 | Keyword _, _ -> -1 | _, Keyword _ -> 1
        | Cons _, _ -> -1 | _, Cons _ -> 1 | Vector _, _ -> -1 | _, Vector _ -> 1
        | Function _, _ -> -1 | _, Function _ -> 1
        (* ***** FIX HERE: Remove redundant Builtin cases ***** *)
        (* | Builtin _, _ -> -1 | _, Builtin _ -> 1 *)


    (* --- Helper functions (Moved/Adapted from Types.ml/Parse.ml) --- *)

    (** Create a symbol. (Could involve interning later) *)
    let mk_symbol name = Symbol { name }

    (** Check if a value is nil *)
    let is_nil = function Nil -> true | _ -> false

    (** Check if a value is truthy in Elisp (anything other than nil) *)
    let is_truthy v = not (is_nil v)

    (** Convert an OCaml list of Value.t to a proper Lisp list (Value.t Cons chain ending in Nil) *)
    let rec list_to_value (l : t list) : t =
      match l with
      | [] -> Nil
      | h :: t -> Cons { car = h; cdr = list_to_value t }

    (** Convert an OCaml list and a final cdr value to a (possibly dotted) Lisp list *)
    let rec list_to_value_dotted (items : t list) (last : t) : t =
       match items with
       | [] -> last
       | car :: cdr -> Cons { car = car; cdr = list_to_value_dotted cdr last }

    (* --- Value to List Conversion --- *)
    let rec value_to_list_opt (v : t) : t list option =
      match v with
      | Nil -> Some []
      | Cons { car; cdr } ->
          (match value_to_list_opt cdr with
           | Some rest -> Some (car :: rest)
           | None -> None (* Improper list *)
          )
      | _ -> None (* Not a list *)


    (* --- Printing --- *)
    (* Keep existing Lisp-style printer setup from Runtime.ml if preferred *)
    let default_to_string v = sexp_of_t v |> Sexp.to_string_hum
    let to_string : (t -> string) ref = ref default_to_string
    (* Ensure Runtime.ml updates this ref if using the Lisp printer *)


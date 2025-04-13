(* InferredType.ml - Defines the representation for inferred Elisp types *)

open! Core
open! Sexplib.Std

(* Define recursive module 'T' containing the type definitions *)
module rec T : sig
  (* Expose the types defined within the module *)
  type t =
    | T_Unknown
    | T_Any
    | T_Nil
    | T_Bool
    | T_Int
    | T_Float
    | T_Char
    | T_String
    | T_Symbol
    | T_Keyword
    | T_Var of string
    | T_Cons of cons_info
    | T_Vector of vector_info
    | T_Function of fun_info
    | T_Union of InferredTypeSet.t (* Reference the Set module defined below *)

  and cons_info = {
    car_type: t;
    cdr_type: t;
  }
  and vector_info = {
    element_type: t;
  }
  and fun_info = {
    arg_types: t list option;
    return_type: t;
  }
  and arg_spec = {
      required: string list;
      optional: (string * Value.t option) list;
      rest: string option;
    }
  [@@deriving compare, sexp] (* Derive functions within the module T *)

end = struct
  (* Actual definition of the types *)
   type t =
    | T_Unknown | T_Any | T_Nil | T_Bool | T_Int | T_Float | T_Char | T_String
    | T_Symbol | T_Keyword | T_Var of string
    | T_Cons of cons_info | T_Vector of vector_info | T_Function of fun_info
    | T_Union of InferredTypeSet.t
  and cons_info = { car_type: t; cdr_type: t; }
  and vector_info = { element_type: t; }
  and fun_info = { arg_types: t list option; return_type: t; }
  and arg_spec = { required: string list; optional: (string * Value.t option) list; rest: string option; }
  [@@deriving compare, sexp]
end
(* Define the Set module using 'and' for mutual recursion with module T *)
and InferredTypeSet : (Set.S with type Elt.t = T.t) = Set.Make(T)

(* Include the types and derived functions from T into the main InferredType scope *)
include T

(* --- Helper Functions --- *)
(* These can now directly use type 't' because of 'include T' *)

(** Flattens nested unions and handles absorbing types (Unknown, Any) *)
let normalize_union_set (s : InferredTypeSet.t) : t =
  if Set.mem s T_Unknown then T_Unknown
  else if Set.mem s T_Any then T_Any
  else
    let flattened = Set.fold s ~init:InferredTypeSet.empty ~f:(fun acc ty ->
      match ty with
      | T_Union inner_s -> Set.union acc inner_s
      | T_Unknown | T_Any -> acc
      | _ -> Set.add acc ty
    )
    in
    if Set.mem flattened T_Unknown then T_Unknown
    else if Set.mem flattened T_Any then T_Any
    else if Set.is_empty flattened then T_Nil
    else if Set.length flattened = 1 then Set.choose_exn flattened
    else T_Union flattened


(** Computes the union (join) of two inferred types using T_Union *)
let type_union t1 t2 : t =
  match compare t1 t2 with (* Uses compare derived in T and included *)
  | 0 -> t1
  | _ ->
      match (t1, t2) with
      | (T_Unknown, _) | (_, T_Unknown) -> T_Unknown
      | (T_Any, _) | (_, T_Any) -> T_Any
      | (T_Union s1, T_Union s2) -> normalize_union_set (Set.union s1 s2)
      | (T_Union s, other) | (other, T_Union s) -> normalize_union_set (Set.add s other)
      | _ -> normalize_union_set (InferredTypeSet.of_list [t1; t2])


(** Pretty-printer for inferred types using derived sexp converter *)
let to_string t =
  sexp_of_t t |> Sexp.to_string_hum (* Uses sexp_of_t derived in T and included *)


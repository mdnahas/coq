(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util

module ValT = Dyn.Make(struct end)
module ArgT = Dyn.Make(struct end)

module Val =
struct

  type 'a typ = 'a ValT.tag

  type _ tag =
  | Base : 'a typ -> 'a tag
  | List : 'a tag -> 'a list tag
  | Opt : 'a tag -> 'a option tag
  | Pair : 'a tag * 'b tag -> ('a * 'b) tag

  type t = Dyn : 'a tag * 'a -> t

  let rec eq : type a b. a tag -> b tag -> (a, b) CSig.eq option =
  fun t1 t2 -> match t1, t2 with
  | Base t1, Base t2 -> ValT.eq t1 t2
  | List t1, List t2 ->
    begin match eq t1 t2 with
    | None -> None
    | Some Refl -> Some Refl
    end
  | Opt t1, Opt t2 ->
    begin match eq t1 t2 with
    | None -> None
    | Some Refl -> Some Refl
    end
  | Pair (t1, u1), Pair (t2, u2) ->
    begin match eq t1 t2 with
    | None -> None
    | Some Refl ->
      match eq u1 u2 with
      | None -> None
      | Some Refl -> Some Refl
    end
  | _ -> None

  let rec repr : type a. a tag -> std_ppcmds = function
  | Base t -> str (ValT.repr t)
  | List t -> repr t ++ spc () ++ str "list"
  | Opt t -> repr t ++ spc () ++ str "option"
  | Pair (t1, t2) -> str "(" ++ repr t1 ++ str " * " ++ repr t2 ++ str ")"

end

type (_, _, _) genarg_type =
| ExtraArg : ('a * 'b * 'c) ArgT.tag -> ('a, 'b, 'c) genarg_type
| ListArg : ('a, 'b, 'c) genarg_type -> ('a list, 'b list, 'c list) genarg_type
| OptArg : ('a, 'b, 'c) genarg_type -> ('a option, 'b option, 'c option) genarg_type
| PairArg : ('a1, 'b1, 'c1) genarg_type * ('a2, 'b2, 'c2) genarg_type ->
  ('a1 * 'a2, 'b1 * 'b2, 'c1 * 'c2) genarg_type

type argument_type = ArgumentType : ('a, 'b, 'c) genarg_type -> argument_type

let rec genarg_type_eq : type a1 a2 b1 b2 c1 c2.
  (a1, b1, c1) genarg_type -> (a2, b2, c2) genarg_type ->
  (a1 * b1 * c1, a2 * b2 * c2) CSig.eq option =
fun t1 t2 -> match t1, t2 with
| ExtraArg t1, ExtraArg t2 -> ArgT.eq t1 t2
| ListArg t1, ListArg t2 ->
  begin match genarg_type_eq t1 t2 with
  | None -> None
  | Some Refl -> Some Refl
  end
| OptArg t1, OptArg t2 ->
  begin match genarg_type_eq t1 t2 with
  | None -> None
  | Some Refl -> Some Refl
  end
| PairArg (t1, u1), PairArg (t2, u2) ->
  begin match genarg_type_eq t1 t2 with
  | None -> None
  | Some Refl ->
    match genarg_type_eq u1 u2 with
    | None -> None
    | Some Refl -> Some Refl
  end
| _ -> None

let rec pr_genarg_type : type a b c. (a, b, c) genarg_type -> std_ppcmds = function
| ListArg t -> pr_genarg_type t ++ spc () ++ str "list"
| OptArg t -> pr_genarg_type t ++ spc () ++ str "opt"
| PairArg (t1, t2) ->
    str "("++ pr_genarg_type t1 ++ spc () ++
    str "*" ++ spc () ++ pr_genarg_type t2 ++ str ")"
| ExtraArg s -> str (ArgT.repr s)

let argument_type_eq arg1 arg2 = match arg1, arg2 with
| ArgumentType t1, ArgumentType t2 ->
  match genarg_type_eq t1 t2 with
  | None -> false
  | Some Refl -> true

let pr_argument_type (ArgumentType t) = pr_genarg_type t

type 'a uniform_genarg_type = ('a, 'a, 'a) genarg_type
(** Alias for concision *)

(* Dynamics but tagged by a type expression *)

type rlevel = [ `rlevel ]
type glevel = [ `glevel ]
type tlevel = [ `tlevel ]

type (_, _) abstract_argument_type =
| Rawwit : ('a, 'b, 'c) genarg_type -> ('a, rlevel) abstract_argument_type
| Glbwit : ('a, 'b, 'c) genarg_type -> ('b, glevel) abstract_argument_type
| Topwit : ('a, 'b, 'c) genarg_type -> ('c, tlevel) abstract_argument_type

type 'l generic_argument = GenArg : ('a, 'l) abstract_argument_type * 'a -> 'l generic_argument

type raw_generic_argument = rlevel generic_argument
type glob_generic_argument = glevel generic_argument
type typed_generic_argument = tlevel generic_argument

let rawwit t = Rawwit t
let glbwit t = Glbwit t
let topwit t = Topwit t

let wit_list t = ListArg t

let wit_opt t = OptArg t

let wit_pair t1 t2 = PairArg (t1, t2)

let in_gen t o = GenArg (t, o)

let abstract_argument_type_eq :
  type a b l. (a, l) abstract_argument_type -> (b, l) abstract_argument_type -> (a, b) CSig.eq option =
  fun t1 t2 -> match t1, t2 with
  | Rawwit t1, Rawwit t2 ->
    begin match genarg_type_eq t1 t2 with
    | None -> None
    | Some Refl -> Some Refl
    end
  | Glbwit t1, Glbwit t2 ->
    begin match genarg_type_eq t1 t2 with
    | None -> None
    | Some Refl -> Some Refl
    end
  | Topwit t1, Topwit t2 ->
    begin match genarg_type_eq t1 t2 with
    | None -> None
    | Some Refl -> Some Refl
    end

let out_gen (type a) (type l) (t : (a, l) abstract_argument_type) (o : l generic_argument) : a =
  let GenArg (t', v) = o in
  match abstract_argument_type_eq t t' with
  | None -> failwith "out_gen"
  | Some Refl -> v

let has_type (GenArg (t, v)) u = match abstract_argument_type_eq t u with
| None -> false
| Some _ -> true

let unquote : type l. (_, l) abstract_argument_type -> _ = function
| Rawwit t -> ArgumentType t
| Glbwit t -> ArgumentType t
| Topwit t -> ArgumentType t

let genarg_tag (GenArg (t, _)) = unquote t

type 'a raw_abstract_argument_type = ('a,rlevel) abstract_argument_type
type 'a glob_abstract_argument_type = ('a,glevel) abstract_argument_type
type 'a typed_abstract_argument_type = ('a,tlevel) abstract_argument_type

(** Creating args *)

module type Param = sig type ('raw, 'glb, 'top) t end
module ArgMap(M : Param) =
struct
  type _ pack = Pack : ('raw, 'glb, 'top) M.t -> ('raw * 'glb * 'top) pack
  include ArgT.Map(struct type 'a t = 'a pack end)
end

type ('raw, 'glb, 'top) load = {
  dyn : 'top Val.tag;
}

module LoadMap = ArgMap(struct type ('r, 'g, 't) t = ('r, 'g, 't) load end)

let arg0_map = ref LoadMap.empty

let create_arg ?dyn name =
  match ArgT.name name with
  | Some _ ->
    Errors.anomaly (str "generic argument already declared: " ++ str name)
  | None ->
    let dyn = match dyn with None -> Val.Base (ValT.create name) | Some dyn -> dyn in
    let obj = LoadMap.Pack { dyn; } in
    let name = ArgT.create name in
    let () = arg0_map := LoadMap.add name obj !arg0_map in
    ExtraArg name

let make0 = create_arg

let rec val_tag : type a b c. (a, b, c) genarg_type -> c Val.tag = function
| ListArg t -> Val.List (val_tag t)
| OptArg t -> Val.Opt (val_tag t)
| PairArg (t1, t2) -> Val.Pair (val_tag t1, val_tag t2)
| ExtraArg s ->
  match LoadMap.find s !arg0_map with LoadMap.Pack obj -> obj.dyn

let val_tag = function Topwit t -> val_tag t

(** Registering genarg-manipulating functions *)

module type GenObj =
sig
  type ('raw, 'glb, 'top) obj
  val name : string
  val default : ('raw, 'glb, 'top) genarg_type -> ('raw, 'glb, 'top) obj option
end

module Register (M : GenObj) =
struct
  module GenMap = ArgMap(struct type ('r, 'g, 't) t = ('r, 'g, 't) M.obj end)
  let arg0_map = ref GenMap.empty

  let register0 arg f = match arg with
  | ExtraArg s ->
    if GenMap.mem s !arg0_map then
      let msg = str M.name ++ str " function already registered: " ++ str (ArgT.repr s) in
      Errors.anomaly msg
    else
      arg0_map := GenMap.add s (GenMap.Pack f) !arg0_map
  | _ -> assert false

  let get_obj0 name =
    try
      let GenMap.Pack obj = GenMap.find name !arg0_map in obj
    with Not_found ->
      match M.default (ExtraArg name) with
      | None ->
        Errors.anomaly (str M.name ++ str " function not found: " ++ str (ArgT.repr name))
      | Some obj -> obj

  (** For now, the following function is quite dummy and should only be applied
      to an extra argument type, otherwise, it will badly fail. *)
  let obj t = match t with
  | ExtraArg s -> get_obj0 s
  | _ -> assert false

end

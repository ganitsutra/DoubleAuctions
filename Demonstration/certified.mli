
type __ = Obj.t

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val sub : int -> int -> int

val eqb : int -> int -> bool

val leb : int -> int -> bool

val ltb : int -> int -> bool

type reflect =
| ReflectT
| ReflectF

module type TotalLeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end

module Nat :
 sig
  val eqb : int -> int -> bool
 end

val last : 'a1 list -> 'a1 -> 'a1

val lt_eq_lt_dec : int -> int -> bool option

val reflect_intro : bool -> reflect

module Decidable :
 sig
  type coq_type = { eqb : (__ -> __ -> bool); eqP : (__ -> __ -> reflect) }

  type coq_E = __

  val eqb : coq_type -> coq_E -> coq_E -> bool
 end

val nat_eqP : int -> int -> reflect

val nat_eqType : Decidable.coq_type

type order = { id : int; otime : int; oquantity : int; oprice : int }

type transaction = { idb : int; ida : int; tprice : int; tquantity : int }

val qty_bid : transaction list -> int -> int

val qty_ask : transaction list -> int -> int

val bcompetitive : order -> order -> bool

val acompetitive : order -> order -> bool

module Sort :
 functor (X:TotalLeBool') ->
 sig
  val merge : X.t list -> X.t list -> X.t list

  val merge_list_to_stack :
    X.t list option list -> X.t list -> X.t list option list

  val merge_stack : X.t list option list -> X.t list

  val iter_merge : X.t list option list -> X.t list -> X.t list

  val sort : X.t list -> X.t list

  val flatten_stack : X.t list option list -> X.t list
 end

module SortB :
 sig
  type t = order

  val leb : order -> order -> bool
 end

module Decr_Bid :
 sig
  val merge : order list -> order list -> order list

  val merge_list_to_stack :
    order list option list -> order list -> order list option list

  val merge_stack : order list option list -> order list

  val iter_merge : order list option list -> order list -> order list

  val sort : order list -> order list

  val flatten_stack : order list option list -> order list
 end

module SortA :
 sig
  type t = order

  val leb : order -> order -> bool
 end

module Incr_Ask :
 sig
  val merge : order list -> order list -> order list

  val merge_list_to_stack :
    order list option list -> order list -> order list option list

  val merge_stack : order list option list -> order list

  val iter_merge : order list option list -> order list -> order list

  val sort : order list -> order list

  val flatten_stack : order list option list -> order list
 end

val match0 : order list -> order list -> transaction list

val assign_Transaction_Price : int -> transaction list -> transaction list

val t0 : transaction

val last_Transaction_Price : transaction list -> int

val uM : order list -> order list -> transaction list

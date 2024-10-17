
type __ = Obj.t

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val add : int -> int -> int **)

let rec add = ( + )

(** val sub : int -> int -> int **)

let rec sub n m =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> n)
    (fun k ->
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> n)
      (fun l -> sub k l)
      m)
    n

(** val eqb : int -> int -> bool **)

let rec eqb = ( = )

(** val leb : int -> int -> bool **)

let rec leb = (<=)

(** val ltb : int -> int -> bool **)

let ltb n m =
  leb ((fun x -> x + 1) n) m

type reflect =
| ReflectT
| ReflectF

module type TotalLeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end

module Nat =
 struct
  (** val eqb : int -> int -> bool **)

  let rec eqb n m =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun n' ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> false)
        (fun m' -> eqb n' m')
        m)
      n
 end

(** val last : 'a1 list -> 'a1 -> 'a1 **)

let rec last l d =
  match l with
  | [] -> d
  | a :: l0 -> (match l0 with
                | [] -> a
                | _ :: _ -> last l0 d)

(** val lt_eq_lt_dec : int -> int -> bool option **)

let rec lt_eq_lt_dec n m =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ ->
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> Some false)
      (fun _ -> Some true)
      m)
    (fun n0 ->
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> None)
      (fun n1 -> lt_eq_lt_dec n0 n1)
      m)
    n

(** val reflect_intro : bool -> reflect **)

let reflect_intro = function
| true -> ReflectT
| false -> ReflectF

module Decidable =
 struct
  type coq_type = { eqb : (__ -> __ -> bool); eqP : (__ -> __ -> reflect) }

  type coq_E = __

  (** val eqb : coq_type -> coq_E -> coq_E -> bool **)

  let eqb t1 =
    t1.eqb
 end

(** val nat_eqP : int -> int -> reflect **)

let nat_eqP x y =
  reflect_intro (eqb x y)

(** val nat_eqType : Decidable.coq_type **)

let nat_eqType =
  { Decidable.eqb = (Obj.magic eqb); Decidable.eqP = (Obj.magic nat_eqP) }

type order = { id : int; otime : int; oquantity : int; oprice : int }

type transaction = { idb : int; ida : int; tprice : int; tquantity : int }

(** val qty_bid : transaction list -> int -> int **)

let rec qty_bid t1 i =
  match t1 with
  | [] -> 0
  | t2 :: t' ->
    if nat_eqType.Decidable.eqb (Obj.magic t2.idb) (Obj.magic i)
    then add t2.tquantity (qty_bid t' i)
    else qty_bid t' i

(** val qty_ask : transaction list -> int -> int **)

let rec qty_ask t1 i =
  match t1 with
  | [] -> 0
  | t2 :: t' ->
    if nat_eqType.Decidable.eqb (Obj.magic t2.ida) (Obj.magic i)
    then add t2.tquantity (qty_ask t' i)
    else qty_ask t' i

(** val bcompetitive : order -> order -> bool **)

let bcompetitive b b' =
  (||) (ltb b'.oprice b.oprice)
    ((&&) (eqb b'.oprice b.oprice) (leb b.otime b'.otime))

(** val acompetitive : order -> order -> bool **)

let acompetitive a a' =
  (||) (ltb a.oprice a'.oprice)
    ((&&) (eqb a.oprice a'.oprice) (leb a.otime a'.otime))

module Sort =
 functor (X:TotalLeBool') ->
 struct
  (** val merge : X.t list -> X.t list -> X.t list **)

  let rec merge l1 l2 =
    let rec merge_aux l3 =
      match l1 with
      | [] -> l3
      | a1 :: l1' ->
        (match l3 with
         | [] -> l1
         | a2 :: l2' ->
           if X.leb a1 a2 then a1 :: (merge l1' l3) else a2 :: (merge_aux l2'))
    in merge_aux l2

  (** val merge_list_to_stack :
      X.t list option list -> X.t list -> X.t list option list **)

  let rec merge_list_to_stack stack l =
    match stack with
    | [] -> (Some l) :: []
    | y :: stack' ->
      (match y with
       | Some l' -> None :: (merge_list_to_stack stack' (merge l' l))
       | None -> (Some l) :: stack')

  (** val merge_stack : X.t list option list -> X.t list **)

  let rec merge_stack = function
  | [] -> []
  | y :: stack' ->
    (match y with
     | Some l -> merge l (merge_stack stack')
     | None -> merge_stack stack')

  (** val iter_merge : X.t list option list -> X.t list -> X.t list **)

  let rec iter_merge stack = function
  | [] -> merge_stack stack
  | a :: l' -> iter_merge (merge_list_to_stack stack (a :: [])) l'

  (** val sort : X.t list -> X.t list **)

  let sort =
    iter_merge []

  (** val flatten_stack : X.t list option list -> X.t list **)

  let rec flatten_stack = function
  | [] -> []
  | o :: stack' ->
    (match o with
     | Some l -> app l (flatten_stack stack')
     | None -> flatten_stack stack')
 end

module SortB =
 struct
  type t = order

  (** val leb : order -> order -> bool **)

  let leb =
    bcompetitive
 end

module Decr_Bid = Sort(SortB)

module SortA =
 struct
  type t = order

  (** val leb : order -> order -> bool **)

  let leb =
    acompetitive
 end

module Incr_Ask = Sort(SortA)

(** val match0 : order list -> order list -> transaction list **)

let match0 a b =
  let rec fix_F x =
    match let pr1,_ = x in pr1 with
    | [] -> []
    | o :: l ->
      (match let _,pr2 = x in pr2 with
       | [] -> []
       | o0 :: l0 ->
         if Nat.eqb (sub o0.oprice o.oprice) 0
         then (match lt_eq_lt_dec o0.oquantity o.oquantity with
               | Some s ->
                 if s
                 then { idb = o.id; ida = o0.id; tprice = o0.oprice;
                        tquantity =
                        o0.oquantity } :: (let y = ({ id = o.id; otime =
                                             o.otime; oquantity =
                                             (sub o.oquantity o0.oquantity);
                                             oprice = o.oprice } :: l),l0
                                           in
                                           fix_F y)
                 else { idb = o.id; ida = o0.id; tprice = o0.oprice;
                        tquantity =
                        o0.oquantity } :: (let y = l,l0 in fix_F y)
               | None ->
                 { idb = o.id; ida = o0.id; tprice = o0.oprice; tquantity =
                   o.oquantity } :: (let y = l,({ id = o0.id; otime =
                                       o0.otime; oquantity =
                                       (sub o0.oquantity o.oquantity);
                                       oprice = o0.oprice } :: l0)
                                     in
                                     fix_F y))
         else let y = (o :: l),l0 in fix_F y)
  in fix_F (a,b)

(** val assign_Transaction_Price :
    int -> transaction list -> transaction list **)

let rec assign_Transaction_Price n = function
| [] -> []
| m :: l' ->
  { idb = m.idb; ida = m.ida; tprice = n; tquantity =
    m.tquantity } :: (assign_Transaction_Price n l')

(** val t0 : transaction **)

let t0 =
  { idb = 0; ida = 0; tprice = 0; tquantity = ((fun x -> x + 1) 0) }

(** val last_Transaction_Price : transaction list -> int **)

let last_Transaction_Price m =
  (last m t0).tprice

(** val uM : order list -> order list -> transaction list **)

let uM b a =
  let b0 = Decr_Bid.sort b in
  let a0 = Incr_Ask.sort a in
  let m = match0 b0 a0 in
  let p = last_Transaction_Price m in assign_Transaction_Price p m

(* Demo file for the work "A Formal Approach to Exchange Design and Regulation" *)

Require Import Uniqueness.
Require Import MM.

(* Weak version of demand-supply theorem *)
Theorem Bound_weak p M B A:
        admissible B A /\ Matching M B A -> 

        Vol(M) <= Qty_orders (supply_below_p p A) + Qty_orders (demand_above_at_p p B).
Proof. intros. apply M_bound2. all:apply H. Qed.

(* Strong version of demand-supply theorem *)
Theorem Bound_strong (p:nat)(M: list transaction)(B A:list order):
NoDup (ids B) -> NoDup (ids A) -> Matching M B A -> 
Vol(M) <= Qty_orders (supply_below_p p A) + 
          Qty_orders (demand_above_p p B) +
          minof (Nat.leb) (Qty_orders (demand_at_p p B))  (Qty_orders (supply_at_p p A)).
Proof. apply Bound. Qed.

(* Correctness of Fair procedure *)
Theorem Fair_main (M: list transaction) (B A: list order): 
        admissible B A /\ Matching M B A -> 
        
        (Matching (Fair M B A) B A) /\  (* (Fair M B A) is a matching over (B, A) *)
        (Vol(M)= Vol((Fair M B A))) /\  (* Volumes of M and (Fair M B A) are the same *)
        (Is_fair (Fair M B A) B A).     (* Process Fair produces a fair matching *)
Proof. apply Fair_main. Qed.

(* Correctness of UM procedure *)
Theorem UM_main (B A: list order) (M: list transaction):
        admissible B A -> Is_uniform M B A ->

        (Is_uniform (UM B A) B A) /\  (* UM is uniform*)
        (Is_fair (UM B A) B A) /\     (* UM is fair *)
        (Vol((UM B A)) >= Vol(M)).    (* UM is maximum amongs all uniform matchings M over (B, A) *)
Proof. intros. split. apply UM_correct. auto. split. apply UM_correct. auto. apply UM_correct. auto. auto. Qed. 

(* Correctness of MM procedure *)
Theorem MM_main (B A: list order) (M: list transaction):
        admissible B A -> Matching M B A -> 
        
        (Matching (MM B A) B A) /\ (* (MM B A) is a matching over (B, A) *)
        (Vol((MM B A)) >= Vol(M)).   (* MM has maximum volume among all matchings M *)
Proof. intros. split. apply MM_Is_Matching. auto. apply MM_optimal. all:auto. Qed. 

(* Uniqueness Theorem (completeness) *)
Theorem completeness M1 M2 B A:
        admissible B A /\ (Vol(M1) = Vol(M2)) /\
        (Matching M1 B A) /\ (Matching M2 B A) /\
        Is_fair M1 B A /\ Is_fair M2 B A ->

        (forall a, Qty_ask M1 (id a) = Qty_ask M2 (id a)) /\
        (forall b, Qty_bid M1 (id b) = Qty_bid M2 (id b)).
Proof. intros. split. intros. eapply completeness with (B:=B)(A:=A). all: try apply H.
auto. split. apply H. split. apply H. split. apply H. split. apply H. apply H. 
intros. eapply completeness with (B:=B)(A:=A). all: try apply H.
auto. split. apply H. split. apply H. split. apply H. split. apply H. apply H. 
 Qed.

(* Converse of Uniqueness Theorem *)
Theorem soundness M1 M2 B A:
        admissible B A /\ 
        (Matching M1 B A) /\ (Matching M2 B A) /\
        Is_fair M1 B A /\ (Vol(M1) = Vol(M2)) /\
        (forall a, Qty_ask M1 (id a) = Qty_ask M2 (id a)) /\
        (forall b, Qty_bid M1 (id b) = Qty_bid M2 (id b)) -> 

        Is_fair M2 B A.              (* M2 is fair matching over (B, A) *)
Proof. intros. apply soundness with (M1:=M1). all:try apply H. Qed.
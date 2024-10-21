(* Demo file for the work "Double Auction: Formalization and Automated Checkers" *)

Require Import Uniqueness.
Require Import MM.


(* Demand-supply theorem *)
Theorem Bound (p:nat)(M: list transaction)(B A:list order):
NoDup (ids B) -> NoDup (ids A) -> Matching M B A -> 
Vol(M) <=  Qty_orders (supply_below_at_p p A) + 
          Qty_orders (demand_above_at_p p B).
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


Require Extraction.

(*This part is tellling coq to extract nat, bool, additions, multiplications, equality and less than
 Into the corrsponding OCaml types. *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".
Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant Nat.eqb => "( = )".
Extract Constant Nat.leb => "(<=)".

Extraction  Language OCaml.
Extraction "Demonstration/certified.ml" UM.UM MM.MM Qty_ask Qty_bid.

Extraction  Language Haskell.
Extraction "Demonstration/certified.hs" UM.UM MM.MM Qty_ask Qty_bid.

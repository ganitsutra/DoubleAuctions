(* Demo file for the work "Double Auction: Formalization and Automated Checkers" *)

Require Import Uniqueness.
Require Import MM.


(* Demand-supply theorem *)
Theorem Bound p M B A:
admissible B A /\ Matching M B A ->
Vol(M) <= (Qty_orders (filter (fun x : order => Nat.leb p (oprice x)) B)) +
          (Qty_orders (filter (fun x : order => Nat.leb (oprice x) p) A)).

Proof. intros. destruct H. apply Bound with (p:=p) in H0. 
unfold supply_below_at_p in H0. unfold demand_above_at_p in H0. lia.
all:apply H.  Qed.


(* Correctness of Fair procedure *)
Theorem Fair_main (M: list transaction) (B A: list order):
admissible B A /\ Matching M B A ->
(Matching (Fair M B A) B A) /\
(* (Fair M B A) is a matching over (B, A) *)
(Vol(M)= Vol((Fair M B A))) /\
(* Trade volumes of M and (Fair M B A) are the same *)
(Is_fair (Fair M B A) B A).
(* Process Fair produces a fair matching *)
Proof. apply Fair_main. Qed.

(* The UM is fair and optimal-uniform algorithm. *)
Theorem UM_correct B A:
admissible B A ->
Is_fair (UM B A) B A /\ Is_optimal_uniform (UM B A) B A.
Proof. intros. split. apply UM_correct. auto. split. apply UM_correct. auto. apply UM_correct. auto. Qed. 


(* The MM is fair and maximum volume matching algorithm. *)
Theorem MM_correct B A:
admissible B A ->
Is_max (MM B A) B A /\ Is_fair (MM B A) B A.
Proof. intros. split.  apply MM_optimal. all:auto. apply MM_Is_fair. auto. Qed. 


(* Uniqueness property (completeness) *)
Theorem completeness M1 M2 B A:
admissible B A /\ (Vol(M1) = Vol(M2)) /\
(Matching M1 B A) /\ (Matching M2 B A) /\
Is_fair M1 B A /\ Is_fair M2 B A ->
(forall a, Qty_ask M1 (id a) = Qty_ask M2 (id a)) /\
(forall b, Qty_bid M1 (id b) = Qty_bid M2 (id b)).
Proof. intros. destruct H. split. intros.
      eapply completeness with (B:=B)(A:=A). 
      apply H. apply H. apply H. apply H. auto. 
      split. apply H0. split. apply H0. split. apply H0. split. apply H0.
      split. apply H0. apply H0. intros.
      eapply completeness with (B:=B)(A:=A). 
      apply H. apply H. apply H. apply H. auto. 
      split. apply H0. split. apply H0. split. apply H0. split. apply H0.
      split. apply H0. apply H0. Qed.

(* Converse uniqueness preperty *)
Theorem soundness M1 M2 B A:
admissible B A /\
(Matching M1 B A) /\ (Matching M2 B A) /\
Is_fair M2 B A /\ (Vol(M1) = Vol(M2)) /\
(forall a, Qty_ask M1 (id a) = Qty_ask M2 (id a)) /\
(forall b, Qty_bid M1 (id b) = Qty_bid M2 (id b)) ->
Is_fair M1 B A.
Proof. intros. apply soundness with (M1:=M2)(B:=B)(M2:=M1)(A:=A).
 all:try apply H. intros. symmetry. apply H. intros. symmetry. apply H. Qed.

(* The fair-on-asks correctness lemma. *)
Theorem FOA_correct B A M:
admissible B A /\ Matching M B A ->
(* (a) *)
Matching (FOA M A) B A /\
(* (b) *)
Vol(M) = Vol(FOA M A) /\
(* (c) *)
Is_fair_asks (FOA M A) A /\
(* (d) *)
(forall b, In b B -> Qty_bid M (id b) = Qty_bid (FOA M A) (id b)).
Proof. intros. apply FOA_correct in H. split. apply H. split. apply H.
split. apply H. apply H. Qed.

(* The Match subroutine outputs a matching over (B, A). *)
Lemma Match_Matching B A:
admissible B A -> Matching (Match B A) B A.
Proof. intros. apply Match_Matching. all:apply H. Qed.

(* The Match subroutine outputs a fair-on-bids matching. *)
Lemma Match_Fair_on_Bids B A:
admissible B A /\ Sorted bcompetitive B -> Is_fair_bids (Match B A) B.
Proof. apply Match_Fair_on_Bids.  Qed.

(* The Match subroutine outputs a fair-on-asks matching. *)
Lemma Match_Fair_on_Asks B A:
admissible B A /\ Sorted bcompetitive B /\ Sorted acompetitive A ->
Is_fair_asks (Match B A) A.
Proof. apply Match_Fair_on_Asks.  Qed.

(* The Match is optimal-uniform when B and A are sorted by competitiveness. *)
Lemma Match_optimal_um M B A:
admissible B A /\ Sorted bcompetitive B /\ Sorted acompetitive A /\ Is_uniform M B A
-> Vol (Match B A) >= Vol M.
Proof. intros. apply Match_OPT. all: apply H. Qed.

(* The Match is optimal when B sorted by competitiveness and A by reverse competitiveness. *)
Lemma Match_optimal_mm M B A:
admissible B A /\ Sorted bcompetitive B /\ Sorted rev_acompetitive A /\ Is_uniform M B A
-> Vol (Match B A) >= Vol M.
Proof. intros. apply MM_aux_optimal. all: apply H. Qed.


(* Correctness of UM procedure: Another form *)
Theorem UM_main (B A: list order) (M: list transaction):
        admissible B A -> Is_uniform M B A ->

        (Is_uniform (UM B A) B A) /\  (* UM is uniform*)
        (Is_fair (UM B A) B A) /\     (* UM is fair *)
        (Vol((UM B A)) >= Vol(M)).    (* UM is maximum amongs all uniform matchings M over (B, A) *)
Proof. intros. split. apply UM_correct. auto. split. apply UM_correct. auto. apply UM_correct. auto. auto. Qed. 

(* Correctness of MM procedure: Another form *)
Theorem MM_main (B A: list order) (M: list transaction):
        admissible B A -> Matching M B A -> 
        
        (Matching (MM B A) B A) /\ (* (MM B A) is a matching over (B, A) *)
        (Vol((MM B A)) >= Vol(M)).   (* MM has maximum volume among all matchings M *)
Proof. intros. split. apply MM_Is_Matching. auto. apply MM_optimal. all:auto. Qed. 



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

Require Import List Setoid Permutation  Orders.
Require Export Competitive.
Require Export List Coq.Sorting.Mergesort Sorted.

Open Scope bool_scope.

(*Local Coercion is_true : bool >-> Sortclass.*)


Module SortB <:  TotalTransitiveLeBool'.

Definition t := order.

Definition leb t1 t2 := bcompetitive t1 t2.

Theorem leb_total : forall a1 a2, leb a1 a2 \/ leb a2 a1.
Proof. intros. unfold leb. unfold bcompetitive. destruct a1. destruct a2. simpl. 
assert((oprice0 = oprice)\/(oprice0 < oprice)\/(oprice < oprice0)). lia. destruct H.
              subst. assert(Nat.ltb oprice oprice = false). apply /ltP. lia. rewrite H. simpl.
              assert(Nat.eqb oprice oprice =true). auto. rewrite H0. simpl. 
              assert((otime0 <= otime)\/(otime < otime0)). lia. destruct H1.
              right. apply /leP. auto. left. apply /leP. lia.
              destruct H. left. apply /orP. left. apply /ltP. auto. right.
              apply /orP. left. apply /ltP. auto. Qed.

(*Transitivity is needed here hence change the module that include transitivity and compare*)
Lemma leb_trans : Transitive leb.
Proof. { unfold Transitive. unfold leb. unfold bcompetitive.
            intros y x z H H1. move /orP in H1. move /orP in H.
            apply /orP. destruct H1;destruct H. 
            { left. move /leP in H0. move /leP in H. apply /leP. lia. }
            { move /andP in H. destruct H. left.  
              move /leP in H0. move /eqP in H. apply /leP. lia. }
            { move /andP in H0. destruct H0. left.
              move /leP in H. move /eqP in H0. apply /leP. lia. }
            { move /andP in H0. move /andP in H. destruct H0. destruct H.
              right.
              move /eqP in H. move /eqP in H0. apply /andP.
              split. apply /eqP. lia. apply /leP. move /leP in H1. 
              move /leP in H2. lia. } } Qed.

End SortB.

Module Decr_Bid := Sort SortB.


Module SortA <:  TotalTransitiveLeBool'.

Definition t := order.

Definition leb t1 t2 := acompetitive t1 t2.

Theorem leb_total : forall a1 a2, leb a1 a2 \/ leb a2 a1.
Proof. intros. unfold leb. unfold acompetitive. destruct a1. destruct a2. simpl. 
assert((oprice0 = oprice)\/(oprice0 < oprice)\/(oprice < oprice0)). lia. destruct H.
subst. assert(Nat.ltb oprice oprice = false). apply /ltP. lia. rewrite H. simpl.
assert(Nat.eqb oprice oprice =true). auto. rewrite H0. simpl. 
assert((otime0 <= otime)\/(otime < otime0)). lia. destruct H1.
right. apply /leP. auto. left. apply /leP. lia.
destruct H. right. apply /orP. left. apply /ltP. auto. left.
apply /orP. left. apply /ltP. auto. Qed.

(*Transitivity is needed here hence change the module that include transitivity and compare*)
Lemma leb_trans : Transitive leb.
Proof. { unfold Transitive. unfold leb. unfold acompetitive.
            intros y x z H H1. move /orP in H1. move /orP in H.
            apply /orP. destruct H1;destruct H. 
            { left. move /leP in H0. move /leP in H. apply /leP. lia. }
            { move /andP in H. destruct H. left.  
              move /leP in H0. move /eqP in H. apply /leP. lia. }
            { move /andP in H0. destruct H0. left.
              move /leP in H. move /eqP in H0. apply /leP. lia. }
            { move /andP in H0. move /andP in H. destruct H0. destruct H.
              right.
              move /eqP in H. move /eqP in H0. apply /andP.
              split. apply /eqP. lia. apply /leP. move /leP in H1. 
              move /leP in H2. lia. } } Qed.

End SortA.

Module Incr_Ask := Sort SortA.


Module SortA_rev <:  TotalTransitiveLeBool'.

Definition t := order.

Definition leb t1 t2 := rev_acompetitive t1 t2.

Theorem leb_total : forall a1 a2, leb a1 a2 \/ leb a2 a1.
Proof. intros. unfold leb. unfold rev_acompetitive. 
destruct a1. destruct a2. simpl. 
assert((oprice0 = oprice)\/(oprice0 < oprice)\/(oprice < oprice0)). 
lia. destruct H.
subst. assert(Nat.ltb oprice oprice = false). apply /ltP. lia. rewrite H. simpl.
assert(Nat.eqb oprice oprice = true). auto. rewrite H0. simpl. 
assert((otime0 <= otime)\/(otime < otime0)). lia. destruct H1.
left. apply /leP. auto. right. apply /leP. lia.
destruct H. left. apply /orP. left. apply /ltP. auto. right.
apply /orP. left. apply /ltP. auto. Qed.

(*Transitivity is needed here hence change the module that include transitivity and compare*)
Lemma leb_trans : Transitive leb.
Proof. { unfold Transitive. unfold leb. unfold acompetitive.
            intros y x z H H1. move /orP in H1. move /orP in H.
            apply /orP. destruct H1;destruct H. 
            { left. move /leP in H0. move /leP in H. apply /leP. lia. }
            { move /andP in H. destruct H. left.  
              move /leP in H0. move /eqP in H. apply /leP. lia. }
            { move /andP in H0. destruct H0. left.
              move /leP in H. move /eqP in H0. apply /leP. lia. }
            { move /andP in H0. move /andP in H. destruct H0. destruct H.
              right.
              move /eqP in H. move /eqP in H0. apply /andP.
              split. apply /eqP. lia. apply /leP. move /leP in H1. 
              move /leP in H2. lia. } } Qed.

End SortA_rev.

Module Decr_Ask := Sort SortA_rev.

Module TranSortD <: TotalLeBool.

Definition t := transaction.
(*
Fixpoint lebnat x y :=
    match x, y with
    | 0, _ => true
    | _, 0 => false
    | S x', S y' => lebnat x' y'
    end.
  Infix "<=?" := lebnat (at level 70, no associativity).

Definition leb t1 t2 := lebnat (tprice t1) (tprice t2).
*)
Definition leb t1 t2 := incr_price t1 t2.

Theorem leb_total : forall a1 a2, leb a1 a2 \/ leb a2 a1.
Proof. unfold leb. unfold incr_price. induction a1;destruct a2 ; simpl; auto.
 destruct (Nat.leb tprice0 tprice) eqn:H1. auto. move /leP in H1. right. apply /leP. lia.  Qed.

Lemma leb_trans : Transitive leb.
Proof. { unfold Transitive. unfold leb. unfold incr_price.
            intros y x z H H1. 
            move /leP in H1. move /leP in H. apply /leP. lia. } Qed.

(*Transitivity is needed here hence change the module that include transitivity and compare*)

End TranSortD.

Module Decr_M := Sort TranSortD.

Module TAPSort := Sort TranSortD.


Module TranSortI <: TotalLeBool.

Definition t := transaction.
(*
Fixpoint gebnat x y :=
    match x, y with
    | _, 0 => true
    | 0, _ => false
    | S x', S y' => gebnat x' y'
    end.
  Infix ">=?" := gebnat (at level 70, no associativity).

Definition leb t1 t2 := gebnat (tprice t1) (tprice t2).
*)

Definition leb t1 t2 := dec_price t1 t2.
Theorem leb_total : forall a1 a2, leb a1 a2 \/ leb a2 a1.
Proof. intros.  unfold leb. unfold dec_price.  destruct a1. destruct a2. simpl. 
destruct (Nat.leb tprice tprice0) eqn:H1. auto. right. move /leP in H1. apply /leP.
lia. Qed.

Lemma leb_trans : Transitive leb.
Proof. { unfold Transitive. unfold leb. unfold dec_price.
            intros y x z H H1. 
            move /leP in H1. move /leP in H. apply /leP. lia. } Qed.
 
End TranSortI.

Module Incr_M := Sort TranSortI.

Section Sorting.

Lemma count_occ_countM (M:list transaction) a:
count a M = count_occ trd_eqbP M a.
Proof. induction M. simpl. auto. simpl. destruct (t_eqb a a0) eqn:H1;destruct (trd_eqbP a0 a) eqn:H2.
lia. move/eqP in H1. destruct n. auto. move/eqP in H1. destruct H1. auto. lia. Qed.
 
Lemma count_occ_count (B:list order) a:
count a B = count_occ ord_eqbP B a.
Proof. induction B. simpl. auto. simpl. destruct (ord_eqb a a0) eqn:H1;destruct (ord_eqbP a0 a) eqn:H2.
lia. move/eqP in H1. destruct n. auto. move/eqP in H1. destruct H1. auto. lia. Qed.


Lemma Permulation_perm (B1 B2:list order):
Permutation B1 B2 <-> perm B1 B2.
Proof. split. intro. apply perm_intro. intros.
eapply Permutation_count_occ with (x:=a) in H. rewrite <- count_occ_count in H. rewrite <- count_occ_count in H.
 auto. intro. eapply Permutation_count_occ. intro. rewrite <- count_occ_count. rewrite <- count_occ_count.
apply perm_elim with (a:=x) in H. auto. Qed.

Lemma Permutation_permM (M1 M2:list transaction):
Permutation M1 M2 <-> perm M1 M2.
Proof. split. intro. apply perm_intro. intros.
eapply Permutation_count_occ in H.  rewrite <- count_occ_countM in H. rewrite <- count_occ_countM in H.
exact H. intro. eapply Permutation_count_occ. intro. rewrite <- count_occ_countM. rewrite <- count_occ_countM.
apply perm_elim with (a:=x) in H. auto. Qed.


Lemma Sorted_tintroD (M: list transaction)(m: transaction):
Sorted dec_price (m::M) -> forall t, In t M -> (Nat.leb (tprice m) (tprice t)).
Proof. intros. apply Sorted_extends in H. 
apply Forall_forall with (x:= t) in H.
auto. auto. unfold Relations_1.Transitive.
unfold dec_price. intros. move /leP in H1. move /leP in H2.
apply /leP. auto. lia. Qed.

Lemma Sorted_tintroI (M: list transaction)(m: transaction):
Sorted incr_price (m::M) -> forall t, In t M -> (Nat.leb (tprice t) (tprice m)).
Proof. intros. apply Sorted_extends in H. 
apply Forall_forall with (x:= t) in H.
auto. auto. unfold Relations_1.Transitive.
unfold incr_price. intros. move /leP in H1. move /leP in H2.
apply /leP. auto. lia. Qed.

Lemma Sorted_ointroB (B: list order)(b: order):
Sorted bcompetitive (b::B) -> forall x, In x B -> (Nat.leb (oprice x) (oprice b)).
Proof. intros. apply Sorted_extends in H. 
apply Forall_forall with (x:= x) in H. 
unfold bcompetitive in  H.  move /orP in H. destruct H. 
move /ltP in H. apply /leP. lia. move /andP in H. destruct H.
move /eqP in H. apply /leP. lia. auto. unfold Relations_1.Transitive.
assert (Ht:transitive bcompetitive). apply bcompetitive_P.
unfold transitive in Ht. intros. specialize (Ht y x0 z).
auto. Qed.

Lemma Sorted_ointroB_tight (B: list order)(b: order):
Sorted bcompetitive (b::B) -> forall x, In x B -> bcompetitive b x. 
Proof. intros. apply Sorted_extends in H. 
apply Forall_forall with (x:= x) in H. all:auto. unfold Relations_1.Transitive.
assert (Ht:transitive bcompetitive). apply bcompetitive_P.
unfold transitive in Ht. intros. specialize (Ht y x0 z).
auto. Qed.


Lemma Sorted_ointroA (A: list order)(a: order):
Sorted acompetitive (a::A) -> forall x, In x A -> (Nat.leb (oprice a) (oprice x)).
Proof. intros. apply Sorted_extends in H. 
apply Forall_forall with (x:= x) in H. 
unfold acompetitive in  H.  move /orP in H. destruct H. 
move /ltP in H. apply /leP. lia. move /andP in H. destruct H.
move /eqP in H. apply /leP. lia. auto. unfold Relations_1.Transitive.
assert (Ht:transitive acompetitive). apply acompetitive_P.
unfold transitive in Ht. intros. specialize (Ht y x0 z).
auto. Qed.

Lemma Sorted_ointroA_tight (A: list order)(a: order):
Sorted acompetitive (a::A) -> forall x, In x A -> acompetitive a x.
Proof. intros. apply Sorted_extends in H. 
apply Forall_forall with (x:= x) in H. all:auto. unfold Relations_1.Transitive.
assert (Ht:transitive acompetitive). apply acompetitive_P.
unfold transitive in Ht. intros. specialize (Ht y x0 z).
auto. Qed.

Lemma Sorted_ointro_not_A_tight (A: list order)(a: order):
Sorted rev_acompetitive (a::A) -> forall x, In x A -> acompetitive x a.
Proof. intros. apply Sorted_extends in H. 
apply Forall_forall with (x:= x) in H. all:auto. 
apply SortA_rev.leb_trans. Qed.

Lemma Sorted_ointro_not_A (A: list order)(a: order):
Sorted rev_acompetitive (a::A) -> 
forall x, In x A -> (Nat.leb (oprice x) (oprice a)).
Proof. intros. apply Sorted_ointro_not_A_tight with (x:=x) in H. 
unfold acompetitive in  H.  move /orP in H. destruct H. 
move /ltP in H. apply /leP. lia. move /andP in H. destruct H.
move /eqP in H. apply /leP. lia. auto.  Qed.

Lemma Sortedtail (B: list order)(b: order):
Sorted bcompetitive (b::B) -> Sorted bcompetitive B.
Proof. intros. apply Sorted_inv in H. apply H. Qed.

Lemma SortedreducedB (B: list order)(b b': order):
(oprice b = oprice b') -> (otime b = otime b') -> Sorted bcompetitive (b::B) -> Sorted bcompetitive (b'::B).
Proof. intros. apply Sorted_inv in H1. apply Sorted_cons. apply H1.
destruct H1. induction B. auto. apply HdRel_inv in H2.
apply HdRel_cons. unfold bcompetitive in H2. unfold bcompetitive. rewrite <- H.  rewrite <- H0.
auto. Qed.

Lemma SortedreducedA (A: list order)(a a': order):
(oprice a = oprice a') -> (otime a = otime a') -> Sorted acompetitive (a::A) -> Sorted acompetitive (a'::A).
Proof. intros. apply Sorted_inv in H1. apply Sorted_cons. apply H1.
destruct H1. induction A. auto. apply HdRel_inv in H2.
apply HdRel_cons. unfold acompetitive in H2. unfold acompetitive. rewrite <- H.  rewrite <- H0.
auto. Qed.

Lemma SortedreducedA_rev (A: list order)(a a': order):
(oprice a = oprice a') -> (otime a = otime a') -> 
Sorted rev_acompetitive (a::A) -> Sorted rev_acompetitive (a'::A).
Proof. intros. apply Sorted_inv in H1. apply Sorted_cons. apply H1.
destruct H1. induction A. auto. apply HdRel_inv in H2.
apply HdRel_cons. unfold rev_acompetitive in H2. unfold rev_acompetitive.
rewrite <- H.  rewrite <- H0. auto. Qed.

Lemma SortedreducedMD (M: list transaction)(m m': transaction):
(tprice m = tprice m') -> Sorted dec_price (m::M) -> Sorted dec_price (m'::M).
Proof. intros. apply Sorted_inv in H0. apply Sorted_cons. apply H0.
destruct H0. induction M. auto. apply HdRel_inv in H1.
apply HdRel_cons. unfold dec_price in H1. unfold dec_price. rewrite <- H. auto. Qed.

Lemma SortedreducedMI (M: list transaction)(m m': transaction):
(tprice m = tprice m') -> Sorted incr_price (m::M) -> Sorted incr_price (m'::M).
Proof. intros. apply Sorted_inv in H0. apply Sorted_cons. apply H0.
destruct H0. induction M. auto. apply HdRel_inv in H1.
apply HdRel_cons. unfold incr_price in H1. unfold incr_price. rewrite <- H. auto. Qed.

Lemma Sorted_perm_acomp_equal A A' (ndt: NoDup (timesof A)): 
Sorted (fun a a' : order => acompetitive a a') A -> 
Sorted (fun a a' : order => acompetitive a a') A' -> 
Permutation A A' ->
A = A'.
Proof. revert A'. induction A. intros. symmetry.  apply Permutation_nil. 
auto. intros. case A' eqn:HA'. apply Permutation_sym in H1. apply Permutation_nil_cons in H1.
inversion H1. assert(In o (a::A)). eapply Permutation_in.
apply Permutation_sym in H1. exact H1. auto.
assert(In a (o::l)). eapply Permutation_in.
exact H1. auto. 
assert(a = o). 
simpl in H2. simpl in H3. destruct H2;destruct H3. 
all:auto.
apply Sorted_ointroA_tight with (x:=o) in H.
apply Sorted_ointroA_tight with (x:=a) in H0. 
unfold acompetitive in H.  unfold acompetitive in H0.
move /orP in H. move /orP in H0.
destruct H;destruct H0.
move /ltP in H. move /ltP in H0. lia.
move /andP in H0. destruct H0. move /eqP in H0. move /ltP in H. lia.
move /andP in H. destruct H. move /eqP in H. move /ltP in H0. lia.
move /andP in H0. destruct H0. move /leP in H4. move /andP in H. destruct H. move /leP in H5.
     apply nodup_timesof_uniq_order with (B:= a::A). auto. auto. auto. lia. all:auto. 
rewrite H4 in H1.
apply Permutation_cons_inv in H1. rewrite H4. f_equal. apply IHA. eauto. 
apply Sorted_inv in H. apply H.
apply Sorted_inv in H0. apply H0.
auto. Qed.


Lemma Sorted_sortA A:
NoDup (timesof A) -> Sorted (fun a a' : order => acompetitive a a') A
-> A = Incr_Ask.sort A.
Proof. intros. apply Sorted_perm_acomp_equal. all:auto. apply Incr_Ask.Sorted_sort.
apply Incr_Ask.Permuted_sort. Qed.


Lemma Sorted_perm_bcomp_equal A A' (ndt: NoDup (timesof A)): 
Sorted (fun a a' : order => bcompetitive a a') A -> 
Sorted (fun a a' : order => bcompetitive a a') A' -> 
Permutation A A' ->
A = A'.
Proof. revert A'. induction A. intros. symmetry.  apply Permutation_nil. 
auto. intros. case A' eqn:HA'. apply Permutation_sym in H1. apply Permutation_nil_cons in H1.
inversion H1. assert(In o (a::A)). eapply Permutation_in.
apply Permutation_sym in H1. exact H1. auto.
assert(In a (o::l)). eapply Permutation_in.
exact H1. auto. 
assert(a = o). 
simpl in H2. simpl in H3. destruct H2;destruct H3. 
all:auto.
apply Sorted_ointroB_tight with (x:=o) in H.
apply Sorted_ointroB_tight with (x:=a) in H0. 
unfold bcompetitive in H.  unfold bcompetitive in H0.
move /orP in H. move /orP in H0.
destruct H;destruct H0.
move /ltP in H. move /ltP in H0. lia.
move /andP in H0. destruct H0. move /eqP in H0. move /ltP in H. lia.
move /andP in H. destruct H. move /eqP in H. move /ltP in H0. lia.
move /andP in H0. destruct H0. move /leP in H4. move /andP in H. destruct H. move /leP in H5.
     apply nodup_timesof_uniq_order with (B:= a::A). auto. auto. auto. lia. all:auto. 
rewrite H4 in H1.
apply Permutation_cons_inv in H1. rewrite H4. f_equal. apply IHA. eauto. 
apply Sorted_inv in H. apply H.
apply Sorted_inv in H0. apply H0.
auto. Qed.


Lemma Sorted_sortB B:
NoDup (timesof B) -> Sorted (fun b b' : order => bcompetitive b b') B
-> B = Decr_Bid.sort B.
Proof. intros. apply Sorted_perm_bcomp_equal. all:auto. apply Decr_Bid.Sorted_sort.
apply Decr_Bid.Permuted_sort. Qed.



Lemma Sorted_perm_rev_acomp_equal A A' (ndt: NoDup (timesof A)): 
Sorted (fun a a' : order => rev_acompetitive a a') A -> 
Sorted (fun a a' : order => rev_acompetitive a a') A' -> 
Permutation A A' ->
A = A'.
Proof. revert A'. induction A. intros. symmetry.  apply Permutation_nil. 
auto. intros. case A' eqn:HA'. apply Permutation_sym in H1. apply Permutation_nil_cons in H1.
inversion H1. assert(In o (a::A)). eapply Permutation_in.
apply Permutation_sym in H1. exact H1. auto.
assert(In a (o::l)). eapply Permutation_in.
exact H1. auto. 
assert(a = o). 
simpl in H2. simpl in H3. destruct H2;destruct H3. 
all:auto.
apply Sorted_ointro_not_A_tight with (x:=o) in H.
apply Sorted_ointro_not_A_tight with (x:=a) in H0. 
unfold acompetitive in H.  unfold acompetitive in H0.
move /orP in H. move /orP in H0.
destruct H;destruct H0.
move /ltP in H. move /ltP in H0. lia.
move /andP in H0. destruct H0. move /eqP in H0. move /ltP in H. lia.
move /andP in H. destruct H. move /eqP in H. move /ltP in H0. lia.
move /andP in H0. destruct H0. move /leP in H4. move /andP in H. destruct H. move /leP in H5.
     apply nodup_timesof_uniq_order with (B:= a::A). auto. auto. auto. lia. all:auto. 
rewrite H4 in H1.
apply Permutation_cons_inv in H1. rewrite H4. f_equal. apply IHA. eauto. 
apply Sorted_inv in H. apply H.
apply Sorted_inv in H0. apply H0.
auto. Qed.


Lemma Sorted_sortA_rev A:
NoDup (timesof A) -> Sorted (fun a a' : order => rev_acompetitive a a') A
-> A = Decr_Ask.sort A.
Proof. intros. apply Sorted_perm_rev_acomp_equal. all:auto. 
apply Decr_Ask.Sorted_sort.
apply Decr_Ask.Permuted_sort. Qed.


Lemma ids_map B:
map id B = ids B.
Proof. induction B. simpl. auto. simpl. f_equal. Qed.

Lemma SortA_perm B:
perm (Incr_Ask.sort B) B.
Proof. apply Permulation_perm. apply Permutation_sym. apply Incr_Ask.Permuted_sort. Qed.

Lemma SortB_perm B:
perm (Decr_Bid.sort B) B.
Proof. apply Permulation_perm. apply Permutation_sym. apply Decr_Bid.Permuted_sort. Qed.

Lemma SortB_NoDup B:
NoDup (ids B) -> NoDup (ids (Decr_Bid.sort B)).
Proof. intros. assert(H1:perm (Decr_Bid.sort B) B).
apply SortB_perm.
apply Permulation_perm in H1.
apply Permutation_map with (f:=id) in H1. rewrite ids_map in H1. rewrite ids_map in H1.
eapply  Permutation_NoDup. apply Permutation_sym. exact H1. auto. Qed.

Lemma SortA_NoDup A:
NoDup (ids A) -> NoDup (ids (Incr_Ask.sort A)).
Proof. intros. assert(H1:perm (Incr_Ask.sort A) A).
apply SortA_perm.
apply Permulation_perm in H1.
apply Permutation_map with (f:=id) in H1. rewrite ids_map in H1. rewrite ids_map in H1.
eapply  Permutation_NoDup. apply Permutation_sym. exact H1. auto. Qed.

Lemma SortA_NoDup_rev A:
NoDup (ids A) -> NoDup (ids (Decr_Ask.sort A)).
Proof. intros. assert(H1:perm (Decr_Ask.sort A) A).
apply Permulation_perm. apply Permutation_sym. apply Decr_Ask.Permuted_sort.
apply Permulation_perm in H1.
apply Permutation_map with (f:=id) in H1. rewrite ids_map in H1. rewrite ids_map in H1.
eapply  Permutation_NoDup. apply Permutation_sym. exact H1. auto. Qed.

End Sorting.

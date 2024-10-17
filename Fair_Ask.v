
(*Commnet Here*)


Require Import Wellfounded.
Require Import List Setoid Permutation  Orders.
Require Import Coq.Logic.Eqdep_dec Coq.Arith.Compare_dec Coq.Arith.PeanoNat.
From Equations Require Export Equations.
Require Export Competitive.
Require Export Demand_suppy_Inequality.
Require Export Coq.Sorting.Mergesort Sorted SortLists.


Section Fair_Ask.

Lemma liaforrun (b a : order): 
oquantity b < oquantity a -> 
~ (oquantity a - oquantity b < 1). lia. Qed.

Lemma liaforrun2 (a : order)(m: transaction): 
tquantity m < oquantity a ->
~ oquantity a - tquantity m < 1. lia. Qed.

Lemma liaforrun3 (a : order)(m: transaction): 
 oquantity a < tquantity m ->
~ tquantity m - oquantity a < 1. lia. Qed.


Equations foo (fuel :list nat) (xs : list nat) : (list nat) by wf ((length fuel) + (length xs)) :=
  foo nil xs := nil;
  foo fuel nil := nil;
  foo (a::fuel) (b :: xs') := if Nat.ltb a b then foo (a::fuel) xs' else foo fuel (b :: xs').
Next Obligation.
induction xs'; (cbn; lia).
Qed.

Equations FOA_aux (M:list transaction) (A: list order): 
(list transaction) by wf ((length M) + (length A)) :=  
FOA_aux nil _ := nil;
FOA_aux _ nil := nil;
FOA_aux (m::M) (a::A) := match (Compare_dec.lt_eq_lt_dec (tquantity m) (oquantity a)) with
    |inleft (right _) =>  (Mk_transaction (idb m) (id a) (tprice m) (oquantity a) (oquantity_cond a))::
                                                                                                  (FOA_aux M A) 
    |inleft (left _) =>  ((Mk_transaction (idb m) (id a) (tprice m) (tquantity m) (tquantity_cond m)):: (FOA_aux M ((Mk_order (id a) (otime a) (oquantity a - tquantity m) (oprice a) _ ) :: A)))
    |inright _ =>  (Mk_transaction (idb m) (id a) (tprice m) (oquantity a) (oquantity_cond a))::
                        (FOA_aux ((Mk_transaction (idb m) (ida m) (tprice m) (tquantity m - oquantity a) _ )::M) A)
    end.

Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. apply liaforrun2;auto. Defined.  
Next Obligation. lia. Defined.
Next Obligation. apply PeanoNat.Nat.ltb_nlt. apply liaforrun3;auto. Defined.
Next Obligation. lia. Defined.

 Lemma test_FOA (M:list transaction) (A: list order):
length M + length A >= length (FOA_aux M A).
Proof. 
apply FOA_aux_elim. simpl. lia. simpl. lia. simpl. intros.
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. destruct s eqn:f2.
specialize (H s). specialize (H l). simpl. simpl in H. lia.
specialize (H0 s). simpl. lia.
specialize (H1 l). simpl. lia.
Qed.

Lemma Vol_FOA (M:list transaction) (A: list order):
Qty_orders A >= Vol (M) -> Vol (M) = Vol (FOA_aux M A).
Proof. 
apply FOA_aux_elim. simpl. lia. simpl. lia. simpl. intros.
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. destruct s eqn:f2.
specialize (H s). specialize (H l). simpl. simpl in H. lia.
specialize (H0 s). simpl. lia.
specialize (H1 l). simpl. lia.
Qed.

Lemma Qty_ask_FOA_zero (M:list transaction) (A: list order) (a1:order):
~ In (id a1) (ids A) -> Qty_ask (FOA_aux M A) (id a1) = 0.
Proof.
apply FOA_aux_elim. 
{ simpl. auto. }
{ simpl. auto. }
{ simpl. intros. 
  destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1.   
  { destruct s eqn:f2.
    { simpl. assert (Ha1:~ (id a = id a1)). apply Decidable.not_or in H2. apply H2. assert(Ha2: ~In (id a1) (ids A0)).
      apply Decidable.not_or in H2. apply H2. destruct (id a =? id a1) eqn:Ha. move /eqP in Ha. lia. 
      apply H. all:auto.
  }
  { simpl. simpl. assert (Ha1:~ (id a = id a1)). apply Decidable.not_or in H2. apply H2. 
    assert(Ha2: ~In (id a1) (ids A0)). apply Decidable.not_or in H2. apply H2.
    destruct (id a =? id a1) eqn:Ha. move /eqP in Ha. lia.  apply H0. all:auto.
  }
}
{ simpl. assert (Ha1:~ (id a = id a1)). apply Decidable.not_or in H2. apply H2. assert(Ha2: ~In (id a1) (ids A0)). 
  apply Decidable.not_or in H2. apply H2. destruct (id a =? id a1) eqn:Ha. move /eqP in Ha. lia. apply H1. all:auto.
}} Qed. 

Lemma Subset_asks_FOA (M:list transaction) (A: list order):
Subset (ids_ask_aux (FOA_aux M A)) (ids A).
Proof. 
apply FOA_aux_elim. 
{ simpl. auto. }
{ simpl. auto. }
{ simpl. intros. 
  destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1.   
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. simpl in H.
      unfold "[<=]". intros. unfold "[<=]" in H.
      simpl in H2. destruct H2. simpl. auto. apply H in H2. auto.
    }
    { specialize (H0 s). simpl. apply Subset_intro. apply H0. auto. }
  }
  { specialize (H1 l). simpl. 
    apply Subset_intro. apply H1.
  }
} Qed.


Lemma Subset_bids_FOA (M:list transaction) (A: list order):
Subset (ids_bid_aux (FOA_aux M A)) (ids_bid_aux M).
Proof. 
apply FOA_aux_elim. 
{ simpl. auto. }
{ simpl. auto. }
{ simpl. intros. 
  destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1.   
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. unfold "[<=]". intros. unfold "[<=]" in H.
      simpl in H2. destruct H2. simpl. auto. simpl. right. apply H. auto. } 
    { specialize (H0 s). simpl. apply Subset_intro. apply H0. auto. }
  }
  { specialize (H1 l). unfold "[<=]". intros. unfold "[<=]" in H1.
    simpl in H2. destruct H2. simpl. auto. apply H1 in H2. auto. 
  }
} Qed.

(*
Lemma Equal_bids_FOA (M:list transaction) (A: list order):
Qty_orders A >= Vol (M) -> (ids_bid_aux (FOA_aux M A)) = (ids_bid_aux M).
Proof. 
apply FOA_aux_elim. 
{ simpl. auto. }
{ simpl. intros. destruct t. simpl in H. assert(HH:=tquantity_cond). 
move /ltP in HH. lia. }
{ simpl. intros. 
  destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1.   
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. f_equal.  apply H. lia. } 
    { specialize (H0 s). simpl. f_equal. apply H0. auto. lia. }
  }
  { specialize (H1 l). simpl in H1. destruct H1. lia. simpl. simpl. auto. apply H1 in H2. auto. 
  }
} Qed.
*)

Lemma Qty_ask_FOA_a (M:list transaction) (A: list order) (a: order):
NoDup (ids (a::A)) -> Qty_ask (FOA_aux M (a::A)) (id a) <= oquantity a.
Proof. revert A a. induction M as [| m M]. intros A a H. rewrite FOA_aux_equation_1. simpl. lia. 
intros A a H. rewrite FOA_aux_equation_3. simpl.
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. replace (id a =? id a) with true. 
    set (a0:= {|id := id a;otime := otime a;oquantity := oquantity a - tquantity m;oprice := oprice a; oquantity_cond := FOA_aux_obligations_obligation_1 m a l|}). 
    replace (id a) with (id a0). cut (Qty_ask (FOA_aux M (a0 :: A)) (id a0) <= oquantity a0).
    simpl. lia. simpl. subst a0. simpl. apply IHM in H as HM. set (a0:= {|id := id a;otime := otime a;oquantity := oquantity a - tquantity m;oprice := oprice a; oquantity_cond := FOA_aux_obligations_obligation_1 m a l|}). replace (id a) with (id a0). apply (IHM A a0). all:auto.
  }
  { simpl. replace (id a =? id a) with true. rewrite Qty_ask_FOA_zero. intro.
    simpl in H. apply NoDup_cons_iff in H.
    destruct H. destruct H. auto. lia. auto.
  }
}
{ simpl. replace (id a =? id a) with true. rewrite Qty_ask_FOA_zero.
 intro.
    simpl in H. apply NoDup_cons_iff in H.
    destruct H. destruct H. auto. lia. auto. }Qed. 

Lemma Qty_ask_FOA_a_rev (M:list transaction) (A: list order) (a: order):
Vol M >= oquantity a -> NoDup (ids (a::A)) -> Qty_ask (FOA_aux M (a::A)) (id a) = oquantity a.
Proof. revert A a. induction M as [| m M]. intros A a Volume0 H. rewrite FOA_aux_equation_1. simpl. 
simpl in Volume0. lia. 
intros A a Volume0 H. rewrite FOA_aux_equation_3. simpl.
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. replace (id a =? id a) with true. 
    set (a0:= {|id := id a;otime := otime a;oquantity := oquantity a - tquantity m;oprice := oprice a; oquantity_cond := FOA_aux_obligations_obligation_1 m a l|}). 
    simpl. replace (id a) with (id a0). rewrite IHM. simpl in Volume0. subst a0. simpl. 
    lia. all:simpl;auto. lia.
  }
  { simpl. replace (id a =? id a) with true. cut(Qty_ask (FOA_aux M A) (id a) = 0).
    lia. apply Qty_ask_t_zero. intro Hin. apply Subset_asks_FOA in Hin. simpl in H. apply NoDup_cons_iff in H.
    destruct H. destruct H. auto. auto.
  }
}
{ simpl. replace (id a =? id a) with true. rewrite Qty_ask_t_zero.
  intro Hin. apply Subset_asks_FOA in Hin. simpl in H. apply NoDup_cons_iff in H.
  destruct H. destruct H. auto. simpl in Volume0. lia. auto.
}Qed. 


Lemma Qty_ask_FOA_a_rev_less (M:list transaction) (A: list order) (a: order):
Vol M < oquantity a -> NoDup (ids (a::A)) -> Qty_ask (FOA_aux M (a::A)) (id a) = Vol (M).
Proof. revert A a. induction M as [| m M]. intros A a Volume0 H. rewrite FOA_aux_equation_1. simpl. 
simpl in Volume0. lia. 
intros A a Volume0 H. rewrite FOA_aux_equation_3. simpl.
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. replace (id a =? id a) with true. 
    set (a0:= {|id := id a;otime := otime a;oquantity := oquantity a - tquantity m;oprice := oprice a; oquantity_cond := FOA_aux_obligations_obligation_1 m a l|}). 
    simpl. replace (id a) with (id a0). rewrite IHM. simpl in Volume0. subst a0. simpl. 
    lia. all:simpl;auto.
  }
  { simpl. replace (id a =? id a) with true. simpl in Volume0. lia. auto. } 
}
{ simpl. replace (id a =? id a) with true. rewrite Qty_ask_t_zero.
  intro Hin. apply Subset_asks_FOA in Hin. simpl in H. apply NoDup_cons_iff in H.
  destruct H. destruct H. auto. simpl in Volume0. lia. auto.
}Qed. 


Lemma Qty_ask_FOA (M:list transaction) (A: list order):
NoDup (ids A) -> (forall a : order, In a A -> Qty_ask (FOA_aux M A) (id a) <= oquantity a).
Proof. 
apply FOA_aux_elim. simpl. lia. simpl. lia. simpl. intros.
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. 
{ destruct s eqn:f2.
  { destruct H3. subst a0. simpl.  replace (id a =? id a) with true.
    simpl. set (a1:= {|id := id a;otime := otime a;oquantity := oquantity a - tquantity m;oprice := oprice a; oquantity_cond := FOA_aux_obligations_obligation_1 m a l|}).
     cut (Qty_ask (FOA_aux M0 (a1 :: A0)) (id a) <= oquantity a - tquantity m).
     simpl. lia. replace (id a) with (id a1). apply Qty_ask_FOA_a. auto. subst a1. all:simpl;auto.
     destruct (id a =? id a0) eqn:Ha. move /eqP in Ha. apply ids_intro in H3.
     rewrite <- Ha in H3. apply NoDup_cons_iff in H3. inversion H3. all:auto.
  }
  { destruct H3. subst a0. simpl.  replace (id a =? id a) with true. 
    rewrite Qty_ask_FOA_zero. intro. simpl in H. apply NoDup_cons_iff in H3. inversion H3.
    auto. lia. auto. simpl. destruct (id a =? id a0) eqn:Haa. 
    move /eqP in Haa. apply ids_intro in H3.
    rewrite <- Haa in H3. apply NoDup_cons_iff in H3. inversion H3.
     auto. apply H0.  auto. auto. eauto. auto.
  }
}
{ destruct H3. subst a0. simpl.  replace (id a =? id a) with true.
    simpl. rewrite Qty_ask_t_zero. intro Hin. apply Subset_asks_FOA in Hin. simpl in H2. apply NoDup_cons_iff in H2.
    destruct H2. destruct H2. auto. lia. auto. simpl. 
    destruct (id a =? id a0) eqn:Ha. move /eqP in Ha. apply ids_intro in H3.
    rewrite <- Ha in H3. apply NoDup_cons_iff in H3. inversion H3. 
     auto. simpl. apply H1. auto. eauto. auto.
} Qed.


Lemma Qty_bid_FOA (M:list transaction) (A: list order)(b:order):
Qty_orders A >= Vol M -> Qty_bid (FOA_aux M A) (id b) = Qty_bid M (id b).
Proof. 
apply FOA_aux_elim. simpl. lia. simpl. intros.
destruct (idb t =? id b). 
cut (tquantity t = 0/\Qty_bid l (id b) <= Vol (l)). lia. split. lia. 
apply Q_vs_Qty_bid. cut (Qty_bid l (id b) <= Vol (l)). lia. 
apply Q_vs_Qty_bid.  simpl. intros.
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. destruct (idb m =? id b). rewrite H. auto. lia. lia.
    rewrite H.  auto. lia. lia.
  }
  { simpl. destruct (idb m =? id b). rewrite H0. auto. lia. lia. lia.
    rewrite H0.  auto. lia. lia. auto.
  }
}
{ simpl. destruct (idb m =? id b). rewrite H1. auto. lia. lia.
    rewrite H1.  auto. lia. lia.
} Qed.




Lemma FOA_head_full M A a a' :
NoDup (id a :: ids A) -> In a' A -> In (id a') (ids_ask_aux (FOA_aux M (a :: A))) -> 
Qty_ask (FOA_aux M (a :: A)) (id a) = oquantity a.
Proof. revert A a a'. induction M as [| m M]. intros A a a' nda H H1. 
rewrite FOA_aux_equation_1 in H1. simpl in H1. inversion H1. 
intros A a a' nda H H1.  rewrite FOA_aux_equation_3 in H1. rewrite FOA_aux_equation_3.
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. replace (id a =? id a) with true. simpl in H1. destruct H1.
    apply ids_intro in H. apply NoDup_cons_iff in nda. destruct nda. destruct H1. rewrite H0. auto. apply IHM in H0.
    simpl in H0. rewrite H0. lia. simpl. all:auto. 
  }
  { simpl. replace (id a =? id a) with true. cut(Qty_ask (FOA_aux M A) (id a) = 0).
    lia. apply Qty_ask_t_zero. intro Hin. apply Subset_asks_FOA in Hin. apply NoDup_cons_iff in nda.
    destruct nda. destruct H0. auto. auto.
  }
}
{ simpl. replace (id a =? id a) with true. rewrite Qty_ask_t_zero.
  intro Hin. apply Subset_asks_FOA in Hin. apply NoDup_cons_iff in nda.
    destruct nda. destruct H0. all:auto. 
}Qed. 

Lemma fair_asks_FOA M A :
NoDup (ids A) -> Sorted acompetitive A -> Sorted dec_price M ->
Is_fair_asks (FOA_aux M A) A.
Proof. 
unfold Is_fair_asks. apply FOA_aux_elim. 
firstorder. firstorder.
simpl. intros m M0 a A0 H H0 H1 nda. intros. 
assert(HbS: forall x, In x A0 -> (Nat.leb (oprice a) (oprice x))). apply Sorted_ointroA. auto.
assert(HmS: forall t, In t M0 -> (Nat.leb (tprice m) (tprice t))). apply Sorted_tintroD. auto.
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. 
{ destruct s eqn:f2.
  { specialize (H s). specialize (H l). destruct H4. destruct H5. destruct H6.
    destruct H4 as [H4 | H4];destruct H5 as [H5 | H5].
    { subst. destruct H6 as [H6a H6b]. apply acompetitive_contadiction in H6a. inversion H6a. all:auto. }
    { subst a0. simpl in H7. destruct H7 as [H7 | H7]. apply ids_intro in H5. 
      apply NoDup_cons_iff in nda. destruct nda. 
      destruct H4. rewrite H7. auto. simpl. replace (id a =? id a) with true.
      rewrite (FOA_head_full M0 A0 _ a'). all:auto. simpl. lia. }
    { subst a'. specialize (HbS a0).  apply Sorted_ointroA_tight with (x:=a0) in H2.
      apply acompetitive_contadiction in H2. inversion H2. apply H6. apply H6. auto. }
    { simpl in H7. destruct H7. apply ids_intro in H5. apply NoDup_cons_iff in nda. destruct nda. 
      destruct H8. rewrite H7. auto. simpl. destruct (id a =? id a0) eqn: Ha. apply ids_intro in H4. 
      apply NoDup_cons_iff in nda. destruct nda. destruct H8. move /eqP in Ha. rewrite Ha. auto.
      apply H with (a':=a'). auto. apply SortedreducedA with (a:=a). all:simpl;auto.
      apply Sorted_inv in H3. apply H3. }
  }
  { specialize (H0 s). simpl. destruct H4. destruct H5. destruct H6.
    destruct H4 as [H4 | H4];destruct H5 as [H5 | H5].
    { subst. destruct H6 as [H6a H6b]. apply acompetitive_contadiction in H6a. inversion H6a. all:auto. }
    { subst a0. simpl in H7. destruct H7 as [H7 | H7]. apply ids_intro in H5. 
      apply NoDup_cons_iff in nda. destruct nda. 
      destruct H4. rewrite H7. auto. simpl. replace (id a =? id a) with true. rewrite Qty_ask_FOA_zero.
      apply NoDup_cons_iff in nda. apply nda. lia. auto. }
    { subst a'. specialize (HbS a0).  apply Sorted_ointroA_tight with (x:=a0) in H2.
      apply acompetitive_contadiction in H2. inversion H2. apply H6. apply H6. auto. }
    { simpl in H7. destruct H7. apply ids_intro in H5. apply NoDup_cons_iff in nda. destruct nda. 
      destruct H8. rewrite H7. auto. simpl. destruct (id a =? id a0) eqn: Ha. apply ids_intro in H4. 
      apply NoDup_cons_iff in nda. destruct nda. destruct H8. move /eqP in Ha. rewrite Ha. auto.
      apply H0 with (a':=a'). all:auto. eauto. apply Sorted_inv in H2. apply H2.
      apply Sorted_inv in H3. apply H3. }
  }
 }
 { specialize (H1 l). simpl. destruct H4. destruct H5. destruct H6.
    destruct H4 as [H4 | H4];destruct H5 as [H5 | H5].
    { subst. destruct H6 as [H6a H6b]. apply acompetitive_contadiction in H6a. inversion H6a. all:auto. }
    { subst a0. simpl in H7. destruct H7 as [H7 | H7]. apply ids_intro in H5. 
      apply NoDup_cons_iff in nda. destruct nda. 
      destruct H4. rewrite H7. auto. simpl. replace (id a =? id a) with true. rewrite Qty_ask_FOA_zero.
      apply NoDup_cons_iff in nda. apply nda. lia. auto. }
    { subst a'. specialize (HbS a0).  apply Sorted_ointroA_tight with (x:=a0) in H2.
      apply acompetitive_contadiction in H2. inversion H2. apply H6. apply H6. auto. }
    { simpl in H7. destruct H7. apply ids_intro in H5. apply NoDup_cons_iff in nda. destruct nda. 
      destruct H8. rewrite H7. auto. simpl. destruct (id a =? id a0) eqn: Ha. apply ids_intro in H4. 
      apply NoDup_cons_iff in nda. destruct nda. destruct H8. move /eqP in Ha. rewrite Ha. auto.
      apply H1 with (a':=a'). all:auto. eauto. apply Sorted_inv in H2. apply H2.
      apply SortedreducedMD with (m:=m). simpl. all:auto. }
  }
 Qed.


Theorem strong_induction:
forall P : nat -> Prop,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n : nat, P n.
Proof. intros P H n; enough (H0: forall p, p <= n -> P p).
    - apply H0, le_n. 
    - induction n. 
      + intros. inversion H0. apply H. intros. inversion H2.
      + intros. apply H. intros. apply IHn.  inversion H0. 
        * rewrite H2 in H1. lia. 
        * specialize (PeanoNat.Nat.lt_le_trans k p n H1 H3). apply PeanoNat.Nat.lt_le_incl. Qed.


Definition Predicate_n_b n := forall M B A, (Vol(M) = n -> (NoDup (ids A) -> (forall t1, (In t1 M -> exists b, In b B/\idb t1 = id b/\(tprice t1 <= oprice b))) -> (forall t2, (In t2 (FOA_aux M A) -> exists b, In b B/\idb t2 = id b/\(tprice t2 <= oprice b))))). 

Lemma exist_b_FOA_aux_aux:
forall n:nat, (forall k, k < n -> Predicate_n_b k) -> Predicate_n_b n.
Proof. unfold Predicate_n_b. intro n. induction n. intros. assert(M = nil). 
{ induction M. auto. simpl in H0. destruct a. simpl in H0. assert(Htemp:= tquantity_cond). 
move /ltP in Htemp. lia. }
rewrite H4 in H3. rewrite FOA_aux_equation_1 in H3. simpl in H3. inversion H3. 
intros. destruct M as [| m M0]. rewrite FOA_aux_equation_1 in H3. inversion H3.
destruct A as [| a A0]. rewrite FOA_aux_equation_2 in H3. inversion H3.
rewrite FOA_aux_equation_3 in H3. 
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl in H3. destruct H3. assert(Hm:In m (m :: M0)). auto. apply H2 in Hm.
    subst t2. simpl. auto. simpl in H0. assert(Vol M0 < S n). destruct m. 
    assert(Htemp:= tquantity_cond). move /ltP in Htemp. simpl in H0. lia.
    specialize (H (Vol(M0))). apply H with (M:=M0)(B:=B)(A:=({|
             id := id a;
             otime := otime a;
             oquantity := oquantity a - tquantity m;
             oprice := oprice a;
             oquantity_cond := FOA_aux_obligations_obligation_1 m a l
           |} :: A0))(t2:=t2) in H4. auto. auto. simpl. eauto. intros. assert(In t1 (m :: M0)).
            simpl. auto. apply H2 in H6. auto. auto. 
   }
   { simpl in H3. destruct H3. assert(Hm:In m (m :: M0)). auto. apply H2 in Hm.
    subst t2. simpl. auto. simpl in H0. assert(Vol M0 < S n). destruct m. 
    assert(Htemp:= tquantity_cond). move /ltP in Htemp. simpl in H0. lia.
    specialize (H (Vol(M0))). apply H with (M:=M0)(B:=B)(A:=(A0))(t2:=t2) in H4. auto. auto. simpl. eauto. intros. assert(In t1 (m :: M0)).  simpl. auto. apply H2 in H6. auto. auto. 
   } }
{ simpl in H3. destruct H3. assert(Hm:In m (m :: M0)). auto. apply H2 in Hm.
    subst t2. simpl. auto. simpl in H0. assert(Vol (({|
             idb := idb m;
             ida := ida m;
             tprice := tprice m;
             tquantity := tquantity m - oquantity a;
             tquantity_cond := FOA_aux_obligations_obligation_4 m a l
           |} :: M0)) < S n). destruct a. 
    assert(Htemp:= oquantity_cond). move /ltP in Htemp. simpl. lia.
    specialize (H (Vol(({|
             idb := idb m;
             ida := ida m;
             tprice := tprice m;
             tquantity := tquantity m - oquantity a;
             tquantity_cond := FOA_aux_obligations_obligation_4 m a l
           |} :: M0)))). 
apply H with (M:=({|
             idb := idb m;
             ida := ida m;
             tprice := tprice m;
             tquantity := tquantity m - oquantity a;
             tquantity_cond := FOA_aux_obligations_obligation_4 m a l
           |} :: M0))(B:=B)(A:=(A0))(t2:=t2) in H4. auto. auto. eauto. intros. simpl in H5. destruct H5. 
assert(In m (m :: M0)). simpl. auto. apply H2 in H6. subst t1. simpl. auto.  auto. auto. 
   } Qed. 


Lemma exist_b_FOA_aux:
forall n, Predicate_n_b n. 
Proof. intros. induction n. unfold Predicate_n_b. intros. assert(M = nil). 
{ induction M. auto. simpl in H. destruct a. simpl in H. assert(Htemp:= tquantity_cond). 
move /ltP in Htemp. lia. }
rewrite H3 in H2. rewrite FOA_aux_equation_1 in H2. simpl in H2. inversion H2. 
apply strong_induction. intros. apply (exist_b_FOA_aux_aux). intros. 
apply H. auto. Qed. 


Lemma exist_b_FOA (B A: list order)(M: list transaction): 
NoDup (ids A) -> 
(forall t1, In t1 M -> exists b, In b B/\idb t1 = id b/\(tprice t1 <= oprice b)) -> 
(forall t2, In t2 (FOA_aux M A) -> exists b, In b B/\idb t2 = id b/\(tprice t2 <= oprice b)).
Proof. destruct (Vol(M)) eqn:HV. eapply exist_b_FOA_aux.  auto.
apply exist_b_FOA_aux with (n:= S n). auto.
Qed.


Definition supply_vol (p: nat)(A: list order): nat :=
  Qty_orders (filter (fun x:order => Nat.leb (oprice x) p) A).

Definition Supply_property M A := 
forall m, In m M -> supply_vol (tprice m) A >= Vol(filter (fun x:transaction => Nat.leb (tprice x) (tprice m)) M).

Lemma filter_nil A0 a m: 
(forall x : order, In x A0 -> oprice a <=? oprice x) -> ~ oprice a <= tprice m -> 
(filter (fun x : order => oprice x <=? tprice m) A0) = nil.
Proof. induction A0. intros. simpl. auto. intros. simpl. 
destruct (oprice a0 <=? tprice m) eqn:ha. assert(In a0 (a0 :: A0)). auto.
apply H in H1. move /leP in ha. move /leP in H1. lia. eapply IHA0. intros.
apply H. auto. auto. Qed.


Lemma M_supply_Matching M B A p:
Matching M B A -> Matching (filter (fun x : transaction => tprice x <=? p) M) 
B (filter (fun x : order => oprice x <=? p) A).
Proof. unfold Matching. unfold Tvalid. unfold valid. intros. destruct H.
destruct H0. split. 
intros. apply filter_In in H2.
destruct H2. apply H in H2. destruct H2 as [b H2]. destruct H2 as [a H2].
destruct H2. destruct H4. destruct H5. destruct H6. destruct H7.
destruct H8. destruct H9. destruct H10.
exists b. exists a. split. apply filter_In. split.
auto. apply /leP. move /leP in H3. lia. split;auto. split;auto. 
split;auto. split. { intros. 
apply H0 in H2. cut(Qty_bid (filter (fun x : transaction => tprice x <=? p) M) (id b) <=Qty_bid M (id b)).
lia. apply Qty_bid_filter. }
{ intros. apply filter_In in H2. destruct H2.
apply H1 in H2. cut (Qty_ask (filter (fun x : transaction => tprice x <=? p) M) (id a) <= Qty_ask M (id a)).
lia. apply Qty_ask_filter. }
 Qed.

Lemma NoDUp_ids_filter A f:
NoDup (ids A) -> NoDup (ids (filter f A)).
Proof.  intros. induction A. simpl. auto. simpl. destruct (f a) eqn:Hf.
simpl. constructor. intro. apply ids_elim in H0. destruct H0. destruct H0.
apply filter_In in H0. destruct H0. apply ids_intro in H0. rewrite H1 in H0.
simpl in H. apply NoDup_cons_iff in H. destruct H. destruct (H H0). apply IHA. eauto.
apply IHA. eauto. Qed.

Lemma Matching_imply_SP M B A:
NoDup (ids A) -> Matching M B A -> Supply_property M A.
Proof. intros. unfold Supply_property. unfold supply_vol. intros. 
apply Matching_Vol_A with (B:=B). apply NoDUp_ids_filter. auto. apply M_supply_Matching. auto. Qed. 



(*A is such that supply_A(tpr(m_i)) >= q(m_1) + q(m_2) +...+ q(m_i) for all i in [r]*)

Lemma FOA_matchable_FOA_aux M A :
NoDup (ids A) -> 
Sorted acompetitive A -> Sorted dec_price M -> 
Supply_property M A -> 
(forall m, In m (FOA_aux M A) -> 
exists a, In a A /\ ida m = id a /\ tprice m >= oprice a).
Proof. apply FOA_aux_elim. firstorder. firstorder. intros. 
assert(HbS: forall x, In x A0 -> (Nat.leb (oprice a) (oprice x))). apply Sorted_ointroA. auto.
assert(HmS: forall t, In t M0 -> (Nat.leb (tprice m) (tprice t))). apply Sorted_tintroD. auto.
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. 
{ destruct s eqn:f2.
  { specialize (H s). specialize (H l). simpl in H6. destruct H6. 
    { exists a. split. auto. subst m0. simpl. split. auto. unfold Supply_property in H5.
      assert(In m (m::M0)). auto. apply H5 in H6. simpl in H6. replace (tprice m <=? tprice m) with true in H6.
      simpl in H6. assert(supply_vol (tprice m) (a :: A0) >= tquantity m). lia. unfold supply_vol in H7. simpl in H7.
      destruct (oprice a <=? tprice m) eqn:Ham. move /leP in Ham. lia. move /leP in Ham. 
      assert((filter (fun x : order => oprice x <=? tprice m) A0) = nil). eapply filter_nil. exact HbS. auto.
      rewrite H8 in H7. simpl in H7. 
      destruct m. simpl in H7. assert(Htemp:= tquantity_cond). move /ltP in Htemp. lia. auto.
    }
    { apply H in H6. destruct H6. destruct H6. simpl in H6. destruct H6. exists a. split. auto. subst x. simpl in H7.
      auto. exists x. split. simpl. auto. auto. simpl. eauto. all:auto. 
      eapply SortedreducedA. simpl. auto. all:auto.
      apply Sorted_inv in H4. apply H4. 

      unfold Supply_property. intros. unfold supply_vol. unfold Supply_property in H5. 
      unfold supply_vol in H5. assert(Hm1:In m1 (m::M0)). auto. apply H5 in Hm1. 
      simpl. simpl in Hm1. destruct (oprice a <=? tprice m1) eqn:Ham1. 
      + simpl. replace (tprice m <=? tprice m1) with true in Hm1.  simpl in Hm1. lia. symmetry. apply HmS in H7. auto.
      + simpl. replace (tprice m <=? tprice m1) with true in Hm1.  simpl in Hm1. lia. symmetry. apply HmS in H7. auto.
    } }
    { specialize (H s). simpl in H6. destruct H6. 
    { exists a. split. auto. subst m0. simpl. split. auto. unfold Supply_property in H5.
      assert(In m (m::M0)). auto. apply H5 in H6. simpl in H6. replace (tprice m <=? tprice m) with true in H6.
      simpl in H6. assert(supply_vol (tprice m) (a :: A0) >= tquantity m). lia. unfold supply_vol in H7. simpl in H7.
      destruct (oprice a <=? tprice m) eqn:Ham. move /leP in Ham. lia. move /leP in Ham. 
      assert((filter (fun x : order => oprice x <=? tprice m) A0) = nil). eapply filter_nil. exact HbS. auto. 
      rewrite H8 in H7. simpl in H7. 
      destruct m. simpl in H7. assert(Htemp:= tquantity_cond). move /ltP in Htemp. lia. auto.
    }
    { apply H0 in H6. destruct H6. exists x. split. simpl. right. apply H6. apply H6. all:auto. eauto. 
      apply Sorted_inv in H3. apply H3. 
      apply Sorted_inv in H4. apply H4. 

      unfold Supply_property. intros. unfold supply_vol. unfold Supply_property in H5. 
      unfold supply_vol in H5. assert(Hm1:In m1 (m::M0)). auto. apply H5 in Hm1. 
      simpl. simpl in Hm1. destruct (oprice a <=? tprice m1) eqn:Ham1. 
      + simpl. replace (tprice m <=? tprice m1) with true in Hm1.  simpl in Hm1. lia. symmetry. apply HmS in H7. auto.
      + simpl. replace (tprice m <=? tprice m1) with true in Hm1.  simpl in Hm1. lia. symmetry. apply HmS in H7. auto.

    } } }
    { simpl in H6. destruct H6. 
    { exists a. split. auto. subst m0. simpl. split. auto. unfold Supply_property in H5.
      assert(In m (m::M0)). auto. apply H5 in H6. simpl in H6. replace (tprice m <=? tprice m) with true in H6.
      simpl in H6. assert(supply_vol (tprice m) (a :: A0) >= tquantity m). lia. unfold supply_vol in H7. simpl in H7.
      destruct (oprice a <=? tprice m) eqn:Ham. move /leP in Ham. lia. move /leP in Ham. 
      assert((filter (fun x : order => oprice x <=? tprice m) A0) = nil). eapply filter_nil. exact HbS. auto.
      rewrite H8 in H7. simpl in H7. 
      destruct m. simpl in H7. assert(Htemp:= tquantity_cond). move /ltP in Htemp. lia. auto.
    }
    { apply H1 in H6. destruct H6. exists x. split. simpl. right. apply H6. apply H6. eauto. all:auto. 
      apply Sorted_inv in H3. apply H3. 
      eapply SortedreducedMD. simpl. auto. all:auto.


      unfold Supply_property. intros. unfold supply_vol. unfold Supply_property in H5. 
      unfold supply_vol in H5. simpl in H7. destruct H7. {  subst m1. simpl. assert(Hm1:In m (m::M0)). auto. apply H5 in Hm1. 
      simpl. simpl in Hm1. destruct (oprice a <=? tprice m) eqn:Ham1. 
      + simpl. replace (tprice m <=? tprice m) with true in Hm1. replace (tprice m <=? tprice m) with true.
        simpl in Hm1. simpl. lia. auto.  auto. 
      + simpl. replace (tprice m <=? tprice m) with true in Hm1.  replace (tprice m <=? tprice m) with true.
        simpl in Hm1. simpl. lia. auto.  auto. } 

    { assert(Hm1:In m1 (m::M0)). auto. apply H5 in Hm1. 
      simpl. simpl in Hm1. destruct (oprice a <=? tprice m1) eqn:Ham1. 
      + simpl. replace (tprice m <=? tprice m1) with true in Hm1. replace (tprice m <=? tprice m1) with true. 
        simpl in Hm1. simpl. lia. symmetry. apply HmS in H7. auto. symmetry. apply HmS in H7. auto. 
      + simpl. replace (tprice m <=? tprice m1) with true in Hm1.  replace (tprice m <=? tprice m1) with true. 
        simpl in Hm1. simpl. lia. symmetry. apply HmS in H7. auto. symmetry. apply HmS in H7. auto. }
    } } Qed.


Lemma FOA_matchable_FOA M B A :
NoDup (ids A) -> 
Sorted acompetitive A -> Sorted dec_price M -> 
Matching M B A -> forall m, In m (FOA_aux M A) -> 
exists a, In a A /\ ida m = id a /\ tprice m >= oprice a.
Proof. intros. assert(Matching M B A -> Supply_property M A). apply Matching_imply_SP. auto. 
apply FOA_matchable_FOA_aux with (M:=M). all:auto. Qed. 

Lemma FOA_Matching M B A :
NoDup (ids A) -> NoDup (ids B) ->
Sorted acompetitive A -> Sorted dec_price M -> 
Matching M B A -> Matching (FOA_aux M A) B A.
Proof.  unfold Matching. unfold Tvalid. unfold valid. intros. 
assert(HQb:(forall b : order, In b B -> Qty_bid (FOA_aux M A) (id b) <= oquantity b)).
{ intros. assert(Qty_bid M (id b) <= oquantity b). apply H3. auto.
cut(Qty_bid (FOA_aux M A) (id b) = Qty_bid M (id b)). lia.
apply Qty_bid_FOA. cut(Vol M <= Qty_orders A). lia. apply Matching_Vol_A with (B:=B).
auto. auto. }
assert(HQa:(forall a : order, In a A -> Qty_ask (FOA_aux M A) (id a) <= oquantity a)).
{ intros. apply Qty_ask_FOA. auto. auto. }
split. intros. apply FOA_matchable_FOA with (m:=t) in H3 as Ha.
apply exist_b_FOA with (B:=B)(M:=M)(t2:=t) in H as Hb. destruct Ha as [a Ha].
destruct Hb as [b Hb]. exists b. exists a. 
destruct Ha as [Ha1 Ha]. destruct Ha as [Ha2 Ha3].
destruct Hb as [Hb1 Hb]. destruct Hb as [Hb2 Hb3].
split. auto. split. auto. split. auto. split. auto. split. unfold tradable. lia.
split. cut(Qty_bid (FOA_aux M A) (idb t) >= tquantity t). apply HQb in Hb1.
rewrite Hb2. lia. apply Qty_bid1. auto.
split. cut(Qty_ask (FOA_aux M A) (ida t) >= tquantity t). apply HQa in Ha1.
rewrite Ha2. lia. apply Qty_ask1. auto.
 split. auto. auto. intros. apply H3 in H5.
destruct H5 as [b H5]. destruct H5 as [a H5]. exists b. split. apply H5. split. apply H5.
cut(oprice b >= tprice t1). lia. apply H5.  all:auto. Qed. 

Lemma FOA_tprice_subset M A :
tprices (FOA_aux M A) [<=] tprices M.
Proof. apply FOA_aux_elim. firstorder. firstorder. simpl. intros.
destruct (lt_eq_lt_dec (tquantity m) (oquantity a)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. apply Subset_intro. auto. } { simpl. apply Subset_intro. auto. } } { simpl. unfold "[<=]". unfold "[<=]" in H1. simpl.  intros. simpl in H1. destruct H2.  auto. apply H1 in H2. auto. } Qed.

Lemma FOA_Uniform M A :
Uniform M -> Uniform (FOA_aux M A).
Proof. unfold Uniform. intros. apply uniform_subset with (l2:=(tprices M)). apply FOA_tprice_subset. auto. Qed.

Lemma FOA_Is_uniform M B A :
NoDup (ids A) -> NoDup (ids B) ->
Sorted acompetitive A -> Sorted dec_price M -> 
Is_uniform M B A -> Is_uniform (FOA_aux M A) B A.
Proof. unfold Is_uniform. intros. split. apply FOA_Uniform. apply H3. apply FOA_Matching. all:auto. apply H3. Qed.


Lemma fair_bids_FOA M B A:
NoDup (ids A) -> NoDup (ids B) -> Is_fair_bids M B -> Matching M B A ->
Is_fair_bids (FOA_aux M A) B.
Proof. 
unfold Is_fair_bids. simpl. intros. destruct H3. destruct H4. 
rewrite Qty_bid_FOA. 
cut(Vol M <= Qty_orders A). lia.
eapply Matching_Vol_A. auto. exact H2. 
specialize (H1 b). specialize (H1 b').
destruct H5. 
rewrite H1. split. auto. split. auto. split. auto. 
assert(ids_bid_aux (FOA_aux M A) [<=] ids_bid_aux M).
apply Subset_bids_FOA. eauto. auto. Qed.


(* The fair on ask correctness lemma. *)
Lemma FOA_aux_correct M B A:
admissible B A /\ Matching M B A ->
Sorted acompetitive A -> Sorted dec_price M -> 
Matching (FOA_aux M A) B A /\                                                       (* (a) *)
Vol(M) = Vol(FOA_aux M A) /\                                                        (* (b) *)
Is_fair_asks (FOA_aux M A) A /\                                                     (* (c) *)
(forall b, In b B -> Qty_bid M (id(b)) = Qty_bid (FOA_aux M A) (id(b)))/\           (* (d) *)
(Is_fair_bids M B -> Is_fair_bids (FOA_aux M A) B).
Proof. intros. split. apply FOA_Matching. all:auto. apply H. apply H. apply H. 
split. rewrite (Vol_FOA M A). cut(Vol M <= Qty_orders A). lia.
eapply Matching_Vol_A. apply H. apply H. auto.
split. apply fair_asks_FOA. apply H. all:auto. 
split. intros. symmetry. apply Qty_bid_FOA. 
cut(Vol M <= Qty_orders A). lia.
eapply Matching_Vol_A. apply H. apply H. intros. apply fair_bids_FOA.
apply H. apply H. auto. apply H. Qed. 

End Fair_Ask.




(*Commnet Here*)


Require Import Wellfounded.
Require Import List Setoid Permutation  Orders.
Require Import Coq.Logic.Eqdep_dec Coq.Arith.Compare_dec Coq.Arith.PeanoNat.
From Equations Require Export Equations.
Require Export Fair_Ask.
Require Export Demand_suppy_Inequality.
Require Export Coq.Sorting.Mergesort Sorted SortLists.


Section Fair_Bid.

Lemma liaforrun (b a : order): 
oquantity b < oquantity a -> 
~ (oquantity a - oquantity b < 1). lia. Qed.

Lemma liaforrun2 (a : order)(m: transaction): 
tquantity m < oquantity a ->
~ oquantity a - tquantity m < 1. lia. Qed.

Lemma liaforrun3 (a : order)(m: transaction): 
 oquantity a < tquantity m ->
~ tquantity m - oquantity a < 1. lia. Qed.


Equations FOB_aux (M:list transaction) (B: list order): 
(list transaction) by wf ((length M) + (length B)) :=  
FOB_aux nil _ := nil;
FOB_aux _ nil := nil;
FOB_aux (m::M) (b::B) := match (Compare_dec.lt_eq_lt_dec (tquantity m) (oquantity b)) with
    |inleft (right _) =>  (Mk_transaction (id b) (ida m) (tprice m) (oquantity b) (oquantity_cond b))::
                                                                                                  (FOB_aux M B) 
    |inleft (left _) =>  ((Mk_transaction (id b) (ida m)  (tprice m) (tquantity m) (tquantity_cond m)):: (FOB_aux M ((Mk_order (id b) (otime b) (oquantity b - tquantity m) (oprice b) _ ) :: B)))
    |inright _ =>  (Mk_transaction (id b) (ida m) (tprice m) (oquantity b) (oquantity_cond b))::
                        (FOB_aux ((Mk_transaction (idb m) (ida m) (tprice m) (tquantity m - oquantity b) _ )::M) B)
    end.

Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. apply liaforrun2;auto. Defined.  
Next Obligation. lia. Defined.
Next Obligation. apply PeanoNat.Nat.ltb_nlt. apply liaforrun3;auto. Defined.
Next Obligation. lia. Defined.

 Lemma test_FOB (M:list transaction) (B: list order):
length M + length B >= length (FOB_aux M B).
Proof. 
apply FOB_aux_elim. simpl. lia. simpl. lia. simpl. intros.
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. destruct s eqn:f2.
specialize (H s). specialize (H l). simpl. simpl in H. lia.
specialize (H0 s). simpl. lia.
specialize (H1 l). simpl. lia.
Qed.


Lemma Vol_FOB (M:list transaction) (B: list order):
Qty_orders B >= Vol (M) -> Vol (M) = Vol (FOB_aux M B).
Proof. 
apply FOB_aux_elim. simpl. lia. simpl. lia. simpl. intros.
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. destruct s eqn:f2.
specialize (H s). specialize (H l). simpl. simpl in H. lia.
specialize (H0 s). simpl. lia.
specialize (H1 l). simpl. lia.
Qed.

Lemma Qty_bid_FOB_zero (M:list transaction) (B: list order) (b1:order):
~ In (id b1) (ids B) -> Qty_bid (FOB_aux M B) (id b1) = 0.
Proof.
apply FOB_aux_elim. 
{ simpl. auto. }
{ simpl. auto. }
{ simpl. intros. 
  destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1.   
  { destruct s eqn:f2.
    { simpl. assert (Hb1:~ (id b = id b1)). apply Decidable.not_or in H2. apply H2. assert(Ha2: ~In (id b1) (ids B0)).
      apply Decidable.not_or in H2. apply H2. destruct (id b =? id b1) eqn:Ha. move /eqP in Ha. lia. 
      apply H. all:auto.
  }
  { simpl. simpl. assert (Hb1:~ (id b = id b1)). apply Decidable.not_or in H2. apply H2. 
    assert(Hb2: ~In (id b1) (ids B0)). apply Decidable.not_or in H2. apply H2.
    destruct (id b =? id b1) eqn:Ha. move /eqP in Ha. lia.  apply H0. all:auto.
  }
}
{ simpl. assert (Hb1:~ (id b = id b1)). apply Decidable.not_or in H2. apply H2. assert(Hb2: ~In (id b1) (ids B0)). 
  apply Decidable.not_or in H2. apply H2. destruct (id b =? id b1) eqn:Ha. move /eqP in Ha. lia. apply H1. all:auto.
}} Qed. 

Lemma Subset_bids_FOB (M:list transaction) (B: list order):
Subset (ids_bid_aux (FOB_aux M B)) (ids B).
Proof. 
apply FOB_aux_elim. 
{ simpl. auto. }
{ simpl. auto. }
{ simpl. intros. 
  destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1.   
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


Lemma Subset_asks_FOB (M:list transaction) (B: list order):
Subset (ids_ask_aux (FOB_aux M B)) (ids_ask_aux M).
Proof. 
apply FOB_aux_elim. 
{ simpl. auto. }
{ simpl. auto. }
{ simpl. intros. 
  destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1.   
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. unfold "[<=]". intros. unfold "[<=]" in H.
      simpl in H2. destruct H2. simpl. auto. simpl. right. apply H. auto. } 
    { specialize (H0 s). simpl. apply Subset_intro. apply H0. auto. }
  }
  { specialize (H1 l). unfold "[<=]". intros. unfold "[<=]" in H1.
    simpl in H2. destruct H2. simpl. auto. apply H1 in H2. auto. 
  }
} Qed.

Lemma Qty_bid_FOB_b (M:list transaction) (B: list order) (b: order):
NoDup (ids (b::B)) -> Qty_bid (FOB_aux M (b::B)) (id b) <= oquantity b.
Proof. revert B b. induction M as [| m M]. intros B b H. rewrite FOB_aux_equation_1. simpl. lia. 
intros B b H. rewrite FOB_aux_equation_3. simpl.
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. replace (id b =? id b) with true. 
    set (b0:= {|id := id b;otime := otime b;oquantity := oquantity b - tquantity m;oprice := oprice b; oquantity_cond := FOB_aux_obligations_obligation_1 m b l|}). 
    replace (id b) with (id b0). cut (Qty_bid (FOB_aux M (b0 :: B)) (id b0) <= oquantity b0).
    simpl. lia. simpl. subst b0. simpl. apply IHM in H as HM. set (b0:= {|id := id b;otime := otime b;oquantity := oquantity b - tquantity m;oprice := oprice b; oquantity_cond := FOB_aux_obligations_obligation_1 m b l|}). replace (id b) with (id b0). apply (IHM B b0). all:auto.
  }
  { simpl. replace (id b =? id b) with true. rewrite Qty_bid_FOB_zero. intro.
    simpl in H. apply NoDup_cons_iff in H.
    destruct H. destruct H. auto. lia. auto.
  }
}
{ simpl. replace (id b =? id b) with true. rewrite Qty_bid_FOB_zero.
 intro.
    simpl in H. apply NoDup_cons_iff in H.
    destruct H. destruct H. auto. lia. auto. }Qed. 

Lemma Qty_bid_FOB_b_rev (M:list transaction) (B: list order) (b: order):
Vol M >= oquantity b -> NoDup (ids (b::B)) -> Qty_bid (FOB_aux M (b::B)) (id b) = oquantity b.
Proof. revert B b. induction M as [| m M]. intros B b Volume0 H. rewrite FOB_aux_equation_1. simpl. 
simpl in Volume0. lia. 
intros B b Volume0 H. rewrite FOB_aux_equation_3. simpl.
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. replace (id b =? id b) with true. 
    set (b0:= {|id := id b;otime := otime b;oquantity := oquantity b - tquantity m;oprice := oprice b; oquantity_cond := FOB_aux_obligations_obligation_1 m b l|}). 
    simpl. replace (id b) with (id b0). rewrite IHM. simpl in Volume0. subst b0. simpl. 
    lia. all:simpl;auto. lia.
  }
  { simpl. replace (id b =? id b) with true. cut(Qty_bid (FOB_aux M B) (id b) = 0).
    lia. apply Qty_bid_t_zero. intro Hin. apply Subset_bids_FOB in Hin. simpl in H. apply NoDup_cons_iff in H.
    destruct H. destruct H. auto. auto.
  }
}
{ simpl. replace (id b =? id b) with true. rewrite Qty_bid_t_zero.
  intro Hin. apply Subset_bids_FOB in Hin. simpl in H. apply NoDup_cons_iff in H.
  destruct H. destruct H. auto. simpl in Volume0. lia. auto.
}Qed.

Lemma Qty_bid_FOB_b_rev_less (M:list transaction) (B: list order) (b: order):
Vol M < oquantity b -> NoDup (ids (b::B)) -> Qty_bid (FOB_aux M (b::B)) (id b) = Vol M.
Proof. revert B b. induction M as [| m M]. intros B b Volume0 H. rewrite FOB_aux_equation_1. simpl. 
simpl in Volume0. lia. 
intros B b Volume0 H. rewrite FOB_aux_equation_3. simpl.
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. replace (id b =? id b) with true. 
    set (b0:= {|id := id b;otime := otime b;oquantity := oquantity b - tquantity m;oprice := oprice b; oquantity_cond := FOB_aux_obligations_obligation_1 m b l|}). 
    simpl. replace (id b) with (id b0). rewrite IHM. simpl in Volume0. subst b0. simpl. 
    lia. all:simpl;auto.
  }
  { simpl. replace (id b =? id b) with true. simpl in Volume0. lia. auto. }  
}
{ simpl. replace (id b =? id b) with true. rewrite Qty_bid_t_zero.
  intro Hin. apply Subset_bids_FOB in Hin. simpl in H. apply NoDup_cons_iff in H.
  destruct H. destruct H. auto. simpl in Volume0. lia. auto.
}Qed.


Lemma Qty_bid_FOB (M:list transaction) (B: list order):
NoDup (ids B) -> (forall b : order, In b B -> Qty_bid (FOB_aux M B) (id b) <= oquantity b).
Proof. 
apply FOB_aux_elim. simpl. lia. simpl. lia. simpl. intros.
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. 
{ destruct s eqn:f2.
  { destruct H3. subst b0. simpl.  replace (id b =? id b) with true.
    simpl. set (b1:= {|id := id b;otime := otime b;oquantity := oquantity b - tquantity m;oprice := oprice b; oquantity_cond := FOB_aux_obligations_obligation_1 m b l|}).
     cut (Qty_bid (FOB_aux M0 (b1 :: B0)) (id b) <= oquantity b - tquantity m).
     simpl. lia. replace (id b) with (id b1). apply Qty_bid_FOB_b. auto. subst b1. all:simpl;auto.
     destruct (id b =? id b0) eqn:Hb. move /eqP in Hb. apply ids_intro in H3.
     rewrite <- Hb in H3. apply NoDup_cons_iff in H3. inversion H3. all:auto.
  }
  { destruct H3. subst b0. simpl.  replace (id b =? id b) with true. 
    rewrite Qty_bid_FOB_zero. intro. simpl in H. apply NoDup_cons_iff in H3. inversion H3.
    auto. lia. auto. simpl. destruct (id b =? id b0) eqn:Hbb. 
    move /eqP in Hbb. apply ids_intro in H3.
    rewrite <- Hbb in H3. apply NoDup_cons_iff in H3. inversion H3.
     auto. apply H0.  auto. auto. eauto. auto.
  }
}
{ destruct H3. subst b0. simpl.  replace (id b =? id b) with true.
    simpl. rewrite Qty_bid_t_zero. intro Hin. apply Subset_bids_FOB in Hin. simpl in H2. apply NoDup_cons_iff in H2.
    destruct H2. destruct H2. auto. lia. auto. simpl. 
    destruct (id b =? id b0) eqn:Hb. move /eqP in Hb. apply ids_intro in H3.
    rewrite <- Hb in H3. apply NoDup_cons_iff in H3. inversion H3. 
     auto. simpl. apply H1. auto. eauto. auto.
} Qed.


Lemma Qty_ask_FOB (M:list transaction) (B: list order)(a:order):
Qty_orders B >= Vol M -> Qty_ask (FOB_aux M B) (id a) = Qty_ask M (id a).
Proof. 
apply FOB_aux_elim. simpl. lia. simpl. intros.
destruct (ida t =? id a). 
cut (tquantity t = 0/\Qty_ask l (id a) <= Vol (l)). lia. split. lia. 
apply Q_vs_Qty_ask. cut (Qty_ask l (id a) <= Vol (l)). lia. 
apply Q_vs_Qty_ask.  simpl. intros.
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. destruct (ida m =? id a). rewrite H. auto. lia. lia.
    rewrite H.  auto. lia. lia.
  }
  { simpl. destruct (ida m =? id a). rewrite H0. auto. lia. lia. lia.
    rewrite H0.  auto. lia. lia. auto.
  }
}
{ simpl. destruct (ida m =? id a). rewrite H1. auto. lia. lia.
    rewrite H1.  auto. lia. lia.
} Qed.




Lemma FOB_head_full M B b b' :
NoDup (id b :: ids B) -> In b' B -> In (id b') (ids_bid_aux (FOB_aux M (b :: B))) -> 
Qty_bid (FOB_aux M (b :: B)) (id b) = oquantity b.
Proof. revert B b b'. induction M as [| m M]. intros B b b' ndb H H1. 
rewrite FOB_aux_equation_1 in H1. simpl in H1. inversion H1. 
intros B b b' ndb H H1.  rewrite FOB_aux_equation_3 in H1. rewrite FOB_aux_equation_3.
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. replace (id b =? id b) with true. simpl in H1. destruct H1.
    apply ids_intro in H. apply NoDup_cons_iff in ndb. destruct ndb. destruct H1. rewrite H0. auto. apply IHM in H0.
    simpl in H0. rewrite H0. lia. simpl. all:auto. 
  }
  { simpl. replace (id b =? id b) with true. cut(Qty_bid (FOB_aux M B) (id b) = 0).
    lia. apply Qty_bid_t_zero. intro Hin. apply Subset_bids_FOB in Hin. apply NoDup_cons_iff in ndb.
    destruct ndb. destruct H0. auto. auto.
  }
}
{ simpl. replace (id b =? id b) with true. rewrite Qty_bid_t_zero.
  intro Hin. apply Subset_bids_FOB in Hin. apply NoDup_cons_iff in ndb.
    destruct ndb. destruct H0. all:auto. 
}Qed. 

Lemma fair_bids_FOB M B :
NoDup (ids B) -> Sorted bcompetitive B -> Sorted incr_price M ->
Is_fair_bids (FOB_aux M B) B.
Proof. 
unfold Is_fair_bids. apply FOB_aux_elim. 
firstorder. firstorder.
simpl. intros m M0 b B0 H H0 H1 ndb. intros. 
assert(HbS: forall x, In x B0 -> (Nat.leb (oprice x) (oprice b))). apply Sorted_ointroB. auto.
assert(HmS: forall t, In t M0 -> (Nat.leb (tprice t) (tprice m))). apply Sorted_tintroI. auto.
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. 
{ destruct s eqn:f2.
  { specialize (H s). specialize (H l). destruct H4. destruct H5. destruct H6.
    destruct H4 as [H4 | H4];destruct H5 as [H5 | H5].
    { subst. destruct H6 as [H6a H6b]. apply bcompetitive_contadiction in H6a. inversion H6a. all:auto. }
    { subst b0. simpl in H7. destruct H7 as [H7 | H7]. apply ids_intro in H5. 
      apply NoDup_cons_iff in ndb. destruct ndb. 
      destruct H4. rewrite H7. auto. simpl. replace (id b =? id b) with true.
      rewrite (FOB_head_full M0 B0 _ b'). all:auto. simpl. lia. }
    { subst b'. specialize (HbS b0).  apply Sorted_ointroB_tight with (x:=b0) in H2.
      apply bcompetitive_contadiction in H2. inversion H2. apply H6. apply H6. auto. }
    { simpl in H7. destruct H7. apply ids_intro in H5. apply NoDup_cons_iff in ndb. destruct ndb. 
      destruct H8. rewrite H7. auto. simpl. destruct (id b =? id b0) eqn: Hb. apply ids_intro in H4. 
      apply NoDup_cons_iff in ndb. destruct ndb. destruct H8. move /eqP in Hb. rewrite Hb. auto.
      apply H with (b':=b'). auto. apply SortedreducedB with (b:=b). all:simpl;auto.
      apply Sorted_inv in H3. apply H3. }
  }
  { specialize (H0 s). simpl. destruct H4. destruct H5. destruct H6.
    destruct H4 as [H4 | H4];destruct H5 as [H5 | H5].
    { subst. destruct H6 as [H6a H6b]. apply bcompetitive_contadiction in H6b. inversion H6b. all:auto. }
    { subst b0. simpl in H7. destruct H7 as [H7 | H7]. apply ids_intro in H5. 
      apply NoDup_cons_iff in ndb. destruct ndb. 
      destruct H4. rewrite H7. auto. simpl. replace (id b =? id b) with true. rewrite Qty_bid_FOB_zero.
      apply NoDup_cons_iff in ndb. apply ndb. lia. auto. }
    { subst b'. specialize (HbS b0).  apply Sorted_ointroB_tight with (x:=b0) in H2.
      apply bcompetitive_contadiction in H2. inversion H2. apply H6. apply H6. auto. }
    { simpl in H7. destruct H7. apply ids_intro in H5. apply NoDup_cons_iff in ndb. destruct ndb. 
      destruct H8. rewrite H7. auto. simpl. destruct (id b =? id b0) eqn: Hb. apply ids_intro in H4. 
      apply NoDup_cons_iff in ndb. destruct ndb. destruct H8. move /eqP in Hb. rewrite Hb. auto.
      apply H0 with (b':=b'). all:auto. eauto. apply Sorted_inv in H2. apply H2.
      apply Sorted_inv in H3. apply H3. }
  }
 }
 { specialize (H1 l). simpl. destruct H4. destruct H5. destruct H6.
    destruct H4 as [H4 | H4];destruct H5 as [H5 | H5].
    { subst. destruct H6 as [H6a H6b]. apply bcompetitive_contadiction in H6b. inversion H6b. all:auto. }
    { subst b0. simpl in H7. destruct H7 as [H7 | H7]. apply ids_intro in H5. 
      apply NoDup_cons_iff in ndb. destruct ndb. 
      destruct H4. rewrite H7. auto. simpl. replace (id b =? id b) with true. rewrite Qty_bid_FOB_zero.
      apply NoDup_cons_iff in ndb. apply ndb. lia. auto. }
    { subst b'. specialize (HbS b0).  apply Sorted_ointroB_tight with (x:=b0) in H2.
      apply bcompetitive_contadiction in H2. inversion H2. apply H6. apply H6. auto. }
    { simpl in H7. destruct H7. apply ids_intro in H5. apply NoDup_cons_iff in ndb. destruct ndb. 
      destruct H8. rewrite H7. auto. simpl. destruct (id b =? id b0) eqn: Hb. apply ids_intro in H4. 
      apply NoDup_cons_iff in ndb. destruct ndb. destruct H8. move /eqP in Hb. rewrite Hb. auto.
      apply H1 with (b':=b'). all:auto. eauto. apply Sorted_inv in H2. apply H2.
      apply SortedreducedMI with (m:=m). simpl. all:auto. }
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


Definition Predicate_n_a n := forall M B A, (Vol(M) = n -> (NoDup (ids B) -> (forall t1, (In t1 M -> exists a, In a A/\ida t1 = id a/\(oprice a <= tprice t1))) -> (forall t2, (In t2 (FOB_aux M B) -> exists a, In a A/\ida t2 = id a/\(oprice a <= tprice t2))))). 

Lemma exist_a_FOB_aux_aux:
forall n:nat, (forall k, k < n -> Predicate_n_a k) -> Predicate_n_a n.
Proof. unfold Predicate_n_a. intro n. induction n. intros. assert(M = nil). 
{ induction M. auto. simpl in H0. destruct a. simpl in H0. assert(Htemp:= tquantity_cond). 
move /ltP in Htemp. lia. }
rewrite H4 in H3. rewrite FOB_aux_equation_1 in H3. simpl in H3. inversion H3. 
intros. destruct M as [| m M0]. rewrite FOB_aux_equation_1 in H3. inversion H3.
destruct B as [| b B0]. rewrite FOB_aux_equation_2 in H3. inversion H3.
rewrite FOB_aux_equation_3 in H3. 
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl in H3. destruct H3. assert(Hm:In m (m :: M0)). auto. apply H2 in Hm.
    subst t2. simpl. auto. simpl in H0. assert(Vol M0 < S n). destruct m. 
    assert(Htemp:= tquantity_cond). move /ltP in Htemp. simpl in H0. lia.
    specialize (H (Vol(M0))). apply H with (M:=M0)(A:=A)(B:=({|
             id := id b;
             otime := otime b;
             oquantity := oquantity b - tquantity m;
             oprice := oprice b;
             oquantity_cond := FOB_aux_obligations_obligation_1 m b l
           |} :: B0))(t2:=t2) in H4. auto. auto. simpl. eauto. intros. assert(In t1 (m :: M0)).
            simpl. auto. apply H2 in H6. auto. auto. 
   }
   { simpl in H3. destruct H3. assert(Hm:In m (m :: M0)). auto. apply H2 in Hm.
    subst t2. simpl. auto. simpl in H0. assert(Vol M0 < S n). destruct m. 
    assert(Htemp:= tquantity_cond). move /ltP in Htemp. simpl in H0. lia.
    specialize (H (Vol(M0))). apply H with (M:=M0)(A:=A)(B:=(B0))(t2:=t2) in H4. auto. auto. simpl. eauto. intros. assert(In t1 (m :: M0)).  simpl. auto. apply H2 in H6. auto. auto. 
   } }
{ simpl in H3. destruct H3. assert(Hm:In m (m :: M0)). auto. apply H2 in Hm.
    subst t2. simpl. auto. simpl in H0. assert(Vol (({|
             idb := idb m;
             ida := ida m;
             tprice := tprice m;
             tquantity := tquantity m - oquantity b;
             tquantity_cond := FOB_aux_obligations_obligation_4 m b l
           |} :: M0)) < S n). destruct b. 
    assert(Htemp:= oquantity_cond). move /ltP in Htemp. simpl. lia.
    specialize (H (Vol(({|
             idb := idb m;
             ida := ida m;
             tprice := tprice m;
             tquantity := tquantity m - oquantity b;
             tquantity_cond := FOB_aux_obligations_obligation_4 m b l
           |} :: M0)))). 
apply H with (M:=({|
             idb := idb m;
             ida := ida m;
             tprice := tprice m;
             tquantity := tquantity m - oquantity b;
             tquantity_cond := FOB_aux_obligations_obligation_4 m b l
           |} :: M0))(A:=A)(B:=(B0))(t2:=t2) in H4. auto. auto. eauto. intros. simpl in H5. destruct H5. 
assert(In m (m :: M0)). simpl. auto. apply H2 in H6. subst t1. simpl. auto.  auto. auto. 
   } Qed. 


Lemma exist_a_FOB_aux:
forall n, Predicate_n_a n. 
Proof. intros. induction n. unfold Predicate_n_a. intros. assert(M = nil). 
{ induction M. auto. simpl in H. destruct a. simpl in H. assert(Htemp:= tquantity_cond). 
move /ltP in Htemp. lia. }
rewrite H3 in H2. rewrite FOB_aux_equation_1 in H2. simpl in H2. inversion H2. 
apply strong_induction. intros. apply (exist_a_FOB_aux_aux). intros. 
apply H. auto. Qed. 


Lemma exist_a_FOB (B A: list order)(M: list transaction): 
NoDup (ids B) -> 
(forall t1, In t1 M -> exists a, In a A/\ida t1 = id a/\(oprice a <= tprice t1)) -> 
(forall t2, In t2 (FOB_aux M B) -> exists a, In a A/\ida t2 = id a/\(oprice a <= tprice t2)).
Proof. destruct (Vol(M)) eqn:HV. eapply exist_a_FOB_aux.  auto.
apply exist_a_FOB_aux with (n:= S n). auto.
Qed.


Definition demand_vol (p: nat)(B: list order): nat :=
  Qty_orders (filter (fun x:order => Nat.leb p (oprice x)) B).

Definition Demand_property M B := 
forall m, In m M -> demand_vol (tprice m) B >= Vol(filter (fun x:transaction => Nat.leb (tprice m) (tprice x)) M).

Lemma filter_nilB B0 b m: 
(forall x : order, In x B0 -> oprice x <=? oprice b) -> ~tprice m <= oprice b -> 
(filter (fun x : order => tprice m <=? oprice x) B0) = nil.
Proof. induction B0. intros. simpl. auto. intros. simpl. 
destruct (tprice m <=? oprice a) eqn:ha. assert(In a (a :: B0)). auto.
apply H in H1. move /leP in ha. move /leP in H1. lia. eapply IHB0. intros.
apply H. auto. auto. Qed.


Lemma M_demand_Matching M B A p:
Matching M B A -> Matching (filter (fun x : transaction => p <=? tprice x) M) 
(filter (fun x : order => p <=? oprice x) B) A.
Proof. unfold Matching. unfold Tvalid. unfold valid. intros. destruct H.
destruct H0. split. 
intros. apply filter_In in H2.
destruct H2. apply H in H2. destruct H2 as [b H2]. destruct H2 as [a H2].
destruct H2. destruct H4. destruct H5. destruct H6. destruct H7.
destruct H8. destruct H9. destruct H10.
exists b. exists a. split. auto. split.
apply filter_In. split. auto. apply /leP. move /leP in H3. lia. split;auto. split;auto. 
split;auto. 
{ intros. apply filter_In in H2. destruct H2.
apply H0 in H2. cut (Qty_bid (filter (fun x : transaction => p <=? tprice x) M) (id b) <= Qty_bid M (id b)).
lia. apply Qty_bid_filter. }
{ intros.
apply H1 in H2. cut(Qty_ask (filter (fun x : transaction => p <=? tprice x ) M) (id a) <=Qty_ask M (id a)).
lia. apply Qty_ask_filter. }
 Qed.

(*Lemma NoDUp_ids_filter A f:
NoDup (ids A) -> NoDup (ids (filter f A)).
Proof.  intros. induction A. simpl. auto. simpl. destruct (f a) eqn:Hf.
simpl. constructor. intro. apply ids_elim in H0. destruct H0. destruct H0.
apply filter_In in H0. destruct H0. apply ids_intro in H0. rewrite H1 in H0.
simpl in H. apply NoDup_cons_iff in H. destruct H. destruct (H H0). apply IHA. eauto.
apply IHA. eauto. Qed.
*)
Lemma Matching_imply_DP M B A:
NoDup (ids B) -> Matching M B A -> Demand_property M B.
Proof. intros. unfold Demand_property. unfold demand_vol. intros. 
apply Matching_Vol_B with (A:=A). apply NoDUp_ids_filter. auto. apply M_demand_Matching. auto. Qed. 



(*A is such that supply_A(tpr(m_i)) >= q(m_1) + q(m_2) +...+ q(m_i) for all i in [r]*)

Lemma FOB_matchable_FOB_aux M B :
NoDup (ids B) -> 
Sorted bcompetitive B -> Sorted incr_price M -> 
Demand_property M B -> 
(forall m, In m (FOB_aux M B) -> 
exists b, In b B /\ idb m = id b /\ oprice b >= tprice m).
Proof. apply FOB_aux_elim. firstorder. firstorder. intros. 
assert(HbS: forall x, In x B0 -> (Nat.leb (oprice x) (oprice b))). apply Sorted_ointroB. auto.
assert(HmS: forall t, In t M0 -> (Nat.leb (tprice t) (tprice m))). apply Sorted_tintroI. auto.
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. 
{ destruct s eqn:f2.
  { specialize (H s). specialize (H l). simpl in H6. destruct H6. 
    { exists b. split. auto. subst m0. simpl. split. auto. unfold Demand_property in H5.
      assert(In m (m::M0)). auto. apply H5 in H6. simpl in H6. 
      replace (tprice m <=? tprice m) with true in H6.
      simpl in H6. assert(demand_vol (tprice m) (b :: B0) >= tquantity m). lia. unfold demand_vol in H7. simpl in H7.
      destruct (tprice m <=? oprice b) eqn:Ham. move /leP in Ham. lia. move /leP in Ham. 
      assert((filter (fun x : order => tprice m <=? oprice x) B0) = nil). eapply filter_nilB. exact HbS. auto.
      rewrite H8 in H7. simpl in H7. 
      destruct m. simpl in H7. assert(Htemp:= tquantity_cond). move /ltP in Htemp. lia. auto.
    }
    { apply H in H6. destruct H6. destruct H6. simpl in H6. destruct H6. exists b. split. auto. subst x. simpl in H7.
      auto. exists x. split. simpl. auto. auto. simpl. eauto. all:auto. 
      eapply SortedreducedB. simpl. auto. all:auto.
      apply Sorted_inv in H4. apply H4. 

      unfold Demand_property. intros. unfold demand_vol. unfold Demand_property in H5. 
      unfold demand_vol in H5. assert(Hm1:In m1 (m::M0)). auto. apply H5 in Hm1. 
      simpl. simpl in Hm1. destruct (tprice m1 <=? oprice b) eqn:Ham1. 
      + simpl. replace (tprice m1 <=? tprice m) with true in Hm1. simpl in Hm1. 
        lia. symmetry. apply HmS in H7. auto.
      + simpl. replace (tprice m1 <=? tprice m) with true in Hm1.  simpl in Hm1. lia. symmetry.
        apply HmS in H7. auto.
    } }
    { specialize (H s). simpl in H6. destruct H6. 
    { exists b. split. auto. subst m0. simpl. split. auto. unfold Demand_property in H5.
      assert(In m (m::M0)). auto. apply H5 in H6. simpl in H6. 
      replace (tprice m <=? tprice m) with true in H6.
      simpl in H6. assert(demand_vol (tprice m) (b :: B0) >= tquantity m). lia. 
      unfold demand_vol in H7. simpl in H7.
      destruct (tprice m <=? oprice b) eqn:Ham. move /leP in Ham. lia. move /leP in Ham. 
      assert((filter (fun x : order => tprice m <=? oprice x) B0) = nil). 
      eapply filter_nilB. exact HbS. auto. 
      rewrite H8 in H7. simpl in H7. 
      destruct m. simpl in H7. assert(Htemp:= tquantity_cond). move /ltP in Htemp. lia. auto.
    }
    { apply H0 in H6. destruct H6. exists x. split. simpl. right. apply H6. apply H6. all:auto.
      eauto. 
      apply Sorted_inv in H3. apply H3. 
      apply Sorted_inv in H4. apply H4. 

      unfold Demand_property. intros. unfold demand_vol. unfold Demand_property in H5. 
      unfold demand_vol in H5. assert(Hm1:In m1 (m::M0)). auto. apply H5 in Hm1. 
      simpl. simpl in Hm1. destruct (tprice m1 <=? oprice b) eqn:Ham1. 
      + simpl. replace (tprice m1 <=? tprice m) with true in Hm1.  simpl in Hm1. 
        lia. symmetry. apply HmS in H7. auto.
      + simpl. replace (tprice m1 <=? tprice m) with true in Hm1.  simpl in Hm1. 
        lia. symmetry. apply HmS in H7. auto.
    } } }
    { simpl in H6. destruct H6. 
    { exists b. split. auto. subst m0. simpl. split. auto. unfold Demand_property in H5.
      assert(In m (m::M0)). auto. apply H5 in H6. simpl in H6. 
      replace (tprice m <=? tprice m) with true in H6.
      simpl in H6. assert(demand_vol (tprice m) (b :: B0) >= tquantity m). lia. 
      unfold demand_vol in H7. simpl in H7.
      destruct (tprice m <=? oprice b) eqn:Ham. move /leP in Ham. lia. move /leP in Ham. 
      assert((filter (fun x : order => tprice m <=? oprice x) B0) = nil). eapply filter_nilB. 
      exact HbS. auto.
      rewrite H8 in H7. simpl in H7. 
      destruct m. simpl in H7. assert(Htemp:= tquantity_cond). move /ltP in Htemp. lia. auto.
    }
    { apply H1 in H6. destruct H6. exists x. split. simpl. right. apply H6. apply H6. 
      eauto. all:auto. 
      apply Sorted_inv in H3. apply H3. 
      eapply SortedreducedMI. simpl. auto. all:auto.


      unfold Demand_property. intros. unfold demand_vol. unfold Demand_property in H5. 
      unfold demand_vol in H5. simpl in H7. destruct H7. { subst m1. simpl. 
      assert(Hm1:In m (m::M0)). auto. apply H5 in Hm1. 
      simpl. simpl in Hm1. destruct (tprice m <=? oprice b) eqn:Ham1. 
      + simpl. replace (tprice m <=? tprice m) with true in Hm1. 
        replace (tprice m <=? tprice m) with true.
        simpl in Hm1. simpl. lia. auto.  auto. 
      + simpl. replace (tprice m <=? tprice m) with true in Hm1.
        replace (tprice m <=? tprice m) with true.
        simpl in Hm1. simpl. lia. auto.  auto. } 

    { assert(Hm1:In m1 (m::M0)). auto. apply H5 in Hm1. 
      simpl. simpl in Hm1. destruct (tprice m1 <=? oprice b) eqn:Ham1. 
      + simpl. replace (tprice m1 <=? tprice m) with true in Hm1. 
        replace (tprice m1 <=? tprice m) with true. 
        simpl in Hm1. simpl. lia. symmetry. apply HmS in H7. auto. symmetry. apply HmS in H7. auto. 
      + simpl. replace (tprice m1 <=? tprice m) with true in Hm1.  
        replace (tprice m1 <=? tprice m) with true. 
        simpl in Hm1. simpl. lia. symmetry. apply HmS in H7. auto. 
        symmetry. apply HmS in H7. auto. }
    } } Qed.


Lemma FOB_matchable_FOB M B A :
NoDup (ids B) -> 
Sorted bcompetitive B -> Sorted incr_price M -> 
Matching M B A -> forall m, In m (FOB_aux M B) -> 
exists b, In b B /\ idb m = id b /\ oprice b >= tprice m.
Proof. intros. assert(Matching M B A -> Demand_property M B). apply Matching_imply_DP. auto. auto. 
apply FOB_matchable_FOB_aux with (M:=M). all:auto. Qed. 

Lemma FOB_Matching M B A :
NoDup (ids A) -> NoDup (ids B) ->
Sorted bcompetitive B -> Sorted incr_price M -> 
Matching M B A -> Matching (FOB_aux M B) B A.
Proof.  unfold Matching. unfold Tvalid. unfold valid. intros. 
assert(HQb:(forall b : order, In b B -> Qty_bid (FOB_aux M B) (id b) <= oquantity b)).
{ intros. apply Qty_bid_FOB. auto. auto. }
assert(HQa:(forall a : order, In a A -> Qty_ask (FOB_aux M B) (id a) <= oquantity a)).
{ intros. assert(Qty_ask M (id a) <= oquantity a). apply H3. auto.
cut(Qty_ask (FOB_aux M B) (id a) = Qty_ask M (id a)). lia.
apply Qty_ask_FOB. cut(Vol M <= Qty_orders B). lia. apply Matching_Vol_B with (A:=A).
auto. auto. }
split. intros. apply FOB_matchable_FOB with (m:=t) in H3 as Hb.
apply (exist_a_FOB B A M) with (t2:=t) in H0 as Ha. 
destruct Ha as [a Ha]. destruct Hb as [b Hb]. exists b. exists a. destruct Ha as [Ha1 Ha]. destruct Ha as [Ha2 Ha3].
destruct Hb as [Hb1 Hb]. destruct Hb as [Hb2 Hb3].
split. auto.  split. auto. split. auto. split. auto. split. unfold tradable. lia.
split. cut(Qty_bid (FOB_aux M B) (idb t) >= tquantity t). apply HQb in Hb1.
rewrite Hb2. lia. apply Qty_bid1. auto.
split. cut(Qty_ask (FOB_aux M B) (ida t) >= tquantity t). apply HQa in Ha1.
rewrite Ha2. lia. apply Qty_ask1. auto.
 split. auto. auto. intros. apply H3 in H5.
destruct H5 as [b H5]. destruct H5 as [a H5]. exists a. split. apply H5. split. apply H5.
cut(oprice a <= tprice t1). lia. apply H5.  all:auto.  Qed. 


Lemma FOB_tprice_subset M B :
tprices (FOB_aux M B) [<=] tprices M.
Proof. apply FOB_aux_elim. firstorder. firstorder. simpl. intros.
destruct (lt_eq_lt_dec (tquantity m) (oquantity b)) eqn:f1. 
{ destruct s eqn:f2.
  { simpl. apply Subset_intro. auto. } { simpl. apply Subset_intro. auto. } } { simpl. unfold "[<=]". unfold "[<=]" in H1. simpl.  intros. simpl in H1. destruct H2.  auto. apply H1 in H2. auto. } Qed.

Lemma FOB_Uniform M B :
Uniform M -> Uniform (FOB_aux M B).
Proof. unfold Uniform. intros. apply uniform_subset with (l2:=(tprices M)). apply FOB_tprice_subset. auto. Qed.

Lemma FOB_Is_uniform M B A :
NoDup (ids A) -> NoDup (ids B) ->
Sorted bcompetitive B -> Sorted incr_price M -> 
Is_uniform M B A -> Is_uniform (FOB_aux M B) B A.
Proof. unfold Is_uniform. intros. split. apply FOB_Uniform. apply H3. apply FOB_Matching. all:auto. apply H3. Qed.


Lemma fair_asks_FOB M B A:
NoDup (ids A) -> NoDup (ids B) -> Is_fair_asks M A -> Matching M B A ->
Is_fair_asks (FOB_aux M B) A.
Proof. 
unfold Is_fair_asks. simpl. intros. destruct H3. destruct H4. 
rewrite Qty_ask_FOB. 
cut(Vol M <= Qty_orders B). lia.
eapply Matching_Vol_B. auto. exact H2. 
specialize (H1 a). specialize (H1 a').
destruct H5. 
rewrite H1. split. auto. split. auto. split. auto. 
assert(ids_ask_aux (FOB_aux M B) [<=] ids_ask_aux M).
apply Subset_asks_FOB. eauto. auto. Qed.


(* The fair on ask correctness lemma. *)
Lemma FOB_aux_correct M B A:
admissible B A /\ Matching M B A ->
Sorted bcompetitive B -> Sorted incr_price M -> 
Matching (FOB_aux M B) B A /\                                                       (* (a) *)
Vol(M) = Vol(FOB_aux M B) /\                                                        (* (b) *)
Is_fair_bids (FOB_aux M B) B /\                                                     (* (c) *)
(forall a, In a A -> Qty_ask M (id(a)) = Qty_ask (FOB_aux M B) (id(a)))/\           (* (d) *)
(Is_fair_asks M A -> Is_fair_asks (FOB_aux M B) A).
Proof. intros. split. apply FOB_Matching. all:auto. apply H. apply H. apply H.
split. rewrite (Vol_FOB M B). cut(Vol M <= Qty_orders B). lia.
eapply Matching_Vol_B. apply H. apply H. auto.
split. apply (fair_bids_FOB M B). apply H. all:auto. 
split. intros. symmetry. apply Qty_ask_FOB. 
cut(Vol M <= Qty_orders B). lia.
eapply Matching_Vol_B. apply H. apply H. intros. apply fair_asks_FOB.
apply H. apply H. auto. apply H. Qed. 

End Fair_Bid.



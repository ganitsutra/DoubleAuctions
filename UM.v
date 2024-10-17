Require Export Match.
Require Export MatchingAlter.
Require Export Fair.
Require Export Coq.Sorting.Mergesort Sorted SortLists.

Section UM.


Definition Is_optimal_uniform (M : list transaction)(B: list order)(A: list order) :=
  Is_uniform M B A /\ 
  (forall M': list transaction, Is_uniform M' B A -> Vol(M') <= Vol(M)).

(*Move this function into other file *)
Fixpoint Assign_Transaction_Price (n:nat) (l:list transaction):=
  match l with
  |nil=>nil
  |m::l'=> (Mk_transaction (idb m)  (ida m) n (tquantity m) (tquantity_cond m))::(Assign_Transaction_Price n l')
  end.

(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_is_uniform (l: list transaction)(n:nat):
  uniform (map tprice (Assign_Transaction_Price n l )).
Proof. induction l. simpl.  constructor. simpl. 
         case l eqn: H. simpl.  constructor. simpl. simpl in IHl. constructor;auto. Qed.
(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_is_p (l:list transaction)(m:transaction)(p:nat): 
In m (Assign_Transaction_Price p l) ->  (tprice m = p).
Proof. { intro H. induction l. auto. inversion H as [H0 |].  
         inversion H0 as [H1 ]. simpl. exact. apply IHl in H0. exact. } Qed.
(*Move this lemma into other file *)

Lemma Assign_Transaction_Price_elim (l: list transaction)(n:nat): 
forall m', In m' (Assign_Transaction_Price n l)-> 
exists m, In m l /\ idb m = idb m' /\ ida m = ida m' /\tquantity m = tquantity m'. 
  Proof. intros. { induction l. 
           { simpl in H. inversion H. }
           { simpl in H. destruct H.
             {  exists a. split. auto. split. subst m'. simpl. auto. subst m'. simpl. auto. }
             { apply IHl in H as H1. destruct H1 as [m H1]. exists m. 
               destruct H1 as [H2 H1]. destruct H1 as [H3 H1]. split.
               auto. split;auto. } } } Qed.
 
(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_elim_bid (l: list transaction)(n:nat) (m:transaction):
In m (Assign_Transaction_Price n l) -> In (idb m) (map idb l).
Proof. { induction l. intros. simpl. destruct H.
         intros. simpl in H. simpl. destruct H. left. 
         simpl in H. subst m. simpl. exact. right. apply IHl. exact. } Qed.
(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_elim_ask (l: list transaction)(n:nat) (m:transaction):
In m (Assign_Transaction_Price n l) -> In (ida m) (map ida l).
Proof. { induction l. intros. simpl. destruct H.
         intros. simpl in H. simpl. destruct H. left. 
         simpl in H. subst m. simpl. exact. right. apply IHl. exact. } Qed.
 (*Move this lemma into other file *)
Lemma Assign_Transaction_Price_bids (l: list transaction)(n:nat):
(map idb l) = (map idb (Assign_Transaction_Price n l)).
  Proof. { induction l. 
           { simpl. auto. }
           { simpl. f_equal. auto. } } Qed. 

(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_asks (l: list transaction)(n:nat):
  (map ida l) = (map ida (Assign_Transaction_Price n l)).
  Proof. { induction l. 
           { simpl. auto. }
           { simpl. f_equal. auto. } } Qed. 

(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_Qty_bid (l: list transaction)(b:order)(n:nat):
Qty_bid l (id b) = Qty_bid (Assign_Transaction_Price n l) (id b).
Proof. induction l. simpl. auto. simpl. 
       destruct (Nat.eqb (idb a) (id b)) eqn:Hba. lia. lia. Qed.
       
(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_Qty_ask (l: list transaction)(a:order)(n:nat):
Qty_ask l (id a) = Qty_ask (Assign_Transaction_Price n l) (id a).
Proof. induction l. simpl. auto. simpl. 
       destruct (Nat.eqb (ida a0) (id a)) eqn:Haa0. lia. lia. Qed.

(*Move this lemma into other file *)
Lemma Assign_Transaction_Price_size (l: list transaction)(n:nat):
Vol(l) = Vol((Assign_Transaction_Price n l)).
Proof. induction l. simpl. auto.
simpl. lia. Qed.


Lemma Assign_Transaction_Price_Matching (M: list transaction)(B A: list order)(p:nat):
admissible B A -> 
(forall t, In t M -> p <= price B (idb t) /\ price A (ida t) <= p) -> 
Matching M B A -> Matching (Assign_Transaction_Price p M) B A.
Proof. unfold Matching. unfold Tvalid. intros. destruct H1. destruct H2.
split. intros. unfold valid. assert(Ht:=H4).
 apply Assign_Transaction_Price_elim in H4. destruct H4.
destruct H4. destruct H5. destruct H6 as [H6 H6b]. apply H0 in H4 as H4a. destruct H4a. apply H1 in H4. unfold valid in H4.
destruct H4 as [b0 H4]. destruct H4 as [a0 H4]. destruct H4. destruct H9. destruct H10. destruct H11.
destruct H12. destruct H13. destruct H14. destruct H15. exists b0. exists a0. split. auto.
split. auto. split. lia. split. lia. split. auto. split. rewrite <- H6b. lia. split. rewrite <- H6b. lia.
split. rewrite H10 in H7. rewrite price_elim1 in H7. split. auto. apply H. 
rewrite (Assign_Transaction_Price_is_p M t p). auto. auto. 
rewrite H11 in H8.  rewrite price_elim1 in H8. split. auto. apply H.
rewrite (Assign_Transaction_Price_is_p M t p). auto. auto. split. 
intros. rewrite <- (Assign_Transaction_Price_Qty_bid M b p). apply H2. auto.
intros. rewrite <- (Assign_Transaction_Price_Qty_ask M a p). apply H3. auto. Qed.


Lemma Assign_Transaction_Price_fairA (M: list transaction)(A: list order)(n:nat):
Is_fair_asks M A -> Is_fair_asks ((Assign_Transaction_Price n M)) A.
Proof. unfold Is_fair_asks. intros. rewrite <- Assign_Transaction_Price_Qty_ask. 
apply H with (a:=a)(a':=a'). split. apply H0. split. apply H0. split. apply H0. 
replace ((ids_ask_aux M)) with (map ida M). rewrite (Assign_Transaction_Price_asks _ n).
replace ((map ida (Assign_Transaction_Price n M))) with (ids_ask_aux (Assign_Transaction_Price n M)).
apply H0. eauto. eauto. Qed.

Lemma Assign_Transaction_Price_fairB (M: list transaction)(B: list order)(n:nat):
Is_fair_bids M B -> Is_fair_bids ((Assign_Transaction_Price n M)) B.
Proof. unfold Is_fair_bids. intros. rewrite <- Assign_Transaction_Price_Qty_bid.
apply H with (b:=b)(b':=b'). split. apply H0. split. apply H0. split. apply H0. 
replace ((ids_bid_aux M)) with (map idb M). rewrite (Assign_Transaction_Price_bids _ n).
replace ((map idb (Assign_Transaction_Price n M))) with (ids_bid_aux (Assign_Transaction_Price n M )). 
apply H0. eauto. eauto. Qed.

Definition UM_aux B A:=
(Match (Decr_Bid.sort B) (Incr_Ask.sort A)).

Lemma UM_aux_Matching B A:
NoDup (ids B) -> NoDup (ids A) -> Matching (UM_aux B A) B A.
Proof. unfold UM_aux. intros. assert(perm (Decr_Bid.sort B) B). apply SortB_perm. 
assert(perm (Incr_Ask.sort A) A). apply SortA_perm. eapply Maching_permutation.
exact H1. exact H2. apply Match_Matching. apply SortA_NoDup. auto. apply SortB_NoDup. auto.  Qed.


Definition t0:= Mk_transaction 0 0 0 1 not1.

Definition Last_Transaction_Price M:= tprice ((last M t0)).

Lemma exists_opt_k (B:list order)(A:list order)(b:order)(a:order)(adm:admissible (b::B) (a::A)):
Sorted bcompetitive (b::B) -> 
Sorted acompetitive (a::A) -> 
(forall k M,
(Is_uniform M (b::B) (a::A)) -> 
oprice b >= oprice a ->
Vol(M)>=(min (oquantity b) (oquantity a)) -> 
(Qty_ask M (id a)) >= (min (oquantity b) (oquantity a))/\
(Qty_bid M (id b)) >= (min (oquantity b) (oquantity a))/\
((min (oquantity b) (oquantity a)) - Qty M (id b) (id a) = k) ->
(exists M0, (Is_uniform M0 (b::B) (a::A))/\
((min (oquantity b) (oquantity a)) - Qty M0 (id b) (id a) = 0)/\
Vol(M)=Vol(M0))).
Proof. revert B A b a adm. induction k. 
       { intros M Uni_M price_ab HvM HQa. exists M. split;auto. split;auto.
         apply HQa. }
       { intros M Uni_M price_ab HvM HQa. destruct HQa as [HQa HQb].
          destruct HQb as [HQb k_n].    (*Main induction case*)
          case (Nat.leb (oquantity b) (oquantity a)) eqn:Hab.
          { assert ((min (oquantity b) (oquantity a)) = oquantity b). 
            eapply min_l. move /leP in Hab;lia.
            assert(Qty M (id b) (id a) < (oquantity b)). lia.
            rewrite H1 in k_n.
            rewrite H1 in HQa. rewrite H1 in HQb. rewrite H1.
            assert(Qty M (id b) (id a) < Qty_bid M (id b)). lia.
            apply Qty_lt_Qty_bid_m_exists in H3.
            assert(Qty M (id b) (id a) < Qty_ask M (id a)). lia.
            apply Qty_lt_Qty_ask_m_exists in H4.
            destruct H3 as [m1 H3]. destruct H4 as [m2 H4]. destruct H3. destruct H5. destruct H4.
            destruct H7. apply increase_ab_quantity_Is_uniform with (m1:=m1)(m2:=m2)(b:=b)(a:=a) in Uni_M.
            apply IHk in Uni_M. destruct Uni_M as [M0 Uni_M]. destruct Uni_M as [U1 U2].
            destruct U2 as [U2 U3]. exists M0. split. auto. split. rewrite <- H1. auto.
            auto. rewrite (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.  intro.
            subst m1. lia. rewrite <- (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.  
            intro;subst m1;lia. split. 
            rewrite (increase_ab_quantity_Qty_ask _ m1 m2 b a). all:auto. intro;subst m1;lia. lia. 
            split. rewrite (increase_ab_quantity_Qty_bid _ m1 m2 b b a). all:auto. intro;subst m1;lia. lia.
            rewrite (increase_ab_quantity_extra _ m1 m2 b a). all:auto. intro;subst m1;lia. lia. apply adm. 
            apply adm.  intro;subst m1;lia.
          }
          { assert ((min (oquantity b) (oquantity a)) = oquantity a). 
            eapply min_r. move /leP in Hab;lia.
            assert(Qty M (id b) (id a) < (oquantity a)). lia.
            rewrite H1 in k_n.
            rewrite H1 in HQa. rewrite H1 in HQb. rewrite H1.
            assert(Qty M (id b) (id a) < Qty_bid M (id b)). lia.
            apply Qty_lt_Qty_bid_m_exists in H3.
            assert(Qty M (id b) (id a) < Qty_ask M (id a)). lia.
            apply Qty_lt_Qty_ask_m_exists in H4.
            destruct H3 as [m1 H3]. destruct H4 as [m2 H4]. destruct H3. destruct H5. destruct H4.
            destruct H7.  apply increase_ab_quantity_Is_uniform with (m1:=m1)(m2:=m2)(b:=b)(a:=a) in Uni_M.
            apply IHk in Uni_M. destruct Uni_M as [M0 Uni_M]. destruct Uni_M as [U1 U2].
            destruct U2 as [U2 U3]. exists M0. split. auto. split. rewrite <- H1. auto.
            auto. rewrite (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.  intro.
            subst m1. lia. rewrite <- (increase_ab_quantity_Vol _ m1 m2 b a). all:auto. 
            intro;subst m1;lia. split. 
            rewrite (increase_ab_quantity_Qty_ask _ m1 m2 b a). all:auto. intro;subst m1;lia. lia. 
            split. rewrite (increase_ab_quantity_Qty_bid _ m1 m2 b b a). all:auto. intro;subst m1;lia. lia.
            rewrite (increase_ab_quantity_extra _ m1 m2 b a). all:auto. intro;subst m1;lia. lia.
            apply adm. apply adm. intro;subst m1;lia.
          } } Qed.

(*Set M:=FAIR M in this Lemma. Also prove that FAIR does not change uniform property*)
Lemma exists_opt (B:list order)(A:list order)(M:list transaction)(b:order)(a:order)
(ndtb: NoDup (timesof (b::B)))(ndta:NoDup (timesof (a::A))):
NoDup (ids (a::A)) -> NoDup (ids (b::B)) ->
Sorted bcompetitive (b::B) -> 
Sorted acompetitive (a::A) -> 
(Is_uniform M (b::B) (a::A)) -> 
oprice b >= oprice a ->
Vol(M)>=(min (oquantity b) (oquantity a)) -> 
(exists OPT, (Is_uniform OPT (b::B) (a::A))/\
(Qty OPT (id b) (id a) = (min (oquantity b) (oquantity a)))/\
Vol(M)=Vol(OPT)).
Proof. set(M':= Fair M (b::B) (a::A)).
intros. destruct ((min (oquantity b) (oquantity a)) - Qty M' (id b) (id a)) eqn:Hk.
{ assert(admissible (b::B) (a::A) /\ Matching M (b::B) (a::A)).
  split. unfold admissible. all:auto. apply H3.
  apply Fair_main in H6. exists M'. split. split. apply Fair_Uniform. apply H3. apply H6. split.
  assert(HQb:= (Qty_le_Qty_bid M' (id b) (id a))).
  assert(HQa:= (Qty_le_Qty_ask M' (id b) (id a))).
  assert(Qty_bid M' (id b) <= (oquantity b)). apply H6. auto.
  assert(Qty_ask M' (id a) <= (oquantity a)). apply H6. auto. lia.
  apply H6. 
} 
{ assert(admissible (b::B) (a::A) /\ Matching M (b::B) (a::A)).
  split. unfold admissible. all:auto. apply H3. apply Fair_main in H6. destruct H6. destruct H7.
  apply exists_opt_k with (M:=M')(A:=A)(B:=B)(k:=S n)(b:=b)(a:=a) in H1.
  destruct H1 as [M0 H1]. destruct H1. destruct H9. exists M0. split. auto.
  split. assert(HQb:= (Qty_le_Qty_bid M0 (id b) (id a))).
  assert(HQa:= (Qty_le_Qty_ask M0 (id b) (id a))). 
  assert(Qty_bid M0 (id b) <= (oquantity b)). apply H1. auto.
  assert(Qty_ask M0 (id a) <= (oquantity a)). apply H1. auto. lia. 
  subst M'. lia. all:auto. unfold admissible. auto. split.
  apply Fair_Uniform. apply H3. subst M'.
  apply H6. subst M'. lia. split. subst M'. apply Is_fair_ab_full. split. unfold admissible. auto.
  split. apply H3. split. auto. split. auto. lia.
  split. subst M'. apply Is_fair_ab_full. split. unfold admissible. auto.
  split. apply H3. split. auto. split. auto. lia. auto. 
} Qed.



(*Main Lemma: first prove this.*)
Lemma Match_OPT (B:list order)(A:list order)(M:list transaction)(ndtb : NoDup (timesof (B)))(ndta : NoDup (timesof (A))):
(NoDup (ids A)) -> (NoDup (ids B)) ->
Sorted bcompetitive B -> 
Sorted acompetitive A -> 
Is_uniform M B A -> Vol(M) <= Vol(Match B A).
Proof. revert M ndtb ndta. apply Match_elim. 
- firstorder. unfold Tvalid in H4. unfold valid in H4. induction M as [|t M]. simpl.
  auto. assert(In t (t::M)). simpl;auto. apply H4 in H7. destruct H7. destruct H7.
  firstorder.
- firstorder. unfold Tvalid in H4. unfold valid in H4. induction M as [|t M]. simpl.
  auto. assert(In t (t::M)). simpl;auto. apply H4 in H7. firstorder.
- intros.
  assert(HaS: forall x, In x A0 -> (acompetitive a x)). apply Sorted_ointroA_tight. auto.
  assert(HbS: forall x, In x B0 -> (bcompetitive b x)). apply Sorted_ointroB_tight. auto.
  destruct H7 as [Hu Hm]. unfold Uniform in Hu. 
  destruct (PeanoNat.Nat.eqb (oprice a - oprice b) 0) eqn:price.
  { destruct (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
   { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. 
      destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (exists_opt B0 A0 _ _ _) in Hv. 
        - destruct Hv as [OPT Hv]. destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
          match goal with |[ |- context[_ (Match (?x::B0) A0)]] => set(a1:=x) end.
          assert(HM0:exists M0, (Is_uniform M0 (a1::B0) A0)/\(Vol(OPT) = Vol(M0) + oquantity a)). 
          destruct Hvu as [Hopt1 Hopt2].  apply remove_ab_transactions_main in Hopt2. destruct Hopt2 as [M0 Hopt2].
          unfold reduced in Hopt2. rewrite f1 in Hopt2. simpl in Hopt2. 
          + exists M0. split. subst a1.  apply Hopt2. 
            replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hopt2. apply Hopt2. lia. 
          + apply Hopt1. 
          + auto. 
          + auto. destruct HM0 as [M0 HMv].   destruct HMv as [HMu HMQ]. rewrite HMQ. 
            cut(Vol M0 <= Vol (Match (a1 :: B0) A0)). lia. subst a1. apply H. all:simpl;auto. eauto. eauto. 
            apply SortedreducedB with (b:=b). all:simpl;auto. apply Sorted_inv in H6. apply H6. 
        - auto. 
        - auto.
        - auto.
        - auto.
        - auto.
        - auto.
        - split. auto. auto.
        - move /eqP in price. lia.
      } 
    }
    { simpl. destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (exists_opt B0 A0 _ _ _) in Hv. all:auto. destruct Hv as [OPT Hv]. 
        destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
        assert(HM0:exists M0, (Is_uniform M0 B0 A0)/\
        (Vol(OPT) = Vol(M0) + oquantity a)). destruct Hvu as [Hopt1 Hopt2].
        apply remove_ab_transactions_main in Hopt2. destruct Hopt2 as [M0 Hopt2].
        unfold reduced in Hopt2. rewrite f1 in Hopt2. simpl in Hopt2. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hopt2.
        exists M0. all:auto. lia.  destruct HM0 as [M0 HMv]. 
        destruct HMv as [HMu HMQ]. rewrite HMQ. cut(Vol M0 <= Vol (Match B0 A0)).
        lia. apply H0. all:simpl;auto. eauto. eauto. eauto. eauto. apply Sorted_inv in H5. apply H5.
        apply Sorted_inv in H6. apply H6. split. auto. auto. 
        move /eqP in price. lia.
      }
    }
  }
  { simpl. destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (exists_opt B0 A0 _ _ _) in Hv. all:auto. destruct Hv as [OPT Hv]. 
        destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
        match goal with |[ |- context[_ (Match B0 (?x::A0))]] => set(a1:=x) end.  
        assert(HM0:exists M0, (Is_uniform M0 B0 (a1::A0))/\
        (Vol(OPT) = Vol(M0) + oquantity b)). destruct Hvu as [Hopt1 Hopt2].
        apply remove_ab_transactions_main in Hopt2. destruct Hopt2 as [M0 Hopt2]. 
        unfold reduced in Hopt2. rewrite f1 in Hopt2. simpl in Hopt2. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in Hopt2.
        exists M0. split. subst a1. apply Hopt2. destruct Hopt2. rewrite H8. lia. 
        lia. auto. lia. destruct HM0 as [M0 HMv]. 
        destruct HMv as [HMu HMQ]. rewrite HMQ. cut(Vol M0 <= Vol (Match B0 (a1 :: A0))).
        lia. subst a1. apply H1. all:simpl;auto. eauto. eauto. apply Sorted_inv in H5. apply H5.
        apply SortedreducedA with (a:=a). all:simpl;auto. split. auto. auto. 
        move /eqP in price. lia.
      }
    }
  } assert(HaS2: forall x, In x A0 -> (Nat.leb (oprice a) (oprice x))). 
    apply Sorted_ointroA. auto. 
    assert(HbS2: forall x, In x B0 -> (Nat.leb (oprice x) (oprice b))).
    apply Sorted_ointroB. auto. 
    assert(~matchable (b :: B0) (a::A0)). 
    + intro. unfold matchable in H7. 
        destruct H7 as [b0 H9]. destruct H9 as [a0' H9]. destruct H9. 
        destruct H8. simpl in H7. simpl in H8. destruct H7;destruct H8.
        -- subst b0;subst a0'. unfold tradable in H9. move /eqP in price. lia.
        -- subst a0'. apply HbS2 in H8. unfold tradable in H9. move /eqP in price. 
           move /leP in H8. lia.
        -- subst b0. apply HaS2 in H7. unfold tradable in H9. move /eqP in price. 
           move /leP in H7. lia.
        -- apply HaS2 in H7. apply HbS2 in H8. unfold tradable in H9. 
           move /eqP in price. move /leP in H7. move /leP in H8. lia.
    + apply not_matchable_matching_nil with (M:=M) in H7. rewrite H7. simpl. lia. auto.
Qed.

Definition UM B A:= 
           let B:= (Decr_Bid.sort B) in
           let A:= (Incr_Ask.sort A) in
           let M:= (Match B A) in
           let p:= Last_Transaction_Price M in
           Assign_Transaction_Price p M.


Theorem UM_Fair (B:list order)(A:list order):
admissible B A -> Is_fair (UM B A) B A.
Proof. unfold admissible. intros. unfold Is_fair.
               split.
                 { unfold UM. apply Assign_Transaction_Price_fairA. 
apply Is_fair_asks_perm with (M1:=(Match (Decr_Bid.sort B) (Incr_Ask.sort A)))(M2:=(Match (Decr_Bid.sort B) (Incr_Ask.sort A)))(A1:=(Incr_Ask.sort A))(A2:=A). auto. apply Permulation_perm.
apply Permutation.Permutation_sym. apply Incr_Ask.Permuted_sort. 
 apply Match_Fair_ask. 
apply perm_nodup with (l:=(ids B)). apply ids_perm. apply Permulation_perm. apply Decr_Bid.Permuted_sort. apply H. 
apply Decr_Bid.Sorted_sort.
apply perm_nodup with (l:=(ids A)). apply ids_perm. apply Permulation_perm. apply Incr_Ask.Permuted_sort. apply H. 
apply Incr_Ask.Sorted_sort.
}
                 { unfold UM. apply Assign_Transaction_Price_fairB. 
apply Is_fair_bids_perm with (M1:=(Match (Decr_Bid.sort B) (Incr_Ask.sort A)))(M2:=(Match (Decr_Bid.sort B) (Incr_Ask.sort A)))(B1:=(Decr_Bid.sort B))(B2:=B). auto. apply Permulation_perm.
apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort. 
 apply Match_Fair_bid. 
apply perm_nodup with (l:=(ids B)). apply ids_perm. apply Permulation_perm. apply Decr_Bid.Permuted_sort. apply H. 
apply Decr_Bid.Sorted_sort. }  Qed.


Theorem UM_Matching (B:list order)(A:list order):
admissible B A -> Matching (UM B A) B A.
Proof. unfold admissible. intros. unfold UM. apply Assign_Transaction_Price_Matching. auto.
intros. split.
{ unfold Last_Transaction_Price. apply Match_priceB in H0. rewrite (price_perm _ (Decr_Bid.sort B) _).
 apply H. apply Permulation_perm. apply Decr_Bid.Permuted_sort. auto. apply perm_nodup with (l:=(ids B)). apply ids_perm. apply Permulation_perm. apply Decr_Bid.Permuted_sort. apply H. 
apply Decr_Bid.Sorted_sort. apply perm_nodup with (l:=(ids A)). apply ids_perm. apply Permulation_perm. apply Incr_Ask.Permuted_sort. apply H. 
apply Incr_Ask.Sorted_sort. }
{ unfold Last_Transaction_Price. apply Match_priceA in H0. rewrite (price_perm _ (Incr_Ask.sort A) _).
 apply H. apply Permulation_perm. apply Incr_Ask.Permuted_sort. auto. apply perm_nodup with (l:=(ids B)). apply ids_perm. apply Permulation_perm. apply Decr_Bid.Permuted_sort. apply H. 
apply Decr_Bid.Sorted_sort. apply perm_nodup with (l:=(ids A)). apply ids_perm. apply Permulation_perm. apply Incr_Ask.Permuted_sort. apply H. 
apply Incr_Ask.Sorted_sort. } eapply Maching_permutation_full with (B1:=(Decr_Bid.sort B))(A1:=(Incr_Ask.sort A)).
apply Permulation_perm. apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort.
apply Permulation_perm. apply Permutation.Permutation_sym. apply Incr_Ask.Permuted_sort.
 exact. eapply Match_Matching. 
 apply perm_nodup with (l:=(ids A)). apply ids_perm. apply Permulation_perm. apply Incr_Ask.Permuted_sort. apply H.
apply perm_nodup with (l:=(ids B)). apply ids_perm. apply Permulation_perm. apply Decr_Bid.Permuted_sort. apply H. 
  Qed.


Theorem UM_Is_optimal_uniform (B:list order)(A:list order):
admissible B A -> Is_optimal_uniform (UM B A) B A.
Proof. unfold admissible. intros. 
               split. split. unfold UM. unfold Uniform.
apply Assign_Transaction_Price_is_uniform. apply UM_Matching. auto. intros. unfold UM. 
rewrite <- Assign_Transaction_Price_size. apply Match_OPT.
apply perm_nodup with (l:=(timesof B)). apply timesof_perm. apply Permulation_perm. apply Decr_Bid.Permuted_sort. apply H. 
apply perm_nodup with (l:=(timesof A)). apply timesof_perm. apply Permulation_perm. apply Incr_Ask.Permuted_sort. apply H.
 apply perm_nodup with (l:=(ids A)). apply ids_perm. apply Permulation_perm. apply Incr_Ask.Permuted_sort. apply H.
apply perm_nodup with (l:=(ids B)). apply ids_perm. apply Permulation_perm. apply Decr_Bid.Permuted_sort. apply H. 
apply Decr_Bid.Sorted_sort. apply Incr_Ask.Sorted_sort. destruct H0. split. auto. 
eapply Maching_permutation_full with (B2:=(Decr_Bid.sort B))(A2:=(Incr_Ask.sort A)) in H1. exact H1. 
apply Permulation_perm.  apply Decr_Bid.Permuted_sort.
apply Permulation_perm. apply Incr_Ask.Permuted_sort.
 exact.  Qed.


Theorem UM_correct (B:list order)(A:list order):
admissible B A -> Is_optimal_uniform (UM B A) B A/\ Is_fair (UM B A) B A.
Proof. intros. split. apply UM_Is_optimal_uniform. auto. apply UM_Fair. auto. Qed.

End UM.


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
Extraction "Demonstration/certified.ml" UM Qty_ask Qty_bid.
Require Export UM.

Section MM.


Definition MM B A:=
FOA (Match (Decr_Bid.sort B) (Decr_Ask.sort A)) A.

(*Definition MM_matching (B:list order) (A:list order) : (list transaction) :=
  FOA (UM B A) A. *)

Theorem MM_Is_Matching (B:list order)(A:list order):
admissible B A -> Matching (MM B A) B A.
Proof. unfold MM. intros. apply FOA_correct. split. auto. eapply Maching_permutation_full with (A1:=(Decr_Ask.sort A))
(B1:=(Decr_Bid.sort B)). apply perm_sym. apply Permulation_perm. apply Decr_Bid.Permuted_sort. 
apply perm_sym. apply Permulation_perm. apply Decr_Ask.Permuted_sort. exact. 
 apply Match_Matching. 
apply perm_nodup with (l:=(ids A)). apply ids_perm. apply Permulation_perm. apply Decr_Ask.Permuted_sort. apply H. 
apply perm_nodup with (l:=(ids B)). apply ids_perm. apply Permulation_perm. apply Decr_Bid.Permuted_sort. apply H.
 Qed.

Theorem MM_Is_fair (B:list order)(A:list order):
admissible B A -> Is_fair (MM B A) B A.
Proof. unfold MM. unfold Is_fair.
intros. split.
{ eapply FOA_correct. split. exact H. eapply Maching_permutation_full with (A1:=(Decr_Ask.sort A))
(B1:=(Decr_Bid.sort B)). apply perm_sym. apply Permulation_perm. apply Decr_Bid.Permuted_sort. 
apply perm_sym. apply Permulation_perm. apply Decr_Ask.Permuted_sort. exact. 
 apply Match_Matching. apply perm_nodup with (l:=(ids A)). apply ids_perm. apply Permulation_perm. apply Decr_Ask.Permuted_sort. apply H. apply perm_nodup with (l:=(ids B)). apply ids_perm. apply Permulation_perm. apply Decr_Bid.Permuted_sort. apply H. } 
{ eapply FOA_correct. split. exact H. eapply Maching_permutation_full with (A1:=(Decr_Ask.sort A))
(B1:=(Decr_Bid.sort B)). apply perm_sym. apply Permulation_perm. apply Decr_Bid.Permuted_sort.
 apply perm_sym. apply Permulation_perm. apply Decr_Ask.Permuted_sort. exact. 
 apply Match_Matching. apply perm_nodup with (l:=(ids A)). apply ids_perm. apply Permulation_perm. apply Decr_Ask.Permuted_sort. apply H. apply perm_nodup with (l:=(ids B)). apply ids_perm. apply Permulation_perm. apply Decr_Bid.Permuted_sort. apply H. eapply Is_fair_bids_perm with (B1:=(Decr_Bid.sort B)) .
exact. apply perm_sym.  apply Permulation_perm. apply Decr_Bid.Permuted_sort.
 apply Match_Fair_on_Bids. split. eapply admissible_perm. 
apply Permulation_perm. apply Decr_Bid.Permuted_sort. 
apply Permulation_perm. apply Decr_Ask.Permuted_sort.
exact H. apply Decr_Bid.Sorted_sort. } Qed.

(*
(*Move this lemma into another file*)
Lemma exists_ttq_top_bid 
(B:list order)(A:list order)(M:list transaction)(b:order)
(NDA:NoDup (ids A))(NDB:NoDup (ids (b::B))):
Sorted bcompetitive (b::B) -> 
 (Matching M (b::B) A) -> 
(exists M', (Matching M' (b::B) A)/\
(Qty_bid M' (id b) >= min (oquantity b) (Vol(M)))/\
Vol(M) = Vol(M')).
Proof. Admitted.

Lemma MM_exists_opt_k (B A:list order)(b a: order)
(NDA:NoDup (ids (a::A)))(NDB:NoDup (ids (b::B))):
Sorted bcompetitive (b::B) -> 
Sorted rev_acompetitive (a::A) -> 
(forall k M, Matching M (b::B) (a::A) ->
oprice b >= oprice a ->
Vol(M) >= (min (oquantity b) (oquantity a)) ->
(*(Qty_bid M (id b) >= (min (oquantity b) (oquantity a))) ->*)
(min (oquantity b) (oquantity a)) - Qty M (id b) (id a) = k ->
(exists M0, (Matching M0 (b::B) (a::A))/\Vol(M)=Vol(M0)/\
(min (oquantity b) (oquantity a)) - Qty M0 (id b) (id a) = 0)).
Proof. revert B A b a NDA NDB. induction k. 
       { intros M Match price_ab HvM HQab. exists M. split;auto. }
       { intros M Match price_ab HvM k_n.    (*Main induction case*)
          case (Nat.leb (oquantity b) (oquantity a)) eqn:Hab.
          { assert ((min (oquantity b) (oquantity a)) = oquantity b). 
            eapply min_l. move /leP in Hab;lia.
            assert(Qty M (id b) (id a) < (oquantity b)). lia.
            rewrite H1 in k_n.
            rewrite H1. assert(Qbid:((Qty_bid M (id b)) < (oquantity b))\/((Qty_bid M (id b)) >= (oquantity b))).
            lia. destruct Qbid as [Qbid | Qbid].
            assert(Htmp:Qty M (id b) (id a) < Qty_bid M (id b)\/Qty M (id b) (id a) >= Qty_bid M (id b)). lia.
            destruct Htmp as [H3 | H3]. 
            assert(Qask:((Qty_ask M (id a)) > (oquantity a))\/((Qty_ask M (id a)) = (oquantity a))\/
            ((Qty_ask M (id a)) < (oquantity a))). lia. destruct Qask as [Qask | Qask].
            assert(((Qty_ask M (id a)) <= (oquantity a))). apply Match. all:auto. lia.
            destruct Qask as [Qask | Qask].
            { (* Case when a is fully traded in M *)
              apply Qty_lt_Qty_bid_m_exists in H3.  assert(Qty M (id b) (id a) < Qty_ask M (id a)). lia.
              apply Qty_lt_Qty_ask_m_exists in H4. destruct H3 as [m1 H3]. destruct H4 as [m2 H4]. destruct H3.
              destruct H5. destruct H4. destruct H7. 
              apply increase_ab_quantity_Matching with (m1:=m1)(m2:=m2)(b:=b)(a:=a) in Match.
              apply IHk in Match. destruct Match as [M0 Match].          
              exists M0. split. apply Match. split. rewrite (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia. apply Match. rewrite <- H1. apply Match.  
              rewrite <- (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia.  rewrite (increase_ab_quantity_extra _ m1 m2 b a). all:auto. intro;subst m1;lia.
              lia. intro;subst m1;lia.
             }
             { apply Qty_lt_Qty_bid_m_exists in H3. destruct H3 as [m H3]. destruct H3.
               destruct H4. apply increase_b_quantity_Matching with (m:=m)(b:=b)(a:=a) in Match.
               apply IHk in Match. destruct Match as [M0 Match]. exists M0. split. apply Match. split.
               rewrite (increase_b_quantity_Vol _ m b a). all:auto. apply Match. rewrite <- H1. apply Match.  
               rewrite <- (increase_b_quantity_Vol _ m b a). all:auto. rewrite H1. 
               rewrite (increase_b_quantity_extra _ m b a).
               all:auto. lia.
             } 

          }
*)

Lemma MM_exists_opt_k (B A:list order)(b a: order)
(NDA:NoDup (ids (a::A)))(NDB:NoDup (ids (b::B))):
Sorted bcompetitive (b::B) -> 
Sorted rev_acompetitive (a::A) -> 
(forall k M, Matching M (b::B) (a::A) ->
oprice b >= oprice a ->
Vol(M) >= (min (oquantity b) (oquantity a)) ->
(Qty_bid M (id b) >= (min (oquantity b) (oquantity a))) ->
(min (oquantity b) (oquantity a)) - Qty M (id b) (id a) = k ->
(exists M0, (Matching M0 (b::B) (a::A))/\Vol(M)=Vol(M0)/\
(min (oquantity b) (oquantity a)) - Qty M0 (id b) (id a) = 0)).
Proof. revert B A b a NDA NDB. induction k. 
       { intros M Match price_ab HvM HQb HQab. exists M. split;auto. }
       { intros M Match price_ab HvM HQb k_n.    (*Main induction case*)
          case (Nat.leb (oquantity b) (oquantity a)) eqn:Hab.
          { assert ((min (oquantity b) (oquantity a)) = oquantity b). 
            eapply min_l. move /leP in Hab;lia.
            assert(Qty M (id b) (id a) < (oquantity b)). lia.
            rewrite H1 in k_n.
            rewrite H1. assert(Qbid:((Qty_bid M (id b)) < (oquantity b))\/((Qty_bid M (id b)) >= (oquantity b))).
            lia. destruct Qbid as [Qbid | Qbid].
            assert(((Qty_bid M (id b)) <= (oquantity b))). apply Match. all:auto. lia.
            assert(Qty M (id b) (id a) < Qty_bid M (id b)). lia.
            assert(Qask:((Qty_ask M (id a)) > (oquantity a))\/((Qty_ask M (id a)) = (oquantity a))\/
            ((Qty_ask M (id a)) < (oquantity a))). lia. destruct Qask as [Qask | Qask].
            assert(((Qty_ask M (id a)) <= (oquantity a))). apply Match. all:auto. lia.
            destruct Qask as [Qask | Qask].
            { (* Case when a is fully traded in M *)
              apply Qty_lt_Qty_bid_m_exists in H3.  assert(Qty M (id b) (id a) < Qty_ask M (id a)). lia.
              apply Qty_lt_Qty_ask_m_exists in H4. destruct H3 as [m1 H3]. destruct H4 as [m2 H4]. destruct H3.
              destruct H5. destruct H4. destruct H7. 
              apply increase_ab_quantity_Matching with (m1:=m1)(m2:=m2)(b:=b)(a:=a) in Match.
              apply IHk in Match. destruct Match as [M0 Match].          
              exists M0. split. apply Match. split. rewrite (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia. apply Match. rewrite <- H1. apply Match.  
              rewrite <- (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia. rewrite H1. rewrite increase_ab_quantity_Qty_bid. all:auto. 
              intro;subst m1;lia. rewrite (increase_ab_quantity_extra _ m1 m2 b a). all:auto. intro;subst m1;lia.
              lia. intro;subst m1;lia.
             }
             { apply Qty_lt_Qty_bid_m_exists in H3. destruct H3 as [m H3]. destruct H3.
               destruct H4. apply increase_b_quantity_Matching with (m:=m)(b:=b)(a:=a) in Match.
               apply IHk in Match. destruct Match as [M0 Match]. exists M0. split. apply Match. split.
               rewrite (increase_b_quantity_Vol _ m b a). all:auto. apply Match. rewrite <- H1. apply Match.  
               rewrite <- (increase_b_quantity_Vol _ m b a). all:auto. rewrite H1. 
               rewrite increase_b_quantity_Qty_bid. all:auto. rewrite (increase_b_quantity_extra _ m b a).
               all:auto. lia.
             }
          }
          { assert ((min (oquantity b) (oquantity a)) = oquantity a). 
            eapply min_r. move /leP in Hab;lia.
            assert(Qty M (id b) (id a) < (oquantity a)). lia.
            rewrite H1 in k_n. rewrite H1 in HQb.  rewrite H1.
            assert(Qty M (id b) (id a) < Qty_bid M (id b)). lia.
            assert(Qask:((Qty_ask M (id a)) > (oquantity a))\/((Qty_ask M (id a)) = (oquantity a))\/
            ((Qty_ask M (id a)) < (oquantity a))). lia. destruct Qask as [Qask | Qask].
            assert(((Qty_ask M (id a)) <= (oquantity a))). apply Match. all:auto. lia.
            destruct Qask as [Qask | Qask].
            { (* Case when a is fully traded in M *)
              apply Qty_lt_Qty_bid_m_exists in H3.  assert(Qty M (id b) (id a) < Qty_ask M (id a)). lia.
              apply Qty_lt_Qty_ask_m_exists in H4. destruct H3 as [m1 H3]. destruct H4 as [m2 H4]. destruct H3.
              destruct H5. destruct H4. destruct H7. 
              apply increase_ab_quantity_Matching with (m1:=m1)(m2:=m2)(b:=b)(a:=a) in Match.
              apply IHk in Match. destruct Match as [M0 Match].          
              exists M0. split. apply Match. split. rewrite (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia. apply Match. rewrite <- H1. apply Match.  
              rewrite <- (increase_ab_quantity_Vol _ m1 m2 b a). all:auto.
              intro. subst m1. lia. rewrite H1. rewrite increase_ab_quantity_Qty_bid. all:auto. 
              intro;subst m1;lia. rewrite (increase_ab_quantity_extra _ m1 m2 b a). all:auto. intro;subst m1;lia.
              lia. intro;subst m1;lia.
             }
             { apply Qty_lt_Qty_bid_m_exists in H3. destruct H3 as [m H3]. destruct H3.
               destruct H4. apply increase_b_quantity_Matching with (m:=m)(b:=b)(a:=a) in Match.
               apply IHk in Match. destruct Match as [M0 Match]. exists M0. split. apply Match. split.
               rewrite (increase_b_quantity_Vol _ m b a). all:auto. apply Match. rewrite <- H1. apply Match.  
               rewrite <- (increase_b_quantity_Vol _ m b a). all:auto. rewrite H1. 
               rewrite increase_b_quantity_Qty_bid. all:auto. rewrite (increase_b_quantity_extra _ m b a).
               all:auto. lia.
             }
} } Qed.



Lemma MM_exists_opt (B:list order)(A:list order)(M:list transaction)(b:order)(a:order)
:
admissible (b::B)(a::A) ->
Sorted bcompetitive (b::B) -> 
Sorted rev_acompetitive (a::A) -> 
(Matching M (b::B) (a::A)) -> 
oprice b >= oprice a ->
Vol(M) >= (min (oquantity b) (oquantity a)) ->
(exists M', (Matching M' (b::B) (a::A))/\
(min (oquantity b) (oquantity a)) = Qty M' (id b) (id a)/\Vol(M)=Vol(M')).
Proof. intro Adm. intros. 
set(M0:= FOB M (b::B)). assert(Hf:= (FOB_correct M (b::B) (a::A))). 
assert(admissible (b :: B) (a :: A) /\ Matching M (b :: B) (a :: A)). auto. apply Hf in H4 as H4a. destruct H4a.
destruct H6. destruct H7. destruct ((min (oquantity b) (oquantity a)) - Qty (FOB M (b :: B)) (id b) (id a)) eqn:Hk.
exists (FOB M (b :: B)). split. auto. split. 
assert(HQb:= Qty_le_Qty_ask (FOB M (b :: B)) (id b) (id a)).
assert(Qty_ask (FOB M (b :: B)) (id a) <= oquantity a). apply H5. auto.
assert(HQa:= Qty_le_Qty_bid (FOB M (b :: B)) (id b) (id a)).
assert(Qty_bid (FOB M (b :: B)) (id b) <= oquantity b). apply H5. auto. lia. auto.
apply MM_exists_opt_k with (M:=(FOB M (b::B)))(A:=A)(B:=B)(k:=S n)(b:=b)(a:=a) in H5.
destruct H5 as [M1 H5]. destruct H5. destruct H9. exists M1. split. auto.
split. 
assert(HQb:= Qty_le_Qty_ask (M1) (id b) (id a)).
assert(Qty_ask (M1) (id a) <= oquantity a). apply H5. auto.
assert(HQa:= Qty_le_Qty_bid (M1) (id b) (id a)).
assert(Qty_bid (M1) (id b) <= oquantity b). apply H5. auto. lia. auto. lia. 
all:auto. apply Adm. apply Adm. lia. apply (Is_FOB_ab_full_bid M B A b a).
split. auto. split. auto. split. auto.  lia. Qed.


Theorem MM_aux_optimal (B:list order)(A:list order)(M:list transaction):
admissible B A ->
Sorted bcompetitive B -> 
Sorted rev_acompetitive A -> 
(Matching M B A) -> 
Vol(M) <= Vol(Match B A).
Proof. revert M. apply Match_elim. 
- firstorder. unfold Tvalid in H3. unfold valid in H3. induction M as [|t M]. simpl.
auto. assert(In t (t::M)). simpl;auto. apply H2 in H8. destruct H8. destruct H8.
firstorder.
- firstorder. unfold Tvalid in H3. unfold valid in H3. induction M as [|t M]. simpl.
auto. assert(In t (t::M)). simpl;auto. apply H2 in H8. firstorder.
- intros b B0 a A0 H H0 H1 H2 M H3. assert(H4:=H3). intros. 
assert(HaS: forall x, In x A0 -> (acompetitive x a)). apply Sorted_ointro_not_A_tight. auto.
assert(HbS: forall x, In x B0 -> (bcompetitive b x)). apply Sorted_ointroB_tight. auto.
destruct (PeanoNat.Nat.eqb (oprice a - oprice b) 0) eqn:price.
{ destruct (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. 
      destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (MM_exists_opt B0 A0 _ _ _) in Hv. all:auto. destruct Hv as [OPT Hv]. 
        destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
        match goal with |[ |- context[_ (Match (?x::B0) A0)]] => set(b1:=x) end.  
        assert(HM0:exists M0, (Matching M0 (b1::B0) A0)/\
        (Vol(OPT) = Vol(M0) + oquantity a)). apply remove_ab_transactions_matching in Hvu. 
        unfold reduced in Hvu. rewrite f1 in Hvu. simpl in Hvu. replace 
        (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hvu. 
        subst b1. auto. lia. auto. auto. destruct HM0 as [M0 HMv]. 
        destruct HMv as [HMu HMQ]. rewrite HMQ. cut(Vol M0 <= Vol (Match (b1 :: B0) A0)).
        lia. subst b1. apply H. all:simpl;auto. destruct H3 as [H3 H3a]. destruct H3a as [H3a H3b]. 
        destruct H3b as [H3b H3c].
        split.  simpl.  auto. split. eauto. split. simpl. auto. eauto. apply SortedreducedB with (b:=b).
        all:simpl;auto. apply Sorted_inv in H6. apply H6. 
        move /eqP in price. lia.
      }
    }
    { simpl. destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (MM_exists_opt B0 A0 _ _ _) in Hv. all:auto. destruct Hv as [OPT Hv]. 
        destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
        assert(HM0:exists M0, (Matching M0 B0 A0)/\
        (Vol(OPT) = Vol(M0) + oquantity a)). apply remove_ab_transactions_matching in Hvu. 
        unfold reduced in Hvu. rewrite f1 in Hvu. simpl in Hvu. replace 
        (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in Hvu. 
        auto. lia. auto. auto. destruct HM0 as [M0 HMv]. 
        destruct HMv as [HMu HMQ]. rewrite HMQ. cut(Vol M0 <= Vol (Match B0 A0)).
        lia. apply H0. all:simpl;auto. destruct H3 as [H3 H3a]. destruct H3a as [H3a H3b]. destruct H3b as [H3b H3c].
        split.  eauto. split. eauto. split. eauto. eauto. apply Sorted_inv in H5. apply H5.
        apply Sorted_inv in H6. apply H6.  auto. auto. 
        move /eqP in price. lia.
      }
    }
  }
  { simpl. destruct (Nat.leb (Vol(M)) (min (oquantity b) (oquantity a))) eqn:Hqab.
      { move /leP in Hqab. 
        replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in Hqab. 
        lia. lia. }
      { move /leP in Hqab. assert(Hv:Vol M >= Nat.min (oquantity b) (oquantity a)). lia.
        apply (MM_exists_opt B0 A0 _ _ _) in Hv. all:auto. destruct Hv as [OPT Hv]. 
        destruct Hv as [Hvu HvQ]. destruct HvQ as [HvQ Hv]. rewrite Hv.
        match goal with |[ |- context[_ (Match B0 (?x::A0))]] => set(a1:=x) end.  
        assert(HM0:exists M0, (Matching M0 B0 (a1::A0))/\
        (Vol(OPT) = Vol(M0) + oquantity b)). apply remove_ab_transactions_matching in Hvu. 
        unfold reduced in Hvu. rewrite f1 in Hvu. simpl in Hvu. replace 
        (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in Hvu. 
        subst a1. auto. lia. auto. auto. destruct HM0 as [M0 HMv]. 
        destruct HMv as [HMu HMQ]. rewrite HMQ. cut(Vol M0 <= Vol (Match B0 (a1 :: A0))).
        lia. subst a1. apply H1. all:simpl;auto. destruct H3 as [H3 H3a]. destruct H3a as [H3a H3b]. 
        destruct H3b as [H3b H3c].  split. eauto. split. simpl. auto. split. eauto. simpl. auto.
        apply Sorted_inv in H5. apply H5.
        apply SortedreducedA_rev with (a:=a). all:simpl;auto. move /eqP in price. lia.
      }
    }
  } apply H2. all:auto. eauto. apply Sorted_inv in H6. destruct H3 as [H3 H3a]. destruct H3a as [H3a H3b]. 
    destruct H3b as [H3b H3c]. split.  simpl.  auto. split. eauto. split. simpl. auto. eauto.
    apply Sorted_inv in H6. apply H6. clear H0 H H1 H2. split.
    intro. intros. apply H7 in H. destruct H as [b0 H]. destruct H as [a0 H].
    destruct H. destruct H0.  destruct H1.  destruct H2. destruct H8. 
    simpl in H. destruct H. subst a0. simpl in H0. destruct H0. subst b0.
    unfold tradable in H8. move /eqP in price. lia.  
    unfold tradable in H8. move /eqP in price. 
    apply Sorted_ointroB with (b:=b) in H. move /leP in H. lia. auto.
    exists b0. exists a0. split. auto. split. auto. split. auto. split. auto. 
    split. auto. split. apply H9. split. apply H9. split. apply H9. apply H9.
    split. intros. apply H7. auto. intros. apply H7. auto. Qed.


Lemma MM_optimal B A:
admissible B A -> Is_max (MM B A) B A.
Proof. unfold Is_max. intros. split. apply MM_Is_Matching. auto. unfold MM. 
assert(Vol ((Match (Decr_Bid.sort B) (Decr_Ask.sort A))) = 
Vol (FOA (Match (Decr_Bid.sort B) (Decr_Ask.sort A)) A)).
eapply FOA_correct. split. exact H. 
eapply Maching_permutation_full with (A1:=(Decr_Ask.sort A))(B1:=(Decr_Bid.sort B)).
apply perm_sym. apply Permulation_perm.
apply Decr_Bid.Permuted_sort.
apply perm_sym. apply Permulation_perm.
apply Decr_Ask.Permuted_sort.
 exact. apply Match_Matching. 
apply perm_nodup with (l:=(ids A)). apply ids_perm. apply Permulation_perm.
apply Decr_Ask.Permuted_sort. apply H.
apply perm_nodup with (l:=(ids B)). apply ids_perm. apply Permulation_perm.
apply Decr_Bid.Permuted_sort. apply H.
rewrite <- H1. apply MM_aux_optimal. 
apply admissible_perm with (A1:=A)(B1:=B). 
apply Permulation_perm.
apply Decr_Bid.Permuted_sort.
apply Permulation_perm.
apply Decr_Ask.Permuted_sort.
apply H. apply Decr_Bid.Sorted_sort. apply Decr_Ask.Sorted_sort.
eapply Maching_permutation_full with (A1:=A)(B1:=B). 
apply Permulation_perm.
apply Decr_Bid.Permuted_sort.
apply Permulation_perm.
apply Decr_Ask.Permuted_sort.
exact. auto. Qed.

End MM.
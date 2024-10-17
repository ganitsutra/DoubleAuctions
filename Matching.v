
(* -----------------Description----------------------------------------------------------

This file contains useful definitions and basic properties of fundamental concepts 
about auctions such as matching, maximum matching (MM), individual rational matching (IR), 
uniform matching, fair matching etc. This file also contains results on matchings, 
IR matchings, uniform matchings.


    Terms          <==>     Explanations
    -----------------------------------------------------
    All_matchable M        Every bid-ask pair in M are matchable
    Matching M B A         M is a Matching over (B, A)
    Is_MM M B A            M is maximal matching for B and A
    Uniform M              all bid-ask pairs in M is traded at single price        
    fair_on_bids B M       M is fair on all bids (i.e. B)
    fair_on_asks A M       M is fair on all asks (i.e. A) 
    Is_fair M B A          M is fair on B and A

Most of the results in this file contains the introduction and elimination rules 
for all the above defined notions.

-----------------------------------------------------------------------------*)

Require Export Competitive.
Require Export Sorted.
(*Require Export Quantity.*)

Section Matching.

(*####Definitions: over, valid, Valid, Qty, idas, idbs, Bids, Asks #######*)
Definition tradable (b a: order):= (oprice b >= oprice a).

Definition matchable (B A : list order):= exists b a, (In a A)/\(In b B)/\(tradable b a).

Definition over (t : transaction)(B A : list order):= exists b a, (In a A)/\(In b B)/\(idb t = id b)/\(ida t = id a).

Definition valid (t : transaction)(B A : list order):= exists b a, (In a A)/\(In b B)/\(idb t = id b)/\(ida t = id a)/\(tradable b a)/\(tquantity t <= oquantity b)/\(tquantity t <= oquantity a)/\(oprice b >= tprice t)/\(tprice t >= oprice a).

Definition Tvalid (T : list transaction)(B A : list order):=forall t, (In t T) -> (valid t B A).


(* ####### Definitions: Matching, Canonical form ######### *)

Definition Matching (M: list transaction)(B A: list order):= 
  (Tvalid M B A)/\
  (forall b, In b B -> (Qty_bid M (id b)) <= (oquantity b))/\
  (forall a, In a A-> (Qty_ask M (id a)) <= (oquantity a)).

Definition MaxMatch (M: list transaction) (B A: list order):=
forall M', Matching M' B A -> Matching M B A -> (Vol M') <= (Vol M).

Lemma Matching_over (M: list transaction) (B A: list order): Matching M B A ->
forall t : transaction, In t M -> over t B A.
Proof. unfold Matching. unfold Tvalid. unfold valid. intros. destruct H.
       unfold over. apply H in H0. destruct H0. destruct H0. exists x. 
       exists x0. repeat split. all: apply H0. Qed.

Lemma anot_matchable_tradable (B A: list order)(b :order):~ matchable B A ->
~ (exists a : order, In a A -> tradable b a) -> ~matchable (b::B) A.
Proof. unfold matchable. intros. intro. destruct H1. destruct H1. simpl in H1.
destruct H1. destruct H2. destruct H2. { subst x. destruct H0. exists x0. auto. }
{ destruct H. exists x. exists x0. auto. } Qed. 

Lemma bnot_matchable_tradable (B A: list order)(a :order): ~ matchable B A -> 
~ (exists b : order, In b B -> tradable b a) -> ~matchable B (a::A).
Proof. unfold matchable. intros. intro. destruct H1. destruct H1. simpl in H1.
destruct H1. destruct H2. destruct H1. { subst. destruct H0. exists x. auto. }
{ destruct H. exists x. exists x0. auto. } Qed. 

Lemma not_matchable_delete (B A: list order)(b a :order): ~matchable B A ->
~matchable (delete_order B (id b)) (delete_order A (id a)).
Proof. intros H H0. unfold matchable in H0. destruct H0 as [b0 H0].
       destruct H0 as [a0 H0]. destruct H0 as [H1 H2]. destruct H2 as [H2 H3].
       assert(In  b0 B). eapply delete_order_intro. exact H2. 
       assert(In  a0 A). eapply delete_order_intro. exact H1. destruct H.
       unfold matchable. exists b0. exists a0. auto. Qed.

Lemma not_matchable_matching_nil (M: list transaction) (B A: list order):
~matchable B A -> Matching M B A -> M=nil.
Proof. intros. destruct H0. unfold Tvalid in H0. unfold valid in H0.
       destruct M eqn:HM. auto. assert(In t (t::l)). auto.  apply 
       H0 in H2.  destruct H2. destruct H2. destruct H2. destruct H3.
       destruct H4. destruct H5. destruct H6. unfold matchable in H.
       destruct H. exists x. exists x0. auto. Qed.

Lemma not_matchable_perm_invariance (A A' B B': list order):
not (matchable B A) -> perm B B' -> perm A A' -> not (matchable B' A').
Proof. intros. unfold perm in H0. unfold perm in H1. move /andP in H0.
       move /andP in H1. destruct H0. destruct H1. intro. destruct H.
       unfold matchable. unfold matchable in H4. firstorder. exists x.
       exists x0. repeat split. eauto. eauto. auto. Qed.

Lemma Maching_perm (A1 A2 B1 B2: list order)(M1 M2: list transaction):
perm B1 B2 -> perm A1 A2 -> Matching M1 B1 A1 -> Matching M2 B2 A2 ->
Matching M2 B1 A1.
Proof. unfold perm. unfold Matching. unfold Tvalid. unfold valid. intros.
       move /andP in H. destruct H. move /andP in H0. destruct H0.
       repeat split. { intros. apply H2 in H5. destruct H5 as [b0 H5]. 
       destruct H5 as [a0 H5]. exists b0. exists a0.  destruct H5. 
       destruct H6. split. eauto. split. eauto. auto. } { intros. 
       apply H2. eauto.  } { intro. intro. apply H2. eauto. } Qed.

Lemma Maching_permutation (A1 A2 B1 B2: list order)(M: list transaction):
perm B1 B2 -> perm A1 A2 -> Matching M B1 A1 -> Matching M B2 A2.

Proof. unfold perm. unfold Matching. unfold Tvalid. unfold valid. intros.
       move /andP in H. destruct H. move /andP in H0. destruct H0.
       repeat split. { intros. apply H1 in H4. destruct H4 as [b0 H4]. 
       destruct H4 as [a0 H4]. exists b0. exists a0. destruct H4. 
       destruct H5. split. eauto. split. eauto. auto. } { intros. 
       apply H1. eauto.  } { intro. intro. apply H1. eauto. } Qed.

Lemma Maching_permutation_full (A1 A2 B1 B2: list order)(M1 M2: list transaction):
perm B1 B2 -> perm A1 A2 -> perm M1 M2 -> Matching M1 B1 A1 -> Matching M2 B2 A2.
Proof. unfold perm. unfold Matching. unfold Tvalid. unfold valid. intros.
       move /andP in H. destruct H. move /andP in H0. destruct H0. 
       move /andP in H1. destruct H1.
       repeat split. { intros. assert(In t M1). eauto. apply H2 in H7. 
       destruct H7 as [b0 H7]. destruct H7 as [a0 H7]. exists b0. exists a0.
       destruct H7. destruct H8. split. eauto. split. eauto. auto. } { intros. 
       assert(In b B1). eauto. rewrite <- (perm_Qty_bid M1 M2 (id b)).
       apply H2. auto. unfold perm. apply /andP. auto. }
       { intros. assert(In a A1). eauto. rewrite <- (perm_Qty_ask M1 M2 (id a)).
       apply H2. auto. unfold perm. apply /andP. auto. } Qed.


Lemma Maching_perm_wB (A1 A2 B1 B2: list order)(M1 M2: list transaction)(w:order):
perm B1 B2 -> perm A1 A2 -> Matching M2 (w :: B2) A2 -> Matching M2 (w :: B1) A1.
Proof. unfold perm. unfold Matching. unfold Tvalid. unfold valid. intros.
       move /andP in H. destruct H. move /andP in H0. destruct H0. repeat 
       split. { intros. apply H1 in H4. destruct H4 as [b0 H4]. destruct H4
       as [a0 H4]. exists b0. exists a0.  destruct H4. destruct H5. split.
       eauto. split. destruct H5. simpl. auto. simpl. right. eauto. auto. }
       { intros. apply H1. destruct H4. subst. auto. eauto. } { intro. intro.
       apply H1. eauto. } Qed.
       
Lemma Maching_perm_wA (A1 A2 B1 B2: list order)(M1 M2: list transaction)(w:order):
perm B1 B2 -> perm A1 A2 -> Matching M2 B2 (w::A2) -> Matching M2 B1 (w::A1).
Proof. unfold perm. unfold Matching. unfold Tvalid. unfold valid. intros.
       move /andP in H. destruct H. move /andP in H0. destruct H0. repeat split.
       { intros. apply H1 in H4. destruct H4 as [b0 H4]. destruct H4 as 
       [a0 H4]. exists b0. exists a0.  destruct H4. destruct H5. split. 
       destruct H4. simpl. auto. simpl. right. eauto. split. eauto. auto. }
       { intros. apply H1. eauto. }  { intro. intros. destruct H4. subst. 
       apply H1. auto. apply H1. simpl. right. eauto. } Qed.

Lemma insert_order_transaction_bid (M: list transaction) (B A: list order) (b:order):
~matchable B A -> Matching M (b::B) A -> (forall t, In t M -> idb t = id b).
Proof. intros.  destruct H0. unfold Tvalid in H0. unfold valid in H0. destruct M
       eqn:HM. auto. assert(In t (t::l)). auto.  apply H0 in H1. destruct H1.
       destruct H1. destruct H1. destruct H4. destruct H5. destruct H6. simpl 
       in H4. destruct H4. { subst x. auto. } { unfold matchable in H. destruct H.
       exists x. exists x0. destruct H7. auto. } Qed.

Lemma insert_order_transaction_ask (M: list transaction) (B A: list order) (a:order):
~matchable B A -> Matching M B (a::A) -> (forall t, In t M -> ida t = id a).
Proof. intros.  destruct H0. unfold Tvalid in H0. unfold valid in H0. 
       destruct M eqn:HM. auto. assert(In t (t::l)). auto.  apply H0 in H1. 
       destruct H1. destruct H1. destruct H1. destruct H4. destruct H5. destruct H6.
       simpl in H1. destruct H1. { subst x0. auto. }  { unfold matchable in H.
       destruct H. exists x. exists x0. destruct H7. auto. } Qed.

Lemma insert_order_t_Q_le_bid_aux1 (M: list transaction) (b:order) :
(forall t, In t M-> idb t = id b) -> Qty_bid M (id b) = Vol M.
Proof. induction M. simpl. auto. intros. simpl. destruct(Nat.eqb (idb a)
       (id b)) eqn:Ht. specialize (H a) as H2. simpl in H2. cut(Qty_bid M
       (id b) = Vol M). lia. apply IHM. intros. move /eqP in Ht. 
       specialize (H t) as H3. simpl in H3. destruct H3. auto. auto.
       specialize (H a) as H2. simpl in H2. destruct H2. auto. 
       move /eqP in Ht. destruct Ht. auto. Qed.

Lemma insert_order_t_Q_le_ask_aux1 (M: list transaction) (b:order) :
(forall t, In t M-> ida t = id b) -> Qty_ask M (id b) = Vol M.
Proof. induction M. simpl. auto. intros. simpl. 
       destruct(Nat.eqb (ida a) (id b)) eqn:Ht. specialize (H a) as H2.
       simpl in H2. cut(Qty_ask M (id b) = Vol M). lia. apply IHM. 
       intros. move /eqP in Ht. specialize (H t) as H3. simpl in H3. 
       destruct H3. auto. auto. specialize (H a) as H2. simpl in H2.
       destruct H2. auto. move /eqP in Ht. destruct Ht. auto. Qed.

Lemma insert_order_t_Q_le_bid_aux2 (M: list transaction) (b:order) :
(forall t, In t M -> idb t = id b) -> Qty_bid M (id b) <= oquantity b
-> Vol M <= oquantity b. intros.
Proof. intros. replace (Vol M) with (Qty_bid M (id b)). induction M 
       as [|m0 M]. simpl;auto. simpl. simpl in H0. 
       destruct(Nat.eqb (idb m0) (id b)) eqn:Ht. auto. auto. 
       apply insert_order_t_Q_le_bid_aux1. auto. Qed.

Lemma insert_order_t_Q_le_ask_aux2 (M: list transaction) (b:order) :
(forall t, In t M -> ida t = id b) -> Qty_ask M (id b) <= oquantity b
-> Vol M <= oquantity b. intros.
Proof. intros. replace (Vol M) with (Qty_ask M (id b)). induction M 
       as [|m0 M]. simpl;auto. simpl. simpl in H0. 
       destruct(Nat.eqb (idb m0) (id b)) eqn:Ht. auto. auto.
       apply insert_order_t_Q_le_ask_aux1. auto. Qed.


Lemma insert_order_t_Q_le_bid (M: list transaction) (B A: list order) (b:order):
~matchable B A -> Matching M (b::B) A -> (Vol M) <= (oquantity b).
Proof. intros. assert((forall t, In t M -> idb t = id b)). intros.
       eapply insert_order_transaction_bid. exact H. exact H0. auto.
       destruct H0. unfold Tvalid in H0. unfold valid in H0. destruct H2.
       assert(In b (b::B)).  auto.  specialize (H2 b). 
       apply insert_order_t_Q_le_bid_aux2. apply H1. auto. Qed.

Lemma insert_order_t_Q_le_ask (M: list transaction) (B A: list order) (a:order):
~matchable B A -> Matching M B (a::A) -> (Vol M) <= (oquantity a).
Proof.  intros. assert((forall t, In t M -> ida t = id a)). intros. 
        eapply insert_order_transaction_ask. exact H. exact H0. auto.
        destruct H0. unfold Tvalid in H0. unfold valid in H0. destruct H2.
        assert(In a (a::A)).  auto.  specialize (H2 a). 
        apply  insert_order_t_Q_le_ask_aux2. apply H1. auto. Qed.


Lemma insert_order_Qle_id_of_b_in_Bhat_aux2 (M: list transaction) (B A: list order) (b:order):
NoDup (ids B)-> In b B -> Matching M B A -> Vol M < oquantity b -> 
In (id b) (ids (odiff B (bids M B))).
Proof. intros. apply odiff_intro. replace (quant B (id b)) with 
       (oquantity b). replace (quant (bids M B) (id b)) with (Qty_bid M (id b)).
       assert(Vol M >= Qty_bid M (id b)). apply Q_vs_Qty_bid. lia. symmetry.
       apply bids_id_quant. auto. apply ids_intro. auto. symmetry. 
       apply quant_elim1. auto. Qed.

Lemma insert_order_Qle_id_of_a_in_Ahat_aux2 (M: list transaction) (B A: list order) (a:order):
NoDup (ids A)-> In a A -> Matching M B A -> Vol M < oquantity a -> 
In (id a) (ids (odiff A (asks M A))). 
Proof. intros. apply odiff_intro. replace (quant A (id a)) with 
       (oquantity a). replace (quant (asks M A) (id a)) with (Qty_ask M (id a)).
       assert(Vol M >= Qty_ask M (id a)). apply Q_vs_Qty_ask. lia. symmetry.
       apply asks_id_quant. auto. apply ids_intro. auto.
       symmetry. apply quant_elim1. auto. Qed.

Lemma insert_order_Qle_id_of_b_in_Bhat 
(M: list transaction) (B A: list order) (b:order):
NoDup (ids (b :: B)) -> ~matchable B A -> Matching M (b::B) A -> 
(Vol M) < (oquantity b) -> In (id b) (ids (odiff (b::B) (bids M (b::B)))).
Proof. intros. apply insert_order_Qle_id_of_b_in_Bhat_aux2 with (A:=A). all: auto. Qed.

Lemma insert_order_Qle_id_of_a_in_Ahat (M: list transaction) (B A: list order) (a:order):
NoDup (ids (a :: A)) -> ~matchable B A -> Matching M B (a::A)-> 
(Vol M) < (oquantity a) -> In (id a) (ids (odiff (a::A) (asks M (a::A)))).
Proof. intros. apply insert_order_Qle_id_of_a_in_Ahat_aux2 with (B:=B). all: auto. Qed.

Lemma QM1_gt_QM2_extra_bid_in_M1_aux1 (M1 M2: list transaction):
(Vol M1)>(Vol M2) -> 
(exists i, (In i (ids_bid_aux M1))/\(Qty_bid M1 i) > Qty_bid M2 i).
Proof. intro. assert(subset (fun_ids_bid M1) (fun_ids_bid M2)
        \/~subset (fun_ids_bid M1) (fun_ids_bid M2)). eauto. destruct H0.
       replace (Vol M1) with (Q_by_bids M1) in H. replace (Vol M2) with 
       (Q_by_bids M2) in H. intros.  unfold Q_by_bids in H.
       assert(Q_by_bids_aux M2 (fun_ids_bid M2) >= Q_by_bids_aux M2 (fun_ids_bid M1)).
       apply Q_by_bids_aux_subset_I1_I2. unfold fun_ids_bid. eauto.
       unfold fun_ids_bid. eauto. auto. assert(Q_by_bids_aux M1 (fun_ids_bid M1) >
       Q_by_bids_aux M2 (fun_ids_bid M1)). lia. apply Q_by_bids_aux_T1_T2 in H2.
       destruct H2 as [i H2]. destruct H2. exists i. split.  unfold fun_ids_bid in H2.
       apply uniq_intro_elim. auto. auto. symmetry. apply Q_Qty_bid. 
       symmetry;apply Q_Qty_bid. assert(exists i, In i (fun_ids_bid M1)/\~In i
       (fun_ids_bid M2)). apply no_subset_existsA. auto. destruct H1 as [i H1].
       exists i. destruct H1. split. apply uniq_intro_elim. auto.
       assert(Qty_bid M2 i = 0). apply Qty_bid_t_zero. intro. apply uniq_intro_elim
       in H3. eauto. rewrite H3. apply ids_bid_intro0. apply uniq_intro_elim;auto.
       Qed.

Lemma QM1_gt_QM2_extra_bid_in_M1 (M1 M2: list transaction) (B A: list order):
Matching M1 B A ->Matching M2 B A -> (Vol M1)>(Vol M2) ->
(exists b, (In b B)/\(Qty_bid M1 (id b)) > 
Qty_bid M2 (id b)/\(exists t, In t M1/\(idb t = id b))).
Proof. intros. apply QM1_gt_QM2_extra_bid_in_M1_aux1 in H1.
       destruct H1. destruct H1. apply ids_bid_aux_intro1 in H1 as H3.
       destruct H3. destruct H. unfold Tvalid in H.
       destruct H3. apply H in H3 as H3m. unfold valid in H3m. destruct H3m.
       destruct H6. exists x1. split. apply H6. split. replace (id x1) with (x).
       auto. subst x. apply H6. exists x0. split.  auto. apply H6. Qed.

Lemma QM1_gt_QM2_extra_ask_in_M1_aux1 (M1 M2: list transaction):
(Vol M1)>(Vol M2) -> 
(exists i, (In i (ids_ask_aux M1))/\(Qty_ask M1 i) > Qty_ask M2 i).
Proof. intro. assert(subset (fun_ids_ask M1) (fun_ids_ask M2)
       \/~subset (fun_ids_ask M1) (fun_ids_ask M2)). eauto.
       destruct H0. replace (Vol M1) with (Q_by_asks M1) in H. 
       replace (Vol M2) with (Q_by_asks M2) in H. intros.  unfold Q_by_asks in H.
       assert(Q_by_asks_aux M2 (fun_ids_ask M2) >= Q_by_asks_aux M2 (fun_ids_ask M1)).
       apply Q_by_asks_aux_subset_I1_I2. unfold fun_ids_ask. eauto. unfold
       fun_ids_ask. eauto. auto. assert(Q_by_asks_aux M1 (fun_ids_ask M1) >
       Q_by_asks_aux M2 (fun_ids_ask M1)). lia. apply Q_by_asks_aux_T1_T2 in H2.
       destruct H2 as [i H2]. destruct H2. exists i. split.  unfold fun_ids_ask in H2.
       apply uniq_intro_elim. auto. auto. symmetry;apply Q_Qty_ask. 
       symmetry;apply Q_Qty_ask. assert(exists i, In i (fun_ids_ask M1)/\
       ~In i (fun_ids_ask M2)). apply no_subset_existsA. auto. destruct H1 as [i H1].
       exists i. destruct H1. split. apply uniq_intro_elim. auto.
       assert(Qty_ask M2 i = 0). apply Qty_ask_t_zero. intro. apply uniq_intro_elim
       in H3. eauto. rewrite H3. apply ids_ask_intro0. apply uniq_intro_elim;auto.
       Qed.

Lemma QM1_gt_QM2_extra_ask_in_M1 (M1 M2: list transaction) (B A: list order):
Matching M1 B A ->Matching M2 B A -> (Vol M1)>(Vol M2) ->
(exists a, (In a A)/\(Qty_ask M1 (id a)) > Qty_ask M2 (id a)/\(exists t, In t M1/\(ida t = id a))).
Proof. intros. apply QM1_gt_QM2_extra_ask_in_M1_aux1 in H1.
       destruct H1. destruct H1. apply ids_ask_aux_intro1 in H1 as H3.
       destruct H3. destruct H. unfold Tvalid in H.
       destruct H3. apply H in H3 as H3m. unfold valid in H3m. destruct H3m.
       destruct H6. exists x2. split. apply H6. split. replace (id x2) with (x).
       auto. subst x. apply H6. exists x0. split.  auto. apply H6. Qed.




Lemma QM1_eq_QM2_extra_bid_in_M1 (M1 M2: list transaction)(i:nat):
Vol M1 = Vol M2 -> Qty_bid M1 i > Qty_bid M2 i -> exists i' : nat, Qty_bid M1 i' < Qty_bid M2 i'. 
Proof. replace (Vol M1) with (Q_by_bids M1).
       replace (Vol M2) with (Q_by_bids M2).
       intros.  unfold Q_by_bids in H.  
       assert(Q_by_bids_aux M1 (fun_ids_bid M1) = Q_by_bids_aux M2 (fun_ids_bid M1)\/
       Q_by_bids_aux M1 (fun_ids_bid M1) > Q_by_bids_aux M2 (fun_ids_bid M1)\/
       Q_by_bids_aux M1 (fun_ids_bid M1) < Q_by_bids_aux M2 (fun_ids_bid M1)). lia. 
       destruct H1. assert(In i(fun_ids_bid M1)\/~In i(fun_ids_bid M1)).
       eauto. destruct H2. apply Q_by_bids_aux_T_i_In_I with (T:=M1) in H2 as Ha1.
       rewrite Ha1 in H1. apply Q_by_bids_aux_T_i_In_I with (T:=M2) in H2 as Ha2.
       rewrite Ha2 in H1. assert(Q_by_bids_aux M1 (delete i (fun_ids_bid M1)) <
       Q_by_bids_aux M2 (delete i (fun_ids_bid M1))). lia. 
       apply Q_by_bids_aux_T1_T2 in H3.
       destruct H3. destruct H3. exists x. lia. unfold not in H2.
       assert(Qty_bid M1 i = 0). apply Qty_bid_t_zero. intro.
       apply uniq_intro_elim in H3. eauto. lia.
       destruct H1. 2:{ apply Q_by_bids_aux_T1_T2 in H1. destruct H1.
       destruct H1. exists x. lia. }
       rewrite H in H1.
       assert(Subset (fun_ids_bid M2) (fun_ids_bid M1)
       \/~Subset (fun_ids_bid M2) (fun_ids_bid M1)). eauto.
       destruct H2.  assert(Q_by_bids_aux M2 (fun_ids_bid M1) >= 
       Q_by_bids_aux M2 (fun_ids_bid M2) ). eapply Q_by_bids_aux_subset_I1_I2 in H2. 
       exact H2. unfold fun_ids_bid. eauto. unfold fun_ids_bid. eauto. lia.
       assert(exists i, In i (fun_ids_bid M2)/\~In i (fun_ids_bid M1)).
       apply no_subset_existsA. auto. destruct H3. exists x. destruct H3. 
       assert(Qty_bid M1 x = 0).  apply Qty_bid_t_zero. intro. 
       apply uniq_intro_elim in H3. apply uniq_intro_elim in H5.
       destruct H4. auto. 
       apply uniq_intro_elim in H3. apply ids_bid_intro0 in H3.
       lia. symmetry;apply Q_Qty_bid. symmetry;apply Q_Qty_bid. Qed.

(*Below theorem: Prove for order instead of nat*)
Lemma QM1_eq_QM2_extra_ask_in_M1 (M1 M2: list transaction)(i:nat):
Vol M1 = Vol M2 -> Qty_ask M1 i > Qty_ask M2 i -> exists i' : nat, Qty_ask M1 i' < Qty_ask M2 i'.
Proof. replace (Vol M1) with (Q_by_asks M1).
       replace (Vol M2) with (Q_by_asks M2).
       intros.  unfold Q_by_asks in H.  
       assert(Q_by_asks_aux M1 (fun_ids_ask M1) = Q_by_asks_aux M2 (fun_ids_ask M1)\/
       Q_by_asks_aux M1 (fun_ids_ask M1) > Q_by_asks_aux M2 (fun_ids_ask M1)\/
       Q_by_asks_aux M1 (fun_ids_ask M1) < Q_by_asks_aux M2 (fun_ids_ask M1)). lia. 
       destruct H1. assert(In i(fun_ids_ask M1)\/~In i(fun_ids_ask M1)).
       eauto. destruct H2. apply Q_by_asks_aux_T_i_In_I with (T:=M1) in H2 as Ha1.
       rewrite Ha1 in H1. apply Q_by_asks_aux_T_i_In_I with (T:=M2) in H2 as Ha2.
       rewrite Ha2 in H1. assert(Q_by_asks_aux M1 (delete i (fun_ids_ask M1)) <
       Q_by_asks_aux M2 (delete i (fun_ids_ask M1))). lia. 
       apply Q_by_asks_aux_T1_T2 in H3.
       destruct H3. destruct H3. exists x. lia. unfold not in H2.
       assert(Qty_ask M1 i = 0). apply Qty_ask_t_zero. intro.
       apply uniq_intro_elim in H3. eauto. lia.
       destruct H1. 2:{ apply Q_by_asks_aux_T1_T2 in H1. destruct H1.
       destruct H1. exists x. lia. }
       rewrite H in H1.
       assert(Subset (fun_ids_ask M2) (fun_ids_ask M1)
       \/~Subset (fun_ids_ask M2) (fun_ids_ask M1)). eauto.
       destruct H2.  assert(Q_by_asks_aux M2 (fun_ids_ask M1) >= 
       Q_by_asks_aux M2 (fun_ids_ask M2) ). eapply Q_by_asks_aux_subset_I1_I2 in H2. 
       exact H2. unfold fun_ids_ask. eauto. unfold fun_ids_ask. eauto. lia.
       assert(exists i, In i (fun_ids_ask M2)/\~In i (fun_ids_ask M1)).
       apply no_subset_existsA. auto. destruct H3. exists x. destruct H3. 
       assert(Qty_ask M1 x = 0).  apply Qty_ask_t_zero. intro. 
       apply uniq_intro_elim in H3. apply uniq_intro_elim in H5.
       destruct H4. auto. 
       apply uniq_intro_elim in H3. apply ids_ask_intro0 in H3.
       lia. symmetry;apply Q_Qty_ask. symmetry;apply Q_Qty_ask. Qed.

Lemma Qty_positive_extra_bid_in_B (M: list transaction) (B A: list order)(x:nat):
Matching M B A -> Qty_bid M x > 0 -> exists b, In b B/\(id b) = x.
Proof. unfold Matching. unfold Tvalid. intros. apply Qty_bid_t_zero_converse in H0.
apply ids_bid_aux_intro1 in H0. destruct H0. unfold valid in H. destruct H.
destruct H0. apply H in H0. destruct H0 as [b H0]. destruct H0 as [a H0].
exists b. split. apply H0. subst. symmetry. apply H0. Qed.

Lemma Qty_positive_extra_ask_in_A (M: list transaction) (B A: list order)(x:nat):
Matching M B A -> Qty_ask M x > 0 -> exists a, In a A/\(id a) = x.
Proof. unfold Matching. unfold Tvalid. intros. apply Qty_ask_t_zero_converse in H0.
apply ids_ask_aux_intro1 in H0. destruct H0. unfold valid in H. destruct H.
destruct H0. apply H in H0. destruct H0 as [b H0]. destruct H0 as [a H0].
exists a. split. apply H0. subst. symmetry. apply H0. Qed.

Lemma nill_is_matching (B A: list order) : Matching nil B A.
Proof. { unfold Matching. 
         split. unfold Tvalid. intros t H. inversion H. 
         split. intros b H. simpl. lia. intros a H. simpl. lia.
       } Qed.

Lemma Anil_implies_Mnil (B : list order)(M : list transaction): 
Matching M B nil -> M = nil.
Proof. { unfold Matching. intros H. destruct H as [H H1]. unfold Tvalid in H.
         unfold valid in H. destruct M. auto. specialize (H t). 
         assert (H2: In t (t::M)). auto. apply H in H2. destruct H2 as [b H2]. 
         destruct H2 as [a H2]. destruct H2 as [H3 H2]. inversion H3.
       } Qed.

Lemma Bnil_implies_Mnil (A : list order)(M : list transaction): 
Matching M nil A -> M = nil.
Proof. { unfold Matching. intros H. destruct H as [H H1]. unfold Tvalid in H.
         unfold valid in H. destruct M. auto. specialize (H t). 
         assert (H2: In t (t::M)). auto. apply H in H2. destruct H2 as [b H2]. 
         destruct H2 as [a H2]. destruct H2 as [H3 H2]. destruct H2 as [H4 H2]. inversion H4.
       } Qed.

Lemma Matching_elim (t: transaction)(B A : list order)(M: list transaction): 
Matching M B A ->  Matching (delete t M) B A.
Proof. unfold Matching. unfold Tvalid. unfold valid. 
       intro H. destruct H as [H1 H]. destruct H as [H2 H].
       split. intros t0 H3. assert (H4: In t0 M). eauto. apply H1 in H4.
       exact.  
       split. intros b H3. apply H2 in H3 as H4. 
       cut (Qty_bid (delete t M) (id b) <= Qty_bid M (id b)). 
       lia. apply Qty_bid_delete0.
       intros a H3. apply H in H3 as H4. 
       cut (Qty_ask (delete t M) (id a) <= Qty_ask M (id a)). 
       lia. apply Qty_ask_delete0. Qed.

Lemma ids_bid_subset (M: list transaction) (B A:list order):
Matching M B A -> NoDup (ids B) ->
Subset (fun_ids_bid M) (ids B).
Proof. revert B A. induction M. simpl. 
unfold fun_ids_bid. simpl. auto.
intros. unfold fun_ids_bid. simpl. 
destruct (memb (idb a) (ids_bid_aux M)) eqn:H1.
apply IHM with (A:=A). apply Matching_elim with (t:=a) in H. 
simpl in H. destruct(t_eqb a a) eqn:Ha. 
auto. move /eqP in Ha. destruct Ha. auto.
auto. assert(Hm:=H).
unfold Matching in H. unfold Tvalid in H. 
unfold valid in H. assert (H2: In a (a::M)).
auto. apply H in H2. destruct H2. destruct H2.
destruct H2. destruct H3. destruct H4.
rewrite H4. apply ids_intro in H3.
assert (uniq (ids_bid_aux M) [<=] ids B).
apply IHM with (A:=A). apply Matching_elim with (t:=a) in H. 
simpl in H. destruct(t_eqb a a) eqn:Ha. 
auto. move /eqP in Ha. destruct Ha. auto. auto.
unfold "[<=]".  simpl. intros. 
destruct H7. subst a0. auto.
auto. Qed.

Lemma ids_ask_subset (M: list transaction) (B A:list order):
Matching M B A -> NoDup (ids A) ->
Subset (fun_ids_ask M) (ids A).
Proof. revert B A. induction M. simpl. 
unfold fun_ids_ask. simpl. auto.
intros. unfold fun_ids_ask. simpl. 
destruct (memb (ida a) (ids_ask_aux M)) eqn:H1.
apply IHM with (B:=B). apply Matching_elim with (t:=a) in H. 
simpl in H. destruct(t_eqb a a) eqn:Ha. 
auto. move /eqP in Ha. destruct Ha. auto.
auto. assert(Hm:=H).
unfold Matching in H. unfold Tvalid in H. 
unfold valid in H. assert (H2: In a (a::M)).
auto. apply H in H2. destruct H2. destruct H2.
destruct H2. destruct H3. destruct H4. destruct H5.
rewrite H5. apply ids_intro in H3.
assert (uniq (ids_ask_aux M) [<=] ids A).
apply IHM with (B:=B). apply Matching_elim with (t:=a) in H. 
simpl in H. destruct(t_eqb a a) eqn:Ha. 
auto. move /eqP in Ha. destruct Ha. auto. auto.
unfold "[<=]".  simpl. intros. 
destruct H8. subst a0. apply ids_intro in H2. auto.
auto. Qed.


Lemma Matching_Vol_B_aux M B: NoDup (ids B) ->
(forall b : order, In b B -> Qty_bid M (id b) <= oquantity b) ->
Q_by_bids_aux M (ids B) <= Qty_orders B.
Proof. revert M. induction B as [| b B]. simpl. auto. 
intros. simpl. 
cut(Qty_bid M (id b) <= oquantity b/\Q_by_bids_aux M (ids B) <= Qty_orders B).
lia. split. apply H0. auto. apply IHB. simpl in H. eauto. intros. apply H0.
eauto. Qed.

Lemma Matching_Vol_A_aux M A: NoDup (ids A) ->
(forall a : order, In a A -> Qty_ask M (id a) <= oquantity a) ->
Q_by_asks_aux M (ids A) <= Qty_orders A.
Proof. revert M. induction A as [| a A]. simpl. auto. 
intros. simpl. 
cut(Qty_ask M (id a) <= oquantity a/\Q_by_asks_aux M (ids A) <= Qty_orders A).
lia. split. apply H0. auto. apply IHA. simpl in H. eauto. intros. apply H0.
eauto. Qed.

Lemma Matching_Vol_B M B A: NoDup (ids B) -> Matching M B A -> Vol(M) <= Qty_orders(B).
Proof. rewrite Q_Qty_bid. unfold Q_by_bids. intros. apply ids_bid_subset in H0 as H1. 
       apply Q_by_bids_aux_subset_I1_I2  with (T1:= M) in H1. 
       cut (Q_by_bids_aux M (ids B) <= Qty_orders B). lia. 
       apply Matching_Vol_B_aux. auto. apply H0. unfold fun_ids_bid.
       eauto. auto. auto. Qed.

Lemma Matching_Vol_A M B A: NoDup (ids A) -> Matching M B A -> Vol(M) <= Qty_orders(A).
Proof. rewrite Q_Qty_ask. unfold Q_by_asks. intros. apply ids_ask_subset in H0 as H1. 
       apply Q_by_asks_aux_subset_I1_I2  with (T1:= M) in H1. 
       cut (Q_by_asks_aux M (ids A) <= Qty_orders A). lia. 
       apply Matching_Vol_A_aux. auto. apply H0. unfold fun_ids_ask.
       eauto. auto. auto. Qed.

Lemma delete_transaction_perm (M1 M2: list transaction)(m:transaction):
perm M1 M2 -> perm (delete m M1) (delete m M2).
Proof. intros. apply perm_intro. intros. 
        assert(Hp1:= H). apply perm_elim with (a:=a) in H.
       assert(In a M2\/~In a M2). eauto. destruct H0.
       { assert(In a M1). unfold perm in Hp1. 
         move /andP in Hp1. destruct Hp1. eauto.
         assert(m = a \/ m<> a). eauto.
         destruct H2. subst m. apply countP7 in H1. 
         apply countP7 in H0. lia. rewrite <- countP9. rewrite <- countP9. lia. 
         intro. destruct H2. symmetry. auto. intro. destruct H2. symmetry. auto. 
       }
       { assert(~In a M1). unfold perm in Hp1. 
         move /andP in Hp1. destruct Hp1. intro. 
         assert(In a M2). eauto. destruct (H0 H4). assert(~In a (delete m M1)).
         intro. apply delete_elim1 in H2. destruct (H1 H2). assert(~In a (delete m M2)).
         intro. apply delete_elim1 in H3. destruct (H0 H3). apply countP2 in H2.
         apply countP2 in H3. lia.
       } Qed.

Lemma ids_ask_perm M1 M2 i:
perm M1 M2 -> In i (ids_ask_aux M1) ->In i (ids_ask_aux M2).
Proof. revert M1. induction M2. intros.  apply perm_elim1 in H.
rewrite H in H0. auto. intros. simpl. apply ids_ask_aux_intro1 in H0.
destruct H0. destruct H0. assert(In x (a :: M2)). unfold perm in H. 
         move /andP in H. destruct H.  apply included_elim5 in H. auto. simpl in H2. destruct H2.
subst a. auto. right. rewrite <- H1. apply ids_ask_intro1 in H2. unfold fun_ids_ask in H2. apply uniq_intro_elim. auto. Qed.

Lemma ids_bid_perm M1 M2 i:
perm M1 M2 -> In i (ids_bid_aux M1) ->In i (ids_bid_aux M2).
Proof. revert M1. induction M2. intros.  apply perm_elim1 in H.
rewrite H in H0. auto. intros. simpl. apply ids_bid_aux_intro1 in H0.
destruct H0. destruct H0. assert(In x (a :: M2)). unfold perm in H. 
         move /andP in H. destruct H. apply included_elim5 in H. auto. simpl in H2. destruct H2.
subst a. auto. right. rewrite <- H1. apply ids_bid_intro1 in H2. unfold fun_ids_bid in H2. apply uniq_intro_elim. auto. Qed.


Lemma Vol_perm M1 M2:
perm M1 M2 -> Vol(M1) = Vol(M2).
Proof. revert M2. induction M1. intros. apply perm_sym in H. 
apply perm_elim1 in H. rewrite H. auto. simpl. intros. apply delete_transaction_perm with (m:=a) in H as H2. simpl in H2. replace (t_eqb a a) with true in H2. apply IHM1 in H2.
rewrite H2. rewrite (Vol_delete_m M2 a). unfold perm in H. move /andP in H. destruct H. 
assert(In a (a :: M1)). auto. eauto. lia. auto.
Qed.

End Matching.

Section Uniform.

Definition tprices (M: list transaction):list nat:=
map tprice M.

Fixpoint tprices2 (M: list transaction):list nat:=
match M with
|nil => nil
|m::M => tprice m::tprices2 M
end.

Lemma count_in_deleted_tprices (m: transaction)(M: list transaction):
  In m M -> count (tprice m) (tprices M) = S (count (tprice m) (tprices (delete m M))).
Proof. { induction M.
       { simpl. auto. }
       { intro h1. destruct h1. 
         { subst a. simpl. replace (Nat.eqb (tprice m) (tprice m)) with true.
           replace (t_eqb m m) with true. auto. auto. auto.
         }
         { simpl. destruct (Nat.eqb (tprice m) (tprice a)) eqn: h2.
           { destruct(t_eqb m a) eqn:Ha.
             { auto. } 
             { simpl. rewrite h2.  apply IHM in H. lia. }
           }
           { simpl. destruct(t_eqb m a) eqn:Ha.
              { move /eqP in Ha. subst a. move /eqP in h2. destruct h2. auto. }
              {  simpl. rewrite h2. apply IHM. auto. } 
           }
         }
      } 
      } Qed.

Lemma included_tprices M1 M2: 
included M1 M2 -> included (tprices M1) (tprices M2).
Proof. { revert M2. induction M1 as [| m1].
       { simpl. auto. }
       { intros M2 h1.
         assert (h2: In m1 M2). eauto.
         assert (h3: included M1 (delete m1 M2)). eauto.
         assert (h3a: included (tprices M1) (tprices (delete m1 M2))).
         { auto. }
         assert(h4:count (tprice m1)(tprices M2)= 
         S (count (tprice m1) (tprices (delete m1 M2)))).
         { eauto using count_in_deleted_tprices. }
         eapply included_intro.
         intro x.  simpl. destruct (Nat.eqb x (tprice m1)) eqn: C1.
         { move /eqP in C1. subst x.
           rewrite h4.
           eapply included_elim in h3a  as h3b. instantiate (1 := tprice m1) in h3b.
           lia. }
         { assert (h3b: included M1 M2). eapply included_elim4; apply h1. 
           apply IHM1 in h3b as h3c. auto. } } } Qed.

Lemma tprices_perm  (M1 M2:list transaction):
perm M1 M2 -> perm (tprices M1) (tprices M2).
Proof. unfold perm. intros. move /andP in H. destruct H.
       apply included_tprices in H0. 
       apply included_tprices in H. apply /andP. auto.  Qed.

Definition Uniform (M : list transaction) := uniform (tprices M).

Lemma tps_of_delete (M: list transaction) (m: transaction) (x:nat):
  In x (tprices (delete m M)) -> In x (tprices M).
  Proof. { intro H. apply in_map_iff in H. destruct H.
destruct H. assert (In x0 (M)). eauto. apply in_map_iff. 
exists x0. split. auto. auto. } Qed.
  
Lemma Uniform_intro (M:list transaction) (m:transaction) : Uniform M -> Uniform (delete m M).
Proof. { unfold Uniform. intro H.
         case M as [|m' M'] eqn: HM.
         { simpl. constructor. }
         { simpl in H. simpl. destruct (t_eqb m m') eqn:H1. 
           { apply uniform_elim2 with (a:=(tprice m')). auto. }
           { simpl. cut (forall x, In x (tprices (delete m M')) -> x=(tprice m')).
             eapply uniform_intro. intros x H2.
             assert (H1b: In x (tprices M')).
             { apply tps_of_delete with (m:=m). exact H2. }
               apply uniform_elim4 with (a1:= (tprice m')) in H1b. 
               auto. apply uniform_elim2 in H. auto. 
               apply uniform_elim with (x:=x) in H as H3. rewrite <- H3.
               auto. auto. } } } Qed.

Lemma Uniform_intro1 (M:list transaction) (m:transaction) : Uniform (m::M) -> Uniform M.
Proof. unfold Uniform.  simpl.  eapply uniform_elim2. Qed.

Lemma Uniform_elim (M:list transaction) (m1 m2:transaction) :
  Uniform M -> In m1 M -> In m2 M -> tprice m1 = tprice m2.
Proof. { unfold Uniform. intros H1 H2 H3. 
         cut (In (tprice m2) (tprices M)).
         cut (In (tprice m1) (tprices M)).
         eapply uniform_elim4. exact. all:apply in_map;auto. } Qed.

Lemma Uniform_intro2 (M:list transaction) (m m':transaction) : Uniform M -> 
In m M -> tprice m = tprice m' -> Uniform (m'::M).
Proof. { unfold Uniform. intros H1 H2 H3. simpl. 
         apply in_map with (f:=tprice) in H2 as H4.
         apply uniform_intro. intros x H5. 
         apply uniform_elim4 with (a1:= x) in H4. subst. all:auto. } Qed.


Lemma Uniform_perm (M1 M2:list transaction): 
perm M1 M2 -> Uniform M1 -> Uniform M2.
Proof. unfold Uniform. intros. apply tprices_perm in H. 
eapply uniform_subset. apply perm_elim2 in H.
unfold "[=]" in H. apply H. auto. Qed.

Definition Is_uniform M B A := (Uniform M /\ Matching M B A).

Definition Is_optimal_uniform M B A := Is_uniform M B A -> forall M', Is_uniform M' B A /\ Vol(M) >= Vol(M').

End Uniform.


Section Maximum.
Definition Is_max M B A := forall M', Matching M' B A -> Matching M B A /\ Vol(M') <= Vol(M).

End Maximum.


Section Fair.

Definition Is_fair_bids (M: list transaction)(B:list order):Prop:=
forall b b', (In b B)/\(In b' B)/\(bcompetitive b b'/\~eqcompetitive b b')/\(In (id b') (ids_bid_aux M)) -> 
(Qty_bid M (id b)) = (oquantity b).


Definition Is_fair_asks (M: list transaction)(A:list order):Prop:=
forall a a', (In a A)/\(In a' A)/\(acompetitive a a'/\~eqcompetitive a a')/\(In (id a') (ids_ask_aux M)) -> 
(Qty_ask M (id a)) = (oquantity a).

Definition Is_fair (M: list transaction) (B A: list order) 
  :=  Is_fair_asks M A /\ Is_fair_bids M B.

Lemma Is_fair_asks_perm M1 M2 A1 A2:
perm M1 M2  -> perm A1 A2 -> Is_fair_asks M1 A1 -> Is_fair_asks M2 A2.
Proof. unfold Is_fair_asks. intros. destruct H2. destruct H3. destruct H4.
assert(In a A1). unfold perm in H0. move /andP in H0. destruct H0. 
 eauto. 
assert(In a' A1). unfold perm in H0. move /andP in H0. destruct H0. 
 eauto.  assert(In (id a') (ids_ask_aux M1)). apply ids_ask_perm with (M1:=M2).
auto. auto. 
 rewrite <- (perm_Qty_ask M1 M2 _). 
eapply H1.  split. auto. split. exact H7. all:auto. 
Qed.

Lemma Is_fair_bids_perm M1 M2 B1 B2:
perm M1 M2  -> perm B1 B2 -> Is_fair_bids M1 B1 -> Is_fair_bids M2 B2.
Proof. unfold Is_fair_bids. intros. destruct H2. destruct H3. destruct H4.
assert(In b B1). unfold perm in H0. move /andP in H0. destruct H0. 
 eauto. 
assert(In b' B1). unfold perm in H0. move /andP in H0. destruct H0. 
 eauto.  assert(In (id b') (ids_bid_aux M1)). apply ids_bid_perm with (M1:=M2).
auto. auto. 
 rewrite <- (perm_Qty_bid M1 M2 _). 
eapply H1.  split. auto. split. exact H7. all:auto. 
Qed.


End Fair.


Section  Admissible.

Definition admissible (B A :list order) := 
(NoDup (ids B))/\(NoDup (ids A))/\
(NoDup (timesof B))/\(NoDup (timesof A)).

Lemma admissible_perm B1 A1 B2 A2:
perm B1 B2 -> perm A1 A2 -> admissible B1 A1 -> admissible B2 A2.
Proof. unfold admissible. intros. destruct H1. destruct H2. 
destruct H3. apply ids_perm in H as H5. apply ids_perm in H0 as H6.
apply timesof_perm in H as H7. apply timesof_perm in H0 as H8.
split. eauto. split. eauto. split. eauto. eauto. Qed.

End  Admissible.
(* Extra Lemma : Delete later if unused *)

Lemma tqm_le_bqm (M:list transaction)(B A:list order)(m:transaction)
(ndb:NoDup (ids B)):
Matching M B A -> In m M -> 
tquantity m <= quant B (idb m).
Proof. intros. induction M. elim H0.
simpl. destruct H0. subst a.
destruct H. unfold Tvalid in H. unfold valid in H.
specialize (H m). assert(Hm: In m (m::M)). auto.
apply H in Hm. destruct Hm as [b Hm]. destruct Hm as [a Hm].
destruct Hm as [H2 Hm]. destruct Hm as [H3 Hm].
destruct Hm as [H4 Hm]. destruct Hm as [H5 Hm].
rewrite H4. rewrite (quant_elim1 B b). split. auto. 
auto. apply Hm. 
apply IHM. apply Matching_elim with (t:=a) in H.
simpl in H. destruct (t_eqb a a) eqn:Ha.
auto. move /eqP in Ha.
destruct Ha. auto. auto. Qed.

Lemma tqm_le_sqm (M:list transaction)(B A:list order)(m:transaction)
(nda:NoDup (ids A)):
Matching M B A -> In m M -> 
tquantity m <= quant A (ida m).
Proof. intros. induction M. elim H0.
simpl. destruct H0. subst a.
destruct H. unfold Tvalid in H. unfold valid in H.
specialize (H m). assert(Hm: In m (m::M)). auto.
apply H in Hm. destruct Hm as [b Hm]. destruct Hm as [a Hm].
destruct Hm as [H2 Hm]. destruct Hm as [H3 Hm].
destruct Hm as [H4 Hm]. destruct Hm as [H5 Hm].
rewrite H5. rewrite (quant_elim1 A a). split. auto. 
auto. apply Hm. 
apply IHM. apply Matching_elim with (t:=a) in H.
simpl in H. destruct (t_eqb a a) eqn:Ha.
auto. move /eqP in Ha.
destruct Ha. auto. auto. Qed.

Definition All_matchable M B A :=
forall m, In m M -> tprice m >= price A (ida m) /\ price B (idb m) >= tprice m.

Lemma Matching_All_matchable M B A :
 NoDup (ids B) ->  NoDup (ids A) -> Matching M B A -> All_matchable M B A.
Proof. unfold All_matchable. unfold Matching.
intros ndb nda. intros. induction M as [|m0 M0]. inversion H0. simpl in H0.
destruct H0. subst m0. destruct H. unfold Tvalid in H. assert(valid m B A).
apply H. auto. unfold valid in H1. destruct H1. destruct H1. destruct H1.
destruct H2. destruct H3. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8.
split. rewrite H4. rewrite price_elim1. auto.  lia. rewrite H3. rewrite price_elim1. auto.  lia.
apply IHM0. destruct H. destruct H1. split. unfold Tvalid in H. unfold Tvalid. intros. apply H. simpl.
right. auto. split. intros. apply H1 in H3. simpl in H3. destruct (Nat.eqb (idb m0) (id b) ).
lia. lia. intros. apply H2 in H3. simpl in H3. destruct (Nat.eqb (ida m0) (id a) ).
lia. lia. auto. Qed.


Lemma liaforrun (b a : order): 
oquantity b < oquantity a -> 
~ (oquantity a - oquantity b < 1). lia. Qed.

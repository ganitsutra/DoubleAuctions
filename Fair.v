Require Export Fair_Bid.

Definition FOA M A:= let A:= (Incr_Ask.sort A) in
                     let M:= (Incr_M.sort M) in
                     FOA_aux M A.

Definition FOB M B:= let B:= (Decr_Bid.sort B) in
                     let M:= (Decr_M.sort M) in
                     FOB_aux M B.

Definition Fair M B A := FOA (FOB M B) A.



Theorem FOA_correct M B A:
admissible B A /\ Matching M B A ->
Matching (FOA M A) B A /\                                                       (* (a) *)
Vol(M) = Vol(FOA M A) /\                                                        (* (b) *)
Is_fair_asks (FOA M A) A /\                                                     (* (c) *)
(forall b, In b B -> Qty_bid M (id(b)) = Qty_bid (FOA M A) (id(b)))/\           (* (d) *)
(Is_fair_bids M B -> Is_fair_bids (FOA M A) B).
Proof.  intros. unfold FOA. destruct H. apply Maching_permutation_full with (A1:=A)(B1:=B)(M1:=M)(A2:=(Incr_Ask.sort A))(M2:=(Incr_M.sort M))(B2:=B) in H0.
apply admissible_perm with (A1:=A)(B1:=B)(A2:=(Incr_Ask.sort A))(B2:=B) in H. 
assert(admissible B (Incr_Ask.sort A) /\ Matching (Incr_M.sort M) B (Incr_Ask.sort A)).
auto. apply FOA_aux_correct with (M:=(Incr_M.sort M))(B:=B)(A:=(Incr_Ask.sort A)) in H1.
destruct H1. destruct H2. destruct H3. destruct H4. split. apply Maching_permutation with (A1:=(Incr_Ask.sort A))(A2:=A)(B2:=B) in H1. auto. eauto. apply Permulation_perm.
apply Permutation.Permutation_sym. apply Incr_Ask.Permuted_sort. 
repeat split. replace (Vol M ) with (Vol (Incr_M.sort M)). auto. apply Vol_perm.
apply Permutation_permM.
apply Permutation.Permutation_sym. apply Incr_M.Permuted_sort. 
eapply Is_fair_asks_perm with (A1:=(Incr_Ask.sort A))(A2:=A)(M1:=(FOA_aux (Incr_M.sort M) (Incr_Ask.sort A))). auto. 
apply Permulation_perm.
apply Permutation.Permutation_sym. apply Incr_Ask.Permuted_sort. 
auto. intros. apply H4 in H6. rewrite <- (perm_Qty_bid (Incr_M.sort M) M (id b)).
auto. apply Permutation_permM. apply Permutation.Permutation_sym.
assert(Permutation.Permutation (Incr_M.sort M) M). apply Permutation.Permutation_sym.
apply Incr_M.Permuted_sort. apply Incr_M.Permuted_sort. intro. apply H5. 
apply Is_fair_bids_perm with (M1:=M)(M2:=(Incr_M.sort M))(B1:=B).
apply Permutation_permM.
 apply Incr_M.Permuted_sort. auto. auto. 
apply Incr_Ask.Sorted_sort. apply Incr_M.Sorted_sort. all:auto. 
apply Permulation_perm. apply Incr_Ask.Permuted_sort.
apply Permulation_perm. apply Incr_Ask.Permuted_sort.
apply Permutation_permM. apply Incr_M.Permuted_sort. Qed.


Theorem FOB_correct M B A:
admissible B A /\ Matching M B A ->
Matching (FOB M B) B A /\                                                       (* (a) *)
Vol(M) = Vol(FOB M B) /\                                                        (* (b) *)
Is_fair_bids (FOB M B) B /\                                                     (* (c) *)
(forall a, In a A -> Qty_ask M (id(a)) = Qty_ask (FOB M B) (id(a)))/\           (* (d) *)
(Is_fair_asks M A -> Is_fair_asks (FOB M B) A).
Proof. intros. unfold FOB. destruct H. apply Maching_permutation_full with (A1:=A)(B1:=B)(M1:=M)(B2:=(Decr_Bid.sort B))(M2:=(Decr_M.sort M))(A2:=A) in H0.
apply admissible_perm with (A1:=A)(B1:=B)(B2:=(Decr_Bid.sort B))(A2:=A) in H. 
assert(admissible (Decr_Bid.sort B) A /\ Matching (Decr_M.sort M) (Decr_Bid.sort B) A).
auto. apply FOB_aux_correct with (M:=(Decr_M.sort M))(A:=A)(B:=(Decr_Bid.sort B)) in H1.
destruct H1. destruct H2. destruct H3. destruct H4. split. apply Maching_permutation with (B1:=(Decr_Bid.sort B))(B2:=B)(A2:=A) in H1. auto. apply Permulation_perm.
apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort. auto. 
repeat split. replace (Vol M ) with (Vol (Decr_M.sort M)). auto. apply Vol_perm.
apply Permutation_permM.
apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort. 
eapply Is_fair_bids_perm with (B1:=(Decr_Bid.sort B))(B2:=B)(M1:=(FOB_aux (Decr_M.sort M) (Decr_Bid.sort B))). auto. 
apply Permulation_perm.
apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort. 
auto. intros. apply H4 in H6. rewrite <- (perm_Qty_ask (Decr_M.sort M) M (id a)).
auto. apply Permutation_permM. apply Permutation.Permutation_sym.
assert(Permutation.Permutation (Decr_M.sort M) M). apply Permutation.Permutation_sym.
apply Decr_M.Permuted_sort. apply Decr_M.Permuted_sort. intro. apply H5. 
apply Is_fair_asks_perm with (M1:=M)(M2:=(Decr_M.sort M))(A1:=A).
apply Permutation_permM.
 apply Decr_M.Permuted_sort. auto. auto. 
apply Decr_Bid.Sorted_sort. apply Decr_M.Sorted_sort. all:auto. 
apply Permulation_perm. apply Decr_Bid.Permuted_sort.
apply Permulation_perm. apply Decr_Bid.Permuted_sort.
apply Permutation_permM. apply Decr_M.Permuted_sort. Qed.


Theorem Fair_main (M: list transaction) (B A: list order):
        admissible B A /\ Matching M B A ->
        (Matching (Fair M B A) B A) /\ (* (Fair M B A) is a matching over (B, A) *)
        (Vol(M)= Vol((Fair M B A))) /\ (* Trade volumes of M and (Fair M B A) are the same *)
        (Is_fair (Fair M B A) B A). (* Process Fair produces a fair matching *)
Proof. unfold Fair.  intro. split. 
       apply FOA_correct. split. apply H. apply FOB_correct. auto.
       split. assert(Vol(M) = Vol(FOB M B)). eapply FOB_correct. split. apply H.
       apply H. assert(Vol(FOB M B) = Vol((FOA (FOB M B) A))). eapply FOA_correct.
       split. apply H. apply FOB_correct. auto. lia. unfold Is_fair. split.
       eapply FOA_correct. split. apply H. eapply FOB_correct. auto.
       assert(Is_fair_bids (FOB M B) B). eapply FOB_correct. exact H. 
       eapply FOA_correct. split. apply H. eapply FOB_correct. auto. auto. Qed.



Lemma Fair_Uniform M B A:
Uniform M -> Uniform (Fair M B A).
Proof. unfold Fair. intros. apply FOA_Uniform. 
apply (Uniform_perm (FOB M B)  (Incr_M.sort (FOB M B))).
apply Permutation_permM. apply Incr_M.Permuted_sort. apply FOB_Uniform.
apply (Uniform_perm M  (Decr_M.sort M)).
apply Permutation_permM. apply Decr_M.Permuted_sort. auto. Qed.
Lemma Fair_Is_uniform M B A:
admissible B A /\ Is_uniform M B A ->
Is_uniform (Fair M B A) B A.
Proof. intros. split. apply Fair_Uniform. apply H. apply Fair_main. 
split. apply H. apply H. Qed.

Lemma Is_fair_ab_full M B A b a :
admissible (b::B) (a::A) /\ Matching M (b::B) (a::A) /\
Sorted bcompetitive (b::B) /\
Sorted acompetitive (a::A) /\ 
Vol(M)>=(min (oquantity b) (oquantity a)) -> 
(Qty_ask (Fair M (b :: B) (a :: A)) (id a)) >= (min (oquantity b) (oquantity a))/\
(Qty_bid (Fair M (b :: B) (a :: A)) (id b)) >= (min (oquantity b) (oquantity a)).
Proof. intros. destruct H. destruct H0. destruct H1. destruct H2. 
       assert(admissible (b::B) (a::A) /\ Matching M (b::B) (a::A)). auto.
       apply Fair_main in H4. destruct H4. destruct H5. set(M':= Fair M (b::B) (a::A)). 
       split.
        { subst M'. unfold Fair.  assert(oquantity b > oquantity a \/ oquantity b <= oquantity a). lia. 
          destruct H7. 
          {assert(Nat.min (oquantity b) (oquantity a) = oquantity a). lia. rewrite H8. unfold FOA. 
           cut(Qty_ask (FOA_aux (Incr_M.sort (FOB M (b :: B))) (Incr_Ask.sort (a :: A))) (id a) = oquantity a).
           lia. rewrite (Sorted_perm_acomp_equal (Incr_Ask.sort (a :: A)) (a :: A) _).
          - eapply nodup_included_nodup with (s:=(timesof (a :: A))). apply H. 
            assert(perm (timesof (Incr_Ask.sort (a :: A))) (timesof (a :: A))). apply timesof_perm.
            apply Permulation_perm. apply Permutation.Permutation_sym. apply Incr_Ask.Permuted_sort. 
            unfold perm in H9. move /andP in H9. apply H9. 
          - apply Incr_Ask.Sorted_sort.
          - auto. 
          - apply Permutation.Permutation_sym. apply Incr_Ask.Permuted_sort.
          - rewrite (Qty_ask_FOA_a_rev (Incr_M.sort (FOB M (b :: B))) A a).
            rewrite (Vol_perm (Incr_M.sort (FOB M (b :: B))) (FOB M (b :: B))). apply Permutation_permM.
            apply Permutation.Permutation_sym. apply Incr_M.Permuted_sort. cut(Vol M = Vol (FOB M (b :: B))). lia.
            eapply FOB_correct with (A:=a::A). auto. apply H. auto. 
         } 
         {assert(Nat.min (oquantity b) (oquantity a) = oquantity b). lia. rewrite H8. rewrite H8 in H3.
          assert(Vol M >= oquantity a\/Vol M < oquantity a). lia. destruct H9. unfold FOA. 
          cut(Qty_ask (FOA_aux (Incr_M.sort (FOB M (b :: B))) (Incr_Ask.sort (a :: A))) (id a) = oquantity a).
          lia. rewrite (Sorted_perm_acomp_equal (Incr_Ask.sort (a :: A)) (a :: A) _) .
          eapply nodup_included_nodup with (s:=(timesof (a :: A))). apply H. 
          assert(perm (timesof (Incr_Ask.sort (a :: A))) (timesof (a :: A))). apply timesof_perm.
          apply Permulation_perm. apply Permutation.Permutation_sym. apply Incr_Ask.Permuted_sort. 
          unfold perm in H10. move /andP in H10. apply H10. apply Incr_Ask.Sorted_sort. auto. 
          apply Permutation.Permutation_sym. apply Incr_Ask.Permuted_sort. 
          rewrite (Qty_ask_FOA_a_rev (Incr_M.sort (FOB M (b :: B))) A a). 
          rewrite (Vol_perm (Incr_M.sort (FOB M (b :: B))) (FOB M (b :: B))). apply Permutation_permM.
          apply Permutation.Permutation_sym. apply Incr_M.Permuted_sort. cut(Vol M = Vol (FOB M (b :: B))). lia.
          eapply FOB_correct with (A:=a::A). auto. apply H. auto. unfold FOA.
          rewrite (Sorted_perm_acomp_equal (Incr_Ask.sort (a :: A)) (a :: A) _). 
          - eapply nodup_included_nodup with (s:=(timesof (a :: A))). apply H. 
            assert(perm (timesof (Incr_Ask.sort (a :: A))) (timesof (a :: A))). apply timesof_perm.
            apply Permulation_perm. apply Permutation.Permutation_sym. apply Incr_Ask.Permuted_sort. 
            unfold perm in H10. move /andP in H10. apply H10. 
          - apply Incr_Ask.Sorted_sort.
          - auto. 
          - apply Permutation.Permutation_sym. apply Incr_Ask.Permuted_sort.
          - rewrite Qty_ask_FOA_a_rev_less. rewrite (Vol_perm (Incr_M.sort (FOB M (b :: B))) (FOB M (b :: B))). 
            apply Permutation_permM. apply Permutation.Permutation_sym. apply Incr_M.Permuted_sort.
            unfold FOB. rewrite <- (Vol_FOB _ (Decr_Bid.sort (b :: B))). rewrite (Vol_perm (Decr_M.sort M) M). 
            apply Permutation_permM. apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort.
            lia. rewrite (Qty_orders_perm _ (b::B)). apply Permulation_perm. apply Permutation.Permutation_sym.
            apply Decr_Bid.Permuted_sort. rewrite (Vol_perm (Decr_M.sort M) M). 
            apply Permutation_permM. apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort.
            apply Matching_Vol_B with (A:=(a::A)). apply H. auto. apply H.
            rewrite (Vol_perm (Incr_M.sort (FOB M (b :: B))) (FOB M (b :: B))). 
            apply Permutation_permM. apply Permutation.Permutation_sym. apply Incr_M.Permuted_sort.
            unfold FOB. rewrite <- (Vol_FOB _ (Decr_Bid.sort (b :: B))). rewrite (Vol_perm (Decr_M.sort M) M).
            apply Permutation_permM. apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort. lia. 
            rewrite (Qty_orders_perm _ (b::B)). apply Permulation_perm. apply Permutation.Permutation_sym.
            apply Decr_Bid.Permuted_sort. rewrite (Vol_perm (Decr_M.sort M) M). 
            apply Permutation_permM. apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort.
            apply Matching_Vol_B with (A:=(a::A)). apply H. auto. 
         }
       }

       { subst M'. unfold Fair. unfold FOA. rewrite Qty_bid_FOA. 
         rewrite (Qty_orders_perm (Incr_Ask.sort (a :: A)) ((a :: A))).
          apply Permulation_perm. apply Permutation.Permutation_sym. apply Incr_Ask.Permuted_sort. 
          rewrite (Vol_perm (Incr_M.sort (FOB M (b :: B))) (FOB M (b :: B)) ). apply Permutation_permM.
         apply Permutation.Permutation_sym. apply Incr_M.Permuted_sort. apply Matching_Vol_A with (B:= (b::B)). 
        apply H.
        apply FOB_correct. auto.
        rewrite (perm_Qty_bid (Incr_M.sort (FOB M (b :: B))) (FOB M (b :: B))  (id b)). apply Permutation_permM.
        apply Permutation.Permutation_sym. apply Incr_M.Permuted_sort.  
        assert(oquantity b > oquantity a \/ oquantity b <= oquantity a). lia. destruct H7. 
        assert(Nat.min (oquantity b) (oquantity a) = oquantity a). lia. rewrite H8. rewrite H8 in H3.
        assert(Vol M >= oquantity b\/Vol M < oquantity b). lia.  destruct H9. 
       { unfold FOB. rewrite (Sorted_perm_bcomp_equal (Decr_Bid.sort (b :: B)) (b :: B) _) .
        - eapply nodup_included_nodup with (s:=(timesof (b :: B))). apply H. 
          assert(perm (timesof (Decr_Bid.sort (b :: B))) (timesof (b :: B))). apply timesof_perm.
          apply Permulation_perm. apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort. 
          unfold perm in H10. move /andP in H10. apply H10.
        - apply Decr_Bid.Sorted_sort.
        - auto. 
        - apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort.
        - rewrite (Qty_bid_FOB_b_rev (Decr_M.sort M) B b). rewrite (Vol_perm (Decr_M.sort M) M). 
          apply Permutation_permM. apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort. auto. apply H. lia.
       }
       { unfold FOB. rewrite <- Sorted_sortB. rewrite Qty_bid_FOB_b_rev_less. rewrite (Vol_perm (Decr_M.sort M) M). 
         apply Permutation_permM. apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort.
         lia. apply H. rewrite (Vol_perm (Decr_M.sort M) M). apply Permutation_permM. 
         apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort. auto. apply H. auto.
       } 
        assert(Nat.min (oquantity b) (oquantity a) = oquantity b). lia. rewrite H8. rewrite H8 in H3.
        unfold FOB. rewrite (Sorted_perm_bcomp_equal (Decr_Bid.sort (b :: B)) (b :: B) _) . 
        apply nodup_included_nodup with (s:=(timesof (b :: B))). apply H. 
        assert(perm (timesof (Decr_Bid.sort (b :: B))) (timesof (b :: B))). apply timesof_perm.
        apply Permulation_perm. apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort.
        unfold perm in H9. move /andP in H9. apply H9.
        apply Decr_Bid.Sorted_sort. auto. apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort.
        rewrite (Qty_bid_FOB_b_rev (Decr_M.sort M) B b). rewrite (Vol_perm (Decr_M.sort M) M). 
        apply Permutation_permM. 
        apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort.  auto. apply H. lia. 
      } Qed. 

Lemma Is_FOB_ab_full_bid M B A b a :
admissible (b::B) (a::A) /\ Matching M (b::B) (a::A) /\ Sorted bcompetitive (b::B) /\
Vol(M)>=(oquantity b) -> 
(Qty_bid (FOB M (b :: B)) (id b)) = (oquantity b).
Proof. intros. destruct H. destruct H0.  assert(H3:=H0). destruct H3.  
       assert(admissible (b::B) (a::A) /\ Matching M (b::B) (a::A)). auto. 
       apply FOB_correct in H4. destruct H4. destruct H5. set(M':= FOB M (b::B)). 
       
       { subst M'. destruct H1. 
       unfold FOB. rewrite (Sorted_perm_bcomp_equal (Decr_Bid.sort (b :: B)) (b :: B) _) .
        - eapply nodup_included_nodup with (s:=(timesof (b :: B))). apply H. 
          assert(perm (timesof (Decr_Bid.sort (b :: B))) (timesof (b :: B))). apply timesof_perm.
          apply Permulation_perm. apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort. 
          unfold perm in H8. move /andP in H8. apply H8.
        - apply Decr_Bid.Sorted_sort.
        - auto. 
        - apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort.
        - rewrite (Qty_bid_FOB_b_rev (Decr_M.sort M) B b). rewrite (Vol_perm (Decr_M.sort M) M). 
          apply Permutation_permM. apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort. auto. apply H. lia.
       } Abort.

Lemma Is_FOB_ab_full_bid M B A b a :
admissible (b::B) (a::A) /\ Matching M (b::B) (a::A) /\ Sorted bcompetitive (b::B) /\
Vol(M)>=(min (oquantity b) (oquantity a)) -> 
(Qty_bid (FOB M (b :: B)) (id b)) >= (min (oquantity b) (oquantity a)) .
Proof. intros. destruct H. destruct H0.  assert(H3:=H0). destruct H3.  
       assert(admissible (b::B) (a::A) /\ Matching M (b::B) (a::A)). auto. 
       apply FOB_correct in H4. destruct H4. destruct H5. set(M':= FOB M (b::B)). 
       
       { subst M'. destruct H1. 
       unfold FOB. rewrite (Sorted_perm_bcomp_equal (Decr_Bid.sort (b :: B)) (b :: B) _) .
        - eapply nodup_included_nodup with (s:=(timesof (b :: B))). apply H. 
          assert(perm (timesof (Decr_Bid.sort (b :: B))) (timesof (b :: B))). apply timesof_perm.
          apply Permulation_perm. apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort. 
          unfold perm in H8. move /andP in H8. apply H8.
        - apply Decr_Bid.Sorted_sort.
        - auto. 
        - apply Permutation.Permutation_sym. apply Decr_Bid.Permuted_sort.
        - assert(Vol M >= oquantity b \/ Vol M < oquantity b). lia. destruct H8. 
rewrite (Qty_bid_FOB_b_rev (Decr_M.sort M) B b). rewrite (Vol_perm (Decr_M.sort M) M). 
          apply Permutation_permM. apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort. lia. apply H. lia.
rewrite (Qty_bid_FOB_b_rev_less (Decr_M.sort M) B b). rewrite (Vol_perm _ M).
apply Permutation_permM. apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort. auto. apply H.
rewrite (Vol_perm _ M).
apply Permutation_permM. apply Permutation.Permutation_sym. apply Decr_M.Permuted_sort. auto. 
 } Qed.


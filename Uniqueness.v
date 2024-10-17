Require Export Matching.


Section Uniqueness.


Theorem completeness_asks (M1 M2: list transaction) (B:list order) (A:list order)
(NDA: NoDup (ids A))(NDt: NoDup (timesof A))(a:order):
  (Matching M1 B A)/\ (Matching M2 B A) 
  /\(Vol(M1) = Vol(M2))
  /\(Is_fair_asks M1 A) /\ (Is_fair_asks M2 A) 
    -> (Qty_ask M1 (id a) = Qty_ask M2 (id a)). 
Proof. unfold Is_fair_asks. intros H. destruct H as [H1 H]. destruct H as [H2 H]. 
destruct H as [H3 H]. destruct H as [H4 H]. 
assert(Hta:(Qty_ask M1 (id a) = Qty_ask M2 (id a))\/(Qty_ask M1 (id a) <> Qty_ask M2 (id a))).
eauto. destruct Hta as [H5 | H5]. auto.
assert(Hga:Qty_ask M1 (id a) > Qty_ask M2 (id a)\/Qty_ask M1 (id a) < Qty_ask M2 (id a)).
lia. destruct Hga as [H6 | H6]. 
  (*Case when there exists an ask a such that it's total trade quantities is more in M1 than M2*)
  { assert(H7:exists a, (In (id a) (ids A))/\(Qty_ask M1 (id a) < Qty_ask M2 (id a))).
    { apply QM1_eq_QM2_extra_ask_in_M1 with (i:=(id a)) in H6 as H1a. 
      destruct H1a as [i H1a]. 
      assert(Hq:Qty_ask M1 (id a) >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      assert(Hq:Qty_ask M2 i >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a2 Hq]. destruct Hq as [Ha2 ida2a].
      exists a2. split. apply ids_intro. auto. rewrite ida2a. all:auto.
    } assert(Hq:Qty_ask M1 (id a) >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      destruct H7 as [a2' H7]. destruct H7 as [H7 H10].
      apply ids_elim in H7. destruct H7 as [a2 H7]. destruct H7 as [H7 H11].
      rewrite <- ida1a in H6. rewrite <- H11 in H10.
      assert(H0:a1 = a2 \/ a1<> a2). eauto. destruct H0 as [H0 | H0]. subst a1. lia. 
      assert(Heq:~eqcompetitive a1 a2). 
      { intro Hn. unfold eqcompetitive in Hn.
        move /andP in Hn. destruct Hn as [Hp Ht]. 
        move /eqP in Ht. apply nodup_timesof_uniq_order with (b1:=a1) in H7.
        auto. all:auto. 
      }
      assert(Ha: (acompetitive a1 a2)\/(acompetitive a2 a1)). 
      apply acompetitive_P. destruct Ha as [Ha | Ha]. 
      { assert(Qty_ask M2 (id a1) = oquantity a1). apply H with (a':=a2).
        split. auto. split. auto.
        split. auto. apply Qty_ask_t_zero_converse. 
        lia. assert (Qty_ask M1 (id a1) <= oquantity a1). apply H1. auto.
        lia.
      }
      { assert(H8:Qty_ask M1 (id a2) = oquantity a2). apply H4 with (a':=a1).
        split. auto. split. auto.
        split. split. auto. unfold eqcompetitive. unfold eqcompetitive in Heq.
        intro. destruct Heq. move /andP in H8. destruct H8 as [H8 H9]. 
        move /eqP in H8. move /eqP in H9. apply /andP. split.
        apply /eqP. auto. apply /eqP. auto. apply Qty_ask_t_zero_converse. 
        lia. assert (Qty_ask M2 (id a2) <= oquantity a2). apply H2. auto.
        lia.
      } auto. }
  (*Case when there exists an ask a such that it's total trade quantities is more in M2 than M1*)
  { assert(H7:exists a, (In (id a) (ids A))/\(Qty_ask M2 (id a) < Qty_ask M1 (id a))).
    { apply QM1_eq_QM2_extra_ask_in_M1 with (i:=(id a)) in H6 as H1a. 
      destruct H1a as [i H1a]. 
      assert(Hq:Qty_ask M2 (id a) >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      assert(Hq:Qty_ask M1 i >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a2 Hq]. destruct Hq as [Ha2 ida2a].
      exists a2. split. apply ids_intro. auto. rewrite ida2a. all:auto.
    } assert(Hq:Qty_ask M2 (id a) >0). lia.
      apply Qty_positive_extra_ask_in_A  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      destruct H7 as [a2' H7]. destruct H7 as [H7 H10].
      apply ids_elim in H7. destruct H7 as [a2 H7]. destruct H7 as [H7 H11].
      rewrite <- ida1a in H6. rewrite <- H11 in H10.
      assert(H0:a1 = a2 \/ a1<> a2). eauto. destruct H0 as [H0 | H0]. subst a1. lia. 
      assert(Heq:~eqcompetitive a1 a2). 
      { intro Hn. unfold eqcompetitive in Hn.
        move /andP in Hn. destruct Hn as [Hp Ht]. 
        move /eqP in Ht. apply nodup_timesof_uniq_order with (b1:=a1) in H7.
        auto. all:auto.
      }
      assert(Ha: (acompetitive a1 a2)\/(acompetitive a2 a1)). 
      apply acompetitive_P. destruct Ha as [Ha | Ha]. 
      { assert(Qty_ask M1 (id a1) = oquantity a1). apply H4 with (a':=a2).
        split. auto. split.  auto.
        split. auto. apply Qty_ask_t_zero_converse. lia.
        assert (Qty_ask M2 (id a1) <= oquantity a1). apply H2. auto.
        lia.
      }
      { assert(H8:Qty_ask M2 (id a2) = oquantity a2). apply H with (a':=a1).
        split. auto. split.  auto.
        split. split. auto. unfold eqcompetitive. unfold eqcompetitive in Heq.
        intro. destruct Heq. move /andP in H8. destruct H8 as [H8 H9]. 
        move /eqP in H8. move /eqP in H9. apply /andP. split.
        apply /eqP. auto. apply /eqP. auto. apply Qty_ask_t_zero_converse. 
        lia. assert (Qty_ask M1 (id a2) <= oquantity a2). apply H1. auto.
        lia.
      } auto. }
Qed.

Theorem completeness_bids (M1 M2: list transaction) (B:list order) (A:list order)
(NDB: NoDup (ids B))(NDt: NoDup (timesof B))(b:order):
  (Matching M1 B A)/\ (Matching M2 B A) 
  /\(Vol(M1) = Vol(M2))
  /\(Is_fair_bids M1 B) /\ (Is_fair_bids M2 B)
    -> (Qty_bid M1 (id b) = Qty_bid M2 (id b)). 
Proof. 
 unfold Is_fair_bids. intros H. destruct H as [H1 H]. destruct H as [H2 H]. 
destruct H as [H3 H]. destruct H as [H4 H]. 
assert(Hta:(Qty_bid M1 (id b) = Qty_bid M2 (id b))\/(Qty_bid M1 (id b) <> Qty_bid M2 (id b))).
eauto. destruct Hta as [H5 | H5]. auto.
assert(Hga:Qty_bid M1 (id b) > Qty_bid M2 (id b)\/Qty_bid M1 (id b) < Qty_bid M2 (id b)).
lia. destruct Hga as [H6 | H6]. 
  (*Case when there exists a bid b such that it's total trade quantities is more in M1 than M2*)
  { assert(H7:exists b, (In (id b) (ids B))/\(Qty_bid M1 (id b) < Qty_bid M2 (id b))).
    { apply QM1_eq_QM2_extra_bid_in_M1 with (i:=(id b)) in H6 as H1a. 
      destruct H1a as [i H1a]. 
      assert(Hq:Qty_bid M1 (id b) >0). lia.
      apply Qty_positive_extra_bid_in_B  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      assert(Hq:Qty_bid M2 i >0). lia.
      apply Qty_positive_extra_bid_in_B  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a2 Hq]. destruct Hq as [Ha2 ida2a].
      exists a2. split. apply ids_intro. auto. rewrite ida2a. all:auto.
    } assert(Hq:Qty_bid M1 (id b) >0). lia.
      apply Qty_positive_extra_bid_in_B  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      destruct H7 as [a2' H7]. destruct H7 as [H7 H10].
      apply ids_elim in H7. destruct H7 as [a2 H7]. destruct H7 as [H7 H11].
      rewrite <- ida1a in H6. rewrite <- H11 in H10.
      assert(H0:a1 = a2 \/ a1<> a2). eauto. destruct H0 as [H0 | H0]. subst a1. lia. 
      assert(Heq:~eqcompetitive a1 a2). 
      { intro Hn. unfold eqcompetitive in Hn.
        move /andP in Hn. destruct Hn as [Hp Ht]. 
        move /eqP in Ht. apply nodup_timesof_uniq_order with (b1:=a1) in H7.
        auto. all:auto. 
      }
      assert(Ha: (bcompetitive a1 a2)\/(bcompetitive a2 a1)). 
      apply bcompetitive_P. destruct Ha as [Ha | Ha]. 
      { assert(Qty_bid M2 (id a1) = oquantity a1). apply H with (b':=a2).
        split. auto. split. auto.
        split. auto. apply Qty_bid_t_zero_converse. 
        lia. assert (Qty_bid M1 (id a1) <= oquantity a1). apply H1. auto.
        lia.
      }
      { assert(H8:Qty_bid M1 (id a2) = oquantity a2). apply H4 with (b':=a1).
        split. auto. split. auto.
        split. split. auto. unfold eqcompetitive. unfold eqcompetitive in Heq.
        intro. destruct Heq. move /andP in H8. destruct H8 as [H8 H9]. 
        move /eqP in H8. move /eqP in H9. apply /andP. split.
        apply /eqP. auto. apply /eqP. auto. apply Qty_bid_t_zero_converse. 
        lia. assert (Qty_bid M2 (id a2) <= oquantity a2). apply H2. auto.
        lia.
      } auto. }
  (*Case when there exists a bid b such that it's total trade quantities is more in M2 than M1*)
  { assert(H7:exists b, (In (id b) (ids B))/\(Qty_bid M2 (id b) < Qty_bid M1 (id b))).
    { apply QM1_eq_QM2_extra_bid_in_M1 with (i:=(id b)) in H6 as H1a. 
      destruct H1a as [i H1a]. 
      assert(Hq:Qty_bid M2 (id b) >0). lia.
      apply Qty_positive_extra_bid_in_B  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      assert(Hq:Qty_bid M1 i >0). lia.
      apply Qty_positive_extra_bid_in_B  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a2 Hq]. destruct Hq as [Ha2 ida2a].
      exists a2. split. apply ids_intro. auto. rewrite ida2a. all:auto.
    } assert(Hq:Qty_bid M2 (id b) >0). lia.
      apply Qty_positive_extra_bid_in_B  with (B:=B)(A:=A) in Hq.
      destruct Hq as [a1 Hq]. destruct Hq as [Ha1 ida1a].
      destruct H7 as [a2' H7]. destruct H7 as [H7 H10].
      apply ids_elim in H7. destruct H7 as [a2 H7]. destruct H7 as [H7 H11].
      rewrite <- ida1a in H6. rewrite <- H11 in H10.
      assert(H0:a1 = a2 \/ a1<> a2). eauto. destruct H0 as [H0 | H0]. subst a1. lia. 
      assert(Heq:~eqcompetitive a1 a2). 
      { intro Hn. unfold eqcompetitive in Hn.
        move /andP in Hn. destruct Hn as [Hp Ht]. 
        move /eqP in Ht. apply nodup_timesof_uniq_order with (b1:=a1) in H7.
        auto. all:auto.
      }
      assert(Ha: (bcompetitive a1 a2)\/(bcompetitive a2 a1)). 
      apply bcompetitive_P. destruct Ha as [Ha | Ha]. 
      { assert(Qty_bid M1 (id a1) = oquantity a1). apply H4 with (b':=a2).
        split. auto. split.  auto.
        split. auto. apply Qty_bid_t_zero_converse. lia.
        assert (Qty_bid M2 (id a1) <= oquantity a1). apply H2. auto.
        lia.
      }
      { assert(H8:Qty_bid M2 (id a2) = oquantity a2). apply H with (b':=a1).
        split. auto. split.  auto.
        split. split. auto. unfold eqcompetitive. unfold eqcompetitive in Heq.
        intro. destruct Heq. move /andP in H8. destruct H8 as [H8 H9]. 
        move /eqP in H8. move /eqP in H9. apply /andP. split.
        apply /eqP. auto. apply /eqP. auto. apply Qty_bid_t_zero_converse. 
        lia. assert (Qty_bid M1 (id a2) <= oquantity a2). apply H1. auto.
        lia.
      } auto. }
Qed.



Theorem completeness (M1 M2: list transaction) (B A:list order)
(NDB: NoDup (ids B))(NDA: NoDup (ids A))
(NDtB: NoDup (timesof B))(NDtA: NoDup (timesof A))
(b a:order):
(Matching M1 B A) /\
(Matching M2 B A) /\
(Vol(M1) = Vol(M2)) /\
(Is_fair M1 B A) /\ (Is_fair M2 B A) -> 
(Qty_ask M1 (id a) = Qty_ask M2 (id a))/\
(Qty_bid M1 (id b) = Qty_bid M2 (id b)).
Proof. intros. split.
                { apply completeness_asks with (B:=B)(A:=A). all:auto. 
                  split. apply H. split. apply H. split. apply H. split. apply H. apply H.
                }
                { apply completeness_bids with (B:=B)(A:=A). all:auto. 
                  split. apply H. split. apply H. split. apply H. split. apply H. apply H.
                } Qed.



Lemma soundness_asks (M1 M2: list transaction) (B A:list order)
(NDA: NoDup (ids A)):
(Matching M1 B A)-> (Matching M2 B A) ->
(forall a, (Qty_ask M1 (id a) = Qty_ask M2 (id a)))
->(Is_fair_asks M1 A)  
-> (Is_fair_asks M2 A).
Proof. unfold Is_fair_asks. 
intros. specialize (H1 a') as Hs'.
specialize (H1 a) as Hs.
destruct H3. destruct H4. 
destruct H5. apply ids_ask_intro0 in H6.
rewrite <- Hs' in H6. 
apply Qty_ask_t_zero_converse in H6.
rewrite <- Hs. apply H2 with (a':=a').
auto. Qed.

Lemma soundness_bids (M1 M2: list transaction) (B A:list order)
(NDB: NoDup (ids B)):
(Matching M1 B A)-> (Matching M2 B A) ->
(forall b, (Qty_bid M1 (id b) = Qty_bid M2 (id b)))
->(Is_fair_bids M1 B)  
-> (Is_fair_bids M2 B).
Proof. unfold Is_fair_bids. 
intros. specialize (H1 b') as Hs'.
specialize (H1 b) as Hs.
destruct H3. destruct H4. 
destruct H5. apply ids_bid_intro0 in H6.
rewrite <- Hs' in H6. 
apply Qty_bid_t_zero_converse in H6.
rewrite <- Hs. apply H2 with (b':= b').
auto. Qed.


Theorem soundness (M1 M2: list transaction) (B A:list order)
(NDB: NoDup (ids B))(NDA: NoDup (ids A)):
(Matching M1 B A)-> (Matching M2 B A) ->
(forall b, (Qty_bid M1 (id b) = Qty_bid M2 (id b))) ->
(forall a, (Qty_ask M1 (id a) = Qty_ask M2 (id a)))
->(Is_fair M1 B A)  
-> (Is_fair M2 B A).
Proof. intros. destruct H3. split.
                { apply soundness_asks with (B:=B)(A:=A)(M2:=M2) in H2. all:auto. 
                }
                { apply soundness_bids with (B:=B)(A:=A)(M2:=M2) in H4. all:auto.
                } Qed.

End Uniqueness.
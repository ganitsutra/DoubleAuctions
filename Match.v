Require Import Wellfounded.
Require Import List Setoid Permutation  Orders.
Require Import Coq.Logic.Eqdep_dec Coq.Arith.Compare_dec Coq.Arith.PeanoNat.
From Equations Require Export Equations.
Require Export Matching.
Require Export Coq.Sorting.Mergesort Sorted SortLists.

Section Match.


Equations Match (B A: list order): 
(list transaction) by wf ((length B) + (length A)) :=  
Match nil _ := nil;
Match _ nil := nil;
Match (b::B) (a::A) := (if (Nat.eqb ((oprice a) - (oprice b)) 0) then 
     (match (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b)) with
         |inleft (right _) =>  (Mk_transaction (id b) (id a) (oprice a) (oquantity a) (oquantity_cond a))::(Match B A) 
         |inleft (left _) =>  ((Mk_transaction (id b) (id a) (oprice a) (oquantity a) (oquantity_cond a)):: 
                          (Match ((Mk_order (id b) (otime b) (oquantity b - oquantity a) (oprice b) _ ) :: B) A ))
         |inright _ =>  (Mk_transaction (id b) (id a) (oprice a) (oquantity b) (oquantity_cond b))::
                        (Match B ((Mk_order (id a) (otime a) (oquantity a - oquantity b) (oprice a) _ ) :: A))
      end) else Match (b::B) A).

Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. apply liaforrun;auto. Defined.  
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. apply PeanoNat.Nat.ltb_nlt. apply liaforrun;auto. Defined. 
Next Obligation. lia. Defined.

Lemma Match_Subset_A B A:
Subset (ids_ask_aux (Match B A)) (ids A).
Proof. apply Match_elim. simpl. auto. simpl. auto. simpl. intros.
destruct (oprice a - oprice b =? 0).
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1.
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. apply Subset_intro. auto. }
    { simpl. apply Subset_intro. auto. }
  }
  { specialize (H1 l). simpl. unfold Subset. intros. simpl in H3. unfold Subset in H1.
    destruct H3. subst;auto. apply H1 in H3. auto.
  }
}
{ auto. } Qed.

Lemma Match_Subset_B B A:
Subset (ids_bid_aux (Match B A)) (ids B).
Proof. apply Match_elim. simpl. auto. simpl. auto. simpl. intros.
destruct (oprice a - oprice b =? 0).
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1.
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. unfold Subset. intros. simpl in H3. unfold Subset in H.
      destruct H3. subst;auto. apply H in H3. auto. 
    } 
    { simpl. apply Subset_intro. auto. }
  }
  { simpl. apply Subset_intro. auto.  }
}
{ auto. } Qed.


Lemma Match_Qty_bid_top B A b:
NoDup (ids (b::B)) -> Qty_bid (Match (b :: B) A) (id b) <= oquantity b.
Proof.
revert B b. induction A. { simpl. intros. rewrite Match_equation_2. simpl. lia. }
{ intros. rewrite Match_equation_3. destruct (oprice a - oprice b =? 0).
  { destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
    { destruct s eqn:f2. 
      { simpl. replace (id b =? id b) with true. 
        match goal with |[ |- context[_ (Match (?x::B) A) _ ]] => set(b1:=x) end. specialize (IHA B b1).
        subst b1. simpl. simpl in IHA. apply IHA in H. lia. auto.
      }
      { simpl. replace (id b =? id b) with true. rewrite Qty_bid_t_zero. intro. simpl in H.
        apply NoDup_cons_iff in H. destruct H. destruct H. apply Match_Subset_B in H0. auto. lia. auto. 
      } 
    } 
    { simpl. replace (id b =? id b) with true. rewrite Qty_bid_t_zero. intro. simpl in H.
        apply NoDup_cons_iff in H. destruct H. destruct H. apply Match_Subset_B in H0. auto. lia. auto. 
    } 
  }
  { apply IHA. auto. }
} Qed.


Lemma Match_Qty_ask_top B A a:
NoDup (ids (a::A)) -> Qty_ask (Match B (a :: A)) (id a) <= oquantity a.
Proof.
revert A a. induction B as [| b B]. { simpl. intros. rewrite Match_equation_1. simpl. lia. }
{ intros. rewrite Match_equation_3. destruct (oprice a - oprice b =? 0).
  { destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
    { destruct s eqn:f2. 
      { simpl. replace (id a =? id a) with true. rewrite Qty_ask_t_zero. intro. simpl in H.
        apply NoDup_cons_iff in H. destruct H. destruct H. apply Match_Subset_A in H0. auto. lia. auto. 
      }
      { simpl. replace (id a =? id a) with true. rewrite Qty_ask_t_zero. intro. simpl in H.
        apply NoDup_cons_iff in H. destruct H. destruct H. apply Match_Subset_A in H0. auto. lia. auto. 
      } 
    } 
    { simpl. replace (id a =? id a) with true. 
      match goal with |[ |- context[_ (Match B (?x::A)) _ ]] => set(a1:=x) end. 
      specialize (IHB A a1). subst a1. simpl. simpl in IHB. apply IHB in H. lia. auto.
    } 
  }
  { rewrite Qty_ask_t_zero. intro. simpl in H. apply NoDup_cons_iff in H. destruct H. destruct H. 
    apply Match_Subset_A in H0. auto. lia. }
} Qed.


Lemma Match_Qty_bid B A:
NoDup (ids A) -> NoDup (ids B) -> (forall b : order, In b B -> Qty_bid (Match B A) (id b) <= oquantity b).
Proof. apply Match_elim. simpl. lia. simpl. lia. simpl. intros.
destruct (oprice a - oprice b =? 0).
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. simpl in H. destruct H5. 
      { subst b0. replace (id b =? id b) with true. 
        match goal with |[ |- context[_ (Match (?x::B0) A0) _ ]] => set(b1:=x) end. 
        apply Match_Qty_bid_top with (A:=A0)(b:=b1) in H4 as H5. subst b1. simpl in H5. lia. auto. 
      } 
      { destruct (id b =? id b0) eqn:Hb. move /eqP in Hb. apply ids_intro in H5.
        rewrite <- Hb in H5. apply NoDup_cons_iff in H4. destruct H4. destruct H4. auto. 
        apply H. eauto. all:auto.
      }
    }
    { simpl.  destruct H5. 
      { subst b0. replace (id b =? id b) with true. rewrite Qty_bid_t_zero. intro. apply NoDup_cons_iff in H4.
        destruct H4. destruct H4. apply Match_Subset_B in H5. auto. lia. auto.
      } 
      { destruct (id b =? id b0) eqn:Hb. move /eqP in Hb. apply ids_intro in H5.
        rewrite <- Hb in H5. apply NoDup_cons_iff in H4. destruct H4. destruct H4. auto. 
        apply H0. all:auto. eauto. eauto.
      }
    }
  }
  { simpl.  destruct H5. 
    { subst b0. replace (id b =? id b) with true. rewrite Qty_bid_t_zero. intro. apply NoDup_cons_iff in H4.
        destruct H4. destruct H4. apply Match_Subset_B in H5. auto. lia. auto.
    }
    { destruct (id b =? id b0) eqn:Hb. move /eqP in Hb. apply ids_intro in H5.
      rewrite <- Hb in H5. apply NoDup_cons_iff in H4. destruct H4. destruct H4. auto. 
      apply H1. all:auto. eauto.
    }
  }
} 
{ apply H2. eauto. auto. auto. } Qed.

Lemma Match_Qty_ask B A:
NoDup (ids A) -> NoDup (ids B) -> (forall a : order, In a A -> Qty_ask (Match B A) (id a) <= oquantity a).
Proof. apply Match_elim. simpl. lia. simpl. lia. simpl. intros.
destruct (oprice a - oprice b =? 0).
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. simpl in H. destruct H5. 
      { subst a0. replace (id a =? id a) with true. rewrite Qty_ask_t_zero. intro. apply NoDup_cons_iff in H3.
        destruct H3. destruct H3. apply Match_Subset_A in H5. auto. lia. auto.
      } 
      { destruct (id a =? id a0) eqn:Ha. move /eqP in Ha. apply ids_intro in H5.
        rewrite <- Ha in H5. apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto. 
        apply H. eauto. all:auto.
      }
    }
    { simpl. destruct H5. 
      { subst a0. replace (id a =? id a) with true. rewrite Qty_ask_t_zero. intro. apply NoDup_cons_iff in H3.
        destruct H3. destruct H3. apply Match_Subset_A in H5. auto. lia. auto.
      } 
      { destruct (id a =? id a0) eqn:Ha. move /eqP in Ha. apply ids_intro in H5.
        rewrite <- Ha in H5. apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto. 
        apply H0. all:auto. eauto. eauto.
      }
    }
  }
  { simpl.  destruct H5. 
    { subst a0. replace (id a =? id a) with true. 
      match goal with |[ |- context[_ (Match B0 (?x::A0)) _ ]] => set(a1:=x) end. 
      apply Match_Qty_ask_top with (A:=A0)(a:=a1)(B:=B0) in H3 as H5. 
      subst a1. simpl in H5. lia. auto.
    }
    { destruct (id a =? id a0) eqn:Ha. move /eqP in Ha. apply ids_intro in H5.
      rewrite <- Ha in H5. apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto. 
      apply H1. all:auto. eauto.
    }
  }
} 
{ destruct H5. subst a0. rewrite Qty_ask_t_zero. intro. simpl in H3. 
  apply NoDup_cons_iff in H3. destruct H3. destruct H3. apply Match_Subset_A in H5. auto. lia. 
  apply H2. eauto. auto. auto. } Qed.




Lemma Match_Tvalid B A:
NoDup (ids B) -> NoDup (ids A) -> Tvalid (Match B A) B A.
Proof. apply Match_elim. 
- simpl. unfold Tvalid. intros. inversion H1.
- simpl. unfold Tvalid. intros. inversion H1.
- simpl. unfold Tvalid. unfold valid. intros. 
destruct (oprice a - oprice b =? 0) eqn:price.
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. simpl in H5. destruct H5. 
      { subst t. simpl. exists b. exists a. split. auto. split. auto. split. auto. split. auto.
        unfold tradable. move /eqP in price. lia.
      } 
      { apply H in H5. destruct H5 as [b0 H5]. destruct H5 as [a0 H5]. destruct H5. destruct H6.
        destruct H6. subst b0. unfold tradable in H7. simpl in H7. destruct H7. destruct H7. destruct H8. 
        destruct H9. destruct H10. destruct H11. exists b. exists a0. split. auto. split. auto.
        split. auto. split. auto. split. unfold tradable. lia. split. lia. split. lia. split. lia. lia.
        exists b0. exists a0. split. auto. split. auto. all:auto. eauto.
      }
    }
    { simpl. simpl in H5. destruct H5. 
      { subst t. simpl. exists b. exists a. split. auto. split. auto.
        split. auto. split. auto. move /eqP in price. split. unfold tradable. lia. 
        all:split;lia.
      } 
      { apply H0 in H5. destruct H5 as [b0 H5]. destruct H5 as [a0 H5]. exists b0. exists a0. split. auto.
        right. apply H5. split. right. apply H5. apply H5. all:auto. eauto. eauto.
      }
    }
  }
  { simpl. simpl in H5. destruct H5. 
    { subst t. simpl. exists b. exists a. split. auto. split. auto. split. auto. split. auto.
        unfold tradable. move /eqP in price. lia.
    }
    { apply H1 in H5. destruct H5 as [b0 H5]. destruct H5 as [a0 H5]. destruct H5. simpl in H5. destruct H5.
      destruct H6. subst a0. unfold tradable in H7. simpl in H7. destruct H7. destruct H7. destruct H8. 
        destruct H9. destruct H10. destruct H11. exists b0. exists a. split. auto. split. auto.
        split. auto. split. auto. split. unfold tradable. lia. split. lia. split. lia. split. lia. lia.
        exists b0. exists a0. split. auto. split. right. apply H6. apply H6. all:auto. eauto.
    }
  }
} 
{ apply H2 in H5. destruct H5 as [b0 H5]. destruct H5 as [a0 H5]. exists b0. exists a0. split. auto.
        right. apply H5. apply H5. all:auto. eauto. 
} Qed.


Lemma Match_Matching B A:
NoDup (ids (A)) -> NoDup (ids (B)) -> Matching (Match B A) B A.
Proof. unfold Matching. unfold admissible. 
intros.  split. apply Match_Tvalid. all:auto. split. intros.
 apply Match_Qty_bid. all:auto. intros. apply Match_Qty_ask. all:auto. Qed. 





(* Fair properties of Match *)

Lemma Match_Fair_ask_head B A a a':
NoDup (ids (a::A)) -> NoDup (ids (B)) -> In a' A -> In (id a') (ids_ask_aux (Match B (a :: A))) -> 
Sorted acompetitive (a::A) -> Sorted bcompetitive B -> Qty_ask (Match B (a :: A)) (id a) = oquantity a.
Proof. revert A a a'. induction B as [| b B]. intros A a a' nba ndb H H1. 
rewrite Match_equation_1 in H1. simpl in H1. inversion H1. 
intros A a a' nda ndb H H1. rewrite Match_equation_3 in H1. rewrite Match_equation_3.
destruct (oprice a - oprice b =? 0) eqn:price.
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { simpl. replace (id a =? id a) with true. rewrite Qty_ask_t_zero. intro. simpl in nda. apply NoDup_cons_iff in nda.
      destruct nda. destruct H2. apply Match_Subset_A in H0. auto. lia. auto.
    }
  { simpl. replace (id a =? id a) with true. cut(Qty_ask (Match B A) (id a) = 0).
    lia. apply Qty_ask_t_zero. intro Hin. apply Match_Subset_A in Hin. simpl in nda. apply NoDup_cons_iff in nda.
    destruct nda. destruct H0. auto. auto.
  }
}
{   simpl. replace (id a =? id a) with true.  simpl in H1. destruct H1.
    apply ids_intro in H. simpl in nda. apply NoDup_cons_iff in nda. destruct nda. destruct H1. 
    rewrite H0. auto. intros. apply IHB in H0. simpl in H0. rewrite H0. lia. simpl. all:auto. eauto. 
    apply SortedreducedA with (a:=a). simpl. auto. simpl. auto. auto. apply Sorted_inv in H2. apply H2.
} } intros.
assert(HaS: forall x, In x A -> (Nat.leb (oprice a) (oprice x))). apply Sorted_ointroA. auto.
assert(HbS: forall x, In x B -> (Nat.leb (oprice x) (oprice b))). apply Sorted_ointroB. auto.
 assert(~matchable (b :: B) A). intro. unfold matchable in H3. destruct H3 as [b0 H3].
destruct H3 as [a0 H3]. destruct H3. destruct H4. simpl in H4. destruct H4. apply HaS in H3.
move /leP in H3. unfold tradable in H5. subst b0. move /eqP in price. lia. 
apply HaS in H3. apply HbS in H4. move /leP in H3. move /leP in H4. 
unfold tradable in H5. move /eqP in price. lia.  assert(Matching (Match (b :: B) A) (b::B) A).
apply Match_Matching with (B:=(b::B))(A:=A). auto. eauto. auto. apply not_matchable_matching_nil in H4.
rewrite H4 in H1. simpl in H1. inversion H1. auto. Qed. 

Lemma Match_Fair_ask_head1 B A a a':
NoDup (ids (a::A)) -> NoDup (ids (B)) -> In a' A -> In (id a') (ids_ask_aux (Match B (a :: A))) -> 
Sorted acompetitive (a::A) -> Qty_ask (Match B (a :: A)) (id a) = oquantity a.

Proof. revert A a a'. induction B as [| b B]. intros A a a' nba ndb H H1. 
rewrite Match_equation_1 in H1. simpl in H1. inversion H1. 
intros A a a' nda ndb H H1. rewrite Match_equation_3 in H1. rewrite Match_equation_3.
destruct (oprice a - oprice b =? 0) eqn:price.
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { simpl. replace (id a =? id a) with true. rewrite Qty_ask_t_zero. intro. simpl in nda. apply NoDup_cons_iff in nda.
      destruct nda. destruct H2. apply Match_Subset_A in H0. auto. lia. auto.
    }
  { simpl. replace (id a =? id a) with true. cut(Qty_ask (Match B A) (id a) = 0).
    lia. apply Qty_ask_t_zero. intro Hin. apply Match_Subset_A in Hin. simpl in nda. apply NoDup_cons_iff in nda.
    destruct nda. destruct H0. auto. auto.
  }
}
{   simpl. replace (id a =? id a) with true.  simpl in H1. destruct H1.
    apply ids_intro in H. simpl in nda. apply NoDup_cons_iff in nda. destruct nda. destruct H1. 
    rewrite H0. auto. intros. apply IHB in H0. simpl in H0. rewrite H0. lia. simpl. all:auto. eauto. 
    apply SortedreducedA with (a:=a). simpl. auto. simpl. auto. auto. 
} } intros.
assert(HaS: forall x, In x A -> (Nat.leb (oprice a) (oprice x))). apply Sorted_ointroA. auto.
apply HaS in H as H2.  move /leP in H2. move /eqP in price. Abort.



Lemma Match_Fair_ask B A:
NoDup (ids (B)) -> Sorted bcompetitive B -> NoDup (ids A) -> Sorted acompetitive A -> 
Is_fair_asks (Match B A) A.
Proof. apply Match_elim. 
- firstorder. 
- firstorder.
- simpl. unfold Is_fair_asks. intros b B0 a A0 H H0 H1 H2 ndb SortB. intros.
assert(HbS: forall x, In x A0 -> (acompetitive a x)). apply Sorted_ointroA_tight. auto.
destruct H5 as [H5 H6]. destruct H6 as [H6 H7]. destruct H7 as [H7 H8].
destruct (oprice a - oprice b =? 0) eqn:price.
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. destruct H5;destruct H6.
      { subst. destruct H7 as [H6a H6b]. apply acompetitive_contadiction in H6a. inversion H6a. all:auto. }
      { simpl in H8. destruct H8. 
        - apply ids_intro in H6. rewrite <- H8 in H6. apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto.
        - subst a0. replace (id a =? id a) with true. rewrite Qty_ask_t_zero. intro. apply NoDup_cons_iff in H3.
        destruct H3. destruct H3. apply Match_Subset_A in H5. auto. lia. auto.
      }
      { subst a'. destruct H7 as [H6a H6b]. specialize (HbS a0). apply HbS in H5. 
        apply acompetitive_contadiction in H5. inversion H5. all:auto.  }
      { simpl in H8. destruct H8. 
        - apply ids_intro in H6. rewrite <- H8 in H6. apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto.
        - destruct (id a =? id a0) eqn: Ha. move /eqP in Ha. apply ids_intro in H5. rewrite <- Ha in H5. 
          apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto. apply H with (a':=a'). eauto.
          apply SortedreducedB with (b:=b). simpl. auto. simpl. auto. all:auto. eauto. 
          apply Sorted_inv in H4. apply H4. }
    }
    { simpl. destruct H5;destruct H6.
      { subst. destruct H7 as [H6a H6b]. apply acompetitive_contadiction in H6a. inversion H6a. all:auto. }
      { simpl in H8. destruct H8. 
        - apply ids_intro in H6. rewrite <- H8 in H6. apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto.
        - subst a0. replace (id a =? id a) with true. rewrite Qty_ask_t_zero. intro. apply NoDup_cons_iff in H3.
        destruct H3. destruct H3. apply Match_Subset_A in H5. auto. lia. auto.
      }
      { subst a'. destruct H7 as [H6a H6b]. specialize (HbS a0). apply HbS in H5. 
        apply acompetitive_contadiction in H5. inversion H5. all:auto.  }
      { simpl in H8. destruct H8. 
        - apply ids_intro in H6. rewrite <- H8 in H6. apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto.
        - destruct (id a =? id a0) eqn: Ha. move /eqP in Ha. apply ids_intro in H5. rewrite <- Ha in H5. 
          apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto. apply H0 with (a':=a'). all:auto. eauto.
          apply Sorted_inv in SortB. apply SortB. eauto. apply Sorted_inv in H4. apply H4. }
    }
  }
  { simpl. destruct H5;destruct H6.
     { subst. destruct H7 as [H6a H6b]. apply acompetitive_contadiction in H6a. inversion H6a. all:auto. }
     { simpl in H8. destruct H8. 
       - apply ids_intro in H6. rewrite <- H8 in H6. apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto.
       - subst a0. replace (id a =? id a) with true. rewrite (Match_Fair_ask_head B0 A0 _ a'). all:simpl;auto.
         eauto. apply SortedreducedA with (a:=a). all:simpl;auto. apply Sorted_inv in SortB. apply SortB. lia.
      }
      { subst a'. destruct H7 as [H6a H6b]. specialize (HbS a0). apply HbS in H5. 
        apply acompetitive_contadiction in H5. inversion H5. all:auto.  }
      { simpl in H8. destruct H8. 
        - apply ids_intro in H6. rewrite <- H8 in H6. apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto.
        - destruct (id a =? id a0) eqn: Ha. move /eqP in Ha. apply ids_intro in H5. rewrite <- Ha in H5. 
          apply NoDup_cons_iff in H3. destruct H3. destruct H3. auto. apply H1 with (a':=a'). all:auto. eauto.
          apply Sorted_inv in SortB. apply SortB. apply SortedreducedA with (a:=a). all:simpl;auto. 
      }
  }
} assert(HaS: forall x, In x A0 -> (Nat.leb (oprice a) (oprice x))). apply Sorted_ointroA. auto.
assert(HbS': forall x, In x B0 -> (Nat.leb (oprice x) (oprice b))). apply Sorted_ointroB. auto.
 assert(~matchable (b :: B0) A0). intro. unfold matchable in H9. destruct H9 as [b0 H9].
destruct H9 as [a0' H9]. destruct H9. destruct H10. simpl in H10. destruct H10. apply HaS in H9.
move /leP in H9. unfold tradable in H11. subst b0. move /eqP in price. lia. 
apply HaS in H9. apply HbS' in H10. move /leP in H9. move /leP in H10. 
unfold tradable in H11. move /eqP in price. lia. assert(Matching (Match (b :: B0) A0) (b::B0) A0).
apply Match_Matching with (B:=(b::B0))(A:=A0). auto. eauto. auto. apply not_matchable_matching_nil in H10.
rewrite H10 in H8. simpl in H8. inversion H8. auto. Qed. 


Lemma Match_Fair_bid_head B A b b':
NoDup (ids (b::B)) -> In b' B -> In (id b') (ids_bid_aux (Match (b::B) A)) -> 
Qty_bid (Match (b::B) A) (id b) = oquantity b.
Proof. revert B b b'. induction A as [| a A]. intros B b b' nbb H H1. 
rewrite Match_equation_2 in H1. simpl in H1. inversion H1. 
intros B b b' ndb H H1. rewrite Match_equation_3 in H1. rewrite Match_equation_3.
destruct (oprice a - oprice b =? 0) eqn:price.
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { simpl. replace (id b =? id b) with true. simpl in H1. destruct H1.
    apply ids_intro in H. simpl in ndb. apply NoDup_cons_iff in ndb. destruct ndb. destruct H1. 
    rewrite H0. auto. apply IHA in H0. simpl in H0. rewrite H0. lia. simpl. all:auto.
    }
  { simpl. replace (id b =? id b) with true. cut(Qty_bid (Match B A) (id b) = 0).
    lia. apply Qty_bid_t_zero. intro Hin. apply Match_Subset_B in Hin. simpl in ndb. apply NoDup_cons_iff in ndb.
    destruct ndb. destruct H0. auto. auto.
  }
}
{   simpl. replace (id b =? id b) with true. simpl in H1. rewrite Qty_bid_t_zero. intro. simpl in ndb. 
    apply NoDup_cons_iff in ndb. destruct ndb. destruct H2. apply Match_Subset_B in H0. auto. lia. auto.
} } apply IHA with (b':=b'). all:auto. Qed.




Lemma Match_Fair_bid B A:
NoDup (ids (B)) -> Sorted bcompetitive B -> 
Is_fair_bids (Match B A) B.
Proof. apply Match_elim. 
- firstorder. 
- firstorder.
- simpl. unfold Is_fair_bids. intros b B0 a A0 H H0 H1 H2 ndb SortB. intros.
assert(HbS: forall x, In x B0 -> (bcompetitive b x)). apply Sorted_ointroB_tight. auto.
destruct H3 as [H3 H4]. destruct H4 as [H4 H5]. destruct H5 as [H5 H6].
destruct (oprice a - oprice b =? 0) eqn:price.
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl. destruct H3;destruct H4.
      { subst. destruct H5 as [H6a H6b]. apply bcompetitive_contadiction in H6a. inversion H6a. all:auto. }
      { simpl in H6. destruct H6. 
        - apply ids_intro in H4. rewrite <- H6 in H4. apply NoDup_cons_iff in ndb. destruct ndb. destruct H7. auto.
        - subst b0. replace (id b =? id b) with true. rewrite (Match_Fair_bid_head B0 A0 _ b'). 
          all:auto. simpl. lia.
      }
      { subst b'. destruct H5 as [H6a H6b]. specialize (HbS b0). apply HbS in H3. 
        apply bcompetitive_contadiction in H6b. inversion H6b. all:auto.  }
      { simpl in H6. destruct H6. 
        - apply ids_intro in H4. rewrite <- H6 in H4. apply NoDup_cons_iff in ndb. destruct ndb. destruct H7. auto.
        - destruct (id b =? id b0) eqn: Hb. move /eqP in Hb. apply ids_intro in H3. rewrite <- Hb in H3. 
          apply NoDup_cons_iff in ndb. destruct ndb. destruct H7. auto. apply H with (b':=b'). all: auto.
          apply SortedreducedB with (b:=b). all:simpl;auto. }
    }
    { simpl. destruct H3;destruct H4.
      { subst. destruct H5 as [H6a H6b]. apply bcompetitive_contadiction in H6a. inversion H6a. all:auto. }
      { simpl in H6. destruct H6. 
        - apply ids_intro in H4. rewrite <- H6 in H4. apply NoDup_cons_iff in ndb. destruct ndb. destruct H7. auto.
        - subst b0. replace (id b =? id b) with true. rewrite Qty_bid_t_zero. intro. apply NoDup_cons_iff in ndb. 
          destruct ndb. apply Match_Subset_B in H3. auto. lia. auto.
      }
      { subst b'. destruct H5 as [H6a H6b]. specialize (HbS b0). apply HbS in H3. 
        apply bcompetitive_contadiction in H6b. inversion H6b. all:auto.  }
      { simpl in H6. destruct H6. 
        - apply ids_intro in H4. rewrite <- H6 in H4. apply NoDup_cons_iff in ndb. destruct ndb. destruct H7. auto.
        - destruct (id b =? id b0) eqn: Hb. move /eqP in Hb. apply ids_intro in H3. rewrite <- Hb in H3. 
          apply NoDup_cons_iff in ndb. destruct ndb. destruct H7. auto. apply H0 with (b':=b'). all: auto.
          eauto. apply Sorted_inv in SortB. apply SortB.
      }
    }
  }
  { simpl. destruct H3;destruct H4.
    { subst. destruct H5 as [H6a H6b]. apply bcompetitive_contadiction in H6a. inversion H6a. all:auto. }
    { simpl in H6. destruct H6. 
        - apply ids_intro in H4. rewrite <- H6 in H4. apply NoDup_cons_iff in ndb. destruct ndb. destruct H7. auto.
        - subst b0. replace (id b =? id b) with true. rewrite Qty_bid_t_zero. intro. apply NoDup_cons_iff in ndb. 
          destruct ndb. apply Match_Subset_B in H3. auto. lia. auto.
      }
      { subst b'. destruct H5 as [H6a H6b]. specialize (HbS b0). apply HbS in H3. 
        apply bcompetitive_contadiction in H6b. inversion H6b. all:auto.  }
      { simpl in H6. destruct H6. 
        - apply ids_intro in H4. rewrite <- H6 in H4. apply NoDup_cons_iff in ndb. destruct ndb. destruct H7. auto.
        - destruct (id b =? id b0) eqn: Hb. move /eqP in Hb. apply ids_intro in H3. rewrite <- Hb in H3. 
          apply NoDup_cons_iff in ndb. destruct ndb. destruct H7. auto. apply H1 with (b':=b'). all: auto.
          eauto. apply Sorted_inv in SortB. apply SortB.
      }
    }
  } apply H2 with (b':=b'). all:auto. Qed.


Lemma Match_Fair_on_Bids B A:
admissible B A /\ Sorted bcompetitive B -> Is_fair_bids (Match B A) B.
Proof. intros. apply Match_Fair_bid. all:apply H. Qed.

Lemma Match_Fair_on_Asks B A:
admissible B A /\ Sorted bcompetitive B /\ Sorted acompetitive A -> Is_fair_asks (Match B A) A.
Proof. intros. apply Match_Fair_ask. all:apply H. Qed.

Definition t0:= Mk_transaction 0 0 0 1 not1.


Lemma last_head (M:list transaction)(m:transaction):
last (m::M) t0 = m\/last (m::M) t0 = last M t0.
Proof. revert m. induction M. simpl. auto. intros. right. 
simpl. case M. auto. intros. auto. Qed.


Lemma Match_priceB B A t:
NoDup (ids (B)) -> Sorted bcompetitive B -> NoDup (ids A) -> Sorted acompetitive A -> 
In t (Match B A) -> tprice (last (Match B A) t0) <= price B (idb t).
Proof. revert t. apply Match_elim. 
- firstorder. 
- firstorder.
- simpl. intros b B0 a A0 H H0 H1 H2 t ndb SortB nda SortA. intros.
assert(HbS: forall x, In x B0 -> (Nat.leb (oprice x) (oprice b))). apply Sorted_ointroB. auto.
assert(HaS: forall x, In x A0 -> (Nat.leb (oprice a) (oprice x))). apply Sorted_ointroA. auto.
destruct (oprice a - oprice b =? 0) eqn:price.
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl in H3. destruct H3.
      { subst. match goal with |[ |- context[(tprice (last (?x::?y) t0) <= _ )] ] => set(m0 := x);set(M0:=y) end.
        destruct M0 eqn:HM. simpl. replace (id b =? id b) with true. move /eqP in price. lia. auto.
        replace (tprice (last (m0 :: t :: l0) t0)) with (tprice (last (t :: l0) t0)). assert(In t (t::l0)). auto.
        rewrite <- HM in H3. subst M0. apply H in H3 as H3a. 
        cut((if id b =? idb t then oprice b else Definitions.price B0 (idb t)) <= (if id b =? idb m0 then oprice b 
        else
        Definitions.price B0 (idb m0))). rewrite <- HM. lia. simpl. replace (id b =? id b) with true. 
        apply Match_Tvalid in H3. unfold valid in H3. destruct H3 as [b0 H3]. 
            destruct H3 as [a0 H3]. destruct H3. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8. 
            rewrite H5. rewrite H5 in H3a. simpl in H4. destruct H4. 
            + replace (id b =? id b0) with true. auto. subst b0. simpl. auto. 
            + replace (id b =? id b0) with false. rewrite price_elim1. split. auto. eauto. move /eqP in price. 
              apply HbS in H4 as H5b. move /leP in H5b. auto. symmetry. apply /eqP. intro. apply ids_intro in H4.
              rewrite <- H10 in H4. apply nodup_elim2 in ndb. firstorder. 
            + simpl. auto.
            + eauto.
            + auto.
            + eauto.
            + eapply SortedreducedB. simpl. exact. simpl. auto. auto.
            + eauto.
            + apply Sorted_inv in SortA. apply SortA.
            + simpl. auto.
      }
      { apply H in H3 as Ht. 
        assert(Hlast:=last_head (Match ({|id := id b; otime := otime b;oquantity := oquantity b - oquantity a;
        oprice := oprice b; oquantity_cond := Match_obligations_obligation_1 b a l|} :: B0) A0) ({|idb := id b;
        ida := id a; tprice := oprice a; tquantity := oquantity a; tquantity_cond := oquantity_cond a |})). 
        destruct Hlast. 
          - rewrite H4. simpl. apply Match_Tvalid in H3. unfold valid in H3. destruct H3 as [b0 H3]. 
            destruct H3 as [a0 H3]. destruct H3. destruct H5. destruct H6. destruct H7. destruct H8. 
            rewrite H6. simpl in H5. destruct H5. 
            + subst b0. simpl. replace (id b =? id b) with true. move /eqP in price. lia. auto.
            + move /eqP in price. auto. apply HbS in H5 as H5b. move /leP in H5b. 
              destruct H9. destruct H10. destruct H11. destruct H12.
              apply HaS in H3 as H3a. move /leP in H3a. destruct (id b =? id b0) eqn:Hb. lia. 
              rewrite price_elim1. split. auto. eauto. lia. destruct (id b =? id b0). lia. 
              rewrite price_elim1. split. auto. eauto. apply HaS in H3 as H3a. move /leP in H3a. lia.
            + simpl. eauto.
            + eauto.
          - rewrite H4. auto. 
          - auto.
          - eapply SortedreducedB. simpl. exact. simpl. auto. auto.
          - eauto.
          - apply Sorted_inv in SortA. apply SortA.
       } } 

    { simpl in H3. destruct H3.
      { subst.
        match goal with |[ |- context[(tprice (last (?x::?y) t0) <= _ )] ] => set(m0 := x);set(M0:=y) end.
        destruct M0 eqn:HM. simpl. replace (id b =? id b) with true. move /eqP in price. lia. auto.
        replace (tprice (last (m0 :: t :: l) t0)) with (tprice (last (t :: l) t0)). assert(In t (t::l)). auto.
        rewrite <- HM in H3. subst M0. apply H0 in H3 as H3a. 
        cut((Definitions.price B0 (idb t)) <= (if id b =? idb m0 then oprice b 
        else
        Definitions.price B0 (idb m0))). rewrite <- HM. lia. simpl. replace (id b =? id b) with true. 
        apply Match_Tvalid in H3. unfold valid in H3. destruct H3 as [b0 H3]. 
        destruct H3 as [a0 H3]. destruct H3. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8. 
        rewrite H5. rewrite H5 in H3a. simpl in H4. rewrite price_elim1. split. auto. eauto. move /eqP in price. 
        apply HbS in H4 as H5b. move /leP in H5b. all:auto. eauto. eauto. eauto. apply Sorted_inv in SortB.
        apply SortB. eauto. apply Sorted_inv in SortA. apply SortA.
      }
      { apply H0 in H3 as Ht. apply Match_Tvalid in H3. unfold valid in H3. destruct H3 as [b0 H3]. 
        destruct H3 as [a0 H3]. destruct H3. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8. 
        destruct H9. destruct H10. assert(Hlast:=last_head (Match B0 A0) ({|idb := id b;
        ida := id a; tprice := oprice a; tquantity := oquantity a; tquantity_cond := oquantity_cond a |})). 
        destruct Hlast. 
          - rewrite H12. simpl. rewrite H5. move /eqP in price. auto. apply HbS in H4 as H5b. 
            move /leP in H5b. apply HaS in H3 as H3a. move /leP in H3a. destruct (id b =? id b0) eqn:Hb. lia. 
            rewrite price_elim1. split. auto. eauto. lia.
          - rewrite H12. rewrite H5 in Ht. replace (Definitions.price B0 (id b0)) with (oprice b0) in Ht. 
            apply HbS in H4 as H5b. move /leP in H5b. apply HaS in H3 as H3a. move /leP in H3a. 
            destruct (id b =? idb t). lia. rewrite H5. rewrite price_elim1. split. auto. eauto. lia.
            rewrite price_elim1. split. auto. eauto. lia.
          - eauto.
          - eauto. 
          - auto.
          - auto. 
          - eauto. 
          - apply Sorted_inv in SortB. apply SortB.
          - eauto.
          - apply Sorted_inv in SortA. apply SortA.
       } } } 
     { simpl in H3. destruct H3.
      { subst. 
        match goal with |[ |- context[(tprice (last (?x::?y) t0) <= _ )] ] => set(m0 := x);set(M0:=y) end.
        destruct M0 eqn:HM. simpl. replace (id b =? id b) with true. move /eqP in price. lia. auto.
        replace (tprice (last (m0 :: t :: l0) t0)) with (tprice (last (t :: l0) t0)). assert(In t (t::l0)). auto.
        rewrite <- HM in H3. subst M0. apply H1 in H3 as H3a. subst m0. rewrite <- HM. simpl. 
        replace (id b =? id b) with true.
        apply Match_Tvalid in H3. unfold valid in H3. destruct H3 as [b0 H3]. 
        destruct H3 as [a0 H3]. destruct H3. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8.
        cut((Definitions.price B0 (idb t)) <= oprice b).  lia. rewrite H5. rewrite price_elim1. split. auto.
        eauto. apply HbS in H4. move /leP in H4. lia. eauto. simpl. auto. eauto. eauto. apply Sorted_inv in SortB. 
        apply SortB. eauto. eapply SortedreducedA. simpl. exact. simpl. auto. auto. simpl. auto.
      }
      { apply H1 in H3 as Ht. 
        assert(Hlast:=last_head (Match B0 ({|id := id a;otime := otime a;
        oquantity := oquantity a - oquantity b; oprice := oprice a;oquantity_cond := 
        Match_obligations_obligation_4 b a l|} :: A0)) ({|idb := id b; ida := id a; tprice := oprice a; 
        tquantity := oquantity b; tquantity_cond := oquantity_cond b |})). 
        destruct Hlast. 
          - rewrite H4. simpl. apply Match_Tvalid in H3. unfold valid in H3. destruct H3 as [b0 H3]. 
            destruct H3 as [a0 H3]. destruct H3. destruct H5. destruct H6. destruct H7. destruct H8. 
            rewrite H6. 
            + move /eqP in price. auto. apply HbS in H5 as H5b. move /leP in H5b. 
              destruct H9. destruct H10. destruct H11.  destruct (id b =? id b0) eqn:Hb. lia. 
              rewrite price_elim1. split. auto. eauto. simpl in H3. destruct H3. subst a0. simpl in H12. lia.
              apply HaS in H3 as H3a. move /leP in H3a. lia.
            + simpl. eauto.
            + eauto.
          - rewrite H4. destruct (id b =? idb t). cut(Definitions.price B0 (idb t) <= oprice b). lia. 
            apply Match_Tvalid in H3. unfold valid in H3. destruct H3 as [b0 H3]. 
            destruct H3 as [a0 H3]. destruct H3. destruct H5. destruct H6. destruct H7. destruct H8. 
            rewrite H6.  rewrite price_elim1. split. auto. eauto. apply HbS in H5. move /leP in H5. lia.
            eauto. simpl. auto. auto.
          - eauto.
          - apply Sorted_inv in SortB. apply SortB.
          - eauto.
          - eapply SortedreducedA. simpl. exact. simpl. auto. auto.
          } } } apply H2. all:auto. eauto.  apply Sorted_inv in SortA. apply SortA. Qed.

Lemma Match_priceA B A t:
NoDup (ids (B)) -> Sorted bcompetitive B -> NoDup (ids A) -> Sorted acompetitive A -> 
In t (Match B A) -> price A (ida t) <= tprice (last (Match B A) t0).
Proof. revert t. apply Match_elim. 
- firstorder. 
- firstorder.
- simpl. intros b B0 a A0 H H0 H1 H2 t ndb SortB nda SortA. intros.
assert(HbS: forall x, In x B0 -> (Nat.leb (oprice x) (oprice b))). apply Sorted_ointroB. auto.
assert(HaS: forall x, In x A0 -> (Nat.leb (oprice a) (oprice x))). apply Sorted_ointroA. auto.
destruct (oprice a - oprice b =? 0) eqn:price.
{ destruct (lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:f1. 
  { destruct s eqn:f2.
    { specialize (H s). specialize (H l). simpl in H3. destruct H3.
      { subst. match goal with |[ |- context[(_ <= tprice (last (?x::?y) t0))] ] => set(m0 := x);set(M0:=y) end.
        destruct M0 eqn:HM. simpl. replace (id a =? id a) with true. move /eqP in price. lia. auto.
        replace (tprice (last (m0 :: t :: l0) t0)) with (tprice (last (t :: l0) t0)). assert(In t (t::l0)). auto.
        rewrite <- HM in H3. subst M0. apply H in H3 as H3a. 
        cut((if id a =? ida m0 then oprice a else Definitions.price A0 (ida m0)) <= Definitions.price A0 (ida t)).
        rewrite <- HM. lia. 
        apply Match_Tvalid in H3. unfold valid in H3. destruct H3 as [b0 H3]. 
        destruct H3 as [a0 H3]. destruct H3. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8. 
        rewrite H6. rewrite H6 in H3a. subst m0. simpl. replace (id a =? id a) with true.  rewrite price_elim1.
        split. auto. eauto. move /eqP in price. apply HaS in H3 as H5b. move /leP in H5b. all:auto. eauto. 
        eapply SortedreducedB. simpl. exact. simpl. auto. auto. eauto. apply Sorted_inv in SortA. apply SortA.
      }
      { apply H in H3 as Ht. replace (id a =? ida t) with false.
        match goal with |[ |- context[(_ <= tprice (last (?x::?y) t0))] ] => set(m0 := x);set(M0:=y) end.
        assert((last (m0 :: M0) t0) = (last (M0) t0)). destruct M0 eqn:Hm. subst M0. rewrite Hm in H3. inversion H3. 
        simpl. auto. rewrite H4. subst M0. auto. symmetry. apply /eqP. intro. apply ids_ask_intro1 in H3. 
        unfold fun_ids_ask in H3. apply uniq_intro_elim in H3. assert(In (ida t) (ids A0)). apply Match_Subset_A in H3. auto.
        rewrite <- H4 in H5. apply nodup_elim2 in nda. destruct (nda H5). all:auto.
        eapply SortedreducedB. simpl. exact. simpl. auto. auto. eauto. apply Sorted_inv in SortA. apply SortA.
      } }
    { simpl in H3. destruct H3.
      { subst.
        match goal with |[ |- context[(_ <=  tprice (last (?x::?y) t0))] ] => set(m0 := x);set(M0:=y) end.
        destruct M0 eqn:HM. simpl. replace (id a =? id a) with true. move /eqP in price. lia. auto.
        replace (tprice (last (m0 :: t :: l) t0)) with (tprice (last (t :: l) t0)). assert(In t (t::l)). auto.
        rewrite <- HM in H3. subst M0. apply H0 in H3 as H3a.  
        cut((if id a =? ida m0 then oprice a else Definitions.price A0 (ida m0)) <= Definitions.price A0 (ida t)). 
        rewrite <- HM. lia. simpl. replace (id a =? id a) with true. 
        apply Match_Tvalid in H3. unfold valid in H3. destruct H3 as [b0 H3]. 
        destruct H3 as [a0 H3]. destruct H3. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8. 
        rewrite H6. rewrite H6 in H3a. simpl in H4. rewrite price_elim1. split. auto. eauto. move /eqP in price. 
        apply HaS in H3 as H5b. move /leP in H5b. all:auto. eauto. eauto. eauto. apply Sorted_inv in SortB.
        apply SortB. eauto. apply Sorted_inv in SortA. apply SortA.
      }
      { apply H0 in H3 as Ht. replace (id a =? ida t) with false.
        match goal with |[ |- context[(_ <=  tprice (last (?x::?y) t0))] ] => set(m0 := x);set(M0:=y) end.
        assert((last (m0 :: M0) t0) = (last (M0) t0)). destruct M0 eqn:Hm. subst M0. rewrite Hm in H3. inversion H3. 
        simpl. auto. rewrite H4. subst M0. auto. symmetry. apply /eqP. intro. apply ids_ask_intro1 in H3. 
        unfold fun_ids_ask in H3. apply uniq_intro_elim in H3. assert(In (ida t) (ids A0)). apply Match_Subset_A in H3. auto.
        rewrite <- H4 in H5. apply nodup_elim2 in nda. destruct (nda H5). all:auto. eauto.
        apply Sorted_inv in SortB. apply SortB. eauto. apply Sorted_inv in SortA. apply SortA.
      } } }
    { simpl in H3. destruct H3.
      { subst. match goal with |[ |- context[(_ <= tprice (last (?x::?y) t0))] ] => set(m0 := x);set(M0:=y) end.
        destruct M0 eqn:HM. simpl. replace (id a =? id a) with true. move /eqP in price. lia. auto.
        replace (tprice (last (m0 :: t :: l0) t0)) with (tprice (last (t :: l0) t0)). assert(In t (t::l0)). auto.
        rewrite <- HM in H3. subst M0. apply H1 in H3 as H3a. 
        cut((if id a =? ida m0 then oprice a else Definitions.price A0 (ida m0)) <= 
        ((if id a =? ida t then oprice a else Definitions.price A0 (ida t)))). rewrite <- HM. lia. 
        simpl. replace (id a =? id a) with true. 
        apply Match_Tvalid in H3. unfold valid in H3. destruct H3 as [b0 H3]. 
        destruct H3 as [a0 H3]. destruct H3. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8. 
        rewrite H6. rewrite H6 in H3a. simpl in H3. destruct H3. 
            + replace (id a =? id a0) with true. auto. subst a0. simpl. auto. 
            + replace (id a =? id a0) with false. rewrite price_elim1. split. auto. eauto. move /eqP in price. 
              apply HaS in H3 as H5b. move /leP in H5b. auto. symmetry. apply /eqP. intro. apply ids_intro in H3.
              rewrite <- H10 in H3. apply nodup_elim2 in nda. firstorder. 
            + eauto.
            + simpl. auto.
            + auto.
            + eauto.
            + apply Sorted_inv in SortB. apply SortB.
            + auto.
            + eapply SortedreducedA. simpl. exact. simpl. auto. auto.
            + simpl. auto.
      }
      { apply H1 in H3 as Ht. 
        match goal with |[ |- context[(_ <= tprice (last (?x::?y) t0))] ] => set(m0 := x);set(M0:=y) end.
        replace (tprice (last (m0 :: M0) t0)) with (tprice (last (M0) t0)). subst M0. auto. destruct M0 eqn:HM. 
        subst M0. rewrite HM in H3. inversion H3. simpl.  auto. eauto. apply Sorted_inv in SortB. apply SortB.
        auto. eapply SortedreducedA. simpl. exact. simpl. auto. auto. } } } apply H2 in H3 as H3a. all:auto. 
        replace (id a =? ida t) with false. auto. symmetry. apply /eqP. intro. apply ids_ask_intro1 in H3. 
        unfold fun_ids_ask in H3. apply uniq_intro_elim in H3. assert(In (ida t) (ids A0)). apply Match_Subset_A in H3. auto.
        rewrite <- H4 in H5. apply nodup_elim2 in nda. destruct (nda H5). all:auto.
        eauto.  apply Sorted_inv in SortA. apply SortA. Qed.


End Match.
Require Export Matching.


Section Bound.

Definition demand (p: nat)(B: list order): list order :=
  filter (fun x:order => Nat.leb p (oprice x)) B.

Definition supply (p: nat)(A: list order): list order :=
  filter (fun x:order => Nat.leb (oprice x) p) A.

Definition demand_above_p (p: nat)(B: list order): list order :=
  filter (fun x:order => Nat.ltb p (oprice x)) B.

Definition demand_above_at_p (p: nat)(B: list order): list order :=
  filter (fun x:order => Nat.leb p (oprice x)) B.

Definition supply_below_p (p: nat)(A: list order): list order :=
  filter (fun x:order => Nat.ltb (oprice x) p) A.

Definition supply_below_at_p (p: nat)(A: list order): list order :=
  filter (fun x:order => Nat.leb (oprice x) p) A.

Definition demand_at_p (p: nat)(B: list order): list order :=
  filter (fun x:order => Nat.eqb p (oprice x)) B.

Definition supply_at_p (p: nat)(A: list order): list order :=
  filter (fun x:order => Nat.eqb (oprice x) p) A.

Definition M_above_p (p: nat)(B: list order) (M: list transaction): list transaction :=
  filter (fun x:transaction => Nat.ltb p (price B (idb x))) M. (*M1*)

Definition M_below_p (p: nat)(B: list order) (M: list transaction): list transaction :=
  filter (fun x:transaction => Nat.ltb (price B (idb x)) p) M. (*M1'*)

Definition M_above_at_p (p: nat)(B: list order) (M: list transaction): list transaction :=
  filter (fun x:transaction => Nat.leb p (price B (idb x))) M. (*M2*)

Definition M_below_at_p (p: nat)(B: list order) (M: list transaction): list transaction :=
  filter (fun x:transaction => Nat.leb (price B (idb x)) p) M. (*M2'*)


Lemma Qty_orders_supply p A:
Qty_orders (supply_below_at_p p A) = Qty_orders (supply_below_p p A) + (Qty_orders (supply_at_p p A)).
Proof. induction A. simpl. auto. simpl. 
destruct (Nat.leb (oprice a) p) eqn:H1;
destruct (Nat.ltb (oprice a) p) eqn:H2;
destruct (Nat.eqb (oprice a) p) eqn:H3.
all: simpl;move /eqP in H3; move /ltP in H2;move /leP in H1;lia. Qed.

Lemma Qty_orders_demand p B: 
Qty_orders (demand_above_at_p p B) = 
Qty_orders (demand_above_p p B) + Qty_orders (demand_at_p p B).
Proof. induction B. simpl. auto. simpl. 
destruct (Nat.leb p (oprice a)) eqn:H1;
destruct (Nat.ltb p (oprice a)) eqn:H2;
destruct (Nat.eqb p (oprice a)) eqn:H3.
all: simpl;move /eqP in H3; move /ltP in H2;move /leP in H1;lia. Qed.


Lemma filter_not_In B p b:
~In b B -> ~In b (demand_above_p p B).
Proof. induction B. simpl.  auto. simpl.  intros. 
intro. destruct (Nat.ltb p (oprice a)) eqn: Ha. 
simpl in H0. destruct H0. destruct H. auto. destruct H. right.
eauto. destruct H. right. eauto. Qed.

Lemma filter_nodup B f:
NoDup (ids B) -> NoDup (ids (filter f B)).
Proof. induction B. simpl. auto. simpl. destruct (f a).
simpl. intros. constructor. apply nodup_elim2 in H. intro. destruct H.
apply ids_elim in H0. destruct H0. destruct H. rewrite <- H0.
apply filter_In in H. destruct H. apply ids_intro. auto.
apply IHB. eauto. intros. apply IHB. eauto. Qed.



Lemma M_above_p_Matching M B A p:
NoDup (ids B) -> Matching M B A -> Matching (M_above_p p B M) (demand_above_p p B) A.
Proof. unfold Matching. unfold Tvalid. unfold valid. intro ndb. intros. destruct H.
destruct H0. split. 
intros. apply filter_In in H2.
destruct H2. apply H in H2. destruct H2 as [b H2]. destruct H2 as [a H2].
destruct H2. destruct H4. destruct H5. destruct H6. destruct H7.
destruct H8. destruct H9. destruct H10.
exists b. exists a. split. auto. split.
move /ltP in H3. apply filter_intro. auto. apply /ltP.
rewrite H5 in H3. rewrite <- price_elim1 with (B:=B).
auto. split. auto. auto. split;auto.  split;auto.
split. { intros. apply filter_In in H2. destruct H2.
apply H0 in H2. cut (Qty_bid (M_above_p p B M) (id b) <= Qty_bid M (id b)).
lia. apply Qty_bid_filter. }
{ intros. 
apply H1 in H2. cut (Qty_ask (M_above_p p B M) (id a) <= Qty_ask M (id a)).
lia. apply Qty_ask_filter. } Qed.

Lemma M_below_at_p_Matching M B A p:
NoDup (ids B) -> Matching M B A -> Matching (M_below_at_p p B M) B (supply_below_at_p p A).
Proof. unfold Matching. unfold Tvalid. unfold valid. intro ndb. intros. destruct H.
destruct H0. split. 
intros. apply filter_In in H2.
destruct H2. apply H in H2. destruct H2 as [b H2]. destruct H2 as [a H2].
destruct H2. destruct H4. destruct H5. destruct H6. destruct H7.
destruct H8. destruct H9. destruct H10.
exists b. exists a. split. apply filter_In. split.
auto. apply /leP. move /leP in H3. rewrite H5 in H3.
rewrite price_elim1 in H3. auto. lia. split;auto. split;auto. 
split;auto. split. { intros. 
apply H0 in H2. 
cut (Qty_bid (M_below_at_p p B M) (id b) <= Qty_bid M (id b)).
lia. apply Qty_bid_filter. }
{ intros. apply filter_In in H2. destruct H2.
apply H1 in H2. cut (Qty_ask (M_below_at_p p B M) (id a) <= Qty_ask M (id a)).
lia. apply Qty_ask_filter. }
 Qed.

Lemma M_above_at_p_Matching M B A p:
NoDup (ids B) -> Matching M B A -> Matching (M_above_at_p p B M) (demand_above_at_p p B) A.
Proof. unfold Matching. unfold Tvalid. unfold valid. intro ndb. intros. destruct H.
destruct H0. split. 
intros. apply filter_In in H2.
destruct H2. apply H in H2. destruct H2 as [b H2]. destruct H2 as [a H2].
destruct H2. destruct H4. destruct H5. destruct H6. destruct H7.
destruct H8. destruct H9. destruct H10.
exists b. exists a. split. auto. split.
move /leP in H3. apply filter_intro. auto. apply /leP.
rewrite H5 in H3. rewrite <- price_elim1 with (B:=B).
auto. split. auto. auto. split;auto.  split;auto.
split. { intros. apply filter_In in H2. destruct H2.
apply H0 in H2. cut (Qty_bid (M_above_at_p p B M) (id b) <= Qty_bid M (id b)).
lia. apply Qty_bid_filter. }
{ intros. 
apply H1 in H2. cut (Qty_ask (M_above_at_p p B M) (id a) <= Qty_ask M (id a)).
lia. apply Qty_ask_filter. } Qed.

Lemma M_below_p_Matching M B A p:
NoDup (ids B) -> Matching M B A -> Matching (M_below_p p B M) B (supply_below_p p A).
Proof. unfold Matching. unfold Tvalid. unfold valid. intro ndb. intros. destruct H.
destruct H0. split. 
intros. apply filter_In in H2.
destruct H2. apply H in H2. destruct H2 as [b H2]. destruct H2 as [a H2].
destruct H2. destruct H4. destruct H5. destruct H6. destruct H7.
destruct H8. destruct H9. destruct H10.
exists b. exists a. split. apply filter_In. split.
auto. apply /leP. move /leP in H3. rewrite H5 in H3.
rewrite price_elim1 in H3. auto. lia. split;auto. split;auto. 
split;auto. split. { intros. 
apply H0 in H2. 
cut (Qty_bid (M_below_p p B M) (id b) <= Qty_bid M (id b)).
lia. apply Qty_bid_filter. }
{ intros. apply filter_In in H2. destruct H2.
apply H1 in H2. cut (Qty_ask (M_below_p p B M) (id a) <= Qty_ask M (id a)).
lia. apply Qty_ask_filter. }
 Qed.


Lemma M_sum1 (p:nat)(M: list transaction)(B A:list order):
Vol(M) = Vol(M_above_p p B M) + Vol((M_below_at_p p B M)).
Proof. induction M. simpl. auto. simpl. 
destruct (Nat.ltb p (price B (idb a))) eqn:H1; destruct (Nat.leb (price B (idb a)) p) eqn:H2.
{ move /ltP in H1. move /leP in H2. lia. }
{ simpl. lia. }
{ simpl. lia. }
{ move /ltP in H1. move /leP in H2. lia. } Qed.

Lemma M_sum2 (p:nat)(M: list transaction)(B A:list order):
Vol(M) = Vol(M_above_at_p p B M) + Vol((M_below_p p B M)).
Proof. induction M. simpl. auto. simpl. 
destruct (Nat.leb p (price B (idb a))) eqn:H1; destruct (Nat.ltb (price B (idb a)) p) eqn:H2.
{ move /leP in H1. move /ltP in H2. lia. }
{ simpl. lia. }
{ simpl. lia. }
{ move /leP in H1. move /ltP in H2. lia. } Qed.



Lemma M_bound1 (p:nat)(M: list transaction)(B A:list order):
NoDup (ids B) -> NoDup (ids A) -> Matching M B A -> Vol(M) <= Qty_orders (supply_below_at_p p A) + Qty_orders (demand_above_p p B).
Proof. intros. assert(H2:= M_sum1 p M B A).  
assert(H3:Matching (M_above_p p B M) (demand_above_p p B) A).
apply M_above_p_Matching. auto. auto. 
assert(H4:Matching (M_below_at_p p B M) B (supply_below_at_p p A)).
apply M_below_at_p_Matching. auto. auto. apply Matching_Vol_B in H3.
apply Matching_Vol_A in H4. rewrite (M_sum1 p M B A). lia. 
apply filter_nodup. auto. apply filter_nodup. auto.
Qed.

Lemma M_bound2 (p:nat)(M: list transaction)(B A:list order):
NoDup (ids B) -> NoDup (ids A) -> Matching M B A -> Vol(M) <= Qty_orders (supply_below_p p A) + Qty_orders (demand_above_at_p p B).
Proof. intros. assert(H2:= M_sum2 p M B A).  
assert(H3:Matching (M_above_at_p p B M) (demand_above_at_p p B) A).
apply M_above_at_p_Matching. auto. auto. 
assert(H4:Matching (M_below_p p B M) B (supply_below_p p A)).
apply M_below_p_Matching. auto. auto. apply Matching_Vol_B in H3.
apply Matching_Vol_A in H4. rewrite (M_sum2 p M B A). lia. 
apply filter_nodup. auto. apply filter_nodup. auto.
Qed.

Theorem Bound (p:nat)(M: list transaction)(B A:list order):
NoDup (ids B) -> NoDup (ids A) -> Matching M B A -> 
Vol(M) <= Qty_orders (supply_below_p p A) + 
          Qty_orders (demand_above_p p B) +
          minof (Nat.leb) (Qty_orders (demand_at_p p B))  (Qty_orders (supply_at_p p A)).

Proof. intros. assert(H2:= M_bound1 p M B A). assert(H3:= M_bound2 p M B A).
apply H2 in H1 as Bound1. apply H3 in H1 as Bound2.
rewrite Qty_orders_supply in Bound1.
rewrite Qty_orders_demand in Bound2. unfold minof.
destruct (Nat.leb (Qty_orders (demand_at_p p B)) (Qty_orders (supply_at_p p A))).
lia. lia. all:auto. Qed.


End Bound.


(* Extra Lemmas *)

Lemma Qty_orders_delete1 (B : list order) (b: order): In b B -> Qty_orders B = Qty_orders (delete b B) + oquantity b.
Proof. revert b. induction B. simpl. intros. inversion H. intros b H. simpl in H.
destruct H. simpl. destruct (ord_eqb b a) eqn: Hb. subst. auto. move /eqP in Hb.
destruct Hb. auto. simpl. destruct (ord_eqb b a) eqn: Hb. move /eqP in Hb. subst. auto.
move /eqP in Hb. simpl. apply IHB in H. lia. Qed.

Lemma Qty_orders_subset (B1 B2 : list order): 
NoDup B1 -> NoDup B2 -> Subset B1 B2 -> Qty_orders B1 <= Qty_orders B2.
Proof. revert B1. induction B2 as [|b2 B2']. simpl. intros B1 ndB1 ndB2 H. apply Subset_of_nil in H. subst B1.
simpl. lia. simpl. intros B1 ndB1 ndB2 H. assert(H0: In b2 B1 \/ ~In b2 B1). eauto. destruct H0.
apply subset_nodup_delete_subset with (a:=b2) in H. simpl in H. 
destruct (ord_eqb b2 b2) eqn:Hb. apply IHB2' in H. assert (Hdel: Qty_orders B1 = Qty_orders (delete b2 B1) + oquantity b2). apply Qty_orders_delete1. auto. lia. eauto. eauto. move /eqP in Hb. destruct Hb. auto. auto. auto. 
apply subset_nodup_subset in H. apply IHB2' in H. lia. all:auto. eauto. Qed.



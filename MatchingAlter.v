Require Export Matching.
Require Export Match.
From Equations Require Export Equations.

Section Transform.

(*########UM Surgery for Q(b,a,M')  = Q(b,a,M) + 1 matching ############*)

(*This function g_increase_top takes two transactions ma and mb of M, where ask of ma is a and bid of mb is b.
 It reduces the trades quantity of ma and mb by 1 and inserts two transactions of single quantity 
between a <--> b and between partners if a and b. This is used in the proofs maximality for MM and UM. 
Here we proves correctness properties of g_increase_top.*)

Equations increase_ab_quantity (M:list transaction)(mb ma:transaction)(b:order)(a:order):(list transaction) :=  
increase_ab_quantity M mb ma b a := 
    (match ((Compare_dec.le_lt_dec (tquantity ma) 1), (Compare_dec.le_lt_dec (tquantity mb) 1)) with 
        |(left _ , left _ ) => ((Mk_transaction (id b) (id a) (tprice ma) 1 not1)::
                          (Mk_transaction (idb ma) (ida mb) (tprice ma) 1 not1)::
                          (delete mb (delete ma M))) 
        |(left _ , right _ ) => 
                   ((Mk_transaction (id b) (id a) (tprice ma) 1 not1)::
                    (Mk_transaction (idb ma) (ida mb) (tprice ma) 1 not1)::
                    (Mk_transaction (idb mb) (ida mb) (tprice mb) (tquantity mb - 1) _)::
                   (delete mb (delete ma M)))
        |(right _ , left _ ) => 
                ((Mk_transaction (id b) (id a) (tprice ma) 1 not1)::
                 (Mk_transaction (idb ma) (ida mb) (tprice ma) 1 not1)::
                 (Mk_transaction (idb ma) (ida ma) (tprice ma) (tquantity ma - 1) _ )::
                 (delete mb (delete ma M)))
       |(right _ , right _ ) =>
                ((Mk_transaction (id b) (id a) (tprice ma) 1 not1)::
                (Mk_transaction (idb ma) (ida mb) (tprice ma) 1 not1)::
                (Mk_transaction (idb ma) (ida ma) (tprice ma) (tquantity ma - 1) _)::
                (Mk_transaction (idb mb) (ida mb) (tprice mb) (tquantity mb - 1) _)::
                (delete mb (delete ma M))) end).

Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. lia. Defined.  
Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. lia. Defined.  
Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. lia. Defined.  
Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. lia. Defined.  

(*Proof that total Volume of matching has not changed due to above surgery *)
Lemma increase_ab_quantity_Vol (M:list transaction)(m1 m2:transaction)(b:order)(a:order):
In m1 M ->
In m2 M ->
m1<>m2 ->
Vol(M) = Vol(increase_ab_quantity M m1 m2 b a).
Proof. rewrite increase_ab_quantity_equation_1. intros. simpl.
       destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1;
       destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2.
       { simpl. assert (Hm2a: In m1 (delete m2 M)). apply delete_intro. auto. 
         intro.  destruct H1. auto. apply Vol_delete_m in Hm2a. apply Vol_delete_m in H0.
         assert(tquantity m2 = 1). destruct m2. simpl. simpl in l0.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
         assert(tquantity m1 = 1). destruct m1. simpl. simpl in l.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia. lia.
       }
       { simpl. assert (Hm2a: In m1 (delete m2 M)). apply delete_intro. auto. 
         intro.  destruct H1. auto. apply Vol_delete_m in Hm2a. apply Vol_delete_m in H0.
         assert(tquantity m1 = 1). destruct m1. simpl. simpl in l.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia. lia.
       }
       { simpl. assert (Hm2a: In m1 (delete m2 M)). apply delete_intro. auto. 
         intro.  destruct H1. auto. apply Vol_delete_m in Hm2a. apply Vol_delete_m in H0.
         assert(tquantity m2 = 1). destruct m2. simpl. simpl in l0.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia. lia. 
       }
       { simpl. assert (Hm2a: In m1 (delete m2 M)). apply delete_intro. auto. 
         intro.  destruct H1. auto. apply Vol_delete_m in Hm2a. apply Vol_delete_m in H0.
         lia.
       } Qed.

(*Proof that in increase_ab_quantity the trade quantity between a and b is increased by a single unit.*)
Lemma increase_ab_quantity_extra (M:list transaction)(m1 m2:transaction)(b:order)(a:order):
In m1 M ->
In m2 M ->
m1<>m2 ->
(id a) = (ida m2) ->
(id b) <> idb m2 ->
(id b) = (idb m1) ->
(id a) <> ida m1 ->
Qty (increase_ab_quantity M m1 m2 b a) (id b) (id a) = 1 + (Qty M (id b) (id a)).
Proof.
rewrite increase_ab_quantity_equation_1. intros.
       destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1;
       destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2.
       { simpl. replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true.
         replace (Nat.eqb (idb m2) (id b) && Nat.eqb (ida m1) (id a)) with false.
         assert (Hm2a: In m2 (delete m1 M)). apply delete_intro. auto. 
         intro.  destruct H1. auto. assert(((ida m1) <> (id a))\/(idb m1) <> (id b)).
         left. auto. apply (Qty_delete (delete m2 M) m1 a b) in H6. 
         assert(((ida m2) <> (id a))\/(idb m2) <> (id b)). right. auto.
         apply Qty_delete with (M:=M) in H7. rewrite H6. rewrite H7. auto.
         destruct (Nat.eqb (idb m2) (id b)) eqn:Hm2b;
         destruct (Nat.eqb (ida m1) (id a)) eqn:Hm1a.
         move /eqP in Hm2b. destruct H3. auto. all:simpl;auto.
         destruct (Nat.eqb (id b) (id b)) eqn:Hb; 
         destruct (Nat.eqb (id a) (id a)) eqn:Ha. simpl;auto.
         move /eqP in Ha. destruct Ha. auto. move /eqP in Hb. destruct Hb. auto.
         move /eqP in Ha. destruct Ha. auto.
       }
       { simpl. replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true.
         replace (Nat.eqb (idb m2) (id b)) with false. simpl. 
         assert(((ida m1) <> (id a))\/(idb m1) <> (id b)).
         left. auto. apply (Qty_delete (delete m2 M) m1 a b) in H6. 
         assert(((ida m2) <> (id a))\/(idb m2) <> (id b)). right. auto.
         apply Qty_delete with (M:=M) in H7. rewrite H6. rewrite H7. auto. symmetry.
         apply /eqP. auto. symmetry.          destruct (Nat.eqb (id b) (id b)) eqn:Hb; 
         destruct (Nat.eqb (id a) (id a)) eqn:Ha. simpl;auto.
         move /eqP in Ha. destruct Ha. auto. move /eqP in Hb. destruct Hb. auto.
         move /eqP in Ha. destruct Ha. auto.
       }
       { simpl. replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true.
         replace (Nat.eqb (idb m2) (id b)) with false. simpl.
         replace (Nat.eqb (ida m1) (id a)) with false. replace (Nat.eqb (idb m1) (id b)) with true. simpl. 
         assert(((ida m1) <> (id a))\/(idb m1) <> (id b)).
         left. auto. apply (Qty_delete (delete m2 M) m1 a b) in H6. 
         assert(((ida m2) <> (id a))\/(idb m2) <> (id b)). right. auto.
         apply Qty_delete with (M:=M) in H7. rewrite H6. rewrite H7. auto. symmetry.
         apply /eqP. auto. symmetry. apply /eqP. auto. symmetry. apply /eqP. auto.
         destruct (Nat.eqb (id b) (id b)) eqn:Hb; 
         destruct (Nat.eqb (id a) (id a)) eqn:Ha. simpl;auto.
         move /eqP in Ha. destruct Ha. auto. move /eqP in Hb. destruct Hb. auto.
         move /eqP in Ha. destruct Ha. auto.
       }
       {  simpl. replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true.
         replace (Nat.eqb (idb m2) (id b)) with false. simpl.
         replace (Nat.eqb (ida m1) (id a)) with false. replace (Nat.eqb (idb m1) (id b)) with true. simpl. 
         assert(((ida m1) <> (id a))\/(idb m1) <> (id b)).
         left. auto. apply (Qty_delete (delete m2 M) m1 a b) in H6. 
         assert(((ida m2) <> (id a))\/(idb m2) <> (id b)). right. auto.
         apply Qty_delete with (M:=M) in H7. rewrite H6. rewrite H7. auto. symmetry.
         apply /eqP. auto. symmetry. apply /eqP. auto. symmetry. apply /eqP. auto.
         destruct (Nat.eqb (id b) (id b)) eqn:Hb; 
         destruct (Nat.eqb (id a) (id a)) eqn:Ha. simpl;auto.
         move /eqP in Ha. destruct Ha. auto. move /eqP in Hb. destruct Hb. auto.
         move /eqP in Ha. destruct Ha. auto.
} Qed.

(* Proof that trade quantity of each bid b0 is invariant in increase_ab_quantity *)
Lemma increase_ab_quantity_Qty_bid (M:list transaction)(m1 m2:transaction)(b b0:order)(a:order):
In m1 M ->
In m2 M ->
m1<>m2 ->
(id a) = (ida m2) ->
(id b) = (idb m1) ->
Qty_bid (increase_ab_quantity M m1 m2 b a) (id b0) = Qty_bid M (id b0).
Proof. rewrite increase_ab_quantity_equation_1. intros.
       destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2;
       destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1.
       { simpl. assert(tquantity m2 = 1). destruct m2. simpl. simpl in l.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
         assert(tquantity m1 = 1). destruct m1. simpl. simpl in l0.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
         destruct (Nat.eqb (id b) (id b0)) eqn:Hbb; destruct (Nat.eqb (idb m2) (id b0)) eqn:Hmb.
         + move /eqP in Hbb. move /eqP in Hmb. rewrite <- Hmb. rewrite <- (Qty_bid_delete2 M m2). 
           replace (idb m2) with (idb m1). rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia.
         + move /eqP in Hbb. move /eqP in Hmb. rewrite <- (Qty_bid_delete1 M m2). 
           replace (id b0) with (idb m1).  rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia.
         + move /eqP in Hmb. replace (id b0) with (idb m2). rewrite <- (Qty_bid_delete2 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). lia. all:auto. move /eqP in Hbb. lia.
         + move /eqP in Hmb. move /eqP in Hbb. rewrite <- (Qty_bid_delete1 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). exact. lia. lia.
        }
        { simpl. assert(tquantity m2 = 1). destruct m2. simpl. simpl in l.
          assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
          destruct (Nat.eqb (id b) (id b0)) eqn:Hbb; destruct (Nat.eqb (idb m2) (id b0)) eqn:Hmb.
         + replace (Nat.eqb (idb m1) (id b0)) with true. 
           move /eqP in Hbb. move /eqP in Hmb. rewrite <- Hmb. rewrite <- (Qty_bid_delete2 M m2). 
           replace (idb m2) with (idb m1). rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with true.  move /eqP in Hbb.
           move /eqP in Hmb. rewrite <- (Qty_bid_delete1 M m2). 
           replace (id b0) with (idb m1).  rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with false. 
           move /eqP in Hmb. replace (id b0) with (idb m2). rewrite <- (Qty_bid_delete2 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). lia. all:auto. move /eqP in Hbb. lia.
           symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with false. 
           move /eqP in Hmb. move /eqP in Hbb. rewrite <- (Qty_bid_delete1 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). exact. lia. lia.
           symmetry. apply /eqP. move /eqP in Hbb. lia.
         }
        { simpl. assert(tquantity m1 = 1). destruct m1. simpl. simpl in l0.
          assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
          destruct (Nat.eqb (id b) (id b0)) eqn:Hbb; destruct (Nat.eqb (idb m2) (id b0)) eqn:Hmb.
         + move /eqP in Hbb. move /eqP in Hmb. rewrite <- Hmb. rewrite <- (Qty_bid_delete2 M m2). 
           replace (idb m2) with (idb m1). rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia.
         + move /eqP in Hmb. rewrite <- (Qty_bid_delete1 M m2). 
           replace (id b0) with (idb m1).  rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. move /eqP in Hbb. lia.
         + move /eqP in Hmb. replace (id b0) with (idb m2). rewrite <- (Qty_bid_delete2 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). lia. all:auto. move /eqP in Hbb. lia.
         + move /eqP in Hmb. move /eqP in Hbb. rewrite <- (Qty_bid_delete1 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). exact. lia. lia.
         }
         { simpl. destruct (Nat.eqb (id b) (id b0)) eqn:Hbb; destruct (Nat.eqb (idb m2) (id b0)) eqn:Hmb.
         + replace (Nat.eqb (idb m1) (id b0)) with true. 
           move /eqP in Hbb. move /eqP in Hmb. rewrite <- Hmb. rewrite <- (Qty_bid_delete2 M m2). 
           replace (idb m2) with (idb m1). rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with true.  move /eqP in Hbb.
           move /eqP in Hmb. rewrite <- (Qty_bid_delete1 M m2). 
           replace (id b0) with (idb m1).  rewrite <- (Qty_bid_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with false. 
           move /eqP in Hmb. replace (id b0) with (idb m2). rewrite <- (Qty_bid_delete2 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). lia. all:auto. move /eqP in Hbb. lia.
           symmetry. apply /eqP. move /eqP in Hbb. lia.
         + replace (Nat.eqb (idb m1) (id b0)) with false. 
           move /eqP in Hmb. move /eqP in Hbb. rewrite <- (Qty_bid_delete1 M m2). 
           rewrite <- (Qty_bid_delete1 (delete m2 M) m1). exact. lia. lia.
           symmetry. apply /eqP. move /eqP in Hbb. lia.
         }
 Qed.

(* Proof that trade quantity of each ask a0 is invariant in increase_ab_quantity *)
Lemma increase_ab_quantity_Qty_ask (M:list transaction)(m1 m2:transaction)(b:order)(a a0:order):
In m1 M ->
In m2 M ->
m1<>m2 ->
(id a) = (ida m2) ->
Qty_ask (increase_ab_quantity M m1 m2 b a) (id a0) = Qty_ask M (id a0).
Proof. rewrite increase_ab_quantity_equation_1. intros.
       destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2;
       destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1.
       { simpl. assert(tquantity m2 = 1). destruct m2. simpl. simpl in l.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
         assert(tquantity m1 = 1). destruct m1. simpl. simpl in l0.
         assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
         destruct (Nat.eqb (id a) (id a0)) eqn:Haa; destruct (Nat.eqb (ida m1) (id a0)) eqn:Hma.
         + replace (id a0) with (ida m2). rewrite <- (Qty_ask_delete2 M m2). 
           replace (ida m2) with (ida m1). rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. move /eqP in Haa. move /eqP in Hma. lia.
           move /eqP in Haa. move /eqP in Hma. lia.
         + move /eqP in Haa. move /eqP in Hma. replace (id a0) with (ida m2). rewrite <- (Qty_ask_delete2 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). lia. all:auto. lia. lia.
         + move /eqP in Haa. move /eqP in Hma. rewrite <- (Qty_ask_delete1 M m2).
           replace (id a0) with (ida m1).  rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia.
         + move /eqP in Haa. move /eqP in Hma. rewrite <- (Qty_ask_delete1 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). exact. lia. lia.
        }
        { simpl. assert(tquantity m2 = 1). destruct m2. simpl. simpl in l.
          assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
          destruct (Nat.eqb (id a) (id a0)) eqn:Haa; destruct (Nat.eqb (ida m1) (id a0)) eqn:Hma.
         + replace (id a0) with (ida m2). rewrite <- (Qty_ask_delete2 M m2). 
           replace (ida m2) with (ida m1). rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. move /eqP in Haa. move /eqP in Hma. lia.
           move /eqP in Haa. move /eqP in Hma. lia.
         + move /eqP in Haa. move /eqP in Hma. replace (id a0) with (ida m2). rewrite <- (Qty_ask_delete2 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). lia. all:auto. lia. lia.
         + move /eqP in Haa. move /eqP in Hma. rewrite <- (Qty_ask_delete1 M m2).
           replace (id a0) with (ida m1).  rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia.
         + move /eqP in Haa. move /eqP in Hma. rewrite <- (Qty_ask_delete1 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). exact. lia. lia.
        }
        { simpl. assert(tquantity m1 = 1). destruct m1. simpl. simpl in l0.
          assert(Ht1:=tquantity_cond).  move /leP in Ht1. lia.
          destruct (Nat.eqb (id a) (id a0)) eqn:Haa; destruct (Nat.eqb (ida m1) (id a0)) eqn:Hma.
         + replace (Nat.eqb (ida m2) (id a0)) with true. replace (id a0) with (ida m2). 
           rewrite <- (Qty_ask_delete2 M m2). 
           replace (ida m2) with (ida m1). rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. move /eqP in Haa. move /eqP in Hma. lia.
           move /eqP in Haa. move /eqP in Hma. lia. symmetry. apply /eqP. move /eqP in Haa. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with true. replace (id a0) with (ida m2). 
           rewrite <- (Qty_ask_delete2 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). lia. all:auto. 
           lia. lia. symmetry. apply /eqP. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with false. rewrite <- (Qty_ask_delete1 M m2).
           replace (id a0) with (ida m1).  rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with false.
           rewrite <- (Qty_ask_delete1 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). exact. lia. lia.
           symmetry. apply /eqP. lia.
        }
        { simpl. 
          destruct (Nat.eqb (id a) (id a0)) eqn:Haa; destruct (Nat.eqb (ida m1) (id a0)) eqn:Hma.
         + replace (Nat.eqb (ida m2) (id a0)) with true. replace (id a0) with (ida m2). 
           rewrite <- (Qty_ask_delete2 M m2). 
           replace (ida m2) with (ida m1). rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. move /eqP in Haa. move /eqP in Hma. lia.
           move /eqP in Haa. move /eqP in Hma. lia. symmetry. apply /eqP. move /eqP in Haa. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with true. replace (id a0) with (ida m2). 
           rewrite <- (Qty_ask_delete2 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). lia. all:auto. 
           lia. lia. symmetry. apply /eqP. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with false. rewrite <- (Qty_ask_delete1 M m2).
           replace (id a0) with (ida m1).  rewrite <- (Qty_ask_delete2 (delete m2 M) m1). lia.
           apply delete_intro. all:auto. lia. symmetry. apply /eqP. lia.
         + move /eqP in Haa. move /eqP in Hma.
           replace (Nat.eqb (ida m2) (id a0)) with false.
           rewrite <- (Qty_ask_delete1 M m2). 
           rewrite <- (Qty_ask_delete1 (delete m2 M) m1). exact. lia. lia.
           symmetry. apply /eqP. lia.
        } Qed.

Lemma increase_ab_quantity_Uniform (M:list transaction)(m1 m2:transaction)(b:order)(a:order):
In m1 M ->
In m2 M ->
Uniform M ->
Uniform (increase_ab_quantity M m1 m2 b a).
Proof. unfold Uniform. intros. rewrite increase_ab_quantity_equation_1.
       destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2;
       destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1.
       { simpl. constructor. auto. apply uniform_intro.
         intros. assert(In x (tprices M)).
         apply tps_of_delete in H2. 
         apply tps_of_delete in H2.
         exact. assert(In (tprice m1) (tprices M)). apply in_map_iff. exists m1. auto.
         apply uniform_elim4 with (l:=tprices M)(a1:=x)(a2:=tprice m2). all:auto.
         apply in_map_iff. exists m2. auto.
       }
       { simpl. constructor. auto. constructor. apply uniform_elim4 with (l:=(tprices M)).
         auto. apply in_map_iff. exists m2. auto. apply in_map_iff. exists m1. auto.
         apply uniform_intro.
         intros. assert(In x (tprices M)).
         apply tps_of_delete in H2. 
         apply tps_of_delete in H2.
         exact. assert(In (tprice m1) (tprices M)). apply in_map_iff. exists m1. auto.
         apply uniform_elim4 with (l:=tprices M)(a1:=x)(a2:=tprice m1). all:auto.
       }
       { simpl. constructor. auto. constructor. apply uniform_elim4 with (l:=(tprices M)).
         auto. apply in_map_iff. exists m2. auto. apply in_map_iff. exists m2. auto.
         apply uniform_intro.
         intros. assert(In x (tprices M)).
         apply tps_of_delete in H2. 
         apply tps_of_delete in H2.
         exact. assert(In (tprice m1) (tprices M)). apply in_map_iff. exists m1. auto.
         apply uniform_elim4 with (l:=tprices M)(a1:=x)(a2:=tprice m2). all:auto.
         apply in_map_iff. exists m2. auto.
       }
       { simpl. constructor. auto. constructor. auto. constructor. apply uniform_elim4 with (l:=(tprices M)).
         auto. apply in_map_iff. exists m2. auto. apply in_map_iff. exists m1. auto.
         apply uniform_intro.
         intros. assert(In x (tprices M)).
         apply tps_of_delete in H2. 
         apply tps_of_delete in H2.
         exact. assert(In (tprice m1) (tprices M)). apply in_map_iff. exists m1. auto.
         apply uniform_elim4 with (l:=tprices M)(a1:=x)(a2:=tprice m1). all:auto.
       } Qed.

Lemma increase_ab_quantity_Is_uniform  (M:list transaction)(m1 m2:transaction)(b:order)(a:order)(B A: list order):
NoDup (ids B) -> NoDup (ids A) ->
In m1 M ->
In m2 M ->
In b B ->
In a A ->
m1<>m2 ->
(id a) = (ida m2) ->
(id b) <> idb m2 ->
(id b) = (idb m1) ->
(id a) <> ida m1 ->
oprice b >= oprice a ->
Is_uniform M B A -> Is_uniform (increase_ab_quantity M m1 m2 b a) B A.
Proof. unfold Is_uniform. unfold Matching. unfold Tvalid. unfold valid. unfold Uniform. intros ndb nda. intros.
       destruct H9 as [Huni H9]. split. apply increase_ab_quantity_Uniform. all:auto. destruct H9.
       rewrite increase_ab_quantity_equation_1. 
       assert(Hm1q: tquantity m1 >0). destruct m1. simpl. assert(htemp:=tquantity_cond). move /ltP in htemp. lia.
       assert(Hm2q: tquantity m2 >0). destruct m2. simpl. assert(htemp:=tquantity_cond). move /ltP in htemp. lia.
       assert(Hbq: oquantity b >= 1). destruct b. simpl. assert(htemp:=oquantity_cond). move /ltP in htemp. lia.
       assert(Haq: oquantity a >= 1). destruct a. simpl. assert(htemp:=oquantity_cond). move /ltP in htemp. lia.
       assert(Hunip:tprice m1 = tprice m2). apply uniform_elim4 with (l:= tprices M). auto. apply in_map_iff. exists m1. 
       auto. apply in_map_iff. exists m2. auto.
       apply H9 in H as Hm1. destruct Hm1 as [b' Hm1]. destruct Hm1 as [a1 Hm1]. destruct Hm1 as [Hm1A Hm1].
       destruct Hm1 as [Hm1B Hm1]. destruct Hm1 as [Hm1idb Hm1]. destruct Hm1 as [Hm1ida Hm1]. destruct Hm1 as [Hm1trad Hm1].
       destruct Hm1 as [Hm1tqb Hm1]. destruct Hm1 as [Hm1tqa Hm1]. destruct Hm1 as [Hm1prb Hm1pra].
       apply H9 in H0 as Hm2. destruct Hm2 as [b1 Hm2]. destruct Hm2 as [a' Hm2]. destruct Hm2 as [Hm2A Hm2].
       destruct Hm2 as [Hm2B Hm2]. destruct Hm2 as [Hm2idb Hm2]. destruct Hm2 as [Hm2ida Hm2]. destruct Hm2 as [Hm2trad Hm2].
       destruct Hm2 as [Hm2tqb Hm2]. destruct Hm2 as [Hm2tqa Hm2]. destruct Hm2 as [Hm2prb Hm2pra]. 
       assert(Hb:b=b'). apply nodup_ids_uniq_order with (B:=B). auto. auto. auto. lia. subst b'.
       assert(Ha:a=a'). apply nodup_ids_uniq_order with (B:=A). auto. auto. auto. lia. subst a'.
       split. 
       { destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1;
         destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2.
         { simpl. intros. destruct H11.
           - subst t. simpl. exists b. exists a. split. auto. split. auto. split. auto. split. auto. split. auto.
             apply H9 in H0. destruct H0. destruct H0. destruct H0. destruct H11. destruct H12. destruct H13. destruct H14.
             split. lia. split. lia. split. lia. lia.
           - destruct H11. subst t. simpl. exists b1. exists a1. split. auto. split. auto. split. auto. split. auto.
             unfold tradable. lia. apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
          }
          { simpl. intros. 
            destruct H11. subst t. simpl. 
            exists b. exists a. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b1. exists a1. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b1. exists a. split. auto. split. auto. split. auto. split.  auto. unfold tradable. lia. 
            apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
          }
          { simpl. intros. destruct H11. subst t. simpl.
            exists b. exists a. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b1. exists a1. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b. exists a1. split. auto. split. auto. split. auto. split.  auto. unfold tradable. lia. 
            apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
          }
          { simpl. intros.
            destruct H11. subst t. simpl. 
            exists b. exists a. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b1. exists a1. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b1. exists a. split. auto. split. auto. split. auto. split.  auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b. exists a1. split. auto. split. auto. split. auto. split.  auto. unfold tradable. lia. 
            apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
          }  } 
          destruct H10. split. rewrite <- increase_ab_quantity_equation_1. intros. apply H10 in H12.
          rewrite increase_ab_quantity_Qty_bid. all:auto. rewrite <- increase_ab_quantity_equation_1.
          intros. apply H11 in H12. rewrite increase_ab_quantity_Qty_ask. all:auto. Qed.

Lemma increase_ab_quantity_Matching (M:list transaction)(m1 m2:transaction)(b:order)(a:order)(B A: list order):
NoDup (ids (b::B)) -> NoDup (ids (a::A)) ->
Sorted bcompetitive (b::B) ->
Sorted rev_acompetitive (a::A) ->
In m1 M ->
In m2 M ->
m1<>m2 ->
(id a) = (ida m2) ->
(id b) <> idb m2 ->
(id b) = (idb m1) ->
(id a) <> ida m1 ->
oprice b >= oprice a ->
Matching M (b::B) (a::A) -> Matching (increase_ab_quantity M m1 m2 b a) (b::B) (a::A).
Proof. unfold Matching. unfold Tvalid. unfold valid. unfold Uniform. intros ndb nda sortB sortA. 
       assert(H1:In b (b::B)). auto. assert(H2:In a (a::A)). auto. intros.
       rewrite increase_ab_quantity_equation_1. 
       assert(Hm1q: tquantity m1 >0). destruct m1. simpl. assert(htemp:=tquantity_cond). move /ltP in htemp. lia.
       assert(Hm2q: tquantity m2 >0). destruct m2. simpl. assert(htemp:=tquantity_cond). move /ltP in htemp. lia.
       assert(Hbq: oquantity b >= 1). destruct b. simpl. assert(htemp:=oquantity_cond). move /ltP in htemp. lia.
       assert(Haq: oquantity a >= 1). destruct a. simpl. assert(htemp:=oquantity_cond). move /ltP in htemp. lia.
       assert(HbS: forall x, In x (b::B) -> (Nat.leb (oprice x) (oprice b))). intros. simpl in H10. destruct H10.
       subst x. auto. apply Sorted_ointroB with (B:=B). auto. auto.
       assert(HaS: forall x, In x (a::A) -> (Nat.leb (oprice x) (oprice a))). intros. simpl in H10. destruct H10.
       subst x. auto. apply Sorted_ointro_not_A with (A:=A)(a:=a). auto. auto.
       apply H9 in H as Hm1. destruct Hm1 as [b' Hm1]. destruct Hm1 as [a1 Hm1]. destruct Hm1 as [Hm1A Hm1].
       destruct Hm1 as [Hm1B Hm1]. destruct Hm1 as [Hm1idb Hm1]. destruct Hm1 as [Hm1ida Hm1]. destruct Hm1 as [Hm1trad Hm1].
       destruct Hm1 as [Hm1tqb Hm1]. destruct Hm1 as [Hm1tqa Hm1]. destruct Hm1 as [Hm1prb Hm1pra].
       apply H9 in H0 as Hm2. destruct Hm2 as [b1 Hm2]. destruct Hm2 as [a' Hm2]. destruct Hm2 as [Hm2A Hm2].
       destruct Hm2 as [Hm2B Hm2]. destruct Hm2 as [Hm2idb Hm2]. destruct Hm2 as [Hm2ida Hm2]. destruct Hm2 as [Hm2trad Hm2].
       destruct Hm2 as [Hm2tqb Hm2]. destruct Hm2 as [Hm2tqa Hm2]. destruct Hm2 as [Hm2prb Hm2pra]. 
       assert(Hb:b=b'). apply nodup_ids_uniq_order with (B:=(b::B)). auto. auto. auto. lia. subst b'.
       assert(Ha:a=a'). apply nodup_ids_uniq_order with (B:=(a::A)). auto. auto. auto. lia. subst a'. clear Hm2A Hm1B. 
       apply HbS in Hm2B as Hm2Bp. move /leP in Hm2Bp. apply HaS in Hm1A as Hm1Ap. move /leP in Hm1Ap.
       split. 
       { intros. assert(H11:=H10). destruct (Compare_dec.le_lt_dec (tquantity m1) 1) eqn:Hm1;
         destruct (Compare_dec.le_lt_dec (tquantity m2) 1) eqn:Hm2.
         { simpl. intros. destruct H11. subst t. simpl. 
             exists b. exists a. split. auto. split. auto. split. auto. split. auto. split. auto. lia.
             destruct H11. subst t. simpl. 
             exists b1. exists a1. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
             apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
          }
          { simpl. intros. 
            destruct H11. subst t. simpl. 
            exists b. exists a. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b1. exists a1. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b1. exists a. split. auto. split. auto. split. auto. split.  auto. unfold tradable. lia. 
            apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
          }
          { simpl. intros. destruct H11. subst t. simpl.
            exists b. exists a. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b1. exists a1. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b. exists a1. split. auto. split. auto. split. auto. split.  auto. unfold tradable. lia. 
            apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
          }
          { simpl. intros.
            destruct H11. subst t. simpl. 
            exists b. exists a. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b1. exists a1. split. auto. split. auto. split. auto. split. auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b1. exists a. split. auto. split. auto. split. auto. split.  auto. unfold tradable. lia. 
            destruct H11. subst t. simpl. 
            exists b. exists a1. split. auto. split. auto. split. auto. split.  auto. unfold tradable. lia. 
            apply delete_elim1 in H11. apply delete_elim1 in H11. apply H9 in H11. auto.
          }  } 
          split. 
          rewrite <- increase_ab_quantity_equation_1. intros. rewrite increase_ab_quantity_Qty_bid. all:auto.
          apply H9. auto.
          rewrite <- increase_ab_quantity_equation_1. intros. rewrite increase_ab_quantity_Qty_ask.
          all:auto. apply H9. auto. Qed.



Theorem increase_ab_quantity_Is_uniform2 (M:list transaction)(m1 m2:transaction)
(b:order)(a:order)(B:list order)(A:list order):
NoDup (ids (b::B)) -> NoDup (ids (a::A)) -> 
In m1 M ->
In m2 M ->
m1<>m2 ->
(id a) = (ida m2) ->
(id b) <> idb m2 ->
(id b) = (idb m1) ->
(id a) <> ida m1 ->
oprice b >= oprice a ->
Is_uniform M (b::B) (a::A) -> Is_uniform (increase_ab_quantity M m1 m2 b a) (b::B) (a::A).
Proof. intros. split. 
      { apply increase_ab_quantity_Uniform. all:auto. apply H9. } 
      { apply increase_ab_quantity_Is_uniform. all:auto. } Qed.

(*#######################End of surgery one#########################*) 


(*########Surgery Two############################*)

Equations increase_b_quantity (M:list transaction)(m:transaction)(b:order)(a:order):(list transaction):=  
increase_b_quantity M m b a := 
    (match (Compare_dec.le_lt_dec (tquantity m) 1) with 
        |left _ => ((Mk_transaction (id b) (id a) (oprice a) 1 not1)::(delete m M)) 
        |right _ => ((Mk_transaction (id b) (id a) (oprice a) 1 not1)::
                     (Mk_transaction (idb m) (ida m) (tprice m) (tquantity m - 1) _ )::(delete m M)) end).
Next Obligation.
 apply PeanoNat.Nat.ltb_nlt. lia. Defined.  

Lemma increase_b_quantity_Vol (M:list transaction)
(m:transaction)(b:order)(a:order):
In m M -> Vol(M) = Vol(increase_b_quantity M m b a).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
apply Vol_delete_m in H. lia. simpl. apply Vol_delete_m in H. lia.  Qed.

(*Proof that in increase_b_quantity, the trade between a and b is increased by single unit.*)
Lemma increase_b_quantity_extra (M:list transaction)(m:transaction)(b:order)(a:order):
In m M ->
(id b) = (idb m) ->
(id a) <> (ida m) ->
Qty (increase_b_quantity M m b a) (id b) (id a) = 1 + Qty M (id b) (id a).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true. 
rewrite Qty_delete. auto. auto. symmetry. apply /andP.  split. auto. auto. 
simpl. replace (Nat.eqb (id b) (id b) && Nat.eqb (id a) (id a)) with true. 
replace (Nat.eqb (idb m) (id b) && Nat.eqb (ida m) (id a)) with false. 
rewrite Qty_delete. auto. auto. symmetry. apply /andP. intro. destruct H2.
move /eqP in H3. destruct H1. auto. symmetry. apply /andP.  split. auto. auto.  Qed.


(*Proof that trade fill of bid b is invariant in g*)
Lemma increase_b_quantity_Qty_bid (M:list transaction)(m:transaction)(b b0:order)(a:order):
In m M ->
id b = idb m ->
Qty_bid (increase_b_quantity M m b a) (id b0) = Qty_bid M (id b0).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
destruct (Nat.eqb (id b) (id b0)) eqn:Hbb. apply Qty_bid_delete2 in H.
replace (idb m) with (id b0) in H. lia. move /eqP in Hbb. lia. rewrite Qty_bid_delete1.
 move /eqP in Hbb. lia. exact. simpl. destruct (Nat.eqb (id b) (id b0)) eqn:Hbb. 
replace (Nat.eqb (idb m) (id b0)) with true. apply Qty_bid_delete2 in H. 
replace (idb m) with (id b0) in H. lia. move /eqP in Hbb. lia. symmetry.
move /eqP in Hbb. apply /eqP. lia. replace (Nat.eqb (idb m) (id b0)) with false.
apply Qty_bid_delete1. move /eqP in Hbb. lia. symmetry.
move /eqP in Hbb. apply /eqP. lia. Qed. 

(* Proof that trade fill of ask a0 is invariant in g *)
Lemma increase_b_quantity_Qty_ask (M:list transaction)(m:transaction)(b:order)(a a0:order):
In m M ->
(id a0) <> (id a) ->
(id a0) <> (ida m) ->
Qty_ask (increase_b_quantity M m b a) (id a0) = Qty_ask M (id a0).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
replace (Nat.eqb (id a) (id a0)) with false. rewrite Qty_ask_delete1. auto. auto.
symmetry.  apply /eqP. lia. simpl. replace (Nat.eqb (id a) (id a0)) with false.
replace (Nat.eqb (ida m) (id a0)) with false. rewrite Qty_ask_delete1. auto. auto.
symmetry. apply /eqP. auto. symmetry. apply /eqP. auto. Qed.

(* Proof that quantity ask a is increased by one *)
Lemma increase_b_quantity_Qty_ask_a (M:list transaction)(m:transaction)(b:order)(a:order):
In m M ->
(id a) <> (ida m) ->
Qty_ask (increase_b_quantity M m b a) (id a) = 1 + Qty_ask M (id a).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
replace (Nat.eqb (id a) (id a)) with true. rewrite Qty_ask_delete1. auto. auto.
symmetry.  apply /eqP. lia. simpl. replace (Nat.eqb (id a) (id a)) with true.
replace (Nat.eqb (ida m) (id a)) with false. rewrite Qty_ask_delete1. auto. auto.
symmetry. apply /eqP. auto. symmetry. apply /eqP. auto. Qed.

(* Proof that quantity (ida m) is decreased by one *)
Lemma increase_b_quantity_Qty_ask_ida_m (M:list transaction)(m:transaction)(b:order)(a:order):
In m M ->
(id a) <> (ida m) ->
1+ Qty_ask (increase_b_quantity M m b a) (ida m) = Qty_ask M (ida m).
Proof. rewrite increase_b_quantity_equation_1. intros. destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
replace (Nat.eqb (id a) (ida m)) with false. apply Qty_ask_delete2 in H. lia. auto.
simpl. replace (Nat.eqb (id a) (ida m)) with false.
replace (Nat.eqb (ida m) (ida m)) with true. apply Qty_ask_delete2 in H. lia. auto.
symmetry. apply /eqP. auto. Qed.

Lemma increase_b_quantity_Tvalid (M:list transaction)(m:transaction)(b:order)(a:order)(B A: list order):
In m M ->
(id b) = (idb m) ->
(id a) <> (ida m) ->
oprice b >= oprice a ->
Tvalid M (b::B) (a::A) -> Tvalid (increase_b_quantity M m b a) (b::B) (a::A).
Proof. unfold Tvalid. unfold valid. rewrite increase_b_quantity_equation_1. intros. 
destruct (Compare_dec.le_lt_dec (tquantity m) 1) eqn:Hm.
{ simpl. assert(tquantity m = 1). destruct m. simpl. simpl in l. assert(Ht:=tquantity_cond). move /leP in Ht. lia.
  simpl in H4. destruct H4.
    + subst t. simpl. exists b. exists a. split. auto. split. auto. split. auto. split. auto.
      split. auto. split. destruct b. simpl. assert(Ht:=oquantity_cond). move /leP in Ht. lia.
      split. destruct a. simpl. assert(Ht:=oquantity_cond). move /leP in Ht. lia. auto. 
    + apply delete_elim1 in H4. apply H3 in H4. auto.
}
{ simpl in H4. destruct H4.
    + subst t. simpl. exists b. exists a. split. auto. split. auto. split. auto. split. auto. split. auto. split.
      destruct b. simpl. assert(Ht:=oquantity_cond). move /leP in Ht. lia. split. destruct a. simpl.
      assert(Ht:=oquantity_cond). move /leP in Ht. lia. auto. 
    + destruct H4.
      ++ subst t. simpl. apply H3 in H. destruct H as [b0 H]. destruct H as [a0 H]. exists b0. exists a0.
         split. apply H. split. apply H.  split. apply H. split. apply H.  split. apply H.  split.
         cut(tquantity m <= oquantity b0). lia. apply H. cut (tquantity m <= oquantity a0). lia.
         apply H.
      ++ apply delete_elim1 in H4. apply H3 in H4. auto.
} Qed. 

Lemma increase_b_quantity_Matching (M:list transaction)(m:transaction)(b:order)(a:order)(B A: list order):
NoDup (ids (a::A)) ->
In m M ->
(id b) = (idb m) ->
(id a) <> (ida m) ->
oprice b >= oprice a ->
Qty_ask M (id a) < oquantity a ->
Matching M (b::B) (a::A) -> Matching (increase_b_quantity M m b a) (b::B) (a::A).
Proof. unfold Matching. intros. split. apply increase_b_quantity_Tvalid. all:auto. apply H5.
split. intros. rewrite increase_b_quantity_Qty_bid. all:auto. apply H5. auto. intros.
simpl in H6. destruct H6. subst a0. rewrite increase_b_quantity_Qty_ask_a. all:auto.
destruct (Nat.eqb (id a0) (ida m)) eqn:Hma. move /eqP in Hma. 
cut(Qty_ask M (id a0) <= oquantity a0). rewrite Hma. rewrite <- (increase_b_quantity_Qty_ask_ida_m M m b a).
 lia. all:auto. apply H5. simpl. right. auto. move /eqP in Hma. rewrite increase_b_quantity_Qty_ask.
all:auto. simpl in H. apply NoDup_cons_iff in H. destruct H. intro. apply ids_intro in H6.
rewrite H8 in H6. eauto. apply H5. simpl. right. auto. Qed. 
 
(*#######################End of surgery Two########################*)

(************************************************************************)

(*########Surgeries for the existence of M'  = M - q matchings ############*)

(* This function removes trades for a given pair of bid and ask. 
This is used in the proofs maximality for MM and UM. We claim that
given a matching M there exists another matching M' in the reduced list of
Bids and Asks such that the size of M' is equal to size of M minus q, 
where q is quanity traded between the a pair of bid and ask. *)



(**************** case when the bid and ask are fully traded **********************)


Fixpoint delete_ba_M (M:list transaction)(nb na:nat) :=
match M with 
| nil => nil
| m::M' => match (Nat.eqb (idb m) nb && Nat.eqb (ida m) na) with 
      |true => delete_ba_M M' nb na
      |false => m::(delete_ba_M M' nb na)
    end
end.

Definition nbool b:= if b then false else true.

Definition remove_ab_transactions M nb na := 
filter (fun x:transaction => nbool (Nat.eqb (idb x) nb && Nat.eqb (ida x) na)) M.


Lemma test M nb na: 
delete_ba_M M nb na = remove_ab_transactions M nb na.
Proof. revert nb na. induction M. simpl. auto. simpl. intros.
destruct (Nat.eqb (idb a) nb && Nat.eqb (ida a) na ) eqn:H1. unfold nbool. apply IHM.
unfold nbool. f_equal. apply IHM. Qed.

Lemma remove_ab_transactions_Qty M nb na:
Qty (remove_ab_transactions M nb na) nb na = 0.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (Nat.eqb (idb m) nb && Nat.eqb (ida m) na ) eqn:H. unfold nbool.
apply IHM'. simpl. rewrite H. apply IHM'. Qed.


(*Move this lemma to earlier file: This is general and basic lemma *)
Lemma filter_Uniform (M:list transaction)(f:transaction->bool) :
Uniform M -> Uniform (filter f M).
Proof. unfold Uniform. induction M as [|m M'].
simpl. auto. simpl. intros. destruct (f m) eqn:Hab.
simpl. apply uniform_intro. intros. apply uniform_elim with (x:=x) in H.
auto. apply in_map_iff in H0. destruct H0. destruct H0.
apply filter_In in H1. destruct H1. apply in_map_iff.
exists x0. auto. apply uniform_elim2 in H. apply IHM'. auto. Qed.

Lemma remove_ab_transactions_Uniform M nb na:
Uniform M -> Uniform (remove_ab_transactions M nb na).
Proof. apply filter_Uniform. Qed.

Lemma remove_ab_transactions_Vol M nb na:
Vol M = Vol (remove_ab_transactions M nb na) + Qty M nb na.
Proof. induction M. simpl. auto. simpl. destruct ((Nat.eqb (idb a) nb && Nat.eqb (ida a) na)).
simpl. lia. simpl. lia. Qed.



Lemma remove_ab_transactions_Qty_full_b M b a t:
Qty_bid M (id b) <= Qty M (id b) (id a) ->
In t (remove_ab_transactions M (id b) (id a)) -> (idb t) <> (id b).
Proof. induction M as [|m M]. simpl. auto. simpl. 
destruct (Nat.eqb (idb m) (id b)) eqn:Hb;destruct (Nat.eqb (ida m) (id a)) eqn:Ha.
{ simpl. intros. apply IHM. lia. auto. }
{ simpl. intros. assert(Qty M (id b) (id a) <= Qty_bid M (id b)).
apply Qty_le_Qty_bid. assert(tquantity m > 0). destruct m. simpl. 
assert(Ht:=tquantity_cond). move /ltP in Ht. lia. lia. }
{ simpl. intros. destruct H0. subst. move /eqP in Hb. auto. apply IHM. all:auto. }
{ simpl. intros. destruct H0. subst. move /eqP in Hb. auto. apply IHM. all:auto. } Qed.

Lemma remove_ab_transactions_Qty_full_a M b a t:
Qty_ask M (id a) <= Qty M (id b) (id a) ->
In t (remove_ab_transactions M (id b) (id a)) -> (ida t) <> (id a).
Proof.  induction M as [|m M]. simpl. auto. simpl. 
destruct (Nat.eqb (idb m) (id b)) eqn:Hb;destruct (Nat.eqb (ida m) (id a)) eqn:Ha.
{ simpl. intros. apply IHM. lia. auto. }
{ simpl. intros. destruct H0. subst. move /eqP in Ha. auto. apply IHM. all:auto. }
{ simpl. intros. assert(Qty M (id b) (id a) <= Qty_ask M (id a)).
apply Qty_le_Qty_ask. assert(tquantity m > 0). destruct m. simpl. 
assert(Ht:=tquantity_cond). move /ltP in Ht. lia. lia. }
{ simpl. intros. destruct H0. subst. move /eqP in Ha. auto. apply IHM. all:auto. } Qed.


Lemma remove_ab_transactions_conservation_bid M b a: 
Qty_bid M (id b) - Qty M (id b) (id a) = Qty_bid (remove_ab_transactions M (id b) (id a)) (id b).
Proof. induction M as [|m M]. simpl. auto. simpl. 
destruct (Nat.eqb (idb m) (id b) && Nat.eqb (ida m) (id a)) eqn:Ha.
{ simpl. replace (Nat.eqb (idb m) (id b)) with true. lia. move /andP in Ha. destruct Ha. symmetry.  apply /eqP. 
move /eqP in H. auto. }
{ simpl. destruct (Nat.eqb (idb m) (id b)) eqn:Hb.
    + assert( Qty M (id b) (id a) <= Qty_bid M (id b)). apply Qty_le_Qty_bid.
      lia.
    + auto.  
} Qed.

Lemma remove_ab_transactions_conservation_ask M b a: 
Qty_ask M (id a) - Qty M (id b) (id a) = Qty_ask (remove_ab_transactions M (id b) (id a)) (id a).
Proof. induction M as [|m M]. simpl. auto. simpl. 
destruct (Nat.eqb (idb m) (id b) && Nat.eqb (ida m) (id a)) eqn:Ha.
{ simpl. replace (Nat.eqb (ida m) (id a)) with true. lia. move /andP in Ha. destruct Ha. symmetry.  apply /eqP. 
move /eqP in H0. auto. }
{ simpl. destruct (Nat.eqb (ida m) (id a)) eqn:Hb.
    + assert( Qty M (id b) (id a) <= Qty_ask M (id a)). apply Qty_le_Qty_ask.
      lia.
    + auto.  
} Qed.




Definition reduced (A0 B0: list order)(b a :order):(list order)*(list order).
refine( match (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b)) with 
        (*bq=ba*) 
|inleft (right _) => (B0, A0)
(*bq>ba*)

 |inright _ => (B0, ((Mk_order (id a) (otime a) (oquantity a - oquantity b) (oprice a) 
(Match.Match_obligations_obligation_4 b a _) )::A0))
 
(*bq < ba*)
 |inleft (left _) => (((Mk_order (id b) (otime b) (oquantity b - oquantity a) (oprice b) 
(Match.Match_obligations_obligation_1 b a _) )::B0), A0) 
end ).
auto. auto. Defined.
(*TODO:Write similar lemma for non uniform case.*)
Lemma remove_ab_transactions_main M B0 A0 b a:
uniform (tprices M) ->
Matching M (b :: B0) (a :: A0) ->
Qty M (id b) (id a) = (Nat.min (oquantity b) (oquantity a)) ->
exists OPT, (Is_uniform OPT (fst (reduced A0 B0 b a)) (snd (reduced A0 B0 b a)))/\
        (Vol(M) = Vol(OPT) + Nat.min (oquantity b) (oquantity a)).
Proof. 
intros. exists (remove_ab_transactions M (id b) (id a)).
unfold reduced.
destruct (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b) ) eqn:Hab.
{ destruct s eqn:Hs.
{ simpl. replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a). 
  replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in H1. split. split. 
  apply remove_ab_transactions_Uniform. apply H. split. unfold Tvalid. intros. apply filter_In in H2 as H3M.
  destruct H3M. unfold nbool in H4. destruct (Nat.eqb (idb t) (id b) && Nat.eqb (ida t) (id a)) eqn:H6.
  inversion H4. apply H0 in H3. unfold valid in H3. destruct H3 as [b0 H3]. destruct H3 as [a0 H5].
  destruct H5. destruct H5. destruct H7. destruct H8. simpl in H3. simpl in H5. assert((ida t) <> (id a)).
  apply remove_ab_transactions_Qty_full_a with (M:=M)(a:=a)(b:=b). assert(Qty_ask M (id a) <= oquantity a).
  apply H0. auto. lia. auto. destruct H3. { subst. lia. }
  { subst. destruct H5. {  subst b0. unfold valid. simpl. 
    exists ({|
     id := id b;
     otime := otime b;
     oquantity := oquantity b - oquantity a;
     oprice := oprice b;
     oquantity_cond := Match.Match_obligations_obligation_1 b a l
   |}). simpl. exists a0. split. auto. split. auto.
    split. auto. split. auto. split. unfold tradable. simpl. apply H9. split. 
assert(Qty_bid M (id b) - Qty M (id b) (id a) = Qty_bid (remove_ab_transactions M (id b) (id a)) (id b)).
apply remove_ab_transactions_conservation_bid. assert(Qty_bid M (id b) <= oquantity b). apply H0. auto.
assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b) <= oquantity b - Qty M (id b) (id a)).
lia. rewrite H1 in H12. assert(tquantity t <= Qty_bid (remove_ab_transactions M (id b) (id a)) (id b) \/
tquantity t > Qty_bid (remove_ab_transactions M (id b) (id a)) (id b)). lia. destruct H13. lia.
assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (idb t) >= tquantity t). apply Qty_bid1. auto.
rewrite H7 in H14. lia. split. apply H9. apply H9. }
    { exists b0. exists a0. auto. } } split. intros. simpl in H2. destruct H2. { subst b0. simpl. 
      rewrite <-remove_ab_transactions_conservation_bid. rewrite H1. assert(Qty_bid M (id b) <= oquantity b).
apply H0. auto. lia. }
    { assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b0) <= Qty_bid M (id b0)).  apply Qty_bid_filter.
    cut (Qty_bid M (id b0) <= oquantity b0). lia. apply H0. auto. }
    intros. assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a0) <= Qty_ask M (id a0)).
    apply Qty_ask_filter. cut (Qty_ask M (id a0) <= oquantity a0). lia. apply H0. auto. 
    rewrite (remove_ab_transactions_Vol M (id b) (id a)). lia. lia. lia. } 
{ assert(oquantity a = oquantity b). lia. replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b). 
  replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in H1. split. split. 
  apply remove_ab_transactions_Uniform. apply H. split. unfold Tvalid. intros. apply filter_In in H3 as H3M.
  destruct H3M. unfold nbool in H5. destruct (Nat.eqb (idb t) (id b) && Nat.eqb (ida t) (id a)) eqn:H6.
  inversion H5. apply H0 in H4. unfold valid in H4. destruct H4 as [b0 H4]. destruct H4 as [a0 H4].
  destruct H4. destruct H7. destruct H8. destruct H9. simpl in H4. simpl in H7. assert((ida t) <> (id a)).
  apply remove_ab_transactions_Qty_full_a with (M:=M)(a:=a)(b:=b). assert(Qty_ask M (id a) <= oquantity a).
  apply H0. auto. lia. auto. assert((idb t) <> (id b)).
  apply remove_ab_transactions_Qty_full_b with (M:=M)(a:=a)(b:=b). assert(Qty_bid M (id b) <= oquantity b).
  apply H0. auto. lia. auto. destruct H4;destruct H7. subst. lia. subst. lia. subst. lia.
  exists b0. exists a0. auto. split. intros. 
  assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b0) <= Qty_bid M (id b0)).  
  apply Qty_bid_filter. cut (Qty_bid M (id b0) <= oquantity b0). lia. apply H0. auto. intros.
  assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a0) <= Qty_ask M (id a0)).  apply Qty_ask_filter.
  cut (Qty_ask M (id a0) <= oquantity a0). lia. apply H0. auto.
  rewrite (remove_ab_transactions_Vol M (id b) (id a)). lia. lia. lia. } }
  { replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b). 
  replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in H1. split. split. 
  apply remove_ab_transactions_Uniform. apply H. split. unfold Tvalid. intros. apply filter_In in H2 as H3M.
  destruct H3M. unfold nbool in H4. destruct (Nat.eqb (idb t) (id b) && Nat.eqb (ida t) (id a)) eqn:H6.
  inversion H4. apply H0 in H3. unfold valid in H3. destruct H3 as [b0 H3]. destruct H3 as [a0 H5].
  destruct H5. destruct H5. destruct H7. destruct H8. simpl in H3. simpl in H5. assert((idb t) <> (id b)).
  apply remove_ab_transactions_Qty_full_b with (M:=M)(a:=a)(b:=b). assert(Qty_bid M (id b) <= oquantity b).
  apply H0. auto. lia. auto. destruct H5. { subst. lia. }
  { subst. destruct H3. {  subst a0. unfold valid. simpl. exists b0. 
    exists ({|
     id := id a;
     otime := otime a;
     oquantity := oquantity a - oquantity b;
     oprice := oprice a;
     oquantity_cond := Match.Match_obligations_obligation_4 b a l
   |}). simpl. split. auto. split. auto.
    split. auto. split. auto. split. unfold tradable. simpl. apply H9. split. apply H9. split. 
assert(Qty_ask M (id a) - Qty M (id b) (id a) = Qty_ask (remove_ab_transactions M (id b) (id a)) (id a)).
apply remove_ab_transactions_conservation_ask. assert(Qty_ask M (id a) <= oquantity a). apply H0. auto.
assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a) <= oquantity a - Qty M (id b) (id a)).
lia. rewrite H1 in H12. assert(tquantity t <= Qty_ask (remove_ab_transactions M (id b) (id a)) (id a) \/
tquantity t > Qty_ask (remove_ab_transactions M (id b) (id a)) (id a)). lia. destruct H13. lia.
assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (ida t) >= tquantity t). apply Qty_ask1. auto.
rewrite H8 in H14. lia. split. apply H9. apply H9. }
    { simpl. unfold valid. exists b0. exists a0. auto. } } split. intros. 
      assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b0) <= Qty_bid M (id b0)).
    apply Qty_bid_filter. cut (Qty_bid M (id b0) <= oquantity b0). lia. apply H0. auto.
    intros. simpl in H2. destruct H2. { subst a0. simpl. 
rewrite <-remove_ab_transactions_conservation_ask. 
    rewrite H1. assert(Qty_ask M (id a) <= oquantity a). apply H0. auto. lia. }    
{ assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a0) <= Qty_ask M (id a0)). 
 apply Qty_ask_filter.
    cut (Qty_ask M (id a0) <= oquantity a0). lia. apply H0. auto. } 
    rewrite (remove_ab_transactions_Vol M (id b) (id a)). lia. lia. lia. }
Qed.


Lemma remove_ab_transactions_main_equal M B0 A0 b a:
uniform (tprices M) ->
Matching M (b :: B0) (a :: A0) ->
(oquantity b) = (oquantity a) ->
Qty M (id b) (id a) = (oquantity a) ->
exists OPT, (Is_uniform OPT B0 A0)/\
        (Vol(M) = Vol(OPT) + (oquantity a)).
Proof. intros. apply remove_ab_transactions_main in H0. destruct H0 as [M0 H0].
unfold reduced in H0.
destruct (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:Hba. 
destruct s. lia. simpl in H0.
exists M0. split. apply H0. replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in H0. 
  apply H0. lia. lia. auto. lia. Qed.


Lemma remove_ab_transactions_matching M B0 A0 b a:
admissible (b::B0) (a::A0) -> Matching M (b :: B0) (a :: A0) ->
Qty M (id b) (id a) = (Nat.min (oquantity b) (oquantity a)) ->
exists OPT, (Matching OPT (fst (reduced A0 B0 b a)) (snd (reduced A0 B0 b a)))/\
        (Vol(M) = Vol(OPT) + Nat.min (oquantity b) (oquantity a)).
Proof. intro adm. exists (remove_ab_transactions M (id b) (id a)). split. split.  intro. intros.
        apply filter_In in H1 as H1f. 
        destruct (Nat.eqb (idb t) (id b)) eqn:Hb;destruct (Nat.eqb (ida t) (id a)) eqn:Ha.
        - simpl in H1f. destruct H1f. inversion H3.
        - simpl in H1f. destruct H1f. unfold  reduced. destruct (Compare_dec.lt_eq_lt_dec (oquantity a)
         (oquantity b)) eqn:Hq. 
          { destruct s.
            { simpl. unfold valid. exists ({|id := id b; otime := otime b;
              oquantity := oquantity b - oquantity a; oprice := oprice b;
              oquantity_cond := Match.Match_obligations_obligation_1 b a l|}). simpl.
              apply H in H2. destruct H2 as [b0 H2]. destruct H2 as [a0 H2]. exists a0.
              destruct H2. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8.
              destruct H9. destruct H10. simpl in H2. destruct H2.
              + subst a0. rewrite H6 in Ha. move /eqP in Ha. destruct Ha. auto.
              + simpl in H4. destruct H4. 
                * subst b0. split. auto. split. auto. split. auto. split. auto. split. auto. split.
                  assert(Qty_bid M (id b) - Qty M (id b) (id a) = 
                  Qty_bid (remove_ab_transactions M (id b) (id a)) (id b)). 
                  apply remove_ab_transactions_conservation_bid. rewrite H0 in H4.
                  replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in H4.
                  assert(Qty_bid M (id b) <= oquantity b). apply H. auto. apply Qty_bid1 in H1.
                  rewrite H5 in H1. lia. lia. split. auto. lia. 
                * move /eqP in Hb. rewrite Hb in H5. apply ids_intro in H4. rewrite <- H5 in H4. 
                  assert(~In (id b) (ids B0)). apply nodup_elim2. apply adm. destruct (H12 H4).
            }
            { simpl. assert(Qty_bid M (id b) - Qty M (id b) (id a) = 
              Qty_bid (remove_ab_transactions M (id b) (id a)) (id b)). 
              apply remove_ab_transactions_conservation_bid. rewrite H0 in H4.
              replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in H4.
              assert(Qty_bid M (id b) <= oquantity b). apply H. auto. apply Qty_bid1 in H1.
              assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b)= 0).
              lia. assert(tquantity t = 0). move /eqP in Hb. rewrite Hb in H1. lia. 
              destruct t. simpl in H7. assert(Hq0:=tquantity_cond). move /ltP in Hq0. lia. lia.
            } }
            { simpl. assert(Qty_bid M (id b) - Qty M (id b) (id a) = 
              Qty_bid (remove_ab_transactions M (id b) (id a)) (id b)). 
              apply remove_ab_transactions_conservation_bid. rewrite H0 in H4.
              replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in H4.
              assert(Qty_bid M (id b) <= oquantity b). apply H. auto. apply Qty_bid1 in H1.
              assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b)= 0).
              lia. assert(tquantity t = 0). move /eqP in Hb. rewrite Hb in H1. lia. 
              destruct t. simpl in H7. assert(Hq0:=tquantity_cond). move /ltP in Hq0. lia. lia.
            } 
        - simpl in H1f. destruct H1f. unfold  reduced. destruct (Compare_dec.lt_eq_lt_dec (oquantity a)
         (oquantity b)) eqn:Hq. 
          { destruct s.
            { simpl. assert(Qty_ask M (id a) - Qty M (id b) (id a) = 
              Qty_ask (remove_ab_transactions M (id b) (id a)) (id a)). 
              apply remove_ab_transactions_conservation_ask. rewrite H0 in H4.
              replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in H4.
              assert(Qty_ask M (id a) <= oquantity a). apply H. auto. apply Qty_ask1 in H1.
              assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a)= 0).
              lia. assert(tquantity t = 0). move /eqP in Ha. rewrite Ha in H1. lia. 
              destruct t. simpl in H7. assert(Hq0:=tquantity_cond). move /ltP in Hq0. lia. lia.
            }
            { simpl. assert(Qty_ask M (id a) - Qty M (id b) (id a) = 
              Qty_ask (remove_ab_transactions M (id b) (id a)) (id a)). 
              apply remove_ab_transactions_conservation_ask. rewrite H0 in H4.
              replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in H4.
              assert(Qty_ask M (id a) <= oquantity a). apply H. auto. apply Qty_ask1 in H1.
              assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a)= 0).
              lia. assert(tquantity t = 0). move /eqP in Ha. rewrite Ha in H1. lia. 
              destruct t. simpl in H7. assert(Hq0:=tquantity_cond). move /ltP in Hq0. lia. lia.
            } }
            { simpl. unfold valid. simpl.
              apply H in H2. destruct H2 as [b0 H2]. destruct H2 as [a0 H2]. exists b0.
              exists ({|id := id a; otime := otime a;
              oquantity := oquantity a - oquantity b; oprice := oprice a;
              oquantity_cond := Match.Match_obligations_obligation_4 b a l|}). simpl.
              destruct H2. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8.
              destruct H9. destruct H10. simpl in H4. destruct H4.
              + subst b0. rewrite H5 in Hb. move /eqP in Hb. destruct Hb. auto.
              + simpl in H2. destruct H2. 
                * subst a0. split. auto. split. auto. split. auto. split. auto. split. auto. split.
                  auto. split.
                  assert(Qty_ask M (id a) - Qty M (id b) (id a) = 
                  Qty_ask (remove_ab_transactions M (id b) (id a)) (id a)). 
                  apply remove_ab_transactions_conservation_ask. rewrite H0 in H2.
                  replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in H2.
                  assert(Qty_ask M (id a) <= oquantity a). apply H. auto. apply Qty_ask1 in H1.
                  rewrite H6 in H1. lia. lia. split. auto. lia. 
                * move /eqP in Ha. rewrite Ha in H6. apply ids_intro in H2. rewrite <- H6 in H2. 
                  assert(~In (id a) (ids A0)). apply nodup_elim2. apply adm. destruct (H12 H2).
            } 
        - simpl in H1f. destruct H1f. apply H in H2. destruct H2 as [b0 H2]. destruct H2 as [a0 H2]. 
          destruct H2. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8.
          destruct H9. destruct H10. simpl in H2. simpl in H4. destruct H2; destruct H4.
          + subst. move /eqP in Ha. lia. 
          + subst. move /eqP in Ha. lia.
          + subst. move /eqP in Hb. lia.
          + exists b0. exists a0. unfold reduced. 
            destruct (Compare_dec.lt_eq_lt_dec (oquantity a) (oquantity b)) eqn:Hq. 
            * destruct s.
              ** simpl. split. auto. split. auto. split. auto. split. auto.
                 split. auto. split. auto. split. auto. split. auto. auto.
              ** simpl. split. auto. split. auto. split. auto. split. auto.
                 split. auto. split. auto. split. auto. split. auto. auto.
            * simpl. split. auto. split. auto. split. auto. split. auto.
                 split. auto. split. auto. split. auto. split. auto. auto.
   - split. 
      * intros. unfold  reduced in H1. destruct (Compare_dec.lt_eq_lt_dec (oquantity a)
         (oquantity b)) eqn:Hq. 
          { destruct s. 
           { simpl in H1. destruct H1. 
            + subst b0. simpl.
              assert(Qty_bid M (id b) - Qty M (id b) (id a) = 
              Qty_bid (remove_ab_transactions M (id b) (id a)) (id b)). 
              apply remove_ab_transactions_conservation_bid. rewrite H0 in H1.
              replace (Nat.min (oquantity b) (oquantity a)) with (oquantity a) in H1.
              assert(Qty_bid M (id b) <= oquantity b). apply H. auto. lia. lia. 
           + assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b0) <= Qty_bid M (id b0)).
             apply Qty_bid_filter. cut (Qty_bid M (id b0) <= oquantity b0). lia. apply H. auto.
          }
          { simpl in H1. assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b0) <= Qty_bid M (id b0)).
            apply Qty_bid_filter. cut (Qty_bid M (id b0) <= oquantity b0). lia. apply H. auto.
          } }
          { simpl in H1. assert(Qty_bid (remove_ab_transactions M (id b) (id a)) (id b0) <= Qty_bid M (id b0)).
            apply Qty_bid_filter. cut (Qty_bid M (id b0) <= oquantity b0). lia. apply H. auto.
          }
      * intros. unfold  reduced in H1. destruct (Compare_dec.lt_eq_lt_dec (oquantity a)
         (oquantity b)) eqn:Hq. 
          { destruct s. 
           { simpl in H1. assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a0) <= Qty_ask M (id a0)).
             apply Qty_ask_filter. cut (Qty_ask M (id a0) <= oquantity a0). lia. apply H. auto.
           }
           { simpl in H1. assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a0) <= Qty_ask M (id a0)).
             apply Qty_ask_filter. cut (Qty_ask M (id a0) <= oquantity a0). lia. apply H. auto.
           } }
         { simpl in H1. destruct H1. 
            + subst a0. simpl.
              assert(Qty_ask M (id a) - Qty M (id b) (id a) = 
              Qty_ask (remove_ab_transactions M (id b) (id a)) (id a)). 
              apply remove_ab_transactions_conservation_ask. rewrite H0 in H1.
              replace (Nat.min (oquantity b) (oquantity a)) with (oquantity b) in H1.
              assert(Qty_ask M (id a) <= oquantity a). apply H. auto. lia. lia. 
           + assert(Qty_ask (remove_ab_transactions M (id b) (id a)) (id a0) <= Qty_ask M (id a0)).
             apply Qty_ask_filter. cut (Qty_ask M (id a0) <= oquantity a0). lia. apply H. auto.
         } 
       - rewrite <- H0. apply remove_ab_transactions_Vol. Qed.


End Transform.
Require Export Definitions.

Set Implicit Arguments.

Section competitiveness.

Definition bcompetitive (b b':order):= (Nat.ltb (oprice b') (oprice b)) ||
((Nat.eqb (oprice b') (oprice b)) && (Nat.leb (otime b) (otime b') )).

Definition acompetitive (a a':order):= (Nat.ltb (oprice a) (oprice a')) ||
((Nat.eqb (oprice a) (oprice a')) && (Nat.leb (otime a) (otime a') )).

Definition eqcompetitive (a a':order):= ((Nat.eqb (oprice a) (oprice a')) && (Nat.eqb (otime a) (otime a') )).

Definition rev_acompetitive (a a':order):= (Nat.ltb (oprice a') (oprice a)) ||
((Nat.eqb (oprice a') (oprice a)) && (Nat.leb (otime a') (otime a))).

Definition dec_price (t t':transaction):= (Nat.leb (tprice t) (tprice t')).

Definition incr_price (t t':transaction):= (Nat.leb (tprice t') (tprice t)).

Lemma bcompetitive_contadiction (b b':order):
bcompetitive b b'-> bcompetitive b' b -> ~eqcompetitive b b' -> False.
Proof. unfold bcompetitive.  unfold eqcompetitive. intros. 
       move /orP in H. move /orP in H0. destruct H0; destruct H.
       {  move /ltP in H. move /ltP in H0. lia. }
       {  destruct H1. move /andP in H. destruct H.
          apply /andP. move /eqP in H.  split. apply /eqP. 
          auto. move /ltP in H0. move /leP in H1. lia. }
       {  destruct H1. move /andP in H0. destruct H0.
          apply /andP. move /eqP in H0.  split. apply /eqP. 
          auto. move /ltP in H. move /leP in H1. lia. }
       {  destruct H1. move /andP in H0. destruct H0.
          move /andP in H. destruct H. apply /andP. split.
          auto. move /leP in H1. move /leP in H2. apply /eqP. lia. } Qed.

Lemma acompetitive_contadiction (a a':order):
acompetitive a a'-> acompetitive a' a -> ~eqcompetitive a a' -> False.
Proof. unfold acompetitive.  unfold eqcompetitive. intros. 
       move /orP in H. move /orP in H0. destruct H0; destruct H.
       {  move /ltP in H. move /ltP in H0. lia. }
       {  destruct H1. move /andP in H. destruct H.
          apply /andP. move /eqP in H.  split. apply /eqP. 
          auto. move /ltP in H0. move /leP in H1. lia. }
       {  destruct H1. move /andP in H0. destruct H0.
          apply /andP. move /eqP in H0.  split. apply /eqP. 
          auto. move /ltP in H. move /leP in H1. lia. }
       {  destruct H1. move /andP in H0. destruct H0.
          move /andP in H. destruct H. apply /andP. split.
          auto. move /leP in H1. move /leP in H2. apply /eqP. lia. } Qed.

Lemma bcompetitive_P : transitive bcompetitive /\ comparable2 bcompetitive.
Proof.  { split.
          { unfold transitive. unfold bcompetitive.  
            intros y x z H H1. move /orP in H1. move /orP in H.
            apply /orP. destruct H1;destruct H. 
            { left. move /leP in H0. move /leP in H. apply /leP. lia. }
            { move /andP in H. destruct H. left.  
              move /leP in H0. move /eqP in H. apply /leP. lia. }
            { move /andP in H0. destruct H0. left.
              move /leP in H. move /eqP in H0. apply /leP. lia. }
            { move /andP in H0. move /andP in H. destruct H0. destruct H.
              right.
              move /eqP in H. move /eqP in H0. apply /andP.
              split. apply /eqP. lia. apply /leP. move /leP in H1. 
              move /leP in H2. lia. } }
            { unfold comparable2.
              unfold bcompetitive. intros. destruct x. destruct y.  simpl. 
              assert((oprice0 = oprice)\/(oprice0 < oprice)\/(oprice < oprice0)).
              lia. destruct H.
              subst. assert(Nat.ltb oprice oprice = false).
              apply /ltP. lia. rewrite H. simpl.
              assert(Nat.eqb oprice oprice =true). auto. rewrite H0. simpl. 
              assert((otime0 <= otime)\/(otime < otime0)). lia. destruct H1.
              right. apply /leP. auto. left. apply /leP. lia.
              destruct H. left. apply /orP. left. apply /ltP. auto. right.
              apply /orP. left. apply /ltP. auto.
               } } Qed.

Lemma acompetitive_P : transitive acompetitive /\ comparable2 acompetitive.
Proof.  { split.
          { unfold transitive. unfold acompetitive.  
            intros y x z H H1. move /orP in H1. move /orP in H.
            apply /orP. destruct H1;destruct H. 
            { left. move /leP in H0. move /leP in H. apply /leP. lia. }
            { move /andP in H. destruct H. left.  
              move /leP in H0. move /eqP in H. apply /leP. lia. }
            { move /andP in H0. destruct H0. left.
              move /leP in H. move /eqP in H0. apply /leP. lia. }
            { move /andP in H0. move /andP in H. destruct H0. destruct H.
              right.
              move /eqP in H. move /eqP in H0. apply /andP.
              split. apply /eqP. lia. apply /leP. move /leP in H1. 
              move /leP in H2. lia. } }
            { unfold comparable2.
              unfold acompetitive. intros. destruct x. destruct y.  simpl. 
              assert((oprice0 = oprice)\/(oprice < oprice0)\/(oprice0 < oprice)).
              lia. destruct H.
              subst. assert(Nat.ltb oprice oprice = false).
              apply /ltP. lia. rewrite H. simpl.
              assert(Nat.eqb oprice oprice =true). auto. rewrite H0. simpl. 
              assert((otime0 <= otime)\/(otime < otime0)). lia. destruct H1.
              right. apply /leP. auto. left. apply /leP. lia.
              destruct H. left. apply /orP. left. apply /ltP. auto. right.
              apply /orP. left. apply /ltP. auto.
               } } Qed.

Lemma not_acompetitive (a1 a2:order): ~acompetitive a1 a2 -> acompetitive a2 a1.
Proof. unfold acompetitive. intros H. unfold not in H. apply /orP.
       destruct(Nat.ltb (oprice a1) (oprice a2)) eqn:H1. 
       { simpl in H. destruct H. auto. }
       { simpl in H.  destruct(Nat.eqb (oprice a1) (oprice a2)) eqn: H2.
          { simpl in H. destruct (Nat.leb (otime a1) (otime a2)) eqn: H3.
           destruct H. auto. right. apply /andP. split. move /eqP in H2.
           rewrite H2. apply /eqP. auto. move /leP in H3. apply /leP. lia. }
          { simpl in H. destruct (Nat.leb (otime a1) (otime a2)) eqn: H3.
            move /ltP in H1. move /eqP in H2. left. apply /ltP. lia. 
            move /ltP in H1. move /eqP in H2. move /leP in H3. 
            left. apply /ltP. lia.
           }
         }
         Qed.  

Lemma not_bcompetitive (b1 b2:order): ~bcompetitive b1 b2 -> bcompetitive b2 b1.
Proof. unfold bcompetitive. intros H. unfold not in H. apply /orP.
       destruct(Nat.ltb (oprice b2) (oprice b1)) eqn:H1. 
       { simpl in H. destruct H. auto. }
       { simpl in H.  destruct(Nat.eqb (oprice b2) (oprice b1)) eqn: H2.
          { simpl in H. destruct (Nat.leb (otime b1) (otime b2)) eqn: H3.
           destruct H. auto. right. apply /andP. split. move /eqP in H2.
           rewrite H2. apply /eqP. auto. move /leP in H3. apply /leP. lia. }
          { destruct (Nat.leb (otime b1) (otime b2)) eqn: H3.
            move /ltP in H1. move /eqP in H2. left. apply /ltP. lia. 
            move /ltP in H1. move /eqP in H2. move /leP in H3. 
            left. apply /ltP. lia.
           }
         }
         Qed.  


End competitiveness.



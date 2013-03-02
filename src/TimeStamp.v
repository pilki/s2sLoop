(* The polyhedral language *)
Require Import Libs.
Require Import Errors.
Require Import Polyhedra.
Require Import Loops.
Require Import Memory.
Require Import ArithClasses.
Require Import Permutation.
Require Import Sorted.
Require Import Instructions.
Require Import Bounds.
Require Import BoxedPolyhedra.
Require Import Psatz.
Require Import PolyBase.
Open Scope string_scope.
(*Set Implicit Arguments.*)
Open Scope Z_scope.

Hint Resolve Zgt_lt.
(* a time stamp is a multi dimentionnal date *)
Definition Time_Stamp := list Z.

Inductive time_stamp_all_0: Time_Stamp -> Prop :=
| TSA0_nil: time_stamp_all_0 []
| TSA0_cons: forall l, time_stamp_all_0 l -> time_stamp_all_0 (0 :: l).

Inductive time_stamp_lt_0: Time_Stamp -> Prop :=
| TSL0_0: forall l, time_stamp_lt_0 l -> time_stamp_lt_0 (0 :: l)
| TSL0_lt: forall z l, z < 0 -> time_stamp_lt_0 (z :: l).

Inductive time_stamp_gt_0: Time_Stamp -> Prop :=
| TSG0_0: forall l, time_stamp_gt_0 l -> time_stamp_gt_0 (0 :: l)
| TSG0_gt: forall z l, 0 < z -> time_stamp_gt_0 (z :: l).

Hint Constructors time_stamp_gt_0 time_stamp_lt_0 time_stamp_all_0: timestamp.

Lemma not_all_0_lt: forall ts,
  time_stamp_all_0 ts -> time_stamp_lt_0 ts -> False.
Proof.
  intros ts H; induction H; intros H'; inv H'; auto with timestamp; lia.
Qed.

Lemma not_all_0_gt: forall ts,
  time_stamp_all_0 ts -> time_stamp_gt_0 ts -> False.
Proof.
  intros ts H; induction H; intros H'; inv H'; auto with timestamp; lia.
Qed.

Lemma not_lt_gt: forall ts,
  time_stamp_gt_0 ts -> time_stamp_lt_0 ts -> False.
Proof.
  intros ts H; induction H; intros H'; inv H'; auto with timestamp; lia.
Qed.
Hint Resolve not_all_0_gt not_all_0_lt not_lt_gt: timestamp.

Lemma time_stamp_0_trichotomy (ts: Time_Stamp):
  {time_stamp_lt_0 ts}+{time_stamp_all_0 ts}+{time_stamp_gt_0 ts}.
Proof.
  induction' ts as [|z ts].
  Case "@nil".
    auto with timestamp.
  Case "cons z ts".
    destruct (Ztrichotomy_inf z 0) as [[?|?]|?]; subst; auto with timestamp.
    destruct IHts as [[?|?]|?]; auto with timestamp.
Qed.

Inductive time_stamp_eq: Time_Stamp -> Time_Stamp -> Prop :=
  | TSE_nil_r: forall l, time_stamp_all_0 l ->
    time_stamp_eq l []
  | TSE_nil_l: forall l, time_stamp_all_0 l ->
    time_stamp_eq [] l
  | TSE_cons: forall z l1 l2, time_stamp_eq l1 l2 ->
    time_stamp_eq (z :: l1) (z::l2).

Hint Constructors time_stamp_eq.

Instance TSE_eq: Equivalence time_stamp_eq. 
Proof.
  prove_equiv.

  Case "Reflexivity".
    intro x; induction' x; auto with timestamp.
  Case "Symmetry".
    intro x; induction x as [|z x]; intros y EQ; inv EQ; auto with timestamp.
  Case "Transitivity".
  intros * EQxy. revert z.
  induction' EQxy; intros * EQyz; inv EQyz; auto with timestamp.
  SCase "TSE_nil_r".
    revert dependent z.
    induction H; intros; inv H0; auto with timestamp.
  SCase "TSE_nil_l".
    inv H. constructor. constructor.
    revert dependent l2; induction H2; intros; inv H0; auto with timestamp.
  SCase "TSE_cons".
    inv H. constructor. constructor. clear IHEQxy.
    revert dependent l1; induction H1; intros; inv EQxy; auto with timestamp.
Qed.

Add Parametric Morphism : time_stamp_eq with 
  signature time_stamp_eq ==> time_stamp_eq ==> iff as TSE_TSE.
Proof.
  intros.
  split; intros.
    symmetry in H. repeat intuition (etransitivity; eauto with timestamp).
    symmetry in H0. repeat intuition (etransitivity; eauto with timestamp).
Qed.
  
Add Parametric Morphism : time_stamp_all_0 with 
  signature time_stamp_eq ==> iff as TSE_TSA0.
Proof.
  intros.
   induction H; split; intro TSA; inv TSA; auto with timestamp;
     match goal with
       | H : _ <-> _ |- _ => destruct H
     end; auto with timestamp.
Qed.

Add Parametric Morphism : time_stamp_lt_0 with 
  signature time_stamp_eq ==> iff as TSE_TSL0.
Proof.
  intros.
  induction H; split; intro TSL; inv TSL; auto with timestamp;
    try (inv H; lia);
    try solve [inv H; exfalso; eauto with timestamp];
    destruct IHtime_stamp_eq; auto with timestamp.
Qed.

Add Parametric Morphism : time_stamp_gt_0 with 
  signature time_stamp_eq ==> iff as TSE_TSG0.
Proof.
  intros.
  induction H; split; intro TSL; inv TSL; auto with timestamp;
    try (inv H; lia);
    try solve [inv H; exfalso; eauto with timestamp];
    destruct IHtime_stamp_eq; auto with timestamp.
Qed.

(* strict but toal ordering on time_stamps *)

Inductive time_stamp_lt: Time_Stamp -> Time_Stamp -> Prop :=
| TSLT_nil_l: forall l, time_stamp_gt_0 l -> time_stamp_lt [] l
| TSLT_nil_r: forall l, time_stamp_lt_0 l -> time_stamp_lt l []
| TSLT_lt: forall a b la lb, a < b -> time_stamp_lt (a :: la) (b :: lb)
| TSLT_eq: forall a l1 l2, time_stamp_lt l1 l2 -> time_stamp_lt (a::l1) (a::l2).

Hint Constructors time_stamp_lt.
Hint Rewrite cons_not_nil nil_not_cons: clean.

(* XXX MOVE SOMEWHERE *)
Lemma Permutation_cons_exists_aux A a (l1 l2 :list A):
  Permutation (a::l1) l2 ->
  exists l21 l22,
    l2 = l21 ++ a :: l22.
Proof.
  intro. assert (In a l2).
    eapply Permutation_in; eauto. red. auto.
  clear H.
  clear l1. revert H0.
  induction l2; auto.
  intro IN.
  destruct IN.
    subst; exists (@nil A) l2; auto.
    edestruct IHl2 as [l21 [l22 ?]]; auto.
    subst.
    exists (a0::l21) l22; auto.
Qed.


Lemma time_stamp_lt_trichotomy: forall (ts1 ts2: Time_Stamp),
  {time_stamp_lt ts1 ts2} + {time_stamp_eq ts1 ts2} + {time_stamp_lt ts2 ts1}.
Proof.
  induction' ts1 as [|z1 ts1].
  Case "@nil".
    intro ts2.
    destruct (time_stamp_0_trichotomy ts2) as [[|]|]; auto with timestamp.
  Case "cons z1 ts1".
    intros ts2; destruct' ts2 as [|z2 ts2].
    SCase "@nil".
      destruct (Ztrichotomy_inf 0 z1) as [[|]|]; subst; auto 6 with timestamp.
      destruct (time_stamp_0_trichotomy ts1) as [[|]|]; auto with timestamp.
    SCase "cons z2 ts2".
      destruct (Ztrichotomy_inf z1 z2) as [[|]|]; subst; auto with timestamp.
        destruct (IHts1 ts2) as [[|]|]; auto with timestamp.
Qed.

Lemma time_stamp_lt_lt_0: forall ts1 ts2,
  time_stamp_lt ts1 ts2 -> time_stamp_lt_0 ts2 ->
  time_stamp_lt_0 ts1.
Proof.
  intros * LT LT0. revert dependent ts1.
  induction' LT0; intros; inv LT; auto with timestamp.
  Case "TSL0_0".
  inv H; auto with timestamp. lia.
  Case "TSL0_lt".
  inv H0;  lia.
  constructor; lia.
Qed.

Lemma time_stamp_gt_gt_0: forall ts1 ts2,
  time_stamp_gt_0 ts1 -> time_stamp_lt ts1 ts2 ->
  time_stamp_gt_0 ts2.
Proof.
  intros * GT0 GT. revert dependent ts2.
  induction' GT0; intros; inv GT; auto with timestamp.
  Case "TSG0_0".
  inv H; auto with timestamp. lia.
  Case "TSG0_gt".
  inv H0;  lia.
  constructor; lia.
Qed.

Lemma time_stamp_lt_0_gt_0_lt: forall ts1 ts2,
  time_stamp_lt_0 ts1 -> time_stamp_gt_0 ts2 ->
  time_stamp_lt ts1 ts2.
Proof.
  intros * TSL; revert ts2; induction' TSL; intros ts2 TSG; inv TSG; auto with timestamp.
  Case "TSL0_lt".
  constructor. lia.
Qed.

Lemma time_stamp_all_0_lt_0_lt: forall st1 st2,
  time_stamp_all_0 st1 -> time_stamp_lt_0 st2 ->
  time_stamp_lt st2 st1.
Proof.
  intros * TSA0; revert st2; induction' TSA0; intros * TSL0.
  Case "TSA0_nil".
    auto with timestamp.
  Case "TSA0_cons".
    inv TSL0; eauto with timestamp.
Qed.

Lemma time_stamp_all_0_gt_0_lt: forall st1 st2,
  time_stamp_all_0 st1 -> time_stamp_gt_0 st2 ->
  time_stamp_lt st1 st2.
Proof.
  intros * TSA0; revert st2; induction' TSA0; intros * TSL0.
  Case "TSA0_nil".
    auto with timestamp.
  Case "TSA0_cons".
    inv TSL0; eauto with timestamp.
Qed.



Lemma time_stamp_lt_0_nil: time_stamp_lt_0 [] -r> False.
Proof. constructor. intro H. inv H. Qed.
Lemma time_stamp_gt_0_nil: time_stamp_gt_0 [] -r> False.
Proof. constructor. intro H. inv H. Qed.


Hint Rewrite time_stamp_lt_0_nil time_stamp_gt_0_nil:clean.

Hint Resolve time_stamp_all_0_lt_0_lt time_stamp_all_0_gt_0_lt
  time_stamp_lt_0_gt_0_lt time_stamp_gt_gt_0 time_stamp_lt_lt_0: timestamp.


Lemma time_stamp_all_0_lt_0: forall st1 st2,
  time_stamp_lt st2 st1 ->
  time_stamp_all_0 st1 ->
  time_stamp_lt_0 st2 .
Proof.
  intros * TSL; induction' TSL; intros TSA0; eauto with timestamp.
  Case "TSLT_nil_l".
      exfalso. eapply not_all_0_gt; eauto.
  Case "TSLT_lt".
    inv TSA0; eauto with timestamp.
  Case "TSLT_eq".
    inv TSA0; eauto with timestamp.
Qed.

Lemma time_stamp_all_0_gt_0: forall st1 st2,
  time_stamp_lt st1 st2 -> time_stamp_all_0 st1 ->
  time_stamp_gt_0 st2.
Proof.
  intros * TSL; induction' TSL; intros TSA0; eauto with timestamp.
  Case "TSLT_nil_r".
      exfalso. eapply not_all_0_lt; eauto.
  Case "TSLT_lt".
    inv TSA0; eauto with timestamp.
  Case "TSLT_eq".
    inv TSA0; eauto with timestamp.
Qed.

Hint Resolve  time_stamp_all_0_lt_0 time_stamp_all_0_gt_0: timestamp.




Instance time_stamp_lt_transitive: Transitive time_stamp_lt.
Proof.
  unfold Transitive.
  intros * TSLTxy. revert z.
  induction' TSLTxy; intros * TSLTls; eauto with timestamp.
  Case "TSLT_lt".
    inv TSLTls; eauto with timestamp.
    inv H0; auto with timestamp.
    constructor. constructor. lia.
    constructor. lia.
  Case "TSLT_eq".
    inv TSLTls; eauto with timestamp.
    inv H; eauto with timestamp.
Qed.

Lemma time_stamp_lt_lt_false: forall ts1 ts2,
  time_stamp_lt ts1 ts2 -> time_stamp_lt ts2 ts1 ->
  False.
Proof.
  intros ts1 ts2 H; induction H; intro TSL21; eauto with timestamp; inv TSL21; subst; eauto with timestamp; lia.
Qed.

Lemma time_stamp_lt_eq_false: forall ts1 ts2,
  time_stamp_lt ts1 ts2 -> time_stamp_eq ts1 ts2 ->
  False.
Proof.
  intros ts1 ts2 H; induction H; intro TSE21; eauto with timestamp; inv TSE21; subst; eauto with timestamp; lia.
Qed.

Hint Resolve time_stamp_lt_eq_false time_stamp_lt_lt_false: timestamp.



Lemma time_stamp_lt_antisymmectric: forall ts1 ts2,
  time_stamp_lt ts1 ts2 -> time_stamp_lt ts2 ts1 -> False.
Proof.
  intros * TS12.
  induction' TS12; intros TS21; auto with timestamp; inv TS21; try omegaContradiction; eauto with timestamp; clean.
Qed.

Hint Resolve time_stamp_lt_antisymmectric: timestamp.

Lemma time_stamp_lt_dec: forall ts1 ts2,
  {time_stamp_lt ts1 ts2} + {~time_stamp_lt ts1 ts2}.
Proof.
  unfold not.
  intros. destruct (time_stamp_lt_trichotomy ts1 ts2) as [[|]|]; eauto with timestamp.
Qed.

Definition time_stamp_le ts1 ts2 :=
  time_stamp_lt ts1 ts2 \/ time_stamp_eq ts1 ts2.

Hint Unfold time_stamp_le.
Lemma time_stamp_le_dec: forall ts1 ts2,
  {time_stamp_le ts1 ts2} + {~time_stamp_le ts1 ts2}.
Proof.
  unfold time_stamp_le, not.
  intros. destruct (time_stamp_lt_trichotomy ts1 ts2) as [[|]|]; eauto with timestamp.
  right. intros [?|?]; eauto with timestamp. symmetry in H. eauto with timestamp.

Qed.

Ltac subst_ts :=
  repeat
  match goal with
    | H : time_stamp_eq ?st1 ?st2 |- _ =>
      try rewrite H in *;
      clear H; clear st1
  end.



Add Parametric Morphism : time_stamp_lt with 
  signature time_stamp_eq ==> time_stamp_eq ==> impl as TSE_TSL_impl.
Proof.
  intros. unfold impl. intro TSL. revert dependent y. revert dependent y0.
  induction' TSL; intros; subst_ts.
  Case "TSLT_nil_l".
    inv H1; eauto with timestamp.
  Case "TSLT_nil_r".
    inv H0; eauto with timestamp.
  Case "TSLT_lt".
    inv H0; try inv H2; inv H1; try inv H0; eauto with timestamp. lia.
  Case "TSLT_eq".
  inv H0; inv H; eauto with timestamp.
  inv H1; inv H0. eauto with timestamp.
  inv H1.  constructor. constructor. rewrite <- H4.
  eauto with timestamp.
  inv H0. constructor. constructor. rewrite <- H4.
  eauto with timestamp.
Qed.




Add Parametric Morphism : time_stamp_lt with 
  signature time_stamp_eq ==> time_stamp_eq ==> iff as TSE_TSL.
Proof.
  split; intro.
  rewrite H in H1. rewrite H0 in H1. assumption.
  rewrite H. rewrite H0. assumption.
Qed.
  



Instance time_stamp_le_transitive: Transitive time_stamp_le.
Proof.
  unfold Transitive. intros.
  unfold time_stamp_le in *.
  destruct H; destruct H0; subst_ts; auto.
  left; etransitivity; eauto.
  right; reflexivity.
Qed.


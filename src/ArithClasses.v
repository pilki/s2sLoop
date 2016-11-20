Add LoadPath "../from_compcert".
Require Import Coqlibext.
Require Import Psatz.
Require Import Libs.
Require Import CeildFloord.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Set Implicit Arguments.
(* we define a very simpl class that subsumes Z and int. We could
   probably do way better, but that should be enough for our purpose
   in Loops*)

Global Generalizable Variable Num.
Class Numerical (A:Type) :=
{ A0: A;
  A1: A;
  Aopp: A -> A;
  Aadd: A -> A -> A;
  Aminus: A -> A -> A;
  Amul: A -> A -> A;
  Ale: relation A;
  Amin : A -> A -> A;
  Amax : A -> A -> A;
  Aceild: A -> A -> option A;
  Afloord: A -> A -> option A;
(* Props *)
  Aadd_comm: forall (a1 a2:A), Aadd a1 a2 = Aadd a2 a1;
  Amul_comm: forall (a1 a2:A), Amul a1 a2 = Amul a2 a1;
  Aadd_A0_r : forall (a:A), Aadd a A0 = a;
  Amul_A0_r: forall (a:A), Amul a A0 = A0;
  Amul_A1_r: forall (a:A), Amul a A1 = a;
  Aopp_involutive: forall (a:A), Aopp (Aopp a) = a;
  Aopp_A0: Aopp A0 = A0;
  Aopp_add_distr: forall (a1 a2:A), Aopp (Aadd a1 a2) = Aadd (Aopp a1) (Aopp a2);
  Aopp_mul_distr_l: forall (a1 a2:A), Aopp (Amul a1 a2) = Amul (Aopp a1) a2;
  Amul_add_distr_r: forall (a1 a2 a3: A), Amul a3 (Aadd a1 a2) = 
    Aadd (Amul a3 a1) (Amul a3 a2);
  Amul_assoc: forall (a1 a2 a3:A), Amul a1 (Amul a2 a3) = Amul (Amul a1 a2) a3;
  Aadd_assoc: forall (a1 a2 a3:A), Aadd a1 (Aadd a2 a3) = Aadd (Aadd a1 a2) a3;
  Ale_dec: forall (a1 a2: A), {Ale a1 a2} + {~(Ale a1 a2)};
  Ale_preorder :> PreOrder Ale;
  Ale_antisym: forall a1 a2, Ale a1 a2 -> Ale a2 a1 -> a1 = a2;
  Agt_le: forall a1 a2, ~Ale a1 a2 -> Ale a2 a1;

  Amin_comm: forall a1 a2, Amin a1 a2 = Amin a2 a1;
  Ale_min: forall a1 a2,
    Ale a1 a2 -> Amin a1 a2 = a1;

  Amax_comm: forall a1 a2, Amax a1 a2 = Amax a2 a1;
  Ale_max: forall a1 a2,
    Ale a1 a2 -> Amax a1 a2 = a2;

  num_eq_dec :> EqDec A
}.

Delimit Scope numerical_scope with numerical.
Notation "0" := A0 : numerical_scope.
Notation "1" := A1: numerical_scope.
Notation "a + b" := (Aadd a b) (at level 50, left associativity): numerical_scope.
Notation "a - b" := (Aminus a b) (at level 50, left associativity): numerical_scope.
Notation "a * b" := (Amul a b) (at level 40, left associativity): numerical_scope.
Notation "- a" := (Aopp a) (at level 35, right associativity): numerical_scope.
Notation "a <= b" := (Ale a b) (at level 70, no associativity): numerical_scope.
Notation "a > b" := (~Ale a b) (at level 70, no associativity): numerical_scope.
Notation "a >= b" := ((b <= a)%numerical) (at level 70, no associativity, only parsing): numerical_scope.
Notation "a < b" := ((b > a)%numerical) (at level 70, no associativity, only parsing): numerical_scope.



Instance Inhab_num `{Numerical A} : Inhabited A:=
{repr := 0%numerical}.
Open Local Scope numerical_scope.

Section WITHA.
  Context A {Num_A: Numerical A}.
  Implicit Type a:A.
  Lemma Amul_A0_l: forall a, 0 * a = 0.
  Proof.
    intros. rewrite Amul_comm. apply Amul_A0_r.
  Qed.

  Lemma Aadd_A0_l: forall a, 0 + a = a.
  Proof.
    intros. rewrite Aadd_comm. apply Aadd_A0_r.
  Qed.

  Lemma Amul_A1_l: forall a, 1 * a = a.
  Proof.
    intros. rewrite Amul_comm. apply Amul_A1_r.
  Qed.

  Lemma Aopp_eq_compat: forall a1 a2,
    -a1 = -a2 <-> a1 = a2.
  Proof.
    intros *.
    split; intros; subst; auto.
    rewrite <- (Aopp_involutive a1). rewrite <- (Aopp_involutive a2).
    f_equal. auto.
  Qed.

  Lemma Aopp_mul_distr_r: forall a1 a2, -(a1 * a2) = a1 * - a2.
  Proof.
    intros a1 a2.
    rewrite Amul_comm. rewrite Aopp_mul_distr_l. apply Amul_comm.
  Qed.

  Lemma Amul_add_distr_l a1 a2 a3: (a1 + a2) * a3= 
    (a1 * a3) + (a2 * a3).
  Proof.
    rewrite Amul_comm. rewrite Amul_add_distr_r.
    f_equal; apply Amul_comm.
  Qed.

  (* same lemma, but with one of the multiplication in the result
     commutated *)
  Lemma Amul_add_distr_r_l a1 a2 a3: Amul a3 (Aadd a1 a2) = 
    Aadd (Amul a3 a1) (Amul a2 a3).
  Proof.
    rewrite Amul_add_distr_r. f_equal. apply Amul_comm.
  Qed.

  Lemma Amul_add_distr_l_r a1 a2 a3: Amul (Aadd a1 a2) a3= 
    Aadd (Amul a1 a3) (Amul a3 a2).
  Proof.
    rewrite Amul_add_distr_l. f_equal. apply Amul_comm.
  Qed.

    

  Lemma Ale_neq_lt: forall a1 a2, a1 <= a2 -> a1 <> a2 -> a1 < a2.
  Proof.
    intros * LE DIFF.
    destruct (Ale_dec a2 a1); auto.
    pose proof (Ale_antisym _ _ LE a). contradiction.
  Qed.
  
  Lemma Agt_min: forall a1 a2, a1 > a2 -> Amin a1 a2 = a2.
  Proof.
    intros * GT.
    rewrite Amin_comm. apply Ale_min.
    apply Agt_le. assumption.
  Qed.

  Lemma Amin_le1: forall a1 a2, Amin a1 a2 <= a1.
  Proof.
    intros.
    destruct' (Ale_dec a1 a2).
    Case "a1 <= a2".
      rewrite Ale_min; auto.
      apply Ale_preorder.
    Case "a1 > a2".
      rewrite Agt_min; auto.
      apply Agt_le; auto.
  Qed.
  Lemma Amin_le2: forall a1 a2, Amin a1 a2 <= a2.
  Proof.
    intros. rewrite Amin_comm. apply Amin_le1.
  Qed.

  Lemma Amin_or: forall a1 a2, Amin a1 a2 = a1 \/ Amin a1 a2 = a2.
  Proof.
    intros.
    destruct' (Ale_dec a1 a2).
    Case "a1 <= a2".
      rewrite Ale_min; auto.
    Case "a1 > a2".
      rewrite Agt_min; auto.
  Qed.


  Lemma Agt_max: forall a1 a2, a1 > a2 -> Amax a1 a2 = a1.
  Proof.
    intros * GT.
    rewrite Amax_comm. apply Ale_max.
    apply Agt_le. assumption.
  Qed.

  Lemma Amax_ge1: forall a1 a2, Amax a1 a2 >= a1.
  Proof.
    intros.
    destruct (Ale_dec a1 a2).
    rewrite Ale_max; auto.
    rewrite Agt_max; auto.
    apply Ale_preorder.
  Qed.

  Lemma Amax_ge2: forall a1 a2, Amax a1 a2 >= a2.
  Proof.
    intros. rewrite Amax_comm. apply Amax_ge1.
  Qed.

  Lemma Amax_or: forall a1 a2, Amax a1 a2 = a1 \/ Amax a1 a2 = a2.
  Proof.
    intros.
    destruct (Ale_dec a1 a2).
    rewrite Ale_max; auto.
    rewrite Agt_max; auto.
  Qed.


  Definition Amin_list (l: not_empty_list A) :=
    fold_left Amin (snd l) (fst l).

  Remark fold_left_Amin_le: forall l a, fold_left Amin l a <= a.
  Proof.
    induction' l; simpl in *; intros.

    Case "nil".
    reflexivity.

    Case "cons".
    etransitivity; eauto. apply Amin_le1.
  Qed.

  Remark fold_left_Amin_le_compat: forall l a1 a2, a1 <= a2 ->
    fold_left Amin l a1 <= fold_left Amin l a2.
  Proof.
    induction' l; simpl.

    Case "nil".
    dintuition.

    Case "cons".
    intros * LE.
    apply IHl.
    destruct (Ale_dec a1 a); [rewrite Ale_min | rewrite Agt_min]; auto;
      (destruct (Ale_dec a2 a); [rewrite Ale_min | rewrite Agt_min]); auto.
    apply Agt_le in n. assert (a = a2); [| subst; reflexivity].
    apply Ale_antisym; auto. etransitivity; eauto.
    reflexivity.
  Qed.



  Lemma Amin_list_le_forall l: not_empty_list_forall (fun x => Amin_list l <= x) l.
  Proof.
    unfold*.
    constructor.
    apply fold_left_Amin_le.

    destruct l as [a l]. unfold Amin_list. simpl.
    induction' l.
    Case "nil".
    constructor.

    Case "cons".
    simpl in *. repeat constructor.
    etransitivity.
    apply fold_left_Amin_le. simpl in *. apply Amin_le2.
    eapply list_forall_imply; [|eauto].
    simpl.
    unfold Amin_list.
    intros. etransitivity; eauto.
    apply fold_left_Amin_le_compat. apply Amin_le1.
  Qed.

  Lemma le_forall_le_Amin_list l a':
    not_empty_list_forall (fun x => a' <= x) l ->
    a' <= Amin_list l.
  Proof.
    unfold*.
    destruct l as [a l].
    unfold Amin_list. simpl.
    intro. inv H.
    revert dependent a. revert H3.
    induction' l; intros LFA * LEQ; simpl.

    Case "nil".
    assumption.

    Case "cons".
    inv LFA.
    apply IHl; auto.
    
    destruct (Ale_dec a0 a); [rewrite Ale_min | rewrite Agt_min]; auto.
  Qed.

  Lemma Amin_list_In l:
    Amin_list l = fst l \/ In (Amin_list l) (snd l).
  Proof.
    destruct l as [a l].
    unfold Amin_list.
    simpl. revert a.
    induction' l as [| a' l'].
    Case "nil".
      simpl. intros a. auto.

    Case "cons a' l'".
      intros a.
      simpl.
      destruct (Amin_or a a');
        rewrite H; edestruct (IHl'); eauto.
  Qed.


  Definition Amax_list (l: not_empty_list A) :=
    fold_left Amax (snd l) (fst l).

  Lemma fold_left_Amax_ge: forall l a, fold_left Amax l a >= a.
  Proof.
    induction' l; simpl in *; intros.

    Case "nil".
    reflexivity.

    Case "cons".
    etransitivity; [| apply IHl].
    apply Amax_ge1.
  Qed.

  Lemma fold_left_Amax_le_compat: forall l a1 a2, a1 <= a2 ->
    fold_left Amax l a1 <= fold_left Amax l a2.
  Proof.
    induction' l as [|a l']; simpl.

    Case "nil".
    dintuition.

    Case "cons a l'".
    intros * LE.
    apply IHl'.
    destruct (Ale_dec a1 a); [rewrite Ale_max | rewrite Agt_max]; auto;
      (destruct (Ale_dec a2 a); [rewrite Ale_max | rewrite Agt_max]); auto.
    reflexivity.

    apply Agt_le in n. auto.

    apply Agt_le in n. etransitivity; eauto.
  Qed.



  Lemma Amax_list_ge_forall l: not_empty_list_forall (fun x => x <= Amax_list l) l.
  Proof.
    unfold*.
    destruct l as [a l]. unfold Amax_list. simpl.
    constructor.
    apply fold_left_Amax_ge.

    induction' l.
    Case "nil".
    constructor.

    Case "cons".
    simpl. repeat constructor.
    etransitivity; [|apply fold_left_Amax_ge].
    apply Amax_ge2.

    eapply list_forall_imply; [|eauto].
    simpl.
    unfold Amax_list.
    intros. etransitivity; eauto.
    apply fold_left_Amax_le_compat. apply Amax_ge1.
  Qed.

  Lemma ge_forall_ge_Amax_list l a':
    not_empty_list_forall (fun x => a' >= x) l ->
    a' >= Amax_list l.
  Proof.
    unfold*.
    destruct l as [a l].
    unfold Amax_list.
    intro. inv H.
    revert dependent a. revert H3.
    simpl.
    induction' l; intros LFA * LEQ; simpl.

    Case "nil".
    assumption.

    Case "cons".
    inv LFA.
    apply IHl; auto.

    destruct (Ale_dec a0 a); [rewrite Ale_max | rewrite Agt_max]; auto.
  Qed.

  Lemma Amax_list_In l:
    Amax_list l = fst l \/ In (Amax_list l) (snd l).
  Proof.
    destruct l as [a l].
    unfold Amax_list.
    simpl. revert a.
    induction' l as [| a' l'].
    Case "nil".
      simpl. intros a. auto.

    Case "cons a' l'".
      intros a.
      simpl.
      destruct (Amax_or a a');
        rewrite H; edestruct (IHl'); eauto.
  Qed.

End WITHA.
(*Implicit Arguments A0_abs_l [[A] [Num_A]].
Implicit Arguments A0_neutral_l [[A] [Num_A]].
Implicit Arguments A1_neutral_l [[A] [Num_A]].
Implicit Arguments Aopp_distr_mult_r [[A] [Num_A]].
*)
 
Hint Rewrite @Amul_A0_l @Amul_A0_r @Aadd_A0_l @Aadd_A0_r
  @Amul_A1_l @Amul_A1_r @Aopp_involutive @Aopp_A0 @Aopp_eq_compat: vect.

Hint Rewrite <-
  @Aopp_add_distr @Aopp_mul_distr_l @Aopp_mul_distr_r
  @Amul_add_distr_l @Amul_add_distr_l_r @Amul_add_distr_r @Amul_add_distr_r_l 
  @Amul_assoc @Aadd_assoc
  : vect.

Tactic Notation "simpl_vect" :=
  autorewrite with vect.
Tactic Notation "simpl_vect" "in" "*" :=
  autorewrite with vect in *.
Tactic Notation "simpl_vect" "in" hyp(H) :=
  autorewrite with vect in H.
Tactic Notation "simpl_vect" "in" "*" "|-" :=
  autorewrite with vect in * |-.

Tactic Notation "unfold_vect" :=
  autounfold with vect.
Tactic Notation "unfold_vect" "in" "*" :=
  autounfold with vect in *.
Tactic Notation "unfold_vect" "in" hyp(H) :=
  autounfold with vect in H.
Tactic Notation "unfold_vect" "in" "*" "|-" :=
  autounfold with vect in * |-.


Instance Numerical_Z: Numerical Z :=
{ A0 := 0%Z;
  A1 := 1%Z;
  Aopp := Zopp;
  Aadd := Zplus;
  Aminus := Zminus;
  Amul := Zmult;
  Ale := Zle;
  Amax := Zmax;
  Amin := Zmin;
  Aceild := ceildZ;
  Afloord := floordZ}.
Proof.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - apply Z_le_dec.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
  - intros; lia.
Defined.



Module IntEqDec <: EQUALITY_TYPE.
  Definition t := int.
  Global Instance EqDec_t: EqDec int :=
  { eq_dec := Int.eq_dec}.
End IntEqDec.

Definition Ile i1 i2 := Int.signed i1 <= Int.signed i2.
Lemma Ile_dec i1 i2: {Ile i1 i2} + {~ Ile i1 i2}.
  unfold Ile. apply Z_le_dec.
Qed.

Definition Imax i1 i2 :=
  if Ile_dec i1 i2 then i2 else i1.
Definition Imin i1 i2 :=
  if Ile_dec i1 i2 then i1 else i2.

Definition Iceild i1 i2 :=
  do z <- ceildZ (Int.signed i1) (Int.signed i2);
  Some (Int.repr z).
Definition Ifloord i1 i2 :=
  do z <- floordZ (Int.signed i1) (Int.signed i2);
  Some (Int.repr z).


Instance Numerical_Int: Numerical int :=
{ A0 := Int.zero;
  A1 := Int.one;
  Aopp := Int.neg;
  Aadd := Int.add;
  Aminus := Int.sub;
  Amul := Int.mul;
  Ale := Ile;
  Amax := Imax;
  Amin := Imin;
  Aceild := Iceild;
  Afloord := Ifloord
}.
Proof.
  apply Int.add_commut.
  apply Int.mul_commut.
  apply Int.add_zero.
  apply Int.mul_zero.
  apply Int.mul_one.
  apply Int.neg_involutive.
  apply Int.neg_zero.
  intros. rewrite Int.neg_add_distr. reflexivity.

  intros.
  rewrite Int.neg_mul_distr_l. reflexivity.

  intros.
  rewrite Int.mul_add_distr_r. reflexivity.

  symmetry. apply Int.mul_assoc.

  symmetry. apply Int.add_assoc.

  intros. apply Z_le_dec.

  constructor.
    intro. unfold Ile. simpl. lia.
    intro. unfold Ile. simpl. intros. lia.
  unfold Ile; simpl; intros.
  rewrite <- (Int.repr_signed a1).
  rewrite <- (Int.repr_signed a2).
  f_equal. lia.

  unfold Ile; simpl; intros; lia.

  unfold Imin.
  intros.
  repeat match goal with | |- context[if ?cond then _ else _] => destruct cond end;
  unfold Ile in *; simpl in *; auto;
  rewrite <- (Int.repr_signed a1);
  rewrite <- (Int.repr_signed a2); f_equal; lia.
  

  unfold Imin.
  intros.
  repeat match goal with | |- context[if ?cond then _ else _] => destruct cond end;
  auto. contradiction.


  unfold Imax.
  intros.
  repeat match goal with | |- context[if ?cond then _ else _] => destruct cond end;
  unfold Ile in *; simpl in *; auto;
  rewrite <- (Int.repr_signed a1);
  rewrite <- (Int.repr_signed a2); f_equal; lia.

  unfold Imax.
  intros.
  repeat match goal with | |- context[if ?cond then _ else _] => destruct cond end;
  auto. contradiction.
Defined.


Module Type NUMERICAL.
  Parameter Num: Type.
  Parameter Numerical_Num: Numerical Num.
End NUMERICAL.

Module ZNum<:NUMERICAL.
  Definition Num := Z.
  Definition Numerical_Num := Numerical_Z.
End ZNum.

Module IntNum<:NUMERICAL.
  Definition Num := int.
  Definition Numerical_Num := Numerical_Int.
End IntNum.



(* a pseudo vector is a vector without it's lenght *)

Definition Pseudo_Vector A := list A.
Hint Unfold Pseudo_Vector: aliases.

Section VECTORS.
Context A {Num_A: Numerical A}.
Implicit Type (a x y z:A).
Variable n: nat.
Definition Vector := {l:Pseudo_Vector A| length l = n}.

(* functions starting with PV work on pseudo vectors, and those
   starting with V on vectors *)

Implicit Type v: Vector.

Lemma PVeq_Veq: forall v1 v2,
  `v1 = `v2 -> v1 = v2.
Proof.
  intros * EQ.
  destruct v1, v2. simpl in *.
  subst x. f_equal.
  (* UIP would be enough, but, mmh... *)
  apply proof_irrelevance.
Qed.

Ltac dest_vect v :=
  try apply PVeq_Veq;
  let Lv := fresh "L" v in
  destruct v as [v Lv].


Fixpoint PVprod va1 va2 : A :=
  match va1, va2 with
    | nil, _
    | _, nil => 0
    | x1 :: va1', x2 :: va2' =>
      (x1 * x2) + (PVprod va1' va2')
  end.


(*Ltac dest_vect v :=
  let av := fresh "a" v in
  let avLENGTH := fresh av "LENGTH" in
  destruct v as [av avLENGTH].*)

Ltac dest_vects :=
  repeat
  match goal with
    | v : Vector |- _ =>
      dest_vect v
  end; unfold_vect in *; simpl.

Program Definition Vprod v1 v2 : A :=
  PVprod v1 v2.

Hint Unfold Vprod: vect.

Notation "〈 v1 , v2 〉" := (Vprod v1 v2) (at level 0,
  format "〈 v1 ,  v2 〉").

Lemma Vprod_comm: forall v1 v2, 〈v1, v2 〉= 〈v2, v1 〉.
Proof.
  intros *.
  dest_vects. clear Lv1 Lv2. revert v2.
  induction v1; destruct v2; simpl; try reflexivity.
  f_equal.
    apply Amul_comm.
    auto.
Qed.

Hint Rewrite repeat_length: vect.

Program Definition Vrepeat a : Vector:=
  repeat n a.
Next Obligation. apply repeat_length. Qed.

Hint Unfold Vrepeat: vect.


Program Definition Vopp v : Vector:= List.map Aopp v.
Next Obligation.
  dest_vect v. simpl. rewrite map_length. auto.
Qed.

Hint Unfold Vopp: vect.

Notation "-- v" := (Vopp v) (at level 35, right associativity).

Lemma Vopp_involutive: forall v, -- -- v = v.
Proof.
  intros *.
  dest_vects. clear Lv.
  induction v; auto; simpl; simpl_vect; congruence.
Qed.

Lemma Vopp_prod_distr_l:
  forall v1 v2,  - 〈v1, v2〉= 〈-- v1, v2〉.
Proof.
  intros. symmetry. dest_vects. simpl.
  clear Lv1 Lv2.
  revert v2.
  induction v1; destruct v2; simpl; intros; simpl_vect; auto.
  rewrite IHv1. simpl_vect. reflexivity.
Qed.

Lemma Vopp_prod_distr_r:
  forall v1 v2, - 〈v1, v2〉= 〈 v1, -- v2〉.
Proof.
  intros. symmetry. dest_vects.
  clear Lv1 Lv2.
  revert v1.
  induction v2; destruct v1; simpl; intros; simpl_vect; auto.
  rewrite IHv2. simpl_vect. reflexivity.
Qed.

Hint Rewrite <- @Vopp_prod_distr_r @Vopp_prod_distr_l: vect.


Program Definition Vmul a v : Vector:=
  map (fun a' => a * a') v.
Next Obligation.
  dest_vect v.
  simpl. rewrite map_length. auto.
Qed.

Notation "z · v" := (Vmul z v) (at level 45).
Hint Unfold Vmul Vprod: vect.

Lemma Vmul_prod_distr_l: forall a v1 v2, 
 a * 〈v1, v2〉= 〈a · v1, v2〉.
Proof.
  intros *. symmetry. dest_vects. clear.
  revert v2.
  induction v1; destruct v2; intros; simpl_vect in *; auto.
  simpl.
  rewrite IHv1. simpl_vect. reflexivity.
Qed.

Lemma Vmul_prod_distr_r: forall a v1 v2, 
 a * 〈v1, v2〉= 〈v1, a · v2〉.
Proof.
  intros *. symmetry. dest_vects. clear.
  revert v1.
  induction v2; destruct v1; intros; simpl_vect in *; auto.
  simpl.
  rewrite IHv2.
  replace (a1 * (a * a0)) with (a * (a1 * a0)).
  simpl_vect. reflexivity.
  rewrite Amul_assoc. rewrite Amul_comm. rewrite Amul_assoc. rewrite Amul_comm.
  f_equal. apply Amul_comm.
Qed.


Hint Rewrite <- @Vmul_prod_distr_l @Vmul_prod_distr_r: vect.



Fixpoint PVadd av1 av2 :=
  match av1, av2 with
    | nil, _
    | _, nil => nil
    | z1::av1', z2::av2' =>
      (z1 + z2) :: PVadd av1' av2'
  end.

Program Definition Vadd v1 v2 : Vector :=
  PVadd v1 v2.
Next Obligation.
  dest_vects.
  generalize dependent v2. revert Lv1. revert n.
  induction v1; destruct v2; simpl; intros; auto.
  simpl in Lv1. destruct n; auto.
Qed.

Notation "v1 ⊹ v2" := (Vadd v1 v2) (at level 50).

Hint Unfold Vadd: vect.


Lemma Vprod_add_distr_l:
  forall v1 v2 v3,
    〈v1 ⊹ v2,  v3〉 = 〈v1, v3〉 + 〈v2, v3〉.
Proof.
  intros. dest_vects.
  generalize dependent v2; generalize dependent v1; revert Lv3; revert n.
  induction v3; intros; destruct v1; destruct v2; simpl in *;
    subst; auto. simpl_vect. reflexivity.
  inv Lv1; inv Lv2.
  erewrite IHv3; eauto; try omega.

  rewrite Amul_comm. rewrite Amul_add_distr_r_l. rewrite Amul_comm.
  simpl_vect. f_equal.
  repeat rewrite Aadd_assoc. repeat rewrite <- (Aadd_comm (PVprod v2 v3)).
  f_equal. apply Aadd_comm.
Qed.

Lemma Vprod_add_distr_r:
  forall v1 v2 v3,
    〈v3,  v1 ⊹ v2〉 = 〈v3, v1〉 + 〈v3, v2〉.
Proof.
  intros. 
  repeat rewrite (Vprod_comm v3). apply Vprod_add_distr_l.
Qed.

Hint Rewrite @Vprod_add_distr_l @Vprod_add_distr_r: vect.



(* caml code should *never* return directly vectors but always go
   through make_vector to check the length test *)

(* checks that pv is of lenght n *)
Fixpoint is_of_length_aux (n: nat) (pv: Pseudo_Vector A) :=
  match n, pv with
    | O, nil => true
    | _, nil
    | O, _ => false
    | S n', _ :: pv' => is_of_length_aux n' pv'
  end.

  Program Definition is_of_length n (pv: Pseudo_Vector A)
    : {length pv = n}+{length pv <> n}:=
    match is_of_length_aux n pv with
      | true => left _
      | false => right _
    end.
  Next Obligation.
    revert dependent pv.
    induction n0; intros; destruct pv; simpl in *; auto.
  Qed.
  Next Obligation.
    revert dependent pv.
    induction n0; intros; destruct pv; simpl in *; auto.
  Qed.

  Program Definition make_vector (pv: Pseudo_Vector A) : option Vector :=
    if is_of_length n pv then
      Some pv
    else
      None.
    
End VECTORS.
Notation "〈 v1 , v2 〉" := (Vprod v1 v2) (at level 0,
  format "〈 v1 ,  v2 〉").
Notation "-- v" := (Vopp v) (at level 35, right associativity).
Notation "z · v" := (Vmul z v) (at level 45).
Notation "v1 ⊹ v2" := (Vadd v1 v2) (at level 50).



  Lemma make_vector_open n `(l: list A) v:
    make_vector n l = Some v ->
    `v = l.
  Proof.
    intro MAKE.
    unfold make_vector in MAKE.
    destruct (is_of_length n l); clean.
  Qed.

Hint Unfold Vprod Vrepeat Vopp Vmul Vadd:vect.
Hint Rewrite @repeat_length @Vopp_involutive @Vprod_add_distr_l @Vprod_add_distr_r: vect.
Hint Rewrite <- @Vopp_prod_distr_r @Vopp_prod_distr_l
  @Vmul_prod_distr_l @Vmul_prod_distr_r @Vprod_add_distr_l
  @Vprod_add_distr_r: vect.

Ltac dest_vect v :=
  let Lv := fresh "L" v in
  destruct v as [v Lv].

Ltac dest_vects :=
  try apply PVeq_Veq;
  repeat
  match goal with
    | v : Vector _ _ |- _ =>
      dest_vect v
  end; unfold_vect in *; simpl.

Instance Inhab_vect `{Inhabited A} n : Inhabited (Vector A n) :=
{repr := Vrepeat n repr}.


Definition V0 `{Numerical Num} n : Vector Num n := Vrepeat n 0.
Hint Unfold V0: vect.


Lemma Vprod_V0_l `{Numerical Num} n (v: Vector Num n):〈V0 n, v〉= 0.
Proof.
  dest_vects. revert dependent v.
  induction n; intros v Lv; destruct v; clean.
  simpl in *. simpl_vect. auto.
Qed.

Hint Rewrite @Vprod_V0_l: vect.

Lemma Vprod_V0_r `{Numerical Num} n (v: Vector Num n): 〈v, V0 n〉= 0.
Proof.
  intros *. dest_vects. revert dependent v.
  induction n; intros v Lv; destruct v; clean.
  simpl in *. simpl_vect. auto.
Qed.

Hint Rewrite @Vprod_V0_r: vect.

Program Definition Vmap {A B:Type} {n} (f:A -> B) (v: Vector A n) : Vector B n :=
  List.map f v.
Next Obligation.
  destruct v. simpl.
  rewrite List.map_length. auto.
Qed.

Unset Implicit Arguments.

Program Definition ovector_of_olist {A} n (ol: option (list A))
  (H: forall l, ol = Some l -> length l = n): option (Vector A n) :=
match ol with
  | None => None
  | Some l => Some l
end.
Lemma simpl_ovector_of_olist: forall A n (ol: option (list A)) H (v: Vector A n), 
  ol = Some (`v) -> @ovector_of_olist A n ol H = Some v.
Proof.
  intros.
  subst ol.
  simpl. f_equal. apply PVeq_Veq. auto.
Qed.
Set Implicit Arguments.


Implicit Arguments ovector_of_olist [[A] n].
Program Definition OVmap {A B: Type} {n}
  (f: A -> option B) (v: Vector A n) : option (Vector B n) :=
  ovector_of_olist (mmap f v) _ .
Next Obligation.
  dest_vect v. simpl in *.
  revert dependent n. revert dependent l.
  induction v; simpl; intros.
  clean.
  destruct n as [| n]. auto.
  monadInv H. simpl. eauto.
Defined.



Program Definition Vcons {A:Type} {n} a (v: Vector A n) : Vector A (S n) :=
  a :: v.
Next Obligation.
  dest_vects. congruence.
Qed.

Hint Unfold Vcons: vect.

Notation " x ::: v" := (Vcons x v) (at level 45, right associativity).

Lemma Vprod_Vcons `{Numerical Num} n (x y: Num) (v1 v2: Vector Num n):
  〈x:::v1, y:::v2〉= (x * y + 〈v1, v2〉)%numerical.
Proof.
  reflexivity.
Qed.
Hint Rewrite @Vprod_Vcons: vect.


Program Definition Vhd {n} `(v: Vector A (S n)): A :=
  match v with
    | nil => !
    | a :: _ => a
  end.
Next Obligation.
  dest_vects. simpl in *. clean.
Qed.

Hint Unfold Vhd: vect.

Program Definition Vtail {A:Type} {n} (v: Vector A (S n)): Vector A n :=
  unsafe_tail v.
Next Obligation.
  destruct v as [v Lv].
  simpl.
  destruct v; inv Lv.
  simpl. reflexivity.
Qed.

Hint Unfold Vtail: vect.

Lemma Vcons_hd_tail {n} `(v: Vector A (S n)):
  Vcons (Vhd v) (Vtail v) = v.
Proof.
  apply PVeq_Veq.
  dest_vects.
  unfold Vcons, Vhd, Vtail; simpl.
  destruct v; inv Lv; simpl. reflexivity.
Qed.

Hint Rewrite @Vcons_hd_tail: vect.
Tactic Notation "Vdestruct" constr(v) "as" ident(hd) ident(tl) :=
  let H := fresh in
  let v' := fresh v in
  rename v into v';
  pose proof (Vcons_hd_tail v') as H;
  remember_no_eq (Vhd v') as hd;
  remember_no_eq (Vtail v') as tl;
  rewrite <- H in *;
  clear H; clear v'.

Program Definition Vapp {A n p} (v1 : Vector A n) (v2 : Vector A p) : Vector A (n + p) :=
  v1 ++ v2.
Next Obligation.
  dest_vects. subst. apply app_length.
Qed.

Hint Unfold Vapp: vect.

Notation "v1 +++ v2" := (Vapp v1 v2) (at level 65, right associativity).

Lemma PVeq_Veq_rew: forall A n (v1 v2 : Vector A n), `v1 = `v2 -r> v1 = v2.
Proof. constructor. apply PVeq_Veq. Qed.

Hint Rewrite @PVeq_Veq_rew: clean.


Lemma V0_Vapp `{Numerical Num} n (v: Vector Num n) :
  V0 0 +++ v = v.
Proof.
  apply PVeq_Veq.
  unfold V0, Vapp. simpl. reflexivity.
Qed.
Hint Rewrite @V0_Vapp: vect.





Lemma Vcons_app_distr:
  forall A n p e (vn: Vector A n) (vp: Vector A p),
    e ::: (vn +++ vp) = (e ::: vn) +++ vp.
Proof. 
  intros. apply PVeq_Veq. simpl. reflexivity.
Qed.

Lemma VJMeq: forall A m n (v1: Vector A m) (v2: Vector A n),
  `v1 = `v2 -> v1 ~= v2.
Proof.
  intros.
  destruct v1 as [v1 Hv1].
  destruct v2 as [v2 Hv2].
  simpl in *.
  clean.
Qed.

Lemma Vapp_assoc:
  forall A m n p (v1: Vector A m) (v2: Vector A n) (v3 : Vector A p),
    v1 +++ (v2 +++ v3) ~= (v1 +++ v2) +++ v3.
Proof.
  intros.
  apply VJMeq.
  simpl. apply app_assoc.
Qed.

Program Definition Vsnoc {A:Type} {n} (v: Vector A n) a : Vector A (S n) :=
  v ++ [a].
Next Obligation.
  dest_vects. rewrite app_length.
  simpl. omega.
Qed.

Notation " v :::: x" := (Vsnoc v x) (at level 71, left associativity).

Hint Unfold Vsnoc: vect.

Lemma Vprod_snoc: forall `{Numerical A} n (v1 v2: Vector A n) (a1 a2: A),
〈v1 :::: a1, v2::::a2〉 = (〈v1, v2〉 + a1 * a2)%numerical.
Proof.
  intros.
  dest_vects.
  revert dependent v1. revert dependent v2.
  induction' n; intros.
  Case "O".
    destruct v1; inversion Lv1.
    destruct v2; inversion Lv2.
    simpl. simpl_vect. reflexivity.

  Case "S".
    destruct v1; inv Lv1.
    destruct v2; inv Lv2.
    simpl. simpl_vect. f_equal. eauto.
Qed.
Hint Rewrite @Vprod_snoc: vect.

Lemma PVprod_repeat_0: forall n v, 
  PVprod (repeat n 0%Z) v = 0%Z.
Proof.
  induction' n; intros; simpl; auto.
  destruct v; auto.
Qed.
Hint Rewrite @PVprod_repeat_0: vect.


Program Definition Vdrop {A p} n (v: Vector A p) : Vector A (p - n) :=
  list_drop n v.
Next Obligation.
  dest_vect v. simpl.
  revert dependent p. revert v.
  induction n; simpl; intros.
  replace (p - O)%nat with p by omega.
  destruct v; auto.
  destruct v; simpl in *; subst; simpl.
  reflexivity.

  erewrite IHn; reflexivity.
Qed.

Hint Unfold Vdrop: vect.

(* the _p means that the type of the original vector is given in a plus form*)

Program Definition Vtake_p {A} n {p} (vect: Vector A (n + p)): Vector A n:=
  list_take n vect.
Next Obligation.
  dest_vects.
  revert dependent vect.
  induction' n as [|n']; intros.
  Case "O".
    simpl. reflexivity.
  Case "S n'".
    simpl. destruct' vect.
    SCase "nil".
      inv Lvect.
    SCase "cons".
      simpl in *.
      rewrite IHn'. reflexivity.
      congruence.
 Qed.

Hint Unfold Vtake_p: vect.

Program Definition Vdrop_p {A} n {p} (vect: Vector A (n + p)): Vector A p:=
  Vdrop n vect.
Next Obligation.
  dest_vects.
  revert dependent vect.
  induction' n as [|n']; intros.
  Case "O".
    simpl in *. assumption.
  Case "S n'".
    destruct' vect.
    SCase "nil".
      inv Lvect.
    SCase "cons".
      inv Lvect.
      simpl.
      eauto.
Qed.

Hint Unfold Vdrop_p: vect.

Lemma Vapp_take_drop: forall A n p (v: Vector A (n + p)%nat),
  Vtake_p n v +++ Vdrop_p n v = v.
Proof.
  intros.
  apply PVeq_Veq. simpl. apply list_take_drop.
Qed.
Hint Rewrite @Vapp_take_drop: vect.
    

Lemma Vtake_p_app: forall A n p (vn : Vector A n) (vp: Vector A p),
  Vtake_p n (vn +++ vp) = vn.
Proof.
  intros.
  apply PVeq_Veq. simpl.
  dest_vects. subst.
  apply list_take_app.
Qed.

Lemma Vdrop_p_app: forall A n p (vn : Vector A n) (vp: Vector A p),
  Vdrop_p n (vn +++ vp) = vp.
Proof.
  intros.
  apply PVeq_Veq. simpl.
  dest_vects. subst.
  apply list_drop_app.
Qed.

Hint Rewrite @Vtake_p_app @Vdrop_p_app: vect.



Definition Vnth `{Inhabited A} n (v: Vector A n) x: A :=
  nth x (`v) repr.

Hint Unfold Vnth: vect.

Lemma Vnth_inj `{INHAB: Inhabited A} n (v1 v2: Vector A n):
  (forall x, (x < n)%nat -> Vnth v1 x = Vnth v2 x) -> v1 = v2.
Proof.
  intro SAMEACC.
  dest_vects.
  simpl in *.
  rewrite <- Lv2 in *. clear dependent n.
  revert dependent v2.
  induction v1; intros.
  destruct v2; auto; inv Lv1.

  destruct v2; inv Lv1.
  erewrite IHv1; eauto.

  specialize (SAMEACC O); simpl in SAMEACC.
  f_equal. apply SAMEACC. auto with arith.

  intros.
  apply (SAMEACC (S x)). simpl.  auto with arith.
Qed.

  Fixpoint Vnth_at_val `{Numerical A} dim n (a:A) : Vector A dim :=
    match dim with
    | O => V0 0
    | S dim' =>
      match n with
      | O => a ::: V0 dim'
      | S n' => 0 ::: (Vnth_at_val dim' n' a)
      end
    end.


  Lemma Vnth_S_cons `{Inhabited A} dim (a:A) (v:Vector A dim) n:
    Vnth (a:::v) (S n) = Vnth v n.
  Proof.
    unfold Vnth, Vcons. simpl. reflexivity.
  Qed.
  
  Lemma Vnth_0 `{Inhabited A} dim (a:A) (v:Vector A dim):
    Vnth (a ::: v) O = a.
  Proof.
    unfold Vnth. simpl. reflexivity.
  Qed.

  Hint Rewrite @Vnth_S_cons @Vnth_0: vect.

  Lemma Vnth_at_val_prod A (NumA: Numerical A) dim (v:Vector A dim) n z:
    〈Vnth_at_val dim n z, v〉= z * (Vnth v n).
  Proof.
    revert n; induction' dim as [|dim]; intros; destruct' n as [|n]; simpl; simpl_vect.
    Case "O"; SCase "O". 
      dest_vects. destruct v; simpl in *; clean. simpl_vect. reflexivity.
    Case "O"; SCase "S n".
      dest_vects. destruct v; simpl in *; clean. simpl_vect. reflexivity.
    Case "S dim"; SCase "O".
      rewrite <- (Vcons_hd_tail v). simpl_vect. Vdestruct v as z1 v.
      rewrite Vprod_Vcons. rewrite Vprod_V0_l. simpl_vect. reflexivity.
    Case "S dim"; SCase "S n".
      Vdestruct v as z1 v. simpl_vect. auto. 
  Qed.




Definition Vcast {A} {n} p (EQUAL: n = p) (v: Vector A n) : Vector A p.
Proof.
  rewrite EQUAL in v. assumption.
Defined.
Implicit Arguments Vcast [[A] [n]].

Notation "( v <:: 'Vector' p )" := (Vcast p _ v).


Lemma Vcast_id: forall A n p EQUAL (v: Vector A n), ` (Vcast p EQUAL v) = `v.
Proof.
  intros. subst. reflexivity.
Qed.

Hint Rewrite @Vcast_id: vect.

Lemma Vcast_access: forall `{Inhabited A} n p EQUAL (v: Vector A n) i,
  Vnth (Vcast p EQUAL v) i = Vnth v i.
Proof.
  intros. unfold Vnth. rewrite Vcast_id. reflexivity.
Qed.

Hint Rewrite @Vcast_access: vect.

Lemma Vcast_JMeq: forall A n p EQUAL (v: Vector A n), (Vcast p EQUAL v) ~= v.
Proof.
  intros. apply VJMeq. apply Vcast_id.
Qed.


Lemma Vprod_app: forall `{Numerical A} n p (v1 v1': Vector A n) (v2 v2': Vector A p),
  〈v1 +++ v2, v1' +++ v2'〉 = (〈v1, v1'〉 + 〈v2, v2'〉)%numerical.
Proof.
  intros.
  dest_vects.
  revert dependent v1. revert dependent v1'.
  induction' n; intros.
  Case "O".
    destruct v1; inversion Lv1.
    destruct v1'; inversion Lv1'.
    simpl. simpl_vect. reflexivity.

  Case "S".
    destruct v1; inv Lv1.
    destruct v1'; inv Lv1'.
    simpl. simpl_vect. f_equal. eauto.
Qed.

Hint Rewrite @Vprod_app: vect.


Lemma Vnth_app_1: forall `{Inhabited A} (n p: nat) (v1: Vector A n) (v2: Vector A p),
  forall i, (i < n)%nat ->
    Vnth (v1 +++ v2) i = Vnth v1 i.
Proof.
  intros *.
  dest_vects. subst. revert i.
  induction' v1 as [|x v1]; intros i INF.
  Case "nil".
    simpl in INF. inv INF.
  Case "cons x v1".
    simpl.
    destruct i; auto.
    apply IHv1. simpl in *; omega.
Qed.

Lemma Vnth_app_2: forall `{Inhabited A} (n p: nat) (v1: Vector A n) (v2: Vector A p),
  forall i,
    Vnth (v1 +++ v2) (n + i) = Vnth v2 i.
Proof.
  intros *.
  dest_vects. subst. unfold Vnth; simpl. 
  induction' v1 as [|x v1]; simpl in *; auto.
Qed.

Hint Rewrite @Vnth_app_1 using omega: vect.
Hint Rewrite @Vnth_app_2: vect.

Lemma Vnth_V0: forall n p, Vnth (V0 n) p = 0%Z.
Proof.
  unfold Vnth, V0, Vrepeat. simpl.
  intro n.
  induction n as [|n]; intros [|p]; simpl; auto.
Qed.

Lemma Vnth_cons: forall `{Inhabited A} a n (v: Vector A n) p,
  Vnth (a ::: v) (S p) = Vnth v p.
Proof.
  intros.
  unfold Vnth; dest_vects; auto.
Qed.

Lemma Vhd_cons: forall `{Inhabited A} a n (v: Vector A n),
  Vhd (a ::: v) = a.
Proof.
  dest_vects. reflexivity.
Qed.

Lemma Vtail_cons: forall A a n (v: Vector A n),
  Vtail (a ::: v) = v.
Proof.
  dest_vects. intros. apply PVeq_Veq. reflexivity.
Qed.

Hint Rewrite @Vnth_V0 @Vnth_cons @Vhd_cons @Vtail_cons: vect. 



Section MATRIX.
Variable A:Type.
Implicit Type (a:A).

(* matrix of n lines and p columns *)
Definition Matrix n p := Vector (Vector A p) n.
Implicit Type n p q: nat.

Definition Pseudo_Matrix := list (list A).


(* same as make_vectors, for matricies *)
Definition make_matrix n p (pm: Pseudo_Matrix) : option (Matrix n p) :=
  do pm2 <- mmap (make_vector p) pm;
  make_vector n pm2.


Program Definition Mprod_vect {Num_A: Numerical A} n p (m: Matrix n p) v
  : Vector A n :=
  List.map (fun v' => 〈v', v〉) (`m).
Next Obligation.
  destruct m. simpl. rewrite List.map_length. auto.
Qed.

(* access to a matrix *)
Definition Mnth_pth {Inhab_A: Inhabited A} {n p} (m: Matrix n p) (x y:nat): A:=
  Vnth (Vnth m x) y.

Lemma Mnth_pth_inj `{Inhab_A: Inhabited A} n p (m1 m2: Matrix n p):
  (forall (x y:nat), (x < n)%nat -> (y < p)%nat ->
    Mnth_pth m1 x y = Mnth_pth m2 x y) ->
  m1 = m2.
Proof.
  intro Same_acc.
  apply Vnth_inj.
  intros.
  apply Vnth_inj.
  intros.
  apply Same_acc; auto.
Qed.


End MATRIX.

Hint Unfold Mnth_pth: vect.

Fixpoint Mtranspose {A} {n p} :
  Matrix A n p -> Matrix A p n :=
  match p with
    | O => fun _ => exist (fun l  => length l = 0%nat) 
              [] eq_refl
    | S p' => fun m =>
      (Vmap Vhd m) ::: (Mtranspose (Vmap Vtail m))
  end.


(*Fixpoint Mtranspose_aux `{Inhab_A: Inhabited A} {n p} :
  matrix A n p -> list (vector A n) :=
  match p return matrix A n p -> list (vector A n) with
    | O => fun _ => nil
    | S p' => fun m =>
      (Vmap Vhd m) :: (Mtranspose_aux (Vmap Vtail m))
  end.


Program Definition transpose `{Inhab_A: Inhabited A} {n p}
  (m: matrix A n p) : matrix A p n :=
  trans_aux m.
Next Obligation.
  induction p; simpl; auto.
Qed.*)

Lemma nth0_Vhd `{Inhab_A: Inhabited A} {n}: forall (v: Vector A (S n)),
  nth 0 (`v) repr = Vhd v.
Proof.
  intros v. dest_vects.
  destruct v; unfold Vhd; simpl in *; clean.
  inv Lv.
Qed.

Lemma nth_vect0: forall A (a:A) x (v:Vector A 0),
  nth x (`v) a = a.
Proof.
  intros *. dest_vects. destruct v; inv Lv. simpl. destruct x; reflexivity.
Qed.

Lemma nth_repeat: forall A (a:A) n x,
  nth x (repeat n a) a = a.
Proof.
  induction n; destruct x; simpl; auto.
Qed.

Hint Rewrite @nth0_Vhd nth_vect0 @nth_repeat: vect.


Lemma Mtranspose_nth_pth `{Inhab_A: Inhabited A} {n p} (m: Matrix A n p):
  forall x y, Mnth_pth m x y = Mnth_pth (Mtranspose m) y x.
Proof.
  unfold Mnth_pth. unfold Vnth.

  revert dependent m.

  induction' p as [|p].

  Case "O".
  intros; simpl. rewrite nth_vect0.
  destruct y; simpl; rewrite nth_repeat; reflexivity.

  Case "S p".
  intros. simpl.
  destruct' y as [|y].

  SCase "O".
  destruct m as [m Lm].
  rewrite nth0_Vhd.
  symmetry.
  assert (@repr A Inhab_A = Vhd (Vrepeat (S p) repr)) by reflexivity.
  rewrite H at 1. simpl.
  rewrite map_nth. reflexivity.

  SCase "S y". simpl in IHp.
  rewrite <- IHp.
  clear'.
  match goal with
    | |- nth _ (` ?TERM1) _ = nth _ (` ?TERM2) _ =>
      replace TERM2 with (Vtail (TERM1)) ;
        [( fst_Case_tac "after replacement"; remember TERM1 as v)
         | fst_Case_tac "the replacement equality"; idtac]
  end.

  SSCase "after replacement".
  clear'.
  destruct v as [v Lv]. simpl.
  induction y; destruct v; simpl; auto.

  SSCase "the replacement equality".
  destruct m as [m Lm]; simpl. clear'. revert m.
  induction x; destruct m; simpl; auto;
    try solve
      [unfold Vrepeat, Vtail; simpl; f_equal; apply proof_irrelevance].
Qed.



Lemma Mtranspose_involutive `{Inhab_A: Inhabited A} {n p} (m: Matrix A n p):
  Mtranspose (Mtranspose m) = m.
Proof.
  eapply Mnth_pth_inj.
  intros * _ _.
  repeat rewrite <- Mtranspose_nth_pth. reflexivity.
Qed.



Notation "m × v" := (Mprod_vect m v) (at level 40).




Notation "'IVector'" := (Vector int).
Notation "'ZVector'" := (Vector Z).
Notation IMatrix := (Matrix int).
Notation ZMatrix := (Matrix Z).


Hint Resolve Zgt_lt.


Lemma Vprod_Vcons_Z n (v1 v2: ZVector n) (a1 a2: Z):
  〈 a1 ::: v1, a2 ::: v2〉= a1 * a2 + 〈v1, v2〉.
Proof.
  reflexivity.
Qed.

Hint Rewrite @Vprod_Vcons @Vprod_Vcons_Z: vect.

Definition Mmul_transp `{Numerical Num} {n m p} (m1: Matrix Num n m)
  (m2: Matrix Num p m) : Matrix Num n p :=
  Vmap (fun l1 => Vmap (fun c2 => 〈l1, c2〉) m2) m1.

Definition Mmul `{Numerical Num} {n m p} (m1: Matrix Num n m)
  (m2: Matrix Num m p) : Matrix Num n p :=
  Mmul_transp m1 (Mtranspose m2).


Lemma Vnth_Vmap `{Inhabited A} `{Inhabited B} n (f:A -> B) (v: Vector A n) i:
  (i < n)%nat ->
  Vnth (Vmap f v) i = f (Vnth v i).
Proof.
  unfold Vnth, Vmap. simpl.
  dest_vect v. unalias in *. simpl.
  revert dependent n. revert v.
  induction' i as [|i]; simpl; intros * LENGTH INF.
  Case "O".
    destruct v; simpl in *; auto. omegaContradiction.
  Case "S i".
    destruct v; simpl in *; auto. omegaContradiction.
    destruct n; auto. assert (length v = n) by omega.
    eapply IHi; eauto. omega.
Qed.

Lemma Vmap_cons A B n (f: A -> B) a (v : Vector A n):
  Vmap f (a ::: v) = f a ::: Vmap f v.
Proof.
  apply PVeq_Veq. unfold Vmap. simpl. auto.
Qed.

Lemma Mprod_vect_cons `{Numerical Num} n p (fst_row: Vector Num p) (m: Matrix Num n p)
  (v:Vector Num p):
  (fst_row ::: m) × v = 〈fst_row, v〉::: (m × v).
Proof.
  unfold Matrix, Mprod_vect, Vprod in *.
  dest_vects. reflexivity.
Qed.

Hint Rewrite @Vmap_cons @Mprod_vect_cons: vect.

Lemma Vect_0 {A} (v : Vector A 0):
  v = (exist (fun l : Pseudo_Vector A => length l = 0%nat) 
              [] eq_refl).
Proof.
  intros. apply PVeq_Veq. dest_vects.
  destruct v; simpl in *; clean.
Qed.




(* let's go for a triple induction proof \o/ *)
Lemma Mmul_prod_assoc: forall n m p (m1: ZMatrix n m)
  (m2: ZMatrix m p) (v: ZVector p),
  (Mmul m1 m2) × v = m1 × (m2 × v).
Proof. 
  induction' n as [|n].
  Case "O".
    intros. unfold Matrix in *. dest_vects.
    destruct m1; simpl in *; clean.
  Case "S n".
    intros.
    Vdestruct m1 as hd1 m1.
    subst.
    specialize (IHn _ _ m1 m2 v).
    unfold Mmul, Mmul_transp in *.
    simpl_vect in *. f_equal; auto. 

    clear'.
    revert dependent p.
    induction' p as [|p]; intros.
    SCase "O".
      rewrite (Vect_0 v). unfold Vprod. simpl.
      unfold Matrix in *. clear'.
      dest_vects. simpl. clear'.  simpl. revert m2.
      induction' hd1 as [|v hd1]; destruct m2; simpl; auto.
      rewrite <- IHhd1. dest_vects. destruct v0; simpl in *; auto. lia.
    SCase "S p".
      simpl.
      rewrite Vmap_cons.
      Vdestruct v as z v.
      simpl_vect. simpl.
      rewrite IHp.
      clear'.
      induction' m as [|m].
      SSCase "O".
        rewrite (Vect_0 m2). clear'.
        unfold Vprod, Vmap. simpl.
        dest_vects. destruct hd1; simpl; reflexivity.
      SSCase "S m".
        Vdestruct hd1 as z1 hd1.
        Vdestruct m2 as vm2 m2.
        specialize (IHm hd1 m2).
        simpl_vect.
        simpl in *.
        unfold ZNum.Numerical_Num in *. 
        match goal with
          | |- ((?A + ?B ) * z + (?C + ?D))%Z = _ =>
            replace ((A + B) * z + (C + D))%Z with
              ((A*z + C) + (B *z + D))%Z by lia
        end.
        f_equal; auto.
        rewrite <- Zmult_assoc.        
        rewrite <- Zmult_plus_distr_r.
        f_equal.
        Vdestruct vm2 as hdvm2 vm2.
        simpl_vect. reflexivity.
  Qed.


Definition Mprod_vect_right_transp `{Numerical A} {n p: nat}
  (m: Matrix A p n) (v: Vector A n) : Vector A p :=
  Vmap (fun c2 => 〈v, c2〉) m.

Definition Mprod_vect_right `{Numerical A} {n p: nat} (v: Vector A n)
  (m: Matrix A n p) : Vector A p :=
  Mprod_vect_right_transp (Mtranspose m) v.

Definition V1 {A} (a:A) : Vector A 1 :=
  exist (fun l : Pseudo_Vector A => length l = 1%nat) [a] eq_refl.


Lemma Mprod_vect_right_transp_correct (n p: nat) (v1: ZVector n)
  (m: ZMatrix n p) (v2: ZVector p):
  〈Mprod_vect_right_transp (Mtranspose m) v1, v2〉=〈v1, m × v2〉.
Proof.
  pose proof (Mmul_prod_assoc (V1 v1) m v2) as MPA.
  unfold Mmul, Mprod_vect_right, Mprod_vect_right_transp, V1, Mmul_transp in *.
  unfold Vmap at 1 in MPA. simpl in MPA.
  match type of MPA with
    | ?x = ?y => assert (`x = `y) as MPA' by congruence
  end. clear MPA. simpl in MPA'. inv MPA'. reflexivity.
Qed.


Lemma Mprod_vect_right_correct (n p: nat) (v1: ZVector n)
  (m: ZMatrix n p) (v2: ZVector p):
  〈Mprod_vect_right v1 m, v2〉=〈v1, m × v2〉.
Proof.
  unfold Mprod_vect_right. apply Mprod_vect_right_transp_correct.
Qed.

Definition extend_matrix {n p} (M: ZMatrix n (S p)): ZMatrix (S n) (S p) :=
  (1 ::: V0 p) ::: M.

Lemma extend_matrix_correct n p (M: ZMatrix n (S p)) (v : ZVector p):
  (extend_matrix M) × (1:::v) = 1 ::: (M × (1:::v)).
Proof.
  intros.
  unfold extend_matrix, Matrix, Matrix in *.
  apply PVeq_Veq.
  unfold Mprod_vect. simpl.
  f_equal. simpl_vect. reflexivity.
Qed.



   Definition V_insert_middle {A} {dim1 dim2 dim3: nat} (v13: Vector A (dim1 + dim3))
     (v2: Vector A dim2) : Vector A ((dim1 + dim2) + dim3) :=
     let v1 := Vtake_p dim1 v13 in
     let v3 := Vdrop_p dim1 v13 in
       (v1 +++ v2) +++ v3.


   Lemma V_insert_middle_ok_l `{Numerical A} (dim1 dim2 dim3: nat)
     (v1 v1': Vector A dim1)
     (v2 v2': Vector A dim2)
     (v3 v3': Vector A dim3):
     〈V_insert_middle (v1 +++ v3) v2, (v1' +++ v2') +++ v3'〉 =
     (〈v1,v1'〉+〈v2,v2'〉)+〈v3,v3'〉.
   Proof.
     unfold V_insert_middle.
     simpl_vect. repeat rewrite Vprod_app. simpl_vect. reflexivity.
   Qed.

   Lemma V_insert_middle_ok_r `{Numerical A} (dim1 dim2 dim3: nat)
     (v1 v1': Vector A dim1)
     (v2 v2': Vector A dim2)
     (v3 v3': Vector A dim3):
     〈(v1' +++ v2') +++ v3', V_insert_middle (v1 +++ v3) v2〉=
     (〈v1',v1〉+〈v2',v2〉)+〈v3',v3〉.
   Proof.
     unfold V_insert_middle.
     simpl_vect. repeat rewrite Vprod_app. simpl_vect. reflexivity.
   Qed.

   Hint Rewrite @V_insert_middle_ok_r @V_insert_middle_ok_l: vect.


   Definition V_insert_middle0 `{Numerical A} {dim1 dim2 dim3: nat} (v13: Vector A (dim1 + dim3))
     : Vector A ((dim1 + dim2) + dim3) :=
     V_insert_middle v13 (V0 dim2).

   Lemma V_insert_middle0_ok_l `{Numerical A} (dim1 dim2 dim3: nat)
     (v1 v1': Vector A dim1)
     (v2': Vector A dim2)
     (v3 v3': Vector A dim3):
     〈V_insert_middle0 (v1 +++ v3), (v1' +++ v2') +++ v3'〉 =
     〈v1,v1'〉+〈v3,v3'〉.
   Proof.
     unfold V_insert_middle0.
     rewrite V_insert_middle_ok_l. simpl_vect. reflexivity.
   Qed.

   Lemma V_insert_middle0_ok_r `{Numerical A} (dim1 dim2 dim3: nat)
     (v1 v1': Vector A dim1)
     (v2': Vector A dim2)
     (v3 v3': Vector A dim3):
     〈(v1' +++ v2') +++ v3', V_insert_middle0 (v1 +++ v3)〉 =
     〈v1',v1〉+〈v3',v3〉.
   Proof.
     unfold V_insert_middle0.
     rewrite V_insert_middle_ok_r. simpl_vect.  reflexivity.
   Qed.
  
   Hint Rewrite @V_insert_middle_ok_r @V_insert_middle_ok_l: vect.


Section INTZ.


Variable n:nat.
Implicit Type iv: IVector n.
Implicit Type zv: ZVector n.

Definition i2z := Int.signed.

Definition z2i (z:Z):= 
  if Z_le_dec Int.min_signed z && Z_le_dec z Int.max_signed then
    Some (Int.repr z)
  else 
    None.


Definition i2zvect iv : ZVector n :=
  Vmap i2z iv.

Definition i2zlist (il: list int): list Z := map i2z il.

Definition z2ivect zv : option (IVector n) :=
  OVmap z2i zv.

Definition z2ilist (zl: list Z) : option (list int) := mmap z2i zl.

Lemma i2z2i i: z2i (i2z i) = Some i.
Proof.
  unfold z2i, i2z.
  pose proof (Int.signed_range i).
  destruct H.
  
  repeat match goal with
    | |- context[Z_le_dec ?X1 ?X2] =>
      destruct (Z_le_dec X1 X2); try contradiction
  end.
  simpl. f_equal.
  apply Int.repr_signed.
Qed.

Lemma z2i2z z: forall i, z2i z = Some i -> i2z i = z.
Proof.
  unfold i2z, z2i.
  intros i SOME.
  repeat match goal with
    | H : context[Z_le_dec ?X1 ?X2] |- _ =>
      destruct (Z_le_dec X1 X2); simpl in H
  end; auto. clean. apply Int.signed_repr; auto.
Qed.

Lemma i2z2ivect iv: z2ivect (i2zvect iv) = Some iv.
Proof.
  unfold z2ivect, i2zvect, OVmap.
  apply simpl_ovector_of_olist.
  dest_vect iv. simpl.
  apply mmap_inv. apply i2z2i.
Qed.

Lemma i2z2ilist il: z2ilist (i2zlist il) = Some il.
Proof.
  unfold z2ilist, i2zlist.
  apply mmap_inv. apply i2z2i.
Qed.
Lemma z2i2zlist zl: forall il, z2ilist zl = Some il -> i2zlist il = zl.
Proof.
  unfold z2ilist, i2zlist.
  induction zl; intros; simpl in *; auto.
  destruct il; simpl in *; auto.
  inv H.

  monadInv H. simpl.
  f_equal.
    apply z2i2z; congruence.
  auto.
Qed.

End INTZ.



Definition i2zmatrix n p  (im: IMatrix n p) : ZMatrix n p:=
  Vmap (Vmap i2z) im.
Implicit Arguments i2zmatrix [[n] [p]].
Implicit Arguments i2zvect [[n]].


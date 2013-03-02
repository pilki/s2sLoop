Require Import Coqlibext.
Require Import Do_notation.
Require Import ClassesAndNotations.
Require Import Psatz.
Require Import Program.

Set Implicit Arguments.


Definition decidable (P:Prop) := {P} + {~P}.

(* Definition of what a vector is and what multiplication on vectors
   mean *)

Local Hint Unfold decidable: pb.
Local Ltac un := autounfold with pb in *.


Section WITHDIM.
Variable n: nat.
Definition vector := {l:list Z| length l = n}.
Implicit Type v: vector.
Implicit Type va: list Z.
Implicit Type x y z: Z.



Fixpoint prod_vect_aux (va1 va2:list Z) : Z :=
  match va1, va2 with
    | nil, _
    | _, nil => 0
    | x1 :: va1', x2 :: va2' =>
      (x1 * x2) + (prod_vect_aux va1' va2')
  end.

Ltac dest_vect v :=
  let av := fresh "a" v in
  let avLENGTH := fresh av "LENGTH" in
  destruct v as [av avLENGTH].

Ltac dest_vects :=
  repeat
  match goal with
    | v : vector |- _ =>
      dest_vect v
  end; simpl.

Program Definition prod_vect v1 v2 : Z :=
  prod_vect_aux v1 v2.


Notation "v1 <*> v2" := (prod_vect v1 v2) (at level 69).

Inductive cmp := EQ | GE.

Record constraint := mkConstraint
  { vect: vector;
    comp: cmp;
    val: Z}.



Definition satisfy_cmp z1 comp z2 :=
  match comp with
    | EQ => z1 = z2
    | GE => z1 >= z2
  end.

Local Hint Unfold satisfy_cmp: pb.

Lemma satisfy_cmp_dec: forall z1 comp z2, decidable (satisfy_cmp z1 comp z2).
Proof.
  intros z1 comp0 z2.
  un.
  destruct comp0. apply zeq. apply Z_ge_dec.
Qed.


Definition satisfy_constr v (constr: constraint) :=
  satisfy_cmp (constr.(vect) <*> v) constr.(comp) constr.(val).

Local Hint Unfold satisfy_constr: pb.


Lemma satisfy_constr_dec: forall v constr, decidable (satisfy_constr v constr).
Proof.
  intros v constr. un.
  apply satisfy_cmp_dec.
Qed.

Fixpoint repeat {A:Type} (m: nat) (a:A) :=
  match m with
    | O => nil
    | S m' => a :: (repeat m' a)
  end.

Lemma repeat_length: forall A m (a:A), 
  length (repeat m a) = m.
Proof.
  induction m; simpl; intros; auto.
Qed.

Program Definition repeat_v z : vector:=
  repeat n z.
Next Obligation. apply repeat_length. Qed.



Definition empty_constr:= mkConstraint (repeat_v 0) GE 1.
Local Hint Unfold empty_constr: pb.
Program Lemma empty_constr_empty : forall v,
  ~satisfy_constr v empty_constr.
Proof.
  intros v.
  un. simpl.

  assert (forall m av, prod_vect_aux (repeat m 0) av = 0).
  induction m; destruct av; simpl; intros; auto.
  assert (repeat_v 0 <*> v = 0).
  dest_vect v. unfold prod_vect. simpl. auto.
  rewrite H0. auto.
Qed.


Definition polyhedron := list constraint.

Hint Unfold polyhedron: aliases.


Definition In_pol v (pol: polyhedron) :=
  list_forall (satisfy_constr v) pol.

Definition empty pol := forall v, ~In_pol v pol.


Program Definition opp_vect v : vector:= List.map Zopp v.
Next Obligation.
  dest_vect v. simpl. rewrite map_length. auto.
Qed.

Local Hint Unfold opp_vect: pb.

Notation "<~> v" := (opp_vect v) (at level 42).

Lemma opp_vect_correct1:
  forall v1 v2,  (<~> v1) <*> v2 = - (v1 <*> v2).
Proof.
  unfold opp_vect, prod_vect. intros. dest_vects. simpl.
  clear av1LENGTH av2LENGTH.
  revert av2.
  induction av1; destruct av2; simpl; intros; auto.
  rewrite IHav1. lia.
Qed.

Lemma opp_vect_correct2:
  forall v1 v2,  v1 <*> (<~> v2) = - (v1 <*> v2).
Proof.
  unfold opp_vect, prod_vect. intros. dest_vects.
  clear av1LENGTH av2LENGTH.
  revert av1.
  induction av2; destruct av1; simpl; intros; auto.
  rewrite IHav2. lia.
Qed.


(* canonize_pol removes all equalities *)
Fixpoint canonize_pol pol :=
  match pol with
    | nil => nil
    | constr :: pol' =>
      match constr.(comp) with
        | EQ =>
          (mkConstraint (<~> constr.(vect)) GE (Zopp constr.(val)))::
          (mkConstraint  constr.(vect) GE constr.(val))::
          canonize_pol pol'
        | GE => constr :: canonize_pol pol'
      end
  end.

Local Hint Unfold In_pol: pb.
Lemma canonize_pol_corr1: forall v pol, In_pol v pol ->
  In_pol v (canonize_pol pol).
Proof.
  un.
  induction pol; simpl; intro LF.
  constructor.
  inversion LF as [|? ? SATIS LF']. subst. clear LF.
  destruct a. simpl. destruct comp0; [|constructor; auto].

  unfold satisfy_constr in SATIS. simpl in *.

  unfold satisfy_constr.
  repeat (constructor; simpl); auto.
  rewrite opp_vect_correct1. lia.
  lia.
Qed.

Lemma canonize_pol_corr2: forall v pol,
  In_pol v (canonize_pol pol) -> In_pol v pol.
Proof.
  un.
  induction pol; simpl; intro LF.
  constructor.
  destruct a. simpl in *. destruct comp0; auto.
  inv LF. inv H2.
  constructor; eauto. clear H4 IHpol.
  unfold satisfy_constr in *; simpl in *.
  rewrite opp_vect_correct1 in H1. lia.
  inv LF. constructor; eauto.
Qed.

Program Definition mult_vect z v : vector:=
  map (fun z' => z * z') v.
Next Obligation.
  dest_vect v.
  simpl. rewrite map_length. auto.
Qed.

Notation "z *> v" := (mult_vect z v) (at level 42).
Local Hint Unfold mult_vect prod_vect: pb.
Lemma mult_vect_correct1: forall z v1 v2, 
 (z *> v1) <*> v2 = (z * (v1 <*> v2)).
Proof.
  un.
  intros z v1 v2. dest_vects.
  clear. revert av2.
  induction av1; destruct av2; intros; simpl in *; auto; try lia.
  rewrite IHav1. lia.
Qed.


Definition mult_constraint z c :=
  mkConstraint
    ((Zabs z) *> c.(vect))
    c.(comp)
    ((Zabs z) * c.(val)).

Local Hint Unfold mult_constraint: pb.

Lemma mult_constraint_correct: forall v z c,
  satisfy_constr v c -> satisfy_constr v (mult_constraint z c).
Proof.
  unfold satisfy_constr, mult_constraint.
  intros v z c H. simpl.
  remember (Zabs z) as z'.
  assert (0 <= z'). rewrite Heqz'. apply Zabs_pos.
  destruct c.
  destruct comp0; simpl in *; auto.
  subst. rewrite mult_vect_correct1. reflexivity.
  rewrite mult_vect_correct1.

  apply Zmult_ge_compat_l; auto. lia.
Qed.


Fixpoint add_vect_aux av1 av2 :=
  match av1, av2 with
    | nil, _
    | _, nil => nil
    | z1::av1', z2::av2' =>
      (z1 + z2) :: add_vect_aux av1' av2'
  end.
Program Definition add_vect v1 v2 : vector :=
  add_vect_aux v1 v2.
Next Obligation.
  dest_vects.
  generalize dependent av2. revert av1LENGTH. revert n.
  induction av1; destruct av2; simpl; intros; auto.
  simpl in av1LENGTH. destruct n; auto.
Qed.

Notation "v1 <+> v2" := (add_vect v1 v2) (at level 42).

Lemma add_vect_correct1:
  forall v3 v1 v2,
    (v1 <+> v2) <*> v3 = (v1 <*> v3) + (v2 <*> v3).
Proof.
  intros. unfold add_vect, prod_vect. dest_vects.
  generalize dependent av2; generalize dependent av1; revert av3LENGTH; revert n.
  induction av3; intros; destruct av1; destruct av2; simpl in *;subst; auto.
  inv av1LENGTH; inv av2LENGTH.
  erewrite IHav3; eauto; try omega. lia.
Qed.


Definition add_constr c1 c2 :=
  mkConstraint (c1.(vect) <+> c2.(vect)) GE (c1.(val) + c2.(val)).

Lemma add_constr_correct : forall v c1 c2,
  satisfy_constr v c1 -> satisfy_constr v c2 -> satisfy_constr v (add_constr c1 c2).
Proof.
  unfold satisfy_constr.
  intros v c1 c2 H H0. destruct c1; destruct c2. simpl in *.
  rewrite add_vect_correct1.
  destruct comp0; destruct comp1; simpl in *; subst; lia.
Qed.

Fixpoint mult_each_constraint (wit: list Z) (pol: polyhedron) : option polyhedron :=
  match wit, pol with
    | nil, nil => Some nil
    | nil, _
    | _, nil => None
    | z :: wit', c::pol' =>
      do pol'' <- mult_each_constraint wit' pol';
      Some ((mult_constraint z c) :: pol'')
  end.

Lemma mult_each_constraint_correct: forall v wit pol pol',
  In_pol v pol -> mult_each_constraint wit pol = Some pol' ->
  In_pol v pol'.
Proof.
  induction wit; destruct pol; unfold In_pol in *; intros; simpl in *; auto.
  inv H0. constructor.

  prog_dos. inv H.
  constructor; eauto.
  apply mult_constraint_correct. auto.
Qed.

Definition colapse_constraints pol :=
  match pol with
    | nil => None
    | c1 :: pol' =>
      Some (fold_left add_constr pol' c1)
  end.

Lemma colapse_constraints_correct: forall v pol c,
  colapse_constraints pol = Some c ->
  In_pol v pol -> satisfy_constr v c.
Proof.
  intros v pol c.
  destruct pol; simpl. auto.
  unfold In_pol. intros HEQ IN. inv HEQ. inv IN.

  generalize dependent c0. generalize dependent pol.
  induction pol; intros; simpl in *; auto.
  inv H2.
  apply IHpol; auto. apply add_constr_correct; auto.
Qed.


(* in lib *)
Fixpoint list_forallb {A:Type} f (l: list A) :=
  match l with
    | nil => true
    | x :: l' =>
      (f x) && (list_forallb f l')
  end.

Lemma list_forallb_correct: forall A f (P: A -> Prop) (l: list A),
  (forall a, f a = true -> P a) ->
  list_forallb f l = true -> list_forall P l.
Proof.
  intros A f P l H H0. 
  induction l; simpl in *; constructor.
  apply H. destruct (f a); auto.
  apply IHl. destruct (list_forallb f l); auto.
  destruct (f a); auto.
Qed.

Definition is_pos z :=
  match z with
    | Zpos _ => true
    | _ => false
  end.

Program Definition check_contradiction (c: constraint) :=
  (is_pos c.(val)) && (list_forallb (fun z => z == 0) c.(vect)).

Lemma check_contradiction_correct:
  forall c, check_contradiction c = true ->
    forall v, ~satisfy_constr v c.
Proof.
  unfold check_contradiction, satisfy_constr; intros c H v H'.
  destruct c. dest_vects. unfold prod_vect in *; simpl in *.
  destruct (andb_prop _ _ H). clear H.
  apply list_forallb_correct with (P := (fun z => z = 0)) in H1.

    Focus 2.
      intros. dest ==; auto.

  assert (0 >= val0).
    clear avLENGTH avect0LENGTH.
    generalize dependent av. revert H1. clear H0. revert val0.
    induction avect0; intros; destruct comp0; simpl in *; auto; try lia.
    destruct av; subst; try lia.
    inv H1. simpl. eauto.
    destruct av; subst; try lia.
    inv H1. simpl in H'. eauto.

  unfold is_pos in H0.
  destruct val0; eauto.
Qed.

Program Definition
  check_emtpy (wit: list Z) (pol: polyhedron) : {empty pol} + {True}:=
  match mult_each_constraint wit pol with
    | None => right _
    | Some pol' =>
      match colapse_constraints pol' with
        | None => right _
        | Some c =>
          match check_contradiction c with
            | true => left _
            | false => right _
          end
      end
  end.
Next Obligation.
  unfold empty. intros v IN.
  symmetry in Heq_anonymous. symmetry in Heq_anonymous0. symmetry in Heq_anonymous1.
  pose proof (mult_each_constraint_correct _ IN Heq_anonymous).
  apply (colapse_constraints_correct Heq_anonymous0) in H.
  eapply check_contradiction_correct; eauto.
Qed.


(* we now use the emptyness test to build an inclusion test *)

Definition inv_constr (c: constraint) :=
  mkConstraint (opp_vect c.(vect)) GE (1 - c.(val)).


Lemma inv_constr_correct: forall c v,
  c.(comp) = GE -> ~(satisfy_constr v (inv_constr c)) ->
  satisfy_constr v c.
Proof.
  unfold satisfy_constr. unfold inv_constr.
  intros c v H H0.
  destruct c. simpl in *. subst.
  rewrite opp_vect_correct1 in H0.
  assert (~(- (vect0 <*> v) >= (1 - val0))); auto.
  simpl. lia.
Qed.


(* is_empty is defined in Polyhedra.v *)
Variable is_empty_canonized : forall (p: polyhedron), {empty p} + {True}.


Definition included p1 p2 :=
  forall v, In_pol v p1 -> In_pol v p2.
Hint Unfold In_pol included.

Definition are_included_aux p1 p2 :=
  list_forallb (fun c => is_empty_canonized ((inv_constr c) :: p1)) (canonize_pol p2).

Lemma empty_inv: forall c p, c.(comp) = GE -> empty ((inv_constr c) :: p) ->
  forall v, (In_pol v p -> satisfy_constr v c).
Proof.
  unfold empty, In_pol.
  intros c p H H0 v H1.
  apply inv_constr_correct; auto.
  intro SATIS.
  apply (H0 v).
  constructor; auto.
Qed.

Lemma are_included_aux_correct:
  forall p1 p2, are_included_aux p1 p2 = true -> included p1 p2.
Proof.
  unfold included, In_pol, are_included_aux.
  intros p1 p2 H v H0.
  apply list_forallb_correct with (P := (fun c=> empty (inv_constr c :: p1))) in H.
  apply canonize_pol_corr2. unfold In_pol.

  induction p2 as [|c p2]; simpl; try constructor.
  destruct c; destruct comp0; simpl in *; constructor; inv H; eauto using empty_inv.
  constructor; inv H4; eauto using empty_inv.

  intros c H1. destruct (is_empty_canonized (inv_constr c :: p1)); simpl in H1; auto.
Qed.

Program Definition are_included_canonized_part p1 p2 : {included p1 p2} + {True} :=
  match are_included_aux p1 p2 with
    | true => left _
    | false => right _
  end.
Next Obligation.
  auto using are_included_aux_correct.
Qed.

Program Definition are_included_part p1 p2 : {included p1 p2} + {True} :=
  match are_included_aux (canonize_pol p1) p2 with
    | true => left _
    | false => right _
  end.
Next Obligation.
  unfold included. intros v H. apply canonize_pol_corr1 in H.
  symmetry in Heq_anonymous. apply are_included_aux_correct in Heq_anonymous.
  unfold included in Heq_anonymous. eauto.
Qed.
End WITHDIM.







Definition pseudo_vector := list Z.

Record pseudo_constraint := mkPseudoConstraint
  { pvect: pseudo_vector;
    pcomp: cmp;
    pval: Z}.

Definition pseudo_polyhedron := list pseudo_constraint.

Fixpoint is_of_length (n: nat) (pv: pseudo_vector) :=
  match n, pv with
    | O, nil => true
    | _, nil
    | O, _ => false
    | S n', _ :: pv' => is_of_length n' pv'
  end.

Program Definition make_vector n (pv: pseudo_vector) : option (vector n) :=
  match is_of_length n pv with
    | true => Some pv
    | false => None
  end.
Next Obligation.
  generalize dependent pv.
  induction n; destruct pv; simpl; intro LENGTH; auto.
Qed.

Definition make_constraint n (pc: pseudo_constraint) : option (constraint n):=
  do v <- make_vector n pc.(pvect);
  point (mkConstraint v pc.(pcomp) pc.(pval)).



Definition make_polyhedron n (ph : pseudo_polyhedron) : option (polyhedron n):=
  mmap (make_constraint n) ph.


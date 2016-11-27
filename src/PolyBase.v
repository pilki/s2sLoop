Add LoadPath "../from_compcert".
Require Import Coqlibext.
Require Import Do_notation.
Require Import ClassesAndNotations.
Require Import Psatz.
Require Import Program.
Require Import ArithClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.

(* move to lib COQLIBEXT *)

Definition Semi_Decidable P := {P} + {True}.


Inductive Comparison := EQ | GE.

Module CompEqDec <: EQUALITY_TYPE.
  Definition t := Comparison.
  Global Instance EqDec_t: EqDec Comparison.
  Proof.
   constructor.
   decide equality.
 Qed.
End CompEqDec.

Section WITHDIM.
Variable n: nat.
Local Notation "'ZVector'" := (Vector Z n).


Implicit Type v: ZVector.
Implicit Type va: list Z.
Implicit Type x y z: Z.




Record Constraint := mkConstraint
  { constr_vect: ZVector;
    constr_comp: Comparison;
    constr_val: Z}.

Definition satisfy_comparison z1 comp z2 :=
  match comp with
    | EQ => z1 = z2
    | GE => z1 >= z2
  end.

Local Hint Unfold satisfy_comparison: autounfold.

Lemma satisfy_comparison_dec: forall z1 comp z2, Decidable (satisfy_comparison z1 comp z2).
Proof.
  intros z1 comp0 z2.
  unfold*.
  destruct comp0. apply zeq. apply Z_ge_dec.
Qed.


Definition satisfy_constraint v (constr: Constraint) :=
  satisfy_comparison 
    〈constr.(constr_vect), v〉
    constr.(constr_comp)
    constr.(constr_val).

Local Hint Unfold satisfy_constraint: autounfold.


Lemma satisfy_constraint_dec: forall v constr,
  Decidable (satisfy_constraint v constr).
Proof.
  intros v constr. unfold*.
  apply satisfy_comparison_dec.
Qed.



Definition empty_constraint : Constraint := 
  {| constr_vect :=(V0 n);
     constr_comp := GE;
     constr_val := 1 |}.

Local Hint Unfold empty_constraint: autounfold.

Program Lemma empty_constraint_empty : forall v,
  ~satisfy_constraint v empty_constraint.
Proof.
  intros v.
  unfold*. simpl.
  rewrite Vprod_V0_l. simpl. lia.
Qed.


Definition Polyhedron := list Constraint.

Hint Unfold Polyhedron: aliases.


(* the prefix P being already used for positive, we'll use Pol_ for
   polyhedra *)

Definition Pol_In v (pol: Polyhedron) :=
  list_forall (satisfy_constraint v) pol.

Notation "v ∈ pol" := (Pol_In v pol) (at level 70).
Notation "v ∉ pol" := (~ v ∈ pol) (at level 70).


Definition Pol_Empty pol := forall v, v ∉ pol.
Notation "pol ≈∅" := (Pol_Empty pol) (at level 70).


(* canonize_pol removes all equalities and replaces them by two inequalities *)
Fixpoint Pol_canonize pol :=
  match pol with
    | nil => nil
    | constr :: pol' =>
      match constr.(constr_comp) with
        | EQ =>
          (mkConstraint (-- constr.(constr_vect)) GE (Zopp constr.(constr_val)))::
          (mkConstraint  constr.(constr_vect) GE constr.(constr_val))::
          Pol_canonize pol'
        | GE => constr :: Pol_canonize pol'
      end
  end.

Local Hint Unfold Pol_In: autounfold.

Definition Pol_Included p1 p2 :=
  forall v, v ∈ p1 -> v ∈ p2.
Hint Unfold Pol_Included: autounfold.

Instance Pol_Included_PreOrder: PreOrder Pol_Included.
Proof.
  constructor; red; unfold*; dintuition.
Qed.

(* the definition of partial order is absurd, so we don't define an instance *)  


Notation "p1 ⊂ p2" := (Pol_Included p1 p2) (at level 70). (* \subset *)


Lemma Pol_Included_canonize: forall pol,
  pol ⊂ (Pol_canonize pol).
Proof.
  autounfold with * in *. unfold Pol_In.

  induction pol; simpl; intros v LF.
  constructor.
  inversion LF as [|? ? SATIS LF']. subst. clear LF.
  destruct a. simpl. destruct constr_comp0; [|constructor; auto].

  unfold satisfy_constraint in SATIS. simpl in *.

  unfold satisfy_constraint in *.
  repeat (constructor; simpl); auto.
  simpl_vect. simpl.
  omega.

  lia.
Qed.

Lemma Pol_canonize_Included: forall pol,
  Pol_canonize pol ⊂ pol.
Proof.
  unfold*. unfold Pol_In.
  induction pol; simpl; intros v LF.
  constructor.
  destruct a. simpl in *. destruct constr_comp0; auto.
  inv LF. inv H2.
  constructor; eauto. clear H4 IHpol.
  unfold satisfy_constraint in *; simpl in *.
  simpl_vect in *. simpl in *. lia.
  inv LF. constructor; eauto.
Qed.

Hint Resolve Pol_Included_canonize Pol_canonize_Included: pol.

Local Hint Unfold Vmul Vprod: autounfold.

(* multiply a constraint by a *positive* number *)

Definition Constr_mul z c :=
  {| constr_vect := ((Zabs z) · c.(constr_vect));
     constr_comp := c.(constr_comp);
     constr_val := ((Zabs z) * c.(constr_val)) |}.

Local Hint Unfold Constr_mul: autounfold.

Lemma Constr_mul_correct: forall v z c,
  satisfy_constraint v c -> satisfy_constraint v (Constr_mul z c).
Proof.
  unfold satisfy_constraint, Constr_mul.
  intros v z c H. simpl.
  remember (Zabs z) as z'.
  assert (0 <= z'). rewrite Heqz'. apply Zabs_pos.
  destruct c.
  destruct constr_comp0; simpl in *; auto; simpl_vect.
  subst. reflexivity.

  apply Zmult_ge_compat_l; auto. lia.
Qed.

Hint Resolve Constr_mul_correct: pol.

(* add two (canonical) constraints *)
Definition Constr_add c1 c2 :=
  {| constr_vect := (c1.(constr_vect) ⊹ c2.(constr_vect));
     constr_comp := GE;
     constr_val := (c1.(constr_val) + c2.(constr_val))|}.

Lemma Constr_add_correct : forall v c1 c2,
  satisfy_constraint v c1 -> satisfy_constraint v c2 ->
  satisfy_constraint v (Constr_add c1 c2).
Proof.
  unfold satisfy_constraint.
  intros v c1 c2 H H0. destruct c1; destruct c2. simpl in *.
  simpl_vect.

  destruct constr_comp0; destruct constr_comp1; simpl in *; subst; lia.
Qed.

Hint Resolve Constr_add_correct: pol.

(* multiply each constraint of the polyhedron by the corresponding
   coefficient in the witnesses list*)

Fixpoint Pol_mul_each_constraint (wit: list Z) (pol: Polyhedron) : option Polyhedron :=
  match wit, pol with
    | nil, nil => Some nil

      (* if we have to many or not enough witnesses, we fail *)
    | nil, _
    | _, nil => None

    | z :: wit', c::pol' =>
      do pol'' <- Pol_mul_each_constraint wit' pol';
      Some ((Constr_mul z c) :: pol'')
  end.

Lemma Pol_Included_mul_each_constraint: forall wit pol pol',
  Pol_mul_each_constraint wit pol = Some pol' ->
  pol ⊂ pol'.
Proof.
  unfold*.
  induction wit; destruct pol; unfold Pol_In in *; intros; simpl in *; auto.
  inv H. constructor.

  prog_dos. inv H0.
  constructor; eauto.
  apply Constr_mul_correct. auto.
Qed.

Hint Resolve Pol_Included_mul_each_constraint: pol.

Definition Pol_add_all_constraints pol :=
  match pol with
    | nil => None
    | c1 :: pol' =>
      Some (fold_left Constr_add pol' c1)
  end.

Lemma Pol_add_all_constraints_correct: forall v pol c,
  Pol_add_all_constraints pol = Some c ->
  v ∈ pol -> satisfy_constraint v c.
Proof.
  intros v pol c.
  destruct pol; simpl. auto.
  unfold Pol_In. intros HEQ IN. inv HEQ. inv IN.

  generalize dependent c0. generalize dependent pol.
  induction pol; intros; simpl in *; auto.
  inv H2.
  apply IHpol; auto. apply Constr_add_correct; auto.
Qed.

Hint Resolve Pol_add_all_constraints_correct: pol.

Definition is_pos z :=
  match z with
    | Zpos _ => true
    | _ => false
  end.

Program Definition Constr_check_contradiction (c: Constraint) :=
  (is_pos c.(constr_val)) && (list_forallb (fun z => z == 0) c.(constr_vect)).

Lemma Constr_check_contradiction_correct:
  forall c, Constr_check_contradiction c = true ->
    forall v, ~satisfy_constraint v c.
Proof.
  unfold Constr_check_contradiction, satisfy_constraint; intros c H v H'.
  destruct c. dest_vects. unfold Vprod in *; simpl in *.
  destruct (andb_prop _ _ H). clear H.
  apply list_forallb_list_forall with (P := (fun z => z = 0)) in H1.

    Focus 2.
      intros. dest ==; auto.

  assert (0 >= constr_val0).
    clear Lconstr_vect0 Lv.
    generalize dependent v. revert H1. clear H0. revert constr_val0.
    induction' constr_vect0; intros; destruct' constr_comp0; simpl in *; auto; try lia.
    Case "cons"; SCase "EQ". 
      destruct v; subst; try lia.
      inv H1. simpl. eauto.
    Case "cons"; SCase "GE".
      destruct v; subst; try lia.
      inv H1. simpl in H'. solve [eauto].

  unfold is_pos in H0.
  destruct constr_val0; eauto.
Qed.

Program Definition
  Pol_check_empty (wit: list Z) (pol: Polyhedron) : Semi_Decidable (pol ≈∅):=
  match Pol_mul_each_constraint wit pol with
    | None => right _
    | Some pol' =>
      match Pol_add_all_constraints pol' with
        | None => right _
        | Some c =>
          match Constr_check_contradiction c with
            | true => left _
            | false => right _
          end
      end
  end.
Next Obligation.
  unfold Pol_Empty. intros v IN.
  symmetry in Heq_anonymous. symmetry in Heq_anonymous0. symmetry in Heq_anonymous1.
  pose proof (Pol_Included_mul_each_constraint wit Heq_anonymous0 IN).
  apply (Pol_add_all_constraints_correct Heq_anonymous1) in H.
  eapply Constr_check_contradiction_correct; eauto.
Qed.


(* we now use the emptyness test to build an inclusion test *)

Definition Constr_inv (c: Constraint) :=
  {| constr_vect := (-- c.(constr_vect));
     constr_comp := GE;
     constr_val := (1 - c.(constr_val))|}.


Lemma Constr_inv_correct: forall c v,
  c.(constr_comp) = GE -> ~(satisfy_constraint v (Constr_inv c)) ->
  satisfy_constraint v c.
Proof.
  unfold satisfy_constraint. unfold Constr_inv.
  intros c v H H0.
  destruct c. simpl in *. subst.
  simpl_vect in *.
  assert (~(- 〈constr_vect0, v〉 >= (1 - constr_val0))); auto.
  simpl. lia.
Qed.


(* Pol_is_empty is defined in Polyhedra.v *)
Variable Pol_Empty_sdec_canonized : forall (p: Polyhedron), Semi_Decidable (p ≈∅).


Definition Pol_Included_sdec_canonized_bool p1 p2 :=
  list_forallb
    (fun c => Pol_Empty_sdec_canonized ((Constr_inv c) :: p1))
    p2.

Lemma Pol_Constr_inv_empty_satisfy: forall c p,
  c.(constr_comp) = GE -> ((Constr_inv c) :: p) ≈∅ ->
  forall v, (v ∈ p -> satisfy_constraint v c).
Proof.
  unfold *.
  intros c p H H0 v H1.
  apply Constr_inv_correct; auto.
  intro SATIS.
  apply (H0 v).
  constructor; auto.
Qed.


(* to lib COQLIBEXT *)

Lemma cons_not_nil: forall A (a:A) (l: list A),
  a::l = [] -r> False.
Proof.
  intros. constructor. intro H. inv H.
Qed.
Lemma nil_not_cons: forall A (a:A) (l: list A),
  [] = a::l -r> False.
Proof.
  intros. constructor. intro H. inv H.
Qed.

Hint Rewrite cons_not_nil nil_not_cons: clean.

Lemma list_forall_to_inv: forall A P (a:A) l,
  tag_to_inv (list_forall P (a :: l)).
Proof.
  dintuition.
Qed.
Hint Rewrite list_forall_to_inv: optional_inv.





Definition Pol_Canonized p := list_forall (fun constr => constr.(constr_comp) = GE) p.
Hint Unfold Pol_Canonized: autounfold.

Remark Pol_canonize_Canonized: forall p,
  Pol_Canonized (Pol_canonize p).
Proof.
  unfold*.
  induction' p; intros; subst; simpl; auto.
  Case "cons".
    destruct a. destruct constr_comp0; simpl; auto.
Qed.
Hint Resolve Pol_canonize_Canonized.

Program Definition Pol_Canonized_dec p : Decidable (Pol_Canonized p) :=
  match list_forallb (fun c => c.(constr_comp) == GE) p with
    | true => left _
    | false => right _
  end.
Next Obligation.
  unfold *.
  eapply list_forallb_list_forall ; [| rewrite Heq_anonymous; eauto].
  simpl. intros. destruct a. simpl in *. dest ==; clean.
Qed.
Next Obligation.
  unfold *.
  intro FORALL.
  eapply list_forall_list_forallb in FORALL. rewrite FORALL in *. clean.
  simpl. intros. destruct a. simpl in *. dest ==; clean.
Qed.


Lemma Pol_Included_sdec_canonized_bool_included:
  forall p1 p2,
    Pol_Canonized p2 ->
    Pol_Included_sdec_canonized_bool p1 p2 = true ->
    p1 ⊂ p2.
Proof.
  unfold*. unfold Pol_Included_sdec_canonized_bool.
  intros p1 p2 CANONIZED INCL_B v FORALL.
  apply list_forallb_list_forall
    with (P := (fun c=> Pol_Empty (Constr_inv c :: p1))) in INCL_B.

  Case "List Forall".

  induction' p2 as [|c p2]; simpl; try solve [constructor].
  SCase "cons c p2".
    clean.
    specialize (IHp2 H4 H2).
    constructor; auto.
    apply Constr_inv_correct; auto.
    intro SATISFY.
    unfold Pol_Empty in H1. apply (H1 v).
    unfold Pol_In.
    constructor; auto.
  Case "Premiss list_forallb_list_forall".
    intros c H1. destruct (Pol_Empty_sdec_canonized (Constr_inv c :: p1)); simpl in H1; auto.
Qed.

Program Definition Pol_Included_sdec_canonized_part p1 p2 (CAN: Pol_Canonized p2) : {p1 ⊂ p2} + {True} :=
  match Pol_Included_sdec_canonized_bool p1 p2 with
    | true => left _
    | false => right _
  end.
Next Obligation.
  eauto using Pol_Included_sdec_canonized_bool_included.
Qed.

Implicit Arguments Pol_Included_sdec_canonized_part [].

Program Definition Pol_Included_sdec_part p1 p2 : {p1 ⊂ p2} + {True} :=
  match Pol_Included_sdec_canonized_part (Pol_canonize p1) (Pol_canonize p2) _ with
    | left _ => left _
    | right _ => right _
  end.
Next Obligation.
  destruct Pol_Included_sdec_canonized_part; clean.

  etransitivity; eauto with pol.
  etransitivity; eauto with pol.
Qed.

End WITHDIM.

Notation "v ∈ pol" := (Pol_In v pol) (at level 70).
Notation "v ∉ pol" := (~ v ∈ pol) (at level 70).
Notation "pol ≈∅" := (Pol_Empty pol) (at level 70).
Notation "p1 ⊂ p2" := (Pol_Included p1 p2) (at level 70).



Section INJECTIVITY.
(* we now move to injectivity of a matrix on a polyhedra *)

Definition M_Injective_on_Pol {n p} (m: ZMatrix n p) (pol: Polyhedron p) :=
  forall v1 v2, v1 ∈ pol -> v2 ∈ pol -> m × v1 = m × v2 -> v1 = v2.


(* infix notation a la haskell. I don't think I can make a general
   notation for infix operators with `, but only specific ones*)

Notation "m '`is_injective_on`' pol" := (M_Injective_on_Pol m pol) (at level 10).

Definition Pol_intersection {n} (pol1 pol2: Polyhedron n) := pol1 ++ pol2.

Notation "pol1 ∩ pol2" := (Pol_intersection pol1 pol2) (at level 65).


Lemma Pol_intersection_Included_l n (pol1 pol2: Polyhedron n):
  pol1 ∩ pol2 ⊂ pol1.
Proof.
  intros v.
  unfold Pol_In.
  apply list_forall_app_list_forall_l.
Qed.
Lemma Pol_intersection_Included_r n (pol1 pol2: Polyhedron n):
  pol1 ∩ pol2 ⊂ pol2.
Proof.
  intros v.
  unfold Pol_In.
  apply list_forall_app_list_forall_r.
Qed.

Lemma Pol_Included_intersertion n (pol1 pol2: Polyhedron n) :
  forall v, v ∈ pol1 -> v ∈ pol2 -> v ∈ pol1 ∩ pol2.
Proof.
  intros v.
  apply list_forall_list_forall_app.
Qed.
Hint Resolve Pol_intersection_Included_r Pol_intersection_Included_l 
  Pol_Included_intersertion: pol.

(* MOVE TO OTHER FILE *)

Lemma Mprod_vect_V0 {n p} `{Numerical Num} (m: Matrix Num n p):
  m × V0 p = V0 n.
Proof.
  unfold Mprod_vect, Matrix, Vrepeat in *.
  apply PVeq_Veq. simpl.
  rewrite map_ext with (g := fun _ => 0%numerical).

  dest_vect m. revert dependent p.
  induction n; simpl; intros; destruct m; simpl in *; clean.
  f_equal. auto.


  intros. apply Vprod_V0_r.

Qed.


Lemma empty_vect_unique A (v: Vector A 0): v = exist _ nil eq_refl.
Proof.
  intros.
  dest_vect v. apply PVeq_Veq. simpl. destruct v; simpl in Lv; auto.
Qed.

Lemma Vprod_empty `{Numerical Num} (v1 v2: Vector Num 0):
  〈v1, v2〉= 0%numerical.
Proof.
  rewrite (empty_vect_unique v1). rewrite (empty_vect_unique v2).
  unfold Vprod. simpl. reflexivity.
Qed.

Lemma Vapp_empty {A n} (v: Vector A n): (exist _ nil eq_refl) +++ v = v.
Proof.
  apply PVeq_Veq. simpl. reflexivity.
Qed.

Hint Rewrite @Vapp_empty @Vprod_empty: empty_vect.

Ltac clean_empty_vect:=
  repeat
  match goal with
    | v : Vector ?A 0 |- _ =>
      rewrite (empty_vect_unique v) in *; clear v
  end;
  autorewrite with empty_vect in *.


Lemma concat_Vprod `{Numerical Num} {n p}
  (v2 v2': Vector Num p)  (v1 v1': Vector Num n):
  (〈v1 +++ v2, v1' +++ v2'〉 = 〈v1, v1'〉 + 〈v2, v2'〉)%numerical.
Proof.
  dest_vects.
  revert dependent v1. revert dependent v1'.
  induction n; intros;
  destruct v1; destruct v1'; simpl in *; auto.

  simpl_vect. reflexivity.

  simpl_vect. f_equal. auto.
Qed.


Definition Constr_translate_l {n} p (c : Constraint n) : Constraint (n + p) :=
  {|constr_vect :=  c.(constr_vect) +++ V0 p;
    constr_comp := c.(constr_comp);
    constr_val := c.(constr_val)|}.


Lemma Constr_translate_l_correct n p (c: Constraint n) v1 v2:
  satisfy_constraint v1 c <-> satisfy_constraint (v1 +++ v2) (Constr_translate_l p c).
Proof.
  destruct c.
  unfold satisfy_constraint. simpl.
  rewrite concat_Vprod. rewrite Vprod_V0_l. simpl_vect. dintuition.
Qed.


Definition Constr_translate_r {n} p (c : Constraint n) : Constraint (p + n) :=
{|constr_vect :=  V0 p +++ c.(constr_vect);
  constr_comp := c.(constr_comp);
  constr_val := c.(constr_val)|}.


Lemma Constr_translate_r_correct n p (c: Constraint n) v1 v2:
  satisfy_constraint v2 c <-> satisfy_constraint (v1 +++ v2) (Constr_translate_r p c).
Proof.
  destruct c.
  unfold satisfy_constraint. simpl.
  rewrite concat_Vprod. rewrite Vprod_V0_l. simpl_vect. dintuition.
Qed.

Hint Resolve Constr_translate_l_correct Constr_translate_r_correct: pol.


Definition Pol_prod {n p} (p1: Polyhedron n) (p2:Polyhedron p) : Polyhedron (n + p) :=
  List.map (Constr_translate_l p) p1
   ∩
   List.map (Constr_translate_r n) p2.

Notation "p1 ⊗ p2" := (Pol_prod p1 p2) (at level 65). (* \otimes *) (* utf8 : 228D *)




Lemma Pol_In_prod_In_l n p (p1: Polyhedron n) (p2:Polyhedron p) v1 v2 :
  v1 +++ v2 ∈ p1 ⊗ p2 -> v1 ∈ p1.
Proof.
  unfold Pol_prod.
  intro IN.
  apply Pol_intersection_Included_l in IN.
  unfold Pol_In in *.
  eapply list_forall_map_list_forall ; [| apply IN].

  intros.
  erewrite Constr_translate_l_correct. eauto.
Qed.

Lemma Pol_In_prod_In_r n p (p1: Polyhedron n) (p2:Polyhedron p) v1 v2 :
  v1 +++ v2 ∈ p1 ⊗ p2 -> v2 ∈ p2.
Proof.
  unfold Pol_prod.
  intro IN.
  apply Pol_intersection_Included_r in IN.
  unfold Pol_In in *.
  eapply list_forall_map_list_forall; [|apply IN].

  intros.
  erewrite Constr_translate_r_correct. eauto.
Qed.


Lemma Pol_In_In_prod n p (p1: Polyhedron n) (p2:Polyhedron p) v1 v2 :
  v1 ∈ p1 -> v2 ∈ p2 -> v1 +++ v2 ∈ p1 ⊗ p2.
Proof.
  intros IN1 IN2.
  apply Pol_Included_intersertion.

  unfold Pol_In in *.
  eapply list_forall_list_forall_map; [|apply IN1].
  intros. erewrite <- Constr_translate_l_correct; auto.

  unfold Pol_In in *.
  eapply list_forall_list_forall_map; [|apply IN2].
  intros. erewrite <- Constr_translate_r_correct; auto.
Qed.
Hint Resolve Pol_In_In_prod Pol_In_prod_In_r Pol_In_prod_In_l: pol.


(* define the polyhedron of dimension 2p such that v1 +++ v2 ∈ pol iff
   m × v1 = m × v2 *)
Definition Pol_same_image_two_matrices {n p1 p2} (m1: ZMatrix n p1)
  (m2: ZMatrix n p2) : Polyhedron (p1 + p2) :=
  map2
  (fun v1 v2 => 
    {| constr_vect := v1 +++ (-- v2);
       constr_comp := EQ;
       constr_val := 0|}
  ) (`m1) (`m2).


Hint Unfold Pol_same_image_two_matrices Pol_In Mprod_vect: autounfold.

Lemma Pol_In_SI2_same_image n p1 p2 (m1: ZMatrix n p1)
  (m2: ZMatrix n p2):
  forall v1 v2, v1 +++ v2 ∈ Pol_same_image_two_matrices m1 m2 -> m1 × v1 = m2 × v2.
Proof.
  unfold*.
  intros * IN_SAME.
  apply PVeq_Veq.
  dest_vect m1; dest_vect m2; simpl in *.
  assert (length m1 = length m2) by congruence.
  clear dependent n.
  generalize dependent m2.
  
  induction' m1 as[|mv1 m1]; intros;
    destruct' m2 as [|mv2 m2]; simpl in *; clean.

  Case "cons mv1 m1"; SCase "cons mv2 m2". 
  inv IN_SAME. inv H.
  f_equal; auto.
  clear' - H2.
  unfold satisfy_constraint, satisfy_comparison in H2.
  simpl in H2. rewrite concat_Vprod in H2. simpl in H2.
  simpl_vect in H2. simpl in H2. lia.
Qed.

Tactic Notation "rewriteZ" "<-" constr(R):=
  let H := fresh "H" in
  pose proof (@R Z _) as H;
  simpl in H; rewrite <- H; clear H.

Tactic Notation "rewriteZ" "<-" constr(R) "in" hyp(h):=
  let H := fresh "H" in
  pose proof (@R Z _) as H;
  simpl in H; rewrite <- H in h; clear H.

Tactic Notation "rewriteZ" constr(R):=
  let H := fresh "H" in
  pose proof (@R Z _) as H;
  simpl in H; rewrite H; clear H.

Tactic Notation "rewriteZ" constr(R) "in" hyp(h):=
  let H := fresh "H" in
  pose proof (@R Z _) as H;
  simpl in H; rewrite H in h; clear H.

Lemma Pol_same_image_In_SI2 n p1 p2 (m1: ZMatrix n p1)
  (m2: ZMatrix n p2):
  forall v1 v2, m1 × v1 = m2 × v2 -> v1 +++ v2 ∈ Pol_same_image_two_matrices m1 m2.
Proof.
  unfold*.
  intros * EQ_PROD.
  inv EQ_PROD.
  dest_vect m1. dest_vect m2. simpl in *.
  assert (length m1 = length m2) by congruence.
  clear dependent n.
  revert dependent m2.
  induction' m1 as [|mv1 m1]; intros;
    destruct' m2 as [|mv2 m2]; simpl in *; clean.
  inv H. inv H0.
  constructor; auto.
  unfold satisfy_constraint, satisfy_comparison.
  simpl.
  assert (〈mv1, v1〉 +(- 〈mv2, v2〉) = 0) by lia.
  rewriteZ Vopp_prod_distr_l in H.
  rewrite concat_Vprod. simpl. assumption.
Qed.




Definition Pol_same_image {n p} (m: ZMatrix n p) : Polyhedron (p + p):= 
  Pol_same_image_two_matrices m m.

  
Lemma Pol_In_SI_same_image n p (m: ZMatrix n p):
  forall v1 v2, v1 +++ v2 ∈ Pol_same_image m -> m × v1 = m × v2.
Proof.
  unfold Pol_same_image. apply Pol_In_SI2_same_image.
Qed.


Lemma Pol_same_image_In_SI n p (m: ZMatrix n p):
  forall v1 v2, m × v1 = m × v2 -> v1 +++ v2 ∈ Pol_same_image m.
Proof.
  unfold Pol_same_image. apply Pol_same_image_In_SI2.
Qed.

Hint Resolve Pol_In_SI_same_image Pol_same_image_In_SI: pol.


(* Pol_is_empty is defined in Polyhedra.v *)
Variable Pol_Empty_sdec_canonized: forall n (pol: Polyhedron n), Semi_Decidable (pol ≈∅).


(* [set_nth_aux n p] sets the nth element of the list of length p to
   v. All other elements are set to 0 *)

Fixpoint PV_all_0_except n p v :=
  match p with
    | O => []
    | S p' =>
      match n with
        | O => v :: repeat p' 0
        | S n' => 0 :: (PV_all_0_except n' p' v)
      end
  end.

Program Definition V_all_0_except n p v : ZVector p :=
  PV_all_0_except n p v.
Next Obligation.
  revert n.
  induction p; intro n; destruct n; simpl; auto.
  f_equal. apply repeat_length.
Qed.

Hint Unfold V_all_0_except: autounfold.

Lemma V_all_0_except_eq p v: forall n,
  (n < p)%nat -> Vnth (V_all_0_except n p v) n = v.
Proof.
  unfold Vnth, V_all_0_except. simpl.
  induction' p as [|p].

  Case "O".
  intros. omega.

  Case "S p".
  intros n INF.
  destruct n; simpl. reflexivity.
  apply IHp. omega.
Qed.

Lemma V_all_0_except_neq p v: forall n n',
  n <> n' -> Vnth (V_all_0_except n p v) n' = 0.
Proof.
  unfold Vnth, V_all_0_except. simpl.
  induction' p as [|p]; intros * DIFF; destruct n, n'; simpl; auto.

  Case "S p".
  clear.
  revert n'; induction p; destruct n'; simpl; auto.
Qed.

Hint Resolve V_all_0_except_eq V_all_0_except_neq: pol.

Lemma Vprod_all_0_except n p val (v:ZVector p):
〈V_all_0_except n p val, v〉 = val * Vnth v n.
Proof.
  dest_vect v.
  unfold Vprod, V_all_0_except, Vnth.
  simpl.
  revert dependent v. revert n.
  induction p; intros; destruct v; simpl in *; auto.
  destruct n; simpl; lia.
  inv Lv.
  destruct n; simpl.

  match goal with
    | |- context[PVprod ?V1 ?V2] =>
      replace (PVprod V1 V2) with 0
  end.
  lia.
  clear.
  induction v; simpl; auto.
  rewrite <- IHp. lia. reflexivity.
Qed.


Program Definition Vnth_eq_on_pol_sdec_canonized {p} (pol: Polyhedron (p + p)) n
  : Semi_Decidable (forall (v1 v2: ZVector p), v1 +++ v2 ∈ pol ->
      Vnth v1 n = Vnth v2 n):=
  let set1 := V_all_0_except n p 1 in
  let setm1 := V_all_0_except n p (-1) in
  let constr1 :=
    {| constr_vect := set1 +++ setm1; constr_comp := GE; constr_val := 1|} in
  let constr2 :=
    {| constr_vect := setm1 +++ set1; constr_comp := GE; constr_val := 1 |} in
  if Pol_Empty_sdec_canonized (constr1 :: pol) then
    if Pol_Empty_sdec_canonized (constr2 :: pol) then
      left _
    else
      right _ 
  else
    right _.
Next Obligation.
  unfold Pol_Empty in *.
  specialize (H (v1 +++ v2)).
  specialize (H0 (v1 +++ v2)).


  repeat match goal with
    | H : ?V ∉ ?constr :: pol |- _ =>
      assert (~ satisfy_constraint V constr) 
        by (intro; apply H; constructor; auto);
      clear H
  end.
  unfold satisfy_constraint in *; simpl in *.

  rewrite concat_Vprod in H2, H0.
  repeat rewrite Vprod_all_0_except in H2, H0.
  simpl Aadd in *.
  destruct (Vnth v1 n) ; destruct (Vnth v2 n); lia.
Qed.


Fixpoint Vnth_all_eq_on_pol_bool_canonized {p} (pol : Polyhedron (p + p)) n : bool:=
  match n with
    | O => Vnth_eq_on_pol_sdec_canonized pol O
    | S n' =>
      Vnth_eq_on_pol_sdec_canonized pol n && Vnth_all_eq_on_pol_bool_canonized pol n'
  end.

Lemma Vnth_all_eq_on_pol_bool_canonized_correct p (pol : Polyhedron (p + p)) n:
  Vnth_all_eq_on_pol_bool_canonized pol n = true ->
  forall v1 v2, v1 +++ v2 ∈ pol ->
  forall n', (n' <= n)%nat -> Vnth v1 n' = Vnth v2 n'.
Proof.
  intros EQTRUE * IN * LEQ.

  induction n; simpl in *.
  assert (n' = 0%nat) by omega. subst.
  destruct (Vnth_eq_on_pol_sdec_canonized pol 0); auto.

  destruct (andb_prop _ _ EQTRUE).
  destruct (lt_eq_lt_dec n' (S n)) as [[?|?] |?]; try omega.
  apply IHn; auto. omega.

  subst. destruct (Vnth_eq_on_pol_sdec_canonized pol (S n)); auto.
Qed.

Hint Resolve @Vnth_all_eq_on_pol_bool_canonized: pol.


Program Definition M_Injective_on_Pol_sdec_part {n p} (m: ZMatrix n p) (pol: Polyhedron p):
  Semi_Decidable (m `is_injective_on` pol) :=
  let pol' := Pol_canonize ( pol ⊗ pol ∩ Pol_same_image m) in
    match p with
      | O => left _
      | S p' => 
        match Vnth_all_eq_on_pol_bool_canonized pol' p' with
          | true => left _
          | false => right _
        end
    end.
Next Obligation.
  unfold M_Injective_on_Pol.
  intros.
  dest_vects.
  simpl in *. destruct v1; destruct v2; simpl in *; clear - Lv1 Lv2; clean.
Qed.
Next Obligation.
  unfold M_Injective_on_Pol.
  intros * IN1 IN2 EQ.
  apply Vnth_inj.
  intros p LT.
  assert (p <= p')%nat by omega.
  clear LT. revert dependent p.


  intros. eapply Vnth_all_eq_on_pol_bool_canonized_correct; eauto.
  apply Pol_Included_canonize.
  auto with pol.
Qed.
End INJECTIVITY.

Notation "p1 ⊗ p2" := (Pol_prod p1 p2) (at level 65). (* \otimes *) (* utf8 : 228D *)


Definition extend_polyhedron {n} (p:Polyhedron n) : Polyhedron (S n) :=
  {| constr_vect := 1 ::: V0 n;
     constr_comp := EQ;
     constr_val := 1 |} ::
  map
    (fun constr =>
      {| constr_vect := 0 ::: constr.(constr_vect);
         constr_comp := constr.(constr_comp);
         constr_val := constr.(constr_val) |}
      ) p.

Lemma extend_polyhedron_correct_1 n (p: Polyhedron n) (v: ZVector n):
  v ∈ p -> 1:::v ∈ (extend_polyhedron p).
Proof.
  unfold Pol_In.
  intro IN.
  unfold extend_polyhedron.
  constructor.
  Case "Head".
    red. simpl. simpl_vect. reflexivity.
  Case "Tail".
  eapply list_forall_list_forall_map; [|eauto].
  intros.
  clear IN.
  destruct a; unfold satisfy_constraint in *; simpl in *.
  simpl_vect. simpl. auto.
Qed.

Lemma extend_polyhedron_Vhd  n (p: Polyhedron n) (v: ZVector (S n)):
  v ∈ (extend_polyhedron p) -> Vhd v = 1.
Proof.
  intro IN.
  unfold Pol_In in IN. unfold extend_polyhedron in IN.
  inv IN. clear H2. red in H1. simpl in H1. 
  dest_vect v. unfold Vhd.
  destruct v; simpl in *. inv Lv.
  unfold Vprod, Vcons in H1. simpl in H1.
  rewrite PVprod_repeat_0 in H1.
  destruct z; lia.
Qed.

(*Lemma Vcase `{Numerical Num} n (v: Vector Num (S n)) :
  exists x v', v = x ::: v'.
Proof.
  exists (Vhd v). exists (Vtail v).*)




Lemma extend_polyhedron_Vtl  n (p: Polyhedron n) (v: ZVector (S n)):
  v ∈ (extend_polyhedron p) -> Vtail v ∈ p.
Proof.
  intro IN.
  Vdestruct v as a v.
  unfold Pol_In in *.
  unfold extend_polyhedron in IN.
  inv IN. clear H1.
  eapply list_forall_map_list_forall; [|eauto].
  clear. intros. destruct a0; unfold satisfy_constraint in *; simpl in *.
  simpl_vect in H. simpl in H. assumption.
Qed.

Lemma Pol_in_cons dim (v:ZVector dim) c pol:
  v ∈ (c :: pol) <-> (satisfy_constraint v c) /\ (v ∈ pol).
Proof.
  split; intro H; inv H; constructor; auto.
Qed.


Definition Pseudo_ZVector := list Z.

Record Pseudo_Constraint := mkPseudoConstraint
  { pconstr_vect: Pseudo_ZVector;
    pconstr_comp: Comparison;
    pconstr_val: Z}.

Definition Pseudo_Polyhedron := list Pseudo_Constraint.

(*Fixpoint is_of_length (n: nat) (pv: Pseudo_ZVector) :=
  match n, pv with
    | O, nil => true
    | _, nil
    | O, _ => false
    | S n', _ :: pv' => is_of_length n' pv'
  end.*)


(*Program Definition make_zvector n (pv: Pseudo_ZVector) : option (ZVector n) :=
  match is_of_length n pv with
    | true => Some pv
    | false => None
  end.
Next Obligation.
  generalize dependent pv.
  induction n; destruct pv; simpl; intro LENGTH; auto.
Qed.*)

Definition make_constraint n (pc: Pseudo_Constraint) : option (Constraint n):=
  do v <- make_vector n pc.(pconstr_vect);
  point (mkConstraint v pc.(pconstr_comp) pc.(pconstr_val)).



Definition make_polyhedron n (ph : Pseudo_Polyhedron) : option (Polyhedron n):=
  mmap (make_constraint n) ph.

Notation "pol1 ∩ pol2" := (Pol_intersection pol1 pol2) (at level 65).

Require Import Coqlibext.
Require Import Do_notation.
Require Import ClassesAndNotations.
Require Import Psatz.
Require Import Program.
Require Import ArithClasses.
Require Export PolyBase.

Generalizable Variable n.

(* an external caml function that generates witness for emptyness test *)
Parameter gen_emptyness_witness: forall n, Polyhedron n -> option (list Z).


Program Definition Pol_Empty_sdec_canonized n p : Semi_Decidable (Pol_Empty p):=
  match gen_emptyness_witness n p with
    | None => right _
    | Some wit => Pol_check_empty wit p
  end.

Program Definition Pol_Empty_sdec `(p: Polyhedron n) : Semi_Decidable (Pol_Empty p):=
  match Pol_Empty_sdec_canonized n (Pol_canonize p) with
    | left _ => left _
    | right _ => right  _
  end.
Next Obligation.
  unfold Pol_Empty in *.
  intros v IN. apply Pol_Included_canonize in IN. eapply wildcard'. eauto.
Qed.

Definition Pol_Included_sdec_canonized n p1 p2 (PCAN: Pol_Canonized p2)
  : Semi_Decidable (p1 ⊂ p2):=
  @Pol_Included_sdec_canonized_part n (Pol_Empty_sdec_canonized n) p1 p2 PCAN.

Definition Pol_Included_sdec n p1 p2: Semi_Decidable (p1 ⊂ p2):=
  @Pol_Included_sdec_part n (Pol_Empty_sdec_canonized n) p1 p2.

Definition M_Injective_on_Pol_sdec {n p} (m: ZMatrix n p) (pol: Polyhedron p) :=
 M_Injective_on_Pol_sdec_part Pol_Empty_sdec_canonized  m pol.


Notation "m '`is_injective_on`' pol" := (M_Injective_on_Pol m pol) (at level 10).


(*Definition is_injective_ext_on {n p} (m: zmatrix n (S p)) (pol: polyhedron p) :=
  forall v1 v2, v1 ∈ pol -> v2 ∈ pol -> m × (1 ::: v1) = m × (1 ::: v2) -> v1 = v2.


(* infix notation a la haskell. I don't think I can make a general
   notation for infix operators with `, but only specific ones*)

Notation "m '`is_injective_ext_on`' pol" := (is_injective_ext_on m pol) (at level 10).

Theorem inj_ext_inj n p (m: zmatrix n (S p)) (pol: polyhedron p):
  m `is_injective_ext_on` pol <-> (vmap vtail m) `is_injective_on` pol.
Proof.
  split; [Case "->" | Case "<-"];
  unfold is_injective_on, is_injective_ext_on;
  intros INJ * IN1 IN2 EQ;
  apply INJ; auto; clear INJ IN1 IN2;
  unfold prod_mat_vect in *; inv EQ;
  apply vect_eq; simpl;
  dest_vect m; simpl in *; clear Lm;
  induction m; simpl in *; auto;
  inv H0; f_equal; auto;
  clear - H1;
  unfold prod_vect, vtail in *; simpl in *;
  dest_vect a; destruct a; clean; simpl in *; lia.
Qed.

Program Definition mat_is_injective_ext_on_pol {n p} (m: zmatrix n (S p)) (pol: polyhedron p) :
  {m `is_injective_ext_on` pol } + {True}:=
  match mat_is_injective_on_pol (vmap vtail m) pol with
    | left _ => left _
    | right _ => right _
  end.
Next Obligation.
  rewrite inj_ext_inj. auto.
Qed.
*)

Definition poly_test1 :=
  make_polyhedron (2%nat)
  ((mkPseudoConstraint [1; -1] GE 0) :: nil).

Definition poly_test2 :=
  make_polyhedron (2%nat)
  ((mkPseudoConstraint [1; 0] GE 0)::
   (mkPseudoConstraint [0; -1] GE 0) 
   :: nil).


Program Definition res_test : bool :=
  match poly_test1, poly_test2 with
    | Some p1, Some p2 => Pol_Included_sdec 2 p2 p1
    | _, _ => !
  end.
Next Obligation.
  unfold poly_test1, poly_test2 in *. compute in H.
  eapply H; eauto.
Qed.


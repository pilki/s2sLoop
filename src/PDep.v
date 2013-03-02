(* compute the dependencies between instructions *)
Require Import Errors.
Require Import Polyhedra.
Require Import Loops.
Require Import Memory.
Require Import ArithClasses.
Require Import Permutation.
Require Import Sorted.
Require Import PLang.
Require Import Psatz.
Require Import Axioms.
Require Import Instructions.
Require Import Bounds.
Require Import Libs.
Require Import Do_notation.
Open Scope string_scope.
(*Set Implicit Arguments.*)
Open Scope Z_scope.


(*
Lemma Vcons_prod `{Numerical Num} n (v1 v2: Vector Num n) (a1 a2: Num):
  〈 a1 ::: v1, a2 ::: v2〉= (a1 * a2 + 〈v1, v2〉)%numerical.
Proof.
  reflexivity.
Qed.

Lemma Vcons_prod_Z n (v1 v2: ZVector n) (a1 a2: Z):
  〈 a1 ::: v1, a2 ::: v2〉= a1 * a2 + 〈v1, v2〉.
Proof.
  reflexivity.
Qed.

Hint Rewrite Vcons_prod Vcons_prod_Z: vect. *)

(*
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
  constructor'.
  NCase "Head".
    red. simpl. simpl_vect. reflexivity.
  NCase "Tail".
  eapply list_forall_list_forall_map; eauto.
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


Tactic Notation "remember_no_eq" constr(X) "as" ident(id) :=
  remember X as id;
  match goal with
    | H: id = X |- _ => clear H
  end.

Tactic Notation "Vdestruct" constr(v) "as" ident(hd) ident(tl) :=
  let H := fresh in
  let v' := fresh v in
  rename v into v';
  pose proof (Vcons_hd_tail v') as H;
  remember_no_eq (Vhd v') as hd;
  remember_no_eq (Vtail v') as tl;
  rewrite <- H in *;
  clear H; clear v'.


Lemma extend_polyhedron_Vtl  n (p: Polyhedron n) (v: ZVector (S n)):
  v ∈ (extend_polyhedron p) -> Vtail v ∈ p.
Proof.
  intro IN.
  Vdestruct v as a v.
  unfold Pol_In in *.
  unfold extend_polyhedron in IN.
  inv IN. clear H1.
  eapply list_forall_map_list_forall; eauto.
  clear. intros. destruct a0; unfold satisfy_constraint in *; simpl in *.
  simpl_vect in H. simpl in H. assumption.
Qed.



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

Hint Rewrite Vmap_cons Mprod_vect_cons: vect.

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
    simpl_vect. rewrite Mprod_vect_cons.
    rewrite Mprod_vect_cons. f_equal; auto.

    clear'.
    revert dependent p.
    induction' p as [|p]; intros.
    SCase "O".
      rewrite (Vect_0 v). unfold Vprod. simpl.
      unfold Matrix in *. clear'.
      dest_vects. simpl. clear'. revert m2.
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
        rewrite Mprod_vect_cons.
        rewrite Mprod_vect_cons. simpl_vect. simpl in *.
        unfold ZNum.Numerical_Num in *.
        match goal with
          | |- (?A + ?B ) * z + (?C + ?D) = _ =>
            replace ((A + B) * z + (C + D)) with
              ((A*z + C) + (B *z + D)) by lia
        end.
        f_equal; auto.
        rewrite <- Zmult_assoc.        
        rewrite <- Zmult_plus_distr_r.
        f_equal.
        Vdestruct vm2 as hdvm2 vm2.
        simpl_vect. reflexivity.
  Qed.




Module PDependencies (Import M:BASEMEM(ZNum))
  (I:INSTRS(ZNum) with Definition Value := M.Value).
  Module T := Tools(ZNum).
  Import T.

  (* find better name *)
  Definition make_poly_containing_things {dim1 dim2} {num_args1 num_args2}
    (transf1: ZMatrix num_args1 (S dim1)) (transf2: ZMatrix num_args2 (S dim2))
    (pol1: Polyhedron (S dim1)) (pol2: Polyhedron (S dim2)) 
    (def_access1: list (ZVector (S (num_args1))))
    (def_access2: list (ZVector (S (num_args2)))):
    res (Polyhedron (S dim1 + S dim2)) :=
    let n := length def_access1 in
    match make_vector n def_access1 with
    | None => Err "Make vector is broken"
    | Some access1 =>
    match make_vector n def_access2 with
    | None =>
      Err "make_poly_containing_things has been called with two accesses of different size"
    | Some access2 =>
    let etransf1 := extend_matrix transf1 in
    let etransf2 := extend_matrix transf2 in
    let M1 := Mmul access1 etransf1 in
    let M2 := Mmul access2 etransf2 in
    OK (Pol_same_image_two_matrices M1 M2 ∩ Pol_prod pol1 pol2)
    end
    end.


  Hint Unfold ZNum.Num: aliases.

  (* I really need to find better names... *)
  Lemma it_works {dim1 dim2} {num_args1 num_args2}
    (transf1: ZMatrix num_args1 (S dim1)) (transf2: ZMatrix num_args2 (S dim2))
    (pol1: Polyhedron (S dim1)) (pol2: Polyhedron (S dim2)) 
    (def_access1: list (ZVector (S (num_args1))))
    (def_access2: list (ZVector (S (num_args2))))
    (v1: ZVector dim1) (v2: ZVector dim2) pol (id:Array_Id):
    make_poly_containing_things transf1 transf2 pol1 pol2 def_access1 def_access2 =
      OK pol ->
    (1:::v1) ∈ pol1 -> (1:::v2) ∈ pol2 ->
    (1 ::: v1) +++ (1::: v2) ∉ pol ->
    translate_locs (1::: (transf1 × (1:::v1))) (id, def_access1) <>
    translate_locs (1::: (transf2 × (1:::v2))) (id, def_access2).
  Proof.
    intros * MAKE_OK IN1 IN2 NOTIN. intro EQ. apply NOTIN; clear NOTIN.
    unfold make_poly_containing_things in MAKE_OK.
    repeat prog_match_option; clean.
    apply Pol_Included_intersertion;[| apply Pol_In_In_prod; auto].
    apply Pol_same_image_In_SI2.
    repeat (rewrite Mmul_prod_assoc).

    unfold translate_locs in EQ. inv EQ.
    repeat match goal with
             | H: _ |- _ => apply make_vector_open in H
           end.
    rewrite <- Heqo0 in *. clear Heqo0. clear def_access2.
    repeat rewrite extend_matrix_correct.
    unfold Mprod_vect at 1. unfold Mprod_vect at 3.
    apply PVeq_Veq. simpl.  unalias in *.  rewrite <- H0.
    f_equal. assumption.
  Qed.

*)

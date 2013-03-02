(* Boxed Polyhedra *)

Require Import Libs.
Require Import Errors.
Require Import Polyhedra.
Require Import Loops.
Require Import Memory.
Require Import ArithClasses.
Require Import Permutation.
Require Import Sorted.
Open Scope string_scope.
(*Set Implicit Arguments.*)
Open Scope nat_scope.



(* set the n-th parameter to 1, and the rest to 0 *)
Program Definition nth_param_at_1 depth nbr_global_parameters n
  : ZVector (depth + nbr_global_parameters) :=
  let aux :=
    (* the function will be used only in the case where n <
       nbr_global_parameters. But it is a pain to pass the prove as an argument,
       so we "build" it locally. This is not a problem because this
       function is only used in specification (no performance
       constraint) *)
    if lt_dec n nbr_global_parameters then
      ((V0 n) +++ (1%Z ::: V0 (nbr_global_parameters - S n)) <:: Vector nbr_global_parameters)
    else
    (* wrong usage. It might be "cleaner" to return an option type,
       but more painful too*)
      (V0 nbr_global_parameters) in
  V0 depth +++ aux.
Next Obligation.
  omega.
Qed.


Lemma nth_param_at_1_correct_0: forall depth nbr_global_parameters n p,
  n < nbr_global_parameters -> p <> (depth + n) ->
  Vnth (nth_param_at_1 depth nbr_global_parameters n) p = 0%Z.
Proof.
  intros * INF DIFF.
  unfold nth_param_at_1.
  destruct (lt_dec n nbr_global_parameters); [|omegaContradiction].

  destruct (lt_dec p depth); simpl_vect; auto.
  Case "depth <= p".
    replace p with (depth + (p - depth)) in *; [|omega]. 
    simpl_vect.
    remember (p-depth) as p' in *. clear Heqp'.
    destruct (lt_eq_lt_dec p' n) as [[|]|]; try omegaContradiction; simpl_vect; auto.
    SCase "n < p".
      replace p' with (n + S (p' - n - 1)) by omega.
      simpl_vect; auto.
Qed.

Lemma nth_param_at_1_correct_1: forall depth nbr_global_parameters n,
  n < nbr_global_parameters ->
  Vnth (nth_param_at_1 depth nbr_global_parameters n) (depth + n) = 1%Z.
Proof.
  intros *  INF.
  unfold nth_param_at_1.
  destruct (lt_dec n nbr_global_parameters); [|omegaContradiction].
  simpl_vect.
  clear INF l.
  remember (nbr_global_parameters - S n) as m. clear Heqm.
  unfold_vect. simpl.
  induction' n as [|n]; auto.
Qed.




(* a constraint that only says the n th param must be equal to x *)

Definition constraint_nth_param depth nbr_global_parameters n x:=
  {| constr_vect := nth_param_at_1 depth nbr_global_parameters n;
     constr_comp := EQ;
     constr_val := x|}.


(* move to lib *)


  
(* if a vector satisfies the constraint, its nth param has value x *)
Lemma satisfies_constraint_nth_param_1:
  forall depth nbr_global_parameters n (INF: n< nbr_global_parameters) x v,
  satisfy_constraint v (constraint_nth_param depth nbr_global_parameters n x) ->
  Vnth (Vdrop_p depth v) n = x.
Proof.
  intros * INF * SATISF.

  unfold satisfy_constraint, constraint_nth_param, nth_param_at_1 in *. simpl in *.
  rewrite <- (Vapp_take_drop _ _ v) in SATISF.
  simpl_vect in *.

  remember (Vdrop_p depth v) as v'. clear Heqv'.
  clear v.

  destruct (lt_dec n nbr_global_parameters); try contradiction.


  assert ((n + (S (nbr_global_parameters - S n)) = nbr_global_parameters)%nat) by omega.
  dest_vects.  simpl_vect in *. simpl in *.
  subst.

  clear INF.
  revert dependent v'.
  induction' n as [|n']; simpl in *; intros.
  Case "O".
    destruct v'.
    simpl in *; omega.
    rewrite PVprod_repeat_0. 
    simpl.
    destruct z; omega.

  Case "S n'".
    destruct v'.
    simpl in *; omega.
    simpl. apply IHn'; auto.
    simpl in *. omega.
Qed.

(* if the n-th param is x, then the vector statifies the constraint *)
Lemma satisfies_constraint_nth_param_2: forall depth nbr_global_parameters n (INF: n < nbr_global_parameters) x v,
  Vnth (Vdrop_p depth v) n = x ->
  satisfy_constraint v (constraint_nth_param depth nbr_global_parameters n x).
Proof.
  intros * INF * ACCESS.

  unfold satisfy_constraint, constraint_nth_param, nth_param_at_1 in *. simpl in *.
  rewrite <- (Vapp_take_drop _ _ v). simpl_vect.

  remember (Vdrop_p depth v) as v'. clear Heqv'.
  clear v.

  destruct (lt_dec n nbr_global_parameters);[|contradiction].

(*  assert ((n + (S (nbr_global_parameters - S n)) = nbr_global_parameters)%nat) by omega.*)

  dest_vects; simpl_vect in *; simpl in *. clear l.

  remember ((nbr_global_parameters - S n)%nat) as m. clear Heqm. subst.

  revert dependent v'.
  induction' n as [|n]; intros.
  Case "O".
    simpl in *.
    destruct v'; simpl in *; auto.
    rewrite PVprod_repeat_0. destruct z; omega.

  Case "S n".
    simpl.
    destruct v'; simpl in *; auto.
    apply IHn. omega.
Qed.

(* all numbers strictly smaller than len *)
Fixpoint sequence_lesser len : list nat :=
  match len with
    | O => []
    | S len' => len' :: sequence_lesser len'
  end.


(*Notation "pol1 ∩ pol2" := (inter_poly pol1 pol2) (at level 65).*)

Definition poly_containing_params_aux {nbr_global_parameters: nat} depth
  (params: ZVector nbr_global_parameters)
   : nat -> Constraint (depth + nbr_global_parameters) :=
  fun p =>
    constraint_nth_param depth nbr_global_parameters p
    (Vnth params p).

(* the polyhedron containing all vectors v of size depth + nbr_global_parameters
   such that drop_v depth v = params *)

Definition poly_containing_params {nbr_global_parameters depth: nat}
  (params: ZVector nbr_global_parameters):
  Polyhedron (depth + nbr_global_parameters) :=
  map (poly_containing_params_aux depth params)
  (sequence_lesser nbr_global_parameters).

(* please note that those functions have pretty bad complexity, but
   are not meant to be executed. Closure containing them might be
   created at run time but (if I did nothing wrong :)) should never be
   run *)


Lemma map_sequence_lesser_forall_1: forall B (f: nat -> B) P n,
  list_forall P (map f (sequence_lesser n)) ->
  forall m, m < n -> P (f m).
Proof.
  intros *.
  induction' n as [|n]; intros.
  Case "O".
    omegaContradiction.

  Case "S n".
  simpl in *. inv H.
  dest m == n.
    SCase "m = n".
    subst. auto.
    SCase "m <> n".
    apply IHn; auto. omega.
Qed.

Lemma map_sequence_lesser_forall_2: forall B (f: nat -> B) (P: B -> Prop) n,
  (forall m, m < n -> P (f m)) ->
  list_forall P (map f (sequence_lesser n)).
Proof.
  intros *.
  induction' n as [|n]; intros FORALL.
  Case "O".
    simpl. constructor.

  Case "S n".
  simpl. constructor.
  apply FORALL. omega.
  apply IHn. intros. apply FORALL. omega.
Qed.

Lemma poly_containing_params_list_forall_1 {nbr_global_parameters depth: nat}
  (params: ZVector nbr_global_parameters) P:
  list_forall P (poly_containing_params params) ->
  forall x (INF: (x < nbr_global_parameters)%nat),
    P (poly_containing_params_aux depth params x).
Proof.
  intros. eapply (map_sequence_lesser_forall_1 _ _ P); eauto.
Qed.

Lemma poly_containing_params_list_forall_2 {nbr_global_parameters depth: nat}
  (params: ZVector nbr_global_parameters) (P: _ -> Prop):
  (forall x (INF: (x < nbr_global_parameters)%nat),
    P (poly_containing_params_aux depth params x)) ->
  list_forall P (poly_containing_params params).
Proof.
  intros. eapply (map_sequence_lesser_forall_2 _ _ P); eauto.
Qed.



(* correctness of poly_containing_params *)
Lemma poly_containing_params_drop_1 {nbr_global_parameters depth: nat}
  (params: ZVector nbr_global_parameters) (v: ZVector (depth + nbr_global_parameters)):
  v ∈ poly_containing_params params -> Vdrop_p depth v = params.
Proof.
  intros IN.
  apply Vnth_inj.
  intros.
  apply (satisfies_constraint_nth_param_1 _ _ _ H).
  unfold Pol_In, poly_containing_params, poly_containing_params_aux in IN.
  eapply map_sequence_lesser_forall_1 in IN; eauto.
Qed.

Lemma poly_containing_params_drop_2 {nbr_global_parameters depth: nat}
  (params: ZVector nbr_global_parameters) (v: ZVector (depth + nbr_global_parameters)):
  Vdrop_p depth v = params -> v ∈ poly_containing_params params.
Proof.
  intros EQ.
  unfold Pol_In, poly_containing_params, poly_containing_params_aux in *.
  apply map_sequence_lesser_forall_2.
  intros. apply satisfies_constraint_nth_param_2; auto.
  subst. reflexivity.
Qed.


(* the important definition *)

(* add to a polyhedron pol the extra constraint that the nbr_global_parameters
   last elements of the vector are equal to params by taking the
   intersection with poly_containing_params*)

Definition constrain_params {nbr_global_parameters depth: nat}
  (params: ZVector nbr_global_parameters)
  (pol: Polyhedron (depth + nbr_global_parameters)):
  Polyhedron (depth + nbr_global_parameters) :=
  poly_containing_params params ∩ pol.



(* any vector in pol that ends with params is in constain_params *)
Lemma in_pol_in_constrain_params: forall (nbr_global_parameters depth: nat)
  (params: ZVector nbr_global_parameters) (pol: Polyhedron (depth + nbr_global_parameters)) v,
  (v +++ params) ∈ pol -> (v +++ params) ∈ (constrain_params params pol).
Proof.
  intros * IN.
  unfold constrain_params.
  apply Pol_Included_intersertion; auto.
  apply poly_containing_params_drop_2.
  apply Vdrop_p_app.
Qed.

Lemma in_pol_in_constrain_params_Vdrop:  forall (nbr_global_parameters depth: nat)
  (params: ZVector nbr_global_parameters) (pol: Polyhedron (depth + nbr_global_parameters)) v,
  v ∈ pol -> Vdrop_p depth v = params -> v ∈ (constrain_params params pol).
Proof.
  intros * IN DROP.
  unfold constrain_params. apply Pol_Included_intersertion; auto.
  apply poly_containing_params_drop_2. apply DROP.
Qed.

Lemma in_constrain_param_in_pol: forall (nbr_global_parameters depth: nat)
  (params: ZVector nbr_global_parameters) (pol: Polyhedron (depth + nbr_global_parameters)),
  (constrain_params params pol) ⊂ pol.
Proof.
  intros.
  unfold constrain_params in *.
  apply Pol_intersection_Included_r.
Qed.

Lemma in_constrain_param_suffix: forall (nbr_global_parameters depth: nat)
  (params: ZVector nbr_global_parameters) (pol: Polyhedron (depth + nbr_global_parameters)) v,
  v ∈ (constrain_params params pol) ->
  exists prefix, v = prefix +++ params.
Proof.
  intros.
  exists (Vtake_p depth v).
  rewrite <- (Vapp_take_drop _ _ v) at 1.
  f_equal; auto.
  apply poly_containing_params_drop_1.
  unfold constrain_params in H.
  apply Pol_intersection_Included_l in H. auto.
Qed.



(* a boxed Polyhedron is a Polyhedron such that when the params are
   fixed, it contains a finite number of elements. Those elements are
   available through the bp_elts function. (in fact, only the prefix
   of length depth is returned, the "real" elements can be obtained by
   concatenation with the params) *)

Record Boxed_Polyhedron nbr_global_parameters depth := mk_Boxed_Polyhedron
  { bp_poly: Polyhedron (depth + nbr_global_parameters);
    bp_elts: forall params: ZVector nbr_global_parameters, list (ZVector depth);

    (* each element is returned only once *)
    bp_elts_NoDup: forall params, NoDup (bp_elts params);

    (* all the elements and only the elements are returned *)
    bp_in_elts_in_poly: forall (vect: ZVector depth) params,
      In vect (bp_elts params) ->
      (vect+++params) ∈ bp_poly;
    bp_in_poly_in_elts: forall (vect: ZVector (depth + nbr_global_parameters)) params,
      vect ∈ (constrain_params params bp_poly) ->
      In (Vtake_p depth vect) (bp_elts params)}.

Implicit Arguments bp_poly [[nbr_global_parameters] [depth]].
Implicit Arguments bp_elts [[nbr_global_parameters] [depth]].

Lemma bp_in_elts_in_poly_constrain (nbr_global_parameters depth : nat)
  (b : Boxed_Polyhedron nbr_global_parameters depth)
  (vect : ZVector depth) (params : ZVector nbr_global_parameters):
  In vect (bp_elts b params) ->
  (vect+++params) ∈ (constrain_params params b.(bp_poly)).
Proof.
  intros.
  unfold constrain_params.
  apply Pol_Included_intersertion.
  apply poly_containing_params_drop_2. simpl_vect. reflexivity.
  apply bp_in_elts_in_poly. auto.
Qed.

Add LoadPath "../from_compcert".

Require Import AST.
Require Import Memory.
(*Require Import Values.*)
Require Import Maps.
Require Import NArith.
Require Import ZArith.
Require Import List.
Require Import Program.
Require Import Coqlibext.
Require Import ArithClasses.
Require Import Integers.
Require Import ClassesAndNotations.
Require Import Do_notation.
Require Import Psatz.
Require Import CeildFloord.
Open Scope numerical_scope.


Set Implicit Arguments.

(* some stuff used in several modules *)
Module Tools (N:NUMERICAL).
  Import N.
  Existing Instance Numerical_Num.
  Open Scope numerical_scope.
  Notation "'NVector'" := (Vector Num).
  Notation "'NMatrix'" := (Matrix Num).
  Section NBRPARAMS.
    (* number of global parameters of a program *)
  Variable nbr_global_parameters: nat.
  Definition Global_Parameters := NVector nbr_global_parameters.
  Variable global_params: Global_Parameters.
  (* the outer iterators (say k ::: j ::: i) *)
  Definition Iterators depth := NVector depth.
  (* an extended context (say 1 ::: k ::: j ::: i ::: params) *)
  Definition Context global_depth :=
    NVector global_depth.
  Definition Context_ext global_depth :=
    NVector (S global_depth).
  Definition extend_context {global_depth} (ctxt: Context global_depth)
    : Context_ext global_depth := 1 ::: ctxt.
(*  Definition make_context_ext {depth} (iters:Iterators depth):
    Context_ext depth := 1 ::: (iters +++ global_params).*)
  (* the arguments of an instruction, obtain from the extended
     environment multiplied by the matrix *)
  Definition Arguments n := NVector n.
  Definition Arguments_ext n := NVector (S n).
  Definition extend_arguments {n} (args: Arguments n):
    Arguments_ext n := 1 ::: args.
  (* translate_locs takes an extended arguments and a list of read locs and build 
     a cell_id *)
  Definition translate_locs {csi} (ectxt: Arguments_ext csi)
    (p: Array_Id * list (NVector (S csi))): Cell_Id Num:=
    {| array := fst p;
       cell := List.map (fun v =>〈v, ectxt〉) (snd p)|}.
  End NBRPARAMS.
  Definition bound global_depth :=
    not_empty_list (Num * (NVector (S (global_depth)))).

  Definition bound_to_not_emptyNum global_depth (b: bound global_depth):
    not_empty_list (Num * NVector (S global_depth)):=
    b.

  Global Coercion bound_to_not_emptyNum: bound >-> not_empty_list.

  (* those two definitions are part of the TCB (they define the
     semantics of Loop), but they are far from being trivially
     correct. They are, nevertheless, proved for Num = Z below *)

  Definition eval_lower_bound {global_depth}
    (ctxt : Context global_depth)
    (lower_bound: bound global_depth) :=
    let ectx := extend_context ctxt in
    do l <- not_empty_mmap (fun p: (Num * (NVector (S global_depth))) => 
        let (k, v) := p in Aceild 〈ectx, v〉 k) lower_bound;
    Some (Amax_list l).

  Definition eval_upper_bound {global_depth}
    (ctxt : Context global_depth)
    (upper_bound: bound global_depth) :=
    let ectx := extend_context ctxt in
    do l <- not_empty_mmap (fun p: (Num * (NVector (S global_depth))) =>
        let (k, v) := p in Afloord 〈ectx, v〉 k) upper_bound;
    Some (Amin_list l).
End Tools.


Module ZTools := Tools(ZNum).
Import ZTools.


(*Definition bound_to_not_emptyZNum global_depth (b: bound global_depth):
  not_empty_list (ZNum.Num * NVector (S global_depth)):=
  b.

Coercion bound_to_not_emptyZNum: bound >-> not_empty_list.

Definition bound_to_not_emptyZ global_depth (b: bound global_depth):
  not_empty_list (Z * NVector (S global_depth)):=
  b.

Coercion bound_to_not_emptyZ: bound >-> not_empty_list.*)


Section GLOBALDEPTH.
  Open Scope Z_scope.
  Context {nbr_params: nat}.

  Local Notation "'bound'" := (bound nbr_params).
  Implicit Types b lb ub: bound.

  Definition bound_constr_correct (bc: ZNum.Num * NVector (S nbr_params))
    := 0 < fst bc.
  Hint Unfold bound_constr_correct: autounfold.

  Program Definition check_bound_constr
    (bc: ZNum.Num * NVector (S nbr_params)) :
    { bound_constr_correct bc }+
    { ~bound_constr_correct bc } :=
    match fst bc with
      | Zpos _ => left _
      | Z0 => right _
      | Zneg _ => right _
    end.
    Next Obligation.
      unfold*; simpl in *; subst; compute; reflexivity.
    Qed.
    Next Obligation.
      unfold *; simpl in *; subst; compute; intro; congruence.
    Qed.
    Next Obligation.
      unfold *; simpl in *; subst; compute; intro; congruence.
    Qed.

  Definition bound_correct (bnd: bound) :=
    list_forall bound_constr_correct bnd.
  Hint Unfold bound_correct: autounfold.

  Definition check_bound (bnd: bound)
    : {bound_correct bnd} +
      {~ bound_correct bnd} :=
    list_forall_dec check_bound_constr bnd.


  (* under a certain environment, z is greater or equal than the constraint,

     (used when talking about lower_bound )
     *)
  Definition ge_bound_constraint (ectxt: Context_ext nbr_params)
    (z:Z) (constr: Z * NVector (S nbr_params)) :=
    let (x, v) := constr in
    〈ectxt, v〉<= x * z.

  Lemma gt0_ge0: forall z, 0 < z -> 0 <= z.
  Proof. intros. lia. Qed.
  Hint Resolve gt0_ge0.

  Lemma ge_bound_constraint_trans (ectxt: Context_ext nbr_params)
    (constr: Z * NVector (S nbr_params)) (z1 z2:Z):
    bound_constr_correct constr ->
    z1 <= z2 ->
    ge_bound_constraint ectxt z1 constr -> ge_bound_constraint ectxt z2 constr.
  Proof.
    unfold*.
    unfold ge_bound_constraint. destruct constr. simpl.
    intros.
    assert (z * z1 <= z * z2).
    apply Zmult_le_compat_l; auto. simpl in *; omega.
  Qed.


  (* under a certain environment, z is lower or equal than the constraint 

     for upper bounds *)
  Definition le_bound_constraint (ectxt: Context_ext nbr_params)
    (z:Z) (constr: Z * NVector (S nbr_params)) :=
    let (x, v) := constr in
    x * z <= 〈ectxt, v〉.

  Lemma le_bound_constraint_trans (ectxt: Context_ext nbr_params)
    (constr: Z * NVector (S nbr_params)) (z1 z2:Z):
    bound_constr_correct constr ->
    z2 <= z1 ->
    le_bound_constraint ectxt z1 constr -> le_bound_constraint ectxt z2 constr.
  Proof.
    unfold le_bound_constraint. destruct constr. simpl.
    intros.
    assert (z * z2 <= z * z1)%Z.
    apply Zmult_le_compat_l; auto. omega.
  Qed.


  Definition ge_bound (ctxt: Context nbr_params)
    (lower_bound: bound) z : Prop :=
    let ectxt := extend_context ctxt in
    list_forall (ge_bound_constraint ectxt z) lower_bound.


  Lemma ge_bound_trans (ctxt: Context nbr_params)
    (lower_bound: bound) z1 z2:
    bound_correct lower_bound ->
    z1 <= z2 ->
    ge_bound ctxt lower_bound z1 -> ge_bound ctxt lower_bound z2.
  Proof.
    unfold ge_bound. unfold *.
    destruct lower_bound as (hd, tl). simpl.
    remember (hd:: tl) as l. clear Heql hd tl.
    induction l; intros; auto.
    inv H1. inv H.
    constructor; eauto using @ge_bound_constraint_trans.
  Qed.

  Definition le_bound (ctxt: Context nbr_params)
    (upper_bound: bound) z : Prop :=
    let ectxt := extend_context ctxt in
    list_forall (le_bound_constraint ectxt z) upper_bound.

  Lemma le_bound_trans (ctxt: Context nbr_params)
    (upper_bound: bound) z1 z2:
    bound_correct upper_bound ->
    z2 <= z1 ->
    le_bound ctxt upper_bound z1 -> le_bound ctxt upper_bound z2.
  Proof.
    unfold le_bound. unfold *.
    destruct upper_bound as (hd, tl). simpl.
    remember (hd:: tl) as l. clear Heql hd tl.
    induction l; intros; auto.
    inv H1. inv H.
    constructor; eauto using @le_bound_constraint_trans.
  Qed.

  (* to lib *)
  Lemma not_empty_mmap_option {C D} (f: C -> option D)
    (nl1: not_empty_list C) (nl2: not_empty_list D):
    not_empty_mmap f nl1 = Some nl2 ->
    list_forall2 (fun d od => Some d = od) nl2 (map f nl1).
  Proof.
    unfold not_empty_mmap. intros.
    destruct nl1 as (hd1, tl1). prog_dos.
    simpl. constructor; auto using @mmap_option.
  Qed.

  (* the result of eval_lower_bound in in the set of value satisfying
     ge_bound *)

  Lemma eval_lower_bound_is_ge (ctxt: Context nbr_params)
    (lower_bound: bound) z:
    eval_lower_bound ctxt lower_bound = Some z ->
    ge_bound ctxt lower_bound z.
  Proof.
    intro EVAL_LOWER.
    unfold eval_lower_bound in EVAL_LOWER.
    prog_do; clean. apply not_empty_mmap_option in Heq_do.

    unfold ge_bound.
    simpl in *.
    destruct lower_bound as (hd_lb, tl_lb).
    simpl in *.
    inv Heq_do. destruct l as (hd_l, tl_l); simpl in *. clean. inv H.
    pose proof (Amax_list_ge_forall (hd_l, tl_l)).

    remember (Amax_list (hd_l, tl_l)) as amax. clear Heqamax.
    inv H.
    constructor.
    Case "head".
      unfold ge_bound_constraint. destruct hd_lb. simpl.
      eapply ceildZ_bound2; eauto.
    Case "tail".
      clear dependent hd_l.
      revert dependent tl_l.
      revert dependent tl_lb.
      induction' tl_lb as [|hd tl]; simpl; intros; clean; auto.
      SCase "cons hd tl".
        inv H3. inv H5. clean.
        constructor.
        SSCase "head".
          unfold ge_bound_constraint. destruct hd. simpl.
          eapply ceildZ_bound2; eauto.
        SSCase "tl".
          eapply IHtl; eauto.
  Qed.

  Lemma eval_lower_bound_bound_correct (ctxt: Context nbr_params)
    (lower_bound: bound) z:
    eval_lower_bound ctxt lower_bound = Some z ->
    bound_correct lower_bound.
  Proof.
    unfold *.
    intro H.
    unfold eval_lower_bound in H.
    prog_do; clean.
    apply not_empty_mmap_option in Heq_do.
    destruct lower_bound. destruct l. simpl in *.
    inv Heq_do.
    constructor.
    Case "head".
      destruct p; simpl in *. clean.
      unfold ceildZ in H2; destruct n0; clean.
    Case "tail".
      revert dependent l. clear H2.
      induction' l0; intros; eauto.
      simpl in *. inv H4.
      constructor; eauto.
      destruct a; simpl in *; clean; unfold ceildZ in *. destruct n0; clean.
  Qed.

  Lemma bound_correct_eval_lower_bound_is_some (ctxt: Context nbr_params)
    (lower_bound: bound):
    bound_correct lower_bound ->
    is_some (eval_lower_bound ctxt lower_bound).
  Proof.
    unfold *.
    intro H.
    unfold eval_lower_bound.
    match goal with
      | |- context[not_empty_mmap ?f ?l] =>
        assert (is_some (not_empty_mmap f l))
    end.
      apply not_empty_mmap_is_some.
      eapply list_forall_imply; [|eauto].
      intros. simpl.
      destruct a as ([|?|?],?); simpl in *; auto; compute in H0; inv H0.
    inv H0. simpl.
    rewrite <- H2. simpl_do; auto.
  Qed.



  (* the result of eval_lower_bound is the smallest of the set of
     value satisfying ge_bound *)


  Lemma ge_bound_ge_lower_bound (ctxt: Context nbr_params)
    (lower_bound: bound) z:
    eval_lower_bound ctxt lower_bound = Some z ->
    forall x, ge_bound ctxt lower_bound x -> z <= x.
  Proof.
    intro EVAL_LOWER.
    unfold eval_lower_bound in EVAL_LOWER.
    prog_do; clean. apply not_empty_mmap_option in Heq_do.

    unfold ge_bound.
    simpl in *.
    destruct lower_bound as (hd_lb, tl_lb).
    simpl in *.
    inv Heq_do. destruct l as (hd_l, tl_l); simpl in *. clean. inv H.

    intros x LFL.
    pose proof (@ge_forall_ge_Amax_list _ _ (hd_l, tl_l)) as GAGAL. simpl in GAGAL. apply GAGAL.
    clear GAGAL.
    inv LFL.

    constructor.
    Case "head".
      unfold ge_bound_constraint in H1.
      destruct hd_lb. simpl in *.
      eapply ceildZ_bound1 in H1; eauto.
    Case "tail".
      simpl.
      clear dependent hd_l. clear dependent hd_lb.
      revert dependent tl_l.
      revert dependent tl_lb.
      induction' tl_lb as [|hd tl]; simpl in *; intros; clean; auto.
      SCase "nil".
        inv H3. constructor.
      SCase "cons hd tl".
        inv H3. inv H4. clean.
        constructor.
        SSCase "head".
          unfold ge_bound_constraint in H1.
          destruct hd. simpl in *.
          eapply ceildZ_bound1 in H1; eauto.
        SSCase "tail".
          eapply IHtl; eauto.
  Qed.

  (* this is the important proof that eval_lower_bound is not absurd *)
  Theorem ge_bound_equiv_eval_lower_bound (ctxt: Context nbr_params)
    (lower_bound: bound) z:
    eval_lower_bound ctxt lower_bound = Some z ->
    forall x, ge_bound ctxt lower_bound x <-> z <= x.
  Proof.
    intros.
    split.
    apply ge_bound_ge_lower_bound; auto.
    intros.
    assert (ge_bound ctxt lower_bound z) by
      (eapply eval_lower_bound_is_ge; eauto).
    eapply ge_bound_trans; eauto.
    eapply list_forall_imply;[|eapply eval_lower_bound_bound_correct; eauto].
    unfold *.
    simpl; intros; lia.
  Qed.



  Lemma eval_upper_bound_is_ge (ctxt: Context nbr_params)
    (upper_bound: bound) z:
    eval_upper_bound ctxt upper_bound = Some z ->
    le_bound ctxt upper_bound z.
  Proof.
    intro EVAL_UPPER.
    unfold eval_upper_bound in EVAL_UPPER.
    prog_do; clean. apply not_empty_mmap_option in Heq_do.

    unfold le_bound.
    simpl in *.
    destruct upper_bound as (hd_ub, tl_ub).
    simpl in *.
    inv Heq_do. destruct l as (hd_l, tl_l); simpl in *. clean. inv H.
    pose proof (Amin_list_le_forall (hd_l, tl_l)).

    remember (Amin_list (hd_l, tl_l)) as amin. clear Heqamin.
    inv H.
    constructor.
    Case "head".
      unfold le_bound_constraint. destruct hd_ub. simpl.
      eapply floordZ_bound2; eauto.
    Case "tail".
      clear dependent hd_l.
      revert dependent tl_l.
      revert dependent tl_ub.
      induction' tl_ub as [|hd tl]; simpl; intros; clean; auto.
      SCase "cons hd tl".
        inv H3. inv H5. clean.
        constructor.
        SSCase "head".
          unfold le_bound_constraint. destruct hd. simpl.
          eapply floordZ_bound2; eauto.
        SSCase "tl".
          eapply IHtl; eauto.
  Qed.

  Lemma le_bound_le_upper_bound (ctxt: Context nbr_params)
    (upper_bound: bound) z:
    eval_upper_bound ctxt upper_bound = Some z ->
    forall x, le_bound ctxt upper_bound x -> x <= z.
  Proof.
    intro EVAL_UPPER.
    unfold eval_upper_bound in EVAL_UPPER.
    prog_do; clean. apply not_empty_mmap_option in Heq_do.

    unfold le_bound.
    simpl in *.
    destruct upper_bound as (hd_ub, tl_ub).
    simpl in *.
    inv Heq_do. destruct l as (hd_l, tl_l); simpl in *. clean. inv H.

    intros x LFL.
    pose proof (@le_forall_le_Amin_list _ _ (hd_l, tl_l)) as LALAL. simpl in LALAL. apply LALAL.
    clear LALAL.
    inv LFL.

    constructor.
    Case "head".
      unfold le_bound_constraint in H1.
      destruct hd_ub. simpl in *.
      eapply floordZ_bound1 in H1; eauto.
    Case "tail".
      simpl.
      clear dependent hd_l. clear dependent hd_ub.
      revert dependent tl_l.
      revert dependent tl_ub.
      induction' tl_ub as [|hd tl]; simpl in *; intros; clean; auto.
      SCase "nil".
        inv H3. constructor.
      SCase "cons hd tl".
        inv H3. inv H4. clean.
        constructor.
        SSCase "head".
          unfold le_bound_constraint in H1.
          destruct hd. simpl in *.
          eapply floordZ_bound1 in H1; eauto.
        SSCase "tail".
          eapply IHtl; eauto.
  Qed.

  Lemma eval_upper_bound_bound_correct (ctxt: Context nbr_params)
    (upper_bound: bound) z:
    eval_upper_bound ctxt upper_bound = Some z ->
    bound_correct upper_bound.
  Proof.
    unfold *.
    intro H.
    unfold eval_upper_bound in H.
    prog_do; clean.
    apply not_empty_mmap_option in Heq_do.
    destruct upper_bound. destruct l. simpl in *.
    inv Heq_do.
    constructor.
    Case "head".
      destruct p; simpl in *. clean.
      unfold floordZ in H2; destruct n0; clean.
    Case "tail".
      revert dependent l. clear H2.
      induction' l0; intros; eauto.
      simpl in *. inv H4.
      constructor; eauto.
      destruct a; simpl in *; clean; unfold floordZ in *. destruct n0; clean.
  Qed.

  Lemma bound_correct_eval_upper_bound_is_some (ctxt: Context nbr_params)
    (upper_bound: bound):
    bound_correct upper_bound ->
    is_some (eval_upper_bound ctxt upper_bound).
  Proof.
    unfold *.
    intro H.
    unfold eval_upper_bound.
    match goal with
      | |- context[not_empty_mmap ?f ?l] =>
        assert (is_some (not_empty_mmap f l))
    end.
      apply not_empty_mmap_is_some.
      eapply list_forall_imply; [|eauto].
      intros. simpl.
      destruct a as ([|?|?],?); simpl in *; auto; compute in H0; inv H0.
    inv H0. simpl.
    rewrite <- H2. simpl_do; auto.
  Qed.


  Lemma le_bound_equiv_eval_upper_bound (ctxt: Context nbr_params)
    (upper_bound: bound) z:
    eval_upper_bound ctxt upper_bound = Some z ->
    forall x, le_bound ctxt upper_bound x <-> x <= z.
  Proof.
    intros.
    split.
    apply le_bound_le_upper_bound; auto.
    intros.
    assert (le_bound ctxt upper_bound z) by
      (eapply eval_upper_bound_is_ge; eauto).
    eapply le_bound_trans; eauto.
    eapply list_forall_imply;[|eapply eval_upper_bound_bound_correct; eauto].
    unfold*.
    simpl; intros; lia.
  Qed.


End GLOBALDEPTH.

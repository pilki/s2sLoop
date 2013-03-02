Require Import Libs.
Require Import Polyhedra.
Require Import Loops.
Require Import Memory.
Require Import ArithClasses.
Require Import Permutation.
Require Import Sorted.
Require Import PLang.
Require Import CeildFloord.
Require Import Psatz.
Require Import Instructions.
Require Import Bounds.
Require Import BoxedPolyhedra.
Require Import TimeStamp.
Open Scope string_scope.

Generalizable Variables nbr_params depth.


Module Extract (Import M:BASEMEM(ZNum))
  (I:INSTRS(ZNum) with Definition Value := M.Value).
  Module L := Semantics(ZNum)(M)(I).
  Import L.
  Import T.
  Module P := PSemantics M I.
  Import P.
  Open Scope Z_scope.

  Definition not_implemented {A:Type} : res A :=
    Err "Not Implemented".

  Definition res_of_option {A:Type} (oa: option A) (err: String.string) : res A :=
    match oa with
      | None => Err err
      | Some a => OK a
    end.

  Definition instruction_not_found :=
    "The instruction is not linked to any instruction".

  Definition wrong_length :=
    "The vector cannot be build because the lenght is incorrect".

  Program Definition point_boxed_polyhedron (global_depth: nat) :
    Boxed_Polyhedron global_depth 0:=
    {| bp_poly := [];
       bp_elts := (fun _ => [V0 0])|}.
  Next Obligation.
    Case "bp_elts_NoDup".
    constructor; auto. constructor.
  Qed.
  Next Obligation.
    Case "bp_in_elts_in_poly".
    unfold constrain_params.
    unfold constrain_params.
(*    apply Pol_Included_intersertion; auto.
    apply poly_containing_params_drop_2.
    apply Vdrop_p_app.*)
    unfold Pol_In. constructor.
  Qed.
  Next Obligation.
    Case "bp_in_poly_in_elts".
    left. apply PVeq_Veq. reflexivity.
  Qed.

(*  Program Definition ptree_get {A} (i: positive) (m: PTree.t A) :
    {a:A | m ! i = Some a}+{ m ! i = None} :=
    match m ! i with
      | None => inright _ _
      | Some a => inleft _ a
    end.*)

  Definition raise_time_stamp {global_depth: nat} (pos: Z)
    (pi: Polyhedral_Instruction global_depth)
    : Polyhedral_Instruction global_depth :=
      {| pi_instr := pi.(pi_instr);
         pi_depth := pi.(pi_depth);
         pi_poly := pi.(pi_poly);
         pi_schedule := (pos ::: V0 (pi.(pi_depth) + global_depth)) :: pi.(pi_schedule);
         pi_transformation := pi.(pi_transformation)|}.




  (* let's try dependent types horrors *)

  Definition cast_list {A: nat -> Type} {n p: nat} (EQnp: p= n)
    (l: list (A n)) : list (A p).
  Proof.
    rewrite <- EQnp in l. exact l.
  Defined.

  Definition cast_A {A: nat -> Type} {n p: nat} (EQnp: p = n)
    (a: (A n)) : (A p).
  Proof.
    rewrite <- EQnp in a; exact a.
  Defined.

  Lemma cast_list_cast_A {A: nat -> Type} {n p: nat} (EQnp: p = n)
    (l: list (A n)):
    cast_list EQnp l = map (cast_A EQnp) l.
  Proof.
    induction' l as [|a l].
    Case "@nil".
      destruct EQnp. reflexivity.
    Case "cons a l".
      simpl.
      rewrite <- IHl. clear IHl.
      destruct EQnp. simpl. reflexivity.
  Qed.

  Definition plus_nSm_Snm n m := eq_sym (plus_Snm_nSm n m).

  Definition cast_polyhedron {nbr_global_parameters depth}
    (pol: Polyhedron (depth + (S nbr_global_parameters))) :
    Polyhedron ((S depth) + nbr_global_parameters):=
    cast_list (plus_Snm_nSm _ _) pol.

  Definition cast_constr {nbr_global_parameters depth}
    (constr: Constraint (depth + (S nbr_global_parameters))) :
    Constraint ((S depth) + nbr_global_parameters) :=
    cast_A (plus_Snm_nSm _ _) constr.

  Lemma cast_poly_cast_constr nbr_global_parameters depth
    (pol: Polyhedron (depth + (S nbr_global_parameters))):
    cast_polyhedron pol = map cast_constr pol.
  Proof.
    apply cast_list_cast_A.
  Qed.

  Ltac dest_eq_rect :=
    match goal with
      | |- context[eq_rect_r _ _ ?H] =>
        match H with
          | eq_refl => fail 1
          | _ => destruct H
        end
    end.




  Lemma satify_cast_constraint nbr_global_parameters depth
    (v1 : ZVector depth) (v2: ZVector nbr_global_parameters) z constr:
    satisfy_constraint (v1 +++ z ::: v2) constr <->
    satisfy_constraint ((v1 :::: z) +++ v2) (cast_constr constr).
  Proof.
    destruct constr.
    unfold satisfy_constraint in *. simpl in *.
    unfold cast_constr, cast_A.
    match goal with
      | |- satisfy_comparison ?z ?c ?v <->
        satisfy_comparison ?z' ?c' ?v' =>
        assert' (z = z') as ZEQ;[|
        End_of_assert ZEQ;
        assert' (c = c') as CEQ;[|
        End_of_assert CEQ;
        assert' (v = v') as VEQ]]
    end.
    SCase "Assert: ZEQ".
      clear.
      unfold Vprod. dest_vects.
      dest_eq_rect.
      simpl. f_equal.
      clear.
      induction v1; simpl; auto. f_equal; auto.
    SCase "Assert: CEQ".
      clear. dest_eq_rect. reflexivity.
    SCase "Assert: VEQ".
      clear. dest_eq_rect. reflexivity.
    End_of_assert VEQ.
    split; intro; congruence.
  Qed.


  Lemma Pol_In_cast_polyhedron nbr_global_parameters depth
    (v1 : ZVector depth) (v2: ZVector nbr_global_parameters) z pol:
    v1 +++ (z ::: v2) ∈ pol <->
    (v1 :::: z) +++ v2 ∈ (cast_polyhedron pol).
  Proof.
    rewrite cast_poly_cast_constr.
    unfold Pol_In.
    induction' pol as [|constr pol]; simpl; intros; auto.
    Case "@nil".
      split; intros; constructor.
    Case "cons constr pol".
    destruct IHpol.
    split'; intros.
    SCase "->".
      inv H1. constructor; auto.
      apply satify_cast_constraint; auto.
    SCase "<-".
      inv H1. constructor; auto.
      apply satify_cast_constraint; auto.
  Qed.


      


  (* list of Z between lb and ub *)

  Lemma nat_of_Z_Zabs_nat: forall z, 0 <= z ->
    nat_of_Z z = Zabs_nat z.
  Proof.
    intros z ABS.
    destruct z; try reflexivity.
    compute in ABS. exfalso. auto.
  Qed.

  Require Import Recdef.
  Function list_of_Z_between_aux (ub lb:Z) {measure (fun lb => nat_of_Z ((ub - lb) + 1)) lb}: list Z:=
    if Z_le_dec lb ub then
      lb :: list_of_Z_between_aux ub (Zsucc lb)
    else
      [].
    intros. clear teq.
    unfold Zsucc.
    rewrite nat_of_Z_Zabs_nat; [|lia].
    rewrite nat_of_Z_Zabs_nat; [|lia].
    zify. lia.
  Qed.

  Definition list_of_Z_between lb ub := list_of_Z_between_aux ub lb.


  Lemma list_of_Z_between_correct: forall lb ub z,
    In z (list_of_Z_between lb ub) <-> lb <= z <= ub.
  Proof.
    intros ? ?. unfold list_of_Z_between.
    functional induction (list_of_Z_between_aux ub lb); intros.
    Case "lb <= ub".
    destruct' (z == lb).
    SCase "z = lb".
      subst. split; simpl; intros; auto. lia.
    SCase "z <> lb".
      split; intros.

      simpl in H.
      destruct H; try congruence;
      destruct (IHl z) as [TRI _];
      specialize (TRI H). unfold Zsucc in *. lia.

      simpl. right. apply IHl. unfold Zsucc. lia.

    Case "lb > ub".
    simpl. split; intro; clean. lia.
  Qed.


  Lemma rewrite_list_of_Z_between_le: forall lb ub, lb <= ub ->
    list_of_Z_between lb ub = lb :: list_of_Z_between (Zsucc lb) ub.
  Proof.
    intros. unfold list_of_Z_between.
    rewrite list_of_Z_between_aux_equation.
    dest_if_goal; auto.
    lia.
  Qed.

  Lemma rewrite_list_of_Z_between_gt: forall lb ub, lb > ub ->
    list_of_Z_between lb ub = [].
  Proof.
    intros. unfold list_of_Z_between.
    rewrite list_of_Z_between_aux_equation.
    dest_if_goal; auto.
    lia.
  Qed.



  Definition constraint_of_lower_bound_constr {nbr_params}
    (constr: ZNum.Num * NVector (S nbr_params))
     : Constraint (S nbr_params):=
    {| constr_vect := fst constr ::: (-- (Vtail (snd constr)));
       constr_comp := GE ;
       constr_val := Vhd (snd constr)|}.


  Lemma constraint_of_lower_bound_constr_correct {nbr_params}
    (constr: ZNum.Num * NVector (S nbr_params)):
    forall z (ctxt: Context nbr_params),
      ge_bound_constraint (extend_context ctxt) z constr <->
      satisfy_constraint (z:::ctxt) (constraint_of_lower_bound_constr constr).
  Proof.
    intros.
    destruct constr as (x, v).
    unfold constraint_of_lower_bound_constr, ge_bound_constraint,
      satisfy_constraint, extend_context; simpl.
    rewrite <- (Vcons_hd_tail v).
    repeat rewrite Vprod_Vcons. simpl_vect.
    simpl. rewrite Vprod_comm. lia.

    constructor. exact 0.
  Qed.


  Definition polyhedron_of_lower_bound {nbr_params}
    (lower_bound: bound nbr_params)
      : Polyhedron (S nbr_params) :=
      map constraint_of_lower_bound_constr lower_bound. 


  Lemma polyhedron_of_lower_bound_correct {nbr_params}
    (lower_bound: bound nbr_params):
    forall z (ctxt: Context nbr_params),
      ge_bound ctxt lower_bound z <->
      (z:::ctxt) ∈ (polyhedron_of_lower_bound lower_bound).
  Proof.
    intros.
    unfold ge_bound, Pol_In, polyhedron_of_lower_bound.
    split; intro. 
    Case "satisfy_constraint".
      eapply list_forall_list_forall_map;[| eauto].
      intros. rewrite <- constraint_of_lower_bound_constr_correct; auto.
    Case "ge_bound_constraint".
      eapply list_forall_map_list_forall;[| eauto].
      intros.
      rewrite -> constraint_of_lower_bound_constr_correct; auto.
  Qed.
    
  Definition constraint_of_upper_bound_constr {nbr_params}
    (constr: ZNum.Num * NVector (S nbr_params))
     : Constraint (S nbr_params):=
    {| constr_vect := (- fst constr) ::: (Vtail (snd constr));
       constr_comp := GE ;
       constr_val := - (Vhd (snd constr))|}.


  Lemma constraint_of_upper_bound_constr_correct {nbr_params}
    (constr: ZNum.Num * NVector (S nbr_params)):
    forall z (ctxt: Context nbr_params),
      le_bound_constraint (extend_context ctxt) z constr <->
      satisfy_constraint (z:::ctxt) (constraint_of_upper_bound_constr constr).
  Proof.
    intros.
    destruct constr as (x, v).
    unfold constraint_of_upper_bound_constr, le_bound_constraint,
      satisfy_constraint, extend_context; simpl.
    rewrite <- (Vcons_hd_tail v).
    repeat rewrite Vprod_Vcons. simpl_vect.
    simpl. rewrite Vprod_comm. unfold ZNum.Num, ZNum.Numerical_Num.
    lia. 
    constructor. exact 0.
  Qed.


  Definition polyhedron_of_upper_bound {nbr_params}
    (upper_bound: bound nbr_params)
      : Polyhedron (S nbr_params) :=
      map constraint_of_upper_bound_constr upper_bound. 


  Lemma polyhedron_of_upper_bound_correct {nbr_params}
    (upper_bound: bound nbr_params):
    forall z (ctxt: Context nbr_params),
      le_bound ctxt upper_bound z <->
      (z:::ctxt) ∈ (polyhedron_of_upper_bound upper_bound).
  Proof.
    intros.
    unfold le_bound, Pol_In, polyhedron_of_upper_bound.
    split; intro. 
    Case "satisfy_constraint".
      eapply list_forall_list_forall_map; [|eauto].
      intros. rewrite <- constraint_of_upper_bound_constr_correct; auto.
    Case "le_bound_constraint".
      eapply list_forall_map_list_forall; [|eauto].
      intros.
      rewrite -> constraint_of_upper_bound_constr_correct; auto.
  Qed.

  Definition Pol_translate_r {n} p (pol: Polyhedron n) : Polyhedron (p + n) :=
    map (Constr_translate_r p) pol.

  Lemma Pol_translate_r_correct n p (pol: Polyhedron n) v1 v2:
    v2 ∈ pol <-> (v1 +++ v2) ∈ (Pol_translate_r p pol).
  Proof.
    unfold Pol_In, Pol_translate_r.
    split; intro H.
    eapply list_forall_list_forall_map; [|eauto].
    intros. apply Constr_translate_r_correct. assumption.


    eapply list_forall_map_list_forall; [|eauto].
    intros. apply <- Constr_translate_r_correct. eassumption.
  Qed.



  Definition build_poly_for_Loop {nbr_param depth} 
    (lower_bound upper_bound: bound nbr_param)
    (pol: Polyhedron (depth + S nbr_param))
    : Polyhedron (S depth + nbr_param) :=
    cast_polyhedron(
      (Pol_translate_r depth (polyhedron_of_lower_bound lower_bound))
    ∩ (Pol_translate_r depth (polyhedron_of_upper_bound upper_bound))
    ∩ pol).

  Program Definition eval_lower_bound_no {nbr_param} params (lower_bound: bound nbr_param)
    (OKLB: bound_correct lower_bound)
      : {z:Z| eval_lower_bound params lower_bound = Some z} :=
    match eval_lower_bound params lower_bound with
      | Some z => z
      | None => !
    end.
  Next Obligation.
    apply bound_correct_eval_lower_bound_is_some with (ctxt := params) in OKLB.
    inv OKLB.
    replace @ZTools.eval_lower_bound with @eval_lower_bound in * by reflexivity.
    congruence.
  Qed.

  Program Definition eval_upper_bound_no {nbr_param} params (upper_bound: bound nbr_param)
    (OKLB: bound_correct upper_bound)
      : {z:Z| eval_upper_bound params upper_bound = Some z} :=
    match eval_upper_bound params upper_bound with
      | Some z => z
      | None => !
    end.
  Next Obligation.
    apply bound_correct_eval_upper_bound_is_some with (ctxt := params) in OKLB.
    inv OKLB.
    replace @ZTools.eval_upper_bound with @eval_upper_bound in * by reflexivity.
    congruence.
  Qed.

  Lemma NoDup_app : forall A (l: list A) l', NoDup l -> NoDup l' ->
    (forall x, In x l -> In x l' -> False) ->
    NoDup (l++l').
  Proof.
    intros A l.
    induction' l as [|a l]; simpl; intros l' NO NO' NOTIN; auto.
    Case "cons a l".
      constructor.
      intro IN. apply in_app_or in IN. destruct IN as [IN|IN].
      inv NO. auto.
      apply (NOTIN a); auto.
      inv NO. apply IHl; auto.
      intros. apply (NOTIN x); eauto.
  Qed.

  Lemma In_map_inj : forall A B (f: A -> B),
    (forall x y, f x = f y -> x = y) ->
    forall a (l: list A),
      In (f a) (map f l) ->
      In a l.
  Proof.
    intros * INJ *.
    induction' l as [|x l]; intro IN; simpl in *; inv IN; auto.
  Qed.

      
  Lemma NoDup_map_inj : forall A B (f: A -> B),
    (forall x y, f x = f y -> x = y) ->
    forall (l: list A), 
    NoDup l ->
    NoDup (map f l).
  Proof.
    intros * INJ.
    induction' l as [|a l]; simpl; intros NO.
    Case "@nil".
      constructor.
    Case "cons a l".
      inv NO.
      constructor; auto.
      intro. apply H1. apply In_map_inj with (f := f); auto.
  Qed.
  

  Lemma In_flatten A (ll: list (list A)) x:
    In x (flatten ll) <-> exists l, In l ll /\ In x l.
  Proof.
    induction' ll as [| l1 ll]; simpl.
    Case "@nil".
      split'; auto.
      SCase "<-".
        intros [?[? ?]]; auto.
    Case "cons l1 ll".
      split'.
      SCase "->".
        intro IN.
        apply in_app_or in IN. destruct IN as [IN | IN].
          exists l1; auto.
          rewrite IHll in IN. destruct IN as [l [? ?]].
          exists l; auto.
      SCase "<-".
        intros [l [[?|?] ?]]; subst;
        apply in_or_app; auto.
        right; apply IHll.
        eexists; eauto.
  Qed.



  Lemma in_map2_exists A B C (f: A -> B -> C) la lb c:
    In c (map2 f la lb) ->
    exists a b,
      In a la /\ In b lb /\ f a b = c.
  Proof.
    revert lb.
    induction' la as [|a la]; destruct' lb as [|b lb]; intros * IN; simpl in *; clean.
    Case "cons a la"; SCase "cons b lb".
      destruct IN.
      exists a b; auto.
      edestruct IHla as [a' [b' [?[? ?]]]]; eauto.
      exists a' b'; auto.
  Qed.
    
  Lemma snoc_inj A l1 l2 (a:A):
    l1 ++ [a] = l2 ++ [a] ->
    l1 = l2.
  Proof.
    revert l2; induction' l1 as [| a1 l1]; intros l2 EQ;
    destruct' l2 as [|a2 l2]; simpl in *; auto.
    Case "@nil"; SCase "cons a2 l2". 
      inv EQ. destruct l2; inv H1.
    Case "cons a1 l1"; SCase "@nil".
      inv EQ; destruct l1; simpl in *; congruence.
    Case "cons a1 l1"; SCase "cons a2 l2".
      inv EQ; f_equal; auto.
  Qed.

  Fixpoint last_Z (l: list Z) :=
    match l with
      | [] => 0
      | [z] => z
      | _ :: l' => last_Z l'
    end.

  Program Definition Vlast_Z {n} (v: ZVector (S n)) :=
    last_Z v.

  Lemma Vlast_Z_Vsnoc n (v: ZVector n) z :
    Vlast_Z (v::::z) = z.
  Proof.
    dest_vects. unfold Vlast_Z. simpl. clear Lv.
    induction v; simpl; auto.
    destruct v; auto.
  Qed.

  Fixpoint Vtake_aux `{Inhabited A} n (l: list A) :=
    match n with
      | O => []
      | S n' =>
        match l with
          | [] => repeat n repr
          | a:: l' => a :: Vtake_aux n' l'
        end
    end.
  Program Definition Vtake `{Inhabited A} n {p} (v: Vector A p): Vector A n:=
    Vtake_aux n v.
  Next Obligation.
    dest_vects.
    clear.
    revert v.
    induction' n as [|n]; intros; simpl.
    Case "O".
      reflexivity.
    Case "S n".
      destruct' v.
      SCase "@nil".
        simpl. f_equal. apply repeat_length.
      SCase "cons".
        simpl. f_equal. auto.
  Qed.

  Lemma split_big_vect nbr_param depth (v:ZVector (S depth + nbr_param)):
    exists elts z params,
      v = (elts :::: z) +++ params.
  Proof.
    exists (Vtake depth v).
    exists (Vnth v depth).
    exists (Vdrop_p (S depth) v).
    dest_vects.
    revert dependent nbr_param.
    revert v.
    induction' depth as [|depth]; simpl; intros; auto.
    Case "O".
      destruct' v as [|z v]; simpl in *; clean.
    Case "S depth".
      destruct' v as [|z v]; simpl in *; clean.
      f_equal; eauto.
  Qed.


  Program Definition build_boxed_poly_for_Loop {nbr_param depth}
    (lower_bound upper_bound: bound nbr_param) (OKLB: bound_correct lower_bound)
    (OKUB: bound_correct upper_bound) (bpol: Boxed_Polyhedron (S nbr_param) depth)
    : Boxed_Polyhedron (nbr_param) (S depth):=
    {| bp_poly := build_poly_for_Loop lower_bound upper_bound bpol.(bp_poly);
       bp_elts := fun params =>
         let lb := eval_lower_bound_no params lower_bound OKLB in
         let ub := eval_upper_bound_no params upper_bound OKUB in
         let lZ := list_of_Z_between lb ub in
         let bpol_params_lst  := map (fun z => z ::: params) lZ in
         let bpol_elts_lst := map bpol.(bp_elts) bpol_params_lst in
         let elts_lst := map2 (fun z vl => map (fun v => v :::: z) vl)
             lZ bpol_elts_lst in
         flatten elts_lst
         |}.
  Next Obligation.
    destruct (eval_lower_bound_no params lower_bound OKLB) as [lb ELB].
    destruct (eval_upper_bound_no params upper_bound OKUB) as [ub EUB].
    simpl.
    unfold list_of_Z_between.
    clear.
    functional induction (list_of_Z_between_aux ub lb); [|constructor].
    simpl.
    apply NoDup_app; auto.
    Case "NoDup".
    apply NoDup_map_inj.
      clear'.
      intros * EQ.
      assert (` (x :::: lb) = ` (y :::: lb)) by congruence. clear EQ.
      dest_vects. simpl in *. eapply snoc_inj; eauto.
      apply bp_elts_NoDup.
      
    Case "Not In".
      intros * IN INFLAT.
      assert' (Vlast_Z x = lb) as VLASTEQ.
        SCase "Assert: VLASTEQ".
        clear' - IN.
        rewrite in_map_iff in IN.
        destruct IN as [v [? ?]].
        subst. apply Vlast_Z_Vsnoc.
      End_of_assert VLASTEQ.
      assert' (Vlast_Z x > lb) as VLASTGT.
        SCase "Assert: VLASTGT".
        clear' - INFLAT.
        rewrite In_flatten in INFLAT.
        destruct INFLAT as [l [INxl INll]].
        apply in_map2_exists in INxl.
        destruct INxl as [z [l' [INz [_ ?]]]]; subst.
        fold (list_of_Z_between (Zsucc lb) ub) in INz.
        rewrite list_of_Z_between_correct in INz.
        apply in_map_iff in INll. destruct INll as [? [? ?]]; subst.
        rewrite Vlast_Z_Vsnoc. unfold Zsucc in *. lia.
      End_of_assert VLASTGT.
      lia.
  Qed.
  Next Obligation.
    destruct (eval_lower_bound_no params lower_bound OKLB) as [lb ELB].
    destruct (eval_upper_bound_no params upper_bound OKUB) as [ub EUB].
    match goal with
      | |-
        @Pol_In (S (depth +  nbr_param))
        ?v ?p =>
        replace (@Pol_In (S (depth + nbr_param))
        v p) with (@Pol_In ((S depth) + nbr_param)
        v p) by reflexivity
    end.
(*    apply in_pol_in_constrain_params.*)

    simpl in *.
    rewrite In_flatten in H.
    destruct H as [l [IN2 INl]].
    rewrite map_map in IN2.

    match type of IN2 with
      | In l (map2 ?f ?loz (map ?g ?loz)) =>
      assert'
      (exists z, In z (list_of_Z_between lb ub) /\
        l = f z (g z)) as EXZ
    end.
    Case "Assert: EXZ".
      remember (list_of_Z_between lb ub) as loz. clear Heqloz.
      induction' loz as [|z loz]; simpl in *; clean.
      SCase "cons z loz".
        inv IN2.
        exists z; split'; auto.
        specialize (IHloz H).
        destruct IHloz as [z' [? ?]].
        exists z'; eauto.
    End_of_assert EXZ.
    clear IN2.
    destruct EXZ as [z [IN ?]].
    subst.
    rewrite list_of_Z_between_correct in IN.
    rewrite in_map_iff in INl.
    destruct INl as [v [? INv]]; subst.

    unfold build_poly_for_Loop.
    apply Pol_In_cast_polyhedron.
    repeat (apply Pol_Included_intersertion).
    Case "lower".
    apply Pol_translate_r_correct.
    apply polyhedron_of_lower_bound_correct.
    apply eval_lower_bound_is_ge in ELB.
    eapply ge_bound_trans; eauto. lia.
    Case "upper".
    apply Pol_translate_r_correct.
    apply polyhedron_of_upper_bound_correct.
    apply eval_upper_bound_is_ge in EUB.
    eapply le_bound_trans; eauto. lia.
    Case "params".
    pose proof in_constrain_param_in_pol. unfold Pol_Included in H.
    eapply H.
    eapply bp_in_elts_in_poly_constrain. eauto.
  Qed.
  Next Obligation.
    destruct (eval_lower_bound_no params lower_bound OKLB) as [lb ELB].
    destruct (eval_upper_bound_no params upper_bound OKUB) as [ub EUB].
    simpl.
    unfold constrain_params in H.
    destruct (split_big_vect _ _ vect) as [elts[z[params' ?]]].
    subst.
    assert' (params = params').
    Case "Assert".
      apply Pol_intersection_Included_l in H.
      apply poly_containing_params_drop_1 in H.
      rewrite Vdrop_p_app in H. auto.
    End_of_assert.
    subst.
    apply Pol_intersection_Included_r in H.
    unfold build_poly_for_Loop in H.
    apply Pol_In_cast_polyhedron in H.
    repeat match goal with
      | H : ?v ∈ ?p1 ∩ ?p2 |- _ =>
        pose proof (Pol_intersection_Included_l _ _ H);
        pose proof (Pol_intersection_Included_r _ _ H);
        clear H
    end.
    rewrite Vtake_p_app.
    apply Pol_translate_r_correct in H. apply Pol_translate_r_correct in H2.
    rewrite <- polyhedron_of_upper_bound_correct in H2.
    rewrite <- polyhedron_of_lower_bound_correct in H.
    eapply ge_bound_ge_lower_bound in H; eauto.
    eapply le_bound_le_upper_bound in H2; eauto.
    clear dependent lower_bound. clear dependent upper_bound.
    apply in_pol_in_constrain_params in H1.
    eapply bp_in_poly_in_elts in H1.
    rewrite Vtake_p_app in H1.
    assert' (In z (list_of_Z_between lb ub)) as INZ.
      Case "Assert: INZ".
      apply list_of_Z_between_correct. lia.
    End_of_assert INZ.
    remember (list_of_Z_between lb ub) as loz. clear Heqloz.
    clear dependent lb. clear dependent ub.
    induction' loz as [|z' loz]; inv INZ; simpl;
    rewrite in_app_iff; auto.
    Case "cons z' loz".
    left.
    apply in_map_iff. eexists; eauto.
  Qed.

  Definition cast_pi_transformation {pi_depth global_depth num_of_args}
    (mat: ZMatrix num_of_args (S (pi_depth + S global_depth)))
      : ZMatrix num_of_args (S (S pi_depth + global_depth)).
    pattern (S pi_depth + global_depth)%nat.
    refine (cast_A (plus_Snm_nSm _ _) mat).
  Defined.

  Lemma snoc_app A (v1 v2: list A) a :
    v1 ++ a :: v2 = (v1 ++[a]) ++ v2.
  Proof.
    induction v1; simpl; auto.
    f_equal; assumption.
  Qed.

  Lemma cast_pi_transformation_id {pi_depth global_depth num_of_args}
    (pi_transf: ZMatrix num_of_args (S (pi_depth + S global_depth))) 
     (a: ZVector pi_depth) lb (ctxt: ZVector global_depth):
    pi_transf × (1 ::: (a +++ lb ::: ctxt)) =
   cast_pi_transformation pi_transf  × (1 ::: ((a :::: lb) +++ ctxt)).
  Proof.
    apply PVeq_Veq. unfold Matrix in *.
    dest_vects.
    unfold Mprod_vect, Vprod. simpl.
    clear.
    unfold cast_pi_transformation. unfold cast_A.
    dest_eq_rect. simpl.
    apply map_ext.
    intro v.
    clear. 
    dest_vects. clear.
    rewrite snoc_app. auto.
  Qed.

  Definition make_pi_schedule {depth global_depth}
    (schedule: list (ZVector (S (depth + S global_depth))))
    : list (ZVector (S ( S depth + global_depth))) :=
    (0::: (((V0 depth) :::: 1) +++ V0 global_depth))::
    cast_list (eq_S _ _ (plus_Snm_nSm _ _)) schedule.

(*  Definition make_schedule*)

  Fixpoint extract_statement {global_depth: nat}
    (st: statement global_depth) {struct st}
    : res (list (Polyhedral_Instruction global_depth)) :=
    match st with
    | Instr instr transf =>
      OK [
        {| pi_instr := instr;
          pi_depth := O;
          pi_poly := point_boxed_polyhedron global_depth;
          pi_schedule := [(1 ::: V0 (0 + global_depth))];
          pi_transformation := transf
        |}]
    | Loop lb ub sts =>
      match check_bound lb with
      | left CLB =>
      match check_bound ub with
      | left CUB =>
      do lpi <- extract_statement_list 1 sts;
      OK(
        map (fun pi =>
          {|pi_instr := pi.(pi_instr);
            pi_depth := S (pi.(pi_depth));
            pi_poly := build_boxed_poly_for_Loop lb ub CLB CUB pi.(pi_poly);
            pi_schedule := make_pi_schedule pi.(pi_schedule);
            pi_transformation := cast_pi_transformation pi.(pi_transformation)|}
        ) lpi)
      | right _ => Err "Upper bound incorrect"
      end
      | right _ => Err "Lower bound incorrect"
      end

    end
  with extract_statement_list {global_depth: nat}
    (pos: Z) (stl: statement_list global_depth) {struct stl}
    : res (list (Polyhedral_Instruction global_depth)) :=
    match stl with
      | stl_nil => OK []
      | stl_cons st stl' =>
        do{;
          pil1 <- extract_statement st;;
          let pil1' := map (raise_time_stamp pos) pil1;;
          pil2 <- extract_statement_list (Zsucc pos) stl';
          OK (pil1' ++ pil2)
        }
    end.

  Lemma res_of_option_OK A (oa: option A) (a:A) err:
    res_of_option oa err = OK a -r> oa = Some a.
  Proof.
    constructor. unfold res_of_option. intro. destruct oa; clean.
  Qed.
  Hint Rewrite res_of_option_OK: clean.


  (* we use another semantics for the proof, juste to remove the poly
     program constructors. It's just a bit easier to express things *)

  Definition poly_list_semantics (global_depth: nat)
    (instrs_lst: list (Polyhedral_Instruction global_depth))
      (params : ZVector global_depth) (sorted_instruction_points : list Instruction_Point)
      (mem1 mem2 : Memory) : Prop :=
      Sorted instruction_point_lt sorted_instruction_points /\
      Permutation (flatten (map (expand_poly_instr params) instrs_lst))
        sorted_instruction_points /\
      instruction_list_semantics sorted_instruction_points mem1 mem2.

  Ltac destr_poly_list_semantics :=
    match goal with
      | H : poly_list_semantics _ _ _ _ _ _ |- _ =>
        destruct H as [? [? ?]]
    end.

(*  Lemma poly_list_semantics_equiv_poly_program_semantics: forall
    (instructions: PTree.t I.Instruction) (global_depth: nat)
    (instrs_lst: list (Polyhedral_Instruction instructions global_depth))
      (params : ZVector global_depth)  (mem1 mem2 : Memory),
      (exists sorted_instruction_points,
        poly_list_semantics instructions global_depth instrs_lst params
          sorted_instruction_points mem1 mem2)
        <->
      poly_program_semantics 
       {| pp_instructions := instructions;
          pp_nbr_global_parameters := global_depth;
          pp_poly_instrs := instrs_lst |} params mem1 mem2.
  Proof.
    intros. constructor; intro H.
    Case "->".
      destruct H. destr_poly_list_semantics. econstructor; eauto.

    Case "<-".
      inv H; econstructor; econstructor; eauto.
  Qed.*)


  Lemma instruction_list_semantics_app1: forall l1 l2 mem1 mem3,
    instruction_list_semantics (l1++l2) mem1 mem3 ->
    exists mem2,
      instruction_list_semantics l1 mem1 mem2 /\
      instruction_list_semantics l2 mem2 mem3.
  Proof.
    intro l1.
    induction' l1 as [|i l1]; intros * INSTR; simpl in *.
    Case "@nil".
      exists mem1. split; auto. constructor.
    Case "cons i l1".
      inv INSTR.
      edestruct IHl1 as [mem2' [? ?]]; eauto.
      eexists; split; eauto.
      econstructor; eauto.
  Qed.

  Lemma instruction_list_semantics_app2: forall l1 l2 mem1 mem2 mem3,
    instruction_list_semantics l1 mem1 mem2 ->
    instruction_list_semantics l2 mem2 mem3 ->
    instruction_list_semantics (l1++l2) mem1 mem3.
  Proof.
    intro l1; induction' l1 as [|i1 l1]; intros * INSTRSEM1 INSTRSEM2;
      simpl in *.
    Case "@nil".
      inv INSTRSEM1; auto.
    Case "cons i1 l1".
      inv INSTRSEM1; econstructor; eauto.
  Qed.



  Definition raise_time_stamp_instr pos ip :=
    {| ip_instruction := ip.(ip_instruction);
       ip_arguments := ip.(ip_arguments);
       ip_time_stamp := pos :: ip.(ip_time_stamp)|}.

  Lemma raise_time_stamp_expand_poly_instr global_depth pos
    (pinstr: Polyhedral_Instruction global_depth) params :
    expand_poly_instr params (raise_time_stamp pos pinstr) = 
    map (raise_time_stamp_instr pos) (expand_poly_instr params pinstr).
  Proof.
    destruct pinstr.
    unfold expand_poly_instr. simpl. clear.

    remember (bp_elts pi_poly0 params) as elts. clear Heqelts.

    induction' elts as [|ctxt elts]; simpl; auto.
    Case "cons ctxt elts".
      simpl. f_equal; auto.
      unfold raise_time_stamp_instr. simpl.
      f_equal.
      f_equal.
      unfold make_context_ext. rewrite Vprod_Vcons. simpl_vect. reflexivity.
  Qed.

  Lemma flatten_map_expand global_depth pos
    (pinstr_lst: list (Polyhedral_Instruction global_depth)) params:
  flatten (map (expand_poly_instr params) (map (raise_time_stamp pos) pinstr_lst)) =
  map (raise_time_stamp_instr pos) (flatten (map (expand_poly_instr params) pinstr_lst)).
  Proof.
    induction pinstr_lst; simpl; auto.
    rewrite map_app. f_equal; auto.
    apply raise_time_stamp_expand_poly_instr.
  Qed.


  Lemma raise_time_stamp_expand_poly_instr_sorted global_depth pos
    (pinstr_lst: list (Polyhedral_Instruction global_depth)) params 
    sorted_list_1:
    Sorted instruction_point_lt sorted_list_1 ->
    Permutation (flatten (map (expand_poly_instr params) pinstr_lst))
      sorted_list_1 ->
    Sorted instruction_point_lt (map (raise_time_stamp_instr pos) sorted_list_1) /\
    Permutation (flatten (map (expand_poly_instr params) 
                  (map (raise_time_stamp pos) pinstr_lst)))
                (map (raise_time_stamp_instr pos) sorted_list_1)
      .
  Proof.
    intros SORTED PERMUT.
    split.
    Case "Sorted".
      clear PERMUT.
      induction' SORTED; simpl; constructor; auto.
      SCase "Sorted_cons".
      clear' - H.
      induction' H; constructor; auto.
      SSCase "HdRel_cons".
        unfold raise_time_stamp_instr, instruction_point_lt in *.
        destruct a; destruct b. simpl in *.
        clear' - H.
        apply TSLT_eq. auto.
    Case "Permutation".
      clear' - PERMUT.
      rewrite flatten_map_expand.
      apply Permutation_map. auto.
  Qed.

  Lemma raise_time_stamp_poly_list_semantics global_depth
    (pil: list (Polyhedral_Instruction global_depth))
    instr_point_lst pos ctxt mem1 mem2:
    poly_list_semantics global_depth pil ctxt instr_point_lst
    mem1 mem2 ->
    poly_list_semantics global_depth (map (raise_time_stamp pos) pil)
    ctxt (map (raise_time_stamp_instr pos) instr_point_lst) mem1 mem2.
  Proof.
    intro PLS.
    destr_poly_list_semantics.
    edestruct raise_time_stamp_expand_poly_instr_sorted; eauto.
    econstructor;[|econstructor]; eauto.
    clear - H1.
    induction H1; econstructor; eauto.
    inv H. econstructor; eauto.
  Qed.


  Fixpoint list_of_statement_list {global_depth} (stl: statement_list global_depth):
    list (statement global_depth) :=
    match stl with
      | stl_nil => []
      | stl_cons st stl' => st :: list_of_statement_list stl'
    end.

  (* ESL_inv1: extract_statement_list invariant *)

  Inductive ESL_inv1 {global_depth : nat} {ctxt: Context global_depth}:
    forall (pos:Z) (mem1 mem2 : Memory)
    (st_lst: statement_list global_depth)
(*    (pol_instr_lst_lst: list (list (Polyhedral_Instruction global_depth)))*)
    (raised_pol_instr_lst_lst: list (list (Polyhedral_Instruction global_depth)))
    (instr_point_lst_lst: list (list Instruction_Point)),
      Prop :=
  | ESLI1_nil: forall pos mem,
    ESL_inv1 pos mem mem stl_nil (*[]*) [] []
  | ESLI2_cons: forall pos mem1 mem2 mem3
    st st_lst pol_instr_lst (*pol_instr_lst_lst*)
    raised_pol_instr_lst raised_pol_instr_lst_lst instr_point_lst instr_point_lst_lst,

    semantics_statement ctxt st mem1 mem2 ->

    extract_statement st = OK pol_instr_lst ->
    raised_pol_instr_lst = map (raise_time_stamp pos) pol_instr_lst ->

    Sorted instruction_point_lt instr_point_lst ->
    Permutation (flatten (map (expand_poly_instr ctxt) raised_pol_instr_lst))
      instr_point_lst ->
    instruction_list_semantics instr_point_lst mem1 mem2 ->


    ESL_inv1 (Zsucc pos) mem2 mem3
      st_lst (*pol_instr_lst_lst*) raised_pol_instr_lst_lst instr_point_lst_lst ->
    ESL_inv1 pos mem1 mem3 (stl_cons st st_lst) (*(pol_instr_lst :: pol_instr_lst_lst)*)
    (raised_pol_instr_lst :: raised_pol_instr_lst_lst) (instr_point_lst :: instr_point_lst_lst).

  Implicit Arguments ESL_inv1 [].

  Lemma ESL_inv1_extract_statement_list global_depth
    (ctxt: Context global_depth) pos mem1 mem2 st_lst (*pol_instr_lst_lst*)
    raised_pol_instr_lst_lst instr_point_lst_lst:
    ESL_inv1 global_depth ctxt pos mem1 mem2
      st_lst (*pol_instr_lst_lst*) raised_pol_instr_lst_lst instr_point_lst_lst ->
    extract_statement_list pos st_lst =
      OK (flatten raised_pol_instr_lst_lst).
  Proof.
    intros ESL; induction' ESL; simpl.
    Case "ESLI1_nil".
      reflexivity.
    Case "ESLI2_cons".
      rewrite H0. simpl_do. rewrite IHESL. simpl_do.
      f_equal.
      f_equal; auto.
  Qed.
    
  Lemma flatten_app {A} (l1 l2: list (list A)):
    flatten (l1 ++ l2) = flatten l1 ++ flatten l2.
  Proof.
    induction' l1; simpl; auto.
    rewrite IHl1. apply app_assoc.
  Qed.


  Lemma ESL_inv1_semantics_statement_list global_depth
    (ctxt: Context global_depth) pos mem1 mem2 st_lst (*pol_instr_lst_lst*)
    raised_pol_instr_lst_lst instr_point_lst_lst:
    ESL_inv1 global_depth ctxt pos mem1 mem2
      st_lst (*pol_instr_lst_lst*) raised_pol_instr_lst_lst instr_point_lst_lst ->
    semantics_statement_list  ctxt st_lst mem1 mem2.
  Proof.
    intro ESL.
    induction ESL; econstructor; eauto.
  Qed.

  Inductive first_dim_eq_time_stamp (pos:Z) : Time_Stamp -> Prop:=
  | fde_intro: forall ts, first_dim_eq_time_stamp pos (pos :: ts).

  Definition first_dim_eq pos ip := first_dim_eq_time_stamp pos (ip.(ip_time_stamp)).

  Inductive first_dim_gt_time_stamp (pos:Z) : Time_Stamp -> Prop:=
  | fdg_intro: forall x ts, pos < x -> first_dim_gt_time_stamp pos (x :: ts).

  Definition first_dim_gt pos ip := first_dim_gt_time_stamp pos (ip.(ip_time_stamp)).


  Lemma ESL_inv1_Forall_first_dim_gt global_depth
    (ctxt: Context global_depth) pos pos' mem1 mem2 st_lst (*pol_instr_lst_lst*)
    raised_pol_instr_lst_lst instr_point_lst_lst:
    ESL_inv1 global_depth ctxt pos' mem1 mem2
      st_lst (*pol_instr_lst_lst*) raised_pol_instr_lst_lst instr_point_lst_lst ->
    pos < pos' ->
    Forall (Forall (first_dim_gt pos)) instr_point_lst_lst.
  Proof.
    intros ESL.
    induction' ESL; simpl; intro INF; auto.
    Case "ESLI2_cons".
      constructor'.
      NSCase "Head".
        eapply Permutation_Forall;[|eauto].
        subst.
        rewrite map_map.
        apply Forall_flatten.
        clear' - INF. 
        induction' pol_instr_lst; simpl; auto.
        SSCase "cons".
          constructor; auto.
          rewrite raise_time_stamp_expand_poly_instr.
          rewrite Forall_forall.
          intros * IN.
          rewrite in_map_iff in IN. destruct IN as [?[? ?]].
          subst. unfold first_dim_gt.
          destruct x0. simpl. constructor; assumption.
      NSCase "Tail".
        apply IHESL. unfold Zsucc. lia.
  Qed.

  Lemma extract_statement_list_ok_correct (global_depth: nat)
    (pos: Z) (st_lst: statement_list global_depth)
    (instrs_lst : list (Polyhedral_Instruction global_depth)):
    extract_statement_list pos st_lst = OK instrs_lst ->
    forall ctxt mem1 mem2,
    semantics_statement_list ctxt st_lst mem1 mem2 ->
    (exists raised_pol_instr_lst_lst instr_point_lst_lst,
      ESL_inv1 global_depth ctxt pos mem1 mem2
        st_lst raised_pol_instr_lst_lst instr_point_lst_lst) ->
    exists sorted_instruction_points,
      poly_list_semantics global_depth instrs_lst
       ctxt sorted_instruction_points mem1 mem2.
  Proof.
    intros EXTRACT * SEM [raised_pol_instr_lst_lst [instr_point_lst_lst ESL]].
    exists (flatten instr_point_lst_lst).
    constructor; [|constructor].
    Case "Sorted".
      clear' - ESL.
      induction' ESL; simpl; auto.
      SCase "ESLI2_cons".
        apply ESL_inv1_Forall_first_dim_gt with (pos := pos) in ESL;
          [|unfold Zsucc; lia].
        subst.
        rewrite map_map in H3.
        assert (Forall (first_dim_eq pos) instr_point_lst) as FA.
          eapply Permutation_Forall; [|eauto].
          apply Forall_flatten.
          rewrite Forall_forall.
          clear'.
          intros instr_point_lst IN.
          rewrite in_map_iff in IN.
          destruct IN as [? [? ?]].
          subst.
          rewrite raise_time_stamp_expand_poly_instr.
          rewrite Forall_forall.
          clear'.
          intros instr_point_lst IN.
          rewrite in_map_iff in IN.
          destruct IN as [? [? ?]].
          subst. destruct x0; compute. constructor.

        clear' - H2 ESL IHESL FA.
        induction' instr_point_lst as [|ip instr_point_lst]; simpl; auto.
        SSCase "cons ip instr_point_lst".
          inv H2.
          specialize (IHinstr_point_lst H1).
          inv FA.
          constructor; auto.
          inv H3; auto; simpl; [|constructor; auto].
          apply Forall_flatten in ESL.
          inv ESL; constructor.
          clear' - H2 H0.
          unfold first_dim_eq, first_dim_gt, instruction_point_lt in *.
          destruct ip; destruct x; simpl in *.
          inv H2; inv H0. constructor. auto.      
    Case "Permutation".
      erewrite ESL_inv1_extract_statement_list in EXTRACT; eauto.
      clean. clear SEM.
      induction' ESL.
      SCase "ESLI1_nil".
        simpl in *. clean.
      SCase "ESLI2_cons".
        simpl.
        rewrite map_app. rewrite flatten_app.
        apply Permutation_app; auto.

    Case "instruction_list_semantics".
      clear' - ESL.
      induction' ESL; simpl.
      SCase "ESLI1_nil".
        constructor.
      SCase "ESLI2_cons".
        eapply instruction_list_semantics_app2; eauto.
  Qed.
  Inductive hd_ge z : list Z -> Prop :=
  | hd_ge_intro: forall x l, z <= x ->
    hd_ge z (x :: l).

  Fixpoint map2_sl {A1 A2 B} (f: A1 -> A2 -> B) (l1: list A1)
    (l2: list A2) : option (list B) :=
    match l1, l2 with
    | [], [] => Some nil
    | [], _
    | _, [] => None
    | a1 :: l1', a2 :: l2' =>
      do l' <- map2_sl f l1' l2';
      Some (f a1 a2 :: l')
    end.


  Lemma flatten_map A B (f: A -> B) ll:
    flatten (map (fun l=> map f l) ll) = map f (flatten ll).
  Proof.
    induction ll; simpl; auto.
    rewrite IHll. symmetry. apply map_app.
  Qed.
    
  Lemma Permutation_flatten_map A B (f: A -> B) l ll:
    Permutation (flatten ll) l ->
    Permutation (flatten (map (fun l' => map f l') ll)) (map f l).
  Proof.
    intros. rewrite flatten_map. apply Permutation_map. assumption.
  Qed.

  Lemma bar: forall A
    (p_fst_part p_snd_part long_list: list (list A))
    (fst_part snd_part: list A),
    Permutation (flatten p_fst_part) fst_part ->
    Permutation (flatten p_snd_part) snd_part ->
    map2_sl (fun l1 l2 => l1 ++ l2) p_fst_part p_snd_part = Some long_list ->
    Permutation (flatten long_list) (fst_part ++ snd_part).
  Proof.
    intros.
    etransitivity; [|eapply Permutation_app; eauto].
    clear - H1.
    revert dependent p_snd_part. revert long_list.
    induction p_fst_part; simpl in *; intros;
    destruct p_snd_part; clean.
    prog_dos.
    specialize (IHp_fst_part _ _ Heq_do).
    simpl.
    etransitivity. apply Permutation_app; [reflexivity|eexact IHp_fst_part].
    rewrite <- app_assoc. rewrite <- app_assoc.
    apply Permutation_app. reflexivity.
    etransitivity;[|
    apply Permutation_app_comm].
    rewrite <- app_assoc.
    apply Permutation_app. reflexivity.
    apply Permutation_app_comm.
  Qed.
    

  Lemma foo: forall A
    (p_fst_part p_snd_part long_list: list (list A))
    (fst_part snd_part: list A)
    f,
    Permutation (flatten p_fst_part) fst_part ->
    Permutation (flatten p_snd_part) snd_part ->
    map2_sl (fun l1 l2 => (map f l1) ++ l2) p_fst_part p_snd_part = Some long_list ->
    Permutation (flatten long_list) (map f fst_part ++ snd_part).
  Proof.
    intros.
    eapply bar; eauto.
    apply Permutation_flatten_map; eauto.
    clear - H1.
    revert H1. revert long_list p_snd_part.
    induction p_fst_part; simpl in *; intros; clean.
    destruct p_snd_part; clean. prog_dos.
    erewrite IHp_fst_part in Heq_do0; eauto. clean.

    
    erewrite IHp_fst_part in Heq_do0;[|eauto]. clean.
  Qed.

  Fixpoint extract_statement_correct (global_depth: nat)
    (st: statement global_depth)
    (instrs_lst: list (Polyhedral_Instruction global_depth)) {struct st}:
    extract_statement st = OK instrs_lst ->
    forall ctxt mem1 mem2, 
      semantics_statement ctxt st mem1 mem2 ->
      exists sorted_instruction_points,
      poly_list_semantics global_depth instrs_lst
       ctxt sorted_instruction_points mem1 mem2
  with extract_statement_list_ok (global_depth: nat)
    (pos: Z) (st_lst: statement_list global_depth)
    (instrs_lst : list (Polyhedral_Instruction global_depth)){struct st_lst}:
    extract_statement_list pos st_lst = OK instrs_lst ->
    forall ctxt mem1 mem2,
    semantics_statement_list ctxt st_lst mem1 mem2 ->
    exists raised_pol_instr_lst_lst instr_point_lst_lst,
      ESL_inv1 global_depth ctxt pos mem1 mem2
        st_lst raised_pol_instr_lst_lst instr_point_lst_lst 
(*  with extract_statement_list_correct (global_depth: nat)
    (instructions: PTree.t I.Instruction) (pos: Z) (st_lst: statement_list global_depth)
    (instrs_lst : list (Polyhedral_Instruction global_depth)) {struct st_lst}:
    extract_statement_list pos st_lst = OK instrs_lst ->
    forall ctxt mem1 mem2, 
      semantics_statement_list ctxt st_lst mem1 mem2 ->
      exists sorted_instruction_points,
      poly_list_semantics global_depth instrs_lst
       ctxt sorted_instruction_points mem1 mem2*).
  Proof.
    Case "extract_statement_correct".
      intros.
      destruct' st; simpl in H; unfold not_implemented in *; clean.
      SCase "Loop".
        destruct (check_bound lower_bound) as [CLB | _]; clean.
        destruct (check_bound upper_bound) as [CUB | _]; clean.
        inv H0; clean.
        assert (
          exists sorted_instruction_points,
            list_forall
              (fun ip => hd_ge lb ip.(ip_time_stamp)) sorted_instruction_points /\
            poly_list_semantics global_depth instrs_lst ctxt
              sorted_instruction_points mem1 mem2) as ASSERT;
        [|solve [destruct ASSERT as [sip [? ?]]; exists sip; auto]].
        prog_dos.
        specialize extract_statement_list_ok with (1 := Heq_do).
        assert' (forall ctxt mem1 mem2,
          semantics_statement_list ctxt body mem1 mem2 ->
          exists sorted_instruction_points,
            poly_list_semantics (S global_depth) lpi
            ctxt sorted_instruction_points mem1 mem2) as ESL_correct.
        SSCase "Assert: ESL_correct".
          intros. eapply extract_statement_list_ok_correct; eauto.
        End_of_assert ESL_correct.
        clear extract_statement_list_ok extract_statement_correct.
        clear Heq_do.
        unfold build_boxed_poly_for_Loop.
        simpl in *.
        unfold poly_list_semantics. simpl.
        
        repeat rewrite map_map. 
        unfold expand_poly_instr. simpl.
        destruct (eval_lower_bound_no ctxt lower_bound CLB) as [lb' ?].
        destruct (eval_upper_bound_no ctxt upper_bound CUB) as [ub' ?].
        simpl.
        assert (ub' = ub) by congruence. subst.
        assert (lb' = lb) by congruence. subst.
        clear dependent lower_bound.
        clear dependent upper_bound.
        unfold list_of_Z_between.
        revert dependent mem2. revert mem1.
        functional induction (list_of_Z_between_aux ub lb); intros.
        SSCase "lb <= ub".
          inv H10; clean;[simpl in *; lia|].
          unfold Zsucc in *.
          specialize (IHl _ _ H6).
          specialize (ESL_correct _ _ _ H3).
          destruct ESL_correct as [fst_part [? [? ?]]].
          destruct IHl as [snd_part [? [? [? ? ]]]].
          exists
            ((map (fun ip => 
                {| ip_instruction := ip.(ip_instruction);
                   ip_arguments := ip.(ip_arguments);
                   ip_time_stamp := lb :: ip.(ip_time_stamp)|}) fst_part) ++
              snd_part).
          repeat (apply conj).
          S3Case "list_forall".
            apply list_forall_list_forall_app.
            S4Case "fst_part".
              clear'.
              induction fst_part; simpl; constructor; auto.
              constructor. lia.
            S4Case "snd_part".
              eapply list_forall_imply; [|eassumption].
              simpl. clear'. intros ip HDGE. inv HDGE. constructor. lia.
          S3Case "Sorted".
            clear' - H H4 H2.
            induction' fst_part as [|ip1 fst_part]; simpl; auto.
            S4Case "cons ip1 fst_part".
              inv H.
              constructor; auto.
              destruct' fst_part as [|ip2 fst_part]; simpl.
              S5Case "@nil".
                destruct' snd_part as [|ip2 snd_part]; simpl; auto.
                S6Case "cons ip2 snd_part".
                  constructor.
                  inv H2. destruct ip2. red. simpl in *.
                  inv H1. apply TSLT_lt. lia.
              S5Case "cons ip2 fst_part".
                constructor. red. simpl. apply TSLT_eq.
                inv H5. red in H0. assumption.
          S3Case "Permutation".
            clear' - H0 H5.
            simpl.
            erewrite map_ext.
            Focus 2. intros.
            rewrite map_map. rewrite map_map.
            rewrite map_app. rewrite map_map.
            reflexivity.
            unfold expand_poly_instr in H0.
            Focus 1.
            eapply foo; eauto.
            clear'.
            induction' lpi as [|pi lpi].
            S4Case "@nil".
              simpl. reflexivity.
            S4Case "cons pi lpi".
              simpl. rewrite IHlpi.
              simpl_do. clear'. f_equal.
              f_equal. f_equal.
              rewrite  map_map. simpl. rewrite map_map. simpl. apply map_ext.
              unfold make_context_ext. simpl.
              intros; f_equal. apply cast_pi_transformation_id.
              f_equal.
              rewrite Vprod_Vcons. simpl. unfold Context in *.
              clear'.
              destruct pi. simpl in *. clear'.
              match goal with
                | |-
                  context[〈?v1 +++ ?v2, ?v3 +++ ?v4〉] =>
                  pose proof (Vprod_app v1 v3 v2 v4) as VPA
              end.
              unfold ZNum.Num in *. unfold ZNum.Numerical_Num in *.
              simpl in VPA. rewrite VPA. clear VPA.
              simpl_vect. simpl; lia.

              destruct pi; simpl in *; clear'.
              rewrite cast_list_cast_A. unfold apply_schedule.
              induction' pi_schedule0; simpl; auto.
              S5Case "cons".
                f_equal; auto.
                clear'. unfold cast_A.
                dest_vects. clear'. dest_eq_rect. simpl.
                rewrite snoc_app; auto.
              
              rewrite map_map. rewrite map_map. apply map_ext.
              intros. reflexivity.

          S3Case "instruction_list_semantics".
            eapply instruction_list_semantics_app2; eauto.
            clear' - H1.
            induction H1; econstructor; eauto.
            inv H; simpl. econstructor; eauto.
          
        SSCase "ub < lb".
          simpl.
          inv H10; clean;[| simpl in *; lia].
          exists (@nil Instruction_Point).
          repeat constructor.
          clear'. induction lpi; auto.

      SCase "Instr".
      eexists; econstructor; [|econstructor]; simpl;[|reflexivity|].
      SSCase "Sorted".
        repeat constructor.
      SSCase "instruction_list_semantics".
        econstructor;[|econstructor].
        unfold make_context_ext.
        rewrite V0_Vapp.
        inv H0. clean.
        econstructor; simpl; clean; eauto.

    Case "extract_statement_list_ok".
      revert instrs_lst pos.
      destruct' st_lst as [|st st_lst]; intros * EXTRACT * SEM; inv SEM; clean.
      SCase "@stl_nil".
        repeat econstructor.
      SCase "stl_cons st st_lst".
        simpl in EXTRACT.
        prog_dos.
        edestruct extract_statement_list_ok as [?[??]]; eauto.
        edestruct extract_statement_correct as [instr_point_lst H0]; eauto.
        eapply raise_time_stamp_poly_list_semantics in H0.
        destr_poly_list_semantics.
        eexists; eexists; econstructor; eauto.
(*    Case "extract_statement_list_correct".
    intros.
    eapply extract_statement_list_ok_correct; eauto.*)
  Qed.

  Definition extract_program (prog:Program) : res Poly_Program :=
    do pil <- extract_statement_list 1 prog.(prog_main);
    OK {|pp_nbr_global_parameters := prog.(prog_nbr_global_parameters);
         pp_poly_instrs := pil|}.

  Theorem extract_program_correct prog pprog:
    extract_program prog = OK pprog ->
    forall params mem1 mem2,
      program_semantics prog params mem1 mem2 ->
      poly_program_semantics_param instruction_point_lt pprog params mem1 mem2.
  Proof.
    intros EXTRACT * PROGSEM.
    unfold extract_program in EXTRACT.
    prog_dos.
    pose proof (extract_statement_list_ok _ _ _ _ Heq_do).

    destruct' (make_vector prog.(prog_nbr_global_parameters) params) as [Vparams|] _eqn.
    Case "Some Vparams".
      inv PROGSEM.
      assert (Vparams0 = Vparams) by congruence. subst.
      clear H0.

      edestruct extract_statement_list_ok_correct; eauto.

      destruct H0 as [? [? ?]].
      econstructor; simpl; eauto.

    Case "@None".
    inv PROGSEM. rewrite H0 in Heqo. clean.
  Qed.

(*  Fixpoint extract_statement (instructions: PTree.t I.instruction)
    nbr_params depth (ctxt: boxed_poly nbr_params depth)
    (st : statement nbr_params depth) :=
*)
End Extract.

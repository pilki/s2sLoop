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
Require Import PLang.
Require Import TimeStamp.
Require Import ExtractPoly.
Require Import Do_notation.
Require Import Tilling.
Open Scope string_scope.
(*Set Implicit Arguments.*)
Open Scope Z_scope.




Module Permut (Import M:BASEMEM(ZNum))
  (I:INSTRS(ZNum) with Definition Value := M.Value).
  Module Til := Tilling.Tilling(M)(I).
  Import Til.
  Import EP.
  Import P. Import T. Import L.
  Import Mem.

  Record Instruction_Point_DTS := {
    ip2_instruction : I.Instruction;
    ip2_arguments: Arguments (I.context_size ip2_instruction);
    ip2_time_stamp1: Time_Stamp;
    ip2_time_stamp2: Time_Stamp
  }.


  Definition compare_IP2TS_1 (comp_TS: Time_Stamp -> Time_Stamp -> Prop)
    ip2ts1 ip2ts2 : Prop :=
    comp_TS ip2ts1.(ip2_time_stamp1) ip2ts2.(ip2_time_stamp1).

  Definition compare_IP2TS_2 (comp_TS: Time_Stamp -> Time_Stamp -> Prop)
    ip2ts1 ip2ts2 : Prop :=
    comp_TS ip2ts1.(ip2_time_stamp2) ip2ts2.(ip2_time_stamp2).

  Definition ip_of_ip2ts_1 ip2ts :=
    {| ip_instruction := ip2ts.(ip2_instruction);
       ip_arguments := ip2ts.(ip2_arguments);
       ip_time_stamp := ip2ts.(ip2_time_stamp1)
    |}.

  Definition ip_of_ip2ts_2 ip2ts :=
    {| ip_instruction := ip2ts.(ip2_instruction);
       ip_arguments := ip2ts.(ip2_arguments);
       ip_time_stamp := ip2ts.(ip2_time_stamp2)
    |}.

  Definition ip2ts_semantics ip2ts mem1 mem2 :=
    instruction_point_semantics (ip_of_ip2ts_1 ip2ts) mem1 mem2.

  Definition ip2ts_list_semantics lip2 :=
    instruction_list_semantics (map ip_of_ip2ts_1 lip2).


(*  Inductive ip2ts_list_semantics: list Instruction_Point_DTS ->
    Memory -> Memory -> Prop:=
  | ILS_nil: forall mem, ip2ts_list_semantics [] mem mem
  | ILS_cons: forall mem1 mem2 mem3 ip il,
    ip2ts_semantics ip mem1 mem2 ->
    ip2ts_list_semantics il mem2 mem3 ->
    ip2ts_list_semantics (ip::il) mem1 mem3.*)


  Definition ip2ts_permutable ip2ts1 ip2ts2 :=
    forall mem1 mem2 mem3,
    ip2ts_semantics ip2ts1 mem1 mem2 ->
    ip2ts_semantics ip2ts2 mem2 mem3 ->
    forall mem1', mem1' ≡ mem1 ->
    exists mem2' mem3',(
      mem3' ≡ mem3 /\
      ip2ts_semantics ip2ts2 mem1' mem2' /\
      ip2ts_semantics ip2ts1 mem2' mem3').


(* move to lib *)


  Lemma EqA_memory_refl: forall m, m ≡ m.
  Proof. reflexivity. Qed.

  Lemma EqA_memory_sym: forall mem1 mem2, mem1 ≡ mem2 -> mem2 ≡ mem1.
  Proof. symmetry. auto. Qed.

  Lemma EqA_memory_trans: forall mem1 mem2 m3, mem1 ≡ mem2 -> mem2 ≡ m3 -> mem1 ≡ m3.
  Proof. etransitivity; eauto. Qed.

  Global Hint Immediate EqA_memory_sym: memory.
  Global Hint Resolve 5 EqA_memory_trans: memory.
  Hint Extern 1 (?X ≡ ?X) => reflexivity: memory.

  Lemma instruction_point_semantics_equiv:
    forall mem1 mem1' mem2 ip,
      instruction_point_semantics ip mem1 mem2 ->
      mem1' ≡ mem1 ->
      exists mem2', mem2' ≡ mem2 /\
        instruction_point_semantics ip mem1' mem2'.
  Proof.
    intros * SEM EQ.
    inv SEM.
    get_all_mem_layouts.
    match goal with
      | H: write mem1 ?cid ?V = Some _ |- _ =>
        assert (is_some (write mem1 cid V)) as IS by auto;
        apply (write_same_layout mem1 mem1') in IS; [|symmetry; assumption]
    end.
    inv IS as [mem2'].
    exists mem2'. clean.
    split'.
    Case "left".
      match goal with
        | H: write mem1 ?cid ?V = Some _ |- _ =>
          remember_no_eq cid as ciw;
          remember_no_eq V as v
      end.      
      rewrite EqA_memory_unfold.
      split'.
      SCase "left".
        apply write_keep_layout in H5. eauto with memory.
      SCase "right".
        intros.
        dest ci == ciw; subst.
        SSCase "ci = ciw".
          pose proof (rws _ _ ciw v H) as RWS.
          unfold read_write in RWS.
          rewrite H5 in RWS. rewrite H4 in RWS. simpl_do in *. assumption.
        SSCase "ci <> ciw".
          eapply rwo in H4; eauto.
          eapply rwo in H5; eauto.
          assert (read mem1 ci = read mem1' ci) by auto with memory.
          congruence.
     Case "right".
       econstructor; eauto.
       erewrite mmap_ext; [eauto|]. eauto with memory.
  Qed.

  Lemma ip2ts_semantics_equiv ip:
    forall mem1 mem2,
    ip2ts_semantics ip mem1 mem2 ->
    forall mem1',
      mem1' ≡ mem1 ->
      exists mem2', mem2' ≡ mem2 /\
        ip2ts_semantics ip mem1' mem2'.
  Proof.
    unfold ip2ts_semantics. intros. eapply instruction_point_semantics_equiv; eauto.
  Qed.

  Lemma ip2ts_list_semantics_equiv ip2tsl:
    forall mem1 mem2,
    ip2ts_list_semantics ip2tsl mem1 mem2 ->
    forall mem1',
      mem1' ≡ mem1 ->
      exists mem2', mem2' ≡ mem2 /\
        ip2ts_list_semantics ip2tsl mem1' mem2'.
  Proof.
    induction' ip2tsl as [|ip2ts ip2tsl].
    Case "nil".
      intros. inv H. exists mem1'; split; auto. constructor.
    Case "cons ip2ts ip2tsl".
      intros * SEM * EQ.
      inv SEM.
      edestruct ip2ts_semantics_equiv as [mem3' [? ?]]; eauto.
      edestruct IHip2tsl as [mem2' [? ?]]; eauto.
      eexists mem2'; split; eauto.
      econstructor; eauto.
  Qed.



(*  Lemma last_go_up_front ip2tsl ip2ts:
    list_forall (fun ip2ts' => ip2ts_permutable ip2ts' ip2ts) ip2tsl ->
    forall mem1 mem2, ip2ts_list_semantics (ip2tsl ++ [ip2ts]) mem1 mem2 ->
    forall mem1', mem1' ≡ mem1 ->
    exists mem2',(mem2' ≡ mem2 /\
      ip2ts_list_semantics (ip2ts::ip2tsl) mem1' mem2').
  Proof.
     induction' ip2tsl as [|ip2ts' ip2tsl]; intros FORALL * SEM * EQUIV; simpl in *.
     Case "nil".
       inv SEM. inv H4.
       edestruct instruction_point_semantics_equiv as [mem2' [? ?]]; eauto.
       exists mem2'; split; auto. econstructor; eauto. constructor.
     Case "cons ip2ts' ip2tsl".
       inv FORALL.
       inv SEM.
       edestruct IHip2tsl as [mem2' [? ?]]; eauto. reflexivity.
       inv H0.
       unfold ip2ts_permutable in H1.
       specialize (H1 _ _ _ H3 H7 _ EQUIV).
       destruct H1 as [mem2'' [mem3' [? [? ?]]]].
       edestruct ip2ts_list_semantics_equiv as [memf [? ?]]; eauto.
       exists memf; split; eauto.
       etransitivity; eauto.
       repeat (econstructor; eauto).
  Qed.*)

  Lemma first_go_last ip2tsl ip2ts:
    list_forall (fun ip2ts' => ip2ts_permutable ip2ts ip2ts') ip2tsl ->
    forall mem1 mem2, ip2ts_list_semantics (ip2ts :: ip2tsl) mem1 mem2 ->
    forall mem1', mem1' ≡ mem1 ->
    exists mem2',(mem2' ≡ mem2 /\
      ip2ts_list_semantics (ip2tsl ++ [ip2ts]) mem1' mem2').
  Proof.
     induction' ip2tsl as [|ip2ts' ip2tsl]; intros FORALL * SEM * EQUIV; simpl in *.
     Case "nil".
       inv SEM. inv H4.
       edestruct instruction_point_semantics_equiv as [mem2' [? ?]]; eauto.
       exists mem2'; split; auto. econstructor; eauto. constructor.
     Case "cons ip2ts' ip2tsl".
       inv FORALL.
       inv SEM.
       inv H6. unfold ip2ts_permutable in H1.
       edestruct H1 as [mem3' [mem4' [? [? ?]]]]; eauto.
       destruct (ip2ts_list_semantics_equiv _ _ _ H8 mem4' H) as [mem2' [? ?]].
       assert (ip2ts_list_semantics (ip2ts :: ip2tsl) mem3' mem2').
         econstructor; eauto.
       edestruct IHip2tsl as [mem2'' [? ?]]. eauto. eauto. reflexivity.
       exists mem2''; split'.
       SCase "left".
         etransitivity; eauto.
       SCase "right".
         econstructor; eauto.
  Qed.

  Lemma Permutation_cons_exists A a (l1 l2 :list A):
    Permutation (a::l1) l2 ->
    exists l21 l22,
      ( l2 = l21 ++ a :: l22 /\
        Permutation l1 (l21 ++ l22)).
  Proof.
    intros.
    edestruct Permutation_cons_exists_aux as [l21 [l22 EQ]]; eauto.
    exists l21 l22; split; auto.
    subst. eapply Permutation_cons_app_inv; eauto.
  Qed.

  Lemma ip2ts_list_semantics_app: forall ipl1 ipl2 mem1 mem3,
    ip2ts_list_semantics (ipl1 ++ ipl2) mem1 mem3 ->
    exists mem2,
      ( ip2ts_list_semantics ipl1 mem1 mem2 /\
        ip2ts_list_semantics ipl2 mem2 mem3).
  Proof.
    induction' ipl1 as [|ip1 ipl1]; intros; simpl in *.
    Case "nil".
      exists mem1; split; auto. constructor.
    Case "cons ip1 ipl1".
      inv H.
      edestruct IHipl1 as [mem2' [? ?]]; eauto.
      exists mem2'; split; eauto.
      econstructor; eauto.
  Qed.

  Lemma ip2ts_list_semantics_app_2: forall ipl1 ipl2 mem1 mem2 mem3,
    ip2ts_list_semantics ipl1 mem1 mem2 ->
    ip2ts_list_semantics ipl2 mem2 mem3 ->
    ip2ts_list_semantics (ipl1 ++ ipl2) mem1 mem3.
  Proof.
    unfold ip2ts_list_semantics.
    intros. rewrite map_app.
    eapply instruction_list_semantics_app2; eauto.
  Qed.
    

  Lemma cons_middle_app A (l1 l2: list A) (a:A):
    l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
  Proof.
    induction l1; simpl in *; congruence.
  Qed.


  Theorem two_sorted_same_semantics ipl1 ipl2:
    Permutation ipl1 ipl2 ->
    Sorted (compare_IP2TS_1 time_stamp_lt) ipl1 ->
    Sorted (compare_IP2TS_2 time_stamp_le) ipl2 ->
    (forall ip1 ip2,
      In ip1 ipl1 ->
      In ip2 ipl2 ->
      (compare_IP2TS_1 time_stamp_lt) ip1 ip2 ->
      (compare_IP2TS_2 time_stamp_le) ip2 ip1 ->
      ip2ts_permutable ip1 ip2) ->
    forall mem1 mem2,
    ip2ts_list_semantics ipl1 mem1 mem2 ->
    forall mem1', mem1' ≡ mem1 ->
    exists mem2',
      ( mem2' ≡ mem2 /\
        ip2ts_list_semantics ipl2 mem1' mem2').
  Proof.
    revert ipl2.
    induction' ipl1 as [|ip1 ipl1]; 
      intros * PERM SORTED1 SORTED2 SWAP * SEM * EQ.
    Case "nil".
      inv SEM. clean.
      exists mem1'; split; auto. constructor.
    Case "cons ip1 ipl1".
      edestruct Permutation_cons_exists as [ipl21 [ipl22 [? PERM']]]; eauto. subst.
      inv SEM as [|? ? ? ? ? SEMI SEML].
      edestruct ip2ts_semantics_equiv as [mem3' [? ?]]; eauto.

      edestruct IHipl1 as [mem2' [? ?]]; eauto.
      SCase "Sorted ipl1".
        inv SORTED1; auto.
      SCase "Sorted ipl21 ++ ipl22".
        clear' - SORTED2.
        apply StronglySorted_Sorted.
        apply Sorted_StronglySorted in SORTED2;[|
          unfold Relations_1.Transitive; unfold compare_IP2TS_2;
            intros; etransitivity; solve [eauto]].
        revert SORTED2.
        induction ipl21; simpl in *; intro.
        inv SORTED2; auto.
        inv SORTED2; econstructor; eauto.
        clear'- H2. induction ipl21; simpl in *; inv H2; auto.
          
      SCase "Permutable".
        intros. apply SWAP; auto. right; assumption.
        apply in_app_or in H2. apply in_or_app. destruct' H2; auto.
        right; right. auto.

      edestruct ip2ts_list_semantics_app as [mem4 [? ?]]; eauto.

      rewrite cons_middle_app.
      assert (ip2ts_list_semantics (ip1::ipl21) mem1' mem4).
      econstructor; eauto.
(*      pose proof (ip2ts_list_semantics_app_2 _ _ _ _ _ H5 H4). simpl in H6.

      edestruct (ip2ts_list_semantics_equiv ipl22) as [mem2'' [? ?]]; eauto.
      exists mem2''; split. etransitivity; eauto.
      eapply ip2ts_list_semantics_app_2; eauto.*)



      assert' (exists mem4',(
        mem4' ≡ mem4 /\
        ip2ts_list_semantics (ipl21++[ip1]) mem1' mem4')) as MEM4'.
      SCase "Assert: MEM4'".
        eapply first_go_last; eauto.
        SSCase "Forall permutable".
          apply forall_list_forall.
          intros ip IN.
          apply SWAP; auto.
          S3Case "In1".
            left; auto.
          S3Case "In2".
            apply in_or_app. auto.
          S3Case "compare1".
            apply Sorted_StronglySorted in SORTED1. inv SORTED1.
            rewrite Forall_forall in H9. apply H9. eapply Permutation_in. symmetry; eauto.
            apply in_or_app. auto.
            unfold Relations_1.Transitive; unfold compare_IP2TS_1; intros; etransitivity; eauto.
          S3Case "compare2".
            clear' - SORTED2 IN.
            apply Sorted_StronglySorted in SORTED2.
            revert SORTED2 IN.
            induction' ipl21 as [|ip21 ipl21]; intros; clean.
            simpl in *. destruct' IN.
            S5Case "ip21 = ip".
              subst.
              inv SORTED2.
              rewrite Forall_forall in H2. apply H2.
                clear'; induction ipl21; simpl; auto.
            S5Case "In ip ipl21".
              inv SORTED2; eauto.
            unfold Relations_1.Transitive, compare_IP2TS_2; intros; etransitivity; eauto.
        reflexivity.
    End_of_assert MEM4'.
      destruct MEM4' as [mem4' [? ?]].
      edestruct (ip2ts_list_semantics_equiv ipl22) as [mem2'' [? ?]]; eauto.
      exists mem2''; split. etransitivity; eauto.
      eapply ip2ts_list_semantics_app_2; eauto.
  Qed.

  
  Theorem different_access_permutable (ip1 ip2: Instruction_Point_DTS):
    let tloc1 := translate_locs (extend_arguments ip1.(ip2_arguments)) in
    let tloc2 := translate_locs (extend_arguments ip2.(ip2_arguments)) in
    let wloc1 := tloc1 (I.write_loc ip1.(ip2_instruction)) in
    let wloc2 := tloc2 (I.write_loc ip2.(ip2_instruction)) in
    (* different write loc *)
    wloc1 <> wloc2 ->
    (* ip2 does not read were ip1 writes *)
    list_forall (fun rloc2 => tloc2 rloc2 <> wloc1)
      (I.read_locs ip2.(ip2_instruction)) ->
    (* ip1 does not read were ip2 writes *)
    list_forall (fun rloc1 => tloc1 rloc1 <> wloc2)
      (I.read_locs ip1.(ip2_instruction)) ->
    ip2ts_permutable ip1 ip2.
    Proof.
      intros * WW W1R2 W2R1.
      unfold ip2ts_permutable.
      intros * SEM12 SEM23 * EQ.
      assert' (same_memory_layout mem1 mem2) as SMT12.
      Case "Assert: SMT12".
        inv SEM12. eapply write_keep_layout; eauto.
      End_of_assert SMT12.
      assert' (same_memory_layout mem2 mem3) as SMT23.
      Case "Assert: SMT23".
        inv SEM23. eapply write_keep_layout; eauto.
      End_of_assert SMT23.
      assert' (forall ci, ci <> wloc1 ->
        read mem2 ci = read mem1 ci) as SAMEREAD12.
      Case "Assert: SAMEREAD12".
        intros.
        inv SEM12. eapply rwo; eauto.
      End_of_assert SAMEREAD12.
      assert' (forall ci, ci <> wloc2 ->
        read mem3 ci = read mem2 ci) as SAMEREAD23.
      Case "Assert: SAMEREAD23".
        intros.
        inv SEM23. eapply rwo; eauto.
      End_of_assert SAMEREAD23.
      rewrite EqA_memory_unfold in EQ. destruct EQ as [SMT11' SAMEREAD11'].
      inv SEM12; inv SEM23.
      unfold ip_of_ip2ts_1 in *. simpl in *.
      repeat match goal with
               | H : _ |- _ => progress (fold tloc1 in H)
               | H : _ |- _ => progress (fold tloc2 in H)
               | H : _ |- _ => progress (fold wloc1 in H)
               | H : _ |- _ => progress (fold wloc2 in H)
             end.

      assert' (is_some (write mem1' wloc2 wval0)) as ISSOME1.
      Case "Assert: ISSOME1".
        apply (write_same_layout mem2).
          transitivity mem1; symmetry; assumption.
          rewrite H7. auto.
      End_of_assert ISSOME1.
      inv ISSOME1 as [mem2' EQMEM2'].
      exists mem2'.
      assert' (is_some (write mem2' wloc1 wval)) as ISSOME2.
      Case "Assert: ISSOME2".
        apply (write_same_layout mem1).
          transitivity mem1'; auto.
            symmetry; assumption.
            eapply write_keep_layout; eauto.
            rewrite H4; auto.
      End_of_assert ISSOME2.
      inv ISSOME2 as [mem3' EQMEM3'].
      assert (forall ci, ci <> wloc2 ->
        read mem2' ci = read mem1' ci) as SAMEREAD1'2' by
        (intros; eapply rwo; eauto).
      assert (forall ci, ci <> wloc1 ->
        read mem3' ci = read mem2' ci) as SAMEREAD2'3' by
        (intros; eapply rwo; eauto).
      exists mem3'.
      split; [Case "EQUIV"| split; [Case "sem ip2"|Case "sem ip1"]].
      Case "EQUIV".
        rewrite EqA_memory_unfold.
        split'.
        SCase "left".
          transitivity mem2'. symmetry; eapply write_keep_layout; eauto.
          transitivity mem1'. symmetry; eapply write_keep_layout; eauto.
          eauto with memory.
        SCase "right".
          intro ci.
          dest ci == wloc2.
          SSCase "ci = wloc2".
            subst.
            rewrite SAMEREAD2'3'; auto.
            assert (same_memory_layout mem1' mem2) as SMT1'2 by eauto with memory.
            pose proof (rws mem1' mem2 wloc2 wval0 SMT1'2) as RWS1'2.
            unfold read_write in RWS1'2. rewrite <- EQMEM2' in RWS1'2.
            rewrite H7 in RWS1'2. simpl_do in RWS1'2. assumption.
          SSCase "ci <> wloc2".
            rewrite SAMEREAD23; auto.
            dest ci == wloc1.
            S3Case "ci = wloc1".
              clean.
              assert (same_memory_layout mem2' mem1) as SMT2'1 by
                (transitivity mem1'; [symmetry; eapply write_keep_layout; eauto| assumption]).
              pose proof (rws mem2' mem1 wloc1 wval SMT2'1) as RWS2'1.
              unfold read_write in RWS2'1. rewrite EQMEM3' in RWS2'1.
              rewrite H4 in RWS2'1. simpl_do in *. assumption.
            S3Case "ci <> wloc1".
              rewrite SAMEREAD2'3'; auto. rewrite SAMEREAD1'2'; auto.
              rewrite SAMEREAD12; auto.
      Case "sem ip2".
        unfold ip2ts_semantics.
        
        econstructor; eauto. rewrite <- H3.
        unfold ip_of_ip2ts_1; simpl. fold tloc2.
        clearbody tloc2.
        assert (forall ci, ci <> wloc1 ->
          read mem1' ci = read mem2 ci) as SAMEREAD21'
        by (intros; transitivity (read mem1 ci); eauto; symmetry; eauto).
        remember_no_eq (I.read_locs (ip2.(ip2_instruction))) as rlocs2.
        clear' - W1R2 SAMEREAD21'.
        induction' rlocs2 as [| rloc2 rlocs2]; intros; simpl in *; auto.
        SCase "cons rloc2 rlocs2".
          inv W1R2. specialize (IHrlocs2 H2). rewrite IHrlocs2.
          match goal with
            | |- 
              (do _ <- ?X ; _) = (do _ <- ?Y; _) =>
                assert (X = Y) as EQ; [auto|rewrite EQ; reflexivity]
          end.
      Case "sem ip1".
        unfold ip2ts_semantics.
        
        econstructor; eauto. rewrite <- H1.
        unfold ip_of_ip2ts_1; simpl. fold tloc1.
        clearbody tloc1.
        assert (forall ci, ci <> wloc2 ->
          read mem2' ci = read mem1 ci) as SAMEREAD2'1 by
          (intros; transitivity (read mem1' ci); eauto).
        remember_no_eq (I.read_locs (ip1.(ip2_instruction))) as rlocs1.
        clear' - W2R1 SAMEREAD2'1.
        induction' rlocs1 as [| rloc1 rlocs1]; intros; simpl in *; auto.
        SCase "cons rloc1 rlocs1".
          inv W2R1. specialize (IHrlocs1 H2). rewrite IHrlocs1.
          match goal with
            | |- 
              (do _ <- ?X ; _) = (do _ <- ?Y; _) =>
                assert (X = Y) as EQ; [auto|rewrite EQ; reflexivity]
          end.
  Qed.


  Record Polyhedral_Instruction_DTS
    (nbr_global_parameters:nat):=
    { (** the instruction *)
      pi2_instr: I.Instruction;
      (** the depth of the instruction in the program *)
      pi2_depth: nat;
      (** the Polyhedron *)
      pi2_poly: Boxed_Polyhedron nbr_global_parameters pi2_depth;
      pi2_poly_ext: Polyhedron (S (pi2_depth + nbr_global_parameters));
      pi2_poly_ext_eq: pi2_poly_ext = extend_polyhedron pi2_poly.(bp_poly);
      (** the schedule of the instruction *)
      pi2_schedule1:
        list (ZVector (S (pi2_depth + nbr_global_parameters)));
      pi2_schedule2:
        list (ZVector (S (pi2_depth + nbr_global_parameters)));
      (** transformation to move from elements of the polyhedron to the
         arguments of the instruction*)
      pi2_transformation:
        ZMatrix (I.context_size pi2_instr) (S (pi2_depth + nbr_global_parameters));
(*      (** we keep the transposed matrix to avoid recalculating it over and over
         again *)
      pi2_transformation_transp:
        ZMatrix (S (pi2_depth + nbr_global_parameters)) (I.context_size pi2_instr);
      pi2_transformation_transp_is_transp:
        pi2_transformation_transp = Mtranspose pi2_transformation;*)

      (** we translate the locations so we don't have to compute it again every time*)
      pi2_wloc: Array_Id * list (Vector Z (S (pi2_depth + nbr_global_parameters)));
      pi2_wloc_eq:
        pi2_wloc = (fst (I.write_loc pi2_instr),
          map (fun v => Mprod_vect_right v (extend_matrix pi2_transformation))
          (snd (I.write_loc pi2_instr)));
      pi2_rlocs: list (Array_Id * list (Vector Z (S (pi2_depth + nbr_global_parameters))));
      pi2_rlocs_eq:
        pi2_rlocs =
        map (fun loc =>
          (fst loc,
          map (fun v => Mprod_vect_right v (extend_matrix pi2_transformation))
          (snd loc))) (I.read_locs pi2_instr)
    }.


  Implicit Arguments pi2_instr [[nbr_global_parameters]].
  Implicit Arguments pi2_depth [[nbr_global_parameters]].
  Implicit Arguments pi2_poly [[nbr_global_parameters]].
  Implicit Arguments pi2_schedule1 [[nbr_global_parameters]].
  Implicit Arguments pi2_schedule2 [[nbr_global_parameters]].
  Implicit Arguments pi2_transformation [[nbr_global_parameters]].
  Implicit Arguments pi2_wloc [[nbr_global_parameters]].
  Implicit Arguments pi2_rlocs [[nbr_global_parameters]].
  Implicit Arguments pi2_poly_ext [[nbr_global_parameters]].


  Definition expand_poly_instr_DTS {nbr_global_parameters}
    (params: Global_Parameters nbr_global_parameters)
    (pi: Polyhedral_Instruction_DTS nbr_global_parameters)
    : list Instruction_Point_DTS:=
    (** build the list of contexts *)
    let ectxts := map (make_context_ext params) (pi.(pi2_poly).(bp_elts) params) in
    (** build one instruction point from each environement *)
    map (fun ectxt =>
      {| ip2_instruction := pi.(pi2_instr);
         ip2_arguments := pi.(pi2_transformation) × ectxt;
         ip2_time_stamp1 := apply_schedule pi.(pi2_schedule1) ectxt;
         ip2_time_stamp2 := apply_schedule pi.(pi2_schedule2) ectxt
         |})
      ectxts.

  (* find better name *)
(*  Definition make_poly_containing_things {dim1 dim2} {num_args1 num_args2}
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
    apply PVeq_Veq. simpl.  unalias in *.
    unfold ZNum.Numerical_Num in *.
    rewrite <- H0.
    f_equal. assumption.
  Qed. *)
  Require Import Recdef.
  Set Implicit Arguments.


  Ltac spec_lia :=
    unfold satisfy_constraint in *; simpl in *; simpl_vect in *; simpl in *;
    unfold Inhab_num, Inhabited_Z, ZNum.Numerical_Num in *; lia.

  Ltac simplify_goal :=
    repeat (
      match goal with
        | |- _ <-> _ =>
          split'
        | |- _ /\ _ =>
          split'
        | H : _ /\ _ |- _ =>
          destruct H
        | H : _ <-> _ |- _ =>
          destruct H
        | H : ?X -> ?Y
        , H1 : ?X |- _ =>
          match Y with
            | _ -> _ => fail 1
            | _ => specialize (H H1)
          end
        | H : (?X /\ ?Y) -> _
        , H1 : ?X
        , H2 : ?Y |- _ => specialize (H (conj H1 H2))
        | H : time_stamp_lt_0 [] |- _ => inv H
        | H : time_stamp_gt_0 [] |- _ => inv H
        | H : time_stamp_lt_0 (_ :: _) |- _ => inv H
        | H : time_stamp_gt_0 (_ :: _) |- _ => inv H
        | H : Exists _ [] |- _ => inv H
        | H : Exists _ (_ :: _) |- _ => inv H
        | H : _ ∈ (_ :: _) |- _ => rewrite Pol_in_cons in H; destruct H
        | H : satisfy_constraint _ _ |- _ =>
          unfold satisfy_constraint in H; simpl in H; simpl_vect in H;
            simpl in H; unfold ZNum.Numerical_Num in *
        | H : (- ?x)%Z = 0%Z |- _ =>
          let H' := fresh in
          assert (x = 0)%Z as H' by spec_lia; clear H;
            unfold ZNum.Numerical_Num in *; rewrite H' in *
        | H : _ = 0%Z |- _ =>
          progress (unfold ZNum.Numerical_Num in *; rewrite H in *)
      end; intros).

  Ltac solve_simpl_goal :=
    repeat 
    (simplify_goal;
      try
     match goal with
       | |- _ ∈ _ :: _ =>
         rewrite Pol_in_cons
       | |- Exists _ (_ :: _) =>
         try solve [constructor 1; solve_simpl_goal];
         solve [constructor 2; auto;
           try match goal with
                 | H : context[_ <-> Exists _ _] |- _ =>
                   rewrite <- H
               end;
           solve_simpl_goal]
       | |- satisfy_constraint _ _ => spec_lia
       | H1 : context[_ <-> Exists _ _]
       , H2 : Exists _ _ |- _ =>
         let H11 := fresh in let H12 := fresh in 
           edestruct H1 as [H11 H12];
           specialize (H12 H2); destruct H12; simplify_goal; solve [auto]
     end); auto.

Hint Constructors time_stamp_lt_0 time_stamp_gt_0.

  Fixpoint make_poly_lt0_l {dim1 dim2: nat}
    (sched1: list (ZVector dim1)) (v2: ZVector dim2)
    (pol: Polyhedron (dim1 + dim2)) :=
    match sched1 with
      | [] => []
      | v1 :: sched1' =>
        let v := (-- v1) +++ v2 in
        ((mkConstraint v GE 1) :: pol) ::
        (make_poly_lt0_l sched1' v2 ((mkConstraint v EQ 0) :: pol))
    end.


  Lemma make_poly_lt0_l_correct (dim1 dim2: nat)
    (sched1: list (ZVector dim1))
    (pol: Polyhedron (dim1 + dim2)):
    forall v1 v2,
      ((v1 +++ v2) ∈ pol /\ time_stamp_lt_0 (map (fun vs1 => 〈vs1, v1〉) sched1)) <->
      Exists (fun p => (v1 +++ v2) ∈ p) (make_poly_lt0_l sched1 (V0 dim2) pol).
  Proof.
    revert pol.
    induction' sched1 as [|vs sched1]; simpl; intros *;
      solve_simpl_goal.

    constructor. lia.
  Qed.

  Fixpoint make_poly_lt0_r {dim1 dim2: nat}
     (v1: ZVector dim1) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2)) :=
    match sched2 with
      | [] => []
      | v2 :: sched2' =>
        let v := v1 +++ (--v2) in
        ((mkConstraint v GE 1) :: pol) ::
        (make_poly_lt0_r v1 sched2' ((mkConstraint v EQ 0) :: pol))
    end.


  Lemma make_poly_lt0_r_correct (dim1 dim2: nat)
    (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2)):
    forall v1 v2,
      ((v1 +++ v2) ∈ pol /\ time_stamp_lt_0 (map (fun vs2 => 〈vs2, v2〉) sched2)) <->
      Exists (fun p => (v1 +++ v2) ∈ p) (make_poly_lt0_r (V0 dim1) sched2 pol).
  Proof.
    revert pol.
    induction' sched2 as [|vs sched2]; simpl; intros *;
      solve_simpl_goal.

    constructor. lia.
  Qed.

  Fixpoint make_poly_gt0_r {dim1 dim2: nat}
    (v1: ZVector dim1) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2))
    : list (Polyhedron (dim1 + dim2)):=
    match sched2 with
      | []=> []
      | v2 :: sched2' =>
        let v := (-- v1) +++ v2 in
        ((mkConstraint v GE 1) :: pol) ::
        (make_poly_gt0_r v1 sched2' ((mkConstraint v EQ 0) :: pol))
    end.


  Lemma make_poly_gt0_r_correct (dim1 dim2: nat)
    (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2)):
    forall v1 v2,
      ((v1 +++ v2) ∈ pol /\ time_stamp_gt_0 (map (fun vs2 => 〈vs2, v2〉) sched2)) <->
      Exists (fun p => (v1 +++ v2) ∈ p) (make_poly_gt0_r (V0 dim1) sched2 pol).
  Proof.
    revert pol.
    induction' sched2 as [|vs sched2]; simpl; intros *; solve_simpl_goal.
    constructor. lia.
  Qed.

  Fixpoint make_poly_gt0_l {dim1 dim2: nat}
    (sched1: list (ZVector dim1)) (v2: ZVector dim2)
    (pol: Polyhedron (dim1 + dim2))
    : list (Polyhedron (dim1 + dim2)):=
    match sched1 with
      | []=> []
      | v1 :: sched1' =>
        let v := v1 +++ (--v2) in
        ((mkConstraint v GE 1) :: pol) ::
        (make_poly_gt0_l sched1' v2 ((mkConstraint v EQ 0) :: pol))
    end.


  Lemma make_poly_gt0_l_correct (dim1 dim2: nat)
    (sched1: list (ZVector dim1))
    (pol: Polyhedron (dim1 + dim2)):
    forall v1 v2,
      ((v1 +++ v2) ∈ pol /\ time_stamp_gt_0 (map (fun vs1 => 〈vs1, v1〉) sched1)) <->
      Exists (fun p => (v1 +++ v2) ∈ p) (make_poly_gt0_l sched1 (V0 dim2) pol).
  Proof.
    revert pol.
    induction' sched1 as [|vs sched1]; simpl; intros *; solve_simpl_goal.
    constructor. lia.
  Qed.


  Fixpoint make_poly_lt {dim1 dim2: nat}
    (sched1: list (ZVector dim1)) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2))
    : list (Polyhedron (dim1 + dim2)):=
    match sched1, sched2 with
      | [], [] => []
      | v1 :: sched1', v2 :: sched2' =>
        let v := (-- v1) +++ v2 in
        ((mkConstraint v GE 1) :: pol) ::
        (make_poly_lt sched1' sched2' ((mkConstraint v EQ 0) :: pol))
      | v1 :: sched1', nil =>
        make_poly_lt0_l sched1 (V0 dim2) pol 
      | [], v2 :: sched2' =>
        make_poly_gt0_r (V0 dim1) sched2 pol
    end.
  
  Lemma make_poly_lt_correct (dim1 dim2: nat)
    (sched1: list (ZVector dim1)) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2)):
    forall v1 v2,
      ((v1 +++ v2) ∈ pol /\
        time_stamp_lt (map (fun vs1 => 〈vs1, v1〉) sched1) (map (fun vs2 => 〈vs2, v2〉) sched2)) <->
      Exists (fun p => (v1 +++ v2) ∈ p) (make_poly_lt sched1 sched2 pol).
  Proof.
    revert sched2 pol.
    induction' sched1 as [|vs1 sched1]; intros *;
      destruct' sched2 as [|vs2 sched2];
      split'; first [intros [IN TSL]||intro EX].
    Case "nil"; SCase "nil"; SSCase "->".
      inv TSL; inv H.
    Case "nil"; SCase "nil"; SSCase "<-".
      inv EX.
    Case "nil"; SCase "cons vs2 sched2"; SSCase "->".
      unfold make_poly_lt. rewrite <- make_poly_gt0_r_correct.
      inv TSL. split; auto.
    Case "nil"; SCase "cons vs2 sched2"; SSCase "<-".
      unfold make_poly_lt in EX. rewrite <- make_poly_gt0_r_correct in EX.
      destruct EX; split; auto.
    Case "cons vs1 sched1"; SCase "nil"; SSCase "->".
      unfold make_poly_lt. rewrite <- make_poly_lt0_l_correct.
      inv TSL. split; auto.
    Case "cons vs1 sched1"; SCase "nil"; SSCase "<-". 
      unfold make_poly_lt in EX. rewrite <- make_poly_lt0_l_correct in EX.
      destruct EX; split; auto.
    Case "cons vs1 sched1"; SCase "cons vs2 sched2"; SSCase "->".
      inv TSL.
      S3Case "<".
        simpl. constructor. constructor; auto. red; simpl. simpl_vect.
        simpl in *. unfold ZNum.Numerical_Num in *. lia.
      S3Case "=".
        simpl. constructor 2. rewrite <- IHsched1.
        split'; auto.
        S4Case "left".
          constructor; auto.
          red; simpl. simpl_vect. simpl in *.  unfold ZNum.Numerical_Num in *. lia.
    Case "cons vs1 sched1"; SCase "cons vs2 sched2"; SSCase "<-".
      inv' EX.
      S3Case "Exists_cons_hd".
        inv H0. red in H2; simpl in H2. simpl_vect in H2. simpl in H2.
        split'; auto.
        S4Case "right".
          simpl. constructor; auto.
          unfold ZNum.Numerical_Num in *. lia.
      S3Case "Exists_cons_tl".
        rewrite <- IHsched1 in H0. destruct H0.
        inv H. red in H3; simpl in H3; simpl_vect in H3; simpl in H3.
        split'; auto.
        S4Case "right".
        simpl.
        unfold ZNum.Numerical_Num in *.
        replace (〈vs1, v1〉) with (〈vs2, v2〉).
        apply TSLT_eq; auto.
        simpl in *. unfold ZNum.Numerical_Num in *. lia.
  Qed.

  Fixpoint make_poly_gt {dim1 dim2: nat}
    (sched1: list (ZVector dim1)) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2))
    : list (Polyhedron (dim1 + dim2)):=
    match sched1, sched2 with
      | [], [] => []
      | v1 :: sched1', v2 :: sched2' =>
        let v := v1 +++ (--v2) in
        ((mkConstraint v GE 1) :: pol) ::
        (make_poly_gt sched1' sched2' ((mkConstraint v EQ 0) :: pol))
      | v1 :: sched1', nil =>
        make_poly_gt0_l sched1 (V0 dim2) pol 
      | [], v2 :: sched2' =>
        make_poly_lt0_r  (V0 dim1) sched2 pol
    end.
  
  Lemma make_poly_gt_correct (dim1 dim2: nat)
    (sched1: list (ZVector dim1)) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2)):
    forall v1 v2,
      ((v1 +++ v2) ∈ pol /\
        time_stamp_lt (map (fun vs2 => 〈vs2, v2〉) sched2) (map (fun vs1 => 〈vs1, v1〉) sched1)) <->
      Exists (fun p => (v1 +++ v2) ∈ p) (make_poly_gt sched1 sched2 pol).
  Proof.
    revert sched2 pol.
    induction' sched1 as [|vs1 sched1]; intros *;
      destruct' sched2 as [|vs2 sched2];
      split'; first [intros [IN TSL]||intro EX].
    Case "nil"; SCase "nil"; SSCase "->".
      inv TSL; inv H.
    Case "nil"; SCase "nil"; SSCase "<-".
      inv EX.
    Case "nil"; SCase "cons vs2 sched2"; SSCase "->".
      unfold make_poly_gt. rewrite <- make_poly_lt0_r_correct.
      inv TSL. split; auto.
    Case "nil"; SCase "cons vs2 sched2"; SSCase "<-".
      unfold make_poly_gt in EX. rewrite <- make_poly_lt0_r_correct in EX.
      destruct EX; split; auto.
    Case "cons vs1 sched1"; SCase "nil"; SSCase "->".
      unfold make_poly_gt. rewrite <- make_poly_gt0_l_correct.
      inv TSL. split; auto.
    Case "cons vs1 sched1"; SCase "nil"; SSCase "<-". 
      unfold make_poly_gt in EX. rewrite <- make_poly_gt0_l_correct in EX.
      destruct EX; split; auto.
    Case "cons vs1 sched1"; SCase "cons vs2 sched2"; SSCase "->".
      inv TSL.
      S3Case "<".
        simpl. constructor. constructor; auto. red; simpl. simpl_vect.
        simpl in *. unfold ZNum.Numerical_Num in *. lia.
      S3Case "=".
        simpl. constructor 2. rewrite <- IHsched1.
        split'; auto.
        S4Case "left".
          constructor; auto.
          red; simpl. simpl_vect. simpl in *.  unfold ZNum.Numerical_Num in *. lia.
    Case "cons vs1 sched1"; SCase "cons vs2 sched2"; SSCase "<-".
      inv' EX.
      S3Case "Exists_cons_hd".
        inv H0. red in H2; simpl in H2. simpl_vect in H2. simpl in H2.
        split'; auto.
        S4Case "right".
          simpl. constructor; auto.
          unfold ZNum.Numerical_Num in *. lia.
      S3Case "Exists_cons_tl".
        rewrite <- IHsched1 in H0. destruct H0.
        inv H. red in H3; simpl in H3; simpl_vect in H3; simpl in H3.
        split'; auto.
        S4Case "right".
        simpl.
        unfold ZNum.Numerical_Num in *.
        replace (〈vs1, v1〉) with (〈vs2, v2〉).
        apply TSLT_eq; auto.
        simpl in *. unfold ZNum.Numerical_Num in *. lia.
  Qed.


  Fixpoint make_poly_all0_l {dim1 dim2: nat}
    (sched1: list (ZVector dim1)) (v2: ZVector dim2)
    (pol: Polyhedron (dim1 + dim2)) : (Polyhedron (dim1 + dim2)):=
    match sched1 with
      | [] => pol
      | v1 :: sched1' =>
        let v := (-- v1) +++ v2 in
        (mkConstraint v EQ 0) ::
        (make_poly_all0_l sched1' v2 pol)
    end.

  

  Lemma make_poly_all0_l_correct (dim1 dim2: nat)
    (sched1: list (ZVector dim1))
    (pol: Polyhedron (dim1 + dim2)) v1 v2:
      ((v1 +++ v2) ∈ pol /\ time_stamp_all_0 (map (fun vs1 => 〈vs1, v1〉) sched1)) <->
      (v1 +++ v2) ∈ (make_poly_all0_l sched1 (V0 dim2) pol).
  Proof.
    induction' sched1 as [|vs1 sched1];[|destruct IHsched1]; intros *; split';
      first [intros [IN ALL0]|| intros INMK]; auto.
    Case "nil"; SCase "<-".
      simpl in INMK. split; auto.
      simpl. constructor.
    Case "cons vs1 sched1"; SCase "->".
      simpl in ALL0. inv ALL0. simpl in *.
      simpl. constructor; auto.
        red. simpl. simpl_vect. simpl. lia.
        apply H. split; auto.
    Case "cons vs1 sched1"; SCase "<-".
      inv INMK.
      specialize (H0 H4). destruct H0.
      split; auto.
      simpl. red in H3. simpl in H3; simpl_vect in H3; simpl in H3.
      replace (〈vs1, v1〉) with 0%Z.
      constructor; auto. lia.
   Qed.


  Fixpoint make_poly_all0_r {dim1 dim2: nat}
    (v1: ZVector dim1) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2)) : (Polyhedron (dim1 + dim2)):=
    match sched2 with
      | [] => pol
      | v2 :: sched2' =>
        let v := (-- v1) +++ v2 in
        (mkConstraint v EQ 0) ::
        (make_poly_all0_r v1 sched2' pol)
    end.

  

  Lemma make_poly_all0_r_correct (dim1 dim2: nat)
    (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2)) v1 v2:
      ((v1 +++ v2) ∈ pol /\ time_stamp_all_0 (map (fun vs2 => 〈vs2, v2〉) sched2)) <->
      (v1 +++ v2) ∈ (make_poly_all0_r (V0 dim1) sched2 pol).
  Proof.
    induction' sched2 as [|vs2 sched2];[|destruct IHsched2]; intros *; split';
      first [intros [IN ALL0]|| intros INMK]; auto.
    Case "nil"; SCase "<-".
      simpl in INMK. split; auto.
      simpl. constructor.
    Case "cons vs2 sched2"; SCase "->".
      simpl in ALL0. inv ALL0. simpl in *.
      simpl. constructor; auto.
        red. simpl. simpl_vect. simpl.
        simpl in *. unfold ZNum.Numerical_Num in *. lia.
        apply H. split; auto.
    Case "cons vs2 sched2"; SCase "<-".
      inv INMK.
      specialize (H0 H4). destruct H0.
      split; auto.
      simpl. red in H3. simpl in H3; simpl_vect in H3; simpl in H3.
      replace (〈vs2, v2〉) with 0%Z.
      constructor; auto.
   Qed.

  Fixpoint make_poly_eq {dim1 dim2: nat}
    (sched1: list (ZVector dim1)) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2))
    : Polyhedron (dim1 + dim2):=
    match sched1, sched2 with
      | [], [] => pol
      | v1 :: sched1', v2 :: sched2' =>
        let v := (-- v1) +++ v2 in
        (mkConstraint v EQ 0) ::
        (make_poly_eq sched1' sched2' pol)
      | v1 :: sched1', nil =>
        make_poly_all0_l sched1 (V0 dim2) pol 
      | [], v2 :: sched2' =>
        make_poly_all0_r (V0 dim1) sched2 pol
    end.

  Lemma make_poly_eq_correct (dim1 dim2: nat)
    (sched1: list (ZVector dim1)) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2)) v1 v2:
      ((v1 +++ v2) ∈ pol /\
        time_stamp_eq (map (fun vs1 => 〈vs1, v1〉) sched1) (map (fun vs2 => 〈vs2, v2〉) sched2)) <->
      (v1 +++ v2) ∈ (make_poly_eq sched1 sched2 pol).
  Proof.
    revert sched2.
    induction' sched1 as [|vs1 sched1]; intros *;
      destruct' sched2 as [|vs2 sched2];
        split'; first [intros [IN TSL]||intro EX]; auto.
    Case "nil"; SCase "nil"; SSCase "<-".
      simpl in *; split; auto. constructor. constructor.
    Case "nil"; SCase "cons vs2 sched2"; SSCase "->".
      unfold make_poly_eq. rewrite <- make_poly_all0_r_correct.
      inv TSL. split; auto.
    Case "nil"; SCase "cons vs2 sched2"; SSCase "<-". 
      unfold make_poly_eq in EX. rewrite <- make_poly_all0_r_correct in EX.
      inv EX; split; simpl; auto.
    Case "cons vs1 sched1"; SCase "nil"; SSCase "->".
      unfold make_poly_eq. rewrite <- make_poly_all0_l_correct.
      inv TSL. split; auto.
    Case "cons vs1 sched1"; SCase "nil"; SSCase "<-". 
      unfold make_poly_eq in EX. rewrite <- make_poly_all0_l_correct in EX.
      inv EX; split; simpl; auto.
    Case "cons vs1 sched1"; SCase "cons vs2 sched2"; SSCase "->".
      simpl in TSL. inv TSL.
      simpl. constructor; auto.
      red. simpl. simpl_vect. simpl in *. unfold ZNum.Numerical_Num in *; lia.
      unfold Pol_In in *; rewrite <- IHsched1.
      split; auto.
    Case "cons vs1 sched1"; SCase "cons vs2 sched2"; SSCase "<-".
      simpl in EX. inv EX. red in H1; simpl in H1; simpl_vect in H1; simpl in H1.
      specialize (IHsched1 sched2).
      destruct IHsched1.
      destruct H0. auto.
      split; auto.
      simpl.
      replace (〈vs1, v1〉) with (〈vs2, v2〉).
      constructor; auto.
       unfold ZNum.Numerical_Num in *. lia.
  Qed.


  Definition make_poly_le {dim1 dim2: nat}
    (sched1: list (ZVector dim1)) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2))
    : list (Polyhedron (dim1 + dim2)):=
    (make_poly_eq sched1 sched2 pol) :: make_poly_lt sched1 sched2 pol.
  
  Lemma make_poly_le_correct (dim1 dim2: nat)
    (sched1: list (ZVector dim1)) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2)):
    forall v1 v2,
      ((v1 +++ v2) ∈ pol /\
        time_stamp_le (map (fun vs1 => 〈vs1, v1〉) sched1) (map (fun vs2 => 〈vs2, v2〉) sched2)) <->
      Exists (fun p => (v1 +++ v2) ∈ p) (make_poly_le sched1 sched2 pol).
  Proof.
    intros.
    split'.
    Case "->".
      intros [IN TLE].
      unfold time_stamp_le in TLE. unfold make_poly_le.
      destruct TLE.
      SCase "TLT".
      apply Exists_cons_tl. apply make_poly_lt_correct. split; auto.
      SCase "TEQ".
      apply Exists_cons_hd; apply make_poly_eq_correct. split; auto.
    Case "<-".
      intros. inv H.
      rewrite <- make_poly_eq_correct in H1. destruct H1.
      split; auto.
      rewrite <- make_poly_lt_correct in H1. destruct H1.
      split; auto.
  Qed.

  Definition make_poly_ge {dim1 dim2: nat}
    (sched1: list (ZVector dim1)) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2))
    : list (Polyhedron (dim1 + dim2)):=
    (make_poly_eq sched1 sched2 pol) :: make_poly_gt sched1 sched2 pol.
  
  Lemma make_poly_ge_correct (dim1 dim2: nat)
    (sched1: list (ZVector dim1)) (sched2: list (ZVector dim2))
    (pol: Polyhedron (dim1 + dim2)):
    forall v1 v2,
      ((v1 +++ v2) ∈ pol /\
        time_stamp_le (map (fun vs2 => 〈vs2, v2〉) sched2) (map (fun vs1 => 〈vs1, v1〉) sched1)) <->
      Exists (fun p => (v1 +++ v2) ∈ p) (make_poly_ge sched1 sched2 pol).
  Proof.
    intros.
    split'.
    Case "->".
      intros [IN TLE].
      unfold time_stamp_le in TLE. unfold make_poly_ge.
      destruct TLE.
      SCase "TLT".
      apply Exists_cons_tl. apply make_poly_gt_correct. split; auto.
      SCase "TEQ".
      apply Exists_cons_hd; apply make_poly_eq_correct. split; auto. symmetry. auto.
    Case "<-".
      intros. inv H.
      rewrite <- make_poly_eq_correct in H1. destruct H1. symmetry in H0.
      split; auto. 
      rewrite <- make_poly_gt_correct in H1. destruct H1.
      split; auto.
  Qed.
    

  Definition validate_one_loc {dim1 dim2}
    (pol: Polyhedron (dim1 + dim2))
    (loc1: Array_Id * list (ZVector dim1))
    (loc2: Array_Id * list (ZVector dim2))
    (pols_lt: list (Polyhedron (dim1 + dim2)))
    (pols_ge: list (Polyhedron (dim1 + dim2))) : res unit :=
    let (id1, loc1) := loc1 in
    let (id2, loc2) := loc2 in
    if id1 == id2 then
      match safe_map2 (fun v1 v2 => mkConstraint ((-- v1) +++ v2) EQ 0) loc1 loc2 with
      | None => Err "Access to the same array with different dimensions"
      | Some sameloc =>
      let sameloc_pol := sameloc ∩ pol in
      if
      (list_forall_semi_dec
        (fun pol_lt =>
          list_forall (fun pol_ge : Polyhedron (dim1 + dim2) =>
              pol_ge ∩ (pol_lt ∩ (sameloc ∩ pol))  ≈∅)
            pols_ge)
        (fun _ => True)
        (fun pol_lt => let pol_lt_sameloc := pol_lt ∩ sameloc_pol in
          list_forall_semi_dec _ (fun _ => True) 
            (fun pol_ge => Pol_Empty_sdec (pol_ge ∩ pol_lt_sameloc)) pols_ge) pols_lt)
      then OK tt else
      Err "Could not validate the emptyness of all polyhedra"
      end
    else
      OK tt.

  Definition translate_locs' {dim} (ectxt: ZVector dim)
    (p: Array_Id * list (ZVector dim)): Cell_Id Z:=
    {| array := fst p;
       cell := List.map (fun v =>〈v, ectxt〉) (snd p)|}.

  Lemma validate_one_loc_OK dim1 dim2
    (pol: Polyhedron (dim1 + dim2))
    (loc1: Array_Id * list (ZVector dim1))
    (loc2: Array_Id * list (ZVector dim2))
    (pols_lt: list (Polyhedron (dim1 + dim2)))
    (pols_ge: list (Polyhedron (dim1 + dim2))):
    validate_one_loc pol loc1 loc2 pols_lt pols_ge = OK tt ->
    forall v1 v2, 
      v1 +++ v2 ∈ pol ->
      Exists (fun pol_lt => v1 +++ v2 ∈ pol_lt) pols_lt ->
      Exists (fun pol_ge => v1 +++ v2 ∈ pol_ge) pols_ge ->
      ~(translate_locs' v1 loc1 = translate_locs' v2 loc2).
  Proof.
    intros VALOK * IN EXLT EXGE EQ.
    unfold validate_one_loc in VALOK.
    destruct loc1 as (id1, loc1).
    destruct loc2 as (id2, loc2).
    dest id1 == id2.
    Case "id1 = id2".
      prog_match_option; clean.
      assert' (v1 +++ v2 ∈ sameloc) as INSAME.
      SCase "Assert: INSAME".
        clear' - Heqo EQ.
        inv EQ.
        revert dependent loc2. revert sameloc.
        induction' loc1 as [|l1 loc1]; intros; destruct' loc2 as [|l2 loc2]; simpl in *;
          clean.
        SSCase "nil"; S3Case "nil".
          constructor.
        SSCase "cons l1 loc1"; S3Case "cons l2 loc2".
          prog_dos. inv H0.
          rewrite Pol_in_cons; split'.
          S4Case "left".
            red; simpl; simpl_vect. spec_lia.
          S4Case "right".
           eauto.
      End_of_assert INSAME. clear Heqo.
      match type of VALOK with
        | match ?X with
          | left _ => _
          | right _ => _ end = _ =>
          destruct X
      end;clean.
      revert EXLT l.
      induction' pols_lt as [|pol_lt pols_lt]; intros.
      SCase "nil".
        inv EXLT.
      SCase "cons pol_lt pols_lt".
        inv l.
        inv' EXLT; eauto.
        SSCase "Exists_cons_hd".
          clear' - EXGE H1 IN H0 INSAME.
          induction' pols_ge as [| pol_ge pols_ge]; clean.
          S3Case "nil".
            inv EXGE.
          S3Case "cons pol_ge pols_ge".
            inv H1. inv' EXGE; eauto.
            S4Case "Exists_cons_hd".
              apply (H3 (v1 +++ v2)).
              repeat (apply Pol_Included_intersertion); auto.
    Case "id1 <> id2".
      apply NEQ. unfold translate_locs' in EQ; simpl in EQ.
      congruence.
  Qed.

    
  




  Definition params_eq nbr_global_parameters dim1 dim2 :
    Polyhedron ((S(dim1 + nbr_global_parameters)) + (S (dim2 + nbr_global_parameters))) :=
    map (fun n =>
    {| constr_vect :=
      (0 ::: (V0 dim1 +++ Vnth_at_val nbr_global_parameters n 1)) +++
      (0 ::: (V0 dim2 +++ Vnth_at_val nbr_global_parameters n (-1)));
       constr_comp := EQ;
       constr_val := 0
      |}) (sequence_lesser nbr_global_parameters).

  Opaque plus. (* to avoid simplifications *)
  Opaque Zplus Zmult.
  Lemma params_eq_correct nbr_global_parameters dim1 dim2
    z1 (v1:ZVector dim1) (params1: ZVector nbr_global_parameters) z2
    (v2: ZVector dim2) (params2:  ZVector nbr_global_parameters):
    (z1 ::: (v1 +++ params1)) +++ (z2 ::: (v2 +++ params2)) 
        ∈ params_eq nbr_global_parameters dim1 dim2 <->
    params1 = params2.
  Proof.
    unfold params_eq.
    split'.
    Case "->".
      intros IN.
      apply Vnth_inj.
      intros. pattern x.
      eapply map_sequence_lesser_forall_1; eauto.
      unfold Pol_In in IN.
      remember_no_eq (sequence_lesser nbr_global_parameters) as l.
      clear' - IN. induction' l as [|n l]; simpl; auto.
      SCase "cons n l".
        inv IN. constructor; eauto. clear' - H1.
        red in H1. simpl in H1. simpl_vect in H1.
        repeat rewrite Vnth_at_val_prod in H1.
        simpl in H1. unfold ZNum.Numerical_Num in *.
        unfold Inhab_num in *. unfold Inhabited_Z in *. simpl in *. lia.
    Case "<-".
      intros; subst.
      unfold Pol_In.
      apply map_sequence_lesser_forall_2.
      intros. red. simpl. simpl_vect.
      repeat rewrite Vnth_at_val_prod. simpl. lia.
  Qed.


  Transparent plus Zplus Zmult.


  Definition validate_two_instrs {nbr_global_parameters}
    (pi1 pi2: Polyhedral_Instruction_DTS nbr_global_parameters):
      res unit:=
    let pols_lt := make_poly_lt pi1.(pi2_schedule1) pi2.(pi2_schedule1) [] in
    let pols_ge := make_poly_ge pi1.(pi2_schedule2) pi2.(pi2_schedule2) [] in
    let pol := params_eq nbr_global_parameters _ _ ∩
      (pi1.(pi2_poly_ext) ⊗ pi2.(pi2_poly_ext) )in
    (* check the two write locations *)
    do _ <- validate_one_loc pol pi1.(pi2_wloc) pi2.(pi2_wloc) pols_lt pols_ge;
    do _ <-
      mfold_left
        (fun (_:unit) rloc2 =>
          validate_one_loc pol pi1.(pi2_wloc) rloc2 pols_lt pols_ge)
        pi2.(pi2_rlocs) tt;
    mfold_left
      (fun (_:unit) rloc1 =>
        validate_one_loc pol rloc1 pi2.(pi2_wloc) pols_lt pols_ge)
      pi1.(pi2_rlocs) tt.

  (* this lemma seems terrible, and it is! Its hypothesis are
     obtained from a modified cut and past of the goal *)

  Lemma useful_for_the_next_one
    (nbr_global_parameters : nat)
    (pi1 : Polyhedral_Instruction_DTS nbr_global_parameters)
    (pi2 : Polyhedral_Instruction_DTS nbr_global_parameters)
    pi2_loc1 pi2_loc2
    loc1 loc2
    (Heq_do : validate_one_loc
             (params_eq nbr_global_parameters (pi2_depth pi1) (pi2_depth pi2)
              ∩ (pi2_poly_ext pi1 ⊗ pi2_poly_ext pi2)) 
             (pi2_loc1) (pi2_loc2)
             (make_poly_lt (pi2_schedule1 pi1) (pi2_schedule1 pi2) [])
             (make_poly_ge (pi2_schedule2 pi1) (pi2_schedule2 pi2) []) =
           OK ())
    (pi2_loc_eq1 : pi2_loc1 =
                  (fst loc1,
                  map
                    (fun v : ZVector (S (I.context_size pi1.(pi2_instr))) =>
                     Mprod_vect_right v (extend_matrix pi1.(pi2_transformation)))
                    (snd loc1)))
    (pi2_loc_eq2 : pi2_loc2 =
                  (fst loc2,
                  map
                    (fun v : ZVector (S (I.context_size pi2.(pi2_instr))) =>
                     Mprod_vect_right v (extend_matrix pi2.(pi2_transformation)))
                    (snd loc2)))
    (params : Global_Parameters nbr_global_parameters)
    (v1' : NVector (pi2_depth pi1))
    (INV1' : In v1' (bp_elts (pi2_poly pi1) params))
    (IN1 : In (1 ::: (v1' +++ params))
          (map (make_context_ext params) (bp_elts (pi2_poly pi1) params)))
    (v2' : NVector (pi2_depth pi2))
    (INV2' : In v2' (bp_elts (pi2_poly pi2) params))
    (IN2 : In (1 ::: (v2' +++ params))
          (map (make_context_ext params) (bp_elts (pi2_poly pi2) params)))
    (COMP1 : time_stamp_lt
            (apply_schedule (pi2_schedule1 pi1) (1 ::: (v1' +++ params)))
            (apply_schedule (pi2_schedule1 pi2) (1 ::: (v2' +++ params))))
    (COMP2 : time_stamp_le
            (apply_schedule (pi2_schedule2 pi2) (1 ::: (v2' +++ params)))
            (apply_schedule (pi2_schedule2 pi1) (1 ::: (v1' +++ params)))):
   translate_locs
     (extend_arguments (pi2_transformation pi1 × (1 ::: (v1' +++ params))))
     loc1 <>
   translate_locs
     (extend_arguments (pi2_transformation pi2 × (1 ::: (v2' +++ params))))
     loc2.
    Proof.
      intro.
      assert' (translate_locs' (1:::(v1' +++ params)) pi2_loc1 
             = translate_locs' (1:::(v2' +++ params)) pi2_loc2)
        as TRANS.
      SCase "Assert: TRANS".
        subst.
        clear' - H.
        unfold translate_locs, translate_locs' in *.
        inv H. f_equal.
        destruct pi1; destruct pi2; simpl in *. subst. auto.
        simpl.
        etransitivity. etransitivity; [|eexact H2].
        rewrite map_map.
        apply map_ext. intros. rewrite Mprod_vect_right_correct.
        rewrite extend_matrix_correct. reflexivity.
        rewrite map_map.
        apply map_ext. intros. rewrite Mprod_vect_right_correct.
        rewrite extend_matrix_correct. reflexivity.
      End_of_assert TRANS.
      clear H. revert TRANS. eapply validate_one_loc_OK; eauto.
      apply Pol_Included_intersertion.
      rewrite params_eq_correct. reflexivity.
      apply Pol_In_In_prod.
      rewrite pi2_poly_ext_eq.
      apply extend_polyhedron_correct_1.
      apply bp_in_elts_in_poly; auto.
      rewrite pi2_poly_ext_eq.
      apply extend_polyhedron_correct_1.
      apply bp_in_elts_in_poly; auto.
      
      apply make_poly_lt_correct.
      split. constructor.
      unfold apply_schedule in *. auto.

      apply make_poly_ge_correct.
      split. constructor.
      unfold apply_schedule in *. auto.
  Qed.




Opaque validate_one_loc.


  Lemma validate_two_instrs_ok nbr_global_parameters
    (pi1 pi2: Polyhedral_Instruction_DTS nbr_global_parameters):
    validate_two_instrs pi1 pi2 = OK tt ->
    forall params ip1 ip2,
      In ip1 (expand_poly_instr_DTS params pi1) ->
      In ip2 (expand_poly_instr_DTS params pi2) ->
      (compare_IP2TS_1 time_stamp_lt) ip1 ip2 ->
      (compare_IP2TS_2 time_stamp_le) ip2 ip1 ->
      ip2ts_permutable ip1 ip2.
  Proof.
    intros VALIDATE * IN1 IN2 COMP1 COMP2.
    unfold expand_poly_instr_DTS in *.
    apply list_in_map_inv in IN1.
    destruct IN1 as [v1 [? IN1]]. subst.
    apply list_in_map_inv in IN2.
    destruct IN2 as [v2 [? IN2]]. subst.
    unfold compare_IP2TS_1, compare_IP2TS_2 in *. simpl in *.
    unfold validate_two_instrs in VALIDATE.
    prog_dos. destruct x; destruct x0.
    assert' (exists v1', (v1 = 1 ::: (v1' +++ params) /\
         In v1' (bp_elts (pi2_poly pi1) params))) as V1EQ.
    Case "Assert: V1EQ".
      clear' - IN1.
      apply list_in_map_inv in IN1. destruct IN1 as [? [? ?]].
      subst. unfold make_context_ext. eexists. eauto.
    End_of_assert V1EQ. destruct V1EQ as [v1' [? INV1']]; subst.
    assert' (exists v2', (v2 = 1 ::: (v2' +++ params) /\
      In v2' (bp_elts (pi2_poly pi2) params))) as V2EQ.
    Case "Assert: V2EQ".
      clear' - IN2.
      apply list_in_map_inv in IN2. destruct IN2 as [? [? ?]].
      subst. unfold make_context_ext. eexists. eauto.
    End_of_assert V2EQ. destruct V2EQ as [v2' [? INV2']]; subst.
    apply different_access_permutable; simpl.
    Case "writes".
      eapply useful_for_the_next_one; eauto.
      apply pi2_wloc_eq. apply pi2_wloc_eq.
    Case "Write1 Read2".
      clear Heq_do VALIDATE.
      rewrite pi2_rlocs_eq in *. rewrite pi2_wloc_eq in *.
      remember_no_eq (I.read_locs (pi2_instr pi2)) as rlocs.
      induction' rlocs as [| rloc rlocs].
      SCase "nil".
        constructor.
      SCase "cons rloc rlocs".
        simpl in Heq_do0.
        Tactic Notation "prog_do" "in" hyp(H) :=
          match type of H with
            | ?TERM => find_do_and_prog TERM; simpl_do in H
          end; try solve [inv H].
        prog_do in Heq_do0. destruct a'.
        
        constructor.
        SSCase "1".
          apply not_eq_sym.
          eapply useful_for_the_next_one; eauto.
        SSCase "2".
          apply IHrlocs. apply Heq_do0.
    Case "Write2 Read1".
      clear Heq_do Heq_do0.
      rewrite pi2_rlocs_eq in *. rewrite pi2_wloc_eq in *.
      remember_no_eq (I.read_locs (pi2_instr pi1)) as rlocs.
      induction' rlocs as [| rloc rlocs].
      SCase "nil".
        constructor.
      SCase "cons rloc rlocs".
        simpl in VALIDATE.
        prog_do in VALIDATE. destruct a'.
        
        constructor.
        SSCase "1".
          eapply useful_for_the_next_one; eauto.
        SSCase "2".
          apply IHrlocs. assumption.
  Qed.

  Fixpoint validate_lst_instrs {nbr_global_parameters}
    (lpi: list (Polyhedral_Instruction_DTS nbr_global_parameters)):
    res unit:=
    match lpi with
    | [] => OK ()
    | pi :: lip' =>
      do _ <- validate_two_instrs pi pi;
      do _ <- mfold_left (fun (_:unit) pi' =>
        do _ <- validate_two_instrs pi pi';
        validate_two_instrs pi' pi) lip' tt;
      validate_lst_instrs lip'
    end.

  Fixpoint change_schedule_aux {nbr_global_parameters}
    (lpi: list (Polyhedral_Instruction nbr_global_parameters))
    (lsched: list (list (list Z))):
    res (list (Polyhedral_Instruction_DTS nbr_global_parameters)):=
    match lpi, lsched with
    | [], [] => OK []
    | _ :: _ , [] => Err "Not enough new schedules"
    | [], _ :: _ => Err "To many new schedules"
    | pi :: lpi', psched :: lsched' =>
    match mmap (make_vector (S (pi.(pi_depth) + nbr_global_parameters))) psched with
    | None => Err "A schedule does not have the right dimension"
    | Some sched =>
    do  l <- change_schedule_aux lpi' lsched';
    OK(
      let ext_transf := (extend_matrix pi.(pi_transformation)) in
      {| pi2_instr := pi.(pi_instr);
         pi2_depth := pi.(pi_depth);
         pi2_poly := pi.(pi_poly);
         pi2_poly_ext := extend_polyhedron (pi.(pi_poly).(bp_poly));
         pi2_poly_ext_eq := eq_refl;
         pi2_schedule1 := pi.(pi_schedule);
         pi2_schedule2 := sched;
         pi2_transformation := pi.(pi_transformation);
         pi2_wloc :=
           (fst (I.write_loc pi.(pi_instr)),
             map (fun v => Mprod_vect_right v ext_transf)
             (snd (I.write_loc pi.(pi_instr))));
         pi2_wloc_eq := eq_refl;
         pi2_rlocs :=
           map (fun loc =>
             (fst loc,
               map (fun v => Mprod_vect_right v ext_transf)
               (snd loc))) (I.read_locs pi.(pi_instr));
         pi2_rlocs_eq := eq_refl|} :: l)
    end
    end.


  Definition change_schedule
    (prog : Poly_Program)
    (lsched: list (list (list Z))):
    res Poly_Program :=
    do pi2l <- change_schedule_aux prog.(pp_poly_instrs) lsched;
    do _ <- validate_lst_instrs pi2l;
    OK
      {| pp_nbr_global_parameters := prog.(pp_nbr_global_parameters);
         pp_poly_instrs := 
           map
             (fun pi2 =>
               {| pi_instr := pi2.(pi2_instr);
                  pi_depth := pi2.(pi2_depth);
                  pi_poly := pi2.(pi2_poly);
                  pi_schedule := pi2.(pi2_schedule2);
                  pi_transformation := pi2.(pi2_transformation)|})
             pi2l|}.



  Definition ip2ts_list_semantics2 lip2 :=
    instruction_list_semantics (map ip_of_ip2ts_2 lip2).

  Lemma ip2ts_list_semantics2_equiv: forall lip2 mem1 mem2,
    ip2ts_list_semantics lip2 mem1 mem2 <->
    ip2ts_list_semantics2 lip2 mem1 mem2.
  Proof.
    unfold ip2ts_list_semantics2, ip2ts_list_semantics.
    induction lip2 as [|ip2 lip2]; intros; split; intro H; inv H; simpl;
      try constructor.
    destruct ip2; unfold ip_of_ip2ts_2, ip_of_ip2ts_1 in *;
      simpl in *; inv H2; econstructor; [econstructor|]; eauto. apply IHlip2; auto.
    destruct ip2; unfold ip_of_ip2ts_2, ip_of_ip2ts_1 in *;
      simpl in *; inv H2; econstructor; [econstructor|]; eauto. 
    apply IHlip2. auto.
  Qed.

  Require Import Structures.Orders.
  

  Module IP2Order <: TotalLeBool.
    Definition t := Instruction_Point_DTS.

    Definition leb (x y :t) : bool :=
      time_stamp_le_dec x.(ip2_time_stamp2) y.(ip2_time_stamp2).

    Lemma leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
    Proof.
      unfold t, leb.
      intros a1 a2; destruct a1; destruct a2; simpl; clear.
      match goal with
        | |- proj_sumbool ?X = _ \/ proj_sumbool ?Y = _ =>
          destruct X; destruct Y; auto
      end.
      exfalso.
      unfold not, time_stamp_le in *.
      destruct (time_stamp_lt_trichotomy ip2_time_stamp4 ip2_time_stamp6) as [[|]|];
        auto.
    Qed.
  End IP2Order.
  Require Import Mergesort.
  Module IP2Sort := Sort(IP2Order).

  Lemma sort_compare2_sorted lip:
    Sorted (compare_IP2TS_2 time_stamp_le) (IP2Sort.sort lip).
  Proof.
    pose proof (IP2Sort.LocallySorted_sort lip).
    remember_no_eq (IP2Sort.sort lip) as lip'. clear lip.
    induction' lip' as [|ip lip].
    Case "nil".
      constructor.
      inv H.
      constructor; auto.
      clear' - H3.
      inv' H3.
      SCase "HdRel_nil".
        constructor.
      SCase "HdRel_cons".
        constructor.
        unfold compare_IP2TS_2.
        unfold is_true in H.
        destruct (time_stamp_le_dec ip.(ip2_time_stamp2) b.(ip2_time_stamp2)); clean.
  Qed.


  Unset Implicit Arguments.

  Theorem validate_lst_instrs_OK nbr_global_parameters
    (lpi2: list (Polyhedral_Instruction_DTS nbr_global_parameters)):
    validate_lst_instrs lpi2 = OK () ->
    forall params lip2,
    flatten (map (expand_poly_instr_DTS params) lpi2) = lip2 ->
    forall mem1 mem2 lip2_sorted1,
    Permutation lip2 lip2_sorted1 ->
    Sorted (compare_IP2TS_1 time_stamp_lt) lip2_sorted1 ->
    ip2ts_list_semantics lip2_sorted1 mem1 mem2 ->
    (exists lip2_sorted2 mem2',
      (Permutation lip2 lip2_sorted2 /\
      Sorted (compare_IP2TS_2 time_stamp_le) lip2_sorted2 /\
      ip2ts_list_semantics2 lip2_sorted2 mem1 mem2'))/\
    (forall lip2_sorted2 mem2',
      Permutation lip2 lip2_sorted2 ->
      Sorted (compare_IP2TS_2 time_stamp_le) lip2_sorted2 ->
      ip2ts_list_semantics2 lip2_sorted2 mem1 mem2' ->
      mem2 ≡ mem2').
  Proof.
    intros VALIDATE * FLATTEN * PERMUT SORTED1 SEM1.
    assert' (forall ip1 ip2,
      In ip1 lip2 ->
      In ip2 lip2 ->
      (compare_IP2TS_1 time_stamp_lt) ip1 ip2 ->
      (compare_IP2TS_2 time_stamp_le) ip2 ip1 ->
      ip2ts_permutable ip1 ip2) as PERMUTABLE.
    Case "Assert: PERMUTABLE".
      subst. clear' - VALIDATE.
      intros. induction' lpi2 as [|pi lpi2]; simpl in *; clean.
      SCase "cons pi lpi2".
        prog_dos. destruct x; destruct x0.
        apply in_app_or in H. apply in_app_or in H0.
        destruct' H; destruct' H0; auto.
        SSCase "In ip1 (expand_poly_instr_DTS params pi)";
          S3Case "In ip2 (expand_poly_instr_DTS params pi)". 
        eapply validate_two_instrs_ok; eauto.
        SSCase "In ip1 (expand_poly_instr_DTS params pi)";
          S3Case "In ip2 (flatten (map (expand_poly_instr_DTS params) lpi2))".
          clear' - Heq_do0 H H0 H1 H2.
          induction' lpi2 as [|pi' lpi2]; simpl in *; clean.
          S4Case "cons pi' lpi2".
          prog_dos. destruct a'; destruct x.
          apply in_app_or in H0. destruct' H0; auto.
          S5Case "In ip2 (expand_poly_instr_DTS params pi')".
            clear Heq_do.
            eapply validate_two_instrs_ok; eauto.
        SSCase "In ip1 (flatten (map (expand_poly_instr_DTS params) lpi2))";
          S3Case "In ip2 (expand_poly_instr_DTS params pi)". 
          clear' - Heq_do0 H H0 H1 H2.
          induction' lpi2 as [|pi' lpi2]; simpl in *; clean.
          S4Case "cons pi' lpi2".
          prog_dos. destruct a'; destruct x.
          apply in_app_or in H. destruct' H; auto.
          S5Case "In ip1 (expand_poly_instr_DTS params pi')".
            clear Heq_do1.
            eapply validate_two_instrs_ok; eauto.
    End_of_assert PERMUTABLE.
    split'.
    Case "left".
      exists (IP2Sort.sort lip2).
     pose proof (sort_compare2_sorted lip2) as SORTED2.
     pose proof (IP2Sort.Permuted_sort lip2) as PERMUT2.
     remember_no_eq (IP2Sort.sort lip2) as lip2_sorted2.
     edestruct (two_sorted_same_semantics lip2_sorted1 lip2_sorted2) as [mem2' [? ?]];
       eauto.
     transitivity lip2; auto. symmetry; auto.
     intros. apply PERMUTABLE; auto.
     symmetry in PERMUT.
     eapply Permutation_in; eauto.
     symmetry in PERMUT2.
     eapply Permutation_in; eauto.
     reflexivity.
     exists mem2'; auto; repeat split; auto.
     rewrite <- ip2ts_list_semantics2_equiv. auto.
   Case "right".
     intros.
     edestruct (two_sorted_same_semantics lip2_sorted1 lip2_sorted2) as [mem3 [? ?]];
       eauto.
     transitivity lip2; auto. symmetry; auto.
     intros. apply PERMUTABLE; auto.
     symmetry in PERMUT.
     eapply Permutation_in; eauto.
     symmetry in H.
     eapply Permutation_in; eauto.
     reflexivity.
     assert (mem2' = mem3);[|subst; symmetry; assumption].
     rewrite <- ip2ts_list_semantics2_equiv in H1.
     clear' - H1 H3. unfold ip2ts_list_semantics in *.
     remember_no_eq (map ip_of_ip2ts_1 lip2_sorted2) as lip2.
     revert dependent mem1.
     induction lip2; intros * SEM1 SEM2;
       inv SEM1; inv SEM2; eauto.
     eapply IHlip2; eauto.
     assert (mem2 = mem4); [|subst; auto].
     clear' - H1 H2.
     inv H1; inv H2; clean.
     assert (rvals = rvals0) by congruence. subst.
     assert (wval = wval0).
     eapply I.semantics_deterministic; eauto. subst.
     congruence.
  Qed.
     
    
  Lemma Permutation_map_exists A B (f : A -> B) la lb:
    Permutation (map f la) lb ->
    exists la',
      lb = map f la' /\
      Permutation la la'.
  Proof.
    intro PERM.
    dependent induction PERM; destruct la; simpl in *; clean.
    exists (@nil A). split; auto.

    inv x. edestruct IHPERM as [la' [? ?]]; eauto.
    subst.
    exists (a::la'); split; auto.

    inv x. destruct la; clean. simpl in H1. inv H1.
    exists (a0 :: a :: la); split; auto.
    apply perm_swap.

    specialize (IHPERM1 A f (a :: la) eq_refl).
    destruct IHPERM1 as [la1 [? ?]].
    subst.
    specialize (IHPERM2 A f la1 eq_refl).
    destruct IHPERM2 as [la2 [? ?]]. subst.
    exists la2; split; auto.
    transitivity la1; auto.
  Qed.
    
  Inductive __no_subst__ (H: Prop) : Prop :=
    __NO_SUBST__: forall (h:H), __no_subst__ H.

  Theorem change_schedule_OK prog tprog lsched :
    change_schedule prog lsched = OK tprog ->
    forall params,
    forall mem1 mem2,
      poly_program_semantics_param instruction_point_lt prog params mem1 mem2 ->
      (exists mem2', poly_program_semantics tprog params mem1 mem2') /\
      (forall mem2', poly_program_semantics tprog params mem1 mem2' -> mem2 ≡ mem2').
  Proof.
    intros CHANGE * SEM1.
    unfold change_schedule in CHANGE.
    prog_dos. destruct x. destruct prog; simpl in *. 
    inv SEM1. simpl in *.
    remember (flatten (map (expand_poly_instr_DTS Vparams) pi2l)) as lip2.
    assert' (flatten (map (expand_poly_instr Vparams) pp_poly_instrs0) =
      map ip_of_ip2ts_1 lip2) as FLATTEN1.
    Case "Assert: FLATTEN1".
      subst. clear' - Heq_do.
      revert dependent pi2l. revert lsched.
      induction pp_poly_instrs0 as [|pi instrs]; intros; destruct lsched as [|sched lsched];
        simpl in *; clean.
      match goal with
        |H: match ?X with Some _ => _ | None  => _ end = _ |- _ =>
          destruct X
      end; clean. prog_dos. simpl in *.
      rewrite map_app. f_equal; eauto.
      clear'.
      unfold expand_poly_instr_DTS, expand_poly_instr. simpl.
      repeat rewrite map_map.  apply map_ext. intros. reflexivity.
    End_of_assert FLATTEN1.
    rewrite FLATTEN1 in *.
    apply Permutation_map_exists in H1.
    destruct H1 as [lip2_sorted1 [? PERMUT]].
    symmetry in Heqlip2.
    edestruct (validate_lst_instrs_OK _ pi2l Heq_do0 Vparams _ Heqlip2 mem1 mem2); eauto.

    SCase "Sorted".
    clear' - H1 H0.
    subst.
    induction' lip2_sorted1 as [|ip1 lip2_sorted1]; auto.
      SSCase "cons ip1 lip2_sorted1".
        inv H0; econstructor; eauto.
        destruct lip2_sorted1; auto.
        simpl in H3. inv H3; auto.
    SCase "semantics".
      unfold ip2ts_list_semantics. subst. auto.
    SCase "main goal".
    split'.
    SSCase "left".
      destruct H3 as [lip2_sorted2 [mem2' [PERM2 [SORTED2 SEM2]]]].
      assert' (Sorted instruction_point_le (map ip_of_ip2ts_2 lip2_sorted2)) as SORTED2'.
      S3Case "Assert: SORTED2'".
        clear' - SORTED2.
        induction lip2_sorted2; inv SORTED2; simpl in *; auto.
        constructor; auto. inv H2; simpl; auto.
      End_of_assert SORTED2'.
      exists mem2'.
      econstructor; simpl; try eassumption.
      subst.
      match goal with
        |H : Permutation ?L1 ?L2 |-
          Permutation ?L3 (map ?f ?L2) =>
          replace L3 with (map f L1)
      end. apply Permutation_map. assumption.
      clear' - Heq_do.
      revert dependent pi2l. revert lsched.
      induction pp_poly_instrs0 as [|pi instrs]; intros; destruct lsched as [|sched lsched];
        simpl in *; clean.
      SSCase "left".
      match goal with
        |H: match ?X with Some _ => _ | None  => _ end = _ |- _ =>
          destruct X
      end; clean. prog_dos. simpl in *.
      rewrite map_app. f_equal; eauto.
      clear'.
      unfold expand_poly_instr_DTS, expand_poly_instr. simpl.
      rewrite map_map. apply map_ext. intros. reflexivity.
    SSCase "right".
      intros.
      inv H5. simpl in *.
      assert (Vparams0 = Vparams) by congruence. subst. clear H6 H.
      match type of H8 with
        | Permutation ?L _ =>
          assert'
          (L =
            map ip_of_ip2ts_2 (flatten (map (expand_poly_instr_DTS Vparams) pi2l)))
          as FLATTEN2
      end.
      S3Case "Assert: FLATTEN2".
        subst. clear' - Heq_do.
        revert dependent pi2l. revert lsched.
        induction pp_poly_instrs0 as [|pi instrs]; intros; destruct lsched as [|sched lsched];
          simpl in *; clean.
        match goal with
          |H: match ?X with Some _ => _ | None  => _ end = _ |- _ =>
            destruct X
        end; clean. prog_dos. simpl in *.
        rewrite map_app. f_equal; eauto.
        clear'.
        unfold expand_poly_instr_DTS, expand_poly_instr. simpl.
        repeat rewrite map_map.  apply map_ext. intros. reflexivity.
      End_of_assert FLATTEN2.
      rewrite FLATTEN2 in *. clear FLATTEN2.
      apply Permutation_map_exists in H8.
      destruct H8 as [lip2_sorted2 [? PERM2]]. subst.
      eapply H4; eauto.
      clear' - H7.
      induction lip2_sorted2; auto; inv H7; constructor; auto.
      inv H2; destruct lip2_sorted2; clean. simpl in H.
      inv H. constructor. auto.
   Qed.



End Permut.


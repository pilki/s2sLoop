(* The polyhedral language *)
Add LoadPath "../from_compcert".
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

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
Require Import TimeStamp.
Open Scope string_scope.
(*Set Implicit Arguments.*)
Open Scope nat_scope.

Hint Resolve Zgt_lt.


Lemma app_in_poly_in_elts: forall nbr_global_parameters depth (bp: Boxed_Polyhedron nbr_global_parameters depth)
  (vect: ZVector depth) (params: ZVector nbr_global_parameters),
  (vect +++ params) ∈ (bp.(bp_poly)) ->
  In vect (bp.(bp_elts) params).
Proof.
  intros * IN.
  replace vect with (Vtake_p depth (vect +++ params)).
  apply bp_in_poly_in_elts.
  apply in_pol_in_constrain_params. assumption.

  apply Vtake_p_app.
Qed.

Open Scope Z_scope.


(* semantics of Polyhedrics programs *)

Module PSemantics (Import M:BASEMEM(ZNum))
  (I:INSTRS(ZNum) with Definition Value := M.Value).
  Module T := Tools(ZNum).
  Import T.


  (* a polyhedral instruction *)

  (* This definition has several flaws that might be fairly
     problematic. It has too many things in Prop:

   * The link between the instruction and its ident. But this is easy
     to check at runtime

   * The boxed polyhedron can be fairly more problematic. It should be
     "easy" to build it when extracting the polyhedral model from a
     Loop one, but definitely less trivial one doing it from a
     polyhedral representation out of the optimizer. I hope that the
     solution will be to update the extracted one, first by adding
     dimensions, then by changing the adapter/schedule. I don't know
     yet how to do so for the code generation.

     *)

  Record Polyhedral_Instruction
    (nbr_global_parameters:nat):=
    { (** the instruction *)
      pi_instr: I.Instruction;
      (** the depth of the instruction in the program *)
      pi_depth: nat;
      (** the Polyhedron *)
      pi_poly: Boxed_Polyhedron nbr_global_parameters pi_depth;
      (** the schedule of the instruction *)
      pi_schedule:
        list (ZVector (S (pi_depth + nbr_global_parameters)));
      (** transformation to move from elements of the polyhedron to the
         arguments of the instruction*)
      pi_transformation:
        ZMatrix (I.context_size pi_instr) (S (pi_depth + nbr_global_parameters))
    }.

  Implicit Arguments pi_instr [[nbr_global_parameters]].
  Implicit Arguments pi_depth [[nbr_global_parameters]].
  Implicit Arguments pi_poly [[nbr_global_parameters]].
  Implicit Arguments pi_schedule [[nbr_global_parameters]].
  Implicit Arguments pi_transformation [[nbr_global_parameters]].



  Record Poly_Program :=
    { pp_nbr_global_parameters: nat;
      pp_poly_instrs:
        list (Polyhedral_Instruction pp_nbr_global_parameters)}.


  (* definition of the semantics *)

  (* one instance of an instruction, in one point of the Polyhedron *)

  Record Instruction_Point := {
    ip_instruction : I.Instruction;
    ip_arguments: Arguments (I.context_size ip_instruction);
    ip_time_stamp: Time_Stamp
  }.

  Definition instruction_point_lt ip1 ip2 : Prop :=
    time_stamp_lt ip1.(ip_time_stamp) ip2.(ip_time_stamp).

  Definition instruction_point_le ip1 ip2 : Prop :=
    time_stamp_le ip1.(ip_time_stamp) ip2.(ip_time_stamp).


  Instance instruction_point_lt_transitive: Transitive instruction_point_lt.
  Proof.
    unfold Transitive, instruction_point_lt. etransitivity; eauto.
  Qed.

  Instance instruction_point_le_transitive: Transitive instruction_point_le.
  Proof.
    unfold Transitive, instruction_point_le. etransitivity; eauto.
  Qed.


  Inductive instruction_point_semantics (ip: Instruction_Point) 
    (mem1 mem2: Memory): Prop :=
  | ip_sem_intro: 
    forall rlocs rvals wval wloc ectxt,
      extend_arguments ip.(ip_arguments) = ectxt ->
  (* we translate the read locations and access them*)
      map (translate_locs ectxt) (I.read_locs ip.(ip_instruction)) = rlocs->
      mmap (M.read mem1) rlocs = Some rvals ->

  (* the semantics gives us a value to write back *)
      I.semantics ip.(ip_instruction) ip.(ip_arguments) rvals wval ->

  (* we write it to the write location *)
      translate_locs ectxt (I.write_loc ip.(ip_instruction)) = wloc->
      M.write mem1 wloc wval = Some mem2 ->
      instruction_point_semantics ip mem1 mem2.
  
  Inductive instruction_list_semantics: list Instruction_Point ->
    Memory -> Memory -> Prop:=
  | ILS_nil: forall mem, instruction_list_semantics [] mem mem
  | ILS_cons: forall mem1 mem2 mem3 ip il,
    instruction_point_semantics ip mem1 mem2 ->
    instruction_list_semantics il mem2 mem3 ->
    instruction_list_semantics (ip::il) mem1 mem3.

  (* get the timestamp from an environement and a schedule *)
  Definition apply_schedule {global_depth}
    (schedule: list (ZVector (S global_depth)))
      (ectxt: Context_ext global_depth)
    : Time_Stamp :=
    map (fun v' => 〈v', ectxt〉) schedule.


  Definition make_context_ext {depth nbr_global_parameters}
    (global_params: Global_Parameters nbr_global_parameters)
    (iters:Iterators depth): Context_ext (depth + nbr_global_parameters) :=
    1 ::: (iters +++ global_params).

  (* all the instruction point of one polyhedric instruction *)

  Definition expand_poly_instr { nbr_global_parameters}
    (params: Global_Parameters nbr_global_parameters)
    (pi: Polyhedral_Instruction nbr_global_parameters)
    : list Instruction_Point:=
    (** build the list of contexts *)
    let ectxts := map (make_context_ext params) (pi.(pi_poly).(bp_elts) params) in
    (** build one instruction point from each environement *)
    map (fun ectxt =>
      {| ip_instruction := pi.(pi_instr);
         ip_arguments := pi.(pi_transformation) × ectxt;
         ip_time_stamp := apply_schedule pi.(pi_schedule) ectxt|})
      ectxts.

  Inductive poly_program_semantics_param
    (ip_order: Instruction_Point ->Instruction_Point -> Prop)
    (prog: Poly_Program)
    (params: list Z) (mem1 mem2 : Memory):Prop :=
  | PPS_intro: forall sorted_instruction_points
    (Vparams: ZVector prog.(pp_nbr_global_parameters)),
    make_vector _ params = Some Vparams ->
    (** sorted_instruction_points is the set of instruction points, 
       flattened and sorted*)
    Sorted ip_order sorted_instruction_points ->
    Permutation (flatten (map (expand_poly_instr Vparams) prog.(pp_poly_instrs)))
      sorted_instruction_points ->
    (** each instruction point is executed in order *)
    instruction_list_semantics sorted_instruction_points mem1 mem2 ->
    poly_program_semantics_param ip_order prog params mem1 mem2.

  Definition poly_program_semantics :=
    poly_program_semantics_param instruction_point_le.
    


  (* LIB *)
  Tactic Notation "replace'" hyp(H) "with" constr(H') "by" tactic(t) :=
    replace H with H' in * by t; clear H.

  Lemma instruction_point_semantics_deterministic:
    forall ip mem1 mem2 mem2',
      instruction_point_semantics ip mem1 mem2 ->
      instruction_point_semantics ip mem1 mem2' ->
      mem2 = mem2'.
  Proof.
    intros * IP IP'.
    inv IP. inv IP'. 
    replace' rvals0 with rvals by congruence.
    replace' wval0 with wval by (eapply I.semantics_deterministic; eauto).
    congruence.
  Qed.



  Lemma instruction_list_semantics_deterministic:
    forall lst mem1 mem2 mem2',
      instruction_list_semantics lst mem1 mem2 ->
      instruction_list_semantics lst mem1 mem2' ->
      mem2 = mem2'.
  Proof.
    intros * ILS.
    induction' ILS; intros ILS'; inv ILS'; auto.
    Case "ILS_cons".
      replace' mem4 with mem2
        by (eapply instruction_point_semantics_deterministic; eauto).
      eauto.
  Qed.


  Lemma instruction_point_lt_sorted_eq: forall l1,
    StronglySorted instruction_point_lt l1 ->
    forall l2,
    StronglySorted instruction_point_lt l2 ->
    Permutation l1 l2 ->
    l1 = l2.
  Proof.
    intros l1 SORTED1.
    induction' SORTED1.
    Case "SSorted_nil".
      intros. symmetry. apply Permutation_nil; auto.
    Case "SSorted_cons".
      intros * SORTED2 PERMUT.
      inv SORTED2.
      SCase "SSorted_nil".
        symmetry in PERMUT.
        apply Permutation_nil in PERMUT. inv PERMUT.
      SCase "SSorted_cons".
        rewrite Forall_forall in *.
        assert (a = a0).
        SSCase "a = a0".
          assert (In a (a0 :: l0)) by
            (eapply Permutation_in; eauto; simpl; eauto).
          simpl in H2.
          destruct H2; [subst; reflexivity|].
          specialize (H1 _ H2).
          assert (In a0 (a :: l)) by
            (symmetry in PERMUT; eapply Permutation_in; eauto; simpl; eauto).
          simpl in H3.
          destruct H3; [subst; reflexivity|].
          specialize (H _ H3).
          clear - H H1.
          elimtype False.
          unfold instruction_point_lt in *.
          eapply time_stamp_lt_antisymmectric; eauto.

        SSCase "l = l0".
          subst.
          f_equal.
          eapply IHSORTED1; eauto.
          eapply Permutation_cons_inv; eauto.
  Qed.

  Theorem poly_program_semantics_lt_deterministic: forall prog params mem1 mem2 mem2',
    poly_program_semantics_param instruction_point_lt prog params mem1 mem2 ->
    poly_program_semantics_param instruction_point_lt prog params mem1 mem2' ->
    mem2 = mem2'.
  Proof.
    intros * PPS PPS'.
    inv PPS; inv PPS'.
    assert (Vparams = Vparams0) by congruence. subst. clear dependent params.
    replace sorted_instruction_points with sorted_instruction_points0 in*.
    eapply instruction_list_semantics_deterministic; eauto.

    assert (Permutation sorted_instruction_points sorted_instruction_points0).
      eapply transitivity. symmetry. eauto. eauto.
    symmetry in H.
    apply instruction_point_lt_sorted_eq; auto;
    apply Sorted_StronglySorted; eauto;
    unfold Relations_1.Transitive; intros; etransitivity; eauto.
  Qed.

End PSemantics.

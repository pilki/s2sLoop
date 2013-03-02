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
Require Import Instructions.
Require Import Bounds.
Open Scope Z_scope.
Set Implicit Arguments.


(* The big step semantics of the Loops language *)
Module Semantics (N:NUMERICAL) (M:BASEMEM(N))
  (Import I:INSTRS(N) with Definition Value := M.Value).

  Import N. Import M.
  Module T := Tools(N).
  Import T.

  Existing Instance Numerical_Num.
  Open Scope numerical_scope.
(*  Local Notation "'context_size'" := I.context_size.*)

  (* global depth is the sum of the number of global arguments plus
     the depth in the loop nest. The idea of unifying both is that
     when doing the extraction toward the polyhedral model, we
     consider momentarily the outer indexes as global parameters *)

  (* [statement n] is a loop statement of depth n (counting the
     parameters of the program, but not the constant 1). I know I am
     going to regret the use of dependent type, but I don't really
     know how to to it in a better way.*)

  Unset Elimination Schemes.

  Inductive statement (global_depth: nat) : Type:=
  (* a loop goes from the lower_bound to the upper_bound, by step of 1 *)

  | Loop :
    forall
      (lower_bound: bound global_depth)
      (upper_bound: bound global_depth)
      (body: (statement_list (S global_depth))),
    statement global_depth

  (* we don't use the regular polymorphic version for statement_list
     because we need induction principles and mutually recursive
     programs and it's easier that way *)

  (* an instruction does not contain the actual "instr" but a label
     pointing to it. The reason is that some instructions are
     "duplicated" and we need to recognize them easily for the
     validation part.

     The list of vectors is the transformation to apply to obtain the
     arguments of the instruction from its context.
     *)

  | Instr: forall instr, NMatrix (context_size instr) (S global_depth) ->
    statement global_depth
  with
  statement_list (global_depth: nat) : Type :=
  | stl_nil: statement_list global_depth
  | stl_cons: forall (stmt:statement global_depth)
    (lst_stmt:statement_list global_depth),
    statement_list global_depth.

  Scheme statement_rect := Induction for statement Sort Type
  with statement_list_rect := Induction for statement_list Sort Type.

  Scheme statement_rec := Induction for statement Sort Set
  with statement_list_rec := Induction for statement_list Sort Set.

  Scheme statement_ind := Induction for statement Sort Prop
  with statement_list_ind := Induction for statement_list Sort Prop.

  Combined Scheme statement_multi_ind from statement_ind, statement_list_ind.
  Implicit Arguments Instr [[global_depth]].
  Implicit Arguments stl_nil [[global_depth]].
  Implicit Arguments stl_cons [[global_depth]].

  (* a program depends on a number of parameters. *)
  Record Program : Type := mkProgram  {
    prog_nbr_global_parameters: nat;
    (* the body of the program is a list of loops *)
    prog_main:statement_list prog_nbr_global_parameters
  }.

  (* big step of loops statements and programs *)

  Unset Elimination Schemes.

  Inductive semantics_statement: forall {global_depth: nat}
    (ctxt: Context global_depth),
    statement global_depth -> Memory -> Memory -> Prop :=
  | sem_instr:
    forall (global_depth: nat) (ctxt:Context global_depth)
      (instr: I.Instruction) (transf: NMatrix _ _)
      (ectxt: Context_ext global_depth)
      (args: Arguments (context_size instr))
      (eargs: Arguments_ext (context_size instr))
      rlocs rvals wloc wval mem1 mem2,

  (* context of the instruction *)
      (extend_context ctxt) = ectxt ->
      transf × ectxt = args ->
      (extend_arguments args) = eargs ->

  (* we translate the read locations and access them*)
      map (translate_locs eargs) (I.read_locs instr) = rlocs->
  (* all locations must be readable *)
      mmap (M.read mem1) rlocs = Some rvals ->

  (* the semantics gives us a value to write back *)
      I.semantics instr args rvals wval ->

  (* we write it to the write location *)
      translate_locs eargs (I.write_loc instr) = wloc->
      M.write mem1 wloc wval = Some mem2 ->

      semantics_statement ctxt (Instr instr transf) mem1 mem2

  | sem_loop:
    forall global_depth (ctxt: Context global_depth)
      (upper_bound lower_bound: bound global_depth)
      stmts ub lb mem1 mem2,
      eval_upper_bound ctxt upper_bound = Some ub ->
      eval_lower_bound ctxt lower_bound = Some lb ->
      semantics_loop ctxt lb ub stmts mem1 mem2 ->
      semantics_statement ctxt (Loop lower_bound upper_bound stmts) mem1 mem2

  with semantics_loop : forall {global_depth: nat} (ctxt:Context global_depth)
    (lower_bound upper_bound: Num),
    statement_list (S global_depth) -> Memory -> Memory -> Prop :=
  | sem_loop_no_more:
    forall global_depth (ctxt: Context global_depth)
      (lower_bound upper_bound: Num) stmt_lst m,
      lower_bound > upper_bound ->
      semantics_loop ctxt lower_bound upper_bound stmt_lst m m
  | sem_loop_step:
    forall global_depth (ctxt: Context global_depth) (lb ub: Num)
      stmt_lst mem1 mem2 mem3,
      lb <= ub ->
      (* execution of the body of the loop*)
      semantics_statement_list (lb ::: ctxt: Context (S global_depth)) stmt_lst mem1 mem2 ->
      (* incrementation of the iterator, and back to the loop *)
      semantics_loop ctxt (lb + 1) ub stmt_lst mem2 mem3 ->
      semantics_loop ctxt lb ub stmt_lst mem1 mem3

  with semantics_statement_list: forall  {global_depth: nat} (iters: Context global_depth),
    statement_list global_depth -> Memory -> Memory -> Prop :=
  | sem_stl_nil: forall global_depth (ctxt: Context global_depth) mem,
    semantics_statement_list ctxt stl_nil mem mem
  | sem_stl_cons: forall global_depth (ctxt: Context global_depth)
    mem1 mem2 mem3 stmt stmt_lst,
    semantics_statement ctxt stmt mem1 mem2 ->
    semantics_statement_list ctxt stmt_lst mem2 mem3 ->
    semantics_statement_list ctxt (stl_cons stmt stmt_lst) mem1 mem3
    .

  Scheme semantics_statement_ind := Induction for semantics_statement Sort Prop
  with semantics_loop_ind := Induction for semantics_loop Sort Prop
  with semantics_statement_list_ind := Induction for semantics_statement_list Sort Prop.

  Combined Scheme semantics_ind from semantics_statement_ind, semantics_loop_ind,
    semantics_statement_list_ind.

  Set Elimination Schemes.

  Program Definition Vnil {A:Type} : Vector A 0 := [].

  Ltac clean_somes :=
    clean no auto;
    repeat
    match goal with
      | H1: ?EXPR = Some ?var1
      , H2: ?EXPR = Some ?var2 |- _ =>
        assert (var1 = var2) by congruence;
          subst; clear H1 H2
    end.

  Lemma semantics_deterministic:
    (forall (global_depth: nat) (ctxt: Context global_depth) 
      (stmt: statement global_depth) mem mem1,
    semantics_statement ctxt stmt mem mem1 ->
    forall mem2, semantics_statement ctxt stmt mem mem2 ->
    mem1 = mem2)/\
    (forall (global_depth: nat) (ctxt: Context global_depth) lb ub 
      (stmts: statement_list (S global_depth)) mem mem1,
    semantics_loop ctxt lb ub stmts mem mem1 ->
    forall mem2, semantics_loop ctxt lb ub stmts mem mem2 ->
    mem1 = mem2)/\
    (forall (global_depth: nat) (ctxt: Context global_depth) (stmts: statement_list global_depth)
      mem mem1,
    semantics_statement_list ctxt stmts mem mem1 ->
    forall mem2, semantics_statement_list ctxt stmts mem mem2 ->
    mem1 = mem2).
  Proof.
    apply semantics_ind.
    Case "1".
    intros. inv H. clean_somes.
    assert (wval = wval0). eapply I.semantics_deterministic; eauto.
    subst. congruence.

    Case "2".
    intros. inv H0; clean_somes.
    eauto.

    Case "3".
    intros.
    inv H; clean_somes. reflexivity. contradiction.

    Case "4".
    intros.
    inv H1; clean_somes; try contradiction.
    assert (mem2 = mem5) by eauto. subst. eauto.

    Case "5".
    intros.
    inv H; clean_somes. reflexivity.

    Case "6".
    intros.
    inv H1; clean_somes.
    assert (mem2 = mem5) by eauto. subst. eauto.
  Qed.


  Lemma semantics_statement_deterministic:
    forall (global_depth: nat) (ctxt: Context global_depth) (stmt: statement global_depth)
      mem mem1,
    semantics_statement ctxt stmt mem mem1 ->
    forall mem2, semantics_statement ctxt stmt mem mem2 ->
    mem1 = mem2.
  Proof.
    destruct semantics_deterministic as [? [? ?]]; auto.
  Qed.


  Lemma semantics_loop_deterministic:
    forall (global_depth: nat) (ctxt: Context global_depth) lb ub 
      (stmts: statement_list (S global_depth)) mem mem1,
      semantics_loop ctxt lb ub stmts mem mem1 ->
      forall mem2, semantics_loop ctxt lb ub stmts mem mem2 ->
        mem1 = mem2.
  Proof.
    destruct semantics_deterministic as [? [? ?]]; auto.
  Qed.

  Lemma semantics_statement_list_deterministic:
    forall (global_depth: nat) (ctxt: Context global_depth) (stmts: statement_list global_depth)
      mem mem1,
      semantics_statement_list ctxt stmts mem mem1 ->
      forall mem2, semantics_statement_list ctxt stmts mem mem2 ->
        mem1 = mem2.
  Proof.
    destruct semantics_deterministic as [? [? ?]]; auto.
  Qed.


  Inductive program_semantics prog params mem1 mem2 :=
  | PS_intros:
    forall Vparams,
      make_vector prog.(prog_nbr_global_parameters) params = Some Vparams ->
      semantics_statement_list  Vparams prog.(prog_main) mem1 mem2->
      program_semantics prog params mem1 mem2.

  Theorem program_sem_determinisic: forall prog params mem1 mem2 mem2',
    program_semantics prog params mem1 mem2 -> program_semantics prog params mem1 mem2' ->
    mem2 = mem2'.
  Proof.
    intros * PROG_SEM PROG_SEM'.
    inv PROG_SEM; inv PROG_SEM'. simpl in *.
    assert (Vparams = Vparams0) by congruence. subst.
    eapply semantics_statement_list_deterministic; eauto.
  Qed.

End Semantics.


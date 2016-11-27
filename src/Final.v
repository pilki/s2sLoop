Add LoadPath "../from_compcert".
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
Require Import PermutInstrs.
Require Import Tilling.
Require Import SimpleLanguage.
Open Scope string_scope.
(*Set Implicit Arguments.*)
Open Scope Z_scope.




Module Validator (Import M:BASEMEM(ZNum))
  (I:INSTRS(ZNum) with Definition Value := M.Value).
  Module Mem := MEMORY(ZNum)(M).
  Import Mem.

  Module Per := Permut(M)(I).
  Import Per.
  Import Til.
  Import EP.
  Import P. Import T. Import L.

  Definition optimize
    (blackbox: Poly_Program -> 
      res ((list (list (positive * nat))) * list (list (list Z))))
    (prog:Program) : res Poly_Program :=
    do{;
      unopt_pprog <- extract_program prog;;
      tilling_info, new_schedule <- blackbox unopt_pprog;;
      tilled_pprog <- res_of_option (mk_tilled_poly_prog unopt_pprog tilling_info)
        "The tilling failed";
      change_schedule tilled_pprog new_schedule
      }.

  Theorem preservation: forall lprog pprog blackbox,
    optimize blackbox lprog = OK pprog ->
    forall args,
      forall mem1 mem2,
        program_semantics lprog args mem1 mem2 ->
        (exists mem2', poly_program_semantics pprog args mem1 mem2') /\
        (forall mem2', poly_program_semantics pprog args mem1 mem2' -> mem2 ≡ mem2').
  Proof.
    intros.
    unfold optimize in H. prog_dos.
    destruct _XY_ as (tilling_info, new_schedule).
    prog_dos.
    pose proof (extract_program_correct _ _ Heq_do args mem1 mem2 X).
    clear Heq_do X.
    rewrite (mk_tilled_poly_prog_ok _ _ _ Heq_do1) in H0.
    eapply change_schedule_OK; eauto.
  Qed.


End Validator.

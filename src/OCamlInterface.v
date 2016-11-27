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
Require Import Final.
Open Scope string_scope.
(*Set Implicit Arguments.*)
Open Scope Z_scope.

Set Implicit Arguments.

Fixpoint Midentity `{Numerical Num} n : Matrix Num n n :=
  match n with
    | O => exist _ [] eq_refl
    | S n' =>
      (1 ::: V0 n') :::
      Vmap (fun v => 0 ::: v) (Midentity n')
  end%numerical.

(*
TODO:

Lemma Midentity_correct `{Numerical Num}: forall n (v: Vector Num n),
  Midentity n × v = v.
Proof.
  induction' n as [|n]; intros.
  Case "O".
    apply PVeq_Veq. dest_vects. destruct v; clean.
  Case "S n".
    simpl.
    Vdestruct v as x v.
    specialize (IHn v).
    unfold Mprod_vect in *.

*)

Definition ZMidentity n : ZMatrix n n := Midentity n.
Definition ext_ZMidentity n : ZMatrix n (S n) :=
  Vmap (fun v => 1 ::: v) (ZMidentity n).


Unset Elimination Schemes.
Module SV := Validator BM SimpleLanguage.Instructions.
Definition optimize := SV.optimize.
Definition preservation := SV.preservation.

(* some functions to not mess up dependent types *)

Import SimpleLanguage.Instructions.

Inductive PExpression : Type :=
| PExp_const: list Z -> PExpression
| PExp_loc: Array_Id -> list (list Z) -> PExpression
| PExp_bin: PExpression -> Binary_opp -> PExpression -> PExpression
| PExp_opp: PExpression -> PExpression.




Fixpoint make_Expression n (pexp: PExpression): option (Expression n) :=
  match pexp with
  | PExp_const l =>
    do v <- make_vector (S n) l;
    Some (Exp_const v)
  | PExp_loc aid l =>
    do v <- mmap (make_vector (S n)) l;
    Some (Exp_loc (aid, v))
  | PExp_bin pl opp pr =>
    do l <- make_Expression n pl;
    do r <- make_Expression n pr;
    Some (Exp_bin l opp r)
  | PExp_opp pe =>
    do e <- make_Expression n pe;
    Some (Exp_opp  e)
  end.


Record PInstruction: Type :=
  { Pcontext_size: nat;
    Pwrite_loc: Array_Id * list (list Z);
    Pbody: PExpression;
    Pinstr_loop_vars : list ocaml_string;
    Pinstr_body_string : ocaml_string }.


Definition make_Instruction (pinstr: PInstruction): option Instruction :=
  let 'Build_PInstruction pnargs (paid, pwloc) pb lvars bstring:= pinstr in
  do wlocs <- mmap (make_vector (S pnargs)) pwloc;
  do b <- make_Expression pnargs pb;
  Some (Build_Instruction' (paid, wlocs) b lvars bstring).

Import SV.Per.Til.EP.L.
Import T.

Definition Pbound := list (Z * list Z).
Definition make_bound global_depth (pbnd: Pbound): option (bound global_depth) :=
  match pbnd with
    | [] => None
    | (z, l) :: pbnd' =>
      do v <- make_vector (S global_depth) l;
      do tl <-
        mmap (fun p: Z * list Z =>
          let (z, l) := p in
            do v <- make_vector (S global_depth) l;
            Some (z, v)) pbnd';
      Some ((z, v), tl)
  end.


Inductive Pstatement : Type :=
    PLoop : Pbound ->
            Pbound ->
            Pstatement_list -> Pstatement
  | PInstr : Instruction ->
             list (list Z) ->
             Pstatement
  with Pstatement_list  : Type :=
    Pstl_nil : Pstatement_list
  | Pstl_cons : Pstatement ->
                Pstatement_list -> Pstatement_list.

Fixpoint make_statement n (pst:Pstatement) : option (statement n) :=
  match pst with
  | PLoop plb pub pstlst =>
    do{;
      lb <- make_bound n plb;;
      ub <- make_bound n pub;;
      stlst <- make_statement_list (S n) pstlst;
      Some (Loop lb ub stlst)
    }
  | PInstr instr l =>
    do m <- make_matrix (context_size instr) (S n) l;
    Some (Instr instr m)
  end
with make_statement_list n pstlst : option (statement_list n) :=
  match pstlst with
  | Pstl_nil => Some stl_nil
  | Pstl_cons pst pstlst' =>
    do{;
      st <- make_statement n pst;;
      stlst <- make_statement_list n pstlst';
      Some (stl_cons st stlst)
    }
  end.

 Record PProgram :=
   { Pprog_nbr_global_parameters : nat;
     Pprog_main : Pstatement_list}.

 Definition make_Program pprog : option Program :=
   do stlst <- make_statement_list pprog.(Pprog_nbr_global_parameters) pprog.(Pprog_main);
   Some {| prog_nbr_global_parameters := pprog.(Pprog_nbr_global_parameters);
           prog_main := stlst|}.








(* this is a simplified version of loops *)

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
Require Import Bounds.
Open Scope Z_scope.


(* we want id for instruction that are not just ident (it polutes
   every thing) so we use a singleton, defined in ClassesAndNotations*)

(*Record Instr_Id := mk_Instr_Id 
  { open_Instr_Id : ident}.

Global Instance singletonInd_Instr_Id : singletonInd Instr_Id ident :=
{ open := open_Instr_Id;
  mk := mk_Instr_Id}.
Proof.
  destruct i; auto.
  auto.
Qed.*)




(* The Loop language and its semantics are parametrized by the
   instructions of the source language, for example C instructions for
   the source to source version, or Cminor ones for the complete
   version bound to Compcert *)

Module Type INSTRS(N:NUMERICAL).
  Import N.
  Existing Instance Numerical_Num.
  Module T := Tools(N).
  Import T.


  (* The values of the language *)
  Parameter Value: Type.

  (* the abstract type of instructions *)
  Parameter Instruction: Type.


  (* the number of variables for the Instruction. Typically, the depth
     of the instruction in the loop nest in the original program plus
     the number of parameters of the program, but not counting the
     extra 1
     

     For example, for a program with one global variable N,

     for (i = 0 -> N){
       T[i] = 0; //I1
       for(j = 0 -> i){
         U[j] += T[j]; //I2
       }
     }

     I1 will have a context_size of 2 (i and N) and I2 of 3 (j, i and
     N) (even if i does not appear in I2)
     *)

  Parameter context_size: Instruction -> nat.


  (* What locations are read by the instruction.

     The ident is the one of the array, and the matrix is the linear
     form that must be applied to the context to obtain the cell in
     the array.


     The context is here augmented with 1, as usual, to allow affine
     and not just linear transformations. All the location are read.

     The lenght of the inside list must correspond to the dimension of
     the array, but this is not enforced by the type.

     *)

  Parameter read_locs: forall i: Instruction,
    list (Array_Id * list (Vector Num ( S (context_size i)))).


  (* each instruction write one, and exactly one location. The initial
     idea of having potentially several location optionally written to
     allow conditional has been abandoned because it would not allow
     to add dynamic tests. The idea is that since a dynamic comparison
     of pointers can fail if one of the two pointers is not defined,
     we must make sure that every location is accessed to be able to
     add the test, so that if a pointer is not valid, the write would
     have failed in the original program.

     One could think you may want to write at most one location. But
     the instructions in loops are pure except for the written
     location. So if an instruction does not write anything, it is
     just useless

     As for read locations, the length of the list must be equal to
     the dimension of the array *)

  Parameter write_loc: forall i: Instruction,
    Array_Id * list (Vector Num (S (context_size i))).



  (* the semantics of the instruction is "pure" (it does not talk
     explicitly about the memory), except specifically on the written
     instructions and depends only on the read values. It is in Prop
     because it is not used by the optimiser (the optimizer is
     agnostic in the semantics of the instructions. for example it
     cannot use the fact that addition is commutative), just by the
     preservation proof. It takes the context as an input to allow
     instruction like T[i] = i; or T[i] = N*)

  Parameter semantics: forall i,
    Context (context_size i) -> (** the context *)
    list Value -> (** the read Values *)
    Value -> (** the result of the evaluation *)
    Prop.

  (* For the validator to prove that two loops programs are
     equivalent, it will lift them to the polyhedral world, and
     compare them there. Hence, it needs a complete equivalence
     between the loop form and the polyhedral form, which should need
     determinism of the semantics. I should check that this is true for
     "pure" C instructions *)

  Parameter semantics_deterministic:
    forall i v lv val1 val2,
      semantics i v lv val1 -> semantics i v lv val2 -> val1 = val2.

End INSTRS.

(* as for memories, we need to be able to move from instruction in int
   to instructions in Z *)

Module INSTRSI2Z (I:INSTRS(IntNum)) <: INSTRS(ZNum).
  Definition Instruction := I.Instruction.
  Definition Value := I.Value.
  Module T := Tools(ZNum).
  Import T.
  (* the number of arguments for the instruction. Typically, the depth
     of the instruction in the loop nest in the original program plus
     the number of parameters of the program *)

  Definition context_size:= I.context_size.

  (* What locations are read by the instruction. The ident is then one
     of the array, and the matrix is the linear form that must be
     applied to the context to obtain the cell in the array. The
     context is here augmented with 1, as usual. All the location are
     read *)

  Definition i2zidmat {p} (pair : Array_Id * list (IVector p)) :=
    match pair with
      | (id, l) => (id, map i2zvect l)
    end.


  Definition read_locs i :=
    map i2zidmat (I.read_locs i).

  Definition write_loc i := i2zidmat (I.write_loc i).

  Inductive sem i (zv: Vector Z (context_size i)) lv v : Prop :=
    | sem_intro:
      forall iv, z2ivect zv = Some iv -> I.semantics i iv lv v ->
        sem i zv lv v.
  Definition semantics := sem.


  Lemma semantics_deterministic:
    forall i v lv val1 val2,
      semantics i v lv val1 -> semantics i v lv val2 -> val1 = val2.
  Proof.
    intros * SEM1 SEM2.
    inv SEM1; inv SEM2.
    replace iv0 with iv in *; [|congruence].
    eapply I.semantics_deterministic; eauto.
  Qed.
End INSTRSI2Z.


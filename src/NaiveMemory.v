(* this is a naive interface for a memory model. It is not used it the
   code, just in my (Alexandre Pilkiewicz) dissertation *)
Require Import Libs.
Require Import AST.
Require Import Setoid.
Require Import ArithClasses.

(*Require Import Floats.*)

Record Array_Id := mk_Array_Id {
  open_Array_Id : ident}.

Global Instance singletonInd_Array_Id : singletonInd Array_Id ident :=
{ open := open_Array_Id;
  mk := mk_Array_Id}.
Proof.
  destruct i; auto.
  auto.
Qed.

Record Cell_Id `(Numerical Num) := mkCellIdent
  { array : Array_Id;
    cell : list Num}.

Implicit Arguments Cell_Id [[H]].
Implicit Arguments array [[Num] [H]].
Implicit Arguments cell [[Num] [H]].


Module Type NAIVEMEM(N:NUMERICAL).
  Import N.
  Existing Instance Numerical_Num.

  (** values of the language *)
  Parameter Value: Type.

  (** memories *)
  Parameter Memory: Type.

  Parameter read: Memory -> Cell_Id Num -> option Value.
  Parameter write: Memory -> Cell_Id Num -> Value -> option Memory.
  Parameter rws: forall mem1 mem2 ci v,
    write mem1 ci v = Some mem2 ->
    read mem2 ci = Some v.

  Parameter rwo: forall mem1 mem2 ci1 ci2 v,
    write mem1 ci1 v = Some mem2 -> ci1 <> ci2 ->
    read mem2 ci2 = read mem1 ci2.
End NAIVEMEM.
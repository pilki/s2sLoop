Require Import Libs.
(*Require Import Floats.*)
Require Import AST.
Require Import Setoid.
Require Import ArithClasses.



(* we define the type of memories for Loops *)


(* memory is splitted in arrays. Each array is recognised through it's
   ident.

   each cell of the array is then accessed through a list of indexes
   of type int *)

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

Definition z2icell (ci: Cell_Id Z) : option (Cell_Id int) :=
  do c <- z2ilist (ci.(cell));
  Some {| array := ci.(array);
     cell := c|}.

Definition i2zcell (ci: Cell_Id int) : Cell_Id Z :=
  {| array := ci.(array);
     cell := i2zlist ci.(cell)|}.

Lemma z2i2zcell zci ici: z2icell zci = Some ici -> i2zcell ici = zci.
Proof.
  unfold z2icell, i2zcell.
  destruct zci, ici. simpl. intro SOME.
  monadInv SOME.
  inv SOME.
  f_equal.
  apply z2i2zlist. auto.
Qed.

Global Instance EqDec_t `{Numerical Num}: EqDec (Cell_Id Num).
Proof.
  constructor. intros.
  dec_eq.
Qed.


Module Type BASEMEM(N:NUMERICAL).
  Import N.
  Existing Instance Numerical_Num.

  (* values of the language *)
  Parameter Value: Type.

  (* memories *)
  Parameter Memory: Type.


  (* memories can be of "same layout", and it's an equivalence
     relation. One can see two memories with the same layout as memories
     with the same arrays, containing the same layout of values. *)

  Parameter same_memory_layout: relation Memory.

  Declare Instance Equiv_smt: Equivalence same_memory_layout.


  Parameter read: Memory -> Cell_Id Num -> option Value.

  (* two memories with same layout are readable at the same locations *)

  Parameter read_same_layout:
    forall mem1 mem2 ci, same_memory_layout mem1 mem2 ->
    is_some (read mem1 ci) -> is_some (read mem2 ci).

  Parameter write: Memory -> Cell_Id Num -> Value -> option Memory.

  (* you don't change the layout of a memory by writing in it *)

  Parameter write_keep_layout:
    forall mem1 mem2 ci v, write mem1 ci v = Some mem2 -> same_memory_layout mem1 mem2.

  (* two memories with the same layout are accessible at the same locations *)
  Parameter write_same_layout:
    forall mem1 mem2 ci v, same_memory_layout mem1 mem2 ->
    (is_some (write mem1 ci v) -> is_some (write mem2 ci v)).


  (* write followed by a read *)
  Definition read_write mem ci v : option Value :=
    do mem' <- write mem ci v;
    read mem' ci.

  (* at the same location for two memories with the same layout, we read
     the new value *)
  (* one might have espect something like:

     read_write mem1 ci v = Some mem2 ->
     read mem2 ci = Some v

     This would not take into account the fact that writing at some
     location can lead to lose information. Say you have a char[] and
     you write a large value in it. The compiler will automatically
     downgrade the large value to a char before writing it. So reading
     it will lead to a value in the range of char, not the initial one.
     
     For the correctness of the reordering of write, it is in fact
     useless to know exactly what would be read, but just that it is
     the same, whatever the order of the writes are*)

  Parameter rws: forall mem1 mem2 ci v,
    same_memory_layout mem1 mem2 ->
    read_write mem1 ci v = read_write mem2 ci v.

  (* at an other location, we read the old value *)
  Parameter rwo: forall mem1 mem2 ci1 ci2 v,
    write mem1 ci1 v = Some mem2 -> ci1 <> ci2 ->
    read mem2 ci2 = read mem1 ci2.

End BASEMEM.


(* This is a very simplist instance of the module type. A more
   credible one can be found in OtherMemory. It is to show it is
   instanciable and to "explain" better some prerequisites*)

Module BMem(N:NUMERICAL) <: BASEMEM(N).
  Import N.
  Existing Instance Numerical_Num.


  Definition Value := Z.

  (*
  Inductive has_type: value -> typ -> Prop :=
  | HT_int: forall i, has_type (Vint i) Tint
  | HT_float: forall f, has_type (Vfloat f) Tfloat.

  Definition typ_of (v:val) :=
    match v with
      | Vint _ => Tint
      | Vfloat _ => Tfloat
    end.
  *)
  Module ValEqDec <: EQUALITY_TYPE.
    Definition t := Value.
    Global Instance EqDec_t: EqDec Value.
    Proof.
      constructor. unfold Value.
      apply ZEqDec.EqDec_t.
    Qed.
  End ValEqDec.



  Definition valid_cell:= Cell_Id Num -> bool.


  Definition eqA_valid_cell (mt1 mt2: valid_cell) := forall ci, mt1 ci = mt2 ci.

  Lemma valid_cell_equiv: Equivalence eqA_valid_cell.
  Proof.
    prove_equiv; dintuition congruence.
  Qed.

  Instance EqA_mt : EqA valid_cell:=
  { eqA := eqA_valid_cell;
    eqAequiv := valid_cell_equiv}.


  (* a memory is a mapping between Cell_Ids and Values *)
  Definition Memory := Cell_Id Num -> option Value.


  Implicit Type m: Memory.

  Definition valid_cell_of (mem: Memory) ci :=
    match mem ci with
      | None => false
      | Some _ => true
    end.

  Definition same_memory_layout mem1 mem2 := valid_cell_of mem1 ≡ valid_cell_of mem2.

  Global Instance Equiv_smt: Equivalence same_memory_layout.
  Proof.
    prove_equiv; unfold same_memory_layout.
    reflexivity. symmetry; auto.
    intros * H H0. eapply transitivity; eauto.
  Defined.


  Definition read m ci:= m ci.

  (* two memories with same layout are readable at the same locations *)

(*  Lemma same_typ_of: forall mem1 mem2 ci, same_memory_layout mem1 mem2 ->
    typ_of <$> mem1 ci = typ_of <$> mem2 ci.
  Proof.
    intros * H.
    unfold same_memory_layout, mem_type_of in H.
    simpl in *. auto.
  Qed.*)

  Lemma read_same_layout:
    forall mem1 mem2 ci, same_memory_layout mem1 mem2 -> is_some (read mem1 ci) ->
      is_some (read mem2 ci).
  Proof.
    unfold same_memory_layout, read, valid_cell_of.
    intros * H. compute in H. specialize (H ci).
    destruct (mem1 ci), (mem2 ci); intro; simpl in *;  auto.
  Qed.


  Definition write m ci v :=
    if valid_cell_of m ci then
      Some (fun ci' => if ci' == ci then Some v else m ci')
    else
      None.

  (* you don't change the layout of a memory by writing in it *)

  Lemma write_keep_layout:
    forall mem1 mem2 ci v, write mem1 ci v = Some mem2 -> same_memory_layout mem1 mem2.
  Proof.
    unfold write, same_memory_layout.
    intros mem1 mem2 ci v H.
    simpl. intro ci'.
    dest_if; simpl; clean.
    unfold valid_cell_of in *; simpl in *.
    dest==; subst; auto.
  Qed.

  Lemma write_same_layout:
    forall mem1 mem2 ci v, same_memory_layout mem1 mem2 -> (is_some (write mem1 ci v) -> is_some (write mem2 ci v)).
  Proof.
    unfold same_memory_layout, write, valid_cell_of. compute.
    intros mem1 mem2 ci v H.
    specialize (H ci).
    destruct (mem1 ci); destruct (mem2 ci); clean.
  Qed.


  Definition read_write m ci v : option Value :=
    do m' <- write m ci v;
    read m' ci.

  Lemma rws: forall mem1 mem2 ci v,
    same_memory_layout mem1 mem2 ->
    read_write mem1 ci v = read_write mem2 ci v.
  Proof.
    unfold same_memory_layout, write, read, valid_cell_of. compute.
    intros mem1 mem2 ci v H.
    specialize (H ci).
    destruct (mem1 ci); destruct (mem2 ci); clean.
  Qed.

  Lemma rwo: forall mem1 mem2 ci1 ci2 v, write mem1 ci1 v = Some mem2 -> ci1 <> ci2 ->
    read mem2 ci2 = read mem1 ci2.
  Proof.
    unfold same_memory_layout, write, read, valid_cell_of. compute.
    intros mem1 mem2 ci1 ci2 v H H0.
    destruct (mem1 ci1); clean.
  Qed.

End BMem.

(* build a complete memory from a base memory *)
Module MEMORY (N:NUMERICAL) (BM: BASEMEM(N)).
  Export BM.

  (* two memories are equivalent if the map the same cells to the same values
     and they have the same layout *)
  Definition eqA_memory mem1 mem2 :=
    same_memory_layout mem1 mem2 /\
    forall ci, read mem1 ci = read mem2 ci.

  Lemma eqA_mem_equiv : Equivalence eqA_memory.
  Proof.
    prove_equiv; unfold eqA_memory; intros; split'.
    Case "Reflexivity"; SCase "left". 
      reflexivity.
    Case "Reflexivity"; SCase "right". 
      reflexivity.
    Case "Symmetry"; SCase "left".
      inv H. symmetry; auto.
    Case "Symmetry"; SCase "right".
      inv H; symmetry; auto.
    Case "Transitivity"; SCase "left".
      inv H; inv H0; etransitivity; eauto.
      inv H; inv H0; etransitivity; eauto.
  Qed.
    


  (* this gives us the notation ≡ *)
  Global Instance EqA_memory : EqA Memory :=
  { eqA := eqA_memory;
    eqAequiv := eqA_mem_equiv}.

  Lemma EqA_memory_unfold: forall mem1 mem2,
    mem1 ≡ mem2 = (same_memory_layout mem1 mem2 /\
    forall ci, read mem1 ci = read mem2 ci).
  Proof.
    reflexivity.
  Qed.

  

  Lemma use_EqA_memory_1: forall mem1 mem2,
    mem1 ≡ mem2 -> forall ci, read mem1 ci = read mem2 ci.
  Proof.
    intros * [? ?]; auto.
  Qed.

  Lemma use_EqA_memory_2: forall mem1 mem2,
    mem1 ≡ mem2 -> same_memory_layout mem1 mem2.
  Proof.
    intros * [? ?]; auto.
  Qed.


  (* we don't want EqA_memory to be unfold in general *)
  Global Opaque EqA_memory.


  Global Hint Resolve use_EqA_memory_1 use_EqA_memory_2 read_same_layout
    write_keep_layout write_same_layout rws rwo: memory.

  Lemma smt_refl: forall m, same_memory_layout m m.
  Proof. reflexivity. Qed.

  Lemma smt_sym: forall mem1 mem2, same_memory_layout mem1 mem2 -> same_memory_layout mem2 mem1.
  Proof. symmetry. auto. Qed.

  Lemma smt_trans: forall mem1 mem2 m3, same_memory_layout mem1 mem2 -> same_memory_layout mem2 m3 -> same_memory_layout mem1 m3.
  Proof. etransitivity; eauto. Qed.

  Global Hint Immediate smt_sym: memory.
  Global Hint Resolve 5 smt_trans: memory.
  Hint Extern 1 (same_memory_layout ?X ?X) => reflexivity: memory.


  Ltac get_all_mem_layouts :=
  option_on_right;
  repeat
  match goal with
    | H: ?mem1 ≡ ?mem2 |- _ =>
      match goal with
        | H' : same_memory_layout mem1 mem2 |- _ => fail 1
        | H' : same_memory_layout mem2 mem1 |- _ => fail 1
        | |- _ =>
          pose proof (use_EqA_memory_2 _ _ H)
      end
  end;
  repeat
  match goal with
    | H: write ?mem1 _ _ = Some ?mem2 |- _ =>
      match goal with
        | H' : same_memory_layout mem1 mem2 |- _ => fail 1
        | H' : same_memory_layout mem2 mem1 |- _ => fail 1
        | |- _ =>
          pose proof (write_keep_layout _ _ _ _ H)
      end
  end.


  Definition owrite omem ci v: option Memory :=
    do mem <- omem;
    write mem ci v.

  Lemma rws': forall mem1 mem2 mem1' mem2' ci v, same_memory_layout mem1 mem2 ->
    write mem1 ci v = Some mem1' -> write mem2 ci v = Some mem2' ->
    read mem1' ci = read mem2' ci.
  Proof.
    intros mem1 mem2 mem1' mem2' ci v H H0 H1. 
    pose proof (rws mem1 mem2 ci v H). compute in H2.
    rewrite H0, H1 in H2. auto.
  Qed.
  Hint Resolve rws': memory.


  Ltac check_diff x y :=
    match goal with
      | H : x <> y |- _ => idtac
      | H : y <> x |- _  => idtac
    end.

  Ltac push_read_up :=
  repeat
  match goal with
    | H: write ?mem1 ?ci1 ?v = Some ?mem2 |- context[read ?mem2 ?ci2] =>
      check_diff ci1 ci2;
      replace (read mem2 ci2) with (read mem1 ci2) by (symmetry; eapply rwo; eauto)
  end.


  Ltac solve_same_memory :=
    repeat match goal with
             | H : _ ≡ _ |- _ => apply use_EqA_memory_2 in H
           end;
    repeat match goal with
             | H: write _ _ _ = Some _ |- _ =>
               apply write_keep_layout in H; revert H
             | H : same_memory_layout _ _ |- _ => revert H
           end;
    clear'; intros;
    let rec aux := (* aux is used to backtrack *)
    match goal with
    | H: same_memory_layout ?m1 ?m2 |- same_memory_layout ?m1 ?m2
      => apply H
    | H: same_memory_layout ?m1 ?m2 |- same_memory_layout ?m1 ?m2
      => symmetry; apply H
    | H: same_memory_layout ?m1 _ |- same_memory_layout ?m1 _ =>
      etransitivity; [eapply H| clear H; solve [aux]]
    | H: same_memory_layout _ ?m1 |- same_memory_layout ?m1 _ =>
      etransitivity; [symmetry; eapply H| clear H; solve [aux]]
    end in solve [aux].


  (* if two cells are differents, we can permut the write *)
  Lemma permut_write: forall mem1 mem2 ci1 ci2 v1 v2, ci1 <> ci2 ->
    mem1 ≡ mem2 ->
    owrite (write mem1 ci1 v1) ci2 v2 ≡ owrite (write mem2 ci2 v2) ci1 v1.
  Proof.
    intros * DIFF EQUIV.
    remember (write mem1 ci1 v1) as omem1.
    remember (write mem2 ci2 v2) as omem2.
    destruct' omem1 as [mem1'|]; destruct' omem2 as [mem2'|];
    unfold owrite; prog_dos; prog_dos; clean; try reflexivity.

    Case "Some mem1'"; SCase "Some mem2'".

    repeat match goal with
        | H: write ?M1 ?CI ?V = Some _|- context[write ?M2 ?CI ?V] =>
          let HSOME := fresh in
          let HSAME := fresh in
            assert (is_some (write M2 CI V)) as HSOME by
            (assert (same_memory_layout M1 M2) as HSAME by solve_same_memory;
             eapply write_same_layout;[ eapply HSAME| instantiate; eauto]);
            inv HSOME
      end.
    simpl; rewrite EqA_memory_unfold.
    get_all_mem_layouts.

    split'.
    SSCase "left".
      eauto with memory.
    SSCase "right".
      intro ci.
      dest ci == ci1; dest ci == ci2; repeat (progress subst); auto;
        push_read_up; eauto with memory.

    Case "Some mem1'"; SCase "None". 
    simpl.
    get_all_mem_layouts.
    prog_match_option; auto.

    assert (is_some (write mem ci2 v2)) by auto. symmetry in H0.
    eapply (write_same_layout mem mem2) in H1.
    rewrite Heqomem2 in H1. auto. etransitivity; eauto.

    Case "None"; SCase "Some mem2'". 
    simpl.
    get_all_mem_layouts.
    case_eq (write mem2' ci1 v1); intros; auto.

    assert (is_some (write mem2' ci1 v1)) by auto. 
    symmetry in H0. eapply (write_same_layout mem2' mem1) in H2.
    rewrite Heqomem1 in H2. auto.
    symmetry in H0. symmetry. etransitivity; eauto.
  Qed.

End MEMORY.

Module ZBMem := BMem(ZNum).
Module IntBMem := BMem(IntNum).

Module Zmem := MEMORY(ZNum)(ZBMem).
Module Intmem := MEMORY(IntNum)(IntBMem).

Module BmemI2Z(BMI: BASEMEM(IntNum)) <: BASEMEM(ZNum).

  (* values of the language *)
  Definition Value:= BMI.Value.

  (* memories *)
  Definition Memory := BMI.Memory.
  Implicit Type m: Memory.
  Implicit Type ci: Cell_Id Z.

  (* memories can be of "same layout", and it's an equivalence relation *)

  Definition same_memory_layout : relation Memory := BMI.same_memory_layout.

  Global Instance Equiv_smt: Equivalence same_memory_layout.

  Definition read m ci : option Value :=
    do ci' <- z2icell ci;
    BMI.read m ci'.

  (* two memories with same layout are readable at the same locations *)

  Lemma read_same_layout:
    forall mem1 mem2 ci, same_memory_layout mem1 mem2 ->
      is_some (read mem1 ci) -> is_some (read mem2 ci).
  Proof.
    intros * SMT SOME.
    unfold read in *.
    monadInv SOME. simpl_do.
    eapply BMI.read_same_layout; eauto.
  Qed.

  Definition write m ci v: option Memory :=
    do ci' <- z2icell ci;
    BMI.write m ci' v.

  (* you don't change the layout of a memory by writing in it *)

  Lemma write_keep_layout:
    forall mem1 mem2 ci v, write mem1 ci v = Some mem2 -> same_memory_layout mem1 mem2.
  Proof.
    unfold write. intros * SOME.
    monadInv SOME. eapply BMI.write_keep_layout; eauto.
  Qed.

  Lemma write_same_layout:
    forall mem1 mem2 ci v, same_memory_layout mem1 mem2 -> (is_some (write mem1 ci v)
      -> is_some (write mem2 ci v)).
  Proof.
    unfold write. intros * SMT SOME.
    monadInv SOME. simpl_do. eapply BMI.write_same_layout; eauto.
  Qed.



  Definition read_write m ci v : option Value :=
    do m' <- write m ci v;
    read m' ci.


  Lemma rws: forall mem1 mem2 ci v,
    same_memory_layout mem1 mem2 ->
    read_write mem1 ci v = read_write mem2 ci v.
  Proof.
    intros * SMT.
    destruct (z2icell ci) as [ci'|] _eqn.
    pose proof (BMI.rws mem1 mem2 ci' v SMT).
    unfold BMI.read_write in H.
    unfold read_write, read, write.
    rewrite Heqo.
    compute in H. compute. auto.

    unfold read_write, read, write.
    rewrite Heqo. simpl_do. reflexivity.
  Qed.
  Lemma inv_cons: forall A (a1 a2 :A) l1 l2,
    tag_to_inv (a1 :: l1 = a2 :: l2).
  Proof. auto. Qed.
  Hint Rewrite inv_cons: opt_inv.

  Lemma rwo: forall mem1 mem2 ci1 ci2 v, write mem1 ci1 v = Some mem2 -> ci1 <> ci2 ->
    read mem2 ci2 = read mem1 ci2.
  Proof.
    unfold write, read.

    intros * SOME DIFF.
    monadInv SOME.
    prog_dos.
    eapply BMI.rwo; eauto.
    intro. apply DIFF. subst.
    erewrite <- z2i2zcell; eauto.
    erewrite <- (z2i2zcell ci1); eauto.
  Qed.


End BmemI2Z.


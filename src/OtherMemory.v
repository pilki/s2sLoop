Require Import Libs.
Require Import AST.
Require Import Setoid.
Require Import Memory.
Require Import ArithClasses.
Require Import Memtype.
Require Import Memdata.
Require Import Values.
Require Import Relation_Operators.
Require Import Operators_Properties.
Require Import Morphisms.
Set Implicit Agruments.
  

Tactic Notation "rewrite_Heq_do" :=
  repeat
    match goal with
      | H : ?TRM = Some _ |- context[?TRM] =>
        rewrite H
      | H : ?TRM = None |- context[?TRM] =>
        rewrite H
    end; simpl_do.



Module ExtraLemma(CM:MEM).
  Lemma load_store: forall (m1 m2 m1' m2': CM.mem) mc b i v,
    CM.store mc m1 b i v = Some m1' ->
    CM.store mc m2 b i v = Some m2' ->
    CM.load mc m1' b i = CM.load mc m2' b i.
  Proof.
    intros * STORE1 STORE2.
    edestruct (CM.load_store_similar _ _ _ _ _ _ STORE1) as [v1 [LOAD1 _]]; eauto.
    edestruct (CM.load_store_similar _ _ _ _ _ _ STORE2) as [v2 [LOAD2 ?]]; eauto.
    rewrite LOAD1, LOAD2.
    apply CM.load_loadbytes in LOAD1.
    apply CM.load_loadbytes in LOAD2.
    destruct LOAD1 as [bytes1 [LB1 DEC1]].
    destruct LOAD2 as [bytes2 [LB2 DEC2]].
    pose proof (CM.loadbytes_store_same _ _ _ _ _ _ STORE1).
    pose proof (CM.loadbytes_store_same _ _ _ _ _ _ STORE2).
    congruence.
  Qed.
End ExtraLemma.


Require Import Cminor.


Module FromCminorEnv(N:NUMERICAL)(CM:MEM)<:(BASEMEM(N)).
  Import N.
  Existing Instance Numerical_Num.


  (* we define a way to inject the memory model of Cminor inside the
     one of Loops, modulo a reasonable expression of the result of an
     alias analysis *)

  Module EL := ExtraLemma(CM).
  Hint Resolve EL.load_store.


  (* a pointer is a block and an offset *)
  Definition ptr := (block * int)%type.

  (* it can be directly injected inside Cminor values *)
  Definition val_of_ptr (p:ptr) : val:=
    let (b, ofs) := p in Vptr b ofs.


  Coercion val_of_ptr: ptr >-> val.

  Hint Unfold val_of_ptr: no_coerc.

  Implicit Type p: ptr.
  Implicit Type mc chunk: memory_chunk.
  Implicit Type b: block.
  Implicit Type i: ident.


  (* location can be either a pointer or a variable in the
     environment. This will allow to represent a local variable as an
     array of size 1 *)

  Inductive location : Type :=
  | LPtr: ptr -> location
  | LVar: ident -> location.
  Implicit Type l:location.

  Definition LPtr' := LPtr.
  Definition LVar' := LVar.
  Coercion LPtr' : ptr >-> location.
  Coercion LVar' : ident >-> location.

  Hint Unfold LPtr' LVar': no_coerc.
  Ltac no_coerc:= autounfold with no_coerc in *.


  (* two location are "non interfering" (result of alias analysis)
     when accessed according to the memory chunks *)

  Inductive non_interfering:
    location -> memory_chunk -> location -> memory_chunk -> Prop :=

  (** a pointer (in the memory) and an ident (in the local store) are
     non interfering*)
  | NI_pv: forall p mc1 i mc2,
    non_interfering p mc1 i mc2
  | NI_vp: forall i mc1 p mc2,
    non_interfering i mc1 p mc2

  (** two different variables do not interfere *)
  | NI_var: forall i1 mc1 i2 mc2, i1 <> i2 ->
    non_interfering i1 mc1 i2 mc2

  (** two pointers in different blocks do not interfere *)
  | NI_diff_block:
    forall b1 b2 ofs1 ofs2 mc1 mc2, b1 <> b2 ->
      non_interfering (LPtr (b1, ofs1)) mc1 (LPtr (b2, ofs2)) mc2

  (** when in the same block, two pointers are non interfering when the
     corresponding locations do not overlap*)
  | NI_12: forall b ofs1 ofs2 mc1 mc2, (** ptr1 before ptr2 *)
    Int.signed ofs1 + (size_chunk mc1) <= Int.signed ofs2 ->
    non_interfering (LPtr (b, ofs1)) mc1 (LPtr (b, ofs2)) mc2
  | NI_21: forall b ofs1 ofs2 mc1 mc2, (** ptr2 before ptr1*)
    Int.signed ofs2 + (size_chunk mc2) <= Int.signed ofs1 ->
    non_interfering (LPtr (b, ofs1)) mc1 (LPtr (b, ofs2)) mc2.




  (* a memory layout maps the array vision to the low level one

   * a "type" is given to each array (all accesses to any cell of this
     array will be done via this type)

   * each cell_id (array * list int) is mapped to a location

   * this mapping is non interfering
   *)

  Definition Correct_Layout chunk_of_array flatten_access :=
      (* the layout is non interfering *)
      forall ci1 ci2 mc1 mc2 l1 l2,
        ci1 <> ci2 ->

        chunk_of_array ci1.(array) = Some mc1 ->
        chunk_of_array ci2.(array) = Some mc2 ->

        flatten_access ci1 = Some l1 ->
        flatten_access ci2 = Some l2 ->

        non_interfering l1 mc1 l2 mc2.

  Record memory_layout : Type := mkLayout {
    chunk_of_array: Array_Id -> option memory_chunk; (* type of each array *)
    flatten_access: Cell_Id Num -> option location; (* where is each cell maps in memory*)
    correct_layout: Correct_Layout chunk_of_array flatten_access
  }.

  Hint Unfold Correct_Layout.

  (* a "memory" for loops is then a Cminor memory, plus a Cminor
     environment, and a layout *)

  (* Coq's kernel does not allow to use an inductive definition as a
     required field of a module. This explains why we go through an
     intermediate Memory' definition*)

  Record Memory': Type := mkMem {
    ll_mem: CM.mem;
    ll_env: env;
    layout: memory_layout}.
  Definition Memory := Memory'.
  Implicit Type mem: Memory.

  Definition Value := val.

  Definition layout' (mem:Memory) := layout mem.
  Coercion layout': Memory >-> memory_layout.
  Hint Unfold layout': no_coerc.

  Definition read mem ci : option val:=
    do mc <- mem.(chunk_of_array) ci.(array);
    do l <- mem.(flatten_access) ci;
    match l with
      | LPtr p => CM.loadv mc mem.(ll_mem) p
      | LVar i => mem.(ll_env) ! i
    end.


  Definition write mem ci v : option Memory :=
    do mc <- mem.(chunk_of_array) ci.(array);
    do l <- mem.(flatten_access) ci;
    match l with
      | LPtr p =>
        do nm <- CM.storev mc mem.(ll_mem) p v;
        Some {| ll_mem := nm;
                ll_env := mem.(ll_env);
                layout := mem.(layout)|}
      | LVar i =>
        (** we need to check that i already existed in the
           environment, to avoid creating new variables *)
        do _ <- mem.(ll_env) ! i;
        Some {| ll_mem := mem.(ll_mem);
                ll_env := PTree.set i v  mem.(ll_env);
                layout := mem.(layout)|}
    end.

  Ltac destr_ptrs :=
    repeat match goal with | p : ptr |- _ => destruct p end.

  Ltac mymonadInv H :=
    let rec aux _ :=
      monadInv H; try
        match type of H with
          | context[match ?l with
                      | LPtr _ => _
                      | LVar _ => _
                    end] =>
          let p := fresh "p" in let i := fresh "i" in
          destruct l as [p| i]; try aux tt
        end in
     aux tt; destr_ptrs; simpl in *; rewrite_Heq_do.
  
  (* two memories are of "same layout" if you can go from one to the
     other trough a sequence or [write] (since it's a refl *sym* trans
     closure, it's a slightly bigger equivalence class)*)

  Inductive sml_aux: relation Memory :=
  |SMTA_intro: forall mem1 mem2 ci v,
    write mem1 ci v = Some mem2 ->
    sml_aux mem1 mem2.

  Definition same_memory_layout: relation Memory :=
    clos_refl_sym_trans_1n _ sml_aux.

  Hint Constructors clos_refl_sym_trans_1n.

  Instance Equiv_smt: Equivalence same_memory_layout.
  Proof.
    unfold same_memory_layout.
    destruct (clos_rst_is_equiv _ sml_aux). unfold reflexive, transitive, symmetric in *.
    prove_equiv; intros; rewrite <- (clos_rst_rst1n_iff) in *; eauto.
  Qed.

  (* you don't change the layout of a memory by writing in it *)
  Lemma write_keep_layout:
    forall mem1 mem2 ci v, write mem1 ci v = Some mem2 -> same_memory_layout mem1 mem2.
  Proof.
    intros * WRITE.
    econstructor; auto.
    left. econstructor. eauto.
  Qed.

(*  Ltac prog_match_loc_aux TERM :=
    match TERM with
      | context[match ?X with |LPtr _ => _ | LVar _ =>  _ end] =>
        let p := fresh "p" in let i := fresh "i" in 
        destruct X as [p|i] _eqn
    end.

  Ltac prog_match_location :=
    match goal with
      | H : ?TERM |- _ =>
        prog_match_loc_aux TERM
      | |- ?TERM =>
        prog_match_loc_aux TERM
    end.*)

  Lemma sml_aux_same_layout:
    forall mem1 mem2, sml_aux mem1 mem2 \/ sml_aux mem2 mem1 ->
      layout mem1 = layout mem2.
  Proof.
    intros * [H|H]; inv H;
    mymonadInv H0; auto.
  Qed.

  Lemma same_layout_same_layout:
    forall mem1 mem2, same_memory_layout mem1 mem2 -> layout mem1 = layout mem2.
  Proof.
    intros * SMT. induction SMT; auto.
    rewrite <- IHSMT.
    apply sml_aux_same_layout; auto.
  Qed.

  Lemma write_same_layout:
    forall mem1 mem2 ci v, same_memory_layout mem1 mem2 ->
    (is_some (write mem1 ci v) -> is_some (write mem2 ci v)).
  Proof.
    intros * SMT. revert ci v. induction SMT; intros * ISSOME'. auto.

    apply IHSMT. clear IHSMT.
    inversion ISSOME' as [m ISSOME]. clear ISSOME'. clean.
    pose proof (sml_aux_same_layout _ _ H) as SML.

    unfold write in *; no_coerc;
    rewrite SML in *;
    unfold CM.storev in *;
    mymonadInv ISSOME.

    (* write in memory *)
    edestruct (CM.valid_access_store) as [m VAS];[|rewrite VAS; simpl_do; auto].
    destruct H as [H | H]; inv H; mymonadInv H0; simpl in *;
    eauto using CM.store_valid_access_1,
      CM.store_valid_access_2, CM.store_valid_access_3.

    (* write in store *)

    destruct H as [H | H]; inv H; mymonadInv H0; auto.
    dest i0 == i; subst.
    rewrite PTree.gss; simpl_do; auto.
    rewrite PTree.gso; auto; simpl_do; rewrite_Heq_do; auto.
    
    dest i0 == i; subst; rewrite_Heq_do; auto.
    rewrite PTree.gso in Heq_do1; auto; simpl_do; rewrite_Heq_do; auto.
  Qed.


  Definition read_write mem ci v : option val :=
    do mem' <- write mem ci v;
    read mem' ci.

  (* two memories with same layout are readable at the same locations *)

  Lemma read_same_layout:
    forall mem1 mem2 ci, same_memory_layout mem1 mem2 ->
    is_some (read mem1 ci) -> is_some (read mem2 ci).
  Proof.
    intros * SMT. revert ci.
    induction SMT; intros * ISSOME'; auto.
    pose proof sml_aux_same_layout _ _ H as SML.
    apply IHSMT; clear IHSMT. clear dependent z.
    inversion ISSOME' as [m ISSOME]; clear ISSOME'. clean.
    unfold read in *. no_coerc. rewrite SML in *.
    mymonadInv ISSOME.


    (* write in memory *)
    edestruct (CM.valid_access_load) as [v HREW]; [| rewrite HREW; auto].
    apply CM.load_valid_access in ISSOME.
    destruct H as [H | H]; inv H; mymonadInv H0; simpl in *;
    eauto using CM.store_valid_access_1,
      CM.store_valid_access_2, CM.store_valid_access_3.

    (* write in store *)
    destruct H as [H | H]; inv H; mymonadInv H0; simpl in *; clean;
    dest i0 == i; subst.
    rewrite PTree.gss; auto.
    rewrite PTree.gso; auto.
    rewrite PTree.gss in ISSOME; auto.
    rewrite PTree.gso in ISSOME; auto.
  Qed.
  
  Lemma rws: forall mem1 mem2 ci v,
    same_memory_layout mem1 mem2 ->
    read_write mem1 ci v = read_write mem2 ci v.
  Proof.
    intros * SMT.
    unfold read_write.
    pose proof (same_layout_same_layout mem1 mem2 SMT) as SML.
    destruct (write mem1 ci v) as [m'|] _eqn; simpl_do.

    assert (is_some (write mem2 ci v)).
      eapply write_same_layout; eauto. auto.
    inversion H as [m'0 ISSOME]; clear H. simpl_do. clean.
    unfold write in*; unfold read in *. no_coerc. rewrite SML in *.
    mymonadInv Heqo; mymonadInv ISSOME; simpl in *. eauto.
    repeat rewrite PTree.gss; auto.

    destruct (write mem2 ci v) as [m'|] _eqn; simpl_do; auto.
    assert (is_some (write mem1 ci v)). symmetry in SMT.
     eapply write_same_layout; eauto. auto.
    inv H; congruence.
  Qed.

  Lemma rwo: forall mem1 mem2 ci1 ci2 v, write mem1 ci1 v = Some mem2 -> ci1 <> ci2 ->
    read mem2 ci2 = read mem1 ci2.
  Proof.
    intros * WRITE NEQ.
    unfold read, write in *.
    mymonadInv WRITE; simpl in *; clean;
    unfold CM.storev, CM.loadv in *; no_coerc;
    prog_dos; try destruct l; try destruct l0; destr_ptrs; simpl_do; eauto;
    destruct mem1; simpl in *;
    destruct layout0; simpl in *;
    specialize (correct_layout0 _ _ _ _ _ _ NEQ Heq_do Heq_do2 Heq_do0 Heq_do3);
    inv correct_layout0;
    
    try eapply CM.load_store_other; eauto.

    rewrite PTree.gso; auto.

  Qed.


End FromCminorEnv.




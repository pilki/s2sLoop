Require Import Coqlib.
Require Import Maps.
Require Import SetoidList.
Require Import Axioms.
Require Import ClassesAndNotations.
Require Import Libs.
Set Implicit Arguments.

(*Definition decidable (P:Prop) := {P} + {~P}.
Definition decidable1 (A:Type) (P:A -> Prop) := forall a, decidable (P a).
Definition decidable2 (A:Type) (P:A -> A -> Prop) := forall a1 a2, decidable (P a1 a2).
Definition semi_decidable (P:Prop) := {P} + {True}.
Definition semi_decidable1 (A:Type) (P:A -> Prop) := forall a, semi_decidable (P a).
Definition semi_decidable2 (A:Type) (P:A -> A -> Prop) := forall a1 a2, semi_decidable (P a1 a2).
*)

Module Type ISET (X:EQUALITY_TYPE).
  Definition elt := X.t.
  Definition eq_elt (t1 t2 : elt) := t1 = t2.
(*  Definition eq_elt := @Logic.eq elt.
  Variable deq_elt: forall e1 e2: elt, decidable (e1 = e2).
  Notation "x =? y" := (deq_elt x y) (at level 70, no associativity).*)
  Variable t:Type.
  Variable empty: t.

  Variable mem: elt -> t -> bool.
  Definition In x s : Prop :=
    mem x s = true.

  Declare Instance EqA_t : EqA t.

  Declare Instance EqASDec_t : EqASDec t.

  Notation "s [<=] t" :=
    (forall x : elt, In x s -> In x t) (at level 70, no associativity).

  Definition included s t := s [<=] t.

  Hypothesis mem_1 : forall x s, In x s -> mem x s = true.
  Hypothesis mem_2 : forall x s, mem x s = true -> In x s.

  Variable add: elt -> t -> t.
(*  Variable remove_force: elt -> t -> t.*)
  Variable remove: elt -> t -> t.
  Hypothesis  mempty:
    forall x, ~ In x empty.

  Hypothesis mas:
    forall x s, In x (add x s).
  Hypothesis add_1:
    forall x s, In x (add x s).
  Hypothesis mao:
    forall x y s, x <> y -> mem x (add y s) = mem x s.
  Hypothesis add_2: forall y s, s [<=] add y s.
  Hypothesis add_3:
    forall x y s, x <> y -> In y (add x s) -> In y s.
  Hypothesis add_iff :
    forall x y s,
      In y (add x s) <-> x = y \/ In y s.
  Hypothesis not_mem_iff :forall x s,  ~In x s <-> mem x s = false.
  Hypothesis maspec:
    forall x y s,
      mem x (add y s) = if x == y then true else mem x s.

  Hypothesis maident:
    forall x s, In x s -> add x s = s.

  Hypothesis rempty: forall x, remove x empty = empty.
(*  Hypothesis rfempty: forall x, remove_force x empty = empty.*)
  Hypothesis mrs:
    forall x s, mem x (remove x s) = false.
  Hypothesis mro:
    forall x y s, x <> y -> mem x (remove y s) = mem x s.
(*  Hypothesis mrfs:
    forall x s, mem x (remove_force x s) = false.
  Hypothesis mrfo:
    forall x y s, x <> y -> mem x (remove_force y s) = mem x s.
  Hypothesis mrfspec:
    forall x y s,
      mem x (remove_force y s) = if x == y then false else mem x s.*)
  Hypothesis mrspec:
    forall x y s,
      mem x (remove y s) = if x == y then false else mem x s.
  Hypothesis remove_1 : forall x s, ~ In x (remove x s).
  Hypothesis remove_2 : forall x y s, x <> y -> In y s -> In y (remove x s).
  Hypothesis remove_3 : forall x s, remove x s [<=] s.

  (* extensional equality *)
  Definition exteq s1 s2 : Prop := s1 ≡ s2.

  Variable bempty: t -> bool.

  Hypothesis bempty_correct: forall s, bempty s = true -> (forall x, ~In x s).

  Definition beq s t := s ≡? t.

  Variable elements: t -> list elt.
  Hypothesis elements_correct:
    forall s x, In x s -> List.In x (elements s).
  Hypothesis elements_1 : forall x s, In x s -> InA eq_elt x (elements s).
  Hypothesis elements_complete:
    forall s x, List.In x (elements s) -> In x s.
  Hypothesis elements_2 :
    forall x s,
      InA eq_elt x (elements s) -> In x s.

  Hypothesis elements_norepet:
  forall s, list_norepet (elements s).


  Variable fold: forall (A: Type), (elt -> A -> A) -> t -> A -> A.


  Hypothesis fold_spec:
    forall (A:Type) (f : elt -> A -> A) s (a : A),
      fold f s a =
        List.fold_left (fun a x => f x a) (elements s) a.
  Definition fold_1 := fold_spec.
  Variable union: t -> t -> t.

  Parameter union_1 : forall s s' x, In x (union s s') -> In x s \/ In x s'.
  Parameter union_2 : forall s s' x, In x s -> In x (union s s').
  Parameter union_3 : forall s s' x, In x s' -> In x (union s s').


  Hypothesis included_trans: forall s2 s1 s3,
    s1 [<=] s2 -> s2 [<=] s3 -> s1 [<=] s3.

  Hypothesis subset_add_2 : forall x s1 s2, s1 [<=] s2 -> s1 [<=] (add x s2).

  Hypothesis subset_refl: forall s, s [<=] s.
  
  Definition for_all f s := List.forallb f (elements s).
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.


  Hypothesis for_all_1 : forall f s,
    For_all (fun x => f x = true) s -> for_all f s = true.


  Hypothesis for_all_2 :
    forall f s,
      for_all f s = true -> For_all (fun x => f x = true) s.

End ISET.

Module PSet <: ISET(PosEqDec).
  Definition elt := positive.
  Definition eq_elt (t1 t2: elt) := t1 = t2.

  Definition t := PTree.t unit.
  Implicit Types x y: positive.
  Implicit Types s: t.


  Definition empty:t := PTree.empty unit.
  Definition mem x s :=
    match PTree.get x s with
      | None => false
      | Some _ => true
    end.

  Definition In x s : Prop :=
    mem x s = true.
  Instance EqA_t : EqA t := {
    eqA := fun s t => (forall x : elt, In x s <-> In x t)}.
  Proof.
    prove_equiv; unfold In; intros; try tauto; dintuition.
    edestruct H; eauto. edestruct H; eauto.
    assert (mem x0 y = true). edestruct H; eauto.
    edestruct H0; eauto.
    assert (mem x0 y = true). edestruct H0; eauto.
    edestruct H; eauto.
  Defined.


  Notation "s [<=] t" := (forall x : elt, In x s -> In x t) (at level 70, no associativity).

  Definition included s t := s [<=] t.

  Lemma mem_1 : forall x s, In x s -> mem x s = true. Proof. auto. Qed.
  Lemma mem_2 : forall x s, mem x s = true -> In x s.  Proof. auto. Qed.

  Definition add x s : t:=
    if mem x s then s else
    PTree.set x tt s.


  Definition remove_force x s : t :=
    PTree.remove_force x s.

  Definition remove x s :=
    if mem x s then remove_force x s else s.

  Hint Unfold In empty mem add remove: pset.
  Hint Rewrite PTree.gempty PTree.gss PTree.gso PTree.grs PTree.gro
    PTree.bempty_correct PTree.elements_complete
    using (auto; congruence): ptree.


  Ltac solve_simpl:=
    repeat match goal with
             | |- context[add ?x ?s] =>
               unfold add; case_eq (mem x s); intro MEM
             | |- _ => intro
           end;
    unfold In, mem, add, remove, remove_force, empty in *; simpl in *;
    autorewrite with ptree in *; simpl in *; auto; try congruence.


  Theorem mempty:
    forall x, ~ In x empty.
  Proof.
    solve_simpl.
  Qed.

  Theorem mempty_false:
    forall x, mem x empty = false.
  Proof.
    solve_simpl.
  Qed.

  Theorem mas:
    forall x s, In x (add x s).
  Proof.
    solve_simpl.
  Qed.

  Definition add_1 := mas.

  Theorem mao:
    forall x y s, x <> y -> mem x (add y s) = mem x s.
  Proof.
    solve_simpl.
  Qed.

  Theorem add_2:
    forall y s, s [<=] add y s.
  Proof.
    solve_simpl.
    dest x == y. subst. rewrite H in MEM. inv MEM.
    solve_simpl.
  Qed.
  Theorem add_3:
    forall x y s, x <> y -> In y (add x s) -> In y s.
  Proof.
    solve_simpl.
  Qed.

  Theorem add_iff :
    forall x y s,
      In y (add x s) <-> x = y \/ In y s.
  Proof.
    intros x y s. split; intro.
    destruct (x == y).
    auto.
    right. eapply add_3; eauto. 
    destruct H. subst. apply mas.
    apply add_2; auto.
  Qed.

  Lemma not_mem_iff :forall x s,  ~In x s <-> mem x s = false.
  Proof.
    intros. unfold In. split; intro H;
    destruct (mem x s); congruence.
  Qed.

  Hint Resolve mempty mas mao: pset.

  Theorem maspec:
    forall x y s,
      mem x (add y s) = if x == y then true else mem x s.
  Proof.
    intros x y s.
    destruct (x == y); subst; auto with pset. apply mas.
  Qed.


  Theorem maident:
    forall x s, In x s -> add x s = s.
  Proof.
    solve_simpl.
  Qed.


  Lemma rfempty: forall x, remove_force x empty = empty.
  Proof.
    unfold remove_force; intros. unfold empty.
    unfold PTree.remove_force, PTree.empty.
    destruct x; reflexivity.
  Qed.

  Lemma rempty: forall x, remove x empty = empty.
  Proof.
    unfold remove. intro x. rewrite mempty_false. reflexivity.
  Qed.


  Theorem mrfs:
    forall x s, mem x (remove_force x s) = false.
  Proof.
    unfold remove_force. unfold mem. 
    intros x s. rewrite PTree.remove_force_same.
    solve_simpl.
  Qed.

  Theorem mrs:
    forall x s, mem x (remove x s) = false.
  Proof.
    unfold remove. intros x s.
    case_eq (mem x s); intro MEM; try congruence.
    apply mrfs.
  Qed.

  Theorem mrfo:
    forall x y s, x <> y -> mem x (remove_force y s) = mem x s.
  Proof.
    intros x y s H. unfold remove_force, mem.
    rewrite PTree.remove_force_same.
    solve_simpl. 
  Qed.


  Theorem mro:
    forall x y s, x <> y -> mem x (remove y s) = mem x s.
  Proof.
    unfold remove; intros.
    case_eq (mem y s); intro MEM; auto.
    apply mrfo. auto.
  Qed.

  Hint Resolve maspec maident rempty mrs mro mrfo mrfs: pset.
  Lemma mrfspec:
    forall x y s,
      mem x (remove_force y s) = if x == y then false else mem x s.
  Proof.
    intros.
    destruct (x == y); subst; auto with pset.
  Qed.

  Theorem mrspec:
    forall x y s,
      mem x (remove y s) = if x == y then false else mem x s.
  Proof.
    intros.
    destruct (x == y); subst; auto with pset.
  Qed.

  Lemma remove_1 : forall x s, ~ In x (remove x s).
  Proof.
    intros x s. unfold In. rewrite mrs. auto.
  Qed.

  Lemma remove_2 : forall x y s, x <> y -> In y s -> In y (remove x s).
  Proof.
    unfold In.
    intros x y s H H0. rewrite mro; auto.
  Qed.


  Lemma remove_3 : forall x s, remove x s [<=] s.
  Proof.
    unfold In.
    intros x s y H.
    erewrite mro in H; eauto.
    intro. subst.
    rewrite mrs in H. inv H.

  Qed.


  (* extensional equality *)

  Definition exteq s1 s2 : Prop := s1 ≡ s2.

  Definition bempty s := PTree.bempty s.

  Lemma bempty_correct: forall s, bempty s = true ->
    (forall x, ~In x s).
  Proof.
    solve_simpl.
  Qed.

  Section EQDEC.
    Instance EqA_unit: EqA unit :=
    {eqA := @Logic.eq _}.

    Instance EqADec_unit: EqADec unit.
    Proof.
      constructor.
      intros.
      left. unfold eqA. simpl. destruct x; destruct y; auto.
    Defined.

    Global Instance EqASDec_t : EqASDec t.
    Proof.
      constructor.
      intros x y.

      dest x ≡? y.
      left.
      unfold eqA in *. simpl in *.
      intros x0.
      unfold PTree.exteq in EQ. specialize (EQ x0).
      unfold In, mem.
      split;
      destruct (x ! x0); destruct (y ! x0); auto.
      right; auto.
    Defined.

    Definition beq s1 s2 := s1 ≡? s2.



    (*  Definition const_true (_ _:X.t) := true.
       Definition beq_t_ : t_ -> t_ -> bool := PTree.beq const_true.
       Definition beq_aux t1 t2 := beq_t_ t1.(m) t2.(m).*)

(*  Lemma beq_aux_correct:
    forall s1 s2, beq_aux s1 s2 = true -> exteq s1 s2.
  Proof.
    unfold beq_aux, exteq, beq_t_, In, mem.
    intros s1 s2 HBEQ. 
    destruct s1 as [s1 CORR1].
    destruct s2 as [s2 CORR2].
    simpl in *.
    intros x.
    pose proof (@PTree.beq_correct elt (fun _ _ => True) const_true) as BC.
    unfold PTree.exteq in BC.
    assert (forall x y : elt, const_true x y = true -> True) as TRIV by auto.
    specialize (BC TRIV s1 s2 HBEQ (X.index x)). clear TRIV.
    case_eq (s1 ! (X.index x)); case_eq (s2 ! (X.index x)); intros; rewrite H in *;
      rewrite H0 in *; tauto.
  Qed.

  Lemma beq: semi_decidable2 exteq.
  Proof. unfold semi_decidable2, semi_decidable.
    intros t1 t2.
    case_eq (beq_aux t1 t2); intro BEQ.
    left. apply beq_aux_correct. trivial.
    right. apply I.
  Qed.
*)

  Definition elements s:= List.map fst (PTree.elements s).

  Theorem elements_correct:
    forall s x, In x s -> List.In x (elements s).
  Proof.
    unfold elements.
    unfold In, mem.
    intros s x IN.
    assert (s ! x = Some tt).
    destruct (s ! x). destruct u; reflexivity. inv IN.
    pose proof (PTree.elements_correct _ _ H).
    replace x with (fst (x, tt)); auto.
    apply List.in_map. auto.
  Qed.

  Theorem elements_complete:
    forall s x, List.In x (elements s) -> In x s.
  Proof.
    unfold elements.
    unfold In, mem.
    intros s x IN.
    replace x with (fst (x, tt)) in IN by auto.
    rewrite PTree.elements_complete with (v := tt). reflexivity.
    rewrite List.in_map_iff in IN.
    destruct IN as [[a b] [? ?]].
    destruct b. simpl in H. subst. auto.
  Qed.

  Theorem elements_norepet:
    forall s, list_norepet (elements s).
  Proof.
    unfold elements. apply PTree.elements_keys_norepet.
  Qed.

  Lemma elements_1 :  forall x s, In x s -> InA eq_elt x (elements s).
  Proof.
    intros x s H. apply In_InA. unfold eq_elt. dintuition congruence.

    apply elements_correct. auto.
  Qed.

  Lemma elements_2 :
    forall x s,
      InA eq_elt x (elements s) -> In x s.
  Proof.
    unfold eq_elt.
    intros x s H. apply elements_complete.
    rewrite InA_alt in H.
    destruct H as [j [? ?]].
    subst. auto.
  Qed.

  Definition f_union :=
    fun (oa ob: option unit) =>
      match oa, ob with
        | None,  None => None
        | Some x, _
        | None, Some x=> Some x
      end.

  Program Definition union (m1 m2: t) :=
    PTree.combine_eqdec f_union m1 m2.

  Lemma union_1 : forall s s' x, In x (union s s') -> In x s \/ In x s'.
  Proof.
    assert (f_union None None = None) as fNNN by reflexivity.
    unfold union, In, mem.
    intros s s' x H.
    pose proof (PTree.gcombine_eqdec f_union fNNN s s' x).
    destruct ((PTree.combine_eqdec f_union s s') ! x); try congruence.
    destruct (s ! x); destruct (s' ! x); simpl in H0; auto.
  Qed.

  Lemma union_2 : forall s s' x, In x s -> In x (union s s').
  Proof.
    assert (f_union None None = None) as fNNN by reflexivity.
    unfold union, In, mem.
    intros s s' x H.
    pose proof (PTree.gcombine_eqdec f_union fNNN s s' x).
    destruct ((PTree.combine_eqdec f_union s s') ! x); try congruence.
    destruct (s ! x); destruct (s' ! x); simpl in H0; auto.
  Qed.
  Lemma union_3 : forall s s' x, In x s' -> In x (union s s').
  Proof.
    assert (f_union None None = None) as fNNN by reflexivity.
    unfold union, In, mem.
    intros s s' x H.
    pose proof (PTree.gcombine_eqdec f_union fNNN s s' x).
    destruct ((PTree.combine_eqdec f_union s s') ! x); try congruence.
    destruct (s ! x); destruct (s' ! x); simpl in H0; auto.
  Qed.


  End EQDEC.


  (*Proof.
     apply PTree.elements_keys_norepet.
     Qed.*)

  Definition fold (A:Type) (f : elt -> A -> A) s (a : A) :=
    PTree.fold (fun a' x _ => f x a') s a.

  Theorem fold_spec:
    forall (A:Type) (f : elt -> A -> A) s (a : A),
      fold f s a =
        List.fold_left (fun a x => f x a) (elements s) a.
  Proof.
    intros. unfold fold, elements.
    rewrite PTree.fold_spec. unfold elt in *.
    remember (@PTree.elements unit s) as elts. clear Heqelts.
    generalize dependent a.
    induction elts; intros; simpl; auto.
  Qed.

  Definition fold_1 := fold_spec.





  Lemma included_trans: forall s2 s1 s3,
    s1 [<=] s2 -> s2 [<=] s3 -> s1 [<=] s3.
  Proof.
    unfold In. auto.
  Qed.

  Lemma subset_add_2 : forall x s1 s2,  s1 [<=] s2 -> s1 [<=] (add x s2).
  Proof.
    unfold included, In.
    intros x s1 s2 H.
    intros i0 H0.
    dest i0 == x; subst.
    apply mas.
    rewrite mao; auto.
  Qed.

  Lemma subset_refl: forall s, s [<=] s.
  Proof. auto. Qed.

  Definition for_all f s := List.forallb f (elements s).
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.


  Lemma for_all_1 : forall f s,
    For_all (fun x => f x = true) s -> for_all f s = true.
  Proof.
    unfold for_all, For_all.
    intros f s FORALL.
    rewrite forallb_forall.
    intros x IN. apply elements_complete in IN. auto.
  Qed.


  Lemma for_all_2 :
    forall f s,
      for_all f s = true -> For_all (fun x => f x = true) s.
    unfold for_all, For_all.
    intros f s FORALL.
    rewrite forallb_forall in FORALL.
    intros x IN. apply elements_correct in IN. auto.
  Qed.

End PSet.
(*
Module Indexed_Pos <: INDEXED_TYPE.
  Definition t := positive.
  Definition index (p:t) := p.
  Lemma index_inj
    : forall (x y: t), index x = index y -> x = y.
  Proof. auto. Qed.
  Definition eq := peq.
End Indexed_Pos.

Module PSet := ISet(Indexed_Pos).

Module PosPair (IS:ISET) <: ISET with Definition elt := (positive * IS.elt)%type.
  Definition elt := (positive * IS.elt)%type.
  Definition eq_elt := @Logic.eq elt.
  Lemma deq_elt: forall e1 e2: elt, decidable (e1 = e2).
  Proof.
    intros. unfold decidable.
    decide equality.
    apply IS.deq_elt.
    apply peq.
  Qed.

  Notation "x == y" := (deq_elt x y) (at level 70, no associativity).

  Definition t := (PTree.t IS.t).

  Implicit Types x y: elt.
  Implicit Types s: t.

  Definition empty: t := PTree.empty _.

  Definition mem (x: elt) (s:t) :=
    match PTree.get (fst x) s with
      | None => false
      | Some s' => IS.mem (snd x) s'
    end.

  Definition In x s : Prop :=
    mem x s = true.

  Notation "s [=] t" := (forall x : elt, In x s <-> In x t) (at level 70, no associativity).
  Notation "s [<=] t" := (forall x : elt, In x s -> In x t) (at level 70, no associativity).

  Definition included s t := s [<=] t.

  Lemma mem_1 : forall x s, In x s -> mem x s = true. Proof. auto. Qed.
  Lemma mem_2 : forall x s, mem x s = true -> In x s. Proof. auto. Qed.

  Definition add (x:elt) (s:t) :=
    match PTree.get (fst x) s with
      | None => PTree.set (fst x) (IS.add (snd x) IS.empty) s
      | Some s' =>
        if IS.mem (snd x) s' then s else
          PTree.set (fst x) (IS.add (snd x) s') s
    end.

  Definition remove x s :=
    match PTree.get (fst x) s with
      | None => s
      | Some s' =>
        if IS.mem (snd x) s' then
          let s'' := IS.remove (snd x) s' in
          if IS.bempty s'' then
            PTree.remove (fst x)  s
          else
            PTree.set (fst x) s'' s
        else
          s
    end.

  Hint Unfold In empty mem add remove: pset.
  Hint Rewrite PTree.gempty PTree.gss PTree.gso PTree.grs PTree.gro PTree.grfs PTree.grfo
    PTree.bempty_correct PTree.elements_complete
    using (auto; congruence): ptree.


  Ltac solve_simpl:=
    repeat match goal with
             | |- context[add ?x ?s] =>
               unfold add; case_eq (mem x s); intro MEM
             | |- _ => intro
           end;
    unfold In, mem, add, remove, empty in *; simpl in *;
    autorewrite with ptree in *; simpl in *;
      eauto using IS.mempty, IS.mas, IS.add_1, IS.mao, IS.add_2, IS.add_3; try congruence.

  Lemma mempty:
    forall x, ~ In x empty.
  Proof.
    solve_simpl.
  Qed.


  Axiom mas:
    forall x s, In x (add x s).


  Axiom add_1:
    forall x s, In x (add x s).
  Axiom mao:
    forall x y s, x <> y -> mem x (add y s) = mem x s.
  Axiom add_2: forall y s, s [<=] add y s.
  Axiom add_3:
    forall x y s, x <> y -> In y (add x s) -> In y s.
  Axiom add_iff :
    forall x y s,
      In y (add x s) <-> x = y \/ In y s.
  Axiom not_mem_iff :forall x s,  ~In x s <-> mem x s = false.
  Axiom maspec:
    forall x y s,
      mem x (add y s) = if x == y then true else mem x s.

  Axiom maident:
    forall x s, In x s -> add x s = s.

  Axiom rempty: forall x, remove x empty = empty.
(*  Axiom rfempty: forall x, remove_force x empty = empty.*)
  Axiom mrs:
    forall x s, mem x (remove x s) = false.


  Axiom mro:
    forall x y s, x <> y -> mem x (remove y s) = mem x s.
(*  Axiom mrfs:
    forall x s, mem x (remove_force x s) = false.
  Axiom mrfo:
    forall x y s, x <> y -> mem x (remove_force y s) = mem x s.
  Axiom mrfspec:
    forall x y s,
      mem x (remove_force y s) = if x == y then false else mem x s.*)
  Axiom mrspec:
    forall x y s,
      mem x (remove y s) = if x == y then false else mem x s.
  Axiom remove_1 : forall x s, ~ In x (remove x s).
  Axiom remove_2 : forall x y s, x <> y -> In y s -> In y (remove x s).
  Axiom remove_3 : forall x s, remove x s [<=] s.

  (* extensional equality *)
  Definition exteq s1 s2 : Prop := s1 [=] s2.

  Definition bempty s := PTree.bempty s.



  Axiom bempty_correct: forall s, bempty s = true -> (forall x, ~In x s).

  Definition beq_b s1 s2 :=
    PTree.beq IS.beq s1 s2.

  Lemma beq: semi_decidable2 exteq.
  Proof.
    unfold semi_decidable2.
    intros s1 s2. case_eq (beq_b s1 s2); intro BEQ.
    unfold beq_b in BEQ.
    assert (forall ss1 ss2, (if IS.beq ss1 ss2 then true else false) = true -> IS.exteq ss1 ss2).
    intros ss1 ss2 H. destruct (IS.beq ss1 ss2). auto. inv H.
    pose proof (PTree.beq_correct IS.exteq _ H _ _ BEQ) as BEQ_CORR.

    unfold PTree.exteq in BEQ_CORR.

    left. unfold exteq. unfold In. unfold mem. intros [a b]. simpl.
    specialize (BEQ_CORR a). unfold IS.exteq in BEQ_CORR. unfold IS.In in BEQ_CORR.
    destruct (s1 ! a); destruct (s2!a); auto; try solve [inv BEQ_CORR]. dintuition.
    right; auto.
  Qed.



  Notation "s [?=] t" := (beq s t) (at level 70, no associativity).

  Definition elements s :=
    List.fold_right
      (fun pss l =>
        let '(p, ss) := pss in
        (List.map (fun e => (p, e)) (IS.elements ss)) ++ l) nil (PTree.elements s).

  Axiom elements_correct:
    forall s x, In x s -> List.In x (elements s).
  Axiom elements_1 : forall x s, In x s -> InA eq_elt x (elements s).
  Axiom elements_complete:
    forall s x, List.In x (elements s) -> In x s.
  Axiom elements_2 :
    forall x s,
      InA eq_elt x (elements s) -> In x s.

  Axiom elements_norepet:
  forall s, list_norepet (elements s).

  Definition fold (A:Type) (f: elt -> A -> A) s a :=
    PTree.fold (fun acc p ss =>
      IS.fold (fun e acc' => f (p, e) acc') ss acc) s a.

  Axiom fold_spec:
    forall (A:Type) (f : elt -> A -> A) s (a : A),
      fold f s a =
        List.fold_left (fun a x => f x a) (elements s) a.
  Definition fold_1 := fold_spec.

  Definition union s1 s2 :=
    PTree.combine_eq_dec IS.exteq IS.beq
    (fun oss1 oss2 =>
      match oss1, oss2 with
        | None, None => None
        | Some ss, None
        | None, Some ss => Some ss
        | Some ss1, Some ss2 => Some (IS.union ss1 ss2)
      end) s1 s2.

  Axiom included_trans: forall s2 s1 s3,
    s1 [<=] s2 -> s2 [<=] s3 -> s1 [<=] s3.

  Axiom subset_add_2 : forall x s1 s2, s1 [<=] s2 -> s1 [<=] (add x s2).

  Axiom subset_refl: forall s, s [<=] s.
  
  Definition for_all f s := List.forallb f (elements s).
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.


  Axiom for_all_1 : forall f s,
    For_all (fun x => f x = true) s -> for_all f s = true.


  Axiom for_all_2 :
    forall f s,
      for_all f s = true -> For_all (fun x => f x = true) s.

End PosPair.



(*Module IndexedPair (IT1:INDEXED_TYPE)(IT2:INDEXED_TYPE).
  Definition t := (IT1.t * IT2.t)%type.
  Fixpoint prep_concat p1 p2 :=
    match p1 with
      | xH => xO (xO p2)
      | (xO p1') => xO (xI (prep_concat p1' p2))
      | (xI p1') => xI (prep_concat p1' p2)
    end.
  Definition index (p:t) :=
    let '(x1, x2) := p in
    prep_concat (IT2.index x2) (IT1.index x1).

  Lemma eq: forall (p1 p2:t), {p1 = p2}+{p1 <> p2}.
  Proof.
    intros. decide equality. apply IT2.eq. apply IT1.eq.
  Qed.

  Lemma prep_concat_correct: forall i1 j1 i2 j2,
    prep_concat i1 j1 = prep_concat i2 j2 ->
    i1 = i2 /\ j1 = j2.
  Proof.
    induction i1; simpl; intros j1 i2 j2 HEQ.
    destruct i2; simpl in HEQ; try congruence.
    inv HEQ.  destruct (IHi1 _ _ _ H0). split; congruence.
    destruct i2; simpl in HEQ; try congruence.
    inv HEQ.  destruct (IHi1 _ _ _ H0). split; congruence.
    destruct i2; simpl in HEQ; try congruence.
    inv HEQ. split; congruence.
  Qed.
    

  Lemma index_inj:
    forall p1 p2, index p1 = index p2 -> p1 = p2.
  Proof.
    intros [x1 y1] [x2 y2] HEQ.
    unfold index in HEQ.
    pose proof (prep_concat_correct _ _ _ _ HEQ).
    destruct H. apply IT2.index_inj in H. apply IT1.index_inj in H0.
    congruence.
  Qed.
End IndexedPair.*)*)


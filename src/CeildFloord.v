Require Import Coqlibext.
Require Import Do_notation.
Require Import ClassesAndNotations.
Require Import Psatz.
Require Import Program.
Require Import Zhints.
Hint Resolve Zgt_pos_0.
Hint Resolve Zle_0_pos.

Definition ceild (n:Z) (d:positive) : Z :=
  let d' := Zpos d in
  if zlt n 0 then
    - ((- n)/d')
  else
    (n + d' - 1) / d'.

Lemma ceild_prop:
  forall n d, let d' := Zpos d in
    n <= (ceild n d) * d' < n + d'.
Proof.
  intros n d d'.
  assert (d' > 0).
  subst d'; auto.

  unfold ceild. subst d'. destruct (zlt n 0);

  match goal with
    | H: ?Y > 0 |- context[?X / ?Y] =>
      pose proof (Z_div_mod X Y H)
  end; unfold Zdiv;
  match goal with
    | |- context[Zdiv_eucl ?X ?Y] => destruct (Zdiv_eucl X Y)
  end;
  lia.
Qed.


Lemma unicity_in_bounding_le_l:
  forall n d x1 x2, d > 0 ->
    n <= x1 * d < n + d ->
    n <= x2 * d < n + d ->
    x1 = x2.
Proof.
  intros n d x1 x2 H H0 H1.
  destruct (Ztrichotomy_inf x1 x2) as [[? | ?]|  ?]; auto; elimtype False.

  assert (x1 + 1 <= x2) by lia.
  assert ((x1 + 1) * d <= x2 * d).
  apply Zmult_le_compat_r; lia. lia.

  assert (x2 + 1 <= x1) by lia.
  assert ((x2 + 1) * d <= x1 * d).
  apply Zmult_le_compat_r; lia. lia.
Qed.



Lemma ceild_unique:
  forall n d x, let d' := Zpos d in
    n <= x * d' < n + d' -> x = ceild n d.
Proof.
  intros n d x d' H. subst d'.
  pose proof (ceild_prop n d). simpl in H0.
  eapply unicity_in_bounding_le_l; eauto.
Qed.



Definition floord (n:Z) (d:positive) : Z :=
  let d' := Zpos d in
  if zlt n 0 then
    - ((d' - n - 1) / d')
  else
    n / d'.

Lemma floord_prop:
  forall n d, let d' := Zpos d in
    n - d' < (floord n d) * d' <= n.
Proof.
  intros n d d'.
  assert (d' > 0).
  subst d'; auto.

  unfold floord. subst d'. destruct (zlt n 0);

  match goal with
    | H: ?Y > 0 |- context[?X / ?Y] =>
      pose proof (Z_div_mod X Y H)
  end; unfold Zdiv;
  match goal with
    | |- context[Zdiv_eucl ?X ?Y] => destruct (Zdiv_eucl X Y)
  end; lia.
Qed.


Lemma unicity_in_bounding_lt_le:
  forall n d x1 x2, d > 0 ->
    n - d < x1 * d <= n ->
    n - d < x2 * d <= n ->
    x1 = x2.
Proof.
  intros n d x1 x2 H H0 H1.
  destruct (Ztrichotomy_inf x1 x2) as [[? | ?]|  ?]; auto; elimtype False.

  assert (x1 + 1 <= x2) by lia.
  assert ((x1 + 1) * d <= x2 * d).
  apply Zmult_le_compat_r; lia. lia.

  assert (x2 + 1 <= x1) by lia.
  assert ((x2 + 1) * d <= x1 * d).
  apply Zmult_le_compat_r; lia. lia.
Qed.



Lemma floord_unique:
  forall n d x, let d' := Zpos d in
    n - d' < x * d' <= n -> x = floord n d.
Proof.
  intros n d x d' H. subst d'.
  pose proof (floord_prop n d). simpl in H0.
  eapply unicity_in_bounding_lt_le; eauto.
Qed.



Definition ceildZ (n d: Z): option Z :=
  match d with
    | Zpos d' => Some (ceild n d')
    | _ => None
  end.

Lemma ceildZ_pos n d: d > 0 -> is_some (ceildZ n d).
Proof.
  intro POS.
  destruct d; simpl in *; auto.
  lia.
  unfold Zgt in POS. simpl in POS. inversion POS.
Qed.

Lemma ceildZ_bound1 d x n c:
  ceildZ n d = Some c -> n <= d * x ->
  c <= x.
Proof.
  intros FLOOR LEQ.
  destruct d as [ | d' | d']; try solve [simpl in *; clean].

  simpl in FLOOR. clean.
  destruct (Z_le_gt_dec (ceild n d') x); auto.
  elimtype False.
  pose proof (ceild_prop n d').
  simpl in H.
  apply (Zmult_gt_compat_r _ _ (Zpos d')) in z; try reflexivity.
  destruct H.

  assert (x = ceild n d'). apply ceild_unique. lia. subst. lia.
Qed.

Lemma ceildZ_bound2 d x n c:
  ceildZ n d = Some c ->
  c <= x -> n <= d * x.
Proof.
  intros FLOOR LEQ.
  destruct d as [ | d' | d']; try solve [simpl in *; clean].

  simpl in FLOOR. clean.
  destruct (Z_le_gt_dec n (Zpos d' * x)); auto.
  elimtype False.

  pose proof (ceild_prop n d').
  simpl in H.
  destruct H.
  apply (Zmult_le_compat_r _ _ (Zpos d')) in LEQ; auto. lia.
Qed.

Definition floordZ (n d:Z) : option Z :=
  match d with
    | Zpos d' => Some (floord n d')
    | _ => None
  end.

Lemma floordZ_pos n d: d > 0 -> is_some (floordZ n d).
Proof.
  intro POS.
  destruct d; simpl in *; auto.
  lia.
  unfold Zgt in POS. simpl in POS. inversion POS.
Qed.


Lemma floordZ_bound1 d x n f:
  floordZ n d = Some f -> d * x <= n ->
  x <= f.
Proof.
  intros FLOOR LEQ.
  destruct d as [ | d' | d']; try solve [simpl in *; clean].

  simpl in FLOOR. clean.
  destruct (Z_le_gt_dec x (floord n d')); auto.
  elimtype False.
  pose proof (floord_prop n d').
  simpl in H.
  apply (Zmult_gt_compat_r _ _ (Zpos d')) in z; try reflexivity.
  destruct H.

  assert (x = floord n d'). apply floord_unique. lia. subst. lia.
Qed.

Lemma floordZ_bound2 d x n f:
  floordZ n d = Some f ->
  x <= f -> d * x <= n.
Proof.
  intros FLOOR LEQ.
  destruct d as [ | d' | d']; try solve [simpl in *; clean].

  simpl in FLOOR. clean.
  destruct (Z_le_gt_dec (Zpos d' * x) n); auto.
  elimtype False.

  pose proof (floord_prop n d').
  simpl in H.
  destruct H.
  apply (Zmult_le_compat_r _ _ (Zpos d')) in LEQ; auto. lia.
Qed.
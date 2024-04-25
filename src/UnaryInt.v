(* begin hide *)
From Coq Require Import
  ZArith
  Arith.PeanoNat
  Logic.FunctionalExtensionality
  Lists.List
  Lia.

From Heapster Require Import
  Utils
  Permissions
  SepStep.

From ITree Require Import
  ITree
  Events.Exception.

From Paco Require Import
  paco.

Import ListNotations.
Import ITreeNotations.

Local Open Scope itree_scope.
(* end hide *)

Section IntPerms.
  Program Definition up_perm (b : Z) : @perm Z :=
    {|
      rely := Z.le;
      guar := Z.le;
      pre x := (b <= x)%Z;
    |}.
  Next Obligation.
    etransitivity; eauto.
  Qed.

  Program Definition updown_perm (b : Z) : perm :=
    {|
      rely := Z.le;
      guar _ _ := True;
      pre x := (b <= x)%Z;
    |}.
  Next Obligation.
    split; repeat intro; auto.
  Qed.
  Next Obligation.
    etransitivity; eauto.
  Qed.

  Program Definition ex_updown_perm (b : Z) : perm :=
    {|
      rely := eq;
      guar _ _ := True;
      pre x := b = x;
    |}.
  Next Obligation.
    split; repeat intro; auto.
  Qed.

  Lemma lte_updown_up_perm b :
    updown_perm b <= up_perm b.
  Proof.
    split; cbn; auto.
  Qed.

  Lemma lte_ex_updown_perm b :
    ex_updown_perm b <= updown_perm b.
  Proof.
    split; cbn; intros; subst; auto; reflexivity.
  Qed.

  Definition up_Perms_b (b : Z) : Perms :=
    singleton_Perms (up_perm b).
  Definition up_Perms : Perms :=
    join_Perms (fun P => exists b, P = up_Perms_b b).

  Definition updown_Perms_b (b : Z) : Perms :=
    singleton_Perms (updown_perm b).
  Definition updown_Perms : Perms :=
    join_Perms (fun P => exists b, P = updown_Perms_b b).

  Definition ex_updown_Perms_b (b : Z) : Perms :=
    singleton_Perms (ex_updown_perm b).
  Definition ex_updown_Perms : Perms :=
    join_Perms (fun P => exists b, P = ex_updown_Perms_b b).

  Lemma lte_updown_up_Perms :
    updown_Perms ⊑ up_Perms.
  Proof.
    intros p (P & (b & ?) & Hp). subst.
    cbn. exists (up_Perms_b b). split.
    exists b. reflexivity.
    cbn in *. etransitivity; eauto. apply lte_updown_up_perm.
  Qed.

  Lemma lte_ex_updown_Perms :
    ex_updown_Perms ⊑ updown_Perms.
  Proof.
    intros p (P & (b & ?) & Hp). subst.
    cbn. exists (updown_Perms_b b). split.
    exists b. reflexivity.
    cbn in *. etransitivity; eauto. apply lte_ex_updown_perm.
  Qed.

  Variant E : Type -> Type :=
    | Load : E Z
    | Store : forall (z : Z), E unit
  .

  Variant step {R} : itree E R -> Z -> itree E R -> Z -> Prop :=
    | step_tau : forall t c, step (Tau t) c t c
    | step_load : forall k c, step (vis Load k) c (k c) c
    | step_store : forall k c c', step (vis (Store c') k) c (k tt) c'
  .

  Variant typing_gen {R} typing (P : Perms) (Q : R -> Perms) : itree E R -> Prop :=
  | cond : forall t, (exists c t' c', step t c t' c') /\ (* we can step *)
                (forall p c, p ∈ P ->
                        pre p c ->
                        forall t' c',
                          step t c t' c' -> (* and everything we can step to... *)
                          (
                            (* we step to configs that satisfy the perm *)
                            guar p c c' /\
                            (* we step to machines that are well-typed by some other perm that maintains separation *)
                            exists P', typing P' Q t' /\ exists p', p' ∈ P' /\ sep_step p p' /\ pre p' c')) ->
                typing_gen typing P Q t
  | ret : forall r, Q r ⊑ P -> typing_gen typing P Q (Ret r).

  (* Definition typing_perm := paco3 typing_perm_gen bot3. *)
  Definition typing {R} := paco3 (@typing_gen R) bot3.

End IntPerms.

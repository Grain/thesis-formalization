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
  Events.Exception
  Eq
  Eq.EqAxiom.

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

  Example lte_updown_up_perm b :
    updown_perm b <= up_perm b.
  Proof.
    split; cbn; auto.
  Qed.

  Example lte_ex_updown_perm b :
    ex_updown_perm b <= updown_perm b.
  Proof.
    split; cbn; intros; subst; auto; reflexivity.
  Qed.

  Example up_perm_sep b b' :
    up_perm b ⊥ up_perm b'.
  Proof.
    split; intros; auto.
  Qed.

  Example up_perm_ex_updown_perm_not_sep b b' :
    up_perm b ⊥ ex_updown_perm b' -> False.
  Proof.
    intros. destruct H. cbn in *.
    specialize (sep_r (Z.of_nat 0) (Z.of_nat 1)).
    lia.
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

  Example up_Perms_ex_updown_Perms_sep_conj :
    up_Perms * ex_updown_Perms ≡ bottom_Perms.
  Proof.
    split; repeat intro.
    - destruct H as (? & ? & (? & (? & ?) & ?) & (? & (? & ?) & ?) & ? & ?). subst.
      cbn in *.
      eapply up_perm_ex_updown_perm_not_sep.
      eapply separate_upwards_closed; eauto.
      symmetry.
      eapply separate_upwards_closed; eauto. symmetry. auto.
    - inversion H.
  Qed.

  Example lte_updown_up_Perms :
    updown_Perms ⊑ up_Perms.
  Proof.
    intros p (P & (b & ?) & Hp). subst.
    cbn. exists (up_Perms_b b). split.
    exists b. reflexivity.
    cbn in *. etransitivity; eauto. apply lte_updown_up_perm.
  Qed.

  Example lte_ex_updown_Perms :
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
  Lemma step_bind {R1 R2} : forall (t1 t2 : itree E R1) (c1 c2 : Z) (k : R1 -> itree E R2),
      step t1 c1 t2 c2 ->
      step (t1 >>= k) c1 (t2 >>= k) c2.
  Proof.
    intros. inversion H; subst.
    - rewritebisim @bind_tau. constructor.
    - rewritebisim @bind_vis. constructor; auto.
    - rewritebisim @bind_vis. constructor; auto.
  Qed.

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
    | ret : forall r, P ⊑ Q r -> typing_gen typing P Q (Ret r).

  Lemma typing_gen_mon {R} : monotone3 (@typing_gen R).
  Proof.
    repeat intro.
    inversion IN; subst.
    - econstructor. destruct H. split; auto.
      intros. edestruct H0; eauto. split; eauto.
      destruct H5 as (? & ? & (? & ? & ? & ?)). eexists. split; eauto.
    - constructor 2; auto.
  Qed.
  Hint Resolve typing_gen_mon : paco.

  Definition typing {R} := paco3 (@typing_gen R) bot3.

  Example typing_ex_updown :
    typing ex_updown_Perms (fun _ => ex_updown_Perms_b (Z.of_nat 1)) (trigger (Store (Z.of_nat 1))).
  Proof.
    pstep. constructor 1. split.
    { exists (Z.of_nat 0), (Ret tt), (Z.of_nat 1). constructor. }
    intros p c (? & (b & ?) & Hp) Hpre t' c' Hstep.
    inversion Hstep; subst. apply Eqdep.EqdepTheory.inj_pair2 in H2. subst. split.
    - apply Hp. cbn. auto.
    - exists (ex_updown_Perms_b (Z.of_nat 1)). split.
      + left. pstep. constructor 2. reflexivity.
      + exists (ex_updown_perm (Z.of_nat 1)). split; [| split]; cbn; auto. reflexivity.
        eapply sep_step_lte. apply Hp.
        apply sep_step_rg; intros; auto.
  Qed.

  Lemma rewrite_spin {R} : (ITree.spin : itree E R) = Tau (ITree.spin).
  Proof.
    intros. apply bisimulation_is_eq.
    ginit. gcofix CIH. gstep. unfold ITree.spin. constructor.
    apply Reflexive_eqit_gen_eq.
  Qed.
  Example typing_spin {R} : forall P Q, typing P Q (ITree.spin : itree E R).
  Proof.
    pcofix CIH. intros. pstep. constructor 1. split.
    - exists (Z.of_nat 0). eexists. exists (Z.of_nat 0). rewrite rewrite_spin. constructor.
    - intros. rewrite rewrite_spin in H1. inversion H1; subst; split; intuition.
      exists P. split.
      + right. auto.
      + exists p; split; [| split]; intuition.
  Qed.

  Lemma typing_bottom_step {R} : forall Q (t : itree E R), (exists c t' c', step t c t' c') -> typing bottom_Perms Q t.
  Proof.
    intros. pstep. constructor. split; auto. inversion 1.
  Qed.

  Lemma typing_lte {R} : forall P P' Q Q' (t : itree E R),
      typing P Q t ->
      P' ⊑ P ->
      (forall r, Q r ⊑ Q' r) ->
      typing P' Q' t.
  Proof.
    pcofix CIH. intros. pstep. pinversion H0; subst.
    - constructor 1. destruct H. split; auto. intros.
      edestruct H3; eauto. split; auto.
      destruct H8 as (? & ? & (? & ? & ? & ?)). pclearbot.
      eexists; split.
      + right. eapply CIH; eauto. reflexivity.
      + eexists. split; [| split]; eauto.
    - constructor 2. etransitivity; eauto. etransitivity; eauto.
  Qed.

  Lemma typing_bind {R1 R2} : forall P Q R (t : itree E R1) (k : R1 -> itree E R2),
      typing P Q t ->
      (forall r1, typing (Q r1) R (k r1)) ->
      typing P R (x <- t;; k x).
  Proof.
    pcofix CIH. intros. pinversion H0; subst.
    - destruct H as ((c & t' & c' & Hstep) & ?). pstep. constructor. split; auto.
      { do 3 eexists. apply step_bind; eauto. }
      intros. inversion H4; subst.
      + pose proof @eqitree_inv_bind_tau.
        edestruct H5 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
          apply bisimulation_is_eq in H7; apply bisimulation_is_eq in H8; subst;
          [| inversion Hstep].
        destruct (H _ _ H2 H3 _ _ (step_tau _ _)) as (? & P' & ? & (p' & ? & ? & ?)).
        pclearbot. split; auto. exists P'. split; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H5 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
          apply bisimulation_is_eq in H7; subst; [| inversion Hstep].
        rewritebisim_in @bind_vis H6. inversion H6. apply Eqdep.EqdepTheory.inj_pair2 in H9; subst.
        destruct (H _ _ H2 H3 _ _ (step_load _ _)) as (? & P' & ? & (p' & ? & ? & ?)).
        pclearbot. split; auto. exists P'. split; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H5 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
          apply bisimulation_is_eq in H7; subst; [| inversion Hstep].
        rewritebisim_in @bind_vis H6. inversion H6. apply Eqdep.EqdepTheory.inj_pair2 in H9; subst.
        destruct (H _ _ H2 H3 _ _ (step_store _ _ _)) as (? & P' & ? & (p' & ? & ? & ?)).
        pclearbot. split; auto. exists P'. split; eauto.
    - rewritebisim @bind_ret_l. eapply paco3_mon_bot; eauto. eapply typing_lte; eauto.
      reflexivity.
  Qed.

  Lemma typing_perm_frame {R : Type} : forall P Q P' (t : itree E R),
      typing P Q t ->
      typing (P * P') (fun r => Q r * P') t.
  Proof.
    pcofix CIH. intros. pinversion H0; subst.
    - pstep. constructor 1. split.
      { destruct H as ((c & t' & c' & Hstep) & ?).
        do 3 eexists; eauto. }
      destruct H as (_ & H).
      intros pp c (p & p' & Hp & Hp' & Hsep & Hpp) Hpre t' c' Hstep.
      edestruct H; eauto.
      { apply Hpp. apply Hpre. }
      split.
      { apply Hpp. constructor. left. assumption. }
      destruct H2 as (P'' & Ht' & p'' & Hpp' & Hsep_step & Hpre').
      exists (P'' * P'). pclearbot. split; auto.
      exists (p'' ** p'). split; [| split].
      + apply sep_conj_Perms_perm; auto.
      + eapply sep_step_lte; eauto. eapply sep_step_sep_conj_l; auto.
      + split; [| split]; auto.
        apply Hpp in Hpre. destruct Hpre as (? & ? & ?). respects.
        apply H4; auto.
    - pstep. constructor 2. apply sep_conj_Perms_monotone; intuition.
  Qed.

End IntPerms.

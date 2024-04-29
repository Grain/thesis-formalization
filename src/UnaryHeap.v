(* begin hide *)
From Coq Require Import
  Arith.PeanoNat
  Logic.FunctionalExtensionality
  Lists.List
  Lia.

From Heapster Require Import
  Utils
  Permissions
  SepStep
  Memory.

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

Section HeapPerms.
  Record config : Type :=
    {
      m : memory;
      e : bool;
    }.
  Definition start_config :=
    {|
      m := nil;
      e := false;
    |}.

  Definition error_config (c : config) : config :=
    {|
      m := m c;
      e := true;
    |}.

  Definition read' (c : config) p :=
    read (m c) p.
  Definition write' (c : config) p v :=
    match write (m c) p v with
    | Some mem => Some
                   {|
                     m := mem;
                     e := e c;
                   |}
    | None => None
    end.

  Variant E : Type -> Type :=
    | Load : forall (p : Value), E Value
    | Store : forall (p v : Value), E unit
  .

  Variant step {R} : itree E R -> config -> itree E R -> config -> Prop :=
    | step_tau : forall t c,
        step (Tau t) c t c
    | step_load : forall k c p v,
        read' c p = Some v ->
        step (vis (Load (VPtr p)) k) c (k v) c
    | step_store : forall k c c' p v,
        write' c p v = Some c' ->
        step (vis (Store (VPtr p) v) k) c (k tt) c'
    | step_load_fail : forall k c p,
        read' c p = None ->
        step (vis (Load (VPtr p)) k) c (k (VNum 0)) (error_config c)
    | step_store_fail : forall k c p v,
        write' c p v = None ->
        step (vis (Store (VPtr p) v) k) c (k tt) (error_config c)
    | step_load_invalid : forall k c b,
        step (vis (Load (VNum b)) k) c (k (VNum 0)) (error_config c)
    | step_store_invalid : forall k c b v,
        step (vis (Store (VNum b) v) k) c (k tt) (error_config c)
  .
  Inductive multistep {R} : itree E R -> config -> itree E R -> config -> Prop :=
  | multistep_refl : forall t c, multistep t c t c
  | multistep_step : forall t c t' c' t'' c'',
      multistep t c t' c' -> step t' c' t'' c'' -> multistep t c t'' c''
  .

  Lemma step_bind {R1 R2} : forall (t1 t2 : itree E R1) (c1 c2 : config) (k : R1 -> itree E R2),
      step t1 c1 t2 c2 ->
      step (t1 >>= k) c1 (t2 >>= k) c2.
  Proof.
    intros. inversion H; subst; try solve [rewritebisim @bind_vis; constructor; auto].
    - rewritebisim @bind_tau. constructor.
    - rewritebisim @bind_vis.
      (* constructor doesn't work here for some reason *)
      apply (step_load (fun v => x <- k0 v;; k x) _ _ _ H0).
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

  Lemma rewrite_spin {R} : (ITree.spin : itree E R) = Tau (ITree.spin).
  Proof.
    intros. apply bisimulation_is_eq.
    ginit. gcofix CIH. gstep. unfold ITree.spin. constructor.
    apply Reflexive_eqit_gen_eq.
  Qed.
  Example typing_spin {R} : forall P Q, typing P Q (ITree.spin : itree E R).
  Proof.
    pcofix CIH. intros. pstep. constructor 1. split.
    - exists start_config. eexists. exists start_config. rewrite rewrite_spin. constructor.
    - intros. rewrite rewrite_spin in H1. inversion H1; subst; split; intuition.
      exists P. split.
      + right. auto.
      + exists p; split; [| split]; intuition.
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
        edestruct H7 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H5; reflexivity | |];
          apply bisimulation_is_eq in H8; subst; [| inversion Hstep].
        rewritebisim_in @bind_vis H5. inversion H5. apply Eqdep.EqdepTheory.inj_pair2 in H10; subst.
        destruct (H _ _ H2 H3 _ _ (step_load _ _ _ _ H6)) as (? & P' & ? & (p' & ? & ? & ?)).
        pclearbot. split; auto. exists P'. split; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H7 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H5; reflexivity | |];
          apply bisimulation_is_eq in H8; subst; [| inversion Hstep].
        rewritebisim_in @bind_vis H5. inversion H5. apply Eqdep.EqdepTheory.inj_pair2 in H10; subst.
        destruct (H _ _ H2 H3 _ _ (step_store _ _ _ _ _ H6)) as (? & P' & ? & (p' & ? & ? & ?)).
        pclearbot. split; auto. exists P'. split; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H7 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H5; reflexivity | |];
          apply bisimulation_is_eq in H8; subst; [| inversion Hstep].
        rewritebisim_in @bind_vis H5. inversion H5. apply Eqdep.EqdepTheory.inj_pair2 in H10; subst.
        destruct (H _ _ H2 H3 _ _ (step_load_fail _ _ _ H6)) as (? & P' & ? & (p' & ? & ? & ?)).
        pclearbot. split; auto. exists P'. split; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H7 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H5; reflexivity | |];
          apply bisimulation_is_eq in H8; subst; [| inversion Hstep].
        rewritebisim_in @bind_vis H5. inversion H5. apply Eqdep.EqdepTheory.inj_pair2 in H10; subst.
        destruct (H _ _ H2 H3 _ _ (step_store_fail _ _ _ _ H6)) as (? & P' & ? & (p' & ? & ? & ?)).
        pclearbot. split; auto. exists P'. split; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H5 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
          apply bisimulation_is_eq in H7; subst; [| inversion Hstep].
        rewritebisim_in @bind_vis H4. inversion H4. apply Eqdep.EqdepTheory.inj_pair2 in H10; subst.
        destruct (H _ _ H2 H3 _ _ (step_load_invalid _ _ _)) as (? & P' & ? & (p' & ? & ? & ?)).
        pclearbot. split; auto. exists P'. split; eauto.
      + pose proof @eqitree_inv_bind_vis.
        edestruct H5 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |];
          apply bisimulation_is_eq in H7; subst; [| inversion Hstep].
        rewritebisim_in @bind_vis H6. inversion H6. apply Eqdep.EqdepTheory.inj_pair2 in H9; subst.
        destruct (H _ _ H2 H3 _ _ (step_store_invalid _ _ _ _)) as (? & P' & ? & (p' & ? & ? & ?)).
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

  Definition no_error (c : config) :=
    e c = false.

  (* use instead of no_guar_error? *)
  Program Definition no_error_perm : perm :=
    {|
      pre := no_error;
      rely := fun c c' => no_error c -> no_error c';
      guar := eq;
    |}.
  Next Obligation.
    constructor; auto.
  Qed.

  Lemma typing_multistep {R} : forall P Q t,
      typing P Q t ->
      forall p c, p ∈ P ->
             pre p c ->
             forall t' c',
               multistep t c t' c' ->
               exists P', @typing R P' Q t' /\ exists p', p' ∈ P' /\ sep_step p p' /\ pre p' c'.
  Proof.
    intros. induction H2.
    - eexists; split; eauto. eexists; split; [| split]; eauto; reflexivity.
    - destruct IHmultistep as (P' & ? & p' & ? & ? & ?); eauto. pinversion H4; subst.
      + destruct H8 as (_ & ?). edestruct H8 as (? & P'' & ? & p'' & ? & ? & ?); eauto. pclearbot.
        exists P''; split; eauto. exists p''; split; [| split]; eauto. etransitivity; eauto.
      + inversion H3.
  Qed.

  Lemma typing_soundness_step {R} : forall P Q t,
      @typing R P Q t ->
      forall p c, p ∈ (P * singleton_Perms no_error_perm) ->
             pre p c ->
             forall t' c', step t c t' c' -> no_error c'.
  Proof.
    intros. rename p into p'. destruct H0 as (p & no_error & ? & ? & ?).
    apply H4 in H1. destruct H1 as (? & ? & ?).
    pinversion H; subst.
    - destruct H7. specialize (H8 _ _ H0 H1 _ _ H2) as (? & _).
      apply H3. respects. apply H6. auto.
    - inversion H2.
  Qed.

  Lemma typing_soundness {R} : forall P Q (t : itree E R),
      typing P Q t ->
      forall p c, p ∈ (P * singleton_Perms no_error_perm) ->
             pre p c ->
             forall t' c', multistep t c t' c' -> no_error c'.
  Proof.
    intros P Q t Htyping p0 c (p & no_err & Hp & Hno_err & Hlte) Hpre t' c' Hmultistep.
    induction Hmultistep.
    - apply Hno_err. apply Hlte. auto.
    - pose proof Hpre as H'. rename H into Hstep.
      apply Hlte in H'. destruct H' as (Hprep & Hpreno_err & Hsep).
      destruct (typing_multistep _ _ _ Htyping _ _ Hp Hprep _ _ Hmultistep) as (P' & Htyping' & p' & Hp' & Hsep_step & Hprep').
      eapply (typing_soundness_step _ _ _ Htyping').
      3: apply Hstep. (* apply H10 in H7. simpl. *)
      exists p', no_error_perm. split; [| split; [| split]]; cbn; auto; try reflexivity.
      apply Hsep_step in Hsep. eapply separate_upwards_closed; eauto.
      split; [| split]; auto.
      2: { apply Hsep_step in Hsep. eapply separate_upwards_closed; eauto. }
      apply IHHmultistep; eauto.
  Qed.


  (*** TODO *)
  Program Definition read_perm (ptr : addr) (v : Value) : perm :=
    {|
      (* ptr points to valid memory *)
      pre x := read x ptr = Some v;
      (* only checks if the memory ptr points to in the 2 configs are equal *)
      rely x y := read x ptr = read y ptr;
      (* no updates allowed *)
      guar x y := x = y;
    |}.
  Next Obligation.
    constructor; repeat intro; auto. etransitivity; eauto.
  Qed.

  Program Definition write_perm (ptr : addr) (v : SByte) : perm :=
    {|
      (* ptr points to valid memory *)
      pre x := read x ptr = Some v;
      (* only checks if the memory ptr points to in the 2 configs are equal *)
      rely x y := read x ptr = read y ptr;
      (* only the pointer we have write permission to may change *)
      guar x y := (forall ptr', ptr <> ptr' -> read x ptr' = read y ptr') /\
                    alloc_invariant x y ptr /\
                    e x = e y;
    |}.
  Next Obligation.
    constructor; repeat intro; auto. etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; split; repeat intro; try solve [intuition].
    - split; [| split]; reflexivity.
    - destruct H, H0. etransitivity. apply H; auto. auto.
    - destruct H as (? & ? & ? & ?), H0 as (? & ? & ? & ?).
      split; [| split]; etransitivity; eauto.
  Qed.

  Definition read_Perms (ptr : addr) (P : SByte -> Perms) : Perms :=
    meet_Perms (fun Q => exists y : SByte, Q = singleton_Perms (read_perm ptr y) ** P y).

  Definition write_Perms (ptr : addr) (P : SByte -> Perms) : Perms :=
    meet_Perms (fun Q => exists y : SByte, Q = singleton_Perms (write_perm ptr y) ** P y).


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

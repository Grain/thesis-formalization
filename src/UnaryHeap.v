(* begin hide *)
From Coq Require Import
  Arith.PeanoNat
  Logic.FunctionalExtensionality
  Lists.List
  Classes.Morphisms
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

  Definition read' (c : config) (p : Value) :=
    match p with
    | VPtr p => read (m c) p
    | VNum _ => None
    end.
  Definition write' (c : config) (p v : Value) :=
    match p with
    | VPtr p =>
        match write (m c) p v with
        | Some mem => Some
                       {|
                         m := mem;
                         e := e c;
                       |}
        | None => None
        end
    | VNum _ => None
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
        step (vis (Load p) k) c (k v) c
    | step_store : forall k c c' p v,
        write' c p v = Some c' ->
        step (vis (Store p v) k) c (k tt) c'
    | step_load_fail : forall k c p,
        read' c p = None ->
        step (vis (Load p) k) c (k (VNum 0)) (error_config c)
    | step_store_fail : forall k c p v,
        write' c p v = None ->
        step (vis (Store p v) k) c (k tt) (error_config c)
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

  Instance Proper_eq_Perms_typing {R} : Proper (eq_Perms ==> (pointwise_relation _ eq_Perms) ==> eq ==> flip impl) (@typing R).
  Proof.
    pcofix CIH. repeat intro. subst. pstep. pinversion H3; subst.
    - constructor 1. destruct H. split; auto. intros.
      edestruct H2; eauto. rewrite <- H0; auto. split; auto.
      destruct H8 as (? & ? & ? & ? & ? & ?). eexists. split.
      right. pclearbot. eapply CIH. 3: reflexivity. 3: apply H8.
      reflexivity. auto. eauto.
    - constructor 2; eauto. rewrite H0. rewrite H1. auto.
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
      (* + pose proof @eqitree_inv_bind_vis. *)
      (*   edestruct H5 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |]; *)
      (*     apply bisimulation_is_eq in H7; subst; [| inversion Hstep]. *)
      (*   rewritebisim_in @bind_vis H4. inversion H4. apply Eqdep.EqdepTheory.inj_pair2 in H10; subst. *)
      (*   destruct (H _ _ H2 H3 _ _ (step_load_invalid _ _ _)) as (? & P' & ? & (p' & ? & ? & ?)). *)
      (*   pclearbot. split; auto. exists P'. split; eauto. *)
      (* + pose proof @eqitree_inv_bind_vis. *)
      (*   edestruct H5 as [(? & ? & ?) | (? & ? & ?)]; [rewrite H6; reflexivity | |]; *)
      (*     apply bisimulation_is_eq in H7; subst; [| inversion Hstep]. *)
      (*   rewritebisim_in @bind_vis H6. inversion H6. apply Eqdep.EqdepTheory.inj_pair2 in H9; subst. *)
      (*   destruct (H _ _ H2 H3 _ _ (step_store_invalid _ _ _ _)) as (? & P' & ? & (p' & ? & ? & ?)). *)
      (*   pclearbot. split; auto. exists P'. split; eauto. *)
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

  (* Lemma typing_soundness {R} : forall P Q (t : itree E R), *)
  (*     typing P Q t -> *)
  (*     forall p c, p ∈ (P * singleton_Perms no_error_perm) -> *)
  (*            pre p c -> *)
  (*            forall r c', multistep t c (Ret r) c' -> exists q, q ∈ (Q r) /\ pre q c'. *)
  (* Proof. *)
  (*   intros P Q t Htyping p0 c (p & no_err & Hp & Hno_err & Hlte) Hpre t' c' Hmultistep. *)
  (*   remember (Ret t'). revert t' Heqi. *)
  (*   induction Hmultistep; intros; subst. *)
  (*   - punfold Htyping. inversion Htyping; subst. *)
  (*     apply Hno_err. apply Hlte. auto. *)
  (*   - pose proof Hpre as H'. rename H into Hstep. *)
  (*     apply Hlte in H'. destruct H' as (Hprep & Hpreno_err & Hsep). *)
  (*     destruct (typing_multistep _ _ _ Htyping _ _ Hp Hprep _ _ Hmultistep) as (P' & Htyping' & p' & Hp' & Hsep_step & Hprep'). *)
  (*     eapply (typing_soundness_step _ _ _ Htyping'). *)
  (*     3: apply Hstep. *)
  (*     exists p', no_error_perm. split; [| split; [| split]]; cbn; auto; try reflexivity. *)
  (*     apply Hsep_step in Hsep. eapply separate_upwards_closed; eauto. *)
  (*     split; [| split]; auto. *)
  (*     2: { apply Hsep_step in Hsep. eapply separate_upwards_closed; eauto. } *)
  (*     apply IHHmultistep; eauto. *)
  (* Qed. *)


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
      3: apply Hstep.
      exists p', no_error_perm. split; [| split; [| split]]; cbn; auto; try reflexivity.
      apply Hsep_step in Hsep. eapply separate_upwards_closed; eauto.
      split; [| split]; auto.
      2: { apply Hsep_step in Hsep. eapply separate_upwards_closed; eauto. }
      apply IHHmultistep; eauto.
  Qed.

  Program Definition read_perm (ptr : addr) (v : Value) : @perm config :=
    {|
      (** [ptr] points to [v] *)
      pre x := read (m x) ptr = Some v;
      (** only checks if the memory [ptr] points to in the 2 memories are equal *)
      rely x y := read (m x) ptr = read (m y) ptr;
      (** no updates allowed *)
      guar x y := x = y;
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; auto; etransitivity; eauto.
  Qed.

  Program Definition write_perm (ptr : addr) (v : Value) : @perm config :=
    {|
      (* [ptr] points to [v] *)
      pre x := Some v = read (m x) ptr;
      (* only checks if the memory [ptr] points to in the 2 configs are equal *)
      rely x y := read (m x) ptr = read (m y) ptr;
      (* only the pointer we have write permission to may change *)
      guar x y :=
        (e x = e y) /\
          (forall ptr', ptr <> ptr' -> read (m x) ptr' = read (m y) ptr') /\
          (forall ptr', sizeof (m x) ptr' = sizeof (m y) ptr') /\
          length (m x) = length (m y);
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; [intros [] |]; auto.
    - intros [] [] [] [] []. split.
      + destruct H, H1. subst. eexists.
      + split; [| split]; (etransitivity; [apply H0; auto |]); apply H2; auto.
  Qed.

  Lemma sep_step_read_perm l v v' :
    sep_step (read_perm l v) (read_perm l v').
  Proof.
    repeat intro. split; apply H; auto.
  Qed.

  Lemma sep_step_write_perm l v v' :
    sep_step (write_perm l v) (write_perm l v').
  Proof.
    repeat intro. split; apply H; auto.
  Qed.

  Lemma read_separate ptr ptr' v v' :
    read_perm ptr v ⊥ read_perm ptr' v'.
  Proof.
    split; intros; auto; destruct x, y; cbn in *; inversion H; auto.
  Qed.

  Lemma read_lte_write : forall ptr v, write_perm ptr v <= read_perm ptr v.
  Proof.
    constructor; cbn; intros [] []; subst; auto.
    intros []; subst.
    split; [| split; [| split]]; try reflexivity.
  Qed.

  Lemma write_write_sep ptr ptr' v v' :
      ptr <> ptr' ->
      write_perm ptr v ⊥ write_perm ptr' v'.
  Proof.
    intros Hdiff. constructor; intros; destruct x, y; cbn; apply H; auto.
  Qed.

  Definition read_Perms (ptr : addr) (P : Value -> Perms) : Perms :=
    join_Perms (fun Q => exists y : Value, Q = singleton_Perms (read_perm ptr y) * P y).

  Definition write_Perms (ptr : addr) (P : Value -> Perms) : Perms :=
    join_Perms (fun Q => exists y : Value, Q = singleton_Perms (write_perm ptr y) * P y).

  Program Definition eqp {A} (a a' : A) : @Perms config :=
    {|
      in_Perms _ := a = a'
    |}.

  Lemma EqRefl A (P : Perms) (xi : A) :
    P ⊑ P * (eqp xi) xi.
  Proof.
    repeat intro.
    exists p, top_perm. split; [| split; [| split]]; cbn; eauto.
    - apply separate_top.
    - rewrite sep_conj_perm_top. reflexivity.
  Qed.

  Lemma EqSym (A : Type) (xi yi : A) :
    (eqp yi) xi ⊑ (eqp xi) yi.
  Proof.
    repeat intro; cbn in *; subst; reflexivity.
  Qed.

  Lemma EqTrans (A : Type) (xi yi zi : A) :
    (eqp yi) xi * (eqp zi) yi ⊑ (eqp zi) xi.
  Proof.
    repeat intro. destruct H as (? & ? & ? & ? & ? & ?). cbn in *; subst. reflexivity.
  Qed.

  Lemma EqCtx (A B : Type) (xi yi : A) (f : A -> B) :
    (eqp yi) xi ⊑ (eqp (f yi)) (f xi).
  Proof.
    repeat intro. congruence.
  Qed.

  Lemma EqDup (A : Type) (xi yi : A) :
    (eqp yi) xi ⊑ (eqp yi) xi * (eqp yi) xi.
  Proof.
    repeat intro. cbn in *. subst. exists top_perm, top_perm.
    split; [| split; [| split]]; auto.
    - apply separate_top.
    - rewrite sep_conj_perm_top. apply top_perm_is_top.
  Qed.

  Lemma Cast (A : Type) (P : A -> Perms) xi yi :
    (eqp yi) xi * P yi ⊑ P xi.
  Proof.
    repeat intro. destruct H as (e & p' & Heq & Hp & Hsep & Hlte).
    cbn in Heq. subst.
    eapply Perms_downwards_closed; eauto. etransitivity. 2: apply lte_r_sep_conj_perm. eauto.
  Qed.

  (*
  Lemma PtrI_Read l l' (T : Value -> Perms) :
    read_Perms l (eqp l') * T l' ⊑ read_Perms l T.
  Proof.
    repeat intro. destruct l. rename p into p'.
    destruct H as (p & t & (P & (v & ?) & Hp) & Hp' & Hsep & Hlte). subst.
    destruct Hp as (? & ? & ? & ? & Hsep' & Hlte'). cbn in *. subst.
    eexists. split; [exists v; reflexivity |].
    eapply Perms_downwards_closed; eauto.
    do 2 eexists. split; [| split; [| split]]. apply H. apply Hp'.
    + symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
    + apply sep_conj_perm_monotone; intuition.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
  Qed.
  Lemma PtrI_Write l v (T : Value -> Perms) :
    write_Perms l (eqp v) * T v ⊑ write_Perms l T.
  Proof.
    repeat intro. destruct l. rename p into p'.
    destruct H as (p & t & (P & (v' & ?) & Hp) & Hp' & Hsep & Hlte). subst.
    destruct Hp as (? & ? & ? & ? & Hsep' & Hlte'). cbn in *. subst.
    eexists. split; [exists v'; reflexivity |].
    eapply Perms_downwards_closed; eauto.
    do 2 eexists. split; [| split; [| split]]. apply H. apply Hp'.
    + symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
    + apply sep_conj_perm_monotone; intuition.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
  Qed.

  Lemma PtrE_Read {R} P l T T' (t : itree E R) :
    (forall v, typing (P * read_Perms l (eqp v) * T v) T' t) ->
    typing (P * read_Perms l T) T' t.
  Proof.
    intros H. unfold read_Perms in *.
    setoid_rewrite <- sep_conj_Perms_assoc in H.
    setoid_rewrite sep_conj_Perms_join_commute in H.
    (* setoid_rewrite sep_conj_Perms_commut in H. *)
    (* setoid_rewrite sep_conj_Perms_commut in H. *)
    (* setoid_rewrite sep_conj_Perms_assoc in H. *)
    (* setoid_rewrite sep_conj_Perms_join_commute in H. *)
    rewrite sep_conj_Perms_commut.
    rewrite sep_conj_Perms_join_commute.

    pcofix CIH. intros H. pstep. constructor.



    repeat intro. rename p into p''. destruct H0 as (p & p' & Hp & Hptr & Hsep & Hlte).
    destruct xi; [contradiction | destruct a].
    destruct Hptr as (? & (? & ?) & ?). subst.
    destruct H2 as (pptr & pt & Hptr & Hpt & Hsep' & Hlte').
    eapply H; eauto. exists (p ** pptr), pt.
    split; [| split; [| split]]; eauto.
    - do 2 eexists. split; [| split; [| split]]. eauto. 3: reflexivity.
      + eexists. split; eauto. do 2 eexists.
        split; [| split; [| split]]. eauto. reflexivity. 2: apply sep_conj_perm_top'.
        apply separate_top.
      + eapply separate_upwards_closed; eauto. etransitivity; eauto. apply lte_l_sep_conj_perm.
    - symmetry. symmetry in Hsep'. apply separate_sep_conj_perm; auto.
      + symmetry. eapply separate_upwards_closed; eauto. etransitivity; eauto.
        apply lte_r_sep_conj_perm.
      + symmetry. eapply separate_upwards_closed; eauto. etransitivity; eauto.
        apply lte_l_sep_conj_perm.
    - etransitivity; eauto. rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; auto; reflexivity.
  Qed.

  Lemma ReadDup o xi yi :
    xi :: ptr (R, o, eqp yi) ⊑
      xi :: ptr (R, o, eqp yi) * xi :: ptr (R, o, eqp yi).
  Proof.
    repeat intro. cbn in *. destruct xi; [contradiction |].
    destruct a as [b o']. unfold offset in *.
    destruct H as (? & (v & ?) & ?). subst.
    exists (read_perm (b, o' + o) v), (read_perm (b, o' + o) v).
    destruct H0 as (pread & peq & Hpread & Hpeq & Hsep & Hlte).
    cbn in Hpread, Hpeq. subst.
    assert (read_perm (b, o' + o) v ∈ ptr_Perms R (VPtr (b, o' + o)) tt (eqp v)).
    {
      eexists. split; eauto. cbn in *. exists (read_perm (b, o' + o) v), top_perm.
      split; [| split; [| split]]. 2: reflexivity.
      - split; intros; auto.
      - apply separate_top.
      - rewrite sep_conj_perm_top. reflexivity.
    }
    split; [| split; [| split]]; auto.
    apply read_separate.
    constructor; intros; eauto.
    - split; [| split]; auto. 1, 2: apply Hpread; apply Hlte; auto.
      apply read_separate.
    - split; apply Hpread; apply Hlte; auto.
    - apply Hlte. constructor. left. apply Hpread. induction H0; auto.
      + destruct H0; auto.
      + etransitivity; eauto.
  Qed.
   *)

  Lemma typing_load ptr (Q : Value -> Perms) :
    typing
      (read_Perms ptr Q)
      (fun x => (read_Perms ptr (eqp x)) * Q x)
      (trigger (Load (VPtr ptr))).
  Proof.
    pstep. constructor 1. split.
    - eexists {| m := _; e := false |}. do 2 eexists.
      constructor. unfold read'. cbn. eapply read_mem_at.
      Unshelve. apply (VNum 0).
    - intros p' c (P & (v & ?) & Hp) Hpre t' c' Hstep. subst.
      destruct Hp as (p & q & Hp & Hq & Hsep & Hlte). cbn in Hp.
      inversion Hstep; subst; apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
      + split; intuition. assert (v = v0). {
          apply Hlte in Hpre. destruct Hpre as (Hpre & _). apply Hp in Hpre.
          rewrite Hpre in H4. inversion H4. auto.
        } subst. eexists. split.
        * left. pstep. constructor 2. reflexivity.
        * exists (p ** q). split; [| split]; eauto.
          2: { eapply sep_step_lte. 2: reflexivity. auto. }
          exists p, q. split; [| split]; intuition.
          eexists. split. eexists. reflexivity. cbn. eexists. exists top_perm.
          split; [| split; [| split]]; eauto. apply separate_top. apply sep_conj_perm_top.
      + apply Hlte in Hpre. destruct Hpre as (Hpre & _). apply Hp in Hpre.
        rewrite Hpre in H4. inversion H4.
  Qed.

  Lemma typing_store_alt {R} ptr val (P Q : Value -> Perms) (r : R) :
    typing
      (write_Perms ptr P * Q val)
      (fun _ => write_Perms ptr Q)
      (trigger (Store (VPtr ptr) val)).
  Proof.
  pstep. constructor 1. split.
  - eexists {| m := _; e := false |}. do 2 eexists.
    constructor. unfold write'. cbn.
    rewrite write_mem_at. reflexivity. Unshelve. apply (VNum 0).
  - intros p'' c (p' & q & (? & (val' & ?) & Hp') & Hq & Hsep'' & Hlte'') Hpre t' c' Hstep. subst.
    destruct Hp' as (pw & p & Hwrite & Hp & Hsep' & Hlte'). cbn in Hwrite.
    inversion Hstep; subst; apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
    {
      assert (guar p' c c').
      {
        unfold write' in H5. destruct (write (m c) ptr val) eqn:Hwrite'; inversion H5.
        apply Hlte'. constructor 1. left. apply Hwrite.
        split; [| split; [| split]]; auto.
        - eapply write_success_read_neq; eauto.
        - eapply write_success_sizeof; eauto.
        - eapply write_success_length; eauto.
      }
      split.
      { apply Hlte''. constructor 1. left. auto. }
      eexists. split.
      { left. pstep. constructor 2. reflexivity. }
      exists (write_perm ptr val ** q). split; [| split].
      - eexists. split; eauto.
        do 2 eexists. split; [| split; [apply Hq | split]]; cbn; try reflexivity.
        symmetry in Hsep''. eapply separate_upwards_closed in Hsep''; eauto.
        apply separate_sep_conj_perm_l in Hsep''.
        eapply separate_upwards_closed in Hsep''; eauto.
        symmetry. split; apply Hsep''.
      - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l.
        { apply Hlte'' in Hpre. apply Hpre. }
        eapply sep_step_lte; eauto. eapply sep_step_lte. apply lte_l_sep_conj_perm.
        eapply sep_step_lte; eauto.
        apply sep_step_write_perm.
      - cbn. split; [| split]; auto.
        + unfold write' in H5. destruct (write (m c) ptr val) eqn:Hwrite'; inversion H5.
          destruct c'. inversion H1. subst. cbn.
          apply write_success_read_eq in Hwrite'.
          symmetry. assumption.
        + respects. 2: { apply Hlte'' in Hpre. apply Hpre. }
                  apply Hlte'' in Hpre. apply Hpre. auto.
        + apply Hlte'' in Hpre. destruct Hpre as (_ & _ & Hsep). symmetry in Hsep.
          eapply separate_upwards_closed in Hsep; eauto.
          apply separate_sep_conj_perm_l in Hsep.
          eapply separate_upwards_closed in Hsep; eauto. destruct Hsep. constructor; auto.
    }
    {
      apply Hlte'' in Hpre. destruct Hpre as (? & _).
      apply Hlte' in H. destruct H as (? & _).
      apply Hwrite in H. cbn in H.
      unfold write' in H5.
      symmetry in H. apply read_success_write with (v' := val) in H. destruct H.
      rewrite H in H5. inversion H5.
    }
  Qed.

  Lemma typing_store {R} ptr val (P Q : Value -> @Perms config) (r : R) :
    typing
      (write_Perms ptr P)
      (fun _ => write_Perms ptr (eqp val))
      (trigger (Store (VPtr ptr) val)).
  Proof.
    assert (top_Perms ≡ eqp val val).
    { split; repeat intro; cbn; auto. }
    rewrite <- sep_conj_Perms_top_identity. rewrite sep_conj_Perms_commut.
    rewrite H. eapply typing_store_alt; eauto.
  Qed.

End HeapPerms.

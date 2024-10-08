(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Logic.Decidable
     Lists.List
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     FSets.FMaps.

From ITree Require Import
     ITree
     Eq.Eqit
     Eq.EqAxiom.

From Heapster Require Import
     Utils
     Permissions
     PermType
     Memory
     Lifetime
     MemoryPerms
     LifetimePerms
     Typing
     SepStep
     PermTypeProofs.

From Paco Require Import
     paco.

Import ITreeNotations.
Import ListNotations.

Open Scope list_scope.
Open Scope itree_scope.
(* end hide *)

Section Perms.
  Context {Si Ss : Type}.
  Context `{Hmemory: Lens Si memory}.
  Context `{Hlifetime: Lens Si Lifetimes}.

  Context `{HGetPut1 : (forall x y, @lget _ _ Hmemory (@lput _ _ Hlifetime x y) = @lget _ _ Hmemory x)}.
  Context `{HGetPut2 : (forall x y, @lget _ _ Hlifetime (@lput _ _ Hmemory x y) = @lget _ _ Hlifetime x)}.
  Context `{HPutPut : (forall si x y, @lput _ _ Hmemory (@lput _ _ Hlifetime si x) y =
                                   @lput _ _ Hlifetime (@lput _ _ Hmemory si y) x)}.
  (* Context `{HPutPut2 : (forall si x y, @lput _ _ Hlifetime (@lput _ _ Hmemory si x) y = *)
  (*                                   @lput _ _ Hmemory (@lput _ _ Hlifetime si y) x)}. *)

  Lemma nonLifetime_read_perm p v :
    @nonLifetime _ Ss _ (read_perm p v).
  Proof.
    intros n. split; intros [] [].
    - intros. cbn in *. destruct H as ((? & H) & _). rewrite H. rewrite HGetPut1. reflexivity.
    - intros. cbn in *. subst. split; reflexivity.
  Qed.
  Lemma nonLifetime_write_perm p v :
    @nonLifetime _ Ss _ (write_perm p v).
  Proof.
    intros n. split; intros [] [].
    - intros. cbn in *. destruct H as ((? & H) & _). rewrite H. rewrite HGetPut1. reflexivity.
    - intros. cbn in *. destruct H as ((? & H) & _). rewrite H. do 2 rewrite HGetPut2.
      split; reflexivity.
  Qed.

  Lemma rely_inv_read_perm p v :
    @rely_inv _ Ss _ (read_perm p v).
  Proof.
    repeat intro. cbn in *. do 2 rewrite HGetPut1. auto.
  Qed.
  Lemma rely_inv_write_perm p v :
    @rely_inv _ Ss _ (write_perm p v).
  Proof.
    repeat intro. cbn in *. do 2 rewrite HGetPut1. auto.
  Qed.

  Lemma guar_inv_read_perm p v :
    @guar_inv _ Ss _ (read_perm p v).
  Proof.
    repeat intro. cbn in *. subst. reflexivity.
  Qed.
  Lemma guar_inv_write_perm p v :
    @guar_inv _ Ss _ (write_perm p v).
  Proof.
    repeat intro. destruct H as ((? & ?) & ? & ? & ?). subst.
    cbn. rewrite !HGetPut1, HGetPut2.
    split; [| split; [| split]]; auto.
    eexists. rewrite HPutPut. reflexivity.
  Qed.

  Lemma pre_inv_read_perm p v :
    @pre_inv _ Ss _ (read_perm p v).
  Proof.
    repeat intro. cbn. rewrite HGetPut1. auto.
  Qed.
  Lemma pre_inv_write_perm p v :
    @pre_inv _ Ss _ (write_perm p v).
  Proof.
    repeat intro. cbn. rewrite HGetPut1. auto.
  Qed.

  Lemma nonLifetime_ptr {A} p rw o' a (T : VPermType A) (HT : forall xi xs, nonLifetime_Perms (xi :: T ▷ xs)) :
    @nonLifetime_Perms _ Ss _ ((VPtr p) :: ptr(rw, o', T) ▷ a).
  Proof.
    intros q Hq. destruct p as [b o]. destruct Hq as (? & (v & ?) & ?). subst.
    destruct H0 as (p & pt' & Hp & Ht' & Hsep & Hlte).
    edestruct (HT v a _ Ht') as (pt & Ht & Hlte' & Hnlt & Hrelyt & Hguart & Hpret).
    destruct rw.
    - assert (Hsep' : (read_perm (b, o + o') v) ⊥ pt).
      {
        eapply separate_upwards_closed. 2: apply Hlte'.
        symmetry. eapply separate_upwards_closed. 2: apply Hp. symmetry; auto.
      }
      exists ((read_perm (b, o + o') v) ** pt). split; [| split; [| split; [| split; [| split]]]].
      + eexists. split. eexists. reflexivity.
        cbn. do 2 eexists. split; [| split; [| split]]; eauto; reflexivity.
      + etransitivity; eauto. apply sep_conj_perm_monotone; auto.
      + apply nonLifetime_sep_conj_perm; auto. apply nonLifetime_read_perm.
      + apply rely_inv_sep_conj_perm; auto. apply rely_inv_read_perm.
      + apply guar_inv_sep_conj_perm; auto. apply guar_inv_read_perm.
      + apply pre_inv_sep_conj_perm; auto. apply pre_inv_read_perm.
    - assert (Hsep' : (write_perm (b, o + o') v) ⊥ pt).
      {
        eapply separate_upwards_closed. 2: apply Hlte'.
        symmetry. eapply separate_upwards_closed. 2: apply Hp. symmetry; auto.
      }
      exists ((write_perm (b, o + o') v) ** pt). split; [| split; [| split; [| split; [| split]]]].
      + eexists. split. eexists. reflexivity.
        cbn. do 2 eexists. split; [| split; [| split]]; eauto; reflexivity.
      + etransitivity; eauto. apply sep_conj_perm_monotone; auto.
      + apply nonLifetime_sep_conj_perm; auto. apply nonLifetime_write_perm.
      + apply rely_inv_sep_conj_perm; auto. apply rely_inv_write_perm.
      + apply guar_inv_sep_conj_perm; auto. apply guar_inv_write_perm.
      + apply pre_inv_sep_conj_perm; auto. apply pre_inv_write_perm.
  Qed.

  Lemma nonLifetime_trueP :
    forall (xi : Value) (xs : unit), @nonLifetime_Perms _ Ss _ (xi :: trueP ▷ xs).
  Proof.
    repeat intro. exists top_perm. cbn. intuition.
    apply top_perm_is_top.
    apply nonLifetime_top.
    apply rely_inv_top.
    apply guar_inv_top.
    apply pre_inv_top.
  Qed.

  Lemma nonLifetime_eqp y :
    forall (xi : Value) (xs : unit), @nonLifetime_Perms _ Ss _ (xi :: eqp y ▷ xs).
  Proof.
    repeat intro. exists top_perm. cbn. intuition.
    apply top_perm_is_top.
    apply nonLifetime_top.
    apply rely_inv_top.
    apply guar_inv_top.
    apply pre_inv_top.
  Qed.

  Lemma nonLifetime_IsNat :
    forall (xi : Value) (xs : {_ : nat & unit}), nonLifetime_Perms (xi :: IsNat Si Ss ▷ xs).
  Proof.
    repeat intro. exists top_perm.
    split; [| split; [| split; [| split; [| split]]]]; auto.
    apply top_perm_is_top.
    apply nonLifetime_top.
    apply rely_inv_top.
    apply guar_inv_top.
    apply pre_inv_top.
  Qed.

  (*** Permission sets made of iterated * *)
  (** when l is only applied to the ptr permission, not the internal permission *)
  Definition when_ptr_Perms {A} (l : nat) (rw : RW) (p : Value) (a : A) (T : VPermType A)
    : @Perms (Si * Ss) :=
    match p with
    | VNum _ => bottom_Perms
    | VPtr p =>
        join_Perms (fun P => exists (v : Value),
                        P = singleton_Perms
                              (match rw with
                               | R => when l (read_perm p v)
                               | W => when l (write_perm p v)
                               end) *
                              (v :: T ▷ a))
    end.

  Definition when_ptr {A} (l : nat) '(rw, o, T) : VPermType A :=
    {|
      ptApp := fun x a => when_ptr_Perms l rw (offset x o) a T;
    |}.

  (** all the when_ptr (R) [Perms] starred together, with a T on each *)
  Fixpoint when_ptrs_T l (vals : list (nat * nat * nat * {A & (prod (VPermType A) A)}))
    : @Perms (Si * Ss) :=
    match vals with
    | nil => top_Perms
    | cons v vals => let '(b, o, o', x) := v in
                    (VPtr (b, o) :: when_ptr l (R, o', (fst (projT2 x))) ▷ (snd (projT2 x))) *
                      when_ptrs_T l vals
    end.

  Lemma when_ptrs_T_app l l1 l2 :
    when_ptrs_T l (l1 ++ l2) ≡
      when_ptrs_T l l1 * when_ptrs_T l l2.
  Proof.
    revert l2.
    induction l1; intros.
    - cbn. rewrite sep_conj_Perms_top_identity. reflexivity.
    - destruct a as [[[? ?] ?] ?]. unfold app. unfold when_ptrs_T.
      rewrite <- sep_conj_Perms_assoc.
      apply Proper_eq_Perms_sep_conj_Perms; [reflexivity | apply IHl1].
  Qed.

  Lemma when_ptrs_T_swap' l a b :
    when_ptrs_T l ([a ; b]) ≡
      when_ptrs_T l ([b ; a]).
  Proof.
    destruct a as [[[? ?] ?] ?].
    destruct b as [[[? ?] ?] ?].
    unfold when_ptrs_T.
    rewrite sep_conj_Perms_commut.
    do 2 rewrite (sep_conj_Perms_commut _ top_Perms).
    do 2 rewrite sep_conj_Perms_top_identity. reflexivity.
  Qed.

  Lemma when_ptrs_T_swap l l1 a b l2 :
    when_ptrs_T l (l1 ++ [a ; b] ++ l2) ≡
      when_ptrs_T l (l1 ++ [b ; a] ++ l2).
  Proof.
    do 4 rewrite when_ptrs_T_app.
    apply Proper_eq_Perms_sep_conj_Perms; [reflexivity |].
    apply Proper_eq_Perms_sep_conj_Perms; [| reflexivity].
    apply when_ptrs_T_swap'.
  Qed.

  (** finished aplied to pointer permission only *)
  Definition finished_ptr_Perms {A} (l : nat) (rw : RW) (p : Value) (a : A) (T : VPermType A) : @Perms (Si * Ss) :=
    match p with
    | VNum _ => top_Perms
    | VPtr p =>
        join_Perms (fun P => exists (v : Value),
                        P = singleton_Perms
                              (match rw with
                               | R => lfinished l (read_perm p v)
                               | W => lfinished l (write_perm p v)
                               end) *
                              (v :: T ▷ a))
    end.

  Definition finished_ptr {A} (l : nat) '(rw, o, T) : VPermType A :=
    {|
      ptApp := fun x a => finished_ptr_Perms l rw (offset x o) a T;
    |}.

  Fixpoint finished_ptrs_T l (vals : list (nat * nat * nat * {A & (prod (VPermType A) A)})) :=
    match vals with
    | nil => lfinished_Perms l top_Perms
    | cons v vals => let '(b, o, o', x) := v in
                    (VPtr (b, o) :: finished_ptr l (W, o', (fst (projT2 x))) ▷ (snd (projT2 x))) *
                      finished_ptrs_T l vals
    end.

  Lemma lfinished_top_twice l :
    lfinished_Perms (Ss := Ss) l top_Perms * lfinished_Perms l top_Perms ≡
    lfinished_Perms l top_Perms.
  Proof.
    split; repeat intro.
    - destruct H as (? & ? & ? & ? & ? & ?).
      eapply Perms_downwards_closed; eauto. etransitivity; eauto. apply lte_r_sep_conj_perm.
    - do 2 exists (lfinished l top_perm). split; [| split; [| split]].
      + cbn. eexists. split. eexists. split. auto. reflexivity.
        cbn. reflexivity.
      + cbn. eexists. split. eexists. split. auto. reflexivity.
        cbn. reflexivity.
      + apply lfinished_separate. apply separate_top.
      + cbn in H. destruct H as (? & (? & _ & ?) & ?). subst. cbn in H0.
        etransitivity. 2: apply lfinished_sep_conj_perm_dist.
        etransitivity; eauto.
        apply lfinished_monotone.
        rewrite sep_conj_perm_top. apply top_perm_is_top.
  Qed.

  Lemma finished_ptrs_T_app l l1 l2 :
    finished_ptrs_T l (l1 ++ l2) ≡
      finished_ptrs_T l l1 * finished_ptrs_T l l2.
  Proof.
    revert l2.
    induction l1; intros.
    - cbn. induction l2.
      + cbn. rewrite lfinished_top_twice. reflexivity.
      + destruct a as [[[? ?] ?] ?]. unfold finished_ptrs_T. rewrite IHl2.
        do 2 rewrite (sep_conj_Perms_commut (lfinished_Perms l top_Perms)).
        rewrite sep_conj_Perms_assoc.
        rewrite <- (sep_conj_Perms_assoc _ (lfinished_Perms l top_Perms)).
        rewrite lfinished_top_twice.
        reflexivity.
    - destruct a as [[[? ?] ?] ?]. unfold app. unfold finished_ptrs_T.
      rewrite <- sep_conj_Perms_assoc.
      apply Proper_eq_Perms_sep_conj_Perms; [reflexivity | apply IHl1].
  Qed.

  Lemma finished_ptrs_T_swap' l a b :
    finished_ptrs_T l ([a ; b]) ≡
      finished_ptrs_T l ([b ; a]).
  Proof.
    destruct a as [[[? ?] ?] ?].
    destruct b as [[[? ?] ?] ?].
    unfold finished_ptrs_T.
    do 2 rewrite sep_conj_Perms_assoc.
    rewrite (sep_conj_Perms_commut (VPtr (n, n0) :: finished_ptr l (W, n1, fst (projT2 s)) ▷ snd (projT2 s))).
    reflexivity.
  Qed.

  Lemma finished_ptrs_T_swap l l1 a b l2 :
    finished_ptrs_T l (l1 ++ [a ; b] ++ l2) ≡
      finished_ptrs_T l (l1 ++ [b ; a] ++ l2).
  Proof.
    do 4 rewrite finished_ptrs_T_app.
    apply Proper_eq_Perms_sep_conj_Perms; [reflexivity |].
    apply Proper_eq_Perms_sep_conj_Perms; [| reflexivity].
    apply finished_ptrs_T_swap'.
  Qed.

  (*** Split rules *)
  (* We *only* have this lemma for pointer permissions, due to contraints about preconditions (I think?) TODO: generalize *)
  Lemma split_Perms_T {A} b o o' l (P Q : @Perms (Si * Ss)) (T : VPermType A) xs
    (HT : forall xi xs, nonLifetime_Perms (xi :: T ▷ xs)) :
    (VPtr (b, o)) :: ptr(W, o', T) ▷ xs * lowned_Perms l P Q ⊑
      (VPtr (b, o) :: when_ptr l (W, o', T) ▷ xs) *
      lowned_Perms l
        ((VPtr (b, o) :: when_ptr l (R, o', trueP) ▷ tt) * P)
        ((VPtr (b, o) :: ptr(W, o', trueP) ▷ tt) * Q).
  Proof.
    intros p0 (p' & powned & Hp' & (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf) & Hsep & Hlte).
    destruct Hp' as (? & (v & ?) & Hv). subst.
    destruct Hv as (pw & pt & Hpw & Hpt & Hsep'' & Hlte'').
    destruct (HT _ _ _ Hpt) as (pt' & Hpt' & Hltept & Hnlpt & Hrelypt & Hguarpt & Hprept).
    assert (Hsepwrite : write_perm (b, o + o') v ⊥ r2).
    {
      eapply owned_sep; auto.
      apply nonLifetime_write_perm. apply rely_inv_write_perm. apply guar_inv_write_perm.
      eapply separate_upwards_closed.
      2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
      symmetry.
      eapply separate_upwards_closed. 2: apply Hpw.
      eapply separate_upwards_closed.
      2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
      symmetry. auto.
    }
    exists (when l (write_perm (b, o + o') v) ** pt').
    exists (r1 ** owned l (write_perm (b, o + o') v ** r2) (nonLifetime_sep_conj_perm _ _ (nonLifetime_write_perm _ _) Hnlr2 Hsepwrite)).
    split; [| split; [| split]].
    - cbn. eexists. split. eexists. reflexivity.
      cbn. do 2 eexists. split. reflexivity.
      split; [| split]; try reflexivity; auto.
      apply sep_when; auto.
      eapply separate_upwards_closed. 2: apply Hltept.
      symmetry. eapply separate_upwards_closed. 2: apply Hpw.
      symmetry; auto.
    - exists r1, (write_perm (b, o + o') v ** r2), Hsepr1, Hnlr1.
      exists (nonLifetime_sep_conj_perm _ _ (nonLifetime_write_perm _ _) Hnlr2 Hsepwrite).
      exists (rely_inv_sep_conj_perm _ _ (rely_inv_write_perm _ _) Hrelyr2).
      exists (guar_inv_sep_conj_perm _ _ (guar_inv_write_perm _ _) Hguarr2).
      split; [| split]. 2: reflexivity.
      + apply sep_conj_Perms_perm; auto.
        cbn. eexists. split. eexists. reflexivity.
        rewrite sep_conj_Perms_commut.
        rewrite sep_conj_Perms_top_identity.
        cbn. reflexivity.
      + intros p1 (pwhen & q & (? & (v' & ?) & Hlte''') & Hq' & Hsep''' & Hlte'''') Hsep''''; subst.
        rewrite sep_conj_Perms_commut in Hlte'''.
        rewrite sep_conj_Perms_top_identity in Hlte'''. cbn in Hlte'''.

        specialize (Hf _ Hq'). destruct Hf as (r & Hr & Hsep_step & Hpre).
        {
          symmetry in Hsep''''.
          eapply separate_upwards_closed in Hsep''''; eauto.
          eapply separate_upwards_closed in Hsep''''; eauto.
          2: apply lte_r_sep_conj_perm.
          symmetry in Hsep''''.
          eapply separate_upwards_closed in Hsep''''; eauto.
          apply sep_conj_perm_monotone. reflexivity.
          apply owned_monotone. apply lte_r_sep_conj_perm.
        }
        exists ((write_perm (b, o + o') v') ** r). split; [| split].
        * apply sep_conj_Perms_perm; auto.
          -- cbn. eexists. split. eexists. reflexivity.
             rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_top_identity.
             cbn. reflexivity.
          -- symmetry. apply Hsep_step.
             symmetry. eapply sep_step_write_perm; eauto.
        * etransitivity.
          -- apply sep_step_sep_conj_r; eauto. symmetry. auto.
          -- apply sep_step_sep_conj_l; eauto. symmetry. apply Hsep_step. symmetry. auto.
             eapply sep_step_write_perm.
        * (** Precondition section *)
          intros. split; [| split].
          -- apply Hlte'''' in H. destruct H as (? & ? & ?).
             apply Hlte''' in H. cbn in H.
             rewrite lGetPut in H. setoid_rewrite nth_error_replace_list_index_eq in H.
             setoid_rewrite HGetPut1 in H.
             cbn. rewrite HGetPut1. symmetry. apply H; auto.
          -- apply Hpre; auto. apply Hlte''''; auto.
          -- symmetry. apply Hsep_step.
             symmetry. eapply sep_step_write_perm; eauto.
    - (** everything is pairwise separate *)
      apply separate_sep_conj_perm_4.
      + apply sep_when; auto.
        eapply separate_upwards_closed. 2: apply Hltept.
        symmetry.
        eapply separate_upwards_closed. 2: apply Hpw. symmetry. auto.
      + apply sep_when; auto.
        eapply separate_upwards_closed.
        2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
        symmetry.
        eapply separate_upwards_closed. 2: apply Hpw.
        eapply separate_upwards_closed.
        2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
        symmetry. auto.
      + apply when_owned_sep.
      + eapply separate_upwards_closed.
        2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
        symmetry.
        eapply separate_upwards_closed. 2: apply Hltept.
        eapply separate_upwards_closed.
        2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
        symmetry. auto.
      + apply sep_sep_conj_perm_owned; auto.
        * eapply separate_upwards_closed. 2: apply Hpw.
          symmetry. eapply separate_upwards_closed; eauto.
        * eapply separate_upwards_closed.
          2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
          symmetry. eapply separate_upwards_closed. 2: apply Hltept.
          eapply separate_upwards_closed.
          2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
          symmetry. auto.
      + apply Hsepr1.
    - (** Shuffling around permissions using <= *)
      etransitivity; eauto.
      etransitivity. apply sep_conj_perm_monotone; [reflexivity | apply Hlte'].
      do 2 rewrite <- sep_conj_perm_assoc.
      do 2 rewrite (sep_conj_perm_commut _ r1).
      do 3 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [reflexivity |].

      etransitivity. apply sep_conj_perm_monotone; [| reflexivity]; eauto.
      rewrite <- sep_conj_perm_assoc.
      rewrite (sep_conj_perm_commut _ pt).
      rewrite (sep_conj_perm_commut _ pt').
      do 2 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [assumption |].

      etransitivity. 2: apply convert.
      apply sep_conj_perm_monotone; [| reflexivity]; auto.
  Qed.

  Lemma split_Perms_eq b o o' l (P Q : @Perms (Si * Ss)) x :
    (VPtr (b, o)) :: ptr(W, o', eqp x) ▷ tt * lowned_Perms l P Q ⊑
      (VPtr (b, o) :: when_ptr l (W, o', eqp x) ▷ tt) *
      lowned_Perms l
        ((VPtr (b, o) :: when_ptr l (R, o', eqp x) ▷ tt) * P)
        ((VPtr (b, o) :: ptr(W, o', eqp x) ▷ tt) * Q).
  Proof.
    intros p0 (p' & powned & Hp' & (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf) & Hsep & Hlte).
    destruct Hp' as (? & (v & ?) & Hv). subst.
    destruct Hv as (pw & pt & Hpw & Hpt & Hsep'' & Hlte'').
    cbn in Hpt. subst.
    assert (Hsepwrite : write_perm (b, o + o') v ⊥ r2).
    {
      eapply owned_sep; auto.
      apply nonLifetime_write_perm. apply rely_inv_write_perm. apply guar_inv_write_perm.
      eapply separate_upwards_closed.
      2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
      symmetry.
      eapply separate_upwards_closed. 2: apply Hpw.
      eapply separate_upwards_closed.
      2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
      symmetry. auto.
    }
    exists (when l (write_perm (b, o + o') v)).
    exists (r1 ** owned l (write_perm (b, o + o') v ** r2) (nonLifetime_sep_conj_perm _ _ (nonLifetime_write_perm _ _) Hnlr2 Hsepwrite)).
    split; [| split; [| split]].
    - cbn. eexists. split. eexists. reflexivity.
      cbn. do 2 eexists.
      split; [| split; [| split]]; try reflexivity; auto.
      apply separate_top.
      apply sep_conj_perm_top.
    - exists r1, (write_perm (b, o + o') v ** r2), Hsepr1, Hnlr1.
      exists (nonLifetime_sep_conj_perm _ _ (nonLifetime_write_perm _ _) Hnlr2 Hsepwrite).
      exists (rely_inv_sep_conj_perm _ _ (rely_inv_write_perm _ _) Hrelyr2).
      exists (guar_inv_sep_conj_perm _ _ (guar_inv_write_perm _ _) Hguarr2).
      split; [| split]. 2: reflexivity.
      + apply sep_conj_Perms_perm; auto.
        cbn. eexists. split. eexists. reflexivity.
        do 2 eexists. split; [| split; [| split]]; cbn; try reflexivity.
        apply separate_top.
        apply sep_conj_perm_top.
      + intros p1 (pwhen & q & (? & (v' & ?) & Hlte''') & Hq' & Hsep''' & Hlte'''') Hsep''''; subst.
        destruct Hlte''' as (? & ? & ? & ? & ? & ?). cbn in H0. subst.
        rename v' into v.
        (* rewrite sep_conj_Perms_commut in Hlte'''. *)
        (* rewrite sep_conj_Perms_bottom_identity in Hlte'''. cbn in Hlte'''. *)

        specialize (Hf _ Hq'). destruct Hf as (r & Hr & Hsep_step & Hpre).
        {
          symmetry in Hsep''''.
          eapply separate_upwards_closed in Hsep''''; eauto.
          eapply separate_upwards_closed in Hsep''''; eauto.
          2: apply lte_r_sep_conj_perm.
          symmetry in Hsep''''.
          eapply separate_upwards_closed in Hsep''''; eauto.
          apply sep_conj_perm_monotone. reflexivity.
          apply owned_monotone. apply lte_r_sep_conj_perm.
        }
        exists ((write_perm (b, o + o') v) ** r). split; [| split].
        * apply sep_conj_Perms_perm; auto.
          -- cbn. eexists. split. eexists. reflexivity. cbn.
             do 2 eexists. split; [| split; [| split]]; try reflexivity.
             apply separate_top.
             apply sep_conj_perm_top.
          -- symmetry. apply Hsep_step.
             symmetry. eauto.
        * etransitivity.
          -- apply sep_step_sep_conj_r; eauto. symmetry. auto.
          -- apply sep_step_sep_conj_l; eauto. symmetry. apply Hsep_step. symmetry. auto.
             eapply sep_step_write_perm.
        * (** Precondition section *)
          intros.
          split; [| split].
          -- apply Hlte'''' in H0. destruct H0 as (? & ? & ?).
             apply H2 in H0. destruct H0. apply H in H0. cbn in H0.
             rewrite lGetPut in H0. setoid_rewrite nth_error_replace_list_index_eq in H0.
             setoid_rewrite HGetPut1 in H0.
             cbn. rewrite HGetPut1. symmetry. apply H0; auto.
          -- apply Hpre; auto. apply Hlte''''; auto.
          -- symmetry. apply Hsep_step.
             symmetry. eauto.
    - (** everything is pairwise separate *)
      apply separate_sep_conj_perm.
      + apply sep_when; auto.
        eapply separate_upwards_closed.
        2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
        symmetry.
        eapply separate_upwards_closed. 2: apply Hpw.
        eapply separate_upwards_closed.
        2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
        symmetry. auto.
      + apply when_owned_sep.
      + symmetry. apply Hsepr1.
    - (** Shuffling around permissions using <= *)
      etransitivity; eauto.
      etransitivity. apply sep_conj_perm_monotone; [reflexivity | apply Hlte'].
      do 2 rewrite <- sep_conj_perm_assoc.
      do 2 rewrite (sep_conj_perm_commut _ r1).
      do 2 rewrite sep_conj_perm_assoc.
      apply sep_conj_perm_monotone; [reflexivity |].

      etransitivity. apply sep_conj_perm_monotone; [| reflexivity]; eauto.
      rewrite (sep_conj_perm_commut _ pt).
      rewrite sep_conj_perm_assoc.

      etransitivity. apply lte_r_sep_conj_perm.
      etransitivity. 2: apply convert.
      apply sep_conj_perm_monotone; [| reflexivity]; auto.
  Qed.

  (*** Partial return rule *)
  Lemma partial_ptr b o l o' P Q x :
    (VPtr (b, o) :: when_ptr l (R, o', eqp x) ▷ tt) *
      lowned_Perms l ((VPtr (b, o) :: when_ptr l (R, o', eqp x) ▷ tt) * P) Q
        ⊑
        lowned_Perms l P Q.
  Proof.
    intros p0 (p' & powned & Hp' & (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf) & Hsep & Hlte).
    destruct Hp' as (? & (v & ?) & Hp'); subst.
    destruct Hp' as (pwhen & pt & Hpwhen & Hpt & Hsep' & Hlte''). cbn in Hpt; subst.
    assert (Hsep'': r1 ⊥ when l (read_perm (b, o + o') v)).
    {
      eapply separate_upwards_closed. 2: eapply Hpwhen.
      eapply separate_upwards_closed. 2: apply lte_l_sep_conj_perm.
      eapply separate_upwards_closed. 2: eauto. symmetry.
      eapply separate_upwards_closed. 2: apply lte_l_sep_conj_perm.
      eapply separate_upwards_closed. 2: eauto. auto.
    }
    exists (when l (read_perm (b, o + o') v) ** r1), r2.
    eexists.
    {
      intros. symmetry. apply separate_sep_conj_perm; symmetry; auto.
      - apply when_owned_sep.
      - symmetry; auto.
    }
    eexists.
    {
      apply nonLifetime_sep_conj_perm; auto.
      apply when_nonLifetime. apply nonLifetime_read_perm. symmetry. auto.
    }
    exists Hnlr2, Hrelyr2, Hguarr2.
    split; [| split]; auto.
    {
      etransitivity; eauto. rewrite sep_conj_perm_assoc. apply sep_conj_perm_monotone; auto.
      etransitivity. 2: apply Hpwhen. etransitivity. 2: apply lte_l_sep_conj_perm. eauto.
    }
    intros p Hp Hsep'''.
    specialize (Hf (when l (read_perm (b, o + o') v) ** p)).
    destruct Hf as (q & Hq & Hsepstep & Hpre).
    - apply sep_conj_Perms_perm; auto.
      + eexists. split. eexists. reflexivity. cbn. do 2 eexists.
        split; [| split; [| split]]; try reflexivity.
        apply separate_top. rewrite sep_conj_perm_top. reflexivity.
      + symmetry. eapply separate_upwards_closed; eauto.
        rewrite sep_conj_perm_assoc. apply lte_l_sep_conj_perm.
    - apply separate_sep_conj_perm_4; auto.
      + rewrite sep_conj_perm_assoc in Hsep'''.
        symmetry. eapply separate_upwards_closed; eauto.
        apply lte_l_sep_conj_perm.
      + symmetry; auto.
      + apply when_owned_sep.
      + rewrite (sep_conj_perm_commut _ r1) in Hsep'''. rewrite sep_conj_perm_assoc in Hsep'''.
        eapply separate_upwards_closed; eauto.
        apply lte_l_sep_conj_perm.
      + eapply separate_upwards_closed; eauto.
        apply lte_r_sep_conj_perm.
    - exists q. split; [| split]; auto.
      intros si ss Hprep (Hprewhen & Hprer1 & Hsep'''').
      apply Hpre; auto.
      split; [| split]; auto.
      rewrite sep_conj_perm_assoc in Hsep'''.
      symmetry. eapply separate_upwards_closed; eauto.
      apply lte_l_sep_conj_perm.
  Qed.

    (*** Memory rules *)

  Lemma weaken_when_ptr b o o' l A (T : VPermType A) xs :
    VPtr (b, o) :: when_ptr l (W, o', T) ▷ xs ⊑
    VPtr (b, o) :: when_ptr l (R, o', T) ▷ xs.
  Proof.
    unfold when_ptr. unfold when_ptr_Perms.
    repeat intro. cbn in *.
    destruct H as (? & (? & ?) & ?). subst. destruct H0 as (? & ? & ? & ? & ? & ?).
    cbn in *.
    eexists. split. eexists. reflexivity.
    cbn. exists x, x1. split; [| split; [| split]]; eauto.
    etransitivity; eauto. apply when_monotone. apply write_lte_read.
  Qed.

  Lemma WhenPtrI A l xi yi xs ys rw o (T : VPermType A) :
    xi :: when_ptr l (rw, o, eqp yi) ▷ xs * yi :: T ▷ ys ⊑ xi :: when_ptr l (rw, o, T) ▷ ys.
  Proof.
    destruct xi; cbn.
    - rewrite sep_conj_Perms_bottom_absorb. reflexivity.
    - repeat intro. destruct a. rename p into p'.
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
  Lemma WhenPtrE A B C (P : Perms) l rw o (T : VPermType A) (xi : Value) xs ti ts (U : @PermType Si Ss B C) :
    (forall yi, P * xi :: when_ptr l (rw, o, eqp yi) ▷ tt * yi :: T ▷ xs ⊢ ti ⤳ ts ::: U) ->
    P * xi :: when_ptr l (rw, o, T) ▷ xs ⊢ ti ⤳ ts ::: U.
  Proof.
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

  Lemma WhenReadDup b o o' l y :
    VPtr (b, o) :: when_ptr l (R, o', eqp y) ▷ tt ⊑
    VPtr (b, o) :: when_ptr l (R, o', eqp y) ▷ tt * VPtr (b, o) :: when_ptr l (R, o', eqp y) ▷ tt.
  Proof.
    (* unfold when_ptr. unfold when_ptr_Perms. *)
    repeat intro.
    destruct H as (? & (v & ?) & ?). subst.
    exists (when l (read_perm (b, o + o') v)), (when l (read_perm (b, o + o') v)).
    destruct H0 as (pread & peq & Hpread & Hpeq & Hsep & Hlte).
    cbn in Hpread, Hpeq. subst.
    assert (when l (read_perm (b, o + o') v) ∈ VPtr (b, o) :: when_ptr l (R, o', eqp v) ▷ tt).
    {
      eexists. split; eauto. cbn in *. exists (when l (read_perm (b, o + o') v)), top_perm.
      split; [| split; [| split]]. 1, 2: reflexivity.
      - apply separate_top.
      - rewrite sep_conj_perm_top. reflexivity.
    }
    assert (@when Si Ss _ l (read_perm (b, o + o') v) ⊥ when l (read_perm (b, o + o') v)).
    {
      apply sep_when; auto.
      apply when_nonLifetime. apply nonLifetime_read_perm.
      symmetry.
      apply sep_when.
      apply nonLifetime_read_perm.
      apply read_separate.
    }
    split; [| split; [| split]]; auto.
    constructor; intros; eauto.
    - split; [| split]; auto. 1, 2: apply Hpread; apply Hlte; auto.
    - split; apply Hpread; apply Hlte; auto.
    - apply Hlte. constructor. left. apply Hpread. induction H1; auto.
      + destruct H1; auto.
      + etransitivity; eauto.
  Qed.

  Lemma Lifetime_Load xi yi xs l rw P Q :
    xi :: when_ptr l (rw, 0, eqp yi) ▷ xs * lowned_Perms l P Q ⊢
       load xi ⤳
       Ret tt :::
       eqp yi ∅ (xi :: when_ptr l (rw, 0, eqp yi) ▷ xs * lowned_Perms l P Q).
  Proof.
    intros p si ss Hp Hpre.
    repeat intro. pstep. unfold load. rewritebisim @bind_trigger.
    econstructor; eauto; try reflexivity.
    destruct xi as [? | [b o]].
    { destruct Hp as (? & ? & ? & ?). contradiction H. }
    destruct Hp as (pwhen & powned & Hpwhen & Hpowned & Hsep & Hlte).
    destruct Hpwhen as (? & (v & ?) & Hpwhen); subst.
    destruct Hpwhen as (pwhen' & peq & Hpwhen' & Hpeq & Hsep' & Hlte'). cbn in Hpeq. subst.
    assert (Hl: statusOf l (lget si) = Some current).
    {
      apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
      destruct Hpowned as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
      apply H0 in Hpre. destruct Hpre as (_ & ? & _).
      apply H2.
    }
    assert (Hv: read (lget si) (b, o) = Some v).
    {
      apply Hlte in Hpre. rewrite Nat.add_0_r in *.
      destruct Hpre as (Hpre & _). apply Hlte' in Hpre.
      destruct Hpre as (Hpre & _). apply Hpwhen' in Hpre.
      destruct rw.
      apply Hpre; auto.
      symmetry. apply Hpre; auto. (* TODO: why are read_perm and write_perm different *)
    }
    rewrite Hv. constructor; auto.
    cbn in Hpwhen'.
    cbn. exists top_perm, p. split; [| split; [| split]]; auto.
    - exists pwhen, powned. split; auto.
      eexists. split; eauto.
      cbn. exists pwhen', top_perm. split; [| split; [| split]]; eauto.
      apply separate_top.
      rewrite sep_conj_perm_top. etransitivity; eauto. apply lte_l_sep_conj_perm.
    - symmetry. apply separate_top.
    - rewrite sep_conj_perm_commut. apply sep_conj_perm_top.
  Qed.


  Lemma sep_step_when_write_perm l p v v' :
    sep_step (when (Ss := Ss) l (write_perm p v)) (when l (write_perm p v')).
  Proof.
    repeat intro. split; apply H; auto.
  Qed.

  Lemma Lifetime_Store xi yi l x P Q :
    xi :: when_ptr l (W, 0, eqp x) ▷ tt * lowned_Perms l P Q ⊢
    store xi yi ⤳
    Ret tt :::
    trueP ∅ (xi :: when_ptr l (W, 0, eqp yi) ▷ tt * lowned_Perms l P Q).
  Proof.
    intros p' si ss H Hpre.
    destruct H as (pwhen & powned & Hpwhen & Hpowned & Hsep & Hlte).
    destruct xi as [| [b o]]; try contradiction.
    destruct Hpwhen as (? & (v & ?) & Hwrite); subst.
    destruct Hwrite as (pw & peq & Hwritelte & Heq & Hsep' & Hlte').
    cbn in Heq. subst.
    destruct Hpowned as (r1 & r2 & Hr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte'' & Hf).
    rewrite Nat.add_0_r in *.
    assert (Hcurrent : statusOf l (lget si) = Some current).
    {
      apply Hlte in Hpre. destruct Hpre as (_ & ? & _).
      apply Hlte'' in H. destruct H as (_ & ? & _). auto.
    }
    assert (Hread: read (lget si) (b, o) = Some v).
    {
      apply Hlte in Hpre. destruct Hpre as (Hpre & ? & _).
      apply Hlte' in Hpre. destruct Hpre as (Hpre & _).
      apply Hwritelte in Hpre.
      symmetry. apply Hpre; auto.
    }
    eapply (read_success_write _ _ _ yi) in Hread.
    destruct Hread as (c' & Hwrite).
    assert (Hguar : guar pwhen (si, ss) ((lput si c'), ss)).
    {
      apply Hlte'. constructor 1. left. apply Hwritelte. cbn. right.
      split; [| split]; auto.
      repeat rewrite lGetPut.
      split; [| split; [| split]].
      - eexists. reflexivity.
      - eapply write_success_read_neq; eauto.
      - eapply write_success_sizeof; eauto.
      - eapply write_success_length; eauto.
    }
    pstep. unfold store.
    rewritebisim @bind_trigger.
    econstructor; auto.
    3: {
      assert (when l (write_perm (b, o) yi) ⊥ powned).
      {
        eapply sep_step_when_write_perm.
        symmetry. eapply separate_upwards_closed.
        2: apply Hwritelte.
        eapply separate_upwards_closed.
        2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
        symmetry. eauto.
      }
      rewrite Hwrite. constructor; auto.
      2: {
        exists top_perm, (when l (write_perm (b, o) yi) ** powned).
        split; [| split; [| split]].
        - cbn. auto.
        - apply sep_conj_Perms_perm; auto.
          + eexists. split. eexists. reflexivity.
            cbn. eexists. exists top_perm.
            split; [| split; [| split]]; eauto; try reflexivity.
            apply separate_top.
            rewrite sep_conj_perm_top. rewrite Nat.add_0_r. reflexivity.
          + exists r1, r2. exists Hr1, Hnlr1, Hnlr2, Hrelyr2, Hguarr2.
            split; [| split]; auto.
        - symmetry. apply separate_top.
        - rewrite sep_conj_perm_commut.
          rewrite sep_conj_perm_top. reflexivity.
      }
      split; [| split]; auto.
      - cbn. intros. symmetry. eapply write_success_read_eq; rewrite lGetPut; eauto.
      - respects.
        2: { apply Hlte. apply Hpre. }
        apply Hsep. apply Hguar.
    }
    - rewrite Hwrite. apply Hlte. constructor. left. apply Hguar.
    - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
      cbn in *. eapply sep_step_lte; eauto.
      eapply sep_step_lte. apply lte_l_sep_conj_perm.
      eapply sep_step_lte; eauto.
      intros ? []. constructor; auto.
  Qed.

  (*** Helper defns and lemmas *)
  Definition remove_fourth {A} (vals : list (nat * nat * nat * A)) :=
    map (fun '(a, b, c, _) => (a, b, c)) vals.
  Lemma remove_fourth_cons {A} h t :
    @remove_fourth A (cons h t) = cons ((fun '(a, b, c, _) => (a, b, c)) h) (remove_fourth t).
  Proof.
    apply map_cons.
  Qed.

  (** all the [when (read_perm)]s starred together *)
  Fixpoint when_read_perms l (vals : list (nat * nat * nat * Value))
    : @perm (Si * Ss) :=
    match vals with
    | nil => top_perm
    | cons v vals => let '(b, o, o', v') := v in
                    when l (read_perm (b, o + o') v') **
                      (when_read_perms l vals)
    end.
  Lemma when_read_perms_sep l b o v l' vals :
    when l (read_perm (b, o) v) ⊥ when_read_perms l' vals.
  Proof.
    revert l b o v.
    induction vals; intros.
    - apply separate_top.
    - destruct a as [[[b' o1] o2] v'].
      apply separate_sep_conj_perm.
      + eapply when_preserves_sep. apply read_separate.
      + apply IHvals.
      + symmetry. apply IHvals.
  Qed.

  (** stars the perms inside the list together *)
  Fixpoint star_list (vals : list (perm * {A & @VPermType Si Ss A} * Value))
    : @perm (Si * Ss) :=
    match vals with
    | nil => top_perm
    | cons v vals => let '(p, _, _) := v in
                    p ** star_list vals
    end.

  Fixpoint specs_type' (vals : list (@perm (Si * Ss) * {A & @VPermType Si Ss A} * Value)) : Type :=
    match vals with
    | nil => unit
    | cons v vals =>
        let '(_, T, _) := v in
        prod (projT1 T) (specs_type' vals)
    end.

  (** checks that each of the perms in the list are in the corresponding T in the list, plus some nonLifetime invariants on the perms *)
  Fixpoint perms_in_T_inv (vals : list (@perm (Si * Ss) * {A & @VPermType Si Ss A} * Value)) :
    specs_type' vals -> Prop.
    refine (fun xs => _).
    destruct vals as [| v vals].
    - apply True.
    - destruct v as [[p T] v].
      destruct xs as [x xs].
      apply (p ∈ v :: projT2 T ▷ x /\
               nonLifetime p /\
               rely_inv p /\
               guar_inv p /\
               pre_inv p /\
               perms_in_T_inv vals xs).
  Defined.

  Lemma star_list_invs vals c xs :
    pre (star_list vals) c ->
    perms_in_T_inv vals xs ->
    nonLifetime (star_list vals) /\
      guar_inv (star_list vals) /\
      rely_inv (star_list vals) /\
      pre_inv (star_list vals).
  Proof.
    induction vals.
    - cbn. split; [| split; [| split]].
      apply nonLifetime_top.
      apply guar_inv_top.
      apply rely_inv_top.
      apply pre_inv_top.
    - intros Hpre H. destruct a as [[p T] v]. destruct xs as [x xs].
      destruct H as (? & ? & ? & ? & ? & ?).
      split; [| split; [| split]].
      + cbn. apply nonLifetime_sep_conj_perm; auto.
        eapply IHvals; eauto.
        apply Hpre. apply Hpre.
      + apply guar_inv_sep_conj_perm; auto. eapply IHvals; eauto. apply Hpre.
      + apply rely_inv_sep_conj_perm; auto. eapply IHvals; eauto. apply Hpre.
      + apply pre_inv_sep_conj_perm; auto. eapply IHvals; eauto. apply Hpre.
  Qed.

  (** all the when_ptr (R) [Perms] starred together, with a trueP on each *)
  Fixpoint when_ptrs_trueP l (vals : list (nat * nat * nat)) :=
    match vals with
    | nil => top_Perms
    | cons v vals => let '(b, o, o') := v in
                    (VPtr (b, o) :: when_ptr l (R, o', trueP) ▷ tt) *
                      when_ptrs_trueP l vals
    end.

  Lemma when_read_perms_when_ptrs_trueP' l vals vals'
    (Hlen : length vals = length vals')
    (Heq : Forall (fun '((b, o1, o2, _), (b', o1', o2')) => b = b' /\ o1 = o1' /\ o2 = o2') (combine vals vals')) :
    when_read_perms l vals ∈ when_ptrs_trueP l vals'.
  Proof.
    revert vals' Hlen Heq.
    induction vals; intros; destruct vals'; try solve [inversion Hlen].
    { cbn. auto. }
    destruct a as [[[b o1] o2] v].
    destruct p as [[b' o1'] o2']. inversion Heq; clear Heq.
    destruct H1 as (? & ? & ?); subst.
    rename H2 into Heq. inversion Hlen; clear Hlen. rename H0 into Hlen.
    specialize (IHvals _ Hlen Heq).
    apply sep_conj_Perms_perm.
    - cbn. eexists. split. eexists. reflexivity.
      rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_top_identity.
      cbn. reflexivity.
    - apply IHvals.
    - apply when_read_perms_sep.
  Qed.

  Fixpoint ptrs_trueP (vals : list (nat * nat * nat)) : @Perms (Si * Ss) :=
    match vals with
    | nil => top_Perms
    | cons v vals => let '(b, o, o') := v in
                    (VPtr (b, o) :: ptr (W, o', trueP) ▷ tt) *
                      ptrs_trueP vals
    end.
  Fixpoint ptrs_trueP' (vals : list (nat * nat * nat)) : @Perms (Si * Ss) :=
    match vals with
    | nil => top_Perms
    | cons v vals => let '(b, o, o') := v in
                    (VPtr (b, o) :: ptr (W, o', trueP) ▷ tt) *
                      ptrs_trueP' vals
    end.
  (** all the [(write_perm)]s starred together *)
  Fixpoint write_perms (vals : list (nat * nat * nat * Value))
    : @perm (Si * Ss) :=
    match vals with
    | nil => top_perm
    | cons v vals => let '(b, o, o', v') := v in
                    (write_perm (b, o + o') v') **
                      (write_perms vals)
    end.

  Lemma split_ptrs_trueP p nov :
    p ∈ ptrs_trueP nov ->
    exists vals
      (Hlen : length nov = length vals)
      (Heq : Forall (fun '((b, o1, o2), (b', o1', o2', v)) => b = b' /\ o1 = o1' /\ o2 = o2') (combine nov vals)),
      p <= write_perms vals.
  Proof.
    revert p. induction nov; intros p Hp.
    {
      exists []. do 2 (exists; auto).
      cbn. apply top_perm_is_top.
    }
    destruct a as [[b o1] o2].
    destruct Hp as (p1 & ps & Hp1 & Hps & Hsep & Hlte).
    destruct Hp1 as (? & (v & ?) & Hp1); subst.
    rewrite sep_conj_Perms_commut in Hp1. rewrite sep_conj_Perms_top_identity in Hp1.
    specialize (IHnov ps Hps).
    destruct IHnov as (vals & Hlen & Heq & Hlte').
    exists (cons (b, o1, o2, v) vals).
    do 2 (exists; cbn; auto).
    etransitivity; eauto.
    apply sep_conj_perm_monotone; auto.
  Qed.


  Fixpoint finished_write_perms l (vals : list (nat * nat * nat * Value))
    : @perm (Si * Ss) :=
    match vals with
    | nil => lfinished l top_perm
    | cons v vals => let '(b, o, o', v') := v in
                    lfinished l (write_perm (b, o + o') v') **
                      (finished_write_perms l vals)
    end.

  Lemma finished_write_perms_separate l not b o1 o2 v c :
    pre (write_perms not) c ->
    write_perm (b, o1 + o2) v ⊥ write_perms not ->
    lfinished l (write_perm (b, o1 + o2) v) ⊥ finished_write_perms l not.
  Proof.
    revert b o1 o2 v.
    induction not; cbn; intros.
    - apply lfinished_separate. apply separate_top.
    - destruct a as [[[b' o1'] o2'] v'].
      cbn. intros.
      apply separate_sep_conj_perm.
      + apply lfinished_separate; auto.
        eapply separate_upwards_closed; eauto.
        apply lte_l_sep_conj_perm.
      + apply IHnot.
        apply H.
        eapply separate_upwards_closed; eauto.
        apply lte_r_sep_conj_perm.
      + symmetry. apply IHnot; apply H.
  Qed.

  Lemma finished_write_perms_separate' not l p (Hp : nonLifetime p) c :
    pre (write_perms not) c ->
    write_perms not ⊥ p ->
    finished_write_perms l not ⊥ p.
  Proof.
    induction not.
    - cbn. intros _ H. apply lfinished_separate'; auto.
    - destruct a as [[[b o1] o2] v].
      intros Hpre Hsep. cbn.
      symmetry. apply separate_sep_conj_perm.
      + symmetry. apply lfinished_separate'; auto.
        symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
        apply lte_l_sep_conj_perm.
      + symmetry. apply IHnot. apply Hpre.
        symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
        apply lte_r_sep_conj_perm.
      + symmetry. eapply finished_write_perms_separate; apply Hpre.
  Qed.

  Lemma lfinished_sep_conj_perm_dist' l vals :
    lfinished l (write_perms vals) <= finished_write_perms l vals.
  Proof.
    induction vals.
    - reflexivity.
    - destruct a as [[[b o1] o2] v]. cbn.
      etransitivity. apply lfinished_sep_conj_perm_dist.
      eapply sep_conj_perm_monotone; auto. reflexivity.
  Qed.

  Lemma bisim_finished {R1 R2} p p' (Q : R1 -> R2 -> Perms) t s l c1 c2
    (Hnlp : nonLifetime p) :
    bisim p Q t c1 s c2 ->
    p' <= lfinished l p ->
    pre p' (c1, c2) ->
    bisim p' (fun r1 r2 => lfinished_Perms (Ss := Ss) l (Q r1 r2)) t c1 s c2.
  Proof.
    revert p p' Q t s c1 c2 Hnlp. pcofix CIH.
    intros p p' Q t s c1 c2 Hnlp Ht Hlte Hpre.
    pstep. punfold Ht.

    revert p' Hlte Hpre.
    induction Ht; intros; auto.
    - constructor 1; auto.
      eexists. split; eauto.
    - constructor 2.
    - constructor 3; eauto.
    - constructor 4; eauto.
    - constructor 5; auto. pclearbot. right. eapply CIH; eauto.
    - apply bisim_gen_pre in Ht. destruct Ht.
      { rewrite H2. constructor 2. }
      econstructor 6; auto.
      + apply Hlte. cbn. right. split; [| split]; auto.
        * eapply nonLifetime_guar in H0; auto.
        * apply Hlte in Hpre. cbn in Hpre.
          symmetry. apply Hpre.
      + eapply sep_step_lte; eauto.
        apply lfinished_sep_step; eauto.
      + eapply IHHt; auto.
        * eapply nonLifetime_sep_step; eauto.
        * reflexivity.
        * apply Hlte in Hpre. destruct Hpre as (Hfin & Hpre).
          cbn. split; auto. apply nonLifetime_guar in H0; auto.
          cbn in H0. rewrite <- H0; auto.
    - econstructor 7; auto.
      + apply Hlte. right. split; [| split]; auto.
        apply Hlte in Hpre. cbn in Hpre.
        symmetry. apply Hpre.
      + eapply sep_step_lte; eauto.
        apply lfinished_sep_step; eauto.
      + apply bisim_gen_pre in Ht. destruct Ht; [rewrite H2; constructor |].
        eapply IHHt; auto.
        * eapply nonLifetime_sep_step; eauto.
        * reflexivity.
        * apply Hlte in Hpre. destruct Hpre as (Hfin & Hpre).
          cbn. split; auto.
    - econstructor 8; eauto.
      3: {
        pclearbot. pose proof H2 as Hsbuter.
        punfold Hsbuter. apply bisim_gen_pre in Hsbuter.
        destruct Hsbuter.
        { left. rewrite H3. pstep. constructor. }
        right. eapply CIH; auto.
        - eapply nonLifetime_sep_step; eauto.
        - apply H2.
        - reflexivity.
        - split; auto.
          eapply nonLifetime_guar in H0; auto. cbn in H0. rewrite <- H0.
          apply Hlte in Hpre. apply Hpre.
      }
      + apply Hlte. cbn. right. split; [| split]; auto.
        * eapply nonLifetime_guar in H0; auto.
        * apply Hlte in Hpre. symmetry. apply Hpre.
      + eapply sep_step_lte; eauto.
        apply lfinished_sep_step; eauto.
    - econstructor; eauto.
      + eapply sep_step_lte; eauto.
        apply lfinished_sep_step; eauto.
      + intros. specialize (H1 b).
        apply bisim_gen_pre in H1. destruct H1; [rewrite H1; constructor 2 |].
        apply H2; auto.
        * eapply nonLifetime_sep_step; eauto.
        * reflexivity.
        * apply Hlte in Hpre. split; auto. apply Hpre.
    - econstructor; auto.
      + eapply sep_step_lte; eauto.
        apply lfinished_sep_step; eauto.
      + intros. specialize (H1 b).
        apply bisim_gen_pre in H1. destruct H1; [rewrite H1; constructor 2 |].
        apply H2; auto.
        * eapply nonLifetime_sep_step; eauto.
        * reflexivity.
        * apply Hlte in Hpre. split; auto. apply Hpre.
    - econstructor 11; eauto.
      + eapply sep_step_lte; eauto.
        apply lfinished_sep_step; eauto.
      + intros. specialize (H1 b1). destruct H1 as (b2 & H1). pclearbot. exists b2.
        pose proof H1 as Hsbuter.
        punfold Hsbuter. apply bisim_gen_pre in Hsbuter.
        destruct Hsbuter; [rewrite H3; left; pstep; constructor |].
        right. eapply CIH. 2: apply H1.
        * eapply nonLifetime_sep_step; eauto.
        * reflexivity.
        * apply Hlte in Hpre. split; auto. apply Hpre.
      + intros. specialize (H2 b2). destruct H2 as (b1 & H2). pclearbot. exists b1.
        pose proof H2 as Hsbuter.
        punfold Hsbuter. apply bisim_gen_pre in Hsbuter.
        destruct Hsbuter; [rewrite H3; left; pstep; constructor |].
        right. eapply CIH. 2: apply H2.
        * eapply nonLifetime_sep_step; eauto.
        * reflexivity.
        * apply Hlte in Hpre. split; auto. apply Hpre.
  Qed.

  Lemma typing_finished {R1 R2} P (Q : R1 -> R2 -> Perms) t s l
    (HP : nonLifetime_Perms P) :
    typing (specConfig := Ss) P Q t s ->
    typing (lfinished_Perms l P) (fun r1 r2 => lfinished_Perms l (Q r1 r2)) t s.
  Proof.
    intros Ht p0 si ss (? & (p' & Hp' & ?) & Hp0) Hpre'; subst.
    destruct (HP _ Hp') as (p & Hp & Hlte & Hnlp & Hrest).
    pose proof Hpre' as H.
    cbn in Hp0.
    apply Hp0 in H. destruct H as (Hfin & Hpre).
    apply Hlte in Hpre.

    eapply bisim_finished; auto.
    apply Hnlp.
    apply Ht; auto.
    etransitivity; eauto. apply lfinished_monotone; auto.
  Qed.

  Fixpoint specs_type (vals : list (nat * nat * nat * {A & @VPermType Si Ss A})) : Type :=
    match vals with
    | nil => unit
    | cons v vals =>
        let '(_, _, _, x) := v in
        prod (projT1 x) (specs_type vals)
    end.
  Fixpoint values_type (vals : list (nat * nat * nat * {A & @VPermType Si Ss A})) : Type :=
    match vals with
    | nil => unit
    | cons v vals =>
        prod Value (values_type vals)
    end.
  Fixpoint values (vals : list (nat * nat * nat * {A & @VPermType Si Ss A})) : values_type vals :=
    match vals with
    | nil => tt
    | cons v vals =>
        let '(b, o, _, _) := v in
        (VPtr (b, o), values vals)
    end.
  Fixpoint when_ptrs_T' l (vals : list (nat * nat * nat * {A : Type & VPermType A}))
    : PermType (values_type vals) (specs_type vals) :=
    match vals with
    | nil => trueP
    | cons v vals => let '(_, _, o', x) := v in
                    when_ptr l (R, o', (projT2 x)) ⊗
                      when_ptrs_T' l vals
    end.

  Lemma specs_type_same nov nop
    (Hlen : length nov = length nop)
    (Heq: Forall (fun '((_, _, _, x), (_, x', _)) => x = x') (combine nov nop))
    : specs_type nov = specs_type' nop.
  Proof.
    revert nop Hlen Heq. induction nov; intros.
    - destruct nop; try solve [inversion Hlen].
      cbn in *. reflexivity.
    - destruct nop; try solve [inversion Hlen].
      destruct a as [[[b o] o'] T]. destruct p as [[p T'] v]. cbn in Heq.
      inversion Heq. subst.
      cbn. f_equal. eapply IHnov; auto.
  Qed.
  Definition specs_type_convert nov nop
    (Hlen : length nov = length nop)
    (Heq: Forall (fun '((_, _, _, x), (_, x', _)) => x = x') (combine nov nop))
    : specs_type nov -> specs_type' nop.
    erewrite specs_type_same; eauto.
  Defined.

  Lemma specs_type_convert_cons b o1 o2 T p v nov nop x (xs : specs_type nov)
    Hlen' Heq'
    (Hlen : length nov = length nop)
    (Heq: Forall (fun '((_, _, _, x), (_, x', _)) => x = x') (combine nov nop))
    :
    specs_type_convert (cons (b, o1, o2, T) nov) (cons (p, T, v) nop)
                       Hlen' Heq' (x, xs) =
      (x, specs_type_convert nov nop Hlen Heq xs).
  Proof.
    revert b o1 o2 T p v nop Hlen Heq Hlen' Heq' x xs.
    induction nov; intros.
    - destruct nop; try solve [inversion Hlen].
      unfold specs_type_convert, eq_rect_r. cbn.
      do 2 rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
    - destruct nop; try solve [inversion Hlen].
      destruct a as [[[b' o1'] o2'] T'].
      destruct p0 as [[p' T''] v'].
      destruct xs as [x' xs].
      inversion Hlen. inversion Heq. subst.
      rename H0 into Hlen'', H3 into Heq'', T'' into T'.
      erewrite (IHnov b' o1' o2' T').
      Unshelve. all: eauto.
      unfold specs_type_convert, eq_rect_r.
      generalize (eq_sym (specs_type_same nov nop Hlen'' Heq'')).
      generalize (eq_sym
                    (specs_type_same (cons (b, o1, o2, T) (cons (b', o1', o2', T') nov))
                       (cons (p, T, v) (cons (p', T', v') nop)) Hlen' Heq')).
      cbn.
      generalize xs.
      rewrite (specs_type_same nov nop).
      all: auto.
      intros.
      clear nov IHnov Heq' Hlen' Heq Hlen xs Hlen'' Heq''.
      do 2 rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
  Qed.

  Lemma split_when_ptrs_T' l nov (* no vals *) xs
    (HT: Forall (fun '(_, _, _, x) => forall (v : Value) (a : (projT1 x)), nonLifetime_Perms (v :: projT2 x ▷ a)) nov)
    p :
    p ∈ values nov :: when_ptrs_T' l nov ▷ xs ->
    (* we are basically only coming up with the list of vals *)
    exists not nop (* no Ts, no s *)
      (Hlen1 : length nov = length not)
      (Hlen2 : length nov = length nop)
      (Heq1: Forall (fun '((b, o1, o2, _), (b', o1', o2', _)) => b = b' /\ o1 = o1' /\ o2 = o2') (combine nov not))
      (Heq2: Forall (fun '((_, _, _, x), (_, x', _)) => x = x') (combine nov nop))
      (Heq3: Forall (fun '((_, _, _, v), (_, _, v')) => v = v') (combine not nop)),
      perms_in_T_inv nop (specs_type_convert _ _ Hlen2 Heq2 xs) /\ (* each of the perms is in v :: T ▷ xs and satisfies invariants *)
        p <= when_read_perms l not ** star_list nop.
  Proof.
    revert p HT. induction nov; intros p HT Hp.
    {
      exists [], []. cbn. do 5 (exists; auto).
      split; auto.
      rewrite sep_conj_perm_top. apply top_perm_is_top.
    }
    destruct a as [[[b o1] o2] X].
    destruct Hp as (p1 & ps & Hp1 & Hps & Hsep & Hlte).
    destruct Hp1 as (? & (v & ?) & Hp1); subst.
    destruct Hp1 as (pptr & pt' & Hpptr & Hpt' & Hsep' & Hlte').
    destruct xs as [x xs].
    inversion HT; subst; clear HT.
    rename H2 into HT.
    cbn in H1, Hpt'. specialize (H1 v x _ Hpt').
    destruct H1 as (pt & Hpt & Hptpt' & Hnlpt & Hrelypt & Hguarpt & Hprept).
    specialize (IHnov xs ps HT Hps).
    destruct IHnov as (not & nop & Hlen1 & Hlen2 & Heq1 & Heq2 & Heq3 & Hin & Hlte'').
    exists (cons (b, o1, o2, v) not), (cons (pt, X, v) nop).

    exists; cbn; auto.
    eexists. Unshelve. 2: f_equal; auto.
    exists; cbn; auto.
    eexists. Unshelve. 2: constructor; auto.
    exists; cbn; auto.

    erewrite specs_type_convert_cons.
    split; [split |]; eauto.
    etransitivity; eauto.
    rewrite sep_conj_perm_assoc.
    rewrite <- (sep_conj_perm_assoc _ pt).
    rewrite (sep_conj_perm_commut _ pt).
    rewrite sep_conj_perm_assoc.
    rewrite <- sep_conj_perm_assoc.
    apply sep_conj_perm_monotone; auto.
    etransitivity; eauto.
    apply sep_conj_perm_monotone; auto.
  Qed.

  Lemma split_ptrs_trueP' p nov :
    p ∈ ptrs_trueP' nov ->
    exists vals
      (Hlen : length nov = length vals)
      (Heq : Forall (fun '((b, o1, o2), (b', o1', o2', _)) => b = b' /\ o1 = o1' /\ o2 = o2') (combine nov vals)),
      p <= write_perms vals.
  Proof.
    revert p. induction nov; intros p Hp.
    {
      exists []. do 2 (exists; auto).
      cbn. apply top_perm_is_top.
    }
    destruct a as [[b o1] o2].
    destruct Hp as (p1 & ps & Hp1 & Hps & Hsep & Hlte).
    destruct Hp1 as (? & (v & ?) & Hp1); subst.
    rewrite sep_conj_Perms_commut in Hp1. rewrite sep_conj_Perms_top_identity in Hp1.
    specialize (IHnov ps Hps).
    destruct IHnov as (vals & Hlen & Heq & Hlte').
    exists (cons (b, o1, o2, v) vals).
    do 2 (exists; cbn; auto).
    etransitivity; eauto.
    apply sep_conj_perm_monotone; auto.
  Qed.


  (*** Actual rules *)
  Definition lownedP
    (* not yet returned *) (back : list (nat * nat * nat))
    (* just the returned ones *) front :
    @PermType Si Ss nat (specs_type front) :=
    {|
      ptApp := fun l xs =>
                 values front :: when_ptrs_T' l front ▷ xs *
                 lowned_Perms l
                   (when_ptrs_trueP l ((remove_fourth front) ++ back))
                   (ptrs_trueP' ((remove_fourth front) ++ back))
    |}.


  Lemma WhenLoad xi yi xs l rw front back xs' :
    xi :: when_ptr l (rw, 0, eqp yi) ▷ xs * l :: lownedP front back ▷ xs' ⊢
    load xi ⤳
    Ret tt :::
    eqp yi ∅ (xi :: when_ptr l (rw, 0, eqp yi) ▷ xs * l :: lownedP front back ▷ xs').
  Proof.
    intros p si ss Hp Hpre.
    repeat intro. pstep. unfold load. rewritebisim @bind_trigger.
    econstructor; eauto; try reflexivity.
    destruct xi as [? | [b o]].
    { destruct Hp as (? & ? & ? & ?). contradiction H. }
    destruct Hp as (pwhen & powned & Hpwhen & Hpowned & Hsep & Hlte).
    destruct Hpwhen as (? & (v & ?) & Hpwhen); subst.
    destruct Hpwhen as (pwhen' & peq & Hpwhen' & Hpeq & Hsep' & Hlte'). cbn in Hpeq. subst.
    assert (Hl: statusOf l (lget si) = Some current).
    {
      apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
      destruct Hpowned as (? & ? & ? & ? & ? & ?).
      destruct H0 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
      apply H2 in Hpre. destruct Hpre as (_ & ? & _).
      apply H3 in H5. apply H5.
    }
    assert (Hv: read (lget si) (b, o) = Some v).
    {
      apply Hlte in Hpre. rewrite Nat.add_0_r in *.
      destruct Hpre as (Hpre & _). apply Hlte' in Hpre.
      destruct Hpre as (Hpre & _). apply Hpwhen' in Hpre.
      destruct rw.
      apply Hpre; auto.
      symmetry. apply Hpre; auto. (* TODO: why are read_perm and write_perm different *)
    }
    rewrite Hv. constructor; auto.
    cbn in Hpwhen'.
    cbn. exists top_perm, p. split; [| split; [| split]]; auto.
    - exists pwhen, powned. split; auto.
      eexists. split; eauto.
      cbn. exists pwhen', top_perm. split; [| split; [| split]]; eauto.
      apply separate_top.
      rewrite sep_conj_perm_top. etransitivity; eauto. apply lte_l_sep_conj_perm.
    - symmetry. apply separate_top.
    - rewrite sep_conj_perm_commut. apply sep_conj_perm_top.
  Qed.

  Lemma WhenStore l A xi yi xs (P : @VPermType Si Ss A) front back xs' :
    xi :: when_ptr l (W, 0, P) ▷ xs * l :: lownedP front back ▷ xs' ⊢
       store xi yi ⤳
       Ret tt :::
       trueP ∅ (xi :: when_ptr l (W, 0, eqp yi) ▷ tt * l :: lownedP front back ▷ xs').
  Proof.
    repeat intro. pstep. unfold store. destruct xi as [| [b o]]; try contradiction.
    { destruct H as (? & ? & ? & ?). inversion H. }
    rewritebisim @bind_trigger.
    rename p into p'. rename H0 into Hpre.
    destruct H as (p & powned & Hpwhen & Hpowned & Hsep & Hlte).
    destruct Hpwhen as (? & (v & ?) & Hwrite); subst.
    destruct Hwrite as (pwhen & pp & Hpwhen & Hp' & Hsep' & Hlte').
    cbn in Hpwhen.
    rewrite Nat.add_0_r in Hpwhen.
    assert (Hl: statusOf l (lget c1) = Some current).
    {
      apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
      destruct Hpowned as (? & ? & ? & ? & ? & ?).
      destruct H0 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
      apply H2 in Hpre. destruct Hpre as (_ & ? & _).
      apply H3 in H5. apply H5.
    }

    assert (exists val, read (lget c1) (b, o) = Some val).
    {
      apply Hlte in Hpre. destruct Hpre as (Hpre & ? & _).
      apply Hlte' in Hpre. destruct Hpre as (Hpre & _).
      apply Hpwhen in Hpre. eexists.
      symmetry. apply Hpre; auto.
    }
    destruct H as (val & Hread). eapply (read_success_write _ _ _ yi) in Hread.
    destruct Hread as (c' & Hwrite).
    assert (Hguar : guar p (c1, c2) ((lput c1 c'), c2)).
    {
      apply Hlte'. constructor. left. apply Hpwhen. right.
      cbn.
      repeat rewrite lGetPut.
      split; [| split; [| split; [| split; [| split]]]]; auto.
      + eexists. reflexivity.
      + eapply write_success_read_neq; eauto.
      + eapply write_success_sizeof; eauto.
      + eapply write_success_length; eauto.
    }
    econstructor; eauto.
    3: {
      rewrite Hwrite. constructor; eauto.
      2: { exists top_perm. eexists. split; [| split; [| split]]; auto.
           3: { symmetry. apply separate_top. }
           3: { rewrite sep_conj_perm_commut. rewrite sep_conj_perm_top. reflexivity. }
           1: { exists. }
           exists (when l (write_perm (b, o) yi)), powned.
           split; [| split; [| split]]; auto.
           - eexists. split; eauto. cbn. eexists. exists top_perm.
             rewrite Nat.add_0_r.
             split; [| split; [| split]]; try reflexivity.
             + apply separate_top.
             + rewrite sep_conj_perm_top. reflexivity.
           - eapply sep_step_when_write_perm. symmetry.
             eapply separate_upwards_closed; eauto.
             eapply separate_upwards_closed. symmetry. eauto.
             etransitivity; eauto. apply lte_l_sep_conj_perm.
           - reflexivity.
      }
      cbn. split; [| split].
      - intros. symmetry. eapply write_success_read_eq; rewrite lGetPut; eauto.
      - respects.
        2: { apply Hlte. apply Hpre. }
        apply Hsep; auto.
      - eapply sep_step_when_write_perm. symmetry.
        eapply separate_upwards_closed; eauto.
        eapply separate_upwards_closed. symmetry; eauto.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
    }
    - rewrite Hwrite. apply Hlte. constructor. left. auto.
    - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
      cbn in *. eapply sep_step_lte; eauto.
      eapply sep_step_lte. apply lte_l_sep_conj_perm.
      eapply sep_step_lte; eauto.
      intros ? []. constructor; auto.
  Qed.

  Lemma StartL :
    lifetime_Perms ⊢
      beginLifetime ⤳
      Ret tt :::
      lownedP [] [] ∅ lifetime_Perms.
  Proof.
    intros p' si ss (? & (l & ?) & Hlte) Hpre; subst.
    unfold beginLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity.

    rewritebisim @bind_trigger.
    econstructor; auto.
    {
      apply Hlte in Hpre. cbn in Hpre. subst. apply Hlte. cbn.
      rewrite lGetPut.
      split; [| split].
      - eexists. reflexivity.
      - intros. symmetry. apply nth_error_app1; auto.
      - intros. apply Lifetimes_lte_app. reflexivity.
    }
    etransitivity. apply sep_step_lte'. apply Hlte. apply sep_step_beginLifetime.

    apply Hlte in Hpre. cbn in Hpre.
    econstructor.
    - cbn. do 2 rewrite lGetPut.
      split; [| split]; auto.
      + unfold statusOf. apply nth_error_app_last; auto.
      + rewrite app_length. rewrite Hpre. reflexivity.
      + apply owned_lifetime_sep. symmetry. apply separate_top. lia.
    - apply sep_conj_Perms_perm.
      + exists top_perm, (owned l top_perm nonLifetime_top).
        split; [| split; [| split]].
        { cbn. auto. }
        2: { symmetry. apply separate_top. }
        2: { rewrite sep_conj_perm_commut. rewrite sep_conj_perm_top. reflexivity. }
        exists top_perm, top_perm. eexists.
        { intros. cbn. symmetry. apply separate_top. }
        exists nonLifetime_top, nonLifetime_top, rely_inv_top, guar_inv_top.
        split; [| split].
        * cbn; auto.
        * rewrite Hpre. rewrite sep_conj_perm_commut. apply sep_conj_perm_top.
        * exists top_perm. split; auto. split. reflexivity.
          intros. cbn. auto.
      + eexists. split. eexists. reflexivity.
        cbn. reflexivity.
      + apply owned_lifetime_sep. symmetry. apply separate_top. lia.
  Qed.

  Fixpoint lfinished_Perms_T l vals
    : PermType (values_type vals) (specs_type vals) :=
    match vals with
    | nil => trueP
    | cons v vals => let '(_, _, o', x) := v in
                    finished_ptr l (W, o', (projT2 x)) ⊗
                      lfinished_Perms_T l vals
    end.

  Definition lfinishedP vals xs : @PermType Si Ss nat unit :=
    {|
      ptApp l _ := (values vals) :: lfinished_Perms_T l vals ▷ xs
    |}.

  Fixpoint combine_specs_type front back :
    specs_type front -> specs_type back -> specs_type (front ++ back).
    refine (
        match front with
        | [] => fun frontT backT => backT
        | cons f front =>
            let '(b, o, o', x) := f in
            fun frontT backT =>
              let '(f, frontT') := frontT in
              (f, combine_specs_type _ _ frontT' backT)
        end).
  Defined.

  Definition cast1 vals (a : specs_type vals) : specs_type (vals ++ []).
    rewrite app_nil_r. apply a.
  Defined.
  Definition cast2 vals (a : specs_type (vals ++ [])) : specs_type vals.
    rewrite app_nil_r in a. apply a.
  Defined.

  Lemma cast1_combine_specs_type vals xs :
    combine_specs_type vals [] xs tt = cast1 _ xs.
  Proof.
    induction vals.
    - cbn in *. destruct xs. unfold cast1. unfold eq_rect_r. cbn.
      rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
    - destruct a as [[[b o] o'] T].
      destruct xs as [x xs]. cbn.
      rewrite IHvals. clear IHvals.
      unfold cast1, eq_rect_r.
      generalize (eq_sym (app_nil_r (cons (b, o, o', T) vals))).
      cbn.
      rewrite (app_nil_r vals).
      intros.
      do 2 rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
  Qed.

  Lemma cast2_combine_specs_type vals xs :
    cast2 _ (combine_specs_type vals [] xs tt) = xs.
  Proof.
    induction vals.
    - cbn in *. destruct xs. unfold cast2.
      rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
    - destruct a as [[[b o] o'] T].
      destruct xs as [x xs]. cbn.
      rewrite <- (IHvals xs) at 2. clear IHvals.
      unfold cast2.
      generalize (app_nil_r (cons (b, o, o', T) vals)).
      generalize (combine_specs_type vals [] xs tt).
      cbn.
      rewrite (app_nil_r vals).
      intros.
      do 2 rewrite <- Eqdep.EqdepTheory.eq_rect_eq. reflexivity.
  Qed.


  Lemma typing_end_ptr_n'' l vals xs
    (HT: Forall (fun '(_, _, _, T) => forall (v : Value) (a : (projT1 T)), nonLifetime_Perms (v :: projT2 T ▷ a)) vals) :
    typing (specConfig := Ss)
      (values vals :: when_ptrs_T' l vals ▷ xs *
         lowned_Perms l
           (when_ptrs_trueP l (remove_fourth vals))
           (ptrs_trueP' (remove_fourth vals)))
      (fun _ _ => values vals :: lfinished_Perms_T l vals ▷ xs)
      (endLifetime l)
      (Ret tt).
  Proof.
    intros p si ss Hp Hpre.
    destruct Hp as (pwhens & powned & Hpwhens & Hpowned & Hsep & Hlte).
    destruct Hpowned as (r1 & r2 & Hsepr1 & Hnlr1 & Hnlr2 & Hrelyr2 & Hguarr2 & Hr2 & Hlte' & Hf).
    assert (Hcurrent: statusOf l (lget si) = Some current).
    {
      apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
      apply Hlte' in Hpre. apply Hpre.
    }
    (* read step, don't do anything here *)
    unfold endLifetime. unfold id.
    rewritebisim @bind_trigger.
    pstep. econstructor; eauto; try reflexivity.
    setoid_rewrite Hcurrent.
    (* apply the function we got from the lowned to get the write ptrs *)

    apply split_when_ptrs_T' in Hpwhens; auto.
    destruct Hpwhens as (not & nop & Hlen1 & Hlen2 & Heq1 & Heq2 & Heq3 & Hnop & Hlte'').
    edestruct Hf as (pptrs & Hpptrs & Hsepstep & Hpre').
    apply (when_read_perms_when_ptrs_trueP' l not (remove_fourth vals)).
    { rewrite <- Hlen1. unfold remove_fourth. rewrite map_length. reflexivity. }
    {
      clear Hf HT Hr2.
      clear nop Hlen2 Heq2 Heq3 Hnop Hlte''.
      revert not Hlen1 Heq1.
      induction vals; intros.
      - destruct not; try solve [inversion Hlen1].
        constructor.
      - destruct not; try solve [inversion Hlen1].
        destruct a as [[[b o1] o2] T].
        destruct p0 as [[[b' o1'] o2'] v].
        destruct xs as [x xs].
        inversion Heq1; subst; clear Heq1. rename H2 into Heq1.
        destruct H1 as (? & ? & ?); subst.
        rename b' into b, o1' into o1, o2' into o2.
        constructor. auto. apply IHvals; auto.
    }
    {
      eapply separate_upwards_closed; eauto.
      symmetry.
      eapply separate_upwards_closed.
      2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
      symmetry. auto.
    }
    apply split_ptrs_trueP' in Hpptrs.
    destruct Hpptrs as (not' & Hlen3 & Heq4 & Hlte''').
    (* the values in the read perms from the when and the write perms
       from the lowned must be the same *)
    assert (not = not').
    {
      specialize (Hpre' si ss).
      apply Hlte''' in Hpre'.
      - apply Hlte in Hpre. destruct Hpre as (Hpre & _).
        apply Hlte'' in Hpre. destruct Hpre as (Hpre & _).
        {
          clear HT Hf Hr2.
          revert vals xs not' nop Hlen1 Hlen2 Heq1 Heq2 Hnop Heq3 Hlte'' Hlen3 Heq4 Hlte''' Hpre'.
          induction not; intros.
          - destruct vals; try solve [inversion Hlen1].
            destruct not'; try solve [inversion Hlen3]; auto.
          - destruct vals; try solve [inversion Hlen1].
            destruct nop; try inversion Hlen2.
            destruct not'; try solve [inversion Hlen3]; auto.
            destruct p0 as [[[? ?] ?] ?].
            destruct p1 as [[? ?] ?].
            destruct p2 as [[[? ?] ?] ?].
            destruct a as [[[? ?] ?] ?].
            destruct xs as [x xs].
            inversion Heq1; subst; clear Heq1; rename H3 into Heq1.
            destruct H2 as (? & ? & ?); subst.
            inversion Heq2; subst; rename H3 into Heq2'.
            inversion Heq3; subst; clear Heq3; rename H3 into Heq3.
            inversion Heq4; subst; clear Heq4; rename H3 into Heq4.
            destruct H2 as (? & ? & ?); subst.
            f_equal.
            + f_equal; auto.
              clear Hlen1 Hlen3 Heq1 Heq3 Heq4 IHnot Hlte Hlte' Hlte'' Hlte'''.
              destruct Hpre as (? & _), Hpre' as (? & _).
              cbn in H, H1. rewrite HGetPut1 in H1.
              rewrite H in H1; auto.
              inversion H1. auto.
            + eapply IHnot with (vals := vals) (nop := nop); eauto.
              * apply Hpre.
              * cbn in Hnop. erewrite specs_type_convert_cons in Hnop. eapply Hnop.
                Unshelve. all: auto.
              * etransitivity; eauto. cbn.
                apply sep_conj_perm_monotone; apply lte_r_sep_conj_perm.
              * etransitivity; eauto. apply lte_r_sep_conj_perm.
              * apply Hpre'.
        }
      - apply Hlte in Hpre. destruct Hpre as (Hpre & _).
        apply Hlte'' in Hpre. destruct Hpre as (Hpre & _).
        rewrite replace_list_index_eq; auto. rewrite lPutGet; auto.
      - apply Hlte'. apply Hlte.
        rewrite replace_list_index_eq; auto. rewrite lPutGet; auto.
    }
    subst. rename not' into not.

    (* End the lifetime *)
    rewritebisim @bind_trigger.
    constructor 6 with (p' := finished_write_perms l not ** star_list nop); unfold id; auto.
    { (* lowned allows us to do this *)
      apply Hlte. constructor 1. right.
      apply Hlte'. constructor 1. right.
      cbn. right.
      repeat rewrite lGetPut.
      split; [| split; [| split]].
      - intros. apply nth_error_replace_list_index_neq; auto.
        apply nth_error_Some. intros Hnone.
        unfold statusOf, Lifetimes in Hcurrent.
        rewrite Hcurrent in Hnone. inversion Hnone.
      - apply replace_list_index_length; auto. apply nth_error_Some. intro Hnone.
        unfold statusOf, Lifetimes in Hcurrent. rewrite Hcurrent in Hnone. inversion Hnone.
      - unfold statusOf. apply nth_error_replace_list_index_eq.
      - rewrite lPutPut, replace_list_index_twice. reflexivity.
    }
    { (* lowned sep_steps to lfinished *)
      eapply sep_step_lte; eauto.
      rewrite sep_conj_perm_commut.
      eapply sep_step_lte.
      {
        apply sep_conj_perm_monotone.
        - etransitivity. apply Hlte'. apply lte_r_sep_conj_perm.
        - etransitivity. apply Hlte''. apply lte_r_sep_conj_perm.
      }
      apply sep_step_sep_conj_l.
      {
        eapply separate_upwards_closed.
        2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
        symmetry. eapply separate_upwards_closed; eauto.
        etransitivity. 2: apply lte_r_sep_conj_perm. eauto.
      }
      etransitivity.
      etransitivity. 2: eapply sep_step_owned_finished.
      apply owned_sep_step; eauto.
      eapply sep_step_lte'.
      etransitivity. apply lfinished_monotone; eauto.
      apply lfinished_sep_conj_perm_dist'.
    }
    constructor.
    - (* the precondition still holds *)
      assert (Hpre'': pre (write_perms not) (lput si (replace_list_index (lget si) l Lifetime.finished), ss)).
      {
        apply Hlte'''. eapply Hpre'.
        - apply Hlte''. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
        - apply Hlte'. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
      }
      split; [| split].
      + clear Hlen1 Hlen3 Heq1 Heq3 Heq4 Hlte''' Hpre' Hr2 Hf.
        induction not; cbn; intros.
        { split; auto. rewrite lGetPut. symmetry. apply nth_error_replace_list_index_eq. }
        destruct a as [[[b o1] o2] v]. cbn.
        assert (Hv : read (lget si) (b, o1 + o2) = Some v).
        {
          apply Hlte in Hpre. destruct Hpre as (Hpre & _).
          apply Hlte'' in Hpre. cbn in Hpre.
          apply Hpre; auto.
        }
        split; [| split].
        * split. { rewrite lGetPut. symmetry. apply nth_error_replace_list_index_eq. }
          rewrite HGetPut1. auto.
        * apply IHnot; auto.
          -- etransitivity; eauto.
             cbn. rewrite sep_conj_perm_assoc. apply lte_r_sep_conj_perm.
          -- apply Hpre''.
        * eapply finished_write_perms_separate; apply Hpre''.
      + assert (pwhens <= star_list nop).
        {
          etransitivity; eauto.
          apply lte_r_sep_conj_perm.
        }
        clear Heq3. clear r2 not Hlen1 Heq1 Hlte'' Hlen3 Heq4 Hlte''' Hpre' Hpre'' Hnlr2 Hrelyr2 Hguarr2 Hr2 Hlte' Hf Hsepstep.
        revert vals xs HT Hlen2 Heq2 Hnop.
        induction nop; intros; cbn; auto.
        destruct vals; try solve [inversion Hlen2].
        destruct a as [[p' ?] ?].
        destruct p0 as [[[b o] o'] T].
        destruct xs as [x xs].
        inversion Heq2; subst.
        rename H3 into Heq2'.
        cbn in Hnop. erewrite specs_type_convert_cons in Hnop.
        split; [| split].
        * apply Hnop. apply H. apply Hlte. apply Hpre.
        * eapply IHnop with (vals := vals); eauto.
          -- etransitivity; eauto. cbn.
             (* apply sep_conj_perm_monotone. reflexivity. *)
             apply lte_r_sep_conj_perm.
          -- inversion HT. auto.
          -- eapply Hnop.
        * apply Hlte in Hpre. destruct Hpre as (Hpre & _).
          apply H in Hpre. apply Hpre.
      + apply Hlte in Hpre. destruct Hpre as (Hpre & _).
        apply Hlte'' in Hpre. destruct Hpre as (_ & Hpre & _).
        destruct (star_list_invs _ _ _ Hpre Hnop) as (? & ? & ? & ?).

        eapply finished_write_perms_separate'; auto.
        apply Hpre''.
        symmetry. eapply separate_upwards_closed. 2: apply Hlte'''.
        symmetry. apply Hsepstep.
        symmetry.
        eapply owned_sep; eauto.
        symmetry.
        eapply separate_upwards_closed.
        2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
        symmetry.
        eapply separate_upwards_closed.
        2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
        auto.
    - (* we can put everything back together again, hiding the values *)
      clear Hf HT.
      assert (Hpre'': pre (write_perms not) (lput si (replace_list_index (lget si) l Lifetime.finished), ss)).
      {
        apply Hlte'''. eapply Hpre'.
        - apply Hlte''. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
        - apply Hlte'. apply Hlte. rewrite replace_list_index_eq; auto.
          rewrite lPutGet. auto.
      }
      clear Hpre' Hr2.
      (* remember (remove_fourth vals). *)
      revert not nop Hlen1 Hlen2 Heq1 Heq2 Heq3 Hlen3 Heq4 Hnop Hlte'' Hlte''' Hpre'' Hpre.
      induction vals; intros.
      + destruct not; try solve [inversion Hlen1].
        destruct nop; try solve [inversion Hlen2].
        cbn. auto.
      + destruct not; try solve [inversion Hlen1].
        destruct nop; try solve [inversion Hlen2].
        destruct p0 as [[[b o1] o2] v'].
        destruct p1 as [[p' T] v].
        inversion Heq3; subst; clear Heq3. rename H2 into Heq3.
        destruct a as [[[b' o1'] o2'] x'].
        inversion Heq1; clear Heq1; subst. rename H2 into Heq1.
        destruct H1 as (? & ? & ?). subst.
        inversion Heq2; subst. rename H2 into Heq2'.
        destruct xs as [x xs].
        erewrite specs_type_convert_cons in Hnop.
        Unshelve. all: auto.
        2: eapply nonLifetime_sep_step; eauto.
        exists (lfinished l (write_perm (b, o1 + o2) v) ** p'), (finished_write_perms l not ** star_list nop).
        assert (pwhens <= star_list (cons (p', T, v) nop)).
        {
          etransitivity.
          2: apply lte_r_sep_conj_perm. eauto.
        }
        split; [| split; [| split]].
        * cbn. eexists. split. eexists. reflexivity.
          cbn. do 2 eexists. split; [| split; [| split]].
          4: reflexivity. reflexivity. apply Hnop.
          apply lfinished_separate'. apply Hnop.
          symmetry. eapply separate_upwards_closed.
          2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
          symmetry. apply Hsepstep.
          symmetry. eapply owned_sep; try apply Hnop; auto.
          eapply separate_upwards_closed.
          2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
          symmetry.
          eapply separate_upwards_closed.
          2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
          symmetry. auto.
        * eapply IHvals; auto.
          -- clear xs IHvals Heq4 Hlen3 Hlen2 Heq2 Hpre'' Hlte''' Hlte'' Hpre Heq3 Heq2' Hnop.
             revert not Hlen1 Heq1.
             induction vals; intros.
             ++ destruct not; constructor.
             ++ destruct not; constructor.
                destruct a as [[[? ?] ?] ?].
                destruct p0 as [[[? ?] ?] ?].
                inversion Heq1; subst. destruct H2 as (? & ? & ?); subst. auto.
                apply IHvals; auto.
                inversion Heq1; subst. auto.
          -- apply Hnop.
          -- etransitivity. apply Hlte''.
             apply sep_conj_perm_monotone; apply lte_r_sep_conj_perm.
          -- etransitivity; eauto. apply lte_r_sep_conj_perm.
          -- apply Hpre''.
        * apply separate_sep_conj_perm_4.
          -- apply lfinished_separate'. apply Hnop.
             (* copied from above *)
             symmetry. eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
             symmetry. apply Hsepstep.
             symmetry. eapply owned_sep; try apply Hnop; auto.
             eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
             symmetry.
             eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
             symmetry. auto.
          -- eapply finished_write_perms_separate; apply Hpre''.
          -- apply Hlte in Hpre. destruct Hpre as (Hpre & _).
             apply Hlte'' in Hpre. destruct Hpre as (_ & Hpre & _).
             destruct Hpre as (_ & Hpre & _).
             destruct Hnop as (? & ? & ? & ? & ? & Hnop).
             destruct (star_list_invs _ _ _ Hpre Hnop) as (? & ? & ? & ?).
             apply lfinished_separate'; auto.

             symmetry. eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
             symmetry. apply Hsepstep.
             symmetry. eapply owned_sep; try apply Hnop; auto.
             eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
             symmetry.
             eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
             symmetry. auto.
          -- symmetry. eapply finished_write_perms_separate'. apply Hnop.
             apply Hpre''.

             symmetry. eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
             symmetry. apply Hsepstep.
             symmetry. eapply owned_sep; try apply Hnop; auto.
             eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
             symmetry.
             eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_l_sep_conj_perm. eauto. }
             symmetry. auto.
          -- apply Hlte in Hpre. destruct Hpre as (Hpre & _).
             apply Hlte'' in Hpre. destruct Hpre as (_ & Hpre & _).
             apply Hpre.
          -- apply Hlte in Hpre. destruct Hpre as (Hpre & _).
             apply Hlte'' in Hpre. destruct Hpre as (_ & Hpre & _).
             destruct Hpre as (_ & Hpre & _).
             destruct Hnop as (? & ? & ? & ? & ? & Hnop).
             destruct (star_list_invs _ _ _ Hpre Hnop) as (? & ? & ? & ?).
             eapply finished_write_perms_separate'; auto.
             apply Hpre''.

             symmetry. eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
             symmetry. apply Hsepstep.
             symmetry. eapply owned_sep; try apply Hnop; auto.
             eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
             symmetry.
             eapply separate_upwards_closed.
             2: { etransitivity. 2: apply lte_r_sep_conj_perm. eauto. }
             symmetry. auto.
        * rewrite sep_conj_perm_assoc.
          rewrite (sep_conj_perm_commut p').
          rewrite sep_conj_perm_assoc.
          rewrite (sep_conj_perm_commut _ p').
          rewrite <- sep_conj_perm_assoc. reflexivity.
  Qed.

  Lemma StopL
    vals l xs
    (HT: Forall (fun '(_, _, _, T) =>
                   forall (v : Value) (a : projT1 T), nonLifetime_Perms (v :: projT2 T ▷ a))
           vals) :
    l :: lownedP [] vals ▷ xs ⊢
      endLifetime l ⤳
      Ret tt :::
      trueP ∅ l :: lfinishedP vals xs ▷ tt.
  Proof.
    cbn.
    intros p si ss Hp Hpre.
    rewrite app_nil_r in *.
    eapply bisim_lte.
    apply typing_end_ptr_n''; eauto.
    repeat intro.
    rewrite sep_conj_Perms_top_identity. auto.
  Qed.

  Lemma ReturnL b o o' A (T : VPermType A) front back xs l xs'
    (Hnlp : forall (xi : Value) (xs0 : A), nonLifetime_Perms (xi :: T ▷ xs0)):
    VPtr (b, o) :: when_ptr l (R, o', T) ▷ xs *
    l :: lownedP (back ++ [(b, o, o')]) front ▷ xs' ⊑

    l :: lownedP back (cons (b, o, o', existT _ A T) front) ▷ (xs, xs').
  Proof.
    unfold lownedP.
    unfold ptApp.
    rewrite sep_conj_Perms_assoc.
    apply sep_conj_Perms_monotone.
    - unfold when_ptrs_T'.
      fold when_ptrs_T'. unfold timesPT. unfold values. fold values.
      unfold fst, snd, projT2.
      apply sep_conj_Perms_monotone; reflexivity.
    - apply Proper_eq_Perms_lowned_Perms; auto.
      + rewrite remove_fourth_cons.
        rewrite <- app_comm_cons.
        rewrite app_assoc.
        remember (remove_fourth front ++ back).
        clear Heql0.
        induction l0.
        * reflexivity.
        * rewrite <- app_comm_cons. unfold when_ptrs_trueP at 2. fold when_ptrs_trueP.
          destruct a as [[? ?] ?].
          rewrite <- IHl0.
          unfold when_ptrs_trueP. fold when_ptrs_trueP.
          do 2 rewrite sep_conj_Perms_assoc.
          rewrite (sep_conj_Perms_commut (VPtr (n, n0) :: when_ptr l (R, n1, trueP) ▷ tt)).
          reflexivity.
      + rewrite remove_fourth_cons.
        rewrite <- app_comm_cons.
        rewrite app_assoc.
        remember (remove_fourth front ++ back).
        clear Heql0.
        induction l0.
        * reflexivity.
        * rewrite <- app_comm_cons. unfold ptrs_trueP' at 2. fold ptrs_trueP'.
          destruct a as [[? ?] ?].
          rewrite <- IHl0.
          unfold ptrs_trueP'. fold ptrs_trueP'.
          do 2 rewrite sep_conj_Perms_assoc.
          rewrite (sep_conj_Perms_commut (VPtr (b, o) :: ptr (W, o', trueP) ▷ tt)).
          reflexivity.
  Qed.

  Lemma SplitL b o o' A (T : VPermType A) front back xs l xs'
    (Hnlp : forall (xi : Value) (xs0 : A), nonLifetime_Perms (xi :: T ▷ xs0)):
    VPtr (b, o) :: ptr (W, o', T) ▷ xs *
      l :: lownedP back front ▷ xs' ⊑

    VPtr (b, o) :: when_ptr l (W, o', T) ▷ xs *
      l :: lownedP (back ++ [(b, o, o')]) front ▷ xs'.
  Proof.
    etransitivity.
    {
      unfold lownedP. unfold ptApp.
      rewrite sep_conj_Perms_commut.
      rewrite <- sep_conj_Perms_assoc.
      apply sep_conj_Perms_monotone; [reflexivity |].
      rewrite sep_conj_Perms_commut.
      apply split_Perms_T; auto.
    }
    rewrite sep_conj_Perms_commut.
    rewrite <- sep_conj_Perms_assoc.
    apply sep_conj_Perms_monotone; [reflexivity |].
    unfold lownedP. unfold ptApp.
    rewrite sep_conj_Perms_commut.
    apply sep_conj_Perms_monotone; [reflexivity |].
    apply Proper_eq_Perms_lowned_Perms; auto.
    - setoid_rewrite sep_conj_Perms_commut.
      rewrite app_assoc.
      remember (remove_fourth front ++ back). clear Heql0.
      induction l0.
      + cbn. rewrite sep_conj_Perms_commut. reflexivity.
      + rewrite <- app_comm_cons. unfold when_ptrs_trueP. fold when_ptrs_trueP.
        destruct a as [[? ?] ?].
        rewrite <- sep_conj_Perms_assoc.
        rewrite <- IHl0. reflexivity.
    - setoid_rewrite sep_conj_Perms_commut.
      rewrite app_assoc.
      remember (remove_fourth front ++ back).  clear Heql0.
      induction l0.
      + cbn. rewrite sep_conj_Perms_commut. reflexivity.
      + rewrite <- app_comm_cons. unfold ptrs_trueP'. fold ptrs_trueP'.
        destruct a as [[? ?] ?].
        rewrite <- sep_conj_Perms_assoc.
        rewrite <- IHl0. reflexivity.
  Qed.

  Lemma lifetime_ex1 b o xs xs' :
    lifetime_Perms * (VPtr (b, o)) :: ptr (W, 0, IsNat Si Ss) ▷ xs * (VPtr (b, o)) :: ptr (W, 1, IsNat Si Ss) ▷ xs' ⊢
      (l <- beginLifetime ;; endLifetime l;; Ret l) ⤳
      (Ret tt) :::
      (lfinishedP [(b, o, 0, existT _ {nat & unit} isNat);
                   (b, o, 1, existT _ {nat & unit} isNat)]
         (xs, (xs', tt)) ∅ lifetime_Perms).
  Proof.
    replace (Ret tt) with (Ret tt;; Ret tt : itree (sceE Ss) unit).
    2: {
      apply bisimulation_is_eq. rewrite bind_ret_l. reflexivity.
    }
    eapply Bind.
    { rewrite <- sep_conj_Perms_assoc. apply Frame. apply StartL. }
    intros l [].
    eapply Weak; [apply PermsE | reflexivity |].
    eapply Weak; [| reflexivity |].
    apply sep_conj_Perms_monotone; [apply PermsE | reflexivity].
    rewrite sep_conj_Perms_commut.
    rewrite sep_conj_Perms_assoc.
    apply Frame.

    eapply Weak; [| reflexivity |].
    {
      rewrite sep_conj_Perms_commut.
      rewrite sep_conj_Perms_assoc.
      apply sep_conj_Perms_monotone; [| reflexivity].
      rewrite sep_conj_Perms_commut.
      apply SplitL.
      apply nonLifetime_IsNat.
    }
    eapply Weak; [| reflexivity |].
    {
      rewrite <- sep_conj_Perms_assoc.
      apply sep_conj_Perms_monotone; [reflexivity |].
      rewrite sep_conj_Perms_commut.
      apply SplitL.
      apply nonLifetime_IsNat.
    }
    eapply Weak; [| reflexivity |].
    {
      apply sep_conj_Perms_monotone; [reflexivity |].
      etransitivity.
      apply sep_conj_Perms_monotone; [apply weaken_when_ptr | reflexivity].
      apply ReturnL.
      apply nonLifetime_IsNat.
    }
    eapply Weak; [| reflexivity |].
    {
      etransitivity.
      apply sep_conj_Perms_monotone; [apply weaken_when_ptr | reflexivity].
      apply ReturnL.
      apply nonLifetime_IsNat.
    }

    replace (Ret tt) with (Ret tt;; Ret tt : itree (sceE Ss) unit).
    2: {
      apply bisimulation_is_eq. rewrite bind_ret_l. reflexivity.
    }

    eapply Bind.
    {
      apply StopL.
      constructor.
      apply nonLifetime_IsNat.
      constructor. apply nonLifetime_IsNat.
      constructor.
    }

    intros [] [].
    eapply Weak; [apply PermsE | reflexivity |].
    eapply Weak; [ | reflexivity |].
    apply lte_r_sep_conj_Perms.
    apply Ret_.
  Qed.

  Axiom t : Value -> Value -> itree (sceE Si) unit.
  Axiom typing_t :
    forall p p' v l front back xs,
      (l :: lownedP front back ▷ xs *
         p :: when_ptr l (R, 0, eqp v) ▷ tt *
         p' :: when_ptr l (R, 0, eqp v) ▷ tt) ⊢
        (t p p') ⤳
        (Ret tt) :::
        (trueP ∅
           (l :: lownedP front back ▷ xs *
              p :: when_ptr l (R, 0, eqp v) ▷ tt *
              p' :: when_ptr l (R, 0, eqp v) ▷ tt)).

  Lemma lifetime_ex2 b o xs :
    lifetime_Perms *
      (VPtr (b, o)) :: ptr (W, 0, IsNat Si Ss) ▷ xs ⊢
        (l <- beginLifetime;; t (VPtr (b, o)) (VPtr (b, o));; endLifetime l;; Ret l) ⤳
        (Ret tt) :::
        (lfinishedP [(b, o, 0, existT _ {nat & unit} isNat)] (xs, tt) ∅ lifetime_Perms).
  Proof.
    (** Start the lifetime *)
    replace (Ret tt) with (Ret tt;; Ret tt : itree (sceE Ss) unit).
    2: {
      apply bisimulation_is_eq. rewrite bind_ret_l. reflexivity.
    }
    eapply Bind.
    {
      apply Frame.
      apply StartL.
    }

    (** Now we have the lifetime [l] *)
    intros l [].
    eapply Weak; [apply PermsE | reflexivity |].
    eapply Weak; [| reflexivity |].
    apply sep_conj_Perms_monotone; [apply PermsE | reflexivity].
    rewrite sep_conj_Perms_commut.
    rewrite sep_conj_Perms_assoc.

    (** Hide the lifetime alloc perm *)
    apply Frame.

    (** Split the write type *)
    eapply Weak; [| reflexivity |].
    {
      rewrite sep_conj_Perms_commut.
      rewrite sep_conj_Perms_commut.
      apply SplitL.
      apply nonLifetime_IsNat.
    }

    (** Weaken write into a read *)
    eapply Weak; [| reflexivity |].
    {
      apply sep_conj_Perms_monotone; [| reflexivity].
      apply weaken_when_ptr.
    }

    (** Move out the content type *)
    rewrite sep_conj_Perms_commut.
    apply WhenPtrE. intros v.

    (** duplicate the read type *)
    eapply Weak; [| reflexivity |].
    {
      rewrite sep_conj_Perms_commut.
      rewrite sep_conj_Perms_assoc.
      apply sep_conj_Perms_monotone; [reflexivity |].
      eapply WhenReadDup.
    }

    (** Handle [t] *)
    rewrite <- sep_conj_Perms_assoc.
    rewrite sep_conj_Perms_commut.
    replace (Ret tt) with (Ret tt;; Ret tt : itree (sceE Ss) unit).
    2: {
      apply bisimulation_is_eq. rewrite bind_ret_l. reflexivity.
    }
    eapply Bind.
    {
      apply Frame.
      rewrite sep_conj_Perms_assoc.
      apply typing_t.
    }

    (** Drop the trueP and the extra read type *)
    intros [] [].
    eapply Weak; [apply PermsE | reflexivity |].
    eapply Weak; [| reflexivity |].
    {
      apply sep_conj_Perms_monotone; [| reflexivity].
      apply PermsE.
    }
    eapply Weak; [| reflexivity |].
    {
      repeat rewrite <- sep_conj_Perms_assoc.
      apply lte_r_sep_conj_Perms.
    }
    eapply Weak; [| reflexivity |].
    {
      apply sep_conj_Perms_monotone; [reflexivity |].
      apply lte_r_sep_conj_Perms.
    }
    (** Put the isNat type back in the pointer type *)
    eapply Weak; [| reflexivity |].
    {
      apply sep_conj_Perms_monotone; [reflexivity |].
      apply WhenPtrI.
    }
    (** Return the read type to the lownedP *)
    eapply Weak; [| reflexivity |].
    {
      rewrite sep_conj_Perms_commut.
      apply ReturnL.
      apply nonLifetime_IsNat.
    }

    (** Handle the endLifetime *)
    replace (Ret tt) with (Ret tt;; Ret tt : itree (sceE Ss) unit).
    2: {
      apply bisimulation_is_eq. rewrite bind_ret_l. reflexivity.
    }
    eapply Bind.
    eapply StopL.
    constructor. apply nonLifetime_IsNat. constructor.

    (** Handle the final ret l *)
    intros [] [].
    eapply Weak; [| reflexivity | apply Ret_].
    etransitivity. apply PermsE.
    apply lte_r_sep_conj_Perms.
  Qed.

End Perms.

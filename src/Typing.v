(* begin hide *)
From Coq Require Import
     Structures.Equalities
     Classes.Morphisms
     Classes.RelationClasses
     Relations.Relation_Operators
     Relations.Operators_Properties
     ProofIrrelevance.

From Heapster Require Import
     Utils
     Permissions
     SepStep.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Exception
     Events.Nondeterminism
     Eq.Eqit
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import ITreeNotations.
Local Open Scope itree_scope.
(* end hide *)

(** * Bisimulation axiom *)
(** We make use of the [bisimulation_is_eq] axiom from the ITrees library.
    This axiom is used to avoid setoid rewriting up to strong bisimulation,
    [eq_itree eq]. This is used for convenience, we could also prove Proper
    instances for our definitions. *)
Ltac rewritebisim lem := pose proof lem as bisim;
                         eapply bisimulation_is_eq in bisim;
                         rewrite bisim;
                         clear bisim.

Ltac rewritebisim_in lem H := pose proof lem as bisim;
                              eapply bisimulation_is_eq in bisim;
                              rewrite bisim in H;
                              clear bisim.

Lemma throw_vis {E R} `{exceptE unit -< E} (k : void -> itree E R) :
  vis (Throw tt) k = throw tt.
Proof.
  apply bisimulation_is_eq. pstep. unfold throw.
  constructor. intros. inversion v.
Qed.

Lemma throw_bind {E R1 R2} `{exceptE unit -< E} (k : R1 -> itree E R2) :
  x <- throw tt;; k x = throw tt.
Proof.
  unfold throw. rewritebisim @bind_vis. apply throw_vis.
Qed.

(** * Stuttering bisimulation *)
Section bisim.
  Context {config specConfig : Type}.

  Inductive bisim_gen {R1 R2 : Type} (bisim : perm -> (R1 -> R2 -> Perms) -> itree (sceE config) R1 -> config -> itree (sceE specConfig) R2 -> specConfig -> Prop)
            (p : perm) (Q : R1 -> R2 -> Perms) :
    itree (sceE config) R1 -> config -> itree (sceE specConfig) R2 -> specConfig -> Prop :=
  | bisim_gen_ret r1 c1 r2 c2 :
      pre p (c1, c2) ->
      p ∈ Q r1 r2 ->
      bisim_gen bisim p Q (Ret r1) c1 (Ret r2) c2
  | bisim_gen_err t1 c1 c2 :
      bisim_gen bisim p Q t1 c1 (throw tt) c2
  | bisim_gen_tau_L t1 c1 t2 c2 :
      pre p (c1, c2) ->
      bisim_gen bisim p Q t1 c1 t2 c2 ->
      bisim_gen bisim p Q (Tau t1) c1 t2 c2
  | bisim_gen_tau_R t1 c1 t2 c2 :
      pre p (c1, c2) ->
      bisim_gen bisim p Q t1 c1 t2 c2 ->
      bisim_gen bisim p Q t1 c1 (Tau t2) c2
  | bisim_gen_tau t1 c1 t2 c2 :
      pre p (c1, c2) ->
      bisim p Q t1 c1 t2 c2 ->
      bisim_gen bisim p Q (Tau t1) c1 (Tau t2) c2
  | bisim_gen_modify_L f k c1 t2 c2 p' :
      pre p (c1, c2) ->
      guar p (c1, c2) (f c1, c2) ->
      sep_step p p' ->
      bisim_gen bisim p' Q (k c1) (f c1) t2 c2 ->
      bisim_gen bisim p Q (vis (Modify f) k) c1 t2 c2
  | bisim_gen_modify_R t1 c1 f k c2 p' :
      pre p (c1, c2) ->
      guar p (c1, c2) (c1, f c2) ->
      sep_step p p' ->
      bisim_gen bisim p' Q t1 c1 (k c2) (f c2) ->
      bisim_gen bisim p Q t1 c1 (vis (Modify f) k) c2
  | bisim_gen_modify f1 k1 c1 f2 k2 c2 p' :
      pre p (c1, c2) ->
      guar p (c1, c2) (f1 c1, f2 c2) ->
      sep_step p p' ->
      (* TODO: f1 c1 satisfies the spred *)
      bisim p' Q (k1 c1) (f1 c1) (k2 c2) (f2 c2) ->
      bisim_gen bisim p Q (vis (Modify f1) k1) c1 (vis (Modify f2) k2) c2
  | bisim_gen_choice_L k c1 t2 c2 p' :
      pre p (c1, c2) ->
      sep_step p p' ->
      (forall b, bisim_gen bisim p' Q (k b) c1 t2 c2) ->
      bisim_gen bisim p Q (vis Or k) c1 t2 c2
  | bisim_gen_choice_R t1 c1 k c2 p' :
      pre p (c1, c2) ->
      sep_step p p' ->
      (forall b, bisim_gen bisim p' Q t1 c1 (k b) c2) ->
      bisim_gen bisim p Q t1 c1 (vis Or k) c2
  | bisim_gen_choice k1 c1 k2 c2 p' :
      pre p (c1, c2) ->
      sep_step p p' ->
      (forall b1, exists b2, bisim p' Q (k1 b1) c1 (k2 b2) c2) ->
      (forall b2, exists b1, bisim p' Q (k1 b1) c1 (k2 b2) c2) ->
      bisim_gen bisim p Q (vis Or k1) c1 (vis Or k2) c2
  .

  Lemma bisim_gen_mon {R1 R2} : monotone6 (@bisim_gen R1 R2).
  Proof.
    repeat intro. induction IN; subst; try solve [econstructor; eauto]; auto.
    econstructor 11; eauto; intros.
    - destruct (H1 b1). eexists; eauto.
    - destruct (H2 b2). eexists; eauto.
  Qed.
  #[local] Hint Resolve bisim_gen_mon : paco.

  Definition bisim {R1 R2} := paco6 (@bisim_gen R1 R2) bot6.

  Lemma bisim_gen_pre {R1 R2} r p (Q : R1 -> R2 -> Perms) t s c1 c2 :
    bisim_gen r p Q t c1 s c2 ->
    s = throw tt \/ pre p (c1, c2).
  Proof.
    inversion 1; auto.
  Qed.

  Lemma bisim_lte {R1 R2} p Q Q' (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2 :
    bisim p Q t c1 s c2 -> (forall r1 r2, Q r1 r2 ⊑ Q' r1 r2) -> bisim p Q' t c1 s c2.
  Proof.
    revert p Q Q' t s c1 c2. pcofix CIH. intros p Q Q' t s c1 c2 Htyping Hlte.
    punfold Htyping. pstep.
    induction Htyping; pclearbot; try solve [econstructor; eauto].
    - constructor; eauto. apply Hlte. auto.
    - econstructor 11; eauto; intros.
      + destruct (H1 b1). eexists. right. eapply CIH; eauto. pclearbot. apply H3.
      + destruct (H2 b2). eexists. right. eapply CIH; eauto. pclearbot. apply H3.
  Qed.

  (** * Typing *)
  Definition typing {R1 R2} P Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :=
    forall p c1 c2, p ∈ P -> pre p (c1, c2) -> bisim p Q t c1 s c2.

  Lemma typing_lte {R1 R2} P P' Q Q' (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing P Q t s ->
    P' ⊑ P ->
    (forall r1 r2, Q r1 r2 ⊑ Q' r1 r2) ->
    typing P' Q' t s.
  Proof.
    repeat intro.
    eapply bisim_lte; eauto.
  Qed.

  Lemma typing_ret {R1 R2} P Q (r1 : R1) (r2 : R2) :
    P ⊑ Q r1 r2 -> typing P Q (Ret r1) (Ret r2).
  Proof.
    repeat intro. pstep. constructor; auto.
  Qed.

  Lemma rewrite_spin {E R} : (ITree.spin : itree E R) = Tau (ITree.spin).
  Proof.
    intros. apply bisimulation_is_eq.
    ginit. gcofix CIH. gstep. unfold ITree.spin. constructor.
    apply Reflexive_eqit_gen_eq.
  Qed.


  Lemma typing_spin {R1 R2} P Q :
    typing P Q (ITree.spin : itree (sceE config) R1) (ITree.spin : itree (sceE specConfig) R2).
  Proof.
    repeat intro. pcofix CIH. pstep.
    rewrite (@rewrite_spin _ R1). rewrite (@rewrite_spin _ R2).
    constructor 5; auto.
  Qed.

  Lemma typing_bottom {R1 R2} Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing bottom_Perms Q t s.
  Proof.
    repeat intro. inversion H.
  Qed.

  Lemma bisim_top {R1 R2} p Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2:
    bisim p Q t c1 s c2 -> bisim p (fun _ _ => top_Perms) t c1 s c2.
  Proof.
    revert p Q t s c1 c2. pcofix CIH. intros. pstep. punfold H0.
    induction H0; pclearbot; try solve [econstructor; cbn; eauto].
    econstructor 11; eauto; intros.
    - destruct (H1 b1). eexists. right. eapply CIH; pclearbot; apply H3.
    - destruct (H2 b2). eexists. right. eapply CIH; pclearbot; apply H3.
  Qed.

  Lemma typing_top {R1 R2} P Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) :
    typing P Q t s -> typing P (fun _ _ => top_Perms) t s.
  Proof.
    repeat intro. eapply bisim_top; eauto.
  Qed.

  Lemma bisim_bind {R1 R2 S1 S2} (p : perm) (Q : R1 -> S1 -> Perms) (R : R2 -> S2 -> Perms)
        (t1 : itree (sceE config) R1) (t2 : R1 -> itree (sceE config) R2)
        (s1 : itree (sceE specConfig) S1) (s2 : S1 -> itree (sceE specConfig) S2)
        c1 c2 r :
    pre p (c1, c2) ->
    bisim p Q t1 c1 s1 c2 ->
    (forall r1 r2 p c1 c2, p ∈ (Q r1 r2) ->
                      pre p (c1, c2) ->
                      paco6 bisim_gen r p R (t2 r1) c1 (s2 r2) c2) ->
    paco6 bisim_gen r p R (x <- t1 ;; t2 x) c1 (x <- s1 ;; s2 x) c2.
  Proof.
    revert p Q R t1 t2 s1 s2 c1 c2. pcofix CIH.
    intros p Q R t1 t2 s1 s2 c1 c2 Hpre Htyping1 Htyping2.
    punfold Htyping1. induction Htyping1.
    - do 2 rewritebisim @bind_ret_l. specialize (Htyping2 _ _ _ c1 c2 H0 H).
      eapply paco6_mon; eauto.
    - rewrite throw_bind. pstep. constructor.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 Hpre Htyping2). punfold IHHtyping1.
      pstep. constructor; auto.
    - rewritebisim @bind_tau.
      specialize (IHHtyping1 Hpre Htyping2). punfold IHHtyping1.
      pstep. constructor; auto.
    - do 2 rewritebisim @bind_tau. pclearbot.
      pstep. constructor 5; auto. right. eapply CIH; eauto.
    - rewritebisim @bind_vis. apply bisim_gen_pre in Htyping1. destruct Htyping1; subst.
      + rewrite throw_bind. pstep. constructor.
      + specialize (IHHtyping1 H2 Htyping2). punfold IHHtyping1. pstep. econstructor; eauto.
    - rewritebisim @bind_vis. apply bisim_gen_pre in Htyping1. destruct Htyping1; subst.
      + pstep. econstructor; eauto. rewrite H2. rewrite throw_bind. constructor.
      + specialize (IHHtyping1 H2 Htyping2). punfold IHHtyping1. pstep. econstructor; eauto.
    - do 2 rewritebisim @bind_vis. pclearbot.
      pose proof H2. punfold H2.
      pstep. econstructor 8; eauto.
      destruct (bisim_gen_pre _ _ _ _ _ _ _ H2); eauto.
      rewrite H4. rewrite throw_bind. left. pstep. constructor.
    - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
      destruct (bisim_gen_pre _ _ _ _ _ _ _ (H1 b)).
      + rewrite H3. rewrite throw_bind. constructor.
      + specialize (H2 b H3 Htyping2). punfold H2.
    - rewritebisim @bind_vis. pstep. econstructor; eauto. intros.
      destruct (bisim_gen_pre _ _ _ _ _ _ _ (H1 b)).
      + rewrite H3. rewrite throw_bind. constructor.
      + specialize (H2 b H3 Htyping2). punfold H2.
    - do 2 rewritebisim @bind_vis. pclearbot. pstep. econstructor 11; eauto; intros.
      + specialize (H1 b1). destruct H1. pclearbot.
        punfold H1. destruct (bisim_gen_pre _ _ _ _ _ _ _ H1).
        * exists x. left. pstep. rewrite H3. rewrite throw_bind. econstructor; eauto.
        * eexists. right. eapply CIH; eauto. pstep; eauto.
      + specialize (H2 b2). destruct H2. pclearbot.
        punfold H2. destruct (bisim_gen_pre _ _ _ _ _ _ _ H2).
        * exists x. left. pstep. rewrite H3. rewrite throw_bind. econstructor; eauto.
        * eexists. right. eapply CIH; eauto. pstep; eauto.
  Qed.

  Lemma typing_bind {R1 R2 S1 S2} (P : Perms) (Q : R1 -> S1 -> Perms) (R : R2 -> S2 -> Perms)
        (t1 : itree (sceE config) R1) (t2 : R1 -> itree (sceE config) R2)
        (s1 : itree (sceE specConfig) S1) (s2 : S1 -> itree (sceE specConfig) S2) :
    typing P Q t1 s1 ->
    (forall r1 r2, typing (Q r1 r2) R (t2 r1) (s2 r2)) ->
    typing P R (x <- t1 ;; t2 x) (x <- s1 ;; s2 x).
  Proof.
    repeat intro.
    eapply bisim_bind; eauto.
  Qed.

  Lemma bisim_frame {R1 R2} p r p' Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) c1 c2:
    pre p' (c1, c2) ->
    r ∈ R ->
    p' <= p ** r ->
    bisim p Q t c1 s c2 ->
    bisim p' (fun r1 r2 => Q r1 r2 * R) t c1 s c2.
  Proof.
    revert p r p' Q R t s c1 c2. pcofix CIH. rename r into r0.
    intros p r p' Q R t s c1 c2 Hpre Hr Hlte Hbisim. pstep. punfold Hbisim.
    revert r p' Hr Hlte Hpre.
    induction Hbisim; intros; pclearbot; try solve [econstructor; eauto].
    - constructor; auto. eapply Perms_downwards_closed; eauto.
      do 2 eexists. split; [| split; [| split]]; eauto.
      apply Hlte in Hpre. apply Hpre.
      reflexivity.
    - apply bisim_gen_pre in Hbisim. destruct Hbisim; [subst; constructor |].
      econstructor; eauto.
      + apply Hlte. constructor. left. auto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      + eapply IHHbisim; eauto. reflexivity.
        split; [| split]; auto.
        * apply Hlte in Hpre. destruct Hpre as (? & ? & ?). respects.
          apply H5. auto.
        * apply H1. apply Hlte in Hpre. apply Hpre.
    - econstructor; eauto.
      + apply Hlte. constructor. left. auto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      + apply bisim_gen_pre in Hbisim. destruct Hbisim; [rewrite H2; constructor |].
        eapply IHHbisim; eauto. reflexivity.
        split; [| split]; auto.
        * apply Hlte in Hpre. destruct Hpre as (? & ? & ?). respects.
          apply H5. auto.
        * apply H1. apply Hlte in Hpre. apply Hpre.
    - econstructor 8; eauto.
      3: { pose proof H2 as Hbisim.
           punfold Hbisim. apply bisim_gen_pre in Hbisim.
           destruct Hbisim; [rewrite H3; left; pstep; constructor |].
           right. eapply CIH. 4: apply H2. 2: eauto. 2: reflexivity.
           apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
           split; [| split]; auto.
           respects. apply H6. auto.
      }
      + apply Hlte. constructor. left. auto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
        apply Hlte in Hpre. apply Hpre.
    - econstructor; eauto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      + intros. specialize (H1 b).
        apply bisim_gen_pre in H1. destruct H1; [subst; constructor |].
        eapply H2; eauto. reflexivity.
        apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
        split; [| split]; auto.
    - econstructor; eauto.
      + eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; eauto.
        apply Hlte in Hpre. apply Hpre.
      + intros. specialize (H1 b).
        apply bisim_gen_pre in H1. destruct H1; [rewrite H1; constructor |].
        eapply H2; eauto. reflexivity.
        apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
        split; [| split]; auto.
    - econstructor 11; eauto.
      2: { intros. specialize (H1 b1). destruct H1 as (b2 & H1). pclearbot. exists b2.
           pose proof H1 as Hbisim.
           punfold Hbisim. apply bisim_gen_pre in Hbisim.
           destruct Hbisim; [rewrite H3; left; pstep; constructor |].
           right. eapply CIH. 4: apply H1. 2: eauto. 2: reflexivity.
           apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
           split; [| split]; auto.
      }
      2: { intros. specialize (H2 b2). destruct H2 as (b1 & H2). pclearbot. exists b1.
           pose proof H2 as Hbisim.
           punfold Hbisim. apply bisim_gen_pre in Hbisim.
           destruct Hbisim; [rewrite H3; left; pstep; constructor |].
           right. eapply CIH. 4: apply H2. 2: eauto. 2: reflexivity.
           apply Hlte in Hpre. destruct Hpre as (? & ? & ?).
           split; [| split]; auto.
      }
      eapply sep_step_lte; eauto. apply sep_step_sep_conj_l; auto.
      apply Hlte in Hpre. apply Hpre.
  Qed.

  Lemma typing_frame {R1 R2} P Q R (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2):
    typing P Q t s ->
    typing (P * R) (fun r1 r2 => Q r1 r2 * R) t s.
  Proof.
    intros Ht p' c1 c2 (p & r & Hp & Hr & Hsep & Hlte) Hpre.
    pose proof Hpre as H. apply Hlte in H. destruct H as (Hprep & Hprer & Hsep').
    eapply bisim_frame; eauto.
  Qed.

  (** * [no_errors] *)
  Variant no_errors_gen {R C : Type} no_errors (c : C) : itree (sceE C) R -> Prop :=
  | no_errors_ret : forall r, no_errors_gen no_errors c (Ret r)
  | no_errors_tau : forall t, no_errors c t -> no_errors_gen no_errors c (Tau t)
  | no_errors_modify : forall f k,
      no_errors (f c) (k c) ->
      no_errors_gen no_errors c (vis (Modify f) k)
  | no_errors_choice : forall k,
      (forall b, no_errors c (k b)) ->
      no_errors_gen no_errors c (vis Or k)
  .
  Lemma no_errors_gen_mon {R C} : monotone2 (@no_errors_gen R C).
  Proof.
    repeat intro. inversion IN; subst; try solve [constructor; auto].
  Qed.
  #[local] Hint Resolve no_errors_gen_mon : paco.

  Definition no_errors {R C : Type} :=
    paco2 (@no_errors_gen R C) bot2.

  Lemma bisim_no_errors {R1 R2} Q (t : itree (sceE config) R1) (s : itree (sceE specConfig) R2) p c1 c2 :
    bisim p Q t c1 s c2 ->
    no_errors c2 s ->
    no_errors c1 t.
  Proof.
    revert Q t s p c1 c2. pcofix CIH. intros Q t s p c1 c2 Htyping Hs. pstep.
    punfold Htyping.
    induction Htyping;
      try solve [constructor; eauto];
      pinversion Hs;
      try (match goal with
           | [H : existT _ _ _ = existT _ _ _ |- _] => apply inj_pair2 in H
           end); subst; eauto;
        try solve [constructor; eauto].
    - subst. apply (H2 true). apply H4.
    - constructor. intros. right. destruct (H1 b). eapply CIH.
      + destruct H3; eauto. inversion b0.
      + inversion Hs. apply inj_pair2 in H5; subst.
        specialize (H6 x). pclearbot. eauto.
  Qed.

  Global Instance Proper_eq_Perms_typing {R1 R2} :
    Proper (eq_Perms ==>
           (pointwise_relation _ (pointwise_relation _ eq_Perms)) ==> eq ==> eq ==> flip impl) (@typing R1 R2).
  Proof.
    repeat intro. subst.
    eapply bisim_lte; eauto. apply H3; auto. rewrite <- H; auto.
    intros. rewrite H0. reflexivity.
  Qed.
End bisim.

#[global] Hint Resolve bisim_gen_mon : paco.

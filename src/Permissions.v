(* begin hide *)
From Coq Require Import
     Classes.Morphisms
     Classes.RelationClasses
     Lists.List
     Relations.Relation_Operators
     Relations.Operators_Properties.

From Heapster Require Import Utils.
(* end hide *)

Section Permissions.
  (** This entire file is parameterized over some state type. *)
  Context {config : Type}.

  (** * Rely-guarantee permissions *)
  Record perm : Type :=
    {
    (** The rely: the updates this permission allows of others. *)
    rely : config -> config -> Prop;
    rely_PO : PreOrder rely;
    (** The guarantee: the updates that this permission allows. *)
    guar : config -> config -> Prop;
    guar_PO : PreOrder guar;
    (** The precondition on configs. *)
    pre : config -> Prop;
    pre_respects : forall x y, rely x y -> pre x -> pre y;
    }.

  (* begin hide *)
  Hint Unfold rely : core.
  Hint Unfold pre : core.
  Hint Unfold guar : core.
  Hint Resolve pre_respects : core.

  Global Instance rely_is_preorder p : PreOrder (rely p) := rely_PO p.
  Global Instance guar_is_preorder p : PreOrder (guar p) := guar_PO p.
  (* end hide *)

  (** ** Permission ordering *)
  Record lte_perm (p q: perm) : Prop :=
    {
    pre_inc : forall x, pre p x -> pre q x;
    rely_inc : forall x y, rely p x y -> rely q x y;
    guar_inc : forall x y, guar q x y -> guar p x y;
    }.

  (* begin hide *)
  Hint Resolve pre_inc : core.
  Hint Resolve rely_inc : core.
  Hint Resolve guar_inc : core.
  (* end hide *)

  Notation "p <= q" := (lte_perm p q).

  Global Instance lte_perm_is_PreOrder : PreOrder lte_perm.
  Proof.
    constructor; [ constructor; auto | constructor; intros ]; eauto.
  Qed.

  (** Equality of permissions = the symmetric closure of the ordering. *)
  Definition eq_perm p q : Prop := p <= q /\ q <= p.
  Notation "p ≡≡ q" := (eq_perm p q) (at level 50).

  Lemma eq_perm_lte_1 : forall p q, p ≡≡ q -> p <= q.
  Proof. intros p q []. auto. Qed.
  Lemma eq_perm_lte_2 : forall p q, p ≡≡ q -> q <= p.
  Proof. intros p q []. auto. Qed.

  (* begin hide *)
  Hint Unfold eq_perm : core.
  Hint Resolve eq_perm_lte_1 : core.
  Hint Resolve eq_perm_lte_2 : core.
  (* end hide *)

  Global Instance Proper_eq_perm_rely :
    Proper (eq_perm ==> eq ==> eq ==> Basics.flip Basics.impl) rely.
  Proof.
    repeat intro. subst. apply H. auto.
  Qed.

  Global Instance Proper_eq_perm_guar :
    Proper (eq_perm ==> eq ==> eq ==> Basics.flip Basics.impl) guar.
  Proof.
    repeat intro. subst. apply H. auto.
  Qed.

  Global Instance Proper_eq_perm_pre :
    Proper (eq_perm ==> eq ==> Basics.flip Basics.impl) pre.
  Proof.
    repeat intro. subst. apply H. auto.
  Qed.

  Global Instance eq_perm_is_Equivalence : Equivalence eq_perm.
  Proof.
    constructor.
    - split; reflexivity.
    - intros x y []. split; auto.
    - intros x y z [] []. split; etransitivity; eauto.
  Qed.

  Global Instance Proper_eq_perm_lte_perm :
    Proper (eq_perm ==> eq_perm ==> Basics.flip Basics.impl) lte_perm.
  Proof.
    repeat intro. subst. etransitivity; eauto. etransitivity; eauto.
  Qed.

  (** Other lattice definitions. *)
  Program Definition bottom_perm : perm :=
    {|
    pre := fun x => False;
    rely := fun x y => x = y;
    guar  := fun x y => True;
    |}.
  Next Obligation.
    constructor; repeat intro; subst; auto.
  Qed.

  Lemma bottom_perm_is_bottom : forall p, bottom_perm <= p.
  Proof.
    constructor; cbn; intros; subst; intuition.
  Qed.

  Program Definition top_perm : perm :=
    {|
    pre := fun x => True;
    rely := fun x y => True;
    guar  := fun x y => x = y;
    |}.
  Next Obligation.
    constructor; repeat intro; subst; auto.
  Qed.

  Lemma top_perm_is_top : forall p, p <= top_perm.
  Proof.
    constructor; cbn; repeat intro; subst; intuition.
  Qed.

  Ltac respects := eapply pre_respects; eauto.

  Program Definition meet_perm' (ps: perm -> Prop) (H: exists p, ps p) : perm :=
    {|
      pre := fun x => forall p, ps p -> pre p x;
      rely := fun x y => forall p, ps p -> rely p x y;
      guar  := clos_trans _ (fun x y => exists p, ps p /\ guar p x y);
    |}.
  Next Obligation.
    constructor; repeat intro.
    - reflexivity.
    - etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor.
    - constructor. eexists. split. apply H0. reflexivity.
    - repeat intro. econstructor 2; eauto.
  Qed.
  Next Obligation.
    respects.
  Qed.

  Lemma lte_meet_perm' (ps : perm -> Prop) p (H : ps p) :
    meet_perm' ps (ex_intro _ p H) <= p.
  Proof.
    constructor; cbn; intros; auto.
    constructor 1. eexists. split; eauto.
  Qed.

  Lemma meet_perm'_max (ps : perm -> Prop) (H : exists p, ps p) r :
    (forall p, ps p -> r <= p) ->
    r <= meet_perm' ps H.
  Proof.
    intros Hlte. constructor; cbn; intros; auto.
    - apply Hlte; auto.
    - apply Hlte; auto.
    - induction H0; auto.
      + destruct H0 as (p' & ? & ?). eapply Hlte; eauto.
      + transitivity y; auto.
  Qed.

  Program Definition meet_perm (p q: perm) : perm :=
    {|
    pre := fun x => pre p x /\ pre q x;
    rely := fun x y => rely p x y /\ rely q x y;
    guar  := clos_trans _ (fun x y => (guar p x y) \/ (guar q x y))
    |}.
  Next Obligation.
    constructor; repeat intro.
    - split; reflexivity.
    - destruct H. destruct H0. split; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor.
    - constructor; left; reflexivity.
    - repeat intro. destruct H, H0.
      + destruct H, H0; econstructor 2; constructor; eauto.
      + econstructor 2. left. apply H. econstructor 2; eauto.
      + econstructor 2; eauto. econstructor 2; eauto. left. assumption.
      + repeat (econstructor 2; eauto).
  Qed.
  Next Obligation.
    split; respects.
  Qed.

  Lemma lte_l_meet_perm : forall p q,
      meet_perm p q <= p.
  Proof.
    intros. constructor; cbn; auto.
    - intros ? [? _]. auto.
    - intros x y []; auto.
    - constructor; auto.
  Qed.

  Lemma lte_r_meet_perm : forall p q,
      meet_perm p q <= q.
  Proof.
    intros. constructor; cbn; auto.
    - intros ? [_ ?]. auto.
    - intros x y []; auto.
    - constructor; auto.
  Qed.

  Lemma meet_perm_max : forall p q r,
      r <= p ->
      r <= q ->
      r <= meet_perm p q.
  Proof.
    intros p q r [] []. constructor; intros; cbn; auto.
    - induction H; auto.
      + destruct H; auto.
      + transitivity y; auto.
  Qed.

  Lemma meet_perm_commut' : forall p q,
      meet_perm p q <= meet_perm q p.
  Proof.
    constructor.
    - intros ? []. split; auto.
    - intros x y []. repeat split; auto.
    - intros. induction H.
      + destruct H; constructor; auto.
      + etransitivity; eauto.
  Qed.

  Lemma meet_perm_commut : forall p q,
      meet_perm p q ≡≡ meet_perm q p.
  Proof.
    split; apply meet_perm_commut'.
  Qed.

  Lemma meet_perm_assoc : forall p q r,
      meet_perm p (meet_perm q r) ≡≡ meet_perm (meet_perm p q) r.
  Proof.
    split; intros.
    {
      constructor.
      - intros x [? [? ?]]. split; [split |]; auto.
      - intros x y [? []].
        repeat split; auto.
      - intros. induction H; try solve [etransitivity; eauto].
        destruct H.
        + induction H; try solve [etransitivity; eauto].
          destruct H.
          * constructor. left. auto.
          * constructor. right. constructor. left. auto.
        + constructor. right. constructor. right. auto.
    }
    {
      constructor.
      - intros x [[? ?] ?]. split; [| split]; auto.
      - intros x y [[] ?].
        repeat split; auto.
      - intros. induction H; try solve [etransitivity; eauto].
        destruct H.
        + constructor. left. constructor. left. auto.
        + induction H; try solve [etransitivity; eauto].
          destruct H.
          * constructor. left. constructor. right. auto.
          * constructor. right. auto.
    }
  Qed.

  Lemma meet_perm_idem : forall p, meet_perm p p ≡≡ p.
  Proof.
    split; intros.
    - constructor.
      + intros ? [? _]; auto.
      + intros x y []. auto.
      + constructor. auto.
    - constructor; intros.
      + split; auto.
      + repeat split; auto.
      + induction H; try solve [etransitivity; eauto].
        destruct H; auto.
  Qed.

  Definition join_rely p q := clos_trans _ (fun x y => (rely p x y) \/ (rely q x y)).

  Program Definition join_perm (p q:perm) : perm :=
    {|
    pre := fun x => pre p x \/ pre q x \/ exists y, (pre p y \/ pre q y) /\ join_rely p q y x;
    rely := join_rely p q;
    guar  := fun x y => guar p x y /\ guar q x y;
    |}.
  Next Obligation.
    constructor; repeat intro.
    - constructor. left. reflexivity.
    - econstructor 2; eauto.
  Qed.
  Next Obligation.
    constructor.
    - constructor; reflexivity.
    - intros x y z [] []. split; etransitivity; eauto.
  Qed.
  Next Obligation.
    induction H; auto.
    destruct H0 as [? | [? | [z [? ?]]]].
    - destruct H; try solve [left; respects].
      right; right. exists x. split; auto. constructor 1. auto.
    - destruct H; try solve [right; left; respects].
      right; right. exists x. split; auto. constructor 1. auto.
    - destruct H; right; right; exists z; split; auto;
        econstructor 2; eauto; constructor 1; auto.
  Qed.

  Lemma lte_join_perm_l : forall p q,
      p <= join_perm p q.
  Proof.
    intros. constructor; cbn; auto.
    - left; auto.
    - intros x y []; auto.
  Qed.
  Lemma lte_join_perm_r : forall p q,
      q <= join_perm p q.
  Proof.
    intros. constructor; cbn; auto.
    - left; auto.
    - intros x y []; auto.
  Qed.
  Lemma join_perm_min : forall p q r,
      p <= r ->
      q <= r ->
      join_perm p q <= r.
  Proof.
    intros p q r [] []. constructor; intros; cbn; auto.
    - cbn in H. destruct H as [? | [? | [? [? ?]]]]; auto.
      induction H0.
      + destruct H, H0; respects.
      + apply IHclos_trans1 in H.
        clear IHclos_trans1 IHclos_trans2 H0_.
        induction H0_0; auto.
        destruct H0; respects.
    - induction H.
      + destruct H; auto.
      + etransitivity; eauto.
  Qed.

  (** ** Separate permissions *)
  Record separate (p q : perm) : Prop :=
    {
    sep_l: forall x y, guar q x y -> rely p x y;
    sep_r: forall x y, guar p x y -> rely q x y;
    }.

  Notation "p ⊥ q" := (separate p q) (at level 50).

  Global Instance separate_symmetric: Symmetric separate.
  Proof.
    intros p q []. constructor; auto.
  Qed.

  Lemma separate_top : forall p, p ⊥ top_perm.
  Proof.
    constructor; intros; cbn; auto.
    inversion H. reflexivity.
  Qed.

  (** We can always weaken permissions and retain separateness. *)
  Lemma separate_upwards_closed : forall p q r, p ⊥ q -> q <= r -> p ⊥ r.
  Proof.
    intros. constructor.
    - intros. apply H; auto. apply H0; auto.
    - intros. apply H0. apply H; auto.
  Qed.

  Global Instance Proper_eq_perm_separate :
    Proper (eq_perm ==> eq_perm ==> Basics.flip Basics.impl) separate.
  Proof.
    repeat intro.
    eapply separate_upwards_closed; eauto. symmetry.
    eapply separate_upwards_closed; eauto. symmetry. auto.
  Qed.

  (** ** Separating conjunction for permissions *)
  Program Definition sep_conj_perm (p q: perm) : perm :=
    {|
    pre := fun x => pre p x /\ pre q x /\ p ⊥ q;
    rely := fun x y => rely p x y /\ rely q x y;
    guar := clos_trans _ (fun x y => (guar p x y) \/ (guar q x y))
    |}.
  Next Obligation.
    constructor; repeat intro.
    - split; reflexivity.
    - destruct H, H0.
      split; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor.
    - constructor; intuition.
    - repeat intro. destruct H, H0.
      + destruct H, H0; econstructor 2; constructor; eauto.
      + econstructor 2. left. apply H. econstructor 2; eauto.
      + econstructor 2; eauto. econstructor 2; eauto. left. assumption.
      + repeat (econstructor 2; eauto).
  Qed.
  Next Obligation.
    split; [respects | split; [respects | auto]].
  Qed.
  Notation "p ** q" := (sep_conj_perm p q) (at level 40).

  Lemma sep_conj_join : forall p q, p ⊥ q -> p ** q ≡≡ meet_perm p q.
  Proof.
    split; intros.
    - constructor; auto; intros x [? [? ?]]; split; auto.
    - constructor; auto; intros x []; split; auto.
  Qed.

  Lemma lte_l_sep_conj_perm : forall p q, p ** q <= p.
  Proof.
    intros. constructor; cbn; auto.
    - intros x []; auto.
    - intros x y []; auto.
    - constructor; auto.
  Qed.

  Lemma lte_r_sep_conj_perm : forall p q, p ** q <= q.
  Proof.
    intros. constructor; cbn; auto.
    - intros x [? [? ?]]; auto.
    - intros x y []; auto.
    - constructor; auto.
  Qed.

  Lemma sep_conj_perm_monotone : forall p p' q q',
      p' <= p -> q' <= q -> p' ** q' <= p ** q.
  Proof.
    constructor; intros; cbn.
    - destruct H1 as (? & ? & ?); split; [| split]; eauto.
      eapply separate_upwards_closed; eauto.
      symmetry. symmetry in H3. eapply separate_upwards_closed; eauto.
    - split.
      + apply H. apply H1.
      + apply H0. apply H1.
    - induction H1.
      + constructor. destruct H1; eauto.
      + econstructor 2; eauto.
  Qed.

  Global Instance Proper_eq_perm_sep_conj_perm :
    Proper (eq_perm ==> eq_perm ==> eq_perm) sep_conj_perm.
  Proof.
    repeat intro. split; apply sep_conj_perm_monotone; auto.
  Qed.

  Lemma sep_conj_perm_top' : forall p, p <= p ** top_perm.
  Proof.
    constructor; intros.
    - split; [| split]; cbn; intuition. apply separate_top.
    - repeat split; auto.
    - induction H.
      + destruct H; auto. inversion H. reflexivity.
      + etransitivity; eauto.
  Qed.

  Lemma sep_conj_perm_top : forall p, p ** top_perm ≡≡ p.
  Proof.
    split; [apply lte_l_sep_conj_perm | apply sep_conj_perm_top'].
  Qed.

  Lemma sep_conj_perm_bottom' : forall p, bottom_perm <= p ** bottom_perm.
  Proof.
    constructor; intros; cbn in *; intuition.
    subst. reflexivity.
  Qed.

  Lemma sep_conj_perm_bottom : forall p, bottom_perm ≡≡ p ** bottom_perm.
  Proof.
    split; [apply sep_conj_perm_bottom' | apply lte_r_sep_conj_perm].
  Qed.

  Lemma sep_conj_perm_commut' : forall p q, p ** q <= q ** p.
  Proof.
    constructor.
    - intros x [? [? ?]]; cbn; split; [| split]; intuition.
    - intros x y []; repeat split; auto.
    - intros. induction H.
      + destruct H; constructor; auto.
      + etransitivity; eauto.
  Qed.

  Lemma sep_conj_perm_commut : forall p q, p ** q ≡≡ q ** p.
  Proof.
    split; apply sep_conj_perm_commut'.
  Qed.

  Lemma separate_sep_conj_perm_l: forall p q r, p ⊥ q ** r -> p ⊥ q.
  Proof.
    intros. destruct H. constructor; intros.
    - apply sep_l0. constructor. left. auto.
    - apply sep_r0. auto.
  Qed.
  Lemma separate_sep_conj_perm_r: forall p q r, p ⊥ q ** r -> p ⊥ r.
  Proof.
    intros. destruct H. constructor; intros.
    - apply sep_l0. constructor. right. auto.
    - apply sep_r0. auto.
  Qed.
  Lemma separate_sep_conj_perm: forall p q r, p ⊥ q ->
                                         p ⊥ r ->
                                         r ⊥ q ->
                                         p ⊥ q ** r.
  Proof.
    intros. constructor; intros.
    - induction H2.
      + destruct H2; [apply H | apply H0]; auto.
      + etransitivity; eauto.
    - split; [apply H | apply H0]; auto.
  Qed.

  Lemma separate_sep_conj_perm_4: forall p q r s,
      p ⊥ q ->
      p ⊥ r ->
      p ⊥ s ->
      q ⊥ r ->
      q ⊥ s ->
      r ⊥ s ->
      p ** q ⊥ r ** s.
  Proof.
    intros. apply separate_sep_conj_perm; symmetry; auto; apply separate_sep_conj_perm; symmetry; auto.
  Qed.

  Lemma sep_conj_perm_assoc : forall p q r,
      (p ** q) ** r ≡≡ p ** (q ** r).
  Proof.
    split; intros.
    {
      constructor.
      - intros x [[? [? ?]] [? ?]]. symmetry in H3.
        pose proof (separate_sep_conj_perm_l _ _ _ H3). symmetry in H4.
        pose proof (separate_sep_conj_perm_r _ _ _ H3). symmetry in H5.
        split; [| split; [split; [| split] |]]; auto.
        apply separate_sep_conj_perm; auto. symmetry; auto.
      - intros x y [[? ?] ?]; cbn; auto.
      - intros. induction H; try solve [etransitivity; eauto].
        destruct H.
        + constructor. left. constructor. left. auto.
        + induction H; try solve [etransitivity; eauto].
          destruct H.
          * constructor. left. constructor. right. auto.
          * constructor. right. auto.
    }
    {
      constructor.
      - intros x [? [[? [? ?]] ?]].
        pose proof (separate_sep_conj_perm_l _ _ _ H3).
        pose proof (separate_sep_conj_perm_r _ _ _ H3).
        split; [split; [| split] | split]; auto.
        symmetry. apply separate_sep_conj_perm; symmetry; auto.
      - intros x y [? [? ?]]. split; [split |]; auto.
      - intros. induction H; try solve [etransitivity; eauto].
        destruct H.
        + induction H; try solve [etransitivity; eauto].
          destruct H.
          * constructor. left. auto.
          * constructor. right. constructor. left. auto.
        + constructor. right. constructor. right. auto.
    }
  Qed.

  (** * Permission sets *)
  (** Perms = upwards-closed sets of permissions *)
  Record Perms :=
    {
    in_Perms : perm -> Prop;
    Perms_downwards_closed : forall p1 p2, in_Perms p1 -> p2 <= p1 -> in_Perms p2
    }.
  Notation "p ∈ P" := (in_Perms P p) (at level 60).

  (** ** Permission set ordering *)
  (** Defined as set inclusion. *)
  Definition lte_Perms (P Q : Perms) : Prop :=
    forall p, p ∈ P -> p ∈ Q.
  Notation "P ⊑ Q" := (lte_Perms P Q) (at level 60).

  Global Instance lte_Perms_is_preorder : PreOrder lte_Perms.
  Proof.
    constructor; repeat intro; auto.
  Qed.

  (** Various lattice definitions. *)
  Program Definition top_Perms : Perms :=
    {|
    in_Perms := fun r => True
    |}.

  Lemma top_Perms_is_top : forall P, P ⊑ top_Perms.
  Proof.
    repeat intro. cbn. auto.
  Qed.

  Program Definition bottom_Perms : Perms :=
    {|
    in_Perms := fun r => False
    |}.

  Lemma bottom_Perms_is_bottom : forall P, bottom_Perms ⊑ P.
  Proof.
    repeat intro. inversion H.
  Qed.

  (** The least Perms set containing a given p *)
  Program Definition singleton_Perms p1 : Perms :=
    {|
    in_Perms := fun p2 => p2 <= p1
    |}.
  Next Obligation.
    etransitivity; eassumption.
  Qed.

  (** Meet of Perms sets = intersection *)
  Program Definition meet_Perms (Ps : Perms -> Prop) : Perms :=
    {|
    in_Perms := fun p => forall P, Ps P -> p ∈ P
    |}.
  Next Obligation.
    eapply Perms_downwards_closed; eauto.
  Qed.
  Lemma lte_meet_Perms : forall (Ps : Perms -> Prop) P,
      Ps P ->
      meet_Perms Ps ⊑ P.
  Proof.
    repeat intro. apply H0. auto.
  Qed.
  Lemma meet_Perms_max : forall (Ps : Perms -> Prop) Q,
      (forall P, Ps P -> Q ⊑ P) ->
      Q ⊑ meet_Perms Ps.
  Proof.
    repeat intro.
    eapply H; eauto.
  Qed.

  (** Join of Perms sets = union *)
  Program Definition join_Perms (Ps : Perms -> Prop) : Perms :=
    {|
    in_Perms := fun p => exists P, Ps P /\ p ∈ P
    |}.
  Next Obligation.
    exists H. split; auto.
    apply (Perms_downwards_closed _ p1); assumption.
  Qed.

  Lemma lte_join_Perms : forall (Ps : Perms -> Prop) P,
      Ps P ->
      P ⊑ join_Perms Ps.
  Proof.
    repeat intro. exists P. auto.
  Qed.

  Lemma join_Perms_min : forall (Ps : Perms -> Prop) Q,
      (forall P, Ps P -> P ⊑ Q) ->
      join_Perms Ps ⊑ Q.
  Proof.
    repeat intro. destruct H0 as [? [? ?]].
    eapply H; eauto.
  Qed.

  Definition join_Perms2 P Q : Perms := join_Perms (fun R => R = P \/ R = Q).

  (** Set equality *)
  Definition eq_Perms (P Q : Perms) : Prop := P ⊑ Q /\ Q ⊑ P.
  Notation "P ≡ Q" := (eq_Perms P Q) (at level 60).

  Global Instance Equivalence_eq_Perms : Equivalence eq_Perms.
  Proof.
    constructor; repeat intro.
    - split; reflexivity.
    - destruct H; split; auto.
    - destruct H, H0. split; etransitivity; eauto.
  Qed.

  Global Instance Proper_eq_Perms_lte_Perms :
    Proper (eq_Perms ==> eq_Perms ==> Basics.flip Basics.impl) lte_Perms.
  Proof.
    do 5 red. intros. etransitivity. apply H. etransitivity. apply H1. apply H0.
  Qed.

  Global Instance Proper_eq_Perms_eq_perm_in_Perms : Proper (eq_Perms ==> eq_perm ==> Basics.flip Basics.impl) in_Perms.
  Proof.
    repeat intro; subst. apply H. eapply Perms_downwards_closed; eauto.
  Qed.

  (** ** Separating conjunction for permission sets *)
  Program Definition sep_conj_Perms (P Q : Perms) : Perms :=
    {|
      in_Perms := fun r => exists p q, p ∈ P /\ q ∈ Q /\ p ⊥ q /\ r <= p ** q
    |}.
  Next Obligation.
    exists H, H1. split; [| split; [| split]]; auto. etransitivity; eauto.
  Qed.
  Notation "P * Q" := (sep_conj_Perms P Q).

  Lemma lte_l_sep_conj_Perms : forall P Q, P * Q ⊑ P.
  Proof.
    intros P Q p' ?. destruct H as (p & q & Hp & Hq & ? & ?).
    eapply Perms_downwards_closed; eauto.
    etransitivity; eauto. apply lte_l_sep_conj_perm.
  Qed.

  Lemma lte_r_sep_conj_Perms : forall P Q, P * Q ⊑ Q.
  Proof.
    intros P Q p' ?. destruct H as (p & q & Hp & Hq & ? & ?).
    eapply Perms_downwards_closed; eauto.
    etransitivity; eauto. apply lte_r_sep_conj_perm.
  Qed.

  Lemma sep_conj_Perms_top_identity : forall P, top_Perms * P ≡ P.
  Proof.
    constructor; repeat intro.
    - destruct H as (? & ? & ? & ? & ? & ?).
      eapply (Perms_downwards_closed P); eauto.
      etransitivity; eauto. apply lte_r_sep_conj_perm.
    - exists top_perm, p. split; cbn; [| split; [| split]]; auto.
      + symmetry. apply separate_top.
      + rewrite sep_conj_perm_commut. apply sep_conj_perm_top.
  Qed.

  Lemma sep_conj_Perms_bottom_absorb : forall P, bottom_Perms * P ≡ bottom_Perms.
  Proof.
    constructor; repeat intro.
    - destruct H as [? [_ [[] _]]].
    - inversion H.
  Qed.

  Lemma sep_conj_Perms_monotone : forall P P' Q Q', P' ⊑ P -> Q' ⊑ Q -> P' * Q' ⊑ P * Q.
  Proof.
    repeat intro. destruct H1 as (? & ? & ? & ? & ?).
    exists x, x0. auto.
  Qed.

  Lemma sep_conj_Perms_perm: forall P Q p q,
      p ∈ P ->
      q ∈ Q ->
      p ⊥ q ->
      p ** q ∈ P * Q.
  Proof.
    intros. exists p, q. split; [| split; [| split]]; auto. reflexivity.
  Qed.

  Lemma sep_conj_Perms_commut : forall P Q, P * Q ≡ Q * P.
  Proof.
    split; repeat intro.
    - destruct H as (q & p' & Hq & Hp & ? & ?).
      exists p', q. split; [| split; [| split]]; auto.
      symmetry. auto.
      rewrite sep_conj_perm_commut. auto.
    - destruct H as (p' & q & Hp & Hq & ? & ?).
      exists q, p'. split; [| split; [| split]]; auto.
      symmetry. auto.
      rewrite sep_conj_perm_commut. auto.
  Qed.

  Lemma sep_conj_Perms_assoc : forall P Q R, P * (Q * R) ≡ (P * Q) * R.
  Proof.
    split; repeat intro.
    - rename p into p'. destruct H as (p & qr & ? & ? & ? & ?).
      destruct H0 as (q & r & ? & ? & ? & ?).
      exists (p ** q), r. split; [| split; [| split]]; auto.
      + apply sep_conj_Perms_perm; auto.
        eapply separate_upwards_closed; eauto.
        etransitivity; eauto. apply lte_l_sep_conj_perm.
      + symmetry. apply separate_sep_conj_perm; symmetry; auto.
        * eapply separate_upwards_closed; eauto.
          etransitivity; eauto. apply lte_r_sep_conj_perm.
        * eapply separate_upwards_closed; eauto.
          etransitivity; eauto. apply lte_l_sep_conj_perm.
      + rewrite sep_conj_perm_assoc.
        etransitivity; eauto.
        apply sep_conj_perm_monotone; intuition.
    - rename p into p'. destruct H as (pq & r & ? & ? & ? & ?).
      destruct H as (p & q & ? & ? & ? & ?).
      exists p, (q ** r). split; [| split; [| split]]; auto.
      + apply sep_conj_Perms_perm; auto.
        symmetry in H1. symmetry. eapply separate_upwards_closed; eauto.
        etransitivity; eauto. apply lte_r_sep_conj_perm.
      + apply separate_sep_conj_perm; auto.
        * symmetry in H1. symmetry. eapply separate_upwards_closed; eauto.
          etransitivity; eauto. apply lte_l_sep_conj_perm.
        * symmetry in H1. eapply separate_upwards_closed; eauto.
          etransitivity; eauto. apply lte_r_sep_conj_perm.
      + rewrite <- sep_conj_perm_assoc.
        etransitivity; eauto.
        apply sep_conj_perm_monotone; intuition.
  Qed.

  Lemma sep_conj_Perms_join_commute : forall (Ps : Perms -> Prop) P,
      (join_Perms Ps) * P ≡ join_Perms (fun Q => exists P', Q = P' * P /\ Ps P').
  Proof.
    split; repeat intro.
    - destruct H as (? & ? & (Q & ? & ?) & ? & ? & ?).
      cbn. eexists. split.
      + exists Q. split; auto.
      + eapply Perms_downwards_closed; eauto.
        exists x, x0. split; [| split; [| split]]; auto. reflexivity.
    - destruct H as (? & (Q & ? & ?) & ?). subst.
      subst. destruct H1 as (? & ? & ? & ? & ? & ?).
      cbn. exists x, x0. split; [| split]; auto.
      eexists; split; eauto.
  Qed.

  Global Instance Proper_eq_Perms_sep_conj_Perms :
    Proper (eq_Perms ==> eq_Perms ==> eq_Perms) sep_conj_Perms.
  Proof.
    repeat intro. etransitivity.
    - split; eapply sep_conj_Perms_monotone; try eapply H0; try eapply H.
    - split; eapply sep_conj_Perms_monotone; try eapply H0; try eapply H; reflexivity.
  Qed.

  (** Separating implication, though we won't be using it. *)
  Definition impl_Perms P Q := join_Perms (fun R => R * P ⊑ Q).

  (** A standard property about separating conjunction and implication. *)
  Lemma adjunction : forall P Q R, P * Q ⊑ R <-> P ⊑ (impl_Perms Q R).
  Proof.
    intros. split; intros.
    - red. red. intros. cbn. exists P. auto.
    - apply (sep_conj_Perms_monotone _ _ Q Q) in H; intuition.
      etransitivity; [apply H |].
      unfold impl_Perms.
      rewrite sep_conj_Perms_join_commute.
      apply join_Perms_min. intros P' [? [? ?]]. subst. auto.
  Qed.

End Permissions.

(* begin hide *)
(* Redefining notations outside the section. *)
Notation "p <= q" := (lte_perm p q).
Notation "p ≡≡ q" := (eq_perm p q) (at level 50).
Notation "p ⊥ q" := (separate p q) (at level 50).
Notation "p ** q" := (sep_conj_perm p q) (at level 40).
Notation "p ∈ P" := (in_Perms P p) (at level 60).
Notation "P ⊑ Q" := (lte_Perms P Q) (at level 60).
Notation "P ≡ Q" := (eq_Perms P Q) (at level 60).
Notation "P * Q" := (sep_conj_Perms P Q).
Notation "P -⊑- Q" := (forall a, P a ⊑ Q a) (at level 60).
Notation "P -≡- Q" := (P -⊑- Q /\ Q -⊑- P) (at level 60).

Ltac respects := eapply pre_respects; eauto.

#[ export ] Hint Unfold rely : core.
#[ export ] Hint Unfold pre : core.
#[ export ] Hint Unfold guar : core.
#[ export ] Hint Resolve pre_respects : core.
#[ export ] Hint Resolve pre_inc : core.
#[ export ] Hint Resolve rely_inc : core.
#[ export ] Hint Resolve guar_inc : core.
#[ export ] Hint Unfold eq_perm : core.
#[ export ] Hint Resolve eq_perm_lte_1 : core.
#[ export ] Hint Resolve eq_perm_lte_2 : core.

(* end hide *)

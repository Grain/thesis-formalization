(* begin hide *)

From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Lia.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.

From Heapster Require Import
     Utils
     Permissions
     Memory
     SepStep
     Typing
     PermType
     PermTypeProofs.

From ITree Require Import
     ITree
     Eq.Eqit
     Eq.EqAxiom
     Basics.

From Paco Require Import
     paco.

Import MonadNotation.
Import ListNotations.
Import ITreeNotations.

Local Open Scope itree_scope.
(* end hide *)

Section MemoryPerms.
  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si memory}.

  (** memory helpers **)

  (* Lemma allocated_read c1 c2 ptr : *)
  (*   read c1 ptr = read c2 ptr -> *)
  (*   allocated c1 ptr -> *)
  (*   allocated c2 ptr. *)
  (* Proof. *)
  (*   destruct ptr as [b o]. *)
  (*   unfold read, allocated. simpl. intros. *)
  (*   destruct (m c1 b), (m c2 b); try solve [inversion H; inversion H0]; auto. *)
  (*   - destruct l0, l1. *)
  (*     destruct (bytes o), (bytes0 o); try solve [contradiction]. *)
  (*     + rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H0. *)
  (*       rewrite H0 in H. *)
  (*       destruct (o <? size0) eqn:?; auto. *)
  (*       rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0. auto. *)
  (*       inversion H. *)
  (*     + rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H0. *)
  (*       rewrite H0 in H. *)
  (*       destruct (o <? size0); inversion H. *)
  (*   - destruct l0. destruct (bytes o); try solve [contradiction]. *)
  (*     rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H0. *)
  (*     rewrite H0 in H. inversion H. *)
  (* Qed. *)

  (* Lemma allocated_read' c1 c2 ptr : *)
  (*   read c1 ptr = read c2 ptr -> *)
  (*   allocated c1 ptr = allocated c2 ptr. *)
  (* Proof. *)
  (* Admitted. *)

  (* Definition alloc_invariant (c1 c2 : config) (ptr : addr) : Prop := *)
  (*   allocated c1 ptr = allocated c2 ptr. *)

  (* Lemma alloc_invariant_read c1 c2 ptr : *)
  (*   alloc_invariant c1 c2 ptr -> *)
  (*   read c2 ptr = None -> *)
  (*   read c1 ptr = None. *)
  (* Proof. *)
  (*   destruct ptr as [b o]. *)
  (*   unfold alloc_invariant. unfold allocated. unfold read. simpl in *. intros. *)
  (*   destruct (m c1 b), (m c2 b); try solve [inversion H0]; auto. *)
  (*   - destruct l0, l1. *)
  (*     destruct (bytes o), (bytes0 o). *)
  (*     + destruct (o <? size) eqn:?; auto. *)
  (*       rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0. *)
  (*       rewrite H in Heqb0. *)
  (*       rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0. *)
  (*       rewrite Heqb0 in H0. inversion H0. *)
  (*     + destruct (o <? size) eqn:?; auto. *)
  (*       rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0. *)
  (*       rewrite H in Heqb0. inversion Heqb0. *)
  (*     + destruct (o <? size); auto. *)
  (*     + destruct (o <? size); auto. *)
  (*   - destruct l0. destruct (bytes o). *)
  (*     + destruct (o <? size) eqn:?; auto. *)
  (*       rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in Heqb0. *)
  (*       rewrite H in Heqb0. inversion Heqb0. *)
  (*     + destruct (o <? size); auto. *)
    (* Qed. *)
  (* Abort. *)

  (* Lemma write_success_allocation c c' ptr val : *)
  (*   write c ptr val = Some c' -> *)
  (*   alloc_invariant c c' ptr. *)
  (* Proof. *)
  (*   destruct ptr as [b o]. *)
  (*   intros. unfold alloc_invariant. unfold allocated. unfold write in H. simpl in *. *)
  (*   destruct (m c b) eqn:?; try solve [inversion H]. destruct l0. *)
  (*   destruct (o <? size) eqn:?; try solve [inversion H]. *)
  (*   destruct (is_some (bytes o)) eqn:?; try solve [inversion H]. *)
  (*   inversion H; subst; clear H. simpl. repeat rewrite Nat.eqb_refl. *)
  (*   destruct (bytes o); auto. inversion Heqb1. *)
  (* Qed. *)


  (* Lemma read_write : forall c ptr, *)
  (*     (exists val, read c ptr = Some val) -> *)
  (*     bind (read c ptr) (fun val => write c ptr val) = Some c. *)
  (* Proof. *)
  (*   intros. destruct H. simpl. rewrite H. unfold read in H. unfold write. *)
  (*   destruct ptr as (b & o). destruct c. simpl in *. *)
  (*   destruct (m0 b) eqn:?; try solve [inversion H]. destruct l1. *)
  (*   destruct (o <? size); try solve [inversion H]. *)
  (*   apply f_equal. (* not sure why I need apply *) *)
  (*   f_equal. apply functional_extensionality. intros. destruct (x0 =? b) eqn:?; auto. *)
  (*   rewrite <- (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in Heqb0; subst. *)
  (*   rewrite Heqo0. f_equal. f_equal. apply functional_extensionality. intros. *)
  (*   destruct (x0 =? o) eqn:?; auto. *)
  (*   rewrite <- (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in Heqb0. subst. auto. *)
  (* Qed. *)

  (* Lemma write_write : forall c ptr val, *)
  (*     bind (write c ptr val) (fun c' => write c' ptr val) = write c ptr val. *)
  (* Proof. *)
  (*   simpl. intros. destruct (write c ptr val) eqn:?; auto. unfold write in *. *)
  (*   destruct (m c (fst ptr)) eqn:?; try solve [inversion Heqo]. *)
  (*   destruct l0 eqn:?. destruct (snd ptr <? size) eqn:?; inversion Heqo. *)
  (*   simpl. rewrite Nat.eqb_refl. rewrite Heqb. apply f_equal. f_equal. *)
  (*   apply functional_extensionality. intros. destruct (x =? fst ptr); auto. *)
  (*   repeat f_equal. apply functional_extensionality. intros. *)
  (*   destruct (x0 =? snd ptr); auto. *)
  (* Qed. *)

  (** * Memory permissions **)

  (** Gives permission to allocate memory, assuming the last allocated block was [n-1] *)
  Program Definition malloc_perm (n : nat) : (@perm (Si * Ss)) :=
    {|
      (** always valid *)
      pre '(x, _) := length (lget x) = n;
      (** No new blocks are allocated *)
      rely '(x, _) '(y, _) := length (lget x) = length (lget y) /\
                                (forall ptr, fst ptr >= n ->
                                        sizeof (lget x) ptr = sizeof (lget y) ptr /\
                                          read (lget x) ptr = read (lget y) ptr);
      (** Existing blocks do not change *)
      guar '(x, _) '(y, _) :=
      (exists z, y = lput x z) /\
      (forall ptr, fst ptr < n ->
              read (lget x) ptr = read (lget y) ptr /\
                sizeof (lget x) ptr = sizeof (lget y) ptr);
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; auto. intros [] [].
    split; [| split]; try solve [etransitivity; eauto];
      (etransitivity; [apply H0 | apply H2]; eauto).
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] [] [] []]; auto.
    - split; auto. eexists. symmetry. apply lPutGet.
    - split.
      + destruct H, H1. subst. eexists. rewrite lPutPut. reflexivity.
      + intros. split; (etransitivity; [apply H0 | apply H2]; auto).
  Qed.

  Program Definition block_perm (size : nat) (ptr : addr) : (@perm (Si * Ss)) :=
    {|
    (** [ptr] points to the first cell of an allocated block of size [size] *)
    pre '(x, _) :=
      (* if we swap the order of the equality then the obligation automatically
      unifies and we lose info... *)
      Some size = sizeof (lget x) ptr;
    (** if [ptr] satisfies the precondition, the size of the block does not change *)
    rely '(x, _) '(y, _) :=
      sizeof (lget x) ptr = sizeof (lget y) ptr;
    (** no updates allowed *)
    guar '(x, _) '(y, _) := x = y;
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; etransitivity; eauto.
  Qed.

  Lemma malloc_block n size ptr :
    size > 0 ->
    fst ptr < n ->
    malloc_perm n ⊥ block_perm size ptr.
  Proof.
    intros Hsize Hn.
    constructor; intros [] [] ?; cbn in *; subst; auto.
    intros. apply H; auto.
  Qed.

  Program Definition read_perm (ptr : addr) (v : Value) : @perm (Si * Ss) :=
    {|
    (** [ptr] points to [v] *)
    pre '(x, _) := read (lget x) ptr = Some v;
    (** only checks if the memory [ptr] points to in the 2 memories are equal *)
    rely '(x, _) '(y, _) := read (lget x) ptr = read (lget y) ptr;
    (** no updates allowed *)
    guar '(x, _) '(y, _) := x = y;
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; [intros [] | intros [] [] [] ? ?]; subst; auto.
  Qed.

  Program Definition write_perm (ptr : addr) (v : Value) : (@perm (Si * Ss)) :=
    {|
    (* [ptr] points to [v] *)
    pre '(x, _) := Some v = read (lget x) ptr;
    (* only checks if the memory [ptr] points to in the 2 configs are equal *)
    rely '(x, _) '(y, _) := read (lget x) ptr = read (lget y) ptr;
    (* only the pointer we have write permission to may change *)
      guar '(x, _) '(y, _) :=
      (exists z, y = lput x z) /\
        (forall ptr', ptr <> ptr' -> read (lget x) ptr' = read (lget y) ptr') /\
        (forall ptr', sizeof (lget x) ptr' = sizeof (lget y) ptr') /\
        length (lget x) = length (lget y);
    |}.
  Next Obligation.
    constructor; [intros [] | intros [] [] []]; auto; etransitivity; eauto.
  Qed.
  Next Obligation.
    constructor; [intros [] |]; auto.
    - split; auto. eexists. symmetry. apply lPutGet.
    - intros [] [] [] [] []. split.
      + destruct H, H1. subst. eexists. rewrite lPutPut. reflexivity.
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
    split; intros; auto; destruct x, y; cbn in *; subst; reflexivity.
  Qed.

  Lemma write_lte_read : forall ptr v, write_perm ptr v <= read_perm ptr v.
  Proof.
    constructor; cbn; intros [] []; subst; auto. intros; subst.
    split; [| split; [| split]]; try reflexivity.
    eexists. symmetry. apply lPutGet.
  Qed.

  Lemma malloc_write : forall n ptr v,
      fst ptr < n ->
      malloc_perm n ⊥ write_perm ptr v.
  Proof.
    intros n ptr v. constructor; intros [] []; cbn in *; intros.
    - destruct ptr. split; [| intros [] ?; split]; auto; apply H0;
                      intro Heq; inversion Heq; subst; lia.
    - apply H0; auto.
  Qed.

  Lemma write_block : forall b o o' size v,
      block_perm size (b, o) ⊥ write_perm (b, o') v.
  Proof.
    constructor; intros [] [] ?; cbn in *; subst; auto.
    apply H.
  Qed.

  Lemma write_write_sep ptr ptr' v v' :
      ptr <> ptr' ->
      write_perm ptr v ⊥ write_perm ptr' v'.
  Proof.
    intros Hdiff. constructor; intros; destruct x, y; cbn; apply H; auto.
  Qed.

  Program Definition post_malloc_perm' n size : @perm (Si * Ss) :=
    {|
    pre '(x, _) :=
      length (lget x) = n + 1 /\
      Some size = sizeof (lget x) (n, 0) /\
      Some (VNum 0) = read (lget x) (n, 0);
    rely x y :=
      rely (malloc_perm (n + 1) ** block_perm size (n, 0) ** write_perm (n, 0) (VNum 0)) x y;
    rely_PO := rely_PO (malloc_perm (n + 1) ** block_perm size (n, 0) ** write_perm (n, 0) (VNum 0));
    guar x y :=
      guar (malloc_perm (n + 1) ** block_perm size (n, 0) ** write_perm (n, 0) (VNum 0)) x y;
    guar_PO := guar_PO (malloc_perm (n + 1) ** block_perm size (n, 0) ** write_perm (n, 0) (VNum 0));
    |}.

  Lemma sep_step_malloc' n size : sep_step (malloc_perm n)
                                          (post_malloc_perm' n size).
  Proof.
    apply sep_step_rg.
    - intros [si ss] [si' ss'] ?. induction H; try solve [etransitivity; eauto].
      destruct H.
      2: { destruct x, y. destruct H as (? & ? & ? & ?). split. apply H.
           split; auto.
           apply H0; intro Heq; inversion Heq; subst; cbn in *; lia.
      }
      induction H; try solve [etransitivity; eauto]. destruct H.
      + destruct x, y. split. apply H. split; apply H; lia.
      + destruct x, y. cbn in *. subst; split; auto.
        eexists. symmetry. apply lPutGet.
    - intros [si ss] [si' ss'] [Hlen Hptr]. simpl in *.
      split; [split; [split |] |]; auto; intros; apply Hptr; cbn; lia.
  Qed.

  (* Lemma read_write_separate_neq_ptr : forall ptr ptr' v v', *)
  (*     read_perm ptr v ⊥ write_perm ptr' v' <-> ptr <> ptr'. *)
  (* Proof. *)
  (*   split; repeat intro. *)
  (*   - destruct H as [? _]. simpl in *. subst. *)
  (*     specialize (sep_l (config_mem ptr' (Byte 0)) (config_mem ptr' (Byte 1))). *)
  (*     do 2 rewrite read_config_mem in sep_l. *)
  (*     assert (Some (Byte 0) = Some (Byte 1) -> False) by inversion 1. *)
  (*     apply H. clear H. apply sep_l. split; [| split; [| split]]; auto. *)
  (*     + intros. unfold read, config_mem. simpl. *)
  (*       destruct ptr', ptr'0. destruct (addr_neq_cases _ _ _ _ H); simpl in *. *)
  (*       * rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in H0. *)
  (*         apply Bool.not_true_is_false in H0. rewrite Nat.eqb_sym in H0. *)
  (*         rewrite H0. auto. *)
  (*       * destruct (n1 =? n); auto. destruct (n2 <? n0 + 1); auto. *)
  (*         rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in H0. *)
  (*         apply Bool.not_true_is_false in H0. rewrite Nat.eqb_sym in H0. *)
  (*         rewrite H0. auto. *)
  (*     + unfold alloc_invariant, allocated, config_mem. simpl. *)
  (*       repeat rewrite Nat.eqb_refl. auto. *)
  (*   - constructor; intros; simpl in *; subst; auto. *)
  (*     destruct H0. auto. *)
  (* Qed. *)

  (* Lemma write_write_separate_neq_ptr : forall ptr ptr' v v', *)
  (*     write_perm ptr v ⊥ write_perm ptr' v' <-> ptr <> ptr'. *)
  (* Proof. *)
  (*   split; intros. *)
  (*   - symmetry in H. eapply separate_antimonotone in H. symmetry in H. *)
  (*     eapply read_write_separate_neq_ptr. apply H. apply read_lte_write. *)
  (*   - constructor; intros; simpl in *; destruct H0; auto. *)
  (* Qed. *)

  (* Lemma read_separate : forall ptr ptr' v v', read_perm ptr v ⊥ read_perm ptr' v'. *)
  (* Proof. *)
  (*   constructor; intros; simpl in *; subst; reflexivity. *)
  (* Qed. *)

  (** * Memory mermission sets *)
  Definition malloc_Perms :=
    join_Perms (fun Q => exists n : nat, Q = singleton_Perms (malloc_perm n)).

  Definition read_Perms (ptr : addr) (P : Value -> Perms) : Perms :=
    join_Perms (fun Q => exists y : Value, Q = singleton_Perms (read_perm ptr y) * P y).

  Definition write_Perms (ptr : addr) (P : Value -> Perms) : Perms :=
    join_Perms (fun Q => exists y : Value, Q = singleton_Perms (write_perm ptr y) * P y).

  Example no_error_load s : no_errors (lput s (mem_at (0, 0) (VNum 1)))
                                      (load (VPtr (0, 0))).
  Proof.
    pstep. unfold load. rewritebisim @bind_trigger. constructor.
    left. pstep. rewrite lGetPut. constructor.
  Qed.
  Example no_error_store s : no_errors (lput s (mem_at (0, 0) (VNum 1)))
                                       (store (VPtr (0, 0)) (VNum 2)).
  Proof.
    pstep. unfold store. rewritebisim @bind_trigger. constructor.
    left. pstep. rewrite lGetPut. constructor.
  Qed.

  Lemma typing_malloc l :
    typing
      malloc_Perms
      (fun v _ => match v with
               | VPtr addr => malloc_Perms *
                             singleton_Perms (block_perm (S l) addr) *
                             write_Perms addr (fun _ => top_Perms)
               | _ => bottom_Perms
               end)
      (malloc (S l))
      (Ret tt).
  Proof.
    intros p si ss Hp Hpre. pstep. unfold malloc.
    destruct Hp as (? & (n & ?) & Hp); subst.
    (* read step *)
    rewritebisim @bind_trigger. econstructor; eauto; try reflexivity.
    (* write step *)
    rewritebisim @bind_trigger. unfold id. econstructor; eauto.
    { apply Hp in Hpre. apply Hp. cbn in *. rewrite lGetPut. split.
      - eexists. reflexivity.
      - intros ptr Hn. split.
        + unfold read, allocated. cbn. subst. rewrite nth_error_app_early; auto.
        + unfold sizeof. cbn. subst. rewrite nth_error_app_early; auto.
    }
    (* return *)
    { eapply sep_step_lte. apply Hp. apply sep_step_malloc'. }
    { econstructor; eauto.
      - cbn. repeat rewrite lGetPut. apply Hp in Hpre. cbn in Hpre.
        split; [| split].
        + rewrite last_length. lia.
        + unfold sizeof. cbn.
          rewrite nth_error_app_last; auto.
        + unfold read, allocated. cbn. rewrite nth_error_app_last; auto.
      - cbn. apply Hp in Hpre. rewrite Hpre.
        eexists. exists (write_perm (n, 0) (VNum 0)).
        split; [| split; [| split]].
        + do 2 eexists. split; [| split; [| split]]; try reflexivity.
          1: eexists; split.
          * exists (n + 1). reflexivity.
          * cbn. reflexivity.
          * apply malloc_block; cbn; lia.
        + eexists. split; [exists (VNum 0); reflexivity |].
          do 2 eexists. split; [cbn; reflexivity | split; [| split]]; cbn; auto.
          * apply separate_top.
          * apply sep_conj_perm_top.
        + symmetry. apply separate_sep_conj_perm.
          * symmetry. apply malloc_write; cbn; lia.
          * symmetry. apply write_block.
          * symmetry. apply malloc_block; cbn; lia.
        + constructor; auto.
          { intros [] (? & ? & ?). cbn in *. split; split; auto.
            - split; [| apply malloc_block; cbn; lia].
              apply H0.
            - symmetry. apply separate_sep_conj_perm; symmetry.
              + apply malloc_write. cbn. lia.
              + apply write_block.
              + apply malloc_block; cbn; lia.
          }
    }
  Qed.

  (*
  Lemma typing_free ptr (Q : Value -> Perms) :
    typing
      (write_Perms ptr Q * singleton_Perms (block_perm 1 ptr))
      (fun _ _ => bottom_Perms)
      (free (VPtr ptr))
      (Ret tt).
  Proof.
    intros p si ss Hp Hpre. pstep. unfold free.
    destruct Hp as (pwrite' & pblock & (? & (v & ?) & Hpwrite) & Hpblock & Hlte); subst.
    destruct Hpwrite as (pwrite & pv & Hpwrite & Hpv & Hlte').
    assert (Hoffset : snd ptr = 0).
    { apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
      apply Hpblock in Hpre. simpl in Hpre. unfold sizeof in Hpre.
      rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)).
      destruct (snd ptr =? 0); inversion Hpre; auto.
    }
    rewrite Hoffset. simpl.
    (* read step *)
    rewritebisim @bind_trigger. econstructor; auto; try reflexivity.
    pose proof Hpre as Hpre'. apply Hlte in Hpre'.
    destruct Hpre' as (Hprewrite & Hpreblock & Hsep).
    apply Hpblock in Hpreblock. simpl in Hpreblock.
    unfold sizeof in Hpreblock. rewrite Hoffset in Hpreblock. simpl in Hpreblock.
    destruct (nth_error (lget si) (fst ptr)) eqn:?; try solve [inversion Hpreblock].
    destruct o; try solve [inversion Hpreblock].
    destruct l. inversion Hpreblock; clear Hpreblock; subst.
    (* write step *)
    rewritebisim @bind_trigger. unfold id. econstructor; auto.
    - apply Hlte. constructor 1. left.
      apply Hlte'. constructor 1. left.
      apply Hpwrite. cbn.
      split; [| split]; rewrite lGetPut; simpl; auto.
      + intros. unfold read. unfold allocated. simpl.
        destruct ptr as [b o]; destruct ptr' as [b' o'].
        apply addr_neq_cases in H. simpl.
        admit. (* break up the <> into cases, then use nth_error_replace_list_index_eq/neq *)
      + admit.
      + assert (fst ptr < length (lget si)).
        { apply nth_error_Some. intro. rewrite H in Heqo. inversion Heqo. }
        apply replace_list_index_length; auto.
    - apply sep_step_lte'. apply bottom_perm_is_bottom.
    - constructor; simpl; auto.
  Admitted.
   *)

  (* Lemma typing_load {R} ptr (Q : Value -> Perms) (r : R) : *)
  (*   typing *)
  (*     (read_Perms ptr Q) *)
  (*     (fun x _ => (read_Perms ptr (eq_p x)) * Q x) *)
  (*     (load (VPtr ptr)) *)
  (*     (Ret r). *)
  (* Proof. *)
  (*   repeat intro. pstep. unfold load. rewritebisim @bind_trigger. *)
  (*   econstructor; eauto; try reflexivity. *)
  (*   destruct H as (? & (? & ?) & ?); subst. *)
  (*   destruct H1 as (? & ? & ? & ? & ?). simpl in *. *)
  (*   assert (read (lget c1) ptr = Some x0). *)
  (*   { apply H2 in H0. destruct H0 as (? & _). apply H in H0. auto. } *)
  (*   rewrite H3. constructor; eauto. *)
  (*   simpl. exists x, x1. split; [| split]; eauto. eexists. split; eauto. *)
  (*   simpl. exists x, bottom_perm. split; [| split]; eauto. *)
  (*   rewrite sep_conj_perm_bottom. reflexivity. *)
  (* Qed. *)

  Lemma typing_store {R} ptr val' (P Q : Value -> Perms) (r : R) :
    typing
      (write_Perms ptr P * Q val')
      (fun _ _ => write_Perms ptr Q)
      (store (VPtr ptr) val')
      (Ret r).
  Proof.
    intros p'' c1 c2 H Hpre. pstep. unfold store. rewritebisim @bind_trigger.
    destruct H as (p' & q & Hwrite & Hq & Hsep & Hlte).
    destruct Hwrite as (? & (v & ?) & Hwrite); subst.
    destruct Hwrite as (pw & p & Hwritelte & Hp & Hsep' & Hlte'). cbn in *.
    assert (exists val, read (lget c1) ptr = Some val).
    {
      apply Hlte in Hpre. destruct Hpre as (Hpre & _).
      apply Hlte' in Hpre. destruct Hpre as (Hpre & _).
      apply Hwritelte in Hpre. eexists. symmetry. apply Hpre.
    }
    destruct H as (val & Hread). eapply (read_success_write _ _ _ val') in Hread.
    destruct Hread as (c' & Hwrite).
    assert (Hguar : guar p' (c1, c2) ((lput c1 c'), c2)).
    {
      apply Hlte'. constructor 1. left. apply Hwritelte. cbn.
      rewrite lGetPut.
      split; [| split; [| split]].
      + eexists. reflexivity.
      + eapply write_success_read_neq; eauto.
      + eapply write_success_sizeof; eauto.
      + rewrite lGetPut. eapply write_success_length; eauto.
    }
    econstructor; eauto.
    3: {
      assert (write_perm ptr val' ⊥ q).
      {
        apply Hlte in Hpre. symmetry in Hsep.
        eapply separate_upwards_closed in Hsep; eauto. apply separate_sep_conj_perm_l in Hsep.
        eapply separate_upwards_closed in Hsep; eauto. symmetry. constructor; apply Hsep.
      }
      rewrite Hwrite. constructor; eauto.
      2: { eexists. split. exists val'. reflexivity.
           cbn. eexists. exists q.
           split; [reflexivity | split; [| split; [| reflexivity]]]; eauto.
      }
      split; [| split]; auto.
      - symmetry. eapply write_success_read_eq; rewrite lGetPut; eauto.
      - apply Hlte in Hpre. respects. 2: apply Hpre; eauto.
        apply Hpre. auto.
    }
    - rewrite Hwrite. apply Hlte. constructor 1. left. auto.
    - eapply sep_step_lte; eauto. apply sep_step_sep_conj_l.
      { apply Hlte in Hpre. apply Hpre. }
      eapply sep_step_lte; eauto. eapply sep_step_lte. apply lte_l_sep_conj_perm.
      eapply sep_step_lte; eauto.
      intros ? []. constructor; auto.
  Qed.

  (* Lemma typing_store' {R} ptr val' (P : Value -> Perms) (r : R): *)
  (*   typing *)
  (*     (write_Perms ptr P) *)
  (*     (fun _ _ => write_Perms ptr (eq_p val')) *)
  (*     (store (VPtr ptr) val') *)
  (*     (Ret r). *)
  (* Proof. *)
  (*   assert (bottom_Perms ≡ @eq_p Si Ss _ val' val'). *)
  (*   { split; repeat intro; simpl; auto. } *)
  (*   rewrite <- sep_conj_Perms_bottom_identity. rewrite sep_conj_Perms_commut. *)
  (*   rewrite H. apply typing_store. *)
  (* Qed. *)

  Definition offset (v : Value) (o : nat) : Value :=
    match v with
    | VNum n => VNum n (* Do nothing. offset is never used with VNums. *)
    | VPtr (blk, n) => VPtr (blk, n + o)
    end.

  Definition ptr_Perms {A} (rw : RW) (p : Value) (a : A) (T : VPermType A) : @Perms (Si * Ss) :=
    match p with
    | VNum _ => bottom_Perms
    | VPtr p =>
        join_Perms (fun P => exists (v : Value),
                        P = singleton_Perms (match rw with
                                             | R => read_perm p v
                                             | W => write_perm p v
                                             end) *
                              (v :: T ▷ a))
    end.

  Definition ptr {A} '(rw, o, T) : VPermType A :=
    {|
      ptApp := fun x a => ptr_Perms rw (offset x o) a T;
    |}.

  Fixpoint arr_perm {A} rw o l T : VPermType (Vector.t A l) :=
    match l with
    | 0 => trueP
    | S l' =>
        {| ptApp := fun xi xss =>
                      xi :: ptr (rw, o, T) ▷ Vector.hd xss *
                        xi :: arr_perm rw (S o) l' T ▷ Vector.tl xss
        |}
    end.
  Notation "'arr' ( rw , o , l , T )" := (arr_perm rw o l T).

  Definition blockPT l : VPermType unit :=
    {| ptApp := fun a _ => match a with
                        | VPtr ptr => singleton_Perms (block_perm l ptr)
                        | _ => bottom_Perms
                        end |}.

  Lemma reach_perm_proper {A} r (T : VPermType A) rw o :
    Proper (lte_PermType ==> lte_PermType)
           (fun U : VPermType (list A) => or (eqp r) (T ⋆ (ptr (rw, o, U)))).
  Proof.
    intros T1 T2 Hlte v l p Hp. cbn.
    destruct l as [| ?]; cbn in *; auto.
    destruct Hp as (pt & pptr & Hpt & Hpptr & Hlte').
    exists pt, pptr. split; [| split]; auto.
    clear Hpt. unfold ptr_Perms in *.
    destruct (offset v o) as [? | l]; auto.
    destruct Hpptr as (? & (v' & ?) & Hpptr); subst.
    destruct Hpptr as (? & ? & ? & ? & ?).
    eexists. split; eauto. do 2 eexists. split; [| split]; eauto. apply Hlte. auto.
  Qed.

  Program Definition reach_perm {A}
          (r : Value) (rw : RW) (o : nat)
          (T : VPermType A)
    : VPermType (list A) :=
    @mu _ _ _ (mu_list A) _ (fixed_point_list _)
        (fun U => or (eqp r) (T ⋆ (ptr (rw, o, U))))
        (reach_perm_proper _ _ _ _).

  Program Definition list_perm rw A (T : VPermType A) : VPermType (list A) :=
    @mu _ _ _ (mu_list A) _ (fixed_point_list _) (fun U => or (eqp (VNum 0)) (ptr (rw, 0, T) ⋆ ptr (rw, 1, U))) _.
  Next Obligation.
    repeat intro. cbn. induction b; cbn in *; auto.
    destruct H0 as (? & ? & ? & ? & ? & ?). exists x0, x1. split; [| split]; auto.
    clear H0. unfold ptr_Perms in *. destruct (offset a 1); auto.
    destruct H1. destruct H0 as ((? & ?) & ?). subst. destruct H1 as (? & ? & ? & ? & ?).
    eexists. split; eauto. do 2 eexists. split; eauto. split; eauto. apply H. auto.
  Qed.

  Definition list_reach_perm {A} r rw (T : VPermType A) : VPermType (list A) :=
    reach_perm r rw 1 (ptr (rw, 0, T)).

  Lemma reach_refl {A} x rw o (T : VPermType A) :
    x :: trueP ▷ tt ⊑ x :: reach_perm x rw o T ▷ nil.
  Proof.
    repeat intro. apply mu_fixed_point. reflexivity.
  Qed.

  Lemma reach_trans {A} x y z rw o (T : VPermType A) xs ys :
    x :: reach_perm y rw o T ▷ xs * y :: reach_perm z rw o T ▷ ys ⊑
                                     x :: reach_perm z rw o T ▷ (xs ++ ys).
  Proof.
    revert x.
    induction xs.
    - intros x p (p1 & p2 & Hp1 & Hp2 & Hsep & Hlte).
      destruct Hp1 as (? & (U & HU & ?) & Hp1); subst.
      apply HU in Hp1. cbn in Hp1. subst. eapply Perms_downwards_closed; eauto.
      etransitivity; eauto. apply lte_r_sep_conj_perm.
    - intros x p (px' & py & Hpx' & Hpy & Hsep & Hlte).
      eapply mu_fixed_point in Hpx'.
      destruct Hpx' as (pa & px & Hpa & Hpx & Hsep' & Hlte').
      (* x must be a pointer *)
      destruct x; try contradiction. destruct a0 as [b o'].
      destruct Hpx as (? & (v & ?) & Hpx); subst.
      destruct Hpx as (px'' & pv & Hpx'' & Hpv & Hsep'' & Hlte'').

      apply mu_fixed_point. cbn.
      exists pa, (px'' ** (pv ** py)). split; [apply Hpa | split; [| split]].
      3: { repeat rewrite <- sep_conj_perm_assoc.
           etransitivity; eauto.
           eapply sep_conj_perm_monotone; intuition.
           repeat rewrite sep_conj_perm_assoc.
           etransitivity; eauto.
           eapply sep_conj_perm_monotone; intuition.
      }
      2: {
        apply separate_sep_conj_perm.
        - eapply separate_upwards_closed; eauto.
          etransitivity; eauto. apply lte_l_sep_conj_perm.
        - apply separate_sep_conj_perm.
          + eapply separate_upwards_closed; eauto.
            etransitivity; eauto. apply lte_r_sep_conj_perm.
          + symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
            etransitivity; eauto. apply lte_l_sep_conj_perm.
          + symmetry in Hsep. eapply separate_upwards_closed; eauto.
            etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
            apply sep_conj_perm_monotone. reflexivity.
            etransitivity; eauto. apply lte_r_sep_conj_perm.
        - symmetry. apply separate_sep_conj_perm.
          + eapply separate_upwards_closed; eauto. reflexivity.
          + symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
            etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
            apply sep_conj_perm_monotone. reflexivity.
            etransitivity; eauto. apply lte_l_sep_conj_perm.
          + symmetry in Hsep. eapply separate_upwards_closed; eauto.
            etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
            apply sep_conj_perm_monotone. reflexivity.
            etransitivity; eauto. apply lte_r_sep_conj_perm.
      }
      eexists; split; [eexists; reflexivity |].
      apply sep_conj_Perms_perm; [apply Hpx'' | |].
      2: {
        apply separate_sep_conj_perm; auto.
        + symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
          etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
          apply sep_conj_perm_monotone. reflexivity.
          etransitivity; eauto. apply lte_l_sep_conj_perm.
        + symmetry in Hsep. eapply separate_upwards_closed; eauto.
          etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
          apply sep_conj_perm_monotone. reflexivity.
          etransitivity; eauto. apply lte_r_sep_conj_perm.
      }
      cbn. exists (v :: reach_perm z rw o T ▷ (xs ++ ys)). split.
      2: {
        apply IHxs. apply sep_conj_Perms_perm; auto.
        symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
        etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
        apply sep_conj_perm_monotone. reflexivity.
        etransitivity; eauto. apply lte_r_sep_conj_perm.
      }
      eexists; split; eauto.
      repeat intro. eapply mu_fixed_point in H; auto.
      Unshelve. all: apply reach_perm_proper.
  Qed.

  (** * Pointer rules *)

  Lemma PtrI A xi yi xs ys rw o (T : @VPermType Si Ss A) :
    xi :: ptr (rw, o, eqp yi) ▷ xs * yi :: T ▷ ys ⊑ xi :: ptr (rw, o, T) ▷ ys.
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

  Lemma PtrE A B C (P : Perms) rw o (T : @VPermType Si Ss A) (xi : Value) xs ti ts (U : @PermType Si Ss B C) :
    (forall yi, P * xi :: ptr (rw, o, eqp yi) ▷ tt * yi :: T ▷ xs ⊢ ti ⤳ ts ::: U) ->
    P * xi :: ptr (rw, o, T) ▷ xs ⊢ ti ⤳ ts ::: U.
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

  Lemma PtrWeak A o xi (T : VPermType A) xs :
    xi :: ptr (W, o, T) ▷ xs ⊑ xi :: ptr (R, o, T) ▷ xs.
  Proof.
    repeat intro. cbn in *. destruct xi; [contradiction |].
    destruct a as [b o']. unfold offset in *.
    destruct H as (? & (v & ?) & ?). subst.
    destruct H0 as (pwrite & pt & Hpwrite & Hpt & Hsep & Hlte). cbn in Hpwrite.
    eexists. split.  eexists. reflexivity.
    exists (read_perm (b, o' + o) v), pt.
    split; [| split; [| split]]; eauto.
    - cbn. reflexivity.
    - symmetry. eapply separate_upwards_closed. symmetry. eauto.
      etransitivity; eauto. apply write_lte_read.
    - etransitivity; eauto. apply sep_conj_perm_monotone; [| reflexivity].
      etransitivity; eauto. apply write_lte_read.
  Qed.

  Lemma ReadDup o xi yi :
    xi :: ptr (R, o, eqp yi) ▷ tt ⊑
       xi :: ptr (R, o, eqp yi) ▷ tt * xi :: ptr (R, o, eqp yi) ▷ tt.
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

  Lemma PtrOff A xi xs rw o1 o2 (T : @VPermType Si Ss A) :
    o1 >= o2 ->
    xi :: ptr (rw, o1, T) ▷ xs ⊑ offset xi o2 :: ptr (rw, o1 - o2, T) ▷ xs.
  Proof.
    destruct xi; [reflexivity | destruct a].
    intros. cbn. rewrite <- Nat.add_assoc.
    rewrite (Nat.add_comm o2 _). rewrite Nat.sub_add; auto.
    reflexivity.
  Qed.
  Lemma PtrOff' A xi xs rw o1 o2 (T : @VPermType Si Ss A) :
    o1 >= o2 ->
    offset xi o2 :: ptr (rw, o1 - o2, T) ▷ xs ⊑ xi :: ptr (rw, o1, T) ▷ xs.
  Proof.
    destruct xi; [reflexivity | destruct a].
    intros. cbn. rewrite <- Nat.add_assoc.
    rewrite (Nat.add_comm o2 _). rewrite Nat.sub_add; auto.
    reflexivity.
  Qed.

  Lemma Load xi yi xs rw :
    xi :: ptr (rw, 0, eqp yi) ▷ xs ⊢
       load xi ⤳
       Ret tt :::
       eqp yi ∅ xi :: ptr (rw, 0, eqp yi) ▷ xs.
  Proof.
    repeat intro. pstep. unfold load. rewritebisim @bind_trigger.
    econstructor; eauto; try reflexivity.
    destruct xi as [? | [b o]]; try contradiction.
    cbn in H.
    destruct H as (? & (v & ?) & ?); subst.
    destruct H1 as (? & ? & ? & ? & Hsep & Hlte). cbn in H, H1. subst.
    assert (read (lget c1) (b, o) = Some v).
    {
      apply Hlte in H0. destruct H0 as (? & _).
      rewrite Nat.add_0_r in H. apply H in H0. destruct rw; auto.
    }
    rewrite H1. constructor; auto.
    (* TODO: these exists are kind of weird *)
    exists top_perm, x. split; [| split; [| split]]; auto.
    - cbn. auto.
    - cbn. eexists. split; eauto.
      cbn. exists x, top_perm. split; [| split; [| split]]; eauto.
      apply separate_top.
      rewrite sep_conj_perm_top. reflexivity.
    - symmetry. apply separate_top.
    - rewrite sep_conj_perm_commut. rewrite sep_conj_perm_top.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
  Qed.

  Lemma Store A xi yi xs (P : @VPermType Si Ss A) :
    xi :: ptr (W, 0, P) ▷ xs ⊢
       store xi yi ⤳
       Ret tt :::
       trueP ∅ xi :: ptr (W, 0, eqp yi) ▷ tt.
  Proof.
    repeat intro. pstep. unfold store. destruct xi as [| [b o]]; try contradiction.
    rewritebisim @bind_trigger.
    rename p into p'. rename H0 into Hpre.
    destruct H as (? & (v & ?) & Hwrite); subst.
    destruct Hwrite as (pw & p & Hwritelte & Hp & Hsep & Hlte).
    rewrite Nat.add_0_r in Hwritelte.
    assert (exists val, read (lget c1) (b, o) = Some val).
    {
      apply Hlte in Hpre. destruct Hpre as (Hpre & _).
      apply Hwritelte in Hpre. eexists.
      symmetry. apply Hpre.
    }
    destruct H as (val & Hread). eapply (read_success_write _ _ _ yi) in Hread.
    destruct Hread as (c' & Hwrite).
    assert (Hguar : guar p' (c1, c2) ((lput c1 c'), c2)).
    {
      apply Hlte. constructor 1. left. apply Hwritelte. cbn.
      repeat rewrite lGetPut.
      split; [| split; [| split]].
      + eexists. reflexivity.
      + eapply write_success_read_neq; eauto.
      + eapply write_success_sizeof; eauto.
      + eapply write_success_length; eauto.
    }
    econstructor; eauto.
    3: {
      rewrite Hwrite. constructor; eauto.
      2: { cbn. exists top_perm. eexists. split; [| split; [| split]]; auto.
           - eexists. split; eauto. cbn. eexists. exists top_perm.
             split; [| split; [| split]]; eauto; try reflexivity.
             apply separate_top.
           - symmetry. apply separate_top.
           - rewrite sep_conj_perm_top. rewrite sep_conj_perm_commut.
             rewrite sep_conj_perm_top. reflexivity.
      }
      rewrite Nat.add_0_r. symmetry. eapply write_success_read_eq; rewrite lGetPut; eauto.
    }
    - rewrite Hwrite. auto.
    - rewrite Nat.add_0_r. eapply sep_step_lte; eauto.
      etransitivity.
      + eapply sep_step_lte; [| reflexivity]. apply lte_l_sep_conj_perm.
      + cbn in *. eapply sep_step_lte; eauto. apply sep_step_write_perm.
  Qed.

  Lemma IsNull1 A xi xs rw o (P : @VPermType Si Ss A) :
    xi :: ptr (rw, o, P) ▷ xs ⊢
       isNull xi ⤳
       Ret tt :::
       eqp false ∅ xi :: ptr (rw, o, P) ▷ xs.
  Proof.
    repeat intro. pstep. unfold isNull. destruct xi; [contradiction |].
    destruct a as [b o']. cbn. constructor; auto.
    cbn. exists top_perm, p. split; [| split; [| split]]; eauto.
    - symmetry. apply separate_top.
    - rewrite sep_conj_perm_commut. rewrite sep_conj_perm_top. reflexivity.
  Qed.

  Lemma IsNull2 xi:
    xi :: @eqp Si Ss _ (VNum 0) ▷ tt ⊢
       isNull xi ⤳
       Ret tt :::
       eqp true.
  Proof.
    repeat intro. pstep. cbn in *. subst. constructor; cbn; auto.
  Qed.

  (*
  (** * Example 2 *)
  Definition ex2i xi yi : itree (sceE Si) Si :=
    x <- load xi;;
    store yi x.

  Definition ex2s : itree (sceE Ss) unit :=
    Ret tt ;;
    Ret tt.

  Lemma ex2_typing A (xi yi : Value) xs (T : @VPermType Si Ss A) :
    xi :: ptr (R, 0, T) ▷ xs * yi :: ptr (W, 0, trueP) ▷ tt ⊢
                                 ex2i xi yi ⤳
                                 ex2s :::
                                 trueP ∅ yi :: ptr (W, 0, T) ▷ xs ∅ xi :: ptr (R, 0, trueP) ▷ tt.
  Proof.
    (* PtrE *)
    rewrite sep_conj_Perms_commut.
    eapply PtrE; eauto; intros zi.
    (* Bind *)
    eapply Bind.
    (* L: Frame and Load *)
    apply Frame. rewrite sep_conj_Perms_commut. apply Frame. apply Load.
    (* Weak *)
    intros wi [].
    eapply Weak with (P2 := yi :: ptr _ _ (W, 0, trueP _ _) ▷ tt *
                              wi :: T ▷ xs *
                              xi :: ptr _ _ (R, 0, trueP _ _) ▷ tt)
                     (U2 := trueP _ _ ∅
                                  yi :: ptr _ _ (W, 0, eqp _ _ wi) ▷ tt ∅
                                  wi :: T ▷ xs ∅
                                  xi :: ptr _ _ (R, 0, trueP _ _) ▷ tt).
    (* Input type *)
    - etransitivity.
      (* PermsE *)
      {
        etransitivity; [apply PermsE |]. rewrite sep_conj_Perms_commut.
        eapply sep_conj_Perms_monotone; [reflexivity |]. (* frame *)
        etransitivity; [| apply PermsE]. rewrite sep_conj_Perms_commut.
        eapply sep_conj_Perms_monotone; [reflexivity |]. (* frame *)
        etransitivity; [| apply PermsE]. rewrite sep_conj_Perms_commut. reflexivity.
      }
      rewrite (sep_conj_Perms_commut (zi :: T ▷ xs) _).
      repeat rewrite <- sep_conj_Perms_assoc.
      apply sep_conj_Perms_monotone; [reflexivity |].
      rewrite sep_conj_Perms_commut.
      eapply sep_conj_Perms_monotone.
      (* Weakening the content type *)
      + etransitivity; [apply PtrI | apply TrueI].
      (* Cast *)
      + apply Cast.
    (* Output type *)
    - intros ? [].
      etransitivity; [apply PermsE |].
      etransitivity; [| apply PermsI].
      eapply sep_conj_Perms_monotone; [| reflexivity]. (* frame *)
      etransitivity; [| apply PermsE].
      etransitivity; [apply PermsI |].
      etransitivity.
      2: {
        eapply sep_conj_Perms_monotone; [| reflexivity]. (* frame *)
        apply PermsE.
      }
      rewrite <- sep_conj_Perms_assoc.
      eapply sep_conj_Perms_monotone; [reflexivity |]. (* frame *)
      (* PtrI *)
      apply PtrI.
    (* Frame and Store *)
    - apply Frame. apply Frame. apply Store.
  Qed.

   *)


  Definition load_store p : itree (sceE Si) unit :=
    p' <- load p;;
    store p' (VNum 1).

  Definition spec : itree (sceE Ss) unit :=
    Ret tt ;;
    Ret tt.

  Lemma load_store_typing p :
    p :: ptr (R, 0, (ptr (W, 0, trueP))) ▷ tt ⊢
      load_store p ⤳
      spec :::
      trueP ∅ p :: ptr (R, 0, (ptr (W, 0, eqp (VNum 1)))) ▷ tt.
  Proof.
    (* PtrE *)
    eapply Weak; [apply TrueI | reflexivity | ].
    rewrite sep_conj_Perms_commut.
    eapply PtrE; eauto; intros p'.

    (* Bind *)
    eapply Bind.
    {
      rewrite sep_conj_Perms_top_identity.
      (* Frame *)
      apply Frame.
      (* Load *)
      apply Load.
    }
    {
      intros xi [].
      (* Weak *)
      apply Weak with
        (P2 := xi :: ptr (W, 0, trueP) ▷ tt * p :: ptr (R, 0, eqp xi) ▷ tt)
        (U2 := trueP ∅ xi :: ptr (W, 0, eqp (VNum 1)) ▷ tt ∅ p :: ptr (R, 0, eqp xi) ▷ tt).
      {
        etransitivity. apply PermsE.
        rewrite sep_conj_Perms_commut.
        etransitivity. apply sep_conj_Perms_monotone. reflexivity.
        apply sep_conj_Perms_monotone.
        etransitivity. apply EqSym. apply EqDup.
        reflexivity.
        rewrite <- sep_conj_Perms_assoc.
        etransitivity. apply sep_conj_Perms_monotone. reflexivity.
        etransitivity. apply sep_conj_Perms_monotone. reflexivity.
        rewrite sep_conj_Perms_commut. apply PtrI. reflexivity.

        rewrite sep_conj_Perms_assoc.
        apply sep_conj_Perms_monotone. 2: reflexivity.
        rewrite sep_conj_Perms_commut.
        etransitivity. apply sep_conj_Perms_monotone. apply EqSym. reflexivity.
        apply Cast.
      }
      2: {
        apply Frame.
        apply Store.
      }
      {
        clear p'. rename xi into p'.
        intros [] [].

        etransitivity. apply PermsE.
        rewrite sep_conj_Perms_commut.
        etransitivity. apply sep_conj_Perms_monotone. reflexivity.
        apply PermsE.
        rewrite sep_conj_Perms_commut.
        rewrite <- sep_conj_Perms_assoc.
        etransitivity. apply sep_conj_Perms_monotone. reflexivity.
        rewrite sep_conj_Perms_commut. apply PtrI.

        etransitivity. apply PermsI. reflexivity.
      }
    }

    Unshelve. apply unit. apply tt.
  Qed.


  (** * Array rules *)
  Lemma ArrCombine_eq A xi rw o l1 l2 (l:le l2 l1) xs1 xs2 (P : @VPermType Si Ss A) :
    eq_Perms (xi :: arr (rw, o, l1, P) ▷ append_leq l1 l2 l xs1 xs2)
             (xi :: arr (rw, o, l2, P) ▷ xs1 * xi :: arr (rw, o + l2, l1 - l2, P) ▷ xs2).
  Proof.
    revert o l2 l xs1 xs2; induction l1; intros.
    - inversion l. subst. cbn. rewrite sep_conj_Perms_top_identity. reflexivity.
    - destruct l2.
      + rewrite sep_conj_Perms_top_identity.
        rewrite Nat.add_0_r. reflexivity.
      + cbn. rewrite (IHl1 (S o) l2).
        rewrite Nat.add_succ_r.
        rewrite sep_conj_Perms_assoc.
        reflexivity.
  Qed.

  Lemma ArrSplit A R1 R2 P l1 l2 xi xs rw o (T : @VPermType Si Ss A) U (ti : itree (sceE Si) R1) (fs : _ -> _ -> itree (sceE Ss) R2) :
    (forall xs1 xs2, P *
                  xi :: arr (rw, o, l2, T) ▷ xs1 *
                  xi :: arr (rw, o + l2, l1 - l2, T) ▷ xs2 ⊢
                     ti ⤳ fs xs1 xs2 ::: U) ->
    P * xi :: arr (rw, o, l1, T) ▷ xs ⊢ ti ⤳ trySplit xs l2 fs ::: U.
  Proof.
    intros. unfold trySplit. destruct (Compare_dec.le_lt_dec l2 l1).
    - rewrite <- (split_leq_append_leq _ l1 xs l2 l).
      rewrite ArrCombine_eq. repeat rewrite split_leq_append_leq.
      rewrite sep_conj_Perms_assoc.
      apply H.
    - apply Err.
  Qed.

  Lemma ArrCombine A xi rw o l1 l2 xs1 xs2 (P : @VPermType Si Ss A) :
    xi :: arr (rw, o, l1, P) ▷ xs1 * xi :: arr (rw, o + l1, l2, P) ▷ xs2 ⊑
    xi :: arr (rw, o, l1 + l2, P) ▷ Vector.append xs1 xs2 .
  Proof.
    repeat intro. destruct H as (p1 & p2 & Hp1 & Hp2 & Hsep & Hlte).
    revert Hp1 Hp2. revert o xi l2 xs2. revert Hsep Hlte. revert p p1 p2. induction l1; intros.
    - rewrite Nat.add_0_r in Hp2. cbn in *. revert xs1. apply Vector.case0. cbn.
      eapply Perms_downwards_closed; eauto. etransitivity; [| apply lte_r_sep_conj_perm]; eauto.
    - cbn. destruct Hp1 as (? & ? & ? & ? & Hsep' & Hlte').
      do 2 eexists. split; [| split; [| split]].
      + rewrite vector_hd_append. apply H.
      + rewrite vector_tl_append. eapply IHl1. 2: reflexivity.
        2: { eapply Perms_downwards_closed; eauto. reflexivity. }
        2: { cbn. rewrite <- plus_n_Sm in Hp2. eauto. }
        symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
        etransitivity; eauto. apply lte_r_sep_conj_perm.
      + apply separate_sep_conj_perm; auto.
        * symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
          etransitivity; eauto. apply lte_l_sep_conj_perm.
        * symmetry in Hsep. eapply separate_upwards_closed; eauto.
          etransitivity; eauto. apply lte_r_sep_conj_perm.
      + rewrite <- sep_conj_perm_assoc. etransitivity; eauto.
        apply sep_conj_perm_monotone; eauto; reflexivity.
  Qed.

  Lemma ArrPtr A xi xs rw o (P : @VPermType Si Ss A) :
    xi :: arr (rw, o, 1, P) ▷ xs ⊑ xi :: ptr (rw, o, P) ▷ Vector.hd xs.
  Proof.
    cbn. rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_top_identity. reflexivity.
  Qed.

  Lemma PtrArr A xi xs rw o (P : @VPermType Si Ss A) :
    xi :: ptr (rw, o, P) ▷ xs ⊑ xi :: arr (rw, o, 1, P) ▷ vsingle xs.
  Proof.
    cbn. rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_top_identity. reflexivity.
  Qed.

  Lemma arr_offset {A} ptr rw o l (T : @VPermType Si Ss A) (v : Vector.t A l) :
    VPtr ptr :: arr (rw, o, l, T) ▷ v ≡ offset (VPtr ptr) o :: arr (rw, 0, l, T) ▷ v.
  Proof.
    revert ptr o. induction l; intros ptr o; try reflexivity.
    split.
    - cbn. apply sep_conj_Perms_monotone.
      + destruct ptr. cbn. rewrite Nat.add_0_r. reflexivity.
      + destruct ptr. rewrite (IHl _ _ 1). cbn.
        specialize (IHl (Vector.tl v) (n, n0) (o + 1)). cbn in IHl.
        rewrite Nat.add_assoc in IHl. rewrite Nat.add_1_r in IHl. apply IHl.
    - cbn. apply sep_conj_Perms_monotone.
      + destruct ptr. cbn. rewrite Nat.add_0_r. reflexivity.
      + destruct ptr. rewrite (IHl _ _ 1). cbn.
        specialize (IHl (Vector.tl v) (n, n0) (o + 1)). cbn in IHl.
        rewrite Nat.add_assoc in IHl. rewrite Nat.add_1_r in IHl. apply IHl.
  Qed.

  (** * Malloc *)
  (** helper lemmas for Malloc *)
  Fixpoint rely_post_malloc n b size x y : Prop :=
    match n with
    | 0 => rely (block_perm size (b, 0) ** malloc_perm (b + 1)) x y
    | S n => rely (write_perm (b, size - S n) (VNum 0)) x y /\
              rely_post_malloc n b size x y
    end.
  Lemma PO_rely_post_malloc n b size :
    PreOrder (rely_post_malloc n b size).
  Proof.
    constructor.
    - intros []; induction n; cbn; auto.
    - intros [] [] [] ? ?. induction n.
      + split; [| split]; try solve [etransitivity; [apply H | apply H0]].
        intros; split; (etransitivity; [apply H | apply H0]); auto.
      + split; try solve [etransitivity; [apply H | apply H0]].
        apply IHn; [apply H | apply H0].
  Qed.

  Fixpoint guar_post_malloc n b size x y : Prop :=
    match n with
    | 0 => guar (block_perm size (b, 0) ** malloc_perm (b + 1)) x y
    | S n => clos_trans _ (fun x y =>
                            guar (write_perm (b, size - S n) (VNum 0)) x y \/
                              guar_post_malloc n b size x y) x y
    end.
  #[local] Instance PO_guar_post_malloc n b size :
    PreOrder (guar_post_malloc n b size).
  Proof.
    constructor.
    - intros []. induction n; cbn; intuition.
    - intros [] [] [] ? ?.
      destruct n; econstructor 2; eauto.
  Qed.

  Definition pre_post_malloc n b size : Si * Ss -> Prop :=
    fun '(x, _) =>
      b + 1 = length (lget x) /\
        Some size = sizeof (lget x) (b, 0) /\
        forall o, o < size -> (size - n <= o)%nat -> Some (VNum 0) = read (lget x) (b, o).
  Lemma pre_respects_post_malloc n b size :
    forall x y, rely_post_malloc (S n) b size x y -> (* we need the fact that n > 0 here *)
           pre_post_malloc (S n) b size x ->
           pre_post_malloc (S n) b size y.
  Proof.
    intros [] [] Hrely (Hlen & Hsizeof & Hread).
    cbn in *.
    induction n; cbn in *.
    - destruct Hrely as (Hread' & Hsizeof' & Hlen' & Hptr).
      split; [rewrite <- Hlen' | split; [rewrite <- Hsizeof' |]]; auto.
      intros. assert (o = size - 1) by lia. subst.
      rewrite <- Hread'. auto.
    - destruct Hrely as (Hread' & Head'' & Hrely). split; [| split].
      + apply IHn; auto. intros. apply Hread; auto. lia.
      + apply IHn; auto. intros. apply Hread; auto. lia.
      + intros. assert (size - S (S n) = o \/ (size - S n <= o)%nat) by lia.
        destruct H1.
        * subst. rewrite <- Hread'. auto.
        * apply IHn; auto. intros. apply Hread; auto. lia.
  Qed.

  (** The intermediate permission for Malloc. *)
  (** [n] is the number of unfoldings to do for the rely/guar. [size] is the size of the block.
    when we use this [n = size], but we need them separate to do induction on [n] *)
  Program Definition post_malloc_perm n b size : @perm (Si * Ss) :=
    {|
      rely := rely_post_malloc (S n) b (S size);
      rely_PO := PO_rely_post_malloc (S n) b (S size);
      guar := guar_post_malloc (S n) b (S size);
      guar_PO := PO_guar_post_malloc (S n) b (S size);
      pre := pre_post_malloc (S n) b (S size);
      pre_respects := pre_respects_post_malloc n b (S size); (* S is applied inside this defn *)
    |}.

  Lemma guar_malloc_post_malloc n b size x y :
    guar_post_malloc n b (S size) x y -> guar (malloc_perm b) x y.
  Proof.
    revert x y. induction n; intros.
    - induction H; try solve [etransitivity; eauto]. destruct H.
      + destruct x, y. cbn in *. subst; split; auto.
        eexists. symmetry. apply lPutGet.
      + destruct x, y. split; [| split]; apply H; lia.
    - induction H; auto.
      + destruct H.
        * destruct x, y. destruct H as (? & ? & ? & ?). split; [| split]; auto.
          apply H0. destruct ptr0. intro. inversion H4. cbn in *. lia.
        * apply IHn; auto.
      + etransitivity; eauto.
  Qed.

  Lemma rely_malloc_post_malloc n b size x y :
    rely (malloc_perm b) x y -> rely_post_malloc n b (S size) x y.
  Proof.
    destruct x, y. induction n; intros.
    - destruct H as (Hlen & Hptr).
      split; [| split]; simpl; auto.
      + apply Hptr; auto.
      + intros. apply Hptr; lia.
    - split; auto. cbn in *. apply H. auto.
  Qed.

  Lemma sep_step_malloc n b size : sep_step (malloc_perm b)
                                            (post_malloc_perm n b size).
  Proof.
    apply sep_step_rg.
    - apply guar_malloc_post_malloc.
    - apply rely_malloc_post_malloc.
  Qed.

  Lemma write_post_malloc_perm m n size b
        (Hsize : (m <= size)%nat)
        (Hm : m > n):
    write_perm (b, size - m) (VNum 0) ⊥ post_malloc_perm n b size.
  Proof.
    constructor; auto; intros.
    - revert H. revert x y. induction n; intros.
      + induction H; try solve [etransitivity; eauto].
        destruct H; [| induction H; try solve [etransitivity; eauto]; destruct H].
        * eapply write_write_sep; eauto. intro. inversion H0. lia.
        * eapply write_block; eauto.
        * eapply malloc_write; eauto. rewrite Nat.add_1_r in H. auto.
      + induction H; try solve [etransitivity; eauto].
        destruct H. 2: apply IHn; auto; lia.
        eapply write_write_sep; eauto. intro. inversion H0. lia.
    - revert H. revert x y. induction n; intros.
      + destruct x, y. split; [| split; [| split; [| split]]]; simpl in *; try apply H.
        * intro. inversion H0. lia.
        * destruct ptr0. intro. cbn in *. inversion H1. lia.
      + destruct x, y. cbn in H. split; [| split]; cbn; try apply H.
        * intro. inversion H0. lia.
        * intro. inversion H0. lia.
        * apply IHn. lia. auto.
  Qed.

  Lemma post_malloc_perm_extend b size n (Hn : (S n <= size)%nat) :
    post_malloc_perm (S n) b size <=
      write_perm (b, size - S n) (VNum 0) ** post_malloc_perm n b size.
  Proof.
    constructor; auto.
    cbn in *; auto. intros [] H. destruct H as (Hlen & Hsizeof & Hread).
    split; [| split; [split; [| split] |]]; auto; try solve [intros; apply Hread; lia].
    apply write_post_malloc_perm; auto.
  Qed.

  Lemma post_malloc_perm_ok {A} n b size (xs : Vector.t A (S n))
        (Hn : (n <= size)%nat) :
    post_malloc_perm n b size (* the perm applies S to n and size inside *) ∈
                     VPtr (b, size - n) :: arr_perm W 0 (S n) trueP ▷ xs *
      singleton_Perms (block_perm (S size) (b, 0)) *
      malloc_Perms.
  Proof.
    cbn. induction n.
    - cbn. do 2 eexists. split; [| split; [| split]].
      + do 2 eexists. split; [| split; [| split]]; try reflexivity.
        * eexists. exists top_perm. split; [| split; [| split]]; auto. 3: reflexivity.
          2: apply separate_top.
          eexists. split; [exists (VNum 0); reflexivity |].
          eexists. exists top_perm. split; [| split; [| split]]; cbn; try reflexivity.
          apply separate_top.
        * do 2 rewrite sep_conj_perm_top. symmetry. apply write_block.
      + eexists. split; [exists (b + 1); reflexivity | cbn; reflexivity].
      + do 2 rewrite sep_conj_perm_top. symmetry. apply separate_sep_conj_perm.
        * apply malloc_write; cbn; lia.
        * apply malloc_block; cbn; lia.
        * apply write_block; cbn; lia.
      + repeat rewrite sep_conj_perm_top. constructor; auto.
        { intros [] (? & ? & ?). cbn in *.
          rewrite Nat.sub_0_r in *. rewrite Nat.add_0_r in *.
          split; split; auto.
          - split; auto. symmetry. apply write_block.
          - symmetry. apply separate_sep_conj_perm.
            + apply malloc_write. cbn; lia.
            + apply malloc_block; cbn; lia.
            + apply write_block.
        }
        { intros [] [] (? & ? & ?). cbn in *.
          rewrite Nat.sub_0_r in *. rewrite Nat.add_0_r in *. auto. }
        { intros [] [] H. rewrite sep_conj_perm_assoc in H.
          rewrite Nat.sub_0_r in *. rewrite Nat.add_0_r in *.
          unfold post_malloc_perm. unfold guar. unfold guar_post_malloc.
          unfold "**". unfold guar. unfold guar in H. unfold "**" in H. unfold guar in H.
          replace (S size - 1) with size. 2: lia. apply H. (* TODO simplify this *)
        }
    - cbn. assert (Hn': (n <= size)%nat) by lia.
      specialize (IHn (Vector.tl xs) Hn').
      rewrite Nat.add_0_r in *.
      destruct IHn as (? & ? & ? & ? & Hsep & Hlte).
      destruct H as (? & ? & ? & ? & Hsep' & Hlte').
      destruct H as (? & ? & ? & ? & Hsep'' & Hlte'').
      (* destruct H0 as (? & (? & ?) & ?). subst. *)
      (* destruct H1 as (? & (? & ?) & ?). subst. *)
      exists (write_perm (b, size - S n) (VNum 0) ** x).
      eexists. split; [| split; [| split]]; eauto.
      2: {
        symmetry. apply separate_sep_conj_perm.
        2: symmetry; auto.
        - symmetry. eapply separate_upwards_closed. apply write_post_malloc_perm; auto.
          etransitivity; eauto. apply lte_r_sep_conj_perm.
        - symmetry. eapply separate_upwards_closed. apply write_post_malloc_perm; auto.
          etransitivity; eauto. apply lte_l_sep_conj_perm.
      }
      {
        exists (write_perm (b, size - S n) (VNum 0) ** x1). eexists.
        split; [| split; [| split]]. 2: apply H1.
        3: { rewrite sep_conj_perm_assoc. apply sep_conj_perm_monotone; auto. reflexivity. }
        2: {
          symmetry. apply separate_sep_conj_perm.
          2: symmetry; auto.
          - symmetry. eapply separate_upwards_closed. apply write_post_malloc_perm; auto.
            etransitivity; eauto. etransitivity. apply lte_l_sep_conj_perm.
            etransitivity; eauto. apply lte_r_sep_conj_perm.
          - symmetry. eapply separate_upwards_closed. apply write_post_malloc_perm; auto.
            etransitivity; eauto. etransitivity. apply lte_l_sep_conj_perm.
            etransitivity; eauto. apply lte_l_sep_conj_perm.
        }
        do 2 eexists. split; [| split; [| split]].
        - eexists. split. exists (VNum 0). reflexivity.
          eexists. exists top_perm. split; [| split; [| split]]; cbn; try reflexivity.
          apply separate_top.
        - assert (Heq : size - S n + 1 = size - n) by lia. rewrite Heq. clear Heq.
          exists x3, x4. split; [| split]; eauto.
          rewrite arr_offset in *. cbn in *.
          assert (Heq : size - S n + 2 = size - n + 1) by lia. rewrite Heq. clear Heq. auto.
        - rewrite sep_conj_perm_top.
          eapply separate_upwards_closed. apply write_post_malloc_perm; auto.
          etransitivity; eauto. etransitivity. 2: apply lte_l_sep_conj_perm.
          etransitivity; eauto. apply lte_l_sep_conj_perm.
        - rewrite sep_conj_perm_top. reflexivity.
      }
      {
        etransitivity. apply post_malloc_perm_extend; auto.
        rewrite sep_conj_perm_assoc. apply sep_conj_perm_monotone; auto. reflexivity.
      }
  Qed.

  Lemma Malloc xi xs size :
    xi :: eqp (S size) ▷ xs * malloc_Perms ⊢
    malloc xi ⤳
    Ret (Vector.const tt (S size), tt) :::
    (arr (W, 0, S size, trueP)) ⋆ (blockPT (S size)) ∅ malloc_Perms.
  Proof.
    intros p si ss Hp Hpre. pstep. unfold malloc.
    destruct Hp as (peq & pmalloc & Heq & Hpmalloc & Hsep & Hlte). cbn in Heq. subst.
    destruct Hpmalloc as (? & (b & ?) & Hpmalloc); subst.
    (* read step *)
    rewritebisim @bind_trigger. econstructor; eauto; try reflexivity.
    (* write step *)
    rewritebisim @bind_trigger. unfold id. econstructor; eauto.
    { apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
      apply Hpmalloc in Hpre. apply Hlte. constructor 1. right. apply Hpmalloc.
      cbn in *. split.
      - eexists. reflexivity.
      - intros ptr Hb. split; rewrite lGetPut.
        + unfold read, allocated. subst. rewrite nth_error_app_early; auto.
        + unfold sizeof. subst. rewrite nth_error_app_early; auto.
    }
    (* return *)
    { eapply sep_step_lte.
      2: apply sep_step_malloc with (size := size).
      etransitivity. apply Hlte.
      etransitivity. apply lte_r_sep_conj_perm. apply Hpmalloc.
    }
    { apply Hlte in Hpre. destruct Hpre as (_ & Hpre & Hlte').
      apply Hpmalloc in Hpre. cbn in Hpre.
      constructor.
      - cbn. repeat rewrite lGetPut. split; [| split].
        + rewrite last_length. lia.
        + unfold sizeof. cbn.
          rewrite nth_error_app_last; auto.
        + intros. unfold read, allocated. cbn. rewrite nth_error_app_last; auto.
          rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H. cbn in *. rewrite H. auto.
      - unfold "∅", "⋆", ptApp.
        setoid_rewrite Hpre.
        replace 0 with (size - size) at 2. 2: lia.
        apply post_malloc_perm_ok; auto.
    }
  Qed.

  (** * Free *)

  (* helper lemma for Free *)
  Lemma combined_arr_guar {A} p parr b len n bytes (v : Vector.t A n) (si : Si) (ss : Ss)
        (Hb : b < length (lget si))
        (Hn: (n <= (S len))%nat)
        (Hlte : p <= parr)
        (Hblock: nth_error (lget si) b = Some (Some (LBlock (S len) bytes)))
        (Hparr: parr ∈ VPtr (b, 0) :: arr (W, (S len) - n, n, trueP) ▷ v) :
    let si' := lput si (replace_n (lget si) b (S len) bytes n) in
    (forall ptr', b <> fst ptr' -> read (lget si) ptr' = read (lget si') ptr') ->
    (forall ptr', sizeof (lget si) ptr' = sizeof (lget si') ptr') ->
    length (lget si) = length (lget si') ->
    guar p (si, ss) (si', ss).
  Proof.
    revert Hlte Hparr Hblock Hb Hn. revert b parr v. revert n.
    induction n; intros.
    - apply Hlte. subst si'. cbn in *.
      rewrite replace_n_0; auto. rewrite lPutGet. reflexivity.
    - destruct Hparr as (pptr & parr' & Hpptr & Hparr' & Hsep & Hlte').
      etransitivity.
      {
        eapply IHn; try lia; try rewrite lGetPut.
        2: { cbn in Hparr'. rewrite Nat.sub_succ_l. eauto. lia. }
        all: auto.
        - etransitivity; eauto. etransitivity; eauto. apply lte_r_sep_conj_perm.
        - cbn. intros. pose proof @read_replace_n_neq; eauto.
        - cbn. intros. pose proof sizeof_replace_n; eauto.
        - apply replace_list_index_length; auto.
      }
      {
        subst si'. cbn. apply Hlte. apply Hlte'. constructor 1. left.
        destruct Hpptr as (val & (? & ?) & Hpptr); subst.
        destruct Hpptr as (pwrite & p' & Hpwrite & _ & Hsep' & Hlte'').
        apply Hlte''. constructor 1. left.
        apply Hpwrite. cbn.
        repeat rewrite lGetPut in *.
        split; [| split; [| split]]; auto.
        - eexists. rewrite lPutPut. reflexivity.
        - intros. destruct (Nat.eq_dec b (fst ptr')).
          2: { pose proof read_replace_n_neq. cbn in H3. repeat rewrite <- H3; auto. }
          subst. destruct ptr' as [b o]. simpl in *.
          assert (Hneq: len - n <> o).
          { apply addr_neq_cases in H2. destruct H2; auto. }
          unfold replace_n, read, allocated. simpl.
          repeat rewrite nth_error_replace_list_index_eq; auto.
          destruct (o <? S len) eqn:?; auto.
          rewrite Bool.andb_true_l. simpl.
          destruct (S len - n <=? o) eqn:?.
          + pose proof Heqb1.
            assert (Himpl: (S len - n <= o -> len - n <= o)%nat) by lia.
            rewrite <- (Bool.reflect_iff _ _ (Nat.leb_spec0 _ _)) in H3. apply Himpl in H3.
            rewrite (Bool.reflect_iff _ _ (Nat.leb_spec0 _ _)) in H3.
            rewrite H3. simpl in Heqb1. rewrite Heqb1. auto.
          + pose proof Heqb1.
            simpl in Heqb1. rewrite Heqb1.
            apply Nat.leb_gt in H3.
            assert (len - n > o) by lia.
            apply Compare_dec.leb_correct_conv in H4. rewrite H4. auto.
        - intros. pose proof sizeof_replace_n. simpl in H2. rewrite <- H2; auto.
        - unfold replace_n. erewrite <- replace_list_index_length; eauto.
      }
  Qed.

  Lemma Free {A} xi len (xs : Vector.t A (S len) * unit) :
    xi :: (arr (W, 0, (S len), trueP)) ⋆ (blockPT (S len)) ▷ xs ⊢
       free xi ⤳
       Ret tt :::
       trueP.
  Proof.
    intros p si ss (parr & pblock & Hparr & Hpblock & Hsep & Hlte) Hpre.
    pstep. unfold free. destruct xi as [| ptr]; try contradiction.
    assert (Hoffset: snd ptr = 0).
    { apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
      apply Hpblock in Hpre. simpl in Hpre. unfold sizeof in Hpre.
      rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)).
      destruct (snd ptr =? 0); inversion Hpre; auto.
    }
    rewrite Hoffset. simpl.
    (* read step *)
    rewritebisim @bind_trigger. econstructor; auto; try reflexivity.
    pose proof Hpre as Hpre'. apply Hlte in Hpre'.
    destruct Hpre' as (Hprewrite & Hpreblock & Hsep').
    apply Hpblock in Hpreblock. simpl in Hpreblock.
    unfold sizeof in Hpreblock. rewrite Hoffset in Hpreblock. simpl in Hpreblock.
    unfold memory in *.
    destruct (nth_error (lget si) (fst ptr)) eqn:?; try solve [inversion Hpreblock].
    destruct o; try solve [inversion Hpreblock].
    destruct l. inversion Hpreblock; clear Hpreblock; subst.
    (* write step *)
    rewritebisim @bind_trigger. unfold id. econstructor; auto.
    - apply Hlte. constructor 1. left.
      assert (Hb: fst ptr < length (lget si)).
      { apply nth_error_Some. intro. rewrite H in Heqo. inversion Heqo. }
      erewrite replace_n_same.
      eapply combined_arr_guar; eauto; try reflexivity; try rewrite lGetPut.
      + destruct ptr. simpl in Hoffset. subst. rewrite Nat.sub_diag. apply Hparr.
      + intros. erewrite read_replace_n_neq; eauto.
      + intros. erewrite sizeof_replace_n; eauto.
      + apply replace_list_index_length; auto.
    - apply sep_step_lte'. apply top_perm_is_top.
    - constructor; cbn; auto.
  Qed.

  (** * Reachability rules *)
  Lemma ReflR {A} x rw o (T : @VPermType Si Ss A) :
    x :: trueP ▷ tt ⊑ x :: reach_perm x rw o T ▷ nil.
  Proof.
    repeat intro. apply mu_fixed_point. reflexivity.
  Qed.

  Lemma TransR {A} x y z rw o (T : @VPermType Si Ss A) xs ys :
    x :: reach_perm y rw o T ▷ xs * y :: reach_perm z rw o T ▷ ys ⊑
                                     x :: reach_perm z rw o T ▷ (xs ++ ys).
  Proof.
    revert x.
    induction xs.
    - intros x p (p1 & p2 & Hp1 & Hp2 & Hsep & Hlte).
      destruct Hp1 as (? & (U & HU & ?) & Hp1); subst.
      apply HU in Hp1. simpl in Hp1. subst. eapply Perms_downwards_closed; eauto.
      etransitivity; eauto. apply lte_r_sep_conj_perm.
    - intros x p (px' & py & Hpx' & Hpy & Hsep & Hlte).
      eapply mu_fixed_point in Hpx'.
      destruct Hpx' as (pa & px & Hpa & Hpx & Hsep' & Hlte').
      (* x must be a pointer *)
      destruct x; try contradiction. destruct a0 as [b o'].
      destruct Hpx as (? & (v & ?) & Hpx); subst.
      destruct Hpx as (px'' & pv & Hpx'' & Hpv & Hsep'' & Hlte'').

      apply mu_fixed_point.
      simpl.
      exists pa. exists (px'' ** (pv ** py)). split; [apply Hpa | split; [| split]].
      2: {
        apply separate_sep_conj_perm.
        - eapply separate_upwards_closed; eauto.
          etransitivity; eauto. apply lte_l_sep_conj_perm.
        - apply separate_sep_conj_perm.
          + eapply separate_upwards_closed; eauto.
            etransitivity; eauto. apply lte_r_sep_conj_perm.
          + symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
            etransitivity; eauto. apply lte_l_sep_conj_perm.
          + symmetry in Hsep. eapply separate_upwards_closed; eauto.
            etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
            apply sep_conj_perm_monotone. reflexivity.
            etransitivity; eauto. apply lte_r_sep_conj_perm.
        - symmetry. apply separate_sep_conj_perm.
          + eapply separate_upwards_closed; eauto. reflexivity.
          + symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
            etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
            apply sep_conj_perm_monotone. reflexivity.
            etransitivity; eauto. apply lte_l_sep_conj_perm.
          + symmetry in Hsep. eapply separate_upwards_closed; eauto.
            etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
            apply sep_conj_perm_monotone. reflexivity.
            etransitivity; eauto. apply lte_r_sep_conj_perm.
      }
      2: { repeat rewrite <- sep_conj_perm_assoc.
           etransitivity; eauto.
           eapply sep_conj_perm_monotone; intuition.
           repeat rewrite sep_conj_perm_assoc.
           etransitivity; eauto.
           eapply sep_conj_perm_monotone; intuition.
      }
      eexists. split; [eexists; reflexivity |].
      apply sep_conj_Perms_perm; [apply Hpx'' | |].
      2: {
        apply separate_sep_conj_perm; auto.
        + symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
          etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
          apply sep_conj_perm_monotone. reflexivity.
          etransitivity; eauto. apply lte_l_sep_conj_perm.
        + symmetry in Hsep. eapply separate_upwards_closed; eauto.
          etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
          apply sep_conj_perm_monotone. reflexivity.
          etransitivity; eauto. apply lte_r_sep_conj_perm.
      }
      cbn. exists (v :: reach_perm z rw o T ▷ (xs ++ ys)). split.
      2: {
        apply IHxs. apply sep_conj_Perms_perm; auto.
        symmetry. symmetry in Hsep. eapply separate_upwards_closed; eauto.
        etransitivity; eauto. etransitivity. 2: apply lte_r_sep_conj_perm.
        apply sep_conj_perm_monotone. reflexivity.
        etransitivity; eauto. apply lte_r_sep_conj_perm.
      }
      eexists; split; eauto.
      repeat intro. eapply mu_fixed_point in H; auto.
      Unshelve. all: apply reach_perm_proper.
  Qed.

  Section example.
    Definition Rs := {_ : nat & unit}.

    Inductive nelist (A : Type) :=
    | nenil : A -> nelist A
    | necons : A -> nelist A -> nelist A
    .
    Definition mu_nelist A := fun R => sum (A * unit) (A * R).


    Global Program Instance fixed_point_list A : FixedPoint (mu_nelist A) (nelist A)
      :=
      {
        foldFP := fun s => match s with
                        | inl (h, _) => nenil A h
                        | inr (h, t) => (necons A h t)
                        end;
        unfoldFP := fun l => match l with
                          | nenil _ h => inl (h, tt)
                          | necons _ h t => inr _ (h, t)
                          end;
      }.
    Next Obligation.
      destruct gx; auto.
      - destruct p. destruct u. reflexivity.
      - destruct p. reflexivity.
    Defined.
    Next Obligation.
      destruct x; auto.
    Defined.


  Program Definition circular_list_perm rw A (T : VPermType A) (p : Value) : VPermType (nelist A) :=
    @mu _ _ _ (mu_nelist A) _ (fixed_point_list _) (fun U => or (ptr (rw, 0, T) ⋆ ptr (rw, 1, (eqp p))) (ptr (rw, 0, T) ⋆ ptr (rw, 1, U))) _.
  Next Obligation.
    repeat intro. cbn. induction b; cbn in *; auto.
    destruct H0 as (? & ? & ? & ? & ? & ?). exists x0, x1. split; [| split]; auto.
    clear H0. unfold ptr_Perms in *. destruct (offset a 1); auto.
    destruct H1. destruct H0 as ((? & ?) & ?). subst. destruct H1 as (? & ? & ? & ? & ?).
    eexists. split; eauto. do 2 eexists. split; eauto. split; eauto. apply H. auto.
  Qed.

  Lemma MuDup A G X `{FixedPoint G X} (F : @PermType Si Ss A X -> @PermType Si Ss A (G X))
    {prp : Proper (lte_PermType ==> lte_PermType) F}
    (Hdup : forall T x y,
        x :: (F T) ▷ y ⊑ x :: (F T) ▷ y * x :: (F T) ▷ y)
    xi xs :
    xi :: mu F ▷ xs ⊑ xi :: mu F ▷ xs * xi :: mu F ▷ xs.
  Proof.
    etransitivity. apply MuUnfold.
    etransitivity. apply Hdup.
    apply sep_conj_Perms_monotone; rewrite <- (unfoldFold xs) at 2; apply MuFold.
  Qed.



  Lemma dup xi xs isNat :
    xi :: list_perm R {n : nat & unit} isNat ▷ xs ⊑
      xi :: list_perm R _ isNat ▷ xs * xi :: list_perm R _ isNat ▷ xs.
  Proof.
    repeat intro.
    exists p, p. split; [| split]; auto.
    cbn in *.
    unfold lte_PermType in H.
    destruct H as (? & ((? & ?) & ?)). destruct H. subst.
    specialize (H xi xs).
    cbn in H.
    destruct xs; cbn in *.
    -
  Abort.

  Lemma dup xi xs isNat v :
    xi :: circular_list_perm R Rs isNat v ▷ xs ⊑
      xi :: circular_list_perm R _ isNat v ▷ xs * xi :: circular_list_perm R _ isNat v ▷ xs.
  Proof.
    repeat intro.
    exists p, p. split; [| split]; auto.

    cbn in H.
    destruct H as (? & ((? & ?) & ?)).
    destruct H. subst.

    (* apply MuDup. *)
    (* intros. *)
    (* cbn. *)
  Admitted.

  Definition nth_i (n : nat) (p : Value) : itree (sceE Si) Value :=
    iter (fun '(v, p) =>
            i <- getNum v;;
            (if (i =? n)
             then v <- load p;;
                  Ret (inr v)
             else p' <- load (offset p 1);;
                  Ret (inl (VNum (i + 1), p'))))
      (VNum 0, p).

  Definition nth_s (n : nat) (l : nelist Rs) : itree (sceE Ss) Rs :=
    ITree.iter (fun '(i, l') =>
            match i with
            | existT _ i _ =>
                Ret tt;;
                if (i =? n)
                then (* return the front element *)
                  sum_rect (fun _ => itree (sceE Ss) (Rs * nelist Rs + Rs))
                    (fun '(h, _) => Ret tt;; Ret (inr h))
                    (fun '(h, t) => Ret tt;; Ret (inr h))
                    (unfoldFP l')
                else  (* continue recursing *)
                  sum_rect (fun _ => itree (sceE Ss) (Rs * nelist Rs + Rs))
                    (fun '(h, _) => Ret tt;; Ret (inl (existT _ (i + 1) tt, l)))
                    (fun '(h, t) => Ret tt;; Ret (inl (existT _ (i + 1) tt, t)))
                    (unfoldFP l')
            end)
      (existT _ 0 tt, l).

  Lemma nth_typing xi xs n :
    xi :: circular_list_perm R Rs isNat xi ▷ xs ⊢
      nth_i n xi ⤳
      nth_s n xs :::
      isNat.
  Proof.
    unfold nth_i, nth_s.

    (* create the isNat permission so we can use Iter *)
    eapply Weak; [apply EqRefl with (xi := VNum 0) | reflexivity |].
    rewrite sep_conj_Perms_commut.
    eapply Weak with (P2 := VNum 0 :: isNat ▷ (existT _ 0 tt) *
                              xi :: circular_list_perm R Rs isNat xi ▷ xs); [| reflexivity |].
    apply sep_conj_Perms_monotone; [| reflexivity].
    (* not sure why i can't just apply ExI, but this works *)
    etransitivity. 2: eapply ExI. reflexivity.

    (* Duplicate the permission on xi and xs for later *)
    eapply Weak; [| reflexivity |].
    apply sep_conj_Perms_monotone; [reflexivity |].
    etransitivity. apply dup. apply PermsI.

    (* Pair the two permissions together for Iter *)
    eapply Weak; [apply ProdI | reflexivity |].

    (* Apply Iter, start looking at the loop bodies *)
    apply PermTypeProofs.Iter.
    intros [ii p] [[i []] l].
    (* ii and i both represent the nat i *)
    (* p and l both represent the list *)
    eapply Weak; [apply ProdE | reflexivity |]. unfold fst, snd.
    eapply Weak; [| reflexivity |].
    apply sep_conj_Perms_monotone; [apply ExE | reflexivity].

    eapply Bind.
    {
      apply Frame.
      apply GetNum.
    }

    (* we finished using ii in getNum, so we can replace it with the new nat value i' now. we have the equality permission i = i' *)
    clear ii. intros i' []. unfold projT1.
    eapply Weak; [apply PermsE | reflexivity |].
    rewrite sep_conj_Perms_commut.

    (* make a copy of the eqp relating i and i' *)
    eapply Weak; [ | reflexivity |].
    apply sep_conj_Perms_monotone; [reflexivity |].
    apply EqDup.
    rewrite sep_conj_Perms_assoc.

    (* Relate the values in the if condition *)
    eapply Weak; [| reflexivity |].
    apply sep_conj_Perms_monotone; [reflexivity |].
    apply EqCtx with (f := fun i => i =? n).

    apply If.
    {
      (* we are done with recursion. return the front of the list *)

      (* drop the permission for i and i' *)
      eapply Weak; [| reflexivity |].
      apply lte_l_sep_conj_Perms.
      clear i i' n.

      (* drop the permission for xi and xs *)
      eapply Weak; [| reflexivity |].
      etransitivity. apply PermsE.
      apply lte_l_sep_conj_Perms.

      eapply Weak; [apply MuUnfold | reflexivity |].
      eapply Weak; [apply TrueI with (xi := tt) | reflexivity |].
      rewrite sep_conj_Perms_commut.
      apply OrE.
      {
        (* we are at the base case of the ne list *)
        intros [[i []] []].
        eapply Weak; [apply lte_r_sep_conj_Perms | reflexivity |].
        eapply Weak; [apply StarE | reflexivity |]. unfold fst.
        rewrite sep_conj_Perms_commut.
        apply PtrE.
        intros v.
        rewrite <- sep_conj_Perms_assoc.
        eapply Weak; [apply lte_r_sep_conj_Perms | reflexivity |].
        eapply Bind.
        {
          apply Frame.
          apply Load.
        }
        {
          intros xi' [].
          eapply Weak; [apply PermsE | reflexivity |].
          eapply Weak; [| reflexivity |].
          {
            apply sep_conj_Perms_monotone; [| reflexivity].
            etransitivity.
            apply PermsE.
            apply lte_l_sep_conj_Perms.
          }
          eapply Weak; [apply Cast | reflexivity |]. clear v.
          eapply Weak; [apply SumI2 | reflexivity |].
          apply Ret_.
        }
      }
      {
        (* not the base case of ne list. Same as the prev case *)
        intros [[i []] l'].
        eapply Weak; [apply lte_r_sep_conj_Perms | reflexivity |].
        eapply Weak; [apply StarE | reflexivity |]. unfold fst.
        rewrite sep_conj_Perms_commut.
        apply PtrE.
        intros v.
        rewrite <- sep_conj_Perms_assoc.
        eapply Weak; [apply lte_r_sep_conj_Perms | reflexivity |].
        eapply Bind.
        {
          apply Frame.
          apply Load.
        }
        {
          intros xi' [].
          eapply Weak; [apply PermsE | reflexivity |].
          eapply Weak; [| reflexivity |].
          {
            apply sep_conj_Perms_monotone; [| reflexivity].
            etransitivity.
            apply PermsE.
            apply lte_l_sep_conj_Perms.
          }
          eapply Weak; [apply Cast | reflexivity |]. clear v.
          eapply Weak; [apply SumI2 | reflexivity |].
          apply Ret_.
        }
      }
    }
    {
      (* keep recursing. *)
      clear n.

      (* unfold the recursive type *)
      eapply Weak; [| reflexivity |].
      apply sep_conj_Perms_monotone; [| reflexivity].
      etransitivity. apply PermsE.
      apply sep_conj_Perms_monotone; [| reflexivity].
      apply MuUnfold.
      rewrite <- sep_conj_Perms_assoc.
      rewrite sep_conj_Perms_commut.

      apply OrE.
      {
        (* we are at the base case of the ne list *)
        intros [[is' []] []].

        rewrite sep_conj_Perms_commut.
        eapply Weak; [| reflexivity |].
        apply sep_conj_Perms_monotone; [| reflexivity].
        apply StarE.

        rewrite <- sep_conj_Perms_assoc.
        eapply Weak; [apply lte_r_sep_conj_Perms | reflexivity |].
        eapply Bind.
        {
          apply Frame.
          eapply Weak; [apply PtrOff with (o2:=1) | reflexivity |]. lia.
          apply Load.
        }
        {
          (* Drop the perm on p + 1 *)
          intros xi' [].
          eapply Weak; [apply PermsE | reflexivity |].
          eapply Weak; [| reflexivity |].
          apply sep_conj_Perms_monotone; [apply PermsE | reflexivity].
          eapply Weak; [| reflexivity |].
          rewrite <- sep_conj_Perms_assoc.
          apply sep_conj_Perms_monotone; [reflexivity |].
          apply lte_r_sep_conj_Perms.

          (* duplicate the perm relating xi and xs again *)
          eapply Weak; [| reflexivity |].
          apply sep_conj_Perms_monotone; [reflexivity |].
          apply sep_conj_Perms_monotone; [| reflexivity].
          apply dup.

          (* get a permission on xi' *)
          do 2 rewrite sep_conj_Perms_assoc.
          eapply Weak; [| reflexivity |].
          apply sep_conj_Perms_monotone; [| reflexivity].
          apply sep_conj_Perms_monotone; [| reflexivity].
          apply Cast.

          (* put the xi permission back together *)
          rewrite sep_conj_Perms_commut.
          eapply Weak; [| reflexivity |].
          apply sep_conj_Perms_monotone; [reflexivity |].
          apply PermsI.

          (* recreate isNat perm *)
          eapply Weak; [| reflexivity |].
          apply sep_conj_Perms_monotone with (P := (VNum (i' + 1)) :: isNat ▷ existT _ (i + 1) tt) ; [| reflexivity].
          etransitivity. 2: eapply ExI.
          apply EqCtx with (f := fun i => VNum (i + 1)).

          (* recreate prod perm *)
          eapply Weak; [| reflexivity |].
          apply ProdI.

          (* recreate sum perm *)
          eapply Weak; [| reflexivity |].
          apply SumI1.
          apply Ret_.
        }
      }
      {
        (* we are not at the base case of the ne list. *)
        intros [[is' []] l'].

        rewrite sep_conj_Perms_commut.
        eapply Weak; [| reflexivity |].
        apply sep_conj_Perms_monotone; [| reflexivity].
        apply StarE.

        (* drop the perm on p *)
        rewrite <- sep_conj_Perms_assoc.
        eapply Weak; [apply lte_r_sep_conj_Perms | reflexivity |].

        (* get the perm on the value p + 1 points to *)
        rewrite sep_conj_Perms_commut.
        apply PtrE. intros v.

        eapply Bind.
        {
          rewrite (sep_conj_Perms_commut _ (p :: ptr (R, 1, eqp v) ▷ tt)).
          rewrite <- sep_conj_Perms_assoc.
          apply Frame.
          eapply Weak; [apply PtrOff with (o2:=1) | reflexivity |]. lia.
          apply Load.
        }
        {
          (* Drop the perm on p + 1 *)
          intros xi' []. unfold snd.
          eapply Weak; [apply PermsE | reflexivity |].
          eapply Weak; [| reflexivity |].
          apply sep_conj_Perms_monotone; [apply PermsE | reflexivity].
          eapply Weak; [| reflexivity |].
          rewrite <- sep_conj_Perms_assoc.
          apply sep_conj_Perms_monotone; [reflexivity |].
          apply lte_r_sep_conj_Perms.

          (* get a permission on xi' *)
          eapply Weak; [| reflexivity |].
          apply sep_conj_Perms_monotone; [reflexivity |].
          rewrite sep_conj_Perms_commut.
          reflexivity.
          do 2 rewrite sep_conj_Perms_assoc.
          eapply Weak; [| reflexivity |].
          apply sep_conj_Perms_monotone; [| reflexivity].
          apply sep_conj_Perms_monotone; [| reflexivity].
          apply Cast.

          (* put the xi permission back together *)
          rewrite sep_conj_Perms_commut.
          eapply Weak; [| reflexivity |].
          apply sep_conj_Perms_monotone; [reflexivity |].
          apply PermsI.

          (* recreate isNat perm *)
          eapply Weak; [| reflexivity |].
          apply sep_conj_Perms_monotone with (P := (VNum (i' + 1)) :: isNat ▷ existT _ (i + 1) tt) ; [| reflexivity].
          etransitivity. 2: eapply ExI.
          apply EqCtx with (f := fun i => VNum (i + 1)).

          (* recreate prod perm *)
          eapply Weak; [| reflexivity |].
          apply ProdI.

          (* recreate sum perm *)
          eapply Weak; [| reflexivity |].
          apply SumI1.
          apply Ret_.
        }
      }
    }
  Qed.

  (*
  n = 0;
  while (v != NULL) {
        v = *(v + 1);
        n++;
  }
   *)
  Definition length_i (p : Value) : itree (sceE Si) Value :=
    iter (fun '(v, p) => n <- getNum v;;
                      b <- isNull p;;
                      if (b : bool)
                      then Ret (inr (VNum n)) (* v == NULL *)
                      else p' <- load (offset p 1);; (* continue with *(p + 1) *)
                           Ret (inl (VNum (n + 1), p')))
      (VNum 0, p).

  Definition length_s {A} (l : list A) : itree (sceE Ss) Rs :=
    ITree.iter (fun '(i, l) =>
            sum_rect (fun _ => itree (sceE Ss) (((sigT (fun _ : nat => unit)) * list A) +
                                               (sigT (fun _ : nat => unit))))
              (fun _ : unit => Ret (inr i))
              (fun '(h, t) => Ret (inl (existT _ (projT1 i + 1) tt, t)))
              (unfoldFP l))
      (existT _ 0 tt, l).

  (* used since [if true] immediately reduces *)
  Definition tb := true.
  Definition fb := false.


  Lemma length_typing A xi xs (T : VPermType A) :
    xi :: list_perm R _ T ▷ xs ⊢
      length_i xi ⤳
      length_s xs :::
      isNat.
  Proof.
    unfold length_i, length_s.

    (* Make the isNat permission for the starting values *)
    eapply Weak with (P2 := VNum 0 :: isNat ▷ existT _ 0 tt * xi :: list_perm R A T ▷ xs);
      [| reflexivity |].
    {
      etransitivity. apply EqRefl with (xi := VNum 0).
      rewrite sep_conj_Perms_commut.
      eapply sep_conj_Perms_monotone; [| reflexivity].
      etransitivity.
      2: apply ExI. reflexivity.
    }

    (* Put the two permissions together with a product type *)
    eapply Weak; [| reflexivity |].
    apply ProdI.

    (* Step into iter bodies *)
    eapply PermTypeProofs.Iter. clear xi xs.
    intros [ni xi] [[ns []] xs].
    (* Take product apart *)
    eapply Weak; [| reflexivity |].
    apply ProdE. unfold fst, snd.

    (* Get ready to handle getNum *)
    (* first add a ret tt to spec side *)
    replace (sum_rect
               (fun _ : unit + A * list A =>
                  itree (sceE Ss) ({_ : nat & unit} * list A + {_ : nat & unit}))
               (fun _ : unit => Ret (inr (existT _ ns tt)))
               (fun '(_, t) => Ret (inl (existT (fun _ : nat => unit) (ns + 1) tt, t)))
               (unfoldFP xs))
      with
      (Ret tt;; sum_rect
                  (fun _ : unit + A * list A =>
                     itree (sceE Ss) ({_ : nat & unit} * list A + {_ : nat & unit}))
                  (fun _ : unit => Ret (inr (existT _ ns tt)))
                  (fun '(_, t) => Ret (inl (existT (fun _ : nat => unit) (ns + 1) tt, t)))
                  (unfoldFP xs)).
    2: {
      apply bisimulation_is_eq. apply bind_ret_l with (r := tt).
    }

    eapply Bind.
    {
      (* GetNum step *)
      apply Frame.
      eapply Weak; [| reflexivity |].
      apply ExE.
      apply GetNum.
    }
    intros n []. unfold projT1.
    eapply Weak; [apply PermsE | reflexivity |].

    (* Unfold recursive type *)
    eapply Weak; [| reflexivity |].
    eapply sep_conj_Perms_monotone; [reflexivity | apply MuUnfold].
    unfold fst, snd.
    eapply OrE.
    - (* null case *)
      intros [].
      (* Get ready to handle isNull *)
      assert ((Ret (inr (existT (fun _ : nat => unit) ns tt)) : itree (sceE Ss) ((Rs * list A) + Rs)) = (Ret tt;; Ret (inr (existT (fun _ : nat => unit) ns tt)) : itree (sceE Ss) ((Rs * list A) + Rs))).
      apply bisimulation_is_eq. rewrite bind_ret_l with (r := tt). reflexivity.
      unfold Rs in H.
      rewrite H. clear H.
      eapply Bind.
      {
        (* isNull *)
        rewrite sep_conj_Perms_commut.
        apply Frame.
        apply IsNull2.
      }

      intros b [].
      (* Get ready to use If *)
      assert ((Ret (inr (existT (fun _ : nat => unit) ns tt)) : itree (sceE Ss) ((Rs * list A) + Rs)) = if tb then Ret (inr (existT (fun _ : nat => unit) ns tt)) else Exception.throw tt).
      reflexivity.
      unfold Rs in H. rewrite H. clear H.
      eapply Weak; [apply PermsE | reflexivity |].
      rewrite sep_conj_Perms_commut.
      apply If.
      2: { apply Err. }
      (* reform isNat and sum type *)
      eapply Weak; [| reflexivity | apply Ret_].
      etransitivity.
      2: apply SumI2.
      etransitivity.
      2: apply ExI.
      apply EqCtx.
    - (* non null case, keep iterating *)
      intros [a xs'].
      rewrite sep_conj_Perms_commut.
      eapply Weak; [| reflexivity |].
      apply sep_conj_Perms_monotone; [apply StarE | reflexivity].

      (* Get ready to handle isNull *)
      assert ((Ret (inl (existT (fun _ : nat => unit) (ns + 1) tt, xs')) : itree (sceE Ss) ((Rs * list A) + Rs)) = (Ret tt;; Ret (inl (existT (fun _ : nat => unit) (ns + 1) tt, xs')) : itree (sceE Ss) ((Rs * list A) + Rs))).
      apply bisimulation_is_eq. rewrite bind_ret_l with (r := tt). reflexivity.
      unfold Rs in H.
      rewrite H. clear H.
      eapply Bind.
      {
        (* isNull *)
        rewrite <- sep_conj_Perms_assoc.
        apply Frame.
        apply IsNull1.
      }
      intros b [].
      (* get ready to use If *)
      assert ((Ret (inl (existT (fun _ : nat => unit) (ns + 1) tt, xs')) : itree (sceE Ss) ((Rs * list A) + Rs)) = if fb then Exception.throw tt else  Ret (inl (existT (fun _ : nat => unit) (ns + 1) tt, xs'))).
      reflexivity.
      unfold Rs in H. rewrite H. clear H.
      eapply Weak; [apply PermsE | reflexivity |].
      eapply Weak; [| reflexivity |].
      apply sep_conj_Perms_monotone; [apply PermsE | reflexivity].
      rewrite <- sep_conj_Perms_assoc.
      rewrite sep_conj_Perms_commut.
      apply If.
      { apply Err. }
      (* drop first ptr type *)
      eapply Weak; [| reflexivity |].
      apply lte_r_sep_conj_Perms.
      (* get ready to use bind *)
      assert ((Ret (inl (existT (fun _ : nat => unit) (ns + 1) tt, xs')) : itree (sceE Ss) ((Rs * list A) + Rs)) = Ret tt;; Ret (inl (existT (fun _ : nat => unit) (ns + 1) tt, xs'))).
      apply bisimulation_is_eq. rewrite bind_ret_l with (r := tt). reflexivity.
      unfold Rs in H. rewrite H. clear H.
      (* expose the value that the pointer points to *)
      rewrite sep_conj_Perms_commut.
      apply PtrE.
      intros v.
      rewrite <- sep_conj_Perms_assoc.
      rewrite sep_conj_Perms_commut.
      rewrite <- sep_conj_Perms_assoc.
      eapply Bind.
      {
        apply Frame.
        eapply Weak; [| reflexivity |].
        apply PtrOff with (o2 := 1). lia.
        (* load *)
        apply Load.
      }
      intros v' [].
      eapply Weak; [apply PermsE | reflexivity |].
      eapply Weak; [| reflexivity |].
      apply sep_conj_Perms_monotone; [apply PermsE | reflexivity].

      (* drop pointer perm we just used *)
      eapply Weak; [| reflexivity |].
      apply sep_conj_Perms_monotone; [| reflexivity].
      apply lte_l_sep_conj_Perms.
      rewrite sep_conj_Perms_assoc.

      (* get rid of old value name v *)
      eapply Weak; [| reflexivity |].
      apply sep_conj_Perms_monotone; [apply Cast | reflexivity].
      clear v. rename v' into v.

      (* reform isNat, list type, and sum type *)
      eapply Weak; [| reflexivity | apply Ret_].
      rewrite sep_conj_Perms_commut.
      etransitivity.
      2: eapply SumI2.
      etransitivity.
      2: eapply ProdI.
      apply sep_conj_Perms_monotone; [| reflexivity].
      etransitivity.
      2: apply ExI.
      apply EqCtx with (f := fun n => VNum (n + 1)).

      Unshelve. 3: apply T.
  Qed.
  End example.

End MemoryPerms.

Notation "'arr' ( rw , o , l , T )" := (arr_perm rw o l T).

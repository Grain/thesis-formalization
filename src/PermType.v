(* begin hide *)
From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.

From Heapster Require Import
     Utils
     Permissions
     Memory
     SepStep
     Typing.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Exception
     Eq.Eqit
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import MonadNotation.
(* end hide *)

Section permType.
  Context {Si Ss : Type}.

  (** * Permission types *)

  Record PermType (A B:Type) : Type :=
    { ptApp : A -> B -> @Perms(Si * Ss) }.
  Definition VPermType A := PermType Value A.
  Notation "xi :: T ▷ xs" := (ptApp _ _ T xi xs) (at level 35).

  Definition withPerms {Ai As} (T: PermType Ai As) (P:@Perms (Si * Ss)) : PermType Ai As:=
    {| ptApp:= fun ai abs => ai :: T ▷ abs * P|}.
  Notation "T ∅ P" := (withPerms T P) (at level 40).

  Definition plusPT {A1 A2 B1 B2}
             (T1:PermType A1 B1) (T2:PermType A2 B2) : PermType (A1+A2) (B1+B2) :=
    {| ptApp := fun eithA eithB =>
                  match (eithA,eithB) with
                  | (inl a1, inl b1) => a1 :: T1 ▷ b1
                  | (inr a2, inr b2) => a2 :: T2 ▷ b2
                  | _ => bottom_Perms
                  end |}.
  Notation "T1 ⊕ T2" := (plusPT T1 T2) (at level 50).

  Definition timesPT {A1 A2 B1 B2}
             (T1:PermType A1 B1) (T2:PermType A2 B2) : PermType (A1*A2) (B1*B2) :=
    {| ptApp := fun a12 b12 =>  fst a12 :: T1 ▷ fst b12 * snd a12 :: T2 ▷ snd b12 |}.
  Notation "T1 ⊗ T2" := (timesPT T1 T2) (at level 40).

  Definition starPT {Ai As Bs} (T1:PermType Ai As) (T2:PermType Ai Bs)
    : PermType Ai (As * Bs) :=
    {| ptApp := fun ai abs => ai :: T1 ▷ fst abs * ai :: T2 ▷ snd abs |}.
  Notation "T1 ⋆ T2" := (starPT T1 T2) (at level 40).

  Definition existsPT {Ai As} {Bs:As -> Type}
             (F : forall a, PermType Ai (Bs a)) : PermType Ai (sigT Bs) :=
    {| ptApp := fun ai abs => ai :: F (projT1 abs) ▷ (projT2 abs) |}.
  Notation "'ex' ( x 'oftype' A ) T" := (existsPT (As:=A) (fun x => T)) (at level 70).

  Definition or {Ai As Bs} (T1:PermType Ai As)
             (T2:PermType Ai Bs) : PermType Ai (As + Bs) :=
    {| ptApp := fun ai abs =>
                  sum_rect _ (ptApp _ _ T1 ai) (ptApp _ _ T2 ai) abs |}.

  Variant RW: Type := R | W.

  Definition trueP {A B} : PermType A B :=
    {| ptApp := fun _ _ => top_Perms |}.
  Definition falseP {A B} : PermType A B :=
    {| ptApp := fun _ _ => bottom_Perms |}.

  Program Definition eqp {A} (a:A): PermType A unit :=
    {| ptApp := fun a' _ => {| in_Perms _ := a=a' |} |}.

  (** * Operations used in typing rules *)

  Definition vsingle {A} (a:A) : Vector.t A 1 :=
    Vector.cons _ a _ (Vector.nil _).

  Definition ifz {A} n (x y:A) : A :=
    if Nat.eqb n 0 then x else y.

  Definition getNum {S} v : itree (sceE S) nat :=
    match v with VNum n => Ret n | VPtr _ => throw tt end.

  Definition isNull {S} v: itree (sceE S) bool :=
    match v with
    | VNum n => if Nat.eqb n 0 then Ret true else throw tt
    | VPtr _ => Ret false
    end.

  Definition isNat := ex (n oftype nat) (eqp (VNum n)).

  (** * Recursive and reachability permissions *)

  (** The ordering on permission types is just the lifting of that on Perms *)
  Definition lte_PermType {A B} (T1 T2:PermType A B): Prop :=
    forall a b, lte_Perms (ptApp _ _ T1 a b) (ptApp _ _ T2 a b).

  (** Equals on PermType is just the symmetric closure of the ordering *)
  Definition eq_PermType {A B} (T1 T2:PermType A B): Prop :=
    lte_PermType T1 T2 /\ lte_PermType T2 T1.

  Global Instance PreOrder_lte_PermType A B : PreOrder (@lte_PermType A B).
  Proof.
    constructor; intro; intros; intros a b.
    - reflexivity.
    - etransitivity; [ apply H | apply H0 ].
  Qed.

  Global Instance Equivalence_eq_PermType A B : Equivalence (@eq_PermType A B).
  Proof.
    constructor; intro; intros.
    - split; reflexivity.
    - destruct H; split; assumption.
    - destruct H; destruct H0; split; etransitivity; eassumption.
  Qed.

  Global Instance Proper_eq_PermType_ptApp A B :
    Proper (eq_PermType ==> eq ==> eq ==> eq_Perms) (ptApp A B).
  Proof.
    intros T1 T2 eT a1 a2 ea b1 b2 eb. rewrite ea; rewrite eb.
    destruct eT. split; [ apply H | apply H0 ].
  Qed.

  (** The join on permission types is just the lifting of that on Perms *)
  Definition join_PermType {A B} (Ts : PermType A B -> Prop) : PermType A B :=
    {| ptApp := fun a b => join_Perms (fun P => exists T, Ts T /\ P = (a :: T ▷ b)) |}.

  (** Join is an upper bound for PermType *)
  Lemma lte_join_PermType {A B} (Ts : PermType A B -> Prop) T:
    Ts T -> lte_PermType T (join_PermType Ts).
  Proof.
    intros ts_t a b. apply lte_join_Perms. exists T; split; eauto.
  Qed.

  (** Join is the least upper bound for PermType *)
  Lemma join_PermType_min {A B} (Ts : PermType A B -> Prop) T:
    (forall T', Ts T' -> lte_PermType T' T) ->
    lte_PermType (join_PermType Ts) T.
  Proof.
    intros lte_T_Ts a b. apply join_Perms_min. intros P [ T' [ Ts_T' P_eq ]].
    rewrite P_eq. apply (lte_T_Ts T' Ts_T' a b).
  Qed.

  (** The greatest fixed-point permission type is defined via the standard
  Knaster-Tarski construction as the join of all F-consistent permission types *)
  Definition fixPT {A B} (F : PermType A B -> PermType A B)
             {prp : Proper (lte_PermType ==> lte_PermType) F} : PermType A B :=
    join_PermType (fun T => lte_PermType T (F T)).

  (** First we prove that fixPT is itself F-consistent *)
  Lemma fixPT_F_consistent {A B} (F : PermType A B -> PermType A B)
    {prp : Proper (lte_PermType ==> lte_PermType) F} :
    lte_PermType (fixPT F) (F (fixPT F)).
  Proof.
    intros a b. apply join_PermType_min. intros T' lte_FT'.
    transitivity (F T'); [ assumption | ]. apply prp.
    apply lte_join_PermType. assumption.
  Qed.

  (** Then we prove that fixPT is a fixed-point *)
  Lemma fixPT_fixed_point {A B} (F : PermType A B -> PermType A B)
    {prp : Proper (lte_PermType ==> lte_PermType) F} :
    eq_PermType (fixPT F) (F (fixPT F)).
  Proof.
    split; [ apply fixPT_F_consistent | ].
    apply lte_join_PermType. apply prp. apply fixPT_F_consistent.
  Qed.

  Class FixedPoint (G : Type -> Type) X : Type :=
    { foldFP : G X -> X;
      unfoldFP : X -> G X;
      foldUnfold : forall gx, unfoldFP (foldFP gx) = gx;
      unfoldFold : forall x, foldFP (unfoldFP x) = x; }.

  Definition unmaprPT {A B C} (f : B -> C) (T : PermType A C) : PermType A B :=
    {| ptApp := fun a b => a :: T ▷ (f b) |}.

  Program Definition mu {A G X} `{FixedPoint G X}
             (F : PermType A X -> PermType A (G X))
             {prp : Proper (lte_PermType ==> lte_PermType) F}
    : PermType A X :=
    @fixPT A X (fun T => unmaprPT unfoldFP (F T)) _.
  Next Obligation.
    intros T1 T2 leqT a x. apply prp. assumption.
  Defined.

  Lemma mu_fixed_point {A G X} `{FixedPoint G X}
        (F : PermType A X -> PermType A (G X))
        {prp : Proper (lte_PermType ==> lte_PermType) F} :
    eq_PermType (mu F) (unmaprPT unfoldFP (F (mu F))).
  Proof.
    apply (fixPT_fixed_point (fun T : PermType A X => unmaprPT unfoldFP (F T))).
  Qed.

  Lemma mu_fixed_point' {A G X} `{FixedPoint G X}
        (F : PermType A X -> PermType A (G X))
        {prp : Proper (lte_PermType ==> lte_PermType) F} :
    lte_PermType (unmaprPT unfoldFP (F (mu F))) (mu F).
  Proof.
    apply (fixPT_fixed_point (fun T : PermType A X => unmaprPT unfoldFP (F T))).
  Qed.

  Definition mu_list A := fun R => sum unit (A * R).
  Global Program Instance fixed_point_list A : FixedPoint (mu_list A) (list A)
   :=
    {
    foldFP := fun s => match s with
                    | inl _ => @nil A
                    | inr (h, t) => (cons h t)
                    end;
    unfoldFP := fun l => match l with
                      | nil => inl tt
                      | cons h t => inr _ (h, t)
                      end;
    }.
  Next Obligation.
    destruct gx.
    - destruct u. auto.
    - destruct p. auto.
  Defined.
  Next Obligation.
    destruct x; auto.
  Defined.
End permType.

Notation "P ⊢ ti ⤳ ts ::: U" := (typing P (ptApp _ _ U) ti ts) (at level 60).
Notation "xi :: T ▷ xs" := (ptApp _ _ T xi xs) (at level 35).
Notation "T1 ⊕ T2" := (plusPT T1 T2) (at level 50).
Notation "T1 ⊗ T2" := (timesPT T1 T2) (at level 40).
Notation "T1 ⋆ T2" := (starPT T1 T2) (at level 40).
Notation "'ex' ( x 'oftype' A ) T" := (existsPT (As:=A) (fun x => T)) (at level 70).
Notation "T ∅ P" := (withPerms T P) (at level 40).

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Locations are a refinement of RTL pseudo-registers, used to reflect
  the results of register allocation (file [Allocation]). *)

Require Import OrderedType.
Require Import Coqlib.
Require Import Maps.
Require Import Ordered.
Require Import AST.
Require Import Values.
Require Export Machregs.
Require Import Program.

(** * Representation of locations *)

(** A location is either a processor register or (an abstract designation of)
  a slot in the activation record of the current function. *)

(** ** Processor registers *)

(** Processor registers usable for register allocation are defined
  in module [Machregs]. *)

(** ** Slots in activation records *)

(** A slot in an activation record is designated abstractly by a kind,
  a type and an integer offset.  Three kinds are considered:
- [Local]: these are the slots used by register allocation for
  pseudo-registers that cannot be assigned a hardware register.
- [Incoming]: used to store the parameters of the current function
  that cannot reside in hardware registers, as determined by the
  calling conventions.
- [Outgoing]: used to store arguments to called functions that
  cannot reside in hardware registers, as determined by the
  calling conventions. *)

Inductive slot: Type :=
  | Local
  | Incoming
  | Outgoing.

(** Morally, the [Incoming] slots of a function are the [Outgoing]
slots of its caller function.

The type of a slot indicates how it will be accessed later once mapped to
actual memory locations inside a memory-allocated activation record:
as 32-bit integers/pointers (type [Tint]) or as 64-bit floats (type [Tfloat]).

The offset of a slot, combined with its type and its kind, identifies
uniquely the slot and will determine later where it resides within the
memory-allocated activation record.  Offsets are always positive.
*)

Lemma slot_eq: forall (p q: slot), {p = q} + {p <> q}.
Proof.
  decide equality.
Defined.

Open Scope Z_scope.

Definition typesize (ty: typ) : Z :=
  match ty with
  | Tint => 1
  | Tlong => 2
  | Tfloat => 2
  | Tsingle => 1
  | Tany32 => 1
  | Tany64 => 2
  end.

Lemma typesize_pos:
  forall (ty: typ), typesize ty > 0.
Proof.
  destruct ty; compute; auto.
Qed.

Definition typealign (ty: typ) : Z :=
  match ty with
  | Tint => 1
  | Tlong => 2
  | Tfloat => 1
  | Tsingle => 1
  | Tany32 => 1
  | Tany64 => 1
  end.

Lemma typealign_pos:
  forall (ty: typ), typealign ty > 0.
Proof.
  destruct ty; compute; auto.
Qed.

Lemma typealign_typesize:
  forall (ty: typ), (typealign ty | typesize ty).
Proof.
  intros. exists (typesize ty / typealign ty); destruct ty; reflexivity.
Qed.

(** ** Locations *)

(** Locations are just the disjoint union of machine registers and
  activation record slots. *)

Inductive loc : Type :=
  | R (r: mreg)
  | S (sl: slot) (pos: Z) (ty: typ).

Module Loc.

  Definition type (l: loc) : typ :=
    match l with
    | R r => mreg_type r
    | S sl pos ty => ty
    end.

  Lemma eq: forall (p q: loc), {p = q} + {p <> q}.
  Proof.
    decide equality.
    apply mreg_eq.
    apply typ_eq.
    apply zeq.
    apply slot_eq.
  Defined.

(** As mentioned previously, two locations can be different (in the sense
  of the [<>] mathematical disequality), yet denote
  overlapping memory chunks within the activation record.
  Given two locations, three cases are possible:
- They are equal (in the sense of the [=] equality)
- They are different and non-overlapping.
- They are different but overlapping.

  The second case (different and non-overlapping) is characterized
  by the following [Loc.diff] predicate.
*)
  Definition diff (l1 l2: loc) : Prop :=
    match l1, l2 with
    | R r1, R r2 =>
        mreg_diff r1 r2
    | S s1 d1 t1, S s2 d2 t2 =>
        s1 <> s2 \/ d1 + typesize t1 <= d2 \/ d2 + typesize t2 <= d1
    | _, _ =>
        True
    end.

  Lemma same_not_diff:
    forall l, ~(diff l l).
  Proof.
    destruct l; unfold diff; auto using Machregs.same_not_diff.
    red; intros. destruct H; auto. generalize (typesize_pos ty); omega.
  Qed.

  Lemma diff_not_eq:
    forall l1 l2, diff l1 l2 -> l1 <> l2.
  Proof.
    unfold not; intros. subst l2. elim (same_not_diff l1 H).
  Qed.

  Lemma diff_sym:
    forall l1 l2, diff l1 l2 -> diff l2 l1.
  Proof.
    destruct l1; destruct l2; unfold diff; auto.
    apply diff_sym.
    intuition.
  Qed.

  Definition diff_dec (l1 l2: loc) : { Loc.diff l1 l2 } + { ~Loc.diff l1 l2 }.
  Proof.
    intros. destruct l1; destruct l2; simpl.
  - apply mreg_diff_dec.
  - left; auto.
  - left; auto.
  - destruct (slot_eq sl sl0).
    destruct (zle (pos + typesize ty) pos0).
    left; auto.
    destruct (zle (pos0 + typesize ty0) pos).
    left; auto.
    right; red; intros [P | [P | P]]. congruence. omega. omega.
    left; auto.
  Defined.

(** We now redefine some standard notions over lists, using the [Loc.diff]
  predicate instead of standard disequality [<>].

  [Loc.notin l ll] holds if the location [l] is different from all locations
  in the list [ll]. *)

  Fixpoint notin (l: loc) (ll: list loc) {struct ll} : Prop :=
    match ll with
    | nil => True
    | l1 :: ls => diff l l1 /\ notin l ls
    end.

  Lemma notin_iff:
    forall l ll, notin l ll <-> (forall l', In l' ll -> Loc.diff l l').
  Proof.
    induction ll; simpl.
    tauto.
    rewrite IHll. intuition. subst a. auto.
  Qed.

  Lemma notin_not_in:
    forall l ll, notin l ll -> ~(In l ll).
  Proof.
    intros; red; intros. rewrite notin_iff in H.
    elim (diff_not_eq l l); auto.
  Qed.

  Lemma notin_dec (l: loc) (ll: list loc) : {notin l ll} + {~notin l ll}.
  Proof.
    induction ll; simpl.
    left; auto.
    destruct (diff_dec l a).
    destruct IHll.
    left; auto.
    right; tauto.
    right; tauto.
  Defined.

(** [Loc.disjoint l1 l2] is true if the locations in list [l1]
  are different from all locations in list [l2]. *)

  Definition disjoint (l1 l2: list loc) : Prop :=
    forall x1 x2, In x1 l1 -> In x2 l2 -> diff x1 x2.

  Lemma disjoint_cons_left:
    forall a l1 l2,
    disjoint (a :: l1) l2 -> disjoint l1 l2.
  Proof.
    unfold disjoint; intros. auto with coqlib.
  Qed.
  Lemma disjoint_cons_right:
    forall a l1 l2,
    disjoint l1 (a :: l2) -> disjoint l1 l2.
  Proof.
    unfold disjoint; intros. auto with coqlib.
  Qed.

  Lemma disjoint_sym:
    forall l1 l2, disjoint l1 l2 -> disjoint l2 l1.
  Proof.
    unfold disjoint; intros. apply diff_sym; auto.
  Qed.

  Lemma in_notin_diff:
    forall l1 l2 ll, notin l1 ll -> In l2 ll -> diff l1 l2.
  Proof.
    intros. rewrite notin_iff in H. auto.
  Qed.

  Lemma notin_disjoint:
    forall l1 l2,
    (forall x, In x l1 -> notin x l2) -> disjoint l1 l2.
  Proof.
    intros; red; intros. exploit H; eauto. rewrite notin_iff; intros. auto.
  Qed.

  Lemma disjoint_notin:
    forall l1 l2 x, disjoint l1 l2 -> In x l1 -> notin x l2.
  Proof.
    intros; rewrite notin_iff; intros. red in H. auto.
  Qed.

(** [Loc.norepet ll] holds if the locations in list [ll] are pairwise
  different. *)

  Inductive norepet : list loc -> Prop :=
  | norepet_nil:
      norepet nil
  | norepet_cons:
      forall hd tl, notin hd tl -> norepet tl -> norepet (hd :: tl).

  Lemma norepet_dec (ll: list loc) : {norepet ll} + {~norepet ll}.
  Proof.
    induction ll.
    left; constructor.
    destruct (notin_dec a ll).
    destruct IHll.
    left; constructor; auto.
    right; red; intros P; inv P; contradiction.
    right; red; intros P; inv P; contradiction.
  Defined.

(** [Loc.no_overlap l1 l2] holds if elements of [l1] never overlap partially
  with elements of [l2]. *)

  Definition no_overlap (l1 l2 : list loc) :=
   forall r, In r l1 -> forall s, In s l2 ->  r = s \/ Loc.diff r s.

End Loc.

(** * Mappings from locations to values *)

(** The [Locmap] module defines mappings from locations to values,
  used as evaluation environments for the semantics of the [LTL]
  and [Linear] intermediate languages.  *)

Set Implicit Arguments.

Module Locmap.
  Inductive entry :=
    | EOne (v: val)
    | ETwo (hi lo: val).

  Inductive reg_part :=
    | POne (r: mreg)
    | PHigh (r: mreg)
    | PLow (r: mreg).

  Definition reg_part_eq: forall p p': reg_part, { p = p' } + { p <> p' }.
  Proof.
    decide equality; apply mreg_eq.
  Defined.

  Definition superregs_cases:
    forall r, {superregs r = nil} + {exists s, superregs r = s :: nil}.
  Proof.
    intros. destruct r; auto; simpl; right; eexists; f_equal.
  Qed.

  Definition subregs_cases:
    forall r s, superregs r = s :: nil -> exists lo hi, subregs s = lo :: hi :: nil.
  Proof.
    intros. destruct r; try inversion H; repeat eexists; simpl; f_equal.
  Qed.

  Lemma subreg_not_diff:
    forall r s, subreg r s -> ~ mreg_diff r s.
  Proof.
    intros. unfold not, mreg_diff, overlap. intuition tauto.
  Qed.

  (** Figure out what register part to access for a given register. Registers
      that are not subregisters of others map to themselves. Subregisters map to
      a description of where to find them in their superregister. For example,
      on ARM, [S1] is the high part of the [D0] register pair, so
      [mreg_access S1 = PHigh D0]. *)
  Program Definition mreg_access (r: mreg): reg_part :=
    match superregs r with
    | nil => POne r
    | s :: _ =>
      match subregs s with
      | lo :: hi :: nil =>
        if mreg_eq r hi then PHigh s else PLow s
      | _ => !
      end
    end.
  Next Obligation.
    generalize (superregs_cases r); intros [A | A].
    rewrite A in Heq_anonymous0; congruence.
    destruct A as [x A]. assert (x = s) by congruence; subst x.
    apply subregs_cases in A. destruct A as [lo [hi]]. congruence.
  Qed.

  Lemma high_is_subreg:
    forall r s, mreg_access r = PHigh s -> subreg r s.
  Proof.
    intros.
    destruct r; compute in H; try inversion H; rewrite dec_eq_true in *; compute; auto.
  Qed.

  Corollary high_not_diff:
    forall r s, mreg_access r = PHigh s -> ~ Loc.diff (R r) (R s).
  Proof.
    intros. unfold Loc.diff, mreg_diff, overlap. apply high_is_subreg in H; intuition auto.
  Qed.

  Corollary high_not_eq:
    forall r s, mreg_access r = PHigh s -> r <> s.
  Proof.
    intros. apply high_is_subreg in H. apply subreg_not_eq; auto.
  Qed.

  Lemma low_is_subreg:
    forall r s, mreg_access r = PLow s -> subreg r s.
  Proof.
    intros.
    destruct r; compute in H; try inversion H;
      rewrite dec_eq_false in *; try congruence;
      subst; compute; auto.
  Qed.

  Corollary low_not_diff:
    forall r s, mreg_access r = PLow s -> ~ Loc.diff (R r) (R s).
  Proof.
    intros. unfold Loc.diff, mreg_diff, overlap. apply low_is_subreg in H; intuition auto.
  Qed.

  Corollary low_not_eq:
    forall r s, mreg_access r = PLow s -> r <> s.
  Proof.
    intros. apply low_is_subreg in H. apply subreg_not_eq; auto.
  Qed.

  Lemma one_is_eq:
    forall r s, mreg_access r = POne s -> r = s.
  Proof.
    intros. destruct r; compute in H; try inversion H; auto.
  Qed.

  Ltac mreg_access_subregs :=
    match goal with
    | [ H: Locmap.mreg_access _ = Locmap.POne _ |- _ ] =>
      apply Locmap.one_is_eq in H; subst; mreg_access_subregs
    | [ H: Locmap.mreg_access _ = Locmap.PHigh _ |- _ ] =>
      apply Locmap.high_is_subreg in H; mreg_access_subregs
    | [ H: Locmap.mreg_access _ = Locmap.PLow _ |- _ ] =>
      apply Locmap.low_is_subreg in H; mreg_access_subregs
    | _ => idtac
    end.

  Lemma subreg_high_or_low:
    forall r s, subreg r s -> mreg_access r = PHigh s \/ mreg_access r = PLow s.
  Proof.
    intros.
    destruct s; compute in H; try contradiction;
      decompose [or] H; try contradiction; subst; auto.
  Qed.

  Lemma superreg_one:
    forall r s, subreg r s -> mreg_access s = POne s.
  Proof.
    intros.
    destruct s; compute in H; try contradiction; reflexivity.
  Qed.

  Lemma mreg_access_high:
    forall r s,
    mreg_access r = PHigh s ->
    exists hi lo, subregs s = lo :: hi :: nil /\ r = hi.
  Proof.
    intros. generalize (high_is_subreg r H); intros.
    destruct s; compute in H0; decompose [or] H0; try contradiction;
      subst; compute in H; try inversion H;
      simpl; eexists; eexists; auto.
  Qed.

  Lemma mreg_access_low:
    forall r s,
    mreg_access r = PLow s ->
    exists hi lo, subregs s = lo :: hi :: nil /\ r = lo.
  Proof.
    intros. generalize (low_is_subreg r H); intros.
    destruct s; compute in H0; decompose [or] H0; try contradiction;
      subst; compute in H; try inversion H;
      simpl; eexists; eexists; auto.
  Qed.

  Lemma mreg_access_inj: forall r r', mreg_access r = mreg_access r' -> r = r'.
  Proof.
    intros.
    destruct (mreg_access r) eqn:R, (mreg_access r') eqn:R'; try inversion H.
    - apply one_is_eq in R. apply one_is_eq in R'. congruence.
    - apply mreg_access_high in R. apply mreg_access_high in R'.
      destruct R as [hi [lo]]; destruct H0. destruct R' as [hi' [lo']]; destruct H3.
      congruence.
    - apply mreg_access_low in R. apply mreg_access_low in R'.
      destruct R as [hi [lo]]; destruct H0. destruct R' as [hi' [lo']]; destruct H3.
      congruence.
  Qed.

  Lemma diff_high_diff:
    forall p p' r hi,
    Loc.diff (R p) (R hi) ->
    mreg_access p = POne p' ->
    mreg_access hi = PHigh r ->
    Loc.diff (R p) (R r).
  Proof.
    intros. assert (p = p') by auto using one_is_eq; subst p'.
    assert (subreg hi r) by auto using high_is_subreg.
    destruct (mreg_eq r p).
    - subst. apply Loc.diff_sym in H.
      unfold Loc.diff, mreg_diff, overlap in H. exfalso. intuition auto.
    - assert (~ subreg r p).
      { apply high_is_subreg in H1. eauto using subreg_intrans. }
      assert (~ superreg r p).
      { contradict H3. apply superregs_subregs in H3.
        apply subreg_high_or_low in H3. destruct H3; congruence. }
      apply Loc.diff_sym. unfold Loc.diff, mreg_diff, overlap. tauto.
  Qed.

  Lemma diff_low_diff:
    forall p p' r lo,
    Loc.diff (R p) (R lo) ->
    mreg_access p = POne p' ->
    mreg_access lo = PLow r ->
    Loc.diff (R p) (R r).
  Proof.
    intros. assert (p = p') by auto using one_is_eq; subst p'.
    assert (subreg lo r) by auto using low_is_subreg.
    destruct (mreg_eq r p).
    - subst. apply Loc.diff_sym in H.
      unfold Loc.diff, mreg_diff, overlap in H. exfalso. intuition auto.
    - assert (~ subreg r p).
      { apply low_is_subreg in H1. eauto using subreg_intrans. }
      assert (~ superreg r p).
      { contradict H3. apply superregs_subregs in H3.
        apply subreg_high_or_low in H3. destruct H3; congruence. }
      apply Loc.diff_sym. unfold Loc.diff, mreg_diff, overlap. tauto.
  Qed.

  Lemma mreg_not_eq_not_diff:
    forall r r',
    r <> r' ->
    ~ mreg_diff r r' ->
    subreg r r' \/ subreg r' r.
  Proof.
    intros. unfold not, mreg_diff, overlap in H0.
    destruct (subreg_dec r r'); auto.
    destruct (subreg_dec r' r); auto.
    assert (~ superreg r r'). { contradict n0. apply superregs_subregs; auto. }
    tauto.
  Qed.

  Lemma mreg_access_cases:
    forall r s,
    mreg_diff r s \/
    r = s \/
    (mreg_access r = POne r /\ (mreg_access s = PHigh r \/ mreg_access s = PLow r)) \/
    (mreg_access s = POne s /\ (mreg_access r = PHigh s \/ mreg_access r = PLow s)).
  Proof.
    intros.
    destruct (mreg_diff_dec r s); auto.
    destruct (mreg_eq r s); auto.
    right. right.
    exploit mreg_not_eq_not_diff; eauto; intros [A | B].
    - right. exploit superreg_one; eauto. exploit subreg_high_or_low; eauto.
    - left. exploit superreg_one; eauto. exploit subreg_high_or_low; eauto.
  Qed.

  Lemma mreg_diff_high:
    forall r s s',
      mreg_diff r s ->
      mreg_access s = PHigh s' ->
      (mreg_diff r s' \/ mreg_access r = PLow s').
  Proof.
    intros.
    destruct (subreg_dec r s').
    - apply subreg_high_or_low in s0 as [Hi | Lo].
      + apply diff_not_eq in H. rewrite <- Hi in H0.
        exfalso. auto using mreg_access_inj.
      + auto.
    - left. unfold mreg_diff. split.
      + contradict H. subst. apply high_is_subreg in H0.
        unfold not; intros. apply diff_sym in H.
        eapply subreg_not_diff; eauto.
      + unfold mreg_diff in H. destruct H. apply high_is_subreg in H0.
        unfold overlap in *. contradict H1. destruct H1.
        * contradiction.
        * apply superregs_subregs in H1.
          exfalso. eauto using subreg_intrans.
  Qed.

  Lemma mreg_diff_low:
    forall r s s',
      mreg_diff r s ->
      mreg_access s = PLow s' ->
      (mreg_diff r s' \/ mreg_access r = PHigh s').
  Proof.
    intros.
    destruct (subreg_dec r s').
    - apply subreg_high_or_low in s0 as [Hi | Lo].
      + auto.
      + apply diff_not_eq in H. rewrite <- Lo in H0.
        exfalso. auto using mreg_access_inj.
    - left. unfold mreg_diff. split.
      + contradict H. subst. apply low_is_subreg in H0.
        unfold not; intros. apply diff_sym in H.
        eapply subreg_not_diff; eauto.
      + unfold mreg_diff in H. destruct H. apply low_is_subreg in H0.
        unfold overlap in *. contradict H1. destruct H1.
        * contradiction.
        * apply superregs_subregs in H1.
          exfalso. eauto using subreg_intrans.
  Qed.

  Lemma mreg_diff_subreg_diff:
    forall r s s',
    mreg_diff r s ->
    subreg s' s ->
    mreg_diff r s'.
  Proof.
    intros. generalize (mreg_access_cases r s'); intros [Diff | [Eq | [Sub | Sub]]].
    - auto.
    - subst. exfalso. eapply subreg_not_diff; eauto.
    - destruct Sub as [Super [Hi | Lo]].
      + apply high_is_subreg in Hi.
        apply subregs_superregs in H0. apply subregs_superregs in Hi.
        generalize (superregs_cases s'); intros [Nil | One].
        * rewrite Nil in *. contradiction.
        * destruct One. rewrite H1 in *. apply diff_not_eq in H.
          inversion H0; inversion Hi; try contradiction; congruence.
      + apply low_is_subreg in Lo.
        apply subregs_superregs in H0. apply subregs_superregs in Lo.
        generalize (superregs_cases s'); intros [Nil | One].
        * rewrite Nil in *. contradiction.
        * destruct One. rewrite H1 in *. apply diff_not_eq in H.
          inversion H0; inversion Lo; try contradiction; congruence.
    - destruct Sub as [Super [Hi | Lo]].
      + apply high_is_subreg in Hi. exfalso. eauto using subreg_intrans.
      + apply low_is_subreg in Lo. exfalso. eauto using subreg_intrans.
  Qed.

  Definition get_one  (e: entry): val := match e with EOne v => v      | _ => Vundef end.
  Definition get_high (e: entry): val := match e with ETwo hi lo => hi | _ => Vundef end.
  Definition get_low  (e: entry): val := match e with ETwo hi lo => lo | _ => Vundef end.

  Definition t := loc -> entry.

  Definition init (x: val) : t := fun (_: loc) => EOne x.

  Definition get (l: loc) (m: t) : val :=
    match l with
    | R r =>
      match mreg_access r with
      | POne r => get_one (m l)
      | PHigh s => get_high (m (R s))
      | PLow s => get_low (m (R s))
      end
    | S _ _ _ => get_one (m l)
    end.

  (* Auxiliary for some places where a function of type [loc -> val] is expected. *)
  Definition read (m: t) : loc -> val := fun (l: loc) => get l m.

  (** The [set] operation over location mappings reflects the overlapping
      properties of locations: changing the value of a location [l]
      invalidates (sets to [Vundef]) the locations that partially overlap
      with [l].  In other terms, the result of [set l v m]
      maps location [l] to value [v], locations that overlap with [l]
      to [Vundef], and locations that are different (and non-overlapping)
      from [l] to their previous values in [m].  This is apparent in the
      ``good variables'' properties [Locmap.gss] and [Locmap.gso].

      Additionally, the [set] operation also anticipates the fact that
      abstract stack slots are mapped to concrete memory locations
      in the [Stacking] phase.  Hence, values stored in stack slots
      are normalized according to the type of the slot. *)

  Definition set_high (e: entry) (v: val): entry :=
    match e with
      | EOne _ => ETwo v Vundef
      | ETwo hi lo => ETwo v lo
    end.

  Definition set_low (e: entry) (v: val): entry :=
    match e with
      | EOne _ => ETwo Vundef v
      | ETwo hi lo => ETwo hi v
    end.

  Definition set (l: loc) (v: val) (m: t) : t :=
    fun (p: loc) =>
      if Loc.eq l p then
        match l with
        | R r =>
          match mreg_access r with
          | POne r => EOne v
          | PHigh s => set_high (m (R s)) v
          | PLow s => set_low (m (R s)) v
          end
        | S sl ofs ty => EOne (Val.load_result (chunk_of_type ty) v)
        end
      else if Loc.diff_dec l p then
        m p
      else
        match l with
        | R r =>
          match mreg_access r with
          | POne r => EOne v
          | PHigh s => set_high (m (R s)) v
          | PLow s => set_low (m (R s)) v
          end
        | S sl ofs ty => EOne Vundef
        end.

  Definition set' (l: loc) (v: val) (m: t) : t :=
    fun (p: loc) =>
      if Loc.diff_dec l p then
        m p
      else
        match l with
          | R r =>
            match mreg_access r with
            | POne r => EOne v
            | PHigh s => set_high (m (R s)) v
            | PLow s => set_low (m (R s)) v
            end
          | S sl ofs ty =>
            if Loc.eq l p then
              EOne (Val.load_result (chunk_of_type ty) v)
            else
              EOne Vundef
        end.

  Lemma set_set'_equal: forall l v m x, (set l v m) x = (set' l v m) x.
  Proof.
    intros. unfold set, set'.
    destruct (Loc.diff_dec l x).
    - rewrite dec_eq_false; auto. apply Loc.diff_not_eq; auto.
    - destruct (Loc.eq l x); auto.
  Qed.

  Lemma get_set_get_set': forall l p v m, get p (set l v m) = get p (set' l v m).
  Proof.
    intros. unfold get.
    destruct p. destruct (mreg_access r); rewrite set_set'_equal; auto.
    rewrite set_set'_equal; auto.
  Qed.

  Lemma gss: forall l v m,
    get l (set l v m) =
    match l with R r => v | S sl ofs ty => Val.load_result (chunk_of_type ty) v end.
  Proof.
    intros.
    destruct l.
    - simpl. unfold set. destruct (mreg_access r) eqn: E.
      + rewrite dec_eq_true; auto.
      + destruct (mreg_eq r r0).
        * apply high_not_eq in E; contradiction.
        * rewrite pred_dec_false; try congruence.
          rewrite pred_dec_false. destruct (m (R r0)); auto. auto using high_not_diff.
      + destruct (mreg_eq r r0).
        * apply low_not_eq in E; contradiction.
        * rewrite pred_dec_false; try congruence.
          rewrite pred_dec_false. destruct (m (R r0)); auto. auto using low_not_diff.
    - unfold get, set. rewrite dec_eq_true. reflexivity.
  Qed.

  Lemma gss_reg: forall r v m, get (R r) (set (R r) v m) = v.
  Proof.
    intros. unfold get, set. destruct (mreg_access r) eqn: E.
    - rewrite dec_eq_true. auto.
    - rewrite !pred_dec_false.
      + destruct (m (R r0)); auto.
      + auto using high_not_diff.
      + apply high_not_eq in E; congruence.
    - rewrite !pred_dec_false.
      + destruct (m (R r0)); auto.
      + auto using low_not_diff.
      + apply low_not_eq in E; congruence.
  Qed.

  Lemma gss_typed: forall l v m, Val.has_type v (Loc.type l) -> get l (set l v m) = v.
  Proof.
    intros. rewrite gss. destruct l. auto. apply Val.load_result_same; auto.
  Qed.

  Lemma gso_aux: forall l v m p, Loc.diff l p -> (set l v m) p = m p.
  Proof.
    intros. unfold set.
    rewrite dec_eq_false, pred_dec_true; auto using Loc.diff_not_eq.
  Qed.

  Lemma gso: forall l v m p, Loc.diff l p -> get p (set l v m) = get p m.
  Proof.
    intros. unfold get. destruct p; rewrite gso_aux; auto.
    destruct (mreg_access r) eqn:E; auto.
    - destruct l; auto.
      rename r0 into super, r1 into other.
      destruct (reg_part_eq (mreg_access other) (PLow super)).
      + unfold set. rewrite dec_eq_false, pred_dec_false.
        rewrite e. destruct (m (R super)); auto.
        apply low_is_subreg in e. unfold Loc.diff, mreg_diff, overlap. intuition tauto.
        apply low_is_subreg, subreg_not_eq in e. congruence.
      + assert (Loc.diff (R other) (R super)).
        { unfold Loc.diff, mreg_diff, overlap. split.
          - apply high_is_subreg, subreg_not_diff in E.
            contradict E. subst. apply Loc.diff_sym in H. auto.
          - unfold not; intros [A | B].
            + apply subreg_high_or_low in A. destruct A.
              * rewrite <- E in H0. generalize (mreg_access_inj other r H0); intros.
                subst. apply Loc.diff_not_eq in H. auto.
              * contradiction.
            + apply superregs_subregs, subreg_high_or_low in B. destruct B.
              * apply high_is_subreg in E. apply high_is_subreg in H0.
                eapply subreg_intrans with (r2 := super); eauto.
              * apply high_is_subreg in E. apply low_is_subreg in H0.
                eapply subreg_intrans with (r2 := super); eauto. }
        unfold set. rewrite dec_eq_false, pred_dec_true; auto.
        auto using Loc.diff_not_eq.
    - destruct l; auto.
      rename r0 into super, r1 into other.
      destruct (reg_part_eq (mreg_access other) (PHigh super)).
      + unfold set. rewrite dec_eq_false, pred_dec_false.
        rewrite e. destruct (m (R super)); auto.
        apply high_is_subreg in e. unfold Loc.diff, mreg_diff, overlap. intuition tauto.
        apply high_is_subreg, subreg_not_eq in e. congruence.
      + assert (Loc.diff (R other) (R super)).
        { unfold Loc.diff, mreg_diff, overlap. split.
          - apply low_is_subreg, subreg_not_diff in E.
            contradict E. subst. apply Loc.diff_sym in H. auto.
          - unfold not; intros [A | B].
            + apply subreg_high_or_low in A. destruct A.
              * contradiction.
              * rewrite <- E in H0. generalize (mreg_access_inj other r H0); intros.
                subst. apply Loc.diff_not_eq in H. auto.
            + apply superregs_subregs, subreg_high_or_low in B. destruct B.
              * apply low_is_subreg in E. apply high_is_subreg in H0.
                eapply subreg_intrans with (r2 := super); eauto.
              * apply low_is_subreg in E. apply low_is_subreg in H0.
                eapply subreg_intrans with (r2 := super); eauto. }
        unfold set. rewrite dec_eq_false, pred_dec_true; auto.
        auto using Loc.diff_not_eq.
  Qed.

  Fixpoint undef (ll: list loc) (m: t) {struct ll} : t :=
    match ll with
    | nil => m
    | l1 :: ll' => undef ll' (set l1 Vundef m)
    end.

  Lemma guo: forall ll l m, Loc.notin l ll -> get l (undef ll m) = get l m.
  Proof.
    induction ll; simpl; intros. auto.
    destruct H. rewrite IHll; auto. apply gso. apply Loc.diff_sym; auto.
  Qed.
  
  Lemma mreg_both_overlap:
    forall r r' s,
    r <> r' ->
    overlap r s ->
    overlap r' s ->
    (mreg_access r = PHigh s /\ mreg_access r' = PLow s) \/
    (mreg_access r = PLow s /\ mreg_access r' = PHigh s).
  Proof.
    intros. unfold overlap in *. destruct H0, H1.
    - destruct s; simpl in *; try contradiction;
        decompose [or] H0; decompose [or] H1; subst; try contradiction; auto.
    - apply superregs_subregs in H1. exfalso. eauto using subreg_intrans.
    - apply superregs_subregs in H0. exfalso. eauto using subreg_intrans.
    - destruct s; simpl in *; try contradiction;
        decompose [or] H0; decompose [or] H1; subst; try contradiction.
  Qed.

  Lemma gus_aux_reg:
    forall r r' m, get (R r) m = Vundef -> get (R r) (set (R r') Vundef m) = Vundef.
  Proof.
    intros.
    destruct (mreg_eq r r'). subst; rewrite gss; auto.
    destruct (mreg_diff_dec r r'). rewrite gso; auto using Loc.diff_sym.
    destruct (mreg_not_eq_not_diff n n0).
    - (* set superreg, read subreg *)
      generalize (superreg_one r r' H0); intros.
      generalize (subreg_high_or_low r r' H0); intros [A | A].
      + unfold get, set. rewrite H1, A. rewrite dec_eq_true; auto.
      + unfold get, set. rewrite H1, A. rewrite dec_eq_true; auto.
    - (* set subreg, read superreg *)
      generalize (superreg_one r' r H0); intros.
      generalize (subreg_high_or_low r' r H0); intros [A | A].
      + unfold get, set. rewrite H1, A.
        rewrite dec_eq_false, pred_dec_false.
        destruct (m (R r)); auto.
        intuition auto using diff_sym.
        congruence.
      + unfold get, set. rewrite H1, A.
        rewrite dec_eq_false, pred_dec_false.
        destruct (m (R r)); auto.
        intuition auto using diff_sym.
        congruence.
  Qed.

  Lemma gus_aux:
    forall l m p, get p m = Vundef -> get p (set l Vundef m) = Vundef.
  Proof.
    intros.
    destruct l, p.
    - apply gus_aux_reg; auto.
    - unfold get, set. rewrite dec_eq_false, pred_dec_true; auto.
      simpl; auto.
      discriminate.
    - unfold get, set. rewrite dec_eq_false, pred_dec_true; auto.
      simpl; auto.
      discriminate.
    - destruct (Loc.eq (S sl0 pos0 ty0) (S sl pos ty)).
      rewrite e, gss. destruct ty; auto.
      destruct (Loc.diff_dec (S sl0 pos0 ty0) (S sl pos ty)).
      rewrite gso; auto using Loc.diff_sym.
      simpl. unfold set.
      rewrite dec_eq_false, pred_dec_false; auto using Loc.diff_sym.
  Qed.

  Lemma gus: forall ll l m, In l ll -> get l (undef ll m) = Vundef.
  Proof.
    assert (P: forall ll l m, get l m = Vundef -> get l (undef ll m) = Vundef).
    { induction ll; simpl; intros. auto. apply IHll.
      apply gus_aux; auto. }
    induction ll; simpl; intros. contradiction.
    destruct H. apply P. subst a. apply gss_typed. exact I.
    auto.
  Qed.

  Definition getpair (p: rpair loc) (m: t) : val :=
    match p with
    | One l => get l m
    | Twolong l1 l2 => Val.longofwords (get l1 m) (get l2 m)
    end.

  Definition setpair (p: rpair mreg) (v: val) (m: t) : t :=
    match p with
    | One r => set (R r) v m
    | Twolong hi lo => set (R lo) (Val.loword  v) (set (R hi) (Val.hiword v) m)
    end.

  Lemma getpair_exten:
    forall p ls1 ls2,
    (forall l, In l (regs_of_rpair p) -> get l ls2 = get l ls1) ->
    getpair p ls2 = getpair p ls1.
  Proof.
    intros. destruct p; simpl. 
    apply H; simpl; auto.
    f_equal; apply H; simpl; auto.
  Qed.

  Lemma gpo:
    forall p v m l,
    forall_rpair (fun r => Loc.diff l (R r)) p -> get l (setpair p v m) = get l m.
  Proof.
    intros; destruct p; simpl in *. 
  - apply gso. apply Loc.diff_sym; auto.
  - destruct H. rewrite ! gso by (apply Loc.diff_sym; auto). auto.
  Qed.

  Fixpoint setres (res: builtin_res mreg) (v: val) (m: t) : t :=
    match res with
    | BR r => set (R r) v m
    | BR_none => m
    | BR_splitlong hi lo =>
        setres lo (Val.loword v) (setres hi (Val.hiword v) m)
    end.

End Locmap.

Notation "a @ b" := (Locmap.get b a) (at level 1) : ltl.

(** * Total ordering over locations *)

Module IndexedTyp <: INDEXED_TYPE.
  Definition t := typ.
  Definition index (x: t) :=
    match x with
    | Tany32 => 1%positive
    | Tint => 2%positive
    | Tsingle => 3%positive
    | Tany64 => 4%positive
    | Tfloat => 5%positive
    | Tlong => 6%positive
    end.
  Lemma index_inj: forall x y, index x = index y -> x = y.
  Proof. destruct x; destruct y; simpl; congruence. Qed.
  Definition eq := typ_eq.
End IndexedTyp.

Module OrderedTyp := OrderedIndexed(IndexedTyp).

Module IndexedSlot <: INDEXED_TYPE.
  Definition t := slot.
  Definition index (x: t) :=
    match x with Local => 1%positive | Incoming => 2%positive | Outgoing => 3%positive end.
  Lemma index_inj: forall x y, index x = index y -> x = y.
  Proof. destruct x; destruct y; simpl; congruence. Qed.
  Definition eq := slot_eq.
End IndexedSlot.

Module OrderedSlot := OrderedIndexed(IndexedSlot).

Module OrderedLoc <: OrderedType.
  Definition t := loc.
  Definition eq (x y: t) := x = y.
  Definition lt (x y: t) :=
    match x, y with
    | R r1, R r2 => OrderedMreg.lt r1 r2
    | R _, S _ _ _ => True
    | S _ _ _, R _ => False
    | S sl1 ofs1 ty1, S sl2 ofs2 ty2 =>
        OrderedSlot.lt sl1 sl2 \/ (sl1 = sl2 /\
        (ofs1 < ofs2 \/ (ofs1 = ofs2 /\ OrderedTyp.lt ty1 ty2)))
    end.
  Lemma eq_refl : forall x : t, eq x x.
  Proof (@refl_equal t).
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof (@sym_equal t).
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof (@trans_equal t).
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros.
    destruct x; destruct y; destruct z; try tauto.
    eauto using OrderedMreg.lt_trans.
    destruct H.
    destruct H0. left; eapply OrderedSlot.lt_trans; eauto.
    destruct H0. subst sl0. auto.
    destruct H. subst sl.
    destruct H0. auto.
    destruct H.
    right.  split. auto.
    intuition.
    right; split. congruence. eapply OrderedTyp.lt_trans; eauto.
  Qed.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros; red; intros. subst y.
    destruct x.
    eapply OrderedMreg.lt_not_eq in H; auto.
    destruct H. eelim OrderedSlot.lt_not_eq; eauto. red; auto.
    destruct H. destruct H0. omega.
    destruct H0. eelim OrderedTyp.lt_not_eq; eauto. red; auto.
  Qed.
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros. destruct x; destruct y.
  - destruct (OrderedMreg.compare r r0).
    + apply LT. red. auto.
    + apply EQ. red. red in e. congruence.
    + apply GT. red. auto.
  - apply LT. red; auto.
  - apply GT. red; auto.
  - destruct (OrderedSlot.compare sl sl0).
    + apply LT. red; auto.
    + destruct (OrderedZ.compare pos pos0).
      * apply LT. red. auto.
      * destruct (OrderedTyp.compare ty ty0).
        apply LT. red; auto.
        apply EQ. red; red in e; red in e0; red in e1. congruence.
        apply GT. red; auto.
      * apply GT. red. auto.
    + apply GT. red; auto.
  Defined.
  Definition eq_dec := Loc.eq.

(** Connection between the ordering defined here and the [Loc.diff] predicate. *)

  Definition diff_low_bound (l: loc) : loc :=
    match l with
    | R r => R (OrderedMreg.diff_low_bound r)
    | S sl ofs ty => S sl (ofs - 1) Tany64
    end.

  Definition diff_high_bound (l: loc) : loc :=
    match l with
    | R r => R (OrderedMreg.diff_high_bound r)
    | S sl ofs ty => S sl (ofs + typesize ty - 1) Tlong
    end.

  Lemma outside_interval_diff:
    forall l l', lt l' (diff_low_bound l) \/ lt (diff_high_bound l) l' -> Loc.diff l l'.
  Proof.
    intros.
    destruct l as [mr | sl ofs ty]; destruct l' as [mr' | sl' ofs' ty']; simpl in *; auto.
    - auto using OrderedMreg.outside_interval_diff.
    - assert (RANGE: forall ty, 1 <= typesize ty <= 2).
      { intros; unfold typesize. destruct ty0; omega.  }
      destruct H.
      + destruct H. left. apply sym_not_equal. apply OrderedSlot.lt_not_eq; auto.
        destruct H. right.
        destruct H0. right. generalize (RANGE ty'); omega.
        destruct H0.
        assert (ty' = Tint \/ ty' = Tsingle \/ ty' = Tany32).
        { unfold OrderedTyp.lt in H1. destruct ty'; auto; compute in H1; congruence. }
        right. destruct H2 as [E|[E|E]]; subst ty'; simpl typesize; omega.
      + destruct H. left. apply OrderedSlot.lt_not_eq; auto.
        destruct H. right.
        destruct H0. left; omega.
        destruct H0. exfalso. destruct ty'; compute in H1; congruence.
  Qed.

  Lemma diff_outside_interval:
    forall l l', Loc.diff l l' -> lt l' (diff_low_bound l) \/ lt (diff_high_bound l) l'.
  Proof.
    intros.
    destruct l as [mr | sl ofs ty]; destruct l' as [mr' | sl' ofs' ty']; simpl in *; auto.
    - auto using OrderedMreg.diff_outside_interval.
    - destruct (OrderedSlot.compare sl sl'); auto.
      destruct H. contradiction.
      destruct H.
      right; right; split; auto. left; omega.
      left; right; split; auto.
      assert (EITHER: typesize ty' = 1 /\ OrderedTyp.lt ty' Tany64 \/ typesize ty' = 2).
      { destruct ty'; compute; auto. }
      destruct (zlt ofs' (ofs - 1)). left; auto.
      destruct EITHER as [[P Q] | P].
      right; split; auto. omega.
      left; omega.
  Qed.

End OrderedLoc.


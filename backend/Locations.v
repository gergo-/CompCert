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
Require Import Memory.
Require Export Memdata.
Require Export Machregs.
Require Export Registerfile.

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
as 32-bit or 64-bit quantities ([Q32] or [Q64]).

The offset of a slot, combined with its quantity and its kind, identifies
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

Definition quantity_align (q: quantity) : Z := 1.

Lemma quantity_align_pos:
  forall (q: quantity), quantity_align q > 0.
Proof.
  destruct q; compute; auto.
Qed.

Lemma quantity_align_typesize:
  forall (q: quantity), (quantity_align q | typesize (typ_of_quantity q)).
Proof.
  intros. destruct q; simpl. exists 1; eauto. exists 2; eauto.
Qed.

(** ** Locations *)

(** Locations are just the disjoint union of machine registers and
  activation record slots. *)

Inductive loc : Type :=
  | R (r: mreg)
  | S (sl: slot) (pos: Z) (q: quantity).

Module Loc.

  Definition type (l: loc) : typ :=
    match l with
    | R r => mreg_type r
    | S sl pos q => typ_of_quantity q
    end.

  Lemma eq: forall (p q: loc), {p = q} + {p <> q}.
  Proof.
    decide equality.
    apply mreg_eq.
    apply quantity_eq.
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
    | S s1 d1 q1, S s2 d2 q2 =>
        s1 <> s2 \/ d1 + typesize (typ_of_quantity q1) <= d2 \/ d2 + typesize (typ_of_quantity q2) <= d1
    | _, _ =>
        True
    end.

  Lemma same_not_diff:
    forall l, ~(diff l l).
  Proof.
    destruct l; unfold diff; auto.
    apply Registerfile.same_not_diff.
    red; intros. destruct H; auto. generalize (typesize_pos (typ_of_quantity q)); omega.
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
    apply Registerfile.diff_sym.
    intuition.
  Qed.

  Definition diff_dec (l1 l2: loc) : { Loc.diff l1 l2 } + { ~Loc.diff l1 l2 }.
  Proof.
    intros. destruct l1; destruct l2; simpl.
  - apply mreg_diff_dec.
  - left; auto.
  - left; auto.
  - destruct (slot_eq sl sl0).
    destruct (zle (pos + typesize (typ_of_quantity q)) pos0).
    left; auto.
    destruct (zle (pos0 + typesize (typ_of_quantity q0)) pos).
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

  Definition t := (Regfile.t * (loc -> list memval))%type.

  Definition chunk_of_loc (l: loc) : memory_chunk :=
    chunk_of_type (Loc.type l).

  Definition init : t := (Regfile.init, fun (l: loc) => encode_val (chunk_of_loc l) Vundef).

  Definition get (l: loc) (m: t) : val :=
    match l, m with
    | R r, (rf, stack) => Regfile.get r rf
    | S _ _ _, (rf, stack) => decode_val (chunk_of_loc l) (stack l)
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

  Definition set (l: loc) (v: val) (m: t) : t :=
    match l, m with
    | R r, (rf, stack) => (Regfile.set r v rf, stack)
    | S _ _ _, (rf, stack) => (rf,
      fun (p: loc) =>
        if Loc.eq l p then
          encode_val (chunk_of_loc l) v
        else if Loc.diff_dec l p then
          stack p
        else
          encode_val (chunk_of_loc l) Vundef)
    end.

  Lemma gss: forall l v m,
    get l (set l v m) = Val.load_result (chunk_of_type (Loc.type l)) v.
  Proof.
    intros.
    destruct l, m. apply Regfile.gss.
    unfold get, set. rewrite dec_eq_true.
    erewrite <- decode_encode_val_similar; eauto.
    eapply decode_encode_val_general.
  Qed.

  Lemma gss_reg: forall r v m, Val.has_type v (mreg_type r) -> get (R r) (set (R r) v m) = v.
  Proof.
    intros. rewrite gss. apply Val.load_result_same; auto.
  Qed.

  Lemma gss_typed: forall l v m, Val.has_type v (Loc.type l) -> get l (set l v m) = v.
  Proof.
    intros. rewrite gss. apply Val.load_result_same; auto.
  Qed.

  Lemma gso: forall l v m p, Loc.diff l p -> get p (set l v m) = get p m.
  Proof.
    intros.
    destruct l, m.
    destruct p; simpl in H; auto. apply Regfile.gso; auto using Registerfile.diff_sym.
    unfold get, set. destruct (Loc.eq (S sl pos q) p).
    subst p. elim (Loc.same_not_diff _ H).
    destruct (Loc.diff_dec (S sl pos q) p).
    auto.
    contradiction.
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

  Lemma gus: forall ll l m, In l ll -> get l (undef ll m) = Vundef.
  Proof.
    assert (P: forall ll l m, get l m = Vundef -> get l (undef ll m) = Vundef).
    { induction ll; simpl; intros. auto. apply IHll.
      destruct (Loc.diff_dec a l).
      rewrite gso; auto.
      destruct (Loc.eq a l). subst; apply gss_typed. simpl; auto.
      destruct a, l, m; simpl in n.
      simpl. rewrite Regfile.gu_overlap; auto.
      apply mreg_overlap_sym. apply not_same_not_diff_overlap; congruence.
      auto. auto. unfold get, set. rewrite dec_eq_false; auto.
      destruct (Loc.diff_dec (S sl pos q) (S sl0 pos0 q0)). auto. apply decode_encode_undef. }
    induction ll; simpl; intros. contradiction.
    destruct H. apply P. subst a. apply gss_typed. exact I.
    auto.
  Qed.

  Lemma gu_overlap:
    forall r s v m,
    mreg_overlap r s ->
    get (R r) (set (R s) v m) = Vundef.
  Proof.
    intros; simpl. destruct m. auto using Regfile.gu_overlap.
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
    intros; destruct p; unfold setpair.
  - apply gso. apply Loc.diff_sym; auto.
  - destruct H. rewrite ! gso by (apply Loc.diff_sym; auto). auto.
  Qed.

  Definition setres (res: builtin_res mreg) (v: val) (m: t) : t :=
    match res with
    | BR r => set (R r) v m
    | BR_none => m
    | BR_splitlong hi lo =>
        set (R lo) (Val.loword v) (set (R hi) (Val.hiword v) m)
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

Module IndexedQuantity <: INDEXED_TYPE.
  Definition t := quantity.
  Definition index (q: t) :=
    match q with
    | Q32 => 1%positive
    | Q64 => 2%positive
    end.
  Lemma index_inj: forall x y, index x = index y -> x = y.
  Proof. destruct x, y; simpl; congruence. Qed.
  Definition eq := quantity_eq.
End IndexedQuantity.

Module OrderedQuantity := OrderedIndexed(IndexedQuantity).

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
    | S sl1 ofs1 q1, S sl2 ofs2 q2 =>
        OrderedSlot.lt sl1 sl2 \/ (sl1 = sl2 /\
        (ofs1 < ofs2 \/ (ofs1 = ofs2 /\ OrderedQuantity.lt q1 q2)))
    end.
  Lemma eq_refl : forall x : t, eq x x.
  Proof (@eq_refl t).
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof (@eq_sym t).
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof (@eq_trans t).
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros.
    destruct x; destruct y; destruct z; try tauto.
    eapply Plt_trans; eauto.
    destruct H.
    destruct H0. left; eapply OrderedSlot.lt_trans; eauto.
    destruct H0. subst sl0. auto.
    destruct H. subst sl.
    destruct H0. auto.
    destruct H.
    right.  split. auto.
    intuition.
    right; split. congruence. eapply OrderedQuantity.lt_trans; eauto.
  Qed.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros; red; intros. subst y.
    destruct x.
    eelim Plt_strict; eauto.
    destruct H. eelim OrderedSlot.lt_not_eq; eauto. red; auto.
    destruct H. destruct H0. omega.
    destruct H0. eelim OrderedQuantity.lt_not_eq; eauto. red; auto.
  Qed.
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros. destruct x; destruct y.
  - destruct (OrderedPositive.compare (IndexedMreg.index r) (IndexedMreg.index r0)).
    + apply LT. red. auto.
    + apply EQ. red. f_equal. apply IndexedMreg.index_inj. auto.
    + apply GT. red. auto.
  - apply LT. red; auto.
  - apply GT. red; auto.
  - destruct (OrderedSlot.compare sl sl0).
    + apply LT. red; auto.
    + destruct (OrderedZ.compare pos pos0).
      * apply LT. red. auto.
      * destruct (OrderedQuantity.compare q q0).
        apply LT. red; auto.
        apply EQ. congruence.
        apply GT. red; auto.
      * apply GT. red. auto.
    + apply GT. red; auto.
  Defined.
  Definition eq_dec := Loc.eq.

(** Connection between the ordering defined here and the [Loc.diff] predicate. *)

  Definition diff_low_bound (l: loc) : loc :=
    match l with
    | R mr => R (OrderedMreg.diff_low_bound mr)
    | S sl ofs q => S sl (ofs - 1) Q64
    end.

  Definition diff_high_bound (l: loc) : loc :=
    match l with
    | R mr => R (OrderedMreg.diff_high_bound mr)
    | S sl ofs q => S sl (ofs + typesize (typ_of_quantity q) - 1) Q64
    end.

  Lemma outside_interval_diff:
    forall l l', lt l' (diff_low_bound l) \/ lt (diff_high_bound l) l' -> Loc.diff l l'.
  Proof.
    intros.
    destruct l as [mr | sl ofs q]; destruct l' as [mr' | sl' ofs' q']; simpl in *; auto.
    - auto using OrderedMreg.outside_interval_diff.
    - assert (RANGE: forall ty, 1 <= typesize ty <= 2).
      { intros; unfold typesize. destruct ty; omega.  }
      destruct H.
      + destruct H. left. apply not_eq_sym. apply OrderedSlot.lt_not_eq; auto.
        destruct H. right.
        destruct H0. right. generalize (RANGE (typ_of_quantity q')); omega.
        destruct H0.
        assert (typ_of_quantity q' = Tany32).
        { unfold OrderedTyp.lt in H1. destruct q'; auto; compute in H1; congruence. }
        right. rewrite H2; simpl typesize; omega.
      + destruct H. left. apply OrderedSlot.lt_not_eq; auto.
        destruct H. right.
        destruct H0. left; omega.
        destruct H0. exfalso. destruct q'; compute in H1; congruence.
  Qed.

  Lemma diff_outside_interval:
    forall l l', Loc.diff l l' -> lt l' (diff_low_bound l) \/ lt (diff_high_bound l) l'.
  Proof.
    intros.
    destruct l as [mr | sl ofs q]; destruct l' as [mr' | sl' ofs' q']; simpl in *; auto.
    - auto using OrderedMreg.diff_outside_interval.
    - destruct (OrderedSlot.compare sl sl'); auto.
      destruct H. contradiction.
      destruct H.
      right; right; split; auto. left; omega.
      left; right; split; auto.
      destruct q'; simpl in H. destruct (zlt ofs' (ofs - 1)).
      left; auto. right; split. omega. compute; auto.
      left; omega.
  Qed.

End OrderedLoc.


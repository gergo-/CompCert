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
  Inductive entry := EOne (v: val).

  Definition t := loc -> entry.

  Definition init (x: val) : t := fun (_: loc) => EOne x.

  Definition get_full (e: entry) : val := match e with EOne v => v end.
  Definition get_high (e: entry) : val := match e with EOne v => Val.pair_hi v end.
  Definition get_low  (e: entry) : val := match e with EOne v => Val.pair_lo v end.

  Definition set_full (e: entry) (v': val): val := match e with EOne v => v' end.
  Definition set_high (e: entry) (v': val): val := match e with EOne v => Val.pair_set_hi v v' end.
  Definition set_low  (e: entry) (v': val): val := match e with EOne v => Val.pair_set_lo v v' end.

  Definition get (l: loc) (m: t) : val :=
    match l with
    | R r =>
      match mreg_part r with
      | PFull r => get_full (m l)
      | PHigh s => get_high (m (R s))
      | PLow s  => get_low  (m (R s))
      end
    | S _ _ _ =>
      get_full (m l)
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

  Definition set_reg_val (r: mreg) (l': loc) (v: val) : val :=
    if Loc.eq (R r) l' then
      Val.load_result (chunk_of_type (mreg_type r)) v
    else
      Vundef.

  Definition set (l: loc) (v: val) (m: t) : t :=
    fun (l': loc) =>
      if Loc.diff_dec l l' then
        m l'
      else
        match l with
        | R r =>
          if Val.has_type_dec v (mreg_type r) then
            match mreg_part r with
            | PFull r => EOne (set_full (m (R r)) v)
            | PHigh s => EOne (set_high (m (R s)) v)
            | PLow s  => EOne (set_low  (m (R s)) v)
            end
          else
            match mreg_part r with
            | PFull r => EOne (set_full (m (R r)) Vundef)
            | PHigh s => EOne (set_high (m (R s)) Vundef)
            | PLow s  => EOne (set_low  (m (R s)) Vundef)
            end
        | S _ _ _ =>
          if Loc.eq l l' then
            EOne (Val.load_result (chunk_of_type (Loc.type l)) v)
          else
            EOne Vundef
        end.
  
  Lemma gss: forall l v m,
    get l (set l v m) = Val.load_result (chunk_of_type (Loc.type l)) v.
  Proof.
    intros. destruct l.
    - simpl. destruct (mreg_part r) eqn:P.
      + unfold get_full, set. rewrite P. apply full_is_eq in P; subst.
        rewrite pred_dec_false; auto using Loc.same_not_diff.
        destruct (Val.has_type_dec v (mreg_type r0)).
        destruct (m (R r0)). rewrite Val.load_result_same; auto.
        unfold set_full. destruct (m (R r0)).
        destruct (mreg_type r0), v; simpl in *; auto; tauto.
      + unfold get_high, set. rewrite pred_dec_false. rewrite P.
        destruct (Val.has_type_dec v (mreg_type r)).
        unfold set_high. destruct (m (R r0)).
        rewrite Val.pair_set_hi_get_hi. rewrite Val.load_result_same; auto.
        apply high_type_Tany32 in P; rewrite P in h; auto.
        unfold set_high. destruct (m (R r0)).
        rewrite Val.pair_set_hi_get_hi; simpl; auto.
        destruct (mreg_type r), v; simpl in *; auto; tauto.
        simpl. auto using subreg_not_diff, high_is_subreg.
      + unfold get_low, set. rewrite pred_dec_false. rewrite P.
        destruct (Val.has_type_dec v (mreg_type r)).
        unfold set_low. destruct (m (R r0)).
        rewrite Val.pair_set_lo_get_lo. rewrite Val.load_result_same; auto.
        apply low_type_Tany32 in P; rewrite P in h; auto.
        unfold set_low. destruct (m (R r0)).
        rewrite Val.pair_set_lo_get_lo; simpl; auto.
        destruct (mreg_type r), v; simpl in *; auto; tauto.
        simpl. auto using subreg_not_diff, low_is_subreg.
    - unfold get, set.
      rewrite pred_dec_false; auto using Loc.same_not_diff.
      rewrite dec_eq_true; auto.
  Qed.

  Lemma gss_reg: forall r v m, Val.has_type v (mreg_type r) -> get (R r) (set (R r) v m) = v.
  Proof.
    intros. rewrite gss. apply Val.load_result_same; auto.
  Qed.

  Lemma gss_typed: forall l v m, Val.has_type v (Loc.type l) -> get l (set l v m) = v.
  Proof.
    intros. rewrite gss. apply Val.load_result_same; auto.
  Qed.

  Lemma gss_untyped: forall l v m, ~ Val.has_type v (Loc.type l) -> get l (set l v m) = Vundef.
  Proof.
    intros.
    destruct l.
    - unfold get, get_full, set.
      destruct (mreg_part r) eqn:P.
      + rewrite pred_dec_false, pred_dec_false by auto using Loc.same_not_diff.
        destruct (m (R r0)); auto.
      + generalize (high_is_subreg r r0 P); intro SUB.
        rewrite pred_dec_false, pred_dec_false by (try apply subreg_not_diff; auto).
        destruct (m (R r0)); simpl; rewrite Val.pair_set_hi_get_hi; simpl; auto.
      + generalize (low_is_subreg r r0 P); intro SUB.
        rewrite pred_dec_false, pred_dec_false by (try apply subreg_not_diff; auto).
        destruct (m (R r0)); simpl; rewrite Val.pair_set_lo_get_lo; simpl; auto.
    - unfold get, get_full, set.
      rewrite pred_dec_false, dec_eq_true by auto using Loc.same_not_diff.
      destruct ty, v; simpl in *; auto; tauto.
  Qed.

  Lemma gso_reg:
    forall r s v m,
    Loc.diff (R r) (R s) ->
    get (R s) (set (R r) v m) = get (R s) m.
  Proof.
    intros. unfold get, set.
    generalize (mreg_relation_cases r s); intros [EQ | [DIFF | [SUB | SUB]]].
    - subst. apply Loc.same_not_diff in H; tauto.
    - destruct (mreg_part s) eqn:P.
      + rewrite pred_dec_true; auto.
      + assert (subreg s r0) by auto using high_is_subreg.
        generalize (subreg_part_cases s r0 H0); intros [[HI FULL] | [LO FULL]].
        generalize (diff_high_cases _ _ _ DIFF HI); intros [DIFF' | LO'].
        rewrite pred_dec_true; auto.
        rewrite pred_dec_false.
        rewrite LO'. destruct (Val.has_type_dec v (mreg_type r)).
        destruct (m (R r0)); simpl. rewrite Val.pair_set_lo_get_hi; auto.
        destruct (m (R r0)); simpl. rewrite Val.pair_set_lo_get_hi; auto.
        apply low_is_subreg in LO'. simpl. auto using subreg_not_diff.
        congruence.
      + assert (subreg s r0) by auto using low_is_subreg.
        generalize (subreg_part_cases s r0 H0); intros [[HI FULL] | [LO FULL]].
        congruence.
        generalize (diff_low_cases _ _ _ DIFF LO); intros [DIFF' | HI'].
        rewrite pred_dec_true; auto.
        rewrite pred_dec_false.
        rewrite HI'. destruct (Val.has_type_dec v (mreg_type r)).
        destruct (m (R r0)); simpl. rewrite Val.pair_set_hi_get_lo; auto.
        destruct (m (R r0)); simpl. rewrite Val.pair_set_hi_get_lo; auto.
        apply high_is_subreg in HI'. simpl. auto using subreg_not_diff.
    - apply subreg_not_diff in SUB; contradiction.
    - apply subreg_not_diff in SUB. contradict SUB. auto using diff_sym.
  Qed.

  Lemma gso: forall l v m p, Loc.diff l p -> get p (set l v m) = get p m.
  Proof.
    intros.
    destruct l, p; auto using gso_reg; unfold get, set; rewrite pred_dec_true; auto.
  Qed.

  Lemma gs_subreg_cases:
    forall r s v m,
      subreg r s ->
      Val.has_type v (mreg_type r) ->
      (mreg_part r = PHigh s /\ get (R s) (set (R r) v m) = Val.pair_set_hi (get (R s) m) v \/
       mreg_part r = PLow s  /\ get (R s) (set (R r) v m) = Val.pair_set_lo (get (R s) m) v).
  Proof.
    intros. destruct (subreg_part_cases r s H) as [[HI FULL] | [LO FULL]].
    - left. split; auto.
      unfold get, set, set_high.
      rewrite FULL, pred_dec_false, pred_dec_true, HI by (simpl; auto using subreg_not_diff).
      destruct (m (R s)); auto.
    - right. split; auto.
      unfold get, set, set_low.
      rewrite FULL, pred_dec_false, pred_dec_true, LO by (simpl; auto using subreg_not_diff).
      destruct (m (R s)); auto.
  Qed.

  Lemma gs_subreg_cases_untyped:
    forall r s v m,
    subreg r s ->
    ~ Val.has_type v (mreg_type r) ->
    (mreg_part r = PHigh s /\ get (R s) (set (R r) v m) = Val.pair_set_hi (get (R s) m) Vundef \/
     mreg_part r = PLow s  /\ get (R s) (set (R r) v m) = Val.pair_set_lo (get (R s) m) Vundef).
  Proof.
    intros. destruct (subreg_part_cases r s H) as [[HI FULL] | [LO FULL]].
    - left. split; auto.
      unfold get, set, set_high.
      rewrite FULL, pred_dec_false, pred_dec_false, HI by (simpl; auto using subreg_not_diff).
      destruct (m (R s)); auto.
    - right. split; auto.
      unfold get, set, set_low.
      rewrite FULL, pred_dec_false, pred_dec_false, LO by (simpl; auto using subreg_not_diff).
      destruct (m (R s)); auto.
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

  Lemma gus_aux_reg:
    forall r s m, get (R r) m = Vundef -> get (R r) (set (R s) Vundef m) = Vundef.
  Proof.
    intros.
    destruct (mreg_relation_cases r s) as [EQ | [DIFF | [SUB | SUB]]].
    - subst. rewrite gss. simpl. destruct (mreg_type s); auto.
    - rewrite gso; simpl; auto using diff_sym.
    - generalize (subreg_part_cases r s SUB); intros [[HI FULL] | [LO FULL]].
      + unfold get, set.
        rewrite HI, pred_dec_false, pred_dec_true; simpl; auto using same_not_diff.
        rewrite FULL. unfold set_full. destruct (m (R s)). simpl; auto.
      + unfold get, set.
        rewrite LO, pred_dec_false, pred_dec_true; simpl; auto using same_not_diff.
        rewrite FULL. unfold set_full. destruct (m (R s)). simpl; auto.
    - generalize (subreg_part_cases s r SUB); intros [[HI FULL] | [LO FULL]].
      + unfold get, set.
        rewrite FULL, pred_dec_false, pred_dec_true; simpl; auto using subreg_not_diff.
        unfold get in H. rewrite FULL in H. rewrite HI.
        destruct (m (R r)). simpl in *. subst; auto.
      + unfold get, set.
        rewrite FULL, pred_dec_false, pred_dec_true; simpl; auto using subreg_not_diff.
        unfold get in H. rewrite FULL in H. rewrite LO.
        destruct (m (R r)). simpl in *. subst; auto.
  Qed.

  Lemma gus_aux:
    forall l p m, get l m = Vundef -> get l (set p Vundef m) = Vundef.
  Proof.
    intros.
    destruct l, p; auto using gus_aux_reg.
    unfold get, set. unfold get in H.
    destruct (Loc.diff_dec (S sl0 pos0 ty0) (S sl pos ty)); auto.
    destruct (Loc.eq (S sl0 pos0 ty0) (S sl pos ty)); auto.
    simpl. destruct (chunk_of_type ty0); auto.
  Qed.

  Lemma gus: forall ll l m, In l ll -> get l (undef ll m) = Vundef.
  Proof.
    assert (P: forall ll l m, get l m = Vundef -> get l (undef ll m) = Vundef).
    { induction ll; simpl; intros. auto. apply IHll.
      auto using gus_aux. }
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


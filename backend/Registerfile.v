(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Gergö Barany, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import OrderedType.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import Ordered.
Require Import AST.
Require Import Values.
Require Import Memdata.
Require Import Memory.
Require Export Machregs.

Open Scope Z_scope.

(** * General requirements for machine registers *)

Lemma mreg_type_cases: forall r, mreg_type r = Tany32 \/ mreg_type r = Tany64.
Proof.
  destruct r; simpl; auto.
Qed.

(** * Facts about register aliasing *)

(** Every architecture defines functions [subregs] and [superregs]
  associating each register with an optional pair of subregisters and an
  optional superregister. It must also define a type [part] and a function
  [mreg_part] mapping subregisters of some register [r] to [PLow r] or
  [PHigh r] as appropriate, and every "full" register [r] (that is not
  a subregister of anything) to [PFull r].

  Based on these definitions, we formulate general information about
  register aliasing.

  We define the relation [subreg r s] as meaning that [r] is strictly
  a subregister of [s], i.e., [subreg] is irreflexive; similarly for
  [superreg]. Registers are either the same ([mreg_eq]), non-overlapping
  ([mreg_diff]), or overlapping ([mreg_overlap]). Registers overlap iff they
  are in a subregister relationship.

  A register's [containing_reg] is its superregister, if any; otherwise, it
  is the register itself.

  We assume that all registers are of size 32 or 64 bit. It follows that
  a superregister is 64 bits, with exactly two 32-bit subregisters. It also
  follows that subregisters cannot have further subregisters. *)

Section REG_ALIASING.

Definition subreg (r s: mreg): Prop :=
  match subregs s with
  | Some (lo, hi) => r = lo \/ r = hi
  | None => False
  end.

Definition subreg_dec (r s: mreg): { subreg r s } + { ~ subreg r s }.
Proof.
  intros. unfold subreg. destruct (subregs s) eqn:S; auto.
  destruct p as [lo hi]. destruct (mreg_eq r lo); auto. destruct (mreg_eq r hi); tauto.
Defined.

Lemma subreg_irrefl:
  forall r, ~ subreg r r.
Proof.
  intros. destruct r; auto; unfold subreg; simpl; intuition congruence.
Qed.

Definition subreg_list r :=
  match subregs r with
  | Some (lo, hi) => lo :: hi :: nil
  | None => nil
  end.

Definition superreg (r s: mreg): Prop :=
  match superregs s with
  | Some s => r = s
  | None => False
  end.

Definition superreg_dec (r s: mreg): { superreg r s } + { ~ superreg r s }.
Proof.
  intros. unfold superreg. destruct (superregs s) eqn:S; auto.
  destruct (mreg_eq r m); auto.
Defined.

Definition superreg_list r :=
  match superregs r with
  | Some s => s :: nil
  | None => nil
  end.

Definition containing_reg (r: mreg): mreg :=
  match superregs r with
  | Some s => s
  | None => r
  end.

Definition mreg_overlap (r s: mreg): Prop :=
  subreg r s \/ subreg s r.

Definition mreg_overlap_dec (r s: mreg): { mreg_overlap r s } + { ~ mreg_overlap r s }.
Proof.
  unfold mreg_overlap.
  destruct (subreg_dec r s); auto.
  destruct (subreg_dec s r); auto.
  tauto.
Defined.

Lemma mreg_overlap_sym: forall r s, mreg_overlap r s -> mreg_overlap s r.
Proof.
  intros. unfold mreg_overlap in *. tauto.
Qed.

Lemma same_not_overlap:
  forall r, ~ mreg_overlap r r.
Proof.
  unfold mreg_overlap, not; intros.
  destruct H; apply subreg_irrefl in H; auto.
Qed.

Definition mreg_diff (r s: mreg): Prop :=
  r <> s /\ ~ mreg_overlap r s.

Lemma same_not_diff:
  forall r, ~ mreg_diff r r.
Proof.
  unfold not, mreg_diff; intros.
  inv H. contradict H0. reflexivity.
Qed.

Lemma not_same_not_diff_overlap:
  forall r s, r <> s -> ~ mreg_diff r s -> mreg_overlap r s.
Proof.
  unfold mreg_diff; intros.
  destruct (mreg_overlap_dec r s); auto.
  contradict H0; auto.
Qed.

Lemma not_same_not_overlap_diff:
  forall r s, r <> s -> ~ mreg_overlap r s -> mreg_diff r s.
Proof.
  unfold mreg_diff; auto.
Qed.

Lemma subreg_not_diff:
  forall r s,
  subreg r s ->
  ~ mreg_diff r s.
Proof.
  intros. unfold mreg_diff, mreg_overlap. intuition auto.
Qed.

Lemma superreg_not_diff:
  forall r s,
  subreg r s ->
  ~ mreg_diff s r.
Proof.
  intros. unfold mreg_diff, mreg_overlap. intuition auto.
Qed.

Lemma diff_not_eq:
  forall r1 r2,
  mreg_diff r1 r2 -> r1 <> r2.
Proof.
  unfold mreg_diff; tauto.
Qed.

Lemma diff_not_overlap:
  forall r1 r2,
  mreg_diff r1 r2 -> ~ mreg_overlap r1 r2.
Proof.
  unfold mreg_diff; tauto.
Qed.

Lemma diff_sym:
  forall r1 r2,
  mreg_diff r1 r2 -> mreg_diff r2 r1.
Proof.
  unfold mreg_diff; intros.
  split.
  - apply not_eq_sym. tauto.
  - unfold not; intro. apply mreg_overlap_sym in H0. tauto.
Qed.

Definition mreg_diff_dec (r1 r2: mreg): { mreg_diff r1 r2 } + { ~ mreg_diff r1 r2 }.
Proof.
  unfold mreg_diff.
  destruct (mreg_eq r1 r2); try tauto.
  destruct (mreg_overlap_dec r1 r2); tauto.
Defined.

Lemma subreg_size:
  forall r s,
  subreg r s ->
  AST.typesize (mreg_type r) = 4.
Proof.
  intros. destruct s; try inv H; auto.
Qed.

Lemma superreg_type:
  forall r s,
  subreg r s -> mreg_type s = Tany64.
Proof.
  intros. destruct s; try inv H; auto.
Qed.

Lemma superreg_size:
  forall r s,
  subreg r s ->
  AST.typesize (mreg_type s) = 8.
Proof.
  intros. destruct s; try inv H; auto.
Qed.

(* Properties of the "containing" register. *)

Lemma containing_reg_charact:
  forall r, r = containing_reg r \/ subreg r (containing_reg r).
Proof.
  intros. destruct r; simpl; auto; unfold subreg, containing_reg; simpl; auto.
Qed.

Lemma subreg_of_containing_reg:
  forall r s, subreg r s -> s = containing_reg r.
Proof.
  intros. unfold subreg, containing_reg in *.
  destruct s; simpl in H; try tauto; destruct H; subst r; simpl; auto.
Qed.

Lemma containing_reg_idempotent:
  forall r, containing_reg (containing_reg r) = containing_reg r.
Proof.
  destruct r; simpl; auto.
Qed.

Lemma overlap_containing_reg:
  forall r s, mreg_overlap r s -> containing_reg r = containing_reg s.
Proof.
  intros. unfold mreg_overlap in H. destruct H as [SUB | SUB].
  apply subreg_of_containing_reg in SUB. rewrite SUB, containing_reg_idempotent; auto.
  apply subreg_of_containing_reg in SUB. rewrite SUB, containing_reg_idempotent; auto.
Qed.

Lemma containing_reg_diff:
  forall r1 r2, containing_reg r1 <> containing_reg r2 -> mreg_diff r1 r2.
Proof.
  intros. unfold mreg_diff; split.
  - congruence.
  - contradict H. apply overlap_containing_reg; auto.
Qed.

(* The relationship between register parts and the other definitions. *)

Lemma superreg_full:
  forall r s,
  subreg r s ->
  mreg_part s = PFull s.
Proof.
  intros. unfold subreg in H.
  destruct s; simpl in H; try contradiction; auto.
Qed.

Lemma subreg_low_or_high:
  forall r s,
  subreg r s ->
  mreg_part r = PLow s \/ mreg_part r = PHigh s.
Proof.
  intros. unfold subreg in H.
  destruct s; simpl in H; try contradiction; destruct H; subst; auto.
Qed.

Lemma subreg_cases:
  forall r s,
  subreg r s -> mreg_part s = PFull s /\ (mreg_part r = PLow s \/ mreg_part r = PHigh s).
Proof.
  intros. split; eauto using superreg_full, subreg_low_or_high.
Qed.

Lemma mreg_relation_cases:
  forall r s,
  r = s \/
  (subreg r s /\ mreg_part s = PFull s /\ (mreg_part r = PLow s \/ mreg_part r = PHigh s)) \/
  (subreg s r /\ mreg_part r = PFull r /\ (mreg_part s = PLow r \/ mreg_part s = PHigh r)) \/
  mreg_diff r s.
Proof.
  intros.
  destruct (mreg_eq r s); auto.
  destruct (subreg_dec r s).
    right. left. repeat split; eauto using superreg_full, subreg_low_or_high.
  destruct (subreg_dec s r).
    right. right. left. repeat split; eauto using superreg_full, subreg_low_or_high.
  right. right. right. unfold mreg_diff, mreg_overlap. tauto.
Qed.

Lemma mreg_relation_cases_simple:
  forall r s,
  r = s \/ subreg r s \/ subreg s r \/ mreg_diff r s.
Proof.
  intros. destruct (mreg_relation_cases r s); tauto.
Qed.

(* Relations between registers should be decidable by computation. *)

Program Instance Decidable_mreg_diff: forall (x y: mreg), Decidable (mreg_diff x y) := {
  Decidable_witness := proj_sumbool (mreg_diff_dec x y)
}.
Next Obligation.
  split; intros. InvBooleans; auto. apply pred_dec_true; auto.
Defined.

Instance Finite_mreg_pair: Finite (mreg * mreg) := Finite_pair mreg mreg Finite_mreg Finite_mreg.

End REG_ALIASING.

(* Make it simple to apply [mreg_relation_cases]. *)

Ltac compare_mregs_base do_rewrite r s :=
  let EQ := fresh "EQ" in
  let SUB := fresh "SUB" in
  let FULL := fresh "FULL" in
  let LO := fresh "LO" in
  let HI := fresh "HI" in
  let DIFF := fresh "DIFF" in
  destruct (mreg_relation_cases r s) as [EQ | [[SUB [FULL [LO | HI]]] | [[SUB [FULL [LO | HI]]] | DIFF]]];
  match do_rewrite with
  | true =>
    match goal with
    | [ EQ: r = s |- _ ] =>
      subst r; destruct (mreg_part s)
    | _ => idtac
    end;
    try rewrite !FULL in *; try rewrite !LO in *; try rewrite !HI in *; auto
  | false => idtac
  end.

Ltac compare_mregs r s := compare_mregs_base false r s.

Ltac xcompare_mregs r s := compare_mregs_base true r s.

(* [decide_goal] isn't powerful enough to some of the goals of the form [mreg_diff r s -> P]
  below. This tactic helps. *)
Ltac decide_mreg_diff_goal :=
  refine
    (Decidable_sound _
      (Decidable_forall mreg Finite_mreg _
        (fun r: mreg =>
          Decidable_forall mreg Finite_mreg _
            (fun s: mreg =>
               Decidable_implies (mreg_diff r s) _
               (Decidable_mreg_diff r s)
               _
            ))) _); reflexivity.

Module OrderedMreg <: OrderedType.
  Definition t := mreg.

  Definition eq (x y: t) := x = y.
  Lemma eq_refl: forall x: t, eq x x.
  Proof (@eq_refl t).
  Lemma eq_sym: forall x y: t, eq x y -> eq y x.
  Proof (@eq_sym t).
  Lemma eq_trans: forall x y z: t, eq x y -> eq y z -> eq x z.
  Proof (@eq_trans t).
  Definition eq_dec := mreg_eq.

  Open Scope positive_scope.

  Definition lt (x y: t) :=
    IndexedMreg.index x < IndexedMreg.index y.

  Lemma lt_trans: forall x y z: t, lt x y -> lt y z -> lt x z.
  Proof.
    intros. eapply Pos.lt_trans; eauto.
  Qed.

  Lemma lt_not_eq: forall x y: t, lt x y -> x <> y.
  Proof.
    intros. apply Plt_ne in H. contradict H; congruence.
  Qed.

  Lemma compare: forall x y: t, Compare lt eq x y.
  Proof.
    intros. destruct (OrderedPositive.compare (IndexedMreg.index x) (IndexedMreg.index y)).
    - apply LT. red. auto.
    - apply EQ. red. auto using IndexedMreg.index_inj.
    - apply GT. red. auto.
  Qed.

  Instance Decidable_lt (x y: t): Decidable (lt x y) :=
    Decidable_lt_positive (IndexedMreg.index x) (IndexedMreg.index y).

  (** Define intervals of registers as follows:
      - A register [R] that is not involved in register pairing maps to the
        interval [(R, R)], i.e., it is its own upper and lower bound.
      - A paired register [D = S_low:S_high] maps to the interval
        [(S_low, S_high)]. Its two component registers map to the intervals
        [(S_low, D)] and [(D, S_high)], respectively.
      The [Machregs] module must define [diff_low_bound] and [diff_high_bound]
      functions conforming to this specification.
   *)

  Lemma low_bound_lt_or_eq: forall r: t, lt (diff_low_bound r) r \/ diff_low_bound r = r.
  Proof.
    intros. destruct r; compute; try tauto.
  Qed.

  Lemma lt_low_bound_not_subreg:
    forall r p, lt p (diff_low_bound r) -> ~ subreg r p.
  Proof.
    intros.
    destruct p; compute; auto;
      intros; decompose [or] H0; subst; compute in H; congruence.
  Qed.

  Lemma lt_low_bound_not_subreg':
    forall r p, lt p (diff_low_bound r) -> ~ subreg p r.
  Proof.
    intros.
    destruct r; compute; auto;
      intros; decompose [or] H0; subst; compute in H; congruence.
  Qed.

  Lemma lt_or_eq_high_bound: forall r: t, lt r (diff_high_bound r) \/ r = diff_high_bound r.
  Proof.
    intros. destruct r; compute; tauto.
  Qed.

  Lemma high_bound_lt_not_subreg:
    forall r p, lt (diff_high_bound r) p -> ~ subreg r p.
  Proof.
    intros.
    destruct p; compute; auto;
      intros; decompose [or] H0; subst; compute in H; congruence.
  Qed.

  Lemma high_bound_lt_not_subreg':
    forall r p, lt (diff_high_bound r) p -> ~ subreg p r.
  Proof.
    intros.
    destruct r; compute; auto;
      intros; decompose [or] H0; subst; compute in H; congruence.
  Qed.

  Definition diff_low_bound r := Machregs.diff_low_bound r.
  Definition diff_high_bound r := Machregs.diff_high_bound r.

  Lemma outside_interval_diff:
    forall r r', lt r' (diff_low_bound r) \/ lt (diff_high_bound r) r' -> mreg_diff r r'.
  Proof.
    unfold diff_low_bound, diff_high_bound. intros r r' [A | B].
    - split.
      + generalize (low_bound_lt_or_eq r); intros [C | D].
        * eapply not_eq_sym, lt_not_eq, lt_trans; eauto.
        * rewrite D in A. apply not_eq_sym, lt_not_eq; auto.
      + generalize (lt_low_bound_not_subreg r r' A); intros.
        generalize (lt_low_bound_not_subreg' r r' A); intros.
        unfold mreg_overlap. intuition auto.
    - split.
      + generalize (lt_or_eq_high_bound r); intros [C | D].
        * eapply lt_not_eq, lt_trans; eauto.
        * rewrite <- D in B. apply lt_not_eq; auto.
      + generalize (high_bound_lt_not_subreg r r' B); intros.
        generalize (high_bound_lt_not_subreg' r r' B); intros.
        unfold mreg_overlap. intuition auto.
  Qed.

  Lemma diff_outside_interval:
    forall r r',
    mreg_diff r r' -> lt r' (diff_low_bound r) \/ lt (diff_high_bound r) r'.
  Proof.
    decide_mreg_diff_goal.
  Qed.

End OrderedMreg.

(** * Representation of the register file *)

(** The [Regfile] module defines mappings from registers to values. The register
  file is represented as a kind of memory block containing bytes addressed using
  register numbers.
  The register numbers are taken from [IndexedMreg], interpreted as words and
  scaled internally to bytes. The indices of adjacent 64-bit registers must
  therefore differ by at least 2. *)

Module Regfile.

  Definition t := ZMap.t memval.

  Definition init := ZMap.init Undef.

  (* A register's address: The index of its first byte. *)
  Definition addr (r: mreg) : Z :=
    let base_addr reg := Zpos (IndexedMreg.index reg) * 4 in
    match mreg_part r with
      | PFull r => base_addr r
      | PLow s  => base_addr s
      | PHigh s => base_addr s + 4
    end.

  Remark addr_pos: forall r, addr r > 0.
  Proof.
    intros. unfold addr. destruct (mreg_part r); xomega.
  Qed.

  (* The address one byte past the end of register [r]. The next nonoverlapping
     register may start here. *)
  Definition next_addr (r: mreg) : Z := addr r + AST.typesize (mreg_type r).

  Lemma outside_interval_neq:
    forall r s, next_addr r <= addr s \/ next_addr s <= addr r -> r <> s.
  Proof.
    intros. destruct H; unfold next_addr in H.
    generalize (AST.typesize_pos (mreg_type r)); intros. contradict H. subst. omega.
    generalize (AST.typesize_pos (mreg_type s)); intros. contradict H. subst. omega.
  Qed.

  Lemma outside_interval_diff:
    forall r s, next_addr r <= addr s \/ next_addr s <= addr r -> mreg_diff r s.
  Proof.
    intros. destruct H; unfold next_addr, addr in H.
    generalize (AST.typesize_pos (mreg_type r)); intros.
    xcompare_mregs r s; try omega.
    apply superreg_size in SUB; omega.
    generalize (AST.typesize_pos (mreg_type s)); intros.
    xcompare_mregs s r; try omega.
    apply superreg_size in SUB; omega.
    auto using diff_sym.
  Qed.

  Lemma diff_outside_interval:
    forall r s, mreg_diff r s -> next_addr r <= addr s \/ next_addr s <= addr r.
  Proof.
    decide_mreg_diff_goal.
  Qed.

  Definition chunk_of_mreg (r: mreg) : memory_chunk :=
    chunk_of_type (mreg_type r).

  Lemma chunk_length:
    forall r v,
    Z.to_nat (AST.typesize (mreg_type r)) = length (encode_val (chunk_of_mreg r) v).
  Proof.
    intros. rewrite encode_val_length.
    unfold chunk_of_mreg. destruct (mreg_type r); auto.
  Qed.

  Definition get_bytes (r: mreg) (rf: t) : list memval :=
    Mem.getN (Z.to_nat (AST.typesize (mreg_type r))) (addr r) rf.

  Definition get (r: mreg) (rf: t) : val :=
    decode_val (chunk_of_mreg r) (get_bytes r rf).

  Definition set_bytes (r: mreg) (bytes: list memval) (rf: t) : t :=
    Mem.setN bytes (addr r) rf.

  Definition set (r: mreg) (v: val) (rf: t) : t :=
    set_bytes r (encode_val (chunk_of_mreg r) v) rf.

  (* Update the [old] register file by choosing the values for the registers in
     [rs] from [new]. *)
  Fixpoint override (rs: list mreg) (new old: t) : t :=
    match rs with
    | nil => old
    | r :: rs' => set r (get r new) (override rs' new old)
    end.

  Fixpoint undef_regs (rs: list mreg) (rf: t) : t :=
    match rs with
    | nil => rf
    | r :: rs => set r Vundef (undef_regs rs rf)
    end.

  Lemma gss:
    forall r v rf,
    get r (set r v rf) = Val.load_result (chunk_of_mreg r) v.
  Proof.
    intros. unfold get, set, get_bytes, set_bytes.
    erewrite chunk_length. rewrite Mem.getN_setN_same.
    erewrite <- decode_encode_val_similar; eauto.
    eapply decode_encode_val_general.
  Qed.

  Lemma gso:
    forall r s v rf,
    mreg_diff r s ->
    get r (set s v rf) = get r rf.
  Proof.
    intros. unfold get, set, get_bytes, set_bytes.
    rewrite Mem.getN_setN_outside; auto.
    rewrite <- chunk_length.
    generalize (AST.typesize_pos (mreg_type s)), (AST.typesize_pos (mreg_type r)); intros.
    apply diff_outside_interval in H. unfold next_addr in H.
    rewrite !Z2Nat.id; omega.
  Qed.

  Lemma gu_subreg:
    forall r s v rf,
    subreg r s ->
    get r (set s v rf) = Vundef.
  Proof.
    intros. unfold get, set, get_bytes, set_bytes, addr.
    generalize (subreg_cases r s H); intros [FULL [LO | HI]]; rewrite FULL.
    - rewrite LO.
      unfold chunk_of_mreg.
      rewrite (subreg_size r s H), (superreg_type r s H).
      rewrite Mem.getN_setN_prefix.

      destruct (chunk_of_type (mreg_type r)); simpl; auto; destruct v; simpl; auto;
      unfold decode_val, proj_bytes; destruct Archi.ptr64; simpl; auto; rewrite !andb_false_r; simpl; auto.

      destruct v; simpl; auto.
    - rewrite HI.
      unfold chunk_of_mreg.
      rewrite (subreg_size r s H), (superreg_type r s H).
      replace 4 with (Z.of_nat (Z.to_nat 4)) at 3; auto.
      rewrite Mem.getN_setN_suffix.

      destruct (chunk_of_type (mreg_type r)); simpl; auto; destruct v; simpl; auto;
      unfold decode_val, proj_bytes; destruct Archi.ptr64; simpl; auto; rewrite !andb_false_r; simpl; auto.

      destruct v; simpl; auto.
  Qed.

  Lemma decode_undef_suffix:
    forall a b c d,
    decode_val Many64 (a :: b :: c :: d :: Undef :: Undef :: Undef :: Undef :: nil) = Vundef.
  Proof.
    intros.
    set (undefs := Undef :: Undef :: Undef :: Undef :: nil).
    change (a :: b :: c :: d :: undefs) with ((a :: b :: c :: d :: nil) ++ undefs).
    unfold decode_val. rewrite proj_bytes_append.
    simpl (proj_bytes undefs).
    destruct a, b, c, d; simpl; auto; rewrite !andb_false_r; auto.
  Qed.

  Lemma gu_superreg:
    forall r s v rf,
    subreg r s ->
    get s (set r v rf) = Vundef.
  Proof.
    intros. unfold get, set, get_bytes, set_bytes, addr.
    generalize (subreg_cases r s H); intros [FULL [LO | HI]]; rewrite FULL.
    - rewrite LO.
      unfold chunk_of_mreg.
      rewrite (superreg_type r s H).
      simpl typesize.
      change (Z.to_nat 8) with (4 + 4)%nat.
      rewrite Mem.getN_concat.
      simpl chunk_of_type.
      replace (4%nat) with (length (encode_val (chunk_of_type (mreg_type r)) v)).
      rewrite Mem.getN_setN_same.
      rewrite Mem.getN_setN_outside.

      unfold decode_val.
      replace (length (encode_val (chunk_of_type (mreg_type r)) v)) with 4%nat.
      apply subreg_size in H.
      destruct (mreg_type r); try inv H.

      destruct v; simpl; auto.
      rewrite proj_value_encode_int_app_l; auto.
      destruct (proj_bytes _); auto.
      destruct Archi.ptr64. simpl proj_value. destruct (proj_bytes _); auto.
      unfold inj_value. simpl inj_value_rec.
      erewrite proj_value_diff_q with (q := Q32).
      destruct (proj_bytes _); auto.
      congruence.
      apply in_app. left. eapply in_eq.

      destruct v; simpl; auto.
      rewrite proj_value_encode_int_app_l; auto.
      destruct (proj_bytes _); auto.

      destruct v; simpl; rewrite !andb_false_r; auto.
      apply subreg_size in H.
      destruct (mreg_type r); simpl; try inv H; auto.
      destruct v; simpl; auto.
      rewrite length_inj_bytes, encode_int_length; auto.
      destruct v; simpl; auto.
      rewrite length_inj_bytes, encode_int_length; auto.
      destruct v; simpl; auto.
      omega.
      apply subreg_size in H.
      destruct (mreg_type r); simpl; try inv H; auto.
      destruct v; simpl; auto.
      rewrite length_inj_bytes, encode_int_length; auto.
      destruct v; simpl; auto.
      rewrite length_inj_bytes, encode_int_length; auto.
      destruct v; simpl; auto.

    - rewrite HI.
      unfold chunk_of_mreg.
      rewrite (superreg_type r s H).
      simpl typesize.
      change (Z.to_nat 8) with (4 + 4)%nat.
      rewrite Mem.getN_concat.
      simpl chunk_of_type.
      rewrite Mem.getN_setN_outside.

      replace (Z.pos (IndexedMreg.index s) * 4 + Z.of_nat 4) with (addr r).
      replace (Z.pos (IndexedMreg.index s) * 4 + 4) with (addr r).
      replace (4%nat) with (length (encode_val (chunk_of_type (mreg_type r)) v)).
      rewrite Mem.getN_setN_same.
      apply subreg_size in H.
      destruct (mreg_type r); try inversion H; simpl encode_val.

      unfold decode_val.
      destruct v; simpl encode_val; try apply decode_undef_suffix.
      rewrite proj_value_encode_int_app_r. destruct (proj_bytes _); auto. auto.

      destruct Archi.ptr64. apply decode_undef_suffix.
      unfold inj_value. simpl inj_value_rec.
      erewrite proj_value_diff_q with (q := Q32).
      destruct (proj_bytes _); auto.
      congruence.
      apply in_app. right. eapply in_eq.

      destruct v; simpl; try apply decode_undef_suffix.
      unfold decode_val.
      rewrite proj_value_encode_int_app_r. destruct (proj_bytes _); auto. auto.

      unfold decode_val.
      erewrite proj_value_diff_q with (q := Q32).
      destruct (proj_bytes _); auto.
      congruence.
      apply in_app. right. destruct v; simpl; auto.

      apply subreg_size in H.
      destruct (mreg_type r); simpl; try inv H; auto.
      destruct v; simpl; auto.
      rewrite length_inj_bytes, encode_int_length; auto.
      destruct v; simpl; auto.
      rewrite length_inj_bytes, encode_int_length; auto.
      destruct v; simpl; auto.

      unfold addr. rewrite HI; congruence.
      unfold addr. rewrite HI. f_equal.
      left.
      simpl. omega.
  Qed.

  Lemma gu_overlap:
    forall r s v rf,
    mreg_overlap r s ->
    get r (set s v rf) = Vundef.
  Proof.
    intros.
    destruct (mreg_relation_cases_simple r s) as [SAME | [SUB | [SUB | DIFF]]].
    - subst. apply same_not_overlap in H; tauto.
    - apply gu_subreg; auto.
    - apply gu_superreg; auto.
    - apply diff_not_overlap in DIFF; tauto.
  Qed.

  Lemma gss_bytes:
    forall r bs rf,
    let sz := Z.to_nat (AST.typesize (mreg_type r)) in
    length bs = sz ->
    get_bytes r (set_bytes r bs rf) = firstn sz bs.
  Proof.
    intros. unfold get_bytes, set_bytes.
    subst sz. rewrite <- H. rewrite Mem.getN_setN_same.
    rewrite firstn_all; auto.
  Qed.

  Lemma gso_bytes:
    forall r s bs rf,
    let sz := Z.to_nat (AST.typesize (mreg_type r)) in
    length bs = sz ->
    mreg_diff r s ->
    get_bytes s (set_bytes r bs rf) = get_bytes s rf.
  Proof.
    intros. unfold get_bytes, set_bytes.
    rewrite Mem.getN_setN_outside; auto.
    rewrite H. subst sz.
    apply diff_outside_interval in H0. unfold next_addr in H0.
    rewrite !Z2Nat.id. omega.
    generalize (AST.typesize_pos (mreg_type r)); omega.
    generalize (AST.typesize_pos (mreg_type s)); omega.
  Qed.

  (*
  Lemma override_in:
    forall rs r new old,
    In r rs -> get r (override rs new old) = get r new.
  Proof.
    intros. induction rs; try contradiction.
    destruct (mreg_eq r a).
    - subst; simpl; rewrite gss.
      unfold chunk_of_mreg. rewrite Val.load_result_same; auto.
      unfold get. rewrite <- type_of_chunk_of_type.
      apply decode_val_type.
    - inversion H; try congruence.
      simpl; rewrite gso; auto.
  Qed.

  Lemma override_notin:
    forall r rs new old,
    ~ In r rs -> get r (override rs new old) = get r old.
  Proof.
    intros. induction rs; auto.
    apply not_in_cons in H. simpl. rewrite gso; intuition auto.
  Qed.
*)

End Regfile.

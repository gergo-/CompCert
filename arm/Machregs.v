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

Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Ordered.
Require Import OrderedType.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers ([Rxx]).
- Single- and double-precision floating-point registers that can be allocated to
  RTL pseudo-registers ([Sxx] and [Dx]). We model the subregister relationship
  between these registers.

  The type [mreg] does not include reserved machine registers
  such as the stack pointer, the link register, and the condition codes. *)

Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | R0: mreg  | R1: mreg  | R2: mreg  | R3: mreg
  | R4: mreg  | R5: mreg  | R6: mreg  | R7: mreg
  | R8: mreg  | R9: mreg  | R10: mreg | R11: mreg
  | R12: mreg
  (** Allocatable single-precision float regs *)
  | S0: mreg  | S1: mreg  | S2: mreg  | S3: mreg
  | S4: mreg  | S5: mreg  | S6: mreg  | S7: mreg
  | S8: mreg  | S9: mreg  | S10: mreg | S11: mreg
  | S12: mreg | S13: mreg | S14: mreg | S15: mreg
  | S16: mreg | S17: mreg | S18: mreg | S19: mreg
  | S20: mreg | S21: mreg | S22: mreg | S23: mreg
  | S24: mreg | S25: mreg | S26: mreg | S27: mreg
  | S28: mreg | S29: mreg | S30: mreg | S31: mreg
  (** Allocatable double-precision float regs *)
  | D0: mreg  | D1: mreg  | D2: mreg  | D3: mreg
  | D4: mreg  | D5: mreg  | D6: mreg  | D7: mreg
  | D8: mreg  | D9: mreg  | D10: mreg | D11: mreg
  | D12: mreg | D13: mreg | D14: mreg | D15: mreg.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
     R0  :: R1  :: R2  :: R3 :: R4  :: R5  :: R6  :: R7
  :: R8  :: R9  :: R10 :: R11 :: R12
  :: S0  :: S1  :: S2  :: S3  :: S4  :: S5  :: S6  :: S7
  :: S8  :: S9  :: S10 :: S11 :: S12 :: S13 :: S14 :: S15
  :: S16 :: S17 :: S18 :: S19 :: S20 :: S21 :: S22 :: S23
  :: S24 :: S25 :: S26 :: S27 :: S28 :: S29 :: S30 :: S31
  :: D0  :: D1  :: D2  :: D3  :: D4  :: D5  :: D6  :: D7
  :: D8  :: D9  :: D10 :: D11 :: D12 :: D13 :: D14 :: D15 :: nil.

Lemma all_mregs_complete:
  forall (r: mreg), In r all_mregs.
Proof.
  assert (forall r, proj_sumbool (In_dec mreg_eq r all_mregs) = true) by (destruct r; reflexivity).
  intros. specialize (H r). InvBooleans. auto.
Qed.

Instance Decidable_eq_mreg : forall (x y: mreg), Decidable (eq x y) := Decidable_eq mreg_eq.

Instance Finite_mreg : Finite mreg := {
  Finite_elements := all_mregs;
  Finite_elements_spec := all_mregs_complete
}.

Definition mreg_type (r: mreg): typ :=
  match r with
  | R0  | R1  | R2  | R3   | R4  | R5  | R6  | R7
  | R8  | R9  | R10 | R11  | R12 => Tany32
  | S0  | S1  | S2  | S3  | S4  | S5  | S6  | S7
  | S8  | S9  | S10 | S11 | S12 | S13 | S14 | S15
  | S16 | S17 | S18 | S19 | S20 | S21 | S22 | S23
  | S24 | S25 | S26 | S27 | S28 | S29 | S30 | S31 => Tsingle
  | D0  | D1  | D2  | D3  | D4  | D5  | D6  | D7
  | D8  | D9  | D10 | D11 | D12 | D13 | D14 | D15 => Tany64
  end.

Definition subregs (r: mreg): option (mreg * mreg) :=
  match r with
  | D0  => Some (S0,  S1)
  | D1  => Some (S2,  S3)
  | D2  => Some (S4,  S5)
  | D3  => Some (S6,  S7)
  | D4  => Some (S8,  S9)
  | D5  => Some (S10, S11)
  | D6  => Some (S12, S13)
  | D7  => Some (S14, S15)
  | D8  => Some (S16, S17)
  | D9  => Some (S18, S19)
  | D10 => Some (S20, S21)
  | D11 => Some (S22, S23)
  | D12 => Some (S24, S25)
  | D13 => Some (S26, S27)
  | D14 => Some (S28, S29)
  | D15 => Some (S30, S31)
  | _ => None
  end.

Definition subreg (r1 r2: mreg) :=
  match subregs r2 with
  | Some (lo, hi) => r1 = lo \/ r1 = hi
  | None => False
  end.

Definition superregs (r: mreg): option mreg :=
  match r with
  | S0  | S1  => Some D0
  | S2  | S3  => Some D1
  | S4  | S5  => Some D2
  | S6  | S7  => Some D3
  | S8  | S9  => Some D4
  | S10 | S11 => Some D5
  | S12 | S13 => Some D6
  | S14 | S15 => Some D7
  | S16 | S17 => Some D8
  | S18 | S19 => Some D9
  | S20 | S21 => Some D10
  | S22 | S23 => Some D11
  | S24 | S25 => Some D12
  | S26 | S27 => Some D13
  | S28 | S29 => Some D14
  | S30 | S31 => Some D15
  | _ => None
  end.

Definition superreg (r1 r2: mreg) :=
  match superregs r2 with
  | Some s => r1 = s
  | None => False
  end.

(*
Ltac subreg_inversion :=
  match goal with
  | [ H: False |- _ ] => inversion H
  | [ H: ?x = ?y \/ _ |- _ ] =>
    let H0 := fresh "H" in let H1 := fresh "H" in
      inversion H as [H0 | H1]; clear H; try inversion H0; subreg_inversion
  end.
*)

Definition subreg_list r :=
  match subregs r with
  | Some (lo, hi) => lo :: hi :: nil
  | None => nil
  end.

Definition superreg_list r :=
  match superregs r with
  | Some s => s :: nil
  | None => nil
  end.

Section REG_PARTS.

(** Accessing parts of registers. *)

Inductive part :=
  | PFull (r: mreg)
  | PHigh (r: mreg)
  | PLow (r: mreg).

Definition mreg_part (r: mreg): part :=
  match r with
  | S0  => PLow D0  | S1  => PHigh D0
  | S2  => PLow D1  | S3  => PHigh D1
  | S4  => PLow D2  | S5  => PHigh D2
  | S6  => PLow D3  | S7  => PHigh D3
  | S8  => PLow D4  | S9  => PHigh D4
  | S10 => PLow D5  | S11 => PHigh D5
  | S12 => PLow D6  | S13 => PHigh D6
  | S14 => PLow D7  | S15 => PHigh D7
  | S16 => PLow D8  | S17 => PHigh D8
  | S18 => PLow D9  | S19 => PHigh D9
  | S20 => PLow D10 | S21 => PHigh D10
  | S22 => PLow D11 | S23 => PHigh D11
  | S24 => PLow D12 | S25 => PHigh D12
  | S26 => PLow D13 | S27 => PHigh D13
  | S28 => PLow D14 | S29 => PHigh D14
  | S30 => PLow D15 | S31 => PHigh D15
  | r   => PFull r
  end.

Definition containing_reg (r: mreg): mreg :=
  match mreg_part r with
  | PFull s | PHigh s | PLow s => s
  end.

Lemma high_is_subreg: forall r s, mreg_part r = PHigh s -> subreg r s.
Proof.
  intros. unfold subreg. destruct r; inversion H; simpl; auto.
Qed.

Lemma low_is_subreg: forall r s, mreg_part r = PLow s -> subreg r s.
Proof.
  intros. unfold subreg. destruct r; inversion H; simpl; auto.
Qed.

Lemma full_not_subreg:
  forall r, mreg_part r = PFull r -> superregs r = None.
Proof.
  intros. destruct r; compute in H; inversion H; auto.
Qed.

Lemma full_is_eq:
  forall r s, mreg_part r = PFull s -> r = s.
Proof.
  intros. destruct r; compute in H; inversion H; auto.
Qed.

(* TODO: much more facts here *)

End REG_PARTS.

Section REG_ALIASING.

(** Facts about register aliasing. *)

Definition subreg_dec (r1 r2: mreg): { subreg r1 r2 } + { ~ subreg r1 r2 }.
Proof.
  unfold subreg.
  destruct (subregs r2) eqn:S.
  destruct p as [lo hi].
  destruct (mreg_eq r1 lo); auto. destruct (mreg_eq r1 hi); tauto.
  auto.
Defined.

Definition superreg_dec (r1 r2: mreg): { superreg r1 r2 } + { ~ superreg r1 r2 }.
Proof.
  unfold superreg.
  destruct (superregs r2) eqn:S. destruct (mreg_eq r1 m); auto. auto.
Defined.

Lemma subregs_or_superregs:
  forall r, subregs r = None \/ superregs r = None.
Proof.
  intros. destruct r; auto.
Qed.

Lemma subreg_superreg:
  forall r1 r2, subreg r1 r2 -> superreg r2 r1.
Proof.
  unfold subreg, superreg. intros.
  destruct r2; simpl in H; try contradiction; destruct H; subst; simpl; auto.
Qed.

Lemma superreg_subreg:
  forall r1 r2, superreg r1 r2 -> subreg r2 r1.
Proof.
  unfold subreg, superreg. intros.
  destruct r2; simpl in H; try contradiction; subst; simpl; auto.
Qed.

Lemma subreg_asymm:
  forall r1 r2,
  subreg r1 r2 -> subreg r2 r1 -> False.
Proof.
  intros.
  destruct r2; simpl; try tauto;
    unfold subreg in *; simpl in *; decompose [or] H; subst; compute in *; tauto.
Qed.

Lemma subreg_irrefl:
  forall r, subreg r r -> False.
Proof.
  intros. destruct r; unfold subreg, subregs in H; inv H; inv H0; inv H.
Qed.

Lemma subreg_not_eq:
  forall r1 r2,
  subreg r1 r2 -> r1 <> r2.
Proof.
  intros. contradict H. subst. eauto using subreg_irrefl.
Qed.

Lemma subreg_intrans:
  forall r1 r2 r3,
  subreg r1 r2 -> subreg r2 r3 -> False.
Proof.
  unfold subreg. intros.
  destruct (subregs_or_superregs r2).
  - rewrite H1 in H. contradiction.
  - apply subreg_superreg in H0.
    unfold superreg in H0. rewrite H1 in H0. contradiction.
Qed.

(** Registers overlap if one is a subregister of the other. Modifying a register
  modifies all overlapping registers as well. *)

Definition overlap (r1 r2: mreg): Prop :=
  subreg r1 r2 \/ subreg r2 r1.

Lemma overlap_sym:
  forall r1 r2,
  overlap r1 r2 -> overlap r2 r1.
Proof.
  intros. unfold overlap in *. tauto.
Qed.

Definition overlap_dec (r1 r2: mreg): { overlap r1 r2 } + { ~ overlap r1 r2 }.
Proof.
  intros. unfold overlap.
  destruct (subreg_dec r1 r2); auto.
  destruct (subreg_dec r2 r1); auto.
  tauto.
Defined.

(** Registers may be different in the sense of [<>] but still overlap. The
  following [mreg_diff] predicate characterizes different and non-overlapping
  registers. *)

Definition mreg_diff (r1 r2: mreg): Prop :=
  r1 <> r2 /\ ~ overlap r1 r2.

Lemma same_not_diff:
  forall r, ~ mreg_diff r r.
Proof.
  unfold not, mreg_diff; intros.
  inv H. contradict H0. reflexivity.
Qed.

Lemma diff_not_eq:
  forall r1 r2,
  mreg_diff r1 r2 -> r1 <> r2.
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
  - unfold not; intro. apply overlap_sym in H0. tauto.
Qed.

Definition mreg_diff_dec (r1 r2: mreg): { mreg_diff r1 r2 } + { ~ mreg_diff r1 r2 }.
Proof.
  intros. unfold mreg_diff.
  destruct (mreg_eq r1 r2); try tauto.
  destruct (overlap_dec r1 r2); tauto.
Defined.

Lemma subreg_not_diff:
  forall r s,
  subreg r s -> ~ mreg_diff r s.
Proof.
  intros. unfold not, mreg_diff, overlap. tauto.
Qed.

(** We group registers into pairwise disjoint "families" (for lack of a better
  term) that are closed under aliasing. That is, a register's family contains
  all of its aliases, but also its "siblings". For example, [S0]'s family
  contains [S1], with which it shares the common superregister [D0]. *)

Definition mreg_family (r: mreg): list mreg :=
  match r with
  | S0  | S1  | D0  =>  S0 ::  S1 ::  D0 :: nil
  | S2  | S3  | D1  =>  S2 ::  S3 ::  D1 :: nil
  | S4  | S5  | D2  =>  S4 ::  S5 ::  D2 :: nil
  | S6  | S7  | D3  =>  S6 ::  S7 ::  D3 :: nil
  | S8  | S9  | D4  =>  S8 ::  S9 ::  D4 :: nil
  | S10 | S11 | D5  => S10 :: S11 ::  D5 :: nil
  | S12 | S13 | D6  => S12 :: S13 ::  D6 :: nil
  | S14 | S15 | D7  => S14 :: S15 ::  D7 :: nil
  | S16 | S17 | D8  => S16 :: S17 ::  D8 :: nil
  | S18 | S19 | D9  => S18 :: S19 ::  D9 :: nil
  | S20 | S21 | D10 => S20 :: S21 :: D10 :: nil
  | S22 | S23 | D11 => S22 :: S23 :: D11 :: nil
  | S24 | S25 | D12 => S24 :: S25 :: D12 :: nil
  | S26 | S27 | D13 => S26 :: S27 :: D13 :: nil
  | S28 | S29 | D14 => S28 :: S29 :: D14 :: nil
  | S30 | S31 | D15 => S30 :: S31 :: D15 :: nil
  | r => r :: nil
  end.

Lemma subreg_same_family:
  forall r1 r2, subreg r1 r2 -> mreg_family r1 = mreg_family r2.
Proof.
  intros.
  destruct r2; compute in H; try contradiction;
    decompose [or] H; try contradiction; subst; auto.
Qed.

Lemma overlap_same_family:
  forall r1 r2, overlap r1 r2 -> mreg_family r1 = mreg_family r2.
Proof.
  intros. destruct H; auto using eq_sym, subreg_same_family.
Qed.

Lemma not_same_family_diff:
  forall r1 r2, mreg_family r1 <> mreg_family r2 -> mreg_diff r1 r2.
Proof.
  intros. unfold mreg_diff; split. congruence.
  contradict H. auto using overlap_same_family.
Qed.

Lemma reg_in_family:
  forall r, In r (mreg_family r).
Proof.
  intros. destruct r; compute; tauto.
Qed.

Lemma subregs_in_family:
  forall r1 r2, subreg r1 r2 -> In r1 (mreg_family r2).
Proof.
  intros.
  destruct r2; compute in H; try contradiction;
    decompose [or] H; try contradiction; subst; compute; tauto.
Qed.

Lemma superregs_in_family:
  forall r1 r2, superreg r1 r2 -> In r1 (mreg_family r2).
Proof.
  intros.
  destruct r2; compute in H; try contradiction;
    decompose [or] H; try contradiction; subst; compute; tauto.
Qed.

Lemma partitioned_families:
  forall r1 r2,
  In r1 (mreg_family r2) <-> mreg_family r1 = mreg_family r2.
Proof.
  intros. split.
  - intros. destruct r2; compute in H; try contradiction; decompose [or] H; try contradiction; subst; auto.
  - intros. destruct r1; destruct r2; simpl in *; try congruence; auto.
Qed.

End REG_ALIASING.

(** Architecture-specific mapping from data types to register classes. *)

Inductive regclass := RCint | RCsingle | RCfloat | RCany.

Definition regclass_of_type (t: typ): regclass :=
  match t with
  | Tint | Tlong => RCint
  | Tsingle => RCsingle
  | Tfloat => RCfloat
  | Tany32 | Tany64 => RCany
  end.

(** Interference between register classes: [regclass_interference t1 t2] is
  [true] if registers in the register classes for distinct types [t1] and
  [t2] may (partially) alias or interfere in some other way. *)

Definition regclass_interference (t1 t2: typ): bool :=
  match t1, t2 with
  | Tsingle, Tfloat | Tfloat, Tsingle => true
  | _, _ => false
  end.

Open Scope positive_scope.

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

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R0 => 1  | R1 => 2  | R2 => 3  | R3 => 4
    | R4 => 5  | R5 => 6  | R6 => 7  | R7 => 8
    | R8 => 9  | R9 => 10 | R10 => 11 | R11 => 12
    | R12 => 13
    (* For the purposes of the ordering we impose on registers below, every
       register's index must come between its subregisters' indices. *)
    | S0  => 14 | D0  => 15 | S1 => 16
    | S2  => 17 | D1  => 18 | S3 => 19
    | S4  => 20 | D2  => 21 | S5 => 22
    | S6  => 23 | D3  => 24 | S7 => 25
    | S8  => 26 | D4  => 27 | S9 => 28
    | S10 => 29 | D5  => 30 | S11 =>31
    | S12 => 32 | D6  => 33 | S13 =>34
    | S14 => 35 | D7  => 36 | S15 =>37
    | S16 => 38 | D8  => 39 | S17 =>40
    | S18 => 41 | D9  => 42 | S19 =>43
    | S20 => 44 | D10 => 45 | S21 => 46
    | S22 => 47 | D11 => 48 | S23 => 49
    | S24 => 50 | D12 => 51 | S25 => 52
    | S26 => 53 | D13 => 54 | S27 => 55
    | S28 => 56 | D14 => 57 | S29 => 58
    | S30 => 59 | D15 => 60 | S31 => 61
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.

End IndexedMreg.

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

  (** Define intervals of registers as follows:
      - A register [R] that is not involved in register pairing maps to the
        interval [(R, R)], i.e., it is its own upper and lower bound.
      - A paired register [D = S_low:S_high] maps to the interval
        [(S_low, S_high)]. Its two component registers map to the intervals
        [(S_low, D)] and [(D, S_high)], respectively. *)
  Definition diff_low_bound (r: t): t :=
    match r with
    | R0  => R0  | R1  => R1 | R2  => R2  | R3  => R3
    | R4  => R4  | R5  => R5 | R6  => R6  | R7  => R7
    | R8  => R8  | R9  => R9 | R10 => R10 | R11 => R11
    | R12 => R12
    | S0  => S0  | D0  => S0  | S1  => D0
    | S2  => S2  | D1  => S2  | S3  => D1
    | S4  => S4  | D2  => S4  | S5  => D2
    | S6  => S6  | D3  => S6  | S7  => D3
    | S8  => S8  | D4  => S8  | S9  => D4
    | S10 => S10 | D5  => S10 | S11 => D5
    | S12 => S12 | D6  => S12 | S13 => D6
    | S14 => S14 | D7  => S14 | S15 => D7
    | S16 => S16 | D8  => S16 | S17 => D8
    | S18 => S18 | D9  => S18 | S19 => D9
    | S20 => S20 | D10 => S20 | S21 => D10
    | S22 => S22 | D11 => S22 | S23 => D11
    | S24 => S24 | D12 => S24 | S25 => D12
    | S26 => S26 | D13 => S26 | S27 => D13
    | S28 => S28 | D14 => S28 | S29 => D14
    | S30 => S30 | D15 => S30 | S31 => D15
    end.

  Definition diff_high_bound (r: t): t :=
    match r with
    | R0  => R0  | R1  => R1 | R2  => R2  | R3  => R3
    | R4  => R4  | R5  => R5 | R6  => R6  | R7  => R7
    | R8  => R8  | R9  => R9 | R10 => R10 | R11 => R11
    | R12 => R12
    | S0  => D0  | D0  => S1  | S1  => S1
    | S2  => D1  | D1  => S3  | S3  => S3
    | S4  => D2  | D2  => S5  | S5  => S5
    | S6  => D3  | D3  => S7  | S7  => S7
    | S8  => D4  | D4  => S9  | S9  => S9
    | S10 => D5  | D5  => S11 | S11 => S11
    | S12 => D6  | D6  => S13 | S13 => S13
    | S14 => D7  | D7  => S15 | S15 => S15
    | S16 => D8  | D8  => S17 | S17 => S17
    | S18 => D9  | D9  => S19 | S19 => S19
    | S20 => D10 | D10 => S21 | S21 => S21
    | S22 => D11 | D11 => S23 | S23 => S23
    | S24 => D12 | D12 => S25 | S25 => S25
    | S26 => D13 | D13 => S27 | S27 => S27
    | S28 => D14 | D14 => S29 | S29 => S29
    | S30 => D15 | D15 => S31 | S31 => S31
    end.

  Lemma low_bound_lt_or_eq: forall r: t, lt (diff_low_bound r) r \/ diff_low_bound r = r.
  Proof.
    intros. destruct r; compute; tauto.
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

  Lemma outside_interval_diff:
    forall r r', lt r' (diff_low_bound r) \/ lt (diff_high_bound r) r' -> mreg_diff r r'.
  Proof.
    intros r r' [A | B].
    - split.
      + generalize (low_bound_lt_or_eq r); intros [C | D].
        * eapply not_eq_sym, lt_not_eq, lt_trans; eauto.
        * rewrite D in A. apply not_eq_sym, lt_not_eq; auto.
      + generalize (lt_low_bound_not_subreg r r' A); intros.
        generalize (lt_low_bound_not_subreg' r r' A); intros.
        unfold overlap. intuition auto.
    - split.
      + generalize (lt_or_eq_high_bound r); intros [C | D].
        * eapply lt_not_eq, lt_trans; eauto.
        * rewrite <- D in B. apply lt_not_eq; auto.
      + generalize (high_bound_lt_not_subreg r r' B); intros.
        generalize (high_bound_lt_not_subreg' r r' B); intros.
        unfold overlap. intuition auto.
  Qed.

  Lemma diff_outside_interval:
    forall r r',
    mreg_diff r r' -> lt r' (diff_low_bound r) \/ lt (diff_high_bound r) r'.
  Proof.
    intros r r' (Neq & Noverlap). unfold overlap in Noverlap.
    apply Decidable.not_or in Noverlap; destruct Noverlap as [A B].
    (* FIXME: slow computation *)
    destruct r, r'; try congruence; compute in *; tauto.
  Qed.

End OrderedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Names of registers *)

Local Open Scope string_scope.

Definition register_names :=
  ("R0", R0) ::  ("R1", R1) ::  ("R2", R2) ::  ("R3", R3) ::
  ("R4", R4) ::  ("R5", R5) ::  ("R6", R6) ::  ("R7", R7) ::
  ("R8", R8) ::  ("R9", R9) ::  ("R10", R10) :: ("R11", R11) ::
  ("R12", R12) ::
  ("S0",  S0)  :: ("S1",  S1)  :: ("S2",  S2)  :: ("S3",  S3)  ::
  ("S4",  S4)  :: ("S5",  S5)  :: ("S6",  S6)  :: ("S7",  S7)  ::
  ("S8",  S8)  :: ("S9",  S9)  :: ("S10", S10) :: ("S11", S11) ::
  ("S12", S12) :: ("S13", S13) :: ("S14", S14) :: ("S15", S15) ::
  ("S16", S16) :: ("S17", S17) :: ("S18", S18) :: ("S19", S19) ::
  ("S20", S20) :: ("S21", S21) :: ("S22", S22) :: ("S23", S23) ::
  ("S24", S24) :: ("S25", S25) :: ("S26", S26) :: ("S27", S27) ::
  ("S28", S28) :: ("S29", S29) :: ("S30", S30) :: ("S31", S31) ::
  ("D0",  D0)  :: ("D1",  D1)  :: ("D2",  D2)  :: ("D3",  D3)  ::
  ("D4",  D4)  :: ("D5",  D5)  :: ("D6",  D6)  :: ("D7",  D7)  ::
  ("D8",  D8)  :: ("D9",  D9)  :: ("D10", D10) :: ("D11", D11) ::
  ("D12", D12) :: ("D13", D13) :: ("D14", D14) :: ("D15", D15) :: nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Odiv | Odivu => R0 :: R1 :: R2 :: R3 :: R12 :: nil
  | Ointoffloat | Ointuoffloat | Ointofsingle | Ointuofsingle => S12 :: S13 :: D6 :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_cond (cond: condition): list mreg :=
  nil.

Definition destroyed_by_jumptable: list mreg :=
  nil.

Fixpoint destroyed_by_clobber (cl: list string): list mreg :=
  match cl with
  | nil => nil
  | c1 :: cl =>
      match register_by_name c1 with
      | Some r => r :: destroyed_by_clobber cl
      | None   => destroyed_by_clobber cl
      end
  end.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_memcpy sz al => R2 :: R3 :: R12 :: S14 :: S15 :: D7 :: nil
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg :=
  R12 :: nil.

Definition destroyed_at_indirect_call: list mreg :=
  R0 :: R1 :: R2 :: R3 :: nil.

Definition temp_for_parent_frame: mreg :=
  R12.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  match op with
  | Odiv | Odivu => (Some R0 :: Some R1 :: nil, Some R0)
  | _ => (nil, None)
  end.

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) :=
  (nil, nil).

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    destroyed_at_indirect_call
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There are none for ARM. *)

Definition two_address_op (op: operation) : bool :=
  false.

Global Opaque two_address_op.

(* Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.

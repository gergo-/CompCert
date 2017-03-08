(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Gergö Barany, INRIA Paris                                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

Require Import Coqlib.
Require Import Decidableplus.
Require Import AST.
Require Import Events.
Require Import Locations.
Require Archi.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Locations]) are divided in
  the following groups:
  - Temporaries used for spilling, reloading, and parallel move operations.
  - Allocatable registers, that can be assigned to RTL pseudo-registers.
    These are further divided into:
  -- Callee-save registers, whose value is preserved across a function call.
  -- Caller-save registers that can be modified during a function call.

  We follow the MPPA ABI conventions for "embedded" (non-PIC) code generation
  for callee- and caller-save registers. *)

Definition is_callee_save (r: mreg): bool :=
  match r with
  | R15 | R16 | R17 | R18 | R19 | R20 | R21 | R22
  | R23 | R24 | R25 | R26 | R27 | R28 | R29 | R30 | R31 => true
  | R16R17 | R18R19 | R20R21 | R22R23
  | R24R25 | R26R27 | R28R29 | R30R31 => true
  | _ => false
  end.

(** As described in [Machregs], we decide to allocate all 32-bit values to the
  [single] and all 64-bit values to the [float] register class. Thus the [int]
  caller- and callee-saved registers are empty. This is OK. *)

Definition int_caller_save_regs := @nil mreg.

Definition single_caller_save_regs :=
     R0  :: R1  :: R2  :: R3  :: R4  :: R5  :: R6  :: R7  :: R8  :: R9
  :: R32 :: R33 :: R34 :: R35 :: R36 :: R37 :: R38 :: R39 :: R40 :: R41
  :: R42 :: R43 :: R44 :: R45 :: R46 :: R47 :: R48 :: R49 :: R50 :: R51
  :: R52 :: R53 :: R54 :: R55 :: R56 :: R57 :: R58 :: R59 :: R60 :: R61
  :: R62 :: R63 :: nil.

Definition float_caller_save_regs :=
     R0R1   :: R2R3   :: R4R5   :: R6R7   :: R8R9
  :: R32R33 :: R34R35 :: R36R37 :: R38R39 :: R40R41
  :: R42R43 :: R44R45 :: R46R47 :: R48R49 :: R50R51
  :: R52R53 :: R54R55 :: R56R57 :: R58R59 :: R60R61
  :: R62R63 :: nil.

Definition int_callee_save_regs := @nil mreg.

Definition single_callee_save_regs :=
     R15 :: R16 :: R17 :: R18 :: R19 :: R20 :: R21 :: R22
  :: R23 :: R24 :: R25 :: R26 :: R27 :: R28 :: R29 :: R30 :: R31 :: nil.

Definition float_callee_save_regs :=
     R16R17 :: R18R19 :: R20R21 :: R22R23
  :: R24R25 :: R26R27 :: R28R29 :: R30R31 :: nil.

Definition destroyed_at_call :=
  List.filter (fun r => negb (is_callee_save r)) all_mregs.

Definition dummy_int_reg := R0.      (**r Used in [Coloring]. *)
Definition dummy_single_reg := R0.   (**r Used in [Coloring]. *)
Definition dummy_float_reg := R0R1.  (**r Used in [Coloring]. *)

Definition is_single_reg (r: mreg): bool :=
  match r with
  | R0  | R1  | R2  | R3  | R4  | R5  | R6  | R7  | R8  | R9  | R15
  | R16 | R17 | R18 | R19 | R20 | R21 | R22 | R23 | R24 | R25
  | R26 | R27 | R28 | R29 | R30 | R31 | R32 | R33 | R34 | R35
  | R36 | R37 | R38 | R39 | R40 | R41 | R42 | R43 | R44 | R45
  | R46 | R47 | R48 | R49 | R50 | R51 | R52 | R53 | R54 | R55
  | R56 | R57 | R58 | R59 | R60 | R61 | R62 | R63 => true
  | _ => false
  end.

Definition is_float_reg (r: mreg): bool :=
  match r with
  | R0R1   | R2R3   | R4R5   | R6R7   | R8R9
  | R16R17 | R18R19 | R20R21 | R22R23 | R24R25
  | R26R27 | R28R29 | R30R31 | R32R33 | R34R35
  | R36R37 | R38R39 | R40R41 | R42R43 | R44R45
  | R46R47 | R48R49 | R50R51 | R52R53 | R54R55
  | R56R57 | R58R59 | R60R61 | R62R63 => true
  | _ => false
  end.

(** * Function calling conventions *)

(** The functions in this section determine the locations (machine registers
  and stack slots) used to communicate arguments and results between the
  caller and the callee during function calls.  These locations are functions
  of the signature of the function and of the call instruction.
  Agreement between the caller and the callee on the locations to use
  is guaranteed by our dynamic semantics for Cminor and RTL, which demand
  that the signature of the call instruction is identical to that of the
  called function.

  Calling conventions are largely arbitrary: they must respect the properties
  proved in this section (such as no overlapping between the locations
  of function arguments), but this leaves much liberty in choosing actual
  locations.  *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in registers
  [R0] to [R7]. We treat a function without result as a function with one
  integer result.

  Even the initial parts of structs are returned on registers, with the rest on
  the stack. This doesn't seem to be a good fit for CompCert and will force us
  to do some manual fixups. *)

Definition loc_result (s: signature) : rpair mreg :=
  match s.(sig_res) with
  | None => One R0
  | Some (Tint | Tsingle | Tany32) => One R0
  | Some (Tlong | Tfloat | Tany64) => One R0R1
  end.

(** The result registers have types compatible with that given in the signature. *)

Lemma loc_result_type:
  forall sig,
  subtype (proj_sig_res sig) (typ_rpair mreg_type (loc_result sig)) = true.
Proof.
  intros. unfold proj_sig_res, loc_result. destruct (sig_res sig) as [[]|]; auto.
Qed.

(** The result locations are caller-save registers *)

Lemma loc_result_caller_save:
  forall (s: signature),
  forall_rpair (fun r => is_callee_save r = false) (loc_result s).
Proof.
  intros.
  unfold loc_result. destruct (sig_res s) as [[]|]; simpl; auto.
Qed.

(** If the result is in a pair of registers, those registers are distinct and have size 4 at least. *)

Lemma loc_result_pair:
  forall sg,
  match loc_result sg with
  | One _ => True
  | Twolong r1 r2 => r1 <> r2 /\ sg.(sig_res) = Some Tlong /\ subtype Tint (mreg_type r1) = true /\ subtype Tint (mreg_type r2) = true /\ Archi.splitlong = true
  end.
Proof.
  intros; unfold loc_result; destruct (sig_res sg) as [[]|];
    repeat split; simpl; auto with zarith; congruence.
Qed.

(** The location of the result depends only on the result part of the signature *)

Lemma loc_result_exten:
  forall s1 s2, s1.(sig_res) = s2.(sig_res) -> loc_result s1 = loc_result s2.
Proof.
  intros. unfold loc_result. rewrite H; auto.
Qed.

(** ** Location of function arguments *)

(** We use the following calling convention:
  - The first arguments of any 32-bit or 64-bit type are passed in registers
    [R0] to [R7], paired as necessary.
  - The above also holds for the first four fields of structures passed as
    arguments.
  - Extra arguments are passed on the stack, in [Outgoing] slots, consecutively
    assigned (with alignment), starting at word offset 0. 64-bit values are
    aligned on doubleword boundaries. *)

Definition param_regs :=
  R0 :: R1 :: R2 :: R3 :: R4 :: R5 :: R6 :: R7 :: nil.

Definition reg_param (n: Z) : mreg :=
  match list_nth_z param_regs n with Some r => r | None => R0 end.

(** We only ever index this list with even indices, so every other element is an
  irrelevant placeholder. *)
Definition paired_param_regs :=
  R0R1 :: R0R1 :: R2R3 :: R2R3 :: R4R5 :: R4R5 :: R6R7 :: R6R7 :: nil.

Definition paired_reg_param (n: Z) : mreg :=
  match list_nth_z paired_param_regs n with Some r => r | None => R0R1 end.

Fixpoint loc_arguments_rec
     (tyl: list typ) (gpr ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | (Tint | Tsingle | Tany32) as ty :: tys =>
      if zlt gpr 8
      then One (R (reg_param gpr)) :: loc_arguments_rec tys (gpr + 1) ofs
      else One (S Outgoing ofs ty) :: loc_arguments_rec tys gpr (ofs + 1)
  | (Tlong | Tfloat | Tany64) as ty :: tys =>
      let gpr := align gpr 2 in
      if zlt gpr 8
      then One (R (paired_reg_param gpr)) :: loc_arguments_rec tys (gpr + 2) ofs
      else let ofs := align ofs 2 in
           One (S Outgoing ofs ty) :: loc_arguments_rec tys gpr (ofs + 2)
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list (rpair loc) :=
  loc_arguments_rec s.(sig_args) 0 0.

(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Fixpoint size_arguments_rec (tyl: list typ) (gpr ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => ofs
  | (Tint | Tsingle | Tany32) :: tys =>
      if zlt gpr 8
      then size_arguments_rec tys (gpr + 1) ofs
      else size_arguments_rec tys gpr (ofs + 1)
  | (Tlong | Tfloat | Tany64) :: tys =>
      let gpr := align gpr 2 in
      if zlt gpr 8
      then size_arguments_rec tys (gpr + 2) ofs
      else size_arguments_rec tys gpr (align ofs 2 + 2)
  end.

Definition size_arguments (s: signature) : Z :=
  size_arguments_rec s.(sig_args) 0 0.

(** Argument locations are either non-temporary registers or [Outgoing]
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => is_callee_save r = false
  | S Outgoing ofs ty => 0 <= ofs /\ (typealign ty | ofs)
  | _ => False
  end.

Definition loc_argument_charact (ofs: Z) (l: loc) : Prop :=
  match l with
  | R r => is_callee_save r = false
  | S Outgoing ofs' ty => ofs <= ofs' /\ (typealign ty | ofs')
  | _ => False
  end.

Remark reg_param_caller_save: forall n, is_callee_save (reg_param n) = false.
Proof.
  unfold reg_param; intros.
  assert (A: forall r, In r param_regs -> is_callee_save r = false) by decide_goal.
  destruct (list_nth_z param_regs n) as [r|] eqn:NTH.
  apply A. eapply list_nth_z_in; eauto.
  auto.
Qed.

Remark paired_reg_param_caller_save: forall n, is_callee_save (paired_reg_param n) = false.
Proof.
  unfold paired_reg_param; intros.
  assert (A: forall r, In r paired_param_regs -> is_callee_save r = false) by decide_goal.
  destruct (list_nth_z paired_param_regs n) as [r|] eqn:NTH.
  apply A. eapply list_nth_z_in; eauto.
  auto.
Qed.

Remark loc_arguments_rec_charact:
  forall tyl gpr ofs p,
  In p (loc_arguments_rec tyl gpr ofs) -> forall_rpair (loc_argument_charact ofs) p.
Proof.
  assert (X: forall ofs1 ofs2 l, loc_argument_charact ofs2 l -> ofs1 <= ofs2 -> loc_argument_charact ofs1 l).
  { destruct l; simpl; intros; auto. destruct sl; auto. intuition omega. }
  assert (Y: forall ofs1 ofs2 p, forall_rpair (loc_argument_charact ofs2) p -> ofs1 <= ofs2 -> forall_rpair (loc_argument_charact ofs1) p).
  { destruct p; simpl; intuition eauto. }
  induction tyl; simpl loc_arguments_rec; intros.
  elim H.
  destruct a.
- (* int *)
  destruct (zlt gpr 8); destruct H;
  subst. apply reg_param_caller_save.
  eapply IHtyl; eauto.
  split; [omega | auto with zarith].
  eapply Y; eauto. omega.
- (* float *)
  set (gpr' := align gpr 2) in *.
  destruct (zlt gpr' 8); destruct H;
  subst. apply paired_reg_param_caller_save.
  eapply IHtyl; eauto.
  split; auto using align_le, align_divides with zarith.
  eapply Y; eauto.
  apply Zle_trans with (align ofs 2); auto using align_le with zarith.
- (* long *)
  set (gpr' := align gpr 2) in *.
  destruct (zlt gpr' 8); destruct H;
  subst. apply paired_reg_param_caller_save.
  eapply IHtyl; eauto.
  split; auto using align_le, align_divides with zarith.
  eapply Y; eauto.
  apply Zle_trans with (align ofs 2); auto using align_le with zarith.
- (* single *)
  destruct (zlt gpr 8); destruct H;
  subst. apply reg_param_caller_save.
  eapply IHtyl; eauto.
  split; [omega | auto with zarith].
  eapply Y; eauto. omega.
- (* any32 *)
  destruct (zlt gpr 8); destruct H;
  subst. apply reg_param_caller_save.
  eapply IHtyl; eauto.
  split; [omega | auto with zarith].
  eapply Y; eauto. omega.
- (* any64 *)
  set (gpr' := align gpr 2) in *.
  destruct (zlt gpr' 8); destruct H;
  subst. apply paired_reg_param_caller_save.
  eapply IHtyl; eauto.
  split; auto using align_le, align_divides with zarith.
  eapply Y; eauto.
  apply Zle_trans with (align ofs 2); auto using align_le with zarith.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (p: rpair loc),
  In p (loc_arguments s) -> forall_rpair loc_argument_acceptable p.
Proof.
  unfold loc_arguments; intros.
  assert (X: forall l, loc_argument_charact 0 l -> loc_argument_acceptable l).
  { unfold loc_argument_charact, loc_argument_acceptable.
    destruct l as [r | [] ofs ty]; auto. }
  assert (Y: forall p, forall_rpair (loc_argument_charact 0) p -> forall_rpair loc_argument_acceptable p).
  { destruct p0; simpl; intuition auto. }
  assert (In p (loc_arguments_rec (sig_args s) 0 0) -> forall_rpair loc_argument_acceptable p).
  { intros. exploit loc_arguments_rec_charact; eauto. }
  destruct (cc_vararg (sig_cc s)); auto.
Qed.

Hint Resolve loc_arguments_acceptable: locs.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark size_arguments_rec_above:
  forall tyl gpr ofs0,
  ofs0 <= size_arguments_rec tyl gpr ofs0.
Proof.
  induction tyl; simpl; intros.
  omega.
  destruct a.
  - (* Tint *)
    destruct (zlt gpr 8); eauto. apply Zle_trans with (ofs0 + 1); auto; omega.
  - (* Tfloat *)
    set (gpr' := align gpr 2).
    destruct (zlt gpr' 8); eauto.
    apply Zle_trans with (align ofs0 2).
    + apply align_le; omega.
    + apply Zle_trans with (align ofs0 2 + 2); auto; omega.
  - (* Tlong *)
    set (gpr' := align gpr 2).
    destruct (zlt gpr' 8); eauto.
    apply Zle_trans with (align ofs0 2).
    + apply align_le; omega.
    + apply Zle_trans with (align ofs0 2 + 2); auto; omega.
  - (* Tsingle *)
    destruct (zlt gpr 8); eauto. apply Zle_trans with (ofs0 + 1); auto; omega.
  - (* Tany32 *)
    destruct (zlt gpr 8); eauto. apply Zle_trans with (ofs0 + 1); auto; omega.
  - (* Tany64 *)
    set (gpr' := align gpr 2).
    destruct (zlt gpr' 8); eauto.
    apply Zle_trans with (align ofs0 2).
    + apply align_le; omega.
    + apply Zle_trans with (align ofs0 2 + 2); auto; omega.
Qed.

Lemma size_arguments_above:
  forall s, size_arguments s >= 0.
Proof.
  intros; unfold size_arguments. apply Zle_ge.
  apply size_arguments_rec_above.
Qed.

Lemma loc_arguments_rec_bounded:
  forall ofs ty tyl gpr ofs0,
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments_rec tyl gpr ofs0)) ->
  ofs + typesize ty <= size_arguments_rec tyl gpr ofs0.
Proof.
  induction tyl; simpl; intros.
  elim H.
  destruct a.
- (* Tint *)
  destruct (zlt gpr 8); destruct H.
  discriminate.
  eauto.
  inv H. apply size_arguments_rec_above.
  eauto.
- (* Tfloat *)
  destruct (zlt (align gpr 2) 8).
  destruct H. discriminate. eauto.
  destruct H. inv H.
  apply Zle_trans with (align ofs0 2 + 2).
    auto using align_le with zarith.
    apply size_arguments_rec_above.
  apply IHtyl.
  assumption.
- (* Tlong *)
  destruct (zlt (align gpr 2) 8).
  destruct H. discriminate. eauto.
  destruct H. inv H.
  apply Zle_trans with (align ofs0 2 + 2).
    auto using align_le with zarith.
    apply size_arguments_rec_above.
  apply IHtyl.
  assumption.
- (* Tsingle *)
  destruct (zlt gpr 8); destruct H.
  discriminate.
  eauto.
  inv H. apply size_arguments_rec_above.
  eauto.
- (* Tany32 *)
  destruct (zlt gpr 8); destruct H.
  discriminate.
  eauto.
  inv H. apply size_arguments_rec_above.
  eauto.
- (* Tany64 *)
  destruct (zlt (align gpr 2) 8).
  destruct H. discriminate. eauto.
  destruct H. inv H.
  apply Zle_trans with (align ofs0 2 + 2).
    auto using align_le with zarith.
    apply size_arguments_rec_above.
  apply IHtyl.
  assumption.
Qed.

Lemma loc_arguments_bounded:
  forall (s: signature) (ofs: Z) (ty: typ),
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments s)) ->
  ofs + typesize ty <= size_arguments s.
Proof.
  unfold loc_arguments, size_arguments; intros.
  apply loc_arguments_rec_bounded. eauto.
Qed.

Lemma loc_arguments_main:
  loc_arguments signature_main = nil.
Proof.
  unfold loc_arguments.
  reflexivity.
Qed.

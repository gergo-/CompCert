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
Require Import Memdata.

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
  | S24 | S25 | S26 | S27 | S28 | S29 | S30 | S31 => Tany32
  | D0  | D1  | D2  | D3  | D4  | D5  | D6  | D7
  | D8  | D9  | D10 | D11 | D12 | D13 | D14 | D15 => Tany64
  end.

Definition subregs (r: mreg): option (mreg * mreg) :=
  match r with
  | D0  => Some ( S0,  S1)
  | D1  => Some ( S2,  S3)
  | D2  => Some ( S4,  S5)
  | D3  => Some ( S6,  S7)
  | D4  => Some ( S8,  S9)
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

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R0  =>  2 | R1 =>  4 | R2  =>  6 | R3  =>  8
    | R4  => 10 | R5 => 12 | R6  => 14 | R7  => 16
    | R8  => 18 | R9 => 20 | R10 => 22 | R11 => 24
    | R12 => 26

    (* For the purposes of the ordering defined in [Registerfile], every double
       register's index must be between its subregisters' indices. *)
    | S0  => 30 | D0  => 31 | S1  => 32
    | S2  => 33 | D1  => 34 | S3  => 35
    | S4  => 36 | D2  => 37 | S5  => 38
    | S6  => 39 | D3  => 40 | S7  => 41
    | S8  => 42 | D4  => 43 | S9  => 44
    | S10 => 45 | D5  => 46 | S11 => 47
    | S12 => 48 | D6  => 49 | S13 => 50
    | S14 => 51 | D7  => 52 | S15 => 53
    | S16 => 54 | D8  => 55 | S17 => 56
    | S18 => 57 | D9  => 58 | S19 => 59
    | S20 => 60 | D10 => 61 | S21 => 62
    | S22 => 63 | D11 => 64 | S23 => 65
    | S24 => 66 | D12 => 67 | S25 => 68
    | S26 => 69 | D13 => 70 | S27 => 71
    | S28 => 72 | D14 => 73 | S29 => 74
    | S30 => 75 | D15 => 76 | S31 => 77
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.

  (* These no longer work:

  Open Scope Z_scope.

  Lemma scaled_index_with_size_aux:
    forall r1 r2, Zpos (index r1) < Zpos (index r2) -> Zpos (index r1) + 2 <= Zpos (index r2).
  Proof.
    decide_goal.
  Qed.

  Lemma scaled_index_with_size:
    forall r1 r2,
    Zpos (index r1) < Zpos (index r2) ->
    Zpos (index r1) * 4 + AST.typesize (mreg_type r1) <= Zpos (index r2) * 4.
  Proof.
    intros.
    generalize (scaled_index_with_size_aux r1 r2); intro.
    assert (AST.typesize (mreg_type r1) <= 8) by (destruct (mreg_type r1); simpl; omega).
    omega.
  Qed.
*)
End IndexedMreg.

(* Machine-specific definitions needed for capturing register aliasing. *)

Inductive part :=
  | PFull (r: mreg)
  | PLow  (r: mreg)
  | PHigh (r: mreg).

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

Definition diff_low_bound (r: mreg): mreg :=
  match mreg_part r with
  | PFull r =>
    match subregs r with
    | Some (lo, hi) => lo
    | None => r
    end
  | PLow s  => r
  | PHigh s => s
  end.

Definition diff_high_bound (r: mreg): mreg :=
  match mreg_part r with
  | PFull r =>
    match subregs r with
    | Some (lo, hi) => hi
    | None => r
    end
  | PLow s => s
  | PHigh s => r
  end.

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
  | Ointoffloat | Ointuoffloat | Ointofsingle | Ointuofsingle => S12 :: D6 :: nil
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

Definition destroyed_by_setstack (q: quantity): list mreg := nil.

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
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.

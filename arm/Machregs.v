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

Definition subregs (r: mreg): list mreg :=
  match r with
  | D0  => S0 :: S1 :: nil
  | D1  => S2 :: S3 :: nil
  | D2  => S4 :: S5 :: nil
  | D3  => S6 :: S7 :: nil
  | D4  => S8 :: S9 :: nil
  | D5  => S10 :: S11 :: nil
  | D6  => S12 :: S13 :: nil
  | D7  => S14 :: S15 :: nil
  | D8  => S16 :: S17 :: nil
  | D9  => S18 :: S19 :: nil
  | D10 => S20 :: S21 :: nil
  | D11 => S22 :: S23 :: nil
  | D12 => S24 :: S25 :: nil
  | D13 => S26 :: S27 :: nil
  | D14 => S28 :: S29 :: nil
  | D15 => S30 :: S31 :: nil
  | _ => nil
  end.

Definition superregs (r: mreg): list mreg :=
  match r with
  | S0  | S1  => D0 :: nil
  | S2  | S3  => D1 :: nil
  | S4  | S5  => D2 :: nil
  | S6  | S7  => D3 :: nil
  | S8  | S9  => D4 :: nil
  | S10 | S11 => D5 :: nil
  | S12 | S13 => D6 :: nil
  | S14 | S15 => D7 :: nil
  | S16 | S17 => D8 :: nil
  | S18 | S19 => D9 :: nil
  | S20 | S21 => D10 :: nil
  | S22 | S23 => D11 :: nil
  | S24 | S25 => D12 :: nil
  | S26 | S27 => D13 :: nil
  | S28 | S29 => D14 :: nil
  | S30 | S31 => D15 :: nil
  | _ => nil
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

    | D0  => 28 | D1  => 30 | D2  => 32 | D3  => 34
    | D4  => 36 | D5  => 38 | D6  => 40 | D7  => 42
    | D8  => 44 | D9  => 46 | D10 => 48 | D11 => 50
    | D12 => 52 | D13 => 54 | D14 => 56 | D15 => 58

    | S0  =>  60 | S1  =>  62 | S2  =>  64 | S3  =>  66
    | S4  =>  68 | S5  =>  70 | S6  =>  72 | S7  =>  74
    | S8  =>  76 | S9  =>  78 | S10 =>  80 | S11 =>  82
    | S12 =>  84 | S13 =>  86 | S14 =>  88 | S15 =>  90
    | S16 =>  92 | S17 =>  94 | S18 =>  96 | S19 =>  98
    | S20 => 100 | S21 => 102 | S22 => 104 | S23 => 106
    | S24 => 108 | S25 => 110 | S26 => 112 | S27 => 114
    | S28 => 116 | S29 => 118 | S30 => 120 | S31 => 122
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.

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
End IndexedMreg.

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

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

Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Op.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations. These are the registers that can be allocated to RTL
  pseudo-registers ([Rxx]).

  The type [mreg] does not include reserved machine registers
  such as the stack pointer or the link register.

  The MPPA has 64 32-bit general purpose (integer or floating-point) registers
  that can be paired to hold 64-bit values. Such a pair must consist of adjacent
  registers [RnR(n+1)] where the lower register number [n] is even.

  We model both the individual general-purpose registers and the register pairs
  as machine registers, then add subregister relationships to ensure correct
  register allocation. We allocate [Tlong] to register pairs instead of using
  the [splitlong] mechanism. This makes register allocation slightly less
  flexible (with [splitlong], the registers holding parts of a long need not
  be adjacent), but it allows us to model the MPPA's 64-bit integer arithmetic
  instructions directly. *)

Inductive mreg: Type :=
  (** Allocatable general-purpose registers *)
  | R0  | R1  | R2  | R3  | R4  | R5  | R6  | R7  | R8  | R9
  (* R10 to R14 are reserved for the frame pointer, stack pointer, etc. *)
  | R15 | R16 | R17 | R18 | R19 | R20 | R21 | R22 | R23 | R24
  | R25 | R26 | R27 | R28 | R29 | R30 | R31 | R32 | R33 | R34
  | R35 | R36 | R37 | R38 | R39 | R40 | R41 | R42 | R43 | R44
  | R45 | R46 | R47 | R48 | R49 | R50 | R51 | R52 | R53 | R54
  | R55 | R56 | R57 | R58 | R59 | R60 | R61 | R62 | R63
  (** Allocatable register pairs *)
  | R0R1   | R2R3   | R4R5   | R6R7   | R8R9
  | R16R17 | R18R19 | R20R21 | R22R23 | R24R25
  | R26R27 | R28R29 | R30R31 | R32R33 | R34R35
  | R36R37 | R38R39 | R40R41 | R42R43 | R44R45
  | R46R47 | R48R49 | R50R51 | R52R53 | R54R55
  | R56R57 | R58R59 | R60R61 | R62R63.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
     R0  :: R1  :: R2  :: R3  :: R4  :: R5  :: R6  :: R7  :: R8  :: R9
  :: R15 :: R16 :: R17 :: R18 :: R19 :: R20 :: R21 :: R22 :: R23 :: R24
  :: R25 :: R26 :: R27 :: R28 :: R29 :: R30 :: R31 :: R32 :: R33 :: R34
  :: R35 :: R36 :: R37 :: R38 :: R39 :: R40 :: R41 :: R42 :: R43 :: R44
  :: R45 :: R46 :: R47 :: R48 :: R49 :: R50 :: R51 :: R52 :: R53 :: R54
  :: R55 :: R56 :: R57 :: R58 :: R59 :: R60 :: R61 :: R62 :: R63
  :: R0R1   :: R2R3   :: R4R5   :: R6R7   :: R8R9
  :: R16R17 :: R18R19 :: R20R21 :: R22R23 :: R24R25
  :: R26R27 :: R28R29 :: R30R31 :: R32R33 :: R34R35
  :: R36R37 :: R38R39 :: R40R41 :: R42R43 :: R44R45
  :: R46R47 :: R48R49 :: R50R51 :: R52R53 :: R54R55
  :: R56R57 :: R58R59 :: R60R61 :: R62R63 :: nil.

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
  | R0  | R1  | R2  | R3  | R4  | R5  | R6  | R7  | R8  | R9
  | R15 | R16 | R17 | R18 | R19 | R20 | R21 | R22 | R23 | R24
  | R25 | R26 | R27 | R28 | R29 | R30 | R31 | R32 | R33 | R34
  | R35 | R36 | R37 | R38 | R39 | R40 | R41 | R42 | R43 | R44
  | R45 | R46 | R47 | R48 | R49 | R50 | R51 | R52 | R53 | R54
  | R55 | R56 | R57 | R58 | R59 | R60 | R61 | R62 | R63 => Tany32
  | R0R1   | R2R3   | R4R5   | R6R7   | R8R9
  | R16R17 | R18R19 | R20R21 | R22R23 | R24R25
  | R26R27 | R28R29 | R30R31 | R32R33 | R34R35
  | R36R37 | R38R39 | R40R41 | R42R43 | R44R45
  | R46R47 | R48R49 | R50R51 | R52R53 | R54R55
  | R56R57 | R58R59 | R60R61 | R62R63 => Tany64
  end.

Definition subregs (r: mreg): list mreg :=
  match r with
  | R0R1   => R0  :: R1  :: nil
  | R2R3   => R2  :: R3  :: nil
  | R4R5   => R4  :: R5  :: nil
  | R6R7   => R6  :: R7  :: nil
  | R8R9   => R8  :: R9  :: nil
  | R16R17 => R16 :: R17 :: nil
  | R18R19 => R18 :: R19 :: nil
  | R20R21 => R20 :: R21 :: nil
  | R22R23 => R22 :: R23 :: nil
  | R24R25 => R24 :: R25 :: nil
  | R26R27 => R26 :: R27 :: nil
  | R28R29 => R28 :: R29 :: nil
  | R30R31 => R30 :: R31 :: nil
  | R32R33 => R32 :: R33 :: nil
  | R34R35 => R34 :: R35 :: nil
  | R36R37 => R36 :: R37 :: nil
  | R38R39 => R38 :: R39 :: nil
  | R40R41 => R40 :: R41 :: nil
  | R42R43 => R42 :: R43 :: nil
  | R44R45 => R44 :: R45 :: nil
  | R46R47 => R46 :: R47 :: nil
  | R48R49 => R48 :: R49 :: nil
  | R50R51 => R50 :: R51 :: nil
  | R52R53 => R52 :: R53 :: nil
  | R54R55 => R54 :: R55 :: nil
  | R56R57 => R56 :: R57 :: nil
  | R58R59 => R58 :: R59 :: nil
  | R60R61 => R60 :: R61 :: nil
  | R62R63 => R62 :: R63 :: nil
  | _ => nil
  end.

Definition superregs (r: mreg): list mreg :=
  match r with
  | R0  | R1  => R0R1 :: nil
  | R2  | R3  => R2R3 :: nil
  | R4  | R5  => R4R5 :: nil
  | R6  | R7  => R6R7 :: nil
  | R8  | R9  => R8R9 :: nil
  (* R15 is a special case: As R14 is reserved, we don't have an R14R15
     register pair, so R15 has no superregister. *)
  | R15 => nil
  | R16 | R17 => R16R17 :: nil
  | R18 | R19 => R18R19 :: nil
  | R20 | R21 => R20R21 :: nil
  | R22 | R23 => R22R23 :: nil
  | R24 | R25 => R24R25 :: nil
  | R26 | R27 => R26R27 :: nil
  | R28 | R29 => R28R29 :: nil
  | R30 | R31 => R30R31 :: nil
  | R32 | R33 => R32R33 :: nil
  | R34 | R35 => R34R35 :: nil
  | R36 | R37 => R36R37 :: nil
  | R38 | R39 => R38R39 :: nil
  | R40 | R41 => R40R41 :: nil
  | R42 | R43 => R42R43 :: nil
  | R44 | R45 => R44R45 :: nil
  | R46 | R47 => R46R47 :: nil
  | R48 | R49 => R48R49 :: nil
  | R50 | R51 => R50R51 :: nil
  | R52 | R53 => R52R53 :: nil
  | R54 | R55 => R54R55 :: nil
  | R56 | R57 => R56R57 :: nil
  | R58 | R59 => R58R59 :: nil
  | R60 | R61 => R60R61 :: nil
  | R62 | R63 => R62R63 :: nil
  | _ => nil
  end.

(** Architecture-specific mapping from data types to register classes. *)

Inductive regclass := RCint | RCsingle | RCfloat | RCany.

(* We don't differentiate between integer and floating-point registers, only
  between 32-bit and 64-bit ones. This size difference is best captured by the
  register classes [RCsingle] and [RCfloat], which is why we allocate integers
  into these classes as well. *)
Definition regclass_of_type (t: typ): regclass :=
  match t with
  | Tint | Tsingle => RCsingle
  | Tlong | Tfloat => RCfloat
  | Tany32 | Tany64 => RCany
  end.

(** Interference between register classes: [regclass_interference t1 t2] is
  [true] if registers in the register classes for distinct types [t1] and
  [t2] may (partially) alias or interfere in some other way. *)

Definition regclass_interference (t1 t2: typ): bool :=
  match regclass_of_type t1, regclass_of_type t2 with
  | RCsingle, RCfloat | RCfloat, RCsingle => true
  | _, _ => false
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R0  => 1  | R1  => 2  | R2  => 3  | R3  => 4  | R4 => 5
    | R5  => 6  | R6  => 7  | R7  => 8  | R8  => 9  | R9 => 10
    | R15 => 16 | R16 => 17 | R17 => 18 | R18 => 19 | R19 => 20
    | R20 => 21 | R21 => 22 | R22 => 23 | R23 => 24 | R24 => 25
    | R25 => 26 | R26 => 27 | R27 => 28 | R28 => 29 | R29 => 30
    | R30 => 31 | R31 => 32 | R32 => 33 | R33 => 34 | R34 => 35
    | R35 => 36 | R36 => 37 | R37 => 38 | R38 => 39 | R39 => 40
    | R40 => 41 | R41 => 42 | R42 => 43 | R43 => 44 | R44 => 45
    | R45 => 46 | R46 => 47 | R47 => 48 | R48 => 49 | R49 => 50
    | R50 => 51 | R51 => 52 | R52 => 53 | R53 => 54 | R54 => 55
    | R55 => 56 | R56 => 57 | R57 => 58 | R58 => 59 | R59 => 60
    | R60 => 61 | R61 => 62 | R62 => 63 | R63 => 64
    | R0R1   => 65  | R2R3   => 67  | R4R5   => 69  | R6R7   => 71  | R8R9   => 73
    | R16R17 => 81  | R18R19 => 83  | R20R21 => 85  | R22R23 => 87  | R24R25 => 89
    | R26R27 => 91  | R28R29 => 93  | R30R31 => 95  | R32R33 => 97  | R34R35 => 99
    | R36R37 => 101 | R38R39 => 103 | R40R41 => 105 | R42R43 => 107 | R44R45 => 109
    | R46R47 => 111 | R48R49 => 113 | R50R51 => 115 | R52R53 => 117 | R54R55 => 119
    | R56R57 => 121 | R58R59 => 123 | R60R61 => 125 | R62R63 => 127
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Names of registers *)

Local Open Scope string_scope.

Definition register_names :=
     ("R0",  R0)  :: ("R1",  R1)  :: ("R2",  R2)  :: ("R3",  R3)  :: ("R4",  R4)
  :: ("R5",  R5)  :: ("R6",  R6)  :: ("R7",  R7)  :: ("R8",  R8)  :: ("R9",  R9)
  :: ("R15", R15) :: ("R16", R16) :: ("R17", R17) :: ("R18", R18) :: ("R19", R19)
  :: ("R20", R20) :: ("R21", R21) :: ("R22", R22) :: ("R23", R23) :: ("R24", R24)
  :: ("R25", R25) :: ("R26", R26) :: ("R27", R27) :: ("R28", R28) :: ("R29", R29)
  :: ("R30", R30) :: ("R31", R31) :: ("R32", R32) :: ("R33", R33) :: ("R34", R34)
  :: ("R35", R35) :: ("R36", R36) :: ("R37", R37) :: ("R38", R38) :: ("R39", R39)
  :: ("R40", R40) :: ("R41", R41) :: ("R42", R42) :: ("R43", R43) :: ("R44", R44)
  :: ("R45", R45) :: ("R46", R46) :: ("R47", R47) :: ("R48", R48) :: ("R49", R49)
  :: ("R50", R50) :: ("R51", R51) :: ("R52", R52) :: ("R53", R53) :: ("R54", R54)
  :: ("R55", R55) :: ("R56", R56) :: ("R57", R57) :: ("R58", R58) :: ("R59", R59)
  :: ("R60", R60) :: ("R61", R61) :: ("R62", R62) :: ("R63", R63)
  :: ("R0R1",   R0R1)   :: ("R2R3",   R2R3)   :: ("R4R5",   R4R5)
  :: ("R6R7",   R6R7)   :: ("R8R9",   R8R9)   :: ("R16R17", R16R17)
  :: ("R18R19", R18R19) :: ("R20R21", R20R21) :: ("R22R23", R22R23)
  :: ("R24R25", R24R25) :: ("R26R27", R26R27) :: ("R28R29", R28R29)
  :: ("R30R31", R30R31) :: ("R32R33", R32R33) :: ("R34R35", R34R35)
  :: ("R36R37", R36R37) :: ("R38R39", R38R39) :: ("R40R41", R40R41)
  :: ("R42R43", R42R43) :: ("R44R45", R44R45) :: ("R46R47", R46R47)
  :: ("R48R49", R48R49) :: ("R50R51", R50R51) :: ("R52R53", R52R53)
  :: ("R54R55", R54R55) :: ("R56R57", R56R57) :: ("R58R59", R58R59)
  :: ("R60R61", R60R61) :: ("R62R63", R62R63) :: nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg :=
  nil.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg :=
  nil.

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
  (* FIXME: Change this based on the manual code we eventually write for memcpy. *)
  | EF_memcpy sz al => nil
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg :=
  nil.

Definition destroyed_at_function_entry: list mreg :=
  nil.

Definition destroyed_at_indirect_call: list mreg :=
  nil.

Definition temp_for_parent_frame: mreg :=
  R8R9.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  (nil, None).

(* TODO: Research this. *)
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
  by [mregs_for_operation].  There are none for MPPA. *)

Definition two_address_op (op: operation) : bool :=
  false.

Global Opaque two_address_op.

(* Constraints on constant propagation for builtins *)

(* TODO: Research this. *)
Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_vload _ => OK_addrany :: nil
  | EF_vstore _ => OK_addrany :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.

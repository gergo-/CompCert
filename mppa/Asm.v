
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

(** Abstract syntax and semantics for ARM assembly language *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.

(** * Abstract syntax *)

(** General-purpose registers. *)

Inductive gpreg: Type :=
  | GPR0  | GPR1  | GPR2  | GPR3  | GPR4  | GPR5  | GPR6  | GPR7  | GPR8  | GPR9
  | GPR10 | GPR11 | GPR12 | GPR13 | GPR14 | GPR15 | GPR16 | GPR17 | GPR18 | GPR19
  | GPR20 | GPR21 | GPR22 | GPR23 | GPR24 | GPR25 | GPR26 | GPR27 | GPR28 | GPR29
  | GPR30 | GPR31 | GPR32 | GPR33 | GPR34 | GPR35 | GPR36 | GPR37 | GPR38 | GPR39
  | GPR40 | GPR41 | GPR42 | GPR43 | GPR44 | GPR45 | GPR46 | GPR47 | GPR48 | GPR49
  | GPR50 | GPR51 | GPR52 | GPR53 | GPR54 | GPR55 | GPR56 | GPR57 | GPR58 | GPR59
  | GPR60 | GPR61 | GPR62 | GPR63.

(** Pairs of general-purpose registers. *)
Inductive pgpreg: Type :=
  | PGPR0R1   | PGPR2R3   | PGPR4R5   | PGPR6R7   | PGPR8R9
  | PGPR10R11 | PGPR12R13 | PGPR14R15 | PGPR16R17 | PGPR18R19
  | PGPR20R21 | PGPR22R23 | PGPR24R25 | PGPR26R27 | PGPR28R29
  | PGPR30R31 | PGPR32R33 | PGPR34R35 | PGPR36R37 | PGPR38R39
  | PGPR40R41 | PGPR42R43 | PGPR44R45 | PGPR46R47 | PGPR48R49
  | PGPR50R51 | PGPR52R53 | PGPR54R55 | PGPR56R57 | PGPR58R59
  | PGPR60R61 | PGPR62R63.

(** Integer registers, floating-point registers. *)

(*
Inductive ireg: Type :=
  | IR0: ireg  | IR1: ireg  | IR2: ireg  | IR3: ireg
  | IR4: ireg  | IR5: ireg  | IR6: ireg  | IR7: ireg
  | IR8: ireg  | IR9: ireg  | IR10: ireg | IR11: ireg
  | IR12: ireg | IR13: ireg | IR14: ireg.

Inductive freg: Type :=
  | FR0: freg  | FR1: freg  | FR2: freg  | FR3: freg
  | FR4: freg  | FR5: freg  | FR6: freg  | FR7: freg
  | FR8: freg  | FR9: freg  | FR10: freg  | FR11: freg
  | FR12: freg  | FR13: freg  | FR14: freg  | FR15: freg.
*)
(*
Notation "'ireg'" := gpreg (only parsing).
Notation "'freg'" := pgpreg (only parsing).
*)

Lemma gpreg_eq: forall (x y: gpreg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma pgpreg_eq: forall (x y: pgpreg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(*
Definition ireg_eq := gpreg_eq.
Definition freg_eq := gpreg_eq.
*)

(** Bits in the condition register. *)

Inductive crbit: Type :=
  | CNE:   crbit    (**r not equal *)
  | CEQ:   crbit    (**r equal *)
  | CLT:   crbit    (**r less than *)
  | CGE:   crbit    (**r greater than or equal *)
  | CLE:   crbit    (**r less than or equal *)
  | CGT:   crbit    (**r greater than or equal *)
  | CLTU:  crbit    (**r less than unsigned *)
  | CGEU:  crbit    (**r greater than or equal unsigned *)
  | CLEU:  crbit    (**r less than or equal unsigned *)
  | CGTU:  crbit    (**r greater than or equal unsigned *)
  (* The following are not used for the moment. *)
  | CALL:  crbit    (**r all bits set in mask *)
  | NALL:  crbit    (**r not all bits set in mask *)
  | CANY:  crbit    (**r any bits set in mask *)
  | CNONE: crbit    (**r not any bits set in mask *)
  .

Lemma crbit_eq: forall (x y: crbit), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** We model the following registers of the MPPA architecture. *)

(*
Inductive preg: Type :=
  | IR: ireg -> preg                    (**r integer registers *)
  | FR: freg -> preg                    (**r double-precision VFP float registers *)
  | CR: crbit -> preg                   (**r bits in the condition register *)
  | PC: preg.                           (**r program counter *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.
Coercion CR: crbit >-> preg.
 *)

Inductive preg: Type :=
  | GPR: gpreg -> preg                  (**r general-purpose registers *)
  | PGPR: pgpreg -> preg                (**r general-purpose register pairs *)
  | PC: preg                            (**r program counter *)
  | RA: preg.                           (**r return addess register *)

Coercion GPR: gpreg >-> preg.
Coercion PGPR: pgpreg >-> preg.

(** Some target-independent proofs assume the existence of constructors [IR]
  and [FR]. For MPPA, we don't have a distinction between integer and
  floating-point registers. Map [IR] to the 32-bit [GPR] class and [FR] to
  the 64-bit [PGPR] register pair class. *)
Notation "'IR'" := GPR (only parsing) : asm.
Notation "'FR'" := PGPR (only parsing) : asm.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply gpreg_eq. apply pgpreg_eq. Defined.

Module PregEq.
  Definition t := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional name for the stack pointer register ([SP]). This is not used by
  the standard MPPA toolchain, but it makes our definitions below nicer to read. *)

Notation "'SP'" := GPR12 (only parsing) : asm.
(*
Notation "'RA'" := IR14 (only parsing) : asm.
*)

(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the MPPA processor. See the MPPA
  reference manuals for more details. *)

Definition label := positive.

(*
Inductive shift_op : Type :=
  | SOimm: int -> shift_op
  | SOreg: ireg -> shift_op
  | SOlsl: ireg -> int -> shift_op
  | SOlsr: ireg -> int -> shift_op
  | SOasr: ireg -> int -> shift_op
  | SOror: ireg -> int -> shift_op.
*)

(* The MPPA's load/store word instructions work for both [int] and [single],
  there are no separate instructions for these types. CompCert assumes
  typed memory accesses, so we use these tags to mark the intended data type
  of the access. They are ignored by the assembly printer. *)
Inductive word_typ: Type := Wint | Wsingle | Wany.

Definition word_chunk wt :=
  match wt with
  | Wint => Mint32
  | Wsingle => Mfloat32
  | Wany => Many32
  end.

Inductive dword_typ: Type := Dlong | Dfloat | Dany.

Definition dword_chunk dt :=
  match dt with
  | Dlong => Mint64
  | Dfloat => Mfloat64
  | Dany => Many64
  end.

Inductive reg_or_imm: Type :=
  | RIimm (i: int)
  | RIreg (r: gpreg).

Inductive preg_or_imm: Type :=
  | PRIimm (i: int64)
  | PRIreg (r: pgpreg).

(* Branch conditions *)
Inductive btest: Type :=
  | BTnez               (** not equal to zero *)
  | BTeqz               (** equal to zero *)
  | BTltz               (** less than zero *)
  | BTgez               (** greater than or equal to zero *)
  | BTlez               (** less than or equal to zero *)
  | BTgtz               (** greater than zero *)
  | BTodd               (** odd (LSB set) *)
  | BTeven.             (** even (LSB clear) *)

(* Integer comparisons *)
Inductive itest: Type :=
  | ITne                (**r not equal *)
  | ITeq                (**r equal *)
  | ITlt                (**r signed less than *)
  | ITge                (**r signed greater or equal *)
  | ITle                (**r signed less than or equal *)
  | ITgt                (**r signed greater *)
  | ITneu               (**r unsigned not equal *)
  | ITequ               (**r unsigned equal *)
  | ITltu               (**r unsigned less than *)
  | ITgeu               (**r unsigned greater or equal *)
  | ITleu               (**r unsigned less than or equal *)
  | ITgtu               (**r unsigned greater *)
  (* The following are not used yet. *)
  | ITall               (**r all bits set in mask *)
  | ITnall              (**r not all bits set in mask *)
  | ITany               (**r any bits set in mask *)
  | ITnone.             (**r not any bits set in mask *)

(* Floating-point comparisons *)
Inductive ftest: Type :=
  | FTone               (**r ordered and not equal *)
  | FTueq               (**r unordered or equal *)
  | FToeq               (**r ordered and equal *)
  | FTune               (**r unordered or not equal *)
  | FTolt               (**r ordered and less than *)
  | FTuge               (**r unordered or greater than or equal *)
  | FToge               (**r ordered and greater than or equal *)
  | FTult               (**r unordered or less than *)
  (* The next four constructors are not supported directly by the MPPA, but
     they are convenient for modeling of the semantics. The smart
     constructors [pfcomp] and [pfcompdl] in [Asmgen] make sure not to
     generate them. *)
  | FTole               (**r ordered and less than or equal *)
  | FTule               (**r unordered or less than or equal *)
  | FTogt               (**r ordered and greater than *)
  | FTugt.              (**r unordered or greater than *)

Inductive instruction : Type :=
  (* Branch control unit instructions *)
  | Pcall (symb: ident) (sig: signature)         (**r call subroutine *)
  | Pcb (t: btest) (r: gpreg) (l: label)         (**r conditional branch *)
  | Pcdb (t: btest) (r: pgpreg) (l: label)       (**r conditional branch on double-word *)
  | Pget (rd: gpreg) (rs: preg)                  (**r get system register *)
  | Pgoto (l: label)                             (**r unconditional branch *)
  | Picall (r: gpreg) (sig: signature)           (**r indirect call subroutine *)
  | Pret                                         (**r return *)
  | Pset (rd: preg) (rs: gpreg)                  (**r set system register *)
  (* Load-store unit instructions *)
  | Pld (t: dword_typ) (rd: pgpreg) (rbase: gpreg) (ofs: int)  (**r load double-word (immediate) *)
  | Plw (t: word_typ) (rd: gpreg) (rbase: gpreg) (ofs: int)    (**r load word (immediate) *)  (* FIXME: generalize *)
  | Psd (t: dword_typ) (rs: pgpreg) (rbase: gpreg) (ofs: int)  (**r load double-word (immediate) *)
  | Psw (t: word_typ) (rs: gpreg) (rbase: gpreg) (ofs: int)    (**r store word (immediate) *)  (* FIXME: generalize *)
  (* ALU instructions *)
  | Padd (rd r1: gpreg) (op2: reg_or_imm)        (**r integer addition *)
  | Paddd (rd r1: pgpreg) (op2: preg_or_imm)     (**r integer double-word addition *)
  | Pcomp (t: itest) (rd: gpreg) (r1: gpreg) (r2: reg_or_imm)     (**r integer comparison *)
  | Pcompdl (t: itest) (rd: gpreg) (r1: pgpreg) (r2: preg_or_imm)   (**r integer double-word comparison *)
  | Pmake (rd: gpreg) (n: int)                   (**r make integer constant *)
  | Pmaked (rd: pgpreg) (n: int64)               (**r make double-word integer constant *)
  | Pneg (rd r1: gpreg)                          (**r integer negation *)
  | Pnegd (rd r1: pgpreg)                        (**r integer double-word negation *)
  | Psbf (rd r1: gpreg) (op2: reg_or_imm)        (**r integer reverse subtraction (i.e., [op2 - r1]) *)
  | Psbfd (rd r1: pgpreg) (op2: preg_or_imm)     (**r integer double-word reverse subtraction *)
  (* Multiplier-ALU instructions *)
  | Pmulwdl (rd r1: gpreg) (op2: reg_or_imm)     (**r integer multiplication (32x32 bits, lower half) *)
  (* FPU instructions *)
  | Pfadd (rd r1 r2: gpreg)                      (**r 32-bit floating-point addition *)
  | Pfaddd (rd r1 r2: pgpreg)                    (**r 64-bit floating-point addition *)
  | Pfcomp (t: ftest) (rd: gpreg) (r1 r2: gpreg)     (**r 32-bit floating-point comparison *)
  | Pfcompdl (t: ftest) (rd: gpreg) (r1 r2: pgpreg)  (**r 64-bit floating-point comparison *)
  | Pfmul (rd r1 r2: gpreg)                      (**r 32-bit floating-point multiplication *)
  | Pfmuld (rd r1 r2: pgpreg)                    (**r 64-bit floating-point multiplication *)
  | Pfneg (rd r1: gpreg)                         (**r 32-bit floating-point negation *)
  | Pfnegd (rd r1: pgpreg)                       (**r 64-bit floating-point negation *)
  | Pfsbf (rd r1 r2: gpreg)                      (**r 32-bit floating-point reverse subtraction *)
  | Pfsbfd (rd r1 r2: pgpreg)                    (**r 64-bit floating-point reverse subtraction *)
  (* Synthetic instructions *)
  | Pcopy (rd r1: gpreg)                         (**r copy word *)
  | Pcopyd (rd r1: pgpreg)                       (**r copy double-word *)
  | Pfmake (rd: gpreg) (f: float32)              (**r make 32-bit floating-point constant *)
  | Pfmaked (rd: pgpreg) (f: float)              (**r make 64-bit floating-point constant *)
(*
  | Pand: ireg -> ireg -> shift_op -> instruction (**r bitwise and *)
  | Pasr: ireg -> ireg -> ireg -> instruction     (**r arithmetic shift right *)
  | Pb: label -> instruction                      (**r branch to label *)
  | Pbc: testcond -> label -> instruction            (**r conditional branch to label *)
  | Pbsymb: ident -> signature -> instruction                  (**r branch to symbol *)
  | Pbreg: ireg -> signature -> instruction                    (**r computed branch *)
  | Pblsymb: ident -> signature -> instruction                 (**r branch and link to symbol *)
  | Pblreg: ireg -> signature -> instruction                   (**r computed branch and link *)
  | Pbic: ireg -> ireg -> shift_op -> instruction (**r bitwise bit-clear *)
  | Pcmp: ireg -> shift_op -> instruction         (**r integer comparison *)
  | Peor: ireg -> ireg -> shift_op -> instruction (**r bitwise exclusive or *)
  | Pldr: ireg -> ireg -> shift_op -> instruction (**r int32 load *)
  | Pldr_a: ireg -> ireg -> shift_op -> instruction (**r any32 load to int register *)
  | Pldrb: ireg -> ireg -> shift_op -> instruction (**r unsigned int8 load *)
  | Pldrh: ireg -> ireg -> shift_op -> instruction (**r unsigned int16 load *)
  | Pldrsb: ireg -> ireg -> shift_op -> instruction (**r signed int8 load *)
  | Pldrsh: ireg -> ireg -> shift_op -> instruction (**r unsigned int16 load *)
  | Plsl: ireg -> ireg -> ireg -> instruction       (**r shift left *)
  | Plsr: ireg -> ireg -> ireg -> instruction       (**r logical shift right *)
  | Pmla: ireg -> ireg -> ireg -> ireg -> instruction      (**r integer multiply-add *)
  | Pmov: ireg -> shift_op -> instruction          (**r integer move *)
  | Pmovw: ireg -> int -> instruction              (**r move 16-bit immediate *)
  | Pmovt: ireg -> int -> instruction              (**r set high 16 bits *)
  | Pmul: ireg -> ireg -> ireg -> instruction      (**r integer multiplication *)
  | Pmvn: ireg -> shift_op -> instruction          (**r integer complement *)
  | Porr: ireg -> ireg -> shift_op -> instruction  (**r bitwise or *)
  | Ppush: list ireg -> instruction (** push registers on the stack instruction *)
  | Prsb: ireg -> ireg -> shift_op -> instruction  (**r integer reverse subtraction *)
  | Psbfx: ireg -> ireg -> int -> int -> instruction (**r signed bitfield extract *)
  | Pstr: ireg -> ireg -> shift_op -> instruction (**r int32 store *)
  | Pstr_a: ireg -> ireg -> shift_op -> instruction (**r any32 store from int register *)
  | Pstrb: ireg -> ireg -> shift_op -> instruction (**r int8 store *)
  | Pstrh: ireg -> ireg -> shift_op -> instruction (**r int16 store *)
  | Psdiv: instruction                              (**r signed division *)
  | Psmull: ireg -> ireg -> ireg -> ireg -> instruction (**r signed multiply long *)
  | Psub: ireg -> ireg -> shift_op -> instruction  (**r integer subtraction *)
  | Pudiv: instruction                             (**r unsigned division *)
  | Pumull: ireg -> ireg -> ireg -> ireg -> instruction (**r unsigned multiply long *)
  (* Floating-point coprocessor instructions (VFP double scalar operations) *)
  | Pfcpyd: freg -> freg -> instruction             (**r float move *)
  | Pfabsd: freg -> freg -> instruction             (**r float absolute value *)
  | Pfnegd: freg -> freg -> instruction             (**r float opposite *)
  | Pfaddd: freg -> freg -> freg -> instruction     (**r float addition *)
  | Pfdivd: freg -> freg -> freg -> instruction     (**r float division *)
  | Pfmuld: freg -> freg -> freg -> instruction     (**r float multiplication *)
  | Pfsubd: freg -> freg -> freg -> instruction     (**r float subtraction *)
  | Pflid: freg -> float -> instruction             (**r load float constant *)
  | Pfcmpd: freg -> freg -> instruction             (**r float comparison *)
  | Pfcmpzd: freg -> instruction                    (**r float comparison with 0.0 *)
  | Pfsitod: freg -> ireg -> instruction            (**r signed int to float *)
  | Pfuitod: freg -> ireg -> instruction            (**r unsigned int to float *)
  | Pftosizd: ireg -> freg -> instruction           (**r float to signed int *)
  | Pftouizd: ireg -> freg -> instruction           (**r float to unsigned int *)
  | Pfabss: freg -> freg -> instruction             (**r float absolute value *)
  | Pfnegs: freg -> freg -> instruction             (**r float opposite *)
  | Pfadds: freg -> freg -> freg -> instruction     (**r float addition *)
  | Pfdivs: freg -> freg -> freg -> instruction     (**r float division *)
  | Pfmuls: freg -> freg -> freg -> instruction     (**r float multiplication *)
  | Pfsubs: freg -> freg -> freg -> instruction     (**r float subtraction *)
  | Pflis: freg -> float32 -> instruction           (**r load float constant *)
  | Pfcmps: freg -> freg -> instruction             (**r float comparison *)
  | Pfcmpzs: freg -> instruction                    (**r float comparison with 0.0 *)
  | Pfsitos: freg -> ireg -> instruction            (**r signed int to float *)
  | Pfuitos: freg -> ireg -> instruction            (**r unsigned int to float *)
  | Pftosizs: ireg -> freg -> instruction           (**r float to signed int *)
  | Pftouizs: ireg -> freg -> instruction           (**r float to unsigned int *)
  | Pfcvtsd: freg -> freg -> instruction            (**r round to single precision *)
  | Pfcvtds: freg -> freg -> instruction            (**r expand to double precision *)
  | Pfldd: freg -> ireg -> int -> instruction       (**r float64 load *)
  | Pfldd_a: freg -> ireg -> int -> instruction     (**r any64 load to FP reg *)
  | Pflds: freg -> ireg -> int -> instruction       (**r float32 load *)
  | Pfstd: freg -> ireg -> int -> instruction       (**r float64 store *)
  | Pfstd_a: freg -> ireg -> int -> instruction     (**r any64 store from FP reg *)
  | Pfsts: freg -> ireg -> int -> instruction       (**r float32 store *)
*)

  (* Pseudo-instructions *)
  | Pallocframe (sz: Z) (pos: ptrofs)               (**r allocate new stack frame *)
  | Pfreeframe (sz: Z) (pos: ptrofs)                (**r deallocate stack frame and restore previous frame *)
  | Plabel (l: label)                               (**r define a code label *)
  | Pbuiltin (ef: external_function) (args: list (builtin_arg preg)) (res: builtin_res preg)
                                                    (**r built-in function (pseudo) *)
  | Ploadsymbol (rd: gpreg) (sym: ident) (ofs: ptrofs)  (**r load the address of a symbol *)
(*
  | Pmovite: testcond -> ireg -> shift_op -> shift_op -> instruction (**r integer conditional move *)
  | Pbtbl: ireg -> list label -> instruction       (**r N-way branch through a jump table *)
  | Padc: ireg -> ireg -> shift_op -> instruction     (**r add with carry *)
  | Pcfi_adjust: int -> instruction                   (**r .cfi_adjust debug directive *)
  | Pclz: ireg -> ireg -> instruction                 (**r count leading zeros. *)
  | Pfsqrt: freg -> freg -> instruction               (**r floating-point square root. *)
  | Prev: ireg -> ireg -> instruction                 (**r reverse bytes and reverse bits. *)
  | Prev16: ireg -> ireg -> instruction               (**r reverse bytes and reverse bits. *)
  | Prsc: ireg -> ireg -> shift_op -> instruction     (**r reverse subtract without carry. *)
  | Psbc: ireg -> ireg -> shift_op -> instruction     (**r add with carry *)
  (* Add, sub, rsb versions with s suffix *)
  | Padds: ireg -> ireg -> shift_op -> instruction    (**r integer addition with update of condition flags *)
  | Psubs: ireg -> ireg -> shift_op -> instruction    (**r integer subtraction with update of condition flags *)
  | Prsbs: ireg -> ireg -> shift_op -> instruction    (**r integer reverse subtraction with update of condition flags *)
  | Pdmb: instruction                                 (**r data memory barrier *)
  | Pdsb: instruction                                 (**r data synchronization barrier *)
  | Pisb: instruction                                 (**r instruction synchronization barrier *)
  | Pbne: label -> instruction                        (**r branch if negative macro *)
  | Pldr_p: ireg -> ireg -> shift_op -> instruction   (**r int32 load with post increment *)
  | Pldrb_p: ireg -> ireg -> shift_op -> instruction  (**r unsigned int8 load with post increment *)
  | Pldrh_p: ireg -> ireg -> shift_op -> instruction  (**r unsigned int16 load with post increment *)
  | Pstr_p: ireg -> ireg -> shift_op -> instruction   (**r int32 store with post increment *)
  | Pstrb_p: ireg -> ireg -> shift_op -> instruction  (**r unsigned int8 store with post increment *)
  | Pstrh_p: ireg -> ireg -> shift_op -> instruction. (**r unsigned int16 store with post increment *)
*)
  .



(** The pseudo-instructions are the following:

- [Plabel]: define a code label at the current program point.
- [Ploadsymbol]: load the address of a symbol plus an offset into an integer
  register. Expands to a [make] instruction and an add of the offset if it is
  nonzero:
<<
        make $rd = symbol
        add $rd = $rd, offset    # if offset <> 0
>>
  Initialized data in the constant data section are not modeled here,
  which is why we use a pseudo-instruction for this purpose.
- [Pallocframe sz pos]: in the formal semantics, this pseudo-instruction
  allocates a memory block with bounds [0] and [sz], stores the value
  of the stack pointer at offset [pos] in this block, and sets the
  stack pointer ([$r12]) to the address of the bottom of this block.
  Note: On MPPA, the stack pointer must always be aligned on an 8-byte boundary,
  and [sz] must always be a multiple of 8. MPPA also expects functions to
  allocate an extra 16-byte scratch region for their callees. (In leaf functions
  this is optional.) These 16 bytes must either be included in [sz] or added here.
  In the printed ASM assembly code, this allocation is:
<<
        add $r12 = $r12, -sz
        ;;
        sw pos[$r12] = $r12
        ;;
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.
- [Pfreeframe sz pos]: in the formal semantics, this pseudo-instruction
  reads the word at [pos] of the block pointed by the stack pointer,
  frees this block, and sets the stack pointer to the value read.
  In the printed ASM assembly code, this freeing is:
<<
        lw $r12 = pos[$r12]
        ;;
        add $r12 = $r12, sz
        ;;
>>
  Again, our memory model cannot comprehend that this operation
  frees (logically) the current stack frame.
- [Pbtbl reg table]: this is a N-way branch, implemented via a jump table
  as follows:
<<
  FIXME for MPPA
        ldr     pc, [pc, reg]
        mov     r0, r0          (* no-op *)
        .word   table[0], table[1], ...
>>
  Note that [reg] contains 4 times the index of the desired table entry.
*)

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and condition bits to either [Vzero] or [Vone]. *)

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Variable ge: genv.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _ => Stuck
    end
  end.

(** Evaluation of register-or-immediate operands *)

Definition eval_reg_or_imm (ri: reg_or_imm) (rs: regset) :=
  match ri with
  | RIimm n => Vint n
  | RIreg r => rs#r
  end.

Definition eval_preg_or_imm (pi: preg_or_imm) (rs: regset) :=
  match pi with
  | PRIimm n => Vlong n
  | PRIreg r => rs#r
  end.

(** Auxiliaries for memory accesses *)

Definition exec_load (chunk: memory_chunk) (addr: val) (r: preg)
                     (rs: regset) (m: mem) :=
  match Mem.loadv chunk m addr with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- v)) m
  end.

Definition exec_store (chunk: memory_chunk) (addr: val) (r: preg)
                      (rs: regset) (m: mem) :=
  match Mem.storev chunk m addr (rs r) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

(** Comparisons. *)

Definition eval_branch_condition (t: btest) (v: val): option bool :=
  match v with
  | Vint n =>
    match t with
    | BTnez  => Some (negb (Int.eq n Int.zero))
    | BTeqz  => Some (Int.eq n Int.zero)
    | BTltz  => Some (Int.lt n Int.zero)
    | BTgez  => Some (negb (Int.lt n Int.zero))
    | BTlez  => Some (negb (Int.lt Int.zero n))
    | BTgtz  => Some (Int.lt Int.zero n)
    | BTodd  => Some (Z.odd (Int.unsigned n))
    | BTeven => Some (Z.even (Int.unsigned n))
    end
  | Vlong n =>
    match t with
    | BTnez  => Some (negb (Int64.eq n Int64.zero))
    | BTeqz  => Some (Int64.eq n Int64.zero)
    | BTltz  => Some (Int64.lt n Int64.zero)
    | BTgez  => Some (negb (Int64.lt n Int64.zero))
    | BTlez  => Some (negb (Int64.lt Int64.zero n))
    | BTgtz  => Some (Int64.lt Int64.zero n)
    | BTodd  => Some (Z.odd (Int64.unsigned n))
    | BTeven => Some (Z.even (Int64.unsigned n))
    end
  | _ => None
  end.

Definition itest_for_cmp (c: comparison) :=
  match c with
  | Cne => ITne
  | Ceq => ITeq
  | Clt => ITlt
  | Cge => ITge
  | Cle => ITle
  | Cgt => ITgt
  end.

Definition uitest_for_cmp (c: comparison) :=
  match c with
  | Cne => ITneu
  | Ceq => ITequ
  | Clt => ITltu
  | Cge => ITgeu
  | Cle => ITleu
  | Cgt => ITgtu
  end.

Definition compare_int (t: itest) (v1 v2: val) (m: mem): val :=
  match t with
  | ITne  => Val.cmp Cne v1 v2
  | ITeq  => Val.cmp Ceq v1 v2
  | ITlt  => Val.cmp Clt v1 v2
  | ITge  => Val.cmp Cge v1 v2
  | ITle  => Val.cmp Cle v1 v2
  | ITgt  => Val.cmp Cgt v1 v2
  | ITneu => Val.cmpu (Mem.valid_pointer m) Cne v1 v2
  | ITequ => Val.cmpu (Mem.valid_pointer m) Ceq v1 v2
  | ITltu => Val.cmpu (Mem.valid_pointer m) Clt v1 v2
  | ITgeu => Val.cmpu (Mem.valid_pointer m) Cge v1 v2
  | ITleu => Val.cmpu (Mem.valid_pointer m) Cle v1 v2
  | ITgtu => Val.cmpu (Mem.valid_pointer m) Cgt v1 v2
  | ITall
  | ITnall
  | ITany
  | ITnone => Vundef
  end.

Definition compare_long (t: itest) (v1 v2: val) (m: mem): val :=
  match t with
  | ITne  => Val.of_optbool (Val.cmpl_bool Cne v1 v2)
  | ITeq  => Val.of_optbool (Val.cmpl_bool Ceq v1 v2)
  | ITlt  => Val.of_optbool (Val.cmpl_bool Clt v1 v2)
  | ITge  => Val.of_optbool (Val.cmpl_bool Cge v1 v2)
  | ITle  => Val.of_optbool (Val.cmpl_bool Cle v1 v2)
  | ITgt  => Val.of_optbool (Val.cmpl_bool Cgt v1 v2)
  | ITneu => Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Cne v1 v2)
  | ITequ => Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Ceq v1 v2)
  | ITltu => Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Clt v1 v2)
  | ITgeu => Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Cge v1 v2)
  | ITleu => Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Cle v1 v2)
  | ITgtu => Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Cgt v1 v2)
  | ITall
  | ITnall
  | ITany
  | ITnone => Vundef
  end.

Definition ftest_for_cmp (c: comparison) :=
  match c with
  | Cne => FTone
  | Ceq => FToeq
  | Clt => FTolt
  | Cge => FToge
  | Cle => FTole
  | Cgt => FTogt
  end.

Definition ftest_for_not_cmp (c: comparison) :=
  match c with
  | Cne => FTueq
  | Ceq => FTune
  | Clt => FTuge
  | Cge => FTult
  | Cle => FTugt
  | Cgt => FTule
  end.

Definition compare_single (t: ftest) (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 =>
    match t with
    | FTone => Val.of_bool (Float32.cmp Cne f1 f2)
    | FTueq => Val.of_bool (negb (Float32.cmp Cne f1 f2))
    | FToeq => Val.of_bool (Float32.cmp Ceq f1 f2)
    | FTune => Val.of_bool (negb (Float32.cmp Ceq f1 f2))
    | FTolt => Val.of_bool (Float32.cmp Clt f1 f2)
    | FTuge => Val.of_bool (negb (Float32.cmp Clt f1 f2))
    | FToge => Val.of_bool (Float32.cmp Cge f1 f2)
    | FTult => Val.of_bool (negb (Float32.cmp Cge f1 f2))
    | FTole => Val.of_bool (Float32.cmp Cle f1 f2)
    | FTule => Val.of_bool (negb (Float32.cmp Cgt f1 f2))
    | FTogt => Val.of_bool (Float32.cmp Cgt f1 f2)
    | FTugt => Val.of_bool (negb (Float32.cmp Cle f1 f2))
    end
  | _, _ => Vundef
  end.

Definition compare_float (t: ftest) (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 =>
    match t with
    | FTone => Val.of_bool (Float.cmp Cne f1 f2)
    | FTueq => Val.of_bool (negb (Float.cmp Cne f1 f2))
    | FToeq => Val.of_bool (Float.cmp Ceq f1 f2)
    | FTune => Val.of_bool (negb (Float.cmp Ceq f1 f2))
    | FTolt => Val.of_bool (Float.cmp Clt f1 f2)
    | FTuge => Val.of_bool (negb (Float.cmp Clt f1 f2))
    | FToge => Val.of_bool (Float.cmp Cge f1 f2)
    | FTult => Val.of_bool (negb (Float.cmp Cge f1 f2))
    | FTole => Val.of_bool (Float.cmp Cle f1 f2)
    | FTule => Val.of_bool (negb (Float.cmp Cgt f1 f2))
    | FTogt => Val.of_bool (Float.cmp Cgt f1 f2)
    | FTugt => Val.of_bool (negb (Float.cmp Cle f1 f2))
    end
  | _, _ => Vundef
  end.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual MPPA instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the MPPA reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the MPPA code we
    generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction.
*)

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (* Branch control unit instructions *)
  | Pcall symb sig =>
    Next (rs#RA <- (Val.add rs#PC Vone)
            #PC <- (Genv.symbol_address ge symb Ptrofs.zero)) m
  | Pcb t r lbl | Pcdb t r lbl =>
    match eval_branch_condition t rs#r with
    | Some true => goto_label f lbl rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
    end
  | Pget rd r1 =>
    (* Only allow get from [RA] for now. *)
    match r1 with
    | RA => Next (nextinstr (rs#rd <- (rs#r1))) m
    | _ => Stuck
    end
  | Pgoto lbl =>
    goto_label f lbl rs m
  | Picall r sig =>
    Next (rs#RA <- (Val.add rs#PC Vone)
            #PC <- (rs#r)) m
  | Pret =>
      Next (rs#PC <- (rs#RA)) m
  | Pset rd r1 =>
    (* Only allow to set [RA] for now. *)
    match rd with
    | RA => Next (nextinstr (rs#rd <- (rs#r1))) m
    | _ => Stuck
    end
  (* Load-store unit instructions *)
  | Pld t rd rbase ofs =>
    exec_load (dword_chunk t) (Val.add rs#rbase (Vint ofs)) rd rs m
  | Plw t rd rbase ofs =>
    exec_load (word_chunk t) (Val.add rs#rbase (Vint ofs)) rd rs m
  | Psd t rd rbase ofs =>
    exec_store (dword_chunk t) (Val.add rs#rbase (Vint ofs)) rd rs m
  | Psw t rd rbase ofs =>
    exec_store (word_chunk t) (Val.add rs#rbase (Vint ofs)) rd rs m
  (* ALU instructions *)
  | Padd rd r1 op2 =>
    let op2 := eval_reg_or_imm op2 rs in
    Next (nextinstr (rs#rd <- (Val.add rs#r1 op2))) m
  | Paddd rd r1 op2 =>
    let op2 := eval_preg_or_imm op2 rs in
    Next (nextinstr (rs#rd <- (Val.addl rs#r1 op2))) m
  | Pcomp t rd r1 op2 =>
    let op2 := eval_reg_or_imm op2 rs in
    Next (nextinstr (rs#rd <- (compare_int t rs#r1 op2 m))) m
  | Pcompdl t rd r1 op2 =>
    let op2 := eval_preg_or_imm op2 rs in
    Next (nextinstr (rs#rd <- (compare_long t rs#r1 op2 m))) m
  | Pmake rd n =>
    Next (nextinstr (rs#rd <- (Vint n))) m
  | Pmaked rd n =>
    Next (nextinstr (rs#rd <- (Vlong n))) m
  | Pneg rd r1 =>
    Next (nextinstr (rs#rd <- (Val.neg rs#r1))) m
  | Pnegd rd r1 =>
    Next (nextinstr (rs#rd <- (Val.negl rs#r1))) m
  | Psbf rd r1 op2 =>
    let op2 := eval_reg_or_imm op2 rs in
    Next (nextinstr (rs#rd <- (Val.sub op2 rs#r1))) m
  | Psbfd rd r1 op2 =>
    let op2 := eval_preg_or_imm op2 rs in
    Next (nextinstr (rs#rd <- (Val.subl op2 rs#r1))) m
  (* Multiplier-ALU instructions *)
  | Pmulwdl rd r1 op2 =>
    let op2 := eval_reg_or_imm op2 rs in
    Next (nextinstr (rs#rd <- (Val.mul rs#r1 op2))) m
  (* FPU instructions *)
  | Pfadd rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.addfs rs#r1 rs#r2))) m
  | Pfaddd rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.addf rs#r1 rs#r2))) m
  | Pfcomp t rd r1 r2 =>
    Next (nextinstr (rs#rd <- (compare_single t rs#r1 rs#r2))) m
  | Pfcompdl t rd r1 r2 =>
    Next (nextinstr (rs#rd <- (compare_float t rs#r1 rs#r2))) m
  | Pfmul rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.mulfs rs#r1 rs#r2))) m
  | Pfmuld rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.mulf rs#r1 rs#r2))) m
  | Pfneg rd r1 =>
    Next (nextinstr (rs#rd <- (Val.negfs rs#r1))) m
  | Pfnegd rd r1 =>
    Next (nextinstr (rs#rd <- (Val.negf rs#r1))) m
  | Pfsbf rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.subfs rs#r2 rs#r1))) m
  | Pfsbfd rd r1 r2 =>
    Next (nextinstr (rs#rd <- (Val.subf rs#r2 rs#r1))) m
  (* Synthetic instructions *)
  | Pcopy rd r1 =>
    Next (nextinstr (rs#rd <- (rs#r1))) m
  | Pcopyd rd r1 =>
    Next (nextinstr (rs#rd <- (rs#r1))) m
  | Pfmake rd f =>
    Next (nextinstr (rs#rd <- (Vsingle f))) m
  | Pfmaked rd f =>
    Next (nextinstr (rs#rd <- (Vfloat f))) m
  (* Pseudo-instructions *)
  | Pallocframe sz pos =>
    let (m1, stk) := Mem.alloc m 0 sz in
    let sp := (Vptr stk Ptrofs.zero) in
    match Mem.storev Mint32 m1 (Val.offset_ptr sp pos) rs#SP with
    | None => Stuck
    | Some m2 => Next (nextinstr (rs#SP <- sp)) m2
    end
  | Pfreeframe sz pos =>
    match Mem.loadv Mint32 m (Val.offset_ptr rs#SP pos) with
    | None => Stuck
    | Some v =>
        match rs#SP with
        | Vptr stk ofs =>
          match Mem.free m stk 0 sz with
          | None => Stuck
          | Some m' => Next (nextinstr (rs#SP <- v)) m'
          end
        | _ => Stuck
        end
    end
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Pbuiltin ef args res => Stuck   (**r treated specially below *)
  | Ploadsymbol rd sym ofs =>
    Next (nextinstr (rs#rd <- (Genv.symbol_address ge sym ofs))) m
  (*| _ => Stuck*)
  end.

(** Translation of the LTL/Linear/Mach view of machine registers to the MPPA
  view. Note that no LTL register maps to [GPR10] to [GPR15]. These registers
  are reserved as temporaries, to be used by the generated MPPA code.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | R0  => GPR0
  | R1  => GPR1
  | R2  => GPR2
  | R3  => GPR3
  | R4  => GPR4
  | R5  => GPR5
  | R6  => GPR6
  | R7  => GPR7
  | R8  => GPR8
  | R9  => GPR9
  | R15 => GPR15
  | R16 => GPR16
  | R17 => GPR17
  | R18 => GPR18
  | R19 => GPR19
  | R20 => GPR20
  | R21 => GPR21
  | R22 => GPR22
  | R23 => GPR23
  | R24 => GPR24
  | R25 => GPR25
  | R26 => GPR26
  | R27 => GPR27
  | R28 => GPR28
  | R29 => GPR29
  | R30 => GPR30
  | R31 => GPR31
  | R32 => GPR32
  | R33 => GPR33
  | R34 => GPR34
  | R35 => GPR35
  | R36 => GPR36
  | R37 => GPR37
  | R38 => GPR38
  | R39 => GPR39
  | R40 => GPR40
  | R41 => GPR41
  | R42 => GPR42
  | R43 => GPR43
  | R44 => GPR44
  | R45 => GPR45
  | R46 => GPR46
  | R47 => GPR47
  | R48 => GPR48
  | R49 => GPR49
  | R50 => GPR50
  | R51 => GPR51
  | R52 => GPR52
  | R53 => GPR53
  | R54 => GPR54
  | R55 => GPR55
  | R56 => GPR56
  | R57 => GPR57
  | R58 => GPR58
  | R59 => GPR59
  | R60 => GPR60
  | R61 => GPR61
  | R62 => GPR62
  | R63 => GPR63
  | R0R1   => PGPR0R1
  | R2R3   => PGPR2R3
  | R4R5   => PGPR4R5
  | R6R7   => PGPR6R7
  | R8R9   => PGPR8R9
  | R16R17 => PGPR16R17
  | R18R19 => PGPR18R19
  | R20R21 => PGPR20R21
  | R22R23 => PGPR22R23
  | R24R25 => PGPR24R25
  | R26R27 => PGPR26R27
  | R28R29 => PGPR28R29
  | R30R31 => PGPR30R31
  | R32R33 => PGPR32R33
  | R34R35 => PGPR34R35
  | R36R37 => PGPR36R37
  | R38R39 => PGPR38R39
  | R40R41 => PGPR40R41
  | R42R43 => PGPR42R43
  | R44R45 => PGPR44R45
  | R46R47 => PGPR46R47
  | R48R49 => PGPR48R49
  | R50R51 => PGPR50R51
  | R52R53 => PGPR52R53
  | R54R55 => PGPR54R55
  | R56R57 => PGPR56R57
  | R58R59 => PGPR58R59
  | R60R61 => PGPR60R61
  | R62R63 => PGPR62R63
  end.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use MPPA registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr (rs#SP) (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs#SP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res rs)#PC <- (rs#RA) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # RA <- Vzero
        # SP <- Vzero in
      Genv.init_mem p = Some m0 ->
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vzero ->
      rs#GPR0 = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
(* determ *)
  (* exec_step_internal *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  (* exec_step_builtin *)
  discriminate.
  discriminate.
  assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  (* exec_step_external *)
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
(* trace length *)
  red; intros; inv H; simpl.
  omega.
  inv H3; eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
(* initial states *)
  inv H; inv H0. f_equal. congruence.
(* final no step *)
  inv H. unfold Vzero in H0. red; intros; red; intros. inv H; congruence.
(* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)
(* FIXME: What to do with the superregister containing the stack pointer? Should
  we model pairs of reserved registers at all? *)
Definition data_preg (r: preg) : bool :=
  match r with
  | GPR (GPR10 | GPR11 | GPR13 | GPR14) => false
  | PGPR (PGPR10R11 | PGPR12R13 | PGPR14R15) => false
  | SP => true
  | GPR _ | PGPR _ => true
  | PC => false
  | RA => false
  end.


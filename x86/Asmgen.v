(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Translation from Mach to IA32 assembly language *)

Require Import Coqlib Errors.
Require Import AST Integers Floats Memdata.
Require Import Op Locations Mach Asm.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

(** The code generation functions take advantage of several characteristics of the [Mach] code generated by earlier passes of the compiler:
- Argument and result registers are of the correct type.
- For two-address instructions, the result and the first argument
  are in the same register.  (True by construction in [RTLgen], and preserved by [Reload].)
- The top of the floating-point stack ([ST0], a.k.a. [FP0]) can only
  appear in [mov] instructions, but never in arithmetic instructions.

All these properties are true by construction, but it is painful to track them statically.  Instead, we recheck them during code generation and fail if they do not hold.
*)

(** Extracting integer or float registers. *)

Definition ireg_of (r: mreg) : res ireg :=
  match preg_of r with IR mr => OK mr | _ => Error(msg "Asmgen.ireg_of") end.

Definition freg_of (r: mreg) : res freg :=
  match preg_of r with FR mr => OK mr | _ => Error(msg "Asmgen.freg_of") end.

(** Smart constructors for some operations. *)

Definition mk_mov (rd rs: preg) (k: code) : res code :=
  match rd, rs with
  | IR rd, IR rs => OK (Pmov_rr rd rs :: k)
  | FR rd, FR rs => OK (Pmovsd_ff rd rs :: k)
  | _, _ => Error(msg "Asmgen.mk_mov")
  end.

Definition mk_shrximm (n: int) (k: code) : res code :=
  let p := Int.sub (Int.shl Int.one n) Int.one in
  OK (Ptestl_rr RAX RAX ::
      Pleal RCX (Addrmode (Some RAX) None (inl _ (Int.unsigned p))) ::
      Pcmov Cond_l RAX RCX ::
      Psarl_ri RAX n :: k).

Definition mk_shrxlimm (n: int) (k: code) : res code :=
  OK (if Int.eq n Int.zero then Pmov_rr RAX RAX :: k else
      Pcqto ::
      Pshrq_ri RDX (Int.sub (Int.repr 64) n) ::
      Pleaq RAX (Addrmode (Some RAX) (Some(RDX, 1)) (inl _ 0)) ::
      Psarq_ri RAX n :: k).

Definition low_ireg (r: ireg) : bool :=
  match r with RAX | RBX | RCX | RDX => true | _ => false end.

Definition mk_intconv (mk: ireg -> ireg -> instruction) (rd rs: ireg) (k: code) :=
  if Archi.ptr64 || low_ireg rs then
    OK (mk rd rs :: k)
  else
    OK (Pmov_rr RAX rs :: mk rd RAX :: k).

Definition addressing_mentions (addr: addrmode) (r: ireg) : bool :=
  match addr with Addrmode base displ const =>
      match base with Some r' => ireg_eq r r' | None => false end
   || match displ with Some(r', sc) => ireg_eq r r' | None => false end
  end.

Definition mk_storebyte (addr: addrmode) (rs: ireg) (k: code) :=
  if Archi.ptr64 || low_ireg rs then
    OK (Pmovb_mr addr rs :: k)
  else if addressing_mentions addr RAX then
    OK (Pleal RCX addr :: Pmov_rr RAX rs ::
        Pmovb_mr (Addrmode (Some RCX) None (inl _ 0)) RAX :: k)
  else
    OK (Pmov_rr RAX rs :: Pmovb_mr addr RAX :: k).

(** Accessing slots in the stack frame. *)

Definition loadind (base: ireg) (ofs: ptrofs) (q: quantity) (dst: mreg) (k: code) :=
  let a := Addrmode (Some base) None (inl _ (Ptrofs.unsigned ofs)) in
  match q, preg_of dst with
  | Q32, IR r => OK (Pmovl_rm_a r a :: k)
  | Q64, IR r => if Archi.ptr64 then OK (Pmovq_rm_a r a :: k) else Error (msg "Asmgen.loadind2")
  | Q32, FR r => OK (Pmovss_fm_a r a :: k)
  | Q32, ST0  => OK (Pflds_m_a a :: k)
  | Q64, FR r => OK (Pmovsd_fm_a r a :: k)
  | Q64, ST0  => OK (Pfldl_m_a a :: k)
  | _, _ => Error (msg "Asmgen.loadind")
  end.

Definition storeind (src: mreg) (base: ireg) (ofs: ptrofs) (q: quantity) (k: code) :=
  let a := Addrmode (Some base) None (inl _ (Ptrofs.unsigned ofs)) in
  match q, preg_of src with
  | Q32, IR r => OK (Pmovl_mr_a a r :: k)
  | Q64, IR r => if Archi.ptr64 then OK (Pmovq_mr_a a r :: k) else Error (msg "Asmgen.storeind2")
  | Q32, FR r => OK (Pmovss_mf_a a r :: k)
  | Q32, ST0  => OK (Pfstps_m_a a :: k)
  | Q64, FR r => OK (Pmovsd_mf_a a r :: k)
  | Q64, ST0  => OK (Pfstpl_m_a a :: k)
  | _, _ => Error (msg "Asmgen.storeind")
  end.

(** Translation of addressing modes *)

Definition transl_addressing (a: addressing) (args: list mreg): res addrmode :=
  match a, args with
  | Aindexed n, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode (Some r1) None (inl _ n))
  | Aindexed2 n, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK(Addrmode (Some r1) (Some(r2, 1)) (inl _ n))
  | Ascaled sc n, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode None (Some(r1, sc)) (inl _ n))
  | Aindexed2scaled sc n, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK(Addrmode (Some r1) (Some(r2, sc)) (inl _ n))
  | Aglobal id ofs, nil =>
      OK(Addrmode None None (inr _ (id, ofs)))
  | Abased id ofs, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode (Some r1) None (inr _ (id, ofs)))
  | Abasedscaled sc id ofs, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode None (Some(r1, sc)) (inr _ (id, ofs)))
  | Ainstack n, nil =>
      OK(Addrmode (Some RSP) None (inl _ (Ptrofs.signed n)))
  | _, _ =>
      Error(msg "Asmgen.transl_addressing")
  end.

Definition normalize_addrmode_32 (a: addrmode) :=
  match a with
  | Addrmode base ofs (inl n) =>
      Addrmode base ofs (inl _ (Int.signed (Int.repr n)))
  | Addrmode base ofs (inr _) =>
      a
  end.

Definition normalize_addrmode_64 (a: addrmode) :=
  match a with
  | Addrmode base ofs (inl n) =>
      if Op.offset_in_range n
      then (a, None)
      else (Addrmode base ofs (inl _ 0), Some (Int64.repr n))
  | Addrmode base ofs (inr (id, delta)) =>
      if Op.ptroffset_in_range delta || negb Archi.ptr64
      then (a, None)
      else (Addrmode base ofs (inr _ (id, Ptrofs.zero)), Some (Ptrofs.to_int64 delta))
  end.

(** Floating-point comparison.  We swap the operands in some cases
   to simplify the handling of the unordered case. *)

Definition floatcomp (cmp: comparison) (r1 r2: freg) : instruction :=
  match cmp with
  | Clt | Cle => Pcomisd_ff r2 r1
  | Ceq | Cne | Cgt | Cge => Pcomisd_ff r1 r2
  end.

Definition floatcomp32 (cmp: comparison) (r1 r2: freg) : instruction :=
  match cmp with
  | Clt | Cle => Pcomiss_ff r2 r1
  | Ceq | Cne | Cgt | Cge => Pcomiss_ff r1 r2
  end.

(** Translation of a condition.  Prepends to [k] the instructions
  that evaluate the condition and leave its boolean result in bits
  of the condition register. *)

Definition transl_cond
              (cond: condition) (args: list mreg) (k: code) : res code :=
  match cond, args with
  | Ccomp c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2; OK (Pcmpl_rr r1 r2 :: k)
  | Ccompu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2; OK (Pcmpl_rr r1 r2 :: k)
  | Ccompimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int.eq_dec n Int.zero then Ptestl_rr r1 r1 :: k else Pcmpl_ri r1 n :: k)
  | Ccompuimm c n, a1 :: nil =>
      do r1 <- ireg_of a1; OK (Pcmpl_ri r1 n :: k)
  | Ccompl c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2; OK (Pcmpq_rr r1 r2 :: k)
  | Ccomplu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2; OK (Pcmpq_rr r1 r2 :: k)
  | Ccomplimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int64.eq_dec n Int64.zero then Ptestq_rr r1 r1 :: k else Pcmpq_ri r1 n :: k)
  | Ccompluimm c n, a1 :: nil =>
      do r1 <- ireg_of a1; OK (Pcmpq_ri r1 n :: k)
  | Ccompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; OK (floatcomp cmp r1 r2 :: k)
  | Cnotcompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; OK (floatcomp cmp r1 r2 :: k)
  | Ccompfs cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; OK (floatcomp32 cmp r1 r2 :: k)
  | Cnotcompfs cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; OK (floatcomp32 cmp r1 r2 :: k)
  | Cmaskzero n, a1 :: nil =>
      do r1 <- ireg_of a1; OK (Ptestl_ri r1 n :: k)
  | Cmasknotzero n, a1 :: nil =>
      do r1 <- ireg_of a1; OK (Ptestl_ri r1 n :: k)
  | _, _ =>
     Error(msg "Asmgen.transl_cond")
  end.

(** What processor condition to test for a given Mach condition. *)

Definition testcond_for_signed_comparison (cmp: comparison) :=
  match cmp with
  | Ceq => Cond_e
  | Cne => Cond_ne
  | Clt => Cond_l
  | Cle => Cond_le
  | Cgt => Cond_g
  | Cge => Cond_ge
  end.

Definition testcond_for_unsigned_comparison (cmp: comparison) :=
  match cmp with
  | Ceq => Cond_e
  | Cne => Cond_ne
  | Clt => Cond_b
  | Cle => Cond_be
  | Cgt => Cond_a
  | Cge => Cond_ae
  end.

Inductive extcond: Type :=
  | Cond_base (c: testcond)
  | Cond_or (c1 c2: testcond)
  | Cond_and (c1 c2: testcond).

Definition testcond_for_condition (cond: condition) : extcond :=
  match cond with
  | Ccomp c => Cond_base(testcond_for_signed_comparison c)
  | Ccompu c => Cond_base(testcond_for_unsigned_comparison c)
  | Ccompimm c n => Cond_base(testcond_for_signed_comparison c)
  | Ccompuimm c n => Cond_base(testcond_for_unsigned_comparison c)
  | Ccompl c => Cond_base(testcond_for_signed_comparison c)
  | Ccomplu c => Cond_base(testcond_for_unsigned_comparison c)
  | Ccomplimm c n => Cond_base(testcond_for_signed_comparison c)
  | Ccompluimm c n => Cond_base(testcond_for_unsigned_comparison c)
  | Ccompf c | Ccompfs c =>
      match c with
      | Ceq => Cond_and Cond_np Cond_e
      | Cne => Cond_or Cond_p Cond_ne
      | Clt => Cond_base Cond_a
      | Cle => Cond_base Cond_ae
      | Cgt => Cond_base Cond_a
      | Cge => Cond_base Cond_ae
      end
  | Cnotcompf c | Cnotcompfs c =>
      match c with
      | Ceq => Cond_or Cond_p Cond_ne
      | Cne => Cond_and Cond_np Cond_e
      | Clt => Cond_base Cond_be
      | Cle => Cond_base Cond_b
      | Cgt => Cond_base Cond_be
      | Cge => Cond_base Cond_b
      end
  | Cmaskzero n => Cond_base Cond_e
  | Cmasknotzero n => Cond_base Cond_ne
  end.

(** Acting upon extended conditions. *)

Definition mk_setcc_base (cond: extcond) (rd: ireg) (k: code) :=
  match cond with
  | Cond_base c =>
      Psetcc c rd :: k
  | Cond_and c1 c2 =>
      if ireg_eq rd RAX
      then Psetcc c1 RAX :: Psetcc c2 RCX :: Pandl_rr RAX RCX :: k
      else Psetcc c1 RAX :: Psetcc c2 rd  :: Pandl_rr rd RAX :: k
  | Cond_or c1 c2 =>
      if ireg_eq rd RAX
      then Psetcc c1 RAX :: Psetcc c2 RCX :: Porl_rr RAX RCX :: k
      else Psetcc c1 RAX :: Psetcc c2 rd  :: Porl_rr rd RAX :: k
  end.

Definition mk_setcc (cond: extcond) (rd: ireg) (k: code) :=
  if Archi.ptr64 || low_ireg rd
  then mk_setcc_base cond rd k
  else mk_setcc_base cond RAX (Pmov_rr rd RAX :: k).

Definition mk_jcc (cond: extcond) (lbl: label) (k: code) :=
  match cond with
  | Cond_base c => Pjcc c lbl :: k
  | Cond_and c1 c2 => Pjcc2 c1 c2 lbl :: k
  | Cond_or c1 c2 => Pjcc c1 lbl :: Pjcc c2 lbl :: k
  end.

(** Translation of the arithmetic operation [r <- op(args)].
  The corresponding instructions are prepended to [k]. *)

Definition transl_op
             (op: operation) (args: list mreg) (res: mreg) (k: code) : Errors.res code :=
  match op, args with
  | Omove, a1 :: nil =>
      mk_mov (preg_of res) (preg_of a1) k
  | Ointconst n, nil =>
      do r <- ireg_of res;
      OK ((if Int.eq_dec n Int.zero then Pxorl_r r else Pmovl_ri r n) :: k)
  | Olongconst n, nil =>
      do r <- ireg_of res;
      OK ((if Int64.eq_dec n Int64.zero then Pxorq_r r else Pmovq_ri r n) :: k)
  | Ofloatconst f, nil =>
      do r <- freg_of res;
      OK ((if Float.eq_dec f Float.zero then Pxorpd_f r else Pmovsd_fi r f) :: k)
  | Osingleconst f, nil =>
      do r <- freg_of res;
      OK ((if Float32.eq_dec f Float32.zero then Pxorps_f r else Pmovss_fi r f) :: k)
  | Oindirectsymbol id, nil =>
      do r <- ireg_of res;
      OK (Pmov_rs r id :: k)
  | Ocast8signed, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv Pmovsb_rr r r1 k
  | Ocast8unsigned, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv Pmovzb_rr r r1 k
  | Ocast16signed, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; OK (Pmovsw_rr r r1 :: k)
  | Ocast16unsigned, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; OK (Pmovzw_rr r r1 :: k)
  | Oneg, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pnegl r :: k)
  | Osub, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Psubl_rr r r2 :: k)
  | Omul, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pimull_rr r r2 :: k)
  | Omulimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pimull_ri r n :: k)
  | Omulhs, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq res DX);
      do r2 <- ireg_of a2; OK (Pimull_r r2 :: k)
  | Omulhu, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq res DX);
      do r2 <- ireg_of a2; OK (Pmull_r r2 :: k)
  | Odiv, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res AX);
      OK(Pcltd :: Pidivl RCX :: k)
  | Odivu, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res AX);
      OK(Pxorl_r RDX :: Pdivl RCX :: k)
  | Omod, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res DX);
      OK(Pcltd :: Pidivl RCX :: k)
  | Omodu, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res DX);
      OK(Pxorl_r RDX :: Pdivl RCX :: k)
  | Oand, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pandl_rr r r2 :: k)
  | Oandimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pandl_ri r n :: k)
  | Oor, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Porl_rr r r2 :: k)
  | Oorimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Porl_ri r n :: k)
  | Oxor, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pxorl_rr r r2 :: k)
  | Oxorimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pxorl_ri r n :: k)
  | Onot, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pnotl r :: k)
  | Oshl, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      assertion (mreg_eq a2 CX);
      do r <- ireg_of res; OK (Psall_rcl r :: k)
  | Oshlimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Psall_ri r n :: k)
  | Oshr, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      assertion (mreg_eq a2 CX);
      do r <- ireg_of res; OK (Psarl_rcl r :: k)
  | Oshrimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Psarl_ri r n :: k)
  | Oshru, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      assertion (mreg_eq a2 CX);
      do r <- ireg_of res; OK (Pshrl_rcl r :: k)
  | Oshruimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pshrl_ri r n :: k)
  | Oshrximm n, a1 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq res AX);
      mk_shrximm n k
  | Ororimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Prorl_ri r n :: k)
  | Oshldimm n, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pshld_ri r r2 n :: k)
  | Olea addr, _ =>
      do am <- transl_addressing addr args; do r <- ireg_of res;
      OK (Pleal r (normalize_addrmode_32 am) :: k)
(* 64-bit integer operations *)
  | Olowlong, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pmovls_rr r :: k)
  | Ocast32signed, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; OK (Pmovsl_rr r r1 :: k)
  | Ocast32unsigned, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; OK (Pmovzl_rr r r1 :: k)
  | Onegl, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pnegq r :: k)
  | Oaddlimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Paddq_ri r n :: k)
  | Osubl, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Psubq_rr r r2 :: k)
  | Omull, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pimulq_rr r r2 :: k)
  | Omullimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pimulq_ri r n :: k)
  | Omullhs, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq res DX);
      do r2 <- ireg_of a2; OK (Pimulq_r r2 :: k)
  | Omullhu, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq res DX);
      do r2 <- ireg_of a2; OK (Pmulq_r r2 :: k)
  | Odivl, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res AX);
      OK(Pcqto :: Pidivq RCX :: k)
  | Odivlu, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res AX);
      OK(Pxorq_r RDX :: Pdivq RCX :: k)
  | Omodl, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res DX);
      OK(Pcqto :: Pidivq RCX :: k)
  | Omodlu, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq a2 CX);
      assertion (mreg_eq res DX);
      OK(Pxorq_r RDX :: Pdivq RCX :: k)
  | Oandl, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pandq_rr r r2 :: k)
  | Oandlimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pandq_ri r n :: k)
  | Oorl, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Porq_rr r r2 :: k)
  | Oorlimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Porq_ri r n :: k)
  | Oxorl, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pxorq_rr r r2 :: k)
  | Oxorlimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pxorq_ri r n :: k)
  | Onotl, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pnotq r :: k)
  | Oshll, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      assertion (mreg_eq a2 CX);
      do r <- ireg_of res; OK (Psalq_rcl r :: k)
  | Oshllimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Psalq_ri r n :: k)
  | Oshrl, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      assertion (mreg_eq a2 CX);
      do r <- ireg_of res; OK (Psarq_rcl r :: k)
  | Oshrlimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Psarq_ri r n :: k)
  | Oshrxlimm n, a1 :: nil =>
      assertion (mreg_eq a1 AX);
      assertion (mreg_eq res AX);
      mk_shrxlimm n k
  | Oshrlu, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      assertion (mreg_eq a2 CX);
      do r <- ireg_of res; OK (Pshrq_rcl r :: k)
  | Oshrluimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pshrq_ri r n :: k)
  | Ororlimm n, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Prorq_ri r n :: k)
  | Oleal addr, _ =>
      do am <- transl_addressing addr args; do r <- ireg_of res;
      OK (match normalize_addrmode_64 am with
          | (am', None)       => Pleaq r am' :: k
          | (am', Some delta) => Pleaq r am' :: Paddq_ri r delta :: k
          end)
(**)
  | Onegf, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; OK (Pnegd r :: k)
  | Oabsf, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; OK (Pabsd r :: k)
  | Oaddf, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Paddd_ff r r2 :: k)
  | Osubf, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Psubd_ff r r2 :: k)
  | Omulf, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Pmuld_ff r r2 :: k)
  | Odivf, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Pdivd_ff r r2 :: k)
  | Onegfs, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; OK (Pnegs r :: k)
  | Oabsfs, a1 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; OK (Pabss r :: k)
  | Oaddfs, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Padds_ff r r2 :: k)
  | Osubfs, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Psubs_ff r r2 :: k)
  | Omulfs, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Pmuls_ff r r2 :: k)
  | Odivfs, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Pdivs_ff r r2 :: k)
  | Osingleoffloat, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; OK (Pcvtsd2ss_ff r r1 :: k)
  | Ofloatofsingle, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; OK (Pcvtss2sd_ff r r1 :: k)
  | Ointoffloat, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1; OK (Pcvttsd2si_rf r r1 :: k)
  | Ofloatofint, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1; OK (Pcvtsi2sd_fr r r1 :: k)
  | Ointofsingle, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1; OK (Pcvttss2si_rf r r1 :: k)
  | Osingleofint, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1; OK (Pcvtsi2ss_fr r r1 :: k)
  | Olongoffloat, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1; OK (Pcvttsd2sl_rf r r1 :: k)
  | Ofloatoflong, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1; OK (Pcvtsl2sd_fr r r1 :: k)
  | Olongofsingle, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1; OK (Pcvttss2sl_rf r r1 :: k)
  | Osingleoflong, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1; OK (Pcvtsl2ss_fr r r1 :: k)
  | Ocmp c, args =>
      do r <- ireg_of res;
      transl_cond c args (mk_setcc (testcond_for_condition c) r k)
  | _, _ =>
      Error(msg "Asmgen.transl_op")
  end.

(** Translation of memory loads and stores *)

Definition transl_load (chunk: memory_chunk)
                       (addr: addressing) (args: list mreg) (dest: mreg)
                       (k: code) : res code :=
  do am <- transl_addressing addr args;
  match chunk with
  | Mint8unsigned =>
      do r <- ireg_of dest; OK(Pmovzb_rm r am :: k)
  | Mint8signed =>
      do r <- ireg_of dest; OK(Pmovsb_rm r am :: k)
  | Mint16unsigned =>
      do r <- ireg_of dest; OK(Pmovzw_rm r am :: k)
  | Mint16signed =>
      do r <- ireg_of dest; OK(Pmovsw_rm r am :: k)
  | Mint32 =>
      do r <- ireg_of dest; OK(Pmovl_rm r am :: k)
  | Mint64 =>
      do r <- ireg_of dest; OK(Pmovq_rm r am :: k)
  | Mfloat32 =>
      do r <- freg_of dest; OK(Pmovss_fm r am :: k)
  | Mfloat64 =>
      do r <- freg_of dest; OK(Pmovsd_fm r am :: k)
  | _ =>
      Error (msg "Asmgen.transl_load")
  end.

Definition transl_store (chunk: memory_chunk)
                        (addr: addressing) (args: list mreg) (src: mreg)
                        (k: code) : res code :=
  do am <- transl_addressing addr args;
  match chunk with
  | Mint8unsigned | Mint8signed =>
      do r <- ireg_of src; mk_storebyte am r k
  | Mint16unsigned | Mint16signed =>
      do r <- ireg_of src; OK(Pmovw_mr am r :: k)
  | Mint32 =>
      do r <- ireg_of src; OK(Pmovl_mr am r :: k)
  | Mint64 =>
      do r <- ireg_of src; OK(Pmovq_mr am r :: k)
  | Mfloat32 =>
      do r <- freg_of src; OK(Pmovss_mf am r :: k)
  | Mfloat64 =>
      do r <- freg_of src; OK(Pmovsd_mf am r :: k)
  | _ =>
      Error (msg "Asmgen.transl_store")
  end.

(** Translation of a Mach instruction. *)

Definition transl_instr (f: Mach.function) (i: Mach.instruction)
                        (ax_is_parent: bool) (k: code) :=
  match i with
  | Mgetstack ofs q dst =>
      loadind RSP ofs q dst k
  | Msetstack src ofs q =>
      storeind src RSP ofs q k
  | Mgetparam ofs q dst =>
      if ax_is_parent then
        loadind RAX ofs q dst k
      else
        (do k1 <- loadind RAX ofs q dst k;
         loadind RSP f.(fn_link_ofs) (quantity_of_typ Tptr) AX k1)
  | Mop op args res =>
      transl_op op args res k
  | Mload chunk addr args dst =>
      transl_load chunk addr args dst k
  | Mstore chunk addr args src =>
      transl_store chunk addr args src k
  | Mcall sig (inl reg) =>
      do r <- ireg_of reg; OK (Pcall_r r sig :: k)
  | Mcall sig (inr symb) =>
      OK (Pcall_s symb sig :: k)
  | Mtailcall sig (inl reg) =>
      do r <- ireg_of reg;
      OK (Pfreeframe f.(fn_stacksize) f.(fn_retaddr_ofs) f.(fn_link_ofs) ::
          Pjmp_r r sig :: k)
  | Mtailcall sig (inr symb) =>
      OK (Pfreeframe f.(fn_stacksize) f.(fn_retaddr_ofs) f.(fn_link_ofs) ::
          Pjmp_s symb sig :: k)
  | Mlabel lbl =>
      OK(Plabel lbl :: k)
  | Mgoto lbl =>
      OK(Pjmp_l lbl :: k)
  | Mcond cond args lbl =>
      transl_cond cond args (mk_jcc (testcond_for_condition cond) lbl k)
  | Mjumptable arg tbl =>
      do r <- ireg_of arg; OK (Pjmptbl r tbl :: k)
  | Mreturn =>
      OK (Pfreeframe f.(fn_stacksize) f.(fn_retaddr_ofs) f.(fn_link_ofs) ::
          Pret :: k)
  | Mbuiltin ef args res =>
      OK (Pbuiltin ef (List.map (map_builtin_arg preg_of) args) (map_builtin_res preg_of res) :: k)
  end.

(** Translation of a code sequence *)

Definition it1_is_parent (before: bool) (i: Mach.instruction) : bool :=
  match i with
  | Msetstack src ofs ty => before
  | Mgetparam ofs ty dst => negb (mreg_eq dst AX)
  | _ => false
  end.

(** This is the naive definition that we no longer use because it
  is not tail-recursive.  It is kept as specification. *)

Fixpoint transl_code (f: Mach.function) (il: list Mach.instruction) (axp: bool) :=
  match il with
  | nil => OK nil
  | i1 :: il' =>
      do k <- transl_code f il' (it1_is_parent axp i1);
      transl_instr f i1 axp k
  end.

(** This is an equivalent definition in continuation-passing style
  that runs in constant stack space. *)

Fixpoint transl_code_rec (f: Mach.function) (il: list Mach.instruction)
                         (axp: bool) (k: code -> res code) :=
  match il with
  | nil => k nil
  | i1 :: il' =>
      transl_code_rec f il' (it1_is_parent axp i1)
        (fun c1 => do c2 <- transl_instr f i1 axp c1; k c2)
  end.

Definition transl_code' (f: Mach.function) (il: list Mach.instruction) (axp: bool) :=
  transl_code_rec f il axp (fun c => OK c).

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

Definition transl_function (f: Mach.function) :=
  do c <- transl_code' f f.(Mach.fn_code) true;
  OK (mkfunction f.(Mach.fn_sig)
        (Pallocframe f.(fn_stacksize) f.(fn_retaddr_ofs) f.(fn_link_ofs) :: c)).

Definition transf_function (f: Mach.function) : res Asm.function :=
  do tf <- transl_function f;
  if zlt Ptrofs.max_unsigned (list_length_z tf.(fn_code))
  then Error (msg "code size exceeded")
  else OK tf.

Definition transf_fundef (f: Mach.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res Asm.program :=
  transform_partial_program transf_fundef p.


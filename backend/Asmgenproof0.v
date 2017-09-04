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

(** Correctness proof for Asm generation: machine-independent framework *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Locations.
Require Import Mach.
Require Import Asm.
Require Import Asmgen.
Require Import Conventions.

(** * Processor registers and register states *)

Hint Extern 2 (_ <> _) => congruence: asmgen.

Lemma ireg_of_eq:
  forall r r', ireg_of r = OK r' -> preg_of r = IR r'.
Proof.
  unfold ireg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma freg_of_eq:
  forall r r', freg_of r = OK r' -> preg_of r = FR r'.
Proof.
  unfold freg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  destruct r1; destruct r2; simpl; intros; reflexivity || discriminate.
Qed.

Lemma preg_of_data:
  forall r, data_preg (preg_of r) = true.
Proof.
  intros. destruct r; reflexivity.
Qed.
Hint Resolve preg_of_data: asmgen.

Lemma data_diff:
  forall r r',
  data_preg r = true -> data_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.
Hint Resolve data_diff: asmgen.

Lemma preg_of_not_SP:
  forall r, preg_of r <> SP.
Proof.
  intros. unfold preg_of; destruct r; simpl; congruence.
Qed.

Lemma preg_of_not_PC:
  forall r, preg_of r <> PC.
Proof.
  intros. apply data_diff; auto with asmgen.
Qed.

Hint Resolve preg_of_not_SP preg_of_not_PC: asmgen.

Lemma sub_pregs_correct:
  forall r,
  match subregs r with
  | Some (a, b) => sub_pregs (preg_of r) = Some (preg_of a, preg_of b)
  | None => sub_pregs (preg_of r) = None
  end.
Proof.
  intros. destruct r; reflexivity.
Qed.

Lemma sub_preg_list_correct:
  forall r, sub_preg_list (preg_of r) = map preg_of (subreg_list r).
Proof.
  intros. destruct r; simpl; auto.
Qed.

Lemma super_pregs_correct:
  forall r,
  match superregs r with
  | Some r' => super_pregs (preg_of r) = Some (preg_of r')
  | None => super_pregs (preg_of r) = None
  end.
Proof.
  intros. destruct r; reflexivity.
Qed.

Lemma super_preg_list_correct:
  forall r, super_preg_list (preg_of r) = map preg_of (superreg_list r).
Proof.
  intros. destruct r; simpl; auto.
Qed.

Lemma sub_preg_super_preg:
  forall p1 p2, sub_preg p1 p2 -> super_preg p2 p1.
Proof.
  unfold sub_preg, super_preg.
  destruct p2; simpl; try tauto.
  destruct f; simpl; intros; destruct H; subst; simpl; auto.
Qed.

Lemma super_preg_sub_preg:
  forall p1 p2, super_preg p1 p2 -> sub_preg p2 p1.
Proof.
  unfold sub_preg, super_preg.
  destruct p2; simpl; try tauto.
  destruct s; simpl; intros; subst; simpl; auto.
Qed.

Lemma sub_pregs_super_pregs:
  forall p,
  match sub_pregs p with
  | Some (a, b) => super_pregs a = Some p /\ super_pregs b = Some p
  | None => True
  end.
Proof.
  destruct p; simpl; try tauto.
  destruct f; simpl; tauto.
Qed.

Lemma super_pregs_sub_pregs:
  forall p,
  match super_pregs p with
  | Some s =>
    match sub_pregs s with
    | Some (a, b) => p = a \/ p = b
    | None => False
    end
 | None => True
 end.
Proof.
  destruct p; simpl; try tauto.
  destruct s; simpl; tauto.
Qed.

Lemma sub_preg_in_list:
  forall r1 r2, sub_preg r1 r2 <-> In r1 (sub_preg_list r2).
Proof.
  unfold sub_preg, sub_preg_list. split; intros.
  destruct (sub_pregs r2) as [[a b]|]; simpl; destruct H; auto.
  destruct (sub_pregs r2) as [[a b]|]; simpl in H; decompose [or] H; auto; tauto.
Qed.

Lemma super_preg_in_list:
  forall r1 r2, super_preg r1 r2 <-> In r1 (super_preg_list r2).
Proof.
  unfold super_preg, super_preg_list. split; intros.
  destruct (super_pregs r2) as [a|]; simpl; destruct H; auto.
  destruct (super_pregs r2) as [a|]; simpl in H; decompose [or] H; auto; tauto.
Qed.

Lemma sub_pregs_of_special_preg:
  forall p, data_preg p = false -> sub_pregs p = None.
Proof.
  intros. destruct p; simpl in *; congruence.
Qed.

Lemma super_pregs_of_special_preg:
  forall p, data_preg p = false -> super_pregs p = None.
Proof.
  intros. destruct p; simpl in *; congruence.
Qed.

Definition preg_overlap p1 p2 := sub_preg p1 p2 \/ sub_preg p2 p1.

Definition preg_diff p1 p2 := p1 <> p2 /\ ~ preg_overlap p1 p2.

Lemma preg_overlap_correct:
  forall r1 r2, preg_overlap (preg_of r1) (preg_of r2) <-> overlap r1 r2.
Proof.
  unfold preg_overlap, overlap, subreg, sub_preg. split; intros.
  - generalize (sub_pregs_correct r1); intro S1.
    generalize (sub_pregs_correct r2); intro S2.
    destruct (subregs r1) as [[a1 b1]|], (subregs r2) as [[a2 b2]|];
      rewrite S1, S2 in H; decompose [or] H; auto using preg_of_injective.
  - generalize (sub_pregs_correct r1); intro S1.
    generalize (sub_pregs_correct r2); intro S2.
    destruct (subregs r1) as [[a1 b1]|], (subregs r2) as [[a2 b2]|];
      rewrite S1, S2; decompose [or] H; subst; tauto.
Qed.

Lemma preg_overlap_sym:
  forall p1 p2, preg_overlap p1 p2 -> preg_overlap p2 p1.
Proof.
  unfold preg_overlap. intros. destruct H; tauto.
Qed.

Lemma not_preg_overlap_sym:
  forall p1 p2, ~ preg_overlap p1 p2 -> ~ preg_overlap p2 p1.
Proof.
  auto using preg_overlap_sym.
Qed.

Lemma preg_of_not_overlap_SP:
  forall r, ~ preg_overlap SP (preg_of r).
Proof.
  intros. destruct r; compute; intros; decompose [or] H; congruence.
Qed.

Lemma preg_of_not_overlap_PC:
  forall r, ~ preg_overlap PC (preg_of r).
Proof.
  intros. destruct r; compute; intros; decompose [or] H; congruence.
Qed.

Lemma special_preg_no_overlap:
  forall p1 p2, data_preg p2 = false -> ~ preg_overlap p1 p2.
Proof.
  intros. unfold preg_overlap.
  unfold not; intros; destruct H0.
  exploit sub_pregs_of_special_preg; eauto; intros.
  unfold sub_preg in H0. rewrite H1 in H0; auto.
  apply sub_preg_super_preg in H0.
  exploit super_pregs_of_special_preg; eauto; intros.
  unfold super_preg in H0. rewrite H1 in H0; auto.
Qed.

Definition preg_overlap_dec p1 p2: { preg_overlap p1 p2 } + { ~ preg_overlap p1 p2 }.
Proof.
  destruct (data_preg p2) eqn:D.
  - unfold preg_overlap.
    destruct (In_dec PregEq.eq p1 (sub_preg_list p2)).
    + left. apply sub_preg_in_list in i; auto.
    + destruct (In_dec PregEq.eq p1 (super_preg_list p2)).
      * left. apply super_preg_in_list, super_preg_sub_preg in i; auto.
      * right. unfold not; intros.
        destruct H. contradict n. apply sub_preg_in_list in H; auto.
        contradict n0. apply sub_preg_super_preg, super_preg_in_list in H; auto.
  - right. auto using special_preg_no_overlap.
Defined.

Lemma undef_regs_same:
  forall r rl rs, In r rl -> undef_regs rl rs r = Vundef.
Proof.
  induction rl; simpl; intros. tauto.
  destruct (PregEq.eq a r).
  subst; rewrite Pregmap.gss; auto.
  destruct H. contradiction.
  rewrite Pregmap.gso; auto.
Qed.

Lemma undef_regs_other:
  forall r rl rs,
  (forall r', In r' rl -> r <> r') ->
  undef_regs rl rs r = rs r.
Proof.
  induction rl; simpl; intros. auto.
  rewrite Pregmap.gso; auto.
Qed.

Fixpoint preg_notin (r: preg) (rl: list mreg) : Prop :=
  match rl with
  | nil => True
  | r1 :: nil => r <> preg_of r1
  | r1 :: rl => r <> preg_of r1 /\ preg_notin r rl
  end.

Remark preg_notin_charact:
  forall r rl,
  preg_notin r rl <-> (forall mr, In mr rl -> r <> preg_of mr).
Proof.
  induction rl; simpl; intros.
  tauto.
  destruct rl.
  simpl. split. intros. intuition congruence. auto.
  rewrite IHrl. split.
  intros [A B]. intros. destruct H. congruence. auto.
  auto.
Qed.

Lemma undef_regs_other_2:
  forall r rl rs,
  preg_notin r rl ->
  undef_regs (map preg_of rl) rs r = rs r.
Proof.
  intros. apply undef_regs_other. intros.
  exploit list_in_map_inv; eauto. intros [mr [A B]]. subst.
  rewrite preg_notin_charact in H. auto.
Qed.

Lemma undef_regs_set_other:
  forall r rl rs r' v,
  r <> r' ->
  ~ In r rl ->
  (Pregmap.set r' v (undef_regs rl rs)) r = rs r.
Proof.
  intros. unfold Pregmap.set.
  destruct (PregEq.eq r r'). contradiction.
  apply undef_regs_other.
  intros. contradict H0. subst; auto.
Qed.

Lemma pregmap_gss:
  forall rs x v, (rs#x <- v)#x = v.
Proof.
  intros. apply Pregmap.gss.
Qed.

Lemma pregmap_gso:
  forall rs x y v,
  x <> y ->
  ~ preg_overlap x y ->
  (rs#y <- v)#x = rs#x.
Proof.
  intros. apply Decidable.not_or in H0; destruct H0.
  unfold pregmap_set, sub_preg, sub_preg_list in *.
  rewrite undef_regs_set_other, undef_regs_other; auto.
  intros. apply super_preg_in_list, super_preg_sub_preg in H2.
  contradict H1. subst; auto.
  contradict H0. apply sub_preg_in_list in H0. auto.
Qed.

Lemma nextinstr_pc:
  forall rs, (nextinstr rs)#PC = Val.offset_ptr rs#PC Ptrofs.one.
Proof.
  intros. apply Pregmap.gss.
Qed.

Lemma nextinstr_inv:
  forall r rs, r <> PC -> (nextinstr rs)#r = rs#r.
Proof.
  intros. unfold nextinstr. apply Pregmap.gso. red; intro; subst. auto.
Qed.

Lemma nextinstr_inv1:
  forall r rs, data_preg r = true -> (nextinstr rs)#r = rs#r.
Proof.
  intros. apply nextinstr_inv. red; intro; subst; discriminate.
Qed.

Lemma nextinstr_set_preg:
  forall rs m v,
  (nextinstr (rs#(preg_of m) <- v))#PC = Val.offset_ptr rs#PC Ptrofs.one.
Proof.
  intros. unfold nextinstr. rewrite pregmap_gss.
  rewrite pregmap_gso.
  auto. apply sym_not_eq, preg_of_not_PC.
  apply preg_of_not_overlap_PC.
Qed.

(** * Agreement between Mach registers and processor registers *)

Record agree (ms: Mach.regset) (sp: val) (rs: Asm.regset) : Prop := mkagree {
  agree_sp: rs#SP = sp;
  agree_sp_def: sp <> Vundef;
  agree_mregs: forall r: mreg, Val.lessdef (ms r) (rs#(preg_of r))
}.

Lemma preg_val:
  forall ms sp rs r, agree ms sp rs -> Val.lessdef (ms r) rs#(preg_of r).
Proof.
  intros. destruct H. auto.
Qed.

Lemma preg_vals:
  forall ms sp rs, agree ms sp rs ->
  forall l, Val.lessdef_list (map ms l) (map rs (map preg_of l)).
Proof.
  induction l; simpl. constructor. constructor. eapply preg_val; eauto. auto.
Qed.

Lemma sp_val:
  forall ms sp rs, agree ms sp rs -> sp = rs#SP.
Proof.
  intros. destruct H; auto.
Qed.

Lemma ireg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  ireg_of r = OK r' ->
  Val.lessdef (ms r) rs#r'.
Proof.
  intros. rewrite <- (ireg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma freg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  freg_of r = OK r' ->
  Val.lessdef (ms r) (rs#r').
Proof.
  intros. rewrite <- (freg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma agree_exten:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, data_preg r = true -> rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H0; auto. auto.
  intros. rewrite H0; auto. apply preg_of_data.
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_set_mreg:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H1; auto. apply sym_not_equal. apply preg_of_not_SP.
  intros. unfold Regmap.set. destruct (RegEq.eq r0 r). congruence.
  rewrite H1. auto. apply preg_of_data.
  red; intros; elim n. eapply preg_of_injective; eauto.
Qed.

Corollary agree_set_mreg_parallel:
  forall ms sp rs r v v',
  agree ms sp rs ->
  Val.lessdef v v' ->
  agree (Regmap.set r v ms) sp (Pregmap.set (preg_of r) v' rs).
Proof.
  intros. eapply agree_set_mreg; eauto. rewrite Pregmap.gss; auto. intros; apply Pregmap.gso; auto.
Qed.

Lemma agree_set_mreg_with_aliases:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> (preg_of r) -> ~ preg_overlap r' (preg_of r) -> rs'#r' = rs#r') ->
  agree (regmap_set r v ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H1; auto. apply sym_not_equal, preg_of_not_SP. apply preg_of_not_overlap_SP.
  intros. unfold regmap_set, Regmap.set. destruct (RegEq.eq r0 r). congruence.

  destruct (overlap_dec r0 r).
  - unfold overlap in o. destruct o.
    + rewrite Mach.undef_regs_same; simpl; auto.
      apply subreg_lists; auto.
    + apply subreg_superreg, superreg_lists in H. destruct H.
      rewrite H2; simpl.
      rewrite Mach.undef_regs_same; simpl; auto.
  - rewrite !Mach.undef_regs_other. rewrite H1. auto. apply preg_of_data.
    red; intros; elim n. eapply preg_of_injective; eauto.
    contradict n0. apply preg_overlap_correct; auto.
    contradict n0. unfold overlap. apply superreg_in_list, superreg_subreg in n0. auto.
    contradict n0. unfold overlap. apply subreg_in_list in n0. auto.
Qed.

Lemma agree_set_other:
  forall ms sp rs r v,
  agree ms sp rs ->
  data_preg r = false ->
  agree ms sp (rs#r <- v).
Proof.
  intros. apply agree_exten with rs. auto.
  intros. apply pregmap_gso. congruence.
  apply special_preg_no_overlap; auto.
Qed.

Lemma agree_set_other':
  forall ms sp rs r v,
  agree ms sp rs ->
  data_preg r = false ->
  agree ms sp (Pregmap.set r v rs).
Proof.
  intros. apply agree_exten with rs. auto.
  intros. apply Pregmap.gso. congruence.
Qed.

Lemma agree_nextinstr:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr rs).
Proof.
  intros. unfold nextinstr. apply agree_set_other. auto. auto.
Qed.

Lemma agree_undef_regs:
  forall ms sp rl rs rs',
  agree ms sp rs ->
  (forall r', data_preg r' = true -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree (Mach.undef_regs rl ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite <- agree_sp0. apply H0; auto.
  rewrite preg_notin_charact. intros. apply not_eq_sym. apply preg_of_not_SP.
  intros. destruct (In_dec mreg_eq r rl).
  rewrite Mach.undef_regs_same; auto.
  rewrite Mach.undef_regs_other; auto. rewrite H0; auto.
  apply preg_of_data.
  rewrite preg_notin_charact. intros; red; intros. elim n.
  exploit preg_of_injective; eauto. congruence.
Qed.

Lemma agree_undef_regs2:
  forall ms sp rl rs rs',
  agree (Mach.undef_regs rl ms) sp rs ->
  (forall r', data_preg r' = true -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree (Mach.undef_regs rl ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite <- agree_sp0. apply H0; auto.
  rewrite preg_notin_charact. intros. apply not_eq_sym. apply preg_of_not_SP.
  intros. destruct (In_dec mreg_eq r rl).
  rewrite Mach.undef_regs_same; auto.
  rewrite H0; auto.
  apply preg_of_data.
  rewrite preg_notin_charact. intros; red; intros. elim n.
  exploit preg_of_injective; eauto. congruence.
Qed.

Lemma agree_undef_regs_undef_pregs:
  forall ms sp rl rs,
  agree ms sp rs ->
  agree (Mach.undef_regs rl ms) sp (undef_regs (map preg_of rl) rs).
Proof.
  intros.
  induction rl. simpl; auto.
  simpl. apply agree_set_mreg_parallel; auto.
Qed.

Lemma agree_undef_nondata_regs:
  forall ms sp rl rs,
  agree ms sp rs ->
  (forall r, In r rl -> data_preg r = false) ->
  agree ms sp (undef_regs rl rs).
Proof.
  induction rl; simpl; intros. auto.
  assert (data_preg a = false) by auto.
  apply agree_set_other'; auto.
Qed.

Lemma agree_set_pair:
  forall sp p v v' ms rs,
  agree ms sp rs ->
  Val.lessdef v v' ->
  agree (Mach.set_pair p v ms) sp (set_pair (map_rpair preg_of p) v' rs).
Proof.
  intros. destruct p; simpl.
- apply agree_set_mreg_parallel; auto.
  rewrite sub_preg_list_correct, super_preg_list_correct.
  repeat apply agree_undef_regs_undef_pregs; auto.
- unfold regmap_set, pregmap_set.
  rewrite !sub_preg_list_correct, !super_preg_list_correct.
  apply agree_set_mreg_parallel; repeat apply agree_undef_regs_undef_pregs.
  apply agree_set_mreg_parallel; repeat apply agree_undef_regs_undef_pregs; auto.
  apply Val.hiword_lessdef; auto. apply Val.loword_lessdef; auto.
Qed.

Lemma agree_set_undef_mreg:
  forall ms sp rs r v rl rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> (preg_of r) -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree (Regmap.set r v (Mach.undef_regs rl ms)) sp rs'.
Proof.
  intros.
  apply agree_set_mreg with (rs := Pregmap.set (preg_of r) (rs#(preg_of r)) rs'); auto.
  apply agree_undef_regs with rs; auto.
  intros. unfold Pregmap.set. destruct (PregEq.eq r' (preg_of r)).
  congruence. auto.
  intros. rewrite Pregmap.gso; auto.
Qed.

Lemma agree_set_undef_mreg_with_aliases:
  forall ms sp rs r v rl rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> (preg_of r) -> ~ preg_overlap r' (preg_of r) -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree (regmap_set r v (Mach.undef_regs rl ms)) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H1; auto using preg_of_not_overlap_SP with asmgen.
  apply preg_notin_charact; auto using preg_of_not_overlap_SP with asmgen.
  intros. unfold regmap_set, Regmap.set. destruct (RegEq.eq r0 r). congruence.

  destruct (overlap_dec r0 r).
  - unfold overlap in o. destruct o.
    + rewrite Mach.undef_regs_same; simpl; auto.
      apply subreg_lists; auto.
    + apply subreg_superreg, superreg_lists in H. destruct H.
      rewrite H2; simpl.
      rewrite Mach.undef_regs_same; simpl; auto.
  - unfold overlap in n0. rewrite Mach.undef_regs_other, Mach.undef_regs_other.
    destruct (in_dec mreg_eq r0 rl).
    + rewrite Mach.undef_regs_same; auto.
    + rewrite Mach.undef_regs_other; auto. rewrite H1; auto. apply preg_of_data.
      contradict n. eapply preg_of_injective; eauto.
      contradict n0. apply preg_overlap_correct; auto.
      apply preg_notin_charact; intros.
      contradict n1. apply preg_of_injective in n1; congruence.
    + contradict n0. apply superreg_in_list, superreg_subreg in n0. auto.
    + contradict n0. apply subreg_in_list in n0. auto.
Qed.

Lemma agree_change_sp:
  forall ms sp rs sp',
  agree ms sp rs -> sp' <> Vundef ->
  agree ms sp' (rs#SP <- sp').
Proof.
  intros. inv H. split; auto.
  intros. rewrite pregmap_gso; auto with asmgen.
  compute. intros. destruct H. tauto.
  destruct r; try tauto; destruct H; try congruence.
Qed.

(** Connection between Mach and Asm calling conventions for external
    functions. *)

Lemma extcall_arg_match:
  forall ms sp rs m m' l v,
  agree ms sp rs ->
  Mem.extends m m' ->
  Mach.extcall_arg ms m sp l v ->
  exists v', Asm.extcall_arg rs m' l v' /\ Val.lessdef v v'.
Proof.
  intros. inv H1.
  exists (rs#(preg_of r)); split. constructor. eapply preg_val; eauto.
  unfold load_stack in H2.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ H) in A.
  exists v'; split; auto.
  econstructor. eauto. assumption.
Qed.

Lemma extcall_arg_pair_match:
  forall ms sp rs m m' p v,
  agree ms sp rs ->
  Mem.extends m m' ->
  Mach.extcall_arg_pair ms m sp p v ->
  exists v', Asm.extcall_arg_pair rs m' p v' /\ Val.lessdef v v'.
Proof.
  intros. inv H1.
- exploit extcall_arg_match; eauto. intros (v' & A & B). exists v'; split; auto. constructor; auto.
- exploit extcall_arg_match. eauto. eauto. eexact H2. intros (v1 & A1 & B1).
  exploit extcall_arg_match. eauto. eauto. eexact H3. intros (v2 & A2 & B2).
  exists (Val.longofwords v1 v2); split. constructor; auto. apply Val.longofwords_lessdef; auto.
Qed.

Lemma extcall_args_match:
  forall ms sp rs m m', agree ms sp rs -> Mem.extends m m' ->
  forall ll vl,
  list_forall2 (Mach.extcall_arg_pair ms m sp) ll vl ->
  exists vl', list_forall2 (Asm.extcall_arg_pair rs m') ll vl' /\ Val.lessdef_list vl vl'.
Proof.
  induction 3; intros.
  exists (@nil val); split. constructor. constructor.
  exploit extcall_arg_pair_match; eauto. intros [v1' [A B]].
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto.
Qed.

Lemma extcall_arguments_match:
  forall ms m m' sp rs sg args,
  agree ms sp rs -> Mem.extends m m' ->
  Mach.extcall_arguments ms m sp sg args ->
  exists args', Asm.extcall_arguments rs m' sg args' /\ Val.lessdef_list args args'.
Proof.
  unfold Mach.extcall_arguments, Asm.extcall_arguments; intros.
  eapply extcall_args_match; eauto.
Qed.

(** Translation of arguments and results to builtins. *)

Remark builtin_arg_match:
  forall ge (rs: regset) sp m a v,
  eval_builtin_arg ge (fun r => rs (preg_of r)) sp m a v ->
  eval_builtin_arg ge rs sp m (map_builtin_arg preg_of a) v.
Proof.
  induction 1; simpl; eauto with barg.
Qed.

Lemma builtin_args_match:
  forall ge ms sp rs m m', agree ms sp rs -> Mem.extends m m' ->
  forall al vl, eval_builtin_args ge ms sp m al vl ->
  exists vl', eval_builtin_args ge rs sp m' (map (map_builtin_arg preg_of) al) vl'
           /\ Val.lessdef_list vl vl'.
Proof.
  induction 3; intros; simpl.
  exists (@nil val); split; constructor.
  exploit (@eval_builtin_arg_lessdef _ ge ms (fun r => rs (preg_of r))); eauto.
  intros; eapply preg_val; eauto.
  intros (v1' & A & B).
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto. apply builtin_arg_match; auto.
Qed.

Lemma agree_set_res:
  forall res ms sp rs v v',
  agree ms sp rs ->
  Val.lessdef v v' ->
  agree (Mach.set_res res v ms) sp (Asm.set_res (map_builtin_res preg_of res) v' rs).
Proof.
  destruct res; simpl; intros.
- unfold regmap_set, pregmap_set.
  apply agree_set_mreg_parallel; auto.
  rewrite sub_preg_list_correct, super_preg_list_correct.
  repeat apply agree_undef_regs_undef_pregs; auto.
- auto.
- repeat apply agree_set_mreg_parallel; auto.
  apply Val.hiword_lessdef; auto.
  apply Val.loword_lessdef; auto.
Qed.

Lemma set_res_other:
  forall r res v rs,
  data_preg r = false ->
  set_res (map_builtin_res preg_of res) v rs r = rs r.
Proof.
  induction res; simpl; intros.
- apply pregmap_gso. red; intros; subst r. rewrite preg_of_data in H; discriminate.
  unfold not; intros. apply preg_overlap_sym in H0.
  eapply special_preg_no_overlap in H; eauto.
- auto.
- rewrite !Pregmap.gso; auto.
  red; intros; subst r. rewrite preg_of_data in H; discriminate.
  red; intros; subst r. rewrite preg_of_data in H; discriminate.
Qed.

(** * Correspondence between Mach code and Asm code *)

Lemma find_instr_in:
  forall c pos i,
  find_instr pos c = Some i -> In i c.
Proof.
  induction c; simpl. intros; discriminate.
  intros until i. case (zeq pos 0); intros.
  left; congruence. right; eauto.
Qed.

(** The ``code tail'' of an instruction list [c] is the list of instructions
  starting at PC [pos]. *)

Inductive code_tail: Z -> code -> code -> Prop :=
  | code_tail_0: forall c,
      code_tail 0 c c
  | code_tail_S: forall pos i c1 c2,
      code_tail pos c1 c2 ->
      code_tail (pos + 1) (i :: c1) c2.

Lemma code_tail_pos:
  forall pos c1 c2, code_tail pos c1 c2 -> pos >= 0.
Proof.
  induction 1. omega. omega.
Qed.

Lemma find_instr_tail:
  forall c1 i c2 pos,
  code_tail pos c1 (i :: c2) ->
  find_instr pos c1 = Some i.
Proof.
  induction c1; simpl; intros.
  inv H.
  destruct (zeq pos 0). subst pos.
  inv H. auto. generalize (code_tail_pos _ _ _ H4). intro. omegaContradiction.
  inv H. congruence. replace (pos0 + 1 - 1) with pos0 by omega.
  eauto.
Qed.

Remark code_tail_bounds_1:
  forall fn ofs c,
  code_tail ofs fn c -> 0 <= ofs <= list_length_z fn.
Proof.
  induction 1; intros; simpl.
  generalize (list_length_z_pos c). omega.
  rewrite list_length_z_cons. omega.
Qed.

Remark code_tail_bounds_2:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) -> 0 <= ofs < list_length_z fn.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> 0 <= ofs < list_length_z fn).
  induction 1; intros; simpl.
  rewrite H. rewrite list_length_z_cons. generalize (list_length_z_pos c'). omega.
  rewrite list_length_z_cons. generalize (IHcode_tail _ _ H0). omega.
  eauto.
Qed.

Lemma code_tail_next:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) ->
  code_tail (ofs + 1) fn c.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> code_tail (ofs + 1) fn c').
  induction 1; intros.
  subst c. constructor. constructor.
  constructor. eauto.
  eauto.
Qed.

Lemma code_tail_next_int:
  forall fn ofs i c,
  list_length_z fn <= Ptrofs.max_unsigned ->
  code_tail (Ptrofs.unsigned ofs) fn (i :: c) ->
  code_tail (Ptrofs.unsigned (Ptrofs.add ofs Ptrofs.one)) fn c.
Proof.
  intros. rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_one.
  rewrite Ptrofs.unsigned_repr. apply code_tail_next with i; auto.
  generalize (code_tail_bounds_2 _ _ _ _ H0). omega.
Qed.

(** [transl_code_at_pc pc fb f c ep tf tc] holds if the code pointer [pc] points
  within the Asm code generated by translating Mach function [f],
  and [tc] is the tail of the generated code at the position corresponding
  to the code pointer [pc]. *)

Inductive transl_code_at_pc (ge: Mach.genv):
    val -> block -> Mach.function -> Mach.code -> bool -> Asm.function -> Asm.code -> Prop :=
  transl_code_at_pc_intro:
    forall b ofs f c ep tf tc,
    Genv.find_funct_ptr ge b = Some(Internal f) ->
    transf_function f = Errors.OK tf ->
    transl_code f c ep = OK tc ->
    code_tail (Ptrofs.unsigned ofs) (fn_code tf) tc ->
    transl_code_at_pc ge (Vptr b ofs) b f c ep tf tc.

(** Equivalence between [transl_code] and [transl_code']. *)

Local Open Scope error_monad_scope.

Lemma transl_code_rec_transl_code:
  forall f il ep k,
  transl_code_rec f il ep k = (do c <- transl_code f il ep; k c).
Proof.
  induction il; simpl; intros.
  auto.
  rewrite IHil.
  destruct (transl_code f il (it1_is_parent ep a)); simpl; auto.
Qed.

Lemma transl_code'_transl_code:
  forall f il ep,
  transl_code' f il ep = transl_code f il ep.
Proof.
  intros. unfold transl_code'. rewrite transl_code_rec_transl_code.
  destruct (transl_code f il ep); auto.
Qed.

(** Predictor for return addresses in generated Asm code.

  The [return_address_offset] predicate defined here is used in the
  semantics for Mach to determine the return addresses that are
  stored in activation records. *)

(** Consider a Mach function [f] and a sequence [c] of Mach instructions
  representing the Mach code that remains to be executed after a
  function call returns.  The predicate [return_address_offset f c ofs]
  holds if [ofs] is the integer offset of the PPC instruction
  following the call in the Asm code obtained by translating the
  code of [f]. Graphically:
<<
     Mach function f    |--------- Mcall ---------|
         Mach code c    |                |--------|
                        |                 \        \
                        |                  \        \
                        |                   \        \
     Asm code           |                    |--------|
     Asm function       |------------- Pcall ---------|

                        <-------- ofs ------->
>>
*)

Definition return_address_offset (f: Mach.function) (c: Mach.code) (ofs: ptrofs) : Prop :=
  forall tf tc,
  transf_function f = OK tf ->
  transl_code f c false = OK tc ->
  code_tail (Ptrofs.unsigned ofs) (fn_code tf) tc.

(** We now show that such an offset always exists if the Mach code [c]
  is a suffix of [f.(fn_code)].  This holds because the translation
  from Mach to PPC is compositional: each Mach instruction becomes
  zero, one or several PPC instructions, but the order of instructions
  is preserved. *)

Lemma is_tail_code_tail:
  forall c1 c2, is_tail c1 c2 -> exists ofs, code_tail ofs c2 c1.
Proof.
  induction 1. exists 0; constructor.
  destruct IHis_tail as [ofs CT]. exists (ofs + 1); constructor; auto.
Qed.

Section RETADDR_EXISTS.

Hypothesis transl_instr_tail:
  forall f i ep k c, transl_instr f i ep k = OK c -> is_tail k c.
Hypothesis transf_function_inv:
  forall f tf, transf_function f = OK tf ->
  exists tc, exists ep, transl_code f (Mach.fn_code f) ep = OK tc /\ is_tail tc (fn_code tf).
Hypothesis transf_function_len:
  forall f tf, transf_function f = OK tf -> list_length_z (fn_code tf) <= Ptrofs.max_unsigned.

Lemma transl_code_tail:
  forall f c1 c2, is_tail c1 c2 ->
  forall tc2 ep2, transl_code f c2 ep2 = OK tc2 ->
  exists tc1, exists ep1, transl_code f c1 ep1 = OK tc1 /\ is_tail tc1 tc2.
Proof.
  induction 1; simpl; intros.
  exists tc2; exists ep2; split; auto with coqlib.
  monadInv H0. exploit IHis_tail; eauto. intros [tc1 [ep1 [A B]]].
  exists tc1; exists ep1; split. auto.
  apply is_tail_trans with x. auto. eapply transl_instr_tail; eauto.
Qed.

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. destruct (transf_function f) as [tf|] eqn:TF.
+ exploit transf_function_inv; eauto. intros (tc1 & ep1 & TR1 & TL1).
  exploit transl_code_tail; eauto. intros (tc2 & ep2 & TR2 & TL2).
Opaque transl_instr.
  monadInv TR2.
  assert (TL3: is_tail x (fn_code tf)).
  { apply is_tail_trans with tc1; auto.
    apply is_tail_trans with tc2; auto.
    eapply transl_instr_tail; eauto. }
  exploit is_tail_code_tail. eexact TL3. intros [ofs CT].
  exists (Ptrofs.repr ofs). red; intros.
  rewrite Ptrofs.unsigned_repr. congruence.
  exploit code_tail_bounds_1; eauto.
  apply transf_function_len in TF. omega.
+ exists Ptrofs.zero; red; intros. congruence.
Qed.

End RETADDR_EXISTS.

Remark code_tail_no_bigger:
  forall pos c1 c2, code_tail pos c1 c2 -> (length c2 <= length c1)%nat.
Proof.
  induction 1; simpl; omega.
Qed.

Remark code_tail_unique:
  forall fn c pos pos',
  code_tail pos fn c -> code_tail pos' fn c -> pos = pos'.
Proof.
  induction fn; intros until pos'; intros ITA CT; inv ITA; inv CT; auto.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  f_equal. eauto.
Qed.

Lemma return_address_offset_correct:
  forall ge b ofs fb f c tf tc ofs',
  transl_code_at_pc ge (Vptr b ofs) fb f c false tf tc ->
  return_address_offset f c ofs' ->
  ofs' = ofs.
Proof.
  intros. inv H. red in H0.
  exploit code_tail_unique. eexact H12. eapply H0; eauto. intro.
  rewrite <- (Ptrofs.repr_unsigned ofs).
  rewrite <- (Ptrofs.repr_unsigned ofs').
  congruence.
Qed.

(** The [find_label] function returns the code tail starting at the
  given label.  A connection with [code_tail] is then established. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some c' else find_label lbl c'
  end.

Lemma label_pos_code_tail:
  forall lbl c pos c',
  find_label lbl c = Some c' ->
  exists pos',
  label_pos lbl pos c = Some pos'
  /\ code_tail (pos' - pos) c c'
  /\ pos < pos' <= pos + list_length_z c.
Proof.
  induction c.
  simpl; intros. discriminate.
  simpl; intros until c'.
  case (is_label lbl a).
  intro EQ; injection EQ; intro; subst c'.
  exists (pos + 1). split. auto. split.
  replace (pos + 1 - pos) with (0 + 1) by omega. constructor. constructor.
  rewrite list_length_z_cons. generalize (list_length_z_pos c). omega.
  intros. generalize (IHc (pos + 1) c' H). intros [pos' [A [B C]]].
  exists pos'. split. auto. split.
  replace (pos' - pos) with ((pos' - (pos + 1)) + 1) by omega.
  constructor. auto.
  rewrite list_length_z_cons. omega.
Qed.

(** Helper lemmas to reason about
- the "code is tail of" property
- correct translation of labels. *)

Definition tail_nolabel (k c: code) : Prop :=
  is_tail k c /\ forall lbl, find_label lbl c = find_label lbl k.

Lemma tail_nolabel_refl:
  forall c, tail_nolabel c c.
Proof.
  intros; split. apply is_tail_refl. auto.
Qed.

Lemma tail_nolabel_trans:
  forall c1 c2 c3, tail_nolabel c2 c3 -> tail_nolabel c1 c2 -> tail_nolabel c1 c3.
Proof.
  intros. destruct H; destruct H0; split.
  eapply is_tail_trans; eauto.
  intros. rewrite H1; auto.
Qed.

Definition nolabel (i: instruction) :=
  match i with Plabel _ => False | _ => True end.

Hint Extern 1 (nolabel _) => exact I : labels.

Lemma tail_nolabel_cons:
  forall i c k,
  nolabel i -> tail_nolabel k c -> tail_nolabel k (i :: c).
Proof.
  intros. destruct H0. split.
  constructor; auto.
  intros. simpl. rewrite <- H1. destruct i; reflexivity || contradiction.
Qed.

Hint Resolve tail_nolabel_refl: labels.

Ltac TailNoLabel :=
  eauto with labels;
  match goal with
  | [ |- tail_nolabel _ (_ :: _) ] => apply tail_nolabel_cons; [auto; exact I | TailNoLabel]
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: assertion_failed = OK _ |- _ ] => discriminate
  | [ H: OK _ = OK _ |- _ ] => inv H; TailNoLabel
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H;  TailNoLabel
  | [ H: (if ?x then _ else _) = OK _ |- _ ] => destruct x; TailNoLabel
  | [ H: match ?x with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct x; TailNoLabel
  | _ => idtac
  end.

Remark tail_nolabel_find_label:
  forall lbl k c, tail_nolabel k c -> find_label lbl c = find_label lbl k.
Proof.
  intros. destruct H. auto.
Qed.

Remark tail_nolabel_is_tail:
  forall k c, tail_nolabel k c -> is_tail k c.
Proof.
  intros. destruct H. auto.
Qed.

(** * Execution of straight-line code *)

Section STRAIGHTLINE.

Variable ge: genv.
Variable fn: function.

(** Straight-line code is composed of processor instructions that execute
  in sequence (no branches, no function calls and returns).
  The following inductive predicate relates the machine states
  before and after executing a straight-line sequence of instructions.
  Instructions are taken from the first list instead of being fetched
  from memory. *)

Inductive exec_straight: code -> regset -> mem ->
                         code -> regset -> mem -> Prop :=
  | exec_straight_one:
      forall i1 c rs1 m1 rs2 m2,
      exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
      exec_straight (i1 :: c) rs1 m1 c rs2 m2
  | exec_straight_step:
      forall i c rs1 m1 rs2 m2 c' rs3 m3,
      exec_instr ge fn i rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
      exec_straight c rs2 m2 c' rs3 m3 ->
      exec_straight (i :: c) rs1 m1 c' rs3 m3.

Lemma exec_straight_trans:
  forall c1 rs1 m1 c2 rs2 m2 c3 rs3 m3,
  exec_straight c1 rs1 m1 c2 rs2 m2 ->
  exec_straight c2 rs2 m2 c3 rs3 m3 ->
  exec_straight c1 rs1 m1 c3 rs3 m3.
Proof.
  induction 1; intros.
  apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_step with rs2 m2; auto.
Qed.

Lemma exec_straight_two:
  forall i1 i2 c rs1 m1 rs2 m2 rs3 m3,
  exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
  exec_instr ge fn i2 rs2 m2 = Next rs3 m3 ->
  rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
  rs3#PC = Val.offset_ptr rs2#PC Ptrofs.one ->
  exec_straight (i1 :: i2 :: c) rs1 m1 c rs3 m3.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_one; auto.
Qed.

Lemma exec_straight_three:
  forall i1 i2 i3 c rs1 m1 rs2 m2 rs3 m3 rs4 m4,
  exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
  exec_instr ge fn i2 rs2 m2 = Next rs3 m3 ->
  exec_instr ge fn i3 rs3 m3 = Next rs4 m4 ->
  rs2#PC = Val.offset_ptr rs1#PC Ptrofs.one ->
  rs3#PC = Val.offset_ptr rs2#PC Ptrofs.one ->
  rs4#PC = Val.offset_ptr rs3#PC Ptrofs.one ->
  exec_straight (i1 :: i2 :: i3 :: c) rs1 m1 c rs4 m4.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  eapply exec_straight_two; eauto.
Qed.

(** The following lemmas show that straight-line executions
  (predicate [exec_straight]) correspond to correct Asm executions. *)

Lemma exec_straight_steps_1:
  forall c rs m c' rs' m',
  exec_straight c rs m c' rs' m' ->
  list_length_z (fn_code fn) <= Ptrofs.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr ge b = Some (Internal fn) ->
  code_tail (Ptrofs.unsigned ofs) (fn_code fn) c ->
  plus step ge (State rs m) E0 (State rs' m').
Proof.
  induction 1; intros.
  apply plus_one.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  eapply plus_left'.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  apply IHexec_straight with b (Ptrofs.add ofs Ptrofs.one).
  auto. rewrite H0. rewrite H3. reflexivity.
  auto.
  apply code_tail_next_int with i; auto.
  traceEq.
Qed.

Lemma exec_straight_steps_2:
  forall c rs m c' rs' m',
  exec_straight c rs m c' rs' m' ->
  list_length_z (fn_code fn) <= Ptrofs.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr ge b = Some (Internal fn) ->
  code_tail (Ptrofs.unsigned ofs) (fn_code fn) c ->
  exists ofs',
     rs'#PC = Vptr b ofs'
  /\ code_tail (Ptrofs.unsigned ofs') (fn_code fn) c'.
Proof.
  induction 1; intros.
  exists (Ptrofs.add ofs Ptrofs.one). split.
  rewrite H0. rewrite H2. auto.
  apply code_tail_next_int with i1; auto.
  apply IHexec_straight with (Ptrofs.add ofs Ptrofs.one).
  auto. rewrite H0. rewrite H3. reflexivity. auto.
  apply code_tail_next_int with i; auto.
Qed.

End STRAIGHTLINE.

(** * Properties of the Mach call stack *)

Section MATCH_STACK.

Variable ge: Mach.genv.

Inductive match_stack: list Mach.stackframe -> Prop :=
  | match_stack_nil:
      match_stack nil
  | match_stack_cons: forall fb sp ra c s f tf tc,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      transl_code_at_pc ge ra fb f c false tf tc ->
      sp <> Vundef ->
      match_stack s ->
      match_stack (Stackframe fb sp ra c :: s).

Lemma parent_sp_def: forall s, match_stack s -> parent_sp s <> Vundef.
Proof.
  induction 1; simpl.
  unfold Vnullptr; destruct Archi.ptr64; congruence.
  auto.
Qed.

Lemma parent_ra_def: forall s, match_stack s -> parent_ra s <> Vundef.
Proof.
  induction 1; simpl.
  unfold Vnullptr; destruct Archi.ptr64; congruence.
  inv H0. congruence.
Qed.

Lemma lessdef_parent_sp:
  forall s v,
  match_stack s -> Val.lessdef (parent_sp s) v -> v = parent_sp s.
Proof.
  intros. inv H0. auto. exploit parent_sp_def; eauto. tauto.
Qed.

Lemma lessdef_parent_ra:
  forall s v,
  match_stack s -> Val.lessdef (parent_ra s) v -> v = parent_ra s.
Proof.
  intros. inv H0. auto. exploit parent_ra_def; eauto. tauto.
Qed.

End MATCH_STACK.


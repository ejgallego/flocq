Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_prop.
Require Import Flocq_rnd_generic.
Require Import Flocq_float_prop.
Require Import Flocq_ulp.
Require Import Flocq_rnd_FIX.
Require Import Flocq_rnd_FLX.
Require Import Flocq_rnd_FLT.

Section Flocq_rnd_NE.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Section Flocq_rnd_gNE.

Variable fexp : Z -> Z.

Variable prop_exp : valid_exp fexp.

Notation format := (generic_format beta fexp).
Notation canonic := (canonic beta fexp).

Definition gNE_prop x f :=
  exists g : float beta, canonic f g /\ Zeven (Fnum g) /\
    forall f2 : R, forall g2 : float beta, Rnd_N_pt format x f2 ->
    canonic f2 g2 -> Zeven (Fnum g2) -> (Rabs f2 <= Rabs f)%R.

Definition Rnd_gNE_pt := Rnd_NG_pt format gNE_prop.

Definition Rnd_gNE (rnd : R -> R) :=
  forall x : R, Rnd_gNE_pt x (rnd x).

Theorem Rnd_gNE_pt_sym :
  forall x f : R,
  Rnd_gNE_pt (-x) (-f) -> Rnd_gNE_pt x f.
Proof.
apply Rnd_NG_pt_sym.
apply generic_format_sym.
clear. unfold gNE_prop.
intros x f ((m, e), (Hfg, (Hg, H))).
exists (Float beta (-m) e).
split.
now apply canonic_sym.
split.
rewrite Zopp_eq_mult_neg_1.
now apply Zeven_mult_Zeven_l.
intros f2 g2 Hf2 Hfg2 Hg2.
rewrite Rabs_Ropp, <- (Rabs_Ropp f2).
apply H with (Float beta (-Fnum g2) (Fexp g2)).
apply Rnd_N_pt_sym.
apply generic_format_sym.
now rewrite Ropp_involutive.
apply canonic_sym.
exact Hfg2.
rewrite Zopp_eq_mult_neg_1.
now apply Zeven_mult_Zeven_l.
Qed.

Theorem canonic_imp_Fnum :
  forall x, forall f : float beta,
  x <> R0 ->
  canonic x f ->
  (Zabs (Fnum f) < Zpower (radix_val beta) (projT1 (ln_beta beta x) - Fexp f))%Z.
Proof.
intros x f Hx.
unfold Flocq_rnd_generic.canonic.
destruct (ln_beta beta x) as (ex, H).
simpl.
specialize (H Hx).
intros (H1, H2).
destruct (Zle_or_lt (Fexp f) ex) as [He|He].
(* . *)
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow (Fexp f)).
apply bpow_gt_0.
replace (Z2R (Zabs (Fnum f)) * bpow (Fexp f))%R with (Rabs x).
rewrite Z2R_Zpower, <- bpow_add.
now ring_simplify (ex - Fexp f + Fexp f)%Z.
omega.
rewrite H1.
apply abs_F2R.
(* . *)
elim (Rlt_not_ge _ _ (proj2 H)).
apply Rle_ge.
rewrite H1.
destruct f as (xm, xe).
rewrite abs_F2R.
unfold F2R. simpl.
rewrite <- (Rmult_1_l (bpow ex)).
apply Rmult_le_compat.
now apply (Z2R_le 0 1).
apply bpow_ge_0.
apply (Z2R_le 1).
apply (Zlt_le_succ 0).
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow xe).
apply bpow_gt_0.
rewrite Rmult_0_l.
replace (Z2R (Zabs xm) * bpow xe)%R with (Rabs x).
now apply Rabs_pos_lt.
rewrite H1.
apply abs_F2R.
apply -> bpow_le.
now apply Zlt_le_weak.
Qed.

Theorem Rnd_gNE_pt_unicity_prop :
  Rnd_NG_pt_unicity_prop format gNE_prop.
Proof.
intros x d u Hxd1 Hxd2 Hxu1 Hxu2 Hd Hu.
assert (H: Rabs d = Rabs u).
(* . *)
destruct Hd as (gd, Hd).
destruct Hu as (gu, Hu).
apply Rle_antisym.
now apply Hu with gd.
now apply Hd with gu.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
(* . *)
rewrite (Rabs_pos_eq d) in H.
rewrite H.
apply Rabs_pos_eq.
apply Rnd_N_pt_pos with format x.
apply generic_format_0.
exact Hx.
exact Hxu2.
apply Rnd_N_pt_pos with format x.
apply generic_format_0.
exact Hx.
exact Hxd2.
(* . *)
rewrite (Rabs_left1 u) in H.
rewrite <- (Ropp_involutive d), <- (Ropp_involutive u).
apply sym_eq.
apply f_equal.
rewrite <- H.
apply Rabs_left1.
apply Rnd_N_pt_neg with format x.
apply generic_format_0.
now apply Rlt_le.
exact Hxd2.
apply Rnd_N_pt_neg with format x.
apply generic_format_0.
now apply Rlt_le.
exact Hxu2.
Qed.

Theorem Rnd_gNE_pt_unicity :
  forall x f1 f2 : R,
  Rnd_gNE_pt x f1 -> Rnd_gNE_pt x f2 ->
  f1 = f2.
Proof.
apply Rnd_NG_pt_unicity.
apply Rnd_gNE_pt_unicity_prop.
Qed.

Theorem Rnd_gNE_pt_monotone :
  rounding_pred_monotone Rnd_gNE_pt.
Proof.
apply Rnd_NG_pt_monotone.
apply Rnd_gNE_pt_unicity_prop.
Qed.

Theorem Rnd_gNE_pt_refl :
  forall x : R, format x ->
  Rnd_gNE_pt x x.
Proof.
intros x Hx.
split.
now apply Rnd_N_pt_refl.
right.
intros f Hf.
now apply Rnd_N_pt_idempotent with format.
Qed.

Theorem Rnd_gNE_pt_idempotent :
  forall x f : R,
  Rnd_gNE_pt x f -> format x ->
  f = x.
Proof.
intros x f Hxf Hx.
destruct Hxf as (Hxf1,_).
now apply Rnd_N_pt_idempotent with format.
Qed.

(*
Theorem Rnd_gNE_pt_total :
  rounding_pred_total Rnd_gNE_pt.
Proof.
apply satisfies_any_imp_NG.
now apply generic_format_satisfies_any.
unfold NG_existence_prop, gNE_prop.
intros x d u Hd Hu.
Abort.
*)

Definition NE_prop (_ : R) f :=
  exists g : float beta, canonic f g /\ Zeven (Fnum g).

Definition Rnd_NE_pt :=
  Rnd_NG_pt format NE_prop.

Definition DN_UP_parity_pos_prop :=
  forall x xd xu cd cu,
  (0 < x)%R ->
  ~ format x ->
  canonic xd cd ->
  canonic xu cu ->
  Rnd_DN_pt format x xd ->
  Rnd_UP_pt format x xu ->
  Zodd (Fnum cd + Fnum cu).

Definition DN_UP_parity_prop :=
  forall x xd xu cd cu,
  ~ format x ->
  canonic xd cd ->
  canonic xu cu ->
  Rnd_DN_pt format x xd ->
  Rnd_UP_pt format x xu ->
  Zodd (Fnum cd + Fnum cu).

Theorem DN_UP_parity_aux :
  DN_UP_parity_pos_prop ->
  DN_UP_parity_prop.
Proof.
intros Hpos x xd xu cd cu Hfx Hd Hu Hxd Hxu.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].
(* . *)
exact (Hpos x xd xu cd cu Hx Hfx Hd Hu Hxd Hxu).
elim Hfx.
rewrite <- Hx.
apply generic_format_0.
(* . *)
assert (Hx': (0 < -x)%R).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive, Ropp_0.
destruct cd as (md, ed).
destruct cu as (mu, eu).
replace (Fnum (Float beta md ed) + Fnum (Float beta mu eu))%Z
  with (-1 * ((Fnum (Float beta (-mu) ed) + Fnum (Float beta (-md) eu))))%Z
  by (unfold Fnum ; ring).
apply Zodd_mult_Zodd.
now apply (Zodd_pred 0).
apply (Hpos (-x)%R (-xu)%R (-xd)%R (Float beta (-mu) eu) (Float beta (-md) ed)).
exact Hx'.
intros H.
apply Hfx.
rewrite <- (Ropp_involutive x).
now apply generic_format_sym.
now apply canonic_sym.
now apply canonic_sym.
apply Rnd_UP_DN_pt_sym.
apply generic_format_sym.
now rewrite 2!Ropp_involutive.
apply Rnd_DN_UP_pt_sym.
apply generic_format_sym.
now rewrite 2!Ropp_involutive.
Qed.

Theorem Rnd_NE_pt_aux :
  DN_UP_parity_prop ->
  forall x f,
  ( Rnd_gNE_pt x f <-> Rnd_NE_pt x f ).
Proof.
intros HP x f.
split.
(* . *)
intros (H1, [H2|H2]).
(* . . *)
split.
exact H1.
left.
destruct H2 as (g, (H2, (H3, H4))).
exists g.
repeat split ; try eapply H2 ; easy.
(* . . *)
split.
exact H1.
now right.
(* . *)
intros (H1, [H2|H2]).
(* . . *)
split.
exact H1.
left.
destruct H2 as (g, (H2, H3)).
exists g.
repeat split ; try eapply H2 ; trivial.
intros f2 g2 Hf2 Hfg2 Hg2.
right.
apply f_equal.
destruct (Req_dec x f) as [Hx|Hx].
rewrite <- Hx.
apply Rnd_N_pt_idempotent with format.
exact Hf2.
rewrite Hx.
apply H1.
assert (Hxf: ~format x).
intros H.
apply Hx.
apply sym_eq.
now apply Rnd_N_pt_idempotent with format.
destruct (Rnd_N_pt_DN_or_UP _ _ _ H1) as [Hxf1|Hxf1].
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hf2) as [Hxf2|Hxf2].
apply Rnd_DN_pt_unicity with (1 := Hxf2) (2 := Hxf1).
elim (Zodd_not_Zeven (Fnum g + Fnum g2)).
now apply (HP x f f2).
now apply Zeven_plus_Zeven.
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hf2) as [Hxf2|Hxf2].
elim (Zodd_not_Zeven (Fnum g2 + Fnum g)).
now apply (HP x f2 f).
now apply Zeven_plus_Zeven.
apply Rnd_UP_pt_unicity with (1 := Hxf2) (2 := Hxf1).
(* . . *)
split.
exact H1.
now right.
Qed.

End Flocq_rnd_gNE.

Section Flocq_rnd_NE_generic.

Variable fexp : Z -> Z.

Hypothesis valid_fexp : valid_exp fexp.

Hypothesis strong_fexp : Zodd (radix_val beta) \/ forall e,
 ((fexp e < e)%Z -> (fexp (e + 1) < e)%Z) /\ ((e <= fexp e)%Z -> fexp (fexp e + 1) = fexp e).

Theorem DN_UP_parity_generic_pos :
  DN_UP_parity_pos_prop fexp.
Proof.
intros x xd xu cd cu H0x Hfx Hd Hu Hxd Hxu.
destruct (ln_beta beta x) as (ex, Hexa).
specialize (Hexa (Rgt_not_eq _ _ H0x)).
generalize Hexa. intros Hex.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ H0x)) in Hex.
destruct (Zle_or_lt ex (fexp ex)) as [Hxe|Hxe].
(* small x *)
assert (Hd3 : Fnum cd = Z0).
apply eq_Z2R.
apply Rmult_eq_reg_r with (bpow (Fexp cd)).
rewrite Rmult_0_l.
fold (F2R cd).
rewrite <- (proj1 Hd).
apply Rnd_DN_pt_unicity with (1 := Hxd).
now apply generic_DN_pt_small_pos with (2 := Hex).
apply Rgt_not_eq.
apply bpow_gt_0.
assert (Hu3 : cu = Float beta (1 * Zpower (radix_val beta) (fexp ex - fexp (fexp ex + 1))) (fexp (fexp ex + 1))).
apply canonic_unicity with (1 := Hu).
replace xu with (bpow (fexp ex)).
split.
rewrite <- F2R_bpow.
apply F2R_change_exp.
now eapply valid_fexp.
simpl.
now rewrite ln_beta_bpow.
apply Rnd_UP_pt_unicity with (2 := Hxu).
now apply generic_UP_pt_small_pos.
rewrite Hd3, Hu3.
rewrite Zmult_1_l.
simpl.
destruct strong_fexp as [H|H].
apply Zodd_Zpower with (2 := H).
apply Zle_minus_le_0.
now eapply valid_fexp.
rewrite (proj2 (H ex)).
now rewrite Zminus_diag.
exact Hxe.
(* large x *)
assert (Hd4: (bpow (ex - 1) <= Rabs xd < bpow ex)%R).
rewrite Rabs_pos_eq.
split.
apply Hxd.
apply generic_format_bpow.
ring_simplify (ex - 1 + 1)%Z.
omega.
apply Hex.
apply Rle_lt_trans with (2 := proj2 Hex).
apply Hxd.
apply Hxd.
apply generic_format_0.
now apply Rlt_le.
assert (Hxe2 : (fexp (ex + 1) <= ex)%Z) by now eapply valid_fexp.
destruct (total_order_T (bpow ex) xu) as [[Hu2|Hu2]|Hu2].
(* - xu > bpow ex  *)
elim (Rlt_not_le _ _ Hu2).
apply Rnd_UP_pt_monotone with (generic_format beta fexp) x (bpow ex).
exact Hxu.
split.
apply generic_format_bpow.
exact Hxe2.
split.
apply Rle_refl.
easy.
now apply Rlt_le.
(* - xu = bpow ex *)
assert (Hu3: cu = Float beta (1 * Zpower (radix_val beta) (ex - fexp (ex + 1))) (fexp (ex + 1))).
apply canonic_unicity with (1 := Hu).
rewrite <- Hu2.
split.
rewrite <- F2R_change_exp.
apply sym_eq.
apply F2R_bpow.
exact Hxe2.
simpl.
apply f_equal.
apply sym_eq.
apply ln_beta_bpow.
assert (Hd3: cd = Float beta (Zpower (radix_val beta) (ex - fexp ex) - 1) (fexp ex)).
apply canonic_unicity with (1 := Hd).
generalize (ulp_pred_succ_pt beta _ valid_fexp x xd xu Hfx Hxd Hxu).
intros Hud.
split.
unfold F2R. simpl.
rewrite minus_Z2R.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Z2R_Zpower, <- bpow_add.
ring_simplify (ex - fexp ex + fexp ex)%Z.
rewrite Hu2, Hud.
unfold ulp.
rewrite ln_beta_unique with beta x ex.
unfold FLX_exp, F2R.
simpl. ring.
rewrite Rabs_pos_eq.
exact Hex.
now apply Rlt_le.
apply Zle_minus_le_0.
now apply Zlt_le_weak.
simpl.
now rewrite ln_beta_unique with (1 := Hd4).
rewrite Hd3, Hu3.
unfold Fnum.
ring_simplify (Zpower (radix_val beta) (ex - fexp ex) - 1 + 1 * Zpower (radix_val beta) (ex - fexp (ex + 1)))%Z.
apply Zodd_pred.
destruct (Zeven_odd_dec (radix_val beta)) as [Hdo|Hdo].
apply Zeven_plus_Zeven.
apply Zeven_Zpower with (2 := Hdo).
omega.
apply Zeven_Zpower with (2 := Hdo).
destruct strong_fexp.
now elim Zeven_not_Zodd with (1 := Hdo).
generalize (proj1 (H _) Hxe).
omega.
apply Zodd_plus_Zodd.
apply Zodd_Zpower with (2 := Hdo).
omega.
apply Zodd_Zpower with (2 := Hdo).
apply Zle_minus_le_0.
exact Hxe2.
(* - xu < bpow ex *)
generalize (ulp_pred_succ_pt beta _ valid_fexp x xd xu Hfx Hxd Hxu).
rewrite (proj1 Hd), (proj1 Hu).
unfold ulp, F2R.
rewrite (proj2 Hd), (proj2 Hu).
rewrite ln_beta_unique with beta xu ex.
rewrite ln_beta_unique with (1 := Hd4).
rewrite ln_beta_unique with (1 := Hexa).
simpl.
rewrite <- Rmult_plus_distr_r.
intros H.
replace (Fnum cu) with (Fnum cd + 1)%Z.
replace (Fnum cd + (Fnum cd + 1))%Z with (2 * Fnum cd + 1)%Z by ring.
apply Zodd_Sn.
now apply Zeven_mult_Zeven_l.
apply sym_eq.
apply eq_Z2R.
rewrite plus_Z2R.
apply Rmult_eq_reg_r with (1 := H).
apply Rgt_not_eq.
apply bpow_gt_0.
rewrite Rabs_pos_eq.
split.
apply Rle_trans with (1 := proj1 Hex).
apply Hxu.
exact Hu2.
apply Rlt_le.
apply Rlt_le_trans with (1 := H0x).
apply Hxu.
Qed.

Theorem Rnd_NE_pt_generic :
  forall x f,
  ( Rnd_gNE_pt fexp x f <-> Rnd_NE_pt fexp x f ).
Proof.
apply Rnd_NE_pt_aux.
apply DN_UP_parity_aux.
exact DN_UP_parity_generic_pos.
Qed.

End Flocq_rnd_NE_generic.

End Flocq_rnd_NE.

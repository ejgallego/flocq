Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_float_prop.
Require Import Fcore_ulp.

Section Fcore_rnd_NE.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Variable prop_exp : valid_exp fexp.

Notation format := (generic_format beta fexp).
Notation canonic := (canonic beta fexp).

Definition NE_prop (_ : R) f :=
  exists g : float beta, f = F2R g /\ canonic g /\ Zeven (Fnum g).

Definition Rnd_NE_pt :=
  Rnd_NG_pt format NE_prop.

Definition DN_UP_parity_pos_prop :=
  forall x xd xu,
  (0 < x)%R ->
  ~ format x ->
  canonic xd ->
  canonic xu ->
  Rnd_DN_pt format x (F2R xd) ->
  Rnd_UP_pt format x (F2R xu) ->
  Zodd (Fnum xd + Fnum xu).

Definition DN_UP_parity_prop :=
  forall x xd xu,
  ~ format x ->
  canonic xd ->
  canonic xu ->
  Rnd_DN_pt format x (F2R xd) ->
  Rnd_UP_pt format x (F2R xu) ->
  Zodd (Fnum xd + Fnum xu).

Theorem DN_UP_parity_aux :
  DN_UP_parity_pos_prop ->
  DN_UP_parity_prop.
Proof.
intros Hpos x xd xu Hfx Hd Hu Hxd Hxu.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].
(* . *)
exact (Hpos x xd xu Hx Hfx Hd Hu Hxd Hxu).
elim Hfx.
rewrite <- Hx.
apply generic_format_0.
(* . *)
assert (Hx': (0 < -x)%R).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive, Ropp_0.
destruct xd as (md, ed).
destruct xu as (mu, eu).
simpl.
replace (md + mu)%Z
  with (-1 * ((Fnum (Float beta (-mu) eu)) + Fnum (Float beta (-md) ed)))%Z
  by (unfold Fnum ; ring).
apply Zodd_mult_Zodd.
now apply (Zodd_pred 0).
apply (Hpos (-x)%R _ _ Hx').
intros H.
apply Hfx.
rewrite <- Ropp_involutive.
now apply generic_format_opp.
now apply canonic_opp.
now apply canonic_opp.
apply Rnd_UP_DN_pt_sym.
apply generic_format_opp.
rewrite <- opp_F2R.
now rewrite 2!Ropp_involutive.
apply Rnd_DN_UP_pt_sym.
apply generic_format_opp.
rewrite <- opp_F2R.
now rewrite 2!Ropp_involutive.
Qed.

Hypothesis valid_fexp : valid_exp fexp.

Definition NE_ex_prop := Zodd (radix_val beta) \/ forall e,
  ((fexp e < e)%Z -> (fexp (e + 1) < e)%Z) /\ ((e <= fexp e)%Z -> fexp (fexp e + 1) = fexp e).

Hypothesis strong_fexp : NE_ex_prop.

Theorem DN_UP_parity_generic_pos :
  DN_UP_parity_pos_prop.
Proof.
intros x xd xu H0x Hfx Hd Hu Hxd Hxu.
destruct (ln_beta beta x) as (ex, Hexa).
specialize (Hexa (Rgt_not_eq _ _ H0x)).
generalize Hexa. intros Hex.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ H0x)) in Hex.
destruct (Zle_or_lt ex (fexp ex)) as [Hxe|Hxe].
(* small x *)
assert (Hd3 : Fnum xd = Z0).
apply F2R_eq_0_reg with beta (Fexp xd).
change (F2R xd = R0).
apply Rnd_DN_pt_unicity with (1 := Hxd).
now apply generic_DN_pt_small_pos with (2 := Hex).
assert (Hu3 : xu = Float beta (1 * Zpower (radix_val beta) (fexp ex - fexp (fexp ex + 1))) (fexp (fexp ex + 1))).
apply canonic_unicity with (1 := Hu).
apply (f_equal fexp).
rewrite <- F2R_change_exp.
now rewrite F2R_bpow, ln_beta_bpow.
now eapply valid_fexp.
rewrite <- F2R_change_exp.
rewrite F2R_bpow.
apply sym_eq.
apply Rnd_UP_pt_unicity with (2 := Hxu).
now apply generic_UP_pt_small_pos.
now eapply valid_fexp.
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
assert (Hd4: (bpow (ex - 1) <= Rabs (F2R xd) < bpow ex)%R).
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
assert (Hud: (F2R xu = F2R xd + ulp beta fexp x)%R).
apply Rnd_UP_pt_unicity with (1 := Hxu).
now apply ulp_DN_UP_pt.
destruct (total_order_T (bpow ex) (F2R xu)) as [[Hu2|Hu2]|Hu2].
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
assert (Hu3: xu = Float beta (1 * Zpower (radix_val beta) (ex - fexp (ex + 1))) (fexp (ex + 1))).
apply canonic_unicity with (1 := Hu).
apply (f_equal fexp).
rewrite <- F2R_change_exp.
now rewrite F2R_bpow, ln_beta_bpow.
now eapply valid_fexp.
rewrite <- Hu2.
apply sym_eq.
rewrite <- F2R_change_exp.
apply F2R_bpow.
exact Hxe2.
assert (Hd3: xd = Float beta (Zpower (radix_val beta) (ex - fexp ex) - 1) (fexp ex)).
assert (H: F2R xd = F2R (Float beta (Zpower (radix_val beta) (ex - fexp ex) - 1) (fexp ex))).
unfold F2R. simpl.
rewrite minus_Z2R.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Z2R_Zpower, <- bpow_add.
ring_simplify (ex - fexp ex + fexp ex)%Z.
rewrite Hu2, Hud.
unfold ulp, canonic_exponent.
rewrite ln_beta_unique with beta x ex.
unfold F2R.
simpl. ring.
rewrite Rabs_pos_eq.
exact Hex.
now apply Rlt_le.
apply Zle_minus_le_0.
now apply Zlt_le_weak.
apply canonic_unicity with (1 := Hd) (3 := H).
apply (f_equal fexp).
rewrite <- H.
apply sym_eq.
now apply ln_beta_unique.
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
revert Hud.
unfold ulp, F2R.
rewrite Hd, Hu.
unfold canonic_exponent.
rewrite ln_beta_unique with beta (F2R xu) ex.
rewrite ln_beta_unique with (1 := Hd4).
rewrite ln_beta_unique with (1 := Hexa).
intros H.
replace (Fnum xu) with (Fnum xd + 1)%Z.
replace (Fnum xd + (Fnum xd + 1))%Z with (2 * Fnum xd + 1)%Z by ring.
apply Zodd_Sn.
now apply Zeven_mult_Zeven_l.
apply sym_eq.
apply eq_Z2R.
rewrite plus_Z2R.
apply Rmult_eq_reg_r with (bpow (fexp ex)).
rewrite H.
simpl. ring.
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

Theorem Rnd_NE_pt_total :
  rounding_pred_total Rnd_NE_pt.
Proof.
apply satisfies_any_imp_NG.
now apply generic_format_satisfies_any.
intros x d u Hf Hd Hu.
generalize (proj1 Hd).
unfold generic_format.
set (ed := canonic_exponent beta fexp d).
set (md := Ztrunc (d * Fcore_Raux.bpow beta (-ed))).
intros Hd1.
destruct (Zeven_odd_dec md) as [He|Ho].
right.
exists (Float beta md ed).
unfold Fcore_generic_fmt.canonic.
rewrite <- Hd1.
now repeat split.
left.
generalize (proj1 Hu).
unfold generic_format.
set (eu := canonic_exponent beta fexp u).
set (mu := Ztrunc (u * Fcore_Raux.bpow beta (-eu))).
intros Hu1.
rewrite Hu1.
eexists ; repeat split.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hu1.
simpl.
replace mu with (md + mu + (-1) * md)%Z by ring.
apply Zodd_plus_Zodd.
apply (DN_UP_parity_aux DN_UP_parity_generic_pos x (Float beta md ed) (Float beta mu eu)).
exact Hf.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hd1.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hu1.
now rewrite <- Hd1.
now rewrite <- Hu1.
now apply Zodd_mult_Zodd.
Qed.

Theorem Rnd_NE_pt_monotone :
  rounding_pred_monotone Rnd_NE_pt.
Proof.
apply Rnd_NG_pt_monotone.
intros x d u Hd Hdn Hu Hun (cd, (Hd1, Hd2)) (cu, (Hu1, Hu2)).
destruct (Req_dec x d) as [Hx|Hx].
rewrite <- Hx.
apply sym_eq.
apply Rnd_UP_pt_idempotent with (1 := Hu).
rewrite Hx.
apply Hd.
absurd (Zodd (Fnum cd + Fnum cu)).
apply Zeven_not_Zodd.
now apply Zeven_plus_Zeven.
apply (DN_UP_parity_aux DN_UP_parity_generic_pos x cd cu) ; try easy.
intros Hf.
apply Hx.
apply sym_eq.
now apply Rnd_DN_pt_idempotent with (1 := Hd).
now rewrite <- Hd1.
now rewrite <- Hu1.
Qed.

Theorem Rnd_NE_pt_rounding :
  rounding_pred Rnd_NE_pt.
split.
apply Rnd_NE_pt_total.
apply Rnd_NE_pt_monotone.
Qed.

End Fcore_rnd_NE.

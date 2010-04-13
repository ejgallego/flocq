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
  F2R xd = rounding beta fexp ZrndDN x ->
  F2R xu = rounding beta fexp ZrndUP x ->
  Zodd (Fnum xd + Fnum xu).

Definition DN_UP_parity_prop :=
  forall x xd xu,
  ~ format x ->
  canonic xd ->
  canonic xu ->
  F2R xd = rounding beta fexp ZrndDN x ->
  F2R xu = rounding beta fexp ZrndUP x ->
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
rewrite generic_DN_opp, <- opp_F2R.
now apply f_equal.
rewrite generic_UP_opp, <- opp_F2R.
now apply f_equal.
Qed.

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
rewrite Hxd.
apply generic_DN_small_pos with (1 := Hex) (2 := Hxe).
assert (Hu3 : xu = Float beta (1 * Zpower (radix_val beta) (fexp ex - fexp (fexp ex + 1))) (fexp (fexp ex + 1))).
apply canonic_unicity with (1 := Hu).
apply (f_equal fexp).
rewrite <- F2R_change_exp.
now rewrite F2R_bpow, ln_beta_bpow.
now eapply prop_exp.
rewrite <- F2R_change_exp.
rewrite F2R_bpow.
apply sym_eq.
rewrite Hxu.
apply sym_eq.
apply generic_UP_small_pos with (1 := Hex) (2 := Hxe).
now eapply prop_exp.
rewrite Hd3, Hu3.
rewrite Zmult_1_l.
simpl.
destruct strong_fexp as [H|H].
apply Zodd_Zpower with (2 := H).
apply Zle_minus_le_0.
now eapply prop_exp.
rewrite (proj2 (H ex)).
now rewrite Zminus_diag.
exact Hxe.
(* large x *)
assert (Hd4: (bpow (ex - 1) <= Rabs (F2R xd) < bpow ex)%R).
rewrite Rabs_pos_eq.
rewrite Hxd.
split.
apply (generic_DN_pt beta fexp prop_exp x).
apply generic_format_bpow.
ring_simplify (ex - 1 + 1)%Z.
omega.
apply Hex.
apply Rle_lt_trans with (2 := proj2 Hex).
apply (generic_DN_pt beta fexp prop_exp x).
rewrite Hxd.
apply (generic_DN_pt beta fexp prop_exp x).
apply generic_format_0.
now apply Rlt_le.
assert (Hxe2 : (fexp (ex + 1) <= ex)%Z) by now eapply prop_exp.
assert (Hud: (F2R xu = F2R xd + ulp beta fexp x)%R).
rewrite Hxu, Hxd.
now apply ulp_DN_UP.
destruct (total_order_T (bpow ex) (F2R xu)) as [[Hu2|Hu2]|Hu2].
(* - xu > bpow ex  *)
elim (Rlt_not_le _ _ Hu2).
rewrite Hxu.
now apply generic_UP_large_pos_le_pow.
(* - xu = bpow ex *)
assert (Hu3: xu = Float beta (1 * Zpower (radix_val beta) (ex - fexp (ex + 1))) (fexp (ex + 1))).
apply canonic_unicity with (1 := Hu).
apply (f_equal fexp).
rewrite <- F2R_change_exp.
now rewrite F2R_bpow, ln_beta_bpow.
now eapply prop_exp.
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
rewrite Hxu.
apply (generic_UP_pt beta fexp prop_exp x).
exact Hu2.
apply Rlt_le.
apply Rlt_le_trans with (1 := H0x).
rewrite Hxu.
apply (generic_UP_pt beta fexp prop_exp x).
Qed.

Theorem DN_UP_parity_generic :
  DN_UP_parity_prop.
Proof.
apply DN_UP_parity_aux.
apply DN_UP_parity_generic_pos.
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
set (md := Ztrunc (scaled_mantissa beta fexp d)).
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
set (mu := Ztrunc (scaled_mantissa beta fexp u)).
intros Hu1.
rewrite Hu1.
eexists ; repeat split.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hu1.
simpl.
replace mu with (md + mu + (-1) * md)%Z by ring.
apply Zodd_plus_Zodd.
apply (DN_UP_parity_generic x (Float beta md ed) (Float beta mu eu)).
exact Hf.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hd1.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hu1.
rewrite <- Hd1.
apply Rnd_DN_pt_unicity with (1 := Hd).
now apply generic_DN_pt.
rewrite <- Hu1.
apply Rnd_UP_pt_unicity with (1 := Hu).
now apply generic_UP_pt.
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
rewrite <- Hd1.
apply Rnd_DN_pt_unicity with (1 := Hd).
now apply generic_DN_pt.
rewrite <- Hu1.
apply Rnd_UP_pt_unicity with (1 := Hu).
now apply generic_UP_pt.
Qed.

Theorem Rnd_NE_pt_rounding :
  rounding_pred Rnd_NE_pt.
split.
apply Rnd_NE_pt_total.
apply Rnd_NE_pt_monotone.
Qed.

Section Znearest.

Variable choice : R -> bool.

Definition Znearest x :=
  match Rcompare (x - Z2R (Zfloor x)) (/2) with
  | Lt => Zfloor x
  | Eq => if choice x then Zceil x else Zfloor x
  | Gt => Zceil x
  end.

Theorem Znearest_Z2R :
  forall n, Znearest (Z2R n) = n.
Proof.
intros n.
unfold Znearest.
rewrite Zfloor_Z2R.
rewrite Rcompare_Lt.
easy.
unfold Rminus.
rewrite Rplus_opp_r.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
Qed.

Theorem Znearest_DN_or_UP :
  forall x,
  Znearest x = Zfloor x \/ Znearest x = Zceil x.
Proof.
intros x.
unfold Znearest.
case Rcompare_spec ; intros _.
now left.
case (choice x).
now right.
now left.
now right.
Qed.

Theorem Znearest_ge_floor :
  forall x,
  (Zfloor x <= Znearest x)%Z.
Proof.
intros x.
destruct (Znearest_DN_or_UP x) as [Hx|Hx] ; rewrite Hx.
apply Zle_refl.
apply le_Z2R.
apply Rle_trans with x.
apply Zfloor_lb.
apply Zceil_ub.
Qed.

Theorem Znearest_le_ceil :
  forall x,
  (Znearest x <= Zceil x)%Z.
Proof.
intros x.
destruct (Znearest_DN_or_UP x) as [Hx|Hx] ; rewrite Hx.
apply le_Z2R.
apply Rle_trans with x.
apply Zfloor_lb.
apply Zceil_ub.
apply Zle_refl.
Qed.

Theorem Znearest_monotone :
  forall x y, (x <= y)%R ->
  (Znearest x <= Znearest y)%Z.
Proof.
intros x y Hxy.
destruct (Rle_or_lt (Z2R (Zceil x)) y) as [H|H].
apply Zle_trans with (1 := Znearest_le_ceil x).
apply Zle_trans with (2 := Znearest_ge_floor y).
now apply Zfloor_lub.
(* . *)
assert (Hf: Zfloor y = Zfloor x).
apply Zfloor_imp.
split.
apply Rle_trans with (2 := Zfloor_lb y).
apply Z2R_le.
now apply Zfloor_le.
apply Rlt_le_trans with (1 := H).
apply Z2R_le.
apply Zceil_glb.
apply Rlt_le.
rewrite plus_Z2R.
apply Zfloor_ub.
(* . *)
unfold Znearest at 1.
case Rcompare_spec ; intro Hx.
(* .. *)
rewrite <- Hf.
apply Znearest_ge_floor.
(* .. *)
unfold Znearest.
rewrite Hf.
case Rcompare_spec ; intro Hy.
elim Rlt_not_le with (1 := Hy).
rewrite <- Hx.
now apply Rplus_le_compat_r.
replace y with x.
apply Zle_refl.
apply Rplus_eq_reg_l with (- Z2R (Zfloor x))%R.
rewrite 2!(Rplus_comm (- (Z2R (Zfloor x)))).
change (x - Z2R (Zfloor x) = y - Z2R (Zfloor x))%R.
now rewrite Hy.
apply Zle_trans with (Zceil x).
case (choice x).
apply Zle_refl.
apply le_Z2R.
apply Rle_trans with x.
apply Zfloor_lb.
apply Zceil_ub.
now apply Zceil_le.
(* .. *)
unfold Znearest.
rewrite Hf.
rewrite Rcompare_Gt.
now apply Zceil_le.
apply Rlt_le_trans with (1 := Hx).
now apply Rplus_le_compat_r.
Qed.

Definition ZrndN := mkZrounding Znearest Znearest_monotone Znearest_Z2R.

Theorem Znearest_N_strict :
  forall x,
  (x - Z2R (Zfloor x) <> /2)%R ->
  (Rabs (x - Z2R (Znearest x)) < /2)%R.
Proof.
intros x Hx.
unfold Znearest.
case Rcompare_spec ; intros H.
rewrite Rabs_pos_eq.
exact H.
apply Rle_0_minus.
apply Zfloor_lb.
now elim Hx.
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
rewrite Zceil_floor_neq.
rewrite plus_Z2R.
simpl.
apply Ropp_lt_cancel.
apply Rplus_lt_reg_r with R1.
replace (1 + -/2)%R with (/2)%R by field.
now replace (1 + - (Z2R (Zfloor x) + 1 - x))%R with (x - Z2R (Zfloor x))%R by ring.
apply Rlt_not_eq.
apply Rplus_lt_reg_r with (- Z2R (Zfloor x))%R.
apply Rlt_trans with (/2)%R.
rewrite Rplus_opp_l.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
now rewrite <- (Rplus_comm x).
apply Rle_minus.
apply Zceil_ub.
Qed.

Theorem Znearest_N :
  forall x,
  (Rabs (x - Z2R (Znearest x)) <= /2)%R.
Proof.
intros x.
destruct (Req_dec (x - Z2R (Zfloor x)) (/2)) as [Hx|Hx].
assert (K: (Rabs (/2) <= /2)%R).
apply Req_le.
apply Rabs_pos_eq.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
destruct (Znearest_DN_or_UP x) as [H|H] ; rewrite H ; clear H.
now rewrite Hx.
rewrite Zceil_floor_neq.
rewrite plus_Z2R.
simpl.
replace (x - (Z2R (Zfloor x) + 1))%R with (x - Z2R (Zfloor x) - 1)%R by ring.
rewrite Hx.
rewrite Rabs_minus_sym.
now replace (1 - /2)%R with (/2)%R by field.
apply Rlt_not_eq.
apply Rplus_lt_reg_r with (- Z2R (Zfloor x))%R.
rewrite Rplus_opp_l, Rplus_comm.
fold (x - Z2R (Zfloor x))%R.
rewrite Hx.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
apply Rlt_le.
now apply Znearest_N_strict.
Qed.

End Znearest.

End Fcore_rnd_NE.

Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_float_prop.

Section Fcore_ulp.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Variable prop_exp : valid_exp fexp.

Definition ulp x := bpow (canonic_exponent beta fexp x).

Definition F := generic_format beta fexp.

Theorem ulp_DN_UP :
  forall x, ~ F x ->
  rounding beta fexp ZrndUP x = (rounding beta fexp ZrndDN x + ulp x)%R.
Proof.
intros x Fx.
unfold rounding, Zrnd, ulp. simpl.
unfold F2R. simpl.
rewrite Zceil_floor_neq.
rewrite plus_Z2R. simpl.
ring.
intros H.
apply Fx.
unfold F, generic_format.
unfold F2R. simpl.
rewrite <- H.
rewrite Ztrunc_Z2R.
rewrite H.
now rewrite scaled_mantissa_bpow.
Qed.

Theorem ulp_error :
  forall Zrnd x,
  (Rabs (rounding beta fexp Zrnd x - x) < ulp x)%R.
Proof.
intros Zrnd x.
destruct (generic_format_EM beta fexp prop_exp x) as [Hx|Hx].
(* x = rnd x *)
rewrite rounding_generic with (1 := Hx).
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply bpow_gt_0.
(* x <> rnd x *)
destruct (rounding_DN_or_UP beta fexp Zrnd x) as [H|H] ; rewrite H ; clear H.
(* . *)
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rplus_lt_reg_r with (rounding beta fexp ZrndDN x).
rewrite <- ulp_DN_UP with (1 := Hx).
ring_simplify.
assert (Hu: (x <= rounding beta fexp ZrndUP x)%R).
apply (generic_UP_pt beta fexp prop_exp x).
destruct Hu as [Hu|Hu].
exact Hu.
elim Hx.
rewrite Hu.
now apply generic_format_rounding.
apply Rle_minus.
apply (generic_DN_pt beta fexp prop_exp x).
(* . *)
rewrite Rabs_pos_eq.
rewrite ulp_DN_UP with (1 := Hx).
apply Rplus_lt_reg_r with (x - ulp x)%R.
ring_simplify.
assert (Hd: (rounding beta fexp ZrndDN x <= x)%R).
apply (generic_DN_pt beta fexp prop_exp x).
destruct Hd as [Hd|Hd].
exact Hd.
elim Hx.
rewrite <- Hd.
now apply generic_format_rounding.
apply Rle_0_minus.
apply (generic_UP_pt beta fexp prop_exp x).
Qed.

Theorem ulp_half_error_pt :
  forall x xr,
  Rnd_N_pt F x xr ->
  (Rabs (xr - x) <= /2 * ulp x)%R.
Proof.
intros x xr Hxr.
destruct (generic_format_EM beta fexp prop_exp x) as [Hx|Hx].
(* x = rnd x *)
rewrite Rnd_N_pt_idempotent with (1 := Hxr).
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply Rmult_le_pos.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
apply bpow_ge_0.
exact Hx.
(* x <> rnd x *)
set (d := rounding beta fexp ZrndDN x).
destruct Hxr as (Hr1, Hr2).
destruct (Rle_or_lt (x - d) (d + ulp x - x)) as [H|H].
(* . rnd(x) = rndd(x) *)
apply Rle_trans with (Rabs (d - x)).
apply Hr2.
apply (generic_DN_pt beta fexp prop_exp x).
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rmult_le_reg_r with 2%R.
now apply (Z2R_lt 0 2).
apply Rplus_le_reg_r with (d - x)%R.
ring_simplify.
apply Rle_trans with (1 := H).
right. field.
apply Rle_minus.
apply (generic_DN_pt beta fexp prop_exp x).
(* . rnd(x) = rndu(x) *)
assert (Hu: (d + ulp x)%R = rounding beta fexp ZrndUP x).
unfold d.
now rewrite <- ulp_DN_UP.
apply Rle_trans with (Rabs (d + ulp x - x)).
apply Hr2.
rewrite Hu.
apply (generic_UP_pt beta fexp prop_exp x).
rewrite Rabs_pos_eq.
apply Rmult_le_reg_r with 2%R.
now apply (Z2R_lt 0 2).
apply Rplus_le_reg_r with (- (d + ulp x - x))%R.
ring_simplify.
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
right. field.
apply Rle_0_minus.
rewrite Hu.
apply (generic_UP_pt beta fexp prop_exp x).
Qed.

Theorem ulp_monotone :
  ( forall m n, (m <= n)%Z -> (fexp m <= fexp n)%Z ) ->
  forall x y: R,
  (0 < x)%R -> (x <= y)%R ->
  (ulp x <= ulp y)%R.
Proof.
intros Hm x y Hx Hxy.
apply -> bpow_le.
apply Hm.
now apply ln_beta_monotone.
Qed.

Theorem ulp_bpow :
  forall e, ulp (bpow e) = bpow (fexp (e + 1)).
intros e.
unfold ulp.
apply f_equal.
apply canonic_exponent_fexp.
rewrite Rabs_pos_eq.
split.
ring_simplify (e + 1 - 1)%Z.
apply Rle_refl.
apply -> bpow_lt.
apply Zlt_succ.
apply bpow_ge_0.
Qed.

Theorem ulp_DN_pt_eq :
  forall x,
  (0 < rounding beta fexp ZrndDN x)%R ->
  ulp (rounding beta fexp ZrndDN x) = ulp x.
Proof.
intros x Hd.
unfold ulp.
now rewrite canonic_exponent_DN with (2 := Hd).
Qed.

End Fcore_ulp.

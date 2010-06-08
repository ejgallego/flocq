Require Import Fcore.

Section Fprop_relative.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Section Fprop_relative_generic.

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.

Variable rnd : Zrounding.

Theorem generic_bounded_relative_error :
  forall emin p,
  ( forall k, (emin < k)%Z -> (p <= k - fexp k)%Z ) ->
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (rounding beta fexp rnd x - x) < bpow (-p + 1) * Rabs x)%R.
Proof.
intros emin p Hmin m x Hx.
apply Rlt_le_trans with (ulp beta fexp x)%R.
now apply ulp_error.
unfold ulp, canonic_exponent.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx).
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_add.
apply -> bpow_le.
assert (emin < ex)%Z.
apply <- bpow_lt.
apply Rle_lt_trans with (2 := proj2 He).
unfold x.
rewrite abs_F2R.
apply bpow_le_F2R.
apply F2R_lt_reg with beta emin.
rewrite F2R_0, <- abs_F2R.
now apply Rabs_pos_lt.
generalize (Hmin ex).
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

Variable choice : R -> bool.

Theorem generic_bounded_relative_error_N :
  forall emin p,
  ( forall k, (emin < k)%Z -> (p <= k - fexp k)%Z ) ->
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (rounding beta fexp (ZrndN choice) x - x) <= /2 * bpow (-p + 1) * Rabs x)%R.
Proof.
intros emin p Hmin m x.
destruct (Req_dec x 0) as [Hx|Hx].
(* . *)
rewrite Hx, rounding_0.
unfold Rminus.
rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0.
rewrite Rmult_0_r.
apply Rle_refl.
(* . *)
apply Rle_trans with (/2 * ulp beta fexp x)%R.
now apply ulp_half_error.
unfold ulp, canonic_exponent.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx).
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_add.
apply -> bpow_le.
assert (emin < ex)%Z.
apply <- bpow_lt.
apply Rle_lt_trans with (2 := proj2 He).
unfold x.
rewrite abs_F2R.
apply bpow_le_F2R.
apply F2R_lt_reg with beta emin.
rewrite F2R_0, <- abs_F2R.
now apply Rabs_pos_lt.
generalize (Hmin ex).
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

End Fprop_relative_generic.

Section Fprop_relative_FLT.

Variable emin prec : Z.
Variable Hp : Zlt 0 prec.

Variable rnd : Zrounding.

Theorem bounded_relative_error_FLT_F2R :
  forall m, let x := F2R (Float beta m (emin + prec - 1)) in
  (x <> 0)%R ->
  (Rabs (rounding beta (FLT_exp emin prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof.
intros m x Hx.
apply generic_bounded_relative_error.
now apply FLT_exp_correct.
intros k Hk.
unfold FLT_exp.
generalize (Zmax_spec (k - prec) emin).
omega.
exact Hx.
Qed.

Theorem bounded_relative_error_FLT :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (rounding beta (FLT_exp emin prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof.
intros x Hx.
apply Rlt_le_trans with (ulp beta (FLT_exp emin prec) x)%R.
apply ulp_error.
now apply FLT_exp_correct.
unfold ulp, canonic_exponent.
assert (Hx': (x <> 0)%R).
intros Hx'.
apply Rlt_not_le with (2 := Hx).
rewrite Hx', Rabs_R0.
apply bpow_gt_0.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx').
apply Rle_trans with (bpow (-prec + 1) * bpow (ex - 1))%R.
rewrite <- bpow_add.
apply -> bpow_le.
unfold FLT_exp.
rewrite Zmax_left.
omega.
cut (emin + prec - 1 < ex)%Z. omega.
apply <- bpow_lt.
apply Rle_lt_trans with (1 := Hx).
apply He.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

Variable choice : R -> bool.

Theorem bounded_relative_error_N_FLT_F2R :
  forall m, let x := F2R (Float beta m (emin + prec - 1)) in
  (Rabs (rounding beta (FLT_exp emin prec) (ZrndN choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof.
intros m x.
apply generic_bounded_relative_error_N.
now apply FLT_exp_correct.
intros k Hk.
unfold FLT_exp.
generalize (Zmax_spec (k - prec) emin).
omega.
Qed.

Theorem bounded_relative_error_N_FLT :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (rounding beta (FLT_exp emin prec) (ZrndN choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof.
intros x Hx.
apply Rle_trans with (/2 * ulp beta (FLT_exp emin prec) x)%R.
apply ulp_half_error.
now apply FLT_exp_correct.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
unfold ulp, canonic_exponent.
assert (Hx': (x <> 0)%R).
intros Hx'.
apply Rlt_not_le with (2 := Hx).
rewrite Hx', Rabs_R0.
apply bpow_gt_0.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx').
apply Rle_trans with (bpow (-prec + 1) * bpow (ex - 1))%R.
rewrite <- bpow_add.
apply -> bpow_le.
unfold FLT_exp.
rewrite Zmax_left.
omega.
cut (emin + prec - 1 < ex)%Z. omega.
apply <- bpow_lt.
apply Rle_lt_trans with (1 := Hx).
apply He.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

End Fprop_relative_FLT.

Section Fprop_relative_FLX.

Variable prec : Z.
Variable Hp : Zlt 0 prec.

Variable rnd : Zrounding.

Theorem bounded_relative_error_FLX :
  forall x,
  (x <> 0)%R ->
  (Rabs (rounding beta (FLX_exp prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof.
intros x Hx.
apply Rlt_le_trans with (ulp beta (FLX_exp prec) x)%R.
apply ulp_error.
now apply FLX_exp_correct.
unfold ulp, canonic_exponent.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx).
apply Rle_trans with (bpow (-prec + 1) * bpow (ex - 1))%R.
rewrite <- bpow_add.
apply -> bpow_le.
unfold FLX_exp.
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

Variable choice : R -> bool.

Theorem bounded_relative_error_N_FLX :
  forall x,
  (Rabs (rounding beta (FLX_exp prec) (ZrndN choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof.
intros x.
destruct (Req_dec x 0) as [Hx|Hx].
(* . *)
rewrite Hx, rounding_0.
unfold Rminus.
rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0.
rewrite Rmult_0_r.
apply Rle_refl.
(* . *)
apply Rle_trans with (/2 * ulp beta (FLX_exp prec) x)%R.
apply ulp_half_error.
now apply FLX_exp_correct.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
unfold ulp, canonic_exponent.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx).
apply Rle_trans with (bpow (-prec + 1) * bpow (ex - 1))%R.
rewrite <- bpow_add.
apply -> bpow_le.
unfold FLX_exp.
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

End Fprop_relative_FLX.

End Fprop_relative.
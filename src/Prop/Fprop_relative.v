Require Import Fcore.

Section Fprop_relative.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Section Fprop_relative_generic.

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.

Variable rnd : Zrounding.

Theorem generic_relative_error :
  forall emin p,
  ( forall k, (emin < k)%Z -> (p <= k - fexp k)%Z ) ->
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (rounding beta fexp rnd x - x) < bpow (-p + 1) * Rabs x)%R.
Proof.
intros emin p Hmin x Hx.
apply Rlt_le_trans with (ulp beta fexp x)%R.
now apply ulp_error.
unfold ulp, canonic_exponent.
assert (Hx': (x <> 0)%R).
intros H.
apply Rlt_not_le with (2 := Hx).
rewrite H, Rabs_R0.
apply bpow_gt_0.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx').
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_add.
apply -> bpow_le.
assert (emin < ex)%Z.
apply <- bpow_lt.
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
generalize (Hmin ex).
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

Theorem generic_relative_error_F2R :
  forall emin p,
  ( forall k, (emin < k)%Z -> (p <= k - fexp k)%Z ) ->
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (rounding beta fexp rnd x - x) < bpow (-p + 1) * Rabs x)%R.
Proof.
intros emin p Hmin m x Hx.
apply generic_relative_error with (1 := Hmin).
unfold x.
rewrite abs_F2R.
apply bpow_le_F2R.
apply F2R_lt_reg with beta emin.
rewrite F2R_0, <- abs_F2R.
now apply Rabs_pos_lt.
Qed.

Theorem generic_relative_error_2 :
  forall emin p, (0 < p)%Z ->
  ( forall k, (emin < k)%Z -> (p <= k - fexp k)%Z ) ->
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (rounding beta fexp rnd x - x) < bpow (-p + 1) * Rabs (rounding beta fexp rnd x))%R.
Proof.
intros emin p Hp Hmin x Hx.
apply Rlt_le_trans with (ulp beta fexp x)%R.
now apply ulp_error.
assert (Hx': (x <> 0)%R).
intros H.
apply Rlt_not_le with (2 := Hx).
rewrite H, Rabs_R0.
apply bpow_gt_0.
unfold ulp, canonic_exponent.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx').
assert (He': (emin < ex)%Z).
apply <- bpow_lt.
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_add.
apply -> bpow_le.
generalize (Hmin ex).
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
generalize He.
apply rounding_abs_abs.
exact prop_exp.
clear rnd x Hx Hx' He.
intros rnd x Hx.
rewrite <- (rounding_generic beta fexp rnd (bpow (ex - 1))).
now apply rounding_monotone.
apply generic_format_bpow.
ring_simplify (ex - 1 + 1)%Z.
generalize (Hmin ex).
omega.
Qed.

Theorem generic_relative_error_F2R_2 :
  forall emin p, (0 < p)%Z ->
  ( forall k, (emin < k)%Z -> (p <= k - fexp k)%Z ) ->
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (rounding beta fexp rnd x - x) < bpow (-p + 1) * Rabs (rounding beta fexp rnd x))%R.
Proof.
intros emin p Hp Hmin m x Hx.
apply generic_relative_error_2 with (1 := Hp) (2 := Hmin).
unfold x.
rewrite abs_F2R.
apply bpow_le_F2R.
apply F2R_lt_reg with beta emin.
rewrite F2R_0, <- abs_F2R.
now apply Rabs_pos_lt.
Qed.

Variable choice : R -> bool.

Theorem generic_relative_error_N :
  forall emin p,
  ( forall k, (emin < k)%Z -> (p <= k - fexp k)%Z ) ->
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (rounding beta fexp (ZrndN choice) x - x) <= /2 * bpow (-p + 1) * Rabs x)%R.
Proof.
intros emin p Hmin x Hx.
apply Rle_trans with (/2 * ulp beta fexp x)%R.
now apply ulp_half_error.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
assert (Hx': (x <> 0)%R).
intros H.
apply Rlt_not_le with (2 := Hx).
rewrite H, Rabs_R0.
apply bpow_gt_0.
unfold ulp, canonic_exponent.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx').
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_add.
apply -> bpow_le.
assert (emin < ex)%Z.
apply <- bpow_lt.
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
generalize (Hmin ex).
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

Theorem generic_relative_error_N_F2R :
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
apply generic_relative_error_N with (1 := Hmin).
unfold x.
rewrite abs_F2R.
apply bpow_le_F2R.
apply F2R_lt_reg with beta emin.
rewrite F2R_0, <- abs_F2R.
now apply Rabs_pos_lt.
Qed.

Theorem generic_relative_error_N_2 :
  forall emin p, (0 < p)%Z ->
  ( forall k, (emin < k)%Z -> (p <= k - fexp k)%Z ) ->
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (rounding beta fexp (ZrndN choice) x - x) <= /2 * bpow (-p + 1) * Rabs (rounding beta fexp (ZrndN choice) x))%R.
Proof.
intros emin p Hp Hmin x Hx.
apply Rle_trans with (/2 * ulp beta fexp x)%R.
now apply ulp_half_error.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
assert (Hx': (x <> 0)%R).
intros H.
apply Rlt_not_le with (2 := Hx).
rewrite H, Rabs_R0.
apply bpow_gt_0.
unfold ulp, canonic_exponent.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx').
assert (He': (emin < ex)%Z).
apply <- bpow_lt.
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_add.
apply -> bpow_le.
generalize (Hmin ex).
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
generalize He.
apply rounding_abs_abs.
exact prop_exp.
clear rnd x Hx Hx' He.
intros rnd x Hx.
rewrite <- (rounding_generic beta fexp rnd (bpow (ex - 1))).
now apply rounding_monotone.
apply generic_format_bpow.
ring_simplify (ex - 1 + 1)%Z.
generalize (Hmin ex).
omega.
Qed.

Theorem generic_relative_error_N_F2R_2 :
  forall emin p, (0 < p)%Z ->
  ( forall k, (emin < k)%Z -> (p <= k - fexp k)%Z ) ->
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (rounding beta fexp (ZrndN choice) x - x) <= /2 * bpow (-p + 1) * Rabs (rounding beta fexp (ZrndN choice) x))%R.
Proof.
intros emin p Hp Hmin m x.
destruct (Req_dec x 0) as [Hx|Hx].
(* . *)
rewrite Hx, rounding_0.
unfold Rminus.
rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0.
rewrite Rmult_0_r.
apply Rle_refl.
(* . *)
apply generic_relative_error_N_2 with (1 := Hp) (2 := Hmin).
unfold x.
rewrite abs_F2R.
apply bpow_le_F2R.
apply F2R_lt_reg with beta emin.
rewrite F2R_0, <- abs_F2R.
now apply Rabs_pos_lt.
Qed.

End Fprop_relative_generic.

Section Fprop_relative_FLT.

Variable emin prec : Z.
Variable Hp : Zlt 0 prec.

Variable rnd : Zrounding.

Theorem relative_error_FLT_F2R :
  forall m, let x := F2R (Float beta m (emin + prec - 1)) in
  (x <> 0)%R ->
  (Rabs (rounding beta (FLT_exp emin prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof.
intros m x Hx.
apply generic_relative_error_F2R.
now apply FLT_exp_correct.
intros k Hk.
unfold FLT_exp.
generalize (Zmax_spec (k - prec) emin).
omega.
exact Hx.
Qed.

Theorem relative_error_FLT :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (rounding beta (FLT_exp emin prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof.
intros x Hx.
apply generic_relative_error with (emin + prec - 1)%Z.
now apply FLT_exp_correct.
intros k Hk.
unfold FLT_exp.
generalize (Zmax_spec (k - prec) emin).
omega.
exact Hx.
Qed.

Variable choice : R -> bool.

Theorem relative_error_N_FLT :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (rounding beta (FLT_exp emin prec) (ZrndN choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof.
intros x Hx.
apply generic_relative_error_N with (emin + prec - 1)%Z.
now apply FLT_exp_correct.
intros k Hk.
unfold FLT_exp.
generalize (Zmax_spec (k - prec) emin).
omega.
exact Hx.
Qed.

Theorem relative_error_N_FLT_2 :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (rounding beta (FLT_exp emin prec) (ZrndN choice) x - x) <= /2 * bpow (-prec + 1) * Rabs (rounding beta (FLT_exp emin prec) (ZrndN choice) x))%R.
Proof.
intros x Hx.
apply generic_relative_error_N_2 with (emin + prec - 1)%Z.
now apply FLT_exp_correct.
exact Hp.
intros k Hk.
unfold FLT_exp.
generalize (Zmax_spec (k - prec) emin).
omega.
exact Hx.
Qed.

Theorem relative_error_N_FLT_F2R :
  forall m, let x := F2R (Float beta m (emin + prec - 1)) in
  (Rabs (rounding beta (FLT_exp emin prec) (ZrndN choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof.
intros m x.
apply generic_relative_error_N_F2R.
now apply FLT_exp_correct.
intros k Hk.
unfold FLT_exp.
generalize (Zmax_spec (k - prec) emin).
omega.
Qed.

Theorem relative_error_N_FLT_F2R_2 :
  forall m, let x := F2R (Float beta m (emin + prec - 1)) in
  (Rabs (rounding beta (FLT_exp emin prec) (ZrndN choice) x - x) <= /2 * bpow (-prec + 1) * Rabs (rounding beta (FLT_exp emin prec) (ZrndN choice) x))%R.
Proof.
intros m x.
apply generic_relative_error_N_F2R_2.
now apply FLT_exp_correct.
exact Hp.
intros k Hk.
unfold FLT_exp.
generalize (Zmax_spec (k - prec) emin).
omega.
Qed.

End Fprop_relative_FLT.

Section Fprop_relative_FLX.

Variable prec : Z.
Variable Hp : Zlt 0 prec.

Variable rnd : Zrounding.

Theorem relative_error_FLX :
  forall x,
  (x <> 0)%R ->
  (Rabs (rounding beta (FLX_exp prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof.
intros x Hx.
destruct (ln_beta beta x) as (ex, He).
specialize (He Hx).
apply generic_relative_error with (ex - 1)%Z.
now apply FLX_exp_correct.
intros k _.
unfold FLX_exp.
omega.
apply He.
Qed.

Theorem relative_error_FLX_2 :
  forall x,
  (x <> 0)%R ->
  (Rabs (rounding beta (FLX_exp prec) rnd x - x) < bpow (-prec + 1) * Rabs (rounding beta (FLX_exp prec) rnd x))%R.
Proof.
intros x Hx.
destruct (ln_beta beta x) as (ex, He).
specialize (He Hx).
apply generic_relative_error_2 with (ex - 1)%Z.
now apply FLX_exp_correct.
exact Hp.
intros k _.
unfold FLX_exp.
omega.
apply He.
Qed.

Variable choice : R -> bool.

Theorem relative_error_N_FLX :
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
destruct (ln_beta beta x) as (ex, He).
specialize (He Hx).
apply generic_relative_error_N with (ex - 1)%Z.
now apply FLX_exp_correct.
intros k _.
unfold FLX_exp.
omega.
apply He.
Qed.

Theorem relative_error_N_FLX_2 :
  forall x,
  (Rabs (rounding beta (FLX_exp prec) (ZrndN choice) x - x) <= /2 * bpow (-prec + 1) * Rabs (rounding beta (FLX_exp prec) (ZrndN choice) x))%R.
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
destruct (ln_beta beta x) as (ex, He).
specialize (He Hx).
apply generic_relative_error_N_2 with (ex - 1)%Z.
now apply FLX_exp_correct.
exact Hp.
intros k _.
unfold FLX_exp.
omega.
apply He.
Qed.

End Fprop_relative_FLX.

End Fprop_relative.
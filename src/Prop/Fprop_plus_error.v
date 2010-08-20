Require Import Fcore.
Require Import Fcalc_ops.

Section Fprop_plus_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.

Theorem rounding_repr_same_exp :
  forall rnd m e,
  exists m',
  rounding beta fexp rnd (F2R (Float beta m e)) = F2R (Float beta m' e).
Proof.
intros rnd m e.
set (e' := canonic_exponent beta fexp (F2R (Float beta m e))).
unfold rounding, scaled_mantissa. fold e'.
destruct (Zle_or_lt e' e) as [He|He].
exists m.
unfold F2R at 2. simpl.
rewrite Rmult_assoc, <- bpow_add.
rewrite <- Z2R_Zpower. 2: omega.
rewrite <- mult_Z2R, Zrnd_Z2R.
unfold F2R. simpl.
rewrite mult_Z2R.
rewrite Rmult_assoc.
rewrite Z2R_Zpower. 2: omega.
rewrite <- bpow_add.
apply (f_equal (fun v => Z2R m * bpow v)%R).
ring.
exists ((Zrnd rnd (Z2R m * bpow (e - e')) e') * Zpower (radix_val beta) (e' - e))%Z.
unfold F2R. simpl.
rewrite mult_Z2R.
rewrite Z2R_Zpower. 2: omega.
rewrite 2!Rmult_assoc.
rewrite <- 2!bpow_add.
apply (f_equal (fun v => _ * bpow v)%R).
ring.
Qed.

Hypothesis monotone_exp : forall ex ey, (ex <= ey)%Z -> (fexp ex <= fexp ey)%Z.
Notation format := (generic_format beta fexp).

Variable choice : R -> bool.

Theorem plus_error_aux :
  forall x y,
  (canonic_exponent beta fexp x <= canonic_exponent beta fexp y)%Z ->
  format x -> format y ->
  format (rounding beta fexp (ZrndN choice) (x + y) - (x + y))%R.
Proof.
intros x y.
set (ex := canonic_exponent beta fexp x).
set (ey := canonic_exponent beta fexp y).
intros He Hx Hy.
destruct (Req_dec (rounding beta fexp (ZrndN choice) (x + y) - (x + y)) R0) as [H0|H0].
rewrite H0.
apply generic_format_0.
set (mx := Ztrunc (scaled_mantissa beta fexp x)).
set (my := Ztrunc (scaled_mantissa beta fexp y)).
(* *)
assert (Hxy: (x + y)%R = F2R (Float beta (mx + my * radix_val beta ^ (ey - ex)) ex)).
rewrite Hx, Hy.
fold mx my ex ey.
rewrite <- plus_F2R.
unfold Fplus. simpl.
now rewrite Zle_imp_le_bool with (1 := He).
(* *)
rewrite Hxy.
destruct (rounding_repr_same_exp (ZrndN choice) (mx + my * radix_val beta ^ (ey - ex)) ex) as (mxy, Hxy').
rewrite Hxy'.
assert (H: (F2R (Float beta mxy ex) -
   F2R (Float beta (mx + my * radix_val beta ^ (ey - ex)) ex))%R = F2R
     (Float beta
        (- (mx + my * radix_val beta ^ (ey - ex)) +
         mxy * radix_val beta ^ (ex - ex)) ex)).
unfold Rminus.
rewrite opp_F2R, Rplus_comm, <- plus_F2R.
unfold Fplus. simpl.
now rewrite Zle_bool_refl.
rewrite H.
apply generic_format_canonic_exponent.
apply monotone_exp.
rewrite <- H, <- Hxy', <- Hxy.
apply ln_beta_monotone_abs.
exact H0.
pattern x at 3 ; replace x with (-(y - (x + y)))%R by ring.
rewrite Rabs_Ropp.
now apply (generic_N_pt beta _ prop_exp choice (x + y)).
Qed.

Theorem plus_error :
  forall x y,
  format x -> format y ->
  format (rounding beta fexp (ZrndN choice) (x + y) - (x + y))%R.
Proof.
intros x y Hx Hy.
destruct (Zle_or_lt (canonic_exponent beta fexp x) (canonic_exponent beta fexp y)).
now apply plus_error_aux.
rewrite Rplus_comm.
apply plus_error_aux ; try easy.
now apply Zlt_le_weak.
Qed.

End Fprop_plus_error.

Section Fprop_plus_zero.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.
Notation format := (generic_format beta fexp).

Hypothesis not_FTZ : forall e, (fexp (fexp e + 1) <= fexp e)%Z.

Theorem rounding_plus_eq_zero_aux :
  forall rnd x y,
  (canonic_exponent beta fexp x <= canonic_exponent beta fexp y)%Z ->
  format x -> format y ->
  (0 <= x + y)%R ->
  rounding beta fexp rnd (x + y) = R0 ->
  (x + y = 0)%R.
Proof.
intros rnd x y He Hx Hy Hp Hxy.
destruct (Req_dec (x + y) 0) as [H0|H0].
exact H0.
destruct (ln_beta beta (x + y)) as (exy, Hexy).
simpl.
specialize (Hexy H0).
destruct (Zle_or_lt exy (fexp exy)) as [He'|He'].
(* . *)
assert (H: (x + y)%R = F2R (Float beta (Ztrunc (x * bpow (- fexp exy)) +
  Ztrunc (y * bpow (- fexp exy)) * Zpower (radix_val beta) (fexp exy - fexp exy)) (fexp exy))).
rewrite (subnormal_exponent beta fexp prop_exp not_FTZ exy x He' Hx) at 1.
rewrite (subnormal_exponent beta fexp prop_exp not_FTZ exy y He' Hy) at 1.
rewrite <- plus_F2R.
unfold Fplus. simpl.
now rewrite Zle_bool_refl.
rewrite H in Hxy.
rewrite rounding_generic in Hxy.
now rewrite <- H in Hxy.
apply generic_format_canonic_exponent.
rewrite <- H.
unfold canonic_exponent.
rewrite ln_beta_unique with (1 := Hexy).
apply Zle_refl.
(* . *)
elim Rle_not_lt with (1 := rounding_monotone beta _ prop_exp rnd _ _ (proj1 Hexy)).
rewrite (Rabs_pos_eq _ Hp).
rewrite Hxy.
rewrite rounding_generic.
apply bpow_gt_0.
apply generic_format_bpow.
ring_simplify (exy - 1 + 1)%Z.
omega.
Qed.

Theorem rounding_plus_eq_zero :
  forall rnd x y,
  format x -> format y ->
  rounding beta fexp rnd (x + y) = R0 ->
  (x + y = 0)%R.
Proof.
intros rnd x y Hx Hy.
destruct (Rle_or_lt R0 (x + y)) as [H1|H1].
(* . *)
revert H1.
destruct (Zle_or_lt (canonic_exponent beta fexp x) (canonic_exponent beta fexp y)) as [H2|H2].
now apply rounding_plus_eq_zero_aux.
rewrite Rplus_comm.
apply rounding_plus_eq_zero_aux ; try easy.
now apply Zlt_le_weak.
(* . *)
revert H1.
rewrite <- (Ropp_involutive (x + y)), Ropp_plus_distr, <- Ropp_0.
intros H1.
rewrite rounding_opp.
intros Hxy.
apply f_equal.
cut (rounding beta fexp (Zrounding_opp rnd) (- x + - y) = 0)%R.
cut (0 <= -x + -y)%R.
destruct (Zle_or_lt (canonic_exponent beta fexp (-x)) (canonic_exponent beta fexp (-y))) as [H2|H2].
apply rounding_plus_eq_zero_aux ; try apply generic_format_opp ; easy.
rewrite Rplus_comm.
apply rounding_plus_eq_zero_aux ; try apply generic_format_opp ; try easy.
now apply Zlt_le_weak.
apply Rlt_le.
now apply Ropp_lt_cancel.
rewrite <- (Ropp_involutive (rounding _ _ _ _)).
rewrite Hxy.
apply Ropp_involutive.
Qed.

End Fprop_plus_zero.

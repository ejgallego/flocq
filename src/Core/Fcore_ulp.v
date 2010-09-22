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

Theorem ulp_opp :
  forall x, ulp (- x) = ulp x.
Proof.
intros x.
unfold ulp.
now rewrite canonic_exponent_opp.
Qed.

Theorem ulp_abs :
  forall x, ulp (Rabs x) = ulp x.
Proof.
intros x.
unfold ulp.
now rewrite canonic_exponent_abs.
Qed.

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

Theorem succ_le_bpow :
  forall x e, (0 < x)%R -> F x ->
  (x < bpow e)%R ->
  (x + ulp x <= bpow e)%R.
Proof.
intros x e Zx Fx Hx.
pattern x at 1 ; rewrite Fx.
unfold ulp, F2R. simpl.
pattern (bpow (canonic_exponent beta fexp x)) at 2 ; rewrite <- Rmult_1_l.
rewrite <- Rmult_plus_distr_r.
change 1%R with (Z2R 1).
rewrite <- plus_Z2R.
change (F2R (Float beta (Ztrunc (scaled_mantissa beta fexp x) + 1) (canonic_exponent beta fexp x)) <= bpow e)%R.
apply F2R_p1_le_bpow.
apply F2R_gt_0_reg with beta (canonic_exponent beta fexp x).
now rewrite <- Fx.
now rewrite <- Fx.
Qed.

Theorem ln_beta_succ :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 <= eps < ulp x)%R ->
  projT1 (ln_beta beta (x + eps)) = projT1 (ln_beta beta x).
Proof.
intros x Zx Fx eps Heps.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He (Rgt_not_eq _ _ Zx)).
apply ln_beta_unique.
rewrite Rabs_pos_eq.
rewrite Rabs_pos_eq in He.
split.
apply Rle_trans with (1 := proj1 He).
pattern x at 1 ; rewrite <- Rplus_0_r.
now apply Rplus_le_compat_l.
apply Rlt_le_trans with (x + ulp x)%R.
now apply Rplus_lt_compat_l.
pattern x at 1 ; rewrite Fx.
unfold ulp, F2R. simpl.
pattern (bpow (canonic_exponent beta fexp x)) at 2 ; rewrite <- Rmult_1_l.
rewrite <- Rmult_plus_distr_r.
change 1%R with (Z2R 1).
rewrite <- plus_Z2R.
change (F2R (Float beta (Ztrunc (scaled_mantissa beta fexp x) + 1) (canonic_exponent beta fexp x)) <= bpow ex)%R.
apply F2R_p1_le_bpow.
apply F2R_gt_0_reg with beta (canonic_exponent beta fexp x).
now rewrite <- Fx.
now rewrite <- Fx.
now apply Rlt_le.
apply Rplus_le_le_0_compat.
now apply Rlt_le.
apply Heps.
Qed.

Theorem rounding_DN_succ :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 <= eps < ulp x)%R ->
  rounding beta fexp ZrndDN (x + eps) = x.
Proof.
intros x Zx Fx eps Heps.
pattern x at 2 ; rewrite Fx.
unfold rounding.
unfold scaled_mantissa, Zrnd. simpl.
unfold canonic_exponent at 1 2.
rewrite ln_beta_succ ; trivial.
apply (f_equal (fun m => F2R (Float beta m _))).
rewrite Ztrunc_floor.
apply Zfloor_imp.
split.
apply (Rle_trans _ _ _ (Zfloor_lb _)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
pattern x at 1 ; rewrite <- Rplus_0_r.
now apply Rplus_le_compat_l.
apply Rlt_le_trans with ((x + ulp x) * bpow (- canonic_exponent beta fexp x))%R.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
now apply Rplus_lt_compat_l.
rewrite Rmult_plus_distr_r.
rewrite plus_Z2R.
apply Rplus_le_compat.
pattern x at 1 3 ; rewrite Fx.
unfold F2R. simpl.
rewrite Rmult_assoc.
rewrite <- bpow_add.
rewrite Zplus_opp_r.
rewrite Rmult_1_r.
rewrite Zfloor_Z2R.
apply Rle_refl.
unfold ulp.
rewrite <- bpow_add.
rewrite Zplus_opp_r.
apply Rle_refl.
apply Rmult_le_pos.
now apply Rlt_le.
apply bpow_ge_0.
Qed.

Theorem generic_format_succ :
  forall x, (0 < x)%R -> F x ->
  F (x + ulp x).
Proof.
intros x Zx Fx.
destruct (ln_beta beta x) as (ex, Ex).
specialize (Ex (Rgt_not_eq _ _ Zx)).
assert (Ex' := Ex).
rewrite Rabs_pos_eq in Ex'.
destruct (succ_le_bpow x ex) ; try easy.
unfold F, generic_format.
unfold scaled_mantissa, canonic_exponent.
rewrite ln_beta_unique with beta (x + ulp x)%R ex.
pattern x at 1 3 ; rewrite Fx.
unfold ulp, scaled_mantissa.
rewrite canonic_exponent_fexp with (1 := Ex).
unfold F2R. simpl.
rewrite Rmult_plus_distr_r.
rewrite Rmult_assoc.
rewrite <- bpow_add, Zplus_opp_r, Rmult_1_r.
change (bpow 0) with (Z2R 1).
rewrite <- plus_Z2R.
rewrite Ztrunc_Z2R.
rewrite plus_Z2R.
rewrite Rmult_plus_distr_r.
now rewrite Rmult_1_l.
rewrite Rabs_pos_eq.
split.
apply Rle_trans with (1 := proj1 Ex').
pattern x at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
apply bpow_ge_0.
exact H.
apply Rplus_le_le_0_compat.
now apply Rlt_le.
apply bpow_ge_0.
rewrite H.
apply generic_format_bpow.
apply (prop_exp ex).
destruct (Zle_or_lt ex (fexp ex)) ; trivial.
elim Rlt_not_le with (1 := Zx).
rewrite Fx.
replace (Ztrunc (scaled_mantissa beta fexp x)) with Z0.
rewrite F2R_0.
apply Rle_refl.
unfold scaled_mantissa.
rewrite canonic_exponent_fexp with (1 := Ex).
destruct (mantissa_small_pos beta fexp x ex) ; trivial.
rewrite Ztrunc_floor.
apply sym_eq.
apply Zfloor_imp.
split.
now apply Rlt_le.
exact H2.
now apply Rlt_le.
now apply Rlt_le.
Qed.

Theorem rounding_UP_succ :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 < eps <= ulp x)%R ->
  rounding beta fexp ZrndUP (x + eps) = (x + ulp x)%R.
Proof.
intros x Zx Fx eps (Heps1,[Heps2|Heps2]).
assert (Heps: (0 <= eps < ulp x)%R).
split.
now apply Rlt_le.
exact Heps2.
assert (Hd := rounding_DN_succ x Zx Fx eps Heps).
rewrite ulp_DN_UP.
rewrite Hd.
unfold ulp, canonic_exponent.
now rewrite ln_beta_succ.
intros Fs.
rewrite rounding_generic in Hd.
apply Rgt_not_eq with (2 := Hd).
pattern x at 2 ; rewrite <- Rplus_0_r.
now apply Rplus_lt_compat_l.
exact Fs.
rewrite Heps2.
apply rounding_generic.
now apply generic_format_succ.
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

Theorem ulp_half_error :
  forall choice x,
  (Rabs (rounding beta fexp (ZrndN choice) x - x) <= /2 * ulp x)%R.
Proof.
intros choice x.
destruct (generic_format_EM beta fexp prop_exp x) as [Hx|Hx].
(* x = rnd x *)
rewrite rounding_generic.
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
destruct (generic_N_pt beta fexp prop_exp choice x) as (Hr1, Hr2).
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


Theorem ulp_error_f :
  (forall m n, (m <= n)%Z -> (fexp m <= fexp n)%Z ) ->
  forall Zrnd x,
  (rounding beta fexp Zrnd x <> 0)%R ->
  (Rabs (rounding beta fexp Zrnd x - x) < ulp (rounding beta fexp Zrnd x))%R.
Proof.
intros Hf Zrnd x Hfx.
case (rounding_DN_or_UP beta fexp Zrnd x); intros Hx.
(* *)
case (Rle_or_lt 0 (rounding beta fexp ZrndDN x)).
intros H; destruct H.
rewrite Hx at 2.
rewrite ulp_DN_pt_eq; trivial.
apply ulp_error.
rewrite Hx in Hfx; contradict Hfx; auto with real.
intros H.
apply Rlt_le_trans with (1:=ulp_error _ _).
rewrite <- (ulp_opp x), <- (ulp_opp (rounding beta fexp Zrnd x)).
apply ulp_monotone; trivial.
apply Ropp_0_gt_lt_contravar; apply Rlt_gt.
case (Rle_or_lt 0 x); trivial.
intros H1; contradict H.
apply Rle_not_lt.
apply rounding_monotone_l; trivial.
apply generic_format_0.
apply Ropp_le_contravar; rewrite Hx.
apply (generic_DN_pt beta fexp prop_exp x).
(* *)
rewrite Hx; case (Rle_or_lt 0 (rounding beta fexp ZrndUP x)).
intros H; destruct H.
apply Rlt_le_trans with (1:=ulp_error _ _).
apply ulp_monotone; trivial.
case (Rle_or_lt x 0); trivial.
intros H1; contradict H.
apply Rle_not_lt.
apply rounding_monotone_r; trivial.
apply generic_format_0.
apply (generic_UP_pt beta fexp prop_exp x).
rewrite Hx in Hfx; contradict Hfx; auto with real.
intros H.
rewrite <- (ulp_opp (rounding beta fexp ZrndUP x)).
rewrite <- rounding_DN_opp.
rewrite ulp_DN_pt_eq; trivial.
replace (rounding beta fexp ZrndUP x - x)%R with (-((rounding beta fexp ZrndDN (-x) - (-x))))%R.
rewrite Rabs_Ropp.
apply ulp_error.
rewrite rounding_DN_opp; ring.
rewrite rounding_DN_opp; apply Ropp_0_gt_lt_contravar; apply Rlt_gt; assumption.
Qed.

Theorem ulp_half_error_f : 
  (forall m n, (m <= n)%Z -> (fexp m <= fexp n)%Z ) ->
  forall choice x,
  (rounding beta fexp (ZrndN choice) x <> 0)%R ->
  (Rabs (rounding beta fexp (ZrndN choice) x - x) <= /2 * ulp (rounding beta fexp (ZrndN choice) x))%R.
Proof.
intros Hf choice x Hfx.
case (rounding_DN_or_UP beta fexp (ZrndN choice) x); intros Hx.
(* *)
case (Rle_or_lt 0 (rounding beta fexp ZrndDN x)).
intros H; destruct H.
rewrite Hx at 2.
rewrite ulp_DN_pt_eq; trivial.
apply ulp_half_error.
rewrite Hx in Hfx; contradict Hfx; auto with real.
intros H.
apply Rle_trans with (1:=ulp_half_error _ _).
apply Rmult_le_compat_l.
auto with real.
rewrite <- (ulp_opp x), <- (ulp_opp (rounding beta fexp (ZrndN choice) x)).
apply ulp_monotone; trivial.
apply Ropp_0_gt_lt_contravar; apply Rlt_gt.
case (Rle_or_lt 0 x); trivial.
intros H1; contradict H.
apply Rle_not_lt.
apply rounding_monotone_l; trivial.
apply generic_format_0.
apply Ropp_le_contravar; rewrite Hx.
apply (generic_DN_pt beta fexp prop_exp x).
(* *)
case (Rle_or_lt 0 (rounding beta fexp ZrndUP x)).
intros H; destruct H.
apply Rle_trans with (1:=ulp_half_error _ _).
apply Rmult_le_compat_l.
auto with real.
apply ulp_monotone; trivial.
case (Rle_or_lt x 0); trivial.
intros H1; contradict H.
apply Rle_not_lt.
apply rounding_monotone_r; trivial.
apply generic_format_0.
rewrite Hx; apply (generic_UP_pt beta fexp prop_exp x).
rewrite Hx in Hfx; contradict Hfx; auto with real.
intros H.
rewrite Hx at 2; rewrite <- (ulp_opp (rounding beta fexp ZrndUP x)).
rewrite <- rounding_DN_opp.
rewrite ulp_DN_pt_eq; trivial.
pattern x at 1 2; rewrite <- Ropp_involutive.
rewrite rounding_N_opp.
unfold Rminus.
rewrite <- Ropp_plus_distr, Rabs_Ropp.
apply ulp_half_error.
rewrite rounding_DN_opp; apply Ropp_0_gt_lt_contravar; apply Rlt_gt; assumption.
Qed.

End Fcore_ulp.

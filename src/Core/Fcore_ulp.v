(*
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2010 Sylvie Boldo
Copyright (C) 2010 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

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


Theorem ulp_le_pos:
  forall x, 
    (0 < x)%R ->
    F x -> 
    (ulp x <= x)%R.
Proof.
intros x Zx Fx.
rewrite <- (Rmult_1_l (ulp x)).
pattern x at 2; rewrite Fx.
unfold F2R, ulp; simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace 1%R with (Z2R (Zsucc 0)) by reflexivity.
apply Z2R_le.
apply Zlt_le_succ.
apply F2R_gt_0_reg with beta (canonic_exponent beta fexp x).
now rewrite <- Fx.
Qed.


Theorem ulp_le_abs:
  forall x, 
    (x <> 0)%R ->
    F x -> 
    (ulp x <= Rabs x)%R.
Proof.
intros x Zx Fx.
case (Rdichotomy _ _ Zx); intros Sx.
(* *)
rewrite <- (Rmult_1_l (ulp x)).
pattern x at 2; rewrite Fx.
rewrite abs_F2R.
unfold F2R, ulp; simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace 1%R with (Z2R (Zsucc 0)) by reflexivity.
apply Z2R_le.
apply Zlt_le_succ.
apply F2R_gt_0_reg with beta (canonic_exponent beta fexp x).
rewrite <- abs_F2R, <- Fx.
rewrite Rabs_left1; auto with real.
(* *)
rewrite Rabs_right.
now apply ulp_le_pos .
now apply Rgt_ge.
Qed.



Theorem ulp_DN_UP :
  forall x, ~ F x ->
  round beta fexp rndUP x = (round beta fexp rndDN x + ulp x)%R.
Proof.
intros x Fx.
unfold round, Zrnd, ulp. simpl.
unfold F2R. simpl.
rewrite Zceil_floor_neq.
rewrite Z2R_plus. simpl.
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
rewrite <- Z2R_plus.
change (F2R (Float beta (Ztrunc (scaled_mantissa beta fexp x) + 1) (canonic_exponent beta fexp x)) <= bpow e)%R.
apply F2R_p1_le_bpow.
apply F2R_gt_0_reg with beta (canonic_exponent beta fexp x).
now rewrite <- Fx.
now rewrite <- Fx.
Qed.

Theorem ln_beta_succ :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 <= eps < ulp x)%R ->
  ln_beta beta (x + eps) = ln_beta beta x :> Z.
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
rewrite <- Z2R_plus.
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

Theorem round_DN_succ :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 <= eps < ulp x)%R ->
  round beta fexp rndDN (x + eps) = x.
Proof.
intros x Zx Fx eps Heps.
pattern x at 2 ; rewrite Fx.
unfold round.
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
rewrite Z2R_plus.
apply Rplus_le_compat.
pattern x at 1 3 ; rewrite Fx.
unfold F2R. simpl.
rewrite Rmult_assoc.
rewrite <- bpow_plus.
rewrite Zplus_opp_r.
rewrite Rmult_1_r.
rewrite Zfloor_Z2R.
apply Rle_refl.
unfold ulp.
rewrite <- bpow_plus.
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
rewrite <- bpow_plus, Zplus_opp_r, Rmult_1_r.
change (bpow 0) with (Z2R 1).
rewrite <- Z2R_plus.
rewrite Ztrunc_Z2R.
rewrite Z2R_plus.
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

Theorem round_UP_succ :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 < eps <= ulp x)%R ->
  round beta fexp rndUP (x + eps) = (x + ulp x)%R.
Proof.
intros x Zx Fx eps (Heps1,[Heps2|Heps2]).
assert (Heps: (0 <= eps < ulp x)%R).
split.
now apply Rlt_le.
exact Heps2.
assert (Hd := round_DN_succ x Zx Fx eps Heps).
rewrite ulp_DN_UP.
rewrite Hd.
unfold ulp, canonic_exponent.
now rewrite ln_beta_succ.
intros Fs.
rewrite round_generic in Hd.
apply Rgt_not_eq with (2 := Hd).
pattern x at 2 ; rewrite <- Rplus_0_r.
now apply Rplus_lt_compat_l.
exact Fs.
rewrite Heps2.
apply round_generic.
now apply generic_format_succ.
Qed.

Theorem succ_lt_le:
  forall x y,
  F x -> F y ->
  (0 < x < y)%R ->
  (x + ulp x <= y)%R.
Proof.
intros x y Hx Hy H.
case (Rle_or_lt (ulp x) (y-x)); intros H1.
apply Rplus_le_reg_r with (-x)%R.
now ring_simplify (x+ulp x + -x)%R.
replace y with (x+(y-x))%R by ring.
absurd (x < y)%R.
2: apply H.
apply Rle_not_lt; apply Req_le.
rewrite <- round_DN_succ with (eps:=(y-x)%R); try easy.
ring_simplify (x+(y-x))%R.
apply sym_eq; now apply round_generic.
split; trivial.
apply Rlt_le; now apply Rlt_Rminus.
Qed.


Theorem ulp_error :
  forall Zrnd x,
  (Rabs (round beta fexp Zrnd x - x) < ulp x)%R.
Proof.
intros Zrnd x.
destruct (generic_format_EM beta fexp prop_exp x) as [Hx|Hx].
(* x = rnd x *)
rewrite round_generic with (1 := Hx).
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply bpow_gt_0.
(* x <> rnd x *)
destruct (round_DN_or_UP beta fexp Zrnd x) as [H|H] ; rewrite H ; clear H.
(* . *)
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rplus_lt_reg_r with (round beta fexp rndDN x).
rewrite <- ulp_DN_UP with (1 := Hx).
ring_simplify.
assert (Hu: (x <= round beta fexp rndUP x)%R).
apply (generic_UP_pt beta fexp prop_exp x).
destruct Hu as [Hu|Hu].
exact Hu.
elim Hx.
rewrite Hu.
now apply generic_format_round.
apply Rle_minus.
apply (generic_DN_pt beta fexp prop_exp x).
(* . *)
rewrite Rabs_pos_eq.
rewrite ulp_DN_UP with (1 := Hx).
apply Rplus_lt_reg_r with (x - ulp x)%R.
ring_simplify.
assert (Hd: (round beta fexp rndDN x <= x)%R).
apply (generic_DN_pt beta fexp prop_exp x).
destruct Hd as [Hd|Hd].
exact Hd.
elim Hx.
rewrite <- Hd.
now apply generic_format_round.
apply Rle_0_minus.
apply (generic_UP_pt beta fexp prop_exp x).
Qed.

Theorem ulp_half_error :
  forall choice x,
  (Rabs (round beta fexp (rndN choice) x - x) <= /2 * ulp x)%R.
Proof.
intros choice x.
destruct (generic_format_EM beta fexp prop_exp x) as [Hx|Hx].
(* x = rnd x *)
rewrite round_generic.
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply Rmult_le_pos.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
apply bpow_ge_0.
exact Hx.
(* x <> rnd x *)
set (d := round beta fexp rndDN x).
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
assert (Hu: (d + ulp x)%R = round beta fexp rndUP x).
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
  (0 < round beta fexp rndDN x)%R ->
  ulp (round beta fexp rndDN x) = ulp x.
Proof.
intros x Hd.
unfold ulp.
now rewrite canonic_exponent_DN with (2 := Hd).
Qed.


Theorem ulp_error_f :
  (forall m n, (m <= n)%Z -> (fexp m <= fexp n)%Z ) ->
  forall Zrnd x,
  (round beta fexp Zrnd x <> 0)%R ->
  (Rabs (round beta fexp Zrnd x - x) < ulp (round beta fexp Zrnd x))%R.
Proof.
intros Hf Zrnd x Hfx.
case (round_DN_or_UP beta fexp Zrnd x); intros Hx.
(* *)
case (Rle_or_lt 0 (round beta fexp rndDN x)).
intros H; destruct H.
rewrite Hx at 2.
rewrite ulp_DN_pt_eq; trivial.
apply ulp_error.
rewrite Hx in Hfx; contradict Hfx; auto with real.
intros H.
apply Rlt_le_trans with (1:=ulp_error _ _).
rewrite <- (ulp_opp x), <- (ulp_opp (round beta fexp Zrnd x)).
apply ulp_monotone; trivial.
apply Ropp_0_gt_lt_contravar; apply Rlt_gt.
case (Rle_or_lt 0 x); trivial.
intros H1; contradict H.
apply Rle_not_lt.
apply round_monotone_l; trivial.
apply generic_format_0.
apply Ropp_le_contravar; rewrite Hx.
apply (generic_DN_pt beta fexp prop_exp x).
(* *)
rewrite Hx; case (Rle_or_lt 0 (round beta fexp rndUP x)).
intros H; destruct H.
apply Rlt_le_trans with (1:=ulp_error _ _).
apply ulp_monotone; trivial.
case (Rle_or_lt x 0); trivial.
intros H1; contradict H.
apply Rle_not_lt.
apply round_monotone_r; trivial.
apply generic_format_0.
apply (generic_UP_pt beta fexp prop_exp x).
rewrite Hx in Hfx; contradict Hfx; auto with real.
intros H.
rewrite <- (ulp_opp (round beta fexp rndUP x)).
rewrite <- round_DN_opp.
rewrite ulp_DN_pt_eq; trivial.
replace (round beta fexp rndUP x - x)%R with (-((round beta fexp rndDN (-x) - (-x))))%R.
rewrite Rabs_Ropp.
apply ulp_error.
rewrite round_DN_opp; ring.
rewrite round_DN_opp; apply Ropp_0_gt_lt_contravar; apply Rlt_gt; assumption.
Qed.

Theorem ulp_half_error_f : 
  (forall m n, (m <= n)%Z -> (fexp m <= fexp n)%Z ) ->
  forall choice x,
  (round beta fexp (rndN choice) x <> 0)%R ->
  (Rabs (round beta fexp (rndN choice) x - x) <= /2 * ulp (round beta fexp (rndN choice) x))%R.
Proof.
intros Hf choice x Hfx.
case (round_DN_or_UP beta fexp (rndN choice) x); intros Hx.
(* *)
case (Rle_or_lt 0 (round beta fexp rndDN x)).
intros H; destruct H.
rewrite Hx at 2.
rewrite ulp_DN_pt_eq; trivial.
apply ulp_half_error.
rewrite Hx in Hfx; contradict Hfx; auto with real.
intros H.
apply Rle_trans with (1:=ulp_half_error _ _).
apply Rmult_le_compat_l.
auto with real.
rewrite <- (ulp_opp x), <- (ulp_opp (round beta fexp (rndN choice) x)).
apply ulp_monotone; trivial.
apply Ropp_0_gt_lt_contravar; apply Rlt_gt.
case (Rle_or_lt 0 x); trivial.
intros H1; contradict H.
apply Rle_not_lt.
apply round_monotone_l; trivial.
apply generic_format_0.
apply Ropp_le_contravar; rewrite Hx.
apply (generic_DN_pt beta fexp prop_exp x).
(* *)
case (Rle_or_lt 0 (round beta fexp rndUP x)).
intros H; destruct H.
apply Rle_trans with (1:=ulp_half_error _ _).
apply Rmult_le_compat_l.
auto with real.
apply ulp_monotone; trivial.
case (Rle_or_lt x 0); trivial.
intros H1; contradict H.
apply Rle_not_lt.
apply round_monotone_r; trivial.
apply generic_format_0.
rewrite Hx; apply (generic_UP_pt beta fexp prop_exp x).
rewrite Hx in Hfx; contradict Hfx; auto with real.
intros H.
rewrite Hx at 2; rewrite <- (ulp_opp (round beta fexp rndUP x)).
rewrite <- round_DN_opp.
rewrite ulp_DN_pt_eq; trivial.
pattern x at 1 2; rewrite <- Ropp_involutive.
rewrite round_N_opp.
unfold Rminus.
rewrite <- Ropp_plus_distr, Rabs_Ropp.
apply ulp_half_error.
rewrite round_DN_opp; apply Ropp_0_gt_lt_contravar; apply Rlt_gt; assumption.
Qed.

Definition pred x :=
  if Req_bool x (bpow (ln_beta beta x - 1)) then
    (x - bpow (fexp (ln_beta beta x - 1)))%R
  else
    (x - ulp x)%R.

Theorem pred_ge_bpow :
  forall x e,  F x ->
  x <> ulp x ->
  (bpow e < x)%R ->
  (bpow e <= x - ulp x)%R.
Proof.
intros x e Fx Hx' Hx.
(* *)
assert (1 <= Ztrunc (scaled_mantissa beta fexp x))%Z.
assert (0 <  Ztrunc (scaled_mantissa beta fexp x))%Z.
apply F2R_gt_0_reg with beta (canonic_exponent beta fexp x).
rewrite <- Fx.
apply Rle_lt_trans with (2:=Hx).
apply bpow_ge_0.
omega.
case (Zle_lt_or_eq _ _ H); intros Hm.
(* *)
pattern x at 1 ; rewrite Fx.
unfold ulp, F2R. simpl.
pattern (bpow (canonic_exponent beta fexp x)) at 2 ; rewrite <- Rmult_1_l.
rewrite <- Rmult_minus_distr_r.
change 1%R with (Z2R 1).
rewrite <- Z2R_minus.
change (bpow e <= F2R (Float beta (Ztrunc (scaled_mantissa beta fexp x) - 1) (canonic_exponent beta fexp x)))%R.
apply bpow_le_F2R_m1; trivial.
now rewrite <- Fx.
(* *)
contradict Hx'.
pattern x at 1; rewrite Fx.
rewrite  <- Hm.
unfold ulp, F2R; simpl.
now rewrite Rmult_1_l.
Qed.


Theorem format_pred_1:
  forall x, (0 < x)%R -> F x -> 
  x <> bpow (ln_beta beta x - 1) ->
  F (x - ulp x).
Proof.
intros x Zx Fx Hx.
destruct (ln_beta beta x) as (ex, Ex).
simpl in Hx.
specialize (Ex (Rgt_not_eq _ _ Zx)).
assert (Ex' : (bpow (ex - 1) < x < bpow ex)%R).
rewrite Rabs_pos_eq in Ex.
destruct Ex as (H,H'); destruct H; split; trivial.
contradict Hx; easy.
now apply Rlt_le.
unfold F, generic_format.
unfold scaled_mantissa, canonic_exponent.
rewrite ln_beta_unique with beta (x - ulp x)%R ex.
pattern x at 1 3 ; rewrite Fx.
unfold ulp, scaled_mantissa.
rewrite canonic_exponent_fexp with (1 := Ex).
unfold F2R. simpl.
rewrite Rmult_minus_distr_r.
rewrite Rmult_assoc.
rewrite <- bpow_plus, Zplus_opp_r, Rmult_1_r.
change (bpow 0) with (Z2R 1).
rewrite <- Z2R_minus.
rewrite Ztrunc_Z2R.
rewrite Z2R_minus.
rewrite Rmult_minus_distr_r.
now rewrite Rmult_1_l.
rewrite Rabs_pos_eq.
split.
apply pred_ge_bpow; trivial.
unfold ulp; intro H.
assert (ex-1 < canonic_exponent beta fexp x  < ex)%Z.
split; apply <- (bpow_lt beta); rewrite <- H; easy.
clear -H0. omega.
apply Ex'.
apply Rle_lt_trans with (2 := proj2 Ex').
pattern x at 3 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
rewrite <-Ropp_0.
apply Ropp_le_contravar.
apply bpow_ge_0.
apply Rle_0_minus.
pattern x at 2; rewrite Fx.
unfold ulp, F2R; simpl.
pattern (bpow (canonic_exponent beta fexp x)) at 1; rewrite <- Rmult_1_l.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace 1%R with (Z2R 1) by reflexivity.
apply Z2R_le.
assert (0 <  Ztrunc (scaled_mantissa beta fexp x))%Z.
apply F2R_gt_0_reg with beta (canonic_exponent beta fexp x).
rewrite <- Fx.
apply Rle_lt_trans with (2:=proj1 Ex').
apply bpow_ge_0.
omega.
Qed.

Theorem format_pred_2 :
  forall x, (0 < x)%R -> F x -> 
  let e := ln_beta_val beta x (ln_beta beta x) in
  x =  bpow (e - 1) ->
  F (x - bpow (fexp (e - 1))).
Proof.
intros x Zx Fx e Hx.
pose (f:=(x - bpow (fexp (e - 1)))%R).
fold f.
assert (He:(fexp (e-1) <= e-1)%Z). 
apply generic_format_bpow_inv with beta; trivial.
rewrite <- Hx; assumption.
case (Zle_lt_or_eq _ _ He); clear He; intros He.
assert (f = F2R (Float beta (Zpower beta (e-1-(fexp (e-1))) -1) (fexp (e-1))))%R.
unfold f; rewrite Hx.
unfold F2R; simpl.
rewrite Z2R_minus, Z2R_Zpower.
rewrite Rmult_minus_distr_r, Rmult_1_l.
rewrite <- bpow_plus.
now replace (e - 1 - fexp (e - 1) + fexp (e - 1))%Z with (e-1)%Z by ring.
omega.
rewrite H.
apply generic_format_canonic_exponent.
apply Zeq_le.
apply canonic_exponent_fexp.
rewrite <- H.
unfold f; rewrite Hx.
rewrite Rabs_right.
split.
apply Rplus_le_reg_l with (bpow (fexp (e-1))).
ring_simplify.
apply Rle_trans with (bpow (e - 2) + bpow (e - 2))%R.
apply Rplus_le_compat; apply -> bpow_le; omega.
apply Rle_trans with (2*bpow (e - 2))%R;[right; ring|idtac].
apply Rle_trans with (bpow 1*bpow (e - 2))%R.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace 2%R with (Z2R 2) by reflexivity.
replace (bpow 1) with (Z2R beta).
apply Z2R_le.
apply <- Zle_is_le_bool.
now destruct beta.
simpl.
unfold Zpower_pos; simpl.
now rewrite Zmult_1_r.
rewrite <- bpow_plus.
replace (1+(e-2))%Z with (e-1)%Z by ring.
now right.
rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply bpow_gt_0.
apply Rle_ge; apply Rle_0_minus.
apply -> bpow_le.
omega.
replace f with 0%R.
apply generic_format_0.
unfold f.
rewrite Hx, He.
ring.
Qed.

Theorem format_pred :
  forall x, (0 < x)%R -> F x -> 
  F (pred x).
Proof.
intros x Zx Fx.
unfold pred.
case Req_bool_spec; intros H.
now apply format_pred_2.
now apply format_pred_1.
Qed.

Theorem pred_ulp_1 :
  forall x, (0 < x)%R -> F x -> 
  x <> bpow (ln_beta beta x - 1) ->
  ((x - ulp x) + ulp (x-ulp x) = x)%R.
Proof.
intros x Zx Fx Hx.
replace (ulp (x - ulp x)) with (ulp x).
ring.
unfold ulp at 1 2; apply f_equal.
unfold canonic_exponent; apply f_equal.
destruct (ln_beta beta x) as (ex, Hex).
simpl in *.
assert (x <> 0)%R by auto with real.
specialize (Hex H).
apply sym_eq.
apply ln_beta_unique.
rewrite Rabs_right.
rewrite Rabs_right in Hex.
2: apply Rle_ge; apply Rlt_le; easy.
split.
destruct Hex as ([H1|H1],H2).
apply pred_ge_bpow; trivial.
unfold ulp; intros H3.
assert (ex-1 < canonic_exponent beta fexp x  < ex)%Z.
split; apply <- (bpow_lt beta); rewrite <- H3; easy.
omega.
contradict Hx; auto with real.
apply Rle_lt_trans with (2:=proj2 Hex).
rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
apply bpow_ge_0.
apply Rle_ge.
apply Rle_0_minus.
pattern x at 2; rewrite Fx.
unfold ulp, F2R; simpl.
pattern (bpow (canonic_exponent beta fexp x)) at 1; rewrite <- Rmult_1_l.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace 1%R with (Z2R (Zsucc 0)) by reflexivity.
apply Z2R_le.
apply Zlt_le_succ.
apply F2R_gt_0_reg with beta (canonic_exponent beta fexp x).
now rewrite <- Fx.
Qed.


Theorem pred_ulp_2:
  forall x, (0 < x)%R -> F x -> 
  let e := ln_beta_val beta x (ln_beta beta x) in
  x =  bpow (e - 1) ->
  (x - bpow (fexp (e-1)) <> 0)%R ->
  ((x - bpow (fexp (e-1))) + ulp (x - bpow (fexp (e-1))) = x)%R.
Proof.
intros x Zx Fx e Hxe Zp.
replace (ulp (x - bpow (fexp (e - 1)))) with (bpow (fexp (e - 1))).
ring.
assert (He:(fexp (e-1) <= e-1)%Z). 
apply generic_format_bpow_inv with beta; trivial.
rewrite <- Hxe; assumption.
case (Zle_lt_or_eq _ _ He); clear He; intros He.
(* *)
unfold ulp; apply f_equal.
unfold canonic_exponent; apply f_equal.
apply sym_eq.
apply ln_beta_unique.
rewrite Rabs_right.
split.
apply Rplus_le_reg_l with (bpow (fexp (e-1))).
ring_simplify.
apply Rle_trans with (bpow (e - 2) + bpow (e - 2))%R.
apply Rplus_le_compat; apply -> bpow_le; omega.
apply Rle_trans with (2*bpow (e - 2))%R;[right; ring|idtac].
apply Rle_trans with (bpow 1*bpow (e - 2))%R.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace 2%R with (Z2R 2) by reflexivity.
replace (bpow 1) with (Z2R beta).
apply Z2R_le.
apply <- Zle_is_le_bool.
now destruct beta.
simpl.
unfold Zpower_pos; simpl.
now rewrite Zmult_1_r.
rewrite <- bpow_plus.
replace (1+(e-2))%Z with (e-1)%Z by ring.
now right.
rewrite <- Rplus_0_r, Hxe.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply bpow_gt_0.
apply Rle_ge; apply Rle_0_minus.
rewrite Hxe.
apply -> bpow_le.
omega.
(* *)
contradict Zp.
rewrite Hxe, He; ring.
Qed.

Theorem pred_ulp :
  forall x, (0 < x)%R -> F x ->
  (pred x <> 0)%R ->
  (pred x + ulp (pred x) = x)%R.
Proof.
intros x Zx Fx.
unfold pred.
case Req_bool_spec; intros H Zp.
now apply pred_ulp_2.
now apply pred_ulp_1.
Qed.

Theorem pred_lt :
  forall x, 
  (pred x < x)%R.
Proof.
intros.
unfold pred.
case Req_bool_spec; intros H.
(* *)
rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply bpow_gt_0.
(* *)
rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply bpow_gt_0.
Qed.

Theorem  pred_pos:
  forall x, 
  (0 < x)%R -> F x -> (0 <= pred x)%R.
intros x Zx Fx.
unfold pred.
case Req_bool_spec; intros H.
(* *)
apply Rle_0_minus.
rewrite H.
apply -> bpow_le.
destruct (ln_beta beta x) as (ex,Ex) ; simpl.
rewrite ln_beta_bpow.
ring_simplify (ex - 1 + 1 - 1)%Z.
apply generic_format_bpow_inv with beta; trivial.
simpl in H.
rewrite <- H; assumption.
apply Rle_0_minus.
now apply ulp_le_pos.
Qed.

Theorem round_UP_pred :
  forall x, (0 < pred x)%R -> F x ->
  forall eps, (0 < eps <= ulp (pred x) )%R ->
  round beta fexp rndUP (pred x + eps) = x.
Proof.
intros x Hx Fx eps Heps.
rewrite round_UP_succ; trivial.
apply pred_ulp; trivial.
apply Rlt_trans with (1:=Hx).
apply pred_lt.
now apply Rgt_not_eq.
apply format_pred; trivial.
apply Rlt_trans with (1:=Hx).
apply pred_lt.
Qed.


Theorem round_DN_pred :
  forall x, (0 < pred x)%R -> F x ->
  forall eps, (0 < eps <= ulp (pred x))%R ->
  round beta fexp rndDN (x - eps) = pred x.
Proof.
intros x Hpx Fx eps Heps.
assert (Hx:(0 < x)%R).
apply Rlt_trans with (1:=Hpx).
apply pred_lt.
replace (x-eps)%R with (pred x + (ulp (pred x)-eps))%R.
2: pattern x at 3; rewrite <- (pred_ulp x); trivial.
2: ring.
2: now apply Rgt_not_eq.
rewrite round_DN_succ; trivial.
now apply format_pred.
split.
apply Rle_0_minus.
now apply Heps.
rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
now apply Heps.
Qed.



Theorem le_pred_lt:
  forall x y,
  F x -> F y ->
  (0 < x < y)%R ->
  (x  <= pred y)%R.
Proof.
intros x y Hx Hy H. 
(* *)
assert (Zp: (0 < pred y)%R).
assert (Zp:(0 <= pred y)%R).
apply pred_pos; trivial.
apply Rlt_trans with (1:=proj1 H).
apply H.
destruct Zp; trivial.
generalize H0.
unfold pred.
destruct (ln_beta beta y); simpl.
case Req_bool_spec; intros Hy2.
(* . *)
(* intros
y = beta^e=beta^ fexp e -> small pos
donc x aussi (exposant <=)
donc x est soit 0 soit y 
donc absurde


unfold valid_exp in prop_exp.*)

admit.


intros Hy3.
contradict Hy2.

(*
rewrite <- round_DN_pred with y (Rmin y (ulp (pred y))).
apply round_monotone_l; trivial.
apply generic_format_0.*)


admit.

(* *)
case (Rle_or_lt (ulp (pred y)) (y-x)); intros H1.
(* *)
apply Rplus_le_reg_r with (-x + ulp (pred y))%R.
ring_simplify (x+(-x+ulp (pred y)))%R.
apply Rle_trans with (1:=H1).
rewrite <- (pred_ulp y) at 1; trivial.
apply Req_le; ring.
apply Rlt_trans with (1:=proj1 H); easy.
now apply Rgt_not_eq.
(* *)
replace x with (y-(y-x))%R by ring.
rewrite <- round_DN_pred with (eps:=(y-x)%R); try easy.
ring_simplify (y-(y-x))%R.
apply Req_le.
apply sym_eq; now apply round_generic.
split; trivial.
now apply Rlt_Rminus.
now apply Rlt_le.
Qed.








End Fcore_ulp.

(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2010 Sylvie Boldo
#<br />#
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

(** * Floating-point format with gradual underflow *)
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_float_prop.
Require Import Fcore_FLX.
Require Import Fcore_FIX.
Require Import Fcore_rnd_ne.

Section RND_FLT.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable emin prec : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.

(* floating-point format with gradual underflow *)
Definition FLT_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Zabs (Fnum f) < Zpower beta prec)%Z /\ (emin <= Fexp f)%Z.

Definition FLT_exp e := Zmax (e - prec) emin.

(** Properties of the FLT format *)
Global Instance FLT_exp_valid : Valid_exp FLT_exp.
Proof.
intros k.
unfold FLT_exp.
generalize (prec_gt_0 prec).
repeat split ;
  intros ; zify ; omega.
Qed.

Theorem FLT_format_generic :
  forall x : R, FLT_format x <-> generic_format beta FLT_exp x.
Proof.
split.
(* . *)
intros ((xm, xe), (Hx1, (Hx2, Hx3))).
destruct (Req_dec x 0) as [Hx4|Hx4].
rewrite Hx4.
apply generic_format_0.
destruct (ln_beta beta x) as (ex, Hx5).
specialize (Hx5 Hx4).
rewrite Hx1.
apply generic_format_canonic_exponent.
rewrite <- Hx1.
rewrite canonic_exponent_fexp with (1 := Hx5).
unfold FLT_exp.
apply Zmax_lub. 2: exact Hx3.
cut (ex -1 < prec + xe)%Z. omega.
apply (lt_bpow beta).
apply Rle_lt_trans with (1 := proj1 Hx5).
rewrite Hx1.
apply F2R_lt_bpow.
simpl.
now ring_simplify (prec + xe - xe)%Z.
(* . *)
unfold generic_format.
set (ex := canonic_exponent beta FLT_exp x).
set (mx := Ztrunc (scaled_mantissa beta FLT_exp x)).
intros Hx.
rewrite Hx.
eexists ; repeat split ; simpl.
apply lt_Z2R.
rewrite Z2R_Zpower. 2: now apply Zlt_le_weak.
apply Rmult_lt_reg_r with (bpow ex).
apply bpow_gt_0.
rewrite <- bpow_plus.
change (F2R (Float beta (Zabs mx) ex) < bpow (prec + ex))%R.
rewrite <- abs_F2R.
rewrite <- Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, Rabs_R0.
apply bpow_gt_0.
unfold canonic_exponent in ex.
destruct (ln_beta beta x) as (ex', He).
simpl in ex.
specialize (He Hx0).
apply Rlt_le_trans with (1 := proj2 He).
apply bpow_le.
cut (ex' - prec <= ex)%Z. omega.
unfold ex, FLT_exp.
apply Zle_max_l.
apply Zle_max_r.
Qed.

Theorem FLT_format_satisfies_any :
  satisfies_any FLT_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLT_exp)).
intros x.
apply iff_sym.
apply FLT_format_generic.
Qed.

Theorem FLT_canonic_FLX :
  forall x, x <> R0 ->
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  canonic_exponent beta FLT_exp x = canonic_exponent beta (FLX_exp prec) x.
Proof.
intros x Hx0 Hx.
unfold canonic_exponent.
apply Zmax_left.
destruct (ln_beta beta x) as (ex, He).
unfold FLX_exp. simpl.
specialize (He Hx0).
cut (emin + prec - 1 < ex)%Z. omega.
apply (lt_bpow beta).
apply Rle_lt_trans with (1 := Hx).
apply He.
Qed.

(** Links between FLT and FLX *)
Theorem FLT_generic_format_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  ( generic_format beta FLT_exp x <-> generic_format beta (FLX_exp prec) x ).
Proof.
intros x Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0.
split ; intros _ ;  apply generic_format_0.
unfold generic_format, scaled_mantissa.
now rewrite (FLT_canonic_FLX x Hx0 Hx).
Qed.


Theorem FLX_generic_format_FLT :
  forall x : R,
  generic_format beta FLT_exp x -> generic_format beta (FLX_exp prec) x.
Proof.
intros x Hx.
unfold generic_format in Hx; rewrite Hx.
apply generic_format_canonic_exponent.
rewrite <- Hx.
unfold canonic_exponent, FLX_exp, FLT_exp.
apply Zle_max_l.
Qed.


Theorem FLT_format_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  ( FLT_format x <-> FLX_format beta prec x ).
Proof.
intros x Hx1.
apply iff_trans with (1 := FLT_format_generic x).
apply iff_trans with (1 := FLT_generic_format_FLX x Hx1).
split.
now apply FLX_format_generic.
now apply generic_format_FLX.
Qed.

Theorem FLT_round_FLX : forall rnd x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  round beta FLT_exp rnd x = round beta (FLX_exp prec) rnd x.
intros rnd x Hx.
unfold round, scaled_mantissa.
rewrite ->FLT_canonic_FLX; trivial.
intros H; contradict Hx.
rewrite H, Rabs_R0; apply Rlt_not_le.
apply bpow_gt_0.
Qed.


(** Links between FLT and FIX (underflow) *)
Theorem FLT_canonic_FIX :
  forall x, x <> R0 ->
  (Rabs x < bpow (emin + prec))%R ->
  canonic_exponent beta FLT_exp x = canonic_exponent beta (FIX_exp emin) x.
Proof.
intros x Hx0 Hx.
unfold canonic_exponent.
apply Zmax_right.
unfold FIX_exp.
destruct (ln_beta beta x) as (ex, Hex).
simpl.
cut (ex - 1 < emin + prec)%Z. omega.
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := Hx).
now apply Hex.
Qed.

Theorem FLT_generic_format_FIX :
  forall x : R,
  (Rabs x <= bpow (emin + prec))%R ->
  ( generic_format beta FLT_exp x <-> generic_format beta (FIX_exp emin) x ).
Proof.
intros x Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0.
split ; intros _ ;  apply generic_format_0.
destruct Hx as [Hx|Hx].
unfold generic_format, scaled_mantissa.
now rewrite (FLT_canonic_FIX x Hx0 Hx).
(* extra case *)
rewrite <- (Rabs_pos_eq (bpow (emin + prec))) in Hx. 2: apply bpow_ge_0.
assert (H1: generic_format beta FLT_exp (bpow (emin + prec))).
rewrite <- F2R_bpow.
apply generic_format_canonic_exponent.
unfold generic_format, canonic_exponent, FLT_exp.
rewrite F2R_bpow, ln_beta_bpow.
assert (Hp := prec_gt_0 prec).
apply Zmax_lub ; omega.
assert (H2: generic_format beta (FIX_exp emin) (bpow (emin + prec))).
rewrite <- F2R_bpow.
apply generic_format_canonic_exponent.
unfold generic_format, canonic_exponent, FIX_exp.
generalize (prec_gt_0 prec).
clear ; omega.
destruct Rabs_eq_Rabs with (1 := Hx) as [H|H] ;
  rewrite H ; clear H ;
  split ; intros _ ;
  try apply generic_format_opp ; easy.
Qed.

Theorem FLT_format_FIX :
  forall x,
  (Rabs x <= bpow (emin + prec))%R ->
  ( FLT_format x <-> FIX_format beta emin x ).
Proof.
intros x Hx1.
apply iff_trans with (1 := FLT_format_generic x).
apply iff_trans with (1 := FLT_generic_format_FIX x Hx1).
apply iff_sym.
now apply FIX_format_generic.
Qed.

(** FLT is a nice format: it has a monotone exponent... *)
Global Instance FLT_exp_monotone : Monotone_exp FLT_exp.
Proof.
intros ex ey.
unfold FLT_exp.
zify ; omega.
Qed.

(** and it allows a rounding to nearest, ties to even. *)
Hypothesis NE_prop : Zeven beta = false \/ (1 < prec)%Z.

Global Instance exists_NE_FLT : Exists_NE beta FLT_exp.
Proof.
destruct NE_prop as [H|H].
now left.
right.
intros e.
unfold FLT_exp.
destruct (Zmax_spec (e - prec) emin) as [(H1,H2)|(H1,H2)] ;
  rewrite H2 ; clear H2.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (e - prec + 1 - prec) emin).
omega.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (emin + 1 - prec) emin).
omega.
Qed.

End RND_FLT.

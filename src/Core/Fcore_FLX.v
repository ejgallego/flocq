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

(** * Floating-point format without underflow *)
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_float_prop.
Require Import Fcore_FIX.
Require Import Fcore_rnd_ne.

Section RND_FLX.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable prec : Z.

Class Prec_gt_0 :=
  prec_gt_0 : (0 < prec)%Z.

Context { prec_gt_0_ : Prec_gt_0 }.

(* unbounded floating-point format *)
Definition FLX_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Zabs (Fnum f) < Zpower beta prec)%Z.

Definition FLX_exp (e : Z) := (e - prec)%Z.

(** Properties of the FLX format *)

Global Instance FLX_exp_valid : Valid_exp FLX_exp.
Proof.
intros k.
unfold FLX_exp.
generalize prec_gt_0.
repeat split ; intros ; omega.
Qed.

Theorem FIX_format_FLX :
  forall x e,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  FLX_format x ->
  FIX_format beta (e - prec) x.
Proof.
clear prec_gt_0_.
intros x e Hx ((xm, xe), (H1, H2)).
rewrite H1, (F2R_prec_normalize beta xm xe e prec).
now eexists.
exact H2.
now rewrite <- H1.
Qed.

Theorem FLX_format_FIX :
  forall x e,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  FIX_format beta (e - prec) x ->
  FLX_format x.
Proof.
intros x e (Hx1,[Hx2|Hx2]).
(* . *)
intros ((xm, xe), (H1, H2)).
rewrite H1.
eexists ; repeat split.
simpl.
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow (e - prec)).
apply bpow_gt_0.
rewrite Z2R_Zpower, <- bpow_plus.
ring_simplify (prec + (e - prec))%Z.
rewrite <- H2.
simpl.
change (F2R (Float beta (Zabs xm) xe) < bpow e)%R.
now rewrite <- abs_F2R, <- H1.
now apply Zlt_le_weak.
(* . *)
intros ((xm, xe), (H1, H2)).
assert (Ha: forall x, FLX_format (Rabs x) -> FLX_format x).
clear.
intros x Ha.
unfold Rabs in Ha.
destruct (Rcase_abs x) as [Hx|Hx].
destruct Ha as ((m,e),(Ha,Hb)).
exists (Float beta (-m) e).
split.
now rewrite <- opp_F2R, <- Ha, Ropp_involutive.
simpl.
now rewrite Zabs_Zopp.
exact Ha.
(* . . *)
apply Ha.
rewrite Hx2.
exists (Float beta 1 e).
split.
apply sym_eq.
apply Rmult_1_l.
now apply Zpower_gt_1.
Qed.

Theorem FLX_format_generic :
  forall x, generic_format beta FLX_exp x -> FLX_format x.
Proof.
intros x H.
rewrite H.
unfold FLX_format.
eexists ; repeat split.
simpl.
apply lt_Z2R.
rewrite Z2R_abs.
rewrite <- scaled_mantissa_generic with (1 := H).
rewrite <- scaled_mantissa_abs.
apply Rmult_lt_reg_r with (bpow (canonic_exponent beta FLX_exp (Rabs x))).
apply bpow_gt_0.
rewrite scaled_mantissa_bpow.
rewrite Z2R_Zpower, <- bpow_plus.
2: now apply Zlt_le_weak.
unfold canonic_exponent, FLX_exp.
ring_simplify (prec + (ln_beta beta (Rabs x) - prec))%Z.
rewrite ln_beta_abs.
destruct (Req_dec x 0) as [Hx|Hx].
rewrite Hx, Rabs_R0.
apply bpow_gt_0.
destruct (ln_beta beta x) as (ex, Ex).
now apply Ex.
Qed.

Theorem generic_format_FLX :
  forall x, FLX_format x -> generic_format beta FLX_exp x.
Proof.
clear prec_gt_0_.
intros x ((mx,ex),(H1,H2)).
simpl in H2.
rewrite H1.
destruct (Z_eq_dec mx 0) as [Zmx|Zmx].
rewrite Zmx, F2R_0.
apply generic_format_0.
destruct (Zle_or_lt 0 prec) as [Hprec|Hprec].
(* *)
apply generic_format_canonic_exponent.
unfold canonic_exponent, FLX_exp.
rewrite ln_beta_F2R with (1 := Zmx).
apply Zplus_le_reg_r with (prec - ex)%Z.
ring_simplify.
apply bpow_lt_bpow with beta.
destruct (ln_beta beta (Z2R mx)) as (emx,Emx). simpl.
specialize (Emx (Z2R_neq _ _ Zmx)).
apply Rle_lt_trans with (1 := proj1 Emx).
rewrite <- Z2R_abs.
rewrite <- Z2R_Zpower with (1 := Hprec).
now apply Z2R_lt.
(* *)
revert H2 Hprec.
case prec ; simpl ; try discriminate.
intros _ H _.
elim (Zlt_irrefl 0).
apply Zle_lt_trans with (2 := H).
apply Zabs_pos.
Qed.

Theorem FLX_format_satisfies_any :
  satisfies_any FLX_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLX_exp)).
intros x.
split.
apply FLX_format_generic.
apply generic_format_FLX.
Qed.

(** unbounded floating-point format with normal mantissas *)
Definition FLXN_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (x <> R0 ->
  Zpower beta (prec - 1) <= Zabs (Fnum f) < Zpower beta prec)%Z.

Theorem FLX_format_FLXN :
  forall x : R, FLX_format x <-> FLXN_format x.
Proof.
intros x.
split.
(* . *)
intros ((xm, xe), (H1, H2)).
destruct (Z_eq_dec xm 0) as [H3|H3].
exists (Float beta 0 0).
split.
rewrite H1, H3.
now rewrite 2!F2R_0.
intros H.
elim H.
rewrite H1, H3.
apply F2R_0.
destruct (ln_beta beta (Z2R xm)) as (d,H4).
specialize (H4 (Z2R_neq _ _ H3)).
assert (H5: (0 <= prec - d)%Z).
cut (d - 1 < prec)%Z. omega.
apply (lt_bpow beta).
apply Rle_lt_trans with (Rabs (Z2R xm)).
apply H4.
rewrite <- Z2R_Zpower, <- Z2R_abs.
now apply Z2R_lt.
now apply Zlt_le_weak.
exists (Float beta (xm * Zpower beta (prec - d)) (xe + d - prec)).
split.
unfold F2R. simpl.
rewrite Z2R_mult, Z2R_Zpower.
rewrite Rmult_assoc, <- bpow_plus.
rewrite H1.
now ring_simplify (prec - d + (xe + d - prec))%Z.
exact H5.
intros _. simpl.
split.
apply le_Z2R.
apply Rmult_le_reg_r with (bpow (d - prec)).
apply bpow_gt_0.
rewrite Z2R_abs, Z2R_mult, Rabs_mult, 2!Z2R_Zpower.
rewrite <- bpow_plus.
rewrite <- Z2R_abs.
rewrite Rabs_pos_eq.
rewrite Rmult_assoc, <- bpow_plus.
ring_simplify (prec - 1 + (d - prec))%Z.
ring_simplify (prec - d + (d - prec))%Z.
now rewrite Rmult_1_r, Z2R_abs.
apply bpow_ge_0.
exact H5.
generalize prec_gt_0.
clear ; omega.
apply lt_Z2R.
rewrite Z2R_abs, Z2R_mult, Rabs_mult.
rewrite 2!Z2R_Zpower.
rewrite <- Z2R_abs, Rabs_pos_eq.
apply Rmult_lt_reg_r with (bpow (d - prec)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- 2!bpow_plus.
ring_simplify (prec + (d - prec))%Z.
ring_simplify (prec - d + (d - prec))%Z.
now rewrite Rmult_1_r, Z2R_abs.
apply bpow_ge_0.
now apply Zlt_le_weak.
exact H5.
(* . *)
intros ((xm, xe), (H1, H2)).
destruct (Req_dec x 0) as [H3|H3].
rewrite H3.
apply FLX_format_generic.
apply generic_format_0.
specialize (H2 H3). clear H3.
rewrite H1.
eexists ; repeat split.
apply H2.
Qed.

Theorem FLXN_format_satisfies_any :
  satisfies_any FLXN_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLX_exp)).
split ; intros H.
apply -> FLX_format_FLXN.
now apply FLX_format_generic.
apply generic_format_FLX.
now apply <- FLX_format_FLXN.
Qed.

(** FLX is a nice format: it has a monotone exponent... *)
Global Instance FLX_exp_monotone : Monotone_exp FLX_exp.
Proof.
intros ex ey Hxy.
now apply Zplus_le_compat_r.
Qed.

(** and it allows a rounding to nearest, ties to even. *)
Hypothesis NE_prop : Zeven beta = false \/ (1 < prec)%Z.

Global Instance exists_NE_FLX : Exists_NE beta FLX_exp.
Proof.
destruct NE_prop as [H|H].
now left.
right.
unfold FLX_exp.
split ; omega.
Qed.

End RND_FLX.

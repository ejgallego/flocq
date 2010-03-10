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
Variable Hp : Zlt 0 prec.

(* floating-point format with gradual underflow *)
Definition FLT_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Zabs (Fnum f) < Zpower (radix_val beta) prec)%Z /\ (emin <= Fexp f)%Z.

Definition FLT_RoundingModeP (rnd : R -> R):=
  Rounding_for_Format FLT_format rnd.

Definition FLT_exp e := Zmax (e - prec) emin.

Theorem FLT_exp_correct : valid_exp FLT_exp.
Proof.
intros k.
unfold FLT_exp.
destruct (Zmax_spec (k - prec) emin) as [(H1,H2)|(H1,H2)] ;
  rewrite H2 ; clear H2.
split.
generalize (Zmax_spec (k + 1 - prec) emin).
omega.
intros H0.
apply False_ind.
omega.
split.
generalize (Zmax_spec (k + 1 - prec) emin).
omega.
split.
generalize (Zmax_spec (emin + 1 - prec) emin).
omega.
intros l H0.
generalize (Zmax_spec (l - prec) emin).
omega.
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
apply <- bpow_lt.
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
rewrite <- bpow_add.
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
apply -> bpow_le.
cut (ex' - prec <= ex)%Z. omega.
unfold ex, FLT_exp.
apply Zle_max_l.
apply Zle_max_r.
Qed.

Theorem FLT_format_satisfies_any :
  satisfies_any FLT_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLT_exp _)).
intros x.
apply iff_sym.
apply FLT_format_generic.
exact FLT_exp_correct.
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
apply <- (bpow_lt beta).
apply Rle_lt_trans with (1 := Hx).
apply He.
Qed.

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

Theorem FLT_format_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  ( FLT_format x <-> FLX_format beta prec x ).
Proof.
intros x Hx1.
apply iff_trans with (1 := FLT_format_generic x).
apply iff_trans with (1 := FLT_generic_format_FLX x Hx1).
apply iff_sym.
now apply FLX_format_generic.
Qed.

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
apply <- (bpow_lt beta).
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
apply Zmax_lub ; omega.
assert (H2: generic_format beta (FIX_exp emin) (bpow (emin + prec))).
rewrite <- F2R_bpow.
apply generic_format_canonic_exponent.
unfold generic_format, canonic_exponent, FIX_exp.
omega.
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

Theorem Rnd_NE_pt_FLT :
  Zodd (radix_val beta) \/ (1 < prec)%Z ->
  rounding_pred (Rnd_NE_pt beta FLT_exp).
Proof.
intros H.
apply Rnd_NE_pt_rounding.
apply FLT_exp_correct.
destruct H.
now left.
right.
intros e.
unfold FLT_exp.
destruct (Zmax_spec (e - prec) emin) as [(H1,H2)|(H1,H2)].
rewrite H2.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (e - prec + 1 - prec) emin).
omega.
rewrite H2.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (emin + 1 - prec) emin).
omega.
Qed.

End RND_FLT.

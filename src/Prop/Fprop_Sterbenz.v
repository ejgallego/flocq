Require Import Fcore.
Require Import Fcalc_ops.

Section Fprop_Sterbenz.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.
Hypothesis monotone_exp : forall ex ey, (ex <= ey)%Z -> (fexp ex <= fexp ey)%Z.
Notation format := (generic_format beta fexp).

Lemma canonic_exponent_monotone :
  forall x y,
  (0 < x)%R -> (x <= y)%R ->
  (canonic_exponent beta fexp x <= canonic_exponent beta fexp y)%Z.
Proof.
intros x y Hx Hxy.
unfold canonic_exponent.
apply monotone_exp.
now apply ln_beta_monotone.
Qed.

Theorem generic_format_plus :
  forall x y,
  format x -> format y ->
  (Rabs (x + y) < bpow (Zmin (projT1 (ln_beta beta x)) (projT1 (ln_beta beta y))))%R ->
  format (x + y)%R.
Proof.
intros x y Fx Fy Hxy.
destruct (Req_dec (x + y) 0) as [Zxy|Zxy].
rewrite Zxy.
apply generic_format_0.
destruct (Req_dec x R0) as [Zx|Zx].
now rewrite Zx, Rplus_0_l.
destruct (Req_dec y R0) as [Zy|Zy].
now rewrite Zy, Rplus_0_r.
revert Hxy.
destruct (ln_beta beta x) as (ex, Ex). simpl.
specialize (Ex Zx).
destruct (ln_beta beta y) as (ey, Ey). simpl.
specialize (Ey Zy).
intros Hxy.
set (fx := Float beta (Ztrunc (scaled_mantissa beta fexp x)) (fexp ex)).
assert (Hx: x = F2R fx).
rewrite Fx at 1.
unfold canonic_exponent.
now rewrite ln_beta_unique with (1 := Ex).
set (fy := Float beta (Ztrunc (scaled_mantissa beta fexp y)) (fexp ey)).
assert (Hy: y = F2R fy).
rewrite Fy at 1.
unfold canonic_exponent.
now rewrite ln_beta_unique with (1 := Ey).
rewrite Hx, Hy.
rewrite <- plus_F2R.
apply generic_format_canonic_exponent.
case_eq (Fplus beta fx fy).
intros mxy exy Pxy.
rewrite <- Pxy, plus_F2R, <- Hx, <- Hy.
unfold canonic_exponent.
replace exy with (fexp (Zmin ex ey)).
apply monotone_exp.
apply bpow_lt_bpow with beta.
apply Rle_lt_trans with (2 := Hxy).
destruct (ln_beta beta (x + y)) as (exy', Exy). simpl.
now apply Exy.
replace exy with (Fexp (Fplus beta fx fy)) by exact (f_equal Fexp Pxy).
unfold Fplus.
generalize (Falign_spec_exp beta fx fy).
case (Falign beta fx fy). simpl.
intros (p, q) z Hz.
rewrite Hz.
simpl. clear -monotone_exp.
apply sym_eq.
destruct (Zmin_spec ex ey) as [(H1,H2)|(H1,H2)] ; rewrite H2.
apply Zmin_left.
now apply monotone_exp.
apply Zmin_right.
apply monotone_exp.
apply Zlt_le_weak.
now apply Zgt_lt.
Qed.

Theorem generic_format_plus_weak :
  forall x y,
  format x -> format y ->
  (Rabs (x + y) <= Rmin (Rabs x) (Rabs y))%R ->
  format (x + y)%R.
Proof.
intros x y Fx Fy Hxy.
destruct (Req_dec x R0) as [Zx|Zx].
now rewrite Zx, Rplus_0_l.
destruct (Req_dec y R0) as [Zy|Zy].
now rewrite Zy, Rplus_0_r.
apply generic_format_plus ; try assumption.
apply Rle_lt_trans with (1 := Hxy).
unfold Rmin.
destruct (Rle_dec (Rabs x) (Rabs y)) as [Hxy'|Hxy'].
rewrite Zmin_left.
destruct (ln_beta beta x) as (ex, Hx).
now apply Hx.
now apply ln_beta_monotone_abs.
rewrite Zmin_right.
destruct (ln_beta beta y) as (ex, Hy).
now apply Hy.
apply ln_beta_monotone_abs.
exact Zy.
apply Rlt_le.
now apply Rnot_le_lt.
Qed.

Theorem sterbenz_aux :
  forall x y, format x -> format y ->
  (y <= x <= 2 * y)%R ->
  format (x - y)%R.
Proof.
intros x y Hx Hy (Hxy1, Hxy2).
assert (Hxy: (0 <= x - y)%R).
apply Rplus_le_reg_r with y.
now ring_simplify.
destruct Hxy as [Hxy|Hxy].
(* . *)
assert (Hy0: (0 <= y)%R).
apply Rplus_le_reg_r with y.
apply Rle_trans with x.
now rewrite Rplus_0_l.
now rewrite Rmult_plus_distr_r, Rmult_1_l in Hxy2.
destruct Hy0 as [Hy0|Hy0].
(* .. *)
assert (Hf: (x - y = F2R (Float beta
  (- Ztrunc (scaled_mantissa beta fexp y) + Ztrunc (scaled_mantissa beta fexp x) *
     Zpower (radix_val beta) (canonic_exponent beta fexp x - canonic_exponent beta fexp y)) (canonic_exponent beta fexp y)))%R).
rewrite Hx at 1.
rewrite Hy at 1.
unfold Rminus.
rewrite opp_F2R.
rewrite Rplus_comm.
rewrite <- plus_F2R.
unfold Fplus. simpl.
rewrite Zle_imp_le_bool.
easy.
now apply canonic_exponent_monotone.
(* ... *)
rewrite Hf.
apply generic_format_canonic_exponent.
rewrite <- Hf.
clear Hf.
apply canonic_exponent_monotone.
exact Hxy.
apply Rplus_le_reg_r with y.
apply Rle_trans with x.
ring_simplify.
apply Rle_refl.
now rewrite Rmult_plus_distr_r, Rmult_1_l in Hxy2.
(* .. *)
elim (Rlt_irrefl 0).
apply Rlt_le_trans with  x.
replace x with (x - y)%R.
exact Hxy.
rewrite <- Hy0.
unfold Rminus.
now rewrite Ropp_0, Rplus_0_r.
now rewrite <- (Rmult_0_r 2), Hy0.
(* . *)
rewrite <- Hxy.
apply generic_format_0.
Qed.

Theorem sterbenz :
  forall x y, format x -> format y ->
  (y / 2 <= x <= 2 * y)%R ->
  format (x - y)%R.
Proof.
intros x y Hx Hy (Hxy1, Hxy2).
destruct (Rle_or_lt x y) as [Hxy|Hxy].
rewrite <- Ropp_minus_distr.
apply generic_format_opp.
apply sterbenz_aux ; try easy.
split.
exact Hxy.
apply Rcompare_not_Lt_inv.
rewrite <- Rcompare_half_r.
now apply Rcompare_not_Lt.
apply sterbenz_aux ; try easy.
split.
now apply Rlt_le.
exact Hxy2.
Qed.

End Fprop_Sterbenz.
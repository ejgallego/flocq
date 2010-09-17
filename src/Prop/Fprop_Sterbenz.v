Require Import Fcore.
Require Import Fcalc_ops.

Section Fprop_Sterbenz.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.
Hypothesis monotone_exp : forall ex ey, (ex <= ey)%Z -> (fexp ex <= fexp ey)%Z.
Notation format := (generic_format beta fexp).

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
rewrite Fexp_Fplus.
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
unfold Rminus.
apply generic_format_plus_weak.
exact Hx.
now apply generic_format_opp.
rewrite Rabs_pos_eq.
rewrite Rabs_Ropp.
rewrite Rmin_comm.
assert (Hy0: (0 <= y)%R).
apply Rplus_le_reg_r with y.
apply Rle_trans with x.
now rewrite Rplus_0_l.
now rewrite Rmult_plus_distr_r, Rmult_1_l in Hxy2.
rewrite Rabs_pos_eq with (1 := Hy0).
rewrite Rabs_pos_eq.
unfold Rmin.
destruct (Rle_dec y x) as [Hyx|Hyx].
apply Rplus_le_reg_r with y.
now ring_simplify.
now elim Hyx.
now apply Rle_trans with y.
now apply Rle_0_minus.
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
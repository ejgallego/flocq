Require Import Fcore.
Require Import Fcalc_ops.

Section Fprop_mult_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable Hp : Zlt 0 prec.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (canonic_exponent beta (FLX_exp prec)).

Theorem mult_error_FLX :
  forall rnd,
  forall x y,
  format x -> format y ->
  format (rounding beta (FLX_exp prec) rnd (x * y) - (x * y))%R.
Proof.
intros rnd x y Hx Hy.
set (f := (rounding beta (FLX_exp prec) rnd (x * y))).
destruct (Req_dec (f - x * y) 0) as [Hr0|Hr0].
rewrite Hr0.
apply generic_format_0.
destruct (Req_dec (x * y) 0) as [Hxy0|Hxy0].
unfold f.
rewrite Hxy0.
rewrite rounding_0.
ring_simplify (0 - 0)%R.
apply generic_format_0.
destruct (ln_beta beta (x * y)) as (exy, Hexy).
specialize (Hexy Hxy0).
destruct (ln_beta beta (f - x * y)) as (er, Her).
specialize (Her Hr0).
destruct (ln_beta beta x) as (ex, Hex).
assert (Hx0: (x <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_l.
specialize (Hex Hx0).
destruct (ln_beta beta y) as (ey, Hey).
assert (Hy0: (y <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_r.
specialize (Hey Hy0).
(* *)
assert (Hc1: (cexp (x * y)%R - prec <= cexp x + cexp y)%Z).
unfold canonic_exponent, FLX_exp.
rewrite ln_beta_unique with (1 := Hex).
rewrite ln_beta_unique with (1 := Hey).
rewrite ln_beta_unique with (1 := Hexy).
cut (exy - 1 < ex + ey)%Z. omega.
apply <- (bpow_lt beta).
apply Rle_lt_trans with (1 := proj1 Hexy).
rewrite Rabs_mult.
rewrite bpow_add.
apply Rmult_le_0_lt_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Hex.
apply Hey.
(* *)
assert (Hc2: (cexp x + cexp y <= cexp (x * y)%R)%Z).
unfold canonic_exponent, FLX_exp.
rewrite ln_beta_unique with (1 := Hex).
rewrite ln_beta_unique with (1 := Hey).
rewrite ln_beta_unique with (1 := Hexy).
cut ((ex - 1) + (ey - 1) < exy)%Z. omega.
apply <- (bpow_lt beta).
apply Rle_lt_trans with (2 := proj2 Hexy).
rewrite Rabs_mult.
rewrite bpow_add.
apply Rmult_le_compat.
apply bpow_ge_0.
apply bpow_ge_0.
apply Hex.
apply Hey.
(* *)
assert (Hr: ((F2R (Float beta (- (Ztrunc (scaled_mantissa beta (FLX_exp prec) x) *
  Ztrunc (scaled_mantissa beta (FLX_exp prec) y)) + Zrnd rnd (scaled_mantissa beta (FLX_exp prec) (x * y)) *
  radix_val beta ^ (cexp (x * y)%R - (cexp x + cexp y))) (cexp x + cexp y))) = f - x * y)%R).
rewrite Hx at 6.
rewrite Hy at 6.
rewrite <- mult_F2R.
simpl.
unfold f, rounding, Rminus.
rewrite opp_F2R, Rplus_comm, <- plus_F2R.
unfold Fplus. simpl.
now rewrite Zle_imp_le_bool with (1 := Hc2).
(* *)
rewrite <- Hr.
apply generic_format_canonic_exponent.
rewrite Hr.
clear Hr.
apply Zle_trans with (cexp (x * y)%R - prec)%Z.
unfold canonic_exponent, FLX_exp.
apply Zplus_le_compat_r.
rewrite ln_beta_unique with (1 := Her).
rewrite ln_beta_unique with (1 := Hexy).
apply (bpow_lt_bpow beta).
apply Rle_lt_trans with (1 := proj1 Her).
apply Rlt_le_trans with (ulp beta (FLX_exp prec) (x * y)).
apply ulp_error.
now apply FLX_exp_correct.
unfold ulp.
apply -> bpow_le.
unfold canonic_exponent, FLX_exp.
rewrite ln_beta_unique with (1 := Hexy).
apply Zle_refl.
apply Hc1.
Qed.

End Fprop_mult_error.
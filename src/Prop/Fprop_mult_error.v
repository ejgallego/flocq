Require Import Fcore.
Require Import Fcalc_ops.

Section Fprop_mult_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable Hp : Zlt 0 prec.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (canonic_exponent beta (FLX_exp prec)).

Theorem mult_error_FLX_aux:
  forall rnd,
  forall x y,
  format x -> format y ->
  (rounding beta (FLX_exp prec) rnd (x * y) - (x * y) <> 0)%R ->
  exists f:float beta, 
      (F2R f = rounding beta (FLX_exp prec) rnd (x * y) - (x * y))%R
      /\  (canonic_exponent beta (FLX_exp prec) (F2R f) <= Fexp f)%Z
      /\ (Fexp f = cexp x + cexp y)%Z.
intros rnd x y Hx Hy Hz.
set (f := (rounding beta (FLX_exp prec) rnd (x * y))).
destruct (Req_dec (x * y) 0) as [Hxy0|Hxy0].
contradict Hz.
rewrite Hxy0.
rewrite rounding_0.
ring.
destruct (ln_beta beta (x * y)) as (exy, Hexy).
specialize (Hexy Hxy0).
destruct (ln_beta beta (f - x * y)) as (er, Her).
specialize (Her Hz).
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
exists (Float beta (- (Ztrunc (scaled_mantissa beta (FLX_exp prec) x) *
  Ztrunc (scaled_mantissa beta (FLX_exp prec) y)) + Zrnd rnd (scaled_mantissa beta (FLX_exp prec) (x * y)) *
  radix_val beta ^ (cexp (x * y)%R - (cexp x + cexp y))) (cexp x + cexp y)).
split;[assumption|split].
rewrite Hr.
simpl.
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
reflexivity.
Qed.


Theorem mult_error_FLX :
  forall rnd,
  forall x y,
  format x -> format y ->
  format (rounding beta (FLX_exp prec) rnd (x * y) - (x * y))%R.
Proof.
intros rnd x y Hx Hy.
destruct (Req_dec (rounding beta (FLX_exp prec) rnd (x * y) - x * y) 0) as [Hr0|Hr0].
rewrite Hr0.
apply generic_format_0.
destruct (mult_error_FLX_aux rnd x y Hx Hy Hr0) as ((m,e),(H1,(H2,H3))).
rewrite <- H1.
apply generic_format_canonic_exponent; simpl.
simpl in H2; assumption.
Qed.


End Fprop_mult_error.
Section Fprop_mult_error_FLT.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable emin prec : Z.
Variable Hp : Zlt 0 prec.
Variable Hpemin: (emin <= prec)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation cexp := (canonic_exponent beta (FLT_exp emin prec)).


Theorem mult_error_FLT :
  forall rnd,
  forall x y,
  format x -> format y ->
  (x*y = 0)%R \/ (bpow (emin + 2*prec - 1) <= Rabs (x * y))%R ->
  format (rounding beta (FLT_exp emin prec) rnd (x * y) - (x * y))%R.
Proof.
clear Hpemin.
intros rnd x y Hx Hy Hxy.
set (f := (rounding beta (FLT_exp emin prec) rnd (x * y))).
destruct (Req_dec (f - x * y) 0) as [Hr0|Hr0].
rewrite Hr0.
apply generic_format_0.
destruct Hxy as [Hxy|Hxy].
unfold f.
rewrite Hxy.
rewrite rounding_0.
ring_simplify (0 - 0)%R.
apply generic_format_0.
destruct (mult_error_FLX_aux beta prec Hp rnd x y) as ((m,e),(H1,(H2,H3))).
now apply FLX_generic_format_FLT with emin.
now apply FLX_generic_format_FLT with emin.
rewrite <- (FLT_rounding_FLX beta emin).
assumption.
apply Rle_trans with (2:=Hxy).
apply -> bpow_le.
omega.
rewrite <- (FLT_rounding_FLX beta emin) in H1.
2:apply Rle_trans with (2:=Hxy).
2:apply -> bpow_le; omega.
unfold f; rewrite <- H1.
apply generic_format_canonic_exponent.
simpl in H2, H3.
unfold canonic_exponent, FLT_exp.
case (Zmax_spec (projT1 (ln_beta beta (F2R (Float beta m e))) - prec) emin);
  intros (M1,M2); rewrite M2.
apply Zle_trans with (2:=H2).
unfold canonic_exponent, FLX_exp.
apply Zle_refl.
rewrite H3.
unfold canonic_exponent, FLX_exp.
assert (Hxy0:(x*y <> 0)%R).
contradict Hr0.
unfold f.
rewrite Hr0.
rewrite rounding_0.
ring.
assert (Hx0: (x <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_l.
assert (Hy0: (y <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_r.
destruct (ln_beta beta x); simpl.
specialize (a Hx0).
destruct (ln_beta beta y); simpl.
specialize (a0 Hy0).
assert (emin+2*prec -1 < x0+x1)%Z.
2: omega.
apply <- (bpow_lt beta).
apply Rle_lt_trans with (1:=Hxy).
rewrite Rabs_mult, bpow_add.
apply Rmult_le_0_lt_compat; try apply Rabs_pos.
apply a.
apply a0.
Qed.



End Fprop_mult_error_FLT.








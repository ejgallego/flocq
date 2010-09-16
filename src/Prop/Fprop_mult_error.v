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
  (x*y = 0)%R \/ (bpow (emin + 3*prec - 2) <= Rabs (x * y))%R ->
  format (rounding beta (FLT_exp emin prec) rnd (x * y) - (x * y))%R.
Proof.
intros rnd x y Hx Hy Hxy.
(* *)
destruct Hxy as [Hxy|Hxy].
rewrite Hxy.
rewrite rounding_0, Rminus_0_r.
apply generic_format_0.
assert (Hxy2:(x*y <> 0)%R).
intro H; contradict Hxy.
rewrite H, Rabs_R0.
apply Rlt_not_le.
apply bpow_gt_0.
case (Req_dec (rounding beta (FLT_exp emin prec) rnd (x * y) - x * y) 0); intros Hr.
rewrite Hr; apply generic_format_0.
(* *)
apply <-FLT_generic_format_FLX.
rewrite FLT_rounding_FLX.
apply mult_error_FLX; trivial.
now apply FLX_generic_format_FLT with emin.
now apply FLX_generic_format_FLT with emin.
apply Rle_trans with (2:=Hxy).
apply -> bpow_le.
omega.
(* *)
assert (exists m:Z, exists e:Z, 
 Rabs (rounding beta (FLT_exp emin prec) rnd (x * y) - x * y) = F2R (Float beta m e) /\
 e=Zmin (cexp (x*y)%R) (cexp x + cexp y)).
exists (Zabs (Fnum ((Fminus beta
        (Float beta
           (Zrnd rnd (scaled_mantissa beta (FLT_exp emin prec) (x * y))) (cexp (x * y)%R))
        (Fmult beta
           (Float beta (Ztrunc (scaled_mantissa beta (FLT_exp emin prec) x))
              (cexp x))
           (Float beta (Ztrunc (scaled_mantissa beta (FLT_exp emin prec) y))
              (cexp y))))))).
exists (Zmin (cexp (x * y)%R) (cexp x + cexp y)).
split; trivial.
rewrite <- abs_F2R.
apply f_equal.
rewrite Hx at 2; rewrite Hy at 2.
rewrite <- mult_F2R.
unfold rounding.
rewrite <- minus_F2R.
case_eq (Fminus beta
     (Float beta
        (Zrnd rnd (scaled_mantissa beta (FLT_exp emin prec) (x * y))) (cexp (x * y)%R))
     (Fmult beta
        (Float beta (Ztrunc (scaled_mantissa beta (FLT_exp emin prec) x))
           (cexp x))
        (Float beta (Ztrunc (scaled_mantissa beta (FLT_exp emin prec) y))
           (cexp y)))).
intros m e H.
replace e with (Zmin (cexp (x * y)%R) (cexp x + cexp y)).
reflexivity.
apply sym_eq.
apply trans_eq with (Fexp (Float beta m e)); [easy|rewrite <- H].
unfold Fminus, Fopp, Fplus,Fmult.
apply trans_eq with (snd (Falign beta
          (Float beta
             (Zrnd rnd (scaled_mantissa beta (FLT_exp emin prec) (x * y))) (cexp (x * y)%R))
          (Float beta
             (-
              (Ztrunc (scaled_mantissa beta (FLT_exp emin prec) x) *
               Ztrunc (scaled_mantissa beta (FLT_exp emin prec) y)))
             (cexp x + cexp y)))).
destruct (Falign beta
          (Float beta
             (Zrnd rnd (scaled_mantissa beta (FLT_exp emin prec) (x * y))) (cexp (x * y)%R))
          (Float beta
             (-
              (Ztrunc (scaled_mantissa beta (FLT_exp emin prec) x) *
               Ztrunc (scaled_mantissa beta (FLT_exp emin prec) y)))
             (cexp x + cexp y))).
destruct p; reflexivity.
rewrite Falign_spec_exp; reflexivity.
(* *)
destruct H as (m,(e,(H1,H2))).
rewrite H1, H2.
apply Rle_trans with (bpow e).
apply ->bpow_le.
rewrite H2.
unfold canonic_exponent, FLT_exp.
apply Zmin_glb.
destruct (ln_beta beta (x*y)); simpl.
cut (emin+3*prec-2 < x0)%Z;[intros He|idtac].
rewrite Zmax_left; omega.
apply <- (bpow_lt beta).
apply Rle_lt_trans with (1:=Hxy).
now apply a.
assert (x <> 0)%R.
intro Y; contradict Hxy2; rewrite Y; ring.
assert (y <> 0)%R.
intro Y; contradict Hxy2; rewrite Y; ring.
destruct (ln_beta beta x); simpl.
specialize (a H).
destruct (ln_beta beta y); simpl.
specialize (a0 H0).
case (Zmax_spec (x0-prec) emin); intros (Hx0a,Hx0b); rewrite Hx0b.
(* . *)
case (Zmax_spec (x1-prec) emin); intros (Hx1a,Hx1b); rewrite Hx1b.
assert (emin+3*prec-2 < x0+x1)%Z.
apply <- (bpow_lt beta).
apply Rle_lt_trans with (1:=Hxy).
rewrite Rabs_mult, bpow_add.
apply Rmult_le_0_lt_compat; try apply Rabs_pos.
apply a.
apply a0.
omega.
assert (2*prec-2 < x0)%Z.
2: omega.
apply <- (bpow_lt beta).
apply Rle_lt_trans with (Rabs x);[idtac|apply a].
apply Rmult_le_reg_l with (Rabs y).
apply Rabs_pos_lt; assumption.
rewrite <- Rabs_mult, (Rmult_comm y x).
apply Rle_trans with (2:=Hxy).
apply Rle_trans with (bpow x1*bpow (2 * prec - 2))%R.
apply Rmult_le_compat_r.
apply bpow_ge_0.
left; apply a0.
rewrite <- bpow_add.
apply ->bpow_le.
omega.
(* . *)
case (Zmax_spec (x1-prec) emin); intros (Hx1a,Hx1b); rewrite Hx1b.
assert (2*prec-2 < x1)%Z.
2: omega.
apply <- (bpow_lt beta).
apply Rle_lt_trans with (Rabs y);[idtac|apply a0].
apply Rmult_le_reg_l with (Rabs x).
apply Rabs_pos_lt; assumption.
rewrite <- Rabs_mult.
apply Rle_trans with (2:=Hxy).
apply Rle_trans with (bpow x0*bpow (2 * prec - 2))%R.
apply Rmult_le_compat_r.
apply bpow_ge_0.
left; apply a.
rewrite <- bpow_add.
apply ->bpow_le.
omega.
contradict Hxy.
apply Rlt_not_le.
rewrite Rabs_mult.
apply Rlt_le_trans with (bpow x0*bpow x1)%R.
apply Rmult_le_0_lt_compat; try apply Rabs_pos.
apply a.
apply a0.
rewrite <- bpow_add.
apply -> bpow_le.
omega.
rewrite H2; apply bpow_le_F2R.
apply F2R_gt_0_reg with beta e.
rewrite <- H1.
apply Rabs_pos_lt; trivial.
Qed.




End Fprop_mult_error_FLT.








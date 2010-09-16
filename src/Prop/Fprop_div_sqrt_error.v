Require Import Fcore.
Require Import Fcalc_ops.
Require Import Fprop_relative.

Section Fprop_divsqrt_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable Hp : Zlt 0 prec.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (canonic_exponent beta (FLX_exp prec)).

Variable choice : R -> bool.

Theorem format_add: forall x y (fx fy: float beta),
  (x = F2R fx)%R -> (y = F2R fy)%R -> (Rabs (x+y) < bpow (prec+Fexp fx))%R -> (Rabs (x+y) < bpow (prec+Fexp fy))%R
  -> format (x+y)%R.
intros x y fx fy Hx Hy H1 H2.
case (Req_dec (x+y) 0); intros H.
rewrite H; apply generic_format_0.
rewrite Hx, Hy, <- plus_F2R.
apply generic_format_canonic_exponent.
case_eq (Fplus beta fx fy).
intros mz ez Hz.
rewrite <- Hz.
apply Zle_trans with (Zmin (Fexp fx) (Fexp fy)).
unfold canonic_exponent, FLX_exp.
rewrite plus_F2R, <- Hx, <- Hy.
destruct (ln_beta beta (x+y)); simpl.
specialize (a H).
apply Zmin_case.
apply Zplus_le_reg_l with prec; ring_simplify.
apply (bpow_lt_bpow beta).
now apply Rle_lt_trans with (1:=proj1 a).
apply Zplus_le_reg_l with prec; ring_simplify.
apply (bpow_lt_bpow beta).
now apply Rle_lt_trans with (1:=proj1 a).
rewrite <- Falign_spec_exp.
generalize (f_equal Fexp Hz).
unfold Fplus.
destruct (Falign beta fx fy) as ((p,q),t).
apply Zeq_le.
Qed.

Theorem format_nx: forall x, format x -> exists fx:float beta, (x=F2R fx)%R /\ Fexp fx = cexp x.
intros x; unfold generic_format.
exists (Float beta (Ztrunc (scaled_mantissa beta (FLX_exp prec) x)) (cexp x)).
split; auto.
Qed.

Theorem div_error_FLX :
  forall Zrnd x y,
  format x -> format y ->
  format (x - rounding beta (FLX_exp prec) Zrnd (x/y) * y)%R.
Proof.
intros Zrnd x y Hx Hy.
destruct (Req_dec y 0) as [Zy|Zy].
now rewrite Zy, Rmult_0_r, Rminus_0_r.
case (Req_dec (rounding beta (FLX_exp prec) Zrnd (x/y)) 0); intros Hr.
rewrite Hr; ring_simplify (x-0*y)%R; assumption.
assert (Zx: x <> R0).
contradict Hr.
rewrite Hr.
unfold Rdiv.
now rewrite Rmult_0_l, rounding_0.
destruct (format_nx x Hx) as (fx,(Hx1,Hx2)).
destruct (format_nx y Hy) as (fy,(Hy1,Hy2)).
destruct (format_nx (rounding beta (FLX_exp prec) Zrnd (x / y))) as (fr,(Hr1,Hr2)).
apply generic_format_rounding.
now apply FLX_exp_correct.
unfold Rminus; apply format_add with fx (Fopp beta (Fmult beta fr fy)); trivial.
now rewrite Fopp_F2R,mult_F2R, <- Hr1, <- Hy1.
(* *)
destruct (relative_error_FLX_ex beta prec Hp Zrnd (x / y)%R) as (eps,(Heps1,Heps2)).
apply Rmult_integral_contrapositive_currified.
exact Zx.
now apply Rinv_neq_0_compat.
rewrite Heps2.
rewrite <- Rabs_Ropp.
replace (-(x + - (x / y * (1 + eps) * y)))%R with (x * eps)%R by now field.
rewrite Rabs_mult.
apply Rlt_le_trans with (Rabs x * 1)%R.
apply Rmult_lt_compat_l.
now apply Rabs_pos_lt.
apply Rlt_le_trans with (1 := Heps1).
change R1 with (bpow 0).
apply -> bpow_le.
clear -Hp. omega.
rewrite Rmult_1_r.
rewrite Hx2.
unfold canonic_exponent.
destruct (ln_beta beta x) as (ex, Hex).
simpl.
specialize (Hex Zx).
apply Rlt_le.
apply Rlt_le_trans with (1 := proj2 Hex).
apply -> bpow_le.
unfold FLX_exp.
ring_simplify.
apply Zle_refl.
(* *)
replace (Fexp (Fopp beta (Fmult beta fr fy))) with (Fexp fr + Fexp fy)%Z.
2: unfold Fopp, Fmult; destruct fr; destruct fy; now simpl.
replace (x + - (rounding beta (FLX_exp prec) Zrnd (x / y) * y))%R with
  (y * (-(rounding beta (FLX_exp prec) Zrnd (x / y) - x/y)))%R.
2: field; assumption.
rewrite Rabs_mult.
apply Rlt_le_trans with (Rabs y * bpow (Fexp fr))%R.
apply Rmult_lt_compat_l.
now apply Rabs_pos_lt.
rewrite Rabs_Ropp.
replace (bpow (Fexp fr)) with (ulp beta (FLX_exp prec) (F2R fr)).
rewrite <- Hr1.
apply ulp_error_f.
now apply FLX_exp_correct.
clear; intros; unfold FLX_exp; omega.
exact Hr.
unfold ulp; apply f_equal.
now rewrite Hr2, <- Hr1.
replace (prec+(Fexp fr+Fexp fy))%Z with ((prec+Fexp fy)+Fexp fr)%Z by ring.
rewrite bpow_add.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite Hy2; unfold canonic_exponent, FLX_exp.
ring_simplify (prec + (projT1 (ln_beta beta y) - prec))%Z.
destruct (ln_beta beta y); simpl.
left; now apply a.
Qed.

Variable Hp1 : Zlt 1 prec.

Theorem sqrt_error_N :
  forall x, format x ->
  format (x - Rsqr (rounding beta (FLX_exp prec) (ZrndN choice) (sqrt x)))%R.
Proof.
intros x Hx.
destruct (total_order_T x 0) as [[Hxz|Hxz]|Hxz].
unfold sqrt.
destruct (Rcase_abs x).
rewrite rounding_0.
unfold Rsqr.
now rewrite Rmult_0_l, Rminus_0_r.
elim (Rlt_irrefl 0).
now apply Rgt_ge_trans with x.
rewrite Hxz, sqrt_0, rounding_0.
unfold Rsqr.
rewrite Rmult_0_l, Rminus_0_r.
apply generic_format_0.
case (Req_dec (rounding beta (FLX_exp prec) (ZrndN choice) (sqrt x)) 0); intros Hr.
rewrite Hr; unfold Rsqr; ring_simplify (x-0*0)%R; assumption.
destruct (format_nx x Hx) as (fx,(Hx1,Hx2)).
destruct (format_nx (rounding beta (FLX_exp prec) (ZrndN choice) (sqrt x))) as (fr,(Hr1,Hr2)).
apply generic_format_rounding.
now apply FLX_exp_correct.
unfold Rminus; apply format_add with fx (Fopp beta (Fmult beta fr fr)); trivial.
unfold Rsqr; now rewrite Fopp_F2R,mult_F2R, <- Hr1.
(* *) 
apply Rle_lt_trans with x.
apply Rabs_Rminus_pos.
apply Rle_0_sqr.
destruct (relative_error_N_FLX_ex beta prec Hp choice (sqrt x)) as (eps,(Heps1,Heps2)).
rewrite Heps2.
rewrite Rsqr_mult, Rsqr_sqrt, Rmult_comm. 2: now apply Rlt_le.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Rle_trans with (5²/4²)%R.
rewrite <- Rsqr_div.
apply Rsqr_le_abs_1.
apply Rle_trans with (1 := Rabs_triang _ _).
rewrite Rabs_R1.
apply Rplus_le_reg_l with (-1)%R.
rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
apply Rle_trans with (1 := Heps1).
rewrite Rabs_pos_eq.
apply Rmult_le_reg_l with 2%R.
now apply (Z2R_lt 0 2).
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
apply Rle_trans with (bpow (-1)).
apply -> bpow_le.
omega.
replace (2 * (-1 + 5 / 4))%R with (/2)%R by field.
apply Rinv_le.
now apply (Z2R_lt 0 2).
apply (Z2R_le 2).
unfold Zpower_pos. simpl.
rewrite Zmult_1_r.
apply Zle_bool_imp_le.
apply beta.
apply Rgt_not_eq.
now apply (Z2R_lt 0 2).
unfold Rdiv.
apply Rmult_le_pos.
now apply (Z2R_le 0 5).
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 4).
apply Rgt_not_eq.
now apply (Z2R_lt 0 4).
unfold Rsqr.
replace (5 * 5 / (4 * 4))%R with (25 * /16)%R by field.
apply Rmult_le_reg_r with 16%R.
now apply (Z2R_lt 0 16).
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now apply (Z2R_le 25 32).
apply Rgt_not_eq.
now apply (Z2R_lt 0 16).
rewrite Hx2; unfold canonic_exponent, FLX_exp.
ring_simplify (prec + (projT1 (ln_beta beta x) - prec))%Z.
destruct (ln_beta beta x); simpl.
rewrite <- (Rabs_right x).
apply a.
now apply Rgt_not_eq.
now apply Rgt_ge.
(* *)
replace (Fexp (Fopp beta (Fmult beta fr fr))) with (Fexp fr + Fexp fr)%Z.
2: unfold Fopp, Fmult; destruct fr; now simpl.
rewrite Hr1.
replace (x + - Rsqr (F2R fr))%R with (-((F2R fr - sqrt x)*(F2R fr + sqrt x)))%R.
2: rewrite <- (sqrt_sqrt x) at 3; auto.
2: unfold Rsqr; ring.
rewrite Rabs_Ropp, Rabs_mult.
apply Rle_lt_trans with ((/2*bpow (Fexp fr))* Rabs (F2R fr + sqrt x))%R.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rle_trans with (/2*ulp beta  (FLX_exp prec) (F2R fr))%R.
rewrite <- Hr1.
apply ulp_half_error_f; trivial.
now apply FLX_exp_correct.
clear; intros; unfold FLX_exp; omega.
right; unfold ulp; apply f_equal.
rewrite Hr2, <- Hr1; trivial. 
rewrite Rmult_assoc, Rmult_comm.
replace (prec+(Fexp fr+Fexp fr))%Z with (Fexp fr + (prec+Fexp fr))%Z by ring.
rewrite bpow_add, Rmult_assoc.
apply Rmult_lt_compat_l.
apply bpow_gt_0.
apply Rmult_lt_reg_l with 2%R.
auto with real.
apply Rle_lt_trans with (Rabs (F2R fr + sqrt x)).
right; field.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
(* . *)
assert (Rabs (F2R fr) < bpow (prec + Fexp fr))%R.
rewrite Hr2; unfold canonic_exponent; rewrite Hr1.
unfold FLX_exp.
ring_simplify (prec + (projT1 (ln_beta beta (F2R fr)) - prec))%Z.
destruct (ln_beta beta (F2R fr)); simpl.
apply a.
rewrite <- Hr1; auto.
(* . *)
apply Rlt_le_trans with (bpow (prec + Fexp fr)+ Rabs (sqrt x))%R.
now apply Rplus_lt_compat_r.
(* . *)
rewrite Rmult_plus_distr_r, Rmult_1_l.
apply Rplus_le_compat_l.
assert (sqrt x <> 0)%R.
apply Rgt_not_eq.
now apply sqrt_lt_R0.
destruct (ln_beta beta (sqrt x)).
specialize (a H0).
apply Rle_trans with (bpow x0).
left; apply a.
apply ->bpow_le.
case (Zle_or_lt x0 (prec+Fexp fr)); trivial.
intros H1.
absurd (Rabs (F2R fr) < bpow (x0-1))%R.
apply Rle_not_lt.
rewrite <- Hr1.
apply rounding_monotone_abs_l.
now apply FLX_exp_correct.
apply generic_format_bpow.
unfold FLX_exp; omega.
apply a.
apply Rlt_le_trans with (1:=H).
apply ->bpow_le; omega.
now apply Rlt_le.
Qed.

End Fprop_divsqrt_error.

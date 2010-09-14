Require Import Fcore.
Require Import Fcalc_ops.

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
replace (Float beta (let (Fnum, _) := Fplus beta fx fy in Fnum)
         (let (_, Fexp) := Fplus beta fx fy in Fexp)) with (Fplus beta fx fy).
2: now destruct (Fplus beta fx fy).
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
unfold Fplus.
rewrite <- Falign_spec_exp.
destruct (Falign beta fx fy) as (p,t); destruct p; now apply Zeq_le.
Qed.
 

Theorem format_nx: forall x, format x -> exists fx:float beta, (x=F2R fx)%R /\ Fexp fx = cexp x.
intros x; unfold generic_format.
exists (Float beta (Ztrunc (scaled_mantissa beta (FLX_exp prec) x)) (cexp x)).
split; auto.
Qed.


Variable Hp1 : Zlt 1 prec.

Theorem div_error_FLX :
  forall Zrnd x y,
  format x -> format y ->
  (y <> 0)%R ->
  format (x - rounding beta (FLX_exp prec) Zrnd (x/y) * y)%R.
Proof.
intros Zrnd x y Hx Hy Zy.
case (Req_dec (rounding beta (FLX_exp prec) Zrnd (x/y)) 0); intros Hr.
rewrite Hr; ring_simplify (x-0*y)%R; assumption.
destruct (format_nx x Hx) as (fx,(Hx1,Hx2)).
destruct (format_nx y Hy) as (fy,(Hy1,Hy2)).
destruct (format_nx (rounding beta (FLX_exp prec) Zrnd (x / y))) as (fr,(Hr1,Hr2)).
apply generic_format_rounding.
now apply FLX_exp_correct.
unfold Rminus; apply format_add with fx (Fopp beta (Fmult beta fr fy)); trivial.
now rewrite Fopp_F2R,mult_F2R, <- Hr1, <- Hy1.
(* *)
apply Rle_lt_trans with (Rabs x).
replace (x + - (rounding beta (FLX_exp prec) Zrnd (x / y) * y))%R with
  (y * (-(rounding beta (FLX_exp prec) Zrnd (x / y) - x/y)))%R.
2: field; assumption.
rewrite Rabs_mult, Rabs_Ropp.
apply Rmult_le_reg_l with (/Rabs y)%R.
apply Rinv_0_lt_compat.
now apply Rabs_pos_lt.
rewrite <- Rmult_assoc, Rinv_l.
2: now apply Rabs_no_R0.
rewrite Rmult_1_l, Hr1.
rewrite <- Rabs_Rinv; trivial.
rewrite <- Rabs_mult.
replace (/y * x)%R with ((F2R fr -(F2R fr - x / y)))%R by (unfold Rdiv ; ring).
apply Rle_trans with (2:=Rabs_triang_inv _ _).
apply Rplus_le_reg_l with (Rabs (F2R fr - x / y)).
apply Rle_trans with (2*Rabs (F2R fr - x / y))%R;[right; ring|idtac].
ring_simplify (Rabs (F2R fr - x / y) + (Rabs (F2R fr) - Rabs (F2R fr - x / y)))%R.
apply Rle_trans with (2* (ulp beta (FLX_exp prec) (F2R fr)))%R.
apply Rmult_le_compat_l.
auto with real.
rewrite <- Hr1; left.
apply ulp_error_f; trivial.
now apply FLX_exp_correct.
clear; intros; unfold FLX_exp; omega.
unfold ulp.
apply Rle_trans with (bpow 1*bpow (cexp (F2R fr)))%R.
apply Rmult_le_compat_r.
apply bpow_ge_0.
simpl; unfold Zpower_pos; simpl; rewrite Zmult_1_r.
replace 2%R with (Z2R 2) by easy.
apply Z2R_le.
clear; destruct beta; simpl.
now apply Zle_bool_imp_le.
rewrite <- bpow_add.
unfold canonic_exponent, FLX_exp.
destruct (ln_beta beta (F2R fr)).
simpl (projT1 (exist (fun e : Z => F2R fr <> 0%R -> (bpow (e - 1) <= Rabs (F2R fr) < bpow e)%R) x0 a))%Z.
rewrite <- Hr1 in a.
specialize (a Hr); rewrite Hr1 in a.
apply Rle_trans with (2:=proj1 a).
apply ->bpow_le; omega.
case (Req_dec x 0); intros Hxz.
rewrite Hxz, Rabs_R0.
apply bpow_gt_0.
rewrite Hx2; unfold canonic_exponent, FLX_exp.
ring_simplify (prec + (projT1 (ln_beta beta x) - prec))%Z.
destruct (ln_beta beta x); simpl.
now apply a.
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
apply Rlt_le_trans with (ulp beta  (FLX_exp prec) (F2R fr)).
rewrite <- Hr1.
apply ulp_error_f; trivial.
now apply FLX_exp_correct.
clear; intros; unfold FLX_exp; omega.
right; unfold ulp; apply f_equal.
rewrite Hr2, <- Hr1; trivial. 
replace (prec+(Fexp fr+Fexp fy))%Z with ((prec+Fexp fy)+Fexp fr)%Z by ring.
rewrite bpow_add.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite Hy2; unfold canonic_exponent, FLX_exp.
ring_simplify (prec + (projT1 (ln_beta beta y) - prec))%Z.
destruct (ln_beta beta y); simpl.
left; now apply a.
Qed.



Theorem sqrt_error_N :
  forall x, (0 <= x)%R ->
  format x ->
  format (x - Rsqr (rounding beta (FLX_exp prec) (ZrndN choice) (sqrt x)))%R.
Proof.
intros x Px Hx.
case (Req_dec (rounding beta (FLX_exp prec) (ZrndN choice) (sqrt x)) 0); intros Hr.
rewrite Hr; unfold Rsqr; ring_simplify (x-0*0)%R; assumption.
case (Req_dec x 0); intros Hxz.
contradict Hr.
now rewrite Hxz, sqrt_0, rounding_0.
destruct (format_nx x Hx) as (fx,(Hx1,Hx2)).
destruct (format_nx (rounding beta (FLX_exp prec) (ZrndN choice) (sqrt x))) as (fr,(Hr1,Hr2)).
apply generic_format_rounding.
now apply FLX_exp_correct.
unfold Rminus; apply format_add with fx (Fopp beta (Fmult beta fr fr)); trivial.
unfold Rsqr; now rewrite Fopp_F2R,mult_F2R, <- Hr1.
(* *) 
apply Rle_lt_trans with x.
apply Rabs_Rminus_pos.
auto with real.
apply Rle_trans with (Rsqr (sqrt (2*x)))%R.
2: right; rewrite Rsqr_sqrt; auto.
2: apply Rmult_le_pos; auto with real.
apply Rsqr_le_abs_1.
rewrite Hr1.
replace (F2R fr) with ((F2R fr - sqrt x)+sqrt x)%R by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (/2*bpow (-prec+1)*Rabs (sqrt x) + Rabs (sqrt x))%R.
apply Rplus_le_compat_r; rewrite <- Hr1.
apply Rle_trans with (/2*ulp beta (FLX_exp prec) (sqrt x))%R.
apply ulp_half_error.
now apply FLX_exp_correct.
rewrite Rmult_assoc; apply Rmult_le_compat_l.
auto with real.
unfold ulp, canonic_exponent, FLX_exp.
destruct (ln_beta beta (sqrt x)); simpl.
apply Rle_trans with (bpow (-prec+1)*bpow(x0-1))%R.
rewrite <- bpow_add.
apply ->bpow_le.
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply a.
assert (0 < sqrt x)%R; auto with real.
apply sqrt_lt_R0.
case Px; trivial.
intros H; contradict H; auto with real.
apply Rle_trans with ((1+bpow (-prec+1)*/2)*Rabs (sqrt x))%R;[right; ring|idtac].
apply Rle_trans with (sqrt 2 * Rabs (sqrt x))%R.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rsqr_incr_0_var.
2: apply sqrt_positivity; auto with real.
rewrite Rsqr_sqrt; auto with real.
apply Rle_trans with (1+bpow (- prec + 1)  + bpow (- prec + 1)*bpow (- prec + 1)*/4)%R.
right; unfold Rsqr; field.
apply Rle_trans with (1+bpow (- 2 + 1) + bpow (- 1 + 1) * bpow (- 1 + 1) * / 4)%R.
apply Rplus_le_compat.
apply Rplus_le_compat_l.
apply ->bpow_le; omega.
apply Rmult_le_compat_r.
left; replace 4%R with (INR 3+1)%R.
apply RinvN_pos.
simpl; ring.
rewrite <-bpow_add, <-bpow_add.
apply ->bpow_le; omega.
simpl.
ring_simplify (2-1)%Z; unfold Zpower_pos; simpl.
rewrite Zmult_1_r, 2!Rmult_1_l.
apply Rle_trans with (1+/ Z2R 2 + /2)%R.
2: simpl; right; field.
apply Rplus_le_compat.
apply Rplus_le_compat_l.
apply Rle_Rinv; try replace 0%R with (Z2R 0) by reflexivity.
apply Z2R_lt; omega.
apply Z2R_lt.
clear;destruct beta; simpl.
assert (2 <= radix_val)%Z.
now apply Zle_bool_imp_le.
omega.
apply Z2R_le.
clear;destruct beta; simpl.
now apply Zle_bool_imp_le.
left; apply Rinv_1_lt_contravar; auto with real.
rewrite <- (Rmult_1_l 2) at 1; auto with real.
rewrite sqrt_mult; auto with real.
rewrite Rabs_mult.
rewrite (Rabs_right (sqrt 2)); auto with real.
apply Rle_ge; apply sqrt_positivity; auto with real.
rewrite Hx2; unfold canonic_exponent, FLX_exp.
ring_simplify (prec + (projT1 (ln_beta beta x) - prec))%Z.
destruct (ln_beta beta x); simpl.
rewrite <- (Rabs_right x).
now apply a.
now apply Rle_ge.
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
assert (0 < sqrt x)%R; auto with real.
apply sqrt_lt_R0.
case Px; trivial.
intros H'; contradict H'; now apply sym_not_eq.
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
Qed.


End Fprop_divsqrt_error.

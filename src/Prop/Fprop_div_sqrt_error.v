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


Theorem div_error_N :
  forall x y,
  format x -> format y ->
  (y <> 0)%R ->
  format (x - rounding beta (FLX_exp prec) (ZrndN choice) (x/y) * y)%R.
Proof.
intros x y Hx Hy Zy.
case (Req_dec (rounding beta (FLX_exp prec) (ZrndN choice) (x/y)) 0); intros Hr.
rewrite Hr; ring_simplify (x-0*y)%R; assumption.
destruct (format_nx x Hx) as (fx,(Hx1,Hx2)).
destruct (format_nx y Hy) as (fy,(Hy1,Hy2)).
destruct (format_nx (rounding beta (FLX_exp prec) (ZrndN choice) (x / y))) as (fr,(Hr1,Hr2)).
apply generic_format_rounding.
now apply FLX_exp_correct.
unfold Rminus; apply format_add with fx (Fopp beta (Fmult beta fr fy)); trivial.
now rewrite Fopp_F2R,mult_F2R, <- Hr1, <- Hy1.
(* *)
apply Rle_lt_trans with (Rabs x).
replace (x + - (rounding beta (FLX_exp prec) (ZrndN choice) (x / y) * y))%R with
  (y * (-(rounding beta (FLX_exp prec) (ZrndN choice) (x / y) - x/y)))%R.
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
apply Rle_trans with (2* (/2 * ulp beta (FLX_exp prec) (F2R fr)))%R.
apply Rmult_le_compat_l.
auto with real.
rewrite <- Hr1.
apply ulp_half_error_f; trivial.
now apply FLX_exp_correct.
clear; intros; unfold FLX_exp; omega.
rewrite <- Rmult_assoc, Rinv_r.
2: assert (0 < 2)%R; auto with real.
unfold ulp.
destruct fr as (nr,er).
rewrite abs_F2R; unfold F2R at 2; simpl.
replace (cexp (F2R (Float beta nr er))) with er.
2: rewrite <- Hr1, <- Hr2; easy.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace 1%R with (Z2R 1) by easy.
apply Z2R_le.
assert (0 < Zabs nr)%Z;[idtac|omega].
apply F2R_gt_0_reg with beta er.
rewrite <- abs_F2R.
apply Rabs_pos_lt.
rewrite <- Hr1; assumption.
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
replace (x + - (rounding beta (FLX_exp prec) (ZrndN choice) (x / y) * y))%R with
  (y * (-(rounding beta (FLX_exp prec) (ZrndN choice) (x / y) - x/y)))%R.
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



Theorem div_error_Z :
  forall x y,
  format x -> format y ->
  format (x - rounding beta (FLX_exp prec) (ZrndTZ) (x/y) * y)%R.
Proof.
(* probablement seulement en FLX *)
Admitted. (* SB *) 


Theorem sqrt_error_N :
  forall x, (0 <= x)%R ->
  format x ->
  format (x - Rsqr (rounding beta (FLX_exp prec) (ZrndN choice) (sqrt x)))%R.
Proof.
(* probablement seulement en FLX *)
Admitted. (* SB *)



End Fprop_divsqrt_error.

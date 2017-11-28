(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2010-2013 Sylvie Boldo
#<br />#
Copyright (C) 2010-2013 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * Remainder of the division and square root are in the FLX format *)
Require Import Core Operations Relative Sterbenz.

Section Fprop_divsqrt_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.

Lemma generic_format_plus_prec :
  forall fexp, (forall e, (fexp e <= e - prec)%Z) ->
  forall x y (fx fy: float beta),
  (x = F2R fx)%R -> (y = F2R fy)%R -> (Rabs (x+y) < bpow (prec+Fexp fx))%R ->
  (Rabs (x+y) < bpow (prec+Fexp fy))%R ->
  generic_format beta fexp (x+y)%R.
Proof.
intros fexp Hfexp x y fx fy Hx Hy H1 H2.
case (Req_dec (x+y) 0); intros H.
rewrite H; apply generic_format_0.
rewrite Hx, Hy, <- F2R_plus.
apply generic_format_F2R.
intros _.
case_eq (Fplus beta fx fy).
intros mz ez Hz.
rewrite <- Hz.
apply Zle_trans with (Zmin (Fexp fx) (Fexp fy)).
rewrite F2R_plus, <- Hx, <- Hy.
unfold cexp.
apply Zle_trans with (1:=Hfexp _).
apply Zplus_le_reg_l with prec; ring_simplify.
apply mag_le_bpow with (1 := H).
now apply Zmin_case.
rewrite <- Fexp_Fplus, Hz.
apply Zle_refl.
Qed.

Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (cexp beta (FLX_exp prec)).

Variable choice : Z -> bool.


(** Remainder of the division in FLX *)
Theorem div_error_FLX :
  forall rnd { Zrnd : Valid_rnd rnd } x y,
  format x -> format y ->
  format (x - round beta (FLX_exp prec) rnd (x/y) * y)%R.
Proof with auto with typeclass_instances.
intros rnd Zrnd x y Hx Hy.
destruct (Req_dec y 0) as [Zy|Zy].
now rewrite Zy, Rmult_0_r, Rminus_0_r.
destruct (Req_dec (round beta (FLX_exp prec) rnd (x/y)) 0) as [Hr|Hr].
rewrite Hr; ring_simplify (x-0*y)%R; assumption.
assert (Zx: x <> R0).
contradict Hr.
rewrite Hr.
unfold Rdiv.
now rewrite Rmult_0_l, round_0.
destruct (canonical_generic_format _ _ x Hx) as (fx,(Hx1,Hx2)).
destruct (canonical_generic_format _ _ y Hy) as (fy,(Hy1,Hy2)).
destruct (canonical_generic_format beta (FLX_exp prec) (round beta (FLX_exp prec) rnd (x / y))) as (fr,(Hr1,Hr2)).
apply generic_format_round...
unfold Rminus; apply generic_format_plus_prec with fx (Fopp beta (Fmult beta fr fy)); trivial.
intros e; apply Zle_refl.
now rewrite F2R_opp, F2R_mult, <- Hr1, <- Hy1.
(* *)
destruct (relative_error_FLX_ex beta prec (prec_gt_0 prec) rnd (x / y)%R) as (eps,(Heps1,Heps2)).
rewrite Heps2.
rewrite <- Rabs_Ropp.
replace (-(x + - (x / y * (1 + eps) * y)))%R with (x * eps)%R by now field.
rewrite Rabs_mult.
apply Rlt_le_trans with (Rabs x * 1)%R.
apply Rmult_lt_compat_l.
now apply Rabs_pos_lt.
apply Rlt_le_trans with (1 := Heps1).
change 1%R with (bpow 0).
apply bpow_le.
generalize (prec_gt_0 prec).
clear ; omega.
rewrite Rmult_1_r.
rewrite Hx2, <- Hx1.
unfold cexp.
destruct (mag beta x) as (ex, Hex).
simpl.
specialize (Hex Zx).
apply Rlt_le.
apply Rlt_le_trans with (1 := proj2 Hex).
apply bpow_le.
unfold FLX_exp.
ring_simplify.
apply Zle_refl.
(* *)
replace (Fexp (Fopp beta (Fmult beta fr fy))) with (Fexp fr + Fexp fy)%Z.
2: unfold Fopp, Fmult; destruct fr; destruct fy; now simpl.
replace (x + - (round beta (FLX_exp prec) rnd (x / y) * y))%R with
  (y * (-(round beta (FLX_exp prec) rnd (x / y) - x/y)))%R.
2: field; assumption.
rewrite Rabs_mult.
apply Rlt_le_trans with (Rabs y * bpow (Fexp fr))%R.
apply Rmult_lt_compat_l.
now apply Rabs_pos_lt.
rewrite Rabs_Ropp.
replace (bpow (Fexp fr)) with (ulp beta (FLX_exp prec) (F2R fr)).
rewrite <- Hr1.
apply error_lt_ulp_round...
apply Rmult_integral_contrapositive_currified; try apply Rinv_neq_0_compat; assumption.
rewrite ulp_neq_0.
2: now rewrite <- Hr1.
apply f_equal.
now rewrite Hr2, <- Hr1.
replace (prec+(Fexp fr+Fexp fy))%Z with ((prec+Fexp fy)+Fexp fr)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite Hy2, <- Hy1 ; unfold cexp, FLX_exp.
ring_simplify (prec + (mag beta y - prec))%Z.
destruct (mag beta y); simpl.
left; now apply a.
Qed.

(** Remainder of the square in FLX (with p>1) and rounding to nearest *)
Variable Hp1 : Zlt 1 prec.

Theorem sqrt_error_FLX_N :
  forall x, format x ->
  format (x - Rsqr (round beta (FLX_exp prec) (Znearest choice) (sqrt x)))%R.
Proof with auto with typeclass_instances.
intros x Hx.
destruct (total_order_T x 0) as [[Hxz|Hxz]|Hxz].
unfold sqrt.
destruct (Rcase_abs x).
rewrite round_0...
unfold Rsqr.
now rewrite Rmult_0_l, Rminus_0_r.
elim (Rlt_irrefl 0).
now apply Rgt_ge_trans with x.
rewrite Hxz, sqrt_0, round_0...
unfold Rsqr.
rewrite Rmult_0_l, Rminus_0_r.
apply generic_format_0.
case (Req_dec (round beta (FLX_exp prec) (Znearest choice) (sqrt x)) 0); intros Hr.
rewrite Hr; unfold Rsqr; ring_simplify (x-0*0)%R; assumption.
destruct (canonical_generic_format _ _ x Hx) as (fx,(Hx1,Hx2)).
destruct (canonical_generic_format beta (FLX_exp prec) (round beta (FLX_exp prec) (Znearest choice) (sqrt x))) as (fr,(Hr1,Hr2)).
apply generic_format_round...
unfold Rminus; apply generic_format_plus_prec with fx (Fopp beta (Fmult beta fr fr)); trivial.
intros e; apply Zle_refl.
unfold Rsqr; now rewrite F2R_opp,F2R_mult, <- Hr1.
(* *)
apply Rle_lt_trans with x.
apply Rabs_minus_le.
apply Rle_0_sqr.
destruct (relative_error_N_FLX_ex beta prec (prec_gt_0 prec) choice (sqrt x)) as (eps,(Heps1,Heps2)).
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
replace (-1 + (1 + Rabs eps))%R with (Rabs eps) by ring.
apply Rle_trans with (1 := Heps1).
rewrite Rabs_pos_eq.
apply Rmult_le_reg_l with 2%R.
now apply IZR_lt.
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
apply Rle_trans with (bpow (-1)).
apply bpow_le.
omega.
replace (2 * (-1 + 5 / 4))%R with (/2)%R by field.
apply Rinv_le.
now apply IZR_lt.
apply IZR_le.
unfold Zpower_pos. simpl.
rewrite Zmult_1_r.
apply Zle_bool_imp_le.
apply beta.
now apply IZR_neq.
unfold Rdiv.
apply Rmult_le_pos.
now apply IZR_le.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply IZR_lt.
now apply IZR_neq.
unfold Rsqr.
replace (5 * 5 / (4 * 4))%R with (25 * /16)%R by field.
apply Rmult_le_reg_r with 16%R.
now apply IZR_lt.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now apply (IZR_le _ 32).
now apply IZR_neq.
rewrite Hx2, <- Hx1; unfold cexp, FLX_exp.
ring_simplify (prec + (mag beta x - prec))%Z.
destruct (mag beta x); simpl.
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
apply error_le_half_ulp_round...
right; rewrite ulp_neq_0.
2: now rewrite <- Hr1.
apply f_equal.
rewrite Hr2, <- Hr1; trivial.
rewrite Rmult_assoc, Rmult_comm.
replace (prec+(Fexp fr+Fexp fr))%Z with (Fexp fr + (prec+Fexp fr))%Z by ring.
rewrite bpow_plus, Rmult_assoc.
apply Rmult_lt_compat_l.
apply bpow_gt_0.
apply Rmult_lt_reg_l with (1 := Rlt_0_2).
apply Rle_lt_trans with (Rabs (F2R fr + sqrt x)).
right; field.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
(* . *)
assert (Rabs (F2R fr) < bpow (prec + Fexp fr))%R.
rewrite Hr2.
unfold cexp, FLX_exp.
ring_simplify (prec + (mag beta (F2R fr) - prec))%Z.
destruct (mag beta (F2R fr)); simpl.
apply a.
rewrite <- Hr1; auto.
(* . *)
apply Rlt_le_trans with (bpow (prec + Fexp fr)+ Rabs (sqrt x))%R.
now apply Rplus_lt_compat_r.
(* . *)
replace (2 * bpow (prec + Fexp fr))%R with (bpow (prec + Fexp fr) + bpow (prec + Fexp fr))%R by ring.
apply Rplus_le_compat_l.
assert (sqrt x <> 0)%R.
apply Rgt_not_eq.
now apply sqrt_lt_R0.
destruct (mag beta (sqrt x)) as (es,Es).
specialize (Es H0).
apply Rle_trans with (bpow es).
now apply Rlt_le.
apply bpow_le.
case (Zle_or_lt es (prec + Fexp fr)) ; trivial.
intros H1.
absurd (Rabs (F2R fr) < bpow (es - 1))%R.
apply Rle_not_lt.
rewrite <- Hr1.
apply abs_round_ge_generic...
apply generic_format_bpow.
unfold FLX_exp; omega.
apply Es.
apply Rlt_le_trans with (1:=H).
apply bpow_le.
omega.
now apply Rlt_le.
Qed.

End Fprop_divsqrt_error.

Section format_REM_aux.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { monotone_exp : Monotone_exp fexp }.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Notation format := (generic_format beta fexp).

Lemma format_REM_aux:
 forall (x y : R),
  (format x) -> (format y) -> (0 <= x)%R -> (0 < y)%R ->
    ~ (rnd (x/y) = 1%Z /\ (0 < x/y < /2)%R) ->
    format (x- IZR (rnd (x/y))*y).
Proof with auto with typeclass_instances.
intros x y Fx Fy Hx Hy rnd_small.
pose (n:=rnd (x / y)).
assert (Hn:(IZR n = round beta (FIX_exp 0) rnd (x/y))%R).
unfold round, FIX_exp, cexp, scaled_mantissa, F2R; simpl.
now rewrite 2!Rmult_1_r.
assert (H:(0 <= n)%Z).
apply le_IZR; rewrite Hn; simpl.
apply Rle_trans with (round beta (FIX_exp 0) rnd 0).
right; apply sym_eq, round_0...
apply round_le...
apply Fourier_util.Rle_mult_inv_pos; assumption.
case (Zle_lt_or_eq 0 n); try exact H.
clear H; intros H.
case (Zle_lt_or_eq 1 n).
omega.
clear H; intros H.
set (ex := cexp beta fexp x).
set (ey := cexp beta fexp y).
set (mx := Ztrunc (scaled_mantissa beta fexp x)).
set (my := Ztrunc (scaled_mantissa beta fexp y)).
case (Zle_or_lt ey ex); intros Hexy.
(* ey <= ex *)
assert (H0:(x-IZR n *y = F2R (Float beta (mx*beta^(ex-ey) - n*my) ey))%R).
unfold Rminus; rewrite Rplus_comm.
replace (IZR n) with (F2R (Float beta n 0)).
rewrite Fx, Fy.
fold mx my ex ey.
rewrite <- F2R_mult.
rewrite <- F2R_opp.
rewrite <- F2R_plus.
unfold Fplus. simpl.
rewrite Zle_imp_le_bool with (1 := Hexy).
f_equal; f_equal; ring.
unfold F2R; simpl; ring.
fold n; rewrite H0.
apply generic_format_F2R.
rewrite <- H0; intros H3.
apply monotone_exp.
apply mag_le_abs.
rewrite H0; apply F2R_neq_0; easy.
apply Rmult_le_reg_l with (/Rabs y)%R.
apply Rinv_0_lt_compat.
apply Rabs_pos_lt.
now apply Rgt_not_eq.
rewrite Rinv_l.
2: apply Rgt_not_eq, Rabs_pos_lt.
2: now apply Rgt_not_eq.
rewrite <- Rabs_Rinv.
2: now apply Rgt_not_eq.
rewrite <- Rabs_mult.
replace (/y * (x - IZR n *y))%R with (-(IZR n - x/y))%R.
rewrite Rabs_Ropp.
rewrite Hn.
apply Rle_trans with (1:= error_le_ulp beta (FIX_exp 0) _ _).
rewrite ulp_FIX.
simpl; apply Rle_refl.
field.
now apply Rgt_not_eq.
(* ex < ey: impossible as 1 < n *)
absurd (1 < n)%Z; try easy.
apply Zle_not_lt.
apply le_IZR; simpl; rewrite Hn.
apply round_le_generic...
apply generic_format_FIX.
exists (Float beta 1 0); try easy.
unfold F2R; simpl; ring.
apply Rmult_le_reg_r with y; try easy.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l, Rmult_1_r, Rmult_1_l.
2: now apply Rgt_not_eq.
assert (mag beta x < mag beta y)%Z.
case (Zle_or_lt (mag beta y) (mag beta x)); try easy.
intros J; apply monotone_exp in J; clear -J Hexy.
unfold ex, ey, cexp in Hexy; omega.
left; apply lt_mag with beta; easy.
(* n = 1 -> Sterbenz + rnd_small *)
intros Hn'; fold n; rewrite <- Hn'.
rewrite Rmult_1_l.
case Hx; intros Hx'.
assert (J:(0 < x/y)%R).
apply Fourier_util.Rlt_mult_inv_pos; assumption.
apply sterbenz...
assert (H0:(Rabs (1  - x/y) < 1)%R).
rewrite Hn', Hn.
apply Rlt_le_trans with (ulp beta (FIX_exp 0) (round beta (FIX_exp 0) rnd (x / y)))%R.
apply error_lt_ulp_round...
now apply Rgt_not_eq.
rewrite ulp_FIX.
rewrite <- Hn, <- Hn'.
apply Rle_refl.
apply Rabs_lt_inv in H0.
split; apply Rmult_le_reg_l with (/y)%R; try now apply Rinv_0_lt_compat.
unfold Rdiv; rewrite <- Rmult_assoc.
rewrite Rinv_l.
2: now apply Rgt_not_eq.
rewrite Rmult_1_l, Rmult_comm; fold (x/y)%R.
case (Rle_or_lt (/2) (x/y)); try easy.
intros K; contradict rnd_small; split.
fold n; rewrite <- Hn'; easy.
now split.
apply Ropp_le_cancel; apply Rplus_le_reg_l with 1%R.
apply Rle_trans with (1-x/y)%R.
2: right; unfold Rdiv; ring.
left; apply Rle_lt_trans with (2:=proj1 H0).
right; field.
now apply Rgt_not_eq.
rewrite <- Hx', Rminus_0_l.
now apply generic_format_opp.
(* n = 0 *)
clear H; intros H; fold n; rewrite <- H.
now rewrite Rmult_0_l, Rminus_0_r.
Qed.

End format_REM_aux.

Section format_REM.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { monotone_exp : Monotone_exp fexp }.

Notation format := (generic_format beta fexp).

Theorem format_REM :
  forall rnd : R -> Z, Valid_rnd rnd ->
  forall x y : R,
  ~ (Zabs (rnd (x/y)%R) = 1%Z /\ (Rabs (x/y) < /2)%R) ->
  format x -> format y ->
  format (x - IZR (rnd (x/y)%R) * y).
Proof with auto with typeclass_instances.
(* assume 0 < y *)
assert (H: forall rnd : R -> Z, Valid_rnd rnd ->
  forall (x y : R),
     ~ (Zabs (rnd (x/y)%R) = 1%Z /\ (Rabs (x/y) < /2)%R) ->
  (format x) -> (format y) -> (0 < y)%R ->
    format (x-IZR (rnd (x/y)%R)*y)).
intros rnd valid_rnd x y Hrnd Fx Fy Hy.
case (Rle_or_lt 0 x); intros Hx.
apply format_REM_aux; try easy.
intros (K1,K2); apply Hrnd; split.
rewrite K1; easy.
rewrite Rabs_right; try easy.
apply Rle_ge; left; apply K2.
replace (x-(IZR (rnd (x/y)))*y)%R with
   (-((-x)-(IZR ((Zrnd_opp rnd)
            ((-x)/y)))*y))%R.
apply generic_format_opp.
apply format_REM_aux; try easy...
now apply generic_format_opp.
apply Ropp_le_cancel; rewrite Ropp_0, Ropp_involutive; now left.
intros (K1,K2); apply Hrnd; split.
unfold Zrnd_opp in K1.
replace (- (- x / y))%R with (x/y)%R in K1 by (unfold Rdiv; ring).
rewrite <- (Zopp_involutive (rnd _)), K1, Zabs_Zopp; easy.
replace (x/y)%R with (-(-x/y))%R by (unfold Rdiv; ring).
rewrite Rabs_Ropp, Rabs_right; try easy.
apply Rle_ge; left; apply K2.
apply trans_eq with (x-((-IZR ((Zrnd_opp rnd) (- x / y)))*y))%R.
ring.
apply Rplus_eq_compat_l; f_equal; f_equal.
unfold Zrnd_opp; rewrite opp_IZR, Ropp_involutive.
f_equal; f_equal; unfold Rdiv; ring.
(* *)
intros rnd valid_rnd x y Hrnd Fx Fy.
case (Rle_or_lt 0 y); intros Hy.
destruct Hy as [Hy|Hy].
now apply H.
now rewrite <- Hy, Rmult_0_r, Rminus_0_r.
replace (IZR (rnd (x/y))*y)%R with
  (IZR ((Zrnd_opp rnd) ((x/(-y))))*(-y))%R.
apply H; try easy...
intros (K1,K2); apply Hrnd; split.
unfold Zrnd_opp in K1.
replace (- ( x / - y))%R with (x/y)%R in K1.
rewrite <- (Zopp_involutive (rnd _)), Zabs_Zopp, K1; easy.
field; apply Rlt_not_eq; assumption.
replace (x/y)%R with (-(x/-y))%R.
now rewrite Rabs_Ropp.
field; apply Rlt_not_eq; assumption.
now apply generic_format_opp.
apply Ropp_lt_cancel; now rewrite Ropp_0, Ropp_involutive.
rewrite Ropp_mult_distr_r_reverse, Ropp_mult_distr_l.
unfold Zrnd_opp; rewrite opp_IZR, Ropp_involutive.
f_equal; f_equal; f_equal.
field; now apply Rlt_not_eq.
Qed.

Theorem format_REM_ZR:
  forall x y : R,
  format x -> format y ->
  format (x - IZR (Ztrunc (x/y)) * y).
Proof with auto with typeclass_instances.
intros x y Fx Fy.
apply format_REM; try easy...
intros (K1,K2).
assert (forall z, (0 <= z < /2)%R -> Ztrunc z = 0)%Z.
intros l Hl; rewrite Ztrunc_floor; try apply Hl.
apply Zfloor_imp.
simpl; split; try easy.
apply Rlt_trans with (1:=proj2 Hl).
apply Rmult_lt_reg_l with 2%R; try apply Rlt_0_2.
apply Rplus_lt_reg_l with (-1)%R.
apply Rle_lt_trans with 0%R.
right; field.
apply Rlt_le_trans with (1:=Rlt_0_1).
right; simpl; ring.
absurd (Ztrunc (x / y) = 0)%Z.
intros K3; contradict K1.
rewrite K3; easy.
case (Rle_or_lt 0 (x/y)); intros H1.
apply H; split; try apply H1.
rewrite Rabs_right in K2; try apply Rle_ge; easy.
rewrite <- (Ropp_involutive (x/y)), <- Zopp_0.
rewrite Ztrunc_opp; f_equal.
apply H; split.
apply Ropp_le_cancel; rewrite Ropp_involutive, Ropp_0; now left.
rewrite Rabs_left in K2; easy.
Qed.

Theorem format_REM_N :
  forall choice,
  forall x y : R,
  format x -> format y ->
  format (x - IZR (Znearest choice (x/y)) * y).
Proof with auto with typeclass_instances.
intros choice x y Fx Fy.
apply format_REM; try easy...
intros (K1,K2).
absurd (Znearest choice (x / y) = 0)%Z.
intros K3; contradict K1; rewrite K3; easy.
apply Znearest_imp.
now rewrite Rminus_0_r.
Qed.

End format_REM.

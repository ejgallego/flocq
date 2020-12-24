(**
This example is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2013-2018 Sylvie Boldo

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import Reals Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.

Section Sec1.

Open Scope R_scope.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Variable choice1 : Z -> bool.
Variable choice2 : Z -> bool.
Variable choice3 : Z -> bool.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx1 :=(round beta (FLX_exp prec) (Znearest choice1)).
Notation round_flx2 :=(round beta (FLX_exp prec) (Znearest choice2)).
Notation round_flx3 :=(round beta (FLX_exp prec) (Znearest choice3)).
Notation ulp_flx :=(ulp beta (FLX_exp prec)).
Notation pred_flx := (pred beta (FLX_exp prec)).

Hypothesis pGt1: (1 < prec)%Z.

Variables x:R.
Hypothesis xPos: 0 < x.
Hypothesis Fx: format x.

Let y:=round_flx1(x*x).
Let z:=round_flx2(sqrt y).


Theorem round_flx_sqr_sqrt_middle: x = sqrt (IZR beta) * bpow (mag beta x - 1) -> z=x.
Proof with auto with typeclass_instances.
intros Hx.
unfold z, y.
replace (round_flx1 (x * x)) with (bpow (2*mag beta x -1)).
replace (sqrt (bpow (2 * mag beta x - 1))) with x.
apply round_generic...
apply sym_eq, sqrt_lem_1.
apply bpow_ge_0.
now left.
rewrite Hx at 1.
rewrite Rmult_comm; rewrite Hx at 1.
apply trans_eq with ((sqrt (IZR beta)*sqrt (IZR beta)) * (bpow (mag beta x-1)*bpow (mag beta x-1))).
ring.
rewrite <- bpow_plus, sqrt_def, <- bpow_1, <- bpow_plus.
apply f_equal; ring.
left; apply radix_pos.
replace (x*x) with (bpow (2 * mag beta x - 1)).
apply sym_eq, round_generic...
apply generic_format_bpow.
unfold FLX_exp; omega.
apply sym_eq; rewrite Hx at 1.
rewrite Rmult_comm; rewrite Hx at 1.
apply trans_eq with ((sqrt (IZR beta)*sqrt (IZR beta)) * (bpow (mag beta x-1)*bpow (mag beta x-1))).
ring.
rewrite <- bpow_plus, sqrt_def, <- bpow_1, <- bpow_plus.
apply f_equal; ring.
left; apply radix_pos.
Qed.

Theorem round_flx_sqr_sqrt_le: (beta <= 4)%Z -> z <= x.
Proof with auto with typeclass_instances.
intros Hb.
case (Req_dec x (sqrt (IZR beta) * bpow (mag beta x - 1))).
intros L; right; now apply round_flx_sqr_sqrt_middle.
intros Hx'.
assert (0 < x*x) by now apply Rmult_lt_0_compat.
assert (0 <= 1 + ulp_flx (x * x) / 2 / (x * x)).
rewrite <- (Rplus_0_l 0).
apply Rplus_le_compat; auto with real.
unfold Rdiv; apply Rmult_le_pos.
apply Rmult_le_pos; auto with real; apply ulp_ge_0.
left; auto with real.
assert (0 <= 1 + ulp_flx x / 2 / x).
rewrite <- (Rplus_0_l 0).
apply Rplus_le_compat; auto with real.
unfold Rdiv; apply Rmult_le_pos.
apply Rmult_le_pos; auto with real; apply ulp_ge_0.
left; auto with real.
(* *)
apply round_N_le_midp; try assumption...
apply Rlt_le_trans with (x*(1+ulp_flx x / 2 / x)).
2: right; rewrite succ_eq_pos; try now left.
2: field; auto with real.
apply Rle_lt_trans with (sqrt ((x*x)*(1+ulp_flx (x*x)/2/(x*x)))).
apply sqrt_le_1_alt.
apply Rplus_le_reg_l with (-x*x).
apply Rle_trans with (y-x*x);[right; ring|idtac].
apply Rle_trans with (/2*ulp_flx (x*x));[idtac|right; field; auto with real].
apply Rle_trans with (1:=RRle_abs _).
apply error_le_half_ulp...
rewrite sqrt_mult; auto with real.
rewrite sqrt_square; auto with real.
apply Rmult_lt_compat_l.
assumption.
rewrite <- (sqrt_square (1 + ulp_flx x / 2 / x)); try assumption.
apply sqrt_lt_1_alt.
split; try assumption.
apply Rmult_lt_reg_l with (2*x*x).
rewrite Rmult_assoc; apply Rmult_lt_0_compat; auto with real.
apply Rplus_lt_reg_r with (-2*x*x - ulp_flx x*ulp_flx x/2).
apply Rle_lt_trans with (ulp_flx (x*x) - ulp_flx x*ulp_flx x/2).
right; field.
auto with real.
apply Rlt_le_trans with (2*x*ulp_flx x).
2: right; field; auto with real.
apply Rle_lt_trans with (ulp_flx (x * x) + ulp_flx x * ulp_flx x / 2).
apply Rplus_le_compat_l.
apply Rplus_le_reg_r with (ulp_flx x * ulp_flx x / 2).
apply Rle_trans with 0;[right; ring|idtac].
apply Rle_trans with (ulp_flx x * ulp_flx x).
apply Rmult_le_pos; apply ulp_ge_0.
right; field.
rewrite 2!ulp_neq_0.
2: now apply Rgt_not_eq.
2: now apply Rgt_not_eq.
unfold cexp, FLX_exp.
destruct (mag beta x) as (e,He).
simpl.
assert (bpow (e - 1) <= x < bpow e).
rewrite <- (Rabs_right x).
apply He; auto with real.
apply Rle_ge; auto with real.
rewrite <- bpow_plus.
case (Rle_or_lt x (sqrt (IZR (radix_val beta))*bpow (e-1))); intros Hx.
(* . *)
destruct Hx.
replace (mag beta (x * x)-prec)%Z with (2*e-1-prec)%Z.
apply Rlt_le_trans with (bpow (2 * e - 1 - prec) + bpow (2*e - 1 - prec) / 2).
apply Rplus_lt_compat_l.
unfold Rdiv; apply Rmult_lt_compat_r.
auto with real.
apply bpow_lt.
omega.
apply Rle_trans with (2*bpow (2 * e - 1 - prec)).
apply Rle_trans with (3/2*bpow (2 * e - 1 - prec)).
right; field.
apply Rmult_le_compat_r.
apply bpow_ge_0.
interval.
rewrite Rmult_assoc; apply Rmult_le_compat_l.
auto with real.
apply Rle_trans with (bpow (e-1)*bpow (e - prec)).
rewrite <- bpow_plus.
apply bpow_le.
omega.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply H2.
apply f_equal with (f:= fun z => (z-prec)%Z).
apply sym_eq, mag_unique.
rewrite Rabs_right.
split.
apply Rle_trans with (bpow (e-1)*bpow (e-1)).
rewrite <- bpow_plus.
right; apply f_equal; ring.
apply Rmult_le_compat; try apply H2; try apply bpow_ge_0.
apply Rlt_le_trans with ((sqrt (IZR beta)*bpow (e-1))*(sqrt (IZR beta)*bpow (e-1))).
apply Rmult_le_0_lt_compat; try apply H3; now left.
apply Rle_trans with ((sqrt (IZR beta)*sqrt (IZR beta)) * (bpow (e-1)*bpow (e-1))).
right; ring.
rewrite <- bpow_plus, sqrt_def, <- bpow_1, <- bpow_plus.
right; apply f_equal; ring.
left; apply radix_pos.
apply Rle_ge; auto with real.
(* . *)
simpl in Hx'; contradict H3; assumption.
(* . *)
replace (mag beta (x * x)-prec)%Z with (2*e-prec)%Z.
case (Zle_lt_or_eq _ _ Hb); clear Hb; intros Hb.
(* .. *)
apply Rle_lt_trans with (2*(sqrt (IZR beta) * bpow (e - 1))* bpow (e - prec)).
2: apply Rmult_lt_compat_r.
2: apply bpow_gt_0.
2: apply Rmult_lt_compat_l; try assumption.
2: auto with real.
apply Rle_trans with ((2 * sqrt (IZR beta)) * bpow (2*e - 1- prec)).
2: replace (2*e)%Z with (e+e)%Z by ring; unfold Zminus.
2: repeat rewrite bpow_plus; right; ring.
apply Rle_trans with ((IZR beta + /4)*bpow (2 * e - 1 - prec)).
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
rewrite <- bpow_1, <- bpow_plus.
right; apply f_equal; ring.
apply Rmult_le_reg_l with 4%R.
apply Rmult_lt_0_compat; auto with real.
apply Rle_trans with (2*bpow (e - prec + (e - prec))).
right; field.
apply Rle_trans with (bpow (2 * e - 1 - prec)).
2: right; field.
apply Rle_trans with (bpow (1+(e - prec + (e - prec)))).
rewrite (bpow_plus _ 1%Z).
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite bpow_1.
apply IZR_le.
generalize (radix_gt_1 beta).
omega.
apply bpow_le.
omega.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert ((radix_val beta = 2%Z)%Z \/ radix_val beta = 3)%Z.
assert (1 < radix_val beta)%Z by apply radix_gt_1.
omega.
destruct H3; rewrite H3; simpl; interval.
(* .. *)
apply Rlt_le_trans with (2 * (2*bpow (e - 1)+bpow (e-prec)) * bpow (e - prec)).
apply Rlt_le_trans with (4* bpow (e - 1)* bpow (e - prec)
  + bpow (e - prec) * bpow (e - prec)*2).
2: right; ring.
replace (4 * bpow (e - 1) * bpow (e - prec)) with (bpow (2 * e - prec)).
apply Rplus_lt_compat_l.
rewrite <- bpow_plus.
unfold Rdiv; apply Rmult_lt_compat_l.
apply bpow_gt_0.
interval.
replace 4 with (bpow 1).
repeat rewrite <- bpow_plus.
apply f_equal; ring.
rewrite bpow_1, Hb; reflexivity.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_le_compat_l.
auto with real.
apply Rle_trans with (2 * bpow (e - 1) + ulp_flx (2 * bpow (e - 1))).
apply Rplus_le_compat_l.
rewrite ulp_neq_0.
2: apply Rmult_integral_contrapositive_currified; apply Rgt_not_eq.
2: apply Rlt_0_2.
2: apply bpow_gt_0.
unfold cexp, FLX_exp.
right; apply f_equal.
apply f_equal2; try reflexivity.
apply sym_eq, mag_unique.
rewrite Rabs_right.
split.
rewrite <- (Rmult_1_l (bpow (e-1))) at 1.
apply Rmult_le_compat_r.
apply bpow_ge_0.
auto with real.
apply Rlt_le_trans with (IZR beta*bpow (e - 1)).
apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite Hb; simpl; interval.
rewrite <- bpow_1, <- bpow_plus.
right; apply f_equal; ring.
apply Rle_ge, Rmult_le_pos.
auto with real.
apply bpow_ge_0.
rewrite <- succ_eq_pos.
apply succ_le_lt...
apply generic_format_FLX.
exists (Float beta 2 (e-1)).
unfold F2R; now simpl.
apply Z.lt_le_trans with (4^1)%Z.
simpl; unfold Z.pow_pos; simpl; omega.
rewrite Hb.
apply (Zpower_le (Build_radix 4 eq_refl)).
now apply Zlt_le_weak.
apply Rle_lt_trans with (2:=Hx).
replace (sqrt (IZR beta)) with 2%R.
now right.
rewrite Hb; simpl.
apply sym_eq, sqrt_square; auto with real.
apply Rmult_le_pos.
now auto with real.
apply bpow_ge_0.
apply f_equal with (f:= fun z => (z-prec)%Z).
apply sym_eq, mag_unique.
rewrite Rabs_right.
split.
apply Rle_trans with ((sqrt (IZR beta)*bpow (e-1))*(sqrt (IZR beta)*bpow (e-1))).
apply Rle_trans with ((sqrt (IZR beta)*sqrt (IZR beta)) * (bpow (e-1)*bpow (e-1))).
2: right; ring.
rewrite <- bpow_plus, sqrt_def, <- bpow_1, <- bpow_plus.
right; apply f_equal; ring.
left; apply radix_pos.
apply Rmult_le_compat.
apply Rmult_le_pos; try apply sqrt_pos; apply bpow_ge_0.
apply Rmult_le_pos; try apply sqrt_pos; apply bpow_ge_0.
now left.
now left.
apply Rlt_le_trans with (bpow (e)*bpow (e)).
2: rewrite <- bpow_plus.
2: right; apply f_equal; ring.
apply Rmult_le_0_lt_compat; try apply H2.
now left.
now left.
apply Rle_ge; auto with real.
Qed.

Lemma ulp_sqr_ulp_lt: forall u, 0 < u ->
  (u < sqrt (IZR (radix_val beta)) * bpow (mag beta u-1)) ->
  ulp_flx (u * u) + ulp_flx u * ulp_flx u / 2 < 2 * u * ulp_flx u.
Proof with auto with typeclass_instances.
intros u Hu.
rewrite 2!ulp_neq_0.
2: now apply Rgt_not_eq.
2: now apply Rgt_not_eq, Rmult_lt_0_compat.
unfold cexp, FLX_exp.
(* *)
destruct (mag beta u) as (e,He); simpl.
intros Cu.
assert (He2:(bpow (e - 1) <= u < bpow e)).
rewrite <- (Rabs_right u).
apply He; auto with real.
apply Rle_ge; now left.
clear He.
destruct (mag beta (u*u)) as (i,Hi); simpl.
assert (Hi2:(bpow (i - 1) <= u*u < bpow i)).
rewrite <- (Rabs_right (u*u)).
apply Hi; auto with real.
apply Rle_ge; apply Rmult_le_pos; auto with real.
clear Hi.
assert (i=2*e-1)%Z.
assert (2*e-2 < i /\ i-1 < 2*e-1)%Z;[idtac|omega].
split;apply lt_bpow with beta.
apply Rle_lt_trans with (2:=proj2 Hi2).
replace (2*e-2)%Z with ((e-1)+(e-1))%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat; try apply bpow_ge_0; apply He2.
apply Rle_lt_trans with (1:=proj1 Hi2).
apply Rlt_le_trans with  ((sqrt (IZR beta) * bpow (e - 1))*(sqrt (IZR beta) * bpow (e - 1))).
apply Rlt_trans with ((sqrt (IZR beta) * bpow (e - 1))*u).
now apply Rmult_lt_compat_r.
apply Rmult_lt_compat_l.
apply Rlt_trans with (1:=Hu); assumption.
assumption.
right; apply trans_eq with ((sqrt (IZR beta) * sqrt (IZR beta)) *(bpow (e - 1) * bpow (e - 1)));[ring|idtac].
rewrite <- bpow_plus.
rewrite sqrt_sqrt.
replace (IZR beta) with (bpow 1).
rewrite <- bpow_plus.
apply f_equal; ring.
apply bpow_1.
generalize (radix_gt_0 beta); intros.
left; now apply IZR_lt.
rewrite H.
apply Rlt_le_trans with (2 * bpow (e-1) * bpow (e - prec)).
change 2%R with (1 + 1)%R.
rewrite Rmult_assoc, Rmult_plus_distr_r, Rmult_1_l.
rewrite <- 2!bpow_plus.
replace (e - 1 + (e - prec))%Z with (2 * e - 1 - prec)%Z by ring.
apply Rplus_lt_compat_l.
apply Rmult_lt_reg_l with 2%R; auto with real.
apply Rle_lt_trans with (bpow (e - prec + (e - prec))).
right; field.
apply Rlt_le_trans with (1*bpow (2 * e - 1 - prec)).
rewrite Rmult_1_l; apply bpow_lt.
omega.
apply Rmult_le_compat_r; auto with real.
apply bpow_ge_0.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_le_compat_l; auto with real.
apply He2.
Qed.

Theorem round_flx_sqr_sqrt_exact_case1:
  (x < sqrt (IZR (radix_val beta)) * bpow (mag beta x-1)) ->
    z = x.
Proof with auto with typeclass_instances.
intros Cu.
case (Req_dec x (bpow (mag beta x - 1))); intros Hx.
(* *)
unfold z, y.
rewrite Hx, <- bpow_plus.
rewrite (round_generic _ _ _ (bpow (mag beta x - 1 + (mag beta x - 1))))...
replace (sqrt (bpow (mag beta x - 1 + (mag beta x - 1)))) with (bpow (mag beta x - 1 )).
apply round_generic...
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
apply sym_eq, sqrt_lem_1; try apply bpow_ge_0.
apply sym_eq, bpow_plus.
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
(* *)
assert (0 < x*x) by now apply Rmult_lt_0_compat.
assert (0 <= 1 - ulp_flx x / 2 / x).
apply Rplus_le_reg_l with (ulp_flx x / 2 / x); ring_simplify.
apply Rmult_le_reg_l with 2; auto with real.
apply Rmult_le_reg_l with x; auto with real.
apply Rle_trans with (ulp_flx x).
right; field; auto with real.
apply Rle_trans with x.
apply ulp_le_id; auto.
lra.
assert (0 <= 1 - ulp_flx (x * x) / 2 / (x * x)).
apply Rplus_le_reg_l with (ulp_flx (x*x) / 2 / (x*x)); ring_simplify.
apply Rmult_le_reg_l with 2; auto with real.
apply Rmult_le_reg_l with (x*x); auto with real.
apply Rle_trans with (ulp_flx (x*x)).
right; field; auto with real.
apply Rle_trans with (x*x).
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold cexp, FLX_exp.
destruct (mag beta (x*x)) as (e,He); simpl.
apply Rle_trans with (bpow (e-1)).
apply bpow_le; auto with zarith.
rewrite <- (Rabs_right (x*x)).
apply He; auto with real.
apply Rle_ge; auto with real.
lra.
assert (0 <= 1 + ulp_flx x / 2 / x).
rewrite <- (Rplus_0_l 0).
apply Rplus_le_compat; auto with real.
unfold Rdiv; apply Rmult_le_pos.
apply Rmult_le_pos; auto with real; apply ulp_ge_0.
left; auto with real.
assert (0 <= 1 + ulp_flx (x * x) / 2 / (x * x)).
rewrite <- (Rplus_0_l 0).
apply Rplus_le_compat; auto with real.
unfold Rdiv; apply Rmult_le_pos.
apply Rmult_le_pos; auto with real; apply ulp_ge_0.
left; auto with real.
(* *)
apply sym_eq, Rle_antisym.
(* . *)
apply round_N_ge_midp; try assumption...
apply Rle_lt_trans with (x*(1-ulp_flx x / 2 / x)).
rewrite pred_eq_pos;[idtac|now left].
unfold pred_pos; rewrite Req_bool_false; trivial.
right; field; auto with real.
apply Rlt_le_trans with (sqrt ((x*x)*(1-ulp_flx (x*x)/2/(x*x)))).
rewrite sqrt_mult; auto with real.
rewrite sqrt_square; auto with real.
apply Rmult_lt_compat_l.
assumption.
rewrite <- (sqrt_square (1 - ulp_flx x / 2 / x)); try assumption.
apply sqrt_lt_1_alt.
split.
apply Rmult_le_pos; assumption.
apply Rmult_lt_reg_l with (2*x*x).
rewrite Rmult_assoc; apply Rmult_lt_0_compat; auto with real.
apply Rplus_lt_reg_r with (-2*x*x+2*x*ulp_flx x+ ulp_flx(x*x)).
apply Rle_lt_trans with (ulp_flx (x*x) + ulp_flx (x)*ulp_flx (x)/2).
right; field.
auto with real.
apply Rlt_le_trans with (2*x*ulp_flx x).
2: right; field; auto with real.
apply ulp_sqr_ulp_lt; auto.
apply sqrt_le_1_alt.
apply Rplus_le_reg_l with (-y+ulp_flx (x * x)/2).
apply Rle_trans with (-(y-x*x));[right; field; auto with real|idtac].
apply Rle_trans with (/2*ulp_flx (x*x));[idtac|right; field; auto with real].
apply Rle_trans with (1:=RRle_abs _).
rewrite Rabs_Ropp.
apply error_le_half_ulp...
(* . *)
apply round_N_le_midp; try assumption...
apply Rlt_le_trans with (x*(1+ulp_flx x / 2 / x)).
2: rewrite succ_eq_pos; try now left.
2: right; field; auto with real.
apply Rle_lt_trans with (sqrt ((x*x)*(1+ulp_flx (x*x)/2/(x*x)))).
apply sqrt_le_1_alt.
apply Rplus_le_reg_l with (-x*x).
apply Rle_trans with (y-x*x);[right; ring|idtac].
apply Rle_trans with (/2*ulp_flx (x*x));[idtac|right; field; auto with real].
apply Rle_trans with (1:=RRle_abs _).
apply error_le_half_ulp...
rewrite sqrt_mult; auto with real.
rewrite sqrt_square; auto with real.
apply Rmult_lt_compat_l.
assumption.
rewrite <- (sqrt_square (1 + ulp_flx x / 2 / x)); try assumption.
apply sqrt_lt_1_alt.
split; try assumption.
apply Rmult_lt_reg_l with (2*x*x).
rewrite Rmult_assoc; apply Rmult_lt_0_compat; auto with real.
apply Rplus_lt_reg_r with (-2*x*x - ulp_flx x*ulp_flx x/2).
apply Rle_lt_trans with (ulp_flx (x*x) - ulp_flx x*ulp_flx x/2).
right; field.
auto with real.
apply Rlt_le_trans with (2*x*ulp_flx x).
2: right; field; auto with real.
apply Rle_lt_trans with (ulp_flx (x * x) + ulp_flx x * ulp_flx x / 2).
2: apply ulp_sqr_ulp_lt; auto.
apply Rplus_le_compat_l.
apply Rplus_le_reg_r with (ulp_flx x * ulp_flx x / 2).
apply Rle_trans with 0;[right; ring|idtac].
apply Rle_trans with (ulp_flx x * ulp_flx x).
apply Rmult_le_pos; apply ulp_ge_0.
right; field.
Qed.

Theorem round_flx_sqr_sqrt_aux2: forall n,
 (0 <= n)%Z ->
 (2*IZR n * bpow (prec-1) * ulp_flx x * (1+bpow (1-prec)/2) < x) ->
  round_flx3(x/(x-IZR n*ulp_flx x)) <= 1.
Proof with auto with typeclass_instances.
intros n Hnp Hn.
apply round_N_le_midp...
replace 1 with (bpow 0) by reflexivity.
apply generic_format_bpow.
unfold FLX_exp; omega.
assert (0 < x - IZR n*ulp_flx x).
apply Rplus_lt_reg_r with (IZR n*ulp_flx x); ring_simplify.
apply Rle_lt_trans with (2:=Hn).
apply Rle_trans with (IZR n*(ulp_flx x*((1*1)*(1+0))));[right; ring|idtac].
apply Rle_trans with (IZR n*(ulp_flx x*(2*bpow (prec - 1)* (1 + bpow (1 - prec) / 2))));[idtac|right; ring].
apply Rmult_le_compat_l.
now apply IZR_le.
apply Rmult_le_compat_l.
unfold ulp; apply ulp_ge_0.
apply Rmult_le_compat.
rewrite Rmult_1_l; apply Rle_0_1.
rewrite Rplus_0_r; apply Rle_0_1.
apply Rmult_le_compat; try apply Rle_0_1.
auto with real.
replace 1 with (bpow 0) by reflexivity.
apply bpow_le.
omega.
apply Rplus_le_compat_l.
unfold Rdiv; apply Rmult_le_pos.
apply bpow_ge_0.
auto with real.
apply Rmult_lt_reg_r with (x - IZR n*ulp_flx x).
assumption.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
2: auto with real.
apply Rplus_lt_reg_r with (-x+IZR n*ulp_flx x + IZR n*ulp_flx x* ulp_flx 1 * / 2); ring_simplify.
apply Rmult_lt_reg_l with (2*/ulp_flx 1).
apply Rmult_lt_0_compat.
auto with real.
apply Rinv_0_lt_compat.
rewrite ulp_neq_0; try apply bpow_gt_0.
apply Rgt_not_eq, Rlt_0_1.
apply Rlt_le_trans with x.
apply Rle_lt_trans with (2:=Hn).
replace  (ulp_flx 1) with (bpow (1-prec)).
rewrite <- bpow_opp.
replace ((-(1-prec)))%Z with (prec -1)%Z by ring.
right; unfold Rdiv; ring.
replace 1 with (bpow 0) by reflexivity.
rewrite ulp_bpow.
apply f_equal; unfold FLX_exp; omega.
rewrite succ_eq_pos.
right; field.
apply Rgt_not_eq.
rewrite ulp_neq_0; try apply bpow_gt_0.
apply Rgt_not_eq, Rlt_0_1.
apply Rle_0_1.
Qed.

End Sec1.

Section Sec2.

Open Scope R_scope.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Variable choice1 : Z -> bool.
Variable choice2 : Z -> bool.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx1 :=(round beta (FLX_exp prec) (Znearest choice1)).
Notation round_flx2 :=(round beta (FLX_exp prec) (Znearest choice2)).
Notation ulp_flx :=(ulp beta (FLX_exp prec)).
Notation pred_flx := (pred beta (FLX_exp prec)).

Hypothesis pGt1: (1 < prec)%Z.

Variables x:R.
Hypothesis xPos: 0 < x.
Hypothesis Fx: format x.
Hypothesis Hx: (sqrt (IZR (radix_val beta)) * bpow (mag beta x-1) < x).

Variable k:Z.
Hypothesis kpos: (0 <= k)%Z.
Hypothesis kLe: (k < radix_val beta)%Z.
Hypothesis kradix2 : (k = 0)%Z  \/  (2 < radix_val beta)%Z.

Let y:=round_flx1(x*x).
Let z:=round_flx2(sqrt y).
Let xk :=  x-IZR k*ulp_flx x.

Lemma xkgt:  bpow (mag beta x - 1) < xk.
Proof.
unfold xk.
case kradix2.
intros V; rewrite V; simpl; ring_simplify.
apply Rle_lt_trans with (2:=Hx).
rewrite <- (Rmult_1_l (bpow (mag beta x - 1))) at 1.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (2 <= beta)%Z.
clear; destruct beta as (v, Hr); simpl.
now apply Zle_bool_imp_le.
apply IZR_le in H.
simpl in H; interval with (i_prec 30).
intros Hb.
apply Rle_lt_trans with (sqrt (IZR beta) * bpow (mag beta x - 1)
    - IZR k * ulp_flx x).
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold cexp, FLX_exp.
apply Rle_trans with (bpow (mag beta x - 1)
   *(sqrt (IZR beta) -IZR k * bpow (1-prec))).
rewrite <- (Rmult_1_r (bpow (mag beta x - 1))) at 1.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply Rplus_le_reg_l with (IZR k * bpow (1 - prec)).
apply Rle_trans with ((1-/IZR beta) * bpow (2 - prec)+1).
apply Rplus_le_compat_r.
apply Rle_trans with (((1-/IZR beta)*IZR beta) * bpow (1 - prec)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rle_trans with (IZR (beta-1)).
apply IZR_le.
omega.
rewrite minus_IZR; right.
simpl; field.
apply Rgt_not_eq, Rlt_gt.
apply IZR_lt, radix_gt_0.
right; rewrite Rmult_assoc; apply f_equal.
rewrite <- bpow_1, <- bpow_plus.
apply f_equal; ring.
ring_simplify (IZR k * bpow (1 - prec) + (sqrt (IZR beta) - IZR k * bpow (1 - prec))).
assert (H':(3 <= beta)%Z) by omega.
apply IZR_le in H'; simpl in H'.
assert (H'':(1 <= IZR beta)).
apply Rle_trans with (2:=H').
apply Rplus_le_reg_l with (-1); ring_simplify.
auto with real.
(* because p=2 is possible *)
case (Zle_lt_or_eq 3 beta).
omega.
intros H1; assert (H1':(4 <= beta)%Z) by omega.
apply IZR_le in H1'; simpl in H1'.
apply Rle_trans with (1*1 +1).
apply Rplus_le_compat_r.
apply Rmult_le_compat.
apply Rplus_le_reg_l with (/IZR beta); ring_simplify.
rewrite <- Rinv_1.
apply Rle_Rinv.
apply Rlt_0_1.
apply Rlt_le_trans with (2:=H''); auto with real.
exact H''.
apply bpow_ge_0.
apply Rplus_le_reg_l with (/IZR beta-1); ring_simplify.
left; apply Rinv_0_lt_compat.
apply Rlt_le_trans with (2:=H''); auto with real.
apply Rle_trans with (bpow 0).
apply bpow_le.
omega.
right; reflexivity.
interval with (i_prec 30).
intros Hb'.
apply Rle_trans with ((1 - / IZR beta) *1 +1).
apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
apply Rplus_le_reg_l with (/IZR beta); ring_simplify.
rewrite <- Rinv_1.
apply Rle_Rinv.
apply Rlt_0_1.
apply Rlt_le_trans with (2:=H''); auto with real.
exact H''.
apply Rle_trans with (bpow 0).
apply bpow_le.
omega.
right; reflexivity.
rewrite <- Hb'; simpl; interval.
right; ring_simplify.
apply f_equal.
apply trans_eq with (IZR k *(bpow (mag beta x - 1) * bpow (1 - prec))).
ring.
apply f_equal.
rewrite <- bpow_plus.
apply f_equal.
ring.
apply Rplus_lt_compat_r.
assumption.
Qed.

Lemma xklt: xk < bpow (mag beta x).
Proof.
apply Rle_lt_trans with x.
apply Rplus_le_reg_l with (-xk); unfold xk; ring_simplify.
apply Rmult_le_pos.
apply IZR_le, kpos.
apply ulp_ge_0.
apply Rle_lt_trans with (1:=RRle_abs _).
apply bpow_mag_gt.
Qed.

Lemma xkpos: 0  < xk.
Proof.
apply Rle_lt_trans with (2:=xkgt).
apply bpow_ge_0.
Qed.

Lemma format_xminusk: format xk.
Proof with auto with typeclass_instances.
apply generic_format_FLX.
unfold generic_format in Fx.
exists  (Float beta (Ztrunc (scaled_mantissa beta (FLX_exp prec) x) - k)
                    (cexp beta (FLX_exp prec) x)).
unfold xk; rewrite Fx at 1; unfold F2R; simpl.
rewrite minus_IZR; ring_simplify.
apply f_equal.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
apply Rmult_comm; apply f_equal.
simpl.
rewrite Z.abs_eq.
apply Z.le_lt_trans with (Ztrunc (scaled_mantissa beta (FLX_exp prec) x) - 0)%Z.
apply Zplus_le_compat_l.
omega.
rewrite Zminus_0_r.
apply lt_IZR.
apply Rmult_lt_reg_r with (bpow (cexp beta (FLX_exp prec) x)).
apply bpow_gt_0.
apply Rle_lt_trans with x.
rewrite Fx at 3.
right; unfold F2R; reflexivity.
rewrite IZR_Zpower.
rewrite <- bpow_plus.
unfold cexp, FLX_exp.
replace  (prec + (mag beta x - prec))%Z with (mag beta x+0)%Z by ring.
rewrite Zplus_0_r.
apply Rle_lt_trans with (Rabs x).
apply RRle_abs.
apply bpow_mag_gt...
omega.
apply le_IZR.
apply Rmult_le_reg_r with (bpow (cexp beta (FLX_exp prec) x)).
apply bpow_gt_0.
rewrite Rmult_0_l.
apply Rle_trans with xk.
left; apply xkpos.
right; unfold xk; rewrite Fx at 1; unfold F2R; simpl; rewrite minus_IZR; ring_simplify.
apply f_equal.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
apply Rmult_comm; apply f_equal.
Qed.

Theorem round_flx_sqr_sqrt_aux1:
  (/ 2 * bpow (mag beta x) <
      (2 * IZR k + 1) * x -
           (IZR k + / 2) * (IZR k + / 2) * bpow (mag beta x - prec)) ->
  xk <= z.
Proof with auto with typeclass_instances.
intros V.
apply round_N_ge_midp...
apply format_xminusk.
assert (Z:(mag_val beta xk (mag beta xk) = mag beta x)%Z).
apply mag_unique.
rewrite Rabs_right; try split.
left; now apply xkgt.
now apply xklt.
apply Rle_ge; left; now apply xkpos.
apply Rle_lt_trans with (x - IZR k * ulp_flx x - ulp_flx x / 2).
rewrite pred_eq_pos.
2: left; apply xkpos.
unfold pred_pos; rewrite Req_bool_false.
2: apply Rgt_not_eq, Rlt_gt.
2: apply Rle_lt_trans with (2:=xkgt).
2: right; apply f_equal, f_equal2...
replace (ulp_flx xk) with (ulp_flx x).
unfold xk; right; field.
rewrite 2!ulp_neq_0; try apply Rgt_not_eq; try assumption.
unfold cexp; now rewrite Z.
apply xkpos.
apply Rle_lt_trans with (x-(IZR k+/2)*ulp_flx x).
right; unfold Rdiv; ring.
assert (0 <= x - (IZR k + / 2) * ulp_flx x).
apply Rplus_le_reg_l with (/2*ulp_flx x).
rewrite Rplus_0_r.
apply Rle_trans with xk.
apply Rle_trans with (1*bpow (mag beta x - 1)).
apply Rmult_le_compat.
auto with real.
apply ulp_ge_0.
interval.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold cexp, FLX_exp.
apply bpow_le; omega.
rewrite Rmult_1_l.
left; apply xkgt.
unfold xk; right; ring.
rewrite <- (sqrt_square (x - (IZR k + / 2) * ulp_flx x)).
2: assumption.
apply sqrt_lt_1_alt.
split.
apply Rmult_le_pos; assumption.
apply Rlt_le_trans with (x*x - /2*bpow (2 * mag beta x  - prec)).
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold cexp, FLX_exp.
apply Rplus_lt_reg_r with (-x*x).
apply Rle_lt_trans with
  (- (bpow (mag beta x - prec)*((2*IZR k +1)*x -
            (IZR k + / 2)*  (IZR k + / 2) * bpow (mag beta x - prec)))).
right; field.
apply Rlt_le_trans with (- (bpow (mag beta x - prec)*
    (/2*bpow (mag beta x)))).
apply Ropp_lt_contravar.
apply Rmult_lt_compat_l.
apply bpow_gt_0.
exact V.
right; apply trans_eq with
  ((-/2)*(bpow (mag beta x - prec)*bpow (mag beta x))).
ring.
rewrite <- bpow_plus.
apply trans_eq with
  ((-/2)*bpow (2 * mag beta x - prec)).
apply f_equal.
apply f_equal; ring.
ring.
apply Rplus_le_reg_l with (-y+/2*bpow (2 * mag beta x  - prec)).
ring_simplify.
apply Rle_trans with (-(y-x*x)).
right; ring.
apply Rle_trans with (1:=RRle_abs _).
rewrite Rabs_Ropp.
apply Rle_trans with (1:=error_le_half_ulp _ _ _ _)...
apply Rmult_le_compat_l.
left; auto with real.
rewrite ulp_neq_0.
2: apply Rmult_integral_contrapositive_currified; now apply Rgt_not_eq.
unfold cexp, FLX_exp.
apply bpow_le.
apply Zplus_le_compat_r.
apply mag_le_bpow.
auto with real.
rewrite Rabs_mult.
replace (2*mag beta x)%Z with (mag beta x+mag beta x)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_0_lt_compat; try apply Rabs_pos; apply bpow_mag_gt.
Qed.


Theorem round_flx_sqr_sqrt_aux1_simpl:
  (/ 2 * bpow (mag beta x) + bpow (2+mag beta x - prec) <= (2 * IZR k + 1) * x)
  -> xk <= z.
Proof.
intros H; apply round_flx_sqr_sqrt_aux1.
apply Rplus_lt_reg_r with (bpow (2 + mag beta x - prec)).
apply Rle_lt_trans with (1:=H).
apply Rplus_lt_reg_r with (-(2 * IZR k + 1) * x + (IZR k + / 2) * (IZR k + / 2) * bpow (mag beta x - prec)).
apply Rle_lt_trans with (((IZR k + / 2) * (IZR k + / 2) )* bpow (mag beta x - prec)).
right; ring.
apply Rlt_le_trans with (bpow (2 + mag beta x - prec)).
2: right; ring.
unfold Zminus; rewrite <- Zplus_assoc.
rewrite bpow_plus with (e1:=2%Z).
apply Rmult_lt_compat_r.
apply bpow_gt_0.
simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r, mult_IZR.
assert (IZR k + /2 < IZR beta).
apply Rle_lt_trans with (IZR (beta -1) + /2).
apply Rplus_le_compat_r.
apply IZR_le.
omega.
rewrite minus_IZR; simpl.
apply Rplus_lt_reg_r with (-IZR beta + /2).
field_simplify.
unfold Rdiv; apply Rmult_lt_compat_r.
apply Rinv_0_lt_compat, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
exact Rlt_0_1.
assert (0 <= IZR k + / 2).
replace 0 with (0+0) by (simpl; ring); apply Rplus_le_compat.
apply IZR_le, kpos.
apply Rlt_le, Rinv_0_lt_compat, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
now apply Rmult_le_0_lt_compat.
Qed.




End Sec2.

Section Sec3.

Open Scope R_scope.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Variable choice1 : Z -> bool.
Variable choice2 : Z -> bool.
Variable choice3 : Z -> bool.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx1 :=(round beta (FLX_exp prec) (Znearest choice1)).
Notation round_flx2 :=(round beta (FLX_exp prec) (Znearest choice2)).
Notation round_flx3 :=(round beta (FLX_exp prec) (Znearest choice3)).
Notation ulp_flx :=(ulp beta (FLX_exp prec)).
Notation pred_flx := (pred beta (FLX_exp prec)).

Hypothesis pGt2: (2 < prec)%Z.

Hypothesis pGt1: (1 < prec)%Z.

Variables x:R.
Hypothesis xPos: 0 < x.
Hypothesis Fx: format x.
Hypothesis Hx: (sqrt (IZR (radix_val beta)) * bpow (mag beta x-1) < x).

Let y:=round_flx1(x*x).
Let z:=round_flx2(sqrt y).

Theorem round_flx_sqr_sqrt_exact_aux: (radix_val beta <= 4)%Z ->
    z=x.
Proof with auto with typeclass_instances.
intros Hb.
apply Rle_antisym.
(* . *)
apply round_flx_sqr_sqrt_le...
(* . *)
assert (((radix_val beta = 2)%Z \/ (radix_val beta=3)%Z) \/ (radix_val beta=4)%Z).
generalize (radix_gt_1 beta); omega.
destruct H.
(* .. radix is 2 or 3 *)
apply Rle_trans with (x - 0 * ulp_flx x).
right; simpl; ring.
apply round_flx_sqr_sqrt_aux1...
omega.
apply radix_gt_0.
apply Rlt_le_trans with (x-/4*bpow (mag beta x - prec)).
2: right; simpl; field.
apply Rle_lt_trans with (sqrt (IZR beta) * bpow (mag beta x - 1)
   - / 4 * bpow (mag beta x - prec)).
2: apply Rplus_lt_compat_r; assumption.
apply Rle_trans with ((IZR beta / 2)*bpow (mag beta x-1)).
replace (bpow (mag beta x)) with (bpow (1+(mag beta x-1))).
rewrite bpow_plus, bpow_1.
right; unfold Rdiv; ring.
apply f_equal; ring.
apply Rle_trans with ((sqrt (IZR beta) - /4* / IZR beta)
    * bpow (mag beta x-1)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
destruct H; rewrite H; simpl; interval.
rewrite Rmult_minus_distr_r.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
rewrite Rmult_assoc; apply Rmult_le_compat_l.
left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; auto with real.
apply Rle_trans with (bpow (-1+(mag beta x - 1))).
apply bpow_le; omega.
rewrite bpow_plus.
right; apply f_equal2; try reflexivity.
rewrite <- bpow_1, <- bpow_opp.
apply f_equal; reflexivity.
(* .. radix is 4 *)
assert (2 * bpow (mag beta x - 1) < x).
apply Rle_lt_trans with (2:=Hx).
right; apply f_equal2; try reflexivity.
rewrite H; simpl.
apply sym_eq, sqrt_square; auto with real.
(* ... *)
assert ((2 * bpow (mag beta x - 1)+1*bpow (mag beta x - prec)) <= x).
assert (0 < 2 * bpow (mag beta x - 1)).
apply Rmult_lt_0_compat.
auto with real.
apply bpow_gt_0.
assert (bpow (mag beta x - prec)=ulp_flx (2 * bpow (mag beta x - 1))).
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold cexp, FLX_exp.
apply f_equal.
apply f_equal2; try reflexivity.
apply sym_eq, mag_unique.
rewrite Rabs_right.
2: apply Rle_ge; left; assumption.
split.
apply Rle_trans with (1*bpow (mag beta x - 1)).
right; ring.
apply Rmult_le_compat_r.
apply bpow_ge_0.
auto with real.
apply Rlt_le_trans with (4*bpow (mag beta x - 1)).
apply Rmult_lt_compat_r.
apply bpow_gt_0.
interval.
rewrite <- H, <- bpow_1, <- bpow_plus.
right; apply f_equal; ring.
rewrite H2, Rmult_1_l.
rewrite <- succ_eq_pos;[idtac|now left].
apply succ_le_lt...
apply generic_format_FLX.
exists (Float beta 2 (mag beta x -1)).
easy.
rewrite H; apply Z.lt_le_trans with (4^1)%Z.
simpl; unfold Z.pow_pos; simpl; omega.
apply (Zpower_le (Build_radix 4 eq_refl)).
now apply Zlt_le_weak.
(* ... *)
apply Rle_trans with (x - 0 * ulp_flx x).
right; simpl; ring.
apply round_flx_sqr_sqrt_aux1...
omega.
apply radix_gt_0.
apply Rlt_le_trans with (x-/4*bpow (mag beta x - prec)).
2: right; simpl; field.
apply Rlt_le_trans with ( (2* bpow (mag beta x - 1) +  1 * bpow (mag beta x - prec))
   - / 4 * bpow (mag beta x - prec)).
2: apply Rplus_le_compat_r; assumption.
apply Rlt_le_trans with ((/2 + (1-/4)*bpow (-prec))
    * bpow (mag beta x)).
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Rle_lt_trans with (/2+0);[right; ring|idtac].
apply Rplus_lt_compat_l.
apply Rmult_lt_0_compat.
interval.
apply bpow_gt_0.
unfold Zminus; repeat rewrite bpow_plus.
replace (bpow (- (1))) with (/4).
right; field.
rewrite bpow_opp, bpow_1, H; reflexivity.
Qed.


Let k:=(Zceil (x*bpow (1-mag beta x)/(2+bpow (1-prec))) -1)%Z.

Lemma kpos: (0 <= k)%Z.
Proof.
assert (0 < x*bpow (1-mag beta x)/(2+bpow (1-prec))).
apply Fourier_util.Rlt_mult_inv_pos.
apply Rmult_lt_0_compat.
assumption.
apply bpow_gt_0.
apply Rplus_lt_0_compat.
now apply IZR_lt.
apply bpow_gt_0.
assert (0 < Zceil (x * bpow (1 - mag beta x) / (2+bpow (1-prec))))%Z.
apply lt_IZR.
apply Rlt_le_trans with (1:=H).
apply Zceil_ub.
unfold k; omega.
Qed.

Lemma kLe: (k < radix_val beta)%Z.
Proof.
cut (Zceil (x * bpow (1 - mag beta x) / (2+bpow (1-prec))) <= beta)%Z.
unfold k; omega.
apply Zceil_glb.
apply Rle_trans with (bpow 1 / 1).
unfold Rdiv; apply Rmult_le_compat.
apply Rmult_le_pos; try apply bpow_ge_0; now left.
apply Rlt_le, Rinv_0_lt_compat.
apply Rplus_lt_0_compat.
now apply IZR_lt.
apply bpow_gt_0.
apply Rle_trans with (bpow (mag beta x)*bpow (1 - mag beta x)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rle_trans with (1:=RRle_abs _).
left; apply bpow_mag_gt.
rewrite <- bpow_plus.
apply bpow_le; omega.
apply Rinv_le.
exact Rlt_0_1.
apply Rplus_le_reg_l with (-1); ring_simplify.
apply Rlt_le, Rle_lt_0_plus_1, bpow_ge_0.
rewrite bpow_1; right; field.
Qed.

Lemma kLe2: (k <= Zceil (IZR(radix_val beta)/ 2) -1)%Z.
Proof.
cut (Zceil (x * bpow (1 - mag beta x) / (2+bpow (1-prec)))
   <= Zceil (IZR(radix_val beta)/ 2))%Z.
unfold k; omega.
apply Zceil_glb.
apply Rle_trans with (bpow 1 / 2).
unfold Rdiv; apply Rmult_le_compat.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
apply Rlt_le, Rinv_0_lt_compat.
apply Rplus_lt_0_compat.
now apply IZR_lt.
apply bpow_gt_0.
apply Rle_trans with (bpow (mag beta x)*bpow (1 - mag beta x)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rle_trans with (1:=RRle_abs _).
left; apply bpow_mag_gt.
rewrite <- bpow_plus.
apply bpow_le; omega.
apply Rinv_le.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rplus_le_reg_l with (-2); ring_simplify.
apply bpow_ge_0.
rewrite bpow_1.
apply Zceil_ub.
Qed.



Lemma round_flx_sqr_sqrt_snd_deg:
  (((radix_val beta=5)%Z /\ (3 < prec)%Z) \/ (5 < radix_val beta)%Z) ->
    sqrt (IZR beta) + / 4 * bpow (3 - prec) <=
      IZR beta * (2 - bpow (1 - prec)) / (2 * (2 + bpow (1 - prec))).
Proof.
intros H; destruct H.
(* radix=5 *)
destruct H as (H1,H2).
apply Rle_trans with (sqrt (IZR beta) + / (4 *IZR beta)).
apply Rplus_le_compat_l.
rewrite (Rinv_mult_distr 4).
apply Rmult_le_compat_l.
apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rle_trans with (bpow (-(1))).
apply bpow_le; omega.
right; rewrite bpow_opp.
apply f_equal, bpow_1.
apply Rgt_not_eq, Rmult_lt_0_compat; apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rgt_not_eq, radix_pos.
apply Rle_trans with (IZR beta * (2-/(IZR beta*IZR beta)) / (2* (2 + /(IZR beta*IZR beta)))).
rewrite H1;simpl; interval.
unfold Rdiv; rewrite 2!Rmult_assoc.
apply Rmult_le_compat_l.
left; apply radix_pos.
apply Rmult_le_compat.
rewrite H1; simpl; interval.
rewrite H1; simpl; interval.
apply Rplus_le_reg_l with (-2); ring_simplify.
apply Ropp_le_contravar.
apply Rle_trans with (bpow (-(2))).
apply bpow_le; omega.
right; rewrite bpow_opp.
apply f_equal; simpl; unfold Z.pow_pos; simpl.
rewrite <- mult_IZR; apply f_equal; ring.
apply Rinv_le.
apply Rmult_lt_0_compat.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rplus_lt_0_compat.
now apply IZR_lt.
apply bpow_gt_0.
apply Rmult_le_compat_l.
apply Rlt_le,Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rplus_le_compat_l.
apply Rle_trans with (bpow (-(2))).
apply bpow_le; omega.
right; rewrite bpow_opp.
apply f_equal; simpl; unfold Z.pow_pos; simpl.
rewrite <- mult_IZR; apply f_equal; ring.
(* radix > 5 *)
apply Rle_trans with (sqrt (IZR beta) + /4*1).
apply Rplus_le_compat_l.
apply Rmult_le_compat_l.
apply Rlt_le, Rinv_0_lt_compat,  Rmult_lt_0_compat; apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rle_trans with (bpow 0).
apply bpow_le; omega.
right; reflexivity.
rewrite Rmult_1_r.
assert (6 <= IZR beta).
apply IZR_le; omega.
apply Rle_trans with (IZR beta*(12/25)).
apply Rplus_le_reg_l with (-sqrt (IZR beta)); ring_simplify.
apply Rle_trans with (IZR beta*(12/25-/sqrt(IZR beta))).
apply Rle_trans with (IZR beta*(71/1000)).
apply Rle_trans with (IZR 6*(71/1000)).
simpl; interval.
apply Rmult_le_compat_r.
interval.
apply IZR_le; omega.
apply Rmult_le_compat_l.
left; apply radix_pos.
interval with (i_prec 30).
assert (sqrt (IZR beta) <> 0).
apply Rgt_not_eq.
apply sqrt_lt_R0, radix_pos.
apply Rplus_le_reg_l with (-12/25*IZR beta).
unfold Rdiv; ring_simplify.
right; rewrite Ropp_mult_distr_l_reverse; apply f_equal.
apply Rmult_eq_reg_l with (sqrt (IZR beta)); trivial.
apply trans_eq with (IZR beta).
field; trivial.
apply sym_eq, sqrt_sqrt.
left; apply radix_pos.
unfold Rdiv; rewrite (Rmult_assoc _ (2 - bpow (1 - prec))).
apply Rmult_le_compat_l.
left; apply radix_pos.
assert (0 <= bpow (1-prec) <= 1/32).
split.
apply bpow_ge_0.
apply Rle_trans with (bpow (-(2))).
apply bpow_le.
omega.
rewrite bpow_opp.
simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r.
apply Rle_trans with (/IZR (6*6)).
apply Rinv_le.
simpl; interval.
apply IZR_le.
apply Zmult_le_compat; omega.
simpl; interval.
interval.
Qed.



Theorem round_flx_sqr_sqrt_aux: (4 < radix_val beta)%Z ->
 ((radix_val beta=5)%Z -> (3 < prec)%Z) ->
 (sqrt (IZR (radix_val beta)) * bpow (mag beta x-1) < x) ->
  round_flx3(x/z) <= 1.
Proof with auto with typeclass_instances.
intros Hbeta Hprec5 H1.
apply Rle_trans with (round_flx3 (x/(x-IZR k*ulp_flx x))).
apply round_le...
unfold Rdiv; apply Rmult_le_compat_l.
now left.
apply Rinv_le.
apply xkpos; try assumption.
apply kLe.
right; omega.
(* *)
apply round_flx_sqr_sqrt_aux1...
apply kpos.
apply kLe.
right; omega.
apply Rplus_lt_reg_l with ((IZR k + / 2) * (IZR k + / 2) * bpow (mag beta x - prec)).
apply Rlt_le_trans with ((2 * IZR k + 1) * x).
2: right; ring.
apply Rle_lt_trans with
 (/4*bpow (2+(mag beta x - prec)) + / 2 * bpow (mag beta x)).
apply Rplus_le_compat_r.
rewrite bpow_plus, <- Rmult_assoc.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (0 <= IZR k + / 2).
replace 0 with (0+0) by (simpl;ring); apply Rplus_le_compat.
apply IZR_le, kpos.
apply Rlt_le, Rinv_0_lt_compat, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
assert (IZR k + / 2 <= IZR beta / 2).
apply Rle_trans with ((IZR (Zceil (IZR beta / 2) - 1)) + /2).
apply Rplus_le_compat_r.
apply IZR_le, kLe2.
rewrite minus_IZR; simpl.
generalize (beta); intros n.
destruct (Zeven_ex n) as [m Hm].
destruct (Z.even n).
rewrite Zplus_0_r in Hm.
rewrite Hm, mult_IZR.
replace (2*IZR m / 2) with (IZR m).
rewrite Zceil_IZR.
apply Rplus_le_reg_l with (-IZR m + /2).
field_simplify.
unfold Rdiv; apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rlt_le, Rlt_0_1.
simpl; field.
rewrite Hm, plus_IZR, mult_IZR.
replace ((2*IZR m + 1)/2) with (IZR m+/2).
replace (Zceil (IZR m + / 2)) with (m+1)%Z.
rewrite plus_IZR; simpl; right; field.
apply sym_eq, Zceil_imp.
split.
ring_simplify (m+1-1)%Z.
apply Rplus_lt_reg_r with (-IZR m).
ring_simplify.
apply Rinv_0_lt_compat.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
rewrite plus_IZR; apply Rplus_le_compat_l.
apply Rplus_le_reg_l with (-/2).
simpl; field_simplify.
unfold Rdiv; apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rlt_le, Rlt_0_1.
simpl; field.
apply Rle_trans with ((IZR beta / 2)*(IZR beta / 2)).
now apply Rmult_le_compat.
simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r, mult_IZR.
right; field.
generalize kpos; unfold k; intros Y.
assert (round_flx_sqr_sqrt_snd_deg := round_flx_sqr_sqrt_snd_deg).
destruct (mag beta x) as (e,He).
simpl (mag_val beta x (Build_mag_prop beta x e He)) in *.
apply Rle_lt_trans with (bpow (e-1)*(/4*bpow (3-prec) + (IZR beta) / 2)).
rewrite (Rmult_plus_distr_l (bpow (e-1))).
apply Rplus_le_compat.
rewrite (Rmult_comm (bpow (e-1))).
rewrite Rmult_assoc; apply Rmult_le_compat_l.
apply Rlt_le, Rinv_0_lt_compat.
apply Rmult_lt_0_compat; apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
rewrite <- bpow_plus.
right; apply f_equal; ring.
unfold Zminus; rewrite bpow_plus, bpow_opp, bpow_1.
right; field.
apply Rgt_not_eq, radix_pos.
apply Rle_lt_trans with
   ((2 * (x * bpow (1 - e) / (2+bpow (1-prec)) - 1) + 1) *
    (sqrt (IZR beta) * bpow (e - 1))).
apply Rle_trans with (bpow (e - 1)*((2 * (x * bpow (1 - e) / (2+bpow (1-prec)) - 1) + 1) *
   sqrt (IZR beta))).
2: right; ring.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply Rplus_le_reg_l with (-(IZR beta/2)+sqrt (IZR beta)).
ring_simplify.
apply Rle_trans with  (IZR beta *(2-bpow(1-prec))/ (2*(2+bpow (1-prec)))).
apply round_flx_sqr_sqrt_snd_deg.
case (Zle_lt_or_eq 5 (radix_val beta)).
omega.
intros G; now right.
intros G; left; split.
now rewrite G.
apply Hprec5; now rewrite G.
apply Rle_trans with (- (IZR beta / 2) + IZR (beta)*2/(2+bpow (1-prec))).
right; field.
apply Rgt_not_eq.
generalize (bpow_gt_0 beta (1 - prec)) ; lra.
apply Rplus_le_compat_l.
apply Rle_trans with (2*sqrt (IZR beta) * ((sqrt (IZR beta) * bpow (e - 1))*bpow (1 - e) /(2+bpow (1-prec)))).
apply Rle_trans with ((sqrt (IZR beta) * sqrt (IZR beta))
   * ((bpow (e - 1) * bpow (1 - e))) *(2/(2+bpow (1-prec)))).
2: right; field.
rewrite <- bpow_plus.
rewrite sqrt_sqrt.
ring_simplify (e-1+(1-e))%Z.
simpl; unfold Rdiv; right; simpl; ring.
left; apply radix_pos.
generalize (bpow_gt_0 beta (1 - prec)) ; lra.
apply Rmult_le_compat_l.
apply Rmult_le_pos.
apply Rlt_le, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply sqrt_pos.
apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat.
generalize (bpow_gt_0 beta (1 - prec)) ; lra.
apply Rmult_le_compat_r.
apply bpow_ge_0.
now left.
apply Rle_lt_trans with
  ((2 * IZR (Zceil (x * bpow (1 - e) / (2+bpow (1-prec))) - 1) + 1)*
    (sqrt (IZR beta) * bpow (e - 1))).
apply Rmult_le_compat_r.
apply Rmult_le_pos.
apply sqrt_pos.
apply bpow_ge_0.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
apply Rlt_le, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
rewrite minus_IZR.
apply Rplus_le_compat_r.
apply Zceil_ub.
apply Rmult_lt_compat_l.
apply Rle_lt_0_plus_1.
apply Rmult_le_pos.
apply Rlt_le, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply IZR_le, Y.
assumption.
(* *)
apply round_flx_sqr_sqrt_aux2...
apply kpos.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold k, cexp, FLX_exp.
destruct (mag beta x) as (e,He).
simpl (mag_val beta x (Build_mag_prop beta x e He)) in *.
apply Rle_lt_trans with (2 * IZR (Zceil (x * bpow (1 - e) / (2+bpow (1-prec))) - 1) *
(bpow (prec - 1) * bpow (e - prec)) * (1 + bpow (1 - prec) / 2)).
right; ring.
rewrite <- bpow_plus.
apply Rlt_le_trans with (2 * (x * bpow (1 - e) / (2+bpow (1-prec))) *
bpow (prec - 1 + (e - prec)) * (1 + bpow (1 - prec) / 2)).
apply Rmult_lt_compat_r.
rewrite Rplus_comm; apply Rle_lt_0_plus_1.
unfold Rdiv; apply Rmult_le_pos.
apply bpow_ge_0.
apply Rlt_le, Rinv_0_lt_compat, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Rmult_lt_compat_l.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
generalize ((x * bpow (1 - e) / (2+bpow (1-prec)))).
intros r; case (Req_dec (IZR (Zfloor r)) r).
intros V; rewrite <- V; rewrite  Zceil_IZR.
apply IZR_lt; omega.
intros V; rewrite (Zceil_floor_neq _ V).
ring_simplify (Zfloor r+1-1)%Z.
case (Zfloor_lb r); try trivial.
intros W; now contradict W.
apply Rle_trans with (x*(bpow (1 - e)*bpow (prec - 1 + (e - prec)))*
   (2*(1 + bpow (1 - prec) / 2)/(2+bpow (1-prec)))).
right; unfold Rdiv; ring.
rewrite <- bpow_plus.
ring_simplify (1 - e + (prec - 1 + (e - prec)))%Z.
simpl (bpow 0); rewrite Rmult_1_r.
right; field.
apply Rgt_not_eq.
generalize (bpow_gt_0 beta (1 - prec)) ; lra.
Qed.

End Sec3.

Section Sec4.

Open Scope R_scope.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable choice1 : Z -> bool.
Variable choice2 : Z -> bool.
Variable choice3 : Z -> bool.
Variable choice4 : Z -> bool.
Variable choice5 : Z -> bool.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx1 :=(round beta (FLX_exp prec) (Znearest choice1)).
Notation round_flx2 :=(round beta (FLX_exp prec) (Znearest choice2)).
Notation round_flx3 :=(round beta (FLX_exp prec) (Znearest choice3)).
Notation round_flx4 :=(round beta (FLX_exp prec) (Znearest choice4)).
Notation round_flx5 :=(round beta (FLX_exp prec) (Znearest choice5)).

Hypothesis pGt1: (2 < prec)%Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.

Theorem round_flx_sqr_sqrt_exact_pos:
  forall x, 0 < x -> format x -> (radix_val beta <= 4)%Z ->
  round_flx2(sqrt (round_flx1(x*x))) = x.
Proof with auto with typeclass_instances.
intros x Hx Fx Hradix.
case (Rle_or_lt x (sqrt (IZR beta) * bpow (mag beta x - 1))).
intros H1; destruct H1.
apply round_flx_sqr_sqrt_exact_case1...
omega.
apply round_flx_sqr_sqrt_middle...
omega.
intros H1.
apply round_flx_sqr_sqrt_exact_aux...
omega.
Qed.

Theorem round_flx_sqr_sqrt_exact:
  forall x, format x -> (beta <= 4)%Z ->
  round_flx2(sqrt (round_flx1(x*x))) = Rabs x.
Proof with auto with typeclass_instances.
intros x Fx Hradix.
case (Rle_or_lt 0 x) as [H1|H1].
destruct H1.
rewrite Rabs_right;[idtac|apply Rle_ge; now left].
now apply round_flx_sqr_sqrt_exact_pos.
rewrite <- H, Rabs_R0, Rmult_0_l.
rewrite round_0...
rewrite sqrt_0.
apply round_0...
replace (x*x) with ((-x)*(-x)) by ring.
rewrite Rabs_left1; auto with real.
apply round_flx_sqr_sqrt_exact_pos; trivial.
auto with real.
now apply generic_format_opp.
Qed.

Hypothesis pradix5: (radix_val beta=5)%Z -> (3 < prec)%Z.

Theorem round_flx_sqr_sqrt_pos:
  forall x, format x -> 0 < x -> (4 < radix_val beta)%Z ->
  ((radix_val beta=5)%Z -> (3 < prec)%Z) ->
  round_flx3(x/round_flx2(sqrt (round_flx1(x*x)))) <= 1.
Proof with auto with typeclass_instances.
intros x Fx Hx Hr1 Hr2.
case (Rle_or_lt x (sqrt (IZR beta) * bpow (mag beta x - 1))); intros H1.
replace (round_flx2 (sqrt (round_flx1 (x * x)))) with x.
replace (x/x) with 1;[idtac|field; auto with real].
right; apply round_generic...
replace 1 with (bpow 0) by reflexivity.
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
destruct H1.
rewrite round_flx_sqr_sqrt_exact_case1...
omega.
rewrite round_flx_sqr_sqrt_middle...
omega.
apply round_flx_sqr_sqrt_aux...
omega.
Qed.

Theorem sqrt_sqr_pos: forall x y:R, format x -> 0 <= x ->
    0 <= round_flx3 (x / round_flx2(sqrt (round_flx4(round_flx1(x*x)+round_flx5(y*y))))) <= 1.
Proof with auto with typeclass_instances.
intros x y Fx Hx.
case Hx; intros Hx'.
assert (round_flx2 (sqrt (round_flx1 (x * x))) <=
        round_flx2 (sqrt (round_flx4 (round_flx1 (x * x) + round_flx5 (y * y))))).
apply round_le...
apply sqrt_le_1_alt.
apply round_ge_generic...
apply generic_format_round...
apply Rplus_le_reg_l with (-(round_flx1 (x*x))); ring_simplify.
rewrite <- round_0 with beta (FLX_exp prec) (Znearest choice5)...
apply round_le...
apply Rle_trans with (Rsqr y);[auto with real|right ; unfold Rsqr; ring].
assert (0 < round_flx2 (sqrt (round_flx1 (x * x)))).
destruct (mag beta x) as (e,He).
apply Rlt_le_trans with (bpow (e-1)).
apply bpow_gt_0.
apply round_ge_generic...
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
rewrite <- (sqrt_sqrt (bpow (e-1))).
2: apply bpow_ge_0.
rewrite <- sqrt_mult; try apply bpow_ge_0.
apply sqrt_le_1_alt.
rewrite <- bpow_plus.
apply round_ge_generic...
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
rewrite bpow_plus.
rewrite Rabs_right in He by now apply Rle_ge.
apply Rmult_le_compat; try apply bpow_ge_0; apply He; auto with real.
split.
(* *)
replace 0 with (round_flx3 0).
apply round_le...
unfold Rdiv; apply Rmult_le_pos; try assumption.
left; apply Rinv_0_lt_compat.
apply Rlt_le_trans with (1:=H0); exact H.
apply round_0...
(* *)
apply Rle_trans with
  (round_flx3 (x / round_flx2 (sqrt (round_flx1 (x * x))))).
apply round_le...
unfold Rdiv; apply Rmult_le_compat_l; try exact Hx.
apply Rinv_le; assumption.
case (Zle_or_lt (radix_val beta) 4); intros Hradix.
rewrite round_flx_sqr_sqrt_exact; try assumption.
rewrite Rabs_right.
2: now apply Rle_ge.
replace (x/x) with 1;[idtac|field; auto with real].
right; apply round_generic...
replace 1 with (bpow 0) by reflexivity.
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
now apply round_flx_sqr_sqrt_pos.
unfold Rdiv; rewrite <- Hx', Rmult_0_l.
rewrite round_0...
auto with real.
Qed.

End Sec4.

Section Sec5.

Open Scope R_scope.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable choice1 : Z -> bool.
Variable choice2 : Z -> bool.
Variable choice3 : Z -> bool.
Variable choice4 : Z -> bool.
Variable choice5 : Z -> bool.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx1 :=(round beta (FLX_exp prec) (Znearest choice1)).
Notation round_flx2 :=(round beta (FLX_exp prec) (Znearest choice2)).
Notation round_flx3 :=(round beta (FLX_exp prec) (Znearest choice3)).
Notation round_flx4 :=(round beta (FLX_exp prec) (Znearest choice4)).
Notation round_flx5 :=(round beta (FLX_exp prec) (Znearest choice5)).

Hypothesis pGt1: (2 < prec)%Z.

Hypothesis pradix5: (radix_val beta=5)%Z -> (3 < prec)%Z.

Lemma sqrt_sqr_except: forall x y:R, format x ->
   -1 <=  round_flx1 (x / round_flx2(sqrt (round_flx3(round_flx4(x*x)+round_flx5(y*y))))) <= 1.
Proof with auto with typeclass_instances.
intros x y Fx.
case (Rle_or_lt 0 x); intros Hx.
split.
apply Rle_trans with 0.
auto with real.
apply sqrt_sqr_pos...
unfold Prec_gt_0; omega.
apply sqrt_sqr_pos...
unfold Prec_gt_0; omega.
replace
 (x / round_flx2 (sqrt (round_flx3 (round_flx4 (x * x) + round_flx5 (y * y))))) with
 (-(((-x) / round_flx2 (sqrt (round_flx3 (round_flx4 ((-x) * (-x)) + round_flx5 (y * y))))))).
rewrite round_N_opp.
split.
apply Ropp_le_contravar.
apply sqrt_sqr_pos...
unfold Prec_gt_0; omega.
now apply generic_format_opp.
auto with real.
apply Rle_trans with (-0).
apply Ropp_le_contravar.
apply sqrt_sqr_pos...
unfold Prec_gt_0; omega.
now apply generic_format_opp.
auto with real.
rewrite Ropp_0; auto with real.
unfold Rdiv; rewrite Ropp_mult_distr_l_reverse, Ropp_involutive.
repeat apply f_equal; apply f_equal2; apply f_equal; ring.
Qed.

End Sec5.
Require Import Compute.
From Flocq Require Import Bracket Round Operations Div.


Section Sec6.

Lemma sqrt_sqr_special_case:
  let beta := Build_radix 5 (eq_refl true) in
  let prec := 3%Z in
  forall c1 c2 mx,
  let x := F2R (Float beta mx 0) in
  (0 <= mx < 125)%Z ->
  let rnd c := round beta (FLX_exp prec) (Znearest c) in
  rnd c1 (R_sqrt.sqrt (rnd c2 (x * x)%R)) = x.
Proof with auto with typeclass_instances.
intros beta prec c1 c2 mx x Hm rnd.
assert (Hprec: Prec_gt_0 prec) by easy.
unfold x, rnd.
set (r c (s : bool) m l := cond_incr (round_N (if s then negb (c (- (m + 1))%Z) else c m) l) m).
rewrite mult_correct with (choice := r c2)...
2: intros x' m l H ; now apply inbetween_int_N_sign.
rewrite sqrt_correct with (fexp := FLX_exp prec) (choice := r c1)...
2: intros x' m l H ; now apply inbetween_int_N_sign.
apply Rminus_diag_uniq.
rewrite <- F2R_minus.
set (f mx := let x := Float beta mx 0 in Fminus
  (sqrt beta (FLX_exp prec) (r c1) (mult beta (FLX_exp prec) (r c2) x x)) x).
fold (f mx).
assert (Fnum (f mx) = Z0).
clear x.
revert mx Hm.
set (g := fix g m := match m with O => true | S m => match Fnum (f (Z_of_nat m)) with Z0 => g m | _ => false end end).
assert (g 125 = true) by now vm_compute.
revert H.
clearbody f.
clear.
change 125%Z with (Z_of_nat 125).
induction (125).
intros _ mx [H1 H2].
elim (Z.lt_irrefl 0).
now apply Z.le_lt_trans with mx.
simpl g.
rewrite inj_S.
intros H mx [H1 H2].
apply Zlt_succ_le in H2.
destruct (Zle_lt_or_eq _ _ H2) as [H3|H3].
destruct (Fnum (f (Z.of_nat n))) ; try easy.
now apply IHn ; try split.
rewrite H3.
now destruct (Fnum (f (Z.of_nat n))).
destruct (f mx).
simpl in H.
rewrite H.
apply F2R_0.
Qed.

End Sec6.
Section Sec7.


Open Scope R_scope.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.

Lemma round_FLX_mult_bpow: forall rnd, Valid_rnd rnd ->
  forall x e, round beta (FLX_exp prec) rnd (x*bpow e) =
      round beta (FLX_exp prec) rnd x*bpow e.
Proof with auto with typeclass_instances.
intros rnd Hrnd x e.
case (Req_dec x 0); intros Hx.
rewrite Hx, Rmult_0_l, round_0...
ring.
unfold round, FLX_exp, scaled_mantissa, cexp.
rewrite mag_mult_bpow; try exact Hx.
unfold F2R; simpl.
rewrite Rmult_assoc; rewrite <- bpow_plus.
rewrite Rmult_assoc; rewrite <- bpow_plus.
f_equal; f_equal.
f_equal; f_equal; f_equal; ring.
ring.
Qed.


Lemma round_FLX_gt_0: forall rnd, Valid_rnd rnd -> Prec_gt_0 prec ->
  forall x, 0 < x -> 0 < round beta (FLX_exp prec) rnd x.
Proof with auto with typeclass_instances.
intros rnd Hrnd Hprec x Hx.
destruct (mag beta x) as (e,He).
apply Rlt_le_trans with (round beta (FLX_exp prec) rnd (bpow (e-1))).
rewrite round_generic...
apply bpow_gt_0.
apply generic_format_bpow.
unfold FLX_exp; unfold Prec_gt_0 in Hprec; omega.
apply round_le...
rewrite <- Rabs_right.
apply He, Rgt_not_eq; easy.
apply Rle_ge; left; easy.
Qed.

Variable choice1 : Z -> bool.
Variable choice2 : Z -> bool.
Variable choice3 : Z -> bool.
Variable choice4 : Z -> bool.
Variable choice5 : Z -> bool.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx1 :=(round beta (FLX_exp prec) (Znearest choice1)).
Notation round_flx2 :=(round beta (FLX_exp prec) (Znearest choice2)).
Notation round_flx3 :=(round beta (FLX_exp prec) (Znearest choice3)).
Notation round_flx4 :=(round beta (FLX_exp prec) (Znearest choice4)).
Notation round_flx5 :=(round beta (FLX_exp prec) (Znearest choice5)).

Hypothesis pGt1: (2 < prec)%Z.


Lemma sqrt_sqr_special_case_all:
   (radix_val beta=5)%Z -> (prec=3)%Z ->
     forall x, format x -> round_flx2 (R_sqrt.sqrt (round_flx4 (x * x))) = Rabs x.
Proof with auto with typeclass_instances.
intros H1 H2.
assert (forall x : R, 0 < x -> format x -> round_flx2 (R_sqrt.sqrt (round_flx4 (x * x))) = x).
intros x Hx Fx.
rewrite Fx.
unfold F2R; simpl.
pose (m:=(Ztrunc (scaled_mantissa beta (FLX_exp prec) x))).
pose (e := cexp beta (FLX_exp prec) x).
fold m; fold e.
replace (IZR m * bpow e * (IZR m * bpow e)) with
  ((IZR m * IZR m)*(bpow e*bpow e)) by ring.
rewrite <- bpow_plus.
rewrite round_FLX_mult_bpow...
rewrite sqrt_mult.
replace (R_sqrt.sqrt (bpow (e + e))) with (bpow e).
rewrite round_FLX_mult_bpow...
f_equal.
replace (IZR m) with (F2R (Float beta m 0)).
rewrite H2.
replace beta with {| radix_val := 5; radix_prop := eq_refl |}.
apply sqrt_sqr_special_case.
assert (0 <= scaled_mantissa beta (FLX_exp prec) x).
apply Rmult_le_pos;[now left|apply bpow_ge_0].
unfold m; rewrite Ztrunc_floor; try easy.
split.
apply Zfloor_lub; simpl; easy.
apply lt_IZR.
apply Rle_lt_trans with (1:=Zfloor_lb _).
rewrite <- (Rabs_right (scaled_mantissa _ _ _)); try (apply Rle_ge; easy).
apply Rlt_le_trans with (1 := scaled_mantissa_lt_bpow _ _ _).
unfold cexp, FLX_exp.
ring_simplify (mag beta x - (mag beta x - prec))%Z.
rewrite H2; simpl.
unfold Z.pow_pos; simpl; rewrite H1.
simpl; right; ring.
apply radix_val_inj; rewrite H1; easy.
unfold F2R; simpl; ring.
apply sym_eq, sqrt_lem_1.
apply bpow_ge_0.
apply bpow_ge_0.
now rewrite bpow_plus.
apply Rle_trans with (round_flx4 0).
right; apply sym_eq, round_0...
apply round_le...
apply FLX_exp_valid; unfold Prec_gt_0; omega.
apply Rle_trans with (1:=Rle_0_sqr (IZR m)).
right; unfold Rsqr; ring.
apply bpow_ge_0.
(* *)
intros x Fx; case (Rle_or_lt 0 x); intros Hx.
case Hx; intros Hx'.
rewrite Rabs_right; try apply Rle_ge; try assumption.
now apply H.
rewrite <- Hx', Rabs_R0, Rmult_0_l, round_0...
rewrite sqrt_0, round_0...
replace (x*x) with ((-x)*(-x)) by ring.
rewrite Rabs_left; try assumption.
apply H.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive, Ropp_0.
now apply generic_format_opp.
Qed.


Theorem sqrt_sqr: forall x y:R, format x ->
   -1 <=  round_flx1 (x / round_flx2(R_sqrt.sqrt (round_flx3(round_flx4(x*x)+round_flx5(y*y))))) <= 1.
Proof with auto with typeclass_instances.
intros x y Fx.
assert (Y:Valid_exp (FLX_exp prec)).
apply FLX_exp_valid; unfold Prec_gt_0; omega.
assert (H: ((radix_val beta=5)%Z -> (3 < prec)%Z) \/
    ((radix_val beta=5)%Z /\ (prec=3)%Z)).
case (Zle_lt_or_eq 3 prec); omega.
case H; intros H'; clear H.
now apply sqrt_sqr_except.
destruct H' as (H1,H2).
apply Rabs_le_inv.
apply abs_round_le_generic...
apply generic_format_FLX.
exists (Float beta 1 0).
unfold F2R; simpl; ring.
simpl.
apply Zpower_gt_1; omega.
case (Req_dec x 0); intros Hx.
rewrite Hx; unfold Rdiv; rewrite Rmult_0_l, Rabs_R0.
left; apply Rlt_0_1.
unfold Rdiv; rewrite Rabs_mult.
apply Rle_trans with (Rabs x * / (Rabs x)).
2: right; field.
2: apply Rgt_not_eq, Rabs_pos_lt; easy.
apply Rmult_le_compat_l.
apply Rabs_pos.
rewrite Rabs_right.
apply Rinv_le.
apply Rabs_pos_lt; easy.
apply Rle_trans with (round_flx2 (R_sqrt.sqrt (round_flx4 (x * x)))).
right; apply sym_eq.
now apply sqrt_sqr_special_case_all.
apply round_le...
apply sqrt_le_1_alt.
apply round_ge_generic...
apply generic_format_round...
apply Rplus_le_reg_r with (-round_flx4 (x * x)); ring_simplify.
replace 0 with (round_flx5 0).
apply round_le...
apply Rle_trans with (1:=Rle_0_sqr y).
right; unfold Rsqr; ring.
apply round_0...
apply Rle_ge; left.
apply Rinv_0_lt_compat.
apply round_FLX_gt_0...
unfold Prec_gt_0; omega.
apply sqrt_lt_R0.
apply round_FLX_gt_0...
unfold Prec_gt_0; omega.
apply Rle_lt_trans with (0+ round_flx5 (y * y)).
rewrite Rplus_0_l.
replace 0 with (round_flx5 0).
apply round_le...
apply Rle_trans with (1:=Rle_0_sqr y).
right; unfold Rsqr; ring.
apply round_0...
apply Rplus_lt_compat_r.
apply round_FLX_gt_0...
unfold Prec_gt_0; omega.
apply Rlt_le_trans with (Rsqr x).
now apply Rlt_0_sqr.
right; unfold Rsqr; ring.
Qed.

End Sec7.





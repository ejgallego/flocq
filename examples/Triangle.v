(**
This example is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2014-2018 Sylvie Boldo

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals Psatz.
From Flocq Require Import Core Relative Sterbenz Operations.
Require Import Interval.Interval_tactic.

Section Delta_FLX.
Open Scope R_scope.

Variables a b c:R.

Lemma Triangle_equiv_expressions: let s:=((a+b+c)/2) in
  sqrt (s*(s-a)*(s-b)*(s-c)) = /4*sqrt ((a+(b+c))*(a+(b-c))*(c+(a-b))*(c-(a-b))).
Proof.
intros s.
assert (0 <= /4).
assert (0 < 2).
apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
left; apply Rinv_0_lt_compat.
now repeat apply Rmult_lt_0_compat.
assert (0 <= /16).
apply Rle_trans with (/4*/4).
now apply Rmult_le_pos.
right; field.
replace (/4) with (sqrt (/16)).
rewrite <- sqrt_mult_alt.
apply f_equal.
unfold s; field.
exact H0.
apply sqrt_lem_1.
exact H0.
exact H.
field.
Qed.

(***********************  FLX ************************************)
Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx :=(round beta (FLX_exp prec) ZnearestE).

Hypothesis pGt1: (1 < prec)%Z.


(** Next two assumptions are proved below in radix 2 (with 7 bits) and radix 10 (with 3 digits) *)
Hypothesis prec_suff: (/2*bpow (1-prec) <= /100).
Hypothesis fourth_format: format (/4).

Hypothesis cPos: 0 <= c.
Hypothesis cLeb: c <= b.
Hypothesis bLea: b <= a.

Hypothesis isaTriangle1: a <= b+c.

Hypothesis Fa: format a.
Hypothesis Fb: format b.
Hypothesis Fc: format c.

Let t1:=round_flx (a+round_flx (b+c)).
Let t4:=round_flx (c-round_flx (a-b)).
Let t3:=round_flx (c+round_flx (a-b)).
Let t2:=round_flx (a+round_flx (b-c)).

Let M := round_flx (round_flx (round_flx (t1*t2)*t3) *t4).
Let E_M := (a+(b+c))*(a+(b-c))*(c+(a-b))*(c-(a-b)).

Let Delta := round_flx ( round_flx (/4) * round_flx (sqrt M)).
Let E_Delta :=  /4*sqrt ((a+(b+c))*(a+(b-c))*(c+(a-b))*(c-(a-b))).


Lemma FLX_pos_is_pos: forall x, 0 <= x -> 0 <= round_flx x.
Proof with auto with typeclass_instances.
intros x Hx.
apply round_pred_ge_0 with (Rnd_NE_pt beta (FLX_exp prec)) x; auto.
apply Rnd_NE_pt_monotone; auto...
apply Rnd_NG_pt_refl.
apply generic_format_0.
apply round_NE_pt...
Qed.


Lemma FLXN_le_exp: forall f1 f2:float beta, 
((Zpower beta (prec - 1) <= Zabs (Fnum f1) < Zpower beta prec)%Z) ->
((Zpower beta (prec - 1) <= Zabs (Fnum f2) < Zpower beta prec))%Z ->
0 <= F2R f1 -> F2R f1 <= F2R f2 ->  (Fexp f1 <= Fexp f2)%Z.
Proof.
intros f1 f2 H1 H2 H3 H4.
case (Zle_or_lt (Fexp f1) (Fexp f2)).
trivial.
assert (F2R f1 <= F2R f2) by assumption.
intros H5; contradict H.
apply Rlt_not_le.
unfold F2R.
apply Rlt_le_trans with (IZR(Zpower beta  prec)*bpow (Fexp f2))%R.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply IZR_lt.
apply Zle_lt_trans with (2:=proj2 H2).
rewrite Z.abs_eq.
auto with zarith.
apply le_IZR.
apply Rmult_le_reg_r with (bpow (Fexp f2)).
apply bpow_gt_0.
rewrite Rmult_0_l.
apply Rle_trans with (1:=H3).
apply H4.
rewrite IZR_Zpower, <-bpow_plus.
apply Rle_trans with (bpow ((prec-1)+Fexp f1)).
apply bpow_le.
omega.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite <- IZR_Zpower.
apply IZR_le.
apply Zle_trans with (1:=proj1 H1).
rewrite Z.abs_eq.
auto with zarith.
apply le_IZR.
apply Rmult_le_reg_r with (bpow (Fexp f1)).
apply bpow_gt_0.
rewrite Rmult_0_l.
exact H3.
omega.
omega.
Qed.





Lemma t1pos: 0 <= t1.
Proof with auto with typeclass_instances.
apply FLX_pos_is_pos.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); exact bLea.
apply FLX_pos_is_pos.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); exact cLeb.
exact cPos.
Qed.


Lemma t2pos: 0 <= t2.
Proof with auto with typeclass_instances.
apply FLX_pos_is_pos.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); exact bLea.
apply FLX_pos_is_pos.
apply Rle_0_minus.
exact cLeb.
Qed.


Lemma t3pos: 0 <= t3.
Proof with auto with typeclass_instances.
apply FLX_pos_is_pos.
apply Rplus_le_le_0_compat.
exact cPos.
apply FLX_pos_is_pos.
apply Rle_0_minus.
exact bLea.
Qed.


Lemma t4pos: 0 <= t4.
Proof with auto with typeclass_instances.
apply FLX_pos_is_pos.
apply Rle_0_minus.
apply round_le_generic...
apply Rplus_le_reg_l with b; ring_simplify.
exact isaTriangle1.
Qed.



Lemma Mpos: 0 <= M.
Proof with auto with typeclass_instances.
apply FLX_pos_is_pos.
apply Rmult_le_pos;[idtac|exact t4pos].
apply FLX_pos_is_pos.
apply Rmult_le_pos;[idtac|exact t3pos].
apply FLX_pos_is_pos.
apply Rmult_le_pos;[exact t1pos|exact t2pos].
Qed.




Lemma ab_exact: round_flx (a-b)=a-b.
Proof with auto with typeclass_instances.
apply round_generic...
apply sterbenz_aux...
lra.
Qed.

Lemma t4_exact_aux: forall (f:float beta) g,
  (Z.abs (Fnum f) < Zpower beta prec)%Z
   -> (0 <= g <= F2R f)%R 
   -> (exists n:Z, (g=IZR n*bpow (Fexp f))%R) 
   -> format g.
Proof with auto with typeclass_instances.
intros f g Hf (Hg1,Hg2) (n,Hg3).
apply generic_format_FLX.
exists (Float beta n (Fexp f)).
exact Hg3.
apply lt_IZR.
rewrite IZR_Zpower.
2: omega.
apply Rmult_lt_reg_r with (bpow (Fexp f)).
apply bpow_gt_0.
apply Rle_lt_trans with (F2R f).
apply Rle_trans with (2:=Hg2).
apply Rle_trans with (Rabs (F2R (Float beta n (Fexp f)))).
rewrite <- F2R_Zabs.
right; reflexivity.
unfold F2R; simpl.
rewrite <- Hg3.
right; apply Rabs_right.
now apply Rle_ge.
rewrite <- (Rabs_right (F2R f)).
replace (F2R f) with (F2R (Float beta (Fnum f) (Fexp f))) by reflexivity.
rewrite <- F2R_Zabs.
unfold F2R; apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite <- IZR_Zpower.
2: omega.
apply IZR_lt.
now simpl.
apply Rle_ge; apply Rle_trans with (1:=Hg1); assumption.
Qed.


Lemma t4_exact: t4=c-(a-b).
Proof with auto with typeclass_instances.
unfold t4; rewrite ab_exact.
case cPos; intros K.
apply round_generic...
apply FLXN_format_generic in Fc...
destruct Fc as [fc Hfc1 Hfc2].
apply t4_exact_aux with fc.
apply Hfc2.
now apply Rgt_not_eq.
split.
apply Rle_0_minus.
apply Rplus_le_reg_l with b; ring_simplify.
exact isaTriangle1.
rewrite <-Hfc1.
apply Rplus_le_reg_l with (-c+a); ring_simplify.
exact bLea.
apply FLXN_format_generic in Fa...
destruct Fa as [fa Hfa1 Hfa2].
apply FLXN_format_generic in Fb...
destruct Fb as [fb Hfb1 Hfb2].
exists (Fnum fc -(Fnum fa*Zpower beta (Fexp fa-Fexp fc) 
-Fnum fb*Zpower beta (Fexp fb-Fexp fc)))%Z.
rewrite Hfa1, Hfb1, Hfc1; unfold F2R; simpl.
rewrite 2!minus_IZR.
rewrite 2!mult_IZR.
rewrite 2!IZR_Zpower.
unfold Zminus; rewrite 2!bpow_plus.
rewrite bpow_opp.
field.
apply Rgt_not_eq.
apply bpow_gt_0.
assert (Fexp fc <= Fexp fb)%Z.
2: omega.
apply FLXN_le_exp.
apply Hfc2.
now apply Rgt_not_eq.
apply Hfb2.
apply Rgt_not_eq.
apply Rlt_le_trans with c; assumption.
rewrite <- Hfc1; assumption.
rewrite <- Hfc1, <-Hfb1; assumption.
assert (Fexp fc <= Fexp fa)%Z.
apply FLXN_le_exp.
apply Hfc2.
now apply Rgt_not_eq.
apply Hfa2.
apply Rgt_not_eq.
apply Rlt_le_trans with c; try assumption.
apply Rle_trans with b; assumption.
rewrite <- Hfc1; assumption.
rewrite <- Hfc1, <-Hfa1.
apply Rle_trans with b; assumption.
omega.
unfold Rminus; rewrite <-K, Rplus_0_l.
rewrite round_NE_opp.
apply f_equal.
apply ab_exact.
Qed.





Notation err x y e := (Rabs (x - y) <= e * Rabs y).
Notation eps :=(/2*bpow (1-prec)).


Lemma epsPos: 0 <= eps.
Proof.
apply Rmult_le_pos.
auto with real.
apply bpow_ge_0.
Qed.

Lemma err_aux: forall x y e1 e2, err x y e1 -> e1 <= e2 -> err x y e2.
Proof.
intros x y e1 e2 H1 H2.
apply Rle_trans with (e1*Rabs y).
exact H1.
apply Rmult_le_compat_r.
apply Rabs_pos.
exact H2.
Qed.


Lemma err_0: forall x, err x x 0.
Proof.
intros x.
replace (x-x) with 0%R by ring.
rewrite Rabs_R0; right; ring.
Qed.

Lemma err_opp: forall x y e, err x y e -> err (-x) (-y) e.
Proof.
intros x y e H.
replace (-x - (-y)) with (-(x-y)) by ring.
now rewrite 2!Rabs_Ropp.
Qed.


Lemma err_init: forall x, err (round_flx x) x eps.
Proof with auto with typeclass_instances.
intros x.
apply Rle_trans with  (/ 2 * bpow (- prec + 1) * Rabs x).
apply relative_error_N_FLX...
right; apply f_equal2; auto.
apply f_equal, f_equal; ring.
Qed.


Lemma err_add: forall x1 y1 e1 x2 y2 e2, err x1 y1 e1 -> err x2 y2 e2 -> 0 <= y1 -> 0 <= y2
  -> err (round_flx (x1+x2)) (y1+y2) (eps + (1+eps)*(Rmax e1 e2)).
Proof with auto with typeclass_instances.
intros x1 y1 e1 x2 y2 e2 H1 H2 Hy1 Hy2.
replace (round_flx (x1+x2) - (y1+y2)) with ((round_flx (x1+x2)-(x1+x2))+(x1+x2 - (y1+y2))) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (eps*Rabs (x1+x2) + Rabs (x1 + x2 - (y1 + y2))).
apply Rplus_le_compat_r.
apply err_init.
rewrite Rmult_plus_distr_r.
pattern (x1+x2) at 1; replace (x1+x2) with ((x1 + x2 - (y1 + y2))+(y1+y2)) by ring.
apply Rle_trans with (eps * Rabs (y1 + y2) + (1 + eps) * (Rabs (x1 + x2 - (y1 + y2)))).
apply Rle_trans with (eps * Rabs (x1 + x2 - (y1 + y2)) + eps *Rabs (y1 + y2) + Rabs (x1 + x2 - (y1 + y2))).
apply Rplus_le_compat_r.
rewrite <- Rmult_plus_distr_l.
apply Rmult_le_compat_l.
apply epsPos.
apply Rabs_triang.
right; ring.
apply Rplus_le_compat_l.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Fourier_util.Rle_zero_pos_plus1, epsPos.
replace (x1 + x2 - (y1 + y2)) with ((x1-y1)+(x2-y2)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (e1*Rabs y1 + e2* Rabs y2).
now apply Rplus_le_compat.
apply Rle_trans with (Rmax e1 e2*Rabs y1 + Rmax e1 e2 * Rabs y2).
apply Rplus_le_compat; apply Rmult_le_compat_r; try apply Rabs_pos.
apply Rmax_l.
apply Rmax_r.
rewrite <- Rmult_plus_distr_l.
right; apply f_equal.
repeat rewrite Rabs_right; try reflexivity; apply Rle_ge; try assumption.
now apply Rplus_le_le_0_compat.
Qed.


Lemma err_add2: forall x x2 y2 e2, err x2 y2 e2 
  -> 0 <= e2 -> 0 <= y2 <= x 
  -> err (round_flx (x+x2)) (x+y2) (eps*(1+e2)+e2/2).
Proof with auto with typeclass_instances.
intros x x2 y2 e2 H2 H (Y1,Y2).
replace (round_flx (x+x2) - (x+y2)) with ((round_flx (x+x2)-(x+x2))+(x2 - y2)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
rewrite Rmult_plus_distr_r. 
apply Rplus_le_compat.
apply Rle_trans with (eps*Rabs (x+x2)).
apply err_init.
rewrite Rmult_assoc with (r3:=Rabs (x + y2)).
apply Rmult_le_compat_l.
apply epsPos.
replace (x+x2) with ((x + y2) +(x2-y2)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
rewrite Rmult_plus_distr_r. 
rewrite Rmult_1_l.
apply Rplus_le_compat_l.
apply Rle_trans with (1:=H2).
apply Rmult_le_compat_l.
apply H.
rewrite 2!Rabs_right.
rewrite <- (Rplus_0_l y2).
apply Rplus_le_compat; auto with real.
apply Rle_trans with y2; assumption.
apply Rle_ge, Rplus_le_le_0_compat.
apply Rle_trans with y2; assumption.
assumption.
apply Rle_ge; assumption.
apply Rle_trans with (1:=H2).
unfold Rdiv; rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply H.
apply Rmult_le_reg_l with 2; auto with real.
rewrite <- Rmult_assoc, Rinv_r.
2:apply Rgt_not_eq, Rlt_gt; auto with real.
rewrite 2!Rabs_pos_eq.
lra.
lra.
easy.
Qed.




Lemma err_mult: forall x1 y1 e1 x2 y2 e2, err x1 y1 e1 -> err x2 y2 e2 
  -> err (round_flx (x1*x2)) (y1*y2) (eps+(1+eps)*(e1+e2+e1*e2)).
Proof with auto with typeclass_instances.
intros x1 y1 e1 x2 y2 e2 H1 H2.
replace (round_flx (x1 * x2) - y1*y2) with ((round_flx (x1 * x2) - x1*x2)+(x1*x2-y1*y2)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (eps*Rabs (x1*x2)+Rabs (x1 * x2 - y1 * y2)).
apply Rplus_le_compat_r.
apply err_init.
rewrite Rmult_plus_distr_r.
apply Rle_trans with (eps*Rabs (y1 * y2) + (1+eps)*Rabs (x1 * x2 - y1 * y2)).
pattern (x1*x2) at 1; replace (x1*x2) with ((x1 * x2 - (y1 * y2))+(y1*y2)) by ring.
apply Rle_trans with (eps * Rabs (x1 * x2 - y1 * y2) + eps*Rabs (y1 * y2) + Rabs (x1 * x2 - y1 * y2)).
apply Rplus_le_compat_r.
rewrite <- Rmult_plus_distr_l.
apply Rmult_le_compat_l.
apply epsPos.
apply Rabs_triang.
right; ring.
apply Rplus_le_compat_l.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Fourier_util.Rle_zero_pos_plus1, epsPos.
rewrite 2!Rmult_plus_distr_r.
replace (x1*x2-y1*y2) with ((x1-y1)*y2+(x2-y2)*y1+(x1-y1)*(x2-y2)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rplus_le_compat.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rplus_le_compat.
rewrite 2!Rabs_mult.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
apply Rabs_pos.
exact H1.
rewrite 2!Rabs_mult.
rewrite (Rmult_comm _ (Rabs y2)).
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
apply Rabs_pos.
exact H2.
apply Rle_trans with ((e1*Rabs y1)*(e2*Rabs y2)).
rewrite Rabs_mult.
apply Rmult_le_compat; try assumption; apply Rabs_pos.
rewrite Rabs_mult; right; ring.
Qed.

Lemma err_mult_exact: forall x y e r, 0 < r -> err x y e -> err (/r*x) (/r*y) e.
Proof.
intros x y e r Hr H.
assert (r <> 0).
now apply Rgt_not_eq.
apply Rmult_le_reg_l with r.
exact Hr.
rewrite <- (Rabs_right r) at 1 4.
rewrite <- Rabs_mult.
replace (r * (/ r * x - / r * y)) with (x-y) by now field.
apply Rle_trans with (1:=H).
rewrite (Rmult_comm (Rabs r) _), Rmult_assoc.
rewrite <- Rabs_mult.
replace (/r * y *r) with y by now field.
apply Rle_refl.
apply Rle_ge; now left.
Qed.





Lemma sqrt_var_maj_2: forall h : R, Rabs h <= /2 -> 
  Rabs (sqrt (1 + h) - 1) <= Rabs h / 2 + (Rabs h) * (Rabs h) / 4.
Proof.
intros h H1.
case (Rle_or_lt 0 h); intros Sh.
assert (0 <= h <= 1).
apply Rabs_le_inv in H1.
lra.
rewrite 2!Rabs_pos_eq.
interval with (i_bisect_diff h).
apply Sh.
interval.
assert (-1/2 <= h <= 0).
apply Rabs_le_inv in H1.
lra.
rewrite 2!Rabs_left.
apply Rplus_le_reg_l with (h / 2 - h * h / 4).
replace (h / 2 - h * h / 4 + - (sqrt (1 + h) - 1)) with ((-h/2) * (-1 + h / 2 + 2 / (sqrt(1 + h) + 1))).
apply Rle_trans with (-h/2 * 0%R).
2: right ; field.
apply Rmult_le_compat_l.
lra.
interval with (i_bisect_diff h).
assert (0 < (sqrt (1 + h) + 1)).
interval.
replace (sqrt (1 + h) - 1) with (h / (sqrt (1 + h) + 1)).
field.
interval.
apply Rmult_eq_reg_l with (sqrt (1 + h) + 1).
2:apply Rgt_not_eq; assumption.
apply trans_eq with h.
field.
apply Rgt_not_eq; assumption.
apply trans_eq with (Rsqr (sqrt (1 + h)) -1).
rewrite Rsqr_sqrt.
ring.
lra.
unfold Rsqr; ring.
exact Sh.
apply Rlt_minus.
rewrite <- sqrt_1 at 2.
apply sqrt_lt_1_alt.
lra.
Qed.



Lemma err_sqrt: forall x y e, 0 <= y -> e <= /2 -> err x y e 
  -> err (round_flx (sqrt x)) (sqrt y) (eps+(1+eps)*(/2*e+/4*e*e)).
Proof with auto with typeclass_instances.
intros x y e Hy He H.
replace (round_flx (sqrt x) - sqrt y) with ((round_flx (sqrt x) - sqrt x)+(sqrt x - sqrt y)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (eps*Rabs (sqrt x)+Rabs (sqrt x - sqrt y)).
apply Rplus_le_compat_r.
apply err_init.
rewrite Rmult_plus_distr_r.
apply Rle_trans with (eps*Rabs (sqrt y) + (1+eps)*Rabs (sqrt x - sqrt y)).
pattern (sqrt x) at 1; replace (sqrt x) with ((sqrt x-sqrt y)+sqrt y) by ring.
apply Rle_trans with (eps * Rabs (sqrt x - sqrt y) + eps*Rabs (sqrt y) + Rabs (sqrt x - sqrt y)).
apply Rplus_le_compat_r.
rewrite <- Rmult_plus_distr_l.
apply Rmult_le_compat_l.
apply epsPos.
apply Rabs_triang.
right; ring.
apply Rplus_le_compat_l.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Fourier_util.Rle_zero_pos_plus1, epsPos.
case (Req_dec y 0); intros Hy'.
(* . *)
replace x with 0.
rewrite Hy', sqrt_0, Rminus_0_r, Rabs_R0, Rmult_0_r.
now apply Req_le.
case (Req_dec x 0).
easy.
intros H1.
absurd (Rabs x = 0).
now apply Rabs_no_R0.
assert (Rabs x <= 0).
replace x with (x-y).
replace 0 with (e*Rabs y).
exact H.
rewrite Hy', Rabs_R0; ring.
rewrite Hy'; ring.
case H0; try easy.
intros K; contradict K.
apply Rle_not_lt, Rabs_pos.
(* . *)
replace (sqrt x - sqrt y) with (sqrt y*(sqrt (1+(x-y)/y) - 1)).
rewrite Rabs_mult, Rmult_comm.
apply Rmult_le_compat_r.
apply Rabs_pos.
assert ((Rabs ((x - y) / y) <= e)).
apply Rmult_le_reg_r with (Rabs y).
case (Rabs_pos y); [easy|intros H'; contradict H'; apply sym_not_eq; now apply Rabs_no_R0].
apply Rle_trans with (2:=H).
rewrite <- Rabs_mult; right.
apply f_equal; now field.
apply Rle_trans with (Rabs ((x - y) / y) /2 + Rabs ((x - y) / y)*Rabs ((x - y) / y)/4).
apply sqrt_var_maj_2.
apply Rle_trans with (2:=He); assumption.
apply Rplus_le_compat.
unfold Rdiv; rewrite Rmult_comm.
apply Rmult_le_compat_l; try assumption.
auto with real.
unfold Rdiv; rewrite Rmult_comm.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
left; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; auto with real.
apply Rmult_le_compat; try apply Rabs_pos; try apply H0.
rewrite Rmult_minus_distr_l, Rmult_1_r.
apply f_equal2;[idtac|reflexivity].
rewrite <- sqrt_mult.
apply f_equal.
now field.
exact Hy.
apply Rmult_le_reg_l with y.
case Hy; [easy|intros H'; contradict H'; now apply sym_not_eq].
apply Rplus_le_reg_l with (-(x-y)).
apply Rle_trans with (-(x-y)).
right; ring.
apply Rle_trans with (1:=RRle_abs _).
rewrite Rabs_Ropp.
apply Rle_trans with (1:=H).
apply Rle_trans with (1*Rabs y).
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rle_trans with (1:=He).
apply Rle_trans with (/1).
apply Interval_missing.Rle_Rinv_pos.
apply Rlt_0_1.
auto with real.
right; apply Rinv_1.
rewrite Rabs_right.
right; now field.
apply Rle_ge, Hy.
Qed.


(* Ugly *)

Lemma M_correct_aux: forall r, 0 <= r <= /100 ->
  2 * r ^ 8 + 15 * r ^ 7 + 50 * r ^ 6 + 97 * r ^ 5 + 120 * r ^ 4 +
   97 * r ^ 3 + 50 * r ^ 2 + 15 * r <= 52 * r ^ 2 + 15 * r.
Proof.
intros r (H1,H2).
case H1; intros K.
apply Rplus_le_reg_l with (-15*r - 51*r*r); ring_simplify.
apply Rmult_le_reg_l with (/(r*r)).
apply Rinv_0_lt_compat.
now apply Rmult_lt_0_compat.
apply Rle_trans with (2*r ^ 6 + 15 * r ^ 5 + 50 * r ^ 4 + 97 * r ^ 3 + 120 * r ^ 2 + 97 * r -1 ).
right; field.
now apply Rgt_not_eq.
apply Rle_trans with 1.
2: right; field.
unfold pow; rewrite Rmult_1_r.
interval_intro (/100) upper.
assert (J := conj H1 (Rle_trans _ _ _ H2 H)).
clear -J.
interval.
now apply Rgt_not_eq.
rewrite <-K.
right; ring.
Qed.


(* Note: order of multiplications does not matter *)

Lemma M_correct: err M E_M (15/2*eps+26*eps*eps).
Proof.
eapply err_aux.
apply err_mult.
apply err_mult.
apply err_mult.
(* t1 *)
eapply err_aux.
apply err_add.
apply err_0.
apply err_init.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); exact bLea.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); exact cLeb.
exact cPos.
apply Rle_trans with (2*eps+eps*eps).
rewrite Rmax_right.
right; ring.
apply epsPos.
now right.
(* t2 *)
eapply err_aux.
apply err_add2.
apply err_init.
apply epsPos.
split.
now apply Rle_0_minus.
apply Rle_trans with (2:=bLea).
apply Rle_trans with (b-0); auto with real.
apply Rplus_le_compat_l; auto with real.
apply Rle_trans with (3/2*eps+eps*eps).
right; field.
now right.
(* t3 *)
unfold t3; rewrite ab_exact.
apply err_init.
(* t4 *)
rewrite t4_exact.
apply err_0.
assert (0 <= eps).
left; apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
apply bpow_gt_0.
generalize H prec_suff; generalize eps.
clear; intros.
field_simplify.
unfold Rdiv; apply Rmult_le_compat_r.
auto with real.
apply M_correct_aux.
split; assumption.
Qed.


(* argh, would be simpler in radix 2  Delta = /4 * round_flx (sqrt M) *)


Lemma Delta_correct : (Rabs (Delta - E_Delta) <= (23/4*eps+38*eps*eps) * E_Delta).
Proof with auto with typeclass_instances.
pattern E_Delta at 2; replace E_Delta with (Rabs E_Delta).
eapply err_aux.
apply err_mult.
replace (round_flx (/ 4)) with (/4).
apply err_0.
apply sym_eq, round_generic...
apply err_sqrt.
repeat apply Rmult_le_pos.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); assumption.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); assumption.
assumption.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); assumption.
now apply Rle_0_minus.
apply Rplus_le_le_0_compat.
assumption.
now apply Rle_0_minus.
apply Rplus_le_reg_l with a; ring_simplify.
rewrite Rplus_comm; assumption.
2: apply M_correct.
apply Rle_trans with (15/2*/100+26*/100).
apply Rplus_le_compat.
apply Rmult_le_compat_l.
unfold Rdiv; apply Rmult_le_pos.
apply IZR_le; auto with zarith.
auto with real.
assumption.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply IZR_le; auto with zarith.
rewrite <- (Rmult_1_l (/100)).
apply Rmult_le_compat.
apply epsPos.
apply epsPos.
apply Rle_trans with (1:=prec_suff).
apply Rmult_le_reg_l with 100%R.
apply IZR_lt; auto with zarith.
rewrite Rinv_r.
rewrite Rmult_1_r.
apply IZR_le; auto with zarith.
apply Rgt_not_eq, Rlt_gt.
apply IZR_lt; auto with zarith.
assumption.
rewrite <- Rmult_plus_distr_r.
clear; interval.
generalize prec_suff epsPos.
cut (0 < eps).
generalize eps; clear.
intros r H0 H1 H2.
field_simplify.
apply Rmult_le_reg_r with 16.
repeat apply Rmult_lt_0_compat; auto with real.
unfold Rdiv; rewrite Rmult_assoc.
replace (/64*16) with (/4) by field.
field_simplify.
unfold Rdiv; apply Rmult_le_compat_r.
interval.
apply Rplus_le_reg_l with (-368*r - 2431*r*r); ring_simplify.
apply Rmult_le_reg_l with (/(r*r)).
apply Rinv_0_lt_compat.
now apply Rmult_lt_0_compat.
apply Rle_trans with  (10816 * r ^ 4  + 27872 * r ^ 3 + 25028 * r ^ 2  +
    9944 * r  -155).
right; field.
now apply Rgt_not_eq.
apply Rle_trans with 1.
2: right; field.
unfold pow; rewrite Rmult_1_r.
interval_intro (/100) upper.
assert (J := conj H2 (Rle_trans _ _ _ H1 H)).
clear -J.
interval.
now apply Rgt_not_eq.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
apply bpow_gt_0.
apply Rabs_right.
apply Rle_ge; apply Rmult_le_pos.
left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
apply sqrt_pos.
Qed.

Lemma Delta_correct_2 : radix_val beta=2%Z -> 
    (Rabs (Delta - E_Delta) <= (19/4*eps+33*eps*eps) * E_Delta).
Proof with auto with typeclass_instances.
intros Hradix.
replace Delta with (/ 4 * round_flx (sqrt M)).
pattern E_Delta at 2; replace E_Delta with (Rabs E_Delta).
apply err_mult_exact.
apply Rmult_lt_0_compat; auto with real.
eapply err_aux.
apply err_sqrt.
repeat apply Rmult_le_pos.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); assumption.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); assumption.
assumption.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); assumption.
now apply Rle_0_minus.
apply Rplus_le_le_0_compat.
assumption.
now apply Rle_0_minus.
apply Rplus_le_reg_l with a; ring_simplify.
rewrite Rplus_comm; assumption.
2: apply M_correct.
apply Rle_trans with (15/2*/100+26*/100).
apply Rplus_le_compat.
apply Rmult_le_compat_l.
unfold Rdiv; apply Rmult_le_pos.
apply IZR_le; auto with zarith.
auto with real.
assumption.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply IZR_le; auto with zarith.
rewrite <- (Rmult_1_l (/100)).
apply Rmult_le_compat.
apply epsPos.
apply epsPos.
apply Rle_trans with (1:=prec_suff).
apply Rmult_le_reg_l with 100%R.
apply IZR_lt; auto with zarith.
rewrite Rinv_r.
rewrite Rmult_1_r.
apply IZR_le; auto with zarith.
apply Rgt_not_eq, Rlt_gt.
apply IZR_lt; auto with zarith.
assumption.
interval.
generalize prec_suff epsPos.
cut (0 < eps).
generalize eps; clear.
intros r H0 H1 H2.
field_simplify.
apply Rmult_le_reg_r with 16.
repeat apply Rmult_lt_0_compat; auto with real.
unfold Rdiv; rewrite Rmult_assoc.
replace (/64*16) with (/4) by field.
field_simplify.
unfold Rdiv; apply Rmult_le_compat_r.
interval.
apply Rplus_le_reg_l with (-304*r - 2111*r*r); ring_simplify.
apply Rmult_le_reg_l with (/(r*r)).
apply Rinv_0_lt_compat.
now apply Rmult_lt_0_compat.
apply Rle_trans with (10816 * r ^ 3 + 17056 * r ^ 2 + 7972 * r -139).
right; field.
now apply Rgt_not_eq.
apply Rle_trans with 1.
2: right; field.
unfold pow; rewrite Rmult_1_r.
interval_intro (/100) upper.
assert (J := conj H2 (Rle_trans _ _ _ H1 H)).
clear -J.
interval.
now apply Rgt_not_eq.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
apply bpow_gt_0.
apply Rabs_right.
apply Rle_ge; apply Rmult_le_pos.
left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
apply sqrt_pos.
apply trans_eq with (round_flx (/ 4 * round_flx (sqrt M))).
apply sym_eq, round_generic...
apply generic_format_FLX.
assert (format (round_flx (sqrt M))).
apply generic_format_round...
apply FLX_format_generic in H...
destruct H as [f Hf1 Hf2].
exists (Float beta (Fnum f) (Fexp f -2)).
rewrite Hf1; unfold F2R; simpl.
unfold Zminus;rewrite bpow_plus.
replace (bpow (-(2))) with (/4).
ring.
simpl; unfold Zpower_pos;simpl.
rewrite Hradix; apply f_equal.
simpl; ring.
now simpl.
apply f_equal.
apply f_equal2.
apply sym_eq, round_generic...
reflexivity.
Qed.

End Delta_FLX.

Section Hyp_ok.

Definition radix10 := Build_radix 10 (refl_equal true).

Lemma prec_suff_2: forall prec:Z, (7 <= prec)%Z -> (/2*bpow radix2 (1-prec) <= /100)%R.
Proof.
intros p Hp.
apply Rle_trans with (/2* bpow radix2 (-6))%R.
apply Rmult_le_compat_l.
lra.
apply bpow_le.
omega.
rewrite <- (Rmult_1_l (bpow _ _)).
interval.
Qed.



Lemma prec_suff_10: forall prec:Z, (3 <= prec)%Z -> (/2*bpow radix10 (1-prec) <= /100)%R.
Proof.
intros p Hp.
apply Rle_trans with (/2* bpow radix10 (-2))%R.
apply Rmult_le_compat_l.
lra.
apply bpow_le.
omega.
rewrite bpow_exp.
change (IZR radix10) with 10%R.
interval.
Qed.

Lemma fourth_format_2: forall prec:Z, (0 < prec)%Z -> generic_format radix2 (FLX_exp prec) (/4).
Proof with auto with typeclass_instances.
intros prec Hprec.
change (/4)%R with (bpow radix2 (-2)).
apply generic_format_bpow'...
unfold FLX_exp.
omega.
Qed.

Lemma fourth_format_10: forall prec:Z, (2 <= prec)%Z -> generic_format radix10 (FLX_exp prec) (/4).
Proof with auto with typeclass_instances.
intros prec Hprec.
apply generic_format_FLX.
exists (Float radix10 25 (-2)).
change (F2R (Float radix10 25 (-2))) with (25 / 100)%R.
field.
simpl.
apply Zlt_le_trans with (10^2)%Z.
unfold Zpower, Zpower_pos; simpl; omega.
change 10%Z with (radix_val radix10).
now apply Zpower_le.
Qed.

End Hyp_ok.

Section Delta_FLT.
Open Scope R_scope.

Variables a b c:R.

Variable beta : radix.
Notation bpow e := (bpow beta e).


Variable prec emin : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.


(***********************  FLT ************************************)
Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) ZnearestE ).

Hypothesis pGt1: (1 < prec)%Z.
Hypothesis OneisNormal: (emin <= -3-prec)%Z.

(** Next two assumptions are proved below in radix 2 (with 7 bits) and radix 10 (with 3 digits) *)
Hypothesis prec_suff: (/2*bpow (1-prec) <= /100).
Hypothesis fourth_format_gen: forall e, (emin +2 <= e)%Z -> format (/4* bpow e).

Lemma fourth_format: format (/4).
Proof.
replace (/4) with (/4*bpow 0).
apply fourth_format_gen.
omega.
simpl; ring.
Qed.


Hypothesis cPos: 0 <= c.
Hypothesis cLeb: c <= b.
Hypothesis bLea: b <= a.

Hypothesis isaTriangle1: a <= b+c.

Hypothesis Fa: format a.
Hypothesis Fb: format b.
Hypothesis Fc: format c.

Let t1:=round_flt (a+round_flt (b+c)).
Let t4:=round_flt (c-round_flt (a-b)).
Let t3:=round_flt (c+round_flt (a-b)).
Let t2:=round_flt (a+round_flt (b-c)).

Let M := round_flt (round_flt (round_flt (t1*t2)*t3) *t4).
Let E_M := (a+(b+c))*(a+(b-c))*(c+(a-b))*(c-(a-b)).

Let Delta := round_flt ( round_flt (/4) * round_flt (sqrt M)).
Let E_Delta :=  /4*sqrt ((a+(b+c))*(a+(b-c))*(c+(a-b))*(c-(a-b))).

Lemma FLT_pos_is_pos: forall x, 0 <= x -> 0 <= round_flt x.
Proof with auto with typeclass_instances.
intros x Hx.
apply round_pred_ge_0 with (Rnd_NE_pt beta (FLT_exp emin prec)) x; auto.
apply Rnd_NE_pt_monotone; auto...
apply Rnd_NG_pt_refl.
apply generic_format_0.
apply round_NE_pt...
Qed.


Lemma t1pos_: 0 <= t1.
Proof with auto with typeclass_instances.
apply FLT_pos_is_pos.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); exact bLea.
apply FLT_pos_is_pos.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); exact cLeb.
exact cPos.
Qed.


Lemma t2pos_: 0 <= t2.
Proof with auto with typeclass_instances.
apply FLT_pos_is_pos.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); exact bLea.
apply FLT_pos_is_pos.
apply Rle_0_minus.
exact cLeb.
Qed.


Lemma t3pos_: 0 <= t3.
Proof with auto with typeclass_instances.
apply FLT_pos_is_pos.
apply Rplus_le_le_0_compat.
exact cPos.
apply FLT_pos_is_pos.
apply Rle_0_minus.
exact bLea.
Qed.


Lemma t4pos_: 0 <= t4.
Proof with auto with typeclass_instances.
apply FLT_pos_is_pos.
apply Rle_0_minus.
apply round_le_generic...
apply Rplus_le_reg_l with b; ring_simplify.
exact isaTriangle1.
Qed.



Lemma Mpos_: 0 <= M.
Proof with auto with typeclass_instances.
apply FLT_pos_is_pos.
apply Rmult_le_pos;[idtac|exact t4pos_].
apply FLT_pos_is_pos.
apply Rmult_le_pos;[idtac|exact t3pos_].
apply FLT_pos_is_pos.
apply Rmult_le_pos;[exact t1pos_|exact t2pos_].
Qed.




Lemma ab_exact_: round_flt (a-b)=a-b.
Proof with auto with typeclass_instances.
apply round_generic...
apply sterbenz_aux...
lra.
Qed.


Lemma t4_exact_aux_: forall (f:float beta) g,
  (Z.abs (Fnum f) < Zpower beta prec)%Z
   -> (0 <= g <= F2R f)%R 
   -> (exists n:Z, (g=IZR n*bpow (Fexp f))%R) 
   -> (emin <= Fexp f)%Z
   -> format g.
Proof with auto with typeclass_instances.
intros f g Hf (Hg1,Hg2) (n,Hg3) Y.
apply generic_format_FLT.
exists (Float beta n (Fexp f)).
exact Hg3.
apply lt_IZR.
rewrite IZR_Zpower.
2: omega.
apply Rmult_lt_reg_r with (bpow (Fexp f)).
apply bpow_gt_0.
apply Rle_lt_trans with (F2R f).
apply Rle_trans with (2:=Hg2).
apply Rle_trans with (Rabs (F2R (Float beta n (Fexp f)))).
rewrite <- F2R_Zabs.
right; reflexivity.
unfold F2R; simpl.
rewrite <- Hg3.
right; apply Rabs_right.
now apply Rle_ge.
rewrite <- (Rabs_right (F2R f)).
replace (F2R f) with (F2R (Float beta (Fnum f) (Fexp f))) by reflexivity.
rewrite <- F2R_Zabs.
unfold F2R; apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite <- IZR_Zpower.
2: omega.
apply IZR_lt.
now simpl.
apply Rle_ge; apply Rle_trans with (1:=Hg1); assumption.
assumption.
Qed.


Lemma t4_exact_: t4=c-(a-b).
Proof with auto with typeclass_instances.
unfold t4; rewrite ab_exact_.
case cPos; intros K.
apply round_generic...
assert (H:(generic_format beta (FLX_exp prec) c)).
now apply generic_format_FLX_FLT with emin.
apply FLXN_format_generic in H...
destruct H as [fc Hfc1 Hfc2].
case (Zle_or_lt emin (Fexp fc)); intros Y.
(* normal *)
apply t4_exact_aux_ with fc.
apply Hfc2.
now apply Rgt_not_eq.
split.
apply Rle_0_minus.
apply Rplus_le_reg_l with b; ring_simplify.
exact isaTriangle1.
rewrite <-Hfc1.
apply Rplus_le_reg_l with (-c+a); ring_simplify.
exact bLea.
apply generic_format_FLX_FLT in Fa.
apply FLXN_format_generic in Fa...
destruct Fa as [fa Hfa1 Hfa2].
apply generic_format_FLX_FLT in Fb.
apply FLXN_format_generic in Fb...
destruct Fb as [fb Hfb1 Hfb2].
exists (Fnum fc -(Fnum fa*Zpower beta (Fexp fa-Fexp fc) 
-Fnum fb*Zpower beta (Fexp fb-Fexp fc)))%Z. 
rewrite Hfa1, Hfb1, Hfc1; unfold F2R; simpl.
rewrite 2!minus_IZR.
rewrite 2!mult_IZR.
rewrite 2!IZR_Zpower.
unfold Zminus; rewrite 2!bpow_plus.
rewrite bpow_opp.
field.
apply Rgt_not_eq.
apply bpow_gt_0.
assert (Fexp fc <= Fexp fb)%Z.
2: omega.
apply FLXN_le_exp with prec...
apply Hfc2.
now apply Rgt_not_eq.
apply Hfb2.
apply Rgt_not_eq.
apply Rlt_le_trans with c; assumption.
rewrite <- Hfc1; assumption.
rewrite <- Hfc1, <-Hfb1; assumption.
assert (Fexp fc <= Fexp fa)%Z.
apply FLXN_le_exp with prec...
apply Hfc2.
now apply Rgt_not_eq.
apply Hfa2.
apply Rgt_not_eq.
apply Rlt_le_trans with c; try assumption.
apply Rle_trans with b; assumption.
rewrite <- Hfc1; assumption.
rewrite <- Hfc1, <-Hfa1.
apply Rle_trans with b; assumption.
omega.
assumption.
(* subnormal *)
assert (exists f:float beta, c = F2R f /\ Fexp f = emin /\ (Z.abs (Fnum f) < beta ^ prec)%Z).
apply FLT_format_generic in Fc...
destruct Fc as [ffc Hffc1 Hffc2 Hffc3].
exists (Float beta (Fnum ffc*Zpower beta (Fexp ffc-emin)) emin).
split.
rewrite Hffc1; unfold F2R; simpl.
rewrite mult_IZR, IZR_Zpower.
unfold Zminus; rewrite bpow_plus, bpow_opp.
field.
apply Rgt_not_eq.
apply bpow_gt_0.
omega.
split.
reflexivity.
simpl.
apply lt_IZR.
rewrite abs_IZR, mult_IZR, IZR_Zpower.
2: omega.
unfold Zminus; rewrite bpow_plus, <- Rmult_assoc.
replace (IZR (Fnum ffc) * bpow (Fexp ffc)) with (F2R ffc) by reflexivity.
rewrite <- Hffc1.
rewrite Hfc1; unfold F2R; rewrite Rmult_assoc, <- bpow_plus.
rewrite Rabs_mult.
apply Rle_lt_trans with (Rabs (IZR (Fnum fc)) *1).
apply Rmult_le_compat_l.
apply Rabs_pos.
rewrite Rabs_right.
2: apply Rle_ge, bpow_ge_0.
replace 1 with (bpow 0) by reflexivity.
apply bpow_le.
omega.
rewrite Rmult_1_r.
rewrite <- abs_IZR.
apply IZR_lt.
apply Hfc2.
now apply Rgt_not_eq.
destruct H as (gc,(Hgc1,(Hgc2,Hgc3))).
apply t4_exact_aux_ with gc.
assumption.
split.
apply Rle_0_minus.
apply Rplus_le_reg_l with b; ring_simplify.
exact isaTriangle1.
rewrite <-Hgc1.
apply Rplus_le_reg_l with (-c+a); ring_simplify.
exact bLea.
apply FLT_format_generic in Fa...
destruct Fa as [fa Hfa1 Hfa2 Hfa3].
apply FLT_format_generic in Fb...
destruct Fb as [fb Hfb1 Hfb2 Hfb3].
rewrite Hgc2.
exists (Fnum gc -(Fnum fa*Zpower beta (Fexp fa-emin) 
-Fnum fb*Zpower beta (Fexp fb -emin)))%Z.
rewrite Hfa1, Hfb1, Hgc1; unfold F2R; simpl.
rewrite Hgc2, 2!minus_IZR.
rewrite 2!mult_IZR.
rewrite 2!IZR_Zpower.
unfold Zminus; rewrite 2!bpow_plus.
rewrite bpow_opp.
field.
apply Rgt_not_eq.
apply bpow_gt_0.
omega.
omega.
omega.
(* *)
unfold Rminus; rewrite <-K, Rplus_0_l.
rewrite round_NE_opp.
apply f_equal.
apply ab_exact_.
Qed.


Lemma t4Let3: t4 <= t3.
Proof with auto with typeclass_instances.
apply round_le...
apply Rplus_le_compat_l.
assert (0 <= round_flt (a - b)).
rewrite ab_exact_.
now apply Rle_0_minus.
apply Rle_trans with (2:=H).
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
Qed.

Lemma t3Let2: t3 <= t2.
Proof with auto with typeclass_instances.
apply round_le...
rewrite ab_exact_.
apply Rle_trans with (a+(c-b));[right; ring|idtac].
apply Rplus_le_compat_l.
apply Rle_trans with 0%R.
now apply Rle_minus.
apply FLT_pos_is_pos.
now apply Rle_0_minus.
Qed.

Lemma t2Let1: t2 <= t1.
Proof with auto with typeclass_instances.
apply round_le...
apply Rplus_le_compat_l.
apply round_le...
apply Rplus_le_compat_l.
apply Rle_trans with (2:=cPos).
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
Qed.



Notation err x y e := (Rabs (x - y) <= e * Rabs y).
Notation eps :=(/2*bpow (1-prec)).

Lemma err_add_no_err: forall x1 x2, 
    format x1 -> format x2
  -> err (round_flt (x1+x2)) (x1+x2) eps.
Proof with auto with typeclass_instances.
intros x1 x2 Fx1 Fx2.
case (Rle_or_lt (bpow (emin+prec-1)) (Rabs (x1+x2))); intros Y.
(* . *)
replace eps with (/ 2 * Raux.bpow beta (- prec + 1)).
apply relative_error_N_FLT...
apply f_equal; apply f_equal; ring.
(* . *)
replace (round_flt (x1 + x2)) with (x1+x2).
apply err_aux with 0.
apply err_0.
apply epsPos.
apply sym_eq, round_generic...
apply generic_format_FLT.
apply FLT_format_generic in Fx1; apply FLT_format_generic in Fx2...
destruct Fx1 as [f Hf1 Hf2 Hf3].
destruct Fx2 as [g Hg1 Hg2 Hg3].
exists (Fplus f g).
now rewrite F2R_plus, Hf1, Hg1.
apply lt_IZR.
rewrite abs_IZR.
rewrite IZR_Zpower.
2: auto with zarith.
apply Rmult_lt_reg_r with (bpow (Fexp (Fplus f g))).
apply bpow_gt_0.
apply Rle_lt_trans with (Rabs (F2R (Fplus f g))).
right; unfold F2R; rewrite Rabs_mult.
apply f_equal.
apply sym_eq, Rabs_right.
apply Rle_ge, bpow_ge_0.
rewrite F2R_plus, <- Hf1, <- Hg1.
apply Rlt_le_trans with (1:=Y).
rewrite <- bpow_plus.
apply bpow_le.
assert (emin <= Fexp (Fplus f g))%Z.
rewrite Fexp_Fplus.
now apply Zmin_case.
omega.
rewrite Fexp_Fplus.
now apply Zmin_case.
Qed.


Lemma err_add_: forall x1 y1 e1 x2 y2 e2, err x1 y1 e1 -> err x2 y2 e2 -> 0 <= y1 -> 0 <= y2
  -> format x1 -> format x2
  -> err (round_flt (x1+x2)) (y1+y2) (eps + (1+eps)*(Rmax e1 e2)).
Proof with auto with typeclass_instances.
intros x1 y1 e1 x2 y2 e2 H1 H2 Hy1 Hy2 Fx1 Fx2.
replace (round_flt (x1+x2) - (y1+y2)) with ((round_flt (x1+x2)-(x1+x2))+(x1+x2 - (y1+y2))) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (eps*Rabs (x1+x2) + Rabs (x1 + x2 - (y1 + y2))).
apply Rplus_le_compat_r.
now apply err_add_no_err.
(* *)
rewrite Rmult_plus_distr_r.
pattern (x1+x2) at 1; replace (x1+x2) with ((x1 + x2 - (y1 + y2))+(y1+y2)) by ring.
apply Rle_trans with (eps * Rabs (y1 + y2) + (1 + eps) * (Rabs (x1 + x2 - (y1 + y2)))).
apply Rle_trans with (eps * Rabs (x1 + x2 - (y1 + y2)) + eps *Rabs (y1 + y2) + Rabs (x1 + x2 - (y1 + y2))).
apply Rplus_le_compat_r.
rewrite <- Rmult_plus_distr_l.
apply Rmult_le_compat_l.
apply epsPos.
apply Rabs_triang.
right; ring.
apply Rplus_le_compat_l.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Fourier_util.Rle_zero_pos_plus1, epsPos.
replace (x1 + x2 - (y1 + y2)) with ((x1-y1)+(x2-y2)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (e1*Rabs y1 + e2* Rabs y2).
now apply Rplus_le_compat.
apply Rle_trans with (Rmax e1 e2*Rabs y1 + Rmax e1 e2 * Rabs y2).
apply Rplus_le_compat; apply Rmult_le_compat_r; try apply Rabs_pos.
apply Rmax_l.
apply Rmax_r.
rewrite <- Rmult_plus_distr_l.
right; apply f_equal.
repeat rewrite Rabs_right; try reflexivity; apply Rle_ge; try assumption.
now apply Rplus_le_le_0_compat.
Qed.

Lemma err_add2_: forall x x2 y2 e2, err x2 y2 e2 
  -> format x -> format x2
  -> 0 <= e2 -> 0 <= y2 <= x 
  -> err (round_flt (x+x2)) (x+y2) (eps*(1+e2)+e2/2).
Proof with auto with typeclass_instances.
intros x x2 y2 e2 H2 Z1 Z2 H (Y1,Y2).
replace (round_flt (x+x2) - (x+y2)) with ((round_flt (x+x2)-(x+x2))+(x2 - y2)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
rewrite Rmult_plus_distr_r. 
apply Rplus_le_compat.
apply Rle_trans with (eps*Rabs (x+x2)).
now apply err_add_no_err.
rewrite Rmult_assoc with (r3:=Rabs (x + y2)).
apply Rmult_le_compat_l.
apply epsPos.
replace (x+x2) with ((x + y2) +(x2-y2)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
rewrite Rmult_plus_distr_r. 
rewrite Rmult_1_l.
apply Rplus_le_compat_l.
apply Rle_trans with (1:=H2).
apply Rmult_le_compat_l.
apply H.
rewrite 2!Rabs_right.
rewrite <- (Rplus_0_l y2).
apply Rplus_le_compat; auto with real.
apply Rle_trans with y2; assumption.
apply Rle_ge, Rplus_le_le_0_compat.
apply Rle_trans with y2; assumption.
assumption.
apply Rle_ge; assumption.
apply Rle_trans with (1:=H2).
unfold Rdiv; rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply H.
apply Rmult_le_reg_l with 2; auto with real.
rewrite <- Rmult_assoc, Rinv_r.
2: now apply IZR_neq.
rewrite 2!Rabs_pos_eq ; lra.
Qed.

Lemma err_mult_aux: forall x1 y1 e1 x2 y2 e2, format x1 -> format x2 -> err x1 y1 e1 -> err x2 y2 e2 
  -> err (round_flt (x1*x2)) (y1*y2) (eps+(1+eps)*(e1+e2+e1*e2)) 
       \/ (Rabs (round_flt (x1*x2)) <= bpow (emin+prec-1)).
Proof with auto with typeclass_instances.
intros x1 y1 e1 x2 y2 e2 Hx1 Hx2 H1 H2.
case (Rle_or_lt (Rabs (x1 * x2)) (bpow (emin + prec-1))); intros Y.
right.
rewrite <- round_NE_abs...
eapply Rnd_NE_pt_monotone with (beta:=beta) (fexp:=(FLT_exp emin prec))...
apply round_NE_pt...
replace (bpow (emin + prec - 1)) with (round_flt ((bpow (emin + prec - 1)))).
apply round_NE_pt...
apply round_generic...
apply generic_format_bpow'...
unfold FLT_exp; apply Zmax_case; omega.
exact Y.
left.
replace (round_flt (x1 * x2) - y1*y2) with ((round_flt (x1 * x2) - x1*x2)+(x1*x2-y1*y2)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (eps*Rabs (x1*x2)+Rabs (x1 * x2 - y1 * y2)).
apply Rplus_le_compat_r.
replace eps with (/ 2 * Raux.bpow beta (- prec + 1)).
apply relative_error_N_FLT...
left; exact Y.
apply f_equal; apply f_equal; ring.
rewrite Rmult_plus_distr_r.
apply Rle_trans with (eps*Rabs (y1 * y2) + (1+eps)*Rabs (x1 * x2 - y1 * y2)).
pattern (x1*x2) at 1; replace (x1*x2) with ((x1 * x2 - (y1 * y2))+(y1*y2)) by ring.
apply Rle_trans with (eps * Rabs (x1 * x2 - y1 * y2) + eps*Rabs (y1 * y2) + Rabs (x1 * x2 - y1 * y2)).
apply Rplus_le_compat_r.
rewrite <- Rmult_plus_distr_l.
apply Rmult_le_compat_l.
apply epsPos.
apply Rabs_triang.
right; ring.
apply Rplus_le_compat_l.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Fourier_util.Rle_zero_pos_plus1, epsPos.
rewrite 2!Rmult_plus_distr_r.
replace (x1*x2-y1*y2) with ((x1-y1)*y2+(x2-y2)*y1+(x1-y1)*(x2-y2)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rplus_le_compat.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rplus_le_compat.
rewrite 2!Rabs_mult.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
apply Rabs_pos.
exact H1.
rewrite 2!Rabs_mult.
rewrite (Rmult_comm _ (Rabs y2)).
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
apply Rabs_pos.
exact H2.
apply Rle_trans with ((e1*Rabs y1)*(e2*Rabs y2)).
rewrite Rabs_mult.
apply Rmult_le_compat; try assumption; apply Rabs_pos.
rewrite Rabs_mult; right; ring.
Qed.

Lemma err_mult_: forall x1 y1 e1 x2 y2 e2, format x1 -> format x2 -> err x1 y1 e1 -> err x2 y2 e2 
  -> (bpow (emin+prec-1) < Rabs (round_flt (x1*x2)))
  -> err (round_flt (x1*x2)) (y1*y2) (eps+(1+eps)*(e1+e2+e1*e2)).
Proof.
intros.
case (err_mult_aux x1  y1 e1 x2 y2 e2); try assumption.
easy.
intros Y; contradict Y.
now apply Rlt_not_le.
Qed.


Lemma err_sqrt_aux: forall x, bpow (Zceil ((IZR (emin+prec-1))/2)) < round_flt (sqrt x) -> bpow (emin+prec-1) < x.
Proof with auto with typeclass_instances.
intros x H.
case (Rle_or_lt x (bpow (emin + prec - 1))); intros H1;[idtac|easy].
contradict H.
apply Rle_not_lt.
apply round_le_generic...
apply generic_format_bpow.
unfold FLT_exp.
rewrite Zmax_l.
omega.
assert (emin + prec-1 <= Zceil (IZR (emin + prec - 1) / 2))%Z;[idtac|omega].
rewrite <- (Zceil_IZR (emin+prec-1)) at 1.
apply Zceil_le.
apply Rmult_le_reg_l with 2%R.
intuition.
apply Rplus_le_reg_l with (-IZR (emin+prec-1)).
apply Rle_trans with (IZR (emin + prec - 1));[right; ring|idtac].
apply Rle_trans with 0%R;[idtac|right;simpl;field].
apply IZR_le.
omega.
apply Rle_trans with (sqrt (bpow (emin + prec - 1))).
now apply sqrt_le_1_alt.
apply Rle_trans with (sqrt (bpow (2*Zceil (IZR (emin + prec - 1) / 2)))).
apply sqrt_le_1_alt.
apply bpow_le.
apply le_IZR.
rewrite mult_IZR.
apply Rle_trans with ( 2 * ((IZR (emin + prec - 1) / 2))).
right; field.
apply Rmult_le_compat_l.
intuition.
apply Zceil_ub.
right; apply sqrt_lem_1.
apply bpow_ge_0.
apply bpow_ge_0.
rewrite <- bpow_plus.
apply f_equal.
ring.
Qed.



Lemma err_sqrt_: forall x y e, 0 <= y -> e <= /2 -> err x y e -> 
     bpow (emin+prec-1) < round_flt (sqrt x)
  -> err (round_flt (sqrt x)) (sqrt y) (eps+(1+eps)*(/2*e+/4*e*e)).
Proof with auto with typeclass_instances.
intros x y e Hy He H Y.
replace (round_flt (sqrt x) - sqrt y) with ((round_flt (sqrt x) - sqrt x)+(sqrt x - sqrt y)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (eps*Rabs (sqrt x)+Rabs (sqrt x - sqrt y)).
apply Rplus_le_compat_r.
replace eps with (/ 2 * Raux.bpow beta (- prec + 1)).
apply relative_error_N_FLT...
rewrite Rabs_right.
2: apply Rle_ge, sqrt_pos.
case (Rle_or_lt (bpow (emin + prec - 1)) (sqrt x)); intros Y1.
assumption.
contradict Y; apply Rle_not_lt.
apply round_le_generic...
apply generic_format_bpow.
unfold FLT_exp.
replace (emin + prec - 1 + 1 - prec)%Z with emin by ring.
rewrite Zmax_l; omega.
now left.
apply f_equal; apply f_equal; ring.
rewrite Rmult_plus_distr_r.
apply Rle_trans with (eps*Rabs (sqrt y) + (1+eps)*Rabs (sqrt x - sqrt y)).
pattern (sqrt x) at 1; replace (sqrt x) with ((sqrt x-sqrt y)+sqrt y) by ring.
apply Rle_trans with (eps * Rabs (sqrt x - sqrt y) + eps*Rabs (sqrt y) + Rabs (sqrt x - sqrt y)).
apply Rplus_le_compat_r.
rewrite <- Rmult_plus_distr_l.
apply Rmult_le_compat_l.
apply epsPos.
apply Rabs_triang.
right; ring.
apply Rplus_le_compat_l.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Fourier_util.Rle_zero_pos_plus1, epsPos.
case (Req_dec y 0); intros Hy'.
(* . *)
replace x with 0.
rewrite Hy', sqrt_0, Rminus_0_r, Rabs_R0, Rmult_0_r.
now apply Req_le.
case (Req_dec x 0).
easy.
intros H1.
absurd (Rabs x = 0).
now apply Rabs_no_R0.
assert (Rabs x <= 0).
replace x with (x-y).
replace 0 with (e*Rabs y).
exact H.
rewrite Hy', Rabs_R0; ring.
rewrite Hy'; ring.
case H0; try easy.
intros K; contradict K.
apply Rle_not_lt, Rabs_pos.
(* . *)
replace (sqrt x - sqrt y) with (sqrt y*(sqrt (1+(x-y)/y) - 1)).
rewrite Rabs_mult, Rmult_comm.
apply Rmult_le_compat_r.
apply Rabs_pos.
assert ((Rabs ((x - y) / y) <= e)).
apply Rmult_le_reg_r with (Rabs y).
case (Rabs_pos y); [easy|intros H'; contradict H'; apply sym_not_eq; now apply Rabs_no_R0].
apply Rle_trans with (2:=H).
rewrite <- Rabs_mult; right.
apply f_equal; now field.
apply Rle_trans with (Rabs ((x - y) / y) /2 + Rabs ((x - y) / y)*Rabs ((x - y) / y)/4).
apply sqrt_var_maj_2.
apply Rle_trans with (2:=He); assumption.
apply Rplus_le_compat.
unfold Rdiv; rewrite Rmult_comm.
apply Rmult_le_compat_l; try assumption.
auto with real.
unfold Rdiv; rewrite Rmult_comm.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
left; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; auto with real.
apply Rmult_le_compat; try apply Rabs_pos; try apply H0.
rewrite Rmult_minus_distr_l, Rmult_1_r.
apply f_equal2;[idtac|reflexivity].
rewrite <- sqrt_mult.
apply f_equal.
now field.
exact Hy.
apply Rmult_le_reg_l with y.
case Hy; [easy|intros H'; contradict H'; now apply sym_not_eq].
apply Rplus_le_reg_l with (-(x-y)).
apply Rle_trans with (-(x-y)).
right; ring.
apply Rle_trans with (1:=RRle_abs _).
rewrite Rabs_Ropp.
apply Rle_trans with (1:=H).
apply Rle_trans with (1*Rabs y).
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rle_trans with (1:=He).
apply Rle_trans with (/1).
apply Interval_missing.Rle_Rinv_pos.
apply Rlt_0_1.
auto with real.
right; apply Rinv_1.
rewrite Rabs_right.
right; now field.
apply Rle_ge, Hy.
Qed.


Lemma subnormal_aux: forall x y, format x -> (Rabs x <= 1 -> Rabs y <= 1) -> bpow (emin+prec-1) < Rabs (round_flt (x*y)) 
   -> bpow (emin+prec-1) < Rabs x.
Proof with auto with typeclass_instances.
intros x y Fx H1 H2.
case (Rle_or_lt (Rabs x) (bpow (emin + prec - 1))); intros H3;[idtac|assumption].
contradict H2.
apply Rle_not_lt.
apply Rle_trans with (2:=H3).
assert (H4: format (round_flt (x * y))).
apply generic_format_round...
rewrite <- round_NE_abs...
apply round_le_generic...
now apply generic_format_abs.
rewrite <- (Rmult_1_r (Rabs x)), Rabs_mult.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply H1.
apply Rle_trans with (1:=H3).
apply Rle_trans with (bpow 0).
apply bpow_le.
omega.
now apply Rle_refl.
Qed.


Lemma subnormal_aux_aux: (round_flt (t1 * t2)) <= 1 -> t3 <= 1.
Proof with auto with typeclass_instances.
intros Y.
case (Rle_or_lt t1 1); intros Y1.
apply Rle_trans with (2:=Y1).
apply Rle_trans with (1:=t3Let2).
apply t2Let1.
case (Rle_or_lt t2 1); intros Y2.
apply Rle_trans with (2:=Y2).
apply t3Let2.
contradict Y.
apply Rlt_not_le.
apply Rlt_le_trans with (1:=Y1).
apply round_ge_generic...
apply generic_format_round...
rewrite <- (Rmult_1_r t1) at 1.
apply Rmult_le_compat_l.
apply t1pos_.
now left.
Qed.



Lemma subnormal_1: bpow (emin+prec-1) < M -> bpow (emin+prec-1) < Rabs (round_flt (round_flt (t1*t2)*t3)).
Proof with auto with typeclass_instances.
intros H.
apply subnormal_aux with t4.
apply generic_format_round...
rewrite 2!Rabs_right.
intros Y.
case (Rle_or_lt (round_flt (t1 * t2)) 1); intros Y1.
apply subnormal_aux_aux in Y1.
apply Rle_trans with (2:=Y1).
apply t4Let3.
case (Rle_or_lt t3 1); intros Y2.
apply Rle_trans with (2:=Y2).
apply t4Let3.
contradict Y.
apply Rlt_not_le.
apply Rlt_le_trans with (1:=Y1).
apply round_ge_generic...
apply generic_format_round...
rewrite <- (Rmult_1_r (round_flt (t1 * t2))) at 1.
apply Rmult_le_compat_l.
apply FLT_pos_is_pos.
apply Rmult_le_pos.
apply t1pos_.
apply t2pos_.
now left.
apply Rle_ge, t4pos_.
apply Rle_ge, FLT_pos_is_pos.
apply Rmult_le_pos.
apply FLT_pos_is_pos.
apply Rmult_le_pos.
apply t1pos_.
apply t2pos_.
apply t3pos_.
rewrite Rabs_right.
exact H.
apply Rle_ge, Mpos_.
Qed.


Lemma subnormal_2: bpow (emin+prec-1) < M -> bpow (emin+prec-1) < Rabs (round_flt (t1*t2)).
Proof with auto with typeclass_instances.
intros H.
apply subnormal_aux with t3.
apply generic_format_round...
rewrite 2!Rabs_right.
apply subnormal_aux_aux.
apply Rle_ge, t3pos_.
apply Rle_ge, FLT_pos_is_pos.
apply Rmult_le_pos.
apply t1pos_.
apply t2pos_.
apply subnormal_1.
exact H.
Qed.




Lemma M_correct_: bpow (emin+prec-1) < M -> err M E_M (15/2*eps+26*eps*eps).
Proof with auto with typeclass_instances.
intros Y1.
eapply err_aux.
apply err_mult_.
apply generic_format_round...
apply generic_format_round...
apply err_mult_.
apply generic_format_round...
apply generic_format_round...
apply err_mult_.
apply generic_format_round...
apply generic_format_round...
(* t1 *)
apply err_add_; try assumption.
apply err_0.
apply err_add_no_err; try assumption.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); exact bLea.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); exact cLeb.
exact cPos.
apply generic_format_round...
(* t2 *)
apply err_add2_; try assumption.
apply err_add_no_err; try assumption.
now apply generic_format_opp...
apply generic_format_round...
apply epsPos.
split.
now apply Rle_0_minus.
apply Rle_trans with (2:=bLea).
apply Rle_trans with (b-0); auto with real.
apply Rplus_le_compat_l; auto with real.
now apply subnormal_2.
(* t3 *)
unfold t3; rewrite ab_exact_.
apply err_add_no_err; try assumption.
rewrite <- ab_exact_.
apply generic_format_round...
now apply subnormal_1.
(* t4 *)
rewrite t4_exact_.
apply err_0.
rewrite Rabs_right.
exact Y1.
apply Rle_ge, Mpos_.
(* Ugly... *)
generalize prec_suff (epsPos beta prec).
cut (0 < eps).
generalize eps; clear.
intros r H0 H1 H2.
rewrite Rmax_right;[idtac|assumption].
field_simplify.
unfold Rdiv; apply Rmult_le_compat_r.
auto with real.
apply Rplus_le_reg_l with (-15*r - 51*r*r); ring_simplify.
apply Rmult_le_reg_l with (/(r*r)).
apply Rinv_0_lt_compat.
now apply Rmult_lt_0_compat.
apply Rle_trans with (2*r ^ 6 + 15 * r ^ 5 + 50 * r ^ 4 + 97 * r ^ 3 + 120 * r ^ 2 + 97 * r -1 ).
right; field.
now apply Rgt_not_eq.
apply Rle_trans with 1.
2: right; field.
unfold pow; rewrite Rmult_1_r.
interval_intro (/100) upper.
assert (J := conj H2 (Rle_trans _ _ _ H1 H)).
clear -J.
interval.
now apply Rgt_not_eq.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
apply bpow_gt_0.
Qed.

(* argh, would be simpler in radix 2  Delta = /4 * round_flx (sqrt M) *)


Lemma Delta_correct_ : 
  /4 * bpow (Zceil ((IZR (emin+prec-1))/2)) < Delta  ->
   (Rabs (Delta - E_Delta) <= (23/4*eps+38*eps*eps) * E_Delta).
Proof with auto with typeclass_instances.
intros Y.
assert (bpow (Zceil (IZR (emin + prec - 1) / 2)) < round_flt (sqrt M)).
case (Rle_or_lt (round_flt (sqrt M)) (bpow (Zceil (IZR (emin + prec - 1) / 2)))); intros Y1.
2: easy.
contradict Y; apply Rle_not_lt.
apply round_le_generic...
apply fourth_format_gen.
apply le_IZR.
apply Rle_trans with (2:=Zceil_ub _).
apply Rmult_le_reg_r with 2%R.
intuition.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite <- mult_IZR.
apply IZR_le.
omega.
apply Rgt_not_eq; intuition.
replace (round_flt (/ 4)) with (/4).
apply Rmult_le_compat_l.
left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; intuition.
exact Y1.
apply sym_eq, round_generic...
apply fourth_format.
pattern E_Delta at 2; replace E_Delta with (Rabs E_Delta).
eapply err_aux.
apply err_mult_.
apply generic_format_round...
apply generic_format_round...
replace (round_flt (/ 4)) with (/4).
apply err_0.
apply sym_eq, round_generic...
apply fourth_format.
apply err_sqrt_.
repeat apply Rmult_le_pos.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); assumption.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); assumption.
assumption.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); assumption.
now apply Rle_0_minus.
apply Rplus_le_le_0_compat.
assumption.
now apply Rle_0_minus.
apply Rplus_le_reg_l with a; ring_simplify.
rewrite Rplus_comm; assumption.
instantiate (1:=(15/2*eps+26*eps*eps)).
generalize prec_suff (epsPos beta prec).
generalize eps; clear.
intros r H1 H2; interval_intro (/100) upper.
assert (J := conj H2 (Rle_trans _ _ _ H1 H)).
interval.
apply M_correct_.
apply err_sqrt_aux.
exact H.
apply Rle_lt_trans with (2:=H).
apply bpow_le.
rewrite <- (Zceil_IZR (emin+prec-1)) at 1.
apply Zceil_le.
apply Rmult_le_reg_l with 2%R.
intuition.
apply Rplus_le_reg_l with (-IZR (emin+prec-1)).
apply Rle_trans with (IZR (emin + prec - 1));[right; ring|idtac].
apply Rle_trans with 0%R;[idtac|right;simpl;field].
apply IZR_le.
omega.
rewrite Rabs_right.
apply Rle_lt_trans with (2:=Y).
apply Rmult_le_reg_l with 4.
apply Rmult_lt_0_compat; intuition.
rewrite <- Rmult_assoc, Rinv_r.
rewrite Rmult_1_l.
apply Rle_trans with (bpow (2+(emin + prec - 1))).
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rle_trans with (IZR (radix_val beta)*IZR (radix_val beta)).
apply (Rmult_le_compat 2 _ 2); try apply IZR_le; try easy; clear.
apply Zle_bool_imp_le; now destruct beta.
apply Zle_bool_imp_le; now destruct beta.
right; simpl.
unfold Zpower_pos; simpl.
now rewrite mult_IZR, Zmult_1_r.
apply bpow_le.
apply le_IZR.
apply Rle_trans with (2:=Zceil_ub _).
apply Rmult_le_reg_r with 2%R.
intuition.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite <- mult_IZR.
apply IZR_le.
omega.
apply Rgt_not_eq.
intuition.
apply Rgt_not_eq.
apply Rmult_lt_0_compat; intuition.
apply Rle_ge; apply FLT_pos_is_pos.
apply Rmult_le_pos.
apply FLT_pos_is_pos.
left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
apply FLT_pos_is_pos.
apply sqrt_pos.
(* *)
generalize prec_suff (epsPos beta prec).
cut (0 < eps).
generalize eps; clear.
intros r H0 H1 H2.
field_simplify.
apply Rmult_le_reg_r with 16.
repeat apply Rmult_lt_0_compat; auto with real.
unfold Rdiv; rewrite Rmult_assoc.
replace (/64*16) with (/4) by field.
field_simplify.
unfold Rdiv; apply Rmult_le_compat_r.
interval.
apply Rplus_le_reg_l with (-368*r - 2431*r*r); ring_simplify.
apply Rmult_le_reg_l with (/(r*r)).
apply Rinv_0_lt_compat.
now apply Rmult_lt_0_compat.
apply Rle_trans with  (10816 * r ^ 4  + 27872 * r ^ 3 + 25028 * r ^ 2  +
    9944 * r  -155).
right; field.
now apply Rgt_not_eq.
apply Rle_trans with 1.
2: right; field.
unfold pow; rewrite Rmult_1_r.
interval_intro (/100) upper.
assert (J := conj H2 (Rle_trans _ _ _ H1 H)).
clear -J.
interval.
now apply Rgt_not_eq.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
apply bpow_gt_0.
apply Rabs_right.
apply Rle_ge; apply Rmult_le_pos.
left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
apply sqrt_pos.
Qed.


Lemma Delta_correct_2_ : radix_val beta=2%Z -> 
  bpow (Zceil ((IZR (emin+prec-1))/2) -2) < Delta  ->
  (Rabs (Delta - E_Delta) <= (19/4*eps+33*eps*eps) * E_Delta).
Proof with auto with typeclass_instances.
intros Hradix Y.
assert (bpow (Zceil (IZR (emin + prec - 1) / 2)) < round_flt (sqrt M)).
case (Rle_or_lt (round_flt (sqrt M)) (bpow (Zceil (IZR (emin + prec - 1) / 2)))); intros Y1.
2: easy.
contradict Y; apply Rle_not_lt.
apply round_le_generic...
apply generic_format_bpow.
unfold FLT_exp.
rewrite Zmax_l.
omega.
assert (emin+prec+1 <= Zceil (IZR (emin + prec - 1) / 2))%Z;[idtac|omega].
apply le_IZR.
apply Rle_trans with (2:=Zceil_ub _).
apply Rmult_le_reg_r with 2%R.
intuition.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite <- mult_IZR.
apply IZR_le.
omega.
apply Rgt_not_eq; intuition.
replace (round_flt (/ 4)) with (/4).
unfold Zminus; rewrite Rmult_comm, bpow_plus.
replace (bpow (-(2))) with (/4).
apply Rmult_le_compat_r.
left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; intuition.
exact Y1.
simpl; apply f_equal; unfold Zpower_pos; simpl.
rewrite Hradix; simpl; ring.
apply sym_eq, round_generic...
apply fourth_format.
replace Delta with (/ 4 * round_flt (sqrt M)).
pattern E_Delta at 2; replace E_Delta with (Rabs E_Delta).
apply err_mult_exact.
apply Rmult_lt_0_compat; auto with real.
eapply err_aux.
apply err_sqrt_.
repeat apply Rmult_le_pos.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); assumption.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); assumption.
assumption.
apply Rplus_le_le_0_compat.
apply Rle_trans with (1:=cPos); apply Rle_trans with (1:=cLeb); assumption.
now apply Rle_0_minus.
apply Rplus_le_le_0_compat.
assumption.
now apply Rle_0_minus.
apply Rplus_le_reg_l with a; ring_simplify.
rewrite Rplus_comm; assumption.
2: apply M_correct_.
generalize prec_suff (epsPos beta prec).
generalize eps; clear.
intros r H1 H2; interval_intro (/100) upper.
assert (J := conj H2 (Rle_trans _ _ _ H1 H)).
interval.
apply err_sqrt_aux.
exact H.
apply Rle_lt_trans with (2:=H).
apply bpow_le.
rewrite <- (Zceil_IZR (emin+prec-1)) at 1.
apply Zceil_le.
apply Rmult_le_reg_l with 2%R.
intuition.
apply Rplus_le_reg_l with (-IZR (emin+prec-1)).
apply Rle_trans with (IZR (emin + prec - 1));[right; ring|idtac].
apply Rle_trans with 0%R;[idtac|right;simpl;field].
apply IZR_le.
omega.
(* *)
generalize prec_suff (epsPos beta prec).
cut (0 < eps).
generalize eps; clear.
intros r H0 H1 H2.
field_simplify.
apply Rmult_le_reg_r with 16.
repeat apply Rmult_lt_0_compat; auto with real.
unfold Rdiv; rewrite Rmult_assoc.
replace (/64*16) with (/4) by field.
field_simplify.
unfold Rdiv; apply Rmult_le_compat_r.
interval.
apply Rplus_le_reg_l with (-304*r - 2111*r*r); ring_simplify.
apply Rmult_le_reg_l with (/(r*r)).
apply Rinv_0_lt_compat.
now apply Rmult_lt_0_compat.
apply Rle_trans with (10816 * r ^ 3 + 17056 * r ^ 2 + 7972 * r -139).
right; field.
now apply Rgt_not_eq.
apply Rle_trans with 1.
2: right; field.
unfold pow; rewrite Rmult_1_r.
interval_intro (/100) upper.
assert (J := conj H2 (Rle_trans _ _ _ H1 H)).
clear -J.
interval.
now apply Rgt_not_eq.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
apply bpow_gt_0.
apply Rabs_right.
apply Rle_ge; apply Rmult_le_pos.
left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
apply sqrt_pos.
apply trans_eq with (round_flt (/ 4 * round_flt (sqrt M))).
apply sym_eq, round_generic...
apply generic_format_FLT.
assert (format (round_flt (sqrt M))).
apply generic_format_round...
apply FLT_format_generic in H0...
destruct H0 as [f Hf1 Hf2 Hf3].
exists (Float beta (Fnum f) (Fexp f -2)).
rewrite Hf1; unfold F2R; simpl.
unfold Zminus;rewrite bpow_plus.
replace (bpow (-(2))) with (/4).
ring.
simpl; unfold Zpower_pos;simpl.
rewrite Hradix; apply f_equal.
simpl; ring.
now simpl.
simpl.
assert (emin+1+prec < prec+Fexp f)%Z;[idtac|omega].
apply lt_bpow with beta.
apply Rle_lt_trans with  (bpow (Zceil (IZR (emin + prec - 1) / 2))).
apply bpow_le.
apply le_IZR.
apply Rle_trans with (2:=Zceil_ub _).
apply Rmult_le_reg_r with 2%R.
intuition.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite <- mult_IZR.
apply IZR_le.
omega.
apply Rgt_not_eq; intuition.
apply Rlt_le_trans with (1:=H).
rewrite Hf1.
apply Rle_trans with (1:=RRle_abs _).
rewrite <- F2R_abs.
unfold F2R; rewrite bpow_plus.
replace (Fexp (Fabs f)) with (Fexp f).
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite <- IZR_Zpower.
left; apply IZR_lt.
replace (Fnum (Fabs f)) with (Zabs (Fnum f)).
assumption.
destruct f; unfold Fabs; reflexivity.
omega.
destruct f; unfold Fabs; reflexivity.
apply f_equal.
apply f_equal2.
apply sym_eq, round_generic...
apply fourth_format.
reflexivity.
Qed.

End Delta_FLT.

Section Hyp_ok_.


Lemma fourth_format_gen_2: forall prec emin e:Z, (0 < prec)%Z -> (emin +2 <= e)%Z
  -> generic_format radix2 (FLT_exp emin prec) (/4*bpow radix2 e).
Proof with auto with typeclass_instances.
intros prec emin e Hprec H.
replace (/4)%R with (bpow radix2 (-2)).
rewrite <- bpow_plus.
apply generic_format_bpow...
unfold FLT_exp.
apply Zmax_case.
omega.
omega.
reflexivity.
Qed.

Lemma fourth_format_gen_10: forall prec emin e:Z, (2 <= prec)%Z -> (emin +2 <= e)%Z
   -> generic_format radix10 (FLT_exp emin prec) (/4*bpow radix10 e).
Proof with auto with typeclass_instances.
intros prec emin e Hprec H.
apply generic_format_FLT.
exists (Float radix10 25 (e-2)).
unfold F2R; simpl.
unfold Zminus; rewrite bpow_plus.
change (bpow radix10 (-(2))) with (/100)%R.
field.
simpl.
apply Zlt_le_trans with (10^2)%Z.
unfold Zpower, Zpower_pos; simpl; omega.
change 10%Z with (radix_val radix10).
now apply Zpower_le.
simpl.
omega.
Qed.

End Hyp_ok_.

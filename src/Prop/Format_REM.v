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

(** * Error of the integer remainder is representable. *)
Require Import Core Operations Sterbenz.

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
    format (x- Z2R (rnd (x/y))*y).
Proof with auto with typeclass_instances.
intros x y Fx Fy Hx Hy rnd_small.
pose (n:=rnd (x / y)).
assert (Hn:(Z2R n = round beta (FIX_exp 0) rnd (x/y))%R).
unfold round, FIX_exp, cexp, scaled_mantissa, F2R; simpl.
now rewrite 2!Rmult_1_r.
assert (H:(0 <= n)%Z).
apply le_Z2R; rewrite Hn; simpl.
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
assert (H0:(x-Z2R n *y = F2R (Float beta (mx*beta^(ex-ey) - n*my) ey))%R).
unfold Rminus; rewrite Rplus_comm.
replace (Z2R n) with (F2R (Float beta n 0)).
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
rewrite H0; apply F2R_neq_0_compat; easy.
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
replace (/y * (x - Z2R n *y))%R with (-(Z2R n - x/y))%R.
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
apply le_Z2R; simpl; rewrite Hn.
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
left; apply mag_lt_pos with beta; easy.
(* n = 1 -> Sterbenz + rnd_small *)
intros Hn'; fold n; rewrite <- Hn'.
rewrite Rmult_1_l.
case Hx; intros Hx'.
assert (J:(0 < x/y)%R).
apply Fourier_util.Rlt_mult_inv_pos; assumption.
apply sterbenz...
assert (H0:(Rabs (1  - x/y) < 1)%R).
change 1%R with (Z2R 1) at 1.
rewrite Hn', Hn.
apply Rlt_le_trans with (ulp beta (FIX_exp 0) (round beta (FIX_exp 0) rnd (x / y)))%R.
apply error_lt_ulp_round...
now apply Rgt_not_eq.
rewrite ulp_FIX.
rewrite <- Hn'.
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

Theorem format_REM: forall rnd : R -> Z, Valid_rnd rnd ->
  forall (x y : R),
   ~ (Zabs (rnd (x/y)%R) = 1%Z /\ (Rabs (x/y) < /2)%R) ->
   (format x) -> (format y) ->
    format (x-Z2R (rnd (x/y)%R)*y).
Proof with auto with typeclass_instances.
(* assume 0 < y *)
assert (H: forall rnd : R -> Z, Valid_rnd rnd ->
  forall (x y : R),
     ~ (Zabs (rnd (x/y)%R) = 1%Z /\ (Rabs (x/y) < /2)%R) ->
  (format x) -> (format y) -> (0 < y)%R ->
    format (x-Z2R (rnd (x/y)%R)*y)).
intros rnd valid_rnd x y Hrnd Fx Fy Hy.
case (Rle_or_lt 0 x); intros Hx.
apply format_REM_aux; try easy.
intros (K1,K2); apply Hrnd; split.
rewrite K1; easy.
rewrite Rabs_right; try easy.
apply Rle_ge; left; apply K2.
replace (x-(Z2R (rnd (x/y)))*y)%R with
   (-((-x)-(Z2R ((Zrnd_opp rnd)
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
apply trans_eq with (x-((-Z2R ((Zrnd_opp rnd) (- x / y)))*y))%R.
ring.
apply Rplus_eq_compat_l; f_equal; f_equal.
unfold Zrnd_opp; rewrite Z2R_opp, Ropp_involutive.
f_equal; f_equal; unfold Rdiv; ring.
(* *)
intros rnd valid_rnd x y Hrnd Fx Fy.
case (Rle_or_lt 0 y); intros Hy.
destruct Hy as [Hy|Hy].
now apply H.
now rewrite <- Hy, Rmult_0_r, Rminus_0_r.
replace (Z2R (rnd (x/y))*y)%R with
  (Z2R ((Zrnd_opp rnd) ((x/(-y))))*(-y))%R.
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
unfold Zrnd_opp; rewrite Z2R_opp, Ropp_involutive.
f_equal; f_equal; f_equal.
field; now apply Rlt_not_eq.
Qed.

Theorem format_REM_ZR:
  forall (x y : R),
  (format x) -> (format y) ->
    format (x-Z2R (Ztrunc (x/y))*y).
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

Theorem format_REM_N: forall choice,
  forall (x y : R),
  (format x) -> (format y) ->
    format (x- (Z2R (Znearest choice (x/y)))*y).
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

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

Section About_Int_Div.
Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Lemma RoundInteger_is_int: forall x,
   exists n:Z, Z2R n = round beta (FIX_exp 0) rnd x.
Proof with auto with typeclass_instances.
intros x.
assert (generic_format beta (FIX_exp 0) (round beta (FIX_exp 0) rnd x)).
apply generic_format_round...
exists (Ztrunc (scaled_mantissa beta (FIX_exp 0)
           (round beta (FIX_exp 0) rnd x))).
rewrite H at 2.
unfold F2R; simpl; ring.
Qed.

Lemma NearestInteger_correct: forall choice, forall x,
   (forall z:Z, (Rabs (round beta (FIX_exp 0) (Znearest choice) x -x)
      <= Rabs (Z2R z - x)))%R.
Proof with auto with typeclass_instances.
intros choice x z.
apply round_N_pt...
apply generic_format_FIX.
exists (Float beta z 0); try easy.
unfold F2R; simpl; ring.
Qed.


End About_Int_Div.

Section format_REM_aux.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { monotone_exp : Monotone_exp fexp }.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Notation round_Int := (round beta (FIX_exp 0) rnd).
Notation format := (generic_format beta fexp).

Hypothesis rnd_small: forall x, (0 < x < /2)%R -> rnd x = 0%Z.


Lemma format_REM_aux:
 forall (x y : R),
  (format x) -> (format y) -> (0 <= x)%R -> (0 < y)%R ->
    format (x-round_Int (x/y)*y).
Proof with auto with typeclass_instances.
intros x y Fx Fy Hx Hy.
destruct (RoundInteger_is_int beta rnd (x/y)) as (n,Hn).
rewrite <- Hn.
assert (H:(0 <= n)%Z).
apply le_Z2R; rewrite Hn; simpl.
apply Rle_trans with (round_Int 0).
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
rewrite H0.
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
intros Hn'; rewrite <- Hn'.
rewrite Rmult_1_l.
apply sterbenz...
assert (H0:(Rabs (1  - x/y) < 1)%R).
replace 1%R with (Z2R 1) at 1 by reflexivity.
rewrite Hn', Hn.
case Hx; intros Hx'.
apply Rlt_le_trans with (ulp beta (FIX_exp 0) (round_Int (x / y)))%R.
apply error_lt_ulp_round...
now apply Rgt_not_eq, Rdiv_lt_0_compat.
rewrite ulp_FIX.
simpl; right; ring.
rewrite <- Hx'; unfold Rdiv; rewrite Rmult_0_l.
rewrite round_0...
rewrite Rminus_0_l, Ropp_0, Rabs_R0; apply Rlt_0_1.
apply Rabs_lt_inv in H0.
split; apply Rmult_le_reg_l with (/y)%R; try now apply Rinv_0_lt_compat.
unfold Rdiv; rewrite <- Rmult_assoc.
rewrite Rinv_l.
2: now apply Rgt_not_eq.
rewrite Rmult_1_l, Rmult_comm; fold (x/y)%R.
case (Rle_or_lt (/2) (x/y)); try easy.
intros K; absurd (n=0)%Z.
omega.
assert (J:(0 <= x / y)%R).
apply Fourier_util.Rle_mult_inv_pos; assumption.
case J; intros J'.
apply eq_Z2R; rewrite Hn.
unfold round, cexp, FIX_exp, F2R, scaled_mantissa; simpl.
rewrite 2!Rmult_1_r.
replace 0%R with (Z2R 0) by reflexivity; f_equal.
apply rnd_small; now split.
apply eq_Z2R; rewrite Hn, <- J', round_0...
apply Ropp_le_cancel; apply Rplus_le_reg_l with 1%R.
apply Rle_trans with (1-x/y)%R.
2: right; unfold Rdiv; ring.
left; apply Rle_lt_trans with (2:=proj1 H0).
right; field.
now apply Rgt_not_eq.
(* n = 0 *)
clear H; intros H; rewrite <- H.
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
  (forall z, (- /2 < z < /2)%R -> rnd z = 0%Z) ->
  forall (x y : R),
  (format x) -> (format y) ->
    format (x-round beta (FIX_exp 0) rnd (x/y)*y).
Proof with auto with typeclass_instances.
(* assume 0 < y *)
assert (H: forall rnd : R -> Z, Valid_rnd rnd ->
  (forall z, (-/2 < z < /2)%R -> rnd z = 0%Z) ->
  forall (x y : R),
  (format x) -> (format y) -> (0 < y)%R ->
    format (x-round beta (FIX_exp 0) rnd (x/y)*y)).
intros rnd valid_rnd Hrnd x y Fx Fy Hy.
case (Rle_or_lt 0 x); intros Hx.
apply format_REM_aux; try easy.
intros z Hz; apply Hrnd; split; try easy.
apply Rle_lt_trans with 0%R; try easy.
apply Ropp_le_cancel; rewrite Ropp_0, Ropp_involutive.
left; apply Rinv_0_lt_compat, Rlt_0_2.
replace (x-(round beta (FIX_exp 0) rnd (x/y))*y)%R with
   (-((-x)-(round beta (FIX_exp 0) (Zrnd_opp rnd)
            ((-x)/y))*y))%R.
apply generic_format_opp.
apply format_REM_aux; try easy...
intros z Hz.
rewrite <- Zopp_0; unfold Zrnd_opp; f_equal.
apply Hrnd; split.
apply Ropp_lt_contravar, Hz.
apply Rlt_trans with (-0)%R.
apply Ropp_lt_contravar, Hz.
rewrite Ropp_0; apply Rinv_0_lt_compat, Rlt_0_2.
now apply generic_format_opp.
apply Ropp_le_cancel; rewrite Ropp_0, Ropp_involutive; now left.
apply trans_eq with (x-((-round beta (FIX_exp 0) (Zrnd_opp rnd) (- x / y))*y))%R.
ring.
apply Rplus_eq_compat_l; f_equal; f_equal.
rewrite <- round_opp; f_equal; unfold Rdiv; ring.
(* *)
intros rnd valid_rnd Hrnd x y Fx Fy.
case (Rle_or_lt 0 y); intros Hy.
destruct Hy as [Hy|Hy].
now apply H.
now rewrite <- Hy, Rmult_0_r, Rminus_0_r.
replace ((round beta (FIX_exp 0) rnd (x/y))*y)%R with
  (round beta (FIX_exp 0) (Zrnd_opp rnd) ((x/(-y)))*(-y))%R.
apply H; try easy...
intros z Hz.
unfold Zrnd_opp; rewrite <- Zopp_0; f_equal.
apply Hrnd; split.
apply Ropp_lt_contravar, Hz.
rewrite <- (Ropp_involutive (/2)).
apply Ropp_lt_contravar, Hz.
now apply generic_format_opp.
apply Ropp_lt_cancel; now rewrite Ropp_0, Ropp_involutive.
rewrite Ropp_mult_distr_r_reverse, Ropp_mult_distr_l.
rewrite <- round_opp; f_equal; f_equal.
field; now apply Rlt_not_eq.
Qed.

Theorem format_REM_ZR:
  forall (x y : R),
  (format x) -> (format y) ->
    format (x-round beta (FIX_exp 0) Ztrunc (x/y)*y).
Proof with auto with typeclass_instances.
intros x y Fx Fy.
apply format_REM; try easy...
intros z Hz.
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
case (Rle_or_lt 0 z); intros Hz'.
now apply H.
rewrite <- (Ropp_involutive z), <- Zopp_0.
rewrite Ztrunc_opp; f_equal.
apply H; split.
apply Ropp_le_cancel; rewrite Ropp_involutive, Ropp_0; now left.
apply Ropp_lt_cancel; rewrite Ropp_involutive; apply Hz.
Qed.

Theorem format_REM_N: forall choice,
  forall (x y : R),
  (format x) -> (format y) ->
    format (x-round beta (FIX_exp 0) (Znearest choice) (x/y)*y).
Proof with auto with typeclass_instances.
intros choice x y Fx Fy.
apply format_REM; try easy...
intros z Hz.
apply Znearest_imp.
rewrite Rminus_0_r.
now apply Rabs_lt.
Qed.

End format_REM.
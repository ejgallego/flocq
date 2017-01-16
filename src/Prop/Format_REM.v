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

Variable choice : Z -> bool.

Lemma NearestInteger_is_int: forall x, 
   exists n:Z, Z2R n = round beta (FIX_exp 0) (Znearest choice) x.
Proof with auto with typeclass_instances.
intros x.
assert (generic_format beta (FIX_exp 0) (round beta (FIX_exp 0) (Znearest choice) x)).
apply generic_format_round...
exists (Ztrunc (scaled_mantissa beta (FIX_exp 0)
           (round beta (FIX_exp 0) (Znearest choice) x))).
rewrite H at 2.
unfold F2R; simpl; ring.
Qed.

Lemma NearestInteger_correct: forall x,
   (forall z:Z, (Rabs (round beta (FIX_exp 0) (Znearest choice) x -x)
      <= Rabs (Z2R z - x)))%R.
Proof with auto with typeclass_instances.
intros x z.
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

Variable choice : Z -> bool.

Notation round_Int := (round beta (FIX_exp 0) (Znearest choice)).
Notation format := (generic_format beta fexp).

Lemma format_REM_aux:
 forall (x y : R),
  (format x) -> (format y) -> (0 <= x)%R -> (0 < y)%R ->
    format (x-round_Int (x/y)*y).
Proof with auto with typeclass_instances.
intros x y Fx Fy Hx Hy.
destruct (NearestInteger_is_int beta choice (x/y)) as (n,Hn).
rewrite <- Hn.
assert (H:(0 <= n)%Z).
apply le_Z2R; rewrite Hn; simpl.
eapply Rnd_N_pt_pos.
3: apply round_N_pt...
apply generic_format_0...
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
(* n = 1 -> Sterbenz *)
intros Hn'; rewrite <- Hn'.
rewrite Rmult_1_l.
apply sterbenz...
assert (H0:(Rabs (1  - x/y) <= /2)%R).
replace 1%R with (Z2R 1) at 1 by reflexivity.
rewrite Hn', Hn.
apply Rle_trans with (/2*ulp beta (FIX_exp 0) (round_Int (x / y)))%R.
apply error_le_half_ulp_round...
rewrite ulp_FIX.
simpl; right; ring.
apply Rabs_le_inv in H0.
split; apply Rmult_le_reg_l with (/y)%R; try now apply Rinv_0_lt_compat.
unfold Rdiv; rewrite <- Rmult_assoc.
rewrite Rinv_l.
2: now apply Rgt_not_eq.
apply Ropp_le_cancel; apply Rplus_le_reg_l with 1%R.
apply Rle_trans with (1-x/y)%R.
right; unfold Rdiv; ring.
apply Rle_trans with (1:=proj2 H0).
right; field.
apply Ropp_le_cancel; apply Rplus_le_reg_l with 1%R.
apply Rle_trans with (1-x/y)%R.
2: right; unfold Rdiv; ring.
apply Rle_trans with (2:=proj1 H0).
apply Rle_trans with (-1)%R.
right; field.
now apply Rgt_not_eq.
apply Ropp_le_contravar.
apply Rmult_le_reg_l with 2%R.
apply Rlt_0_2.
rewrite Rinv_r.
apply Rplus_le_reg_l with (-1)%R; ring_simplify.
apply Rle_0_1.
apply Rgt_not_eq, Rlt_0_2.
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

Theorem format_REM:
 forall choice : Z -> bool,
 forall (x y : R),
  (format x) -> (format y) ->
    format (x-round beta (FIX_exp 0) (Znearest choice) (x/y)*y).
Proof with auto with typeclass_instances.
(* assume 0 < y *)
assert (H: forall choice : Z -> bool, forall (x y : R),
  (format x) -> (format y) -> (0 < y)%R ->
    format (x-round beta (FIX_exp 0) (Znearest choice) (x/y)*y)).
intros choice x y Fx Fy Hy.
case (Rle_or_lt 0 x); intros Hx.
now apply format_REM_aux.
replace (x-(round beta (FIX_exp 0) (Znearest choice) (x/y))*y)%R with 
   (-((-x)-(round beta (FIX_exp 0) (Znearest (fun t : Z => negb (choice (- (t + 1))%Z)))
            ((-x)/y))*y))%R.
apply generic_format_opp.
apply format_REM_aux; try easy.
now apply generic_format_opp.
apply Ropp_le_cancel; rewrite Ropp_0, Ropp_involutive; now left.
ring_simplify.
apply Rplus_eq_compat_l.
rewrite Ropp_div, round_N_opp.
rewrite Ropp_mult_distr_l_reverse; f_equal.
rewrite Rmult_comm; f_equal.
unfold round; f_equal; f_equal.
unfold Znearest; rewrite Bool.negb_involutive.
now ring_simplify (- (- (Zfloor (scaled_mantissa beta (FIX_exp 0) (x / y)) + 1) + 1))%Z.
(* *)
intros choice x y Fx Fy.
case (Rle_or_lt 0 y); intros Hy.
destruct Hy as [Hy|Hy].
now apply H.
now rewrite <- Hy, Rmult_0_r, Rminus_0_r.
replace ((round beta (FIX_exp 0) (Znearest choice) (x/y))*y)%R with 
  (round beta (FIX_exp 0) (Znearest (fun t : Z => negb (choice (- (t + 1))%Z))) ((x/(-y)))*(-y))%R.
apply H; try easy.
now apply generic_format_opp.
apply Ropp_lt_cancel; now rewrite Ropp_0, Ropp_involutive.
rewrite Ropp_mult_distr_r_reverse, Ropp_mult_distr_l; f_equal.
unfold Rdiv; rewrite <- Ropp_inv_permute.
rewrite Ropp_mult_distr_r_reverse.
rewrite round_N_opp, Ropp_involutive.
unfold round; f_equal; f_equal.
unfold Znearest; rewrite Bool.negb_involutive.
now ring_simplify (- (- (Zfloor (scaled_mantissa beta (FIX_exp 0) (x */ y)) + 1) + 1))%Z.
now apply Rlt_not_eq.
Qed.

End format_REM.
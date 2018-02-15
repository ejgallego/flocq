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

(** * Helper functions and theorems for computing the rounded square root of a floating-point number. *)

Require Import Raux Defs Digits Generic_fmt Float_prop Bracket.

Section Fcalc_sqrt.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

(** Computes a mantissa of precision p, the corresponding exponent,
    and the position with respect to the real square root of the
    input floating-point number.

The algorithm performs the following steps:
- Shift the mantissa so that it has at least 2p-1 digits;
  shift it one digit more if the new exponent is not even.
- Compute the square root s (at least p digits) of the new
  mantissa, and its remainder r.
- Compute the position according to the remainder:
  -- r == 0  =>  Eq,
  -- r <= s  =>  Lo,
  -- r >= s  =>  Up.

Complexity is fine as long as p1 <= 2p-1.
*)

Definition Fsqrt_core m e :=
  let d := Zdigits beta m in
  let e' := Zmin (fexp (Z.div2 (d + e + 1))) (Z.div2 e) in
  let m' := (m * Zpower beta (e - 2 * e'))%Z in
  let (q, r) := Z.sqrtrem m' in
  let l :=
    if Zeq_bool r 0 then loc_Exact
    else loc_Inexact (if Zle_bool r q then Lt else Gt) in
  (q, e', l).

Theorem Fsqrt_core_correct :
  forall m e,
  (0 < m)%Z ->
  let '(m', e', l) := Fsqrt_core m e in
  (e' <= cexp beta fexp (sqrt (F2R (Float beta m e))))%Z /\
  inbetween_float beta m' e' (sqrt (F2R (Float beta m e))) l.
Proof.
intros m e Hm.
unfold Fsqrt_core.
set (d := Zdigits beta m).
set (e'' := Z.div2 (d + e + 1)).
set (e' := Zmin (fexp e'') (Z.div2 e)).
set (s := (e - 2 * e')%Z).
set (m' := (m * Zpower beta s)%Z).
assert (bpow (e'' - 1) <= sqrt (F2R (Float beta m e)) < bpow e'')%R as Hs.
{ unfold e'', d. clear -Hm.
  rewrite <- (mag_F2R_Zdigits beta m e (Zgt_not_eq _ _ Hm)).
  destruct mag as [e' Hs'].
  simpl.
  assert (bpow (e' - 1) <= F2R (Float beta m e) < bpow e')%R as Hs.
    rewrite Rabs_pos_eq in Hs'.
    now apply Hs', F2R_neq_0, Zgt_not_eq.
    now apply F2R_ge_0, Zlt_le_weak.
  clear Hs'.
  split.
  - rewrite <- (sqrt_Rsqr (bpow _)) by now apply bpow_ge_0.
    apply sqrt_le_1_alt.
    unfold Rsqr.
    rewrite <- bpow_plus.
    apply Rle_trans with (2 := proj1 Hs).
    apply bpow_le.
    replace (e' - 1)%Z with (e' + 1 - 2)%Z by ring.
    rewrite (Zdiv2_odd_eqn (e' + 1)) at 3.
    case Z.odd ; clear ; omega.
  - rewrite <- (sqrt_Rsqr (bpow _)) by now apply bpow_ge_0.
    apply sqrt_lt_1_alt.
    split.
      now apply F2R_ge_0, Zlt_le_weak.
    unfold Rsqr.
    rewrite <- bpow_plus.
    apply Rlt_le_trans with (1 := proj2 Hs).
    apply bpow_le.
    replace e' with (e' + 1 - 1)%Z at 1 by ring.
    rewrite (Zdiv2_odd_eqn (e' + 1)) at 1.
    case Z.odd ; clear ; omega. }
assert (F2R (Float beta m e) = F2R (Float beta m' (2 * e'))) as Hf.
  apply F2R_change_exp.
  unfold e'.
  rewrite <- Z.mul_min_distr_nonneg_l by easy.
  apply Zle_trans with (1 := Z.le_min_r _ _).
  rewrite (Zdiv2_odd_eqn e) at 2.
  case Z.odd ; clear ; omega.
assert (0 <= m')%Z as Hm'.
  apply Z.mul_nonneg_nonneg.
  now apply Zlt_le_weak.
  apply Zpower_ge_0.
generalize (Z.sqrtrem_spec m' Hm').
destruct Z.sqrtrem as [q r].
intros [Hq Hr].
split.
  unfold cexp.
  rewrite (mag_unique _ _ e'').
  apply Z.le_min_l.
  rewrite Rabs_pos_eq.
  exact Hs.
  apply sqrt_ge_0.
rewrite Hf.
unfold inbetween_float, F2R. simpl Fnum.
rewrite sqrt_mult.
2: now apply IZR_le.
2: apply Rlt_le ; apply bpow_gt_0.
replace (2 * e')%Z with (e' + e')%Z by ring.
simpl Fexp.
rewrite bpow_plus.
fold (Rsqr (bpow e')).
rewrite sqrt_Rsqr by apply bpow_ge_0.
apply inbetween_mult_compat.
apply bpow_gt_0.
rewrite Hq.
case Zeq_bool_spec ; intros Hr'.
(* .. r = 0 *)
rewrite Hr', Zplus_0_r, mult_IZR.
fold (Rsqr (IZR q)).
rewrite sqrt_Rsqr.
now constructor.
apply IZR_le.
clear -Hr ; omega.
(* .. r <> 0 *)
constructor.
split.
(* ... bounds *)
apply Rle_lt_trans with (sqrt (IZR (q * q))).
rewrite mult_IZR.
fold (Rsqr (IZR q)).
rewrite sqrt_Rsqr.
apply Rle_refl.
apply IZR_le.
clear -Hr ; omega.
apply sqrt_lt_1.
rewrite mult_IZR.
apply Rle_0_sqr.
rewrite <- Hq.
now apply IZR_le.
apply IZR_lt.
omega.
apply Rlt_le_trans with (sqrt (IZR ((q + 1) * (q + 1)))).
apply sqrt_lt_1.
rewrite <- Hq.
now apply IZR_le.
rewrite mult_IZR.
apply Rle_0_sqr.
apply IZR_lt.
ring_simplify.
omega.
rewrite mult_IZR.
fold (Rsqr (IZR (q + 1))).
rewrite sqrt_Rsqr.
apply Rle_refl.
apply IZR_le.
clear -Hr ; omega.
(* ... location *)
rewrite Rcompare_half_r.
generalize (Rcompare_sqr (2 * sqrt (IZR (q * q + r))) (IZR q + IZR (q + 1))).
rewrite 2!Rabs_pos_eq.
intros <-.
replace ((2 * sqrt (IZR (q * q + r))) * (2 * sqrt (IZR (q * q + r))))%R
  with (4 * Rsqr (sqrt (IZR (q * q + r))))%R by (unfold Rsqr ; ring).
rewrite Rsqr_sqrt.
rewrite <- plus_IZR, <- 2!mult_IZR.
rewrite Rcompare_IZR.
replace ((q + (q + 1)) * (q + (q + 1)))%Z with (4 * (q * q) + 4 * q + 1)%Z by ring.
generalize (Zle_cases r q).
case (Zle_bool r q) ; intros Hr''.
change (4 * (q * q + r) < 4 * (q * q) + 4 * q + 1)%Z.
omega.
change (4 * (q * q + r) > 4 * (q * q) + 4 * q + 1)%Z.
omega.
rewrite <- Hq.
now apply IZR_le.
rewrite <- plus_IZR.
apply IZR_le.
clear -Hr ; omega.
apply Rmult_le_pos.
now apply IZR_le.
apply sqrt_ge_0.
Qed.

End Fcalc_sqrt.

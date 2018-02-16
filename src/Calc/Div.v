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

(** * Helper function and theorem for computing the rounded quotient of two floating-point numbers. *)

Require Import Raux Defs Generic_fmt Float_prop Digits Bracket.

Section Fcalc_div.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

(** Computes a mantissa of precision p, the corresponding exponent,
    and the position with respect to the real quotient of the
    input floating-point numbers.

The algorithm performs the following steps:
- Shift dividend mantissa so that it has at least p2 + p digits.
- Perform the Euclidean division.
- Compute the position according to the division remainder.

Complexity is fine as long as p1 <= 2p and p2 <= p.
*)

Definition Fdiv_core m1 e1 m2 e2 :=
  let d1 := Zdigits beta m1 in
  let d2 := Zdigits beta m2 in
  let e' := (d1 + e1 - (d2 + e2))%Z in
  let e := Zmin (Zmin (fexp e') (fexp (e' + 1))) (e1 - e2) in
  let m := (m1 * Zpower beta (e1 - e2 - e))%Z in
  let '(q, r) :=  Zdiv_eucl m m2 in
  (q, e, new_location m2 r loc_Exact).

Theorem Fdiv_core_correct :
  forall m1 e1 m2 e2,
  (0 < m1)%Z -> (0 < m2)%Z ->
  let '(m, e, l) := Fdiv_core m1 e1 m2 e2 in
  (e <= cexp beta fexp (F2R (Float beta m1 e1) / F2R (Float beta m2 e2)))%Z /\
  inbetween_float beta m e (F2R (Float beta m1 e1) / F2R (Float beta m2 e2)) l.
Proof.
intros m1 e1 m2 e2 Hm1 Hm2.
unfold Fdiv_core.
set (d1 := Zdigits beta m1).
set (d2 := Zdigits beta m2).
set (e := (d1 + e1 - (d2 + e2))%Z).
set (e' := Zmin (Zmin (fexp e) (fexp (e + 1))) (e1 - e2)).
set (m' := (m1 * Zpower beta (e1 - e2 - e'))%Z).
assert (bpow (e - 1) < F2R (Float beta m1 e1) / F2R (Float beta m2 e2) < bpow (e + 1))%R as Hd.
{ unfold e, d1, d2.
  rewrite <- (mag_F2R_Zdigits beta m1 e1) by now apply Zgt_not_eq.
  rewrite <- (mag_F2R_Zdigits beta m2 e2) by now apply Zgt_not_eq.
  destruct mag as [e1' He1].
  destruct mag as [e2' He2].
  simpl.
  assert (bpow (e1' - 1) <= F2R (Float beta m1 e1) < bpow e1')%R as H1.
  { rewrite Rabs_pos_eq in He1.
    now apply He1, F2R_neq_0, Zgt_not_eq.
    now apply Rlt_le, F2R_gt_0. }
  assert (bpow (e2' - 1) <= F2R (Float beta m2 e2) < bpow e2')%R as H2.
  { rewrite Rabs_pos_eq in He2.
    now apply He2, F2R_neq_0, Zgt_not_eq.
    now apply Rlt_le, F2R_gt_0. }
  split.
  - replace (e1' - e2' - 1)%Z with (e1' - 1 + -e2')%Z by ring.
    rewrite bpow_plus, bpow_opp.
    apply Rle_lt_trans with (F2R (Float beta m1 e1) * / bpow e2')%R.
    apply Rmult_le_compat_r with (2 := proj1 H1).
    apply Rlt_le, Rinv_0_lt_compat, bpow_gt_0.
    apply Rmult_lt_compat_l.
    now apply F2R_gt_0.
    apply Rinv_lt with (2 := proj2 H2).
    now apply F2R_gt_0.
  - replace (e1' - e2' + 1)%Z with (e1' + -(e2' - 1))%Z by ring.
    rewrite bpow_plus, bpow_opp.
    apply Rle_lt_trans with (F2R (Float beta m1 e1) * / bpow (e2' - 1))%R.
    apply Rmult_le_compat_l.
    now apply F2R_ge_0, Zlt_le_weak.
    apply Rinv_le with (2 := proj1 H2).
    apply bpow_gt_0.
    apply Rmult_lt_compat_r with (2 := proj2 H1).
    apply Rinv_0_lt_compat, bpow_gt_0. }
assert (F2R (Float beta m1 e1) = F2R (Float beta m' (e' + e2))) as Hf1.
  unfold m'.
  replace (e1 - e2 - e')%Z with (e1 - (e' + e2))%Z by ring.
  apply F2R_change_exp.
  cut (e' <= e1 - e2)%Z. clear ; omega.
  apply Z.le_min_r.
generalize (Z_div_mod m' m2 (Zlt_gt _ _ Hm2)).
destruct (Zdiv_eucl m' m2) as (q, r).
intros (Hq, Hr).
split.
- apply Zle_trans with (1 := Zle_min_l _ _).
  unfold cexp.
  assert (e <= mag beta (F2R (Float beta m1 e1) / F2R (Float beta m2 e2)) <= e + 1)%Z as [H1 H2].
  { destruct Hd as [Hd1 Hd2].
    assert (0 < F2R (Float beta m1 e1) / F2R (Float beta m2 e2))%R as H.
      apply Rmult_lt_0_compat.
      now apply F2R_gt_0.
      now apply Rinv_0_lt_compat, F2R_gt_0.
    split.
    - apply mag_ge_bpow.
      rewrite Rabs_pos_eq ; now apply Rlt_le.
    - apply mag_le_bpow.
      now apply Rgt_not_eq.
      rewrite Rabs_pos_eq.
      exact Hd2.
      now apply Rlt_le. }
  destruct (Zle_lt_or_eq _ _ H1) as [H|H].
  + replace (fexp (mag _ _)) with (fexp (e + 1)).
    apply Zle_min_r.
    clear -H1 H2 H ; apply f_equal ; omega.
  + replace (fexp (mag _ _)) with (fexp e).
    apply Zle_min_l.
    clear -H1 H2 H ; apply f_equal ; omega.
- rewrite Hf1.
unfold inbetween_float, F2R. simpl.
rewrite bpow_plus, plus_IZR.
rewrite Hq, plus_IZR, mult_IZR.
replace ((IZR m2 * IZR q + IZR r) * (bpow e' * bpow e2) / (IZR m2 * bpow e2))%R
  with ((IZR q + IZR r / IZR m2) * bpow e')%R.
apply inbetween_mult_compat.
apply bpow_gt_0.
destruct (Z_lt_le_dec 1 m2) as [Hm2''|Hm2''].
replace 1%R with (IZR m2 * /IZR m2)%R.
apply new_location_correct ; try easy.
apply Rinv_0_lt_compat.
now apply IZR_lt.
now constructor.
apply Rinv_r.
apply Rgt_not_eq.
now apply IZR_lt.
assert (r = 0 /\ m2 = 1)%Z by (clear -Hr Hm2'' ; omega).
rewrite (proj1 H), (proj2 H).
unfold Rdiv.
rewrite Rmult_0_l, Rplus_0_r.
now constructor.
field.
split ; apply Rgt_not_eq.
apply bpow_gt_0.
now apply IZR_lt.
Qed.

End Fcalc_div.

(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2010 Sylvie Boldo
#<br />#
Copyright (C) 2010 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * Computing the rounded division *)
Require Import Fcore.
Require Import Fcalc_bracket.
Require Import Fcalc_digits.

Section Fcalc_div.

Variable beta : radix.
Notation bpow e := (bpow beta e).

(**
 - Shift dividend mantissa so that it has at least p2 + p digits.
 - Perform the euclidean division.
 - Compute position with remainder.
 
  Complexity is fine as long as p1 <= 2p and p2 <= p.
 *)

Definition Fdiv_aux prec m1 e1 m2 e2 :=
  let d1 := digits beta m1 in
  let d2 := digits beta m2 in
  let e := (e1 - e2)%Z in
  let (m, e') :=
    match (d2 + prec - d1)%Z with
    | Zpos p => (m1 * Zpower_pos beta p, e + Zneg p)%Z
    | _ => (m1, e)
    end in
  let '(q, r) :=  Zdiv_eucl m m2 in
  (q, e', new_location m2 r loc_Exact).

Theorem Fdiv_aux_correct :
  forall prec m1 e1 m2 e2,
  (0 < prec)%Z ->
  (0 < m1)%Z -> (1 < m2)%Z ->
  let '(m, e, l) := Fdiv_aux prec m1 e1 m2 e2 in
  (prec <= digits beta m)%Z /\
  inbetween_float beta m e (F2R (Float beta m1 e1) / F2R (Float beta m2 e2)) l.
Proof.
intros prec m1 e1 m2 e2 Hprec Hm1 Hm2.
unfold Fdiv_aux.
set (d1 := digits beta m1).
set (d2 := digits beta m2).
case_eq
 (match (d2 + prec - d1)%Z with
  | Zpos p => ((m1 * Zpower_pos beta p)%Z, (e1 - e2 + Zneg p)%Z)
  | _ => (m1, (e1 - e2)%Z)
  end).
intros m' e' Hme.
(* . the shifted mantissa m' has enough digits *)
assert (Hs: F2R (Float beta m' (e' + e2)) = F2R (Float beta m1 e1) /\ (0 < m')%Z /\ (d2 + prec <= digits beta m')%Z).
replace (d2 + prec)%Z with (d2 + prec - d1 + d1)%Z by ring.
destruct (d2 + prec - d1)%Z as [|p|p] ;
  unfold d1 ;
  inversion Hme.
ring_simplify (e1 - e2 + e2)%Z.
repeat split.
now rewrite <- H0.
apply Zle_refl.
replace (e1 - e2 + Zneg p + e2)%Z with (e1 - Zpos p)%Z by (unfold Zminus ; simpl ; ring).
fold (Zpower beta (Zpos p)).
split.
pattern (Zpos p) at 1 ; replace (Zpos p) with (e1 - (e1 - Zpos p))%Z by ring.
apply sym_eq.
apply F2R_change_exp.
assert (0 < Zpos p)%Z by easy.
omega.
split.
apply Zmult_lt_0_compat.
exact Hm1.
now apply Zpower_gt_0.
rewrite digits_shift.
rewrite Zplus_comm.
apply Zle_refl.
apply sym_not_eq.
now apply Zlt_not_eq.
easy.
split.
now ring_simplify (e1 - e2 + e2)%Z.
assert (Zneg p < 0)%Z by easy.
omega.
(* . *)
destruct Hs as (Hs1, (Hs2, Hs3)).
rewrite <- Hs1.
assert (Hm2': (0 < m2)%Z) by omega.
generalize (Z_div_mod m' m2 (Zlt_gt _ _ Hm2')).
destruct (Zdiv_eucl m' m2) as (q, r).
intros (Hq, Hr).
split.
(* . the result mantissa q has enough digits *)
cut (digits beta m' <= d2 + digits beta q)%Z. omega.
unfold d2.
rewrite Hq.
assert (Hq': (0 < q)%Z).
apply Zmult_lt_reg_r with m2.
exact Hm2'.
assert (m2 < m')%Z.
apply digits_lt with beta.
now apply Zlt_le_weak.
unfold d2 in Hs3.
omega.
cut (q * m2 = m' - r)%Z. omega.
rewrite Hq.
ring.
apply Zle_trans with (digits beta (m2 + q + m2 * q)).
apply digits_le.
rewrite <- Hq.
now apply Zlt_le_weak.
omega.
apply digits_mult_strong.
omega.
now apply Zlt_le_weak.
(* . the location is correctly computed *)
unfold inbetween_float, F2R. simpl.
rewrite bpow_plus, Z2R_plus.
rewrite Hq, Z2R_plus, Z2R_mult.
replace ((Z2R m2 * Z2R q + Z2R r) * (bpow e' * bpow e2) / (Z2R m2 * bpow e2))%R
  with ((Z2R q + Z2R r / Z2R m2) * bpow e')%R.
apply inbetween_mult_compat.
apply bpow_gt_0.
replace (Z2R 1) with (Z2R m2 * /Z2R m2)%R.
apply new_location_correct ; try easy.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0).
now constructor.
apply Rinv_r.
apply Rgt_not_eq.
now apply (Z2R_lt 0).
field.
split ; apply Rgt_not_eq.
apply bpow_gt_0.
now apply (Z2R_lt 0).
Qed.

End Fcalc_div.
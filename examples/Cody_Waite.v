(**
This example is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2014-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals Flocq.Core.Core.
Require Import Gappa.Gappa_tactic Interval.Interval_tactic.

Open Scope R_scope.

Lemma rel_helper :
  forall xa xe b : R,
  xe <> 0 ->
  (Rabs ((xa - xe) / xe) <= b <-> Rabs (xa - xe) <= b * Rabs xe).
Proof.
intros xa xe b Zx.
unfold Rdiv.
rewrite Rabs_mult, Rabs_Rinv by exact Zx.
split ; intros H.
- apply Rmult_le_reg_r with (/ Rabs xe).
  apply Rinv_0_lt_compat.
  now apply Rabs_pos_lt.
  rewrite Rmult_assoc, Rinv_r, Rmult_1_r.
  exact H.
  now apply Rabs_no_R0.
- apply Rmult_le_reg_r with (Rabs xe).
  now apply Rabs_pos_lt.
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
  exact H.
  now apply Rabs_no_R0.
Qed.

Lemma Rdiv_compat_r :
  forall a b c : R, a <> 0 -> c <> 0 ->
  (a*b) / (a*c) = b/c.
Proof.
intros a b c Ha Hc.
field.
apply conj.
apply Hc.
apply Ha.
Qed.

Notation pow2 := (bpow radix2).
Notation rnd := (round radix2 (FLT_exp (-1074) 53) ZnearestE).

Definition add x y := rnd (x + y).
Definition sub x y := rnd (x - y).
Definition mul x y := rnd (x * y).
Definition div x y := rnd (x / y).
Definition nearbyint x := round radix2 (FIX_exp 0) ZnearestE x.

Definition Log2h := 3048493539143 * pow2 (-42).
Definition Log2l := 544487923021427 * pow2 (-93).
Definition InvLog2 := 3248660424278399 * pow2 (-51).

Definition p0 := 1 * pow2 (-2).
Definition p1 := 4002712888408905 * pow2 (-59).
Definition p2 := 1218985200072455 * pow2 (-66).
Definition q0 := 1 * pow2 (-1).
Definition q1 := 8006155947364787 * pow2 (-57).
Definition q2 := 4573527866750985 * pow2 (-63).

Definition cw_exp (x : R) :=
  let k := nearbyint (mul x InvLog2) in
  let t := sub (sub x (mul k Log2h)) (mul k Log2l) in
  let t2 := mul t t in
  let p := add p0 (mul t2 (add p1 (mul t2 p2))) in
  let q := add q0 (mul t2 (add q1 (mul t2 q2))) in
  pow2 (Zfloor k + 1) * (add (div (mul t p) (sub q (mul t p))) (1/2)).

Lemma method_error :
  forall t : R,
  let t2 := t * t in
  let p := p0 + t2 * (p1 + t2 * p2) in
  let q := q0 + t2 * (q1 + t2 * q2) in
  let f := 2 * ((t * p) / (q - t * p) + 1/2) in
  Rabs t <= 355 / 1024 ->
  Rabs ((f - exp t) / exp t) <= 23 * pow2 (-62).
Proof.
intros t t2 p q f Ht.
unfold f, q, p, t2, p0, p1, p2, q0, q1, q2 ;
interval with (i_bisect_taylor t 9, i_prec 70).
Qed.

Lemma argument_reduction :
  forall x : R,
  generic_format radix2 (FLT_exp (-1074) 53) x ->
  -746 <= x <= 710 ->
  let k := nearbyint (mul x InvLog2) in
  let tf := sub (sub x (mul k Log2h)) (mul k Log2l) in
  let te := x - k * ln 2 in
  Rabs tf <= 355 / 1024 /\
  Rabs (tf - te) <= 65537 * pow2 (-71).
Proof with auto with typeclass_instances.
intros x Fx Bx k tf te.
assert (Rabs x <= 5/16 \/ 5/16 <= Rabs x <= 746) as [Bx'|Bx'] by gappa.
- assert (k = 0).
    clear -Bx'.
    refine (let H := _ in Rle_antisym _ _ (proj2 H) (proj1 H)).
    unfold k, mul, nearbyint, InvLog2, Log2h ; gappa.
  unfold tf, te, mul, sub.
  rewrite H.
  rewrite 2!Rmult_0_l.
  rewrite round_0...
  rewrite Rmult_0_l.
  rewrite 2!Rminus_0_r.
  rewrite 2!round_generic with (2 := Fx)...
  gappa.
- assert (Hl: - 1 * pow2 (-102) <= Log2l - (ln 2 - Log2h) <= 0).
    unfold Log2l, Log2h ;
    interval with (i_prec 110).
  assert (Ax: x = x * InvLog2 * (1 / InvLog2)).
    field.
    unfold InvLog2 ; interval.
  unfold te.
  replace (x - k * ln 2) with (x - k * Log2h - k * (ln 2 - Log2h)) by ring.
  revert Hl Ax.
  unfold tf, te, k, sub, mul, nearbyint, InvLog2, Log2h, Log2l ; gappa.
Qed.

Theorem exp_correct :
  forall x : R,
  generic_format radix2 (FLT_exp (-1074) 53) x ->
  -746 <= x <= 710 ->
  Rabs ((cw_exp x - exp x) / exp x) <= 1 * pow2 (-51).
Proof.
intros x Fx Bx.
generalize (argument_reduction x Fx Bx).
unfold cw_exp.
set (k := nearbyint (mul x InvLog2)).
set (t := sub (sub x (mul k Log2h)) (mul k Log2l)).
set (t2 := mul t t).
intros [Bt Et].
clearbody t.
generalize (method_error t Bt).
intros Ef.
rewrite bpow_plus, Rmult_assoc.
assert (exp x = pow2 (Zfloor k) * exp (x - k * ln 2)) as ->.
  assert (exists k', k = IZR k') as [k' ->] by (eexists ; apply Rmult_1_r).
  rewrite Zfloor_IZR, bpow_exp, <- exp_plus.
  apply f_equal.
  simpl ; ring.
rewrite <- Rmult_minus_distr_l.
rewrite Rdiv_compat_r.
2: apply Rgt_not_eq, bpow_gt_0.
2: apply Rgt_not_eq, exp_pos.
clearbody k.
revert Et.
generalize (x - k * ln 2).
clear x Fx Bx.
intros x Ex.
assert (Rabs ((exp t - exp x) / exp x) <= 33 * pow2 (-60)).
  unfold Rdiv.
  rewrite Rmult_minus_distr_r.
  rewrite Rinv_r by apply Rgt_not_eq, exp_pos.
  rewrite <- exp_Ropp, <- exp_plus.
  revert Ex.
  unfold Rminus ; generalize (t + - x) ; clear.
  intros r Hr ; interval with (i_prec 60).
apply rel_helper. apply Rgt_not_eq, exp_pos.
apply rel_helper in H. 2: apply Rgt_not_eq, exp_pos.
apply rel_helper in Ef. 2: apply Rgt_not_eq, exp_pos.
unfold t2, add, mul, sub, div, p0, p1, p2, q0, q1, q2 in * ; gappa.
Qed.

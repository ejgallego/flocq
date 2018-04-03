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

Require Import Reals Psatz.
Require Import Flocq.Core.Core Gappa.Gappa_tactic.

Open Scope R_scope.

Lemma Rdiv_le_l :
  forall a b c,
  0 < a -> b <= c / a -> a * b <= c.
Proof.
intros a b c Ha Hb.
apply Rmult_le_reg_r with (/a).
now apply Rinv_0_lt_compat.
replace (a * b * /a) with b.
exact Hb.
field.
now apply Rgt_not_eq.
Qed.

Lemma FIX_format_IZR :
  forall beta x, FIX_format beta 0 (IZR x).
Proof.
intros beta x.
exists (Float beta x 0).
apply sym_eq, Rmult_1_r.
apply eq_refl.
Qed.

Lemma Rmult_le_lt_reg_l :
  forall a b c d, 0 < a ->
  a * b <= a * c < a * d ->
  b <= c < d.
Proof.
intros a b c d Ha H.
split.
now apply Rmult_le_reg_l with (1 := Ha).
now apply Rmult_lt_reg_l with (1 := Ha).
Qed.

Lemma Rplus_le_lt_reg_r :
  forall a b c d,
  b + a <= c + a < d + a ->
  b <= c < d.
Proof.
intros a b c d H.
split.
now apply Rplus_le_reg_r with a.
now apply Rplus_lt_reg_r with a.
Qed.

Coercion IZR : Z >-> R.

Lemma IZR_le_le :
  forall a b c,
  (a <= b <= c)%Z ->
  a <= b <= c.
Proof.
intros a b c.
now split ; apply IZR_le.
Qed.

Notation pow2 := (bpow radix2).
Notation register_fmt := (FLT_exp (-65597) 64).
Notation fma x y z := (round radix2 register_fmt rndNE (x * y + z)).
Notation fnma x y z := (round radix2 register_fmt rndNE (z - x * y)).

Axiom frcpa : R -> R.
Axiom frcpa_spec : forall x : R,
  1 <= Rabs x <= 65536 ->
  generic_format radix2 (FLT_exp (-65597) 11) (frcpa x) /\
  Rabs (frcpa x - 1 / x) <= 4433 * pow2 (-21) * Rabs (1 / x).

Definition div_u16 a b :=
  let y0 := frcpa b in
  let q0 := fma a y0 0 in
  let e0 := fnma b y0 (1 + pow2 (-17)) in
  let q1 := fma e0 q0 q0 in
  Zfloor q1.

Lemma div_u16_spec : forall a b,
  (1 <= a <= 65535)%Z ->
  (1 <= b <= 65535)%Z ->
  div_u16 a b = (a / b)%Z.
Proof.
intros a b Ba Bb.
unfold div_u16.
set (y0 := frcpa b).
set (q0 := fma a y0 0).
set (e0 := fnma b y0 (1 + pow2 (-17))).
set (q1 := fma e0 q0 q0).
apply Zfloor_imp.
rewrite plus_IZR.
simpl.
apply Rmult_le_lt_reg_l with b.
  apply IZR_lt ; lia.
apply Rplus_le_lt_reg_r with (-a).
replace (b * (a / b)%Z + - a) with (-(a - (a / b)%Z * b)) by ring.
replace (b * ((a / b)%Z + 1) + - a) with (b - (a - (a / b)%Z * b)) by ring.
rewrite <- mult_IZR, <- minus_IZR.
rewrite <- Zmod_eq_full by lia.
cut (0 <= b * q1 - a < 1).
  cut (0 <= Zmod a b <= b - 1).
    lra.
  rewrite <- minus_IZR.
  apply IZR_le_le.
  generalize (Z_mod_lt a b).
  lia.
assert (Ba': 1 <= a <= 65535).
  now split ; apply IZR_le.
assert (Bb': 1 <= b <= 65535).
  now split ; apply IZR_le.
refine (let '(conj H1 H2) := _ in conj H1 (Rnot_le_lt _ _ H2)).
set (err := (q1 - a / b) / (a / b)).
replace (b * q1 - a) with (a * err) by abstract (unfold err ; field ; lra).
set (Mq0 := a * y0 + 0).
set (Me0 := 1 + pow2 (-17) - b * y0).
set (Mq1 := Me0 * Mq0 + Mq0).
set (eps0 := (y0 - 1 / b) / (1 / b)).
assert (H: (Mq1 - a / b) / (a / b) = -(eps0 * eps0) + (1 + eps0) * pow2 (-17))
  by abstract (unfold Mq1, Me0, Mq0, eps0 ; field ; lra).
revert H.
unfold Mq1, Me0, Mq0, eps0, err, q1, e0, q0, y0.
generalize (frcpa_spec b) (FIX_format_IZR radix2 a) (FIX_format_IZR radix2 b).
gappa.
Qed.

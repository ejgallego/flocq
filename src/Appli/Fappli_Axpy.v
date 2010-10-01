(*
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2010 Sylvie Boldo
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

Require Import Fcore.

Section Axpy.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable Hp : Zlt 0 prec.

(* FLX ou FLT ou aussi FTZ ou ? *)

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (canonic_exponent beta (FLX_exp prec)).
Notation ulp := (ulp beta (FLX_exp prec)).

Definition MinOrMax x f := 
   ((f = round beta (FLX_exp prec) rndDN x) 
     \/ (f = round beta (FLX_exp prec) rndUP x)).

Theorem MinOrMax_opp: forall x f,
   MinOrMax x f <->  MinOrMax (-x) (-f).
assert (forall x f, MinOrMax x f -> MinOrMax (- x) (- f)).
unfold MinOrMax; intros x f [H|H].
right.
now rewrite H, round_UP_opp.
left.
now rewrite H, round_DN_opp.
intros x f; split; intros H1.
now apply H.
rewrite <- (Ropp_involutive x), <- (Ropp_involutive f).
now apply H.
Qed.


Theorem implies_DN_lt_ulp:
  forall x f, format f ->
  (0 < f <= x)%R ->
  (Rabs (f-x) < ulp f)%R -> 
  (f = round beta (FLX_exp prec) rndDN x)%R.
intros x f Hf Hxf1 Hxf2.
apply sym_eq.
replace x with (f+-(f-x))%R by ring.
apply round_DN_succ; trivial.
apply Hxf1.
replace (- (f - x))%R with (Rabs (f-x)).
split; trivial; apply Rabs_pos.
rewrite Rabs_left1; trivial.
now apply Rle_minus.
Qed.

Theorem implies_MinOrMax_not_bpow:
  forall x f, format f ->
  (0 < f)%R ->
  f <> bpow (ln_beta beta f) ->
  (Rabs (f-x) < ulp f)%R -> 
  MinOrMax x f.
intros x f Hf1 Hf2 Hf3 Hxf1.
case (Rlt_or_le x f); intros Hxf2.
(* *)
(* assert (ulp (f-ulp f) = ulp f)%R.

admit.

right; apply sym_eq.
replace f with ((f-ulp f) + (ulp (f-ulp f)))%R.
2: rewrite H; ring.
replace x with ((f-ulp f)+-(f-ulp f-x))%R by ring.
apply round_UP_succ; trivial.

apply Hxf1.
replace (- (f - x))%R with (Rabs (f-x)).
split; trivial; apply Rabs_pos.
rewrite Rabs_left1; trivial.
now apply Rle_minus.
*)

admit.
(* *)
left.
apply  implies_DN_lt_ulp; try split; easy.
Qed.


Theorem implies_MinOrMax_bpow:
  forall x f, format f ->
  f = bpow (ln_beta beta f) ->
  (Rabs (f-x) < /2* ulp f)%R -> 
  MinOrMax x f.
intros x f Hf1 Hf2 Hxf.


Admitted.





Variable choice : R -> bool.

Variable a1 x1 y1 a x y:R.

Hypothesis Ha: format a.
Hypothesis Hx: format x.
Hypothesis Hy: format y.

Notation t := (round beta (FLX_exp prec) (rndN choice) (a*x)).
Notation u := (round beta (FLX_exp prec) (rndN choice) (t+y)).



Theorem Axpy_opt :
  (6 <= prec)%Z ->
 ((bpow 1 +1 + bpow (4-prec))* Rabs (a*x) <= Rabs y)%R ->
   (Rabs (y1 - y + a1 * x1 - a * x) <=
      bpow (1-prec) / (6*bpow 1) * Rabs y)%R ->
         (MinOrMax (a1 * x1 + y1) u).
Admitted.


End Axpy.
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

(** * Necessary conditions to compute a*x+y faithfully *)
Require Import Fcore.

Section Axpy.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable Hp : Zlt 0 prec.

(* FLX first - probably correct in FLTand maybe FTZ? *)

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (canonic_exp beta (FLX_exp prec)).
Notation ulp := (ulp beta (FLX_exp prec)).

Theorem pred_gt_0: forall f,
  format f -> (0 < f)%R -> (0 < pred beta (FLX_exp prec) f)%R.
intros f Hf Zf.
unfold pred, Fcore_ulp.ulp, canonic_exp, FLX_exp.
destruct (mag beta f) as (ef,Hef).
simpl.
assert (Zf2: (f <>0)%R) by now apply Rgt_not_eq.
specialize (Hef Zf2).
rewrite Rabs_right in Hef.
2: now apply Rgt_ge.
case (Zle_lt_or_eq 1 prec).
omega.
intros Hp1.
case Req_bool_spec; intros H; apply Rlt_Rminus;
    apply Rlt_le_trans with (2:=proj1 Hef);
    apply bpow_lt; omega.
(* special case for p = 1 *)
intros Hp1.
case Req_bool_spec; intros H; apply Rlt_Rminus.
apply Rlt_le_trans with (2:=proj1 Hef).
apply bpow_lt; omega.
rewrite <- Hp1.
case (proj1 Hef); trivial.
intros H'.
now contradict H.
Qed.


Definition MinOrMax x f :=
   ((f = round beta (FLX_exp prec) Zfloor x)
     \/ (f = round beta (FLX_exp prec) Zceil x)).

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
  (f = round beta (FLX_exp prec) Zfloor x)%R.
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

Theorem MinOrMax_ulp_pred:
  forall x f, format f ->
  (0 < f)%R ->
  (Rabs (f-x) < ulp (pred beta (FLX_exp prec) f))%R ->
  MinOrMax x f.
intros x f Ff Zf Hf.
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
apply  implies_DN_lt_ulp; trivial.
now split.
apply Rlt_le_trans with (1:=Hf).
apply ulp_monotone.
clear; intros m n H.
unfold FLX_exp.
omega.
now apply pred_gt_0.
left.
apply pred_lt.
Qed.


Theorem implies_MinOrMax_bpow:
  forall x f, format f ->
  f = bpow (mag beta f) ->
  (Rabs (f-x) < /2* ulp f)%R ->
  MinOrMax x f.
intros x f Hf1 Hf2 Hxf.


Admitted.





Variable choice : Z -> bool.

Variable a1 x1 y1 a x y:R.

Hypothesis Ha: format a.
Hypothesis Hx: format x.
Hypothesis Hy: format y.

Notation t := (round beta (FLX_exp prec) (Znearest choice) (a*x)).
Notation u := (round beta (FLX_exp prec) (Znearest choice) (t+y)).

(*
Axpy_aux1 : lemma Closest?(b)(a*x,t) => Closest?(b)(t+y,u) => 0 < u
   => abs(t-a*x)          <=  Fulp(b)(Fpred(b)(u))/4
   => abs(y1-y+a1*x1-a*x) <   Fulp(b)(Fpred(b)(u))/4
   => MinOrMax?(y1+a1*x1,u)


Axpy_aux1_aux1 : lemma Closest?(b)(a*x,t) => Closest?(b)(t+y,u) => 0 < u
  => Fnormal?(b)(t) => radix*abs(t) <= Fpred(b)(u)
  => abs(t-a*x)  <=  Fulp(b)(Fpred(b)(u))/4

Axpy_aux1_aux2 : lemma Closest?(b)(a*x,t) => Closest?(b)(t+y,u) => 0 < u
  => Fsubnormal?(b)(t) => 1-dExp(b) <= Fexp(Fpred(b)(u))
  => abs(t-a*x) <=  Fulp(b)(Fpred(b)(u))/4

Axpy_aux2 : lemma Closest?(b)(a*x,t) => Closest?(b)(t+y,u) => 0 < u
  => Fsubnormal?(b)(t) => u=t+y
  => abs(y1-y+a1*x1-a*x) < Fulp(b)(Fpred(b)(u))/4
  => MinOrMax?(y1+a1*x1,u)


Axpy_aux3 : lemma Closest?(b)(a*x,t) => Closest?(b)(t+y,u) => 0 < u
  => Fsubnormal?(b)(t)
  => -dExp(b) = Fexp(Fpred(b)(u)) =>  1-dExp(b) <= Fexp(u)
  => abs(y1-y+a1*x1-a*x) < Fulp(b)(Fpred(b)(u))/4
  => MinOrMax?(y1+a1*x1,u)


AxpyPos : lemma Closest?(b)(a*x,t) => Closest?(b)(t+y,u) => 0 < u
  => (Fnormal?(b)(t) => radix*abs(t) <= Fpred(b)(u))
  => abs(y1-y+a1*x1-a*x) < Fulp(b)(Fpred(b)(u))/4
  => MinOrMax?(y1+a1*x1,u)

Axpy_opt_aux1_aux1 : lemma Fnormal?(b)(t) => Fnormal?(b)(u) => 0 < u
    => Prec(b) >= 3 =>
   (1+radix*(1+1/(2*abs(Fnum(u))))*(1+1/abs(Fnum(Fpred(b)(u)))))/(1-1/(2*abs(Fnum(t))))
      <= 1+radix+radix^(4-Prec(b))

Axpy_opt_aux1 : lemma Closest?(b)(a*x,t) => Closest?(b)(t+y,u) => 0 < u
  =>  Prec(b) >= 3 => Fnormal?(b)(t)
  => (radix+1+radix^(4-Prec(b)))*abs(a*x) <= abs(y)
  =>  radix*abs(t) <= Fpred(b)(u)

Axpy_opt_aux2 : lemma  Closest?(b)(a*x,t) => Closest?(b)(t+y,u) => 0 < u
  =>  Prec(b) >= 6 =>  Fnormal?(b)(t)
  => (radix+1+radix^(4-Prec(b)))*abs(a*x) <= abs(y)
  =>  abs(y)*radix^(1-Prec(b))/(radix+1) < Fulp(b)(Fpred(b)(u))

Axpy_opt_aux3 : lemma  Closest?(b)(a*x,t) => Closest?(b)(t+y,u) => 0 < u
  =>  Prec(b) >= 3  =>  Fsubnormal?(b)(t)
  => (radix+1+radix^(4-Prec(b)))*abs(a*x) <= abs(y)
  =>  abs(y)*radix^(1-Prec(b))/(radix+radix/2) <= Fulp(b)(Fpred(b)(u))


Axpy_optPos : lemma Closest?(b)(a*x,t) => Closest?(b)(t+y,u) => 0 < u
  => Prec(b) >= 6
  => (radix+1+radix^(4-Prec(b)))*abs(a*x) <= abs(y)
  => abs(y1-y+a1*x1-a*x) < abs(y)*radix^(1-Prec(b))/(6*radix)
  => MinOrMax?(y1+a1*x1,u)

Axpy_optZero : lemma Closest?(b)(a*x,t) => Closest?(b)(t+y,u) => 0 = u
  => (radix+1+radix^(4-Prec(b)))*abs(a*x) <= abs(y)
  => abs(y1-y+a1*x1-a*x) < abs(y)*radix^(1-Prec(b))/(6*radix)
  => MinOrMax?(y1+a1*x1,u)

Axpy_opt : lemma Closest?(b)(a*x,t) => Closest?(b)(t+y,u)
  => Prec(b) >= 6
  => (radix+1+radix^(4-Prec(b)))*abs(a*x) <= abs(y)
  => abs(y1-y+a1*x1-a*x) < abs(y)*radix^(1-Prec(b))/(6*radix)
  => MinOrMax?(y1+a1*x1,u)

Axpy_simpl : lemma Closest?(b)(a*x,t) => Closest?(b)(t+y,u)
  => Prec(b) >= 24 => radix=2
  => (3+1/100000)*abs(a*x) <= abs(y)
  => abs(y1-y+a1*x1-a*x) < abs(y)*2^(1-Prec(b))/12
  => MinOrMax?(y1+a1*x1,u)
*)

Theorem Axpy_opt :
  (6 <= prec)%Z ->
 ((bpow 1 +1 + bpow (4-prec))* Rabs (a*x) <= Rabs y)%R ->
   (Rabs (y1 - y + a1 * x1 - a * x) <=
      bpow (1-prec) / (6*bpow 1) * Rabs y)%R ->
         (MinOrMax (a1 * x1 + y1) u).
Admitted.


End Axpy.
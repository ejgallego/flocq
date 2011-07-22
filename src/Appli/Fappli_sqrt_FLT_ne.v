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

Require Import Fcore.
Require Import Fcalc_bracket.
Require Import Fcalc_round.
Require Import Fcalc_sqrt.

Section test.

Variable beta : radix.
Variable prec emin : Z.
Variable Hprec : (1 < prec)%Z.

Definition Fsqrt_FLT_ne (f : float beta) :=
  let '(Float m e) := f in
  if Zle_bool m 0 then Float beta 0 0
  else
    let '(m', e', l) := truncate beta (FLT_exp emin prec) (Fsqrt_core beta prec m e) in
    Float beta (cond_incr (round_N (negb (Zeven m')) l) m') e'.

Theorem Fsqrt_FLT_ne_correct :
  forall x,
  Rnd_NE_pt beta (FLT_exp emin prec) (sqrt (F2R x)) (F2R (Fsqrt_FLT_ne x)).
Proof.
intros x.
replace (F2R (Fsqrt_FLT_ne x)) with (round beta (FLT_exp emin prec) rndNE (sqrt (F2R x))).
apply round_NE_pt_FLT.
omega.
now right.
unfold Fsqrt_FLT_ne.
destruct x as (mx, ex).
generalize (Zle_cases mx 0).
case (Zle_bool mx 0) ; intros Hm.
(* mx = 0 *)
rewrite F2R_0.
replace (sqrt (F2R (Float beta mx ex))) with R0.
apply round_0.
destruct (Zle_lt_or_eq _ _ Hm) as [Hm'|Hm'].
unfold sqrt.
case Rcase_abs ; intros Hs.
easy.
elim Rge_not_lt with (1 := Hs).
now apply F2R_lt_0_compat.
rewrite Hm', F2R_0.
now rewrite sqrt_0.
(* 0 < mx *)
generalize (Fsqrt_core_correct beta prec mx ex (Zgt_lt _ _ Hm)).
destruct (Fsqrt_core beta prec mx ex) as ((ms, es), ls).
intros (H1, H2).
assert (Hp : (0 < prec)%Z) by omega.
generalize (@round_trunc_NE_correct beta _  (FLT_exp_valid emin prec Hp) (sqrt (F2R (Float beta mx ex))) ms es ls).
destruct (truncate beta (FLT_exp emin prec) (ms, es, ls)) as ((mr, er), lr).
intros Hr. apply Hr. clear Hr.
apply sqrt_ge_0.
apply H2.
left.
unfold FLT_exp.
generalize (Zmax_spec (Fcalc_digits.digits beta ms + es - prec) emin).
omega.
Qed.

End test.

Definition radix10 : radix.
now refine (Build_radix 10 _).
Defined.

(* Time Eval vm_compute in (Fsqrt radix10 20 (-15) (Float radix10 2 0)). *)

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

(** * Fixed-point format *)
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_rnd_ne.

Section RND_FIX.

Variable beta : radix.

Notation bpow := (bpow beta).

Variable emin : Z.

(* fixed-point format with exponent emin *)
Definition FIX_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Fexp f = emin)%Z.

Definition FIX_RoundingModeP (rnd : R -> R):=
  Rounding_for_Format FIX_format rnd.

Definition FIX_exp (e : Z) := emin.

(** Properties of the FIX format *)
Theorem FIX_exp_correct : valid_exp FIX_exp.
Proof.
intros k.
unfold FIX_exp.
split ; intros H.
now apply Zlt_le_weak.
split.
apply Zle_refl.
now intros _ _.
Qed.

Theorem FIX_format_generic :
  forall x : R, FIX_format x <-> generic_format beta FIX_exp x.
Proof.
split.
(* . *)
intros ((xm, xe), (Hx1, Hx2)).
rewrite Hx1.
now apply generic_format_canonic.
(* . *)
intros H.
rewrite H.
eexists ; repeat split.
Qed.

Theorem FIX_format_satisfies_any :
  satisfies_any FIX_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FIX_exp _)).
intros x.
apply iff_sym.
apply FIX_format_generic.
exact FIX_exp_correct.
Qed.

Theorem Rnd_NE_pt_FIX :
  round_pred (Rnd_NE_pt beta FIX_exp).
Proof.
apply Rnd_NE_pt_round.
apply FIX_exp_correct.
right.
split ; easy.
Qed.

Theorem FIX_not_FTZ :
  not_FTZ_prop FIX_exp.
Proof.
intros e.
apply Zle_refl.
Qed.

End RND_FIX.

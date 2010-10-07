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

(** * Helper function for computing the rounded value of a real number. *)

Require Import Fcore.
Require Import Fcalc_bracket.
Require Import Fcalc_digits.

Section Fcalc_round.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.
Notation format := (generic_format beta fexp).

(** Relates location and rounding. *)

Theorem inbetween_float_round :
  forall rnd choice,
  ( forall x m l, inbetween_int m x l -> Zrnd rnd x = choice m l ) ->
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rnd x = F2R (Float beta (choice m l) e).
Proof.
intros rnd choice Hc x m l e Hl.
unfold round, F2R. simpl.
apply (f_equal (fun m => (Z2R m * bpow e)%R)).
apply Hc.
apply inbetween_mult_reg with (bpow e).
apply bpow_gt_0.
now rewrite scaled_mantissa_bpow.
Qed.

(** Relates location and rounding down. *)

Theorem inbetween_float_DN :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rndDN x = F2R (Float beta m e).
Proof.
apply inbetween_float_round with (choice := fun m l => m).
intros x m l Hl.
refine (Zfloor_imp m _ _).
apply inbetween_bounds with (2 := Hl).
apply Z2R_lt.
apply Zlt_succ.
Qed.

(** Relates location and rounding up. *)

Definition cond_incr (b : bool) m := if b then (m + 1)%Z else m.

Definition round_UP l :=
  match l with
  | loc_Exact => false
  | _ => true
  end.

Theorem inbetween_float_UP :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rndUP x = F2R (Float beta (cond_incr (round_UP l) m) e).
Proof.
apply inbetween_float_round with (choice := fun m l => cond_incr (round_UP l) m).
intros x m l Hl.
assert (Hl': l = loc_Exact \/ (l <> loc_Exact /\ round_UP l = true)).
case l ; try (now left) ; now right ; split.
destruct Hl' as [Hl'|(Hl1, Hl2)].
(* Exact *)
rewrite Hl'.
destruct Hl ; try easy.
rewrite H.
exact (Zceil_Z2R _).
(* not Exact *)
rewrite Hl2.
simpl.
apply Zceil_imp.
ring_simplify (m + 1 - 1)%Z.
refine (let H := _ in conj (proj1 H) (Rlt_le _ _ (proj2 H))).
apply inbetween_bounds_not_Eq with (2 := Hl1) (1 := Hl).
Qed.

(** Relates location and rounding to nearest even. *)

Definition round_NE (p : bool) l :=
  match l with
  | loc_Exact => false
  | loc_Inexact Lt => false
  | loc_Inexact Eq => if p then false else true
  | loc_Inexact Gt => true
  end.

Theorem inbetween_float_NE :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rndNE x = F2R (Float beta (cond_incr (round_NE (Zeven m) l) m) e).
Proof.
apply inbetween_float_round with (choice := fun m l => cond_incr (round_NE (Zeven m) l) m).
intros x m l Hl.
inversion_clear Hl as [Hx|l' Hx Hl'].
(* Exact *)
rewrite Hx.
now rewrite Zrnd_Z2R.
(* not Exact *)
unfold Zrnd, rndNE, rndN, Znearest.
assert (Hm: Zfloor x = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
rewrite Zceil_floor_neq.
rewrite Hm.
replace (Rcompare (x - Z2R m) (/2)) with l'.
now case l'.
rewrite <- Hl'.
rewrite Z2R_plus.
rewrite <- (Rcompare_plus_r (- Z2R m) x).
apply f_equal.
simpl (Z2R 1).
field.
rewrite Hm.
now apply Rlt_not_eq.
Qed.

(** Given a triple (mantissa, exponent, position), this function
    computes a triple with a canonic exponent, assuming the
    original triple had enough precision. *)

Definition truncate t :=
  let '(m, e, l) := t in
  let k := (fexp (digits beta m + e) - e)%Z in
  if Zlt_bool 0 k then
    let p := Zpower beta k in
    (Zdiv m p, (e + k)%Z, new_location p (Zmod m p) l)
  else t.

Theorem truncate_correct :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (digits beta m + e))%Z \/ l = loc_Exact ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = canonic_exponent beta fexp x \/ (l' = loc_Exact /\ format x)).
Proof.
intros x m e l Hx H1 H2.
unfold truncate.
set (k := (fexp (digits beta m + e) - e)%Z).
set (p := Zpower beta k).
(* *)
assert (Hx': (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R).
apply inbetween_bounds with (2 := H1).
apply F2R_lt_compat.
apply Zlt_succ.
(* *)
assert (Hm: (0 <= m)%Z).
cut (0 < m + 1)%Z. omega.
apply F2R_lt_reg with beta e.
rewrite F2R_0.
apply Rle_lt_trans with  (1 := Hx).
apply Hx'.
destruct Hx as [Hx|Hx].
(* . 0 < x *)
assert (He: (e + k = canonic_exponent beta fexp x)%Z).
(* .. *)
unfold canonic_exponent.
destruct (Zle_lt_or_eq _ _ Hm) as [Hm'|Hm'].
(* ... 0 < m *)
rewrite ln_beta_F2R_bounds with (1 := Hm') (2 := Hx').
assert (H: m <> Z0).
apply sym_not_eq.
now apply Zlt_not_eq.
rewrite ln_beta_F2R with (1 := H).
rewrite <- digits_ln_beta with (1 := H).
unfold k.
ring.
destruct H2 as [H2|H2].
(* ... m = 0 and enough digits *)
rewrite <- Hm' in H2.
destruct (ln_beta beta x) as (ex, Hex).
simpl.
specialize (Hex (Rgt_not_eq _ _ Hx)).
unfold k.
ring_simplify.
rewrite <- Hm'.
simpl.
apply sym_eq.
apply (proj2 (prop_exp e)).
exact H2.
apply Zle_trans with e.
eapply bpow_lt_bpow.
apply Rle_lt_trans with (1 := proj1 Hex).
rewrite Rabs_pos_eq.
rewrite <- F2R_bpow.
rewrite <- Hm' in Hx'.
apply Hx'.
now apply Rlt_le.
exact H2.
(* ... m = 0 and exact location *)
rewrite H2 in H1.
inversion_clear H1.
rewrite <- Hm', F2R_0 in H.
rewrite H in Hx.
elim Rlt_irrefl with (1 := Hx).
(* .. *)
generalize (Zlt_cases 0 k).
case (Zlt_bool 0 k) ; intros Hk ; unfold k in Hk.
(* ... shift *)
split.
now apply inbetween_float_new_location.
now left.
split.
exact H1.
destruct H2 as [H2|H2].
left.
rewrite <- He.
unfold k.
omega.
(* ... no shift *)
right.
split.
exact H2.
rewrite H2 in H1.
inversion_clear H1.
rewrite H.
apply generic_format_canonic_exponent.
rewrite <- H, <- He.
unfold k.
omega.
(* . x = 0 *)
destruct H1 as [H1|l' H1 _].
(* .. exact location *)
case (Zlt_bool 0 k).
(* ... shift *)
assert (Hm': m = Z0).
apply F2R_eq_0_reg with beta e.
rewrite <- H1.
now apply sym_eq.
rewrite Hm'.
rewrite Zdiv_0_l, Zmod_0_l.
replace (new_location p 0 loc_Exact) with loc_Exact.
split.
constructor.
rewrite F2R_0.
now apply sym_eq.
right.
repeat split.
rewrite <- Hx.
apply generic_format_0.
unfold new_location.
case (Zeven p) ; [ unfold new_location_even | unfold new_location_odd ] ;
  ( case Zeq_bool_spec ; [ easy | intros H ; now elim H ] ).
(* ... no shift *)
split.
now constructor.
right.
repeat split.
rewrite <- Hx.
apply generic_format_0.
(* .. inexact location *)
elim Rlt_not_le with (1 := proj1 H1).
rewrite <- Hx.
now apply F2R_ge_0_compat.
Qed.

Section round_dir.

Variable rnd: Zround.
Variable choice : Z -> location -> Z.
Hypothesis choice_valid : forall m, choice m loc_Exact = m.
Hypothesis inbetween_float_valid :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rnd x = F2R (Float beta (choice m l) e).

Theorem round_any_correct :
  forall x m e l,
  inbetween_float beta m e x l ->
  (e = canonic_exponent beta fexp x \/ (l = loc_Exact /\ format x)) ->
  round beta fexp rnd x = F2R (Float beta (choice m l) e).
Proof.
intros x m e l Hin [He|(Hl,Hf)].
rewrite He in Hin |- *.
apply inbetween_float_valid with (1 := Hin).
rewrite Hl in Hin.
inversion_clear Hin.
rewrite Hl, choice_valid.
rewrite <- H.
now apply round_generic.
Qed.

(** Truncating a triple is sufficient to round a real number. *)

Theorem round_trunc_any_correct :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (digits beta m + e))%Z \/ l = loc_Exact ->
  round beta fexp rnd x = let '(m', e', l') := truncate (m, e, l) in F2R (Float beta (choice m' l') e').
Proof.
intros x m e l Hx Hl He.
generalize (truncate_correct x m e l Hx Hl He).
destruct (truncate (m, e, l)) as ((m', e'), l').
intros (H1, H2).
now apply round_any_correct.
Qed.

End round_dir.

(** * Instances of the theorems above, for the usual rounding modes. *)

Definition round_DN_correct :=
  round_any_correct _ (fun m _ => m)
    (fun _ => refl_equal _) inbetween_float_DN.

Definition round_trunc_DN_correct :=
  round_trunc_any_correct _ (fun m _ => m)
    (fun _ => refl_equal _) inbetween_float_DN.

Definition round_UP_correct :=
  round_any_correct _ (fun m l => cond_incr (round_UP l) m)
    (fun _ => refl_equal _) inbetween_float_UP.

Definition round_trunc_UP_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_UP l) m)
    (fun _ => refl_equal _) inbetween_float_UP.

Definition round_NE_correct :=
  round_any_correct _ (fun m l => cond_incr (round_NE (Zeven m) l) m)
    (fun _ => refl_equal _) inbetween_float_NE.

Definition round_trunc_NE_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_NE (Zeven m) l) m)
    (fun _ => refl_equal _) inbetween_float_NE.

End Fcalc_round.

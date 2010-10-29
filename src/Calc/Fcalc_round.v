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

Section Fcalc_round_fexp.

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

Definition cond_Zopp (b : bool) m := if b then Zopp m else m.
Definition cond_incr (b : bool) m := if b then (m + 1)%Z else m.

Theorem inbetween_float_round_sign :
  forall rnd choice,
  ( forall x m l, inbetween_int m (Rabs x) l ->
    Zrnd rnd x = cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l) ) ->
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp rnd x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l)) e).
Proof.
intros rnd choice Hc x m l e Hx.
apply (f_equal (fun m => (Z2R m * bpow e)%R)).
simpl.
replace (Rlt_bool x 0) with (Rlt_bool (scaled_mantissa beta fexp x) 0).
(* *)
apply Hc.
apply inbetween_mult_reg with (bpow e).
apply bpow_gt_0.
rewrite <- (Rabs_right (bpow e)) at 3.
rewrite <- Rabs_mult.
now rewrite scaled_mantissa_bpow.
apply Rle_ge.
apply bpow_ge_0.
(* *)
destruct (Rlt_bool_spec x 0) as [Zx|Zx] ; simpl.
apply Rlt_bool_true.
rewrite <- (Rmult_0_l (bpow (-e))).
apply Rmult_lt_compat_r with (2 := Zx).
apply bpow_gt_0.
apply Rlt_bool_false.
apply Rmult_le_pos with (1 := Zx).
apply bpow_ge_0.
Qed.

(** Relates location and rounding down. *)

Theorem inbetween_int_DN :
  forall x m l,
  inbetween_int m x l ->
  Zrnd rndDN x = m.
Proof.
intros x m l Hl.
refine (Zfloor_imp m _ _).
apply inbetween_bounds with (2 := Hl).
apply Z2R_lt.
apply Zlt_succ.
Qed.

Theorem inbetween_float_DN :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rndDN x = F2R (Float beta m e).
Proof.
apply inbetween_float_round with (choice := fun m l => m).
exact inbetween_int_DN.
Qed.

Definition round_sign_DN s l :=
  match l with
  | loc_Exact => false
  | _ => s
  end.

Theorem inbetween_int_DN_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  Zrnd rndDN x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_DN (Rlt_bool x 0) l) m).
Proof.
intros x m l Hl.
unfold Rabs in Hl.
destruct (Rcase_abs x) as [Zx|Zx] .
(* *)
rewrite Rlt_bool_true with (1 := Zx).
inversion_clear Hl ; simpl.
rewrite <- (Ropp_involutive x).
rewrite H, <- Z2R_opp.
apply Zfloor_Z2R.
apply Zfloor_imp.
split.
apply Rlt_le.
rewrite Z2R_opp.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
ring_simplify (- (m + 1) + 1)%Z.
rewrite Z2R_opp.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
(* *)
rewrite Rlt_bool_false.
inversion_clear Hl ; simpl.
rewrite H.
apply Zfloor_Z2R.
apply Zfloor_imp.
split.
now apply Rlt_le.
apply H.
now apply Rge_le.
Qed.

Theorem inbetween_float_DN_sign :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp rndDN x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_DN (Rlt_bool x 0) l) m)) e).
Proof.
apply inbetween_float_round_sign with (choice := fun s m l => cond_incr (round_sign_DN s l) m).
exact inbetween_int_DN_sign.
Qed.

(** Relates location and rounding up. *)

Definition round_UP l :=
  match l with
  | loc_Exact => false
  | _ => true
  end.

Theorem inbetween_int_UP :
  forall x m l,
  inbetween_int m x l ->
  Zrnd rndUP x = cond_incr (round_UP l) m.
Proof.
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

Theorem inbetween_float_UP :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rndUP x = F2R (Float beta (cond_incr (round_UP l) m) e).
Proof.
apply inbetween_float_round with (choice := fun m l => cond_incr (round_UP l) m).
exact inbetween_int_UP.
Qed.

Definition round_sign_UP s l :=
  match l with
  | loc_Exact => false
  | _ => negb s
  end.

Theorem inbetween_int_UP_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  Zrnd rndUP x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_UP (Rlt_bool x 0) l) m).
Proof.
intros x m l Hl.
unfold Rabs in Hl.
destruct (Rcase_abs x) as [Zx|Zx] .
(* *)
rewrite Rlt_bool_true with (1 := Zx).
simpl.
unfold Zceil.
apply f_equal.
inversion_clear Hl ; simpl.
rewrite H.
apply Zfloor_Z2R.
apply Zfloor_imp.
split.
now apply Rlt_le.
apply H.
(* *)
rewrite Rlt_bool_false.
simpl.
inversion_clear Hl ; simpl.
rewrite H.
apply Zceil_Z2R.
apply Zceil_imp.
split.
change (m + 1 - 1)%Z with (Zpred (Zsucc m)).
now rewrite <- Zpred_succ.
now apply Rlt_le.
now apply Rge_le.
Qed.

Theorem inbetween_float_UP_sign :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp rndUP x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_UP (Rlt_bool x 0) l) m)) e).
Proof.
apply inbetween_float_round_sign with (choice := fun s m l => cond_incr (round_sign_UP s l) m).
exact inbetween_int_UP_sign.
Qed.

(** Relates location and rounding toward zero. *)

Definition round_ZR (s : bool) l :=
  match l with
  | loc_Exact => false
  | _ => s
  end.

Theorem inbetween_int_ZR :
  forall x m l,
  inbetween_int m x l ->
  Zrnd rndZR x = cond_incr (round_ZR (Zlt_bool m 0) l) m.
Proof.
intros x m l Hl.
inversion_clear Hl as [Hx|l' Hx Hl'].
(* Exact *)
rewrite Hx.
now rewrite Zrnd_Z2R.
(* not Exact *)
unfold Zrnd, rndZR, Ztrunc.
assert (Hm: Zfloor x = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
rewrite Zceil_floor_neq.
rewrite Hm.
unfold cond_incr.
simpl.
generalize (Zlt_cases m 0).
destruct (Rlt_le_dec x 0) as [Hx'|Hx'] ;
  case (Zlt_bool m 0) ; try easy ; intros Hm'.
elim Rlt_not_le with (1 := Hx').
apply Rlt_le.
apply Rle_lt_trans with (2 := proj1 Hx).
apply (Z2R_le 0).
now apply Zge_le.
elim Rle_not_lt with (1 := Hx').
apply Rlt_le_trans with (1 := proj2 Hx).
apply (Z2R_le _ 0).
now apply Zlt_le_succ.
rewrite Hm.
now apply Rlt_not_eq.
Qed.

Theorem inbetween_float_ZR :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rndZR x = F2R (Float beta (cond_incr (round_ZR (Zlt_bool m 0) l) m) e).
Proof.
apply inbetween_float_round with (choice := fun m l => cond_incr (round_ZR (Zlt_bool m 0) l) m).
exact inbetween_int_ZR.
Qed.

Theorem inbetween_int_ZR_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  Zrnd rndZR x = cond_Zopp (Rlt_bool x 0) m.
Proof.
intros x m l Hl.
simpl.
unfold Ztrunc.
destruct (Rlt_le_dec x 0) as [Zx|Zx].
(* *)
rewrite Rlt_bool_true with (1 := Zx).
simpl.
unfold Zceil.
apply f_equal.
apply Zfloor_imp.
rewrite <- Rabs_left with (1 := Zx).
apply inbetween_bounds with (2 := Hl).
apply Z2R_lt.
apply Zlt_succ.
(* *)
rewrite Rlt_bool_false with (1 := Zx).
simpl.
apply Zfloor_imp.
rewrite <- Rabs_pos_eq with (1 := Zx).
apply inbetween_bounds with (2 := Hl).
apply Z2R_lt.
apply Zlt_succ.
Qed.

Theorem inbetween_float_ZR_sign :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp rndZR x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) m) e).
Proof.
apply inbetween_float_round_sign with (choice := fun s m l => m).
exact inbetween_int_ZR_sign.
Qed.

(** Relates location and rounding to nearest even. *)

Definition round_NE (p : bool) l :=
  match l with
  | loc_Exact => false
  | loc_Inexact Lt => false
  | loc_Inexact Eq => if p then false else true
  | loc_Inexact Gt => true
  end.

Theorem inbetween_int_NE :
  forall x m l,
  inbetween_int m x l ->
  Zrnd rndNE x = cond_incr (round_NE (Zeven m) l) m.
Proof.
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

Theorem inbetween_float_NE :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rndNE x = F2R (Float beta (cond_incr (round_NE (Zeven m) l) m) e).
Proof.
apply inbetween_float_round with (choice := fun m l => cond_incr (round_NE (Zeven m) l) m).
exact inbetween_int_NE.
Qed.

Theorem inbetween_int_NE_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  Zrnd rndNE x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_NE (Zeven m) l) m).
Proof.
intros x m l Hl.
simpl.
unfold Rabs in Hl.
destruct (Rcase_abs x) as [Zx|Zx].
(* *)
rewrite Rlt_bool_true with (1 := Zx).
simpl.
rewrite <- (Ropp_involutive x).
rewrite Znearest_opp.
apply f_equal.
inversion_clear Hl as [Hx|l' Hx Hl'].
rewrite Hx.
apply Znearest_Z2R.
assert (Hm: Zfloor (-x) = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
unfold Znearest.
rewrite Zceil_floor_neq.
rewrite Hm.
replace (Rcompare (- x - Z2R m) (/2)) with l'.
case l' ; try easy.
rewrite Bool.negb_involutive, Zeven_opp, Zeven_plus.
now case (Zeven m).
rewrite <- Hl'.
rewrite Z2R_plus.
rewrite <- (Rcompare_plus_r (- Z2R m) (-x)).
apply f_equal.
simpl (Z2R 1).
field.
rewrite Hm.
now apply Rlt_not_eq.
(* *)
rewrite Rlt_bool_false.
simpl.
inversion_clear Hl as [Hx|l' Hx Hl'].
rewrite Hx.
apply Znearest_Z2R.
assert (Hm: Zfloor x = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
unfold Znearest.
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
now apply Rge_le.
Qed.

Theorem inbetween_float_NE_sign :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp rndNE x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_NE (Zeven m) l) m)) e).
Proof.
apply inbetween_float_round_sign with (choice := fun s m l => cond_incr (round_NE (Zeven m) l) m).
exact inbetween_int_NE_sign.
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
Hypothesis inbetween_int_valid :
  forall x m l,
  inbetween_int m x l ->
  Zrnd rnd x = choice m l.

Theorem round_any_correct :
  forall x m e l,
  inbetween_float beta m e x l ->
  (e = canonic_exponent beta fexp x \/ (l = loc_Exact /\ format x)) ->
  round beta fexp rnd x = F2R (Float beta (choice m l) e).
Proof.
intros x m e l Hin [He|(Hl,Hf)].
rewrite He in Hin |- *.
apply inbetween_float_round with (2 := Hin).
exact inbetween_int_valid.
rewrite Hl in Hin.
inversion_clear Hin.
rewrite Hl.
replace (choice m loc_Exact) with m.
rewrite <- H.
now apply round_generic.
rewrite <- (Zrnd_Z2R rnd m) at 1.
apply inbetween_int_valid.
now constructor.
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
  round_any_correct _ (fun m _ => m) inbetween_int_DN.

Definition round_trunc_DN_correct :=
  round_trunc_any_correct _ (fun m _ => m) inbetween_int_DN.

Definition round_UP_correct :=
  round_any_correct _ (fun m l => cond_incr (round_UP l) m) inbetween_int_UP.

Definition round_trunc_UP_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_UP l) m) inbetween_int_UP.

Definition round_ZR_correct :=
  round_any_correct _ (fun m l => cond_incr (round_ZR (Zlt_bool m 0) l) m) inbetween_int_ZR.

Definition round_trunc_ZR_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_ZR (Zlt_bool m 0) l) m) inbetween_int_ZR.

Definition round_NE_correct :=
  round_any_correct _ (fun m l => cond_incr (round_NE (Zeven m) l) m) inbetween_int_NE.

Definition round_trunc_NE_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_NE (Zeven m) l) m) inbetween_int_NE.

End Fcalc_round_fexp.

(** Specialization of truncate for FIX formats. *)

Variable emin : Z.

Definition truncate_FIX t :=
  let '(m, e, l) := t in
  let k := (emin - e)%Z in
  if Zlt_bool 0 k then
    let p := Zpower beta k in
    (Zdiv m p, (e + k)%Z, new_location p (Zmod m p) l)
  else t.

Theorem truncate_FIX_correct :
  forall x m e l,
  inbetween_float beta m e x l ->
  (e <= emin)%Z \/ l = loc_Exact ->
  let '(m', e', l') := truncate_FIX (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = canonic_exponent beta (FIX_exp emin) x \/ (l' = loc_Exact /\ generic_format beta (FIX_exp emin) x)).
Proof.
intros x m e l H1 H2.
unfold truncate_FIX.
set (k := (emin - e)%Z).
set (p := Zpower beta k).
unfold canonic_exponent, FIX_exp.
generalize (Zlt_cases 0 k).
case (Zlt_bool 0 k) ; intros Hk.
(* shift *)
split.
now apply inbetween_float_new_location.
clear H2.
left.
unfold k.
ring.
(* no shift *)
split.
exact H1.
unfold k in Hk.
destruct H2 as [H2|H2].
left.
omega.
right.
split.
exact H2.
rewrite H2 in H1.
inversion_clear H1.
rewrite H.
apply generic_format_canonic_exponent.
unfold canonic_exponent.
omega.
Qed.

End Fcalc_round.

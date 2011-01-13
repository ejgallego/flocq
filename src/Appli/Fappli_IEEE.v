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

(** * IEEE-754 arithmetic *)
Require Import Fcore.
Require Import Fcalc_digits.
Require Import Fcalc_round.
Require Import Fcalc_bracket.
Require Import Fcalc_ops.
Require Import Fcalc_div.
Require Import Fcalc_sqrt.
Require Import Fprop_relative.

Section Binary.

Variable prec emax : Z.
Hypothesis Hprec : (0 < prec)%Z.
Hypothesis Hmax : (prec < emax)%Z.

Let emin := (3 - emax - prec)%Z.
Let fexp := FLT_exp emin prec.
Let fexp_correct : valid_exp fexp := FLT_exp_correct _ _ Hprec.

Definition bounded_prec m e :=
  Zeq_bool (fexp (Z_of_nat (S (digits2_Pnat m)) + e)) e.

Definition bounded m e :=
  andb (bounded_prec m e) (Zle_bool e (emax - prec)).

Inductive binary_float :=
  | B754_zero : bool -> binary_float
  | B754_infinity : bool -> binary_float
  | B754_nan : binary_float
  | B754_finite : bool ->
    forall (m : positive) (e : Z), bounded m e = true -> binary_float.

Definition radix2 := Build_radix 2 (refl_equal true).

Definition B2R f :=
  match f with
  | B754_finite s m e _ => F2R (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => R0
  end.

Theorem canonic_bounded_prec :
  forall (sx : bool) mx ex,
  bounded_prec mx ex = true ->
  canonic radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof.
intros sx mx ex H.
assert (Hx := Zeq_bool_eq _ _ H). clear H.
apply sym_eq.
simpl.
pattern ex at 2 ; rewrite <- Hx.
apply (f_equal fexp).
rewrite ln_beta_F2R_digits.
rewrite <- digits_abs.
rewrite Z_of_nat_S_digits2_Pnat.
now case sx.
now case sx.
Qed.

Theorem generic_format_B2R :
  forall x,
  generic_format radix2 fexp (B2R x).
Proof.
intros [sx|sx| |sx mx ex Hx] ; try apply generic_format_0.
simpl.
apply generic_format_canonic.
apply canonic_bounded_prec.
now destruct (andb_prop _ _ Hx) as (H, _).
Qed.

Definition is_finite_strict f :=
  match f with
  | B754_finite _ _ _ _ => true
  | _ => false
  end.

Theorem binary_unicity :
  forall x y : binary_float,
  is_finite_strict x = true ->
  is_finite_strict y = true ->
  B2R x = B2R y ->
  x = y.
Proof.
intros [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ; try easy.
simpl.
intros _ _ Heq.
assert (Hs: sx = sy).
(* *)
revert Heq. clear.
case sx ; case sy ; try easy ;
  intros Heq ; apply False_ind ; revert Heq.
apply Rlt_not_eq.
apply Rlt_trans with R0.
now apply F2R_lt_0_compat.
now apply F2R_gt_0_compat.
apply Rgt_not_eq.
apply Rgt_trans with R0.
now apply F2R_gt_0_compat.
now apply F2R_lt_0_compat.
assert (mx = my /\ ex = ey).
(* *)
refine (_ (canonic_unicity _ fexp _ _ _ _ Heq)).
rewrite Hs.
now case sy ; intro H ; injection H ; split.
apply canonic_bounded_prec.
exact (proj1 (andb_prop _ _ Hx)).
apply canonic_bounded_prec.
exact (proj1 (andb_prop _ _ Hy)).
(* *)
revert Hx.
rewrite Hs, (proj1 H), (proj2 H).
intros Hx.
apply f_equal.
apply eqbool_irrelevance.
Qed.

Definition is_finite f :=
  match f with
  | B754_finite _ _ _ _ => true
  | B754_zero _ => true
  | _ => false
  end.

Definition Bopp x :=
  match x with
  | B754_nan => x
  | B754_infinity sx => B754_infinity (negb sx)
  | B754_finite sx mx ex Hx => B754_finite (negb sx) mx ex Hx
  | B754_zero sx => B754_zero (negb sx)
  end.

Theorem Bopp_involutive :
  forall x, Bopp (Bopp x) = x.
Proof.
now intros [sx|sx| |sx mx ex Hx] ; simpl ; try rewrite Bool.negb_involutive.
Qed.

Theorem B2R_Bopp :
  forall x,
  B2R (Bopp x) = (- B2R x)%R.
Proof.
intros [sx|sx| |sx mx ex Hx] ; apply sym_eq ; try apply Ropp_0.
simpl.
rewrite opp_F2R.
now case sx.
Qed.

Theorem bounded_lt_emax :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R.
Proof.
intros mx ex Hx.
destruct (andb_prop _ _ Hx) as (H1,H2).
generalize (Zeq_bool_eq _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
generalize (ln_beta_F2R_digits radix2 (Zpos mx) ex).
destruct (ln_beta radix2 (F2R (Float radix2 (Zpos mx) ex))) as (e',Ex).
unfold ln_beta_val.
intros H.
apply Rlt_le_trans with (bpow radix2 e').
change (Zpos mx) with (Zabs (Zpos mx)).
rewrite <- abs_F2R.
apply Ex.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
apply bpow_le.
rewrite H. 2: discriminate.
revert H1. clear -H2.
rewrite Z_of_nat_S_digits2_Pnat.
change Fcalc_digits.radix2 with radix2.
unfold fexp, FLT_exp.
generalize (digits radix2 (Zpos mx)).
intros ; zify ; subst.
clear -H H2. clearbody emin.
omega.
Qed.

Theorem B2R_lt_emax :
  forall x,
  (Rabs (B2R x) < bpow radix2 emax)%R.
Proof.
intros [sx|sx| |sx mx ex Hx] ; simpl ; try ( rewrite Rabs_R0 ; apply bpow_gt_0 ).
rewrite abs_F2R, abs_cond_Zopp.
now apply bounded_lt_emax.
Qed.

Theorem bounded_canonic_lt_emax :
  forall mx ex,
  canonic radix2 fexp (Float radix2 (Zpos mx) ex) ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R ->
  bounded mx ex = true.
Proof.
intros mx ex Cx Bx.
apply andb_true_intro.
split.
unfold bounded_prec.
unfold canonic, Fexp in Cx.
rewrite Cx at 2.
rewrite Z_of_nat_S_digits2_Pnat.
change Fcalc_digits.radix2 with radix2.
unfold canonic_exponent.
rewrite ln_beta_F2R_digits. 2: discriminate.
now apply -> Zeq_is_eq_bool.
apply Zle_bool_true.
unfold canonic, Fexp in Cx.
rewrite Cx.
unfold canonic_exponent, fexp, FLT_exp.
destruct (ln_beta radix2 (F2R (Float radix2 (Zpos mx) ex))) as (e',Ex). simpl.
apply Zmax_lub.
cut (e' - 1 < emax)%Z. clear ; omega.
apply lt_bpow with radix2.
apply Rle_lt_trans with (2 := Bx).
change (Zpos mx) with (Zabs (Zpos mx)).
rewrite <- abs_F2R.
apply Ex.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
unfold emin. clear -Hprec Hmax.
omega.
Qed.

Inductive mode := mode_NE | mode_ZR | mode_DN | mode_UP | mode_NA.

Definition round_mode m :=
  match m with
  | mode_NE => rndNE
  | mode_ZR => rndZR
  | mode_DN => rndDN
  | mode_UP => rndUP
  | mode_NA => rndNA
  end.

Definition choice_mode m sx mx lx :=
  match m with
  | mode_NE => cond_incr (round_N (negb (Zeven mx)) lx) mx
  | mode_ZR => mx
  | mode_DN => cond_incr (round_sign_DN sx lx) mx
  | mode_UP => cond_incr (round_sign_UP sx lx) mx
  | mode_NA => cond_incr (round_N true lx) mx
  end.

Definition binary_round_sign mode sx mx ex lx :=
  let '(m', e', l') := truncate radix2 fexp (Zpos mx, ex, lx) in
  let '(m'', e'', l'') := truncate radix2 fexp (choice_mode mode sx m' l', e', loc_Exact) in
  match m'' with
  | Z0 => B754_zero sx
  | Zpos m =>
    match Sumbool.sumbool_of_bool (bounded m e'') with
    | left H => B754_finite sx m e'' H
    | right _ => B754_infinity sx
    end
  | _ => B754_nan (* dummy *)
  end.

Theorem binary_round_sign_correct :
  forall mode x mx ex lx,
  inbetween_float radix2 (Zpos mx) ex (Rabs x) lx ->
  (ex <= fexp (digits radix2 (Zpos mx) + ex))%Z ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode) x)) (bpow radix2 emax) then
    B2R (binary_round_sign mode (Rlt_bool x 0) mx ex lx) = round radix2 fexp (round_mode mode) x
  else
    binary_round_sign mode (Rlt_bool x 0) mx ex lx = B754_infinity (Rlt_bool x 0).
Proof.
intros m x mx ex lx Bx Ex.
unfold binary_round_sign.
refine (_ (round_trunc_sign_any_correct _ _ fexp_correct (round_mode m) (choice_mode m) _ x (Zpos mx) ex lx Bx (or_introl _ Ex))).
refine (_ (truncate_correct_partial _ _ fexp_correct _ _ _ _ _ Bx Ex)).
destruct (truncate radix2 fexp (Zpos mx, ex, lx)) as ((m1, e1), l1).
set (m1' := choice_mode m (Rlt_bool x 0) m1 l1).
intros (H1a,H1b) H1c.
rewrite H1c.
assert (Hm: (m1 <= m1')%Z).
(* . *)
unfold m1', choice_mode, cond_incr.
case m ;
  try apply Zle_refl ;
  match goal with |- (m1 <= if ?b then _ else _)%Z =>
    case b ; [ apply Zle_succ | apply Zle_refl ] end.
assert (Hr: Rabs (round radix2 fexp (round_mode m) x) = F2R (Float radix2 m1' e1)).
(* . *)
rewrite <- (Zabs_eq m1').
replace (Zabs m1') with (Zabs (cond_Zopp (Rlt_bool x 0) m1')).
rewrite <- abs_F2R.
now apply f_equal.
apply abs_cond_Zopp.
apply Zle_trans with (2 := Hm).
apply Zlt_succ_le.
apply F2R_gt_0_reg with radix2 e1.
apply Rle_lt_trans with (1 := Rabs_pos x).
exact (proj2 (inbetween_float_bounds _ _ _ _ _ H1a)).
(* . *)
assert (Br: inbetween_float radix2 m1' e1 (Rabs (round radix2 fexp (round_mode m) x)) loc_Exact).
now apply inbetween_Exact.
destruct m1' as [|m1'|m1'].
(* . m1' = 0 *)
rewrite Rlt_bool_true.
generalize (truncate_0 radix2 fexp e1 loc_Exact).
destruct (truncate radix2 fexp (Z0, e1, loc_Exact)) as ((m2, e2), l2).
intros Hm2.
rewrite Hm2. simpl.
apply sym_eq.
case Rlt_bool ; apply F2R_0.
rewrite abs_F2R, abs_cond_Zopp, F2R_0.
apply bpow_gt_0.
(* . 0 < m1' *)
assert (He: (e1 <= fexp (digits radix2 (Zpos m1') + e1))%Z).
rewrite <- ln_beta_F2R_digits, <- Hr, ln_beta_abs.
2: discriminate.
rewrite H1b.
rewrite canonic_exponent_abs.
fold (canonic_exponent radix2 fexp (round radix2 fexp (round_mode m) x)).
apply canonic_exponent_round.
apply fexp_correct.
apply FLT_exp_monotone.
rewrite H1c.
case (Rlt_bool x 0).
apply Rlt_not_eq.
now apply F2R_lt_0_compat.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
refine (_ (truncate_correct_partial _ _ fexp_correct _ _ _ _ _ Br He)).
2: now rewrite Hr ; apply F2R_gt_0_compat.
refine (_ (truncate_correct_format radix2 fexp (Zpos m1') e1 _ _ He)).
2: discriminate.
destruct (truncate radix2 fexp (Zpos m1', e1, loc_Exact)) as ((m2, e2), l2).
intros (H3,H4) (H2,_).
destruct m2 as [|m2|m2].
elim Rgt_not_eq with (2 := H3).
rewrite F2R_0.
now apply F2R_gt_0_compat.
rewrite F2R_cond_Zopp, H3, abs_cond_Ropp, abs_F2R.
simpl Zabs.
case (Sumbool.sumbool_of_bool (bounded m2 e2)) ; intros Hb.
rewrite Rlt_bool_true.
simpl.
apply F2R_cond_Zopp.
now apply bounded_lt_emax.
rewrite Rlt_bool_false.
apply refl_equal.
apply Rnot_lt_le.
intros Hx.
revert Hb.
rewrite bounded_canonic_lt_emax with (2 := Hx).
discriminate.
unfold canonic.
now rewrite <- H3.
elim Rgt_not_eq with (2 := H3).
apply Rlt_trans with R0.
now apply F2R_lt_0_compat.
now apply F2R_gt_0_compat.
rewrite <- Hr.
apply generic_format_abs.
apply generic_format_round.
apply fexp_correct.
(* . not m1' < 0 *)
elim Rgt_not_eq with (2 := Hr).
apply Rlt_le_trans with R0.
now apply F2R_lt_0_compat.
apply Rabs_pos.
(* *)
apply Rlt_le_trans with (2 := proj1 (inbetween_float_bounds _ _ _ _ _ Bx)).
now apply F2R_gt_0_compat.
(* all the modes are valid *)
clear. case m.
exact inbetween_int_NE_sign.
exact inbetween_int_ZR_sign.
exact inbetween_int_DN_sign.
exact inbetween_int_UP_sign.
exact inbetween_int_NA_sign.
Qed.

Definition Bsign x :=
  match x with
  | B754_nan => false
  | B754_zero s => s
  | B754_infinity s => s
  | B754_finite s _ _ _ => s
  end.

Definition Bmult m x y :=
  match x, y with
  | B754_nan, _ => x
  | _, B754_nan => y
  | B754_infinity sx, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity _, B754_zero _ => B754_nan
  | B754_zero _, B754_infinity _ => B754_nan
  | B754_finite sx _ _ _, B754_zero sy => B754_zero (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => B754_zero (xorb sx sy)
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    binary_round_sign m (xorb sx sy) (Pmult mx my) (ex + ey) loc_Exact
  end.

Theorem Bmult_correct :
  forall m x y,
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x * B2R y))) (bpow radix2 emax) then
    B2R (Bmult m x y) = round radix2 fexp (round_mode m) (B2R x * B2R y)
  else
    Bmult m x y = B754_infinity (xorb (Bsign x) (Bsign y)).
Proof.
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ;
  try ( rewrite ?Rmult_0_r, ?Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ apply refl_equal | apply bpow_gt_0 ] ).
simpl.
rewrite <- mult_F2R.
simpl Fmult.
replace (xorb sx sy) with (Rlt_bool (F2R (Float radix2 (cond_Zopp sx (Zpos mx) * cond_Zopp sy (Zpos my)) (ex + ey))) 0).
apply binary_round_sign_correct.
constructor.
rewrite abs_F2R.
apply F2R_eq_compat.
rewrite Zabs_Zmult.
now rewrite 2!abs_cond_Zopp.
(* *)
change (Zpos (mx * my)) with (Zpos mx * Zpos my)%Z.
assert (forall m e, bounded m e = true -> fexp (digits radix2 (Zpos m) + e) = e)%Z.
clear. intros m e Hb.
destruct (andb_prop _ _ Hb) as (H,_).
apply Zeq_bool_eq.
now rewrite <- Z_of_nat_S_digits2_Pnat.
generalize (H _ _ Hx) (H _ _ Hy).
clear sx sy Hx Hy H.
unfold fexp, FLT_exp.
refine (_ (digits_mult_ge radix2 (Zpos mx) (Zpos my) _ _)) ; try discriminate.
refine (_ (digits_gt_0 radix2 (Zpos mx) _) (digits_gt_0 radix2 (Zpos my) _)) ; try discriminate.
generalize (digits radix2 (Zpos mx)) (digits radix2 (Zpos my)) (digits radix2 (Zpos mx * Zpos my)).
clear -Hprec Hmax.
unfold emin.
intros dx dy dxy Hx Hy Hxy.
zify ; intros ; subst.
omega.
(* *)
case sx ; case sy.
apply Rlt_bool_false.
now apply F2R_ge_0_compat.
apply Rlt_bool_true.
now apply F2R_lt_0_compat.
apply Rlt_bool_true.
now apply F2R_lt_0_compat.
apply Rlt_bool_false.
now apply F2R_ge_0_compat.
Qed.

Theorem Bmult_correct_finite :
  forall m x y,
  is_finite (Bmult m x y) = true ->
  B2R (Bmult m x y) = round radix2 fexp (round_mode m) (B2R x * B2R y)%R.
Proof.
intros m x y.
generalize (Bmult_correct m x y).
destruct (Bmult m x y) as [sz|sz| |sz mz ez Hz] ; try easy.
now case Rlt_bool.
now case Rlt_bool.
Qed.

Definition fexp_scale mx ex :=
  let ex' := fexp (Z_of_nat (S (digits2_Pnat mx)) + ex) in
  match (ex' - ex)%Z with
  | Zneg d => (shift_pos d mx, ex')
  | _ => (mx, ex)
  end.

Theorem fexp_scale_correct :
  forall mx ex,
  let (mx', ex') := fexp_scale mx ex in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex') /\
  (ex' <= fexp (digits radix2 (Zpos mx') + ex'))%Z.
Proof.
intros mx ex.
unfold fexp_scale.
rewrite Z_of_nat_S_digits2_Pnat.
change (Fcalc_digits.radix2) with radix2.
set (e' := fexp (digits radix2 (Zpos mx) + ex)).
pattern e' at 2 ; replace e' with (e' - ex + ex)%Z by ring.
case_eq (e' - ex)%Z ; fold e'.
(* d = 0 *)
intros H.
repeat split.
rewrite Zminus_eq with (1 := H).
apply Zle_refl.
(* d > 0 *)
intros d Hd.
repeat split.
replace e' with (e' - ex + ex)%Z by ring.
rewrite Hd.
pattern ex at 1 ; rewrite <- Zplus_0_l.
now apply Zplus_le_compat_r.
(* d < 0 *)
intros d Hd.
rewrite shift_pos_correct, Zmult_comm.
change (Zpower_pos 2 d) with (Zpower radix2 (Zpos d)).
rewrite digits_shift ; try easy.
change (Zpos d) with (Zopp (Zneg d)).
rewrite <- Hd.
split.
replace (- (e' - ex))%Z with (ex - e')%Z by ring.
replace (e' - ex + ex)%Z with e' by ring.
apply F2R_change_exp.
apply Zle_0_minus_le.
replace (ex - e')%Z with (-(e' - ex))%Z by ring.
now rewrite Hd.
ring_simplify (digits radix2 (Zpos mx) + - (e' - ex) + (e' - ex + ex))%Z.
fold e'.
ring_simplify.
apply Zle_refl.
Qed.

Definition Bplus m x y :=
  match x, y with
  | B754_nan, _ => x
  | _, B754_nan => y
  | B754_infinity sx, B754_infinity sy =>
    if Bool.eqb sx sy then x else B754_nan
  | B754_infinity _, _ => x
  | _, B754_infinity _ => y
  | B754_zero sx, B754_zero sy =>
    if Bool.eqb sx sy then x else
    match m with mode_DN => B754_zero true | _ => B754_zero false end
  | B754_zero _, _ => y
  | _, B754_zero _ => x
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    let fx := Float radix2 (cond_Zopp sx (Zpos mx)) ex in
    let fy := Float radix2 (cond_Zopp sy (Zpos my)) ey in
    match Fplus radix2 fx fy with
    | Float Z0 _ =>
      match m with mode_DN => B754_zero true | _ => B754_zero false end
    | Float (Zpos mz) ez => let '(m', e') := fexp_scale mz ez in binary_round_sign m false m' e' loc_Exact
    | Float (Zneg mz) ez => let '(m', e') := fexp_scale mz ez in binary_round_sign m true m' e' loc_Exact
    end
  end.

Theorem Bplus_correct :
  forall m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x + B2R y))) (bpow radix2 emax) then
    B2R (Bplus m x y) = round radix2 fexp (round_mode m) (B2R x + B2R y)
  else
    (Bplus m x y = B754_infinity (Bsign x) /\ Bsign x = Bsign y).
Proof.
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] Fx Fy ; try easy.
(* *)
rewrite Rplus_0_r, round_0, Rabs_R0, Rlt_bool_true.
simpl.
case (Bool.eqb sx sy) ; try easy.
now case m.
apply bpow_gt_0.
(* *)
rewrite Rplus_0_l, round_generic, Rlt_bool_true.
apply refl_equal.
apply B2R_lt_emax.
apply generic_format_B2R.
(* *)
rewrite Rplus_0_r, round_generic, Rlt_bool_true.
apply refl_equal.
apply B2R_lt_emax.
apply generic_format_B2R.
(* *)
clear Fx Fy.
simpl.
rewrite <- plus_F2R.
case_eq (Fplus radix2 (Float radix2 (cond_Zopp sx (Zpos mx)) ex)
  (Float radix2 (cond_Zopp sy (Zpos my)) ey)).
intros mz ez Hz.
assert (Sz: (bpow radix2 emax <= Rabs (round radix2 fexp (round_mode m) (F2R (Float radix2 mz ez))))%R -> sx = Rlt_bool (F2R (Float radix2 mz ez)) 0 /\ sx = sy).
(* . *)
rewrite <- Hz.
rewrite plus_F2R.
intros Bz.
destruct (Bool.bool_dec sx sy) as [Hs|Hs].
(* .. *)
refine (conj _ Hs).
rewrite Hs.
apply sym_eq.
case sy.
apply Rlt_bool_true.
rewrite <- (Rplus_0_r 0).
apply Rplus_lt_compat.
now apply F2R_lt_0_compat.
now apply F2R_lt_0_compat.
apply Rlt_bool_false.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
now apply F2R_ge_0_compat.
now apply F2R_ge_0_compat.
(* .. *)
elim Rle_not_lt with (1 := Bz).
generalize (bounded_lt_emax _ _ Hx) (bounded_lt_emax _ _ Hy) (andb_prop _ _ Hx) (andb_prop _ _ Hy).
intros Bx By (Hx',_) (Hy',_).
generalize (canonic_bounded_prec sx _ _ Hx') (canonic_bounded_prec sy _ _ Hy').
clear -Bx By Hs fexp_correct.
intros Cx Cy.
destruct sx.
(* ... *)
destruct sy.
now elim Hs.
clear Hs.
apply Rabs_lt.
split.
apply Rlt_le_trans with (F2R (Float radix2 (cond_Zopp true (Zpos mx)) ex)).
rewrite <- opp_F2R.
now apply Ropp_lt_contravar.
apply round_monotone_l.
apply fexp_correct.
now apply generic_format_canonic.
pattern (F2R (Float radix2 (cond_Zopp true (Zpos mx)) ex)) at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
now apply F2R_ge_0_compat.
apply Rle_lt_trans with (2 := By).
apply round_monotone_r.
apply fexp_correct.
now apply generic_format_canonic.
rewrite <- (Rplus_0_l (F2R (Float radix2 (Zpos my) ey))).
apply Rplus_le_compat_r.
now apply F2R_le_0_compat.
(* ... *)
destruct sy.
2: now elim Hs.
clear Hs.
apply Rabs_lt.
split.
apply Rlt_le_trans with (F2R (Float radix2 (cond_Zopp true (Zpos my)) ey)).
rewrite <- opp_F2R.
now apply Ropp_lt_contravar.
apply round_monotone_l.
apply fexp_correct.
now apply generic_format_canonic.
pattern (F2R (Float radix2 (cond_Zopp true (Zpos my)) ey)) at 1 ; rewrite <- Rplus_0_l.
apply Rplus_le_compat_r.
now apply F2R_ge_0_compat.
apply Rle_lt_trans with (2 := Bx).
apply round_monotone_r.
apply fexp_correct.
now apply generic_format_canonic.
rewrite <- (Rplus_0_r (F2R (Float radix2 (Zpos mx) ex))).
apply Rplus_le_compat_l.
now apply F2R_le_0_compat.
destruct mz as [|mz|mz].
(* . mz = 0 *)
rewrite F2R_0, round_0, Rabs_R0, Rlt_bool_true.
now case m.
apply bpow_gt_0.
(* . mz > 0 *)
generalize (fexp_scale_correct mz ez).
destruct (fexp_scale mz ez) as (m', e').
intros (Hz', Ez).
refine (_ (binary_round_sign_correct m (F2R (Float radix2 (Zpos mz) ez)) m' e' loc_Exact _ Ez)).
2: constructor ; now rewrite abs_F2R.
revert Sz.
rewrite (Rlt_bool_false _ 0).
2: now apply F2R_ge_0_compat.
intros Sz.
case Rlt_bool_spec ; intros Bz.
easy.
specialize (Sz Bz).
intros H.
split.
rewrite H.
now apply f_equal.
apply Sz.
(* . mz < 0 *)
generalize (fexp_scale_correct mz ez).
destruct (fexp_scale mz ez) as (m', e').
intros (Hz', Ez).
refine (_ (binary_round_sign_correct m (F2R (Float radix2 (Zneg mz) ez)) m' e' loc_Exact _ Ez)).
2: constructor ; now rewrite abs_F2R.
revert Sz.
rewrite (Rlt_bool_true _ 0).
intros Sz.
2: now apply F2R_lt_0_compat.
case Rlt_bool_spec ; intros Bz.
easy.
specialize (Sz Bz).
intros H.
split.
rewrite H.
now apply f_equal.
apply Sz.
Qed.

Definition Bminus m x y := Bplus m x (Bopp y).

Definition Bdiv m x y :=
  match x, y with
  | B754_nan, _ => x
  | _, B754_nan => y
  | B754_infinity sx, B754_infinity sy => B754_nan
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity sx, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_infinity sy => B754_zero (xorb sx sy)
  | B754_finite sx _ _ _, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => B754_nan
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    let '(mz, ez, lz) := Fdiv_core radix2 prec (Zpos mx) ex (Zpos my) ey in
    match mz with
    | Zpos mz => binary_round_sign m (xorb sx sy) mz ez lz
    | _ => B754_nan (* dummy *)
    end
  end.

Theorem Bdiv_correct :
  forall m x y,
  B2R y <> R0 ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x / B2R y))) (bpow radix2 emax) then
    B2R (Bdiv m x y) = round radix2 fexp (round_mode m) (B2R x / B2R y)
  else
    Bdiv m x y = B754_infinity (xorb (Bsign x) (Bsign y)).
Proof.
intros m x [sy|sy| |sy my ey Hy] Zy ; try now elim Zy.
revert x.
unfold Rdiv.
intros [sx|sx| |sx mx ex Hx] ;
  try ( rewrite Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ apply refl_equal | apply bpow_gt_0 ] ).
simpl.
refine (_ (Fdiv_core_correct radix2 prec (Zpos mx) ex (Zpos my) ey _ _ _)) ; try easy.
destruct (Fdiv_core radix2 prec (Zpos mx) ex (Zpos my) ey) as ((mz, ez), lz).
intros (Pz, Bz).
replace (xorb sx sy) with (Rlt_bool (F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) *
   / F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey)) 0).
destruct mz as [|mz|mz].
(* . mz = 0 *)
elim (Zlt_irrefl prec).
now apply Zle_lt_trans with Z0.
(* . mz > 0 *)
apply binary_round_sign_correct.
rewrite Rabs_mult, Rabs_Rinv.
now rewrite 2!abs_F2R, 2!abs_cond_Zopp.
exact Zy.
revert Pz.
generalize (digits radix2 (Zpos mz)).
unfold fexp, FLT_exp.
clear.
intros ; zify ; subst.
omega.
(* . mz < 0 *)
elim Rlt_not_le  with (1 := proj2 (inbetween_float_bounds _ _ _ _ _ Bz)).
apply Rle_trans with R0.
apply F2R_le_0_compat.
now case mz.
apply Rmult_le_pos.
now apply F2R_ge_0_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply F2R_gt_0_compat.
(* *)
revert Zy. clear.
case sy ; simpl.
change (Zneg my) with (Zopp (Zpos my)).
rewrite <- opp_F2R.
intros Zy.
rewrite <- Ropp_inv_permute.
rewrite Ropp_mult_distr_r_reverse.
case sx ; simpl.
apply Rlt_bool_false.
rewrite <- Ropp_mult_distr_l_reverse.
apply Rmult_le_pos.
rewrite opp_F2R.
now apply F2R_ge_0_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply F2R_gt_0_compat.
apply Rlt_bool_true.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply Rmult_lt_0_compat.
now apply F2R_gt_0_compat.
apply Rinv_0_lt_compat.
now apply F2R_gt_0_compat.
contradict Zy.
rewrite Zy.
apply Ropp_0.
intros Zy.
case sx.
apply Rlt_bool_true.
rewrite <- opp_F2R.
rewrite Ropp_mult_distr_l_reverse.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply Rmult_lt_0_compat.
now apply F2R_gt_0_compat.
apply Rinv_0_lt_compat.
now apply F2R_gt_0_compat.
apply Rlt_bool_false.
apply Rmult_le_pos.
now apply F2R_ge_0_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply F2R_gt_0_compat.
Qed.

Definition Bsqrt m x :=
  match x with
  | B754_nan => x
  | B754_infinity false => x
  | B754_infinity true => B754_nan
  | B754_finite true _ _ _ => B754_nan
  | B754_zero _ => x
  | B754_finite sx mx ex Hx =>
    let '(mz, ez, lz) := Fsqrt_core radix2 prec (Zpos mx) ex in
    match mz with
    | Zpos mz => binary_round_sign m false mz ez lz
    | _ => B754_nan (* dummy *)
    end
  end.

Theorem Bsqrt_correct :
  forall m x,
  B2R (Bsqrt m x) = round radix2 fexp (round_mode m) (sqrt (B2R x)).
Proof.
intros m [sx|[|]| |sx mx ex Hx] ; try ( now simpl ; rewrite sqrt_0, round_0 ).
simpl.
refine (_ (Fsqrt_core_correct radix2 prec (Zpos mx) ex _)) ; try easy.
destruct (Fsqrt_core radix2 prec (Zpos mx) ex) as ((mz, ez), lz).
intros (Pz, Bz).
case sx.
apply sym_eq.
unfold sqrt.
case Rcase_abs.
intros _.
apply round_0.
intros H.
elim Rge_not_lt with (1 := H).
now apply F2R_lt_0_compat.
destruct mz as [|mz|mz].
(* . mz = 0 *)
elim (Zlt_irrefl prec).
now apply Zle_lt_trans with Z0.
(* . mz > 0 *)
simpl.
refine (_ (binary_round_sign_correct m (sqrt (F2R (Float radix2 (Zpos mx) ex))) mz ez lz _ _)).
rewrite Rlt_bool_true.
rewrite Rlt_bool_false.
easy.
apply sqrt_ge_0.
(* .. *)
rewrite Rabs_pos_eq.
refine (_ (relative_error_FLT_ex radix2 emin prec Hprec (round_mode m) (sqrt (F2R (Float radix2 (Zpos mx) ex))) _)).
fold fexp.
intros (eps, (Heps, Hr)).
rewrite Hr.
assert (Heps': (Rabs eps < 1)%R).
apply Rlt_le_trans with (1 := Heps).
fold (bpow radix2 0).
apply bpow_le.
clear -Hprec. omega.
apply Rsqr_incrst_0.
3: apply bpow_ge_0.
rewrite Rsqr_mult.
rewrite Rsqr_sqrt.
2: now apply F2R_ge_0_compat.
unfold Rsqr.
apply Rmult_ge_0_gt_0_lt_compat.
apply Rle_ge.
apply Rle_0_sqr.
apply bpow_gt_0.
now apply bounded_lt_emax.
apply Rlt_le_trans with 4%R.
apply Rsqr_incrst_1.
apply Rplus_lt_compat_l.
apply (Rabs_lt_inv _ _ Heps').
rewrite <- (Rplus_opp_r 1).
apply Rplus_le_compat_l.
apply Rlt_le.
apply (Rabs_lt_inv _ _ Heps').
now apply (Z2R_le 0 2).
change 4%R with (bpow radix2 2).
apply bpow_le.
clear -Hprec Hmax.
omega.
apply Rmult_le_pos.
apply sqrt_ge_0.
rewrite <- (Rplus_opp_r 1).
apply Rplus_le_compat_l.
apply Rlt_le.
apply (Rabs_lt_inv _ _ Heps').
rewrite Rabs_pos_eq.
2: apply sqrt_ge_0.
apply Rsqr_incr_0.
2: apply bpow_ge_0.
2: apply sqrt_ge_0.
rewrite Rsqr_sqrt.
2: now apply F2R_ge_0_compat.
apply Rle_trans with (bpow radix2 emin).
unfold Rsqr.
rewrite <- bpow_plus.
apply bpow_le.
unfold emin.
clear -Hprec Hmax.
omega.
apply generic_format_ge_bpow with fexp.
intros.
apply Zle_max_r.
now apply F2R_gt_0_compat.
apply generic_format_canonic.
apply (canonic_bounded_prec false).
apply (andb_prop _ _ Hx).
(* .. *)
apply round_monotone_l.
apply fexp_correct.
apply generic_format_0.
apply sqrt_ge_0.
rewrite Rabs_pos_eq.
exact Bz.
apply sqrt_ge_0.
revert Pz.
generalize (digits radix2 (Zpos mz)).
unfold fexp, FLT_exp.
clear.
intros ; zify ; subst.
omega.
(* . mz < 0 *)
elim Rlt_not_le  with (1 := proj2 (inbetween_float_bounds _ _ _ _ _ Bz)).
apply Rle_trans with R0.
apply F2R_le_0_compat.
now case mz.
apply sqrt_ge_0.
Qed.

End Binary.

Section Binary_Bits.

Variable mw ew : Z.
Hypothesis Hmw : (0 <= mw)%Z.
Hypothesis Hew : (0 < ew)%Z.

Let emax := Zpower 2 (ew - 1).
Let prec := (mw + 1)%Z.
Let emin := (3 - emax - prec)%Z.
Let binary_float := binary_float prec emax.

Let Hprec : (0 < prec)%Z.
unfold prec.
now apply Zle_lt_succ.
Qed.

Let Hm_gt_0 : (0 < 2^mw)%Z.
now apply (Zpower_gt_0 radix2).
Qed.

Let He_gt_0 : (0 < 2^ew)%Z.
apply (Zpower_gt_0 radix2).
now apply Zlt_le_weak.
Qed.

Hypothesis Hmax : (prec < emax)%Z.

Definition join_bits (s : bool) m e :=
  (((if s then Zpower 2 ew else 0) + e) * Zpower 2 mw + m)%Z.

Definition split_bits x :=
  let mm := Zpower 2 mw in
  let em := Zpower 2 ew in
  (Zle_bool (mm * em) x, Zmod x mm, Zmod (Zdiv x mm) em)%Z.

Theorem split_join_bits :
  forall s m e,
  (0 <= m < Zpower 2 mw)%Z ->
  (0 <= e < Zpower 2 ew)%Z ->
  split_bits (join_bits s m e) = (s, m, e).
Proof.
intros s m e Hm He.
unfold split_bits, join_bits.
apply f_equal2.
apply f_equal2.
(* *)
case s.
apply Zle_bool_true.
apply Zle_0_minus_le.
ring_simplify.
apply Zplus_le_0_compat.
apply Zmult_le_0_compat.
apply He.
now apply Zlt_le_weak.
apply Hm.
apply Zle_bool_false.
apply Zplus_lt_reg_l with (2^mw * (-e))%Z.
replace (2 ^ mw * - e + ((0 + e) * 2 ^ mw + m))%Z with (m * 1)%Z by ring.
rewrite <- Zmult_plus_distr_r.
apply Zlt_le_trans with (2^mw * 1)%Z.
now apply Zmult_lt_compat_r.
apply Zmult_le_compat_l.
clear -He. omega.
now apply Zlt_le_weak.
(* *)
rewrite Zplus_comm.
rewrite Z_mod_plus_full.
now apply Zmod_small.
(* *)
rewrite Z_div_plus_full_l.
rewrite Zdiv_small with (1 := Hm).
rewrite Zplus_0_r.
case s.
replace (2^ew + e)%Z with (e + 1 * 2^ew)%Z by ring.
rewrite Z_mod_plus_full.
now apply Zmod_small.
now apply Zmod_small.
now apply Zgt_not_eq.
Qed.

Theorem join_split_bits :
  forall x,
  (0 <= x < Zpower 2 (mw + ew + 1))%Z ->
  let '(s, m, e) := split_bits x in
  join_bits s m e = x.
Proof.
intros x Hx.
unfold split_bits, join_bits.
pattern x at 4 ; rewrite Z_div_mod_eq_full with x (2^mw)%Z.
apply (f_equal (fun v => (v + _)%Z)).
rewrite Zmult_comm.
apply f_equal.
pattern (x / (2^mw))%Z at 2 ; rewrite Z_div_mod_eq_full with (x / (2^mw))%Z (2^ew)%Z.
apply (f_equal (fun v => (v + _)%Z)).
replace (x / 2 ^ mw / 2 ^ ew)%Z with (if Zle_bool (2 ^ mw * 2 ^ ew) x then 1 else 0)%Z.
case Zle_bool.
now rewrite Zmult_1_r.
now rewrite Zmult_0_r.
rewrite Zdiv_Zdiv.
apply sym_eq.
case Zle_bool_spec ; intros Hs.
apply Zle_antisym.
cut (x / (2^mw * 2^ew) < 2)%Z. clear ; omega.
apply Zdiv_lt_upper_bound.
apply Hx.
now apply Zmult_lt_0_compat.
rewrite <- Zpower_exp.
change 2%Z at 1 with (Zpower 2 1).
rewrite <- Zpower_exp.
now rewrite Zplus_comm.
discriminate.
apply Zle_ge.
apply Zplus_le_0_compat with (1 := Hmw).
now apply Zlt_le_weak.
now apply Zle_ge.
apply Zle_ge.
now apply Zlt_le_weak.
apply Zdiv_le_lower_bound.
apply Hx.
now apply Zmult_lt_0_compat.
now rewrite Zmult_1_l.
apply Zdiv_small.
now split.
now apply Zlt_le_weak.
now apply Zlt_le_weak.
now apply Zgt_not_eq.
now apply Zgt_not_eq.
Qed.

Definition bits_of_binary_float (x : binary_float) :=
  match x with
  | B754_zero sx => join_bits sx 0 0
  | B754_infinity sx => join_bits sx 0 (Zpower 2 ew - 1)
  | B754_nan => join_bits false (Zpower 2 mw - 1) (Zpower 2 ew - 1)
  | B754_finite sx mx ex _ =>
    if Zle_bool (Zpower 2 mw) (Zpos mx) then
      join_bits sx (Zpos mx - Zpower 2 mw) (ex - emin + 1)
    else
      join_bits sx (Zpos mx) 0
  end.

Definition split_bits_of_binary_float (x : binary_float) :=
  match x with
  | B754_zero sx => (sx, 0, 0)%Z
  | B754_infinity sx => (sx, 0, Zpower 2 ew - 1)%Z
  | B754_nan => (false, Zpower 2 mw - 1, Zpower 2 ew - 1)%Z
  | B754_finite sx mx ex _ =>
    if Zle_bool (Zpower 2 mw) (Zpos mx) then
      (sx, Zpos mx - Zpower 2 mw, ex - emin + 1)%Z
    else
      (sx, Zpos mx, 0)%Z
  end.

Theorem split_bits_of_binary_float_correct :
  forall x,
  split_bits (bits_of_binary_float x) = split_bits_of_binary_float x.
Proof.
intros [sx|sx| |sx mx ex Hx] ;
  try ( simpl ; apply split_join_bits ; split ; try apply Zle_refl ; try apply Zlt_pred ; trivial ; omega ).
unfold bits_of_binary_float, split_bits_of_binary_float.
assert (Hf: (emin <= ex /\ digits radix2 (Zpos mx) <= prec)%Z).
destruct (andb_prop _ _ Hx) as (Hx', _).
unfold bounded_prec in Hx'.
rewrite Z_of_nat_S_digits2_Pnat in Hx'.
generalize (Zeq_bool_eq _ _ Hx').
unfold FLT_exp.
change (Fcalc_digits.radix2) with radix2.
unfold emin.
clear ; zify ; omega.
destruct (Zle_bool_spec (2^mw) (Zpos mx)) as [H|H] ;
  apply split_join_bits ; try now split.
(* *)
split.
clear -He_gt_0 H ; omega.
cut (Zpos mx < 2 * 2^mw)%Z. clear ; omega.
replace (2 * 2^mw)%Z with (2^prec)%Z.
apply (Zpower_gt_digits radix2 _ (Zpos mx)).
apply Hf.
unfold prec.
rewrite Zplus_comm.
now apply Zpower_exp ; apply Zle_ge.
(* *)
split.
generalize (proj1 Hf).
clear ; omega.
destruct (andb_prop _ _ Hx) as (_, Hx').
unfold emin.
replace (2^ew)%Z with (2 * emax)%Z.
generalize (Zle_bool_imp_le _ _ Hx').
clear ; omega.
apply sym_eq.
rewrite (Zsucc_pred ew).
unfold Zsucc.
rewrite Zplus_comm.
apply Zpower_exp ; apply Zle_ge.
discriminate.
now apply Zlt_0_le_0_pred.
Qed.

Lemma binary_float_of_bits_aux1 :
  forall x sx mx ex,
  split_bits x = (sx, Zpos mx, ex) ->
  bounded prec emax mx emin = true.
Proof.
intros x sx mx ex Hx.
injection Hx.
intros Hex Hmx _.
assert (digits radix2 (Zpos mx) <= mw)%Z.
apply digits_le_Zpower.
simpl.
rewrite <- Hmx.
eapply Z_mod_lt.
apply Zlt_gt.
now apply (Zpower_gt_0 radix2).
apply bounded_canonic_lt_emax ; try assumption.
unfold canonic, canonic_exponent.
fold emin.
rewrite ln_beta_F2R_digits. 2: discriminate.
unfold Fexp, FLT_exp.
apply sym_eq.
apply Zmax_right.
clear -H Hprec.
unfold prec ; omega.
apply Rnot_le_lt.
intros H0.
refine (_ (ln_beta_monotone radix2 _ _ _ H0)).
rewrite ln_beta_bpow.
rewrite ln_beta_F2R_digits. 2: discriminate.
unfold emin, prec.
apply Zlt_not_le.
cut (0 < emax)%Z. clear -H Hew ; omega.
apply (Zpower_gt_0 radix2).
clear -Hew ; omega.
apply bpow_gt_0.
Qed.

Lemma binary_float_of_bits_aux2 :
  forall x sx mx ex px,
  split_bits x = (sx, mx, ex) ->
  Zeq_bool ex 0 = false ->
  Zeq_bool ex (Zpower 2 ew - 1) = false ->
  (mx + Zpower 2 mw)%Z = Zpos px ->
  bounded prec emax px (ex + emin - 1) = true.
Proof.
intros x sx mx ex px Hx Hex Hex' Hmx.
injection Hx.
intros Hex'' Hmx' _.
assert (prec = digits radix2 (Zpos px)).
rewrite digits_ln_beta. 2: discriminate.
apply sym_eq.
apply ln_beta_unique.
rewrite <- Z2R_abs.
unfold Zabs.
replace (prec - 1)%Z with mw by ( unfold prec ; ring ).
rewrite <- Z2R_Zpower with (1 := Hmw).
rewrite <- Z2R_Zpower. 2: now apply Zlt_le_weak.
rewrite <- Hmx.
rewrite <- Hmx'.
split.
apply Z2R_le.
change (radix2^mw)%Z with (0 + 2^mw)%Z.
apply Zplus_le_compat_r.
eapply Z_mod_lt.
apply Zlt_gt.
now apply (Zpower_gt_0 radix2).
apply Z2R_lt.
unfold prec.
rewrite Zpower_exp. 2: now apply Zle_ge. 2: discriminate.
rewrite <- Zplus_diag_eq_mult_2.
apply Zplus_lt_compat_r.
eapply Z_mod_lt.
apply Zlt_gt.
now apply (Zpower_gt_0 radix2).
(* *)
apply bounded_canonic_lt_emax ; try assumption.
unfold canonic, canonic_exponent.
rewrite ln_beta_F2R_digits. 2: discriminate.
unfold Fexp, FLT_exp.
rewrite <- H.
replace (prec + (ex + emin - 1) - prec)%Z with (ex + emin - 1)%Z by ring.
apply sym_eq.
apply Zmax_left.
generalize (Zeq_bool_neq _ _ Hex).
cut (0 <= ex)%Z.
unfold emin.
clear ; intros H1 H2 ; omega.
rewrite <- Hex''.
eapply Z_mod_lt.
apply Zlt_gt.
apply (Zpower_gt_0 radix2).
now apply Zlt_le_weak.
apply Rnot_le_lt.
intros H0.
refine (_ (ln_beta_monotone radix2 _ _ _ H0)).
rewrite ln_beta_bpow.
rewrite ln_beta_F2R_digits. 2: discriminate.
rewrite <- H.
apply Zlt_not_le.
unfold emin.
apply Zplus_lt_reg_r with (emax - 1)%Z.
ring_simplify.
generalize (Zeq_bool_neq _ _ Hex').
cut (ex < 2^ew)%Z.
replace (2^ew)%Z with (2 * emax)%Z.
clear ; intros H1 H2 ; omega.
replace ew with (1 + (ew - 1))%Z by ring.
rewrite Zpower_exp.
apply refl_equal.
discriminate.
clear -Hew ; omega.
rewrite <- Hex''.
eapply Z_mod_lt.
apply Zlt_gt.
apply (Zpower_gt_0 radix2).
now apply Zlt_le_weak.
apply bpow_gt_0.
Qed.

Definition binary_float_of_bits (x : Z) :=
  match split_bits x as v1 return split_bits x = v1 -> binary_float with
  | (sx, mx, ex) =>
    match Zeq_bool ex 0 as v2 return _ = v2 -> _ -> binary_float with
    | true => fun _ =>
      match mx as v3 return split_bits x = (sx, v3, ex) -> binary_float with
      | Zpos px => fun H1 => B754_finite prec emax sx px emin (binary_float_of_bits_aux1 x sx px ex H1)
      | Z0 => fun _ => B754_zero prec emax sx
      | _ => fun _ => B754_nan prec emax (* dummy *)
      end
    | false => fun H2 =>
      match Zeq_bool ex (Zpower 2 ew - 1) as v3 return _ = v3 -> _ -> binary_float with
      | true => fun _ _ =>
        if Zeq_bool mx 0 then B754_infinity prec emax sx else B754_nan prec emax
      | false => fun H3 H1 =>
        match (mx + Zpower 2 mw)%Z as v4 return _ = v4 -> binary_float with
        | Zpos px => fun H4 => B754_finite prec emax sx px _ (binary_float_of_bits_aux2 x sx mx ex px H1 H2 H3 H4)
        | _ => fun _ => B754_nan prec emax (* dummy *)
        end (refl_equal _)
      end (refl_equal _)
    end (refl_equal _)
  end (refl_equal _).

End Binary_Bits.

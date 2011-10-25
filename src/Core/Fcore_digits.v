(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2011 Sylvie Boldo
#<br />#
Copyright (C) 2011 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Fcore_Raux.
Require Import ZOdiv.

Theorem Zmod_mod_mult :
  forall n a b, (0 < a)%Z -> (0 <= b)%Z ->
  Zmod (Zmod n (a * b)) b = Zmod n b.
Proof.
intros n a [|b|b] Ha Hb.
now rewrite 2!Zmod_0_r.
rewrite (Zmod_eq n (a * Zpos b)).
rewrite Zmult_assoc.
unfold Zminus.
rewrite Zopp_mult_distr_l.
apply Z_mod_plus.
easy.
apply Zmult_gt_0_compat.
now apply Zlt_gt.
easy.
now elim Hb.
Qed.

Theorem ZOmod_eq :
  forall a b,
  ZOmod a b = (a - ZOdiv a b * b)%Z.
Proof.
intros a b.
rewrite (ZO_div_mod_eq a b) at 2.
ring.
Qed.

Theorem ZOmod_mod_mult :
  forall n a b,
  ZOmod (ZOmod n (a * b)) b = ZOmod n b.
Proof.
intros n a b.
assert (ZOmod n (a * b) = n + - (n / (a * b) * a) * b)%Z.
rewrite <- Zopp_mult_distr_l.
rewrite <- Zmult_assoc.
apply ZOmod_eq.
rewrite H.
apply ZO_mod_plus.
rewrite <- H.
apply ZOmod_sgn2.
Qed.

Theorem Zdiv_mod_mult :
  forall n a b, (0 <= a)%Z -> (0 <= b)%Z ->
  (Zdiv (Zmod n (a * b)) a) = Zmod (Zdiv n a) b.
Proof.
intros n a b Ha Hb.
destruct (Zle_lt_or_eq _ _ Ha) as [Ha'|Ha'].
destruct (Zle_lt_or_eq _ _ Hb) as [Hb'|Hb'].
rewrite (Zmod_eq n (a * b)).
rewrite (Zmult_comm a b) at 2.
rewrite Zmult_assoc.
unfold Zminus.
rewrite Zopp_mult_distr_l.
rewrite Z_div_plus by now apply Zlt_gt.
rewrite <- Zdiv_Zdiv by easy.
apply sym_eq.
apply Zmod_eq.
now apply Zlt_gt.
now apply Zmult_gt_0_compat ; apply Zlt_gt.
rewrite <- Hb'.
rewrite Zmult_0_r, 2!Zmod_0_r.
apply Zdiv_0_l.
rewrite <- Ha'.
now rewrite 2!Zdiv_0_r, Zmod_0_l.
Qed.

Theorem ZOdiv_mod_mult :
  forall n a b,
  (ZOdiv (ZOmod n (a * b)) a) = ZOmod (ZOdiv n a) b.
Proof.
intros n a b.
destruct (Z_eq_dec a 0) as [Za|Za].
rewrite Za.
now rewrite 2!ZOdiv_0_r, ZOmod_0_l.
assert (ZOmod n (a * b) = n + - (n / a / b * b) * a)%Z.
rewrite (ZOmod_eq n (a * b)) at 1.
rewrite ZOdiv_ZOdiv.
ring.
rewrite H.
rewrite ZO_div_plus with (2 := Za).
apply sym_eq.
apply ZOmod_eq.
rewrite <- H.
apply ZOmod_sgn2.
Qed.

Theorem ZOdiv_small_abs :
  forall a b,
  (Zabs a < b)%Z -> ZOdiv a b = Z0.
Proof.
intros a b Ha.
destruct (Zle_or_lt 0 a) as [H|H].
apply ZOdiv_small.
split.
exact H.
now rewrite Zabs_eq in Ha.
apply Zopp_inj.
rewrite <- ZOdiv_opp_l, Zopp_0.
apply ZOdiv_small.
generalize (Zabs_non_eq a).
omega.
Qed.

Theorem ZOmod_small_abs :
  forall a b,
  (Zabs a < b)%Z -> ZOmod a b = a.
Proof.
intros a b Ha.
destruct (Zle_or_lt 0 a) as [H|H].
apply ZOmod_small.
split.
exact H.
now rewrite Zabs_eq in Ha.
apply Zopp_inj.
rewrite <- ZOmod_opp_l.
apply ZOmod_small.
generalize (Zabs_non_eq a).
omega.
Qed.

Section Fcore_digits.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Definition Zdigit n k := ZOmod (ZOdiv n (Zpower beta k)) beta.

Theorem Zdigit_lt :
  forall n k,
  (k < 0)%Z ->
  Zdigit n k = Z0.
Proof.
intros n [|k|k] Hk ; try easy.
now case n.
Qed.

Theorem Zdigit_0 :
  forall k, Zdigit 0 k = Z0.
Proof.
intros k.
unfold Zdigit.
rewrite ZOdiv_0_l.
apply ZOmod_0_l.
Qed.

Theorem Zdigit_opp :
  forall n k,
  Zdigit (-n) k = Zopp (Zdigit n k).
Proof.
intros n k.
unfold Zdigit.
rewrite ZOdiv_opp_l.
apply ZOmod_opp_l.
Qed.

Theorem Zdigit_ge_Zpower_pos :
  forall e n,
  (0 <= n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof.
intros e n Hn k Hk.
unfold Zdigit.
rewrite ZOdiv_small.
apply ZOmod_0_l.
split.
apply Hn.
apply Zlt_le_trans with (1 := proj2 Hn).
replace k with (e + (k - e))%Z by ring.
rewrite Zpower_exp.
rewrite <- (Zmult_1_r (beta ^ e)) at 1.
apply Zmult_le_compat_l.
apply (Zlt_le_succ 0).
apply Zpower_gt_0.
now apply Zle_minus_le_0.
apply Zlt_le_weak.
now apply Zle_lt_trans with n.
generalize (Zle_lt_trans _ _ _ (proj1 Hn) (proj2 Hn)).
clear.
now destruct e as [|e|e].
apply Zle_ge.
now apply Zle_minus_le_0.
Qed.

Theorem Zdigit_ge_Zpower :
  forall e n,
  (Zabs n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof.
intros e [|n|n] Hn k.
easy.
apply Zdigit_ge_Zpower_pos.
now split.
intros He.
change (Zneg n) with (Zopp (Zpos n)).
rewrite Zdigit_opp.
rewrite Zdigit_ge_Zpower_pos with (2 := He).
apply Zopp_0.
now split.
Qed.

Theorem Zdigit_not_0_pos :
  forall e n, (0 <= e)%Z ->
  (Zpower beta e <= n < Zpower beta (e + 1))%Z ->
  Zdigit n e <> Z0.
Proof.
intros e n He (Hn1,Hn2).
unfold Zdigit.
rewrite <- ZOdiv_mod_mult.
rewrite ZOmod_small.
intros H.
apply Zle_not_lt with (1 := Hn1).
rewrite (ZO_div_mod_eq n (beta ^ e)).
rewrite H, Zmult_0_r, Zplus_0_l.
apply ZOmod_lt_pos_pos.
apply Zle_trans with (2 := Hn1).
apply Zpower_ge_0.
now apply Zpower_gt_0.
split.
apply Zle_trans with (2 := Hn1).
apply Zpower_ge_0.
replace (beta ^ e * beta)%Z with (beta ^ (e + 1))%Z.
exact Hn2.
rewrite <- (Zmult_1_r beta) at 3.
apply Zpower_exp.
now apply Zle_ge.
easy.
Qed.

Theorem Zdigit_mul_pow :
  forall n k k', (0 <= k')%Z ->
  Zdigit (n * Zpower beta k') k = Zdigit n (k - k').
Proof.
intros n k k' Hk'.
destruct (Zle_or_lt k' k) as [H|H].
revert k H.
pattern k' ; apply Zlt_0_ind with (2 := Hk').
clear k' Hk'.
intros k' IHk' Hk' k H.
unfold Zdigit.
pattern k at 1 ; replace k with (k - k' + k')%Z by ring.
rewrite Zpower_exp by omega.
rewrite ZOdiv_mult_cancel_r.
apply refl_equal.
apply Zgt_not_eq.
now apply Zpower_gt_0.
destruct (Zle_or_lt 0 k) as [H0|H0].
rewrite (Zdigit_lt n) by omega.
unfold Zdigit.
replace k' with (k' - k + k)%Z by ring.
rewrite Zpower_exp by omega.
rewrite Zmult_assoc, ZO_div_mult.
replace (k' - k)%Z with (k' - k - 1 + 1)%Z by ring.
rewrite Zpower_exp by omega.
rewrite Zmult_assoc.
change (Zpower beta 1) with (beta * 1)%Z.
rewrite Zmult_1_r.
apply ZO_mod_mult.
apply Zgt_not_eq.
now apply Zpower_gt_0.
rewrite Zdigit_lt with (1 := H0).
apply sym_eq.
apply Zdigit_lt.
omega.
Qed.

Theorem Zdigit_div_pow :
  forall n k k', (0 <= k)%Z -> (0 <= k')%Z ->
  Zdigit (n / Zpower beta k') k = Zdigit n (k + k').
Proof.
intros n k k' Hk Hk'.
unfold Zdigit.
rewrite ZOdiv_ZOdiv.
rewrite Zplus_comm.
now rewrite Zpower_exp ; try apply Zle_ge.
Qed.

Theorem Zdigit_mod_pow :
  forall n k k', (k < k')%Z ->
  Zdigit (ZOmod n (Zpower beta k')) k = Zdigit n k.
Proof.
intros n k k' Hk.
destruct (Zle_or_lt 0 k) as [H|H].
unfold Zdigit.
rewrite <- 2!ZOdiv_mod_mult.
apply (f_equal (fun x => ZOdiv x (beta ^ k))).
replace k' with (k + 1 + (k' - (k + 1)))%Z by ring.
rewrite Zpower_exp by omega.
rewrite Zmult_comm.
rewrite Zpower_exp by omega.
change (Zpower beta 1) with (beta * 1)%Z.
rewrite Zmult_1_r.
apply ZOmod_mod_mult.
now rewrite 2!Zdigit_lt.
Qed.

Theorem Zpower_le :
  forall e1 e2, (e1 <= e2)%Z ->
  (Zpower beta e1 <= Zpower beta e2)%Z.
Proof.
intros e1 e2 He.
destruct (Zle_or_lt 0 e1)%Z as [H1|H1].
replace e2 with (e2 - e1 + e1)%Z by ring.
rewrite Zpower_exp.
rewrite <- (Zmult_1_l (beta ^ e1)) at 1.
apply Zmult_le_compat_r.
apply (Zlt_le_succ 0).
apply Zpower_gt_0.
now apply Zle_minus_le_0.
apply Zpower_ge_0.
apply Zle_ge.
now apply Zle_minus_le_0.
now apply Zle_ge.
clear He.
destruct e1 as [|e1|e1] ; try easy.
apply Zpower_ge_0.
Qed.

Theorem Zdigit_mod_pow_ge :
  forall n k k', (0 <= k' <= k)%Z ->
  Zdigit (ZOmod n (Zpower beta k')) k = Z0.
Proof.
intros n k k' Hk.
unfold Zdigit.
rewrite ZOdiv_small_abs.
apply ZOmod_0_l.
apply Zlt_le_trans with (Zpower beta k').
rewrite <- (Zabs_eq (beta ^ k')) at 2 by apply Zpower_ge_0.
apply ZOmod_lt.
apply Zgt_not_eq.
now apply Zpower_gt_0.
now apply Zpower_le.
Qed.

Fixpoint Zsum_digit f k :=
  match k with
  | O => Z0
  | S k => (Zsum_digit f k + f (Z_of_nat k) * Zpower beta (Z_of_nat k))%Z
  end.

Theorem Zsum_digit_digit :
  forall n k,
  Zsum_digit (Zdigit n) k = ZOmod n (Zpower beta (Z_of_nat k)).
Proof.
intros n.
induction k.
apply sym_eq.
apply ZOmod_1_r.
simpl Zsum_digit.
rewrite IHk.
unfold Zdigit.
rewrite <- ZOdiv_mod_mult.
rewrite <- (ZOmod_mod_mult n beta).
rewrite Zmult_comm.
replace (beta ^ Z_of_nat k * beta)%Z with (Zpower beta (Z_of_nat (S k))).
rewrite Zplus_comm, Zmult_comm.
apply sym_eq.
apply ZO_div_mod_eq.
rewrite inj_S.
unfold Zsucc.
rewrite Zpower_exp.
apply f_equal.
apply Zmult_1_r.
apply Zle_ge.
apply Zle_0_nat.
easy.
Qed.

Theorem Zpower_gt :
  forall n, (n < Zpower beta n)%Z.
Proof.
intros [|n|n] ; try easy.
simpl.
rewrite Zpower_pos_nat.
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
induction (nat_of_P n).
easy.
rewrite inj_S.
change (Zpower_nat beta (S n0)) with (beta * Zpower_nat beta n0)%Z.
unfold Zsucc.
apply Zlt_le_trans with (beta * (Z_of_nat n0 + 1))%Z.
clear.
apply Zlt_0_minus_lt.
replace (beta * (Z_of_nat n0 + 1) - (Z_of_nat n0 + 1))%Z with ((beta - 1) * (Z_of_nat n0 + 1))%Z by ring.
apply Zmult_lt_0_compat.
cut (2 <= beta)%Z. omega.
apply Zle_bool_imp_le.
apply beta.
apply (Zle_lt_succ 0).
apply Zle_0_nat.
apply Zmult_le_compat_l.
now apply Zlt_le_succ.
apply Zle_trans with 2%Z.
easy.
apply Zle_bool_imp_le.
apply beta.
Qed.

Theorem Zdigit_ext :
  forall n1 n2,
  (forall k, (0 <= k)%Z -> Zdigit n1 k = Zdigit n2 k) ->
  n1 = n2.
Proof.
intros n1 n2 H.
rewrite <- (ZOmod_small_abs n1 (Zpower beta (Zmax (Zabs n1) (Zabs n2)))).
rewrite <- (ZOmod_small_abs n2 (Zpower beta (Zmax (Zabs n1) (Zabs n2)))) at 2.
replace (Zmax (Zabs n1) (Zabs n2)) with (Z_of_nat (Zabs_nat (Zmax (Zabs n1) (Zabs n2)))).
rewrite <- 2!Zsum_digit_digit.
induction (Zabs_nat (Zmax (Zabs n1) (Zabs n2))).
easy.
simpl.
rewrite H, IHn.
apply refl_equal.
apply Zle_0_nat.
rewrite inj_Zabs_nat.
apply Zabs_eq.
apply Zle_trans with (Zabs n1).
apply Zabs_pos.
apply Zle_max_l.
apply Zlt_le_trans with (Zpower beta (Zabs n2)).
apply Zpower_gt.
apply Zpower_le.
apply Zle_max_r.
apply Zlt_le_trans with (Zpower beta (Zabs n1)).
apply Zpower_gt.
apply Zpower_le.
apply Zle_max_l.
Qed.

Definition Zscale n k :=
  if Zle_bool 0 k then n * Zpower beta k else ZOdiv n (Zpower beta (-k)).

Theorem Zdigit_scale :
  forall n k k', (0 <= k')%Z ->
  Zdigit (Zscale n k) k' = Zdigit n (k' - k).
Proof.
intros n k k' Hk'.
unfold Zscale.
case Zle_bool_spec ; intros Hk.
now apply Zdigit_mul_pow.
apply Zdigit_div_pow with (1 := Hk').
omega.
Qed.

Definition Zslice n k1 k2 :=
  if Zle_bool 0 k2 then ZOmod (Zscale n (-k1)) (Zpower beta k2) else Z0.

Theorem Zdigit_slice :
  forall n k1 k2 k, (0 <= k < k2) ->
  Zdigit (Zslice n k1 k2) k = Zdigit n (k1 + k).
Proof.
intros n k1 k2 k Hk.
unfold Zslice.
rewrite Zle_bool_true.
rewrite Zdigit_mod_pow by apply Hk.
rewrite Zdigit_scale by apply Hk.
unfold Zminus.
now rewrite Zopp_involutive, Zplus_comm.
omega.
Qed.

Theorem Zdigit_slice_ge :
  forall n k1 k2 k, (k2 <= k)%Z ->
  Zdigit (Zslice n k1 k2) k = Z0.
Proof.
intros n k1 k2 k Hk.
unfold Zslice.
case Zle_bool_spec ; intros Hk2.
apply Zdigit_mod_pow_ge.
now split.
apply Zdigit_0.
Qed.

Theorem Zslice_slice :
  forall n k1 k2 k1' k2', (0 <= k1' <= k2)%Z ->
  Zslice (Zslice n k1 k2) k1' k2' = Zslice n (k1 + k1') (Zmin (k2 - k1') k2').
Proof.
intros n k1 k2 k1' k2' Hk1'.
destruct (Zle_or_lt 0 k2') as [Hk2'|Hk2'].
apply Zdigit_ext.
intros k Hk.
destruct (Zle_or_lt (Zmin (k2 - k1') k2') k) as [Hk'|Hk'].
rewrite (Zdigit_slice_ge n (k1 + k1')) with (1 := Hk').
destruct (Zle_or_lt k2' k) as [Hk''|Hk''].
now apply Zdigit_slice_ge.
rewrite Zdigit_slice by now split.
apply Zdigit_slice_ge.
zify ; omega.
rewrite Zdigit_slice by (zify ; omega).
rewrite (Zdigit_slice n (k1 + k1')) by now split.
rewrite Zdigit_slice.
now rewrite Zplus_assoc.
zify ; omega.
unfold Zslice.
rewrite Zmin_right.
now rewrite Zle_bool_false.
omega.
Qed.

End Fcore_digits.

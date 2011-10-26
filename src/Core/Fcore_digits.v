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

Theorem Zmult_pow :
  forall n k1 k2, (0 <= k1)%Z -> (0 <= k2)%Z ->
  (Zpower n k1 * Zpower n k2)%Z = Zpower n (k1 + k2).
Proof.
intros n k1 k2 H1 H2.
apply sym_eq.
now apply Zpower_exp ; apply Zle_ge.
Qed.

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

Theorem ZOdiv_plus :
  forall a b c, (0 <= a * b)%Z ->
  (ZOdiv (a + b) c = ZOdiv a c + ZOdiv b c + ZOdiv (ZOmod a c + ZOmod b c) c)%Z.
Proof.
intros a b c Hab.
destruct (Z_eq_dec c 0) as [Zc|Zc].
now rewrite Zc, 4!ZOdiv_0_r.
apply Zmult_reg_r with (1 := Zc).
rewrite 2!Zmult_plus_distr_l.
assert (forall d, (d / c) * c = d - d mod c)%Z.
intros d.
rewrite ZOmod_eq.
ring.
rewrite 4!H.
rewrite <- ZOplus_mod with (1 := Hab).
ring.
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
rewrite <- Zmult_pow.
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
apply sym_eq.
now apply (Zmult_pow beta e 1).
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
apply (f_equal (fun x => ZOmod x beta)).
pattern k at 1 ; replace k with (k - k' + k')%Z by ring.
rewrite <- Zmult_pow with (2 := Hk').
apply ZOdiv_mult_cancel_r.
apply Zgt_not_eq.
now apply Zpower_gt_0.
now apply Zle_minus_le_0.
destruct (Zle_or_lt 0 k) as [H0|H0].
rewrite (Zdigit_lt n) by omega.
unfold Zdigit.
replace k' with (k' - k + k)%Z by ring.
rewrite <- Zmult_pow with (2 := H0).
rewrite Zmult_assoc, ZO_div_mult.
replace (k' - k)%Z with (k' - k - 1 + 1)%Z by ring.
rewrite Zpower_exp by omega.
rewrite Zmult_assoc.
change (Zpower beta 1) with (beta * 1)%Z.
rewrite Zmult_1_r.
apply ZO_mod_mult.
apply Zgt_not_eq.
now apply Zpower_gt_0.
apply Zle_minus_le_0.
now apply Zlt_le_weak.
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
now rewrite <- Zmult_pow.
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
rewrite <- Zmult_pow by easy.
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
rewrite <- Zmult_pow with (2 := H1).
rewrite <- (Zmult_1_l (beta ^ e1)) at 1.
apply Zmult_le_compat_r.
apply (Zlt_le_succ 0).
apply Zpower_gt_0.
now apply Zle_minus_le_0.
apply Zpower_ge_0.
now apply Zle_minus_le_0.
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
apply sym_eq.
rewrite <- (Zmult_1_r beta) at 2.
apply (Zmult_pow beta (Z_of_nat k) 1).
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

Theorem ZOmod_plus_pow_digit :
  forall u v n, (0 <= u * v)%Z ->
  (forall k, (0 <= k < n)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  ZOmod (u + v) (Zpower beta n) = (ZOmod u (Zpower beta n) + ZOmod v (Zpower beta n))%Z.
Proof.
intros u v n Huv Hd.
destruct (Zle_or_lt 0 n) as [Hn|Hn].
rewrite ZOplus_mod with (1 := Huv).
apply ZOmod_small_abs.
generalize (Zle_refl n).
pattern n at -2 ; rewrite <- Zabs_eq with (1 := Hn).
rewrite <- (inj_Zabs_nat n).
induction (Zabs_nat n) as [|p IHp].
now rewrite 2!ZOmod_1_r.
rewrite <- 2!Zsum_digit_digit.
simpl Zsum_digit.
rewrite inj_S.
intros Hn'.
replace (Zsum_digit (Zdigit u) p + Zdigit u (Z_of_nat p) * beta ^ Z_of_nat p +
  (Zsum_digit (Zdigit v) p + Zdigit v (Z_of_nat p) * beta ^ Z_of_nat p))%Z with
  (Zsum_digit (Zdigit u) p + Zsum_digit (Zdigit v) p +
  (Zdigit u (Z_of_nat p) + Zdigit v (Z_of_nat p)) * beta ^ Z_of_nat p)%Z by ring.
apply (Zle_lt_trans _ _ _ (Zabs_triangle _ _)).
replace (beta ^ Zsucc (Z_of_nat p))%Z with (beta ^ Z_of_nat p + (beta - 1) * beta ^ Z_of_nat p)%Z.
apply Zplus_lt_le_compat.
rewrite 2!Zsum_digit_digit.
apply IHp.
now apply Zle_succ_le.
rewrite Zabs_Zmult.
rewrite (Zabs_eq (beta ^ Z_of_nat p)) by apply Zpower_ge_0.
apply Zmult_le_compat_r. 2: apply Zpower_ge_0.
apply Zlt_succ_le.
assert (forall u v, Zabs (Zdigit u v) < Zsucc (beta -  1))%Z.
clear ; intros n k.
assert (0 < beta)%Z.
apply Zlt_le_trans with 2%Z.
apply refl_equal.
apply Zle_bool_imp_le.
apply beta.
replace (Zsucc (beta - 1)) with (Zabs beta).
apply ZOmod_lt.
now apply Zgt_not_eq.
rewrite Zabs_eq.
apply Zsucc_pred.
now apply Zlt_le_weak.
assert (0 <= Z_of_nat p < n)%Z.
split.
apply Zle_0_nat.
apply Zgt_lt.
now apply Zle_succ_gt.
destruct (Hd (Z_of_nat p) H0) as [K|K] ; rewrite K.
apply H.
rewrite Zplus_0_r.
apply H.
unfold Zsucc.
ring_simplify.
rewrite <- Zmult_pow.
change (beta ^1)%Z with (beta * 1)%Z.
now rewrite Zmult_1_r.
apply Zle_0_nat.
easy.
destruct n as [|n|n] ; try easy.
now rewrite 3!ZOmod_0_r.
Qed.  

Theorem ZOdiv_plus_pow_digit :
  forall u v n, (0 <= u * v)%Z ->
  (forall k, (0 <= k < n)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  ZOdiv (u + v) (Zpower beta n) = (ZOdiv u (Zpower beta n) + ZOdiv v (Zpower beta n))%Z.
Proof.
intros u v n Huv Hd.
rewrite <- (Zplus_0_r (u / beta ^ n + v / beta ^ n)).
rewrite ZOdiv_plus with (1 := Huv).
rewrite <- ZOmod_plus_pow_digit by assumption.
apply f_equal.
destruct (Zle_or_lt 0 n) as [Hn|Hn].
apply ZOdiv_small_abs.
rewrite <- Zabs_eq.
apply ZOmod_lt.
apply Zgt_not_eq.
now apply Zpower_gt_0.
apply Zpower_ge_0.
clear -Hn.
destruct n as [|n|n] ; try easy.
apply ZOdiv_0_r.
Qed.

Theorem Zdigit_plus :
  forall u v, (0 <= u * v)%Z ->
  (forall k, (0 <= k)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  forall k,
  Zdigit (u + v) k = (Zdigit u k + Zdigit v k)%Z.
Proof.
intros u v Huv Hd k.
destruct (Zle_or_lt 0 k) as [Hk|Hk].
unfold Zdigit.
rewrite ZOdiv_plus_pow_digit with (1 := Huv).
rewrite <- (Zmult_1_r beta) at 3 5 7.
change (beta * 1)%Z with (beta ^1)%Z.
apply ZOmod_plus_pow_digit.
destruct (Zle_or_lt 0 u) as [Hu|Hu].
destruct (Zle_or_lt 0 v) as [Hv|Hv].
apply Zmult_le_0_compat.
apply ZO_div_pos with (1 := Hu).
apply Zpower_ge_0.
apply ZO_div_pos with (1 := Hv).
apply Zpower_ge_0.
destruct (Zle_lt_or_eq _ _ Hu) as [Hu'|Hu'].
elim Zle_not_lt with (1 := Huv).
rewrite <- (Zmult_0_r u).
unfold Zlt.
rewrite <- Zmult_compare_compat_l.
easy.
now apply Zlt_gt.
now rewrite <- Hu', ZOdiv_0_l.
destruct (Zle_or_lt v 0) as [Hv|Hv].
rewrite <- (Zopp_involutive u), <- (Zopp_involutive v).
rewrite ZOdiv_opp_l, (ZOdiv_opp_l (-v)).
rewrite Zmult_opp_opp.
apply Zmult_le_0_compat.
apply ZO_div_pos.
clear -Hu ; omega.
apply Zpower_ge_0.
apply ZO_div_pos.
clear -Hv ; omega.
apply Zpower_ge_0.
elim Zle_not_lt with (1 := Huv).
rewrite <- (Zmult_0_l v).
unfold Zlt.
rewrite <- Zmult_compare_compat_r.
easy.
now apply Zlt_gt.
intros k' (Hk1,Hk2).
rewrite 2!Zdigit_div_pow by assumption.
apply Hd.
now apply Zplus_le_0_compat.
intros k' (Hk1,Hk2).
now apply Hd.
now rewrite 3!Zdigit_lt.
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

Theorem Zscale_mul_pow :
  forall n k k', (0 <= k)%Z ->
  Zscale (n * Zpower beta k) k' = Zscale n (k + k').
Proof.
intros n k k' Hk.
unfold Zscale.
case Zle_bool_spec ; intros Hk'.
rewrite Zle_bool_true.
rewrite <- Zmult_assoc.
apply f_equal.
now apply Zmult_pow.
now apply Zplus_le_0_compat.
case Zle_bool_spec ; intros Hk''.
pattern k at 1 ; replace k with (k + k' + -k')%Z by ring.
assert (0 <= -k')%Z by omega.
rewrite <- Zmult_pow by easy.
rewrite Zmult_assoc, ZO_div_mult.
apply refl_equal.
apply Zgt_not_eq.
now apply Zpower_gt_0.
replace (-k')%Z with (-(k+k') + k)%Z by ring.
rewrite <- Zmult_pow with (2 := Hk).
apply ZOdiv_mult_cancel_r.
apply Zgt_not_eq.
now apply Zpower_gt_0.
omega.
Qed.

Theorem Zscale_scale :
  forall n k k', (0 <= k)%Z ->
  Zscale (Zscale n k) k' = Zscale n (k + k').
Proof.
intros n k k' Hk.
unfold Zscale at 2.
rewrite Zle_bool_true with (1 := Hk).
now apply Zscale_mul_pow.
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

Theorem Zslice_mul_pow :
  forall n k k1 k2, (0 <= k)%Z ->
  Zslice (n * Zpower beta k) k1 k2 = Zslice n (k1 - k) k2.
Proof.
intros n k k1 k2 Hk.
unfold Zslice.
case Zle_bool_spec ; intros Hk2.
2: apply refl_equal.
rewrite Zscale_mul_pow with (1 := Hk).
now replace (- (k1 - k))%Z with (k + -k1)%Z by ring.
Qed.

Theorem Zslice_div_pow_ge :
  forall n k k1 k2, (0 <= k)%Z -> (0 <= k1)%Z ->
  Zslice (n / Zpower beta k) k1 k2 = Zslice n (k1 + k) k2.
Proof.
intros n k k1 k2 Hk Hk1.
unfold Zslice.
case Zle_bool_spec ; intros Hk2.
2: apply refl_equal.
apply (f_equal (fun x => ZOmod x (beta ^ k2))).
unfold Zscale.
case Zle_bool_spec ; intros Hk1'.
replace k1 with Z0 by omega.
case Zle_bool_spec ; intros Hk'.
replace k with Z0 by omega.
simpl.
now rewrite ZOdiv_1_r.
rewrite Zopp_involutive.
apply Zmult_1_r.
rewrite Zle_bool_false by omega.
rewrite 2!Zopp_involutive, Zplus_comm.
rewrite <- Zmult_pow by assumption.
apply ZOdiv_ZOdiv.
Qed.

Theorem Zslice_scale :
  forall n k k1 k2, (0 <= k1)%Z ->
  Zslice (Zscale n k) k1 k2 = Zslice n (k1 - k) k2.
Proof.
intros n k k1 k2 Hk1.
unfold Zscale.
case Zle_bool_spec; intros Hk.
now apply Zslice_mul_pow.
apply Zslice_div_pow_ge with (2 := Hk1).
omega.
Qed.

Theorem Zslice_div_pow :
  forall n k k1 k2, (0 <= k)%Z ->
  Zslice (n / Zpower beta k) k1 k2 = Zscale (Zslice n k (k1 + k2)) (-k1).
Proof.
intros n k k1 k2 Hk.
apply Zdigit_ext.
intros k' Hk'.
rewrite Zdigit_scale with (1 := Hk').
unfold Zminus.
rewrite (Zplus_comm k'), Zopp_involutive.
destruct (Zle_or_lt k2 k') as [Hk2|Hk2].
rewrite Zdigit_slice_ge with (1 := Hk2).
apply sym_eq.
apply Zdigit_slice_ge.
now apply Zplus_le_compat_l.
rewrite Zdigit_slice by now split.
destruct (Zle_or_lt 0 (k1 + k')) as [Hk1'|Hk1'].
rewrite Zdigit_slice by omega.
rewrite Zdigit_div_pow by assumption.
apply f_equal.
ring.
now rewrite 2!Zdigit_lt.
Qed.

End Fcore_digits.

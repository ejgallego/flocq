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

Theorem Zdiv_mod_mult :
  forall n a b, (0 <= a)%Z -> (0 <= b)%Z ->
  (Zmod n (a * b) / a)%Z = Zmod (n / a) b.
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

Section Fcore_digits.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Definition Zdigit n k := Zmod (Zdiv n (Zpower beta k)) beta.

Theorem Zdigit_below :
  forall n k,
  (k < 0)%Z ->
  Zdigit n k = Z0.
Proof.
intros n [|k|k] Hk ; try easy.
now case n.
Qed.

Theorem Zdigit_ge_Zpower :
  forall e n,
  (0 <= n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof.
intros e n Hn k Hk.
unfold Zdigit.
rewrite Zdiv_small.
apply Zmod_0_l.
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

Theorem Zdigit_not_0 :
  forall e n, (0 <= e)%Z ->
  (Zpower beta e <= n < Zpower beta (e + 1))%Z ->
  Zdigit n e <> Z0.
Proof.
intros e n He (Hn1,Hn2).
unfold Zdigit.
rewrite <- Zdiv_mod_mult.
rewrite Zmod_small.
intros H.
apply Zle_not_lt with (1 := Hn1).
assert (beta ^ e > 0)%Z.
apply Zlt_gt.
now apply Zpower_gt_0.
rewrite (Z_div_mod_eq n (beta^e)) with (1 := H0).
rewrite H, Zmult_0_r, Zplus_0_l.
now apply Z_mod_lt.
split.
apply Zle_trans with (2 := Hn1).
apply Zpower_ge_0.
replace (beta ^ e * beta)%Z with (beta ^ (e + 1))%Z.
exact Hn2.
rewrite <- (Zmult_1_r beta) at 3.
apply Zpower_exp.
now apply Zle_ge.
easy.
apply Zpower_ge_0.
apply Zle_trans with 2%Z.
easy.
apply Zle_bool_imp_le.
apply beta.
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
rewrite Zdiv_mult_cancel_r.
apply refl_equal.
apply Zgt_not_eq.
now apply Zpower_gt_0.
destruct (Zle_or_lt 0 k) as [H0|H0].
rewrite (Zdigit_below n) by omega.
unfold Zdigit.
replace k' with (k' - k + k)%Z by ring.
rewrite Zpower_exp by omega.
rewrite Zmult_assoc, Z_div_mult.
replace (k' - k)%Z with (k' - k - 1 + 1)%Z by ring.
rewrite Zpower_exp by omega.
rewrite Zmult_assoc.
change (Zpower beta 1) with (beta * 1)%Z.
rewrite Zmult_1_r.
apply Z_mod_mult.
apply Zlt_gt.
now apply Zpower_gt_0.
rewrite Zdigit_below with (1 := H0).
apply sym_eq.
apply Zdigit_below.
omega.
Qed.

Theorem Zdigit_div_pow :
  forall n k k', (0 <= k)%Z -> (0 <= k')%Z ->
  Zdigit (n / Zpower beta k') k = Zdigit n (k + k').
Proof.
intros n k k' Hk Hk'.
unfold Zdigit.
rewrite Zdiv_Zdiv by apply Zpower_ge_0.
rewrite Zplus_comm.
now rewrite Zpower_exp ; try apply Zle_ge.
Qed.

Fixpoint Zsum_digit f k :=
  match k with
  | O => Z0
  | S k => (Zsum_digit f k + f (Z_of_nat k) * Zpower beta (Z_of_nat k))%Z
  end.

Theorem Zsum_digit_digit :
  forall n k,
  Zsum_digit (Zdigit n) k = Zmod n (Zpower beta (Z_of_nat k)).
Proof.
intros n.
induction k.
apply sym_eq.
apply Zmod_1_r.
simpl Zsum_digit.
rewrite IHk.
unfold Zdigit.
rewrite <- Zdiv_mod_mult.
rewrite <- (Zmod_mod_mult n beta).
rewrite Zmult_comm.
replace (beta ^ Z_of_nat k * beta)%Z with (Zpower beta (Z_of_nat (S k))).
rewrite Zplus_comm, Zmult_comm.
apply sym_eq.
apply Z_div_mod_eq.
apply Zlt_gt.
apply Zpower_gt_0.
apply Zle_0_nat.
rewrite inj_S.
unfold Zsucc.
rewrite Zpower_exp.
apply f_equal.
apply Zmult_1_r.
apply Zle_ge.
apply Zle_0_nat.
easy.
apply Zlt_le_trans with 2%Z.
easy.
apply Zle_bool_imp_le.
apply beta.
apply Zpower_ge_0.
apply Zpower_ge_0.
apply Zle_trans with 2%Z.
easy.
apply Zle_bool_imp_le.
apply beta.
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

Theorem Zdigit_ext_pos :
  forall n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  (forall k, Zdigit n1 k = Zdigit n2 k) ->
  n1 = n2.
Proof.
intros n1 n2 Hn1 Hn2 H.
rewrite <- (Zmod_small n1 (Zpower beta (Zmax n1 n2))).
rewrite <- (Zmod_small n2 (Zpower beta (Zmax n1 n2))) at 2.
replace (Zmax n1 n2) with (Z_of_nat (Zabs_nat (Zmax n1 n2))).
rewrite <- 2!Zsum_digit_digit.
induction (Zabs_nat (Zmax n1 n2)).
easy.
simpl.
now rewrite H, IHn.
rewrite inj_Zabs_nat.
apply Zabs_eq.
apply Zle_trans with (1 := Hn1).
apply Zle_max_l.
split.
exact Hn2.
apply Zlt_le_trans with (Zpower beta n2).
apply Zpower_gt.
apply Zpower_le.
apply Zle_max_r.
split.
exact Hn1.
apply Zlt_le_trans with (Zpower beta n1).
apply Zpower_gt.
apply Zpower_le.
apply Zle_max_l.
Qed.

End Fcore_digits.

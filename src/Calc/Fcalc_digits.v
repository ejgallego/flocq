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

(** * Functions for computing the number of digits of integers
      and related theorems. *)

Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_float_prop.

Section Fcalc_digits.

Variable beta : radix.
Notation bpow e := (bpow beta e).

(** Computes the number of bits (radix 2) of a positive integer.

It serves as an upper bound on the number of digits to ensure termination.
*)

Fixpoint digits2_Pnat (n : positive) : nat :=
  match n with
  | xH => O
  | xO p => S (digits2_Pnat p)
  | xI p => S (digits2_Pnat p)
  end.

Theorem digits2_Pnat_correct :
  forall n,
  let d := digits2_Pnat n in
  (Zpower_nat 2 d <= Zpos n < Zpower_nat 2 (S d))%Z.
Proof.
intros n d. unfold d. clear.
assert (Hp: forall m, (Zpower_nat 2 (S m) = 2 * Zpower_nat 2 m)%Z) by easy.
induction n ; simpl.
rewrite Zpos_xI, 2!Hp.
omega.
rewrite (Zpos_xO n), 2!Hp.
omega.
now split.
Qed.

Section digits_aux.

Variable p : Z.
Hypothesis Hp : (0 <= p)%Z.

Fixpoint digits_aux (nb pow : Z) (n : nat) { struct n } : Z :=
  match n with
  | O => nb
  | S n => if Zlt_bool p pow then nb else digits_aux (nb + 1) (Zmult beta pow) n
  end.

Lemma digits_aux_invariant :
  forall k n nb,
  (0 <= nb)%Z ->
  (Zpower beta (nb + Z_of_nat k - 1) <= p)%Z ->
  digits_aux (nb + Z_of_nat k) (Zpower beta (nb + Z_of_nat k)) n =
  digits_aux nb (Zpower beta nb) (n + k).
Proof.
induction k ; intros n nb Hnb.
now rewrite Zplus_0_r, plus_0_r.
rewrite inj_S.
unfold Zsucc.
intros H.
rewrite (Zplus_comm _ 1), Zplus_assoc.
rewrite IHk.
rewrite <- plus_n_Sm.
simpl.
generalize (Zlt_cases p (Zpower beta nb)).
case Zlt_bool ; intros Hpp.
elim (Zlt_irrefl p).
apply Zlt_le_trans with (1 := Hpp).
apply Zle_trans with (2 := H).
replace (nb + (Z_of_nat k + 1) - 1)%Z with (nb + Z_of_nat k)%Z by ring.
apply le_Z2R.
rewrite Z2R_Zpower with (1 := Hnb).
rewrite Z2R_Zpower.
apply bpow_le.
omega.
omega.
rewrite Zpower_exp.
unfold Zpower at 2, Zpower_pos, iter_pos.
rewrite Zmult_1_r.
now rewrite Zmult_comm.
now apply Zle_ge.
easy.
omega.
now rewrite <- Zplus_assoc, (Zplus_comm 1).
Qed.

End digits_aux.

Definition digits n :=
  match n with
  | Z0 => Z0
  | Zneg p => digits_aux (Zpos p) 1 beta (digits2_Pnat p)
  | Zpos p => digits_aux n 1 beta (digits2_Pnat p)
  end.

Theorem digits_abs :
  forall n, digits (Zabs n) = digits n.
Proof.
now intros [|n|n].
Qed.

Theorem digits_ln_beta :
  forall n,
  n <> Z0 ->
  digits n = ln_beta beta (Z2R n).
Proof.
intros n Hn.
destruct (ln_beta beta (Z2R n)) as (e, He).
simpl.
specialize (He (Z2R_neq _ _ Hn)).
rewrite <- Z2R_abs in He.
assert (Hn': (0 < Zabs n)%Z).
destruct n ; try easy.
now elim Hn.
rewrite <- digits_abs.
destruct (Zabs n) as [|p|p] ; try (now elim Hn').
clear n Hn Hn'.
simpl.
assert (He1: (0 <= e - 1)%Z).
apply Zlt_0_le_0_pred.
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
apply (Z2R_le 1).
now apply (Zlt_le_succ 0).
assert (He2: (Z_of_nat (Zabs_nat (e - 1)) = e - 1)%Z).
rewrite inj_Zabs_nat.
now apply Zabs_eq.
replace (radix_val beta) with (Zpower beta 1).
replace (digits2_Pnat p) with (digits2_Pnat p - Zabs_nat (e - 1) + Zabs_nat (e - 1)).
rewrite <- digits_aux_invariant.
rewrite He2.
ring_simplify (1 + (e - 1))%Z.
destruct (digits2_Pnat p - Zabs_nat (e - 1)) as [|n].
easy.
simpl.
generalize (Zlt_cases (Zpos p) (Zpower beta e)).
case Zlt_bool ; intros Hpp.
easy.
elim Rlt_not_le with (1 := proj2 He).
rewrite <- Z2R_Zpower.
apply Z2R_le.
now apply Zge_le.
omega.
easy.
rewrite He2.
ring_simplify (1 + (e - 1) - 1)%Z.
apply le_Z2R.
now rewrite Z2R_Zpower.
rewrite plus_comm.
apply le_plus_minus_r.
apply inj_le_rev.
rewrite He2.
cut (e - 1 < Z_of_nat (S (digits2_Pnat p)))%Z.
rewrite inj_S.
omega.
apply (lt_bpow beta).
apply Rle_lt_trans with (1 := proj1 He).
rewrite <- Z2R_Zpower_nat.
apply Z2R_lt.
apply Zlt_le_trans with (Zpower_nat 2 (S (digits2_Pnat p))).
exact (proj2 (digits2_Pnat_correct p)).
clear.
induction (S (digits2_Pnat p)).
easy.
change (2 * Zpower_nat 2 n <= beta * Zpower_nat beta n)%Z.
apply Zmult_le_compat ; try easy.
apply Zle_bool_imp_le.
apply beta.
now apply Zpower_NR0.
apply Zmult_1_r.
Qed.

Theorem digits_gt_0 :
  forall n, (n <> 0)%Z -> (0 < digits n)%Z.
Proof.
intros n H.
rewrite digits_ln_beta with (1 := H).
destruct ln_beta as (e, He). simpl.
apply (lt_bpow beta).
apply Rle_lt_trans with (Rabs (Z2R n)).
simpl.
rewrite <- Z2R_abs.
apply (Z2R_le 1).
apply (Zlt_le_succ 0).
revert H.
case n ; try easy.
intros H.
now elim H.
apply He.
now apply (Z2R_neq _ 0).
Qed.

Theorem digits_ge_0 :
  forall n, (0 <= digits n)%Z.
Proof.
intros n.
destruct (Z_eq_dec n 0) as [H|H].
now rewrite H.
apply Zlt_le_weak.
now apply digits_gt_0.
Qed.

Theorem ln_beta_F2R_digits :
  forall m e, m <> Z0 ->
  (ln_beta beta (F2R (Float beta m e)) = digits m + e :> Z)%Z.
Proof.
intros m e Hm.
rewrite ln_beta_F2R with (1 := Hm).
apply (f_equal (fun v => Zplus v e)).
apply sym_eq.
now apply digits_ln_beta.
Qed.

Theorem digits_shift :
  forall m e,
  m <> Z0 -> (0 <= e)%Z ->
  digits (m * Zpower beta e) = (digits m + e)%Z.
Proof.
intros m e Hm He.
rewrite <- ln_beta_F2R_digits with (1 := Hm).
rewrite digits_ln_beta.
rewrite Z2R_mult.
now rewrite Z2R_Zpower with (1 := He).
contradict Hm.
apply Zmult_integral_l with (2 := Hm).
apply neq_Z2R.
rewrite Z2R_Zpower with (1 := He).
apply Rgt_not_eq.
apply bpow_gt_0.
Qed.

Theorem digits_Zpower :
  forall e,
  (0 <= e)%Z ->
  digits (Zpower beta e) = (e + 1)%Z.
Proof.
intros e He.
rewrite <- (Zmult_1_l (Zpower beta e)).
rewrite digits_shift ; try easy.
apply Zplus_comm.
Qed.

Theorem digits_le :
  forall x y,
  (0 <= x)%Z -> (x <= y)%Z ->
  (digits x <= digits y)%Z.
Proof.
intros x y Hx Hxy.
case (Z_lt_le_dec 0 x).
clear Hx. intros Hx.
assert (Hy: (y <> 0)%Z).
apply sym_not_eq.
apply Zlt_not_eq.
now apply Zlt_le_trans with x.
rewrite 2!digits_ln_beta.
destruct (ln_beta beta (Z2R x)) as (ex, Hex). simpl.
specialize (Hex (Rgt_not_eq _ _ (Z2R_lt _ _ Hx))).
destruct (ln_beta beta (Z2R y)) as (ey, Hey). simpl.
specialize (Hey (Z2R_neq _ _ Hy)).
eapply bpow_lt_bpow.
apply Rle_lt_trans with (1 := proj1 Hex).
apply Rle_lt_trans with (Rabs (Z2R y)).
rewrite Rabs_pos_eq.
apply Rle_trans with (Z2R y).
now apply Z2R_le.
apply RRle_abs.
apply (Z2R_le 0).
now apply Zlt_le_weak.
apply Hey.
exact Hy.
apply sym_not_eq.
now apply Zlt_not_eq.
intros Hx'.
rewrite (Zle_antisym _ _ Hx' Hx).
apply digits_ge_0.
Qed.

Theorem lt_digits :
  forall x y,
  (0 <= y)%Z ->
  (digits x < digits y)%Z ->
  (x < y)%Z.
Proof.
intros x y Hy.
cut (y <= x -> digits y <= digits x)%Z. omega.
now apply digits_le.
Qed.

Theorem Zpower_le_digits :
  forall e x,
  (e < digits x)%Z ->
  (Zpower beta e <= Zabs x)%Z.
Proof.
intros [|e|e] x Hex.
(* *)
apply (Zlt_le_succ 0).
apply lt_digits.
apply Zabs_pos.
now rewrite digits_abs.
2: apply Zabs_pos.
(* *)
apply le_Z2R.
rewrite Z2R_Zpower. 2: easy.
assert (Zx: x <> Z0).
intros H.
apply Zlt_not_le with (1 := Hex).
now rewrite H.
revert Hex.
rewrite digits_ln_beta with (1 := Zx).
destruct (ln_beta beta (Z2R x)) as (ex, Ex).
unfold ln_beta_val.
specialize (Ex (Z2R_neq _ 0 Zx)).
intros Hex.
rewrite <- Z2R_abs in Ex.
apply Rle_trans with (2 := proj1 Ex).
apply bpow_le.
omega.
Qed.

Theorem digits_le_Zpower :
  forall e x,
  (Zabs x < Zpower beta e)%Z ->
  (digits x <= e)%Z.
Proof.
intros e x.
generalize (Zpower_le_digits e x).
omega.
Qed.

Theorem digits_gt_Zpower :
  forall e x,
  (Zpower beta e <= Zabs x)%Z ->
  (e < digits x)%Z.
Proof.
intros [|e|e] x Hex.
(* *)
apply Zlt_le_trans with 1%Z.
apply refl_equal.
rewrite <- digits_abs.
change 1%Z with (digits 1).
now apply digits_le.
(* *)
rewrite (Zpred_succ (Zpos e)).
apply Zlt_le_trans with (1 := Zlt_pred _).
unfold Zsucc.
rewrite <- digits_Zpower. 2: easy.
rewrite <- (digits_abs x).
apply digits_le with (2 := Hex).
apply le_Z2R.
rewrite Z2R_Zpower.
apply bpow_ge_0.
easy.
(* *)
apply Zlt_le_trans with Z0.
apply refl_equal.
apply digits_ge_0.
Qed.

Theorem Zpower_gt_digits :
  forall e x,
  (digits x <= e)%Z ->
  (Zabs x < Zpower beta e)%Z.
Proof.
intros e x Hex.
generalize (digits_gt_Zpower e x).
omega.
Qed.

(** Characterizes the number digits of a product.

This strong version is needed for proofs of division and square root
algorithms, since they involve operation remainders.
*)

Theorem digits_mult_strong :
  forall x y,
  (0 <= x)%Z -> (0 <= y)%Z ->
  (digits (x + y + x * y) <= digits x + digits y)%Z.
Proof.
intros x y Hx Hy.
case (Z_lt_le_dec 0 x).
clear Hx. intros Hx.
case (Z_lt_le_dec 0 y).
clear Hy. intros Hy.
(* . *)
assert (Hxy: (0 < Z2R (x + y + x * y))%R).
apply (Z2R_lt 0).
change Z0 with (0 + 0 + 0)%Z.
apply Zplus_lt_compat.
now apply Zplus_lt_compat.
now apply Zmult_lt_0_compat.
rewrite 3!digits_ln_beta ; try now (apply sym_not_eq ; apply Zlt_not_eq).
apply ln_beta_le with (1 := Rgt_not_eq _ _ Hxy).
rewrite Rabs_pos_eq with (1 := Rlt_le _ _ Hxy).
destruct (ln_beta beta (Z2R x)) as (ex, Hex). simpl.
specialize (Hex (Rgt_not_eq _ _ (Z2R_lt _ _ Hx))).
destruct (ln_beta beta (Z2R y)) as (ey, Hey). simpl.
specialize (Hey (Rgt_not_eq _ _ (Z2R_lt _ _ Hy))).
apply Rlt_le_trans with (Z2R (x + 1) * Z2R (y + 1))%R.
rewrite <- Z2R_mult.
apply Z2R_lt.
apply Zplus_lt_reg_r with (- (x + y + x * y + 1))%Z.
now ring_simplify.
rewrite bpow_plus.
apply Rmult_le_compat ; try (apply (Z2R_le 0) ; omega).
rewrite <- (Rmult_1_r (Z2R (x + 1))).
change (F2R (Float beta (x + 1) 0) <= bpow ex)%R.
apply F2R_p1_le_bpow.
exact Hx.
unfold F2R. rewrite Rmult_1_r.
apply Rle_lt_trans with (Rabs (Z2R x)).
apply RRle_abs.
apply Hex.
rewrite <- (Rmult_1_r (Z2R (y + 1))).
change (F2R (Float beta (y + 1) 0) <= bpow ey)%R.
apply F2R_p1_le_bpow.
exact Hy.
unfold F2R. rewrite Rmult_1_r.
apply Rle_lt_trans with (Rabs (Z2R y)).
apply RRle_abs.
apply Hey.
apply neq_Z2R.
now apply Rgt_not_eq.
(* . *)
intros Hy'.
rewrite (Zle_antisym _ _ Hy' Hy).
rewrite Zmult_0_r, 3!Zplus_0_r.
apply Zle_refl.
intros Hx'.
rewrite (Zle_antisym _ _ Hx' Hx).
rewrite Zmult_0_l, Zplus_0_r, 2!Zplus_0_l.
apply Zle_refl.
Qed.

Theorem digits_mult :
  forall x y,
  (digits (x * y) <= digits x + digits y)%Z.
Proof.
intros x y.
rewrite <- digits_abs.
rewrite <- (digits_abs x).
rewrite <- (digits_abs y).
apply Zle_trans with (digits (Zabs x + Zabs y + Zabs x * Zabs y)).
apply digits_le.
apply Zabs_pos.
rewrite Zabs_Zmult.
generalize (Zabs_pos x) (Zabs_pos y).
omega.
apply digits_mult_strong ; apply Zabs_pos.
Qed.

Theorem digits_mult_ge :
  forall x y,
  (x <> 0)%Z -> (y <> 0)%Z ->
  (digits x + digits y - 1 <= digits (x * y))%Z.
Proof.
intros x y Zx Zy.
cut ((digits x - 1) + (digits y - 1) < digits (x * y))%Z. omega.
apply digits_gt_Zpower.
rewrite Zabs_Zmult.
rewrite Zpower_exp.
apply Zmult_le_compat.
apply Zpower_le_digits.
apply Zlt_pred.
apply Zpower_le_digits.
apply Zlt_pred.
apply Zpower_ge_0.
apply Zpower_ge_0.
generalize (digits_gt_0 x). omega.
generalize (digits_gt_0 y). omega.
Qed.

Theorem digits_shr :
  forall m e,
  (0 <= m)%Z ->
  (0 <= e <= digits m)%Z ->
  digits (m / Zpower beta e) = (digits m - e)%Z.
Proof.
intros m e Hm He.
destruct (Zle_lt_or_eq 0 m Hm) as [Hm'|Hm'].
(* *)
destruct (Zle_lt_or_eq _ _ (proj2 He)) as [He'|He'].
(* . *)
unfold Zminus.
rewrite <- ln_beta_F2R_digits.
2: now apply Zgt_not_eq.
assert (Hp: (0 < Zpower beta e)%Z).
apply lt_Z2R.
rewrite Z2R_Zpower with (1 := proj1 He).
apply bpow_gt_0.
rewrite digits_ln_beta.
rewrite <- Zfloor_div with (1 := Zgt_not_eq _ _ Hp).
rewrite Z2R_Zpower with (1 := proj1 He).
unfold Rdiv.
rewrite <- bpow_opp.
change (Z2R m * bpow (-e))%R with (F2R (Float beta m (-e))).
destruct (ln_beta beta (F2R (Float beta m (-e)))) as (e', E').
simpl.
specialize (E' (Rgt_not_eq _ _ (F2R_gt_0_compat beta (Float beta m (-e)) Hm'))).
apply ln_beta_unique.
rewrite Rabs_pos_eq in E'.
2: now apply F2R_ge_0_compat.
rewrite Rabs_pos_eq.
split.
assert (H': (0 <= e' - 1)%Z).
(* .. *)
cut (1 <= e')%Z. omega.
apply bpow_lt_bpow with beta.
apply Rle_lt_trans with (2 := proj2 E').
simpl.
rewrite <- (Rinv_r (bpow e)).
rewrite <- bpow_opp.
unfold F2R. simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite <- Z2R_Zpower with (1 := proj1 He).
apply Z2R_le.
rewrite <- Zabs_eq with (1 := Hm).
now apply Zpower_le_digits.
apply Rgt_not_eq.
apply bpow_gt_0.
(* .. *)
rewrite <- Z2R_Zpower with (1 := H').
apply Z2R_le.
apply Zfloor_lub.
rewrite Z2R_Zpower with (1 := H').
apply E'.
apply Rle_lt_trans with (2 := proj2 E').
apply Zfloor_lb.
apply (Z2R_le 0).
apply Zfloor_lub.
now apply F2R_ge_0_compat.
apply Zgt_not_eq.
apply Zlt_le_trans with (beta^e / beta^e)%Z.
rewrite Z_div_same_full.
apply refl_equal.
now apply Zgt_not_eq.
apply Z_div_le.
now apply Zlt_gt.
rewrite <- Zabs_eq with (1 := Hm).
now apply Zpower_le_digits.
(* . *)
unfold Zminus.
rewrite He', Zplus_opp_r.
rewrite Zdiv_small.
apply refl_equal.
apply conj with (1 := Hm).
pattern m at 1 ; rewrite <- Zabs_eq with (1 := Hm).
apply Zpower_gt_digits.
apply Zle_refl.
(* *)
revert He.
rewrite <- Hm'.
intros (H1, H2).
simpl.
now rewrite (Zle_antisym _ _ H2 H1).
Qed.

End Fcalc_digits.

Definition radix2 := Build_radix 2 (refl_equal _).

Theorem Z_of_nat_S_digits2_Pnat :
  forall m : positive,
  Z_of_nat (S (digits2_Pnat m)) = digits radix2 (Zpos m).
Proof.
intros m.
rewrite digits_ln_beta. 2: easy.
apply sym_eq.
apply ln_beta_unique.
generalize (digits2_Pnat m) (digits2_Pnat_correct m).
intros d H.
simpl in H.
replace (Z_of_nat (S d) - 1)%Z with (Z_of_nat d).
rewrite <- Z2R_abs.
rewrite <- 2!Z2R_Zpower_nat.
split.
now apply Z2R_le.
now apply Z2R_lt.
rewrite inj_S.
apply Zpred_succ.
Qed.

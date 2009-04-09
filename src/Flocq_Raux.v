Require Export Reals.
Require Export ZArith.

Section Rmissing.

Lemma Rle_0_minus :
  forall x y, (x <= y)%R -> (0 <= y - x)%R.
Proof.
intros.
apply Rge_le.
apply Rge_minus.
now apply Rle_ge.
Qed.

Lemma Rabs_eq_Rabs :
  forall x y : R,
  Rabs x = Rabs y -> x = y \/ x = Ropp y.
Proof.
intros x y H.
unfold Rabs in H.
destruct (Rcase_abs x) as [_|_].
assert (H' := f_equal Ropp H).
rewrite Ropp_involutive in H'.
rewrite H'.
destruct (Rcase_abs y) as [_|_].
left.
apply Ropp_involutive.
now right.
rewrite H.
now destruct (Rcase_abs y) as [_|_] ; [right|left].
Qed.

Lemma Rplus_le_reg_r :
  forall r r1 r2 : R,
  (r1 + r <= r2 + r)%R -> (r1 <= r2)%R.
Proof.
intros.
apply Rplus_le_reg_l with r.
now rewrite 2!(Rplus_comm r).
Qed.

Lemma Rmult_lt_reg_r :
  forall r r1 r2 : R, (0 < r)%R ->
  (r1 * r < r2 * r)%R -> (r1 < r2)%R.
Proof.
intros.
apply Rmult_lt_reg_l with r.
exact H.
now rewrite 2!(Rmult_comm r).
Qed.

Lemma Rmult_le_reg_r :
  forall r r1 r2 : R, (0 < r)%R ->
  (r1 * r <= r2 * r)%R -> (r1 <= r2)%R.
Proof.
intros.
apply Rmult_le_reg_l with r.
exact H.
now rewrite 2!(Rmult_comm r).
Qed.

Lemma exp_increasing_weak :
  forall x y : R,
  (x <= y)%R -> (exp x <= exp y)%R.
Proof.
intros x y [H|H].
apply Rlt_le.
now apply exp_increasing.
rewrite H.
apply Rle_refl.
Qed.

End Rmissing.

Section Z2R.

Fixpoint P2R (p : positive) :=
  match p with
  | xH => 1%R
  | xO xH => 2%R
  | xO t => (2 * P2R t)%R
  | xI xH => 3%R
  | xI t => (1 + 2 * P2R t)%R
  end.

Definition Z2R n :=
  match n with
  | Zpos p => P2R p
  | Zneg p => Ropp (P2R p)
  | Z0 => R0
  end.

Lemma P2R_INR :
  forall n, P2R n = INR (nat_of_P n).
Proof.
induction n ; simpl ; try (
  rewrite IHn ;
  rewrite <- (mult_INR 2) ;
  rewrite <- (nat_of_P_mult_morphism 2) ;
  change (2 * n)%positive with (xO n)).
(* xI *)
rewrite (Rplus_comm 1).
change (nat_of_P (xO n)) with (Pmult_nat n 2).
case n ; intros ; simpl ; try apply refl_equal.
case (Pmult_nat p 4) ; intros ; try apply refl_equal.
rewrite Rplus_0_l.
apply refl_equal.
apply Rplus_comm.
(* xO *)
case n ; intros ; apply refl_equal.
(* xH *)
apply refl_equal.
Qed.

Lemma Z2R_IZR :
  forall n, Z2R n = IZR n.
Proof.
intro.
case n ; intros ; simpl.
apply refl_equal.
apply P2R_INR.
apply Ropp_eq_compat.
apply P2R_INR.
Qed.

Lemma opp_Z2R :
  forall n, Z2R (-n) = (- Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply Ropp_Ropp_IZR.
Qed.

Lemma plus_Z2R :
  forall m n, (Z2R (m + n) = Z2R m + Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply plus_IZR.
Qed.

Lemma minus_IZR :
  forall n m : Z,
  IZR (n - m) = (IZR n - IZR m)%R.
Proof.
intros.
unfold Zminus.
rewrite plus_IZR.
rewrite Ropp_Ropp_IZR.
apply refl_equal.
Qed.

Lemma minus_Z2R :
  forall m n, (Z2R (m - n) = Z2R m - Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply minus_IZR.
Qed.

Lemma mult_Z2R :
  forall m n, (Z2R (m * n) = Z2R m * Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply mult_IZR.
Qed.

Lemma le_Z2R :
  forall m n, (Z2R m <= Z2R n)%R -> (m <= n)%Z.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply le_IZR.
Qed.

Lemma Z2R_le :
  forall m n, (m <= n)%Z -> (Z2R m <= Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_le.
Qed.

Lemma lt_Z2R :
  forall m n, (Z2R m < Z2R n)%R -> (m < n)%Z.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply lt_IZR.
Qed.

Lemma Z2R_lt :
  forall m n, (m < n)%Z -> (Z2R m < Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_lt.
Qed.

Lemma Z2R_lt_le:  forall e1 e2, (Z2R (e1-1) < Z2R e2)%R -> (Z2R e1 <= Z2R e2)%R.
intros.
apply Z2R_le.
assert (e1 -1 < e2)%Z; auto with zarith.
now apply lt_Z2R.
Qed.

Lemma Z2R_neq :
forall m n, (m <> n)%Z -> (Z2R m <> Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_neq.
Qed.

Lemma Rabs_Z2R: forall z, Rabs (Z2R z) = Z2R (Zabs z).
intros.
repeat rewrite Z2R_IZR.
apply Rabs_Zabs. 
Qed.

End Z2R.

Section Floor_Ceil.

Definition Zfloor (x : R) := (up x - 1)%Z.

Lemma Zfloor_lb :
  forall x : R,
  (Z2R (Zfloor x) <= x)%R.
Proof.
intros x.
unfold Zfloor.
rewrite minus_Z2R.
simpl.
rewrite Z2R_IZR.
apply Rplus_le_reg_r with (1 - x)%R.
ring_simplify.
exact (proj2 (archimed x)).
Qed.

Lemma Zfloor_lub :
  forall n x,
  (Z2R n <= x)%R ->
  (n <= Zfloor x)%Z.
Proof.
intros n x Hnx.
apply Zlt_succ_le.
unfold Zfloor.
change (n < Zsucc (Zpred (up x)))%Z.
rewrite <- Zsucc_pred.
apply lt_Z2R.
apply Rle_lt_trans with (1 := Hnx).
rewrite Z2R_IZR.
exact (proj1 (archimed x)).
Qed.

Lemma Zfloor_imp :
  forall n x,
  (Z2R n <= x < Z2R (n + 1))%R ->
  Zfloor x = n.
Proof.
intros n x Hnx.
apply Zle_antisym.
apply Zlt_succ_le.
apply lt_Z2R.
apply Rle_lt_trans with (2 := proj2 Hnx).
apply Zfloor_lb.
now apply Zfloor_lub.
Qed.

End Floor_Ceil.

Section pow.

Record radix :=  { radix_val : Z ; radix_prop :  (2 <= radix_val )%Z }.

Variable r: radix.

Lemma radix_pos: (0 < Z2R (radix_val r))%R.
Proof.
destruct r; simpl.
apply Rle_lt_trans with (Z2R 0).
right; reflexivity.
apply Z2R_lt; auto with zarith.
Qed.

Definition epow e :=
  match e with
  | Zpos p => Z2R (Zpower_pos (radix_val r) p)
  | Zneg p => Rinv (Z2R (Zpower_pos (radix_val r) p))
  | Z0 => R1
  end.

Lemma Zpower_pos_powerRZ :
  forall n m,
  Z2R (Zpower_pos n m) = powerRZ (Z2R n) (Zpos m).
Proof.
intros.
rewrite Zpower_pos_nat.
simpl.
induction (nat_of_P m).
apply refl_equal.
unfold Zpower_nat.
simpl.
rewrite mult_Z2R.
apply Rmult_eq_compat_l.
exact IHn0.
Qed.

Lemma epow_powerRZ :
  forall e,
  epow e = powerRZ (Z2R (radix_val r)) e.
Proof.
destruct e ; unfold epow.
reflexivity.
now rewrite Zpower_pos_powerRZ.
now rewrite Zpower_pos_powerRZ.
Qed.

Lemma  epow_ge_0 :
  forall e : Z, (0 <= epow e)%R.
Proof.
intros.
rewrite epow_powerRZ.
apply powerRZ_le.
change R0 with (Z2R 0).
apply Z2R_lt.
destruct r; simpl; auto with zarith.
Qed.

Lemma epow_gt_0 :
  forall e : Z, (0 < epow e)%R.
Proof.
intros.
rewrite epow_powerRZ.
apply powerRZ_lt.
change R0 with (Z2R 0).
apply Z2R_lt.
destruct r; simpl; auto with zarith.
Qed.

Lemma epow_add :
  forall e1 e2 : Z, (epow (e1 + e2) = epow e1 * epow e2)%R.
Proof.
intros.
repeat rewrite epow_powerRZ.
apply powerRZ_add.
change R0 with (Z2R 0).
apply Z2R_neq.
destruct r; simpl; auto with zarith.
Qed.

Lemma epow_1 :
  epow 1 = Z2R (radix_val r).
Proof.
unfold epow, Zpower_pos, iter_pos.
now rewrite Zmult_1_r.
Qed.

Lemma epow_add1 :
  forall e : Z, (epow (e+1) = Z2R (radix_val r) * epow e)%R.
Proof.
intros.
rewrite <- epow_1.
rewrite <- epow_add.
now rewrite Zplus_comm.
Qed.

Lemma epow_opp :
  forall e : Z, (epow (-e) = /epow e)%R.
Proof.
intros e; destruct e.
simpl; now rewrite Rinv_1.
now replace (-Zpos p)%Z with (Zneg p) by reflexivity.
replace (-Zneg p)%Z with (Zpos p) by reflexivity.
simpl; rewrite Rinv_involutive; trivial.
generalize (epow_gt_0 (Zpos p)).
simpl; auto with real.
Qed.

Lemma Z2R_Zpower :
  forall e : Z,
  (0 <= e)%Z ->
  Z2R (Zpower (radix_val r) e) = epow e.
Proof.
intros [|e|e] H.
split.
split.
now elim H.
Qed.

Lemma epow_lt_aux :
  forall e1 e2 : Z,
  (e1 < e2)%Z -> (epow e1 < epow e2)%R.
Proof.
intros e1 e2 H.
replace e2 with (e1 + (e2 - e1))%Z by ring.
rewrite <- (Rmult_1_r (epow e1)).
rewrite epow_add.
apply Rmult_lt_compat_l.
apply epow_gt_0.
assert (0 < e2 - e1)%Z by omega.
destruct (e2 - e1)%Z ; try discriminate H0.
clear.
unfold epow.
apply (Z2R_lt 1).
rewrite Zpower_pos_nat.
case_eq (nat_of_P p).
intros H.
elim (lt_irrefl 0).
pattern O at 2 ; rewrite <- H.
apply lt_O_nat_of_P.
intros n _.
assert (1 < Zpower_nat (radix_val r) 1)%Z.
unfold Zpower_nat, iter_nat.
rewrite Zmult_1_r.
generalize (radix_prop r).
omega.
induction n.
exact H.
change (S (S n)) with (1 + (S n))%nat.
rewrite Zpower_nat_is_exp.
change 1%Z with (1 * 1)%Z.
apply Zmult_lt_compat.
now split.
now split.
Qed.

Lemma epow_lt :
  forall e1 e2 : Z,
  (e1 < e2)%Z <-> (epow e1 < epow e2)%R.
Proof.
intros e1 e2.
split.
apply epow_lt_aux.
intros H.
apply Zgt_lt.
apply Znot_le_gt.
intros H'.
apply Rlt_not_le with (1 := H).
destruct (Zle_lt_or_eq _ _ H').
apply Rlt_le.
now apply epow_lt_aux.
apply Req_le.
now apply f_equal.
Qed.

Lemma epow_le :
  forall e1 e2 : Z,
  (e1 <= e2)%Z <-> (epow e1 <= epow e2)%R.
Proof.
intros e1 e2.
split.
intros H.
apply Rnot_lt_le.
intros H'.
apply Zle_not_gt with (1 := H).
apply Zlt_gt.
now apply <- epow_lt.
intros H.
apply Znot_gt_le.
intros H'.
apply Rle_not_lt with (1 := H).
apply -> epow_lt.
now apply Zgt_lt.
Qed.

Lemma epow_eq :
  forall e1 e2 : Z,
  e1 = e2 -> epow e1 = epow e2.
Proof.
intros.
apply Rle_antisym.
apply -> epow_le.
now apply Zeq_le.
apply -> epow_le.
apply Zeq_le.
now apply sym_eq.
Qed.

Lemma epow_exp :
  forall e : Z,
  epow e = exp (Z2R e * ln (Z2R (radix_val r))).
Proof.
(* positive case *)
assert (forall e, epow (Zpos e) = exp (Z2R (Zpos e) * ln (Z2R (radix_val r)))).
intros e.
unfold epow.
rewrite Zpower_pos_nat.
unfold Z2R at 2.
rewrite P2R_INR.
induction (nat_of_P e).
rewrite Rmult_0_l.
unfold Zpower_nat, iter_nat.
now rewrite exp_0.
change (S n) with (1 + n)%nat.
rewrite plus_INR.
rewrite Zpower_nat_is_exp.
rewrite Rmult_plus_distr_r.
rewrite exp_plus.
rewrite Rmult_1_l.
rewrite exp_ln.
rewrite <- IHn.
rewrite <- mult_Z2R.
apply f_equal.
unfold Zpower_nat at 1, iter_nat.
now rewrite Zmult_1_r.
apply (Z2R_lt 0).
generalize (radix_prop r).
omega.
(* general case *)
intros [|e|e].
rewrite Rmult_0_l.
now rewrite exp_0.
apply H.
unfold epow.
change (Z2R (Zpower_pos (radix_val r) e)) with (epow (Zpos e)).
rewrite H.
rewrite <- exp_Ropp.
rewrite <- Ropp_mult_distr_l_reverse.
now rewrite <- opp_Z2R.
Qed.

Lemma ln_beta :
  forall x : R,
  {e | (0 < x)%R -> (epow (e - 1)%Z <= x < epow e)%R}.
Proof.
intros x.
set (fact := ln (Z2R (radix_val r))).
(* . *)
assert (0 < fact)%R.
apply exp_lt_inv.
rewrite exp_0.
unfold fact.
rewrite exp_ln.
apply (Z2R_lt 1).
generalize (radix_prop r).
omega.
apply (Z2R_lt 0).
generalize (radix_prop r).
omega.
(* . *)
exists (up (ln x / fact))%Z.
intros Hx.
rewrite 2!epow_exp.
fold fact.
pattern x at 2 3 ; replace x with (exp (ln x / fact * fact)).
split.
rewrite minus_Z2R.
apply exp_increasing_weak.
apply Rmult_le_compat_r.
now apply Rlt_le.
simpl (Z2R 1).
pattern (ln x / fact)%R at 2 ; replace (ln x / fact)%R with (1 + (ln x / fact - 1))%R by ring.
replace (Z2R (up (ln x / fact)) - 1)%R with ((Z2R (up (ln x / fact)) - ln x / fact) + (ln x / fact - 1))%R by ring.
apply Rplus_le_compat_r.
rewrite Z2R_IZR.
eapply for_base_fp.
apply exp_increasing.
apply Rmult_lt_compat_r.
exact H.
rewrite Z2R_IZR.
apply Rplus_lt_reg_r with (- (ln x / fact))%R.
rewrite Rplus_opp_l.
rewrite Rplus_comm.
eapply for_base_fp.
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
now apply exp_ln.
now apply Rgt_not_eq.
Qed.

Lemma epow_lt_epow :
  forall e1 e2,
  (epow (e1 - 1) < epow e2)%R ->
  (e1 <= e2)%Z.
Proof.
intros e1 e2 He.
rewrite (Zsucc_pred e1).
apply Zlt_le_succ.
now apply <- epow_lt.
Qed.

Lemma epow_unique :
  forall x e1 e2,
  (epow (e1 - 1) <= x < epow e1)%R ->
  (epow (e2 - 1) <= x < epow e2)%R ->
  e1 = e2.
Proof.
intros x e1 e2 (H1a,H1b) (H2a,H2b).
apply Zle_antisym ;
  apply epow_lt_epow ;
  apply Rle_lt_trans with x ;
  assumption.
Qed.

Lemma ln_beta_unique :
  forall (x : R) (e : Z),
  (epow (e - 1) <= x < epow e)%R ->
  projT1 (ln_beta x) = e.
Proof.
intros x e1 Hx1.
destruct (ln_beta x) as (e2, Hx2).
apply epow_unique with (2 := Hx1).
simpl.
apply Hx2.
apply Rlt_le_trans with (2 := proj1 Hx1).
apply epow_gt_0.
Qed.

Lemma Zpower_pos_gt_0 :
  forall b p, (0 < b)%Z ->
  (0 < Zpower_pos b p)%Z.
Proof.
intros b p Hb.
apply lt_Z2R.
rewrite Zpower_pos_powerRZ.
apply powerRZ_lt.
now apply (Z2R_lt 0).
Qed.

Lemma Zpower_gt_0 :
  forall b p,
  (0 < b)%Z -> (0 < p)%Z ->
  (0 < Zpower b p)%Z.
Proof.
intros b p Hb Hz.
unfold Zpower.
destruct p ; try easy.
now apply Zpower_pos_gt_0.
Qed.

Lemma Zpower_gt_1 :
  forall p,
  (0 < p)%Z ->
  (1 < Zpower (radix_val r) p)%Z.
Proof.
intros.
apply lt_Z2R.
rewrite Z2R_Zpower.
now apply -> (epow_lt 0).
now apply Zlt_le_weak.
Qed.

End pow.

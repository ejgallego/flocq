Require Export Reals.
Require Export ZArith.

Section Rmissing.

Theorem Rle_0_minus :
  forall x y, (x <= y)%R -> (0 <= y - x)%R.
Proof.
intros.
apply Rge_le.
apply Rge_minus.
now apply Rle_ge.
Qed.

Theorem Rabs_eq_Rabs :
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

Theorem Rplus_le_reg_r :
  forall r r1 r2 : R,
  (r1 + r <= r2 + r)%R -> (r1 <= r2)%R.
Proof.
intros.
apply Rplus_le_reg_l with r.
now rewrite 2!(Rplus_comm r).
Qed.

Theorem Rmult_lt_reg_r :
  forall r r1 r2 : R, (0 < r)%R ->
  (r1 * r < r2 * r)%R -> (r1 < r2)%R.
Proof.
intros.
apply Rmult_lt_reg_l with r.
exact H.
now rewrite 2!(Rmult_comm r).
Qed.

Theorem Rmult_le_reg_r :
  forall r r1 r2 : R, (0 < r)%R ->
  (r1 * r <= r2 * r)%R -> (r1 <= r2)%R.
Proof.
intros.
apply Rmult_le_reg_l with r.
exact H.
now rewrite 2!(Rmult_comm r).
Qed.

Theorem Rmult_eq_reg_r :
  forall r r1 r2 : R, (r1 * r)%R = (r2 * r)%R ->
  r <> 0%R -> r1 = r2.
Proof.
intros r r1 r2 H1 H2.
apply Rmult_eq_reg_l with r.
now rewrite 2!(Rmult_comm r).
exact H2.
Qed.

Theorem exp_increasing_weak :
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

Section Zmissing.

Theorem Zopp_le_cancel :
  forall x y : Z,
  (-y <= -x)%Z -> Zle x y.
Proof.
intros x y Hxy.
apply Zplus_le_reg_r with (-x - y)%Z.
now ring_simplify.
Qed.

End Zmissing.

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

Theorem P2R_INR :
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

Theorem Z2R_IZR :
  forall n, Z2R n = IZR n.
Proof.
intro.
case n ; intros ; simpl.
apply refl_equal.
apply P2R_INR.
apply Ropp_eq_compat.
apply P2R_INR.
Qed.

Theorem opp_Z2R :
  forall n, Z2R (-n) = (- Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply Ropp_Ropp_IZR.
Qed.

Theorem plus_Z2R :
  forall m n, (Z2R (m + n) = Z2R m + Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply plus_IZR.
Qed.

Theorem minus_IZR :
  forall n m : Z,
  IZR (n - m) = (IZR n - IZR m)%R.
Proof.
intros.
unfold Zminus.
rewrite plus_IZR.
rewrite Ropp_Ropp_IZR.
apply refl_equal.
Qed.

Theorem minus_Z2R :
  forall m n, (Z2R (m - n) = Z2R m - Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply minus_IZR.
Qed.

Theorem mult_Z2R :
  forall m n, (Z2R (m * n) = Z2R m * Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply mult_IZR.
Qed.

Theorem le_Z2R :
  forall m n, (Z2R m <= Z2R n)%R -> (m <= n)%Z.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply le_IZR.
Qed.

Theorem Z2R_le :
  forall m n, (m <= n)%Z -> (Z2R m <= Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_le.
Qed.

Theorem lt_Z2R :
  forall m n, (Z2R m < Z2R n)%R -> (m < n)%Z.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply lt_IZR.
Qed.

Theorem Z2R_lt :
  forall m n, (m < n)%Z -> (Z2R m < Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_lt.
Qed.

Theorem Z2R_le_lt :
  forall m n p, (m <= n < p)%Z -> (Z2R m <= Z2R n < Z2R p)%R.
Proof.
intros m n p (H1, H2).
split.
now apply Z2R_le.
now apply Z2R_lt.
Qed.

Theorem le_lt_Z2R :
  forall m n p, (Z2R m <= Z2R n < Z2R p)%R -> (m <= n < p)%Z.
Proof.
intros m n p (H1, H2).
split.
now apply le_Z2R.
now apply lt_Z2R.
Qed.

Theorem eq_Z2R :
  forall m n, (Z2R m = Z2R n)%R -> (m = n)%Z.
Proof.
intros m n H.
apply eq_IZR.
now rewrite <- 2!Z2R_IZR.
Qed.

Theorem neq_Z2R :
  forall m n, (Z2R m <> Z2R n)%R -> (m <> n)%Z.
Proof.
intros m n H H'.
apply H.
now apply f_equal.
Qed.

Theorem Z2R_neq :
  forall m n, (m <> n)%Z -> (Z2R m <> Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_neq.
Qed.

Theorem abs_Z2R :
  forall z, Z2R (Zabs z) = Rabs (Z2R z).
Proof.
intros.
repeat rewrite Z2R_IZR.
now rewrite Rabs_Zabs.
Qed.

End Z2R.

Section Floor_Ceil.

Definition Zfloor (x : R) := (up x - 1)%Z.

Theorem Zfloor_lb :
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

Theorem Zfloor_ub :
  forall x : R,
  (x < Z2R (Zfloor x) + 1)%R.
Proof.
intros x.
unfold Zfloor.
rewrite minus_Z2R.
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_r.
rewrite Z2R_IZR.
exact (proj1 (archimed x)).
Qed.

Theorem Zfloor_lub :
  forall n x,
  (Z2R n <= x)%R ->
  (n <= Zfloor x)%Z.
Proof.
intros n x Hnx.
apply Zlt_succ_le.
apply lt_Z2R.
apply Rle_lt_trans with (1 := Hnx).
unfold Zsucc.
rewrite plus_Z2R.
apply Zfloor_ub.
Qed.

Theorem Zfloor_imp :
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

Definition Zceil (x : R) := (- Zfloor (- x))%Z.

Theorem Zceil_ub :
  forall x : R,
  (x <= Z2R (Zceil x))%R.
Proof.
intros x.
unfold Zceil.
rewrite opp_Z2R.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Zfloor_lb.
Qed.

Theorem Zceil_lub :
  forall n x,
  (x <= Z2R n)%R ->
  (Zceil x <= n)%Z.
Proof.
intros n x Hnx.
unfold Zceil.
apply Zopp_le_cancel.
rewrite Zopp_involutive.
apply Zfloor_lub.
rewrite opp_Z2R.
now apply Ropp_le_contravar.
Qed.

Theorem Zceil_imp :
  forall n x,
  (Z2R (n - 1) < x <= Z2R n)%R ->
  Zceil x = n.
Proof.
intros n x Hnx.
unfold Zceil.
rewrite <- (Zopp_involutive n).
apply f_equal.
apply Zfloor_imp.
split.
rewrite opp_Z2R.
now apply Ropp_le_contravar.
rewrite <- (Zopp_involutive 1).
rewrite <- Zopp_plus_distr.
rewrite opp_Z2R.
now apply Ropp_lt_contravar.
Qed.

Theorem Zceil_floor_neq :
  forall x : R,
  (Z2R (Zfloor x) <> x)%R ->
  (Zceil x = Zfloor x + 1)%Z.
Proof.
intros x Hx.
apply Zceil_imp.
split.
ring_simplify (Zfloor x + 1 - 1)%Z.
apply Rnot_le_lt.
intros H.
apply Hx.
apply Rle_antisym.
apply Zfloor_lb.
exact H.
apply Rlt_le.
rewrite plus_Z2R.
apply Zfloor_ub.
Qed.

End Floor_Ceil.

Section pow.

Record radix :=  { radix_val : Z ; radix_prop :  (2 <= radix_val )%Z }.

Variable r: radix.

Theorem radix_pos: (0 < Z2R (radix_val r))%R.
Proof.
destruct r; simpl.
apply Rle_lt_trans with (Z2R 0).
right; reflexivity.
apply Z2R_lt; auto with zarith.
Qed.

Definition bpow e :=
  match e with
  | Zpos p => Z2R (Zpower_pos (radix_val r) p)
  | Zneg p => Rinv (Z2R (Zpower_pos (radix_val r) p))
  | Z0 => R1
  end.

Theorem Zpower_pos_powerRZ :
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

Theorem bpow_powerRZ :
  forall e,
  bpow e = powerRZ (Z2R (radix_val r)) e.
Proof.
destruct e ; unfold bpow.
reflexivity.
now rewrite Zpower_pos_powerRZ.
now rewrite Zpower_pos_powerRZ.
Qed.

Theorem  bpow_ge_0 :
  forall e : Z, (0 <= bpow e)%R.
Proof.
intros.
rewrite bpow_powerRZ.
apply powerRZ_le.
change R0 with (Z2R 0).
apply Z2R_lt.
destruct r; simpl; auto with zarith.
Qed.

Theorem bpow_gt_0 :
  forall e : Z, (0 < bpow e)%R.
Proof.
intros.
rewrite bpow_powerRZ.
apply powerRZ_lt.
change R0 with (Z2R 0).
apply Z2R_lt.
destruct r; simpl; auto with zarith.
Qed.

Theorem bpow_add :
  forall e1 e2 : Z, (bpow (e1 + e2) = bpow e1 * bpow e2)%R.
Proof.
intros.
repeat rewrite bpow_powerRZ.
apply powerRZ_add.
change R0 with (Z2R 0).
apply Z2R_neq.
destruct r; simpl; auto with zarith.
Qed.

Theorem bpow_1 :
  bpow 1 = Z2R (radix_val r).
Proof.
unfold bpow, Zpower_pos, iter_pos.
now rewrite Zmult_1_r.
Qed.

Theorem bpow_add1 :
  forall e : Z, (bpow (e+1) = Z2R (radix_val r) * bpow e)%R.
Proof.
intros.
rewrite <- bpow_1.
rewrite <- bpow_add.
now rewrite Zplus_comm.
Qed.

Theorem bpow_opp :
  forall e : Z, (bpow (-e) = /bpow e)%R.
Proof.
intros e; destruct e.
simpl; now rewrite Rinv_1.
now replace (-Zpos p)%Z with (Zneg p) by reflexivity.
replace (-Zneg p)%Z with (Zpos p) by reflexivity.
simpl; rewrite Rinv_involutive; trivial.
generalize (bpow_gt_0 (Zpos p)).
simpl; auto with real.
Qed.

Theorem Z2R_Zpower :
  forall e : Z,
  (0 <= e)%Z ->
  Z2R (Zpower (radix_val r) e) = bpow e.
Proof.
intros [|e|e] H.
split.
split.
now elim H.
Qed.

Theorem bpow_lt_aux :
  forall e1 e2 : Z,
  (e1 < e2)%Z -> (bpow e1 < bpow e2)%R.
Proof.
intros e1 e2 H.
replace e2 with (e1 + (e2 - e1))%Z by ring.
rewrite <- (Rmult_1_r (bpow e1)).
rewrite bpow_add.
apply Rmult_lt_compat_l.
apply bpow_gt_0.
assert (0 < e2 - e1)%Z by omega.
destruct (e2 - e1)%Z ; try discriminate H0.
clear.
unfold bpow.
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

Theorem bpow_lt :
  forall e1 e2 : Z,
  (e1 < e2)%Z <-> (bpow e1 < bpow e2)%R.
Proof.
intros e1 e2.
split.
apply bpow_lt_aux.
intros H.
apply Zgt_lt.
apply Znot_le_gt.
intros H'.
apply Rlt_not_le with (1 := H).
destruct (Zle_lt_or_eq _ _ H').
apply Rlt_le.
now apply bpow_lt_aux.
apply Req_le.
now apply f_equal.
Qed.

Theorem bpow_le :
  forall e1 e2 : Z,
  (e1 <= e2)%Z <-> (bpow e1 <= bpow e2)%R.
Proof.
intros e1 e2.
split.
intros H.
apply Rnot_lt_le.
intros H'.
apply Zle_not_gt with (1 := H).
apply Zlt_gt.
now apply <- bpow_lt.
intros H.
apply Znot_gt_le.
intros H'.
apply Rle_not_lt with (1 := H).
apply -> bpow_lt.
now apply Zgt_lt.
Qed.

Theorem bpow_eq :
  forall e1 e2 : Z,
  e1 = e2 -> bpow e1 = bpow e2.
Proof.
intros.
apply Rle_antisym.
apply -> bpow_le.
now apply Zeq_le.
apply -> bpow_le.
apply Zeq_le.
now apply sym_eq.
Qed.

Theorem bpow_exp :
  forall e : Z,
  bpow e = exp (Z2R e * ln (Z2R (radix_val r))).
Proof.
(* positive case *)
assert (forall e, bpow (Zpos e) = exp (Z2R (Zpos e) * ln (Z2R (radix_val r)))).
intros e.
unfold bpow.
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
unfold bpow.
change (Z2R (Zpower_pos (radix_val r) e)) with (bpow (Zpos e)).
rewrite H.
rewrite <- exp_Ropp.
rewrite <- Ropp_mult_distr_l_reverse.
now rewrite <- opp_Z2R.
Qed.

Theorem ln_beta :
  forall x : R,
  {e | (x <> 0)%R -> (bpow (e - 1)%Z <= Rabs x < bpow e)%R}.
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
now apply Zlt_le_trans with (2 := radix_prop r).
apply (Z2R_lt 0).
now apply Zlt_le_trans with (2 := radix_prop r).
(* . *)
exists (Zfloor (ln (Rabs x) / fact) + 1)%Z.
intros Hx'.
generalize (Rabs_pos_lt _ Hx'). clear Hx'.
generalize (Rabs x). clear x.
intros x Hx.
rewrite 2!bpow_exp.
fold fact.
pattern x at 2 3 ; replace x with (exp (ln x * / fact * fact)).
split.
rewrite minus_Z2R.
apply exp_increasing_weak.
apply Rmult_le_compat_r.
now apply Rlt_le.
unfold Rminus.
rewrite plus_Z2R.
rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
apply Zfloor_lb.
apply exp_increasing.
apply Rmult_lt_compat_r.
exact H.
rewrite plus_Z2R.
apply Zfloor_ub.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
now apply exp_ln.
now apply Rgt_not_eq.
Qed.

Theorem bpow_lt_bpow :
  forall e1 e2,
  (bpow (e1 - 1) < bpow e2)%R ->
  (e1 <= e2)%Z.
Proof.
intros e1 e2 He.
rewrite (Zsucc_pred e1).
apply Zlt_le_succ.
now apply <- bpow_lt.
Qed.

Theorem bpow_unique :
  forall x e1 e2,
  (bpow (e1 - 1) <= x < bpow e1)%R ->
  (bpow (e2 - 1) <= x < bpow e2)%R ->
  e1 = e2.
Proof.
intros x e1 e2 (H1a,H1b) (H2a,H2b).
apply Zle_antisym ;
  apply bpow_lt_bpow ;
  apply Rle_lt_trans with x ;
  assumption.
Qed.

Theorem ln_beta_unique :
  forall (x : R) (e : Z),
  (bpow (e - 1) <= Rabs x < bpow e)%R ->
  projT1 (ln_beta x) = e.
Proof.
intros x e1 He.
destruct (Req_dec x 0) as [Hx|Hx].
elim Rle_not_lt with (1 := proj1 He).
rewrite Hx, Rabs_R0.
apply bpow_gt_0.
destruct (ln_beta x) as (e2, Hx2).
simpl.
apply bpow_unique with (2 := He).
now apply Hx2.
Qed.

Theorem ln_beta_opp :
  forall x,
  projT1 (ln_beta (-x)) = projT1 (ln_beta x).
Proof.
intros x.
destruct (Req_dec x 0) as [Hx|Hx].
now rewrite Hx, Ropp_0.
destruct (ln_beta x) as (e, He).
simpl.
specialize (He Hx).
apply ln_beta_unique.
now rewrite Rabs_Ropp.
Qed.

Theorem ln_beta_monotone :
  forall x y,
  (0 < x)%R -> (x <= y)%R ->
  (projT1 (ln_beta x) <= projT1 (ln_beta y))%Z.
Proof.
intros x y H0x Hxy.
destruct (ln_beta x) as (ex, Hx).
destruct (ln_beta y) as (ey, Hy).
simpl.
apply bpow_lt_bpow.
specialize (Hx (Rgt_not_eq _ _ H0x)).
specialize (Hy (Rgt_not_eq _ _ (Rlt_le_trans _ _ _ H0x Hxy))).
apply Rle_lt_trans with (1 := proj1 Hx).
apply Rle_lt_trans with (2 := proj2 Hy).
rewrite 2!Rabs_pos_eq.
exact Hxy.
apply Rle_trans with (2 := Hxy).
now apply Rlt_le.
now apply Rlt_le.
Qed.

Theorem Zpower_pos_gt_0 :
  forall b p, (0 < b)%Z ->
  (0 < Zpower_pos b p)%Z.
Proof.
intros b p Hb.
apply lt_Z2R.
rewrite Zpower_pos_powerRZ.
apply powerRZ_lt.
now apply (Z2R_lt 0).
Qed.

Theorem Zpower_gt_0 :
  forall b p,
  (0 < b)%Z -> (0 <= p)%Z ->
  (0 < Zpower b p)%Z.
Proof.
intros b p Hb Hz.
unfold Zpower.
destruct p.
easy.
now apply Zpower_pos_gt_0.
now elim Hz.
Qed.

Theorem Zpower_gt_1 :
  forall p,
  (0 < p)%Z ->
  (1 < Zpower (radix_val r) p)%Z.
Proof.
intros.
apply lt_Z2R.
rewrite Z2R_Zpower.
now apply -> (bpow_lt 0).
now apply Zlt_le_weak.
Qed.

Theorem Zln_beta :
  forall x : Z,
  {e | (Zpower (radix_val r) (e - 1) <= Zabs x < Zpower (radix_val r) e)%Z}.
Proof.
intros x.
destruct (Z_eq_dec x 0) as [Hx|Hx].
(* . *)
exists Z0.
rewrite Hx.
now split.
(* . *)
destruct (ln_beta (Z2R x)) as (e, H).
specialize (H (Z2R_neq _ _ Hx)).
exists e.
assert (He: (1 <= e)%Z).
apply (Zlt_le_succ 0).
apply <- bpow_lt.
apply Rle_lt_trans with (2 := proj2 H).
rewrite <- abs_Z2R.
apply (Z2R_le 1).
apply (Zlt_le_succ 0).
generalize (Zabs_spec x).
omega.
(* . . *)
split.
apply le_Z2R.
rewrite Z2R_Zpower, abs_Z2R.
apply H.
now apply Zle_minus_le_0.
apply lt_Z2R.
rewrite Z2R_Zpower, abs_Z2R.
apply H.
now apply Zle_succ_le.
Qed.

End pow.

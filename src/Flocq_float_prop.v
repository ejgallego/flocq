Require Import Flocq_Raux.
Require Import Flocq_defs.

Section Float_prop.

Variable beta : radix.

Notation bpow e := (epow beta e).

Theorem F2R_ge_0_reg :
  forall m e : Z,
  (0 <= F2R (Float beta m e))%R ->
  (0 <= m)%Z.
Proof.
intros m e H.
apply le_Z2R.
apply Rmult_le_reg_r with (bpow e).
apply epow_gt_0.
now rewrite Rmult_0_l.
Qed.

Theorem F2R_le_0_reg :
  forall m e : Z,
  (F2R (Float beta m e) <= 0)%R ->
  (m <= 0)%Z.
Proof.
intros m e H.
apply le_Z2R.
apply Ropp_le_cancel.
apply Rmult_le_reg_r with (bpow e).
apply epow_gt_0.
simpl (Z2R 0).
rewrite Ropp_0.
rewrite Rmult_0_l.
rewrite Ropp_mult_distr_l_reverse.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
Qed.

Theorem F2R_gt_0_reg :
  forall m e : Z,
  (0 < F2R (Float beta m e))%R ->
  (0 < m)%Z.
Proof.
intros m e H.
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow e).
apply epow_gt_0.
now rewrite Rmult_0_l.
Qed.

Theorem F2R_gt_0_compat :
  forall f : float beta,
  (0 < Fnum f)%Z ->
  (0 < F2R f)%R.
Proof.
intros f Hm.
unfold F2R.
apply Rmult_lt_0_compat.
now apply (Z2R_lt 0).
apply epow_gt_0.
Qed.

Theorem F2R_le_reg :
  forall e m1 m2 : Z,
  (F2R (Float beta m1 e) <= F2R (Float beta m2 e))%R ->
  (m1 <= m2)%Z.
Proof.
intros e m1 m2 H.
apply le_Z2R.
apply Rmult_le_reg_r with (bpow e).
apply epow_gt_0.
exact H.
Qed.

Theorem F2R_le_compat :
  forall m1 m2 e : Z,
  (m1 <= m2)%Z ->
  (F2R (Float beta m1 e) <= F2R (Float beta m2 e))%R.
Proof.
intros m1 m2 e H.
unfold F2R. simpl.
apply Rmult_le_compat_r.
apply epow_ge_0.
now apply Z2R_le.
Qed.

Theorem F2R_lt_reg :
  forall e m1 m2 : Z,
  (F2R (Float beta m1 e) < F2R (Float beta m2 e))%R ->
  (m1 < m2)%Z.
Proof.
intros e m1 m2 H.
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow e).
apply epow_gt_0.
exact H.
Qed.

Theorem F2R_lt_compat :
  forall e m1 m2 : Z,
  (m1 < m2)%Z ->
  (F2R (Float beta m1 e) < F2R (Float beta m2 e))%R.
Proof.
intros e m1 m2 H.
unfold F2R. simpl.
apply Rmult_lt_compat_r.
apply epow_gt_0.
now apply Z2R_lt.
Qed.

Theorem epow_le_F2R :
  forall m e : Z,
  (0 < m)%Z ->
  (bpow e <= F2R (Float beta m e))%R.
Proof.
intros m e H.
rewrite <- (Rmult_1_l (bpow e)).
unfold F2R. simpl.
apply Rmult_le_compat_r.
apply epow_ge_0.
apply (Z2R_le 1).
now apply (Zlt_le_succ 0).
Qed.

Theorem F2R_p1_le_epow :
  forall m e1 e2 : Z,
  (0 < m)%Z ->
  (F2R (Float beta m e1) < bpow e2)%R ->
  (F2R (Float beta (m + 1) e1) <= bpow e2)%R.
Proof.
intros m e1 e2 Hm.
intros H.
assert (He : (e1 <= e2)%Z).
(* . *)
apply <- (epow_le beta).
apply Rle_trans with (F2R (Float beta m e1)).
unfold F2R. simpl.
rewrite <- (Rmult_1_l (bpow e1)) at 1.
apply Rmult_le_compat_r.
apply epow_ge_0.
apply (Z2R_le 1).
now apply (Zlt_le_succ 0).
now apply Rlt_le.
(* . *)
revert H.
replace e2 with (e2 - e1 + e1)%Z by ring.
rewrite epow_add.
unfold F2R. simpl.
rewrite <- (Z2R_Zpower beta (e2 - e1)).
intros H.
apply Rmult_le_compat_r.
apply epow_ge_0.
apply Rmult_lt_reg_r in H.
apply Z2R_le.
apply Zlt_le_succ.
now apply lt_Z2R.
apply epow_gt_0.
now apply Zle_minus_le_0.
Qed.

Theorem abs_F2R :
  forall m e : Z,
  Rabs (F2R (Float beta m e)) = F2R (Float beta (Zabs m) e).
Proof.
intros m e.
unfold F2R.
rewrite Rabs_mult.
rewrite Rabs_Z2R.
simpl.
apply f_equal.
apply Rabs_right.
apply Rle_ge.
apply epow_ge_0.
Qed.

Theorem opp_F2R :
  forall m e : Z,
  Ropp (F2R (Float beta m e)) = F2R (Float beta (Zopp m) e).
Proof.
intros m e.
unfold F2R. simpl.
rewrite <- Ropp_mult_distr_l_reverse.
now rewrite opp_Z2R.
Qed.

Theorem F2R_change_exp :
  forall e' m e : Z,
  (e' <= e)%Z ->
  F2R (Float beta m e) = F2R (Float beta (m * Zpower (radix_val beta) (e - e')) e').
Proof.
intros e' m e He.
unfold F2R. simpl.
rewrite mult_Z2R, Z2R_Zpower, Rmult_assoc.
apply f_equal.
pattern e at 1 ; replace e with (e - e' + e')%Z by ring.
apply epow_add.
now apply Zle_minus_le_0.
Qed.

Theorem F2R_prec_normalize :
  forall m e e' p : Z,
  (Zabs m < Zpower (radix_val beta) p)%Z ->
  (bpow (e' - 1)%Z <= Rabs (F2R (Float beta m e)))%R ->
  F2R (Float beta m e) = F2R (Float beta (m * Zpower (radix_val beta) (e - e' + p)) (e' - p)).
Proof.
intros m e e' p Hm Hf.
assert (Hp: (0 <= p)%Z).
destruct p ; try easy.
now elim (Zle_not_lt _ _ (Zabs_pos m)).
(* . *)
replace (e - e' + p)%Z with (e - (e' - p))%Z by ring.
apply F2R_change_exp.
cut (e' - 1 < e + p)%Z. omega.
apply <- epow_lt.
apply Rle_lt_trans with (1 := Hf).
rewrite abs_F2R, Zplus_comm, epow_add.
apply Rmult_lt_compat_r.
apply epow_gt_0.
rewrite <- Z2R_Zpower.
now apply Z2R_lt.
exact Hp.
Qed.

Theorem ln_beta_F2R :
  forall m e : Z,
  m <> Z0 ->
  (projT1 (ln_beta beta (F2R (Float beta m e))) = projT1 (ln_beta beta (Z2R m)) + e)%Z.
Proof.
intros m e H.
destruct (ln_beta beta (Z2R m)) as (d, Hd).
simpl.
specialize (Hd (Z2R_neq _ _ H)).
apply ln_beta_unique.
rewrite abs_F2R.
unfold F2R. simpl.
rewrite Rabs_Z2R in Hd.
split.
replace (d + e - 1)%Z with (d - 1 + e)%Z by ring.
rewrite epow_add.
apply Rmult_le_compat_r.
apply epow_ge_0.
apply Hd.
rewrite epow_add.
apply Rmult_lt_compat_r.
apply epow_gt_0.
apply Hd.
Qed.

Theorem float_distribution_pos :
  forall m1 e1 m2 e2 : Z,
  (0 < m1)%Z ->
  (F2R (Float beta m1 e1) < F2R (Float beta m2 e2) < F2R (Float beta (m1 + 1) e1))%R ->
  (e2 < e1)%Z /\ (e1 + projT1 (ln_beta beta (Z2R m1)) = e2 + projT1 (ln_beta beta (Z2R m2)))%Z.
Proof.
intros m1 e1 m2 e2 Hp1 (H12, H21).
assert (He: (e2 < e1)%Z).
(* . *)
apply Znot_ge_lt.
intros H0.
elim Rlt_not_le with (1 := H21).
apply Zge_le in H0.
apply (F2R_change_exp e1 m2 e2) in H0.
rewrite H0.
apply F2R_le_compat.
apply Zlt_le_succ.
apply (F2R_lt_reg e1).
now rewrite <- H0.
(* . *)
split.
exact He.
rewrite (Zplus_comm e1), (Zplus_comm e2).
assert (Hp2: (0 < m2)%Z).
apply (F2R_gt_0_reg m2 e2).
apply Rlt_trans with (2 := H12).
now apply F2R_gt_0_compat.
rewrite <- 2!ln_beta_F2R.
destruct (ln_beta beta (F2R (Float beta m1 e1))) as (e1', H1).
simpl.
apply sym_eq.
apply ln_beta_unique.
assert (H2 : (bpow (e1' - 1) <= F2R (Float beta m1 e1) < bpow e1')%R).
rewrite <- (Zabs_eq m1), <- abs_F2R.
apply H1.
apply Rgt_not_eq.
apply Rlt_gt.
unfold F2R. simpl.
apply Rmult_lt_0_compat.
now apply (Z2R_lt 0).
apply epow_gt_0.
now apply Zlt_le_weak.
clear H1.
rewrite abs_F2R, Zabs_eq.
split.
apply Rlt_le.
apply Rle_lt_trans with (2 := H12).
apply H2.
apply Rlt_le_trans with (1 := H21).
now apply F2R_p1_le_epow.
now apply Zlt_le_weak.
apply sym_not_eq.
now apply Zlt_not_eq.
apply sym_not_eq.
now apply Zlt_not_eq.
Qed.

End Float_prop.

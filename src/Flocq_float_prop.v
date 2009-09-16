Require Import Flocq_Raux.
Require Import Flocq_defs.

Section Float_prop.

Variable beta : radix.

Notation bpow := (epow beta).

Theorem F2R_ge_0_imp_Fnum :
  forall f : float beta,
  (0 <= F2R f)%R ->
  (0 <= Fnum f)%Z.
Proof.
intros f H.
apply le_Z2R.
apply Rmult_le_reg_l with (bpow (Fexp f)).
apply epow_gt_0.
rewrite Rmult_0_r.
now rewrite Rmult_comm.
Qed.

Theorem F2R_le_0_imp_Fnum :
  forall f : float beta,
  (F2R f <= 0)%R ->
  (Fnum f <= 0)%Z.
Proof.
intros f H.
apply le_Z2R.
apply Ropp_le_cancel.
apply Rmult_le_reg_l with (bpow (Fexp f)).
apply epow_gt_0.
simpl (Z2R 0).
rewrite Ropp_0.
rewrite Rmult_0_r.
rewrite Ropp_mult_distr_r_reverse.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now rewrite Rmult_comm.
Qed.

Theorem F2R_gt_0_imp_Fnum :
  forall f : float beta,
  (0 < F2R f)%R ->
  (0 < Fnum f)%Z.
Proof.
intros f H.
apply lt_Z2R.
apply Rmult_lt_reg_l with (bpow (Fexp f)).
apply epow_gt_0.
rewrite Rmult_0_r.
now rewrite Rmult_comm.
Qed.

Theorem epow_le_F2R :
  forall f : float beta,
  (0 < F2R f)%R ->
  (bpow (Fexp f) <= F2R f)%R.
Proof.
intros f H.
rewrite <- (Rmult_1_l (bpow (Fexp f))).
unfold F2R. simpl.
apply Rmult_le_compat_r.
apply epow_ge_0.
apply (Z2R_le 1).
apply (Zlt_le_succ 0).
now apply F2R_gt_0_imp_Fnum.
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

End Float_prop.

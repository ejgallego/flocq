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

Theorem F2R_prec_normalize_pos :
  forall m e e' p : Z,
  (Zabs m < Zpower (radix_val beta) p)%Z ->
  (bpow e' <= F2R (Float beta m e))%R ->
  exists m' : Z,
  F2R (Float beta m e) = F2R (Float beta m' (e' - (p - 1))).
Proof.
intros m e e' p Hm Hf.
exists (m * Zpower (radix_val beta) (e - (e' - (p - 1))))%Z.
unfold F2R.
simpl.
rewrite mult_Z2R.
rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
rewrite Z2R_Zpower.
rewrite <- epow_add.
apply f_equal.
ring.
assert (e' <= e + (p - 1))%Z.
2: omega.
apply Zlt_succ_le.
unfold Zsucc.
replace (e + (p - 1) + 1)%Z with (e + p)%Z by ring.
apply <- epow_lt.
apply Rle_lt_trans with (1 := Hf).
unfold F2R.
rewrite epow_add.
rewrite Rmult_comm.
apply Rmult_lt_compat_l.
apply epow_gt_0.
simpl.
apply Rle_lt_trans with (1 := RRle_abs _).
rewrite Z2R_IZR.
rewrite Rabs_Zabs.
rewrite <- Z2R_IZR.
replace (bpow p) with (Z2R (Zpower (radix_val beta) p)).
now apply Z2R_lt.
rewrite Z2R_Zpower.
apply refl_equal.
clear -Hm.
destruct p as [_|p|p] ; try discriminate.
simpl in Hm.
elim Zlt_not_le with (1 := Hm).
apply Zabs_pos.
Qed.

Theorem F2R_prec_normalize :
  forall m e e' p : Z,
  (Zabs m < Zpower (radix_val beta) p)%Z ->
  (bpow e' <= Rabs (F2R (Float beta m e)))%R ->
  exists m' : Z,
  F2R (Float beta m e) = F2R (Float beta m' (e' - (p - 1))).
Proof.
intros [|m|m] e e' p Hm Hf.
exists Z0.
unfold F2R. simpl.
now rewrite 2!Rmult_0_l.
(* . *)
apply F2R_prec_normalize_pos.
exact Hm.
now rewrite abs_F2R in Hf.
(* . *)
destruct (F2R_prec_normalize_pos (Zpos m) e e' p) as (m', Hm').
exact Hm.
now rewrite abs_F2R in Hf.
exists (Zopp m').
rewrite <- opp_F2R.
rewrite <- Hm'.
unfold F2R. simpl.
apply Ropp_mult_distr_l_reverse.
Qed.

End Float_prop.
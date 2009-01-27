Require Import Flocq_Raux.
Require Import Flocq_defs.

Section Float_prop.

Open Scope R_scope.

Variable beta : radix.

Notation bpow := (epow beta).

Lemma F2R_ge_0_imp_Fnum :
  forall f : float beta,
  0 <= F2R f ->
  (0 <= Fnum f)%Z.
Proof.
intros f H.
apply le_Z2R.
apply Rmult_le_reg_l with (bpow (Fexp f)).
apply epow_gt_0.
rewrite Rmult_0_r.
now rewrite Rmult_comm.
Qed.

Lemma F2R_le_0_imp_Fnum :
  forall f : float beta,
  F2R f <= 0 ->
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

Lemma F2R_prec_normalize :
  forall m e e' p : Z,
  (Zabs m < Zpower (radix_val beta) p)%Z ->
  bpow e' <= F2R (Float beta m e) ->
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

End Float_prop.
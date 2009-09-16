Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_generic.
Require Import Flocq_float_prop.
Require Import Flocq_rnd_FLX.

Section RND_FTZ.

Variable beta : radix.

Notation bpow e := (epow beta e).

Variable emin prec : Z.
Variable Hp : Zlt 0 prec.

(* floating-point format with abrupt underflow *)
Definition FTZ_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Fnum f <> 0 -> Zpower (radix_val beta) (prec - 1) <= Zabs (Fnum f) < Zpower (radix_val beta) prec)%Z /\
  (emin <= Fexp f)%Z.

Definition FTZ_RoundingModeP (rnd : R -> R):=
  Rounding_for_Format FTZ_format rnd.

Definition FTZ_exp e := if Zlt_bool (e - prec) emin then (emin + prec - 1)%Z else (e - prec)%Z.

Theorem FTZ_exp_correct : valid_exp FTZ_exp.
Proof.
intros k.
unfold FTZ_exp.
generalize (Zlt_cases (k - prec) emin).
case (Zlt_bool (k - prec) emin) ; intros H1.
split ; intros H2.
omega.
split.
generalize (Zlt_cases (emin + prec + 1 - prec) emin).
case (Zlt_bool (emin + prec + 1 - prec) emin) ; intros H3.
omega.
generalize (Zlt_cases (emin + prec - 1 + 1 - prec) emin).
case (Zlt_bool (emin + prec - 1 + 1 - prec) emin) ; omega.
intros l H3.
generalize (Zlt_cases (l - prec) emin).
case (Zlt_bool (l - prec) emin) ; omega.
split ; intros H2.
generalize (Zlt_cases (k + 1 - prec) emin).
case (Zlt_bool (k + 1 - prec) emin) ; omega.
split ; intros ; omega.
Qed.

Theorem FTZ_format_generic :
  forall x : R, generic_format beta FTZ_exp x <-> FTZ_format x.
Proof.
split.
(* . *)
intros ((xm, xe), (Hx1, Hx2)).
destruct (Req_dec x 0) as [Hx3|Hx3].
exists (Float beta 0 emin).
split.
unfold F2R. simpl.
now rewrite Rmult_0_l.
split.
intros H.
now elim H.
apply Zle_refl.
destruct (ln_beta beta (Rabs x)) as (ex, Hx4).
simpl in Hx2.
specialize (Hx4 (Rabs_pos_lt x Hx3)).
unfold FTZ_exp in Hx2.
generalize (Zlt_cases (ex - prec) emin) Hx2. clear Hx2.
case (Zlt_bool (ex - prec) emin) ; intros Hx5 Hx2.
elim Rlt_not_ge with (1 := proj2 Hx4).
apply Rle_ge.
rewrite Hx1, abs_F2R.
rewrite <- (Rmult_1_l (bpow ex)).
unfold F2R. simpl.
apply Rmult_le_compat.
now apply (Z2R_le 0 1).
apply epow_ge_0.
apply (Z2R_le 1).
apply (Zlt_le_succ 0).
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow xe).
apply epow_gt_0.
rewrite Rmult_0_l.
change (0 < F2R (Float beta (Zabs xm) xe))%R.
rewrite <- abs_F2R, <- Hx1.
now apply Rabs_pos_lt.
apply -> epow_le.
omega.
exists (Float beta xm xe).
split.
exact Hx1.
split.
intros _.
split.
apply le_Z2R.
rewrite Z2R_Zpower.
apply Rmult_le_reg_r with (bpow (ex - prec)).
apply epow_gt_0.
rewrite <- epow_add.
replace (prec - 1 + (ex - prec))%Z with (ex - 1)%Z by ring.
rewrite <- Hx2.
change (bpow (ex - 1) <= F2R (Float beta (Zabs xm) xe))%R.
rewrite <- abs_F2R, <- Hx1.
apply Hx4.
apply Zle_minus_le_0.
now apply (Zlt_le_succ 0).
apply lt_Z2R.
rewrite Z2R_Zpower.
apply Rmult_lt_reg_r with (bpow (ex - prec)).
apply epow_gt_0.
rewrite <- epow_add.
replace (prec + (ex - prec))%Z with ex by ring.
rewrite <- Hx2.
change (F2R (Float beta (Zabs xm) xe) < bpow ex)%R.
rewrite <- abs_F2R, <- Hx1.
apply Hx4.
now apply Zlt_le_weak.
simpl.
rewrite Hx2.
now apply Zge_le.
(* . *)
intros ((xm, xe), (Hx1, (Hx2, Hx3))).
destruct (Req_dec x 0) as [Hx4|Hx4].
exists (Float beta 0 (FTZ_exp (projT1 (ln_beta beta (Rabs x))))).
repeat split.
unfold F2R. simpl.
now rewrite Hx4, Rmult_0_l.
assert (Hx5: xm <> Z0).
intros H.
apply Hx4.
rewrite Hx1, H.
apply Rmult_0_l.
specialize (Hx2 Hx5).
unfold generic_format, canonic, FTZ_exp.
destruct (ln_beta beta (Rabs x)) as (ex, Hx6).
simpl.
specialize (Hx6 (Rabs_pos_lt _ Hx4)).
generalize (Zlt_cases (ex - prec) emin).
case (Zlt_bool (ex - prec) emin) ; intros H1.
elim (Rlt_not_ge _ _ (proj2 Hx6)).
apply Rle_ge.
rewrite Hx1.
apply Rle_trans with (bpow (prec - 1) * bpow emin)%R.
rewrite <- epow_add.
apply -> epow_le.
omega.
rewrite abs_F2R.
unfold F2R. simpl.
apply Rmult_le_compat.
apply epow_ge_0.
apply epow_ge_0.
rewrite <- Z2R_Zpower.
now apply Z2R_le.
apply Zle_minus_le_0.
now apply (Zlt_le_succ 0).
now apply -> epow_le.
rewrite Hx1, (F2R_prec_normalize beta xm xe ex prec (proj2 Hx2)).
now eexists.
now rewrite <- Hx1.
Qed.

End RND_FTZ.
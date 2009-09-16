Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_generic.
Require Import Flocq_float_prop.

Section RND_FLX.

Variable beta : radix.

Notation bpow e := (epow beta e).

Variable prec : Z.
Variable Hp : Zlt 0 prec.

(* unbounded floating-point format *)
Definition FLX_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Zabs (Fnum f) < Zpower (radix_val beta) prec)%Z.

Definition FLX_RoundingModeP (rnd : R -> R):=
  Rounding_for_Format FLX_format rnd.

Definition FLX_exp (e : Z) := (e - prec)%Z.

Theorem FLX_exp_correct : valid_exp FLX_exp.
Proof.
intros k.
unfold FLX_exp.
repeat split ; intros ; omega.
Qed.

Theorem FLX_format_generic :
  forall x : R, generic_format beta FLX_exp x <-> FLX_format x.
Proof.
split.
(* . *)
intros ((xm, xe), (Hx1, Hx2)).
destruct (Req_dec x 0) as [Hx3|Hx3].
exists (Float beta 0 0).
split.
unfold F2R. simpl.
now rewrite Rmult_0_l.
simpl.
apply Zpower_gt_0.
now apply Zlt_le_trans with (2 := radix_prop beta).
now apply Zlt_le_weak.
rewrite Hx1.
eexists ; repeat split.
simpl.
destruct (ln_beta beta (Rabs x)) as (ex, Hx4).
simpl in Hx2.
specialize (Hx4 (Rabs_pos_lt x Hx3)).
apply lt_Z2R.
rewrite Z2R_Zpower.
apply Rmult_lt_reg_r with (bpow (ex - prec)).
apply epow_gt_0.
rewrite <- epow_add.
replace (prec + (ex - prec))%Z with ex by ring.
change (ex - prec)%Z with (FLX_exp ex).
rewrite <- Hx2.
replace (Z2R (Zabs xm) * bpow xe)%R with (Rabs x).
exact (proj2 Hx4).
rewrite Hx1.
apply abs_F2R.
now apply Zlt_le_weak.
(* . *)
intros ((xm, xe), (Hx1, Hx2)).
destruct (Req_dec x 0) as [Hx3|Hx3].
rewrite Hx3.
exists (Float beta 0 _) ; repeat split.
unfold F2R. simpl.
now rewrite Rmult_0_l.
simpl in Hx2.
unfold generic_format, canonic.
destruct (ln_beta beta (Rabs x)) as (ex, Hx4).
simpl.
specialize (Hx4 (Rabs_pos_lt _ Hx3)).
rewrite Hx1, (F2R_prec_normalize beta xm xe ex prec Hx2).
now eexists.
now rewrite <- Hx1.
Qed.

Theorem FLX_format_satisfies_any :
  satisfies_any FLX_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLX_exp _)).
exact FLX_format_generic.
exact FLX_exp_correct.
Qed.

(* unbounded floating-point format with normal mantissas *)
Definition FLXN_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Fnum f <> 0 ->
  Zpower (radix_val beta) (prec - 1) <= Zabs (Fnum f) < Zpower (radix_val beta) prec)%Z.

Definition FLXN_RoundingModeP (rnd : R -> R):=
  Rounding_for_Format FLXN_format rnd.

Theorem FLX_format_FLXN :
  forall x : R, FLX_format x <-> FLXN_format x.
Proof.
intros x.
split.
(* . *)
intros ((xm, xe), (H1, H2)).
destruct (Z_eq_dec xm 0) as [H3|H3].
exists (Float beta 0 0).
split.
rewrite H1, H3.
unfold F2R. simpl.
now rewrite 2!Rmult_0_l.
intros H.
now elim H.
destruct (ln_beta beta (Z2R (Zabs xm))) as (d,H4).
assert (H5: (0 < Z2R (Zabs xm))%R).
rewrite <- Rabs_Z2R.
apply Rabs_pos_lt.
now apply (Z2R_neq _ 0).
specialize (H4 H5). clear H5.
assert (H5: (0 <= prec - d)%Z).
cut (d - 1 < prec)%Z. omega.
apply <- (epow_lt beta).
apply Rle_lt_trans with (Z2R (Zabs xm)).
apply H4.
rewrite <- Z2R_Zpower.
now apply Z2R_lt.
now apply Zlt_le_weak.
eexists (Float beta (xm * Zpower (radix_val beta) (prec - d)) (xe + d - prec)).
split.
unfold F2R. simpl.
rewrite mult_Z2R, Z2R_Zpower.
rewrite Rmult_assoc, <- epow_add.
rewrite H1.
now ring_simplify (prec - d + (xe + d - prec))%Z.
exact H5.
intros _. simpl.
split.
apply le_Z2R.
apply Rmult_le_reg_r with (bpow (d - prec)).
apply epow_gt_0.
rewrite <- Rabs_Z2R, mult_Z2R, Rabs_mult, 2!Z2R_Zpower.
rewrite <- epow_add.
rewrite Rabs_Z2R.
rewrite Rabs_pos_eq.
rewrite Rmult_assoc, <- epow_add.
ring_simplify (prec - 1 + (d - prec))%Z.
ring_simplify (prec - d + (d - prec))%Z.
now rewrite Rmult_1_r.
apply epow_ge_0.
exact H5.
omega.
apply lt_Z2R.
rewrite <- Rabs_Z2R, mult_Z2R, Rabs_mult.
rewrite 2!Z2R_Zpower.
rewrite Rabs_Z2R, Rabs_pos_eq.
apply Rmult_lt_reg_r with (bpow (d - prec)).
apply epow_gt_0.
rewrite Rmult_assoc, <- 2!epow_add.
ring_simplify (prec + (d - prec))%Z.
ring_simplify (prec - d + (d - prec))%Z.
now rewrite Rmult_1_r.
apply epow_ge_0.
now apply Zlt_le_weak.
exact H5.
(* . *)
intros ((xm, xe), (H1, H2)).
destruct (Z_eq_dec xm 0) as [H3|H3].
exists (Float beta 0 0).
split.
rewrite H1, H3.
unfold F2R.
now rewrite 2!Rmult_0_l.
apply Zpower_gt_0.
generalize (radix_prop beta). omega.
now apply Zlt_le_weak.
specialize (H2 H3). clear H3.
rewrite H1.
eexists ; repeat split.
apply H2.
Qed.

Theorem FLXN_format_satisfies_any :
  satisfies_any FLXN_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLX_exp _)).
split ; intros H.
apply -> FLX_format_FLXN.
now apply -> FLX_format_generic.
apply <- FLX_format_generic.
now apply <- FLX_format_FLXN.
exact FLX_exp_correct.
Qed.

End RND_FLX.

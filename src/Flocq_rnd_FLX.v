Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_generic.
Require Import Flocq_float_prop.

Section RND_FIX.

Variable beta : radix.

Notation bpow := (epow beta).

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
exact Hp.
specialize (Hx2 Hx3).
exists (Float beta xm xe).
split.
exact Hx1.
simpl.
destruct (ln_beta beta (Rabs x) (Rabs_pos_lt x Hx3)) as (ex, Hx4).
simpl in Hx2.
apply lt_Z2R.
rewrite Z2R_Zpower.
apply Rmult_lt_reg_r with (bpow (ex - prec)%Z).
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
exists (Float beta 0 0).
split.
unfold F2R. simpl.
now rewrite Rmult_0_l.
intros H.
now elim H.
destruct (ln_beta beta (Rabs x) (Rabs_pos_lt _ Hx3)) as (ex, Hx4).
simpl in Hx2.
destruct (F2R_prec_normalize beta xm xe (ex - 1) prec Hx2) as (mx, Hx5).
rewrite <- Hx1.
exact (proj1 Hx4).
rewrite Hx1.
replace (ex - 1 - (prec - 1))%Z with (ex - prec)%Z in Hx5 by ring.
rewrite Hx5.
eexists ; repeat split.
intros H.
change (Fexp (Float beta mx (ex - prec))) with (FLX_exp ex).
apply f_equal.
apply sym_eq.
apply ln_beta_unique.
rewrite <- Hx5.
now rewrite <- Hx1.
Qed.

Theorem FLX_format_satisfies_any :
  satisfies_any FLX_format.
Proof.
pose (fexp e := (e - prec)%Z).
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta fexp _)).
exact FLX_format_generic.
exact FLX_exp_correct.
Qed.

End RND_FIX.

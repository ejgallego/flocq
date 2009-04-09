Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_generic.
Require Import Flocq_float_prop.

Section RND_FLT.

Variable beta : radix.

Notation bpow := (epow beta).

Variable emin prec : Z.
Variable Hp : Zlt 0 prec.

(* floating-point format with gradual underflow *)
Definition FLT_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Zabs (Fnum f) < Zpower (radix_val beta) prec)%Z /\ (emin <= Fexp f)%Z.

Definition FLT_RoundingModeP (rnd : R -> R):=
  Rounding_for_Format FLT_format rnd.

Definition FLT_exp e := Zmax (e - prec) emin.

Theorem FLT_exp_correct : valid_exp FLT_exp.
Proof.
intros k.
unfold FLT_exp.
destruct (Zmax_spec (k - prec) emin) as [(H1,H2)|(H1,H2)] ;
  rewrite H2 ; clear H2.
split.
generalize (Zmax_spec (k + 1 - prec) emin).
omega.
intros H0.
apply False_ind.
omega.
split.
generalize (Zmax_spec (k + 1 - prec) emin).
omega.
split.
generalize (Zmax_spec (emin + 1 - prec) emin).
omega.
intros l H0.
generalize (Zmax_spec (l - prec) emin).
omega.
Qed.

Theorem FLT_format_generic :
  forall x : R, generic_format beta FLT_exp x <-> FLT_format x.
Proof.
split.
(* . *)
intros ((xm, xe), (Hx1, Hx2)).
destruct (Req_dec x 0) as [Hx3|Hx3].
exists (Float beta 0 emin).
split.
unfold F2R. simpl.
now rewrite Rmult_0_l.
simpl.
split.
apply Zpower_gt_0.
now apply Zlt_le_trans with (2 := radix_prop beta).
exact Hp.
apply Zle_refl.
specialize (Hx2 Hx3).
exists (Float beta xm xe).
split.
exact Hx1.
simpl.
destruct (ln_beta beta (Rabs x) (Rabs_pos_lt x Hx3)) as (ex, Hx4).
simpl in Hx2.
split.
apply lt_Z2R.
rewrite Z2R_Zpower.
apply Rmult_lt_reg_r with (bpow (ex - prec)%Z).
apply epow_gt_0.
rewrite <- epow_add.
replace (prec + (ex - prec))%Z with ex by ring.
apply Rle_lt_trans with (Z2R (Zabs xm) * bpow xe)%R.
rewrite Hx2.
apply Rmult_le_compat_l.
apply (Z2R_le 0).
apply Zabs_pos.
apply -> epow_le.
apply Zle_max_l.
replace (Z2R (Zabs xm) * bpow xe)%R with (Rabs x).
exact (proj2 Hx4).
rewrite Hx1.
apply abs_F2R.
now apply Zlt_le_weak.
rewrite Hx2.
apply Zle_max_r.
(* . *)
intros ((xm, xe), (Hx1, (Hx2, Hx3))).
destruct (Req_dec x 0) as [Hx4|Hx4].
rewrite Hx4.
exists (Float beta 0 0).
split.
unfold F2R. simpl.
now rewrite Rmult_0_l.
intros H.
now elim H.
destruct (ln_beta beta (Rabs x) (Rabs_pos_lt _ Hx4)) as (ex, Hx5).
simpl in Hx2, Hx3.
assert (Hx6 : x = F2R (Float beta (xm * Zpower (radix_val beta) (xe - FLT_exp ex)) (FLT_exp ex))).
rewrite Hx1.
unfold F2R. simpl.
rewrite mult_Z2R.
rewrite Z2R_Zpower.
rewrite Rmult_assoc.
apply f_equal.
rewrite <- epow_add.
apply f_equal.
ring.
apply Zle_minus_le_0.
unfold FLT_exp.
apply Zmax_lub.
cut (ex - 1 < xe + prec)%Z.
omega.
apply <- epow_lt.
apply Rle_lt_trans with (1 := proj1 Hx5).
rewrite Hx1.
rewrite abs_F2R.
unfold F2R. simpl.
rewrite Zplus_comm.
rewrite epow_add.
apply Rmult_lt_compat_r.
apply epow_gt_0.
rewrite <- Z2R_Zpower.
now apply Z2R_lt.
now apply Zlt_le_weak.
exact Hx3.
rewrite Hx6.
eexists ; repeat split.
intros H.
simpl.
apply f_equal.
apply sym_eq.
apply ln_beta_unique.
now rewrite <- Hx6.
Qed.

Theorem FLT_format_satisfies_any :
  satisfies_any FLT_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLT_exp _)).
exact FLT_format_generic.
exact FLT_exp_correct.
Qed.

End RND_FLT.

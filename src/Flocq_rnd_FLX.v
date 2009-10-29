Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_generic.
Require Import Flocq_float_prop.
Require Import Flocq_rnd_FIX.

Section RND_FLX.

Variable beta : radix.

Notation bpow e := (bpow beta e).

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

Theorem FLX_format_FIX :
  forall x e,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  ( FLX_format x <-> FIX_format beta (e - prec) x ).
Proof.
intros x e Hx.
split.
(* . *)
intros ((xm, xe), (H1, H2)).
rewrite H1, (F2R_prec_normalize beta xm xe e prec).
now eexists.
exact H2.
now rewrite <- H1.
(* . *)
destruct Hx as (Hx1,[Hx2|Hx2]).
(* . . *)
intros ((xm, xe), (H1, H2)).
rewrite H1.
eexists ; repeat split.
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow (e - prec)).
apply bpow_gt_0.
rewrite Z2R_Zpower, <- bpow_add.
ring_simplify (prec + (e - prec))%Z.
rewrite <- H2.
simpl.
change (F2R (Float beta (Zabs xm) xe) < bpow e)%R.
now rewrite <- abs_F2R, <- H1.
now apply Zlt_le_weak.
(* . . *)
intros ((xm, xe), (H1, H2)).
assert (Ha: forall x, FLX_format (Rabs x) -> FLX_format x).
clear.
intros x Ha.
unfold Rabs in Ha.
destruct (Rcase_abs x) as [Hx|Hx].
destruct Ha as ((m,e),(Ha,Hb)).
exists (Float beta (-m) e).
split.
now rewrite <- opp_F2R, <- Ha, Ropp_involutive.
simpl.
now rewrite Zabs_Zopp.
exact Ha.
(* . . *)
apply Ha.
rewrite Hx2.
exists (Float beta 1 e).
split.
apply sym_eq.
apply Rmult_1_l.
now apply Zpower_gt_1.
Qed.

Theorem FLX_format_generic :
  forall x : R, FLX_format x <-> generic_format beta FLX_exp x.
Proof.
intros x.
destruct (Req_dec x 0) as [Hx|Hx1].
(* . *)
split ; intros H ; rewrite Hx.
apply generic_format_0.
exists (Float beta 0 0).
split.
unfold F2R. simpl.
now rewrite Rmult_0_l.
apply Zpower_gt_0.
now apply Zlt_le_trans with (2 := radix_prop beta).
now apply Zlt_le_weak.
(* . *)
destruct (ln_beta beta x) as (ex, Hx2).
simpl.
specialize (Hx2 Hx1).
apply iff_trans with (generic_format beta (FIX_exp (ex - prec)) x).
apply iff_trans with (FIX_format beta (ex - prec) x).
apply FLX_format_FIX.
exact (conj (proj1 Hx2) (Rlt_le _ _ (proj2 Hx2))).
apply FIX_format_generic.
assert (Hf: FLX_exp (projT1 (ln_beta beta x)) = FIX_exp (ex - prec) (projT1 (ln_beta beta x))).
unfold FIX_exp, FLX_exp.
now rewrite ln_beta_unique with (1 := Hx2).
split ; apply generic_format_fun_eq ; now rewrite Hf.
Qed.

Theorem FLX_format_satisfies_any :
  satisfies_any FLX_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLX_exp _)).
intros x.
apply iff_sym.
apply FLX_format_generic.
exact FLX_exp_correct.
Qed.

(* unbounded floating-point format with normal mantissas *)
Definition FLXN_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (x <> R0 ->
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
elim H.
rewrite H1, H3.
apply Rmult_0_l.
destruct (ln_beta beta (Z2R xm)) as (d,H4).
specialize (H4 (Z2R_neq _ _ H3)).
assert (H5: (0 <= prec - d)%Z).
cut (d - 1 < prec)%Z. omega.
apply <- (bpow_lt beta).
apply Rle_lt_trans with (Rabs (Z2R xm)).
apply H4.
rewrite <- Z2R_Zpower, <- abs_Z2R.
now apply Z2R_lt.
now apply Zlt_le_weak.
exists (Float beta (xm * Zpower (radix_val beta) (prec - d)) (xe + d - prec)).
split.
unfold F2R. simpl.
rewrite mult_Z2R, Z2R_Zpower.
rewrite Rmult_assoc, <- bpow_add.
rewrite H1.
now ring_simplify (prec - d + (xe + d - prec))%Z.
exact H5.
intros _. simpl.
split.
apply le_Z2R.
apply Rmult_le_reg_r with (bpow (d - prec)).
apply bpow_gt_0.
rewrite abs_Z2R, mult_Z2R, Rabs_mult, 2!Z2R_Zpower.
rewrite <- bpow_add.
rewrite <- abs_Z2R.
rewrite Rabs_pos_eq.
rewrite Rmult_assoc, <- bpow_add.
ring_simplify (prec - 1 + (d - prec))%Z.
ring_simplify (prec - d + (d - prec))%Z.
now rewrite Rmult_1_r, abs_Z2R.
apply bpow_ge_0.
exact H5.
omega.
apply lt_Z2R.
rewrite abs_Z2R, mult_Z2R, Rabs_mult.
rewrite 2!Z2R_Zpower.
rewrite <- abs_Z2R, Rabs_pos_eq.
apply Rmult_lt_reg_r with (bpow (d - prec)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- 2!bpow_add.
ring_simplify (prec + (d - prec))%Z.
ring_simplify (prec - d + (d - prec))%Z.
now rewrite Rmult_1_r, abs_Z2R.
apply bpow_ge_0.
now apply Zlt_le_weak.
exact H5.
(* . *)
intros ((xm, xe), (H1, H2)).
destruct (Req_dec x 0) as [H3|H3].
rewrite H3.
apply <- FLX_format_generic.
apply generic_format_0.
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
now apply <- FLX_format_generic.
apply -> FLX_format_generic.
now apply <- FLX_format_FLXN.
exact FLX_exp_correct.
Qed.

End RND_FLX.

Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_generic.
Require Import Flocq_float_prop.
Require Import Flocq_rnd_FLX.
Require Import Flocq_rnd_FIX.

Section RND_FLT.

Variable beta : radix.

Notation bpow e := (epow beta e).

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
now apply Zlt_le_weak.
apply Zle_refl.
rewrite Hx1.
eexists ; repeat split.
destruct (ln_beta beta x) as (ex, Hx4).
simpl in Hx2.
specialize (Hx4 Hx3).
apply lt_Z2R.
rewrite Z2R_Zpower.
apply Rmult_lt_reg_r with (bpow (ex - prec)).
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
apply generic_format_0.
simpl in Hx2, Hx3.
unfold generic_format, canonic, FLT_exp.
destruct (ln_beta beta x) as (ex, Hx5).
simpl.
specialize (Hx5 Hx4).
destruct (Zmax_spec (ex - prec) emin) as [(H1,H2)|(H1,H2)] ;
  rewrite H2 ; clear H2.
rewrite Hx1, (F2R_prec_normalize beta xm xe ex prec Hx2).
now eexists.
now rewrite <- Hx1.
rewrite Hx1, (F2R_change_exp beta emin).
now eexists.
exact Hx3.
Qed.

Theorem FLT_format_satisfies_any :
  satisfies_any FLT_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLT_exp _)).
exact FLT_format_generic.
exact FLT_exp_correct.
Qed.

Theorem FLT_format_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  ( FLT_format x <-> FLX_format beta prec x ).
Proof.
intros x Hx1.
split.
(* . *)
intros ((xm, xe), (Hx2, (Hx3, Hx4))).
rewrite Hx2.
eexists ; split ; easy.
(* . *)
intros Hx2.
destruct (Req_dec x 0) as [Hx3|Hx3].
(* . . *)
rewrite Hx3.
apply -> FLT_format_generic.
apply generic_format_0.
(* . . *)
destruct (proj2 (FLX_format_generic _ _ Hp x) Hx2) as ((xm, xe), (Hx4, Hx5)).
apply -> FLT_format_generic.
rewrite Hx4.
eexists ; repeat split.
rewrite Hx5. clear Hx5.
rewrite <- Hx4.
destruct (ln_beta beta x) as (ex, Hx5).
unfold FLX_exp, FLT_exp.
simpl.
apply sym_eq.
apply Zmax_left.
cut (emin + prec <= ex)%Z. omega.
apply epow_lt_epow with beta.
apply Rle_lt_trans with (1 := Hx1).
now apply Hx5.
Qed.

Theorem FLT_format_FIX :
  forall x,
  (Rabs x <= bpow (emin + prec))%R ->
  ( FLT_format x <-> FIX_format beta emin x ).
Proof.
intros x Hx.
split.
(* . *)
intros ((xm, xe), (H1, (H2, H3))).
rewrite H1, (F2R_change_exp beta emin).
now eexists.
exact H3.
(* . *)
destruct Hx as [Hx|Hx].
(* . . *)
intros ((xm, xe), (H1, H2)).
rewrite H1.
eexists ; repeat split.
apply lt_Z2R.
rewrite Z2R_Zpower.
apply Rmult_lt_reg_r with (bpow xe).
apply epow_gt_0.
rewrite H1, abs_F2R in Hx.
apply Rlt_le_trans with (1 := Hx).
rewrite <- epow_add.
apply -> epow_le.
rewrite Zplus_comm, <- H2.
apply Zle_refl.
now apply Zlt_le_weak.
now apply Zeq_le.
(* . . *)
assert (Ha: forall x, FLT_format (Rabs x) -> FLT_format x).
clear.
intros x Ha.
unfold Rabs in Ha.
destruct (Rcase_abs x) as [Hx|Hx].
apply -> FLT_format_generic.
rewrite <- (Ropp_involutive x).
apply generic_format_sym.
now apply <- FLT_format_generic.
exact Ha.
(* . . *)
intros _.
apply Ha.
rewrite Hx.
exists (Float beta 1 (emin + prec)).
split.
apply sym_eq.
apply Rmult_1_l.
simpl.
split.
now apply Zpower_gt_1.
omega.
Qed.

End RND_FLT.

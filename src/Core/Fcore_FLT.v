Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_float_prop.
Require Import Fcore_FLX.
Require Import Fcore_FIX.
Require Import Fcore_rnd_ne.

Section RND_FLT.

Variable beta : radix.

Notation bpow e := (bpow beta e).

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
  forall x : R, FLT_format x <-> generic_format beta FLT_exp x.
Proof.
split.
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
apply bpow_gt_0.
rewrite <- bpow_add.
replace (prec + (ex - prec))%Z with ex by ring.
apply Rle_lt_trans with (Z2R (Zabs xm) * bpow xe)%R.
rewrite Hx2.
apply Rmult_le_compat_l.
apply (Z2R_le 0).
apply Zabs_pos.
apply -> bpow_le.
apply Zle_max_l.
replace (Z2R (Zabs xm) * bpow xe)%R with (Rabs x).
exact (proj2 Hx4).
rewrite Hx1.
apply abs_F2R.
now apply Zlt_le_weak.
rewrite Hx2.
apply Zle_max_r.
Qed.

Theorem FLT_format_satisfies_any :
  satisfies_any FLT_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLT_exp _)).
intros x.
apply iff_sym.
apply FLT_format_generic.
exact FLT_exp_correct.
Qed.

Theorem FLT_canonic_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  forall f : float beta,
  ( canonic beta FLT_exp x f <-> canonic beta (FLX_exp prec) x f ).
Proof.
intros x Hx f.
unfold canonic.
replace (FLT_exp (projT1 (ln_beta beta x))) with (FLX_exp prec (projT1 (ln_beta beta x))).
apply iff_refl.
unfold FLX_exp, FLT_exp.
apply sym_eq.
apply Zmax_left.
destruct (ln_beta beta x) as (ex, He).
simpl.
assert (emin + prec - 1 < ex)%Z. 2: omega.
apply <- (bpow_lt beta).
apply Rle_lt_trans with (1 := Hx).
apply He.
intros H.
elim Rlt_not_le with (2 := Hx).
rewrite H, Rabs_R0.
apply bpow_gt_0.
Qed.

Theorem FLT_generic_format_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  ( generic_format beta FLT_exp x <-> generic_format beta (FLX_exp prec) x ).
Proof.
intros x Hx.
assert (Hc := FLT_canonic_FLX x Hx).
split ; intros (f, Hf) ; exists f.
now apply -> Hc.
now apply <- Hc.
Qed.

Theorem FLT_format_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  ( FLT_format x <-> FLX_format beta prec x ).
Proof.
intros x Hx1.
assert (Hc := FLT_canonic_FLX x Hx1).
apply iff_trans with (1 := FLT_format_generic x).
apply iff_trans with (1 := FLT_generic_format_FLX x Hx1).
apply iff_sym.
now apply FLX_format_generic.
Qed.

Theorem FLT_exp_FIX :
  forall x, x <> R0 ->
  (Rabs x < bpow (emin + prec))%R ->
  FLT_exp (projT1 (ln_beta beta x)) = FIX_exp emin (projT1 (ln_beta beta x)).
Proof.
intros x Hx0 Hx.
unfold FIX_exp, FLT_exp.
rewrite Zmax_right.
apply refl_equal.
destruct (ln_beta beta x) as (ex, Hex).
simpl.
cut (ex - 1 < emin + prec)%Z. omega.
apply <- (bpow_lt beta).
apply Rle_lt_trans with (2 := Hx).
now apply Hex.
Qed.

Theorem FLT_canonic_FIX :
  forall x : R, x <> R0 ->
  (Rabs x < bpow (emin + prec))%R ->
  forall f : float beta,
  ( canonic beta FLT_exp x f <-> canonic beta (FIX_exp emin) x f ).
Proof.
intros x Hx0 Hx f.
unfold canonic.
now rewrite FLT_exp_FIX.
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
apply bpow_gt_0.
rewrite H1, abs_F2R in Hx.
apply Rlt_le_trans with (1 := Hx).
rewrite <- bpow_add.
apply -> bpow_le.
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
apply <- FLT_format_generic.
rewrite <- (Ropp_involutive x).
apply generic_format_sym.
now apply -> FLT_format_generic.
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

Theorem Rnd_NE_pt_FLT :
  Zodd (radix_val beta) \/ (1 < prec)%Z ->
  rounding_pred (Rnd_NE_pt beta FLT_exp).
Proof.
intros H.
apply Rnd_NE_pt_rounding.
apply FLT_exp_correct.
destruct H.
now left.
right.
intros e.
unfold FLT_exp.
destruct (Zmax_spec (e - prec) emin) as [(H1,H2)|(H1,H2)].
rewrite H2.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (e - prec + 1 - prec) emin).
omega.
rewrite H2.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (emin + 1 - prec) emin).
omega.
Qed.

End RND_FLT.

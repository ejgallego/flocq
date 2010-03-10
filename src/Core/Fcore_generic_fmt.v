Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_float_prop.

Section RND_generic.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Definition valid_exp :=
  forall k : Z,
  ( (fexp k < k)%Z -> (fexp (k + 1) <= k)%Z ) /\
  ( (k <= fexp k)%Z ->
    (fexp (fexp k + 1) <= fexp k)%Z /\
    forall l : Z, (l <= fexp k)%Z -> fexp l = fexp k ).

Variable prop_exp : valid_exp.

Definition canonic_exponent x :=
  fexp (projT1 (ln_beta beta x)).

Definition canonic (f : float beta) :=
  Fexp f = canonic_exponent (F2R f).

Definition scaled_mantissa x :=
  (x * bpow (- canonic_exponent x))%R.

Definition generic_format (x : R) :=
  x = F2R (Float beta (Ztrunc (scaled_mantissa x)) (canonic_exponent x)).

(*
Theorem canonic_mantissa_0 :
  canonic_mantissa 0 = Z0.
Proof.
unfold canonic_mantissa.
rewrite Rmult_0_l.
exact (Zfloor_Z2R 0).
Qed.
*)

Theorem generic_format_0 :
  generic_format 0.
Proof.
unfold generic_format, scaled_mantissa.
rewrite Rmult_0_l.
change (Ztrunc 0) with (Ztrunc (Z2R 0)).
now rewrite Ztrunc_Z2R, F2R_0.
Qed.

Theorem canonic_exponent_opp :
  forall x,
  canonic_exponent (-x) = canonic_exponent x.
Proof.
intros x.
unfold canonic_exponent.
now rewrite ln_beta_opp.
Qed.

(*
Theorem canonic_mantissa_opp :
  forall x,
  generic_format x ->
  canonic_mantissa (-x) = (- canonic_mantissa x)%Z.
Proof.
unfold generic_format, canonic_mantissa.
intros x Hx.
rewrite canonic_exponent_opp.
rewrite Hx at 1 3.
generalize (canonic_exponent x).
intros e.
clear.
unfold F2R. simpl.
rewrite Ropp_mult_distr_l_reverse.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_r.
rewrite Rmult_1_r.
rewrite <- opp_Z2R.
now rewrite 2!Zfloor_Z2R.
Qed.
*)

Theorem generic_format_bpow :
  forall e, (fexp (e + 1) <= e)%Z ->
  generic_format (bpow e).
Proof.
intros e H.
unfold generic_format, scaled_mantissa, canonic_exponent.
rewrite ln_beta_bpow.
rewrite <- bpow_add.
rewrite <- (Z2R_Zpower beta (e + - fexp (e + 1))).
rewrite Ztrunc_Z2R.
rewrite <- F2R_bpow.
rewrite F2R_change_exp with (1 := H).
now rewrite Zmult_1_l.
omega.
Qed.

Theorem generic_format_canonic_exponent :
  forall m e,
  (canonic_exponent (F2R (Float beta m e)) <= e)%Z ->
  generic_format (F2R (Float beta m e)).
Proof.
intros m e.
unfold generic_format, scaled_mantissa.
set (e' := canonic_exponent (F2R (Float beta m e))).
intros He.
unfold F2R at 3. simpl.
assert (H: (Z2R m * bpow e * bpow (- e') = Z2R (m * Zpower (radix_val beta) (e + -e')))%R).
rewrite Rmult_assoc, <- bpow_add, mult_Z2R.
rewrite Z2R_Zpower.
apply refl_equal.
now apply Zle_left.
rewrite H, Ztrunc_Z2R.
unfold F2R. simpl.
rewrite <- H.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_l.
now rewrite Rmult_1_r.
Qed.

Theorem canonic_opp :
  forall m e,
  canonic (Float beta m e) ->
  canonic (Float beta (-m) e).
Proof.
intros m e H.
unfold canonic.
now rewrite <- opp_F2R, canonic_exponent_opp.
Qed.

Theorem canonic_unicity :
  forall f1 f2,
  canonic f1 ->
  canonic f2 ->
  F2R f1 = F2R f2 ->
  f1 = f2.
Proof.
intros (m1, e1) (m2, e2).
unfold canonic. simpl.
intros H1 H2 H.
rewrite H in H1.
rewrite <- H2 in H1. clear H2.
rewrite H1 in H |- *.
apply (f_equal (fun m => Float beta m e2)).
apply F2R_eq_reg with (1 := H).
Qed.

Theorem scaled_mantissa_generic :
  forall x,
  generic_format x ->
  scaled_mantissa x = Z2R (Ztrunc (scaled_mantissa x)).
Proof.
intros x Hx.
unfold scaled_mantissa.
pattern x at 1 3 ; rewrite Hx.
unfold F2R. simpl.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_r, Rmult_1_r.
now rewrite Ztrunc_Z2R.
Qed.

Theorem scaled_mantissa_bpow :
  forall x,
  (scaled_mantissa x * bpow (canonic_exponent x))%R = x.
Proof.
intros x.
unfold scaled_mantissa.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_l.
apply Rmult_1_r.
Qed.

Theorem scaled_mantissa_opp :
  forall x,
  scaled_mantissa (-x) = (-scaled_mantissa x)%R.
Proof.
intros x.
unfold scaled_mantissa.
rewrite canonic_exponent_opp.
now rewrite Ropp_mult_distr_l_reverse.
Qed.

Theorem generic_format_opp :
  forall x, generic_format x -> generic_format (-x).
Proof.
intros x Hx.
unfold generic_format.
rewrite scaled_mantissa_opp, canonic_exponent_opp.
rewrite Ztrunc_opp.
rewrite <- opp_F2R.
now apply f_equal.
Qed.

Theorem canonic_exponent_fexp_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  canonic_exponent x = fexp ex.
Proof.
intros x ex Hx.
unfold canonic_exponent.
rewrite <- (Rabs_pos_eq x) in Hx.
now rewrite ln_beta_unique with (1 := Hx).
apply Rle_trans with (2 := proj1 Hx).
apply bpow_ge_0.
Qed.

Theorem canonic_exponent_fexp_neg :
  forall x ex,
  (bpow (ex - 1) <= -x < bpow ex)%R ->
  canonic_exponent x = fexp ex.
Proof.
intros x ex Hx.
unfold canonic_exponent.
rewrite <- (Rabs_left1 x) in Hx.
now rewrite ln_beta_unique with (1 := Hx).
apply Ropp_le_cancel.
rewrite Ropp_0.
apply Rle_trans with (2 := proj1 Hx).
apply bpow_ge_0.
Qed.

Theorem canonic_exponent_fexp :
  forall x ex,
  (bpow (ex - 1) <= Rabs x < bpow ex)%R ->
  canonic_exponent x = fexp ex.
Proof.
intros x ex Hx.
unfold canonic_exponent.
now rewrite ln_beta_unique with (1 := Hx).
Qed.

Theorem mantissa_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  (0 < x * bpow (- fexp ex) < 1)%R.
Proof.
intros x ex Hx He.
split.
apply Rmult_lt_0_compat.
apply Rlt_le_trans with (2 := proj1 Hx).
apply bpow_gt_0.
apply bpow_gt_0.
apply Rmult_lt_reg_r with (bpow (fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_l.
rewrite Rmult_1_r, Rmult_1_l.
apply Rlt_le_trans with (1 := proj2 Hx).
now apply -> bpow_le.
Qed.

Theorem mantissa_DN_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Zfloor (x * bpow (- fexp ex)) = Z0.
Proof.
intros x ex Hx He.
apply Zfloor_imp. simpl.
assert (H := mantissa_small_pos x ex Hx He).
split ; try apply Rlt_le ; apply H.
Qed.

Theorem mantissa_UP_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Zceil (x * bpow (- fexp ex)) = 1%Z.
Proof.
intros x ex Hx He.
apply Zceil_imp. simpl.
assert (H := mantissa_small_pos x ex Hx He).
split ; try apply Rlt_le ; apply H.
Qed.

Theorem generic_format_discrete :
  forall x m,
  let e := canonic_exponent x in
  (F2R (Float beta m e) < x < F2R (Float beta (m + 1) e))%R ->
  ~ generic_format x.
Proof.
intros x m e (Hx,Hx2) Hf.
apply Rlt_not_le with (1 := Hx2). clear Hx2.
rewrite Hf.
fold e.
apply F2R_le_compat.
apply Zlt_le_succ.
apply lt_Z2R.
rewrite <- scaled_mantissa_generic with (1 := Hf).
apply Rmult_lt_reg_r with (bpow e).
apply bpow_gt_0.
now rewrite scaled_mantissa_bpow.
Qed.

Theorem generic_DN_pt_large_pos_ge_pow_aux :
  forall x ex,
  (fexp ex < ex)%Z ->
  (bpow (ex - 1) <= x)%R ->
  (bpow (ex - 1) <= F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex)))%R.
Proof.
intros x ex He1 Hx1.
unfold F2R. simpl.
replace (ex - 1)%Z with ((ex - 1 - fexp ex) + fexp ex)%Z by ring.
rewrite bpow_add.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (Hx2 : bpow (ex - 1 - fexp ex) = Z2R (Zpower (radix_val beta) (ex - 1 - fexp ex))).
apply sym_eq.
apply Z2R_Zpower.
omega.
rewrite Hx2.
apply Z2R_le.
apply Zfloor_lub.
rewrite <- Hx2.
unfold Zminus at 1.
rewrite bpow_add.
apply Rmult_le_compat_r.
apply bpow_ge_0.
exact Hx1.
Qed.

Theorem generic_format_canonic :
  forall f, canonic f ->
  generic_format (F2R f).
Proof.
intros (m, e) Hf.
unfold canonic in Hf. simpl in Hf.
unfold generic_format, scaled_mantissa.
rewrite <- Hf.
apply (f_equal (fun m => F2R (Float beta m e))).
unfold F2R. simpl.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_r, Rmult_1_r.
now rewrite Ztrunc_Z2R.
Qed.

Section Fcore_generic_rounding_pos.

Variable Zrnd : R -> Z.
Hypothesis Zrnd_monotone : forall x y, (x <= y)%R -> (Zrnd x <= Zrnd y)%Z.
Hypothesis Zrnd_Z2R : forall n, Zrnd (Z2R n) = n.

Definition rounding x :=
  F2R (Float beta (Zrnd (scaled_mantissa x)) (canonic_exponent x)).

Theorem rounding_monotone_pos :
  forall x y, (0 < x)%R -> (x <= y)%R -> (rounding x <= rounding y)%R.
Proof.
intros x y Hx Hxy.
unfold rounding, scaled_mantissa, canonic_exponent.
destruct (ln_beta beta x) as (ex, Hex). simpl.
destruct (ln_beta beta y) as (ey, Hey). simpl.
specialize (Hex (Rgt_not_eq _ _ Hx)).
specialize (Hey (Rgt_not_eq _ _ (Rlt_le_trans _ _ _ Hx Hxy))).
rewrite Rabs_pos_eq in Hex.
2: now apply Rlt_le.
rewrite Rabs_pos_eq in Hey.
2: apply Rle_trans with (2:=Hxy); now apply Rlt_le.
assert (He: (ex <= ey)%Z).
cut (ex - 1 < ey)%Z. omega.
apply <- bpow_lt.
apply Rle_lt_trans with (1 := proj1 Hex).
apply Rle_lt_trans with (1 := Hxy).
apply Hey.
destruct (Zle_or_lt ey (fexp ey)) as [Hy1|Hy1].
rewrite (proj2 (proj2 (prop_exp ey) Hy1) ex).
apply F2R_le_compat.
apply Zrnd_monotone.
apply Rmult_le_compat_r.
apply bpow_ge_0.
exact Hxy.
now apply Zle_trans with ey.
destruct (Zle_lt_or_eq _ _ He) as [He'|He'].
destruct (Zle_or_lt ey (fexp ex)) as [Hx2|Hx2].
rewrite (proj2 (proj2 (prop_exp ex) (Zle_trans _ _ _ He Hx2)) ey Hx2).
apply F2R_le_compat.
apply Zrnd_monotone.
apply Rmult_le_compat_r.
apply bpow_ge_0.
exact Hxy.
apply Rle_trans with (F2R (Float beta (Zrnd (bpow (ey - 1) * bpow (- fexp ey))%R) (fexp ey))).
rewrite <- bpow_add.
rewrite <- (Z2R_Zpower beta (ey - 1 + -fexp ey)). 2: omega.
rewrite Zrnd_Z2R.
destruct (Zle_or_lt ex (fexp ex)) as [Hx1|Hx1].
apply Rle_trans with (F2R (Float beta 1 (fexp ex))).
apply F2R_le_compat.
rewrite <- (Zrnd_Z2R 1).
apply Zrnd_monotone.
apply Rlt_le.
exact (proj2 (mantissa_small_pos _ _ Hex Hx1)).
unfold F2R. simpl.
rewrite Z2R_Zpower. 2: omega.
rewrite <- bpow_add, Rmult_1_l.
apply -> bpow_le.
omega.
apply Rle_trans with (F2R (Float beta (Zrnd (bpow ex * bpow (- fexp ex))%R) (fexp ex))).
apply F2R_le_compat.
apply Zrnd_monotone.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rlt_le.
apply Hex.
rewrite <- bpow_add.
rewrite <- Z2R_Zpower. 2: omega.
rewrite Zrnd_Z2R.
unfold F2R. simpl.
rewrite 2!Z2R_Zpower ; try omega.
rewrite <- 2!bpow_add.
apply -> bpow_le.
omega.
apply F2R_le_compat.
apply Zrnd_monotone.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Hey.
rewrite He'.
apply F2R_le_compat.
apply Zrnd_monotone.
apply Rmult_le_compat_r.
apply bpow_ge_0.
exact Hxy.
Qed.

Theorem rounding_generic :
  forall x,
  generic_format x ->
  rounding x = x.
Proof.
intros x Hx.
unfold rounding.
rewrite scaled_mantissa_generic with (1 := Hx).
rewrite Zrnd_Z2R.
now apply sym_eq.
Qed.

Theorem rounding_0 :
  rounding 0 = R0.
Proof.
unfold rounding, scaled_mantissa.
rewrite Rmult_0_l.
fold (Z2R 0).
rewrite Zrnd_Z2R.
apply F2R_0.
Qed.

End Fcore_generic_rounding_pos.

Section Fcore_generic_rounding.

Variable Zrnd : R -> Z.
Hypothesis Zrnd_monotone : forall x y, (x <= y)%R -> (Zrnd x <= Zrnd y)%Z.
Hypothesis Zrnd_Z2R : forall n, Zrnd (Z2R n) = n.

Theorem rounding_monotone :
  forall x y, (x <= y)%R -> (rounding Zrnd x <= rounding Zrnd y)%R.
Proof.
intros x y Hxy.
destruct (total_order_T x 0) as [[Hx|Hx]|Hx].
3: now apply rounding_monotone_pos.
(* x < 0 *)
unfold rounding.
destruct (Rlt_or_le y 0) as [Hy|Hy].
(* . y < 0 *)
rewrite <- (Ropp_involutive x), <- (Ropp_involutive y).
rewrite (scaled_mantissa_opp (-x)), (scaled_mantissa_opp (-y)).
rewrite (canonic_exponent_opp (-x)), (canonic_exponent_opp (-y)).
apply Ropp_le_cancel.
rewrite 2!opp_F2R.
apply (rounding_monotone_pos (fun m => (- Zrnd (- m))%Z)).
clear - Zrnd_monotone.
intros.
apply Zopp_le_cancel.
rewrite 2!Zopp_involutive.
apply Zrnd_monotone.
now apply Ropp_le_contravar.
clear - Zrnd_Z2R.
intros n.
rewrite <- opp_Z2R, Zrnd_Z2R.
apply Zopp_involutive.
rewrite <- Ropp_0.
now apply Ropp_lt_contravar.
now apply Ropp_le_contravar.
(* . 0 <= y *)
apply Rle_trans with R0.
apply F2R_le_0_compat. simpl.
rewrite <- (Zrnd_Z2R 0).
apply Zrnd_monotone.
simpl.
rewrite <- (Rmult_0_l (bpow (- fexp (projT1 (ln_beta beta x))))).
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply Rlt_le.
apply F2R_ge_0_compat. simpl.
rewrite <- (Zrnd_Z2R Z0).
apply Zrnd_monotone.
apply Rmult_le_pos.
exact Hy.
apply bpow_ge_0.
(* x = 0 *)
rewrite Hx.
rewrite rounding_0. 2: exact Zrnd_Z2R.
apply F2R_ge_0_compat.
simpl.
rewrite <- (Zrnd_Z2R 0).
apply Zrnd_monotone.
apply Rmult_le_pos.
now rewrite <- Hx.
apply bpow_ge_0.
Qed.

End Fcore_generic_rounding.

Theorem generic_DN_pt_pos :
  forall x, (0 < x)%R ->
  Rnd_DN_pt generic_format x (F2R (Float beta (Zfloor (scaled_mantissa x)) (canonic_exponent x))).
Proof.
intros x H0x.
unfold scaled_mantissa, canonic_exponent.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He (Rgt_not_eq _ _ H0x)).
rewrite (Rabs_pos_eq _ (Rlt_le _ _ H0x)) in He.
destruct (Z_lt_le_dec (fexp ex) ex) as [He1|He1].
(* - positive big enough *)
assert (Hbl : (bpow (ex - 1) <= F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex)))%R).
now apply generic_DN_pt_large_pos_ge_pow_aux.
(* - . smaller *)
assert (Hrx : (F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex)) <= x)%R).
unfold F2R. simpl.
apply Rmult_le_reg_r with (bpow (- fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_r, Rmult_1_r.
apply Zfloor_lb.
split.
(* - . rounded *)
apply generic_format_canonic.
apply sym_eq.
apply canonic_exponent_fexp_pos.
split.
exact Hbl.
now apply Rle_lt_trans with (2 := proj2 He).
split.
exact Hrx.
(* - . biggest *)
intros g Hg Hgx.
destruct (Rle_or_lt g R0) as [Hg3|Hg3].
apply Rle_trans with (2 := Hbl).
apply Rle_trans with (1 := Hg3).
apply bpow_ge_0.
apply Rnot_lt_le.
intros Hrg.
assert (bpow (ex - 1) <= g < bpow ex)%R.
split.
apply Rle_trans with (1 := Hbl).
now apply Rlt_le.
now apply Rle_lt_trans with (1 := Hgx).
assert (Hcg: canonic_exponent g = fexp ex).
unfold canonic_exponent.
rewrite <- (Rabs_pos_eq g (Rlt_le _ _ Hg3)) in H.
now rewrite ln_beta_unique with (1 := H).
apply Rlt_not_le with (1 := Hrg).
rewrite Hg.
rewrite Hcg.
apply F2R_le_compat.
apply Zfloor_lub.
apply Rmult_le_reg_r with (bpow (fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc.
rewrite <- bpow_add.
rewrite Zplus_opp_l.
rewrite Rmult_1_r.
rewrite <- Hcg.
now rewrite Hg in Hgx.
(* - positive too small *)
rewrite mantissa_DN_small_pos with (1 := He) (2 := He1).
rewrite F2R_0.
split.
(* - . rounded *)
exact generic_format_0.
split.
now apply Rlt_le.
(* - . biggest *)
intros g Hg Hgx.
apply Rnot_lt_le.
intros Hg3.
destruct (ln_beta beta g) as (ge, Hg4).
simpl in Hg.
specialize (Hg4 (Rgt_not_eq _ _ Hg3)).
assert (Hcg: canonic_exponent g = fexp ge).
unfold canonic_exponent.
now rewrite ln_beta_unique with (1 := Hg4).
rewrite Rabs_pos_eq in Hg4.
apply (Rlt_not_le _ _ (Rle_lt_trans _ _ _ Hgx (proj2 He))).
apply Rle_trans with (bpow (fexp ge)).
apply -> bpow_le.
rewrite (proj2 (proj2 (prop_exp ex) He1) ge).
exact He1.
apply Zle_trans with (2 := He1).
cut (ge - 1 < ex)%Z. omega.
apply <- bpow_lt.
apply Rle_lt_trans with (2 := proj2 He).
apply Rle_trans with (2 := Hgx).
exact (proj1 Hg4).
rewrite Hg.
rewrite <- F2R_bpow.
rewrite Hcg.
apply F2R_le_compat.
apply (Zlt_le_succ 0).
apply F2R_lt_reg with beta (fexp ge).
rewrite F2R_0, <- Hcg.
now rewrite Hg in Hg3.
now apply Rlt_le.
Qed.

Theorem generic_DN_pt_neg :
  forall x, (x < 0)%R ->
  Rnd_DN_pt generic_format x (F2R (Float beta (Zfloor (scaled_mantissa x)) (canonic_exponent x))).
Proof.
intros x Hx0.
unfold scaled_mantissa, canonic_exponent.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He (Rlt_not_eq _ _ Hx0)).
rewrite (Rabs_left _ Hx0) in He.
assert (Hbr : (F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex)) <= x)%R).
(* - bounded right *)
unfold F2R. simpl.
apply Rmult_le_reg_r with (bpow (-fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_r, Rmult_1_r.
apply Zfloor_lb.
destruct (Z_lt_le_dec (fexp ex) ex) as [He1|He1].
(* - negative big enough *)
assert (Hbl : (- bpow ex <= F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex)))%R).
(* - . bounded left *)
unfold F2R. simpl.
apply Rmult_le_reg_r with (bpow (-fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_r, Rmult_1_r.
assert (Hp : (- bpow ex * bpow (-fexp ex) = Z2R (- Zpower (radix_val beta) (ex - fexp ex)))%R).
rewrite Ropp_mult_distr_l_reverse.
rewrite <- bpow_add, <- Z2R_Zpower.
now rewrite opp_Z2R.
omega.
rewrite Hp.
apply Z2R_le.
apply Zfloor_lub.
rewrite <- Hp.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
now apply Rlt_le.
split.
(* - . rounded *)
destruct (Rle_lt_or_eq_dec _ _ Hbl) as [Hbl2|Hbl2].
(* - . . not a radix power *)
apply generic_format_canonic.
assert (Hb: (bpow (ex - 1) <= - F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex)) < bpow ex)%R).
split.
apply Rle_trans with (1 := proj1 He).
now apply Ropp_le_contravar.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
apply sym_eq.
apply canonic_exponent_fexp_neg with (1 := Hb).
(* - . . a radix power *)
rewrite <- Hbl2.
apply generic_format_opp.
apply generic_format_bpow.
exact (proj1 (prop_exp _) He1).
split.
exact Hbr.
(* - . biggest *)
intros g Hg Hgx.
apply Rnot_lt_le.
intros Hg3.
assert (Hg4 : (g < 0)%R).
now apply Rle_lt_trans with (1 := Hgx).
destruct (ln_beta beta g) as (ge, Hge).
specialize (Hge (Rlt_not_eq _ _ Hg4)).
apply Rlt_not_le with (1 := Hg3).
rewrite Hg.
assert (Hge' : ge = ex).
apply bpow_unique with (1 := Hge).
split.
apply Rle_trans with (1 := proj1 He).
rewrite Rabs_left with (1 := Hg4).
now apply Ropp_le_contravar.
apply Ropp_lt_cancel.
rewrite Rabs_left with (1 := Hg4).
rewrite Ropp_involutive.
now apply Rle_lt_trans with (1 := Hbl).
assert (Hcg: canonic_exponent g = fexp ex).
rewrite <- Hge'.
now apply canonic_exponent_fexp.
rewrite Hcg.
apply F2R_le_compat.
apply Zfloor_lub.
apply Rmult_le_reg_r with (bpow (fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc.
rewrite <- bpow_add, Zplus_opp_l, Rmult_1_r.
rewrite <- Hcg.
now rewrite Hg in Hgx.
(* - negative too small *)
rewrite <- (Zopp_involutive (Zfloor (x * bpow (- fexp ex)))).
rewrite <- (Ropp_involutive x) at 2.
rewrite Ropp_mult_distr_l_reverse.
change (- Zfloor (- (- x * bpow (- fexp ex))))%Z with (Zceil (- x * bpow (- fexp ex)))%Z.
rewrite mantissa_UP_small_pos ; try assumption.
unfold F2R. simpl.
rewrite Ropp_mult_distr_l_reverse.
rewrite Rmult_1_l.
(* - . rounded *)
split.
apply generic_format_opp.
apply generic_format_bpow.
exact (proj1 (proj2 (prop_exp _) He1)).
split.
(* - . smaller *)
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Rlt_le.
apply Rlt_le_trans with (1 := proj2 He).
now apply -> bpow_le.
(* - . biggest *)
intros g Hg Hgx.
apply Rnot_lt_le.
intros Hg3.
assert (Hg4 : (g < 0)%R).
now apply Rle_lt_trans with (1 := Hgx).
destruct (ln_beta beta g) as (ge, Hge).
simpl in Hg.
specialize (Hge (Rlt_not_eq g 0 Hg4)).
rewrite (Rabs_left _ Hg4) in Hge.
assert (Hge' : (ge <= fexp ex)%Z).
cut (ge - 1 < fexp ex)%Z. omega.
apply <- bpow_lt.
apply Rle_lt_trans with (1 := proj1 Hge).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
assert (Hcg: canonic_exponent g = fexp ex).
unfold canonic_exponent.
rewrite <- Rabs_left with (1 := Hg4) in Hge.
rewrite ln_beta_unique with (1 := Hge).
exact (proj2 (proj2 (prop_exp _) He1) _ Hge').
apply Rlt_not_le with (1 := proj2 Hge).
rewrite Hg.
unfold scaled_mantissa, F2R. simpl.
rewrite <- Ropp_mult_distr_l_reverse.
rewrite Hcg.
pattern (fexp ex) at 2 ; replace (fexp ex) with (fexp ex - ge + ge)%Z by ring.
rewrite bpow_add.
rewrite <- Rmult_assoc.
pattern (bpow ge) at 1 ; rewrite <- Rmult_1_l.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (- Z2R (Ztrunc (g * bpow (- fexp ex))) * bpow (fexp ex - ge) = Z2R (- Ztrunc (g * bpow (-fexp ex)) * Zpower (radix_val beta) (fexp ex - ge)))%R.
rewrite mult_Z2R.
rewrite Z2R_Zpower. 2: omega.
now rewrite opp_Z2R.
rewrite H.
apply (Z2R_le 1).
apply (Zlt_le_succ 0).
apply lt_Z2R.
rewrite <- H.
unfold Zminus.
rewrite bpow_add, <- Rmult_assoc.
apply Rmult_lt_0_compat.
rewrite <- Ropp_0.
rewrite Ropp_mult_distr_l_reverse.
apply Ropp_lt_contravar.
rewrite <- Hcg.
now rewrite Hg in Hg4.
apply bpow_gt_0.
Qed.

Theorem generic_format_satisfies_any :
  satisfies_any generic_format.
Proof.
split.
(* symmetric set *)
exact generic_format_0.
exact generic_format_opp.
(* rounding down *)
intros x.
exists (match Req_EM_T x 0 with
  | left Hx => R0
  | right Hx => F2R (Float beta (Zfloor (x * bpow (- canonic_exponent x))) (canonic_exponent x))
  end).
destruct (Req_EM_T x 0) as [Hx|Hx].
(* . *)
split.
apply generic_format_0.
rewrite Hx.
split.
apply Rle_refl.
now intros g _ H.
(* . *)
destruct (ln_beta beta x) as (ex, H1).
simpl.
specialize (H1 Hx).
destruct (Rdichotomy _ _ Hx) as [H2|H2].
now apply generic_DN_pt_neg.
now apply generic_DN_pt_pos.
Qed.

Theorem generic_DN_pt :
  forall x,
  Rnd_DN_pt generic_format x (F2R (Float beta (Zfloor (x * bpow (- canonic_exponent x))) (canonic_exponent x))).
Proof.
intros x.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].
now apply generic_DN_pt_pos.
rewrite <- Hx, Rmult_0_l.
fold (Z2R 0).
rewrite Zfloor_Z2R, F2R_0.
apply Rnd_DN_pt_refl.
apply generic_format_0.
now apply generic_DN_pt_neg.
Qed.

Theorem generic_UP_pt :
  forall x,
  Rnd_UP_pt generic_format x (F2R (Float beta (Zceil (x * bpow (- canonic_exponent x))) (canonic_exponent x))).
Proof.
intros x.
apply Rnd_DN_UP_pt_sym.
apply generic_format_satisfies_any.
unfold Zceil.
rewrite <- Ropp_mult_distr_l_reverse.
rewrite opp_F2R, Zopp_involutive.
rewrite <- canonic_exponent_opp.
apply generic_DN_pt.
Qed.

Theorem generic_DN_pt_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Rnd_DN_pt generic_format x R0.
Proof.
intros x ex Hx He.
rewrite <- (F2R_0 beta (canonic_exponent x)).
rewrite <- mantissa_DN_small_pos with (1 := Hx) (2 := He).
rewrite <- canonic_exponent_fexp_pos with (1 := Hx).
apply generic_DN_pt.
Qed.

Theorem generic_UP_pt_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Rnd_UP_pt generic_format x (bpow (fexp ex)).
Proof.
intros x ex Hx He.
rewrite <- F2R_bpow.
rewrite <- mantissa_UP_small_pos with (1 := Hx) (2 := He).
rewrite <- canonic_exponent_fexp_pos with (1 := Hx).
apply generic_UP_pt.
Qed.

Theorem generic_UP_pt_large_pos_le_pow :
  forall x xu ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (fexp ex < ex)%Z ->
  Rnd_UP_pt generic_format x xu ->
  (xu <= bpow ex)%R.
Proof.
intros x xu ex Hx He (_, (_, Hu4)).
apply Hu4 with (2 := Rlt_le _ _ (proj2 Hx)).
apply generic_format_bpow.
exact (proj1 (prop_exp _) He).
Qed.

Theorem generic_format_EM :
  forall x,
  generic_format x \/ ~generic_format x.
Proof.
intros x.
destruct (proj1 (satisfies_any_imp_DN _ generic_format_satisfies_any) x) as (d, Hd).
destruct (Rle_lt_or_eq_dec d x) as [Hxd|Hxd].
apply Hd.
right.
intros Fx.
apply Rlt_not_le with (1 := Hxd).
apply Req_le.
apply sym_eq.
now apply Rnd_DN_pt_idempotent with (1 := Hd).
left.
rewrite <- Hxd.
apply Hd.
Qed.

Theorem generic_DN_pt_large_pos_ge_pow :
  forall x d e,
  (0 < d)%R ->
  Rnd_DN_pt generic_format x d ->
  (bpow e <= x)%R ->
  (bpow e <= d)%R.
Proof.
intros x d e Hd Hxd Hex.
destruct (ln_beta beta x) as (ex, He).
assert (Hx: (0 < x)%R).
apply Rlt_le_trans with (1 := Hd).
apply Hxd.
specialize (He (Rgt_not_eq _ _ Hx)).
rewrite Rabs_pos_eq in He. 2: now apply Rlt_le.
apply Rle_trans with (bpow (ex - 1)).
apply -> bpow_le.
cut (e < ex)%Z. omega.
apply <- bpow_lt.
now apply Rle_lt_trans with (2 := proj2 He).
apply Hxd with (2 := proj1 He).
apply generic_format_bpow.
destruct (Zle_or_lt ex (fexp ex)).
elim Rgt_not_eq with (1 := Hd).
apply Rnd_DN_pt_unicity with (1 := Hxd).
now apply generic_DN_pt_small_pos with (1 := He).
ring_simplify (ex - 1 + 1)%Z.
omega.
Qed.

Theorem canonic_exponent_DN_pt :
  forall x d : R,
  (0 < d)%R ->
  Rnd_DN_pt generic_format x d ->
  canonic_exponent d = canonic_exponent x.
Proof.
intros x d Hd Hxd.
unfold canonic_exponent.
apply f_equal.
apply ln_beta_unique.
rewrite (Rabs_pos_eq d). 2: now apply Rlt_le.
destruct (ln_beta beta x) as (ex, He).
simpl.
assert (Hx: (0 < x)%R).
apply Rlt_le_trans with (1 := Hd).
apply Hxd.
specialize (He (Rgt_not_eq _ _ Hx)).
rewrite Rabs_pos_eq in He. 2: now apply Rlt_le.
split.
now apply generic_DN_pt_large_pos_ge_pow with (2 := Hxd).
apply Rle_lt_trans with (2 := proj2 He).
apply Hxd.
Qed.

End RND_generic.

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

Record Zrounding := mkZrounding {
  Zrnd : R -> Z ;
  Zrnd_monotone : forall x y, (x <= y)%R -> (Zrnd x <= Zrnd y)%Z ;
  Zrnd_Z2R : forall n, Zrnd (Z2R n) = n
}.

Variable rnd : Zrounding.
Let Zrnd := Zrnd rnd.
Let Zrnd_monotone := Zrnd_monotone rnd.
Let Zrnd_Z2R := Zrnd_Z2R rnd.

Theorem Zrnd_DN_or_UP :
  forall x, Zrnd x = Zfloor x \/ Zrnd x = Zceil x.
Proof.
intros x.
destruct (Zle_or_lt (Zrnd x) (Zfloor x)) as [Hx|Hx].
left.
apply Zle_antisym with (1 := Hx).
rewrite <- (Zrnd_Z2R (Zfloor x)).
apply Zrnd_monotone.
apply Zfloor_lb.
right.
apply Zle_antisym.
rewrite <- (Zrnd_Z2R (Zceil x)).
apply Zrnd_monotone.
apply Zceil_ub.
rewrite Zceil_floor_neq.
omega.
intros H.
rewrite <- H in Hx.
rewrite Zfloor_Z2R, Zrnd_Z2R in Hx.
apply Zlt_irrefl with (1 := Hx).
Qed.

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

Theorem rounding_bounded_large_pos :
  forall x ex,
  (fexp ex < ex)%Z ->
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (bpow (ex - 1) <= rounding x <= bpow ex)%R.
Proof.
intros x ex He Hx.
unfold rounding, scaled_mantissa.
rewrite (canonic_exponent_fexp_pos _ _ Hx).
unfold F2R. simpl.
destruct (Zrnd_DN_or_UP (x * bpow (- fexp ex))) as [Hr|Hr] ; rewrite Hr.
(* DN *)
split.
replace (ex - 1)%Z with (ex - 1 + - fexp ex + fexp ex)%Z by ring.
rewrite bpow_add.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (Hf: Z2R (Zpower (radix_val beta) (ex - 1 - fexp ex)) = bpow (ex - 1 + - fexp ex)).
apply Z2R_Zpower.
omega.
rewrite <- Hf.
apply Z2R_le.
apply Zfloor_lub.
rewrite Hf.
rewrite bpow_add.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Hx.
apply Rle_trans with (2 := Rlt_le _ _ (proj2 Hx)).
apply Rmult_le_reg_r with (bpow (- fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_r, Rmult_1_r.
apply Zfloor_lb.
(* UP *)
split.
apply Rle_trans with (1 := proj1 Hx).
apply Rmult_le_reg_r with (bpow (- fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_r, Rmult_1_r.
apply Zceil_ub.
pattern ex at 3 ; replace ex with (ex - fexp ex + fexp ex)%Z by ring.
rewrite bpow_add.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (Hf: Z2R (Zpower (radix_val beta) (ex - fexp ex)) = bpow (ex - fexp ex)).
apply Z2R_Zpower.
omega.
rewrite <- Hf.
apply Z2R_le.
apply Zceil_glb.
rewrite Hf.
unfold Zminus.
rewrite bpow_add.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rlt_le.
apply Hx.
Qed.

Theorem rounding_bounded_small_pos :
  forall x ex,
  (ex <= fexp ex)%Z ->
  (bpow (ex - 1) <= x < bpow ex)%R ->
  rounding x = R0 \/ rounding x = bpow (fexp ex).
Proof.
intros x ex He Hx.
unfold rounding, scaled_mantissa.
rewrite (canonic_exponent_fexp_pos _ _ Hx).
unfold F2R. simpl.
destruct (Zrnd_DN_or_UP (x * bpow (-fexp ex))) as [Hr|Hr] ; rewrite Hr.
(* DN *)
left.
apply Rmult_eq_0_compat_r.
apply (@f_equal _ _ Z2R _ Z0).
apply Zfloor_imp.
refine (let H := _ in conj (Rlt_le _ _ (proj1 H)) (proj2 H)).
now apply mantissa_small_pos.
(* UP *)
right.
pattern (bpow (fexp ex)) at 2 ; rewrite <- Rmult_1_l.
apply (f_equal (fun m => (m * bpow (fexp ex))%R)).
apply (@f_equal _ _ Z2R _ 1%Z).
apply Zceil_imp.
refine (let H := _ in conj (proj1 H) (Rlt_le _ _ (proj2 H))).
now apply mantissa_small_pos.
Qed.

Theorem generic_format_rounding_pos :
  forall x,
  (0 < x)%R ->
  generic_format (rounding x).
Proof.
intros x Hx0.
destruct (ln_beta beta x) as (ex, Hex).
specialize (Hex (Rgt_not_eq _ _ Hx0)).
rewrite Rabs_pos_eq in Hex. 2: now apply Rlt_le.
destruct (Zle_or_lt ex (fexp ex)) as [He|He].
(* small *)
destruct (rounding_bounded_small_pos _ _ He Hex) as [Hr|Hr] ; rewrite Hr.
apply generic_format_0.
apply generic_format_bpow.
now apply (proj2 (prop_exp ex)).
(* large *)
generalize (rounding_bounded_large_pos _ _ He Hex).
intros (Hr1, Hr2).
destruct (Rle_or_lt (bpow ex) (rounding x)) as [Hr|Hr].
rewrite <- (Rle_antisym _ _ Hr Hr2).
apply generic_format_bpow.
now apply (proj1 (prop_exp ex)).
assert (Hr' := conj Hr1 Hr).
unfold generic_format, scaled_mantissa.
rewrite (canonic_exponent_fexp_pos _ _ Hr').
unfold rounding, scaled_mantissa.
rewrite (canonic_exponent_fexp_pos _ _ Hex).
unfold F2R at 3. simpl.
rewrite Rmult_assoc, <- bpow_add, Zplus_opp_r, Rmult_1_r.
now rewrite Ztrunc_Z2R.
Qed.

End Fcore_generic_rounding_pos.

Definition ZrndDN := mkZrounding Zfloor Zfloor_le Zfloor_Z2R.
Definition ZrndUP := mkZrounding Zceil Zceil_le Zceil_Z2R.

Theorem rounding_DN_or_UP :
  forall rnd x,
  rounding rnd x = rounding ZrndDN x \/ rounding rnd x = rounding ZrndUP x.
Proof.
intros rnd x.
unfold rounding.
unfold Zrnd at 2 4. simpl.
destruct (Zrnd_DN_or_UP rnd (scaled_mantissa x)) as [Hx|Hx].
left. now rewrite Hx.
right. now rewrite Hx.
Qed.

Theorem rounding_monotone :
  forall rnd x y, (x <= y)%R -> (rounding rnd x <= rounding rnd y)%R.
Proof.
intros rnd x y Hxy.
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
assert (Hrnd_monotone : forall x y, (x <= y)%R -> (- Zrnd rnd (-x) <= - Zrnd rnd (-y))%Z).
clear.
intros x y Hxy.
apply Zopp_le_cancel.
rewrite 2!Zopp_involutive.
apply Zrnd_monotone.
now apply Ropp_le_contravar.
assert (Hrnd_Z2R : forall n, (- Zrnd rnd (- Z2R n))%Z = n).
intros n.
rewrite <- opp_Z2R, Zrnd_Z2R.
apply Zopp_involutive.
apply (rounding_monotone_pos (mkZrounding (fun m => (- Zrnd rnd (- m))%Z) Hrnd_monotone Hrnd_Z2R)).
rewrite <- Ropp_0.
now apply Ropp_lt_contravar.
now apply Ropp_le_contravar.
(* . 0 <= y *)
apply Rle_trans with R0.
apply F2R_le_0_compat. simpl.
rewrite <- (Zrnd_Z2R rnd 0).
apply Zrnd_monotone.
simpl.
rewrite <- (Rmult_0_l (bpow (- fexp (projT1 (ln_beta beta x))))).
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply Rlt_le.
apply F2R_ge_0_compat. simpl.
rewrite <- (Zrnd_Z2R rnd 0).
apply Zrnd_monotone.
apply Rmult_le_pos.
exact Hy.
apply bpow_ge_0.
(* x = 0 *)
rewrite Hx.
rewrite rounding_0.
apply F2R_ge_0_compat.
simpl.
rewrite <- (Zrnd_Z2R rnd 0).
apply Zrnd_monotone.
apply Rmult_le_pos.
now rewrite <- Hx.
apply bpow_ge_0.
Qed.

Theorem rounding_DN_opp :
  forall x,
  rounding ZrndDN (-x) = (- rounding ZrndUP x)%R.
Proof.
intros x.
unfold rounding.
rewrite scaled_mantissa_opp.
rewrite opp_F2R.
unfold Zrnd. simpl.
unfold Zceil.
rewrite Zopp_involutive.
now rewrite canonic_exponent_opp.
Qed.

Theorem rounding_UP_opp :
  forall x,
  rounding ZrndUP (-x) = (- rounding ZrndDN x)%R.
Proof.
intros x.
unfold rounding.
rewrite scaled_mantissa_opp.
rewrite opp_F2R.
unfold Zrnd. simpl.
unfold Zceil.
rewrite Ropp_involutive.
now rewrite canonic_exponent_opp.
Qed.

Theorem generic_format_rounding :
  forall Zrnd x,
  generic_format (rounding Zrnd x).
Proof.
intros rnd x.
destruct (total_order_T x 0) as [[Hx|Hx]|Hx].
rewrite <- (Ropp_involutive x).
destruct (rounding_DN_or_UP rnd (- - x)) as [Hr|Hr] ; rewrite Hr.
rewrite rounding_DN_opp.
apply generic_format_opp.
apply generic_format_rounding_pos.
now apply Ropp_0_gt_lt_contravar.
rewrite rounding_UP_opp.
apply generic_format_opp.
apply generic_format_rounding_pos.
now apply Ropp_0_gt_lt_contravar.
rewrite Hx.
rewrite rounding_0.
apply generic_format_0.
now apply generic_format_rounding_pos.
Qed.

Theorem generic_DN_pt :
  forall x,
  Rnd_DN_pt generic_format x (rounding ZrndDN x).
Proof.
intros x.
split.
apply generic_format_rounding.
split.
pattern x at 2 ; rewrite <- scaled_mantissa_bpow.
unfold rounding, F2R. simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Zfloor_lb.
intros g Hg Hgx.
rewrite <- (rounding_generic ZrndDN _ Hg).
now apply rounding_monotone.
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
exists (rounding ZrndDN x).
apply generic_DN_pt.
Qed.

Theorem generic_UP_pt :
  forall x,
  Rnd_UP_pt generic_format x (rounding ZrndUP x).
Proof.
intros x.
apply Rnd_DN_UP_pt_sym.
apply generic_format_satisfies_any.
rewrite <- rounding_DN_opp.
apply generic_DN_pt.
Qed.

Theorem rounding_DN_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  rounding ZrndDN x = R0.
Proof.
intros x ex Hx He.
rewrite <- (F2R_0 beta (canonic_exponent x)).
rewrite <- mantissa_DN_small_pos with (1 := Hx) (2 := He).
now rewrite <- canonic_exponent_fexp_pos with (1 := Hx).
Qed.

Theorem rounding_UP_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  rounding ZrndUP x = (bpow (fexp ex)).
Proof.
intros x ex Hx He.
rewrite <- F2R_bpow.
rewrite <- mantissa_UP_small_pos with (1 := Hx) (2 := He).
now rewrite <- canonic_exponent_fexp_pos with (1 := Hx).
Qed.

Theorem generic_format_EM :
  forall x,
  generic_format x \/ ~generic_format x.
Proof.
intros x.
destruct (Req_dec (rounding ZrndDN x) x) as [Hx|Hx].
left.
rewrite <- Hx.
apply generic_format_rounding.
right.
intros H.
apply Hx.
now apply rounding_generic.
Qed.

Theorem rounding_large_pos_ge_pow :
  forall rnd x e,
  (0 < rounding rnd x)%R ->
  (bpow e <= x)%R ->
  (bpow e <= rounding rnd x)%R.
Proof.
intros rnd x e Hd Hex.
destruct (ln_beta beta x) as (ex, He).
assert (Hx: (0 < x)%R).
apply Rlt_le_trans with (2 := Hex).
apply bpow_gt_0.
specialize (He (Rgt_not_eq _ _ Hx)).
rewrite Rabs_pos_eq in He. 2: now apply Rlt_le.
apply Rle_trans with (bpow (ex - 1)).
apply -> bpow_le.
cut (e < ex)%Z. omega.
apply <- bpow_lt.
now apply Rle_lt_trans with (2 := proj2 He).
destruct (Zle_or_lt ex (fexp ex)).
destruct (rounding_bounded_small_pos rnd x ex H He) as [Hr|Hr].
rewrite Hr in Hd.
elim Rlt_irrefl with (1 := Hd).
rewrite Hr.
apply -> bpow_le.
omega.
apply (rounding_bounded_large_pos rnd x ex H He).
Qed.

Theorem canonic_exponent_DN :
  forall x,
  (0 < rounding ZrndDN x)%R ->
  canonic_exponent (rounding ZrndDN x) = canonic_exponent x.
Proof.
intros x Hd.
unfold canonic_exponent.
apply f_equal.
apply ln_beta_unique.
rewrite (Rabs_pos_eq (rounding ZrndDN x)). 2: now apply Rlt_le.
destruct (ln_beta beta x) as (ex, He).
simpl.
assert (Hx: (0 < x)%R).
apply Rlt_le_trans with (1 := Hd).
apply (generic_DN_pt x).
specialize (He (Rgt_not_eq _ _ Hx)).
rewrite Rabs_pos_eq in He. 2: now apply Rlt_le.
split.
apply rounding_large_pos_ge_pow with (1 := Hd).
apply He.
apply Rle_lt_trans with (2 := proj2 He).
apply (generic_DN_pt x).
Qed.

Theorem generic_N_pt_DN_or_UP :
  forall x f,
  Rnd_N_pt generic_format x f ->
  f = rounding ZrndDN x \/ f = rounding ZrndUP x.
Proof.
intros x f Hxf.
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf).
left.
apply Rnd_DN_pt_unicity with (1 := H).
apply generic_DN_pt.
right.
apply Rnd_UP_pt_unicity with (1 := H).
apply generic_UP_pt.
Qed.

End RND_generic.

Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_float_prop.

Section Fcore_ulp.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Variable prop_exp : valid_exp fexp.

Definition ulp x := bpow (canonic_exponent beta fexp x).

Definition F := generic_format beta fexp.

Theorem ulp_DN_UP_pt :
  forall x xd,
  ~ F x ->
  Rnd_DN_pt F x xd ->
  Rnd_UP_pt F x (xd + ulp x)%R.
Proof.
intros x xd Fx Hd1.
set (ex := canonic_exponent beta fexp x).
assert (Hd2 := generic_DN_pt beta _ prop_exp x).
generalize (generic_UP_pt beta _ prop_exp x).
fold ex in Hd2 |- *.
replace (F2R (Float beta (Zceil (x * bpow (- ex))) ex)) with (xd + ulp x)%R.
easy.
rewrite (Rnd_DN_pt_unicity _ _ _ _ Hd1 Hd2).
unfold ulp. fold ex.
unfold F2R. simpl.
rewrite Zceil_floor_neq.
rewrite plus_Z2R. simpl.
ring.
intros H.
apply Fx.
unfold F, generic_format.
unfold F2R. simpl.
unfold scaled_mantissa.
fold ex.
rewrite <- H.
rewrite Ztrunc_Z2R.
rewrite H.
now rewrite Rmult_assoc, <- bpow_add, Zplus_opp_l, Rmult_1_r.
Qed.

Theorem ulp_error :
  forall rnd : R -> R,
  Rounding_for_Format F rnd ->
  forall x,
  (Rabs (rnd x - x) < ulp x)%R.
Proof.
intros rnd Hrnd x.
assert (Hs := generic_format_satisfies_any beta _ prop_exp).
destruct (proj1 (satisfies_any_imp_DN F Hs) x) as (d, Hd).
destruct (Rle_lt_or_eq_dec d x) as [Hxd|Hxd].
(* x <> rnd x *)
apply Hd.
assert (Fx : ~F x).
intros Fx.
apply Rlt_not_le with (1 := Hxd).
apply Req_le.
apply sym_eq.
now apply Rnd_DN_pt_idempotent with (1 := Hd).
assert (Hu := ulp_DN_UP_pt _ _ Fx Hd).
set (u := (d + ulp x)%R).
assert (Hxu : (x < u)%R).
destruct (Rle_lt_or_eq_dec x u) as [Hxu|Hxu].
apply Hu.
exact Hxu.
elim Fx.
rewrite Hxu.
apply Hu.
destruct (Rnd_DN_or_UP_pt _ _ Hrnd _ _ _ Hd Hu) as [Hr|Hr] ;
  rewrite Hr ; clear Hr.
rewrite <- Ropp_minus_distr.
rewrite Rabs_Ropp, Rabs_pos_eq.
apply Rplus_lt_reg_r with d.
now replace (d + (x - d))%R with x by ring.
apply Rle_0_minus.
apply Hd.
rewrite Rabs_pos_eq.
apply Rplus_lt_reg_r with (x - ulp x)%R.
now ring_simplify.
apply Rle_0_minus.
apply Hu.
(* x = rnd x *)
rewrite Hxd in Hd.
rewrite (proj2 (proj2 Hrnd)).
unfold Rminus.
rewrite Rplus_opp_r.
rewrite Rabs_R0.
apply bpow_gt_0.
apply Hd.
Qed.

Theorem ulp_half_error_pt :
  forall x xr,
  Rnd_N_pt F x xr ->
  (Rabs (xr - x) <= /2 * ulp x)%R.
Proof.
intros x xr Hxr.
assert (Hs := generic_format_satisfies_any beta _ prop_exp).
destruct (proj1 (satisfies_any_imp_DN F Hs) x) as (d, Hd).
destruct (Rle_lt_or_eq_dec d x) as [Hxd|Hxd].
(* x <> rnd x *)
apply Hd.
assert (Fx : ~F x).
intros Fx.
apply Rlt_not_le with (1 := Hxd).
apply Req_le.
apply sym_eq.
now apply Rnd_DN_pt_idempotent with (1 := Hd).
assert (Hu := ulp_DN_UP_pt _ _ Fx Hd).
destruct Hxr as (Hr1, Hr2).
assert (Hdx : (Rabs (d - x) = x - d)%R).
rewrite <- Ropp_minus_distr.
rewrite Rabs_Ropp.
apply Rabs_pos_eq.
apply Rle_0_minus.
apply Hd.
assert (Hux : (Rabs (d + ulp x - x) = d + ulp x - x)%R).
apply Rabs_pos_eq.
apply Rle_0_minus.
apply Hu.
destruct (Rle_or_lt (x - d) (d + ulp x - x)) as [H|H].
(* . rnd(x) = rndd(x) *)
apply Rle_trans with (1 := Hr2 _ (proj1 Hd)).
rewrite Hdx.
apply Rmult_le_reg_l with 2%R.
now apply (Z2R_lt 0 2).
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
apply Rle_trans with (1 := Rplus_le_compat_l (x - d) _ _ H).
field_simplify.
apply Rle_refl.
(* . rnd(x) = rndu(x) *)
apply Rle_trans with (1 := Hr2 _ (proj1 Hu)).
rewrite Hux.
apply Rmult_le_reg_l with 2%R.
now apply (Z2R_lt 0 2).
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
apply Rlt_le.
apply Rlt_le_trans with (1 := Rplus_lt_compat_l (d + ulp x - x) _ _ H).
field_simplify.
apply Rle_refl.
(* x = rnd x *)
rewrite Hxd in Hd.
rewrite Rnd_N_pt_idempotent with (1 := Hxr).
unfold Rminus.
rewrite Rplus_opp_r.
rewrite Rabs_R0.
apply Rmult_le_pos.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
apply bpow_ge_0.
apply Hd.
Qed.

Theorem ulp_monotone :
  ( forall m n, (m <= n)%Z -> (fexp m <= fexp n)%Z ) ->
  forall x y: R,
  (0 < x)%R -> (x <= y)%R ->
  (ulp x <= ulp y)%R.
Proof.
intros Hm x y Hx Hxy.
apply -> bpow_le.
apply Hm.
now apply ln_beta_monotone.
Qed.

Theorem ulp_bpow :
  forall e, ulp (bpow e) = bpow (fexp (e + 1)).
intros e.
unfold ulp.
apply f_equal.
apply canonic_exponent_fexp.
rewrite Rabs_pos_eq.
split.
ring_simplify (e + 1 - 1)%Z.
apply Rle_refl.
apply -> bpow_lt.
apply Zlt_succ.
apply bpow_ge_0.
Qed.

Theorem ulp_DN_pt_eq :
  forall x d : R,
  (0 < d)%R ->
  Rnd_DN_pt F x d ->
  ulp d = ulp x.
Proof.
intros x d Hd Hxd.
unfold ulp.
now rewrite canonic_exponent_DN_pt with (3 := Hxd).
Qed.

End Fcore_ulp.

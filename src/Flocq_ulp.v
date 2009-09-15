Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_prop.
Require Import Flocq_rnd_generic.
Require Import Flocq_float_prop.

Section Flocq_ulp.

Variable beta : radix.

Notation bpow e := (epow beta e).

Variable fexp : Z -> Z.

Variable prop_exp : valid_exp fexp.

Definition ulp x := F2R (Float beta 1 (fexp (projT1 (ln_beta beta (Rabs x))))).

Definition F := generic_format beta fexp.

Theorem ulp_pred_succ_pt_pos :
  forall x xd xu,
  Rlt 0 x -> ~ F x ->
  Rnd_DN_pt F x xd -> Rnd_UP_pt F x xu ->
  (xu = xd + ulp x)%R.
Proof.
intros x xd xu Hx1 Fx Hd1 Hu1.
unfold ulp.
rewrite Rabs_pos_eq.
destruct (ln_beta beta x) as (ex, Hx2).
simpl.
specialize (Hx2 Hx1).
destruct (Z_lt_le_dec (fexp ex) ex) as [He1|He1].
(* positive big *)
assert (Hd2 := generic_DN_pt_pos _ _ prop_exp _ _ Hx2).
assert (Hu2 := generic_UP_pt_pos _ _ prop_exp _ _ Hx2).
rewrite (Rnd_DN_pt_unicity _ _ _ _ Hd1 Hd2).
rewrite (Rnd_UP_pt_unicity _ _ _ _ Hu1 Hu2).
unfold F2R. simpl.
rewrite <- Rmult_plus_distr_r.
change R1 with (Z2R 1).
rewrite <- plus_Z2R.
apply (f_equal (fun v => (Z2R v * bpow (fexp ex))%R)).
apply Zceil_floor_neq.
intros Hx4.
assert (Hx5 : x = F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex))).
unfold F2R. simpl.
rewrite Hx4.
rewrite Rmult_assoc.
rewrite <- epow_add.
rewrite Zplus_opp_l.
now rewrite Rmult_1_r.
apply Fx.
rewrite Hx5.
apply Hd2.
(* positive small *)
rewrite Rnd_UP_pt_unicity with F x xu (bpow (fexp ex)).
rewrite Rnd_DN_pt_unicity with F x xd R0.
rewrite Rplus_0_l.
unfold F2R. simpl.
now rewrite Rmult_1_l.
exact Hd1.
now apply generic_DN_pt_small_pos with ex.
exact Hu1.
now apply generic_UP_pt_small_pos.
(* . *)
now apply Rlt_le.
Qed.

Theorem ulp_pred_succ_pt :
  forall x xd xu,
  ~ F x ->
  Rnd_DN_pt F x xd -> Rnd_UP_pt F x xu ->
  (xu = xd + ulp x)%R.
Proof.
intros x xd xu Fx Hd1 Hu1.
destruct (Rdichotomy x 0) as [Hx2|Hx2].
(* zero *)
intros Hx.
elim Fx.
rewrite Hx.
exists (Float beta 0 _) ; repeat split.
unfold F2R. simpl.
now rewrite Rmult_0_l.
(* negative *)
assert (Hu2 : Rnd_DN_pt F (-x) (-xu)).
apply Rnd_UP_DN_pt_sym.
now eapply generic_format_satisfies_any.
now rewrite 2!Ropp_involutive.
assert (Hd2 : Rnd_UP_pt F (-x) (-xd)).
apply Rnd_DN_UP_pt_sym.
now eapply generic_format_satisfies_any.
now rewrite 2!Ropp_involutive.
rewrite <- (Ropp_involutive xd).
rewrite ulp_pred_succ_pt_pos with (3 := Hu2) (4 := Hd2).
unfold ulp.
rewrite Rabs_Ropp.
ring.
rewrite <- Ropp_0.
now apply Ropp_lt_contravar.
intros ((xm, xe), (H1, H2)).
apply Fx.
exists (Float beta (-xm) xe).
split.
rewrite <- opp_F2R.
rewrite <- H1.
now rewrite Ropp_involutive.
now rewrite <- Rabs_Ropp.
(* positive *)
now apply ulp_pred_succ_pt_pos.
Qed.

Theorem ulp_error :
  forall rnd : R -> R,
  Rounding_for_Format F rnd ->
  forall x,
  (Rabs (rnd x - x) < ulp x)%R.
Proof.
intros rnd Hrnd x.
assert (Hs := generic_format_satisfies_any beta _ prop_exp).
destruct (satisfies_any_imp_DN F Hs) as (rndd, Hd).
specialize (Hd x).
destruct (Rle_lt_or_eq_dec (rndd x) x) as [Hxd|Hxd].
(* x <> rnd x *)
apply Hd.
assert (Fx : ~F x).
intros Fx.
apply Rlt_not_le with (1 := Hxd).
apply Req_le.
apply sym_eq.
now apply Rnd_DN_pt_idempotent with (1 := Hd).
destruct (satisfies_any_imp_UP F Hs) as (rndu, Hu).
specialize (Hu x).
assert (Hxu : (x < rndu x)%R).
apply Rnot_le_lt.
intros Hxu.
apply Fx.
rewrite Rle_antisym with (2 := Hxu).
apply Hu.
apply Hu.
rewrite (ulp_pred_succ_pt _ _ _ Fx Hd Hu) in Hxu, Hu.
destruct (Rnd_DN_or_UP_pt _ _ Hrnd _ _ _ Hd Hu) as [Hr|Hr] ;
  rewrite Hr ; clear Hr.
rewrite <- Ropp_minus_distr.
rewrite Rabs_Ropp, Rabs_pos_eq.
apply Rplus_lt_reg_r with (rndd x).
now replace (rndd x + (x - rndd x))%R with x by ring.
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
unfold ulp, F2R. simpl.
rewrite Rmult_1_l.
apply epow_gt_0.
apply Hd.
Qed.

Theorem ulp_half_error_pt :
  forall x xr,
  Rnd_N_pt F x xr ->
  (Rabs (xr - x) <= /2 * ulp x)%R.
Proof.
intros x xr Hxr.
assert (Hs := generic_format_satisfies_any beta _ prop_exp).
destruct (satisfies_any_imp_DN F Hs) as (rndd, Hd).
specialize (Hd x).
destruct (Rle_lt_or_eq_dec (rndd x) x) as [Hxd|Hxd].
(* x <> rnd x *)
apply Hd.
assert (Fx : ~F x).
intros Fx.
apply Rlt_not_le with (1 := Hxd).
apply Req_le.
apply sym_eq.
now apply Rnd_DN_pt_idempotent with (1 := Hd).
destruct (satisfies_any_imp_UP F Hs) as (rndu, Hu).
specialize (Hu x).
rewrite (ulp_pred_succ_pt _ _ _ Fx Hd Hu) in Hu.
destruct Hxr as (Hr1, Hr2).
assert (Hdx : (Rabs (rndd x - x) = x - rndd x)%R).
rewrite <- Ropp_minus_distr.
rewrite Rabs_Ropp.
apply Rabs_pos_eq.
apply Rle_0_minus.
apply Hd.
assert (Hux : (Rabs (rndd x + ulp x - x) = rndd x + ulp x - x)%R).
apply Rabs_pos_eq.
apply Rle_0_minus.
apply Hu.
destruct (Rle_or_lt (x - rndd x) (rndd x + ulp x - x)) as [H|H].
(* . rnd(x) = rndd(x) *)
apply Rle_trans with (1 := Hr2 _ (proj1 Hd)).
rewrite Hdx.
apply Rmult_le_reg_l with 2%R.
now apply (Z2R_lt 0 2).
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
apply Rle_trans with (1 := Rplus_le_compat_l (x - rndd x) _ _ H).
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
apply Rlt_le_trans with (1 := Rplus_lt_compat_l (rndd x + ulp x - x) _ _ H).
field_simplify.
apply Rle_refl.
(* x = rnd x *)
rewrite Hxd in Hd.
rewrite Rnd_N_pt_idempotent with (1 := Hxr).
unfold Rminus.
rewrite Rplus_opp_r.
rewrite Rabs_R0.
unfold ulp, F2R. simpl.
rewrite Rmult_1_l.
apply Rmult_le_pos.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
apply epow_ge_0.
apply Hd.
Qed.

Theorem ulp_monotone :
  ( forall m n, (m <= n)%Z -> (fexp m <= fexp n)%Z ) ->
  forall x y: R,
  (0 < x)%R -> (x <= y)%R ->
  (ulp x <= ulp y)%R.
Proof.
intros Hm x y Hx Hxy.
unfold ulp.
unfold F2R. simpl.
rewrite 2!Rmult_1_l.
apply -> epow_le.
apply Hm.
rewrite 2!Rabs_pos_eq ; try apply Rlt_le ; trivial.
now apply ln_beta_monotone.
now apply Rlt_le_trans with x.
Qed.

Theorem ulp_epow :
  forall e, ulp (bpow e) = bpow (fexp (e + 1)).
intros e.
unfold ulp.
rewrite (ln_beta_unique beta (Rabs (bpow e)) (e + 1)).
unfold F2R.
now rewrite Rmult_1_l.
rewrite Rabs_pos_eq.
split.
apply -> epow_le.
omega.
apply -> epow_lt.
omega.
apply epow_ge_0.
Qed.

End Flocq_ulp.

Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_prop.
Require Import Flocq_rnd_generic.
Require Import Flocq_float_prop.

Section Flocq_ulp.

Variable beta : radix.

Notation bpow := (epow beta).

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
assert (Hu2 : Rnd_DN_pt F (-x) (-xu)).
apply Rnd_UP_DN_pt_sym.
now eapply generic_format_satisfies_any.
now rewrite 2!Ropp_involutive.
assert (Hx3 : (bpow (ex - 1)%Z <= --x < bpow ex)%R).
now rewrite Ropp_involutive.
assert (Hu3 := generic_DN_pt_neg _ _ prop_exp _ _ Hx3).
rewrite (Rnd_DN_pt_unicity _ _ _ _ Hd1 Hd2).
rewrite <- (Ropp_involutive xu).
rewrite (Rnd_DN_pt_unicity _ _ _ _ Hu2 Hu3).
unfold F2R. simpl.
rewrite <- Rmult_plus_distr_r.
rewrite <- Ropp_mult_distr_l_reverse.
apply (f_equal (fun v => v * bpow (fexp ex))%R).
rewrite <- opp_Z2R.
change R1 with (Z2R 1).
rewrite <- plus_Z2R.
apply f_equal.
rewrite Ropp_mult_distr_l_reverse.
apply Zceil_floor_neq.
intros Hx4.
assert (Hx5 : x = F2R (Float beta (Zfloor (x * bpow (- fexp ex)%Z)) (fexp ex))).
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
(* x = rnd x *)
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
(* x <> rnd x *)
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

End Flocq_ulp.

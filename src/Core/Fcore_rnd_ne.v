Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_float_prop.
Require Import Fcore_ulp.

Section Fcore_rnd_NE.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Variable prop_exp : valid_exp fexp.

Notation format := (generic_format beta fexp).
Notation canonic := (canonic beta fexp).

Definition NE_prop (_ : R) f :=
  exists g : float beta, canonic f g /\ Zeven (Fnum g).

Definition Rnd_NE_pt :=
  Rnd_NG_pt format NE_prop.

Definition DN_UP_parity_pos_prop :=
  forall x xd xu cd cu,
  (0 < x)%R ->
  ~ format x ->
  canonic xd cd ->
  canonic xu cu ->
  Rnd_DN_pt format x xd ->
  Rnd_UP_pt format x xu ->
  Zodd (Fnum cd + Fnum cu).

Definition DN_UP_parity_prop :=
  forall x xd xu cd cu,
  ~ format x ->
  canonic xd cd ->
  canonic xu cu ->
  Rnd_DN_pt format x xd ->
  Rnd_UP_pt format x xu ->
  Zodd (Fnum cd + Fnum cu).

Theorem DN_UP_parity_aux :
  DN_UP_parity_pos_prop ->
  DN_UP_parity_prop.
Proof.
intros Hpos x xd xu cd cu Hfx Hd Hu Hxd Hxu.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].
(* . *)
exact (Hpos x xd xu cd cu Hx Hfx Hd Hu Hxd Hxu).
elim Hfx.
rewrite <- Hx.
apply generic_format_0.
(* . *)
assert (Hx': (0 < -x)%R).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive, Ropp_0.
destruct cd as (md, ed).
destruct cu as (mu, eu).
replace (Fnum (Float beta md ed) + Fnum (Float beta mu eu))%Z
  with (-1 * ((Fnum (Float beta (-mu) ed) + Fnum (Float beta (-md) eu))))%Z
  by (unfold Fnum ; ring).
apply Zodd_mult_Zodd.
now apply (Zodd_pred 0).
apply (Hpos (-x)%R (-xu)%R (-xd)%R (Float beta (-mu) eu) (Float beta (-md) ed)).
exact Hx'.
intros H.
apply Hfx.
rewrite <- (Ropp_involutive x).
now apply generic_format_sym.
now apply canonic_sym.
now apply canonic_sym.
apply Rnd_UP_DN_pt_sym.
apply generic_format_sym.
now rewrite 2!Ropp_involutive.
apply Rnd_DN_UP_pt_sym.
apply generic_format_sym.
now rewrite 2!Ropp_involutive.
Qed.

Hypothesis valid_fexp : valid_exp fexp.

Hypothesis strong_fexp : Zodd (radix_val beta) \/ forall e,
 ((fexp e < e)%Z -> (fexp (e + 1) < e)%Z) /\ ((e <= fexp e)%Z -> fexp (fexp e + 1) = fexp e).

Theorem DN_UP_parity_generic_pos :
  DN_UP_parity_pos_prop.
Proof.
intros x xd xu cd cu H0x Hfx Hd Hu Hxd Hxu.
destruct (ln_beta beta x) as (ex, Hexa).
specialize (Hexa (Rgt_not_eq _ _ H0x)).
generalize Hexa. intros Hex.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ H0x)) in Hex.
destruct (Zle_or_lt ex (fexp ex)) as [Hxe|Hxe].
(* small x *)
assert (Hd3 : Fnum cd = Z0).
apply F2R_eq_0_reg with beta (Fexp cd).
change (F2R cd = R0).
rewrite <- (proj1 Hd).
apply Rnd_DN_pt_unicity with (1 := Hxd).
now apply generic_DN_pt_small_pos with (2 := Hex).
assert (Hu3 : cu = Float beta (1 * Zpower (radix_val beta) (fexp ex - fexp (fexp ex + 1))) (fexp (fexp ex + 1))).
apply canonic_unicity with (1 := Hu).
replace xu with (bpow (fexp ex)).
split.
rewrite <- F2R_bpow.
apply F2R_change_exp.
now eapply valid_fexp.
simpl.
now rewrite ln_beta_bpow.
apply Rnd_UP_pt_unicity with (2 := Hxu).
now apply generic_UP_pt_small_pos.
rewrite Hd3, Hu3.
rewrite Zmult_1_l.
simpl.
destruct strong_fexp as [H|H].
apply Zodd_Zpower with (2 := H).
apply Zle_minus_le_0.
now eapply valid_fexp.
rewrite (proj2 (H ex)).
now rewrite Zminus_diag.
exact Hxe.
(* large x *)
assert (Hd4: (bpow (ex - 1) <= Rabs xd < bpow ex)%R).
rewrite Rabs_pos_eq.
split.
apply Hxd.
apply generic_format_bpow.
ring_simplify (ex - 1 + 1)%Z.
omega.
apply Hex.
apply Rle_lt_trans with (2 := proj2 Hex).
apply Hxd.
apply Hxd.
apply generic_format_0.
now apply Rlt_le.
assert (Hxe2 : (fexp (ex + 1) <= ex)%Z) by now eapply valid_fexp.
destruct (total_order_T (bpow ex) xu) as [[Hu2|Hu2]|Hu2].
(* - xu > bpow ex  *)
elim (Rlt_not_le _ _ Hu2).
apply Rnd_UP_pt_monotone with (generic_format beta fexp) x (bpow ex).
exact Hxu.
split.
apply generic_format_bpow.
exact Hxe2.
split.
apply Rle_refl.
easy.
now apply Rlt_le.
(* - xu = bpow ex *)
assert (Hu3: cu = Float beta (1 * Zpower (radix_val beta) (ex - fexp (ex + 1))) (fexp (ex + 1))).
apply canonic_unicity with (1 := Hu).
rewrite <- Hu2.
split.
rewrite <- F2R_change_exp.
apply sym_eq.
apply F2R_bpow.
exact Hxe2.
simpl.
apply f_equal.
apply sym_eq.
apply ln_beta_bpow.
assert (Hd3: cd = Float beta (Zpower (radix_val beta) (ex - fexp ex) - 1) (fexp ex)).
apply canonic_unicity with (1 := Hd).
generalize (ulp_pred_succ_pt beta _ valid_fexp x xd xu Hfx Hxd Hxu).
intros Hud.
split.
unfold F2R. simpl.
rewrite minus_Z2R.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Z2R_Zpower, <- bpow_add.
ring_simplify (ex - fexp ex + fexp ex)%Z.
rewrite Hu2, Hud.
unfold ulp.
rewrite ln_beta_unique with beta x ex.
unfold F2R.
simpl. ring.
rewrite Rabs_pos_eq.
exact Hex.
now apply Rlt_le.
apply Zle_minus_le_0.
now apply Zlt_le_weak.
simpl.
now rewrite ln_beta_unique with (1 := Hd4).
rewrite Hd3, Hu3.
unfold Fnum.
ring_simplify (Zpower (radix_val beta) (ex - fexp ex) - 1 + 1 * Zpower (radix_val beta) (ex - fexp (ex + 1)))%Z.
apply Zodd_pred.
destruct (Zeven_odd_dec (radix_val beta)) as [Hdo|Hdo].
apply Zeven_plus_Zeven.
apply Zeven_Zpower with (2 := Hdo).
omega.
apply Zeven_Zpower with (2 := Hdo).
destruct strong_fexp.
now elim Zeven_not_Zodd with (1 := Hdo).
generalize (proj1 (H _) Hxe).
omega.
apply Zodd_plus_Zodd.
apply Zodd_Zpower with (2 := Hdo).
omega.
apply Zodd_Zpower with (2 := Hdo).
apply Zle_minus_le_0.
exact Hxe2.
(* - xu < bpow ex *)
generalize (ulp_pred_succ_pt beta _ valid_fexp x xd xu Hfx Hxd Hxu).
rewrite (proj1 Hd), (proj1 Hu).
unfold ulp, F2R.
rewrite (proj2 Hd), (proj2 Hu).
rewrite ln_beta_unique with beta xu ex.
rewrite ln_beta_unique with (1 := Hd4).
rewrite ln_beta_unique with (1 := Hexa).
simpl.
intros H.
replace (Fnum cu) with (Fnum cd + 1)%Z.
replace (Fnum cd + (Fnum cd + 1))%Z with (2 * Fnum cd + 1)%Z by ring.
apply Zodd_Sn.
now apply Zeven_mult_Zeven_l.
apply sym_eq.
apply eq_Z2R.
rewrite plus_Z2R.
apply Rmult_eq_reg_r with (bpow (fexp ex)).
rewrite H.
simpl. ring.
apply Rgt_not_eq.
apply bpow_gt_0.
rewrite Rabs_pos_eq.
split.
apply Rle_trans with (1 := proj1 Hex).
apply Hxu.
exact Hu2.
apply Rlt_le.
apply Rlt_le_trans with (1 := H0x).
apply Hxu.
Qed.

Theorem Rnd_NE_pt_total :
  rounding_pred_total Rnd_NE_pt.
Proof.
apply satisfies_any_imp_NG.
now apply generic_format_satisfies_any.
intros x d u Hf Hd Hu.
elim Hd. intros (cd, Hcd) _.
destruct (Zeven_odd_dec (Fnum cd)) as [He|Ho].
right.
exists cd.
now split.
left.
elim Hu. intros (cu, Hcu) _.
exists cu.
split.
exact Hcu.
replace (Fnum cu) with (Fnum cd + Fnum cu + (-1) * Fnum cd)%Z by ring.
apply Zodd_plus_Zodd.
now apply (DN_UP_parity_aux DN_UP_parity_generic_pos x d u).
now apply Zodd_mult_Zodd.
Qed.

Theorem Rnd_NE_pt_monotone :
  rounding_pred_monotone Rnd_NE_pt.
Proof.
apply Rnd_NG_pt_monotone.
intros x d u Hd Hdn Hu Hun (cd, (Hd1, Hd2)) (cu, (Hu1, Hu2)).
destruct (Req_dec x d) as [Hx|Hx].
rewrite <- Hx.
apply sym_eq.
apply Rnd_UP_pt_idempotent with (1 := Hu).
rewrite Hx.
apply Hd.
absurd (Zodd (Fnum cd + Fnum cu)).
apply Zeven_not_Zodd.
now apply Zeven_plus_Zeven.
apply (DN_UP_parity_aux DN_UP_parity_generic_pos x d u) ; try easy.
intros Hf.
apply Hx.
apply sym_eq.
now apply Rnd_DN_pt_idempotent with (1 := Hd).
Qed.

Theorem Rnd_NE_pt_rounding :
  rounding_pred Rnd_NE_pt.
split.
apply Rnd_NE_pt_total.
apply Rnd_NE_pt_monotone.
Qed.

End Fcore_rnd_NE.

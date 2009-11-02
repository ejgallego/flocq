Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_prop.
Require Import Flocq_float_prop.

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

Definition canonic x (f : float beta) :=
  x = F2R f /\ Fexp f = fexp (projT1 (ln_beta beta x)).

Definition generic_format (x : R) :=
  exists f : float beta,
  canonic x f.

Theorem generic_format_0 :
  generic_format 0.
Proof.
exists (Float beta 0 _) ; repeat split.
now rewrite F2R_0.
Qed.

Theorem generic_DN_pt_large_pos_ge_pow :
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

Theorem generic_DN_pt_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  Rnd_DN_pt generic_format x (F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex))).
Proof.
intros x ex (Hx1, Hx2).
destruct (Z_lt_le_dec (fexp ex) ex) as [He1|He1].
(* - positive big enough *)
assert (Hbl : (bpow (ex - 1) <= F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex)))%R).
now apply generic_DN_pt_large_pos_ge_pow.
(* - . smaller *)
assert (Hrx : (F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex)) <= x)%R).
unfold F2R. simpl.
pattern x at 2 ; replace x with ((x * bpow (- fexp ex)) * bpow (fexp ex))%R.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Zfloor_lb.
rewrite Rmult_assoc.
rewrite <- bpow_add.
rewrite Zplus_opp_l.
apply Rmult_1_r.
split.
(* - . rounded *)
eexists ; repeat split.
simpl.
apply f_equal.
apply sym_eq.
apply ln_beta_unique.
rewrite Rabs_pos_eq.
split.
exact Hbl.
now apply Rle_lt_trans with (2 := Hx2).
apply Rle_trans with (2 := Hbl).
apply bpow_ge_0.
split.
exact Hrx.
(* - . biggest *)
intros g ((gm, ge), (Hg1, Hg2)) Hgx.
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
rewrite <- (Rabs_pos_eq g (Rlt_le _ _ Hg3)) in H.
rewrite ln_beta_unique with (1 := H) in Hg2.
simpl in Hg2.
apply Rlt_not_le with (1 := Hrg).
rewrite Hg1, Hg2.
apply F2R_le_compat.
apply Zfloor_lub.
apply Rmult_le_reg_r with (bpow (fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc.
rewrite <- bpow_add.
rewrite Zplus_opp_l.
rewrite Rmult_1_r.
unfold F2R in Hg1.
simpl in Hg1.
rewrite <- Hg2.
now rewrite <- Hg1.
(* - positive too small *)
replace (Zfloor (x * bpow (- fexp ex))) with Z0.
(* - . rounded *)
rewrite F2R_0.
split.
exact generic_format_0.
split.
apply Rle_trans with (2 := Hx1).
apply bpow_ge_0.
(* - . biggest *)
intros g ((gm, ge), (Hg1, Hg2)) Hgx.
apply Rnot_lt_le.
intros Hg3.
destruct (ln_beta beta g) as (ge', Hg4).
simpl in Hg2.
specialize (Hg4 (Rgt_not_eq _ _ Hg3)).
rewrite Rabs_pos_eq in Hg4.
apply (Rlt_not_le _ _ (Rle_lt_trans _ _ _ Hgx Hx2)).
apply Rle_trans with (bpow ge).
apply -> bpow_le.
simpl in Hg2.
rewrite Hg2.
rewrite (proj2 (proj2 (prop_exp ex) He1) ge').
exact He1.
apply Zle_trans with (2 := He1).
cut (ge' - 1 < ex)%Z. omega.
apply <- bpow_lt.
apply Rle_lt_trans with (2 := Hx2).
apply Rle_trans with (2 := Hgx).
exact (proj1 Hg4).
rewrite Hg1.
rewrite <- F2R_bpow.
apply F2R_le_compat.
apply (Zlt_le_succ 0).
apply F2R_lt_reg with beta ge.
now rewrite F2R_0, <- Hg1.
now apply Rlt_le.
(* - . . *)
apply sym_eq.
apply Zfloor_imp.
simpl.
split.
apply Rmult_le_pos.
apply Rle_trans with (2 := Hx1).
apply bpow_ge_0.
apply bpow_ge_0.
apply Rmult_lt_reg_r with (bpow (fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc.
rewrite <- bpow_add.
rewrite Zplus_opp_l.
rewrite Rmult_1_r, Rmult_1_l.
apply Rlt_le_trans with (1 := Hx2).
now apply -> bpow_le.
Qed.

Theorem generic_DN_pt_neg :
  forall x ex,
  (bpow (ex - 1) <= -x < bpow ex)%R ->
  Rnd_DN_pt generic_format x (F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex))).
Proof.
intros x ex (Hx1, Hx2).
assert (Hx : (x < 0)%R).
apply Ropp_lt_cancel.
rewrite Ropp_0.
apply Rlt_le_trans with (2 := Hx1).
apply bpow_gt_0.
assert (Hbr : (F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex)) <= x)%R).
(* - bounded right *)
unfold F2R. simpl.
pattern x at 2 ; rewrite <- Rmult_1_r.
change R1 with (bpow Z0).
rewrite <- (Zplus_opp_l (fexp ex)).
rewrite bpow_add.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Zfloor_lb.
destruct (Z_lt_le_dec (fexp ex) ex) as [He1|He1].
(* - negative big enough *)
assert (Hbl : (- bpow ex <= F2R (Float beta (Zfloor (x * bpow (- fexp ex))) (fexp ex)))%R).
(* - . bounded left *)
unfold F2R. simpl.
pattern ex at 1 ; replace ex with (ex - fexp ex + fexp ex)%Z by ring.
rewrite bpow_add.
rewrite <- Ropp_mult_distr_l_reverse.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (Hp : (- bpow (ex - fexp ex) = Z2R (- Zpower (radix_val beta) (ex - fexp ex)))%R).
rewrite <- Z2R_Zpower.
now rewrite opp_Z2R.
omega.
rewrite Hp.
apply Z2R_le.
apply Zfloor_lub.
rewrite <- Hp.
unfold Zminus.
rewrite bpow_add.
rewrite <- Ropp_mult_distr_l_reverse.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
now apply Rlt_le.
split.
(* - . rounded *)
destruct (Rle_lt_or_eq_dec _ _ Hbl) as [Hbl2|Hbl2].
(* - . . not a radix power *)
eexists ; repeat split.
simpl.
apply f_equal.
apply sym_eq.
apply ln_beta_unique.
rewrite Rabs_left.
split.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Rle_trans with (1 := Hbr).
apply Ropp_le_cancel.
now rewrite Ropp_involutive.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
apply Rle_lt_trans with (1 := Hbr).
exact Hx.
(* - . . a radix power *)
rewrite <- Hbl2.
generalize (proj1 (prop_exp _) He1).
clear.
intros He2.
exists (Float beta (- Zpower (radix_val beta) (ex - fexp (ex + 1))) (fexp (ex + 1))).
unfold canonic, F2R. simpl.
split.
clear -He2.
pattern ex at 1 ; replace ex with (ex - fexp (ex + 1) + fexp (ex + 1))%Z by ring.
rewrite bpow_add.
rewrite <- Ropp_mult_distr_l_reverse.
rewrite opp_Z2R.
apply (f_equal (fun x => (- x * _)%R)).
apply sym_eq.
apply Z2R_Zpower.
omega.
apply f_equal.
apply sym_eq.
apply ln_beta_unique.
rewrite Rabs_Ropp.
rewrite Rabs_right.
split.
apply -> bpow_le.
omega.
apply -> bpow_lt.
apply Zlt_succ.
apply Rle_ge.
apply bpow_ge_0.
split.
exact Hbr.
(* - . biggest *)
intros g ((gm, ge), (Hg1, Hg2)) Hgx.
apply Rnot_lt_le.
intros Hg3.
assert (Hg4 : (g < 0)%R).
now apply Rle_lt_trans with (1 := Hgx).
destruct (ln_beta beta g) as (ge', Hge).
simpl in Hg2.
specialize (Hge (Rlt_not_eq _ _ Hg4)).
apply Rlt_not_le with (1 := Hg3).
rewrite Hg1.
unfold F2R. simpl.
rewrite Hg2.
assert (Hge' : ge' = ex).
apply bpow_unique with (1 := Hge).
split.
apply Rle_trans with (1 := Hx1).
rewrite Rabs_left with (1 := Hg4).
now apply Ropp_le_contravar.
apply Ropp_lt_cancel.
rewrite Rabs_left with (1 := Hg4).
rewrite Ropp_involutive.
now apply Rle_lt_trans with (1 := Hbl).
rewrite Hge'.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Z2R_le.
apply Zfloor_lub.
apply Rmult_le_reg_r with (bpow (fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc.
rewrite <- bpow_add.
rewrite Zplus_opp_l.
rewrite Rmult_1_r.
rewrite <- Hge'.
rewrite <- Hg2.
unfold F2R in Hg1. simpl in Hg1.
now rewrite <- Hg1.
(* - negative too small *)
replace (Zfloor (x * bpow (- fexp ex))) with (-1)%Z.
unfold F2R. simpl.
rewrite Ropp_mult_distr_l_reverse.
rewrite Rmult_1_l.
(* - . rounded *)
split.
destruct (proj2 (prop_exp _) He1) as (He2, _).
exists (Float beta (- Zpower (radix_val beta) (fexp ex - fexp (fexp ex + 1))) (fexp (fexp ex + 1))).
unfold canonic, F2R. simpl.
split.
rewrite opp_Z2R.
pattern (fexp ex) at 1 ; replace (fexp ex) with (fexp ex - fexp (fexp ex + 1) + fexp (fexp ex + 1))%Z by ring.
rewrite bpow_add.
rewrite Ropp_mult_distr_l_reverse.
apply (f_equal (fun x => (- (x * _))%R)).
apply sym_eq.
apply Z2R_Zpower.
omega.
apply f_equal.
apply sym_eq.
apply ln_beta_unique.
rewrite Rabs_Ropp.
rewrite Rabs_pos_eq.
split.
replace (fexp ex + 1 - 1)%Z with (fexp ex) by ring.
apply Rle_refl.
apply -> bpow_lt.
apply Zlt_succ.
apply bpow_ge_0.
split.
(* - . smaller *)
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hx2).
now apply -> bpow_le.
(* - . biggest *)
intros g ((gm, ge), (Hg1, Hg2)) Hgx.
apply Rnot_lt_le.
intros Hg3.
assert (Hg4 : (g < 0)%R).
now apply Rle_lt_trans with (1 := Hgx).
destruct (ln_beta beta g) as (ge', Hge).
simpl in Hg2.
specialize (Hge (Rlt_not_eq g 0 Hg4)).
rewrite (Rabs_left _ Hg4) in Hge.
assert (Hge' : (ge' <= fexp ex)%Z).
cut (ge' - 1 < fexp ex)%Z. omega.
apply <- bpow_lt.
apply Rle_lt_trans with (1 := proj1 Hge).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
rewrite (proj2 (proj2 (prop_exp _) He1) _ Hge') in Hg2.
rewrite <- Hg2 in Hge'.
apply Rlt_not_le with (1 := proj2 Hge).
rewrite Hg1.
unfold F2R. simpl.
rewrite <- Ropp_mult_distr_l_reverse.
replace ge with (ge - ge' + ge')%Z by ring.
rewrite bpow_add.
rewrite <- Rmult_assoc.
pattern (bpow ge') at 1 ; rewrite <- Rmult_1_l.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite <- opp_Z2R.
assert (1 <= -gm)%Z.
apply (Zlt_le_succ 0).
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow ge).
apply bpow_gt_0.
rewrite Rmult_0_l.
change (0 < F2R (Float beta (-gm) ge))%R.
rewrite <- opp_F2R.
rewrite <- Hg1.
rewrite <- Ropp_0.
now apply Ropp_lt_contravar.
apply Rle_trans with (1 * bpow (ge - ge'))%R.
rewrite Rmult_1_l.
apply -> (bpow_le beta 0).
omega.
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply (Z2R_le 1).
(* - . . *)
apply sym_eq.
apply Zfloor_imp.
simpl.
split.
apply Rle_trans with (- bpow ex * bpow (- fexp ex))%R.
rewrite Ropp_mult_distr_l_reverse.
rewrite <- bpow_add.
apply Ropp_le_contravar.
apply (proj1 (bpow_le beta _ 0)).
omega.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
now apply Rlt_le.
rewrite <- (Rmult_0_l (bpow (- fexp ex))).
apply Rmult_lt_compat_r.
apply bpow_gt_0.
exact Hx.
Qed.

Theorem canonic_unicity :
  forall x f1 f2,
  canonic x f1 ->
  canonic x f2 ->
  f1 = f2.
Proof.
intros x (m1,e1) (m2,e2) (H1a,H1b) (H2a,H2b).
simpl in H1b, H2b.
rewrite H1b, <- H2b.
apply (f_equal (fun m => Float beta m e2)).
apply eq_Z2R.
apply Rmult_eq_reg_r with (bpow e1).
change (F2R (Float beta m1 e1) = F2R (Float beta m2 e1)).
now rewrite <- H1a, H1b, <- H2b.
apply Rgt_not_eq.
apply bpow_gt_0.
Qed.

Theorem canonic_sym :
  forall x m e,
  canonic x (Float beta m e) ->
  canonic (-x) (Float beta (-m) e).
Proof.
intros x m e.
destruct (Req_dec x 0) as [Hx|Hx].
(* . *)
rewrite Hx, Ropp_0.
intros (H1,H2).
split.
now rewrite <- opp_F2R, <- H1, Ropp_0.
exact H2.
(* . *)
intros (H1,H2).
split.
rewrite H1.
apply opp_F2R.
now rewrite ln_beta_opp.
Qed.

Theorem generic_format_sym :
  forall x, generic_format x -> generic_format (-x).
Proof.
intros x ((m,e),H).
exists (Float beta (-m) e).
now apply canonic_sym.
Qed.

Theorem generic_format_satisfies_any :
  satisfies_any generic_format.
Proof.
split.
(* symmetric set *)
exact generic_format_0.
exact generic_format_sym.
(* rounding down *)
intros x.
exists (match Req_EM_T x 0 with
  | left Hx => R0
  | right Hx =>
    let e := fexp (projT1 (ln_beta beta x)) in
    F2R (Float beta (Zfloor (x * bpow (Zopp e))) e)
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
apply generic_DN_pt_neg.
now rewrite <- Rabs_left.
apply generic_DN_pt_pos.
rewrite Rabs_right in H1.
exact H1.
now apply Rgt_ge.
Qed.

Theorem generic_DN_pt_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Rnd_DN_pt generic_format x R0.
Proof.
intros x ex Hx He.
split.
exact generic_format_0.
split.
apply Rle_trans with (2 := proj1 Hx).
apply bpow_ge_0.
(* . *)
intros g ((gm, ge), (Hg1, Hg2)) Hgx.
apply Rnot_lt_le.
intros Hg3.
destruct (ln_beta beta g) as (eg, Hg4).
simpl in Hg2.
specialize (Hg4 (Rgt_not_eq g 0 Hg3)).
rewrite Rabs_right in Hg4.
apply Rle_not_lt with (1 := Hgx).
rewrite Hg1.
apply Rlt_le_trans with (1 := proj2 Hx).
rewrite (proj2 (proj2 (prop_exp _) He) eg) in Hg2.
rewrite Hg2.
apply Rle_trans with (bpow (fexp ex)).
now apply -> bpow_le.
rewrite <- Hg2.
rewrite Hg1 in Hg3.
apply bpow_le_F2R.
apply F2R_gt_0_reg with (1 := Hg3).
apply bpow_lt_bpow with beta.
apply Rlt_le_trans with (bpow ex).
apply Rle_lt_trans with (2 := proj2 Hx).
now apply Rle_trans with g.
now apply -> bpow_le.
apply Rle_ge.
now apply Rlt_le.
Qed.

Theorem generic_UP_pt_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Rnd_UP_pt generic_format x (bpow (fexp ex)).
Proof.
intros x ex Hx He.
assert (bpow (fexp ex) = F2R (Float beta (Zpower (radix_val beta) (fexp ex - fexp (fexp ex + 1))) (fexp (fexp ex + 1)))).
unfold F2R. simpl.
rewrite Z2R_Zpower.
rewrite <- bpow_add.
apply f_equal.
ring.
generalize (proj1 (proj2 (prop_exp ex) He)).
omega.
split.
(* . *)
rewrite H.
eexists ; repeat split.
simpl.
apply f_equal.
apply sym_eq.
rewrite <- H.
apply ln_beta_unique.
split.
replace (fexp ex + 1 - 1)%Z with (fexp ex) by ring.
apply RRle_abs.
rewrite Rabs_pos_eq.
apply -> bpow_lt.
apply Zle_lt_succ.
apply Zle_refl.
apply bpow_ge_0.
split.
(* . *)
apply Rlt_le.
apply Rlt_le_trans with (1 := proj2 Hx).
now apply -> bpow_le.
(* . *)
intros g ((gm, ge), (Hg1, Hg2)) Hgx.
assert (g <> R0).
apply Rgt_not_eq.
apply Rlt_le_trans with (2 := Hgx).
apply Rlt_le_trans with (2 := proj1 Hx).
apply bpow_gt_0.
destruct (ln_beta beta g) as (eg, Hg3).
simpl in Hg2.
specialize (Hg3 H0).
apply Rnot_lt_le.
intros Hgp.
apply Rlt_not_le with (1 := Hgp).
rewrite <- (proj2 (proj2 (prop_exp ex) He) eg).
rewrite <- Hg2.
rewrite Hg1.
apply bpow_le_F2R.
apply F2R_gt_0_reg with beta ge.
rewrite <- Hg1.
apply Rlt_le_trans with (2 := Hgx).
apply Rlt_le_trans with (2 := proj1 Hx).
apply bpow_gt_0.
apply bpow_lt_bpow with beta.
apply Rle_lt_trans with g.
rewrite <- (Rabs_right g).
apply Hg3.
apply Rle_ge.
apply Rle_trans with (2 := Hgx).
apply Rle_trans with (2 := proj1 Hx).
apply bpow_ge_0.
exact Hgp.
Qed.

Theorem generic_UP_pt_large_pos_le_pow :
  forall x xu ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (fexp ex < ex)%Z ->
  Rnd_UP_pt generic_format x xu ->
  (xu <= bpow ex)%R.
Proof.
intros x xu ex Hx He (((dm, de), (Hu1, Hu2)), (Hu3, Hu4)).
apply Hu4 with (2 := (Rlt_le _ _ (proj2 Hx))).
exists (Float beta (Zpower (radix_val beta) (ex - fexp (ex + 1))) (fexp (ex + 1))).
unfold canonic, F2R. simpl.
split.
(* . *)
rewrite Z2R_Zpower.
rewrite <- bpow_add.
apply f_equal.
ring.
generalize (proj1 (prop_exp _) He).
omega.
(* . *)
apply f_equal.
apply sym_eq.
apply ln_beta_unique.
rewrite Rabs_pos_eq.
split.
ring_simplify (ex + 1 - 1)%Z.
apply Rle_refl.
apply -> bpow_lt.
apply Zlt_succ.
apply bpow_ge_0.
Qed.

Theorem generic_UP_pt_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  Rnd_UP_pt generic_format x (F2R (Float beta (Zceil (x * bpow (Zopp (fexp ex)))) (fexp ex))).
Proof.
intros x ex Hx1.
apply Rnd_DN_UP_pt_sym.
apply generic_format_satisfies_any.
unfold Zceil.
rewrite <- Ropp_mult_distr_l_reverse.
rewrite opp_F2R.
rewrite Zopp_involutive.
apply generic_DN_pt_neg.
now rewrite Ropp_involutive.
Qed.

Theorem generic_UP_pt_neg :
  forall x ex,
  (bpow (ex - 1) <= - x < bpow ex)%R ->
  Rnd_UP_pt generic_format x (F2R (Float beta (Zceil (x * bpow (Zopp (fexp ex)))) (fexp ex))).
Proof.
intros x ex Hx1.
apply Rnd_DN_UP_pt_sym.
apply generic_format_satisfies_any.
unfold Zceil.
rewrite <- Ropp_mult_distr_l_reverse.
rewrite opp_F2R.
rewrite Zopp_involutive.
now apply generic_DN_pt_pos.
Qed.

End RND_generic.

Theorem canonic_fun_eq :
  forall beta : radix, forall f1 f2 : Z -> Z, forall x f,
  f1 (projT1 (ln_beta beta x)) = f2 (projT1 (ln_beta beta x)) ->
  canonic beta f1 x f -> canonic beta f2 x f.
Proof.
intros beta f1 f2 x f Hf (Hx1,Hx2).
split.
exact Hx1.
now rewrite <- Hf.
Qed.

Theorem generic_format_fun_eq :
  forall beta : radix, forall f1 f2 : Z -> Z, forall x,
  f1 (projT1 (ln_beta beta x)) = f2 (projT1 (ln_beta beta x)) ->
  generic_format beta f1 x -> generic_format beta f2 x.
Proof.
intros beta f1 f2 x Hf (f,Hx).
exists f.
now apply canonic_fun_eq with (1 := Hf).
Qed.

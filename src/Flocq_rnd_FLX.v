Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_prop.
Require Import Flocq_rnd_FIX.

Section RND_FIX.

Open Scope R_scope.

Variable beta : radix.

Notation bpow := (epow beta).

Lemma F2R_pos_imp_Fnum_pos :
  forall f : float beta,
  0 <= F2R f ->
  (0 <= Fnum f)%Z.
Proof.
intros f H.
apply le_Z2R.
apply Rmult_le_reg_l with (bpow (Fexp f)).
apply epow_gt_0.
rewrite Rmult_0_r.
now rewrite Rmult_comm.
Qed.

Lemma F2R_constrain :
  forall m e e' p : Z,
  (Zabs m < Zpower (radix_val beta) p)%Z ->
  bpow e' <= F2R (Float beta m e) ->
  exists m' : Z,
  F2R (Float beta m e) = F2R (Float beta m' (e' - (p - 1))).
Proof.
intros m e e' p Hm Hf.
exists (m * Zpower (radix_val beta) (e - (e' - (p - 1))))%Z.
unfold F2R.
simpl.
rewrite mult_Z2R.
rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
rewrite Z2R_Zpower.
rewrite <- epow_add.
apply f_equal.
ring.
assert (e' <= e + (p - 1))%Z.
2: omega.
apply Zlt_succ_le.
unfold Zsucc.
replace (e + (p - 1) + 1)%Z with (e + p)%Z by ring.
apply <- epow_lt.
apply Rle_lt_trans with (1 := Hf).
unfold F2R.
rewrite epow_add.
rewrite Rmult_comm.
apply Rmult_lt_compat_l.
apply epow_gt_0.
simpl.
apply Rle_lt_trans with (1 := RRle_abs _).
rewrite Z2R_IZR.
rewrite Rabs_Zabs.
rewrite <- Z2R_IZR.
replace (bpow p) with (Z2R (Zpower (radix_val beta) p)).
now apply Z2R_lt.
rewrite Z2R_Zpower.
apply refl_equal.
clear -Hm.
destruct p as [_|p|p] ; try discriminate.
simpl in Hm.
elim Zlt_not_le with (1 := Hm).
apply Zabs_pos.
Qed.

Variable prec : Z.
Variable Hp : Zlt 0 prec.

Theorem FLX_format_satisfies_any :
  satisfies_any (FLX_format beta prec).
Proof.
refine ((fun D => Satisfies_any _ _ _ (projT1 D) (projT2 D)) _).
(* symmetric set *)
exists (Float beta 0 0).
split.
unfold F2R.
now rewrite Rmult_0_l.
apply lt_Z2R.
rewrite Z2R_Zpower.
apply epow_gt_0.
now apply Zlt_le_weak.
intros x ((m,e),(H1,H2)).
exists (Float beta (-m) e).
split.
rewrite H1.
unfold F2R.
simpl.
now rewrite opp_Z2R, Ropp_mult_distr_l_reverse.
simpl.
now rewrite Zabs_Zopp.
(* rounding down *)
assert (Hh : forall x, 0 > x -> 0 < -x).
intros x Hx.
apply Ropp_gt_lt_0_contravar.
exact Hx.
exists (fun x =>
  let e :=
  Zminus match total_order_T 0 x with
  | inleft (left Hx) => projS1 (ln_beta beta _ Hx)
  | inleft (right Hx) => Z0
  | inright Hx => projS1 (ln_beta beta _ (Hh _ Hx))
  end prec in
  match FIX_format_satisfies_any beta e with
  | Satisfies_any _ _ rnd Hr => rnd x
  end).
intros x.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].
(* x positive *)
clear Hh.
set (e := (projT1 (ln_beta beta x Hx) - prec)%Z).
destruct (FIX_format_satisfies_any beta e) as (_,_,rnd,Hr).
destruct (Hr x) as ((f,(Hr1,Hr2)),(Hr3,Hr4)).
destruct (ln_beta beta x Hx) as (e', Hb).
simpl in e.
split.
(* - f is compatible with the format *)
assert (Hm: (Zabs (Fnum f) < Zpower (radix_val beta) prec)%Z).
apply Zgt_lt.
apply Znot_le_gt.
intros Hm.
apply Rlt_not_le with (1 := proj2 Hb).
apply Rle_trans with (2 := Hr3).
rewrite Hr1.
unfold F2R.
rewrite Hr2.
replace e' with (prec + e)%Z by ( unfold e ; ring ).
rewrite epow_add.
apply Rmult_le_compat_r.
apply epow_ge_0.
rewrite <- Z2R_Zpower.
apply Z2R_le.
rewrite <- (Zabs_eq (Fnum f)).
exact Hm.
apply F2R_pos_imp_Fnum_pos.
rewrite <- Hr1.
apply Rnd_pos_imp_pos with (FIX_format beta e).
exists (Float beta 0 e).
repeat split.
unfold F2R.
now rewrite Rmult_0_l.
split.
now apply Rnd_DN_monotone with (FIX_format beta e).
now apply Rnd_DN_idempotent.
now apply Rlt_le.
now apply Zlt_le_weak.
now exists f ; split.
(* - f is the biggest float smaller than x *)
split.
exact Hr3.
intros g ((mg,eg),(Hg1,Hg2)) Hgx.
destruct (Rle_or_lt g (bpow (e' - 1)%Z)).
apply Rle_trans with (1 := H).
apply Hr4.
exists (Float beta (Zpower (radix_val beta) (prec - 1)) e).
repeat split.
unfold F2R.
simpl.
rewrite Z2R_Zpower.
rewrite <- epow_add.
unfold e.
apply f_equal.
ring.
omega.
apply Hb.
apply Hr4.
destruct (F2R_constrain mg eg (e' - 1) prec Hg2) as (mg',Hg).
rewrite <- Hg1.
now apply Rlt_le.
rewrite Hg1, Hg.
replace (e' - 1 - (prec - 1))%Z with (e' - prec)%Z by ring.
now exists (Float beta mg' (e' - prec)).
exact Hgx.
(* x zero *)
admit.
(* x negative *)
admit.
Qed.

End RND_FIX.

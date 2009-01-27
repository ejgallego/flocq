Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_float_prop.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_prop.
Require Import Flocq_rnd_FIX.

Section RND_FIX.

Open Scope R_scope.

Variable beta : radix.

Notation bpow := (epow beta).

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
  match satisfies_any_imp_DN _ (FIX_format_satisfies_any beta e) with
  | exist rnd Hr => rnd x
  end).
intros x.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].
(* x positive *)
clear Hh.
set (e := (projT1 (ln_beta beta x Hx) - prec)%Z).
destruct (satisfies_any_imp_DN _ (FIX_format_satisfies_any beta e)) as (rnd,Hr).
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
apply F2R_ge_0_imp_Fnum.
rewrite <- Hr1.
apply Rnd_pos_imp_pos with (FIX_format beta e).
apply (FIX_format_satisfies_any beta e).
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
destruct (F2R_prec_normalize beta mg eg (e' - 1) prec Hg2) as (mg',Hg).
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

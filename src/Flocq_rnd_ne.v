Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_prop.
Require Import Flocq_rnd_generic.
Require Import Flocq_float_prop.
Require Import Flocq_ulp.

Section Flocq_rnd_NE.

Variable beta : radix.

Notation bpow e := (epow beta e).

Variable fexp : Z -> Z.

Variable prop_exp : valid_exp fexp.

Notation generic_format := (generic_format beta fexp).
Notation canonic := (canonic beta fexp).

Definition Rnd_NE_pt (x f : R) :=
  Rnd_N_pt generic_format x f /\
  ( ( exists g : float beta, canonic f g /\ Zeven (Fnum g) ) \/
    ( forall f2 : R, Rnd_N_pt generic_format x f2 -> f2 = f ) ).

Definition Rnd_NE (rnd : R -> R) :=
  forall x : R, Rnd_NE_pt x (rnd x).

Theorem Rnd_NE_pt_sym :
  forall x f : R,
  Rnd_NE_pt (-x) (-f) -> Rnd_NE_pt x f.
Proof.
intros x f (H1,H2).
split.
apply Rnd_N_pt_sym.
apply generic_format_sym.
exact H1.
(* . *)
destruct H2 as [((m,e),((H2,H3),H4))|H2].
left.
exists (Float beta (-m) e).
repeat split.
now rewrite <- opp_F2R, <- H2, Ropp_involutive.
simpl in H3 |- *.
now rewrite H3, Rabs_Ropp.
simpl in H4 |- *.
rewrite Zopp_eq_mult_neg_1.
now apply Zeven_mult_Zeven_l.
(* . *)
right.
intros f2 H3.
rewrite <- (Ropp_involutive f), <- (Ropp_involutive f2).
apply f_equal.
apply H2.
apply Rnd_N_pt_sym.
apply generic_format_sym.
now rewrite 2!Ropp_involutive.
Qed.

Theorem Rnd_NE_pt_unicity :
  forall x f1 f2 : R,
  Rnd_NE_pt x f1 -> Rnd_NE_pt x f2 ->
  f1 = f2.
Proof.
intros x f1 f2 (H1,[H2|H2]) (H3,H4).
destruct H4 as [H4|H4].
destruct (Req_dec x f1) as [H5|H5].
(* . *)
rewrite <- H5.
apply sym_eq.
apply (Rnd_N_pt_idempotent generic_format).
exact H3.
rewrite H5.
apply H1.
(* . *)
destruct (satisfies_any_imp_DN _ (generic_format_satisfies_any beta fexp prop_exp)) as (rndD, Hd).
destruct (satisfies_any_imp_UP _ (generic_format_satisfies_any beta fexp prop_exp)) as (rndU, Hu).
assert (forall d u, canonic (rndD x) d -> canonic (rndU x) u -> d <> u ->
  Zeven (Fnum d) -> Zeven (Fnum u) -> False).
clear -prop_exp Hd Hu.
intros d u Cd Cu Hdu Ed Eu.
apply (Zeven_not_Zodd (Fnum u)).
exact Eu.
Check (ulp_pred_succ_pt beta fexp prop_exp x (rndU x)).
admit.
(* . *)
destruct (Rnd_N_pt_DN_or_UP generic_format x (rndD x) (rndU x) f1) as [H6|H6].
apply Hd.
apply Hu.
apply H1.
destruct (Rnd_N_pt_DN_or_UP generic_format x (rndD x) (rndU x) f2) as [H7|H7].
apply Hd.
apply Hu.
apply H3.
now rewrite H6, H7.
destruct H2 as (d,(H2a,H2b)).
destruct H4 as (u,(H4a,H4b)).
elim (H d u) ; try assumption.
now rewrite <- H6.
now rewrite <- H7.
intros H8. apply H5.
apply Rle_antisym.
rewrite (proj1 H2a), H8, <- (proj1 H4a), H7.
eapply Hu.
rewrite H6.
eapply Hd.
destruct (Rnd_N_pt_DN_or_UP generic_format x (rndD x) (rndU x) f2) as [H7|H7].
apply Hd.
apply Hu.
apply H3.
destruct H2 as (u,(H2a,H2b)).
destruct H4 as (d,(H4a,H4b)).
elim (H d u) ; try assumption.
now rewrite <- H7.
now rewrite <- H6.
intros H8. apply H5.
apply Rle_antisym.
rewrite H6.
eapply Hu.
rewrite (proj1 H2a), <- H8, <- (proj1 H4a), H7.
eapply Hd.
now rewrite H6, H7.
(* . *)
now apply H4.
apply sym_eq.
now apply H2.
Qed.

Theorem Rnd_NE_pt_monotone :
  forall x y f g : R,
  Rnd_NE_pt x f -> Rnd_NE_pt y g ->
  (x <= y)%R -> (f <= g)%R.
Proof.
intros x y f g (Hx1,Hx2) (Hy1,Hy2) [Hxy|Hxy].
eapply Rnd_N_pt_monotone ; eassumption.
apply Req_le.
apply Rnd_NE_pt_unicity with x.
now split.
rewrite Hxy.
now split.
Qed.

End Flocq_rnd_NE.

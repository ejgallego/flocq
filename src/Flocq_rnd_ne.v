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

Definition Rnd_gNE_pt (x f : R) :=
  Rnd_N_pt generic_format x f /\
  ( ( exists g : float beta, canonic f g /\ Zeven (Fnum g) /\
        forall f2 : R, forall g : float beta, Rnd_N_pt generic_format x f2 ->
        canonic f2 g -> Zeven (Fnum g) -> (Rabs f2 <= Rabs f)%R ) \/
    ( forall f2 : R, Rnd_N_pt generic_format x f2 -> f = f2 ) ).

Definition Rnd_gNE (rnd : R -> R) :=
  forall x : R, Rnd_gNE_pt x (rnd x).

Theorem Rnd_gNE_pt_sym :
  forall x f : R,
  Rnd_gNE_pt (-x) (-f) -> Rnd_gNE_pt x f.
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
intros f2 g Hx Hxg Hg.
rewrite <- (Rabs_Ropp f), <- (Rabs_Ropp f2).
eapply H4.
apply Rnd_N_pt_sym.
apply generic_format_sym.
now rewrite 2!Ropp_involutive.
eapply canonic_sym.
eexact Hxg.
simpl.
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

Lemma canonic_imp_Fnum :
  forall x, forall f : float beta,
  x <> R0 ->
  canonic x f ->
  (Zabs (Fnum f) < Zpower (radix_val beta) (projT1 (ln_beta beta (Rabs x)) - Fexp f))%Z.
Proof.
intros x f Hx.
unfold Flocq_rnd_generic.canonic.
destruct (ln_beta beta (Rabs x)) as (ex, H).
simpl.
specialize (H (Rabs_pos_lt x Hx)).
intros (H1, H2).
destruct (Zle_or_lt (Fexp f) ex) as [He|He].
(* . *)
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow (Fexp f)).
apply epow_gt_0.
replace (Z2R (Zabs (Fnum f)) * bpow (Fexp f))%R with (Rabs x).
rewrite Z2R_Zpower, <- epow_add.
now ring_simplify (ex - Fexp f + Fexp f)%Z.
omega.
rewrite H1.
apply abs_F2R.
(* . *)
elim (Rlt_not_ge _ _ (proj2 H)).
apply Rle_ge.
rewrite H1.
destruct f as (xm, xe).
rewrite abs_F2R.
unfold F2R. simpl.
rewrite <- (Rmult_1_l (bpow ex)).
apply Rmult_le_compat.
now apply (Z2R_le 0 1).
apply epow_ge_0.
apply (Z2R_le 1).
apply (Zlt_le_succ 0).
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow xe).
apply epow_gt_0.
rewrite Rmult_0_l.
replace (Z2R (Zabs xm) * bpow xe)%R with (Rabs x).
now apply Rabs_pos_lt.
rewrite H1.
apply abs_F2R.
apply -> epow_le.
now apply Zlt_le_weak.
Qed.

Theorem Rnd_gNE_pt_unicity :
  forall x f1 f2 : R,
  Rnd_gNE_pt x f1 -> Rnd_gNE_pt x f2 ->
  f1 = f2.
Proof.
intros x f1 f2 (H1,[Hf1|Hf1]) (H2,Hf2).
destruct Hf2 as [Hf2|Hf2].
(* . *)
destruct Hf1 as (g1, (Hg1a, (Hg1b, Hg1c))).
destruct Hf2 as (g2, (Hg2a, (Hg2b, Hg2c))).
assert (Rabs f1 = Rabs f2).
apply Rle_antisym.
now apply Hg2c with g1.
now apply Hg1c with g2.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
rewrite (Rabs_pos_eq f1) in H.
rewrite H.
apply Rabs_pos_eq.
apply Rnd_N_pt_pos with generic_format x.
apply generic_format_0.
exact Hx.
exact H2.
apply Rnd_N_pt_pos with generic_format x.
apply generic_format_0.
exact Hx.
exact H1.
rewrite (Rabs_left1 f1) in H.
rewrite <- (Ropp_involutive f1), <- (Ropp_involutive f2).
rewrite H.
apply f_equal.
apply Rabs_left1.
apply Rnd_N_pt_neg with generic_format x.
apply generic_format_0.
now apply Rlt_le.
exact H2.
apply Rnd_N_pt_neg with generic_format x.
apply generic_format_0.
now apply Rlt_le.
exact H1.
(* . *)
apply sym_eq.
now apply Hf2.
now apply Hf1.
Qed.

Theorem Rnd_gNE_pt_monotone :
  forall x y f g : R,
  Rnd_gNE_pt x f -> Rnd_gNE_pt y g ->
  (x <= y)%R -> (f <= g)%R.
Proof.
intros x y f g (Hx1,Hx2) (Hy1,Hy2) [Hxy|Hxy].
eapply Rnd_N_pt_monotone ; eassumption.
apply Req_le.
apply Rnd_gNE_pt_unicity with x.
now split.
rewrite Hxy.
now split.
Qed.

Theorem Rnd_gNE_pt_idempotent :
  forall x f : R,
  Rnd_gNE_pt x f -> generic_format x ->
  f = x.
Proof.
intros x f Hxf Hx.
destruct Hxf as (Hxf1,_).
now apply Rnd_N_pt_idempotent with generic_format.
Qed.

End Flocq_rnd_NE.

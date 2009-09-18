Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_prop.
Require Import Flocq_rnd_generic.
Require Import Flocq_float_prop.
Require Import Flocq_ulp.
Require Import Flocq_rnd_FIX.
Require Import Flocq_rnd_FLX.
Require Import Flocq_rnd_FLT.

Section Flocq_rnd_NE.

Variable beta : radix.

Notation bpow e := (epow beta e).

Section Flocq_rnd_gNE.

Variable fexp : Z -> Z.

Variable prop_exp : valid_exp fexp.

Notation format := (generic_format beta fexp).
Notation canonic := (canonic beta fexp).

Definition Rnd_gNE_pt (x f : R) :=
  Rnd_N_pt format x f /\
  ( ( exists g : float beta, canonic f g /\ Zeven (Fnum g) /\
        forall f2 : R, forall g : float beta, Rnd_N_pt format x f2 ->
        canonic f2 g -> Zeven (Fnum g) -> (Rabs f2 <= Rabs f)%R ) \/
    ( forall f2 : R, Rnd_N_pt format x f2 -> f = f2 ) ).

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
apply Rnd_N_pt_pos with format x.
apply generic_format_0.
exact Hx.
exact H2.
apply Rnd_N_pt_pos with format x.
apply generic_format_0.
exact Hx.
exact H1.
rewrite (Rabs_left1 f1) in H.
rewrite <- (Ropp_involutive f1), <- (Ropp_involutive f2).
rewrite H.
apply f_equal.
apply Rabs_left1.
apply Rnd_N_pt_neg with format x.
apply generic_format_0.
now apply Rlt_le.
exact H2.
apply Rnd_N_pt_neg with format x.
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
  Rnd_gNE_pt x f -> format x ->
  f = x.
Proof.
intros x f Hxf Hx.
destruct Hxf as (Hxf1,_).
now apply Rnd_N_pt_idempotent with format.
Qed.

Definition Rnd_NE_pt (x f : R) :=
  Rnd_N_pt format x f /\
  ( ( exists g : float beta, canonic f g /\ Zeven (Fnum g) ) \/
    ( forall f2 : R, Rnd_N_pt format x f2 -> f = f2 ) ).

Definition DN_UP_parity_prop :=
  forall x xd xu cd cu,
  ~ format x ->
  canonic xd cd ->
  canonic xu cu ->
  Rnd_DN_pt format x xd ->
  Rnd_UP_pt format x xu ->
  Zeven (Fnum cd) ->
  Zeven (Fnum cu) ->
  False.

Theorem Rnd_NE_pt_aux :
  DN_UP_parity_prop ->
  forall x f,
  format f ->
  ( Rnd_gNE_pt x f <-> Rnd_NE_pt x f ).
Proof.
intros HP x f Hf.
split.
(* . *)
intros (H1, [H2|H2]).
(* . . *)
split.
exact H1.
left.
destruct H2 as (g, (H2, (H3, H4))).
exists g.
repeat split ; try eapply H2 ; easy.
(* . . *)
split.
exact H1.
now right.
(* . *)
intros (H1, [H2|H2]).
(* . . *)
split.
exact H1.
left.
destruct H2 as (g, (H2, H3)).
exists g.
repeat split ; try eapply H2 ; trivial.
intros f2 g2 Hf2 Hfg2 Hg2.
right.
apply f_equal.
destruct (Req_dec x f) as [Hx|Hx].
rewrite <- Hx.
apply Rnd_N_pt_idempotent with format.
exact Hf2.
rewrite Hx.
apply H1.
assert (Hxf: ~format x).
intros H.
apply Hx.
apply sym_eq.
now apply Rnd_N_pt_idempotent with format.
destruct (Rnd_N_pt_DN_or_UP _ _ _ H1) as [Hxf1|Hxf1].
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hf2) as [Hxf2|Hxf2].
apply Rnd_DN_pt_unicity with (1 := Hxf2) (2 := Hxf1).
now elim HP with (1 := Hxf) (2 := H2) (3 := Hfg2).
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hf2) as [Hxf2|Hxf2].
now elim HP with (1 := Hxf) (2 := Hfg2) (3 := H2).
apply Rnd_UP_pt_unicity with (1 := Hxf2) (2 := Hxf1).
(* . . *)
split.
exact H1.
now right.
Qed.

End Flocq_rnd_gNE.

Section Flocq_rnd_NE_FIX.

Variable emin : Z.

Notation FIXf := (FIX_exp emin).

Theorem DN_UP_parity_FIX :
  DN_UP_parity_prop FIXf.
Proof.
intros x xd xu cd cu Hfx (Hd1,Hd2) (Hu1,Hu2) Hxd Hxu Hed Heu.
generalize (ulp_pred_succ_pt beta FIXf (FIX_exp_correct emin) x xd xu Hfx Hxd Hxu).
rewrite Hd1, Hu1.
unfold ulp, F2R.
rewrite Hd2, Hu2.
unfold FIX_exp. simpl.
rewrite <- Rmult_plus_distr_r.
intros H.
absurd (Fnum cu = Fnum cd + 1)%Z.
intros H'.
apply (Zeven_not_Zodd _ Heu).
rewrite H'.
now apply Zodd_Sn.
apply eq_Z2R.
apply Rmult_eq_reg_r with (bpow emin).
rewrite plus_Z2R.
exact H.
apply Rgt_not_eq.
apply epow_gt_0.
Qed.

Theorem Rnd_NE_pt_FIX :
  forall x f,
  FIX_format beta emin f ->
  ( Rnd_gNE_pt FIXf x f <-> Rnd_NE_pt FIXf x f ).
Proof.
intros x f Hf.
apply Rnd_NE_pt_aux.
exact DN_UP_parity_FIX.
now apply -> FIX_format_generic.
Qed.

End Flocq_rnd_NE_FIX.

Section Flocq_rnd_NE_FLX.

Variable prec : Z.
Variable Hp : Zlt 0 prec.

Notation FLXf := (FLX_exp prec).

(*
Axiom Rnd_DN_pt_eq :
  forall F1 F2 a b,
  ( forall x, (a <= x <= b)%R -> ( F1 x <-> F2 x ) ) ->
  forall x f, (a <= x <= b)%R ->
  ( Rnd_DN_pt F1 x f <-> Rnd_DN_pt F2 x f ).
*)

Theorem DN_UP_parity_FLX_pos :
  forall x xd xu cd cu,
  (0 < x)%R ->
  ~ generic_format beta FLXf x ->
  canonic beta FLXf xd cd ->
  canonic beta FLXf xu cu ->
  Rnd_DN_pt (generic_format beta FLXf) x xd ->
  Rnd_UP_pt (generic_format beta FLXf) x xu ->
  Zeven (Fnum cd) ->
  Zeven (Fnum cu) ->
  False.
Proof.
intros x xd xu cd cu H0x Hfx (Hd1,Hd2) (Hu1,Hu2) Hxd Hxu Hed Heu.
destruct (ln_beta beta x) as (ex, Hex).
specialize (Hex H0x).
destruct (total_order_T (bpow ex) xu) as [[Hu|Hu]|Hu].
(* . *)
apply (Rlt_not_le _ _ Hu).
apply Rnd_UP_pt_monotone with (generic_format beta FLXf) x (bpow ex).
exact Hxu.
split.
apply <- FLX_format_generic.
exists (Float beta 1 ex).
split.
apply sym_eq.
apply Rmult_1_l.
apply Zpower_gt_1.
exact Hp.
exact Hp.
split.
apply Rle_refl.
easy.
now apply Rlt_le.
(* . *)
generalize (ulp_pred_succ_pt beta FLXf (FLX_exp_correct prec Hp) x xd xu Hfx Hxd Hxu).
admit.
(* . *)
generalize (ulp_pred_succ_pt beta FLXf (FLX_exp_correct prec Hp) x xd xu Hfx Hxd Hxu).
rewrite Hd1, Hu1.
unfold ulp, F2R.
rewrite Hd2, Hu2.
rewrite (ln_beta_unique beta (Rabs xu) ex).
rewrite (ln_beta_unique beta (Rabs xd) ex).
rewrite (ln_beta_unique beta (Rabs x) ex).
simpl.
rewrite <- Rmult_plus_distr_r.
intros H.
absurd (Fnum cu = Fnum cd + 1)%Z.
intros H'.
apply (Zeven_not_Zodd _ Heu).
rewrite H'.
now apply Zodd_Sn.
apply eq_Z2R.
apply Rmult_eq_reg_r with (bpow (FLXf ex)).
rewrite plus_Z2R.
exact H.
apply Rgt_not_eq.
apply epow_gt_0.
rewrite Rabs_pos_eq.
exact Hex.
now apply Rlt_le.
admit.
admit.
Qed.

Theorem DN_UP_parity_FLX :
  DN_UP_parity_prop FLXf.
Proof.
intros x xd xu cd cu Hfx Hd Hu Hxd Hxu Hed Heu.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].
exact (DN_UP_parity_FLX_pos x xd xu cd cu Hx Hfx Hd Hu Hxd Hxu Hed Heu).
apply Hfx.
rewrite <- Hx.
apply generic_format_0.
assert (Hx': (0 < -x)%R).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive, Ropp_0.
destruct cd as (md, ed).
destruct cu as (mu, eu).
apply DN_UP_parity_FLX_pos with (-x)%R (-xu)%R (-xd)%R (Float beta (-mu) eu) (Float beta (-md) ed).
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
rewrite Zopp_eq_mult_neg_1, Zmult_comm.
now apply Zeven_mult_Zeven_r.
rewrite Zopp_eq_mult_neg_1, Zmult_comm.
now apply Zeven_mult_Zeven_r.
Qed.

Theorem Rnd_NE_pt_FLX :
  forall x f,
  FLX_format beta prec f ->
  ( Rnd_gNE_pt FLXf x f <-> Rnd_NE_pt FLXf x f ).
Proof.
intros x f Hf.
apply Rnd_NE_pt_aux.
exact DN_UP_parity_FLX.
now apply <- FLX_format_generic.
Qed.

End Flocq_rnd_NE_FLX.

End Flocq_rnd_NE.

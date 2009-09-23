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
now rewrite <- ln_beta_opp.
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
  (Zabs (Fnum f) < Zpower (radix_val beta) (projT1 (ln_beta beta x) - Fexp f))%Z.
Proof.
intros x f Hx.
unfold Flocq_rnd_generic.canonic.
destruct (ln_beta beta x) as (ex, H).
simpl.
specialize (H Hx).
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

Definition DN_UP_parity_pos_prop :=
  forall x xd xu cd cu,
  (0 < x)%R ->
  ~ format x ->
  canonic xd cd ->
  canonic xu cu ->
  Rnd_DN_pt format x xd ->
  Rnd_UP_pt format x xu ->
  Zeven (Fnum cd) ->
  Zeven (Fnum cu) ->
  False.

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

Theorem DN_UP_parity_aux :
  DN_UP_parity_pos_prop ->
  DN_UP_parity_prop.
Proof.
intros Hpos x xd xu cd cu Hfx Hd Hu Hxd Hxu Hed Heu.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].
(* . *)
exact (Hpos x xd xu cd cu Hx Hfx Hd Hu Hxd Hxu Hed Heu).
apply Hfx.
rewrite <- Hx.
apply generic_format_0.
(* . *)
assert (Hx': (0 < -x)%R).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive, Ropp_0.
destruct cd as (md, ed).
destruct cu as (mu, eu).
apply Hpos with (-x)%R (-xu)%R (-xd)%R (Float beta (-mu) eu) (Float beta (-md) ed).
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
destruct (ln_beta beta x) as (ex, Hexa).
specialize (Hexa (Rgt_not_eq _ _ H0x)).
generalize Hexa. intros Hex.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ H0x)) in Hex.
assert (Hd4: (bpow (ex - 1) <= Rabs xd < bpow ex)%R).
rewrite Rabs_pos_eq.
split.
apply Hxd.
apply <- FLX_format_generic.
exists (Float beta 1 (ex - 1)).
split.
apply sym_eq.
apply Rmult_1_l.
apply Zpower_gt_1.
exact Hp.
exact Hp.
apply Hex.
apply Rle_lt_trans with (2 := proj2 Hex).
apply Hxd.
apply Hxd.
apply generic_format_0.
now apply Rlt_le.
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
assert (Hu3: cu = Float beta (Zpower (radix_val beta) (prec - 1)) (ex - prec + 1)).
apply canonic_unicity with (1 := conj Hu1 Hu2).
split.
unfold F2R. simpl.
rewrite Z2R_Zpower, <- epow_add.
rewrite <- Hu.
apply f_equal.
ring.
apply Zle_minus_le_0.
now apply (Zlt_le_succ 0).
simpl.
rewrite <- Hu.
rewrite ln_beta_unique with beta (bpow ex) (ex + 1)%Z.
unfold FLX_exp. ring.
rewrite Rabs_pos_eq.
split.
replace (ex + 1 - 1)%Z with ex by ring.
apply Rle_refl.
apply -> epow_lt.
apply Zlt_succ.
apply epow_ge_0.
assert (Hd3: cd = Float beta (Zpower (radix_val beta) prec - 1) (ex - prec)).
apply canonic_unicity with (1 := conj Hd1 Hd2).
generalize (ulp_pred_succ_pt beta FLXf (FLX_exp_correct prec Hp) x xd xu Hfx Hxd Hxu).
intros Hud.
split.
unfold F2R. simpl.
rewrite minus_Z2R.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Z2R_Zpower, <- epow_add.
ring_simplify (prec + (ex - prec))%Z.
rewrite Hu, Hud.
unfold ulp.
rewrite ln_beta_unique with beta x ex.
unfold FLX_exp, F2R.
simpl. ring.
rewrite Rabs_pos_eq.
exact Hex.
now apply Rlt_le.
now apply Zlt_le_weak.
simpl.
now rewrite ln_beta_unique with (1 := Hd4).
rewrite Hd3 in Hed. simpl in Hed.
rewrite Hu3 in Heu. simpl in Heu.
clear -Hp Hed Heu.
destruct (Zeven_odd_dec (radix_val beta)) as [Hr|Hr].
apply Zeven_not_Zodd with (1 := Hed).
apply Zodd_pred.
replace prec with (prec - 1 + 1)%Z by ring.
rewrite Zpower_exp.
apply Zeven_mult_Zeven_r.
unfold Zpower, Zpower_pos.
simpl.
now rewrite Zmult_1_r.
omega.
apply Zle_ge.
apply Zle_succ.
apply Zeven_not_Zodd with (1 := Heu).
clear Hed Heu.
cut (0 <= prec - 1)%Z.
destruct (prec - 1)%Z as [|p|p] ; intros H.
exact I.
simpl.
rewrite Zpower_pos_nat.
induction (nat_of_P p).
exact I.
rewrite (Zpower_nat_is_exp 1 n).
apply Zodd_mult_Zodd.
unfold Zpower_nat. simpl.
now rewrite Zmult_1_r.
exact IHn.
now elim H.
apply Zle_minus_le_0.
now apply (Zlt_le_succ 0).
(* . *)
generalize (ulp_pred_succ_pt beta FLXf (FLX_exp_correct prec Hp) x xd xu Hfx Hxd Hxu).
rewrite Hd1, Hu1.
unfold ulp, F2R.
rewrite Hd2, Hu2.
rewrite ln_beta_unique with beta xu ex.
rewrite ln_beta_unique with (1 := Hd4).
rewrite ln_beta_unique with (1 := Hexa).
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
split.
apply Rle_trans with (1 := proj1 Hex).
apply Hxu.
exact Hu.
apply Rlt_le.
apply Rlt_le_trans with (1 := H0x).
apply Hxu.
Qed.

Theorem Rnd_NE_pt_FLX :
  forall x f,
  FLX_format beta prec f ->
  ( Rnd_gNE_pt FLXf x f <-> Rnd_NE_pt FLXf x f ).
Proof.
intros x f Hf.
apply Rnd_NE_pt_aux.
apply DN_UP_parity_aux.
exact DN_UP_parity_FLX_pos.
now apply <- FLX_format_generic.
Qed.

End Flocq_rnd_NE_FLX.

Section Flocq_rnd_NE_FLT.

Variable prec : Z.
Variable emin : Z.
Variable Hp : Zlt 0 prec.

Notation FLTf := (FLT_exp emin prec).

Theorem FIX_FLT_exp_subnormal :
  forall x, x <> R0 ->
  (Rabs x < bpow (emin + prec))%R ->
  FIX_exp emin (projT1 (ln_beta beta x)) = FLTf (projT1 (ln_beta beta x)).
Proof.
intros x Hx0 Hx.
unfold FIX_exp, FLT_exp.
rewrite Zmax_right.
apply refl_equal.
destruct (ln_beta beta x) as (ex, Hex).
simpl.
cut (ex - 1 < emin + prec)%Z. omega.
apply <- epow_lt.
eapply Rle_lt_trans with (2 := Hx).
now apply Hex.
Qed.

Theorem DN_UP_parity_FLT_pos :
  DN_UP_parity_pos_prop FLTf.
Proof.
intros x xd xu cd cu Hx0 Hfx Hd Hu Hxd Hxu Hed Heu.
destruct (Rlt_or_le (bpow (emin + prec - 1)) x) as [Hx|Hx].
(* . *)
admit.
(* . *)
apply (DN_UP_parity_FIX emin x xd xu cd cu) ; trivial.
intros H.
apply Hfx.
apply generic_format_fun_eq with (2 := H).
apply FIX_FLT_exp_subnormal.
intros H1.
apply Hfx.
rewrite H1.
apply generic_format_0.
rewrite Rabs_pos_eq.
apply Rle_lt_trans with (1 := Hx).
apply -> epow_lt.
apply Zlt_pred.
now apply Rlt_le.
apply canonic_fun_eq with (2 := Hd).
apply sym_eq.
apply FIX_FLT_exp_subnormal.
admit.
rewrite Rabs_pos_eq.
apply Rle_lt_trans with x.
apply Hxd.
apply Rle_lt_trans with (1 := Hx).
apply -> epow_lt.
apply Zlt_pred.
apply Hxd.
apply generic_format_0.
now apply Rlt_le.
apply canonic_fun_eq with (2 := Hu).
apply sym_eq.
apply FIX_FLT_exp_subnormal.
apply Rgt_not_eq.
apply Rlt_le_trans with (1 := Hx0).
apply Hxu.
rewrite Rabs_pos_eq.
apply Rle_lt_trans with (bpow (emin + prec - 1)).
apply Hxu.
admit.
exact Hx.
apply -> epow_lt.
apply Zlt_pred.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hx0).
apply Hxu.
admit.
admit.
Qed.

Theorem Rnd_NE_pt_FLT :
  forall x f,
  FLT_format beta emin prec f ->
  ( Rnd_gNE_pt FLTf x f <-> Rnd_NE_pt FLTf x f ).
Proof.
intros x f Hf.
apply Rnd_NE_pt_aux.
apply DN_UP_parity_aux.
exact DN_UP_parity_FLT_pos.
now apply <- FLT_format_generic.
Qed.

End Flocq_rnd_NE_FLT.

End Flocq_rnd_NE.

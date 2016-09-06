(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2010-2013 Sylvie Boldo
#<br />#
Copyright (C) 2010-2013 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** Translation from Flocq to Pff *)

Require Import Veltkamp.
Require Import Fcore.
Require Import Fappli_IEEE.


Section Bounds.

Variable beta : radix.
Variable p E:Z.
Hypothesis precisionNotZero : (1 < p)%Z.

Definition make_bound := Bound
      (Z.to_pos (Zpower beta p))
      (Z.abs_N E).

Lemma make_bound_Emin: (E <= 0)%Z ->
        ((Z_of_N (dExp (make_bound)))=-E)%Z.
Proof.
simpl.
rewrite Zabs2N.id_abs.
now apply Z.abs_neq.
Qed.

Lemma make_bound_p: 
        Zpos (vNum (make_bound))=(Zpower_nat beta (Zabs_nat p)).
Proof.
unfold make_bound, vNum; simpl.
rewrite Z2Pos.id.
apply Zpower_nat_Zpower.
omega.
generalize (Zpower_gt_0 beta); simpl.
intros T; apply T.
omega.
Qed.


End Bounds.
Section b_Bounds.

Definition bsingle := make_bound radix2 24 (-149)%Z.

Lemma psGivesBound: Zpos (vNum bsingle) = Zpower_nat 2 24.
unfold bsingle; apply make_bound_p.
omega.
Qed.

Definition bdouble := make_bound radix2 53 1074.

Lemma pdGivesBound: Zpos (vNum bdouble) = Zpower_nat 2 53.
unfold bdouble; apply make_bound_p.
omega.
Qed.

End b_Bounds.
Section Equiv.

Variable beta: radix.
Variable b : Fbound.
Variable p : Z.

Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat beta (Zabs_nat p).
Hypothesis precisionNotZero : (1 < p)%Z.


Lemma pff_format_is_format: forall f, Fbounded b f ->
  (generic_format beta (FLT_exp (-dExp b) p) (FtoR beta f)).
intros f Hf.
apply generic_format_FLT; auto with zarith.
exists (Float beta (Float.Fnum f) (Float.Fexp f)).
simpl; split.
unfold F2R, FtoR; simpl.
rewrite <- 2!Z2R_IZR.
rewrite bpow_powerRZ.
reflexivity.
split; destruct Hf.
apply Zlt_le_trans with (1:=H).
rewrite pGivesBound.
rewrite Zpower_Zpower_nat; auto with zarith.
exact H0.
Qed.


Lemma format_is_pff_format: forall r,
  (generic_format beta (FLT_exp (-dExp b) p) r)
  -> exists f, FtoR beta f = r /\ Fbounded b f.
intros r Hr.
apply FLT_format_generic in Hr; auto with zarith.
destruct Hr as (f,(Hf1,(Hf2,Hf3))).
exists (Float.Float (Fnum f) (Fexp f)); split.
rewrite Hf1.
unfold F2R, FtoR; simpl.
rewrite Z2R_IZR.
rewrite bpow_powerRZ.
rewrite Z2R_IZR; reflexivity.
split.
apply Zlt_le_trans with (1:=Hf2).
rewrite pGivesBound.
rewrite Zpower_Zpower_nat; auto with zarith.
exact Hf3.
unfold Prec_gt_0;auto with zarith.
Qed.


Lemma equiv_RNDs_aux: forall z, Zeven z = true -> Even z.
intros z; unfold Zeven, Even.
case z.
intros; exists 0%Z; auto with zarith.
intros p0; case p0.
intros p1 H; contradict H; auto.
intros p1 _.
exists (Zpos p1); auto with zarith.
intros H; contradict H; auto.
intros p0; case p0.
intros p1 H; contradict H; auto.
intros p1 _.
exists (Zneg p1); auto with zarith.
intros H; contradict H; auto.
Qed.

Lemma pff_canonic_is_canonic: forall f, Fcanonic beta b f -> FtoR beta f <> 0 ->
  canonic beta (FLT_exp (- dExp b) p)
    (Float beta (Float.Fnum f) (Float.Fexp f)).
intros f Hf1 Hf2; unfold canonic; simpl.
assert (K:(F2R (Float beta (Float.Fnum f) (Float.Fexp f)) = FtoR beta f)).
unfold FtoR, F2R; simpl.
rewrite bpow_powerRZ; rewrite <- 2!Z2R_IZR; reflexivity.
unfold canonic_exp, FLT_exp.
rewrite K.
destruct (ln_beta beta (FtoR beta f)) as (e, He).
simpl; destruct Hf1.
(* . *)
destruct H as (H1,H2).
cut (Float.Fexp f = e-p)%Z.
intros V; rewrite V.
apply sym_eq; apply Zmax_left.
rewrite <- V; destruct H1; auto with zarith.
assert (e = Float.Fexp f + p)%Z;[idtac|omega].
apply trans_eq with (ln_beta beta (FtoR beta f)).
apply sym_eq; apply ln_beta_unique.
apply He; assumption.
apply ln_beta_unique.
rewrite <- K; unfold F2R; simpl.
rewrite Rabs_mult.
rewrite (Rabs_right (bpow beta (Float.Fexp f))).
2: apply Rle_ge; apply bpow_ge_0.
split.
replace (Float.Fexp f + p - 1)%Z with ((p-1)+Float.Fexp f)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
(* .. *)
apply Rmult_le_reg_l with (Z2R beta).
replace 0%R with (Z2R 0) by reflexivity.
apply Z2R_lt.
apply radix_gt_0.
rewrite <- bpow_plus1.
replace (p-1+1)%Z with (Z_of_nat (Zabs_nat p)).
rewrite <- Z2R_Zpower_nat.
simpl; rewrite <- pGivesBound, 3!Z2R_IZR.
rewrite Rabs_Zabs.
rewrite <- mult_IZR.
apply IZR_le.
rewrite <- (Zabs_eq (beta)).
rewrite <- Zabs.Zabs_Zmult.
assumption.
apply Zlt_le_weak; apply radix_gt_0.
rewrite inj_abs; try ring.
omega.
(* .. *)
rewrite Zplus_comm, bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite <- (inj_abs p);[idtac|omega].
rewrite <- Z2R_Zpower_nat.
simpl; rewrite <- pGivesBound, 2!Z2R_IZR.
rewrite Rabs_Zabs.
apply IZR_lt.
destruct H1; assumption.
(* . *)
destruct H as (H1,(H2,H3)).
rewrite H2.
apply sym_eq; apply Zmax_right.
assert ((e-1) < p-dExp b)%Z;[idtac|omega].
apply lt_bpow with beta.
apply Rle_lt_trans with (Rabs (FtoR beta f)).
apply He; auto.
apply Rlt_le_trans with (FtoR beta (firstNormalPos beta b (Zabs_nat p))).
rewrite <- Fabs_correct.
2: apply radix_gt_0.
apply FsubnormalLtFirstNormalPos; auto with zarith.
apply radix_gt_1.
intros KK; absurd (1 < p)%Z; try assumption.
apply Zle_not_lt; rewrite <- (inj_abs p); omega.
apply FsubnormFabs; auto with zarith.
apply radix_gt_1.
split; [idtac|split]; assumption.
rewrite Fabs_correct; auto with real zarith.
apply radix_gt_0.
unfold firstNormalPos, FtoR, nNormMin.
simpl.
replace (IZR (Zpower_nat beta (Peano.pred (Zabs_nat p)))) with (bpow beta (p-1)).
rewrite <- Z2R_IZR.
rewrite <- (bpow_powerRZ _).
rewrite <- bpow_plus.
apply bpow_le.
omega.
replace (p-1)%Z with (Z_of_nat (Peano.pred (Zabs_nat p))).
rewrite <- Z2R_Zpower_nat.
rewrite Z2R_IZR; reflexivity.
rewrite inj_pred; try omega.
rewrite inj_abs; omega.
intros KK; absurd (1 < p)%Z; try assumption.
apply Zle_not_lt; rewrite <- (inj_abs p); omega.
Qed.


Lemma pff_round_NE_is_round: forall (r:R),
   (FtoR beta (RND_EvenClosest b beta (Zabs_nat p) r)
     =  round beta (FLT_exp (-dExp b) p) rndNE r).
Proof.
intros.
assert (Rnd_NE_pt beta (FLT_exp (-dExp b) p) r
         (round beta (FLT_exp (-dExp b) p) rndNE r)).
apply round_NE_pt; auto with zarith.
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
apply exists_NE_FLT.
now right.
unfold Rnd_NE_pt, Rnd_NG_pt, Rnd_N_pt, NE_prop in H.
destruct H as ((H1,H2),H3).
destruct (format_is_pff_format _ H1) as (f,(Hf1,Hf2)).
rewrite <- Hf1.
generalize (EvenClosestUniqueP b beta (Zabs_nat p)); unfold UniqueP; intros T.
apply sym_eq; apply T with r; auto with zarith; clear T.
apply radix_gt_1.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; omega.
split.
(* *)
split; auto; intros g Hg.
rewrite Hf1.
apply H2.
apply pff_format_is_format; auto.
(* *)
case (Req_dec (FtoR beta (Fnormalize beta b (Zabs_nat p) f))  0%R); intros L.
left.
unfold FNeven, Feven, Even.
exists 0%Z.
rewrite Zmult_0_r.
apply eq_IZR.
apply Rmult_eq_reg_l with (powerRZ beta (Float.Fexp (Fnormalize beta b (Zabs_nat p) f)))%R.
simpl (IZR 0); rewrite Rmult_0_r.
rewrite <- L; unfold FtoR; simpl; ring.
apply powerRZ_NOR; auto with zarith real.
apply Rgt_not_eq; replace 0%R with (IZR 0) by reflexivity.
apply IZR_lt; apply radix_gt_0.
destruct H3.
(* . *)
destruct H as (g,(Hg1,(Hg2,Hg3))).
left.
unfold FNeven, Feven.
apply equiv_RNDs_aux.
replace (Float.Fnum (Fnormalize beta b (Zabs_nat p) f)) with (Fnum g); try assumption.
replace g with (Float beta (Float.Fnum (Fnormalize beta b (Zabs_nat p) f)) (Float.Fexp (Fnormalize beta b (Zabs_nat p) f))).
easy.
apply canonic_unicity with (FLT_exp (- dExp b) p).
2: assumption.
apply pff_canonic_is_canonic.
apply FnormalizeCanonic; auto with zarith real.
apply radix_gt_1.
intros KK; absurd (1 < p)%Z; try assumption.
apply Zle_not_lt; rewrite <- (inj_abs p); omega.
exact L.
rewrite <- Hg1, <- Hf1.
rewrite <- FnormalizeCorrect with beta b (Zabs_nat p) f; auto with zarith.
unfold F2R, FtoR; simpl.
rewrite Z2R_IZR, bpow_powerRZ.
rewrite Z2R_IZR; reflexivity.
apply radix_gt_1.
(* . *)
right; intros q (Hq1,Hq2).
rewrite Hf1.
apply H.
split.
apply pff_format_is_format; auto.
intros g Hg.
destruct (format_is_pff_format _ Hg) as (v,(Hv1,Hv2)).
rewrite <- Hv1.
apply Hq2; auto.
apply RND_EvenClosest_correct; auto with zarith.
apply radix_gt_1.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; omega.
Qed.


Lemma round_NE_is_pff_round: forall (r:R),
   exists f:Float.float, (Fcanonic beta b f /\ (EvenClosest b beta (Zabs_nat p) r f) /\
    FtoR beta f =  round beta (FLT_exp (-dExp b) p) rndNE r).
intros r.
exists (RND_EvenClosest b beta (Zabs_nat p) r).
split.
apply RND_EvenClosest_canonic; auto with zarith.
apply radix_gt_1.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; omega.
split.
apply RND_EvenClosest_correct; auto with zarith.
apply radix_gt_1.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; omega.
apply pff_round_NE_is_round.
Qed.

End Equiv.

Section Equiv_instanc.

Lemma round_NE_is_pff_round_b32: forall (r:R),
   exists f:Float.float, (Fcanonic 2 bsingle f /\ (EvenClosest bsingle 2 24 r f) /\
    FtoR 2 f =  round radix2 (FLT_exp (-149) 24) rndNE r).
apply (round_NE_is_pff_round radix2 bsingle 24).
apply psGivesBound.
omega.
Qed.


Lemma round_NE_is_pff_round_b64: forall (r:R),
   exists f:Float.float, (Fcanonic 2 bdouble f /\ (EvenClosest bdouble 2 53 r f) /\
    FtoR 2 f =  round radix2 (FLT_exp (-1074) 53) rndNE r).
apply (round_NE_is_pff_round radix2 bdouble 53).
apply pdGivesBound.
omega.
Qed.



End Equiv_instanc.

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


Definition nat_to_N (n:nat) := match n with 
   |  0    => N0
   | (S m) => (Npos (P_of_succ_nat m))
   end.

Lemma nat_to_N_correct: forall n:nat, Z_of_N (nat_to_N n)=n.
intros.
intros; induction n; simpl; auto.
Qed.


Definition make_bound (p E:nat) := Bound 
      (P_of_succ_nat (Peano.pred (Zabs_nat (Zpower_nat 2%Z p))))
      (nat_to_N E).

Lemma make_EGivesEmin: forall p E:nat, 
        (Z_of_N (dExp (make_bound p E)))=E.
intros; simpl; apply nat_to_N_correct.
Qed.

Lemma make_pGivesBound: forall p E:nat, 
        Zpos (vNum (make_bound p E))=(Zpower_nat 2 p).
intros.
unfold make_bound, vNum.
apply
 trans_eq
  with
    (Z_of_nat
       (nat_of_P
          (P_of_succ_nat
             (Peano.pred (Zabs_nat (Zpower_nat 2 p)))))).
unfold Z_of_nat in |- *; rewrite nat_of_P_o_P_of_succ_nat_eq_succ;
 auto with zarith.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ; auto with arith zarith.
cut (Zabs (Zpower_nat 2 p) = Zpower_nat 2 p).
intros H; pattern (Zpower_nat 2 p) at 2 in |- *; rewrite <- H.
rewrite Zabs_absolu.
rewrite <- (S_pred (Zabs_nat (Zpower_nat 2 p)) 0);
 auto with arith zarith.
apply lt_Zlt_inv; simpl in |- *; auto with zarith arith.
rewrite <- Zabs_absolu; rewrite H; auto with arith zarith.
apply Zabs_eq; auto with arith zarith.
Qed.

Definition bsingle := make_bound 24 149.

Lemma psGreaterThanOne: 1 < 24.
auto with arith.
Qed.

Lemma psGivesBound: Zpos (vNum bsingle) = Zpower_nat 2 24.
unfold bsingle; apply make_pGivesBound.
Qed.

Definition bdouble := make_bound 53 1074.

Lemma pdGreaterThanOne: 1 < 53.
auto with arith.
Qed.

Lemma pdGivesBound: Zpos (vNum bdouble) = Zpower_nat 2 53.
unfold bdouble; apply make_pGivesBound.
Qed.

End Bounds.


Section Equiv.
Variable b : Fbound.
Variable p : nat.
 
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat 2%Z p.
Hypothesis precisionNotZero : 1 < p.


Lemma equiv_RNDs_aux1: forall f, Fbounded b f ->
  (generic_format radix2 (FLT_exp (-dExp b) p) (FtoR 2 f)).
intros f Hf.
apply generic_format_FLT; auto with zarith.
exists (Float radix2 (Float.Fnum f) (Float.Fexp f)).
simpl; split.
unfold F2R, FtoR; simpl.
rewrite Z2R_IZR.
rewrite bpow_powerRZ.
reflexivity.
split; destruct Hf.
apply Zlt_le_trans with (1:=H).
rewrite pGivesBound.
rewrite Zpower_Zpower_nat; auto with zarith.
rewrite Zabs_nat_Z_of_nat; auto with zarith.
exact H0.
Qed.


Lemma equiv_RNDs_aux2: forall r, 
  (generic_format radix2 (FLT_exp (-dExp b) p) r)
  -> exists f, FtoR 2 f = r /\ Fbounded b f.
intros r Hr.
apply FLT_format_generic in Hr; auto with zarith.
destruct Hr as (f,(Hf1,(Hf2,Hf3))).
exists (Float.Float (Fnum f) (Fexp f)); split.
rewrite Hf1.
unfold F2R, FtoR; simpl.
rewrite Z2R_IZR.
rewrite bpow_powerRZ.
reflexivity.
split.
apply Zlt_le_trans with (1:=Hf2).
rewrite pGivesBound.
rewrite Zpower_Zpower_nat; auto with zarith.
rewrite Zabs_nat_Z_of_nat; auto with zarith.
exact Hf3.
unfold Prec_gt_0;auto with zarith.
Qed.


Lemma equiv_RNDs_aux3: forall z, Zeven z = true -> Even z.
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

Lemma equiv_RNDs_aux4: forall f, Fcanonic 2 b f -> FtoR 2 f <> 0 ->
  canonic radix2 (FLT_exp (- dExp b) p) 
    (Float radix2 (Float.Fnum f) (Float.Fexp f)).
intros f Hf1 Hf2; unfold canonic; simpl.
assert (K:(F2R (Float radix2 (Float.Fnum f) (Float.Fexp f)) = FtoR 2 f)).
unfold FtoR, F2R; simpl.
rewrite bpow_powerRZ; rewrite Z2R_IZR; reflexivity.
unfold canonic_exp, FLT_exp.
rewrite K.
destruct (ln_beta radix2 (FtoR 2 f)) as (e, He).
simpl; destruct Hf1.
(* . *)
destruct H as (H1,H2).
cut (Float.Fexp f = e-p)%Z.
intros V; rewrite V.
apply sym_eq; apply Zmax_left.
rewrite <- V; destruct H1; auto with zarith.
assert (e = Float.Fexp f + p)%Z;[idtac|omega].
apply trans_eq with (ln_beta radix2 (FtoR 2 f)).
apply sym_eq; apply ln_beta_unique.
apply He; assumption.
apply ln_beta_unique.
rewrite <- K; unfold F2R; simpl.
rewrite Rabs_mult.
rewrite (Rabs_right (bpow radix2 (Float.Fexp f))).
2: apply Rle_ge; apply bpow_ge_0.
split.
replace (Float.Fexp f + p - 1)%Z with ((p-1)+Float.Fexp f)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
(* .. *)
apply Rmult_le_reg_l with (Z2R radix2).
auto with real.
rewrite <- bpow_plus1.
replace (p-1+1)%Z with (Z_of_nat p) by ring.
rewrite <- Z2R_Zpower_nat.
simpl; rewrite <- pGivesBound, 2!Z2R_IZR.
rewrite Rabs_Zabs.
replace 2%R with (IZR 2) by (simpl; ring).
rewrite <- mult_IZR.
apply IZR_le.
replace 2%Z with (Zabs 2).
rewrite <- Zabs.Zabs_Zmult.
assumption.
auto with zarith.
(* .. *)
rewrite Zplus_comm, bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
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
apply lt_bpow with radix2.
apply Rle_lt_trans with (Rabs (FtoR 2 f)).
apply He; auto.
apply Rlt_le_trans with (FtoR 2 (firstNormalPos 2 b p)).
rewrite <- Fabs_correct.
apply FsubnormalLtFirstNormalPos; auto with zarith.
apply FsubnormFabs; auto with zarith.
split; [idtac|split]; assumption.
rewrite Fabs_correct; auto with real zarith.
auto with zarith.
unfold firstNormalPos, FtoR, nNormMin.
simpl.
replace (IZR (Zpower_nat 2 (Peano.pred p))) with (bpow radix2 (Peano.pred p)).
rewrite <- (bpow_powerRZ radix2).
rewrite <- bpow_plus.
apply bpow_le.
rewrite inj_pred; try unfold Zpred; auto with zarith arith.
rewrite <- Z2R_Zpower_nat.
rewrite Z2R_IZR; reflexivity.
Qed.


Lemma equiv_RNDs_aux5: forall (r:R),
   (FtoR 2 (RND_EvenClosest b 2 p r) 
     =  round radix2 (FLT_exp (-dExp b) p) rndNE r).
intros.
assert (Rnd_NE_pt radix2 (FLT_exp (-dExp b) p) r
         (round radix2 (FLT_exp (-dExp b) p) rndNE r)).
apply round_NE_pt; auto with zarith.
apply FLT_exp_valid.
unfold Prec_gt_0; auto with zarith.
apply exists_NE_FLT.
right; auto with zarith.
unfold Rnd_NE_pt, Rnd_NG_pt, Rnd_N_pt, NE_prop in H.
destruct H as ((H1,H2),H3).
destruct (equiv_RNDs_aux2 _ H1) as (f,(Hf1,Hf2)).
rewrite <- Hf1.
generalize (EvenClosestUniqueP b 2 p); unfold UniqueP; intros T.
apply sym_eq; apply T with r; auto with zarith; clear T.
split.
(* *)
split; auto; intros g Hg.
rewrite Hf1.
apply H2.
apply equiv_RNDs_aux1; auto.
(* *)
case (Req_dec (FtoR 2 (Fnormalize 2 b p f))  0%R); intros L.
left.
unfold FNeven, Feven, Even.
exists 0%Z.
rewrite Zmult_0_r.
apply eq_IZR.
apply Rmult_eq_reg_l with (powerRZ 2 (Float.Fexp (Fnormalize 2 b p f)))%R.
simpl (IZR 0); rewrite Rmult_0_r.
rewrite <- L; unfold FtoR; simpl; ring.
apply powerRZ_NOR; auto with zarith real.
destruct H3.
(* . *)
destruct H as (g,(Hg1,(Hg2,Hg3))).
left.
unfold FNeven, Feven.
apply equiv_RNDs_aux3.
replace (Float.Fnum (Fnormalize 2 b p f)) with (Fnum g); try assumption.
replace g with (Float radix2 (Float.Fnum (Fnormalize 2 b p f)) (Float.Fexp (Fnormalize 2 b p f))).
easy.
apply canonic_unicity with (FLT_exp (- dExp b) p).
2: assumption.
apply equiv_RNDs_aux4.
apply FnormalizeCanonic; auto with zarith real.
exact L.
rewrite <- Hg1, <- Hf1.
rewrite <- FnormalizeCorrect with 2%Z b p f; auto with zarith.
unfold F2R, FtoR; simpl.
rewrite Z2R_IZR, bpow_powerRZ.
reflexivity.
(* . *)
right; intros q (Hq1,Hq2).
rewrite Hf1.
apply H.
split.
apply equiv_RNDs_aux1; auto.
intros g Hg.
destruct (equiv_RNDs_aux2 _ Hg) as (v,(Hv1,Hv2)).
rewrite <- Hv1.
apply Hq2; auto.
apply RND_EvenClosest_correct; auto with zarith.
Qed.


Lemma equiv_RNDs: forall (r:R),
   exists f:Float.float, (Fcanonic 2 b f /\ (EvenClosest b 2 p r f) /\ 
    FtoR 2 f =  round radix2 (FLT_exp (-dExp b) p) rndNE r).
intros r.
exists (RND_EvenClosest b 2 p r).
split.
apply RND_EvenClosest_canonic; auto with zarith.
split.
apply RND_EvenClosest_correct; auto with zarith.
apply equiv_RNDs_aux5.
Qed.

End Equiv.

Section Equiv_instanc.

Lemma equiv_RNDs_s: forall (r:R),
   exists f:Float.float, (Fcanonic 2 bsingle f /\ (EvenClosest bsingle 2 24 r f) /\ 
    FtoR 2 f =  round radix2 (FLT_exp (-149) 24) rndNE r).
apply equiv_RNDs.
apply psGivesBound.
apply psGreaterThanOne.
Qed.


Lemma equiv_RNDs_d: forall (r:R),
   exists f:Float.float, (Fcanonic 2 bdouble f /\ (EvenClosest bdouble 2 53 r f) /\ 
    FtoR 2 f =  round radix2 (FLT_exp (-1074) 53) rndNE r).
apply equiv_RNDs.
apply pdGivesBound.
apply pdGreaterThanOne.
Qed.



End Equiv_instanc.

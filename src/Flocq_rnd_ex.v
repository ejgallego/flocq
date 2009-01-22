Require Import Flocq_Raux.
Require Import Flocq_defs.

Open Scope R_scope.

Section RND_ex.

Theorem Rnd_DN_pt_unicity :
  forall F : R -> Prop,
  forall x f1 f2 : R,
  Rnd_DN_pt F x f1 -> Rnd_DN_pt F x f2 ->
  f1 = f2.
Proof.
intros F x f1 f2 H1 H2.
apply Rle_antisym.
eapply H2.
now eapply H1.
now eapply H1.
eapply H1.
now eapply H2.
now eapply H2.
Qed.

Theorem Rnd_DN_unicity :
  forall F : R -> Prop,
  forall rnd1 rnd2 : R -> R,
  Rnd_DN F rnd1 -> Rnd_DN F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Proof.
intros F rnd1 rnd2 H1 H2 x.
now eapply Rnd_DN_pt_unicity.
Qed.

Theorem Rnd_UP_pt_unicity :
  forall F : R -> Prop,
  forall x f1 f2 : R,
  Rnd_UP_pt F x f1 -> Rnd_UP_pt F x f2 ->
  f1 = f2.
Proof.
intros F x f1 f2 H2 H1.
apply Rle_antisym.
eapply H2.
now eapply H1.
now eapply H1.
eapply H1.
now eapply H2.
now eapply H2.
Qed.

Theorem Rnd_UP_unicity :
  forall F : R -> Prop,
  forall rnd1 rnd2 : R -> R,
  Rnd_UP F rnd1 -> Rnd_UP F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Proof.
intros F rnd1 rnd2 H1 H2 x.
now eapply Rnd_UP_pt_unicity.
Qed.

Theorem Rnd_DN_UP_pt_sym :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_DN_pt F (-x) (-f) -> Rnd_UP_pt F x f.
Proof.
intros F HF x f H.
rewrite <- (Ropp_involutive f).
repeat split.
apply HF.
apply H.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply H.
intros.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply H.
now apply HF.
now apply Ropp_le_contravar.
Qed.

Theorem Rnd_DN_UP_sym :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall rnd1 rnd2 : R -> R,
  Rnd_DN F rnd1 -> Rnd_UP F rnd2 ->
  forall x, rnd1 (- x) = - rnd2 x.
Proof.
intros F HF rnd1 rnd2 H1 H2 x.
rewrite <- (Ropp_involutive (rnd1 (-x))).
apply f_equal.
apply (Rnd_UP_unicity F (fun x => - rnd1 (-x))) ; trivial.
intros y.
apply Rnd_DN_UP_pt_sym.
apply HF.
rewrite Ropp_involutive.
apply H1.
Qed.

Theorem Rnd_DN_pt_monotone :
  forall F : R -> Prop,
  forall x y f g : R,
  Rnd_DN_pt F x f -> Rnd_DN_pt F y g ->
  x <= y -> f <= g.
Proof.
intros F x y f g (Hx1,(Hx2,_)) (Hy1,(_,Hy2)) Hxy.
apply Hy2.
apply Hx1.
now apply Rle_trans with (2 := Hxy).
Qed.

Theorem Rnd_DN_monotone :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rnd_DN F rnd ->
  MonotoneP rnd.
Proof.
intros F rnd Hr x y Hxy.
now eapply Rnd_DN_pt_monotone.
Qed.

Theorem Rnd_DN_pt_involutive :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_DN_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (_,(Hx1,Hx2)) Hx.
apply Rle_antisym.
exact Hx1.
apply Hx2.
exact Hx.
apply Rle_refl.
Qed.

Theorem Rnd_DN_involutive :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rnd_DN F rnd ->
  InvolutiveP F rnd.
Proof.
intros F rnd Hr.
split.
intros.
eapply Hr.
intros x Hx.
now apply Rnd_DN_pt_involutive with (2 := Hx).
Qed.

Theorem Rnd_UP_pt_monotone :
  forall F : R -> Prop,
  forall x y f g : R,
  Rnd_UP_pt F x f -> Rnd_UP_pt F y g ->
  x <= y -> f <= g.
Proof.
intros F x y f g (Hx1,(_,Hx2)) (Hy1,(Hy2,_)) Hxy.
apply Hx2.
apply Hy1.
now apply Rle_trans with (1 := Hxy).
Qed.

Theorem Rnd_UP_monotone :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rnd_UP F rnd ->
  MonotoneP rnd.
Proof.
intros F rnd Hr x y Hxy.
now eapply Rnd_UP_pt_monotone.
Qed.

Theorem Rnd_UP_pt_involutive :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_UP_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (_,(Hx1,Hx2)) Hx.
apply Rle_antisym.
apply Hx2.
exact Hx.
apply Rle_refl.
exact Hx1.
Qed.

Theorem Rnd_UP_involutive :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rnd_UP F rnd ->
  InvolutiveP F rnd.
Proof.
intros F rnd Hr.
split.
intros.
eapply Hr.
intros x Hx.
now apply Rnd_UP_pt_involutive with (2 := Hx).
Qed.

Theorem Rnd_DN_pt_le_rnd :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rounding_for_Format F rnd -> 
  forall x fd : R,
  Rnd_DN_pt F x fd ->
  fd <= rnd x.
Proof.
intros F rnd (Hr1,(Hr2,Hr3)) x fd Hd.
replace fd with (rnd fd).
apply Hr1.
apply Hd.
apply Hr3.
apply Hd.
Qed.

Theorem Rnd_DN_le_rnd :
  forall F : R -> Prop,
  forall rndd rnd: R -> R,
  Rnd_DN F rndd -> 
  Rounding_for_Format F rnd -> 
  forall x, rndd x <= rnd x.
Proof.
intros F rndd rnd Hd Hr x.
eapply Rnd_DN_pt_le_rnd.
apply Hr.
apply Hd.
Qed.

Theorem Rnd_UP_pt_ge_rnd :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rounding_for_Format F rnd -> 
  forall x fu : R,
  Rnd_UP_pt F x fu ->
  rnd x <= fu.
Proof.
intros F rnd (Hr1,(Hr2,Hr3)) x fu Hu.
replace fu with (rnd fu).
apply Hr1.
apply Hu.
apply Hr3.
apply Hu.
Qed.

Theorem Rnd_UP_ge_rnd :
  forall F : R -> Prop,
  forall rndu rnd: R -> R,
  Rnd_UP F rndu ->
  Rounding_for_Format F rnd -> 
  forall x, rnd x <= rndu x.
Proof.
intros F rndu rnd Hu Hr x.
eapply Rnd_UP_pt_ge_rnd.
apply Hr.
apply Hu.
Qed.

Lemma Only_DN_or_UP :
  forall F : R -> Prop,
  forall x fd fu f : R,
  Rnd_DN_pt F x fd -> Rnd_UP_pt F x fu ->
  F f -> (fd <= f <= fu)%R ->
  f = fd \/ f = fu.
Proof.
intros F x fd fu f Hd Hu Hf ([Hdf|Hdf], Hfu).
2 : now left.
destruct Hfu.
2 : now right.
destruct (Rle_or_lt x f).
elim Rlt_not_le with (1 := H).
now apply Hu.
elim Rlt_not_le with (1 := Hdf).
apply Hd ; auto with real.
Qed.

Theorem Rnd_DN_or_UP_pt :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rounding_for_Format F rnd ->
  forall x fd fu : R,
  Rnd_DN_pt F x fd -> Rnd_UP_pt F x fu ->
  rnd x = fd \/ rnd x = fu.
Proof.
intros F rnd Hr x fd fu Hd Hu.
eapply Only_DN_or_UP ; try eassumption.
apply Hr.
split.
eapply Rnd_DN_pt_le_rnd ; eassumption.
eapply Rnd_UP_pt_ge_rnd ; eassumption.
Qed.

Theorem Rnd_DN_or_UP :
  forall F : R -> Prop,
  forall rndd rndu rnd : R -> R,
  Rnd_DN F rndd -> Rnd_UP F rndu ->
  Rounding_for_Format F rnd ->
  forall x, rnd x = rndd x \/ rnd x = rndu x.
Proof.
intros F rndd rndu rnd Hd Hu Hr x.
eapply Rnd_DN_or_UP_pt.
apply Hr.
apply Hd.
apply Hu.
Qed.

Theorem Rnd_N_pt_DN_or_UP :
  forall F : R -> Prop,
  forall x fd fu f : R,
  Rnd_DN_pt F x fd -> Rnd_UP_pt F x fu ->
  Rnd_N_pt F x f ->
  f = fd \/ f = fu.
Proof.
intros F x fd fu f Hd Hu Hf.
eapply Only_DN_or_UP ; try eassumption.
apply Hf.
split.
(* fd <= f *)
destruct (Rle_or_lt x f).
apply Rle_trans with (2 := H).
apply Hd.
assert (Hd' := proj2 Hf fd).
apply Ropp_le_cancel.
apply Rplus_le_reg_l with x.
replace (x + -f) with (Rabs (f - x)).
replace (x + -fd) with (Rabs (fd - x)).
apply Hd'.
apply Hd.
rewrite Rabs_left1.
ring.
apply Rle_minus.
apply Hd.
rewrite Rabs_left.
ring.
now apply Rlt_minus.
(* f <= fu *)
destruct (Rle_or_lt x f).
assert (Hu' := proj2 Hf fu).
apply Rplus_le_reg_l with (-x).
replace (-x + f) with (Rabs (f - x)).
replace (-x + fu) with (Rabs (fu - x)).
apply Hu'.
apply Hu.
rewrite Rabs_pos_eq.
ring.
apply Rle_0_minus.
apply Hu.
rewrite Rabs_pos_eq.
ring.
now apply Rle_0_minus.
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
apply Hu.
Qed.

Theorem Rnd_N_pt_monotone :
  forall F : R -> Prop,
  forall x y f g : R,
  Rnd_N_pt F x f -> Rnd_N_pt F y g ->
  x < y -> f <= g.
Proof.
intros F x y f g (Hf,Hx) (Hg,Hy) Hxy.
apply Rnot_lt_le.
intros Hgf.
assert (Hfgx := Hx g Hg).
assert (Hgfy := Hy f Hf).
clear F Hf Hg Hx Hy.
destruct (Rle_or_lt x g) as [Hxg|Hgx].
(* x <= g < f *)
apply Rle_not_lt with (1 := Hfgx).
rewrite 2!Rabs_pos_eq.
now apply Rplus_lt_compat_r.
apply Rle_0_minus.
apply Rlt_le.
now apply Rle_lt_trans with (1 := Hxg).
now apply Rle_0_minus.
assert (Hgy := Rlt_trans _ _ _ Hgx Hxy).
destruct (Rle_or_lt f y) as [Hfy|Hyf].
(* g < f <= y *)
apply Rle_not_lt with (1 := Hgfy).
rewrite (Rabs_left (g - y)).
2: now apply Rlt_minus.
rewrite Rabs_left1.
apply Ropp_lt_contravar.
now apply Rplus_lt_compat_r.
now apply Rle_minus.
(* g < x < y < f *)
rewrite Rabs_left, Rabs_pos_eq, Ropp_minus_distr in Hgfy.
rewrite Rabs_pos_eq, Rabs_left, Ropp_minus_distr in Hfgx.
apply Rle_not_lt with (1 := Rplus_le_compat _ _ _ _ Hfgx Hgfy).
apply Rminus_lt.
ring_simplify.
apply Rlt_minus.
apply Rmult_lt_compat_l.
now apply (Z2R_lt 0 2).
exact Hxy.
now apply Rlt_minus.
apply Rle_0_minus.
apply Rlt_le.
now apply Rlt_trans with (1 := Hxy).
apply Rle_0_minus.
now apply Rlt_le.
now apply Rlt_minus.
Qed.

Theorem Rnd_N_monotone :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rnd_N F rnd ->
  MonotoneP rnd.
Proof.
intros F rnd Hr x y [Hxy|Hxy].
now apply Rnd_N_pt_monotone with F x y.
rewrite Hxy.
apply Rle_refl.
Qed.

Theorem Rnd_N_pt_involutive :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_N_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (_,Hf) Hx.
apply Rminus_diag_uniq.
destruct (Req_dec (f - x) 0) as [H|H].
exact H.
elim Rabs_no_R0 with (1 := H).
apply Rle_antisym.
replace 0 with (Rabs (x - x)).
now apply Hf.
unfold Rminus.
rewrite Rplus_opp_r.
apply Rabs_R0.
apply Rabs_pos.
Qed.

Theorem Rnd_N_involutive :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rnd_N F rnd ->
  InvolutiveP F rnd.
Proof.
intros F rnd Hr.
split.
intros x.
eapply Hr.
intros x Hx.
now apply Rnd_N_pt_involutive with F.
Qed.

Theorem Rnd_NA_pt_involutive :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_NA_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (Hf,_) Hx.
now apply Rnd_N_pt_involutive with F.
Qed.

Theorem Rnd_NA_involutive :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rnd_NA F rnd ->
  InvolutiveP F rnd.
Proof.
intros F rnd Hr.
split.
intros x.
eapply Hr.
intros x Hx.
now apply Rnd_NA_pt_involutive with F.
Qed.

Theorem Rnd_0 :
  forall F : R -> Prop,
  forall rnd : R -> R, 
  F 0 ->  
  Rounding_for_Format F rnd ->
  rnd 0 = 0.
Proof.
intros F rnd H0 (_,H2).
now apply H2.
Qed.

Theorem Rnd_pos_imp_pos :
  forall F : R -> Prop,
  forall rnd : R -> R, 
  F 0 ->  
  Rounding_for_Format F rnd ->
  forall x, 0 <= x -> 0 <= rnd x.
Proof.
intros F rnd H0 H x H'.
rewrite <- Rnd_0 with (2 := H) ; trivial.
now apply H.
Qed.

Theorem Rnd_neg_imp_neg :
  forall F : R -> Prop,
  forall rnd : R -> R, 
  F 0 ->  
  Rounding_for_Format F rnd ->
  forall x, x <= 0 -> rnd x <= 0.
Proof.
intros F rnd H0 H x H'.
rewrite <- Rnd_0 with (2 := H) ; trivial.
now apply H.
Qed.

(* ensures a real number can always be rounded toward -inf *)
Definition satisfies_DN (F : R -> Prop) :=
  exists rnd : R-> R, Rnd_DN F rnd.

Definition satisfies_any (F : R -> Prop) :=
  F 0%R /\ (forall x : R, F x -> F (-x)%R) /\
     satisfies_DN F.

Theorem satisfies_any_imp_UP :
  forall F : R -> Prop,
  satisfies_any F ->
  exists rnd : R -> R, Rnd_UP F rnd.
Proof.
intros F (H1,(H2,(rnd,H3))).
exists (fun x => -rnd(-x)).
intros x.
apply Rnd_DN_UP_pt_sym.
apply H2.
now rewrite Ropp_involutive.
Qed.

Theorem satisfies_any_imp_ZR :
  forall F : R -> Prop,
  satisfies_any F ->
  exists rnd : R -> R, Rnd_ZR F rnd.
Proof.
intros F (H1,(H2,(rnd,H3))).
exists (fun x =>  match Rle_dec 0 x with
  | left _  => rnd x
  | right _ => - rnd (-x)
  end).
assert (K : Rounding_for_Format F rnd).
split.
now apply Rnd_DN_monotone with F.
now apply Rnd_DN_involutive.
intros x.
destruct (Rle_dec 0 x) as [Hx|Hx] ; split.
(* positive or zero *)
intros _.
apply H3.
intros Hx'.
replace x with 0 by now apply Rle_antisym.
rewrite Rnd_0 with F rnd ; trivial.
repeat split ; auto with real.
(* negative *)
intros Hx'.
elim (Hx Hx').
intros Hx'.
apply Rnd_DN_UP_pt_sym.
apply H2.
rewrite Ropp_involutive.
apply H3.
Qed.

Theorem satisfies_any_imp_NA :
  forall F : R -> Prop,
  satisfies_any F ->
  exists rnd : R -> R,
  Rnd_NA F rnd.
Proof.
intros F Hany.
assert (H' := Hany).
destruct H' as (H1,(H2,(rndd,Hd))).
destruct (satisfies_any_imp_UP F Hany) as (rndu, Hu).
exists (fun x =>
  match total_order_T (Rabs (rndu x - x)) (Rabs (rndd x - x)) with
  | inleft (left  _ ) => rndu x
  | inleft (right _ ) => match (Rle_dec (Rabs (rndd x)) (Rabs (rndu x))) with
                            left  _ => rndu x
                          | right _ => rndd x
                          end
  | inright _         => rndd x
  end).
split.
(* *** nearest *)
destruct (total_order_T (Rabs (rndu x - x)) (Rabs (rndd x - x))) as [[H|H]|H].
(* |up(x) - x| < [dn(x) - x| *)
destruct (Hu x) as (H3,(H4,H5)).
split.
exact H3.
intros.
destruct (Rle_or_lt x g).
rewrite Rabs_right.
2 : apply Rge_minus ; apply Rle_ge ; exact H4.
rewrite Rabs_right.
2 : apply Rge_minus ; apply Rle_ge ; exact H6.
apply Rplus_le_compat_r.
now apply H5.
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
do 2 rewrite <- (Rabs_minus_sym x).
rewrite Rabs_right.
rewrite Rabs_right.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
now eapply Hd ;auto with real.
apply Rge_minus.
apply Rle_ge.
now left.
apply Rge_minus.
apply Rle_ge.
now eapply Hd.
(* |up(x) - x| = [dn(x) - x| *)
destruct (Rle_dec (Rabs (rndd x)) (Rabs (rndu x))) as [H'|H'].
(* - |dn(x)| <= |up(x)| *)
split.
now eapply Hu.
intros.
destruct (Rle_or_lt x g).
rewrite Rabs_right.
rewrite Rabs_right.
apply Rplus_le_compat_r.
now eapply Hu.
apply Rge_minus.
now apply Rle_ge.
apply Rge_minus.
apply Rle_ge.
now eapply Hu.
rewrite H.
do 2 rewrite <- (Rabs_minus_sym x).
rewrite Rabs_right.
rewrite Rabs_right.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
now eapply Hd ; auto with real.
apply Rge_minus.
apply Rle_ge.
now left.
apply Rge_minus.
apply Rle_ge.
now eapply Hd.
(* - |dn(x)| > |up(x)| *)
split.
now eapply Hd.
intros.
destruct (Rle_or_lt x g).
rewrite <- H.
rewrite Rabs_right.
rewrite Rabs_right.
apply Rplus_le_compat_r.
now eapply Hu.
apply Rge_minus.
now apply Rle_ge.
apply Rge_minus.
apply Rle_ge.
now eapply Hu.
rewrite Rabs_left1.
rewrite Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
now eapply Hd ; auto with real.
auto with real.
apply Rle_minus.
now eapply Hd.
(* |up(x) - x| > [dn(x) - x| *)
destruct (Hd x) as (H3,(H4,H5)).
split.
exact H3.
intros.
destruct (Rle_or_lt x g).
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
repeat rewrite Rabs_right.
apply Rplus_le_compat_r.
now eapply Hu.
apply Rge_minus.
now apply Rle_ge.
apply Rge_minus.
apply Rle_ge.
now eapply Hu.
repeat rewrite Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
now eapply Hd ; auto with real.
auto with real.
apply Rle_minus.
now eapply Hd.
(* *** away *)
intros f Hf.
destruct (Rnd_N_pt_DN_or_UP F x (rndd x) (rndu x) f) as [K|K] ; trivial.
rewrite K.
destruct (total_order_T (Rabs (rndu x - x)) (Rabs (rndd x - x))) as [[H|H]|H] ;
  try apply Rle_refl.
elim Rlt_not_le with (1 := H).
rewrite <- K.
apply Hf.
eapply Hu.
destruct (Rle_dec (Rabs (rndd x)) (Rabs (rndu x))) ; auto with real.
rewrite K.
destruct (total_order_T (Rabs (rndu x - x)) (Rabs (rndd x - x))) as [[H|H]|H] ;
  try apply Rle_refl.
destruct (Rle_dec (Rabs (rndd x)) (Rabs (rndu x))) ; auto with real.
elim Rgt_not_le with (1 := H).
rewrite <- K.
apply Hf.
eapply Hd.
Qed.


(*
(* symmetric sets are simpler *)
Theorem satisfies_DN_imp_UP :
  forall is_float : R -> Prop,
  ( forall x : R, is_float x -> is_float (-x)%R ) ->
  satisfies_DN is_float ->
  satisfies_DN_UP is_float.
Proof.
intros is_float Hneg Hdn.
split.
apply Hdn.
intros x.
destruct (Hdn (-x)%R) as (yn,(H1,(H2,H3))).
exists (-yn)%R.
repeat split.
now apply Hneg.
rewrite <- (Ropp_involutive x).
now apply Ropp_le_contravar.
intros z Hz Hxz.
rewrite <- (Ropp_involutive z).
apply Ropp_le_contravar.
apply H3.
now apply Hneg.
now apply Ropp_le_contravar.
Qed.

Theorem Rnd_DN_is_rounding :
  forall is_float : R -> Prop,
  satisfies_DN is_float ->
  RoundedModeP (Rnd_DN is_float) /\ Compatible_With_Format is_float (Rnd_DN is_float).
Proof.
intros is_float K.
repeat split ; try apply Rle_refl ; trivial.
(* monotone *)
intros x y f g Hx Hy Hxy.
eapply Hy.
eapply Hx.
apply Rle_trans with (2 := Hxy).
eapply Hx.
(* . *)
eapply H.
intros Hx.
eapply Hx.
Qed.




Theorem exp_ln_powerRZ :
 forall u v : Z, (0 < u)%Z -> exp (ln (IZR u) * (IZR v)) = powerRZ (IZR u) v.
admit.
Qed.

(*
Theorem exp_monotone : forall x y : R, (x <= y)%R -> (exp x <= exp y)%R.
intros x y H; case H; intros H2.
left; apply exp_increasing; auto.
right; auto with real.
Qed.*)


Definition floor_int (r : R) :=(up r-1)%Z.


Theorem floor_int_pos : forall r : R, (0 <= r)%R -> (0 <=  IZR (floor_int r))%R.
Proof.
intros r H1; unfold floor_int in |- *.
generalize (archimed r); intros T; elim T; intros H3 H2; clear T.
replace 0%R with (IZR 0); auto with real; apply IZR_le.
assert (0 < up r)%Z; auto with zarith.
apply lt_IZR; apply Rle_lt_trans with r; auto with real zarith.
Qed.


Theorem  floor_int_correct1 : forall r : R, (IZR (floor_int r) <= r)%R. 
Proof.
intros r; unfold  floor_int in |- *.
generalize (archimed r); intros T; elim T; intros H1 H2; clear T.
apply Rplus_le_reg_l with (1 + - r)%R.
ring_simplify (1 + - r + r)%R.
apply Rle_trans with (2 := H2).
unfold Zminus; rewrite plus_IZR; right; simpl in |- *; ring.
Qed.

Theorem floor_int_correct2 : forall r : R, (r < IZR (floor_int r+1))%R.
intros r; unfold floor_int in |- *.
generalize (archimed r); intros T; elim T; intros H1 H2; clear T.
ring_simplify (up r - 1 + 1)%Z; auto.
Qed.

Theorem floor_int_correct3 : forall r : R, (r - 1 < IZR (floor_int r))%R.
intros r; unfold floor_int in |- *.
generalize (archimed r); intros T; elim T; intros H1 H2; clear T.
unfold Rminus, Zminus; rewrite plus_IZR; simpl in |- *; auto with real. 
Qed.


Variable radix emin prec : Z.


Definition RND_DN_pos_fn (r : R) :=
  match Rle_dec (powerRZ (IZR radix) (prec-1+emin)) r with
  | left _ =>
      let e := floor_int (ln r / ln (IZR radix) + IZR (- prec+1)) in
      Float radix (floor_int (r * powerRZ (IZR radix) (- e))) e
  | right _ => Float radix (floor_int (r * powerRZ (IZR radix) (-emin))) emin
  end.

Variable radix_gt_0 : (0 < radix)%Z.

Lemma FLT_format_satisfies_DN_aux:
 forall x : R, (0 <= x)%R -> exists f : R, Rnd_DN (FLT_format radix emin prec) x f.
Proof.
intros; exists (F2R (RND_DN_pos_fn x)); split.
exists (RND_DN_pos_fn x); split; auto; split.
unfold RND_DN_pos_fn; case (Rle_dec (powerRZ (IZR radix) (prec-1+emin)) x); simpl; intros H1.
rewrite Zabs_eq.
2: apply le_IZR; apply floor_int_pos; apply Rmult_le_pos; auto.
2: admit. (* cf apres *)
apply lt_IZR.
apply Rle_lt_trans with (1:=floor_int_correct1 _).
rewrite <- exp_ln_powerRZ; auto.
apply Rlt_le_trans with  (x *
    (exp (-ln x) * exp (ln (IZR radix) * IZR (prec))))%R.
apply Rmult_lt_compat_l; auto with real.
apply Rlt_le_trans with (2:=H1); auto with real zarith.
admit. (* cf apres *)
rewrite <- exp_plus.
apply exp_increasing.
apply Rmult_lt_reg_l with (/ln (IZR radix))%R.
admit.
apply Rle_lt_trans with (IZR (- floor_int (ln x / ln (IZR radix) + IZR (- prec+1)))).
right; field.
admit.
apply Rlt_le_trans with (-(ln x / ln (IZR radix) - IZR (prec)))%R.
2: right; field.
2: admit.
rewrite Ropp_Ropp_IZR.
apply Ropp_lt_contravar.
apply Rle_lt_trans with (2:= floor_int_correct3 _).
rewrite plus_IZR; rewrite Ropp_Ropp_IZR; simpl; right; ring.
rewrite exp_Ropp; rewrite exp_ln; auto.
2: admit.
rewrite  exp_ln_powerRZ.
admit.
auto.
rewrite Zabs_eq.
2: apply le_IZR; apply floor_int_pos; apply Rmult_le_pos; auto.
2: admit. (* cf apres *)
apply lt_IZR.
apply Rle_lt_trans with (1:=floor_int_correct1 _).
apply Rlt_le_trans with (powerRZ (IZR radix) (prec - 1 + emin)* powerRZ (IZR radix) (- emin))%R.
apply Rmult_lt_compat_r.
admit.
auto with real.
rewrite <- powerRZ_add; auto with real.
(* apply Rle_ powerRZ.*)
admit.
admit.
unfold RND_DN_pos_fn; case (Rle_dec (powerRZ (IZR radix) (prec-1+emin)) x); 
  simpl; auto with zarith; intros H1.
assert (emin-1  < floor_int (ln x / ln (IZR radix) + IZR (- prec + 1)))%Z; auto with zarith.
apply lt_IZR.
apply Rle_lt_trans with (2:= floor_int_correct3 _).
apply Rplus_le_reg_l with (IZR prec).
apply Rmult_le_reg_l with (ln (IZR radix)).
admit.
apply Rle_trans with (ln x).
exp
ln


rewrite <- exp_ln_powerRZ; auto.
apply Rlt_le_trans with  (x *
    (exp (-ln x) * exp (ln (IZR radix) * IZR (prec))))%R.
apply Rmult_lt_compat_l; auto with real.
apply Rlt_le_trans with (2:=H1); auto with real zarith.
admit. (* cf apres *)
rewrite <- exp_plus.
apply exp_increasing.
apply Rmult_lt_reg_l with (/ln (IZR radix))%R.
admit.
apply Rle_lt_trans with (IZR (- floor_int (ln x / ln (IZR radix) + IZR (- prec+1)))).
right; field.
admit.
apply Rlt_le_trans with (-(ln x / ln (IZR radix) - IZR (prec)))%R.
2: right; field.
2: admit.
rewrite Ropp_Ropp_IZR.
apply Ropp_lt_contravar.
apply Rle_lt_trans with (2:= floor_int_correct3 _).
rewrite plus_IZR; rewrite Ropp_Ropp_IZR; simpl; right; ring.
rewrite exp_Ropp; rewrite exp_ln; auto.
2: admit.
rewrite  exp_ln_powerRZ.
admit.
auto.



      (ln (IZR radix) *
       IZR (- (ln x / ln (IZR radix) + IZR (- Zpred prec))))


apply Rle_lt_trans with (x *
    powerRZ (IZR radix)
      (- floor_int (ln x / ln (IZR radix) + IZR (- Zpred prec)))

rewrite powerRZ_add; auto with real zarith.


rewrite Zpower_powerRZ; rewrite <- Rabsolu_Zabs.



unfold FLT_format.



Theorem FLT_format_satisfies_DN : satisfies_DN (FLT_format radix emin prec).
Proof.
unfold satisfies_DN.
intros.


Theorem FLT_format_satisfies_DN_UP :
  satisfies_DN_UP (FLT_format radix emin prec).
Proof.
intros.
assert (Hdn: satisfies_DN (FLT_format radix emin prec)) by admit.
apply satisfies_DN_imp_UP.
intros x (f,(Hx,(Hm,He))).
exists (Float radix (-(Fnum f))%Z (Fexp f)).
repeat split.
rewrite Hx.
unfold F2R.
simpl.
rewrite Ropp_Ropp_IZR.
now rewrite Ropp_mult_distr_l_reverse.
simpl.
now rewrite Zabs_Zopp.
exact He.
exact Hdn.
Qed.

Variable radix_gt_0 : (0 < radix)%Z.

Lemma powerRZ_radix_ge_0 :
  forall e : Z, (0 <= powerRZ (IZR radix) e)%R.
Proof.
intros.
apply powerRZ_le.
change R0 with (IZR 0).
apply IZR_lt.
exact radix_gt_0.
Qed.

Lemma powerRZ_radix_gt_0 :
  forall e : Z, (0 < powerRZ (IZR radix) e)%R.
Proof.
intros.
apply powerRZ_lt.
change R0 with (IZR 0).
apply IZR_lt.
exact radix_gt_0.
Qed.

Lemma IZR_radix_neq_0 :
  IZR radix <> R0.
Proof.
apply Rgt_not_eq.
change R0 with (IZR 0).
apply IZR_lt.
exact radix_gt_0.
Qed.

Theorem FIX_format_satisfies_DN_UP :
  satisfies_DN_UP (FIX_format radix emin).
Proof.
intros.
assert (Hdn: satisfies_DN (FIX_format radix emin)).
intros x.
pose (m := up (x * powerRZ (IZR radix) (Zopp emin))).
pose (f := Float radix (m - 1) emin).
exists (F2R f).
split.
now exists f.
split.
unfold F2R, f, m.
simpl.
pattern x at 2 ; rewrite <- Rmult_1_r.
change R1 with (powerRZ (IZR radix) 0).
rewrite <- (Zplus_opp_l emin).
rewrite powerRZ_add.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
apply powerRZ_radix_ge_0.
generalize (x * powerRZ (IZR radix) (- emin))%R.
clear.
intros.
unfold Zminus.
rewrite plus_IZR.
simpl.
pattern r at 2 ; replace r with ((r + 1) + -1)%R by ring.
apply Rplus_le_compat_r.
replace (IZR (up r)) with (r + (IZR (up r) - r))%R by ring.
apply Rplus_le_compat_l.
eapply for_base_fp.
apply IZR_radix_neq_0.
intros g (fx,(H1,H2)) H3.
rewrite H1.
unfold F2R.
rewrite H2.
simpl (Fexp f).
apply Rmult_le_compat_r.
apply powerRZ_radix_ge_0.
apply IZR_le.
apply Zlt_succ_le.
apply lt_IZR.
eapply Rmult_lt_reg_l.
apply (powerRZ_radix_gt_0 emin).
do 2 rewrite (Rmult_comm (powerRZ (IZR radix) emin)).
apply Rle_lt_trans with x.
rewrite <- H2.
fold (F2R fx).
now rewrite <- H1.
pattern x ; rewrite <- Rmult_1_r.
change R1 with (powerRZ (IZR radix) 0).
rewrite <- (Zplus_opp_l emin).
rewrite powerRZ_add.
rewrite <- Rmult_assoc.
apply Rmult_lt_compat_r.
apply powerRZ_radix_gt_0.
simpl.
change (m - 1)%Z with (Zpred m).
rewrite <- Zsucc_pred.
eapply archimed.
apply IZR_radix_neq_0.
(* . *)
apply satisfies_DN_imp_UP.
intros x (f,(Hx,He)).
exists (Float radix (-(Fnum f))%Z (Fexp f)).
repeat split.
rewrite Hx.
unfold F2R.
simpl.
rewrite Ropp_Ropp_IZR.
now rewrite Ropp_mult_distr_l_reverse.
exact He.
exact Hdn.
Qed.

Theorem Rnd_DN_is_FLT_rounding :
  FLT_RoundedModeP radix emin prec (Rnd_DN (FLT_format radix emin prec)).
Proof.
intros.
apply Rnd_DN_is_rounding.
eapply FLT_format_satisfies_DN_UP.
Qed.

Theorem Rnd_DN_is_FIX_rounding :
  FIX_RoundedModeP radix emin (Rnd_DN (FIX_format radix emin)).
Proof.
intros.
apply Rnd_DN_is_rounding.
eapply FIX_format_satisfies_DN_UP.
Qed.
*)

Variable beta: radix.

Notation bpow := (epow beta).


End RND_ex.
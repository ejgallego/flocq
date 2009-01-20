Require Import Flocq_Raux.
Require Import Flocq_defs.

Open Scope R_scope.

Section RND_ex.

Theorem Rnd_DN_unicity :
  forall D F : R -> Prop,
  forall rnd1 rnd2 : R -> R,
  Rnd_DN D F rnd1 -> Rnd_DN D F rnd2 ->
  forall x, D x -> rnd1 x = rnd2 x.
Proof.
intros D F rnd1 rnd2 H1 H2 x Hx.
apply Rle_antisym.
eapply H2.
exact Hx.
now eapply H1.
now eapply H1.
eapply H1.
exact Hx.
now eapply H2.
now eapply H2.
Qed.

Theorem Rnd_UP_unicity :
  forall D F : R -> Prop,
  forall rnd1 rnd2 : R -> R,
  Rnd_UP D F rnd1 -> Rnd_UP D F rnd2 ->
  forall x, D x -> rnd1 x = rnd2 x.
Proof.
intros D F rnd1 rnd2 H1 H2 x Hx.
apply Rle_antisym.
eapply H1.
exact Hx.
now eapply H2.
now eapply H2.
eapply H2.
exact Hx.
now eapply H1.
now eapply H1.
Qed.

Theorem Rnd_DN_UP_sym :
  forall D F : R -> Prop,
  ( forall x, D x -> D (- x) ) ->
  ( forall x, F x -> F (- x) ) ->
  forall rnd1 rnd2 : R -> R,
  Rnd_DN D F rnd1 -> Rnd_UP D F rnd2 ->
  forall x, D x -> rnd1 (- x) = - rnd2 x.
Proof.
intros D F HD HF rnd1 rnd2 H1 H2 x Hx.
rewrite <- (Ropp_involutive (rnd1 (- x))).
apply f_equal.
apply (Rnd_UP_unicity D F (fun x => - rnd1 (- x))) ; trivial.
intros y Hy.
destruct (H1 (- y)) as (H3,(H4,H5)).
now apply HD.
repeat split.
now apply HD.
now apply HF.
apply Ropp_le_cancel.
now rewrite Ropp_involutive.
intros g Hg Hyg.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply H5.
now apply HF.
now apply Ropp_le_contravar.
Qed.

(*
Theorem Rnd_DN_involutive :
  forall D F : R -> Prop,
  forall rnd : R -> R,
  Rnd_DN D F rnd ->
  InvolutiveP (fun x => F x /\ D x) rnd.
Proof.
intros D F rnd Hrnd x (Hx1, Hx2).
apply (Rnd_DN_unicity D F (fun x => rnd (rnd x))) ; trivial.
clear -Hrnd.
intros x Hx.
destruct (Hrnd (rnd x)) as (H1,(H2,(H3,H4))).
now eapply Hrnd.
repeat split ; trivial.
apply Rle_trans with (1 := H3).
now eapply Hrnd.
intros g Hg Hgx.
apply H4.
exact Hg.
now eapply Hrnd.
Qed.
*)

Theorem Rnd_DN_monotone :
  forall D F : R -> Prop,
  forall rnd : R -> R,
  Rnd_DN D F rnd ->
  MonotoneP D rnd.
Proof.
intros D F rnd Hrnd x y Hx Hy Hxy.
destruct (Rle_or_lt x (rnd y)).
apply Rle_trans with (2 := H).
now eapply Hrnd.
eapply Hrnd.
apply Hy.
now eapply Hrnd.
apply Rle_trans with (2 := Hxy).
now eapply Hrnd.
Qed.

Theorem Rnd_UP_monotone :
  forall D F : R -> Prop,
  forall rnd : R -> R,
  Rnd_UP D F rnd ->
  MonotoneP D rnd.
Proof.
intros D F rnd Hrnd x y Hx Hy Hxy.
destruct (Rle_or_lt (rnd x) y).
apply Rle_trans with (1 := H).
now eapply Hrnd.
eapply Hrnd.
apply Hx.
now eapply Hrnd.
apply Rle_trans with (1 := Hxy).
now eapply Hrnd.
Qed.

(*
Theorem Rnd_UP_involutive :
  forall D F : R -> Prop,
  forall rnd : R -> R,
  Rnd_UP D F rnd ->
  InvolutiveP (fun x => F x /\ D x) rnd.
Proof.
intros D F rnd Hrnd x (Hx1, Hx2).
apply (Rnd_UP_unicity D F (fun x => rnd (rnd x))) ; trivial.
clear -Hrnd.
intros x Hx.
destruct (Hrnd (rnd x)) as (H1,(H2,(H3,H4))).
now eapply Hrnd.
repeat split ; trivial.
apply Rle_trans with (2 := H3).
now eapply Hrnd.
intros g Hg Hgx.
apply H4.
exact Hg.
now eapply Hrnd.
Qed.
*)

Theorem Rnd_DN_le_rnd :
  forall D F : R -> Prop,
  forall rndd rnd: R -> R,
  Rnd_DN D F rndd -> 
  Rounding_for_Format D F rnd -> 
  forall x, D x -> rndd x <= rnd x.
Proof.
intros D F rndd rnd Hd (Hr1,(Hr2,Hr3)) x Hx.
destruct (Hd x Hx) as (H1,(H2,(H3,H4))).
replace (rndd x) with (rnd (rndd x)).
now apply Hr1.
now apply Hr3.
Qed.

Theorem Rnd_UP_ge_rnd :
  forall D F : R -> Prop,
  forall rndu rnd: R -> R,
  Rnd_UP D F rndu ->
  Rounding_for_Format D F rnd -> 
  forall x, D x -> rnd x <= rndu x.
Proof.
intros D F rndu rnd Hu (Hr1,(Hr2,Hr3)) x Hx.
destruct (Hu x Hx) as (H1,(H2,(H3,H4))).
replace (rndu x) with (rnd (rndu x)).
now apply Hr1.
now apply Hr3.
Qed.

Theorem Rnd_UP_or_DN: 
  forall D F : R -> Prop,
  forall rndd rndu rnd: R -> R,
  Rnd_DN D F rndd -> Rnd_UP D F rndu ->
  Rounding_for_Format D F rnd ->
  forall x, D x -> rnd x = rndd x \/ rnd x = rndu x.
Proof.
intros D F rndd rndu rnd Hd Hu Hr x Hx.
destruct (Rnd_DN_le_rnd _ _ _ _ Hd Hr x Hx) as [Hdlt|H].
2 : now left.
destruct (Rnd_UP_ge_rnd _ _ _ _ Hu Hr x Hx) as [Hugt|H].
2 : now right.
destruct Hr as (Hr1,(Hr2,Hr3)).
destruct (Rle_or_lt x (rnd x)).
elim Rlt_not_le with (1 := Hugt).
eapply Hu ; trivial.
now apply Hr2.
elim Rlt_not_le with (1 := Hdlt).
eapply Hd ; auto with real.
Qed.


Variable beta: radix.

Notation bpow := (epow beta).


(* ensures a real number can always be rounded toward -inf *)
Definition satisfies_DN (F : R -> Prop) :=
  exists rnd:R-> R, Rnd_DN R_whole F rnd.

Definition satisfies_any (F : R -> Prop) :=
  F 0%R /\ (forall x : R, F x -> F (-x)%R) /\
     satisfies_DN F.

Theorem satisfies_any_imp_UP: forall (F:R->Prop),
   satisfies_any F ->
       exists rnd:R-> R, Rnd_UP R_whole F rnd.
intros F (H1,(H2,(rnd,H3))).
exists (fun x=> -rnd(-x)).
intros x _.
destruct (H3 (-x) I).
repeat split.
now apply H2.
apply Ropp_le_cancel; rewrite Ropp_involutive.
apply H0.
intros.
apply Ropp_le_cancel; rewrite Ropp_involutive.
apply H0.
now apply H2.
now apply Ropp_le_contravar.
Qed.

Theorem satisfies_any_imp_ZR: forall (F:R->Prop),
   satisfies_any F ->
       exists rnd:R-> R, Rnd_ZR R_whole F rnd.
intros F (H1,(H2,(rnd,H3))).
exists (fun x =>  match Rle_dec 0 x with
  | left _  => rnd x
  | right _ => - rnd (-x)
  end).
split ; intros x (_, Hx).
(* rnd DN *)
destruct (Rle_dec 0 x) as [_|H'].
apply H3.
elim (H' Hx).
(* rnd UP *)
destruct (Rle_dec 0 x) as [H'|H'].
(* - zero *)
replace x with 0 by now apply Rle_antisym.
replace (rnd 0) with 0.
repeat split ; auto with real.
apply Rle_antisym.
apply (H3 0 I) ; auto with real.
apply (H3 0 I).
(* - negative *)
destruct (H3 (-x) I) as (H,(H4,H5)).
repeat split.
now apply H2.
now apply Ropp_le_cancel; rewrite Ropp_involutive.
intros.
apply Ropp_le_cancel; rewrite Ropp_involutive.
apply H5.
now apply H2.
now apply Ropp_le_contravar.
Qed.

Theorem satisfies_any_imp_NA: forall (F:R->Prop),
   satisfies_any F ->
       exists rnd:R-> R, Rnd_NA R_whole F rnd.
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
intros x _.
destruct (total_order_T (Rabs (rndu x - x)) (Rabs (rndd x - x))) as [[H|H]|H].
(* |up(x) - x| < [dn(x) - x| *)
destruct (Hu x I) as (H3,(H4,H5)).
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
destruct (Hd x I) as (H3,(H4,H5)).
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
intros x y _ Hy Hg.
destruct (total_order_T (Rabs (rndu x - x)) (Rabs (rndd x - x))) as [[H|H]|H].



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

End RND.
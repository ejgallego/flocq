Require Import Flocq_Raux.
Require Import Flocq_defs.

Section RND_prop.

Open Scope R_scope.

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

Theorem Rnd_UP_DN_pt_sym :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_UP_pt F (-x) (-f) -> Rnd_DN_pt F x f.
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

Theorem Rnd_DN_pt_idempotent :
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

Theorem Rnd_DN_idempotent :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rnd_DN F rnd ->
  IdempotentP F rnd.
Proof.
intros F rnd Hr.
split.
intros.
eapply Hr.
intros x Hx.
now apply Rnd_DN_pt_idempotent with (2 := Hx).
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

Theorem Rnd_UP_pt_idempotent :
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

Theorem Rnd_UP_idempotent :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rnd_UP F rnd ->
  IdempotentP F rnd.
Proof.
intros F rnd Hr.
split.
intros.
eapply Hr.
intros x Hx.
now apply Rnd_UP_pt_idempotent with (2 := Hx).
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
  forall x f : R,
  Rnd_N_pt F x f ->
  Rnd_DN_pt F x f \/ Rnd_UP_pt F x f.
Proof.
intros F x f (Hf1,Hf2).
destruct (Rle_or_lt x f) as [Hxf|Hxf].
(* . *)
right.
repeat split ; try assumption.
intros g Hg Hxg.
specialize (Hf2 g Hg).
rewrite 2!Rabs_pos_eq in Hf2.
now apply Rplus_le_reg_r with (-x)%R.
now apply Rle_0_minus.
now apply Rle_0_minus.
(* . *)
left.
repeat split ; try assumption.
now apply Rlt_le.
intros g Hg Hxg.
specialize (Hf2 g Hg).
rewrite 2!Rabs_left1 in Hf2.
generalize (Ropp_le_cancel _ _ Hf2).
intros H.
now apply Rplus_le_reg_r with (-x)%R.
now apply Rle_minus.
apply Rlt_le.
now apply Rlt_minus.
Qed.

Theorem Rnd_N_pt_DN_or_UP_eq :
  forall F : R -> Prop,
  forall x fd fu f : R,
  Rnd_DN_pt F x fd -> Rnd_UP_pt F x fu ->
  Rnd_N_pt F x f ->
  f = fd \/ f = fu.
Proof.
intros F x fd fu f Hd Hu Hf.
destruct (Rnd_N_pt_DN_or_UP F x f Hf) as [H|H].
left.
apply Rnd_DN_pt_unicity with (1 := H) (2 := Hd).
right.
apply Rnd_UP_pt_unicity with (1 := H) (2 := Hu).
Qed.

Theorem Rnd_N_pt_sym :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_N_pt F (-x) (-f) -> Rnd_N_pt F x f.
Proof.
intros F HF x f (H1,H2).
rewrite <- (Ropp_involutive f).
repeat split.
apply HF.
apply H1.
intros g H3.
rewrite Ropp_involutive.
replace (f - x)%R with (-(-f - -x))%R by ring.
replace (g - x)%R with (-(-g - -x))%R by ring.
rewrite 2!Rabs_Ropp.
apply H2.
now apply HF.
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

Theorem Rnd_N_pt_idempotent :
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

Theorem Rnd_N_idempotent :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rnd_N F rnd ->
  IdempotentP F rnd.
Proof.
intros F rnd Hr.
split.
intros x.
eapply Hr.
intros x Hx.
now apply Rnd_N_pt_idempotent with F.
Qed.

Theorem Rnd_N_pt_0 :
  forall F : R -> Prop,
  F 0 ->
  Rnd_N_pt F 0 0.
Proof.
intros F HF.
split.
exact HF.
intros g _.
rewrite 2!Rminus_0_r, Rabs_R0.
apply Rabs_pos.
Qed.

Theorem Rnd_N_pt_pos :
  forall F : R -> Prop, F 0 ->
  forall x f, 0 <= x ->
  Rnd_N_pt F x f ->
  0 <= f.
Proof.
intros F HF x f [Hx|Hx] Hxf.
eapply Rnd_N_pt_monotone ; try eassumption.
now apply Rnd_N_pt_0.
right.
apply sym_eq.
apply Rnd_N_pt_idempotent with F.
now rewrite Hx.
exact HF.
Qed.

Theorem Rnd_N_pt_neg :
  forall F : R -> Prop, F 0 ->
  forall x f, x <= 0 ->
  Rnd_N_pt F x f ->
  f <= 0.
Proof.
intros F HF x f [Hx|Hx] Hxf.
eapply Rnd_N_pt_monotone ; try eassumption.
now apply Rnd_N_pt_0.
right.
apply Rnd_N_pt_idempotent with F.
now rewrite <- Hx.
exact HF.
Qed.

Theorem Rnd_NA_pt_monotone :
  forall F : R -> Prop,
  F 0 ->
  forall x y f g : R,
  Rnd_NA_pt F x f -> Rnd_NA_pt F y g ->
  x <= y -> f <= g.
Proof.
intros F HF x y f g (Hf,Hx) (Hg,Hy) [Hxy|Hxy].
now apply Rnd_N_pt_monotone with F x y.
apply Req_le.
rewrite <- Hxy in Hg, Hy.
clear y Hxy.
assert (K: f = g \/ f = -g).
apply Rabs_eq_Rabs.
apply Rle_antisym.
now apply Hy.
now apply Hx.
destruct K as [K|K].
exact K.
rewrite K.
rewrite K in Hf.
clear f Hx Hy K.
unfold Rnd_N_pt in Hf, Hg.
assert (L: g + x = g - x \/  g + x = x - g).
rewrite <- (Ropp_minus_distr g x).
apply Rabs_eq_Rabs.
rewrite <- Rabs_Ropp.
rewrite Ropp_plus_distr.
fold (-g - x).
apply Rle_antisym.
now apply Hf.
now apply Hg.
destruct L as [L|L].
assert (g = 0).
apply Rnd_N_pt_idempotent with F.
replace 0 with x.
exact Hg.
apply Rmult_eq_reg_l with 2.
rewrite Rmult_0_r.
rewrite <- (Rminus_diag_eq _ _ L).
ring.
now apply (Z2R_neq 2 0).
exact HF.
rewrite H.
apply Ropp_0.
apply Rplus_eq_reg_l with x.
fold (x - g).
rewrite <- L.
apply Rplus_comm.
Qed.

Theorem Rnd_NA_monotone :
  forall F : R -> Prop,
  F 0 ->
  forall rnd : R -> R,
  Rnd_NA F rnd ->
  MonotoneP rnd.
Proof.
intros F rnd Hr x y Hxy.
now apply Rnd_NA_pt_monotone with F.
Qed.

Theorem Rnd_NA_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_NA_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (Hf,_) Hx.
now apply Rnd_N_pt_idempotent with F.
Qed.

Theorem Rnd_NA_idempotent :
  forall F : R -> Prop,
  forall rnd : R -> R,
  Rnd_NA F rnd ->
  IdempotentP F rnd.
Proof.
intros F rnd Hr.
split.
intros x.
eapply Hr.
intros x Hx.
now apply Rnd_NA_pt_idempotent with F.
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

End RND_prop.

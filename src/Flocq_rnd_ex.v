Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_prop.

Section RND_ex.

Open Scope R_scope.

(* ensures a real number can always be rounded *)
Inductive satisfies_any (F : R -> Prop) :=
  Satisfies_any :
    F 0 -> ( forall x : R, F x -> F (-x) ) ->
    forall rnd : R -> R, Rnd_DN F rnd -> satisfies_any F.

Theorem satisfies_any_eq :
  forall F1 F2 : R -> Prop,
  ( forall x, F1 x <-> F2 x ) ->
  satisfies_any F1 ->
  satisfies_any F2.
Proof.
intros F1 F2 Heq (Hzero, Hsym, rnd, Hrnd).
refine (Satisfies_any _ _ _ rnd _).
now apply -> Heq.
intros x Hx.
apply -> Heq.
apply Hsym.
now apply <- Heq.
intros x.
destruct (Hrnd x) as (H1, (H2, H3)).
split.
now apply -> Heq.
split.
exact H2.
intros g Hg Hgx.
apply H3 ; try assumption.
now apply <- Heq.
Qed.

Theorem satisfies_any_imp_DN :
  forall F : R -> Prop,
  satisfies_any F ->
  { rnd : R -> R | Rnd_DN F rnd }.
Proof.
intros F (_,_,rnd,Hr).
now exists rnd.
Qed.

Theorem satisfies_any_imp_UP :
  forall F : R -> Prop,
  satisfies_any F ->
  { rnd : R -> R | Rnd_UP F rnd }.
Proof.
intros F (_,H,rnd,Hr).
exists (fun x => - rnd (-x)).
intros x.
apply Rnd_DN_UP_pt_sym.
apply H.
now rewrite Ropp_involutive.
Qed.

Theorem satisfies_any_imp_ZR :
  forall F : R -> Prop,
  satisfies_any F ->
  { rnd : R -> R | Rnd_ZR F rnd }.
Proof.
intros F S.
destruct (satisfies_any_imp_DN F S) as (rndd, Hd).
destruct (satisfies_any_imp_UP F S) as (rndu, Hu).
exists (fun x =>
  match Rle_dec 0 x with
  | left _  => rndd x
  | right _ => rndu x
  end).
intros x.
destruct (Rle_dec 0 x) as [Hx|Hx] ; split.
(* positive or zero *)
intros _.
apply Hd.
intros Hx'.
replace x with 0 by now apply Rle_antisym.
generalize S. intros (S0,_,_,_).
rewrite Rnd_0 with F rndd ; trivial.
repeat split ; auto with real.
split.
now apply Rnd_DN_monotone with F.
now apply Rnd_DN_idempotent.
(* negative *)
intros Hx'.
elim (Hx Hx').
intros Hx'.
apply Hu.
Qed.

Theorem satisfies_any_imp_NA :
  forall F : R -> Prop,
  satisfies_any F ->
  { rnd : R -> R | Rnd_NA F rnd }.
Proof.
intros F Hany.
destruct (satisfies_any_imp_DN F Hany) as (rndd, Hd).
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
rewrite Rabs_pos_eq.
2 : now apply Rle_0_minus.
rewrite Rabs_pos_eq.
2 : now apply Rle_0_minus.
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

End RND_ex.

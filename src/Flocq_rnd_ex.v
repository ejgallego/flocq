Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_prop.

Section RND_ex.

Open Scope R_scope.

(* ensures a real number can always be rounded *)
Inductive satisfies_any (F : R -> Prop) :=
  Satisfies_any :
    F 0 -> ( forall x : R, F x -> F (-x) ) ->
    rounding_pred_total (Rnd_DN_pt F) -> satisfies_any F.

Theorem satisfies_any_eq :
  forall F1 F2 : R -> Prop,
  ( forall x, F1 x <-> F2 x ) ->
  satisfies_any F1 ->
  satisfies_any F2.
Proof.
intros F1 F2 Heq (Hzero, Hsym, Hrnd).
split.
now apply -> Heq.
intros x Hx.
apply -> Heq.
apply Hsym.
now apply <- Heq.
intros x.
destruct (Hrnd x) as (f, (H1, (H2, H3))).
exists f.
split.
now apply -> Heq.
split.
exact H2.
intros g Hg Hgx.
apply H3.
now apply <- Heq.
exact Hgx.
Qed.

Theorem satisfies_any_imp_DN :
  forall F : R -> Prop,
  satisfies_any F ->
  rounding_pred (Rnd_DN_pt F).
Proof.
intros F (_,_,Hrnd).
split.
apply Hrnd.
apply Rnd_DN_pt_monotone.
Qed.

Theorem satisfies_any_imp_UP :
  forall F : R -> Prop,
  satisfies_any F ->
  rounding_pred (Rnd_UP_pt F).
Proof.
intros F Hany.
split.
intros x.
destruct (proj1 (satisfies_any_imp_DN F Hany) (-x)) as (f, Hf).
exists (-f).
apply Rnd_DN_UP_pt_sym.
apply Hany.
now rewrite Ropp_involutive.
apply Rnd_UP_pt_monotone.
Qed.

Theorem satisfies_any_imp_ZR :
  forall F : R -> Prop,
  satisfies_any F ->
  rounding_pred (Rnd_ZR_pt F).
Proof.
intros F Hany.
split.
intros x.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
(* positive *)
destruct (proj1 (satisfies_any_imp_DN F Hany) x) as (f, Hf).
exists f.
split.
now intros _.
intros Hx'.
(* zero *)
assert (x = 0).
now apply Rle_antisym.
rewrite H in Hf |- *.
clear Hx Hx'.
rewrite Rnd_DN_pt_idempotent with (1 := Hf).
split.
apply Hany.
split.
apply Rle_refl.
now intros.
apply Hany.
(* negative *)
destruct (proj1 (satisfies_any_imp_UP F Hany) x) as (f, Hf).
exists f.
split.
intros Hx'.
elim (Rlt_irrefl 0).
now apply Rle_lt_trans with x.
now intros _.
(* . *)
apply Rnd_ZR_pt_monotone.
apply Hany.
Qed.

Theorem satisfies_any_imp_NG :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  satisfies_any F ->
  ( forall x d u, Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> { P x u } + { P x d } ) ->
  { rnd : R -> R | Rnd_NG F P rnd }.
Proof.
intros F P Hany HP.
destruct (rounding_fun_of_pred _ (satisfies_any_imp_DN F Hany)) as (rndd, Hd).
destruct (rounding_fun_of_pred _ (satisfies_any_imp_UP F Hany)) as (rndu, Hu).
exists (fun x =>
  match total_order_T (Rabs (rndu x - x)) (Rabs (rndd x - x)) with
  | inleft (left  _ ) => rndu x
  | inleft (right _ ) => match HP x _ _ (Hd _) (Hu _) with
                            left  _ => rndu x
                          | right _ => rndd x
                          end
  | inright _         => rndd x
  end).
split.
(* *** nearest *)
destruct (total_order_T (Rabs (rndu x - x)) (Rabs (rndd x - x))) as [[H|H]|H].
(* |up(x) - x| < |dn(x) - x| *)
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
now eapply Hd ; try apply Rlt_le.
apply Rge_minus.
apply Rle_ge.
now left.
apply Rge_minus.
apply Rle_ge.
now eapply Hd.
(* |up(x) - x| = [dn(x) - x| *)
destruct (HP x _ _ (Hd x) (Hu x)) as [H'|H'].
(* - u >> d *)
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
(* - d >> u *)
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
now eapply Hd ; try apply Rlt_le.
apply Rle_minus.
now apply Rlt_le.
apply Rle_minus.
now eapply Hd.
(* |up(x) - x| > |dn(x) - x| *)
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
now eapply Hd ; try apply Rlt_le.
apply Rle_minus.
now apply Rlt_le.
apply Rle_minus.
now eapply Hd.
(* *** away *)
destruct (total_order_T (Rabs (rndu x - x)) (Rabs (rndd x - x))) as [[H|H]|H].
right.
intros f2 Hxf2.
destruct (Rnd_N_pt_DN_or_UP_eq F x _ _ f2 (Hd x) (Hu x) Hxf2) as [K|K] ; rewrite K.
elim Rlt_not_le with (1 := H).
rewrite <- K.
apply Hxf2.
eapply Hu.
apply refl_equal.
destruct (HP x (rndd x) (rndu x) (Hd x) (Hu x)) as [H0|H0].
now left.
now left.
right.
intros f2 Hxf2.
destruct (Rnd_N_pt_DN_or_UP_eq F x _ _ f2 (Hd x) (Hu x) Hxf2) as [K|K] ; rewrite K.
apply refl_equal.
elim Rlt_not_le with (1 := H).
rewrite <- K.
apply Hxf2.
eapply Hd.
Qed.

Theorem satisfies_any_imp_NA :
  forall F : R -> Prop,
  satisfies_any F ->
  { rnd : R -> R | Rnd_NA F rnd }.
Proof.
intros F Hany.
destruct (satisfies_any_imp_NG F (fun a b => (Rabs a <= Rabs b)%R) Hany) as (rnd, Hrnd).
intros x d u Hxd Hxu.
destruct (Rle_lt_dec 0 x) as [Hx|Hx].
left.
rewrite Rabs_pos_eq with (1 := Hx).
rewrite Rabs_pos_eq.
apply Hxu.
apply Rle_trans with (1 := Hx).
apply Hxu.
right.
rewrite Rabs_left with (1 := Hx).
rewrite Rabs_left1.
apply Ropp_le_contravar.
apply Hxd.
apply Rlt_le.
apply Rle_lt_trans with (2 := Hx).
apply Hxd.
exists rnd.
intros x.
apply <- Rnd_NA_NG_pt.
apply Hrnd.
apply Hany.
Qed.

End RND_ex.

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
clear H Hx Hx'.
rewrite Rnd_DN_pt_idempotent with (1 := Hf).
apply Rnd_UP_pt_refl.
apply Hany.
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
  rounding_pred_total (Rnd_NG_pt F P).
Proof.
intros F P Hany HP x.
destruct (proj1 (satisfies_any_imp_DN F Hany) x) as (d, Hd).
destruct (proj1 (satisfies_any_imp_UP F Hany) x) as (u, Hu).
destruct (total_order_T (Rabs (u - x)) (Rabs (d - x))) as [[H|H]|H].
(* |up(x) - x| < |dn(x) - x| *)
exists u.
split.
(* - . *)
split.
apply Hu.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
do 2 rewrite <- (Rabs_minus_sym x).
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
now apply Hd.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hd.
(* - . *)
right.
intros f Hf.
destruct (Rnd_N_pt_DN_or_UP_eq F x _ _ _ Hd Hu Hf) as [K|K] ; rewrite K.
elim Rlt_not_le with (1 := H).
rewrite <- K.
apply Hf.
apply Hu.
apply refl_equal.
(* |up(x) - x| = [dn(x) - x| *)
destruct (HP x _ _ Hd Hu) as [H'|H'].
(* - u >> d *)
exists u.
split.
split.
apply Hu.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
rewrite H.
rewrite 2!Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
now apply Hd.
now apply Rle_minus.
apply Rle_minus.
apply Hd.
now left.
(* - d >> u *)
exists d.
split.
split.
apply Hd.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
rewrite <- H.
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
rewrite 2!Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
now apply Hd.
now apply Rle_minus.
apply Rle_minus.
apply Hd.
now left.
(* |up(x) - x| > |dn(x) - x| *)
exists d.
split.
split.
apply Hd.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
rewrite 2!Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
now apply Hd.
now apply Rle_minus.
apply Rle_minus.
apply Hd.
right.
intros f Hf.
destruct (Rnd_N_pt_DN_or_UP_eq F x _ _ _ Hd Hu Hf) as [K|K] ; rewrite K.
apply refl_equal.
elim Rlt_not_le with (1 := H).
rewrite <- K.
apply Hf.
apply Hd.
Qed.

Theorem satisfies_any_imp_NA :
  forall F : R -> Prop,
  satisfies_any F ->
  rounding_pred (Rnd_NA_pt F).
Proof.
intros F Hany.
split.
assert (H : rounding_pred_total (Rnd_NG_pt F (fun a b => (Rabs a <= Rabs b)%R))).
apply satisfies_any_imp_NG.
apply Hany.
intros x d u Hd Hu.
destruct (Rle_lt_dec 0 x) as [Hx|Hx].
left.
rewrite Rabs_pos_eq with (1 := Hx).
rewrite Rabs_pos_eq.
apply Hu.
apply Rle_trans with (1 := Hx).
apply Hu.
right.
rewrite Rabs_left with (1 := Hx).
rewrite Rabs_left1.
apply Ropp_le_contravar.
apply Hd.
apply Rlt_le in Hx.
apply Rle_trans with (2 := Hx).
apply Hd.
intros x.
destruct (H x) as (f, Hf).
exists f.
apply <- Rnd_NA_NG_pt.
apply Hf.
apply Hany.
apply Rnd_NA_pt_monotone.
apply Hany.
Qed.

End RND_ex.

Require Import Fcore.

Section Fcalc_bracket.

Variable d u : R.
Hypothesis Hdu : (d < u)%R.

Lemma ordered_middle :
  (d < (d + u)/2 < u)%R.
Proof.
split.
apply Rmult_lt_reg_r with 2%R.
now apply (Z2R_lt 0 2).
unfold Rdiv.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
rewrite Rmult_plus_distr_l, Rmult_1_r.
now apply Rplus_lt_compat_l.
now apply (Z2R_neq 2 0).
apply Rmult_lt_reg_r with 2%R.
now apply (Z2R_lt 0 2).
unfold Rdiv.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
rewrite Rmult_plus_distr_l, Rmult_1_r.
now apply Rplus_lt_compat_r.
now apply (Z2R_neq 2 0).
Qed.

Inductive location := loc_Exact | loc_Inexact : comparison -> location.

Variable x : R.

Inductive inbetween : location -> Prop :=
  | inbetween_Exact : x = d -> inbetween loc_Exact
  | inbetween_Inexact l : (d < x < u)%R -> Rcompare x ((d + u) / 2)%R = l -> inbetween (loc_Inexact l).

Section Fcalc_bracket_any.

Variable l : location.

Theorem inbetween_not_Hi :
  inbetween l ->
  l <> loc_Inexact Gt ->
  (d <= x <= (d + u)/2)%R.
Proof.
intros [Hx|[] Hx Hl] H ; try (now elim H) ; clear l H.
rewrite Hx.
split.
apply Rle_refl.
apply Rlt_le.
apply ordered_middle.
rewrite Rcompare_Eq_inv with (1 := Hl).
split.
apply Rlt_le.
apply ordered_middle.
apply Rle_refl.
split ; apply Rlt_le.
apply Hx.
now apply Rcompare_Lt_inv.
Qed.

Theorem inbetween_Mi_Hi :
  inbetween l ->
  l = loc_Inexact Eq \/ l = loc_Inexact Gt ->
  ((d + u)/2 <= x <= u)%R.
Proof.
intros [Hx|[] Hx Hl] H ; try (now elim H) ; clear l H.
rewrite Rcompare_Eq_inv with (1 := Hl).
split.
apply Rle_refl.
apply Rlt_le.
apply ordered_middle.
split ; apply Rlt_le.
now apply Rcompare_Gt_inv.
apply Hx.
Qed.

Theorem inbetween_bounds :
  inbetween l ->
  (d <= x < u)%R.
Proof.
intros [Hx|l' Hx Hl] ; clear l.
rewrite Hx.
split.
apply Rle_refl.
exact Hdu.
now split ; try apply Rlt_le.
Qed.

Theorem inbetween_bounds_not_Eq :
  inbetween l ->
  l <> loc_Exact ->
  (d < x < u)%R.
Proof.
intros [Hx|l' Hx Hl] H.
now elim H.
exact Hx.
Qed.

End Fcalc_bracket_any.

Theorem inbetween_distance_inexact :
  forall l,
  inbetween (loc_Inexact l) ->
  Rcompare (x - d) (u - x) = l.
Proof.
intros l Hl.
inversion_clear Hl as [|l' Hl' Hx].
now rewrite Rcompare_middle.
Qed.

Theorem inbetween_distance_inexact_abs :
  forall l,
  inbetween (loc_Inexact l) ->
  Rcompare (Rabs (d - x)) (Rabs (u - x)) = l.
Proof.
intros l Hl.
rewrite Rabs_left1.
rewrite Rabs_pos_eq.
rewrite Ropp_minus_distr.
now apply inbetween_distance_inexact.
apply Rle_0_minus.
apply Rlt_le.
apply (inbetween_bounds _ Hl).
apply Rle_minus.
apply (inbetween_bounds _ Hl).
Qed.

End Fcalc_bracket.

Section Fcalc_bracket_step.

Variable start step : R.
Variable nb_steps : Z.
Variable Hstep : (0 < step)%R.

Lemma double_div2 :
  ((start + start)/2 = start)%R.
Proof.
field.
Qed.

Lemma ordered_steps :
  forall k,
  (start + Z2R k * step < start + Z2R (k + 1) * step)%R.
Proof.
intros k.
apply Rplus_lt_compat_l.
apply Rmult_lt_compat_r.
exact Hstep.
apply Z2R_lt.
apply Zlt_succ.
Qed.

Lemma mid_step :
  forall k,
  ((start + (start + Z2R k * step)) / 2 = start + (Z2R k / 2 * step))%R.
Proof.
intros k.
field.
Qed.

Hypothesis (Hnb_steps : (1 < nb_steps)%Z).

Lemma inbetween_step_not_Eq :
  forall x k l l',
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  (0 < k < nb_steps)%Z ->
  Rcompare x (start + (Z2R nb_steps / 2 * step))%R = l' ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact l').
Proof.
intros x k l l' Hx Hk Hl'.
constructor.
(* . *)
assert (Hx' := inbetween_bounds _ _ (ordered_steps _) _ _ Hx).
split.
apply Rlt_le_trans with (2 := proj1 Hx').
rewrite <- (Rplus_0_r start) at 1.
apply Rplus_lt_compat_l.
apply Rmult_lt_0_compat.
now apply (Z2R_lt 0).
exact Hstep.
apply Rlt_le_trans with (1 := proj2 Hx').
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Z2R_le.
omega.
(* . *)
now rewrite mid_step.
Qed.

Theorem inbetween_step_Lo :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  (0 < k)%Z -> (2 * k + 1 < nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Lt).
Proof.
intros x k l Hx Hk1 Hk2.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
apply Rcompare_Lt.
assert (Hx' := inbetween_bounds _ _ (ordered_steps _) _ _ Hx).
apply Rlt_le_trans with (1 := proj2 Hx').
apply Rcompare_not_Lt_inv.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_l.
apply Rcompare_not_Lt.
change 2%R with (Z2R 2).
rewrite <- mult_Z2R.
apply Z2R_le.
omega.
exact Hstep.
Qed.

Theorem inbetween_step_Hi :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  (nb_steps < 2 * k)%Z -> (k < nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Gt).
Proof.
intros x k l Hx Hk1 Hk2.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
apply Rcompare_Gt.
assert (Hx' := inbetween_bounds _ _ (ordered_steps _) _ _ Hx).
apply Rlt_le_trans with (2 := proj1 Hx').
apply Rcompare_Lt_inv.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_l.
apply Rcompare_Lt.
change 2%R with (Z2R 2).
rewrite <- mult_Z2R.
apply Z2R_lt.
omega.
exact Hstep.
Qed.

Theorem inbetween_step_Lo_not_Eq :
  forall x l,
  inbetween start (start + step) x l ->
  l <> loc_Exact ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Lt).
Proof.
intros x l Hx Hl.
assert (Hx' := inbetween_bounds_not_Eq _ _ _ _ Hx Hl).
constructor.
(* . *)
split.
apply Hx'.
apply Rlt_trans with (1 := proj2 Hx').
apply Rplus_lt_compat_l.
rewrite <- (Rmult_1_l step) at 1.
apply Rmult_lt_compat_r.
exact Hstep.
now apply (Z2R_lt 1).
(* . *)
apply Rcompare_Lt.
apply Rlt_le_trans with (1 := proj2 Hx').
rewrite mid_step.
apply Rcompare_not_Lt_inv.
rewrite <- (Rmult_1_l step) at 2.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_l.
rewrite Rmult_1_r.
apply Rcompare_not_Lt.
apply (Z2R_le 2).
now apply (Zlt_le_succ 1).
exact Hstep.
Qed.

Lemma middle_odd :
  forall k,
  (2 * k + 1 = nb_steps)%Z ->
  (((start + Z2R k * step) + (start + Z2R (k + 1) * step))/2 = start + Z2R nb_steps /2 * step)%R.
Proof.
intros k Hk.
rewrite <- Hk.
rewrite 2!plus_Z2R, mult_Z2R.
simpl. field.
Qed.

Theorem inbetween_step_any_Mi_odd :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x (loc_Inexact l) ->
  (2 * k + 1 = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact l).
Proof.
intros x k l Hx Hk.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
inversion_clear Hx as [|l' _ Hl].
now rewrite (middle_odd _ Hk) in Hl.
Qed.

Theorem inbetween_step_Lo_Mi_Eq_odd :
  forall x k,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x loc_Exact ->
  (2 * k + 1 = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Lt).
Proof.
intros x k Hx Hk.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
inversion_clear Hx as [Hl|].
rewrite Hl.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_r.
apply Rcompare_Lt.
change 2%R with (Z2R 2).
rewrite <- mult_Z2R.
apply Z2R_lt.
rewrite <- Hk.
apply Zlt_succ.
exact Hstep.
Qed.

Theorem inbetween_step_Hi_Mi_even :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  l <> loc_Exact ->
  (2 * k = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Gt).
Proof.
intros x k l Hx Hl Hk.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
apply Rcompare_Gt.
assert (Hx' := inbetween_bounds_not_Eq _ _ _ _ Hx Hl).
apply Rle_lt_trans with (2 := proj1 Hx').
apply Rcompare_not_Lt_inv.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_r.
change 2%R with (Z2R 2).
rewrite <- mult_Z2R.
apply Rcompare_not_Lt.
apply Z2R_le.
rewrite Hk.
apply Zle_refl.
exact Hstep.
Qed.

Theorem inbetween_step_Mi_Mi_even :
  forall x k,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x loc_Exact ->
  (2 * k = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Eq).
Proof.
intros x k Hx Hk.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
apply Rcompare_Eq.
inversion_clear Hx as [Hx'|].
rewrite Hx', <- Hk, mult_Z2R.
simpl (Z2R 2).
field.
Qed.

Definition new_location_even k l :=
  if Zeq_bool k 0 then
    match l with loc_Exact => l | _ => loc_Inexact Lt end
  else
    loc_Inexact
    match Zcompare (2 * k) nb_steps with
    | Lt => Lt
    | Eq => match l with loc_Exact => Eq | _ => Gt end
    | Gt => Gt
    end.

Theorem new_location_even_correct :
  Zeven nb_steps = true ->
  forall x k l, (0 <= k < nb_steps)%Z ->
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  inbetween start (start + Z2R nb_steps * step) x (new_location_even k l).
Proof.
intros He x k l Hk Hx.
unfold new_location_even.
destruct (Zeq_bool_spec k 0) as [Hk0|Hk0].
(* k = 0 *)
rewrite Hk0 in Hx.
rewrite Rmult_0_l, Rplus_0_r, Rmult_1_l in Hx.
set (l' := match l with loc_Exact => l | _ => loc_Inexact Lt end).
assert ((l = loc_Exact /\ l' = loc_Exact) \/ (l <> loc_Exact /\ l' = loc_Inexact Lt)).
unfold l' ; case l ; try (now left) ; right ; now split.
destruct H as [(H1,H2)|(H1,H2)] ; rewrite H2.
constructor.
rewrite H1 in Hx.
now inversion_clear Hx.
now apply inbetween_step_Lo_not_Eq with (2 := H1).
(* k <> 0 *)
destruct (Zcompare_spec (2 * k) nb_steps) as [Hk1|Hk1|Hk1].
(* . 2 * k < nb_steps *)
apply inbetween_step_Lo with (1 := Hx).
omega.
destruct (Zeven_ex nb_steps).
rewrite He in H.
omega.
(* . 2 * k = nb_steps *)
set (l' := match l with loc_Exact => Eq | _ => Gt end).
assert ((l = loc_Exact /\ l' = Eq) \/ (l <> loc_Exact /\ l' = Gt)).
unfold l' ; case l ; try (now left) ; right ; now split.
destruct H as [(H1,H2)|(H1,H2)] ; rewrite H2.
rewrite H1 in Hx.
now apply inbetween_step_Mi_Mi_even with (1 := Hx).
now apply inbetween_step_Hi_Mi_even with (1 := Hx).
(* . 2 * k > nb_steps *)
apply inbetween_step_Hi with (1 := Hx).
exact Hk1.
apply Hk.
Qed.

Definition new_location_odd k l :=
  if Zeq_bool k 0 then
    match l with loc_Exact => l | _ => loc_Inexact Lt end
  else
    loc_Inexact
    match Zcompare (2 * k + 1) nb_steps with
    | Lt => Lt
    | Eq => match l with loc_Inexact l => l | loc_Exact => Lt end
    | Gt => Gt
    end.

Theorem new_location_odd_correct :
  Zeven nb_steps = false ->
  forall x k l, (0 <= k < nb_steps)%Z ->
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  inbetween start (start + Z2R nb_steps * step) x (new_location_odd k l).
Proof.
intros Ho x k l Hk Hx.
unfold new_location_odd.
destruct (Zeq_bool_spec k 0) as [Hk0|Hk0].
(* k = 0 *)
rewrite Hk0 in Hx.
rewrite Rmult_0_l, Rplus_0_r, Rmult_1_l in Hx.
set (l' := match l with loc_Exact => l | _ => loc_Inexact Lt end).
assert ((l = loc_Exact /\ l' = loc_Exact) \/ (l <> loc_Exact /\ l' = loc_Inexact Lt)).
unfold l' ; case l ; try (now left) ; right ; now split.
destruct H as [(H1,H2)|(H1,H2)] ; rewrite H2.
constructor.
rewrite H1 in Hx.
now inversion_clear Hx.
now apply inbetween_step_Lo_not_Eq with (2 := H1).
(* k <> 0 *)
destruct (Zcompare_spec (2 * k + 1) nb_steps) as [Hk1|Hk1|Hk1].
(* . 2 * k + 1 < nb_steps *)
apply inbetween_step_Lo with (1 := Hx) (3 := Hk1).
omega.
(* . 2 * k + 1 = nb_steps *)
destruct l.
apply inbetween_step_Lo_Mi_Eq_odd with (1 := Hx) (2 := Hk1).
apply inbetween_step_any_Mi_odd with (1 := Hx) (2 := Hk1).
(* . 2 * k + 1 > nb_steps *)
apply inbetween_step_Hi with (1 := Hx).
destruct (Zeven_ex nb_steps).
rewrite Ho in H.
omega.
apply Hk.
Qed.

Definition new_location :=
  if Zeven nb_steps then new_location_even else new_location_odd.

Theorem new_location_correct :
  forall x k l, (0 <= k < nb_steps)%Z ->
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  inbetween start (start + Z2R nb_steps * step) x (new_location k l).
Proof.
intros x k l Hk Hx.
unfold new_location.
generalize (refl_equal nb_steps) (Zle_lt_trans _ _ _ (proj1 Hk) (proj2 Hk)).
pattern nb_steps at 2 3 5 ; case nb_steps.
now intros _.
(* . *)
intros [p|p|] Hp _.
apply new_location_odd_correct with (2 := Hk) (3 := Hx).
now rewrite Hp.
apply new_location_even_correct with (2 := Hk) (3 := Hx).
now rewrite Hp.
now rewrite Hp in Hnb_steps.
(* . *)
now intros p _.
Qed.

End Fcalc_bracket_step.

Section Fcalc_bracket_N.

Variable F : R -> Prop.
Variable d u x : R.
Hypothesis Hd : Rnd_DN_pt F x d.
Hypothesis Hu : Rnd_UP_pt F x u.

Theorem Rnd_N_pt_bracket_not_Hi :
  forall l, l <> loc_Inexact Gt ->
  inbetween d u x l ->
  Rnd_N_pt F x d.
Proof.
intros l Hl Hx.
apply Rnd_DN_pt_N with (1 := Hd) (2 := Hu).
inversion Hx as [Hx'|l' Hx' Hl'].
rewrite Hx'.
unfold Rminus.
rewrite Rplus_opp_r.
apply Rle_0_minus.
apply Rle_trans with x.
apply Hd.
apply Hu.
apply Rcompare_not_Gt_inv.
rewrite Rcompare_middle.
rewrite Hl'.
contradict Hl.
now rewrite <- H, Hl.
Qed.

Theorem Rnd_N_pt_bracket_Mi_Hi :
  forall l, l = loc_Inexact Eq \/ l = loc_Inexact Gt ->
  inbetween d u x l ->
  Rnd_N_pt F x u.
Proof.
intros l Hl Hx.
apply Rnd_UP_pt_N with (1 := Hd) (2 := Hu).
inversion Hx as [Hx' Hl'|l' Hx' Hl' Hl''].
now destruct Hl as [Hl|Hl] ; rewrite Hl in Hl'.
apply Rcompare_not_Lt_inv.
rewrite Rcompare_middle.
rewrite Hl'.
intros H.
rewrite H in Hl''.
rewrite <- Hl'' in Hl.
now destruct Hl.
Qed.

Theorem Rnd_not_N_pt_bracket_Hi :
  inbetween d u x (loc_Inexact Gt) ->
  ~ Rnd_N_pt F x d.
Proof.
intros Hx (_, Hn).
specialize (Hn u (proj1 Hu)).
apply Rle_not_lt with (1 := Hn).
apply Rcompare_Gt_inv.
apply inbetween_distance_inexact_abs.
refine (let H := _ in Rlt_trans _ x _ (proj1 H) (proj2 H)).
now apply inbetween_bounds_not_Eq with (1 := Hx).
exact Hx.
Qed.

Theorem Rnd_not_N_pt_bracket_Lo :
  inbetween d u x (loc_Inexact Lt) ->
  ~ Rnd_N_pt F x u.
Proof.
intros Hx (_, Hn).
specialize (Hn d (proj1 Hd)).
apply Rle_not_lt with (1 := Hn).
apply Rcompare_Lt_inv.
apply inbetween_distance_inexact_abs.
refine (let H := _ in Rlt_trans _ x _ (proj1 H) (proj2 H)).
now apply inbetween_bounds_not_Eq with (1 := Hx).
exact Hx.
Qed.

End Fcalc_bracket_N.

Section Fcalc_bracket_scale.

Lemma inbetween_mult_aux :
  forall x d s,
  ((x * s + d * s) / 2 = (x + d) / 2 * s)%R.
Proof.
intros x d s.
field.
Qed.

Theorem inbetween_mult_compat :
  forall x d u l s,
  (0 < s)%R ->
  inbetween x d u l ->
  inbetween (x * s) (d * s) (u * s) l.
Proof.
intros x d u l s Hs [Hx|l' Hx Hl] ; constructor.
now rewrite Hx.
now split ; apply Rmult_lt_compat_r.
rewrite inbetween_mult_aux.
now rewrite Rcompare_mult_r.
Qed.

Theorem inbetween_mult_reg :
  forall x d u l s,
  (0 < s)%R ->
  inbetween (x * s) (d * s) (u * s) l ->
  inbetween x d u l.
Proof.
intros x d u l s Hs [Hx|l' Hx Hl] ; constructor.
apply Rmult_eq_reg_r with (1 := Hx).
now apply Rgt_not_eq.
now split ; apply Rmult_lt_reg_r with s.
rewrite <- Rcompare_mult_r with (1 := Hs).
now rewrite inbetween_mult_aux in Hl.
Qed.

End Fcalc_bracket_scale.

Section Fcalc_bracket_generic.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.
Notation format := (generic_format beta fexp).

Definition inbetween_float m e x l :=
  inbetween (F2R (Float beta m e)) (F2R (Float beta (m + 1) e)) x l.

Definition inbetween_int m x l :=
  inbetween (Z2R m) (Z2R (m + 1)) x l.

Theorem inbetween_float_new_location :
  forall x m e l k,
  (0 < k)%Z ->
  inbetween_float m e x l ->
  inbetween_float (Zdiv m (Zpower (radix_val beta) k)) (e + k) x (new_location (Zpower (radix_val beta) k) (Zmod m (Zpower (radix_val beta) k)) l).
Proof.
intros x m e l k Hk Hx.
unfold inbetween_float in *.
assert (Hr: forall m, F2R (Float beta m (e + k)) = F2R (Float beta (m * Zpower (radix_val beta) k) e)).
clear -Hk. intros m.
rewrite (F2R_change_exp beta e).
apply (f_equal (fun r => F2R (Float beta (m * Zpower _ r) e))).
ring.
omega.
assert (Hp: (Zpower (radix_val beta) k > 0)%Z).
apply Zlt_gt.
apply Zpower_gt_0.
generalize (radix_prop beta).
omega.
now apply Zlt_le_weak.
(* . *)
rewrite 2!Hr.
rewrite Zmult_plus_distr_l, Zmult_1_l.
unfold F2R at 2. simpl.
rewrite plus_Z2R, Rmult_plus_distr_r.
apply new_location_correct.
apply bpow_gt_0.
now apply Zpower_gt_1.
now apply Z_mod_lt.
rewrite <- 2!Rmult_plus_distr_r, <- 2!plus_Z2R.
rewrite Zmult_comm, Zplus_assoc.
now rewrite <- Z_div_mod_eq.
Qed.

Theorem inbetween_float_new_location_single :
  forall x m e l,
  inbetween_float m e x l ->
  inbetween_float (Zdiv m (radix_val beta)) (e + 1) x (new_location (radix_val beta) (Zmod m (radix_val beta)) l).
Proof.
intros x m e l Hx.
replace (radix_val beta) with (Zpower (radix_val beta) 1).
now apply inbetween_float_new_location.
apply Zmult_1_r.
Qed.

Theorem inbetween_float_rounding :
  forall rnd choice,
  ( forall x m l, inbetween_int m x l -> Zrnd rnd x = choice m l ) ->
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float m e x l ->
  rounding beta fexp rnd x = F2R (Float beta (choice m l) e).
Proof.
intros rnd choice Hc x m l e Hl.
unfold rounding, F2R. simpl.
apply (f_equal (fun m => (Z2R m * bpow e)%R)).
apply Hc.
apply inbetween_mult_reg with (bpow e).
apply bpow_gt_0.
now rewrite scaled_mantissa_bpow.
Qed.

Theorem inbetween_float_DN :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float m e x l ->
  rounding beta fexp ZrndDN x = F2R (Float beta m e).
Proof.
apply inbetween_float_rounding with (choice := fun m l => m).
intros x m l Hl.
apply Zfloor_imp.
apply inbetween_bounds with (2 := Hl).
apply Z2R_lt.
apply Zlt_succ.
Qed.

Definition cond_incr (b : bool) m := if b then (m + 1)%Z else m.

Definition round_UP l :=
  match l with
  | loc_Exact => false
  | _ => true
  end.

Theorem inbetween_float_UP :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float m e x l ->
  rounding beta fexp ZrndUP x = F2R (Float beta (cond_incr (round_UP l) m) e).
Proof.
apply inbetween_float_rounding with (choice := fun m l => cond_incr (round_UP l) m).
intros x m l Hl.
assert (Hl': l = loc_Exact \/ (l <> loc_Exact /\ round_UP l = true)).
case l ; try (now left) ; now right ; split.
destruct Hl' as [Hl'|(Hl1, Hl2)].
(* Exact *)
rewrite Hl'.
destruct Hl ; try easy.
rewrite H.
apply Zceil_Z2R.
(* not Exact *)
rewrite Hl2.
simpl.
apply Zceil_imp.
ring_simplify (m + 1 - 1)%Z.
refine (let H := _ in conj (proj1 H) (Rlt_le _ _ (proj2 H))).
apply inbetween_bounds_not_Eq with (2 := Hl1) (1 := Hl).
Qed.

Definition round_NE (p : bool) l :=
  match l with
  | loc_Exact => false
  | loc_Inexact Lt => false
  | loc_Inexact Eq => if p then false else true
  | loc_Inexact Gt => true
  end.

Theorem inbetween_float_NE :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float m e x l ->
  rounding beta fexp ZrndNE x = F2R (Float beta (cond_incr (round_NE (Zeven m) l) m) e).
Proof.
apply inbetween_float_rounding with (choice := fun m l => cond_incr (round_NE (Zeven m) l) m).
intros x m l Hl.
inversion_clear Hl as [Hx|l' Hx Hl'].
(* Exact *)
rewrite Hx.
now rewrite Zrnd_Z2R.
(* not Exact *)
unfold Zrnd, ZrndNE, ZrndN, Znearest.
assert (Hm: Zfloor x = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
rewrite Zceil_floor_neq.
rewrite Hm.
replace (Rcompare (x - Z2R m) (/2)) with l'.
now case l'.
rewrite <- Hl'.
rewrite plus_Z2R.
rewrite <- (Rcompare_plus_r (- Z2R m) x).
apply f_equal.
simpl (Z2R 1).
field.
rewrite Hm.
now apply Rlt_not_eq.
Qed.

End Fcalc_bracket_generic.

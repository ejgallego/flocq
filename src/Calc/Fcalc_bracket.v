Require Import Fcore.

Inductive Zeq_bool_prop (x y : Z) : bool -> Prop :=
  | Zeq_bool_true : x = y -> Zeq_bool_prop x y true
  | Zeq_bool_false : x <> y -> Zeq_bool_prop x y false.

Lemma Zeq_bool_spec :
  forall x y, Zeq_bool_prop x y (Zeq_bool x y).
Proof.
intros x y.
generalize (Zeq_is_eq_bool x y).
case (Zeq_bool x y) ; intros (H1, H2) ; constructor.
now apply H2.
intros H.
specialize (H1 H).
discriminate H1.
Qed.

Inductive Zcompare_prop (x y : Z) : comparison -> Prop :=
  | Zcompare_Lt : (x < y)%Z -> Zcompare_prop x y Lt
  | Zcompare_Eq : x = y -> Zcompare_prop x y Eq
  | Zcompare_Gt : (y < x)%Z -> Zcompare_prop x y Gt.

Lemma Zcompare_spec :
  forall x y, Zcompare_prop x y (Zcompare x y).
Proof.
intros x y.
destruct (Z_dec x y) as [[H|H]|H].
generalize (Zlt_compare _ _ H).
case (Zcompare x y) ; try easy.
now constructor.
generalize (Zgt_compare _ _ H).
case (Zcompare x y) ; try easy.
constructor.
now apply Zgt_lt.
generalize (proj2 (Zcompare_Eq_iff_eq _ _) H).
case (Zcompare x y) ; try easy.
now constructor.
Qed.

Section Fcalc_bracket.

Variable d u : R.

Lemma ordered_middle :
  (d <= u)%R -> (d <= (d + u)/2 <= u)%R.
Proof.
intros Hdu.
split.
apply Rmult_le_reg_r with 2%R.
now apply (Z2R_lt 0 2).
unfold Rdiv.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
rewrite Rmult_plus_distr_l, Rmult_1_r.
now apply Rplus_le_compat_l.
now apply (Z2R_neq 2 0).
apply Rmult_le_reg_r with 2%R.
now apply (Z2R_lt 0 2).
unfold Rdiv.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
rewrite Rmult_plus_distr_l, Rmult_1_r.
now apply Rplus_le_compat_r.
now apply (Z2R_neq 2 0).
Qed.

Lemma ordered_middle_strict :
  (d < u)%R -> (d < (d + u)/2 < u)%R.
Proof.
intros Hdu.
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

Inductive location := loc_Eq | loc_Lo | loc_Mi | loc_Hi.

Variable x : R.

Inductive inbetween : location -> Prop :=
  | inbetween_Eq : x = d -> inbetween loc_Eq
  | inbetween_Lo : (d < x)%R -> (x < (d + u)/2)%R -> inbetween loc_Lo
  | inbetween_Mi : x = ((d + u)/2)%R -> inbetween loc_Mi
  | inbetween_Hi : ((d + u)/2 < x)%R -> (x < u)%R -> inbetween loc_Hi.

Variable l : location.

Theorem inbetween_not_Hi :
  (d <= u)%R ->
  inbetween l ->
  l <> loc_Hi ->
  (d <= x <= (d + u)/2)%R.
Proof.
intros Hdu [Hx|Hx1 Hx2|Hx|Hx1 Hx2] H ; try (now elim H) ; clear H.
rewrite Hx.
split.
apply Rle_refl.
now eapply ordered_middle.
split ; now apply Rlt_le.
rewrite Hx.
split.
now eapply ordered_middle.
apply Rle_refl.
Qed.

Theorem inbetween_Mi_Hi :
  (d <= u)%R ->
  inbetween l ->
  l = loc_Mi \/ l = loc_Hi ->
  ((d + u)/2 <= x <= u)%R.
Proof.
intros Hdu [Hx|Hx1 Hx2|Hx|Hx1 Hx2] H ; try (now elim H) ; clear H.
rewrite Hx.
split.
apply Rle_refl.
now eapply ordered_middle.
split ; now apply Rlt_le.
Qed.

Theorem inbetween_bounds :
  (d <= u)%R ->
  inbetween l ->
  (d <= x <= u)%R.
Proof.
intros Hdu [Hx|Hx1 Hx2|Hx|Hx1 Hx2] ; clear l.
rewrite Hx.
split.
apply Rle_refl.
exact Hdu.
split.
now apply Rlt_le.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hx2).
now eapply ordered_middle.
rewrite Hx.
now apply ordered_middle.
split. 2: now apply Rlt_le.
apply Rlt_le.
apply Rle_lt_trans with (2 := Hx1).
now eapply ordered_middle.
Qed.

Theorem inbetween_bounds_strict :
  (d < u)%R ->
  inbetween l ->
  (d <= x < u)%R.
Proof.
intros Hdu Hl.
split.
eapply inbetween_bounds.
now apply Rlt_le.
exact Hl.
destruct Hl as [Hx|Hx1 Hx2|Hx|Hx1 Hx2].
now rewrite Hx.
apply Rlt_le_trans with (1 := Hx2).
refine (proj2 (ordered_middle _)).
now apply Rlt_le.
rewrite Hx.
exact (proj2 (ordered_middle_strict Hdu)).
exact Hx2.
Qed.

Theorem inbetween_bounds_strict_not_Eq :
  (d < u)%R ->
  inbetween l ->
  l <> loc_Eq ->
  (d < x < u)%R.
Proof.
intros Hdu Hl.
split.
2: exact (proj2 (inbetween_bounds_strict Hdu Hl)).
destruct Hl as [Hx|Hx1 Hx2|Hx|Hx1 Hx2] ; try (now elim H) ; clear H.
exact Hx1.
rewrite Hx.
exact (proj1 (ordered_middle_strict Hdu)).
apply Rle_lt_trans with (2 := Hx1).
refine (proj1 (ordered_middle _)).
now apply Rlt_le.
Qed.

End Fcalc_bracket.

Section Fcalc_bracket_step.

Variable start step : R.
Variable nb_steps : Z.
Variable Hstep : (0 < step)%R.

Lemma double_div2 :
  ((start + start)/2 = start)%R.
Proof.
rewrite <- (Rmult_1_r start).
unfold Rdiv.
rewrite <- Rmult_plus_distr_l, Rmult_assoc.
apply f_equal.
apply Rinv_r.
now apply (Z2R_neq 2 0).
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

Hypothesis (Hnb_steps : (1 < nb_steps)%Z).

Theorem inbetween_step_Lo :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  (0 < k)%Z -> (2 * k + 1 < nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x loc_Lo.
Proof.
intros x k l Hx Hk1 Hk2.
constructor.
(* . *)
apply Rlt_le_trans with (start + Z2R k * step)%R.
rewrite <- (Rplus_0_r start) at 1.
apply Rplus_lt_compat_l.
apply Rmult_lt_0_compat.
now apply (Z2R_lt 0).
exact Hstep.
refine (proj1 (inbetween_bounds _ _ _ _ _ Hx)).
apply Rlt_le.
apply ordered_steps.
(* . *)
apply Rlt_le_trans with (start + Z2R (k + 1) * step)%R.
exact (proj2 (inbetween_bounds_strict _ _ _ _ (ordered_steps _) Hx)).
rewrite <- Rplus_assoc.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
fold ((start + start)/2)%R.
rewrite double_div2.
apply Rplus_le_compat_l.
replace (Z2R nb_steps * step * / 2)%R with (Z2R nb_steps * /2 * step)%R by ring.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Rmult_le_reg_r with 2%R.
now apply (Z2R_lt 0 2).
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
change 2%R with (Z2R 2).
rewrite <- mult_Z2R.
apply Z2R_le.
omega.
now apply (Z2R_neq 2 0).
Qed.

Theorem inbetween_step_Hi :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  (nb_steps < 2 * k)%Z -> (k < nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x loc_Hi.
Proof.
intros x k l Hx Hk1 Hk2.
constructor.
(* . *)
apply Rlt_le_trans with (start + Z2R k * step)%R.
rewrite <- Rplus_assoc.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
fold ((start + start)/2)%R.
rewrite double_div2.
apply Rplus_lt_compat_l.
replace (Z2R nb_steps * step * / 2)%R with (Z2R nb_steps * /2 * step)%R by ring.
apply Rmult_lt_compat_r.
exact Hstep.
apply Rmult_lt_reg_r with 2%R.
now apply (Z2R_lt 0 2).
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
change 2%R with (Z2R 2).
rewrite <- mult_Z2R.
apply Z2R_lt.
now rewrite Zmult_comm.
now apply (Z2R_neq 2 0).
refine (proj1 (inbetween_bounds _ _ _ _ _ Hx)).
apply Rlt_le.
apply ordered_steps.
(* . *)
apply Rlt_le_trans with (start + Z2R (k + 1) * step)%R.
exact (proj2 (inbetween_bounds_strict _ _ _ _ (ordered_steps _) Hx)).
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Z2R_le.
now apply Zlt_le_succ.
Qed.

Theorem inbetween_step_Lo_Eq :
  forall x l,
  inbetween start (start + step) x l ->
  l <> loc_Eq ->
  inbetween start (start + Z2R nb_steps * step) x loc_Lo.
Proof.
intros x l Hx Hl.
constructor.
(* . *)
refine (proj1 (inbetween_bounds_strict_not_Eq _ _ _ _ _ Hx Hl)).
rewrite <- (Rplus_0_r start) at 1.
now apply Rplus_lt_compat_l.
(* . *)
apply Rlt_le_trans with (start + step)%R.
refine (proj2 (inbetween_bounds_strict _ _ _ _ _ Hx)).
rewrite <- (Rplus_0_r start) at 1.
now apply Rplus_lt_compat_l.
rewrite <- Rplus_assoc.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
fold ((start + start)/2)%R.
rewrite double_div2.
apply Rplus_le_compat_l.
replace (Z2R nb_steps * step * / 2)%R with (Z2R nb_steps * /2 * step)%R by ring.
rewrite <- (Rmult_1_l step) at 1.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Rmult_le_reg_r with 2%R.
now apply (Z2R_lt 0 2).
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
change 2%R with (Z2R 2).
rewrite <- (mult_Z2R 1).
apply Z2R_le.
exact (Zlt_le_succ _ _ Hnb_steps).
now apply (Z2R_neq 2 0).
Qed.

Lemma middle_odd :
  forall k,
  (2 * k + 1 = nb_steps)%Z ->
  (((start + Z2R k * step) + (start + Z2R (k + 1) * step))/2 = start + Z2R nb_steps * step * /2)%R.
Proof.
intros k Hk.
apply Rminus_diag_uniq.
rewrite plus_Z2R.
simpl (Z2R 1).
unfold Rdiv.
match goal with
| |- ?v = R0 => replace v with (start * (2 * /2 + -1) + step * /2 * ((2 * Z2R k + 1) - Z2R nb_steps))%R by ring
end.
rewrite Rinv_r, Rplus_opp_r, Rmult_0_r, Rplus_0_l.
apply Rmult_eq_0_compat_l.
change (Z2R 2 * Z2R k + Z2R 1 - Z2R nb_steps = 0)%R.
rewrite <- mult_Z2R, <- plus_Z2R, <- minus_Z2R.
now rewrite Hk, Zminus_diag.
now apply (Z2R_neq 2 0).
Qed.

Theorem inbetween_step_Lo_Mi_odd :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  l = loc_Eq \/ l = loc_Lo ->
  (2 * k + 1 = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x loc_Lo.
Proof.
intros x k l Hx Hl Hk.
constructor.
(* . *)
apply Rlt_le_trans with (start + Z2R k * step)%R.
rewrite <- (Rplus_0_r start) at 1.
apply Rplus_lt_compat_l.
apply Rmult_lt_0_compat with (2 := Hstep).
apply (Z2R_lt 0).
omega.
refine (proj1 (inbetween_bounds _ _ _ _ _ Hx)).
apply Rlt_le.
apply ordered_steps.
(* . *)
rewrite <- Rplus_assoc.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
fold ((start + start)/2)%R.
rewrite double_div2.
destruct Hx as [Hx|Hx1 Hx2|Hx|Hx1 Hx2] ; try (now elim Hl) ; clear Hl.
(* .. *)
rewrite Hx.
apply Rplus_lt_compat_l.
apply Rmult_lt_reg_r with 2%R.
now apply (Z2R_lt 0 2).
rewrite (Rmult_assoc (Z2R nb_steps * step)), Rinv_l, Rmult_1_r.
replace (Z2R k * step * 2)%R with (Z2R k * 2 * step)%R by ring.
apply Rmult_lt_compat_r with (1 := Hstep).
change 2%R with (Z2R 2).
rewrite <- mult_Z2R.
apply Z2R_lt.
omega.
now apply (Z2R_neq 2 0).
(* .. *)
now rewrite <- middle_odd with (1 := Hk).
Qed.

Theorem inbetween_step_Hi_Mi_odd :
  forall x k,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x loc_Hi ->
  (2 * k + 1 = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x loc_Hi.
Proof.
intros x k Hx Hk.
constructor.
(* . *)
rewrite <- Rplus_assoc.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
fold ((start + start)/2)%R.
rewrite double_div2.
inversion_clear Hx.
now rewrite <- middle_odd with (1 := Hk).
(* . *)
apply Rlt_le_trans with (start + Z2R (k + 1) * step)%R.
exact (proj2 (inbetween_bounds_strict _ _ _ _ (ordered_steps _) Hx)).
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Z2R_le.
omega.
Qed.

Theorem inbetween_step_Hi_Mi_even :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  l <> loc_Eq ->
  (2 * k = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x loc_Hi.
Proof.
intros x k l Hx Hl Hk.
constructor.
(* . *)
rewrite <- Rplus_assoc.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
fold ((start + start)/2)%R.
rewrite double_div2.
replace (Z2R nb_steps * step * / 2)%R with (Z2R k * step)%R.
exact (proj1 (inbetween_bounds_strict_not_Eq _ _ _ _ (ordered_steps _) Hx Hl)).
rewrite <- Hk, mult_Z2R.
simpl (Z2R 2).
replace (2 * Z2R k * step * / 2)%R with (Z2R k * step * (2 * /2))%R by ring.
rewrite Rinv_r, Rmult_1_r.
apply refl_equal.
now apply (Z2R_neq 2 0).
(* . *)
apply Rlt_le_trans with (start + Z2R (k + 1) * step)%R.
exact (proj2 (inbetween_bounds_strict _ _ _ _ (ordered_steps _) Hx)).
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Z2R_le.
omega.
Qed.

Theorem inbetween_step_Mi_Mi_even :
  forall x k,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x loc_Eq ->
  (2 * k = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x loc_Mi.
Proof.
intros x k Hx Hk.
constructor.
inversion_clear Hx.
rewrite <- Rplus_assoc.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
fold ((start + start)/2)%R.
rewrite double_div2.
rewrite H.
apply f_equal.
rewrite <- Hk, mult_Z2R.
simpl (Z2R 2).
replace (2 * Z2R k * step * / 2)%R with (Z2R k * step * (2 * /2))%R by ring.
rewrite Rinv_r, Rmult_1_r.
apply refl_equal.
now apply (Z2R_neq 2 0).
Qed.

Theorem inbetween_step_Mi_Mi_odd :
  forall x k,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x loc_Mi ->
  (2 * k + 1 = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x loc_Mi.
Proof.
intros x k Hx Hk.
constructor.
inversion_clear Hx.
rewrite H.
rewrite middle_odd with (1 := Hk).
rewrite <- Rplus_assoc.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
fold ((start + start)/2)%R.
now rewrite double_div2.
Qed.

Definition new_location_even k l :=
  if Zeq_bool k 0 then
    match l with loc_Eq => loc_Eq | _ => loc_Lo end
  else
    match Zcompare (2 * k) nb_steps with
    | Lt => loc_Lo
    | Eq => match l with loc_Eq => loc_Mi | _ => loc_Hi end
    | Gt => loc_Hi
    end.

Theorem new_location_even_correct :
  Zeven nb_steps ->
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
set (l' := match l with loc_Eq => loc_Eq | _ => loc_Lo end).
assert ((l = loc_Eq /\ l' = loc_Eq) \/ (l <> loc_Eq /\ l' = loc_Lo)).
unfold l' ; case l ; try (now left) ; right ; now split.
destruct H as [(H1,H2)|(H1,H2)] ; rewrite H2.
constructor.
rewrite H1 in Hx.
now inversion_clear Hx.
now apply inbetween_step_Lo_Eq with (2 := H1).
(* k <> 0 *)
destruct (Zcompare_spec (2 * k) nb_steps) as [Hk1|Hk1|Hk1].
(* . 2 * k < nb_steps *)
apply inbetween_step_Lo with (1 := Hx).
case (Z_le_lt_eq_dec _ _ (proj1 Hk)).
easy.
intros H.
rewrite <- H in Hk0.
now elim Hk0.
destruct (Zeven_ex _ He).
omega.
(* . 2 * k = nb_steps *)
set (l' := match l with loc_Eq => loc_Mi | _ => loc_Hi end).
assert ((l = loc_Eq /\ l' = loc_Mi) \/ (l <> loc_Eq /\ l' = loc_Hi)).
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
    match l with loc_Eq => loc_Eq | _ => loc_Lo end
  else
    match Zcompare (2 * k + 1) nb_steps with
    | Lt => loc_Lo
    | Eq => match l with loc_Mi => loc_Mi | loc_Hi => loc_Hi | _ => loc_Lo end
    | Gt => loc_Hi
    end.

Theorem new_location_odd_correct :
  Zodd nb_steps ->
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
set (l' := match l with loc_Eq => loc_Eq | _ => loc_Lo end).
assert ((l = loc_Eq /\ l' = loc_Eq) \/ (l <> loc_Eq /\ l' = loc_Lo)).
unfold l' ; case l ; try (now left) ; right ; now split.
destruct H as [(H1,H2)|(H1,H2)] ; rewrite H2.
constructor.
rewrite H1 in Hx.
now inversion_clear Hx.
now apply inbetween_step_Lo_Eq with (2 := H1).
(* k <> 0 *)
destruct (Zcompare_spec (2 * k + 1) nb_steps) as [Hk1|Hk1|Hk1].
(* . 2 * k + 1 < nb_steps *)
apply inbetween_step_Lo with (1 := Hx) (3 := Hk1).
case (Z_le_lt_eq_dec _ _ (proj1 Hk)).
easy.
intros H.
rewrite <- H in Hk0.
now elim Hk0.
(* . 2 * k + 1 = nb_steps *)
destruct l.
apply inbetween_step_Lo_Mi_odd with (1 := Hx) (3 := Hk1).
now left.
apply inbetween_step_Lo_Mi_odd with (1 := Hx) (3 := Hk1).
now right.
apply inbetween_step_Mi_Mi_odd with (1 := Hx) (2 := Hk1).
apply inbetween_step_Hi_Mi_odd with (1 := Hx) (2 := Hk1).
(* . 2 * k + 1 > nb_steps *)
apply inbetween_step_Hi with (1 := Hx).
destruct (Zodd_ex _ Ho).
omega.
apply Hk.
Qed.

Definition new_location :=
  match nb_steps with
  | Zpos (xO _) => new_location_even
  | Zpos (xI _) => new_location_odd
  | _ => fun _ l => l
  end.

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
rewrite Hp.
change (Zpos (xI p)) with (1 + 2 * Zpos p)%Z.
rewrite Zplus_comm.
apply Zodd_2p_plus_1.
apply new_location_even_correct with (2 := Hk) (3 := Hx).
rewrite Hp.
exact (Zeven_2p (Zpos p)).
now rewrite Hp in Hnb_steps.
(* . *)
now intros p _.
Qed.

End Fcalc_bracket_step.

Section Fcalc_bracket_NE.

Theorem Rnd_N_pt_bracket_not_Hi :
  forall F d u x l,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  inbetween d u x l ->
  l <> loc_Hi -> Rnd_N_pt F x d.
Proof.
intros F d u x l Hd Hu Hx Hl.
split.
apply Hd.
intros g Hg.
rewrite Rabs_left1. 2: apply Rle_minus ; apply Hd.
rewrite Ropp_minus_distr.
destruct (Rnd_DN_UP_pt_split  _ _ _ _ Hd Hu g Hg) as [H|H].
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rplus_le_compat_l.
now apply Ropp_le_contravar.
apply Rle_minus.
apply Rle_trans with (1 := H).
apply Hd.
rewrite Rabs_pos_eq.
apply Rplus_le_reg_r with (x + d)%R.
ring_simplify.
apply Rle_trans with (d + u)%R.
apply Rmult_le_reg_l with (/2)%R.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l.
rewrite Rmult_comm.
refine (proj2 (inbetween_not_Hi _ _ _ _ _ Hx Hl)).
apply Rle_trans with x.
apply Hd.
apply Hu.
now apply (Z2R_neq 2 0).
now apply Rplus_le_compat_l.
apply Rle_0_minus.
apply Rle_trans with (2 := H).
apply Hu.
Qed.

Theorem Rnd_N_pt_bracket_Mi_Hi :
  forall F d u x l,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  inbetween d u x l ->
  l = loc_Mi \/ l = loc_Hi ->
  Rnd_N_pt F x u.
Proof.
intros F d u x l Hd Hu Hx Hl.
split.
apply Hu.
intros g Hg.
rewrite Rabs_pos_eq. 2: now apply Rle_0_minus ; apply Hu.
destruct (Rnd_DN_UP_pt_split  _ _ _ _ Hd Hu g Hg) as [H|H].
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rplus_le_reg_r with (x + g)%R.
ring_simplify.
apply Rle_trans with (u + d)%R.
now apply Rplus_le_compat_l.
rewrite Rplus_comm.
apply Rmult_le_reg_l with (/2)%R.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l.
rewrite Rmult_comm.
refine (proj1 (inbetween_Mi_Hi _ _ _ _ _ Hx Hl)).
apply Rle_trans with x.
apply Hd.
apply Hu.
now apply (Z2R_neq 2 0).
apply Rle_minus.
apply Rle_trans with (1 := H).
apply Hd.
rewrite Rabs_pos_eq.
now apply Rplus_le_compat_r.
apply Rle_0_minus.
apply Rle_trans with (2 := H).
apply Hu.
Qed.

End Fcalc_bracket_NE.

Section Fcalc_bracket_generic.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.
Notation format := (generic_format beta fexp).

Definition inbetween_float m e x l :=
  inbetween (F2R (Float beta m e)) (F2R (Float beta (m + 1) e)) x l.

Theorem inbetween_float_new_location :
  forall x m e l,
  inbetween_float m e x l ->
  inbetween_float (Zdiv m (radix_val beta)) (e + 1) x (new_location (radix_val beta) (Zmod m (radix_val beta)) l).
Proof.
intros x m e l Hx.
unfold inbetween_float in *.
assert (Hr: forall m, F2R (Float beta m (e + 1)) = F2R (Float beta (m * radix_val beta) e)).
clear. intros m.
rewrite (F2R_change_exp beta e). 2: apply Zle_succ.
apply (f_equal (fun r => F2R (Float beta (m * r) e))).
replace (e + 1 - e)%Z with 1%Z by ring.
apply Zmult_1_r.
(* . *)
rewrite 2!Hr.
rewrite Zmult_plus_distr_l, Zmult_1_l.
unfold F2R at 2. simpl.
rewrite plus_Z2R, Rmult_plus_distr_r.
apply new_location_correct.
apply bpow_gt_0.
apply Zgt_lt.
apply Zlt_succ_gt.
apply beta.
apply Z_mod_lt.
apply Zlt_gt.
now apply Zlt_le_trans with (2 := radix_prop beta).
rewrite <- 2!Rmult_plus_distr_r, <- 2!plus_Z2R.
rewrite Zmult_comm, Zplus_assoc.
rewrite <- Z_div_mod_eq.
exact Hx.
apply Zlt_gt.
now apply Zlt_le_trans with (2 := radix_prop beta).
Qed.

Theorem inbetween_float_DN :
  forall x m e l, (0 < m)%Z ->
  inbetween_float m e x l ->
  canonic beta fexp (Float beta m e) ->
  Rnd_DN_pt format x (F2R (Float beta m e)).
Proof.
intros x m e l Hm Hl Hc.
assert (Hb: (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R).
apply inbetween_bounds_strict with (2 := Hl).
apply F2R_lt_compat.
apply Zlt_succ.
assert (Hf := generic_format_canonic _ _ _ Hc).
split.
exact Hf.
split.
exact (proj1 Hb).
intros g Hg Hgx.
apply Rnot_lt_le.
intros Hg1.
apply Rle_not_lt with (1 := Hgx). clear Hgx.
apply Rlt_le_trans with (1 := proj2 Hb).
apply Rnot_lt_le.
intros Hg2.
exact (generic_format_discrete _ _ _ _ Hm Hc _ (conj Hg1 Hg2) Hg).
Qed.

Definition cond_incr (b : bool) m := if b then (m + 1)%Z else m.

Definition round_UP l :=
  match l with
  | loc_Eq => false
  | _ => true
  end.

Theorem inbetween_float_UP :
  forall x m e l, (0 < m)%Z ->
  inbetween_float m e x l ->
  canonic beta fexp (Float beta m e) ->
  Rnd_UP_pt format x (F2R (Float beta (cond_incr (round_UP l) m) e)).
Proof.
intros x m e l Hm Hl Hc.
assert (Hl': l = loc_Eq \/ l <> loc_Eq).
case l ; try (now left) ; now right.
destruct Hl' as [Hl'|Hl'].
(* loc_Eq *)
rewrite Hl' in Hl.
inversion_clear Hl.
rewrite H, Hl'.
apply Rnd_UP_pt_refl.
now apply generic_format_canonic.
(* not loc_Eq *)
replace (round_UP l) with true.
assert (Hb: (F2R (Float beta m e) < x < F2R (Float beta (m + 1) e))%R).
apply inbetween_bounds_strict_not_Eq with (2 := Hl).
apply F2R_lt_compat.
apply Zlt_succ.
exact Hl'.
assert (Hd := inbetween_float_DN _ _ _ _ Hm Hl Hc).
simpl.
replace (F2R (Float beta (m + 1) e)) with (F2R (Float beta m e) + ulp beta fexp x)%R.
apply ulp_DN_UP_pt ; try easy.
intros Fx.
apply Rlt_not_le with (1 := proj1 Hb).
apply Req_le.
apply Rnd_DN_pt_unicity with (2 := Hd).
now apply Rnd_DN_pt_refl.
rewrite <- ulp_DN_pt_eq with (3 := Hd).
unfold ulp.
rewrite <- Hc.
unfold F2R. simpl.
rewrite plus_Z2R.
simpl. ring.
exact prop_exp.
now apply F2R_gt_0_compat.
clear -Hl'.
destruct l ; try easy.
now elim Hl'.
Qed.

Definition round_NE (p : bool) l :=
  match l with
  | loc_Eq => false
  | loc_Lo => false
  | loc_Mi => if p then false else true
  | loc_Hi => true
  end.

Theorem inbetween_float_NE :
  forall x m e l, (0 < m)%Z ->
  inbetween_float m e x l ->
  canonic beta fexp (Float beta m e) ->
  Rnd_NE_pt beta fexp x (F2R (Float beta (cond_incr (round_NE (projT1 (Zeven_odd_bool m)) l) m) e)).
Proof.
intros x m e l Hm Hl Hc.
assert (Hd := inbetween_float_DN _ _ _ _ Hm Hl Hc).
unfold round_NE.
generalize (inbetween_float_UP _ _ _ _ Hm Hl Hc).
destruct l ; simpl ; intros Hu.
(* loc_Eq *)
inversion_clear Hl.
rewrite H.
apply Rnd_NG_pt_refl.
apply Hd.
(* loc_Lo *)
split.
now apply (Rnd_N_pt_bracket_not_Hi _ _ _ _ _ Hd Hu Hl).
right.
admit.
(* loc_Mi *)
destruct (Zeven_odd_bool m) as ([|], Heo) ; simpl.
split.
now apply (Rnd_N_pt_bracket_not_Hi _ _ _ _ _ Hd Hu Hl).
left.
now eexists ; repeat split.
split.
apply (Rnd_N_pt_bracket_Mi_Hi _ _ _ _ _ Hd Hu Hl).
now left.
left.
admit.
(* loc_Hi *)
split.
apply (Rnd_N_pt_bracket_Mi_Hi _ _ _ _ _ Hd Hu Hl).
now right.
right.
admit.
Qed.

End Fcalc_bracket_generic.

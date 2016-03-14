Require Import Reals.
Require Import Fcore.
Require Import Fcalc_ops.
Require Import Psatz.
Require Import Fprop_relative.
Require Import Fprop_plus_error.

Section Theory.

Variable emin : Z.
Variable prec : Z.
Context {Hprec : Prec_gt_0 prec}.

Notation fexp := (FLT_exp emin prec).

Definition Bmin := bpow radix2 (emin + prec).

Definition hombnd (m M u v : R) (b B : float radix2) :=
  (0 <= F2R b)%R /\ (1 <= F2R B)%R /\
  ((Bmin <= m)%R -> (Rabs (u - v) <= F2R b * M)%R /\ (Rabs v <= F2R B * M)%R).

Lemma hombnd_fact :
  forall m M1 M2 u v b B,
  (M1 <= M2)%R ->
  hombnd m M1 u v b B ->
  hombnd m M2 u v b B.
Proof.
intros m M1 M2 u v b B HM [H1 [H2 H]].
refine (conj H1 (conj H2 _)).
intros H0.
destruct (H H0) as [H3 H4].
split.
apply Rle_trans with (1 := H3).
now apply Rmult_le_compat_l.
apply Rle_trans with (1 := H4).
apply Rmult_le_compat_l with (2 := HM).
now apply Rle_trans with (1 := Rle_0_1).
Qed.

Lemma hombnd_cond :
  forall m1 m2 M u v b B,
  (m2 <= m1)%R ->
  hombnd m1 M u v b B ->
  hombnd m2 M u v b B.
Proof.
intros m1 m2 M u v b B Hm [H1 [H2 H]].
refine (conj H1 (conj H2 _)).
intros H0.
apply H.
now apply Rle_trans with (2 := Hm).
Qed.

Lemma hombnd_cond' :
  forall m M u v b B,
  hombnd (Rmin Bmin m) M u v b B ->
  hombnd m M u v b B.
Proof.
intros m M u v b B [H1 [H2 H]].
refine (conj H1 (conj H2 _)).
intros H0.
apply H.
apply Rmin_glb with (2 := H0).
apply Rle_refl.
Qed.

Lemma hombnd_plus :
  forall m M u1 v1 b1 B1 u2 v2 b2 B2,
  hombnd m M u1 v1 b1 B1 ->
  hombnd m M u2 v2 b2 B2 ->
  hombnd m M (u1 + u2) (v1 + v2) (Fplus radix2 b1 b2) (Fplus radix2 B1 B2).
Proof.
intros m M u1 v1 b1 B1 u2 v2 b2 B2 [H11 [H12 H1]] [H21 [H22 H2]].
unfold hombnd.
rewrite F2R_plus.
split.
now apply Rplus_le_le_0_compat.
rewrite F2R_plus.
split.
clear -H12 H22 ; lra.
intros H.
destruct (H1 H) as [H13 H14].
destruct (H2 H) as [H23 H24].
rewrite 2!Rmult_plus_distr_r.
replace ((u1 + u2) - (v1 + v2))%R with ((u1 - v1) + (u2 - v2))%R by ring.
split ;
  apply Rle_trans with (1 := Rabs_triang _ _) ;
  now apply Rplus_le_compat.
Qed.

Lemma hombnd_minus :
  forall m M u1 v1 b1 B1 u2 v2 b2 B2,
  hombnd m M u1 v1 b1 B1 ->
  hombnd m M u2 v2 b2 B2 ->
  hombnd m M (u1 - u2) (v1 - v2) (Fplus radix2 b1 b2) (Fplus radix2 B1 B2).
Proof.
intros m M u1 v1 b1 B1 u2 v2 b2 B2 H1 [H21 [H22 H2]].
apply hombnd_plus with (1 := H1).
refine (conj H21 (conj H22 _)).
intros H.
destruct (H2 H) as [H23 H24].
replace (- u2 - - v2)%R with (- (u2 - v2))%R by ring.
rewrite 2!Rabs_Ropp.
now split.
Qed.

Definition mult_err b1 B1 b2 B2 :=
  Fplus radix2 (Fplus radix2 (Fmult radix2 b1 B2) (Fmult radix2 B1 b2)) (Fmult radix2 b1 b2).

Lemma hombnd_mult :
  forall m M1 u1 v1 b1 B1 M2 u2 v2 b2 B2,
  hombnd m M1 u1 v1 b1 B1 ->
  hombnd m M2 u2 v2 b2 B2 ->
  hombnd m (M1 * M2) (u1 * u2) (v1 * v2) (mult_err b1 B1 b2 B2) (Fmult radix2 B1 B2).
Proof.
intros m M1 u1 v1 b1 B1 M2 u2 v2 b2 B2 [H11 [H12 H1]] [H21 [H22 H2]].
unfold hombnd, mult_err.
rewrite 2!F2R_plus, 4!F2R_mult.
split.
apply Rplus_le_le_0_compat.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos with (1 := H11).
now apply Rle_trans with (1 := Rle_0_1).
apply Rmult_le_pos with (2 := H21).
now apply Rle_trans with (1 := Rle_0_1).
now apply Rmult_le_pos.
split.
rewrite <- (Rmult_1_r 1).
now apply Rmult_le_compat ; try apply Rle_0_1.
intros H.
destruct (H1 H) as [H13 H14].
destruct (H2 H) as [H23 H24].
assert (H0: forall u v, ((u * v) * (M1 * M2) = (u * M1) * (v * M2))%R).
  intros u v ; ring.
split.
replace (u1 * u2 - v1 * v2)%R
  with ((u1 - v1) * v2 + v1 * (u2 - v2) + (u1 - v1) * (u2 - v2))%R by ring.
rewrite 2!Rmult_plus_distr_r.
rewrite 3!H0.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
rewrite Rabs_mult.
now apply Rmult_le_compat ; try apply Rabs_pos.
rewrite Rabs_mult.
now apply Rmult_le_compat ; try apply Rabs_pos.
rewrite Rabs_mult.
now apply Rmult_le_compat ; try apply Rabs_pos.
rewrite H0, Rabs_mult.
now apply Rmult_le_compat ; try apply Rabs_pos.
Qed.

Definition round_err b B :=
  Fplus radix2 (Fmult radix2 (Fplus radix2 b B) (Float radix2 1 (- prec))) b.

Lemma hombnd_rnd :
  forall m M u v b B,
  hombnd m M u v b B ->
  hombnd (Rmin m M) M (round radix2 fexp ZnearestE u) v (round_err b B) B.
Proof with auto with typeclass_instances.
intros m M u v b B [Ho1 [Ho2 Ho]].
unfold hombnd, round_err.
rewrite F2R_plus, F2R_mult, F2R_plus.
split.
apply Rplus_le_le_0_compat with (2 := Ho1).
apply Rmult_le_pos.
apply Rplus_le_le_0_compat with (1 := Ho1).
now apply Rle_trans with (1 := Rle_0_1).
now apply F2R_ge_0_compat.
apply (conj Ho2).
intros H.
specialize (Ho (Rle_trans _ _ _ H (Rmin_l _ _))).
destruct Ho as [Ho3 Ho4].
refine (conj _ Ho4).
replace (round radix2 fexp ZnearestE u - v)%R
  with ((round radix2 fexp ZnearestE u - u) + (u - v))%R by ring.
rewrite Rmult_plus_distr_r.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat with (2 := Ho3).
apply Rle_trans with (1 := error_le_half_ulp _ _ _ _).
apply Rmult_le_reg_l with 2%R.
apply Rlt_0_2.
rewrite <- (Rmult_assoc 2), Rinv_r, Rmult_1_l by apply Rgt_not_eq, Rlt_0_2.
assert (HM : (0 <= M)%R).
  apply Rle_trans with (2 := Rmin_r m M).
  apply Rle_trans with (2 := H).
  apply bpow_ge_0.
assert (H' : (0 <= (F2R b + F2R B) * M)%R).
  apply Rmult_le_pos with (2 := HM).
  apply Rplus_le_le_0_compat with (1 := Ho1).
  now apply Rle_trans with (1 := Rle_0_1).
apply Rle_trans with (ulp radix2 fexp ((F2R b + F2R B) * M)).
apply ulp_le...
rewrite Rabs_pos_eq with (1 := H').
rewrite Rmult_plus_distr_r.
replace u with (u - v + v)%R by ring.
apply Rle_trans with (1 := Rabs_triang _ _).
now apply Rplus_le_compat.
replace (2 * ((F2R b + F2R B) * F2R {| Fnum := 1; Fexp := - prec |} * M))%R
  with ((F2R b + F2R B) * M * bpow radix2 (1 - prec))%R.
rewrite <- Rabs_pos_eq with (1 := H') at 2.
apply ulp_FLT_le.
rewrite Rabs_pos_eq with (1 := H').
apply Rle_trans with (1 := H).
apply Rle_trans with (1 := Rmin_r _ _).
rewrite <- (Rmult_1_l M) at 1.
rewrite <- (Rplus_0_l 1).
apply Rmult_le_compat_r with (1 := HM).
now apply Rplus_le_compat.
unfold Zminus.
rewrite bpow_plus.
simpl (bpow radix2 1).
rewrite F2R_bpow.
ring.
Qed.

End Theory.

Section Example.

Definition fxp := FLT_exp (-1074) 53.
Definition add x y := round radix2 fxp ZnearestE (x + y).
Definition sub x y := round radix2 fxp ZnearestE (x - y).
Definition mul x y := round radix2 fxp ZnearestE (x * y).

Definition hombnd' := hombnd (-1074) 53.

Lemma hombnd_sub_init :
  forall u v,
  generic_format radix2 fxp u ->
  generic_format radix2 fxp v ->
  hombnd' (Bmin (-1074) 53) (Rabs (u - v)) (sub u v) (u - v) (Float radix2 1 (-53)) (Float radix2 1 0).
Proof.
intros u v Fu Fv.
split.
now apply F2R_ge_0_compat.
unfold F2R at 1 3 ; simpl.
rewrite 2!Rmult_1_l.
repeat split ; try apply Rle_refl.
unfold sub.
destruct (Rle_or_lt (Rabs (u - v)) (bpow radix2 (53 + -1074))) as [S|S].
rewrite round_generic.
unfold Rminus at 1.
rewrite Rplus_opp_r, Rabs_R0.
apply Rmult_le_pos.
now apply F2R_ge_0_compat.
apply Rabs_pos.
apply valid_rnd_N.
apply FLT_format_plus_small ; try easy.
now apply generic_format_opp.
replace (F2R (Float radix2 1 (-53))) with (bpow radix2 (-1) * bpow radix2 (-53 + 1))%R.
apply relative_error_N_FLT.
easy.
apply Rlt_le.
apply Rle_lt_trans with (2 := S).
now apply bpow_le.
rewrite <- bpow_plus.
unfold F2R.
rewrite Rmult_1_l.
now apply f_equal.
Qed.

Lemma hombnd_fact' :
  forall {m M1 M2 u v b B},
  (M1 <= M2)%R ->
  hombnd' m M1 u v b B ->
  hombnd' m M2 u v b B.
Proof.
apply hombnd_fact.
Qed.

Lemma hombnd_cond'' :
  forall {m1 m2 M u v b B},
  (m2 <= m1)%R ->
  hombnd' m1 M u v b B ->
  hombnd' m2 M u v b B.
Proof.
apply hombnd_cond.
Qed.

Lemma hombnd_add :
  forall {m M u1 v1 b1 B1 u2 v2 b2 B2},
  hombnd' m M u1 v1 b1 B1 ->
  hombnd' m M u2 v2 b2 B2 ->
  hombnd' m M (u1 + u2) (v1 + v2) (Fplus radix2 b1 b2) (Fplus radix2 B1 B2).
Proof.
apply hombnd_plus.
Qed.

Lemma hombnd_sub :
  forall {m M u1 v1 b1 B1 u2 v2 b2 B2},
  hombnd' m M u1 v1 b1 B1 ->
  hombnd' m M u2 v2 b2 B2 ->
  hombnd' m M (u1 - u2) (v1 - v2) (Fplus radix2 b1 b2) (Fplus radix2 B1 B2).
Proof.
apply hombnd_minus.
Qed.

Lemma hombnd_mul :
  forall {m M1 u1 v1 b1 B1 M2 u2 v2 b2 B2},
  hombnd' m M1 u1 v1 b1 B1 ->
  hombnd' m M2 u2 v2 b2 B2 ->
  hombnd' m (M1 * M2) (u1 * u2) (v1 * v2) (mult_err b1 B1 b2 B2) (Fmult radix2 B1 B2).
Proof.
apply hombnd_mult.
Qed.

Lemma hombnd_rnd' :
  forall {m M u v b B},
  hombnd' m M u v b B ->
  hombnd' (Rmin m M) M (round radix2 fxp ZnearestE u) v (round_err 53 b B) B.
Proof.
now apply hombnd_rnd.
Qed.

Lemma hombnd_rnd'' :
  forall {M u v b B},
  hombnd' (Bmin (-1074) 53) M u v b B ->
  hombnd' M M (round radix2 fxp ZnearestE u) v (round_err 53 b B) B.
Proof.
intros M u v b B H.
apply hombnd_cond'.
now apply hombnd_rnd'.
Qed.

Definition orient2d x1 y1 x2 y2 x3 y3 :=
  sub (mul (sub x1 x3) (sub y2 y3)) (mul (sub x2 x3) (sub y1 y3)).

Definition orient2d_exact x1 y1 x2 y2 x3 y3 :=
  ((x1 - x3) * (y2 - y3) - (x2 - x3) * (y1 - y3))%R.

Definition norm2d x y := Rmax (Rabs x) (Rabs y).

Lemma orient2d_spec :
  forall x1 y1 x2 y2 x3 y3,
  generic_format radix2 fxp x1 ->
  generic_format radix2 fxp y1 ->
  generic_format radix2 fxp x2 ->
  generic_format radix2 fxp y2 ->
  generic_format radix2 fxp x3 ->
  generic_format radix2 fxp y3 ->
  let M := (norm2d (x1 - x3) (x2 - x3) * norm2d (y1 - y3) (y2 - y3))%R in
  hombnd' M M (orient2d x1 y1 x2 y2 x3 y3) (orient2d_exact x1 y1 x2 y2 x3 y3)
    (Float radix2 5846006549323612646370400306145384485685829828610 (-212)) (Float radix2 2 0).
Proof.
intros x1 y1 x2 y2 x3 y3 Fx1 Fy1 Fx2 Fy2 Fx3 Fy3.
assert (Sx13 := hombnd_sub_init x1 x3 Fx1 Fx3).
assert (Sy13 := hombnd_sub_init y1 y3 Fy1 Fy3).
assert (Sx23 := hombnd_sub_init x2 x3 Fx2 Fx3).
assert (Sy23 := hombnd_sub_init y2 y3 Fy2 Fy3).
apply (hombnd_fact' (Rmax_l _ (Rabs (x2 - x3)))) in Sx13.
apply (hombnd_fact' (Rmax_l _ (Rabs (y2 - y3)))) in Sy13.
apply (hombnd_fact' (Rmax_r (Rabs (x1 - x3)) _)) in Sx23.
apply (hombnd_fact' (Rmax_r (Rabs (y1 - y3)) _)) in Sy23.
assert (M1 := hombnd_mul Sx13 Sy23).
assert (M2 := hombnd_mul Sx23 Sy13).
clear Sx13 Sy23 Sx23 Sy13.
apply hombnd_rnd'' in M1.
apply hombnd_rnd'' in M2.
assert (D := hombnd_sub M1 M2).
clear M1 M2.
apply hombnd_rnd' in D.
rewrite Rmin_left in D by apply Rle_refl.
(*
match goal with
| H: hombnd' _ _ _ _ ?err _ |- _ => let e := eval vm_compute in err in idtac e
end.
*)
exact D.
Qed.

Lemma Rmax_assoc :
  forall x y z,
  Rmax x (Rmax y z) = Rmax (Rmax x y) z.
Proof.
intros x y z.
unfold Rmax.
destruct (Rle_dec x y) as [Hxy|Hxy].
destruct (Rle_dec y) as [Hyz|Hyz].
assert (Hxz := Rle_trans _ _ _ Hxy Hyz).
now case Rle_dec.
now case Rle_dec.
destruct (Rle_dec y) as [Hyz|Hyz].
easy.
case Rle_dec ; try easy.
intros _.
case Rle_dec ; try easy.
intros Hxz.
elim Hxy.
apply Rle_trans with (1 := Hxz).
apply Rlt_le.
now apply Rnot_le_lt.
Qed.

Lemma Rmin_max :
  forall x y,
  Rmin (Rmin x y) (Rmax x y) = Rmin x y.
Proof.
intros x y.
apply Rmin_left.
apply Rle_trans with x.
apply Rmin_l.
apply Rmax_l.
Qed.

Lemma Rmin_min :
  forall x y,
  Rmin (Rmin x y) y = Rmin x y.
Proof.
intros x y.
apply Rmin_left.
apply Rmin_r.
Qed.

Definition incircle2d x1 y1 x2 y2 x3 y3 x4 y4 :=
  let X1 := sub x1 x4 in
  let X2 := sub x2 x4 in
  let X3 := sub x3 x4 in
  let Y1 := sub y1 y4 in
  let Y2 := sub y2 y4 in
  let Y3 := sub y3 y4 in
  let Z1 := add (mul X1 X1) (mul Y1 Y1) in
  let Z2 := add (mul X2 X2) (mul Y2 Y2) in
  let Z3 := add (mul X3 X3) (mul Y3 Y3) in
  add (add
    (mul (sub (mul X1 Y2) (mul X2 Y1)) Z3)
    (mul (sub (mul X2 Y3) (mul X3 Y2)) Z1))
    (mul (sub (mul X3 Y1) (mul X1 Y3)) Z2).

Definition incircle2d_exact x1 y1 x2 y2 x3 y3 x4 y4 :=
 (let X1 := x1 - x4 in
  let X2 := x2 - x4 in
  let X3 := x3 - x4 in
  let Y1 := y1 - y4 in
  let Y2 := y2 - y4 in
  let Y3 := y3 - y4 in
  let Z1 := X1 * X1 + Y1 * Y1 in
  let Z2 := X2 * X2 + Y2 * Y2 in
  let Z3 := X3 * X3 + Y3 * Y3 in
  (X1 * Y2 - X2 * Y1) * Z3 +
  (X2 * Y3 - X3 * Y2) * Z1 +
  (X3 * Y1 - X1 * Y3) * Z2)%R.

Definition norm3d x y z := Rmax (Rmax (Rabs x) (Rabs y)) (Rabs z).

Lemma incircle2d_spec :
  forall x1 y1 x2 y2 x3 y3 x4 y4,
  generic_format radix2 fxp x1 ->
  generic_format radix2 fxp y1 ->
  generic_format radix2 fxp x2 ->
  generic_format radix2 fxp y2 ->
  generic_format radix2 fxp x3 ->
  generic_format radix2 fxp y3 ->
  generic_format radix2 fxp x4 ->
  generic_format radix2 fxp y4 ->
  let Nx := norm3d (x1 - x4) (x2 - x4) (x3 - x4) in
  let Ny := norm3d (y1 - y4) (y2 - y4) (y3 - y4) in
  let M := (Nx * Ny * Rmax (Rsqr Nx) (Rsqr Ny))%R in
  let m := Rmin (Rmin (Rsqr Nx) (Rsqr Ny)) M in
  hombnd' m M (incircle2d x1 y1 x2 y2 x3 y3 x4 y4) (incircle2d_exact x1 y1 x2 y2 x3 y3 x4 y4)
    (Float radix2 449891379454319880216566500258074099295902168735244158654493060906025297480090105222776999487941175938788545391377857876066937154874210214115994952429543498973192 (-583)) (Float radix2 12 0).
Proof.
intros x1 y1 x2 y2 x3 y3 x4 y4 Fx1 Fy1 Fx2 Fy2 Fx3 Fy3 Fx4 Fy4.
assert (X1 := hombnd_sub_init x1 x4 Fx1 Fx4).
assert (Y1 := hombnd_sub_init y1 y4 Fy1 Fy4).
assert (X2 := hombnd_sub_init x2 x4 Fx2 Fx4).
assert (Y2 := hombnd_sub_init y2 y4 Fy2 Fy4).
assert (X3 := hombnd_sub_init x3 x4 Fx3 Fx4).
assert (Y3 := hombnd_sub_init y3 y4 Fy3 Fy4).
apply (hombnd_fact' (Rmax_l _ (Rabs (x2 - x4)))) in X1.
apply (hombnd_fact' (Rmax_l _ (Rabs (x3 - x4)))) in X1.
apply (hombnd_fact' (Rmax_l _ (Rabs (y2 - y4)))) in Y1.
apply (hombnd_fact' (Rmax_l _ (Rabs (y3 - y4)))) in Y1.
apply (hombnd_fact' (Rmax_r (Rabs (x1 - x4)) _)) in X2.
apply (hombnd_fact' (Rmax_l _ (Rabs (x3 - x4)))) in X2.
apply (hombnd_fact' (Rmax_r (Rabs (y1 - y4)) _)) in Y2.
apply (hombnd_fact' (Rmax_l _ (Rabs (y3 - y4)))) in Y2.
apply (hombnd_fact' (Rmax_r (Rabs (x2 - x4)) _)) in X3.
apply (hombnd_fact' (Rmax_r (Rabs (x1 - x4)) _)) in X3.
apply (hombnd_fact' (Rmax_r (Rabs (y2 - y4)) _)) in Y3.
apply (hombnd_fact' (Rmax_r (Rabs (y1 - y4)) _)) in Y3.
rewrite Rmax_assoc in X3.
rewrite Rmax_assoc in Y3.
assert (M12 := hombnd_mul X1 Y2).
assert (M21 := hombnd_mul X2 Y1).
assert (M23 := hombnd_mul X2 Y3).
assert (M32 := hombnd_mul X3 Y2).
assert (M31 := hombnd_mul X3 Y1).
assert (M13 := hombnd_mul X1 Y3).
apply hombnd_rnd'' in M12.
apply hombnd_rnd'' in M21.
apply hombnd_rnd'' in M23.
apply hombnd_rnd'' in M32.
apply hombnd_rnd'' in M31.
apply hombnd_rnd'' in M13.
assert (D12 := hombnd_sub M12 M21).
assert (D23 := hombnd_sub M23 M32).
assert (D31 := hombnd_sub M31 M13).
apply hombnd_rnd' in D12.
apply hombnd_rnd' in D23.
apply hombnd_rnd' in D31.
rewrite Rmin_left in D12 by apply Rle_refl.
rewrite Rmin_left in D23 by apply Rle_refl.
rewrite Rmin_left in D31 by apply Rle_refl.
clear M12 M21 M23 M32 M31 M13.
assert (M1x := hombnd_mul X1 X1).
assert (M1y := hombnd_mul Y1 Y1).
assert (M2x := hombnd_mul X2 X2).
assert (M2y := hombnd_mul Y2 Y2).
assert (M3x := hombnd_mul X3 X3).
assert (M3y := hombnd_mul Y3 Y3).
clear X1 Y1 X2 Y2 X3 Y3.
apply hombnd_rnd'' in M1x.
apply hombnd_rnd'' in M1y.
apply hombnd_rnd'' in M2x.
apply hombnd_rnd'' in M2y.
apply hombnd_rnd'' in M3x.
apply hombnd_rnd'' in M3y.
apply (hombnd_cond'' (Rmin_l _ (Rsqr (norm3d (y1 - y4) (y2 - y4) (y3 - y4))))) in M1x.
apply (hombnd_cond'' (Rmin_r (Rsqr (norm3d (x1 - x4) (x2 - x4) (x3 - x4))) _)) in M1y.
apply (hombnd_fact' (Rmax_l _ (Rsqr (norm3d (y1 - y4) (y2 - y4) (y3 - y4))))) in M1x.
apply (hombnd_fact' (Rmax_r (Rsqr (norm3d (x1 - x4) (x2 - x4) (x3 - x4))) _)) in M1y.
apply (hombnd_cond'' (Rmin_l _ (Rsqr (norm3d (y1 - y4) (y2 - y4) (y3 - y4))))) in M2x.
apply (hombnd_cond'' (Rmin_r (Rsqr (norm3d (x1 - x4) (x2 - x4) (x3 - x4))) _)) in M2y.
apply (hombnd_fact' (Rmax_l _ (Rsqr (norm3d (y1 - y4) (y2 - y4) (y3 - y4))))) in M2x.
apply (hombnd_fact' (Rmax_r (Rsqr (norm3d (x1 - x4) (x2 - x4) (x3 - x4))) _)) in M2y.
apply (hombnd_cond'' (Rmin_l _ (Rsqr (norm3d (y1 - y4) (y2 - y4) (y3 - y4))))) in M3x.
apply (hombnd_cond'' (Rmin_r (Rsqr (norm3d (x1 - x4) (x2 - x4) (x3 - x4))) _)) in M3y.
apply (hombnd_fact' (Rmax_l _ (Rsqr (norm3d (y1 - y4) (y2 - y4) (y3 - y4))))) in M3x.
apply (hombnd_fact' (Rmax_r (Rsqr (norm3d (x1 - x4) (x2 - x4) (x3 - x4))) _)) in M3y.
assert (Z1 := hombnd_add M1x M1y).
assert (Z2 := hombnd_add M2x M2y).
assert (Z3 := hombnd_add M3x M3y).
clear M1x M1y M2x M2y M3x M3y.
apply hombnd_rnd' in Z1.
apply hombnd_rnd' in Z2.
apply hombnd_rnd' in Z3.
rewrite Rmin_max in Z1.
rewrite Rmin_max in Z2.
rewrite Rmin_max in Z3.
apply (hombnd_cond'' (Rmin_l _ (Rmin (Rsqr (norm3d (x1 - x4) (x2 - x4) (x3 - x4))) (Rsqr (norm3d (y1 - y4) (y2 - y4) (y3 - y4)))))) in D12.
apply (hombnd_cond'' (Rmin_l _ (Rmin (Rsqr (norm3d (x1 - x4) (x2 - x4) (x3 - x4))) (Rsqr (norm3d (y1 - y4) (y2 - y4) (y3 - y4)))))) in D23.
apply (hombnd_cond'' (Rmin_l _ (Rmin (Rsqr (norm3d (x1 - x4) (x2 - x4) (x3 - x4))) (Rsqr (norm3d (y1 - y4) (y2 - y4) (y3 - y4)))))) in D31.
apply (hombnd_cond'' (Rmin_r (norm3d (x1 - x4) (x2 - x4) (x3 - x4) * norm3d (y1 - y4) (y2 - y4) (y3 - y4)) _)) in Z1.
apply (hombnd_cond'' (Rmin_r (norm3d (x1 - x4) (x2 - x4) (x3 - x4) * norm3d (y1 - y4) (y2 - y4) (y3 - y4)) _)) in Z2.
apply (hombnd_cond'' (Rmin_r (norm3d (x1 - x4) (x2 - x4) (x3 - x4) * norm3d (y1 - y4) (y2 - y4) (y3 - y4)) _)) in Z3.
assert (M1 := hombnd_mul D12 Z3).
assert (M2 := hombnd_mul D23 Z1).
assert (M3 := hombnd_mul D31 Z2).
clear D12 D23 D31 Z1 Z2 Z3.
apply hombnd_rnd' in M1.
apply hombnd_rnd' in M2.
apply hombnd_rnd' in M3.
assert (A1 := hombnd_add M1 M2).
clear M1 M2.
apply hombnd_rnd' in A1.
rewrite Rmin_min in A1.
assert (A2 := hombnd_add A1 M3).
apply hombnd_rnd' in A2.
clear A1 M3.
rewrite Rmin_min in A2.
rewrite (Rmin_right (Rmult _ _)) in A2.
exact A2.
clear.
unfold Rmin.
destruct Rle_dec as [H|H].
apply Rsqr_incr_0 in H.
apply Rmult_le_compat_l with (2 := H).
repeat apply Rmax_case ; apply Rabs_pos.
unfold norm3d ; repeat apply Rmax_case ; apply Rabs_pos.
unfold norm3d ; repeat apply Rmax_case ; apply Rabs_pos.
apply Rnot_le_lt in H.
apply Rlt_le in H.
apply Rsqr_incr_0 in H.
apply Rmult_le_compat_r with (2 := H).
repeat apply Rmax_case ; apply Rabs_pos.
unfold norm3d ; repeat apply Rmax_case ; apply Rabs_pos.
unfold norm3d ; repeat apply Rmax_case ; apply Rabs_pos.
Qed.

End Example.

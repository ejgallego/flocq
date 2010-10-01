Require Export Reals.
Require Export ZArith.

Section Rmissing.

Theorem Rle_0_minus :
  forall x y, (x <= y)%R -> (0 <= y - x)%R.
Proof.
intros.
apply Rge_le.
apply Rge_minus.
now apply Rle_ge.
Qed.

Theorem Rabs_eq_Rabs :
  forall x y : R,
  Rabs x = Rabs y -> x = y \/ x = Ropp y.
Proof.
intros x y H.
unfold Rabs in H.
destruct (Rcase_abs x) as [_|_].
assert (H' := f_equal Ropp H).
rewrite Ropp_involutive in H'.
rewrite H'.
destruct (Rcase_abs y) as [_|_].
left.
apply Ropp_involutive.
now right.
rewrite H.
now destruct (Rcase_abs y) as [_|_] ; [right|left].
Qed.


Theorem Rabs_Rminus_pos:
  forall x y : R,
  (0 <= y)%R -> (y <= 2*x)%R ->
  (Rabs (x-y) <= x)%R.
intros x y Hx Hy.
unfold Rabs; case (Rcase_abs (x - y)); intros H.
apply Rplus_le_reg_l with x; ring_simplify; assumption.
apply Rplus_le_reg_l with (-x)%R; ring_simplify.
auto with real.
Qed.


Theorem Rplus_le_reg_r :
  forall r r1 r2 : R,
  (r1 + r <= r2 + r)%R -> (r1 <= r2)%R.
Proof.
intros.
apply Rplus_le_reg_l with r.
now rewrite 2!(Rplus_comm r).
Qed.

Theorem Rmult_lt_reg_r :
  forall r r1 r2 : R, (0 < r)%R ->
  (r1 * r < r2 * r)%R -> (r1 < r2)%R.
Proof.
intros.
apply Rmult_lt_reg_l with r.
exact H.
now rewrite 2!(Rmult_comm r).
Qed.

Theorem Rmult_le_reg_r :
  forall r r1 r2 : R, (0 < r)%R ->
  (r1 * r <= r2 * r)%R -> (r1 <= r2)%R.
Proof.
intros.
apply Rmult_le_reg_l with r.
exact H.
now rewrite 2!(Rmult_comm r).
Qed.

Theorem Rmult_eq_reg_r :
  forall r r1 r2 : R, (r1 * r)%R = (r2 * r)%R ->
  r <> 0%R -> r1 = r2.
Proof.
intros r r1 r2 H1 H2.
apply Rmult_eq_reg_l with r.
now rewrite 2!(Rmult_comm r).
exact H2.
Qed.

Theorem Rmult_minus_distr_r :
  forall r r1 r2 : R,
  ((r1 - r2) * r = r1 * r - r2 * r)%R.
Proof.
intros r r1 r2.
rewrite <- 3!(Rmult_comm r).
apply Rmult_minus_distr_l.
Qed.

Theorem Rmult_min_distr_r :
  forall r r1 r2 : R,
  (0 <= r)%R ->
  (Rmin r1 r2 * r)%R = Rmin (r1 * r) (r2 * r).
Proof.
intros r r1 r2 [Hr|Hr].
unfold Rmin.
destruct (Rle_dec r1 r2) as [H1|H1] ;
  destruct (Rle_dec (r1 * r) (r2 * r)) as [H2|H2] ;
  try easy.
apply (f_equal (fun x => Rmult x r)).
apply Rle_antisym.
exact H1.
apply Rmult_le_reg_r with (1 := Hr).
apply Rlt_le.
now apply Rnot_le_lt.
apply Rle_antisym.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Rlt_le.
now apply Rnot_le_lt.
exact H2.
rewrite <- Hr.
rewrite 3!Rmult_0_r.
unfold Rmin.
destruct (Rle_dec 0 0) as [H0|H0].
easy.
elim H0.
apply Rle_refl.
Qed.

Theorem Rmult_min_distr_l :
  forall r r1 r2 : R,
  (0 <= r)%R ->
  (r * Rmin r1 r2)%R = Rmin (r * r1) (r * r2).
Proof.
intros r r1 r2 Hr.
rewrite 3!(Rmult_comm r).
now apply Rmult_min_distr_r.
Qed.

Theorem exp_increasing_weak :
  forall x y : R,
  (x <= y)%R -> (exp x <= exp y)%R.
Proof.
intros x y [H|H].
apply Rlt_le.
now apply exp_increasing.
rewrite H.
apply Rle_refl.
Qed.

Theorem Rinv_lt :
  forall x y,
  (0 < x)%R -> (x < y)%R -> (/y < /x)%R.
Proof.
intros x y Hx Hxy.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
exact Hx.
now apply Rlt_trans with x.
exact Hxy.
Qed.

Theorem Rinv_le :
  forall x y,
  (0 < x)%R -> (x <= y)%R -> (/y <= /x)%R.
Proof.
intros x y Hx Hxy.
apply Rle_Rinv.
exact Hx.
now apply Rlt_le_trans with x.
exact Hxy.
Qed.

Theorem sqrt_ge_0 :
  forall x : R,
  (0 <= sqrt x)%R.
Proof.
intros x.
unfold sqrt.
destruct (Rcase_abs x) as [_|H].
apply Rle_refl.
apply Rsqrt_positivity.
Qed.

Theorem Rabs_le :
  forall x y,
  (-y <= x <= y)%R -> (Rabs x <= y)%R.
Proof.
intros x y (Hyx,Hxy).
unfold Rabs.
case Rcase_abs ; intros Hx.
apply Ropp_le_cancel.
now rewrite Ropp_involutive.
exact Hxy.
Qed.

Theorem Rabs_le_inv :
  forall x y,
  (Rabs x <= y)%R -> (-y <= x <= y)%R.
Proof.
intros x y Hxy.
split.
apply Rle_trans with (- Rabs x)%R.
now apply Ropp_le_contravar.
apply Ropp_le_cancel.
rewrite Ropp_involutive, <- Rabs_Ropp.
apply RRle_abs.
apply Rle_trans with (2 := Hxy).
apply RRle_abs.
Qed.

Theorem Rabs_ge :
  forall x y,
  (y <= -x \/ x <= y)%R -> (x <= Rabs y)%R.
Proof.
intros x y [Hyx|Hxy].
apply Rle_trans with (-y)%R.
apply Ropp_le_cancel.
now rewrite Ropp_involutive.
rewrite <- Rabs_Ropp.
apply RRle_abs.
apply Rle_trans with (1 := Hxy).
apply RRle_abs.
Qed.

Theorem Rabs_ge_inv :
  forall x y,
  (x <= Rabs y)%R -> (y <= -x \/ x <= y)%R.
Proof.
intros x y.
unfold Rabs.
case Rcase_abs ; intros Hy Hxy.
left.
apply Ropp_le_cancel.
now rewrite Ropp_involutive.
now right.
Qed.

Theorem Rabs_lt :
  forall x y,
  (-y < x < y)%R -> (Rabs x < y)%R.
Proof.
intros x y (Hyx,Hxy).
now apply Rabs_def1.
Qed.

Theorem Rabs_lt_inv :
  forall x y,
  (Rabs x < y)%R -> (-y < x < y)%R.
Proof.
intros x y H.
now split ; eapply Rabs_def2.
Qed.

Theorem Rabs_gt :
  forall x y,
  (y < -x \/ x < y)%R -> (x < Rabs y)%R.
Proof.
intros x y [Hyx|Hxy].
rewrite <- Rabs_Ropp.
apply Rlt_le_trans with (Ropp y).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
apply RRle_abs.
apply Rlt_le_trans with (1 := Hxy).
apply RRle_abs.
Qed.

Theorem Rabs_gt_inv :
  forall x y,
  (x < Rabs y)%R -> (y < -x \/ x < y)%R.
Proof.
intros x y.
unfold Rabs.
case Rcase_abs ; intros Hy Hxy.
left.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
now right.
Qed.

End Rmissing.

Section Zmissing.

Theorem Zopp_le_cancel :
  forall x y : Z,
  (-y <= -x)%Z -> Zle x y.
Proof.
intros x y Hxy.
apply Zplus_le_reg_r with (-x - y)%Z.
now ring_simplify.
Qed.

Theorem Zmin_left :
  forall x y : Z,
  (x <= y)%Z -> Zmin x y = x.
Proof.
intros x y.
generalize (Zmin_spec x y).
omega.
Qed.

Theorem Zmin_right :
  forall x y : Z,
  (y <= x)%Z -> Zmin x y = y.
Proof.
intros x y.
generalize (Zmin_spec x y).
omega.
Qed.

End Zmissing.

Section Z2R.

Fixpoint P2R (p : positive) :=
  match p with
  | xH => 1%R
  | xO xH => 2%R
  | xO t => (2 * P2R t)%R
  | xI xH => 3%R
  | xI t => (1 + 2 * P2R t)%R
  end.

Definition Z2R n :=
  match n with
  | Zpos p => P2R p
  | Zneg p => Ropp (P2R p)
  | Z0 => R0
  end.

Theorem P2R_INR :
  forall n, P2R n = INR (nat_of_P n).
Proof.
induction n ; simpl ; try (
  rewrite IHn ;
  rewrite <- (mult_INR 2) ;
  rewrite <- (nat_of_P_mult_morphism 2) ;
  change (2 * n)%positive with (xO n)).
(* xI *)
rewrite (Rplus_comm 1).
change (nat_of_P (xO n)) with (Pmult_nat n 2).
case n ; intros ; simpl ; try apply refl_equal.
case (Pmult_nat p 4) ; intros ; try apply refl_equal.
rewrite Rplus_0_l.
apply refl_equal.
apply Rplus_comm.
(* xO *)
case n ; intros ; apply refl_equal.
(* xH *)
apply refl_equal.
Qed.

Theorem Z2R_IZR :
  forall n, Z2R n = IZR n.
Proof.
intro.
case n ; intros ; simpl.
apply refl_equal.
apply P2R_INR.
apply Ropp_eq_compat.
apply P2R_INR.
Qed.

Theorem Z2R_opp :
  forall n, Z2R (-n) = (- Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply Ropp_Ropp_IZR.
Qed.

Theorem Z2R_plus :
  forall m n, (Z2R (m + n) = Z2R m + Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply plus_IZR.
Qed.

Theorem minus_IZR :
  forall n m : Z,
  IZR (n - m) = (IZR n - IZR m)%R.
Proof.
intros.
unfold Zminus.
rewrite plus_IZR.
rewrite Ropp_Ropp_IZR.
apply refl_equal.
Qed.

Theorem Z2R_minus :
  forall m n, (Z2R (m - n) = Z2R m - Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply minus_IZR.
Qed.

Theorem Z2R_mult :
  forall m n, (Z2R (m * n) = Z2R m * Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply mult_IZR.
Qed.

Theorem le_Z2R :
  forall m n, (Z2R m <= Z2R n)%R -> (m <= n)%Z.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply le_IZR.
Qed.

Theorem Z2R_le :
  forall m n, (m <= n)%Z -> (Z2R m <= Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_le.
Qed.

Theorem lt_Z2R :
  forall m n, (Z2R m < Z2R n)%R -> (m < n)%Z.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply lt_IZR.
Qed.

Theorem Z2R_lt :
  forall m n, (m < n)%Z -> (Z2R m < Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_lt.
Qed.

Theorem Z2R_le_lt :
  forall m n p, (m <= n < p)%Z -> (Z2R m <= Z2R n < Z2R p)%R.
Proof.
intros m n p (H1, H2).
split.
now apply Z2R_le.
now apply Z2R_lt.
Qed.

Theorem le_lt_Z2R :
  forall m n p, (Z2R m <= Z2R n < Z2R p)%R -> (m <= n < p)%Z.
Proof.
intros m n p (H1, H2).
split.
now apply le_Z2R.
now apply lt_Z2R.
Qed.

Theorem eq_Z2R :
  forall m n, (Z2R m = Z2R n)%R -> (m = n)%Z.
Proof.
intros m n H.
apply eq_IZR.
now rewrite <- 2!Z2R_IZR.
Qed.

Theorem neq_Z2R :
  forall m n, (Z2R m <> Z2R n)%R -> (m <> n)%Z.
Proof.
intros m n H H'.
apply H.
now apply f_equal.
Qed.

Theorem Z2R_neq :
  forall m n, (m <> n)%Z -> (Z2R m <> Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_neq.
Qed.

Theorem Z2R_abs :
  forall z, Z2R (Zabs z) = Rabs (Z2R z).
Proof.
intros.
repeat rewrite Z2R_IZR.
now rewrite Rabs_Zabs.
Qed.

End Z2R.

Section Zcompare.

Inductive Zeq_bool_prop (x y : Z) : bool -> Prop :=
  | Zeq_bool_true : x = y -> Zeq_bool_prop x y true
  | Zeq_bool_false : x <> y -> Zeq_bool_prop x y false.

Theorem Zeq_bool_spec :
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
  | Zcompare_Lt_ : (x < y)%Z -> Zcompare_prop x y Lt
  | Zcompare_Eq_ : x = y -> Zcompare_prop x y Eq
  | Zcompare_Gt_ : (y < x)%Z -> Zcompare_prop x y Gt.

Theorem Zcompare_spec :
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

Theorem Zcompare_Lt :
  forall x y,
  (x < y)%Z -> Zcompare x y = Lt.
Proof.
easy.
Qed.

Theorem Zcompare_Eq :
  forall x y,
  (x = y)%Z -> Zcompare x y = Eq.
Proof.
intros x y.
apply <- Zcompare_Eq_iff_eq.
Qed.

Theorem Zcompare_Gt :
  forall x y,
  (y < x)%Z -> Zcompare x y = Gt.
Proof.
intros x y.
apply Zlt_gt.
Qed.

End Zcompare.

Section Rcompare.

Definition Rcompare x y :=
  match total_order_T x y with
  | inleft (left _) => Lt
  | inleft (right _) => Eq
  | inright _ => Gt
  end.

Inductive Rcompare_prop (x y : R) : comparison -> Prop :=
  | Rcompare_Lt_ : (x < y)%R -> Rcompare_prop x y Lt
  | Rcompare_Eq_ : x = y -> Rcompare_prop x y Eq
  | Rcompare_Gt_ : (y < x)%R -> Rcompare_prop x y Gt.

Theorem Rcompare_spec :
  forall x y, Rcompare_prop x y (Rcompare x y).
Proof.
intros x y.
unfold Rcompare.
now destruct (total_order_T x y) as [[H|H]|H] ; constructor.
Qed.

Global Opaque Rcompare.

Theorem Rcompare_Lt :
  forall x y,
  (x < y)%R -> Rcompare x y = Lt.
Proof.
intros x y H.
case Rcompare_spec ; intro H'.
easy.
rewrite H' in H.
elim (Rlt_irrefl _ H).
elim (Rlt_irrefl x).
now apply Rlt_trans with y.
Qed.

Theorem Rcompare_Lt_inv :
  forall x y,
  Rcompare x y = Lt -> (x < y)%R.
Proof.
intros x y.
now case Rcompare_spec.
Qed.

Theorem Rcompare_not_Lt :
  forall x y,
  (y <= x)%R -> Rcompare x y <> Lt.
Proof.
intros x y H1 H2.
apply Rle_not_lt with (1 := H1).
now apply Rcompare_Lt_inv.
Qed.

Theorem Rcompare_not_Lt_inv :
  forall x y,
  Rcompare x y <> Lt -> (y <= x)%R.
Proof.
intros x y H.
apply Rnot_lt_le.
contradict H.
now apply Rcompare_Lt.
Qed.

Theorem Rcompare_Eq :
  forall x y,
  x = y -> Rcompare x y = Eq.
Proof.
intros x y H.
rewrite H.
now case Rcompare_spec ; intro H' ; try elim (Rlt_irrefl _ H').
Qed.

Theorem Rcompare_Eq_inv :
  forall x y,
  Rcompare x y = Eq -> x = y.
Proof.
intros x y.
now case Rcompare_spec.
Qed.

Theorem Rcompare_Gt :
  forall x y,
  (y < x)%R -> Rcompare x y = Gt.
Proof.
intros x y H.
case Rcompare_spec ; intro H'.
elim (Rlt_irrefl x).
now apply Rlt_trans with y.
rewrite H' in H.
elim (Rlt_irrefl _ H).
easy.
Qed.

Theorem Rcompare_Gt_inv :
  forall x y,
  Rcompare x y = Gt -> (y < x)%R.
Proof.
intros x y.
now case Rcompare_spec.
Qed.

Theorem Rcompare_not_Gt :
  forall x y,
  (x <= y)%R -> Rcompare x y <> Gt.
Proof.
intros x y H1 H2.
apply Rle_not_lt with (1 := H1).
now apply Rcompare_Gt_inv.
Qed.

Theorem Rcompare_not_Gt_inv :
  forall x y,
  Rcompare x y <> Gt -> (x <= y)%R.
Proof.
intros x y H.
apply Rnot_lt_le.
contradict H.
now apply Rcompare_Gt.
Qed.

Theorem Rcompare_Z2R :
  forall x y, Rcompare (Z2R x) (Z2R y) = Zcompare x y.
Proof.
intros x y.
case Rcompare_spec ; intros H ; apply sym_eq.
apply Zcompare_Lt.
now apply lt_Z2R.
apply Zcompare_Eq.
now apply eq_Z2R.
apply Zcompare_Gt.
now apply lt_Z2R.
Qed.

Theorem Rcompare_sym :
  forall x y,
  Rcompare x y = CompOpp (Rcompare y x).
Proof.
intros x y.
destruct (Rcompare_spec y x) as [H|H|H].
now apply Rcompare_Gt.
now apply Rcompare_Eq.
now apply Rcompare_Lt.
Qed.

Theorem Rcompare_plus_r :
  forall z x y,
  Rcompare (x + z) (y + z) = Rcompare x y.
Proof.
intros z x y.
destruct (Rcompare_spec x y) as [H|H|H].
apply Rcompare_Lt.
now apply Rplus_lt_compat_r.
apply Rcompare_Eq.
now rewrite H.
apply Rcompare_Gt.
now apply Rplus_lt_compat_r.
Qed.

Theorem Rcompare_plus_l :
  forall z x y,
  Rcompare (z + x) (z + y) = Rcompare x y.
Proof.
intros z x y.
rewrite 2!(Rplus_comm z).
apply Rcompare_plus_r.
Qed.

Theorem Rcompare_mult_r :
  forall z x y,
  (0 < z)%R ->
  Rcompare (x * z) (y * z) = Rcompare x y.
Proof.
intros z x y Hz.
destruct (Rcompare_spec x y) as [H|H|H].
apply Rcompare_Lt.
now apply Rmult_lt_compat_r.
apply Rcompare_Eq.
now rewrite H.
apply Rcompare_Gt.
now apply Rmult_lt_compat_r.
Qed.

Theorem Rcompare_mult_l :
  forall z x y,
  (0 < z)%R ->
  Rcompare (z * x) (z * y) = Rcompare x y.
Proof.
intros z x y.
rewrite 2!(Rmult_comm z).
apply Rcompare_mult_r.
Qed.

Theorem Rcompare_middle :
  forall x d u,
  Rcompare (x - d) (u - x) = Rcompare x ((d + u) / 2).
Proof.
intros x d u.
rewrite <- (Rcompare_plus_r (- x / 2 - d / 2) x).
rewrite <- (Rcompare_mult_r (/2) (x - d)).
field_simplify (x + (- x / 2 - d / 2))%R.
now field_simplify ((d + u) / 2 + (- x / 2 - d / 2))%R.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
Qed.

Theorem Rcompare_half_l :
  forall x y, Rcompare (x / 2) y = Rcompare x (2 * y).
Proof.
intros x y.
rewrite <- (Rcompare_mult_r 2%R).
unfold Rdiv.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now rewrite Rmult_comm.
now apply (Z2R_neq 2 0).
now apply (Z2R_lt 0 2).
Qed.

Theorem Rcompare_half_r :
  forall x y, Rcompare x (y / 2) = Rcompare (2 * x) y.
Proof.
intros x y.
rewrite <- (Rcompare_mult_r 2%R).
unfold Rdiv.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now rewrite Rmult_comm.
now apply (Z2R_neq 2 0).
now apply (Z2R_lt 0 2).
Qed.

Theorem Rcompare_sqr :
  forall x y,
  (0 <= x)%R -> (0 <= y)%R ->
  Rcompare (x * x) (y * y) = Rcompare x y.
Proof.
intros x y Hx Hy.
destruct (Rcompare_spec x y) as [H|H|H].
apply Rcompare_Lt.
now apply Rsqr_incrst_1.
rewrite H.
now apply Rcompare_Eq.
apply Rcompare_Gt.
now apply Rsqr_incrst_1.
Qed.

End Rcompare.

Section Rle_bool.

Definition Rle_bool x y :=
  match Rcompare x y with
  | Gt => false
  | _ => true
  end.

Inductive Rle_bool_prop (x y : R) : bool -> Prop :=
  | Rle_bool_true_ : (x <= y)%R -> Rle_bool_prop x y true
  | Rle_bool_false_ : (y < x)%R -> Rle_bool_prop x y false.

Theorem Rle_bool_spec :
  forall x y, Rle_bool_prop x y (Rle_bool x y).
Proof.
intros x y.
unfold Rle_bool.
case Rcompare_spec ; constructor.
now apply Rlt_le.
rewrite H.
apply Rle_refl.
exact H.
Qed.

Theorem Rle_bool_true :
  forall x y,
  (x <= y)%R -> Rle_bool x y = true.
Proof.
intros x y Hxy.
case Rle_bool_spec ; intros H.
apply refl_equal.
elim (Rlt_irrefl x).
now apply Rle_lt_trans with y.
Qed.

Theorem Rle_bool_false :
  forall x y,
  (y < x)%R -> Rle_bool x y = false.
Proof.
intros x y Hxy.
case Rle_bool_spec ; intros H.
elim (Rlt_irrefl x).
now apply Rle_lt_trans with y.
apply refl_equal.
Qed.

End Rle_bool.
Section Req_bool.

Definition Req_bool x y :=
  match Rcompare x y with
  | Eq => true
  | _ => false
  end.

Inductive Req_bool_prop (x y : R) : bool -> Prop :=
  | Req_bool_true_ : (x = y)%R -> Req_bool_prop x y true
  | Req_bool_false_ : (x <> y)%R -> Req_bool_prop x y false.

Theorem Req_bool_spec :
  forall x y, Req_bool_prop x y (Req_bool x y).
Proof.
intros x y.
unfold Req_bool.
case Rcompare_spec ; constructor.
now apply Rlt_not_eq.
easy.
now apply Rgt_not_eq.
Qed.

Theorem Req_bool_true :
  forall x y,
  (x = y)%R -> Req_bool x y = true.
Proof.
intros x y Hxy.
case Req_bool_spec ; intros H.
apply refl_equal.
contradict H.
exact Hxy.
Qed.

Theorem Req_bool_false :
  forall x y,
  (x <> y)%R -> Req_bool x y = false.
Proof.
intros x y Hxy.
case Req_bool_spec ; intros H.
contradict Hxy.
exact H.
apply refl_equal.
Qed.

End Req_bool.
Section Floor_Ceil.

Definition Zfloor (x : R) := (up x - 1)%Z.

Theorem Zfloor_lb :
  forall x : R,
  (Z2R (Zfloor x) <= x)%R.
Proof.
intros x.
unfold Zfloor.
rewrite Z2R_minus.
simpl.
rewrite Z2R_IZR.
apply Rplus_le_reg_r with (1 - x)%R.
ring_simplify.
exact (proj2 (archimed x)).
Qed.

Theorem Zfloor_ub :
  forall x : R,
  (x < Z2R (Zfloor x) + 1)%R.
Proof.
intros x.
unfold Zfloor.
rewrite Z2R_minus.
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_r.
rewrite Z2R_IZR.
exact (proj1 (archimed x)).
Qed.

Theorem Zfloor_lub :
  forall n x,
  (Z2R n <= x)%R ->
  (n <= Zfloor x)%Z.
Proof.
intros n x Hnx.
apply Zlt_succ_le.
apply lt_Z2R.
apply Rle_lt_trans with (1 := Hnx).
unfold Zsucc.
rewrite Z2R_plus.
apply Zfloor_ub.
Qed.

Theorem Zfloor_imp :
  forall n x,
  (Z2R n <= x < Z2R (n + 1))%R ->
  Zfloor x = n.
Proof.
intros n x Hnx.
apply Zle_antisym.
apply Zlt_succ_le.
apply lt_Z2R.
apply Rle_lt_trans with (2 := proj2 Hnx).
apply Zfloor_lb.
now apply Zfloor_lub.
Qed.

Theorem Zfloor_Z2R :
  forall n,
  Zfloor (Z2R n) = n.
Proof.
intros n.
apply Zfloor_imp.
split.
apply Rle_refl.
apply Z2R_lt.
apply Zlt_succ.
Qed.

Theorem Zfloor_le :
  forall x y, (x <= y)%R ->
  (Zfloor x <= Zfloor y)%Z.
Proof.
intros x y Hxy.
apply Zfloor_lub.
apply Rle_trans with (2 := Hxy).
apply Zfloor_lb.
Qed.

Definition Zceil (x : R) := (- Zfloor (- x))%Z.

Theorem Zceil_ub :
  forall x : R,
  (x <= Z2R (Zceil x))%R.
Proof.
intros x.
unfold Zceil.
rewrite Z2R_opp.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Zfloor_lb.
Qed.

Theorem Zceil_glb :
  forall n x,
  (x <= Z2R n)%R ->
  (Zceil x <= n)%Z.
Proof.
intros n x Hnx.
unfold Zceil.
apply Zopp_le_cancel.
rewrite Zopp_involutive.
apply Zfloor_lub.
rewrite Z2R_opp.
now apply Ropp_le_contravar.
Qed.

Theorem Zceil_imp :
  forall n x,
  (Z2R (n - 1) < x <= Z2R n)%R ->
  Zceil x = n.
Proof.
intros n x Hnx.
unfold Zceil.
rewrite <- (Zopp_involutive n).
apply f_equal.
apply Zfloor_imp.
split.
rewrite Z2R_opp.
now apply Ropp_le_contravar.
rewrite <- (Zopp_involutive 1).
rewrite <- Zopp_plus_distr.
rewrite Z2R_opp.
now apply Ropp_lt_contravar.
Qed.

Theorem Zceil_Z2R :
  forall n,
  Zceil (Z2R n) = n.
Proof.
intros n.
unfold Zceil.
rewrite <- Z2R_opp, Zfloor_Z2R.
apply Zopp_involutive.
Qed.

Theorem Zceil_le :
  forall x y, (x <= y)%R ->
  (Zceil x <= Zceil y)%Z.
Proof.
intros x y Hxy.
apply Zceil_glb.
apply Rle_trans with (1 := Hxy).
apply Zceil_ub.
Qed.

Theorem Zceil_floor_neq :
  forall x : R,
  (Z2R (Zfloor x) <> x)%R ->
  (Zceil x = Zfloor x + 1)%Z.
Proof.
intros x Hx.
apply Zceil_imp.
split.
ring_simplify (Zfloor x + 1 - 1)%Z.
apply Rnot_le_lt.
intros H.
apply Hx.
apply Rle_antisym.
apply Zfloor_lb.
exact H.
apply Rlt_le.
rewrite Z2R_plus.
apply Zfloor_ub.
Qed.

Definition Ztrunc x := if Rlt_le_dec x 0 then Zceil x else Zfloor x.

Theorem Ztrunc_Z2R :
  forall n,
  Ztrunc (Z2R n) = n.
Proof.
intros n.
unfold Ztrunc.
destruct Rlt_le_dec as [H|H].
apply Zceil_Z2R.
apply Zfloor_Z2R.
Qed.

Theorem Ztrunc_floor :
  forall x,
  (0 <= x)%R ->
  Ztrunc x = Zfloor x.
Proof.
intros x Hx.
unfold Ztrunc.
destruct Rlt_le_dec as [H|_].
elim Rlt_irrefl with (1 := Rle_lt_trans _ _ _ Hx H).
easy.
Qed.

Theorem Ztrunc_ceil :
  forall x,
  (x <= 0)%R ->
  Ztrunc x = Zceil x.
Proof.
intros x Hx.
unfold Ztrunc.
destruct Rlt_le_dec as [_|H].
easy.
rewrite (Rle_antisym _ _ Hx H).
fold (Z2R 0).
rewrite Zceil_Z2R.
apply Zfloor_Z2R.
Qed.

Theorem Ztrunc_le : 
 forall x y, (x <= y)%R ->
  (Ztrunc x <= Ztrunc y)%Z.
Proof.
intros x y Hxy; unfold Ztrunc at 1.
destruct Rlt_le_dec as [Hx|Hx].
unfold Ztrunc; destruct Rlt_le_dec as [Hy|Hy].
now apply Zceil_le.
apply Zle_trans with 0%Z.
apply Zceil_glb.
simpl; auto with real.
apply Zfloor_lub.
now simpl.
rewrite Ztrunc_floor.
now apply Zfloor_le.
now apply Rle_trans with (1:=Hx). 
Qed.


Theorem Ztrunc_opp :
  forall x,
  Ztrunc (- x) = Zopp (Ztrunc x).
Proof.
intros x.
destruct (Rlt_le_dec x 0) as [H|H].
rewrite Ztrunc_floor.
rewrite Ztrunc_ceil.
apply sym_eq.
apply Zopp_involutive.
now apply Rlt_le.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
rewrite Ztrunc_ceil.
unfold Zceil.
rewrite Ropp_involutive.
now rewrite Ztrunc_floor.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
Qed.

Theorem Ztrunc_abs :
  forall x,
  Ztrunc (Rabs x) = Zabs (Ztrunc x).
Proof.
intros x.
rewrite Ztrunc_floor. 2: apply Rabs_pos.
unfold Ztrunc.
destruct Rlt_le_dec as [H|H].
rewrite Rabs_left with (1 := H).
rewrite Zabs_non_eq.
apply sym_eq.
apply Zopp_involutive.
apply Zceil_glb.
now apply Rlt_le.
rewrite Rabs_pos_eq with (1 := H).
apply sym_eq.
apply Zabs_eq.
now apply Zfloor_lub.
Qed.

Theorem Ztrunc_lub :
  forall n x,
  (Z2R n <= Rabs x)%R ->
  (n <= Zabs (Ztrunc x))%Z.
Proof.
intros n x H.
rewrite <- Ztrunc_abs.
rewrite Ztrunc_floor. 2: apply Rabs_pos.
now apply Zfloor_lub.
Qed.

End Floor_Ceil.

Section Even_Odd.

Definition Zeven (n : Z) :=
  match n with
  | Zpos (xO _) => true
  | Zneg (xO _) => true
  | Z0 => true
  | _ => false
  end.

Theorem Zeven_mult :
  forall x y, Zeven (x * y) = orb (Zeven x) (Zeven y).
Proof.
now intros [|[xp|xp|]|[xp|xp|]] [|[yp|yp|]|[yp|yp|]].
Qed.

Theorem Zeven_opp :
  forall x, Zeven (- x) = Zeven x.
Proof.
now intros [|[n|n|]|[n|n|]].
Qed.

Theorem Zeven_ex :
  forall x, exists p, x = (2 * p + if Zeven x then 0 else 1)%Z.
Proof.
intros [|[n|n|]|[n|n|]].
now exists Z0.
now exists (Zpos n).
now exists (Zpos n).
now exists Z0.
exists (Zneg n - 1)%Z.
change (2 * Zneg n - 1 = 2 * (Zneg n - 1) + 1)%Z.
ring.
now exists (Zneg n).
now exists (-1)%Z.
Qed.

Theorem Zeven_2xp1 :
  forall n, Zeven (2 * n + 1) = false.
Proof.
intros n.
destruct (Zeven_ex (2 * n + 1)) as (p, Hp).
revert Hp.
case (Zeven (2 * n + 1)) ; try easy.
intros H.
apply False_ind.
omega.
Qed.

Theorem Zeven_plus :
  forall x y, Zeven (x + y) = Bool.eqb (Zeven x) (Zeven y).
Proof.
intros x y.
destruct (Zeven_ex x) as (px, Hx).
rewrite Hx at 1.
destruct (Zeven_ex y) as (py, Hy).
rewrite Hy at 1.
replace (2 * px + (if Zeven x then 0 else 1) + (2 * py + (if Zeven y then 0 else 1)))%Z
  with (2 * (px + py) + ((if Zeven x then 0 else 1) + (if Zeven y then 0 else 1)))%Z by ring.
case (Zeven x) ; case (Zeven y).
rewrite Zplus_0_r.
now rewrite Zeven_mult.
apply Zeven_2xp1.
apply Zeven_2xp1.
replace (2 * (px + py) + (1 + 1))%Z with (2 * (px + py + 1))%Z by ring.
now rewrite Zeven_mult.
Qed.

End Even_Odd.

Section Proof_Irrelevance.

Scheme eq_dep_elim := Induction for eq Sort Type.

Definition eqbool_dep P (h1 : P true) b :=
  match b return P b -> Prop with
  | true => fun (h2 : P true) => h1 = h2
  | false => fun (h2 : P false) => False
  end.

Lemma eqbool_irrelevance : forall (b : bool) (h1 h2 : b = true), h1 = h2.
Proof.
assert (forall (h : true = true), refl_equal true = h).
apply (eq_dep_elim bool true (eqbool_dep _ _) (refl_equal _)).
intros b.
case b.
intros h1 h2.
now rewrite <- (H h1).
intros h.
discriminate h.
Qed.

End Proof_Irrelevance.

Section pow.

Record radix := { radix_val :> Z ; radix_prop : Zle_bool 2 radix_val = true }.

Theorem radix_val_inj :
  forall r1 r2, radix_val r1 = radix_val r2 -> r1 = r2.
Proof.
intros (r1, H1) (r2, H2) H.
simpl in H.
revert H1.
rewrite H.
intros H1.
apply f_equal.
apply eqbool_irrelevance.
Qed.

Variable r : radix.

Theorem radix_gt_1 : (1 < r)%Z.
Proof.
destruct r as (v, Hr). simpl.
apply Zlt_le_trans with 2%Z.
easy.
now apply Zle_bool_imp_le.
Qed.

Theorem radix_pos : (0 < Z2R r)%R.
Proof.
destruct r as (v, Hr). simpl.
apply (Z2R_lt 0).
apply Zlt_le_trans with 2%Z.
easy.
now apply Zle_bool_imp_le.
Qed.

Definition bpow e :=
  match e with
  | Zpos p => Z2R (Zpower_pos r p)
  | Zneg p => Rinv (Z2R (Zpower_pos r p))
  | Z0 => R1
  end.

Theorem Z2R_Zpower_pos :
  forall n m,
  Z2R (Zpower_pos n m) = powerRZ (Z2R n) (Zpos m).
Proof.
intros.
rewrite Zpower_pos_nat.
simpl.
induction (nat_of_P m).
apply refl_equal.
unfold Zpower_nat.
simpl.
rewrite Z2R_mult.
apply Rmult_eq_compat_l.
exact IHn0.
Qed.

Theorem bpow_powerRZ :
  forall e,
  bpow e = powerRZ (Z2R r) e.
Proof.
destruct e ; unfold bpow.
reflexivity.
now rewrite Z2R_Zpower_pos.
now rewrite Z2R_Zpower_pos.
Qed.

Theorem  bpow_ge_0 :
  forall e : Z, (0 <= bpow e)%R.
Proof.
intros.
rewrite bpow_powerRZ.
apply powerRZ_le.
apply radix_pos.
Qed.

Theorem bpow_gt_0 :
  forall e : Z, (0 < bpow e)%R.
Proof.
intros.
rewrite bpow_powerRZ.
apply powerRZ_lt.
apply radix_pos.
Qed.

Theorem bpow_plus :
  forall e1 e2 : Z, (bpow (e1 + e2) = bpow e1 * bpow e2)%R.
Proof.
intros.
repeat rewrite bpow_powerRZ.
apply powerRZ_add.
apply Rgt_not_eq.
apply radix_pos.
Qed.

Theorem bpow_1 :
  bpow 1 = Z2R r.
Proof.
unfold bpow, Zpower_pos, iter_pos.
now rewrite Zmult_1_r.
Qed.

Theorem bpow_plus1 :
  forall e : Z, (bpow (e + 1) = Z2R r * bpow e)%R.
Proof.
intros.
rewrite <- bpow_1.
rewrite <- bpow_plus.
now rewrite Zplus_comm.
Qed.

Theorem bpow_opp :
  forall e : Z, (bpow (-e) = /bpow e)%R.
Proof.
intros e; destruct e.
simpl; now rewrite Rinv_1.
now replace (-Zpos p)%Z with (Zneg p) by reflexivity.
replace (-Zneg p)%Z with (Zpos p) by reflexivity.
simpl; rewrite Rinv_involutive; trivial.
generalize (bpow_gt_0 (Zpos p)).
simpl; auto with real.
Qed.

Theorem Z2R_Zpower_nat :
  forall e : nat,
  Z2R (Zpower_nat r e) = bpow (Z_of_nat e).
Proof.
intros [|e].
split.
rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ.
rewrite <- Zpower_pos_nat.
now rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
Qed.

Theorem Z2R_Zpower :
  forall e : Z,
  (0 <= e)%Z ->
  Z2R (Zpower r e) = bpow e.
Proof.
intros [|e|e] H.
split.
split.
now elim H.
Qed.

Theorem bpow_lt_aux :
  forall e1 e2 : Z,
  (e1 < e2)%Z -> (bpow e1 < bpow e2)%R.
Proof.
intros e1 e2 H.
replace e2 with (e1 + (e2 - e1))%Z by ring.
rewrite <- (Rmult_1_r (bpow e1)).
rewrite bpow_plus.
apply Rmult_lt_compat_l.
apply bpow_gt_0.
assert (0 < e2 - e1)%Z by omega.
destruct (e2 - e1)%Z ; try discriminate H0.
clear.
unfold bpow.
apply (Z2R_lt 1).
rewrite Zpower_pos_nat.
case_eq (nat_of_P p).
intros H.
elim (lt_irrefl 0).
pattern O at 2 ; rewrite <- H.
apply lt_O_nat_of_P.
intros n _.
assert (1 < Zpower_nat r 1)%Z.
unfold Zpower_nat, iter_nat.
rewrite Zmult_1_r.
apply radix_gt_1.
induction n.
exact H.
change (S (S n)) with (1 + (S n))%nat.
rewrite Zpower_nat_is_exp.
change 1%Z with (1 * 1)%Z.
apply Zmult_lt_compat.
now split.
now split.
Qed.

Theorem bpow_lt :
  forall e1 e2 : Z,
  (e1 < e2)%Z <-> (bpow e1 < bpow e2)%R.
Proof.
intros e1 e2.
split.
apply bpow_lt_aux.
intros H.
apply Zgt_lt.
apply Znot_le_gt.
intros H'.
apply Rlt_not_le with (1 := H).
destruct (Zle_lt_or_eq _ _ H').
apply Rlt_le.
now apply bpow_lt_aux.
apply Req_le.
now apply f_equal.
Qed.

Theorem bpow_le :
  forall e1 e2 : Z,
  (e1 <= e2)%Z <-> (bpow e1 <= bpow e2)%R.
Proof.
intros e1 e2.
split.
intros H.
apply Rnot_lt_le.
intros H'.
apply Zle_not_gt with (1 := H).
apply Zlt_gt.
now apply <- bpow_lt.
intros H.
apply Znot_gt_le.
intros H'.
apply Rle_not_lt with (1 := H).
apply -> bpow_lt.
now apply Zgt_lt.
Qed.

Theorem bpow_eq :
  forall e1 e2 : Z,
  bpow e1 = bpow e2 -> e1 = e2.
Proof.
intros.
apply Zle_antisym.
apply <- bpow_le.
now apply Req_le.
apply <- bpow_le.
now apply Req_le.
Qed.

Theorem bpow_exp :
  forall e : Z,
  bpow e = exp (Z2R e * ln (Z2R r)).
Proof.
(* positive case *)
assert (forall e, bpow (Zpos e) = exp (Z2R (Zpos e) * ln (Z2R r))).
intros e.
unfold bpow.
rewrite Zpower_pos_nat.
unfold Z2R at 2.
rewrite P2R_INR.
induction (nat_of_P e).
rewrite Rmult_0_l.
unfold Zpower_nat, iter_nat.
now rewrite exp_0.
change (S n) with (1 + n)%nat.
rewrite plus_INR.
rewrite Zpower_nat_is_exp.
rewrite Rmult_plus_distr_r.
rewrite exp_plus.
rewrite Rmult_1_l.
rewrite exp_ln.
rewrite <- IHn.
rewrite <- Z2R_mult.
apply f_equal.
unfold Zpower_nat at 1, iter_nat.
now rewrite Zmult_1_r.
apply radix_pos.
(* general case *)
intros [|e|e].
rewrite Rmult_0_l.
now rewrite exp_0.
apply H.
unfold bpow.
change (Z2R (Zpower_pos r e)) with (bpow (Zpos e)).
rewrite H.
rewrite <- exp_Ropp.
rewrite <- Ropp_mult_distr_l_reverse.
now rewrite <- Z2R_opp.
Qed.

Record ln_beta_prop x := {
  ln_beta_val :> Z ;
   _ : (x <> 0)%R -> (bpow (ln_beta_val - 1)%Z <= Rabs x < bpow ln_beta_val)%R
}.

Definition ln_beta :
  forall x : R, ln_beta_prop x.
Proof.
intros x.
set (fact := ln (Z2R r)).
(* . *)
assert (0 < fact)%R.
apply exp_lt_inv.
rewrite exp_0.
unfold fact.
rewrite exp_ln.
apply (Z2R_lt 1).
apply radix_gt_1.
apply radix_pos.
(* . *)
exists (Zfloor (ln (Rabs x) / fact) + 1)%Z.
intros Hx'.
generalize (Rabs_pos_lt _ Hx'). clear Hx'.
generalize (Rabs x). clear x.
intros x Hx.
rewrite 2!bpow_exp.
fold fact.
pattern x at 2 3 ; replace x with (exp (ln x * / fact * fact)).
split.
rewrite Z2R_minus.
apply exp_increasing_weak.
apply Rmult_le_compat_r.
now apply Rlt_le.
unfold Rminus.
rewrite Z2R_plus.
rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
apply Zfloor_lb.
apply exp_increasing.
apply Rmult_lt_compat_r.
exact H.
rewrite Z2R_plus.
apply Zfloor_ub.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
now apply exp_ln.
now apply Rgt_not_eq.
Qed.

Theorem bpow_lt_bpow :
  forall e1 e2,
  (bpow (e1 - 1) < bpow e2)%R ->
  (e1 <= e2)%Z.
Proof.
intros e1 e2 He.
rewrite (Zsucc_pred e1).
apply Zlt_le_succ.
now apply <- bpow_lt.
Qed.

Theorem bpow_unique :
  forall x e1 e2,
  (bpow (e1 - 1) <= x < bpow e1)%R ->
  (bpow (e2 - 1) <= x < bpow e2)%R ->
  e1 = e2.
Proof.
intros x e1 e2 (H1a,H1b) (H2a,H2b).
apply Zle_antisym ;
  apply bpow_lt_bpow ;
  apply Rle_lt_trans with x ;
  assumption.
Qed.

Theorem ln_beta_unique :
  forall (x : R) (e : Z),
  (bpow (e - 1) <= Rabs x < bpow e)%R ->
  ln_beta x = e :> Z.
Proof.
intros x e1 He.
destruct (Req_dec x 0) as [Hx|Hx].
elim Rle_not_lt with (1 := proj1 He).
rewrite Hx, Rabs_R0.
apply bpow_gt_0.
destruct (ln_beta x) as (e2, Hx2).
simpl.
apply bpow_unique with (2 := He).
now apply Hx2.
Qed.

Theorem ln_beta_opp :
  forall x,
  ln_beta (-x) = ln_beta x :> Z.
Proof.
intros x.
destruct (Req_dec x 0) as [Hx|Hx].
now rewrite Hx, Ropp_0.
destruct (ln_beta x) as (e, He).
simpl.
specialize (He Hx).
apply ln_beta_unique.
now rewrite Rabs_Ropp.
Qed.

Theorem ln_beta_abs :
  forall x,
  ln_beta (Rabs x) = ln_beta x :> Z.
Proof.
intros x.
unfold Rabs.
case Rcase_abs ; intros _.
apply ln_beta_opp.
apply refl_equal.
Qed.

Theorem ln_beta_monotone_abs :
  forall x y,
  (x <> 0)%R -> (Rabs x <= Rabs y)%R ->
  (ln_beta x <= ln_beta y)%Z.
Proof.
intros x y H0x Hxy.
destruct (ln_beta x) as (ex, Hx).
destruct (ln_beta y) as (ey, Hy).
simpl.
apply bpow_lt_bpow.
specialize (Hx H0x).
apply Rle_lt_trans with (1 := proj1 Hx).
apply Rle_lt_trans with (1 := Hxy).
apply Hy.
intros Hy'.
apply Rlt_not_le with (1 := Rabs_pos_lt _ H0x).
apply Rle_trans with (1 := Hxy).
rewrite Hy', Rabs_R0.
apply Rle_refl.
Qed.

Theorem ln_beta_monotone :
  forall x y,
  (0 < x)%R -> (x <= y)%R ->
  (ln_beta x <= ln_beta y)%Z.
Proof.
intros x y H0x Hxy.
apply ln_beta_monotone_abs.
now apply Rgt_not_eq.
rewrite 2!Rabs_pos_eq.
exact Hxy.
apply Rle_trans with (2 := Hxy).
now apply Rlt_le.
now apply Rlt_le.
Qed.

Theorem ln_beta_bpow :
  forall e, (ln_beta (bpow e) = e + 1 :> Z)%Z.
Proof.
intros e.
apply ln_beta_unique.
rewrite Rabs_right.
replace (e + 1 - 1)%Z with e by ring.
split.
apply Rle_refl.
apply -> bpow_lt.
apply Zlt_succ.
apply Rle_ge.
apply bpow_ge_0.
Qed.

Theorem Zpower_pos_gt_0 :
  forall b p, (0 < b)%Z ->
  (0 < Zpower_pos b p)%Z.
Proof.
intros b p Hb.
apply lt_Z2R.
rewrite Z2R_Zpower_pos.
apply powerRZ_lt.
now apply (Z2R_lt 0).
Qed.

Theorem Zpower_gt_1 :
  forall p,
  (0 < p)%Z ->
  (1 < Zpower r p)%Z.
Proof.
intros.
apply lt_Z2R.
rewrite Z2R_Zpower.
now apply -> (bpow_lt 0).
now apply Zlt_le_weak.
Qed.

Theorem Zpower_gt_0 :
  forall p,
  (0 < p)%Z ->
  (0 < Zpower r p)%Z.
Proof.
intros.
apply Zlt_trans with 1%Z.
easy.
now apply Zpower_gt_1.
Qed.

Theorem Zpower_Zpower_nat :
  forall b e, (0 <= e)%Z ->
  Zpower b e = Zpower_nat b (Zabs_nat e).
Proof.
intros b [|e|e] He.
apply refl_equal.
apply Zpower_pos_nat.
elim He.
apply refl_equal.
Qed.

Theorem Zeven_Zpower :
  forall b e, (0 < e)%Z ->
  Zeven (Zpower b e) = Zeven b.
Proof.
intros b e He.
case_eq (Zeven b) ; intros Hb.
(* b even *)
replace e with (e - 1 + 1)%Z by ring.
rewrite Zpower_exp.
rewrite Zeven_mult.
replace (Zeven (b ^ 1)) with true.
apply Bool.orb_true_r.
unfold Zpower, Zpower_pos, iter_pos.
now rewrite Zmult_1_r.
omega.
discriminate.
(* b odd *)
rewrite Zpower_Zpower_nat.
induction (Zabs_nat e).
easy.
unfold Zpower_nat. simpl.
rewrite Zeven_mult.
now rewrite Hb.
now apply Zlt_le_weak.
Qed.

Theorem Zeven_Zpower_odd :
  forall b e, (0 <= e)%Z -> Zeven b = false ->
  Zeven (Zpower b e) = false.
Proof.
intros b e He Hb.
destruct (Z_le_lt_eq_dec _ _ He) as [He'|He'].
rewrite <- Hb.
now apply Zeven_Zpower.
now rewrite <- He'.
Qed.

End pow.

Section Bool.

Theorem eqb_sym :
  forall x y, Bool.eqb x y = Bool.eqb y x.
Proof.
now intros [|] [|].
Qed.

Theorem eqb_false :
  forall x y, x = negb y -> Bool.eqb x y = false.
Proof.
now intros [|] [|].
Qed.

Theorem eqb_true :
  forall x y, x = y -> Bool.eqb x y = true.
Proof.
now intros [|] [|].
Qed.

End Bool.

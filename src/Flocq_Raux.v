Require Export Reals.
Require Export ZArith.

Lemma Rle_0_minus :
  forall x y, (x <= y)%R -> (0 <= y - x)%R.
Proof.
intros.
apply Rge_le.
apply Rge_minus.
now apply Rle_ge.
Qed.

Lemma Rabs_eq_Rabs :
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

Lemma P2R_INR :
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

Lemma Z2R_IZR :
  forall n, Z2R n = IZR n.
Proof.
intro.
case n ; intros ; simpl.
apply refl_equal.
apply P2R_INR.
apply Ropp_eq_compat.
apply P2R_INR.
Qed.

Lemma plus_Z2R :
  forall m n, (Z2R (m + n) = Z2R m + Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply plus_IZR.
Qed.

Lemma minus_IZR :
  forall n m : Z,
  IZR (n - m) = (IZR n - IZR m)%R.
Proof.
intros.
unfold Zminus.
rewrite plus_IZR.
rewrite Ropp_Ropp_IZR.
apply refl_equal.
Qed.


Lemma minus_Z2R :
  forall m n, (Z2R (m - n) = Z2R m - Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply minus_IZR.
Qed.

Lemma mult_Z2R :
  forall m n, (Z2R (m * n) = Z2R m * Z2R n)%R.
Proof.
intros.
repeat rewrite Z2R_IZR.
apply mult_IZR.
Qed.

Lemma le_Z2R :
  forall m n, (Z2R m <= Z2R n)%R -> (m <= n)%Z.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply le_IZR.
Qed.

Lemma Z2R_le :
  forall m n, (m <= n)%Z -> (Z2R m <= Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_le.
Qed.

Lemma lt_Z2R :
  forall m n, (Z2R m < Z2R n)%R -> (m < n)%Z.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply lt_IZR.
Qed.

Lemma Z2R_lt :
  forall m n, (m < n)%Z -> (Z2R m < Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_lt.
Qed.


Lemma Z2R_neq :
forall m n, (m <> n)%Z -> (Z2R m <> Z2R n)%R.
Proof.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_neq.
Qed.

End Z2R.


Section pow.

Record radix :=  { radix_val :Z ; radix_prop :  (2 <= radix_val )%Z }.

Variable r: radix.

Definition epow e :=
  match e with
  | Zpos p => Z2R (Zpower_pos (radix_val r) p)
  | Zneg p => Rinv (Z2R (Zpower_pos (radix_val r) p))
  | Z0 => R1
  end.


Lemma Zpower_pos_powerRZ :
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
rewrite mult_Z2R.
apply Rmult_eq_compat_l.
exact IHn0.
Qed.

Theorem epow_powerRZ :
   forall e,
  epow e = powerRZ (Z2R (radix_val r)) e.
Proof.
destruct e ; unfold epow.
reflexivity.
now rewrite Zpower_pos_powerRZ.
now rewrite Zpower_pos_powerRZ.
Qed.


Theorem  epow_ge_0 :
  forall e : Z, (0 <= epow e)%R.
Proof.
intros.
rewrite epow_powerRZ.
apply powerRZ_le.
change R0 with (Z2R 0).
apply Z2R_lt.
destruct r; simpl; auto with zarith.
Qed.

Lemma epow_gt_0 :
  forall e : Z, (0 < epow e)%R.
Proof.
intros.
rewrite epow_powerRZ.
apply powerRZ_lt.
change R0 with (Z2R 0).
apply Z2R_lt.
destruct r; simpl; auto with zarith.
Qed.

Lemma epow_add :
  forall e1 e2 : Z, (epow (e1+e2) = epow e1 * epow e2)%R.
Proof.
intros.
repeat rewrite epow_powerRZ.
apply powerRZ_add.
change R0 with (Z2R 0).
apply Z2R_neq.
destruct r; simpl; auto with zarith.
Qed.

Lemma epow_1 :
  epow 1 = Z2R (radix_val r).
Proof.
unfold epow, Zpower_pos, iter_pos.
now rewrite Zmult_1_r.
Qed.

End pow.


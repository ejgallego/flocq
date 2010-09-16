Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_float_prop.

Section Float_ops.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Definition Falign (f1 f2 : float beta) :=
  let '(Float m1 e1) := f1 in
  let '(Float m2 e2) := f2 in
  if Zle_bool e1 e2
  then (m1, (m2 * Zpower (radix_val beta) (e2 - e1))%Z, e1)
  else ((m1 * Zpower (radix_val beta) (e1 - e2))%Z, m2, e2).

Theorem Falign_spec :
  forall f1 f2 : float beta,
  let '(m1, m2 ,e) := Falign f1 f2 in
  F2R f1 = F2R (Float beta m1 e) /\ F2R f2 = F2R (Float beta m2 e).
Proof.
unfold Falign.
intros (m1, e1) (m2, e2).
generalize (Zle_cases e1 e2).
case (Zle_bool e1 e2) ; intros He ; split ; trivial.
now rewrite <- F2R_change_exp.
rewrite <- F2R_change_exp.
apply refl_equal.
omega.
Qed.

Theorem Falign_spec_exp:
  forall f1 f2 : float beta,
  snd (Falign f1 f2)= Zmin (Fexp f1) (Fexp f2).
intros f1 f2.
destruct f1 as (m1,e1);destruct f2 as (m2,e2).
unfold Falign; simpl.
generalize (Zle_cases e1 e2);case (Zle_bool e1 e2); intros He.
case (Zmin_spec e1 e2); intros (H1,H2); easy.
case (Zmin_spec e1 e2); intros (H1,H2); easy.
Qed.



Definition Fopp (f1: float beta) :=
   let '(Float m1 e1) := f1 in
    Float beta (-m1)%Z e1.

Theorem Fopp_F2R :
  forall f1 : float beta,
  (F2R (Fopp f1) = -F2R f1)%R.
unfold Fopp, F2R; intros (m1,e1).
simpl; rewrite opp_Z2R; ring.
Qed.

Definition Fabs (f1: float beta) :=
   let '(Float m1 e1) := f1 in
    Float beta (Zabs m1)%Z e1.

Theorem Fabs_F2R :
  forall f1 : float beta,
  (F2R (Fabs f1) = Rabs (F2R f1))%R.
intros (m1,e1).
now rewrite abs_F2R.
Qed.

Definition Fplus (f1 f2 : float beta) :=
  let '(m1, m2 ,e) := Falign f1 f2 in
  Float beta (m1 + m2) e.

Theorem plus_F2R :
  forall f1 f2 : float beta,
  F2R (Fplus f1 f2) = (F2R f1 + F2R f2)%R.
Proof.
intros f1 f2.
unfold Fplus.
generalize (Falign_spec f1 f2).
destruct (Falign f1 f2) as ((m1, m2), e).
intros (H1, H2).
rewrite H1, H2.
unfold F2R. simpl.
rewrite plus_Z2R.
apply Rmult_plus_distr_r.
Qed.


Definition Fminus (f1 f2 : float beta) :=
  Fplus f1 (Fopp f2).

Theorem minus_F2R :
  forall f1 f2 : float beta,
  F2R (Fminus f1 f2) = (F2R f1 - F2R f2)%R.
Proof.
intros f1 f2; unfold Fminus.
rewrite plus_F2R, Fopp_F2R.
ring.
Qed.


Definition Fmult (f1 f2 : float beta) :=
  let '(Float m1 e1) := f1 in
  let '(Float m2 e2) := f2 in
  Float beta (m1 * m2) (e1 + e2).

Theorem mult_F2R :
  forall f1 f2 : float beta,
  F2R (Fmult f1 f2) = (F2R f1 * F2R f2)%R.
Proof.
intros (m1, e1) (m2, e2).
unfold Fmult, F2R. simpl.
rewrite mult_Z2R, bpow_add.
ring.
Qed.

End Float_ops.

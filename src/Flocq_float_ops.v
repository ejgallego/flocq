Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_float_prop.

Section Flocq_float_ops.

Variable beta : radix.

Notation bpow e := (epow beta e).

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
rewrite mult_Z2R, epow_add.
ring.
Qed.

End Flocq_float_ops.
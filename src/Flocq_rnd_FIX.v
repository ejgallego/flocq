Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_generic.

Section RND_FIX.

Variable beta : radix.

Notation bpow := (epow beta).

Variable emin : Z.

(* fixed-point format *)
Definition FIX_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Fexp f = emin)%Z.

Definition FIX_RoundingModeP (rnd : R -> R):=
  Rounding_for_Format FIX_format rnd.

Definition FIX_exp (e : Z) := emin.

Theorem FIX_exp_correct : valid_exp FIX_exp.
Proof.
intros k.
unfold FIX_exp.
split ; intros H.
now apply Zlt_le_weak.
split.
apply Zle_refl.
now intros _ _.
Qed.

Theorem FIX_format_generic :
  forall x : R, generic_format beta FIX_exp x <-> FIX_format x.
Proof.
split.
(* . *)
intros ((xm, xe), (Hx1, Hx2)).
destruct (Req_dec x 0) as [Hx3|Hx3].
exists (Float beta 0 emin).
repeat split.
unfold F2R. simpl.
now rewrite Rmult_0_l.
specialize (Hx2 Hx3).
exists (Float beta xm emin).
repeat split.
rewrite Hx1.
apply (f_equal (fun e => F2R (Float beta xm e))).
simpl in Hx2.
now unfold FIX_exp in Hx2.
(* . *)
intros ((xm, xe), (Hx1, Hx2)).
exists (Float beta xm (FIX_exp xe)).
split.
unfold FIX_exp.
now rewrite <- Hx2.
now intros Hx3.
Qed.

Theorem FIX_format_satisfies_any :
  satisfies_any FIX_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FIX_exp _)).
exact FIX_format_generic.
exact FIX_exp_correct.
Qed.

End RND_FIX.

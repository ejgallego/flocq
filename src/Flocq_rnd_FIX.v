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
  forall x : R, FIX_format x <-> generic_format beta FIX_exp x.
Proof.
split.
(* . *)
intros ((xm, xe), (Hx1, Hx2)).
rewrite Hx1.
eexists ; repeat split.
exact Hx2.
(* . *)
intros ((xm, xe), (Hx1, Hx2)).
rewrite Hx1.
eexists ; repeat split.
exact Hx2.
Qed.

Theorem FIX_format_satisfies_any :
  satisfies_any FIX_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FIX_exp _)).
exact FIX_format_generic.
exact FIX_exp_correct.
Qed.

End RND_FIX.

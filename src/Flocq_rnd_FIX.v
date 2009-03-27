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

Theorem FIX_format_satisfies_any :
  satisfies_any FIX_format.
Proof.
pose (fexp (e : Z) := emin).
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta fexp _)).
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
unfold fexp in Hx2.
apply Hx2.
(* . *)
intros ((xm, xe), (Hx1, Hx2)).
exists (Float beta xm (fexp xe)).
split.
unfold fexp.
now rewrite <- Hx2.
now intros Hx3.
(* . *)
intros k.
unfold fexp.
split ; intros H.
now apply Zlt_le_weak.
split.
apply Zle_refl.
now intros _ _.
Qed.

End RND_FIX.

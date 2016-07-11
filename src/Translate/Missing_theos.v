Require Import Fcore.
Require Import Fprop_plus_error.
Require Import Fprop_mult_error.

Require Import FmaErr.

Require Import Ftranslate_flocq2Pff.

Open Scope R_scope.

Section ErrFMA.

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE).
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).

(** inputs *)
Variable a x y:R.
Hypothesis Fa: format a.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorith *)
Let r1 := round_flt (a*x+y).
Let u1 := round_flt (a*x).
Let u2 := u1-a*x.
Let alpha1 := round_flt (y+u2).
Let alpha2 := alpha1 -(y+u2).
Let beta1 := round_flt (u1+alpha1).
Let beta2 := beta1 -(u1+alpha1).
Let gamma := round_flt (round_flt (beta1-r1)+beta2).
Let r2 := round_flt (gamma+alpha2).
Let r3 := r2 - (gamma+alpha2).


(** Non-underflow hypotheses *)


(** theorems *)
Lemma ErrFMA_bounded: format r1 /\ format r2 /\ format r3.
Proof with auto with typeclass_instances.
split.
apply generic_format_round...
split.
apply generic_format_round...
apply plus_error...
apply generic_format_round...
apply plus_error...
apply mult_error_FLT...
admit. (* underflow *)
Qed.


Lemma ErrFMA_correct:
   r1+r2+r3 = a*x+y.
Proof with auto with typeclass_instances.
destruct (format_is_pff_format (make_bound emin prec) _ _ _ r1).

apply sym_eq; apply FmaErr_Even.

Admitted.


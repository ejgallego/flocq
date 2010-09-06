Require Import Fcore.
Require Import Fcalc_ops.

Section Fprop_divsqrt_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.
Notation format := (generic_format beta fexp).
Variable choice : R -> bool.

Theorem div_error_N :
  forall x y,
  format x -> format y ->
  format (x - rounding beta fexp (ZrndN choice) (x/y) * y)%R.
Proof.
(* probablement seulement en FLX *)
Admitted. (* SB *)

Theorem div_error_Z :
  forall x y,
  format x -> format y ->
  format (x - rounding beta fexp (ZrndTZ) (x/y) * y)%R.
Proof.
(* probablement seulement en FLX *)
Admitted. (* SB *) 


Theorem sqrt_error_N :
  forall x, (0 <= x)%R ->
  format x ->
  format (x - Rsqr (rounding beta fexp (ZrndN choice) (sqrt x)))%R.
Proof.
(* probablement seulement en FLX *)
Admitted. (* SB *)

End Fprop_divsqrt_error.

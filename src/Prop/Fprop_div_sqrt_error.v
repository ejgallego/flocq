Require Import Fcore.
Require Import Fcalc_ops.

Section Fprop_divsqrt_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable Hp : Zlt 0 prec.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (canonic_exponent beta (FLX_exp prec)).

Variable choice : R -> bool.

Theorem format_FLX: forall x,
  (exists f: float beta, x=F2R f /\ (cexp x <= Fexp f)%Z)
  -> format x.
intros x (f, (H1,H2)).
unfold generic_format.
rewrite H1 at 1; unfold F2R; simpl.
replace (Ztrunc (scaled_mantissa beta (FLX_exp prec) x)) with (Fnum f * Zpower (radix_val beta) (Fexp f - cexp x))%Z.
rewrite mult_Z2R.
rewrite Z2R_Zpower.
unfold Zminus; rewrite bpow_add.
rewrite Rmult_assoc; rewrite Rmult_assoc.
rewrite <- bpow_add.
ring_simplify (-cexp x+cexp x)%Z.
simpl; ring.
omega.
unfold scaled_mantissa.
replace (x*bpow (-cexp x))%R with (Z2R ((Fnum f * radix_val beta ^ (Fexp f - cexp x)))).
now rewrite Ztrunc_Z2R.
rewrite mult_Z2R.
rewrite Z2R_Zpower.
unfold Zminus; rewrite bpow_add.
rewrite H1 at 2; unfold F2R.
ring.
omega.
Qed.



Theorem div_error_N :
  forall x y,
  format x -> format y ->
  format (x - rounding beta (FLX_exp prec) (ZrndN choice) (x/y) * y)%R.
Proof.
Admitted. (* SB *)

Theorem div_error_Z :
  forall x y,
  format x -> format y ->
  format (x - rounding beta (FLX_exp prec) (ZrndTZ) (x/y) * y)%R.
Proof.
(* probablement seulement en FLX *)
Admitted. (* SB *) 


Theorem sqrt_error_N :
  forall x, (0 <= x)%R ->
  format x ->
  format (x - Rsqr (rounding beta (FLX_exp prec) (ZrndN choice) (sqrt x)))%R.
Proof.
(* probablement seulement en FLX *)
Admitted. (* SB *)

End Fprop_divsqrt_error.

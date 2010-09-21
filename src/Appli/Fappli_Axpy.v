Require Import Fcore.

Section Axpy.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable Hp : Zlt 0 prec.

(* FLX ou FLT ? *)

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (canonic_exponent beta (FLX_exp prec)).

Variable choice : R -> bool.

Variable a1 x1 y1 a x y:R.

Hypothesis Ha: format a.
Hypothesis Hx: format x.
Hypothesis Hy: format y.

Notation t := (rounding beta (FLX_exp prec) (ZrndN choice) (a*x)).
Notation u := (rounding beta (FLX_exp prec) (ZrndN choice) (t+y)).
Notation MinOrMax x f := 
   ((f = rounding beta (FLX_exp prec) ZrndUP x) 
     \/ (f = rounding beta (FLX_exp prec) ZrndDN x)).


Theorem Axpy_opt :
  (6 <= prec)%Z ->
 ((bpow 1 +1 + bpow (4-prec))* Rabs (a*x) <= Rabs y)%R ->
   (Rabs (y1 - y + a1 * x1 - a * x) <=
      bpow (1-prec) / (6*bpow 1) * Rabs y)%R ->
         (MinOrMax (a1 * x1 + y1) u).
Admitted.


End Axpy.
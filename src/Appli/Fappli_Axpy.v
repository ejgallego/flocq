Require Import Fcore.

Section Axpy.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable Hp : Zlt 0 prec.

(* FLX ou FLT ? *)

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (canonic_exponent beta (FLX_exp prec)).
Notation ulp := (ulp beta (FLX_exp prec)).

Definition MinOrMax x f := 
   ((f = rounding beta (FLX_exp prec) ZrndDN x) 
     \/ (f = rounding beta (FLX_exp prec) ZrndUP x)).

Theorem MinOrMax_opp: forall x f,
   MinOrMax x f <->  MinOrMax (-x) (-f).
assert (forall x f, MinOrMax x f -> MinOrMax (- x) (- f)).
unfold MinOrMax; intros x f [H|H].
right.
now rewrite H, rounding_UP_opp.
left.
now rewrite H, rounding_DN_opp.
intros x f; split; intros H1.
now apply H.
rewrite <- (Ropp_involutive x), <- (Ropp_involutive f).
now apply H.
Qed.


Theorem implies_DN_lt_ulp_f:
  forall x f, format f ->
  (0 < f <= x)%R ->
  (Rabs (f-x) < ulp f)%R -> 
  (f = rounding beta (FLX_exp prec) ZrndDN x)%R.
intros x f Hf Hxf1 Hxf2.
apply sym_eq.
replace x with (f+-(f-x))%R by ring.
apply rounding_DN_succ; trivial.
apply Hxf1.
replace (- (f - x))%R with (Rabs (f-x)).
split; trivial; apply Rabs_pos.
rewrite Rabs_left1; trivial.
now apply Rle_minus.
Qed.


Theorem implies_DN_lt_ulp:
  forall x f, format f ->
  (0 < f <= x)%R ->
  (Rabs (f-x) < ulp x)%R -> 
  (f = rounding beta (FLX_exp prec) ZrndDN x)%R.
intros x f Hf Hxf1 Hxf2.
apply implies_DN_lt_ulp_f; trivial.
Admitted.


Theorem implies_MinOrMax_quarter:
  forall x f, format f ->
  (Rabs (f-x) < /4* ulp x)%R -> 
  MinOrMax x f.
intros x f Hf Hxf.
Admitted.





Variable choice : R -> bool.

Variable a1 x1 y1 a x y:R.

Hypothesis Ha: format a.
Hypothesis Hx: format x.
Hypothesis Hy: format y.

Notation t := (rounding beta (FLX_exp prec) (ZrndN choice) (a*x)).
Notation u := (rounding beta (FLX_exp prec) (ZrndN choice) (t+y)).



Theorem Axpy_opt :
  (6 <= prec)%Z ->
 ((bpow 1 +1 + bpow (4-prec))* Rabs (a*x) <= Rabs y)%R ->
   (Rabs (y1 - y + a1 * x1 - a * x) <=
      bpow (1-prec) / (6*bpow 1) * Rabs y)%R ->
         (MinOrMax (a1 * x1 + y1) u).
Admitted.


End Axpy.
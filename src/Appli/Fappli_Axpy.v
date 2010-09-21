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


Theorem implies_MinOrMax_le:
  forall x f, format f ->
  (f <= x)%R ->
  (Rabs (f-x) < ulp x)%R -> 
  MinOrMax x f.
intros x f Hf Hxf1 Hxf2.
left; apply sym_eq.
apply Rnd_DN_pt_unicity with format x.
apply generic_DN_pt.
now apply FLX_exp_correct.
split;[assumption|idtac].
split;[assumption|idtac].
intros g Hg Hxg.
case (Rle_or_lt g f); trivial; intros Hfg.
contradict Hxf2.
apply Rle_not_lt.
rewrite Rabs_left1.
2: apply Rle_minus; assumption.
replace (-(f-x))%R with ((x-g)+(g-f))%R by ring.
rewrite <- (Rplus_0_l (ulp x)).
apply Rplus_le_compat.
apply Rle_0_minus; assumption.
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
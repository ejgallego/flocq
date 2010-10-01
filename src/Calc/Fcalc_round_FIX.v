Require Import Fcore.
Require Import Fcalc_bracket.
Require Import Fcalc_digits.

Section Fcalc_round_FIX.

Variable beta : radix.
Notation bpow e := (bpow beta e).
Variable emin : Z.
Notation format := (generic_format beta (FIX_exp emin)).

Definition round_FIX t :=
  let '(m, e, l) := t in
  let k := (emin - e)%Z in
  if Zlt_bool 0 k then
    let p := Zpower beta k in
    (Zdiv m p, (e + k)%Z, new_location p (Zmod m p) l)
  else t.

Theorem round_FIX_correct :
  forall x m e l,
  inbetween_float beta m e x l ->
  (e <= emin)%Z \/ l = loc_Exact ->
  let '(m', e', l') := round_FIX (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = canonic_exponent beta (FIX_exp emin) x \/ (l' = loc_Exact /\ format x)).
Proof.
intros x m e l H1 H2.
unfold round_FIX.
set (k := (emin - e)%Z).
set (p := Zpower beta k).
unfold canonic_exponent, FIX_exp.
generalize (Zlt_cases 0 k).
case (Zlt_bool 0 k) ; intros Hk.
(* shift *)
split.
now apply inbetween_float_new_location.
clear H2.
left.
unfold k.
ring.
(* no shift *)
split.
exact H1.
unfold k in Hk.
destruct H2 as [H2|H2].
left.
omega.
right.
split.
exact H2.
rewrite H2 in H1.
inversion_clear H1.
rewrite H.
apply generic_format_canonic_exponent.
unfold canonic_exponent.
omega.
Qed.

End Fcalc_round_FIX.

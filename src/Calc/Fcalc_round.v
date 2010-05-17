Require Import Fcore.
Require Import Fcalc_bracket.
Require Import Fcalc_digits.

Section Fcalc_round.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.
Notation format := (generic_format beta fexp).

Theorem round_DN_correct :
  forall x m e l,
  inbetween_float beta m e x l /\
  (e = canonic_exponent beta fexp x \/ (l = loc_Exact /\ format x)) ->
  rounding beta fexp ZrndDN x = F2R (Float beta m e).
Proof.
intros x m e l (Hin,[He|(Hl,Hf)]).
rewrite He in Hin |- *.
apply inbetween_float_DN with (1 := Hin).
rewrite Hl in Hin.
inversion_clear Hin.
rewrite <- H.
now apply rounding_generic.
Qed.

Theorem round_UP_correct :
  forall x m e l,
  inbetween_float beta m e x l /\
  (e = canonic_exponent beta fexp x \/ (l = loc_Exact /\ format x)) ->
  rounding beta fexp ZrndUP x = F2R (Float beta (cond_incr (round_UP l) m) e).
Proof.
intros x m e l (Hin,[He|(Hl,Hf)]).
rewrite He in Hin |- *.
apply inbetween_float_UP with (1 := Hin).
rewrite Hl in Hin.
inversion_clear Hin.
rewrite Hl. simpl.
rewrite <- H.
now apply rounding_generic.
Qed.

Theorem round_NE_correct :
  forall x m e l,
  inbetween_float beta m e x l /\
  (e = canonic_exponent beta fexp x \/ (l = loc_Exact /\ format x)) ->
  rounding beta fexp ZrndNE x = F2R (Float beta (cond_incr (round_NE (Zeven m) l) m) e).
Proof.
intros x m e l (Hin,[He|(Hl,Hf)]).
rewrite He in Hin |- *.
apply inbetween_float_NE with (1 := Hin).
rewrite Hl in Hin.
inversion_clear Hin.
rewrite Hl. simpl.
rewrite <- H.
now apply rounding_generic.
Qed.

End Fcalc_round.
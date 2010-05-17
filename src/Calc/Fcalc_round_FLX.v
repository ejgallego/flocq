Require Import Fcore.
Require Import Fcalc_bracket.
Require Import Fcalc_digits.

Section Fcalc_round_FLX.

Variable beta : radix.
Notation bpow e := (bpow beta e).
Variable prec : Z.
Variable Hprec : (1 < prec)%Z.
Notation format := (generic_format beta (FLX_exp prec)).

Definition round_FLX t :=
  let '(m, e, l) := t in
  let k := (digits beta m - prec)%Z in
  if Zlt_bool 0 k then
    let p := Zpower (radix_val beta) k in
    (Zdiv m p, (e + k)%Z, new_location p (Zmod m p) l)
  else t.

Theorem round_FLX_correct :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (prec <= digits beta m)%Z \/ l = loc_Exact ->
  let '(m', e', l') := round_FLX (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = canonic_exponent beta (FLX_exp prec) x \/ (l' = loc_Exact /\ format x)).
Proof.
intros x m e l Hx H1 H2.
unfold round_FLX.
set (k := (digits beta m - prec)%Z).
set (p := Zpower (radix_val beta) k).
(* *)
assert (Hx': (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R).
apply inbetween_bounds with (2 := H1).
apply F2R_lt_compat.
apply Zlt_succ.
(* *)
assert (Hm: (0 <= m)%Z).
cut (0 < m + 1)%Z. omega.
apply F2R_lt_reg with beta e.
rewrite F2R_0.
apply Rle_lt_trans with  (1 := Hx).
apply Hx'.
(* *)
assert (He: (m <> 0 -> e + k = canonic_exponent beta (FLX_exp prec) x)%Z).
intros H.
unfold canonic_exponent, FLX_exp.
rewrite ln_beta_F2R_bounds with (2 := Hx').
rewrite ln_beta_F2R with (1 := H).
rewrite <- digits_ln_beta with (1 := H).
unfold k.
ring.
omega.
(* *)
assert (He': (prec <= digits beta m -> e + k = canonic_exponent beta (FLX_exp prec) x)%Z).
intros Hp.
apply He.
destruct (Zle_lt_or_eq _ _ Hm) as [Hm'|Hm'].
apply sym_not_eq.
now apply Zlt_not_eq.
rewrite <- Hm' in Hp.
simpl in Hp.
omega.
clear Hm.
generalize (Zlt_cases 0 k).
case (Zlt_bool 0 k) ; intros Hk ; unfold k in Hk.
(* shift *)
split.
now apply inbetween_float_new_location.
clear H2.
left.
apply He'.
omega.
(* no shift *)
split.
exact H1.
assert (H3: prec = digits beta m \/ ((digits beta m <= prec)%Z /\ l = loc_Exact)).
destruct H2 as [H2|H2].
left.
omega.
right.
split.
omega.
easy.
clear H2.
destruct H3 as [H2|(H2,H3)].
(* . matching prec *)
left.
rewrite <- He'.
unfold k.
rewrite H2.
ring.
rewrite H2.
apply Zle_refl.
(* . exact location *)
right.
split.
exact H3.
rewrite H3 in H1.
inversion_clear H1.
rewrite H.
destruct (Z_eq_dec m 0) as [Hm|Hm].
rewrite Hm, F2R_0.
apply generic_format_0.
apply generic_format_canonic_exponent.
rewrite <- H, <- He.
unfold k.
omega.
exact Hm.
Qed.

End Fcalc_round_FLX.

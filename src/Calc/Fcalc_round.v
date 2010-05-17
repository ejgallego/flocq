Require Import Fcore.
Require Import Fcalc_bracket.
Require Import Fcalc_digits.

Section Fcalc_round.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.
Notation format := (generic_format beta fexp).

Definition truncate t :=
  let '(m, e, l) := t in
  let k := (fexp (digits beta m + e) - e)%Z in
  if Zlt_bool 0 k then
    let p := Zpower (radix_val beta) k in
    (Zdiv m p, (e + k)%Z, new_location p (Zmod m p) l)
  else t.

Theorem truncate_correct :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (digits beta m + e))%Z \/ l = loc_Exact ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = canonic_exponent beta fexp x \/ (l' = loc_Exact /\ format x)).
Proof.
intros x m e l Hx H1 H2.
unfold truncate.
set (k := (fexp (digits beta m + e) - e)%Z).
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
destruct Hx as [Hx|Hx].
(* . 0 < x *)
assert (He: (e + k = canonic_exponent beta fexp x)%Z).
(* .. *)
unfold canonic_exponent.
destruct (Zle_lt_or_eq _ _ Hm) as [Hm'|Hm'].
(* ... 0 < m *)
rewrite ln_beta_F2R_bounds with (1 := Hm') (2 := Hx').
assert (H: m <> Z0).
apply sym_not_eq.
now apply Zlt_not_eq.
rewrite ln_beta_F2R with (1 := H).
rewrite <- digits_ln_beta with (1 := H).
unfold k.
ring.
destruct H2 as [H2|H2].
(* ... m = 0 and enough digits *)
rewrite <- Hm' in H2.
destruct (ln_beta beta x) as (ex, Hex).
simpl.
specialize (Hex (Rgt_not_eq _ _ Hx)).
unfold k.
ring_simplify.
rewrite <- Hm'.
simpl.
apply sym_eq.
apply (proj2 (prop_exp e)).
exact H2.
apply Zle_trans with e.
eapply bpow_lt_bpow.
apply Rle_lt_trans with (1 := proj1 Hex).
rewrite Rabs_pos_eq.
rewrite <- F2R_bpow.
rewrite <- Hm' in Hx'.
apply Hx'.
now apply Rlt_le.
exact H2.
(* ... m = 0 and exact location *)
rewrite H2 in H1.
inversion_clear H1.
rewrite <- Hm', F2R_0 in H.
rewrite H in Hx.
elim Rlt_irrefl with (1 := Hx).
(* .. *)
generalize (Zlt_cases 0 k).
case (Zlt_bool 0 k) ; intros Hk ; unfold k in Hk.
(* ... shift *)
split.
now apply inbetween_float_new_location.
now left.
split.
exact H1.
destruct H2 as [H2|H2].
left.
rewrite <- He.
unfold k.
omega.
(* ... no shift *)
right.
split.
exact H2.
rewrite H2 in H1.
inversion_clear H1.
rewrite H.
apply generic_format_canonic_exponent.
rewrite <- H, <- He.
unfold k.
omega.
(* . x = 0 *)
destruct H1 as [H1|l' H1 _].
(* .. exact location *)
case (Zlt_bool 0 k).
(* ... shift *)
assert (Hm': m = Z0).
apply F2R_eq_0_reg with beta e.
rewrite <- H1.
now apply sym_eq.
rewrite Hm'.
rewrite Zdiv_0_l, Zmod_0_l.
replace (new_location p 0 loc_Exact) with loc_Exact.
split.
constructor.
rewrite F2R_0.
now apply sym_eq.
right.
repeat split.
rewrite <- Hx.
apply generic_format_0.
unfold new_location.
case (Zeven p) ; [ unfold new_location_even | unfold new_location_odd ] ;
  ( case Zeq_bool_spec ; [ easy | intros H ; now elim H ] ).
(* ... no shift *)
split.
now constructor.
right.
repeat split.
rewrite <- Hx.
apply generic_format_0.
(* .. inexact location *)
elim Rlt_not_le with (1 := proj1 H1).
rewrite <- Hx.
now apply F2R_ge_0_compat.
Qed.

Section round_dir.

Variable rnd: Zrounding.
Variable choice : Z -> location -> Z.
Hypothesis choice_valid : forall m, choice m loc_Exact = m.
Hypothesis inbetween_float_valid :
  forall x m l,
  let e := canonic_exponent beta fexp x in
  inbetween_float beta m e x l ->
  rounding beta fexp rnd x = F2R (Float beta (choice m l) e).

Theorem round_any_correct :
  forall x m e l,
  inbetween_float beta m e x l ->
  (e = canonic_exponent beta fexp x \/ (l = loc_Exact /\ format x)) ->
  rounding beta fexp rnd x = F2R (Float beta (choice m l) e).
Proof.
intros x m e l Hin [He|(Hl,Hf)].
rewrite He in Hin |- *.
apply inbetween_float_valid with (1 := Hin).
rewrite Hl in Hin.
inversion_clear Hin.
rewrite Hl, choice_valid.
rewrite <- H.
now apply rounding_generic.
Qed.

Theorem round_trunc_any_correct :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (digits beta m + e))%Z \/ l = loc_Exact ->
  let '(m', e', l') := truncate (m, e, l) in
  rounding beta fexp rnd x = F2R (Float beta (choice m' l') e').
Proof.
intros x m e l Hx Hl He.
generalize (truncate_correct x m e l Hx Hl He).
destruct (truncate (m, e, l)) as ((m', e'), l').
intros (H1, H2).
now apply round_any_correct.
Qed.

End round_dir.

Definition round_DN_correct :=
  round_any_correct _ (fun m _ => m)
    (fun _ => refl_equal _) (inbetween_float_DN beta fexp).

Definition round_trunc_DN_correct :=
  round_trunc_any_correct _ (fun m _ => m)
    (fun _ => refl_equal _) (inbetween_float_DN beta fexp).

Definition round_UP_correct :=
  round_any_correct _ (fun m l => cond_incr (round_UP l) m)
    (fun _ => refl_equal _) (inbetween_float_UP beta fexp).

Definition round_trunc_UP_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_UP l) m)
    (fun _ => refl_equal _) (inbetween_float_UP beta fexp).

Definition round_NE_correct :=
  round_any_correct _ (fun m l => cond_incr (round_NE (Zeven m) l) m)
    (fun _ => refl_equal _) (inbetween_float_NE beta fexp).

Definition round_trunc_NE_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_NE (Zeven m) l) m)
    (fun _ => refl_equal _) (inbetween_float_NE beta fexp).

End Fcalc_round.

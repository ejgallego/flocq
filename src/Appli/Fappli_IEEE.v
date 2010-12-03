Require Import Fcore.
Require Import Fcalc_digits.
Require Import Fcalc_round.
Require Import Fcalc_bracket.
Require Import Fcalc_ops.

Section Binary.

Variable prec emax : Z.
Hypothesis Hprec : (0 < prec)%Z.

Let fexp := FLT_exp (1 - (emax + prec)) prec.

Definition bounded_prec m e :=
  Zeq_bool (fexp (Z_of_nat (S (digits2_Pnat m)) + e)) e.

Definition bounded m e :=
  andb (bounded_prec m e) (Zle_bool e emax).

Inductive binary_float :=
  | B754_zero : bool -> binary_float
  | B754_infinity : bool -> binary_float
  | B754_nan : binary_float
  | B754_finite : bool ->
    forall (m : positive) (e : Z), bounded m e = true -> binary_float.

Definition radix2 := Build_radix 2 (refl_equal true).

Definition B2R f :=
  match f with
  | B754_finite s m e _ => F2R (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => R0
  end.

Theorem canonic_bounded_prec :
  forall (sx : bool) mx ex,
  bounded_prec mx ex = true ->
  canonic radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof.
intros sx mx ex H.
assert (Hx := Zeq_bool_eq _ _ H). clear H.
apply sym_eq.
simpl.
pattern ex at 2 ; rewrite <- Hx.
apply (f_equal fexp).
rewrite ln_beta_F2R_digits.
rewrite <- digits_abs.
rewrite Z_of_nat_S_digits2_Pnat.
now case sx.
now case sx.
Qed.

Theorem generic_format_B2R :
  forall x,
  generic_format radix2 fexp (B2R x).
Proof.
intros [sx|sx| |sx mx ex Hx] ; try apply generic_format_0.
simpl.
apply generic_format_canonic.
apply canonic_bounded_prec.
now destruct (andb_prop _ _ Hx) as (H, _).
Qed.

Definition is_finite_strict f :=
  match f with
  | B754_finite _ _ _ _ => true
  | _ => false
  end.

Theorem binary_unicity :
  forall x y : binary_float,
  is_finite_strict x = true ->
  is_finite_strict y = true ->
  B2R x = B2R y ->
  x = y.
Proof.
intros [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ; try easy.
simpl.
intros _ _ Heq.
assert (Hs: sx = sy).
(* *)
revert Heq. clear.
case sx ; case sy ; try easy ;
  intros Heq ; apply False_ind ; revert Heq.
apply Rlt_not_eq.
apply Rlt_trans with R0.
now apply F2R_lt_0_compat.
now apply F2R_gt_0_compat.
apply Rgt_not_eq.
apply Rgt_trans with R0.
now apply F2R_gt_0_compat.
now apply F2R_lt_0_compat.
assert (mx = my /\ ex = ey).
(* *)
refine (_ (canonic_unicity _ fexp _ _ _ _ Heq)).
rewrite Hs.
now case sy ; intro H ; injection H ; split.
apply canonic_bounded_prec.
exact (proj1 (andb_prop _ _ Hx)).
apply canonic_bounded_prec.
exact (proj1 (andb_prop _ _ Hy)).
(* *)
revert Hx.
rewrite Hs, (proj1 H), (proj2 H).
intros Hx.
apply f_equal.
apply eqbool_irrelevance.
Qed.

Definition is_finite f :=
  match f with
  | B754_finite _ _ _ _ => true
  | B754_zero _ => true
  | _ => false
  end.

Definition Bopp x :=
  match x with
  | B754_nan => x
  | B754_infinity sx => B754_infinity (negb sx)
  | B754_finite sx mx ex Hx => B754_finite (negb sx) mx ex Hx
  | B754_zero sx => B754_zero (negb sx)
  end.

Theorem Bopp_involutive :
  forall x, Bopp (Bopp x) = x.
Proof.
now intros [sx|sx| |sx mx ex Hx] ; simpl ; try rewrite Bool.negb_involutive.
Qed.

Theorem B2R_Bopp :
  forall x,
  B2R (Bopp x) = (- B2R x)%R.
Proof.
intros [sx|sx| |sx mx ex Hx] ; apply sym_eq ; try apply Ropp_0.
simpl.
rewrite opp_F2R.
now case sx.
Qed.

Inductive mode := mode_NE | mode_ZR | mode_DN | mode_UP | mode_NA.

Definition round_mode m :=
  match m with
  | mode_NE => rndNE
  | mode_ZR => rndZR
  | mode_DN => rndDN
  | mode_UP => rndUP
  | mode_NA => rndNA
  end.

Definition Bplus m x y :=
  match x, y with
  | B754_nan, _ => x
  | _, B754_nan => y
  | B754_infinity sx, B754_infinity sy =>
    if Bool.eqb sx sy then x else B754_nan
  | B754_infinity _, _ => x
  | _, B754_infinity _ => y
  | B754_zero sx, B754_zero sy =>
    if Bool.eqb sx sy then x else
    match m with mode_DN => B754_zero true | _ => B754_zero false end
  | B754_zero _, _ => y
  | _, B754_zero _ => x
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    B754_nan
  end.

Theorem B2R_Bplus :
  forall m x y,
  is_finite x = true ->
  is_finite y = true ->
  B2R (Bplus m x y) = round radix2 fexp (round_mode m) (B2R x + B2R y)%R.
Proof.
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ; try easy ; intros _ _.
(* *)
rewrite Rplus_0_r, round_0.
simpl.
case (Bool.eqb sx sy) ; try easy.
now case m.
(* *)
rewrite Rplus_0_l.
apply sym_eq.
apply round_generic.
apply generic_format_B2R.
(* *)
rewrite Rplus_0_r.
apply sym_eq.
apply round_generic.
apply generic_format_B2R.
(* *)
Admitted.

End Binary.

Require Import Fcore.
Require Import Fcalc_digits.
Require Import Fcalc_round.
Require Import Fcalc_bracket.
Require Import Fcalc_ops.

Section Binary.

Variable prec emin emax : Z.
Hypothesis Hprec : (0 < prec)%Z.
Hypothesis Hmin : (emin <= 0)%Z.
Hypothesis Hminmax : (emin <= emax)%Z.

Let fexp := FLT_exp emin prec.

Let fexp_correct : valid_exp fexp := FLT_exp_correct _ _ Hprec.

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

Theorem abs_B2R_lt_emax :
  forall x,
  (Rabs (B2R x) < bpow radix2 (emax + prec))%R.
Proof.
intros [sx|sx| |sx mx ex Hx] ; simpl ; try ( rewrite Rabs_R0 ; apply bpow_gt_0 ).
destruct (andb_prop _ _ Hx) as (H1,H2).
generalize (Zeq_bool_eq _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
replace (Rabs (F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex))) with (Rabs (F2R (Float radix2 (Zpos mx) ex))).
2: rewrite 2!abs_F2R ; now case sx.
generalize (ln_beta_F2R_digits radix2 (Zpos mx) ex).
destruct (ln_beta radix2 (F2R (Float radix2 (Zpos mx) ex))) as (e',Ex).
unfold ln_beta_val.
intros H.
apply Rlt_le_trans with (bpow radix2 e').
apply Ex.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
apply bpow_le.
rewrite H. 2: discriminate.
revert H1. clear -H2.
rewrite Z_of_nat_S_digits2_Pnat.
change Fcalc_digits.radix2 with radix2.
unfold fexp, FLT_exp.
generalize (Zmax_spec (digits radix2 (Zpos mx) + ex - prec) emin).
intros.
omega.
Qed.

Theorem bounded_canonic_lt_emax :
  forall mx ex,
  canonic radix2 fexp (Float radix2 (Zpos mx) ex) ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 (emax + prec))%R ->
  bounded mx ex = true.
Proof.
intros mx ex Cx Bx.
apply andb_true_intro.
split.
unfold bounded_prec.
unfold canonic, Fexp in Cx.
rewrite Cx at 2.
rewrite Z_of_nat_S_digits2_Pnat.
change Fcalc_digits.radix2 with radix2.
unfold canonic_exponent.
rewrite ln_beta_F2R_digits. 2: discriminate.
now apply -> Zeq_is_eq_bool.
apply Zle_bool_true.
unfold canonic, Fexp in Cx.
rewrite Cx.
unfold canonic_exponent, fexp, FLT_exp.
destruct (ln_beta radix2 (F2R (Float radix2 (Zpos mx) ex))) as (e',Ex). simpl.
apply Zmax_lub with (2 := Hminmax).
cut (e' - 1 < emax + prec)%Z. omega.
apply lt_bpow with radix2.
apply Rle_lt_trans with (2 := Bx).
change (Zpos mx) with (Zabs (Zpos mx)).
rewrite <- abs_F2R.
apply Ex.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
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

Definition choice_mode m sx mx lx :=
  match m with
  | mode_NE => cond_incr (round_N (negb (Zeven mx)) lx) mx
  | mode_ZR => mx
  | mode_DN => cond_incr (round_sign_DN sx lx) mx
  | mode_UP => cond_incr (round_sign_UP sx lx) mx
  | mode_NA => cond_incr (round_N true lx) mx
  end.

Definition binary_round_sign mode sx mx ex lx :=
  let '(m', e', l') := truncate radix2 fexp (Zpos mx, ex, lx) in
  let '(m'', e'', l'') := truncate radix2 fexp (choice_mode mode sx m' l', e', loc_Exact) in
  match m'' with
  | Z0 => B754_zero sx
  | Zpos m =>
    match Sumbool.sumbool_of_bool (bounded m e'') with
    | left H => B754_finite sx m e'' H
    | right _ => B754_infinity sx
    end
  | _ => B754_nan (* dummy *)
  end.

Theorem binary_round_sign_correct :
  forall mode x mx ex lx,
  inbetween_float radix2 (Zpos mx) ex (Rabs x) lx ->
  (ex <= fexp (digits radix2 (Zpos mx) + ex))%Z ->
  (Rabs (round radix2 fexp (round_mode mode) x) < bpow radix2 (emax + prec))%R ->
  B2R (binary_round_sign mode (Rlt_bool x 0) mx ex lx) = round radix2 fexp (round_mode mode) x.
Proof.
intros m x mx ex lx Bx Ex Hx.
unfold binary_round_sign.
refine (_ (round_trunc_sign_any_correct _ _ fexp_correct (round_mode m) (choice_mode m) _ x (Zpos mx) ex lx Bx (or_introl _ Ex))).
refine (_ (truncate_correct_partial _ _ fexp_correct _ _ _ _ _ Bx Ex)).
destruct (truncate radix2 fexp (Zpos mx, ex, lx)) as ((m1, e1), l1).
set (m1' := choice_mode m (Rlt_bool x 0) m1 l1).
intros (H1a,H1b) H1c.
rewrite H1c.
assert (Hm: (m1 <= m1')%Z).
(* . *)
unfold m1', choice_mode, cond_incr.
case m ;
  try apply Zle_refl ;
  match goal with |- (m1 <= if ?b then _ else _)%Z =>
    case b ; [ apply Zle_succ | apply Zle_refl ] end.
assert (Hr: Rabs (round radix2 fexp (round_mode m) x) = F2R (Float radix2 m1' e1)).
(* . *)
rewrite <- (Zabs_eq m1').
replace (Zabs m1') with (Zabs (cond_Zopp (Rlt_bool x 0) m1')).
rewrite <- abs_F2R.
now apply f_equal.
apply abs_cond_Zopp.
apply Zle_trans with (2 := Hm).
apply Zlt_succ_le.
apply F2R_gt_0_reg with radix2 e1.
apply Rle_lt_trans with (1 := Rabs_pos x).
exact (proj2 (inbetween_float_bounds _ _ _ _ _ H1a)).
(* . *)
assert (Br: inbetween_float radix2 m1' e1 (Rabs (round radix2 fexp (round_mode m) x)) loc_Exact).
now apply inbetween_Exact.
destruct m1' as [|m1'|m1'].
(* . m1' = 0 *)
generalize (truncate_0 radix2 fexp e1 loc_Exact).
destruct (truncate radix2 fexp (Z0, e1, loc_Exact)) as ((m2, e2), l2).
intros Hm2.
rewrite Hm2. simpl.
apply sym_eq.
case Rlt_bool ; apply F2R_0.
(* . 0 < m1' *)
assert (He: (e1 <= fexp (digits radix2 (Zpos m1') + e1))%Z).
rewrite <- ln_beta_F2R_digits, <- Hr, ln_beta_abs.
2: discriminate.
rewrite H1b.
rewrite canonic_exponent_abs.
fold (canonic_exponent radix2 fexp (round radix2 fexp (round_mode m) x)).
apply canonic_exponent_round.
apply fexp_correct.
apply FLT_exp_monotone.
rewrite H1c.
case (Rlt_bool x 0).
apply Rlt_not_eq.
now apply F2R_lt_0_compat.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
refine (_ (truncate_correct_partial _ _ fexp_correct _ _ _ _ _ Br He)).
2: now rewrite Hr ; apply F2R_gt_0_compat.
refine (_ (truncate_correct_format radix2 fexp (Zpos m1') e1 _ _ He)).
2: discriminate.
destruct (truncate radix2 fexp (Zpos m1', e1, loc_Exact)) as ((m2, e2), l2).
intros (H3,H4) (H2,_).
destruct m2 as [|m2|m2].
elim Rgt_not_eq with (2 := H3).
rewrite F2R_0.
now apply F2R_gt_0_compat.
case (Sumbool.sumbool_of_bool (bounded m2 e2)) ; intros Hb.
simpl.
now rewrite 2!F2R_cond_Zopp, H3.
rewrite bounded_canonic_lt_emax in Hb.
discriminate Hb.
unfold canonic.
now rewrite <- H3.
now rewrite <- H3, <- Hr.
elim Rgt_not_eq with (2 := H3).
apply Rlt_trans with R0.
now apply F2R_lt_0_compat.
now apply F2R_gt_0_compat.
rewrite <- Hr.
apply generic_format_abs.
apply generic_format_round.
apply fexp_correct.
(* . not m1' < 0 *)
elim Rgt_not_eq with (2 := Hr).
apply Rlt_le_trans with R0.
now apply F2R_lt_0_compat.
apply Rabs_pos.
(* *)
apply Rlt_le_trans with (2 := proj1 (inbetween_float_bounds _ _ _ _ _ Bx)).
now apply F2R_gt_0_compat.
(* all the modes are valid *)
clear. case m.
exact inbetween_int_NE_sign.
exact inbetween_int_ZR_sign.
exact inbetween_int_DN_sign.
exact inbetween_int_UP_sign.
exact inbetween_int_NA_sign.
Qed.

Definition Bmult m x y :=
  match x, y with
  | B754_nan, _ => x
  | _, B754_nan => y
  | B754_infinity sx, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity _, B754_zero _ => B754_nan
  | B754_zero _, B754_infinity _ => B754_nan
  | B754_finite sx _ _ _, B754_zero sy => B754_zero (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => B754_zero (xorb sx sy)
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    binary_round_sign m (xorb sx sy) (Pmult mx my) (ex + ey) loc_Exact
  end.

Theorem B2R_mult :
  forall m x y,
  (Rabs (round radix2 fexp (round_mode m) (B2R x * B2R y)%R) < bpow radix2 (emax + prec))%R ->
  B2R (Bmult m x y) = round radix2 fexp (round_mode m) (B2R x * B2R y)%R.
Proof.
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ;
  try ( intros ; apply sym_eq ; try rewrite Rmult_0_r ; try rewrite Rmult_0_l ; apply round_0 ).
simpl.
rewrite <- mult_F2R.
simpl Fmult.
replace (xorb sx sy) with (Rlt_bool (F2R (Float radix2 (cond_Zopp sx (Zpos mx) * cond_Zopp sy (Zpos my)) (ex + ey))) 0).
apply binary_round_sign_correct.
constructor.
rewrite abs_F2R.
apply F2R_eq_compat.
rewrite Zabs_Zmult.
now rewrite 2!abs_cond_Zopp.
(* *)
change (Zpos (mx * my)) with (Zpos mx * Zpos my)%Z.
assert (forall m e, bounded m e = true -> fexp (digits radix2 (Zpos m) + e) = e)%Z.
clear. intros m e Hb.
destruct (andb_prop _ _ Hb) as (H,_).
apply Zeq_bool_eq.
now rewrite <- Z_of_nat_S_digits2_Pnat.
generalize (H _ _ Hx) (H _ _ Hy).
clear sx sy Hx Hy H.
unfold fexp, FLT_exp.
refine (_ (digits_mult_ge radix2 (Zpos mx) (Zpos my) _ _)) ; try discriminate.
refine (_ (digits_gt_0 radix2 (Zpos mx) _) (digits_gt_0 radix2 (Zpos my) _)) ; try discriminate.
generalize (digits radix2 (Zpos mx)) (digits radix2 (Zpos my)) (digits radix2 (Zpos mx * Zpos my)).
clear -Hprec Hmin.
intros dx dy dxy Hx Hy Hxy.
zify ; intros ; subst.
omega.
(* *)
case sx ; case sy.
apply Rlt_bool_false.
now apply F2R_ge_0_compat.
apply Rlt_bool_true.
now apply F2R_lt_0_compat.
apply Rlt_bool_true.
now apply F2R_lt_0_compat.
apply Rlt_bool_false.
now apply F2R_ge_0_compat.
Qed.

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

Require Import Fcore.
Require Import Fprop_plus_error.

Open Scope R_scope.

Section av1.


Definition radix2 := Build_radix 2 (refl_equal true).
Notation bpow e := (bpow radix2 e).

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE). 
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation cexp := (canonic_exp radix2 (FLT_exp emin prec)).

Lemma FLT_format_double: forall u, format u -> format (2*u).
Proof with auto with typeclass_instances.
intros u Fu.
apply generic_format_FLT.
apply FLT_format_generic in Fu...
destruct Fu as (uf, (H1,(H2,H3))).
exists (Float radix2 (Fnum uf) (Fexp uf+1)).
split.
rewrite H1; unfold F2R; simpl.
rewrite bpow_plus, bpow_1.
simpl;ring.
split.
now simpl.
simpl; apply Zle_trans with (1:=H3).
omega.
Qed.


Lemma FLT_format_half: forall u, 
   format u -> bpow (prec+emin) <= Rabs u -> format (u/2).
Proof with auto with typeclass_instances.
intros u Fu H.
apply FLT_format_generic in Fu...
destruct Fu as ((n,e),(H1,(H2,H3))).
simpl in H1, H2, H3.
apply generic_format_FLT.
exists (Float radix2 n (e-1)).
split; simpl.
rewrite H1; unfold F2R; simpl.
unfold Zminus; rewrite bpow_plus.
simpl; unfold Rdiv; ring.
split;[assumption|idtac].
assert (prec + emin < prec +e)%Z;[idtac|omega].
apply lt_bpow with radix2.
apply Rle_lt_trans with (1:=H).
rewrite H1; unfold F2R; simpl.
rewrite Rabs_mult; rewrite (Rabs_right (bpow e)).
2: apply Rle_ge, bpow_ge_0.
rewrite bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite <- Z2R_abs.
rewrite <- Z2R_Zpower.
now apply Z2R_lt.
unfold Prec_gt_0 in prec_gt_0_; omega.
Qed.



Lemma FLT_ulp_le_id: forall u, bpow emin <= u -> ulp_flt u <= u.
Proof with auto with typeclass_instances.
intros u H.
case (Rle_or_lt (bpow (emin+prec-1)) u); intros Hu.
unfold ulp; rewrite canonic_exp_FLT_FLX.
unfold canonic_exp, FLX_exp.
destruct (ln_beta radix2 u) as (e,He); simpl.
apply Rle_trans with (bpow (e-1)).
apply bpow_le.
unfold Prec_gt_0 in prec_gt_0_; omega.
rewrite <- (Rabs_right u).
apply He.
apply Rgt_not_eq, Rlt_gt.
apply Rlt_le_trans with (2:=Hu).
apply bpow_gt_0.
apply Rle_ge, Rle_trans with (2:=Hu), bpow_ge_0.
rewrite Rabs_right.
assumption.
apply Rle_ge, Rle_trans with (2:=Hu), bpow_ge_0.
unfold ulp; rewrite canonic_exp_FLT_FIX.
apply H.
apply Rgt_not_eq, Rlt_gt.
apply Rlt_le_trans with (2:=H).
apply bpow_gt_0.
rewrite Rabs_right.
apply Rlt_le_trans with (1:=Hu).
apply bpow_le; omega.
apply Rle_ge, Rle_trans with (2:=H), bpow_ge_0.
Qed.



Lemma FLT_ulp_double: forall u, ulp_flt (2*u) <= 2*ulp_flt(u).
intros u.
pattern 2 at 2; replace 2 with (bpow 1) by reflexivity.
unfold ulp; rewrite <- bpow_plus.
apply bpow_le.
case (Rle_or_lt (bpow (emin+prec-1)) (Rabs u)); intros Hu.
(* *)
rewrite canonic_exp_FLT_FLX.
rewrite canonic_exp_FLT_FLX; trivial.
unfold canonic_exp, FLX_exp.
replace 2 with (bpow 1) by reflexivity.
rewrite Rmult_comm, ln_beta_mult_bpow.
omega.
intros H; contradict Hu.
apply Rlt_not_le; rewrite H, Rabs_R0.
apply bpow_gt_0.
apply Rle_trans with (1:=Hu).
rewrite Rabs_mult.
pattern (Rabs u) at 1; rewrite <- (Rmult_1_l (Rabs u)).
apply Rmult_le_compat_r.
apply Rabs_pos.
rewrite Rabs_right.
now auto with real.
apply Rle_ge; now auto with real.
(* *)
case (Req_dec u 0); intros K.
rewrite K, Rmult_0_r.
omega.
rewrite canonic_exp_FLT_FIX.
rewrite canonic_exp_FLT_FIX; trivial.
unfold FIX_exp, canonic_exp; omega.
apply Rlt_le_trans with (1:=Hu).
apply bpow_le; omega.
apply Rmult_integral_contrapositive_currified; trivial.
apply Rgt_not_eq, Rlt_gt; now auto with real.
rewrite Rabs_mult.
rewrite Rabs_right.
2: apply Rle_ge; now auto with real.
apply Rlt_le_trans with (2*bpow (emin + prec - 1)).
apply Rmult_lt_compat_l.
now auto with real.
assumption.
replace 2 with (bpow 1) by reflexivity.
rewrite <- bpow_plus.
apply bpow_le; omega.
Qed.



Definition average1 (x y : R) :=round_flt(round_flt(x+y)/2).

Variables x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let a:=(x+y)/2.
Let av:=average1 x y.


Lemma average1_symmetry: forall u v, average1 u v = average1 v u.
Proof.
intros u v; unfold average1.
rewrite Rplus_comm; reflexivity.
Qed.

Lemma average1_symmetry_Ropp: forall u v, average1 (-u) (-v) = - average1 u v.
Proof.
intros u v; unfold average1.
replace (-u+-v) with (-(u+v)) by ring.
rewrite round_NE_opp.
replace (- round_flt (u + v) / 2) with (- (round_flt (u + v) / 2)) by (unfold Rdiv; ring).
now rewrite round_NE_opp.
Qed.

Lemma average1_same_sign_1: 0 <= a -> 0 <= av.
Proof with auto with typeclass_instances.
intros H.
apply round_ge_generic...
apply generic_format_0.
apply Rmult_le_pos.
apply round_ge_generic...
apply generic_format_0.
apply Rmult_le_reg_r with (/2).
auto with real.
rewrite Rmult_0_l; exact H.
auto with real.
Qed.

Lemma average1_same_sign_2: a <= 0-> av <= 0.
Proof with auto with typeclass_instances.
intros H.
apply round_le_generic...
apply generic_format_0.
replace 0 with (0*/2) by ring.
apply Rmult_le_compat_r.
auto with real.
apply round_le_generic...
apply generic_format_0.
apply Rmult_le_reg_r with (/2).
auto with real.
rewrite Rmult_0_l; exact H.
Qed.

Lemma average1_between: Rmin x y <= av <= Rmax x y.
Proof with auto with typeclass_instances.
assert (forall u v, format u -> format v -> u <= v -> u <= average1 u v <= v).
(* *)
intros u v Fu Fv H; split.
apply round_ge_generic...
apply Rmult_le_reg_l with 2.
auto with real.
apply Rle_trans with (round_flt (u + v)).
2: right; field.
apply round_ge_generic...
now apply FLT_format_double.
replace (2*u) with (u+u) by ring.
now apply Rplus_le_compat_l.
apply round_le_generic...
apply Rmult_le_reg_l with 2.
auto with real.
apply Rle_trans with (round_flt (u + v)).
right; field.
apply round_le_generic...
now apply FLT_format_double.
replace (2*v) with (v+v) by ring.
now apply Rplus_le_compat_r.
(* *)
case (Rle_or_lt x y); intros H1.
rewrite Rmin_left; try exact H1.
rewrite Rmax_right; try exact H1.
now apply H.
rewrite Rmin_right; try (left;exact H1).
rewrite Rmax_left; try (left;exact H1).
unfold av; rewrite average1_symmetry.
apply H; trivial; left; exact H1.
Qed.


Lemma average1_zero: a = 0 -> av = 0.
Proof with auto with typeclass_instances.
intros H1; unfold av, average1.
replace (x+y) with 0.
rewrite round_0...
unfold Rdiv; rewrite Rmult_0_l.
rewrite round_0...
apply Rmult_eq_reg_r with (/2).
rewrite Rmult_0_l, <- H1; reflexivity.
apply Rgt_not_eq, Rlt_gt.
auto with real.
Qed.



Lemma average1_no_underflow: (bpow emin) <= Rabs a -> av <> 0.
Proof with auto with typeclass_instances.
intros H.
(* *)
cut (bpow emin <= Rabs av).
intros H1 H2.
rewrite H2 in H1; rewrite Rabs_R0 in H1.
contradict H1.
apply Rlt_not_le.
apply bpow_gt_0.
(* *)
apply abs_round_ge_generic...
apply FLT_format_bpow...
omega.
apply Rmult_le_reg_l with 2.
auto with real.
apply Rle_trans with (Rabs (round_flt (x + y))).
apply abs_round_ge_generic...
apply FLT_format_double.
apply FLT_format_bpow...
omega.
apply Rmult_le_reg_l with (/2).
auto with real.
apply Rle_trans with (bpow emin).
right; field.
apply Rle_trans with (1:=H).
right; unfold a.
unfold Rdiv; rewrite Rabs_mult.
rewrite (Rabs_right (/2)).
ring.
apply Rle_ge; auto with real.
right; unfold Rdiv; rewrite Rabs_mult.
rewrite (Rabs_right (/2)).
field.
apply Rle_ge; auto with real.
Qed.


Lemma average1_correct: Rabs (av -a) <= /2*ulp_flt a.
Proof with auto with typeclass_instances.
case (Rle_or_lt (bpow (prec + emin)) (Rabs (x+y))).
(* normal case: division by 2 is exact *)
intros H.
replace av with (round_flt (x + y) / 2).
apply Rmult_le_reg_l with 2.
auto with real.
apply Rle_trans with (Rabs (round_flt (x + y) - (x+y))).
rewrite <- (Rabs_right 2) at 1.
rewrite <- Rabs_mult.
right; apply f_equal.
unfold a; field.
apply Rle_ge; auto with real.
apply Rle_trans with (/2*ulp_flt (x+y)).
apply ulp_half_error...
right; apply trans_eq with (/2*(2*ulp_flt a)).
2: ring.
apply f_equal.
unfold ulp, a.
pattern 2 at 1; replace 2 with (bpow 1) by reflexivity.
rewrite <- bpow_plus.
apply f_equal.
unfold Rdiv; replace (/2) with (bpow (-1)) by reflexivity.
rewrite canonic_exp_FLT_FLX.
rewrite canonic_exp_FLT_FLX.
unfold canonic_exp, FLX_exp.
rewrite ln_beta_mult_bpow.
ring.
intros H1; rewrite H1, Rabs_R0 in H.
contradict H; apply Rlt_not_le, bpow_gt_0.
rewrite Rabs_mult.
rewrite (Rabs_right (bpow (-1))).
unfold Zminus; rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite Zplus_comm; exact H.
apply Rle_ge, bpow_ge_0.
apply Rle_trans with (2:=H).
apply bpow_le; omega.
apply sym_eq, round_generic...
apply FLT_format_half.
apply generic_format_round...
apply abs_round_ge_generic...
apply FLT_format_bpow...
unfold Prec_gt_0 in prec_gt_0_; omega.
(* subnormal case: addition is exact, but division by 2 is not *)
intros H.
unfold av, average1.
replace (round_flt (x + y)) with (x+y).
unfold a; apply ulp_half_error...
apply sym_eq, round_generic...
apply FLT_format_plus_small...
left; assumption.
Qed.

Lemma average1_correct_weak: Rabs (av -a) <= 3/2*ulp_flt a.
Proof with auto with typeclass_instances.
apply Rle_trans with (1:=average1_correct).
apply Rmult_le_compat_r.
unfold ulp; apply bpow_ge_0.
apply Rle_trans with (1/2); unfold Rdiv.
right; ring.
apply Rmult_le_compat_r.
now auto with real.
apply Rplus_le_reg_l with (-1); ring_simplify.
now auto with real.
Qed.



(* Hypothesis diff_sign: (0 <= x /\ y <= 0) \/ (x <= 0 /\ 0 <= y).
  is useless for properties: only useful for preventing overflow *)


End av1.

Section av3.

Notation bpow e := (bpow radix2 e).

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE). 
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation cexp := (canonic_exp radix2 (FLT_exp emin prec)).

Definition average3 (x y : R) :=round_flt(x+round_flt(round_flt(y-x)/2)).

Variables x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let a:=(x+y)/2.
Let av:=average3 x y.


Lemma average3_symmetry_Ropp: forall u v, average3 (-u) (-v) = - average3 u v.
intros u v; unfold average3.
replace (-v--u) with (-(v-u)) by ring.
rewrite round_NE_opp.
replace (- round_flt (v-u) / 2) with (- (round_flt (v-u) / 2)) by (unfold Rdiv; ring).
rewrite round_NE_opp.
replace (- u + - round_flt (round_flt (v - u) / 2)) with
   (-(u+round_flt (round_flt (v - u) / 2))) by ring.
apply round_NE_opp.
Qed.


Lemma average3_same_sign_1: 0 <= a -> 0 <= av.
Proof with auto with typeclass_instances.
intros H.
apply round_ge_generic...
apply generic_format_0.
apply Rplus_le_reg_l with (-x).
ring_simplify.
apply round_ge_generic...
now apply generic_format_opp.
apply Rmult_le_reg_l with 2.
auto with real.
apply Rle_trans with (-(2*x)).
right; ring.
apply Rle_trans with (round_flt (y - x)).
2: right; field.
apply round_ge_generic...
apply generic_format_opp.
now apply FLT_format_double...
apply Rplus_le_reg_l with (2*x).
apply Rmult_le_reg_r with (/2).
auto with real.
apply Rle_trans with 0;[right; ring|idtac].
apply Rle_trans with (1:=H).
right; unfold a, Rdiv; ring.
Qed.

Lemma average3_same_sign_2: a <= 0-> av <= 0.
Proof with auto with typeclass_instances.
intros H.
apply round_le_generic...
apply generic_format_0.
apply Rplus_le_reg_l with (-x).
ring_simplify.
apply round_le_generic...
now apply generic_format_opp.
apply Rmult_le_reg_l with 2.
auto with real.
apply Rle_trans with (-(2*x)).
2: right; ring.
apply Rle_trans with (round_flt (y - x)).
right; field.
apply round_le_generic...
apply generic_format_opp.
now apply FLT_format_double...
apply Rplus_le_reg_l with (2*x).
apply Rmult_le_reg_r with (/2).
auto with real.
apply Rle_trans with 0;[idtac|right; ring].
apply Rle_trans with (2:=H).
right; unfold a, Rdiv; ring.
Qed.




Lemma average3_between_aux: forall u v, format u -> format v -> u <= v ->
    u <= average3 u v <= v.
Proof with auto with typeclass_instances.
clear Fx Fy a av x y.
intros x y Fx Fy M.
split.
(* . *)
apply round_ge_generic...
apply Rplus_le_reg_l with (-x).
ring_simplify.
apply round_ge_generic...
apply generic_format_0.
unfold Rdiv; apply Rmult_le_pos.
apply round_ge_generic...
apply generic_format_0.
apply Rplus_le_reg_l with x.
now ring_simplify.
auto with real.
(* . *)
apply round_le_generic...
assert (H:(0 <= round radix2 (FLT_exp emin prec) Zfloor (y-x))).
apply round_ge_generic...
apply generic_format_0.
apply Rplus_le_reg_l with x.
now ring_simplify.
destruct H as [H|H].
(* .. *)
pattern y at 2; replace y with (x + (y-x)) by ring.
apply Rplus_le_compat_l.
case (generic_format_EM radix2 (FLT_exp emin prec) (y-x)); intros K.
apply round_le_generic...
rewrite round_generic...
apply Rmult_le_reg_l with 2.
auto with real.
apply Rplus_le_reg_l with (2*x-y).
apply Rle_trans with x.
right; field.
apply Rle_trans with (1:=M).
right; field.
apply Rle_trans with (round radix2 (FLT_exp emin prec) Zfloor (y - x)).
apply round_le_generic...
apply generic_format_round...
apply Rmult_le_reg_l with 2.
auto with real.
apply Rle_trans with (round_flt (y - x)).
right; field.
case (round_DN_or_UP radix2 (FLT_exp emin prec) ZnearestE (y-x));
   intros H1; rewrite H1.
apply Rplus_le_reg_l with (-round radix2 (FLT_exp emin prec) Zfloor (y - x)).
ring_simplify.
now left.
rewrite ulp_DN_UP.
apply Rplus_le_reg_l with (-round radix2 (FLT_exp emin prec) Zfloor (y - x)); ring_simplify.
apply round_DN_pt...
unfold ulp.
apply FLT_format_bpow...
apply Z.le_max_r.
case (Rle_or_lt (bpow (emin + prec - 1))  (y-x)); intros P.
apply FLT_ulp_le_id...
apply Rle_trans with (2:=P).
apply bpow_le; unfold Prec_gt_0 in prec_gt_0_; omega.
contradict K.
apply FLT_format_plus_small...
now apply generic_format_opp.
rewrite Rabs_right.
apply Rle_trans with (bpow (emin+prec-1)).
left; exact P.
apply bpow_le; omega.
apply Rle_ge; apply Rplus_le_reg_l with x; now ring_simplify.
assumption.
apply round_DN_pt...
(* .. *)
case M; intros H1.
2: rewrite H1; replace (y-y) with 0 by ring.
2: rewrite round_0...
2: unfold Rdiv; rewrite Rmult_0_l.
2: rewrite round_0...
2: right; ring.
apply Rle_trans with (x+0).
2: rewrite Rplus_0_r; assumption.
apply Rplus_le_compat_l.
replace 0 with (round_flt (bpow emin/2)).
apply round_le...
unfold Rdiv; apply Rmult_le_compat_r.
auto with real.
apply round_le_generic...
apply FLT_format_bpow...
omega.
case (Rle_or_lt (y-x) (bpow emin)); trivial.
intros H2.
contradict H.
apply Rlt_not_eq.
apply Rlt_le_trans with (bpow emin).
apply bpow_gt_0.
apply round_DN_pt...
apply FLT_format_bpow...
omega.
now left.
replace (bpow emin /2) with (bpow (emin-1)).
unfold round, scaled_mantissa, canonic_exp, FLT_exp.
rewrite ln_beta_bpow.
replace (emin - 1 + 1 - prec)%Z with (emin-prec)%Z by ring.
rewrite Z.max_r.
2: unfold Prec_gt_0 in prec_gt_0_; omega.
rewrite <- bpow_plus.
replace (emin-1+-emin)%Z with (-1)%Z by ring.
replace (ZnearestE (bpow (-1))) with 0%Z.
unfold F2R; simpl; ring.
simpl; unfold Znearest.
replace (Zfloor (/2)) with 0%Z.
rewrite Rcompare_Eq.
reflexivity.
simpl; ring.
apply sym_eq, Zfloor_imp.
simpl; split.
auto with real.
apply Rmult_lt_reg_l with 2.
auto with real.
apply Rle_lt_trans with 1.
right; field.
rewrite Rmult_1_r.
auto with real.
unfold Zminus; rewrite bpow_plus.
reflexivity.
Qed.

Lemma average3_between: Rmin x y <= av <= Rmax x y.
Proof with auto with typeclass_instances.
case (Rle_or_lt x y); intros M.
(* x <= y *)
rewrite Rmin_left; try exact M.
rewrite Rmax_right; try exact M.
now apply average3_between_aux.
(* y < x *)
rewrite Rmin_right; try now left.
rewrite Rmax_left; try now left.
unfold av; rewrite <- (Ropp_involutive x); rewrite <- (Ropp_involutive y).
rewrite average3_symmetry_Ropp.
split; apply Ropp_le_contravar.
apply average3_between_aux.
now apply generic_format_opp.
now apply generic_format_opp.
apply Ropp_le_contravar; now left.
apply average3_between_aux.
now apply generic_format_opp.
now apply generic_format_opp.
apply Ropp_le_contravar; now left.
Qed.


Lemma average3_zero: a = 0 -> av = 0.
Proof with auto with typeclass_instances.
intros H.
assert (y=-x).
apply Rplus_eq_reg_l with x.
apply Rmult_eq_reg_r with (/2).
apply trans_eq with a.
reflexivity.
rewrite H; ring.
apply Rgt_not_eq, Rlt_gt.
auto with real.
unfold av, average3.
rewrite H0.
replace (-x-x) with (-(2*x)) by ring.
rewrite round_generic with (x:=(-(2*x)))...
replace (-(2*x)/2) with (-x) by field.
rewrite round_generic with (x:=-x)...
replace (x+-x) with 0 by ring.
apply round_0...
now apply generic_format_opp.
apply generic_format_opp.
now apply FLT_format_double.
Qed.


Lemma average3_no_underflow_aux_aux: forall z:Z, (0 < z)%Z -> 
    (ZnearestE (Z2R z / 2) < z)%Z.
Proof.
intros z H1.
case (Zle_lt_or_eq 1 z); [omega|intros H2|intros H2].
apply lt_Z2R.
apply Rplus_lt_reg_r with (- ((Z2R z)/2)).
apply Rle_lt_trans with (-(((Z2R z) /2) - Z2R (ZnearestE (Z2R z / 2)))).
right; ring.
apply Rle_lt_trans with (1:= RRle_abs _).
rewrite Rabs_Ropp.
apply Rle_lt_trans with (1:=Znearest_N (fun x => negb (Zeven x)) _).
apply Rle_lt_trans with (1*/2);[right; ring|idtac].
apply Rlt_le_trans with ((Z2R z)*/2);[idtac|right; field].
apply Rmult_lt_compat_r.
auto with real.
replace 1 with (Z2R 1) by reflexivity.
now apply Z2R_lt.
rewrite <- H2.
unfold Znearest; simpl.
replace (Zfloor (1 / 2)) with 0%Z.
rewrite Rcompare_Eq.
simpl; omega.
simpl; field.
unfold Rdiv; rewrite Rmult_1_l.
apply sym_eq, Zfloor_imp.
simpl; split.
auto with real.
apply Rmult_lt_reg_l with 2.
auto with real.
apply Rle_lt_trans with 1.
right; field.
rewrite Rmult_1_r.
auto with real.
Qed.


Lemma average3_no_underflow_aux1: forall f, format f -> 0 < f ->
  f <= round_flt (f/2) -> False.
Proof with auto with typeclass_instances.
intros f Ff Hf1 Hf2.
apply FLT_format_generic in Ff...
destruct Ff as (g, (H1,(H2,H3))).
case (Zle_lt_or_eq emin (Fexp g)); try exact H3; intros H4.
contradict Hf2.
apply Rlt_not_le.
rewrite round_generic...
apply Rplus_lt_reg_l with (-(f/2)).
apply Rle_lt_trans with 0;[right; ring|idtac].
apply Rlt_le_trans with (f*/2);[idtac|right;field].
apply Rmult_lt_0_compat; try assumption.
auto with real.
apply generic_format_FLT.
exists (Float radix2 (Fnum g) (Fexp g-1)).
split.
rewrite H1; unfold F2R; simpl.
unfold Zminus; rewrite bpow_plus.
simpl; field.
split.
now simpl.
simpl; omega.
contradict Hf2; apply Rlt_not_le.
unfold round, scaled_mantissa.
replace (cexp (f/2)) with emin.
rewrite H1; unfold F2R; simpl.
rewrite <- H4.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Z2R_lt.
replace (Z2R (Fnum g) * bpow emin / 2 * bpow (- emin)) with (Z2R (Fnum g) /2).
apply average3_no_underflow_aux_aux.
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow (Fexp g)).
apply bpow_gt_0.
rewrite Rmult_0_l.
apply Rlt_le_trans with (1:=Hf1).
right; rewrite H1; reflexivity.
unfold Rdiv; apply trans_eq with (Z2R (Fnum g) * / 2 * (bpow (- emin)*bpow emin)).
rewrite <- bpow_plus.
ring_simplify (-emin+emin)%Z.
simpl; ring.
ring.
apply sym_eq, canonic_exp_FLT_FIX.
apply Rgt_not_eq, Rlt_gt.
unfold Rdiv; apply Rmult_lt_0_compat; try assumption.
auto with real.
rewrite H1; unfold F2R, Rdiv; simpl.
replace (/2) with (bpow (-1)) by reflexivity.
rewrite Rmult_assoc, <- bpow_plus.
rewrite Rabs_mult.
rewrite (Rabs_right (bpow _)).
2: apply Rle_ge, bpow_ge_0.
rewrite (Zplus_comm emin _).
rewrite (bpow_plus _ prec _).
apply Rmult_lt_compat.
apply Rabs_pos.
apply bpow_ge_0.
rewrite <- Z2R_Zpower, <- Z2R_abs.
now apply Z2R_lt.
unfold Prec_gt_0 in prec_gt_0_; omega.
rewrite <- H4; apply bpow_lt.
omega.
Qed.


Lemma average3_no_underflow_aux2: forall u v, format u -> format v -> 
    (0 <= u /\ 0 <= v) \/ (u <= 0 /\ v <= 0) ->
    u <= v ->
   (bpow emin) <= Rabs ((u+v)/2) -> average3 u v <> 0.
Proof with auto with typeclass_instances.
clear Fx Fy a av x y; intros x y Fx Fy same_sign xLey H; unfold average3.
intros J.
apply round_plus_eq_zero in J...
2: apply generic_format_round...
assert (H1:x <= 0).
apply Rplus_le_reg_r with (round_flt (round_flt (y - x) / 2)).
rewrite J, Rplus_0_l.
apply round_ge_generic...
apply generic_format_0.
unfold Rdiv; apply Rmult_le_pos.
apply round_ge_generic...
apply generic_format_0.
apply Rplus_le_reg_l with x; now ring_simplify.
auto with real.
destruct H1 as [H1|H1].
(* *)
destruct same_sign as [(H2,H3)|(_,H2)].
contradict H2; now apply Rlt_not_le.
apply average3_no_underflow_aux1 with (-x).
now apply generic_format_opp.
rewrite <- Ropp_0; now apply Ropp_lt_contravar.
apply Rle_trans with (round_flt (round_flt (y - x) / 2)).
apply Rplus_le_reg_l with x.
rewrite J; right; ring.
apply round_le...
unfold Rdiv; apply Rmult_le_compat_r.
auto with real.
apply round_le_generic...
now apply generic_format_opp.
apply Rplus_le_reg_l with x.
now ring_simplify.
(* *)
rewrite H1 in J, H.
rewrite Rplus_0_l in H.
contradict J; apply Rgt_not_eq, Rlt_gt.
rewrite Rplus_0_l.
unfold Rminus; rewrite Ropp_0, Rplus_0_r.
rewrite round_generic with (x:=y)...
apply Rlt_le_trans with (bpow emin).
apply bpow_gt_0.
apply round_ge_generic...
apply FLT_format_bpow...
omega.
apply Rle_trans with (1:=H).
right; apply Rabs_right.
apply Rle_ge; unfold Rdiv; apply Rmult_le_pos.
rewrite <- H1; assumption.
auto with real.
Qed.

Lemma average3_no_underflow_aux3: forall u v, format u -> format v -> 
    (0 <= u /\ 0 <= v) \/ (u <= 0 /\ v <= 0) ->
   (bpow emin) <= Rabs ((u+v)/2) -> average3 u v <> 0.
Proof with auto with typeclass_instances.
clear Fx Fy a av x y; intros x y Fx Fy.
intros same_sign H.
case (Rle_or_lt x y); intros H1.
now apply average3_no_underflow_aux2.
rewrite <- (Ropp_involutive x); rewrite <- (Ropp_involutive y).
rewrite average3_symmetry_Ropp.
apply Ropp_neq_0_compat.
apply average3_no_underflow_aux2.
now apply generic_format_opp.
now apply generic_format_opp.
rewrite <- Ropp_0; case same_sign; intros (T1,T2).
right; split; now apply Ropp_le_contravar.
left; split; now apply Ropp_le_contravar.
apply Ropp_le_contravar; now left.
apply Rle_trans with (1:=H).
rewrite <- Rabs_Ropp.
right; apply f_equal.
unfold Rdiv; ring.
Qed.


Lemma average3_no_underflow: 
  (0 <= x /\ 0 <= y) \/ (x <= 0 /\ y <= 0) ->
  (bpow emin) <= Rabs a -> av <> 0.
Proof with auto with typeclass_instances.
intros; now apply average3_no_underflow_aux3.
Qed.



Lemma average3_correct_aux: forall u v, format u -> format v -> u <= v ->
     (0 <= u /\ 0 <= v) \/ (u <= 0 /\ v <= 0) ->
     0 < Rabs ((u+v)/2) < bpow emin ->
     Rabs (average3 u v -((u+v)/2)) <= 3/2 * ulp_flt ((u+v)/2).
Proof with auto with typeclass_instances.
clear Fx Fy a av x y.
intros x y Fx Fy xLey same_sign.
pose (a:=(x+y)/2); fold a.
(* mostly forward proof *)
intros (H1,H2).
apply generic_format_FIX_FLT,FIX_format_generic in Fx.
apply generic_format_FIX_FLT,FIX_format_generic in Fy.
destruct Fx as ((nx,ex),(J1,J2)).
destruct Fy as ((ny,ey),(J3,J4)); simpl in J2, J4.
(* a is bpow emin /2 *)
assert (a = Z2R (nx+ny) * bpow (emin-1)).
unfold a; rewrite J1, J3; unfold F2R; rewrite J2,J4; simpl.
unfold Zminus; rewrite bpow_plus, Z2R_plus; simpl; field.
assert (Z.abs (nx+ny) = 1)%Z.
assert (0 < Z.abs (nx+ny) < 2)%Z;[idtac|omega].
split; apply lt_Z2R; simpl; rewrite Z2R_abs; 
 apply Rmult_lt_reg_l with (bpow (emin-1)); try apply bpow_gt_0.
rewrite Rmult_0_r.
apply Rlt_le_trans with (1:=H1).
right; rewrite H, Rabs_mult.
rewrite (Rabs_right (bpow (emin -1))).
ring.
apply Rle_ge, bpow_ge_0.
apply Rle_lt_trans with (Rabs a).
right; rewrite H, Rabs_mult.
rewrite (Rabs_right (bpow (emin -1))).
ring.
apply Rle_ge, bpow_ge_0.
apply Rlt_le_trans with (1:=H2).
right; unfold Zminus; rewrite bpow_plus.
simpl; field.
(* only 2 possible values for x and y *)
assert (((nx=0)/\ (ny=1)) \/ ((nx=-1)/\(ny=0)))%Z.
assert (nx <= ny)%Z.
apply le_Z2R.
apply Rmult_le_reg_r with (bpow emin).
apply bpow_gt_0.
apply Rle_trans with x.
right; rewrite J1,J2; reflexivity.
apply Rle_trans with (1:=xLey).
right; rewrite J3,J4; reflexivity.
case same_sign; intros (L1,L2).
rewrite J1 in L1; apply F2R_ge_0_reg in L1; simpl in L1.
rewrite J3 in L2; apply F2R_ge_0_reg in L2; simpl in L2.
left.
rewrite Z.abs_eq in H0.
omega.
omega.
rewrite J1 in L1; apply F2R_le_0_reg in L1; simpl in L1.
rewrite J3 in L2; apply F2R_le_0_reg in L2; simpl in L2.
right.
rewrite Z.abs_neq in H0.
omega.
omega.
(* look into the 2 possible cases *)
assert (G1:(round_flt (bpow emin/2) = 0)).
replace (bpow emin /2) with (bpow (emin-1)).
unfold round, scaled_mantissa.
rewrite canonic_exp_FLT_FIX.
unfold canonic_exp, FIX_exp; simpl.
rewrite <- bpow_plus.
replace (bpow (emin - 1 + - emin)) with (/2).
replace (ZnearestE (/ 2)) with 0%Z.
unfold F2R; simpl; ring.
unfold Znearest.
replace (Zfloor (/2)) with 0%Z.
rewrite Rcompare_Eq.
reflexivity.
simpl; ring.
apply sym_eq, Zfloor_imp.
simpl; split.
auto with real.
apply Rmult_lt_reg_l with 2.
auto with real.
apply Rle_lt_trans with 1.
right; field.
rewrite Rmult_1_r.
auto with real.
ring_simplify (emin-1+-emin)%Z; reflexivity.
apply Rgt_not_eq, Rlt_gt, bpow_gt_0.
rewrite Rabs_right.
apply bpow_lt.
unfold Prec_gt_0 in prec_gt_0_; omega.
apply Rle_ge, bpow_ge_0.
unfold Zminus; rewrite bpow_plus.
reflexivity.
case H3; intros (T1,T2).
unfold a, average3.
rewrite J1,J3,J2,J4,T1,T2; unfold F2R; simpl.
rewrite Rmult_0_l, Rmult_1_l, 2!Rplus_0_l.
unfold Rminus; rewrite Ropp_0, Rplus_0_r.
rewrite (round_generic _ _ _ (bpow (emin)))...
2: apply FLT_format_bpow...
2: omega.
rewrite G1.
rewrite round_0...
rewrite Rplus_0_l, Rabs_Ropp.
rewrite Rabs_right.
2: apply Rle_ge, Rmult_le_pos.
2: apply bpow_ge_0.
2: now auto with real.
apply Rle_trans with ((3*ulp_flt (bpow emin / 2))/2);[idtac|right; unfold Rdiv; ring].
unfold Rdiv; apply Rmult_le_compat_r.
now auto with real.
apply Rle_trans with (3*bpow emin).
apply Rle_trans with (1*bpow emin).
right; ring.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rplus_le_reg_l with (-1); ring_simplify.
now auto with real.
apply Rmult_le_compat_l.
apply Fourier_util.Rle_zero_pos_plus1.
now auto with real.
unfold ulp; apply bpow_le.
unfold canonic_exp, FLT_exp.
apply Z.le_max_r.
unfold a, average3.
rewrite J1,J3,J2,J4,T1,T2; unfold F2R; simpl.
rewrite Rmult_0_l, Rplus_0_r.
replace (0 - -1 * bpow emin) with (bpow emin) by ring.
rewrite (round_generic _ _ _ (bpow (emin)))...
2: apply FLT_format_bpow...
2: omega.
rewrite G1.
replace (-1 * bpow emin + 0) with (-bpow emin) by ring.
rewrite round_generic...
2: apply generic_format_opp.
2: apply FLT_format_bpow...
2: omega.
replace (- bpow emin - -1 * bpow emin / 2) with (-((bpow emin)/2)) by field.
rewrite Rabs_Ropp.
rewrite Rabs_right.
replace (-1 * bpow emin / 2) with (-((bpow emin/2))) by field.
rewrite ulp_opp.
apply Rle_trans with ((3*ulp_flt (bpow emin / 2))/2);[idtac|right; unfold Rdiv; ring].
unfold Rdiv; apply Rmult_le_compat_r.
now auto with real.
apply Rle_trans with (3*bpow emin).
apply Rle_trans with (1*bpow emin).
right; ring.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rplus_le_reg_l with (-1); ring_simplify.
now auto with real.
apply Rmult_le_compat_l.
apply Fourier_util.Rle_zero_pos_plus1.
now auto with real.
unfold ulp; apply bpow_le.
unfold canonic_exp, FLT_exp.
apply Z.le_max_r.
apply Rle_ge, Rmult_le_pos.
apply bpow_ge_0.
now auto with real.
Qed.



Lemma average3_correct_aux2: forall u v, format u -> format v -> u <= v ->
     (0 <= u /\ 0 <= v) \/ (u <= 0 /\ v <= 0) ->
     Rabs (average3 u v -((u+v)/2)) <= 3/2 * ulp_flt ((u+v)/2).
Proof with auto with typeclass_instances.
clear Fx Fy a av x y.
intros x y Fx Fy xLey same_sign.
pose (a:=(x+y)/2); fold a.
assert (T: forall z, Rabs (2*z) = 2* Rabs z).
intros z; rewrite Rabs_mult.
rewrite Rabs_right; try reflexivity.
apply Rle_ge; now auto with real.
destruct xLey as [xLty|xEqy].
(* when x < y *)
assert (B: x <= y) by now left.
assert (K1: a <> 0).
apply Rmult_integral_contrapositive_currified.
2: apply Rgt_not_eq, Rlt_gt; now auto with real.
intros L; case same_sign; intros (L1,L2).
absurd (0 <= x); try assumption.
apply Rlt_not_le.
apply Rlt_le_trans with y; try assumption.
apply Rplus_le_reg_l with x.
rewrite L, Rplus_0_r; assumption.
absurd (y <= 0); try assumption.
apply Rlt_not_le.
apply Rle_lt_trans with x; try assumption.
apply Rplus_le_reg_r with y.
rewrite L, Rplus_0_l; assumption.
(* . initial lemma *)
assert (Y:(Rabs (round_flt (y - x) - (y-x)) <= ulp_flt a)).
apply Rle_trans with (/2*ulp_flt (y-x)).
apply ulp_half_error...
apply Rmult_le_reg_l with 2.
now auto with real.
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
2: apply Rgt_not_eq, Rlt_gt; now auto with real.
apply Rle_trans with (ulp_flt (2*a)).
case same_sign; intros (T1,T2).
apply ulp_le...
apply Rplus_lt_reg_l with x; ring_simplify; assumption.
apply Rle_trans with (2*(a-x)).
right; unfold a; field.
apply Rmult_le_compat_l.
now auto with real.
apply Rplus_le_reg_l with (-a+x); ring_simplify; assumption.
rewrite <- (ulp_opp _ _ (2*a)).
apply ulp_le...
apply Rplus_lt_reg_l with x; ring_simplify; assumption.
apply Rle_trans with (2*(y-a)).
right; unfold a; field.
apply Rle_trans with (2*(-a));[idtac|right; ring].
apply Rmult_le_compat_l.
now auto with real.
apply Rplus_le_reg_l with a; ring_simplify; assumption.
unfold ulp.
replace 2 with (bpow 1) by reflexivity.
rewrite <- bpow_plus.
apply bpow_le.
unfold canonic_exp, FLT_exp.
rewrite Rmult_comm, ln_beta_mult_bpow; trivial.
rewrite <- Z.add_max_distr_l.
replace (ln_beta radix2 a + 1 - prec)%Z with (1 + (ln_beta radix2 a - prec))%Z by ring.
apply Z.max_le_compat_l.
omega.
(* . splitting case of av=0 *)
case (Rle_or_lt (bpow emin) (Rabs a)); intros D.
(* . main proof *)
unfold average3.
case (Rle_or_lt (bpow (prec+emin)) (y-x)); intros H1.
(* .. y-x is big enough: division by 2 is exact *)
cut (round_flt (round_flt (y - x) / 2) = round_flt (y - x) / 2).
intros Z; rewrite Z.
replace (round_flt (x + round_flt (y - x) / 2) - a) with
   ((round_flt (x + round_flt (y - x) / 2) - (x + round_flt (y - x) / 2)) +/2*(round_flt (y - x)-(y-x))).
2: unfold a; field.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (ulp_flt a+/2*ulp_flt a);[idtac|right; field].
apply Rplus_le_compat.
apply Rle_trans with (/2*ulp_flt (x + round_flt (y - x) / 2)).
apply ulp_half_error...
apply Rmult_le_reg_l with 2.
auto with real.
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
2: apply Rgt_not_eq, Rlt_gt; now auto with real.
apply Rle_trans with (2:=FLT_ulp_double _ _ _).
rewrite <- ulp_abs, <- (ulp_abs _ _ (2*a)).
apply ulp_le...
apply Rabs_pos_lt.
intros K2; apply average3_no_underflow_aux3 with x y; trivial.
unfold average3.
rewrite Z, K2, round_0...
replace (x + round_flt (y - x) / 2) with (a+/2*(round_flt (y - x) - (y - x))).
2: unfold a; field.
rewrite (T a).
rewrite Rmult_plus_distr_r, Rmult_1_l.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rplus_le_compat_l.
rewrite Rabs_mult.
rewrite Rabs_right.
2: apply Rle_ge; now auto with real.
apply Rmult_le_reg_l with 2.
now auto with real.
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
2: apply Rgt_not_eq, Rlt_gt; now auto with real.
apply Rle_trans with (1:=Y).
apply Rle_trans with (ulp_flt (2*a)).
rewrite <- ulp_abs, <- (ulp_abs _ _ (2*a)).
apply ulp_le...
now apply Rabs_pos_lt.
rewrite <- (Rmult_1_l (Rabs a)).
rewrite (T a).
apply Rmult_le_compat_r.
apply Rabs_pos.
now auto with real.
rewrite <- (T a).
rewrite <- ulp_abs.
apply FLT_ulp_le_id...
assert (H:generic_format radix2 (FIX_exp emin) (2*a)).
replace (2*a) with (x+y).
2: unfold a; field.
apply generic_format_FIX_FLT,FIX_format_generic in Fx.
apply generic_format_FIX_FLT,FIX_format_generic in Fy.
destruct Fx as (fx,(J1,J2)).
destruct Fy as (fy,(J3,J4)).
apply generic_format_FIX.
exists (Float radix2 (Fnum fx+Fnum fy) emin).
split;[idtac|reflexivity].
rewrite J1,J3; unfold F2R; simpl.
rewrite J2,J4, Z2R_plus; ring.
apply FIX_format_generic in H.
destruct H as ((n,e),(J1,J2)).
rewrite J1; unfold F2R; rewrite J2.
simpl; rewrite Rabs_mult.
pattern (bpow emin) at 1; rewrite <- (Rmult_1_l (bpow emin)).
rewrite (Rabs_right (bpow emin)).
2: apply Rle_ge, bpow_ge_0.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite <- Z2R_abs.
replace 1 with (Z2R 1) by reflexivity.
apply Z2R_le.
assert (0 < Z.abs n)%Z;[idtac|omega].
apply Z.abs_pos.
intros M; apply K1.
apply Rmult_eq_reg_l with 2.
2: apply Rgt_not_eq, Rlt_gt; now auto with real.
rewrite Rmult_0_r, J1,M; unfold F2R; simpl; ring.
rewrite Rabs_mult.
rewrite Rabs_right.
2: apply Rle_ge; auto with real.
apply Rmult_le_compat_l.
now auto with real.
exact Y.
apply round_generic...
apply FLT_format_half...
apply generic_format_round...
apply abs_round_ge_generic...
apply FLT_format_bpow...
unfold Prec_gt_0 in prec_gt_0_; omega.
rewrite Rabs_right; try assumption.
apply Rle_ge; left; apply Rplus_lt_reg_l with x; now ring_simplify.
(* .. y-x is small: subtraction is exact *)
cut ((round_flt (y - x)= (y-x))).
intros Z; rewrite Z.
replace (x + round_flt ((y-x) / 2)) with (a+((round_flt ((y-x) / 2) - (y-x)/2))).
2: unfold a; field.
pose (eps:=(round_flt ((y - x) / 2) - (y - x) / 2)%R); fold eps.
assert (Rabs eps <= /2*bpow emin).
unfold eps.
apply Rle_trans with (1:=ulp_half_error _ _ _ _)...
right; apply f_equal.
unfold ulp; apply f_equal.
apply canonic_exp_FLT_FIX.
apply Rmult_integral_contrapositive_currified.
apply Rgt_not_eq, Rlt_gt.
apply Rplus_lt_reg_l with x; now ring_simplify.
apply Rgt_not_eq, Rlt_gt; now auto with real.
rewrite Zplus_comm; apply Rle_lt_trans with (2:=H1).
rewrite Rabs_right.
apply Rmult_le_reg_l with 2.
now auto with real.
apply Rplus_le_reg_l with (-y+2*x).
apply Rle_trans with x.
right; field.
left; now ring_simplify.
apply Rle_ge, Rmult_le_pos.
apply Rplus_le_reg_l with x; now ring_simplify.
now auto with real.
replace (round_flt (a + eps) - a) with ((round_flt (a+eps) -(a+eps)) + eps) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (/2*ulp_flt (a+eps) + /2*bpow emin).
apply Rplus_le_compat.
apply ulp_half_error...
assumption.
apply Rmult_le_reg_l with 2.
now auto with real.
apply Rle_trans with (ulp_flt (a + eps)+bpow emin).
right; field.
apply Rle_trans with (2*ulp_flt a + ulp_flt a).
2: right; field.
apply Rplus_le_compat.
apply Rle_trans with (2:=FLT_ulp_double _ _ _).
rewrite <- ulp_abs, <- (ulp_abs _ _ (2*a)).
apply ulp_le...
apply Rabs_pos_lt.
intros K2; apply average3_no_underflow_aux3 with x y; trivial.
unfold average3.
rewrite Z.
replace (x + round_flt ((y - x) / 2)) with (a+eps).
rewrite K2, round_0...
unfold a, eps; field.
replace (x + round_flt (y - x) / 2) with (a+/2*(round_flt (y - x) - (y - x))).
2: unfold a; field.
rewrite (T a).
rewrite Rmult_plus_distr_r, Rmult_1_l.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rplus_le_compat_l.
apply Rle_trans with (2:=D).
rewrite <- (Rmult_1_l (bpow emin)).
apply Rle_trans with (1:=H).
apply Rmult_le_compat_r.
apply bpow_ge_0.
pattern 1 at 3; rewrite <- Rinv_1.
apply Rinv_le; now auto with real.
unfold ulp; apply bpow_le.
unfold canonic_exp, FLT_exp.
apply Z.le_max_r.
apply round_generic...
apply FLT_format_plus_small...
now apply generic_format_opp.
rewrite Rabs_right.
now left.
apply Rle_ge, Rplus_le_reg_l with x; now ring_simplify.
(* . when a = bpow emin /2 *)
apply average3_correct_aux; trivial.
split; trivial.
now apply Rabs_pos_lt.
(* . x = y *)
unfold average3,a.
rewrite xEqy.
replace (y-y) with 0 by ring.
rewrite round_0...
unfold Rdiv; rewrite Rmult_0_l.
rewrite round_0...
rewrite Rplus_0_r.
rewrite round_generic...
replace ((y+y)*/2) with y by field.
replace (y-y) with 0 by ring.
rewrite Rabs_R0.
apply Rmult_le_pos.
apply Rmult_le_pos.
apply Fourier_util.Rle_zero_pos_plus1; now auto with real.
now auto with real.
apply bpow_ge_0.
Qed.




(* tight example x=1/2 and y=2^p-1: error is 5/4 ulp *) 

Lemma average3_correct: (0 <= x /\ 0 <= y) \/ (x <= 0 /\ y <= 0) ->
     Rabs (av-a) <= 3/2 * ulp_flt a.
Proof with auto with typeclass_instances.
intros same_sign; case (Rle_or_lt x y); intros H.
now apply average3_correct_aux2.
unfold av, a.
rewrite <- (Ropp_involutive x), <- (Ropp_involutive y).
rewrite average3_symmetry_Ropp.
rewrite <- Rabs_Ropp.
replace (- (- average3 (- x) (- y) - (- - x + - - y) / 2)) with
   (average3 (-x) (-y) - ((-x+-y)/2)).
2: unfold Rdiv; ring.
apply Rle_trans with (3 / 2 * ulp_flt ((- x + - y) / 2)).
apply average3_correct_aux2.
now apply generic_format_opp.
now apply generic_format_opp.
apply Ropp_le_contravar; now left.
rewrite <- Ropp_0; case same_sign; intros (T1,T2).
right; split; now apply Ropp_le_contravar.
left; split; now apply Ropp_le_contravar.
right; apply f_equal.
rewrite <- ulp_opp.
apply f_equal.
unfold Rdiv; ring.
Qed.


(* Lemma average3_symmetry: forall u v, average3 u v = average3 v u.
   is false *)


End av3.

Section average.

Notation bpow e := (bpow radix2 e).

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE). 
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation cexp := (canonic_exp radix2 (FLT_exp emin prec)).

Definition average (x y : R) := 
   let samesign :=  match (Rle_bool 0 x), (Rle_bool 0 y) with
        true  , true   => true
      | false , false => true
      | _,_ => false
   end in
     if samesign then 
       match (Rle_bool (Rabs x) (Rabs y)) with
            true => average3 emin prec x y
          | false => average3 emin prec y x
        end
      else average1 emin prec x y.

Variables x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let a:=(x+y)/2.
Let av:=average x y.

Lemma average_symmetry: forall u v, average u v = average v u.
Proof.
intros u v; unfold average.
case (Rle_bool_spec 0 u); case (Rle_bool_spec 0 v); intros.
rewrite 2!Rabs_right; try apply Rle_ge; try assumption.
case (Rle_bool_spec u v); case (Rle_bool_spec v u); trivial.
intros; replace u with v; trivial; auto with real.
intros H1 H2; contradict H1; auto with real.
apply average1_symmetry.
apply average1_symmetry.
rewrite 2!Rabs_left; try assumption.
case (Rle_bool_spec (-u) (-v)); case (Rle_bool_spec (-v) (-u)); trivial.
intros; replace u with v; trivial; auto with real.
intros H1 H2; contradict H1; auto with real.
Qed.

Lemma average_symmetry_Ropp: forall u v, format u -> format v -> 
  average (-u) (-v) = - average u v.
Proof with auto with typeclass_instances.
(* first: nonnegative u *)
assert (forall u v, 0 <= u -> format u -> format v -> 
  average (-u) (-v) = - average u v).
intros u v Hu Fu Fv; unfold average.
rewrite 2!Rabs_Ropp.
destruct Hu as [Hu|Hu].
 (* 0 < u *)
 rewrite Rle_bool_false.
 2: apply Ropp_lt_cancel.
 2: now rewrite Ropp_involutive, Ropp_0.
 rewrite (Rle_bool_true 0 u); [idtac|now left].
 rewrite Rabs_right.
 2: apply Rle_ge; now left.
 destruct (total_order_T 0 v) as [Hv|Hv];[destruct Hv as [Hv|Hv] |idtac].
 (* . 0 < u and 0 < v *)
   rewrite Rle_bool_false.
   2: apply Ropp_lt_cancel.
   2: now rewrite Ropp_involutive, Ropp_0.
   rewrite (Rle_bool_true 0 v); [idtac|now left].
   rewrite Rabs_right.
   2: apply Rle_ge; now left.
   case (Rle_bool_spec u v);intros.
   apply average3_symmetry_Ropp.
   apply average3_symmetry_Ropp.
 (* . 0 < u and v = 0 *)
   rewrite <- Hv, Ropp_0, Rabs_R0.
   rewrite Rle_bool_true ;[idtac|now right].
   rewrite Rle_bool_false; try exact Hu.
   unfold average1, average3.
   unfold Rminus; rewrite Ropp_0, Rplus_0_l, 2!Rplus_0_r.
   rewrite (round_generic _ _ _ u); trivial.
   rewrite (round_generic _ _ _ (-u)).
   2: now apply generic_format_opp.
   rewrite <- round_NE_opp.
   rewrite <- round_NE_opp.
   rewrite (round_generic _ _ _ (round_flt (-(u/2)))).
   apply f_equal; field.
   apply generic_format_round...
 (* . 0 < u and v < 0 *)
   rewrite Rabs_left; trivial.
   rewrite Rle_bool_true.
   rewrite Rle_bool_false; trivial.
   apply average1_symmetry_Ropp.
   rewrite <- Ropp_0; apply Ropp_le_contravar.
   now left.
 (* u = 0 *)
   rewrite <- Hu, Ropp_0, Rabs_R0.
   rewrite Rle_bool_true.
   2: now right.
   rewrite (Rle_bool_true 0 (Rabs v)).
   2: apply Rabs_pos.
   destruct (total_order_T 0 v) as [Hv|Hv];[destruct Hv as [Hv|Hv] |idtac].
   (* . u=0 and 0 < v *)
   rewrite Rle_bool_false.
   rewrite Rle_bool_true.
   unfold average1, average3.
   unfold Rminus; rewrite Ropp_0, 2!Rplus_0_l, Rplus_0_r.
   rewrite (round_generic _ _ _ v); trivial.
   rewrite (round_generic _ _ _ (-v)).
   2: now apply generic_format_opp.
   rewrite <- round_NE_opp.
   rewrite <- round_NE_opp.
   rewrite (round_generic _ _ _ (round_flt (-(v/2)))).
   apply f_equal; field.
   apply generic_format_round...
   now left.
   rewrite <- Ropp_0; now apply Ropp_lt_contravar.
  (* . u=0 and v=0 *)
   rewrite <- Hv, Ropp_0.
   rewrite Rle_bool_true.
   2: now right.
   unfold average3.
   replace (0-0) with 0 by ring; rewrite round_0...
   unfold Rdiv; rewrite Rmult_0_l, round_0, Rplus_0_l...
  rewrite round_0...
  ring.
  (* . u=0 and v < 0 *)
  rewrite Rle_bool_true.
  rewrite Rle_bool_false.
   unfold average1, average3.
   unfold Rminus; rewrite Ropp_0, 2!Rplus_0_l, Rplus_0_r.
   rewrite (round_generic _ _ _ v); trivial.
   rewrite (round_generic _ _ _ (-v)).
   2: now apply generic_format_opp.
   rewrite <- round_NE_opp.
   rewrite (round_generic _ _ _ (round_flt (-v/2))).
   apply f_equal; field.
   apply generic_format_round...
   exact Hv.
   rewrite <- Ropp_0; apply Ropp_le_contravar; now left.
(* any u *)
intros u v Fu Fv.
case (Rle_or_lt 0 u).
intros Hu; now apply H.
intros Hu.
apply trans_eq with (- average (--u) (--v)).
rewrite (H (-u) (-v)).
ring.
rewrite <- Ropp_0; apply Ropp_le_contravar; now left.
apply generic_format_opp...
apply generic_format_opp...
apply f_equal, f_equal2; ring.
Qed.


Lemma average_same_sign_1: 0 <= a -> 0 <= av.
Proof with auto with typeclass_instances.
intros H; unfold av, average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_same_sign_1...
apply average3_same_sign_1...
now rewrite Rplus_comm.
apply average1_same_sign_1...
apply average1_same_sign_1...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_same_sign_1...
apply average3_same_sign_1...
now rewrite Rplus_comm.
Qed.

Lemma average_same_sign_2: a <= 0-> av <= 0.
Proof with auto with typeclass_instances.
intros H; unfold av, average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_same_sign_2...
apply average3_same_sign_2...
now rewrite Rplus_comm.
apply average1_same_sign_2...
apply average1_same_sign_2...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_same_sign_2...
apply average3_same_sign_2...
now rewrite Rplus_comm.
Qed.

Lemma average_correct: Rabs (av -a) <= 3/2 * ulp_flt a.
Proof with auto with typeclass_instances.
unfold av,a,average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_correct...
rewrite Rplus_comm.
apply average3_correct...
apply average1_correct_weak...
apply average1_correct_weak...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_correct...
right; split; now left.
rewrite Rplus_comm.
apply average3_correct...
right; split; now left.
Qed.

Lemma average_between: Rmin x y <= av <= Rmax x y.
Proof with auto with typeclass_instances.
unfold av,a,average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_between...
rewrite Rmin_comm, Rmax_comm.
apply average3_between...
apply average1_between...
apply average1_between...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_between...
rewrite Rmin_comm, Rmax_comm.
apply average3_between...
Qed.


Lemma average_zero: a = 0 -> av = 0.
Proof with auto with typeclass_instances.
unfold av,a,average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_zero...
apply average3_zero...
now rewrite Rplus_comm.
apply average1_zero...
apply average1_zero...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_zero...
apply average3_zero...
now rewrite Rplus_comm.
Qed.


Lemma average_no_underflow: (bpow emin) <= Rabs a -> av <> 0.
Proof with auto with typeclass_instances.
unfold av,a,average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_no_underflow...
apply average3_no_underflow...
now rewrite Rplus_comm.
apply average1_no_underflow...
apply average1_no_underflow...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_no_underflow...
right; split; now left.
apply average3_no_underflow...
right; split; now left.
now rewrite Rplus_comm.
Qed.



End average.
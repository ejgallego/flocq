Require Import Fcore.
Require Import Fprop_plus_error.
Require Import Fprop_mult_error.

Require Import FmaErr.

Require Import Ftranslate_flocq2Pff.

Open Scope R_scope.

Section ErrFMA.

Variable emin prec : Z.
Hypothesis precisionGe3 : (3 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE).
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).

(** inputs *)
Variable a x y:R.
Hypothesis Fa: format a.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorithm *)
Let r1 := round_flt (a*x+y).
Let u1 := round_flt (a*x).
Let u2 := a*x-u1.
Let alpha1 := round_flt (y+u2).
Let alpha2 := (y+u2)-alpha1.
Let beta1 := round_flt (u1+alpha1).
Let beta2 := (u1+alpha1) - beta1.
Let gamma := round_flt (round_flt (beta1-r1)+beta2).
Let r2 := round_flt (gamma+alpha2).
Let r3 := (gamma+alpha2) -r2.


Lemma precisionNotZero : (1 < prec)%Z.
omega.
Qed.

(** Non-underflow hypotheses *)


(** Theorems *)
Lemma ErrFMA_bounded: format r1 /\ format r2 /\ format r3.
Proof with auto with typeclass_instances.
split.
apply generic_format_round...
split.
apply generic_format_round...
replace (r3) with (-(r2-(gamma+alpha2))) by (unfold r3; ring).
apply generic_format_opp.
apply plus_error...
apply generic_format_round...
replace (alpha2) with (-(alpha1-(y+u2))) by (unfold alpha2; ring).
apply generic_format_opp.
apply plus_error...
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
admit. (* underflow *)
Qed.


Lemma ErrFMA_correct:
   a*x+y = r1+r2+r3.
Proof with auto with typeclass_instances.
replace (r1+r2+r3) with (r1+gamma+alpha2).
2: unfold r3; ring.
assert (J1: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
admit. (* underflow *)
assert (J2: format alpha2).
replace (alpha2) with (-(alpha1-(y+u2))) by (unfold alpha2; ring).
apply generic_format_opp.
apply plus_error...
assert (J3: format beta2).
replace (beta2) with (-(beta1-(u1+alpha1))) by (unfold beta2; ring).
apply generic_format_opp.
apply plus_error...
apply generic_format_round...
apply generic_format_round...
(* values *)
destruct (format_is_pff_format (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero a)
  as (fa,(Hfa,Hfa')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero u2)
  as (fu2,(Hfu2,Hfu2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero alpha2)
  as (fal2,(Hfal2,Hfal2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero beta2)
  as (fbe2,(Hfbe2,Hfbe2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
rewrite <- Hfa, <- Hfx, <- Hfy, <- Hfal2.
(* roundings *)
destruct (round_NE_is_pff_round  (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero (a*x+y))
  as (fr1,(Hfr1, (Hfr1',Hfr1''))).
rewrite make_bound_Emin in Hfr1''; try assumption.
replace (--emin)%Z with emin in Hfr1'' by omega.
destruct (round_NE_is_pff_round  (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero (a*x))
  as (fu1,(Hfu1, (Hfu1',Hfu1''))).
rewrite make_bound_Emin in Hfu1''; try assumption.
replace (--emin)%Z with emin in Hfu1'' by omega.
destruct (round_NE_is_pff_round  (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero (y+u2))
  as (fal1,(Hfal1, (Hfal1',Hfal1''))).
rewrite make_bound_Emin in Hfal1''; try assumption.
replace (--emin)%Z with emin in Hfal1'' by omega.
destruct (round_NE_is_pff_round  (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero (u1+alpha1))
  as (fbe1,(Hfbe1, (Hfbe1',Hfbe1''))).
rewrite make_bound_Emin in Hfbe1''; try assumption.
replace (--emin)%Z with emin in Hfbe1'' by omega.
destruct (round_NE_is_pff_round  (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero (beta1-r1))
  as (ff,(Hff, (Hff',Hff''))).
rewrite make_bound_Emin in Hff''; try assumption.
replace (--emin)%Z with emin in Hff'' by omega.
destruct (round_NE_is_pff_round  (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero (FtoR 2 ff+beta2))
  as (fga,(Hfga, (Hfga',Hfga''))).
rewrite make_bound_Emin in Hfga''; try assumption.
replace (--emin)%Z with emin in Hfga'' by omega.
destruct (round_NE_is_pff_round  (make_bound prec emin)
   prec (make_bound_p prec emin precisionNotZero) precisionNotZero (gamma+alpha2))
  as (fr2,(Hfr2, (Hfr2',Hfr2''))).
rewrite make_bound_Emin in Hfr2''; try assumption.
replace (--emin)%Z with emin in Hfr2'' by omega.
unfold r1; rewrite <- Hfr1''.
unfold gamma; rewrite <- Hff'', <- Hfga''.
(* *)
apply FmaErr_Even with (make_bound prec emin) (Z.abs_nat prec) fu1 fu2 fal1 fbe1 fbe2 ff;
  try assumption.
omega.
apply make_bound_p; omega.
replace 3%nat with (Z.abs_nat 3).
apply Zabs_nat_le; omega.
now unfold Z.abs_nat, Pos.to_nat.
now exists 1%Z.

admit. (* underflow *)
admit. (* underflow *)
admit. (* underflow *)
admit. (* underflow *)
admit. (* underflow *)

rewrite Hfa, Hfx; apply Hfu1'.
now rewrite Hfu2, Hfa, Hfx, Hfu1''.
rewrite Hfy, Hfu2; apply Hfal1'.
now rewrite Hfal2, Hfy, Hfu2, Hfal1''.
now rewrite Hfbe2, Hfu1'', Hfal1'', Hfbe1''.
rewrite Hfbe1'', Hfr1''; apply Hff'.
rewrite Hfbe2; apply Hfga'.
rewrite Hfa, Hfx, Hfy; apply Hfr1'.
rewrite Hfu1'', Hfal1''; apply Hfbe1'.
Qed.



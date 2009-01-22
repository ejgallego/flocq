Require Import Flocq_Raux.

Section Def.

Record float (beta : radix) := Float { Fnum : Z ; Fexp : Z }.

Implicit Arguments Fnum [[beta]].
Implicit Arguments Fexp [[beta]].

Variable beta : radix.

Definition F2R (f : float beta) :=
  (Z2R (Fnum f) * epow beta (Fexp f))%R.

(* A rounding mode will be a function, ie a R -> R                         *)
(* It will then have to satisfy a number of properties on a given domain D *)
(*    The domain will be used to formalize Overflow, flush to zero...      *)


Definition MonotoneP (rnd : R -> R) :=
  forall x y : R,
  (x <= y)%R -> (rnd x <= rnd y)%R.


Definition IdempotentP (F : R -> Prop) (rnd : R -> R) :=
    (forall x : R, F (rnd x))
        /\ (forall x : R, F x -> rnd x = x). 

Definition Rounding_for_Format (F : R -> Prop) (rnd : R -> R) :=
   MonotoneP rnd /\ IdempotentP F rnd.

(* unbounded floating-point format *)
Definition FLX_format (prec : Z) (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Zabs (Fnum f) < Zpower (radix_val beta) prec)%Z.

(* floating-point format with gradual underflow *)
Definition FLT_format (emin prec : Z) (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Zabs (Fnum f) < Zpower (radix_val beta) prec)%Z /\ (emin <= Fexp f)%Z.

(* fixed-point format *)
Definition FIX_format (emin : Z) (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Fexp f = emin)%Z.

Definition FLX_RoundingModeP (prec : Z) (rnd : R -> R):=
  Rounding_for_Format (FLX_format prec) rnd.

Definition FLT_RoundingModeP (emin prec : Z) (rnd : R -> R):=
  Rounding_for_Format (FLT_format emin prec) rnd.

Definition FIX_RoundingModeP (emin : Z) (rnd : R -> R):=
  Rounding_for_Format (FIX_format emin) rnd.

End Def.

Implicit Arguments Fnum [[beta]].
Implicit Arguments Fexp [[beta]].
Implicit Arguments F2R [[beta]].

Section RND.

(* property of being a rounding toward -inf *)
Definition Rnd_DN_pt (F : R -> Prop) (x f : R) :=
  F f /\ (f <= x)%R /\
  forall g : R, F g -> (g <= x)%R -> (g <= f)%R.

Definition Rnd_DN (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_DN_pt F x (rnd x).

(* property of being a rounding toward +inf *)
Definition Rnd_UP_pt (F : R -> Prop) (x f : R) :=
  F f /\ (x <= f)%R /\
  forall g : R, F g -> (x <= g)%R -> (f <= g)%R.

Definition Rnd_UP (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_UP_pt F x (rnd x).

(* property of being a rounding toward zero *)
Definition Rnd_ZR_pt (F : R -> Prop) (x f : R) :=
  ( (0 <= x)%R -> Rnd_DN_pt F x f ) /\
  ( (x <= 0)%R -> Rnd_UP_pt F x f ).

Definition Rnd_ZR (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_ZR_pt F x (rnd x).

Theorem toto :
  forall (F : R -> Prop) (rnd: R-> R), 
  Rnd_ZR F rnd ->
  forall x : R,  (Rabs (rnd x) <= Rabs x)%R.
Proof.
intros F rnd H x.
assert (F 0%R).
replace 0%R with (rnd 0%R).
eapply H.
apply Rle_refl.
destruct (H 0%R) as (H1, H2).
apply Rle_antisym.
apply H1.
apply Rle_refl.
apply H2.
apply Rle_refl.
(* . *)
destruct (Rle_or_lt 0 x).
(* positive *)
rewrite Rabs_right.
rewrite Rabs_right; auto with real.
now apply (proj1 (H x)).
apply Rle_ge.
now apply (proj1 (H x)).
(* negative *)
rewrite Rabs_left1.
rewrite Rabs_left1 ; auto with real.
apply Ropp_le_contravar.
apply (proj2 (H x)).
auto with real.
apply (proj2 (H x)) ; auto with real.
Qed.

(* property of being a rounding to nearest *)
Definition Rnd_N_pt (F : R -> Prop) (x f : R) :=
  F f /\
  forall g : R, F g -> (Rabs (f - x) <= Rabs (g - x))%R.

Definition Rnd_N (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_N_pt F x (rnd x).

Definition Rnd_NA_pt (F : R -> Prop) (x f : R) :=
  Rnd_N_pt F x f /\
  forall f2 : R, Rnd_N_pt F x f2 ->
  (Rabs f2 <= Rabs f)%R.

Definition Rnd_NA (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_NA_pt F x (rnd x).

End RND.

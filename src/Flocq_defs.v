Require Import Flocq_Raux.

Section Def.

Record float (beta : radix) := Float { Fnum : Z ; Fexp : Z }.

Implicit Arguments Fnum [[beta]].
Implicit Arguments Fexp [[beta]].

Variable beta : radix.

Definition F2R (f : float beta) :=
  (Z2R (Fnum f) * bpow beta (Fexp f))%R.

Definition MonotoneP (rnd : R -> R) :=
  forall x y : R,
  (x <= y)%R -> (rnd x <= rnd y)%R.

Definition IdempotentP (F : R -> Prop) (rnd : R -> R) :=
    (forall x : R, F (rnd x))
        /\ (forall x : R, F x -> rnd x = x). 

Definition Rounding_for_Format (F : R -> Prop) (rnd : R -> R) :=
   MonotoneP rnd /\ IdempotentP F rnd.

Definition rounding_pred_total (P : R -> R -> Prop) :=
  forall x, exists f, P x f.

Definition rounding_pred_monotone (P : R -> R -> Prop) :=
  forall x y f g, P x f -> P y g -> (x <= y)%R -> (f <= g)%R.

Definition rounding_pred (P : R -> R -> Prop) :=
  rounding_pred_total P /\
  rounding_pred_monotone P.

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

(* property of being a rounding to nearest *)
Definition Rnd_N_pt (F : R -> Prop) (x f : R) :=
  F f /\
  forall g : R, F g -> (Rabs (f - x) <= Rabs (g - x))%R.

Definition Rnd_N (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_N_pt F x (rnd x).

Definition Rnd_NG_pt (F : R -> Prop) (P : R -> R -> Prop) (x f : R) :=
  Rnd_N_pt F x f /\
  ( P x f \/ forall f2 : R, Rnd_N_pt F x f2 -> f2 = f ).

Definition Rnd_NG (F : R -> Prop) (P : R -> R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_NG_pt F P x (rnd x).

Definition Rnd_NA_pt (F : R -> Prop) (x f : R) :=
  Rnd_N_pt F x f /\
  forall f2 : R, Rnd_N_pt F x f2 -> (Rabs f2 <= Rabs f)%R.

Definition Rnd_NA (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_NA_pt F x (rnd x).

End RND.

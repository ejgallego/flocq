Require Import Flocq_Raux.

Section Def.

Variable beta: radix.

Notation bpow := (epow beta).

Record float (beta : radix) := Float { Fnum : Z ; Fexp : Z }.
Implicit Arguments Fnum [[beta]].
Implicit Arguments Fexp [[beta]].

Definition F2R {beta : radix} (f : float beta) :=
  (Z2R (Fnum f) * bpow (Fexp f))%R.

(* A rounding mode will be a function, ie a R -> R                         *)
(* It will then have to satisfy a number of properties on a given domain D *)
(*    The domain will be used to formalize Overflow, flush to zero...      *)


Definition MonotoneP (D: R -> Prop) (rnd : R -> R) :=
  forall x y: R, D x -> D y ->
     (x <= y)%R -> (rnd x <= rnd y)%R.

(*
Definition InvolutiveP (D: R -> Prop) (rnd : R -> R) :=
  forall x : R, D x -> rnd (rnd x) = rnd x.
*)

Definition Rounding_for_Format (D:R->Prop) (F : R -> Prop) (rnd : R->R) :=
   MonotoneP D rnd
           /\ (forall x : R, D x -> F (rnd x))
           /\ (forall x : R, D x -> F x -> rnd x = x).


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

Definition R_whole := fun _:R => True.

Definition FLX_RoundingModeP (prec : Z) (rnd : R -> R):=
  Rounding_for_Format R_whole (FLX_format prec) rnd.

Definition FLT_RoundingModeP (emin prec : Z) (rnd : R -> R):=
  Rounding_for_Format R_whole (FLT_format emin prec) rnd.

Definition FIX_RoundingModeP (emin : Z) (rnd : R -> R):=
  Rounding_for_Format R_whole (FIX_format emin) rnd.

End Def.

Section RND.

(* property of being a rounding toward -inf *)
Definition Rnd_DN (D : R -> Prop) (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, D x ->  
  D (rnd x) /\ F (rnd x) /\ (rnd x <= x)%R /\
  forall g : R, F g -> (g <= x)%R -> (g <= rnd x)%R.


(* property of being a rounding toward +inf *)
Definition Rnd_UP (D : R -> Prop) (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, D x ->
  D (rnd x) /\ F (rnd x) /\ (x <= rnd x)%R /\
  forall g : R, F g -> (x <= g)%R -> (rnd x <= g)%R.

(* property of being a rounding toward zero *)
Definition Rnd_ZR (D:R->Prop) (F : R -> Prop) (rnd : R->R) :=
     Rnd_DN (fun x => D x /\ (0 <= x)%R) F rnd
  /\ Rnd_UP (fun x => D x /\ (x <= 0)%R) F rnd.
      

Theorem toto: forall (F : R -> Prop) (rnd: R-> R), 
   Rnd_ZR R_whole F rnd ->
   forall (x:R),  (Rabs (rnd x) <= Rabs x)%R.
intros F rnd (H1,H2).
assert (F 0%R).
replace 0%R with (rnd 0%R).
eapply H1 ; repeat split ; apply Rle_refl.
apply Rle_antisym.
now destruct (H1 0%R); repeat split ; auto with real.
now destruct (H2 0%R); repeat split ; auto with real.
intros x.
destruct (Rle_or_lt 0 x).
(* positive *)
rewrite Rabs_right.
rewrite Rabs_right; auto with real.
eapply H1.
now split.
apply Rle_ge.
eapply H1.
now split.
exact H.
exact H0.
(* negative *)
rewrite Rabs_left1.
rewrite Rabs_left1 ; auto with real.
apply Ropp_le_contravar.
eapply H2.
repeat split.
auto with real.
eapply H2.
repeat split.
auto with real.
exact H.
auto with real.
Qed.





(* property of being a rounding to nearest *)
Definition Rnd_N (D:R->Prop) (F : R -> Prop) (rnd : R->R) :=
  forall x:R, D x ->  
     F (rnd x) /\
     forall g : R, F g -> (Rabs (rnd x-x) <= Rabs (g-x))%R.


Definition Rnd_NA (D:R->Prop) (F : R -> Prop) (rnd : R->R) :=
   Rnd_N D F rnd /\
    forall (x y:R), D x -> F y ->
      (forall g : R, F g -> (Rabs (y-x) <= Rabs (g-x))%R)
          -> (Rabs y <= Rabs (rnd x))%R.



End RND.

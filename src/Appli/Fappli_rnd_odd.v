Require Import Fcore.

Definition Zrnd_odd x :=  match Rcompare x (Z2R (Zfloor x))  with
  | Eq => Zfloor x
  | _  => match (Zeven (Zfloor x)) with
      | true => Zceil x
      | false => Zfloor x
     end
  end.


Lemma Zrnd_odd_Zodd: forall x, x <> (Z2R (Zfloor x)) ->
  (Zeven (Zrnd_odd x)) = false.
Proof.
intros x Hx; unfold Zrnd_odd.
destruct (Rcompare_spec  x (Z2R (Zfloor x))).
case_eq (Zeven (Zfloor x)).
contradict H; apply Rle_not_lt.
apply Zfloor_lb.
trivial.
now contradict H.
case_eq (Zeven (Zfloor x)).
(* difficult case *)
intros H'.
rewrite Zceil_floor_neq.
rewrite Zeven_plus, H'.
reflexivity.
now apply sym_not_eq.
trivial.
Qed.

Section Fcore_rnd_odd.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Context { valid_exp : Valid_exp fexp }.
Context { exists_NE_ : Exists_NE beta fexp }.

Notation format := (generic_format beta fexp).
Notation canonic := (canonic beta fexp).





Definition Rnd_DN_pt (F : R -> Prop) (x f : R) :=
  F f /\ (f <= x)%R /\
  forall g : R, F g -> (g <= x)%R -> (g <= f)%R.

Definition Rnd_DN (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_DN_pt F x (rnd x).

Definition NE_prop (_ : R) f :=
  exists g : float beta, f = F2R g /\ canonic g /\ Zeven (Fnum g) = true.

Definition Rnd_NE_pt :=
  Rnd_NG_pt format NE_prop.



Theorem Rnd_NE_pt_total :
  round_pred_total Rnd_NE_pt.


Theorem Rnd_NE_pt_monotone :
  round_pred_monotone Rnd_NE_pt.

  
Theorem Rnd_NE_pt_round :
  round_pred Rnd_NE_pt.
split.
apply Rnd_NE_pt_total.
apply Rnd_NE_pt_monotone.
Qed.

Lemma round_NE_pt_pos :
  forall x,
  (0 < x)%R ->
  Rnd_NE_pt x (round beta fexp ZnearestE x).

Theorem round_NE_opp :
  forall x,
  round beta fexp ZnearestE (-x) = (- round beta fexp ZnearestE x)%R.
Proof.
Lemma round_NE_abs:
  forall x : R,
  round beta fexp ZnearestE (Rabs x) = Rabs (round beta fexp ZnearestE x).
Proof with auto with typeclass_instances.
Theorem round_NE_pt :
  forall x,
  Rnd_NE_pt x (round beta fexp ZnearestE x).

--------------------------------------------
Definition To_Odd (r : R) (p : float) :=
  Fbounded b p /\ 
  ((r=p) \/
  (((isMin b radix r p) \/ (isMax b radix r p)) /\ (FNodd b radix precision p))).

Theorem ClosestStrictPred: forall (f:float) (z:R), 
  (Fcanonic radix b f) -> (0 < f)%R -> 
    (-Fulp b radix p (FNPred b radix p f) < 2%nat *(z - f) < Fulp b radix p f)%R
 ->  Closest b radix z f /\
    (forall q : float, Closest b radix z q -> FtoR radix q = FtoR radix f).


Theorem ClosestStrictPos: forall (f:float) (z:R), 
  (Fcanonic radix b f) -> (0 < f)%R -> Fnum f <> nNormMin radix p
 -> (2%nat * Rabs (z - f) < Fulp b radix p f)%R
 ->  Closest b radix z f /\
    (forall q : float, Closest b radix z q -> FtoR radix q = FtoR radix f).


Theorem ClosestStrict: forall (f:float) (z0:R), 
  (Fcanonic radix b f) -> Zabs (Fnum f) <> nNormMin radix p
 -> (2%nat * Rabs (z0 - f) < Fulp b radix p f)%R
 ->  Closest b radix z0 f /\
    (forall q : float, Closest b radix z0 q -> FtoR radix q = FtoR radix f).

Hypotheses By : (Fbounded be y).
Hypotheses Bz : (Fbounded b  z).
Hypotheses Bv : (Fbounded b  v).
Hypotheses Cv : (Fcanonic radix b v).

Hypotheses ydef : (To_Odd      be radix (plus p k) x y).
Hypotheses zdef : (EvenClosest b  radix p          y z).
Hypotheses vdef : (EvenClosest b  radix p          x v).

Hypotheses rangeext: (-(dExp be) <= (Zpred (Zpred (-(dExp b)))))%Z.

Hypotheses H:(Fnum v=(nNormMin radix p))%Z.
Hypotheses H':(x<>y)%R.
Hypotheses H1: (0 <= v)%R.


Theorem To_Odd_Even_is_Even_nNormMin: EvenClosest b radix p y v.


Let radix := 2%Z.
Let FtoRradix := FtoR radix.
Coercion FtoRradix : float >-> R.

Hypotheses pGreaterThanOne :  (lt (S O) p).
Hypotheses kGreaterThanOne :  (lt (S O) k).
Hypotheses pGivesBound   :  (Zpos (vNum b)) = (Zpower_nat radix p).
Hypotheses pkGivesBounde :  (Zpos (vNum be)) = (Zpower_nat radix (plus p k)).


Hypotheses By : (Fbounded be y).
Hypotheses Bz : (Fbounded b  z).
Hypotheses Bv : (Fbounded b  v).
Hypotheses Cv : (Fcanonic radix b v).

Hypotheses ydef : (To_Odd      be radix (plus p k) x y).
Hypotheses zdef : (EvenClosest b  radix p          y z).
Hypotheses vdef : (EvenClosest b  radix p          x v).

Hypotheses rangeext: (-(dExp be) <= (Zpred (Zpred (-(dExp b)))))%Z.


Theorem To_Odd_Even_is_Even: ((FtoRradix v)=(FtoRradix z))%R.



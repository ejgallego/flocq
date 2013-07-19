Require Import Fcore.

Definition Zrnd_odd x :=  match Req_EM_T x (Z2R (Zfloor x))  with
  | left _   => Zfloor x
  | right _  => match (Zeven (Zfloor x)) with
      | true => Zceil x
      | false => Zfloor x
     end
  end. 



Global Instance valid_rnd_odd : Valid_rnd Zrnd_odd.
Proof.
split.
(* . *)
intros x y Hxy.
assert (Zfloor x <= Zrnd_odd y)%Z.
(* .. *)
apply Zle_trans with (Zfloor y).
now apply Zfloor_le.
unfold Zrnd_odd; destruct (Req_EM_T  y (Z2R (Zfloor y))).
now apply Zle_refl.
case (Zeven (Zfloor y)).
apply le_Z2R.
apply Rle_trans with y.
apply Zfloor_lb.
apply Zceil_ub.
now apply Zle_refl.
unfold Zrnd_odd at 1.
(* . *)
destruct (Req_EM_T  x (Z2R (Zfloor x))) as [Hx|Hx].
(* .. *)
apply H.
(* .. *)
case_eq (Zeven (Zfloor x)); intros Hx2.
2: apply H.
unfold Zrnd_odd; destruct (Req_EM_T  y (Z2R (Zfloor y))) as [Hy|Hy].
apply Zceil_glb.
now rewrite <- Hy.
case_eq (Zeven (Zfloor y)); intros Hy2.
now apply Zceil_le.
apply Zceil_glb.
assert (H0:(Zfloor x <= Zfloor y)%Z) by now apply Zfloor_le.
case (Zle_lt_or_eq _ _  H0); intros H1.
apply Rle_trans with (1:=Zceil_ub _).
rewrite Zceil_floor_neq.
apply Z2R_le; omega.
now apply sym_not_eq.
contradict Hy2.
rewrite <- H1, Hx2; discriminate.
(* . *)
intros n; unfold Zrnd_odd.
rewrite Zfloor_Z2R, Zceil_Z2R.
destruct (Req_EM_T  (Z2R n) (Z2R n)); trivial.
case (Zeven n); trivial.
Qed.



Lemma Zrnd_odd_Zodd: forall x, x <> (Z2R (Zfloor x)) ->
  (Zeven (Zrnd_odd x)) = false.
Proof.
intros x Hx; unfold Zrnd_odd.
destruct (Req_EM_T  x (Z2R (Zfloor x))) as [H|H].
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
Notation cexp := (canonic_exp beta fexp).


Definition Rnd_odd_pt (x f : R) :=
  format f /\ ((f = x)%R \/
    ((Rnd_DN_pt format  f x \/ Rnd_UP_pt format f x) /\
    exists g : float beta, f = F2R g /\ canonic g /\ Zeven (Fnum g) = false)).

Definition Rnd_odd (rnd : R -> R) :=
  forall x : R, Rnd_odd_pt x (rnd x).


Lemma Rmult_neq_reg_r: forall  r1 r2 r3:R, (r2 * r1 <> r3 * r1)%R -> r2 <> r3.
intros r1 r2 r3 H1 H2.
apply H1; rewrite H2; ring.
Qed.



Lemma round_odd_pt :
  forall x,
  Rnd_odd_pt x (round beta fexp Zrnd_odd x).
Proof with auto with typeclass_instances.
intros x.
generalize (generic_format_round beta fexp Zrnd_odd x).
set (o:=round beta fexp Zrnd_odd x).
intros Ho.
split.
assumption.
case (Req_dec o x); intros Hx.
now left.
right.
split.

admit. (* très facile *)

BLOP.

generalize (generic_format_round beta fexp Zfloor x).
set (d:=round beta fexp Zfloor x).
unfold generic_format.
set (ed := canonic_exp beta fexp d).
set (md := Ztrunc (scaled_mantissa beta fexp d)).
intros Hd1.
case_eq (Zeven md) ; [ intros He | intros Hee ].

admit.


exists (Float beta md ed).
unfold Fcore_generic_fmt.canonic.
rewrite <- Hd1.
repeat split; try assumption.
unfold d, o, Zrnd_odd, round.
apply f_equal; apply f_equal2; try reflexivity.
fold md.


SearchRewrite (round _ _ _ _).




left.
generalize (proj1 Hu).
unfold generic_format.
set (eu := canonic_exp beta fexp u).
set (mu := Ztrunc (scaled_mantissa beta fexp u)).
intros Hu1.
rewrite Hu1.
eexists ; repeat split.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hu1.
rewrite (DN_UP_parity_generic x (Float beta md ed) (Float beta mu eu)).
simpl.
now rewrite Ho.
exact Hf.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hd1.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hu1.
rewrite <- Hd1.
apply Rnd_DN_pt_unicity with (1 := Hd).
now apply round_DN_pt.
rewrite <- Hu1.
apply Rnd_UP_pt_unicity with (1 := Hu).
now apply round_UP_pt.
























reflexivity.

[reflexivity|split].
reflexivity.
simpl.
apply Zrnd_odd_Zodd.
apply Rmult_neq_reg_r with (bpow (canonic_exp beta fexp x)).
rewrite scaled_mantissa_mult_bpow.
apply sym_not_eq.
replace ((Z2R (Zfloor (scaled_mantissa beta fexp x)) * bpow (canonic_exp beta fexp x)))%R with
  (round beta fexp Zfloor x) by reflexivity.
intros H; apply Hx; clear Hx.
unfold round, Zrnd_odd in *.
case (Req_EM_T (scaled_mantissa beta fexp x)
               (Z2R (Zfloor (scaled_mantissa beta fexp x)))); intros Hx.
assumption.
absurd (scaled_mantissa beta fexp x =
     Z2R (Zfloor (scaled_mantissa beta fexp x))).
assumption.
unfold scaled_mantissa at 1.
rewrite <- H at 1.
unfold F2R; simpl.
rewrite Rmult_assoc, <- bpow_plus.
ring_simplify (canonic_exp beta fexp x + - canonic_exp beta fexp x)%Z.
apply Rmult_1_r.
Qed.




Theorem Rnd_NG_pt_unicity :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  Rnd_NG_pt_unicity_prop F P ->
  forall x f1 f2 : R,
  Rnd_NG_pt F P x f1 -> Rnd_NG_pt F P x f2 ->
  f1 = f2.

Theorem Rnd_NG_pt_monotone :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  Rnd_NG_pt_unicity_prop F P ->
  round_pred_monotone (Rnd_NG_pt F P).

Theorem Rnd_NG_pt_refl :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  forall x, F x -> Rnd_NG_pt F P x x.
Proof.
intros F P x Hx.
split.
now apply Rnd_N_pt_refl.
right.
intros f2 Hf2.
now apply Rnd_N_pt_idempotent with F.
Qed.

Theorem Rnd_NG_pt_sym :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  ( forall x, F x -> F (-x) ) ->
  ( forall x f, P x f -> P (-x) (-f) ) ->
  forall x f : R,
  Rnd_NG_pt F P (-x) (-f) -> Rnd_NG_pt F P x f.

Theorem satisfies_any_imp_UP :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_UP_pt F).

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



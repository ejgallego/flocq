Require Import Fcore.
Require Import Fcalc_ops.

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
    ((Rnd_DN_pt format x f \/ Rnd_UP_pt format x f) /\
    exists g : float beta, f = F2R g /\ canonic g /\ Zeven (Fnum g) = false)).

Definition Rnd_odd (rnd : R -> R) :=
  forall x : R, Rnd_odd_pt x (rnd x).

(*
Lemma Rmult_neq_reg_r: forall  r1 r2 r3:R, (r2 * r1 <> r3 * r1)%R -> r2 <> r3.
intros r1 r2 r3 H1 H2.
apply H1; rewrite H2; ring.
Qed.*)

Lemma Rmult_neq_compat_r: forall  r1 r2 r3:R, (r1 <> 0)%R -> (r2 <> r3)%R 
   -> (r2 *r1 <> r3*r1)%R.
intros r1 r2 r3 H H1 H2.
now apply H1, Rmult_eq_reg_r with r1. 
Qed.


Theorem Rnd_odd_pt_sym :   forall x f : R,
  Rnd_odd_pt (-x) (-f) -> Rnd_odd_pt x f.
Proof with auto with typeclass_instances.
intros x f (H1,H2).
split.
replace f with (-(-f))%R by ring.
now apply generic_format_opp.
destruct H2.
left.
replace f with (-(-f))%R by ring.
rewrite H; ring.
right.
destruct H as (H2,(g,(Hg1,(Hg2,Hg3)))).
split.
destruct H2.
right.
replace f with (-(-f))%R by ring.
replace x with (-(-x))%R by ring.
apply Rnd_DN_UP_pt_sym...
apply generic_format_opp.
left.
replace f with (-(-f))%R by ring.
replace x with (-(-x))%R by ring.
apply Rnd_UP_DN_pt_sym...
apply generic_format_opp.
exists (Float beta (-Fnum g) (Fexp g)).
split.
rewrite F2R_Zopp.
replace f with (-(-f))%R by ring.
rewrite Hg1; reflexivity.
split.
now apply canonic_opp.
simpl.
now rewrite Zeven_opp.
Qed.


Theorem round_odd_opp :
  forall x,
  (round beta fexp Zrnd_odd  (-x) = (- round beta fexp Zrnd_odd x))%R.
Proof.
intros x; unfold round.
rewrite <- F2R_Zopp.
unfold F2R; simpl.
apply f_equal2; apply f_equal.
rewrite scaled_mantissa_opp.
generalize (scaled_mantissa beta fexp x); intros r.
unfold Zrnd_odd.
case (Req_EM_T (- r) (Z2R (Zfloor (- r)))).
case (Req_EM_T r (Z2R (Zfloor r))).
intros Y1 Y2.
apply eq_Z2R.
now rewrite Z2R_opp, <- Y1, <-Y2.
intros Y1 Y2.
absurd (r=Z2R (Zfloor r)); trivial.
pattern r at 2; replace r with (-(-r))%R by ring.
rewrite Y2, <- Z2R_opp.
rewrite Zfloor_Z2R.
rewrite Z2R_opp, <- Y2.
ring.
case (Req_EM_T r (Z2R (Zfloor r))).
intros Y1 Y2.
absurd (-r=Z2R (Zfloor (-r)))%R; trivial.
pattern r at 2; rewrite Y1.
rewrite <- Z2R_opp, Zfloor_Z2R.
now rewrite Z2R_opp, <- Y1.
intros Y1 Y2.
unfold Zceil; rewrite Ropp_involutive.
SearchAbout Zceil.
replace  (Zeven (Zfloor (- r))) with (negb (Zeven (Zfloor r))).
case (Zeven (Zfloor r));  simpl; ring.
apply trans_eq with (Zeven (Zceil r)).
rewrite Zceil_floor_neq.
rewrite Zeven_plus.
simpl; reflexivity.
now apply sym_not_eq.
rewrite <- (Zeven_opp (Zfloor (- r))).
reflexivity.
apply canonic_exp_opp.
Qed.



Theorem round_odd_pt :
  forall x,
  Rnd_odd_pt x (round beta fexp Zrnd_odd x).
Proof with auto with typeclass_instances.
cut (forall x : R, (0 < x)%R -> Rnd_odd_pt x (round beta fexp Zrnd_odd x)).
intros H x; case (Rle_or_lt 0 x).
intros H1; destruct H1.
now apply H.
rewrite <- H0.
rewrite round_0...
split.
apply generic_format_0.
now left.
intros Hx; apply Rnd_odd_pt_sym.
rewrite <- round_odd_opp.
apply H.
auto with real.
(* *)
intros x Hxp.
generalize (generic_format_round beta fexp Zrnd_odd x).
set (o:=round beta fexp Zrnd_odd x).
intros Ho.
split.
assumption.
(* *)
case (Req_dec o x); intros Hx.
now left.
right.
assert (o=round beta fexp Zfloor x \/ o=round beta fexp Zceil x).
unfold o, round, F2R;simpl.
case (Zrnd_DN_or_UP Zrnd_odd  (scaled_mantissa beta fexp x))...
intros H; rewrite H; now left.
intros H; rewrite H; now right.
split.
destruct H; rewrite H.
left; apply round_DN_pt...
right; apply round_UP_pt...
(* *)
unfold o, Zrnd_odd, round.
case (Req_EM_T (scaled_mantissa beta fexp x)
     (Z2R (Zfloor (scaled_mantissa beta fexp x)))).
intros T.
absurd (o=x); trivial.
apply round_generic...
unfold generic_format, F2R; simpl.
rewrite <- (scaled_mantissa_mult_bpow beta fexp) at 1.
apply f_equal2; trivial; rewrite T at 1.
apply f_equal, sym_eq, Ztrunc_floor.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
intros L.
case_eq (Zeven (Zfloor (scaled_mantissa beta fexp x))).
(* . *)
generalize (generic_format_round beta fexp Zceil x).
unfold generic_format.
set (f:=round beta fexp Zceil x).
set (ef := canonic_exp beta fexp f).
set (mf := Ztrunc (scaled_mantissa beta fexp f)).
exists (Float beta mf ef).
unfold Fcore_generic_fmt.canonic.
rewrite <- H0.
repeat split; try assumption.
apply trans_eq with (negb (Zeven (Zfloor (scaled_mantissa beta fexp x)))).
2: rewrite H1; reflexivity.
apply trans_eq with (negb (Zeven (Fnum 
  (Float beta  (Zfloor (scaled_mantissa beta fexp x)) (cexp x))))).
2: reflexivity.
case (Rle_lt_or_eq_dec 0 (round beta fexp Zfloor x)).
rewrite <- round_0 with beta fexp Zfloor...
apply round_le...
now left.
intros Y.
generalize (DN_UP_parity_generic beta fexp)...
unfold DN_UP_parity_prop.
intros T; apply T with x; clear T.
unfold generic_format.
rewrite <- (scaled_mantissa_mult_bpow beta fexp x) at 1.
unfold F2R; simpl.
apply Rmult_neq_compat_r.
apply Rgt_not_eq, bpow_gt_0.
rewrite Ztrunc_floor.
assumption.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
unfold Fcore_generic_fmt.canonic.
simpl.
apply sym_eq, canonic_exp_DN...
unfold Fcore_generic_fmt.canonic.
rewrite <- H0; reflexivity.
reflexivity.
apply trans_eq with (round beta fexp Ztrunc (round beta fexp Zceil x)).
reflexivity.
apply round_generic...
intros Y.
replace  (Fnum {| Fnum := Zfloor (scaled_mantissa beta fexp x); Fexp := cexp x |})
   with (Fnum (Float beta 0 (fexp (ln_beta beta 0)))).
generalize (DN_UP_parity_generic beta fexp)...
unfold DN_UP_parity_prop.
intros T; apply T with x; clear T.
unfold generic_format.
rewrite <- (scaled_mantissa_mult_bpow beta fexp x) at 1.
unfold F2R; simpl.
apply Rmult_neq_compat_r.
apply Rgt_not_eq, bpow_gt_0.
rewrite Ztrunc_floor.
assumption.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
apply canonic_0.
unfold Fcore_generic_fmt.canonic.
rewrite <- H0; reflexivity.
rewrite <- Y; unfold F2R; simpl; ring.
apply trans_eq with (round beta fexp Ztrunc (round beta fexp Zceil x)).
reflexivity.
apply round_generic...
simpl.
apply eq_Z2R, Rmult_eq_reg_r with (bpow (cexp x)).
unfold round, F2R in Y; simpl in Y; rewrite <- Y.
simpl; ring.
apply Rgt_not_eq, bpow_gt_0.
(* . *)
intros Y.
case (Rle_lt_or_eq_dec 0 (round beta fexp Zfloor x)).
rewrite <- round_0 with beta fexp Zfloor...
apply round_le...
now left.
intros Hrx.
set (ef := canonic_exp beta fexp x).
set (mf := Zfloor (scaled_mantissa beta fexp x)).
exists (Float beta mf ef).
unfold Fcore_generic_fmt.canonic.
repeat split; try assumption.
simpl.
apply trans_eq with (cexp (round beta fexp Zfloor x )).
apply sym_eq, canonic_exp_DN...
reflexivity.
intros Hrx; contradict Y.
replace (Zfloor (scaled_mantissa beta fexp x)) with 0%Z.
simpl; discriminate.
apply eq_Z2R, Rmult_eq_reg_r with (bpow (cexp x)).
unfold round, F2R in Hrx; simpl in Hrx; rewrite <- Hrx.
simpl; ring.
apply Rgt_not_eq, bpow_gt_0.
Qed.

End Fcore_rnd_odd.

Section Odd_prop.

Variable beta : radix.
Hypothesis Even_beta: Zeven (radix_val beta)=true.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Variable fexpe : Z -> Z.

Context { valid_exp : Valid_exp fexp }.
(*Context { exists_NE_ : Exists_NE beta fexp }.*)
Context { monotone_exp : Monotone_exp fexp }.

Context { valid_expe : Valid_exp fexpe }.
Context { exists_NE_e : Exists_NE beta fexpe }.

Hypothesis fexpe_fexp: forall e, (fexpe e <= fexp e -2)%Z. (*  ??? *)


Lemma generic_format_F2R_2: forall c, forall (x:R) (f:float beta),
       x = F2R f -> ((x <> 0)%R -> 
       (canonic_exp beta c x <= Fexp f)%Z) ->
       generic_format beta c x.
Proof.
intros c x f H1 H2.
rewrite H1; destruct f as (m,e).
apply  generic_format_F2R.
simpl in *; intros H3.
rewrite <- H1; apply H2.
intros Y; apply H3.
apply F2R_eq_0_reg with beta e.
now rewrite <- H1.
Qed.


Variable choice:Z->bool.
Variable x:R.


Variable d u: float beta.
Hypothesis Hd: Rnd_DN_pt (generic_format beta fexp) x (F2R d).
Hypothesis Cd: canonic beta fexp d.
Hypothesis Hu: Rnd_UP_pt (generic_format beta fexp) x (F2R u).
Hypothesis Cu: canonic beta fexp u.

Hypothesis dPos: (0 < F2R d)%R.


Let m:= ((F2R d+F2R u)/2)%R.


Lemma d_eq: F2R d= round beta fexp Zfloor x.
Proof with auto with typeclass_instances.
apply Rnd_DN_pt_unicity with (generic_format beta fexp) x...
apply round_DN_pt...
Qed.


Lemma u_eq: F2R u= round beta fexp Zceil x.
Proof with auto with typeclass_instances.
apply Rnd_UP_pt_unicity with (generic_format beta fexp) x...
apply round_UP_pt...
Qed.


Lemma Fexp_d: Fexp d =fexp (ln_beta beta x).
Proof with auto with typeclass_instances.
apply bpow_inj with beta.
apply sym_eq, trans_eq with (ulp beta fexp x).
reflexivity.
rewrite <- ulp_DN, Cd...
rewrite d_eq; reflexivity.
rewrite <- d_eq; assumption.
Qed.

Lemma Fexp_u:  (fexp (ln_beta beta x) <= Fexp u)%Z.
rewrite Cu; unfold canonic_exp.
apply monotone_exp.
apply ln_beta_le.
apply Rlt_le_trans with (1:=dPos).
apply Hd.
apply Hu.
Qed.

Lemma d_le_m: (F2R d <= m)%R.
apply Rmult_le_reg_l with 2%R.
auto with real.
apply Rplus_le_reg_l with (-F2R d)%R.
apply Rle_trans with (F2R d).
right; ring.
apply Rle_trans with (F2R u).
apply Rle_trans with x.
apply Hd.
apply Hu.
right; unfold m; field.
Qed.

Lemma m_le_u: (m <= F2R u)%R.
apply Rmult_le_reg_l with 2%R.
auto with real.
apply Rplus_le_reg_l with (-F2R u)%R.
apply Rle_trans with (F2R d).
right; unfold m; field.
apply Rle_trans with (F2R u).
apply Rle_trans with x.
apply Hd.
apply Hu.
right; ring.
Qed.

Lemma ln_beta_m: (ln_beta beta m =ln_beta beta (F2R d) :>Z).
Proof with auto with typeclass_instances.
apply ln_beta_unique.
rewrite Rabs_right.
split.
apply Rle_trans with (F2R d).
destruct (ln_beta beta (F2R d)) as (e,He).
simpl.
rewrite Rabs_right in He.
apply He.
now apply Rgt_not_eq.
apply Rle_ge; now left.
apply d_le_m.
case m_le_u; intros H.
apply Rlt_le_trans with (1:=H).
rewrite u_eq.
apply round_le_generic...
apply generic_format_bpow.
apply valid_exp.
apply ln_beta_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonic.
case (Rle_or_lt x (bpow (ln_beta beta (F2R d)))); trivial; intros Z.
absurd ((bpow (ln_beta beta (F2R d)) <= (F2R d)))%R.
apply Rlt_not_le.
destruct  (ln_beta beta (F2R d)) as (e,He).
simpl in *; rewrite Rabs_right in He.
apply He.
now apply Rgt_not_eq.
apply Rle_ge; now left.
apply Rle_trans with (round beta fexp Zfloor x).
2: right; apply sym_eq, d_eq.
apply round_ge_generic...
apply generic_format_bpow.
apply valid_exp.
apply ln_beta_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonic.
now left.
replace m with (F2R d).
destruct  (ln_beta beta (F2R d)) as (e,He).
simpl in *; rewrite Rabs_right in He.
apply He.
now apply Rgt_not_eq.
apply Rle_ge; now left.
assert (F2R d = F2R u).
apply Rmult_eq_reg_l with (/2)%R.
apply Rplus_eq_reg_l with (/2*F2R u)%R.
apply trans_eq with m.
unfold m, Rdiv; ring.
rewrite H; field.
auto with real.
apply Rgt_not_eq, Rlt_gt; auto with real.
unfold m; rewrite <- H0; field.
apply Rle_ge; unfold m; apply Rmult_le_pos.
2: left; auto with real.
apply Rle_trans with (0+0)%R;[right; ring|apply Rplus_le_compat].
now left.
apply Rle_trans with (F2R d).
now left.
apply Rle_trans with x.
apply Hd.
apply Hu.
Qed.



Lemma m_eq: exists f:float beta, F2R f = m /\ (Fexp f = fexp (ln_beta beta x) -1)%Z.
specialize (Zeven_ex (radix_val beta)); rewrite Even_beta.
intros (b, Hb); rewrite Zplus_0_r in Hb.
exists (Fmult beta (Float beta b (-1)) (Fplus beta d u))%R.
split.
rewrite F2R_mult, F2R_plus.
unfold m; rewrite Rmult_comm.
unfold Rdiv; apply f_equal.
unfold F2R; simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r, Hb, Z2R_mult.
simpl; field.
apply Rgt_not_eq, Rmult_lt_reg_l with (Z2R 2).
simpl; auto with real.
rewrite Rmult_0_r, <-Z2R_mult, <-Hb.
apply radix_pos.
apply trans_eq with (-1+Fexp (Fplus beta d u))%Z.
unfold Fmult.
destruct  (Fplus beta d u); reflexivity.
rewrite Zplus_comm; unfold Zminus; apply f_equal2.
2: reflexivity.
rewrite Fexp_Fplus.
rewrite Z.min_l.
now rewrite Fexp_d.
rewrite Fexp_d.
apply Fexp_u.
Qed.


Lemma Fm: generic_format beta fexpe m.
destruct m_eq as (g,(Hg1,Hg2)).
apply generic_format_F2R_2 with g.
now apply sym_eq.
intros H; unfold canonic_exp; rewrite Hg2.
rewrite ln_beta_m.
rewrite <- Fexp_d.
rewrite Cd.
unfold canonic_exp.
generalize (fexpe_fexp  (ln_beta beta (F2R d))).
omega.
Qed.



Lemma Zm: 
   exists g : float beta, m = F2R g /\ canonic beta fexp g /\ Zeven (Fnum g) = true.
Proof with auto with typeclass_instances.
destruct m_eq as (g,(Hg1,Hg2)).
apply generic_format_F2R_2 with g.




Theorem rnd_opp: forall x,
  round beta fexp ZnearestE  (round beta fexpe Zrnd_odd x) = 
               round beta fexp ZnearestE x.
Proof with auto with typeclass_instances.
intros x.

Rle_or_lt x m

round_N_UP_betw



apply round_unicity with (Rnd_NE_pt beta fexp) x...
apply Rnd_NE_pt_monotone...
2: apply round_NE_pt...
TOTO.




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



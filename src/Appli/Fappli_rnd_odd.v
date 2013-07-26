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

Section Odd_prop_aux.

Variable beta : radix.
Hypothesis Even_beta: Zeven (radix_val beta)=true.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Variable fexpe : Z -> Z.

Context { valid_exp : Valid_exp fexp }.
Context { valid_expe : Valid_exp fexpe }.
Context { exists_NE_e : Exists_NE beta fexpe }.

Hypothesis fexpe_fexp: forall e, (fexpe e <= fexp e -2)%Z.


Lemma generic_format_F2R_2: forall c, forall (x:R) (f:float beta),
       F2R f = x -> ((x <> 0)%R -> 
       (canonic_exp beta c x <= Fexp f)%Z) ->
       generic_format beta c x.
Proof.
intros c x f H1 H2.
rewrite <- H1; destruct f as (m,e).
apply  generic_format_F2R.
simpl in *; intros H3.
rewrite H1; apply H2.
intros Y; apply H3.
apply F2R_eq_0_reg with beta e.
now rewrite H1.
Qed.


Lemma generic_format_fexpe_fexp: forall x,
 generic_format beta fexp x ->  generic_format beta fexpe x.
Proof.
intros x Hx; unfold generic_format in Hx.
apply generic_format_F2R_2 with 
   (Float beta (Ztrunc (scaled_mantissa beta fexp x)) 
      (canonic_exp beta fexp x)).
now apply sym_eq.
intros; simpl; unfold canonic_exp.
generalize (fexpe_fexp (ln_beta beta x)).
omega.
Qed.



Lemma exists_even_fexp_lt: forall (c:Z->Z), forall (x:R),
      (exists f:float beta, F2R f = x /\ (c (ln_beta beta x) < Fexp f)%Z) ->
      exists f:float beta, F2R f =x /\ canonic beta c f /\ Zeven (Fnum f) = true.   
Proof with auto with typeclass_instances.
intros c x (g,(Hg1,Hg2)).
exists (Float beta 
     (Fnum g*Z.pow (radix_val beta) (Fexp g - c (ln_beta beta x)))
     (c (ln_beta beta x))).
assert (F2R (Float beta 
     (Fnum g*Z.pow (radix_val beta) (Fexp g - c (ln_beta beta x)))
     (c (ln_beta beta x))) = x).
unfold F2R; simpl.
rewrite Z2R_mult, Z2R_Zpower.
rewrite Rmult_assoc, <- bpow_plus.
rewrite <- Hg1; unfold F2R.
apply f_equal, f_equal.
ring.
omega.
split; trivial.
split.
unfold canonic, canonic_exp.
now rewrite H.
simpl.
rewrite Zeven_mult.
rewrite Zeven_Zpower.
rewrite Even_beta.
apply Bool.orb_true_intro.
now right.
omega.
Qed.


Variable choice:Z->bool.
Variable x:R.


Variable d u: float beta.
Hypothesis Hd: Rnd_DN_pt (generic_format beta fexp) x (F2R d).
Hypothesis Cd: canonic beta fexp d.
Hypothesis Hu: Rnd_UP_pt (generic_format beta fexp) x (F2R u).
Hypothesis Cu: canonic beta fexp u.

Hypothesis xPos: (0 < x)%R.


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


Lemma d_ge_0: (0 <= F2R d)%R.
Proof with auto with typeclass_instances.
rewrite d_eq; apply round_ge_generic...
apply generic_format_0.
now left.
Qed.


Lemma Fexp_d: (0 < F2R d)%R -> Fexp d =fexp (ln_beta beta x).
Proof with auto with typeclass_instances.
intros Y.
apply bpow_inj with beta.
apply sym_eq, trans_eq with (ulp beta fexp x).
reflexivity.
rewrite <- ulp_DN, Cd...
rewrite d_eq; reflexivity.
rewrite <- d_eq; assumption.
Qed.


Lemma format_bpow_x: (0 < F2R d)%R 
    -> generic_format beta fexp  (bpow (ln_beta beta x)).
Proof with auto with typeclass_instances.
intros Y.
apply generic_format_bpow.
apply valid_exp.
rewrite <- Fexp_d; trivial.
apply Zlt_le_trans with  (ln_beta beta (F2R d))%Z.
rewrite Cd; apply ln_beta_generic_gt...
now apply Rgt_not_eq.
apply Hd.
apply ln_beta_le; trivial.
apply Hd.
Qed.


Lemma format_bpow_d: (0 < F2R d)%R ->
  generic_format beta fexp (bpow (ln_beta beta (F2R d))).
Proof with auto with typeclass_instances.
intros Y; apply generic_format_bpow.
apply valid_exp.
apply ln_beta_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonic.
Qed.


(*
Lemma Fexp_u:  (fexp (ln_beta beta x) <= Fexp u)%Z.
rewrite Cu; unfold canonic_exp.
apply monotone_exp.
apply ln_beta_le.
apply Rlt_le_trans with (1:=dPos).
apply Hd.
apply Hu.
Qed.
*)

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

Lemma ln_beta_m: (0 < F2R d)%R -> (ln_beta beta m =ln_beta beta (F2R d) :>Z).
Proof with auto with typeclass_instances.
intros dPos; apply ln_beta_unique.
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

Lemma u'_eq:  exists f:float beta, F2R f = F2R u /\ (Fexp f = Fexp d)%Z.
Proof with auto with typeclass_instances.
case d_ge_0; intros Y.
assert ((bpow (ln_beta beta x-1)) <= F2R u <= bpow(ln_beta beta x))%R.
split.
apply Rle_trans with x.
destruct (ln_beta beta x) as (e,He); simpl; intros.
rewrite Rabs_right in He.
apply He, Rgt_not_eq.
apply xPos.
left; apply xPos.
apply Hu.
rewrite u_eq; apply round_le_generic...
now apply format_bpow_x.
destruct (ln_beta beta x) as (e,He); simpl; intros.
rewrite Rabs_right in He.
left; apply He, Rgt_not_eq.
apply xPos.
left; apply xPos.
destruct H as (H1,H2); case H2; intros H3.
exists u; split; trivial.
rewrite Fexp_d, Cu.
unfold canonic_exp; apply f_equal, ln_beta_unique.
rewrite Rabs_right.
split; assumption.
apply Rle_ge; left; apply Rlt_le_trans with (1:=xPos).
apply Hu.
assumption.
rewrite Fexp_d; trivial.
exists (Float beta (Zpower beta (ln_beta beta x-fexp (ln_beta beta x))) 
      (fexp (ln_beta beta x))).
split;[idtac|reflexivity].
rewrite H3; unfold F2R; simpl.
rewrite Z2R_Zpower.
rewrite <- bpow_plus.
apply f_equal; ring.
assert (fexp (ln_beta beta x) <= ln_beta beta x)%Z;[idtac|omega].
replace (ln_beta_val beta x (ln_beta beta x))%Z with (ln_beta beta (F2R u)-1)%Z.
apply TOTO.

apply Zle_trans with (ln_beta beta (F2R u)); [idtac|omega].
apply valid_exp.
apply ln_beta_generic_gt...
apply Rgt_not_eq.
apply Rlt_le_trans with (1:=xPos).
apply Hu.
now apply generic_format_canonic.
assert (ln_beta_val beta (F2R u) (ln_beta beta (F2R u)) = ln_beta beta x+1)%Z.
(*;[idtac|omega].*)
apply ln_beta_unique.
rewrite H3, Rabs_right.
split.
apply bpow_le; omega.
apply bpow_lt; omega.


omega.


Z2R_Zpower_nat


replace  (bpow (ln_beta beta x)) with (bpow (ln_beta beta (F2R d)))%Z.
apply generic_format_bpow.
apply valid_exp.
apply ln_beta_generic_gt...
now apply Rgt_not_eq.
apply Hd.
apply f_equal.
apply ln_beta_unique.
rewrite Rabs_right.
split.
rewrite d_eq; apply round_ge_generic...
apply generic_format_bpow.
apply valid_exp.
apply ln_beta_generic_gt...

ewrite <- Fexp_d.
ln_beta_generic_gt...



rewrite Fexp_d.


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
   exists g : float beta, F2R g = m /\ canonic beta fexpe g /\ Zeven (Fnum g) = true.
Proof with auto with typeclass_instances.
destruct m_eq as (g,(Hg1,Hg2)).
apply exists_even_fexp_lt.
exists g; split; trivial.
rewrite Hg2.
rewrite ln_beta_m.
rewrite <- Fexp_d.
rewrite Cd.
unfold canonic_exp.
generalize (fexpe_fexp  (ln_beta beta (F2R d))).
omega.
Qed.


Lemma DN_odd_d_aux: forall z, (F2R d< z< F2R u)%R ->
    Rnd_DN_pt (generic_format beta fexp) z (F2R d).
Proof with auto with typeclass_instances.
intros z Hz1.
split.
apply Hd.
split.
left; apply Hz1.
intros g Hg1 Hg2.
case (Rle_or_lt g (F2R d)); trivial; intros Y.
assert (F2R u <= g)%R.
rewrite u_eq, ulp_DN_UP.
replace  (ulp beta fexp x) with
  (ulp beta fexp (round beta fexp Zfloor x)).
apply succ_le_lt; try assumption.
apply generic_format_round...
rewrite <- d_eq; now split.
unfold ulp, canonic_exp.
now rewrite <- d_eq, <- Fexp_d, Cd.
intros Z.
absurd (F2R d < F2R u)%R.
apply Rle_not_lt.
right; rewrite d_eq, u_eq.
rewrite round_generic...
rewrite round_generic...
apply Rlt_trans with z; apply Hz1.
absurd (F2R u < F2R u)%R.
auto with real.
apply Rle_lt_trans with (1:=H); now apply Rle_lt_trans with (2:=proj2 Hz1).
Qed.

Lemma UP_odd_d_aux: forall z, (F2R d< z< F2R u)%R ->
    Rnd_UP_pt (generic_format beta fexp) z (F2R u).
Proof with auto with typeclass_instances.
intros z Hz1.
split.
apply Hu.
split.
left; apply Hz1.
intros g Hg1 Hg2.
case (Rle_or_lt (F2R u) g); trivial; intros Y.
assert (g <= F2R d)%R.
apply Rle_trans with (pred beta fexp (F2R u)).
apply le_pred_lt...
apply Hu.
apply Rlt_le_trans with (1:=dPos).
apply Rle_trans with z; left; apply Hz1.
right; rewrite d_eq, u_eq.
apply pred_UP_eq_DN...
apply Rlt_le_trans with (1:=dPos).
apply Rle_trans with z; left.
apply Hz1.
rewrite <- u_eq; apply Hz1.
intros T; absurd (F2R d < F2R u)%R.
apply Rle_not_lt; right.
rewrite u_eq, d_eq, round_generic, round_generic...
now apply Rlt_trans with z.
absurd (z < z)%R.
auto with real.
apply Rle_lt_trans with (1:=Hg2); now apply Rle_lt_trans with (2:=proj1 Hz1).
Qed.



(* SUPPRIMER MONOTONE_EXP ET D_POS *)


Theorem round_odd_prop_pos: 
  round beta fexp ZnearestE  (round beta fexpe Zrnd_odd x) = 
               round beta fexp ZnearestE x.
Proof with auto with typeclass_instances.
set (o:=round beta fexpe Zrnd_odd x).
case (generic_format_EM beta fexp x); intros Hx.
replace o with x; trivial.
unfold o; apply sym_eq, round_generic...
now apply generic_format_fexpe_fexp.
assert (K1:(F2R d <= o)%R).
apply round_ge_generic...
apply generic_format_fexpe_fexp, Hd.
apply Hd.
assert (K2:(o <= F2R u)%R).
apply round_le_generic...
apply generic_format_fexpe_fexp, Hu.
apply Hu.
destruct K1.
destruct K2.
assert (P:(x <> m -> o=m -> (forall P:Prop, P))).
intros Y1 Y2.
assert (Rnd_odd_pt beta fexpe x o).
apply round_odd_pt...
destruct H1 as (_,H1); destruct H1.
absurd (x=m)%R; try trivial.
now rewrite <- Y2, H1.
destruct H1 as (_,(k,(Hk1,(Hk2,Hk3)))).
destruct Zm as (k',(Hk'1,(Hk'2,Hk'3))).
absurd (true=false).
discriminate.
rewrite <- Hk3, <- Hk'3.
apply f_equal, f_equal.
apply canonic_unicity with fexpe...
now rewrite Hk'1, <- Y2.
case (Rle_or_lt  x m); intros Y;[destruct Y|idtac].
(* . *)
apply trans_eq with (F2R d).
apply round_N_DN_betw with (F2R u)...
apply DN_odd_d_aux; now split.
apply UP_odd_d_aux; now split.
split.
apply round_ge_generic...
apply generic_format_fexpe_fexp, Hd.
apply Hd.
assert (o <= (F2R d + F2R u) / 2)%R.
apply round_le_generic...
apply Fm.
now left.
destruct H2; trivial.
apply P.
now apply Rlt_not_eq.
trivial.
apply sym_eq, round_N_DN_betw with (F2R u)...
split.
apply Hd.
exact H1.
(* . *)
replace o with x.
reflexivity.
apply sym_eq, round_generic...
rewrite H1; apply Fm.
(* . *)
apply trans_eq with (F2R u).
apply round_N_UP_betw with (F2R d)...
apply DN_odd_d_aux; now split.
apply UP_odd_d_aux; now split.
split.
assert ((F2R d + F2R u) / 2 <= o)%R.
apply round_ge_generic...
apply Fm.
now left.
destruct H1; trivial.
apply P.
now apply Rgt_not_eq.
rewrite <- H1; trivial.
apply round_le_generic...
apply generic_format_fexpe_fexp, Hu.
apply Hu.
apply sym_eq, round_N_UP_betw with (F2R d)...
split.
exact Y.
apply Hu.
(* *)
admit.
admit.

Qed.


End Odd_prop_aux.

Section Odd_prop.

Variable beta : radix.
Hypothesis Even_beta: Zeven (radix_val beta)=true.

Variable fexp : Z -> Z.
Variable fexpe : Z -> Z.
Variable choice:Z->bool.

Context { valid_exp : Valid_exp fexp }.
Context { valid_expe : Valid_exp fexpe }.
Context { exists_NE_e : Exists_NE beta fexpe }.

Hypothesis fexpe_fexp: forall e, (fexpe e <= fexp e -2)%Z.


Theorem round_odd_prop: forall x, 
  round beta fexp ZnearestE  (round beta fexpe Zrnd_odd x) = 
               round beta fexp ZnearestE x.
Proof with auto with typeclass_instances.
intros x.
case (total_order_T x 0); intros H; [case H; clear H; intros H | idtac].
admit.


rewrite H; repeat rewrite round_0...

apply round_odd_prop_pos.


Section Odd_prop.

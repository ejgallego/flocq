Require Import Fcore.
Require Import Fcalc_ops.

Section Fprop_plus_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Hypothesis prop_exp : valid_exp fexp.

Theorem rounding_repr_same_exp :
  forall rnd m e,
  exists m',
  rounding beta fexp rnd (F2R (Float beta m e)) = F2R (Float beta m' e).
Proof.
intros rnd m e.
set (e' := canonic_exponent beta fexp (F2R (Float beta m e))).
unfold rounding, scaled_mantissa. fold e'.
destruct (Zle_or_lt e' e) as [He|He].
exists m.
unfold F2R at 2. simpl.
rewrite Rmult_assoc, <- bpow_add.
rewrite <- Z2R_Zpower. 2: omega.
rewrite <- mult_Z2R, Zrnd_Z2R.
unfold F2R. simpl.
rewrite mult_Z2R.
rewrite Rmult_assoc.
rewrite Z2R_Zpower. 2: omega.
rewrite <- bpow_add.
apply (f_equal (fun v => Z2R m * bpow v)%R).
ring.
exists ((Zrnd rnd (Z2R m * bpow (e - e'))) * Zpower (radix_val beta) (e' - e))%Z.
unfold F2R. simpl.
rewrite mult_Z2R.
rewrite Z2R_Zpower. 2: omega.
rewrite 2!Rmult_assoc.
rewrite <- 2!bpow_add.
apply (f_equal (fun v => _ * bpow v)%R).
ring.
Qed.

Hypothesis monotone_exp : forall ex ey, (ex <= ey)%Z -> (fexp ex <= fexp ey)%Z.
Notation format := (generic_format beta fexp).

Variable choice : R -> bool.

Theorem plus_error_aux :
  forall x y,
  (canonic_exponent beta fexp x <= canonic_exponent beta fexp y)%Z ->
  format x -> format y ->
  format (rounding beta fexp (ZrndN choice) (x + y) - (x + y))%R.
Proof.
intros x y.
set (ex := canonic_exponent beta fexp x).
set (ey := canonic_exponent beta fexp y).
intros He Hx Hy.
destruct (Req_dec (rounding beta fexp (ZrndN choice) (x + y) - (x + y)) R0) as [H0|H0].
rewrite H0.
apply generic_format_0.
set (mx := Ztrunc (scaled_mantissa beta fexp x)).
set (my := Ztrunc (scaled_mantissa beta fexp y)).
(* *)
assert (Hxy: (x + y)%R = F2R (Float beta (mx + my * radix_val beta ^ (ey - ex)) ex)).
rewrite Hx, Hy.
fold mx my ex ey.
rewrite <- plus_F2R.
unfold Fplus. simpl.
now rewrite Zle_imp_le_bool with (1 := He).
(* *)
rewrite Hxy.
destruct (rounding_repr_same_exp (ZrndN choice) (mx + my * radix_val beta ^ (ey - ex)) ex) as (mxy, Hxy').
rewrite Hxy'.
assert (H: (F2R (Float beta mxy ex) -
   F2R (Float beta (mx + my * radix_val beta ^ (ey - ex)) ex))%R = F2R
     (Float beta
        (- (mx + my * radix_val beta ^ (ey - ex)) +
         mxy * radix_val beta ^ (ex - ex)) ex)).
unfold Rminus.
rewrite opp_F2R, Rplus_comm, <- plus_F2R.
unfold Fplus. simpl.
now rewrite Zle_bool_refl.
rewrite H.
apply generic_format_canonic_exponent.
apply monotone_exp.
rewrite <- H, <- Hxy', <- Hxy.
apply ln_beta_monotone_abs.
exact H0.
pattern x at 3 ; replace x with (-(y - (x + y)))%R by ring.
rewrite Rabs_Ropp.
now apply (generic_N_pt beta _ prop_exp choice (x + y)).
Qed.

Theorem plus_error :
  forall x y,
  format x -> format y ->
  format (rounding beta fexp (ZrndN choice) (x + y) - (x + y))%R.
Proof.
intros x y Hx Hy.
destruct (Zle_or_lt (canonic_exponent beta fexp x) (canonic_exponent beta fexp y)).
now apply plus_error_aux.
rewrite Rplus_comm.
apply plus_error_aux ; try easy.
now apply Zlt_le_weak.
Qed.

End Fprop_plus_error.
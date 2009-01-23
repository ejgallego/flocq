Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.

Section RND_FIX.

Open Scope R_scope.

(*
Theorem exp_ln_powerRZ :
 forall u v : Z, (0 < u)%Z -> exp (ln (IZR u) * (IZR v)) = powerRZ (IZR u) v.
admit.
Qed.

(*
Theorem exp_monotone : forall x y : R, (x <= y)%R -> (exp x <= exp y)%R.
intros x y H; case H; intros H2.
left; apply exp_increasing; auto.
right; auto with real.
Qed.*)


Definition floor_int (r : R) :=(up r-1)%Z.


Theorem floor_int_pos : forall r : R, (0 <= r)%R -> (0 <=  IZR (floor_int r))%R.
Proof.
intros r H1; unfold floor_int in |- *.
generalize (archimed r); intros T; elim T; intros H3 H2; clear T.
replace 0%R with (IZR 0); auto with real; apply IZR_le.
assert (0 < up r)%Z; auto with zarith.
apply lt_IZR; apply Rle_lt_trans with r; auto with real zarith.
Qed.


Theorem  floor_int_correct1 : forall r : R, (IZR (floor_int r) <= r)%R. 
Proof.
intros r; unfold  floor_int in |- *.
generalize (archimed r); intros T; elim T; intros H1 H2; clear T.
apply Rplus_le_reg_l with (1 + - r)%R.
ring_simplify (1 + - r + r)%R.
apply Rle_trans with (2 := H2).
unfold Zminus; rewrite plus_IZR; right; simpl in |- *; ring.
Qed.

Theorem floor_int_correct2 : forall r : R, (r < IZR (floor_int r+1))%R.
intros r; unfold floor_int in |- *.
generalize (archimed r); intros T; elim T; intros H1 H2; clear T.
ring_simplify (up r - 1 + 1)%Z; auto.
Qed.

Theorem floor_int_correct3 : forall r : R, (r - 1 < IZR (floor_int r))%R.
intros r; unfold floor_int in |- *.
generalize (archimed r); intros T; elim T; intros H1 H2; clear T.
unfold Rminus, Zminus; rewrite plus_IZR; simpl in |- *; auto with real. 
Qed.
*)

Variable beta : radix.

Notation bpow := (epow beta).

Variable emin prec : Z.

(*
Definition RND_DN_pos_fn (r : R) :=
  match Rle_dec (powerRZ (IZR radix) (prec-1+emin)) r with
  | left _ =>
      let e := floor_int (ln r / ln (IZR radix) + IZR (- prec+1)) in
      Float radix (floor_int (r * powerRZ (IZR radix) (- e))) e
  | right _ => Float radix (floor_int (r * powerRZ (IZR radix) (-emin))) emin
  end.

Variable radix_gt_0 : (0 < radix)%Z.

Lemma FLT_format_satisfies_DN_aux:
 forall x : R, (0 <= x)%R -> exists f : R, Rnd_DN (FLT_format radix emin prec) x f.
Proof.
intros; exists (F2R (RND_DN_pos_fn x)); split.
exists (RND_DN_pos_fn x); split; auto; split.
unfold RND_DN_pos_fn; case (Rle_dec (powerRZ (IZR radix) (prec-1+emin)) x); simpl; intros H1.
rewrite Zabs_eq.
2: apply le_IZR; apply floor_int_pos; apply Rmult_le_pos; auto.
2: admit. (* cf apres *)
apply lt_IZR.
apply Rle_lt_trans with (1:=floor_int_correct1 _).
rewrite <- exp_ln_powerRZ; auto.
apply Rlt_le_trans with  (x *
    (exp (-ln x) * exp (ln (IZR radix) * IZR (prec))))%R.
apply Rmult_lt_compat_l; auto with real.
apply Rlt_le_trans with (2:=H1); auto with real zarith.
admit. (* cf apres *)
rewrite <- exp_plus.
apply exp_increasing.
apply Rmult_lt_reg_l with (/ln (IZR radix))%R.
admit.
apply Rle_lt_trans with (IZR (- floor_int (ln x / ln (IZR radix) + IZR (- prec+1)))).
right; field.
admit.
apply Rlt_le_trans with (-(ln x / ln (IZR radix) - IZR (prec)))%R.
2: right; field.
2: admit.
rewrite Ropp_Ropp_IZR.
apply Ropp_lt_contravar.
apply Rle_lt_trans with (2:= floor_int_correct3 _).
rewrite plus_IZR; rewrite Ropp_Ropp_IZR; simpl; right; ring.
rewrite exp_Ropp; rewrite exp_ln; auto.
2: admit.
rewrite  exp_ln_powerRZ.
admit.
auto.
rewrite Zabs_eq.
2: apply le_IZR; apply floor_int_pos; apply Rmult_le_pos; auto.
2: admit. (* cf apres *)
apply lt_IZR.
apply Rle_lt_trans with (1:=floor_int_correct1 _).
apply Rlt_le_trans with (powerRZ (IZR radix) (prec - 1 + emin)* powerRZ (IZR radix) (- emin))%R.
apply Rmult_lt_compat_r.
admit.
auto with real.
rewrite <- powerRZ_add; auto with real.
(* apply Rle_ powerRZ.*)
admit.
admit.
unfold RND_DN_pos_fn; case (Rle_dec (powerRZ (IZR radix) (prec-1+emin)) x); 
  simpl; auto with zarith; intros H1.
assert (emin-1  < floor_int (ln x / ln (IZR radix) + IZR (- prec + 1)))%Z; auto with zarith.
apply lt_IZR.
apply Rle_lt_trans with (2:= floor_int_correct3 _).
apply Rplus_le_reg_l with (IZR prec).
apply Rmult_le_reg_l with (ln (IZR radix)).
admit.
apply Rle_trans with (ln x).
exp
ln


rewrite <- exp_ln_powerRZ; auto.
apply Rlt_le_trans with  (x *
    (exp (-ln x) * exp (ln (IZR radix) * IZR (prec))))%R.
apply Rmult_lt_compat_l; auto with real.
apply Rlt_le_trans with (2:=H1); auto with real zarith.
admit. (* cf apres *)
rewrite <- exp_plus.
apply exp_increasing.
apply Rmult_lt_reg_l with (/ln (IZR radix))%R.
admit.
apply Rle_lt_trans with (IZR (- floor_int (ln x / ln (IZR radix) + IZR (- prec+1)))).
right; field.
admit.
apply Rlt_le_trans with (-(ln x / ln (IZR radix) - IZR (prec)))%R.
2: right; field.
2: admit.
rewrite Ropp_Ropp_IZR.
apply Ropp_lt_contravar.
apply Rle_lt_trans with (2:= floor_int_correct3 _).
rewrite plus_IZR; rewrite Ropp_Ropp_IZR; simpl; right; ring.
rewrite exp_Ropp; rewrite exp_ln; auto.
2: admit.
rewrite  exp_ln_powerRZ.
admit.
auto.



      (ln (IZR radix) *
       IZR (- (ln x / ln (IZR radix) + IZR (- Zpred prec))))


apply Rle_lt_trans with (x *
    powerRZ (IZR radix)
      (- floor_int (ln x / ln (IZR radix) + IZR (- Zpred prec)))

rewrite powerRZ_add; auto with real zarith.


rewrite Zpower_powerRZ; rewrite <- Rabsolu_Zabs.



unfold FLT_format.



Theorem FLT_format_satisfies_DN : satisfies_DN (FLT_format radix emin prec).
Proof.
unfold satisfies_DN.
intros.


Theorem FLT_format_satisfies_DN_UP :
  satisfies_DN_UP (FLT_format radix emin prec).
Proof.
intros.
assert (Hdn: satisfies_DN (FLT_format radix emin prec)) by admit.
apply satisfies_DN_imp_UP.
intros x (f,(Hx,(Hm,He))).
exists (Float radix (-(Fnum f))%Z (Fexp f)).
repeat split.
rewrite Hx.
unfold F2R.
simpl.
rewrite Ropp_Ropp_IZR.
now rewrite Ropp_mult_distr_l_reverse.
simpl.
now rewrite Zabs_Zopp.
exact He.
exact Hdn.
Qed.

Variable radix_gt_0 : (0 < radix)%Z.

Lemma powerRZ_radix_ge_0 :
  forall e : Z, (0 <= powerRZ (IZR radix) e)%R.
Proof.
intros.
apply powerRZ_le.
change R0 with (IZR 0).
apply IZR_lt.
exact radix_gt_0.
Qed.

Lemma powerRZ_radix_gt_0 :
  forall e : Z, (0 < powerRZ (IZR radix) e)%R.
Proof.
intros.
apply powerRZ_lt.
change R0 with (IZR 0).
apply IZR_lt.
exact radix_gt_0.
Qed.

Lemma IZR_radix_neq_0 :
  IZR radix <> R0.
Proof.
apply Rgt_not_eq.
change R0 with (IZR 0).
apply IZR_lt.
exact radix_gt_0.
Qed.
*)

Theorem FIX_format_satisfies_any :
  satisfies_any (FIX_format beta emin).
Proof.
refine ((fun D => Satisfies_any _ _ _ (projT1 D) (projT2 D)) _).
(* symmetric set *)
exists (Float beta 0 emin).
split.
unfold F2R.
now rewrite Rmult_0_l.
apply refl_equal.
intros x ((m,e),(H1,H2)).
exists (Float beta (-m) emin).
split.
rewrite H1.
unfold F2R.
simpl.
rewrite opp_Z2R, Ropp_mult_distr_l_reverse.
now rewrite <- H2.
apply refl_equal.
(* rounding down *)
exists (fun x => F2R (Float beta (up (x * bpow (Zopp emin)) - 1) emin)).
intros x.
set (m := up (x * bpow (Zopp emin))).
set (f := Float beta (m - 1) emin).
split.
now exists f.
split.
unfold F2R, f, m.
simpl.
pattern x at 2 ; rewrite <- Rmult_1_r.
change 1 with (bpow Z0).
rewrite <- (Zplus_opp_l emin).
rewrite epow_add.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
apply epow_ge_0.
generalize (x * bpow (- emin)%Z)%R.
clear.
intros.
rewrite minus_Z2R.
simpl.
apply Rminus_le.
replace (Z2R (up r) - 1 - r) with ((Z2R (up r) - r) - 1) by ring.
apply Rle_minus.
rewrite Z2R_IZR.
eapply for_base_fp.
intros g ((mx,ex),(H1,H2)) H3.
rewrite H1.
unfold F2R.
rewrite H2.
simpl.
apply Rmult_le_compat_r.
apply epow_ge_0.
apply Z2R_le.
apply Zlt_succ_le.
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow emin).
apply epow_gt_0.
apply Rle_lt_trans with x.
rewrite <- H2.
change (F2R (Float beta mx ex) <= x).
now rewrite <- H1.
pattern x ; rewrite <- Rmult_1_r.
change R1 with (bpow Z0).
rewrite <- (Zplus_opp_l emin).
rewrite epow_add.
rewrite <- Rmult_assoc.
apply Rmult_lt_compat_r.
apply epow_gt_0.
change (m - 1)%Z with (Zpred m).
rewrite <- Zsucc_pred.
rewrite Z2R_IZR.
eapply archimed.
Qed.

End RND_FIX.

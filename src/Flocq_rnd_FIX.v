Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.

Section RND_FIX.

Open Scope R_scope.



Variable beta : radix.

Notation bpow := (epow beta).

Variable emin : Z.

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

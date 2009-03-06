Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_float_prop.
Require Import Flocq_rnd_ex. 
Require Import Flocq_rnd_FIX.
Require Import Flocq_rnd_FLX.

Section RND_FLT.

Open Scope R_scope.

Variable beta : radix.

Notation bpow := (epow beta).



Variable emin prec : Z.
Variable Hp : Zlt 0 prec.


Theorem FLT_format_satisfies_any :
  satisfies_any (FLT_format beta emin prec).
elim (FIX_format_satisfies_any beta emin); intros O1 T2 r1 H1; clear T2.
elim (FLX_format_satisfies_any beta prec); trivial; intros O1' T2 r2 H2; clear T2.
refine ((fun D => Satisfies_any _ _ _ (projT1 D) (projT2 D)) _).
(* symmetric set *)
exists (Float beta 0 emin).
split.
unfold F2R.
now rewrite Rmult_0_l.
split.
apply lt_Z2R.
rewrite Z2R_Zpower.
apply epow_gt_0.
now apply Zlt_le_weak.
apply Zeq_le.
apply refl_equal.
intros x ((m,e),(K1,K2)).
exists (Float beta (-m) e).
split.
rewrite K1.
unfold F2R.
simpl.
now rewrite opp_Z2R, Ropp_mult_distr_l_reverse.
split.
simpl.
now rewrite Zabs_Zopp.
now simpl.
(* rounding *)
exists (fun x =>
  match total_order_T  0 x with
     |inleft _  => match total_order_T (bpow (prec+emin)%Z) x with
                   | inleft  _  => r2 x
                   | inright _ => r1 x
                   end
    | inright _ => match total_order_T x (-bpow (prec+emin)%Z) with
                   | inleft  _  => r2 x
                   | inright _ => r1 x
                   end
  end).
intros x.
destruct (total_order_T 0 x) as [B|B].
assert (0 <= x);[destruct B; auto with real| clear B].
(* x >= 0 *)
destruct (total_order_T (bpow (prec+emin)%Z) x) as [Hx|Hx].
(** x big *)
assert (bpow (prec + emin)%Z <= x);[destruct Hx; auto with real| clear Hx].
destruct (H2 x) as ((f,(Lf1,Lf2)),(L1,L2)).
split.
exists f.
repeat split; trivial.
apply <- (epow_le beta).
apply Rmult_le_reg_l with (bpow prec).
apply epow_gt_0.
rewrite <- epow_add.
apply Rle_trans with (F2R f).
rewrite <- Lf1.
apply L2; trivial.
exists (Float beta 1 (prec+emin)).
split.
unfold F2R; simpl; auto with real.
simpl.
now apply vNum_gt_1.
unfold F2R; apply Rmult_le_compat_r.
apply epow_ge_0.
rewrite <- Z2R_Zpower; auto with zarith.
apply Z2R_le.
rewrite <- (Zabs_eq (Fnum f)); auto with zarith.
apply le_Z2R.
apply Rmult_le_reg_l with (bpow (Fexp f)).
apply epow_gt_0.
apply Rle_trans with 0%R.
simpl; right; ring.
apply Rle_trans with (r2 x).
now apply L2.
right; rewrite Lf1; unfold F2R; now apply Rmult_comm.
split; trivial.
intros g P1 P2.
apply L2; trivial.
destruct P1 as (f',(M1,(M2,M3))).
exists f'; split; auto.
(** x small *)
assert (x < bpow (prec + emin)%Z);[auto with real| clear Hx].
destruct (H1 x) as ((f,(Lf1,Lf2)),(L1,L2)).
split.
exists f.
repeat split; trivial.
apply lt_Z2R.
rewrite <- Rabs_Z2R.
rewrite Z2R_Zpower; auto with zarith.
apply Rmult_lt_reg_r with (bpow emin).
apply epow_gt_0.
rewrite <- epow_add.
apply Rle_lt_trans with (2:=H0).
apply Rle_trans with (2:=L1).
rewrite <- (Rabs_right (r1 x)).
right; rewrite Lf1.
unfold F2R; rewrite Rabs_mult.
rewrite (Rabs_right (bpow (Fexp f))).
now rewrite Lf2.
apply Rle_ge; apply epow_ge_0.
apply Rle_ge; now apply L2.
rewrite Lf2; auto with zarith.
split; trivial.
intros g P1 P2.
apply L2; trivial.
destruct P1 as (f',(M1,(M2,M3))).
exists (Float beta ((Fnum f'*Zpower (radix_val beta) (Fexp f'-emin))) emin); split; auto.
rewrite M1; unfold F2R; simpl.
rewrite mult_Z2R.
rewrite Z2R_Zpower; auto with zarith.
rewrite Rmult_assoc; rewrite <- epow_add.
now replace (Fexp f' - emin + emin)%Z with (Fexp f') by ring.
assert (x < 0);[auto with real| clear B].
(* x < 0 *)
destruct (total_order_T x (-bpow (prec+emin)%Z)) as [Hx|Hx].
(** x big *)
assert (x <= - bpow (prec + emin)%Z);[destruct Hx; auto with real| clear Hx].
destruct (H2 x) as ((f,(Lf1,Lf2)),(L1,L2)).
split.
exists f.
repeat split; trivial.
apply <- (epow_le beta).
apply Rmult_le_reg_l with (bpow prec).
apply epow_gt_0.
rewrite <- epow_add.
apply Ropp_le_cancel.
apply Rle_trans with (2:=H0).
apply Rle_trans with (2:=L1).
rewrite Lf1.
rewrite <- Ropp_mult_distr_l_reverse.
unfold F2R; apply Rmult_le_compat_r.
apply epow_ge_0.
apply Ropp_le_cancel.
eapply Rle_trans.
apply RRle_abs.
rewrite Rabs_Ropp; rewrite Rabs_Z2R.
rewrite Ropp_involutive.
rewrite <- Z2R_Zpower; auto with zarith.
apply Z2R_le; auto with zarith.
split; trivial.
intros g P1 P2.
apply L2; trivial.
destruct P1 as (f',(M1,(M2,M3))).
exists f'; split; auto.
(** x small *)
assert (- bpow (prec + emin)%Z < x);[auto with real| clear Hx].
destruct (H1 x) as ((f,(Lf1,Lf2)),(L1,L2)).
split.
assert (-bpow (prec + emin)%Z <= r1 x).
apply L2.
exists (Float beta (-Zpower (radix_val beta) prec)%Z emin); split.
unfold F2R; simpl.
rewrite opp_Z2R.
rewrite Z2R_Zpower; auto with zarith.
rewrite Ropp_mult_distr_l_reverse.
now rewrite <- epow_add.
now simpl.
now left.
case H3; intros I.
exists f.
repeat split; trivial.
apply lt_Z2R.
rewrite <- Rabs_Z2R.
rewrite Z2R_Zpower; auto with zarith.
apply Rmult_lt_reg_r with (bpow emin).
apply epow_gt_0.
rewrite <- epow_add.
apply Ropp_lt_cancel.
apply Rlt_le_trans with (1:=I).
apply Ropp_le_cancel; rewrite Ropp_involutive.
rewrite <- (Rabs_left1 (r1 x)).
right; rewrite Lf1.
unfold F2R; rewrite Rabs_mult.
rewrite (Rabs_right (bpow (Fexp f))).
now rewrite Lf2.
apply Rle_ge; apply epow_ge_0.
apply Rle_trans with (1:=L1); now left.
rewrite Lf2; auto with zarith.
exists (Float beta (-Zpower (radix_val beta) (prec-1)) (emin+1)).
split.
rewrite <- I.
unfold F2R; simpl.
rewrite opp_Z2R.
rewrite Z2R_Zpower; auto with zarith.
rewrite Ropp_mult_distr_l_reverse.
rewrite <- epow_add.
now replace (prec - 1 + (emin + 1))%Z with (prec+emin)%Z by ring.
split.
simpl.
rewrite Zabs_Zopp.
rewrite Zabs_eq.
apply lt_Z2R.
repeat rewrite Z2R_Zpower; auto with zarith.
apply -> epow_lt; auto with zarith.
apply le_Z2R.
rewrite Z2R_Zpower; auto with zarith.
simpl.
apply epow_ge_0.
simpl; auto with zarith.
split; trivial.
intros g P1 P2.
apply L2; trivial.
destruct P1 as (f',(M1,(M2,M3))).
exists (Float beta ((Fnum f'*Zpower (radix_val beta) (Fexp f'-emin))) emin); split; auto.
rewrite M1; unfold F2R; simpl.
rewrite mult_Z2R.
rewrite Z2R_Zpower; auto with zarith.
rewrite Rmult_assoc; rewrite <- epow_add.
now replace (Fexp f' - emin + emin)%Z with (Fexp f') by ring.
Qed.


End RND_FLT.

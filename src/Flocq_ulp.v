Require Import Flocq_Raux.
Require Import Flocq_defs.
Require Import Flocq_rnd_ex.
Require Import Flocq_rnd_prop.
Require Import Flocq_rnd_generic.

Section Flocq_ulp.

Variable beta : radix.

Notation bpow := (epow beta).

Variable fexp : Z -> Z.

Variable prop_exp : valid_exp fexp.

Definition ulp x :=
  match Req_EM_T x 0 with
  | left _ => R0
  | right Hx => F2R (Float beta 1 (fexp (projT1 (ln_beta beta (Rabs x) (Rabs_pos_lt _ Hx)))))
  end.

Definition F := generic_format beta fexp.

Lemma zero_not_in_format :
  forall x, ~ F x -> x <> R0.
Proof.
intros x Fx Hx.
elim Fx.
rewrite Hx.
clear.
exists (Float beta 0 0).
split.
unfold F2R. simpl.
now rewrite Rmult_0_l.
intros H.
now elim H.
Qed.

Theorem ulp_pred_succ_pt :
  forall x xd xu,
  ~ F x -> Rnd_DN_pt F x xd -> Rnd_UP_pt F x xu ->
  (xu = xd + ulp x)%R.
Proof.
intros x xd xu Fx Hd1 Hu1.
unfold ulp.
destruct (Req_EM_T x 0) as [Hx1|Hx1].
now elim zero_not_in_format with x.
destruct (Rdichotomy x 0 Hx1) as [Hx2|Hx2].
(* negative *)
destruct (ln_beta beta (Rabs x) (Rabs_pos_lt x Hx1)) as (ex, Hx3).
simpl.
destruct (Z_lt_le_dec (fexp ex) ex) as [He1|He1].
(* . negative big *)
admit.
(* . negative small *)
rewrite (Rabs_left _ Hx2) in Hx3.
rewrite Rnd_UP_pt_unicity with F x xu R0.
rewrite Rnd_DN_pt_unicity with F x xd (- bpow (fexp ex))%R.
unfold F2R. simpl.
rewrite Rmult_1_l.
now rewrite Rplus_opp_l.
exact Hd1.
apply Rnd_UP_DN_pt_sym.
now eapply generic_format_satisfies_any.
rewrite Ropp_involutive.
now apply generic_UP_pt_small_pos.
exact Hu1.
apply Rnd_DN_UP_pt_sym.
now eapply generic_format_satisfies_any.
rewrite Ropp_0.
now apply generic_DN_pt_small_pos with ex.
(* positive *)
destruct (ln_beta beta (Rabs x) (Rabs_pos_lt x Hx1)) as (ex, Hx3).
simpl.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hx2)) in Hx3.
destruct (Z_lt_le_dec (fexp ex) ex) as [He1|He1].
(* . positive big *)
assert (Hd2 := generic_DN_pt_pos _ _ prop_exp _ _ Hx3).
assert (Hu2 : Rnd_DN_pt F (-x) (-xu)).
apply Rnd_UP_DN_pt_sym.
now eapply generic_format_satisfies_any.
now rewrite 2!Ropp_involutive.
assert (Hx4 : (bpow (ex - 1)%Z <= --x < bpow ex)%R).
now rewrite Ropp_involutive.
assert (Hu3 := generic_DN_pt_neg _ _ prop_exp _ _ Hx4).
rewrite (Rnd_DN_pt_unicity _ _ _ _ Hd1 Hd2).
rewrite <- (Ropp_involutive xu).
rewrite (Rnd_DN_pt_unicity _ _ _ _ Hu2 Hu3).
clear.
unfold F2R. simpl.
rewrite <- Rmult_plus_distr_r.
rewrite <- Ropp_mult_distr_l_reverse.
apply (f_equal (fun v => v * bpow (fexp ex))%R).
rewrite 2!minus_Z2R.
simpl.
ring_simplify.
rewrite Ropp_mult_distr_l_reverse.
generalize (x * bpow (- fexp ex)%Z)%R.
clear. intros x.
admit.
(* . positive small *)
rewrite Rnd_UP_pt_unicity with F x xu (bpow (fexp ex)).
rewrite Rnd_DN_pt_unicity with F x xd R0.
rewrite Rplus_0_l.
unfold F2R. simpl.
now rewrite Rmult_1_l.
exact Hd1.
now apply generic_DN_pt_small_pos with ex.
exact Hu1.
now apply generic_UP_pt_small_pos.
Qed.

End Flocq_ulp.
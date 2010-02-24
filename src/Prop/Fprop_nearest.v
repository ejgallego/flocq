Require Import Fcore.

Section Fprop_nearest.

Open Scope R_scope.

Theorem Rnd_N_pt_abs :
  forall F : R -> Prop,
  F 0 ->
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_N_pt F x f -> Rnd_N_pt F (Rabs x) (Rabs f).
Proof.
intros F HF0 HF x f Hxf.
unfold Rabs at 1.
destruct (Rcase_abs x) as [Hx|Hx].
rewrite Rabs_left1.
apply Rnd_N_pt_sym.
exact HF.
now rewrite 2!Ropp_involutive.
apply Rnd_N_pt_neg with (3 := Hxf).
exact HF0.
now apply Rlt_le.
rewrite Rabs_pos_eq.
exact Hxf.
apply Rnd_N_pt_pos with (3 := Hxf).
exact HF0.
now apply Rge_le.
Qed.

(*
Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Variable prop_exp : valid_exp fexp.

Notation format := (generic_format beta fexp).

Theorem half_format_eq_dist :
  forall x d u : R,
  format x -> 0 < d ->
  Rnd_DN_pt format (/2 * x) d -> Rnd_UP_pt format (/2 * x) u ->
  d + u = x.
Proof.
intros x d u Fx H0d Hd Hu.
destruct Fx as ((mx, ex), Hxc).
unfold canonic in Hxc.
destruct (generic_format_EM beta fexp prop_exp (/2 * x)).
(* x/2 in format *)
rewrite Rnd_DN_pt_idempotent with (1 := Hd) (2 := H).
rewrite Rnd_UP_pt_idempotent with (1 := Hu) (2 := H).
field.
(* x/2 not in format *)
rewrite (ulp_pred_succ_pt _ _ _ _ _ _ H Hd Hu).
destruct (proj1 Hd) as ((md, ed), Hdc).
assert (He: (ed <= ex)%Z).
admit.
assert (Zodd mx).
destruct (Zeven_odd_dec mx) as [Hm|Hm]. 2: exact Hm.
elim H. clear H.
destruct (Zeven_ex mx Hm) as (m, H).
exists (Float beta (m * Zpower (radix_val beta) (ex - ed)) ed).
split.
admit.
simpl.
apply bpow_eq with beta.
destruct Hdc as (Hd1,Hd2).
simpl in Hd2.
rewrite Hd2.
now apply ulp_DN_pt_eq.
replace (d + (d + ulp beta fexp (/ 2 * x))) with (2 * d + ulp beta fexp (/ 2 * x)) by ring.
replace d with (Z2R (Zdiv2 (mx * Zpower (radix_val beta) (ex - ed))) * bpow ed).
rewrite <- (ulp_DN_pt_eq _ _ prop_exp _ _ H0d Hd).
unfold ulp.
rewrite <- (proj2 Hdc).
simpl.
apply trans_eq with (Z2R (2 * Zdiv2 (mx * radix_val beta ^ (ex - ed)) + 1) * bpow ed).
rewrite plus_Z2R, mult_Z2R.
simpl. ring.
rewrite <- Zodd_div2.
admit.
admit.
SearchAbout Zodd.



unfold generic_format.
SearchAbout Zeven.
Print Zeven.


destruct (Rlt_or_le d x) as [Hdx|Hdx].



Theorem Rnd_N_pt_half :
  forall x f : R, 0 <= x ->
  format x -> Rnd_N_pt (/2 * x) f -> Rnd_UP_pt (/2 * x) f.

Theorem half_monotony : (* FmultRadixInv *)
  forall x y z : R,
  format x ->
  Rnd_N_pt format y z -> /2 * x < y -> /2 * x <= z.
Proof.
intros x y z Fx Hyz Hxy.
destruct (satisfies_any_imp_UP format (generic_format_satisfies_any _ _ prop_exp)) as (Hu,_).
destruct (Hu (/2 * x)) as (xhu, Hxhu).
destruct (Rlt_or_le xhu y).
(* . *)
apply Rle_trans with xhu.
apply Hxhu.
apply Rnd_N_pt_monotone with (2 := Hyz) (3 := H).
apply Rnd_N_pt_refl.
apply Hxhu.
(* . *)
unfold Rnd_UP_pt in Hxhu.

apply Rlt_le.
apply Rlt_le_trans



Theorem ClosestExp :
 forall x f : R,
 Rnd_N_pt format x f -> Rabs (x - f) <= /2 * bpow (Fexp f).
*)

End Fprop_nearest.
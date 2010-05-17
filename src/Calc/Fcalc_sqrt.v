Require Import Fcore.
Require Import Fcalc_bracket.
Require Import Fcalc_digits.

Section Fcalc_sqrt.

Fixpoint Zsqrt_aux (p : positive) : Z * Z :=
  match p with
  | xH => (1, 0)%Z
  | xO xH => (1, 1)%Z
  | xI xH => (1, 2)%Z
  | xO (xO p) =>
    let (q, r) := Zsqrt_aux p in
    let r' := (4 * r)%Z in
    let d := (r' - (4 * q + 1))%Z in
    if Zlt_bool d 0 then (2 * q, r')%Z else (2 * q + 1, d)%Z
  | xO (xI p) =>
    let (q, r) := Zsqrt_aux p in
    let r' := (4 * r + 2)%Z in
    let d := (r' - (4 * q + 1))%Z in
    if Zlt_bool d 0 then (2 * q, r')%Z else (2 * q + 1, d)%Z
  | xI (xO p) =>
    let (q, r) := Zsqrt_aux p in
    let r' := (4 * r + 1)%Z in
    let d := (r' - (4 * q + 1))%Z in
    if Zlt_bool d 0 then (2 * q, r')%Z else (2 * q + 1, d)%Z
  | xI (xI p) =>
    let (q, r) := Zsqrt_aux p in
    let r' := (4 * r + 3)%Z in
    let d := (r' - (4 * q + 1))%Z in
    if Zlt_bool d 0 then (2 * q, r')%Z else (2 * q + 1, d)%Z
  end.

Lemma Zsqrt_ind :
  forall P : positive -> Prop,
  P xH -> P (xO xH) -> P (xI xH) ->
  ( forall p, P p -> P (xO (xO p)) /\ P (xO (xI p)) /\ P (xI (xO p)) /\ P (xI (xI p)) ) ->
  forall p, P p.
Proof.
intros P H1 H2 H3 Hp.
fix 1.
intros [[p|p|]|[p|p|]|].
refine (proj2 (proj2 (proj2 (Hp p _)))).
apply Zsqrt_ind.
refine (proj1 (proj2 (proj2 (Hp p _)))).
apply Zsqrt_ind.
exact H3.
refine (proj1 (proj2 (Hp p _))).
apply Zsqrt_ind.
refine (proj1 (Hp p _)).
apply Zsqrt_ind.
exact H2.
exact H1.
Qed.

Lemma Zsqrt_aux_correct :
  forall p,
  let (q, r) := Zsqrt_aux p in
  Zpos p = (q * q + r)%Z /\ (0 <= r <= 2 * q)%Z.
Proof.
intros p.
elim p using Zsqrt_ind ; clear p.
now repeat split.
now repeat split.
now repeat split.
intros p.
Opaque Zmult. simpl. Transparent Zmult.
destruct (Zsqrt_aux p) as (q, r).
intros (Hq, Hr).
change (Zpos p~0~0) with (4 * Zpos p)%Z.
change (Zpos p~0~1) with (4 * Zpos p + 1)%Z.
change (Zpos p~1~0) with (4 * Zpos p + 2)%Z.
change (Zpos p~1~1) with (4 * Zpos p + 3)%Z.
rewrite Hq. clear Hq.
repeat split.
generalize (Zlt_cases (4 * r - (4 * q + 1)) 0).
case Zlt_bool ; ( split ; [ ring | omega ] ).
generalize (Zlt_cases (4 * r + 2 - (4 * q + 1)) 0).
case Zlt_bool ; ( split ; [ ring | omega ] ).
generalize (Zlt_cases (4 * r + 1 - (4 * q + 1)) 0).
case Zlt_bool ; ( split ; [ ring | omega ] ).
generalize (Zlt_cases (4 * r + 3 - (4 * q + 1)) 0).
case Zlt_bool ; ( split ; [ ring | omega ] ).
Qed.

Definition Zsqrt p :=
  match p with
  | Zpos p => Zsqrt_aux p
  | _ => (0, 0)%Z
  end.

Theorem Zsqrt_correct :
  forall x,
  (0 <= x)%Z ->
  let (q, r) := Zsqrt x in
  x = (q * q + r)%Z /\ (0 <= r <= 2 * q)%Z.
Proof.
unfold Zsqrt.
intros [|p|p] Hx.
now repeat split.
apply Zsqrt_aux_correct.
now elim Hx.
Qed.

Variable beta : radix.
Notation bpow e := (bpow beta e).

(*
 * 1. Shift the mantissa so that it has at least 2p-1 digits;
 *    shift it one digit more if the new exponent is not even.
 * 2. Compute the square root s (at least p digits) of the new
 *    mantissa, and its remainder r.
 * 3. Current position: r == 0  =>  Eq,
 *                      r <= s  =>  Lo,
 *                      r >= s  =>  Up.
 *
 * Complexity is fine as long as p1 <= 2p-1.
 *)

Definition Fsqrt_aux prec m e :=
  let d := digits beta m in
  let s := Zmax (2 * prec - d) 0 in
  let e' := (e - s)%Z in
  let (s', e'') := if Zeven e' then (s, e') else (s + 1, e' - 1)%Z in
  let m' :=
    match s' with
    | Zpos p => (m * Zpower_pos (radix_val beta) p)%Z
    | _ => m
    end in
  let (q, r) := Zsqrt m' in
  let l :=
    if Zeq_bool r 0 then loc_Exact
    else loc_Inexact (if Zle_bool r q then Lt else Gt) in
  (q, e'', l).

Theorem Fsqrt_aux_correct :
  forall prec m e,
  (0 < m)%Z ->
  let '(m', e', l) := Fsqrt_aux prec m e in
  (prec <= digits beta m')%Z /\
  inbetween_float beta m' (Zdiv2 e') (sqrt (F2R (Float beta m e))) l.
Proof.
intros prec m e Hm.
unfold Fsqrt_aux.
set (d := digits beta m).
set (s := Zmax (2 * prec - d) 0).
(* . exponent *)
case_eq (if Zeven (e - s) then (s, (e - s)%Z) else ((s + 1)%Z, (e - s - 1)%Z)).
intros s' e' Hse.
assert (He: (Zeven e' = true /\ 0 <= s' /\ 2 * prec - d <= s' /\ s' + e' = e)%Z).
revert Hse.
case_eq (Zeven (e - s)) ; intros He Hse ; inversion Hse.
repeat split.
exact He.
unfold s.
apply Zle_max_r.
apply Zle_max_l.
ring.
assert (H: (Zmax (2 * prec - d) 0 <= s + 1)%Z).
fold s.
apply Zle_succ.
repeat split.
unfold Zminus at 1.
now rewrite Zeven_plus, He.
apply Zle_trans with (2 := H).
apply Zle_max_r.
apply Zle_trans with (2 := H).
apply Zle_max_l.
ring.
clear -Hm He.
destruct He as (He1, (He2, (He3, He4))).
(* . shift *)
set (m' := match s' with
  | Z0 => m
  | Zpos p => (m * Zpower_pos (radix_val beta) p)%Z
  | Zneg _ => m
  end).
assert (Hs: F2R (Float beta m' e') = F2R (Float beta m e) /\ (2 * prec <= digits beta m')%Z /\ (0 < m')%Z).
rewrite <- He4.
unfold m'.
destruct s' as [|p|p].
repeat split ; try easy.
fold d.
omega.
fold (Zpower (radix_val beta) (Zpos p)).
split.
replace (Zpos p) with (Zpos p + e' - e')%Z by ring.
rewrite <- F2R_change_exp.
apply (f_equal (fun v => F2R (Float beta m v))).
ring.
assert (0 < Zpos p)%Z by easy.
omega.
split.
rewrite digits_shift.
fold d.
omega.
apply sym_not_eq.
now apply Zlt_not_eq.
easy.
apply Zmult_lt_0_compat.
exact Hm.
apply Zpower_gt_0.
generalize (radix_prop beta).
omega.
easy.
now elim He2.
clearbody m'.
destruct Hs as (Hs1, (Hs2, Hs3)).
generalize (Zsqrt_correct m' (Zlt_le_weak _ _ Hs3)).
destruct (Zsqrt m') as (q, r).
intros (Hq, Hr).
rewrite <- Hs1. clear Hs1.
split.
(* . mantissa width *)
apply Zmult_le_reg_r with 2%Z.
easy.
rewrite Zmult_comm.
apply Zle_trans with (1 := Hs2).
rewrite Hq.
apply Zle_trans with (digits beta (q + q + q * q)).
apply digits_le.
rewrite <- Hq.
now apply Zlt_le_weak.
omega.
replace (digits beta q * 2)%Z with (digits beta q + digits beta q)%Z by ring.
apply digits_mult_strong.
omega.
omega.
(* . rounding *)
unfold inbetween_float, F2R. simpl.
rewrite sqrt_mult.
2: now apply (Z2R_le 0) ; apply Zlt_le_weak.
2: apply Rlt_le ; apply bpow_gt_0.
destruct (Zeven_ex e') as (e2, Hev).
rewrite He1, Zplus_0_r in Hev. clear He1.
rewrite Hev.
replace (Zdiv2 (2 * e2)) with e2 by now case e2.
replace (2 * e2)%Z with (e2 + e2)%Z by ring.
rewrite bpow_add.
fold (Rsqr (bpow e2)).
rewrite sqrt_Rsqr.
2: apply Rlt_le ; apply bpow_gt_0.
apply inbetween_mult_compat.
apply bpow_gt_0.
rewrite Hq.
case Zeq_bool_spec ; intros Hr'.
(* .. r = 0 *)
rewrite Hr', Zplus_0_r, mult_Z2R.
fold (Rsqr (Z2R q)).
rewrite sqrt_Rsqr.
now constructor.
apply (Z2R_le 0).
omega.
(* .. r <> 0 *)
constructor.
split.
(* ... bounds *)
apply Rle_lt_trans with (sqrt (Z2R (q * q))).
rewrite mult_Z2R.
fold (Rsqr (Z2R q)).
rewrite sqrt_Rsqr.
apply Rle_refl.
apply (Z2R_le 0).
omega.
apply sqrt_lt_1.
rewrite mult_Z2R.
apply Rle_0_sqr.
rewrite <- Hq.
apply (Z2R_le 0).
now apply Zlt_le_weak.
apply Z2R_lt.
omega.
apply Rlt_le_trans with (sqrt (Z2R ((q + 1) * (q + 1)))).
apply sqrt_lt_1.
rewrite <- Hq.
apply (Z2R_le 0).
now apply Zlt_le_weak.
rewrite mult_Z2R.
apply Rle_0_sqr.
apply Z2R_lt.
ring_simplify.
omega.
rewrite mult_Z2R.
fold (Rsqr (Z2R (q + 1))).
rewrite sqrt_Rsqr.
apply Rle_refl.
apply (Z2R_le 0).
omega.
(* ... location *)
rewrite Rcompare_half_r.
rewrite <- Rcompare_sqr.
replace ((2 * sqrt (Z2R (q * q + r))) * (2 * sqrt (Z2R (q * q + r))))%R
  with (4 * Rsqr (sqrt (Z2R (q * q + r))))%R by (unfold Rsqr ; ring).
rewrite Rsqr_sqrt.
change 4%R with (Z2R 4).
rewrite <- plus_Z2R, <- 2!mult_Z2R.
rewrite Rcompare_Z2R.
replace ((q + (q + 1)) * (q + (q + 1)))%Z with (4 * (q * q) + 4 * q + 1)%Z by ring.
generalize (Zle_cases r q).
case (Zle_bool r q) ; intros Hr''.
change (4 * (q * q + r) < 4 * (q * q) + 4 * q + 1)%Z.
omega.
change (4 * (q * q + r) > 4 * (q * q) + 4 * q + 1)%Z.
omega.
rewrite <- Hq.
apply (Z2R_le 0).
now apply Zlt_le_weak.
apply Rmult_le_pos.
now apply (Z2R_le 0 2).
apply sqrt_ge_0.
rewrite <- plus_Z2R.
apply (Z2R_le 0).
omega.
Qed.

End Fcalc_sqrt.
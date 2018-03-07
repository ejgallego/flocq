From Flocq Require Import Core Bracket Round Operations Div Sqrt.

Section Compute.

Variable beta : radix.

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.

Variable prec : Z.
Hypothesis Hprec : (0 < prec)%Z.
Hypothesis fexp_prec :
  forall e, (e - prec <= fexp e)%Z.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Variable choice : bool -> Z -> location -> Z.
Hypothesis rnd_choice :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  rnd x = cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l).

Lemma Rsgn_F2R :
  forall m e,
  Rlt_bool (F2R (Float beta m e)) 0 = Zlt_bool m 0.
Proof.
intros m e.
case Zlt_bool_spec ; intros H.
apply Rlt_bool_true.
now apply F2R_lt_0.
apply Rlt_bool_false.
now apply F2R_ge_0.
Qed.

Definition plus (x y : float beta) :=
  let (m, e) := Fplus x y in
  let s := Zlt_bool m 0 in
  let '(m', e', l) := truncate beta fexp (Zabs m, e, loc_Exact) in
  Float beta (cond_Zopp s (choice s m' l)) e'.

Theorem plus_correct :
  forall x y : float beta,
  round beta fexp rnd (F2R x + F2R y) = F2R (plus x y).
Proof.
intros x y.
unfold plus.
rewrite <- F2R_plus.
destruct (Fplus x y) as [m e].
rewrite (round_trunc_sign_any_correct beta fexp rnd choice rnd_choice _ (Zabs m) e loc_Exact).
3: now right.
destruct truncate as [[m' e'] l'].
apply (f_equal (fun s => F2R (Float beta (cond_Zopp s (choice s _ _)) _))).
apply Rsgn_F2R.
apply inbetween_Exact.
apply sym_eq, F2R_Zabs.
Qed.

Definition mult (x y : float beta) :=
  let (m, e) := Fmult x y in
  let s := Zlt_bool m 0 in
  let '(m', e', l) := truncate beta fexp (Zabs m, e, loc_Exact) in
  Float beta (cond_Zopp s (choice s m' l)) e'.

Theorem mult_correct :
  forall x y : float beta,
  round beta fexp rnd (F2R x * F2R y) = F2R (mult x y).
Proof.
intros x y.
unfold mult.
rewrite <- F2R_mult.
destruct (Fmult x y) as [m e].
rewrite (round_trunc_sign_any_correct beta fexp rnd choice rnd_choice _ (Zabs m) e loc_Exact).
3: now right.
destruct truncate as [[m' e'] l'].
apply (f_equal (fun s => F2R (Float beta (cond_Zopp s (choice s _ _)) _))).
apply Rsgn_F2R.
apply inbetween_Exact.
apply sym_eq, F2R_Zabs.
Qed.

Definition sqrt (x : float beta) :=
  if Zlt_bool 0 (Fnum x) then
    let '(m', e', l) := truncate beta fexp (Fsqrt fexp x) in
    Float beta (choice false m' l) e'
  else Float beta 0 0.

Theorem sqrt_correct :
  forall x : float beta,
  round beta fexp rnd (R_sqrt.sqrt (F2R x)) = F2R (sqrt x).
Proof.
intros x.
unfold sqrt.
case Zlt_bool_spec ; intros Hm.
generalize (Fsqrt_correct fexp x (F2R_gt_0 _ _ Hm)).
destruct Fsqrt as [[m' e'] l].
intros [Hs1 Hs2].
rewrite (round_trunc_sign_any_correct' beta fexp rnd choice rnd_choice _ m' e' l).
destruct truncate as [[m'' e''] l'].
now rewrite Rlt_bool_false by apply sqrt_ge_0.
now rewrite Rabs_pos_eq by apply sqrt_ge_0.
now left.
destruct (Req_dec (F2R x) 0) as [Hz|Hz].
rewrite Hz, sqrt_0, F2R_0.
now apply round_0.
unfold R_sqrt.sqrt.
destruct Rcase_abs as [H|H].
rewrite F2R_0.
now apply round_0.
destruct H as [H|H].
elim Rgt_not_le with (1 := H).
now apply F2R_le_0.
now elim Hz.
Qed.

Lemma Rsgn_div :
  forall x y : R,
  x <> 0%R -> y <> 0%R ->
  Rlt_bool (x / y) 0 = xorb (Rlt_bool x 0) (Rlt_bool y 0).
Proof.
intros x y Hx0 Hy0.
unfold Rdiv.
case (Rlt_bool_spec x) ; intros Hx ;
  case (Rlt_bool_spec y) ; intros Hy.
apply Rlt_bool_false.
rewrite <- Rmult_opp_opp.
apply Rlt_le, Rmult_lt_0_compat.
now apply Ropp_gt_lt_0_contravar.
apply Ropp_gt_lt_0_contravar.
now apply Rinv_lt_0_compat.
apply Rlt_bool_true.
apply Ropp_lt_cancel.
rewrite Ropp_0, <- Ropp_mult_distr_l_reverse.
apply Rmult_lt_0_compat.
now apply Ropp_gt_lt_0_contravar.
apply Rinv_0_lt_compat.
destruct Hy as [Hy|Hy].
easy.
now elim Hy0.
apply Rlt_bool_true.
apply Ropp_lt_cancel.
rewrite Ropp_0, <- Ropp_mult_distr_r_reverse.
apply Rmult_lt_0_compat.
destruct Hx as [Hx|Hx].
easy.
now elim Hx0.
apply Ropp_gt_lt_0_contravar.
now apply Rinv_lt_0_compat.
apply Rlt_bool_false.
apply Rlt_le, Rmult_lt_0_compat.
destruct Hx as [Hx|Hx].
easy.
now elim Hx0.
apply Rinv_0_lt_compat.
destruct Hy as [Hy|Hy].
easy.
now elim Hy0.
Qed.

Definition div (x y : float beta) :=
  if Zeq_bool (Fnum x) 0 then Float beta 0 0
  else
    let '(m, e, l) := truncate beta fexp (Fdiv fexp (Fabs x) (Fabs y)) in
    let s := xorb (Zlt_bool (Fnum x) 0) (Zlt_bool (Fnum y) 0) in
    Float beta (cond_Zopp s (choice s m l)) e.

Theorem div_correct :
  forall x y : float beta,
  F2R y <> 0%R ->
  round beta fexp rnd (F2R x / F2R y) = F2R (div x y).
Proof.
intros x y Hy.
unfold div.
case Zeq_bool_spec ; intros Hm.
  destruct x as [mx ex].
  simpl in Hm.
  rewrite Hm, 2!F2R_0.
  unfold Rdiv.
  rewrite Rmult_0_l.
  now apply round_0.
assert (0 < F2R (Fabs x))%R as Hx.
  destruct x as [mx ex].
  now apply F2R_gt_0, Z.abs_pos.
assert (0 < F2R (Fabs y))%R as Hy'.
  destruct y as [my ey].
  apply F2R_gt_0, Z.abs_pos.
  contradict Hy.
  rewrite Hy.
  apply F2R_0.
generalize (Fdiv_correct fexp _ _ Hx Hy').
destruct Fdiv as [[m e] l].
intros [Hs1 Hs2].
rewrite (round_trunc_sign_any_correct' beta fexp rnd choice rnd_choice _ m e l).
- destruct truncate as [[m' e'] l'].
  apply (f_equal (fun s => F2R (Float beta (cond_Zopp s (choice s _ _)) _))).
  rewrite Rsgn_div.
  apply f_equal2 ; apply Rsgn_F2R.
  contradict Hm.
  apply eq_0_F2R with (1 := Hm).
  exact Hy.
- unfold Rdiv.
  rewrite Rabs_mult, Rabs_Rinv by exact Hy.
  now rewrite <- 2!F2R_abs.
- left.
  rewrite <- cexp_abs.
  unfold Rdiv.
  rewrite Rabs_mult, Rabs_Rinv by exact Hy.
  now rewrite <- 2!F2R_abs.
Qed.

End Compute.

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.WelfareSecond

/-!
# Issues in the choice of a commodity space

SLP §15.3, pp. 458–462. Sequences are indexed by `t : ℕ`; in the book's ℓ_∞ example the periods
are `t = 1, 2, …`, so the book's period `t + 1` is index `t` here.

* **Exercise 15.7** (p. 460): (a) `ex_15_7a`: for `1 ≤ p < ∞` the positive orthant
  `lpPosOrthant p` of `ℓ_p` has empty interior; (b) `ex_15_7b`: the positive orthant of `ℓ_∞`
  has nonempty interior (it contains the ball of radius `1/2` about `(1, 1, …)`).
* The example on pp. 460–461: `S = ℓ_∞`, one consumer with `X = ℓ_∞⁺` and `u(x) = inf_t x_t`
  (`ex158X`, `ex158U`), one firm with `Y = {y : 0 ≤ y_t ≤ 1 + 1/t}` (`ex158Y`).
  * **Exercise 15.8** (`ex_15_8`): the economy satisfies Assumptions 15.1–15.5 (15.3 via
    `abs_ex158U_sub_le`, `|u x − u x′| ≤ ‖x − x′‖_∞`; 15.5 via `half_mem_interior_ex158Y`).
  * `ex158_paretoOptimal`: `x⁰ = y⁰ = (1 + 1/t)_t` is Pareto optimal; `ex158_exists_price`:
    Theorem 15.4 gives a nonzero supporting `φ ∈ ℓ_∞*`.
  * `ex158_price_vanishes_single`: every `φ` satisfying (2) and (3) vanishes on every unit
    sequence `e_t` (hence on all finitely supported sequences): "all its weight at infinity".
  * `ex158_no_inner_product`: no nonzero such `φ` has the form `φ(x) = Σ_t p_t x_t`
    (§15.3 (4)).
* **Exercise 15.9** (`ex_15_9`, p. 462): with the weighted norm (5),
  `‖x‖ = Σ_t β^t |x_t|`, the utility `u(x) = inf_t x_t` is not continuous at `(1, 1, …)` on the
  positive orthant (`weightedDist` is the distance of the norm (5)).
* NOTE to p. 462: `weighted_orthant_no_interior` — in the norm (5) no point of the positive
  orthant is interior; so no subset of it (in particular not `Y`) has an interior point
  (`weighted_no_interior_of_subset_orthant`). This is what the book needs; Exercise 15.6 itself
  is about the box `{|x_t| ≤ 1}`.
* NOTE to p. 462 (indexing): `hasSum_state_probabilities` — the probabilities `β^t(1 − β)` sum to
  `1` over `t = 0, 1, …`, so the stochastic re-reading of the example (indexed `t = 1, 2, …`) must
  use `β^{t−1}(1 − β)`.

**Corrections.** None to the exercises (the manual's solutions are correct). The p. 462 sentence
"by Exercise 15.6 the positive orthant has no interior point" cites the wrong result; the claim
is true and is proved directly here (`weighted_orthant_no_interior`).
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Set
open scoped ENNReal

/-- With a single firm the aggregate technology is that firm's production set. -/
theorem aggTech_of_unit {S : Type*} [NormedAddCommGroup S] (Y : Unit → Set S) :
    aggTech Y = Y () := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy ()
  · intro hw
    exact ⟨fun _ => w, fun _ => hw, by simp⟩

/-! ### Exercise 15.7 -/

/-- The positive orthant `ℓ_p⁺ = {x ∈ ℓ_p : x_t ≥ 0 for all t}`. -/
def lpPosOrthant (p : ℝ≥0∞) : Set (lp (fun _ : ℕ => ℝ) p) := {x | ∀ t, 0 ≤ x t}

/-- **Exercise 15.7(a)**: for `1 ≤ p < ∞` the positive orthant of `ℓ_p` has no interior point.
Given `x` and `ε > 0`, some coordinate has `|x_N| < ε/2` (as `x_t → 0`); lowering it to `−ε/2`
moves less than `ε` and leaves the orthant. -/
theorem ex_15_7a {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) : interior (lpPosOrthant p) = ∅ := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos (Fact.out : 1 ≤ p)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0.ne' hp
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  have hsum : Summable fun t => ‖x t‖ ^ p.toReal := (memℓp_gen_iff hpr).1 x.prop
  have hev : ∀ᶠ t in atTop, ‖x t‖ ^ p.toReal < (ε / 2) ^ p.toReal :=
    Filter.Tendsto.eventually_lt_const (Real.rpow_pos_of_pos (by linarith) _)
      hsum.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := hev.exists
  have hxN : |x N| < ε / 2 := by
    rw [← Real.norm_eq_abs]
    exact (Real.rpow_lt_rpow_iff (norm_nonneg _) (by linarith) hpr).1 hN
  rw [abs_lt] at hxN
  set c := x N + ε / 2 with hc
  set z := x - lp.single p N c with hz
  have hzball : z ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, hz, sub_sub_cancel_left, norm_neg, lp.norm_single hp0,
      Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have := hball hzball N
  simp only [hz, lp.coeFn_sub, Pi.sub_apply, lp.single_apply, Pi.single_eq_same] at this
  linarith

/-- **Exercise 15.7(b)**: the positive orthant of `ℓ_∞` has an interior point, `(1, 1, …)`: the
ball of radius `1/2` about it lies in the orthant. -/
theorem ex_15_7b : (1 : lp (fun _ : ℕ => ℝ) ∞) ∈ interior (lpPosOrthant ∞) := by
  refine mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨1 / 2, by norm_num, fun y hy t => ?_⟩)
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h := (lp.norm_apply_le_norm ENNReal.top_ne_zero (y - 1) t).trans_lt hy
  rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_one, Pi.one_apply, Real.norm_eq_abs,
    abs_lt] at h
  linarith [h.1]

/-! ### The ℓ_∞ example of pp. 460–461 and Exercise 15.8 -/

/-- Consumption set of the p. 460 example: `X = ℓ_∞⁺`. -/
def ex158X : Unit → Set (lp (fun _ : ℕ => ℝ) ∞) := fun _ => lpPosOrthant ∞

/-- Production set of the p. 460 example: `Y = {y : 0 ≤ y_t ≤ 1 + 1/t}` (book period `t + 1` is
index `t`). -/
def ex158Y : Unit → Set (lp (fun _ : ℕ => ℝ) ∞) :=
  fun _ => {y | ∀ t, 0 ≤ y t ∧ y t ≤ 1 + 1 / ((t : ℝ) + 1)}

/-- Utility of the p. 460 example, §15.3 (1): `u(x) = inf_t x_t`. -/
noncomputable def ex158U : Unit → lp (fun _ : ℕ => ℝ) ∞ → ℝ := fun _ x => ⨅ t, x t

/-- The coordinates of a bounded sequence are bounded below. -/
theorem bddBelow_range_lpInfty (x : lp (fun _ : ℕ => ℝ) ∞) : BddBelow (range fun t => x t) := by
  refine ⟨-‖x‖, ?_⟩
  rintro _ ⟨t, rfl⟩
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero x t
  rw [Real.norm_eq_abs] at this
  linarith [neg_abs_le (x t)]

/-- `inf_t x_t ≤ x_s`. -/
theorem ex158U_le (x : lp (fun _ : ℕ => ℝ) ∞) (s : ℕ) : ex158U () x ≤ x s :=
  ciInf_le (bddBelow_range_lpInfty x) s

/-- A lower bound for every coordinate is a lower bound for `inf_t x_t`. -/
theorem le_ex158U {x : lp (fun _ : ℕ => ℝ) ∞} {c : ℝ} (h : ∀ t, c ≤ x t) : c ≤ ex158U () x :=
  le_ciInf h

/-- If `x_t ≤ 1 + 1/(t + 1)` for all `t` then `inf_t x_t ≤ 1`. -/
theorem ex158U_le_one {x : lp (fun _ : ℕ => ℝ) ∞} (h : ∀ t, x t ≤ 1 + 1 / ((t : ℝ) + 1)) :
    ex158U () x ≤ 1 := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  linarith [ex158U_le x n, h n]

/-- `|inf x − inf x′| ≤ ‖x − x′‖_∞` (the one-line fact behind the manual's Assumption 15.3
argument). -/
theorem abs_ex158U_sub_le (x x' : lp (fun _ : ℕ => ℝ) ∞) :
    |ex158U () x - ex158U () x'| ≤ ‖x - x'‖ := by
  have hcoord : ∀ t, |x t - x' t| ≤ ‖x - x'‖ := fun t => by
    have := lp.norm_apply_le_norm ENNReal.top_ne_zero (x - x') t
    rwa [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] at this
  rw [abs_le]
  constructor
  · have : ex158U () x' - ‖x - x'‖ ≤ ex158U () x := le_ex158U fun t => by
      linarith [ex158U_le x' t, (abs_le.1 (hcoord t)).1]
    linarith
  · have : ex158U () x - ‖x - x'‖ ≤ ex158U () x' := le_ex158U fun t => by
      linarith [ex158U_le x t, (abs_le.1 (hcoord t)).2]
    linarith

/-- The constant sequence `(1/2, 1/2, …)` is an interior point of `Y` (radius `1/2`). -/
theorem half_mem_interior_ex158Y :
    ((1 / 2 : ℝ) • (1 : lp (fun _ : ℕ => ℝ) ∞)) ∈ interior (ex158Y ()) := by
  refine mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨1 / 2, by norm_num, fun w hw t => ?_⟩)
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h := (lp.norm_apply_le_norm ENNReal.top_ne_zero (w - (1 / 2 : ℝ) • 1) t).trans_lt hw
  rw [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, lp.infty_coeFn_one,
    Pi.one_apply, smul_eq_mul, mul_one, Real.norm_eq_abs, abs_lt] at h
  have : (0 : ℝ) ≤ 1 / ((t : ℝ) + 1) := by positivity
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **Exercise 15.8** (p. 460): the economy `S = ℓ_∞`, `X = ℓ_∞⁺`, `u(x) = inf_t x_t`,
`Y = {0 ≤ y_t ≤ 1 + 1/t}` satisfies Assumptions 15.1–15.5. -/
theorem ex_15_8 :
    Assumption15_1 ex158X ∧ Assumption15_2 ex158X ex158U ∧ Assumption15_3 ex158X ex158U ∧
    Assumption15_4 ex158Y ∧ Assumption15_5 (lp (fun _ : ℕ => ℝ) ∞) ex158Y := by
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, ?_, ?_⟩
  · intro x hx x' hx' a b ha hb _ t
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx t
    have := hx' t
    positivity
  · intro z _ z' _ hlt θ hθ0 hθ1
    have hlow : θ * ex158U () z + (1 - θ) * ex158U () z' ≤ ex158U () (θ • z + (1 - θ) • z') :=
      le_ex158U fun t => by
        simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h1 := mul_le_mul_of_nonneg_left (ex158U_le z t) hθ0.le
        have h2 := mul_le_mul_of_nonneg_left (ex158U_le z' t) (sub_nonneg.2 hθ1.le)
        linarith
    nlinarith
  · refine Continuous.continuousOn ?_
    refine (LipschitzWith.of_dist_le_mul fun x x' => ?_).continuous (K := 1)
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    exact abs_ex158U_sub_le x x'
  · rw [Assumption15_4, aggTech_of_unit]
    intro y hy y' hy' a b ha hb hab t
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨h1, h2⟩ := hy t
    obtain ⟨h3, h4⟩ := hy' t
    constructor
    · positivity
    · have := mul_le_mul_of_nonneg_left h2 ha
      have := mul_le_mul_of_nonneg_left h4 hb
      nlinarith
  · left
    rw [aggTech_of_unit]
    exact ⟨_, half_mem_interior_ex158Y⟩

/-- The Pareto-optimal allocation of the example: `x⁰ = y⁰ = (1 + 1/t)_t`. -/
noncomputable def ex158x0 : lp (fun _ : ℕ => ℝ) ∞ :=
  ⟨fun t => 1 + 1 / ((t : ℝ) + 1), memℓp_infty_iff.2 ⟨2, by
    rintro _ ⟨t, rfl⟩
    have h0 : (0 : ℝ) ≤ 1 / ((t : ℝ) + 1) := by positivity
    have h1 : 1 / ((t : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    linarith⟩⟩

/-- Coordinates of `x⁰`. -/
theorem ex158x0_apply (t : ℕ) : ex158x0 t = 1 + 1 / ((t : ℝ) + 1) := rfl

/-- `u(x⁰) = 1`. -/
theorem ex158U_x0 : ex158U () ex158x0 = 1 := by
  refine le_antisymm (ex158U_le_one fun t => le_rfl) (le_ex158U fun t => ?_)
  rw [ex158x0_apply]
  have : (0 : ℝ) ≤ 1 / ((t : ℝ) + 1) := by positivity
  linarith

/-- The allocation `x⁰ = y⁰ = (1 + 1/t)_t` of the example is Pareto optimal (any feasible `x`
has `x_t ≤ 1 + 1/t`, so `u(x) ≤ 1 = u(x⁰)`). -/
theorem ex158_paretoOptimal :
    ParetoOptimal ex158X ex158U ex158Y (fun _ => ex158x0) (fun _ => ex158x0) := by
  have hpos : ∀ t, 0 ≤ ex158x0 t := fun t => by
    rw [ex158x0_apply]
    positivity
  refine ⟨⟨fun _ => hpos, fun _ t => ⟨hpos t, le_rfl⟩, by simp⟩, ?_⟩
  rintro ⟨x', y', ⟨-, hy', hsum⟩, -, i, hi⟩
  have hxy : x' () = y' () := by simpa [sub_eq_zero] using hsum
  have hle : ex158U () (x' ()) ≤ 1 := ex158U_le_one fun t => by
    rw [hxy]
    exact (hy' () t).2
  cases i
  rw [ex158U_x0] at hi
  linarith

/-- Consumer nonsatiation at `x⁰`: `x̂ = (2, 2, …)` has `u(x̂) = 2 > 1 = u(x⁰)`. -/
theorem ex158_nonsatiated :
    (2 : ℝ) • (1 : lp (fun _ : ℕ => ℝ) ∞) ∈ ex158X () ∧
    ex158U () ex158x0 < ex158U () ((2 : ℝ) • (1 : lp (fun _ : ℕ => ℝ) ∞)) := by
  have hc : ∀ t, ((2 : ℝ) • (1 : lp (fun _ : ℕ => ℝ) ∞)) t = 2 := fun t => by
    rw [lp.coeFn_smul, Pi.smul_apply, lp.infty_coeFn_one, Pi.one_apply, smul_eq_mul, mul_one]
  refine ⟨fun t => by rw [hc]; norm_num, ?_⟩
  rw [ex158U_x0]
  have : (2 : ℝ) ≤ ex158U () ((2 : ℝ) • 1) := le_ex158U fun t => (hc t).ge
  linarith

/-- By Theorem 15.4 the example has a nonzero supporting price `φ ∈ ℓ_∞*` satisfying §15.3 (2)
and (3). -/
theorem ex158_exists_price : ∃ φ : StrongDual ℝ (lp (fun _ : ℕ => ℝ) ∞), φ ≠ 0 ∧
    SupportsAllocation ex158X ex158U ex158Y (fun _ => ex158x0) (fun _ => ex158x0) φ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ex_15_8
  exact theorem_15_4 h1 h2 h3 h4 h5 ex158_paretoOptimal ex158_nonsatiated.1 ex158_nonsatiated.2

/-- The unit sequence `e_t ∈ ℓ_∞` (`1` in position `t`, `0` elsewhere). -/
noncomputable def ex158e (t : ℕ) : lp (fun _ : ℕ => ℝ) ∞ := lp.single ∞ t 1

/-- Coordinates of `e_t`. -/
theorem ex158e_apply (t s : ℕ) : ex158e t s = if s = t then 1 else 0 := by
  rcases eq_or_ne s t with rfl | hs
  · simp [ex158e]
  · simp [ex158e, hs]

/-- Coordinates of `x⁰ − c e_t`. -/
theorem ex158x0_sub_single_apply (c : ℝ) (t s : ℕ) :
    (ex158x0 - c • ex158e t) s = if s = t then ex158x0 t - c else ex158x0 s := by
  rw [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, ex158e_apply, smul_eq_mul]
  split_ifs with hs
  · rw [hs, mul_one]
  · rw [mul_zero, sub_zero]

/-- **All weight at infinity** (p. 461): any `φ` satisfying §15.3 (2) and (3) vanishes on every
unit sequence `e_t`. From (3) with `y⁰ − y⁰_t e_t ∈ Y`, `φ(e_t) ≥ 0`; from (2) with
`x⁰ − e_t/(t + 1)`, which has utility `1 = u(x⁰)`, `φ(e_t) ≤ 0`. -/
theorem ex158_price_vanishes_single {φ : StrongDual ℝ (lp (fun _ : ℕ => ℝ) ∞)}
    (hφ : SupportsAllocation ex158X ex158U ex158Y (fun _ => ex158x0) (fun _ => ex158x0) φ)
    (t : ℕ) : φ (ex158e t) = 0 := by
  have ht0 : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
  -- the firm: profit maximisation
  have hY : ex158x0 - ex158x0 t • ex158e t ∈ ex158Y () := fun s => by
    rw [ex158x0_sub_single_apply]
    split_ifs with hs
    · simp only [sub_self, le_refl, true_and]
      positivity
    · exact ⟨by rw [ex158x0_apply]; positivity, le_rfl⟩
  have hfirm := hφ.2 () _ hY
  beta_reduce at hfirm
  rw [map_sub, map_smul, smul_eq_mul, ex158x0_apply] at hfirm
  have hge : 0 ≤ φ (ex158e t) := by
    by_contra hneg
    push Not at hneg
    nlinarith
  -- the consumer: cost minimisation over the weakly preferred set
  have hlow : ∀ s, 1 ≤ (ex158x0 - (1 / ((t : ℝ) + 1)) • ex158e t) s := fun s => by
    rw [ex158x0_sub_single_apply]
    split_ifs
    · rw [ex158x0_apply]
      linarith
    · rw [ex158x0_apply]
      have : (0 : ℝ) ≤ 1 / ((s : ℝ) + 1) := by positivity
      linarith
  have hX : ex158x0 - (1 / ((t : ℝ) + 1)) • ex158e t ∈ ex158X () := fun s =>
    le_trans zero_le_one (hlow s)
  have hcons := hφ.1 () _ hX (by beta_reduce; rw [ex158U_x0]; exact le_ex158U hlow)
  beta_reduce at hcons
  rw [map_sub, map_smul, smul_eq_mul] at hcons
  have hle : φ (ex158e t) ≤ 0 := by
    by_contra hpos
    push Not at hpos
    nlinarith
  linarith

/-- **No inner-product representation** (§15.3 (4), p. 461): no nonzero `φ` satisfying (2) and
(3) has the form `φ(x) = Σ_t p_t x_t` for all `x ∈ ℓ_∞`. -/
theorem ex158_no_inner_product {φ : StrongDual ℝ (lp (fun _ : ℕ => ℝ) ∞)} (hφ0 : φ ≠ 0)
    (hφ : SupportsAllocation ex158X ex158U ex158Y (fun _ => ex158x0) (fun _ => ex158x0) φ) :
    ¬ ∃ p : ℕ → ℝ, ∀ x : lp (fun _ : ℕ => ℝ) ∞, HasSum (fun t => p t * x t) (φ x) := by
  rintro ⟨p, hp⟩
  have hpt : ∀ t, p t = 0 := fun t => by
    have h1 := hp (ex158e t)
    have h2 : HasSum (fun s => p s * (ex158e t) s) (p t) := by
      convert hasSum_single t (f := fun s => p s * (ex158e t) s) (fun s hs => by
        simp [ex158e_apply, hs]) using 1
      simp [ex158e_apply]
    rw [← h1.unique h2, ex158_price_vanishes_single hφ t]
  refine hφ0 (ContinuousLinearMap.ext fun x => ?_)
  have := hp x
  simp only [hpt, zero_mul] at this
  rw [zero_apply]
  exact this.unique hasSum_zero

/-! ### Exercise 15.9 and the weighted norm (5) -/

/-- The distance of the weighted norm §15.3 (5): `Σ_t β^t |x_t − x′_t|`. -/
noncomputable def weightedDist (β : ℝ) (x x' : ℕ → ℝ) : ℝ := ∑' t, β ^ t * |x t - x' t|

/-- The weighted distance between sequences that differ only at `T`. -/
theorem weightedDist_update (β : ℝ) (x : ℕ → ℝ) (T : ℕ) (a : ℝ) :
    weightedDist β x (Function.update x T a) = β ^ T * |x T - a| := by
  rw [weightedDist, tsum_eq_single T fun t ht => by simp [Function.update_of_ne ht]]
  simp

/-- Summability (membership of the space with norm (5)) is preserved by changing one
coordinate. -/
theorem summable_weighted_update {β : ℝ} {x : ℕ → ℝ} (hx : Summable fun t => β ^ t * |x t|)
    (T : ℕ) (a : ℝ) : Summable fun t => β ^ t * |Function.update x T a t| := by
  have : (fun t => β ^ t * |Function.update x T a t|) =
      Function.update (fun t => β ^ t * |x t|) T (β ^ T * |a|) := by
    funext t
    rcases eq_or_ne t T with rfl | ht
    · simp
    · simp [Function.update_of_ne ht]
  rw [this]
  exact hx.update T _

/-- **Exercise 15.9** (p. 462): `u(x) = inf_t x_t` is not continuous at `1 = (1, 1, …)` on the
positive orthant of the space with norm (5), `Σ_t β^t |x_t| < ∞`: for `ε = 1/2` and every
`δ > 0`, lowering one far-out coordinate to `1/2` gives `x′` within `δ` of `1` with
`|u(1) − u(x′)| = 1/2`. -/
theorem ex_15_9 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Summable (fun t => β ^ t * |(1 : ℝ)|) ∧
    ∃ ε > 0, ∀ δ > 0, ∃ x' : ℕ → ℝ, (∀ t, 0 ≤ x' t) ∧ Summable (fun t => β ^ t * |x' t|) ∧
      weightedDist β (fun _ => 1) x' < δ ∧ ε ≤ |(⨅ _ : ℕ, (1 : ℝ)) - ⨅ t, x' t| := by
  have hgeo : Summable fun t : ℕ => β ^ t * |(1 : ℝ)| := by
    simpa using summable_geometric_of_lt_one hβ0.le hβ1
  refine ⟨hgeo, 1 / 2, by norm_num, fun δ hδ => ?_⟩
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hδ hβ1
  set x' := Function.update (fun _ : ℕ => (1 : ℝ)) T (1 / 2) with hx'
  have hcoord : ∀ t, 1 / 2 ≤ x' t := fun t => by
    rcases eq_or_ne t T with rfl | ht
    · simp [hx']
    · norm_num [hx', Function.update_of_ne ht]
  refine ⟨x', fun t => le_trans (by norm_num) (hcoord t), summable_weighted_update hgeo T _, ?_,
    ?_⟩
  · rw [hx', weightedDist_update]
    norm_num
    linarith [pow_pos hβ0 T]
  · have hinf : ⨅ t, x' t = 1 / 2 := le_antisymm
      (by
        have := ciInf_le (⟨1 / 2, by rintro _ ⟨t, rfl⟩; exact hcoord t⟩ :
          BddBelow (range x')) T
        simpa [hx'] using this)
      (le_ciInf hcoord)
    rw [ciInf_const, hinf]
    norm_num [abs_of_pos]

/-- **NOTE to p. 462**: in the norm (5) no point `x` of the positive orthant is interior: for every
`δ > 0` some `z` of the space within distance `δ` of `x` has a negative coordinate. -/
theorem weighted_orthant_no_interior {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℕ → ℝ}
    (hx : Summable fun t => β ^ t * |x t|) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z : ℕ → ℝ, Summable (fun t => β ^ t * |z t|) ∧ weightedDist β x z < δ ∧ ∃ t, z t < 0 := by
  have h1 : ∀ᶠ t in atTop, β ^ t * |x t| < δ / 2 :=
    Filter.Tendsto.eventually_lt_const (by linarith) hx.tendsto_atTop_zero
  have h2 : ∀ᶠ t in atTop, β ^ t < δ / 2 :=
    Filter.Tendsto.eventually_lt_const (by linarith)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1)
  obtain ⟨T, hT1, hT2⟩ := (h1.and h2).exists
  refine ⟨Function.update x T (x T - (|x T| + 1)), summable_weighted_update hx T _, ?_, T, ?_⟩
  · rw [weightedDist_update, sub_sub_cancel, abs_of_pos (by positivity), mul_add, mul_one]
    linarith
  · simp only [Function.update_self]
    linarith [le_abs_self (x T)]

/-- Consequently, in the norm (5) no subset of the positive orthant (for instance the
technology `Y = {0 ≤ y_t ≤ 1 + 1/t}`) has an interior point, so Assumption 15.5 fails there. -/
theorem weighted_no_interior_of_subset_orthant {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {B : Set (ℕ → ℝ)} (hB : ∀ y ∈ B, ∀ t, 0 ≤ y t) {x : ℕ → ℝ}
    (hx : Summable fun t => β ^ t * |x t|) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z : ℕ → ℝ, Summable (fun t => β ^ t * |z t|) ∧ weightedDist β x z < δ ∧ z ∉ B := by
  obtain ⟨z, hz, hd, t, ht⟩ := weighted_orthant_no_interior hβ0 hβ1 hx hδ
  exact ⟨z, hz, hd, fun hzB => (hB z hzB t).not_gt ht⟩

/-- **NOTE to p. 462** (indexing): the state probabilities `(1 − β)β^t` sum to `1` over
`t = 0, 1, 2, …`; with the example's periods `t = 1, 2, …` they must be `(1 − β)β^{t−1}`. -/
theorem hasSum_state_probabilities {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun t : ℕ => (1 - β) * β ^ t) 1 := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left (1 - β)
  rwa [mul_inv_cancel₀ (by linarith)] at h

end StokeyLucasPrescott.ParetoOptimaEquilibria

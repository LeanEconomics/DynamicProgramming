/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Tactic.LinearCombination

/-!
# Deterministic Radner economies with one stock

The setting of Examples 13.6.1 and 13.6.2 and Exercises 13.5–13.6 (Miao, §13.6, pp. 441–444,
and §13.9, p. 453): a deterministic economy with finitely many agents `ι` and one long-lived
asset (stock or money) with ex-dividend price `p_t` and dividend `d_t`.

* `bp_detBudget`: agent `i`'s sequential budget constraints (13.11),
  `c_0 + p_0θ_0 ≤ (p_0 + d_0)θ_{−1} + y_0` and `c_t + p_tθ_t ≤ (p_t + d_t)θ_{t−1} + y_t`, with
  positive consumption and a portfolio constraint `con t p_t θ_t` (a borrowing constraint
  (13.14), a short-sales constraint (13.15), …).
* `BPDetEqm` (Definition 13.4.1): budget feasibility, optimality among admissible feasible
  plans, and market clearing `∑ᵢ θⁱ_t = θ̄_{−1}`, `∑ᵢ cⁱ_t = ȳ_t + θ̄_{−1} d_t`.
* `bp_detU β u c = ∑ βᵗ u(c_t)`; a plan is admissible (`bp_detAdm`) when this series converges.
* `bp_det_sufficiency`: the Euler–Kuhn–Tucker sufficiency argument used to verify optimality in
  the examples: with a supergradient `u'`, multipliers `λ_t = βᵗ u'(c_t)`,
  `(θ'_t − θ_t)(λ_{t+1}(p_{t+1} + d_{t+1}) − λ_t p_t) ≤ 0` for every feasible `θ'` and a
  vanishing boundary term, `c` beats every admissible feasible `c'`.
* `bp_log_supergradient`, `bp_crra_supergradient`: `log` and `c^{1−γ}/(1−γ)` (`γ > 0`, `γ ≠ 1`)
  satisfy `u(x') ≤ u(x) + u'(x)(x' − x)`.
* `bp_tail f t = ∑_{s>t} f_s` and its elementary properties.
-/

open Filter Topology

namespace Miao.CompleteMarkets

/-- Agent `i`'s budget set in the deterministic one-asset economy (Miao, (13.11)): positive
consumption, the date-0 and date-`t` budget constraints, and the portfolio constraint. -/
def bp_detBudget (p d y : ℕ → ℝ) (θ0 : ℝ) (con : ℕ → ℝ → ℝ → Prop) (c θ : ℕ → ℝ) : Prop :=
  (∀ t, 0 < c t) ∧ c 0 + p 0 * θ 0 ≤ (p 0 + d 0) * θ0 + y 0 ∧
    (∀ t, c (t + 1) + p (t + 1) * θ (t + 1) ≤ (p (t + 1) + d (t + 1)) * θ t + y (t + 1)) ∧
    ∀ t, con t (p t) (θ t)

variable {ι : Type*} [Fintype ι] (U : ι → (ℕ → ℝ) → ℝ) (adm : ι → (ℕ → ℝ) → Prop)
  (y : ι → ℕ → ℝ) (d : ℕ → ℝ) (θ0 : ι → ℝ) (con : ι → ℕ → ℝ → ℝ → Prop) (c θ : ι → ℕ → ℝ)
  (p : ℕ → ℝ) in
/-- A Radner equilibrium of the deterministic one-asset economy (Miao, Definition 13.4.1,
p. 427): each agent's plan is feasible and best among admissible feasible plans, and the asset
and goods markets clear. -/
structure BPDetEqm : Prop where
  budget : ∀ i, bp_detBudget p d (y i) (θ0 i) (con i) (c i) (θ i)
  adm_self : ∀ i, adm i (c i)
  optimal : ∀ i c' θ', bp_detBudget p d (y i) (θ0 i) (con i) c' θ' → adm i c' →
    U i c' ≤ U i (c i)
  clear_assets : ∀ t, ∑ i, θ i t = ∑ i, θ0 i
  clear_goods : ∀ t, ∑ i, c i t = ∑ i, y i t + (∑ i, θ0 i) * d t

/-- Discounted utility `∑ βᵗ u(c_t)`. -/
noncomputable def bp_detU (β : ℝ) (u : ℝ → ℝ) (c : ℕ → ℝ) : ℝ := ∑' t, β ^ t * u (c t)

/-- A consumption plan is admissible when its discounted utility converges. -/
def bp_detAdm (β : ℝ) (u : ℝ → ℝ) (c : ℕ → ℝ) : Prop := Summable (fun t => β ^ t * u (c t))

/-- The tail sum `∑_{s > t} f_s`. -/
noncomputable def bp_tail (f : ℕ → ℝ) (t : ℕ) : ℝ := ∑' k, f (k + (t + 1))

theorem bp_tail_succ (f : ℕ → ℝ) (hf : Summable f) (t : ℕ) :
    bp_tail f t = f (t + 1) + bp_tail f (t + 1) := by
  unfold bp_tail
  have hs : Summable (fun k => f (k + (t + 1))) := (summable_nat_add_iff (t + 1)).2 hf
  rw [hs.tsum_eq_zero_add]
  simp only [zero_add]
  congr 1
  refine tsum_congr (fun k => ?_)
  congr 1
  omega

theorem bp_sum_add_tail (f : ℕ → ℝ) (hf : Summable f) (t : ℕ) :
    ∑ s ∈ Finset.range (t + 1), f s + bp_tail f t = ∑' s, f s :=
  hf.sum_add_tsum_nat_add (t + 1)

theorem bp_tail_tendsto (f : ℕ → ℝ) : Tendsto (bp_tail f) atTop (𝓝 0) :=
  (tendsto_add_atTop_iff_nat 1).2 (tendsto_sum_nat_add f)

theorem bp_tail_nonneg (f : ℕ → ℝ) (hf : ∀ t, 0 ≤ f t) (t : ℕ) : 0 ≤ bp_tail f t :=
  tsum_nonneg (fun _ => hf _)

/-- The partial-sum form of the sufficiency argument: summing
`λ_t(c'_t − c_t) ≤ λ_t((p_t + d_t)(θ'_{t−1} − θ_{t−1}) − p_t(θ'_t − θ_t))` by parts. -/
theorem bp_det_partial (lam p d y : ℕ → ℝ) (θ0 : ℝ) (c θ c' θ' : ℕ → ℝ)
    (hlam : ∀ t, 0 ≤ lam t)
    (hb0 : c 0 + p 0 * θ 0 = (p 0 + d 0) * θ0 + y 0)
    (hb : ∀ t, c (t + 1) + p (t + 1) * θ (t + 1) = (p (t + 1) + d (t + 1)) * θ t + y (t + 1))
    (hb0' : c' 0 + p 0 * θ' 0 ≤ (p 0 + d 0) * θ0 + y 0)
    (hb' : ∀ t, c' (t + 1) + p (t + 1) * θ' (t + 1) ≤
      (p (t + 1) + d (t + 1)) * θ' t + y (t + 1)) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), lam t * (c' t - c t) ≤
      ∑ t ∈ Finset.range n,
        (θ' t - θ t) * (lam (t + 1) * (p (t + 1) + d (t + 1)) - lam t * p t) -
      lam n * p n * (θ' n - θ n) := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, zero_sub]
    have h : c' 0 - c 0 ≤ -(p 0 * (θ' 0 - θ 0)) := by linarith
    have := mul_le_mul_of_nonneg_left h (hlam 0)
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun t => (θ' t - θ t) *
      (lam (t + 1) * (p (t + 1) + d (t + 1)) - lam t * p t))]
    have h : c' (n + 1) - c (n + 1) ≤
        (p (n + 1) + d (n + 1)) * (θ' n - θ n) - p (n + 1) * (θ' (n + 1) - θ (n + 1)) := by
      linarith [hb n, hb' n]
    have h1 := mul_le_mul_of_nonneg_left h (hlam (n + 1))
    linear_combination ih + h1

/-- The Euler–Kuhn–Tucker sufficiency argument (used in Examples 13.6.1–13.6.2 and Exercises
13.5–13.6). Let `u'` be a supergradient of `u` on `(0, ∞)`, `λ_t = βᵗu'(c_t) ≥ 0`, let `(c, θ)`
satisfy the budget constraints with equality and `(c', θ')` satisfy them. If
`(θ'_t − θ_t)(λ_{t+1}(p_{t+1} + d_{t+1}) − λ_t p_t) ≤ 0` for all `t` (the Euler equation with
complementary slackness) and the boundary term `−λ_T p_T(θ'_T − θ_T)` is bounded by a sequence
tending to zero, then `∑ βᵗu(c'_t) ≤ ∑ βᵗu(c_t)`. -/
theorem bp_det_sufficiency (β : ℝ) (hβ : 0 ≤ β) (u u' : ℝ → ℝ)
    (hsg : ∀ x x', 0 < x → 0 < x' → u x' ≤ u x + u' x * (x' - x))
    (p d y : ℕ → ℝ) (θ0 : ℝ) (c θ c' θ' : ℕ → ℝ)
    (hc : ∀ t, 0 < c t) (hc' : ∀ t, 0 < c' t) (hu' : ∀ t, 0 ≤ u' (c t))
    (hb0 : c 0 + p 0 * θ 0 = (p 0 + d 0) * θ0 + y 0)
    (hb : ∀ t, c (t + 1) + p (t + 1) * θ (t + 1) = (p (t + 1) + d (t + 1)) * θ t + y (t + 1))
    (hb0' : c' 0 + p 0 * θ' 0 ≤ (p 0 + d 0) * θ0 + y 0)
    (hb' : ∀ t, c' (t + 1) + p (t + 1) * θ' (t + 1) ≤
      (p (t + 1) + d (t + 1)) * θ' t + y (t + 1))
    (hKT : ∀ t, (θ' t - θ t) * (β ^ (t + 1) * u' (c (t + 1)) * (p (t + 1) + d (t + 1)) -
      β ^ t * u' (c t) * p t) ≤ 0)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hbd : ∀ T, -(β ^ T * u' (c T) * p T * (θ' T - θ T)) ≤ e T)
    (hs : Summable (fun t => β ^ t * u (c t))) (hs' : Summable (fun t => β ^ t * u (c' t))) :
    ∑' t, β ^ t * u (c' t) ≤ ∑' t, β ^ t * u (c t) := by
  set lam : ℕ → ℝ := fun t => β ^ t * u' (c t) with hlam
  have hlam0 : ∀ t, 0 ≤ lam t := fun t => mul_nonneg (pow_nonneg hβ t) (hu' t)
  have hpart := bp_det_partial lam p d y θ0 c θ c' θ' hlam0 hb0 hb hb0' hb'
  have hbound : ∀ n, ∑ t ∈ Finset.range (n + 1), (β ^ t * u (c' t) - β ^ t * u (c t)) ≤ e n := by
    intro n
    have h1 : ∑ t ∈ Finset.range (n + 1), (β ^ t * u (c' t) - β ^ t * u (c t)) ≤
        ∑ t ∈ Finset.range (n + 1), lam t * (c' t - c t) := by
      refine Finset.sum_le_sum (fun t _ => ?_)
      have := mul_le_mul_of_nonneg_left (hsg (c t) (c' t) (hc t) (hc' t)) (pow_nonneg hβ t)
      simp only [hlam]
      linarith
    have h2 : ∑ t ∈ Finset.range n,
        (θ' t - θ t) * (lam (t + 1) * (p (t + 1) + d (t + 1)) - lam t * p t) ≤ 0 :=
      Finset.sum_nonpos (fun t _ => hKT t)
    have h3 := hpart n
    have h4 := hbd n
    simp only [hlam] at h3 h2
    linarith
  have hlim : Tendsto (fun n => ∑ t ∈ Finset.range (n + 1),
      (β ^ t * u (c' t) - β ^ t * u (c t))) atTop
      (𝓝 (∑' t, β ^ t * u (c' t) - ∑' t, β ^ t * u (c t))) := by
    rw [← hs'.tsum_sub hs]
    exact (tendsto_add_atTop_iff_nat 1).2 (hs'.sub hs).hasSum.tendsto_sum_nat
  have := le_of_tendsto_of_tendsto' hlim he hbound
  linarith

/-- `log` has the supergradient `1/x`: `log x' ≤ log x + (x' − x)/x`. -/
theorem bp_log_supergradient (x x' : ℝ) (hx : 0 < x) (hx' : 0 < x') :
    Real.log x' ≤ Real.log x + 1 / x * (x' - x) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx' hx)
  rw [Real.log_div hx'.ne' hx.ne'] at h
  have : x' / x - 1 = 1 / x * (x' - x) := by field_simp
  linarith

/-- The one-dimensional core of the CRRA supergradient: `(r^a − 1)/a ≤ r − 1` for `r > 0`,
`a < 1`, `a ≠ 0`. -/
theorem bp_rpow_sub_one_div_le (r a : ℝ) (hr : 0 < r) (ha1 : a < 1) (ha0 : a ≠ 0) :
    (r ^ a - 1) / a ≤ r - 1 := by
  rcases lt_or_gt_of_ne ha0 with ha | ha
  · -- `a < 0`: weighted AM–GM with weights `1/(1−a)`, `−a/(1−a)` on `r^a`, `r`
    have h1a : 0 < 1 - a := by linarith
    have hw1 : 0 ≤ 1 / (1 - a) := by positivity
    have hw2 : 0 ≤ -a / (1 - a) := div_nonneg (by linarith) h1a.le
    have hsum : 1 / (1 - a) + -a / (1 - a) = 1 := by field_simp; ring
    have hgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2
      (Real.rpow_nonneg hr.le a) hr.le hsum
    have hlhs : (r ^ a) ^ (1 / (1 - a)) * r ^ (-a / (1 - a)) = 1 := by
      rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr]
      have : a * (1 / (1 - a)) + -a / (1 - a) = 0 := by field_simp; ring
      rw [this, Real.rpow_zero]
    rw [hlhs] at hgm
    have key : 1 - a ≤ r ^ a - a * r := by
      have := mul_le_mul_of_nonneg_left hgm h1a.le
      have e1 : (1 - a) * (1 / (1 - a) * r ^ a + -a / (1 - a) * r) = r ^ a - a * r := by
        field_simp
        ring
      rw [e1] at this
      linarith
    rw [div_le_iff_of_neg ha]
    nlinarith
  · -- `0 < a < 1`: weighted AM–GM with weights `a`, `1 − a` on `r`, `1`
    have hgm := Real.geom_mean_le_arith_mean2_weighted ha.le (by linarith : 0 ≤ 1 - a) hr.le
      zero_le_one (by ring)
    rw [Real.one_rpow, mul_one] at hgm
    rw [div_le_iff₀ ha]
    nlinarith

/-- The CRRA utility `u(c) = c^{1−γ}/(1−γ)` (`γ > 0`, `γ ≠ 1`) has the supergradient `c^{−γ}`:
`u(x') ≤ u(x) + x^{−γ}(x' − x)`. -/
theorem bp_crra_supergradient (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≠ 1) (x x' : ℝ) (hx : 0 < x)
    (hx' : 0 < x') :
    x' ^ (1 - γ) / (1 - γ) ≤ x ^ (1 - γ) / (1 - γ) + x ^ (-γ) * (x' - x) := by
  set r := x' / x with hr
  have hrpos : 0 < r := div_pos hx' hx
  have hx'eq : x' = x * r := by rw [hr]; field_simp
  have ha0 : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  have hcore := bp_rpow_sub_one_div_le r (1 - γ) hrpos (by linarith) ha0
  have hxa : 0 < x ^ (1 - γ) := Real.rpow_pos_of_pos hx _
  have hmul := mul_le_mul_of_nonneg_left hcore hxa.le
  have e1 : x' ^ (1 - γ) = x ^ (1 - γ) * r ^ (1 - γ) := by
    rw [hx'eq, Real.mul_rpow hx.le hrpos.le]
  have e2 : x ^ (-γ) * (x' - x) = x ^ (1 - γ) * (r - 1) := by
    rw [hx'eq, show 1 - γ = -γ + 1 by ring, Real.rpow_add hx, Real.rpow_one]
    ring
  rw [e1, e2]
  have e3 : x ^ (1 - γ) * r ^ (1 - γ) / (1 - γ) =
      x ^ (1 - γ) / (1 - γ) + x ^ (1 - γ) * ((r ^ (1 - γ) - 1) / (1 - γ)) := by
    field_simp
    ring
  rw [e3]
  linarith

/-- The CRRA utility is strictly increasing on `(0, ∞)`. -/
theorem bp_crra_mono (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≠ 1) (x x' : ℝ) (hx : 0 < x)
    (hxx' : x ≤ x') : x ^ (1 - γ) / (1 - γ) ≤ x' ^ (1 - γ) / (1 - γ) := by
  have hsg := bp_crra_supergradient γ hγ hγ1 x' x (by linarith) hx
  have : 0 ≤ x' ^ (-γ) * (x' - x) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (by linarith)
  have h2 : x' ^ (-γ) * (x - x') ≤ 0 := by nlinarith
  linarith

end Miao.CompleteMarkets

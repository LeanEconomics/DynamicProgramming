/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NonlinearValuation.Koopmans
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Time additive and risk-sensitive lifetime utility

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.2.1–§7.2.2
(pp. 219–227).

* (7.6) and Exercise 7.2.1: under the ansatz `Vₜ = v(Xₜ)`, the time additive
  recursion (7.5) becomes `v = r + βPv`, uniquely solved by `(I − βP)⁻¹r`.
* The entropic risk-adjusted expectation `E_θ[ξ] = θ⁻¹ log E exp(θξ)` of a random
  variable with a finite distribution `q`: Exercise 7.2.2 (translation), Exercise
  7.2.3 (the Gaussian case `E_θ[ξ] = Eξ + θ Var ξ/2`, by the moment generating
  function), and Lemma 7.2.1 (`E_θ ≤ E` for `θ < 0`, `E_θ ≥ E` for `θ > 0`, with
  strict inequality iff `Var ξ > 0`, by strict Jensen).
* Proposition 7.2.2 is proved in `Koopmans` from Proposition 7.3.3.
* Exercise 7.2.4: with `r(x) = x` and Gaussian AR(1) dynamics, `v(x) = ax + b` with
  `a = 1/(1 − ρβ)` and `b = θ(β/(1 − β))(aσ)²/2` solves (7.11).
* Exercise 7.2.6: with IID states the fixed point is `v* = r + κ` with the constant
  `κ` solving the one-dimensional equation `κ = βκ + βE_θ[r]`, so
  `v* = r + (β/(1 − β))E_θ[r]`.
-/

open Matrix Finset Filter Topology Function Set MeasureTheory ProbabilityTheory

namespace SargentStachurski.NonlinearValuation

variable {X : Type*} [Fintype X]

/-! ### The time additive recursion -/

/-- (7.6) and Exercise 7.2.1 (p. 220): for `P` Markov and `0 ≤ β < 1`, `v* = (I − βP)⁻¹r` solves
`v = r + βPv`, and it is the only solution; hence `Vₜ = v*(Xₜ)` satisfies the recursion (7.5). -/
theorem timeAdditive_solution [DecidableEq X] [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (r : X → ℝ) :
    (1 - β • P)⁻¹ *ᵥ r = r + β • (P *ᵥ ((1 - β • P)⁻¹ *ᵥ r)) ∧
      ∀ w, w = r + β • (P *ᵥ w) → w = (1 - β • P)⁻¹ *ᵥ r := by
  have hρ : specRad (β • P) < 1 := by rw [specRad_smul_isMarkov hP hβ0]; exact hβ1
  refine ⟨?_, fun w hw => (eq_add_mulVec_iff hρ r w).1 (by rwa [smul_mulVec])⟩
  rw [← smul_mulVec]
  exact inv_mulVec_eq_add hρ r

/-! ### The entropic risk-adjusted expectation (§7.2.2.2) -/

/-- The entropic risk-adjusted expectation `E_θ[ξ] = θ⁻¹ log ∑ q(x) exp(θξ(x))` of `ξ` under the
finite distribution `q`. -/
noncomputable def entExp (θ : ℝ) (q ξ : X → ℝ) : ℝ := θ⁻¹ * Real.log (∑ x, q x * Real.exp (θ * ξ x))

/-- The entropic certainty equivalent is the risk-adjusted expectation under each row of `P`. -/
theorem entR_eq_entExp (θ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) (x : X) :
    entR θ P v x = entExp θ (P x) v := rfl

/-- Exercise 7.2.2 (p. 223): `E_θ[ξ + c] = E_θ[ξ] + c`. -/
theorem entExp_add_const {θ : ℝ} (hθ : θ ≠ 0) {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ)
    (c : ℝ) : entExp θ q (fun x => ξ x + c) = entExp θ q ξ + c := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, 0 < q x := by
    by_contra hcon
    have : ∑ x, q x ≤ 0 := sum_nonpos fun x _ => not_lt.1 fun h => hcon ⟨x, h⟩
    linarith [hq.sum_eq_one]
  have hS : 0 < ∑ x, q x * Real.exp (θ * ξ x) :=
    lt_of_lt_of_le (mul_pos hx₀ (Real.exp_pos _))
      (single_le_sum (fun x _ => mul_nonneg (hq.nonneg x) (Real.exp_pos _).le) (mem_univ x₀))
  have h1 : ∑ x, q x * Real.exp (θ * (ξ x + c)) =
      Real.exp (θ * c) * ∑ x, q x * Real.exp (θ * ξ x) := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by rw [mul_add, Real.exp_add]; ring
  unfold entExp
  rw [h1, Real.log_mul (Real.exp_pos _).ne' hS.ne', Real.log_exp]
  field_simp
  ring

/-- Exercise 7.2.3 (p. 223): if `ξ ∼ N(μ, v)` then `E_θ[ξ] = μ + θv/2`, from the Gaussian moment
generating function. -/
theorem entExp_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω} {ξ : Ω → ℝ}
    {μ : ℝ} {v : NNReal} (hξ : HasLaw ξ (gaussianReal μ v) ν) {θ : ℝ} (hθ : θ ≠ 0) :
    θ⁻¹ * Real.log (∫ ω, Real.exp (θ * ξ ω) ∂ν) = μ + θ * v / 2 := by
  have h := mgf_gaussianReal hξ θ
  unfold mgf at h
  rw [h, Real.log_exp]
  field_simp

/-- Jensen's inequality for the exponential: `exp(θE[ξ]) ≤ E[exp(θξ)]`. -/
theorem exp_mean_le {θ : ℝ} {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ) :
    Real.exp (θ * ∑ x, q x * ξ x) ≤ ∑ x, q x * Real.exp (θ * ξ x) := by
  have h := convexOn_exp.map_sum_le (t := univ) (w := q) (p := fun x => θ * ξ x)
    (fun x _ => hq.nonneg x) hq.sum_eq_one (fun x _ => mem_univ _)
  simp only [smul_eq_mul] at h
  have e : ∑ x, q x * (θ * ξ x) = θ * ∑ x, q x * ξ x := by
    rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
  rwa [e] at h

/-- `θE[ξ] ≤ log E[exp(θξ)]`. -/
theorem mul_mean_le_log {θ : ℝ} {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ) :
    θ * ∑ x, q x * ξ x ≤ Real.log (∑ x, q x * Real.exp (θ * ξ x)) := by
  have h := exp_mean_le (θ := θ) hq ξ
  rwa [← Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h)] at h

/-- **Lemma 7.2.1 (i)** (p. 224): `E_θ[ξ] ≤ E[ξ]` for `θ < 0`. -/
theorem entExp_le_mean {θ : ℝ} (hθ : θ < 0) {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ) :
    entExp θ q ξ ≤ ∑ x, q x * ξ x := by
  have h := mul_le_mul_of_nonpos_left (mul_mean_le_log (θ := θ) hq ξ) (inv_lt_zero.2 hθ).le
  rw [← mul_assoc, inv_mul_cancel₀ hθ.ne, one_mul] at h
  exact h

/-- **Lemma 7.2.1 (ii)** (p. 224): `E_θ[ξ] ≥ E[ξ]` for `θ > 0`. -/
theorem mean_le_entExp {θ : ℝ} (hθ : 0 < θ) {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ) :
    ∑ x, q x * ξ x ≤ entExp θ q ξ := by
  have h := mul_le_mul_of_nonneg_left (mul_mean_le_log (θ := θ) hq ξ) (inv_pos.2 hθ).le
  rw [← mul_assoc, inv_mul_cancel₀ hθ.ne', one_mul] at h
  exact h

/-- Lemma 7.2.1 (p. 224), strictness: if `Var[ξ] > 0`, then `E_θ[ξ] ≠ E[ξ]` for `θ ≠ 0`, by strict
Jensen on the support of `q`. -/
theorem entExp_ne_mean {θ : ℝ} (hθ : θ ≠ 0) {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ)
    (hvar : 0 < ∑ x, q x * (ξ x - ∑ y, q y * ξ y) ^ 2) : entExp θ q ξ ≠ ∑ x, q x * ξ x := by
  classical
  set E := ∑ y, q y * ξ y with hE
  set t := univ.filter fun x => 0 < q x with ht
  have hsupp : ∀ g : X → ℝ, ∑ x ∈ t, q x * g x = ∑ x, q x * g x := fun g =>
    sum_filter_of_ne fun x _ hx =>
      lt_of_le_of_ne (hq.nonneg x) (fun h => hx (by rw [← h, zero_mul]))
  -- a support point away from the mean, and a second support point with a different value
  have hsupp1 : ∑ x ∈ t, q x = ∑ x, q x :=
    sum_filter_of_ne fun x _ hx => lt_of_le_of_ne (hq.nonneg x) (Ne.symm hx)
  obtain ⟨j, hj⟩ : ∃ j, 0 < q j * (ξ j - E) ^ 2 := by
    by_contra hcon
    have : ∑ x, q x * (ξ x - E) ^ 2 ≤ 0 := sum_nonpos fun x _ => not_lt.1 fun h => hcon ⟨x, h⟩
    linarith
  have hqj : 0 < q j := by
    rcases (hq.nonneg j).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hj; exact absurd hj (lt_irrefl 0)
  have hjE : ξ j ≠ E := fun h => by rw [h, sub_self] at hj; simp at hj
  obtain ⟨k, hk, hjk⟩ : ∃ k ∈ t, ξ j ≠ ξ k := by
    by_contra hcon
    have hall : ∀ k ∈ t, ξ k = ξ j := fun k hk => by
      by_contra hne
      exact hcon ⟨k, hk, fun h => hne h.symm⟩
    have : E = ξ j := by
      rw [hE, ← hsupp ξ, sum_congr rfl fun k hk => by rw [hall k hk], ← sum_mul, hsupp1,
        hq.sum_eq_one, one_mul]
    exact hjE this.symm
  have hj' : j ∈ t := mem_filter.2 ⟨mem_univ _, hqj⟩
  have hstrict := strictConvexOn_exp.map_sum_lt (t := t) (w := q) (p := fun x => θ * ξ x)
    (fun x hx => (mem_filter.1 hx).2) (by rw [hsupp1]; exact hq.sum_eq_one)
    (fun x _ => mem_univ _) ⟨j, hj', k, hk, fun h => hjk (mul_left_cancel₀ hθ h)⟩
  simp only [smul_eq_mul] at hstrict
  have e1 : ∑ x ∈ t, q x * (θ * ξ x) = θ * E := by
    rw [hsupp fun x => θ * ξ x, mul_sum]; exact sum_congr rfl fun x _ => by ring
  rw [e1, hsupp fun x => Real.exp (θ * ξ x)] at hstrict
  have hlog : θ * E < Real.log (∑ x, q x * Real.exp (θ * ξ x)) :=
    (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) hstrict)).2 hstrict
  intro heq
  unfold entExp at heq
  have : Real.log (∑ x, q x * Real.exp (θ * ξ x)) = θ * E := by
    rw [← heq, ← mul_assoc, mul_inv_cancel₀ hθ, one_mul]
  linarith

/-- Lemma 7.2.1 (p. 224), equality case: if `Var[ξ] = 0` then `E_θ[ξ] = E[ξ]`. -/
theorem entExp_eq_mean {θ : ℝ} (hθ : θ ≠ 0) {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ)
    (hvar : ∑ x, q x * (ξ x - ∑ y, q y * ξ y) ^ 2 = 0) : entExp θ q ξ = ∑ x, q x * ξ x := by
  set E := ∑ y, q y * ξ y with hE
  have hterm := (sum_eq_zero_iff_of_nonneg fun x _ =>
    mul_nonneg (hq.nonneg x) (sq_nonneg _)).1 hvar
  have h1 : ∑ x, q x * Real.exp (θ * ξ x) = Real.exp (θ * E) := by
    have : ∀ x, q x * Real.exp (θ * ξ x) = q x * Real.exp (θ * E) := fun x => by
      rcases mul_eq_zero.1 (hterm x (mem_univ x)) with h | h
      · rw [h, zero_mul, zero_mul]
      · rw [sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)]
    rw [sum_congr rfl fun x _ => this x, ← sum_mul, hq.sum_eq_one, one_mul]
  unfold entExp
  rw [h1, Real.log_exp, ← mul_assoc, inv_mul_cancel₀ hθ, one_mul]

/-! ### Exercise 7.2.4: the Gaussian case -/

/-- `E[exp(a + bW)] = exp(a + b²/2)` for a standard normal `W`. -/
theorem integral_exp_add_mul_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {η : Ω → ℝ} (hη : HasLaw η (gaussianReal 0 1) ν) (a b : ℝ) :
    ∫ ω, Real.exp (a + b * η ω) ∂ν = Real.exp (a + b ^ 2 / 2) := by
  simp_rw [Real.exp_add]
  rw [integral_const_mul]
  have h := mgf_gaussianReal hη b
  unfold mgf at h
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul] at h
  rw [h, ← Real.exp_add]

/-- Exercise 7.2.4 (p. 225): with `r(x) = x`, `X' = ρx + σW` and `W` standard normal, the affine
function `v(x) = ax + b` with `a = 1/(1 − ρβ)` and `b = θ(β/(1 − β))(aσ)²/2` solves (7.11),
`v(x) = x + βE_θ[v(ρx + σW)]`. -/
theorem riskSensitive_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {W : Ω → ℝ} (hW : HasLaw W (gaussianReal 0 1) ν) {β ρ σ θ : ℝ} (hθ : θ ≠ 0) (hβ : β ≠ 1)
    (hρβ : ρ * β ≠ 1) (x : ℝ) :
    1 / (1 - ρ * β) * x + θ * (β / (1 - β)) * (1 / (1 - ρ * β) * σ) ^ 2 / 2 =
      x + β * (θ⁻¹ * Real.log (∫ ω, Real.exp (θ * (1 / (1 - ρ * β) * (ρ * x + σ * W ω) +
        θ * (β / (1 - β)) * (1 / (1 - ρ * β) * σ) ^ 2 / 2)) ∂ν)) := by
  set a := 1 / (1 - ρ * β) with ha
  set b := θ * (β / (1 - β)) * (a * σ) ^ 2 / 2 with hb
  have h1 : ∀ ω, θ * (a * (ρ * x + σ * W ω) + b) = θ * (a * ρ * x + b) + θ * a * σ * W ω :=
    fun ω => by ring
  simp_rw [h1]
  rw [integral_exp_add_mul_gaussian hW, Real.log_exp]
  have h1ρβ : 1 - ρ * β ≠ 0 := sub_ne_zero.2 (Ne.symm hρβ)
  have h1β : 1 - β ≠ 0 := sub_ne_zero.2 (Ne.symm hβ)
  rw [hb, ha]
  field_simp
  ring

/-! ### Exercise 7.2.6: IID consumption -/

/-- Exercise 7.2.6 (p. 225): with IID states drawn from `φ`, the risk-sensitive Koopmans operator is
`(Kv)(x) = r(x) + βE_θ^φ[v]`, so a fixed point has the form `v* = r + κ` for a constant `κ`, which
by translation equivariance solves the one-dimensional linear equation `κ = βκ + βE_θ^φ[r]`; hence
`v* = r + (β/(1 − β))E_θ^φ[r]`. -/
theorem riskSensitive_iid {θ : ℝ} (hθ : θ ≠ 0) {φ : X → ℝ} (hφ : IsDistribution φ) (r : X → ℝ)
    {β : ℝ} (hβ : β ≠ 1) :
    IsFixedPt (koopmans (additive r β) (entR θ (Matrix.of fun _ x' => φ x')))
      (fun x => r x + β / (1 - β) * entExp θ φ r) := by
  funext x
  have h1β : 1 - β ≠ 0 := sub_ne_zero.2 (Ne.symm hβ)
  change r x + β * entExp θ φ (fun x' => r x' + β / (1 - β) * entExp θ φ r) =
    r x + β / (1 - β) * entExp θ φ r
  rw [entExp_add_const hθ hφ]
  field_simp
  ring

/-- Exercise 7.2.6: the IID kernel is Markov, so for `0 ≤ β < 1` the fixed point
`r + (β/(1 − β))E_θ^φ[r]` is the unique lifetime value, by Proposition 7.2.2. -/
theorem riskSensitive_iid_unique {θ : ℝ} (hθ : θ ≠ 0) {φ : X → ℝ} (hφ : IsDistribution φ)
    (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {v : X → ℝ}
    (hv : IsFixedPt (koopmans (additive r β) (entR θ (Matrix.of fun _ x' => φ x'))) v) :
    v = fun x => r x + β / (1 - β) * entExp θ φ r := by
  have hP : IsMarkov (Matrix.of fun (_ : X) x' => φ x') :=
    ⟨fun _ x' => hφ.nonneg x', fun _ => hφ.sum_eq_one⟩
  obtain ⟨u, -, huniq, -⟩ := globallyStable_riskSensitive hP hθ r hβ0 hβ1
  rw [huniq v hv, huniq _ (riskSensitive_iid hθ hφ r hβ1.ne)]

end SargentStachurski.NonlinearValuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.SpectralGap

/-!
# Variance reduction and the asymptotic variance (MT §20.2.1, p. 515)

Meyn and Tweedie, pp. 515 and 521–522.

* `integral_controlVariate_eq_zero`, `integral_controlVariate_pow_eq_zero` (p. 521): the control
  variate `W_t = g(Φ_t) − Pg(Φ_t)` (20.20) has steady-state mean `π(g − Pg) = 0` at every time.
* `cvEstimator` (20.19), `cvEstimator_poisson` (p. 521): with `g = f̂` a solution of Poisson's
  equation, `W_k = f(Φ_k) − π(f)` and the estimator equals `π(f)` on every path (zero variance).
* `exists_poisson_of_vUniform` (p. 511): for a `V`-uniformly ergodic chain every `f ∈ L∞_V` has
  the solution `f̂ = Zf` of Poisson's equation (through Theorem 20.1.1 and `fundKernel_poisson`).
* `asymptoticVariance_le` (p. 515, proof of Proposition 20.1.2 (ii), corrected): if
  `‖Pⁿf̃‖₂ ≤ R r⁻ⁿ ‖f̃‖₂`, the asymptotic variance (17.3),
  `γ² = π(f̃²) + 2 Σ_{n≥1} π(f̃ Pⁿf̃) = ⟪f̃, f̃⟫ + 2Σ⟪f̃, Pⁿf̃⟫_{L²(π)}`, satisfies
  `γ² ≤ R (r + 1)/(r − 1) ‖f̃‖₂²`; stated for any linear map on a real inner product space.
* `asymptoticVariance_le_sq`: with (20.7) as printed (squared norms) the bound is
  `√R (√r + 1)/(√r − 1) ‖f̃‖₂²`.

**Correction.** (20.7) defines geometric ergodicity in `Lᵖ(π)` with `p`-th powers,
`‖Pⁿf − π(f)‖ₚᵖ ≤ R r⁻ⁿ ‖f‖ₚᵖ`; with that definition the variance bound
`γ² ≤ R (r + 1)/(r − 1) ‖f‖₂²` on p. 515 is false. `asymptoticVariance_book_counterexample`: the
eigenvalue-`1/2` direction of the two-state chain `[[3/4, 1/4], [1/4, 3/4]]` satisfies the squared
form with `R = 1`, `r = 4`, but `γ² = 3 > 5/3`. The bound holds for the norm form of (20.7)
(`asymptoticVariance_le`), which is the reading used in `IsLpGeomErgodic` (module `MM1Spectrum`).

**Elsewhere and not formalised.** Proposition 20.1.2 (ii) is `proposition_20_1_2_ii` in
`BranchChain`, with a simpler chain than Häggström's example [150]. Proposition 20.1.2 (iii)
(Roberts–Rosenthal [329]: a reversible chain is geometrically ergodic in `L²(π)` iff it is
`V`-uniformly ergodic for some `V`) needs the spectral theorem for self-adjoint operators on
`L²(π)` together with Theorem 15.0.1 and is not formalised.
Figure 20.1 is a simulation.
-/
namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### Control variates (§20.2.1) -/

/-- **The control variate has steady-state mean zero** (MT p. 521): for `π` invariant and `g`,
`Pg` both `π`-integrable, `E_π[W_t] = π(g − Pg) = 0`, `W_t = g(Φ_t) − Pg(Φ_t)`. -/
theorem integral_controlVariate_eq_zero (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : IsInvariant P π) {g : X → ℝ} (hg : Measurable g)
    (hgi : Integrable g π) (hPgi : Integrable (fun x => ∫ y, g y ∂P x) π) :
    ∫ x, (g x - ∫ y, g y ∂P x) ∂π = 0 := by
  have h := integral_comp_kernel_of_integrable P π hg (by rw [hinv]; exact hgi)
  rw [hinv] at h
  rw [integral_sub hgi hPgi, ← h, sub_self]

/-- `E_π[W_t] = 0` at every time `t`: the law of `Φ_t` under `P_π` is `πPᵗ = π`. -/
theorem integral_controlVariate_pow_eq_zero (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : IsInvariant P π) {g : X → ℝ} (hg : Measurable g)
    (hgi : Integrable g π) (hPgi : Integrable (fun x => ∫ y, g y ∂P x) π) (t : ℕ) :
    ∫ x, (g x - ∫ y, g y ∂P x) ∂((P ^ t) ∘ₘ π) = 0 := by
  have hinvt : (P ^ t) ∘ₘ π = π := by
    induction t with
    | zero => rw [pow_zero]; exact Measure.id_comp
    | succ t ih =>
      rw [pow_succ]
      change ((P ^ t) ∘ₖ P) ∘ₘ π = π
      rw [← Measure.comp_assoc, hinv]; exact ih
  rw [hinvt]
  exact integral_controlVariate_eq_zero P π hinv hg hgi hPgi

/-- The control-variate estimator (20.19): `π̂ⁿ_CV(f) = n⁻¹ Σ_{k<n} [f(Φ_k) − W_k]` along a path
`ω`, with `W_k = ĝ(Φ_k) − Pĝ(Φ_k)` (20.20). -/
noncomputable def cvEstimator (P : Kernel X X) (f g : X → ℝ) (ω : ℕ → X) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (f (ω k) - (g (ω k) - ∫ y, g y ∂P (ω k)))

/-- **Zero variance with the solution of Poisson's equation** (MT p. 521): if `ĝ` solves
Poisson's equation `Pĝ = ĝ − f + π(f)`, then `W_k = f(Φ_k) − π(f)` and the control-variate
estimator equals `π(f)` exactly, on every path and for every `n ≥ 1`. -/
theorem cvEstimator_poisson (P : Kernel X X) {f g : X → ℝ} {m : ℝ}
    (hpois : ∀ x, ∫ y, g y ∂P x = g x - f x + m) (ω : ℕ → X) {n : ℕ} (hn : n ≠ 0) :
    cvEstimator P f g ω n = m := by
  have : ∀ k, f (ω k) - (g (ω k) - ∫ y, g y ∂P (ω k)) = m := fun k => by
    rw [hpois]; ring
  rw [cvEstimator, Finset.sum_congr rfl fun k _ => this k, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn),
    one_mul]

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- **Poisson's equation has a solution for every `f ∈ L∞_V`** when the chain is `V`-uniformly
ergodic (MT p. 511): `f̂ = (Zg)V` with the fundamental kernel `Z = Z_1` of Theorem 20.1.1. Hence
the zero-variance control variate of p. 521 exists. -/
theorem exists_poisson_of_vUniform [IsMarkovKernel P] [IsProbabilityMeasure π]
    (hinv : IsInvariant P π) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hrate : ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧
      ∀ n, vErgDist (eW V) P π n ≤ R * r⁻¹ ^ n) (g : BM X) :
    ∃ ĝ : BM X, ∀ x, ∫ y, bmFun ĝ y * (V y : ℂ) ∂P x =
      bmFun ĝ x * V x - bmFun g x * V x + ∫ y, bmFun g y * (V y : ℂ) ∂π := by
  obtain ⟨r, hr, R, hR, hb⟩ := hrate
  obtain ⟨hP, hPi, -⟩ := norm_sub_pow_le_of_rate hinv hV hV1 hr hR hb
  obtain ⟨ε₀, -, hε₀, hZ, -⟩ := theorem_20_1_1_i hinv hV hV1 ⟨r, hr, R, hR, hb⟩
  exact ⟨_, fundKernel_poisson hinv hP hPi (hZ 1 (by rw [norm_one]; exact hε₀)).1 g⟩

/-! ### The asymptotic variance under `L²(π)` geometric ergodicity (Proposition 20.1.2 (ii)) -/

/-- **The variance bound in the proof of Proposition 20.1.2 (ii)** (MT p. 515), corrected form.
In `L²(π)` the asymptotic variance (17.3) of a centred `f̃` is
`γ² = ⟪f̃, f̃⟫ + 2 Σ_{n ≥ 1} ⟪f̃, Pⁿf̃⟫`. If `‖Pⁿf̃‖ ≤ R r⁻ⁿ ‖f̃‖` (geometric ergodicity in
`L²(π)` with norms, `R ≥ 1`, `r > 1`), then `γ² ≤ R (r + 1)/(r − 1) ‖f̃‖²`. The statement is for
any linear map `T` on a real inner product space (`T = P` on `L²(π)`). -/
theorem asymptoticVariance_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (f : E) {R r : ℝ} (hR : 1 ≤ R) (hr : 1 < r)
    (hT : ∀ n : ℕ, ‖(T ^ n) f‖ ≤ R * r⁻¹ ^ n * ‖f‖) :
    Summable (fun n : ℕ => inner ℝ f ((T ^ (n + 1)) f)) ∧
      inner ℝ f f + 2 * ∑' n : ℕ, inner ℝ f ((T ^ (n + 1)) f) ≤
        R * ((r + 1) / (r - 1)) * ‖f‖ ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hq0 : 0 ≤ r⁻¹ := inv_nonneg.2 hr0.le
  have hq1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have hbd : ∀ n : ℕ, |inner ℝ f ((T ^ (n + 1)) f)| ≤ R * ‖f‖ ^ 2 * r⁻¹ * r⁻¹ ^ n := fun n => by
    calc |inner ℝ f ((T ^ (n + 1)) f)| ≤ ‖f‖ * ‖(T ^ (n + 1)) f‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖f‖ * (R * r⁻¹ ^ (n + 1) * ‖f‖) := mul_le_mul_of_nonneg_left (hT _) (norm_nonneg _)
      _ = R * ‖f‖ ^ 2 * r⁻¹ * r⁻¹ ^ n := by ring
  have hgeom : Summable fun n : ℕ => R * ‖f‖ ^ 2 * r⁻¹ * r⁻¹ ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hsum : Summable fun n : ℕ => inner ℝ f ((T ^ (n + 1)) f) :=
    Summable.of_norm_bounded hgeom fun n => by rw [Real.norm_eq_abs]; exact hbd n
  refine ⟨hsum, ?_⟩
  have h1 : ∑' n : ℕ, inner ℝ f ((T ^ (n + 1)) f) ≤ R * ‖f‖ ^ 2 * r⁻¹ * (1 - r⁻¹)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hq0 hq1, ← tsum_mul_left]
    exact hsum.tsum_le_tsum (fun n => (le_abs_self _).trans (hbd n)) hgeom
  have h0 : inner ℝ f f ≤ R * ‖f‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    exact le_mul_of_one_le_left (sq_nonneg _) hR
  have hfrac : r⁻¹ * (1 - r⁻¹)⁻¹ = 1 / (r - 1) := by
    field_simp
  calc inner ℝ f f + 2 * ∑' n : ℕ, inner ℝ f ((T ^ (n + 1)) f)
      ≤ R * ‖f‖ ^ 2 + 2 * (R * ‖f‖ ^ 2 * r⁻¹ * (1 - r⁻¹)⁻¹) := by linarith
    _ = R * ‖f‖ ^ 2 * (1 + 2 * (r⁻¹ * (1 - r⁻¹)⁻¹)) := by ring
    _ = R * ((r + 1) / (r - 1)) * ‖f‖ ^ 2 := by
        rw [hfrac]
        have : r - 1 ≠ 0 := by linarith
        field_simp
        ring

/-- **The bound of p. 515 fails for (20.7) as printed** (with `p`-th powers,
`‖Pⁿf − π(f)‖₂² ≤ R r⁻ⁿ ‖f‖₂²`). On `ℝ` with `T = 1/2` (the two-state chain
`P = [[3/4, 1/4], [1/4, 3/4]]` on its centred functions, eigenvalue `1/2`), `‖Tⁿf‖² = 4⁻ⁿ‖f‖²`,
so the squared form of (20.7) holds with `R = 1`, `r = 4`; but for `f = 1` the asymptotic
variance is `1 + 2 Σ 2⁻ⁿ = 3 > R (r + 1)/(r − 1) ‖f‖² = 5/3`. -/
theorem asymptoticVariance_book_counterexample :
    (∀ n : ℕ, ‖((1 / 2 : ℝ) ^ n) * 1‖ ^ 2 ≤ 1 * (4 : ℝ)⁻¹ ^ n * ‖(1 : ℝ)‖ ^ 2) ∧
      (1 : ℝ) * 1 + 2 * ∑' n : ℕ, (1 : ℝ) * ((1 / 2) ^ (n + 1) * 1) = 3 ∧
      ¬ ((3 : ℝ) ≤ 1 * ((4 + 1) / (4 - 1)) * ‖(1 : ℝ)‖ ^ 2) := by
  refine ⟨fun n => le_of_eq ?_, ?_, by norm_num⟩
  · rw [mul_one, norm_pow, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      norm_one, one_pow, mul_one, one_mul, ← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  · have h : ∑' n : ℕ, (1 : ℝ) * ((1 / 2) ^ (n + 1) * 1) = 1 := by
      simp_rw [one_mul, mul_one, pow_succ]
      rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    rw [h]; norm_num

/-- **The bound with (20.7) as printed** (squared norms): if `‖Tⁿf‖² ≤ R r⁻ⁿ ‖f‖²`, then
`γ² ≤ √R (√r + 1)/(√r − 1) ‖f‖²` (apply `asymptoticVariance_le` with `√R`, `√r`). -/
theorem asymptoticVariance_le_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (f : E) {R r : ℝ} (hR : 1 ≤ R) (hr : 1 < r)
    (hT : ∀ n : ℕ, ‖(T ^ n) f‖ ^ 2 ≤ R * r⁻¹ ^ n * ‖f‖ ^ 2) :
    inner ℝ f f + 2 * ∑' n : ℕ, inner ℝ f ((T ^ (n + 1)) f) ≤
      Real.sqrt R * ((Real.sqrt r + 1) / (Real.sqrt r - 1)) * ‖f‖ ^ 2 := by
  have hsr : 1 < Real.sqrt r := by
    rw [Real.lt_sqrt zero_le_one, one_pow]; exact hr
  have hsR : 1 ≤ Real.sqrt R := by
    rw [Real.le_sqrt zero_le_one (by linarith), one_pow]; exact hR
  refine (asymptoticVariance_le T f hsR hsr fun n => ?_).2
  have h := hT n
  have hr0 : 0 ≤ r := by linarith
  rw [← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_sq (norm_nonneg _)] at h
  have e : r⁻¹ ^ n = ((Real.sqrt r)⁻¹ ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, inv_pow (Real.sqrt r) 2, Real.sq_sqrt hr0, inv_pow]
  calc ‖(T ^ n) f‖ ≤ Real.sqrt (R * r⁻¹ ^ n * ‖f‖ ^ 2) := h
    _ = Real.sqrt R * (Real.sqrt r)⁻¹ ^ n * ‖f‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by linarith), Real.sqrt_sq
          (norm_nonneg _), e, Real.sqrt_sq (by positivity)]

end MeynTweedie.Epilogue

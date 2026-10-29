/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.RegenerativeModels
import VUniformErgodicity.CountableIrreducibility

/-!
# Models from queueing theory (MT §16.4)

Meyn and Tweedie, §16.4, pp. 411–414. The embedded M/G/1 queue `N*ₙ` of (Q4) is the chain
`matKernel (mG1Matrix q)` on `ℤ₊` with `P(0, j) = q_j`, `P(i, i − 1 + k) = q_k` for `i ≥ 1`, where
`q_k = ∫ e^{−λt}(λt)ᵏ/k! H(dt)` (`poissonWeight H λ`) is the law of the number of Poisson(`λ`)
arrivals during a service time `T ∼ H`.

* `tsum_exp_mul_poissonWeight` (p. 412): the generating function of the arrivals,
  `Σₖ e^{δk} q_k = ∫ exp{(e^δ − 1)λt} H(dt)`, the identity behind the proof of Theorem 16.4.1.
* `mG1_lintegral_succ`, `mG1_lintegral_zero`: `PV(i) = Σₖ q_k V(i − 1 + k)` for `i ≥ 1` and
  `PV(0) = Σₖ q_k V(k)`.
* **Theorem 16.4.1** (`theorem_16_4_1`, p. 411): if the M/G/1 chain is ergodic,
  `Σₖ k q_k < 1`, and the service time law is in `G⁺(γ)`, then the chain is `e^{δi}`-uniformly
  ergodic for some `δ > 0`, hence geometrically ergodic.

The proof follows the book's: the arrival law inherits a geometric tail from `H`
(`tsum_exp_mul_poissonWeight`), and with the increment `W = A − 1` of the chain off `0`
(`E[W] < 0`) `exists_mgf_lt_one` gives `E[e^{δW}] < 1` for small `δ`, which is (V4) for
`V*(i) = e^{δi}` with `C = {0}`. This is Theorem 16.3.1 for `V(i) = i`, done directly; the
book's remark that `V(i) = i` solves (16.25) holds after rescaling by `(1 − Σ k q_k)⁻¹`.

**Hypotheses.** The service law is not concentrated at `0` and `λ > 0`, so that the chain is
irreducible (`mG1_poisson_isIrreducibleChain`); "ergodic" is read as `Σₖ k q_k < 1`, which is
positivity by Proposition 10.3.1.

**Elsewhere.** Theorem 16.4.2 (the gated-limited polling system) is `theorem_16_4_2` in
`PollingModels`, and Theorem 16.4.3 (the `h`-approximation of the M/PH/1 queue) is
`theorem_16_4_3` in `PHQueue`.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology NNReal Nat

/-! ### The generating function of the arrivals -/

/-- **The generating function of the M/G/1 arrivals** (MT p. 412):
`Σₖ e^{δk} q_k = ∫ exp{(e^δ − 1)λt} H(dt)` for `q = poissonWeight H λ`. -/
theorem tsum_exp_mul_poissonWeight (H : Measure ℝ≥0) (r : ℝ≥0) (δ : ℝ) :
    ∑' k : ℕ, ENNReal.ofReal (Real.exp (δ * k)) * poissonWeight H r k =
      ∫⁻ t, ENNReal.ofReal (Real.exp ((Real.exp δ - 1) * ((r * t : ℝ≥0) : ℝ))) ∂H := by
  unfold poissonWeight
  have hm : ∀ k : ℕ, Measurable fun t : ℝ≥0 => poissonMeasure (r * t) {k} := fun k => by
    simp_rw [poissonMeasure_singleton]
    fun_prop
  simp_rw [← lintegral_const_mul _ (hm _)]
  rw [← lintegral_tsum fun k => ((hm k).const_mul _).aemeasurable]
  refine lintegral_congr fun t => ?_
  simp_rw [poissonMeasure_singleton]
  set x : ℝ := ((r * t : ℝ≥0) : ℝ) with hx
  have hx0 : 0 ≤ x := NNReal.coe_nonneg _
  have hterm : ∀ k : ℕ, ENNReal.ofReal (Real.exp (δ * k)) *
      ENNReal.ofReal (Real.exp (-x) * x ^ k / k !) =
      ENNReal.ofReal (Real.exp (-x) * ((Real.exp δ * x) ^ k / k !)) := fun k => by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring_nf
  simp_rw [hterm]
  have hsum := Real.summable_pow_div_factorial (Real.exp δ * x)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (hsum.mul_left _),
    tsum_mul_left]
  congr 1
  have he : ∑' k : ℕ, (Real.exp δ * x) ^ k / k ! = Real.exp (Real.exp δ * x) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [he, ← Real.exp_add]
  ring_nf

/-! ### The M/G/1 kernel -/

/-- `PV(i) = Σₖ q_k V(i − 1 + k)` for `i ≥ 1`. -/
theorem mG1_lintegral_succ (q : ℕ → ℝ≥0∞) (f : ℕ → ℝ≥0∞) (i : ℕ) :
    ∫⁻ y, f y ∂matKernel (mG1Matrix q) (i + 1) = ∑' k, q k * f (k + i) := by
  rw [lintegral_matKernel, ← Summable.sum_add_tsum_nat_add'
    (f := fun y => mG1Matrix q (i + 1) y * f y) (k := i) ENNReal.summable]
  have h0 : ∑ y ∈ Finset.range i, mG1Matrix q (i + 1) y * f y = 0 :=
    Finset.sum_eq_zero fun y hy => by
      have : ¬ (i + 1 ≤ y + 1) := by have := Finset.mem_range.1 hy; omega
      simp only [mG1Matrix, Nat.add_one_ne_zero, ite_false, this, zero_mul]
  rw [h0, zero_add]
  refine tsum_congr fun k => ?_
  have h1 : i + 1 ≤ k + i + 1 := by omega
  have h2 : k + i + 1 - (i + 1) = k := by omega
  have h3 : mG1Matrix q (i + 1) (k + i) = q k := by
    simp only [mG1Matrix, Nat.add_one_ne_zero, ite_false, h1, ite_true, h2]
  rw [h3]

/-- `PV(0) = Σₖ q_k V(k)`. -/
theorem mG1_lintegral_zero (q : ℕ → ℝ≥0∞) (f : ℕ → ℝ≥0∞) :
    ∫⁻ y, f y ∂matKernel (mG1Matrix q) 0 = ∑' k, q k * f k := by
  rw [lintegral_matKernel]
  simp [mG1Matrix]

/-! ### Theorem 16.4.1 -/

/-- **Theorem 16.4.1** (MT p. 411): for the embedded M/G/1 queue with Poisson(`λ`) arrivals,
`λ > 0`, and a service law `H` not concentrated at `0`, if the chain is ergodic
(`Σₖ k q_k < 1`) and `H ∈ G⁺(γ)` (`∫ e^{γt} H(dt) < ∞`, `γ > 0`), then for some `δ > 0` the
chain is positive and `e^{δi}`-uniformly ergodic: every invariant probability `π` has
`Σ rⁿ |||Pⁿ − 1 ⊗ π|||_{V*} < ∞` for some `r > 1`, `V*(i) = e^{δi}`. -/
theorem theorem_16_4_1 (H : Measure ℝ≥0) [IsProbabilityMeasure H] {r : ℝ≥0} (hr : r ≠ 0)
    (hH : H {0}ᶜ ≠ 0) (hmean : ∑' k : ℕ, (k : ℝ≥0∞) * poissonWeight H r k < 1) {γ : ℝ}
    (hγ : 0 < γ) (hHγ : ∫⁻ t, ENNReal.ofReal (Real.exp (γ * t)) ∂H ≠ ∞) :
    haveI := isMarkovKernel_matKernel (proposition_3_3_2 H r)
    ∃ δ : ℝ, 0 < δ ∧ IsPositive (matKernel (mG1Matrix (poissonWeight H r))) Measure.count ∧
      ∀ (μ : Measure ℕ) [IsProbabilityMeasure μ],
        IsInvariant (matKernel (mG1Matrix (poissonWeight H r))) μ →
        IsVUniformlyErgodic (fun i : ℕ => ENNReal.ofReal (Real.exp (δ * i)))
          (matKernel (mG1Matrix (poissonWeight H r))) μ ∧
        ∃ ρ : ℝ≥0∞, 1 < ρ ∧ ρ ≠ ∞ ∧ ∑' n, ρ ^ n * vErgDist
          (fun i : ℕ => ENNReal.ofReal (Real.exp (δ * i)))
          (matKernel (mG1Matrix (poissonWeight H r))) μ n ≠ ∞ := by
  have hM := isMarkovKernel_matKernel (proposition_3_3_2 H r)
  set q := poissonWeight H r with hq
  set P := matKernel (mG1Matrix q) with hP
  set A : Measure ℕ := P 0 with hA
  have hAq : ∀ f : ℕ → ℝ≥0∞, ∫⁻ k, f k ∂A = ∑' k, q k * f k := fun f => mG1_lintegral_zero q f
  -- the increment law `Γ` of `A − 1`
  set Γ : Measure ℝ := A.map (fun k : ℕ => (k : ℝ) - 1) with hΓ
  have hmap : Measurable fun k : ℕ => (k : ℝ) - 1 := measurable_of_countable _
  have hΓl : ∀ g : ℝ → ℝ≥0∞, Measurable g → ∫⁻ w, g w ∂Γ = ∑' k, q k * g ((k : ℝ) - 1) :=
    fun g hg => by rw [hΓ, lintegral_map hg hmap, hAq]
  have hmeant : ∑' k : ℕ, (k : ℝ≥0∞) * q k ≠ ∞ := (hmean.trans ENNReal.one_lt_top).ne
  -- integrability of the increment
  have hWint : Integrable (fun w : ℝ => w) Γ := by
    refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
    change ∫⁻ w, ‖w‖ₑ ∂Γ < ∞
    rw [hΓl (fun w => ‖w‖ₑ) measurable_id.enorm]
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => mul_le_mul' le_rfl
      (show ‖(k : ℝ) - 1‖ₑ ≤ (k : ℝ≥0∞) + 1 from ?_)) ?_
    · rw [Real.enorm_eq_ofReal_abs]
      calc ENNReal.ofReal |(k : ℝ) - 1| ≤ ENNReal.ofReal ((k : ℝ) + 1) :=
            ENNReal.ofReal_le_ofReal (by
              rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
        _ = (k : ℝ≥0∞) + 1 := by rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp
    · simp_rw [mul_add, mul_one]
      rw [ENNReal.tsum_add, tsum_poissonWeight H r]
      refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.one_lt_top⟩
      simp_rw [mul_comm (q _)]
      exact lt_top_iff_ne_top.2 hmeant
  -- the mean of the increment is negative
  have hmeanΓ : ∫ w, w ∂Γ < 0 := by
    have hk : Integrable (fun k : ℕ => (k : ℝ)) A := by
      refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
      change ∫⁻ k, ‖(k : ℝ)‖ₑ ∂A < ∞
      rw [hAq]
      simp_rw [Real.enorm_natCast, mul_comm (q _)]
      exact lt_top_iff_ne_top.2 hmeant
    have hint : ∫ k, (k : ℝ) ∂A = (∑' k : ℕ, (k : ℝ≥0∞) * q k).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun k => by positivity)
        hk.aestronglyMeasurable, hAq]
      simp_rw [ENNReal.ofReal_natCast, mul_comm (q _)]
    rw [hΓ, integral_map hmap.aemeasurable (by fun_prop), integral_sub hk (integrable_const 1),
      integral_const, probReal_univ, one_smul, hint, sub_neg]
    exact ENNReal.toReal_lt_of_lt_ofReal (by simpa using hmean)
  -- the Laplace transform of the increment
  set s₁ : ℝ := Real.log (1 + γ / r) with hs₁
  have hr0 : (0 : ℝ) < r := by exact_mod_cast pos_iff_ne_zero.2 hr
  have hs₁0 : 0 < s₁ := Real.log_pos (by have : 0 < γ / r := div_pos hγ hr0; linarith)
  have hes₁ : (Real.exp s₁ - 1) * r = γ := by
    rw [hs₁, Real.exp_log (by positivity)]; field_simp; ring
  have hgen : ∑' k : ℕ, ENNReal.ofReal (Real.exp (s₁ * k)) * q k ≠ ∞ := by
    rw [hq, tsum_exp_mul_poissonWeight]
    refine ne_top_of_le_ne_top hHγ (lintegral_mono fun t => ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 (le_of_eq ?_)))
    push_cast
    rw [← hes₁]; ring
  have hLap : IsLaplaceFinite Γ s₁ := by
    refine ⟨hs₁0, fun s hs0 hss => ⟨(by fun_prop : Measurable fun w : ℝ =>
      Real.exp (s * w)).aestronglyMeasurable, ?_⟩⟩
    change ∫⁻ w, ‖Real.exp (s * w)‖ₑ ∂Γ < ∞
    rw [hΓl (fun w => ‖Real.exp (s * w)‖ₑ) (by fun_prop)]
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => mul_le_mul' le_rfl
      (show ‖Real.exp (s * ((k : ℝ) - 1))‖ₑ ≤ ENNReal.ofReal (Real.exp (s₁ * k)) from ?_)) ?_
    · rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith [k.cast_nonneg (α := ℝ)]))
    · simp_rw [mul_comm (q _)]
      exact lt_top_iff_ne_top.2 hgen
  obtain ⟨s, hs0, -, hsint, hsM⟩ := exists_mgf_lt_one hWint hmeanΓ hLap
  set Mg := ∫ w, Real.exp (s * w) ∂Γ with hMg
  have hMg0 : 0 ≤ Mg := integral_nonneg fun w => (Real.exp_pos _).le
  have hMgl : ∑' k : ℕ, q k * ENNReal.ofReal (Real.exp (s * ((k : ℝ) - 1))) =
      ENNReal.ofReal Mg := by
    rw [← hΓl (fun w => ENNReal.ofReal (Real.exp (s * w))) (by fun_prop),
      ofReal_integral_eq_lintegral_ofReal hsint
      (Eventually.of_forall fun w => (Real.exp_pos _).le)]
  -- the drift for `V*(i) = e^{si}`
  set V : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (Real.exp (s * i)) with hV
  have hsplit : ∀ i k : ℕ, ENNReal.ofReal (Real.exp (s * ((k + i : ℕ) : ℝ))) =
      ENNReal.ofReal (Real.exp (s * ((i + 1 : ℕ) : ℝ))) *
        ENNReal.ofReal (Real.exp (s * ((k : ℝ) - 1))) := fun i k => by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; push_cast; ring
  have hdrift : DriftV4 P V (ENNReal.ofReal Mg) (ENNReal.ofReal (Real.exp s * Mg)) {0} := by
    intro x
    rcases Nat.eq_zero_or_eq_succ_pred x with hx | hx
    · subst hx
      rw [indicator_of_mem (mem_singleton 0), hP, mG1_lintegral_zero]
      refine le_add_left (le_of_eq ?_)
      have e : ∀ k : ℕ, q k * V k = ENNReal.ofReal (Real.exp s) *
          (q k * ENNReal.ofReal (Real.exp (s * ((k : ℝ) - 1)))) := fun k => by
        rw [hV]; simp only
        rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 3; ring
      simp_rw [e]
      rw [ENNReal.tsum_mul_left, hMgl, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    · rw [hx, hP, mG1_lintegral_succ, indicator_of_notMem (by simp)]
      rw [add_zero]
      refine le_of_eq ?_
      have e : ∀ k : ℕ, q k * V (k + x.pred) = V (x.pred + 1) *
          (q k * ENNReal.ofReal (Real.exp (s * ((k : ℝ) - 1)))) := fun k => by
        rw [hV]; simp only
        rw [hsplit]; ring
      simp_rw [e]
      rw [ENNReal.tsum_mul_left, hMgl, mul_comm]
  -- the chain is irreducible and aperiodic, `{0}` petite
  obtain ⟨_, hirr⟩ := mG1_poisson_isIrreducibleChain H hr hH
  have hψ := isMaximalIrreducibility_count P hirr
  have hq0 : 0 < q 0 := pos_iff_ne_zero.2 (poissonWeight_ne_zero hr hH 0)
  have hP0 : 0 < P 0 {0} := by rw [hP, matKernel_singleton]; simpa [mG1Matrix] using hq0
  obtain ⟨Mz, hMC, hMν, -⟩ := exists_minorization_of_le (P := P) (measurableSet_singleton 0)
    ⟨0, rfl⟩ (ν' := P 0) (fun x hx => by rw [mem_singleton_iff.1 hx]) hP0
  have hap : IsAperiodic P Measure.count := isAperiodic_of_minorization hψ Mz
    (by rw [hMC]; simp) (by rw [hMν]; exact one_pos)
  have hpet : IsPetite P {0} := by
    refine ⟨_, _, proposition_5_5_3 (m := 1) (ν := P 0) ⟨measurableSet_singleton 0, one_pos,
      fun h => by simp [h] at hP0, fun x hx => ?_⟩⟩
    rw [mem_singleton_iff.1 hx, pow_one]
  have hVm : Measurable V := measurable_of_countable _
  have hV1 : ∀ i, 1 ≤ V i := fun i => by
    rw [hV, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hs0.le i.cast_nonneg))
  have hVt : ∀ i, V i ≠ ∞ := fun i => ENNReal.ofReal_ne_top
  have hρ : ENNReal.ofReal Mg < 1 := ENNReal.ofReal_lt_one.2 hsM
  refine ⟨s, hs0, (geometric_ergodic_of_driftV4 hψ hap hVm hV1 hρ ENNReal.ofReal_ne_top hpet
    hdrift (hVt 0)).1, fun μ _ hμ => ?_⟩
  obtain ⟨hsum, hlim⟩ := theorem_16_1_2 hψ hap hVm hV1 hVt hρ ENNReal.ofReal_ne_top hpet hdrift μ
    hμ
  exact ⟨⟨hμ, hlim⟩, hsum⟩

end MeynTweedie.VUniformErgodicity

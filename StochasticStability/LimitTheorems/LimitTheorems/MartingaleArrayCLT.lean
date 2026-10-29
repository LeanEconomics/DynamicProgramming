/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.MartingaleCLT

/-!
# A central limit theorem for martingale difference arrays (used for MT Theorem D.6.4)

The finite-dimensional distributions in the functional CLT (MT Theorem D.6.4, p. 563) are the
laws of weighted sums `Σₖ wₙₖ Dₖ / √n` of martingale differences. This module extends McLeish's
method of `MartingaleCLT` from one sequence to triangular arrays.

**Results.**
* `martingale_array_clt`: let `X i k` (row `i`, `k < Lᵢ`) be `𝓕ₖ₊₁`-measurable, square integrable,
  with `E[X i k | 𝓕ₖ] = 0`, such that almost surely `Σ_{k<Lᵢ} X i k² → σ²` and
  `max_{k<Lᵢ} |X i k| → 0`, and `E Σ_{k<Lᵢ} X i k² ≤ C`. Then `Σ_{k<Lᵢ} X i k ⇒ N(0, σ²)`.
* `martingale_weighted_clt_rows`, `martingale_fidi_clt_rows`: the next two results along rows of
  lengths `rᵢ`, with the averages of `Dₖ²` and `max_{k≤rᵢ} Dₖ²/rᵢ → 0` assumed along the rows.
* `martingale_weighted_clt`: for martingale differences `Dₖ` with `(1/n) Σ_{k<n} Dₖ² → σ²` a.s.,
  `Σ_{k<n} E[Dₖ²] ≤ C n`, and deterministic weights `|w n k| ≤ W` with
  `(1/n) Σ_{k<n} w n k² Dₖ² → τ²` a.s., `n^{−1/2} Σ_{k<n} w n k Dₖ ⇒ N(0, τ²)`.
* `martingale_fidi_clt`: the finite-dimensional CLT for the partial sums `Sₘ = Σ_{k<m} Dₖ`: for
  times `0 ≤ tᵢ ≤ 1` and coefficients `cᵢ`, `n^{−1/2} Σᵢ cᵢ S_{⌊n tᵢ⌋} ⇒ N(0, σ² Σᵢⱼ cᵢcⱼ tᵢ ∧ tⱼ)`.
* Tools: `tendsto_sum_floor_div` (`(1/n) Σ_{k<⌊ns⌋} uₖ → s ℓ` when `(1/n) Σ_{k<n} uₖ → ℓ`),
  `eventually_le_mul_of_tendsto_average` (then eventually `uₖ ≤ ε n` for all `k ≤ n`, so
  `max_{k≤n} |Dₖ| / √n → 0`; `ae_eventually_sq_le_of_tendsto`) and `sum_range_ite_lt`.

The weights of the finite-dimensional sums are `w n k = Σᵢ cᵢ 1{k < ⌊n tᵢ⌋}`; their squares give
`Σᵢⱼ cᵢcⱼ 1{k < ⌊n (tᵢ ∧ tⱼ)⌋}`, whence the covariance `σ² (tᵢ ∧ tⱼ)` of Brownian motion.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {Ω₀ : Type*} [mΩ₀ : MeasurableSpace Ω₀]

/-! ### The array CLT -/

/-- **A martingale-array CLT** (McLeish's method): for each row `i` let `X i k` (`k < Lᵢ`) be
`𝓕ₖ₊₁`-measurable square-integrable martingale differences, `E[X i k | 𝓕ₖ] = 0`. If almost surely
`Σ_{k<Lᵢ} X i k² → σ²` and `max_{k<Lᵢ} |X i k| → 0`, and `E Σ_{k<Lᵢ} X i k² ≤ C`, then
`Σ_{k<Lᵢ} X i k` converges in distribution to `N(0, σ²)`. -/
theorem martingale_array_clt {Q : Measure Ω₀} [IsProbabilityMeasure Q] {ℱ : Filtration ℕ mΩ₀}
    {X : ℕ → ℕ → Ω₀ → ℝ} {L : ℕ → ℕ} (hX : ∀ i k, StronglyMeasurable[ℱ (k + 1)] (X i k))
    (hL2 : ∀ i k, MemLp (X i k) 2 Q) (h0 : ∀ i k, Q[X i k | ℱ k] =ᵐ[Q] 0) {σ2 : ℝ}
    (hσ : 0 ≤ σ2)
    (hvar : ∀ᵐ ω ∂Q, Tendsto (fun i => ∑ k ∈ Finset.range (L i), X i k ω ^ 2) atTop (𝓝 σ2))
    (hmax : ∀ᵐ ω ∂Q, ∀ ε > 0, ∀ᶠ i in atTop, ∀ k < L i, |X i k ω| ≤ ε)
    {C : ℝ} (hbdd : ∀ i, ∑ k ∈ Finset.range (L i), ∫ ω, X i k ω ^ 2 ∂Q ≤ C)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 σ2.toNNReal) Q') :
    TendstoInDistribution (fun (i : ℕ) ω => ∑ k ∈ Finset.range (L i), X i k ω) atTop
      Z (fun _ => Q) Q' := by
  have hXm0 : ∀ i k, Measurable (X i k) := fun i k =>
    (hX i k).measurable.mono (ℱ.le (k + 1)) le_rfl
  refine TendstoInDistribution.of_tendsto_charFun (fun i =>
    (Finset.measurable_sum _ fun k _ => hXm0 i k).aemeasurable) hZ.aemeasurable fun t => ?_
  set L0 : ℂ := ((Real.exp (-(t ^ 2 * σ2 / 2)) : ℝ) : ℂ) with hLdef
  have htarget : charFun (Q'.map Z) t = L0 := by
    rw [hZ.map_eq, charFun_gaussianReal, hLdef, Real.coe_toNNReal _ hσ]
    push_cast
    congr 1
    ring
  rw [htarget]
  have hcf : ∀ i : ℕ, charFun (Q.map fun ω => ∑ k ∈ Finset.range (L i), X i k ω) t =
      ∫ ω, Complex.exp (((t * ∑ k ∈ Finset.range (L i), X i k ω : ℝ) : ℂ) * Complex.I) ∂Q := by
    intro i
    have hSm : Measurable fun ω => ∑ k ∈ Finset.range (L i), X i k ω :=
      Finset.measurable_sum _ fun k _ => hXm0 i k
    have hcont : Continuous fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
      fun_prop
    rw [charFun_apply_real, integral_map hSm.aemeasurable hcont.aestronglyMeasurable]
    congr 1
    ext ω
    push_cast
    ring_nf
  simp_rw [hcf]
  have hC0 : 0 ≤ C := (Finset.sum_nonneg fun k _ => integral_nonneg fun ω => sq_nonneg _).trans
    (hbdd 0)
  set c := σ2 + 1 with hc
  have hc0 : 0 ≤ c := by linarith
  set w : ℕ → ℕ → Ω₀ → ℝ := fun i k ω => truncWeight (X i) c k ω with hw
  set T : ℕ → Ω₀ → ℂ := fun i ω => truncProd (X i) c t (L i) ω with hTdef
  set U : ℕ → Ω₀ → ℂ := fun i ω => ∏ k ∈ Finset.range (L i),
    Complex.exp (((t * (X i k ω * w i k ω)) : ℝ) * Complex.I) /
      (1 + ((t * (X i k ω * w i k ω)) : ℝ) * Complex.I) with hUdef
  have hwm : ∀ i k, Measurable (w i k) := fun i k =>
    Measurable.ite (measurableSet_le (Finset.measurable_sum _ fun j _ => (hXm0 i j).pow_const 2)
      measurable_const) measurable_const measurable_const
  have hxpm : ∀ i k, Measurable fun ω => ((t * (X i k ω * w i k ω) : ℝ) : ℂ) := fun i k =>
    Complex.measurable_ofReal.comp (measurable_const.mul ((hXm0 i k).mul (hwm i k)))
  have hTm : ∀ i, Measurable (T i) := fun i =>
    Finset.measurable_prod _ fun k _ => measurable_const.add ((hxpm i k).mul measurable_const)
  have hUm : ∀ i, Measurable (U i) := fun i =>
    Finset.measurable_prod _ fun k _ => (Complex.measurable_exp.comp
      ((hxpm i k).mul measurable_const)).div (measurable_const.add
        ((hxpm i k).mul measurable_const))
  have hTU : ∀ i ω, Complex.exp (((t * ∑ k ∈ Finset.range (L i), X i k ω * w i k ω : ℝ) : ℂ) *
      Complex.I) = T i ω * U i ω := by
    intro i ω
    rw [Finset.mul_sum]
    exact cexp_sum_eq_prod_mul (fun k => t * (X i k ω * w i k ω)) (L i)
  have hT1 : ∀ i, ∫ ω, T i ω ∂Q = 1 := fun i =>
    integral_truncProd_eq_one (hX i) (hL2 i) (h0 i) hc0 t (L i)
  have hXsq : ∀ i, ∫ ω, ∑ k ∈ Finset.range (L i), X i k ω ^ 2 ∂Q ≤ C := by
    intro i
    rw [integral_finsetSum _ fun k _ => (hL2 i k).integrable_sq]
    exact hbdd i
  have hbdi : ∀ i, Integrable (fun ω => Real.exp (t ^ 2 * c) *
      (1 + t ^ 2 * ∑ k ∈ Finset.range (L i), X i k ω ^ 2)) Q := fun i =>
    ((integrable_const 1).add ((integrable_finsetSum _ fun k _ =>
      (hL2 i k).integrable_sq).const_mul _)).const_mul _
  have hT2 : ∀ i, Integrable (fun ω => ‖T i ω‖ ^ 2) Q := by
    intro i
    refine (hbdi i).mono' ((hTm i).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_truncProd_sq_le (X i) hc0 t (L i) ω
  have hK : ∀ i, ∫ ω, ‖T i ω‖ ^ 2 ∂Q ≤ Real.exp (t ^ 2 * c) * (1 + t ^ 2 * C) := by
    intro i
    calc ∫ ω, ‖T i ω‖ ^ 2 ∂Q ≤ ∫ ω, Real.exp (t ^ 2 * c) *
          (1 + t ^ 2 * ∑ k ∈ Finset.range (L i), X i k ω ^ 2) ∂Q :=
          integral_mono (hT2 i) (hbdi i) fun ω => norm_truncProd_sq_le (X i) hc0 t (L i) ω
      _ = Real.exp (t ^ 2 * c) * (1 + t ^ 2 *
            ∫ ω, ∑ k ∈ Finset.range (L i), X i k ω ^ 2 ∂Q) := by
          rw [integral_const_mul, integral_add (integrable_const 1)
            ((integrable_finsetSum _ fun k _ => (hL2 i k).integrable_sq).const_mul _),
            integral_const_mul, integral_const, probReal_univ, one_smul]
      _ ≤ Real.exp (t ^ 2 * c) * (1 + t ^ 2 * C) := by
          gcongr
          exact hXsq i
  have hU1 : ∀ i ω, ‖U i ω‖ ≤ 1 := fun i ω => by
    rw [hUdef, norm_prod]
    exact Finset.prod_le_one₀ (fun k _ => norm_nonneg _) fun k _ => norm_cexp_div_le_one _
  have hL1 : ‖L0‖ ≤ 1 := norm_cexp_neg_le_one (by positivity)
  -- the almost sure behaviour
  have hae : ∀ᵐ ω ∂Q, (∀ᶠ i in atTop, ∀ k < L i, w i k ω = 1) ∧
      Tendsto (fun i => U i ω) atTop (𝓝 L0) := by
    filter_upwards [hvar, hmax] with ω hω hmω
    set q : ℕ → ℝ := fun i => ∑ k ∈ Finset.range (L i), X i k ω ^ 2 with hq
    have hev : ∀ᶠ i in atTop, q i < c := hω.eventually (eventually_lt_nhds (by linarith))
    have hw1 : ∀ᶠ i in atTop, ∀ k < L i, w i k ω = 1 := by
      filter_upwards [hev] with i hi k hk
      have hle : ∑ j ∈ Finset.range k, X i j ω ^ 2 ≤ c :=
        calc ∑ j ∈ Finset.range k, X i j ω ^ 2 ≤ q i :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk.le)
                fun j _ _ => sq_nonneg _
          _ ≤ c := hi.le
      simp [hw, truncWeight, hle]
    refine ⟨hw1, ?_⟩
    have hexp : Tendsto (fun i => ((Real.exp (-(t ^ 2 * q i / 2)) : ℝ) : ℂ)) atTop
        (𝓝 L0) :=
      (Complex.continuous_ofReal.comp Real.continuous_exp).tendsto _ |>.comp
        (((hω.const_mul (t ^ 2)).div_const 2).neg)
    have hdiff : Tendsto (fun i => U i ω - ((Real.exp (-(t ^ 2 * q i / 2)) : ℝ) : ℂ)) atTop
        (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro η hη
      set ε := η / (2 * (2 * |t| ^ 3 * c + 1)) with hε
      have hε0 : 0 < ε := by positivity
      obtain ⟨N, hN⟩ := eventually_atTop.1 ((hw1.and hev).and (hmω ε hε0))
      refine ⟨N, fun i hi => ?_⟩
      obtain ⟨⟨hwi, hqi⟩, hXi⟩ := hN i hi
      rw [dist_eq_norm, sub_zero]
      have hU' : U i ω = ∏ k ∈ Finset.range (L i),
          Complex.exp (((t * X i k ω) : ℝ) * Complex.I) / (1 + ((t * X i k ω) : ℝ) * Complex.I) :=
        Finset.prod_congr rfl fun k hk => by rw [hwi k (Finset.mem_range.1 hk), mul_one]
      have hq' : -(t ^ 2 * q i / 2) =
          -((∑ k ∈ Finset.range (L i), (t * X i k ω) ^ 2) / 2) := by
        simp only [hq, mul_pow, Finset.mul_sum]
      rw [hU', hq']
      refine (norm_prod_cexp_div_sub_le (fun k => t * X i k ω) (L i)).trans_lt ?_
      have hsum : ∑ k ∈ Finset.range (L i), |t * X i k ω| ^ 3 ≤ |t| ^ 3 * (ε * q i) := by
        have h3 : 0 ≤ |t| ^ 3 := by positivity
        calc ∑ k ∈ Finset.range (L i), |t * X i k ω| ^ 3
            ≤ ∑ k ∈ Finset.range (L i), |t| ^ 3 * (ε * X i k ω ^ 2) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have h1 := hXi k (Finset.mem_range.1 hk)
              rw [abs_mul, mul_pow]
              have : |X i k ω| ^ 3 ≤ ε * X i k ω ^ 2 := by
                have e : |X i k ω| ^ 3 = |X i k ω| * X i k ω ^ 2 := by
                  rw [← sq_abs (X i k ω)]; ring
                rw [e]
                exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
              exact mul_le_mul_of_nonneg_left this h3
          _ = |t| ^ 3 * (ε * q i) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
      have hq0 : 0 ≤ q i := Finset.sum_nonneg fun k _ => sq_nonneg _
      have h4 : 2 * (|t| ^ 3 * (ε * q i)) ≤ ε * (2 * |t| ^ 3 * c) := by
        have : 2 * (|t| ^ 3 * (ε * q i)) = ε * (2 * |t| ^ 3 * q i) := by ring
        rw [this]
        gcongr
      have h5 : ε * (2 * |t| ^ 3 * c) < η := by
        rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [show 0 ≤ 2 * |t| ^ 3 * c by positivity]
      linarith
    have := hdiff.add hexp
    rw [zero_add] at this
    exact this.congr fun i => by ring
  have hmain := tendsto_integral_mul_of_bdd hTm hUm hT1 hT2 hK hU1 hL1
    (hae.mono fun ω h => h.2)
  have hmeasS : ∀ i, Measurable fun ω => Complex.exp
      (((t * ∑ k ∈ Finset.range (L i), X i k ω : ℝ) : ℂ) * Complex.I) := fun i =>
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (measurable_const.mul
      (Finset.measurable_sum _ fun k _ => hXm0 i k))).mul measurable_const)
  have hmeasS' : ∀ i, Measurable fun ω => Complex.exp
      (((t * ∑ k ∈ Finset.range (L i), X i k ω * w i k ω : ℝ) : ℂ) * Complex.I) := fun i =>
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (measurable_const.mul
      (Finset.measurable_sum _ fun k _ => (hXm0 i k).mul (hwm i k)))).mul measurable_const)
  have hgap : Tendsto (fun i => ∫ ω, (Complex.exp
      (((t * ∑ k ∈ Finset.range (L i), X i k ω : ℝ) : ℂ) * Complex.I) - Complex.exp
      (((t * ∑ k ∈ Finset.range (L i), X i k ω * w i k ω : ℝ) : ℂ) * Complex.I)) ∂Q) atTop
      (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := Q) (f := fun _ => (0 : ℂ))
      (fun _ => (2 : ℝ)) (fun i => ((hmeasS i).sub (hmeasS' i)).aestronglyMeasurable)
      (integrable_const 2) (fun i => Eventually.of_forall fun ω => by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]; norm_num)
      (hae.mono fun ω h => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [h.1] with i hi
        have : ∑ k ∈ Finset.range (L i), X i k ω * w i k ω =
            ∑ k ∈ Finset.range (L i), X i k ω :=
          Finset.sum_congr rfl fun k hk => by rw [hi k (Finset.mem_range.1 hk), mul_one]
        simp only [Pi.sub_apply]
        rw [this, sub_self])
    simpa using h
  have hintS : ∀ i, Integrable (fun ω => Complex.exp
      (((t * ∑ k ∈ Finset.range (L i), X i k ω : ℝ) : ℂ) * Complex.I)) Q := fun i =>
    Integrable.of_bound (hmeasS i).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by rw [Complex.norm_exp_ofReal_mul_I])
  have hintS' : ∀ i, Integrable (fun ω => Complex.exp
      (((t * ∑ k ∈ Finset.range (L i), X i k ω * w i k ω : ℝ) : ℂ) * Complex.I)) Q := fun i =>
    Integrable.of_bound (hmeasS' i).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by rw [Complex.norm_exp_ofReal_mul_I])
  have hfinal := hgap.add hmain
  rw [zero_add] at hfinal
  refine hfinal.congr fun i => ?_
  have e1 : ∫ ω, T i ω * U i ω ∂Q = ∫ ω, Complex.exp
      (((t * ∑ k ∈ Finset.range (L i), X i k ω * w i k ω : ℝ) : ℂ) * Complex.I) ∂Q :=
    integral_congr_ae (Eventually.of_forall fun ω => (hTU i ω).symm)
  have hsubint : Integrable (fun ω => Complex.exp
      (((t * ∑ k ∈ Finset.range (L i), X i k ω : ℝ) : ℂ) * Complex.I) - Complex.exp
      (((t * ∑ k ∈ Finset.range (L i), X i k ω * w i k ω : ℝ) : ℂ) * Complex.I)) Q :=
    (hintS i).sub (hintS' i)
  rw [e1, ← integral_add hsubint (hintS' i)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [sub_add_cancel]

/-! ### Elementary limits -/

/-- If `(1/n) Σ_{k<n} uₖ → ℓ` with `uₖ ≥ 0`, then for every `ε > 0` eventually `uₖ ≤ ε n` for all
`k ≤ n`. -/
theorem eventually_le_mul_of_tendsto_average {u : ℕ → ℝ} (hu0 : ∀ k, 0 ≤ u k) {ℓ : ℝ}
    (hu : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, u k) / n) atTop (𝓝 ℓ)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, ∀ k ≤ n, u k ≤ ε * n := by
  have h1 := tendsto_term_div_of_tendsto_average hu
  obtain ⟨K, hK⟩ := eventually_atTop.1 (h1.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by
    positivity)))
  set M := ∑ j ∈ Finset.range K, u j with hM
  obtain ⟨N, hN⟩ := exists_nat_gt (M / ε)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn k hk
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  by_cases hkK : K ≤ k
  · have h2 := hK k hkK
    rw [div_lt_iff₀ (by positivity)] at h2
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    nlinarith
  · push Not at hkK
    have h3 : u k ≤ M := Finset.single_le_sum (fun j _ => hu0 j) (Finset.mem_range.2 hkK)
    have h4 : M < ε * n := by
      rw [div_lt_iff₀ hε] at hN
      nlinarith
    linarith

/-- `(1/n) Σ_{k<⌊n s⌋} uₖ → s ℓ` when `(1/m) Σ_{k<m} uₖ → ℓ` and `s ≥ 0`. -/
theorem tendsto_sum_floor_div {u : ℕ → ℝ} {ℓ : ℝ}
    (hu : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, u k) / n) atTop (𝓝 ℓ)) {s : ℝ}
    (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range ⌊(n : ℝ) * s⌋₊, u k) / n) atTop (𝓝 (s * ℓ)) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  have hm : Tendsto (fun n : ℕ => ⌊(n : ℝ) * s⌋₊) atTop atTop := by
    refine (tendsto_nat_floor_mul_atTop s hs).congr fun n => ?_
    rw [mul_comm]
  have hr : Tendsto (fun n : ℕ => (⌊(n : ℝ) * s⌋₊ : ℝ) / n) atTop (𝓝 s) := by
    refine ((tendsto_nat_floor_mul_div_atTop hs.le).comp tendsto_natCast_atTop_atTop).congr
      fun n => ?_
    simp only [Function.comp_apply, mul_comm s]
  have h := (hu.comp hm).mul hr
  rw [mul_comm ℓ s] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  rcases Nat.eq_zero_or_pos ⌊(n : ℝ) * s⌋₊ with h0 | h0
  · rw [h0]; simp
  · have : (⌊(n : ℝ) * s⌋₊ : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    field_simp

omit [MeasurableSpace Ω₀] in
/-- `Σ_{k<n} 1{k < m} f k = Σ_{k<m} f k` for `m ≤ n`. -/
theorem sum_range_ite_lt (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Finset.range n, (if k < m then f k else 0) = ∑ k ∈ Finset.range m, f k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Finset.sum_range_add]
  have h1 : ∑ k ∈ Finset.range m, (if k < m then f k else 0) = ∑ k ∈ Finset.range m, f k :=
    Finset.sum_congr rfl fun k hk => by simp [Finset.mem_range.1 hk]
  have h2 : ∑ x ∈ Finset.range j, (if m + x < m then f (m + x) else 0) = 0 :=
    Finset.sum_eq_zero fun x _ => by simp
  rw [h1, h2, add_zero]

/-! ### Weighted sums of martingale differences -/

/-- **A CLT for weighted martingale sums along rows**: for martingale differences `Dₖ` with
`Σ_{k<n} E[Dₖ²] ≤ C n`, row lengths `rᵢ` with `max_{k≤rᵢ} Dₖ²/rᵢ → 0` a.s., and deterministic
weights `|w i k| ≤ W` with `(1/rᵢ) Σ_{k<rᵢ} w i k² Dₖ² → τ²` a.s.,
`rᵢ^{−1/2} Σ_{k<rᵢ} w i k Dₖ ⇒ N(0, τ²)`. -/
theorem martingale_weighted_clt_rows {Q : Measure Ω₀} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ₀} {D : ℕ → Ω₀ → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    {C : ℝ} (hbdd : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂Q ≤ C * n) {r : ℕ → ℕ}
    (hmax : ∀ᵐ ω ∂Q, ∀ ε > 0, ∀ᶠ i in atTop, ∀ k ≤ r i, D k ω ^ 2 ≤ ε * r i)
    {w : ℕ → ℕ → ℝ} {W : ℝ} (hW : ∀ i k, |w i k| ≤ W) {τ2 : ℝ} (hτ : 0 ≤ τ2)
    (hwvar : ∀ᵐ ω ∂Q, Tendsto (fun i : ℕ =>
      (∑ k ∈ Finset.range (r i), w i k ^ 2 * D k ω ^ 2) / r i) atTop (𝓝 τ2))
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 τ2.toNNReal) Q') :
    TendstoInDistribution (fun (i : ℕ) ω => (√(r i : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (r i), w i k * D k ω) atTop Z (fun _ => Q) Q' := by
  set X : ℕ → ℕ → Ω₀ → ℝ := fun i k ω => (√(r i : ℝ))⁻¹ * (w i k * D k ω) with hXdef
  have hXsq : ∀ i k ω, X i k ω ^ 2 = w i k ^ 2 * D k ω ^ 2 / r i := fun i k ω => by
    simp only [hXdef]
    rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), mul_pow, inv_mul_eq_div]
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0 0)
  have hX : ∀ i k, StronglyMeasurable[ℱ (k + 1)] (X i k) := fun i k =>
    ((hD k).const_mul (w i k)).const_mul _
  have hXL2 : ∀ i k, MemLp (X i k) 2 Q := fun i k => ((hL2 k).const_mul _).const_mul _
  have hX0 : ∀ i k, Q[X i k | ℱ k] =ᵐ[Q] 0 := fun i k => by
    have := condExp_smul (μ := Q) ((√(r i : ℝ))⁻¹ * w i k) (D k) (ℱ k)
    have e : X i k = ((√(r i : ℝ))⁻¹ * w i k) • D k := by
      ext ω; simp only [hXdef, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    refine this.trans ((h0 k).mono fun ω h => ?_)
    simp [h]
  have hsum : ∀ i ω, ∑ k ∈ Finset.range (r i), X i k ω ^ 2 =
      (∑ k ∈ Finset.range (r i), w i k ^ 2 * D k ω ^ 2) / r i := fun i ω => by
    simp only [hXsq, Finset.sum_div]
  have hfun : (fun (i : ℕ) ω => (√(r i : ℝ))⁻¹ * ∑ k ∈ Finset.range (r i), w i k * D k ω) =
      fun (i : ℕ) ω => ∑ k ∈ Finset.range (r i), X i k ω := by
    funext i ω; simp only [hXdef, Finset.mul_sum]
  rw [hfun]
  refine martingale_array_clt (L := r) hX hXL2 hX0 hτ ?_ ?_ (C := W ^ 2 * C) ?_ hZ
  · filter_upwards [hwvar] with ω hω
    exact hω.congr fun i => (hsum i ω).symm
  · filter_upwards [hmax] with ω hω ε hε
    have hε' : 0 < ε ^ 2 / (W ^ 2 + 1) := by positivity
    filter_upwards [hω _ hε'] with i hi k hk
    have hn0 : (0 : ℝ) < r i := by exact_mod_cast (show 0 < r i by omega)
    have hsq : X i k ω ^ 2 ≤ ε ^ 2 := by
      rw [hXsq, div_le_iff₀ hn0]
      have h1 : w i k ^ 2 ≤ W ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hW i k) 2
      have h2 := hi k hk.le
      calc w i k ^ 2 * D k ω ^ 2 ≤ W ^ 2 * (ε ^ 2 / (W ^ 2 + 1) * r i) :=
            mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
        _ ≤ ε ^ 2 * r i := by
            rw [← mul_assoc, ← mul_div_assoc, mul_comm (W ^ 2) (ε ^ 2), mul_div_assoc]
            gcongr
            · exact mul_le_of_le_one_right (sq_nonneg _)
                ((div_le_one (by positivity)).2 (by linarith))
    rw [← sq_abs (X i k ω)] at hsq
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) hε.le two_ne_zero).1 hsq
  · intro i
    rcases Nat.eq_zero_or_pos (r i) with h | hn
    · rw [h]
      simp only [Finset.range_zero, Finset.sum_empty]
      have := hbdd 1
      simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_one, mul_one] at this
      exact mul_nonneg (sq_nonneg W) ((integral_nonneg fun ω => sq_nonneg _).trans this)
    have hn0 : (0 : ℝ) < r i := by exact_mod_cast hn
    simp_rw [hXsq]
    have e : ∀ k, ∫ ω, w i k ^ 2 * D k ω ^ 2 / r i ∂Q =
        w i k ^ 2 * (∫ ω, D k ω ^ 2 ∂Q) / r i :=
      fun k => by rw [integral_div, integral_const_mul]
    simp_rw [e]
    rw [← Finset.sum_div, div_le_iff₀ hn0]
    calc ∑ k ∈ Finset.range (r i), w i k ^ 2 * ∫ ω, D k ω ^ 2 ∂Q
        ≤ ∑ k ∈ Finset.range (r i), W ^ 2 * ∫ ω, D k ω ^ 2 ∂Q := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_
            (integral_nonneg fun ω => sq_nonneg _)
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hW i k) 2
      _ = W ^ 2 * ∑ k ∈ Finset.range (r i), ∫ ω, D k ω ^ 2 ∂Q := by rw [Finset.mul_sum]
      _ ≤ W ^ 2 * (C * r i) := mul_le_mul_of_nonneg_left (hbdd (r i)) (sq_nonneg W)
      _ = W ^ 2 * C * r i := by ring

/-- `max_{k≤n} Dₖ²/n → 0` along the full sequence when `(1/n) Σ_{k<n} Dₖ² converges. -/
theorem ae_eventually_sq_le_of_tendsto {Q : Measure Ω₀} {D : ℕ → Ω₀ → ℝ} {σ2 : ℝ}
    (hvar : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, D k ω ^ 2) / n) atTop
      (𝓝 σ2)) :
    ∀ᵐ ω ∂Q, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k ≤ n, D k ω ^ 2 ≤ ε * n := by
  filter_upwards [hvar] with ω hω ε hε
  exact eventually_le_mul_of_tendsto_average (fun k => sq_nonneg (D k ω)) hω hε

/-- **A CLT for weighted martingale sums**: for martingale differences `Dₖ` with
`(1/n) Σ_{k<n} Dₖ² → σ²` a.s. and `Σ_{k<n} E[Dₖ²] ≤ C n`, and deterministic weights
`|w n k| ≤ W` with `(1/n) Σ_{k<n} w n k² Dₖ² → τ²` a.s., `n^{−1/2} Σ_{k<n} w n k Dₖ ⇒ N(0, τ²)`. -/
theorem martingale_weighted_clt {Q : Measure Ω₀} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ₀} {D : ℕ → Ω₀ → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {σ2 : ℝ}
    (hvar : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, D k ω ^ 2) / n) atTop
      (𝓝 σ2))
    {C : ℝ} (hbdd : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂Q ≤ C * n)
    {w : ℕ → ℕ → ℝ} {W : ℝ} (hW : ∀ n k, |w n k| ≤ W) {τ2 : ℝ} (hτ : 0 ≤ τ2)
    (hwvar : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, w n k ^ 2 * D k ω ^ 2) / n)
      atTop (𝓝 τ2))
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 τ2.toNNReal) Q') :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, w n k * D k ω)
      atTop Z (fun _ => Q) Q' :=
  martingale_weighted_clt_rows (r := fun n => n) hD hL2 h0 hbdd
    (ae_eventually_sq_le_of_tendsto hvar) hW hτ hwvar hZ

/-! ### The finite-dimensional CLT for the partial-sum process -/

/-- **The finite-dimensional CLT along rows** for martingale partial sums `Sₘ = Σ_{k<m} Dₖ`: for
times `tⱼ ≤ 1`, row lengths `rᵢ` with `(1/rᵢ) Σ_{k<⌊rᵢ tⱼ⌋} Dₖ² → tⱼ σ²` and
`max_{k≤rᵢ} Dₖ²/rᵢ → 0` a.s., and `Σ_{k<n} E[Dₖ²] ≤ C n`,
`rᵢ^{−1/2} Σⱼ cⱼ S_{⌊rᵢ tⱼ⌋} ⇒ N(0, σ² Σⱼₗ cⱼ cₗ min(tⱼ, tₗ))`. -/
theorem martingale_fidi_clt_rows {Q : Measure Ω₀} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ₀} {D : ℕ → Ω₀ → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    {C : ℝ} (hbdd : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂Q ≤ C * n)
    {K : ℕ} (t : Fin K → ℝ) (ht1 : ∀ i, t i ≤ 1) (c : Fin K → ℝ)
    {σ2 : ℝ} {r : ℕ → ℕ}
    (hvt : ∀ j, ∀ᵐ ω ∂Q, Tendsto (fun i : ℕ =>
      (∑ k ∈ Finset.range ⌊(r i : ℝ) * t j⌋₊, D k ω ^ 2) / r i) atTop (𝓝 (t j * σ2)))
    (hmax : ∀ᵐ ω ∂Q, ∀ ε > 0, ∀ᶠ i in atTop, ∀ k ≤ r i, D k ω ^ 2 ≤ ε * r i)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0
      (σ2 * ∑ i, ∑ j, c i * c j * min (t i) (t j)).toNNReal) Q') :
    TendstoInDistribution (fun (i : ℕ) ω => (√(r i : ℝ))⁻¹ *
      ∑ j, c j * ∑ k ∈ Finset.range ⌊(r i : ℝ) * t j⌋₊, D k ω) atTop Z (fun _ => Q) Q' := by
  set w : ℕ → ℕ → ℝ := fun n k => ∑ i, c i * (if k < ⌊(r n : ℝ) * t i⌋₊ then 1 else 0) with hw
  have hfl : ∀ (n : ℕ) i, ⌊(r n : ℝ) * t i⌋₊ ≤ r n := fun n i => by
    refine Nat.floor_le_of_le ?_
    calc (r n : ℝ) * t i ≤ r n * 1 := mul_le_mul_of_nonneg_left (ht1 i) (Nat.cast_nonneg _)
      _ = r n := mul_one _
  have hrep : ∀ (n : ℕ) ω, ∑ i, c i * ∑ k ∈ Finset.range ⌊(r n : ℝ) * t i⌋₊, D k ω =
      ∑ k ∈ Finset.range (r n), w n k * D k ω := by
    intro n ω
    simp only [hw, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_range_ite_lt (fun k => D k ω) (hfl n i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  have hW : ∀ n k, |w n k| ≤ ∑ i, |c i| := fun n k => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    split_ifs <;> simp
  have hmin : ∀ (n k : ℕ) i j, (if k < ⌊(r n : ℝ) * t i⌋₊ then (1 : ℝ) else 0) *
      (if k < ⌊(r n : ℝ) * t j⌋₊ then 1 else 0) =
        if k < ⌊(r n : ℝ) * min (t i) (t j)⌋₊ then 1 else 0 := by
    intro n k i j
    have e : ⌊(r n : ℝ) * min (t i) (t j)⌋₊ = min ⌊(r n : ℝ) * t i⌋₊ ⌊(r n : ℝ) * t j⌋₊ := by
      rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg _)]
      exact Monotone.map_min Nat.floor_mono
    rw [e]
    by_cases h1 : k < ⌊(r n : ℝ) * t i⌋₊ <;> by_cases h2 : k < ⌊(r n : ℝ) * t j⌋₊ <;>
      simp [h1, h2, lt_min_iff]
  have hwvar : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range (r n), w n k ^ 2 * D k ω ^ 2) / r n)
      atTop (𝓝 (σ2 * ∑ i, ∑ j, c i * c j * min (t i) (t j))) := by
    filter_upwards [ae_all_iff.2 hvt] with ω hω
    have hij : ∀ i j, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (r n),
        (if k < ⌊(r n : ℝ) * min (t i) (t j)⌋₊ then (1 : ℝ) else 0) * D k ω ^ 2) / r n) atTop
        (𝓝 (min (t i) (t j) * σ2)) := by
      intro i j
      have hm : ∃ l, min (t i) (t j) = t l := by
        rcases le_total (t i) (t j) with h | h
        · exact ⟨i, min_eq_left h⟩
        · exact ⟨j, min_eq_right h⟩
      obtain ⟨l, hl⟩ := hm
      rw [hl]
      refine (hω l).congr fun n => ?_
      congr 1
      rw [← sum_range_ite_lt (fun k => D k ω ^ 2) (hfl n l)]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> ring
    have hall := tendsto_finsetSum (Finset.univ : Finset (Fin K)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin K)) fun j _ => (hij i j).const_mul (c i * c j)
    have hlim : ∑ i, ∑ j, c i * c j * (min (t i) (t j) * σ2) =
        σ2 * ∑ i, ∑ j, c i * c j * min (t i) (t j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hlim] at hall
    refine hall.congr fun n => ?_
    have e : ∀ k, w n k ^ 2 * D k ω ^ 2 = ∑ i, ∑ j, c i * c j *
        ((if k < ⌊(r n : ℝ) * min (t i) (t j)⌋₊ then (1 : ℝ) else 0) * D k ω ^ 2) := by
      intro k
      simp only [hw]
      rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hmin n k i j]
      ring
    simp_rw [e]
    have e2 : ∑ k ∈ Finset.range (r n), ∑ i, ∑ j, c i * c j *
        ((if k < ⌊(r n : ℝ) * min (t i) (t j)⌋₊ then (1 : ℝ) else 0) * D k ω ^ 2) =
        ∑ i, ∑ j, ∑ k ∈ Finset.range (r n), c i * c j *
        ((if k < ⌊(r n : ℝ) * min (t i) (t j)⌋₊ then (1 : ℝ) else 0) * D k ω ^ 2) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [e2]
    simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  have hτ0 : 0 ≤ σ2 * ∑ i, ∑ j, c i * c j * min (t i) (t j) := by
    obtain ⟨ω, hω⟩ := hwvar.exists
    exact ge_of_tendsto' hω fun n => div_nonneg (Finset.sum_nonneg fun k _ =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hfun : (fun (n : ℕ) ω => (√(r n : ℝ))⁻¹ *
      ∑ i, c i * ∑ k ∈ Finset.range ⌊(r n : ℝ) * t i⌋₊, D k ω) =
      fun (n : ℕ) ω => (√(r n : ℝ))⁻¹ * ∑ k ∈ Finset.range (r n), w n k * D k ω := by
    funext n ω; rw [hrep]
  rw [hfun]
  exact martingale_weighted_clt_rows hD hL2 h0 hbdd hmax hW hτ0 hwvar hZ

/-- **The finite-dimensional CLT** for martingale partial sums `Sₘ = Σ_{k<m} Dₖ`: under the
hypotheses of `martingale_clt`, for times `0 ≤ tᵢ ≤ 1` and coefficients `cᵢ`,
`n^{−1/2} Σᵢ cᵢ S_{⌊n tᵢ⌋}` converges in distribution to `N(0, σ² Σᵢⱼ cᵢ cⱼ min(tᵢ, tⱼ))`. -/
theorem martingale_fidi_clt {Q : Measure Ω₀} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ₀} {D : ℕ → Ω₀ → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {σ2 : ℝ}
    (hvar : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, D k ω ^ 2) / n) atTop
      (𝓝 σ2))
    {C : ℝ} (hbdd : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂Q ≤ C * n)
    {K : ℕ} (t : Fin K → ℝ) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) (c : Fin K → ℝ)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0
      (σ2 * ∑ i, ∑ j, c i * c j * min (t i) (t j)).toNNReal) Q') :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ *
      ∑ i, c i * ∑ k ∈ Finset.range ⌊(n : ℝ) * t i⌋₊, D k ω) atTop Z (fun _ => Q) Q' :=
  martingale_fidi_clt_rows (r := fun n => n) hD hL2 h0 hbdd t ht1 c
    (fun j => hvar.mono fun _ hω => tendsto_sum_floor_div hω (ht0 j))
    (ae_eventually_sq_le_of_tendsto hvar) hZ

end MeynTweedie.LimitTheorems

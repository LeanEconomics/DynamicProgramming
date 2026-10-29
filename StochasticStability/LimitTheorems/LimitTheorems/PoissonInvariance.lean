/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.PoissonEquation

/-!
# Invariance equations and Poisson's equation (MT §17.7, commentary)

Meyn and Tweedie, Theorems 17.7.1–17.7.2 and Lemma 17.7.3, pp. 459–461. For `f ≥ 1` with
`π(f) < ∞` and an `f`-regular set `C ∈ B⁺(X)`, `V* = G_C(·, f)`,
`V*(x) = E_x[Σ_{k=0}^{σ_C} f(Φₖ)]` (17.60) (`gKernelFn P C f`), and
`f* = f − 1_C U_C(·, f)` (17.62).

* `tendsto_toReal_lintegral_of_fNorm`: `‖Pⁿ(x, ·) − π‖_f → 0` gives `Pⁿφ(x) → π(φ)` for
  `0 ≤ φ ≤ K f`.
* `lintegral_pow_add_sum`: iterating `PG + f = G + u` gives
  `PⁿG + Σ_{k<n} Pᵏf = G + Σ_{k<n} Pᵏu`.
* **Lemma 17.7.3** (`lemma_17_7_3`, p. 460): (i) `V*` is finite on a full absorbing set;
  (ii) (17.61) in the form `PV* + f = V* + 1_C U_C(·, f)`, and `f*` has `π`-mean zero
  (`π(1_C U_C f) = π(f)`, the generalized Kac theorem (10.2)); (iii) the first limit,
  `(1/n) E_x[V*(Φₙ)] → 0` for every `x` with `V*(x) < ∞`.
* **Theorem 17.7.2** (`theorem_17_7_2`, p. 460): if `Ph = h − g + η` with `|g| ≤ c f` and
  `|h| ≤ c V*`, then `π(g) = η`, so `h` solves Poisson's equation with forcing function `g`.
* **Theorem 17.7.1** (`theorem_17_7_1`, p. 459): under (V3) with `V` everywhere finite, `f ≥ 1`
  and `C` petite, without `π(V) < ∞`, there is `R` such that for every `|g| ≤ f` Poisson's
  equation has the solution `ĝ(x) = Σₙ (Pⁿg(x) − Pⁿg(x₀))` with `|ĝ| ≤ R (V + 1)`. The proof
  differs from the book's (the split chain `G_α̌(x, g)`, or the resolvent): the series converges by
  the bound `Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f ≤ A (V(x) + V(y)) + B` (Theorem 14.3.4,
  `tsum_fNorm_le_of_driftV3`) and telescopes by the `f`-Norm Ergodic Theorem.

**Hypotheses and omissions.** The chain is assumed aperiodic in all three results, so that the
`f`-Norm Ergodic Theorem 14.0.1 and (14.24) apply; the book handles the periodic case through
Theorem 14.3.6 (17.7.2, 17.7.3) and the resolvent `K_{a_ε}` (17.7.1), now proved in
`PeriodicPoisson` (`theorem_17_7_1_periodic`) and `PeriodicInvariance`
(`theorem_17_7_2_periodic`, `lemma_17_7_3_periodic`).
The book defines `V*` for any `C ∈ B⁺(X)` but invokes `f`-regularity of `C` for its finiteness
(the remark before (17.60)); `C` is taken `f`-regular. The second limit of Lemma 17.7.3 (iii),
`E_x[V*(Φₖ) 1{τ_C > k}] → 0`, is not used by Theorem 17.7.2 and is not formalised.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Convergence of expectations from `f`-norm convergence -/

/-- `‖μₙ − ν‖_f → 0` gives `μₙ(φ) → ν(φ)` for measurable `0 ≤ φ ≤ K f`, `K < ∞`, when `μₙ(f)`
and `ν(f)` are finite. -/
theorem tendsto_toReal_lintegral_of_fNorm {f : X → ℝ≥0∞} (hf : Measurable f)
    {μs : ℕ → Measure X} {ν : Measure X} (h : Tendsto (fun n => fNorm f (μs n) ν) atTop (𝓝 0))
    (hμ : ∀ n, ∫⁻ x, f x ∂μs n ≠ ∞) (hν : ∫⁻ x, f x ∂ν ≠ ∞) {φ : X → ℝ≥0∞}
    (hφm : Measurable φ) {K : ℝ≥0∞} (hK : K ≠ ∞) (hφ : ∀ x, φ x ≤ K * f x) :
    Tendsto (fun n => (∫⁻ x, φ x ∂μs n).toReal) atTop (𝓝 (∫⁻ x, φ x ∂ν).toReal) := by
  rcases eq_or_ne K 0 with hK0 | hK0
  · have h0 : ∀ x, φ x = 0 := fun x => le_antisymm (by simpa [hK0] using hφ x) zero_le
    simp only [h0, lintegral_zero, ENNReal.toReal_zero]
    exact tendsto_const_nhds
  have hKr : 0 < K.toReal := ENNReal.toReal_pos hK0 hK
  set g : X → ℝ := fun x => (φ x).toReal / K.toReal with hg
  have hgm : Measurable g := hφm.ennreal_toReal.div_const _
  have hgf : ∀ x, ENNReal.ofReal |g x| ≤ f x := fun x => by
    rw [hg, abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg hKr.le)]
    rcases eq_or_ne (f x) ∞ with hfx | hfx
    · rw [hfx]; exact le_top
    have hφx : φ x ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hK hfx) (hφ x)
    rw [ENNReal.ofReal_div_of_pos hKr, ENNReal.ofReal_toReal hφx, ENNReal.ofReal_toReal hK,
      ENNReal.div_le_iff hK0 hK, mul_comm]
    exact hφ x
  have ht := (tendsto_integral_of_tendsto_fNorm h hμ hν hgm hgf).const_mul K.toReal
  have hint : ∀ μ : Measure X, ∫⁻ x, f x ∂μ ≠ ∞ →
      K.toReal * ∫ x, g x ∂μ = (∫⁻ x, φ x ∂μ).toReal := fun μ hμf => by
    rw [hg, integral_div, mul_div_cancel₀ _ hKr.ne']
    have hfin : ∀ᵐ x ∂μ, φ x < ∞ := by
      filter_upwards [ae_lt_top' hf.aemeasurable hμf] with x hx
      exact lt_of_le_of_lt (hφ x) (ENNReal.mul_lt_top hK.lt_top hx)
    exact integral_toReal hφm.aemeasurable hfin
  rw [← hint ν hν]
  exact ht.congr fun n => hint (μs n) (hμ n)

/-! ### Iterating an additive drift identity -/

/-- If `PG + f = G + u` pointwise, then `PⁿG + Σ_{k<n} Pᵏf = G + Σ_{k<n} Pᵏu`. -/
theorem lintegral_pow_add_sum {P : Kernel X X} {G f u : X → ℝ≥0∞} (hG : Measurable G)
    (hf : Measurable f) (hu : Measurable u)
    (hstep : ∀ y, ∫⁻ z, G z ∂P y + f y = G y + u y) (n : ℕ) (x : X) :
    ∫⁻ y, G y ∂(P ^ n : Kernel X X) x + ∑ k ∈ Finset.range n, ∫⁻ y, f y ∂(P ^ k : Kernel X X) x =
      G x + ∑ k ∈ Finset.range n, ∫⁻ y, u y ∂(P ^ k : Kernel X X) x := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    rw [pow_zero]
    exact lintegral_dirac' x hG
  | succ n ih =>
    have hone : ∫⁻ y, G y ∂(P ^ (n + 1) : Kernel X X) x + ∫⁻ y, f y ∂(P ^ n : Kernel X X) x =
        ∫⁻ y, G y ∂(P ^ n : Kernel X X) x + ∫⁻ y, u y ∂(P ^ n : Kernel X X) x := by
      rw [pow_succ']
      change ∫⁻ y, G y ∂(P ∘ₖ (P ^ n : Kernel X X)) x + _ = _
      rw [Kernel.lintegral_comp _ _ _ hG, ← lintegral_add_right _ hf, ← lintegral_add_right _ hu]
      exact lintegral_congr fun y => hstep y
    rw [Finset.sum_range_succ, Finset.sum_range_succ, add_left_comm, hone, ← add_assoc,
      add_comm (∑ k ∈ Finset.range n, ∫⁻ y, f y ∂(P ^ k : Kernel X X) x), ih, add_assoc]

/-! ### Lemma 17.7.3 -/

variable [MeasurableSpace.CountablyGenerated X]

/-- The bounds behind Lemma 17.7.3 for an `f`-regular `C ∈ B⁺(X)`: there is `M < ∞` with
`f ≤ M` and `U_C(·, f) ≤ M + M` on `C`, `G_C(·, f)` solves (V3) with `b = M + M`,
`PⁿG_C(·, f)(x) ≤ G_C(x, f) + n(M + M)`, and `C` is petite and non-empty. -/
theorem gKernelFn_bounds {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} (hC : IsFRegularSet P ψ f C) (hψC : 0 < ψ C) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ (∀ y ∈ C, f y ≤ M) ∧ (∀ y ∈ C, tabooPotFn P C f y ≤ M + M) ∧
      DriftV3 P (gKernelFn P C f) f (M + M) C ∧ IsPetite P C ∧ C.Nonempty ∧
      ∀ (n : ℕ) (x : X), ∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x ≤
        gKernelFn P C f x + (n : ℝ≥0∞) * (M + M) := by
  have hCm := hC.1
  obtain ⟨M, hM, hbound⟩ := hC.2 C hCm hψC
  have hfC : ∀ y ∈ C, f y ≤ M := fun y hy => (le_fSumReturn P C hf y).trans (hbound y hy)
  have hU : ∀ y ∈ C, tabooPotFn P C f y ≤ M + M := fun y hy =>
    (tabooPotFn_le hCm hf hfC y).trans (add_le_add (hbound y hy) le_rfl)
  have hGm := measurable_gKernelFn (P := P) hCm hf
  have huM : ∀ y, C.indicator (tabooPotFn P C f) y ≤ M + M := fun y => by
    by_cases hy : y ∈ C
    · rw [indicator_of_mem hy]; exact hU y hy
    · rw [indicator_of_notMem hy]; exact zero_le
  refine ⟨M, hM, hfC, hU, driftV3_gKernelFn hCm hf hU,
    (theorem_14_2_3_ii hψ hf hf1 hC hψC).1, nonempty_of_measure_ne_zero hψC.ne', fun n x => ?_⟩
  have hiter := lintegral_pow_add_sum (P := P) hGm hf
    ((measurable_tabooPotFn P hCm hf).indicator hCm) (fun y => theorem_11_3_5_i P hCm hf y) n x
  calc ∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x
      ≤ ∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x +
        ∑ k ∈ Finset.range n, ∫⁻ y, f y ∂(P ^ k : Kernel X X) x := le_self_add
    _ = gKernelFn P C f x + ∑ k ∈ Finset.range n,
        ∫⁻ y, C.indicator (tabooPotFn P C f) y ∂(P ^ k : Kernel X X) x := hiter
    _ ≤ gKernelFn P C f x + n * (M + M) := by
        refine add_le_add le_rfl ?_
        calc ∑ k ∈ Finset.range n, ∫⁻ y, C.indicator (tabooPotFn P C f) y ∂(P ^ k : Kernel X X) x
            ≤ ∑ _k ∈ Finset.range n, (M + M) := Finset.sum_le_sum fun k _ => by
              have := isMarkovKernel_pow P k
              calc ∫⁻ y, C.indicator (tabooPotFn P C f) y ∂(P ^ k : Kernel X X) x
                  ≤ ∫⁻ _y, (M + M) ∂(P ^ k : Kernel X X) x := lintegral_mono huM
                _ = M + M := by rw [lintegral_const, measure_univ, mul_one]
          _ = n * (M + M) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Lemma 17.7.3** (MT p. 460): for an aperiodic `ψ`-irreducible chain with invariant
probability `π`, `f ≥ 1` with `π(f) < ∞` and an `f`-regular set `C ∈ B⁺(X)`, the function
`V* = G_C(·, f)` (17.60) satisfies
(i) `V* < ∞` on a full absorbing set;
(ii) (17.61): `PV* + f = V* + 1_C U_C(·, f)`, that is `PV* = V* − f*`, and
`π(1_C U_C(·, f)) = π(f)`, so `f*` (17.62) has `π`-mean zero;
(iii) `(1/n) E_x[V*(Φₙ)] → 0` for every `x` with `V*(x) < ∞`. -/
theorem lemma_17_7_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ x, f x ∂π ≠ ∞) {C : Set X} (hC : IsFRegularSet P ψ f C)
    (hψC : 0 < ψ C) :
    (IsFull ψ {x | gKernelFn P C f x ≠ ∞} ∧ IsAbsorbing P {x | gKernelFn P C f x ≠ ∞}) ∧
    (∀ x, ∫⁻ y, gKernelFn P C f y ∂P x + f x =
      gKernelFn P C f x + C.indicator (tabooPotFn P C f) x) ∧
    ∫⁻ x, C.indicator (tabooPotFn P C f) x ∂π = ∫⁻ x, f x ∂π ∧
    ∀ x, gKernelFn P C f x ≠ ∞ → Tendsto (fun n : ℕ =>
      (∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x).toReal / n) atTop (𝓝 0) := by
  have hCm := hC.1
  obtain ⟨-, -, -, hfull, habs, -⟩ := theorem_14_2_5 hψ hf hf1 hC hψC
  have hstep : ∀ x, ∫⁻ y, gKernelFn P C f y ∂P x + f x =
      gKernelFn P C f x + C.indicator (tabooPotFn P C f) x := fun x => theorem_11_3_5_i P hCm hf x
  -- the generalized Kac theorem
  have hrec : IsRecurrentChain P ψ := proposition_10_1_1 ⟨hψ, π, inferInstance, hπ⟩
  have hKac : ∫⁻ x, C.indicator (tabooPotFn P C f) x ∂π = ∫⁻ x, f x ∂π := by
    rw [lintegral_indicator hCm, lintegral_eq_tabooPotFn hrec ⟨inferInstance, hπ⟩ hCm hψC
      (measure_ne_top π C) hf]
  refine ⟨⟨hfull, habs⟩, hstep, hKac, fun x hx => ?_⟩
  obtain ⟨M, hM, hfC, hU, hdrift, hpet, ⟨c, hc⟩, hpow⟩ := gKernelFn_bounds hψ hf hf1 hC hψC
  have hGm := measurable_gKernelFn (P := P) hCm hf
  have hMM : M + M ≠ ∞ := ENNReal.add_ne_top.2 ⟨hM, hM⟩
  have hc0 : gKernelFn P C f c ≠ ∞ := by
    rw [gKernelFn_of_mem hCm hf hc]; exact ne_top_of_le_ne_top hM (hfC c hc)
  obtain ⟨-, -, -, hconv, -⟩ := theorem_14_0_1_consequences hψ hap hf hf1 hpet hGm hMM hc0
    hdrift hπ
  have htend := hconv x hx
  set u := C.indicator (tabooPotFn P C f) with hu
  have hum : Measurable u := (measurable_tabooPotFn P hCm hf).indicator hCm
  have huf : ∀ y, u y ≤ (M + M) * f y := fun y => by
    by_cases hy : y ∈ C
    · rw [hu, indicator_of_mem hy]
      exact (hU y hy).trans (le_mul_of_one_le_right zero_le (hf1 y))
    · rw [hu, indicator_of_notMem hy]; exact zero_le
  have hfin : ∀ n, ∫⁻ y, f y ∂(P ^ n : Kernel X X) x ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hx, ENNReal.mul_ne_top (by
      exact_mod_cast ENNReal.natCast_ne_top (n + 1)) hMM⟩)
      (lintegral_pow_le_of_driftV3 hf hGm hCm hdrift x n)
  have hufin : ∀ n, ∫⁻ y, u y ∂(P ^ n : Kernel X X) x ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hMM (hfin n))
      ((lintegral_mono huf).trans (by rw [lintegral_const_mul _ hf]))
  have hAfin : ∀ n, ∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hx, ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top n) hMM⟩) (hpow n x)
  -- the identity in real numbers
  have hreal : ∀ n : ℕ, (∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x).toReal =
      (gKernelFn P C f x).toReal + ∑ k ∈ Finset.range n,
        ((∫⁻ y, u y ∂(P ^ k : Kernel X X) x).toReal -
          (∫⁻ y, f y ∂(P ^ k : Kernel X X) x).toReal) := fun n => by
    have h := congrArg ENNReal.toReal (lintegral_pow_add_sum (P := P) hGm hf hum hstep n x)
    rw [ENNReal.toReal_add (hAfin n) (ENNReal.sum_ne_top.2 fun k _ => hfin k),
      ENNReal.toReal_add hx (ENNReal.sum_ne_top.2 fun k _ => hufin k),
      ENNReal.toReal_sum fun k _ => hfin k, ENNReal.toReal_sum fun k _ => hufin k] at h
    rw [Finset.sum_sub_distrib]
    linarith
  -- the Cesàro limit
  have hπu : ∫⁻ y, u y ∂π ≠ ∞ := by rw [hu, hKac]; exact hπf
  have h1 := tendsto_toReal_lintegral_of_fNorm hf htend hfin hπf hum hMM huf
  have h2 := tendsto_toReal_lintegral_of_fNorm hf htend hfin hπf hf ENNReal.one_ne_top
    (fun y => by rw [one_mul])
  have hd := (h1.sub h2).cesaro
  rw [hu, hKac, sub_self] at hd
  have hG : Tendsto (fun n : ℕ => (gKernelFn P C f x).toReal / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have := hG.add hd
  rw [add_zero] at this
  refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change _ = (∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x).toReal / n
  rw [hreal n, add_div, hu]
  field_simp

/-! ### Theorem 17.7.2 -/

/-- **Theorem 17.7.2** (MT p. 460): for an aperiodic `ψ`-irreducible chain with invariant
probability `π`, `f ≥ 1` with `π(f) < ∞` and an `f`-regular set `C ∈ B⁺(X)`, if `(g, h, η)`
solves the invariance equation (17.59) `Ph = h − g + η` with `|g| ≤ c f` (`g ∈ L^f_∞`) and
`|h| ≤ c V*` (`h ∈ L^{V*}_∞`), then `π(g) = η`, so that `h` solves Poisson's equation with
forcing function `g`. -/
theorem theorem_17_7_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ x, f x ∂π ≠ ∞) {C : Set X} (hC : IsFRegularSet P ψ f C)
    (hψC : 0 < ψ C) {g h : X → ℝ} {η : ℝ} (hgm : Measurable g) (hhm : Measurable h)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hgf : ∀ x, ENNReal.ofReal |g x| ≤ c * f x)
    (hhV : ∀ x, ENNReal.ofReal |h x| ≤ c * gKernelFn P C f x)
    (hsol : IsPoissonSolution P g h η) : ∫ y, g y ∂π = η := by
  have hCm := hC.1
  obtain ⟨M, hM, hfC, hU, hdrift, hpet, ⟨x₀, hx₀C⟩, hpow⟩ := gKernelFn_bounds hψ hf hf1 hC hψC
  obtain ⟨-, -, -, hlim⟩ := lemma_17_7_3 hψ hap hπ hf hf1 hπf hC hψC
  have hGm := measurable_gKernelFn (P := P) hCm hf
  have hMM : M + M ≠ ∞ := ENNReal.add_ne_top.2 ⟨hM, hM⟩
  have hx₀ : gKernelFn P C f x₀ ≠ ∞ := by
    rw [gKernelFn_of_mem hCm hf hx₀C]; exact ne_top_of_le_ne_top hM (hfC x₀ hx₀C)
  obtain ⟨-, -, -, hconv, -⟩ := theorem_14_0_1_consequences hψ hap hf hf1 hpet hGm hMM hx₀
    hdrift hπ
  have htend := hconv x₀ hx₀
  have hfin : ∀ n, ∫⁻ y, f y ∂(P ^ n : Kernel X X) x₀ ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hx₀, ENNReal.mul_ne_top (by
      exact_mod_cast ENNReal.natCast_ne_top (n + 1)) hMM⟩)
      (lintegral_pow_le_of_driftV3 hf hGm hCm hdrift x₀ n)
  have hAfin : ∀ n, ∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x₀ ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hx₀, ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top n) hMM⟩) (hpow n x₀)
  have hhi : ∀ n, Integrable h ((P ^ n : Kernel X X) x₀) := fun n =>
    integrable_of_ofReal_abs_le hhm hhV (by
      rw [lintegral_const_mul _ hGm]; exact ENNReal.mul_ne_top hc (hAfin n))
  have hgi : ∀ n, Integrable g ((P ^ n : Kernel X X) x₀) := fun n =>
    integrable_of_ofReal_abs_le hgm hgf (by
      rw [lintegral_const_mul _ hf]; exact ENNReal.mul_ne_top hc (hfin n))
  -- iterating the invariance equation
  have hiter : ∀ n : ℕ, ∫ y, h y ∂(P ^ n : Kernel X X) x₀ =
      h x₀ + n * η - ∑ k ∈ Finset.range n, ∫ y, g y ∂(P ^ k : Kernel X X) x₀ := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero_apply, integral_dirac' _ _ hhm.stronglyMeasurable]
      simp
    | succ n ih =>
      have := isMarkovKernel_pow P n
      have hstep : ∫ y, h y ∂(P ^ (n + 1) : Kernel X X) x₀ =
          ∫ y, h y ∂(P ^ n : Kernel X X) x₀ - ∫ y, g y ∂(P ^ n : Kernel X X) x₀ + η := by
        have hi := hhi (n + 1)
        rw [pow_succ'] at hi ⊢
        change ∫ y, h y ∂(P ∘ₖ (P ^ n : Kernel X X)) x₀ = _
        rw [Kernel.integral_comp hi]
        have heq : ∀ y, ∫ z, h z ∂P y = h y - g y + η := fun y => by
          have := (hsol y).2; rw [kernelInt] at this; linarith
        simp_rw [heq]
        have hi1 : Integrable (fun y => h y - g y) ((P ^ n : Kernel X X) x₀) := (hhi n).sub (hgi n)
        rw [integral_add hi1 (integrable_const η), integral_sub (hhi n) (hgi n),
          integral_const, probReal_univ, one_smul]
      rw [hstep, ih, Finset.sum_range_succ]
      push_cast
      ring
  -- the limits
  have hgc : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ k ∈ Finset.range n,
      ∫ y, g y ∂(P ^ k : Kernel X X) x₀) atTop (𝓝 (∫ y, g y ∂π)) := by
    rcases eq_or_ne c 0 with hc0 | hc0
    · have hg0 : ∀ x, g x = 0 := fun x => by
        have h0 : ENNReal.ofReal |g x| = 0 :=
          le_antisymm (by rw [← zero_mul (f x), ← hc0]; exact hgf x) zero_le
        exact abs_nonpos_iff.1 (ENNReal.ofReal_eq_zero.1 h0)
      simp only [hg0, integral_zero, Finset.sum_const_zero, mul_zero]
      exact tendsto_const_nhds
    have hcr : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
    have hg'f : ∀ x, ENNReal.ofReal |g x / c.toReal| ≤ f x := fun x => by
      rw [abs_div, abs_of_pos hcr, ENNReal.ofReal_div_of_pos hcr, ENNReal.ofReal_toReal hc,
        ENNReal.div_le_iff hc0 hc, mul_comm]
      exact hgf x
    have h1 := (tendsto_integral_of_tendsto_fNorm htend hfin hπf (hgm.div_const _) hg'f).const_mul
      c.toReal
    have hint : ∀ μ : Measure X, c.toReal * ∫ y, g y / c.toReal ∂μ = ∫ y, g y ∂μ := fun μ => by
      rw [integral_div, mul_div_cancel₀ _ hcr.ne']
    simp_rw [hint] at h1
    exact h1.cesaro
  have hhc : Tendsto (fun n : ℕ => ((∫ y, h y ∂(P ^ n : Kernel X X) x₀) - h x₀) / n) atTop
      (𝓝 0) := by
    have hb := hlim x₀ hx₀
    have hb' : Tendsto (fun n : ℕ => c.toReal *
        ((∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x₀).toReal / n)) atTop (𝓝 0) := by
      have := hb.const_mul c.toReal; rwa [mul_zero] at this
    have hh0 : Tendsto (fun n : ℕ => h x₀ / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hmain : Tendsto (fun n : ℕ => (∫ y, h y ∂(P ^ n : Kernel X X) x₀) / n) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) hb'
      rw [Real.norm_eq_abs, abs_div, Nat.abs_cast, ← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
      have := ofReal_abs_integral_le_lintegral (μ := (P ^ n : Kernel X X) x₀) hhV
      rw [lintegral_const_mul _ hGm] at this
      have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top hc (hAfin n)) this
      rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul] at h2
    have := hmain.sub hh0
    rw [sub_zero] at this
    exact this.congr fun n => by rw [sub_div]
  -- `η = π(g)`
  have hsum := hhc.add hgc
  rw [zero_add] at hsum
  have hconst : ∀ᶠ n : ℕ in atTop, ((∫ y, h y ∂(P ^ n : Kernel X X) x₀) - h x₀) / n +
      (n⁻¹ : ℝ) * ∑ k ∈ Finset.range n, ∫ y, g y ∂(P ^ k : Kernel X X) x₀ = η := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [hiter n]
    field_simp
    ring
  exact tendsto_nhds_unique hsum (tendsto_const_nhds.congr' (hconst.mono fun n hn => hn.symm))

/-! ### Theorem 17.7.1 -/

/-- **Theorem 17.7.1** (MT p. 459), for aperiodic chains: if the chain is `ψ`-irreducible and
aperiodic and (V3) holds with `V` everywhere finite, `f ≥ 1` and `C` petite, then for the invariant
probability `π` (which exists, `isPositive_of_driftV3`) and any reference state `x₀` there is
`R < ∞` such that for every `|g| ≤ f`, `ĝ(x) = Σₙ (Pⁿg(x) − Pⁿg(x₀))` solves Poisson's equation
`ĝ − Pĝ = g − π(g)` with `|ĝ| ≤ R (V + 1)`. No moment `π(V) < ∞` is needed (compare
Theorem 17.4.2): the series converges by Theorem 14.3.4's bound
`Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f ≤ A (V(x) + V(y)) + B`, and telescopes to `g − π(g)` by the
`f`-Norm Ergodic Theorem. -/
theorem theorem_17_7_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C)
    (hV : Measurable V) (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) (x₀ : X) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ g : X → ℝ, Measurable g → (∀ x, ENNReal.ofReal |g x| ≤ f x) →
      IsPoissonSolution P g
        (fun x => ∑' n, (∫ y, g y ∂(P ^ n : Kernel X X) x - ∫ y, g y ∂(P ^ n : Kernel X X) x₀))
        (∫ y, g y ∂π) ∧
      Measurable (fun x => ∑' n, (∫ y, g y ∂(P ^ n : Kernel X X) x -
        ∫ y, g y ∂(P ^ n : Kernel X X) x₀)) ∧
      ∀ x, |∑' n, (∫ y, g y ∂(P ^ n : Kernel X X) x - ∫ y, g y ∂(P ^ n : Kernel X X) x₀)| ≤
        R * ((V x).toReal + 1) := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hpet; exact h.1
  have hπf : ∫⁻ x, f x ∂π ≠ ∞ := by
    obtain ⟨_, hfin⟩ := isPositive_of_driftV3 hψ hf hf1 hpet hV hb (hVfin x₀) hdrift
    exact hfin π inferInstance hπ
  have hpos : IsPositive P ψ := ⟨hψ, π, inferInstance, hπ⟩
  obtain ⟨A, B, hA, hB, hbd⟩ := tsum_fNorm_le_of_driftV3 hpos hap hπ hV hf hf1 hb hpet hdrift hπf
  obtain ⟨-, -, -, hconv, -⟩ := theorem_14_0_1_consequences hψ hap hf hf1 hpet hV hb (hVfin x₀)
    hdrift hπ
  set K : X → ℝ≥0∞ := fun x => A * (V x + V x₀) + B with hK
  have hKfin : ∀ x, K x ≠ ∞ := fun x => ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hA
    (ENNReal.add_ne_top.2 ⟨hVfin x, hVfin x₀⟩), hB⟩
  have hKm : Measurable K := (measurable_const.mul (hV.add measurable_const)).add measurable_const
  have hKreal : ∀ x, (K x).toReal = A.toReal * (V x).toReal + (A * V x₀ + B).toReal := fun x => by
    have e : K x = A * V x + (A * V x₀ + B) := by simp only [hK]; ring
    rw [e, ENNReal.toReal_add (ENNReal.mul_ne_top hA (hVfin x))
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hA (hVfin x₀), hB⟩), ENNReal.toReal_mul]
  set R := max A.toReal (A * V x₀ + B).toReal with hR
  have hR0 : 0 ≤ R := le_max_of_le_left ENNReal.toReal_nonneg
  have hKR : ∀ x, (K x).toReal ≤ R * ((V x).toReal + 1) := fun x => by
    rw [hKreal, mul_add, mul_one]
    exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
      (le_max_right _ _)
  refine ⟨R, hR0, fun g hgm hgf => ?_⟩
  have hPf : ∀ n x, ∫⁻ y, f y ∂(P ^ n : Kernel X X) x ≠ ∞ := fun n x =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hVfin x, ENNReal.mul_ne_top (by
      exact_mod_cast ENNReal.natCast_ne_top (n + 1)) hb⟩)
      (lintegral_pow_le_of_driftV3 hf hV hCm hdrift x n)
  have hgi : ∀ n x, Integrable g ((P ^ n : Kernel X X) x) := fun n x =>
    integrable_of_ofReal_abs_le hgm hgf (hPf n x)
  set a : ℕ → X → ℝ := fun n x => ∫ y, g y ∂(P ^ n : Kernel X X) x -
    ∫ y, g y ∂(P ^ n : Kernel X X) x₀ with ha
  have habs : ∀ n x, ENNReal.ofReal |a n x| ≤
      fNorm f ((P ^ n : Kernel X X) x) ((P ^ n : Kernel X X) x₀) :=
    fun n x => ofReal_abs_integral_sub_le_fNorm ⟨hgm, hgf, hgi n x, hgi n x₀⟩
  have hbound : ∀ x, ∑' n, ENNReal.ofReal |a n x| ≤ K x := fun x =>
    (ENNReal.tsum_le_tsum fun n => habs n x).trans (hbd x x₀)
  have hsumm : ∀ x, Summable fun n => |a n x| := fun x =>
    (ENNReal.summable_toReal (ne_top_of_le_ne_top (hKfin x) (hbound x))).congr fun n => by
      rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  have htsum : ∀ x, ∑' n, |a n x| ≤ (K x).toReal := fun x => by
    rw [show ∑' n, |a n x| = (∑' n, ENNReal.ofReal |a n x|).toReal by
      rw [ENNReal.tsum_toReal_eq (fun n => ENNReal.ofReal_ne_top)]
      simp_rw [ENNReal.toReal_ofReal (abs_nonneg _)]]
    exact ENNReal.toReal_mono (hKfin x) (hbound x)
  have hasum : ∀ x, Summable fun n => a n x := fun x =>
    Summable.of_norm ((hsumm x).congr fun n => (Real.norm_eq_abs _).symm)
  have habs' : ∀ x, |∑' n, a n x| ≤ (K x).toReal := fun x => by
    have h1 : |∑' n, a n x| ≤ ∑' n, |a n x| := by
      have := norm_tsum_le_tsum_norm ((hsumm x).congr fun n => (Real.norm_eq_abs _).symm)
      simpa [Real.norm_eq_abs] using this
    exact h1.trans (htsum x)
  have ham : ∀ n, Measurable (a n) := fun n => by
    have := isMarkovKernel_pow P n
    exact ((StronglyMeasurable.integral_kernel hgm.stronglyMeasurable).measurable).sub
      measurable_const
  have hghm : Measurable fun x => ∑' n, a n x := by
    refine measurable_of_tendsto_metrizable (f := fun N x => ∑ n ∈ Finset.range N, a n x)
      (fun N => Finset.measurable_sum _ fun n _ => ham n) ?_
    rw [tendsto_pi_nhds]
    intro x
    exact (hasum x).hasSum.tendsto_sum_nat
  refine ⟨fun x => ?_, hghm, fun x => (habs' x).trans (hKR x)⟩
  -- Poisson's equation at `x`
  have hPV : ∫⁻ y, V y ∂P x ≠ ∞ := by
    have h := hdrift x
    have hrhs : V x + C.indicator (fun _ => b) x ≠ ∞ := ENNReal.add_ne_top.2 ⟨hVfin x, by
      by_cases hx : x ∈ C
      · rw [indicator_of_mem hx]; exact hb
      · rw [indicator_of_notMem hx]; exact ENNReal.zero_ne_top⟩
    exact ne_top_of_le_ne_top hrhs (le_trans le_self_add h)
  have hPK : ∫⁻ y, K y ∂P x ≠ ∞ := by
    simp only [hK]
    have hVm' : Measurable fun y => V y + V x₀ := hV.add measurable_const
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hVm',
      lintegral_add_right _ measurable_const, lintegral_const, lintegral_const, measure_univ,
      mul_one, mul_one]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hA (ENNReal.add_ne_top.2 ⟨hPV, hVfin x₀⟩), hB⟩
  have hdom : Integrable (fun y => (K y).toReal) (P x) :=
    integrable_toReal_of_lintegral_ne_top hKm.aemeasurable hPK
  have hint : Integrable (fun y => ∑' n, a n y) (P x) :=
    hdom.mono' hghm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact habs' y)
  refine ⟨hint, ?_⟩
  -- each term is dominated by `K`
  have haK : ∀ n y, |a n y| ≤ (K y).toReal := fun n y => by
    have h1 : ENNReal.ofReal |a n y| ≤ K y := (ENNReal.le_tsum n).trans (hbound y)
    have h2 := ENNReal.toReal_mono (hKfin y) h1
    rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h2
  have hai : ∀ n, Integrable (a n) (P x) := fun n =>
    hdom.mono' (ham n).aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact haK n y)
  -- `∫ a n dP(x) = Pⁿ⁺¹g(x) − Pⁿg(x₀)`
  have hstep : ∀ n, ∫ y, a n y ∂P x = ∫ y, g y ∂(P ^ (n + 1) : Kernel X X) x -
      ∫ y, g y ∂(P ^ n : Kernel X X) x₀ := by
    intro n
    have := isMarkovKernel_pow P n
    have hi1 : Integrable (fun y => ∫ z, g z ∂(P ^ n : Kernel X X) y) (P x) :=
      ((hai n).add (integrable_const (∫ y, g y ∂(P ^ n : Kernel X X) x₀))).congr
        (Eventually.of_forall fun y => by simp [ha])
    rw [ha]
    simp only
    rw [integral_sub hi1 (integrable_const _), integral_const, probReal_univ, one_smul]
    congr 1
    rw [pow_succ]
    change _ = ∫ z, g z ∂((P ^ n : Kernel X X) ∘ₖ P) x
    rw [Kernel.integral_comp]
    have := hgi (n + 1) x
    rw [pow_succ] at this
    exact this
  -- the series of integrals
  have hsm : Measurable fun y => ∑' n, |a n y| := by
    refine measurable_of_tendsto_metrizable (f := fun N y => ∑ n ∈ Finset.range N, |a n y|)
      (fun N => Finset.measurable_sum _ fun n _ => measurable_abs_of_measurable (ham n)) ?_
    rw [tendsto_pi_nhds]
    intro y
    exact (hsumm y).hasSum.tendsto_sum_nat
  have hbI : Integrable (fun y => ∑' n, |a n y|) (P x) :=
    hdom.mono' hsm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun n => abs_nonneg _)]
      exact htsum y)
  have hhas : HasSum (fun n => ∫ y, a n y ∂P x) (∫ y, ∑' n, a n y ∂P x) :=
    hasSum_integral_of_dominated_convergence (fun n y => |a n y|)
      (fun n => (ham n).aestronglyMeasurable)
      (fun n => Eventually.of_forall fun y => le_of_eq (Real.norm_eq_abs _))
      (Eventually.of_forall hsumm) hbI (Eventually.of_forall fun y => (hasum y).hasSum)
  have hdiff := (hasum x).hasSum.sub hhas
  set bs : ℕ → ℝ := fun n => ∫ y, g y ∂(P ^ n : Kernel X X) x with hbs
  have hterm : ∀ n, a n x - ∫ y, a n y ∂P x = bs n - bs (n + 1) := fun n => by
    rw [hstep n, ha, hbs]; ring
  simp_rw [hterm] at hdiff
  have hpart := hdiff.tendsto_sum_nat
  simp_rw [Finset.sum_range_sub'] at hpart
  have hlim : Tendsto (fun N => bs 0 - bs N) atTop (𝓝 (bs 0 - ∫ y, g y ∂π)) :=
    tendsto_const_nhds.sub (tendsto_integral_of_tendsto_fNorm (hconv x (hVfin x))
      (fun n => hPf n x) hπf hgm hgf)
  have heq := tendsto_nhds_unique hpart hlim
  have hb0 : bs 0 = g x := by
    rw [hbs]; simp only
    rw [pow_zero_apply, integral_dirac' _ _ hgm.stronglyMeasurable]
  rw [hb0] at heq
  exact heq
end MeynTweedie.LimitTheorems

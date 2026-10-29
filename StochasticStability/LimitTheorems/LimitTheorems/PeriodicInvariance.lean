/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.PoissonInvariance
import LimitTheorems.FPeriodicErgodic

/-!
# Invariance equations for periodic chains (MT §17.7)

Meyn and Tweedie, Theorem 17.7.2 and Lemma 17.7.3, pp. 460–461, without aperiodicity.
`PoissonInvariance` proves them for aperiodic chains through the `f`-Norm Ergodic Theorem; the
book handles the periodic case "by Theorem 14.3.6" (and the `d`-skeleton for Lemma 17.7.3).
Here Theorem 14.3.6 (i) (`theorem_14_3_6_i`, the `f`-norm convergence of `P^{nd+r}(x, ·)` to
`π_{i+r}` on each cycle class) is turned into Cesàro convergence of `Pᵏ(x, ·)`, which is all
that the two proofs need. `V* = G_C(·, f)` (17.60) is `gKernelFn P C f`.

* `sum_range_mod_eq`, `tendsto_cesaro_of_phase`: if `c(dn + r) → L(r)` for every `r < d`, then
  `(1/n) Σ_{k<n} c(k) → d⁻¹ Σ_{r<d} L(r)`.
* `exists_full_tendsto_cesaro`: for a positive recurrent chain, `f ≥ 1`, `π(f) < ∞`, there is a
  measurable full set on which `(1/n) Σ_{k<n} Pᵏg(x) → π(g)` for every `|g| ≤ c f` (where
  `Pᵏf(x) < ∞`), using `π = d⁻¹ Σ_{r<d} π_{i+r}`.
* `exists_absorbing_cesaro`: such a set inside `{V* < ∞}` that is also absorbing and non-empty.
* `tendsto_pow_gKernelFn_div_of_cesaro`: Lemma 17.7.3 (iii) at a state with Cesàro convergence.

**Results.**
* **Lemma 17.7.3** (`lemma_17_7_3_periodic`, p. 460): (i), (ii) as in `lemma_17_7_3`, and (iii)
  `(1/n) E_x[V*(Φₙ)] → 0` on a non-empty full absorbing set `X_f ⊆ {V* < ∞}`.
* **Theorem 17.7.2** (`theorem_17_7_2_periodic`, p. 460): if `Ph = h − g + η` with `|g| ≤ c f`
  and `|h| ≤ c V*`, then `π(g) = η`.

**Deviations from the book.** In Lemma 17.7.3 (iii) the aperiodic version holds at every `x` with
`V*(x) < ∞`; for periodic chains it is proved on the full absorbing set `X_f` of the book's
statement (Theorem 14.3.6 (i) gives convergence off a `ψ`-null set). As in `lemma_17_7_3`, `C` is
taken `f`-regular and the second limit of (iii) is not formalised.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- The partial sums of a `d`-periodic sequence: `Σ_{k<n} L(k mod d) = ⌊n/d⌋ Σ_{r<d} L(r) +
Σ_{j < n mod d} L(j)`. -/
theorem sum_range_mod_eq {d : ℕ} (L : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, L (k % d) =
      (n / d : ℕ) * ∑ r ∈ Finset.range d, L r + ∑ j ∈ Finset.range (n % d), L j := by
  have hblock : ∀ q, ∑ k ∈ Finset.range (d * q), L (k % d) = q * ∑ r ∈ Finset.range d, L r := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show d * (q + 1) = d * q + d by ring, Finset.sum_range_add, ih]
      have : ∀ r ∈ Finset.range d, L ((d * q + r) % d) = L r := fun r hr => by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.1 hr)]
      rw [Finset.sum_congr rfl this]
      push_cast; ring
  conv_lhs => rw [← Nat.div_add_mod n d]
  rw [Finset.sum_range_add, hblock]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Nat.mul_add_mod]
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [h0, Nat.mod_zero]
  · rw [Nat.mod_eq_of_lt ((Finset.mem_range.1 hj).trans (Nat.mod_lt n hpos))]

/-- **Cesàro limits from phase limits**: if `c(dn + r) → L(r)` for every phase `r < d`, then
`(1/n) Σ_{k<n} c(k) → d⁻¹ Σ_{r<d} L(r)`. -/
theorem tendsto_cesaro_of_phase {d : ℕ} (hd : 0 < d) {c L : ℕ → ℝ}
    (h : ∀ r < d, Tendsto (fun n => c (d * n + r)) atTop (𝓝 (L r))) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, c k) atTop
      (𝓝 ((d : ℝ)⁻¹ * ∑ r ∈ Finset.range d, L r)) := by
  -- `c(k) − L(k mod d) → 0`
  have h1 : Tendsto (fun k => c k - L (k % d)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hall : ∀ r ∈ Finset.range d, ∀ᶠ n in atTop, dist (c (d * n + r) - L r) 0 < ε :=
      fun r hr => by
        have := tendsto_sub_nhds_zero_iff.2 (h r (Finset.mem_range.1 hr))
        exact (Metric.tendsto_nhds.1 this) ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((Finset.eventually_all _).2 hall)
    refine ⟨d * N, fun k hk => ?_⟩
    have hk' : N ≤ k / d := (Nat.le_div_iff_mul_le hd).2 (by rw [mul_comm]; exact hk)
    have := hN (k / d) hk' (k % d) (Finset.mem_range.2 (Nat.mod_lt k hd))
    rwa [Nat.div_add_mod] at this
  have h2 := h1.cesaro
  -- the periodic part
  set S := ∑ r ∈ Finset.range d, L r with hS
  set B := |S| + ∑ r ∈ Finset.range d, |L r| with hB
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h3 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, L (k % d) - (d : ℝ)⁻¹ * S)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => B / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩) hlim
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [sum_range_mod_eq L n]
    set R := ∑ j ∈ Finset.range (n % d), L j with hR
    have hcast : ((n / d : ℕ) : ℝ) = ((n : ℝ) - (n % d : ℕ)) / d := by
      have := Nat.div_add_mod n d
      rw [eq_div_iff hdpos.ne']
      have h' : ((d * (n / d) + n % d : ℕ) : ℝ) = n := by exact_mod_cast this
      push_cast at h'
      linarith
    have hexpr : (n : ℝ)⁻¹ * (((n / d : ℕ) : ℝ) * S + R) - (d : ℝ)⁻¹ * S =
        (n : ℝ)⁻¹ * (R - ((n % d : ℕ) : ℝ) / d * S) := by
      rw [hcast]; field_simp; ring
    rw [hexpr, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hn0, inv_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ hn0.le
    have hmod : ((n % d : ℕ) : ℝ) / d ≤ 1 := by
      rw [div_le_one hdpos]; exact_mod_cast (Nat.mod_lt n hd).le
    have hmod0 : 0 ≤ ((n % d : ℕ) : ℝ) / d := by positivity
    have hR : |R| ≤ ∑ r ∈ Finset.range d, |L r| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (Nat.mod_lt n hd).le) fun _ _ _ => abs_nonneg _)
    calc |R - ((n % d : ℕ) : ℝ) / d * S| ≤ |R| + |((n % d : ℕ) : ℝ) / d * S| := abs_sub _ _
      _ ≤ ∑ r ∈ Finset.range d, |L r| + |S| := by
          refine add_le_add hR ?_
          rw [abs_mul, abs_of_nonneg hmod0]
          exact mul_le_of_le_one_left (abs_nonneg _) hmod
      _ = B := by rw [hB]; ring
  have h4 := (h2.add h3).add (tendsto_const_nhds (x := (d : ℝ)⁻¹ * S))
  rw [zero_add, zero_add] at h4
  refine h4.congr fun n => ?_
  rw [Finset.sum_sub_distrib]
  ring


variable [MeasurableSpace.CountablyGenerated X]

/-- **Cesàro convergence for periodic chains** (from Theorem 14.3.6 (i)): for a positive
recurrent chain with invariant probability `π`, `f ≥ 1` and `π(f) < ∞`, there is a measurable
full set `S` such that for `x ∈ S` with `Pᵏf(x) < ∞` for all `k`, and every measurable `g` with
`|g| ≤ c f`, `c < ∞`, `(1/n) Σ_{k<n} Pᵏg(x) → π(g)`. -/
theorem exists_full_tendsto_cesaro {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ x, f x ∂π ≠ ∞) :
    ∃ S : Set X, MeasurableSet S ∧ IsFull ψ S ∧ ∀ x ∈ S,
      (∀ k, ∫⁻ y, f y ∂(P ^ k : Kernel X X) x ≠ ∞) → ∀ g : X → ℝ, Measurable g →
        ∀ c : ℝ≥0∞, c ≠ ∞ → (∀ y, ENNReal.ofReal |g y| ≤ c * f y) →
          Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            ∫ y, g y ∂(P ^ k : Kernel X X) x) atTop (𝓝 (∫ y, g y ∂π)) := by
  have hrec := proposition_10_1_1 hpos
  obtain ⟨d, hper, D, hD, hprob, S, hS, hconv⟩ := theorem_14_3_6_i hpos hπ hf hf1 hπf
  have hd := hper.1
  set S0 := S ∩ ⋃ i, D i with hS0
  have hS0full : ψ S0ᶜ = 0 := by
    rw [hS0, compl_inter]
    exact measure_union_null hS hD.null_compl
  refine ⟨(toMeasurable ψ S0ᶜ)ᶜ, (measurableSet_toMeasurable ψ _).compl, ?_,
    fun x hx hfin g hgm c hc hgf => ?_⟩
  · change ψ (toMeasurable ψ S0ᶜ)ᶜᶜ = 0
    rw [compl_compl, measure_toMeasurable]; exact hS0full
  have hxS0 : x ∈ S0 := by
    by_contra h
    exact hx (subset_toMeasurable ψ _ h)
  obtain ⟨i, hxi⟩ := mem_iUnion.1 hxS0.2
  -- reduce to `|g| ≤ f`
  rcases eq_or_ne c 0 with hc0 | hc0
  · have hg0 : ∀ y, g y = 0 := fun y => by
      have h0 : ENNReal.ofReal |g y| = 0 :=
        le_antisymm (by rw [← zero_mul (f y), ← hc0]; exact hgf y) zero_le
      exact abs_nonpos_iff.1 (ENNReal.ofReal_eq_zero.1 h0)
    simp only [hg0, integral_zero, Finset.sum_const_zero, mul_zero]
    exact tendsto_const_nhds
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
  set g' : X → ℝ := fun y => g y / c.toReal with hg'
  have hg'm : Measurable g' := hgm.div_const _
  have hg'f : ∀ y, ENNReal.ofReal |g' y| ≤ f y := fun y => by
    rw [hg', abs_div, abs_of_pos hcr, ENNReal.ofReal_div_of_pos hcr, ENNReal.ofReal_toReal hc,
      ENNReal.div_le_iff hc0 hc, mul_comm]
    exact hgf y
  have hint : ∀ μ : Measure X, ∫ y, g y ∂μ = c.toReal * ∫ y, g' y ∂μ := fun μ => by
    rw [hg', integral_div, mul_div_cancel₀ _ hcr.ne']
  simp_rw [hint]
  suffices hmain : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
      ∫ y, g' y ∂(P ^ k : Kernel X X) x) atTop (𝓝 (∫ y, g' y ∂π)) by
    refine (hmain.const_mul c.toReal).congr fun n => ?_
    rw [← Finset.mul_sum]; ring
  -- the phase limits
  have hσf : ∀ j, ∫⁻ y, f y ∂cycleInv π D j ≠ ∞ := fun j => by
    rw [cycleInv, lintegral_smul_measure]
    exact ENNReal.mul_ne_top (by simp) (ne_top_of_le_ne_top hπf (setLIntegral_le_lintegral _ _))
  have hphase : ∀ r < d, Tendsto (fun n => ∫ y, g' y ∂(P ^ (d * n + r) : Kernel X X) x) atTop
      (𝓝 (∫ y, g' y ∂cycleInv π D (i + r))) := fun r hr =>
    tendsto_integral_of_tendsto_fNorm (hconv i r hr x ⟨hxi, hxS0.1⟩) (fun n => hfin _)
      (hσf _) hg'm hg'f
  have hlim := tendsto_cesaro_of_phase hd (c := fun k => ∫ y, g' y ∂(P ^ k : Kernel X X) x)
    (L := fun r => ∫ y, g' y ∂cycleInv π D (i + r)) hphase
  have hπeq : ∫ y, g' y ∂π =
      (d : ℝ)⁻¹ * ∑ r ∈ Finset.range d, ∫ y, g' y ∂cycleInv π D (i + r) := by
    conv_lhs => rw [hD.eq_smul_sum_cycleInv hd hrec hπ i]
    rw [integral_smul_measure, integral_finsetSum_measure fun r _ =>
      integrable_of_ofReal_abs_le hg'm hg'f (hσf _), smul_eq_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
  rw [hπeq]
  exact hlim


/-- **Lemma 17.7.3 (iii)** at a state with Cesàro convergence (MT p. 461): for an `f`-regular
`C ∈ B⁺(X)`, if `V*(x) < ∞` and `(1/n) Σ_{k<n} Pᵏg(x) → π(g)` for all `|g| ≤ c f`, then
`(1/n) E_x[V*(Φₙ)] → 0`. -/
theorem tendsto_pow_gKernelFn_div_of_cesaro {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hπf : ∫⁻ x, f x ∂π ≠ ∞) {C : Set X} (hC : IsFRegularSet P ψ f C) (hψC : 0 < ψ C) {x : X}
    (hx : gKernelFn P C f x ≠ ∞)
    (hces : ∀ g : X → ℝ, Measurable g → ∀ c : ℝ≥0∞, c ≠ ∞ →
      (∀ y, ENNReal.ofReal |g y| ≤ c * f y) →
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          ∫ y, g y ∂(P ^ k : Kernel X X) x) atTop (𝓝 (∫ y, g y ∂π))) :
    Tendsto (fun n : ℕ =>
      (∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x).toReal / n) atTop (𝓝 0) := by
  have hCm := hC.1
  have hstep : ∀ x, ∫⁻ y, gKernelFn P C f y ∂P x + f x =
      gKernelFn P C f x + C.indicator (tabooPotFn P C f) x := fun x => theorem_11_3_5_i P hCm hf x
  have hrec : IsRecurrentChain P ψ := proposition_10_1_1 ⟨hψ, π, inferInstance, hπ⟩
  have hKac : ∫⁻ x, C.indicator (tabooPotFn P C f) x ∂π = ∫⁻ x, f x ∂π := by
    rw [lintegral_indicator hCm, lintegral_eq_tabooPotFn hrec ⟨inferInstance, hπ⟩ hCm hψC
      (measure_ne_top π C) hf]
  obtain ⟨M, hM, hfC, hU, hdrift, -, -, hpow⟩ := gKernelFn_bounds hψ hf hf1 hC hψC
  have hGm := measurable_gKernelFn (P := P) hCm hf
  have hMM : M + M ≠ ∞ := ENNReal.add_ne_top.2 ⟨hM, hM⟩
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
  -- the Cesàro limits
  have hπu : ∫⁻ y, u y ∂π ≠ ∞ := by rw [hu, hKac]; exact hπf
  have hconv : ∀ (φ : X → ℝ≥0∞), Measurable φ → ∀ K : ℝ≥0∞, K ≠ ∞ → (∀ y, φ y ≤ K * f y) →
      ∫⁻ y, φ y ∂π ≠ ∞ → (∀ k, ∫⁻ y, φ y ∂(P ^ k : Kernel X X) x ≠ ∞) →
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        (∫⁻ y, φ y ∂(P ^ k : Kernel X X) x).toReal) atTop (𝓝 (∫⁻ y, φ y ∂π).toReal) := by
    intro φ hφm K hK hφf hφπ hφk
    have hg : ∀ y, ENNReal.ofReal |(φ y).toReal| ≤ K * f y := fun y => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact ENNReal.ofReal_toReal_le.trans (hφf y)
    have h := hces (fun y => (φ y).toReal) hφm.ennreal_toReal K hK hg
    rw [integral_toReal hφm.aemeasurable (ae_lt_top hφm hφπ)] at h
    refine h.congr fun n => ?_
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    exact integral_toReal hφm.aemeasurable (ae_lt_top hφm (hφk k))
  have h1 := hconv u hum (M + M) hMM huf hπu hufin
  have h2 := hconv f hf 1 ENNReal.one_ne_top (fun y => by rw [one_mul]) hπf hfin
  have hd := h1.sub h2
  rw [hu, hKac, sub_self] at hd
  have hG : Tendsto (fun n : ℕ => (gKernelFn P C f x).toReal / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have := hG.add hd
  rw [add_zero] at this
  refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change _ = (∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x).toReal / n
  rw [hreal n, add_div, hu, Finset.sum_sub_distrib]
  field_simp

/-- For an `f`-regular `C ∈ B⁺(X)` there is a non-empty, measurable, absorbing, full set `B` on
which `V* = G_C(·, f)` is finite and the Cesàro averages `(1/n) Σ_{k<n} Pᵏg(x)` converge to
`π(g)` for every `|g| ≤ c f`. -/
theorem exists_absorbing_cesaro {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hπf : ∫⁻ x, f x ∂π ≠ ∞) {C : Set X} (hC : IsFRegularSet P ψ f C) (hψC : 0 < ψ C) :
    ∃ B ⊆ {x | gKernelFn P C f x ≠ ∞}, B.Nonempty ∧ MeasurableSet B ∧ IsAbsorbing P B ∧
      IsFull ψ B ∧ ∀ x ∈ B, ∀ g : X → ℝ, Measurable g → ∀ c : ℝ≥0∞, c ≠ ∞ →
        (∀ y, ENNReal.ofReal |g y| ≤ c * f y) →
          Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            ∫ y, g y ∂(P ^ k : Kernel X X) x) atTop (𝓝 (∫ y, g y ∂π)) := by
  have hCm := hC.1
  obtain ⟨S, hSm, hSfull, hS⟩ := exists_full_tendsto_cesaro ⟨hψ, π, inferInstance, hπ⟩ hπ hf hf1
    hπf
  obtain ⟨-, -, -, hfull, -, -⟩ := theorem_14_2_5 hψ hf hf1 hC hψC
  obtain ⟨M, hM, -, -, hdrift, -, -, -⟩ := gKernelFn_bounds hψ hf hf1 hC hψC
  have hMM : M + M ≠ ∞ := ENNReal.add_ne_top.2 ⟨hM, hM⟩
  have hGm := measurable_gKernelFn (P := P) hCm hf
  have hTm : MeasurableSet {x | gKernelFn P C f x ≠ ∞} :=
    (measurableSet_singleton ∞).compl.preimage hGm
  have hA : MeasurableSet (S ∩ {x | gKernelFn P C f x ≠ ∞}) := hSm.inter hTm
  have hAfull : IsFull ψ (S ∩ {x | gKernelFn P C f x ≠ ∞}) := by
    change ψ (S ∩ _)ᶜ = 0
    rw [compl_inter]
    exact measure_union_null hSfull hfull
  obtain ⟨B, hBA, hBne, hBm, hBabs, hBfull⟩ := proposition_4_2_3_ii hψ hA hAfull
  refine ⟨B, fun x hx => (hBA hx).2, hBne, hBm, hBabs, hBfull, fun x hx => ?_⟩
  have hx' := hBA hx
  refine hS x hx'.1 fun n => ?_
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hx'.2, ENNReal.mul_ne_top (by
      exact_mod_cast ENNReal.natCast_ne_top (n + 1)) hMM⟩)
      (lintegral_pow_le_of_driftV3 hf hGm hCm hdrift x n)


/-- **Lemma 17.7.3** (MT p. 460), general case: for a `ψ`-irreducible chain (periodic or not)
with invariant probability `π`, `f ≥ 1` with `π(f) < ∞` and an `f`-regular set `C ∈ B⁺(X)`,
`V* = G_C(·, f)` (17.60) satisfies
(i) `V* < ∞` on a full absorbing set;
(ii) (17.61): `PV* + f = V* + 1_C U_C(·, f)`, and `π(1_C U_C(·, f)) = π(f)` (`f*` has mean zero);
(iii) there is a non-empty full absorbing set `X_f` on which `V* < ∞` and
`(1/n) E_x[V*(Φₙ)] → 0`. The book's proof of (iii) for periodic chains goes through the
`d`-skeleton and Theorem 14.3.6; here Theorem 14.3.6 (i) gives Cesàro convergence of `Pᵏ(x, ·)`
(`exists_full_tendsto_cesaro`). -/
theorem lemma_17_7_3_periodic {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hπf : ∫⁻ x, f x ∂π ≠ ∞) {C : Set X} (hC : IsFRegularSet P ψ f C) (hψC : 0 < ψ C) :
    (IsFull ψ {x | gKernelFn P C f x ≠ ∞} ∧ IsAbsorbing P {x | gKernelFn P C f x ≠ ∞}) ∧
    (∀ x, ∫⁻ y, gKernelFn P C f y ∂P x + f x =
      gKernelFn P C f x + C.indicator (tabooPotFn P C f) x) ∧
    ∫⁻ x, C.indicator (tabooPotFn P C f) x ∂π = ∫⁻ x, f x ∂π ∧
    ∃ Xf ⊆ {x | gKernelFn P C f x ≠ ∞}, Xf.Nonempty ∧ MeasurableSet Xf ∧ IsAbsorbing P Xf ∧
      IsFull ψ Xf ∧ ∀ x ∈ Xf, Tendsto (fun n : ℕ =>
        (∫⁻ y, gKernelFn P C f y ∂(P ^ n : Kernel X X) x).toReal / n) atTop (𝓝 0) := by
  have hCm := hC.1
  obtain ⟨-, -, -, hfull, habs, -⟩ := theorem_14_2_5 hψ hf hf1 hC hψC
  have hrec : IsRecurrentChain P ψ := proposition_10_1_1 ⟨hψ, π, inferInstance, hπ⟩
  have hKac : ∫⁻ x, C.indicator (tabooPotFn P C f) x ∂π = ∫⁻ x, f x ∂π := by
    rw [lintegral_indicator hCm, lintegral_eq_tabooPotFn hrec ⟨inferInstance, hπ⟩ hCm hψC
      (measure_ne_top π C) hf]
  obtain ⟨B, hBV, hBne, hBm, hBabs, hBfull, hBces⟩ :=
    exists_absorbing_cesaro hψ hπ hf hf1 hπf hC hψC
  exact ⟨⟨hfull, habs⟩, fun x => theorem_11_3_5_i P hCm hf x, hKac, B, hBV, hBne, hBm, hBabs,
    hBfull, fun x hx => tendsto_pow_gKernelFn_div_of_cesaro hψ hπ hf hf1 hπf hC hψC (hBV hx)
      (hBces x hx)⟩

/-- **Theorem 17.7.2** (MT p. 460), general case: for a `ψ`-irreducible chain (periodic or not)
with invariant probability `π`, `f ≥ 1` with `π(f) < ∞` and an `f`-regular set `C ∈ B⁺(X)`, if
`(g, h, η)` solves the invariance equation (17.59) `Ph = h − g + η` with `|g| ≤ c f` and
`|h| ≤ c V*`, then `π(g) = η`. The book's proof: "by Theorem 14.3.6 in general"; here the
Cesàro averages of Theorem 14.3.6 (i) are used at one state of the set `X_f` of
Lemma 17.7.3. -/
theorem theorem_17_7_2_periodic {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hπf : ∫⁻ x, f x ∂π ≠ ∞) {C : Set X} (hC : IsFRegularSet P ψ f C) (hψC : 0 < ψ C)
    {g h : X → ℝ} {η : ℝ} (hgm : Measurable g) (hhm : Measurable h) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hgf : ∀ x, ENNReal.ofReal |g x| ≤ c * f x)
    (hhV : ∀ x, ENNReal.ofReal |h x| ≤ c * gKernelFn P C f x)
    (hsol : IsPoissonSolution P g h η) : ∫ y, g y ∂π = η := by
  have hCm := hC.1
  obtain ⟨M, hM, -, -, hdrift, -, -, hpow⟩ := gKernelFn_bounds hψ hf hf1 hC hψC
  obtain ⟨B, hBV, ⟨x₀, hx₀B⟩, -, -, -, hBces⟩ := exists_absorbing_cesaro hψ hπ hf hf1 hπf hC hψC
  have hx₀ : gKernelFn P C f x₀ ≠ ∞ := hBV hx₀B
  have hGm := measurable_gKernelFn (P := P) hCm hf
  have hMM : M + M ≠ ∞ := ENNReal.add_ne_top.2 ⟨hM, hM⟩
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
        have hi1 : Integrable (fun y => h y - g y) ((P ^ n : Kernel X X) x₀) :=
          (hhi n).sub (hgi n)
        rw [integral_add hi1 (integrable_const η), integral_sub (hhi n) (hgi n),
          integral_const, probReal_univ, one_smul]
      rw [hstep, ih, Finset.sum_range_succ]
      push_cast
      ring
  -- the limits
  have hgc := hBces x₀ hx₀B g hgm c hc hgf
  have hhc : Tendsto (fun n : ℕ => ((∫ y, h y ∂(P ^ n : Kernel X X) x₀) - h x₀) / n) atTop
      (𝓝 0) := by
    have hb := tendsto_pow_gKernelFn_div_of_cesaro hψ hπ hf hf1 hπf hC hψC hx₀ (hBces x₀ hx₀B)
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

end MeynTweedie.LimitTheorems

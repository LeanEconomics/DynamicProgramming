/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.GeometricConverse
import LimitTheorems.QueueInvariantMinimal
import LimitTheorems.ModelCountableModels
import LimitTheorems.FErgodicModels
import LimitTheorems.LinkedRenewal

/-!
# Geometrically ergodic models (MT §15.1.4 and §15.5)

Meyn and Tweedie, §15.1.4 (pp. 370–372) and §15.5 (pp. 388–390).

**Forward recurrence time chains** (p. 370), with the renewal state `0` (the book's `1`).
* `fwdRec_kendallMoment`: `E_0[r^{τ_0}] = Σₙ rⁿ p(n)`; `fwdRec_isKendall_iff`: `{0}` is Kendall of
  rate `κ` iff `Σₙ κⁿ p(n) < ∞`.
* `fwdRec_tails_of_isGeomErgodicAtom` (through Theorem 15.1.5) and `fwdRec_geomErgodic_of_tails`
  (through Theorem 15.1.4, for an aperiodic chain): the chain is geometrically ergodic iff `p` has
  geometric tails.

**A non-geometrically ergodic chain** (15.20) (`nonGeomKernel`, pp. 370–371).
* `nonGeom_tabooKernel_pos`, `nonGeom_tabooKernel_univ_pos`: `P_j(τ_0 = n + 1) = β_jⁿ (1 − β_j)`
  and `P_j(τ_0 > n) = β_jⁿ` for `j ≥ 1`; `nonGeom_meanReturnTime_pos`: `E_j[τ_0] = (1 − β_j)⁻¹`.
* `nonGeom_meanReturnTime_zero`: the mean return time to `0`; `nonGeom_isPositive_iff`: the chain
  is positive iff (15.21) holds; `nonGeom_isIrreducibleChain`.
* `nonGeom_tabooKernel_zero_ge`, `nonGeom_kendallMoment_eq_top`, `nonGeom_not_geomErgodic`: if
  `β_j → 1`, then `E_0[r^{τ_0}] = ∞` for every `r > 1`, so `{0}` is Kendall of no rate and is not a
  geometrically ergodic atom for any invariant probability, whatever `γ`.

**Different rates of convergence** (pp. 371–372).
* `rateMatrix`, `rateKernel`, `ratePi`, `isInvariant_ratePi`: the `3 × 3` example and
  `π = (1/4, 1/2, 1/4)`; `rateMatrix_pow_row_zero`, `rateMatrix_pow_col_two`,
  `rateMatrix_pow_row_one`: closed forms for the powers.
* `rateKernel_pow_zero_two`: `Pⁿ(0, 0) = π(0)` and `Pⁿ(2, 2) = π(2)` for `n ≥ 1`.
* `rateKernel_state_one`: `Pⁿ(1, 1) − π(1) = 4⁻ⁿ` for `n ≥ 1`.
* `isInvariant_uniform_of_symm`: a symmetric transition matrix on a finite space has the uniform
  invariant law (p. 372, Teugels' example).

**The Bernoulli random walk on `ℤ₊`** (§15.5.1, p. 388; `bernoulliWalk`).
* `lintegral_bernoulliWalk`, `bernoulliWalk_driftV4`: for `V(x) = zˣ`,
  `PV(x) = (pz + (1 − p)/z) V(x)` for `x > 0`, so (V4) holds with `C = {0}`;
  `bernoulli_rate_lt_one`: `pz + (1 − p)/z < 1` for some `z > 1` when `p < 1/2`.
* `bernoulliWalk_geometricErgodic`: for `0 < p < 1/2` the walk is irreducible, aperiodic and
  `V`-geometrically ergodic (Theorem 15.0.1).

**Linear and bilinear models** (§15.5.2, pp. 389–390).
* `ar1_eq_15_49` ((15.49)), `ar1Kernel_eq_bilinearKernel`, `ar1_geometricErgodic`: the simple
  linear model with `E|W| < ∞` and `|α| < 1` is `V`-geometrically ergodic, `V(x) = |x| + 1`.
* `bilinear_eq_15_51` ((15.51)); `pow_affine_le`, `bilinear_le_mul_add`,
  `isUnboundedOffPetite_enorm_pow`, `bilinear_geometricErgodic`: if `E|W|ᵏ < ∞` and
  `E|θ + bW|ᵏ < 1` then `V(x) = |x|ᵏ + 1` satisfies (V4) and the chain is `V`-geometrically
  ergodic; `k = 1` is (15.52).
* `bilinear_variance_convergence`: for centred `W` with `θ² + b²σ² < 1`,
  `Σₙ rⁿ |∫ Pⁿ(x, dy) y² − ∫ π(dy) y²| ≤ R (x² + 1)` (p. 390).

**Corrections.**
* (15.20) defines `P(j, j) = β_j` and `P(j, 0) = 1 − β_j` "for `j ∈ ℤ₊`", which clashes with
  `P(0, ·) = γ` at `j = 0`; the last two rows are for `j ≥ 1`. Accordingly the mean return time is
  `E_0[τ_0] = 1 + Σ_{j ≥ 1} γ_j (1 − β_j)⁻¹` (`nonGeom_meanReturnTime_zero`): a jump from `0` to
  `0` returns at time `1`, not after `1 + (1 − β_0)⁻¹` steps. The bound
  `E_0[r^{τ_0}] ≥ r Σ_j γ_j E_j[r^{τ_0}]` likewise needs `j ≥ 1`; the proof here uses
  `nonGeom_tabooKernel_zero_ge` directly.
* For the `3 × 3` matrix the book says the rate for state `1` is at least `ρ₁ > 1/4`. In fact
  `|Pⁿ(1, 1) − π(1)| = 4⁻ⁿ` for `n ≥ 1`, so the best rate is exactly `1/4`
  (`rateKernel_state_one`: `(1/4)ⁿ` works with constant `1`, and no `ρ < 1/4` works). The rates
  still differ from those of states `0` and `2`, which are `0`. The printed
  `U^{(z)}(1, 1) = 1 + z/2(1 − z) + z/4(1 − z)`, read like `U^{(z)}(0, 0)`, has `z²` coefficient
  `3/4`, but `P²(1, 1) = 9/16` (`rateKernel_U11_counterexample`); the generating function is
  `1 + z/(2(1 − z)) + z/(4 − z)`.
* §15.5.2 uses `V(x) = x²` for the bilinear model; (V4) needs `V ≥ 1`, so `V(x) = x² + 1` is used.

**Hypotheses.** For the linear and bilinear models, `ψ`-irreducibility, aperiodicity and the
petiteness of compact sets are assumed, as in `proposition_14_4_2`: the book derives them from a
positive density of `W` through the T-chain property, which is not formalised for these models.
The Bernoulli walk needs `p > 0` for irreducibility. `fwdRec_geomErgodic_of_tails` assumes
aperiodicity, as Theorem 15.1.4 (corrected) requires.

**Not formalised.** The first-passage generating functions (15.48) of the Bernoulli walk and
their analyticity for `z < 2/√(p(1 − p))`: the drift route, which the book calls "rather
easier", gives the same conclusion. Teugels' `(N + 1)`-state example beyond the uniform invariant
law: the eigenvalues and the expansion of `Pᵐ(k, k)` are quoted from [384] with "considerable
algebra" omitted.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal Topology

/-! ### The forward recurrence time chain (§15.1.4) -/

/-- **The forward recurrence time chain** (MT §15.1.4, p. 370), with the renewal state `0` (the
book's state `1`): `E_0[r^{τ_0}] = Σₙ rⁿ p(n)`. -/
theorem fwdRec_kendallMoment {p : Measure ℕ} [IsProbabilityMeasure p] (hp0 : p {0} = 0)
    (r : ℝ≥0∞) :
    haveI := isMarkovKernel_fwdRecKernel p
    kendallMoment (fwdRecKernel p) {0} r 0 = ∑' n, r ^ n * p {n} := by
  have := isMarkovKernel_fwdRecKernel p
  rw [kendallMoment_eq_tsum _ (measurableSet_singleton 0) r (fwdRec_hitProb_zero p 0),
    ← Summable.sum_add_tsum_nat_add' (f := fun n => r ^ n * p {n}) (k := 1) ENNReal.summable]
  simp only [Finset.range_one, Finset.sum_singleton, hp0, mul_zero, zero_add]
  refine tsum_congr fun n => ?_
  rw [fwdRec_tabooKernel hp0 n 0, zero_add]

/-- The renewal state of the forward recurrence time chain is Kendall of rate `κ` iff
`Σₙ κⁿ p(n) < ∞` (MT p. 370). -/
theorem fwdRec_isKendall_iff {p : Measure ℕ} [IsProbabilityMeasure p] (hp0 : p {0} = 0)
    (κ : ℝ≥0∞) :
    haveI := isMarkovKernel_fwdRecKernel p
    IsKendall (fwdRecKernel p) {0} κ ↔ 1 < κ ∧ κ ≠ ∞ ∧ ∑' n, κ ^ n * p {n} ≠ ∞ := by
  have := isMarkovKernel_fwdRecKernel p
  rw [← fwdRec_kendallMoment hp0 κ]
  constructor
  · rintro ⟨-, hκ, hκt, M, hM, hb⟩
    exact ⟨hκ, hκt, ne_top_of_le_ne_top hM (hb 0 rfl)⟩
  · rintro ⟨hκ, hκt, h⟩
    refine ⟨measurableSet_singleton 0, hκ, hκt, _, h, fun x hx => ?_⟩
    rw [mem_singleton_iff.1 hx]

/-- **Geometric ergodicity forces geometric tails** (MT p. 370): if the renewal state of the forward
recurrence time chain is a geometrically ergodic atom, then `Σₙ κⁿ p(n) < ∞` for some `κ > 1`. -/
theorem fwdRec_tails_of_isGeomErgodicAtom {p : Measure ℕ} [IsProbabilityMeasure p]
    (hp0 : p {0} = 0) (hsupp : ∀ N, ∃ n, N < n ∧ 0 < p {n}) {π : Measure ℕ}
    [IsProbabilityMeasure π]
    (hπ : haveI := isMarkovKernel_fwdRecKernel p; IsInvariant (fwdRecKernel p) π)
    (hge : haveI := isMarkovKernel_fwdRecKernel p; IsGeomErgodicAtom (fwdRecKernel p) π {0}) :
    ∃ κ : ℝ≥0∞, 1 < κ ∧ κ ≠ ∞ ∧ ∑' n, κ ^ n * p {n} ≠ ∞ := by
  have := isMarkovKernel_fwdRecKernel p
  obtain ⟨κ, hκ, hκt, hfull, -⟩ := theorem_15_1_5 (fwdRec_isAccessibleAtom hp0 hsupp) hπ hge
  refine ⟨κ, hκ, hκt, ?_⟩
  rw [← fwdRec_kendallMoment hp0 κ]
  have h0 := Measure.count_eq_zero_iff.1 hfull
  by_contra h
  have hmem : (0 : ℕ) ∈ {x | kendallMoment (fwdRecKernel p) {0} κ x ≠ ∞}ᶜ := fun h' => h' h
  rw [h0] at hmem
  exact hmem

/-- **Geometric tails give geometric ergodicity** (MT p. 370, through Theorem 15.1.4): for an
aperiodic forward recurrence time chain with `Σₙ κⁿ p(n) < ∞`, `κ > 1`, and an invariant
probability `π`, for some `r > 1` and `R < ∞`,
`Σₙ rⁿ⁺¹ ‖Pⁿ⁺¹(x, ·) − π‖ ≤ R U_0^{(κ)}(x, 1) < ∞` for every `x`. -/
theorem fwdRec_geomErgodic_of_tails {p : Measure ℕ} [IsProbabilityMeasure p] (hp0 : p {0} = 0)
    (hsupp : ∀ N, ∃ n, N < n ∧ 0 < p {n})
    (hap : haveI := isMarkovKernel_fwdRecKernel p; IsAperiodic (fwdRecKernel p) Measure.count)
    {π : Measure ℕ} [IsProbabilityMeasure π]
    (hπ : haveI := isMarkovKernel_fwdRecKernel p; IsInvariant (fwdRecKernel p) π) {κ : ℝ≥0∞}
    (hκ : 1 < κ) (hκt : κ ≠ ∞) (h : ∑' n, κ ^ n * p {n} ≠ ∞) :
    haveI := isMarkovKernel_fwdRecKernel p
    (∀ x, geomTaboo (fwdRecKernel p) {0} κ (fun _ => 1) x ≠ ∞) ∧
      ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
        ∑' n, r ^ (n + 1) * fNorm (fun _ => 1) ((fwdRecKernel p ^ (n + 1) : Kernel ℕ ℕ) x) π ≤
          R * geomTaboo (fwdRecKernel p) {0} κ (fun _ => 1) x := by
  have := isMarkovKernel_fwdRecKernel p
  have hK := ((fwdRec_isKendall_iff hp0 κ).2 ⟨hκ, hκt, h⟩).isFKendall_one
  obtain ⟨hfull, -, hbound⟩ := theorem_15_1_4 hap (fwdRec_isAccessibleAtom hp0 hsupp) hπ
    measurable_const (fun _ => le_rfl) hK
  have h0 := Measure.count_eq_zero_iff.1 hfull
  refine ⟨fun x => ?_, hbound⟩
  by_contra hx
  have hmem : x ∈ {x | geomTaboo (fwdRecKernel p) {0} κ (fun _ => 1) x ≠ ∞}ᶜ := fun h' => h' hx
  rw [h0] at hmem
  exact hmem

/-! ### A non-geometrically ergodic chain (15.20) -/

/-- The transition laws of the chain (15.20) on `ℤ₊`: from `0` the chain jumps to `j` with
probability `γ_j`; from `j ≥ 1` it stays with probability `β_j` and returns to `0` otherwise. -/
noncomputable def nonGeomMeas (γ : Measure ℕ) (β : ℕ → ℝ≥0∞) (j : ℕ) : Measure ℕ :=
  if j = 0 then γ else β j • Measure.dirac j + (1 - β j) • Measure.dirac 0

/-- The chain (15.20) (MT p. 370). -/
noncomputable def nonGeomKernel (γ : Measure ℕ) (β : ℕ → ℝ≥0∞) : Kernel ℕ ℕ :=
  ⟨nonGeomMeas γ β, measurable_of_countable _⟩

/-- `P(0, ·) = γ`. -/
theorem nonGeomKernel_zero (γ : Measure ℕ) (β : ℕ → ℝ≥0∞) : nonGeomKernel γ β 0 = γ := by
  change nonGeomMeas γ β 0 = γ
  simp [nonGeomMeas]

/-- `P(j, ·) = β_j δ_j + (1 − β_j) δ_0` for `j ≥ 1`. -/
theorem nonGeomKernel_pos (γ : Measure ℕ) (β : ℕ → ℝ≥0∞) {j : ℕ} (hj : j ≠ 0) :
    nonGeomKernel γ β j = β j • Measure.dirac j + (1 - β j) • Measure.dirac 0 := by
  change nonGeomMeas γ β j = _
  simp [nonGeomMeas, hj]

/-- The chain (15.20) is a transition kernel when `γ` is a probability and `β_j ≤ 1`. -/
theorem isMarkovKernel_nonGeomKernel (γ : Measure ℕ) [IsProbabilityMeasure γ] {β : ℕ → ℝ≥0∞}
    (hβ : ∀ j, β j ≤ 1) : IsMarkovKernel (nonGeomKernel γ β) := by
  refine ⟨fun j => ⟨?_⟩⟩
  by_cases hj : j = 0
  · rw [hj, nonGeomKernel_zero]; exact measure_univ
  · rw [nonGeomKernel_pos γ β hj, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      add_tsub_cancel_of_le (hβ j)]

/-- **The law of `τ_0` from `j ≥ 1`** (MT p. 371): `P_j(τ_0 = n + 1) = β_jⁿ (1 − β_j)`, so
`P_j(τ_0 > n) = β_jⁿ`. -/
theorem nonGeom_tabooKernel_pos (γ : Measure ℕ) [IsProbabilityMeasure γ] {β : ℕ → ℝ≥0∞}
    (hβ : ∀ j, β j ≤ 1) {j : ℕ} (hj : j ≠ 0) (n : ℕ) :
    haveI := isMarkovKernel_nonGeomKernel γ hβ
    tabooKernel (nonGeomKernel γ β) (measurableSet_singleton 0) n j {0} = β j ^ n * (1 - β j) := by
  have := isMarkovKernel_nonGeomKernel γ hβ
  induction n with
  | zero =>
    rw [tabooKernel_zero, nonGeomKernel_pos γ β hj, Measure.add_apply, Measure.smul_apply,
      Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton 0),
      Measure.dirac_apply_of_mem (mem_singleton 0),
      indicator_of_notMem (show j ∉ ({0} : Set ℕ) from hj), smul_eq_mul, smul_eq_mul, mul_zero,
      zero_add, mul_one, pow_zero, one_mul]
  | succ n ih =>
    rw [tabooKernel_succ_apply _ _ n _ (measurableSet_singleton 0),
      ← lintegral_indicator (measurableSet_singleton 0).compl, nonGeomKernel_pos γ β hj,
      lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
      lintegral_dirac, indicator_of_mem (show j ∈ ({0} : Set ℕ)ᶜ from hj),
      indicator_of_notMem (show (0 : ℕ) ∉ ({0} : Set ℕ)ᶜ from fun h => h rfl), ih, smul_eq_mul,
      smul_eq_mul, mul_zero, add_zero, pow_succ]
    ring

/-- From `0`, `P_0(τ_0 = n + 2) ≥ γ_j β_jⁿ (1 − β_j)` for each `j ≥ 1`. -/
theorem nonGeom_tabooKernel_zero_ge (γ : Measure ℕ) [IsProbabilityMeasure γ] {β : ℕ → ℝ≥0∞}
    (hβ : ∀ j, β j ≤ 1) {j : ℕ} (hj : j ≠ 0) (n : ℕ) :
    haveI := isMarkovKernel_nonGeomKernel γ hβ
    γ {j} * (β j ^ n * (1 - β j)) ≤
      tabooKernel (nonGeomKernel γ β) (measurableSet_singleton 0) (n + 1) 0 {0} := by
  have := isMarkovKernel_nonGeomKernel γ hβ
  rw [tabooKernel_succ_apply _ _ n _ (measurableSet_singleton 0), nonGeomKernel_zero]
  calc γ {j} * (β j ^ n * (1 - β j))
      = ∫⁻ y in {j}, tabooKernel (nonGeomKernel γ β) (measurableSet_singleton 0) n y {0} ∂γ := by
        rw [lintegral_singleton, nonGeom_tabooKernel_pos γ hβ hj n, mul_comm]
    _ ≤ _ := lintegral_mono_set (singleton_subset_iff.2 (show j ∈ ({0} : Set ℕ)ᶜ from hj))

/-- **The chain (15.20) is not geometrically ergodic when `β_j → 1`** (MT p. 371): if `γ_j > 0`
and `β_j < 1` for every `j ≥ 1` and `β_j → 1`, then `E_0[r^{τ_0}] = ∞` for every `r > 1`, whatever
the law `γ`. -/
theorem nonGeom_kendallMoment_eq_top (γ : Measure ℕ) [IsProbabilityMeasure γ] {β : ℕ → ℝ≥0∞}
    (hβ : ∀ j, β j ≤ 1) (hγ : ∀ j, j ≠ 0 → 0 < γ {j}) (hβ1 : ∀ j, j ≠ 0 → β j < 1)
    (hlim : Tendsto β atTop (𝓝 1)) {r : ℝ≥0∞} (hr : 1 < r) :
    haveI := isMarkovKernel_nonGeomKernel γ hβ
    kendallMoment (nonGeomKernel γ β) {0} r 0 = ∞ := by
  have := isMarkovKernel_nonGeomKernel γ hβ
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  have hrinv : r⁻¹ < 1 := ENNReal.inv_lt_one.2 hr
  obtain ⟨j, hjβ, hj1⟩ := ((hlim.eventually (lt_mem_nhds hrinv)).and
    (eventually_ge_atTop 1)).exists
  have hj : j ≠ 0 := by omega
  have hrβ : 1 ≤ r * β j :=
    (ENNReal.inv_le_iff_le_mul (fun _ => hr0) (fun _ => (lt_of_le_of_lt bot_le hjβ).ne')).1 hjβ.le
  have hc : γ {j} * (1 - β j) * r ^ 2 ≠ 0 := mul_ne_zero (mul_ne_zero (hγ j hj).ne'
    (tsub_pos_of_lt (hβ1 j hj)).ne') (pow_ne_zero 2 hr0)
  set T := tabooKernel (nonGeomKernel γ β) (measurableSet_singleton 0) with hT
  refine top_le_iff.1 ?_
  calc ∞ = ∑' _ : ℕ, γ {j} * (1 - β j) * r ^ 2 := (ENNReal.tsum_const_eq_top_of_ne_zero hc).symm
    _ ≤ ∑' n, r ^ (n + 1 + 1) * T (n + 1) 0 {0} := ENNReal.tsum_le_tsum fun n => by
        calc γ {j} * (1 - β j) * r ^ 2 ≤ γ {j} * (1 - β j) * r ^ 2 * (r * β j) ^ n :=
              le_mul_of_one_le_right' (one_le_pow₀ hrβ)
          _ = r ^ (n + 1 + 1) * (γ {j} * (β j ^ n * (1 - β j))) := by rw [mul_pow]; ring
          _ ≤ _ := mul_le_mul' le_rfl (nonGeom_tabooKernel_zero_ge γ hβ hj n)
    _ ≤ ∑' n, r ^ (n + 1) * T n 0 {0} := by
        rw [← Summable.sum_add_tsum_nat_add' (f := fun n => r ^ (n + 1) * T n 0 {0}) (k := 1)
          ENNReal.summable]
        exact le_add_self
    _ ≤ _ := tsum_pow_tabooKernel_le_kendallMoment _ _ r 0

/-- Under the hypotheses of `nonGeom_kendallMoment_eq_top`, the chain (15.20) is irreducible. -/
theorem nonGeom_isIrreducibleChain (γ : Measure ℕ) [IsProbabilityMeasure γ] {β : ℕ → ℝ≥0∞}
    (hβ : ∀ j, β j ≤ 1) (hγ : ∀ j, j ≠ 0 → 0 < γ {j}) (hβ1 : ∀ j, j ≠ 0 → β j < 1) :
    haveI := isMarkovKernel_nonGeomKernel γ hβ
    IsIrreducibleChain (nonGeomKernel γ β) := by
  have := isMarkovKernel_nonGeomKernel γ hβ
  have hto : ∀ j, Leads (nonGeomKernel γ β) 0 j := fun j => by
    rcases eq_or_ne j 0 with rfl | hj
    · exact Or.inl rfl
    · refine (leads_iff_exists_pow _ 0 j).2 ⟨1, ?_⟩
      rw [pow_one, nonGeomKernel_zero]
      exact hγ j hj
  have hfrom : ∀ j, Leads (nonGeomKernel γ β) j 0 := fun j => by
    rcases eq_or_ne j 0 with rfl | hj
    · exact Or.inl rfl
    · refine (leads_iff_exists_pow _ j 0).2 ⟨1, ?_⟩
      rw [pow_one, nonGeomKernel_pos γ β hj, Measure.add_apply, Measure.smul_apply,
        Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton 0),
        Measure.dirac_apply_of_mem (mem_singleton 0),
        indicator_of_notMem (show j ∉ ({0} : Set ℕ) from hj), smul_eq_mul, smul_eq_mul, mul_zero,
        zero_add, mul_one]
      exact tsub_pos_of_lt (hβ1 j hj)
  exact (isIrreducibleChain_iff _).2 fun x y =>
    ⟨(hfrom x).trans (hto y), (hfrom y).trans (hto x)⟩

/-- From `j ≥ 1`, `P_j(τ_0 > n) = _0Pⁿ⁺¹(j, X) = β_jⁿ`. -/
theorem nonGeom_tabooKernel_univ_pos (γ : Measure ℕ) [IsProbabilityMeasure γ] {β : ℕ → ℝ≥0∞}
    (hβ : ∀ j, β j ≤ 1) {j : ℕ} (hj : j ≠ 0) (n : ℕ) :
    haveI := isMarkovKernel_nonGeomKernel γ hβ
    tabooKernel (nonGeomKernel γ β) (measurableSet_singleton 0) n j univ = β j ^ n := by
  have := isMarkovKernel_nonGeomKernel γ hβ
  induction n with
  | zero => rw [tabooKernel_zero, measure_univ, pow_zero]
  | succ n ih =>
    rw [tabooKernel_succ_apply _ _ n _ MeasurableSet.univ,
      ← lintegral_indicator (measurableSet_singleton 0).compl, nonGeomKernel_pos γ β hj,
      lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
      lintegral_dirac, indicator_of_mem (show j ∈ ({0} : Set ℕ)ᶜ from hj),
      indicator_of_notMem (show (0 : ℕ) ∉ ({0} : Set ℕ)ᶜ from fun h => h rfl), ih, smul_eq_mul,
      smul_eq_mul, mul_zero, add_zero, pow_succ, mul_comm]

/-- From `j ≥ 1`, `E_j[τ_0] = (1 − β_j)⁻¹` (MT p. 370). -/
theorem nonGeom_meanReturnTime_pos (γ : Measure ℕ) [IsProbabilityMeasure γ] {β : ℕ → ℝ≥0∞}
    (hβ : ∀ j, β j ≤ 1) {j : ℕ} (hj : j ≠ 0) :
    haveI := isMarkovKernel_nonGeomKernel γ hβ
    meanReturnTime (nonGeomKernel γ β) {0} j = (1 - β j)⁻¹ := by
  have := isMarkovKernel_nonGeomKernel γ hβ
  rw [meanReturnTime_eq_tsum _ (measurableSet_singleton 0)]
  simp_rw [nonGeom_tabooKernel_univ_pos γ hβ hj]
  exact ENNReal.tsum_geometric _

/-- **The mean return time to `0`** (MT p. 370), corrected:
`E_0[τ_0] = 1 + Σ_{j ≥ 1} γ_j (1 − β_j)⁻¹`. The book's `Σ_j γ_j [1 + (1 − β_j)⁻¹]` is this with
the bracket for `j = 0` (a direct return, `τ_0 = 1`) replaced by `1`; `β_0` is not defined by
(15.20), whose rows for `j ≥ 1` are meant. -/
theorem nonGeom_meanReturnTime_zero (γ : Measure ℕ) [IsProbabilityMeasure γ] {β : ℕ → ℝ≥0∞}
    (hβ : ∀ j, β j ≤ 1) :
    haveI := isMarkovKernel_nonGeomKernel γ hβ
    meanReturnTime (nonGeomKernel γ β) {0} 0 = 1 + ∑' j, γ {j + 1} * (1 - β (j + 1))⁻¹ := by
  have := isMarkovKernel_nonGeomKernel γ hβ
  rw [meanReturnTime_eq_one_add _ (measurableSet_singleton 0), nonGeomKernel_zero,
    lintegral_countable', ← Summable.sum_add_tsum_nat_add' (k := 1) ENNReal.summable,
    Finset.sum_range_one, meanHitTime_of_mem _ (measurableSet_singleton 0) (mem_singleton 0),
    zero_mul, zero_add]
  congr 1
  refine tsum_congr fun j => ?_
  have hj : j + 1 ≠ 0 := by omega
  rw [meanHitTime_of_notMem _ (measurableSet_singleton 0) (show j + 1 ∉ ({0} : Set ℕ) from hj),
    nonGeom_meanReturnTime_pos γ hβ hj, mul_comm]

/-- **The ergodicity criterion (15.21)** (MT p. 370): under the hypotheses of
`nonGeom_isIrreducibleChain`, the chain (15.20) is positive iff `Σ_{j ≥ 1} γ_j (1 − β_j)⁻¹ < ∞`. -/
theorem nonGeom_isPositive_iff (γ : Measure ℕ) [IsProbabilityMeasure γ] {β : ℕ → ℝ≥0∞}
    (hβ : ∀ j, β j ≤ 1) (hγ : ∀ j, j ≠ 0 → 0 < γ {j}) (hβ1 : ∀ j, j ≠ 0 → β j < 1) :
    haveI := isMarkovKernel_nonGeomKernel γ hβ
    IsPositive (nonGeomKernel γ β) Measure.count ↔
      ∑' j, γ {j + 1} * (1 - β (j + 1))⁻¹ ≠ ∞ := by
  have := isMarkovKernel_nonGeomKernel γ hβ
  have hacc : IsAccessibleAtom (nonGeomKernel γ β) Measure.count {0} :=
    ⟨isAtom_singleton _ 0, isMaximalIrreducibility_count _
      (nonGeom_isIrreducibleChain γ hβ hγ hβ1), by simp⟩
  rw [(theorem_10_2_2 hacc (mem_singleton 0)).1, nonGeom_meanReturnTime_zero γ hβ,
    ENNReal.add_ne_top]
  exact ⟨fun h => h.2, fun h => ⟨ENNReal.one_ne_top, h⟩⟩

/-- **The chain (15.20) is not geometrically ergodic** (MT p. 371): under the hypotheses of
`nonGeom_kendallMoment_eq_top`, `{0}` is Kendall of no rate, and for no invariant probability `π`
is `{0}` a geometrically ergodic atom (Theorem 15.1.5 would make it Kendall). -/
theorem nonGeom_not_geomErgodic (γ : Measure ℕ) [IsProbabilityMeasure γ] {β : ℕ → ℝ≥0∞}
    (hβ : ∀ j, β j ≤ 1) (hγ : ∀ j, j ≠ 0 → 0 < γ {j}) (hβ1 : ∀ j, j ≠ 0 → β j < 1)
    (hlim : Tendsto β atTop (𝓝 1)) :
    haveI := isMarkovKernel_nonGeomKernel γ hβ
    (∀ κ, ¬ IsKendall (nonGeomKernel γ β) {0} κ) ∧
      ∀ (π : Measure ℕ) [IsProbabilityMeasure π], IsInvariant (nonGeomKernel γ β) π →
        ¬ IsGeomErgodicAtom (nonGeomKernel γ β) π {0} := by
  have := isMarkovKernel_nonGeomKernel γ hβ
  refine ⟨fun κ hK => ?_, fun π _ hπ hge => ?_⟩
  · obtain ⟨-, hκ, -, M, hM, hb⟩ := hK
    exact hM <| top_le_iff.1 ((nonGeom_kendallMoment_eq_top γ hβ hγ hβ1 hlim hκ).symm.le.trans
      (hb 0 rfl))
  have hacc : IsAccessibleAtom (nonGeomKernel γ β) Measure.count {0} :=
    ⟨isAtom_singleton _ 0, isMaximalIrreducibility_count _
      (nonGeom_isIrreducibleChain γ hβ hγ hβ1), by simp⟩
  obtain ⟨κ, hκ, -, hfull, -⟩ := theorem_15_1_5 hacc hπ hge
  have h0 := Measure.count_eq_zero_iff.1 hfull
  have hmem : (0 : ℕ) ∈ {x | kendallMoment (nonGeomKernel γ β) {0} κ x ≠ ∞}ᶜ := fun h' =>
    h' (nonGeom_kendallMoment_eq_top γ hβ hγ hβ1 hlim hκ)
  rw [h0] at hmem
  exact hmem

/-! ### Different rates of convergence (§15.1.4) -/

/-- The `3 × 3` transition matrix of MT p. 371, on the states `0, 1, 2`. -/
noncomputable def rateMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / 4, 1 / 2, 1 / 4; 0, 3 / 4, 1 / 4; 3 / 4, 0, 1 / 4]

/-- The entries of `rateMatrix` are non-negative. -/
theorem rateMatrix_nonneg (x y : Fin 3) : 0 ≤ rateMatrix x y := by
  fin_cases x <;> fin_cases y <;> simp [rateMatrix] <;> norm_num

/-- The rows of `rateMatrix` sum to `1`. -/
theorem rateMatrix_rowSum (x : Fin 3) : ∑ y, rateMatrix x y = 1 := by
  fin_cases x <;> simp [rateMatrix, Fin.sum_univ_three] <;> norm_num

/-- The chain with transition matrix `rateMatrix`. -/
noncomputable def rateKernel : Kernel (Fin 3) (Fin 3) :=
  matKernel fun x y => ENNReal.ofReal (rateMatrix x y)

/-- `rateKernel` is a transition kernel. -/
theorem isMarkovKernel_rateKernel : IsMarkovKernel rateKernel := by
  refine isMarkovKernel_matKernel fun x => ?_
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun y _ => rateMatrix_nonneg x y,
    rateMatrix_rowSum, ENNReal.ofReal_one]

/-- The powers of `rateMatrix` are non-negative. -/
theorem rateMatrix_pow_nonneg (n : ℕ) (x z : Fin 3) : 0 ≤ (rateMatrix ^ n) x z := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun y _ => mul_nonneg (rateMatrix_nonneg x y) (ih y)

/-- `Pⁿ(x, {z}) = (Mⁿ)(x, z)` for the real matrix `M = rateMatrix`. -/
theorem rateKernel_pow_singleton (n : ℕ) (x z : Fin 3) :
    (rateKernel ^ n) x {z} = ENNReal.ofReal ((rateMatrix ^ n) x z) := by
  rw [rateKernel, matKernel_pow_singleton]
  induction n generalizing x with
  | zero =>
    rw [pow_zero, Matrix.one_apply, matPow]
    by_cases h : x = z <;> simp [h]
  | succ n ih =>
    rw [matPow]
    simp_rw [ih]
    rw [tsum_fintype, pow_succ', Matrix.mul_apply, ENNReal.ofReal_sum_of_nonneg fun y _ =>
      mul_nonneg (rateMatrix_nonneg x y) (rateMatrix_pow_nonneg n y z)]
    exact Finset.sum_congr rfl fun y _ => (ENNReal.ofReal_mul (rateMatrix_nonneg x y)).symm

/-- Row `0` of every power `Mⁿ⁺¹` is `(1/4, 1/2, 1/4)`, the first row of `M`. -/
theorem rateMatrix_pow_row_zero (n : ℕ) (z : Fin 3) :
    (rateMatrix ^ (n + 1)) 0 z = rateMatrix 0 z := by
  induction n generalizing z with
  | zero => rw [zero_add, pow_one]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih]
    fin_cases z <;> simp [rateMatrix, Fin.sum_univ_three] <;> norm_num

/-- Column `2` of every power `Mⁿ⁺¹` is constant `1/4`. -/
theorem rateMatrix_pow_col_two (n : ℕ) (x : Fin 3) : (rateMatrix ^ (n + 1)) x 2 = 1 / 4 := by
  induction n generalizing x with
  | zero => rw [zero_add, pow_one]; fin_cases x <;> simp [rateMatrix]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    rw [← Finset.sum_mul, rateMatrix_rowSum, one_mul]

/-- Row `1` of `Mⁿ⁺¹`: `(1/4 − 4^{−(n+1)}, 1/2 + 4^{−(n+1)}, 1/4)`. -/
theorem rateMatrix_pow_row_one (n : ℕ) :
    (rateMatrix ^ (n + 1)) 1 0 = 1 / 4 - (1 / 4) ^ (n + 1) ∧
      (rateMatrix ^ (n + 1)) 1 1 = 1 / 2 + (1 / 4) ^ (n + 1) := by
  induction n with
  | zero => simp [rateMatrix]; norm_num
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have h2 := rateMatrix_pow_col_two n 1
    rw [pow_succ, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_three,
      h0, h1, h2]
    simp [rateMatrix]
    constructor <;> ring

/-- The law `π = (1/4, 1/2, 1/4)` (the first row of `M`). -/
noncomputable def ratePi : Measure (Fin 3) := rateKernel 0

/-- `π{z} = M(0, z)`. -/
theorem ratePi_singleton (z : Fin 3) : ratePi {z} = ENNReal.ofReal (rateMatrix 0 z) := by
  rw [ratePi, ← pow_one rateKernel, rateKernel_pow_singleton, pow_one]

/-- `π` is invariant (MT p. 371). -/
theorem isInvariant_ratePi : IsInvariant rateKernel ratePi := by
  have := isMarkovKernel_rateKernel
  refine Measure.ext_of_singleton fun z => ?_
  have h := rateKernel_pow_singleton 2 0 z
  rw [rateMatrix_pow_row_zero 1 z, pow_two] at h
  change (rateKernel ∘ₖ rateKernel) 0 {z} = _ at h
  rw [Kernel.comp_apply] at h
  change (rateKernel ∘ₘ rateKernel 0) {z} = ratePi {z}
  rw [h, ratePi_singleton]

/-- **The states `0` and `2` converge at rate `0`** (MT p. 371): `Pⁿ(0, 0) = π(0)` and
`Pⁿ(2, 2) = π(2)` for every `n ≥ 1`; the limits are attained at every step. -/
theorem rateKernel_pow_zero_two (n : ℕ) :
    (rateKernel ^ (n + 1)) 0 {0} = ratePi {0} ∧ (rateKernel ^ (n + 1)) 2 {2} = ratePi {2} := by
  rw [rateKernel_pow_singleton, rateKernel_pow_singleton, ratePi_singleton, ratePi_singleton,
    rateMatrix_pow_row_zero, rateMatrix_pow_col_two]
  simp [rateMatrix]

/-- **The state `1` converges at rate exactly `1/4`** (MT p. 371), corrected:
`Pⁿ(1, 1) − π(1) = 4⁻ⁿ` for every `n ≥ 1`, so `|Pⁿ(1, 1) − π(1)| ≤ (1/4)ⁿ` for every `n`, while
no rate `ρ < 1/4` works. The book says the rate is at least `ρ₁ > 1/4`; it is `1/4`. The rates
of the states do differ (`0` for the states `0` and `2`). -/
theorem rateKernel_state_one :
    (∀ n, ((rateKernel ^ (n + 1)) 1 {1}).toReal - (ratePi {1}).toReal = (1 / 4) ^ (n + 1)) ∧
      (∀ n, |((rateKernel ^ n) 1 {1}).toReal - (ratePi {1}).toReal| ≤ (1 / 4) ^ n) ∧
      ∀ ρ M : ℝ, 0 ≤ ρ → ρ < 1 / 4 →
        ¬ ∀ n, |((rateKernel ^ n) 1 {1}).toReal - (ratePi {1}).toReal| ≤ M * ρ ^ n := by
  have hπ : (ratePi {1}).toReal = 1 / 2 := by
    rw [ratePi_singleton, ENNReal.toReal_ofReal (rateMatrix_nonneg 0 1)]
    simp [rateMatrix]
  have hexact : ∀ n, ((rateKernel ^ (n + 1)) 1 {1}).toReal - (ratePi {1}).toReal =
      (1 / 4) ^ (n + 1) := fun n => by
    rw [rateKernel_pow_singleton, ENNReal.toReal_ofReal (rateMatrix_pow_nonneg _ _ _),
      (rateMatrix_pow_row_one n).2, hπ]
    ring
  refine ⟨hexact, fun n => ?_, fun ρ M hρ0 hρ h => ?_⟩
  · rcases n with _ | n
    · rw [rateKernel_pow_singleton, pow_zero, pow_zero, Matrix.one_apply_eq, hπ,
        ENNReal.toReal_ofReal zero_le_one]
      norm_num [abs_of_pos]
    · rw [hexact n, abs_of_pos (by positivity)]
  · -- `4⁻ⁿ ≤ M ρⁿ` for all `n` fails, as `(4ρ)ⁿ → 0`
    have hlim : Tendsto (fun n : ℕ => M * (4 * ρ) ^ n) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ 4 * ρ) (by linarith)
      simpa using this.const_mul M
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
    have h1 := h (n + 1)
    rw [hexact n, abs_of_pos (by positivity)] at h1
    have h4 : (0 : ℝ) < 4 ^ (n + 1) := by positivity
    have e : (1 / 4 : ℝ) ^ (n + 1) * 4 ^ (n + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have e2 : M * ρ ^ (n + 1) * 4 ^ (n + 1) = M * (4 * ρ) ^ (n + 1) := by rw [mul_pow]; ring
    have h5 := mul_le_mul_of_nonneg_right h1 h4.le
    rw [e, e2] at h5
    have h6 : M * (4 * ρ) ^ (n + 1) ≤ M * (4 * ρ) ^ n ∨ M < 0 := by
      rcases le_or_gt 0 M with hM | hM
      · left
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) (by linarith)
          n.le_succ) hM
      · right; exact hM
    rcases h6 with h6 | h6
    · linarith
    · nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 4 * ρ) (n + 1)]

/-- **The printed generating function `U^{(z)}(1, 1)` is wrong** (MT p. 371). Read as
`1 + z/(2(1 − z)) + z/(4(1 − z))` (as `U^{(z)}(0, 0) = 1 + z/(4(1 − z))` is), its `z²`
coefficient is `3/4`, but `P²(1, 1) = 9/16`. From `rateKernel_state_one`,
`U^{(z)}(1, 1) = 1 + z/(2(1 − z)) + z/(4 − z)`. -/
theorem rateKernel_U11_counterexample :
    (rateKernel ^ 2) 1 {1} = ENNReal.ofReal (9 / 16) ∧
      (rateKernel ^ 2) 1 {1} ≠ ENNReal.ofReal (1 / 2 + 1 / 4) := by
  have h : (rateKernel ^ 2) 1 {1} = ENNReal.ofReal (9 / 16) := by
    rw [rateKernel_pow_singleton, (rateMatrix_pow_row_one 1).2]
    norm_num
  refine ⟨h, ?_⟩
  rw [h]
  intro h'
  have := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)).1 h'
  norm_num at this

/-- **A symmetric transition matrix has the uniform invariant law** (MT p. 372, for the matrix of
Teugels' example): if `P(x, y) = P(y, x)` on a finite space, `π = |X|⁻¹ · count` is invariant. -/
theorem isInvariant_uniform_of_symm {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype X] {p : X → X → ℝ≥0∞} (hp : IsTransitionMatrix p) (hsymm : ∀ x y, p x y = p y x) :
    IsInvariant (matKernel p) ((Fintype.card X : ℝ≥0∞)⁻¹ • Measure.count) := by
  refine Measure.ext_of_singleton fun y => ?_
  rw [Measure.bind_apply (measurableSet_singleton y)
      (Kernel.aemeasurable _), lintegral_smul_measure, lintegral_count, Measure.smul_apply,
    Measure.count_singleton, smul_eq_mul, smul_eq_mul, mul_one]
  simp_rw [matKernel_singleton, hsymm _ y]
  rw [hp y, mul_one]

/-! ### The Bernoulli random walk on `ℤ₊` (§15.5.1) -/

/-- The Bernoulli increment law: `+1` with probability `p`, `−1` with probability `1 − p`. -/
noncomputable def bernoulliStep (p : ℝ) : Measure ℤ :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac (-1)

/-- The Bernoulli increment law is a probability for `0 ≤ p ≤ 1`. -/
theorem isProbabilityMeasure_bernoulliStep {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliStep p) :=
  ⟨by rw [bernoulliStep, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
    measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.ofReal_add hp0 (by linarith), add_sub_cancel, ENNReal.ofReal_one]⟩

/-- **The Bernoulli random walk on `ℤ₊`** (MT §15.5.1, p. 388): `P(x, x + 1) = p`,
`P(x, x − 1) = 1 − p` for `x > 0` and `P(0, 0) = 1 − p`. -/
noncomputable def bernoulliWalk (p : ℝ) : Kernel ℕ ℕ := reflectedWalkKernel (bernoulliStep p)

/-- The Bernoulli walk is a transition kernel. -/
theorem isMarkovKernel_bernoulliWalk {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsMarkovKernel (bernoulliWalk p) :=
  haveI := isProbabilityMeasure_bernoulliStep hp0 hp1
  isMarkovKernel_reflectedWalkKernel _

/-- `PV(x) = p V(x + 1) + (1 − p) V(x − 1)` (with `0 − 1 = 0` in `ℕ`). -/
theorem lintegral_bernoulliWalk (p : ℝ) (V : ℕ → ℝ≥0∞) (x : ℕ) :
    ∫⁻ y, V y ∂bernoulliWalk p x =
      ENNReal.ofReal p * V (x + 1) + ENNReal.ofReal (1 - p) * V (x - 1) := by
  have h1 : reflectStep (x, 1) = x + 1 := by simp only [reflectStep]; omega
  have h2 : reflectStep (x, -1) = x - 1 := by simp only [reflectStep]; omega
  rw [bernoulliWalk, reflectedWalkKernel, recursionKernel_apply _ (measurable_of_countable _) x,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _), bernoulliStep,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
    lintegral_dirac, h1, h2, smul_eq_mul, smul_eq_mul]

/-- `P(x, {y}) = p 1{y = x + 1} + (1 − p) 1{y = x − 1}`. -/
theorem bernoulliWalk_singleton (p : ℝ) (x y : ℕ) :
    bernoulliWalk p x {y} = ENNReal.ofReal p * ({y} : Set ℕ).indicator 1 (x + 1) +
      ENNReal.ofReal (1 - p) * ({y} : Set ℕ).indicator 1 (x - 1) := by
  rw [← lintegral_indicator_one (measurableSet_singleton y), lintegral_bernoulliWalk]

/-- **(V4) for the Bernoulli walk** (MT p. 388): for `V(x) = zˣ` with `z ≥ 1`,
`PV(x) = (pz + (1 − p)/z) V(x)` for `x > 0` and `PV(0) = pz + 1 − p`. -/
theorem bernoulliWalk_driftV4 {p z : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz : 1 ≤ z) :
    DriftV4 (bernoulliWalk p) (fun x => ENNReal.ofReal (z ^ x))
      (ENNReal.ofReal (p * z + (1 - p) / z)) (ENNReal.ofReal (p * z + (1 - p))) {0} := by
  have hz0 : 0 < z := by linarith
  have h1p : 0 ≤ 1 - p := by linarith
  intro x
  rw [lintegral_bernoulliWalk]
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [indicator_of_mem (mem_singleton 0)]
    refine le_trans (le_of_eq ?_) le_add_self
    rw [← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_mul h1p, ← ENNReal.ofReal_add
      (mul_nonneg hp0 (by positivity)) (mul_nonneg h1p (by positivity))]
    congr 1
    simp
  · obtain ⟨k, rfl⟩ : ∃ k, x = k + 1 := ⟨x - 1, by omega⟩
    rw [indicator_of_notMem (show k + 1 ∉ ({0} : Set ℕ) by simp), add_zero, Nat.add_sub_cancel,
      ← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_mul h1p, ← ENNReal.ofReal_add
      (mul_nonneg hp0 (by positivity)) (mul_nonneg h1p (by positivity)),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    field_simp
    ring

/-- For `p < 1/2` some `z > 1` has `pz + (1 − p)/z < 1` (MT p. 388), e.g. `z = 1 + (1 − 2p)/2`. -/
theorem bernoulli_rate_lt_one {p : ℝ} (hp : p < 1 / 2) :
    ∃ z : ℝ, 1 < z ∧ p * z + (1 - p) / z < 1 := by
  refine ⟨1 + (1 - 2 * p) / 2, by linarith, ?_⟩
  have hz0 : 0 < 1 + (1 - 2 * p) / 2 := by linarith
  rw [show p * (1 + (1 - 2 * p) / 2) + (1 - p) / (1 + (1 - 2 * p) / 2) =
      (p * (1 + (1 - 2 * p) / 2) ^ 2 + (1 - p)) / (1 + (1 - 2 * p) / 2) by field_simp,
    div_lt_one hz0]
  have hd : 0 < 1 - 2 * p := by linarith
  nlinarith [mul_pos (mul_pos hd hd) (by linarith : (0 : ℝ) < 2 - p)]

/-- For `0 < p < 1` the Bernoulli walk is irreducible. -/
theorem bernoulliWalk_isIrreducibleChain {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    haveI := isMarkovKernel_bernoulliWalk hp0.le hp1.le
    IsIrreducibleChain (bernoulliWalk p) := by
  have := isMarkovKernel_bernoulliWalk hp0.le hp1.le
  have hup : ∀ x, Leads (bernoulliWalk p) x (x + 1) := fun x =>
    (leads_iff_exists_pow _ _ _).2 ⟨1, by
      rw [pow_one, bernoulliWalk_singleton, indicator_of_mem (mem_singleton _), Pi.one_apply,
        mul_one]
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hp0) le_self_add⟩
  have hdown : ∀ x, Leads (bernoulliWalk p) (x + 1) x := fun x =>
    (leads_iff_exists_pow _ _ _).2 ⟨1, by
      rw [pow_one, bernoulliWalk_singleton, Nat.add_sub_cancel,
        indicator_of_mem (mem_singleton x), Pi.one_apply, mul_one]
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by linarith)) le_add_self⟩
  have hfrom0 : ∀ y, Leads (bernoulliWalk p) 0 y := fun y => by
    induction y with
    | zero => exact Or.inl rfl
    | succ y ih => exact ih.trans (hup y)
  have hto0 : ∀ y, Leads (bernoulliWalk p) y 0 := fun y => by
    induction y with
    | zero => exact Or.inl rfl
    | succ y ih => exact (hdown y).trans ih
  exact (isIrreducibleChain_iff _).2 fun x y =>
    ⟨(hto0 x).trans (hfrom0 y), (hto0 y).trans (hfrom0 x)⟩

/-- **The Bernoulli walk is geometrically ergodic for `p < 1/2`** (MT p. 388): for `0 < p < 1/2`
there is `z > 1` such that `V(x) = zˣ` satisfies (V4) with `C = {0}`; the chain is positive,
`π(V) < ∞`, and `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_V ≤ R V(x)` for some `r > 1`, `R < ∞` and every `x`. -/
theorem bernoulliWalk_geometricErgodic {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) :
    haveI := isMarkovKernel_bernoulliWalk hp0.le (by linarith)
    ∃ z : ℝ, 1 < z ∧ ∃ ρ : ℝ≥0∞, ρ < 1 ∧
      DriftV4 (bernoulliWalk p) (fun x => ENNReal.ofReal (z ^ x)) ρ
        (ENNReal.ofReal (p * z + (1 - p))) {0} ∧
      IsPositive (bernoulliWalk p) Measure.count ∧
      ∀ (π : Measure ℕ) [IsProbabilityMeasure π], IsInvariant (bernoulliWalk p) π →
        ∫⁻ x, ENNReal.ofReal (z ^ x) ∂π ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
          ∑' n, r ^ n * fNorm (fun x => ENNReal.ofReal (z ^ x))
            ((bernoulliWalk p ^ n : Kernel ℕ ℕ) x) π ≤ R * ENNReal.ofReal (z ^ x) := by
  have hp1 : p < 1 := by linarith
  have := isMarkovKernel_bernoulliWalk hp0.le hp1.le
  obtain ⟨z, hz, hρ⟩ := bernoulli_rate_lt_one hp
  have hdrift := bernoulliWalk_driftV4 hp0.le hp1.le hz.le
  have hψ := isMaximalIrreducibility_count _ (bernoulliWalk_isIrreducibleChain hp0 hp1)
  -- aperiodicity: `P(0, ·) ≥ (1 − p) δ₀`
  have hδ0 : 0 < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.2 (by linarith)
  have hδ1 : ENNReal.ofReal (1 - p) < 1 := by
    rw [ENNReal.ofReal_lt_one]; linarith
  let M : Minorization (bernoulliWalk p) :=
    { C := {0}, δ := ENNReal.ofReal (1 - p), ν := Measure.dirac 0,
      measurableSet_C := measurableSet_singleton 0, δ_pos := hδ0, δ_lt_one := hδ1,
      isProbabilityMeasure_ν := inferInstance,
      le := fun x hx => Measure.le_intro fun A _ _ => by
        rw [mem_singleton_iff.1 hx, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply' _ (by measurability),
          ← lintegral_indicator_one (by measurability), lintegral_bernoulliWalk]
        exact le_add_self }
  have hap : IsAperiodic (bernoulliWalk p) Measure.count :=
    isAperiodic_of_minorization hψ M (by simp [M]) (by simp [M])
  have hV1 : ∀ x : ℕ, 1 ≤ ENNReal.ofReal (z ^ x) := fun x =>
    ENNReal.one_le_ofReal.2 (one_le_pow₀ hz.le)
  have hC : IsPetite (bernoulliWalk p) {0} := (isAtom_singleton _ 0).isPetite ⟨0, rfl⟩
  obtain ⟨-, -, hpos, hπ⟩ := theorem_15_0_1_consequences hψ hap (measurable_of_countable _) hV1
    (x₀ := 0) ENNReal.ofReal_ne_top (ENNReal.ofReal_lt_one.2 hρ) ENNReal.ofReal_ne_top hC hdrift
  exact ⟨z, hz, _, ENNReal.ofReal_lt_one.2 hρ, hdrift, hpos, hπ⟩

/-! ### The simple linear and bilinear models (§15.5.2) -/

/-- The real inequality behind (V4) for the bilinear model: for `t ≥ 0`, `0 ≤ a < 1`, `c ≥ 0`
and `T = 2c/(1 − a)`, `(at + c)ᵏ ≤ ((1 + a)/2)ᵏ tᵏ + (aT + c)ᵏ`. -/
theorem pow_affine_le {a c t : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (k : ℕ) :
    (a * t + c) ^ k ≤ ((1 + a) / 2) ^ k * t ^ k + (a * (2 * c / (1 - a)) + c) ^ k := by
  have h1a : 0 < 1 - a := by linarith
  have hT0 : 0 ≤ 2 * c / (1 - a) := div_nonneg (by linarith) h1a.le
  have hM0 : 0 ≤ (a * (2 * c / (1 - a)) + c) ^ k := pow_nonneg (by positivity) k
  have hq0 : 0 ≤ ((1 + a) / 2) ^ k * t ^ k := by positivity
  rcases le_or_gt t (2 * c / (1 - a)) with htT | htT
  · have : (a * t + c) ^ k ≤ (a * (2 * c / (1 - a)) + c) ^ k :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) k
    linarith
  · have hlin : a * t + c ≤ (1 + a) / 2 * t := by
      have : 2 * c < t * (1 - a) := (div_lt_iff₀ h1a).1 htT
      nlinarith
    have : (a * t + c) ^ k ≤ ((1 + a) / 2) ^ k * t ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hlin k
    linarith

/-- **(15.51)** (MT p. 390): `E[|X₁| | X₀ = x] ≤ E|θ + bW| |x| + E|W|` for the bilinear model. -/
theorem bilinear_eq_15_51 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (θ b x : ℝ) :
    ∫⁻ y, ‖y‖ₑ ∂(bilinearKernel Γ θ b x) ≤
      (∫⁻ w, ‖θ + b * w‖ₑ ∂Γ) * ‖x‖ₑ + ∫⁻ w, ‖w‖ₑ ∂Γ := by
  have h := bilinear_lintegral_pow_le Γ θ b x le_rfl
  simp only [pow_one, Nat.cast_one, inv_one, ENNReal.rpow_one] at h
  exact h

/-- **(V4) for the bilinear model, `k`-th moments** (MT p. 390): if `E|W|ᵏ < ∞` and
`E|θ + bW|ᵏ < 1` (`k ≥ 1`), then `V(x) = |x|ᵏ + 1` satisfies `PV ≤ λV + L` with `λ < 1` and
`L < ∞`. For `k = 1` this is (15.52) with (15.51). -/
theorem bilinear_le_mul_add (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (θ b : ℝ) {k : ℕ}
    (hk : 1 ≤ k) (hW : ∫⁻ w, ‖w‖ₑ ^ k ∂Γ ≠ ∞) (hρ : ∫⁻ w, ‖θ + b * w‖ₑ ^ k ∂Γ < 1) :
    ∃ lam L : ℝ≥0∞, lam < 1 ∧ L ≠ ∞ ∧ ∀ x, ∫⁻ y, (‖y‖ₑ ^ k + 1) ∂bilinearKernel Γ θ b x ≤
      lam * (‖x‖ₑ ^ k + 1) + L := by
  have := isMarkovKernel_bilinearKernel Γ θ b
  have hk0 : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hk)
  set A := (∫⁻ w, ‖θ + b * w‖ₑ ^ k ∂Γ) ^ (k : ℝ)⁻¹ with hA
  set C := (∫⁻ w, ‖w‖ₑ ^ k ∂Γ) ^ (k : ℝ)⁻¹ with hC
  have hA1 : A < 1 := ENNReal.rpow_lt_one hρ hk0
  have hAt : A ≠ ∞ := ne_top_of_lt hA1
  have hCt : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hk0.le hW
  set a := A.toReal with ha
  set c := C.toReal with hc
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have ha1 : a < 1 := by
    have := (ENNReal.toReal_lt_toReal hAt ENNReal.one_ne_top).2 hA1
    rwa [ENNReal.toReal_one] at this
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ (a * (2 * c / (1 - a)) + c) ^ k :=
    pow_nonneg (add_nonneg (mul_nonneg ha0 (div_nonneg (by linarith) (by linarith))) hc0) k
  refine ⟨ENNReal.ofReal (((1 + a) / 2) ^ k), ENNReal.ofReal ((a * (2 * c / (1 - a)) + c) ^ k) + 1,
    ?_, ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩, fun x => ?_⟩
  · rw [ENNReal.ofReal_lt_one]
    exact pow_lt_one₀ (by positivity) (by linarith) (by omega)
  have hb := bilinear_lintegral_pow_le Γ θ b x hk
  have hAx : A * ‖x‖ₑ + C = ENNReal.ofReal (a * |x| + c) := by
    rw [ENNReal.ofReal_add (mul_nonneg ha0 (abs_nonneg x)) hc0, ENNReal.ofReal_mul ha0,
      ENNReal.ofReal_toReal hAt, ENNReal.ofReal_toReal hCt, ← Real.enorm_eq_ofReal_abs]
  rw [hAx, ← ENNReal.ofReal_pow (add_nonneg (mul_nonneg ha0 (abs_nonneg x)) hc0)] at hb
  have hx : ‖x‖ₑ ^ k = ENNReal.ofReal (|x| ^ k) := by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_pow (abs_nonneg x)]
  rw [lintegral_add_left (measurable_enorm.pow_const k), lintegral_const, measure_univ, mul_one]
  calc ∫⁻ y, ‖y‖ₑ ^ k ∂bilinearKernel Γ θ b x + 1
      ≤ ENNReal.ofReal ((a * |x| + c) ^ k) + 1 := add_le_add hb le_rfl
    _ ≤ ENNReal.ofReal (((1 + a) / 2) ^ k * |x| ^ k + (a * (2 * c / (1 - a)) + c) ^ k) + 1 :=
        add_le_add (ENNReal.ofReal_le_ofReal (pow_affine_le ha0 ha1 hc0 (abs_nonneg x) k)) le_rfl
    _ = ENNReal.ofReal (((1 + a) / 2) ^ k) * ‖x‖ₑ ^ k +
          (ENNReal.ofReal ((a * (2 * c / (1 - a)) + c) ^ k) + 1) := by
        rw [ENNReal.ofReal_add (by positivity) hM0, ENNReal.ofReal_mul (by positivity), hx,
          add_assoc]
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl le_self_add) le_rfl

/-- Sublevel sets of `|x|ᵏ + 1` are bounded, hence petite when compact sets are petite. -/
theorem isUnboundedOffPetite_enorm_pow {P : Kernel ℝ ℝ}
    (hcpt : ∀ K : Set ℝ, IsCompact K → IsPetite P K) {k : ℕ} (hk : 1 ≤ k) :
    IsUnboundedOffPetite P (fun x : ℝ => ‖x‖ₑ ^ k + 1) := by
  intro ℓ hℓ
  refine (hcpt (Icc (-max 1 ℓ.toReal) (max 1 ℓ.toReal)) isCompact_Icc).subset
    (measurableSet_le ((measurable_enorm.pow_const k).add measurable_const) measurable_const)
    fun x hx => ?_
  have h1 : ENNReal.ofReal (|x| ^ k) ≤ ℓ := by
    rw [ENNReal.ofReal_pow (abs_nonneg x), ← Real.enorm_eq_ofReal_abs]
    exact le_self_add.trans hx
  have h2 : |x| ^ k ≤ ℓ.toReal := (ENNReal.ofReal_le_iff_le_toReal hℓ).1 h1
  have h3 : |x| ≤ max 1 ℓ.toReal := by
    rcases le_or_gt |x| 1 with h | h
    · exact h.trans (le_max_left _ _)
    · exact (le_self_pow₀ h.le (by omega)).trans (h2.trans (le_max_right _ _))
  exact abs_le.1 h3

/-- **The bilinear model is `V`-geometrically ergodic** (MT p. 390), for `V(x) = |x|ᵏ + 1`: if
`E|W|ᵏ < ∞` and `E|θ + bW|ᵏ < 1` (`k ≥ 1`; `k = 1` is (15.52)), and the chain is
`ψ`-irreducible and aperiodic with compact sets petite, then (V4) holds for a petite set, the
chain is positive, `π(V) < ∞`, and `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_V ≤ R V(x)` for every `x`. -/
theorem bilinear_geometricErgodic (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (θ b : ℝ) {k : ℕ}
    (hk : 1 ≤ k) (hW : ∫⁻ w, ‖w‖ₑ ^ k ∂Γ ≠ ∞) (hρ : ∫⁻ w, ‖θ + b * w‖ₑ ^ k ∂Γ < 1)
    {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_bilinearKernel Γ θ b
      IsMaximalIrreducibility (bilinearKernel Γ θ b) ψ)
    (hap : IsAperiodic (bilinearKernel Γ θ b) ψ)
    (hcpt : ∀ K : Set ℝ, IsCompact K → IsPetite (bilinearKernel Γ θ b) K) :
    haveI := isMarkovKernel_bilinearKernel Γ θ b
    (∃ ρ c : ℝ≥0∞, ρ < 1 ∧ c ≠ ∞ ∧ ∃ C, IsPetite (bilinearKernel Γ θ b) C ∧
      DriftV4 (bilinearKernel Γ θ b) (fun x => ‖x‖ₑ ^ k + 1) ρ c C) ∧
      IsPositive (bilinearKernel Γ θ b) ψ ∧
      ∀ (π : Measure ℝ) [IsProbabilityMeasure π], IsInvariant (bilinearKernel Γ θ b) π →
        ∫⁻ x, (‖x‖ₑ ^ k + 1) ∂π ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
          ∑' n, r ^ n * fNorm (fun x : ℝ => ‖x‖ₑ ^ k + 1)
            ((bilinearKernel Γ θ b ^ n : Kernel ℝ ℝ) x) π ≤ R * (‖x‖ₑ ^ k + 1) := by
  have := isMarkovKernel_bilinearKernel Γ θ b
  have hVm : Measurable fun x : ℝ => ‖x‖ₑ ^ k + 1 :=
    (measurable_enorm.pow_const k).add measurable_const
  have hV1 : ∀ x : ℝ, 1 ≤ ‖x‖ₑ ^ k + 1 := fun x => le_add_self
  obtain ⟨lam, L, hlam, hL, h⟩ := bilinear_le_mul_add Γ θ b hk hW hρ
  obtain ⟨ρ, c, hρ1, hc, C, hC, hdrift⟩ := (lemma_15_2_8 hVm hV1).2
    ⟨isUnboundedOffPetite_enorm_pow hcpt hk, lam, L, hlam, hL, h⟩
  obtain ⟨-, -, hpos, hπ⟩ := theorem_15_0_1_consequences hψ hap hVm hV1 (x₀ := 0)
    (ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top enorm_ne_top, ENNReal.one_ne_top⟩) hρ1 hc hC hdrift
  exact ⟨⟨ρ, c, hρ1, hc, C, hC, hdrift⟩, hpos, hπ⟩

/-- **The variances converge geometrically** (MT p. 390): for the bilinear model with a centred
`W` of variance `σ²` and `θ² + b²σ² < 1`, `V(x) = x² + 1` satisfies (V4), and if the chain is
`ψ`-irreducible and aperiodic with compact sets petite, then for every invariant probability `π`,
`π(x²) < ∞` and for some `r > 1`, `R < ∞`,
`Σₙ rⁿ |∫ Pⁿ(x, dy) y² − ∫ π(dy) y²| ≤ R (x² + 1)` for every `x`. -/
theorem bilinear_variance_convergence (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (θ b : ℝ)
    (hW1 : Integrable (fun w => w) Γ) (hW2 : Integrable (fun w => w ^ 2) Γ)
    (h0 : ∫ w, w ∂Γ = 0) (h : θ ^ 2 + b ^ 2 * ∫ w, w ^ 2 ∂Γ < 1) {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_bilinearKernel Γ θ b
      IsMaximalIrreducibility (bilinearKernel Γ θ b) ψ)
    (hap : IsAperiodic (bilinearKernel Γ θ b) ψ)
    (hcpt : ∀ K : Set ℝ, IsCompact K → IsPetite (bilinearKernel Γ θ b) K) :
    haveI := isMarkovKernel_bilinearKernel Γ θ b
    ∀ (π : Measure ℝ) [IsProbabilityMeasure π], IsInvariant (bilinearKernel Γ θ b) π →
      ∫⁻ x, ‖x‖ₑ ^ 2 ∂π ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
        ∑' n, r ^ n * ENNReal.ofReal |∫ y, y ^ 2 ∂(bilinearKernel Γ θ b ^ n : Kernel ℝ ℝ) x -
          ∫ y, y ^ 2 ∂π| ≤ R * (‖x‖ₑ ^ 2 + 1) := by
  have := isMarkovKernel_bilinearKernel Γ θ b
  obtain ⟨hW, hρ⟩ := bilinear_condition_14_32 Γ θ b hW1 hW2 h0 h
  obtain ⟨⟨ρ, c, hρ1, hc, C, hC, hdrift⟩, -, hπ⟩ :=
    bilinear_geometricErgodic Γ θ b (by norm_num) hW hρ hψ hap hcpt
  intro π _ hinv
  obtain ⟨hπV, r, hr, R, hR, hbound⟩ := hπ π hinv
  have hVm : Measurable fun x : ℝ => ‖x‖ₑ ^ 2 + 1 :=
    (measurable_enorm.pow_const 2).add measurable_const
  have hCm : MeasurableSet C := by
    obtain ⟨_, _, hm, -⟩ := hC
    exact hm
  -- `y²` is integrable whenever `∫ (y² + 1) < ∞`
  have hint : ∀ μ : Measure ℝ, ∫⁻ y, (‖y‖ₑ ^ 2 + 1) ∂μ ≠ ∞ → Integrable (fun y : ℝ => y ^ 2) μ :=
    fun μ hμ => ⟨(measurable_id.pow_const 2).aestronglyMeasurable, by
      change ∫⁻ y, ‖y ^ 2‖ₑ ∂μ < ∞
      simp_rw [enorm_pow]
      exact lt_of_le_of_lt (lintegral_mono fun y => le_self_add) hμ.lt_top⟩
  refine ⟨ne_top_of_le_ne_top hπV (lintegral_mono fun y => le_self_add), r, hr, R, hR,
    fun x => le_trans (ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl ?_) (hbound x)⟩
  have := isMarkovKernel_pow (bilinearKernel Γ θ b) n
  have hPn : ∫⁻ y, (‖y‖ₑ ^ 2 + 1) ∂(bilinearKernel Γ θ b ^ n : Kernel ℝ ℝ) x ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top
      enorm_ne_top, ENNReal.one_ne_top⟩, ENNReal.mul_ne_top hc (ENNReal.natCast_ne_top n)⟩)
      (hdrift.pow_le hVm hρ1.le hCm n x)
  refine ofReal_abs_integral_sub_le_fNorm ⟨measurable_id.pow_const 2, fun y => ?_, hint _ hPn,
    hint _ hπV⟩
  rw [abs_of_nonneg (sq_nonneg y), ← sq_abs, ENNReal.ofReal_pow (abs_nonneg y),
    ← Real.enorm_eq_ofReal_abs]
  exact le_self_add

/-- The simple linear model `Xₙ₊₁ = αXₙ + Wₙ₊₁` is the bilinear model with `b = 0`. -/
theorem ar1Kernel_eq_bilinearKernel (Γ : Measure ℝ) (α : ℝ) :
    ar1Kernel Γ α = bilinearKernel Γ α 0 := by
  rw [ar1Kernel, bilinearKernel]
  congr 1
  funext q
  rw [bilinearStep_eq]
  ring

/-- **(15.49)** (MT p. 389): for the simple linear model and `V(x) = |x| + 1`,
`E_x[V(X₁)] ≤ |α| V(x) + E|W| + 1`. -/
theorem ar1_eq_15_49 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (α x : ℝ) :
    ∫⁻ y, (‖y‖ₑ + 1) ∂ar1Kernel Γ α x ≤ ‖α‖ₑ * (‖x‖ₑ + 1) + (∫⁻ w, ‖w‖ₑ ∂Γ + 1) := by
  have := isMarkovKernel_bilinearKernel Γ α 0
  have h := bilinear_eq_15_51 Γ α 0 x
  simp only [zero_mul, add_zero, lintegral_const, measure_univ, mul_one] at h
  rw [ar1Kernel_eq_bilinearKernel, lintegral_add_left measurable_enorm, lintegral_const,
    measure_univ, mul_one]
  calc ∫⁻ y, ‖y‖ₑ ∂bilinearKernel Γ α 0 x + 1 ≤ ‖α‖ₑ * ‖x‖ₑ + ∫⁻ w, ‖w‖ₑ ∂Γ + 1 :=
        add_le_add h le_rfl
    _ ≤ _ := by
        rw [add_assoc]
        exact add_le_add (mul_le_mul' le_rfl le_self_add) le_rfl

/-- **The simple linear model is geometrically ergodic** (MT p. 389): if `E|W| < ∞` and
`|α| < 1`, and the chain is `ψ`-irreducible and aperiodic with compact sets petite (the book
obtains these from an everywhere positive density of `W`), then `V(x) = |x| + 1` satisfies (V4)
for a petite set, the chain is positive, `π(V) < ∞`, and `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_V ≤ R V(x)`. -/
theorem ar1_geometricErgodic (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ}
    (hW : ∫⁻ w, ‖w‖ₑ ∂Γ ≠ ∞) (hα : |α| < 1) {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_ar1Kernel Γ α; IsMaximalIrreducibility (ar1Kernel Γ α) ψ)
    (hap : IsAperiodic (ar1Kernel Γ α) ψ)
    (hcpt : ∀ K : Set ℝ, IsCompact K → IsPetite (ar1Kernel Γ α) K) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    (∃ ρ c : ℝ≥0∞, ρ < 1 ∧ c ≠ ∞ ∧ ∃ C, IsPetite (ar1Kernel Γ α) C ∧
      DriftV4 (ar1Kernel Γ α) (fun x => ‖x‖ₑ ^ 1 + 1) ρ c C) ∧
      IsPositive (ar1Kernel Γ α) ψ ∧
      ∀ (π : Measure ℝ) [IsProbabilityMeasure π], IsInvariant (ar1Kernel Γ α) π →
        ∫⁻ x, (‖x‖ₑ ^ 1 + 1) ∂π ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
          ∑' n, r ^ n * fNorm (fun x : ℝ => ‖x‖ₑ ^ 1 + 1)
            ((ar1Kernel Γ α ^ n : Kernel ℝ ℝ) x) π ≤ R * (‖x‖ₑ ^ 1 + 1) := by
  simp only [ar1Kernel_eq_bilinearKernel] at hψ hap hcpt ⊢
  refine bilinear_geometricErgodic Γ α 0 le_rfl (by simpa using hW) ?_ hψ hap hcpt
  simp only [zero_mul, add_zero, pow_one, lintegral_const, measure_univ, mul_one]
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_lt_one]
  exact hα

end MeynTweedie.LimitTheorems

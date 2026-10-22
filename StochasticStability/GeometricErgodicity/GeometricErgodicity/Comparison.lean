/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeometricErgodicity.AtomInvariant
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Centering

/-!
# Dynkin's formula and the comparison theorem (MT §11.3.1, Lemma 11.3.10)

Copied for Chapter 13 from the Chapter 11 project
(`DriftRegularity/Comparison.lean`), with the namespace changed to
`MeynTweedie.GeometricErgodicity` and the imports to this project's modules.

Meyn and Tweedie, §11.3.1, pp. 263–267, and Lemma 11.3.10, p. 269. This module is the
infrastructure for Chapters 11 and 14–16: the drift inequalities are turned into bounds on sums
along the path up to a stopping time.

**Sums up to a random time.** For `τ : Ω → ℕ ∪ {∞}` and `F : ℕ → Ω → [0, ∞]`,
`sumBefore τ F ω = Σ_{k < τ(ω)} F_k(ω)`; `lintegral_sumBefore`:
`∫ Σ_{k<τ} F_k = Σ_k ∫_{k<τ} F_k`; `toENNReal_eq_sumBefore_one`: `τ = Σ_{k<τ} 1`;
monotonicity and congruence lemmas (`sumBefore_mono`, `sumBefore_mono_time`,
`sumBefore_mono_before`, `sumBefore_congr`, `sumBefore_eq_of_eq`, `sumBefore_const_mul`).

**Results.**
* `comparison_partial`, `comparison_lintegral`: the core of the comparison theorem on an arbitrary
  measure space. If `∫_{n<τ} Z_{n+1} + ∫_{n<τ} F_n ≤ ∫_{n<τ} Z_n + ∫_{n<τ} S_n` for all `n`,
  then `∫ Σ_{k<τ} F_k ≤ ∫ Z_0 + ∫ Σ_{k<τ} S_k`. Everything is in `[0, ∞]`, so no integrability
  is needed and no truncation of `τ` or of `Z` (the book's `τⁿ`) is used.
* **Theorem 11.3.1** (Dynkin's formula, `theorem_11_3_1`, p. 264): for an adapted integrable real
  process `Z` and a bounded stopping time `τ`,
  `E[Z_τ] = E[Z_0] + E[Σ_{i<τ} (E[Z_{i+1} | 𝓕_i] − Z_i)]`; proved through the Doob decomposition
  and the optional stopping theorem of Mathlib.
* **Proposition 11.3.2** (`proposition_11_3_2`, p. 265): if
  `E[Z_{k+1} | 𝓕_k] ≤ Z_k − f_k(Φ_k) + s_k(Φ_k)` (in the integrated form: on every event of
  `𝓕_k`), then `E[Σ_{k<τ} f_k(Φ_k)] ≤ E[Z_0] + E[Σ_{k<τ} s_k(Φ_k)]` for every stopping time
  `τ`; `proposition_11_3_2_condExp` takes the hypothesis as an inequality of conditional
  expectations of real processes.
* `comparison_theorem` (the form used in Chapters 11 and 14–16): for a Markov chain, if
  `PV_{k+1} + f_k ≤ V_k + s_k` on a set `D` and the chain stays in `D` before `τ`, then
  `E_μ[Σ_{k<τ} f_k(Φ_k)] ≤ μ(V_0) + E_μ[Σ_{k<τ} s_k(Φ_k)]`; `comparison_theorem_pathKernel` is the
  time-homogeneous form from a point, `E_x[Σ_{k<τ} f(Φ_k)] ≤ V(x) + E_x[Σ_{k<τ} s(Φ_k)]` when
  `PV + f ≤ V + s`.
* Restarting at time one: `le_firstHit_iff`, `notMem_of_lt_firstHit`,
  `firstReturn_eq_firstHit_shift` (`τ_A = 1 + σ_A ∘ θ`), `sumBefore_firstReturn`, and the Markov
  property at time one, `lintegral_shift_one`; `lintegral_coord_zero`.
* **Proposition 11.3.3** (`proposition_11_3_3`, p. 266): if `ε_{k+1} ≤ c ε_k` and
  `P z_{k+1} + ε_k ≤ z_k` off `A`, then `E_x[Σ_{i<τ_A} ε_i(Φ_i)] ≤ z_0(x)` for `x ∉ A`, and
  `≤ ε_0(x) + c P z_0(x)` for every `x`; `lintegral_sumBefore_firstHit_le` is the hitting-time
  form.
* **Lemma 11.3.10** (`lemma_11_3_10`, p. 269): `E_x[Σ_{k<τ} K_a(Φ_k, f)] = Σᵢ a(i)
  E_x[Σ_{k<τ} f(Φ_{k+i})]` for every stopping time `τ` (`setLIntegral_pow_coord`,
  `lintegral_sampledKernel_eq`).

**Hypotheses.** Proposition 11.3.3 is stated for processes `Z_k = z_k(Φ_k)` that are functions of
the current state (the case used in the book, with `z_k = V` or `z_k = r^k V`): the book's proof of
the second bound restarts the chain at time `1`, which needs this form. Dynkin's formula is
stated for bounded stopping times and integrable `Z`, which is what the book's truncation `τⁿ`
achieves. Lemma 11.3.10 holds for every stopping time and every weight sequence `a`.

**Corrections.** None.
-/

namespace MeynTweedie.GeometricErgodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-! ### Sums before a random time -/

/-- `Σ_{k < τ(ω)} F_k(ω)`, the sum of a nonnegative process strictly before the random time
`τ` (`τ = ∞` allowed). -/
noncomputable def sumBefore {Ω : Type*} (τ : Ω → WithTop ℕ) (F : ℕ → Ω → ℝ≥0∞) (ω : Ω) :
    ℝ≥0∞ :=
  ∑' k : ℕ, {ω | (k : WithTop ℕ) < τ ω}.indicator (F k) ω

/-- `Σ_{k<τ} F_k` is measurable. -/
theorem measurable_sumBefore {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → WithTop ℕ}
    (hτ : ∀ n : ℕ, MeasurableSet {ω | (n : WithTop ℕ) < τ ω}) {F : ℕ → Ω → ℝ≥0∞}
    (hF : ∀ n, Measurable (F n)) : Measurable (sumBefore τ F) :=
  Measurable.tsum fun n : ℕ => (hF n).indicator (hτ n)

/-- `∫ Σ_{k<τ} F_k = Σ_k ∫_{k<τ} F_k`. -/
theorem lintegral_sumBefore {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {τ : Ω → WithTop ℕ} (hτ : ∀ n : ℕ, MeasurableSet {ω | (n : WithTop ℕ) < τ ω})
    {F : ℕ → Ω → ℝ≥0∞} (hF : ∀ n, Measurable (F n)) :
    ∫⁻ ω, sumBefore τ F ω ∂μ = ∑' n : ℕ, ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, F n ω ∂μ := by
  unfold sumBefore
  rw [lintegral_tsum fun n => ((hF n).indicator (hτ n)).aemeasurable]
  exact tsum_congr fun n : ℕ => lintegral_indicator (hτ n) _

/-- `Σ_{k<τ} F_k` is monotone in `F`. -/
theorem sumBefore_mono {Ω : Type*} (τ : Ω → WithTop ℕ) {F G : ℕ → Ω → ℝ≥0∞}
    (h : ∀ k ω, F k ω ≤ G k ω) (ω : Ω) : sumBefore τ F ω ≤ sumBefore τ G ω :=
  ENNReal.tsum_le_tsum fun k : ℕ => indicator_le_indicator (h k ω)

/-- `Σ_{k<τ} F_k` is monotone in `τ`. -/
theorem sumBefore_mono_time {Ω : Type*} {τ τ' : Ω → WithTop ℕ} (h : ∀ ω, τ ω ≤ τ' ω)
    (F : ℕ → Ω → ℝ≥0∞) (ω : Ω) : sumBefore τ F ω ≤ sumBefore τ' F ω :=
  ENNReal.tsum_le_tsum fun _ => indicator_le_indicator_of_subset
    (fun _ hω => lt_of_lt_of_le hω (h _)) (fun _ => zero_le) ω

/-- `Σ_{k<τ} F_k ≤ Σ_{k<τ} G_k` when `F_k ≤ G_k` for `k < τ`. -/
theorem sumBefore_mono_before {Ω : Type*} (τ : Ω → WithTop ℕ) {F G : ℕ → Ω → ℝ≥0∞} {ω : Ω}
    (h : ∀ k : ℕ, (k : WithTop ℕ) < τ ω → F k ω ≤ G k ω) :
    sumBefore τ F ω ≤ sumBefore τ G ω := by
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : (k : WithTop ℕ) < τ ω
  · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ ω} from hk),
      indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ ω} from hk)]
    exact h k hk
  · rw [indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < τ ω} from hk)]
    exact zero_le

/-- `Σ_{k<τ} F_k` at `ω` only depends on `τ(ω)`. -/
theorem sumBefore_eq_of_eq {Ω : Type*} {τ τ' : Ω → WithTop ℕ} {ω : Ω} (h : τ ω = τ' ω)
    (F : ℕ → Ω → ℝ≥0∞) : sumBefore τ F ω = sumBefore τ' F ω := by
  unfold sumBefore
  simp only [Set.indicator_apply, mem_ofPred_eq, h]

/-- `Σ_{k<τ} F_k` only sees `F_k` for `k < τ`. -/
theorem sumBefore_congr {Ω : Type*} (τ : Ω → WithTop ℕ) {F G : ℕ → Ω → ℝ≥0∞} {ω : Ω}
    (h : ∀ k : ℕ, (k : WithTop ℕ) < τ ω → F k ω = G k ω) :
    sumBefore τ F ω = sumBefore τ G ω := by
  unfold sumBefore
  refine tsum_congr fun k : ℕ => ?_
  by_cases hk : (k : WithTop ℕ) < τ ω
  · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ ω} from hk),
      indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ ω} from hk), h k hk]
  · rw [indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < τ ω} from hk),
      indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < τ ω} from hk)]

/-- `τ = Σ_{k<τ} 1` in `[0, ∞]`. -/
theorem toENNReal_eq_sumBefore_one {Ω : Type*} (τ : Ω → WithTop ℕ) (ω : Ω) :
    ENat.toENNReal (τ ω) = sumBefore τ (fun _ _ => 1) ω := by
  rw [coe_eq_tsum_le, sumBefore]
  refine tsum_congr fun n : ℕ => ?_
  have hiff : WithTop.some (n + 1) ≤ τ ω ↔ (n : WithTop ℕ) < τ ω := by
    cases h : τ ω with
    | top => simp
    | coe m =>
      change ((n + 1 : ℕ) : WithTop ℕ) ≤ (m : WithTop ℕ) ↔ (n : WithTop ℕ) < (m : WithTop ℕ)
      norm_cast
  by_cases hn : (n : WithTop ℕ) < τ ω
  · rw [indicator_of_mem (show n ∈ {n : ℕ | WithTop.some (n + 1) ≤ τ ω} from hiff.2 hn),
      indicator_of_mem (show ω ∈ {ω | (n : WithTop ℕ) < τ ω} from hn)]
    rfl
  · rw [indicator_of_notMem (show n ∉ {n : ℕ | WithTop.some (n + 1) ≤ τ ω} from
      fun h => hn (hiff.1 h)), indicator_of_notMem (show ω ∉ {ω | (n : WithTop ℕ) < τ ω} from hn)]

/-- For a stopping time, `{n < τ} ∈ 𝓕ₙ`. -/
theorem measurableSet_lt_of_isStoppingTime {Ω : Type*} {m0 : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m0} {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) (n : ℕ) :
    MeasurableSet[ℱ n] {ω | (n : WithTop ℕ) < τ ω} := by
  have : {ω | (n : WithTop ℕ) < τ ω} = {ω | τ ω ≤ n}ᶜ := by ext ω; simp
  rw [this]
  exact (hτ n).compl

/-- `ω ↦ τ(ω)` is measurable into `[0, ∞]` when every `{n < τ}` is an event. -/
theorem measurable_toENNReal {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → WithTop ℕ}
    (hτ : ∀ n : ℕ, MeasurableSet {ω | (n : WithTop ℕ) < τ ω}) :
    Measurable fun ω => ENat.toENNReal (τ ω) := by
  simp_rw [toENNReal_eq_sumBefore_one τ]
  exact measurable_sumBefore hτ fun _ => measurable_const

/-! ### The comparison theorem on a measure space -/

/-- **The finite-horizon comparison inequality.** If
`∫_{n<τ} Z_{n+1} + ∫_{n<τ} F_n ≤ ∫_{n<τ} Z_n + ∫_{n<τ} S_n` for every `n`, then for every `N`,
`∫_{N<τ} Z_N + Σ_{n<N} ∫_{n<τ} F_n ≤ ∫_{0<τ} Z_0 + Σ_{n<N} ∫_{n<τ} S_n`. -/
theorem comparison_partial {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {τ : Ω → WithTop ℕ} {Z F S : ℕ → Ω → ℝ≥0∞}
    (hstep : ∀ n : ℕ, ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, Z (n + 1) ω ∂μ +
        ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, F n ω ∂μ ≤
      ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, Z n ω ∂μ +
        ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, S n ω ∂μ) (N : ℕ) :
    ∫⁻ ω in {ω | (N : WithTop ℕ) < τ ω}, Z N ω ∂μ +
        ∑ n ∈ Finset.range N, ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, F n ω ∂μ ≤
      ∫⁻ ω in {ω | ((0 : ℕ) : WithTop ℕ) < τ ω}, Z 0 ω ∂μ +
        ∑ n ∈ Finset.range N, ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, S n ω ∂μ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hsub : {ω | ((N + 1 : ℕ) : WithTop ℕ) < τ ω} ⊆ {ω | (N : WithTop ℕ) < τ ω} :=
      fun ω (h : ((N + 1 : ℕ) : WithTop ℕ) < τ ω) =>
        show (N : WithTop ℕ) < τ ω from lt_of_le_of_lt (by exact_mod_cast Nat.le_succ N) h
    have hmono : ∫⁻ ω in {ω | ((N + 1 : ℕ) : WithTop ℕ) < τ ω}, Z (N + 1) ω ∂μ ≤
        ∫⁻ ω in {ω | (N : WithTop ℕ) < τ ω}, Z (N + 1) ω ∂μ := lintegral_mono_set hsub
    set a := ∫⁻ ω in {ω | ((N + 1 : ℕ) : WithTop ℕ) < τ ω}, Z (N + 1) ω ∂μ
    set a' := ∫⁻ ω in {ω | (N : WithTop ℕ) < τ ω}, Z (N + 1) ω ∂μ
    set fN := ∫⁻ ω in {ω | (N : WithTop ℕ) < τ ω}, F N ω ∂μ
    set sN := ∫⁻ ω in {ω | (N : WithTop ℕ) < τ ω}, S N ω ∂μ
    set zN := ∫⁻ ω in {ω | (N : WithTop ℕ) < τ ω}, Z N ω ∂μ
    set sF := ∑ n ∈ Finset.range N, ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, F n ω ∂μ
    set sS := ∑ n ∈ Finset.range N, ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, S n ω ∂μ
    set z0 := ∫⁻ ω in {ω | ((0 : ℕ) : WithTop ℕ) < τ ω}, Z 0 ω ∂μ
    have h1 : a' + fN ≤ zN + sN := hstep N
    calc a + (sF + fN) ≤ a' + (sF + fN) := add_le_add_left hmono _
      _ = (a' + fN) + sF := by ring
      _ ≤ (zN + sN) + sF := add_le_add_left h1 _
      _ = (zN + sF) + sN := by ring
      _ ≤ (z0 + sS) + sN := add_le_add_left ih _
      _ = z0 + (sS + sN) := by ring

/-- **The comparison theorem on a measure space** (the core of MT Proposition 11.3.2). If
`∫_{n<τ} Z_{n+1} + ∫_{n<τ} F_n ≤ ∫_{n<τ} Z_n + ∫_{n<τ} S_n` for every `n`, then
`∫ Σ_{k<τ} F_k ≤ ∫ Z_0 + ∫ Σ_{k<τ} S_k`. -/
theorem comparison_lintegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {τ : Ω → WithTop ℕ} (hτ : ∀ n : ℕ, MeasurableSet {ω | (n : WithTop ℕ) < τ ω})
    {Z F S : ℕ → Ω → ℝ≥0∞} (hF : ∀ n, Measurable (F n)) (hS : ∀ n, Measurable (S n))
    (hstep : ∀ n : ℕ, ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, Z (n + 1) ω ∂μ +
        ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, F n ω ∂μ ≤
      ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, Z n ω ∂μ +
        ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, S n ω ∂μ) :
    ∫⁻ ω, sumBefore τ F ω ∂μ ≤ ∫⁻ ω, Z 0 ω ∂μ + ∫⁻ ω, sumBefore τ S ω ∂μ := by
  rw [lintegral_sumBefore μ hτ hF, lintegral_sumBefore μ hτ hS, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  calc ∑ n ∈ Finset.range N, ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, F n ω ∂μ
      ≤ ∫⁻ ω in {ω | (N : WithTop ℕ) < τ ω}, Z N ω ∂μ +
        ∑ n ∈ Finset.range N, ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω}, F n ω ∂μ := le_add_self
    _ ≤ _ := comparison_partial μ hstep N
    _ ≤ _ := add_le_add (setLIntegral_le_lintegral _ _) (ENNReal.sum_le_tsum _)

/-! ### Dynkin's formula -/

/-- **Theorem 11.3.1** (Dynkin's formula, MT p. 264). For an adapted process `Z` of integrable
real random variables and a bounded stopping time `τ`,
`E[Z_τ] = E[Z_0] + E[Σ_{i<τ} (E[Z_{i+1} | 𝓕_i] − Z_i)]`. -/
theorem theorem_11_3_1 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m0) {Z : ℕ → Ω → ℝ} (hZ : StronglyAdapted ℱ Z)
    (hint : ∀ n, Integrable (Z n) μ) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) {N : ℕ}
    (hN : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue Z τ ω ∂μ = ∫ ω, Z 0 ω ∂μ +
      ∫ ω, ∑ i ∈ Finset.range (τ ω).untopA, (μ[Z (i + 1) | ℱ i] ω - Z i ω) ∂μ := by
  set M := martingalePart Z ℱ μ with hMdef
  set A := predictablePart Z ℱ μ with hAdef
  have hM : Martingale M ℱ μ := martingale_martingalePart hZ hint
  have hMA : ∀ n ω, Z n ω = M n ω + A n ω := fun n ω => by
    have := congrFun (congrFun (martingalePart_add_predictablePart ℱ μ Z) n) ω
    simpa using this.symm
  have hdecomp : stoppedValue Z τ = fun ω => stoppedValue M τ ω + stoppedValue A τ ω := by
    funext ω; exact hMA _ ω
  have hAint : ∀ n, Integrable (A n) μ := fun n => by
    simp only [hAdef, predictablePart]
    exact integrable_finsetSum' _ fun i _ => integrable_condExp
  have hMint : ∀ n, Integrable (M n) μ := integrable_martingalePart hint
  have hsvM := integrable_stoppedValue ℕ hτ hMint hN
  have hsvA := integrable_stoppedValue ℕ hτ hAint hN
  -- `E[M_τ] = E[M_0] = E[Z_0]` by optional stopping
  have h0 : IsStoppingTime ℱ (fun _ => ((0 : ℕ) : WithTop ℕ)) := isStoppingTime_const ℱ 0
  have hle : (fun _ => ((0 : ℕ) : WithTop ℕ)) ≤ τ := fun ω => by simp
  have e1 := hM.submartingale.expected_stoppedValue_mono h0 hτ hle hN
  have e2 := hM.neg.submartingale.expected_stoppedValue_mono h0 hτ hle hN
  have hneg : ∀ σ : Ω → WithTop ℕ, stoppedValue (-M) σ = fun ω => -stoppedValue M σ ω :=
    fun σ => rfl
  rw [hneg, hneg, integral_neg, integral_neg, neg_le_neg_iff] at e2
  have hMτ : ∫ ω, stoppedValue M τ ω ∂μ = ∫ ω, Z 0 ω ∂μ := by
    have h00 : stoppedValue M (fun _ => ((0 : ℕ) : WithTop ℕ)) = Z 0 := by
      funext ω
      simp [stoppedValue, hMdef]
    rw [h00] at e1 e2
    exact le_antisymm e2 e1
  -- `E[A_τ]` is the expected sum of the predictable increments
  have hAτ : ∫ ω, stoppedValue A τ ω ∂μ =
      ∫ ω, ∑ i ∈ Finset.range (τ ω).untopA, (μ[Z (i + 1) | ℱ i] ω - Z i ω) ∂μ := by
    refine integral_congr_ae ?_
    have hae : ∀ᵐ ω ∂μ, ∀ i : ℕ, μ[Z (i + 1) - Z i | ℱ i] ω = μ[Z (i + 1) | ℱ i] ω - Z i ω := by
      rw [ae_all_iff]
      intro i
      filter_upwards [condExp_sub (hint (i + 1)) (hint i) (ℱ i)] with ω hω
      rw [hω, Pi.sub_apply, condExp_of_stronglyMeasurable (ℱ.le i) (hZ i) (hint i)]
    filter_upwards [hae] with ω hω
    simp only [stoppedValue, hAdef, predictablePart, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hω i
  rw [hdecomp, integral_add hsvM hsvA, hMτ, hAτ]

/-! ### Proposition 11.3.2 -/

variable {X : Type*} [MeasurableSpace X]

/-- **Proposition 11.3.2** (MT p. 265). Let `Φ` be adapted to a filtration `𝓕`, `τ` a stopping
time, `Z_k ≥ 0` a process and `f_k, s_k ≥ 0` measurable functions with
`E[Z_{k+1} | 𝓕_k] ≤ Z_k − f_k(Φ_k) + s_k(Φ_k)`, in the integrated form
`∫_G Z_{k+1} + ∫_G f_k(Φ_k) ≤ ∫_G Z_k + ∫_G s_k(Φ_k)` for `G ∈ 𝓕_k`. Then
`E[Σ_{k<τ} f_k(Φ_k)] ≤ E[Z_0] + E[Σ_{k<τ} s_k(Φ_k)]`. -/
theorem proposition_11_3_2 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) {Φ : ℕ → Ω → X} (hΦ : ∀ k, Measurable (Φ k))
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) {Z : ℕ → Ω → ℝ≥0∞} {f s : ℕ → X → ℝ≥0∞}
    (hf : ∀ k, Measurable (f k)) (hs : ∀ k, Measurable (s k))
    (hdrift : ∀ k (G : Set Ω), MeasurableSet[ℱ k] G →
      ∫⁻ ω in G, Z (k + 1) ω ∂μ + ∫⁻ ω in G, f k (Φ k ω) ∂μ ≤
        ∫⁻ ω in G, Z k ω ∂μ + ∫⁻ ω in G, s k (Φ k ω) ∂μ) :
    ∫⁻ ω, sumBefore τ (fun k ω => f k (Φ k ω)) ω ∂μ ≤
      ∫⁻ ω, Z 0 ω ∂μ + ∫⁻ ω, sumBefore τ (fun k ω => s k (Φ k ω)) ω ∂μ :=
  comparison_lintegral μ (fun n => ℱ.le n _ (measurableSet_lt_of_isStoppingTime hτ n))
    (F := fun k ω => f k (Φ k ω)) (S := fun k ω => s k (Φ k ω)) (fun k => (hf k).comp (hΦ k))
    (fun k => (hs k).comp (hΦ k))
    fun n => hdrift n _ (measurableSet_lt_of_isStoppingTime hτ n)

/-- `∫_G ofReal g = ofReal (∫_G g)` for a nonnegative integrable `g`. -/
theorem setLIntegral_ofReal_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → ℝ}
    (hg : Integrable g μ) (h0 : ∀ ω, 0 ≤ g ω) (G : Set Ω) :
    ∫⁻ ω in G, ENNReal.ofReal (g ω) ∂μ = ENNReal.ofReal (∫ ω in G, g ω ∂μ) :=
  (ofReal_integral_eq_lintegral_ofReal hg.integrableOn (Eventually.of_forall h0)).symm

/-- **Proposition 11.3.2**, with the hypothesis as an inequality of conditional expectations
(MT p. 265): for nonnegative integrable real processes with `Z` adapted and
`E[Z_{k+1} | 𝓕_k] ≤ Z_k − f_k(Φ_k) + s_k(Φ_k)` almost surely,
`E[Σ_{k<τ} f_k(Φ_k)] ≤ E[Z_0] + E[Σ_{k<τ} s_k(Φ_k)]` for every stopping time `τ`. -/
theorem proposition_11_3_2_condExp {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {Φ : ℕ → Ω → X} (hΦ : ∀ k, Measurable (Φ k))
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) {Z : ℕ → Ω → ℝ} {f s : ℕ → X → ℝ}
    (hZ0 : ∀ k ω, 0 ≤ Z k ω) (hf0 : ∀ k x, 0 ≤ f k x) (hs0 : ∀ k x, 0 ≤ s k x)
    (hZi : ∀ k, Integrable (Z k) μ) (hf : ∀ k, Measurable (f k)) (hs : ∀ k, Measurable (s k))
    (hfi : ∀ k, Integrable (fun ω => f k (Φ k ω)) μ)
    (hsi : ∀ k, Integrable (fun ω => s k (Φ k ω)) μ)
    (hdrift : ∀ k, μ[Z (k + 1) | ℱ k] ≤ᵐ[μ] fun ω => Z k ω - f k (Φ k ω) + s k (Φ k ω)) :
    ∫⁻ ω, sumBefore τ (fun k ω => ENNReal.ofReal (f k (Φ k ω))) ω ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (Z 0 ω) ∂μ +
        ∫⁻ ω, sumBefore τ (fun k ω => ENNReal.ofReal (s k (Φ k ω))) ω ∂μ := by
  refine proposition_11_3_2 μ ℱ hΦ hτ (Z := fun k ω => ENNReal.ofReal (Z k ω))
    (f := fun k x => ENNReal.ofReal (f k x)) (s := fun k x => ENNReal.ofReal (s k x))
    (fun k => ENNReal.measurable_ofReal.comp (hf k))
    (fun k => ENNReal.measurable_ofReal.comp (hs k)) fun k G hG => ?_
  have hreal : ∫ ω in G, Z (k + 1) ω ∂μ + ∫ ω in G, f k (Φ k ω) ∂μ ≤
      ∫ ω in G, Z k ω ∂μ + ∫ ω in G, s k (Φ k ω) ∂μ := by
    have h1 : ∫ ω in G, Z (k + 1) ω ∂μ = ∫ ω in G, (μ[Z (k + 1) | ℱ k]) ω ∂μ :=
      (setIntegral_condExp (ℱ.le k) (hZi (k + 1)) hG).symm
    have h2 : ∫ ω in G, (μ[Z (k + 1) | ℱ k]) ω ∂μ ≤
        ∫ ω in G, (Z k ω - f k (Φ k ω) + s k (Φ k ω)) ∂μ :=
      setIntegral_mono_ae integrable_condExp.integrableOn
        (((hZi k).sub (hfi k)).add (hsi k)).integrableOn (hdrift k)
    have h3 : ∫ ω in G, (Z k ω - f k (Φ k ω) + s k (Φ k ω)) ∂μ =
        ∫ ω in G, Z k ω ∂μ - ∫ ω in G, f k (Φ k ω) ∂μ + ∫ ω in G, s k (Φ k ω) ∂μ := by
      rw [integral_add (f := fun ω => Z k ω - f k (Φ k ω)) (g := fun ω => s k (Φ k ω))
        ((hZi k).sub (hfi k)).integrableOn (hsi k).integrableOn,
        integral_sub (f := fun ω => Z k ω) (g := fun ω => f k (Φ k ω)) (hZi k).integrableOn
          (hfi k).integrableOn]
    linarith
  rw [setLIntegral_ofReal_eq (hZi (k + 1)) (hZ0 (k + 1)), setLIntegral_ofReal_eq (hfi k)
      (fun ω => hf0 k _), setLIntegral_ofReal_eq (hZi k) (hZ0 k),
    setLIntegral_ofReal_eq (hsi k) (fun ω => hs0 k _),
    ← ENNReal.ofReal_add (setIntegral_nonneg_of_ae (Eventually.of_forall (hZ0 (k + 1))))
      (setIntegral_nonneg_of_ae (Eventually.of_forall fun ω => hf0 k _)),
    ← ENNReal.ofReal_add (setIntegral_nonneg_of_ae (Eventually.of_forall (hZ0 k)))
      (setIntegral_nonneg_of_ae (Eventually.of_forall fun ω => hs0 k _))]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ### The comparison theorem for Markov chains -/

/-- **The comparison theorem.** For a Markov chain started with law `μ`, let `V_k, f_k, s_k ≥ 0`
be measurable with `PV_{k+1} + f_k ≤ V_k + s_k` on a set `D` (the drift inequality
`PV_{k+1} ≤ V_k − f_k + s_k`), and let `τ` be a stopping time before which the chain stays in
`D`. Then `E_μ[Σ_{k<τ} f_k(Φ_k)] ≤ μ(V_0) + E_μ[Σ_{k<τ} s_k(Φ_k)]`. -/
theorem comparison_theorem (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {V f s : ℕ → X → ℝ≥0∞} (hV : ∀ k, Measurable (V k))
    (hf : ∀ k, Measurable (f k)) (hs : ∀ k, Measurable (s k)) {D : Set X}
    (hdrift : ∀ k, ∀ x ∈ D, ∫⁻ y, V (k + 1) y ∂P x + f k x ≤ V k x + s k x)
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (natFilt (X := X)) τ)
    (hτD : ∀ ω (k : ℕ), (k : WithTop ℕ) < τ ω → ω k ∈ D) :
    ∫⁻ ω, sumBefore τ (fun k ω => f k (ω k)) ω ∂pathMeasure P μ ≤
      ∫⁻ x, V 0 x ∂μ + ∫⁻ ω, sumBefore τ (fun k ω => s k (ω k)) ω ∂pathMeasure P μ := by
  have hGk := measurableSet_lt_of_isStoppingTime hτ
  have hG : ∀ n : ℕ, MeasurableSet {ω | (n : WithTop ℕ) < τ ω} :=
    fun n => (natFilt (X := X)).le n _ (hGk n)
  have h := comparison_lintegral (pathMeasure P μ) hG (Z := fun k ω => V k (ω k))
    (F := fun k ω => f k (ω k)) (S := fun k ω => s k (ω k))
    (fun k => (hf k).comp (measurable_pi_apply k)) (fun k => (hs k).comp (measurable_pi_apply k))
    fun n => by
      have hPV : Measurable fun y => ∫⁻ z, V (n + 1) z ∂P y := (hV (n + 1)).lintegral_kernel
      have hc := measurable_pi_apply (X := fun _ : ℕ => X) n
      rw [setLIntegral_succ P μ (hGk n) (hV (n + 1)),
        ← lintegral_add_left (f := fun ω : ℕ → X => ∫⁻ z, V (n + 1) z ∂P (ω n)) (hPV.comp hc),
        ← lintegral_add_left (f := fun ω : ℕ → X => V n (ω n)) ((hV n).comp hc)]
      exact setLIntegral_mono' (hG n) fun ω hω => hdrift n (ω n) (hτD ω n hω)
  have h0 : ∫⁻ ω, V 0 (ω 0) ∂pathMeasure P μ = ∫⁻ x, V 0 x ∂μ := by
    rw [← lintegral_map (hV 0) (measurable_pi_apply 0), pathMeasure_map_zero]
  rwa [h0] at h

/-- `∫ g(Φ₀) dP_x = g(x)`. -/
theorem lintegral_coord_zero (P : Kernel X X) [IsMarkovKernel P] (x : X) {g : X → ℝ≥0∞}
    (hg : Measurable g) : ∫⁻ ω, g (ω 0) ∂pathKernel P x = g x := by
  rw [← lintegral_map hg (measurable_pi_apply 0), pathKernel_map_zero, lintegral_dirac' _ hg]

/-- **The comparison theorem** from a point, time-homogeneous form: if `PV + f ≤ V + s` on `D`
and the chain stays in `D` before `τ`, then `E_x[Σ_{k<τ} f(Φ_k)] ≤ V(x) + E_x[Σ_{k<τ} s(Φ_k)]`. -/
theorem comparison_theorem_pathKernel (P : Kernel X X) [IsMarkovKernel P] {V f s : X → ℝ≥0∞}
    (hV : Measurable V) (hf : Measurable f) (hs : Measurable s) {D : Set X}
    (hdrift : ∀ x ∈ D, ∫⁻ y, V y ∂P x + f x ≤ V x + s x)
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (natFilt (X := X)) τ)
    (hτD : ∀ ω (k : ℕ), (k : WithTop ℕ) < τ ω → ω k ∈ D) (x : X) :
    ∫⁻ ω, sumBefore τ (fun k ω => f (ω k)) ω ∂pathKernel P x ≤ V x +
      ∫⁻ ω, sumBefore τ (fun k ω => s (ω k)) ω ∂pathKernel P x := by
  have h := comparison_theorem P (Measure.dirac x) (V := fun _ => V) (f := fun _ => f)
    (s := fun _ => s) (fun _ => hV) (fun _ => hf) (fun _ => hs) (fun _ => hdrift) hτ hτD
  rwa [pathMeasure_dirac, lintegral_dirac' _ hV] at h

/-! ### Restarting at time one -/

omit [MeasurableSpace X] in
/-- `n ≤ σ_A` iff the path avoids `A` at the times `0, …, n − 1`. -/
theorem le_firstHit_iff (A : Set X) (ω : ℕ → X) (n : ℕ) :
    WithTop.some n ≤ firstHit A ω ↔ ∀ j < n, ω j ∉ A := by
  rw [firstHit, ← not_lt, hittingAfter_lt_iff]
  simp only [mem_Ico, not_exists, not_and]
  exact ⟨fun h j hj hjA => h j ⟨Nat.zero_le j, hj⟩ hjA, fun h j hj => h j hj.2⟩

omit [MeasurableSpace X] in
/-- Before `σ_A` the path is outside `A`. -/
theorem notMem_of_lt_firstHit {A : Set X} {ω : ℕ → X} {k : ℕ}
    (hk : (k : WithTop ℕ) < firstHit A ω) : ω k ∉ A := by
  have h1 : WithTop.some (k + 1) ≤ firstHit A ω := by
    cases h : firstHit A ω with
    | top => exact le_top
    | coe m =>
      rw [h] at hk
      rw [Nat.cast_withTop] at hk
      have : k < m := WithTop.coe_lt_coe.1 hk
      exact WithTop.coe_le_coe.2 this
  exact (le_firstHit_iff A ω (k + 1)).1 h1 k (Nat.lt_succ_self k)

omit [MeasurableSpace X] in
/-- Two elements of `ℕ ∪ {∞}` with the same natural lower bounds are equal. -/
theorem withTop_eq_of_forall_le_iff {a b : WithTop ℕ}
    (h : ∀ n : ℕ, WithTop.some n ≤ a ↔ WithTop.some n ≤ b) : a = b :=
  le_antisymm (WithTop.forall_coe_le_iff_le.1 fun n hn => (h n).1 hn)
    (WithTop.forall_coe_le_iff_le.1 fun n hn => (h n).2 hn)

omit [MeasurableSpace X] in
/-- `τ_A = 1 + σ_A ∘ θ`: the first return time is one plus the first hitting time of the path
started at time `1`. -/
theorem firstReturn_eq_firstHit_shift (A : Set X) (ω : ℕ → X) :
    firstReturn A ω = firstHit A (shift 1 ω) + 1 := by
  refine withTop_eq_of_forall_le_iff fun n => ?_
  rcases n with _ | m
  · exact ⟨fun _ => zero_le, fun _ => zero_le⟩
  · have e : WithTop.some (m + 1) = WithTop.some m + 1 := rfl
    rw [e, WithTop.add_le_add_iff_right WithTop.one_ne_top, ← e, le_firstReturn_iff,
      le_firstHit_iff]
    constructor
    · intro h j hj
      have := h (1 + j) (by omega) (by omega)
      simpa [shift] using this
    · intro h j hj1 hj
      have := h (j - 1) (by omega)
      simp only [shift] at this
      rwa [show 1 + (j - 1) = j by omega] at this

omit [MeasurableSpace X] in
/-- The sum before `τ_A`, restarted at time `1`:
`Σ_{k<τ_A} ε_k(Φ_k) = ε_0(Φ_0) + Σ_{j<σ_A ∘ θ} ε_{j+1}(Φ_{j+1})`. -/
theorem sumBefore_firstReturn (A : Set X) (ε : ℕ → X → ℝ≥0∞) (ω : ℕ → X) :
    sumBefore (firstReturn A) (fun k ω => ε k (ω k)) ω =
      ε 0 (ω 0) + sumBefore (firstHit A) (fun k ω => ε (k + 1) (ω k)) (shift 1 ω) := by
  unfold sumBefore
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine congrArg₂ (· + ·) ?_ ?_
  · have h0 : ((0 : ℕ) : WithTop ℕ) < firstReturn A ω :=
      lt_of_lt_of_le (by rw [Nat.cast_withTop]; exact WithTop.coe_lt_coe.2 one_pos)
        (one_le_firstReturn A ω)
    exact indicator_of_mem (show ω ∈ {ω | ((0 : ℕ) : WithTop ℕ) < firstReturn A ω} from h0) _
  · refine tsum_congr fun k => ?_
    have hiff : ((k + 1 : ℕ) : WithTop ℕ) < firstReturn A ω ↔
        (k : WithTop ℕ) < firstHit A (shift 1 ω) := by
      rw [firstReturn_eq_firstHit_shift, Nat.cast_succ,
        WithTop.add_lt_add_iff_right WithTop.one_ne_top]
    have hval : ω (k + 1) = shift 1 ω k := by simp [shift, add_comm]
    by_cases hk : (k : WithTop ℕ) < firstHit A (shift 1 ω)
    · rw [indicator_of_mem (show ω ∈ {ω | ((k + 1 : ℕ) : WithTop ℕ) < firstReturn A ω} from
        hiff.2 hk), indicator_of_mem (show shift 1 ω ∈ {ω | (k : WithTop ℕ) < firstHit A ω} from
        hk)]
      exact congrArg (ε (k + 1)) hval
    · rw [indicator_of_notMem (show ω ∉ {ω | ((k + 1 : ℕ) : WithTop ℕ) < firstReturn A ω} from
        fun h => hk (hiff.1 h)), indicator_of_notMem
        (show shift 1 ω ∉ {ω | (k : WithTop ℕ) < firstHit A ω} from hk)]

/-- **The Markov property at time `1`**: `E_x[H ∘ θ] = ∫ P(x, dy) E_y[H]`. -/
theorem lintegral_shift_one (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, H (shift 1 ω) ∂pathKernel P x = ∫⁻ y, ∫⁻ ω', H ω' ∂pathKernel P y ∂P x := by
  have := isMarkovKernel_pathKernel P
  rw [← pathMeasure_dirac, markov_lintegral_univ P (Measure.dirac x) 1 hH, pathMeasure_dirac,
    ← lintegral_map hH.lintegral_kernel (measurable_pi_apply 1), pathKernel_map_coord, pow_one]

/-- `σ_A` is a stopping time, so `{k < σ_A}` is an event. -/
theorem measurableSet_lt_firstHit {A : Set X} (hA : MeasurableSet A) (k : ℕ) :
    MeasurableSet {ω : ℕ → X | (k : WithTop ℕ) < firstHit A ω} :=
  (natFilt (X := X)).le k _ (measurableSet_lt_of_isStoppingTime (proposition_3_4_4 hA).2 k)

/-- `τ_A` is a stopping time, so `{k < τ_A}` is an event. -/
theorem measurableSet_lt_firstReturn {A : Set X} (hA : MeasurableSet A) (k : ℕ) :
    MeasurableSet {ω : ℕ → X | (k : WithTop ℕ) < firstReturn A ω} :=
  (natFilt (X := X)).le k _ (measurableSet_lt_of_isStoppingTime (proposition_3_4_4 hA).1 k)

/-- `Σ_{k<τ} c F_k = c Σ_{k<τ} F_k`. -/
theorem sumBefore_const_mul {Ω : Type*} (τ : Ω → WithTop ℕ) (c : ℝ≥0∞) (F : ℕ → Ω → ℝ≥0∞)
    (ω : Ω) : sumBefore τ (fun k ω => c * F k ω) ω = c * sumBefore τ F ω := by
  unfold sumBefore
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  by_cases hk : (k : WithTop ℕ) < τ ω
  · rw [indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ ω} from hk),
      indicator_of_mem (show ω ∈ {ω | (k : WithTop ℕ) < τ ω} from hk)]
  · rw [indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < τ ω} from hk),
      indicator_of_notMem (show ω ∉ {ω | (k : WithTop ℕ) < τ ω} from hk), mul_zero]

/-- The hitting-time form of the first bound of Proposition 11.3.3: if `Pz_{k+1} + ε_k ≤ z_k` off
`A`, then `E_x[Σ_{k<σ_A} ε_k(Φ_k)] ≤ z_0(x)` for every `x`. -/
theorem lintegral_sumBefore_firstHit_le (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {z ε : ℕ → X → ℝ≥0∞} (hz : ∀ k, Measurable (z k))
    (hε : ∀ k, Measurable (ε k)) (h2 : ∀ k, ∀ x ∉ A, ∫⁻ y, z (k + 1) y ∂P x + ε k x ≤ z k x)
    (x : X) :
    ∫⁻ ω, sumBefore (firstHit A) (fun k ω => ε k (ω k)) ω ∂pathKernel P x ≤ z 0 x := by
  have h := comparison_theorem P (Measure.dirac x) (s := fun _ _ => 0) hz hε
    (fun _ => measurable_const) (D := Aᶜ) (fun k y hy => by rw [add_zero]; exact h2 k y hy)
    (proposition_3_4_4 hA).2 fun ω k hk => notMem_of_lt_firstHit hk
  have h0 : ∀ ω : ℕ → X, sumBefore (firstHit A) (fun _ _ => (0 : ℝ≥0∞)) ω = 0 := fun ω => by
    simp [sumBefore]
  simp_rw [h0, lintegral_zero, add_zero, pathMeasure_dirac] at h
  rwa [lintegral_dirac' _ (hz 0)] at h

/-- **Proposition 11.3.3** (MT p. 266). Let `A` be measurable and `z_k, ε_k ≥ 0` measurable with
(i) `ε_{k+1} ≤ c ε_k` off `A`, and (ii) `P z_{k+1} + ε_k ≤ z_k` off `A` (the drift
`E[Z_{k+1} | 𝓕_k] ≤ Z_k − ε_k(Φ_k)` before `σ_A`, for `Z_k = z_k(Φ_k)`). Then
`E_x[Σ_{i<τ_A} ε_i(Φ_i)] ≤ z_0(x)` for `x ∉ A`, and `≤ ε_0(x) + c P z_0(x)` for every `x`. -/
theorem proposition_11_3_3 (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {z ε : ℕ → X → ℝ≥0∞} (hz : ∀ k, Measurable (z k))
    (hε : ∀ k, Measurable (ε k)) {c : ℝ≥0∞} (h1 : ∀ k, ∀ x ∉ A, ε (k + 1) x ≤ c * ε k x)
    (h2 : ∀ k, ∀ x ∉ A, ∫⁻ y, z (k + 1) y ∂P x + ε k x ≤ z k x) :
    (∀ x ∉ A, ∫⁻ ω, sumBefore (firstReturn A) (fun k ω => ε k (ω k)) ω ∂pathKernel P x ≤
      z 0 x) ∧
    ∀ x, ∫⁻ ω, sumBefore (firstReturn A) (fun k ω => ε k (ω k)) ω ∂pathKernel P x ≤
      ε 0 x + c * ∫⁻ y, z 0 y ∂P x := by
  have := isMarkovKernel_pathKernel P
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · -- off `A`, `τ_A = σ_A` almost surely
    have hnull : pathKernel P x {ω | ω 0 ∈ A} = 0 := by
      rw [pathKernel_zero_mem P x hA, indicator_of_notMem hx]
    have hae : (fun ω => sumBefore (firstReturn A) (fun k ω => ε k (ω k)) ω) =ᵐ[pathKernel P x]
        fun ω => sumBefore (firstHit A) (fun k ω => ε k (ω k)) ω := by
      refine measure_mono_null (fun ω hω => ?_) hnull
      by_contra h0
      apply hω
      exact sumBefore_eq_of_eq (firstHit_eq_firstReturn A (show ω 0 ∉ A from h0)).symm _
    rw [lintegral_congr_ae hae]
    exact lintegral_sumBefore_firstHit_le P hA hz hε h2 x
  · set H : (ℕ → X) → ℝ≥0∞ := sumBefore (firstHit A) (fun k ω => ε (k + 1) (ω k)) with hHdef
    have hHm : Measurable H := measurable_sumBefore (measurableSet_lt_firstHit hA)
      fun k => (hε (k + 1)).comp (measurable_pi_apply k)
    simp_rw [sumBefore_firstReturn A ε]
    rw [lintegral_add_left (f := fun ω : ℕ → X => ε 0 (ω 0)) ((hε 0).comp (measurable_pi_apply 0)),
      lintegral_coord_zero P x (hε 0), lintegral_shift_one P x hHm]
    refine add_le_add le_rfl ?_
    have key : ∀ y, ∫⁻ ω, H ω ∂pathKernel P y ≤ c * z 0 y := fun y => by
      by_cases hy : y ∈ A
      · have hm : MeasurableSet {ω : ℕ → X | ω 0 ∈ A} := measurable_pi_apply 0 hA
        have hnull : pathKernel P y {ω | ω 0 ∈ A}ᶜ = 0 := by
          rw [prob_compl_eq_zero_iff hm, pathKernel_zero_mem P y hA,
            indicator_of_mem hy, Pi.one_apply]
        have hae : H =ᵐ[pathKernel P y] fun _ => 0 := by
          refine measure_mono_null (fun ω hω => ?_) hnull
          intro h0
          apply hω
          have h00 : firstHit A ω = WithTop.some 0 := (firstHit_eq_zero_iff A ω).2 h0
          change sumBefore (firstHit A) (fun k ω => ε (k + 1) (ω k)) ω = 0
          rw [sumBefore_eq_of_eq (τ' := fun _ => WithTop.some 0) h00]
          simp [sumBefore]
        rw [lintegral_congr_ae hae, lintegral_zero]
        exact zero_le
      · have hle : ∀ ω, H ω ≤ c * sumBefore (firstHit A) (fun k ω => ε k (ω k)) ω := fun ω => by
          rw [← sumBefore_const_mul]
          exact sumBefore_mono_before _ fun k hk => h1 k (ω k) (notMem_of_lt_firstHit hk)
        calc ∫⁻ ω, H ω ∂pathKernel P y
            ≤ ∫⁻ ω, c * sumBefore (firstHit A) (fun k ω => ε k (ω k)) ω ∂pathKernel P y :=
              lintegral_mono hle
          _ = c * ∫⁻ ω, sumBefore (firstHit A) (fun k ω => ε k (ω k)) ω ∂pathKernel P y :=
              lintegral_const_mul c (measurable_sumBefore (measurableSet_lt_firstHit hA)
                fun k => (hε k).comp (measurable_pi_apply k))
          _ ≤ c * z 0 y := by
              gcongr
              exact lintegral_sumBefore_firstHit_le P hA hz hε h2 y
    calc ∫⁻ y, ∫⁻ ω, H ω ∂pathKernel P y ∂P x ≤ ∫⁻ y, c * z 0 y ∂P x := lintegral_mono key
      _ = c * ∫⁻ y, z 0 y ∂P x := lintegral_const_mul c (hz 0)

/-! ### Lemma 11.3.10 -/

/-- `K_a(y, f) = Σᵢ a(i) Pⁱf(y)`. -/
theorem lintegral_sampledKernel_eq (P : Kernel X X) (a : ℕ → ℝ≥0∞) (y : X) (f : X → ℝ≥0∞) :
    ∫⁻ z, f z ∂sampledKernel P a y = ∑' i, a i * ∫⁻ z, f z ∂(P ^ i) y := by
  change ∫⁻ z, f z ∂(Measure.sum fun n => a n • (P ^ n) y) = _
  rw [lintegral_sum_measure]
  exact tsum_congr fun i => lintegral_smul_measure _ _

/-- **The Markov property at a stopping time's predecessors**: for a stopping time `τ`,
`E_x[Pⁱf(Φ_k); k < τ] = E_x[f(Φ_{k+i}); k < τ]`. -/
theorem setLIntegral_pow_coord (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (natFilt (X := X)) τ) (k i : ℕ)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in {ω | (k : WithTop ℕ) < τ ω}, ∫⁻ z, f z ∂(P ^ i) (ω k) ∂pathKernel P x =
      ∫⁻ ω in {ω | (k : WithTop ℕ) < τ ω}, f (ω (k + i)) ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  have hH : Measurable fun ω : ℕ → X => f (ω i) := hf.comp (measurable_pi_apply i)
  have h := markov_lintegral P (Measure.dirac x) (measurableSet_lt_of_isStoppingTime hτ k) hH
  rw [pathMeasure_dirac] at h
  simp only [shift] at h
  rw [h]
  refine setLIntegral_congr_fun ((natFilt (X := X)).le k _
    (measurableSet_lt_of_isStoppingTime hτ k)) fun ω _ => ?_
  rw [← pathKernel_map_coord, lintegral_map hf (measurable_pi_apply i)]

/-- **Lemma 11.3.10** (MT p. 269). For a stopping time `τ` (in the book the first entrance time
`τ_B`), a sampling distribution `a` and measurable `f ≥ 0`,
`E_x[Σ_{k<τ} K_a(Φ_k, f)] = Σᵢ a(i) E_x[Σ_{k<τ} f(Φ_{k+i})]`. -/
theorem lemma_11_3_10 (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (natFilt (X := X)) τ) (a : ℕ → ℝ≥0∞)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, sumBefore τ (fun k ω => ∫⁻ z, f z ∂sampledKernel P a (ω k)) ω ∂pathKernel P x =
      ∑' i, a i * ∫⁻ ω, sumBefore τ (fun k ω => f (ω (k + i))) ω ∂pathKernel P x := by
  have hG : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | (n : WithTop ℕ) < τ ω} :=
    fun n => (natFilt (X := X)).le n _ (measurableSet_lt_of_isStoppingTime hτ n)
  have hKm : ∀ k, Measurable fun ω : ℕ → X => ∫⁻ z, f z ∂sampledKernel P a (ω k) :=
    fun k => hf.lintegral_kernel.comp (measurable_pi_apply k)
  have hPm : ∀ i k, Measurable fun ω : ℕ → X => ∫⁻ z, f z ∂(P ^ i) (ω k) :=
    fun i k => hf.lintegral_kernel.comp (measurable_pi_apply k)
  have hR : ∀ i, ∫⁻ ω, sumBefore τ (fun k ω => f (ω (k + i))) ω ∂pathKernel P x =
      ∑' k : ℕ, ∫⁻ ω in {ω | (k : WithTop ℕ) < τ ω}, f (ω (k + i)) ∂pathKernel P x :=
    fun i => lintegral_sumBefore _ hG (fun k => hf.comp (measurable_pi_apply (k + i)))
  rw [lintegral_sumBefore _ hG hKm]
  simp_rw [hR, lintegral_sampledKernel_eq]
  calc ∑' k : ℕ, ∫⁻ ω in {ω | (k : WithTop ℕ) < τ ω},
        ∑' i, a i * ∫⁻ z, f z ∂(P ^ i) (ω k) ∂pathKernel P x
      = ∑' k : ℕ, ∑' i, a i * ∫⁻ ω in {ω | (k : WithTop ℕ) < τ ω},
          ∫⁻ z, f z ∂(P ^ i) (ω k) ∂pathKernel P x := by
        refine tsum_congr fun k => ?_
        rw [lintegral_tsum fun i => ((hPm i k).const_mul (a i)).aemeasurable]
        exact tsum_congr fun i => lintegral_const_mul _ (hPm i k)
    _ = ∑' k : ℕ, ∑' i, a i * ∫⁻ ω in {ω | (k : WithTop ℕ) < τ ω}, f (ω (k + i))
          ∂pathKernel P x := by
        simp_rw [setLIntegral_pow_coord P x hτ _ _ hf]
    _ = _ := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun i => ENNReal.tsum_mul_left

end MeynTweedie.GeometricErgodicity

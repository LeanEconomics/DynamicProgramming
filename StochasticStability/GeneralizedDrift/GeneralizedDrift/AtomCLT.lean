/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.AtomLLN
import GeneralizedDrift.KolmogorovAnscombe
import Mathlib.Probability.CentralLimitTheorem

/-!
# The CLT for chains with an atom (MT §17.2.2)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/AtomCLT.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Meyn and Tweedie, Theorem 17.2.2 and (17.13)–(17.20), pp. 429–432. `α` is a recurrent atom with
`a ∈ α`, `ρ = cycleLaw P α a` the law of a full cycle, `m = E_ρ[σ_α + 1] = E_a[τ_α]` the mean
cycle length (`cycleMeanLength`), `π(g) = E_ρ[s(g)]/m` the stationary mean (`atomMean`), and
`γ_g² = E_ρ[s(ḡ)²]/m` with `ḡ = g − π(g)` (`cltVariance`).

**Tools.**
* `iIndepFun_cycles`, `identDistrib_cycles`: under `P_μ` the variables `φ(cycle (j + 1))` are
  i.i.d. (from the regeneration theorem `map_cycles_eq_infinitePi`).
* `cycleCount α n ω`: the number of full cycles completed by time `n`, with
  `cycleCount_eq` (it is `j` when `σ_α(j) ≤ n < σ_α(j + 1)`) and the pathwise bound (17.15)
  `abs_pathSum_sub_le`.
* `tendsto_cycleCount_div`: `ℓₙ/n → 1/m` a.s. (17.18).

**Results.**
* **(17.13)** `theorem_17_2_2_variance`: under the moment condition (17.14) the chain has the
  invariant probability `π = μ°_α/μ°_α(X)`, with `π(α) = 1/m`, `π(g) = atomMean`, and
  `γ_g² = π(α) E_a[(Σ_{k=1}^{τ_α} ḡ(Φₖ))²]`.
* **Theorem 17.2.2** (`theorem_17_2_2`, p. 430): under (17.14), `n^{−1/2} Sₙ(ḡ)` converges in
  distribution to `N(0, γ_g²)` under every initial law from which `α` is reached a.s.
  (`theorem_17_2_2_harris`: from every initial state, for a Harris chain with an accessible
  atom). The case `γ_g² = 0` is included: the limit is then `0`.

The LIL part of Theorem 17.2.2 is `theorem_17_2_2_lil` in `ChainLIL` (from the i.i.d. LIL of
`IIDLIL`).
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Independence of cycle functionals -/

/-- Under `P_μ`, cycle functionals `φ(cycle (j + 1))` are independent. -/
theorem iIndepFun_cycles (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α)
    (hν : ∀ᵐ ω ∂pathMeasure P (P a), firstHit α ω ≠ ⊤) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤)
    {φ : (ℕ → X) → ℝ} (hφ : Measurable φ) :
    iIndepFun (fun j ω => φ (cycle α (j + 1) ω)) (pathMeasure P μ) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have := isProbabilityMeasure_cycleLaw P α a
  have hΞ : Measurable fun ω j => cycle α (j + 1) ω :=
    measurable_pi_iff.2 fun j => measurable_cycle hα.1 (j + 1)
  have hmX : ∀ j, Measurable fun ω => φ (cycle α (j + 1) ω) := fun j =>
    hφ.comp (measurable_cycle hα.1 (j + 1))
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hmX]
  have hlaw := map_cycles_eq_infinitePi P hα ha hν μ hμ
  have h1 : (pathMeasure P μ).map (fun ω j => φ (cycle α (j + 1) ω)) =
      ((pathMeasure P μ).map fun ω j => cycle α (j + 1) ω).map fun s j => φ (s j) := by
    have hg : Measurable fun (s : ℕ → ℕ → X) j => φ (s j) :=
      measurable_pi_iff.2 fun j => hφ.comp (measurable_pi_apply j)
    rw [Measure.map_map hg hΞ]
    rfl
  have h2 : ∀ j, (pathMeasure P μ).map (fun ω => φ (cycle α (j + 1) ω)) =
      (cycleLaw P α a).map φ := by
    intro j
    have : (fun ω => φ (cycle α (j + 1) ω)) = (fun s : ℕ → ℕ → X => φ (s j)) ∘
        fun ω j => cycle α (j + 1) ω := rfl
    have hg : Measurable fun s : ℕ → ℕ → X => φ (s j) := hφ.comp (measurable_pi_apply j)
    rw [this, ← Measure.map_map hg hΞ, hlaw,
      show (fun s : ℕ → ℕ → X => φ (s j)) = φ ∘ fun s => s j from rfl,
      ← Measure.map_map hφ (measurable_pi_apply j), Measure.infinitePi_map_eval]
  rw [h1, hlaw, Measure.infinitePi_map_pi _ (fun _ => hφ)]
  simp_rw [h2]

/-- Under `P_μ`, the law of `φ(cycle (j + 1))` is `ρ ∘ φ⁻¹` for every `j`. -/
theorem map_cycle_eq (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α)
    (hν : ∀ᵐ ω ∂pathMeasure P (P a), firstHit α ω ≠ ⊤) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤)
    {φ : (ℕ → X) → ℝ} (hφ : Measurable φ) (j : ℕ) :
    (pathMeasure P μ).map (fun ω => φ (cycle α (j + 1) ω)) = (cycleLaw P α a).map φ := by
  have := isProbabilityMeasure_cycleLaw P α a
  have hΞ : Measurable fun ω j => cycle α (j + 1) ω :=
    measurable_pi_iff.2 fun j => measurable_cycle hα.1 (j + 1)
  have : (fun ω => φ (cycle α (j + 1) ω)) = (fun s : ℕ → ℕ → X => φ (s j)) ∘
      fun ω j => cycle α (j + 1) ω := rfl
  have hg : Measurable fun s : ℕ → ℕ → X => φ (s j) := hφ.comp (measurable_pi_apply j)
  rw [this, ← Measure.map_map hg hΞ,
    map_cycles_eq_infinitePi P hα ha hν μ hμ,
    show (fun s : ℕ → ℕ → X => φ (s j)) = φ ∘ fun s => s j from rfl,
    ← Measure.map_map hφ (measurable_pi_apply j), Measure.infinitePi_map_eval]

/-- Under `P_μ`, the cycle functionals `φ(cycle (j + 1))` are identically distributed. -/
theorem identDistrib_cycles (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α)
    (hν : ∀ᵐ ω ∂pathMeasure P (P a), firstHit α ω ≠ ⊤) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤)
    {φ : (ℕ → X) → ℝ} (hφ : Measurable φ) (j : ℕ) :
    IdentDistrib (fun ω => φ (cycle α (j + 1) ω)) (fun ω => φ (cycle α (0 + 1) ω))
      (pathMeasure P μ) (pathMeasure P μ) :=
  ⟨(hφ.comp (measurable_cycle hα.1 _)).aemeasurable,
    (hφ.comp (measurable_cycle hα.1 _)).aemeasurable,
    (map_cycle_eq P hα ha hν μ hμ hφ j).trans (map_cycle_eq P hα ha hν μ hμ hφ 0).symm⟩

/-! ### The number of completed cycles -/

/-- `ℓₙ`: the number of full cycles completed by time `n`, `#{j ≥ 1 : σ_α(j) ≤ n}`. -/
noncomputable def cycleCount (α : Set X) (n : ℕ) (ω : ℕ → X) : ℕ :=
  ((Finset.range n).filter fun j => renewalTime α (j + 1) ω ≤ n).card

omit [MeasurableSpace X] in
/-- `ℓₙ = j` when `σ_α(j) ≤ n < σ_α(j + 1)`. -/
theorem cycleCount_eq (α : Set X) {n j : ℕ} {ω : ℕ → X} (h1 : renewalTime α j ω ≤ n)
    (h2 : n < renewalTime α (j + 1) ω) : cycleCount α n ω = j := by
  have hmono : StrictMono fun i => renewalTime α i ω :=
    strictMono_nat_of_lt_succ fun i => renewalTime_lt_succ α i ω
  have hjn : j ≤ n := (le_renewalTime α j ω).trans h1
  have : (Finset.range n).filter (fun i => renewalTime α (i + 1) ω ≤ n) = Finset.range j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hi⟩
      by_contra hij
      push Not at hij
      have := hmono.monotone (show j + 1 ≤ i + 1 by omega)
      omega
    · intro hi
      exact ⟨by omega, (hmono.monotone (show i + 1 ≤ j by omega)).trans h1⟩
  rw [cycleCount, this, Finset.card_range]

omit [MeasurableSpace X] in
/-- `ℓₙ ≤ n`. -/
theorem cycleCount_le (α : Set X) (n : ℕ) (ω : ℕ → X) : cycleCount α n ω ≤ n :=
  (Finset.card_filter_le _ _).trans (Finset.card_range n).le

/-- `renewalTime α j` is measurable. -/
theorem measurable_renewalTime {α : Set X} (hα : MeasurableSet α) (j : ℕ) :
    Measurable (renewalTime α j) := by
  induction j with
  | zero => exact measurable_hitNat hα
  | succ j ih =>
    have : renewalTime α (j + 1) = fun ω => hitNat α ω + 1 + renewalTime α j (restart α ω) :=
      rfl
    rw [this]
    exact ((measurable_hitNat hα).add_const 1).add (ih.comp (measurable_restart hα))

/-- `ℓₙ` is measurable. -/
theorem measurable_cycleCount {α : Set X} (hα : MeasurableSet α) (n : ℕ) :
    Measurable (cycleCount α n) := by
  have : cycleCount α n = fun ω => ∑ j ∈ Finset.range n,
      if renewalTime α (j + 1) ω ≤ n then 1 else 0 := by
    ext ω; rw [cycleCount, Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ fun j _ => Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (measurable_renewalTime hα (j + 1)) measurable_const

omit [MeasurableSpace X] in
/-- Every `n ≥ σ_α` lies between two consecutive visit times. -/
theorem exists_renewalTime_between (α : Set X) {n : ℕ} {ω : ℕ → X}
    (hn : renewalTime α 0 ω ≤ n) :
    ∃ j, renewalTime α j ω ≤ n ∧ n < renewalTime α (j + 1) ω := by
  classical
  have hex : ∃ j, n < renewalTime α (j + 1) ω := ⟨n, by
    have := le_renewalTime α (n + 1) ω; omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; exact hn
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at this
    rwa [Nat.sub_add_cancel h] at this

/-! ### The pathwise comparison (17.15) -/

omit [MeasurableSpace X] in
/-- **(17.15)**: for `σ_α ≤ n`, `|Sₙ(g) − Σ_{j < ℓₙ} s_j(g)| ≤ |g(Φ₀)| + |s(g)(cycle 0)| +
s(|g|)(cycle (ℓₙ + 1))`. -/
theorem abs_pathSum_sub_le (α : Set X) (g : X → ℝ) {n : ℕ} {ω : ℕ → X}
    (hn : renewalTime α 0 ω ≤ n) :
    |pathSum g n ω - ∑ j ∈ Finset.range (cycleCount α n ω), cycleSum α g (cycle α (j + 1) ω)| ≤
      |g (ω 0)| + |cycleSum α g (cycle α 0 ω)| +
        cycleSum α (fun x => |g x|) (cycle α (cycleCount α n ω + 1) ω) := by
  obtain ⟨j, h1, h2⟩ := exists_renewalTime_between α hn
  rw [cycleCount_eq α h1 h2]
  set T := renewalTime α j ω with hT
  set T' := renewalTime α (j + 1) ω with hT'
  -- the sum up to `T`
  have hupto : ∑ i ∈ Finset.range (T + 1), g (ω i) =
      cycleSum α g (cycle α 0 ω) + ∑ i ∈ Finset.range j, cycleSum α g (cycle α (i + 1) ω) := by
    rw [hT, sum_range_renewalTime, Finset.sum_range_succ']; ring
  -- the partial last cycle
  have hpart : |∑ i ∈ Finset.Ico (T + 1) (n + 1), g (ω i)| ≤
      cycleSum α (fun x => |g x|) (cycle α (j + 1) ω) := by
    have hfull : ∑ i ∈ Finset.Ico (T + 1) (T' + 1), |g (ω i)| =
        cycleSum α (fun x => |g x|) (cycle α (j + 1) ω) := by
      have e1 := sum_range_renewalTime α (fun x => |g x|) (j + 1) ω
      have e2 := sum_range_renewalTime α (fun x => |g x|) j ω
      rw [Finset.sum_range_succ (fun i => cycleSum α (fun x => |g x|) (cycle α i ω)) (j + 1)]
        at e1
      rw [Finset.sum_Ico_eq_sub _ (by omega), e1, e2]; ring
    calc |∑ i ∈ Finset.Ico (T + 1) (n + 1), g (ω i)|
        ≤ ∑ i ∈ Finset.Ico (T + 1) (n + 1), |g (ω i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico (T + 1) (T' + 1), |g (ω i)| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
            fun i _ _ => abs_nonneg _
      _ = _ := hfull
  have hsplit : pathSum g n ω = ∑ i ∈ Finset.range (T + 1), g (ω i) +
      ∑ i ∈ Finset.Ico (T + 1) (n + 1), g (ω i) - g (ω 0) := by
    rw [pathSum_eq_sum_range_sub, Finset.sum_range_add_sum_Ico _ (by omega : T + 1 ≤ n + 1)]
  rw [hsplit, hupto]
  have := abs_add_three (-g (ω 0)) (cycleSum α g (cycle α 0 ω))
    (∑ i ∈ Finset.Ico (T + 1) (n + 1), g (ω i))
  rw [abs_neg] at this
  calc |cycleSum α g (cycle α 0 ω) + ∑ i ∈ Finset.range j, cycleSum α g (cycle α (i + 1) ω) +
        ∑ i ∈ Finset.Ico (T + 1) (n + 1), g (ω i) - g (ω 0) -
        ∑ i ∈ Finset.range j, cycleSum α g (cycle α (i + 1) ω)|
      = |-g (ω 0) + cycleSum α g (cycle α 0 ω) + ∑ i ∈ Finset.Ico (T + 1) (n + 1), g (ω i)| := by
        congr 1; ring
    _ ≤ _ := this
    _ ≤ _ := by linarith

/-! ### Deterministic lemmas -/

omit [MeasurableSpace X] in
/-- If `(Σ_{j<n} aⱼ)/n → L`, then `aₙ/(n + 1) → 0`. -/
theorem tendsto_term_div_of_tendsto_average {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, a j) / n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => a n / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (∑ j ∈ Finset.range (n + 1), a j) / ((n : ℝ) + 1)) atTop
      (𝓝 L) := by
    have := h.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp [Function.comp_apply]
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have : Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at this
    refine this.congr fun j => ?_
    have : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp; ring
  have h3 := h1.sub (h.mul h2)
  rw [mul_one, sub_self] at h3
  refine h3.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [Finset.sum_range_succ]
  field_simp
  ring

omit [MeasurableSpace X] in
/-- If `uⱼ ≥ 0` and `uⱼ/(j + 1) → 0`, then `u_{k(n)}/(n + 1) → 0` for indices `k(n) ≤ n`. -/
theorem tendsto_index_div_of_le {u : ℕ → ℝ} (hu0 : ∀ j, 0 ≤ u j)
    (hu : Tendsto (fun j : ℕ => u j / ((j : ℝ) + 1)) atTop (𝓝 0)) {k : ℕ → ℕ}
    (hk : ∀ n, k n ≤ n) : Tendsto (fun n : ℕ => u (k n) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hu ⊢
  intro ε hε
  obtain ⟨J, hJ⟩ := hu (ε / 2) (by positivity)
  set M := ∑ j ∈ Finset.range J, u j with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => hu0 j
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * M / ε)
  refine ⟨n₀, fun n hn => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hu0 _) hpos.le)]
  by_cases hkJ : J ≤ k n
  · have h1 := hJ (k n) hkJ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hu0 _) (by positivity))] at h1
    have h2 : u (k n) / ((n : ℝ) + 1) ≤ u (k n) / ((k n : ℝ) + 1) :=
      div_le_div_of_nonneg_left (hu0 _) (by positivity) (by exact_mod_cast (by
        have := hk n; omega : k n + 1 ≤ n + 1))
    linarith
  · push Not at hkJ
    have h1 : u (k n) ≤ M :=
      Finset.single_le_sum (fun j _ => hu0 j) (Finset.mem_range.2 hkJ)
    have hnn : 2 * M / ε < (n : ℝ) + 1 := by
      have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hε] at hnn
    rw [div_lt_iff₀ hpos]
    nlinarith

/-! ### Means and variances of cycles -/

/-- The mean cycle length `m = E_ρ[σ_α + 1] = E_a[τ_α]`. -/
noncomputable def cycleMeanLength (P : Kernel X X) [IsMarkovKernel P] (α : Set X) (a : X) : ℝ :=
  ∫ e, ((hitNat α e : ℝ) + 1) ∂cycleLaw P α a

/-- The stationary mean `π(g) = E_ρ[s(g)]/m`. -/
noncomputable def atomMean (P : Kernel X X) [IsMarkovKernel P] (α : Set X) (a : X)
    (g : X → ℝ) : ℝ :=
  (∫ e, cycleSum α g e ∂cycleLaw P α a) / cycleMeanLength P α a

/-- The asymptotic variance `γ_g² = E_ρ[s(ḡ)²]/m`, `ḡ = g − π(g)` (17.13). -/
noncomputable def cltVariance (P : Kernel X X) [IsMarkovKernel P] (α : Set X) (a : X)
    (g : X → ℝ) : ℝ :=
  (∫ e, cycleSum α (fun x => g x - atomMean P α a g) e ^ 2 ∂cycleLaw P α a) /
    cycleMeanLength P α a

omit [MeasurableSpace X] in
/-- `s(g − c) = s(g) − c (σ_α + 1)`. -/
theorem cycleSum_sub_const (α : Set X) (g : X → ℝ) (c : ℝ) (e : ℕ → X) :
    cycleSum α (fun x => g x - c) e = cycleSum α g e - c * ((hitNat α e : ℝ) + 1) := by
  simp only [cycleSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  push_cast; ring

/-- The mean cycle length is at least `1`. -/
theorem one_le_cycleMeanLength (P : Kernel X X) [IsMarkovKernel P] (α : Set X)
    (a : X) (hL : Integrable (fun e => (hitNat α e : ℝ) + 1)
      (cycleLaw P α a)) : 1 ≤ cycleMeanLength P α a := by
  have := isProbabilityMeasure_cycleLaw P α a
  rw [cycleMeanLength]
  calc (1 : ℝ) = ∫ _e, (1 : ℝ) ∂cycleLaw P α a := by simp
    _ ≤ _ := integral_mono (integrable_const 1) hL fun e => by
        have := (hitNat α e).cast_nonneg (α := ℝ); simp only; linarith

/-- Under (17.14), the centred cycle sums are square integrable. -/
theorem memLp_cycleSum_centred (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) {g : X → ℝ} (hgm : Measurable g)
    (hg2 : MemLp (cycleSum α fun x => |g x|) 2 (cycleLaw P α a))
    (hL2 : MemLp (fun e => (hitNat α e : ℝ) + 1) 2 (cycleLaw P α a)) (c : ℝ) :
    MemLp (cycleSum α fun x => g x - c) 2 (cycleLaw P α a) := by
  refine (hg2.add (hL2.const_mul |c|)).of_le
    (measurable_cycleSum hα (hgm.sub measurable_const)).aestronglyMeasurable
    (Eventually.of_forall fun e => ?_)
  have h1 : |cycleSum α (fun x => g x - c) e| ≤
      cycleSum α (fun x => |g x|) e + |c| * ((hitNat α e : ℝ) + 1) := by
    rw [cycleSum_sub_const]
    have h2 := abs_cycleSum_le α g e
    have h3 : |c * ((hitNat α e : ℝ) + 1)| = |c| * ((hitNat α e : ℝ) + 1) := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (hitNat α e : ℝ) + 1 by positivity)]
    have := abs_sub (cycleSum α g e) (c * ((hitNat α e : ℝ) + 1))
    linarith
  have h4 : 0 ≤ cycleSum α (fun x => |g x|) e + |c| * ((hitNat α e : ℝ) + 1) :=
    add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (by positivity)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg h4]
  exact h1

/-- The centred cycle sums have mean zero. -/
theorem integral_cycleSum_centred (P : Kernel X X) [IsMarkovKernel P] (α : Set X)
    (a : X) {g : X → ℝ} (hg1 : Integrable (cycleSum α g) (cycleLaw P α a))
    (hL : Integrable (fun e => (hitNat α e : ℝ) + 1) (cycleLaw P α a)) :
    ∫ e, cycleSum α (fun x => g x - atomMean P α a g) e ∂cycleLaw P α a = 0 := by
  have hm := one_le_cycleMeanLength P α a hL
  simp_rw [cycleSum_sub_const]
  rw [integral_sub hg1 (hL.const_mul _), integral_const_mul, ← cycleMeanLength, atomMean,
    div_mul_cancel₀ _ (by linarith)]
  ring

/-! ### Convergence in distribution: index changes and deterministic factors -/

/-- Convergence in distribution is preserved along indices `N(n) → ∞`. -/
theorem tendstoInDistribution_comp_index {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    {W : ℕ → Ω → ℝ} {Z : Ω' → ℝ} (hW : TendstoInDistribution W atTop Z (fun _ => Q) Q')
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    TendstoInDistribution (fun n => W (N n)) atTop Z (fun _ => Q) Q' :=
  ⟨fun n => hW.forall_aemeasurable (N n), hW.aemeasurable_limit, hW.tendsto.comp hN⟩

/-- Slutsky for deterministic factors: `Wₙ ⇒ Z` and `cₙ → c₀` give `cₙ Wₙ ⇒ c₀ Z`. -/
theorem tendstoInDistribution_const_mul_seq {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {W : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hW : TendstoInDistribution W atTop Z (fun _ => Q) Q') {c : ℕ → ℝ} {c₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) :
    TendstoInDistribution (fun n ω => c n * W n ω) atTop (fun ω => c₀ * Z ω) (fun _ => Q) Q' := by
  have hY : TendstoInMeasure Q (fun n (_ : Ω) => c n) atTop (fun _ => c₀) :=
    tendstoInMeasure_of_tendsto_ae (fun n => aestronglyMeasurable_const)
      (Eventually.of_forall fun _ => hc)
  exact hW.continuous_comp_prodMk_of_tendstoInMeasure_const (g := fun p : ℝ × ℝ => p.2 * p.1)
    (by fun_prop) hY fun n => aemeasurable_const

/-! ### The number of cycles grows like `n/m` -/

omit [MeasurableSpace X] in
/-- If `(Tⱼ + 1)/(j + 1) → m > 0`, then `j/Tⱼ → 1/m` and `j/T_{j+1} → 1/m`. -/
theorem tendsto_index_div_renewal {T : ℕ → ℕ} {m : ℝ} (hm : 0 < m)
    (h : Tendsto (fun j : ℕ => ((T j : ℝ) + 1) / ((j : ℝ) + 1)) atTop (𝓝 m)) :
    Tendsto (fun j : ℕ => (j : ℝ) / T j) atTop (𝓝 (1 / m)) ∧
      Tendsto (fun j : ℕ => (j : ℝ) / T (j + 1)) atTop (𝓝 (1 / m)) := by
  have h1 : Tendsto (fun j : ℕ => (T j : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 m) := by
    have := h.sub (tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [sub_zero] at this
    refine this.congr fun j => ?_
    rw [← sub_div]; ring_nf
  have h2 : Tendsto (fun j : ℕ => ((j : ℝ) + 1) / T j) atTop (𝓝 (1 / m)) := by
    have := h1.inv₀ hm.ne'
    rw [← one_div] at this
    refine this.congr fun j => ?_
    rw [inv_div]
  have h3 : Tendsto (fun j : ℕ => (j : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 1) := by
    have : Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at this
    refine this.congr fun j => ?_
    have : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp; ring
  have hev : ∀ᶠ j in atTop, (T j : ℝ) ≠ 0 := by
    filter_upwards [h1.eventually (eventually_gt_nhds hm)] with j hj
    intro h0; rw [h0, zero_div] at hj; exact absurd hj (lt_irrefl 0)
  constructor
  · have := h3.mul h2
    rw [one_mul] at this
    refine this.congr' ?_
    filter_upwards [hev] with j hj
    have : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · have h2' := h2.comp (tendsto_add_atTop_nat 1)
    have h3' : Tendsto (fun j : ℕ => (j : ℝ) / ((j : ℝ) + 1 + 1)) atTop (𝓝 1) := by
      have : Tendsto (fun j : ℕ => 1 - 2 / ((j : ℝ) + 1 + 1)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
          ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_add
            tendsto_const_nhds))
      rw [sub_zero] at this
      refine this.congr fun j => ?_
      have : (j : ℝ) + 1 + 1 ≠ 0 := by positivity
      field_simp; ring
    have := h3'.mul h2'
    rw [one_mul] at this
    refine this.congr' ?_
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hev] with j hj
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hj ⊢
    have : (j : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp

/-- **(17.18)**: `ℓₙ/n → 1/m`, `P_μ`-a.s., when the mean cycle length is finite. -/
theorem tendsto_cycleCount_div (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (hrec : hitProb P α a = 1) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤)
    (hL : Integrable (fun e => (hitNat α e : ℝ) + 1) (cycleLaw P α a)) :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n : ℕ => (cycleCount α n ω : ℝ) / n) atTop
      (𝓝 (1 / cycleMeanLength P α a)) := by
  have hν := ae_firstHit_ne_top_of_hitProb P hα.1 hrec
  have hm := one_le_cycleMeanLength P α a hL
  have hLm : Measurable fun e : ℕ → X => (hitNat α e : ℝ) + 1 :=
    ((measurable_of_countable _).comp (measurable_hitNat hα.1)).add_const 1
  have hsl := tendsto_cycle_average P hα ha hν μ hμ hLm hL
  filter_upwards [hsl] with ω hω
  -- `(σ_α(j) + 1)/(j + 1) → m`
  have hT : Tendsto (fun j : ℕ => ((renewalTime α j ω : ℝ) + 1) / ((j : ℝ) + 1)) atTop
      (𝓝 (cycleMeanLength P α a)) := by
    have h2 : Tendsto (fun j : ℕ => (j : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 1) := by
      have : Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
      rw [sub_zero] at this
      refine this.congr fun j => ?_
      have : (j : ℝ) + 1 ≠ 0 := by positivity
      field_simp; ring
    have h5 : Tendsto (fun j : ℕ => ((hitNat α (cycle α 0 ω) : ℝ) + 1) / ((j : ℝ) + 1))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h4 := (hω.mul h2).add h5
    rw [mul_one, add_zero] at h4
    refine h4.congr' (eventually_atTop.2 ⟨1, fun j hj => ?_⟩)
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    have : (j : ℝ) + 1 ≠ 0 := by positivity
    change _ = ((renewalTime α j ω : ℝ) + 1) / ((j : ℝ) + 1)
    rw [renewalTime_add_one, Finset.sum_range_succ']
    field_simp
  obtain ⟨hlo, hhi⟩ := tendsto_index_div_renewal (by linarith) hT
  refine tendsto_of_renewal_sandwich
    (strictMono_nat_of_lt_succ fun j => renewalTime_lt_succ α j ω) ?_ hhi hlo
  filter_upwards [eventually_ge_atTop 1] with j hj n hn1 hn2
  rw [cycleCount_eq α hn1 hn2]
  have hT0 : (0 : ℝ) < renewalTime α j ω := by
    have := le_renewalTime α j ω; exact_mod_cast (show 0 < renewalTime α j ω by omega)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hT0 (by exact_mod_cast hn1)
  constructor
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hn0 (by exact_mod_cast hn2.le)
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hT0 (by exact_mod_cast hn1)

/-! ### Theorem 17.2.2 -/

/-- A sum with a measurable random number of terms is measurable. -/
theorem measurable_sum_range_random {Ω : Type*} [MeasurableSpace Ω] {Y : ℕ → Ω → ℝ}
    (hY : ∀ j, Measurable (Y j)) {K : Ω → ℕ} (hK : Measurable K) :
    Measurable fun ω => ∑ j ∈ Finset.range (K ω), Y j ω := by
  have hF : Measurable fun p : Ω × ℕ => ∑ j ∈ Finset.range p.2, Y j p.1 :=
    measurable_from_prod_countable_left fun n => by
      dsimp only
      exact Finset.measurable_sum _ fun j _ => hY j
  exact hF.comp (measurable_id.prodMk hK)

/-- Cycle sums of `|g|` are integrable bounds for cycle sums of `g`. -/
theorem integrable_cycleSum_of_abs {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) {a : X} {g : X → ℝ} (hgm : Measurable g)
    (h : Integrable (cycleSum α fun x => |g x|) (cycleLaw P α a)) :
    Integrable (cycleSum α g) (cycleLaw P α a) :=
  h.mono' (measurable_cycleSum hα hgm).aestronglyMeasurable
    (Eventually.of_forall fun e => by rw [Real.norm_eq_abs]; exact abs_cycleSum_le α g e)

/-- **Theorem 17.2.2** (MT p. 430), the CLT part: let `α ∋ a` be a recurrent atom, `μ` an
initial law from which `α` is reached a.s., and suppose the moment condition (17.14),
`E_ρ[s(|g|)²] < ∞` and `E_ρ[(σ_α + 1)²] < ∞`. Then `n^{−1/2} Sₙ(g − π(g))` converges in
distribution under `P_μ` to a normal variable with variance `γ_g² = cltVariance P α a g`. -/
theorem theorem_17_2_2 (P : Kernel X X) [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {a : X} (ha : a ∈ α) (hrec : hitProb P α a = 1) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ ω ∂pathMeasure P μ, firstHit α ω ≠ ⊤) {g : X → ℝ} (hgm : Measurable g)
    (hg2 : MemLp (cycleSum α fun x => |g x|) 2 (cycleLaw P α a))
    (hL2 : MemLp (fun e => (hitNat α e : ℝ) + 1) 2 (cycleLaw P α a))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (cltVariance P α a g).toNNReal) P') :
    haveI := isProbabilityMeasure_pathMeasure P μ
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ *
      pathSum (fun x => g x - atomMean P α a g) n ω) atTop Z (fun _ => pathMeasure P μ) P' := by
  have := isProbabilityMeasure_pathMeasure P μ
  have := isProbabilityMeasure_cycleLaw P α a
  have hν := ae_firstHit_ne_top_of_hitProb P hα.1 hrec
  set c := atomMean P α a g with hc
  set gb : X → ℝ := fun x => g x - c with hgb
  have hgbm : Measurable gb := hgm.sub measurable_const
  set m := cycleMeanLength P α a with hmdef
  have hL : Integrable (fun e => (hitNat α e : ℝ) + 1) (cycleLaw P α a) :=
    hL2.integrable one_le_two
  have hm1 : 1 ≤ m := one_le_cycleMeanLength P α a hL
  have hm0 : 0 < m := by linarith
  -- the cycle variables `Yⱼ = s(ḡ)(cycle (j + 1))`
  set φ := cycleSum α gb with hφ
  have hφm : Measurable φ := measurable_cycleSum hα.1 hgbm
  have hφ2 : MemLp φ 2 (cycleLaw P α a) := memLp_cycleSum_centred P hα.1 a hgm hg2 hL2 c
  have hg1 : Integrable (cycleSum α g) (cycleLaw P α a) :=
    integrable_cycleSum_of_abs hα.1 hgm (hg2.integrable one_le_two)
  have hφ0 : ∫ e, φ e ∂cycleLaw P α a = 0 := integral_cycleSum_centred P α a hg1 hL
  set Y : ℕ → (ℕ → X) → ℝ := fun j ω => φ (cycle α (j + 1) ω) with hYdef
  have hYm : ∀ j, Measurable (Y j) := fun j => hφm.comp (measurable_cycle hα.1 (j + 1))
  have hind : iIndepFun Y (pathMeasure P μ) := iIndepFun_cycles P hα ha hν μ hμ hφm
  have hident : ∀ j, IdentDistrib (Y j) (Y 0) (pathMeasure P μ) (pathMeasure P μ) :=
    identDistrib_cycles P hα ha hν μ hμ hφm
  have hY0 : IdentDistrib (Y 0) φ (pathMeasure P μ) (cycleLaw P α a) :=
    ⟨(hYm 0).aemeasurable, hφm.aemeasurable, map_cycle_eq P hα ha hν μ hμ hφm 0⟩
  have hY02 : MemLp (Y 0) 2 (pathMeasure P μ) := hY0.memLp_iff.2 hφ2
  have hY0mean : ∫ ω, Y 0 ω ∂pathMeasure P μ = 0 := hY0.integral_eq.trans hφ0
  set σ2 := ∫ e, φ e ^ 2 ∂cycleLaw P α a with hσ2
  have hσ0 : 0 ≤ σ2 := integral_nonneg fun e => sq_nonneg _
  have hvar : Var[Y 0; pathMeasure P μ] = σ2 := by
    rw [hY0.variance_eq, variance_of_integral_eq_zero hφm.aemeasurable hφ0]
  have hγ : cltVariance P α a g = σ2 / m := rfl
  -- the Gaussian limit `Z₀ = √m Z` of the i.i.d. sums
  set Z₀ : Ω' → ℝ := fun ω' => √m * Z ω' with hZ₀def
  have hZ₀ : HasLaw Z₀ (gaussianReal 0 (Var[Y 0; pathMeasure P μ]).toNNReal) P' := by
    have h := gaussianReal_const_mul hZ (√m)
    rw [mul_zero] at h
    convert h using 2
    rw [hvar, hγ]
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.sq_sqrt hm0.le]
    rw [Real.coe_toNNReal _ hσ0, Real.coe_toNNReal _ (div_nonneg hσ0 hm0.le)]
    field_simp
  have hCLT := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ₀ hY02 hind hident
  simp only [hY0mean, mul_zero, sub_zero] at hCLT
  -- along `N(n) = ⌊n/m⌋`
  set N : ℕ → ℕ := fun n => ⌊(1 / m) * n⌋₊ with hN
  have hNt : Tendsto N atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity))
  have hcn : Tendsto (fun n : ℕ => √(N n : ℝ) / √(n : ℝ)) atTop (𝓝 (1 / √m)) := by
    have h1 : Tendsto (fun n : ℕ => (N n : ℝ) / n) atTop (𝓝 (1 / m)) :=
      (tendsto_nat_floor_mul_div_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    have h2 := (Real.continuous_sqrt.tendsto _).comp h1
    rw [Real.sqrt_div' _ hm0.le, Real.sqrt_one] at h2
    refine h2.congr fun n => ?_
    rw [Function.comp_apply, Real.sqrt_div' _ (Nat.cast_nonneg n)]
  have hX := tendstoInDistribution_const_mul_seq (tendstoInDistribution_comp_index hCLT hNt) hcn
  have hZeq : (fun ω' => 1 / √m * Z₀ ω') = Z := by
    ext ω'
    have : √m ≠ 0 := (Real.sqrt_pos.2 hm0).ne'
    simp only [hZ₀def]
    field_simp
  rw [hZeq] at hX
  set X' : ℕ → (ℕ → X) → ℝ := fun n ω => (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range (N n), Y k ω
    with hX'def
  have hXeq : (fun n ω => √(N n : ℝ) / √(n : ℝ) *
      ((√(N n : ℝ))⁻¹ * ∑ k ∈ Finset.range (N n), Y k ω)) = X' := by
    ext n ω
    rcases Nat.eq_zero_or_pos (N n) with h0 | hpos
    · simp [hX'def, h0]
    · have hn : n ≠ 0 := by
        rintro rfl; simp [hN] at hpos
      have h1 : √(N n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hpos)).ne'
      have h2 : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)).ne'
      simp only [hX'def]
      field_simp
  rw [hXeq] at hX
  -- the random-index step
  have hK := tendsto_cycleCount_div P hα ha hrec μ hμ hL
  have hR2 := tendstoInMeasure_anscombe hind hYm hident hY02 hY0mean
    (measurable_cycleCount hα.1) (c := 1 / m) (by positivity) hK
  set V : ℕ → (ℕ → X) → ℝ := fun n ω =>
    (√(n : ℝ))⁻¹ * ∑ j ∈ Finset.range (cycleCount α n ω), Y j ω with hVdef
  have hVm : ∀ n, Measurable (V n) := fun n =>
    measurable_const.mul (measurable_sum_range_random hYm (measurable_cycleCount hα.1 n))
  have hV : TendstoInDistribution V atTop Z (fun _ => pathMeasure P μ) P' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub V Z hX ?_
      fun n => (hVm n).aemeasurable
    convert hR2 using 1
    ext n ω
    simp only [hVdef, hX'def, Pi.sub_apply, hN]
    ring
  -- the pathwise error `R₁ → 0` a.s.
  set ψ := cycleSum α fun x => |gb x| with hψ
  have hψm : Measurable ψ := measurable_cycleSum hα.1 (measurable_abs_of_measurable hgbm)
  have hψ2 : MemLp ψ 2 (cycleLaw P α a) := by
    refine (hg2.add (hL2.const_mul |c|)).of_le hψm.aestronglyMeasurable
      (Eventually.of_forall fun e => ?_)
    have h4 : 0 ≤ cycleSum α (fun x => |g x|) e + |c| * ((hitNat α e : ℝ) + 1) :=
      add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (by positivity)
    have h5 : 0 ≤ ψ e := Finset.sum_nonneg fun i _ => abs_nonneg _
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg h4, abs_of_nonneg h5]
    have : ψ e ≤ cycleSum α (fun x => |g x| + |c|) e :=
      Finset.sum_le_sum fun i _ => by
        simp only [hgb]; exact (abs_sub _ _)
    have h6 : cycleSum α (fun x => |g x| + |c|) e =
        cycleSum α (fun x => |g x|) e + |c| * ((hitNat α e : ℝ) + 1) := by
      simp only [cycleSum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      push_cast; ring
    linarith
  have hsl2 := tendsto_cycle_average P hα ha hν μ hμ (hψm.pow_const 2) hψ2.integrable_sq
  have hR1 : ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ *
      (pathSum gb n ω - ∑ j ∈ Finset.range (cycleCount α n ω), Y j ω)) atTop (𝓝 0) := by
    filter_upwards [hsl2] with ω hω
    set u : ℕ → ℝ := fun j => ψ (cycle α (j + 1) ω) ^ 2 with hu
    have hu1 : Tendsto (fun j : ℕ => u j / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_term_div_of_tendsto_average hω
    have hu2 := tendsto_index_div_of_le (fun j => sq_nonneg _) hu1 (k := fun n => cycleCount α n ω)
      (cycleCount_le α · ω)
    set C := |gb (ω 0)| + |cycleSum α gb (cycle α 0 ω)| with hC
    -- the bound `(√n)⁻¹ (C + ψ(cycle (ℓₙ + 1)))` tends to `0`
    have hsqrt : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hZ' : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * ψ (cycle α (cycleCount α n ω + 1) ω))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
        have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
        rw [add_zero] at this
        refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
        have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        field_simp
      have h2 := (hu2.mul h1)
      rw [zero_mul] at h2
      have h3 := (Real.continuous_sqrt.tendsto _).comp h2
      rw [Real.sqrt_zero] at h3
      refine h3.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hψ0 : 0 ≤ ψ (cycle α (cycleCount α n ω + 1) ω) :=
        Finset.sum_nonneg fun i _ => abs_nonneg _
      simp only [Function.comp_apply]
      rw [show u (cycleCount α n ω) / ((n : ℝ) + 1) * (((n : ℝ) + 1) / n) =
          ψ (cycle α (cycleCount α n ω + 1) ω) ^ 2 / n by
        simp only [hu]; field_simp]
      rw [Real.sqrt_div' _ hn0.le, Real.sqrt_sq hψ0, inv_mul_eq_div]
    have hbound := (hsqrt.mul_const C).add hZ'
    rw [zero_mul, add_zero] at hbound
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop (renewalTime α 0 ω)] with n hn
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    have h := abs_pathSum_sub_le α gb hn
    have : (√(n : ℝ))⁻¹ * |pathSum gb n ω - ∑ j ∈ Finset.range (cycleCount α n ω), Y j ω| ≤
        (√(n : ℝ))⁻¹ * (C + ψ (cycle α (cycleCount α n ω + 1) ω)) :=
      mul_le_mul_of_nonneg_left (by simpa [hYdef, hφ, hC, hψ] using h)
        (inv_nonneg.2 (Real.sqrt_nonneg _))
    linarith
  -- combine
  have hfinal : TendstoInMeasure (pathMeasure P μ)
      ((fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum gb n ω) - V) atTop 0 := by
    refine (tendstoInMeasure_of_tendsto_ae (fun n => ?_) hR1).congr_left (fun n => ?_)
    · exact (measurable_const.mul ((measurable_pathSum hgbm n).sub
        (measurable_sum_range_random hYm (measurable_cycleCount hα.1 n)))).aestronglyMeasurable
    · exact Eventually.of_forall fun ω => by simp only [Pi.sub_apply, hVdef]; ring
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ Z hV hfinal
    fun n => (measurable_const.mul (measurable_pathSum hgbm n)).aemeasurable

/-! ### The invariant probability and the variance (17.13) -/

/-- The law of a full cycle is the law of the excursion of `θ¹Φ` under `P_a`:
`E_ρ[F] = E_a[F(excursion(θ¹Φ))]`. -/
theorem integral_cycleLaw (P : Kernel X X) [IsMarkovKernel P] {α : Set X} (hα : MeasurableSet α)
    (a : X) {F : (ℕ → X) → ℝ} (hF : Measurable F) :
    ∫ e, F e ∂cycleLaw P α a = ∫ ω, F (excursion α (shift 1 ω)) ∂pathKernel P a := by
  rw [cycleLaw, ← pathKernel_map_shift_one, Measure.map_map (measurable_excursion hα)
    (measurable_shift 1), integral_map ((measurable_excursion hα).comp
      (measurable_shift 1)).aemeasurable hF.aestronglyMeasurable]
  rfl

/-- `μ°_α(X) = m`: the total mass of the atom measure is the mean cycle length. -/
theorem atomMeasure_univ_eq (P : Kernel X X) [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {a : X} (hrec : hitProb P α a = 1)
    (hL : Integrable (fun e => (hitNat α e : ℝ) + 1) (cycleLaw P α a)) :
    atomMeasure P hα.1 a univ = ENNReal.ofReal (cycleMeanLength P α a) := by
  have h := lintegral_cycleSumE P hα hrec (f := fun _ => 1) measurable_const
  rw [lintegral_one] at h
  rw [← h, cycleMeanLength, ofReal_integral_eq_lintegral_ofReal hL
    (Eventually.of_forall fun e => by positivity)]
  refine lintegral_congr fun e => ?_
  simp only [cycleSumE, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_one,
    ENNReal.ofReal_natCast, Nat.cast_add, Nat.cast_one]

/-- **(17.13) and positivity** (MT p. 430): if the mean cycle length `m` is finite, the chain has
the invariant probability `π = μ°_α/μ°_α(X)`, with `π(α) = 1/m` and, for `E_ρ[s(|g|)] < ∞`,
`π(g) = atomMean P α a g`; the CLT variance is
`γ_g² = π(α) E_a[(Σ_{k=1}^{τ_α} ḡ(Φₖ))²]`, where `Σ_{k=1}^{τ_α}` is written
`Σ_{i ≤ σ_α(θ¹Φ)} ḡ(Φ_{i+1})` (`τ_α = σ_α ∘ θ¹ + 1`). -/
theorem theorem_17_2_2_variance (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (hrec : hitProb P α a = 1) {g : X → ℝ}
    (hgm : Measurable g) (hg1 : Integrable (cycleSum α fun x => |g x|) (cycleLaw P α a))
    (hL : Integrable (fun e => (hitNat α e : ℝ) + 1) (cycleLaw P α a)) :
    let π := (atomMeasure P hα.1 a univ)⁻¹ • atomMeasure P hα.1 a
    IsProbabilityMeasure π ∧ IsInvariant P π ∧
      π α = ENNReal.ofReal (1 / cycleMeanLength P α a) ∧
      ∫ x, g x ∂π = atomMean P α a g ∧
      cltVariance P α a g = (π α).toReal * ∫ ω, (∑ i ∈ Finset.range
        (hitNat α (shift 1 ω) + 1), (g (ω (i + 1)) - atomMean P α a g)) ^ 2 ∂pathKernel P a := by
  intro π
  have hm1 := one_le_cycleMeanLength P α a hL
  have hm0 : 0 < cycleMeanLength P α a := by linarith
  have huniv := atomMeasure_univ_eq P hα hrec hL
  set c := atomMeasure P hα.1 a univ with hcdef
  have hc0 : c ≠ 0 := by rw [huniv]; exact (ENNReal.ofReal_pos.2 hm0).ne'
  have hctop : c ≠ ∞ := by rw [huniv]; exact ENNReal.ofReal_ne_top
  have hπprob : IsProbabilityMeasure π := by
    constructor
    simp only [π, Measure.smul_apply, smul_eq_mul]
    rw [← hcdef, ENNReal.inv_mul_cancel hc0 hctop]
  have hinv0 : IsInvariant P (atomMeasure P hα.1 a) := by
    have h := theorem_10_2_1_iii hα ha
    refine h.2 ?_
    rw [← h.1]; exact hctop
  have hαval : atomMeasure P hα.1 a α = 1 := by rw [atomMeasure_self, hrec]
  have hπα : π α = ENNReal.ofReal (1 / cycleMeanLength P α a) := by
    simp only [π, Measure.smul_apply, smul_eq_mul, hαval, mul_one]
    rw [← hcdef, huniv, ENNReal.ofReal_div_of_pos hm0, ENNReal.ofReal_one, one_div]
  -- `g` is `μ°_α`-integrable
  have hgi : Integrable g (atomMeasure P hα.1 a) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp_rw [Real.norm_eq_abs]
    rw [← lintegral_cycleSumE P hα hrec (measurable_abs_of_measurable hgm).ennreal_ofReal]
    simp_rw [← ofReal_cycleSum (fun x => abs_nonneg (g x))]
    rw [← ofReal_integral_eq_lintegral_ofReal hg1
      (Eventually.of_forall fun e => Finset.sum_nonneg fun i _ => abs_nonneg _)]
    exact ENNReal.ofReal_lt_top
  have hπα' : (π α).toReal = 1 / cycleMeanLength P α a := by
    rw [hπα, ENNReal.toReal_ofReal (by positivity)]
  refine ⟨hπprob, hinv0.smul _, hπα, ?_, ?_⟩
  · simp only [π]
    rw [integral_smul_measure, smul_eq_mul, ← integral_cycleSum P hα hrec hgm hgi, atomMean,
      ← hcdef, huniv, ENNReal.toReal_inv, ENNReal.toReal_ofReal hm0.le]
    ring
  · have hFm : Measurable fun e => cycleSum α (fun x => g x - atomMean P α a g) e ^ 2 :=
      (measurable_cycleSum hα.1 (hgm.sub measurable_const)).pow_const 2
    rw [hπα', cltVariance, integral_cycleLaw P hα.1 a hFm]
    simp_rw [cycleSum_excursion]
    rw [div_eq_inv_mul, one_div]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [shift_apply, add_comm]

/-- **Theorem 17.2.2**, from every initial state (MT p. 430): for a Harris chain with an accessible
atom `α ∋ a` and the moment condition (17.14), `n^{−1/2} Sₙ(ḡ) ⇒ N(0, γ_g²)` under every `P_x`. -/
theorem theorem_17_2_2_harris [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ) {α : Set X}
    (hacc : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) {g : X → ℝ} (hgm : Measurable g)
    (hg2 : MemLp (cycleSum α fun x => |g x|) 2 (cycleLaw P α a))
    (hL2 : MemLp (fun e => (hitNat α e : ℝ) + 1) 2 (cycleLaw P α a))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (cltVariance P α a g).toNNReal) P') (x : X) :
    haveI := isProbabilityMeasure_pathMeasure P (Measure.dirac x)
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ *
      pathSum (fun x => g x - atomMean P α a g) n ω) atTop Z
      (fun _ => pathMeasure P (Measure.dirac x)) P' := by
  have hhit : ∀ y, hitProb P α y = 1 := fun y =>
    le_antisymm (hitProb_le_one P α y) (by
      rw [← theorem_9_1_4 hH hacc.1.1 hacc.2.2 y]; exact harrisQ_le_hitProb P α y)
  refine theorem_17_2_2 P hacc.1 ha (hhit a) (Measure.dirac x) ?_ hgm hg2 hL2 hZ
  rw [pathMeasure_dirac]
  exact ae_firstHit_ne_top_of_hitProb_eq_one P hacc.1.1 (hhit x)

end MeynTweedie.GeneralizedDrift

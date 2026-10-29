/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.MartingaleLIL
import GeneralizedDrift.DependentLIL
import GeneralizedDrift.CLTCriteria

/-!
# The LIL for Markov chains through Poisson's equation (MT §17.4–17.5)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/MartingaleLILChains.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Meyn and Tweedie state the LIL alongside the CLT throughout §17.4–17.5 (Theorem 17.0.1 (iv),
p. 422; "the CLT and LIL hold", Theorems 17.5.3 and 17.5.4, pp. 452–453), and prove it through
the split chain of an `m`-skeleton. Here it is proved from the martingale LIL (`MartingaleLIL`)
for the Poisson martingale `Mₙ(g)` (17.43), which needs neither aperiodicity nor a minorization:
for a Harris chain with invariant probability `π` and a solution `ĝ` of `ĝ − Pĝ = g − c` with
`ĝ, Pĝ ∈ L²(π)`, from every initial law, `Sₙ(g − c)` obeys the LIL with constant
`γ_g = √(π(ĝ² − (Pĝ)²))` (17.46), the constant of the CLT (Theorem 17.4.5).

**Tools.**
* `HasLIL.comp_add`, `HasLIL.of_comp_add`, `hasLIL_shift_iff`, `pathSum_shift`,
  `isShiftInvariant_hasLIL`: the LIL event of `Sₙ(f)` is shift-invariant, so Proposition 17.1.6
  carries it from `P_π` to every `P_μ`.
* `integral_kernel_comp_real`; `ae_tendsto_avg_condExp_shift`: for `H ∈ L¹(P_π)`,
  `(1/n) Σ_{k<n} E_π[H ∘ θᵏ | 𝓕ₖ^Φ] → E_π[H]` a.s. (the Markov property and Birkhoff's theorem;
  this is how (D.8) and (D.9) are verified on MT p. 448).
* `ae_tendsto_coord_div_sqrt`: `n^{−1/2} h(Φₙ) → 0` `P_π`-a.s. for `h ∈ L²(π)`.

**Results.**
* `hasLIL_poissonMart_stationary`: the martingale `Mₙ(g)` obeys the LIL with constant `γ_g`
  under `P_π`.
* `hasLIL_pathSum_poisson_stationary`: `Sₙ(g − c)` obeys the LIL under `P_π`, by (17.44)
  (`Sₙ(g − c) = Mₙ(g) + Pĝ(Φ₀) − Pĝ(Φₙ)`).
* **`hasLIL_pathSum_poisson`**, `hasLIL_pathSum_poisson_initial`: the LIL under every `P_μ` and
  every `P_x`; `limsup_liminf_pathSum_poisson`: the `limsup`/`liminf` form. The applications
  to Theorems 17.0.1 (iv), 17.5.3, 17.5.4 and to §17.6 are in `MartingaleLILApplications`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### The LIL is a shift-invariant property -/

/-- Shifting the index by `m` keeps the LIL (`γ ≥ 0`). -/
theorem HasLIL.comp_add {s : ℕ → ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (h : HasLIL s γ) (m : ℕ) :
    HasLIL (fun n => s (n + m)) γ := by
  have hT : Tendsto (fun n : ℕ => ((n + m : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + (m : ℝ) * (1 / (n : ℝ))) atTop (𝓝 (1 + m * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat)
    rw [mul_zero, add_zero] at this
    refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    push_cast
    field_simp
  have h1 := h.comp_index hγ (T := fun n => n + m) (fun n => by omega) one_pos hT
  rwa [Real.sqrt_one, one_mul] at h1

/-- The LIL does not see the first `m` terms: `HasLIL (n ↦ s(n + m)) γ` gives `HasLIL s γ`
(`γ ≥ 0`). -/
theorem HasLIL.of_comp_add {s : ℕ → ℝ} {γ : ℝ} (hγ : 0 ≤ γ) {m : ℕ}
    (h : HasLIL (fun n => s (n + m)) γ) : HasLIL s γ := by
  have hT : Tendsto (fun n : ℕ => ((n - m : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 - (m : ℝ) * (1 / (n : ℝ))) atTop (𝓝 (1 - m * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat)
    rw [mul_zero, sub_zero] at this
    refine this.congr' (eventually_atTop.2 ⟨m + 1, fun n hn => ?_⟩)
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    change 1 - (m : ℝ) * (1 / (n : ℝ)) = ((n - m : ℕ) : ℝ) / n
    rw [Nat.cast_sub (by omega)]
    field_simp
  have h1 := h.comp_index hγ (T := fun n => n - m) (fun n => by omega) one_pos hT
  rw [Real.sqrt_one, one_mul] at h1
  refine h1.of_tendsto_sub (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop m] with n hn
  simp only [Nat.sub_add_cancel hn, sub_self, zero_div]

/-- **The LIL is shift-invariant**: `HasLIL (n ↦ s(m + n) − s(m)) γ ↔ HasLIL s γ` for `γ ≥ 0`. -/
theorem hasLIL_shift_iff {s : ℕ → ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (m : ℕ) :
    HasLIL (fun n => s (m + n) - s m) γ ↔ HasLIL s γ := by
  have hc : Tendsto (fun n => s m / lilScale n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_lilScale
  constructor
  · intro h
    refine HasLIL.of_comp_add hγ (m := m) (h.of_tendsto_sub ?_)
    refine hc.congr fun n => ?_
    rw [add_comm m n]; ring
  · intro h
    refine (h.comp_add hγ m).of_tendsto_sub ?_
    have := hc.neg
    rw [neg_zero] at this
    refine this.congr fun n => ?_
    rw [add_comm m n]; ring

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- The partial sums along a shifted path: `Sₙ(f)(θᵐω) = S_{m+n}(f)(ω) − S_m(f)(ω)`. -/
theorem pathSum_shift (f : X → ℝ) (m n : ℕ) (ω : ℕ → X) :
    pathSum f n (shift m ω) = pathSum f (m + n) ω - pathSum f m ω := by
  rw [pathSum, pathSum, pathSum, Finset.sum_range_add, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [shift]
  rfl

omit [MeasurableSpace X] in
/-- The LIL event of the partial sums `Sₙ(f)` is shift-invariant. -/
theorem isShiftInvariant_hasLIL (f : X → ℝ) {γ : ℝ} (hγ : 0 ≤ γ) :
    IsShiftInvariant {ω : ℕ → X | HasLIL (fun n => pathSum f n ω) γ} := by
  intro m ω
  simp only [mem_ofPred_eq]
  simp_rw [pathSum_shift]
  exact hasLIL_shift_iff (s := fun n => pathSum f n ω) hγ m

/-! ### Conditional ergodic averages under `P_π` -/

/-- `∫ f d(κ ∘ μ) = ∫ ∫ f dκ(y) μ(dy)` for real integrable `f` (as in `FunctionalCLT`). -/
theorem integral_kernel_comp_real {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (κ : Kernel Y Z) [IsSFiniteKernel κ] (ν : Measure Y) [SFinite ν] {f : Z → ℝ}
    (hf : Integrable f (κ ∘ₘ ν)) : ∫ z, f z ∂(κ ∘ₘ ν) = ∫ y, ∫ z, f z ∂κ y ∂ν := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The ergodic theorem for conditional expectations** (as in the verification of (D.8) and
(D.9), MT p. 448): for a Harris chain with invariant probability `π` and `H ∈ L¹(P_π)`,
`P_π`-almost surely `(1/n) Σ_{k<n} E_π[H ∘ θᵏ | 𝓕ₖ^Φ] → E_π[H]`. By the Markov property the
conditional expectations are `h(Φₖ)`, `h(x) = E_x[H]`, and Birkhoff's theorem applies. -/
theorem ae_tendsto_avg_condExp_shift {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {H : (ℕ → X) → ℝ} (hHm : Measurable H) (hHi : Integrable H (pathMeasure P π)) :
    ∀ᵐ ω ∂pathMeasure P π, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      (pathMeasure P π)[fun ω => H (shift k ω) | natFilt k] ω) / n) atTop
      (𝓝 (∫ ω, H ω ∂pathMeasure P π)) := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  set h : X → ℝ := fun x => ∫ ω, H ω ∂pathKernel P x with hh
  have hhm : Measurable h :=
    (StronglyMeasurable.integral_kernel hHm.stronglyMeasurable).measurable
  have hcomp : Integrable H (pathKernel P ∘ₘ π) := by rw [← pathMeasure_eq_comp]; exact hHi
  have hhi : Integrable h π := by
    have h2 := ((Measure.integrable_comp_iff hcomp.1).1 hcomp).2
    refine h2.mono' hhm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    exact norm_integral_le_integral_norm _
  have hhint : ∫ x, h x ∂π = ∫ ω, H ω ∂pathMeasure P π := by
    rw [pathMeasure_eq_comp, integral_kernel_comp_real _ _ hcomp]
  -- the Markov property
  have hmk : ∀ k, (pathMeasure P π)[fun ω => H (shift k ω) | natFilt k]
      =ᵐ[pathMeasure P π] fun ω => h (ω k) := fun k => by
    have hint : Integrable (fun ω => H (shift k ω)) (pathMeasure P π) := by
      have h1 := hHi
      rw [← (measurePreserving_shift hπ k).map_eq] at h1
      exact h1.comp_measurable (measurable_shift k)
    exact markov_property P π k hHm hint
  -- Birkhoff's theorem for `h(Φ₀)`
  have hFi : Integrable (fun ω : ℕ → X => h (ω 0)) (pathMeasure P π) :=
    integrable_coord_of_invariant P hπ hhi 0
  have hFint : ∫ ω, h (ω 0) ∂pathMeasure P π = ∫ x, h x ∂π := by
    rw [show ∫ x, h x ∂π = ∫ x, h x ∂((pathMeasure P π).map fun ω => ω 0) by
      rw [hπ.map_coord 0], integral_map (measurable_pi_apply 0).aemeasurable
      hhm.aestronglyMeasurable]
  have hb := ae_tendsto_birkhoffAverage_of_ergodic (measurePreserving_shift hπ 1)
    (hhm.comp (measurable_pi_apply 0)) hFi (ergodic_pathMeasure hH π)
  rw [show (h ∘ fun f : ℕ → X => f 0) = fun ω => h (ω 0) from rfl, hFint, hhint] at hb
  filter_upwards [hb, ae_all_iff.2 hmk] with ω hω hkω
  refine hω.congr fun n => ?_
  rw [birkhoffAverage_shift_eq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hkω k]
  simp only [shift, add_zero]

/-! ### The LIL for the Poisson martingale and for the chain -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The martingale LIL for `Mₙ(g)` under `P_π`**: for a Harris chain with invariant probability
`π` and `ĝ, Pĝ ∈ L²(π)`, the martingale `Mₙ(g) = Σ_{k=1}^n [ĝ(Φₖ) − Pĝ(Φₖ₋₁)]` (17.43) obeys the
LIL with constant `γ_g = √(π(ĝ² − (Pĝ)²))` (17.46), `P_π`-a.s. Its increments are identically
distributed under `P_π`, and their conditional variances and conditional truncated second
moments obey the ergodic theorem (`ae_tendsto_avg_condExp_shift`), so `hasLIL_martingale`
applies. -/
theorem hasLIL_poissonMart_stationary {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {gh : X → ℝ} (hghm : Measurable gh) (hgh2 : MemLp gh 2 π)
    (hPgh2 : MemLp (kernelInt P gh) 2 π) :
    ∀ᵐ ω ∂pathMeasure P π, HasLIL (fun n => poissonMart P gh n ω)
      (√(∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π)) := by
  have := isProbabilityMeasure_pathMeasure P π
  have hPm := measurable_kernelInt P hghm
  obtain ⟨hD, hL2, h0, hsq⟩ := poisson_increment_props P hπ hghm hgh2 hPgh2
  set D : ℕ → (ℕ → X) → ℝ := fun k ω => gh (ω (k + 1)) - kernelInt P gh (ω k) with hDdef
  have hD0m : Measurable (D 0) :=
    (hghm.comp (measurable_pi_apply 1)).sub (hPm.comp (measurable_pi_apply 0))
  have hshift : ∀ k, (fun ω => D 0 (shift k ω)) = D k := fun k => by
    funext ω
    simp only [hDdef, shift, add_zero, zero_add]
  have hident : ∀ k, IdentDistrib (D k) (D 0) (pathMeasure P π) (pathMeasure P π) := fun k =>
    ⟨(hD k).measurable.mono (natFilt.le _) le_rfl |>.aemeasurable, hD0m.aemeasurable, by
      rw [← hshift k, show (fun ω => D 0 (shift k ω)) = D 0 ∘ shift k from rfl,
        ← Measure.map_map hD0m (measurable_shift k), (measurePreserving_shift hπ k).map_eq]⟩
  -- the conditional variances
  have hV : ∀ᵐ ω ∂pathMeasure P π, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      (pathMeasure P π)[fun ω => D k ω ^ 2 | natFilt k] ω) / n) atTop
      (𝓝 (∫ ω, D 0 ω ^ 2 ∂pathMeasure P π)) := by
    have h1 := ae_tendsto_avg_condExp_shift hH hπ (H := fun ω => D 0 ω ^ 2)
      (hD0m.pow_const 2) (hL2 0).integrable_sq
    filter_upwards [h1] with ω hω
    exact hω.congr fun n => rfl
  -- the conditional truncated second moments
  have hT : ∀ K : ℕ, ∀ᵐ ω ∂pathMeasure P π, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      (pathMeasure P π)[fun ω => {ω | (K : ℝ) ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω |
        natFilt k] ω) / n) atTop
      (𝓝 (∫ ω, {ω | (K : ℝ) ≤ D 0 ω ^ 2}.indicator (fun ω => D 0 ω ^ 2) ω
        ∂pathMeasure P π)) := by
    intro K
    have hset : MeasurableSet {ω | (K : ℝ) ≤ D 0 ω ^ 2} :=
      measurableSet_le measurable_const (hD0m.pow_const 2)
    have h1 := ae_tendsto_avg_condExp_shift hH hπ
      (H := fun ω => {ω | (K : ℝ) ≤ D 0 ω ^ 2}.indicator (fun ω => D 0 ω ^ 2) ω)
      ((hD0m.pow_const 2).indicator hset) ((hL2 0).integrable_sq.indicator hset)
    filter_upwards [h1] with ω hω
    exact hω.congr fun n => rfl
  have hlil := hasLIL_martingale hD h0 hident (hL2 0) hV hT
  rw [hsq 0] at hlil
  exact hlil

/-- Under `P_π`, `n^{−1/2} h(Φₙ) → 0` almost surely for `h ∈ L²(π)`. -/
theorem ae_tendsto_coord_div_sqrt {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {h : X → ℝ} (hm : Measurable h)
    (h2 : MemLp h 2 π) :
    ∀ᵐ ω ∂pathMeasure P π, Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * h (ω n)) atTop (𝓝 0) := by
  have := isProbabilityMeasure_pathMeasure P π
  set Z : ℕ → (ℕ → X) → ℝ := fun n ω => h (ω n) with hZ
  have hlaw : ∀ n, (pathMeasure P π).map (Z n) = π.map h := fun n => by
    change (pathMeasure P π).map (h ∘ fun ω => ω n) = π.map h
    rw [← Measure.map_map hm (measurable_pi_apply n), hπ.map_coord n]
  have hident : ∀ n, IdentDistrib (Z n) (Z 0) (pathMeasure P π) (pathMeasure P π) := fun n =>
    ⟨(hm.comp (measurable_pi_apply n)).aemeasurable, (hm.comp (measurable_pi_apply 0)).aemeasurable,
      by rw [hlaw n, hlaw 0]⟩
  have hZ2 : MemLp (Z 0) 2 (pathMeasure P π) := by
    have : MemLp h 2 ((pathMeasure P π).map fun ω => ω 0) := by rw [hπ.map_coord 0]; exact h2
    exact this.comp_of_map (measurable_pi_apply 0).aemeasurable
  filter_upwards [ae_tendsto_sq_div_of_identDistrib hident hZ2] with ω hω
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have h2' := hω.mul h1
  rw [zero_mul] at h2'
  have h3 := (Real.continuous_sqrt.tendsto _).comp h2'
  rw [Real.sqrt_zero] at h3
  refine squeeze_zero_norm' (Eventually.of_forall fun n => le_of_eq ?_) h3
  simp only [Function.comp_apply, hZ]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_mul, norm_zero, zero_add,
      div_zero, mul_zero]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hn0)),
      show h (ω n) ^ 2 / ((n : ℝ) + 1) * (((n : ℝ) + 1) / n) = h (ω n) ^ 2 / n by field_simp,
      Real.sqrt_div' _ hn0.le, Real.sqrt_sq_eq_abs, inv_mul_eq_div]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The LIL for the stationary chain**: for a Harris chain with invariant probability `π` and a
solution `ĝ` of Poisson's equation `ĝ − Pĝ = g − c` with `ĝ, Pĝ ∈ L²(π)`, `P_π`-a.s. `Sₙ(g − c)`
obeys the LIL with constant `γ_g = √(π(ĝ² − (Pĝ)²))`: by (17.44),
`Sₙ(g − c) = Mₙ(g) + Pĝ(Φ₀) − Pĝ(Φₙ)`, the martingale obeys the LIL
(`hasLIL_poissonMart_stationary`) and the remainder is `o(√n)`. -/
theorem hasLIL_pathSum_poisson_stationary {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g gh : X → ℝ} {c : ℝ} (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh)
    (hgh2 : MemLp gh 2 π) (hPgh2 : MemLp (kernelInt P gh) 2 π) :
    ∀ᵐ ω ∂pathMeasure P π, HasLIL (fun n => pathSum (fun x => g x - c) n ω)
      (√(∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π)) := by
  have hPm := measurable_kernelInt P hghm
  filter_upwards [hasLIL_poissonMart_stationary hH hπ hghm hgh2 hPgh2,
    ae_tendsto_coord_div_sqrt hπ hPm hPgh2] with ω hM hR
  refine hM.of_tendsto_sub (tendsto_div_lilScale_of_sqrt ?_)
  have h0 : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * kernelInt P gh (ω 0)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      tendsto_natCast_atTop_atTop)).mul_const (kernelInt P gh (ω 0))
    rwa [zero_mul] at this
  have h1 := h0.sub hR
  rw [sub_zero] at h1
  refine h1.congr fun n => ?_
  rw [pathSum_eq_poissonMart hsol n ω]
  ring

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The LIL for a Harris chain with a Poisson solution, from every initial law** (MT §17.4–17.5,
"the CLT and LIL hold", without aperiodicity or a minorization): for a Harris chain with invariant
probability `π` and a solution `ĝ` of `ĝ − Pĝ = g − c` with `ĝ, Pĝ ∈ L²(π)`, under every initial
law `μ`, `P_μ`-a.s. `Sₙ(g − c)` obeys the LIL with constant `γ_g = √(π(ĝ² − (Pĝ)²))`. The LIL event
is shift-invariant (`isShiftInvariant_hasLIL`), so it passes from `P_π` to every `P_μ` by
Proposition 17.1.6. -/
theorem hasLIL_pathSum_poisson {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g gh : X → ℝ} {c : ℝ} (hsol : IsPoissonSolution P g gh c) (hgm : Measurable g)
    (hghm : Measurable gh) (hgh2 : MemLp gh 2 π) (hPgh2 : MemLp (kernelInt P gh) 2 π)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂pathMeasure P μ, HasLIL (fun n => pathSum (fun x => g x - c) n ω)
      (√(∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π)) := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isProbabilityMeasure_pathMeasure P μ
  set E := {ω : ℕ → X | HasLIL (fun n => pathSum (fun x => g x - c) n ω)
    (√(∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π))} with hE
  have hEm : MeasurableSet E :=
    measurableSet_hasLIL (fun n => measurable_pathSum (hgm.sub measurable_const) n) _
  have hinv : IsShiftInvariant E := isShiftInvariant_hasLIL _ (Real.sqrt_nonneg _)
  have h1 : pathMeasure P π E = 1 := (mem_ae_iff_prob_eq_one hEm).1
    (hasLIL_pathSum_poisson_stationary hH hπ hsol hghm hgh2 hPgh2)
  exact (mem_ae_iff_prob_eq_one hEm).2 (proposition_17_1_6_measure hH hEm hinv π h1 μ)

variable [MeasurableSpace.CountablyGenerated X] in
/-- `hasLIL_pathSum_poisson` from every initial state `x` (under `P_x`). -/
theorem hasLIL_pathSum_poisson_initial {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g gh : X → ℝ} {c : ℝ} (hsol : IsPoissonSolution P g gh c) (hgm : Measurable g)
    (hghm : Measurable gh) (hgh2 : MemLp gh 2 π) (hPgh2 : MemLp (kernelInt P gh) 2 π) (x : X) :
    haveI := isMarkovKernel_pathKernel P
    ∀ᵐ ω ∂pathKernel P x, HasLIL (fun n => pathSum (fun x => g x - c) n ω)
      (√(∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π)) := by
  have h := hasLIL_pathSum_poisson hH hπ hsol hgm hghm hgh2 hPgh2 (Measure.dirac x)
  rwa [pathMeasure_dirac] at h

variable [MeasurableSpace.CountablyGenerated X] in
/-- `hasLIL_pathSum_poisson` in `limsup`/`liminf` form: `P_μ`-a.s.
`limsup Sₙ(g − c)/√(2 n log log n) = γ_g` and `liminf Sₙ(g − c)/√(2 n log log n) = −γ_g`. -/
theorem limsup_liminf_pathSum_poisson {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g gh : X → ℝ} {c : ℝ} (hsol : IsPoissonSolution P g gh c) (hgm : Measurable g)
    (hghm : Measurable gh) (hgh2 : MemLp gh 2 π) (hPgh2 : MemLp (kernelInt P gh) 2 π)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂pathMeasure P μ,
      limsup (fun n => pathSum (fun x => g x - c) n ω / lilScale n) atTop =
        √(∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π) ∧
      liminf (fun n => pathSum (fun x => g x - c) n ω / lilScale n) atTop =
        -√(∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π) := by
  filter_upwards [hasLIL_pathSum_poisson hH hπ hsol hgm hghm hgh2 hPgh2 μ] with ω hω
  exact ⟨hω.limsup_eq, hω.liminf_eq⟩

end MeynTweedie.GeneralizedDrift

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StationaryDistributions.HopenhaynPrescott

/-!
# Asset distributions induced by saving rules

In a Bewley–Huggett–Aiyagari economy with i.i.d. income `z ∼ π`, a household with assets at grid
point `i` and income `z` moves to grid point `σ(i, z)`. Assets then follow the Markov chain
`P_σ(i, j) = ∑_z π(z)𝟙{σ(i, z) = j}` (`policyKernel`).

* `policyKernel_isKernel`, `policyKernel_isMonotone`: `P_σ` is a Markov kernel, and it is
  monotone when `σ` is increasing in assets — the conclusion of Topkis's theorem for the savings
  problem (`Extensions/MonotonePolicies`).
* `policyKernel_le`: a pointwise higher saving rule gives FOSD-higher rows.
* `aggregate_assets_mono`: if `σ ≤ σ'` are increasing saving rules and `P_σ` satisfies monotone
  mixing, the stationary asset distribution under `σ` is below every stationary distribution
  under `σ'`, so aggregate assets `∑ ψ(i) level(i)` are lower. This is the monotonicity of
  aggregate capital supply in any parameter that raises the saving rule.
-/

open Finset Filter Topology

namespace DPExtensions.StationaryDistributions

variable {Z : Type*} [Fintype Z] {n : ℕ}

/-- The asset chain under the saving rule `σ` with i.i.d. income `π`. -/
def policyKernel (π : Z → ℝ) (σ : ℕ → Z → ℕ) (i j : ℕ) : ℝ :=
  ∑ z, π z * if σ i z = j then 1 else 0

theorem cdf_policyKernel (π : Z → ℝ) (σ : ℕ → Z → ℕ) (i y : ℕ) :
    cdf (policyKernel π σ i) y = ∑ z, π z * if σ i z ≤ y then 1 else 0 := by
  simp only [cdf, policyKernel]
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [← mul_sum, sum_ite_eq]
  simp only [mem_range, Nat.lt_succ_iff]

theorem policyKernel_isKernel {π : Z → ℝ} (hπ0 : ∀ z, 0 ≤ π z) (hπ1 : ∑ z, π z = 1)
    {σ : ℕ → Z → ℕ} (hσ : ∀ i ≤ n, ∀ z, σ i z ≤ n) : IsKernel n (policyKernel π σ) := by
  refine ⟨fun i j => sum_nonneg fun z _ => mul_nonneg (hπ0 z) (by split_ifs <;> norm_num),
    fun i hi => ?_⟩
  rw [cdf_policyKernel]
  calc ∑ z, π z * (if σ i z ≤ n then (1 : ℝ) else 0) = ∑ z, π z :=
        sum_congr rfl fun z _ => by simp [hσ i hi z]
    _ = 1 := hπ1

/-- An increasing saving rule gives a monotone asset chain. -/
theorem policyKernel_isMonotone {π : Z → ℝ} (hπ0 : ∀ z, 0 ≤ π z) {σ : ℕ → Z → ℕ}
    (hσ : ∀ z, Monotone fun i => σ i z) : IsMonotone n (policyKernel π σ) := by
  intro i i' hii' _ y _
  rw [cdf_policyKernel, cdf_policyKernel]
  refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hπ0 z)
  have := hσ z hii'
  simp only at this
  split_ifs <;> first | omega | norm_num

/-- A pointwise higher saving rule has FOSD-higher rows. -/
theorem policyKernel_le {π : Z → ℝ} (hπ0 : ∀ z, 0 ≤ π z) {σ σ' : ℕ → Z → ℕ}
    (h : ∀ i z, σ i z ≤ σ' i z) (i y : ℕ) :
    cdf (policyKernel π σ' i) y ≤ cdf (policyKernel π σ i) y := by
  rw [cdf_policyKernel, cdf_policyKernel]
  refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hπ0 z)
  have := h i z
  split_ifs <;> first | omega | norm_num

/-- **Aggregate assets rise with the saving rule.** If `σ ≤ σ'` and `P_σ` is monotone and
mixing, the stationary asset distribution under `σ` is FOSD-below every stationary distribution
under `σ'`, and aggregate assets `∑_i ψ(i)·level(i)` are lower for every increasing grid
`level`. -/
theorem aggregate_assets_mono {π : Z → ℝ} (hπ0 : ∀ z, 0 ≤ π z) (hπ1 : ∑ z, π z = 1)
    {σ σ' : ℕ → Z → ℕ} (hσn : ∀ i ≤ n, ∀ z, σ i z ≤ n)
    (hσm : ∀ z, Monotone fun i => σ i z) (hσσ' : ∀ i z, σ i z ≤ σ' i z)
    (hmix : MonotoneMixing n (policyKernel π σ)) {ψ ψ' : ℕ → ℝ} (hd : IsDist n ψ)
    (hs : IsStationary n (policyKernel π σ) ψ) (hd' : IsDist n ψ')
    (hs' : IsStationary n (policyKernel π σ') ψ') {level : ℕ → ℝ}
    (hlevel : ∀ i < n, level i ≤ level (i + 1)) :
    Dominated n ψ ψ' ∧
      ∑ i ∈ range (n + 1), ψ i * level i ≤ ∑ i ∈ range (n + 1), ψ' i * level i := by
  have h := stationary_mono (policyKernel_isKernel hπ0 hπ1 hσn) (policyKernel_isMonotone hπ0 hσm)
    hmix (fun i _ y _ => policyKernel_le hπ0 hσσ' i y) hd hs hd' hs'
  exact ⟨h.1, h.2 level hlevel⟩

end DPExtensions.StationaryDistributions

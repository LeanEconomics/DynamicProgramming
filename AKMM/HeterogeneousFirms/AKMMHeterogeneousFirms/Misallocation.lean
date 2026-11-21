/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMHeterogeneousFirms.Lognormal

/-!
# Reallocation and misallocation (AKMM §22.3–22.4)

AKMM, §22.3, pp. 668–669 ((22.9)), §22.4, pp. 671–673, and footnote 14, p. 676.

* **Job flows (22.9)**: job creation minus job destruction is the net change in employment,
  `JC − JD = (L_t − L_{t−1})/L̄_t` (`jobflows_net`); in a steady state `JC = JD` (footnote 14,
  `jobflows_steady`).
* **The FHK decomposition** (p. 671): the exact identity for the change in output-weighted
  productivity with continuers, entrants and exiters (`fhk_decomposition`); without share changes,
  entry or exit only within-firm growth remains (`fhk_within_only`).
* **The planner bound**: any allocation of total input `M` produces at most `AM^γ`
  (`simple_planner_A`).
* **Wedges (22.10)**: firms facing output taxes `τ` choose `m = m*(γ, c, (1−τ)a)` and then
  `Y = AM^γ` with `A` of (22.10) (`eq_22_10`); **misallocation lowers TFP**: for every
  distribution of `(a, τ)`, `A` of (22.10) is at most `A` of (22.6) (`wedge_A_le`). The book
  shows this only for the lognormal case (22.11).
-/

open MeasureTheory

namespace AKMM.HeterogeneousFirms

/-! ### Job flows -/

/-- AKMM, (22.9), p. 669: job creation `Σ_{ℓ_t > ℓ_{t−1}} (ℓ_t − ℓ_{t−1}) / L̄`; entrants have
`ℓ_{t−1} = 0`, exiters `ℓ_t = 0`. -/
noncomputable def jobCreation {ι : Type*} (S : Finset ι) (l0 l1 : ι → ℝ) (Lbar : ℝ) : ℝ :=
  (∑ i ∈ S.filter (fun i => l0 i < l1 i), (l1 i - l0 i)) / Lbar

/-- AKMM, p. 669: job destruction `Σ_{ℓ_t < ℓ_{t−1}} (ℓ_{t−1} − ℓ_t) / L̄`. -/
noncomputable def jobDestruction {ι : Type*} (S : Finset ι) (l0 l1 : ι → ℝ) (Lbar : ℝ) : ℝ :=
  (∑ i ∈ S.filter (fun i => l1 i < l0 i), (l0 i - l1 i)) / Lbar

/-- AKMM, p. 669: **gross and net flows**. `JC − JD = (L_t − L_{t−1})/L̄`. -/
theorem jobflows_net {ι : Type*} (S : Finset ι) (l0 l1 : ι → ℝ) (Lbar : ℝ) :
    jobCreation S l0 l1 Lbar - jobDestruction S l0 l1 Lbar =
      (∑ i ∈ S, l1 i - ∑ i ∈ S, l0 i) / Lbar := by
  classical
  unfold jobCreation jobDestruction
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  have h1 : ∑ i ∈ S.filter (fun i => l0 i < l1 i), (l1 i - l0 i) =
      ∑ i ∈ S, if l0 i < l1 i then l1 i - l0 i else 0 := Finset.sum_filter _ _
  have h2 : ∑ i ∈ S.filter (fun i => l1 i < l0 i), (l0 i - l1 i) =
      ∑ i ∈ S, if l1 i < l0 i then l0 i - l1 i else 0 := Finset.sum_filter _ _
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases lt_trichotomy (l0 i) (l1 i) with h | h | h
  · simp [h, h.not_gt]
  · simp [h]
  · simp [h, h.not_gt]

/-- AKMM, p. 676, footnote 14: **in a steady state job creation equals job destruction**. -/
theorem jobflows_steady {ι : Type*} (S : Finset ι) (l0 l1 : ι → ℝ) (Lbar : ℝ)
    (hL : ∑ i ∈ S, l1 i = ∑ i ∈ S, l0 i) :
    jobCreation S l0 l1 Lbar = jobDestruction S l0 l1 Lbar := by
  have h := jobflows_net S l0 l1 Lbar
  rw [hL, sub_self, zero_div] at h
  linarith

/-! ### The Foster–Haltiwanger–Krizan decomposition -/

/-- AKMM, p. 671: **the FHK decomposition**. Let `C`, `N`, `X` be the continuing, entering and
exiting establishments, with output shares `s₀` (at `t−1`, on `C ∪ X`) and `s₁` (at `t`, on
`C ∪ N`) summing to one, and `Ā₀ = Σ_{C∪X} s₀a₀`, `Ā₁ = Σ_{C∪N} s₁a₁`. Then `Ā₁ − Ā₀` is the sum
of the within, between, cross, entry and exit terms. -/
theorem fhk_decomposition {ι : Type*} (C N X : Finset ι) (s0 s1 a0 a1 : ι → ℝ)
    (h0 : ∑ i ∈ C, s0 i + ∑ i ∈ X, s0 i = 1) (h1 : ∑ i ∈ C, s1 i + ∑ i ∈ N, s1 i = 1) :
    (∑ i ∈ C, s1 i * a1 i + ∑ i ∈ N, s1 i * a1 i) -
        (∑ i ∈ C, s0 i * a0 i + ∑ i ∈ X, s0 i * a0 i) =
      ∑ i ∈ C, s0 i * (a1 i - a0 i) +
        ∑ i ∈ C, (a0 i - (∑ j ∈ C, s0 j * a0 j + ∑ j ∈ X, s0 j * a0 j)) * (s1 i - s0 i) +
        ∑ i ∈ C, (a1 i - a0 i) * (s1 i - s0 i) +
        ∑ i ∈ N, s1 i * (a1 i - (∑ j ∈ C, s0 j * a0 j + ∑ j ∈ X, s0 j * a0 j)) -
        ∑ i ∈ X, s0 i * (a0 i - (∑ j ∈ C, s0 j * a0 j + ∑ j ∈ X, s0 j * a0 j)) := by
  set A0 := ∑ j ∈ C, s0 j * a0 j + ∑ j ∈ X, s0 j * a0 j
  have e1 : ∑ i ∈ C, (a0 i - A0) * (s1 i - s0 i) =
      ∑ i ∈ C, a0 i * (s1 i - s0 i) - A0 * (∑ i ∈ C, s1 i - ∑ i ∈ C, s0 i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ N, s1 i * (a1 i - A0) = ∑ i ∈ N, s1 i * a1 i - A0 * ∑ i ∈ N, s1 i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i ∈ X, s0 i * (a0 i - A0) = ∑ i ∈ X, s0 i * a0 i - A0 * ∑ i ∈ X, s0 i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : ∑ i ∈ C, s1 i * a1 i - ∑ i ∈ C, s0 i * a0 i =
      ∑ i ∈ C, s0 i * (a1 i - a0 i) + ∑ i ∈ C, a0 i * (s1 i - s0 i) +
        ∑ i ∈ C, (a1 i - a0 i) * (s1 i - s0 i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3]
  linear_combination e4 - A0 * h0 + A0 * h1

/-- AKMM, p. 672: without share changes and without entry or exit, the only source of growth in
`Ā` is within-establishment productivity growth. -/
theorem fhk_within_only {ι : Type*} (C : Finset ι) (s a0 a1 : ι → ℝ) :
    ∑ i ∈ C, s i * a1 i - ∑ i ∈ C, s i * a0 i = ∑ i ∈ C, s i * (a1 i - a0 i) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The planner bound and wedges -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- AKMM, p. 665: **the aggregate production function is a frontier**. For any allocation
`m ≥ 0` with total `M = ∫ m > 0`, output is at most `AM^γ`, with `A` of (22.6). -/
theorem simple_planner_A {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) {a m : Ω → ℝ}
    (ha : ∀ ω, 0 < a ω) (hm : ∀ ω, 0 ≤ m ω) (hmI : Integrable m P)
    (hpI : Integrable (fun ω => a ω ^ (1 / (1 - γ))) P)
    (hyI : Integrable (fun ω => a ω * m ω ^ γ) P) (hI : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) ∂P)
    (hM : 0 < ∫ ω, m ω ∂P) :
    ∫ ω, a ω * m ω ^ γ ∂P ≤ aggTFP P γ a * (∫ ω, m ω ∂P) ^ γ := by
  set S := ∫ ω, a ω ^ (1 / (1 - γ)) ∂P
  set M := ∫ ω, m ω ∂P
  have h1γ : 0 < 1 - γ := by linarith
  set c := γ * (S / M) ^ (1 - γ) with hcdef
  have hc : 0 < c := by positivity
  have hγc : γ / c = (M / S) ^ (1 - γ) := by
    rw [hcdef, div_mul_eq_div_div, div_self hγ.ne', one_div, ← Real.inv_rpow (by positivity),
      inv_div]
  have hsum : ∫ ω, simpleScale γ c (a ω) ∂P = M := by
    rw [simple_M_eq P hc hγ ha, hγc, ← Real.rpow_mul (by positivity), mul_one_div_cancel
      h1γ.ne', Real.rpow_one, div_mul_cancel₀ _ hI.ne']
  have hsI : Integrable (fun ω => simpleScale γ c (a ω)) P := by
    have : (fun ω => simpleScale γ c (a ω)) =
        fun ω => (γ / c) ^ (1 / (1 - γ)) * a ω ^ (1 / (1 - γ)) :=
      funext fun ω => simple_scale_eq hc hγ (ha ω)
    rw [this]; exact hpI.const_mul _
  have hYI : Integrable (fun ω => a ω * simpleScale γ c (a ω) ^ γ) P := by
    have : (fun ω => a ω * simpleScale γ c (a ω) ^ γ) =
        fun ω => c / γ * simpleScale γ c (a ω) :=
      funext fun ω => simple_output_eq hc hγ hγ1 (ha ω)
    rw [this]; exact hsI.const_mul _
  have h := simple_planner P hc hγ hγ1 ha hm hmI hsI hYI hyI (by rw [hsum])
  rw [eq_22_7_M P hc hγ hγ1 ha hI, hsum] at h
  exact h

/-- `(γb a/c)^{1/(1−γ)}`-scales with wedges: `a·m^γ = a^{1/(1−γ)}b^{γ/(1−γ)}·K^γ` and
`m = a^{1/(1−γ)}b^{1/(1−γ)}·K` where `K = (γ/c)^{1/(1−γ)}`. -/
theorem wedge_scale_eq {γ c a b : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1) (ha : 0 < a)
    (hb : 0 < b) :
    simpleScale γ c (b * a) =
        (γ / c) ^ (1 / (1 - γ)) * (a ^ (1 / (1 - γ)) * b ^ (1 / (1 - γ))) ∧
      a * simpleScale γ c (b * a) ^ γ =
        ((γ / c) ^ (1 / (1 - γ))) ^ γ * (a ^ (1 / (1 - γ)) * b ^ (γ / (1 - γ))) := by
  have h1γ : 0 < 1 - γ := by linarith
  have hK : 0 < (γ / c) ^ (1 / (1 - γ)) := by positivity
  have hs := simple_scale_eq hc hγ (mul_pos hb ha)
  rw [Real.mul_rpow hb.le ha.le] at hs
  refine ⟨by rw [hs]; ring, ?_⟩
  rw [hs, Real.mul_rpow hK.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hb.le, ← Real.rpow_mul ha.le]
  have ea : a * a ^ (1 / (1 - γ) * γ) = a ^ (1 / (1 - γ)) := by
    rw [← Real.rpow_one_add' ha.le (by positivity)]
    congr 1; field_simp; ring
  have eb : 1 / (1 - γ) * γ = γ / (1 - γ) := by ring
  rw [eb] at ea ⊢
  calc a * (((γ / c) ^ (1 / (1 - γ))) ^ γ * (b ^ (γ / (1 - γ)) * a ^ (γ / (1 - γ))))
      = ((γ / c) ^ (1 / (1 - γ))) ^ γ * ((a * a ^ (γ / (1 - γ))) * b ^ (γ / (1 - γ))) := by
        ring
    _ = _ := by rw [ea]

/-- AKMM, (22.10), p. 672: **the aggregate production function with wedges**. Firm `i` solves
`max (1−τᵢ)aᵢmᵞ − cm`, i.e. the scale problem with productivity `bᵢaᵢ`, `bᵢ = 1 − τᵢ`
(`eq_22_1`), so `mᵢ = m*(γ, c, bᵢaᵢ)`; output `Y = ∫ aᵢmᵢ^γ` is `AM^γ` with `A` of (22.10). -/
theorem eq_22_10 {P : Measure Ω} {γ c : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1)
    {a b : Ω → ℝ} (ha : ∀ ω, 0 < a ω) (hb : ∀ ω, 0 < b ω)
    (hI : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) * b ω ^ (1 / (1 - γ)) ∂P) :
    ∫ ω, a ω * simpleScale γ c (b ω * a ω) ^ γ ∂P =
      wedgeTFP P γ a b * (∫ ω, simpleScale γ c (b ω * a ω) ∂P) ^ γ := by
  have hK : 0 < (γ / c) ^ (1 / (1 - γ)) := by positivity
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (wedge_scale_eq hc hγ hγ1 (ha ω) (hb ω)).2),
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (wedge_scale_eq hc hγ hγ1 (ha ω) (hb ω)).1), integral_const_mul, integral_const_mul,
    Real.mul_rpow hK.le hI.le, wedgeTFP]
  field_simp

/-- AKMM, pp. 672–673: **misallocation lowers TFP**, for any joint distribution of
productivity and wedges: `A` of (22.10) is at most `A` of (22.6). The wedge allocation is one
allocation of the same total input, so the planner bound `simple_planner_A` applies. -/
theorem wedge_A_le {P : Measure Ω} {γ c : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ < 1)
    {a b : Ω → ℝ} (ha : ∀ ω, 0 < a ω) (hb : ∀ ω, 0 < b ω)
    (hpI : Integrable (fun ω => a ω ^ (1 / (1 - γ))) P)
    (hmI : Integrable (fun ω => a ω ^ (1 / (1 - γ)) * b ω ^ (1 / (1 - γ))) P)
    (hyI : Integrable (fun ω => a ω ^ (1 / (1 - γ)) * b ω ^ (γ / (1 - γ))) P)
    (hI : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) ∂P)
    (hJ : 0 < ∫ ω, a ω ^ (1 / (1 - γ)) * b ω ^ (1 / (1 - γ)) ∂P) :
    wedgeTFP P γ a b ≤ aggTFP P γ a := by
  set K := (γ / c) ^ (1 / (1 - γ))
  have hK : 0 < K := by positivity
  have hm : ∀ ω, 0 ≤ simpleScale γ c (b ω * a ω) := fun ω =>
    (simple_scale_pos hc hγ (mul_pos (hb ω) (ha ω))).le
  have hmI' : Integrable (fun ω => simpleScale γ c (b ω * a ω)) P := by
    rw [show (fun ω => simpleScale γ c (b ω * a ω)) = fun ω =>
      K * (a ω ^ (1 / (1 - γ)) * b ω ^ (1 / (1 - γ))) from
      funext fun ω => (wedge_scale_eq hc hγ hγ1 (ha ω) (hb ω)).1]
    exact hmI.const_mul _
  have hyI' : Integrable (fun ω => a ω * simpleScale γ c (b ω * a ω) ^ γ) P := by
    rw [show (fun ω => a ω * simpleScale γ c (b ω * a ω) ^ γ) = fun ω =>
      K ^ γ * (a ω ^ (1 / (1 - γ)) * b ω ^ (γ / (1 - γ))) from
      funext fun ω => (wedge_scale_eq hc hγ hγ1 (ha ω) (hb ω)).2]
    exact hyI.const_mul _
  have hM : 0 < ∫ ω, simpleScale γ c (b ω * a ω) ∂P := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (wedge_scale_eq hc hγ hγ1 (ha ω) (hb ω)).1), integral_const_mul]
    positivity
  have h := simple_planner_A hγ hγ1 ha hm hmI' hpI hyI' hI hM
  rw [eq_22_10 hc hγ hγ1 ha hb hJ] at h
  exact le_of_mul_le_mul_right h (by positivity)

end AKMM.HeterogeneousFirms

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.FiniteHorizon
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Example 4.1: the finite-horizon model in closed form

AKMM, §4.2.4, Example 4.1, pp. 103–104: `u(c) = log c`, `f(k) = Ak^α`, `δ = 1`. With
`q = αβ` and `n = T − t` periods left after `t`, the saving rate is
`s_n = q(1 − qⁿ)/(1 − qⁿ⁺¹)`.

* `example41_rate_recursion`: `s_{n+1} = q/(1 + q − s_n)`, the backward-induction step, and
  `example41_rate_geometric`: `s_n = q(1 + q + ⋯ + q^{n−1})/(1 + q + ⋯ + qⁿ)`, the book's
  intermediate forms (`example41_kT`, `example41_kTminus1`).
* `example41_consumption_share`: `1 − s_n = (1 − q)/(1 − qⁿ⁺¹)`, the book's `c_t`.
* `eq_4_11`: the plan `k_{t+1} = s_{T−t}Ak_t^α` satisfies the Euler equation (4.11) for `t < T`,
  and `k_{T+1} = 0`.
* `example_4_1`: it is the unique maximizer of (P3) (via `ngm_finite_sufficient` and
  `ngm_finite_unique`).
-/

namespace AKMM.DynamicOptimization

open Real

/-- AKMM, p. 103: the saving rate with `n` periods left, `s_n = q(1 − qⁿ)/(1 − qⁿ⁺¹)`. -/
noncomputable def example41Rate (q : ℝ) (n : ℕ) : ℝ := q * (1 - q ^ n) / (1 - q ^ (n + 1))

theorem example41_rate_zero (q : ℝ) : example41Rate q 0 = 0 := by simp [example41Rate]

/-- AKMM, p. 103: the backward-induction step `s_{n+1} = q/(1 + q − s_n)`. -/
theorem example41_rate_recursion {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    example41Rate q (n + 1) = q / (1 + q - example41Rate q n) := by
  have h1 : 0 < 1 - q ^ (n + 1) := sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))
  have h2 : 0 < 1 - q ^ (n + 1 + 1) := sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))
  unfold example41Rate
  have e : 1 + q - q * (1 - q ^ n) / (1 - q ^ (n + 1)) =
      (1 - q ^ (n + 1 + 1)) / (1 - q ^ (n + 1)) := by
    field_simp; ring
  rw [e]
  field_simp

/-- AKMM, p. 103: the saving rate in geometric-sum form,
`s_n = q(1 + q + ⋯ + q^{n−1})/(1 + q + ⋯ + qⁿ)`. -/
theorem example41_rate_geometric {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    example41Rate q n = q * (∑ i ∈ Finset.range n, q ^ i) / ∑ i ∈ Finset.range (n + 1), q ^ i := by
  have hq : q ≠ 1 := hq1.ne
  rw [geom_sum_eq hq, geom_sum_eq hq, example41Rate]
  have h1 : (q - 1) ≠ 0 := sub_ne_zero.2 hq
  have h2 : 1 - q ^ (n + 1) ≠ 0 := (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))).ne'
  have h3 : q ^ (n + 1) - 1 ≠ 0 := by intro h; apply h2; linarith
  field_simp
  ring

/-- AKMM, p. 103: `k_T = (αβ/(1 + αβ))Ak_{T−1}^α`, i.e. `s₁ = q/(1 + q)`. -/
theorem example41_kT {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : example41Rate q 1 = q / (1 + q) := by
  rw [example41_rate_geometric hq0 hq1]; simp [Finset.sum_range_succ]

/-- AKMM, p. 103: `k_{T−1} = (αβ(1 + αβ)/(1 + αβ + (αβ)²))Ak_{T−2}^α`. -/
theorem example41_kTminus1 {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    example41Rate q 2 = q * (1 + q) / (1 + q + q ^ 2) := by
  rw [example41_rate_geometric hq0 hq1]; simp [Finset.sum_range_succ]

/-- AKMM, p. 103: the consumption share `1 − s_n = (1 − q)/(1 − qⁿ⁺¹)`, so
`c_t = ((1 − αβ)/(1 − (αβ)^{T−t+1}))Ak_t^α`. -/
theorem example41_consumption_share {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    1 - example41Rate q n = (1 - q) / (1 - q ^ (n + 1)) := by
  have h2 : 1 - q ^ (n + 1) ≠ 0 := (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))).ne'
  unfold example41Rate
  field_simp
  ring

theorem example41_rate_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    0 ≤ example41Rate q n :=
  div_nonneg (mul_nonneg hq0.le (sub_nonneg.2 (pow_le_one₀ hq0.le hq1.le)))
    (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))).le

theorem example41_rate_lt_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    example41Rate q n < 1 := by
  have h := example41_consumption_share hq0 hq1 n
  have : 0 < (1 - q) / (1 - q ^ (n + 1)) :=
    div_pos (by linarith) (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega)))
  linarith

theorem example41_rate_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {n : ℕ} (hn : 0 < n) :
    0 < example41Rate q n :=
  div_pos (mul_pos hq0 (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))))
    (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega)))

/-- The plan of Example 4.1: `k₀` given and `k_{t+1} = s_{T−t}Ak_t^α`. -/
noncomputable def example41Plan (A α β : ℝ) (T : ℕ) (k0 : ℝ) : ℕ → ℝ
  | 0 => k0
  | t + 1 => example41Rate (α * β) (T - t) * (A * example41Plan A α β T k0 t ^ α)

theorem example41_plan_succ (A α β : ℝ) (T : ℕ) (k0 : ℝ) (t : ℕ) :
    example41Plan A α β T k0 (t + 1) =
      example41Rate (α * β) (T - t) * (A * example41Plan A α β T k0 t ^ α) := rfl

variable {A α β : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
include hA hα0 hα1 hβ0 hβ1

theorem example41_plan_pos {T : ℕ} {k0 : ℝ} (hk0 : 0 < k0) {t : ℕ} (ht : t ≤ T) :
    0 < example41Plan A α β T k0 t := by
  have hq0 : 0 < α * β := mul_pos hα0 hβ0
  have hq1 : α * β < 1 := by nlinarith
  induction t with
  | zero => exact hk0
  | succ t ih =>
    rw [example41_plan_succ]
    exact mul_pos (example41_rate_pos hq0 hq1 (by omega))
      (mul_pos hA (rpow_pos_of_pos (ih (by omega)) α))

/-- **AKMM, (4.11), p. 103.** The plan `k_{t+1} = s_{T−t}Ak_t^α` satisfies the Euler equation
`1/(Ak_t^α − k_{t+1}) = β · αAk_{t+1}^{α−1}/(Ak_{t+1}^α − k_{t+2})` for `t < T`, and
`k_{T+1} = 0`. -/
theorem eq_4_11 {T : ℕ} {k0 : ℝ} (hk0 : 0 < k0) :
    (∀ t < T, 1 / (A * example41Plan A α β T k0 t ^ α - example41Plan A α β T k0 (t + 1)) =
      β * (α * A * example41Plan A α β T k0 (t + 1) ^ (α - 1)) /
        (A * example41Plan A α β T k0 (t + 1) ^ α - example41Plan A α β T k0 (t + 2))) ∧
    example41Plan A α β T k0 (T + 1) = 0 := by
  have hq0 : 0 < α * β := mul_pos hα0 hβ0
  have hq1 : α * β < 1 := by nlinarith
  refine ⟨fun t ht => ?_, by rw [example41_plan_succ, Nat.sub_self, example41_rate_zero,
    zero_mul]⟩
  have hk : 0 < example41Plan A α β T k0 t := example41_plan_pos hA hα0 hα1 hβ0 hβ1 hk0 ht.le
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  have hk1 := example41_plan_succ A α β T k0 t
  have hk2 := example41_plan_succ A α β T k0 (t + 1)
  rw [hn] at hk1
  rw [hn'] at hk2
  rw [show t + 2 = t + 1 + 1 by rfl, hk2, hk1]
  set Y := A * example41Plan A α β T k0 t ^ α
  have hY : 0 < Y := mul_pos hA (rpow_pos_of_pos hk α)
  set s := example41Rate (α * β) (n + 1)
  set s' := example41Rate (α * β) n
  have hs0 : 0 < s := example41_rate_pos hq0 hq1 (by omega)
  have hs1 : s < 1 := example41_rate_lt_one hq0 hq1 _
  have hs'1 : s' < 1 := example41_rate_lt_one hq0 hq1 _
  have hrec : s * (1 - s') = α * β * (1 - s) := by
    have hthis : s = α * β / (1 + α * β - s') := example41_rate_recursion hq0 hq1 n
    have hne : 1 + α * β - s' ≠ 0 := by linarith
    rw [hthis]
    field_simp
    ring
  have hsY : 0 < s * Y := mul_pos hs0 hY
  have hpow : (s * Y) ^ (α - 1) = (s * Y) ^ α / (s * Y) := rpow_sub_one hsY.ne' α
  rw [hpow]
  have hP : 0 < (s * Y) ^ α := rpow_pos_of_pos hsY α
  have h1 : Y - s * Y ≠ 0 := by nlinarith
  have h2 : A * (s * Y) ^ α - s' * (A * (s * Y) ^ α) ≠ 0 := by
    have : 0 < A * (s * Y) ^ α := mul_pos hA hP
    nlinarith
  rw [div_eq_div_iff h1 h2]
  field_simp
  linear_combination hrec

/-- **Example 4.1** (AKMM, pp. 103–104): the plan `k_{t+1} = αβ(1 − (αβ)^{T−t})/(1 − (αβ)^{T−t+1})
Ak_t^α` is the unique maximizer of (P3) with `u = log`, `f(k) = Ak^α`, `δ = 1`, among feasible
plans with positive consumption (the others have value `−∞` in the book). -/
theorem example_4_1 {T : ℕ} {k0 : ℝ} (hk0 : 0 < k0) {k : ℕ → ℝ}
    (hk : NGMFeasible (fun k => A * k ^ α) k0 T k)
    (hkS : ∀ t ≤ T, A * k t ^ α - k (t + 1) ∈ Set.Ioi 0) :
    NGMFeasible (fun k => A * k ^ α) k0 T (example41Plan A α β T k0) ∧
      ngmObjective Real.log (fun k => A * k ^ α) β k T ≤
        ngmObjective Real.log (fun k => A * k ^ α) β (example41Plan A α β T k0) T ∧
      ((∀ x : ℕ → ℝ, NGMFeasible (fun k => A * k ^ α) k0 T x →
        (∀ t ≤ T, A * x t ^ α - x (t + 1) ∈ Set.Ioi 0) →
          ngmObjective Real.log (fun k => A * k ^ α) β x T ≤
            ngmObjective Real.log (fun k => A * k ^ α) β k T) →
        ∀ t ≤ T + 1, k t = example41Plan A α β T k0 t) := by
  have hq0 : 0 < α * β := mul_pos hα0 hβ0
  have hq1 : α * β < 1 := by nlinarith
  set h : ℝ → ℝ := fun k => A * k ^ α
  set ks := example41Plan A α β T k0
  have hpos : ∀ t ≤ T, 0 < ks t := fun t ht => example41_plan_pos hA hα0 hα1 hβ0 hβ1 hk0 ht
  have hc : ∀ t ≤ T, h (ks t) - ks (t + 1) = (1 - example41Rate (α * β) (T - t)) * h (ks t) :=
    fun t _ => by simp only [h, ks, example41_plan_succ]; ring
  have hhpos : ∀ t ≤ T, 0 < h (ks t) := fun t ht => mul_pos hA (rpow_pos_of_pos (hpos t ht) α)
  have hcpos : ∀ t ≤ T, 0 < h (ks t) - ks (t + 1) := fun t ht => by
    rw [hc t ht]
    exact mul_pos (by linarith [example41_rate_lt_one hq0 hq1 (T - t)]) (hhpos t ht)
  have hfeas : NGMFeasible h k0 T ks := by
    refine ⟨rfl, fun t ht => ⟨?_, ?_⟩⟩
    · rw [show ks (t + 1) = _ from example41_plan_succ A α β T k0 t]
      exact mul_nonneg (example41_rate_nonneg hq0 hq1 _) (hhpos t ht).le
    · linarith [hcpos t ht]
  have hS : Convex ℝ (Set.Ioi (0 : ℝ)) := convex_Ioi 0
  have hup : ∀ x ∈ Set.Ioi (0 : ℝ), ∀ y, x ≤ y → y ∈ Set.Ioi (0 : ℝ) :=
    fun x hx y hxy => lt_of_lt_of_le hx hxy
  have hhc : StrictConcaveOn ℝ (Set.Ici 0) h := by
    refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have := (strictConcaveOn_rpow hα0 hα1).2 hx hy hxy ha hb hab
    simp only [smul_eq_mul, h] at this ⊢
    have := mul_lt_mul_of_pos_left this hA
    linarith
  have hdu : ∀ t ≤ T, HasDerivAt Real.log (h (ks t) - ks (t + 1))⁻¹ (h (ks t) - ks (t + 1)) :=
    fun t ht => hasDerivAt_log (hcpos t ht).ne'
  have hdh : ∀ t ≤ T, HasDerivAt h (A * (α * ks t ^ (α - 1))) (ks t) := fun t ht =>
    (hasDerivAt_rpow_const (Or.inl (hpos t ht).ne')).const_mul A
  have heuler : ∀ t < T, (h (ks t) - ks (t + 1))⁻¹ =
      β * (h (ks (t + 1)) - ks (t + 1 + 1))⁻¹ * (A * (α * ks (t + 1) ^ (α - 1))) := by
    intro t ht
    have := (eq_4_11 hA hα0 hα1 hβ0 hβ1 (T := T) hk0).1 t ht
    rw [← one_div, this]
    simp only [h, ks]
    ring
  have hterm : ks (T + 1) = 0 := (eq_4_11 hA hα0 hα1 hβ0 hβ1 (T := T) hk0).2
  have hdu0 : 0 ≤ (h (ks T) - ks (T + 1))⁻¹ := (inv_pos.2 (hcpos T le_rfl)).le
  have hopt := fun (x : ℕ → ℝ) (hx : NGMFeasible h k0 T x)
      (hxS : ∀ t ≤ T, h (x t) - x (t + 1) ∈ Set.Ioi 0) =>
    ngm_finite_sufficient hS hup strictConcaveOn_log_Ioi.concaveOn
      strictMonoOn_log.monotoneOn hhc.concaveOn hβ0.le hk0.le hfeas (fun t ht => hcpos t ht)
      hdu hdh hdu0 heuler hterm hx hxS
  refine ⟨hfeas, hopt k hk hkS, fun hkmax => ?_⟩
  refine finite_unique_max (ngm_return_strictConcave hS hup strictConcaveOn_log_Ioi strictMonoOn_log
      hhc) hβ0 (x0 := k0)
    (P := {x | NGMFeasible h k0 T x ∧ ∀ t ≤ T, h (x t) - x (t + 1) ∈ Set.Ioi 0})
    (fun x hx => hx.1.1) (fun x hx t ht => ⟨?_, hx.2 t ht⟩) ?_ ⟨hk, hkS⟩
    ⟨hfeas, fun t ht => hcpos t ht⟩ (fun x hx => hkmax x hx.1 hx.2) (fun x hx => hopt x hx.1 hx.2)
  · rcases t with _ | t
    · rw [hx.1.1]; exact hk0.le
    · exact (hx.1.2 t (by omega)).1
  · intro x hx y hy
    have hnn : ∀ z : ℕ → ℝ, NGMFeasible h k0 T z → ∀ t ≤ T, 0 ≤ z t := by
      intro z hz t ht
      rcases t with _ | t
      · rw [hz.1]; exact hk0.le
      · exact (hz.2 t (by omega)).1
    refine ⟨⟨by simp only [hx.1.1, hy.1.1]; ring, fun t ht => ?_⟩, fun t ht => ?_⟩
    · have hcc := hhc.concaveOn.2 (Set.mem_Ici.2 (hnn x hx.1 t ht))
        (Set.mem_Ici.2 (hnn y hy.1 t ht)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hcc
      rw [show (1 / 2 : ℝ) * x t + 1 / 2 * y t = (x t + y t) / 2 by ring] at hcc
      exact ⟨by linarith [(hx.1.2 t ht).1, (hy.1.2 t ht).1],
        by linarith [(hx.1.2 t ht).2, (hy.1.2 t ht).2]⟩
    · have hcc := hhc.concaveOn.2 (Set.mem_Ici.2 (hnn x hx.1 t ht))
        (Set.mem_Ici.2 (hnn y hy.1 t ht)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hcc
      rw [show (1 / 2 : ℝ) * x t + 1 / 2 * y t = (x t + y t) / 2 by ring] at hcc
      have h1 := hx.2 t ht
      have h2 := hy.2 t ht
      simp only [Set.mem_Ioi] at h1 h2 ⊢
      linarith

end AKMM.DynamicOptimization

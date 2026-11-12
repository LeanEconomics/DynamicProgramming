/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSustainability.LogGrowth

/-!
# Growth with an exhaustible resource: Dasgupta–Heal

AKMM, §25.5.2, "A production economy" (pp. 777–778). The planner maximises `Σβ^t log c_t`
subject to `c_t + k_{t+1} = Az_t k_t^α e_t^ν` (full depreciation) and `Σ_t e_t ≤ R`, with
`z_t = z₀γ_z^t`, `A, z₀, γ_z > 0`, `0 < α < 1`, `ν ≥ 0`, `0 < β < 1`.

* The optimal plan extracts as in cake eating, `e_t = (1 − β)β^t R` (`e_t = (1 − β)R_t`,
  `R_{t+1} = R_t − e_t`), and saves `k_{t+1} = αβy_t` (`dhK`, `dh_saving`); it is feasible
  (`dh_feasible`), its utility converges (`dh_summable`) and it beats every feasible plan with
  convergent utility (`dh_optimal`): the extraction and saving problems separate exactly
  (`lg_compare` and `cake_overtake`).
* Growth: the gross growth of output `G_t = y_{t+1}/y_t` obeys
  `G_{t+1} = γ_zβ^ν G_t^α` (`dh_growth_rec`), whose unique fixed point is
  `g = (γ_zβ^ν)^{1/(1−α)}`, `g = γ_z g^α β^ν` (`dh_bgp`), and `G_t → g` (`dh_growth_tendsto`).
* Prices: the gross interest rate `1 + r_{t+1} = αy_{t+1}/k_{t+1}` equals `G_t/β`, so
  `1 + r → g/β` (`dh_interest`, `dh_interest_tendsto`); `r > 0` iff `g > β` in the limit
  (`dh_interest_pos_iff`); the resource price `p_t = νy_t/e_t` grows at `1 + r_{t+1}` every period
  — the Hotelling rule (`dh_hotelling`).
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

/-- AKMM, p. 777: output `y_t = Az₀γ_z^t k_t^α e_t^ν`. -/
noncomputable def dhOut (A z0 γz α ν : ℝ) (k e : ℕ → ℝ) (t : ℕ) : ℝ :=
  A * z0 * γz ^ t * k t ^ α * e t ^ ν

/-- AKMM, p. 777: the planner's capital path `k_{t+1} = αβy_t` with extraction
`e_t = (1 − β)β^t R`. -/
noncomputable def dhK (A z0 γz α β ν K0 R : ℝ) : ℕ → ℝ
  | 0 => K0
  | t + 1 => α * β * (A * z0 * γz ^ t * dhK A z0 γz α β ν K0 R t ^ α * cakePath β R t ^ ν)

variable {A z0 γz α β ν K0 R : ℝ}

/-- AKMM, p. 777: "we find `k_{t+1} = αβAz_t k_t^α e_t^ν`". -/
theorem dh_saving (t : ℕ) :
    dhK A z0 γz α β ν K0 R (t + 1) =
      α * β * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t := by
  simp only [dhK, dhOut]

/-- `log y_t = (log(Az₀) + t log γ_z + ν log e_t) + α log k_t`. -/
theorem dh_log_out (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) {k e : ℕ → ℝ} (t : ℕ)
    (hk : 0 < k t) (he : 0 < e t) :
    Real.log (dhOut A z0 γz α ν k e t) =
      (Real.log (A * z0) + t * Real.log γz + ν * Real.log (e t)) + α * Real.log (k t) := by
  unfold dhOut
  have h1 : 0 < γz ^ t := pow_pos hγ t
  have h2 := Real.rpow_pos_of_pos hk α
  have h3 := Real.rpow_pos_of_pos he ν
  rw [Real.log_mul (by positivity) h3.ne', Real.log_mul (by positivity) h2.ne',
    Real.log_mul (by positivity) h1.ne', Real.log_pow, Real.log_rpow hk, Real.log_rpow he]
  ring

/-- AKMM, p. 777: the planner's plan is feasible: positive capital and consumption
`c_t = (1 − αβ)y_t`. -/
theorem dh_feasible (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) (t : ℕ) :
    0 < dhK A z0 γz α β ν K0 R t ∧
      dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t -
        dhK A z0 γz α β ν K0 R (t + 1) =
        (1 - α * β) * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t ∧
      0 < dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t := by
  have he : ∀ s, 0 < cakePath β R s := fun s => by
    have : 0 < 1 - β := by linarith
    unfold cakePath; positivity
  have hk : ∀ s, 0 < dhK A z0 γz α β ν K0 R s := by
    intro s
    induction s with
    | zero => exact hK0
    | succ n ih =>
      rw [dh_saving]
      unfold dhOut
      have := Real.rpow_pos_of_pos ih α
      have := Real.rpow_pos_of_pos (he n) ν
      positivity
  refine ⟨hk t, by rw [dh_saving]; ring, ?_⟩
  unfold dhOut
  have := Real.rpow_pos_of_pos (hk t) α
  have := Real.rpow_pos_of_pos (he t) ν
  positivity

/-- `log e*_t = log((1 − β)R) + t log β`. -/
theorem dh_log_cake (hβ0 : 0 < β) (hβ1 : β < 1) (hR : 0 < R) (s : ℕ) :
    Real.log (cakePath β R s) = Real.log ((1 - β) * R) + s * Real.log β := by
  have h1 : 0 < (1 - β) * R := mul_pos (by linarith) hR
  have : cakePath β R s = ((1 - β) * R) * β ^ s := by simp only [cakePath]; ring
  rw [this, Real.log_mul h1.ne' (pow_pos hβ0 s).ne', Real.log_pow]

/-- The planner's log capital grows at most linearly. -/
theorem dh_log_k_bound (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) :
    ∃ P Q : ℝ, ∀ t, |Real.log (dhK A z0 γz α β ν K0 R t)| ≤ P + Q * t := by
  have he : ∀ s, 0 < cakePath β R s := fun s => by
    have : 0 < 1 - β := by linarith
    unfold cakePath; positivity
  have hab : 0 < α * β := mul_pos hα0 hβ0
  set M := |Real.log (α * β)| + |Real.log (A * z0)| + |Real.log γz| +
    |ν| * (|Real.log ((1 - β) * R)| + |Real.log β|) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hlogE : ∀ s : ℕ, Real.log (cakePath β R s) =
      Real.log ((1 - β) * R) + s * Real.log β := dh_log_cake hβ0 hβ1 hR
  refine ⟨|Real.log K0|, M / (1 - α), fun t => ?_⟩
  have h := lg_linear_bound (a := fun s => Real.log (dhK A z0 γz α β ν K0 R s))
    (c := fun s => Real.log (α * β) + (Real.log (A * z0) + s * Real.log γz +
      ν * Real.log (cakePath β R s))) hα0.le hα1 hM0 (fun s => by
      rw [hlogE]
      have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      calc |Real.log (α * β) + (Real.log (A * z0) + s * Real.log γz +
            ν * (Real.log ((1 - β) * R) + s * Real.log β))|
          ≤ |Real.log (α * β)| + (|Real.log (A * z0)| + s * |Real.log γz| +
            |ν| * (|Real.log ((1 - β) * R)| + s * |Real.log β|)) := by
            refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
            refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
            · refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
              rw [abs_mul, abs_of_nonneg hs]
            · rw [abs_mul]
              refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (abs_nonneg _)
              rw [abs_mul, abs_of_nonneg hs]
        _ ≤ M * (1 + s) := by
            rw [hM]
            nlinarith [abs_nonneg (Real.log (α * β)), abs_nonneg (Real.log (A * z0)),
              abs_nonneg (Real.log γz), abs_nonneg ν, abs_nonneg (Real.log ((1 - β) * R)),
              abs_nonneg (Real.log β), mul_nonneg (abs_nonneg ν) (abs_nonneg (Real.log β)),
              mul_nonneg (mul_nonneg (abs_nonneg ν) (abs_nonneg (Real.log β))) hs,
              mul_nonneg (abs_nonneg (Real.log (α * β))) hs,
              mul_nonneg (abs_nonneg (Real.log (A * z0))) hs,
              mul_nonneg (mul_nonneg (abs_nonneg ν) (abs_nonneg (Real.log ((1 - β) * R)))) hs])
    (fun s => by
      have hk := (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR s).1
      rw [dh_saving, Real.log_mul hab.ne' (dh_feasible hA hz hγ hα0 hβ0 hβ1 hK0 hR s).2.2.ne',
        dh_log_out hA hz hγ s hk (he s)]
      ring) t
  exact h

/-- AKMM, pp. 777: the planner's utility converges. -/
theorem dh_summable (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) :
    Summable (fun t => β ^ t * Real.log (dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R)
      (cakePath β R) t - dhK A z0 γz α β ν K0 R (t + 1))) := by
  obtain ⟨P, Q, hPQ⟩ := dh_log_k_bound (ν := ν) hA hz hγ hα0 hα1 hβ0 hβ1 hK0 hR
  have hab : α * β < 1 := by nlinarith
  have he : ∀ s, 0 < cakePath β R s := fun s => by
    have : 0 < 1 - β := by linarith
    unfold cakePath; positivity
  set c0 := |Real.log (1 - α * β)| + |Real.log (A * z0)| + |ν| * |Real.log ((1 - β) * R)| +
    α * P with hc0
  set c1 := |Real.log γz| + |ν| * |Real.log β| + α * Q with hc1
  refine Summable.of_norm_bounded (g := fun t : ℕ => β ^ t * (c0 + c1 * t))
    (lg_summable_linear hβ0.le hβ1 _ _) fun t => ?_
  obtain ⟨hk, hc, hy⟩ := dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le t), hc,
    Real.log_mul (by linarith) hy.ne', dh_log_out hA hz hγ t hk (he t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le t)
  have hlogE := dh_log_cake hβ0 hβ1 hR t
  rw [hlogE]
  have hk' := hPQ t
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  calc |Real.log (1 - α * β) + (Real.log (A * z0) + t * Real.log γz +
        ν * (Real.log ((1 - β) * R) + t * Real.log β) + α * Real.log (dhK A z0 γz α β ν K0 R t))|
      ≤ |Real.log (1 - α * β)| + (|Real.log (A * z0)| + t * |Real.log γz| +
        |ν| * (|Real.log ((1 - β) * R)| + t * |Real.log β|) +
          α * |Real.log (dhK A z0 γz α β ν K0 R t)|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [abs_mul, abs_of_nonneg ht]
          · rw [abs_mul]
            refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (abs_nonneg _)
            rw [abs_mul, abs_of_nonneg ht]
        · rw [abs_mul, abs_of_pos hα0]
    _ ≤ c0 + c1 * t := by
        have := mul_le_mul_of_nonneg_left hk' hα0.le
        rw [hc0, hc1]
        nlinarith [mul_nonneg (abs_nonneg ν) (abs_nonneg (Real.log β))]

/-- **AKMM, p. 777: the Dasgupta–Heal planner's optimum.** The plan `e_t = (1 − β)β^t R`,
`k_{t+1} = αβy_t` maximises `Σβ^t log c_t` among all plans with `k₀` given, `k_t, e_t > 0`,
`Σ_{t<T} e_t ≤ R`, `c_t = y_t − k_{t+1} > 0` and convergent utility. -/
theorem dh_optimal (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α) (hα1 : α < 1)
    (hν : 0 ≤ ν) (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) {k e : ℕ → ℝ}
    (hk0 : k 0 = K0) (hk : ∀ t, 0 < k t) (he : ∀ t, 0 < e t)
    (hsum : ∀ T, ∑ t ∈ range T, e t ≤ R) (hc : ∀ t, 0 < dhOut A z0 γz α ν k e t - k (t + 1))
    {U : ℝ} (hU : HasSum (fun t => β ^ t * Real.log (dhOut A z0 γz α ν k e t - k (t + 1))) U) :
    U ≤ ∑' t, β ^ t * Real.log (dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t -
      dhK A z0 γz α β ν K0 R (t + 1)) := by
  have hab0 : 0 < α * β := mul_pos hα0 hβ0
  have hab1 : α * β < 1 := by nlinarith
  have h1ab : 0 < 1 - α * β := by linarith
  have h1β : 0 < 1 - β := by linarith
  have hes : ∀ s, 0 < cakePath β R s := fun s => by unfold cakePath; positivity
  set Ks := dhK A z0 γz α β ν K0 R
  set B := 1 / (1 - α * β) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the finite-horizon comparison
  have hcmp := fun T => lg_compare (β := β) hab0 hab1 hβ0 (K := k)
    (Y := dhOut A z0 γz α ν k e) (C := fun t => dhOut A z0 γz α ν k e t - k (t + 1))
    (w := fun t => Real.log (A * z0) + t * Real.log γz + ν * Real.log (e t)) (Ks := Ks)
    (Ys := dhOut A z0 γz α ν Ks (cakePath β R))
    (Cs := fun t => dhOut A z0 γz α ν Ks (cakePath β R) t - Ks (t + 1))
    (ws := fun t => Real.log (A * z0) + t * Real.log γz + ν * Real.log (cakePath β R t))
    hk hc (fun t => by ring) (fun t => dh_log_out hA hz hγ t (hk t) (he t))
    (fun t => (dh_feasible hA hz hγ hα0 hβ0 hβ1 hK0 hR t).1)
    (fun t => by
      have := (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR t).2
      rw [this.1]; exact mul_pos h1ab this.2)
    (fun t => by ring)
    (fun t => dh_log_out hA hz hγ t (dh_feasible hA hz hγ hα0 hβ0 hβ1 hK0 hR t).1 (hes t))
    (fun t => dh_saving t) (by rw [hk0]; rfl) T
  -- the extraction part is the cake-eating comparison
  have hcake := cake_overtake hβ0 hβ1 hR he hsum
  -- terminal terms
  obtain ⟨P, Q, hPQ⟩ := dh_log_k_bound (ν := ν) hA hz hγ hα0 hα1 hβ0 hβ1 hK0 hR
  have hCt : Tendsto (fun t => β ^ t * Real.log (dhOut A z0 γz α ν k e t - k (t + 1))) atTop
      (𝓝 0) := hU.summable.tendsto_atTop_zero
  -- `log c_T ≤ log y_T ≤ log(Az₀) + T log γ_z + ν log R + α log k_T`
  have hterm : ∀ T : ℕ, -(α * Real.log (k T)) ≤ |Real.log (A * z0)| + T * |Real.log γz| +
      ν * |Real.log R| - Real.log (dhOut A z0 γz α ν k e T - k (T + 1)) := by
    intro T
    have hy : 0 < dhOut A z0 γz α ν k e T := by linarith [hc T, hk (T + 1)]
    have h1 : Real.log (dhOut A z0 γz α ν k e T - k (T + 1)) ≤
        Real.log (dhOut A z0 γz α ν k e T) :=
      Real.log_le_log (hc T) (by linarith [hk (T + 1)])
    rw [dh_log_out hA hz hγ T (hk T) (he T)] at h1
    have heR : e T ≤ R := by
      have := hsum (T + 1)
      rw [sum_range_succ] at this
      have : 0 ≤ ∑ t ∈ range T, e t := sum_nonneg fun t _ => (he t).le
      linarith
    have h2 : Real.log (e T) ≤ |Real.log R| :=
      (Real.log_le_log (he T) heR).trans (le_abs_self _)
    have h3 : (T : ℝ) * Real.log γz ≤ T * |Real.log γz| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg T)
    have h4 := mul_le_mul_of_nonneg_left h2 hν
    have h5 := le_abs_self (Real.log (A * z0))
    linarith
  set c1 := |Real.log (A * z0)| with hc1
  set c2 := |Real.log γz| with hc2
  set c3 := ν * |Real.log R| with hc3
  refine sust_hasSum_le_of_partial hU (dh_summable hA hz hγ hα0 hα1 hβ0 hβ1 hK0 hR).hasSum
    (ε := fun T => B * ν * (β ^ T / (1 - β)) + B * (β ^ T * (c1 + c3 + c2 * T)) -
      B * (β ^ T * Real.log (dhOut A z0 γz α ν k e T - k (T + 1))) +
      B * α * (β ^ T * (P + Q * T))) ?_ (Eventually.of_forall fun T => ?_)
  · have t1 := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).div_const (1 - β)).const_mul
      (B * ν)
    have t2 := (lg_tendsto_linear hβ0.le hβ1 (c1 + c3) c2).const_mul B
    have t3 := hCt.const_mul B
    have t4 := (lg_tendsto_linear hβ0.le hβ1 P Q).const_mul (B * α)
    have := ((t1.add t2).sub t3).add t4
    simp only [zero_div, mul_zero, add_zero, sub_zero] at this
    exact this
  · have hc := hcmp T
    have hcT := hcake T
    have ht := hterm T
    have hl := (abs_le.mp (hPQ T)).2
    have hbT : 0 ≤ β ^ T := pow_nonneg hβ0.le T
    -- the energy term
    have hw : ∑ t ∈ range T, β ^ t * ((Real.log (A * z0) + t * Real.log γz + ν * Real.log (e t)) -
        (Real.log (A * z0) + t * Real.log γz + ν * Real.log (cakePath β R t))) =
        ν * (∑ t ∈ range T, β ^ t * Real.log (e t) -
          ∑ t ∈ range T, β ^ t * Real.log (cakePath β R t)) := by
      rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun t _ => ?_
      ring
    rw [hw] at hc
    have hen : ν * (∑ t ∈ range T, β ^ t * Real.log (e t) -
        ∑ t ∈ range T, β ^ t * Real.log (cakePath β R t)) ≤ ν * (β ^ T / (1 - β)) :=
      mul_le_mul_of_nonneg_left (by linarith) hν
    have e1 : α / (1 - α * β) = B * α := by rw [hB]; ring
    rw [e1] at hc
    have k1 := mul_le_mul_of_nonneg_left ht (mul_nonneg hB0 hbT)
    have k2 := mul_le_mul_of_nonneg_left hl (mul_nonneg (mul_nonneg hB0 hα0.le) hbT)
    have k3 := mul_le_mul_of_nonneg_left hen hB0
    nlinarith

/-- AKMM, p. 777: along the optimum the gross growth of output `G_t = y_{t+1}/y_t` satisfies
`G_{t+1} = γ_zβ^ν G_t^α`. -/
theorem dh_growth_rec (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) (t : ℕ) :
    dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 2) /
        dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) =
      γz * β ^ ν * (dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t) ^ α := by
  have h1β : 0 < 1 - β := by linarith
  set Ks := dhK A z0 γz α β ν K0 R
  have hy : ∀ s, 0 < dhOut A z0 γz α ν Ks (cakePath β R) s :=
    fun s => (dh_feasible hA hz hγ hα0 hβ0 hβ1 hK0 hR s).2.2
  have hk : ∀ s, 0 < Ks s := fun s => (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR s).1
  -- `y_{s+1}/y_s = γ_z β^ν (k_{s+1}/k_s)^α`
  have hstep : ∀ s, dhOut A z0 γz α ν Ks (cakePath β R) (s + 1) /
      dhOut A z0 γz α ν Ks (cakePath β R) s = γz * β ^ ν * (Ks (s + 1) / Ks s) ^ α := by
    intro s
    have he : cakePath β R (s + 1) = β * cakePath β R s := by
      simp only [cakePath, pow_succ]; ring
    have hes : 0 < cakePath β R s := by unfold cakePath; positivity
    unfold dhOut
    rw [he, Real.mul_rpow hβ0.le hes.le, Real.div_rpow (hk (s + 1)).le (hk s).le, pow_succ]
    have := Real.rpow_pos_of_pos (hk s) α
    have := Real.rpow_pos_of_pos hes ν
    field_simp
  -- `k_{s+2}/k_{s+1} = y_{s+1}/y_s`
  have hk2 : Ks (t + 2) / Ks (t + 1) = dhOut A z0 γz α ν Ks (cakePath β R) (t + 1) /
      dhOut A z0 γz α ν Ks (cakePath β R) t := by
    rw [show t + 2 = (t + 1) + 1 from rfl,
      show Ks (t + 1 + 1) = α * β * dhOut A z0 γz α ν Ks (cakePath β R) (t + 1) from
        dh_saving (t + 1),
      show Ks (t + 1) = α * β * dhOut A z0 γz α ν Ks (cakePath β R) t from dh_saving t]
    have := hy t; have := hy (t + 1)
    field_simp
  rw [hstep (t + 1), hk2]

/-- AKMM, p. 777: the balanced growth rate `g = (γ_zβ^ν)^{1/(1−α)}` solves `g = γ_z g^α β^ν`, and
it is the only positive solution. -/
theorem dh_bgp (hγ : 0 < γz) (hβ0 : 0 < β) (hα1 : α < 1) {g : ℝ} (hg : 0 < g) :
    g = γz * g ^ α * β ^ ν ↔ g = (γz * β ^ ν) ^ (1 / (1 - α)) := by
  have h1α : (1 : ℝ) - α ≠ 0 := (by linarith : (0 : ℝ) < 1 - α).ne'
  have hc : 0 < γz * β ^ ν := by positivity
  constructor
  · intro h
    have : g ^ (1 - α) = γz * β ^ ν := by
      rw [Real.rpow_sub hg, Real.rpow_one]
      have hga := Real.rpow_pos_of_pos hg α
      field_simp
      linarith
    rw [← this, ← Real.rpow_mul hg.le, mul_one_div_cancel h1α, Real.rpow_one]
  · intro h
    have hga : g ^ (1 - α) = γz * β ^ ν := by
      rw [h, ← Real.rpow_mul hc.le, one_div_mul_cancel h1α, Real.rpow_one]
    rw [Real.rpow_sub hg, Real.rpow_one] at hga
    have := Real.rpow_pos_of_pos hg α
    field_simp at hga
    linarith

/-- AKMM, p. 777: "long-run gross capital growth `g` is constant if `z` grows at a constant
rate": the growth factor of output converges to `g = (γ_zβ^ν)^{1/(1−α)}` (so does that of
capital, `k_{t+1}/k_t = y_t/y_{t−1}`). -/
theorem dh_growth_tendsto (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) :
    Tendsto (fun t => dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
      dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t) atTop
      (𝓝 ((γz * β ^ ν) ^ (1 / (1 - α)))) := by
  set G := fun t => dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
      dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t with hG
  have hy := fun s => (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR s).2.2
  have hGpos : ∀ t, 0 < G t := fun t => div_pos (hy (t + 1)) (hy t)
  have hc : 0 < γz * β ^ ν := by positivity
  set lg := Real.log (γz * β ^ ν) / (1 - α) with hlg
  -- `log G_{t+1} − lg = α(log G_t − lg)`
  have hrec : ∀ t, Real.log (G (t + 1)) - lg = α * (Real.log (G t) - lg) := by
    intro t
    have h := dh_growth_rec (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR t
    have : G (t + 1) = γz * β ^ ν * G t ^ α := h
    rw [this, Real.log_mul hc.ne' (Real.rpow_pos_of_pos (hGpos t) α).ne',
      Real.log_rpow (hGpos t), hlg]
    have : (1 : ℝ) - α ≠ 0 := (by linarith : (0 : ℝ) < 1 - α).ne'
    field_simp
    ring
  have hgeo : ∀ t, Real.log (G t) - lg = α ^ t * (Real.log (G 0) - lg) := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hrec, ih, pow_succ]; ring
  have hlog : Tendsto (fun t => Real.log (G t)) atTop (𝓝 lg) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hα0.le hα1).mul_const
      (Real.log (G 0) - lg)).add_const lg
    simp only [zero_mul, zero_add] at this
    exact this.congr fun t => by rw [← hgeo t]; ring
  have hexp := (Real.continuous_exp.tendsto lg).comp hlog
  have hlim : Real.exp lg = (γz * β ^ ν) ^ (1 / (1 - α)) := by
    rw [Real.rpow_def_of_pos hc, hlg]; ring_nf
  rw [← hlim]
  exact hexp.congr fun t => by simp [Real.exp_log (hGpos t)]

/-- AKMM, p. 777: the gross interest rate `1 + r_{t+1} = αy_{t+1}/k_{t+1}` (full depreciation)
equals `G_t/β`, consistent with the Euler equation `c_{t+1}/c_t = β(1 + r_{t+1})` and
`c = (1 − αβ)y`. -/
theorem dh_interest (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) (t : ℕ) :
    α * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        dhK A z0 γz α β ν K0 R (t + 1) =
      dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t / β := by
  have hy := (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR t).2.2
  rw [dh_saving]
  field_simp

/-- AKMM, p. 777: `1 + r = (γ_zβ^ν)^{1/(1−α)}/β` in the long run. -/
theorem dh_interest_tendsto (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) :
    Tendsto (fun t => α * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        dhK A z0 γz α β ν K0 R (t + 1)) atTop (𝓝 ((γz * β ^ ν) ^ (1 / (1 - α)) / β)) := by
  have := (dh_growth_tendsto (ν := ν) hA hz hγ hα0 hα1 hβ0 hβ1 hK0 hR).div_const β
  exact this.congr fun t => (dh_interest hA hz hγ hα0 hβ0 hβ1 hK0 hR t).symm

/-- AKMM, p. 777: "the net real interest rate is positive if `g > β`". -/
theorem dh_interest_pos_iff (hβ0 : 0 < β) {g : ℝ} : 1 < g / β ↔ β < g := by
  rw [one_lt_div hβ0]

/-- AKMM, p. 777: the resource price `p_t = νy_t/e_t` grows at the gross interest rate every
period: `p_{t+1}/p_t = αy_{t+1}/k_{t+1} = 1 + r_{t+1}` — the Hotelling rule. -/
theorem dh_hotelling (hA : 0 < A) (hz : 0 < z0) (hγ : 0 < γz) (hα0 : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hK0 : 0 < K0) (hR : 0 < R) (hν : ν ≠ 0) (t : ℕ) :
    (ν * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        cakePath β R (t + 1)) /
      (ν * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) t / cakePath β R t) =
      α * dhOut A z0 γz α ν (dhK A z0 γz α β ν K0 R) (cakePath β R) (t + 1) /
        dhK A z0 γz α β ν K0 R (t + 1) := by
  rw [dh_interest hA hz hγ hα0 hβ0 hβ1 hK0 hR t]
  have hy := (dh_feasible (ν := ν) hA hz hγ hα0 hβ0 hβ1 hK0 hR t).2.2
  have h1β : 0 < 1 - β := by linarith
  have hes : 0 < cakePath β R t := by unfold cakePath; positivity
  have he : cakePath β R (t + 1) = β * cakePath β R t := by
    simp only [cakePath, pow_succ]; ring
  rw [he]
  field_simp

end AKMM.Sustainability

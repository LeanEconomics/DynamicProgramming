/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.FiniteExample
import AKMMDynamicOptimization.Proposition44
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The infinite-horizon neoclassical growth model

AKMM, §4.3.2, pp. 111–113.

* (4.16): a steady state with positive consumption satisfies `1 = β(f'(k̄) + 1 − δ)`
  (`eq_4_16_of_euler`), and under strict concavity and the Inada conditions there is exactly one
  (`eq_4_16`).
* Example 4.5: the truncated saving rates converge to `αβ` (`example_4_5_limit`), giving (4.17)
  `k_{t+1} = αβAk_t^α`; along it `βᵗu'(c_t)f'(k_t)k_t = βᵗα/(1 − αβ)`, so the TVC holds
  (`example_4_5_tvc`), and by Proposition 4.4 the plan is optimal (`example_4_5`).
* Example 4.6: the guess `k_{t+1} = sAk_t^α` satisfies the Euler equation iff `s = αβ`
  (`example_4_6`).
* p. 112: `k̄ = (αβA)^{1/(1−α)}` is the steady state of (4.17) (`example_4_5_steady`), and every
  path of (4.17) from `k₀ > 0` converges to it (`example_4_5_convergence`).
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real DPExtensions.EulerTransversality

/-- AKMM, (4.16), p. 111: with constant positive consumption `c̄` (`u'(c̄) ≠ 0`), the Euler
equation (4.10) at a steady state reduces to `1 = β(f'(k̄) + 1 − δ)`. -/
theorem eq_4_16_of_euler {β du dh : ℝ} (hdu : du ≠ 0) (heuler : du = β * du * dh) :
    1 = β * dh := by
  have : du * (1 - β * dh) = 0 := by linear_combination heuler
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hdu
  · linarith

/-- **AKMM, (4.16), p. 111: the steady state is unique.** If `f'` is continuous and strictly
decreasing on `(0, ∞)`, `f'(k) → ∞` as `k → 0⁺` and `f'(k) → 0` as `k → ∞`, `0 < β < 1` and
`0 ≤ δ`, there is exactly one `k̄ > 0` with `1 = β(f'(k̄) + 1 − δ)`. -/
theorem eq_4_16 {f' : ℝ → ℝ} (hcont : ContinuousOn f' (Set.Ioi 0))
    (hanti : StrictAntiOn f' (Set.Ioi 0)) (h0 : Tendsto f' (𝓝[>] 0) atTop)
    (htop : Tendsto f' atTop (𝓝 0)) {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) :
    ∃! k, 0 < k ∧ 1 = β * (f' k + 1 - δ) := by
  set ρ := 1 / β - 1 + δ
  have hρ : 0 < ρ := by
    have : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
    simp only [ρ]; linarith
  have hiff : ∀ k, 1 = β * (f' k + 1 - δ) ↔ f' k = ρ := fun k => by
    simp only [ρ]
    constructor <;> intro h
    · field_simp; linarith
    · rw [h]; field_simp; ring
  obtain ⟨a, ha, ha0⟩ := ((h0.eventually (eventually_gt_atTop ρ)).and
    self_mem_nhdsWithin).exists
  obtain ⟨b, hb, hab⟩ := ((htop.eventually (gt_mem_nhds hρ)).and
    (eventually_ge_atTop a)).exists
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hivt := intermediate_value_Icc' hab (hcont.mono fun x hx =>
    (lt_of_lt_of_le (Set.mem_Ioi.1 ha0) hx.1))
  obtain ⟨k, hk, hfk⟩ := hivt ⟨hb.le, ha.le⟩
  refine ⟨k, ⟨lt_of_lt_of_le ha0 hk.1, (hiff k).2 hfk⟩, fun k' ⟨hk'0, hk'⟩ => ?_⟩
  have h1 := (hiff k').1 hk'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := hanti (Set.mem_Ioi.2 hk'0) (Set.mem_Ioi.2 (lt_of_lt_of_le ha0 hk.1)) hlt
    linarith
  · have := hanti (Set.mem_Ioi.2 (lt_of_lt_of_le ha0 hk.1)) (Set.mem_Ioi.2 hk'0) hlt
    linarith

/-- **AKMM, Example 4.5, p. 112: the limit of the truncated solutions.** As `T → ∞`,
`αβ(1 − (αβ)^{T−t})/(1 − (αβ)^{T−t+1}) → αβ`, which gives (4.17) `k_{t+1} = αβAk_t^α`. -/
theorem example_4_5_limit {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (t : ℕ) :
    Tendsto (fun T : ℕ => example41Rate q (T - t)) atTop (𝓝 q) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
  have hlim : Tendsto (fun n : ℕ => example41Rate q n) atTop (𝓝 q) := by
    have h1 : Tendsto (fun n : ℕ => q * (1 - q ^ n) / (1 - q ^ (n + 1))) atTop
        (𝓝 (q * (1 - 0) / (1 - 0))) := by
      refine ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hpow)).div
        (tendsto_const_nhds.sub ((tendsto_add_atTop_iff_nat 1).2 hpow)) (by norm_num))
    simpa [example41Rate] using h1
  exact hlim.comp (tendsto_sub_atTop_nat t)

variable {A α β : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
include hA hα0 hα1 hβ0 hβ1

/-- **AKMM, Example 4.5, p. 112: the TVC along (4.17).** With `c_t = Ak_t^α − k_{t+1}` and
`k_{t+1} = αβAk_t^α`, `βᵗu'(c_t)f'(k_t)k_t = βᵗα/(1 − αβ)`, which tends to `0`. -/
theorem example_4_5_tvc {k : ℕ → ℝ} (hk : ∀ t, 0 < k t)
    (hplan : ∀ t, k (t + 1) = α * β * A * k t ^ α) :
    (∀ t, β ^ t * ((1 / (A * k t ^ α - k (t + 1))) * (α * A * k t ^ (α - 1)) * k t) =
      β ^ t * (α / (1 - α * β))) ∧
    Tendsto (fun t => β ^ t * ((1 / (A * k t ^ α - k (t + 1))) * (α * A * k t ^ (α - 1)) * k t))
      atTop (𝓝 0) := by
  have hq1 : α * β < 1 := by nlinarith
  have hid : ∀ t, β ^ t * ((1 / (A * k t ^ α - k (t + 1))) * (α * A * k t ^ (α - 1)) * k t) =
      β ^ t * (α / (1 - α * β)) := by
    intro t
    have hkt := hk t
    have hP : 0 < k t ^ α := rpow_pos_of_pos hkt α
    rw [hplan t, rpow_sub_one hkt.ne']
    have h1 : A * k t ^ α - α * β * A * k t ^ α ≠ 0 := by
      have : 0 < A * k t ^ α * (1 - α * β) := mul_pos (mul_pos hA hP) (by linarith)
      nlinarith
    have h2 : (1 - α * β) ≠ 0 := by linarith
    field_simp
  refine ⟨hid, ?_⟩
  simp only [hid]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (α / (1 - α * β))

omit hα1 hβ1 in
/-- **AKMM, Example 4.6, p. 112: guess and verify.** For `0 < s < 1` and `k > 0`, the guess
`k' = sAk^α`, `k'' = sAk'^α` satisfies the Euler equation
`1/(Ak^α − sAk^α) = βαAk'^{α−1}/(Ak'^α − sAk'^α)` iff `s = αβ`. -/
theorem example_4_6 {s k : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hk : 0 < k) :
    1 / (A * k ^ α - s * A * k ^ α) =
        β * α * A * (s * A * k ^ α) ^ (α - 1) /
          (A * (s * A * k ^ α) ^ α - s * A * (s * A * k ^ α) ^ α) ↔ s = α * β := by
  have hP : 0 < k ^ α := rpow_pos_of_pos hk α
  set k' := s * A * k ^ α
  have hk' : 0 < k' := mul_pos (mul_pos hs0 hA) hP
  have hP' : 0 < k' ^ α := rpow_pos_of_pos hk' α
  rw [rpow_sub_one hk'.ne']
  have h1 : A * k ^ α - s * A * k ^ α ≠ 0 := by
    have : 0 < A * k ^ α * (1 - s) := mul_pos (mul_pos hA hP) (by linarith)
    nlinarith
  have h2 : A * k' ^ α - s * A * k' ^ α ≠ 0 := by
    have : 0 < A * k' ^ α * (1 - s) := mul_pos (mul_pos hA hP') (by linarith)
    nlinarith
  have h3 : (1 - s) ≠ 0 := by linarith
  rw [div_eq_div_iff h1 h2]
  have e : β * α * A * (k' ^ α / k') * (A * k ^ α - s * A * k ^ α) =
      α * β * (1 / s) * (A * k' ^ α - s * A * k' ^ α) := by
    simp only [k']
    field_simp
  rw [e, one_mul]
  have h4 : 0 < A * k' ^ α - s * A * k' ^ α := by
    have : 0 < A * k' ^ α * (1 - s) := mul_pos (mul_pos hA hP') (by linarith)
    nlinarith
  constructor
  · intro h
    have : α * β * (1 / s) = 1 := by
      have := mul_right_cancel₀ h4.ne' (h.symm.trans (one_mul _).symm)
      exact this
    field_simp at this
    linarith
  · intro h
    rw [h]
    field_simp [show α * β ≠ 0 from (mul_pos hα0 hβ0).ne']

omit hβ1 in
/-- AKMM, p. 112: `k̄ = (αβA)^{1/(1−α)}` is a steady state of (4.17), `k̄ = αβAk̄^α`, and
satisfies (4.16) with `δ = 1`: `1 = β · αAk̄^{α−1}`. -/
theorem example_4_5_steady :
    (α * β * A) ^ (1 / (1 - α)) = α * β * A * ((α * β * A) ^ (1 / (1 - α))) ^ α ∧
      1 = β * (α * A * ((α * β * A) ^ (1 / (1 - α))) ^ (α - 1)) := by
  have hq : 0 < α * β * A := mul_pos (mul_pos hα0 hβ0) hA
  have h1α : (1 - α) ≠ 0 := by linarith
  set kb := (α * β * A) ^ (1 / (1 - α))
  have hkb : 0 < kb := rpow_pos_of_pos hq _
  have hkey : kb ^ (α - 1) = (α * β * A)⁻¹ := by
    simp only [kb]
    rw [← rpow_mul hq.le, show 1 / (1 - α) * (α - 1) = -1 by field_simp; ring, rpow_neg_one]
  have hkα : kb ^ α = kb ^ (α - 1) * kb := by
    rw [← rpow_add_one hkb.ne']; ring_nf
  refine ⟨?_, ?_⟩
  · rw [hkα, hkey]; field_simp
  · rw [hkey]; field_simp

omit hβ1 in
/-- AKMM, p. 112: every path of (4.17) from `k₀ > 0` converges to `k̄ = (αβA)^{1/(1−α)}`; in logs,
`log k_t − log k̄ = αᵗ(log k₀ − log k̄)`. -/
theorem example_4_5_convergence {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hplan : ∀ t, k (t + 1) = α * β * A * k t ^ α) :
    (∀ t, Real.log (k t) - Real.log ((α * β * A) ^ (1 / (1 - α))) =
      α ^ t * (Real.log (k 0) - Real.log ((α * β * A) ^ (1 / (1 - α))))) ∧
    Tendsto k atTop (𝓝 ((α * β * A) ^ (1 / (1 - α)))) := by
  have hq : 0 < α * β * A := mul_pos (mul_pos hα0 hβ0) hA
  set kb := (α * β * A) ^ (1 / (1 - α))
  have hkb : 0 < kb := rpow_pos_of_pos hq _
  have hpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih => rw [hplan]; exact mul_pos hq (rpow_pos_of_pos ih α)
  have hsteady : kb = α * β * A * kb ^ α := (example_4_5_steady hA hα0 hα1 hβ0).1
  have hlogkb : Real.log kb = Real.log (α * β * A) + α * Real.log kb := by
    conv_lhs => rw [hsteady]
    rw [Real.log_mul hq.ne' (rpow_pos_of_pos hkb α).ne', Real.log_rpow hkb]
  have hlog : ∀ t, Real.log (k t) - Real.log kb = α ^ t * (Real.log (k 0) - Real.log kb) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hplan, Real.log_mul hq.ne' (rpow_pos_of_pos (hpos t) α).ne', Real.log_rpow (hpos t),
        pow_succ]
      linear_combination α * ih - hlogkb
  refine ⟨hlog, ?_⟩
  have hdiff : Tendsto (fun t => Real.log (k t) - Real.log kb) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hα0.le hα1).mul_const
      (Real.log (k 0) - Real.log kb)
    rw [zero_mul] at this
    exact this.congr fun t => (hlog t).symm
  have hl : Tendsto (fun t => Real.log (k t)) atTop (𝓝 (Real.log kb)) := by
    simpa using hdiff.add_const (Real.log kb)
  have := (Real.continuous_exp.tendsto _).comp hl
  simpa [Function.comp_def, Real.exp_log (hpos _), Real.exp_log hkb] using this

/-- **Example 4.5** (AKMM, pp. 111–112): with `u = log`, `f(k) = Ak^α`, `δ = 1`, the plan (4.17)
`k_{t+1} = αβAk_t^α` from `k₀ > 0` is catching-up optimal among plans with positive capital and
consumption, by Proposition 4.4: it satisfies the Euler equation (Example 4.6) and the TVC. -/
theorem example_4_5 {k0 : ℝ} (hk0 : 0 < k0) :
    CatchingUp {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 < p.2 ∧ p.2 < A * p.1 ^ α}
      (fun a b => Real.log (A * a ^ α - b)) β
      (fun t => (fun k => α * β * A * k ^ α)^[t] k0) := by
  have hq1 : α * β < 1 := by nlinarith
  set k : ℕ → ℝ := fun t => (fun k => α * β * A * k ^ α)^[t] k0
  have hplan : ∀ t, k (t + 1) = α * β * A * k t ^ α := fun t =>
    Function.iterate_succ_apply' _ _ _
  have hpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih => rw [hplan]; exact mul_pos (mul_pos (mul_pos hα0 hβ0) hA) (rpow_pos_of_pos ih α)
  set h : ℝ → ℝ := fun x => A * x ^ α
  have hc : ∀ t, h (k t) - k (t + 1) = (1 - α * β) * (A * k t ^ α) := fun t => by
    simp only [h, hplan]; ring
  have hcpos : ∀ t, 0 < h (k t) - k (t + 1) := fun t => by
    rw [hc]; exact mul_pos (by linarith) (mul_pos hA (rpow_pos_of_pos (hpos t) α))
  have hhc : ConcaveOn ℝ (Set.Ici 0) h := (concaveOn_rpow hα0.le hα1.le).smul hA.le
  have hconc := ngm_return_concave (convex_Ioi (0 : ℝ)) (fun x hx y hxy => lt_of_lt_of_le hx hxy)
    strictConcaveOn_log_Ioi.concaveOn strictMonoOn_log.monotoneOn hhc
  have hex : ∀ t, ∃ D : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun p : ℝ × ℝ => Real.log (h p.1 - p.2)) D (k t, k (t + 1)) ∧
        D (1, 0) = (h (k t) - k (t + 1))⁻¹ * (A * (α * k t ^ (α - 1))) ∧
        D (0, 1) = -(h (k t) - k (t + 1))⁻¹ := fun t =>
    ngm_hasFDerivAt (Real.hasDerivAt_log (hcpos t).ne')
      ((hasDerivAt_rpow_const (Or.inl (hpos t).ne')).const_mul A)
  choose D hD using hex
  have htvc := (example_4_5_tvc hA hα0 hα1 hβ0 hβ1 hpos hplan).2
  refine (proposition_4_4 (Γ := fun x => {y | 0 ≤ x ∧ 0 < y ∧ y < A * x ^ α}) hconc
    (fun x y hy => ⟨hy.1, by simp only [h, Set.mem_Ioi]; linarith [hy.2.2]⟩) hβ0.le
    (fun t => ⟨(hpos t).le, hpos (t + 1), by linarith [hcpos t]⟩) D (fun t => (hD t).1)
    (fun t => ?_) (fun t => ?_) ?_ (fun x hx t => ?_)).1
  · rw [(hD t).2.1]
    exact mul_nonneg (inv_pos.2 (hcpos t)).le
      (mul_nonneg hA.le (mul_nonneg hα0.le (rpow_pos_of_pos (hpos t) _).le))
  · -- the Euler equation is Example 4.6 with `s = αβ`
    rw [(hD t).2.2, (hD (t + 1)).2.1]
    have he := (example_4_6 hA hα0 hβ0 (s := α * β) (k := k t) (mul_pos hα0 hβ0) hq1
      (hpos t)).2 rfl
    have e1 : h (k t) - k (t + 1) = A * k t ^ α - α * β * A * k t ^ α := by
      simp only [h, hplan]
    have e2 : h (k (t + 1)) - k (t + 1 + 1) =
        A * (α * β * A * k t ^ α) ^ α - α * β * A * (α * β * A * k t ^ α) ^ α := by
      simp only [h, hplan]
    rw [e1, e2, hplan t]
    rw [← one_div, ← one_div, he]
    ring
  · refine htvc.congr fun t => ?_
    rw [(hD t).2.1]
    simp only [h, one_div]
    ring
  · rcases t with _ | t
    · rw [hx.1]; exact (hpos 0).le
    · exact (hx.2 t).2.1.le

end AKMM.DynamicOptimization

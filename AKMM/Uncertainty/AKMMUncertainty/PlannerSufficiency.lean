/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.PlannerTree
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sufficiency of the Euler equation and the transversality condition; the closed form

AKMM, §7.3.2, pp. 199–200 (with fn. 9). Notation as in `PlannerTree`.

* **"A transversality condition must be added to determine a solution"** (p. 199–200): if `u`
  lies below its tangents, `u′ > 0`, `f(A, ·)` lies below its tangent at the plan's capital, the
  plan is feasible, satisfies (7.13) at every history and the transversality condition
  `βᵗ Σ_{ωᵗ} πₜ(ωᵗ)u′(Cₜ(ωᵗ))Kₜ₊₁(ωᵗ) → 0`, then it solves the planner's problem
  (`pt_euler_tvc_optimal`). The proof sums the tangent inequalities over the tree; the Euler
  equation makes the capital terms telescope (`pt_telescope`), leaving the transversality term.
* **The closed form** (p. 200: "when the utility function is logarithmic, the production function
  is Cobb–Douglas, and `δ = 1` … a constant saving rate is optimal"): with `u = log`,
  `f(A, K) = AK^α`, `0 < α < 1`, the plan `Kₜ₊₁ = αβAₜKₜ^α`, `Cₜ = (1 − αβ)AₜKₜ^α`
  (`pt_logK`, `pt_logC`) is feasible (`pt_log_feasible`), satisfies (7.13) at every history
  (`pt_log_euler`) and the transversality condition (`pt_log_tvc`), and is optimal when TFP takes
  values in `[a, ā] ⊂ (0, ∞)` (`pt_log_optimal`).

Departure: the book asserts these; the TVC is stated in the form the proof uses (the marginal-
utility value of the capital stock), and the closed form needs `0 < α < 1`, `0 < β < 1` and TFP
bounded away from zero and infinity (for the utility series to converge).
-/

namespace AKMM.Uncertainty

open Miao.CompleteMarkets Filter Topology AKMM.CompetitiveEquilibrium Real

variable {S : Type*} [Fintype S] {α' : Type*}

/-- The capital terms telescope: `Σ_{t ≤ n} (E_t − D_t) = −D_n` when `E₀ = 0` and
`E_{t+1} = D_t`. -/
theorem pt_telescope {D E : ℕ → ℝ} (h0 : E 0 = 0) (h : ∀ t, E (t + 1) = D t) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), (E t - D t) = -D n := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ih, h n]; ring

/-- **AKMM, pp. 199–200: the Euler equation and the transversality condition are sufficient.**
Let `β > 0`, `u(c′) ≤ u(c) + u′(c)(c′ − c)` on `(0, ∞)`, `u′(Cₜ) > 0`, `K₀ ≥ 0`, and
`f(Aₜ, k′) ≤ f(Aₜ, Kₜ) + f₂(Aₜ, Kₜ)(k′ − Kₜ)` for `k′ ≥ 0` at the plan's capital `Kₜ`. A feasible
plan satisfying (7.13) at every history and
`βᵗ Σ_{ωᵗ} πₜ(ωᵗ)u′(Cₜ(ωᵗ))Kₜ₊₁(ωᵗ) → 0` solves the planner's problem. -/
theorem pt_euler_tvc_optimal (T : BPTree S) {β : ℝ} (hβ : 0 < β) {u du : ℝ → ℝ}
    (hu : ∀ c c', 0 < c → 0 < c' → u c' ≤ u c + du c * (c' - c)) {f f2 : α' → ℝ → ℝ}
    {A : List S → α'} {K0 : ℝ} (hK0 : 0 ≤ K0) {C K : List S → ℝ}
    (hf : ∀ h k', 0 ≤ k' → f (A h) k' ≤
      f (A h) (pt_prevK K0 K h) + f2 (A h) (pt_prevK K0 K h) * (k' - pt_prevK K0 K h))
    (hdu : ∀ h, 0 < du (C h)) (hfeas : pt_Feasible T β u f A K0 C K)
    (heuler : ∀ h, du (C h) =
      β * ∑ s, T.pr (s :: h) / T.pr h * du (C (s :: h)) * f2 (A (s :: h)) (K h))
    (htvc : Tendsto (fun t => β ^ t * bp_nodeSum t (fun h => T.pr h * du (C h) * K h)) atTop
      (𝓝 0)) :
    pt_Optimal T β u f A K0 C K := by
  refine ⟨hfeas, fun C' K' hfeas' => ?_⟩
  obtain ⟨hC, hK, hR, hsum⟩ := hfeas
  obtain ⟨hC', hK', hR', hsum'⟩ := hfeas'
  have hprev : ∀ h, 0 ≤ pt_prevK K0 K h := fun h => by
    cases h with
    | nil => exact hK0
    | cons s g => exact hK g
  have hprev' : ∀ h, 0 ≤ pt_prevK K0 K' h := fun h => by
    cases h with
    | nil => exact hK0
    | cons s g => exact hK' g
  set D : ℕ → ℝ := fun t => β ^ t * bp_nodeSum t (fun h => T.pr h * du (C h) * (K' h - K h))
    with hD
  set E : ℕ → ℝ := fun t => β ^ t * bp_nodeSum t (fun h => T.pr h * du (C h) *
    (f2 (A h) (pt_prevK K0 K h) * (pt_prevK K0 K' h - pt_prevK K0 K h))) with hE
  -- the date-`t` utility gain is at most `E_t − D_t`
  have hstep : ∀ t, pt_util T β u C' t - pt_util T β u C t ≤ E t - D t := fun t => by
    simp only [pt_util, hD, hE, ← mul_sub, ← bp_nodeSum_sub]
    refine mul_le_mul_of_nonneg_left (bp_nodeSum_mono t _ _ fun h => ?_)
      (pow_nonneg hβ.le t)
    have h1 := hu (C h) (C' h) (hC h) (hC' h)
    have h2 := hf h (pt_prevK K0 K' h) (hprev' h)
    have hc : C' h - C h =
        f (A h) (pt_prevK K0 K' h) - K' h - (f (A h) (pt_prevK K0 K h) - K h) := by
      have := hR h; have := hR' h; linarith
    have hp := T.pr_pos h
    have hd := hdu h
    have h3 : u (C' h) - u (C h) ≤
        du (C h) * (f2 (A h) (pt_prevK K0 K h) * (pt_prevK K0 K' h - pt_prevK K0 K h) -
          (K' h - K h)) := by
      have : du (C h) * (C' h - C h) ≤ du (C h) * (f2 (A h) (pt_prevK K0 K h) *
          (pt_prevK K0 K' h - pt_prevK K0 K h) - (K' h - K h)) :=
        mul_le_mul_of_nonneg_left (by rw [hc]; linarith) hd.le
      linarith
    have := mul_le_mul_of_nonneg_left h3 hp.le
    nlinarith
  -- `E₀ = 0` and `E_{t+1} = D_t` by the Euler equation
  have hE0 : E 0 = 0 := by simp [hE, bp_nodeSum_zero, pt_prevK]
  have hED : ∀ t, E (t + 1) = D t := fun t => by
    simp only [hE, hD, bp_nodeSum_succ, pt_prevK, pow_succ]
    rw [mul_assoc]
    congr 1
    rw [← bp_nodeSum_smul]
    refine bp_nodeSum_congr t _ _ fun h _ => ?_
    have he := heuler h
    have hp := (T.pr_pos h).ne'
    rw [Finset.mul_sum]
    have e : T.pr h * du (C h) = β * ∑ s, T.pr (s :: h) * du (C (s :: h)) *
        f2 (A (s :: h)) (K h) := by
      rw [he, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by field_simp
    rw [e, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  -- partial sums of the gains are bounded by the transversality term
  have hbound : ∀ n, ∑ t ∈ Finset.range (n + 1), (pt_util T β u C' t - pt_util T β u C t) ≤
      β ^ n * bp_nodeSum n (fun h => T.pr h * du (C h) * K h) := fun n => by
    refine (Finset.sum_le_sum fun t _ => hstep t).trans ?_
    rw [pt_telescope hE0 hED n]
    simp only [hD, ← mul_neg, ← bp_nodeSum_neg]
    refine mul_le_mul_of_nonneg_left (bp_nodeSum_mono n _ _ fun h => ?_) (pow_nonneg hβ.le n)
    have := mul_pos (T.pr_pos h) (hdu h)
    nlinarith [hK' h]
  have hs := (hsum'.sub hsum).hasSum.tendsto_sum_nat
  have hs1 := (tendsto_add_atTop_iff_nat 1).2 hs
  have hle := le_of_tendsto_of_tendsto' hs1 htvc hbound
  rw [hsum'.tsum_sub hsum] at hle
  linarith

/-! ### The closed form -/

/-- AKMM, p. 200: capital under the constant saving rate, `Kₜ₊₁ = αβAₜKₜ^α`. -/
noncomputable def pt_logK (α β : ℝ) (A : List S → ℝ) (K0 : ℝ) : List S → ℝ
  | [] => α * β * A [] * K0 ^ α
  | s :: g => α * β * A (s :: g) * pt_logK α β A K0 g ^ α

/-- AKMM, p. 200: consumption under the constant saving rate, `Cₜ = (1 − αβ)AₜKₜ^α`. -/
noncomputable def pt_logC (α β : ℝ) (A : List S → ℝ) (K0 : ℝ) (h : List S) : ℝ :=
  (1 - α * β) * A h * pt_prevK K0 (pt_logK α β A K0) h ^ α

omit [Fintype S] in
theorem pt_logK_eq (α β : ℝ) (A : List S → ℝ) (K0 : ℝ) (h : List S) :
    pt_logK α β A K0 h = α * β * A h * pt_prevK K0 (pt_logK α β A K0) h ^ α := by
  cases h <;> rfl

omit [Fintype S] in
theorem pt_logK_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {A : List S → ℝ} (hA : ∀ h, 0 < A h)
    {K0 : ℝ} (hK0 : 0 < K0) (h : List S) :
    0 < pt_logK α β A K0 h ∧ 0 < pt_prevK K0 (pt_logK α β A K0) h := by
  induction h with
  | nil =>
    have := hA []
    exact ⟨by simp only [pt_logK]; have := rpow_pos_of_pos hK0 α; positivity, hK0⟩
  | cons s g ih =>
    refine ⟨?_, ih.1⟩
    simp only [pt_logK]
    have := rpow_pos_of_pos ih.1 α
    have := hA (s :: g)
    positivity

omit [Fintype S] in
/-- AKMM, p. 200: the constant-saving plan satisfies (7.11) with `f(A, K) = AK^α` and has
positive consumption and capital. -/
theorem pt_log_resource {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α * β < 1)
    {A : List S → ℝ} (hA : ∀ h, 0 < A h) {K0 : ℝ} (hK0 : 0 < K0) :
    pt_Resource (fun a k => a * k ^ α) A K0 (pt_logC α β A K0) (pt_logK α β A K0) ∧
      (∀ h, 0 < pt_logC α β A K0 h) ∧ ∀ h, 0 ≤ pt_logK α β A K0 h := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => (pt_logK_pos hα hβ hA hK0 h).1.le⟩
  · rw [pt_logK_eq, pt_logC]; ring
  · have := rpow_pos_of_pos (pt_logK_pos hα hβ hA hK0 h).2 α
    have := hA h
    have : 0 < 1 - α * β := by linarith
    simp only [pt_logC]
    positivity

/-- **AKMM, p. 200: the constant saving rate satisfies the Euler equation (7.13)** at every
history, with `u = log`, `u′(c) = 1/c`, `f(A, K) = AK^α`, `f₂(A, K) = αAK^{α−1}`. -/
theorem pt_log_euler (T : BPTree S) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α * β < 1)
    {A : List S → ℝ} (hA : ∀ h, 0 < A h) {K0 : ℝ} (hK0 : 0 < K0) (h : List S) :
    (pt_logC α β A K0 h)⁻¹ = β * ∑ s, T.pr (s :: h) / T.pr h * (pt_logC α β A K0 (s :: h))⁻¹ *
      (α * A (s :: h) * pt_logK α β A K0 h ^ (α - 1)) := by
  have hK := (pt_logK_pos hα hβ hA hK0 h).1
  have hKp := (pt_logK_pos hα hβ hA hK0 h).2
  have h1 : 0 < 1 - α * β := by linarith
  have hterm : ∀ s, (pt_logC α β A K0 (s :: h))⁻¹ *
      (α * A (s :: h) * pt_logK α β A K0 h ^ (α - 1)) =
      α / ((1 - α * β) * pt_logK α β A K0 h) := fun s => by
    have hAs := (hA (s :: h)).ne'
    have hKa := (rpow_pos_of_pos hK α).ne'
    simp only [pt_logC, pt_prevK]
    rw [rpow_sub_one hK.ne']
    field_simp
  have hsum : ∑ s, T.pr (s :: h) / T.pr h * (pt_logC α β A K0 (s :: h))⁻¹ *
      (α * A (s :: h) * pt_logK α β A K0 h ^ (α - 1)) =
      α / ((1 - α * β) * pt_logK α β A K0 h) := by
    rw [Finset.sum_congr rfl fun s _ => by rw [mul_assoc, hterm s], ← Finset.sum_mul,
      (tree_condProb_sum T h).1, one_mul]
  rw [hsum, pt_logK_eq]
  have := (rpow_pos_of_pos hKp α).ne'
  have := (hA h).ne'
  simp only [pt_logC]
  field_simp

/-- AKMM, p. 200: the constant saving rate satisfies the transversality condition:
`βᵗ Σ πₜKₜ₊₁/Cₜ = βᵗαβ/(1 − αβ) → 0` for `β < 1`. -/
theorem pt_log_tvc (T : BPTree S) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (hαβ : α * β < 1) {A : List S → ℝ} (hA : ∀ h, 0 < A h) {K0 : ℝ} (hK0 : 0 < K0) :
    Tendsto (fun t => β ^ t * bp_nodeSum t (fun h => T.pr h * (pt_logC α β A K0 h)⁻¹ *
      pt_logK α β A K0 h)) atTop (𝓝 0) := by
  have h1 : 0 < 1 - α * β := by linarith
  have e : ∀ t, bp_nodeSum t (fun h => T.pr h * (pt_logC α β A K0 h)⁻¹ *
      pt_logK α β A K0 h) = α * β / (1 - α * β) := fun t => by
    rw [← bp_nodeSum_const T t (α * β / (1 - α * β))]
    refine bp_nodeSum_congr t _ _ fun h _ => ?_
    have := (rpow_pos_of_pos (pt_logK_pos hα hβ hA hK0 h).2 α).ne'
    have := (hA h).ne'
    rw [mul_assoc, pt_logK_eq, pt_logC]
    field_simp
  simp only [e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const (α * β / (1 - α * β))

omit [Fintype S] in
/-- Bounds on `log K` along the constant-saving plan when `a ≤ Aₜ ≤ ā`. -/
theorem pt_logK_log_bound {α β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    {A : List S → ℝ} {a abar : ℝ} (ha : 0 < a) (hA : ∀ h, a ≤ A h ∧ A h ≤ abar) {K0 : ℝ}
    (hK0 : 0 < K0) (h : List S) :
    |Real.log (pt_prevK K0 (pt_logK α β A K0) h)| ≤
      max |Real.log K0| ((|Real.log (α * β)| + max |Real.log a| |Real.log abar|) / (1 - α)) := by
  have hApos : ∀ h, 0 < A h := fun h => lt_of_lt_of_le ha (hA h).1
  set L := |Real.log (α * β)| + max |Real.log a| |Real.log abar| with hL
  set M := max |Real.log K0| (L / (1 - α)) with hM
  have h1α : 0 < 1 - α := by linarith
  have hlogA : ∀ h, |Real.log (A h)| ≤ max |Real.log a| |Real.log abar| := fun h => by
    rw [abs_le]
    have l1 := Real.log_le_log ha (hA h).1
    have l2 := Real.log_le_log (hApos h) (hA h).2
    constructor
    · have := neg_abs_le (Real.log a)
      have := le_max_left |Real.log a| |Real.log abar|
      linarith
    · have := le_abs_self (Real.log abar)
      have := le_max_right |Real.log a| |Real.log abar|
      linarith
  have hLM : L + α * M ≤ M := by
    have : L / (1 - α) ≤ M := le_max_right _ _
    rw [div_le_iff₀ h1α] at this
    linarith
  induction h with
  | nil => exact le_max_left _ _
  | cons s g ih =>
    have hKg := (pt_logK_pos hα hβ hApos hK0 g).1
    have hKp := (pt_logK_pos hα hβ hApos hK0 g).2
    simp only [pt_prevK]
    rw [pt_logK_eq, Real.log_mul (by have := hApos g; positivity) (rpow_pos_of_pos hKp α).ne',
      Real.log_mul (by positivity) (hApos g).ne', Real.log_rpow hKp]
    calc |Real.log (α * β) + Real.log (A g) + α * Real.log (pt_prevK K0 (pt_logK α β A K0) g)|
        ≤ |Real.log (α * β)| + |Real.log (A g)| +
          α * |Real.log (pt_prevK K0 (pt_logK α β A K0) g)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_pos hα]
          linarith [abs_add_le (Real.log (α * β)) (Real.log (A g))]
      _ ≤ L + α * M := by
          have := hlogA g
          have := mul_le_mul_of_nonneg_left ih hα.le
          rw [hL]; linarith
      _ ≤ M := hLM

/-- **AKMM, p. 200: the constant saving rate is optimal.** With `u = log`, `f(A, K) = AK^α`,
`0 < α < 1`, `0 < β < 1`, `K₀ > 0` and TFP in `[a, ā]` with `a > 0`, the plan
`Kₜ₊₁ = αβAₜKₜ^α` solves the planner's problem. -/
theorem pt_log_optimal (T : BPTree S) {α β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) {A : List S → ℝ} {a abar : ℝ} (ha : 0 < a) (hA : ∀ h, a ≤ A h ∧ A h ≤ abar)
    {K0 : ℝ} (hK0 : 0 < K0) :
    pt_Optimal T β Real.log (fun a k => a * k ^ α) A K0 (pt_logC α β A K0)
      (pt_logK α β A K0) := by
  have hApos : ∀ h, 0 < A h := fun h => lt_of_lt_of_le ha (hA h).1
  have hαβ : α * β < 1 := by nlinarith
  obtain ⟨hR, hC, hK⟩ := pt_log_resource hα hβ hαβ hApos hK0
  -- the utility series converges
  set M := max |Real.log K0| ((|Real.log (α * β)| + max |Real.log a| |Real.log abar|) / (1 - α))
  set B := |Real.log (1 - α * β)| + max |Real.log a| |Real.log abar| + α * M with hB
  have hlogC : ∀ h, |Real.log (pt_logC α β A K0 h)| ≤ B := fun h => by
    have hKp := (pt_logK_pos hα hβ hApos hK0 h).2
    have h1 : 0 < 1 - α * β := by linarith
    have hlogA : |Real.log (A h)| ≤ max |Real.log a| |Real.log abar| := by
      rw [abs_le]
      have l1 := Real.log_le_log ha (hA h).1
      have l2 := Real.log_le_log (hApos h) (hA h).2
      constructor
      · have := neg_abs_le (Real.log a)
        have := le_max_left |Real.log a| |Real.log abar|
        linarith
      · have := le_abs_self (Real.log abar)
        have := le_max_right |Real.log a| |Real.log abar|
        linarith
    have hk := pt_logK_log_bound hα hα1 hβ ha hA hK0 h
    rw [pt_logC, Real.log_mul (by have := hApos h; positivity) (rpow_pos_of_pos hKp α).ne',
      Real.log_mul h1.ne' (hApos h).ne', Real.log_rpow hKp]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hα]
    have := abs_add_le (Real.log (1 - α * β)) (Real.log (A h))
    have := mul_le_mul_of_nonneg_left hk hα.le
    rw [hB]; linarith
  have hsum : Summable (pt_util T β Real.log (pt_logC α β A K0)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ.le hβ1).mul_right B)
      fun t => ?_
    rw [Real.norm_eq_abs, pt_util, abs_mul, abs_of_pos (pow_pos hβ t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_pos hβ t).le
    rw [abs_le]
    constructor
    · have := bp_nodeSum_mono t (fun h => T.pr h * (-B))
        (fun h => T.pr h * Real.log (pt_logC α β A K0 h)) fun h =>
          mul_le_mul_of_nonneg_left (neg_le_of_abs_le (hlogC h)) (T.pr_pos h).le
      rw [bp_nodeSum_const] at this
      exact this
    · have := bp_nodeSum_mono t (fun h => T.pr h * Real.log (pt_logC α β A K0 h))
        (fun h => T.pr h * B) fun h =>
          mul_le_mul_of_nonneg_left (le_of_abs_le (hlogC h)) (T.pr_pos h).le
      rw [bp_nodeSum_const] at this
      exact this
  -- apply sufficiency
  refine pt_euler_tvc_optimal T hβ (du := fun c => c⁻¹)
    (f2 := fun a k => α * a * k ^ (α - 1)) (fun c c' hc hc' => ce_log_tangent hc hc')
    hK0.le (fun h k' hk' => ?_) (fun h => inv_pos.2 (hC h)) ⟨hC, hK, hR, hsum⟩
    (fun h => pt_log_euler T hα hβ hαβ hApos hK0 h) (pt_log_tvc T hα hβ hβ1 hαβ hApos hK0)
  -- the Cobb–Douglas tangent inequality
  have hk := (pt_logK_pos hα hβ hApos hK0 h).2
  set k := pt_prevK K0 (pt_logK α β A K0) h
  have hs : -1 ≤ k' / k - 1 := by have := div_nonneg hk' hk.le; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hα.le hα1.le
  rw [show 1 + (k' / k - 1) = k' / k by ring, div_rpow hk' hk.le] at hb
  have hka := rpow_pos_of_pos hk α
  rw [div_le_iff₀ hka] at hb
  have e : α * A h * k ^ (α - 1) * (k' - k) = A h * (k ^ α * (α * (k' / k - 1))) := by
    rw [rpow_sub_one hk.ne']; field_simp
  rw [e]
  have := hApos h
  nlinarith

end AKMM.Uncertainty

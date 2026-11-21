/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.IHDetPrinciple
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The unit-elastic growth model as a deterministic dynamic program

Copied from `RecursiveMethods/DeterministicDP` (modules `Assumption42` and `LogGrowth`, SLP
§§4.1 and 4.4, pp. 69 and 93–95), namespace renamed to `Miao.InfiniteHorizonDP.IHDet`; only the
parts used for Miao, Example 7.1.1 (pp. 200–201), are copied.

* `tendsto_of_summable_pos`, `assumption42_of_summable_pos`, `summable_max_of_le_geometric`:
  partial sums converge in `R̄` when the positive parts are summable.
* `logΓ`, `logF`: `Γ(k) = (0, k^α)` and `F(k, y) = ln(k^α − y)` on `(0, ∞)`. The book's
  constraint `C, K′ ≥ 0` gives `ln 0 = −∞`, while `F` must be real-valued; the open interval has
  the same supremum.
* `coefB = α/(1 − αβ)`, `coefC = ln(1 − αβ) + (αβ/(1 − αβ)) ln(αβ)`, `logPolicy` (`αβk^α`),
  `log_objective_le` (the maximisation in the Bellman equation for `A + B ln k`),
  `log_capital_le` (`ln k_t ≤ αᵗ ln k₀`), `logF_le`, `log_assumption42`.
-/

open Filter Topology Real

namespace Miao.InfiniteHorizonDP

namespace IHDet

/-- Partial sums of a real sequence converge in `R̄` if the positive parts are summable. -/
theorem tendsto_of_summable_pos (a : ℕ → ℝ) (h : Summable fun t => max (a t) 0) :
    ∃ L : EReal,
      Tendsto (fun n => ((∑ t ∈ Finset.range (n + 1), a t : ℝ) : EReal)) atTop (𝓝 L) := by
  set P : ℕ → ℝ := fun n => ∑ t ∈ Finset.range (n + 1), max (a t) 0
  set N : ℕ → ℝ := fun n => ∑ t ∈ Finset.range (n + 1), max (-a t) 0
  have hP : Tendsto P atTop (𝓝 (∑' t, max (a t) 0)) :=
    h.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hNmono : Monotone fun n => ((N n : ℝ) : EReal) := fun m n hmn => by
    refine EReal.coe_le_coe_iff.2 (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by omega)) fun _ _ _ => le_max_right _ _)
  have hN := tendsto_atTop_iSup hNmono
  have hsplit : ∀ n, ((∑ t ∈ Finset.range (n + 1), a t : ℝ) : EReal) =
      ((P n : ℝ) : EReal) + -((N n : ℝ) : EReal) := fun n => by
    rw [← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    simp only [P, N, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_total (a t) 0 with h0 | h0
    · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
  refine ⟨((∑' t, max (a t) 0 : ℝ) : EReal) + -(⨆ n, ((N n : ℝ) : EReal)), ?_⟩
  simp only [hsplit]
  refine Tendsto.comp (f := fun n => (((P n : ℝ) : EReal), -((N n : ℝ) : EReal)))
    (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))
    ((EReal.tendsto_coe.2 hP).prodMk_nhds (continuous_neg.tendsto _ |>.comp hN))

variable {X : Type*} {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ}

/-- **p. 69.** Assumption 4.2 holds if `Σ βᵗF⁺(x_t, x_{t+1}) < ∞` along every feasible plan. -/
theorem assumption42_of_summable_pos
    (h : ∀ x₀, ∀ x ∈ Feasible Γ x₀, Summable fun t => max (β ^ t * F (x t) (x (t + 1))) 0) :
    Assumption42 Γ F β := fun x₀ x hx => tendsto_of_summable_pos _ (h x₀ x hx)

/-- Positive multiples of a geometric bound are summable. -/
theorem summable_max_of_le_geometric {b : ℕ → ℝ} {c r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hc : 0 ≤ c) (hb : ∀ t, b t ≤ c * r ^ t) : Summable fun t => max (b t) 0 :=
  Summable.of_nonneg_of_le (fun _ => le_max_right _ _)
    (fun t => max_le (hb t) (mul_nonneg hc (pow_nonneg hr0 t)))
    ((summable_geometric_of_lt_one hr0 hr).mul_left c)

/-- `(0, ∞)`. -/
abbrev PosR := {k : ℝ // 0 < k}

variable {α β : ℝ}

/-- `Γ(k) = (0, k^α)`. -/
def logΓ (α : ℝ) (k : PosR) : Set PosR := {y | y.1 < k.1 ^ α}

/-- `F(k, y) = ln(k^α − y)`. -/
noncomputable def logF (α : ℝ) (k y : PosR) : ℝ := Real.log (k.1 ^ α - y.1)

/-- `B = α/(1 − αβ)`. -/
noncomputable def coefB (α β : ℝ) : ℝ := α / (1 - α * β)

/-- `C = ln(1 − αβ) + (αβ/(1 − αβ)) ln(αβ)`. -/
noncomputable def coefC (α β : ℝ) : ℝ :=
  Real.log (1 - α * β) + α * β / (1 - α * β) * Real.log (α * β)

/-- The optimal saving `αβk^α ∈ Γ(k)`. -/
noncomputable def logPolicy (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k : PosR) : PosR :=
  ⟨α * β * k.1 ^ α, by have := rpow_pos_of_pos k.2 α; positivity⟩

variable (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
include hα0 hα1 hβ0 hβ1

omit hβ0 in
theorem αβ_lt_one : α * β < 1 := by nlinarith

omit hβ0 in
theorem coefB_pos : 0 < coefB α β := div_pos hα0 (by linarith [αβ_lt_one hα0 hα1 hβ1])

theorem logPolicy_mem (k : PosR) : logPolicy α β hα0 hβ0 k ∈ logΓ α k := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have := rpow_pos_of_pos k.2 α
  change α * β * k.1 ^ α < k.1 ^ α
  nlinarith

/-- The maximization: for `y ∈ (0, k^α)`,
`ln(k^α − y) + β(A + B ln y) ≤ ln((1 − αβ)k^α) + β(A + B ln(αβk^α))`. -/
theorem log_objective_le (A : ℝ) (k y : PosR) (hy : y ∈ logΓ α k) :
    logF α k y + β * (A + coefB α β * Real.log y.1) ≤
      logF α k (logPolicy α β hα0 hβ0 k) +
        β * (A + coefB α β * Real.log (logPolicy α β hα0 hβ0 k).1) := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have hab : 0 < α * β := mul_pos hα0 hβ0
  set c := k.1 ^ α
  have hc : 0 < c := rpow_pos_of_pos k.2 α
  have hy0 : 0 < y.1 := y.2
  have hyc : y.1 < c := hy
  simp only [logF, logPolicy, coefB]
  have hcy : 0 < c - y.1 := by linarith
  have hcs : 0 < c - α * β * c := by nlinarith
  have hsc : 0 < α * β * c := by positivity
  -- `ln u ≤ u − 1` at `u = (c − y)/((1 − αβ)c)` and `u = y/(αβc)`
  have e1 := Real.log_le_sub_one_of_pos (div_pos hcy hcs)
  have e2 := Real.log_le_sub_one_of_pos (div_pos hy0 hsc)
  rw [Real.log_div hcy.ne' hcs.ne'] at e1
  rw [Real.log_div hy0.ne' hsc.ne'] at e2
  have hk : 0 < β * (α / (1 - α * β)) := mul_pos hβ0 (div_pos hα0 (by linarith))
  have e2' := mul_le_mul_of_nonneg_left e2 hk.le
  have hne : (1 - α * β) ≠ 0 := by linarith
  have key : (c - y.1) / (c - α * β * c) - 1 + β * (α / (1 - α * β)) * (y.1 / (α * β * c) - 1)
      = 0 := by
    rw [show c - α * β * c = (1 - α * β) * c by ring]
    field_simp
    ring
  nlinarith

omit hα1 hβ0 hβ1 in
/-- Along feasible plans, `ln k_t ≤ αᵗ ln k₀` (the technology bound (4), p. 94). -/
theorem log_capital_le {k₀ : PosR} {k : ℕ → PosR} (hk : k ∈ Feasible (logΓ α) k₀) (t : ℕ) :
    Real.log (k t).1 ≤ α ^ t * Real.log k₀.1 := by
  induction t with
  | zero => simp [hk.1]
  | succ t ih =>
    have h := Real.log_lt_log (k (t + 1)).2 (hk.2 t)
    rw [Real.log_rpow (k t).2] at h
    calc Real.log (k (t + 1)).1 ≤ α * Real.log (k t).1 := h.le
      _ ≤ α * (α ^ t * Real.log k₀.1) := mul_le_mul_of_nonneg_left ih hα0.le
      _ = α ^ (t + 1) * Real.log k₀.1 := by ring

omit hα1 hβ0 hβ1 in
/-- (4), p. 94: `F(k_t, k_{t+1}) ≤ αᵗ⁺¹ ln k₀`. -/
theorem logF_le {k₀ : PosR} {k : ℕ → PosR} (hk : k ∈ Feasible (logΓ α) k₀) (t : ℕ) :
    logF α (k t) (k (t + 1)) ≤ α ^ (t + 1) * Real.log k₀.1 := by
  have hc : 0 < (k t).1 ^ α := rpow_pos_of_pos (k t).2 α
  have hlt : (k (t + 1)).1 < (k t).1 ^ α := hk.2 t
  have hpos : 0 < (k t).1 ^ α - (k (t + 1)).1 := by linarith
  calc logF α (k t) (k (t + 1)) ≤ Real.log ((k t).1 ^ α) :=
        Real.log_le_log hpos (by linarith [(k (t + 1)).2])
    _ = α * Real.log (k t).1 := Real.log_rpow (k t).2 α
    _ ≤ α * (α ^ t * Real.log k₀.1) :=
        mul_le_mul_of_nonneg_left (log_capital_le hα0 hk t) hα0.le
    _ = α ^ (t + 1) * Real.log k₀.1 := by ring

theorem log_assumption42 : Assumption42 (logΓ α) (logF α) β :=
  assumption42_of_summable_pos fun k₀ k hk =>
    summable_max_of_le_geometric (mul_pos hα0 hβ0).le (αβ_lt_one hα0 hα1 hβ1)
      (by positivity : (0 : ℝ) ≤ α * |Real.log k₀.1|) fun t => by
        have := logF_le hα0 hk t
        calc β ^ t * logF α (k t) (k (t + 1)) ≤ β ^ t * (α ^ (t + 1) * |Real.log k₀.1|) :=
              mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_left
                (le_abs_self _) (pow_nonneg hα0.le _))) (pow_nonneg hβ0.le t)
          _ = α * |Real.log k₀.1| * (α * β) ^ t := by rw [mul_pow]; ring

end IHDet

end Miao.InfiniteHorizonDP

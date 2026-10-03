/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Basics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The Gumbel max trick

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.3.2 (pp. 166–168).

When every feasible action's reward carries an independent standard Gumbel
shock, the expected maximum in the expected value Bellman operator has the
closed form `ln ∑ exp(·)` (Lemma 5.3.2, cited from Huijben et al.), and the
operator becomes (5.36):
`(Rg)(y, a) = ∑_{y'} ln[∑_{a'} exp(r(y', a') + βg(y', a'))] P(y, a, y')`.
Proposition 5.3.3: this `R` is a contraction of modulus `β`, by Blackwell's
condition: it is order preserving and `R(g + c) = Rg + βc`.

Exercise 5.3.2 is formalised at the level of distribution functions: the
Gumbel CDF with mode `μ` is `F_μ(z) = exp(−exp(−(z − μ)))`, and shifting a
random variable by `λ` shifts the mode, `F_μ(z − λ) = F_{μ+λ}(z)`. The book
prints `exp(−exp(z − μ))`, which is decreasing in `z` and so cannot be a
distribution function; the sign inside is corrected here. The mean `μ + γ` and
Lemma 5.3.2 itself are statements about integrals against the Gumbel density
and are not claimed.
-/

open Finset Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

/-- The Gumbel distribution function with mode `μ` (p. 167, with the sign corrected):
`F_μ(z) = exp(−exp(−(z − μ)))`. -/
noncomputable def gumbelCDF (μ z : ℝ) : ℝ := Real.exp (-Real.exp (-(z - μ)))

/-- Exercise 5.3.2 (p. 167), at the level of distribution functions: if `Z ∼ G(μ)` then
`Z + λ ∼ G(μ + λ)`, since `P{Z + λ ≤ z} = F_μ(z − λ) = F_{μ+λ}(z)`. -/
theorem gumbelCDF_shift (μ lam z : ℝ) : gumbelCDF μ (z - lam) = gumbelCDF (μ + lam) z := by
  unfold gumbelCDF
  congr 3
  ring

/-- The corrected CDF is increasing in `z`, as a distribution function must be. -/
theorem gumbelCDF_monotone (μ : ℝ) : Monotone (gumbelCDF μ) := by
  intro z z' hzz'
  unfold gumbelCDF
  exact Real.exp_le_exp.2 (neg_le_neg (Real.exp_le_exp.2 (by linarith)))

variable {Y A : Type*} [Fintype Y] [Fintype A]

/-- The Gumbel expected value Bellman operator (5.36) on `ℝ^{Y × A}`, for unrestricted actions:
`(Rg)(y, a) = ∑_{y'} ln[∑_{a'} exp(r(y', a') + βg(y', a'))] P(y, a, y')`. -/
noncomputable def gumbelR (r : Y → A → ℝ) (P : Y → A → Y → ℝ) (β : ℝ) (g : Y × A → ℝ) :
    Y × A → ℝ := fun p =>
  ∑ y', Real.log (∑ a', Real.exp (r y' a' + β * g (y', a'))) * P p.1 p.2 y'

/-- The log-sum-exp is order preserving. -/
theorem logSumExp_mono [Nonempty A] {f f' : A → ℝ} (h : ∀ a, f a ≤ f' a) :
    Real.log (∑ a, Real.exp (f a)) ≤ Real.log (∑ a, Real.exp (f' a)) := by
  apply Real.log_le_log
  · exact sum_pos (fun a _ => Real.exp_pos _) univ_nonempty
  · exact sum_le_sum fun a _ => Real.exp_le_exp.2 (h a)

/-- Adding a constant inside the log-sum-exp adds it outside. -/
theorem logSumExp_add_const [Nonempty A] (f : A → ℝ) (c : ℝ) :
    Real.log (∑ a, Real.exp (f a + c)) = Real.log (∑ a, Real.exp (f a)) + c := by
  simp only [Real.exp_add, ← sum_mul]
  rw [Real.log_mul (sum_pos (fun a _ => Real.exp_pos _) univ_nonempty).ne' (Real.exp_pos c).ne',
    Real.log_exp]

/-- The Gumbel operator is order preserving (proof of Proposition 5.3.3). -/
theorem gumbelR_monotone [Nonempty A] (r : Y → A → ℝ) {P : Y → A → Y → ℝ}
    (hP : ∀ y a y', 0 ≤ P y a y') {β : ℝ} (hβ : 0 ≤ β) : Monotone (gumbelR r P β) := by
  intro g g' hgg' p
  unfold gumbelR
  refine sum_le_sum fun y' _ => mul_le_mul_of_nonneg_right ?_ (hP _ _ _)
  exact logSumExp_mono fun a' => add_le_add le_rfl (mul_le_mul_of_nonneg_left (hgg' (y', a')) hβ)

/-- `R(g + c) = Rg + βc` (proof of Proposition 5.3.3). -/
theorem gumbelR_add_const [Nonempty A] (r : Y → A → ℝ) {P : Y → A → Y → ℝ}
    (hP : ∀ y a, ∑ y', P y a y' = 1) (β : ℝ) (g : Y × A → ℝ) (c : ℝ) :
    gumbelR r P β (g + fun _ => c) = gumbelR r P β g + fun _ => β * c := by
  funext p
  simp only [gumbelR, Pi.add_apply]
  have h : ∀ y', Real.log (∑ a', Real.exp (r y' a' + β * (g (y', a') + c))) =
      Real.log (∑ a', Real.exp (r y' a' + β * g (y', a'))) + β * c := by
    intro y'
    rw [← logSumExp_add_const (fun a' => r y' a' + β * g (y', a')) (β * c)]
    congr 1
    exact sum_congr rfl fun a' _ => by ring_nf
  simp only [h, add_mul, sum_add_distrib, ← mul_sum, hP p.1 p.2, mul_one]

/-- **Proposition 5.3.3** (p. 167): the Gumbel operator (5.36) is a contraction of modulus `β` on
`ℝ^{Y × A}`, by Blackwell's condition. -/
theorem isContractionOn_gumbelR [Nonempty A] (r : Y → A → ℝ) {P : Y → A → Y → ℝ}
    (hP0 : ∀ y a y', 0 ≤ P y a y') (hP1 : ∀ y a, ∑ y', P y a y' = 1) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : IsContractionOn (gumbelR r P β) Set.univ β :=
  isContractionOn_of_blackwell hβ0 hβ1 (gumbelR_monotone r hP0 hβ0) fun g c _ =>
    (gumbelR_add_const r hP1 β g c).le

end SargentStachurski.MarkovDecisionProcesses

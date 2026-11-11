/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The endowment chain and the autarky value (Miao §22.1, pp. 774–775)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1, pp. 774–775. The agent's
endowment follows a Markov chain on finitely many states `θ₁, …, θₙ` (an arbitrary finite type
`ι`) with transition probabilities `pl i j = π(θⱼ | θᵢ)`. The outside option is the autarky value
`U_d(y_t) = E_t Σ_{s ≥ t} β^{s-t} u(y_s)`.

We define the one-step conditional expectation `lc_condExp`, the autarky value `lc_autarky` as the
discounted series of iterated conditional expectations of a reward `r = u ∘ θ`, and prove:
the series converges, it satisfies the recursion `U_d = r + β π U_d`, it is the unique solution
of that recursion, and it splits at any fixed date `τ` as
`U_d(θᵢ) = E[Σ_{t<τ} β^t r(y_t) | y₀ = θᵢ] + β^τ E[U_d(y_τ) | y₀ = θᵢ]`
(the identity behind the definition of `d_i(τ)` in §22.1.3, p. 780, for deterministic dates).
-/

namespace Miao.RecursiveContracts

open Filter Topology

variable {ι : Type*} [Fintype ι]

/-- The conditional expectation `(π f)(θᵢ) = Σⱼ π(θⱼ | θᵢ) f(θⱼ)` (Miao, p. 774). -/
def lc_condExp (pl : ι → ι → ℝ) (f : ι → ℝ) (i : ι) : ℝ := ∑ j, pl i j * f j

/-- `pl` is a transition matrix: nonnegative entries and rows summing to one (Miao, p. 774). -/
def lc_IsStochastic (pl : ι → ι → ℝ) : Prop := (∀ i j, 0 ≤ pl i j) ∧ ∀ i, ∑ j, pl i j = 1

/-- The autarky value `U_d(θᵢ) = Σ_t β^t E[r(y_t) | y₀ = θᵢ]` (Miao, p. 775), for a reward
`r = u ∘ θ`. -/
noncomputable def lc_autarky (β : ℝ) (pl : ι → ι → ℝ) (r : ι → ℝ) (i : ι) : ℝ :=
  ∑' t : ℕ, β ^ t * (lc_condExp pl)^[t] r i

/-- The conditional expectation is bounded by any bound on the function. -/
theorem lc_condExp_abs_le {pl : ι → ι → ℝ} (hpl : lc_IsStochastic pl) {f : ι → ℝ} {M : ℝ}
    (hf : ∀ j, |f j| ≤ M) (i : ι) : |lc_condExp pl f i| ≤ M := by
  unfold lc_condExp
  calc |∑ j, pl i j * f j| ≤ ∑ j, |pl i j * f j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, pl i j * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hpl.1 i j)]
        exact mul_le_mul_of_nonneg_left (hf j) (hpl.1 i j)
    _ = M := by rw [← Finset.sum_mul, hpl.2 i, one_mul]

/-- Iterated conditional expectations keep the bound. -/
theorem lc_condExp_iter_abs_le {pl : ι → ι → ℝ} (hpl : lc_IsStochastic pl) {f : ι → ℝ} {M : ℝ}
    (hf : ∀ j, |f j| ≤ M) (t : ℕ) (i : ι) : |(lc_condExp pl)^[t] f i| ≤ M := by
  induction t generalizing i with
  | zero => exact hf i
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact lc_condExp_abs_le hpl ih i

omit [Fintype ι] in
/-- A finite family of reals has a common bound. -/
theorem lc_exists_bound [Finite ι] (f : ι → ℝ) : ∃ M, ∀ j, |f j| ≤ M := by
  cases nonempty_fintype ι
  exact ⟨∑ j, |f j|, fun j => Finset.single_le_sum (f := fun j => |f j|)
    (fun k _ => abs_nonneg (f k)) (Finset.mem_univ j)⟩

/-- The autarky series converges (Miao, p. 775). -/
theorem lc_autarky_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (r : ι → ℝ) (i : ι) :
    Summable fun t : ℕ => β ^ t * (lc_condExp pl)^[t] r i := by
  obtain ⟨M, hM⟩ := lc_exists_bound r
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
  exact mul_le_mul_of_nonneg_right (lc_condExp_iter_abs_le hpl hM t i) (pow_nonneg hβ0 t)

/-- Miao, p. 775: the autarky value satisfies the recursion
`U_d(θᵢ) = u(θᵢ) + β Σⱼ π(θⱼ | θᵢ) U_d(θⱼ)`. -/
theorem lc_autarky_recursion {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (r : ι → ℝ) (i : ι) :
    lc_autarky β pl r i = r i + β * ∑ j, pl i j * lc_autarky β pl r j := by
  unfold lc_autarky
  rw [(lc_autarky_summable hβ0 hβ1 hpl r i).tsum_eq_zero_add]
  congr 1
  · simp
  · have hs := fun j => lc_autarky_summable hβ0 hβ1 hpl r j
    have h1 : ∀ t : ℕ, β ^ (t + 1) * (lc_condExp pl)^[t + 1] r i =
        β * ∑ j, pl i j * (β ^ t * (lc_condExp pl)^[t] r j) := by
      intro t
      rw [Function.iterate_succ_apply', lc_condExp, Finset.mul_sum, Finset.mul_sum, pow_succ]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [h1]
    rw [tsum_mul_left, Summable.tsum_finsetSum fun j _ => (hs j).mul_left (pl i j)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact tsum_mul_left

/-- Miao, p. 775: the autarky value is the unique solution of the recursion
`f = r + β π f` (finite states, `0 ≤ β < 1`). -/
theorem lc_autarky_unique {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (r f : ι → ℝ)
    (hf : ∀ i, f i = r i + β * ∑ j, pl i j * f j) : f = lc_autarky β pl r := by
  have hg := lc_autarky_recursion hβ0 hβ1 hpl r
  generalize lc_autarky β pl r = g at hg ⊢
  rcases isEmpty_or_nonempty ι with hι | hι
  · funext i; exact (IsEmpty.false i).elim
  obtain ⟨i0, hi0⟩ := Finite.exists_max fun i => |f i - g i|
  have hd : ∀ i, |f i - g i| ≤ β * |f i0 - g i0| := by
    intro i
    have : f i - g i = β * lc_condExp pl (fun j => f j - g j) i := by
      rw [hf i, hg i, lc_condExp]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [this, abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (lc_condExp_abs_le hpl hi0 i) hβ0
  have h0 : |f i0 - g i0| = 0 := by
    have := hd i0
    have hn := abs_nonneg (f i0 - g i0)
    nlinarith
  funext i
  have := hi0 i
  rw [h0] at this
  linarith [abs_nonneg (f i - g i), abs_eq_zero.mp (le_antisymm this (abs_nonneg _))]

/-- Iterated conditional expectations are linear. -/
theorem lc_condExp_iter_linear (pl : ι → ι → ℝ) (a : ℝ) (f g : ι → ℝ) (t : ℕ) (i : ι) :
    (lc_condExp pl)^[t] (fun j => f j + a * g j) i =
      (lc_condExp pl)^[t] f i + a * (lc_condExp pl)^[t] g i := by
  induction t generalizing f g i with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply]
    have : lc_condExp pl (fun j => f j + a * g j) =
        fun j => lc_condExp pl f j + a * lc_condExp pl g j := by
      funext j
      simp only [lc_condExp, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this, ih]

/-- Miao, p. 780 (for a deterministic date `τ`): the autarky value splits as
`U_d(θᵢ) = Σ_{t<τ} β^t E[u(y_t) | y₀ = θᵢ] + β^τ E[U_d(y_τ) | y₀ = θᵢ]`. -/
theorem lc_autarky_split {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (r : ι → ℝ) (τ : ℕ) (i : ι) :
    lc_autarky β pl r i = ∑ t ∈ Finset.range τ, β ^ t * (lc_condExp pl)^[t] r i +
      β ^ τ * (lc_condExp pl)^[τ] (lc_autarky β pl r) i := by
  induction τ generalizing i with
  | zero => simp
  | succ τ ih =>
    rw [ih, Finset.sum_range_succ]
    have hrec : lc_autarky β pl r = fun j => r j + β * lc_condExp pl (lc_autarky β pl r) j := by
      funext j; exact lc_autarky_recursion hβ0 hβ1 hpl r j
    have : (lc_condExp pl)^[τ] (lc_autarky β pl r) i =
        (lc_condExp pl)^[τ] r i + β * (lc_condExp pl)^[τ + 1] (lc_autarky β pl r) i := by
      conv_lhs => rw [hrec]
      rw [lc_condExp_iter_linear, Function.iterate_succ_apply]
    rw [this, pow_succ]
    ring

end Miao.RecursiveContracts

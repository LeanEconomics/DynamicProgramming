/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Objective
import MarkovDecisionProcesses.KernelTools
import Mathlib.Probability.Distributions.Exponential

/-!
# Discrete choice: Rust's replacement problem

Miao, §5.2.1, pp. 143–144. The state `s ≥ 0` is accumulated utilisation; the action `a = 0`
keeps the durable and `a = 1` replaces it. Utilisation grows by an exponential increment with
rate `λ`: `s_{t+1} = s_t + ε` after keeping, `s_{t+1} = ε` after replacing, `ε ~ Exp(λ)`
(`rustKernel`). The reward is `−c(s)` when keeping and `−(P_b − P_s) − c(0)` when replacing.

* `rust_cdf_keep`, `rust_cdf_replace`: the transition probabilities printed on p. 144,
  `P(s, 0; [s, x]) = 1 − exp(−λ(x − s))` and `P(s, 1; [0, x]) = 1 − exp(−λx)`.
  **Correction:** the book calls these the *densities* of the kernels; they are the
  distribution functions (the densities are `λ exp(−λ(x − s))` and `λ exp(−λx)`).
* `rust_nonneg`: the kernel keeps the state in `S = ℝ₊` (the model is set on `ℝ`, with
  `[0, ∞)` invariant; the book takes `S = ℝ₊`).
* `rust_assumptions`: with `c` measurable and bounded, the model satisfies Assumptions
  5.1.1, 5.1.2 (for `β ∈ (0, 1)`) and 5.1.4, and the kernels are stochastic kernels.
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory

/-- The state from which the next increment is added: `s` if kept, `0` if replaced. -/
def rustBase (x : ℝ × Fin 2) : ℝ := if x.2 = 0 then x.1 else 0

theorem measurable_rustBase : Measurable rustBase :=
  measurable_from_prod_countable_left fun a => by
    by_cases h : a = 0
    · simp only [rustBase, h, ↓reduceIte]
      exact measurable_id
    · simp only [rustBase, h, ↓reduceIte]
      exact measurable_const

theorem measurable_rustNext : Measurable fun p : (ℝ × Fin 2) × ℝ => rustBase p.1 + p.2 :=
  (measurable_rustBase.comp measurable_fst).add measurable_snd

/-- The kernel `P(s, a; ·)`: the law of `rustBase(s, a) + ε`, `ε ~ Exp(λ)`. -/
noncomputable def rustKernel (lam : ℝ) : Kernel (ℝ × Fin 2) ℝ :=
  pushKernel (Kernel.const _ (expMeasure lam)) fun p => rustBase p.1 + p.2

/-- Rust's replacement problem (Miao, §5.2.1). -/
noncomputable def rust (lam β Pb Ps : ℝ) (c : ℝ → ℝ) : MDP ℝ (Fin 2) where
  Γ := fun _ => Set.univ
  P := fun _ => rustKernel lam
  u := fun _ x => if x.2 = 0 then -c x.1 else -(Pb - Ps) - c 0
  uT := fun _ => 0
  β := β

theorem rustKernel_apply {lam : ℝ} (hl : 0 < lam) (x : ℝ × Fin 2) {B : Set ℝ}
    (hB : MeasurableSet B) :
    rustKernel lam x B = expMeasure lam ((fun e => rustBase x + e) ⁻¹' B) := by
  have := isProbabilityMeasure_expMeasure hl
  rw [rustKernel, pushKernel_apply _ measurable_rustNext, Kernel.const_apply]
  exact Measure.map_apply (f := fun e => rustBase x + e) (measurable_const_add _) hB

theorem expMeasure_Iic {lam : ℝ} (hl : 0 < lam) (y : ℝ) :
    expMeasure lam (Set.Iic y) =
      ENNReal.ofReal (if 0 ≤ y then 1 - Real.exp (-(lam * y)) else 0) := by
  have := isProbabilityMeasure_expMeasure hl
  rw [← ofReal_cdf, cdf_expMeasure_eq hl]

/-- Miao, p. 144 (corrected: a distribution function, not a density): after keeping,
`P(s, 0; (−∞, x]) = 1 − exp(−λ(x − s))` for `x ≥ s`, and `0` for `x < s`. -/
theorem rust_cdf_keep {lam : ℝ} (hl : 0 < lam) (s x : ℝ) :
    rustKernel lam (s, 0) (Set.Iic x) =
      ENNReal.ofReal (if s ≤ x then 1 - Real.exp (-(lam * (x - s))) else 0) := by
  rw [rustKernel_apply hl _ measurableSet_Iic]
  have : (fun e => rustBase (s, 0) + e) ⁻¹' Set.Iic x = Set.Iic (x - s) := by
    ext e
    simp only [rustBase, ↓reduceIte, Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  rw [this, expMeasure_Iic hl]
  simp only [sub_nonneg]

/-- Miao, p. 144 (corrected: a distribution function, not a density): after replacing,
`P(s, 1; (−∞, x]) = 1 − exp(−λx)` for `x ≥ 0`, and `0` for `x < 0`. -/
theorem rust_cdf_replace {lam : ℝ} (hl : 0 < lam) (s x : ℝ) :
    rustKernel lam (s, 1) (Set.Iic x) =
      ENNReal.ofReal (if 0 ≤ x then 1 - Real.exp (-(lam * x)) else 0) := by
  rw [rustKernel_apply hl _ measurableSet_Iic]
  have : (fun e => rustBase (s, 1) + e) ⁻¹' Set.Iic x = Set.Iic x := by
    ext e
    simp [rustBase]
  rw [this, expMeasure_Iic hl]

/-- The state space `ℝ₊` is invariant: from `s ≥ 0`, the next state is `≥ 0` almost surely. -/
theorem rust_nonneg {lam : ℝ} (hl : 0 < lam) {s : ℝ} (hs : 0 ≤ s) (a : Fin 2) :
    rustKernel lam (s, a) (Set.Iio 0) = 0 := by
  rw [rustKernel_apply hl _ measurableSet_Iio]
  have hb : 0 ≤ rustBase (s, a) := by
    unfold rustBase
    split_ifs
    · exact hs
    · exact le_rfl
  refine le_antisymm ?_ (zero_le)
  calc expMeasure lam ((fun e => rustBase (s, a) + e) ⁻¹' Set.Iio 0)
      ≤ expMeasure lam (Set.Iic 0) := measure_mono fun e he => by
        simp only [Set.mem_preimage, Set.mem_Iio] at he
        exact Set.mem_Iic.2 (by linarith)
    _ = 0 := by rw [expMeasure_Iic hl]; simp

/-- Miao, §5.2.1: Rust's model satisfies Assumptions 5.1.1, 5.1.2 and 5.1.4 when `c` is
measurable and bounded and `β ∈ (0, 1)`. -/
theorem rust_assumptions {lam β Pb Ps C : ℝ} {c : ℝ → ℝ} (hl : 0 < lam) (hc : Measurable c)
    (hC : ∀ s, |c s| ≤ C) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (rust lam β Pb Ps c).IsMarkov ∧ HasMeasurableSelection (rust lam β Pb Ps c).Γ ∧
      Assumption512 (rust lam β Pb Ps c) ∧ Assumption514 (rust lam β Pb Ps c) := by
  have hP : (rust lam β Pb Ps c).IsMarkov := fun _ => by
    have := isProbabilityMeasure_expMeasure hl
    exact isMarkovKernel_pushKernel _ measurable_rustNext
  refine ⟨hP, ⟨fun _ => 0, measurable_const, fun _ => Set.mem_univ _⟩, ⟨hβ0, hβ1⟩,
    assumption_5_1_4_of_bounded hP (fun _ => ⟨rfl, rfl⟩) (B := |Pb - Ps| + C) ?_ ?_ hβ0.le hβ1⟩
  · intro t x
    have h0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    simp only [rust]
    split_ifs
    · rw [abs_neg]
      linarith [hC x.1, abs_nonneg (Pb - Ps)]
    · calc |-(Pb - Ps) - c 0| ≤ |-(Pb - Ps)| + |c 0| := abs_sub _ _
        _ ≤ |Pb - Ps| + C := by rw [abs_neg]; linarith [hC 0]
  · intro t
    refine measurable_from_prod_countable_left fun a => ?_
    by_cases h : a = 0
    · simp only [rust, h, ↓reduceIte]
      exact hc.neg
    · simp only [rust, h, ↓reduceIte]
      exact measurable_const

end Miao.MarkovDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Partial derivatives and Euler's theorem (copied)

Copied from `EconomicDynamics/Applications` (module `IVQTheory`, Miao §8.6.2, pp. 278–280),
names `iv_*` renamed to `rx_*`, namespace renamed.

* `rx_HasPartials Ψ a b p`: `Ψ : ℝ × ℝ → ℝ` is differentiable at `p` with partial derivatives
  `Ψ₁(p) = a`, `Ψ₂(p) = b`; `rx_HasPartials.comp` is the chain rule along a path.
* `rx_euler_homog`: Euler's theorem `Ψ(I, K) = IΨ₁ + KΨ₂` for a linearly homogeneous `Ψ`.
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- `Ψ : ℝ × ℝ → ℝ` is differentiable at `p` with partial derivatives `Ψ₁(p) = a` and
`Ψ₂(p) = b`. -/
def rx_HasPartials (Ψ : ℝ × ℝ → ℝ) (a b : ℝ) (p : ℝ × ℝ) : Prop :=
  HasFDerivAt Ψ (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) p

/-- The derivative of `Ψ` along a differentiable path `k ↦ (x k, y k)`. -/
theorem rx_HasPartials.comp {Ψ : ℝ × ℝ → ℝ} {a b : ℝ} {x y : ℝ → ℝ} {x' y' k : ℝ}
    (hΨ : rx_HasPartials Ψ a b (x k, y k)) (hx : HasDerivAt x x' k) (hy : HasDerivAt y y' k) :
    HasDerivAt (fun s => Ψ (x s, y s)) (a * x' + b * y') k := by
  unfold rx_HasPartials at hΨ
  have := HasFDerivAt.comp_hasDerivAt (l := Ψ) (f := fun s => (x s, y s)) k hΨ
    (HasDerivAt.prodMk hx hy)
  simpa [Function.comp_def, smul_eq_mul] using this

/-- Miao, p. 280 (Euler's theorem for linearly homogeneous functions): if
`Ψ(λI, λK) = λΨ(I, K)` for all `λ > 0` and `Ψ` has partial derivatives `Ψ₁ = a`, `Ψ₂ = b` at
`(I, K)`, then `Ψ(I, K) = IΨ₁ + KΨ₂`. -/
theorem rx_euler_homog {Ψ : ℝ × ℝ → ℝ} {I K a b : ℝ}
    (hhom : ∀ l : ℝ, 0 < l → Ψ (l * I, l * K) = l * Ψ (I, K))
    (hd : rx_HasPartials Ψ a b (I, K)) : Ψ (I, K) = I * a + K * b := by
  have hd' : rx_HasPartials Ψ a b ((fun l : ℝ => l * I) 1, (fun l : ℝ => l * K) 1) := by
    simpa using hd
  have d1 : HasDerivAt (fun l : ℝ => Ψ (l * I, l * K)) (a * I + b * K) 1 := by
    have := hd'.comp ((hasDerivAt_id (1 : ℝ)).mul_const I) ((hasDerivAt_id (1 : ℝ)).mul_const K)
    simpa using this
  have d2 : HasDerivAt (fun l : ℝ => Ψ (l * I, l * K)) (Ψ (I, K)) 1 := by
    have h0 : HasDerivAt (fun l : ℝ => l * Ψ (I, K)) (1 * Ψ (I, K)) 1 :=
      (hasDerivAt_id (1 : ℝ)).mul_const _
    rw [one_mul] at h0
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with l hl
    exact hhom l hl
  have := d1.unique d2
  linarith

end Miao.NeoclassicalGrowth

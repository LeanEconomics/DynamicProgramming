/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.Principle

/-!
# Unbounded returns

SLP §4.4, pp. 92–93. The operator `(Tf)(x) = sup_{y ∈ Γ(x)} [F(x, y) + βf(y)]` acts on all
functions `X → R̄` (`opT`). Starting from an upper bound `v̂` of `v*` with `Tv̂ ≤ v̂`, the iterates
`Tⁿv̂` decrease to a limit `v` (`limitFn`); if that limit solves (FE) it is `v*`.

* `opT_mono`: `T` is monotone.
* `iterate_antitone`, `tendsto_iterate`: `Tⁿ⁺¹v̂ ≤ Tⁿv̂`, and `Tⁿv̂ → v`.
* `theorem_4_14`: under Assumptions 4.1–4.2, with (2) `limsup βⁿv̂(xₙ) ≤ 0` and
  (3) `u(x) ≤ v̂(x₀)` along feasible plans, a limit `v` that is a fixed point of `T` equals `v*`.
  Condition (1) `Tv̂ ≤ v̂` makes `v` the limit of the iterates.
-/

open Filter Topology

namespace StokeyLucasPrescott.DeterministicDP

variable {X : Type*} {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ}

/-- `(Tf)(x) = sup_{y ∈ Γ(x)} [F(x, y) + βf(y)]` on functions `X → R̄`. -/
noncomputable def opT (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (f : X → EReal) (x : X) : EReal :=
  ⨆ y ∈ Γ x, ((F x y : EReal) + (β : EReal) * f y)

theorem satisfiesFE_iff_opT {v : X → EReal} : SatisfiesFE Γ F β v ↔ opT Γ F β v = v :=
  ⟨fun h => funext fun x => (h x).symm, fun h x => (congrFun h x).symm⟩

/-- `T` is monotone. -/
theorem opT_mono (hβ : 0 ≤ β) {f g : X → EReal} (hfg : f ≤ g) : opT Γ F β f ≤ opT Γ F β g :=
  fun _ => iSup₂_mono fun y _ => add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (hfg y) (EReal.coe_nonneg.2 hβ))

/-- From `Tv̂ ≤ v̂` the iterates decrease. -/
theorem iterate_antitone (hβ : 0 ≤ β) {vhat : X → EReal} (h1 : opT Γ F β vhat ≤ vhat) :
    Antitone fun n => (opT Γ F β)^[n] vhat := by
  have key : ∀ n, opT Γ F β ((opT Γ F β)^[n] vhat) ≤ (opT Γ F β)^[n] vhat := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact opT_mono hβ ih
  refine antitone_nat_of_succ_le fun n => ?_
  rw [Function.iterate_succ_apply']
  exact key n

/-- `v(x) = lim (Tⁿv̂)(x)`, the infimum of the decreasing iterates. -/
noncomputable def limitFn (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (vhat : X → EReal) (x : X) :
    EReal :=
  ⨅ n : ℕ, (opT Γ F β)^[n] vhat x

theorem tendsto_iterate (hβ : 0 ≤ β) {vhat : X → EReal} (h1 : opT Γ F β vhat ≤ vhat) (x : X) :
    Tendsto (fun n => (opT Γ F β)^[n] vhat x) atTop (𝓝 (limitFn Γ F β vhat x)) :=
  tendsto_atTop_iInf fun _ _ hmn => iterate_antitone hβ h1 hmn x

/-- **Theorem 4.14.** Let Assumptions 4.1–4.2 hold with `β > 0`, and let `v̂ : X → R̄` satisfy
(2) `limsup βⁿv̂(xₙ) ≤ 0` and (3) `u(x) ≤ v̂(x₀)` along every feasible plan. If
`v = inf Tⁿv̂` is a fixed point of `T`, then `v = v*`. Under (1) `Tv̂ ≤ v̂`, `v` is the limit
`lim Tⁿv̂` (`tendsto_iterate`); (1) is used only for that. -/
theorem theorem_4_14 (hβ : 0 < β) (h41 : Assumption41 Γ) (h42 : Assumption42 Γ F β)
    {vhat : X → EReal}
    (h2 : ∀ x₀, ∀ x ∈ Feasible Γ x₀,
      limsup (fun n => ((β ^ n : ℝ) : EReal) * vhat (x n)) atTop ≤ 0)
    (h3 : ∀ x₀, ∀ x ∈ Feasible Γ x₀, total F β x ≤ vhat x₀)
    (hfix : opT Γ F β (limitFn Γ F β vhat) = limitFn Γ F β vhat) :
    limitFn Γ F β vhat = vstar Γ F β := by
  set v := limitFn Γ F β vhat
  have hvle : v ≤ vhat := fun x => iInf_le (fun n => (opT Γ F β)^[n] vhat x) 0
  -- `v ≤ v*` by Exercise 4.3a
  have hle : v ≤ vstar Γ F β := fun x₀ =>
    ex_4_3a hβ h42 (satisfiesFE_iff_opT.2 hfix) (fun x₀ x hx => (limsup_le_limsup
      (Eventually.of_forall fun n => mul_le_mul_of_nonneg_left (hvle (x n))
        (EReal.coe_nonneg.2 (pow_nonneg hβ.le n)))).trans (h2 x₀ x hx)) x₀
  -- `v* ≤ Tⁿv̂` for all `n`
  have hstar : ∀ n, vstar Γ F β ≤ (opT Γ F β)^[n] vhat := by
    intro n
    induction n with
    | zero => exact fun x₀ => iSup₂_le fun x hx => h3 x₀ x hx
    | succ n ih =>
      rw [Function.iterate_succ_apply', ← satisfiesFE_iff_opT.1 (theorem_4_2 hβ.le h41 h42)]
      exact opT_mono hβ.le ih
  exact le_antisymm hle fun x => le_iInf fun n => hstar n x

end StokeyLucasPrescott.DeterministicDP

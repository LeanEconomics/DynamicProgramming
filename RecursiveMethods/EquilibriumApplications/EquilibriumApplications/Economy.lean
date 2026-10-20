/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Economies, Pareto optima and competitive equilibria

SLP §15.2, pp. 452–455. The commodity space is a real normed space `S`. There are finitely many
consumers `i : ι`, with consumption sets `X i ⊆ S` and utility functions `u i : S → ℝ` (only their
values on `X i` matter), and finitely many firms `j : κ`, with production sets `Y j ⊆ S`.

* `Feasible`: `xᵢ ∈ Xᵢ`, `yⱼ ∈ Yⱼ` and `Σ xᵢ − Σ yⱼ = 0` (p. 452).
* `ParetoOptimal`: feasible, and no feasible allocation makes every consumer at least as well off
  and some consumer strictly better off (p. 452).
* `CompetitiveEq`: with a price system `φ ∈ S*`, (E1) feasibility, (E2) each `xᵢ` maximises `uᵢ`
  on the budget set `{x ∈ Xᵢ : φ x ≤ φ xᵢ}`, (E3) each `yⱼ` maximises profit `φ` on `Yⱼ`
  (pp. 452–453).
* `LocalNonsatiation`: the hypothesis of Theorem 15.3.
* `Assumption15_1` … `Assumption15_5` (p. 455).
* `aggTech`: the aggregate technology `Y = Σⱼ Yⱼ`.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] {ι κ : Type*} [Fintype ι]
  [Fintype κ]

/-- An allocation `[(xᵢ), (yⱼ)]` is **feasible** (p. 452). -/
def Feasible (X : ι → Set S) (Y : κ → Set S) (x : ι → S) (y : κ → S) : Prop :=
  (∀ i, x i ∈ X i) ∧ (∀ j, y j ∈ Y j) ∧ ∑ i, x i - ∑ j, y j = 0

/-- A feasible allocation is **Pareto optimal** (p. 452). -/
def ParetoOptimal (X : ι → Set S) (u : ι → S → ℝ) (Y : κ → Set S) (x : ι → S) (y : κ → S) :
    Prop :=
  Feasible X Y x y ∧ ¬ ∃ x' y', Feasible X Y x' y' ∧ (∀ i, u i (x i) ≤ u i (x' i)) ∧
    ∃ i, u i (x i) < u i (x' i)

/-- `[(xᵢ), (yⱼ), φ]` is a **competitive equilibrium** (pp. 452–453): (E1)–(E3). -/
def CompetitiveEq (X : ι → Set S) (u : ι → S → ℝ) (Y : κ → Set S) (x : ι → S) (y : κ → S)
    (φ : StrongDual ℝ S) : Prop :=
  Feasible X Y x y ∧ (∀ i, ∀ z ∈ X i, φ z ≤ φ (x i) → u i z ≤ u i (x i)) ∧
    ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y j)

/-- **Local nonsatiation** (Theorem 15.3): every `x ∈ Xᵢ` is a limit of strictly preferred
points of `Xᵢ`. -/
def LocalNonsatiation (X : ι → Set S) (u : ι → S → ℝ) : Prop :=
  ∀ i, ∀ z ∈ X i, ∃ zs : ℕ → S, (∀ n, zs n ∈ X i) ∧ Tendsto zs atTop (𝓝 z) ∧
    ∀ n, u i z < u i (zs n)

/-- The aggregate technology `Y = Σⱼ Yⱼ` (p. 452). -/
def aggTech (Y : κ → Set S) : Set S :=
  {w | ∃ y : κ → S, (∀ j, y j ∈ Y j) ∧ w = ∑ j, y j}

/-- **Assumption 15.1**: each `Xᵢ` is convex. -/
def Assumption15_1 (X : ι → Set S) : Prop := ∀ i, Convex ℝ (X i)

/-- **Assumption 15.2**: if `uᵢ(x) > uᵢ(x′)` and `0 < θ < 1` then
`uᵢ(θx + (1 − θ)x′) > uᵢ(x′)`. -/
def Assumption15_2 (X : ι → Set S) (u : ι → S → ℝ) : Prop :=
  ∀ i, ∀ z ∈ X i, ∀ z' ∈ X i, u i z' < u i z → ∀ θ : ℝ, 0 < θ → θ < 1 →
    u i z' < u i (θ • z + (1 - θ) • z')

/-- **Assumption 15.3**: each `uᵢ` is continuous (on `Xᵢ`). -/
def Assumption15_3 (X : ι → Set S) (u : ι → S → ℝ) : Prop := ∀ i, ContinuousOn (u i) (X i)

/-- **Assumption 15.4**: the aggregate technology is convex. -/
def Assumption15_4 (Y : κ → Set S) : Prop := Convex ℝ (aggTech Y)

/-- **Assumption 15.5**: the aggregate technology has an interior point, or `S` is finite
dimensional. -/
def Assumption15_5 (S : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S] {κ : Type*} [Fintype κ]
    (Y : κ → Set S) : Prop :=
  (interior (aggTech Y)).Nonempty ∨ FiniteDimensional ℝ S

end StokeyLucasPrescott.EquilibriumApplications

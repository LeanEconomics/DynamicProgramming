/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.CUDExistence
import MarkovDriving.ChentsovGeneral
import MarkovDriving.OccupationPoisson

/-! # Chentsov's theorem for irreducible chains (post #3)

Post #3: "if the QMC method we use is 'completely uniformly distributed' … then the generated
Markov simulations are consistent for the empirical state frequencies and time averages
(Chentsov, 1967)". In the post's terms, for an **irreducible** chain (`∀ i j, ∃ k, Pᵏ(i,j) > 0`,
periodic chains allowed) the stationary distribution `π` is unique (`OccupationPoisson`), so
`ChentsovGeneral` applies.

**Results.**
* `stationary_unique_of_irreducible`: every stationary probability vector of an irreducible `P`
  is `π` (the uniqueness hypothesis of `ChentsovGeneral`).
* `tendsto_occFreq_of_isCUD_irreducible`: `N_j(T)/T → π_j` for every start and every CUD `u`.
* `tendsto_timeAvg_of_isCUD_irreducible`: `(1/T) ∑_{t<T} g(x_t) → ∑_j π_j g(j)`.
* `ae_tendsto_occFreq_iidUniform_irreducible`: since i.i.d. uniform sequences are CUD almost
  surely (`ae_isCUD_iidUniform`), the same holds for almost every MC driving sequence — the
  theorem is not vacuous, and it contains the MC ergodic theorem for the inverse-CDF chain.
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology Finset

variable {n : ℕ}

/-- For an irreducible stochastic matrix, every stationary probability vector (in sum form) is
the stationary distribution `π`. -/
theorem stationary_unique_of_irreducible {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsStochastic P)
    (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {π : Fin n → ℝ} (hπ : IsStationaryDistribution P π)
    (x₀ : Fin n) (ρ : Fin n → ℝ) (hρ : ∀ j, ∑ i, ρ i * P i j = ρ j) (_hρ0 : ∀ i, 0 ≤ ρ i)
    (hρ1 : ∑ i, ρ i = 1) : ρ = π := by
  have : Nonempty (Fin n) := ⟨x₀⟩
  exact hπ.eq_of_vecMul_eq_self hP.nonneg hP.sum_eq_one hirr (funext hρ) hρ1

/-- **Chentsov's theorem for irreducible chains** (post #3). For an irreducible stochastic
matrix `P` (periodic allowed) with stationary distribution `π` and any CUD sequence `u`, the
path driven by `u` through the inverse-CDF update has `N_j(T)/T → π_j`, from every start. -/
theorem tendsto_occFreq_of_isCUD_irreducible {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsStochastic P) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {π : Fin n → ℝ}
    (hπ : IsStationaryDistribution P π) {u : ℕ → ℝ} (hu : IsCUD u) (x₀ j : Fin n) :
    Tendsto (fun T => (occCount (drivenPath P x₀ u) j T : ℝ) / T) atTop (𝓝 (π j)) :=
  tendsto_occFreq_of_isCUD_general hP hu (stationary_unique_of_irreducible hP hirr hπ x₀) x₀ j

/-- **Time averages for irreducible chains** (post #3): `(1/T) ∑_{t<T} g(x_t) → ∑_j π_j g(j)`. -/
theorem tendsto_timeAvg_of_isCUD_irreducible {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsStochastic P) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {π : Fin n → ℝ}
    (hπ : IsStationaryDistribution P π) {u : ℕ → ℝ} (hu : IsCUD u) (x₀ : Fin n)
    (g : Fin n → ℝ) :
    Tendsto (fun T => (∑ t ∈ range T, g (drivenPath P x₀ u t)) / T) atTop
      (𝓝 (∑ j, π j * g j)) :=
  tendsto_timeAvg_of_isCUD_general hP hu (stationary_unique_of_irreducible hP hirr hπ x₀) x₀ g

/-- **Not vacuous:** for almost every i.i.d. `U[0,1)` driving sequence (which is CUD a.s.), the
occupation frequencies of an irreducible chain converge to `π`, for every start and state. -/
theorem ae_tendsto_occFreq_iidUniform_irreducible {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsStochastic P) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {π : Fin n → ℝ}
    (hπ : IsStationaryDistribution P π) :
    ∀ᵐ u ∂(iidUniform ℕ), ∀ x₀ j : Fin n,
      Tendsto (fun T => (occCount (drivenPath P x₀ u) j T : ℝ) / T) atTop (𝓝 (π j)) := by
  filter_upwards [ae_isCUD_iidUniform] with u hu x₀ j
  exact tendsto_occFreq_of_isCUD_irreducible hP hirr hπ hu x₀ j

end RQMCMarkov.MarkovDriving

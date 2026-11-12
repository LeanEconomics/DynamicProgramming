/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SmallOpenEconomyDynamics.StochasticConsumption

/-!
# The linearised bond economy has a unit root

AKMM, §23.3.3, pp. 714–715.

The linearised UIP condition says `Eₜ[Ŵ_{t+1}] = Ŵ_t` (see `bond_wealth_loglin`). The book: "in
the linearized version of the bond economy, relative wealth is non-stationary … due to the fact
that the model is linearized around a non-stochastic steady state in which … `βR = 1`". This is
Hall's random walk: a linear Euler equation `u′(Ŵ_t) = (1 + r)βEₜ u′(Ŵ_{t+1})` with linear
marginal utility `u′(x) = 1 − x` and `(1 + r)β = 1`. Using Obstfeld–Rogoff's Hall theorems
(`hall_martingale`, `hall_condExp_future`) in the measure-theoretic setting of a filtration, we
prove that the relative wealth gap is a martingale (`unitroot_martingale`), that every forecast
equals the current gap, `Eₜ[Ŵ_s] = Ŵ_t` for all `s ≥ t` — shocks are permanent, there is no mean
reversion (`unitroot_forecast`) — and that the gap is a unit-root process `Ŵ_{t+1} = Ŵ_t + ε_{t+1}`
with `Eₜ[ε_{t+1}] = 0` (`unitroot_innovation`). In contrast, with a debt-elastic (Uzawa) factor
`ρ ∈ (−1, 1)` the forecasts `ρᵏŴ_t` revert to zero (`unitroot_uzawa_contrast`).
-/

namespace AKMM.InternationalMacro

open MeasureTheory Filter Topology
open ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption (quadMU hall_martingale
  hall_condExp_future)

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The linearised UIP condition `Eₜ[Ŵ_{t+1}] = Ŵ_t` is Hall's Euler equation for the linear
marginal utility `1 − Ŵ` with `(1 + r)β = 1`. -/
theorem unitroot_hall_form [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {W : ℕ → Ω → ℝ}
    {r β : ℝ} (hrβ : (1 + r) * β = 1) (hWi : ∀ t, Integrable (W t) μ)
    (h18 : ∀ t, μ[W (t + 1) | ℱ t] =ᵐ[μ] W t) (t : ℕ) :
    μ[fun ω => quadMU 1 (W (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => quadMU 1 (W t ω) / ((1 + r) * β) := by
  have h1 : (fun ω => quadMU 1 (W (t + 1) ω)) = (fun _ => (1 : ℝ)) - W (t + 1) := by
    funext ω; simp [quadMU]
  rw [h1, hrβ]
  filter_upwards [condExp_sub (integrable_const (1 : ℝ)) (hWi (t + 1)) (ℱ t), h18 t]
    with ω h2 h3
  rw [h2, Pi.sub_apply, condExp_const (ℱ.le t), h3]
  simp [quadMU]

/-- AKMM, p. 714: under the linearised UIP condition `Eₜ[Ŵ_{t+1}] = Ŵ_t` (and `βR = 1` at the
steady state), the relative wealth gap is a martingale. -/
theorem unitroot_martingale [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {W : ℕ → Ω → ℝ}
    {β : ℝ} (hβ : 0 < β) (hW : StronglyAdapted ℱ W) (hWi : ∀ t, Integrable (W t) μ)
    (h18 : ∀ t, μ[W (t + 1) | ℱ t] =ᵐ[μ] W t) : Martingale W ℱ μ := by
  have hrβ : (1 + (1 / β - 1)) * β = 1 := by field_simp; ring
  exact hall_martingale ℱ one_ne_zero hrβ hW hWi (unitroot_hall_form ℱ hrβ hWi h18)

/-- AKMM, p. 714: "relative wealth is non-stationary: the economy does not converge back to the
symmetric steady state": every forecast of the wealth gap equals its current value,
`Eₜ[Ŵ_s] = Ŵ_t` for all `s ≥ t`. -/
theorem unitroot_forecast [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {W : ℕ → Ω → ℝ}
    {β : ℝ} (hβ : 0 < β) (hW : StronglyAdapted ℱ W) (hWi : ∀ t, Integrable (W t) μ)
    (h18 : ∀ t, μ[W (t + 1) | ℱ t] =ᵐ[μ] W t) {t s : ℕ} (hts : t ≤ s) :
    μ[W s | ℱ t] =ᵐ[μ] W t := by
  have hrβ : (1 + (1 / β - 1)) * β = 1 := by field_simp; ring
  exact hall_condExp_future ℱ one_ne_zero hrβ hW hWi (unitroot_hall_form ℱ hrβ hWi h18) hts

/-- AKMM, pp. 714–715: the classic unit-root form `Ŵ_{t+1} = Ŵ_t + ε_{t+1}` with
`Eₜ[ε_{t+1}] = 0`. -/
theorem unitroot_innovation [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {W : ℕ → Ω → ℝ}
    (hW : StronglyAdapted ℱ W) (hWi : ∀ t, Integrable (W t) μ)
    (h18 : ∀ t, μ[W (t + 1) | ℱ t] =ᵐ[μ] W t) (t : ℕ) :
    μ[W (t + 1) - W t | ℱ t] =ᵐ[μ] 0 := by
  have hCt : μ[W t | ℱ t] = W t := condExp_of_stronglyMeasurable (ℱ.le t) (hW t) (hWi t)
  filter_upwards [condExp_sub (hWi (t + 1)) (hWi t) (ℱ t), h18 t] with ω h1 h2
  rw [h1, Pi.sub_apply, h2, hCt, sub_self]
  rfl

/-- AKMM, p. 715: the contrast with debt-elastic (Uzawa) discounting, which restores
stationarity: if forecasts evolve as `e_{k+1} = ρ e_k` with `|ρ| < 1`, they revert to zero,
`e_k = ρᵏ e_0 → 0`; with the unit root `ρ = 1` they stay at `e_0`. -/
theorem unitroot_uzawa_contrast {ρ : ℝ} (e : ℕ → ℝ) (he : ∀ k, e (k + 1) = ρ * e k) :
    (∀ k, e k = ρ ^ k * e 0) ∧ (|ρ| < 1 → Tendsto e atTop (𝓝 0)) ∧ (ρ = 1 → ∀ k, e k = e 0) := by
  have hk : ∀ k, e k = ρ ^ k * e 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [he, ih, pow_succ]; ring
  refine ⟨hk, fun hρ => ?_, fun h1 k => by rw [hk, h1, one_pow, one_mul]⟩
  have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hρ).mul_const (e 0)
  rw [zero_mul] at this
  exact this.congr fun k => (hk k).symm

end AKMM.InternationalMacro

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdaptiveLearning.LyapunovSA
import Mathlib.Analysis.PSeries

/-!
# Learning in the cobweb model

Muth (1961), Bray and Savin (1986), Evans and Honkapohja (2001, Ch. 2).

The reduced form of a market whose supply depends on the expected price is
`p_t = μ + βp^e_t + η_t`. The rational expectations equilibrium (REE) forecast is
`p̄ = μ/(1 − β)`. Agents who do not know `μ` and `β` forecast with the sample mean of past prices,
recursively `a_{t+1} = a_t + γ_t(p_t − a_t)` with `p^e_t = a_t` (steady-state learning). With the
decreasing gain `γ_t = 1/(t + 1)` this is least squares on a constant.

* `cobweb_learning`: if `β < 1` (E-stability), the forecasts `a_t → p̄` almost surely, for any
  step sizes with `∑ γ_t = ∞`, `∑ γ_t² < ∞`. The map `a ↦ μ + βa` need not be a contraction: for
  `β < −1` it expands distances, and learning still converges.
* `learning_eq`, `learning_diverges`: without noise, the forecast error is multiplied by
  `1 + γ_t(β − 1)` each period, so for `β > 1` (E-instability) learning moves away from the REE
  from any other start.
* `harmonic_gain`, `recursive_mean`: the gain `1/(t + 1)` satisfies the Robbins–Monro conditions,
  and with it `a_{t+1}` is the sample mean of `p_0, …, p_t`.
* `naive_eq`, `naive_diverges`: under naive expectations `p^e_t = p_{t−1}` the deviation from the
  REE is `β^t(p_0 − p̄)`, which explodes for `|β| > 1`.
* `cobweb_market`: from primitives — demand `q = A − b p`, supply `q = s₀ + s p^e + ε`, with
  `b, s > 0` — the reduced form has `β = −s/b < 0`, so least-squares learning always converges to
  the REE, while naive expectations diverge whenever `s > b` (the cobweb theorem).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace DPExtensions.AdaptiveLearning

/-! ### Deterministic dynamics -/

/-- Naive expectations: `p_{t+1} = μ + βp_t` gives `p_t − p̄ = β^t(p_0 − p̄)`. -/
theorem naive_eq {μ β : ℝ} (hβ : β ≠ 1) {p : ℕ → ℝ} (hrec : ∀ t, p (t + 1) = μ + β * p t)
    (t : ℕ) : p t - μ / (1 - β) = β ^ t * (p 0 - μ / (1 - β)) := by
  have h1 : (1 - β) ≠ 0 := sub_ne_zero.2 (Ne.symm hβ)
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hrec, pow_succ]
    have e : μ + β * p t - μ / (1 - β) = β * (p t - μ / (1 - β)) := by
      field_simp
      ring
    rw [e, ih]
    ring

/-- Under naive expectations the cobweb explodes when `|β| > 1`, from any start other than the
REE. -/
theorem naive_diverges {μ β : ℝ} (hβ : 1 < |β|) {p : ℕ → ℝ}
    (hrec : ∀ t, p (t + 1) = μ + β * p t) (hp0 : p 0 ≠ μ / (1 - β)) :
    Tendsto (fun t => |p t - μ / (1 - β)|) atTop atTop := by
  have hβ1 : β ≠ 1 := fun h => by rw [h, abs_one] at hβ; exact lt_irrefl _ hβ
  have e : (fun t => |p t - μ / (1 - β)|) = fun t => |β| ^ t * |p 0 - μ / (1 - β)| :=
    funext fun t => by rw [naive_eq hβ1 hrec, abs_mul, abs_pow]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hβ).atTop_mul_const
    (abs_pos.2 (sub_ne_zero.2 hp0))

/-- Without noise, steady-state learning multiplies the forecast error by `1 + γ_t(β − 1)`. -/
theorem learning_eq {μ β : ℝ} (hβ : β ≠ 1) {γ a : ℕ → ℝ}
    (hrec : ∀ t, a (t + 1) = a t + γ t * (μ + β * a t - a t)) (t : ℕ) :
    a t - μ / (1 - β) = (∏ s ∈ Finset.range t, (1 + γ s * (β - 1))) * (a 0 - μ / (1 - β)) := by
  have h1 : (1 - β) ≠ 0 := sub_ne_zero.2 (Ne.symm hβ)
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hrec, Finset.prod_range_succ]
    have e : a t + γ t * (μ + β * a t - a t) - μ / (1 - β) =
        (1 + γ t * (β - 1)) * (a t - μ / (1 - β)) := by
      field_simp
      ring
    rw [e, ih]
    ring

/-- `∏ (1 + x_s) ≥ 1 + ∑ x_s` for `x_s ≥ 0`. -/
theorem one_add_sum_le_prod {x : ℕ → ℝ} (hx : ∀ s, 0 ≤ x s) (t : ℕ) :
    1 + ∑ s ∈ Finset.range t, x s ≤ ∏ s ∈ Finset.range t, (1 + x s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have h0 : 0 ≤ ∑ s ∈ Finset.range t, x s := Finset.sum_nonneg fun s _ => hx s
    nlinarith [hx t]

/-- **E-instability**: for `β > 1` and `∑ γ_t = ∞`, noiseless learning moves away from the REE
from any other start: `|a_t − p̄| → ∞`. -/
theorem learning_diverges {μ β : ℝ} (hβ : 1 < β) {γ a : ℕ → ℝ} (hγ0 : ∀ t, 0 ≤ γ t)
    (hdiv : ¬ Summable γ) (hrec : ∀ t, a (t + 1) = a t + γ t * (μ + β * a t - a t))
    (ha0 : a 0 ≠ μ / (1 - β)) :
    Tendsto (fun t => |a t - μ / (1 - β)|) atTop atTop := by
  have hβ1 : β ≠ 1 := ne_of_gt hβ
  have hx : ∀ s, 0 ≤ γ s * (β - 1) := fun s => mul_nonneg (hγ0 s) (by linarith)
  have hS : Tendsto (fun t => ∑ s ∈ Finset.range t, γ s * (β - 1)) atTop atTop := by
    have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hγ0).1 hdiv
    have e : (fun t => ∑ s ∈ Finset.range t, γ s * (β - 1)) =
        fun t => (∑ s ∈ Finset.range t, γ s) * (β - 1) :=
      funext fun t => (Finset.sum_mul _ _ _).symm
    rw [e]
    exact h.atTop_mul_const (by linarith)
  have hprod : Tendsto (fun t => ∏ s ∈ Finset.range t, (1 + γ s * (β - 1))) atTop atTop :=
    tendsto_atTop_mono (fun t => (one_add_sum_le_prod hx t).trans' (by linarith))
      (tendsto_atTop_add_const_left _ 1 hS)
  have e : (fun t => |a t - μ / (1 - β)|) =
      fun t => (∏ s ∈ Finset.range t, (1 + γ s * (β - 1))) * |a 0 - μ / (1 - β)| := by
    funext t
    rw [learning_eq hβ1 hrec, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun s _ => by
      linarith [hx s])]
  rw [e]
  exact hprod.atTop_mul_const (abs_pos.2 (sub_ne_zero.2 ha0))

/-- The least-squares gain `γ_t = 1/(t + 1)` satisfies the Robbins–Monro conditions. -/
theorem harmonic_gain : (∀ t : ℕ, 0 ≤ 1 / ((t : ℝ) + 1)) ∧
    (¬ Summable fun t : ℕ => 1 / ((t : ℝ) + 1)) ∧
    Summable fun t : ℕ => (1 / ((t : ℝ) + 1)) ^ 2 := by
  refine ⟨fun t => by positivity, fun hs => ?_, ?_⟩
  · exact not_tendsto_atTop_of_tendsto_nhds hs.hasSum.tendsto_sum_nat
      Real.tendsto_sum_range_one_div_nat_succ_atTop
  · have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    refine h.congr fun t => ?_
    push_cast
    rw [div_pow, one_pow]

/-- With the gain `1/(t + 1)`, steady-state learning is least squares on a constant: the forecast
`a_{t+1}` is the sample mean of `p_0, …, p_t`. -/
theorem recursive_mean {a p : ℕ → ℝ}
    (hrec : ∀ t, a (t + 1) = a t + 1 / ((t : ℝ) + 1) * (p t - a t)) (t : ℕ) :
    a (t + 1) = (∑ s ∈ Finset.range (t + 1), p s) / ((t : ℝ) + 1) := by
  induction t with
  | zero => rw [hrec]; simp
  | succ t ih =>
    rw [hrec, ih, Finset.sum_range_succ _ (t + 1)]
    push_cast
    field_simp
    ring

/-! ### Stochastic learning -/

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℕ m0}

/-- **Learnability of the cobweb REE** (Bray and Savin, 1986; Evans and Honkapohja, 2001):
with `p_t = μ + βa_t + η_t`, `a_{t+1} = a_t + γ_t(p_t − a_t)`, `β < 1`, noise `η_t` that is
`ℱ_{t+1}`-measurable, square integrable, with `𝔼[η_t | ℱ_t] = 0` and `𝔼[η_t² | ℱ_t] ≤ σ²`, and
`γ_t ≥ 0` with `∑ γ_t = ∞`, `∑ γ_t² < ∞`, the forecasts converge to `μ/(1 − β)` almost
surely. -/
theorem cobweb_learning {μ β : ℝ} (hβ : β < 1) {γ : ℕ → ℝ} (hγ0 : ∀ t, 0 ≤ γ t)
    (hdiv : ¬ Summable γ) (hsq : Summable fun t => γ t ^ 2) {a p η : ℕ → Ω → ℝ}
    (hp : ∀ t ω, p t ω = μ + β * a t ω + η t ω)
    (hrec : ∀ t ω, a (t + 1) ω = a t ω + γ t * (p t ω - a t ω))
    (ha0m : StronglyMeasurable[ℱ 0] (a 0)) (ha0 : MemLp (a 0) 2 P)
    (hηm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (η t)) (hη2 : ∀ t, MemLp (η t) 2 P)
    (hη0 : ∀ t, P[η t | ℱ t] =ᵐ[P] 0) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    (hησ : ∀ t, P[fun ω => η t ω ^ 2 | ℱ t] ≤ᵐ[P] fun _ => σ2) :
    ∀ᵐ ω ∂P, Tendsto (fun t => a t ω) atTop (𝓝 (μ / (1 - β))) := by
  have h1 : (1 - β) ≠ 0 := by linarith
  have hh : ∀ x : ℝ, μ + β * x - x = (β - 1) * (x - μ / (1 - β)) := fun x => by
    field_simp
    ring
  refine sa_lyapunov (ℱ := ℱ) (h := fun x : ℝ => μ + β * x - x) (by fun_prop)
    (Q := ContinuousLinearMap.id ℝ ℝ) (fun x y => rfl) (m := 1) (κ := 1 - β)
    (L := |β - 1|) one_pos (by linarith) (fun x => ?_) (fun x => ?_) (fun x => ?_) hγ0 hdiv hsq
    (W := η) (fun t ω => ?_) ha0m ha0 hηm hη2 hη0 hσ (fun t => ?_)
  · simp
  · simp only [ContinuousLinearMap.id_apply, hh x, Real.norm_eq_abs]
    have : inner ℝ (x - μ / (1 - β)) ((β - 1) * (x - μ / (1 - β))) =
        (β - 1) * (x - μ / (1 - β)) ^ 2 := by
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    rw [this, sq_abs]
    linarith
  · rw [hh x, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  · rw [hrec, hp, smul_eq_mul]
    ring
  · filter_upwards [hησ t] with ω hω
    have e : (fun ω => ‖η t ω‖ ^ 2) = fun ω => η t ω ^ 2 :=
      funext fun ω => by rw [Real.norm_eq_abs, sq_abs]
    rw [e]
    refine hω.trans ?_
    nlinarith [sq_nonneg ‖a t ω‖]

/-- **The cobweb model from primitives.** Demand `q = A − b p` and supply
`q = s₀ + s a_t + ε_t` (`b, s > 0`), with market clearing, give `p_t = μ + βa_t + η_t` with
`β = −s/b < 0`. So least-squares learning converges to the REE almost surely, while naive
expectations diverge when `s > b`. -/
theorem cobweb_market {A s₀ b s : ℝ} (hb : 0 < b) (hs : 0 < s) {γ : ℕ → ℝ}
    (hγ0 : ∀ t, 0 ≤ γ t) (hdiv : ¬ Summable γ) (hsq : Summable fun t => γ t ^ 2)
    {a p ε : ℕ → Ω → ℝ} (hclear : ∀ t ω, A - b * p t ω = s₀ + s * a t ω + ε t ω)
    (hrec : ∀ t ω, a (t + 1) ω = a t ω + γ t * (p t ω - a t ω))
    (ha0m : StronglyMeasurable[ℱ 0] (a 0)) (ha0 : MemLp (a 0) 2 P)
    (hεm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (ε t)) (hε2 : ∀ t, MemLp (ε t) 2 P)
    (hε0 : ∀ t, P[ε t | ℱ t] =ᵐ[P] 0) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    (hεσ : ∀ t, P[fun ω => ε t ω ^ 2 | ℱ t] ≤ᵐ[P] fun _ => σ2) :
    (∀ᵐ ω ∂P, Tendsto (fun t => a t ω) atTop (𝓝 ((A - s₀) / b / (1 - -(s / b))))) ∧
      (b < s → ∀ q : ℕ → ℝ, (∀ t, q (t + 1) = (A - s₀) / b + -(s / b) * q t) →
        q 0 ≠ (A - s₀) / b / (1 - -(s / b)) →
        Tendsto (fun t => |q t - (A - s₀) / b / (1 - -(s / b))|) atTop atTop) := by
  have hb0 : b ≠ 0 := hb.ne'
  refine ⟨?_, fun hbs q hq hq0 => naive_diverges ?_ hq hq0⟩
  · refine cobweb_learning (β := -(s / b)) (by have := div_pos hs hb; linarith) hγ0 hdiv hsq
      (η := fun t ω => -b⁻¹ * ε t ω) (fun t ω => ?_) hrec ha0m ha0
      (fun t => stronglyMeasurable_const.mul (hεm t)) (fun t => (hε2 t).const_mul _)
      (fun t => ?_) (σ2 := b⁻¹ ^ 2 * σ2) (by positivity) (fun t => ?_)
    · field_simp
      linarith [hclear t ω]
    · have e : (fun ω => -b⁻¹ * ε t ω) = (-b⁻¹) • ε t := rfl
      rw [e]
      filter_upwards [condExp_smul (μ := P) (-b⁻¹) (ε t) (ℱ t), hε0 t] with ω h1 h2
      rw [h1, Pi.smul_apply, h2, Pi.zero_apply, smul_zero]
    · have e : (fun ω => (-b⁻¹ * ε t ω) ^ 2) = (b⁻¹ ^ 2) • fun ω => ε t ω ^ 2 := by
        funext ω
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      filter_upwards [condExp_smul (μ := P) (b⁻¹ ^ 2) (fun ω => ε t ω ^ 2) (ℱ t), hεσ t]
        with ω h1 h2
      rw [h1, Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  · rw [abs_neg, abs_div, abs_of_pos hs, abs_of_pos hb, one_lt_div hb]
    exact hbs

end DPExtensions.AdaptiveLearning

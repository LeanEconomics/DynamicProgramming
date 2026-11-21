/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.ScalarRE

/-!
# Exercise 1: the stochastic Cagan model

Miao, §2.6, Exercise 1, p. 82: `m_t − p_t = −αE_t(p_{t+1} − p_t)`, `α > 0`,
`m_{t+1} = ρm_t + ε_{t+1}`, `ρ ∈ [0, 1]`, `m₀` given. Setting: a `CondExpSystem ℝ V`
(`ScalarRE`).

* For adapted `p` the model is `E_tp_{t+1} = ((1 + α)/α)p_t − α^{−1}m_t` (`ex_1_iff`), a
  first-order equation with `b = (1 + α)/α > 1` (`ex_1_b_gt_one`).
* Condition and uniqueness: for every `α > 0` and every stable adapted `m` there is exactly one
  stable adapted solution, the forward solution `p_t = α^{−1}∑ⱼ b^{−j−1}E_tm_{t+j}`
  (`ex_1_unique`).
* The solution: if `E_tε_{t+1} = 0`, then `E_tm_{t+j} = ρʲm_t` and
  `p_t = m_t/(1 + α(1 − ρ))` (`ex_1_solution`); it is the forward solution for every
  `ρ ∈ [0, 1]` (`ex_1_solution_eq_fwd`), and for `ρ ∈ [0, 1)` with `ε` stable, `m` is stable
  and this is the unique stable solution (`ex_1`).
* What the shock must satisfy: the book takes `ε` a white noise; the formula solves the model iff
  `E_tε_{t+1} = 0` for all `t` (`ex_1_solution_iff`), which a white noise need not satisfy
  (`whiteNoise_not_mds` in `VARMoments`).
* `ρ = 1`: `m` is a martingale (`ex_1_rho_one_martingale`) whose norm grows at most linearly
  (`ex_1_rho_one_growth`); `p = m` solves the model and is the unique adapted solution satisfying
  the transversality condition (2.5) (`ex_1_rho_one`), whether or not `m` is stable; it is stable
  exactly when `m` is. (That a random walk with stable white-noise increments is not stable in
  `L¹`, e.g. `E|m_t| ~ √(2t/π)` for ±1 steps, is not formalised.)
-/

namespace Miao.RationalExpectations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exercise 1 (Miao, p. 82): the Cagan model `m_t − p_t = −αE_t(p_{t+1} − p_t)`. -/
def ex1_IsSol (E : CondExpSystem ℝ V) (α : ℝ) (m p : ℕ → V) : Prop :=
  ∀ t, m t - p t = -α • E.E t (p (t + 1) - p t)

/-- **Exercise 1** (Miao, p. 82): for adapted `p` and `α ≠ 0`, the Cagan model is
`E_tp_{t+1} = ((1 + α)/α)p_t − α^{−1}m_t`. -/
theorem ex_1_iff (E : CondExpSystem ℝ V) {α : ℝ} (hα : α ≠ 0) {m p : ℕ → V}
    (hp : sre_IsAdapted E p) :
    ex1_IsSol E α m p ↔ ∀ t, E.E t (p (t + 1)) = ((1 + α) / α) • p t + (-α⁻¹ • m) t := by
  refine forall_congr' fun t => ?_
  rw [map_sub, hp t, Pi.smul_apply]
  constructor
  · intro h
    have h2 : E.E t (p (t + 1)) = α⁻¹ • (α • E.E t (p (t + 1))) := by
      rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
    rw [h2]
    have h3 : α • E.E t (p (t + 1)) = α • p t + p t - m t := by
      rw [smul_sub] at h
      linear_combination (norm := module) h
    rw [h3]
    have : (1 + α) / α = α⁻¹ * (1 + α) := by ring
    rw [this, mul_smul]
    module
  · intro h
    rw [h]
    have : (1 + α) / α = α⁻¹ * (1 + α) := by ring
    rw [this, mul_smul]
    have h4 : α • α⁻¹ • ((1 + α) • p t) = (1 + α) • p t := by
      rw [smul_smul, mul_inv_cancel₀ hα, one_smul]
    have h5 : α • α⁻¹ • m t = m t := by rw [smul_smul, mul_inv_cancel₀ hα, one_smul]
    linear_combination (norm := module) h4 - h5

/-- Exercise 1: `b = (1 + α)/α > 1` for `α > 0`. -/
theorem ex_1_b_gt_one {α : ℝ} (hα : 0 < α) : 1 < |(1 + α) / α| := by
  rw [abs_of_pos (by positivity), lt_div_iff₀ hα]
  linarith

/-- **Exercise 1** (Miao, p. 82), existence and uniqueness: for `α > 0` and a stable adapted
money supply, the forward solution `p_t = α^{−1}∑ⱼ b^{−j−1}E_tm_{t+j}`, `b = (1 + α)/α`, is a
stable adapted solution, and it is the only one. -/
theorem ex_1_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {α : ℝ} (hα : 0 < α)
    {m : ℕ → V} (hma : sre_IsAdapted E m) (hm : sre_IsBounded m) :
    (sre_IsAdapted E (sre_fwd E ((1 + α) / α) (-α⁻¹ • m)) ∧
      sre_IsBounded (sre_fwd E ((1 + α) / α) (-α⁻¹ • m)) ∧
      ex1_IsSol E α m (sre_fwd E ((1 + α) / α) (-α⁻¹ • m))) ∧
    ∀ p, sre_IsAdapted E p → sre_IsBounded p → ex1_IsSol E α m p →
      p = sre_fwd E ((1 + α) / α) (-α⁻¹ • m) := by
  have hb := ex_1_b_gt_one hα
  have hfa := sre_smul_isAdapted E (-α⁻¹) hma
  have hfb := sre_smul_isBounded (-α⁻¹) hm
  have hpa := sre_fwd_adapted E hb hfb
  refine ⟨⟨hpa, sre_fwd_isBounded E hb hfb,
    (ex_1_iff E hα.ne' hpa).2 (sre_fwd_rec E hb hfa hfb)⟩, fun p hp hpb hps => ?_⟩
  exact eq_2_3_unique E hb hfa hfb hp hpb ((ex_1_iff E hα.ne' hp).1 hps)

/-- Exercise 1: `m_{t+1} = ρm_t + ε_{t+1}` with `E_tε_{t+1} = 0` gives `E_tm_{t+1} = ρm_t`. -/
theorem ex_1_Em (E : CondExpSystem ℝ V) {ρ : ℝ} {m ε : ℕ → V} (hma : sre_IsAdapted E m)
    (hrec : ∀ t, m (t + 1) = ρ • m t + ε (t + 1)) (hε : ∀ t, E.E t (ε (t + 1)) = 0) (t : ℕ) :
    E.E t (m (t + 1)) = ρ • m t := by
  rw [hrec, map_add, hε, add_zero, map_smul, hma]

/-- **Exercise 1** (Miao, p. 82): if `E_tm_{t+1} = ρm_t` (e.g. `E_tε_{t+1} = 0`, `ex_1_Em`) and
`1 + α(1 − ρ) ≠ 0`, then `p_t = m_t/(1 + α(1 − ρ))` solves the Cagan model. -/
theorem ex_1_solution (E : CondExpSystem ℝ V) {α ρ : ℝ} {m : ℕ → V}
    (hma : sre_IsAdapted E m) (hm : ∀ t, E.E t (m (t + 1)) = ρ • m t)
    (hd : 1 + α * (1 - ρ) ≠ 0) :
    ex1_IsSol E α m (fun t => (1 + α * (1 - ρ))⁻¹ • m t) := by
  intro t
  rw [map_sub, map_smul, map_smul, hm, hma]
  have hk : (1 + α * (1 - ρ))⁻¹ * (1 + α * (1 - ρ)) = 1 := inv_mul_cancel₀ hd
  linear_combination (norm := module) -(hk • m t)

/-- **Exercise 1** (Miao, p. 82): the solution `m_t/(1 + α(1 − ρ))` is the forward solution
for every `ρ ∈ [0, 1]` (the forward sum converges since `ρ ≤ 1 < b`, even if `m` is not stable). -/
theorem ex_1_solution_eq_fwd (E : CondExpSystem ℝ V) {α ρ : ℝ} (hα : 0 < α) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) {m : ℕ → V} (hma : sre_IsAdapted E m)
    (hm : ∀ t, E.E t (m (t + 1)) = ρ • m t) (t : ℕ) :
    sre_fwd E ((1 + α) / α) (-α⁻¹ • m) t = (1 + α * (1 - ρ))⁻¹ • m t := by
  have hb := ex_1_b_gt_one hα
  have hρb : |ρ| < |(1 + α) / α| := by
    rw [abs_of_nonneg hρ0]
    exact lt_of_le_of_lt hρ1 hb
  rw [sre_fwd_ar1 E hρb (sre_smul_isAdapted E _ hma) (fun t => by
    simp only [Pi.smul_apply, map_smul, hm t, smul_comm (-α⁻¹) ρ]) t, Pi.smul_apply, smul_smul]
  congr 1
  have h1 : ρ - (1 + α) / α ≠ 0 := by
    intro h
    have : ρ = (1 + α) / α := by linarith
    rw [this, abs_of_pos (by positivity)] at hρb
    exact lt_irrefl _ hρb
  have h2 : 1 + α * (1 - ρ) ≠ 0 := by nlinarith
  rw [show ρ - (1 + α) / α = -(1 + α * (1 - ρ)) / α by field_simp; ring, inv_div]
  field_simp

/-- **Exercise 1** (Miao, p. 82), the answer: for `α > 0`, `ρ ∈ [0, 1)`, `m₀` adapted and a
stable shock with `E_tε_{t+1} = 0`, the money supply is stable and `p_t = m_t/(1 + α(1 − ρ))` is
the unique stable adapted solution. -/
theorem ex_1 [CompleteSpace V] (E : CondExpSystem ℝ V) {α ρ : ℝ} (hα : 0 < α) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {m ε : ℕ → V} (hma : sre_IsAdapted E m)
    (hrec : ∀ t, m (t + 1) = ρ • m t + ε (t + 1)) (hε : ∀ t, E.E t (ε (t + 1)) = 0)
    (hεb : sre_IsBounded ε) :
    sre_IsBounded m ∧ ex1_IsSol E α m (fun t => (1 + α * (1 - ρ))⁻¹ • m t) ∧
      sre_IsBounded (fun t => (1 + α * (1 - ρ))⁻¹ • m t) ∧
      ∀ p, sre_IsAdapted E p → sre_IsBounded p → ex1_IsSol E α m p →
        p = fun t => (1 + α * (1 - ρ))⁻¹ • m t := by
  have hEm := ex_1_Em E hma hrec hε
  have hd : 1 + α * (1 - ρ) ≠ 0 := by nlinarith
  have hmb : sre_IsBounded m := by
    obtain ⟨U, hU⟩ := hεb
    have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0)
    have hl : |ρ| < 1 := by rw [abs_of_nonneg hρ0]; exact hρ1
    refine ⟨_, sre_bounded_of_rec hl hU0 (fun t => ?_)⟩
    rw [hrec]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    exact hU _
  refine ⟨hmb, ex_1_solution E hma hEm hd, ?_, fun p hp hpb hps => ?_⟩
  · have := sre_smul_isBounded (1 + α * (1 - ρ))⁻¹ hmb
    exact this
  · rw [(ex_1_unique E hα hma hmb).2 p hp hpb hps]
    funext t
    exact ex_1_solution_eq_fwd E hα hρ0 hρ1.le hma hEm t

/-- **Exercise 1** (Miao, p. 82), what the shock must satisfy: with `m` adapted,
`m_{t+1} = ρm_t + ε_{t+1}` and `1 + α(1 − ρ) ≠ 0`, the price `m_t/(1 + α(1 − ρ))` solves the
model iff `E_tε_{t+1} = 0` for all `t`. A white noise (the book's assumption) need not satisfy this
(`whiteNoise_not_mds`). -/
theorem ex_1_solution_iff (E : CondExpSystem ℝ V) {α ρ : ℝ} {m ε : ℕ → V}
    (hma : sre_IsAdapted E m) (hrec : ∀ t, m (t + 1) = ρ • m t + ε (t + 1))
    (hd : 1 + α * (1 - ρ) ≠ 0) (hα : α ≠ 0) :
    ex1_IsSol E α m (fun t => (1 + α * (1 - ρ))⁻¹ • m t) ↔ ∀ t, E.E t (ε (t + 1)) = 0 := by
  refine ⟨fun h t => ?_, fun h => ex_1_solution E hma (ex_1_Em E hma hrec h) hd⟩
  have ht := h t
  rw [map_sub, map_smul, map_smul, hma, hrec, map_add, map_smul, hma] at ht
  have hk : (1 + α * (1 - ρ))⁻¹ * (1 + α * (1 - ρ)) = 1 := inv_mul_cancel₀ hd
  have h2 : (α * (1 + α * (1 - ρ))⁻¹) • E.E t (ε (t + 1)) = 0 := by
    linear_combination (norm := module) ht + hk • m t
  exact (smul_eq_zero.1 h2).resolve_left (mul_ne_zero hα (inv_ne_zero hd))

/-- Exercise 1 with `ρ = 1`: `m` is a martingale, `E_tm_{t+j} = m_t`. -/
theorem ex_1_rho_one_martingale (E : CondExpSystem ℝ V) {m ε : ℕ → V}
    (hma : sre_IsAdapted E m) (hrec : ∀ t, m (t + 1) = m t + ε (t + 1))
    (hε : ∀ t, E.E t (ε (t + 1)) = 0) (j t : ℕ) : E.E t (m (t + j)) = m t := by
  have := sre_iter E hma (b := 1) (fun t => by
    rw [one_smul]; simpa using ex_1_Em E hma (ρ := 1) (fun t => by rw [one_smul, hrec]) hε t) j t
  rwa [one_pow, one_smul] at this

omit [NormedSpace ℝ V] in
/-- Exercise 1 with `ρ = 1`: `‖m_t‖ ≤ ‖m₀‖ + tU` when `‖ε_t‖ ≤ U`; the norm grows at most
linearly (and need not stay bounded). -/
theorem ex_1_rho_one_growth {m ε : ℕ → V} {U : ℝ} (hrec : ∀ t, m (t + 1) = m t + ε (t + 1))
    (hU : ∀ t, ‖ε t‖ ≤ U) (t : ℕ) : ‖m t‖ ≤ ‖m 0‖ + t * U := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hrec]
    calc ‖m t + ε (t + 1)‖ ≤ ‖m t‖ + ‖ε (t + 1)‖ := norm_add_le _ _
      _ ≤ ‖m 0‖ + t * U + U := add_le_add ih (hU _)
      _ = ‖m 0‖ + ((t + 1 : ℕ) : ℝ) * U := by push_cast; ring

/-- **Exercise 1** with `ρ = 1` (Miao, p. 82): `p = m` solves the Cagan model and is the unique
adapted solution satisfying the transversality condition (2.5) `b^{−T}E_tp_{t+T} → 0`
(`b = (1 + α)/α`), with no stability assumption on `m`; `p` is stable iff `m` is. -/
theorem ex_1_rho_one (E : CondExpSystem ℝ V) {α : ℝ} (hα : 0 < α) {m ε : ℕ → V}
    (hma : sre_IsAdapted E m) (hrec : ∀ t, m (t + 1) = m t + ε (t + 1))
    (hε : ∀ t, E.E t (ε (t + 1)) = 0) :
    ex1_IsSol E α m m ∧ sre_Transversality E ((1 + α) / α) m ∧
      ∀ p, sre_IsAdapted E p → sre_Transversality E ((1 + α) / α) p → ex1_IsSol E α m p →
        p = m := by
  have hb := ex_1_b_gt_one hα
  have hEm : ∀ t, E.E t (m (t + 1)) = (1 : ℝ) • m t := fun t => by
    rw [one_smul]; exact (by simpa using ex_1_rho_one_martingale E hma hrec hε 1 t)
  have hsol : ex1_IsSol E α m m := by
    have := ex_1_solution E hma hEm (α := α) (by simp)
    simpa using this
  have htv : sre_Transversality E ((1 + α) / α) m := by
    intro t
    have hr : |((1 + α) / α)⁻¹| < 1 := sre_inv_abs_lt_one hb
    have hl := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).smul_const (m t)
    rw [zero_smul] at hl
    refine hl.congr fun T => ?_
    rw [ex_1_rho_one_martingale E hma hrec hε T t]
  have hb0 : (1 + α) / α ≠ 0 := by positivity
  refine ⟨hsol, htv, fun p hp hpt hps => ?_⟩
  exact sre_unique_of_tvc E hb0 hp hma hpt htv ((ex_1_iff E hα.ne' hp).1 hps)
    ((ex_1_iff E hα.ne' hma).1 hsol)

end Miao.RationalExpectations

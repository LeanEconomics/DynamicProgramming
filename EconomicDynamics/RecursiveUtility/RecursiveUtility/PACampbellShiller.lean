/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.PALogNormal
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The Campbell–Shiller approximation and the return decomposition

Miao, *Economic Dynamics in Discrete Time*, §20.4.2 (pp. 717–719), equations (20.36)–(20.41).

* (20.36): the exact log return is `r_{t+1} = d_{t+1} − p_t + ln(1 + e^{p_{t+1} − d_{t+1}})`
  (`pa_cs_exact`); `x ↦ ln(1 + eˣ)` has derivative `ϱ = 1/(1 + exp(d̄ − p̄))` at the mean
  `p̄ − d̄` (`pa_cs_hasDerivAt`), its tangent there is `κ + ϱ x` with
  `κ = −ln ϱ − (1 − ϱ) ln(1/ϱ − 1)` (`pa_cs_kappa`), and so (20.36) is the first-order Taylor
  expansion, with an error that is `o(p_{t+1} − d_{t+1} − (p̄ − d̄))` (`eq_20_36`).
* (20.38): `eq_20_38` (a rearrangement of (20.36)).
* (20.37): solving forward with the terminal condition `ϱⁿ(p_{t+n} − d_{t+n}) → 0`, path by
  path (`pa_cs_iterate`, `eq_20_37`), and its conditional expectation (`eq_20_37_cond`).
* (20.39): `eq_20_39`, with `E_t`, `E_{t+1}` linear operators on random variables.
* (20.40)–(20.41), the equity volatility accounting with dividends `d_e = λ c` and
  `E_t r_{e,t+1+k} = μ_e + ρ E_t Δc_{t+1+k}`: `eq_20_40`, `eq_20_41` (finite sample space, so
  that conditional expectations commute with the limits of the discounted sums).

Departure: the terminal condition is imposed on the log price–dividend ratio
`ϱⁿ(p_{t+n} − d_{t+n}) → 0` (the text writes `ϱⁱ p_{t+i} → 0`); this is the condition the
forward solution uses.
-/

namespace Miao.RecursiveUtility

open Real Filter Topology Asymptotics

/-- Miao, p. 717: the linearisation coefficient `ϱ = 1/(1 + exp(d̄ − p̄))`, as a function of the
mean log dividend–price ratio `d̄ − p̄`. -/
noncomputable def pa_varrho (dp : ℝ) : ℝ := 1 / (1 + Real.exp dp)

/-- Miao, p. 717: the constant `κ = −ln ϱ − (1 − ϱ) ln(1/ϱ − 1)`. -/
noncomputable def pa_kappa (ϱ : ℝ) : ℝ := -Real.log ϱ - (1 - ϱ) * Real.log (1 / ϱ - 1)

theorem pa_varrho_pos (dp : ℝ) : 0 < pa_varrho dp := by
  unfold pa_varrho; positivity

theorem pa_varrho_lt_one (dp : ℝ) : pa_varrho dp < 1 := by
  unfold pa_varrho
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos dp]

/-- Miao, p. 717: the exact identity behind (20.36). With `p = ln P`, `d = ln D`,
`r_{t+1} = ln((P_{t+1} + D_{t+1})/P_t) = d_{t+1} − p_t + ln(1 + exp(p_{t+1} − d_{t+1}))`. -/
theorem pa_cs_exact {P P' D' : ℝ} (hP : 0 < P) (hP' : 0 < P') (hD' : 0 < D') :
    Real.log ((P' + D') / P)
      = Real.log D' - Real.log P + Real.log (1 + Real.exp (Real.log P' - Real.log D')) := by
  rw [Real.exp_sub, Real.exp_log hP', Real.exp_log hD']
  have h1 : (P' + D') / P = D' / P * (1 + P' / D') := by field_simp; ring
  rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_div hD'.ne' hP.ne']

/-- Miao, p. 717: the derivative of `x ↦ ln(1 + eˣ)` at `x̄ = p̄ − d̄` is
`ϱ = 1/(1 + exp(d̄ − p̄))`. -/
theorem pa_cs_hasDerivAt (xbar : ℝ) :
    HasDerivAt (fun x => Real.log (1 + Real.exp x)) (pa_varrho (-xbar)) xbar := by
  have h := ((Real.hasDerivAt_exp xbar).const_add 1).log (by positivity)
  convert h using 1
  simp only [pa_varrho, Real.exp_neg]
  have := Real.exp_pos xbar
  field_simp
  ring

/-- Miao, p. 717: the tangent of `x ↦ ln(1 + eˣ)` at `x̄` is `κ + ϱ x`, i.e.
`ln(1 + e^{x̄}) − ϱ x̄ = κ = −ln ϱ − (1 − ϱ) ln(1/ϱ − 1)` with `ϱ = 1/(1 + e^{−x̄})`. -/
theorem pa_cs_kappa (xbar : ℝ) :
    Real.log (1 + Real.exp xbar) - pa_varrho (-xbar) * xbar = pa_kappa (pa_varrho (-xbar)) := by
  have h1 : 1 / pa_varrho (-xbar) - 1 = Real.exp (-xbar) := by
    simp only [pa_varrho]; field_simp; ring
  have h2 : Real.log (1 + Real.exp xbar) = xbar + Real.log (1 + Real.exp (-xbar)) := by
    rw [← Real.log_exp xbar, ← Real.log_mul (by positivity) (by positivity), Real.log_exp]
    congr 1
    rw [mul_add, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    ring
  simp only [pa_kappa, h1, Real.log_exp]
  rw [h2]
  simp only [pa_varrho, one_div, Real.log_inv]
  ring

/-- Miao, (20.36), p. 717: the Campbell–Shiller approximation. With `x̄ = p̄ − d̄`,
`ϱ = 1/(1 + exp(d̄ − p̄))` and `κ = −ln ϱ − (1 − ϱ) ln(1/ϱ − 1)`, the exact log return is
`r_{t+1} = κ + ϱ p_{t+1} + (1 − ϱ) d_{t+1} − p_t + e(p_{t+1} − d_{t+1})`, where the error
`e(x) = ln(1 + eˣ) − κ − ϱx` is `o(x − x̄)` as `x → x̄`. -/
theorem eq_20_36 (xbar : ℝ) :
    (∀ p d' p' : ℝ, Real.log ((Real.exp p' + Real.exp d') / Real.exp p)
      = pa_kappa (pa_varrho (-xbar)) + pa_varrho (-xbar) * p' + (1 - pa_varrho (-xbar)) * d' - p
        + (Real.log (1 + Real.exp (p' - d')) - pa_kappa (pa_varrho (-xbar))
          - pa_varrho (-xbar) * (p' - d'))) ∧
    (fun x => Real.log (1 + Real.exp x) - pa_kappa (pa_varrho (-xbar))
      - pa_varrho (-xbar) * x) =o[𝓝 xbar] fun x => x - xbar := by
  refine ⟨fun p d' p' => ?_, ?_⟩
  · rw [pa_cs_exact (Real.exp_pos p) (Real.exp_pos p') (Real.exp_pos d'), Real.log_exp,
      Real.log_exp, Real.log_exp]
    ring
  · have h := (hasDerivAt_iff_isLittleO.1 (pa_cs_hasDerivAt xbar))
    refine h.congr_left fun x => ?_
    rw [← pa_cs_kappa xbar, smul_eq_mul]
    ring

/-- Miao, (20.38), p. 717: (20.36) rewritten as
`r_{t+1} = κ + ϱ(p_{t+1} − d_{t+1}) + Δd_{t+1} + (d_t − p_t)`. -/
theorem eq_20_38 (κ ϱ p d p' d' : ℝ) :
    κ + ϱ * p' + (1 - ϱ) * d' - p = κ + ϱ * (p' - d') + (d' - d) + (d - p) := by ring

/-- Iterating (20.38) forward `n` periods:
`pd_t = ∑_{k<n} ϱᵏ (κ + Δd_{t+1+k} − r_{t+1+k}) + ϱⁿ pd_{t+n}`, `pd = p − d`. -/
theorem pa_cs_iterate {κ ϱ : ℝ} {pd dd r : ℕ → ℝ}
    (h38 : ∀ t, r (t + 1) = κ + ϱ * pd (t + 1) + dd (t + 1) - pd t) (t n : ℕ) :
    pd t = ∑ k ∈ Finset.range n, ϱ ^ k * (κ + dd (t + 1 + k) - r (t + 1 + k))
      + ϱ ^ n * pd (t + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := h38 (t + n)
    rw [show t + n + 1 = t + 1 + n by ring] at h
    rw [ih, Finset.sum_range_succ, show t + (n + 1) = t + 1 + n by ring, h, pow_succ]
    ring

/-- Miao, (20.37), p. 717: solving (20.38) forward under the terminal condition
`ϱⁿ pd_{t+n} → 0`, `pd_t = κ/(1 − ϱ) + ∑_{k≥0} ϱᵏ (Δd_{t+1+k} − r_{t+1+k})` (the partial sums
converge to `pd_t − κ/(1 − ϱ)`), path by path. -/
theorem eq_20_37 {κ ϱ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) {pd dd r : ℕ → ℝ}
    (h38 : ∀ t, r (t + 1) = κ + ϱ * pd (t + 1) + dd (t + 1) - pd t) (t : ℕ)
    (hterm : Tendsto (fun n => ϱ ^ n * pd (t + n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ k * (dd (t + 1 + k) - r (t + 1 + k))) atTop
      (𝓝 (pd t - κ / (1 - ϱ))) := by
  have hgeom := (hasSum_geometric_of_lt_one hϱ0 hϱ1).tendsto_sum_nat
  have heq : ∀ n, ∑ k ∈ Finset.range n, ϱ ^ k * (dd (t + 1 + k) - r (t + 1 + k))
      = pd t - ϱ ^ n * pd (t + n) - κ * ∑ k ∈ Finset.range n, ϱ ^ k := by
    intro n
    rw [pa_cs_iterate h38 t n, Finset.mul_sum]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have : ∑ k ∈ Finset.range n, ϱ ^ k * κ = ∑ k ∈ Finset.range n, κ * ϱ ^ k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [this]
    ring
  simp only [heq]
  have := ((tendsto_const_nhds (x := pd t)).sub hterm).sub (hgeom.const_mul κ)
  convert this using 2
  rw [sub_zero, div_eq_mul_inv]

/-- Miao, (20.37), p. 717, conditional form: for any linear conditional expectation `E_t` that
fixes constants and the time-`t` variable `pd_t`, if the partial sums converge to `Y` on every
path, then `pd_t = κ/(1 − ϱ) + E_t Y`. -/
theorem eq_20_37_cond {Ω : Type*} {κ ϱ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    {pd dd r : ℕ → Ω → ℝ} (h38 : ∀ ω t, r (t + 1) ω = κ + ϱ * pd (t + 1) ω + dd (t + 1) ω - pd t ω)
    (t : ℕ) (hterm : ∀ ω, Tendsto (fun n => ϱ ^ n * pd (t + n) ω) atTop (𝓝 0))
    (E : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) (hE1 : E (fun _ => 1) = fun _ => 1) (hEpd : E (pd t) = pd t)
    {Y : Ω → ℝ} (hY : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n,
      ϱ ^ k * (dd (t + 1 + k) ω - r (t + 1 + k) ω)) atTop (𝓝 (Y ω))) :
    pd t = (fun _ => κ / (1 - ϱ)) + E Y := by
  have hYeq : Y = pd t - (κ / (1 - ϱ)) • fun _ => (1 : ℝ) := by
    funext ω
    have h := eq_20_37 hϱ0 hϱ1 (pd := fun t => pd t ω) (dd := fun t => dd t ω)
      (r := fun t => r t ω) (fun t => h38 ω t) t (hterm ω)
    rw [tendsto_nhds_unique (hY ω) h]
    simp
  rw [hYeq, map_sub, map_smul, hE1, hEpd]
  funext ω
  simp

/-- Miao, (20.39), p. 717: unexpected returns are revisions in expected dividend growth less
revisions in expected future returns,
`r_{t+1} − E_t r_{t+1}
= (E_{t+1} − E_t) ∑_{k≥0} ϱᵏ Δd_{t+1+k} − (E_{t+1} − E_t) ∑_{k≥1} ϱᵏ r_{t+1+k}`.
`E_t`, `E_{t+1}` are linear, fix constants, `E_{t+1}` fixes the time-`t+1` variables and both
fix `pd_t`; `D` and `Rs` are the path-by-path sums. -/
theorem eq_20_39 {Ω : Type*} {κ ϱ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    {pd dd r : ℕ → Ω → ℝ} (h38 : ∀ ω t, r (t + 1) ω = κ + ϱ * pd (t + 1) ω + dd (t + 1) ω - pd t ω)
    (t : ℕ) (hterm : ∀ ω, Tendsto (fun n => ϱ ^ n * pd (t + 1 + n) ω) atTop (𝓝 0))
    (E0 E1 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) (h01 : E0 (fun _ => 1) = fun _ => 1)
    (h11 : E1 (fun _ => 1) = fun _ => 1) (hE0pd : E0 (pd t) = pd t) (hE1pd : E1 (pd t) = pd t)
    (hE1r : E1 (r (t + 1)) = r (t + 1)) {D Rs : Ω → ℝ}
    (hD : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ k * dd (t + 1 + k) ω) atTop
      (𝓝 (D ω)))
    (hRs : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) * r (t + 2 + k) ω) atTop
      (𝓝 (Rs ω))) :
    r (t + 1) - E0 (r (t + 1)) = (E1 D - E0 D) - (E1 Rs - E0 Rs) := by
  -- path by path, `r_{t+1} = κ/(1 − ϱ) + D − Rs − pd_t`
  have hpath : r (t + 1) = (κ / (1 - ϱ)) • (fun _ => (1 : ℝ)) + D - Rs - pd t := by
    funext ω
    have h37 := eq_20_37 hϱ0 hϱ1 (pd := fun t => pd t ω) (dd := fun t => dd t ω)
      (r := fun t => r t ω) (fun t => h38 ω t) (t + 1) (hterm ω)
    have hshift : Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) * dd (t + 2 + k) ω)
        atTop (𝓝 (D ω - dd (t + 1) ω)) := by
      have h := ((hD ω).comp (tendsto_add_atTop_nat 1)).sub_const (dd (t + 1) ω)
      refine h.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul, add_zero, add_sub_cancel_right]
      exact Finset.sum_congr rfl fun k _ => by rw [show t + 1 + (k + 1) = t + 2 + k by ring]
    have hR2 : Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) * r (t + 2 + k) ω) atTop
        (𝓝 ((D ω - dd (t + 1) ω) - ϱ * (pd (t + 1) ω - κ / (1 - ϱ)))) := by
      refine (hshift.sub (h37.const_mul ϱ)).congr fun n => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by
        rw [show t + 1 + 1 + k = t + 2 + k by ring, pow_succ]; ring
    have hRs' := tendsto_nhds_unique (hRs ω) hR2
    have h1 : (1 : ℝ) - ϱ ≠ 0 := by linarith
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [hRs', h38 ω t]
    field_simp
    ring
  have hlhs : r (t + 1) - E0 (r (t + 1)) = E1 (r (t + 1)) - E0 (r (t + 1)) := by rw [hE1r]
  rw [hlhs, ← LinearMap.sub_apply, hpath]
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, h01, h11, hE0pd, hE1pd]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Miao, (20.40), p. 719: with dividends `d_e = λ c` and expected returns
`E_t r_{e,t+1+k} = μ_e + ρ E_t Δc_{t+1+k}` (from (20.33) and (20.35)), (20.37) becomes
`pd_{e,t} = k_e/(1 − ϱ) + (λ − ρ) E_t ∑_{i≥0} ϱⁱ Δc_{t+1+i}`, `k_e = κ − μ_e`.
The sample space is finite, so `E_t` is continuous. -/
theorem eq_20_40 {Ω : Type*} [Finite Ω] {κ ϱ lam ρ μe : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    {pd dd r dc : ℕ → Ω → ℝ}
    (h38 : ∀ ω t, r (t + 1) ω = κ + ϱ * pd (t + 1) ω + dd (t + 1) ω - pd t ω)
    (hdd : ∀ t, dd t = lam • dc t) (t : ℕ)
    (hterm : ∀ ω, Tendsto (fun n => ϱ ^ n * pd (t + n) ω) atTop (𝓝 0))
    (E0 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) (h01 : E0 (fun _ => 1) = fun _ => 1)
    (hE0pd : E0 (pd t) = pd t)
    (hr : ∀ k, E0 (r (t + 1 + k)) = μe • (fun _ => 1) + ρ • E0 (dc (t + 1 + k)))
    {G : Ω → ℝ} (hG : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ k * dc (t + 1 + k) ω)
      atTop (𝓝 (G ω))) :
    pd t = (fun _ => (κ - μe) / (1 - ϱ)) + (lam - ρ) • E0 G := by
  have hc : Continuous E0 := LinearMap.continuous_of_finiteDimensional E0
  set S : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, ϱ ^ k • (dd (t + 1 + k) - r (t + 1 + k))
    with hS
  set Gn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, ϱ ^ k • dc (t + 1 + k) with hGn
  have hSlim : Tendsto S atTop (𝓝 (pd t - (κ / (1 - ϱ)) • fun _ => (1 : ℝ))) := by
    refine tendsto_pi_nhds.2 fun ω => ?_
    have h := eq_20_37 hϱ0 hϱ1 (pd := fun t => pd t ω) (dd := fun t => dd t ω)
      (r := fun t => r t ω) (fun t => h38 ω t) t (hterm ω)
    simp only [hS, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_one]
    exact h
  have hGlim : Tendsto Gn atTop (𝓝 G) := by
    refine tendsto_pi_nhds.2 fun ω => ?_
    simp only [hGn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hG ω
  have hES : ∀ n, E0 (S n) = (lam - ρ) • E0 (Gn n)
      - (μe * ∑ k ∈ Finset.range n, ϱ ^ k) • fun _ => (1 : ℝ) := by
    intro n
    simp only [hS, hGn, map_sum, map_smul, map_sub, hdd, hr]
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul,
      mul_one, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hlim1 := (hc.tendsto _).comp hSlim
  have hgeom := (hasSum_geometric_of_lt_one hϱ0 hϱ1).tendsto_sum_nat
  have hlim2 : Tendsto (fun n => E0 (S n)) atTop
      (𝓝 ((lam - ρ) • E0 G - (μe * (1 - ϱ)⁻¹) • fun _ => (1 : ℝ))) := by
    simp only [hES]
    exact (((hc.tendsto _).comp hGlim).const_smul (lam - ρ)).sub
      ((hgeom.const_mul μe).smul_const _)
  have huniq := tendsto_nhds_unique hlim1 hlim2
  rw [map_sub, map_smul, h01, hE0pd] at huniq
  funext ω
  have := congrFun huniq ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one] at this
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : (1 : ℝ) - ϱ ≠ 0 := by linarith
  field_simp at this ⊢
  linarith

/-- Miao, (20.41), p. 719: with `d_e = λ c` and `E r_{e,t+1+k} = μ_e + ρ E Δc_{t+1+k}` under
both `E_t` and `E_{t+1}` (`k ≥ 1`),
`r_{e,t+1} − E_t r_{e,t+1}
= λ(Δc_{t+1} − E_t Δc_{t+1}) + (λ − ρ)(E_{t+1} − E_t) ∑_{i≥1} ϱⁱ Δc_{t+1+i}`.
-/
theorem eq_20_41 {Ω : Type*} [Finite Ω] {κ ϱ lam ρ μe : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    {pd dd r dc : ℕ → Ω → ℝ}
    (h38 : ∀ ω t, r (t + 1) ω = κ + ϱ * pd (t + 1) ω + dd (t + 1) ω - pd t ω)
    (hdd : ∀ t, dd t = lam • dc t) (t : ℕ)
    (hterm : ∀ ω, Tendsto (fun n => ϱ ^ n * pd (t + 1 + n) ω) atTop (𝓝 0))
    (E0 E1 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) (h01 : E0 (fun _ => 1) = fun _ => 1)
    (h11 : E1 (fun _ => 1) = fun _ => 1) (hE0pd : E0 (pd t) = pd t) (hE1pd : E1 (pd t) = pd t)
    (hE1r : E1 (r (t + 1)) = r (t + 1)) (hE1c : E1 (dc (t + 1)) = dc (t + 1))
    (hr0 : ∀ k, E0 (r (t + 2 + k)) = μe • (fun _ => 1) + ρ • E0 (dc (t + 2 + k)))
    (hr1 : ∀ k, E1 (r (t + 2 + k)) = μe • (fun _ => 1) + ρ • E1 (dc (t + 2 + k)))
    {G1 Rs : Ω → ℝ}
    (hG1 : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) * dc (t + 2 + k) ω) atTop
      (𝓝 (G1 ω)))
    (hRs : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) * r (t + 2 + k) ω) atTop
      (𝓝 (Rs ω))) :
    r (t + 1) - E0 (r (t + 1))
      = lam • (dc (t + 1) - E0 (dc (t + 1))) + (lam - ρ) • (E1 G1 - E0 G1) := by
  have hc0 : Continuous E0 := LinearMap.continuous_of_finiteDimensional E0
  have hc1 : Continuous E1 := LinearMap.continuous_of_finiteDimensional E1
  set D : Ω → ℝ := lam • (dc (t + 1) + G1) with hDdef
  have hD : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ k * dd (t + 1 + k) ω) atTop
      (𝓝 (D ω)) := by
    intro ω
    have h := (((hG1 ω).const_add (dc (t + 1) ω)).const_mul lam).comp
      (tendsto_sub_atTop_nat 1)
    refine (h.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Function.comp_apply, Nat.add_sub_cancel, hdd, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, add_zero, mul_add, Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by
      rw [show t + 1 + (k + 1) = t + 2 + k by ring]; ring
  have h39 := eq_20_39 hϱ0 hϱ1 h38 t hterm E0 E1 h01 h11 hE0pd hE1pd hE1r hD hRs
  -- revisions of the return sum are `ρ` times revisions of the consumption-growth sum
  set Rn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) • r (t + 2 + k) with hRn
  set Gn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) • dc (t + 2 + k) with hGn
  have hRlim : Tendsto Rn atTop (𝓝 Rs) := by
    refine tendsto_pi_nhds.2 fun ω => ?_
    simp only [hRn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hRs ω
  have hGlim : Tendsto Gn atTop (𝓝 G1) := by
    refine tendsto_pi_nhds.2 fun ω => ?_
    simp only [hGn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hG1 ω
  have hrev : ∀ n, E1 (Rn n) - E0 (Rn n) = ρ • (E1 (Gn n) - E0 (Gn n)) := by
    intro n
    simp only [hRn, hGn, map_sum, map_smul, hr0, hr1, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hl1 : Tendsto (fun n => E1 (Rn n) - E0 (Rn n)) atTop (𝓝 (E1 Rs - E0 Rs)) :=
    ((hc1.tendsto _).comp hRlim).sub ((hc0.tendsto _).comp hRlim)
  have hl2 : Tendsto (fun n => E1 (Rn n) - E0 (Rn n)) atTop (𝓝 (ρ • (E1 G1 - E0 G1))) := by
    simp only [hrev]
    exact (((hc1.tendsto _).comp hGlim).sub ((hc0.tendsto _).comp hGlim)).const_smul ρ
  rw [h39, tendsto_nhds_unique hl1 hl2, hDdef, map_smul, map_smul, map_add, map_add, hE1c]
  funext ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Miao.RecursiveUtility

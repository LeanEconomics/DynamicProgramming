/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.JDSteadyState
import SearchAndMatching.JDBusinessCycle

/-!
# Exercises 18.3–18.5 (Miao, p. 614)

Miao, *Economic Dynamics in Discrete Time*, §18.4, Exercises 3–5, p. 614.

**Exercise 18.3** (a mean-preserving spread in `G`, model of §18.2). A mean-preserving spread
(increase in risk, Rothschild–Stiglitz) raises the option-value integral pointwise,
`Φ_{G′} ≥ Φ_G`, with the mean unchanged; this integral condition is the hypothesis used, and a
concrete spread (`δ₁` versus `½ δ_{1/2} + ½ δ_{3/2}`) satisfies it (`jd_mps_example`). Proved:
steady-state tightness does not fall, and rises strictly if `Φ_{G′}(z̄*) > Φ_G(z̄*)`
(`ex_18_3_theta`); the reservation productivity moves with
`H(θ) = η θ κ − (1 − ρˣ) κ / q(θ)`, a function that does not involve `G`:
`(1 − η) A (z̄*′ − z̄*) = H(θ′) − H(θ)` (`ex_18_3_reservation`), so `z̄*` rises when `H` is
nondecreasing (`ex_18_3_reservation_mono`); steady-state unemployment falls if the separation
rate does not rise and tightness rises strictly (`ex_18_3_unemployment`). In general the
effects on `z̄*` and `u` are ambiguous (`H` need not be monotone; `G` itself changes `ρ`).

**Exercise 18.4** (the planner's problem for the model of §18.3). The planner chooses next-period
capital and vacancies subject to the resource constraint and `N′ = (1 − ρ) N + M(1 − N, v)`
(`jd_plannerObj`). Proved: the first-order conditions for capital and vacancies
(`ex_18_4_foc_K`, `ex_18_4_foc_v`), the envelope conditions (`ex_18_4_envelope_K`,
`ex_18_4_envelope_N`), the planner's Euler equation (`ex_18_4_euler`) and surplus recursion with
job creation condition (`ex_18_4_surplus`); the partial derivatives of `M(u, v) = v q(v/u)`:
`M_v = q (1 − ξ)`, `M_u = ξ θ q` with `ξ = −θ q′/q` (`jd_matching_partial_v`,
`jd_matching_partial_u`). Efficiency: node by node,
`S^F − (1 − η) S^P = −(1 − η) b + (η − ξ) κ ((1 − ρ)/q − θ)/(1 − ξ)` (`ex_18_4_gap`), so with
`b = 0` and the Hosios condition `η = ξ` the decentralised firm surplus is `(1 − η)` times the
planner's surplus and the two job creation conditions coincide (`ex_18_4_hosios`). The steady-state
tightness equations are the analogues of (18.18) and (18.28) (`ex_18_4_ss_decentralised`,
`ex_18_4_ss_planner`), and coincide when `η = ξ`, `b = 0` (`ex_18_4_ss_hosios`).

**Exercise 18.5** (calibration of §18.3; the numerical solution is not formalised). Its
mathematical content: the steady-state rental rate `R = 1/β − 1 + δ` (`ex_18_5_rental`),
employment and unemployment `N = f/(ρ + f)`, `u = ρ/(ρ + f)` (`ex_18_5_employment`), the
separation rate implied by targets for `u` and `f` (`ex_18_5_rho`), the posting cost implied by a
target `θ` (`ex_18_5_kappa`, the unique `κ` solving the steady-state tightness equation), and
steady-state consumption from the resource constraint (`ex_18_5_consumption`).
-/

namespace Miao.SearchAndMatching

open MeasureTheory Filter Topology

/-- **Exercise 18.3** (Miao, p. 614): a mean-preserving spread does not lower steady-state
tightness. `(θ, c)` is the steady state for `G = μ`, `(θ′, c′)` for `G′ = μ′`, and
`Φ_μ ≤ Φ_{μ′}` pointwise. If moreover `Φ_μ(c) < Φ_{μ′}(c)`, tightness rises strictly. -/
theorem ex_18_3_theta {μ μ' : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ}
    {β ρx η κ A b θ θ' c c' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1)
    (hη0 : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hA : 0 < A) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hθ : 0 < θ) (hθ' : 0 < θ')
    (hmps : ∀ x, jd_Phi μ x ≤ jd_Phi μ' x)
    (hC : jd_JC μ q β η κ A θ c) (hD : jd_JD μ β ρx η κ A b θ c)
    (hC' : jd_JC μ' q β η κ A θ' c') (hD' : jd_JD μ' β ρx η κ A b θ' c') :
    θ ≤ θ' ∧ (jd_Phi μ c < jd_Phi μ' c → θ < θ') := by
  unfold jd_JC at hC hC'
  unfold jd_JD at hD hD'
  have hK : 0 < β * (1 - η) * A := mul_pos (mul_pos hβ0 (by linarith)) hA
  have hk0 : 0 ≤ β * (1 - ρx) := mul_nonneg hβ0.le (by linarith)
  have hk1 : β * (1 - ρx) < 1 := by nlinarith
  have hc1 : 0 < (1 - η) * A := mul_pos (by linarith) hA
  have hq := hqpos θ hθ
  have hq' := hqpos θ' hθ'
  -- JD in the form `η θ κ + (1 − η) b = (1 − η) A h(c)`
  have eD : η * θ * κ + (1 - η) * b = (1 - η) * A * (c + β * (1 - ρx) * jd_Phi μ c) := by
    rw [hD]; ring
  have eD' : η * θ' * κ + (1 - η) * b = (1 - η) * A * (c' + β * (1 - ρx) * jd_Phi μ' c') := by
    rw [hD']; ring
  have hh := jd_h_strictMono hint hk0 hk1
  have hηκ : 0 < η * κ := mul_pos hη0 hκ
  have hweak : θ ≤ θ' := by
    by_contra hne
    have hlt : θ' < θ := not_le.mp hne
    have hqq : q θ < q θ' := hqanti (Set.mem_Ioi.mpr hθ') (Set.mem_Ioi.mpr hθ) hlt
    have h1 : κ / q θ' < κ / q θ := div_lt_div_of_pos_left hκ hq hqq
    rw [hC, hC'] at h1
    have h2 : jd_Phi μ' c' < jd_Phi μ c := lt_of_mul_lt_mul_left h1 hK.le
    have hcc : c < c' := by
      by_contra h3
      have := jd_Phi_antitone hint (not_lt.mp h3)
      linarith [hmps c']
    have h4 := hh hcc
    beta_reduce at h4
    have h5 : c' + β * (1 - ρx) * jd_Phi μ c' ≤ c' + β * (1 - ρx) * jd_Phi μ' c' := by
      have := mul_le_mul_of_nonneg_left (hmps c') hk0; linarith
    have : η * θ * κ < η * θ' * κ := by nlinarith
    nlinarith
  refine ⟨hweak, fun hstr => ?_⟩
  rcases hweak.lt_or_eq with h | h
  · exact h
  · exfalso
    subst h
    have hPP : jd_Phi μ' c' = jd_Phi μ c := by
      have : β * (1 - η) * A * jd_Phi μ' c' = β * (1 - η) * A * jd_Phi μ c := by
        rw [← hC, ← hC']
      exact mul_left_cancel₀ hK.ne' this
    have hhh : c' + β * (1 - ρx) * jd_Phi μ' c' = c + β * (1 - ρx) * jd_Phi μ c := by
      have : (1 - η) * A * (c' + β * (1 - ρx) * jd_Phi μ' c') =
          (1 - η) * A * (c + β * (1 - ρx) * jd_Phi μ c) := by rw [← eD, ← eD']
      exact mul_left_cancel₀ hc1.ne' this
    rw [hPP] at hhh
    have hcc : c' = c := by linarith
    rw [hcc] at hPP
    linarith

/-- **Exercise 18.3** (Miao, p. 614): combining (18.44) and (18.45),
`(1 − η)(A z̄* − b) = H(θ) := η θ κ − (1 − ρˣ) κ / q(θ)` for every `G`, so across two steady
states `(1 − η) A (z̄*′ − z̄*) = H(θ′) − H(θ)`. -/
theorem ex_18_3_reservation {μ μ' : Measure ℝ} {q : ℝ → ℝ} {β ρx η κ A b θ θ' c c' : ℝ}
    (hC : jd_JC μ q β η κ A θ c) (hD : jd_JD μ β ρx η κ A b θ c)
    (hC' : jd_JC μ' q β η κ A θ' c') (hD' : jd_JD μ' β ρx η κ A b θ' c') :
    (1 - η) * A * (c' - c) =
      (η * θ' * κ - (1 - ρx) * κ / q θ') - (η * θ * κ - (1 - ρx) * κ / q θ) := by
  unfold jd_JC at hC hC'
  unfold jd_JD at hD hD'
  have e : ∀ x, (1 - ρx) * κ / q x = (1 - ρx) * (κ / q x) := fun x => by ring
  rw [e, e, hC, hC']
  linarith

/-- **Exercise 18.3** (Miao, p. 614): if `H(θ) = η θ κ − (1 − ρˣ) κ / q(θ)` is nondecreasing on
`(0, ∞)`, a mean-preserving spread raises the reservation productivity (more job destruction). -/
theorem ex_18_3_reservation_mono {μ μ' : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ}
    {β ρx η κ A b θ θ' c c' : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hθ : 0 < θ) (hθ' : 0 < θ')
    (hmps : ∀ x, jd_Phi μ x ≤ jd_Phi μ' x)
    (hH : MonotoneOn (fun x => η * x * κ - (1 - ρx) * κ / q x) (Set.Ioi 0))
    (hC : jd_JC μ q β η κ A θ c) (hD : jd_JD μ β ρx η κ A b θ c)
    (hC' : jd_JC μ' q β η κ A θ' c') (hD' : jd_JD μ' β ρx η κ A b θ' c') : c ≤ c' := by
  have hθθ := (ex_18_3_theta (μ' := μ') hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hqpos hqanti hθ hθ' hmps
    hC hD hC' hD').1
  have e := ex_18_3_reservation hC hD hC' hD'
  have hm := hH (Set.mem_Ioi.mpr hθ) (Set.mem_Ioi.mpr hθ') hθθ
  beta_reduce at hm
  have hc1 : 0 < (1 - η) * A := mul_pos (by linarith) hA
  have : 0 ≤ (1 - η) * A * (c' - c) := by rw [e]; linarith
  by_contra hne
  have := mul_neg_of_pos_of_neg hc1 (by linarith [not_le.mp hne] : c' - c < 0)
  linarith

/-- **Exercise 18.3** (Miao, p. 614): steady-state unemployment `u = ρ/(ρ + q(θ)θ)` falls after the
spread if the separation rate does not rise and tightness rises strictly (`θ q(θ)` strictly
increasing). -/
theorem ex_18_3_unemployment {q : ℝ → ℝ} {ρ ρ' θ θ' : ℝ}
    (hf : StrictMonoOn (fun x => x * q x) (Set.Ioi 0)) (hθ : 0 < θ) (hθθ : θ < θ')
    (hqθ : 0 ≤ θ * q θ) (hρ : 0 < ρ) (hρ' : 0 ≤ ρ') (hρρ : ρ' ≤ ρ) :
    ρ' / (ρ' + θ' * q θ') < ρ / (ρ + θ * q θ) := by
  have := hf (Set.mem_Ioi.mpr hθ) (Set.mem_Ioi.mpr (lt_trans hθ hθθ)) hθθ
  beta_reduce at this
  exact jd_compstat_kappaA_u hρ hρ' hρρ hqθ this

/-- **Exercise 18.3** (a concrete mean-preserving spread): `G′ = ½ δ_{1/2} + ½ δ_{3/2}` spreads
`G = δ₁`: same total mass and mean, and `Φ_G ≤ Φ_{G′}` pointwise. -/
theorem jd_mps_example :
    let μ' : Measure ℝ := (1 / 2 : ENNReal) • Measure.dirac (1 / 2 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac (3 / 2 : ℝ)
    μ' Set.univ = 1 ∧ ∫ z, z ∂μ' = 1 ∧ ∀ c, jd_Phi (Measure.dirac 1) c ≤ jd_Phi μ' c := by
  intro μ'
  have hint : ∀ f : ℝ → ℝ, Integrable f μ' := by
    intro f
    refine Integrable.add_measure ?_ ?_
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
  have hI : ∀ f : ℝ → ℝ, ∫ z, f z ∂μ' = 1 / 2 * f (1 / 2) + 1 / 2 * f (3 / 2) := by
    intro f
    rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
      integral_dirac]
    · simp
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
  have _ := hint
  refine ⟨?_, ?_, fun c => ?_⟩
  · simp only [μ', Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [ENNReal.add_halves]
  · rw [hI]; norm_num
  · unfold jd_Phi
    rw [hI, integral_dirac]
    apply max_le
    · have h1 := le_max_left (1 / 2 - c) 0
      have h2 := le_max_left (3 / 2 - c) 0
      linarith
    · have h1 := le_max_right (1 / 2 - c) 0
      have h2 := le_max_right (3 / 2 - c) 0
      linarith

/-- **Exercise 18.4** (Miao, p. 614): the planner's objective at a node of the §18.3 model.
Controls are next-period capital `K′` and vacancies `v`; consumption comes from the resource
constraint `C = F(K, A N) + (1 − δ) K − κ v − K′` and employment evolves by
`N′ = (1 − ρ) N + M(1 − N, v)`. -/
noncomputable def jd_plannerObj {S : Type*} [Fintype S] (u : ℝ → ℝ) (p : S → ℝ)
    (W : S → ℝ → ℝ → ℝ) (F M : ℝ → ℝ → ℝ) (β δ χ φ ρ κ A K N K' v : ℝ) : ℝ :=
  u (F K (A * N) + (1 - δ) * K - κ * v - K') - χ * N ^ (1 + φ) / (1 + φ) +
    β * ∑ s, p s * W s K' ((1 - ρ) * N + M (1 - N) v)

/-- **Exercise 18.4** (Miao, p. 614): the planner's first-order condition for capital,
`Λ_t = β E_t ∂W_{t+1}/∂K_{t+1}`. -/
theorem ex_18_4_foc_K {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {W : S → ℝ → ℝ → ℝ}
    {F M : ℝ → ℝ → ℝ} {Wv : ℝ → ℝ → ℝ} {β δ χ φ ρ κ A K₀ N₀ K₁ v₀ Λ : ℝ} {WK : S → ℝ}
    (hmax : ∀ K N K' v, jd_plannerObj u p W F M β δ χ φ ρ κ A K N K' v ≤ Wv K N)
    (hopt : jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v₀ = Wv K₀ N₀)
    (hu : HasDerivAt u Λ (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - K₁))
    (hWK : ∀ s, HasDerivAt (fun k => W s k ((1 - ρ) * N₀ + M (1 - N₀) v₀)) (WK s) K₁) :
    Λ = β * ∑ s, p s * WK s := by
  have hin : HasDerivAt (fun k => F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - k) (-1) K₁ := by
    simpa using (hasDerivAt_id K₁).const_sub (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀)
  have hsum : HasDerivAt (fun k => ∑ s, p s * W s k ((1 - ρ) * N₀ + M (1 - N₀) v₀))
      (∑ s, p s * WK s) K₁ := HasDerivAt.fun_sum fun s _ => (hWK s).const_mul (p s)
  have hd := ((hu.comp K₁ hin).sub_const (χ * N₀ ^ (1 + φ) / (1 + φ))).add (hsum.const_mul β)
  have := jd_foc (h := fun k => jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ k v₀)
    (fun k => (hmax K₀ N₀ k v₀).trans hopt.ge) hd
  linarith

/-- **Exercise 18.4** (Miao, p. 614): the planner's first-order condition for vacancies,
`κ Λ_t = M_v(u_t, v_t) β E_t ∂W_{t+1}/∂N_{t+1}`. -/
theorem ex_18_4_foc_v {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {W : S → ℝ → ℝ → ℝ}
    {F M : ℝ → ℝ → ℝ} {Wv : ℝ → ℝ → ℝ} {β δ χ φ ρ κ A K₀ N₀ K₁ v₀ Λ Mv : ℝ} {WN : S → ℝ}
    (hmax : ∀ K N K' v, jd_plannerObj u p W F M β δ χ φ ρ κ A K N K' v ≤ Wv K N)
    (hopt : jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v₀ = Wv K₀ N₀)
    (hu : HasDerivAt u Λ (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - K₁))
    (hMv : HasDerivAt (fun y => M (1 - N₀) y) Mv v₀)
    (hWN : ∀ s, HasDerivAt (fun n => W s K₁ n) (WN s) ((1 - ρ) * N₀ + M (1 - N₀) v₀)) :
    κ * Λ = Mv * (β * ∑ s, p s * WN s) := by
  have hin : HasDerivAt (fun v => F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v - K₁) (-κ) v₀ := by
    simpa using (((hasDerivAt_id v₀).const_mul κ).const_sub
      (F K₀ (A * N₀) + (1 - δ) * K₀)).sub_const K₁
  have hin2 : HasDerivAt (fun v => (1 - ρ) * N₀ + M (1 - N₀) v) Mv v₀ :=
    hMv.const_add ((1 - ρ) * N₀)
  have hsum : HasDerivAt (fun v => ∑ s, p s * W s K₁ ((1 - ρ) * N₀ + M (1 - N₀) v))
      (∑ s, p s * (WN s * Mv)) v₀ :=
    HasDerivAt.fun_sum fun s _ => ((hWN s).comp_of_eq v₀ hin2 (by ring)).const_mul (p s)
  have hd := ((hu.comp v₀ hin).sub_const (χ * N₀ ^ (1 + φ) / (1 + φ))).add (hsum.const_mul β)
  have := jd_foc (h := fun v => jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v)
    (fun v => (hmax K₀ N₀ K₁ v).trans hopt.ge) hd
  have e : ∑ s, p s * (WN s * Mv) = Mv * ∑ s, p s * WN s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e] at this
  linarith

/-- **Exercise 18.4** (Miao, p. 614): the planner's envelope condition for capital,
`∂W_t/∂K_t = Λ_t (F₁(K_t, A_t N_t) + 1 − δ)`. -/
theorem ex_18_4_envelope_K {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ}
    {W : S → ℝ → ℝ → ℝ} {F M : ℝ → ℝ → ℝ} {Wv : ℝ → ℝ → ℝ}
    {β δ χ φ ρ κ A K₀ N₀ K₁ v₀ Λ F₁ WK₀ : ℝ}
    (hmax : ∀ K N K' v, jd_plannerObj u p W F M β δ χ φ ρ κ A K N K' v ≤ Wv K N)
    (hopt : jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v₀ = Wv K₀ N₀)
    (hu : HasDerivAt u Λ (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - K₁))
    (hF₁ : HasDerivAt (fun k => F k (A * N₀)) F₁ K₀) (hW : HasDerivAt (fun k => Wv k N₀) WK₀ K₀) :
    WK₀ = Λ * (F₁ + 1 - δ) := by
  have hin : HasDerivAt (fun k => F k (A * N₀) + (1 - δ) * k - κ * v₀ - K₁) (F₁ + (1 - δ)) K₀ := by
    simpa using ((hF₁.add ((hasDerivAt_id K₀).const_mul (1 - δ))).sub_const (κ * v₀)).sub_const K₁
  have hd := ((hu.comp K₀ hin).sub_const (χ * N₀ ^ (1 + φ) / (1 + φ))).add_const
    (β * ∑ s, p s * W s K₁ ((1 - ρ) * N₀ + M (1 - N₀) v₀))
  have := jd_envelope (g := fun k => jd_plannerObj u p W F M β δ χ φ ρ κ A k N₀ K₁ v₀)
    (fun k => hmax k N₀ K₁ v₀) hopt hW hd
  rw [this]
  ring

/-- **Exercise 18.4** (Miao, p. 614): the planner's Euler equation
`Λ_t = β E_t[Λ_{t+1}(F₁(K_{t+1}, A_{t+1} N_{t+1}) + 1 − δ)]`, identical to (18.49) with
`R_k = F₁` (18.51). -/
theorem ex_18_4_euler {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {W : S → ℝ → ℝ → ℝ}
    {F M : ℝ → ℝ → ℝ} {Wv : ℝ → ℝ → ℝ} {β δ χ φ ρ κ A K₀ N₀ K₁ v₀ Λ : ℝ}
    {WK Λn F₁n : S → ℝ}
    (hmax : ∀ K N K' v, jd_plannerObj u p W F M β δ χ φ ρ κ A K N K' v ≤ Wv K N)
    (hopt : jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v₀ = Wv K₀ N₀)
    (hu : HasDerivAt u Λ (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - K₁))
    (hWK : ∀ s, HasDerivAt (fun k => W s k ((1 - ρ) * N₀ + M (1 - N₀) v₀)) (WK s) K₁)
    (henv : ∀ s, WK s = Λn s * (F₁n s + 1 - δ)) :
    Λ = β * ∑ s, p s * (Λn s * (F₁n s + 1 - δ)) := by
  rw [ex_18_4_foc_K hmax hopt hu hWK]
  simp only [henv]

/-- **Exercise 18.4** (Miao, p. 614): the planner's envelope condition for employment,
`∂W_t/∂N_t = Λ_t A_t F₂ − χ N_t^φ + (1 − ρ − M_u) β E_t ∂W_{t+1}/∂N_{t+1}`. -/
theorem ex_18_4_envelope_N {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ}
    {W : S → ℝ → ℝ → ℝ} {F M : ℝ → ℝ → ℝ} {Wv : ℝ → ℝ → ℝ}
    {β δ χ φ ρ κ A K₀ N₀ K₁ v₀ Λ F₂ Mu WN₀ : ℝ} {WN : S → ℝ} (hφ : 0 < φ) (hN : 0 < N₀)
    (hmax : ∀ K N K' v, jd_plannerObj u p W F M β δ χ φ ρ κ A K N K' v ≤ Wv K N)
    (hopt : jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v₀ = Wv K₀ N₀)
    (hu : HasDerivAt u Λ (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - K₁))
    (hF₂ : HasDerivAt (F K₀) F₂ (A * N₀)) (hMu : HasDerivAt (fun x => M x v₀) Mu (1 - N₀))
    (hWN : ∀ s, HasDerivAt (fun n => W s K₁ n) (WN s) ((1 - ρ) * N₀ + M (1 - N₀) v₀))
    (hW : HasDerivAt (fun n => Wv K₀ n) WN₀ N₀) :
    WN₀ = Λ * (A * F₂) - χ * N₀ ^ φ + (1 - ρ - Mu) * (β * ∑ s, p s * WN s) := by
  have hAN : HasDerivAt (fun n => A * n) A N₀ := by simpa using (hasDerivAt_id N₀).const_mul A
  have hin : HasDerivAt (fun n => F K₀ (A * n) + (1 - δ) * K₀ - κ * v₀ - K₁) (F₂ * A) N₀ :=
    (((hF₂.comp N₀ hAN).add_const ((1 - δ) * K₀)).sub_const (κ * v₀)).sub_const K₁
  have h1N : HasDerivAt (fun n : ℝ => 1 - n) (-1) N₀ := by
    simpa using (hasDerivAt_id N₀).const_sub 1
  have hMN : HasDerivAt (fun n => M (1 - n) v₀) (Mu * (-1)) N₀ := hMu.comp N₀ h1N
  have hin2 : HasDerivAt (fun n => (1 - ρ) * n + M (1 - n) v₀) ((1 - ρ) + Mu * (-1)) N₀ := by
    have := ((hasDerivAt_id N₀).const_mul (1 - ρ)).add hMN
    exact this.congr_deriv (by ring)
  have hsum : HasDerivAt (fun n => ∑ s, p s * W s K₁ ((1 - ρ) * n + M (1 - n) v₀))
      (∑ s, p s * (WN s * ((1 - ρ) + Mu * (-1)))) N₀ :=
    HasDerivAt.fun_sum fun s _ => ((hWN s).comp_of_eq N₀ hin2 (by ring)).const_mul (p s)
  have hd := ((hu.comp_of_eq N₀ hin (by ring)).sub
    (jd_disutility_hasDerivAt (χ := χ) hφ hN)).add (hsum.const_mul β)
  have := jd_envelope (g := fun n => jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ n K₁ v₀)
    (fun n => hmax K₀ n K₁ v₀) hopt hW hd
  rw [this]
  have e : ∑ s, p s * (WN s * ((1 - ρ) + Mu * (-1))) = (1 - ρ - Mu) * ∑ s, p s * WN s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  ring

/-- **Exercise 18.4** (Miao, p. 614): with the planner's surplus `S^P_t = (∂W_t/∂N_t)/Λ_t`,
`m = β Λ_{t+1}/Λ_t` and `∂W_{t+1}/∂N_{t+1} = Λ_{t+1} S^P_{t+1}`, the planner's job creation
condition is `κ / M_v = E_t[m S^P_{t+1}]` and
`S^P_t = A_t F₂ − χ N_t^φ/Λ_t + (1 − ρ − M_u) κ / M_v`. -/
theorem ex_18_4_surplus {S : Type*} [Fintype S] {p Λn SPn WN : S → ℝ}
    {β χ φ ρ κ A F₂ N₀ Λ Mu Mv WN₀ : ℝ} (hΛ : Λ ≠ 0) (hMv : Mv ≠ 0)
    (hfoc : κ * Λ = Mv * (β * ∑ s, p s * WN s))
    (henv : WN₀ = Λ * (A * F₂) - χ * N₀ ^ φ + (1 - ρ - Mu) * (β * ∑ s, p s * WN s))
    (hnext : ∀ s, WN s = Λn s * SPn s) :
    κ / Mv = ∑ s, p s * (β * Λn s / Λ * SPn s) ∧
      WN₀ / Λ = A * F₂ - χ * N₀ ^ φ / Λ + (1 - ρ - Mu) * (κ / Mv) := by
  have e : ∑ s, p s * (β * Λn s / Λ * SPn s) = (β * ∑ s, p s * WN s) / Λ := by
    rw [Finset.mul_sum, Finset.sum_div]; congr 1; funext s; rw [hnext]; field_simp
  have h1 : κ / Mv = (β * ∑ s, p s * WN s) / Λ := by
    field_simp; linarith
  refine ⟨by rw [e, h1], ?_⟩
  rw [h1, henv]
  field_simp

/-- **Exercise 18.4** (Miao, p. 614): for `M(u, v) = v q(v/u)` and `θ = v/u`,
`∂M/∂v = q(θ) + θ q′(θ) = q(θ)(1 − ξ(θ))`, `ξ = −θ q′/q`. -/
theorem jd_matching_partial_v {q : ℝ → ℝ} {u v q' : ℝ} (hu : 0 < u)
    (hq : HasDerivAt q q' (v / u)) :
    HasDerivAt (fun y => y * q (y / u)) (q (v / u) + v / u * q') v := by
  have hin : HasDerivAt (fun y => y / u) (1 / u) v := by
    simpa using (hasDerivAt_id v).div_const u
  have := (hasDerivAt_id v).mul (hq.comp v hin)
  exact this.congr_deriv (by simp only [Function.comp_apply, id_eq]; field_simp)

/-- **Exercise 18.4** (Miao, p. 614): for `M(u, v) = v q(v/u)`,
`∂M/∂u = −θ² q′(θ) = ξ(θ) θ q(θ)`. -/
theorem jd_matching_partial_u {q : ℝ → ℝ} {u v q' : ℝ} (hu : 0 < u)
    (hq : HasDerivAt q q' (v / u)) :
    HasDerivAt (fun x => v * q (v / x)) (-(v / u) ^ 2 * q') u := by
  have hin : HasDerivAt (fun x => v / x) (-(v / u ^ 2)) u := by
    have := (hasDerivAt_inv hu.ne').const_mul v
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp
  have := (hq.comp u hin).const_mul v
  exact this.congr_deriv (by field_simp)

/-- **Exercise 18.4** (efficiency gap, Miao, pp. 599, 614). At a node, with `M_v = q (1 − ξ)`,
`M_u = ξ θ q`, the decentralised firm surplus (18.54) under the wage (18.56),
`S^F = (1 − η)(A F₂ − b − χ N^φ/Λ) − η κ θ + (1 − ρ) κ / q`, and the planner's surplus
`S^P = A F₂ − χ N^φ/Λ + (1 − ρ − M_u) κ / M_v` satisfy
`S^F − (1 − η) S^P = −(1 − η) b + (η − ξ) κ ((1 − ρ)/q − θ)/(1 − ξ)`. -/
theorem ex_18_4_gap {η ξ ρ κ θ q b y : ℝ} (hq : q ≠ 0) (hξ : ξ ≠ 1) :
    ((1 - η) * (y - b) - η * κ * θ + (1 - ρ) * κ / q) -
      (1 - η) * (y + (1 - ρ - ξ * θ * q) * κ / (q * (1 - ξ))) =
      -(1 - η) * b + (η - ξ) * κ * ((1 - ρ) / q - θ) / (1 - ξ) := by
  have h1 : (1 - ξ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hξ)
  field_simp
  ring

/-- **Exercise 18.4: the Hosios condition** (Miao, pp. 599, 614). With `b = 0` and `η = ξ`
(constant elasticity, e.g. Cobb–Douglas matching), the decentralised firm surplus is `(1 − η)`
times the planner's surplus at every node, so the decentralised job creation condition (18.55),
`κ / q = E_t[m S^F_{t+1}]`, holds iff the planner's, `κ / M_v = E_t[m S^P_{t+1}]` with
`M_v = q (1 − η)`. -/
theorem ex_18_4_hosios {S : Type*} [Fintype S] {p m SFn SPn : S → ℝ} {η q κ : ℝ}
    (hη1 : η < 1) (hq : q ≠ 0) (hrel : ∀ s, SFn s = (1 - η) * SPn s) :
    κ / q = ∑ s, p s * (m s * SFn s) ↔ κ / (q * (1 - η)) = ∑ s, p s * (m s * SPn s) := by
  have h1 : (1 - η) ≠ 0 := by linarith
  have e : ∑ s, p s * (m s * SFn s) = (1 - η) * ∑ s, p s * (m s * SPn s) := by
    rw [Finset.mul_sum]; congr 1; funext s; rw [hrel]; ring
  rw [e]
  constructor
  · intro h
    rw [div_mul_eq_div_div, h]
    field_simp
  · intro h
    rw [div_mul_eq_div_div] at h
    rw [← h]
    field_simp

/-- **Exercise 18.4** (Miao, p. 614): the node identity behind `ex_18_4_hosios`: with `b = 0` and
`ξ = η`, `S^F = (1 − η) S^P`. -/
theorem ex_18_4_surplus_hosios {η ρ κ θ q y : ℝ} (hq : q ≠ 0) (hη : η ≠ 1) :
    (1 - η) * (y - 0) - η * κ * θ + (1 - ρ) * κ / q =
      (1 - η) * (y + (1 - ρ - η * θ * q) * κ / (q * (1 - η))) := by
  have := ex_18_4_gap (η := η) (ξ := η) (ρ := ρ) (κ := κ) (θ := θ) (b := 0) (y := y) hq hη
  simp only [sub_self, zero_mul, zero_div, mul_zero, add_zero] at this
  linarith

/-- **Exercise 18.4** (Miao, p. 614; analogue of (18.18)): in a steady state of the decentralised
§18.3 economy (`m = β` in (18.55), wage (18.56)), with `a = A F₂` and `h = χ N^φ/Λ`:
`κ / q(θ) (1 − β(1 − ρ)) + β η κ θ = β (1 − η)(a − h − b)`. -/
theorem ex_18_4_ss_decentralised {β ρ κ η θ q w b a h SF : ℝ}
    (h55 : κ / q = β * SF) (h54 : SF = a - w + (1 - ρ) * κ / q)
    (h56 : w = (1 - η) * (b + h) + η * (a + κ * θ)) :
    κ / q * (1 - β * (1 - ρ)) + β * η * κ * θ = β * (1 - η) * (a - h - b) := by
  rw [h54, h56] at h55
  have e : (1 - ρ) * κ / q = (1 - ρ) * (κ / q) := by ring
  rw [e] at h55
  linear_combination h55

/-- **Exercise 18.4** (Miao, p. 614; analogue of (18.28)): in a steady state of the planner's
problem (`m = β`), with `M_v = q (1 − ξ)`, `M_u = ξ θ q`, `a = A F₂`, `h = χ N^φ/Λ`:
`κ / q(θ) (1 − β(1 − ρ)) + β ξ κ θ = β (1 − ξ)(a − h)`. -/
theorem ex_18_4_ss_planner {β ρ κ ξ θ q a h SP : ℝ} (hq : q ≠ 0) (hξ : ξ ≠ 1)
    (hjc : κ / (q * (1 - ξ)) = β * SP)
    (hsp : SP = a - h + (1 - ρ - ξ * θ * q) * (κ / (q * (1 - ξ)))) :
    κ / q * (1 - β * (1 - ρ)) + β * ξ * κ * θ = β * (1 - ξ) * (a - h) := by
  have h1 : (1 - ξ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hξ)
  rw [hsp] at hjc
  have e : κ / (q * (1 - ξ)) = κ / q / (1 - ξ) := by rw [div_mul_eq_div_div]
  rw [e] at hjc
  linear_combination (norm := (field_simp; ring)) (1 - ξ) * hjc

/-- **Exercise 18.4** (Miao, pp. 599, 614): with `b = 0`, the decentralised and planner's
steady-state tightness equations (`ex_18_4_ss_decentralised`, `ex_18_4_ss_planner`) differ by
`β (η − ξ)(κ θ + y)`, `y = a − h`: they coincide when `η = ξ` (Hosios), and if both hold with
`κ θ + y ≠ 0`, `β > 0`, then `η = ξ`. -/
theorem ex_18_4_ss_hosios {β ρ κ η ξ θ q y : ℝ} :
    (η = ξ → (κ / q * (1 - β * (1 - ρ)) + β * η * κ * θ = β * (1 - η) * (y - 0) ↔
      κ / q * (1 - β * (1 - ρ)) + β * ξ * κ * θ = β * (1 - ξ) * y)) ∧
    (0 < β → κ * θ + y ≠ 0 →
      κ / q * (1 - β * (1 - ρ)) + β * η * κ * θ = β * (1 - η) * (y - 0) →
      κ / q * (1 - β * (1 - ρ)) + β * ξ * κ * θ = β * (1 - ξ) * y → η = ξ) := by
  refine ⟨fun h => by rw [h, sub_zero], fun hβ hne h1 h2 => ?_⟩
  have : β * ((η - ξ) * (κ * θ + y)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h3 | h3
  · linarith
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exact absurd h4 hne

/-- **Exercise 18.5** (Miao, p. 614): in a deterministic steady state the Euler equation (18.49),
`1 = β (R + 1 − δ)`, gives the rental rate `R = 1/β − 1 + δ`. -/
theorem ex_18_5_rental {β δ R : ℝ} (hβ : 0 < β) (h49 : 1 = β * (R + 1 - δ)) :
    R = 1 / β - 1 + δ := by
  field_simp
  linarith

/-- **Exercise 18.5** (Miao, p. 614): steady-state employment (18.48) with job-finding rate
`f = q(θ) θ`: `N = (1 − ρ) N + f (1 − N)` iff `N = f/(ρ + f)`, and then `u = ρ/(ρ + f)`. -/
theorem ex_18_5_employment {ρ f N : ℝ} (hpos : 0 < ρ + f) :
    N = (1 - ρ) * N + f * (1 - N) ↔ N = f / (ρ + f) ∧ 1 - N = ρ / (ρ + f) := by
  constructor
  · intro h
    constructor
    · field_simp; linarith
    · field_simp; linarith
  · intro ⟨h, _⟩
    rw [h]
    field_simp
    ring

/-- **Exercise 18.5** (Miao, p. 614): targets for unemployment `u ∈ (0, 1)` and the job-finding
rate `f` pin down the separation rate `ρ = f u /(1 − u)` (steady state of (18.48)). -/
theorem ex_18_5_rho {ρ f u : ℝ} (hu1 : u < 1) :
    1 - u = (1 - ρ) * (1 - u) + f * u ↔ ρ = f * u / (1 - u) := by
  have : (1 - u) ≠ 0 := by linarith
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp; ring

/-- **Exercise 18.5** (Miao, p. 614): given a target `θ` and `y = A F₂ − χ N^φ/Λ`, the
steady-state tightness equation of `ex_18_4_ss_decentralised` determines the posting cost
uniquely: `κ = β (1 − η)(y − b) / ((1 − β(1 − ρ))/q(θ) + β η θ)`. -/
theorem ex_18_5_kappa {β ρ η θ q y b κ : ℝ}
    (hden : (1 - β * (1 - ρ)) / q + β * η * θ ≠ 0) :
    κ / q * (1 - β * (1 - ρ)) + β * η * κ * θ = β * (1 - η) * (y - b) ↔
      κ = β * (1 - η) * (y - b) / ((1 - β * (1 - ρ)) / q + β * η * θ) := by
  rw [eq_div_iff hden]
  have e : κ / q * (1 - β * (1 - ρ)) + β * η * κ * θ =
      κ * ((1 - β * (1 - ρ)) / q + β * η * θ) := by ring
  rw [e]

/-- **Exercise 18.5** (Miao, p. 614): steady-state consumption from the resource constraint,
`C = F(K, A N) − δ K − κ v` with `v = θ u`. -/
theorem ex_18_5_consumption {C K Y δ κ v θ u : ℝ} (hv : v = θ * u)
    (hrc : C + K - (1 - δ) * K = Y - κ * v) : C = Y - δ * K - κ * θ * u := by
  rw [hv] at hrc
  linarith

end Miao.SearchAndMatching

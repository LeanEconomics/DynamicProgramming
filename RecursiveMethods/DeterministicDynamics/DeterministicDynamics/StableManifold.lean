/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.LyapunovPerron
import DeterministicDynamics.LocalStability

/-!
# The stable manifold (Theorem 6.6)

SLP §6.3, p. 147. Let `h(x̄) = x̄`, with `h` strictly differentiable at `x̄` with Jacobian `A`
(this holds if `h` is continuously differentiable near `x̄`), and let `m` of the characteristic
roots of `A` lie inside the unit circle. Then there are a neighborhood `U` of `x̄` and a map `φ`,
differentiable at `x̄` with derivative the projection `Q_u` onto `E_u` along `E_s` (rank
`n − m`), such that every solution of `x_{t+1} = h(x_t)` with `x₀ ∈ U` and `φ(x₀) = 0` converges
to `x̄` (`theorem_6_6`). The book also asks for `φ` to be continuously differentiable; the
construction gives differentiability at `x̄`, which is what the rank condition is about.

The proof follows the dichotomy of `Dichotomy` and the Lyapunov–Perron construction of
`LyapunovPerron`. Write `h(x̄ + z) = x̄ + Az + r(z)`.

* `exists_lip_remainder`: strict differentiability makes `r` `ε`-Lipschitz near `0`, for every
  `ε > 0`; the Lipschitz extension to `ℝⁿ` (`LipschitzOnWith.extend_pi`) keeps the constant.
* With `ψ(ξ) = Q_u z₀(ξ)` the unstable part of the solution through `P_sξ`, set
  `φ(x) = Q_u(x − x̄) − ψ(P_s(x − x̄))`. If `φ(x₀) = 0` then `x₀ − x̄ = z₀(ξ)`, so the orbit of
  `x₀` is `x̄ + z_t → x̄`. And `‖ψ(ξ)‖ ≤ 2K²cε'‖ξ‖/(1 − cγ)` with `ε'` the Lipschitz constant of `r`
  near `0`, which tends to `0`: `ψ(ξ) = o(ξ)`, so `Dφ(x̄) = Q_u`.
-/

open Set Filter Topology Module Asymptotics
open scoped Matrix NNReal

namespace StokeyLucasPrescott.DeterministicDynamics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `A` as a continuous linear map. -/
noncomputable def clmOf (A : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

theorem clmOf_apply (A : Matrix ι ι ℝ) (z : ι → ℝ) : clmOf A z = A *ᵥ z := rfl

theorem invB_pow_mem (A : Matrix ι ι ℝ) (k : ℕ) {v : ι → ℝ}
    (hv : v ∈ unstableR A) : (invB A ^ k) *ᵥ v ∈ unstableR A := by
  induction k with
  | zero => simpa using hv
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact inv_mem A ih

/-- The dichotomy of `A` is `LPData`. -/
theorem lpData_of (A : Matrix ι ι ℝ) {K a c γ : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a)
    (haγ : a < γ) (hc : 0 < c) (hcγ : c * γ < 1)
    (hA : ∀ k z, ‖(A ^ k) *ᵥ projS A z‖ ≤ K * a ^ k * ‖z‖)
    (hB : ∀ k z, ‖(invB A ^ k) *ᵥ projU A z‖ ≤ K * c ^ k * ‖z‖) :
    LPData A (invB A) (projS A) (projU A) K a c γ where
  PQ := projS_add_projU A
  PP z := projS_of_mem A (projS_mem A z)
  PB k z := projS_of_mem_unstable A (invB_pow_mem A _ (projU_mem A z))
  AB k z := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact inv_right A (invB_pow_mem A k (projU_mem A z))
  K_nn := hK
  a_nn := ha
  aγ := haγ
  c_pos := hc
  cγ := hcγ
  bA := hA
  bB := hB

/-- The remainder `r(z) = h(x̄ + z) − x̄ − Az` is `ε`-Lipschitz near `0`. -/
theorem exists_lip_remainder {h : (ι → ℝ) → (ι → ℝ)} {xbar : ι → ℝ}
    {A : Matrix ι ι ℝ} (hA : HasStrictFDerivAt h (clmOf A) xbar) {ε : ℝ}
    (hε : 0 < ε) : ∃ ρ > 0, ∀ z ∈ Metric.closedBall (0 : ι → ℝ) ρ,
      ∀ z' ∈ Metric.closedBall (0 : ι → ℝ) ρ,
        ‖(h (xbar + z) - xbar - A *ᵥ z) - (h (xbar + z') - xbar - A *ᵥ z')‖ ≤ ε * ‖z - z'‖ := by
  obtain ⟨s, hs, happ⟩ := hA.approximates_deriv_on_nhds (c := ⟨ε, hε.le⟩) (Or.inr hε)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hs
  refine ⟨ρ / 2, by linarith, fun z hz z' hz' => ?_⟩
  have hmem : ∀ v ∈ Metric.closedBall (0 : ι → ℝ) (ρ / 2), xbar + v ∈ s := fun v hv =>
    hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      rw [Metric.mem_closedBall, dist_zero_right] at hv
      linarith)
  have := happ _ (hmem z hz) _ (hmem z' hz')
  have e : (h (xbar + z) - xbar - A *ᵥ z) - (h (xbar + z') - xbar - A *ᵥ z') =
      h (xbar + z) - h (xbar + z') - clmOf A (xbar + z - (xbar + z')) := by
    simp only [clmOf, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply,
      add_sub_add_left_eq_sub, Matrix.mulVec_sub]
    abel
  rw [e]
  simp only [add_sub_add_left_eq_sub, map_sub] at this ⊢
  exact this

/-- **Theorem 6.6 (stable manifold).** -/
theorem theorem_6_6 {n : ℕ} {h : (Fin n → ℝ) → (Fin n → ℝ)} {xbar : Fin n → ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hfix : h xbar = xbar)
    (hA : HasStrictFDerivAt h (matCLM A) xbar) :
    ∃ U ∈ 𝓝 xbar, ∃ φ : (Fin n → ℝ) → (Fin n → ℝ), φ xbar = 0 ∧
      HasFDerivAt φ (LinearMap.toContinuousLinearMap (projU A)) xbar ∧
      finrank ℝ (LinearMap.range (projU A)) =
        n - ((A.charpoly.map Complex.ofRealHom).roots.filter fun μ => ‖μ‖ < 1).card ∧
      ∀ x₀ ∈ U, φ x₀ = 0 → Tendsto (fun t => h^[t] x₀) atTop (𝓝 xbar) := by
  -- the dichotomy constants
  obtain ⟨a, ha0, ha1, Ks, hKs0, hKs⟩ := stable_bound A
  set γ := (a + 1) / 2
  have hγ0 : 0 < γ := by simp only [γ]; linarith
  have haγ : a < γ := by simp only [γ]; linarith
  have hγ1 : γ < 1 := by simp only [γ]; linarith
  set c := (1 + γ⁻¹) / 2
  have hγi : 1 < γ⁻¹ := (one_lt_inv₀ hγ0).2 hγ1
  have hc1 : 1 < c := by simp only [c]; linarith
  have hcγ : c * γ < 1 := by
    simp only [c]; rw [div_mul_eq_mul_div, add_mul, inv_mul_cancel₀ hγ0.ne']; linarith
  obtain ⟨Ku, hKu0, hKu⟩ := unstable_bound A hc1
  set K := max Ks Ku
  have hK0 : 0 ≤ K := le_max_of_le_left hKs0
  have hD : LPData A (invB A) (projS A) (projU A) K a c γ :=
    lpData_of A hK0 ha0.le haγ (by linarith) hcγ
      (fun k z => (hKs k z).trans (by
        have := mul_nonneg (pow_nonneg ha0.le k) (norm_nonneg z)
        nlinarith [le_max_left Ks Ku]))
      (fun k z => (hKu k z).trans (by
        have := mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ c) k) (norm_nonneg z)
        nlinarith [le_max_right Ks Ku]))
  have hP : ∀ v, ‖projS A v‖ ≤ K * ‖v‖ := fun v => by simpa using hD.bA 0 v
  set Λ := 1 / (γ - a) + c / (1 - c * γ)
  have hΛ : 0 < Λ := by
    have : 0 < γ - a := by linarith
    have : 0 < 1 - c * γ := by linarith
    positivity
  set ε := 1 / (2 * (K * Λ + 1))
  have hε : 0 < ε := by positivity
  have hsmall : K * ε * Λ ≤ 1 / 2 := by
    have e : K * ε * Λ = K * Λ / (2 * (K * Λ + 1)) := by simp only [ε]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hK0 hΛ.le]
  -- the remainder and its Lipschitz extension
  set r : (Fin n → ℝ) → (Fin n → ℝ) := fun z => h (xbar + z) - xbar - A *ᵥ z
  have hr0 : r 0 = 0 := by simp [r, hfix]
  obtain ⟨ρ, hρ, hlip⟩ := exists_lip_remainder (A := A) hA hε
  have hlipOn : LipschitzOnWith (Real.toNNReal ε) r (Metric.closedBall 0 ρ) :=
    LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hε.le]
      exact hlip z hz z' hz'
  obtain ⟨rt, hrt, hrteq⟩ := hlipOn.extend_pi
  have hrt0 : rt 0 = 0 := by rw [← hrteq (Metric.mem_closedBall_self hρ.le), hr0]
  have hrtl : ∀ x y, ‖rt x - rt y‖ ≤ ε * ‖x - y‖ := fun x y => by
    have := hrt.dist_le_mul x y
    rwa [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hε.le] at this
  -- the Lyapunov–Perron solutions
  have hLP := fun ξ => lyapunov_perron hD hε.le hrt0 hrtl hsmall ξ
  choose Z hZrec hZP hZb hZQ hZrep using hLP
  set ψ : (Fin n → ℝ) → (Fin n → ℝ) := fun ξ => projU A (Z ξ 0)
  set φ : (Fin n → ℝ) → (Fin n → ℝ) := fun x => projU A (x - xbar) - ψ (projS A (x - xbar))
  have hZ0 : Z 0 0 = 0 := by
    have := hZb 0 0
    simp only [norm_zero, mul_zero, zero_mul] at this
    exact norm_le_zero_iff.1 this
  have hφ0 : φ xbar = 0 := by simp [φ, ψ, hZ0]
  -- the solution through a point of the manifold is the orbit
  have horbit : ∀ x₀, φ x₀ = 0 → 2 * K * ‖projS A (x₀ - xbar)‖ ≤ ρ → ∀ t,
      h^[t] x₀ = xbar + Z (projS A (x₀ - xbar)) t := by
    intro x₀ hφx hsm t
    set ξ := projS A (x₀ - xbar)
    have hZ0' : Z ξ 0 = x₀ - xbar := by
      have h1 : projS A (Z ξ 0) = projS A (x₀ - xbar) := by
        rw [hZP ξ, hD.PP]
      have h2 : projU A (Z ξ 0) = projU A (x₀ - xbar) := by
        simp only [φ, ψ, sub_eq_zero] at hφx; exact hφx.symm
      rw [← projS_add_projU A (Z ξ 0), h1, h2, projS_add_projU]
    have hin : ∀ t, Z ξ t ∈ Metric.closedBall 0 ρ := fun t => by
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (hZb ξ t).trans ?_
      have := pow_le_one₀ hγ0.le hγ1.le (n := t)
      have := mul_nonneg hK0 (norm_nonneg ξ)
      nlinarith
    induction t with
    | zero => simp [hZ0']
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih, hZrec, ← hrteq (hin t)]
      simp only [r]; abel
  refine ⟨Metric.ball xbar (ρ / (2 * K ^ 2 + 1)), Metric.ball_mem_nhds _ (by positivity), φ,
    hφ0, ?_, ?_, fun x₀ hx₀ hφx => ?_⟩
  · -- `Dφ(x̄) = Q_u`: `ψ(ξ) = o(ξ)`
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine isLittleO_iff.2 fun η hη => ?_
    set ε' := η * (1 - c * γ) / (2 * K ^ 3 * c + 1)
    have hε' : 0 < ε' := by
      have : 0 < 1 - c * γ := by linarith
      have : 0 < c := by linarith
      positivity
    obtain ⟨ρ', hρ', hlip'⟩ := exists_lip_remainder (A := A) hA hε'
    set δ := min ρ ρ' / (2 * K ^ 2 + 1)
    have hδ : 0 < δ := by positivity
    filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℝ) hδ] with v hv
    rw [Metric.mem_ball, dist_zero_right] at hv
    set ξ := projS A v
    have hξ : ‖ξ‖ ≤ K * ‖v‖ := hP v
    have hKξ : 2 * K * ‖ξ‖ ≤ min ρ ρ' := by
      have h1 : 2 * K * ‖ξ‖ ≤ 2 * K ^ 2 * ‖v‖ := by nlinarith
      have h2 : 2 * K ^ 2 * ‖v‖ ≤ min ρ ρ' := by
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * K ^ 2 + 1)).1 hv
        nlinarith [norm_nonneg v, min_le_left ρ ρ']
      linarith
    have hin : ∀ j, Z ξ j ∈ Metric.closedBall 0 ρ ∩ Metric.closedBall 0 ρ' := fun j => by
      have := (hZb ξ j).trans (by
        have := pow_le_one₀ hγ0.le hγ1.le (n := j)
        have := mul_nonneg hK0 (norm_nonneg ξ)
        nlinarith : 2 * K * ‖ξ‖ * γ ^ j ≤ min ρ ρ')
      exact ⟨by rw [Metric.mem_closedBall, dist_zero_right]; linarith [min_le_left ρ ρ'],
        by rw [Metric.mem_closedBall, dist_zero_right]; linarith [min_le_right ρ ρ']⟩
    have hrb : ∀ j, ‖rt (Z ξ j)‖ ≤ (ε' * (2 * K * ‖ξ‖)) * γ ^ j := fun j => by
      rw [← hrteq (hin j).1]
      have := hlip' _ (hin j).2 0 (Metric.mem_closedBall_self hρ'.le)
      simp only [add_zero, hfix, sub_self, Matrix.mulVec_zero, sub_zero] at this
      refine this.trans ?_
      have := mul_le_mul_of_nonneg_left (hZb ξ j) hε'.le
      linarith [show ε' * (2 * K * ‖ξ‖ * γ ^ j) = ε' * (2 * K * ‖ξ‖) * γ ^ j by ring]
    have hψ := hZQ ξ _ hrb
    have e : φ (xbar + v) - φ xbar - (LinearMap.toContinuousLinearMap (projU A)) v = -ψ ξ := by
      rw [show φ (xbar + v) = projU A v - ψ ξ by simp only [φ, ξ, add_sub_cancel_left], hφ0]
      simp only [LinearMap.coe_toContinuousLinearMap', sub_zero]
      abel
    rw [e, norm_neg]
    refine hψ.trans ?_
    have hcγ' : 0 < 1 - c * γ := by linarith
    rw [div_le_iff₀ hcγ']
    have : K * c * (ε' * (2 * K * ‖ξ‖)) ≤ K * c * (ε' * (2 * K * (K * ‖v‖))) := by
      have : 0 ≤ K * c * ε' * (2 * K) := by have := hε'.le; positivity
      nlinarith
    have hε'def : ε' * (2 * K ^ 3 * c + 1) = η * (1 - c * γ) := by
      simp only [ε']; field_simp
    nlinarith [norm_nonneg v, mul_nonneg hε'.le (norm_nonneg v)]
  · -- the rank
    rw [projU, Submodule.range_projection]
    have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_stableR_unstableR A)
    rw [finrank_stableR, Module.finrank_fin_fun] at h1
    omega
  · -- convergence on the manifold
    rw [Metric.mem_ball, dist_eq_norm] at hx₀
    have hsm : 2 * K * ‖projS A (x₀ - xbar)‖ ≤ ρ := by
      have h1 := hP (x₀ - xbar)
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * K ^ 2 + 1)).1 hx₀
      nlinarith [norm_nonneg (x₀ - xbar)]
    have hob := horbit x₀ hφx hsm
    simp only [hob]
    have hz : Tendsto (fun t => Z (projS A (x₀ - xbar)) t) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun t => hZb _ t) ?_
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0.le hγ1).const_mul
        (2 * K * ‖projS A (x₀ - xbar)‖)
    simpa using hz.const_add xbar

/-- **The local stable family.** The solutions `z(ξ)` through `P_sξ` decay geometrically, are
orbits of `h` for small `ξ`, and their unstable parts at `t = 0` depend on `ξ` with Lipschitz
constant as small as we like near `0`. -/
theorem local_stable_family {h : (ι → ℝ) → (ι → ℝ)} {xbar : ι → ℝ} {A : Matrix ι ι ℝ}
    (hfix : h xbar = xbar) (hA : HasStrictFDerivAt h (clmOf A) xbar) :
    ∃ γ, 0 < γ ∧ γ < 1 ∧ ∃ C, 0 ≤ C ∧ ∃ δ > 0, ∃ Z : (ι → ℝ) → ℕ → ι → ℝ,
      (∀ ξ, projS A (Z ξ 0) = projS A ξ) ∧ (∀ ξ t, ‖Z ξ t‖ ≤ C * ‖ξ‖ * γ ^ t) ∧
      (∀ ξ, ‖ξ‖ ≤ δ → ∀ t, h^[t] (xbar + Z ξ 0) = xbar + Z ξ t) ∧
      ∀ η > 0, ∃ δ' > 0, ∀ ξ ξ', ‖ξ‖ ≤ δ' → ‖ξ'‖ ≤ δ' →
        ‖projU A (Z ξ 0) - projU A (Z ξ' 0)‖ ≤ η * ‖ξ - ξ'‖ := by
  obtain ⟨a, ha0, ha1, Ks, hKs0, hKs⟩ := stable_bound A
  set γ := (a + 1) / 2
  have hγ0 : 0 < γ := by simp only [γ]; linarith
  have haγ : a < γ := by simp only [γ]; linarith
  have hγ1 : γ < 1 := by simp only [γ]; linarith
  set c := (1 + γ⁻¹) / 2
  have hγi : 1 < γ⁻¹ := (one_lt_inv₀ hγ0).2 hγ1
  have hc1 : 1 < c := by simp only [c]; linarith
  have hcγ : c * γ < 1 := by
    simp only [c]; rw [div_mul_eq_mul_div, add_mul, inv_mul_cancel₀ hγ0.ne']; linarith
  obtain ⟨Ku, hKu0, hKu⟩ := unstable_bound A hc1
  set K := max Ks Ku
  have hK0 : 0 ≤ K := le_max_of_le_left hKs0
  have hD : LPData A (invB A) (projS A) (projU A) K a c γ :=
    lpData_of A hK0 ha0.le haγ (by linarith) hcγ
      (fun k z => (hKs k z).trans (by
        have := mul_nonneg (pow_nonneg ha0.le k) (norm_nonneg z)
        nlinarith [le_max_left Ks Ku]))
      (fun k z => (hKu k z).trans (by
        have := mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ c) k) (norm_nonneg z)
        nlinarith [le_max_right Ks Ku]))
  set Λ := 1 / (γ - a) + c / (1 - c * γ)
  have hΛ : 0 < Λ := by
    have : 0 < γ - a := by linarith
    have : 0 < 1 - c * γ := by linarith
    positivity
  set ε := 1 / (2 * (K * Λ + 1))
  have hε : 0 < ε := by positivity
  have hsmall : K * ε * Λ ≤ 1 / 2 := by
    have e : K * ε * Λ = K * Λ / (2 * (K * Λ + 1)) := by simp only [ε]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hK0 hΛ.le]
  set r : (ι → ℝ) → (ι → ℝ) := fun z => h (xbar + z) - xbar - A *ᵥ z
  have hr0 : r 0 = 0 := by simp [r, hfix]
  obtain ⟨ρ, hρ, hlip⟩ := exists_lip_remainder (A := A) hA hε
  have hlipOn : LipschitzOnWith (Real.toNNReal ε) r (Metric.closedBall 0 ρ) :=
    LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hε.le]
      exact hlip z hz z' hz'
  obtain ⟨rt, hrt, hrteq⟩ := hlipOn.extend_pi
  have hrt0 : rt 0 = 0 := by rw [← hrteq (Metric.mem_closedBall_self hρ.le), hr0]
  have hrtl : ∀ x y, ‖rt x - rt y‖ ≤ ε * ‖x - y‖ := fun x y => by
    have := hrt.dist_le_mul x y
    rwa [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hε.le] at this
  have hLP := fun ξ => lyapunov_perron hD hε.le hrt0 hrtl hsmall ξ
  choose Z hZrec hZP hZb hZQ hZrep using hLP
  have hball : ∀ ξ t {R : ℝ}, 2 * K * ‖ξ‖ ≤ R → Z ξ t ∈ Metric.closedBall 0 R := fun ξ t R hR => by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (hZb ξ t).trans ?_
    have := pow_le_one₀ hγ0.le hγ1.le (n := t)
    have := mul_nonneg hK0 (norm_nonneg ξ)
    nlinarith
  refine ⟨γ, hγ0, hγ1, 2 * K, by positivity, ρ / (2 * K + 1), by positivity, Z,
    hZP, hZb, fun ξ hξ t => ?_, fun η hη => ?_⟩
  · -- orbits
    have hsm : 2 * K * ‖ξ‖ ≤ ρ := by
      rw [le_div_iff₀ (by positivity)] at hξ
      nlinarith [norm_nonneg ξ]
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih, hZrec, ← hrteq (hball ξ t hsm)]
      simp only [r]; abel
  · -- small Lipschitz constant
    have hcγ' : 0 < 1 - c * γ := by linarith
    set ε' := η * (1 - c * γ) / (2 * K ^ 2 * c + 1)
    have hε' : 0 < ε' := by
      have : 0 < c := by linarith
      positivity
    obtain ⟨ρ', hρ', hlip'⟩ := exists_lip_remainder (A := A) hA hε'
    refine ⟨min ρ ρ' / (2 * K + 1), by positivity, fun ξ ξ' hξ hξ' => ?_⟩
    have hsm : ∀ ζ : ι → ℝ, ‖ζ‖ ≤ min ρ ρ' / (2 * K + 1) → 2 * K * ‖ζ‖ ≤ min ρ ρ' :=
      fun ζ hζ => by
        rw [le_div_iff₀ (by positivity)] at hζ
        nlinarith [norm_nonneg ζ]
    have hin : ∀ ζ : ι → ℝ, ‖ζ‖ ≤ min ρ ρ' / (2 * K + 1) → ∀ j,
        Z ζ j ∈ Metric.closedBall 0 ρ ∧ Z ζ j ∈ Metric.closedBall 0 ρ' := fun ζ hζ j =>
      ⟨hball ζ j ((hsm ζ hζ).trans (min_le_left _ _)),
        hball ζ j ((hsm ζ hζ).trans (min_le_right _ _))⟩
    set Cm := 2 * K * max ‖ξ‖ ‖ξ'‖
    have hb1 : ∀ t, ‖Z ξ t‖ ≤ Cm * γ ^ t := fun t => (hZb ξ t).trans (by
      have := pow_nonneg hγ0.le t
      have := le_max_left ‖ξ‖ ‖ξ'‖
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * K)
      nlinarith)
    have hb2 : ∀ t, ‖Z ξ' t‖ ≤ Cm * γ ^ t := fun t => (hZb ξ' t).trans (by
      have := pow_nonneg hγ0.le t
      have := le_max_right ‖ξ‖ ‖ξ'‖
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * K)
      nlinarith)
    obtain ⟨hL1, hL2⟩ := lp_lipschitz hD hε.le hrt0 hrtl hsmall hb1 hb2 (hZrep ξ) (hZrep ξ')
    have hM : ∀ j, ‖rt (Z ξ j) - rt (Z ξ' j)‖ ≤ (ε' * (2 * K * ‖ξ - ξ'‖)) * γ ^ j := fun j => by
      rw [← hrteq (hin ξ hξ j).1, ← hrteq (hin ξ' hξ' j).1]
      refine (hlip' _ (hin ξ hξ j).2 _ (hin ξ' hξ' j).2).trans ?_
      have := mul_le_mul_of_nonneg_left (hL1 j) hε'.le
      linarith [show ε' * (2 * K * ‖ξ - ξ'‖ * γ ^ j) = ε' * (2 * K * ‖ξ - ξ'‖) * γ ^ j by ring]
    refine (hL2 _ hM).trans ?_
    rw [div_le_iff₀ hcγ']
    have hε'def : ε' * (2 * K ^ 2 * c + 1) = η * (1 - c * γ) := by
      simp only [ε']; field_simp
    have : 0 ≤ ε' * ‖ξ - ξ'‖ := mul_nonneg hε'.le (norm_nonneg _)
    nlinarith

end StokeyLucasPrescott.DeterministicDynamics

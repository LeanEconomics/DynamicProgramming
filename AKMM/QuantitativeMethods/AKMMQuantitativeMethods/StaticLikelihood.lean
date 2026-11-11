/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMQuantitativeMethods.StaticModel
import StructuralEstimation.MLLikelihood
import Mathlib.Probability.Independence.Basic

/-!
# Structural estimation of the static model

AKMM, §8.7, (8.19)–(8.20) and the likelihood, pp. 231–232.

* **(8.19)–(8.20)**: for `0 < G < y`, (8.2)–(8.3) hold iff `A = y(1 − G/y)^{1/(1+ψ)}` and
  `η = (G/y)/(γ(1 − G/y))` (`eq_8_19_8_20`); the map `(A, η) ↦ (y, G)` is a bijection of the
  positive quadrant onto `{0 < G < y}` with this inverse (`sl_bijection`).
* **The likelihood**: for discretely distributed independent shocks, the probability of observing
  `(y, G)` is `p_A(A)p_η(η)` at the shocks given by (8.19)–(8.20) (`sl_likelihood_discrete`), and
  the log likelihood of a sample is the sum of the logs (`sl_loglik`).
* **Correction**: for densities, the density of `(y, G)` carries the Jacobian of
  `(y, G) ↦ (A, η)`. Its partial derivatives and determinant
  `(1 − s)^{1/(1+ψ) − 2}/(γy)`, `s = G/y`, are computed (`sl_jacobian`); the determinant depends on
  `ψ` (`sl_jacobian_depends_on_psi`), so the printed `Prob(G, y | ψ, γ) = p_A(A)p_η(η)` is not
  the likelihood of `(y, G)` (the change-of-variables formula itself is not formalised).
* **The implied multiplier** (p. 232): by Miao's invariance theorem, the multiplier
  `(1+γ)/(1+γ+ψ)` at the maximum-likelihood estimate maximises the profile likelihood of the
  multiplier (`sl_multiplier_mle`).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory ProbabilityTheory

/-- **(8.19)–(8.20)** (AKMM, p. 232): for `0 < G < y` and `γ > 0`, (8.2) and (8.3) hold iff
`A = y(1 − G/y)^{1/(1+ψ)}` and `η = (G/y)/(γ(1 − G/y))`. -/
theorem eq_8_19_8_20 {ψ γ η A y G : ℝ} (hγ : 0 < γ) (hy : 0 < y) (hG : 0 < G)
    (hGy : G < y) :
    (y = A * (1 - G / y) ^ (-(1 + ψ)⁻¹) ∧ G = γ * η / (1 + γ * η) * y) ↔
      (A = y * (1 - G / y) ^ (1 + ψ)⁻¹ ∧ η = G / y / (γ * (1 - G / y))) := by
  have hs1 : 0 < 1 - G / y := by rw [sub_pos, div_lt_one hy]; exact hGy
  have hs0 : 0 < G / y := div_pos hG hy
  have hGs : G = G / y * y := by field_simp
  set s := G / y with hs_def
  set R := (1 - s) ^ (1 + ψ)⁻¹ with hR_def
  have hR : 0 < R := Real.rpow_pos_of_pos hs1 _
  have hneg : (1 - s) ^ (-(1 + ψ)⁻¹) = R⁻¹ := Real.rpow_neg hs1.le _
  rw [hneg]
  refine and_congr ?_ ?_
  · constructor
    · intro h; rw [h]; field_simp
    · intro h; rw [h]; field_simp
  · rw [hGs]
    constructor
    · intro h
      have h' : s = γ * η / (1 + γ * η) := mul_right_cancel₀ hy.ne' h
      have h1 : 1 + γ * η ≠ 0 := by
        intro h0; rw [h0, div_zero] at h'; linarith
      have h2 : s * (1 + γ * η) = γ * η := by rw [h']; field_simp
      rw [eq_div_iff (by positivity)]
      linear_combination -h2
    · intro h
      have hX : 1 + γ * η = (1 - s)⁻¹ := by
        rw [h]; field_simp; ring
      rw [hX, h]
      field_simp

/-- **The shocks are recovered from the data** (AKMM, p. 232): `(A, η) ↦ (y*, G*)` maps the
positive quadrant into `{0 < G < y}`, and (8.19)–(8.20) invert it. -/
theorem sl_bijection {ψ γ A η : ℝ} (hγ : 0 < γ) (hA : 0 < A) (hη : 0 < η) :
    0 < sm_Gstar ψ γ η A ∧ sm_Gstar ψ γ η A < sm_ystar ψ γ η A ∧
      A = sm_ystar ψ γ η A * (1 - sm_Gstar ψ γ η A / sm_ystar ψ γ η A) ^ (1 + ψ)⁻¹ ∧
      η = sm_Gstar ψ γ η A / sm_ystar ψ γ η A /
        (γ * (1 - sm_Gstar ψ γ η A / sm_ystar ψ γ η A)) := by
  have hγη : 0 < γ * η := mul_pos hγ hη
  have hy : 0 < sm_ystar ψ γ η A := by unfold sm_ystar; positivity
  have hG : 0 < sm_Gstar ψ γ η A := (sm_star_feasible (ψ := ψ) hγη hA).2.1
  have hGy : sm_Gstar ψ γ η A < sm_ystar ψ γ η A := by
    rw [(sm_ystar_eq (ψ := ψ) (A := A) hγη).2]
    have : γ * η / (1 + γ * η) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  have h := (sm_equilibrium_unique (ψ := ψ) (A := A) hγη hy (G := sm_Gstar ψ γ η A)).2
    ⟨rfl, rfl⟩
  obtain ⟨h1, h2⟩ := (eq_8_19_8_20 hγ hy hG hGy).1 h
  exact ⟨hG, hGy, h1, h2⟩

/-- **The likelihood of an observation** (AKMM, p. 232), for discrete shocks: if
`y = y*(A, η)` and `G = G*(A, η)` pointwise, `A, η > 0`, and `A`, `η` are independent, then for
data `0 < G₀ < y₀`, `Pr(y = y₀, G = G₀) = Pr(A = A₀)·Pr(η = η₀)` with `(A₀, η₀)` given by
(8.19)–(8.20) at `(y₀, G₀)`. -/
theorem sl_likelihood_discrete {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ψ γ : ℝ} (hγ : 0 < γ) {A η y G : Ω → ℝ}
    (hApos : ∀ ω, 0 < A ω) (hηpos : ∀ ω, 0 < η ω)
    (hy : ∀ ω, y ω = sm_ystar ψ γ (η ω) (A ω)) (hG : ∀ ω, G ω = sm_Gstar ψ γ (η ω) (A ω))
    (hind : IndepFun A η μ) {y0 G0 : ℝ} (hy0 : 0 < y0) (hG0 : 0 < G0) (hGy0 : G0 < y0) :
    μ {ω | y ω = y0 ∧ G ω = G0} =
      μ {ω | A ω = y0 * (1 - G0 / y0) ^ (1 + ψ)⁻¹} *
        μ {ω | η ω = G0 / y0 / (γ * (1 - G0 / y0))} := by
  have hset : {ω | y ω = y0 ∧ G ω = G0} =
      A ⁻¹' {y0 * (1 - G0 / y0) ^ (1 + ψ)⁻¹} ∩ η ⁻¹' {G0 / y0 / (γ * (1 - G0 / y0))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    obtain ⟨-, -, h1, h2⟩ := sl_bijection hγ (hApos ω) (hηpos ω)
    rw [hy, hG]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨h1, h2⟩
    · rintro ⟨hA0, hη0⟩
      have h82 := (eq_8_19_8_20 hγ hy0 hG0 hGy0 (A := A ω) (η := η ω)).2 ⟨hA0, hη0⟩
      have hγη : 0 < γ * η ω := mul_pos hγ (hηpos ω)
      obtain ⟨e1, e2⟩ := (sm_equilibrium_unique (ψ := ψ) (A := A ω) hγη hy0).1 h82
      exact ⟨e1.symm, e2.symm⟩
  rw [hset]
  exact hind.measure_inter_preimage_eq_mul _ _ (MeasurableSet.singleton _)
    (MeasurableSet.singleton _)

/-- **The sample likelihood** (AKMM, p. 232): with positive likelihoods, the log of
`∏ₜ p_A(Aₜ)p_η(ηₜ)` is `Σₜ (log p_A(Aₜ) + log p_η(ηₜ))`. -/
theorem sl_loglik {T : ℕ} (pA pη : ℝ → ℝ) (A η : ℕ → ℝ) (hA : ∀ t, 0 < pA (A t))
    (hη : ∀ t, 0 < pη (η t)) :
    Real.log (∏ t ∈ Finset.range T, (pA (A t) * pη (η t))) =
      ∑ t ∈ Finset.range T, (Real.log (pA (A t)) + Real.log (pη (η t))) := by
  rw [Real.log_prod (fun t _ => (mul_pos (hA t) (hη t)).ne')]
  exact Finset.sum_congr rfl fun t _ => Real.log_mul (hA t).ne' (hη t).ne'

/-- **The Jacobian of (8.19)–(8.20)** (AKMM, p. 232, corrected): at `0 < G < y`, with
`s = G/y` and `q = 1/(1+ψ)`, the map `(y, G) ↦ (A, η)` has partial derivatives
`∂A/∂y = (1−s)^q + qs(1−s)^{q−1}`, `∂A/∂G = −q(1−s)^{q−1}`, `∂η/∂y = −s/(γy(1−s)²)`,
`∂η/∂G = 1/(γy(1−s)²)`, and Jacobian determinant `(1−s)^q/(γy(1−s)²)`. The density of `(y, G)` is
`p_A(A)p_η(η)` times this determinant, not `p_A(A)p_η(η)` as printed. -/
theorem sl_jacobian {ψ γ y G : ℝ} (hγ : 0 < γ) (hy : 0 < y) (hG : 0 < G)
    (hGy : G < y) :
    HasDerivAt (fun y' => y' * (1 - G / y') ^ (1 + ψ)⁻¹)
      ((1 - G / y) ^ (1 + ψ)⁻¹ + (1 + ψ)⁻¹ * (G / y) * (1 - G / y) ^ ((1 + ψ)⁻¹ - 1)) y ∧
    HasDerivAt (fun G' => y * (1 - G' / y) ^ (1 + ψ)⁻¹)
      (-((1 + ψ)⁻¹ * (1 - G / y) ^ ((1 + ψ)⁻¹ - 1))) G ∧
    HasDerivAt (fun y' => G / y' / (γ * (1 - G / y')))
      (-(G / y / (γ * y * (1 - G / y) ^ 2))) y ∧
    HasDerivAt (fun G' => G' / y / (γ * (1 - G' / y))) (1 / (γ * y * (1 - G / y) ^ 2)) G ∧
    ((1 - G / y) ^ (1 + ψ)⁻¹ + (1 + ψ)⁻¹ * (G / y) * (1 - G / y) ^ ((1 + ψ)⁻¹ - 1)) *
        (1 / (γ * y * (1 - G / y) ^ 2)) -
      (-((1 + ψ)⁻¹ * (1 - G / y) ^ ((1 + ψ)⁻¹ - 1))) * (-(G / y / (γ * y * (1 - G / y) ^ 2))) =
      (1 - G / y) ^ (1 + ψ)⁻¹ / (γ * y * (1 - G / y) ^ 2) := by
  set q := (1 + ψ)⁻¹ with hq
  have hs : 0 < 1 - G / y := by rw [sub_pos, div_lt_one hy]; exact hGy
  have hyG : 0 < y - G := by linarith
  have hq1 : (1 - G / y) ^ (q - 1) = (1 - G / y) ^ q / (1 - G / y) := Real.rpow_sub_one hs.ne' q
  -- `∂A/∂y`
  have hin : HasDerivAt (fun y' : ℝ => 1 - G / y') (G / y ^ 2) y := by
    have := ((hasDerivAt_inv hy.ne').const_mul G).const_sub 1
    convert this using 1
    · funext y'; simp [div_eq_mul_inv]
    · field_simp
  have hAy := (hasDerivAt_id y).mul (hin.rpow_const (p := q) (Or.inl hs.ne'))
  -- `∂A/∂G`
  have hinG : HasDerivAt (fun G' : ℝ => 1 - G' / y) (-(1 / y)) G := by
    have := ((hasDerivAt_id G).div_const y).const_sub 1
    convert this using 1
    simp
  have hAG := (hinG.rpow_const (p := q) (Or.inl hs.ne')).const_mul y
  -- `∂η/∂y`: near `y`, `η = G/(γ(y' − G))`
  have hηy0 : HasDerivAt (fun y' => G / (γ * (y' - G))) (-(G * γ) / (γ * (y - G)) ^ 2) y := by
    have h1 : HasDerivAt (fun y' => γ * (y' - G)) γ y := by
      simpa using ((hasDerivAt_id y).sub_const G).const_mul γ
    have := (h1.inv (by positivity)).const_mul G
    convert this using 1
    · funext y'; simp [div_eq_mul_inv]
    · ring
  have hηy : HasDerivAt (fun y' => G / y' / (γ * (1 - G / y')))
      (-(G * γ) / (γ * (y - G)) ^ 2) y := by
    refine hηy0.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hy] with y' hy'
    rcases eq_or_ne (y' - G) 0 with h | h
    · rw [show y' = G by linarith]
      simp [div_self hG.ne']
    · field_simp
  -- `∂η/∂G`
  have hηG0 : HasDerivAt (fun G' => G' / (γ * (y - G'))) (y / (γ * (y - G) ^ 2)) G := by
    have h1 : HasDerivAt (fun G' => γ * (y - G')) (-γ) G := by
      simpa using ((hasDerivAt_id G).const_sub y).const_mul γ
    have := (hasDerivAt_id G).div h1 (by positivity)
    convert this using 1
    · rfl
    · simp only [id]; field_simp; ring
  have hηG : HasDerivAt (fun G' => G' / y / (γ * (1 - G' / y))) (y / (γ * (y - G) ^ 2)) G := by
    refine hηG0.congr_of_eventuallyEq ?_
    filter_upwards with G'
    rcases eq_or_ne (y - G') 0 with h | h
    · rw [show G' = y by linarith]
      simp [div_self hy.ne']
    · field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert hAy using 1
    · rfl
    · rw [hq1, id_eq]
      field_simp
  · convert hAG using 1
    field_simp
  · convert hηy using 1
    field_simp
  · convert hηG using 1
    field_simp
  · rw [hq1]
    field_simp
    ring

/-- **The Jacobian depends on `ψ`** (AKMM, p. 232): at `y = 1`, `G = 1/2`, `γ = 1` the
determinant `(1−s)^q/(γy(1−s)²)` differs between `ψ = 1` and `ψ = 3`, so omitting it changes the
likelihood as a function of `ψ`. -/
theorem sl_jacobian_depends_on_psi :
    (1 - (1 / 2 : ℝ) / 1) ^ ((1 + (1 : ℝ))⁻¹) / (1 * 1 * (1 - (1 / 2 : ℝ) / 1) ^ 2) ≠
      (1 - (1 / 2 : ℝ) / 1) ^ ((1 + (3 : ℝ))⁻¹) / (1 * 1 * (1 - (1 / 2 : ℝ) / 1) ^ 2) := by
  intro h
  have hpos : (0 : ℝ) < 1 * 1 * (1 - (1 / 2 : ℝ) / 1) ^ 2 := by norm_num
  rw [div_left_inj' hpos.ne'] at h
  have : (1 - (1 / 2 : ℝ) / 1) ^ ((1 + (1 : ℝ))⁻¹) < (1 - (1 / 2 : ℝ) / 1) ^ ((1 + (3 : ℝ))⁻¹) :=
    Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- **The implied multiplier** (AKMM, p. 232): "once we have estimated the parameters, we can
differentiate (8.2) to find the implied fiscal multiplier". For any likelihood `L` on
`θ = (ψ, γ)` maximised at `θ̂`, the multiplier `m(θ) = (1+γ)/(1+γ+ψ)` (Appendix 8.A.2 at
`η̄ = 1`) at `θ̂` maximises the profile likelihood of the multiplier (Miao's invariance
theorem `ml_invariance_profile`). -/
theorem sl_multiplier_mle (L : ℝ × ℝ → ℝ) (θhat : ℝ × ℝ) (hmax : ∀ θ, L θ ≤ L θhat) :
    Miao.StructuralEstimation.ml_profileLikelihood L (fun θ => (1 + θ.2) / (1 + θ.2 + θ.1))
        ((1 + θhat.2) / (1 + θhat.2 + θhat.1)) = L θhat ∧
      ∀ m ∈ Set.range (fun θ : ℝ × ℝ => (1 + θ.2) / (1 + θ.2 + θ.1)),
        Miao.StructuralEstimation.ml_profileLikelihood L
          (fun θ => (1 + θ.2) / (1 + θ.2 + θ.1)) m ≤
        Miao.StructuralEstimation.ml_profileLikelihood L
          (fun θ => (1 + θ.2) / (1 + θ.2 + θ.1)) ((1 + θhat.2) / (1 + θhat.2 + θhat.1)) :=
  Miao.StructuralEstimation.ml_invariance_profile L _ θhat hmax

end AKMM.QuantitativeMethods

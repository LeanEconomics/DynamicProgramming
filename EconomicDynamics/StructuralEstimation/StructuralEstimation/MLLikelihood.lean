/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Maximum likelihood: likelihood, score, information matrix equality, Cramér–Rao

Miao, §12.2, pp. 396–399. Observations `x₁, …, x_T` are drawn i.i.d. from `f(·, θ)`.

* `ml_likelihood`, `ml_logLikelihood`: `L(θ | x) = ∏ₜ f(xₜ, θ)` and `ln L = ∑ₜ ln f(xₜ, θ)`;
  `eq_ml_log_likelihood` (p. 396): `ln L = ∑ₜ ln f(xₜ, θ)` when `f > 0`;
  `ml_isMaxOn_likelihood_iff`: maximising `L` and maximising `ln L` are the same problem.
* `ml_first_order_condition` (p. 397): at an interior maximiser `∑ₜ ∂ ln f(xₜ, θ̂)/∂θ = 0`, i.e.
  the ML estimator sets the sample mean of the GMM moment `h(x, θ) = ∂ ln f(x, θ)/∂θ` to zero.
* `ml_score_mean_zero` (p. 397, the population moment condition `E[∂ ln f(x, θ)/∂θ] = 0`),
  `ml_information_matrix_equality` (p. 398, `−E[∂² ln f/∂θ²] = E[(∂ ln f/∂θ)²]`) and
  `ml_cramer_rao` (p. 398, the Cramér–Rao bound `Var_θ(δ) · I(θ) ≥ g′(θ)²` for an unbiased
  estimator `δ` of `g(θ)`), for a model on a finite sample space with a scalar parameter.
  `ml_cramer_rao_bernoulli`: one coin toss attains the bound with equality.
* `ml_invariance`, `ml_invariance_profile` (p. 398, invariance): `c(θ̂)` maximises the induced
  (profile) likelihood `γ ↦ sup {L(θ) : c(θ) = γ}`; no differentiability of `c` is needed.
* `ml_gaussian_tests_equal` (pp. 398–399): in the Gaussian location model with known variance
  and `H₀ : μ = μ₀`, the likelihood-ratio, Wald and Lagrange multiplier statistics all equal
  `T(x̄ − μ₀)²/σ²`.

Departures. The book states the information matrix equality and the Cramér–Rao bound for a
vector parameter and a general density, without conditions; here they are proved for a
scalar parameter and a finite sample space, where differentiating `∑ₓ f(x, θ) = 1` under the
sum is automatic. The asymptotic statements (consistency, asymptotic normality, efficiency,
the χ² limits of the three tests) are listed in the book "without explicitly stating relevant
conditions and proofs"; they are proved for the models of Exercises 12.1 and 12.2 in
`MLExercises`.
-/

namespace Miao.StructuralEstimation

open Real

/-- The likelihood of an i.i.d. sample, Miao p. 396: `L(θ | x₁, …, x_T) = ∏ₜ f(xₜ, θ)`. -/
noncomputable def ml_likelihood {X Θ : Type*} (f : X → Θ → ℝ) {T : ℕ} (x : Fin T → X)
    (θ : Θ) : ℝ :=
  ∏ t, f (x t) θ

/-- The log-likelihood, Miao p. 396: `∑ₜ ln f(xₜ, θ)`. -/
noncomputable def ml_logLikelihood {X Θ : Type*} (f : X → Θ → ℝ) {T : ℕ} (x : Fin T → X)
    (θ : Θ) : ℝ :=
  ∑ t, Real.log (f (x t) θ)

/-- Miao, p. 396: the logarithm of the likelihood is the log-likelihood
`ln L(θ | x) = ∑ₜ ln f(xₜ, θ)` (for a positive density). -/
theorem eq_ml_log_likelihood {X Θ : Type*} (f : X → Θ → ℝ) {T : ℕ} (x : Fin T → X) (θ : Θ)
    (hpos : ∀ t, 0 < f (x t) θ) :
    Real.log (ml_likelihood f x θ) = ml_logLikelihood f x θ := by
  unfold ml_likelihood ml_logLikelihood
  exact Real.log_prod fun t _ => (hpos t).ne'

/-- Miao, p. 396: with a positive density, `θ̂` maximises the likelihood on `Θ₀` iff it
maximises the log-likelihood there. -/
theorem ml_isMaxOn_likelihood_iff {X Θ : Type*} (f : X → Θ → ℝ) {T : ℕ} (x : Fin T → X)
    (Θ₀ : Set Θ) (θhat : Θ) (hpos : ∀ θ t, 0 < f (x t) θ) :
    IsMaxOn (ml_likelihood f x) Θ₀ θhat ↔ IsMaxOn (ml_logLikelihood f x) Θ₀ θhat := by
  have hL : ∀ θ, 0 < ml_likelihood f x θ := fun θ =>
    Finset.prod_pos fun t _ => hpos θ t
  constructor
  · intro h θ hθ
    have h' : ml_likelihood f x θ ≤ ml_likelihood f x θhat := h hθ
    change ml_logLikelihood f x θ ≤ ml_logLikelihood f x θhat
    rw [← eq_ml_log_likelihood f x θ (hpos θ), ← eq_ml_log_likelihood f x θhat (hpos θhat)]
    exact Real.log_le_log (hL θ) h'
  · intro h θ hθ
    have h' : ml_logLikelihood f x θ ≤ ml_logLikelihood f x θhat := h hθ
    change ml_likelihood f x θ ≤ ml_likelihood f x θhat
    rw [← eq_ml_log_likelihood f x θ (hpos θ), ← eq_ml_log_likelihood f x θhat (hpos θhat)] at h'
    exact (Real.log_le_log_iff (hL θ) (hL θhat)).1 h'

/-- Miao, p. 397: the first-order condition of ML. If `θ̂` is a local maximiser of the
log-likelihood and each `θ ↦ ln f(xₜ, θ)` has derivative `s(xₜ, θ̂)` at `θ̂`, then
`∑ₜ s(xₜ, θ̂) = 0`: the ML estimator is the GMM estimator that sets the sample mean of the
moment function `h(x, θ) = ∂ ln f(x, θ)/∂θ` (the score) to zero. -/
theorem ml_first_order_condition {X : Type*} (f : X → ℝ → ℝ) (s : X → ℝ → ℝ) {T : ℕ}
    (x : Fin T → X) (θhat : ℝ) (hmax : IsLocalMax (ml_logLikelihood f x) θhat)
    (hd : ∀ t, HasDerivAt (fun θ => Real.log (f (x t) θ)) (s (x t) θhat) θhat) :
    ∑ t, s (x t) θhat = 0 := by
  have hsum : HasDerivAt (ml_logLikelihood f x) (∑ t, s (x t) θhat) θhat := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun t _ => hd t
    exact this
  exact hmax.hasDerivAt_eq_zero hsum

/-- Miao, p. 397 (the population moment condition `E[∂ ln f(x, θ)/∂θ] = 0`): for a model
`p(·, θ)` on a finite sample space with `∑ₓ p(x, θ) = 1` for all `θ`, positive probabilities and
`∂ₜₕₑₜₐ p(x, θ) = p′(x, θ)`, the score `s = p′/p = ∂ ln p/∂θ` has mean zero:
`∑ₓ p(x, θ) s(x, θ) = 0`. Hence the ML estimator is a GMM estimator with the score as moment. -/
theorem ml_score_mean_zero {Ω : Type*} [Fintype Ω] (p p' : Ω → ℝ → ℝ)
    (hsum : ∀ θ, ∑ x, p x θ = 1) (hpos : ∀ x θ, 0 < p x θ)
    (hp : ∀ x θ, HasDerivAt (p x) (p' x θ) θ) (θ : ℝ) :
    ∑ x, p x θ * (p' x θ / p x θ) = 0 ∧ ∑ x, p' x θ = 0 := by
  have hd : HasDerivAt (fun θ => ∑ x, p x θ) (∑ x, p' x θ) θ :=
    HasDerivAt.fun_sum (u := Finset.univ) fun x _ => hp x θ
  have hconst : (fun θ => ∑ x, p x θ) = fun _ => (1 : ℝ) := funext hsum
  rw [hconst] at hd
  have h0 : ∑ x, p' x θ = 0 := (hd.unique (hasDerivAt_const θ 1)).symm ▸ rfl
  refine ⟨?_, h0⟩
  rw [← h0]
  refine Finset.sum_congr rfl fun x _ => ?_
  field_simp [(hpos x θ).ne']

/-- **Information matrix equality** (Miao, p. 398), for a scalar parameter on a finite sample
space: with `∑ₓ p(x, θ) = 1`, `p > 0`, `∂p/∂θ = p′`, `∂p′/∂θ = p″`, the score
`s = ∂ ln p/∂θ` and its derivative `H = ∂² ln p/∂θ²` satisfy
`−E[H] = E[s²]`, i.e. `I(θ) = −E[∂² ln p/∂θ²] = E[(∂ ln p/∂θ)²]`. The functions `s` and `H` are
arbitrary functions with these derivative properties. -/
theorem ml_information_matrix_equality {Ω : Type*} [Fintype Ω] (p p' p'' s H : Ω → ℝ → ℝ)
    (hsum : ∀ θ, ∑ x, p x θ = 1) (hpos : ∀ x θ, 0 < p x θ)
    (hp : ∀ x θ, HasDerivAt (p x) (p' x θ) θ) (hp' : ∀ x θ, HasDerivAt (p' x) (p'' x θ) θ)
    (hs : ∀ x θ, HasDerivAt (fun θ => Real.log (p x θ)) (s x θ) θ)
    (hH : ∀ x θ, HasDerivAt (s x) (H x θ) θ) (θ : ℝ) :
    -∑ x, p x θ * H x θ = ∑ x, p x θ * s x θ ^ 2 := by
  -- the score is `p′/p`
  have hs_eq : ∀ x θ, s x θ = p' x θ / p x θ := fun x θ =>
    (hs x θ).unique (((hp x θ).log (hpos x θ).ne'))
  -- `∑ p″ = 0`, differentiating `∑ p′ = 0`
  have h1 : ∀ θ, ∑ x, p' x θ = 0 := fun θ => (ml_score_mean_zero p p' hsum hpos hp θ).2
  have hd : HasDerivAt (fun θ => ∑ x, p' x θ) (∑ x, p'' x θ) θ :=
    HasDerivAt.fun_sum (u := Finset.univ) fun x _ => hp' x θ
  rw [show (fun θ => ∑ x, p' x θ) = fun _ => (0 : ℝ) from funext h1] at hd
  have h2 : ∑ x, p'' x θ = 0 := (hd.unique (hasDerivAt_const θ 0)).symm ▸ rfl
  -- `H = (p″ p − p′²)/p²`
  have hH_eq : ∀ x, H x θ = (p'' x θ * p x θ - p' x θ * p' x θ) / p x θ ^ 2 := fun x => by
    have hsx : s x = fun θ => p' x θ / p x θ := funext fun θ => hs_eq x θ
    have := hH x θ
    rw [hsx] at this
    exact this.unique ((hp' x θ).div (hp x θ) (hpos x θ).ne')
  have key : ∀ x, -(p x θ * H x θ) = p x θ * s x θ ^ 2 - p'' x θ := fun x => by
    rw [hH_eq x, hs_eq x θ]
    field_simp [(hpos x θ).ne']
    ring
  rw [← Finset.sum_neg_distrib, Finset.sum_congr rfl fun x _ => key x, Finset.sum_sub_distrib,
    h2, sub_zero]

/-- **Cramér–Rao bound** (Miao, p. 398), for a scalar parameter on a finite sample space. Let
`δ` be an unbiased estimator of `g(θ)`: `∑ₓ p(x, θ) δ(x) = g(θ)` for all `θ`, with
`g′(θ) = g'`. Then `g′(θ)² ≤ Var_θ(δ) · I(θ)`, where `Var_θ(δ) = ∑ₓ p (δ − g(θ))²` and
`I(θ) = ∑ₓ p s²` with the score `s = p′/p`. -/
theorem ml_cramer_rao {Ω : Type*} [Fintype Ω] (p p' : Ω → ℝ → ℝ) (δ : Ω → ℝ) (g : ℝ → ℝ)
    (hsum : ∀ θ, ∑ x, p x θ = 1) (hpos : ∀ x θ, 0 < p x θ)
    (hp : ∀ x θ, HasDerivAt (p x) (p' x θ) θ) (hunb : ∀ θ, ∑ x, p x θ * δ x = g θ)
    (θ g' : ℝ) (hg : HasDerivAt g g' θ) :
    g' ^ 2 ≤ (∑ x, p x θ * (δ x - g θ) ^ 2) * ∑ x, p x θ * (p' x θ / p x θ) ^ 2 := by
  have hd : HasDerivAt (fun θ => ∑ x, p x θ * δ x) (∑ x, p' x θ * δ x) θ :=
    HasDerivAt.fun_sum (u := Finset.univ) fun x _ => (hp x θ).mul_const (δ x)
  rw [show (fun θ => ∑ x, p x θ * δ x) = g from funext hunb] at hd
  have hg' : g' = ∑ x, p' x θ * δ x := hg.unique hd
  have h0 := (ml_score_mean_zero p p' hsum hpos hp θ).2
  -- `g′ = ∑ √p (δ − g) · √p s`
  have hrep : g' = ∑ x, (Real.sqrt (p x θ) * (δ x - g θ)) *
      (Real.sqrt (p x θ) * (p' x θ / p x θ)) := by
    rw [hg']
    have : ∑ x, p' x θ * δ x = ∑ x, p' x θ * δ x - g θ * ∑ x, p' x θ := by rw [h0]; ring
    rw [this, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hsq : Real.sqrt (p x θ) * Real.sqrt (p x θ) = p x θ :=
      Real.mul_self_sqrt (hpos x θ).le
    have hne := (hpos x θ).ne'
    calc p' x θ * δ x - g θ * p' x θ
        = (Real.sqrt (p x θ) * Real.sqrt (p x θ)) * (δ x - g θ) * (p' x θ / p x θ) := by
          rw [hsq]; field_simp
      _ = _ := by ring
  rw [hrep]
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (le_of_eq ?_)
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_pow, Real.sq_sqrt (hpos x θ).le]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_pow, Real.sq_sqrt (hpos x θ).le]

/-- The Cramér–Rao bound is attained (Miao, p. 398, the efficiency claim, in its simplest
instance): for one coin toss with `P(heads) = θ ∈ (0, 1)`, the estimator `δ = 1{heads}` of
`g(θ) = θ` has `Var_θ(δ) = θ(1 − θ)`, the information is `I(θ) = 1/(θ(1 − θ))`, and
`Var_θ(δ) · I(θ) = 1 = g′(θ)²`. -/
theorem ml_cramer_rao_bernoulli (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) :
    let p : Bool → ℝ → ℝ := fun b t => if b then t else 1 - t
    let p' : Bool → ℝ → ℝ := fun b _ => if b then 1 else -1
    let δ : Bool → ℝ := fun b => if b then 1 else 0
    (∑ x, p x θ * (δ x - θ) ^ 2 = θ * (1 - θ)) ∧
      (∑ x, p x θ * (p' x θ / p x θ) ^ 2 = 1 / (θ * (1 - θ))) ∧
      (∑ x, p x θ * (δ x - θ) ^ 2) * (∑ x, p x θ * (p' x θ / p x θ) ^ 2) = 1 ^ 2 := by
  intro p p' δ
  have hv : ∑ x, p x θ * (δ x - θ) ^ 2 = θ * (1 - θ) := by
    simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton, p, δ, ite_true, ite_false, Bool.false_eq_true]
    ring
  have hI : ∑ x, p x θ * (p' x θ / p x θ) ^ 2 = 1 / (θ * (1 - θ)) := by
    simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton, p, p', ite_true, ite_false, Bool.false_eq_true]
    have : (1 - θ) ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨hv, hI, ?_⟩
  rw [hv, hI]
  have : (1 - θ) ≠ 0 := by linarith
  field_simp

/-- **Invariance** (Miao, p. 398), for a reparametrisation `e : Θ ≃ Γ`: if `θ̂` maximises `L`
then `γ̂ = e(θ̂)` maximises the likelihood `γ ↦ L(e⁻¹ γ)` of `γ = e(θ)`. -/
theorem ml_invariance {Θ Γ : Type*} (L : Θ → ℝ) (e : Θ ≃ Γ) (θhat : Θ)
    (hmax : ∀ θ, L θ ≤ L θhat) : ∀ γ, L (e.symm γ) ≤ L (e.symm (e θhat)) := by
  intro γ
  rw [e.symm_apply_apply]
  exact hmax _

/-- The profile (induced) likelihood of `γ = c(θ)`: `L*(γ) = sup {L(θ) : c(θ) = γ}`. -/
noncomputable def ml_profileLikelihood {Θ Γ : Type*} (L : Θ → ℝ) (c : Θ → Γ) (γ : Γ) : ℝ :=
  sSup (L '' {θ | c θ = γ})

/-- **Invariance** (Miao, p. 398), for any `c : Θ → Γ` (Zehna's theorem): if `θ̂` maximises `L`,
then `c(θ̂)` maximises the profile likelihood `L*(γ) = sup {L(θ) : c(θ) = γ}` over the attainable
`γ`, and `L*(c(θ̂)) = L(θ̂)`. The book asks `c` to be continuously differentiable; no regularity
of `c` is needed. -/
theorem ml_invariance_profile {Θ Γ : Type*} (L : Θ → ℝ) (c : Θ → Γ) (θhat : Θ)
    (hmax : ∀ θ, L θ ≤ L θhat) :
    ml_profileLikelihood L c (c θhat) = L θhat ∧
      ∀ γ ∈ Set.range c, ml_profileLikelihood L c γ ≤ ml_profileLikelihood L c (c θhat) := by
  have hfib : ml_profileLikelihood L c (c θhat) = L θhat := by
    unfold ml_profileLikelihood
    refine le_antisymm (csSup_le ⟨L θhat, θhat, rfl, rfl⟩ ?_) ?_
    · rintro _ ⟨θ, -, rfl⟩
      exact hmax θ
    · exact le_csSup ⟨L θhat, by rintro _ ⟨θ, -, rfl⟩; exact hmax θ⟩ ⟨θhat, rfl, rfl⟩
  refine ⟨hfib, ?_⟩
  rintro γ ⟨θ₀, rfl⟩
  rw [hfib]
  unfold ml_profileLikelihood
  refine csSup_le ⟨L θ₀, θ₀, rfl, rfl⟩ ?_
  rintro _ ⟨θ, -, rfl⟩
  exact hmax θ

/-- The log-likelihood of the Gaussian location model with known variance `σ²`, up to the
constant `−(T/2) ln(2πσ²)`: `ℓ(μ) = −∑ₜ (xₜ − μ)²/(2σ²)`. -/
noncomputable def ml_gaussLogLik {T : ℕ} (σ2 : ℝ) (x : Fin T → ℝ) (μ : ℝ) : ℝ :=
  -(∑ t, (x t - μ) ^ 2) / (2 * σ2)

/-- Miao, pp. 398–399: the likelihood ratio, Wald and Lagrange multiplier tests of
`H₀ : μ = μ₀` in the Gaussian location model `xₜ ~ N(μ, σ²)` (known `σ² > 0`, `T ≥ 1`
observations, ML estimator `μ̂ = x̄`) coincide:
`LR = 2(ℓ(x̄) − ℓ(μ₀))`, `W = c(μ̂)² / Var(c(μ̂))` with `c(μ) = μ − μ₀`, `Var(x̄) = σ²/T`, and
`LM = ℓ′(μ₀)² / I` with the sample information `I = T/σ²` all equal `T(x̄ − μ₀)²/σ²`. -/
theorem ml_gaussian_tests_equal {T : ℕ} (hT : 0 < T) (σ2 : ℝ) (hσ : 0 < σ2) (x : Fin T → ℝ)
    (μ₀ : ℝ) :
    let xbar := (∑ t, x t) / T
    let LR := 2 * (ml_gaussLogLik σ2 x xbar - ml_gaussLogLik σ2 x μ₀)
    let W := (xbar - μ₀) ^ 2 / (σ2 / T)
    let LM := ((∑ t, (x t - μ₀)) / σ2) ^ 2 / (T / σ2)
    LR = T * (xbar - μ₀) ^ 2 / σ2 ∧ W = T * (xbar - μ₀) ^ 2 / σ2 ∧
      LM = T * (xbar - μ₀) ^ 2 / σ2 := by
  intro xbar LR W LM
  have hT' : (T : ℝ) ≠ 0 := by positivity
  have hS : ∑ t, x t = T * xbar := by
    simp only [xbar]; field_simp
  have hdecomp : ∀ m : ℝ, ∑ t, (x t - m) ^ 2 =
      ∑ t, (x t - xbar) ^ 2 + T * (xbar - m) ^ 2 := fun m => by
    have : ∀ t, (x t - m) ^ 2 = (x t - xbar) ^ 2 + 2 * (xbar - m) * x t +
        (m ^ 2 - xbar ^ 2) := fun t => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS]
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [LR, ml_gaussLogLik]
    rw [hdecomp xbar, hdecomp μ₀]
    field_simp
    ring
  · simp only [W]
    field_simp
  · simp only [LM]
    have : ∑ t, (x t - μ₀) = T * (xbar - μ₀) := by
      rw [Finset.sum_sub_distrib, hS]; simp
      ring
    rw [this]
    field_simp

end Miao.StructuralEstimation

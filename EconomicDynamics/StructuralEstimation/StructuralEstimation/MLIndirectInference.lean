/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.MLSimulatedMoments
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Simulated maximum likelihood and indirect inference (§§12.3.2–12.3.3)

Miao, §12.3.2, pp. 403–404, and §12.3.3 with Example 12.3.3 and (12.7), pp. 404–408.

**Simulated maximum likelihood.**
* `ml_sml_average_unbiased`: the average `(1/S)∑ₛ f̃(θ | x, ωˢ)` of an unbiased simulator is
  unbiased; `ml_sml_simulator_slln`: it converges to `f(x, θ)` a.s. as `S → ∞` (the book's
  `lim (1/S)∑ₛ f̃ = f`, by the strong law).
* `ml_sml_log_bias` (why SML is inconsistent for fixed `S`): `E ln f̃ ≤ ln E f̃ = ln f`;
  `ml_sml_log_bias_strict`: strictly, for a two-point simulator (`E ln f̃ = ln f + ½ ln ¾`).

**Indirect inference.**
* `ml_iiAverage`, `ml_ii_average_correction`: `β̂_ST(θ)` must be the average
  `(1/S)∑ₛ β̂ˢ_T(θ)`; the book's sum `∑ₛ β̂ˢ_T(θ)` is `S` times it.
* `example_12_3_3`: in the exponential duration model with hazard `β` the log-likelihood is
  `N ln β − β ∑ Dᵢ` and the ML estimator is `β̂ = N/∑ᵢ Dᵢ = 1/D̄`, not the book's `∑ᵢ Dᵢ/N`;
  `example_12_3_3_book_false` is a counterexample to the printed formula.
  `example_12_3_3_mean`: parametrised by the mean duration `λ = 1/β`, the ML estimator is `D̄`;
  `example_12_3_3_ii_eq_smm`: then indirect inference is SMM matching the mean duration (as the
  book says), while `example_12_3_3_hazard_ne` shows that with the hazard parametrisation and
  `S = 2` it is not.
* `ml_binding_derivative` (p. 407): differentiating the first-order condition
  `∂ψ_∞(θ, b(θ))/∂β = 0` gives `∂b/∂θ = J₀⁻¹ ∂²ψ_∞/∂β∂θ′` (`ml_binding_derivative_J`), with
  `J₀ = −∂²ψ_∞/∂β∂β′`; for general normed spaces.
* `ml_ii_Q`, `eq_12_7_optimal` (p. 407): with `W* = J₀(I₀ − K₀)⁻¹J₀`,
  `Q_S(W*) = (1 + 1/S)(bᵀW*b)⁻¹ = (1 + 1/S)(Dᵀ(I₀ − K₀)⁻¹D)⁻¹` for `b = J₀⁻¹D`,
  `D = ∂²ψ_∞/∂β∂θ′`, and `Q_S(W) − Q_S(W*)` is positive semidefinite.

Not formalised (stated in the book without proof or computational): the SML limit theory with
`√T/S → 0`, the approximation of `I(θ₀)`, the consistent estimator of `I₀ − K₀`, the EMM
estimator, the limit (12.7) itself and the `χ²(q − k)` global specification test.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology Matrix

/-- Miao, p. 403: if each draw `f̃(θ | x, ωˢ)` is an unbiased simulator of `f(x, θ)`, so is their
average. -/
theorem ml_sml_average_unbiased {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S : ℕ}
    (hS : 0 < S) (ftil : Fin S → Ω → ℝ) (f : ℝ) (hint : ∀ s, Integrable (ftil s) P)
    (hunb : ∀ s, ∫ a, ftil s a ∂P = f) :
    ∫ a, (1 / (S : ℝ)) * ∑ s, ftil s a ∂P = f := by
  rw [integral_const_mul, integral_finsetSum _ fun s _ => hint s]
  simp only [hunb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (S : ℝ) ≠ 0 := by positivity
  field_simp

/-- Miao, p. 403: for i.i.d. draws `ωˢ` and an unbiased simulator,
`(1/S)∑_{s<S} f̃(θ | x, ωˢ) → f(x, θ)` almost surely as `S → ∞` (the strong law). -/
theorem ml_sml_simulator_slln {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ftil : ℕ → Ω → ℝ) (f : ℝ) (hint : Integrable (ftil 0) P)
    (hindep : Pairwise fun i j => IndepFun (ftil i) (ftil j) P)
    (hident : ∀ i, IdentDistrib (ftil i) (ftil 0) P P) (hunb : ∫ a, ftil 0 a ∂P = f) :
    ∀ᵐ a ∂P, Tendsto (fun S : ℕ => (∑ s ∈ Finset.range S, ftil s a) / S) atTop (𝓝 f) := by
  have := strong_law_ae_real ftil hint hindep hident
  rw [hunb] at this
  exact this

/-- Miao, p. 403 (the source of the inconsistency of SML for fixed `S`): for a positive unbiased
simulator `Y` of `f > 0` (`E Y = f`), `E ln Y ≤ ln f`: the simulated log-likelihood is biased
downward. -/
theorem ml_sml_log_bias {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (f : ℝ) (hf : 0 < f) (hpos : ∀ a, 0 < Y a)
    (hint : Integrable Y P) (hlog : Integrable (fun a => Real.log (Y a)) P)
    (hmean : ∫ a, Y a ∂P = f) : ∫ a, Real.log (Y a) ∂P ≤ Real.log f := by
  have hpt : ∀ a, Real.log (Y a) ≤ Real.log f + (Y a / f - 1) := fun a => by
    have := Real.log_le_sub_one_of_pos (div_pos (hpos a) hf)
    rw [Real.log_div (hpos a).ne' hf.ne'] at this
    linarith
  have hint2 : Integrable (fun a => Real.log f + (Y a / f - 1)) P :=
    (integrable_const _).add ((hint.div_const f).sub (integrable_const 1))
  calc ∫ a, Real.log (Y a) ∂P ≤ ∫ a, (Real.log f + (Y a / f - 1)) ∂P :=
        integral_mono hlog hint2 hpt
    _ = Real.log f := by
        have hi : Integrable (fun a => Y a / f - 1) P := (hint.div_const f).sub (integrable_const 1)
        rw [integral_add (integrable_const _) hi,
          integral_sub (hint.div_const f) (integrable_const 1), integral_div, hmean]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        field_simp
        ring

/-- Miao, p. 403: the bias is strict in general. For the unbiased two-point simulator equal to
`f/2` or `3f/2` with probability `1/2` each, `E f̃ = f` but
`E ln f̃ = ln f + ½ ln(3/4) < ln f`. -/
theorem ml_sml_log_bias_strict (f : ℝ) (hf : 0 < f) :
    (1 / 2 : ℝ) * (f / 2) + 1 / 2 * (3 * f / 2) = f ∧
      (1 / 2 : ℝ) * Real.log (f / 2) + 1 / 2 * Real.log (3 * f / 2) =
        Real.log f + 1 / 2 * Real.log (3 / 4) ∧
      (1 / 2 : ℝ) * Real.log (f / 2) + 1 / 2 * Real.log (3 * f / 2) < Real.log f := by
  have h1 : Real.log (f / 2) = Real.log f - Real.log 2 :=
    Real.log_div hf.ne' two_ne_zero
  have h2 : Real.log (3 * f / 2) = Real.log 3 + Real.log f - Real.log 2 := by
    rw [Real.log_div (by positivity) two_ne_zero, Real.log_mul (by norm_num) hf.ne']
  have h3 : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast; ring
  have heq : (1 / 2 : ℝ) * Real.log (f / 2) + 1 / 2 * Real.log (3 * f / 2) =
      Real.log f + 1 / 2 * Real.log (3 / 4) := by
    rw [h1, h2, h3]; ring
  refine ⟨by ring, heq, ?_⟩
  rw [heq]
  have : Real.log (3 / 4) < 0 := Real.log_neg (by norm_num) (by norm_num)
  linarith

/-- The average auxiliary estimate over simulations, `β̂_ST(θ) = (1/S)∑ₛ β̂ˢ_T(θ)`. -/
noncomputable def ml_iiAverage {S p : ℕ} (βs : Fin S → Fin p → ℝ) : Fin p → ℝ :=
  (1 / (S : ℝ)) • ∑ s, βs s

/-- Miao, p. 405 (correction): the average of `S` identical auxiliary estimates `b` is `b`,
while the book's `∑ₛ β̂ˢ_T(θ)` is `S • b`, so the indirect inference criterion must use the
average. -/
theorem ml_ii_average_correction {S p : ℕ} (hS : 0 < S) (b : Fin p → ℝ) :
    ml_iiAverage (fun _ : Fin S => b) = b ∧ ∑ _s : Fin S, b = (S : ℝ) • b := by
  have : (S : ℝ) ≠ 0 := by positivity
  refine ⟨?_, by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul]⟩
  unfold ml_iiAverage
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, one_div_mul_cancel this, one_smul]

/-- **Example 12.3.3** (Miao, p. 405): in the exponential duration model with constant hazard
`β`, the log-likelihood of the durations `D₁, …, D_N` is
`∑ᵢ ln(βe^{−βDᵢ}) = N ln β − β ∑ᵢ Dᵢ`, and (when `∑ᵢ Dᵢ > 0`) it is maximised at
`β̂ = N/∑ᵢ Dᵢ = 1/D̄`, the inverse of the mean duration. -/
theorem example_12_3_3 {N : ℕ} (D : Fin N → ℝ) (hS : 0 < ∑ i, D i) :
    (∀ β, 0 < β → ml_logLikelihood ml_expDensity D β = N * Real.log β - β * ∑ i, D i) ∧
      IsMaxOn (ml_logLikelihood ml_expDensity D) (Set.Ioi 0) ((N : ℝ) / ∑ i, D i) := by
  refine ⟨fun β hβ => ex_12_2_logLikelihood D hβ, ?_⟩
  obtain ⟨hpos, -, hmax⟩ := ex_12_2 D hS
  intro θ hθ
  have hθ' : (0 : ℝ) < θ := hθ
  have h := hmax hθ
  change ml_logLikelihood ml_expDensity D θ ≤ ml_logLikelihood ml_expDensity D (N / ∑ i, D i)
  have hdens : ∀ η : ℝ, 0 < η → ∀ t, 0 < ml_expDensity (D t) η := fun η hη t => by
    unfold ml_expDensity; positivity
  rw [← eq_ml_log_likelihood _ _ _ (hdens θ hθ'), ← eq_ml_log_likelihood _ _ _ (hdens _ hpos)]
  exact Real.log_le_log (Finset.prod_pos fun t _ => hdens θ hθ' t) h

/-- Counterexample to the printed formula `β̂_T = ∑ᵢ Dᵢ/N` of Example 12.3.3 (Miao, p. 405):
for one observed duration `D₁ = 2`, the book's value `β = 2` gives a lower log-likelihood than
`β = 1/2` (the true maximiser `1/D̄`). -/
theorem example_12_3_3_book_false :
    ml_logLikelihood ml_expDensity (fun _ : Fin 1 => (2 : ℝ)) 2 <
      ml_logLikelihood ml_expDensity (fun _ : Fin 1 => (2 : ℝ)) (1 / 2) := by
  rw [ex_12_2_logLikelihood _ (by norm_num), ex_12_2_logLikelihood _ (by norm_num)]
  simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, one_mul,
    Real.log_inv, one_div]
  have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
  norm_num
  linarith

/-- Example 12.3.3 (Miao, p. 405), corrected: parametrised by the mean duration `λ = 1/β`, the
exponential likelihood `λ ↦ L(1/λ)` is maximised at the mean duration `λ̂ = D̄ = ∑ᵢ Dᵢ/N`
(invariance of ML). -/
theorem example_12_3_3_mean {N : ℕ} (D : Fin N → ℝ) (hS : 0 < ∑ i, D i) :
    ∀ lam, 0 < lam → ml_likelihood ml_expDensity D (1 / lam) ≤
      ml_likelihood ml_expDensity D (1 / ((∑ i, D i) / N)) := by
  obtain ⟨-, heq, hmax⟩ := ex_12_2 D hS
  intro lam hlam
  rw [← heq]
  exact hmax (show (0 : ℝ) < 1 / lam by positivity)

/-- Example 12.3.3 (Miao, pp. 405–406): with the mean-duration parametrisation, the auxiliary
estimates are `D̄` (data) and `D̄ˢ(θ)` (simulations), and the indirect inference criterion
`W(D̄ − (1/S)∑ₛ D̄ˢ(θ))²` equals `W g²` for the SMM moment `g = (1/N)∑ᵢ (Dᵢ − (1/S)∑ₛ Dᵢˢ(θ))`
of (12.5) with `m(D) = D`: indirect inference is SMM matching the mean duration. -/
theorem example_12_3_3_ii_eq_smm {N S : ℕ} (hN : 0 < N) (D : Fin N → ℝ)
    (Dsim : Fin S → Fin N → ℝ) (W : ℝ) :
    W * ((∑ i, D i) / N - (1 / (S : ℝ)) * ∑ s, (∑ i, Dsim s i) / N) ^ 2 =
      W * ((1 / (N : ℝ)) * ∑ i, (D i - (1 / (S : ℝ)) * ∑ s, Dsim s i)) ^ 2 := by
  congr 2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm (f := fun i s => Dsim s i),
    ← Finset.sum_div]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

/-- Example 12.3.3 (Miao, p. 406): with the hazard parametrisation and `S = 2` simulations,
indirect inference does not reduce to matching the mean duration. Data mean `D̄ = 2`, simulated
means `D̄¹ = 1`, `D̄² = 3`: the mean durations match (`2 = (1 + 3)/2`), but the auxiliary
hazards do not (`1/2 ≠ (1/1 + 1/3)/2`). -/
theorem example_12_3_3_hazard_ne :
    (2 : ℝ) - (1 / 2) * (1 + 3) = 0 ∧ (1 / 2 : ℝ) - (1 / 2) * (1 / 1 + 1 / 3) ≠ 0 := by
  norm_num

/-- Miao, p. 407: the derivative of the binding function. If `b(θ)` solves the first-order
condition `G(θ, b(θ)) = 0` for all `θ`, where `G = ∂ψ_∞/∂β` has derivative `G′` at
`(θ₀, b(θ₀))` and `b` has derivative `b′` at `θ₀`, then
`G′(·, 0) + G′(0, b′ ·) = 0`, i.e. `∂²ψ_∞/∂β∂θ′ + ∂²ψ_∞/∂β∂β′ · ∂b/∂θ′ = 0`. -/
theorem ml_binding_derivative {Eθ Eβ F : Type*} [NormedAddCommGroup Eθ] [NormedSpace ℝ Eθ]
    [NormedAddCommGroup Eβ] [NormedSpace ℝ Eβ] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : Eθ × Eβ → F) (b : Eθ → Eβ) (θ₀ : Eθ) (G' : Eθ × Eβ →L[ℝ] F) (b' : Eθ →L[ℝ] Eβ)
    (hfoc : ∀ θ, G (θ, b θ) = 0) (hG : HasFDerivAt G G' (θ₀, b θ₀))
    (hb : HasFDerivAt b b' θ₀) :
    G'.comp (ContinuousLinearMap.inl ℝ Eθ Eβ) +
      (G'.comp (ContinuousLinearMap.inr ℝ Eθ Eβ)).comp b' = 0 := by
  have hpair : HasFDerivAt (fun θ => (θ, b θ)) ((ContinuousLinearMap.id ℝ Eθ).prod b') θ₀ :=
    (hasFDerivAt_id θ₀).prodMk hb
  have hcomp := hG.comp θ₀ hpair
  have hconst : (G ∘ fun θ => (θ, b θ)) = fun _ => 0 := funext hfoc
  rw [hconst] at hcomp
  have h0 := hcomp.unique (hasFDerivAt_const 0 θ₀)
  ext v
  have := congrArg (fun L : Eθ →L[ℝ] F => L v) h0
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq, _root_.zero_apply] at this
  simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    _root_.zero_apply]
  rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  exact this

/-- Miao, p. 407: `∂b/∂θ′ = J₀⁻¹ ∂²ψ_∞/∂β∂θ′`, where `J₀ = −∂²ψ_∞/∂β∂β′` (the `β`-block of `G′`
with a minus sign) is invertible. -/
theorem ml_binding_derivative_J {Eθ Eβ F : Type*} [NormedAddCommGroup Eθ] [NormedSpace ℝ Eθ]
    [NormedAddCommGroup Eβ] [NormedSpace ℝ Eβ] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : Eθ × Eβ → F) (b : Eθ → Eβ) (θ₀ : Eθ) (G' : Eθ × Eβ →L[ℝ] F) (b' : Eθ →L[ℝ] Eβ)
    (hfoc : ∀ θ, G (θ, b θ) = 0) (hG : HasFDerivAt G G' (θ₀, b θ₀))
    (hb : HasFDerivAt b b' θ₀) (J : Eβ ≃L[ℝ] F)
    (hJ : (J : Eβ →L[ℝ] F) = -G'.comp (ContinuousLinearMap.inr ℝ Eθ Eβ)) :
    b' = (J.symm : F →L[ℝ] Eβ).comp (G'.comp (ContinuousLinearMap.inl ℝ Eθ Eβ)) := by
  have h := ml_binding_derivative G b θ₀ G' b' hfoc hG hb
  ext v
  have hv := congrArg (fun L : Eθ →L[ℝ] F => L v) h
  simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    _root_.zero_apply] at hv
  have hJv : J (b' v) = G' ((ContinuousLinearMap.inl ℝ Eθ Eβ) v) := by
    have : (J : Eβ →L[ℝ] F) (b' v) = -(G' ((ContinuousLinearMap.inr ℝ Eθ Eβ) (b' v))) := by
      rw [hJ]; rfl
    rw [ContinuousLinearEquiv.coe_coe] at this
    rw [this]
    exact (neg_eq_of_add_eq_zero_left hv)
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  rw [← hJv, ContinuousLinearEquiv.symm_apply_apply]

/-- The indirect inference asymptotic variance (12.7) (Miao, p. 406):
`Q_S(W) = (1 + 1/S)(bᵀWb)⁻¹ bᵀW J₀⁻¹(I₀ − K₀)J₀⁻¹ Wb (bᵀWb)⁻¹`, with `b = ∂b(θ₀)/∂θ′`
(`q × k`) and `Pm = I₀ − K₀`. -/
noncomputable def ml_ii_Q {q k : ℕ} (S : ℕ) (b : Matrix (Fin q) (Fin k) ℝ)
    (J Pm W : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (1 + 1 / (S : ℝ)) • ml_sandwich b (J⁻¹ * Pm * J⁻¹) W

/-- Miao, (12.7) and p. 407: the optimal weighting matrix of indirect inference. With `J₀`
symmetric invertible, `I₀ − K₀` positive semidefinite invertible and
`W* = J₀(I₀ − K₀)⁻¹J₀`: `Q_S(W*) = (1 + 1/S)(bᵀW*b)⁻¹`; if `b = J₀⁻¹D` with
`D = ∂²ψ_∞/∂β∂θ′`, then `bᵀW*b = Dᵀ(I₀ − K₀)⁻¹D`, so
`Q_S(W*) = (1 + 1/S)(Dᵀ(I₀ − K₀)⁻¹D)⁻¹`; and `Q_S(W) − Q_S(W*)` is positive semidefinite for
every symmetric `W` with `bᵀWb` invertible. -/
theorem eq_12_7_optimal {q k : ℕ} (S : ℕ) (b : Matrix (Fin q) (Fin k) ℝ)
    (J Pm W : Matrix (Fin q) (Fin q) ℝ) (hJ : Jᵀ = J) (hJu : IsUnit J.det)
    (hP : Pm.PosSemidef) (hPu : IsUnit Pm.det) (hM : IsUnit (bᵀ * (J * Pm⁻¹ * J) * b).det)
    (hW : Wᵀ = W) (hA : IsUnit (bᵀ * W * b).det) :
    ml_ii_Q S b J Pm (J * Pm⁻¹ * J) = (1 + 1 / (S : ℝ)) • (bᵀ * (J * Pm⁻¹ * J) * b)⁻¹ ∧
      (∀ D : Matrix (Fin q) (Fin k) ℝ, b = J⁻¹ * D →
        bᵀ * (J * Pm⁻¹ * J) * b = Dᵀ * Pm⁻¹ * D) ∧
      (ml_ii_Q S b J Pm W - ml_ii_Q S b J Pm (J * Pm⁻¹ * J)).PosSemidef := by
  set Ω := J⁻¹ * Pm * J⁻¹ with hΩ
  have hJi : (J⁻¹)ᵀ = J⁻¹ := by rw [transpose_nonsing_inv, hJ]
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJu
  have hJJ' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hJu
  have hPP : Pm * Pm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPu
  have hJiu : IsUnit (J⁻¹).det := by
    rw [Matrix.det_nonsing_inv]; exact hJu.ringInverse
  have hΩu : IsUnit Ω.det := by
    rw [hΩ, Matrix.det_mul, Matrix.det_mul]
    exact (hJiu.mul hPu).mul hJiu
  have hΩinv : Ω⁻¹ = J * Pm⁻¹ * J := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hΩ]
    calc J * Pm⁻¹ * J * (J⁻¹ * Pm * J⁻¹) = J * Pm⁻¹ * (J * J⁻¹) * Pm * J⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hJJ, Matrix.mul_one, Matrix.mul_assoc J, Matrix.nonsing_inv_mul _ hPu,
            Matrix.mul_one, hJJ]
  have hΩpsd : Ω.PosSemidef := by
    have := hP.mul_mul_conjTranspose_same J⁻¹
    rwa [conjTranspose_eq_transpose_of_trivial, hJi] at this
  have hWstar : J * Pm⁻¹ * J = ((1 : ℝ) • Ω)⁻¹ := by rw [one_smul, hΩinv]
  have hM' : IsUnit (bᵀ * Ω⁻¹ * b).det := by rw [hΩinv]; exact hM
  have h1 : ml_ii_Q S b J Pm (J * Pm⁻¹ * J) = (1 + 1 / (S : ℝ)) • (bᵀ * (J * Pm⁻¹ * J) * b)⁻¹ := by
    unfold ml_ii_Q
    rw [← hΩ]
    conv_lhs => rw [hWstar]
    rw [ml_sandwich_inv b Ω hΩu hM' one_ne_zero, hΩinv]
  have hc : (0 : ℝ) ≤ 1 + 1 / (S : ℝ) := by positivity
  refine ⟨h1, fun D hD => ?_, ?_⟩
  · rw [hD, transpose_mul, hJi]
    calc Dᵀ * J⁻¹ * (J * Pm⁻¹ * J) * (J⁻¹ * D) = Dᵀ * (J⁻¹ * J) * Pm⁻¹ * (J * J⁻¹) * D := by
          simp only [Matrix.mul_assoc]
      _ = Dᵀ * Pm⁻¹ * D := by rw [hJJ', hJJ, Matrix.mul_one, Matrix.mul_one]
  · have hopt := ml_sandwich_optimal b Ω W hΩpsd hΩu hW hA hM'
    rw [h1, ml_ii_Q, ← hΩ, ← hΩinv, ← smul_sub]
    exact hopt.smul hc

end Miao.StructuralEstimation

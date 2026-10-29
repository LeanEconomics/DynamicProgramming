/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.LimitApplications
import LimitTheorems.LinearTChains
import Mathlib.Probability.CramerWold
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The vector linear state space model: (V4), the asymptotic variance and the CLT (MT §17.6.2)

Meyn and Tweedie, §17.6.2 and Theorem 17.6.2, pp. 455–456, for the linear state space model
LSS(F, G), `Xₖ₊₁ = F Xₖ + G Wₖ₊₁` on `ℝⁿ = Fin n → ℝ` (`lssMatrixKernel Γ F G`, `Γ` the law of
`W` on `ℝᵖ`), under the eigenvalue condition (LSS5) (`IsStableMatrix F`) and a centred
square-integrable disturbance (`HasCentredSecondMoments Γ`; the book's standing `E[W] = 0`).

**The Lyapunov matrix** (12.34).
* `abs_pow_apply_le`: `|(Fᵏ)ᵢⱼ| ≤ C rᵏ`, `r < 1`; `lyapunovMatrix F = M = Σₖ (Fᵏ)ᵀ Fᵏ`,
  `summable_lyapunov`; **`lyapunov_equation`**: `Fᵀ M F − M = −I`;
  `hasSum_quadForm_lyapunov` (`xᵀMx = Σₖ |Fᵏx|²`), `dotProduct_self_le_quadForm`
  (`|x|² ≤ xᵀMx`), `quadForm_le` (`xᵀMx ≤ Λ|x|²`), `quadForm_lyapunov_mulVec`
  (`(Fx)ᵀM(Fx) = xᵀMx − |x|²`).
* Norm helpers: `sq_norm_le_dotProduct_self`, `dotProduct_self_le_sq_norm`,
  `abs_dotProduct_le`, `sq_dotProduct_le` (Cauchy–Schwarz).

**The disturbance and one step of the model.** `disturbanceCov Γ = Σ_W`;
`integral_dotProduct_disturbance` (`E[v ⬝ W] = 0`), `integral_sq_dotProduct_disturbance`
(`E[(e ⬝ W)²] = eᵀΣ_We`), `integral_lssMatrixKernel`, `lintegral_lssMatrixKernel`,
`quadForm_add_mulVec`, `integral_dotProduct_lss` (`∫ c ⬝ y P(x, dy) = c ⬝ Fx`),
`integral_sq_dotProduct_lss`, `integral_dotProduct_lss_pow` (`∫ c ⬝ y Pᵏ(x, dy) = c ⬝ Fᵏx`).

**(V4).** `lssWeight F x = V(x) = 1 + xᵀMx`; `lintegral_lssWeight`
(`PV(x) = 1 + (Fx)ᵀM(Fx) + E[(GW)ᵀM(GW)]`) and **`lss_driftV4`**: (V4) for `V` and a petite
set, when compact sets are petite.

**Poisson's equation and the variance.** `isUnit_det_one_sub` (`I − F` is invertible),
`vecMul_inv_one_sub`; `lss_stationary_mean` (`π(c ⬝ x) = 0`); `lss_poissonSeries`: the
solution (17.39) of Poisson's equation for `g(x) = c ⬝ x` is `ĝ(x) = c (I − F)⁻¹ x`;
`lss_variance_integral`; `lssLongRunCov Γ F G = (I − F)⁻¹ G Σ_W Gᵀ (I − Fᵀ)⁻¹` and
`quadForm_lssLongRunCov`; `posSemidef_disturbanceCov`, `posSemidef_lssLongRunCov`.

**Results.**
* **Theorem 17.6.2** (`theorem_17_6_2_vector`, p. 456): (V4) for `V(x) = 1 + xᵀMx`, positive
  Harris recurrence, and for the invariant probability `π` and every `c ∈ ℝⁿ`: `π(c ⬝ x) = 0`,
  `γ_c² = cᵀ (I − F)⁻¹ G Σ_W Gᵀ (I − Fᵀ)⁻¹ c` for the asymptotic variance (17.3) of
  `Yₖ = c ⬝ Xₖ`, and `(1/n) E_π[Sₙ(Y)²] → γ_c²`. The variance is computed through Poisson's
  equation, `γ_c² = π(ĝ² − (Pĝ)²) = E[(ĝ(GW))²]`, rather than through the spectral density
  `D(ω)` of the book: the two agree at `ω = 0`, which is the formula.
* `theorem_17_6_2_vector_clt`: the CLT `n^{−1/2} Σ_{k=1}^n c ⬝ Xₖ ⇒ N(0, γ_c²)` under every
  `P_x`.
* **The vector-valued CLT** after the proof (`theorem_17_6_2_vector_clt_vec`):
  `n^{−1/2} Σ_{k=1}^n Xₖ ⇒ N(0, (I − F)⁻¹ G Σ_W Gᵀ (I − Fᵀ)⁻¹)` under every `P_x`, in
  `EuclideanSpace ℝ (Fin n)`, with Mathlib's `multivariateGaussian` as the limit, by the
  Cramér–Wold theorem; `hasLaw_inner_multivariateGaussian` gives the laws of its projections.
* `lss_irreducible_petite`: under (LCM3), (LSS4) and (LSS5) the model is `ψ`-irreducible and
  compact sets are petite (Proposition 6.3.5).

**Hypotheses.** As for the scalar model (`theorem_17_6_2` in `LimitApplications`),
`ψ`-irreducibility, aperiodicity and petiteness of compact sets are hypotheses. The book takes
all three from (LSS4) and (LCM3) through Proposition 6.3.5; `lss_irreducible_petite` derives the
first and third from them, but aperiodicity is not derived (Proposition 6.3.5 in the project
gives a `ψ`-irreducible T-chain with compact small sets, not aperiodicity). The second moments
are assumed as `E[WᵢWⱼ]` finite, which is the book's `E|W|² < ∞`.

**Not formalised.** The book's statement that the chain is `V`-uniformly ergodic for
`V(x) = |x|² + 1` is proved for `V(x) = 1 + xᵀMx`, which is equivalent
(`|x|² ≤ xᵀMx ≤ Λ|x|²`); the spectral density `D(ω)` for `ω ≠ 0`; the LIL.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology Matrix
open scoped ENNReal NNReal

variable {n p : ℕ}

/-! ### Euclidean and sup norms on `ℝⁿ` -/

/-- `x ⬝ x ≥ 0`. -/
theorem dotProduct_self_nonneg' (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- The square of the sup norm is at most the Euclidean square `x ⬝ x`. -/
theorem sq_norm_le_dotProduct_self (x : Fin n → ℝ) : ‖x‖ ^ 2 ≤ x ⬝ᵥ x := by
  have h0 := dotProduct_self_nonneg' x
  have hle : ‖x‖ ≤ √(x ⬝ᵥ x) := (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => by
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    rw [sq]
    exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  calc ‖x‖ ^ 2 ≤ √(x ⬝ᵥ x) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = x ⬝ᵥ x := Real.sq_sqrt h0

/-- `x ⬝ x ≤ n ‖x‖²`. -/
theorem dotProduct_self_le_sq_norm (x : Fin n → ℝ) : x ⬝ᵥ x ≤ n * ‖x‖ ^ 2 := by
  calc x ⬝ᵥ x = ∑ i, x i * x i := rfl
    _ ≤ ∑ _i : Fin n, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        have h := norm_le_pi_norm x i
        rw [Real.norm_eq_abs] at h
        rw [← sq, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = n * ‖x‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `|v ⬝ y| ≤ (Σᵢ |vᵢ|) ‖y‖`. -/
theorem abs_dotProduct_le (v y : Fin n → ℝ) : |v ⬝ᵥ y| ≤ (∑ i, |v i|) * ‖y‖ := by
  calc |v ⬝ᵥ y| = |∑ i, v i * y i| := rfl
    _ ≤ ∑ i, |v i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| * ‖y‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        have h := norm_le_pi_norm y i
        rw [Real.norm_eq_abs] at h
        exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = (∑ i, |v i|) * ‖y‖ := (Finset.sum_mul _ _ _).symm

/-- Cauchy–Schwarz: `(c ⬝ y)² ≤ (c ⬝ c)(y ⬝ y)`. -/
theorem sq_dotProduct_le (c y : Fin n → ℝ) : (c ⬝ᵥ y) ^ 2 ≤ (c ⬝ᵥ c) * (y ⬝ᵥ y) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c y
  simp only [sq] at h ⊢
  exact h

/-! ### The Lyapunov matrix (12.34) -/

/-- Under (LSS5) the entries of `Fᵏ` decay geometrically: `|(Fᵏ)ᵢⱼ| ≤ C rᵏ` with `r < 1`. -/
theorem abs_pow_apply_le {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ (k : ℕ) (i j : Fin n), |(F ^ k) i j| ≤ C * r ^ k := by
  obtain ⟨C, r, hC, hr0, hr1, h⟩ := isStableMatrix_geometric hF
  refine ⟨C, r, hC, hr0, hr1, fun k i j => ?_⟩
  have e : (F ^ k) i j = ((F ^ k) *ᵥ Pi.single j 1) i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hs : ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => by
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
  calc |(F ^ k) i j| = ‖((F ^ k) *ᵥ Pi.single j 1) i‖ := by rw [e, Real.norm_eq_abs]
    _ ≤ ‖(F ^ k) *ᵥ Pi.single j 1‖ := norm_le_pi_norm _ i
    _ ≤ C * r ^ k * ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ := h k _
    _ ≤ C * r ^ k := mul_le_of_le_one_right (by positivity) hs

/-- The Lyapunov matrix `M = Σₖ (Fᵏ)ᵀ Fᵏ` of (12.34). -/
noncomputable def lyapunovMatrix (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑' k : ℕ, (F ^ k)ᵀ * F ^ k

/-- Under (LSS5) the series defining the Lyapunov matrix converges. -/
theorem summable_lyapunov {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F) :
    Summable fun k : ℕ => (F ^ k)ᵀ * F ^ k := by
  obtain ⟨C, r, hC, hr0, hr1, h⟩ := abs_pow_apply_le hF
  have hg : Summable fun k : ℕ => (n : ℝ) * C ^ 2 * (r ^ 2) ^ k :=
    (summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
  have key : ∀ a b, Summable fun k : ℕ => ((F ^ k)ᵀ * F ^ k) a b := fun a b => by
    refine Summable.of_norm_bounded hg fun k => ?_
    change ‖∑ i, (F ^ k) i a * (F ^ k) i b‖ ≤ _
    calc ‖∑ i, (F ^ k) i a * (F ^ k) i b‖ ≤ ∑ i, ‖(F ^ k) i a * (F ^ k) i b‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, C * r ^ k * (C * r ^ k) := Finset.sum_le_sum fun i _ => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul (h k i a) (h k i b) (abs_nonneg _) (by positivity)
      _ = (n : ℝ) * C ^ 2 * (r ^ 2) ^ k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  exact Pi.summable.2 fun a => Pi.summable.2 fun b => key a b

/-- **The Lyapunov equation** (12.34): under (LSS5), `Fᵀ M F − M = −I`. -/
theorem lyapunov_equation {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F) :
    Fᵀ * lyapunovMatrix F * F - lyapunovMatrix F = -1 := by
  have hs := summable_lyapunov hF
  have h1 : Fᵀ * lyapunovMatrix F * F = ∑' k : ℕ, (F ^ (k + 1))ᵀ * F ^ (k + 1) := by
    rw [lyapunovMatrix, ← hs.tsum_mul_left, ← (hs.mul_left Fᵀ).tsum_mul_right]
    congr 1
    funext k
    rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  have h2 := hs.tsum_eq_zero_add
  rw [h1, lyapunovMatrix, h2, pow_zero, Matrix.transpose_one, Matrix.one_mul]
  abel

/-- The quadratic form of `M`: `xᵀ M x = Σₖ |Fᵏ x|²`. -/
theorem hasSum_quadForm_lyapunov {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (x : Fin n → ℝ) :
    HasSum (fun k : ℕ => ((F ^ k) *ᵥ x) ⬝ᵥ ((F ^ k) *ᵥ x)) (x ⬝ᵥ lyapunovMatrix F *ᵥ x) := by
  let φ : Matrix (Fin n) (Fin n) ℝ →+ ℝ :=
    { toFun := fun A => x ⬝ᵥ A *ᵥ x
      map_zero' := by simp
      map_add' := fun A B => by simp [Matrix.add_mulVec, dotProduct_add] }
  have hφ : Continuous φ :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  have h := (summable_lyapunov hF).hasSum.map φ hφ
  refine h.congr_fun fun k => ?_
  change ((F ^ k) *ᵥ x) ⬝ᵥ ((F ^ k) *ᵥ x) = x ⬝ᵥ ((F ^ k)ᵀ * F ^ k) *ᵥ x
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec x, Matrix.vecMul_transpose]

/-- `xᵀ M x ≥ x ⬝ x` (the term `k = 0`). -/
theorem dotProduct_self_le_quadForm {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (x : Fin n → ℝ) : x ⬝ᵥ x ≤ x ⬝ᵥ lyapunovMatrix F *ᵥ x := by
  have h := le_hasSum (hasSum_quadForm_lyapunov hF x) 0 fun k _ => dotProduct_self_nonneg' _
  simpa using h

/-- `xᵀ M x ≤ Λ (x ⬝ x)` for some `Λ ≥ 1`: `M` is comparable with the identity, so `1 + xᵀMx` and
`1 + |x|²` are equivalent weights. -/
theorem quadForm_le {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ x, x ⬝ᵥ lyapunovMatrix F *ᵥ x ≤ Λ * (x ⬝ᵥ x) := by
  obtain ⟨C, r, hC, hr0, hr1, h⟩ := isStableMatrix_geometric hF
  have hr2 : r ^ 2 < 1 := by nlinarith
  set K : ℝ := (n : ℝ) * C ^ 2 * (1 - r ^ 2)⁻¹ with hK
  refine ⟨max 1 K, le_max_left _ _, fun x => ?_⟩
  have hg : HasSum (fun k : ℕ => (n : ℝ) * C ^ 2 * (x ⬝ᵥ x) * (r ^ 2) ^ k)
      ((n : ℝ) * C ^ 2 * (x ⬝ᵥ x) * (1 - r ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hr2).mul_left _
  have hle := hasSum_le (fun k => ?_) (hasSum_quadForm_lyapunov hF x) hg
  · calc x ⬝ᵥ lyapunovMatrix F *ᵥ x ≤ (n : ℝ) * C ^ 2 * (x ⬝ᵥ x) * (1 - r ^ 2)⁻¹ := hle
      _ = K * (x ⬝ᵥ x) := by rw [hK]; ring
      _ ≤ max 1 K * (x ⬝ᵥ x) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (dotProduct_self_nonneg' x)
  · calc ((F ^ k) *ᵥ x) ⬝ᵥ ((F ^ k) *ᵥ x) ≤ n * ‖(F ^ k) *ᵥ x‖ ^ 2 :=
          dotProduct_self_le_sq_norm _
      _ ≤ n * (C * r ^ k * ‖x‖) ^ 2 := by
          gcongr
          exact h k x
      _ = (n : ℝ) * C ^ 2 * ‖x‖ ^ 2 * (r ^ 2) ^ k := by ring
      _ ≤ (n : ℝ) * C ^ 2 * (x ⬝ᵥ x) * (r ^ 2) ^ k := by
          gcongr
          exact sq_norm_le_dotProduct_self x

/-- The Lyapunov identity on quadratic forms: `(Fx)ᵀ M (Fx) = xᵀ M x − x ⬝ x`. -/
theorem quadForm_lyapunov_mulVec {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (x : Fin n → ℝ) :
    (F *ᵥ x) ⬝ᵥ lyapunovMatrix F *ᵥ (F *ᵥ x) = x ⬝ᵥ lyapunovMatrix F *ᵥ x - x ⬝ᵥ x := by
  have hM : Fᵀ * lyapunovMatrix F * F = lyapunovMatrix F - 1 := by
    rw [← sub_eq_zero, sub_sub_eq_add_sub, ← sub_add_eq_add_sub, lyapunov_equation hF]
    abel
  have e : (F *ᵥ x) ⬝ᵥ lyapunovMatrix F *ᵥ (F *ᵥ x) =
      x ⬝ᵥ (Fᵀ * lyapunovMatrix F * F) *ᵥ x := by
    symm
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec x Fᵀ,
      Matrix.vecMul_transpose]
  rw [e, hM, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]

/-! ### Moments of the disturbance -/

/-- The disturbance `W ∼ Γ` on `ℝᵖ` is centred with finite second moments (MT (LSS2) with
`E[W] = 0`, the standing assumption of §17.6.2): every `Wᵢ` and every `WᵢWⱼ` is integrable and
`E[Wᵢ] = 0`. -/
def HasCentredSecondMoments (Γ : Measure (Fin p → ℝ)) : Prop :=
  (∀ i, Integrable (fun w => w i) Γ) ∧ (∀ i j, Integrable (fun w => w i * w j) Γ) ∧
    ∀ i, ∫ w, w i ∂Γ = 0

/-- The covariance matrix `Σ_W = E[W Wᵀ]` of the disturbance. -/
noncomputable def disturbanceCov (Γ : Measure (Fin p → ℝ)) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => ∫ w, w i * w j ∂Γ

/-- Linear functionals of `W` are integrable. -/
theorem integrable_dotProduct_disturbance {Γ : Measure (Fin p → ℝ)}
    (hW : HasCentredSecondMoments Γ) (v : Fin p → ℝ) : Integrable (fun w => v ⬝ᵥ w) Γ := by
  have e : (fun w : Fin p → ℝ => v ⬝ᵥ w) = fun w => ∑ i, v i * w i := rfl
  rw [e]
  exact integrable_finsetSum _ fun i _ => (hW.1 i).const_mul (v i)

/-- Linear functionals of `W` have mean zero. -/
theorem integral_dotProduct_disturbance {Γ : Measure (Fin p → ℝ)}
    (hW : HasCentredSecondMoments Γ) (v : Fin p → ℝ) : ∫ w, v ⬝ᵥ w ∂Γ = 0 := by
  have e : (fun w : Fin p → ℝ => v ⬝ᵥ w) = fun w => ∑ i, v i * w i := rfl
  rw [e, integral_finsetSum _ fun i _ => (hW.1 i).const_mul (v i)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, hW.2.2 i, mul_zero]

/-- Quadratic polynomials in `W` are integrable. -/
theorem integrable_sum_sum_disturbance {Γ : Measure (Fin p → ℝ)}
    (hW : HasCentredSecondMoments Γ) (a : Fin p → Fin p → ℝ) :
    Integrable (fun w => ∑ i, ∑ j, a i j * (w i * w j)) Γ :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hW.2.1 i j).const_mul _

/-- `E[Σᵢⱼ aᵢⱼ WᵢWⱼ] = Σᵢⱼ aᵢⱼ (Σ_W)ᵢⱼ`. -/
theorem integral_sum_sum_disturbance {Γ : Measure (Fin p → ℝ)}
    (hW : HasCentredSecondMoments Γ) (a : Fin p → Fin p → ℝ) :
    ∫ w, ∑ i, ∑ j, a i j * (w i * w j) ∂Γ = ∑ i, ∑ j, a i j * disturbanceCov Γ i j := by
  rw [integral_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => (hW.2.1 i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hW.2.1 i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

/-- A quadratic form as a double sum. -/
theorem quadForm_eq_sum_sum (B : Matrix (Fin p) (Fin p) ℝ) (w : Fin p → ℝ) :
    w ⬝ᵥ B *ᵥ w = ∑ i, ∑ j, B i j * (w i * w j) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The square of a linear form as a double sum. -/
theorem sq_dotProduct_eq_sum_sum (e w : Fin p → ℝ) :
    (e ⬝ᵥ w) ^ 2 = ∑ i, ∑ j, (e i * e j) * (w i * w j) := by
  rw [sq]
  simp only [dotProduct, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `E[(e ⬝ W)²] = eᵀ Σ_W e`. -/
theorem integral_sq_dotProduct_disturbance {Γ : Measure (Fin p → ℝ)}
    (hW : HasCentredSecondMoments Γ) (e : Fin p → ℝ) :
    ∫ w, (e ⬝ᵥ w) ^ 2 ∂Γ = e ⬝ᵥ disturbanceCov Γ *ᵥ e := by
  simp_rw [sq_dotProduct_eq_sum_sum]
  rw [integral_sum_sum_disturbance hW]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### One step of the model -/

/-- `∫ φ(y) P(x, dy) = E[φ(F x + G W)]` for the LSS(F, G) model. -/
theorem integral_lssMatrixKernel (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Measurable φ) (x : Fin n → ℝ) :
    ∫ y, φ y ∂lssMatrixKernel Γ F G x = ∫ w, φ (F *ᵥ x + G *ᵥ w) ∂Γ := by
  have hs : Measurable fun w : Fin p → ℝ => F *ᵥ (x, w).1 + G *ᵥ (x, w).2 :=
    (measurable_lssMatrixStep F G).comp measurable_prodMk_left
  rw [lssMatrixKernel, recursionKernel_apply Γ (measurable_lssMatrixStep F G) x,
    integral_map hs.aemeasurable hφ.aestronglyMeasurable]

/-- `∫⁻ φ(y) P(x, dy) = E[φ(F x + G W)]` for the LSS(F, G) model. -/
theorem lintegral_lssMatrixKernel (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) {φ : (Fin n → ℝ) → ℝ≥0∞}
    (hφ : Measurable φ) (x : Fin n → ℝ) :
    ∫⁻ y, φ y ∂lssMatrixKernel Γ F G x = ∫⁻ w, φ (F *ᵥ x + G *ᵥ w) ∂Γ := by
  have hs : Measurable fun w : Fin p → ℝ => F *ᵥ (x, w).1 + G *ᵥ (x, w).2 :=
    (measurable_lssMatrixStep F G).comp measurable_prodMk_left
  rw [lssMatrixKernel, recursionKernel_apply Γ (measurable_lssMatrixStep F G) x,
    lintegral_map hφ hs]

/-- `d ⬝ (u + G w) = d ⬝ u + (dᵀ G) ⬝ w`. -/
theorem dotProduct_add_mulVec (d u : Fin n → ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (w : Fin p → ℝ) : d ⬝ᵥ (u + G *ᵥ w) = d ⬝ᵥ u + (d ᵥ* G) ⬝ᵥ w := by
  rw [dotProduct_add, dotProduct_mulVec]

/-- Expansion of a quadratic form along `u + G w`. -/
theorem quadForm_add_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) (w : Fin p → ℝ) :
    (u + G *ᵥ w) ⬝ᵥ A *ᵥ (u + G *ᵥ w) =
      u ⬝ᵥ A *ᵥ u + (u ᵥ* (A * G) + (A *ᵥ u) ᵥ* G) ⬝ᵥ w + w ⬝ᵥ (Gᵀ * A * G) *ᵥ w := by
  have h1 : u ⬝ᵥ A *ᵥ (G *ᵥ w) = (u ᵥ* (A * G)) ⬝ᵥ w := by
    rw [Matrix.mulVec_mulVec, dotProduct_mulVec]
  have h2 : (G *ᵥ w) ⬝ᵥ A *ᵥ u = ((A *ᵥ u) ᵥ* G) ⬝ᵥ w := by
    rw [dotProduct_comm, dotProduct_mulVec]
  have h3 : (G *ᵥ w) ⬝ᵥ A *ᵥ (G *ᵥ w) = w ⬝ᵥ (Gᵀ * A * G) *ᵥ w := by
    symm
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec w Gᵀ,
      Matrix.vecMul_transpose]
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, h1, h2, h3,
    add_dotProduct]
  ring

/-! ### (V4) for `V(x) = 1 + xᵀ M x` -/

/-- The weight `V(x) = 1 + xᵀ M x` of the proof of Theorem 17.6.2 (MT p. 456, from (12.34)). -/
noncomputable def lssWeight (F : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 + x ⬝ᵥ lyapunovMatrix F *ᵥ x)

/-- `V` is continuous, hence measurable. -/
theorem measurable_lssWeight (F : Matrix (Fin n) (Fin n) ℝ) : Measurable (lssWeight F) :=
  (continuous_const.add (continuous_id.dotProduct
    (continuous_const.matrix_mulVec continuous_id))).measurable.ennreal_ofReal

/-- `xᵀ M x ≥ 0`. -/
theorem quadForm_lyapunov_nonneg {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ lyapunovMatrix F *ᵥ x :=
  (dotProduct_self_nonneg' x).trans (dotProduct_self_le_quadForm hF x)

/-- `V ≥ 1`. -/
theorem one_le_lssWeight {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (x : Fin n → ℝ) : 1 ≤ lssWeight F x :=
  ENNReal.one_le_ofReal.2 (le_add_of_nonneg_right (quadForm_lyapunov_nonneg hF x))

/-- `V` is finite. -/
theorem lssWeight_ne_top (F : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : lssWeight F x ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- The one-step mean of `V`: `PV(x) = 1 + (Fx)ᵀ M (Fx) + E[(GW)ᵀ M (GW)]` for a centred `W`. -/
theorem lintegral_lssWeight (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hW : HasCentredSecondMoments Γ) {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (G : Matrix (Fin n) (Fin p) ℝ) (x : Fin n → ℝ) :
    ∫⁻ y, lssWeight F y ∂lssMatrixKernel Γ F G x =
      ENNReal.ofReal (1 + (F *ᵥ x) ⬝ᵥ lyapunovMatrix F *ᵥ (F *ᵥ x) +
        ∫ w, w ⬝ᵥ (Gᵀ * lyapunovMatrix F * G) *ᵥ w ∂Γ) := by
  set M := lyapunovMatrix F
  set u := F *ᵥ x
  rw [lintegral_lssMatrixKernel Γ F G (measurable_lssWeight F)]
  have hB : Integrable (fun w => w ⬝ᵥ (Gᵀ * M * G) *ᵥ w) Γ := by
    simp_rw [quadForm_eq_sum_sum]
    exact integrable_sum_sum_disturbance hW _
  have hL := integrable_dotProduct_disturbance hW (u ᵥ* (M * G) + (M *ᵥ u) ᵥ* G)
  have hfun : (fun w => 1 + (u + G *ᵥ w) ⬝ᵥ M *ᵥ (u + G *ᵥ w)) = fun w =>
      (1 + u ⬝ᵥ M *ᵥ u) + ((u ᵥ* (M * G) + (M *ᵥ u) ᵥ* G) ⬝ᵥ w + w ⬝ᵥ (Gᵀ * M * G) *ᵥ w) := by
    funext w
    rw [quadForm_add_mulVec]
    ring
  have hint : Integrable (fun w => 1 + (u + G *ᵥ w) ⬝ᵥ M *ᵥ (u + G *ᵥ w)) Γ := by
    rw [hfun]; exact (integrable_const _).add (hL.add hB)
  have hnn : 0 ≤ᵐ[Γ] fun w => 1 + (u + G *ᵥ w) ⬝ᵥ M *ᵥ (u + G *ᵥ w) :=
    Eventually.of_forall fun w => by
      have := quadForm_lyapunov_nonneg hF (u + G *ᵥ w)
      change 0 ≤ 1 + _
      linarith
  change ∫⁻ w, ENNReal.ofReal (1 + (u + G *ᵥ w) ⬝ᵥ M *ᵥ (u + G *ᵥ w)) ∂Γ = _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hfun]
  congr 1
  have hLB : Integrable (fun w => (u ᵥ* (M * G) + (M *ᵥ u) ᵥ* G) ⬝ᵥ w +
      w ⬝ᵥ (Gᵀ * M * G) *ᵥ w) Γ := hL.add hB
  rw [integral_add (integrable_const _) hLB, integral_add hL hB, integral_const,
    probReal_univ, one_smul, integral_dotProduct_disturbance hW, zero_add]

/-- **(V4) for the vector linear model** (MT p. 456, through (12.34)): under (LSS5), with a
centred square-integrable disturbance and compact sets petite, `V(x) = 1 + xᵀ M x` satisfies
(V4) for a petite set. With `M` the Lyapunov matrix, `PV(x) = V(x) − |x|² + E[(GW)ᵀM(GW)]` and
`|x|² ≥ xᵀMx/Λ`. -/
theorem lss_driftV4 (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hW : HasCentredSecondMoments Γ) {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (G : Matrix (Fin n) (Fin p) ℝ)
    (hcpt : ∀ K : Set (Fin n → ℝ), IsCompact K → IsPetite (lssMatrixKernel Γ F G) K) :
    haveI := isMarkovKernel_lssMatrixKernel Γ F G
    ∃ ρ c : ℝ≥0∞, ρ < 1 ∧ c ≠ ∞ ∧ ∃ C, IsPetite (lssMatrixKernel Γ F G) C ∧
      DriftV4 (lssMatrixKernel Γ F G) (lssWeight F) ρ c C := by
  have := isMarkovKernel_lssMatrixKernel Γ F G
  set M := lyapunovMatrix F with hMdef
  obtain ⟨Λ, hΛ1, hΛ⟩ := quadForm_le hF
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ1
  set K := ∫ w, w ⬝ᵥ (Gᵀ * M * G) *ᵥ w ∂Γ
  have hU : IsUnboundedOffPetite (lssMatrixKernel Γ F G) (lssWeight F) := by
    intro ℓ hℓ
    refine (hcpt (Metric.closedBall 0 √ℓ.toReal) (isCompact_closedBall _ _)).subset
      (measurableSet_le (measurable_lssWeight F) measurable_const) fun x hx => ?_
    have h1 : 1 + x ⬝ᵥ M *ᵥ x ≤ ℓ.toReal := (ENNReal.ofReal_le_iff_le_toReal hℓ).1 hx
    have h2 : ‖x‖ ^ 2 ≤ ℓ.toReal := by
      linarith [sq_norm_le_dotProduct_self x, dotProduct_self_le_quadForm hF x]
    rw [mem_closedBall_zero_iff]
    simpa [abs_norm] using Real.abs_le_sqrt h2
  refine (lemma_15_2_8 (measurable_lssWeight F) (one_le_lssWeight hF)).2
    ⟨hU, ENNReal.ofReal (1 - Λ⁻¹), ENNReal.ofReal (Λ⁻¹ + K),
      ENNReal.ofReal_lt_one.2 (by linarith [inv_pos.2 hΛ0]), ENNReal.ofReal_ne_top,
      fun x => ?_⟩
  rw [lintegral_lssWeight Γ hW hF G x, quadForm_lyapunov_mulVec hF x]
  have hle : Λ⁻¹ * (x ⬝ᵥ M *ᵥ x) ≤ x ⬝ᵥ x := by
    rw [inv_mul_le_iff₀ hΛ0]; exact hΛ x
  have hQ := quadForm_lyapunov_nonneg hF x
  have hinv : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ1
  have hreal : 1 + (x ⬝ᵥ M *ᵥ x - x ⬝ᵥ x) + K ≤
      (1 - Λ⁻¹) * (1 + x ⬝ᵥ M *ᵥ x) + (Λ⁻¹ + K) := by nlinarith
  calc ENNReal.ofReal (1 + (x ⬝ᵥ M *ᵥ x - x ⬝ᵥ x) + K)
      ≤ ENNReal.ofReal ((1 - Λ⁻¹) * (1 + x ⬝ᵥ M *ᵥ x) + (Λ⁻¹ + K)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal ((1 - Λ⁻¹) * (1 + x ⬝ᵥ M *ᵥ x)) + ENNReal.ofReal (Λ⁻¹ + K) :=
        ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (1 - Λ⁻¹) * lssWeight F x + ENNReal.ofReal (Λ⁻¹ + K) := by
        rw [ENNReal.ofReal_mul (by linarith)]
        rfl

/-! ### Linear and quadratic functionals of the state -/

/-- `(c ⬝ y)² ≤ (1 + c ⬝ c) V(y)` and `|c ⬝ y| ≤ (1 + c ⬝ c) V(y)`, as real numbers. -/
theorem sq_dotProduct_le_weight {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (c y : Fin n → ℝ) :
    (c ⬝ᵥ y) ^ 2 ≤ (1 + c ⬝ᵥ c) * (1 + y ⬝ᵥ lyapunovMatrix F *ᵥ y) ∧
      |c ⬝ᵥ y| ≤ (1 + c ⬝ᵥ c) * (1 + y ⬝ᵥ lyapunovMatrix F *ᵥ y) := by
  have h1 := sq_dotProduct_le c y
  have h2 := dotProduct_self_le_quadForm hF y
  have hc := dotProduct_self_nonneg' c
  have hy := dotProduct_self_nonneg' y
  have h3 : (c ⬝ᵥ c) * (y ⬝ᵥ y) ≤ (c ⬝ᵥ c) * (y ⬝ᵥ lyapunovMatrix F *ᵥ y) :=
    mul_le_mul_of_nonneg_left h2 hc
  have h4 : |c ⬝ᵥ y| ≤ 1 + (c ⬝ᵥ y) ^ 2 := by
    nlinarith [abs_nonneg (c ⬝ᵥ y), sq_abs (c ⬝ᵥ y)]
  constructor <;> nlinarith

/-- The same bounds in `ℝ≥0∞`, against the weight `V`. -/
theorem ofReal_sq_dotProduct_le_weight {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (c y : Fin n → ℝ) :
    ENNReal.ofReal ((c ⬝ᵥ y) ^ 2) ≤ ENNReal.ofReal (1 + c ⬝ᵥ c) * lssWeight F y ∧
      ENNReal.ofReal |c ⬝ᵥ y| ≤ ENNReal.ofReal (1 + c ⬝ᵥ c) * lssWeight F y := by
  have hc : 0 ≤ 1 + c ⬝ᵥ c := by linarith [dotProduct_self_nonneg' c]
  obtain ⟨h1, h2⟩ := sq_dotProduct_le_weight hF c y
  rw [lssWeight, ← ENNReal.ofReal_mul hc]
  exact ⟨ENNReal.ofReal_le_ofReal h1, ENNReal.ofReal_le_ofReal h2⟩

/-- A function dominated by a multiple of `V` is integrable for a measure with `μ(V) < ∞`. -/
theorem integrable_of_le_lssWeight {F : Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Fin n → ℝ)}
    (hμ : ∫⁻ y, lssWeight F y ∂μ ≠ ∞) {g : (Fin n → ℝ) → ℝ} (hgm : Measurable g) {K : ℝ≥0∞}
    (hK : K ≠ ∞) (hg : ∀ y, ENNReal.ofReal |g y| ≤ K * lssWeight F y) : Integrable g μ := by
  refine ⟨hgm.aestronglyMeasurable, ?_⟩
  change ∫⁻ y, ‖g y‖ₑ ∂μ < ∞
  calc ∫⁻ y, ‖g y‖ₑ ∂μ ≤ ∫⁻ y, K * lssWeight F y ∂μ :=
        lintegral_mono fun y => by rw [Real.enorm_eq_ofReal_abs]; exact hg y
    _ = K * ∫⁻ y, lssWeight F y ∂μ := lintegral_const_mul _ (measurable_lssWeight F)
    _ < ∞ := ENNReal.mul_lt_top hK.lt_top hμ.lt_top

/-- `c ⬝ y` and `(c ⬝ y)²` are integrable for a measure with `μ(V) < ∞`. -/
theorem integrable_dotProduct_of_lssWeight {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    {μ : Measure (Fin n → ℝ)} (hμ : ∫⁻ y, lssWeight F y ∂μ ≠ ∞) (c : Fin n → ℝ) :
    Integrable (fun y => c ⬝ᵥ y) μ ∧ Integrable (fun y => (c ⬝ᵥ y) ^ 2) μ := by
  have hm : Measurable fun y : Fin n → ℝ => c ⬝ᵥ y :=
    (continuous_const.dotProduct continuous_id).measurable
  refine ⟨integrable_of_le_lssWeight hμ hm ENNReal.ofReal_ne_top fun y =>
    (ofReal_sq_dotProduct_le_weight hF c y).2,
    integrable_of_le_lssWeight hμ (hm.pow_const 2) (K := ENNReal.ofReal (1 + c ⬝ᵥ c))
    ENNReal.ofReal_ne_top fun y => ?_⟩
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (ofReal_sq_dotProduct_le_weight hF c y).1

/-- One step of a linear functional: `∫ c ⬝ y P(x, dy) = c ⬝ F x` (`E[W] = 0`). -/
theorem integral_dotProduct_lss (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hW : HasCentredSecondMoments Γ) (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) (c x : Fin n → ℝ) :
    ∫ y, c ⬝ᵥ y ∂lssMatrixKernel Γ F G x = c ⬝ᵥ F *ᵥ x := by
  rw [integral_lssMatrixKernel Γ F G (φ := fun y => c ⬝ᵥ y)
    (continuous_const.dotProduct continuous_id).measurable]
  simp_rw [dotProduct_add_mulVec]
  rw [integral_add (integrable_const _) (integrable_dotProduct_disturbance hW _), integral_const,
    probReal_univ, one_smul, integral_dotProduct_disturbance hW, add_zero]

/-- One step of a squared linear functional:
`∫ (d ⬝ y)² P(x, dy) = (d ⬝ F x)² + (dᵀG) Σ_W (dᵀG)ᵀ`. -/
theorem integral_sq_dotProduct_lss (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hW : HasCentredSecondMoments Γ) (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) (d x : Fin n → ℝ) :
    ∫ y, (d ⬝ᵥ y) ^ 2 ∂lssMatrixKernel Γ F G x =
      (d ⬝ᵥ F *ᵥ x) ^ 2 + (d ᵥ* G) ⬝ᵥ disturbanceCov Γ *ᵥ (d ᵥ* G) := by
  rw [integral_lssMatrixKernel Γ F G (φ := fun y => (d ⬝ᵥ y) ^ 2)
    ((continuous_const.dotProduct continuous_id).measurable.pow_const 2)]
  set a := d ⬝ᵥ F *ᵥ x
  set e := d ᵥ* G
  have hfun : (fun w => (d ⬝ᵥ (F *ᵥ x + G *ᵥ w)) ^ 2) =
      fun w => a ^ 2 + (2 * a * (e ⬝ᵥ w) + (e ⬝ᵥ w) ^ 2) := by
    funext w
    rw [dotProduct_add_mulVec]
    ring
  have hL : Integrable (fun w => 2 * a * (e ⬝ᵥ w)) Γ :=
    (integrable_dotProduct_disturbance hW e).const_mul _
  have hQ : Integrable (fun w => (e ⬝ᵥ w) ^ 2) Γ := by
    simp_rw [sq_dotProduct_eq_sum_sum]
    exact integrable_sum_sum_disturbance hW _
  have hLQ : Integrable (fun w => 2 * a * (e ⬝ᵥ w) + (e ⬝ᵥ w) ^ 2) Γ := hL.add hQ
  rw [hfun, integral_add (integrable_const _) hLQ, integral_add hL hQ, integral_const,
    probReal_univ, one_smul, integral_const_mul, integral_dotProduct_disturbance hW,
    mul_zero, zero_add, integral_sq_dotProduct_disturbance hW]

/-- Under (LSS5), `I − F` is invertible: if `(I − F) v = 0` then `Fᵏ v = v → 0`. -/
theorem isUnit_det_one_sub {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F) :
    IsUnit (1 - F).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hFv : F *ᵥ v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv.symm
  have hk : ∀ k : ℕ, (F ^ k) *ᵥ v = v := fun k => by
    induction k with
    | zero => rw [pow_zero, Matrix.one_mulVec]
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hFv, ih]
  obtain ⟨C, r, hC, hr0, hr1, h⟩ := isStableMatrix_geometric hF
  have ht : Tendsto (fun k : ℕ => C * r ^ k * ‖v‖) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul C
    simpa using this.mul_const ‖v‖
  have hle : ‖v‖ ≤ 0 := ge_of_tendsto' ht fun k => by
    have := h k v
    rwa [hk k] at this
  exact hv0 (norm_le_zero_iff.1 hle)

/-- `d = c (I − F)⁻¹` solves `d − dF = c`. -/
theorem vecMul_inv_one_sub {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (c : Fin n → ℝ) : c ᵥ* (1 - F)⁻¹ - (c ᵥ* (1 - F)⁻¹) ᵥ* F = c := by
  have h := Matrix.nonsing_inv_mul (1 - F) (isUnit_det_one_sub hF)
  have e : (c ᵥ* (1 - F)⁻¹) ᵥ* (1 - F) = c := by
    rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
  rw [Matrix.vecMul_sub, Matrix.vecMul_one] at e
  exact e

/-- `∫ c ⬝ y Pᵏ(x, dy) = c ⬝ Fᵏ x`, when every `Pᵏ(x, ·)` integrates `V`. -/
theorem integral_dotProduct_lss_pow (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hW : HasCentredSecondMoments Γ) {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (G : Matrix (Fin n) (Fin p) ℝ)
    (hV : ∀ (k : ℕ) (x : Fin n → ℝ),
      ∫⁻ y, lssWeight F y ∂(lssMatrixKernel Γ F G ^ k : Kernel _ _) x ≠ ∞)
    (k : ℕ) (c x : Fin n → ℝ) :
    ∫ y, c ⬝ᵥ y ∂(lssMatrixKernel Γ F G ^ k : Kernel _ _) x = c ⬝ᵥ (F ^ k) *ᵥ x := by
  have := isMarkovKernel_lssMatrixKernel Γ F G
  induction k generalizing c x with
  | zero =>
    rw [pow_zero_apply, integral_dirac, pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    have := isMarkovKernel_pow (lssMatrixKernel Γ F G) k
    have hi := (integrable_dotProduct_of_lssWeight hF (hV (k + 1) x) c).1
    rw [pow_succ] at hi ⊢
    change ∫ y, c ⬝ᵥ y ∂((lssMatrixKernel Γ F G ^ k : Kernel _ _) ∘ₖ
      lssMatrixKernel Γ F G) x = _
    rw [Kernel.integral_comp hi]
    simp_rw [ih c]
    simp_rw [dotProduct_mulVec c (F ^ k)]
    rw [integral_dotProduct_lss Γ hW F G, ← dotProduct_mulVec, Matrix.mulVec_mulVec, pow_succ]

/-! ### The stationary mean, Poisson's equation and the asymptotic variance -/

/-- The invariant probability has mean zero: `∫ c ⬝ y π(dy) = 0` for every `c` (from
`π(c ⬝ y) = π((cF) ⬝ y)` and `c = d − dF`). -/
theorem lss_stationary_mean (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hW : HasCentredSecondMoments Γ) {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (G : Matrix (Fin n) (Fin p) ℝ) {π : Measure (Fin n → ℝ)} [IsProbabilityMeasure π]
    (hπ : IsInvariant (lssMatrixKernel Γ F G) π) (hπV : ∫⁻ y, lssWeight F y ∂π ≠ ∞)
    (c : Fin n → ℝ) : ∫ y, c ⬝ᵥ y ∂π = 0 := by
  have := isMarkovKernel_lssMatrixKernel Γ F G
  have hstep : ∀ v : Fin n → ℝ, ∫ y, v ⬝ᵥ y ∂π = ∫ y, (v ᵥ* F) ⬝ᵥ y ∂π := fun v => by
    have hi := (integrable_dotProduct_of_lssWeight hF hπV v).1
    conv_lhs => rw [← hπ]
    rw [integral_measure_comp _ _ (by rw [hπ]; exact hi)]
    simp_rw [integral_dotProduct_lss Γ hW F G, dotProduct_mulVec]
  have hd := vecMul_inv_one_sub hF c
  rw [← hd]
  simp_rw [sub_dotProduct]
  rw [integral_sub (integrable_dotProduct_of_lssWeight hF hπV _).1
    (integrable_dotProduct_of_lssWeight hF hπV _).1, hstep (c ᵥ* (1 - F)⁻¹), sub_self]

/-- **Poisson's equation for linear functionals**: the solution (17.39) for `g(x) = c ⬝ x` is
`ĝ(x) = c (I − F)⁻¹ x`, the telescoping sum of `c Fᵏ x = d Fᵏ x − d Fᵏ⁺¹ x`, `d = c (I − F)⁻¹`. -/
theorem lss_poissonSeries (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hW : HasCentredSecondMoments Γ) {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (G : Matrix (Fin n) (Fin p) ℝ)
    (hV : ∀ (k : ℕ) (x : Fin n → ℝ),
      ∫⁻ y, lssWeight F y ∂(lssMatrixKernel Γ F G ^ k : Kernel _ _) x ≠ ∞)
    {π : Measure (Fin n → ℝ)} {c : Fin n → ℝ} (hm : ∫ y, c ⬝ᵥ y ∂π = 0) :
    poissonSeries (lssMatrixKernel Γ F G) π (fun y => c ⬝ᵥ y) =
      fun x => (c ᵥ* (1 - F)⁻¹) ⬝ᵥ x := by
  funext x
  have hd := vecMul_inv_one_sub hF c
  obtain ⟨C, r, hC, hr0, hr1, h⟩ := isStableMatrix_geometric hF
  set d := c ᵥ* (1 - F)⁻¹ with hddef
  set a : ℕ → ℝ := fun k => d ⬝ᵥ (F ^ k) *ᵥ x with ha
  have hterm : ∀ k : ℕ, (∫ y, c ⬝ᵥ y ∂(lssMatrixKernel Γ F G ^ k : Kernel _ _) x -
      ∫ y, c ⬝ᵥ y ∂π) = a k - a (k + 1) := fun k => by
    rw [integral_dotProduct_lss_pow Γ hW hF G hV k c x, hm, sub_zero]
    conv_lhs => rw [← hd]
    rw [sub_dotProduct, ← dotProduct_mulVec d F, Matrix.mulVec_mulVec, ← pow_succ']
  have hbound : ∀ k, ‖a k‖ ≤ (∑ i, |d i|) * (C * ‖x‖) * r ^ k := fun k => by
    rw [Real.norm_eq_abs]
    calc |a k| ≤ (∑ i, |d i|) * ‖(F ^ k) *ᵥ x‖ := abs_dotProduct_le _ _
      _ ≤ (∑ i, |d i|) * (C * r ^ k * ‖x‖) :=
          mul_le_mul_of_nonneg_left (h k x) (Finset.sum_nonneg fun i _ => abs_nonneg _)
      _ = (∑ i, |d i|) * (C * ‖x‖) * r ^ k := by ring
  have hgeo : Summable fun k : ℕ => (∑ i, |d i|) * (C * ‖x‖) * r ^ k :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_left _
  have hsa : Summable a := Summable.of_norm_bounded hgeo hbound
  have hs : Summable fun k => a k - a (k + 1) := hsa.sub ((summable_nat_add_iff 1).2 hsa)
  have hsum : HasSum (fun k => a k - a (k + 1)) (a 0) := by
    rw [hs.hasSum_iff_tendsto_nat]
    have e : (fun N => ∑ i ∈ Finset.range N, (a i - a (i + 1))) = fun N => a 0 - a N :=
      funext fun N => Finset.sum_range_sub' a N
    rw [e]
    simpa using (tendsto_const_nhds (x := a 0)).sub hsa.tendsto_atTop_zero
  rw [poissonSeries]
  simp_rw [hterm]
  rw [hsum.tsum_eq]
  simp only [ha, pow_zero, Matrix.one_mulVec]

/-- The stationary identity behind the variance: for invariant `π` with `π(V) < ∞`,
`∫ ((d ⬝ x)² − (d ⬝ Fx)²) π(dx) = (dᵀG) Σ_W (dᵀG)ᵀ`. -/
theorem lss_variance_integral (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hW : HasCentredSecondMoments Γ) {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (G : Matrix (Fin n) (Fin p) ℝ) {π : Measure (Fin n → ℝ)} [IsProbabilityMeasure π]
    (hπ : IsInvariant (lssMatrixKernel Γ F G) π) (hπV : ∫⁻ y, lssWeight F y ∂π ≠ ∞)
    (d : Fin n → ℝ) :
    ∫ x, ((d ⬝ᵥ x) ^ 2 - (d ⬝ᵥ F *ᵥ x) ^ 2) ∂π =
      (d ᵥ* G) ⬝ᵥ disturbanceCov Γ *ᵥ (d ᵥ* G) := by
  have := isMarkovKernel_lssMatrixKernel Γ F G
  have h1 := (integrable_dotProduct_of_lssWeight hF hπV d).2
  have h2 : Integrable (fun x => (d ⬝ᵥ F *ᵥ x) ^ 2) π := by
    simp_rw [dotProduct_mulVec d F]
    exact (integrable_dotProduct_of_lssWeight hF hπV (d ᵥ* F)).2
  rw [integral_sub h1 h2]
  have hinv : ∫ x, (d ⬝ᵥ x) ^ 2 ∂π =
      ∫ x, (d ⬝ᵥ F *ᵥ x) ^ 2 ∂π + (d ᵥ* G) ⬝ᵥ disturbanceCov Γ *ᵥ (d ᵥ* G) := by
    conv_lhs => rw [← hπ]
    rw [integral_measure_comp _ _ (by rw [hπ]; exact h1)]
    simp_rw [integral_sq_dotProduct_lss Γ hW F G d]
    rw [integral_add h2 (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [hinv]
  ring

/-- The long-run covariance `Σ = (I − F)⁻¹ G Σ_W Gᵀ (I − Fᵀ)⁻¹` (MT p. 456), the value at
frequency `0` of the spectral density of the stationary process. -/
noncomputable def lssLongRunCov (Γ : Measure (Fin p → ℝ)) (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - F)⁻¹ * G * disturbanceCov Γ * Gᵀ * (1 - Fᵀ)⁻¹

/-- With `d = c (I − F)⁻¹`: `(dG) Σ_W (dG)ᵀ = cᵀ (I − F)⁻¹ G Σ_W Gᵀ (I − Fᵀ)⁻¹ c`. -/
theorem quadForm_lssLongRunCov (Γ : Measure (Fin p → ℝ)) (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) (c : Fin n → ℝ) :
    ((c ᵥ* (1 - F)⁻¹) ᵥ* G) ⬝ᵥ disturbanceCov Γ *ᵥ ((c ᵥ* (1 - F)⁻¹) ᵥ* G) =
      c ⬝ᵥ lssLongRunCov Γ F G *ᵥ c := by
  have hAT : (1 - Fᵀ)⁻¹ = ((1 - F)⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one]
  rw [lssLongRunCov, hAT, Matrix.vecMul_vecMul, ← dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-! ### Theorem 17.6.2 for the vector model -/

/-- (V4) is preserved by a constant factor `K`: `P(KV) ≤ ρ (KV) + K b 1_C`. -/
theorem DriftV4.const_mul' {X : Type*} [MeasurableSpace X] {P : Kernel X X} {V : X → ℝ≥0∞}
    {ρ b : ℝ≥0∞} {C : Set X} (h : DriftV4 P V ρ b C) (hV : Measurable V) (K : ℝ≥0∞) :
    DriftV4 P (fun x => K * V x) ρ (K * b) C := fun x => by
  rw [lintegral_const_mul _ hV]
  have hi : K * C.indicator (fun _ => b) x = C.indicator (fun _ => K * b) x := by
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  calc K * ∫⁻ y, V y ∂P x ≤ K * (ρ * V x + C.indicator (fun _ => b) x) := by gcongr; exact h x
    _ = ρ * (K * V x) + C.indicator (fun _ => K * b) x := by rw [mul_add, hi, mul_left_comm]

/-- **Theorem 17.6.2** (MT p. 456) for the vector linear model `Xₖ₊₁ = F Xₖ + G Wₖ₊₁` on `ℝⁿ`:
under the eigenvalue condition (LSS5), a centred square-integrable disturbance, and
`ψ`-irreducibility, aperiodicity and petiteness of compact sets (see
`lss_irreducible_petite`), (V4) holds for `V(x) = 1 + xᵀMx` and a petite set, the chain is
positive Harris, and for its invariant probability `π` and every `c ∈ ℝⁿ`, `Yₖ = c ⬝ Xₖ` has
`π(Y) = 0`, asymptotic variance (17.3)
`γ_c² = cᵀ (I − F)⁻¹ G Σ_W Gᵀ (I − Fᵀ)⁻¹ c`, and `(1/n) E_π[Sₙ(Y)²] → γ_c²`. -/
theorem theorem_17_6_2_vector (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hW : HasCentredSecondMoments Γ) {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (G : Matrix (Fin n) (Fin p) ℝ) {ψ : Measure (Fin n → ℝ)}
    (hψ : haveI := isMarkovKernel_lssMatrixKernel Γ F G
      IsMaximalIrreducibility (lssMatrixKernel Γ F G) ψ)
    (hap : IsAperiodic (lssMatrixKernel Γ F G) ψ)
    (hcpt : ∀ K : Set (Fin n → ℝ), IsCompact K → IsPetite (lssMatrixKernel Γ F G) K) :
    haveI := isMarkovKernel_lssMatrixKernel Γ F G
    (∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧ ∃ C, IsPetite (lssMatrixKernel Γ F G) C ∧
      DriftV4 (lssMatrixKernel Γ F G) (lssWeight F) ρ b C) ∧
    IsPositiveHarris (lssMatrixKernel Γ F G) ψ ∧
    ∀ (π : Measure (Fin n → ℝ)) [IsProbabilityMeasure π],
      IsInvariant (lssMatrixKernel Γ F G) π → ∀ c : Fin n → ℝ,
        ∫ y, c ⬝ᵥ y ∂π = 0 ∧
        asymptoticVariance (lssMatrixKernel Γ F G) π (fun y => c ⬝ᵥ y) =
          c ⬝ᵥ lssLongRunCov Γ F G *ᵥ c ∧
        Tendsto (fun m : ℕ => (∫ ω, pathSum (fun y => c ⬝ᵥ y) m ω ^ 2
          ∂pathMeasure (lssMatrixKernel Γ F G) π) / m) atTop
          (𝓝 (c ⬝ᵥ lssLongRunCov Γ F G *ᵥ c)) := by
  have := isMarkovKernel_lssMatrixKernel Γ F G
  obtain ⟨ρ, b, hρ, hb, C, hC, hdrift⟩ := lss_driftV4 Γ hW hF G hcpt
  have hVm := measurable_lssWeight F
  have hV1 := one_le_lssWeight hF
  have hVfin := lssWeight_ne_top F
  have hph := isPositiveHarris_of_driftV4 hψ hVm hV1 hVfin hρ hb hC hdrift
  refine ⟨⟨ρ, b, hρ, hb, C, hC, hdrift⟩, hph, fun π _ hπ c => ?_⟩
  obtain ⟨-, hgeo⟩ := geometric_ergodic_of_driftV4 hψ hap hVm hV1 hρ hb hC hdrift (hVfin 0)
  have hπV := (hgeo π hπ).1
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hPV : ∀ (k : ℕ) (x : Fin n → ℝ),
      ∫⁻ y, lssWeight F y ∂(lssMatrixKernel Γ F G ^ k : Kernel _ _) x ≠ ∞ := fun k x =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hVfin x, ENNReal.mul_ne_top hb
      (ENNReal.natCast_ne_top k)⟩) (hdrift.pow_le hVm hρ.le hCm k x)
  have hm := lss_stationary_mean Γ hW hF G hπ hπV c
  set K := ENNReal.ofReal (1 + c ⬝ᵥ c) with hK
  have hK1 : 1 ≤ K := ENNReal.one_le_ofReal.2 (le_add_of_nonneg_right (dotProduct_self_nonneg' c))
  have hV'1 : ∀ x, 1 ≤ K * lssWeight F x := fun x =>
    calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ K * lssWeight F x := mul_le_mul' hK1 (hV1 x)
  have hV'fin : ∀ x, K * lssWeight F x ≠ ∞ := fun x =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hVfin x)
  have hg : ∀ x, ENNReal.ofReal ((fun y => c ⬝ᵥ y) x ^ 2) ≤ K * lssWeight F x := fun x =>
    (ofReal_sq_dotProduct_le_weight hF c x).1
  obtain ⟨-, -, -, h4, -, h6, -⟩ := theorem_17_5_4 hph hap (hVm.const_mul K) hV'1 hV'fin hρ
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb) hC (hdrift.const_mul' hVm K) hπ
    (g := fun y => c ⬝ᵥ y) (continuous_const.dotProduct continuous_id).measurable hg
  have hps := lss_poissonSeries Γ hW hF G hPV hm
  have hki : kernelInt (lssMatrixKernel Γ F G) (fun y => (c ᵥ* (1 - F)⁻¹) ⬝ᵥ y) =
      fun x => (c ᵥ* (1 - F)⁻¹) ⬝ᵥ F *ᵥ x :=
    funext fun x => integral_dotProduct_lss Γ hW F G _ x
  have hvar : ∫ x, (poissonSeries (lssMatrixKernel Γ F G) π (fun y => c ⬝ᵥ y) x ^ 2 -
      kernelInt (lssMatrixKernel Γ F G)
        (poissonSeries (lssMatrixKernel Γ F G) π (fun y => c ⬝ᵥ y)) x ^ 2) ∂π =
      c ⬝ᵥ lssLongRunCov Γ F G *ᵥ c := by
    rw [hps, hki, ← quadForm_lssLongRunCov]
    exact lss_variance_integral Γ hW hF G hπ hπV _
  have heq : asymptoticVariance (lssMatrixKernel Γ F G) π (fun y => c ⬝ᵥ y) =
      ∫ x, (poissonSeries (lssMatrixKernel Γ F G) π (fun y => c ⬝ᵥ y) x ^ 2 -
        kernelInt (lssMatrixKernel Γ F G)
          (poissonSeries (lssMatrixKernel Γ F G) π (fun y => c ⬝ᵥ y)) x ^ 2) ∂π := h6.symm
  refine ⟨hm, heq.trans hvar, ?_⟩
  rw [hvar] at h4
  simp only [hm, sub_zero] at h4
  exact h4

/-- **Theorem 17.6.2** (MT p. 456), the CLT for `Yₖ = c ⬝ Xₖ`: under the hypotheses of
`theorem_17_6_2_vector`, `n^{−1/2} Σ_{k=1}^n c ⬝ Xₖ ⇒ N(0, γ_c²)` under every `P_x`, with
`γ_c² = cᵀ (I − F)⁻¹ G Σ_W Gᵀ (I − Fᵀ)⁻¹ c`. -/
theorem theorem_17_6_2_vector_clt (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hW : HasCentredSecondMoments Γ) {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (G : Matrix (Fin n) (Fin p) ℝ) {ψ : Measure (Fin n → ℝ)}
    (hψ : haveI := isMarkovKernel_lssMatrixKernel Γ F G
      IsMaximalIrreducibility (lssMatrixKernel Γ F G) ψ)
    (hap : IsAperiodic (lssMatrixKernel Γ F G) ψ)
    (hcpt : ∀ K : Set (Fin n → ℝ), IsCompact K → IsPetite (lssMatrixKernel Γ F G) K)
    {π : Measure (Fin n → ℝ)} [IsProbabilityMeasure π]
    (hπ : haveI := isMarkovKernel_lssMatrixKernel Γ F G
      IsInvariant (lssMatrixKernel Γ F G) π) (c : Fin n → ℝ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (c ⬝ᵥ lssLongRunCov Γ F G *ᵥ c).toNNReal) P')
    (x : Fin n → ℝ) :
    haveI := isMarkovKernel_lssMatrixKernel Γ F G
    haveI := isMarkovKernel_pathKernel (lssMatrixKernel Γ F G)
    TendstoInDistribution (fun (m : ℕ) ω => (√(m : ℝ))⁻¹ * pathSum (fun y => c ⬝ᵥ y) m ω)
      atTop Z (fun _ => pathKernel (lssMatrixKernel Γ F G) x) P' := by
  have := isMarkovKernel_lssMatrixKernel Γ F G
  obtain ⟨⟨ρ, b, hρ, hb, C, hC, hdrift⟩, hph, hres⟩ :=
    theorem_17_6_2_vector Γ hW hF G hψ hap hcpt
  obtain ⟨hm, hvar, -⟩ := hres π hπ c
  have hVm := measurable_lssWeight F
  set K := ENNReal.ofReal (1 + c ⬝ᵥ c) with hK
  have hK1 : 1 ≤ K := ENNReal.one_le_ofReal.2 (le_add_of_nonneg_right (dotProduct_self_nonneg' c))
  have hV'1 : ∀ x, 1 ≤ K * lssWeight F x := fun x =>
    calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ K * lssWeight F x := mul_le_mul' hK1 (one_le_lssWeight hF x)
  have hV'fin : ∀ x, K * lssWeight F x ≠ ∞ := fun x =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lssWeight_ne_top F x)
  have hg : ∀ x, ENNReal.ofReal ((fun y => c ⬝ᵥ y) x ^ 2) ≤ K * lssWeight F x := fun x =>
    (ofReal_sq_dotProduct_le_weight hF c x).1
  rw [← hvar] at hZ
  have h := theorem_17_0_1_iv hph hap (hVm.const_mul K) hV'1 hV'fin hρ
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb) hC (hdrift.const_mul' hVm K) hπ
    (g := fun y => c ⬝ᵥ y) (continuous_const.dotProduct continuous_id).measurable hg hZ x
  simp only [hm, sub_zero] at h
  exact h

/-! ### The vector-valued CLT (Cramér–Wold) -/

/-- The disturbance covariance `Σ_W` is positive semidefinite. -/
theorem posSemidef_disturbanceCov {Γ : Measure (Fin p → ℝ)} (hW : HasCentredSecondMoments Γ) :
    (disturbanceCov Γ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, disturbanceCov]
    exact integral_congr_ae (Eventually.of_forall fun w => mul_comm _ _)
  · rw [star_trivial, ← integral_sq_dotProduct_disturbance hW]
    exact integral_nonneg fun w => sq_nonneg _

/-- The long-run covariance `(I − F)⁻¹ G Σ_W Gᵀ (I − Fᵀ)⁻¹` is positive semidefinite. -/
theorem posSemidef_lssLongRunCov {Γ : Measure (Fin p → ℝ)} (hW : HasCentredSecondMoments Γ)
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    (lssLongRunCov Γ F G).PosSemidef := by
  have h := (posSemidef_disturbanceCov hW).mul_mul_conjTranspose_same ((1 - F)⁻¹ * G)
  have e : lssLongRunCov Γ F G = (1 - F)⁻¹ * G * disturbanceCov Γ * ((1 - F)⁻¹ * G)ᴴ := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one, lssLongRunCov]
    simp only [Matrix.mul_assoc]
  rw [e]
  exact h

/-- Under the multivariate Gaussian `N(0, S)` on `EuclideanSpace ℝ (Fin n)`, the projection
`v ↦ ⟪v, t⟫` has law `N(0, tᵀ S t)`. -/
theorem hasLaw_inner_multivariateGaussian {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (t : EuclideanSpace ℝ (Fin n)) :
    HasLaw (fun v : EuclideanSpace ℝ (Fin n) => inner ℝ v t)
      (gaussianReal 0 (t ⬝ᵥ S *ᵥ t).toNNReal) (multivariateGaussian 0 S) := by
  set μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S
  have hfun : (fun v : EuclideanSpace ℝ (Fin n) => inner ℝ v t) = ⇑(innerSL ℝ t) :=
    funext fun v => by rw [innerSL_apply_apply, real_inner_comm]
  have hmean : ∫ v, innerSL ℝ t v ∂μ = 0 := by
    rw [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id,
      integral_id_multivariateGaussian, map_zero]
  have hvar : Var[⇑(innerSL ℝ t); μ] = t ⬝ᵥ S *ᵥ t := by
    rw [← covarianceBilin_multivariateGaussian hS t t, covarianceBilin_self IsGaussian.memLp_two_id]
    rfl
  refine ⟨(innerSL ℝ t).continuous.measurable.aemeasurable.congr (by rw [hfun]), ?_⟩
  rw [hfun, IsGaussian.map_eq_gaussianReal, hvar]
  congr 1

/-- **The vector-valued CLT** stated after Theorem 17.6.2 (MT p. 456): under the hypotheses of
`theorem_17_6_2_vector`, `n^{−1/2} Σ_{k=1}^n Xₖ ⇒ N(0, Σ)` under every `P_x`, with
`Σ = (I − F)⁻¹ G Σ_W Gᵀ (I − Fᵀ)⁻¹`, as random vectors in `EuclideanSpace ℝ (Fin n)`. The book
asks for a vector-valued martingale CLT; by the Cramér–Wold theorem it follows from the scalar
CLTs for all `c ⬝ Xₖ` (`theorem_17_6_2_vector_clt`). -/
theorem theorem_17_6_2_vector_clt_vec (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hW : HasCentredSecondMoments Γ) {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F)
    (G : Matrix (Fin n) (Fin p) ℝ) {ψ : Measure (Fin n → ℝ)}
    (hψ : haveI := isMarkovKernel_lssMatrixKernel Γ F G
      IsMaximalIrreducibility (lssMatrixKernel Γ F G) ψ)
    (hap : IsAperiodic (lssMatrixKernel Γ F G) ψ)
    (hcpt : ∀ K : Set (Fin n → ℝ), IsCompact K → IsPetite (lssMatrixKernel Γ F G) K)
    {π : Measure (Fin n → ℝ)} [IsProbabilityMeasure π]
    (hπ : haveI := isMarkovKernel_lssMatrixKernel Γ F G
      IsInvariant (lssMatrixKernel Γ F G) π) (x : Fin n → ℝ) :
    haveI := isMarkovKernel_lssMatrixKernel Γ F G
    haveI := isMarkovKernel_pathKernel (lssMatrixKernel Γ F G)
    TendstoInDistribution (fun (m : ℕ) (ω : ℕ → Fin n → ℝ) =>
        (√(m : ℝ))⁻¹ • WithLp.toLp 2 (∑ k ∈ Finset.range m, ω (k + 1)))
      atTop id (fun _ => pathKernel (lssMatrixKernel Γ F G) x)
      (multivariateGaussian 0 (lssLongRunCov Γ F G)) := by
  have := isMarkovKernel_lssMatrixKernel Γ F G
  have := isMarkovKernel_pathKernel (lssMatrixKernel Γ F G)
  have hS := posSemidef_lssLongRunCov hW F G
  have hmeas : ∀ m : ℕ, AEMeasurable (fun ω : ℕ → Fin n → ℝ =>
      (√(m : ℝ))⁻¹ • WithLp.toLp 2 (∑ k ∈ Finset.range m, ω (k + 1)))
      (pathKernel (lssMatrixKernel Γ F G) x) := fun m => by
    have h1 : Measurable fun ω : ℕ → Fin n → ℝ =>
        (WithLp.toLp 2 (∑ k ∈ Finset.range m, ω (k + 1)) : EuclideanSpace ℝ (Fin n)) :=
      (PiLp.continuous_toLp 2 _).measurable.comp
        (Finset.measurable_sum _ fun k _ => measurable_pi_apply (k + 1))
    exact (h1.const_smul ((√(m : ℝ))⁻¹)).aemeasurable
  refine (tendstoInDistribution_iff_tendstoInDistribution_inner aemeasurable_id hmeas).2
    fun t => ?_
  have h := theorem_17_6_2_vector_clt Γ hW hF G hψ hap hcpt hπ (WithLp.ofLp t)
    (hasLaw_inner_multivariateGaussian hS t) x
  convert h using 2 with m
  · funext ω
    rw [real_inner_smul_left]
    congr 1
    rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial, dotProduct_sum]
    rfl
  · rfl

/-- The hypotheses of `theorem_17_6_2_vector` other than aperiodicity, from the book's
conditions: under controllability (LCM3), a disturbance law that is not singular with respect
to Lebesgue measure (LSS4) and (LSS5), the model is `ψ`-irreducible and compact sets are petite
(Proposition 6.3.5). -/
theorem lss_irreducible_petite (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G)
    (hns : ¬ Γ ⟂ₘ volume) (hF : IsStableMatrix F) :
    haveI := isMarkovKernel_lssMatrixKernel Γ F G
    (∃ ψ, IsMaximalIrreducibility (lssMatrixKernel Γ F G) ψ) ∧
      ∀ K : Set (Fin n → ℝ), IsCompact K → IsPetite (lssMatrixKernel Γ F G) K := by
  have := isMarkovKernel_lssMatrixKernel Γ F G
  obtain ⟨_, ⟨φ, hφ0, hφ⟩, -, hsmall⟩ := proposition_6_3_5 Γ hc hns hF
  exact ⟨⟨_, isMaximalIrreducibility_maxIrrMeasure _ hφ hφ0⟩, fun K hK => (hsmall K hK).isPetite⟩

end MeynTweedie.LimitTheorems

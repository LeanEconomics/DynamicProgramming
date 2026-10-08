/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.OrderContraction
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Operators on `L¹(ψ)`

The Banach lattice `L¹(ψ)` with the `ψ`-a.e. order (§A.5.2.5, Example A.5.7), and the operators
used in §4.2.1.2 and §4.2.2.

* If `ψ` is stationary for the stochastic kernel `P` (`ψP = ψ`, §A.5.4.4), then
  `(Pv)(x) = ∫ v(x')P(x, dx')` is a well defined positive operator on `L¹(ψ)` with `‖P‖ ≤ 1`
  (Lemma A.5.32): `ψ`-null sets are `P(x, ·)`-null for `ψ`-almost every `x`.
* Multiplication by a bounded measurable function is a bounded operator on `L¹(ψ)`, positive when
  the function is nonnegative.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace SargentStachurski.AdditionalApplications

namespace L1

variable {X : Type*} [MeasurableSpace X] (ψ : Measure X)

/-! ### Stationary distributions -/

/-- If `ψP = ψ`, a `ψ`-a.e. property holds `P(x, ·)`-a.e. for `ψ`-a.e. `x`. -/
theorem ae_ae_of_stationary {P : Kernel X X} (hst : ψ.bind P = ψ) {p : X → Prop}
    (h : ∀ᵐ y ∂ψ, p y) : ∀ᵐ x ∂ψ, ∀ᵐ y ∂(P x), p y :=
  Measure.ae_ae_of_ae_bind P.measurable.aemeasurable (by rw [hst]; exact h)

/-- If `ψP = ψ`, then `∫∫ f(y) P(x, dy) ψ(dx) = ∫ f dψ`. -/
theorem lintegral_stationary {P : Kernel X X} (hst : ψ.bind P = ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ x, ∫⁻ y, f y ∂(P x) ∂ψ = ∫⁻ y, f y ∂ψ := by
  conv_rhs => rw [← hst]
  rw [Measure.lintegral_bind P.measurable.aemeasurable hf.aemeasurable]

/-! ### The Markov operator on `L¹(ψ)` -/

variable {ψ} {P : Kernel X X} (hst : ψ.bind P = ψ)

/-- `x ↦ ∫ v(x')P(x, dx')` for a representative of `v ∈ L¹(ψ)`. -/
noncomputable def markovFun (f : Lp ℝ 1 ψ) (x : X) : ℝ := ∫ y, f y ∂(P x)

include hst in
theorem lintegral_markov_le (f : Lp ℝ 1 ψ) :
    ∫⁻ x, ‖markovFun (P := P) f x‖ₑ ∂ψ ≤ ∫⁻ y, ‖f y‖ₑ ∂ψ := by
  rw [← lintegral_stationary ψ hst (Lp.stronglyMeasurable f).measurable.enorm]
  exact lintegral_mono fun x => enorm_integral_le_lintegral_enorm _

include hst in
theorem memLp_markovFun (f : Lp ℝ 1 ψ) : MemLp (markovFun (P := P) f) 1 ψ := by
  refine memLp_one_iff_integrable.2
    ⟨((Lp.stronglyMeasurable f).integral_kernel (κ := P)).aestronglyMeasurable, ?_⟩
  exact (lintegral_markov_le hst f).trans_lt
    ((memLp_one_iff_integrable.1 (Lp.memLp f)).hasFiniteIntegral)

include hst in
/-- For `ψ`-a.e. `x`, `v ∈ L¹(ψ)` is `P(x, ·)`-integrable. -/
theorem ae_integrable (f : Lp ℝ 1 ψ) : ∀ᵐ x ∂ψ, Integrable f (P x) := by
  have hfin : ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂(P x) ∂ψ < ∞ := by
    rw [lintegral_stationary ψ hst (Lp.stronglyMeasurable f).measurable.enorm]
    exact (memLp_one_iff_integrable.1 (Lp.memLp f)).hasFiniteIntegral
  filter_upwards [ae_lt_top ((Lp.stronglyMeasurable f).measurable.enorm.lintegral_kernel)
    hfin.ne] with x hx
  exact ⟨(Lp.stronglyMeasurable f).aestronglyMeasurable, hx⟩

include hst in
/-- `markovFun` respects `ψ`-a.e. equality. -/
theorem markovFun_congr {f : Lp ℝ 1 ψ} {g : X → ℝ} (h : ⇑f =ᵐ[ψ] g) :
    ∀ᵐ x ∂ψ, markovFun (P := P) f x = ∫ y, g y ∂(P x) := by
  filter_upwards [ae_ae_of_stationary ψ hst h] with x hx
  exact integral_congr_ae hx

/-- The Markov operator on `L¹(ψ)`, as a linear map. -/
noncomputable def markovLin : Lp ℝ 1 ψ →ₗ[ℝ] Lp ℝ 1 ψ where
  toFun f := (memLp_markovFun hst f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_markovFun hst (f + g)).coeFn_toLp,
      Lp.coeFn_add ((memLp_markovFun hst f).toLp _) ((memLp_markovFun hst g).toLp _),
      (memLp_markovFun hst f).coeFn_toLp, (memLp_markovFun hst g).coeFn_toLp,
      markovFun_congr hst (Lp.coeFn_add f g), ae_integrable hst f, ae_integrable hst g]
      with x h1 h2 h3 h4 h5 h6 h7
    rw [h1, h2, Pi.add_apply, h3, h4, h5]
    exact integral_add h6 h7
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_markovFun hst (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_markovFun hst f).toLp _), (memLp_markovFun hst f).coeFn_toLp,
      markovFun_congr hst (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _

theorem markovLin_apply (f : Lp ℝ 1 ψ) :
    markovLin hst f = (memLp_markovFun hst f).toLp _ := rfl

theorem markovLin_norm_le (f : Lp ℝ 1 ψ) : ‖markovLin hst f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul, Lp.norm_def, Lp.norm_def, markovLin_apply]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) ?_
  rw [eLpNorm_congr_ae (memLp_markovFun hst f).coeFn_toLp,
    eLpNorm_one_eq_lintegral_enorm (memLp_markovFun hst f).aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm (Lp.stronglyMeasurable f).aestronglyMeasurable]
  exact lintegral_markov_le hst f

/-- The Markov operator `(Pv)(x) = ∫ v(x')P(x, dx')` on `L¹(ψ)`, with `‖P‖ ≤ 1`. -/
noncomputable def markovCLM : Lp ℝ 1 ψ →L[ℝ] Lp ℝ 1 ψ :=
  (markovLin hst).mkContinuous 1 (markovLin_norm_le hst)

/-- **Lemma A.5.32**, the bound used here: `‖P‖ ≤ 1` on `L¹(ψ)`. -/
theorem markovCLM_norm_le : ‖markovCLM hst‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem markovCLM_coeFn (f : Lp ℝ 1 ψ) :
    ⇑(markovCLM hst f) =ᵐ[ψ] fun x => ∫ y, f y ∂(P x) :=
  (memLp_markovFun hst f).coeFn_toLp

/-- The Markov operator is positive. -/
theorem markovCLM_isPositive : BanachLattice.IsPositiveOp (markovCLM hst) := fun f hf => by
  rw [← Lp.coeFn_nonneg] at hf ⊢
  filter_upwards [markovCLM_coeFn hst f, ae_ae_of_stationary ψ hst hf] with x h1 h2
  rw [h1]
  exact integral_nonneg_of_ae h2

/-! ### Multiplication operators -/

theorem memLp_mul {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (f : Lp ℝ 1 ψ) : MemLp (fun x => h x * f x) 1 ψ :=
  memLp_one_iff_integrable.2 ((memLp_one_iff_integrable.1 (Lp.memLp f)).bdd_mul
    hm.aestronglyMeasurable (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x))

variable (ψ) in
/-- Multiplication by a bounded measurable `h`, as a linear map on `L¹(ψ)`. -/
noncomputable def mulLin {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    Lp ℝ 1 ψ →ₗ[ℝ] Lp ℝ 1 ψ where
  toFun f := (memLp_mul hm hC f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_mul hm hC (f + g)).coeFn_toLp,
      Lp.coeFn_add ((memLp_mul hm hC f).toLp _) ((memLp_mul hm hC g).toLp _),
      (memLp_mul hm hC f).coeFn_toLp, (memLp_mul hm hC g).coeFn_toLp, Lp.coeFn_add f g]
      with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_mul hm hC (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_mul hm hC f).toLp _), (memLp_mul hm hC f).coeFn_toLp,
      Lp.coeFn_smul c f] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring

theorem mulLin_apply {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (f : Lp ℝ 1 ψ) : mulLin ψ hm hC f = (memLp_mul hm hC f).toLp _ := rfl

variable (ψ) in
/-- Multiplication by a bounded measurable `h`, `|h| ≤ C`, as a bounded operator on `L¹(ψ)`. -/
noncomputable def mulCLM {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    Lp ℝ 1 ψ →L[ℝ] Lp ℝ 1 ψ :=
  (mulLin ψ hm hC).mkContinuous C fun f => by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_mul hm hC f).coeFn_toLp] with x hx
    rw [mulLin_apply, hx, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem mulCLM_coeFn {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (f : Lp ℝ 1 ψ) : ⇑(mulCLM ψ hm hC f) =ᵐ[ψ] fun x => h x * f x :=
  (memLp_mul hm hC f).coeFn_toLp

/-- Multiplication by `h ≥ 0` is positive. -/
theorem mulCLM_isPositive {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (hh : ∀ x, 0 ≤ h x) : BanachLattice.IsPositiveOp (mulCLM ψ hm hC) := fun f hf => by
  rw [← Lp.coeFn_nonneg] at hf ⊢
  filter_upwards [mulCLM_coeFn hm hC f, hf] with x h1 h2
  rw [h1]
  exact mul_nonneg (hh x) h2

/-- Multiplication by `0 ≤ h ≤ 1` lies below the identity on the positive cone. -/
theorem mulCLM_le_self {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (hh1 : ∀ x, h x ≤ 1) {f : Lp ℝ 1 ψ} (hf : 0 ≤ f) : mulCLM ψ hm hC f ≤ f := by
  rw [← Lp.coeFn_nonneg] at hf
  rw [← Lp.coeFn_le]
  filter_upwards [mulCLM_coeFn hm hC f, hf] with x h1 h2
  rw [h1]
  exact mul_le_of_le_one_left h2 (hh1 x)

end L1

end SargentStachurski.AdditionalApplications

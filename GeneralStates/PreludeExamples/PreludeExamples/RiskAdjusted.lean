/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PreludeExamples.FirmProblem
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.Integral

/-!
# Beyond risk neutrality

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.1.3 (pp. 12–18) and §1.2.3.2
(pp. 34–35).

* §1.1.3.4: the entropic certainty equivalent `e_γ(μ) = −(1/γ) ln ∫ exp(−γz) μ(dz)`. For
  `γ > 0` it lies below the mean (Jensen's inequality), and for a normal distribution it is
  exactly `m − γσ²/2` (p. 16: "the approximation becomes exact when `Z_σ` is normally
  distributed"). Value-at-risk `VaR_α(Z) = inf {c : ℙ{Z + c < 0} ≤ α}` falls when payoffs rise.
* §1.1.3.6: recursive risk adjustment `v_σ = σs + (1 − σ)(π + βKv_σ)` (1.14). The book asks
  whether `v_σ` is well defined. It is, whenever `K` is order preserving and shifts constants,
  `K(v + c) = Kv + c`: then `K` does not increase the supremum distance, each policy operator is
  a `β`-contraction on `bX`, and the conclusions of Theorem 1.1.1 hold. The entropic operator
  `(Kv)(x) = −(1/γ) ln ∫ exp(−γv(x')) P(x, dx')` qualifies for `γ > 0`.
* The mean-variance operator `Kv = Pv − (γ/2) Var_P(v)` (p. 18) is not order preserving: an
  explicit two-point example.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Function

open scoped NNReal ENNReal

namespace SargentStachurski.PreludeExamples

/-! ### Certainty equivalents for a single payoff -/

/-- The entropic certainty equivalent `e_γ(μ) = −(1/γ) ln ∫ exp(−γz) μ(dz)` (§1.1.3.4). -/
noncomputable def entropicCE (γ : ℝ) (μ : Measure ℝ) : ℝ :=
  -(1 / γ) * Real.log (∫ z, Real.exp (-γ * z) ∂μ)

/-- §1.1.3.4 (p. 16): for a normal payoff `N(m, σ²)`, `e_γ = m − γσ²/2` exactly. -/
theorem entropicCE_gaussianReal {γ : ℝ} (hγ : γ ≠ 0) (m : ℝ) (v : ℝ≥0) :
    entropicCE γ (gaussianReal m v) = m - γ * v / 2 := by
  have h : ∫ z, Real.exp (-γ * z) ∂(gaussianReal m v) =
      Real.exp (m * -γ + v * (-γ) ^ 2 / 2) := by
    have := congrFun (mgf_id_gaussianReal (μ := m) (v := v)) (-γ)
    rw [mgf] at this
    simpa using this
  rw [entropicCE, h, Real.log_exp]
  field_simp
  ring

/-- §1.1.3.4 (p. 15): for `γ > 0`, the decision maker values a risky payoff below its mean,
`e_γ(μ) ≤ ∫ z μ(dz)`. -/
theorem entropicCE_le_integral {γ : ℝ} (hγ : 0 < γ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : ℝ => z) μ) (he : Integrable (fun z => Real.exp (-γ * z)) μ) :
    entropicCE γ μ ≤ ∫ z, z ∂μ := by
  have hj := convexOn_exp.map_integral_le (μ := μ) (f := fun z => -γ * z)
    Real.continuous_exp.continuousOn isClosed_univ (Eventually.of_forall fun _ => mem_univ _)
    (hi.const_mul (-γ)) he
  rw [integral_const_mul] at hj
  have hpos : 0 < ∫ z, Real.exp (-γ * z) ∂μ := (Real.exp_pos _).trans_le hj
  have hlog : -γ * ∫ z, z ∂μ ≤ Real.log (∫ z, Real.exp (-γ * z) ∂μ) :=
    (Real.le_log_iff_exp_le hpos).2 hj
  rw [entropicCE]
  have : 1 / γ * (-γ * ∫ z, z ∂μ) = -∫ z, z ∂μ := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog (one_div_nonneg.2 hγ.le)]

/-- Value-at-risk `VaR_α(Z) = inf {c ∈ ℝ : ℙ{Z + c < 0} ≤ α}` (§1.1.3.4). -/
noncomputable def valueAtRisk {Ω : Type*} [MeasurableSpace Ω] (α : ℝ≥0∞) (μ : Measure Ω)
    (Z : Ω → ℝ) : ℝ :=
  sInf {c : ℝ | μ {ω | Z ω + c < 0} ≤ α}

/-- §1.1.3.4 (p. 16): a payoff with less downside needs a smaller cash injection: if `Z ≤ Z'`
then `VaR_α(Z') ≤ VaR_α(Z)` (whenever both infima are over nonempty sets bounded below). -/
theorem valueAtRisk_anti {Ω : Type*} [MeasurableSpace Ω] {α : ℝ≥0∞} {μ : Measure Ω}
    {Z Z' : Ω → ℝ} (h : ∀ ω, Z ω ≤ Z' ω)
    (hne : {c : ℝ | μ {ω | Z ω + c < 0} ≤ α}.Nonempty)
    (hbdd : BddBelow {c : ℝ | μ {ω | Z' ω + c < 0} ≤ α}) :
    valueAtRisk α μ Z' ≤ valueAtRisk α μ Z := by
  refine csInf_le_csInf hbdd hne fun c hc => ?_
  refine (measure_mono fun ω (hω : Z' ω + c < 0) => ?_).trans hc
  change Z ω + c < 0
  linarith [h ω]

/-! ### Recursive risk adjustment -/

variable {X : Type*} [MeasurableSpace X]

/-- An operator `K` on `bX` that is order preserving and shifts constants, `K(v + c) = Kv + c`,
like a certainty equivalent. -/
structure IsShiftMonotone (K : (X → ℝ) → X → ℝ) : Prop where
  mapsTo : MapsTo K (bX X) (bX X)
  mono : ∀ v ∈ bX X, ∀ w ∈ bX X, v ≤ w → K v ≤ K w
  shift : ∀ v ∈ bX X, ∀ c : ℝ, K (fun x => v x + c) = fun x => K v x + c

/-- An order preserving, constant-shifting operator does not increase the supremum distance. -/
theorem IsShiftMonotone.abs_sub_le {K : (X → ℝ) → X → ℝ} (hK : IsShiftMonotone K) {v w : X → ℝ}
    (hv : v ∈ bX X) (hw : w ∈ bX X) {c : ℝ} (h : ∀ x, |v x - w x| ≤ c) (x : X) :
    |K v x - K w x| ≤ c := by
  have hwc : ∀ d : ℝ, (fun x => w x + d) ∈ bX X := fun d =>
    ⟨hw.1.add measurable_const, hw.2.add (isBdd_const d)⟩
  have h1 : K v ≤ fun x => K w x + c := by
    rw [← hK.shift w hw c]
    exact hK.mono v hv _ (hwc c) fun y => by linarith [(abs_le.1 (h y)).2]
  have h2 : (fun x => K w x + -c) ≤ K v := by
    rw [← hK.shift w hw (-c)]
    exact hK.mono _ (hwc (-c)) v hv fun y => by linarith [(abs_le.1 (h y)).1]
  rw [abs_le]
  constructor
  · linarith [h2 x]
  · linarith [h1 x]

namespace FirmProblem

variable (F : FirmProblem X)

/-- The risk-adjusted policy operator (1.14): `T_σ v = σs + (1 − σ)(π + βKv)`. -/
noncomputable def TσK (K : (X → ℝ) → X → ℝ) (σ : X → Bool) (v : X → ℝ) : X → ℝ :=
  fun x => if σ x then F.s else F.profit x + F.β * K v x

/-- §1.1.3.6: with an order preserving, constant-shifting `K`, the risk-adjusted firm problem
(1.14) is a contracting dynamic program on `bX`; in particular every `v_σ` is well defined. -/
noncomputable def toDPK {K : (X → ℝ) → X → ℝ} (hK : IsShiftMonotone K) :
    ContractingDP X (FirmPolicy X) where
  V := bX X
  T σ := F.TσK K σ.1
  β := F.β
  β_nonneg := F.β_nonneg
  β_lt_one := F.β_lt_one
  nonempty := ⟨_, const_mem_bX 0⟩
  bdd := fun _ h => h.2
  closed := isUniformlyClosed_bX
  mapsTo σ v hv := by
    obtain ⟨hm, N, hN⟩ := hK.mapsTo hv
    obtain ⟨M, hM⟩ := F.profit_mem.2
    refine ⟨Measurable.ite (σ.2 (measurableSet_singleton true)) measurable_const
      (F.profit_mem.1.add (measurable_const.mul hm)), max |F.s| (M + F.β * N), fun x => ?_⟩
    simp only [TσK]
    split_ifs
    · exact le_max_left _ _
    · refine (abs_add_le _ _).trans (le_max_of_le_right (add_le_add (hM x) ?_))
      rw [abs_mul, abs_of_nonneg F.β_nonneg]
      exact mul_le_mul_of_nonneg_left (hN x) F.β_nonneg
  mono σ v hv w hw h x := by
    simp only [TσK]
    split_ifs
    · exact le_rfl
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hK.mono v hv w hw h x) F.β_nonneg)
  contraction σ v hv w hw c h x := by
    simp only [TσK]
    split_ifs
    · simpa using mul_nonneg F.β_nonneg ((abs_nonneg _).trans (h x))
    · rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg F.β_nonneg]
      exact mul_le_mul_of_nonneg_left (hK.abs_sub_le hv hw h x) F.β_nonneg
  exists_greedy v hv := by
    obtain ⟨hm, -⟩ := hK.mapsTo hv
    have hmeas : Measurable fun x => decide (F.profit x + F.β * K v x ≤ F.s) := by
      refine measurable_to_bool ?_
      have : (fun x => decide (F.profit x + F.β * K v x ≤ F.s)) ⁻¹' {true} =
          {x | F.profit x + F.β * K v x ≤ F.s} := by ext x; simp
      rw [this]
      exact measurableSet_le (F.profit_mem.1.add (measurable_const.mul hm)) measurable_const
    refine ⟨⟨_, hmeas⟩, fun τ x => ?_⟩
    change F.TσK K τ.1 v x ≤ F.TσK K _ v x
    simp only [TσK]
    by_cases hx : F.profit x + F.β * K v x ≤ F.s
    · simp only [hx, decide_true, ↓reduceIte]
      split_ifs
      · exact le_rfl
      · exact hx
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · exact (le_of_not_ge hx)
      · exact le_rfl

/-- §1.1.3.6: Theorem 1.1.1 for the risk-adjusted firm (1.14). Each `v_σ` is the unique solution
of (1.14) in `bX`; `v* = sup_σ v_σ` uniquely solves `v = s ∨ (π + βKv)` in `bX`; an optimal
policy exists and a policy is optimal iff it is `v*`-greedy; VFI converges. -/
theorem riskAdjusted_optimality {K : (X → ℝ) → X → ℝ} (hK : IsShiftMonotone K) :
    (∀ σ, (F.toDPK hK).vσ σ ∈ bX X ∧ ∀ w ∈ bX X, F.TσK K σ.1 w = w → w = (F.toDPK hK).vσ σ) ∧
      IsGreatest (range (F.toDPK hK).vσ) (F.toDPK hK).vstar ∧
      (∀ v ∈ bX X, (F.toDPK hK).bellman v = v ↔ v = (F.toDPK hK).vstar) ∧
      (∀ σ, (F.toDPK hK).IsOptimal σ ↔ (F.toDPK hK).IsGreedy (F.toDPK hK).vstar σ) ∧
      (∃ σ, (F.toDPK hK).IsOptimal σ) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => (F.toDPK hK).bellman^[n] v)
        (F.toDPK hK).vstar atTop := by
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := (F.toDPK hK).optimality
  exact ⟨fun σ => ⟨(F.toDPK hK).vσ_mem σ, fun w hw h => (F.toDPK hK).eq_vσ hw h⟩, h1, h3, h4,
    h5, h6⟩

end FirmProblem

/-! ### The entropic operator -/

/-- The entropic risk operator `(Kv)(x) = −(1/γ) ln ∫ exp(−γv(x')) P(x, dx')` (§1.1.3.6). -/
noncomputable def entropicOp (γ : ℝ) (P : ProbabilityTheory.Kernel X X) (v : X → ℝ) (x : X) : ℝ :=
  -(1 / γ) * Real.log (∫ y, Real.exp (-γ * v y) ∂(P x))

/-- §1.1.3.6: for `γ > 0` the entropic operator is order preserving on `bX` and shifts
constants, so the entropic version of (1.14) is well defined and Theorem 1.1.1 holds for it. -/
theorem isShiftMonotone_entropicOp {γ : ℝ} (hγ : 0 < γ) (P : ProbabilityTheory.Kernel X X)
    [IsMarkovKernel P] : IsShiftMonotone (entropicOp γ P) := by
  -- `exp(−γv) ∈ bX` and its integral is positive
  have hexp : ∀ v ∈ bX X, (fun y => Real.exp (-γ * v y)) ∈ bX X := by
    intro v hv
    obtain ⟨M, hM⟩ := hv.2
    refine ⟨(measurable_const.mul hv.1).exp, Real.exp (γ * M), fun y => ?_⟩
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by nlinarith [(abs_le.1 (hM y)).1])
  have hpos : ∀ v ∈ bX X, ∀ x, 0 < ∫ y, Real.exp (-γ * v y) ∂(P x) := by
    intro v hv x
    obtain ⟨M, hM⟩ := hv.2
    have hle : ∫ _y, Real.exp (-γ * M) ∂(P x) ≤ ∫ y, Real.exp (-γ * v y) ∂(P x) :=
      integral_mono (integrable_const _) (integrable_of_mem_bX P (hexp v hv) x) fun y =>
        Real.exp_le_exp.2 (by nlinarith [(abs_le.1 (hM y)).2])
    simp only [integral_const, probReal_univ, one_smul] at hle
    exact (Real.exp_pos _).trans_le hle
  refine ⟨fun v hv => ?_, fun v hv w hw h x => ?_, fun v hv c => ?_⟩
  · -- measurable and bounded
    obtain ⟨M, hM⟩ := hv.2
    have hmI : Measurable fun x => ∫ y, Real.exp (-γ * v y) ∂(P x) :=
      measurable_markovOp P (hexp v hv).1
    refine ⟨measurable_const.mul (Real.measurable_log.comp hmI), |M|, fun x => ?_⟩
    have hvM : ∀ y, |v y| ≤ |M| := fun y => (hM y).trans (le_abs_self M)
    have hlo : ∫ _y, Real.exp (-γ * |M|) ∂(P x) ≤ ∫ y, Real.exp (-γ * v y) ∂(P x) :=
      integral_mono (integrable_const _) (integrable_of_mem_bX P (hexp v hv) x) fun y =>
        Real.exp_le_exp.2 (by
          nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 (hvM y)).2 hγ.le])
    have hhi : ∫ y, Real.exp (-γ * v y) ∂(P x) ≤ ∫ _y, Real.exp (γ * |M|) ∂(P x) :=
      integral_mono (integrable_of_mem_bX P (hexp v hv) x) (integrable_const _) fun y =>
        Real.exp_le_exp.2 (by
          nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 (hvM y)).1 hγ.le])
    simp only [integral_const, probReal_univ, one_smul] at hlo hhi
    have l1 := Real.log_le_log (Real.exp_pos _) hlo
    have l2 := Real.log_le_log (hpos v hv x) hhi
    rw [Real.log_exp] at l1 l2
    simp only [entropicOp]
    rw [abs_le]
    have hγ' : 0 < 1 / γ := one_div_pos.2 hγ
    constructor
    · have := mul_le_mul_of_nonneg_left l2 hγ'.le
      have e : 1 / γ * (γ * |M|) = |M| := by field_simp
      nlinarith
    · have := mul_le_mul_of_nonneg_left l1 hγ'.le
      have e : 1 / γ * (-γ * |M|) = -|M| := by field_simp
      nlinarith
  · -- order preserving
    have hle : ∫ y, Real.exp (-γ * w y) ∂(P x) ≤ ∫ y, Real.exp (-γ * v y) ∂(P x) :=
      integral_mono (integrable_of_mem_bX P (hexp w hw) x) (integrable_of_mem_bX P (hexp v hv) x)
        fun y => Real.exp_le_exp.2 (by nlinarith [h y])
    have hl := Real.log_le_log (hpos w hw x) hle
    simp only [entropicOp]
    nlinarith [mul_le_mul_of_nonneg_left hl (one_div_pos.2 hγ).le]
  · -- shifting constants
    funext x
    have hsplit : (fun y => Real.exp (-γ * (v y + c))) =
        fun y => Real.exp (-γ * c) * Real.exp (-γ * v y) := by
      funext y; rw [← Real.exp_add]; ring_nf
    simp only [entropicOp]
    rw [hsplit, integral_const_mul, Real.log_mul (Real.exp_pos _).ne' (hpos v hv x).ne',
      Real.log_exp]
    field_simp
    ring

/-! ### Mean-variance is not order preserving -/

/-- The mean-variance criterion `E v − (γ/2) Var v` under a probability measure `μ` (p. 15). -/
noncomputable def meanVariance {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (μ : Measure Ω)
    (v : Ω → ℝ) : ℝ :=
  ∫ ω, v ω ∂μ - γ / 2 * ∫ ω, (v ω - ∫ ω', v ω' ∂μ) ^ 2 ∂μ

/-- §1.1.3.6 (p. 18): the mean-variance operator is not order preserving. For a fair coin `μ`
and `γ > 0`, the payoff `w = (8/γ)𝟙{heads}` dominates `v = 0` but has lower mean-variance
value. So (1.14) with the mean-variance `K` falls outside the order-based theory. -/
theorem meanVariance_not_monotone {γ : ℝ} (hγ : 0 < γ) :
    ∃ v w : Bool → ℝ, v ≤ w ∧
      meanVariance γ (PMF.uniformOfFintype Bool).toMeasure w <
        meanVariance γ (PMF.uniformOfFintype Bool).toMeasure v := by
  refine ⟨fun _ => 0, fun b => if b then 8 / γ else 0, fun b => ?_, ?_⟩
  · cases b
    · simp
    · simpa using (div_pos (by norm_num : (0 : ℝ) < 8) hγ).le
  · simp only [meanVariance, PMF.integral_eq_sum, PMF.uniformOfFintype_apply, Fintype.univ_bool,
      Fintype.card_bool, smul_eq_mul]
    norm_num
    field_simp
    nlinarith

end SargentStachurski.PreludeExamples

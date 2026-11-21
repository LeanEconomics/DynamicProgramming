/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Belief distortions and entropy

Miao, §9.6, pp. 316–319 ("Belief Distortions and Entropy" and (9.45)–(9.46)). The reference
model is a probability space `(Ω, μ)` with the filtration `ℱ_t = σ(x₀, ε^t)`. A belief
distortion is a sequence of one-step likelihood ratios `m_{t+1} = π̂(ε_{t+1}|ε^t)/π(ε_{t+1})`,
`ℱ_{t+1}`-measurable, nonnegative, with `E[m_{t+1}|ε^t] = 1` (`RCRatios`; we also assume them
bounded, see below). Then `M_t = ∏_{j ≤ t} m_j` (`rcM`) and `Q_t = M_t · μ` (`rcQ`).

* `rc_lr_mean_one` (p. 317): `∫ (π̂(ε|ε^t)/π(ε)) π(ε) dε = 1`.
* `rcM_succ`: `M_{t+1} = m_{t+1}M_t`; `rc_martingale`: `{M_t}` is a martingale.
* `rc_distorted_integral` (p. 317): `E^Q φ = E[M_tφ]`; `rcQ_isProbability`; the distorted
  measures are consistent across horizons (`rc_distorted_consistent`).
* `rc_rnDeriv`, `rc_relEntropy`: `dQ/dP|_{ℱ_t} = M_t` and `E^Q[ln dQ/dP] = E[M_t ln M_t]`.
* `rc_entropy_nonneg`, `rc_entropy_eq_zero_iff`, `rcQ_eq_iff`: relative entropy is nonnegative
  and zero iff `M_t = 1` a.e. iff `Q = P`.
* `rc_entropy_decomp` (p. 317): `E[M_t ln M_t] = ∑_{j<t} E[M_j E(m_{j+1} ln m_{j+1}|ε^j)]`, each
  term nonnegative (`rc_increment_nonneg`).
* `rc_discounted_entropy` (p. 318): `(1 − β)∑βʲE[M_j ln M_j] = β∑βʲE[M_jE(m_{j+1} ln m_{j+1}|ε^j)]`
  (the abstract summation identity is `rc_discounted_sum`); the entropy constraint (9.45) is
  `rcEntropyConstraint`.
* `eq_9_46` (p. 319): the multiplier objective under `Q` equals
  `E∑βᵗM_t(r_t + βθE(m_{t+1} ln m_{t+1}|ε^t))`, over a finite horizon `T` (with `Q = Q_T`).

Departures: the ratios are assumed bounded (`m_{t+1} ≤ K`), which makes every expectation
finite; the book's Gaussian worst-case ratios are unbounded, but the general statements here are
the book's identities, which it uses without integrability conditions. The objective (9.46) is
treated over a finite horizon: `Q` on the whole path space (a projective limit of the `Q_T`) is not
constructed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace Miao.LinearQuadratic

/-- Miao, p. 317: the one-step likelihood ratio `m(ε) = π̂(ε|h)/π(ε)` of a density `π̂(·|h)`
with respect to a positive density `π` has mean one under `π`: `∫ (π̂/π) π = 1`. -/
theorem rc_lr_mean_one {H Eps : Type*} [MeasurableSpace Eps] (ν : Measure Eps)
    (dens : Eps → ℝ) (dhat : H → Eps → ℝ) (hpos : ∀ e, 0 < dens e)
    (hint : ∀ h, ∫ e, dhat h e ∂ν = 1) (h : H) :
    ∫ e, dhat h e / dens e * dens e ∂ν = 1 := by
  have : (fun e => dhat h e / dens e * dens e) = dhat h :=
    funext fun e => div_mul_cancel₀ _ (hpos e).ne'
  rw [this]
  exact hint h

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The one-step likelihood ratios of a belief distortion (Miao, p. 317): `m_{t+1}` is
`ℱ_{t+1}`-measurable, `0 ≤ m_{t+1} ≤ K` and `E[m_{t+1}|ℱ_t] = 1`. -/
structure RCRatios (μ : Measure Ω) (ℱ : Filtration ℕ m0) (m : ℕ → Ω → ℝ) (K : ℝ) : Prop where
  meas : ∀ t, Measurable[ℱ (t + 1)] (m (t + 1))
  nonneg : ∀ t ω, 0 ≤ m (t + 1) ω
  le : ∀ t ω, m (t + 1) ω ≤ K
  mean : ∀ t, μ[m (t + 1) | ℱ t] =ᵐ[μ] 1

/-- The likelihood ratio of the distorted joint density, `M_t = ∏_{j<t} m_{j+1}`, `M_0 = 1`. -/
def rcM (m : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := ∏ j ∈ Finset.range t, m (j + 1) ω

/-- Miao, p. 317: `M_0 = 1`. -/
theorem rcM_zero (m : ℕ → Ω → ℝ) : rcM m 0 = 1 := by
  funext ω
  simp [rcM]

/-- Miao, p. 317: `M_{t+1} = m_{t+1}M_t`. -/
theorem rcM_succ (m : ℕ → Ω → ℝ) (t : ℕ) : rcM m (t + 1) = fun ω => m (t + 1) ω * rcM m t ω := by
  funext ω
  simp [rcM, Finset.prod_range_succ, mul_comm]

variable {μ : Measure Ω} {ℱ : Filtration ℕ m0} {m : ℕ → Ω → ℝ} {K : ℝ}

theorem RCRatios.K_nonneg (hm : RCRatios μ ℱ m K) (ω : Ω) : 0 ≤ K :=
  (hm.nonneg 0 ω).trans (hm.le 0 ω)

theorem rcM_measurable (hm : RCRatios μ ℱ m K) (t : ℕ) : Measurable[ℱ t] (rcM m t) := by
  induction t with
  | zero => rw [rcM_zero]; exact measurable_const
  | succ t ih =>
    rw [rcM_succ]
    exact (hm.meas t).mul (ih.mono (ℱ.mono (Nat.le_succ t)) le_rfl)

theorem rcM_nonneg (hm : RCRatios μ ℱ m K) (t : ℕ) (ω : Ω) : 0 ≤ rcM m t ω :=
  Finset.prod_nonneg fun j _ => hm.nonneg j ω

theorem rcM_le (hm : RCRatios μ ℱ m K) (t : ℕ) (ω : Ω) : rcM m t ω ≤ K ^ t := by
  calc rcM m t ω = ∏ j ∈ Finset.range t, m (j + 1) ω := rfl
    _ ≤ ∏ _j ∈ Finset.range t, K :=
        Finset.prod_le_prod₀ (fun j _ => hm.nonneg j ω) (fun j _ => hm.le j ω)
    _ = K ^ t := by simp

/-- `|x ln x| ≤ 1 + c²` for `0 ≤ x ≤ c`. -/
theorem rc_abs_mul_log_le {x c : ℝ} (hx : 0 ≤ x) (hxc : x ≤ c) : |x * log x| ≤ 1 + c ^ 2 := by
  have h1 : x - 1 ≤ x * log x := by
    have := InformationTheory.klFun_nonneg hx
    rw [InformationTheory.klFun_apply] at this
    linarith
  have h2 : x * log x ≤ x * (x - 1) := by
    rcases hx.eq_or_lt with h | h
    · subst h; simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) hx
  rw [abs_le]
  constructor <;> nlinarith

theorem rc_integrable_of_bound [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (c : ℝ)
    (hc : ∀ ω, |f ω| ≤ c) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable c
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hc ω)

theorem rc_m_integrable [IsFiniteMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    Integrable (m (t + 1)) μ :=
  rc_integrable_of_bound ((hm.meas t).mono (ℱ.le _) le_rfl) K
    fun ω => by rw [abs_of_nonneg (hm.nonneg t ω)]; exact hm.le t ω

theorem rcM_integrable [IsFiniteMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    Integrable (rcM m t) μ :=
  rc_integrable_of_bound ((rcM_measurable hm t).mono (ℱ.le _) le_rfl) (K ^ t)
    fun ω => by rw [abs_of_nonneg (rcM_nonneg hm t ω)]; exact rcM_le hm t ω

theorem rcM_bound (hm : RCRatios μ ℱ m K) (t : ℕ) : ∀ᵐ ω ∂μ, ‖rcM m t ω‖ ≤ K ^ t :=
  Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (rcM_nonneg hm t ω)]; exact rcM_le hm t ω

/-- The one-step property: `E[m_{t+1}ψ] = E[ψ]` for `ℱ_t`-measurable integrable `ψ`. -/
theorem rc_one_step [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) {ψ : Ω → ℝ}
    (hψ : StronglyMeasurable[ℱ t] ψ) (hψi : Integrable ψ μ) :
    ∫ ω, m (t + 1) ω * ψ ω ∂μ = ∫ ω, ψ ω ∂μ := by
  have hmi := rc_m_integrable hm t
  have hprod : Integrable (ψ * m (t + 1)) μ :=
    hψi.mul_bdd (c := K) hmi.aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hm.nonneg t ω)]; exact hm.le t ω)
  calc ∫ ω, m (t + 1) ω * ψ ω ∂μ = ∫ ω, (ψ * m (t + 1)) ω ∂μ := by
        congr 1; funext ω; simp [mul_comm]
    _ = ∫ ω, (μ[ψ * m (t + 1) | ℱ t]) ω ∂μ := (integral_condExp (ℱ.le t)).symm
    _ = ∫ ω, (ψ * μ[m (t + 1) | ℱ t]) ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hψ hprod hmi)
    _ = ∫ ω, ψ ω ∂μ := integral_congr_ae ((hm.mean t).mono fun ω h => by simp [h])

/-- Miao, p. 317: the likelihood-ratio process `{M_t}` is a martingale. -/
theorem rc_martingale [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) :
    Martingale (rcM m) ℱ μ := by
  refine martingale_nat (fun t => (rcM_measurable hm t).stronglyMeasurable)
    (fun t => rcM_integrable hm t) fun t => ?_
  have hmi := rc_m_integrable hm t
  have hprod : Integrable (rcM m t * m (t + 1)) μ :=
    (rcM_integrable hm t).mul_bdd (c := K) hmi.aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hm.nonneg t ω)]; exact hm.le t ω)
  have h1 : rcM m (t + 1) = rcM m t * m (t + 1) := by
    rw [rcM_succ]; funext ω; simp [mul_comm]
  rw [h1]
  refine ((condExp_mul_of_stronglyMeasurable_left (rcM_measurable hm t).stronglyMeasurable
    hprod hmi).trans ?_).symm
  filter_upwards [hm.mean t] with ω h
  simp [h]

/-- `E[M_Tφ] = E[M_sφ]` for `s ≤ T` and `ℱ_s`-measurable integrable `φ`. -/
theorem rc_tower [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) {s T : ℕ} (hsT : s ≤ T)
    {φ : Ω → ℝ} (hφ : StronglyMeasurable[ℱ s] φ) (hφi : Integrable φ μ) :
    ∫ ω, rcM m T ω * φ ω ∂μ = ∫ ω, rcM m s ω * φ ω ∂μ := by
  induction T, hsT using Nat.le_induction with
  | base => rfl
  | succ T hsT ih =>
    rw [← ih]
    have hψ : StronglyMeasurable[ℱ T] (fun ω => rcM m T ω * φ ω) :=
      (rcM_measurable hm T).stronglyMeasurable.mul (hφ.mono (ℱ.mono hsT))
    have hψi : Integrable (fun ω => rcM m T ω * φ ω) μ :=
      hφi.bdd_mul (c := K ^ T) ((rcM_measurable hm T).mono (ℱ.le T) le_rfl).aestronglyMeasurable
        (rcM_bound hm T)
    rw [← rc_one_step hm T hψ hψi, rcM_succ]
    congr 1
    funext ω
    ring

theorem rc_integral_M [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    ∫ ω, rcM m t ω ∂μ = 1 := by
  have h := rc_tower hm (Nat.zero_le t) (φ := fun _ => 1) stronglyMeasurable_const
    (integrable_const 1)
  simpa [rcM_zero] using h

/-- The distorted measure `Q_t = M_t · μ` on `ℱ_t` (Miao, p. 317). -/
noncomputable def rcQ (μ : Measure Ω) (m : ℕ → Ω → ℝ) (t : ℕ) : Measure Ω :=
  μ.withDensity fun ω => ENNReal.ofReal (rcM m t ω)

/-- Miao, p. 317: `E^Q φ = E[M_tφ]`. -/
theorem rc_distorted_integral (hm : RCRatios μ ℱ m K) (t : ℕ) (φ : Ω → ℝ) :
    ∫ ω, φ ω ∂(rcQ μ m t) = ∫ ω, rcM m t ω * φ ω ∂μ := by
  have hM : Measurable (rcM m t) := (rcM_measurable hm t).mono (ℱ.le t) le_rfl
  rw [rcQ, integral_withDensity_eq_integral_toReal_smul hM.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext ω
  rw [ENNReal.toReal_ofReal (rcM_nonneg hm t ω), smul_eq_mul]

/-- `Q_t` is a probability measure. -/
theorem rcQ_isProbability [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    IsProbabilityMeasure (rcQ μ m t) := by
  constructor
  rw [rcQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (rcM_integrable hm t)
      (Eventually.of_forall fun ω => rcM_nonneg hm t ω), rc_integral_M hm t, ENNReal.ofReal_one]

/-- The distorted measures are consistent (Miao, p. 317, "`{M_t}` induces a distorted measure
`Q`"): for `s ≤ T` and `ℱ_s`-measurable `φ`, `E^{Q_T}φ = E^{Q_s}φ`. -/
theorem rc_distorted_consistent [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) {s T : ℕ}
    (hsT : s ≤ T) {φ : Ω → ℝ} (hφ : StronglyMeasurable[ℱ s] φ) (hφi : Integrable φ μ) :
    ∫ ω, φ ω ∂(rcQ μ m T) = ∫ ω, φ ω ∂(rcQ μ m s) := by
  rw [rc_distorted_integral hm, rc_distorted_integral hm, rc_tower hm hsT hφ hφi]

/-- Miao, p. 317: `dQ/dP` on `ℱ_t` is `M_t`. -/
theorem rc_rnDeriv [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    (fun ω => ((rcQ μ m t).rnDeriv μ ω).toReal) =ᵐ[μ] rcM m t := by
  have hM : Measurable (rcM m t) := (rcM_measurable hm t).mono (ℱ.le t) le_rfl
  filter_upwards [Measure.rnDeriv_withDensity μ hM.ennreal_ofReal] with ω h
  simp only [rcQ, h, ENNReal.toReal_ofReal (rcM_nonneg hm t ω)]

/-- Miao, p. 317: relative entropy `E^Q[ln dQ/dP] = E[M_t ln M_t]`. -/
theorem rc_relEntropy [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    ∫ ω, log ((rcQ μ m t).rnDeriv μ ω).toReal ∂(rcQ μ m t) =
      ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ := by
  have hac : rcQ μ m t ≪ μ := withDensity_absolutelyContinuous _ _
  have h1 : (fun ω => ((rcQ μ m t).rnDeriv μ ω).toReal) =ᵐ[rcQ μ m t] rcM m t :=
    hac.ae_eq (rc_rnDeriv hm t)
  rw [integral_congr_ae (g := fun ω => log (rcM m t ω)) (by filter_upwards [h1] with ω h; rw [h]),
    rc_distorted_integral hm t]

theorem rc_MlogM_integrable [IsFiniteMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    Integrable (fun ω => rcM m t ω * log (rcM m t ω)) μ := by
  have hM : Measurable (rcM m t) := (rcM_measurable hm t).mono (ℱ.le t) le_rfl
  exact rc_integrable_of_bound (hM.mul hM.log) (1 + (K ^ t) ^ 2)
    fun ω => rc_abs_mul_log_le (rcM_nonneg hm t ω) (rcM_le hm t ω)

/-- Miao, p. 317: relative entropy is nonnegative, `E[M_t ln M_t] ≥ 0`. -/
theorem rc_entropy_nonneg [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    0 ≤ ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ := by
  have h : ∫ ω, (rcM m t ω - 1) ∂μ ≤ ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ := by
    refine integral_mono ((rcM_integrable hm t).sub (integrable_const 1))
      (rc_MlogM_integrable hm t) fun ω => ?_
    have := InformationTheory.klFun_nonneg (rcM_nonneg hm t ω)
    rw [InformationTheory.klFun_apply] at this
    simp only
    linarith
  rwa [integral_sub (rcM_integrable hm t) (integrable_const 1), rc_integral_M hm t,
    integral_const, probReal_univ, one_smul, sub_self] at h

/-- Miao, p. 317: relative entropy is zero iff `M_t = 1` (a.e.). -/
theorem rc_entropy_eq_zero_iff [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ = 0 ↔ rcM m t =ᵐ[μ] 1 := by
  have hkl : Integrable (fun ω => InformationTheory.klFun (rcM m t ω)) μ := by
    simp only [InformationTheory.klFun_apply]
    exact ((rc_MlogM_integrable hm t).add (integrable_const 1)).sub (rcM_integrable hm t)
  have hint : ∫ ω, InformationTheory.klFun (rcM m t ω) ∂μ =
      ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ := by
    simp only [InformationTheory.klFun_apply]
    rw [integral_sub (f := fun ω => rcM m t ω * log (rcM m t ω) + 1)
      ((rc_MlogM_integrable hm t).add (integrable_const 1)) (rcM_integrable hm t),
      integral_add (f := fun ω => rcM m t ω * log (rcM m t ω)) (rc_MlogM_integrable hm t)
        (integrable_const 1), rc_integral_M hm t,
      integral_const, probReal_univ, one_smul]
    ring
  constructor
  · intro h
    rw [← hint, integral_eq_zero_iff_of_nonneg
      (fun ω => InformationTheory.klFun_nonneg (rcM_nonneg hm t ω)) hkl] at h
    filter_upwards [h] with ω hω
    exact (InformationTheory.klFun_eq_zero_iff (rcM_nonneg hm t ω)).1 hω
  · intro h
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (by filter_upwards [h] with ω hω; simp [hω]),
      integral_zero]

/-- Miao, p. 317: `Q = P` (on `ℱ_t`) iff `M_t = 1` a.e. -/
theorem rcQ_eq_iff [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    rcQ μ m t = μ ↔ rcM m t =ᵐ[μ] 1 := by
  have hM : Measurable (rcM m t) := (rcM_measurable hm t).mono (ℱ.le t) le_rfl
  have hfin : ∫⁻ ω, ENNReal.ofReal (rcM m t ω) ∂μ ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (rcM_integrable hm t)
      (Eventually.of_forall fun ω => rcM_nonneg hm t ω)]
    exact ENNReal.ofReal_ne_top
  have h := withDensity_eq_iff (μ := μ) hM.ennreal_ofReal.aemeasurable
    (aemeasurable_const (b := (1 : ENNReal))) hfin
  have e : (μ.withDensity fun _ => (1 : ENNReal)) = μ := withDensity_one
  rw [e] at h
  rw [rcQ, h]
  constructor
  · intro h'
    filter_upwards [h'] with ω hω
    have h0 := rcM_nonneg hm t ω
    rw [ENNReal.ofReal_eq_one] at hω
    simp [hω]
  · intro h'
    filter_upwards [h'] with ω hω
    simp [hω]

/-- The conditional relative entropy integrand `m_{t+1} ln m_{t+1}`. -/
noncomputable def rcG (m : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := m (t + 1) ω * log (m (t + 1) ω)

theorem rcG_measurable (hm : RCRatios μ ℱ m K) (t : ℕ) : Measurable (rcG m t) := by
  have h := (hm.meas t).mono (ℱ.le _) le_rfl
  exact h.mul h.log

theorem rcG_abs_le (hm : RCRatios μ ℱ m K) (t : ℕ) (ω : Ω) : |rcG m t ω| ≤ 1 + K ^ 2 :=
  rc_abs_mul_log_le (hm.nonneg t ω) (hm.le t ω)

theorem rcG_integrable [IsFiniteMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    Integrable (rcG m t) μ :=
  rc_integrable_of_bound (rcG_measurable hm t) _ (rcG_abs_le hm t)

/-- `E[M_tE(m_{t+1} ln m_{t+1}|ε^t)] = E[M_t m_{t+1} ln m_{t+1}]`. -/
theorem rc_increment_eq [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    ∫ ω, rcM m t ω * (μ[rcG m t | ℱ t]) ω ∂μ = ∫ ω, rcM m t ω * rcG m t ω ∂μ := by
  have hfg : Integrable (rcM m t * rcG m t) μ :=
    (rcG_integrable hm t).bdd_mul (c := K ^ t)
      ((rcM_measurable hm t).mono (ℱ.le t) le_rfl).aestronglyMeasurable (rcM_bound hm t)
  calc ∫ ω, rcM m t ω * (μ[rcG m t | ℱ t]) ω ∂μ = ∫ ω, (rcM m t * μ[rcG m t | ℱ t]) ω ∂μ := rfl
    _ = ∫ ω, (μ[rcM m t * rcG m t | ℱ t]) ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left
          (rcM_measurable hm t).stronglyMeasurable hfg (rcG_integrable hm t)).symm
    _ = ∫ ω, (rcM m t * rcG m t) ω ∂μ := integral_condExp (ℱ.le t)
    _ = ∫ ω, rcM m t ω * rcG m t ω ∂μ := rfl

/-- Miao, p. 318: each conditional relative-entropy term is nonnegative,
`E[M_tE(m_{t+1} ln m_{t+1}|ε^t)] ≥ 0`. -/
theorem rc_increment_nonneg [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    0 ≤ ∫ ω, rcM m t ω * (μ[rcG m t | ℱ t]) ω ∂μ := by
  rw [rc_increment_eq hm t]
  have hMi := rcM_integrable hm t
  have hM1 := rcM_integrable hm (t + 1)
  have hfg : Integrable (fun ω => rcM m t ω * rcG m t ω) μ :=
    (rcG_integrable hm t).bdd_mul (c := K ^ t)
      ((rcM_measurable hm t).mono (ℱ.le t) le_rfl).aestronglyMeasurable (rcM_bound hm t)
  have h : ∫ ω, (rcM m (t + 1) ω - rcM m t ω) ∂μ ≤ ∫ ω, rcM m t ω * rcG m t ω ∂μ := by
    refine integral_mono (hM1.sub hMi) hfg fun ω => ?_
    have := InformationTheory.klFun_nonneg (hm.nonneg t ω)
    rw [InformationTheory.klFun_apply] at this
    rw [rcM_succ]
    simp only [rcG]
    nlinarith [rcM_nonneg hm t ω]
  rwa [integral_sub hM1 hMi, rc_integral_M hm, rc_integral_M hm, sub_self] at h

/-- Miao, p. 317: the decomposition of relative entropy,
`E[M_t ln M_t] = ∑_{j<t} E[M_j E(m_{j+1} ln m_{j+1}|ε^j)]`. -/
theorem rc_entropy_decomp [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ =
      ∑ j ∈ Finset.range t, ∫ ω, rcM m j ω * (μ[rcG m j | ℱ j]) ω ∂μ := by
  induction t with
  | zero => simp [rcM_zero]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih, rc_increment_eq hm t]
    have key : ∀ ω, rcM m (t + 1) ω * log (rcM m (t + 1) ω) =
        m (t + 1) ω * (rcM m t ω * log (rcM m t ω)) + rcM m t ω * rcG m t ω := by
      intro ω
      rw [rcM_succ]
      simp only [rcG]
      by_cases ha : m (t + 1) ω = 0
      · simp [ha]
      by_cases hb : rcM m t ω = 0
      · simp [hb]
      rw [Real.log_mul ha hb]
      ring
    have hψ : StronglyMeasurable[ℱ t] (fun ω => rcM m t ω * log (rcM m t ω)) :=
      ((rcM_measurable hm t).mul (rcM_measurable hm t).log).stronglyMeasurable
    have h1 : Integrable (fun ω => m (t + 1) ω * (rcM m t ω * log (rcM m t ω))) μ :=
      (rc_MlogM_integrable hm t).bdd_mul (c := K) (rc_m_integrable hm t).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hm.nonneg t ω)]; exact hm.le t ω)
    have h2 : Integrable (fun ω => rcM m t ω * rcG m t ω) μ :=
      (rcG_integrable hm t).bdd_mul (c := K ^ t)
        ((rcM_measurable hm t).mono (ℱ.le t) le_rfl).aestronglyMeasurable (rcM_bound hm t)
    simp_rw [key]
    rw [integral_add h1 h2, rc_one_step hm t hψ (rc_MlogM_integrable hm t)]

/-- The summation identity behind (9.45) (Miao, p. 318): for `e_j = ∑_{i<j} c_i` with bounded
`c` and `0 ≤ β < 1`, `(1 − β)∑βʲe_j = β∑βʲc_j`, both series converging. -/
theorem rc_discounted_sum {β C : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {c : ℕ → ℝ}
    (hc : ∀ j, |c j| ≤ C) :
    Summable (fun j => β ^ j * ∑ i ∈ Finset.range j, c i) ∧ Summable (fun j => β ^ j * c j) ∧
      (1 - β) * ∑' j, β ^ j * ∑ i ∈ Finset.range j, c i = β * ∑' j, β ^ j * c j := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hc 0)
  have he : ∀ j, |∑ i ∈ Finset.range j, c i| ≤ j * C := by
    intro j
    calc |∑ i ∈ Finset.range j, c i| ≤ ∑ i ∈ Finset.range j, |c i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range j, C := Finset.sum_le_sum fun i _ => hc i
      _ = j * C := by simp
  have hβn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1
  have hs1 : Summable (fun j => β ^ j * ∑ i ∈ Finset.range j, c i) := by
    refine Summable.of_norm_bounded
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hβn).mul_left C) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j), pow_one]
    calc β ^ j * |∑ i ∈ Finset.range j, c i| ≤ β ^ j * (j * C) :=
          mul_le_mul_of_nonneg_left (he j) (pow_nonneg hβ0 j)
      _ = C * ((j : ℝ) * β ^ j) := by ring
  have hs2 : Summable (fun j => β ^ j * c j) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left C)
      fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j)]
    calc β ^ j * |c j| ≤ β ^ j * C := mul_le_mul_of_nonneg_left (hc j) (pow_nonneg hβ0 j)
      _ = C * β ^ j := by ring
  refine ⟨hs1, hs2, ?_⟩
  have hpart : ∀ n, (1 - β) * ∑ j ∈ Finset.range n, β ^ j * ∑ i ∈ Finset.range j, c i +
      β ^ n * ∑ i ∈ Finset.range n, c i = β * ∑ j ∈ Finset.range n, β ^ j * c j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => β ^ j * c j),
        Finset.sum_range_succ c]
      linear_combination ih
  have hrem : Tendsto (fun n => β ^ n * ∑ i ∈ Finset.range n, c i) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_)
      (by simpa using (tendsto_self_mul_const_pow_of_lt_one hβ0 hβ1).mul_const C)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 n)]
      calc β ^ n * |∑ i ∈ Finset.range n, c i| ≤ β ^ n * (n * C) :=
            mul_le_mul_of_nonneg_left (he n) (pow_nonneg hβ0 n)
        _ = (n : ℝ) * β ^ n * C := by ring
  have hL : Tendsto (fun n => (1 - β) * ∑ j ∈ Finset.range n, β ^ j * ∑ i ∈ Finset.range j, c i +
      β ^ n * ∑ i ∈ Finset.range n, c i) atTop
      (𝓝 ((1 - β) * ∑' j, β ^ j * ∑ i ∈ Finset.range j, c i + 0)) :=
    (hs1.hasSum.tendsto_sum_nat.const_mul _).add hrem
  have hR : Tendsto (fun n => β * ∑ j ∈ Finset.range n, β ^ j * c j) atTop
      (𝓝 (β * ∑' j, β ^ j * c j)) := hs2.hasSum.tendsto_sum_nat.const_mul _
  rw [add_zero] at hL
  exact tendsto_nhds_unique (hL.congr hpart) hR

/-- Miao, p. 318: discounted entropy,
`(1 − β)∑βʲE[M_j ln M_j] = β∑βʲE[M_jE(m_{j+1} ln m_{j+1}|ε^j)]`. -/
theorem rc_discounted_entropy [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (1 - β) * ∑' j, β ^ j * ∫ ω, rcM m j ω * log (rcM m j ω) ∂μ =
      β * ∑' j, β ^ j * ∫ ω, rcM m j ω * (μ[rcG m j | ℱ j]) ω ∂μ := by
  have hc : ∀ j, |∫ ω, rcM m j ω * (μ[rcG m j | ℱ j]) ω ∂μ| ≤ 1 + K ^ 2 := by
    intro j
    rw [rc_increment_eq hm j]
    have h2 : Integrable (fun ω => rcM m j ω * rcG m j ω) μ :=
      (rcG_integrable hm j).bdd_mul (c := K ^ j)
        ((rcM_measurable hm j).mono (ℱ.le j) le_rfl).aestronglyMeasurable (rcM_bound hm j)
    calc |∫ ω, rcM m j ω * rcG m j ω ∂μ| ≤ ∫ ω, |rcM m j ω * rcG m j ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, rcM m j ω * (1 + K ^ 2) ∂μ := by
          refine integral_mono h2.abs ((rcM_integrable hm j).mul_const _) fun ω => ?_
          rw [abs_mul, abs_of_nonneg (rcM_nonneg hm j ω)]
          exact mul_le_mul_of_nonneg_left (rcG_abs_le hm j ω) (rcM_nonneg hm j ω)
      _ = 1 + K ^ 2 := by rw [integral_mul_const, rc_integral_M hm, one_mul]
  have h := (rc_discounted_sum hβ0 hβ1 hc).2.2
  simp_rw [rc_entropy_decomp hm]
  exact h

/-- The discounted entropy `β∑_{j≥0}βʲE[M_jE(m_{j+1} ln m_{j+1}|ε^j)]` of (9.45). -/
noncomputable def rcDiscEntropy (μ : Measure Ω) (ℱ : Filtration ℕ m0) (m : ℕ → Ω → ℝ) (β : ℝ) :
    ℝ :=
  β * ∑' j, β ^ j * ∫ ω, rcM m j ω * (μ[rcG m j | ℱ j]) ω ∂μ

/-- The entropy constraint (9.45) (Miao, p. 318): discounted entropy at most `η₀`. -/
def rcEntropyConstraint (μ : Measure Ω) (ℱ : Filtration ℕ m0) (m : ℕ → Ω → ℝ) (β η₀ : ℝ) :
    Prop :=
  rcDiscEntropy μ ℱ m β ≤ η₀

/-- Discounted entropy is nonnegative, so (9.45) with `η₀ = 0` forces no distortion of any
conditional law (Miao, p. 318). -/
theorem rc_discEntropy_nonneg [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) {β : ℝ}
    (hβ0 : 0 ≤ β) : 0 ≤ rcDiscEntropy μ ℱ m β :=
  mul_nonneg hβ0 (tsum_nonneg fun j => mul_nonneg (pow_nonneg hβ0 j) (rc_increment_nonneg hm j))

/-- `E[M_T ∑_{t<T} φ_t] = ∑_{t<T} E[M_tφ_t]` for adapted integrable `φ`. -/
theorem rc_tower_sum [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (T : ℕ)
    (φ : ℕ → Ω → ℝ) (hφ : ∀ t, StronglyMeasurable[ℱ t] (φ t)) (hφi : ∀ t, Integrable (φ t) μ) :
    ∫ ω, rcM m T ω * ∑ t ∈ Finset.range T, φ t ω ∂μ =
      ∑ t ∈ Finset.range T, ∫ ω, rcM m t ω * φ t ω ∂μ := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun t _ => (hφi t).bdd_mul (c := K ^ T)
    ((rcM_measurable hm T).mono (ℱ.le T) le_rfl).aestronglyMeasurable (rcM_bound hm T)]
  refine Finset.sum_congr rfl fun t ht => ?_
  exact rc_tower hm (Finset.mem_range.1 ht).le (hφ t) (hφi t)

/-- (9.46) (Miao, p. 319), over a finite horizon `T`: the multiplier objective
`E^Q∑βᵗr_t + βθE^Q∑βᵗE(m_{t+1} ln m_{t+1}|ε^t)` equals
`E∑βᵗM_t(r_t + βθE(m_{t+1} ln m_{t+1}|ε^t))`, with `Q = Q_T`. -/
theorem eq_9_46 [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (T : ℕ) (β θ : ℝ)
    (r : ℕ → Ω → ℝ) (hr : ∀ t, StronglyMeasurable[ℱ t] (r t)) (hri : ∀ t, Integrable (r t) μ) :
    ∫ ω, ∑ t ∈ Finset.range T, β ^ t * r t ω ∂(rcQ μ m T) +
        β * θ * ∫ ω, ∑ t ∈ Finset.range T, β ^ t * (μ[rcG m t | ℱ t]) ω ∂(rcQ μ m T) =
      ∑ t ∈ Finset.range T,
        ∫ ω, β ^ t * rcM m t ω * (r t ω + β * θ * (μ[rcG m t | ℱ t]) ω) ∂μ := by
  have hc : ∀ t, StronglyMeasurable[ℱ t] (μ[rcG m t | ℱ t]) := fun t => stronglyMeasurable_condExp
  have hci : ∀ t, Integrable (μ[rcG m t | ℱ t]) μ := fun t => integrable_condExp
  rw [rc_distorted_integral hm, rc_distorted_integral hm,
    rc_tower_sum hm T (fun t ω => β ^ t * r t ω) (fun t => (hr t).const_mul _)
      (fun t => (hri t).const_mul _),
    rc_tower_sum hm T (fun t ω => β ^ t * (μ[rcG m t | ℱ t]) ω) (fun t => (hc t).const_mul _)
      (fun t => (hci t).const_mul _), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : Integrable (fun ω => rcM m t ω * r t ω) μ :=
    (hri t).bdd_mul (c := K ^ t) ((rcM_measurable hm t).mono (ℱ.le t) le_rfl).aestronglyMeasurable
      (rcM_bound hm t)
  have h2 : Integrable (fun ω => rcM m t ω * (μ[rcG m t | ℱ t]) ω) μ :=
    (hci t).bdd_mul (c := K ^ t) ((rcM_measurable hm t).mono (ℱ.le t) le_rfl).aestronglyMeasurable
      (rcM_bound hm t)
  have e : ∀ ω, β ^ t * rcM m t ω * (r t ω + β * θ * (μ[rcG m t | ℱ t]) ω) =
      β ^ t * (rcM m t ω * r t ω) + β * θ * β ^ t * (rcM m t ω * (μ[rcG m t | ℱ t]) ω) := by
    intro ω; ring
  simp_rw [e]
  rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]
  have e1 : ∫ ω, rcM m t ω * (β ^ t * r t ω) ∂μ = β ^ t * ∫ ω, rcM m t ω * r t ω ∂μ := by
    rw [← integral_const_mul]; congr 1; funext ω; ring
  have e2 : ∫ ω, rcM m t ω * (β ^ t * (μ[rcG m t | ℱ t]) ω) ∂μ =
      β ^ t * ∫ ω, rcM m t ω * (μ[rcG m t | ℱ t]) ω ∂μ := by
    rw [← integral_const_mul]; congr 1; funext ω; ring
  rw [e1, e2]
  ring

end Miao.LinearQuadratic

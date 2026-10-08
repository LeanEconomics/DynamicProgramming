/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPsOnPospaces.NoDiscountStopping
import ADPsOnPospaces.SequentialAnalysis
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Sequential analysis revisited

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.2.4 (pp. 117–121).

The belief state `π` evolves by Bayes' rule (3.30), `π' = κ(π, Z)` with `Z` drawn from the
predictive density `ψ(π, ·)` (3.26). The kernel `P` is built on `X = [0, 1]`: the book's
`(0, 1)` is not invariant when the supports of `f₀` and `f₁` differ (`kappa_hits_zero`).

* The belief kernel `P(π, ·)` = law of `κ(π, Z)`, `Z ∼ ψ(π, z) dz`, with
  `(Pg)(π) = ∫ g(κ(π, z))ψ(π, z) dz` (3.26).
* Beliefs are a martingale, and the conditional variance is (3.32)–(3.33):
  `∫ (κ(π, z) − π)²ψ(π, z) dz ≥ π²(1 − π)²Δ(f₀, f₁)`, with `Δ` the triangular discrimination.
* **Lemma 3.2.11**: `Δ(f₀, f₁) > 0` when `f₀ ≠ f₁` on a set of positive measure.
* **Lemma 3.2.12**, in drift form: with `W(π) = 1 − π²`, `(PW)(π) + δ ≤ W(π)` on `(a, b)` for
  `δ = a²(1 − b)²Δ`. A drift bound gives `𝔼_π τ ≤ W(π)/δ ≤ 1/δ` (replacing the martingale
  bound of Theorem A.3.9).
* **Proposition 3.2.10**: when `f₀, f₁` are distinct, Assumption 3.2.1 holds for the sequential
  analysis stopping problem with exit cost `e(π) = min{πL₀, (1 − π)L₁}` (3.27), so the fundamental
  min-optimality properties hold and min-VFI, min-OPI and min-HPI converge.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace SargentStachurski.ADPsOnPospaces

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

/-- The belief space `X = [0, 1]`. -/
abbrev Belief : Type := ↥(Icc (0 : ℝ) 1)

/-- The sequential analysis problem (§1.4, §3.2.4.1): densities `f₀, f₁` on `ℝ`, losses
`L₀, L₁ > 0` and a sampling cost `c > 0`. -/
structure SeqAnalysis where
  /-- the density under hypothesis 0 -/
  f₀ : ℝ → ℝ
  /-- the density under hypothesis 1 -/
  f₁ : ℝ → ℝ
  f₀_nonneg : ∀ z, 0 ≤ f₀ z
  f₁_nonneg : ∀ z, 0 ≤ f₁ z
  f₀_meas : Measurable f₀
  f₁_meas : Measurable f₁
  f₀_int : Integrable f₀
  f₁_int : Integrable f₁
  f₀_one : ∫ z, f₀ z = 1
  f₁_one : ∫ z, f₁ z = 1
  /-- the loss from wrongly accepting `f₀` -/
  L₀ : ℝ
  /-- the loss from wrongly accepting `f₁` -/
  L₁ : ℝ
  /-- the cost of a draw -/
  c : ℝ
  L₀_pos : 0 < L₀
  L₁_pos : 0 < L₁
  c_pos : 0 < c

namespace SeqAnalysis

variable (S : SeqAnalysis)

/-- `ψ(π, z)`, nonnegative on `[0, 1]`. -/
theorem psi_nonneg (π : Belief) (z : ℝ) : 0 ≤ predDensity S.f₀ S.f₁ π.1 z :=
  add_nonneg (mul_nonneg (by linarith [π.2.2]) (S.f₀_nonneg z)) (mul_nonneg π.2.1 (S.f₁_nonneg z))

theorem measurable_psi : Measurable fun p : Belief × ℝ => predDensity S.f₀ S.f₁ p.1.1 p.2 :=
  ((measurable_const.sub (measurable_subtype_coe.comp measurable_fst)).mul
    (S.f₀_meas.comp measurable_snd)).add
    ((measurable_subtype_coe.comp measurable_fst).mul (S.f₁_meas.comp measurable_snd))

theorem integrable_psi (π : ℝ) : Integrable (predDensity S.f₀ S.f₁ π) :=
  (S.f₀_int.const_mul _).add (S.f₁_int.const_mul _)

/-- The predictive distribution `ψ(π, z) dz` as a kernel from `[0, 1]` to `ℝ`. -/
noncomputable def Q : Kernel Belief ℝ :=
  Kernel.withDensity (Kernel.const Belief volume)
    fun π z => ENNReal.ofReal (predDensity S.f₀ S.f₁ π.1 z)

theorem measurable_density :
    Measurable (uncurry fun (π : Belief) (z : ℝ) => ENNReal.ofReal (predDensity S.f₀ S.f₁ π.1 z)) :=
  ENNReal.measurable_ofReal.comp S.measurable_psi

theorem isMarkov_Q : IsMarkovKernel S.Q := by
  refine ⟨fun π => ⟨?_⟩⟩
  rw [Q, Kernel.withDensity_apply _ S.measurable_density, Kernel.const_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (S.integrable_psi π.1)
      (Eventually.of_forall (S.psi_nonneg π)),
    integral_predDensity S.f₀_int S.f₁_int S.f₀_one S.f₁_one, ENNReal.ofReal_one]

/-- Bayes' rule (3.30) as a map `[0, 1] × ℝ → [0, 1]`. -/
noncomputable def kappa (p : Belief × ℝ) : Belief :=
  ⟨bayesUpdate S.f₀ S.f₁ p.1.1 p.2, bayesUpdate_mem_Icc S.f₀_nonneg S.f₁_nonneg p.1.2 p.2⟩

theorem measurable_kappa : Measurable S.kappa :=
  (((measurable_subtype_coe.comp measurable_fst).mul (S.f₁_meas.comp measurable_snd)).div
    S.measurable_psi).subtype_mk

/-- The belief kernel (3.26): `P(π, ·)` is the law of `κ(π, Z)` with `Z ∼ ψ(π, z) dz`. -/
noncomputable def P : Kernel Belief Belief :=
  Kernel.map (Kernel.deterministic id measurable_id ×ₖ S.Q) S.kappa

theorem isMarkov_P : IsMarkovKernel S.P := by
  have := S.isMarkov_Q
  exact Kernel.IsMarkovKernel.map _ S.measurable_kappa

theorem P_apply (π : Belief) : S.P π = (S.Q π).map fun z => S.kappa (π, z) := by
  have := S.isMarkov_Q
  rw [P, Kernel.map_apply _ S.measurable_kappa, Kernel.prod_apply, Kernel.deterministic_apply,
    Measure.dirac_prod, Measure.map_map S.measurable_kappa measurable_prodMk_left]
  rfl

/-- (3.26): `(Pg)(π) = ∫ g(κ(π, z))ψ(π, z) dz` for bounded measurable `g`. -/
theorem integral_P {g : Belief → ℝ} (hg : Measurable g) (π : Belief) :
    ∫ x, g x ∂(S.P π) = ∫ z, g (S.kappa (π, z)) * predDensity S.f₀ S.f₁ π.1 z := by
  have hk : Measurable fun z => S.kappa (π, z) := S.measurable_kappa.comp measurable_prodMk_left
  rw [S.P_apply, integral_map hk.aemeasurable hg.aestronglyMeasurable, Q,
    Kernel.withDensity_apply _ S.measurable_density, Kernel.const_apply]
  have hd : Measurable fun z => (predDensity S.f₀ S.f₁ π.1 z).toNNReal :=
    (S.measurable_psi.comp measurable_prodMk_left).real_toNNReal
  rw [show (fun z => ENNReal.ofReal (predDensity S.f₀ S.f₁ π.1 z)) =
      fun z => ((predDensity S.f₀ S.f₁ π.1 z).toNNReal : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul hd]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (S.psi_nonneg π z), smul_eq_mul]
  ring

/-! ### The triangular discrimination -/

/-- The triangular discrimination `Δ(f₀, f₁) = ∫ (f₁ − f₀)²/(f₀ + f₁)` (the integrand is `0` where
`f₀ + f₁ = 0`). -/
noncomputable def triDisc : ℝ := ∫ z, (S.f₁ z - S.f₀ z) ^ 2 / (S.f₀ z + S.f₁ z)

theorem triDisc_integrand_nonneg (z : ℝ) : 0 ≤ (S.f₁ z - S.f₀ z) ^ 2 / (S.f₀ z + S.f₁ z) :=
  div_nonneg (sq_nonneg _) (add_nonneg (S.f₀_nonneg z) (S.f₁_nonneg z))

theorem triDisc_integrand_le (z : ℝ) :
    (S.f₁ z - S.f₀ z) ^ 2 / (S.f₀ z + S.f₁ z) ≤ S.f₀ z + S.f₁ z := by
  have h0 := S.f₀_nonneg z
  have h1 := S.f₁_nonneg z
  rcases (add_nonneg h0 h1).eq_or_lt with h | h
  · rw [← h, div_zero]
  · rw [div_le_iff₀ h]
    nlinarith

theorem integrable_triDisc :
    Integrable fun z => (S.f₁ z - S.f₀ z) ^ 2 / (S.f₀ z + S.f₁ z) := by
  refine (S.f₀_int.add S.f₁_int).mono' (((S.f₁_meas.sub S.f₀_meas).pow_const 2).div
    (S.f₀_meas.add S.f₁_meas)).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (S.triDisc_integrand_nonneg z)]
  exact S.triDisc_integrand_le z

theorem triDisc_nonneg : 0 ≤ S.triDisc := integral_nonneg S.triDisc_integrand_nonneg

/-- **Lemma 3.2.11** (p. 120): if `f₀` and `f₁` are distinct (not equal almost everywhere), the
triangular discrimination is positive. -/
theorem lemma_3_2_11 (h : ¬ S.f₀ =ᵐ[volume] S.f₁) : 0 < S.triDisc := by
  refine (integral_pos_iff_support_of_nonneg S.triDisc_integrand_nonneg
    S.integrable_triDisc).2 ?_
  rw [Filter.EventuallyEq, ae_iff] at h
  refine (pos_iff_ne_zero.2 h).trans_le (measure_mono fun z hz => ?_)
  have hz' : S.f₀ z ≠ S.f₁ z := hz
  have hs : 0 < S.f₀ z + S.f₁ z := by
    rcases (add_nonneg (S.f₀_nonneg z) (S.f₁_nonneg z)).eq_or_lt with h0 | h0
    · exact absurd (by linarith [S.f₀_nonneg z, S.f₁_nonneg z]) hz'
    · exact h0
  exact (div_pos (pow_pos (abs_pos.2 (sub_ne_zero.2 hz'.symm)) 2 |>.trans_eq
    (sq_abs _)) hs).ne'

/-! ### Beliefs: martingale and conditional variance -/

theorem measurable_val : Measurable fun x : Belief => (x : ℝ) := measurable_subtype_coe

/-- Beliefs are a martingale (§3.2.4.2): `∫ π' P(π, dπ') = π`. -/
theorem integral_P_id (π : Belief) : ∫ x, (x : ℝ) ∂(S.P π) = π := by
  rw [S.integral_P measurable_val]
  exact integral_bayesUpdate_mul_predDensity S.f₀_nonneg S.f₁_nonneg S.f₁_one π.2

theorem integrable_bounded_mul_psi {h : ℝ → ℝ} (hh : Measurable h) (hb : ∀ z, |h z| ≤ 1)
    (π : Belief) : Integrable fun z => h z * predDensity S.f₀ S.f₁ π.1 z :=
  (S.integrable_psi π.1).bdd_mul hh.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb z)

theorem measurable_bayes (π : Belief) : Measurable (bayesUpdate S.f₀ S.f₁ π.1) :=
  (measurable_const.mul S.f₁_meas).div ((measurable_const.mul S.f₀_meas).add
    (measurable_const.mul S.f₁_meas))

theorem abs_bayes_le (π : Belief) (z : ℝ) : |bayesUpdate S.f₀ S.f₁ π.1 z| ≤ 1 := by
  obtain ⟨h0, h1⟩ := bayesUpdate_mem_Icc S.f₀_nonneg S.f₁_nonneg π.2 z
  rw [abs_le]
  constructor <;> linarith

/-- The conditional variance of beliefs:
`∫ π'² P(π, dπ') − π² = ∫ (κ(π, z) − π)²ψ(π, z) dz`. -/
theorem integral_P_sq (π : Belief) :
    ∫ x, (x : ℝ) ^ 2 ∂(S.P π) - (π : ℝ) ^ 2 =
      ∫ z, (bayesUpdate S.f₀ S.f₁ π.1 z - π) ^ 2 * predDensity S.f₀ S.f₁ π.1 z := by
  have hκ := S.measurable_bayes π
  have hb := S.abs_bayes_le π
  rw [S.integral_P (measurable_val.pow_const 2)]
  have i1 := S.integrable_bounded_mul_psi (hκ.pow_const 2) (fun z => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hb z)) π
  have i2 := S.integrable_bounded_mul_psi hκ hb π
  have i3 := S.integrable_psi π.1
  have hexp : (fun z => (bayesUpdate S.f₀ S.f₁ π.1 z - π) ^ 2 * predDensity S.f₀ S.f₁ π.1 z) =
      fun z => (bayesUpdate S.f₀ S.f₁ π.1 z ^ 2 * predDensity S.f₀ S.f₁ π.1 z -
        2 * π * (bayesUpdate S.f₀ S.f₁ π.1 z * predDensity S.f₀ S.f₁ π.1 z)) +
          π ^ 2 * predDensity S.f₀ S.f₁ π.1 z := by
    funext z
    ring
  rw [hexp, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    integral_bayesUpdate_mul_predDensity S.f₀_nonneg S.f₁_nonneg S.f₁_one π.2,
    integral_predDensity S.f₀_int S.f₁_int S.f₀_one S.f₁_one]
  · simp only [kappa]
    ring
  · exact i1
  · exact i2.const_mul _
  · exact i1.sub (i2.const_mul _)
  · exact i3.const_mul _

/-- (3.32)–(3.33) (p. 121): for `0 < π < 1`,
`∫ (κ(π, z) − π)²ψ(π, z) dz ≥ π²(1 − π)²Δ(f₀, f₁)`. -/
theorem variance_ge (π : Belief) (h0 : 0 < (π : ℝ)) (h1 : (π : ℝ) < 1) :
    (π : ℝ) ^ 2 * (1 - π) ^ 2 * S.triDisc ≤
      ∫ z, (bayesUpdate S.f₀ S.f₁ π.1 z - π) ^ 2 * predDensity S.f₀ S.f₁ π.1 z := by
  rw [triDisc, ← integral_const_mul]
  refine integral_mono (S.integrable_triDisc.const_mul _)
    (S.integrable_bounded_mul_psi (((S.measurable_bayes π).sub measurable_const).pow_const 2)
      (fun z => ?_) π) fun z => ?_
  · obtain ⟨hk0, hk1⟩ := bayesUpdate_mem_Icc S.f₀_nonneg S.f₁_nonneg π.2 z
    have hp0 := π.2.1
    have hp1 := π.2.2
    simp only [Pi.sub_apply]
    rw [abs_of_nonneg (sq_nonneg _), sq_le_one_iff_abs_le_one, abs_le]
    constructor <;> linarith
  · have ha := S.f₀_nonneg z
    have hb := S.f₁_nonneg z
    simp only [bayesUpdate, predDensity]
    set a := S.f₀ z
    set b := S.f₁ z
    set p : ℝ := (π : ℝ)
    have hq : 0 ≤ 1 - p := by linarith
    have hqa : 0 ≤ (1 - p) * a := mul_nonneg hq ha
    have hpb : 0 ≤ p * b := mul_nonneg h0.le hb
    rcases (add_nonneg hqa hpb).eq_or_lt with hψ | hψ
    · have hA : (1 - p) * a = 0 := by linarith
      have hB : p * b = 0 := by linarith
      have ha0 : a = 0 := (mul_eq_zero.1 hA).resolve_left (sub_ne_zero.2 (ne_of_gt h1))
      have hb0 : b = 0 := (mul_eq_zero.1 hB).resolve_left h0.ne'
      simp [ha0, hb0]
    · have hle : (1 - p) * a + p * b ≤ a + b := by nlinarith
      have key : (p * b / ((1 - p) * a + p * b) - p) ^ 2 * ((1 - p) * a + p * b) =
          p ^ 2 * (1 - p) ^ 2 * ((b - a) ^ 2 / ((1 - p) * a + p * b)) := by
        field_simp
        ring
      rw [key]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (sq_nonneg _) hψ hle)
        (by positivity)

/-! ### Lemma 3.2.12 in drift form -/

/-- The Lyapunov function `W(π) = 1 − π²`. -/
noncomputable def W : BM Belief :=
  ⟨fun x => 1 - (x : ℝ) ^ 2, measurable_const.sub (measurable_val.pow_const 2), ⟨1, fun x => by
    have h0 := x.2.1
    have h1 := x.2.2
    rw [abs_le]
    constructor <;> nlinarith⟩⟩

theorem W_nonneg : 0 ≤ W := fun x => by
  have h0 := x.2.1
  have h1 := x.2.2
  change 0 ≤ 1 - (x : ℝ) ^ 2
  nlinarith

/-- `(PW)(π) = 1 − π² − ∫ (κ(π, z) − π)²ψ(π, z) dz`. -/
theorem markovOp_W (π : Belief) :
    markovOp S.P W.toFun π = 1 - (π : ℝ) ^ 2 -
      ∫ z, (bayesUpdate S.f₀ S.f₁ π.1 z - π) ^ 2 * predDensity S.f₀ S.f₁ π.1 z := by
  have := S.isMarkov_P
  have hsq : Integrable (fun x : Belief => (x : ℝ) ^ 2) (S.P π) :=
    Integrable.of_bound (measurable_val.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        have h0 := x.2.1
        have h1 := x.2.2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith)
  have h := S.integral_P_sq π
  simp only [markovOp, W]
  rw [integral_sub (integrable_const 1) hsq, integral_const, probReal_univ, one_smul]
  linarith

/-- **Lemma 3.2.12** (p. 120), drift form: for `0 < a ≤ π ≤ b < 1`,
`(PW)(π) + a²(1 − b)²Δ(f₀, f₁) ≤ W(π)`. With the drift criterion this bounds `𝔼_π τ` by
`W(π)/δ < 1/δ`, `δ = a²(1 − b)²Δ`. -/
theorem lemma_3_2_12 {a b : ℝ} (ha : 0 < a) (hb : b < 1) (π : Belief) (hπa : a ≤ π)
    (hπb : (π : ℝ) ≤ b) :
    markovOp S.P W.toFun π + a ^ 2 * (1 - b) ^ 2 * S.triDisc ≤ W.toFun π := by
  have hv := S.variance_ge π (ha.trans_le hπa) (hπb.trans_lt hb)
  rw [S.markovOp_W]
  have h1 : a ^ 2 * (1 - b) ^ 2 ≤ (π : ℝ) ^ 2 * (1 - π) ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ ha.le hπa 2) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
      (sq_nonneg _) (sq_nonneg _)
  have h2 := mul_le_mul_of_nonneg_right h1 S.triDisc_nonneg
  change _ ≤ 1 - (π : ℝ) ^ 2
  linarith

/-! ### The stopping problem and Proposition 3.2.10 -/

/-- The exit cost (3.27): `e(π) = min{πL₀, (1 − π)L₁}`. -/
noncomputable def exitCost : BM Belief :=
  ⟨fun x => min ((x : ℝ) * S.L₀) ((1 - x) * S.L₁),
    (measurable_val.mul measurable_const).min ((measurable_const.sub measurable_val).mul
      measurable_const), ⟨S.L₀ + S.L₁, fun x => by
        have h0 := x.2.1
        have h1 := x.2.2
        have hL₀ := S.L₀_pos
        have hL₁ := S.L₁_pos
        rw [abs_of_nonneg (le_min (by positivity) (mul_nonneg (by linarith) hL₁.le))]
        exact (min_le_left _ _).trans (by nlinarith)⟩⟩

/-- The sequential analysis problem as a no-discount stopping problem (§3.2.4.1): exit cost
(3.27), constant flow cost `c` and the belief kernel (3.26). -/
noncomputable abbrev stopping : NoDiscountStopping Belief where
  P := S.P
  e := S.exitCost
  e_nonneg x := le_min (mul_nonneg x.2.1 S.L₀_pos.le) (mul_nonneg (by linarith [x.2.2])
    S.L₁_pos.le)
  c := BM.const S.c
  c_nonneg _ := S.c_pos.le

attribute [local instance] SeqAnalysis.isMarkov_P

/-- Off the certain exit region, `c/L₀ < π < 1 − c/L₁` (§3.2.4.2). -/
theorem bounds_of_notMem_Ebar {π : Belief} (h : π ∉ S.stopping.Ebar) :
    S.c / S.L₀ < π ∧ (π : ℝ) < 1 - S.c / S.L₁ := by
  have h' : ¬ (S.exitCost.toFun π ≤ S.c) := h
  rw [not_le] at h'
  have h : S.c < min ((π : ℝ) * S.L₀) ((1 - π) * S.L₁) := h'
  have h1 : S.c < π * S.L₀ := h.trans_le (min_le_left _ _)
  have h2 : S.c < (1 - π) * S.L₁ := h.trans_le (min_le_right _ _)
  constructor
  · rw [div_lt_iff₀ S.L₀_pos]
    exact h1
  · have : S.c / S.L₁ < 1 - π := by
      rw [div_lt_iff₀ S.L₁_pos]
      exact h2
    linarith

/-- §3.2.4.2: if `f₀` and `f₁` are distinct, Assumption 3.2.1 holds, with `sup_π 𝔼_π τ̄ ≤ 1/δ`,
`δ = (c/L₀)²(c/L₁)²Δ(f₀, f₁)`. -/
theorem assumption321 (h : ¬ S.f₀ =ᵐ[volume] S.f₁) : S.stopping.Assumption321 := by
  have hΔ := S.lemma_3_2_11 h
  have ha : 0 < S.c / S.L₀ := div_pos S.c_pos S.L₀_pos
  have hb : 1 - S.c / S.L₁ < 1 := by linarith [div_pos S.c_pos S.L₁_pos]
  refine S.stopping.assumption321_of_drift W_nonneg
    (δ := (S.c / S.L₀) ^ 2 * (1 - (1 - S.c / S.L₁)) ^ 2 * S.triDisc)
    (by have : 0 < 1 - (1 - S.c / S.L₁) := by linarith
        positivity) fun π hπ => ?_
  obtain ⟨h1, h2⟩ := S.bounds_of_notMem_Ebar hπ
  exact S.lemma_3_2_12 ha hb π h1.le h2.le

/-- **Proposition 3.2.10** (p. 119): if `f₀` and `f₁` are distinct, then for the sequential
analysis ADP the fundamental min-optimality properties hold, and min-VFI, min-OPI and min-HPI
all converge. -/
theorem proposition_3_2_10 (h : ¬ S.f₀ =ᵐ[volume] S.f₁) :
    S.stopping.adp.MinFundamentalOptimality
        (S.stopping.proposition_3_2_5 (S.assumption321 h)).wellPosed ∧
      ∃ vstar, S.stopping.adp.IsMinValueFunction vstar ∧ S.stopping.adp.MinVFIConverges vstar ∧
        ∀ g, S.stopping.adp.IsMinSelector g → S.stopping.adp.MinOPIConverges g vstar ∧
          S.stopping.adp.MinHPIConverges
            (S.stopping.proposition_3_2_5 (S.assumption321 h)).wellPosed g vstar :=
  S.stopping.theorem_3_2_9 (S.assumption321 h)

/-- (3.25) and (3.28) agree with the Bellman operator (1.58) of §1.4: the Bellman min-operator of
the stopping ADP is `min{πL₀, (1 − π)L₁, c + ∫ g(κ(π, z))ψ(π, z) dz}`. -/
theorem minBellman_eq_seqBellman (g : {g : BM Belief // 0 ≤ g}) (π : Belief) :
    (S.stopping.T (S.stopping.minGreedy g) g.1).toFun π =
      seqBellman S.f₀ S.f₁ S.L₀ S.L₁ S.c
        (fun x => if h : x ∈ Icc (0 : ℝ) 1 then g.1.toFun ⟨x, h⟩ else 0) π := by
  rw [NoDiscountStopping.T_minGreedy_apply]
  have hint : ∫ z, g.1.toFun (S.kappa (π, z)) * predDensity S.f₀ S.f₁ π.1 z =
      ∫ z, (fun x => if h : x ∈ Icc (0 : ℝ) 1 then g.1.toFun ⟨x, h⟩ else 0)
        (bayesUpdate S.f₀ S.f₁ π.1 z) * predDensity S.f₀ S.f₁ π.1 z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    split_ifs with hz
    · rfl
    · exact absurd (bayesUpdate_mem_Icc S.f₀_nonneg S.f₁_nonneg π.2 z) hz
  simp only [seqBellman, markovOp]
  rw [S.integral_P g.1.measurable', hint, ← min_assoc]
  rfl

end SeqAnalysis

/-- **The belief space `(0, 1)` of §3.2.4.1 is not invariant.** With `f₀ = 𝟙_{[0, 1]}` and
`f₁ = 2 · 𝟙_{[0, 1/2]}` (both densities), every `π ∈ (0, 1)` and every `z ∈ (1/2, 1]` give
`ψ(π, z) > 0` and `κ(π, z) = 0`: from any interior belief the posterior jumps to `0` with
probability `(1 − π)/2 > 0`. -/
theorem kappa_hits_zero :
    ∃ f₀ f₁ : ℝ → ℝ, (∀ z, 0 ≤ f₀ z) ∧ (∀ z, 0 ≤ f₁ z) ∧ (∫ z, f₀ z = 1) ∧ (∫ z, f₁ z = 1) ∧
      ∀ π : ℝ, 0 < π → π < 1 → ∀ z ∈ Ioc (1 / 2 : ℝ) 1,
        0 < predDensity f₀ f₁ π z ∧ bayesUpdate f₀ f₁ π z = 0 := by
  refine ⟨(Icc (0 : ℝ) 1).indicator fun _ => 1, (Icc (0 : ℝ) (1 / 2)).indicator fun _ => 2,
    fun z => indicator_nonneg (fun _ _ => zero_le_one) z,
    fun z => indicator_nonneg (fun _ _ => zero_le_two) z, ?_, ?_, fun π h0 h1 z hz => ?_⟩
  · rw [integral_indicator_const (1 : ℝ) measurableSet_Icc, Real.volume_real_Icc]
    norm_num
  · rw [integral_indicator_const (2 : ℝ) measurableSet_Icc, Real.volume_real_Icc]
    norm_num
  · have hz1 : z ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
    have hz2 : z ∉ Icc (0 : ℝ) (1 / 2) := fun h => absurd h.2 (not_le.2 hz.1)
    simp only [predDensity, bayesUpdate, indicator_of_mem hz1, indicator_of_notMem hz2,
      mul_zero, add_zero, zero_div, and_true, mul_one]
    linarith

end SargentStachurski.ADPsOnPospaces

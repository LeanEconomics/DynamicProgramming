/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.DualSpaces

/-!
# The dual of `L_p` for `1 < p < ∞`

SLP §15.1, Example 4, pp. 448–450: for `1 ≤ p < ∞` and `1/p + 1/q = 1` the dual of
`L_p(Z, 𝒵, μ)` is `L_q(Z, 𝒵, μ)`. The book states this without proof. The case `p = 1` (with
σ-finiteness) is `l1_dual_sigmaFinite` in `DualSpaces`. Here `1 < p < ∞` and `μ` is a finite
measure, which covers the probability spaces the book uses.

* **Example 4** (`example_15_4`): `y ↦ (x ↦ ∫ y x dμ)` is an isometric isomorphism from `L_q`
  onto `L_p*` (`dualLp`).

Proof, for `φ ∈ L_p*`:
* `dualSignedMeasure`: `A ↦ φ(1_A)` is a signed measure. Countable additivity comes from
  `hasSum_indicatorConstLp`: indicators of disjoint unions converge in `L_p`.
* It is absolutely continuous with respect to `μ` (`dualSignedMeasure_ac`). Its Radon–Nikodym
  density `g = dualDensity` satisfies `∫_A g = φ(1_A)` (`setIntegral_dualDensity`), and
  `φ(s) = ∫ g s` for simple `s` (`dualDensity_simpleFunc`).
* `eLpNorm_dualDensity_le`: `‖g‖_q ≤ ‖φ‖`. Take simple `sₖ → g` with the sign of `g` and
  `|sₖ| ≤ |g|` (`signedApprox`). The test functions `sgn(sₖ)|sₖ|^{q−1}` give
  `∫ |sₖ|^q ≤ ‖φ‖^q`, and Fatou's lemma gives the bound for `g`.
* `exists_preimage_pairLqLp`: `φ = (x ↦ ∫ g x)`, because both sides are continuous and agree
  on indicators, which are dense in `L_p`. `pairLqLp_injective` gives injectivity for every
  σ-finite measure.

σ-finite and arbitrary measures, `1 < p < ∞`: see `DualLpSigmaFinite`
(`example_15_4_sigmaFinite`, `example_15_4_general`).
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Metric Set MeasureTheory Function
open scoped ENNReal symmDiff

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The finite unions of disjoint sets give sums of indicators. -/
theorem indicatorConstLp_biUnion [IsFiniteMeasure μ] {f : ℕ → Set Z} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Disjoint on f)) (s : Finset ℕ) :
    indicatorConstLp p (s.measurableSet_biUnion fun i _ => hf i) (measure_ne_top μ _) (1 : ℝ) =
      ∑ i ∈ s, indicatorConstLp p (hf i) (measure_ne_top μ _) (1 : ℝ) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine Lp.ext ?_
    filter_upwards [indicatorConstLp_coeFn (p := p) (μ := μ) (c := (1 : ℝ))
      (hs := Finset.measurableSet_biUnion (∅ : Finset ℕ) fun i _ => hf i)
      (hμs := measure_ne_top μ _), Lp.coeFn_zero ℝ p μ] with z h1 h2
    rw [h1, h2]; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    refine Lp.ext ?_
    filter_upwards [indicatorConstLp_coeFn (p := p) (μ := μ) (c := (1 : ℝ))
      (hs := Finset.measurableSet_biUnion (insert a s) fun i _ => hf i)
      (hμs := measure_ne_top μ _),
      Lp.coeFn_add (indicatorConstLp p (hf a) (measure_ne_top μ _) (1 : ℝ))
        (indicatorConstLp p (s.measurableSet_biUnion fun i _ => hf i) (measure_ne_top μ _) 1),
      indicatorConstLp_coeFn (p := p) (μ := μ) (c := (1 : ℝ)) (hs := hf a)
        (hμs := measure_ne_top μ _),
      indicatorConstLp_coeFn (p := p) (μ := μ) (c := (1 : ℝ))
        (hs := s.measurableSet_biUnion fun i _ => hf i) (hμs := measure_ne_top μ _)]
      with z h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4, Finset.set_biUnion_insert]
    have hdis : Disjoint (f a) (⋃ i ∈ s, f i) := by
      rw [Set.disjoint_iUnion₂_right]
      exact fun i hi => hd (fun h => ha (h ▸ hi))
    rw [Set.indicator_union_of_disjoint hdis]


/-- The disjoint unions converge in `Lp`. -/
theorem hasSum_indicatorConstLp [IsFiniteMeasure μ] (hp : p ≠ ∞) {f : ℕ → Set Z}
    (hf : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    HasSum (fun i => indicatorConstLp p (hf i) (measure_ne_top μ _) (1 : ℝ))
      (indicatorConstLp p (MeasurableSet.iUnion hf) (measure_ne_top μ _) (1 : ℝ)) := by
  unfold HasSum
  have e : (fun s : Finset ℕ => ∑ i ∈ s, indicatorConstLp p (hf i) (measure_ne_top μ _) (1 : ℝ)) =
      fun s => indicatorConstLp p (s.measurableSet_biUnion fun i _ => hf i) (measure_ne_top μ _)
        (1 : ℝ) := funext fun s => (indicatorConstLp_biUnion hf hd s).symm
  rw [e]
  refine tendsto_indicatorConstLp_set hp ?_
  have hsub : ∀ s : Finset ℕ, (⋃ i ∈ s, f i) ⊆ ⋃ i, f i := fun s =>
    iUnion₂_subset fun i _ => subset_iUnion f i
  have e2 : ∀ s : Finset ℕ, (⋃ i ∈ s, f i) ∆ (⋃ i, f i) = (⋃ i, f i) \ ⋃ i ∈ s, f i :=
    fun s => symmDiff_of_le (hsub s)
  simp only [e2]
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := fun s : Finset ℕ =>
      (⋃ i, f i) \ ⋃ i ∈ s, f i)
    (fun s => ((MeasurableSet.iUnion hf).diff
      (s.measurableSet_biUnion fun i _ => hf i)).nullMeasurableSet)
    (fun s t hst z hz => ⟨hz.1, fun h' => hz.2 (by
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 h'
      exact mem_iUnion₂.2 ⟨i, hst hi, hzi⟩)⟩)
    ⟨∅, measure_ne_top μ _⟩
  have hempty : (⋂ s : Finset ℕ, (⋃ i, f i) \ ⋃ i ∈ s, f i) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 (mem_iInter.1 hz ∅).1
    exact (mem_iInter.1 hz {i}).2 (mem_iUnion₂.2 ⟨i, Finset.mem_singleton_self i, hi⟩)
  rw [hempty, measure_empty] at hlim
  exact hlim

open Classical in
/-- The signed measure `A ↦ φ(1_A)` of a functional `φ ∈ L_p*`, for a finite measure. -/
noncomputable def dualSignedMeasure [IsFiniteMeasure μ] (hp : p ≠ ∞)
    (φ : StrongDual ℝ (Lp ℝ p μ)) : SignedMeasure Z where
  measureOf' A := if h : MeasurableSet A then φ (indicatorConstLp p h (measure_ne_top μ A) 1)
    else 0
  empty' := by
    simp only [MeasurableSet.empty, ↓reduceDIte]
    rw [indicatorConstLp_empty, map_zero]
  not_measurable' A hA := by simp [hA]
  m_iUnion' f hf hd := by
    simp only [MeasurableSet.iUnion hf, hf, ↓reduceDIte]
    exact (hasSum_indicatorConstLp hp hf hd).mapL φ


/-- `dualSignedMeasure hp φ A = φ(1_A)` for measurable `A`. -/
theorem dualSignedMeasure_apply [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ))
    {A : Set Z} (hA : MeasurableSet A) :
    dualSignedMeasure hp φ A = φ (indicatorConstLp p hA (measure_ne_top μ A) 1) := by
  simp [dualSignedMeasure, hA]

omit [Fact (1 ≤ p)] in
/-- The indicator of a null set is `0` in `L_p`. -/
theorem indicatorConstLp_eq_zero_of_null {A : Set Z} (hA : MeasurableSet A) (hμA : μ A = 0)
    (c : ℝ) : indicatorConstLp (μ := μ) p hA (by simp [hμA]) c = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [indicatorConstLp_coeFn (p := p) (μ := μ) (c := c) (hs := hA)
    (hμs := by simp [hμA]), measure_eq_zero_iff_ae_notMem.1 hμA] with z h1 h2
  rw [h1, indicator_of_notMem h2]; rfl

/-- `A ↦ φ(1_A)` is absolutely continuous with respect to `μ`. -/
theorem dualSignedMeasure_ac [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    dualSignedMeasure hp φ ≪ᵥ μ.toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun A hA h0 => ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at h0
  rw [dualSignedMeasure_apply hp φ hA, indicatorConstLp_eq_zero_of_null hA h0, map_zero]

/-- The Radon–Nikodym density of `A ↦ φ(1_A)`. -/
noncomputable def dualDensity [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    Z → ℝ :=
  (dualSignedMeasure hp φ).rnDeriv μ

/-- The density of `A ↦ φ(1_A)` is integrable. -/
theorem integrable_dualDensity [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    Integrable (dualDensity hp φ) μ := SignedMeasure.integrable_rnDeriv _ _

/-- `∫_A g dμ = φ(1_A)` for the density `g` of `A ↦ φ(1_A)`. -/
theorem setIntegral_dualDensity [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ))
    {A : Set Z} (hA : MeasurableSet A) :
    ∫ z in A, dualDensity hp φ z ∂μ = φ (indicatorConstLp p hA (measure_ne_top μ A) 1) := by
  rw [← dualSignedMeasure_apply hp φ hA,
    ← SignedMeasure.withDensityᵥ_rnDeriv_eq _ μ (dualSignedMeasure_ac hp φ)]
  exact (withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hA).symm


omit [Fact (1 ≤ p)] in
/-- `1_A c = c · 1_A` in `L_p`. -/
theorem indicatorConstLp_eq_smul {A : Set Z} (hA : MeasurableSet A) (hμA : μ A ≠ ∞) (c : ℝ) :
    indicatorConstLp p hA hμA c = c • indicatorConstLp p hA hμA (1 : ℝ) := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hA) (hμs := hμA) (c := c),
    Lp.coeFn_smul c (indicatorConstLp p hA hμA (1 : ℝ)),
    indicatorConstLp_coeFn (p := p) (hs := hA) (hμs := hμA) (c := (1 : ℝ))] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  by_cases hz : z ∈ A <;> simp [hz]

/-- `φ(s) = ∫ g s` for simple `s`, where `g` is the density of `A ↦ φ(1_A)`. -/
theorem dualDensity_simpleFunc [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ))
    (s : SimpleFunc Z ℝ) :
    φ ((s.memLp_of_isFiniteMeasure p μ).toLp s) = ∫ z, dualDensity hp φ z * s z ∂μ := by
  induction s using SimpleFunc.induction with
  | const c hA =>
    rename_i A
    have e : (SimpleFunc.memLp_of_isFiniteMeasure
        (SimpleFunc.piecewise A hA (SimpleFunc.const Z c) (SimpleFunc.const Z 0)) p μ).toLp _ =
        indicatorConstLp p hA (measure_ne_top μ A) c := by
      refine Lp.ext ?_
      filter_upwards [MemLp.coeFn_toLp (SimpleFunc.memLp_of_isFiniteMeasure
        (SimpleFunc.piecewise A hA (SimpleFunc.const Z c) (SimpleFunc.const Z 0)) p μ),
        indicatorConstLp_coeFn (p := p) (μ := μ) (c := c) (hs := hA)
          (hμs := measure_ne_top μ A)] with z h1 h2
      rw [h1, h2, SimpleFunc.coe_piecewise]
      by_cases hz : z ∈ A <;> simp [hz]
    rw [e, indicatorConstLp_eq_smul, map_smul, smul_eq_mul,
      ← setIntegral_dualDensity hp φ hA, ← integral_const_mul, ← integral_indicator hA]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    rw [SimpleFunc.coe_piecewise]
    by_cases hz : z ∈ A <;> simp [hz, mul_comm]
  | @add f g _ hf hg =>
    have hfi : Integrable (fun z => dualDensity hp φ z * f z) μ :=
      (integrable_dualDensity hp φ).mul_of_top_left (f.memLp_top μ)
    have hgi : Integrable (fun z => dualDensity hp φ z * g z) μ :=
      (integrable_dualDensity hp φ).mul_of_top_left (g.memLp_top μ)
    have e : (SimpleFunc.memLp_of_isFiniteMeasure (f + g) p μ).toLp _ =
        (f.memLp_of_isFiniteMeasure p μ).toLp f + (g.memLp_of_isFiniteMeasure p μ).toLp g :=
      MemLp.toLp_add _ _
    rw [e, map_add, hf, hg, ← integral_add hfi hgi]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp [mul_add]


/-- The simple approximants `(g⁺)ₖ − (g⁻)ₖ` of a real function `g`, built from `eapprox`. -/
noncomputable def signedApprox (g : Z → ℝ) (k : ℕ) : SimpleFunc Z ℝ :=
  (SimpleFunc.eapprox (fun z => ENNReal.ofReal (g z)) k).map ENNReal.toReal -
    (SimpleFunc.eapprox (fun z => ENNReal.ofReal (-g z)) k).map ENNReal.toReal

/-- `eapprox f k ≤ f`. -/
theorem eapprox_le_self {f : Z → ℝ≥0∞} (hf : Measurable f) (k : ℕ) (z : Z) :
    SimpleFunc.eapprox f k z ≤ f z :=
  (le_iSup (fun n => SimpleFunc.eapprox f n z) k).trans_eq (SimpleFunc.iSup_eapprox_apply hf z)

/-- `eapprox f k → f` pointwise. -/
theorem tendsto_eapprox_apply {f : Z → ℝ≥0∞} (hf : Measurable f) (z : Z) :
    Tendsto (fun k => SimpleFunc.eapprox f k z) atTop (𝓝 (f z)) := by
  rw [← SimpleFunc.iSup_eapprox_apply hf z]
  exact tendsto_atTop_iSup fun m n h => SimpleFunc.monotone_eapprox f h z

/-- `signedApprox g k` has the sign of `g` and lies between `0` and `g`. -/
theorem signedApprox_bounds {g : Z → ℝ} (hg : Measurable g) (k : ℕ) (z : Z) :
    (0 ≤ g z → 0 ≤ signedApprox g k z ∧ signedApprox g k z ≤ g z) ∧
      (g z < 0 → g z ≤ signedApprox g k z ∧ signedApprox g k z ≤ 0) := by
  have hgn : Measurable fun z => -g z := hg.neg
  have hp := eapprox_le_self hg.ennreal_ofReal k z
  have hn := eapprox_le_self hgn.ennreal_ofReal k z
  simp only [signedApprox, SimpleFunc.coe_sub, SimpleFunc.coe_map, Pi.sub_apply,
    Function.comp_apply]
  constructor
  · intro h
    have h0 : SimpleFunc.eapprox (fun z => ENNReal.ofReal (-g z)) k z = 0 := by
      have : ENNReal.ofReal (-g z) = 0 := ENNReal.ofReal_eq_zero.2 (by linarith)
      exact le_antisymm (hn.trans this.le) bot_le
    rw [h0, ENNReal.toReal_zero, sub_zero]
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal h hp⟩
  · intro h
    have h0 : SimpleFunc.eapprox (fun z => ENNReal.ofReal (g z)) k z = 0 := by
      have : ENNReal.ofReal (g z) = 0 := ENNReal.ofReal_eq_zero.2 h.le
      exact le_antisymm (hp.trans this.le) bot_le
    rw [h0, ENNReal.toReal_zero, zero_sub]
    set e := (SimpleFunc.eapprox (fun z => ENNReal.ofReal (-g z)) k z).toReal
    have h1 : e ≤ -g z := ENNReal.toReal_le_of_le_ofReal (by linarith) hn
    have h2 : 0 ≤ e := ENNReal.toReal_nonneg
    exact ⟨by linarith, by linarith⟩

/-- `signedApprox g k → g` pointwise. -/
theorem tendsto_signedApprox {g : Z → ℝ} (hg : Measurable g) (z : Z) :
    Tendsto (fun k => signedApprox g k z) atTop (𝓝 (g z)) := by
  have h1 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp
    (tendsto_eapprox_apply hg.ennreal_ofReal z)
  have hgn : Measurable fun z => -g z := hg.neg
  have h2 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp
    (tendsto_eapprox_apply hgn.ennreal_ofReal z)
  have := h1.sub h2
  simp only [ENNReal.toReal_ofReal', max_zero_sub_eq_self] at this
  simpa [signedApprox] using this


/-- If `0 ≤ S ≤ C S^{1/P}` with `1/P + 1/Q = 1`, then `S ≤ C^Q`. -/
theorem le_rpow_of_le_mul_rpow {P Q S C : ℝ} (hPQ : P.HolderConjugate Q) (hS0 : 0 ≤ S)
    (hC : 0 ≤ C) (hb : S ≤ C * S ^ (1 / P)) : S ≤ C ^ Q := by
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have hsplit : S = S ^ (1 / P) * S ^ (1 / Q) := by
      have h11 : 1 / P + 1 / Q = 1 := by rw [one_div, one_div, hPQ.inv_add_inv_eq_one]
      rw [← Real.rpow_add hpos, h11, Real.rpow_one]
    have h1 : S ^ (1 / Q) ≤ C := by
      have hp' : 0 < S ^ (1 / P) := Real.rpow_pos_of_pos hpos _
      nth_rewrite 1 [hsplit] at hb
      rw [mul_comm (S ^ (1 / P)) (S ^ (1 / Q))] at hb
      exact le_of_mul_le_mul_right hb hp'
    calc S = (S ^ (1 / Q)) ^ Q := by
          rw [← Real.rpow_mul hS0, one_div_mul_cancel hPQ.symm.ne_zero, Real.rpow_one]
      _ ≤ C ^ Q := Real.rpow_le_rpow (by positivity) h1 hPQ.symm.nonneg

/-- The density `g` of `A ↦ φ(1_A)` lies in `L_q` with `‖g‖_q ≤ ‖φ‖`. The test functions are
`sgn(sₖ)|sₖ|^{q−1}` for simple `sₖ → g` with the sign of `g` and `|sₖ| ≤ |g|`; then Fatou's
lemma. -/
theorem eLpNorm_dualDensity_le [IsFiniteMeasure μ] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    [p.HolderConjugate q]
    (hp : p ≠ ∞) (hq : q ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    eLpNorm (dualDensity hp φ) q μ ≤ ENNReal.ofReal ‖φ‖ := by
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  set P := p.toReal
  set Q := q.toReal
  set g := dualDensity hp φ with hgdef
  have hgm : Measurable g := SignedMeasure.measurable_rnDeriv _ _
  set s := signedApprox g
  have hsb : ∀ k z, (0 ≤ g z → 0 ≤ s k z ∧ s k z ≤ g z) ∧
      (g z < 0 → g z ≤ s k z ∧ s k z ≤ 0) := signedApprox_bounds hgm
  have hst : ∀ z, Tendsto (fun k => s k z) atTop (𝓝 (g z)) := tendsto_signedApprox hgm
  let F : ℝ → ℝ := fun t => if 0 ≤ t then t ^ (Q - 1) else -((-t) ^ (Q - 1))
  have hQ1 : 0 < Q - 1 := hPQ.symm.sub_one_pos
  have hQP : (Q - 1) * P = Q := hPQ.symm.sub_one_mul_conj
  have hpow : ∀ t : ℝ, 0 ≤ t → t ^ Q = t ^ (Q - 1) * t := fun t ht => by
    conv_lhs => rw [show Q = (Q - 1) + 1 by ring]
    rw [Real.rpow_add' ht (by linarith), Real.rpow_one]
  have hF1 : ∀ t : ℝ, |F t| = |t| ^ (Q - 1) := fun t => by
    simp only [F]
    split_ifs with h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.rpow_nonneg h _)]
    · rw [abs_neg, abs_of_nonneg (Real.rpow_nonneg (by linarith) _), abs_of_neg (not_le.1 h)]
  have hF2 : ∀ k z, |s k z| ^ Q ≤ g z * F (s k z) := fun k z => by
    obtain ⟨hpos, hneg⟩ := hsb k z
    by_cases hg0 : 0 ≤ g z
    · obtain ⟨h1, h2⟩ := hpos hg0
      simp only [F, h1, ↓reduceIte]
      rw [abs_of_nonneg h1, hpow _ h1, mul_comm]
      exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg h1 _)
    · obtain ⟨h1, h2⟩ := hneg (not_le.1 hg0)
      rcases h2.lt_or_eq with h3 | h3
      · simp only [F, not_le.2 h3, ↓reduceIte]
        rw [abs_of_neg h3, hpow _ (by linarith), mul_comm]
        have : 0 ≤ (-(s k z)) ^ (Q - 1) := Real.rpow_nonneg (by linarith) _
        nlinarith
      · rw [h3]
        simp only [F, le_refl, ↓reduceIte, abs_zero]
        rw [Real.zero_rpow (by linarith), Real.zero_rpow hQ1.ne', mul_zero]
  have hi1 : ∀ k, Integrable (fun z => |s k z| ^ Q) μ := fun k =>
    ((s k).map fun t => |t| ^ Q).integrable_of_isFiniteMeasure
  have hS : ∀ k, ∫ z, |s k z| ^ Q ∂μ ≤ ‖φ‖ ^ Q := fun k => by
    set x := (s k).map F
    have hxm := x.memLp_of_isFiniteMeasure p μ
    have hi2 : Integrable (fun z => g z * x z) μ :=
      (integrable_dualDensity hp φ).mul_of_top_left (x.memLp_top μ)
    have h1 : ∫ z, |s k z| ^ Q ∂μ ≤ φ (hxm.toLp x) := by
      rw [dualDensity_simpleFunc]
      exact integral_mono (hi1 k) hi2 fun z => by
        rw [SimpleFunc.map_apply]; exact hF2 k z
    have h2 : ‖hxm.toLp x‖ = (∫ z, |s k z| ^ Q ∂μ) ^ (1 / P) := by
      rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm (ne_zero_of_lt
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p))) hp hxm,
        ENNReal.toReal_ofReal (by positivity), one_div]
      congr 2
      ext z
      rw [SimpleFunc.map_apply, Real.norm_eq_abs, hF1, ← Real.rpow_mul (abs_nonneg _), hQP]
    refine le_rpow_of_le_mul_rpow hPQ (integral_nonneg fun z => by positivity) (norm_nonneg _) ?_
    calc ∫ z, |s k z| ^ Q ∂μ ≤ φ (hxm.toLp x) := h1
      _ ≤ ‖φ‖ * ‖hxm.toLp x‖ := (le_abs_self _).trans (φ.le_opNorm _)
      _ = _ := by rw [h2]
  have hlim : ∀ z, Tendsto (fun k => ENNReal.ofReal (|s k z| ^ Q)) atTop
      (𝓝 (ENNReal.ofReal (|g z| ^ Q))) := fun z =>
    (ENNReal.continuous_ofReal.tendsto _).comp
      (((continuous_abs.tendsto _).comp (hst z)).rpow_const
        (Or.inr hPQ.symm.nonneg))
  have hfat : ∫⁻ z, ENNReal.ofReal (|g z| ^ Q) ∂μ ≤ ENNReal.ofReal (‖φ‖ ^ Q) := by
    calc ∫⁻ z, ENNReal.ofReal (|g z| ^ Q) ∂μ
        = ∫⁻ z, liminf (fun k => ENNReal.ofReal (|s k z| ^ Q)) atTop ∂μ :=
          lintegral_congr fun z => (hlim z).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ z, ENNReal.ofReal (|s k z| ^ Q) ∂μ) atTop :=
          lintegral_liminf_le' fun k =>
            (((s k).map fun t => ENNReal.ofReal (|t| ^ Q)).measurable).aemeasurable
      _ ≤ ENNReal.ofReal (‖φ‖ ^ Q) := by
          refine (liminf_le_liminf (Eventually.of_forall fun k => ?_)).trans
            (liminf_const _).le
          rw [← ofReal_integral_eq_lintegral_ofReal (hi1 k)
            (Eventually.of_forall fun z => by positivity)]
          exact ENNReal.ofReal_le_ofReal (hS k)
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq hgm.aestronglyMeasurable]
  have e : ∀ z, ‖g z‖ₑ ^ Q = ENNReal.ofReal (|g z| ^ Q) := fun z => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hPQ.symm.nonneg]
  change (∫⁻ z, ‖g z‖ₑ ^ Q ∂μ) ^ (1 / Q) ≤ _
  rw [lintegral_congr fun z => e z]
  calc (∫⁻ z, ENNReal.ofReal (|g z| ^ Q) ∂μ) ^ (1 / Q) ≤ ENNReal.ofReal (‖φ‖ ^ Q) ^ (1 / Q) :=
        ENNReal.rpow_le_rpow hfat (by positivity)
    _ = ENNReal.ofReal ‖φ‖ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hPQ.symm.ne_zero, Real.rpow_one]


variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The pairing `(y, x) ↦ ∫ y x dμ` of `L_q` with `L_p` (Mathlib's `lpPairing`). -/
noncomputable def pairLqLp (μ : Measure Z) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] : Lp ℝ q μ →L[ℝ] Lp ℝ p μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p

/-- `pairLqLp μ p q y x = ∫ y x dμ`. -/
theorem pairLqLp_apply (y : Lp ℝ q μ) (x : Lp ℝ p μ) :
    pairLqLp μ p q y x = ∫ z, y z * x z ∂μ := by
  rw [pairLqLp, ContinuousLinearMap.lpPairing_eq_integral]; rfl

/-- Hölder's inequality: `|∫ y x dμ| ≤ ‖y‖_q ‖x‖_p`. -/
theorem abs_pairLqLp_le (y : Lp ℝ q μ) (x : Lp ℝ p μ) : |pairLqLp μ p q y x| ≤ ‖y‖ * ‖x‖ := by
  have h1 : pairLqLp μ p q y x = L1.integral ((ContinuousLinearMap.mul ℝ ℝ).holder 1 y x) := by
    rw [pairLqLp_apply, L1.integral_eq_integral]
    exact integral_congr_ae ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder y x).symm
  rw [h1, ← Real.norm_eq_abs]
  refine (L1.norm_integral_le _).trans ?_
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le y x).trans ?_
  have := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖y‖ * ‖x‖ ≤ 1 * ‖y‖ * ‖x‖ := by gcongr
    _ = ‖y‖ * ‖x‖ := by rw [one_mul]

/-- `∫ y (c 1_A) dμ = (∫_A y dμ) c`. -/
theorem pairLqLp_indicator (y : Lp ℝ q μ) {A : Set Z} (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    (c : ℝ) : pairLqLp μ p q y (indicatorConstLp p hA hμA c) = (∫ z in A, y z ∂μ) * c := by
  rw [pairLqLp_apply, ← integral_mul_const, ← integral_indicator hA]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hA) (hμs := hμA) (c := c)] with z hz
  rw [hz]
  by_cases h : z ∈ A <;> simp [h]

/-- For a σ-finite measure, `y ↦ (x ↦ ∫ y x dμ)` is injective from `L_q` to `L_p*`. -/
theorem pairLqLp_injective [SigmaFinite μ] : Function.Injective (pairLqLp μ p q) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  have hint : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (fun z => y z) s μ :=
    fun s hs hμs => by
      have : Fact (μ s < ∞) := ⟨hμs⟩
      have hm : MemLp (fun z => y z) q (μ.restrict s) := (Lp.memLp y).restrict s
      exact hm.integrable Fact.out
  have h0 := ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hint fun s hs hμs => by
    have := pairLqLp_indicator (p := p) y hs hμs.ne 1
    rw [hy, mul_one] at this
    exact this.symm
  exact (Lp.eq_zero_iff_ae_eq_zero).2 h0

/-- For a finite measure and `1 < p < ∞`, every `φ ∈ L_p*` is `x ↦ ∫ y x dμ` for some
`y ∈ L_q` with `‖y‖_q ≤ ‖φ‖`; `y` is the Radon–Nikodym density of `A ↦ φ(1_A)`. -/
theorem exists_preimage_pairLqLp [IsFiniteMeasure μ] (hp : p ≠ ∞) (hq : q ≠ ∞)
    (φ : StrongDual ℝ (Lp ℝ p μ)) :
    ∃ y : Lp ℝ q μ, pairLqLp μ p q y = φ ∧ ‖y‖ ≤ ‖φ‖ := by
  have hb := eLpNorm_dualDensity_le hp hq φ
  have hm : MemLp (dualDensity hp φ) q μ := memLp_iff.2 (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
  refine ⟨hm.toLp _, ?_, ?_⟩
  · refine (Lp.induction (p := p) hp (fun x => pairLqLp μ p q (hm.toLp _) x = φ x) ?_ ?_
      (isClosed_eq (pairLqLp μ p q (hm.toLp _)).continuous φ.continuous) ·) |>
      ContinuousLinearMap.ext
    · intro c s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst, pairLqLp_indicator, indicatorConstLp_eq_smul,
        map_smul, smul_eq_mul, ← setIntegral_dualDensity hp φ hs, mul_comm]
      congr 1
      exact setIntegral_congr_ae hs (by
        filter_upwards [hm.coeFn_toLp] with z hz _ using hz)
    · intro f f' hf hf' _ h1 h2
      simp only [map_add, h1, h2]
  · rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) hb

/-- For a finite measure and `1 < p < ∞`, `y ↦ (x ↦ ∫ y x dμ)` preserves norms. -/
theorem norm_pairLqLp [IsFiniteMeasure μ] (hp : p ≠ ∞) (hq : q ≠ ∞) (y : Lp ℝ q μ) :
    ‖pairLqLp μ p q y‖ = ‖y‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
      rw [Real.norm_eq_abs]; exact abs_pairLqLp_le y x
  · obtain ⟨y', hy', hn⟩ := exists_preimage_pairLqLp hp hq (pairLqLp μ p q y)
    calc ‖y‖ = ‖y'‖ := by rw [pairLqLp_injective hy']
      _ ≤ ‖pairLqLp μ p q y‖ := hn

/-- `L_p* = L_q` for a finite measure and conjugate `1 < p, q < ∞`. -/
noncomputable def dualLp [IsFiniteMeasure μ] (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ) :=
  LinearIsometryEquiv.ofSurjective ⟨(pairLqLp μ p q).toLinearMap, norm_pairLqLp hp hq⟩
    fun φ => (exists_preimage_pairLqLp hp hq φ).imp fun _ h => h.1

/-- **Example 4** (pp. 449–450): for a finite measure and `1 < p < ∞` with `1/p + 1/q = 1`, the
dual of `L_p(Z, 𝒵, μ)` is `L_q(Z, 𝒵, μ)`. Each `y ∈ L_q` gives `x ↦ ∫ y x dμ` in `L_p*`,
every element of `L_p*` arises from exactly one `y`, and norms are preserved. -/
theorem example_15_4 [IsFiniteMeasure μ] (hp : p ≠ ∞) (hq : q ≠ ∞) :
    ∃ e : Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ), ∀ y x, e y x = ∫ z, y z * x z ∂μ :=
  ⟨dualLp hp hq, fun y x => pairLqLp_apply y x⟩

end StokeyLucasPrescott.ParetoOptimaEquilibria

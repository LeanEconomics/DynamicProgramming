/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.DualLp

/-!
# The dual of `L_p` for `1 < p < ∞` on σ-finite and arbitrary measure spaces

SLP §15.1, Example 4, pp. 449–450: for `1 < p < ∞` and `1/p + 1/q = 1` the dual of
`L_p(Z, 𝒵, μ)` is `L_q(Z, 𝒵, μ)`. `DualLp` proves this for finite `μ` (`example_15_4`). Here it
is proved for σ-finite `μ`, and then for every measure `μ`, which is the book's claim in full for
`1 < p < ∞`. (For `p = 1` the claim needs σ-finiteness: `l1_dual_counterexample`.)

* **Example 4, σ-finite** (`example_15_4_sigmaFinite`): `y ↦ (x ↦ ∫ y x dμ)` is an isometric
  isomorphism from `L_q` onto `L_p*` (`dualLpSigmaFinite`).
* **Example 4, any measure** (`example_15_4_general`): the same with no finiteness or
  σ-finiteness assumption (`dualLpOfNeTop`).
* `norm_pairLqLp_eq`, `pairLqLp_injective_of_ne_top`: for every `μ`, `y ↦ (x ↦ ∫ y x dμ)`
  preserves norms and is injective.

Proof.
* `isDualRep_of_weight`: let `w ≥ 0` be integrable and vanish exactly off `S`. The measure `w μ`
  is finite, and `x ↦ w^{1/p} x` is an isometry of `L_p(w μ)` into `L_p(μ)`
  (`eLpNorm_rpow_mul`). `example_15_4`'s `exists_preimage_pairLqLp` represents
  `x ↦ φ(w^{1/p} x)` by some `g ∈ L_q(w μ)`, and `y = w^{1/q} g` represents `φ` on functions
  vanishing off `S` (`IsDualRep`).
* σ-finite `μ`: take `w > 0` everywhere (`exists_pos_lintegral_lt_of_sigmaFinite`), `S = Z`.
* The test function `sgn(y)|y|^{q−1}` (`testFn`) gives `∫ |y|^q ≤ ‖φ‖^q` for every
  representing `y` (`IsDualRep.integral_le`), hence the norm identity, and uniqueness of the
  representation on each `S` (`IsDualRep.ae_eq`).
* Any `μ` (`exists_preimage_pairLqLp_of_ne_top`): each `u ∈ L_p` vanishes off a set on which `μ`
  is σ-finite (`exists_sigmaFinite_support`), and on each such set `S` there is a
  representation `y_S` (`exists_isDualRep`). Take a countable union `S*` of such sets along
  which `∫ |y_S|^q` tends to its supremum (`sigmaFinite_restrict_iUnion`). For `u ∈ L_p` with
  σ-finite support `t`, the representation on `S* ∪ t` restricts to `y_{S*}` on `S*`
  (`IsDualRep.indicator`, `IsDualRep.ae_eq`), and maximality forces it to vanish off `S*`, so
  `φ(u) = ∫ y_{S*} u dμ`.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Metric Set MeasureTheory Function
open scoped ENNReal NNReal

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-- Weighting by `w ^ a`, `a ≠ 0`, turns `μ.withDensity w`-a.e. equality into `μ`-a.e.
equality. -/
theorem ae_eq_rpow_mul_of_withDensity {w : Z → ℝ≥0} (hw : Measurable w) {a : ℝ} (ha : a ≠ 0)
    {f f' : Z → ℝ} (h : f =ᵐ[μ.withDensity fun z => (w z : ℝ≥0∞)] f') :
    (fun z => ((w z ^ a : ℝ≥0) : ℝ) * f z) =ᵐ[μ] fun z => ((w z ^ a : ℝ≥0) : ℝ) * f' z := by
  have h' := (ae_withDensity_iff hw.coe_nnreal_ennreal).1 h
  filter_upwards [h'] with z hz
  by_cases h0 : w z = 0
  · simp [h0, NNReal.zero_rpow ha]
  · rw [hz (by simpa using h0)]

/-- `‖w^{1/r} f‖_{L_r(μ)} = ‖f‖_{L_r(w μ)}`. -/
theorem eLpNorm_rpow_mul {w : Z → ℝ≥0} (hw : Measurable w) {r : ℝ≥0∞} (hr0 : r ≠ 0)
    (hrt : r ≠ ∞) {f : Z → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun z => ((w z ^ (1 / r.toReal) : ℝ≥0) : ℝ) * f z) r μ =
      eLpNorm f r (μ.withDensity fun z => (w z : ℝ≥0∞)) := by
  have hR : 0 < r.toReal := ENNReal.toReal_pos hr0 hrt
  have hwm : Measurable fun z => ((w z ^ (1 / r.toReal) : ℝ≥0) : ℝ) :=
    (hw.pow_const _).coe_nnreal_real
  have hm : AEStronglyMeasurable (fun z => ((w z ^ (1 / r.toReal) : ℝ≥0) : ℝ) * f z) μ :=
    hwm.aestronglyMeasurable.mul hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrt hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrt
      (hf.mono_ac (withDensity_absolutelyContinuous _ _)),
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hw.coe_nnreal_ennreal
      (ae_of_all _ fun z => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply]
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hR.le]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, NNReal.abs_eq, ENNReal.ofReal_coe_nnreal,
    ← ENNReal.coe_rpow_of_nonneg _ hR.le, ← NNReal.rpow_mul, one_div_mul_cancel hR.ne',
    NNReal.rpow_one]

/-- `w^a w^{-a} t = t` where `w ≠ 0`, and `= 0` where `w = 0`. -/
theorem rpow_mul_rpow_neg_mul (x : ℝ≥0) {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    ((x ^ a : ℝ≥0) : ℝ) * (((x ^ (-a) : ℝ≥0) : ℝ) * t) = if x = 0 then 0 else t := by
  by_cases h0 : x = 0
  · simp [h0, NNReal.zero_rpow ha]
  · rw [← mul_assoc, ← NNReal.coe_mul, NNReal.rpow_neg, mul_inv_cancel₀ (by positivity)]
    simp [h0]

/-- If `f ∈ L_r(w μ)`, then `w^{1/r} f ∈ L_r(μ)`. -/
theorem memLp_rpow_mul {w : Z → ℝ≥0} (hw : Measurable w) {r : ℝ≥0∞} (hr0 : r ≠ 0)
    (hrt : r ≠ ∞) {f : Z → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfm : MemLp f r (μ.withDensity fun z => (w z : ℝ≥0∞))) :
    MemLp (fun z => ((w z ^ (1 / r.toReal) : ℝ≥0) : ℝ) * f z) r μ :=
  by rw [memLp_iff, eLpNorm_rpow_mul hw hr0 hrt hf]; exact hfm

/-- If `u ∈ L_r(μ)`, then `w^{-1/r} u ∈ L_r(w μ)`. -/
theorem memLp_rpow_neg_mul {w : Z → ℝ≥0} (hw : Measurable w) {r : ℝ≥0∞} (hr0 : r ≠ 0)
    (hrt : r ≠ ∞) {u : Z → ℝ} (hu : MemLp u r μ) :
    MemLp (fun z => ((w z ^ (-(1 / r.toReal)) : ℝ≥0) : ℝ) * u z) r
      (μ.withDensity fun z => (w z : ℝ≥0∞)) := by
  have hR : 0 < r.toReal := ENNReal.toReal_pos hr0 hrt
  have hm : AEStronglyMeasurable (fun z => ((w z ^ (-(1 / r.toReal)) : ℝ≥0) : ℝ) * u z) μ :=
    (hw.pow_const _).coe_nnreal_real.aestronglyMeasurable.mul hu.aestronglyMeasurable
  rw [memLp_iff, ← eLpNorm_rpow_mul hw hr0 hrt hm]
  refine lt_of_le_of_lt (eLpNorm_mono
    ((hw.pow_const _).coe_nnreal_real.aestronglyMeasurable.mul hm) fun z => ?_) hu
  rw [rpow_mul_rpow_neg_mul _ (by positivity)]
  split_ifs <;> simp

/-- `y` represents `φ ∈ L_p*` on the set `S`: `y ∈ L_r` vanishes off `S`, and
`φ(u) = ∫ y u dμ` for every `u ∈ L_p` vanishing a.e. off `S`. -/
def IsDualRep {p : ℝ≥0∞} [Fact (1 ≤ p)] (φ : StrongDual ℝ (Lp ℝ p μ)) (r : ℝ≥0∞) (S : Set Z)
    (y : Z → ℝ) : Prop :=
  MemLp y r μ ∧ (∀ z, z ∉ S → y z = 0) ∧
    ∀ u : Lp ℝ p μ, (∀ᵐ z ∂μ, z ∉ S → u z = 0) → φ u = ∫ z, y z * u z ∂μ

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The representation on a weight's support: if `w ≥ 0` is integrable and vanishes exactly off
`S`, then every `φ ∈ L_p*` is represented on `S` by some `y`. Apply `exists_preimage_pairLqLp`
to the finite measure `w μ` and the functional `x ↦ φ(w^{1/p} x)`, which gives `g ∈ L_q(w μ)`;
then `y = w^{1/q} g`. -/
theorem isDualRep_of_weight (hp : p ≠ ∞) (hq : q ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ))
    {S : Set Z} {w : Z → ℝ≥0} (hw : Measurable w) (hwi : ∫⁻ z, (w z : ℝ≥0∞) ∂μ ≠ ∞)
    (hwS : ∀ z, w z = 0 ↔ z ∉ S) : ∃ y, IsDualRep φ q S y := by
  set ν := μ.withDensity fun z => (w z : ℝ≥0∞) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hwi
  have hp0 : p ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hP1 : 1 / p.toReal ≠ 0 := one_div_ne_zero hP.ne'
  have hT : ∀ x : Lp ℝ p ν, MemLp (fun z => ((w z ^ (1 / p.toReal) : ℝ≥0) : ℝ) * x z) p μ :=
    fun x => memLp_rpow_mul hw hp0 hp (Lp.stronglyMeasurable x).aestronglyMeasurable (Lp.memLp x)
  let T : Lp ℝ p ν →ₗ[ℝ] Lp ℝ p μ :=
    { toFun := fun x => (hT x).toLp _
      map_add' := fun x x' => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [ae_eq_rpow_mul_of_withDensity hw hP1 (Lp.coeFn_add x x')] with z hz
        simp only [Pi.add_apply] at hz ⊢
        rw [hz, mul_add]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [ae_eq_rpow_mul_of_withDensity hw hP1 (Lp.coeFn_smul c x)] with z hz
        simp only [Pi.smul_apply, smul_eq_mul] at hz ⊢
        rw [hz]; ring }
  have hTn : ∀ x, ‖T x‖ = ‖x‖ := fun x => by
    change ‖(hT x).toLp _‖ = ‖x‖
    rw [Lp.norm_toLp, Lp.norm_def,
      eLpNorm_rpow_mul hw hp0 hp (Lp.stronglyMeasurable x).aestronglyMeasurable]
  let ψ : StrongDual ℝ (Lp ℝ p ν) := (φ.toLinearMap.comp T).mkContinuous ‖φ‖ fun x => by
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [← hTn x]; exact φ.le_opNorm _
  obtain ⟨g, hg, -⟩ := exists_preimage_pairLqLp (μ := ν) hp hq ψ
  refine ⟨fun z => ((w z ^ (1 / q.toReal) : ℝ≥0) : ℝ) * g z,
    memLp_rpow_mul hw hq0 hq (Lp.stronglyMeasurable g).aestronglyMeasurable (Lp.memLp g),
    fun z hz => by simp [(hwS z).2 hz, NNReal.zero_rpow (inv_ne_zero hQ.ne')],
    fun u hu => ?_⟩
  set v := fun z => ((w z ^ (-(1 / p.toReal)) : ℝ≥0) : ℝ) * u z with hvdef
  have hv : MemLp v p ν := memLp_rpow_neg_mul hw hp0 hp (Lp.memLp u)
  have hTv : T (hv.toLp v) = u := by
    change (hT _).toLp _ = u
    conv_rhs => rw [← Lp.toLp_coeFn u (Lp.memLp u)]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [ae_eq_rpow_mul_of_withDensity hw hP1 hv.coeFn_toLp, hu] with z h1 h2
    rw [h1, hvdef]
    dsimp only
    rw [rpow_mul_rpow_neg_mul _ hP1]
    split_ifs with h0
    · exact (h2 ((hwS z).1 h0)).symm
    · rfl
  have key : ∀ z, w z • (g z * v z) =
      ((w z ^ (1 / q.toReal) : ℝ≥0) : ℝ) * g z * u z := fun z => by
    rw [hvdef, NNReal.smul_def, smul_eq_mul]
    by_cases h0 : w z = 0
    · simp [h0, NNReal.zero_rpow (inv_ne_zero hQ.ne')]
    · have e : (w z : ℝ) * ((w z ^ (-(1 / p.toReal)) : ℝ≥0) : ℝ) =
          ((w z ^ (1 / q.toReal) : ℝ≥0) : ℝ) := by
        rw [← NNReal.coe_mul]
        congr 1
        have h1 : w z * w z ^ (-(1 / p.toReal)) = w z ^ (1 + -(1 / p.toReal)) := by
          rw [NNReal.rpow_add h0, NNReal.rpow_one]
        rw [h1]
        congr 1
        have := hPQ.inv_add_inv_eq_one
        rw [one_div, one_div]
        linarith
      calc (w z : ℝ) * (g z * (((w z ^ (-(1 / p.toReal)) : ℝ≥0) : ℝ) * u z)) =
          ((w z : ℝ) * ((w z ^ (-(1 / p.toReal)) : ℝ≥0) : ℝ)) * g z * u z := by ring
        _ = _ := by rw [e]
  calc φ u = ψ (hv.toLp v) := by rw [← hTv]; rfl
    _ = ∫ z, g z * (hv.toLp v) z ∂ν := by rw [← hg, pairLqLp_apply]
    _ = ∫ z, g z * v z ∂ν :=
        integral_congr_ae (by filter_upwards [hv.coeFn_toLp] with z hz; rw [hz])
    _ = ∫ z, w z • (g z * v z) ∂μ := integral_withDensity_eq_integral_smul hw _
    _ = _ := integral_congr_ae (ae_of_all _ fun z => key z)

/-- The test function `t ↦ t |t|^{Q−2}`, that is `sgn(t) |t|^{Q−1}`. -/
noncomputable def testFn (Q t : ℝ) : ℝ := t * |t| ^ (Q - 2)

/-- `t · testFn Q t = |t|^Q`. -/
theorem mul_testFn {Q : ℝ} (hQ : 0 < Q) (t : ℝ) : t * testFn Q t = |t| ^ Q := by
  unfold testFn
  by_cases h : t = 0
  · simp [h, Real.zero_rpow hQ.ne']
  · have ha : 0 < |t| := abs_pos.2 h
    rw [← mul_assoc, ← abs_mul_abs_self t]
    calc |t| * |t| * |t| ^ (Q - 2) = |t| ^ ((1 : ℝ) + 1 + (Q - 2)) := by
          rw [Real.rpow_add ha, Real.rpow_add ha, Real.rpow_one]
      _ = |t| ^ Q := by ring_nf

/-- `|testFn Q t| = |t|^{Q−1}` for `Q > 1`. -/
theorem abs_testFn {Q : ℝ} (hQ : 1 < Q) (t : ℝ) : |testFn Q t| = |t| ^ (Q - 1) := by
  unfold testFn
  by_cases h : t = 0
  · simp [h, Real.zero_rpow (by linarith : Q - 1 ≠ 0)]
  · have ha : 0 < |t| := abs_pos.2 h
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
    calc |t| * |t| ^ (Q - 2) = |t| ^ ((1 : ℝ) + (Q - 2)) := by
          rw [Real.rpow_add ha, Real.rpow_one]
      _ = |t| ^ (Q - 1) := by ring_nf

/-- `testFn Q` is measurable. -/
theorem measurable_testFn (Q : ℝ) : Measurable (testFn Q) :=
  measurable_id.mul (continuous_abs.measurable.pow_const _)

/-- For `d ∈ L_q`, the test function `sgn(d) |d|^{q−1}` lies in `L_p`. -/
theorem memLp_testFn (hp : p ≠ ∞) (hq : q ≠ ∞) {d : Z → ℝ} (hd : MemLp d q μ) :
    MemLp (fun z => testFn q.toReal (d z)) p μ := by
  have hp0 : p ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hm : AEStronglyMeasurable (fun z => testFn q.toReal (d z)) μ :=
    ((measurable_testFn _).comp_aemeasurable
      hd.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hm hp0 hp]
  refine ((integrable_norm_rpow_iff hd.aestronglyMeasurable hq0 hq).2 hd).congr
    (ae_of_all _ fun z => ?_)
  dsimp only
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_testFn (by linarith [hPQ.symm.sub_one_pos]),
    ← Real.rpow_mul (abs_nonneg _), hPQ.symm.sub_one_mul_conj]

/-- `‖sgn(d)|d|^{q−1}‖_p = (∫ |d|^q)^{1/p}`. -/
theorem norm_toLp_testFn (hp : p ≠ ∞) (hq : q ≠ ∞) {d : Z → ℝ} (hd : MemLp d q μ) :
    ‖(memLp_testFn hp hq hd).toLp _‖ = (∫ z, ‖d z‖ ^ q.toReal ∂μ) ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm hp0 hp (memLp_testFn hp hq hd),
    ENNReal.toReal_ofReal (by positivity), one_div]
  congr 2
  ext z
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_testFn (by linarith [hPQ.symm.sub_one_pos]),
    ← Real.rpow_mul (abs_nonneg _), hPQ.symm.sub_one_mul_conj]

/-- A representing function has `∫ |y|^q ≤ ‖φ‖^q`: test `φ` with `sgn(y)|y|^{q−1}`. -/
theorem IsDualRep.integral_le (hp : p ≠ ∞) (hq : q ≠ ∞) {φ : StrongDual ℝ (Lp ℝ p μ)}
    {S : Set Z} {y : Z → ℝ} (h : IsDualRep φ q S y) :
    ∫ z, ‖y z‖ ^ q.toReal ∂μ ≤ ‖φ‖ ^ q.toReal := by
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  set u := (memLp_testFn hp hq h.1).toLp _
  have hu : ∀ᵐ z ∂μ, z ∉ S → u z = 0 := by
    filter_upwards [MemLp.coeFn_toLp (memLp_testFn hp hq h.1)] with z hz hzS
    rw [hz, h.2.1 z hzS]
    simp [testFn]
  have h1 : φ u = ∫ z, ‖y z‖ ^ q.toReal ∂μ := by
    rw [h.2.2 u hu]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_testFn hp hq h.1)] with z hz
    rw [hz, mul_testFn hQ, Real.norm_eq_abs]
  refine le_rpow_of_le_mul_rpow hPQ (integral_nonneg fun z => by positivity) (norm_nonneg _) ?_
  calc ∫ z, ‖y z‖ ^ q.toReal ∂μ = φ u := h1.symm
    _ ≤ ‖φ‖ * ‖u‖ := (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact φ.le_opNorm u)
    _ = _ := by rw [norm_toLp_testFn hp hq h.1]

/-- A representing function has `‖y‖_q ≤ ‖φ‖`. -/
theorem IsDualRep.eLpNorm_le (hp : p ≠ ∞) (hq : q ≠ ∞) {φ : StrongDual ℝ (Lp ℝ p μ)}
    {S : Set Z} {y : Z → ℝ} (h : IsDualRep φ q S y) :
    eLpNorm y q μ ≤ ENNReal.ofReal ‖φ‖ := by
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [MemLp.eLpNorm_eq_integral_rpow_norm hq0 hq h.1]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∫ z, ‖y z‖ ^ q.toReal ∂μ) ^ q.toReal⁻¹ ≤ (‖φ‖ ^ q.toReal) ^ q.toReal⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun z => by positivity) (h.integral_le hp hq)
          (inv_nonneg.2 hQ.le)
    _ = ‖φ‖ := by rw [← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hQ.ne', Real.rpow_one]

/-- For every measure and `1 < p < ∞`, `y ↦ (x ↦ ∫ y x dμ)` preserves norms. -/
theorem norm_pairLqLp_eq (hp : p ≠ ∞) (hq : q ≠ ∞) (y : Lp ℝ q μ) :
    ‖pairLqLp μ p q y‖ = ‖y‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    rw [Real.norm_eq_abs]; exact abs_pairLqLp_le y x) ?_
  have h : IsDualRep (pairLqLp μ p q y) q univ y :=
    ⟨Lp.memLp y, fun z hz => absurd (mem_univ z) hz, fun u _ => pairLqLp_apply y u⟩
  rw [Lp.norm_def]
  exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (h.eLpNorm_le hp hq)

/-- For every measure and `1 < p < ∞`, `y ↦ (x ↦ ∫ y x dμ)` is injective. -/
theorem pairLqLp_injective_of_ne_top (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Function.Injective (pairLqLp μ p q) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  have h := norm_pairLqLp_eq hp hq y
  rw [hy, norm_zero] at h
  exact norm_eq_zero.1 h.symm

/-- For a σ-finite measure and `1 < p < ∞`, every `φ ∈ L_p*` is `x ↦ ∫ y x dμ` for some
`y ∈ L_q`. The weight is a positive integrable `w` (`exists_pos_lintegral_lt_of_sigmaFinite`). -/
theorem exists_preimage_pairLqLp_sigmaFinite [SigmaFinite μ] (hp : p ≠ ∞) (hq : q ≠ ∞)
    (φ : StrongDual ℝ (Lp ℝ p μ)) : ∃ y : Lp ℝ q μ, pairLqLp μ p q y = φ := by
  obtain ⟨w, hpos, hwm, hwi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  obtain ⟨y, hy⟩ := isDualRep_of_weight (S := univ) hp hq φ hwm (ne_top_of_lt hwi)
    fun z => by simp [(hpos z).ne']
  refine ⟨hy.1.toLp y, ContinuousLinearMap.ext fun u => ?_⟩
  rw [pairLqLp_apply, hy.2.2 u (ae_of_all _ fun z hz => absurd (mem_univ z) hz)]
  exact integral_congr_ae (by filter_upwards [hy.1.coeFn_toLp] with z hz; rw [hz])

/-- `L_p* = L_q` for a σ-finite measure and conjugate `1 < p, q < ∞`. -/
noncomputable def dualLpSigmaFinite [SigmaFinite μ] (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ) :=
  LinearIsometryEquiv.ofSurjective ⟨(pairLqLp μ p q).toLinearMap, norm_pairLqLp_eq hp hq⟩
    (exists_preimage_pairLqLp_sigmaFinite hp hq)

/-- **Example 4** (pp. 449–450) for σ-finite measures: for `1 < p < ∞` with `1/p + 1/q = 1`, the
dual of `L_p(Z, 𝒵, μ)` is `L_q(Z, 𝒵, μ)`. Each `y ∈ L_q` gives `x ↦ ∫ y x dμ` in `L_p*`,
every element of `L_p*` arises from exactly one `y`, and norms are preserved. -/
theorem example_15_4_sigmaFinite [SigmaFinite μ] (hp : p ≠ ∞) (hq : q ≠ ∞) :
    ∃ e : Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ), ∀ y x, e y x = ∫ z, y z * x z ∂μ :=
  ⟨dualLpSigmaFinite hp hq, fun y x => pairLqLp_apply y x⟩

/-- Two functions representing `φ` on the same set agree a.e.: test the difference `d` with
`sgn(d)|d|^{q−1}`. -/
theorem IsDualRep.ae_eq (hp : p ≠ ∞) (hq : q ≠ ∞) {φ : StrongDual ℝ (Lp ℝ p μ)} {S : Set Z}
    {y y' : Z → ℝ} (h : IsDualRep φ q S y) (h' : IsDualRep φ q S y') : y =ᵐ[μ] y' := by
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  set d := y - y' with hd_def
  have hd : MemLp d q μ := h.1.sub h'.1
  set u := (memLp_testFn hp hq hd).toLp _
  have hu : ∀ᵐ z ∂μ, z ∉ S → u z = 0 := by
    filter_upwards [MemLp.coeFn_toLp (memLp_testFn hp hq hd)] with z hz hzS
    rw [hz, hd_def, Pi.sub_apply, h.2.1 z hzS, h'.2.1 z hzS]
    simp [testFn]
  have i1 : Integrable (fun z => y z * u z) μ := h.1.integrable_mul (Lp.memLp u)
  have i2 : Integrable (fun z => y' z * u z) μ := h'.1.integrable_mul (Lp.memLp u)
  have e : ∫ z, d z * u z ∂μ = 0 := by
    have : ∫ z, d z * u z ∂μ = ∫ z, y z * u z ∂μ - ∫ z, y' z * u z ∂μ := by
      rw [← integral_sub i1 i2]
      congr 1
      ext z
      rw [hd_def, Pi.sub_apply, sub_mul]
    rw [this, ← h.2.2 u hu, ← h'.2.2 u hu, sub_self]
  have e2 : ∫ z, ‖d z‖ ^ q.toReal ∂μ = 0 := by
    rw [← e]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_testFn hp hq hd)] with z hz
    rw [hz, mul_testFn hQ, Real.norm_eq_abs]
  have hi : Integrable (fun z => ‖d z‖ ^ q.toReal) μ :=
    (integrable_norm_rpow_iff hd.aestronglyMeasurable hq0 hq).2 hd
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun z => by positivity) hi).1 e2] with z hz
  have h0 : ‖d z‖ ^ q.toReal = 0 := hz
  rw [Real.rpow_eq_zero (norm_nonneg _) hQ.ne', norm_eq_zero, hd_def, Pi.sub_apply,
    sub_eq_zero] at h0
  exact h0

omit [Fact (1 ≤ q)] [p.HolderConjugate q] in
/-- A representation on `S'` restricts to one on a measurable `S ⊆ S'`. -/
theorem IsDualRep.indicator {φ : StrongDual ℝ (Lp ℝ p μ)} {S S' : Set Z} {y : Z → ℝ}
    (hS : MeasurableSet S) (hSS : S ⊆ S') (h : IsDualRep φ q S' y) :
    IsDualRep φ q S (S.indicator y) := by
  refine ⟨h.1.indicator hS, fun z hz => indicator_of_notMem hz _, fun u hu => ?_⟩
  rw [h.2.2 u (by filter_upwards [hu] with z hz hz' using hz fun h => hz' (hSS h))]
  refine integral_congr_ae ?_
  filter_upwards [hu] with z hz
  by_cases hzS : z ∈ S
  · rw [indicator_of_mem hzS]
  · rw [indicator_of_notMem hzS, hz hzS, mul_zero, mul_zero]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] in
/-- A countable union of sets on which `μ` is σ-finite is one too. -/
theorem sigmaFinite_restrict_iUnion {S : ℕ → Set Z} (hS : ∀ n, MeasurableSet (S n))
    (hσ : ∀ n, SigmaFinite (μ.restrict (S n))) : SigmaFinite (μ.restrict (⋃ n, S n)) := by
  set U := ⋃ n, S n
  refine Measure.sigmaFinite_of_countable (S := range (fun nk : ℕ × ℕ =>
      spanningSets (μ.restrict (S nk.1)) nk.2 ∩ S nk.1) ∪ {Uᶜ})
    ((countable_range _).union (countable_singleton _)) ?_ ?_
  · rintro s (⟨⟨n, k⟩, rfl⟩ | hs)
    · calc μ.restrict U (spanningSets (μ.restrict (S n)) k ∩ S n)
          ≤ μ (spanningSets (μ.restrict (S n)) k ∩ S n) := Measure.restrict_le_self _
        _ = μ.restrict (S n) (spanningSets (μ.restrict (S n)) k) :=
          (Measure.restrict_apply (measurableSet_spanningSets _ _)).symm
        _ < ∞ := measure_spanningSets_lt_top _ _
    · rw [mem_singleton_iff.1 hs, Measure.restrict_apply (MeasurableSet.iUnion hS).compl,
        compl_inter_self, measure_empty]
      exact ENNReal.zero_lt_top
  · refine eq_univ_of_forall fun z => ?_
    by_cases hz : z ∈ U
    · obtain ⟨n, hn⟩ := mem_iUnion.1 hz
      have hz' : z ∈ ⋃ k, spanningSets (μ.restrict (S n)) k := by
        rw [iUnion_spanningSets]; exact mem_univ z
      obtain ⟨k, hk⟩ := mem_iUnion.1 hz'
      exact mem_sUnion.2 ⟨_, Or.inl ⟨(n, k), rfl⟩, hk, hn⟩
    · exact mem_sUnion.2 ⟨Uᶜ, Or.inr rfl, hz⟩

/-- Every `φ ∈ L_p*` is represented on each measurable `S` on which `μ` is σ-finite. The weight
is `1_S g` for a positive `g` with `∫_S g < ∞`. -/
theorem exists_isDualRep (hp : p ≠ ∞) (hq : q ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) {S : Set Z}
    (hS : MeasurableSet S) [SigmaFinite (μ.restrict S)] : ∃ y, IsDualRep φ q S y := by
  obtain ⟨g, hpos, hgm, hgi⟩ := exists_pos_lintegral_lt_of_sigmaFinite (μ.restrict S) one_ne_zero
  refine isDualRep_of_weight hp hq φ (w := S.indicator g) (hgm.indicator hS) ?_ fun z => ?_
  · have e : ∀ z, ((S.indicator g z : ℝ≥0) : ℝ≥0∞) = S.indicator (fun z => (g z : ℝ≥0∞)) z :=
      fun z => by by_cases hz : z ∈ S <;> simp [hz]
    rw [lintegral_congr e, lintegral_indicator hS]
    exact ne_top_of_lt hgi
  · by_cases hz : z ∈ S <;> simp [hz, (hpos z).ne']

omit [Fact (1 ≤ q)] [p.HolderConjugate q] in
/-- Every `u ∈ L_p`, `p < ∞`, vanishes a.e. off a measurable set on which `μ` is σ-finite. -/
theorem exists_sigmaFinite_support (hp : p ≠ ∞) (u : Lp ℝ p μ) :
    ∃ t, MeasurableSet t ∧ SigmaFinite (μ.restrict t) ∧ ∀ᵐ z ∂μ, z ∉ t → u z = 0 := by
  have hp0 : p ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p))
  obtain ⟨t, ht, hu, hσ⟩ := ((Lp.memLp u).aefinStronglyMeasurable hp0 hp).exists_set_sigmaFinite
  exact ⟨t, ht, hσ, by
    filter_upwards [(ae_restrict_iff' ht.compl).1 hu] with z hz hzt using by simpa using hz hzt⟩

/-- For every measure and `1 < p < ∞`, every `φ ∈ L_p*` is `x ↦ ∫ y x dμ` for some `y ∈ L_q`.
Among the representations `y_S` on σ-finite sets `S`, take `S*` (a countable union) with
`∫ |y_{S*}|^q` maximal. For `u ∈ L_p`, enlarge `S*` by the σ-finite support of `u`: maximality
forces the new representation to vanish off `S*`, so it equals `y_{S*}`. -/
theorem exists_preimage_pairLqLp_of_ne_top (hp : p ≠ ∞) (hq : q ≠ ∞)
    (φ : StrongDual ℝ (Lp ℝ p μ)) : ∃ y : Lp ℝ q μ, pairLqLp μ p q y = φ := by
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  set A : Set ℝ := {r | ∃ S : Set Z, ∃ y : Z → ℝ, MeasurableSet S ∧ SigmaFinite (μ.restrict S) ∧
    IsDualRep φ q S y ∧ r = ∫ z, ‖y z‖ ^ q.toReal ∂μ}
  have hA : A.Nonempty := by
    have : SigmaFinite (μ.restrict (∅ : Set Z)) := by rw [Measure.restrict_empty]; infer_instance
    obtain ⟨y, hy⟩ := exists_isDualRep hp hq φ MeasurableSet.empty
    exact ⟨_, ∅, y, MeasurableSet.empty, this, hy, rfl⟩
  have hAb : BddAbove A :=
    ⟨‖φ‖ ^ q.toReal, by rintro r ⟨S, y, -, -, hy, rfl⟩; exact hy.integral_le hp hq⟩
  have hint : ∀ {v : Z → ℝ}, MemLp v q μ → Integrable (fun z => ‖v z‖ ^ q.toReal) μ :=
    fun hv => (integrable_norm_rpow_iff hv.aestronglyMeasurable hq0 hq).2 hv
  have hpt : ∀ (T : Set Z) (v : Z → ℝ) (z : Z),
      ‖T.indicator v z‖ ^ q.toReal ≤ ‖v z‖ ^ q.toReal := fun T v z => by
    by_cases hz : z ∈ T
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, norm_zero, Real.zero_rpow hQ.ne']; positivity
  obtain ⟨r, -, hr, hrA⟩ := exists_seq_tendsto_sSup hA hAb
  choose S y hSm hSσ hy hry using hrA
  have hUm : MeasurableSet (⋃ n, S n) := MeasurableSet.iUnion hSm
  have : SigmaFinite (μ.restrict (⋃ n, S n)) := sigmaFinite_restrict_iUnion hSm hSσ
  obtain ⟨ys, hys⟩ := exists_isDualRep hp hq φ hUm
  have hle : sSup A ≤ ∫ z, ‖ys z‖ ^ q.toReal ∂μ := by
    refine le_of_tendsto' hr fun n => ?_
    have e := (hys.indicator (hSm n) (subset_iUnion S n)).ae_eq hp hq (hy n)
    have e' : (fun z => ‖(S n).indicator ys z‖ ^ q.toReal) =ᵐ[μ]
        fun z => ‖y n z‖ ^ q.toReal := by
      filter_upwards [e] with z hz; rw [hz]
    rw [hry n, ← integral_congr_ae e']
    exact integral_mono (hint (hys.1.indicator (hSm n))) (hint hys.1) (hpt _ _)
  refine ⟨hys.1.toLp ys, ContinuousLinearMap.ext fun u => ?_⟩
  obtain ⟨t, ht, htσ, hut⟩ := exists_sigmaFinite_support hp u
  have hσ' : SigmaFinite (μ.restrict ((⋃ n, S n) ∪ t)) := inferInstance
  obtain ⟨y', hy'⟩ := exists_isDualRep hp hq φ (hUm.union ht)
  have e1 : (⋃ n, S n).indicator y' =ᵐ[μ] ys :=
    (hy'.indicator hUm subset_union_left).ae_eq hp hq hys
  have hI : ∫ z, ‖y' z‖ ^ q.toReal ∂μ ≤ ∫ z, ‖(⋃ n, S n).indicator y' z‖ ^ q.toReal ∂μ := by
    calc ∫ z, ‖y' z‖ ^ q.toReal ∂μ ≤ sSup A :=
          le_csSup hAb ⟨_, y', hUm.union ht, hσ', hy', rfl⟩
      _ ≤ ∫ z, ‖ys z‖ ^ q.toReal ∂μ := hle
      _ = _ := integral_congr_ae (by filter_upwards [e1] with z hz; rw [hz])
  have hnn : ∀ z, 0 ≤ ‖y' z‖ ^ q.toReal - ‖(⋃ n, S n).indicator y' z‖ ^ q.toReal :=
    fun z => sub_nonneg.2 (hpt _ _ z)
  have hi := (hint hy'.1).sub (hint (hy'.1.indicator hUm))
  have h0 : ∫ z, (‖y' z‖ ^ q.toReal - ‖(⋃ n, S n).indicator y' z‖ ^ q.toReal) ∂μ = 0 :=
    le_antisymm (by rw [integral_sub (hint hy'.1) (hint (hy'.1.indicator hUm))]; linarith)
      (integral_nonneg hnn)
  have e3 : y' =ᵐ[μ] (⋃ n, S n).indicator y' := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hi).1 h0] with z hz
    by_cases hzU : z ∈ ⋃ n, S n
    · rw [indicator_of_mem hzU]
    · rw [indicator_of_notMem hzU]
      have h1 : ‖y' z‖ ^ q.toReal = 0 := by
        have h2 : ‖y' z‖ ^ q.toReal - ‖(⋃ n, S n).indicator y' z‖ ^ q.toReal = 0 := hz
        rwa [indicator_of_notMem hzU, norm_zero, Real.zero_rpow hQ.ne', sub_zero] at h2
      rwa [Real.rpow_eq_zero (norm_nonneg _) hQ.ne', norm_eq_zero] at h1
  rw [pairLqLp_apply, hy'.2.2 u (by
    filter_upwards [hut] with z hz hz' using hz fun h => hz' (Or.inr h))]
  refine integral_congr_ae ?_
  filter_upwards [hys.1.coeFn_toLp, e1, e3] with z h1 h2 h3
  rw [h1, h3, h2]

/-- `L_p* = L_q` for every measure and conjugate `1 < p, q < ∞`. -/
noncomputable def dualLpOfNeTop (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ) :=
  LinearIsometryEquiv.ofSurjective ⟨(pairLqLp μ p q).toLinearMap, norm_pairLqLp_eq hp hq⟩
    (exists_preimage_pairLqLp_of_ne_top hp hq)

/-- **Example 4** (pp. 449–450) on an arbitrary measure space: for `1 < p < ∞` with
`1/p + 1/q = 1`, the dual of `L_p(Z, 𝒵, μ)` is `L_q(Z, 𝒵, μ)`, with no finiteness or
σ-finiteness assumption on `μ`. Each `y ∈ L_q` gives `x ↦ ∫ y x dμ` in `L_p*`, every element of
`L_p*` arises from exactly one `y`, and norms are preserved. -/
theorem example_15_4_general (hp : p ≠ ∞) (hq : q ≠ ∞) :
    ∃ e : Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ), ∀ y x, e y x = ∫ z, y z * x z ∂μ :=
  ⟨dualLpOfNeTop hp hq, fun y x => pairLqLp_apply y x⟩

end StokeyLucasPrescott.ParetoOptimaEquilibria

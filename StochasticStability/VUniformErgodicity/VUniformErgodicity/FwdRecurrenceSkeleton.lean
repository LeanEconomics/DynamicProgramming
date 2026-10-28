/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.RenewalChain
import VUniformErgodicity.RegenerativeModels
import VUniformErgodicity.UniformErgodic

/-!
# The forward recurrence time `δ`-skeleton is `e^{γx}`-uniformly ergodic (MT §16.1.3)

Meyn and Tweedie, §16.1.3, p. 399: the forward recurrence time `δ`-skeleton `V⁺_δ` of a renewal
process with spread-out increment law `Γ ∈ G⁺(γ)`. As in `RenewalChain`, the chain is
`fwdChain Γ δ`: it moves by `V⁺_δ` (`fwdSkelKernel Γ δ`) on `(0, ∞)` and restarts uniformly on
`(0, δ)` from `(−∞, 0]`, so that it is irreducible on all of `ℝ` (`fwdChain_structure`).

* `ofReal_exp_fwdTimeCts_le`, `lintegral_exp_fwdSkelKernel_le`: for `x ≤ δ`,
  `E_x[e^{γ V⁺(δ)}] ≤ (∫ e^{γy} Γ(dy)) δ_x ∗ U(−∞, δ]` (the overshoot is at most one increment).
* `fwdChain_driftV4`: (V4) for `V(x) = e^{γ x⁺}` (`fwdExpV`): off `C = (−∞, δ]` the chain moves
  deterministically, `P(x, {x − δ}) = 1`, and `PV(x)/V(x) = e^{−γδ} < 1`; on `C` the drift is
  bounded through the renewal measure (`renMeas_dirac_Iic_le`).
* `fwdChain_isPetite_Iic`: `C = (−∞, 0] ∪ (0, δ) ∪ {δ}` is petite (a union of small sets).
* `fwdChain_vUniformlyErgodic` (p. 399): for every small enough `δ > 0` the chain is positive,
  aperiodic and `e^{γx⁺}`-uniformly ergodic, with `Σ rⁿ |||Pⁿ − 1 ⊗ π|||_V < ∞`, and
  `‖Pⁿ(x, ·) − π‖_V ≤ R r⁻ⁿ e^{γ x⁺}`: the moment generating function, and so every polynomial
  moment, converges geometrically fast.
* `fwdSkelKernel_pow_of_lt`: for `x > nδ`, `Pⁿ(x, ·) = δ_{x − nδ}`.
* `fwdChain_not_uniformlyErgodic` (p. 399, from Theorem 16.0.2): the chain on `ℝ` is not uniformly
  ergodic for any invariant probability; `restrict_fwdChain_not_uniformlyErgodic`: nor is its
  restriction to any absorbing set that is unbounded above.
* `fwdSkelInv_Ioi_pos`, `exists_mem_gt_of_unbounded`: if `Γ` is not of bounded range, the
  stationary law `F[y, ∞) dy` (10.36) charges every `(c, ∞)`, so every absorbing set that carries
  it is unbounded above and no restriction to such a set is uniformly ergodic
  (`fwdChain_unbounded_not_uniformlyErgodic`). This is the book's "only if `Γ` is of bounded
  range".

**Hypotheses.** The book's `C = [0, δ]` is `(−∞, δ]` here, since the restart region `(−∞, 0]`
belongs to the state space of `fwdChain`. The increments are nonnegative and not concentrated at
`0`, and `δ` is small, as in `fwdChain_structure` (aperiodicity and small sets, Propositions 5.3.3
and 5.4.7).

**Not formalised.** The remarks that `Γ ∈ G⁺(γ)` is also necessary for geometric ergodicity
("obvious from its construction") and that for bounded range `Γ[0, c] = 1` the chain restricted to
`[0, c]` is uniformly ergodic, and the comparison with §15.1.4.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-! ### The exponential overshoot -/

/-- **The exponential overshoot**: if `x ≤ δ`, the increments are nonnegative and their partial
sums diverge, then `e^{γ V⁺(δ)} ≤ Σⱼ e^{γ Yⱼ} 1{Z_{j+1} ≤ δ}` for `γ ≥ 0`. -/
theorem ofReal_exp_fwdTimeCts_le {γ x δ : ℝ} (hγ : 0 ≤ γ) (hxδ : x ≤ δ) {w : ℕ → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) :
    ENNReal.ofReal (Real.exp (γ * fwdTimeCts (resEpoch x w) δ)) ≤
      ∑' j : ℕ, ENNReal.ofReal (Real.exp (γ * w j)) *
        (Iic δ).indicator 1 (resEpoch x w (j + 1)) := by
  rw [fwdTimeCts_eq_resEpoch hw hdiv]
  set τ := sInf {m | δ < resEpoch x w (m + 1)} with hτdef
  have hex := exists_resEpoch_gt (x := x) hdiv δ
  have hτ : δ < resEpoch x w (τ + 1) := Nat.sInf_mem (s := {m | δ < resEpoch x w (m + 1)}) hex
  have hτ1 : 1 ≤ τ := by
    by_contra h
    have h0 : τ = 0 := by omega
    rw [h0, zero_add, resEpoch_succ_eq, Finset.range_zero, Finset.sum_empty, add_zero] at hτ
    linarith
  obtain ⟨j, hj⟩ : ∃ j, τ = j + 1 := ⟨τ - 1, by omega⟩
  have hjle : resEpoch x w (j + 1) ≤ δ :=
    not_lt.1 (Nat.notMem_of_lt_sInf (s := {m | δ < resEpoch x w (m + 1)}) (by omega))
  have hstep : resEpoch x w (τ + 1) - δ ≤ w j := by
    rw [hj, resEpoch_succ_eq, Finset.sum_range_succ] at hτ ⊢
    rw [resEpoch_succ_eq] at hjle
    linarith
  calc ENNReal.ofReal (Real.exp (γ * (resEpoch x w (τ + 1) - δ)))
      ≤ ENNReal.ofReal (Real.exp (γ * w j)) * 1 := by
        rw [mul_one]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hstep hγ))
    _ = ENNReal.ofReal (Real.exp (γ * w j)) * (Iic δ).indicator 1 (resEpoch x w (j + 1)) := by
        rw [indicator_of_mem (show resEpoch x w (j + 1) ∈ Iic δ from hjle), Pi.one_apply]
    _ ≤ _ := ENNReal.le_tsum (f := fun j : ℕ =>
        ENNReal.ofReal (Real.exp (γ * w j)) * (Iic δ).indicator 1 (resEpoch x w (j + 1))) j

variable (Γ : Measure ℝ) [IsProbabilityMeasure Γ]

/-- **The exponential moment of the forward recurrence time**: for `x ≤ δ` and `γ ≥ 0`,
`E_x[e^{γ V⁺(δ)}] ≤ (∫ e^{γy} Γ(dy)) δ_x ∗ U(−∞, δ]`. -/
theorem lintegral_exp_fwdSkelKernel_le (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    {γ x δ : ℝ} (hγ : 0 ≤ γ) (hxδ : x ≤ δ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (γ * y)) ∂fwdSkelKernel Γ δ x ≤
      (∫⁻ y, ENNReal.ofReal (Real.exp (γ * y)) ∂Γ) * renMeas Γ (Measure.dirac x) (Iic δ) := by
  set ν := incr Γ with hν
  have hfm : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (γ * y)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp (measurable_const_mul γ))
  rw [fwdSkelKernel, recursionKernel_apply _ (measurable_fwdSkelStep δ) x,
    lintegral_map (f := fun y => ENNReal.ofReal (Real.exp (γ * y)))
      (g := fun w => fwdSkelStep δ (x, w)) hfm
      ((measurable_fwdSkelStep δ).comp measurable_prodMk_left)]
  have hpair : ∀ j : ℕ, Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) := fun j =>
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hF : ∀ j : ℕ, Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (γ * q.2)) * (Iic δ).indicator 1 (x + q.1) := fun j =>
    (hfm.comp measurable_snd).mul
      ((measurable_one.indicator measurableSet_Iic).comp (measurable_const.add measurable_fst))
  calc ∫⁻ w, ENNReal.ofReal (Real.exp (γ * fwdSkelStep δ (x, w))) ∂ν
      ≤ ∫⁻ w, ∑' j : ℕ, ENNReal.ofReal (Real.exp (γ * w j)) *
          (Iic δ).indicator 1 (resEpoch x w (j + 1)) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨hdiv, hw⟩
        exact ofReal_exp_fwdTimeCts_le hγ hxδ hw hdiv
    _ = ∑' j : ℕ, ∫⁻ w, ENNReal.ofReal (Real.exp (γ * w j)) *
          (Iic δ).indicator 1 (resEpoch x w (j + 1)) ∂ν :=
        lintegral_tsum fun j => ((hF j).comp (hpair j)).aemeasurable
    _ = ∑' j : ℕ, (∫⁻ y, ENNReal.ofReal (Real.exp (γ * y)) ∂Γ) *
          ν {w | resEpoch x w (j + 1) ∈ Iic δ} := by
        refine tsum_congr fun j => ?_
        have e : ∫⁻ w, ENNReal.ofReal (Real.exp (γ * w j)) *
            (Iic δ).indicator 1 (resEpoch x w (j + 1)) ∂ν =
            ∫⁻ q, ENNReal.ofReal (Real.exp (γ * q.2)) * (Iic δ).indicator 1 (x + q.1)
              ∂((convPow Γ j).prod Γ) := by
          rw [← infinitePi_map_partialSum_next Γ j, lintegral_map (hF j) (hpair j)]
          rfl
        have hsm : Measurable fun w : ℕ → ℝ => ∑ i ∈ Finset.range j, w i :=
          Finset.measurable_sum _ fun i _ => measurable_pi_apply i
        have hind : Measurable fun s : ℝ => (Iic δ).indicator (1 : ℝ → ℝ≥0∞) (x + s) :=
          (measurable_one.indicator measurableSet_Iic).comp (measurable_const.add measurable_id)
        have e2 : ∫⁻ q, ENNReal.ofReal (Real.exp (γ * q.2)) * (Iic δ).indicator 1 (x + q.1)
            ∂((convPow Γ j).prod Γ) = (∫⁻ s, (Iic δ).indicator (1 : ℝ → ℝ≥0∞) (x + s)
              ∂convPow Γ j) * ∫⁻ y, ENNReal.ofReal (Real.exp (γ * y)) ∂Γ := by
          rw [← lintegral_prod_mul hind.aemeasurable hfm.aemeasurable]
          exact lintegral_congr fun q => mul_comm _ _
        have e3 : ∫⁻ s, (Iic δ).indicator (1 : ℝ → ℝ≥0∞) (x + s) ∂convPow Γ j =
            ν {w | resEpoch x w (j + 1) ∈ Iic δ} := by
          rw [← incr_map_partialSum Γ j, lintegral_map hind hsm]
          exact (lintegral_indicator_const_comp (measurable_const.add hsm) measurableSet_Iic
            1).trans (one_mul _)
        rw [e, e2, e3, mul_comm]
    _ = (∫⁻ y, ENNReal.ofReal (Real.exp (γ * y)) ∂Γ) * renMeas Γ (Measure.dirac x) (Iic δ) := by
        rw [ENNReal.tsum_mul_left, renMeas_dirac_apply Γ x measurableSet_Iic]

/-! ### The drift (V4) with `V(x) = e^{γ x⁺}` -/

/-- The test function `V(x) = e^{γ x⁺}` of p. 399 (`e^{γx}` on `(0, ∞)`, `1` on `(−∞, 0]`). -/
noncomputable def fwdExpV (γ x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ * max x 0))

/-- `fwdExpV γ` is measurable. -/
theorem measurable_fwdExpV (γ : ℝ) : Measurable (fwdExpV γ) :=
  ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    ((measurable_id.max measurable_const).const_mul γ))

/-- `fwdExpV γ ≥ 1` for `γ ≥ 0`. -/
theorem one_le_fwdExpV {γ : ℝ} (hγ : 0 ≤ γ) (x : ℝ) : 1 ≤ fwdExpV γ x := by
  rw [fwdExpV, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hγ (le_max_right x 0)))

/-- `fwdExpV γ` is finite. -/
theorem fwdExpV_ne_top (γ x : ℝ) : fwdExpV γ x ≠ ∞ := ENNReal.ofReal_ne_top

/-- **(V4) for the forward recurrence time `δ`-skeleton** (MT p. 399): with `V(x) = e^{γ x⁺}`,
`PV(x) = e^{−γδ} V(x)` for `x > δ`, and on `C = (−∞, δ]`, `PV ≤ b` with
`b = (∫ e^{γy} Γ(dy)) eᵟ (1 − φ)⁻¹ + e^{γδ}`, `φ = ∫ e^{−y} Γ(dy)`. -/
theorem fwdChain_driftV4 (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    {γ δ : ℝ} (hγ : 0 ≤ γ) (hδ : 0 < δ) :
    DriftV4 (fwdChain Γ δ) (fwdExpV γ) (ENNReal.ofReal (Real.exp (-(γ * δ))))
      ((∫⁻ y, ENNReal.ofReal (Real.exp (γ * y)) ∂Γ) * (ENNReal.ofReal (Real.exp δ) *
        (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹) + ENNReal.ofReal (Real.exp (γ * δ)))
      (Iic δ) := by
  intro x
  rcases le_or_gt x δ with hxδ | hxδ
  · rw [indicator_of_mem (show x ∈ Iic δ from hxδ)]
    refine le_trans ?_ le_add_self
    by_cases hx0 : 0 < x
    · rw [fwdChain, absorbKernel_of_mem _ _ _ (show x ∈ Ioi (0 : ℝ) from hx0)]
      have hae : ∀ᵐ y ∂fwdSkelKernel Γ δ x,
          fwdExpV γ y = ENNReal.ofReal (Real.exp (γ * y)) := by
        have h0 := fwdSkelKernel_Iic_zero Γ hΓ0 hΓpos δ x
        refine (measure_eq_zero_iff_ae_notMem.1 h0).mono fun y hy => ?_
        rw [fwdExpV, max_eq_left (not_le.1 hy).le]
      rw [lintegral_congr_ae hae]
      refine (lintegral_exp_fwdSkelKernel_le Γ hΓ0 hΓpos hγ hxδ).trans (le_trans ?_ le_self_add)
      refine mul_le_mul' le_rfl ((renMeas_dirac_Iic_le Γ x δ).trans (mul_le_mul'
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))) le_rfl))
    · rw [fwdChain, absorbKernel_of_notMem _ _ _ (show x ∉ Ioi (0 : ℝ) from hx0)]
      refine le_trans ?_ le_add_self
      have := isProbabilityMeasure_unifδ hδ
      have hmem : ∀ᵐ y ∂unifδ δ, y ∈ Ioo 0 δ := by
        rw [unifδ]
        exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioo) _
      calc ∫⁻ y, fwdExpV γ y ∂unifδ δ ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (γ * δ)) ∂unifδ δ := by
            refine lintegral_mono_ae (hmem.mono fun y hy => ?_)
            exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
              (mul_le_mul_of_nonneg_left (max_le hy.2.le hδ.le) hγ))
        _ = ENNReal.ofReal (Real.exp (γ * δ)) := by rw [lintegral_const, measure_univ, mul_one]
  · rw [indicator_of_notMem (show x ∉ Iic δ from not_le.2 hxδ), add_zero, fwdChain,
      absorbKernel_of_mem _ _ _ (show x ∈ Ioi (0 : ℝ) from hδ.trans hxδ),
      fwdSkelKernel_of_lt Γ hΓ0 hΓpos hδ.le hxδ, lintegral_dirac, fwdExpV, fwdExpV,
      max_eq_left (by linarith), max_eq_left (by linarith),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    exact le_of_eq (congrArg ENNReal.ofReal (congrArg Real.exp (by ring)))

/-- **`C = (−∞, δ]` is petite** for the restarted chain: `(−∞, 0]` is small (one step restarts
uniformly on `(0, δ)`), `(0, δ)` is small for `V⁺_δ`, and the singleton `{δ}` is small. -/
theorem fwdChain_isPetite_Iic (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ : ℝ}
    (hδ : 0 < δ) {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_fwdChain Γ hδ; IsMaximalIrreducibility (fwdChain Γ δ) ψ)
    {M : ℕ} {c : ℝ≥0∞}
    (hsm : IsSmallSet (fwdSkelKernel Γ δ) M (c • volume.restrict (Ioo 0 δ)) (Ioo 0 δ)) :
    IsPetite (fwdChain Γ δ) (Iic δ) := by
  have := isMarkovKernel_fwdChain Γ hδ
  have := isProbabilityMeasure_unifδ hδ
  have hset : Iic δ = (Iic 0 ∪ Ioo 0 δ) ∪ {δ} := by
    ext y
    simp only [mem_Iic, mem_union, mem_Ioo, mem_singleton_iff]
    constructor
    · intro h
      rcases le_or_gt y 0 with h0 | h0
      · exact Or.inl (Or.inl h0)
      · rcases lt_or_eq_of_le h with h1 | h1
        · exact Or.inl (Or.inr ⟨h0, h1⟩)
        · exact Or.inr h1
    · rintro ((h | ⟨-, h⟩) | h)
      · linarith
      · exact h.le
      · exact h.le
  have h1 : IsSmallSet (fwdChain Γ δ) 1 (unifδ δ) (Iic 0) := by
    refine ⟨measurableSet_Iic, one_pos, IsProbabilityMeasure.ne_zero _, fun x hx => ?_⟩
    rw [pow_one, fwdChain, absorbKernel_of_notMem _ _ _
      (show x ∉ Ioi (0 : ℝ) from fun h => not_lt.2 (mem_Iic.1 hx) h)]
  have h2 : IsSmallSet (fwdChain Γ δ) M (c • volume.restrict (Ioo 0 δ)) (Ioo 0 δ) := by
    refine ⟨hsm.1, hsm.2.1, hsm.2.2.1, fun x hx => ?_⟩
    rw [fwdChain_pow_of_pos Γ hΓ0 hΓpos δ M hx.1]
    exact hsm.2.2.2 x hx
  have h3 : IsSmallSet (fwdChain Γ δ) 1 (fwdChain Γ δ δ) {δ} := by
    refine ⟨measurableSet_singleton δ, one_pos, IsProbabilityMeasure.ne_zero _, fun x hx => ?_⟩
    rw [mem_singleton_iff.1 hx, pow_one]
  rw [hset]
  exact proposition_5_5_5_ii _ hψ (proposition_5_5_5_ii _ hψ ⟨_, _, proposition_5_5_3 h1⟩
    ⟨_, _, proposition_5_5_3 h2⟩) ⟨_, _, proposition_5_5_3 h3⟩

omit [IsProbabilityMeasure Γ] in
/-- `Γ ∈ G⁺(γ)` gives a finite exponential moment `∫ e^{γy} Γ(dy) < ∞` and a finite mean. -/
theorem fwd_moments_ne_top {γ : ℝ} (hγ : IsLaplaceFinite Γ γ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (γ * y)) ∂Γ ≠ ∞ ∧ ∫⁻ y, ENNReal.ofReal y ∂Γ ≠ ∞ := by
  have hexp := ((hγ.2 γ hγ.1 le_rfl).lintegral_lt_top).ne
  refine ⟨hexp, ?_⟩
  have hle : ∀ y, ENNReal.ofReal y ≤ ENNReal.ofReal γ⁻¹ * ENNReal.ofReal (Real.exp (γ * y)) :=
    fun y => by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hγ.1.le)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := Real.add_one_le_exp (γ * y)
      rw [le_inv_mul_iff₀ hγ.1]
      linarith
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hexp

/-- **The forward recurrence time `δ`-skeleton is `e^{γx}`-uniformly ergodic** (MT p. 399): for a
spread-out increment law `Γ` on `[0, ∞)` with `Γ ∈ G⁺(γ)`, and every small enough `δ > 0`, the
(restarted) chain is positive and aperiodic, and for every invariant probability `π` it is
`V`-uniformly ergodic for `V(x) = e^{γ x⁺}`, with `Σ rⁿ |||Pⁿ − 1 ⊗ π|||_V < ∞` and
`‖Pⁿ(x, ·) − π‖_V ≤ R r⁻ⁿ V(x)` for some `r > 1`, `R < ∞`. -/
theorem fwdChain_vUniformlyErgodic (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) (hs : IsSpreadOut Γ) {γ : ℝ} (hγ : IsLaplaceFinite Γ γ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ (hδ : 0 < δ), δ ≤ δ₀ →
      haveI := isMarkovKernel_fwdChain Γ hδ
      ∃ ψ : Measure ℝ, IsPositive (fwdChain Γ δ) ψ ∧ IsAperiodic (fwdChain Γ δ) ψ ∧
        ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], IsInvariant (fwdChain Γ δ) μ →
          IsVUniformlyErgodic (fwdExpV γ) (fwdChain Γ δ) μ ∧
          (∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧
            ∑' n, r ^ n * vErgDist (fwdExpV γ) (fwdChain Γ δ) μ n ≠ ∞) ∧
          ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x n,
            fNorm (fwdExpV γ) ((fwdChain Γ δ ^ n) x) μ ≤ R * r⁻¹ ^ n * fwdExpV γ x := by
  obtain ⟨hexp, hm⟩ := fwd_moments_ne_top Γ hγ
  obtain ⟨δ₁, hδ₁, hall⟩ := fwdChain_structure Γ hΓ0 hΓpos hs hm
  obtain ⟨δ₂, hδ₂, hsmallAll⟩ := proposition_5_3_3 Γ hΓ0 hΓpos hs
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hδle => ?_⟩
  have := isMarkovKernel_fwdChain Γ hδ
  obtain ⟨ψ, hpos, hap, -⟩ := hall δ hδ (hδle.trans (min_le_left _ _))
  obtain ⟨M, c, -, hsm, -⟩ := hsmallAll δ hδ (hδle.trans (min_le_right _ _))
  have hpet := fwdChain_isPetite_Iic Γ hΓ0 hΓpos hδ hpos.1 hsm
  have hγ0 : 0 ≤ γ := hγ.1.le
  have hd := fwdChain_driftV4 Γ hΓ0 hΓpos hγ0 hδ
  have hρ : ENNReal.ofReal (Real.exp (-(γ * δ))) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2
      (Real.exp_lt_one_iff.2 (neg_lt_zero.2 (mul_pos hγ.1 hδ)))
  have hφ := exp_moment_lt_one Γ hΓ0 hΓpos
  have hb : (∫⁻ y, ENNReal.ofReal (Real.exp (γ * y)) ∂Γ) * (ENNReal.ofReal (Real.exp δ) *
      (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹) + ENNReal.ofReal (Real.exp (γ * δ)) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hexp (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hφ).ne')), ENNReal.ofReal_ne_top⟩
  have hVm := measurable_fwdExpV γ
  have hV1 := one_le_fwdExpV hγ0
  refine ⟨ψ, hpos, hap, fun μ _ hμ => ?_⟩
  obtain ⟨hsum, hlim⟩ := theorem_16_1_2 hpos.1 hap hVm hV1 (fwdExpV_ne_top γ) hρ hb hpet hd μ hμ
  obtain ⟨-, r, hr, -, R, hR, hbd⟩ :=
    vErgDist_le_of_driftV4 hpos.1 hap hVm hV1 (fwdExpV_ne_top γ) hρ hb hpet hd μ hμ
  refine ⟨⟨hμ, hlim⟩, hsum, r, hr, R, hR, fun x n => ?_⟩
  exact (fNorm_pow_le_vErgDist_mul _ μ n (zero_lt_one.trans_le (hV1 x)).ne'
    (fwdExpV_ne_top γ x)).trans (mul_le_mul' (hbd n) le_rfl)

/-! ### No uniform ergodicity -/

/-- **Deterministic descent** (MT p. 399): for `x > nδ`, `(V⁺_δ)ⁿ(x, ·) = δ_{x − nδ}`. -/
theorem fwdSkelKernel_pow_of_lt (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ : ℝ}
    (hδ : 0 ≤ δ) (n : ℕ) :
    ∀ x : ℝ, n * δ < x → (fwdSkelKernel Γ δ ^ n) x = Measure.dirac (x - n * δ) := by
  have := isMarkovKernel_fwdSkelKernel Γ δ
  induction n with
  | zero =>
    intro x _
    rw [pow_zero_apply, Nat.cast_zero, zero_mul, sub_zero]
  | succ n ih =>
    intro x hx
    have h1 : ((n + 1 : ℕ) : ℝ) * δ = n * δ + δ := by push_cast; ring
    have h0 : (0 : ℝ) ≤ n * δ := mul_nonneg n.cast_nonneg hδ
    have hxδ : δ < x := by linarith
    ext A hA
    rw [pow_succ_apply _ n x hA, fwdSkelKernel_of_lt Γ hΓ0 hΓpos hδ hxδ, lintegral_dirac,
      ih (x - δ) (by linarith)]
    have e : x - δ - (n : ℝ) * δ = x - ((n + 1 : ℕ) : ℝ) * δ := by rw [h1]; ring
    rw [e]

/-- A Dirac law is at total variation distance at least `1/2` from a probability that gives its
point mass at most `1/2`. -/
theorem half_le_tvNorm_dirac {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] {y : X} (hy : μ {y} ≤ 2⁻¹) :
    (2⁻¹ : ℝ) ≤ tvNorm (Measure.dirac y) μ := by
  have hf1 : ∀ x, |({y} : Set X).indicator (1 : X → ℝ) x| ≤ 1 := fun x => by
    by_cases hx : x ∈ ({y} : Set X)
    · rw [indicator_of_mem hx, Pi.one_apply, abs_one]
    · rw [indicator_of_notMem hx, abs_zero]
      exact zero_le_one
  have h := abs_integral_sub_le_tvNorm (Measure.dirac y) μ
    (measurable_one.indicator (measurableSet_singleton y)) hf1
  rw [integral_indicator_one (measurableSet_singleton y),
    integral_indicator_one (measurableSet_singleton y)] at h
  have h1 : (Measure.dirac y).real {y} = 1 := by
    rw [measureReal_def, Measure.dirac_apply_of_mem (mem_singleton y), ENNReal.toReal_one]
  have h2 : μ.real {y} ≤ 2⁻¹ := by
    have := ENNReal.toReal_mono (by norm_num : (2⁻¹ : ℝ≥0∞) ≠ ∞) hy
    rwa [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at this
  rw [h1] at h
  calc (2⁻¹ : ℝ) ≤ 1 - μ.real {y} := by linarith
    _ ≤ |1 - μ.real {y}| := le_abs_self _
    _ ≤ _ := h

/-- Of two distinct points, one has probability at most `1/2`. -/
theorem exists_le_half_of_ne {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] {y₁ y₂ : X} (h : y₁ ≠ y₂) :
    μ {y₁} ≤ 2⁻¹ ∨ μ {y₂} ≤ 2⁻¹ := by
  by_contra hc
  push Not at hc
  have hadd : μ {y₁} + μ {y₂} = μ ({y₁} ∪ {y₂}) :=
    (measure_union (disjoint_singleton.2 h) (measurableSet_singleton y₂)).symm
  have hle : μ {y₁} + μ {y₂} ≤ 1 := hadd ▸ prob_le_one
  have hlt : (1 : ℝ≥0∞) < μ {y₁} + μ {y₂} :=
    calc (1 : ℝ≥0∞) = 2⁻¹ + 2⁻¹ := ENNReal.inv_two_add_inv_two.symm
      _ < μ {y₁} + μ {y₂} := ENNReal.add_lt_add hc.1 hc.2
  exact absurd hlt (not_lt.2 hle)

/-- **The forward recurrence time chain is not uniformly ergodic** (MT p. 399, via
Theorem 16.0.2): from `y + nδ` the chain is at `y` at time `n`, so
`sup_x ‖Pⁿ(x, ·) − π‖ ≥ 1/2` for every `n` and every probability `π`. -/
theorem fwdChain_not_uniformlyErgodic (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ : ℝ}
    (hδ : 0 < δ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ¬ IsUniformlyErgodic (fwdChain Γ δ) μ := by
  have := isMarkovKernel_fwdChain Γ hδ
  intro h
  have hlow : ∀ n, ENNReal.ofReal 2⁻¹ ≤
      ⨆ x, ENNReal.ofReal (tvNorm ((fwdChain Γ δ ^ n) x) μ) := fun n => by
    obtain ⟨y, hy0, hy⟩ : ∃ y : ℝ, 0 < y ∧ μ {y} ≤ 2⁻¹ := by
      rcases exists_le_half_of_ne μ (show (1 : ℝ) ≠ 2 by norm_num) with h1 | h2
      · exact ⟨1, one_pos, h1⟩
      · exact ⟨2, two_pos, h2⟩
    have h0 : (0 : ℝ) ≤ n * δ := mul_nonneg n.cast_nonneg hδ.le
    have hx : (n : ℝ) * δ < y + n * δ := by linarith
    have hpos : 0 < y + n * δ := by linarith
    refine le_trans ?_ (le_iSup _ (y + n * δ))
    rw [fwdChain_pow_of_pos Γ hΓ0 hΓpos δ n hpos,
      fwdSkelKernel_pow_of_lt Γ hΓ0 hΓpos hδ.le n _ hx, add_sub_cancel_right]
    exact ENNReal.ofReal_le_ofReal (half_le_tvNorm_dirac μ hy)
  have hle : ENNReal.ofReal 2⁻¹ ≤ 0 := ge_of_tendsto h.2 (Eventually.of_forall hlow)
  exact absurd hle (not_le.2 (ENNReal.ofReal_pos.2 (by norm_num)))

/-- **No restriction to an unbounded absorbing set is uniformly ergodic**: if `A` is absorbing
and unbounded above, the chain restricted to `A` is not uniformly ergodic for any probability
on `A`. -/
theorem restrict_fwdChain_not_uniformlyErgodic (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ} (hA : MeasurableSet A)
    (hAbs : IsAbsorbing (fwdChain Γ δ) A) (hunb : ∀ c, ∃ y ∈ A, c < y) (μ : Measure A)
    [IsProbabilityMeasure μ] : ¬ IsUniformlyErgodic (restrictKernel (fwdChain Γ δ) hA) μ := by
  have := isMarkovKernel_fwdChain Γ hδ
  intro h
  have hlow : ∀ n, ENNReal.ofReal 2⁻¹ ≤
      ⨆ x, ENNReal.ofReal (tvNorm ((restrictKernel (fwdChain Γ δ) hA ^ n) x) μ) := fun n => by
    have h0 : (0 : ℝ) ≤ n * δ := mul_nonneg n.cast_nonneg hδ.le
    obtain ⟨y₁, hy₁A, hy₁⟩ := hunb (n * δ)
    obtain ⟨y₂, hy₂A, hy₂⟩ := hunb y₁
    have himg : ∀ y ∈ A, (n : ℝ) * δ < y →
        (fwdChain Γ δ ^ n) y = Measure.dirac (y - n * δ) ∧ y - n * δ ∈ A := fun y hyA hy => by
      have hpos : 0 < y := by linarith
      have hd : (fwdChain Γ δ ^ n) y = Measure.dirac (y - n * δ) := by
        rw [fwdChain_pow_of_pos Γ hΓ0 hΓpos δ n hpos,
          fwdSkelKernel_pow_of_lt Γ hΓ0 hΓpos hδ.le n y hy]
      refine ⟨hd, ?_⟩
      by_contra hz
      have hc := hAbs.pow_compl hA n hyA
      rw [hd, Measure.dirac_apply_of_mem (show y - n * δ ∈ Aᶜ from hz)] at hc
      exact one_ne_zero hc
    obtain ⟨hd₁, hz₁⟩ := himg y₁ hy₁A hy₁
    obtain ⟨hd₂, hz₂⟩ := himg y₂ hy₂A (hy₁.trans hy₂)
    have hne : (⟨y₁ - n * δ, hz₁⟩ : A) ≠ ⟨y₂ - n * δ, hz₂⟩ := fun he => by
      have he' : y₁ - n * δ = y₂ - n * δ := congrArg Subtype.val he
      linarith
    have hdir : ∀ (y : ℝ) (hyA : y ∈ A) (hz : y - n * δ ∈ A),
        (fwdChain Γ δ ^ n) y = Measure.dirac (y - n * δ) →
        (restrictKernel (fwdChain Γ δ) hA ^ n) ⟨y, hyA⟩ = Measure.dirac ⟨y - n * δ, hz⟩ :=
      fun y hyA hz hd => by
        ext B hB
        have hB' : MeasurableSet (Subtype.val '' B) :=
          (MeasurableEmbedding.subtype_coe hA).measurableSet_image.2 hB
        rw [restrictKernel_pow_apply _ hA hAbs n _ hB, hd, Measure.dirac_apply' _ hB',
          Measure.dirac_apply' _ hB]
        by_cases hzB : (⟨y - n * δ, hz⟩ : A) ∈ B
        · rw [indicator_of_mem hzB, indicator_of_mem (mem_image_of_mem _ hzB)]
          rfl
        · rw [indicator_of_notMem hzB, indicator_of_notMem]
          rintro ⟨w, hw, hwz⟩
          exact hzB ((Subtype.ext hwz : w = ⟨y - n * δ, hz⟩) ▸ hw)
    rcases exists_le_half_of_ne μ hne with h1 | h2
    · refine le_trans ?_ (le_iSup _ (⟨y₁, hy₁A⟩ : A))
      rw [hdir y₁ hy₁A hz₁ hd₁]
      exact ENNReal.ofReal_le_ofReal (half_le_tvNorm_dirac μ h1)
    · refine le_trans ?_ (le_iSup _ (⟨y₂, hy₂A⟩ : A))
      rw [hdir y₂ hy₂A hz₂ hd₂]
      exact ENNReal.ofReal_le_ofReal (half_le_tvNorm_dirac μ h2)
  have hle : ENNReal.ofReal 2⁻¹ ≤ 0 := ge_of_tendsto h.2 (Eventually.of_forall hlow)
  exact absurd hle (not_le.2 (ENNReal.ofReal_pos.2 (by norm_num)))

omit [IsProbabilityMeasure Γ] in
/-- If `Γ` is not of bounded range, the stationary law `F[y, ∞) dy` of (10.36) charges every
half line `(c, ∞)`. -/
theorem fwdSkelInv_Ioi_pos (hunb : ∀ c, 0 < Γ (Ioi c)) (c : ℝ) : 0 < fwdSkelInv Γ (Ioi c) := by
  set c' := max c 0 with hc'
  have hsub : Ioo c' (c' + 1) ⊆ Ioi c ∩ Ioi 0 := fun y hy =>
    ⟨lt_of_le_of_lt (le_max_left _ _) hy.1, lt_of_le_of_lt (le_max_right _ _) hy.1⟩
  rw [fwdSkelInv, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  calc (0 : ℝ≥0∞) < Γ (Ioi (c' + 1)) * volume (Ioo c' (c' + 1)) := by
        rw [Real.volume_Ioo, add_sub_cancel_left, ENNReal.ofReal_one, mul_one]
        exact hunb _
    _ = ∫⁻ _ in Ioo c' (c' + 1), Γ (Ioi (c' + 1)) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in Ioo c' (c' + 1), Γ (Ici y) :=
        setLIntegral_mono' measurableSet_Ioo fun y hy =>
          measure_mono fun z hz => (hy.2.trans (mem_Ioi.1 hz)).le
    _ ≤ ∫⁻ y in Ioi c ∩ Ioi 0, Γ (Ici y) := lintegral_mono_set hsub

omit [IsProbabilityMeasure Γ] in
/-- If `Γ` is not of bounded range, every set carrying the stationary law `F[y, ∞) dy` is unbounded
above. -/
theorem exists_mem_gt_of_unbounded (hunb : ∀ c, 0 < Γ (Ioi c)) {A : Set ℝ}
    (hAc : fwdSkelInv Γ Aᶜ = 0) (c : ℝ) : ∃ y ∈ A, c < y := by
  by_contra h
  push Not at h
  have hsub : Ioi c ⊆ Aᶜ := fun y hy hyA => absurd (mem_Ioi.1 hy) (not_lt.2 (h y hyA))
  exact (fwdSkelInv_Ioi_pos Γ hunb c).ne' (measure_mono_null hsub hAc)

/-- **Uniform ergodicity needs bounded range** (MT p. 399): if `Γ(c, ∞) > 0` for every `c`, the
chain restricted to any absorbing set that carries the stationary law `F[y, ∞) dy` is not
uniformly ergodic, for any probability on that set. -/
theorem fwdChain_unbounded_not_uniformlyErgodic (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    (hunb : ∀ c, 0 < Γ (Ioi c)) {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ} (hA : MeasurableSet A)
    (hAbs : IsAbsorbing (fwdChain Γ δ) A) (hAc : fwdSkelInv Γ Aᶜ = 0) (μ : Measure A)
    [IsProbabilityMeasure μ] : ¬ IsUniformlyErgodic (restrictKernel (fwdChain Γ δ) hA) μ :=
  restrict_fwdChain_not_uniformlyErgodic Γ hΓ0 hΓpos hδ hA hAbs
    (exists_mem_gt_of_unbounded Γ hunb hAc) μ

end MeynTweedie.VUniformErgodicity

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.OCSetting
import Applications.SLPLemma95
import Mathlib.Probability.Distributions.Geometric

/-!
# Lemma 6.4.1: the expected continuation value is continuous

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCLemma641`), namespace renamed.

Miao, §6.4, p. 174. For continuous `f : X × Z → ℝ`,
`h(x, a, z) = ∫ f(φ(x, a, z, z′), z′) Q(z, dz′)` is continuous on `X × A × Z`. The book refers
to SLP Lemmas 9.5 and 9.5′.

* `lemma_6_4_1_compact`: case (ii) of Assumption 6.4.3 (`Z` compact, `Q` Feller), for every
  continuous `f`, bounded or not. It rests on `continuous_mop_of_compact`, SLP's Lemma 9.5(b)
  (`lemma_9_5_compact`) without the bound on `f`: on a compact `Z` each section `f(w, ·)` is
  bounded, which is all the proof needs.
* `lemma_6_4_1_countable`: case (i) (`Z` discrete with all subsets measurable), for **bounded**
  continuous `f`, by SLP's `lemma_9_5'` and `lemma_9_5_discrete` applied with the action
  `(a, z)`, since here `φ` also depends on the current shock. Countability of `Z` is not needed.
* **Correction.** In case (i) the lemma is false for unbounded `f`
  (`lemma_6_4_1_countable_counterexample`): with `Z = ℕ`, `Q(z, {n}) = 2^{-(n+1)}`, `φ = x` and
  `f(x, n) = 2^{n+1} max(0, 1 − |(n+1)x − 1|)`, each `f(x, ·)` vanishes off a finite set, yet
  `h(1/(m+1)) ≥ 1` for all `m` while `h(0) = 0`. Theorem 6.4.1 in case (i) therefore needs
  bounded rewards (`OCExistence`).
* `ExpCont P`: the conclusion of Lemma 6.4.1 (continuity and integrability of the sections) for
  the functions `f` with property `P`; `expCont_compact` (all `f`) and `expCont_countable`
  (bounded `f`) are the two cases. The later theorems are proved for any `P`.
-/

namespace Miao.Applications

open MeasureTheory ProbabilityTheory Filter Topology

variable {Z : Type*} [MeasurableSpace Z]

/-- SLP's Lemma 9.5(b) without the bound: if `Z` is compact and `Q` is Feller, then for every
continuous `f : W × Z → ℝ` the sections `f(w, ·)` are integrable and
`(w, z) ↦ ∫ f(w, z′) Q(z, dz′)` is continuous. -/
theorem continuous_mop_of_compact {W : Type*} [TopologicalSpace W] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [CompactSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {f : W × Z → ℝ} (hf : Continuous f) :
    Continuous (mop Q f) ∧ ∀ w z, Integrable (fun z' => f (w, z')) (Q z) := by
  have hsec : ∀ w, Continuous fun z' => f (w, z') := fun w => hf.comp (Continuous.prodMk_right w)
  have hbdd : ∀ w, ∃ B, ∀ z', |f (w, z')| ≤ B := fun w => by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (hsec w).continuousOn
    exact ⟨B, fun z' => by rw [← Real.norm_eq_abs]; exact hB z' (Set.mem_univ _)⟩
  have hint : ∀ w z, Integrable (fun z' => f (w, z')) (Q z) := fun w z =>
    integrable_of_abs_le (hsec w).measurable (hbdd w).choose_spec
  refine ⟨?_, hint⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨w, z⟩
  set g : C(W, C(Z, ℝ)) := (ContinuousMap.mk f hf).curry with hgdef
  set k : Z → ℝ := markovOpR Q fun z' => f (w, z') with hkdef
  have hk : Continuous k := hQ _ (hsec w) (hbdd w)
  have hdist : Tendsto (fun p : W × Z => dist (g p.1) (g w)) (𝓝 (w, z)) (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 ((g.continuous.tendsto w).comp continuous_fst.continuousAt)
  have hA : Tendsto (fun p : W × Z => mop Q f p - k p.2) (𝓝 (w, z)) (𝓝 0) := by
    refine squeeze_zero_norm (fun p => ?_) hdist
    rw [mop, hkdef, markovOpR, ← integral_sub (hint p.1 p.2) (hint w p.2)]
    have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := dist (g p.1) (g w))
      (f := fun z' => f (p.1, z') - f (w, z')) (Eventually.of_forall fun z' => by
        rw [← dist_eq_norm]
        exact ContinuousMap.dist_apply_le_dist (f := g p.1) (g := g w) z')
    simpa [measureReal_def] using this
  have hB' : Tendsto (fun p : W × Z => k p.2) (𝓝 (w, z)) (𝓝 (k z)) :=
    (hk.tendsto z).comp continuous_snd.continuousAt
  have hsum := hA.add hB'
  rw [zero_add] at hsum
  have heq : (fun p : W × Z => mop Q f p - k p.2 + k p.2) = mop Q f :=
    funext fun p => sub_add_cancel _ _
  rw [heq] at hsum
  exact hsum

namespace OCModel

variable {E F : Type*} (M : OCModel E F Z)

/-- The conclusion of Lemma 6.4.1 for the functions `f` with property `P`: the sections
`z′ ↦ f(φ(x, a, z, z′), z′)` are integrable and `h(x, a, z)` is continuous on `X × A × Z`. -/
def ExpCont [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace Z]
    (P : (E → Z → ℝ) → Prop) : Prop :=
  ∀ f, P f → ContinuousOn (fun p : E × Z => f p.1 p.2) (M.X ×ˢ Set.univ) →
    ContinuousOn (fun p : E × F × Z => M.cont f p.1 p.2.1 p.2.2) (M.X ×ˢ M.A ×ˢ Set.univ) ∧
      ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z, Integrable (fun z' => f (M.φ x a z z') z') (M.Q z)

/-- **Lemma 6.4.1** (Miao, p. 174), case (ii) of Assumption 6.4.3: if `Z` is compact and `Q`
is Feller, then for every continuous `f` on `X × Z` the function
`h(x, a, z) = ∫ f(φ(x, a, z, z′), z′) Q(z, dz′)` is continuous on `X × A × Z` (and its
integrands are integrable). No bound on `f` is needed. -/
theorem lemma_6_4_1_compact [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [CompactSpace Z] [IsMarkovKernel M.Q] (hQ : IsFeller M.Q)
    (h645 : M.Assumption645) {f : E → Z → ℝ}
    (hf : ContinuousOn (fun p : E × Z => f p.1 p.2) (M.X ×ˢ Set.univ)) :
    ContinuousOn (fun p : E × F × Z => M.cont f p.1 p.2.1 p.2.2) (M.X ×ˢ M.A ×ˢ Set.univ) ∧
      ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z, Integrable (fun z' => f (M.φ x a z z') z') (M.Q z) := by
  set S := M.X ×ˢ M.A ×ˢ (Set.univ : Set Z)
  -- the composite integrand on `S × Z`
  have hφc : Continuous fun q : S × Z => M.φ q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.2 := by
    refine h645.2.comp_continuous (Continuous.prodMk
      (continuous_subtype_val.comp continuous_fst).fst
      (Continuous.prodMk (continuous_subtype_val.comp continuous_fst).snd.fst
        (Continuous.prodMk (continuous_subtype_val.comp continuous_fst).snd.snd
          continuous_snd))) fun q => ?_
    exact ⟨q.1.2.1, q.1.2.2.1, Set.mem_univ _⟩
  have hψ : Continuous fun q : S × Z => f (M.φ q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.2) q.2 := by
    refine hf.comp_continuous (hφc.prodMk continuous_snd) fun q => ⟨?_, Set.mem_univ _⟩
    exact h645.1 _ q.1.2.1 _ q.1.2.2.1 _ _
  obtain ⟨hM, hint⟩ := continuous_mop_of_compact M.Q hQ hψ
  refine ⟨?_, fun x hx a ha z => hint ⟨(x, a, z), hx, ha, Set.mem_univ _⟩ z⟩
  rw [continuousOn_iff_continuous_domRestrict]
  exact hM.comp (continuous_id.prodMk (continuous_subtype_val.snd.snd))

/-- `ExpCont` holds for all functions in case (ii) of Assumption 6.4.3 (Lemma 6.4.1). -/
theorem expCont_compact [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [CompactSpace Z] [IsMarkovKernel M.Q] (hQ : IsFeller M.Q)
    (h645 : M.Assumption645) : M.ExpCont fun _ => True := fun _ _ hf =>
  M.lemma_6_4_1_compact hQ h645 hf

/-- **Lemma 6.4.1** (Miao, p. 174), case (i) of Assumption 6.4.3, for bounded `f`: if `Z` has the
discrete topology and all its subsets are measurable, then for every bounded continuous `f` on
`X × Z`, `h(x, a, z) = ∫ f(φ(x, a, z, z′), z′) Q(z, dz′)` is continuous on `X × A × Z`. The
proof applies SLP's Lemma 9.5′ (`lemma_9_5'`) with the action `(a, z)` and Lemma 9.5(a). -/
theorem lemma_6_4_1_countable [MetricSpace E] [MetricSpace F] [MetricSpace Z] [DiscreteTopology Z]
    [DiscreteMeasurableSpace Z] [IsMarkovKernel M.Q] (h645 : M.Assumption645) {f : E → Z → ℝ}
    (hf : ContinuousOn (fun p : E × Z => f p.1 p.2) (M.X ×ˢ Set.univ)) {B : ℝ}
    (hB : ∀ x ∈ M.X, ∀ z, |f x z| ≤ B) :
    ContinuousOn (fun p : E × F × Z => M.cont f p.1 p.2.1 p.2.2) (M.X ×ˢ M.A ×ˢ Set.univ) ∧
      ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z, Integrable (fun z' => f (M.φ x a z z') z') (M.Q z) := by
  -- SLP's state space `↥X`, action space `↥A × Z`, law of motion `φ′`
  let φ' : ↥M.X × (↥M.A × Z) × Z → ↥M.X := fun q =>
    ⟨M.φ q.1 q.2.1.1 q.2.1.2 q.2.2, h645.1 _ q.1.2 _ q.2.1.1.2 _ _⟩
  let f' : ↥M.X × Z → ℝ := fun p => f p.1 p.2
  have hf' : Continuous f' :=
    hf.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      fun p => ⟨p.1.2, Set.mem_univ _⟩
  have hφ' : ContinuousOn (fun q : (↥M.X × (↥M.A × Z)) × Z => φ' (q.1.1, q.1.2, q.2))
      (Set.univ ×ˢ Set.univ) := by
    refine Continuous.continuousOn (Continuous.subtype_mk ?_ _)
    refine h645.2.comp_continuous ((continuous_subtype_val.comp continuous_fst.fst).prodMk
      ((continuous_subtype_val.comp continuous_fst.snd.fst).prodMk
        (continuous_fst.snd.snd.prodMk continuous_snd))) fun q => ?_
    exact ⟨q.1.1.2, q.1.2.1.2, Set.mem_univ _⟩
  have hQ : PreservesBC (↥(Set.univ : Set (↥M.X × (↥M.A × Z)))) M.Q :=
    lemma_9_5_discrete M.Q
  have h95 := lemma_9_5' (Set.univ : Set (↥M.X × (↥M.A × Z))) hφ' M.Q hQ hf'
    (B := B) fun p => hB _ p.1.2 _
  refine ⟨?_, fun x hx a ha z => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hmap : Continuous fun w : ↥(M.X ×ˢ M.A ×ˢ (Set.univ : Set Z)) =>
        (((⟨w.1.1, w.2.1⟩ : ↥M.X), ((⟨w.1.2.1, w.2.2.1⟩ : ↥M.A), w.1.2.2)), w.1.2.2) := by
      refine Continuous.prodMk (Continuous.prodMk ?_ (Continuous.prodMk ?_
        continuous_subtype_val.snd.snd)) continuous_subtype_val.snd.snd
      · exact continuous_subtype_val.fst.subtype_mk _
      · exact continuous_subtype_val.snd.fst.subtype_mk _
    rw [continuousOn_iff_continuous_domRestrict] at h95
    exact h95.comp (hmap.subtype_mk fun _ => ⟨Set.mem_univ _, Set.mem_univ _⟩)
  · exact integrable_of_abs_le Measurable.of_discrete fun z' =>
      hB _ (h645.1 x hx a ha z z') z'

/-- `ExpCont` holds for the bounded functions in case (i) of Assumption 6.4.3 (Lemma 6.4.1). -/
theorem expCont_countable [MetricSpace E] [MetricSpace F] [MetricSpace Z] [DiscreteTopology Z]
    [DiscreteMeasurableSpace Z] [IsMarkovKernel M.Q] (h645 : M.Assumption645) :
    M.ExpCont fun f => ∃ B, ∀ x ∈ M.X, ∀ z, |f x z| ≤ B := fun _ ⟨_, hB⟩ hf =>
  M.lemma_6_4_1_countable h645 hf hB

end OCModel

/-- The tent `ψ(s) = max(0, 1 − |s − 1|)` used in the counterexample. -/
noncomputable def oc_tent (s : ℝ) : ℝ := max 0 (1 - |s - 1|)

/-- The unbounded continuous function of the counterexample:
`f(x, n) = 2^{n+1} ψ((n + 1)x)`. -/
noncomputable def oc_spike (x : ℝ) (n : ℕ) : ℝ := 2 ^ (n + 1) * oc_tent ((n + 1) * x)

theorem oc_tent_eq_zero {s : ℝ} (hs : s ≤ 0 ∨ 2 ≤ s) : oc_tent s = 0 := by
  have : 1 ≤ |s - 1| := by
    rcases hs with hs | hs
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp only [oc_tent]
  exact max_eq_left (by linarith)

theorem oc_tent_nonneg (s : ℝ) : 0 ≤ oc_tent s := le_max_left _ _

theorem oc_tent_le_one (s : ℝ) : oc_tent s ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg (s - 1)])

theorem oc_spike_bound (x : ℝ) (n : ℕ) : |oc_spike x n| ≤ 2 ^ (⌈2 / x⌉₊ + 1) := by
  rw [oc_spike, abs_of_nonneg (mul_nonneg (by positivity) (oc_tent_nonneg _))]
  rcases le_or_gt x 0 with hx | hx
  · rw [oc_tent_eq_zero (Or.inl (mul_nonpos_of_nonneg_of_nonpos (by positivity) hx))]
    simp
  rcases lt_or_ge n ⌈2 / x⌉₊ with hn | hn
  · calc (2 : ℝ) ^ (n + 1) * oc_tent ((n + 1) * x) ≤ 2 ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left (oc_tent_le_one _) (by positivity)
      _ ≤ 2 ^ (⌈2 / x⌉₊ + 1) := by
          rw [mul_one]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  · have h1 : 2 / x ≤ (n : ℝ) := (Nat.ceil_le.1 hn)
    have h2 : 2 ≤ ((n : ℝ) + 1) * x := by
      have := (div_le_iff₀ hx).1 h1
      nlinarith
    rw [oc_tent_eq_zero (Or.inr h2)]
    simp

/-- The success probability `1/2` of the geometric law in the counterexample. -/
noncomputable def oc_half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The model of the counterexample: `X = A = ℝ`, `Z = ℕ`, `Q(z, ·)` geometric with
`Q(z, {n}) = 2^{-(n+1)}`, `φ(x, a, z, z′) = x`. -/
noncomputable def oc_spikeModel : OCModel ℝ ℝ ℕ :=
  ⟨Set.univ, Set.univ, Kernel.const ℕ (geometricMeasure oc_half), fun _ _ => Set.univ,
    fun x _ _ _ => x, fun _ _ _ _ => 0, fun _ _ => 0, 1, 1⟩

/-- **Counterexample to Lemma 6.4.1 in case (i) for unbounded `f`** (Miao, p. 174). Take
`X = A = ℝ`, `Z = ℕ` with `Q(z, {n}) = 2^{-(n+1)}` (the geometric law), `φ(x, a, z, z′) = x` and
the continuous `f(x, n) = 2^{n+1} max(0, 1 − |(n + 1)x − 1|)`. Assumptions 6.4.1, 6.4.2, 6.4.3(i)
and 6.4.5 hold and every integrand is integrable (each `f(x, ·)` is bounded), but `h` is not
continuous: `h(1/(m+1), a, z) ≥ 1` for all `m` while `h(0, a, z) = 0`. -/
theorem lemma_6_4_1_countable_counterexample :
    ∃ (M : OCModel ℝ ℝ ℕ) (f : ℝ → ℕ → ℝ), IsMarkovKernel M.Q ∧ M.Assumption641 ∧
      M.Assumption642 ∧ OCModel.Assumption643i ℕ ∧ M.Assumption645 ∧
      ContinuousOn (fun p : ℝ × ℕ => f p.1 p.2) (M.X ×ˢ Set.univ) ∧
      (∀ x a z, Integrable (fun z' => f (M.φ x a z z') z') (M.Q z)) ∧
      ¬ ContinuousOn (fun p : ℝ × ℝ × ℕ => M.cont f p.1 p.2.1 p.2.2)
        (M.X ×ˢ M.A ×ˢ Set.univ) := by
  have hp : oc_half ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    norm_num [oc_half] at this
  have hQ : ∀ z, oc_spikeModel.Q z = geometricMeasure oc_half := fun z => Kernel.const_apply _ _
  have hint : ∀ x, Integrable (oc_spike x) (geometricMeasure oc_half) := fun x =>
    integrable_of_abs_le Measurable.of_discrete (oc_spike_bound x)
  have hcont : ∀ x a z, oc_spikeModel.cont oc_spike x a z =
      ∫ n, oc_spike x n ∂geometricMeasure oc_half := fun x a z => by
    simp only [OCModel.cont, hQ]
    rfl
  have hX : oc_spikeModel.X = Set.univ := rfl
  have hA : oc_spikeModel.A = Set.univ := rfl
  have h641 : oc_spikeModel.Assumption641 := ⟨(by rw [hX]; exact convex_univ),
    (by rw [hX]; exact MeasurableSet.univ)⟩
  have h642 : oc_spikeModel.Assumption642 := ⟨(by rw [hA]; exact convex_univ),
    (by rw [hA]; exact MeasurableSet.univ)⟩
  have h645 : oc_spikeModel.Assumption645 :=
    ⟨fun _ _ _ _ _ _ => by rw [hX]; exact Set.mem_univ _, continuous_fst.continuousOn⟩
  refine ⟨oc_spikeModel, oc_spike, ⟨fun z => by rw [hQ]; infer_instance⟩, h641, h642,
    ⟨inferInstance, inferInstance, inferInstance⟩, h645, ?_, fun x a z => by
      rw [hQ]; exact hint x, ?_⟩
  · refine Continuous.continuousOn (continuous_prod_of_discrete_right.2 fun n => ?_)
    simp only [oc_spike, oc_tent]
    fun_prop
  · intro hc
    rw [hX, hA, Set.univ_prod_univ, Set.univ_prod_univ, continuousOn_univ] at hc
    -- along `x_m = 1/(m+1) → 0`, `h(x_m) ≥ 1`, but `h(0) = 0`
    have h0 : Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 1), (0 : ℝ), (0 : ℕ))) atTop
        (𝓝 (0, 0, 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.prodMk_nhds tendsto_const_nhds
    have hlim := (hc.tendsto _).comp h0
    have hzero : oc_spikeModel.cont oc_spike 0 0 0 = 0 := by
      rw [hcont]
      have : ∀ n, oc_spike 0 n = 0 := fun n => by
        simp only [oc_spike, mul_zero, oc_tent_eq_zero (le_refl (0 : ℝ) |> Or.inl)]
      simp [this]
    have hone : ∀ m : ℕ, 1 ≤ oc_spikeModel.cont oc_spike (1 / ((m : ℝ) + 1)) 0 0 := fun m => by
      rw [hcont]
      have hle := setIntegral_le_integral (s := {m}) (hint (1 / ((m : ℝ) + 1)))
        (Eventually.of_forall fun n => mul_nonneg (by positivity) (oc_tent_nonneg _))
      rw [integral_singleton, geometricMeasure_real_singleton hp] at hle
      refine le_trans (le_of_eq ?_) hle
      have hm : ((m : ℝ) + 1) * (1 / ((m : ℝ) + 1)) = 1 := by field_simp
      simp only [oc_spike, hm, oc_tent, sub_self, abs_zero, sub_zero, oc_half, smul_eq_mul]
      rw [max_eq_right zero_le_one, mul_one, pow_succ]
      norm_num
      have : ((1 : ℝ) / 2) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
      linear_combination -this
    have := ge_of_tendsto hlim (Eventually.of_forall hone)
    simp only at this
    rw [hzero] at this
    norm_num at this

end Miao.Applications

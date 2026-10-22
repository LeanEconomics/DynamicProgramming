/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeometricErgodicity.GeometricSkeletons

/-!
# The Geometric Ergodic Theorem (MT §15.4, Theorem 15.0.1)

Meyn and Tweedie, Theorem 15.0.1 (pp. 362–363) and §15.4 (pp. 384–388). The state space is
countably generated and `ψ` is a maximal irreducibility measure.

**The split chain.** `M : Minorization P` splits the chain on `C`; `C̃ = C × {0, 1}`,
`α̌ = C × {1}` and `f̌(x, i) = f(x)`.
* `Minorization.lintegral_pathKernel_split`: path functionals of the first coordinate from a split
  initial law are those of the original chain.
* `Minorization.geomTaboo_split_le`: `Ǔ_{C̃}^{(r)}(z, f̌) ≤ ((1 − δ)⁻¹ + δ⁻¹) sup_C U_C^{(r)}(·, f)`
  on `C̃` (one step of the split chain moves by `R(x, ·) ≤ (1 − δ)⁻¹ P(x, ·)` or by
  `ν ≤ δ⁻¹ P(x, ·)`);
* `Minorization.measure_returnTimeK_one_lt_le`: every visit of the split chain to `C̃` lands in
  `α̌` with probability `δ`, so `P̌_z(τ_{C̃} < τ_{α̌}) ≤ 1 − δ`.
* `Minorization.tsum_fNorm_le_geom`: **the strongly aperiodic case** (the proof of
  Theorem 15.4.1 (ii)): if `U_C^{(r₀)}(·, f)` is bounded on `C`, then
  `Σ_{n ≥ 1} rⁿ ‖Pⁿ(x, ·) − π‖_f ≤ R (U_C^{(r₀)}(x, f) + 1)`: the geometric trials argument in the
  split chain makes `α̌` an `f̌`-Kendall atom, and the atom bound (15.18) passes to the marginal.

**Results.**
* `geometric_ergodic_of_driftV4` ((15.4)): for an aperiodic chain with (V4) for a petite set and
  `V` finite somewhere, the chain is positive, `π(V) < ∞`, and for some `r > 1`, `R < ∞`,
  `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_V ≤ R V(x)` for every `x`. The proof is step (iii) of Theorem 15.4.1: the
  skeleton satisfies (V4) (Theorem 15.3.4), is `V`-geometrically regular (Theorem 15.3.3), is split
  on a set where `V` is bounded, and Lemma 14.3.2 returns to the chain.
* **Theorem 15.4.1** (`theorem_15_4_1`, p. 384): a petite non-empty `f`-Kendall set `C` of rate
  `κ` gives `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f ≤ R G_C^{(κ)}(x, f)`, with `{G_C^{(κ)}(·, f) < ∞}` full and
  absorbing.
* **Theorem 15.4.3** (`theorem_15_4_3`, p. 387): local geometric convergence (15.47) of the
  `ν_C`-average on a small set gives geometric ergodicity on a full absorbing set.
* **Theorem 15.0.1** (`theorem_15_0_1`, p. 362), the Geometric Ergodic Theorem: (i) local
  geometric ergodicity (`IsLocallyGeomErgodic`), (ii) a petite Kendall set (`HasKendallPetite`)
  and (iii) (V4) (`HasDriftV4`) are equivalent. (ii) ⇒ (iii) is Theorem 15.2.4 with `f = 1`,
  (iii) ⇒ (ii) takes a sublevel set `{V ≤ ℓ}` (Theorems 15.2.5, 15.2.6), (iii) ⇒ (i) is
  `geometric_ergodic_of_driftV4` tested on `C`, and (i) ⇒ (ii)
  splits a skeleton on a set where (15.1) holds, makes the split atom Kendall (Theorem 15.1.5),
  builds (V4) for the skeleton from `x ↦ ∫ Ǧ dx*`, and returns to the chain through
  Theorems 15.3.3 and 15.3.6. The consequences (15.4) are `theorem_15_0_1_consequences`.

**Corrections.**
* Theorem 15.0.1 (ii) needs `C ≠ ∅`: the empty set is petite and Kendall for every chain
  (`theorem_15_0_1_counterexample`, the null recurrent forward recurrence time chain).
* Theorem 15.4.1: the bound is proved with `G_C^{(κ)}` (a sum up to `σ_C`), which implies the
  book's bound with a sum up to `τ_C`, since `σ_C ≤ τ_C`.
* Theorem 15.4.3: the book assumes a positive Harris chain; positivity is enough here.

The converse Theorem 15.4.2 is in `GeometricConverse` (atom case) and `GeometricConverseGeneral`.
-/

namespace MeynTweedie.GeometricErgodicity

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### Constant multiples -/

/-- `U_B^{(r)}(x, c f) = c U_B^{(r)}(x, f)`. -/
theorem geomTaboo_const_mul (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) (r c : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    geomTaboo P B r (fun y => c * f y) x = c * geomTaboo P B r f x := by
  rw [geomTaboo, geomTaboo, ← lintegral_const_mul c (measurable_sumBefore_geomTaboo hB r hf)]
  refine lintegral_congr fun ω => ?_
  rw [← sumBefore_const_mul]
  exact sumBefore_congr _ fun k _ => by ring

/-! ### The split chain -/

/-- **Path functionals of the first coordinate**: for a probability `μ` and measurable `H`,
`∫ μ*(dw) Ě_w[H(Φ̌.1)] = ∫ μ(dy) E_y[H(Φ)]`. -/
theorem Minorization.lintegral_pathKernel_split {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) (μ : Measure X) [IsProbabilityMeasure μ] {H : (ℕ → X) → ℝ≥0∞}
    (hH : Measurable H) :
    haveI := M.isMarkovKernel_splitKernel
    ∫⁻ w, ∫⁻ ω, H (fun n => (ω n).1) ∂pathKernel M.splitKernel w ∂M.split μ =
      ∫⁻ y, ∫⁻ ω, H ω ∂pathKernel P y ∂μ := by
  have := M.isMarkovKernel_splitKernel
  have hπ : Measurable fun (ω : ℕ → X × Bool) (n : ℕ) => (ω n).1 :=
    measurable_pi_iff.2 fun n => measurable_fst.comp (measurable_pi_apply n)
  calc ∫⁻ w, ∫⁻ ω, H (fun n => (ω n).1) ∂pathKernel M.splitKernel w ∂M.split μ
      = ∫⁻ ω, H (fun n => (ω n).1) ∂pathMeasure M.splitKernel (M.split μ) := by
        rw [pathMeasure_eq_comp, Measure.lintegral_bind (Kernel.aemeasurable _)
          (f := fun ω : ℕ → X × Bool => H (fun n => (ω n).1)) (hH.comp hπ).aemeasurable]
    _ = ∫⁻ ω, H ω ∂pathMeasure P μ := M.lintegral_split_fst μ hH
    _ = ∫⁻ y, ∫⁻ ω, H ω ∂pathKernel P y ∂μ := by
        rw [pathMeasure_eq_comp, Measure.lintegral_bind (Kernel.aemeasurable _) hH.aemeasurable]

/-- `Ǔ_{C̃}^{(r)}` and `E_·[r^{τ_{C̃}}]` from a split initial law. -/
theorem Minorization.lintegral_geomTaboo_split {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) (μ : Measure X) [IsProbabilityMeasure μ] {C : Set X}
    (hC : MeasurableSet C) (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) :
    haveI := M.isMarkovKernel_splitKernel
    ∫⁻ w, geomTaboo M.splitKernel (Prod.fst ⁻¹' C) r (fun w => f w.1) w ∂M.split μ =
      ∫⁻ y, geomTaboo P C r f y ∂μ :=
  M.lintegral_pathKernel_split μ (measurable_sumBefore_geomTaboo hC r hf)

/-- `E_·[r^{τ_{C̃}}]` from a split initial law (`r > 1`). -/
theorem Minorization.lintegral_kendallMoment_split {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) (μ : Measure X) [IsProbabilityMeasure μ] {C : Set X}
    (hC : MeasurableSet C) {r : ℝ≥0∞} (hr : 1 < r) :
    haveI := M.isMarkovKernel_splitKernel
    ∫⁻ w, kendallMoment M.splitKernel (Prod.fst ⁻¹' C) r w ∂M.split μ =
      ∫⁻ y, kendallMoment P C r y ∂μ :=
  M.lintegral_pathKernel_split μ (measurable_tpow_comp (measurableSet_lt_firstReturn hC) hr)

/-- **One step of the split chain**: `Ǔ_{C̃}^{(r)}(z, f̌) ≤ ((1 − δ)⁻¹ + δ⁻¹) K` for `z ∈ C̃`, when
`U_C^{(r)}(·, f) ≤ K` on `C`. -/
theorem Minorization.geomTaboo_split_le {P : Kernel X X} [IsMarkovKernel P] (M : Minorization P)
    (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) {K : ℝ≥0∞}
    (hK : ∀ y ∈ M.C, geomTaboo P M.C r f y ≤ K) {z : X × Bool} (hz : z.1 ∈ M.C) :
    haveI := M.isMarkovKernel_splitKernel
    geomTaboo M.splitKernel (Prod.fst ⁻¹' M.C) r (fun w => f w.1) z ≤
      ((1 - M.δ)⁻¹ + M.δ⁻¹) * K := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_baseK
  have hC := M.measurableSet_C
  have hCt : MeasurableSet (Prod.fst ⁻¹' M.C : Set (X × Bool)) := measurable_fst hC
  have hfs : Measurable fun w : X × Bool => f w.1 := hf.comp measurable_fst
  have hGm := measurable_geomG P hC r hf
  have hbase : ∫⁻ w, geomG M.splitKernel (Prod.fst ⁻¹' M.C) r (fun w => f w.1) w
      ∂M.splitKernel z = ∫⁻ y, geomG P M.C r f y ∂M.baseK z := by
    rw [M.splitKernel_apply z]
    exact M.lintegral_pathKernel_split (M.baseK z) (measurable_sumBefore_geomG hC r hf)
  rw [geomTaboo_eq M.splitKernel hCt r hfs z, hbase]
  obtain ⟨x, b⟩ := z
  have hx : x ∈ M.C := hz
  cases b
  · have hle : M.baseK (x, false) ≤ (1 - M.δ)⁻¹ • P x := by
      rw [M.baseK_apply_false]
      refine Measure.le_intro fun A hA _ => ?_
      rw [M.resid_apply, M.residMeas_apply_of_mem hx hA, Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl tsub_le_self
    calc r * ∫⁻ y, geomG P M.C r f y ∂M.baseK (x, false)
        ≤ r * ∫⁻ y, geomG P M.C r f y ∂((1 - M.δ)⁻¹ • P x) :=
          mul_le_mul' le_rfl (lintegral_mono' hle le_rfl)
      _ = (1 - M.δ)⁻¹ * geomTaboo P M.C r f x := by
          rw [lintegral_smul_measure, smul_eq_mul, geomTaboo_eq P hC r hf x]; ring
      _ ≤ ((1 - M.δ)⁻¹ + M.δ⁻¹) * K := mul_le_mul' le_self_add (hK x hx)
  · have hle : M.baseK (x, true) ≤ M.δ⁻¹ • P x := by
      rw [M.baseK_apply_true]
      refine Measure.le_intro fun A _ _ => ?_
      rw [Measure.smul_apply, smul_eq_mul]
      calc M.ν A = M.δ⁻¹ * (M.δ * M.ν A) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel M.δ_pos.ne' M.δ_ne_top, one_mul]
        _ ≤ M.δ⁻¹ * P x A := mul_le_mul' le_rfl (M.le_apply hx A)
    calc r * ∫⁻ y, geomG P M.C r f y ∂M.baseK (x, true)
        ≤ r * ∫⁻ y, geomG P M.C r f y ∂(M.δ⁻¹ • P x) :=
          mul_le_mul' le_rfl (lintegral_mono' hle le_rfl)
      _ = M.δ⁻¹ * geomTaboo P M.C r f x := by
          rw [lintegral_smul_measure, smul_eq_mul, geomTaboo_eq P hC r hf x]; ring
      _ ≤ ((1 - M.δ)⁻¹ + M.δ⁻¹) * K := mul_le_mul' le_add_self (hK x hx)

/-- **Each visit to `C̃` lands in `α̌` with probability `δ`**: `P̌_z(τ_{C̃} < τ_{α̌}) ≤ 1 − δ` for
every `z`. -/
theorem Minorization.measure_returnTimeK_one_lt_le {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) (z : X × Bool) :
    haveI := M.isMarkovKernel_splitKernel
    pathKernel M.splitKernel z
      {ω | returnTimeK (Prod.fst ⁻¹' M.C) 1 ω < firstReturn M.checkAlpha ω} ≤ 1 - M.δ := by
  have := M.isMarkovKernel_splitKernel
  have hC := M.measurableSet_C
  set A : Set (X × Bool) := Prod.fst ⁻¹' M.C with hA
  have hAm : MeasurableSet A := measurable_fst hC
  set B0 : Set (X × Bool) := M.C ×ˢ {false} with hB0
  have hB0m : MeasurableSet B0 := hC.prod (measurableSet_singleton false)
  have hstep : ∀ y, M.splitKernel y B0 = (1 - M.δ) * M.splitKernel y A := fun y => by
    rw [M.splitKernel_apply, M.split_apply_false _ hC, inter_self, inter_compl_self,
      measure_empty, add_zero, hA, M.split_fst_preimage _ hC]
  have htk : ∀ n y, tabooKernel M.splitKernel hAm n y B0 =
      (1 - M.δ) * tabooKernel M.splitKernel hAm n y A := fun n y => by
    rw [tabooKernel, Kernel.comp_apply' _ _ _ hB0m, Kernel.comp_apply' _ _ _ hAm,
      ← lintegral_const_mul _ (Kernel.measurable_coe _ hAm)]
    exact lintegral_congr fun w => hstep w
  have hsub : {ω | returnTimeK A 1 ω < firstReturn M.checkAlpha ω} ⊆
      ⋃ n : ℕ, ({ω : ℕ → X × Bool | ω (n + 1) ∈ B0} ∩
        {ω | WithTop.some (n + 1) ≤ firstReturn A ω}) := fun ω hω => by
    have hω' : firstReturn A ω < firstReturn M.checkAlpha ω := hω
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω'.ne_top
    have ht1 : 1 ≤ t := by
      have := one_le_firstReturn A ω; rw [← ht] at this; exact WithTop.coe_le_coe.1 this
    have hmem : ω t ∈ A := mem_of_firstReturn_eq ht.symm
    have hnot : ω t ∉ M.checkAlpha := fun h => by
      have := firstReturn_le_of_mem (A := M.checkAlpha) ht1 h
      rw [← ht] at hω'
      exact absurd (lt_of_lt_of_le hω' this) (lt_irrefl _)
    refine mem_iUnion.2 ⟨t - 1, ?_, ?_⟩
    · change ω (t - 1 + 1) ∈ B0
      rw [Nat.sub_add_cancel ht1]
      refine ⟨hmem, ?_⟩
      have : (ω t).2 ≠ true := fun h2 => hnot ⟨hmem, h2⟩
      simpa using this
    · change WithTop.some (t - 1 + 1) ≤ firstReturn A ω
      rw [Nat.sub_add_cancel ht1, ← ht]
  calc pathKernel M.splitKernel z {ω | returnTimeK A 1 ω < firstReturn M.checkAlpha ω}
      ≤ ∑' n : ℕ, pathKernel M.splitKernel z ({ω : ℕ → X × Bool | ω (n + 1) ∈ B0} ∩
          {ω | WithTop.some (n + 1) ≤ firstReturn A ω}) :=
        (measure_mono hsub).trans (measure_iUnion_le _)
    _ = ∑' n, (1 - M.δ) * tabooKernel M.splitKernel hAm n z A := tsum_congr fun n => by
        rw [← htk]; exact tabooProb_eq_tabooKernel M.splitKernel hAm n z hB0m
    _ = (1 - M.δ) * hitProb M.splitKernel A z := by
        rw [ENNReal.tsum_mul_left, hitProb_eq_tsum M.splitKernel hAm z]
    _ ≤ 1 - M.δ := mul_le_of_le_one_right' (hitProb_le_one _ _ _)

/-! ### The strongly aperiodic case -/

/-- **The strongly aperiodic geometric ergodic bound** (the proof of Theorem 15.4.1 (ii)). Let
the chain be positive with invariant probability `π`, `M` a minorization on `C ∈ B⁺(X)` with
`ν(C) > 0`, `f ≥ 1`, and suppose `U_C^{(r₀)}(·, f) ≤ K₀` on `C` for some `r₀ > 1`. Then for some
`r > 1` and `R < ∞`, `Σ_{n ≥ 0} r^{n+1} ‖Pⁿ⁺¹(x, ·) − π‖_f ≤ R (U_C^{(r₀)}(x, f) + 1)` for every
`x`. -/
theorem Minorization.tsum_fNorm_le_geom {P : Kernel X X} [IsMarkovKernel P] (M : Minorization P)
    {ψ : Measure X} (hpos : IsPositive P ψ) (hψC : 0 < ψ M.C) (hνC : 0 < M.ν M.C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {r₀ : ℝ≥0∞} (hr₀ : 1 < r₀) (hr₀' : r₀ ≠ ∞)
    {K₀ : ℝ≥0∞} (hK₀ : K₀ ≠ ∞) (hU : ∀ y ∈ M.C, geomTaboo P M.C r₀ f y ≤ K₀) :
    ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
      ∑' n, r ^ (n + 1) * fNorm f ((P ^ (n + 1) : Kernel X X) x) π ≤
        R * (geomTaboo P M.C r₀ f x + 1) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_splitK
  have hC := M.measurableSet_C
  obtain ⟨hposs, hatom, hπs, hinv⟩ := M.split_positive hpos hψC hπ
  obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hψC.ne'
  have ha : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  obtain ⟨hrep, hLa⟩ := atom_rep_of_invariant hatom ha hinv
  have hfs : Measurable fun w : X × Bool => f w.1 := hf.comp measurable_fst
  have hfs1 : ∀ w : X × Bool, 1 ≤ f w.1 := fun w => hf1 w.1
  have hAm : MeasurableSet (Prod.fst ⁻¹' M.C : Set (X × Bool)) := measurable_fst hC
  set c₁ := (1 - M.δ)⁻¹ + M.δ⁻¹ with hc₁
  have hc₁t : c₁ ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 M.one_sub_δ_ne_zero,
    ENNReal.inv_ne_top.2 M.δ_pos.ne'⟩
  have hUs : ∀ z ∈ (Prod.fst ⁻¹' M.C : Set (X × Bool)),
      geomTaboo M.splitKernel (Prod.fst ⁻¹' M.C) r₀ (fun w => f w.1) z ≤ c₁ * K₀ :=
    fun z hz => M.geomTaboo_split_le r₀ hf hU hz
  have hKs : ∀ z ∈ (Prod.fst ⁻¹' M.C : Set (X × Bool)),
      kendallMoment M.splitKernel (Prod.fst ⁻¹' M.C) r₀ z ≤ c₁ * K₀ := fun z hz =>
    (kendallMoment_le_geomTaboo _ _ hr₀.le hfs1 z).trans (hUs z hz)
  have hq : 1 - M.δ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero M.δ_pos.ne'
  obtain ⟨r₁, hr₁, hr₁₀, K, hK, hbd⟩ := geomTaboo_trials M.splitKernel M.measurableSet_checkAlpha
    hAm hfs hr₀ hr₀' (ENNReal.mul_ne_top hc₁t hK₀) (ENNReal.mul_ne_top hc₁t hK₀) hKs hUs le_rfl hq
    fun z _ => M.measure_returnTimeK_one_lt_le z
  have hr₁t : r₁ ≠ ∞ := ne_top_of_le_ne_top hr₀' hr₁₀
  have haA : (c, true) ∈ (Prod.fst ⁻¹' M.C : Set (X × Bool)) := hc
  have hUa : geomTaboo M.splitKernel M.checkAlpha r₁ (fun w => f w.1) (c, true) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (hbd (c, true))
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hc₁t hK₀) (hUs _ haA), ENNReal.mul_ne_top hK (ne_top_of_le_ne_top
        (ENNReal.mul_ne_top hc₁t hK₀) (hKs _ haA))⟩, hK⟩
  obtain ⟨r, hr, -, R, hR, hatomb⟩ := tsum_fNorm_le_geom_atom hatom.1 ha hrep hLa
    (M.isAperiodicLaw_entryLaw_checkAlpha hνC) hr₁ hr₁t hfs hfs1 hUa
  refine ⟨r, hr, R * (1 + K), ENNReal.mul_ne_top hR (ENNReal.add_ne_top.2
    ⟨ENNReal.one_ne_top, hK⟩), fun x => ?_⟩
  have hsd : M.split (Measure.dirac x) = M.splitK x := Measure.dirac_bind M.splitK.measurable x
  have := M.isProbabilityMeasure_split (Measure.dirac x)
  have hUmx := measurable_geomTaboo P hC r₀ hf
  have hKmx := measurable_kendallMoment P hC hr₀
  have hb := hatomb (M.split (Measure.dirac x))
  -- the split bound from `x*`
  have hint : ∫⁻ w, geomTaboo M.splitKernel M.checkAlpha r₁ (fun w => f w.1) w
      ∂M.split (Measure.dirac x) ≤ geomTaboo P M.C r₀ f x + K * kendallMoment P M.C r₀ x + K := by
    have hm1 := measurable_geomTaboo M.splitKernel hAm r₀ hfs
    have hm2 := measurable_kendallMoment M.splitKernel hAm hr₀
    calc ∫⁻ w, geomTaboo M.splitKernel M.checkAlpha r₁ (fun w => f w.1) w
          ∂M.split (Measure.dirac x)
        ≤ ∫⁻ w, (geomTaboo M.splitKernel (Prod.fst ⁻¹' M.C) r₀ (fun w => f w.1) w +
            K * kendallMoment M.splitKernel (Prod.fst ⁻¹' M.C) r₀ w + K)
            ∂M.split (Measure.dirac x) := lintegral_mono fun w => hbd w
      _ = ∫⁻ y, geomTaboo P M.C r₀ f y ∂Measure.dirac x +
            K * ∫⁻ y, kendallMoment P M.C r₀ y ∂Measure.dirac x + K := by
          rw [lintegral_add_right _ measurable_const, lintegral_add_left hm1,
            lintegral_const_mul _ hm2, lintegral_const, measure_univ, mul_one,
            M.lintegral_geomTaboo_split _ hC r₀ hf, M.lintegral_kendallMoment_split _ hC hr₀]
      _ = geomTaboo P M.C r₀ f x + K * kendallMoment P M.C r₀ x + K := by
          rw [lintegral_dirac' _ hUmx, lintegral_dirac' _ hKmx]
  have hKU : kendallMoment P M.C r₀ x ≤ geomTaboo P M.C r₀ f x :=
    kendallMoment_le_geomTaboo P M.C hr₀.le hf1 x
  calc ∑' n, r ^ (n + 1) * fNorm f ((P ^ (n + 1) : Kernel X X) x) π
      ≤ ∑' n, r ^ (n + 1) * fNorm (fun w : X × Bool => f w.1)
          ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ M.split (Measure.dirac x))
          (M.split π) := ENNReal.tsum_le_tsum fun n => by
        refine mul_le_mul' le_rfl ?_
        have h1 := fNorm_map_le measurable_fst f
          ((M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) ∘ₘ M.split (Measure.dirac x))
          (M.split π)
        rwa [split_comp_pow_map_fst, M.split_map_fst, dirac_kernel] at h1
    _ ≤ R * ∫⁻ w, geomTaboo M.splitKernel M.checkAlpha r₁ (fun w => f w.1) w
          ∂M.split (Measure.dirac x) := hb
    _ ≤ R * (geomTaboo P M.C r₀ f x + K * kendallMoment P M.C r₀ x + K) := mul_le_mul' le_rfl hint
    _ ≤ R * ((1 + K) * (geomTaboo P M.C r₀ f x + 1)) := by
        refine mul_le_mul' le_rfl ?_
        calc geomTaboo P M.C r₀ f x + K * kendallMoment P M.C r₀ x + K
            ≤ geomTaboo P M.C r₀ f x + K * geomTaboo P M.C r₀ f x + K :=
              add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hKU)) le_rfl
          _ ≤ (1 + K) * (geomTaboo P M.C r₀ f x + 1) := by
              calc geomTaboo P M.C r₀ f x + K * geomTaboo P M.C r₀ f x + K
                  ≤ geomTaboo P M.C r₀ f x + K * geomTaboo P M.C r₀ f x + (1 + K) :=
                    add_le_add le_rfl le_add_self
                _ = (1 + K) * (geomTaboo P M.C r₀ f x + 1) := by ring
    _ = R * (1 + K) * (geomTaboo P M.C r₀ f x + 1) := by ring

/-! ### The general aperiodic case -/

/-- The restriction of a minorization to a measurable subset `D ⊆ C`. -/
noncomputable def Minorization.restrict {P : Kernel X X} (M : Minorization P) {D : Set X}
    (hD : MeasurableSet D) (hDC : D ⊆ M.C) : Minorization P where
  C := D
  δ := M.δ
  ν := M.ν
  measurableSet_C := hD
  δ_pos := M.δ_pos
  δ_lt_one := M.δ_lt_one
  isProbabilityMeasure_ν := M.isProbabilityMeasure_ν
  le := fun x hx => M.le x (hDC hx)

/-- If `μ(C ∩ {V < ∞}) > 0`, then `μ(C ∩ {V ≤ n}) > 0` for all large `n`. -/
theorem eventually_measure_inter_sublevel_pos {μ : Measure X} {V : X → ℝ≥0∞} {C : Set X}
    (h : 0 < μ (C ∩ {x | V x ≠ ∞})) :
    ∀ᶠ n : ℕ in atTop, 0 < μ (C ∩ {x | V x ≤ n}) := by
  have hmono : Monotone fun n : ℕ => C ∩ {x | V x ≤ n} := fun m n hmn x hx =>
    ⟨hx.1, le_trans (show V x ≤ m from hx.2) (by exact_mod_cast hmn)⟩
  have hU : ⋃ n : ℕ, C ∩ {x | V x ≤ n} = C ∩ {x | V x ≠ ∞} := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    refine ⟨fun ⟨n, h1, h2⟩ => ⟨h1, ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) h2⟩,
      fun ⟨h1, h2⟩ => ?_⟩
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h2
    exact ⟨n, h1, hn.le⟩
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hU] at ht
  exact ht.eventually (lt_mem_nhds h)

/-- `μ(C ∩ S) = μ(C)` when `μ(Sᶜ) = 0`. -/
theorem measure_inter_of_compl_null {μ : Measure X} {C S : Set X} (hS : MeasurableSet S)
    (h : μ Sᶜ = 0) : μ (C ∩ S) = μ C := by
  refine le_antisymm (measure_mono inter_subset_left) ?_
  calc μ C ≤ μ (C ∩ S) + μ (C \ S) := by rw [measure_inter_add_sdiff _ hS]
    _ ≤ μ (C ∩ S) + 0 := add_le_add le_rfl (le_of_le_of_eq (measure_mono fun x hx => hx.2) h)
    _ = μ (C ∩ S) := add_zero _

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The geometric ergodic bound (15.4)** (MT Theorems 15.0.1 and 15.4.1, step (iii)): for an
aperiodic `ψ`-irreducible chain, if (V4) holds for `V ≥ 1`, a petite `C`, `ρ < 1` and `b < ∞`,
with `V` finite at some point, then the chain is positive, every invariant probability `π` has
`π(V) < ∞`, and for some `r > 1` and `R < ∞`, `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_V ≤ R V(x)` for every `x`. -/
theorem geometric_ergodic_of_driftV4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞)
    {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {x₀ : X} (hx₀ : V x₀ ≠ ∞) :
    IsPositive P ψ ∧ ∀ (π : Measure X) [IsProbabilityMeasure π], IsInvariant P π →
      ∫⁻ x, V x ∂π ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
        ∑' n, r ^ n * fNorm V ((P ^ n : Kernel X X) x) π ≤ R * V x := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hct : (1 - ρ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ).ne'
  obtain ⟨hpos, hπV⟩ := isPositive_of_driftV3 hψ hV hV1 hC (hV.const_mul _)
    (ENNReal.mul_ne_top hct hb) (ENNReal.mul_ne_top hct hx₀) (h.driftV3_scaled hV hρ)
  refine ⟨hpos, fun π _ hπ => ⟨hπV π inferInstance hπ, ?_⟩⟩
  have hπVt := hπV π inferInstance hπ
  -- the skeleton and its minorization
  obtain ⟨m, hm, M₀, hψC₀, hνC₀⟩ := exists_skeleton_minorization hψ hap
  have := isMarkovKernel_pow P m
  have hψQ : IsMaximalIrreducibility (P ^ m : Kernel X X) ψ :=
    ((proposition_5_4_5_iii P hψ hap).1 m hm).1
  have hposQ : IsPositive (P ^ m : Kernel X X) ψ := ⟨hψQ, π, inferInstance, hπ.pow m⟩
  obtain ⟨ρ', b', hρ', hb', C', hsmall, hdriftQ⟩ :=
    theorem_15_3_4_i hψ hap hV hV1 hρ hb hC h hm
  obtain ⟨k, ν', hsm⟩ := hsmall
  have hpetQ : IsPetite (P ^ m : Kernel X X) C' := ⟨_, _, proposition_5_5_3 hsm⟩
  obtain ⟨habsQ, hfullQ⟩ := lemma_15_2_2_i hψQ.2.1 hV hρ'.le hb' hdriftQ
  have hfull := hfullQ ⟨x₀, hx₀⟩
  set S := {x | V x ≠ ∞} with hSdef
  have hSm : MeasurableSet S := (measurableSet_singleton ∞).compl.preimage hV
  -- `ν` does not charge `{V = ∞}`
  have hψCS : ψ (M₀.C ∩ S) = ψ M₀.C := measure_inter_of_compl_null hSm hfull
  obtain ⟨y, hyC, hyS⟩ := nonempty_of_measure_ne_zero (hψCS.symm ▸ hψC₀.ne' :
    ψ (M₀.C ∩ S) ≠ 0)
  have hνS : M₀.ν Sᶜ = 0 := by
    have h1 : (P ^ m : Kernel X X) y Sᶜ = 0 := (prob_compl_eq_zero_iff hSm).2 (habsQ y hyS)
    have h2 := M₀.le_apply hyC Sᶜ
    rw [h1, nonpos_iff_eq_zero, mul_eq_zero] at h2
    exact h2.resolve_left M₀.δ_pos.ne'
  have hνCS : M₀.ν (M₀.C ∩ S) = M₀.ν M₀.C := measure_inter_of_compl_null hSm hνS
  obtain ⟨n, hnψ, hnν⟩ := ((eventually_measure_inter_sublevel_pos (hψCS.symm ▸ hψC₀)).and
    (eventually_measure_inter_sublevel_pos (hνCS.symm ▸ hνC₀))).exists
  have hDm : MeasurableSet (M₀.C ∩ {x | V x ≤ n}) :=
    M₀.measurableSet_C.inter (measurableSet_le hV measurable_const)
  set M₁ := M₀.restrict hDm inter_subset_left with hM₁
  have hM₁C : M₁.C = M₀.C ∩ {x | V x ≤ n} := rfl
  -- the skeleton is `V`-geometrically regular: `U_{C₁}^{(s)}(x, V) ≤ c V(x)`
  obtain ⟨-, hregQ⟩ := theorem_15_3_3 hψQ hV hV1 hρ' hb' hpetQ hdriftQ hx₀
  obtain ⟨s₀, hs₀, cB, hcB, hUB⟩ := hregQ M₁.C hDm hnψ
  set s := min s₀ 2 with hsdef
  have hs1 : 1 < s := lt_min hs₀ (by norm_num)
  have hst : s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top (min_le_right _ _)
  -- the function `V^{(m)}` of Lemma 14.3.2
  set W := fSkel P m V with hWdef
  have hWm : Measurable W := measurable_fSkel P m hV
  have hW1 : ∀ x, 1 ≤ W x := one_le_fSkel P hm hV hV1
  set c' := (m : ℝ≥0∞) * (1 + b * m) with hc'
  have hc't : c' ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top m)
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hb (ENNReal.natCast_ne_top m)⟩)
  have hWV : ∀ x, W x ≤ c' * V x := fSkel_le_of_driftV4 hV hV1 (fun _ => le_rfl) hρ.le hCm h m
  have hUW : ∀ x, geomTaboo (P ^ m : Kernel X X) M₁.C s W x ≤ c' * (cB * V x) := fun x => by
    calc geomTaboo (P ^ m : Kernel X X) M₁.C s W x
        ≤ geomTaboo (P ^ m : Kernel X X) M₁.C s (fun y => c' * V y) x :=
          geomTaboo_mono_f _ _ s hWV x
      _ = c' * geomTaboo (P ^ m : Kernel X X) M₁.C s V x := geomTaboo_const_mul _ hDm s c' hV x
      _ ≤ c' * (cB * V x) := mul_le_mul' le_rfl ((geomTaboo_mono_r _ _ (min_le_left _ _) V x).trans
          (hUB x))
  have hK₀ : ∀ x ∈ M₁.C, geomTaboo (P ^ m : Kernel X X) M₁.C s W x ≤ c' * (cB * n) :=
    fun x hx => (hUW x).trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hx.2))
  obtain ⟨r₂, hr₂, R₂, hR₂, hbdQ⟩ := M₁.tsum_fNorm_le_geom hposQ hnψ hnν (hπ.pow m) hWm hW1 hs1
    hst (ENNReal.mul_ne_top hc't (ENNReal.mul_ne_top hcB (ENNReal.natCast_ne_top n))) hK₀
  -- back to the chain
  obtain ⟨r, hr, hrt, hrr₂⟩ := exists_one_lt_pow_le hr₂ m
  have hrm : r ^ m ≠ ∞ := ENNReal.pow_ne_top hrt
  set πV := ∫⁻ x, V x ∂π with hπVdef
  set R := (m : ℝ≥0∞) * r ^ m * (c' + m * πV + R₂ * (c' * cB + 1)) with hRdef
  refine ⟨r, hr, hrt, R, ?_, fun x => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hrm)
      (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hc't, ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top m) hπVt⟩, ENNReal.mul_ne_top hR₂ (ENNReal.add_ne_top.2
          ⟨ENNReal.mul_ne_top hc't hcB, ENNReal.one_ne_top⟩)⟩)
  set F : ℕ → ℝ≥0∞ := fun j => fNorm W (((P ^ m : Kernel X X) ^ j : Kernel X X) x) π with hFdef
  have hblock : ∀ j, ∑ i ∈ range m, r ^ (m * j + i) * fNorm V ((P ^ (m * j + i) : Kernel X X) x) π
      ≤ m * ((r ^ m) ^ (j + 1) * F j) := fun j => by
    calc ∑ i ∈ range m, r ^ (m * j + i) * fNorm V ((P ^ (m * j + i) : Kernel X X) x) π
        ≤ ∑ _i ∈ range m, (r ^ m) ^ (j + 1) * F j := Finset.sum_le_sum fun i hi => by
          have hi' := Finset.mem_range.1 hi
          refine mul_le_mul' ?_ ?_
          · rw [← pow_mul]
            exact pow_le_pow_right₀ hr.le (by rw [Nat.mul_succ]; omega)
          · have h1 := lemma_14_3_2_i_measure hπ hi' j V (Measure.dirac x)
            rw [dirac_kernel, dirac_kernel, show j * m + i = m * j + i by ring,
              show j * m = m * j by ring] at h1
            rw [hFdef]
            simp only
            rwa [← pow_mul]
      _ = m * ((r ^ m) ^ (j + 1) * F j) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hF0 : F 0 ≤ c' * V x + m * πV := by
    change fNorm W ((((P ^ m : Kernel X X) ^ 0 : Kernel X X)) x) π ≤ _
    rw [pow_zero_apply]
    refine (fNorm_le_add _ _ _).trans (add_le_add ?_ (le_of_eq (lintegral_fSkel P hπ m hV)))
    rw [lintegral_dirac' _ hWm]
    exact hWV x
  have htail : ∑' j, (r ^ m) ^ (j + 2) * F (j + 1) ≤ r ^ m * (R₂ * (c' * (cB * V x) + 1)) := by
    calc ∑' j, (r ^ m) ^ (j + 2) * F (j + 1)
        ≤ ∑' j, r ^ m * (r₂ ^ (j + 1) * F (j + 1)) := ENNReal.tsum_le_tsum fun j => by
          rw [pow_succ', mul_assoc]
          exact mul_le_mul' le_rfl (mul_le_mul' (pow_le_pow_left₀ zero_le hrr₂ _) le_rfl)
      _ = r ^ m * ∑' j, r₂ ^ (j + 1) * F (j + 1) := ENNReal.tsum_mul_left
      _ ≤ r ^ m * (R₂ * (c' * (cB * V x) + 1)) := by
          refine mul_le_mul' le_rfl ((le_of_eq ?_).trans ((hbdQ x).trans
            (mul_le_mul' le_rfl (add_le_add (hUW x) le_rfl))))
          exact tsum_congr fun j => rfl
  calc ∑' n, r ^ n * fNorm V ((P ^ n : Kernel X X) x) π
      = ∑' j, ∑ i ∈ range m, r ^ (m * j + i) * fNorm V ((P ^ (m * j + i) : Kernel X X) x) π :=
        tsum_eq_tsum_sum_block (fun n => r ^ n * fNorm V ((P ^ n : Kernel X X) x) π) hm
    _ ≤ ∑' j, m * ((r ^ m) ^ (j + 1) * F j) := ENNReal.tsum_le_tsum hblock
    _ = m * ((r ^ m) ^ (0 + 1) * F 0 + ∑' j, (r ^ m) ^ (j + 1 + 1) * F (j + 1)) := by
        rw [ENNReal.tsum_mul_left, tsum_eq_zero_add' ENNReal.summable]
    _ ≤ m * (r ^ m * (c' * V x + m * πV) + r ^ m * (R₂ * (c' * (cB * V x) + 1))) := by
        rw [zero_add, pow_one]
        exact mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hF0) htail)
    _ ≤ m * (r ^ m * ((c' + m * πV) * V x) + r ^ m * (R₂ * ((c' * cB + 1) * V x))) := by
        refine mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl ?_)
          (mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)))
        · rw [add_mul]; exact add_le_add le_rfl (le_mul_of_one_le_right' (hV1 x))
        · calc c' * (cB * V x) + 1 ≤ c' * (cB * V x) + V x := add_le_add le_rfl (hV1 x)
            _ = (c' * cB + 1) * V x := by ring
    _ = R * V x := by rw [hRdef]; ring

/-! ### Theorem 15.4.1 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.4.1** (MT p. 384): for a `ψ`-irreducible aperiodic chain with a petite,
non-empty `f`-Kendall set `C` of rate `κ` (`f ≥ 1`), with `V = G_C^{(κ)}(·, f)` of (15.40), the set
`S_f^κ = {V < ∞}` is full and absorbing, the chain is positive, every invariant probability has
`π(f) < ∞`, and for some `r > 1`, `R < ∞`, `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f ≤ R V(x)` for every `x`.
The book's bound `R E_x[Σ_{k=0}^{τ_C} f(Φ_k) κᵏ]` is weaker, since `σ_C ≤ τ_C`. -/
theorem theorem_15_4_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) {C : Set X} (hC : IsPetite P C)
    (hne : C.Nonempty) {κ : ℝ≥0∞} (hK : IsFKendall P f C κ) :
    IsFull ψ {x | geomG P C κ f x ≠ ∞} ∧ IsAbsorbing P {x | geomG P C κ f x ≠ ∞} ∧
      IsPositive P ψ ∧ ∀ (π : Measure X) [IsProbabilityMeasure π], IsInvariant P π →
        ∫⁻ x, f x ∂π ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
          ∑' n, r ^ n * fNorm f ((P ^ n : Kernel X X) x) π ≤ R * geomG P C κ f x := by
  obtain ⟨M, hM, hdrift, hfV, hVC⟩ := theorem_15_2_4 hf hf1 hK
  obtain ⟨hCm, hκ, -, -⟩ := hK
  have hVm := measurable_geomG P hCm κ hf
  have hV1 : ∀ x, 1 ≤ geomG P C κ f x := fun x => (hf1 x).trans (hfV x)
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hκ).ne'
  have hρ : κ⁻¹ < 1 := ENNReal.inv_lt_one.2 hκ
  have hb : κ⁻¹ * M ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hκ0) hM
  obtain ⟨x₀, hx₀⟩ := hne
  have hfin : geomG P C κ f x₀ ≠ ∞ := ne_top_of_le_ne_top hM (hVC x₀ hx₀)
  obtain ⟨habs, hfull⟩ := lemma_15_2_2_i hψ.2.1 hVm hρ.le hb hdrift
  obtain ⟨hpos, hgeo⟩ := geometric_ergodic_of_driftV4 hψ hap hVm hV1 hρ hb hC hdrift hfin
  refine ⟨hfull ⟨x₀, hfin⟩, habs, hpos, fun π _ hπ => ?_⟩
  obtain ⟨hπV, r, hr, -, R, hR, hbd⟩ := hgeo π hπ
  refine ⟨ne_top_of_le_ne_top hπV (lintegral_mono hfV), r, hr, R, hR, fun x => ?_⟩
  exact (ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl (fNorm_mono hfV _ _)).trans (hbd x)

/-! ### Theorem 15.0.1 -/

/-- **Condition (i) of Theorem 15.0.1** (15.1): the chain is positive and some petite `C ∈ B⁺(X)`
has `|Pⁿ(x, C) − P^∞(C)| ≤ M_C ρ_Cⁿ` for `x ∈ C`, with `ρ_C < 1` and `P^∞(C) > 0`. -/
def IsLocallyGeomErgodic (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) : Prop :=
  IsPositive P ψ ∧ ∃ C, IsPetite P C ∧ 0 < ψ C ∧ ∃ ρ M p : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ 0 < p ∧
    ∀ x ∈ C, ∀ n, |((P ^ n : Kernel X X) x C).toReal - p| ≤ M * ρ ^ n

/-- **Condition (ii) of Theorem 15.0.1** (15.2), corrected: a petite, **non-empty** Kendall set. -/
def HasKendallPetite (P : Kernel X X) [IsMarkovKernel P] : Prop :=
  ∃ C, IsPetite P C ∧ C.Nonempty ∧ IsKendallSet P C

/-- **Condition (iii) of Theorem 15.0.1** (15.3): (V4) for a petite set and a `V ≥ 1` finite at
some point. -/
def HasDriftV4 (P : Kernel X X) : Prop :=
  ∃ V : X → ℝ≥0∞, Measurable V ∧ (∀ x, 1 ≤ V x) ∧ (∃ x₀, V x₀ ≠ ∞) ∧
    ∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧ ∃ C, IsPetite P C ∧ DriftV4 P V ρ b C

/-- A Kendall set of rate `κ` is `1`-Kendall of rate `κ`. -/
theorem IsKendall.isFKendall_one {P : Kernel X X} [IsMarkovKernel P] {A : Set X} {κ : ℝ≥0∞}
    (h : IsKendall P A κ) : IsFKendall P (fun _ => 1) A κ := by
  obtain ⟨hA, hκ, hκ', M, hM, hb⟩ := h
  have hκ1 : κ - 1 ≠ 0 := (tsub_pos_iff_lt.2 hκ).ne'
  have hκ1t : κ - 1 ≠ ∞ := ENNReal.sub_ne_top hκ'
  refine ⟨hA, hκ, hκ', (κ - 1)⁻¹ * M, ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hκ1) hM,
    fun x hx => ?_⟩
  have h1 := kendallMoment_eq_one_add P hA hκ x
  calc geomSum P A κ (fun _ => 1) x
      = (κ - 1)⁻¹ * ((κ - 1) * geomSum P A κ (fun _ => 1) x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hκ1 hκ1t, one_mul]
    _ ≤ (κ - 1)⁻¹ * kendallMoment P A κ x := mul_le_mul' le_rfl (h1 ▸ le_add_self)
    _ ≤ (κ - 1)⁻¹ * M := mul_le_mul' le_rfl (hb x hx)

/-- **(ii) ⇒ (iii)** (Theorem 15.2.4 with `f = 1`): `V = G_C^{(κ)}(·, 1)` solves (V4). -/
theorem hasDriftV4_of_hasKendallPetite {P : Kernel X X} [IsMarkovKernel P]
    (h : HasKendallPetite P) : HasDriftV4 P := by
  obtain ⟨C, hC, ⟨x₀, hx₀⟩, κ, hK⟩ := h
  have hK1 := hK.isFKendall_one
  obtain ⟨M, hM, hdrift, hfV, hVC⟩ := theorem_15_2_4 measurable_const (fun _ => le_rfl) hK1
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hK.2.1).ne'
  exact ⟨geomG P C κ (fun _ => 1), measurable_geomG P hK.1 κ measurable_const, hfV,
    ⟨x₀, ne_top_of_le_ne_top hM (hVC x₀ hx₀)⟩, κ⁻¹, κ⁻¹ * M, ENNReal.inv_lt_one.2 hK.2.1,
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hκ0) hM, C, hC, hdrift⟩

/-- **(iii) ⇒ (ii)** (Theorem 15.2.6): a sublevel set `D` of `V` in `B⁺(X)` is a petite Kendall
set. -/
theorem hasKendallPetite_of_hasDriftV4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (h : HasDriftV4 P) : HasKendallPetite P := by
  obtain ⟨V, hV, hV1, ⟨x₀, hx₀⟩, ρ, b, hρ, hb, C, hC, hdrift⟩ := h
  obtain ⟨ℓ, hℓt, -, hψD, hpet, -, s, hs1, hst, d, hd, hbd⟩ :=
    exists_kendall_sublevel hψ hV hV1 hρ hb hC hdrift hx₀ ENNReal.one_ne_top
  have hDm : MeasurableSet {x | V x ≤ ℓ} := measurableSet_le hV measurable_const
  refine ⟨{x | V x ≤ ℓ}, hpet, nonempty_of_measure_ne_zero hψD.ne', s, hDm, hs1, hst,
    1 + (s - 1) * (d * ℓ), ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
      (ENNReal.sub_ne_top hst) (ENNReal.mul_ne_top hd hℓt)⟩, fun x hx => ?_⟩
  exact (kendallMoment_le_one_add P hDm hs1 hV1 x).trans (add_le_add le_rfl
    (mul_le_mul' le_rfl ((hbd x).trans (mul_le_mul' le_rfl hx))))

/-- A set `A` gives the test function `1_A` for `‖·‖_f`, `f ≥ 1`:
`|μ(A) − ν(A)| ≤ ‖μ − ν‖_f` for finite measures. -/
theorem ofReal_abs_measureReal_sub_le_fNorm {f : X → ℝ≥0∞} (hf1 : ∀ x, 1 ≤ f x)
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set X}
    (hA : MeasurableSet A) :
    ENNReal.ofReal |μ.real A - ν.real A| ≤ fNorm f μ ν := by
  have hg : IsFTest f μ ν (A.indicator 1) := by
    refine ⟨measurable_one.indicator hA, fun x => ?_, (integrable_const 1).indicator hA,
      (integrable_const 1).indicator hA⟩
    refine le_trans ?_ (hf1 x)
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, Pi.one_apply, abs_one, ENNReal.ofReal_one]
    · rw [indicator_of_notMem hx, abs_zero, ENNReal.ofReal_zero]; exact zero_le
  have h := ofReal_abs_integral_sub_le_fNorm hg
  rwa [integral_indicator_one hA, integral_indicator_one hA] at h

variable [MeasurableSpace.CountablyGenerated X] in
/-- **(iii) ⇒ (i)** (MT p. 363): under (V4), a sublevel set `D` of `V` in `B⁺(X)` has
`|Pⁿ(x, D) − π(D)| ≤ ‖Pⁿ(x, ·) − π‖_V ≤ R ℓ r⁻ⁿ` on `D`, with `π(D) > 0`. -/
theorem isLocallyGeomErgodic_of_hasDriftV4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) (h : HasDriftV4 P) :
    IsLocallyGeomErgodic P ψ := by
  obtain ⟨V, hV, hV1, ⟨x₀, hx₀⟩, ρ, b, hρ, hb, C, hC, hdrift⟩ := h
  obtain ⟨ℓ, hℓt, -, hψD, hpet, -⟩ :=
    exists_kendall_sublevel hψ hV hV1 hρ hb hC hdrift hx₀ ENNReal.one_ne_top
  obtain ⟨hpos, hgeo⟩ := geometric_ergodic_of_driftV4 hψ hap hV hV1 hρ hb hC hdrift hx₀
  obtain ⟨-, π, hπp, hπ⟩ := id hpos
  obtain ⟨-, r, hr, hrt, R, hR, hbd⟩ := hgeo π hπ
  set D := {x | V x ≤ ℓ} with hDdef
  have hDm : MeasurableSet D := measurableSet_le hV measurable_const
  have hrec := proposition_10_1_1 hpos
  have hequiv := theorem_10_4_9_equiv hrec ⟨inferInstance, hπ⟩ (IsProbabilityMeasure.ne_zero π)
  have hπD : π D ≠ 0 := fun h0 => hψD.ne' (hequiv.2 h0)
  have hr1 : 1 < r.toReal := by
    have := ENNReal.toReal_strict_mono hrt hr; rwa [ENNReal.toReal_one] at this
  refine ⟨hpos, D, hpet, hψD, r.toReal⁻¹, (R * ℓ).toReal, (π D).toReal, by positivity,
    inv_lt_one_of_one_lt₀ hr1, ENNReal.toReal_pos hπD (measure_ne_top π D), fun x hx n => ?_⟩
  have := isMarkovKernel_pow P n
  have h1 : r ^ n * ENNReal.ofReal |((P ^ n : Kernel X X) x D).toReal - (π D).toReal| ≤
      R * ℓ := by
    calc r ^ n * ENNReal.ofReal |((P ^ n : Kernel X X) x D).toReal - (π D).toReal|
        ≤ r ^ n * fNorm V ((P ^ n : Kernel X X) x) π :=
          mul_le_mul' le_rfl (ofReal_abs_measureReal_sub_le_fNorm hV1 hDm)
      _ ≤ ∑' k, r ^ k * fNorm V ((P ^ k : Kernel X X) x) π :=
          ENNReal.le_tsum (f := fun k => r ^ k * fNorm V ((P ^ k : Kernel X X) x) π) n
      _ ≤ R * V x := hbd x
      _ ≤ R * ℓ := mul_le_mul' le_rfl hx
  have hrn0 : r ^ n ≠ 0 := pow_ne_zero _ (zero_lt_one.trans hr).ne'
  have hrnt : r ^ n ≠ ∞ := ENNReal.pow_ne_top hrt
  have h2 : ENNReal.ofReal |((P ^ n : Kernel X X) x D).toReal - (π D).toReal| ≤
      R * ℓ * (r ^ n)⁻¹ := by
    calc ENNReal.ofReal |((P ^ n : Kernel X X) x D).toReal - (π D).toReal|
        = (r ^ n)⁻¹ * (r ^ n * ENNReal.ofReal |((P ^ n : Kernel X X) x D).toReal -
            (π D).toReal|) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hrn0 hrnt, one_mul]
      _ ≤ (r ^ n)⁻¹ * (R * ℓ) := mul_le_mul' le_rfl h1
      _ = R * ℓ * (r ^ n)⁻¹ := mul_comm _ _
  have hRℓ : R * ℓ ≠ ∞ := ENNReal.mul_ne_top hR hℓt
  have h3 := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hRℓ
    (ENNReal.inv_ne_top.2 hrn0))).1 h2
  rwa [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ← inv_pow] at h3

/-! ### From local geometric convergence to a Kendall atom (Theorem 15.4.3) -/

/-- The renewal sequence of the split atom: `P̌ⁿ⁺¹(α̌, α̌) = δ ∫ ν(dx) Pⁿ(x, C)`. -/
theorem Minorization.atomRenewal_split_succ {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) (c : X) (n : ℕ) :
    atomRenewal M.splitKernel M.checkAlpha (c, true) (n + 1) =
      (M.δ * ∫⁻ x, (P ^ n : Kernel X X) x M.C ∂M.ν).toReal := by
  rw [atomRenewal, M.splitKernel_pow_succ_apply, Minorization.checkAlpha,
    M.split_apply_true _ M.measurableSet_C, inter_self, M.baseK_apply_true,
    Measure.bind_apply M.measurableSet_C (Kernel.aemeasurable _)]

/-- **Local geometric convergence makes the split atom Kendall** (the proof of Theorem 15.4.3):
for a positive chain with a minorization on `C ∈ B⁺(X)`, `ν(C) > 0`, if
`|∫ ν(dx) Pⁿ(x, C) − p| ≤ K ρⁿ` with `ρ < 1`, then `α̌` is geometrically ergodic,
hence (Kendall's theorem, Theorem 15.1.5) a Kendall atom of some rate `κ > 1`. -/
theorem Minorization.isKendall_split_of_local {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) {ψ : Measure X} (hpos : IsPositive P ψ) (hψC : 0 < ψ M.C)
    (hνC : 0 < M.ν M.C) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {p ρ K : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hloc : ∀ n, |(∫⁻ x, (P ^ n : Kernel X X) x M.C ∂M.ν).toReal - p| ≤ K * ρ ^ n) :
    haveI := M.isMarkovKernel_splitKernel
    ∃ κ, IsKendall M.splitKernel M.checkAlpha κ := by
  have := M.isMarkovKernel_splitKernel
  obtain ⟨hposs, hatom, hπs, hinv⟩ := M.split_positive hpos hψC hπ
  obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hψC.ne'
  have ha : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  obtain ⟨hrep, hLa⟩ := atom_rep_of_invariant hatom ha hinv
  set δR := M.δ.toReal with hδR
  have hδR0 : 0 ≤ δR := ENNReal.toReal_nonneg
  have hI : ∀ n, ∫⁻ x, (P ^ n : Kernel X X) x M.C ∂M.ν ≠ ∞ := fun n => by
    have := isMarkovKernel_pow P n
    have := M.isProbabilityMeasure_ν
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∫⁻ x, (P ^ n : Kernel X X) x M.C ∂M.ν ≤ ∫⁻ _, 1 ∂M.ν := lintegral_mono fun x =>
          prob_le_one
      _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
  set u := atomRenewal M.splitKernel M.checkAlpha (c, true) with hu
  have hus : ∀ n, |u (n + 1) - δR * p| ≤ δR * K * ρ ^ n := fun n => by
    rw [hu, M.atomRenewal_split_succ, ENNReal.toReal_mul, ← mul_sub, abs_mul, abs_of_nonneg hδR0,
      mul_assoc]
    exact mul_le_mul_of_nonneg_left (hloc n) hδR0
  -- the two limits agree
  have hlim1 : Tendsto u atTop (𝓝 (δR * p)) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (Real.norm_eq_abs _).le.trans (hus n)) ?_)
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul (δR * K)
    rwa [mul_zero] at this
  have hlim2 := tendsto_atomRenewal_of_aperiodicLaw hatom.1 ha hrep hLa
    (M.isAperiodicLaw_entryLaw_checkAlpha hνC)
  have hceq : δR * p = (M.split π M.checkAlpha).toReal := tendsto_nhds_unique hlim1 hlim2
  -- geometric ergodicity of the atom
  set rg := 2 / (1 + ρ) with hrg
  have hrg1 : 1 < rg := by rw [hrg, lt_div_iff₀ (by linarith)]; linarith
  have hρrg : ρ * rg < 1 := by rw [hrg, mul_div_assoc', div_lt_one (by linarith)]; linarith
  have hrg0 : 0 ≤ rg := by linarith
  have hge : IsGeomErgodicAtom M.splitKernel (M.split π) M.checkAlpha := by
    refine ⟨rg, hrg1, fun a' ha' => ?_⟩
    have he : atomRenewal M.splitKernel M.checkAlpha a' = u :=
      funext fun n => hatom.1.atomRenewal_eq ha' ha n
    rw [he, ← hceq, ← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg hrg0 _))
      (fun n => ?_) ((summable_geometric_of_lt_one (mul_nonneg hρ0 hrg0) hρrg).mul_left
        (δR * K * rg))
    calc |u (n + 1) - δR * p| * rg ^ (n + 1) ≤ δR * K * ρ ^ n * rg ^ (n + 1) :=
          mul_le_mul_of_nonneg_right (hus n) (pow_nonneg hrg0 _)
      _ = δR * K * rg * (ρ * rg) ^ n := by rw [mul_pow, pow_succ]; ring
  obtain ⟨κ, hκ, hκt, hfull, -, -⟩ := theorem_15_1_5 hatom hinv hge
  -- a point of `α̌` with a finite Kendall moment
  have hSm : MeasurableSet {z | kendallMoment M.splitKernel M.checkAlpha κ z ≠ ∞} :=
    (measurableSet_singleton ∞).compl.preimage
      (measurable_kendallMoment _ M.measurableSet_checkAlpha hκ)
  have hint := measure_inter_of_compl_null (C := M.checkAlpha) hSm hfull
  obtain ⟨z₀, hz₀α, hz₀⟩ := nonempty_of_measure_ne_zero (hint.symm ▸ hatom.2.2.ne' :
    M.split ψ (M.checkAlpha ∩ {z | kendallMoment M.splitKernel M.checkAlpha κ z ≠ ∞}) ≠ 0)
  have hU0 : geomTaboo M.splitKernel M.checkAlpha κ (fun _ => 1) z₀ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hκt (ENNReal.inv_ne_top.2
      (tsub_pos_iff_lt.2 hκ).ne')) hz₀) (geomTaboo_one_le_kendallMoment _
        M.measurableSet_checkAlpha hκ hκt z₀)
  refine ⟨κ, M.measurableSet_checkAlpha, hκ, hκt, _, hU0, fun z hz => ?_⟩
  exact (kendallMoment_le_geomTaboo _ _ hκ.le (fun _ => le_rfl) z).trans (le_of_eq
    (hatom.1.geomTaboo_const κ measurable_const hz hz₀α))

/-- `1^{(m)} = m`. -/
theorem fSkel_one_const (P : Kernel X X) [IsMarkovKernel P] (m : ℕ) (x : X) :
    fSkel P m (fun _ => 1) x = m := by
  unfold fSkel
  have h : ∀ i, ∫⁻ _, (1 : ℝ≥0∞) ∂(P ^ i : Kernel X X) x = 1 := fun i => by
    have := isMarkovKernel_pow P i
    rw [lintegral_const, measure_univ, one_mul]
  simp_rw [h]
  simp

/-- **(V4) for the chain from a Kendall split atom**: if `α̌` is a Kendall atom of the split chain
(`C ≠ ∅`), `V(x) = ∫ x*(dz) Ǧ_{α̌}^{(κ)}(z, 1)` solves (V4) for the chain with the set `C`, `V ≥ 1`,
and `V` is finite at some point. -/
theorem Minorization.driftV4_of_isKendall_split {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (hne : M.C.Nonempty)
    {κ : ℝ≥0∞}
    (hK : haveI := M.isMarkovKernel_splitKernel; IsKendall M.splitKernel M.checkAlpha κ) :
    ∃ V : X → ℝ≥0∞, Measurable V ∧ (∀ x, 1 ≤ V x) ∧ (∃ x₀, V x₀ ≠ ∞) ∧
      ∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧ DriftV4 P V ρ b M.C := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_splitK
  have hC := M.measurableSet_C
  have hK1 := hK.isFKendall_one
  obtain ⟨Mv, hMv, hdrift, hfV, -⟩ := theorem_15_2_4 measurable_const (fun _ => le_rfl) hK1
  obtain ⟨hαm, hκ, -, -⟩ := hK
  set W := geomG M.splitKernel M.checkAlpha κ (fun _ => 1) with hWdef
  have hWm : Measurable W := measurable_geomG _ hαm κ measurable_const
  have hκ0 : κ ≠ 0 := (zero_lt_one.trans hκ).ne'
  have hbt : κ⁻¹ * Mv ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hκ0) hMv
  refine ⟨fun x => ∫⁻ z, W z ∂M.splitK x, hWm.lintegral_kernel, fun x => ?_, ?_, κ⁻¹, κ⁻¹ * Mv,
    ENNReal.inv_lt_one.2 hκ, hbt, fun x => ?_⟩
  · calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂M.splitK x := by rw [lintegral_const, measure_univ, one_mul]
      _ ≤ ∫⁻ z, W z ∂M.splitK x := lintegral_mono fun z => hfV z
  · -- `W < ∞` off a `ψ*`-null set `N`, and `x*(N) = 0` for `ψ`-a.e. `x`
    obtain ⟨c, hc⟩ := hne
    have hWa : W (c, true) ≠ ∞ := by
      rw [hWdef, geomG_of_mem _ hαm κ measurable_const (show (c, true) ∈ M.checkAlpha from
        ⟨hc, rfl⟩)]
      exact ENNReal.one_ne_top
    have hψs := M.isMaximalIrreducibility_split hψ
    have hfull := (lemma_15_2_2_i hψs.2.1 hWm (ENNReal.inv_lt_one.2 hκ).le hbt hdrift).2
      ⟨(c, true), hWa⟩
    set N := {z | W z ≠ ∞}ᶜ with hN
    have hNm : MeasurableSet N := ((measurableSet_singleton ∞).compl.preimage hWm).compl
    have h0 : ∫⁻ x, M.splitK x N ∂ψ = 0 := by
      rw [← Measure.bind_apply hNm M.splitK.aemeasurable]; exact hfull
    have hae := (lintegral_eq_zero_iff (Kernel.measurable_coe _ hNm)).1 h0
    have : (ae ψ).NeBot := ae_neBot.2 hψ.1
    obtain ⟨x, hx⟩ := hae.exists
    have hx' : (1 - M.splitProb x) * N.indicator 1 (x, false) +
        M.splitProb x * N.indicator 1 (x, true) = 0 := by
      have := M.lintegral_splitK x (f := N.indicator 1) (measurable_one.indicator hNm)
      rw [lintegral_indicator_one hNm] at this
      rw [← this]; exact hx
    obtain ⟨h1, h2⟩ := add_eq_zero.1 hx'
    have hr1 : 1 - M.splitProb x ≠ 0 := (tsub_pos_iff_lt.2 ((M.splitProb_le x).trans_lt
      M.δ_lt_one)).ne'
    have hfalse : W (x, false) ≠ ∞ := by
      have := (mul_eq_zero.1 h1).resolve_left hr1
      by_contra hW
      rw [indicator_of_mem (show (x, false) ∈ N from by simpa [hN] using hW)] at this
      exact one_ne_zero this
    refine ⟨x, ?_⟩
    change ∫⁻ z, W z ∂M.splitK x ≠ ∞
    rw [M.lintegral_splitK x hWm]
    rcases mul_eq_zero.1 h2 with hr | hind
    · rw [hr, zero_mul, add_zero]
      exact ENNReal.mul_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top) hfalse
    · have htrue : W (x, true) ≠ ∞ := by
        by_contra hW
        rw [indicator_of_mem (show (x, true) ∈ N from by simpa [hN] using hW)] at hind
        exact one_ne_zero hind
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)
        hfalse, ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
          (M.splitProb_le_one x)) htrue⟩
  · have hsd : M.split (Measure.dirac x) = M.splitK x := Measure.dirac_bind M.splitK.measurable x
    calc ∫⁻ y, ∫⁻ z, W z ∂M.splitK y ∂P x = ∫⁻ z, W z ∂M.split (P x) :=
          (Measure.lintegral_bind M.splitK.aemeasurable hWm.aemeasurable).symm
      _ = ∫⁻ z, W z ∂(M.splitKernel ∘ₘ M.split (Measure.dirac x)) := by
          rw [M.split_comp_splitKernel, dirac_kernel]
      _ = ∫⁻ z, ∫⁻ w, W w ∂M.splitKernel z ∂M.split (Measure.dirac x) :=
          Measure.lintegral_bind (Kernel.aemeasurable _) hWm.aemeasurable
      _ ≤ ∫⁻ z, (κ⁻¹ * W z + M.checkAlpha.indicator (fun _ => κ⁻¹ * Mv) z)
            ∂M.split (Measure.dirac x) := lintegral_mono fun z => hdrift z
      _ = κ⁻¹ * ∫⁻ z, W z ∂M.split (Measure.dirac x) +
            κ⁻¹ * Mv * M.split (Measure.dirac x) M.checkAlpha := by
          rw [lintegral_add_left (hWm.const_mul _), lintegral_const_mul _ hWm,
            lintegral_indicator_const hαm]
      _ ≤ κ⁻¹ * ∫⁻ z, W z ∂M.splitK x + M.C.indicator (fun _ => κ⁻¹ * Mv) x := by
          rw [hsd]
          refine add_le_add le_rfl ?_
          rw [← hsd, Minorization.checkAlpha, M.split_apply_true _ hC, inter_self,
            Measure.dirac_apply' x hC]
          by_cases hx : x ∈ M.C
          · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, mul_one]
            exact mul_le_of_le_one_right' (M.δ_lt_one.le)
          · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero, mul_zero]

/-- **A small set with a concentrated minorization** (Theorem 5.5.7, with `ν(Cᶜ) = 0`): for an
aperiodic chain, every petite `C ∈ B⁺(X)` carries a concentrated minorization for some skeleton
`Pᵐ`, `m ≥ 1`. -/
theorem exists_concentrated_minorization [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ)
    {C : Set X} (hC : IsPetite P C) (hψC : 0 < ψ C) :
    ∃ m, 1 ≤ m ∧ ∃ M : Minorization (P ^ m : Kernel X X), M.C = C ∧ M.IsConcentrated := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨ν₀, hν₀, T, hT⟩ := exists_forall_large_minorization P hψ hap hC
  obtain ⟨δ, hδ, hδle⟩ := hT (T + 1) (Nat.le_succ T)
  obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hψC.ne'
  have h1 : δ * ν₀ univ ≤ 1 := by
    have := isMarkovKernel_pow P (T + 1)
    have := hδle c hc univ
    rw [Measure.smul_apply, smul_eq_mul] at this
    exact this.trans prob_le_one
  have hν₀fin : ν₀ univ ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.mul_top hδ.ne'] at h1
    exact absurd h1 (by simp)
  have hδt : δ ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.top_mul (Measure.measure_univ_ne_zero.2 hν₀)] at h1
    exact absurd h1 (by simp)
  -- some `j` with `∫ ν₀(dy) Pʲ(y, C) > 0`
  have hcover : (univ : Set X) ⊆ ⋃ n : ℕ, {y | 0 < (P ^ (n + 1) : Kernel X X) y C} := fun y _ =>
    mem_iUnion.2 ((hitProb_pos_iff P hCm y).1 (hψ.2.1 C hCm hψC y))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < ν₀ {y | 0 < (P ^ (n + 1) : Kernel X X) y C} := by
    by_contra hcon
    push Not at hcon
    apply hν₀
    rw [← Measure.measure_univ_eq_zero]
    exact le_antisymm ((measure_mono hcover).trans (le_of_eq (measure_iUnion_null fun n =>
      nonpos_iff_eq_zero.1 (hcon n)))) zero_le
  set j := n + 1 with hj
  have hgm : Measurable fun y => (P ^ j : Kernel X X) y C := Kernel.measurable_coe _ hCm
  have hint : 0 < ∫⁻ y, (P ^ j : Kernel X X) y C ∂ν₀ := by
    rw [lintegral_pos_iff_support hgm]
    refine hn.trans_le (measure_mono fun y hy => ?_)
    exact (show 0 < (P ^ j : Kernel X X) y C from hy).ne'
  set m := T + 1 + j with hm
  have := isMarkovKernel_pow P m
  set ν' : Measure X := δ • (((P ^ j : Kernel X X) ∘ₘ ν₀).restrict C) with hν'
  have hle : ∀ x ∈ C, ν' ≤ (P ^ m : Kernel X X) x := fun x hx => by
    refine Measure.le_intro fun A hA _ => ?_
    rw [hν', Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul,
      Measure.bind_apply (hA.inter hCm) (Kernel.aemeasurable _),
      hm, Kernel.pow_add_apply_eq_lintegral P (T + 1) j x hA, ← lintegral_const_mul _
        (Kernel.measurable_coe _ (hA.inter hCm))]
    calc ∫⁻ y, δ * (P ^ j : Kernel X X) y (A ∩ C) ∂ν₀
        = ∫⁻ y, (P ^ j : Kernel X X) y (A ∩ C) ∂(δ • ν₀) := by
          rw [lintegral_smul_measure, smul_eq_mul, lintegral_const_mul _
            (Kernel.measurable_coe _ (hA.inter hCm))]
      _ ≤ ∫⁻ y, (P ^ j : Kernel X X) y (A ∩ C) ∂(P ^ (T + 1) : Kernel X X) x :=
          lintegral_mono' (hδle x hx) le_rfl
      _ ≤ ∫⁻ y, (P ^ j : Kernel X X) y A ∂(P ^ (T + 1) : Kernel X X) x :=
          lintegral_mono fun y => measure_mono inter_subset_left
  have hpos : 0 < ν' C := by
    rw [hν', Measure.smul_apply, Measure.restrict_apply hCm, inter_self, smul_eq_mul,
      Measure.bind_apply hCm (Kernel.aemeasurable _)]
    exact ENNReal.mul_pos hδ.ne' hint.ne'
  have hfin : ν' C ≠ ∞ := by
    rw [hν', Measure.smul_apply, Measure.restrict_apply hCm, inter_self, smul_eq_mul,
      Measure.bind_apply hCm (Kernel.aemeasurable _)]
    refine ENNReal.mul_ne_top hδt ?_
    · refine ne_top_of_le_ne_top hν₀fin ?_
      calc ∫⁻ y, (P ^ j : Kernel X X) y C ∂ν₀ ≤ ∫⁻ _, 1 ∂ν₀ := lintegral_mono fun y => by
            have := isMarkovKernel_pow P j
            exact prob_le_one
        _ = ν₀ univ := by rw [lintegral_one]
  exact ⟨m, by omega, Minorization.ofLe hCm hle hpos hfin, rfl,
    Minorization.ofLe_isConcentrated hCm hle hpos hfin⟩

/-- **The skeleton gives the chain on `S`** (Theorem 15.3.7, restricted form): if the `m`-skeleton
restricted to `S` is `f^{(m)}`-geometrically regular, so is the chain `f`-geometrically
regular on `S`. -/
theorem IsFGeomRegularOn.of_skeleton {P : Kernel X X} [IsMarkovKernel P] {f : X → ℝ≥0∞}
    (hf : Measurable f) {m : ℕ} (hm : 1 ≤ m) {S : Set X}
    (h : haveI := isMarkovKernel_pow P m; IsFGeomRegularOn (P ^ m : Kernel X X) (fSkel P m f) S) :
    IsFGeomRegularOn P f S := by
  have := isMarkovKernel_pow P m
  obtain ⟨C, hC, R, hR, -, hfin, M, hM, hb⟩ := h
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨r, hr, hrt, hrR⟩ := exists_one_lt_pow_le hR m
  have hle : ∀ x, geomSum P C r f x ≤ r ^ m *
      geomSum (P ^ m : Kernel X X) C R (fSkel P m f) x := fun x =>
    (geomSum_le_skeleton hm hCm hr.le hf x).trans (mul_le_mul' le_rfl
      (geomSum_mono_r _ C hrR _ x))
  exact ⟨C, hC.of_skeleton, r, hr, hrt, fun x hx => ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top hrt) (hfin x hx)) (hle x),
    r ^ m * M, ENNReal.mul_ne_top (ENNReal.pow_ne_top hrt) hM, fun x hx =>
      (hle x).trans (mul_le_mul' le_rfl (hb x hx))⟩

/-- `E_x[Σ_{k<τ_∅} rᵏ] = ∞` for `r ≥ 1`. -/
theorem geomSum_empty_one (P : Kernel X X) [IsMarkovKernel P] {r : ℝ≥0∞} (hr : 1 ≤ r) (x : X) :
    geomSum P ∅ r (fun _ => 1) x = ∞ := by
  have := isMarkovKernel_pathKernel P
  have h : ∀ ω : ℕ → X, sumBefore (firstReturn ∅) (fun k ω => r ^ k * 1) ω = ∞ := fun ω => by
    have h0 : firstReturn (∅ : Set X) ω = ⊤ := by simp [firstReturn, hittingAfter_empty]
    rw [sumBefore_eq_of_eq (τ' := fun _ => ⊤) h0, sumBefore_top_eq]
    exact tsum_eq_top_of_one_le fun k => by rw [mul_one]; exact one_le_pow₀ hr
  rw [geomSum, lintegral_congr h, lintegral_const, measure_univ, mul_one]

/-- **A geometrically regular chain on `S ≠ ∅` has a petite Kendall set**: the petite set of (15.36)
with `f = 1` is non-empty and Kendall. -/
theorem hasKendallPetite_of_isFGeomRegularOn {P : Kernel X X} [IsMarkovKernel P] {S : Set X}
    (hS : S.Nonempty) (h : IsFGeomRegularOn P (fun _ => 1) S) : HasKendallPetite P := by
  obtain ⟨C, hC, κ, hκ, hκt, hfin, M, hM, hb⟩ := h
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  obtain ⟨x, hx⟩ := hS
  have hne : C.Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty] at h0
    subst h0
    exact hfin x hx (geomSum_empty_one P hκ.le x)
  refine ⟨C, hC, hne, κ, hCm, hκ, hκt, 1 + (κ - 1) * M, ENNReal.add_ne_top.2
    ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (ENNReal.sub_ne_top hκt) hM⟩, fun y hy => ?_⟩
  rw [kendallMoment_eq_one_add P hCm hκ]
  exact add_le_add le_rfl (mul_le_mul' le_rfl (hb y hy))

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The core of (i) ⇒ (ii) and of Theorem 15.4.3**: for an aperiodic positive chain, a
minorization of a skeleton `Pᵐ` on `C ∈ B⁺(X)` with `ν(C) > 0` and
`|∫ ν(dx) P^{mn}(x, C) − p| ≤ K ρⁿ`, `ρ < 1`, gives a petite Kendall set. -/
theorem hasKendallPetite_of_split_local {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) (hpos : IsPositive P ψ)
    {m : ℕ} (hm : 1 ≤ m) (M : Minorization (P ^ m : Kernel X X)) (hψC : 0 < ψ M.C)
    (hνC : 0 < M.ν M.C) {p ρ K : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hloc : ∀ n, |(∫⁻ x, ((P ^ m : Kernel X X) ^ n : Kernel X X) x M.C ∂M.ν).toReal - p| ≤
      K * ρ ^ n) : HasKendallPetite P := by
  have := isMarkovKernel_pow P m
  obtain ⟨-, π, hπp, hπ⟩ := hpos
  have hψQ : IsMaximalIrreducibility (P ^ m : Kernel X X) ψ :=
    ((proposition_5_4_5_iii P hψ hap).1 m hm).1
  have hposQ : IsPositive (P ^ m : Kernel X X) ψ := ⟨hψQ, π, hπp, hπ.pow m⟩
  obtain ⟨κ, hK⟩ := M.isKendall_split_of_local hposQ hψC hνC (hπ.pow m) hρ0 hρ1 hloc
  obtain ⟨V, hV, hV1, ⟨x₀, hx₀⟩, ρ', b', hρ', hb', hdrift⟩ :=
    M.driftV4_of_isKendall_split hψQ (nonempty_of_measure_ne_zero hψC.ne') hK
  have := M.isProbabilityMeasure_ν
  have hsm : IsSmallSet (P ^ m : Kernel X X) 1 (M.δ • M.ν) M.C := ⟨M.measurableSet_C, one_pos,
    smul_measure_ne_zero (IsProbabilityMeasure.ne_zero M.ν) M.δ_pos.ne', fun x hx =>
      Measure.le_intro fun A _ _ => by
        rw [pow_one, Measure.smul_apply, smul_eq_mul]; exact M.le_apply hx A⟩
  obtain ⟨hreg, -⟩ := theorem_15_3_3 hψQ hV hV1 hρ' hb' ⟨_, _, proposition_5_5_3 hsm⟩ hdrift hx₀
  have hreg' : IsFGeomRegularOn (P ^ m : Kernel X X) (fSkel P m (fun _ => 1))
      {x | V x ≠ ∞} := hreg.of_le_const_mul hV (ENNReal.natCast_ne_top m) fun x => by
    rw [fSkel_one_const]; exact le_mul_of_one_le_right' (hV1 x)
  exact hasKendallPetite_of_isFGeomRegularOn ⟨x₀, hx₀⟩ (hreg'.of_skeleton measurable_const hm)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **(i) ⇒ (ii) of Theorem 15.0.1** (via Theorem 15.4.3): local geometric convergence on a petite
`C ∈ B⁺(X)` gives a petite Kendall set. -/
theorem hasKendallPetite_of_isLocallyGeomErgodic {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ)
    (h : IsLocallyGeomErgodic P ψ) : HasKendallPetite P := by
  obtain ⟨hpos, C, hC, hψC, ρ, K, p, hρ0, hρ1, -, hloc⟩ := h
  obtain ⟨m, hm, M, hMC, hconc⟩ := exists_concentrated_minorization hψ hap hC hψC
  have := isMarkovKernel_pow P m
  have := M.isProbabilityMeasure_ν
  have hνC : M.ν M.C = 1 := by
    rw [← prob_compl_eq_zero_iff M.measurableSet_C]; exact hconc
  have hae : ∀ᵐ x ∂M.ν, x ∈ M.C := ae_iff.2 hconc
  have hK0 : 0 ≤ K := by
    obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hψC.ne'
    have := hloc c hc 0
    exact (abs_nonneg _).trans (this.trans_eq (by simp))
  refine hasKendallPetite_of_split_local hψ hap hpos hm M (hMC ▸ hψC) (by rw [hνC]; exact one_pos)
    hρ0 hρ1 (p := p) (K := K) fun n => ?_
  have hint : (∫⁻ x, ((P ^ m : Kernel X X) ^ n : Kernel X X) x M.C ∂M.ν).toReal =
      ∫ x, (((P ^ m : Kernel X X) ^ n : Kernel X X) x M.C).toReal ∂M.ν :=
    (integral_toReal ((Kernel.measurable_coe _ M.measurableSet_C).aemeasurable)
      (Eventually.of_forall fun x => by
        have := isMarkovKernel_pow (P ^ m : Kernel X X) n
        exact measure_lt_top _ _)).symm
  have hgi : Integrable (fun x => (((P ^ m : Kernel X X) ^ n : Kernel X X) x M.C).toReal) M.ν := by
    refine Integrable.of_bound (C := 1) ((Kernel.measurable_coe _
      M.measurableSet_C).ennreal_toReal.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    have := isMarkovKernel_pow (P ^ m : Kernel X X) n
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  rw [hint, show p = ∫ _, p ∂M.ν by simp, ← integral_sub hgi (integrable_const p)]
  have hb : ∀ᵐ x ∂M.ν, ‖(((P ^ m : Kernel X X) ^ n : Kernel X X) x M.C).toReal - p‖ ≤ K * ρ ^ n :=
    hae.mono fun x hx => by
      rw [Real.norm_eq_abs, ← pow_mul, hMC]
      refine (hloc x (hMC ▸ hx) (m * n)).trans (mul_le_mul_of_nonneg_left ?_ hK0)
      exact pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_mul_of_pos_left n (by omega))
  have := norm_integral_le_of_norm_le_const hb
  rw [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, Real.norm_eq_abs] at this
  exact this

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.4.3** (MT p. 387): for an aperiodic positive chain, if `C ∈ B⁺(X)` is `ν`-small
(`P^{m}(x, ·) ≥ ν` on `C`, `ν(C) > 0`) and
`|∫ ν_C(dx) (Pⁿ(x, C) − P^∞(C))| ≤ M_C ρ_Cⁿ` (15.47) with `ν_C = ν(· ∩ C)/ν(C)`, then there is a
full absorbing set `S` on which the chain is geometrically ergodic:
`Σₙ rⁿ ‖Pⁿ(x, ·) − π‖ ≤ R W(x) < ∞` for `x ∈ S = {W < ∞}`. -/
theorem theorem_15_4_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) (hpos : IsPositive P ψ)
    {m : ℕ} {ν : Measure X} {C : Set X} (hsmall : IsSmallSet P m ν C) (hψC : 0 < ψ C)
    (hνC : 0 < ν C) {p ρ K : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hloc : ∀ n, |(∫⁻ x in C, (P ^ n : Kernel X X) x C ∂ν).toReal / (ν C).toReal - p| ≤
      K * ρ ^ n) :
    ∃ W : X → ℝ≥0∞, Measurable W ∧ IsFull ψ {x | W x ≠ ∞} ∧ IsAbsorbing P {x | W x ≠ ∞} ∧
      ∀ (π : Measure X) [IsProbabilityMeasure π], IsInvariant P π →
        ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
          ∑' n, r ^ n * fNorm (fun _ => 1) ((P ^ n : Kernel X X) x) π ≤ R * W x := by
  have hm : 1 ≤ m := hsmall.2.1
  have := isMarkovKernel_pow P m
  have hCm := hsmall.1
  have hνfin : ν C ≠ ∞ := by
    obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hψC.ne'
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ((hsmall.2.2.2 c hc C).trans prob_le_one)
  have hle : ∀ x ∈ C, ν.restrict C ≤ (P ^ m : Kernel X X) x := fun x hx =>
    Measure.restrict_le_self.trans (hsmall.2.2.2 x hx)
  have hpos' : 0 < ν.restrict C C := by rw [Measure.restrict_apply hCm, inter_self]; exact hνC
  have hfin' : ν.restrict C C ≠ ∞ := by rw [Measure.restrict_apply hCm, inter_self]; exact hνfin
  set M := Minorization.ofLe hCm hle hpos' hfin' with hMdef
  have hMν : M.ν = (ν C)⁻¹ • ν.restrict C := by
    rw [hMdef]; change ((ν.restrict C) C)⁻¹ • (ν.restrict C).restrict C = _
    rw [Measure.restrict_apply hCm, inter_self, Measure.restrict_restrict hCm, inter_self]
  have hMC : M.C = C := rfl
  have hK : HasKendallPetite P := by
    refine hasKendallPetite_of_split_local hψ hap hpos hm M (hMC ▸ hψC) ?_ hρ0 hρ1 (p := p)
      (K := K) fun n => ?_
    · rw [hMν, hMC, Measure.smul_apply, Measure.restrict_apply hCm, inter_self, smul_eq_mul,
        ENNReal.inv_mul_cancel hνC.ne' hνfin]
      exact one_pos
    · rw [hMν, hMC, lintegral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ← pow_mul, mul_comm, ← div_eq_mul_inv]
      refine (hloc (m * n)).trans (mul_le_mul_of_nonneg_left ?_ ?_)
      · exact pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_mul_of_pos_left n (by omega))
      · obtain ⟨c, hc⟩ := nonempty_of_measure_ne_zero hψC.ne'
        have := hloc 0
        exact (abs_nonneg _).trans (this.trans_eq (by simp))
  obtain ⟨V, hV, hV1, ⟨x₀, hx₀⟩, ρ', b', hρ', hb', D, hD, hdrift⟩ :=
    hasDriftV4_of_hasKendallPetite hK
  obtain ⟨habs, hfull⟩ := lemma_15_2_2_i hψ.2.1 hV hρ'.le hb' hdrift
  obtain ⟨-, hgeo⟩ := geometric_ergodic_of_driftV4 hψ hap hV hV1 hρ' hb' hD hdrift hx₀
  refine ⟨V, hV, hfull ⟨x₀, hx₀⟩, habs, fun π _ hπ => ?_⟩
  obtain ⟨-, r, hr, -, R, hR, hbd⟩ := hgeo π hπ
  exact ⟨r, hr, R, hR, fun x => (ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl
    (fNorm_mono hV1 _ _)).trans (hbd x)⟩

/-! ### The Geometric Ergodic Theorem -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.0.1** (the Geometric Ergodic Theorem, MT p. 362), corrected: for a
`ψ`-irreducible aperiodic chain, (i) local geometric convergence (15.1) on a petite `C ∈ B⁺(X)`,
(ii) a petite **non-empty** Kendall set (15.2), and (iii) the drift condition (V4) (15.3) for a
petite set and a `V ≥ 1` finite at some point, are equivalent. -/
theorem theorem_15_0_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) :
    List.TFAE [IsLocallyGeomErgodic P ψ, HasKendallPetite P, HasDriftV4 P] := by
  tfae_have 1 → 2 := hasKendallPetite_of_isLocallyGeomErgodic hψ hap
  tfae_have 2 → 3 := hasDriftV4_of_hasKendallPetite
  tfae_have 3 → 1 := isLocallyGeomErgodic_of_hasDriftV4 hψ hap
  tfae_finish

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The consequences in Theorem 15.0.1** (MT p. 363): if `V` satisfies (iii), then
`S_V = {V < ∞}` is absorbing and full, the chain is positive, `π(V) < ∞`, and for some `r > 1`,
`R < ∞`, `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_V ≤ R V(x)` for every `x` (15.4), trivially off `S_V`. -/
theorem theorem_15_0_1_consequences {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) {x₀ : X} (hx₀ : V x₀ ≠ ∞) {ρ b : ℝ≥0∞}
    (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) :
    IsAbsorbing P {x | V x ≠ ∞} ∧ IsFull ψ {x | V x ≠ ∞} ∧ IsPositive P ψ ∧
      ∀ (π : Measure X) [IsProbabilityMeasure π], IsInvariant P π →
        ∫⁻ x, V x ∂π ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x,
          ∑' n, r ^ n * fNorm V ((P ^ n : Kernel X X) x) π ≤ R * V x := by
  obtain ⟨habs, hfull⟩ := lemma_15_2_2_i hψ.2.1 hV hρ.le hb h
  obtain ⟨hpos, hgeo⟩ := geometric_ergodic_of_driftV4 hψ hap hV hV1 hρ hb hC h hx₀
  refine ⟨habs, hfull ⟨x₀, hx₀⟩, hpos, fun π _ hπ => ?_⟩
  obtain ⟨hπV, r, hr, -, R, hR, hbd⟩ := hgeo π hπ
  exact ⟨hπV, r, hr, R, hR, hbd⟩

/-- **The counterexample to Theorem 15.0.1 (ii) as stated** (`C = ∅`): for the null recurrent
forward recurrence time chain of `heavyRenewal`, `∅` is petite and Kendall (vacuously), but (iii)
fails: (V4) would make the chain positive. -/
theorem theorem_15_0_1_counterexample :
    haveI := isProbabilityMeasure_heavyRenewal
    haveI := isMarkovKernel_fwdRecKernel heavyRenewal
    IsPetite (fwdRecKernel heavyRenewal) ∅ ∧ IsKendall (fwdRecKernel heavyRenewal) ∅ 2 ∧
      ¬ HasDriftV4 (fwdRecKernel heavyRenewal) := by
  have := isProbabilityMeasure_heavyRenewal
  have := isMarkovKernel_fwdRecKernel heavyRenewal
  obtain ⟨hrec, hpet, -, -, -, hnpos⟩ := theorem_10_0_1_counterexample
  refine ⟨hpet, ⟨MeasurableSet.empty, by norm_num, ENNReal.ofNat_ne_top, 0, ENNReal.zero_ne_top,
    fun x hx => absurd hx (notMem_empty x)⟩, ?_⟩
  rintro ⟨V, hV, hV1, ⟨x₀, hx₀⟩, ρ, b, hρ, hb, C, hC, h⟩
  have hct : (1 - ρ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ).ne'
  exact hnpos (isPositive_of_driftV3 hrec.1 hV hV1 hC (hV.const_mul _)
    (ENNReal.mul_ne_top hct hb) (ENNReal.mul_ne_top hct hx₀) (h.driftV3_scaled hV hρ)).1

end MeynTweedie.GeometricErgodicity

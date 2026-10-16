/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.DistributionFunctions

/-!
# Weak convergence of distribution functions

SLP §12.3, Theorem 12.8 and Exercises 12.4–12.5, pp. 369–372.

* `nullCoord μ i`: the levels `c` with `λ{y : yᵢ = c} = 0`. Its complement is countable
  (`countable_nullCoord_compl`), so it is dense.
* `continuousAt_distFun`: a point whose coordinates are all null levels is a continuity point
  of `F`.
* **Theorem 12.8** (`theorem_12_8`): `λₙ ⇒ λ` iff `Fₙ(x) → F(x)` at every continuity point `x` of
  `F`. For (⇐), boxes with null-level coordinates satisfy the hypotheses of Theorem 12.5, and
  their measures are alternating sums of `F` at continuity points.
* **Exercise 12.4** (`ex_12_4`): for `S ⊆ ℝˡ` Borel, `λₙ ⇒ λ` on `S` iff the extensions
  `λ̂(A) = λ(A ∩ S)` converge weakly on `ℝˡ`.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {l : ℕ}

/-- The levels `c` with `λ{y : yᵢ = c} = 0`. -/
def nullCoord (μ : Measure (Fin l → ℝ)) (i : Fin l) : Set ℝ := {c | μ {y | y i = c} = 0}

theorem countable_nullCoord_compl (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] (i : Fin l) :
    (nullCoord μ i)ᶜ.Countable := by
  refine (Measure.countable_meas_level_set_pos (μ := μ) (measurable_pi_apply i)).mono ?_
  intro c hc
  exact pos_iff_ne_zero.2 hc

theorem dense_nullCoord (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] (i : Fin l) :
    Dense (nullCoord μ i) := by
  simpa using (countable_nullCoord_compl μ i).dense_compl ℝ

/-- A point whose coordinates are null levels is a continuity point of `F`. -/
theorem continuousAt_distFun (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    {v : Fin l → ℝ} (hv : ∀ i, v i ∈ nullCoord μ i) : ContinuousAt (distFun μ) v := by
  refine ex_12_3 (distFun_mono μ) (contFromAbove_distFun μ v) ((theorem_12_7c μ v).2 ?_)
  refine measure_mono_null (t := ⋃ i, {y : Fin l → ℝ | y i = v i}) (fun y hy => ?_)
    (measure_iUnion_null fun i => hv i)
  rw [frontier_Iic_eq] at hy
  obtain ⟨hle, hlt⟩ := hy
  simp only [lowerOpen, Set.mem_pi, mem_univ, true_implies, mem_Iio, not_forall, not_lt] at hlt
  obtain ⟨i, hi⟩ := hlt
  exact mem_iUnion.2 ⟨i, le_antisymm (hle i) hi⟩

/-- A continuity point of `F` has a `λ`-null boundary of `(−∞, x]`. -/
theorem frontier_null_of_continuousAt (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    {x : Fin l → ℝ} (h : ContinuousAt (distFun μ) x) : μ (frontier (Iic x)) = 0 := by
  refine (theorem_12_7c μ x).1 ?_
  have hc : Tendsto (fun ε : ℝ => x - diag ε) (𝓝[>] 0) (𝓝 x) := by
    have : Tendsto (fun ε : ℝ => x - diag ε) (𝓝 0) (𝓝 (x - diag 0)) :=
      (continuous_const.sub (continuous_pi fun _ => continuous_id)).tendsto 0
    have h0 : x - diag 0 = x := by ext; simp [diag]
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact h.tendsto.comp hc

theorem box_inter (a b a' b' : Fin l → ℝ) : box a b ∩ box a' b' = box (a ⊔ a') (b ⊓ b') := by
  ext y
  simp only [box, mem_inter_iff, Set.mem_pi, mem_univ, true_implies, mem_Ioc, Pi.sup_apply,
    Pi.inf_apply, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨h1, h2⟩ i; exact ⟨⟨(h1 i).1, (h2 i).1⟩, (h1 i).2, (h2 i).2⟩
  · intro h; exact ⟨fun i => ⟨(h i).1.1, (h i).2.1⟩, fun i => ⟨(h i).1.2, (h i).2.2⟩⟩

theorem box_eq_empty {a b : Fin l → ℝ} (h : ¬ a ≤ b) : box a b = ∅ := by
  rw [Pi.le_def] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  ext y
  simp only [box, Set.mem_pi, mem_univ, true_implies, mem_Ioc, mem_empty_iff_false, iff_false,
    not_forall]
  exact ⟨i, fun h => by linarith [h.1, h.2]⟩

/-- **Theorem 12.8.** For probability measures on `ℝˡ`, `λₙ ⇒ λ` iff `Fₙ(x) → F(x)` at every
continuity point `x` of `F`. -/
theorem theorem_12_8 (ls : ℕ → Measure (Fin l → ℝ)) (μ : Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ] :
    ConvWeak ls μ ↔ ∀ x, ContinuousAt (distFun μ) x →
      Tendsto (fun n => distFun (ls n) x) atTop (𝓝 (distFun μ x)) := by
  constructor
  · intro h x hx
    exact (theorem_12_3 ls μ).2.2.1 h (Iic x) measurableSet_Iic
      (frontier_null_of_continuousAt μ hx)
  · intro h
    set 𝒜 : Set (Set (Fin l → ℝ)) := {A | ∃ a b, (∀ i, a i ∈ nullCoord μ i ∧
      b i ∈ nullCoord μ i) ∧ A = box a b}
    refine theorem_12_5 (𝒜 := 𝒜) (fun A ⟨a, b, _, hA⟩ => hA ▸ measurableSet_box a b) ?_ ?_ ?_
    · rintro _ ⟨a, b, hab, rfl⟩ _ ⟨a', b', hab', rfl⟩
      refine ⟨a ⊔ a', b ⊓ b', fun i => ⟨?_, ?_⟩, box_inter a b a' b'⟩
      · simp only [Pi.sup_apply]; rcases le_total (a i) (a' i) with h1 | h1
        · rw [max_eq_right h1]; exact (hab' i).1
        · rw [max_eq_left h1]; exact (hab i).1
      · simp only [Pi.inf_apply]; rcases le_total (b i) (b' i) with h1 | h1
        · rw [min_eq_left h1]; exact (hab i).2
        · rw [min_eq_right h1]; exact (hab' i).2
    · intro x ε hε
      have hε2 : 0 < ε / 2 := by positivity
      choose a ha hai using fun i => (dense_nullCoord μ i).exists_between
        (show x i - ε / 2 < x i by linarith)
      choose b hb hbi using fun i => (dense_nullCoord μ i).exists_between
        (show x i < x i + ε / 2 by linarith)
      refine ⟨box a b, ⟨a, b, fun i => ⟨ha i, hb i⟩, rfl⟩, ?_, fun y hy => ?_⟩
      · refine mem_interior.2 ⟨Set.pi univ fun i => Ioo (a i) (b i), fun y hy i _ =>
          ⟨(hy i trivial).1, (hy i trivial).2.le⟩,
          isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo, fun i _ => ⟨(hai i).2, (hbi i).1⟩⟩
      · rw [Metric.mem_ball, dist_pi_lt_iff hε]
        intro i
        have := hy i trivial
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [(hai i).1, (hbi i).2, this.1, this.2]
    · rintro _ ⟨a, b, hab, rfl⟩
      by_cases hle : a ≤ b
      · simp_rw [← vertexSum_eq _ hle]
        refine tendsto_finsetSum _ fun t _ => (h _ ?_).const_mul _
        refine continuousAt_distFun μ fun i => ?_
        simp only [vertex]
        split_ifs
        · exact (hab i).2
        · exact (hab i).1
      · simp [box_eq_empty hle]

/-- **Exercise 12.4.** For `S ⊆ ℝˡ`, `λₙ ⇒ λ` on `S` iff the extensions `λ̂(A) = λ(A ∩ S)` converge
weakly on `ℝˡ`. (Measurability of `S` is not needed.) -/
theorem ex_12_4 {S : Set (Fin l → ℝ)} (ls : ℕ → Measure S) (μ : Measure S)
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ] :
    ConvWeak ls μ ↔ ConvWeak (fun n => (ls n).map Subtype.val) (μ.map Subtype.val) := by
  have hmap : ∀ (ν : Measure S) {F : Set (Fin l → ℝ)}, MeasurableSet F →
      (ν.map Subtype.val).real F = ν.real (Subtype.val ⁻¹' F) := fun ν F hF => by
    rw [measureReal_def, Measure.map_apply measurable_subtype_coe hF]; rfl
  rw [(theorem_12_3 ls μ).1, (theorem_12_3 _ _).1]
  constructor
  · intro h F hF
    simp_rw [hmap _ hF.measurableSet]
    exact h _ (hF.preimage continuous_subtype_val)
  · intro h A hA
    obtain ⟨F, hF, rfl⟩ := isClosed_induced_iff.1 hA
    have := h F hF
    simp_rw [hmap _ hF.measurableSet] at this
    exact this

/-- **Exercise 12.5a.** On `S = [a, b] ⊆ ℝˡ`, if `λₙ([a, x]) → λ([a, x])` for every `x ∈ S`, then
`λₙ ⇒ λ` (through Exercise 12.4 and Theorem 12.8). -/
theorem ex_12_5a {a b : Fin l → ℝ} (ls : ℕ → Measure (Icc a b)) (μ : Measure (Icc a b))
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ]
    (h : ∀ x ∈ Icc a b, Tendsto (fun n => (ls n).real (Subtype.val ⁻¹' Icc a x)) atTop
      (𝓝 (μ.real (Subtype.val ⁻¹' Icc a x)))) : ConvWeak ls μ := by
  obtain ⟨s₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hab : a ≤ b := s₀.2.1.trans s₀.2.2
  refine (ex_12_4 ls μ).2 ((theorem_12_8 _ _).2 fun y _ => ?_)
  have hmap : ∀ (ν : Measure (Icc a b)), distFun (ν.map Subtype.val) y =
      ν.real (Subtype.val ⁻¹' Iic y) := fun ν => by
    rw [distFun, measureReal_def, Measure.map_apply measurable_subtype_coe measurableSet_Iic]; rfl
  simp_rw [hmap]
  by_cases hay : a ≤ y
  · have hpre : (Subtype.val ⁻¹' Iic y : Set (Icc a b)) = Subtype.val ⁻¹' Icc a (y ⊓ b) := by
      ext s
      simp only [mem_preimage, mem_Iic, mem_Icc, le_inf_iff]
      exact ⟨fun hs => ⟨s.2.1, hs, s.2.2⟩, fun hs => hs.2.1⟩
    rw [hpre]
    exact h _ ⟨le_inf hay hab, inf_le_right⟩
  · have hpre : (Subtype.val ⁻¹' Iic y : Set (Icc a b)) = ∅ := by
      ext s
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun hs => hay (s.2.1.trans hs)
    simp [hpre]

/-- The continuous nondecreasing ramp `gₙ(s) = min 1 (n Σᵢ max 0 (sᵢ - xᵢ))`, which increases to the
indicator of `{s : ¬ s ≤ x}` (used for Exercise 12.5b in place of the book's Lemma 12.1
functions). -/
noncomputable def ramp (x : Fin l → ℝ) (n : ℕ) (s : Fin l → ℝ) : ℝ :=
  min 1 ((n : ℝ) * ∑ i, max 0 (s i - x i))

theorem continuous_ramp (x : Fin l → ℝ) (n : ℕ) : Continuous (ramp x n) := by
  unfold ramp; fun_prop

theorem ramp_mem (x : Fin l → ℝ) (n : ℕ) (s : Fin l → ℝ) : 0 ≤ ramp x n s ∧ ramp x n s ≤ 1 :=
  ⟨le_min zero_le_one (mul_nonneg n.cast_nonneg
    (Finset.sum_nonneg fun _ _ => le_max_left _ _)), min_le_left _ _⟩

theorem monotone_ramp (x : Fin l → ℝ) (n : ℕ) : Monotone (ramp x n) := fun s t hst =>
  min_le_min_left _ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
    max_le_max le_rfl (by linarith [hst i])) n.cast_nonneg)

theorem tendsto_ramp (x s : Fin l → ℝ) :
    Tendsto (fun n => ramp x n s) atTop (𝓝 ((Iic x)ᶜ.indicator 1 s)) := by
  by_cases hs : s ≤ x
  · have : ∀ n, ramp x n s = 0 := fun n => by
      have : ∀ i, max 0 (s i - x i) = 0 := fun i => max_eq_left (by linarith [hs i])
      simp [ramp, this]
    simp only [this, indicator_of_notMem (show s ∉ (Iic x)ᶜ by simpa using hs)]
    exact tendsto_const_nhds
  · obtain ⟨i, hi⟩ : ∃ i, x i < s i := by
      by_contra h; push Not at h; exact hs h
    have hc : s i - x i ≤ ∑ j, max 0 (s j - x j) :=
      (le_max_right _ _).trans (Finset.single_le_sum (f := fun j => max 0 (s j - x j))
        (fun j _ => le_max_left _ _) (Finset.mem_univ i))
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (s i - x i))
    rw [indicator_of_mem (show s ∈ (Iic x)ᶜ by simpa using hs)]
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have hpos : 0 < s i - x i := by linarith
    have : 1 ≤ (n : ℝ) * ∑ j, max 0 (s j - x j) := by
      have h1 : 1 < N * (s i - x i) := by rwa [div_lt_iff₀ hpos] at hN
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    simp [ramp, min_eq_left this]

/-- **Exercise 12.5b** (corrected). On `S = [a, b]`, probability measures agreeing on the integrals
of all continuous nondecreasing functions are equal. (The book's hint cites "Theorem 12.1", i.e.
Lemma 12.1, whose functions are nonincreasing; nondecreasing functions suffice, which is what
Theorem 12.12 needs.) -/
theorem ex_12_5b {a b : Fin l → ℝ} (lam μ : Measure (Icc a b)) [IsProbabilityMeasure lam]
    [IsProbabilityMeasure μ] (h : ∀ f : Icc a b →ᵇ ℝ, Monotone f → ∫ s, f s ∂lam = ∫ s, f s ∂μ) :
    lam = μ := by
  have hE : ∀ x : Fin l → ℝ, MeasurableSet (Subtype.val ⁻¹' (Iic x)ᶜ : Set (Icc a b)) :=
    fun x => measurableSet_Iic.compl.preimage measurable_subtype_coe
  have hlim : ∀ (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] (x : Fin l → ℝ),
      Tendsto (fun n => ∫ s, ramp x n (s : Fin l → ℝ) ∂ν) atTop
        (𝓝 (ν.real (Subtype.val ⁻¹' (Iic x)ᶜ))) := fun ν _ x => by
    rw [← integral_indicator_one (hE x)]
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => ((continuous_ramp x n).comp continuous_subtype_val).aestronglyMeasurable)
      (integrable_const 1) (fun n => Eventually.of_forall fun s => ?_)
      (Eventually.of_forall fun s => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (ramp_mem x n s).1]; exact (ramp_mem x n s).2
    · exact tendsto_ramp x s
  have heq : ∀ x : Fin l → ℝ, lam.real (Subtype.val ⁻¹' (Iic x)ᶜ) =
      μ.real (Subtype.val ⁻¹' (Iic x)ᶜ) := fun x => by
    refine tendsto_nhds_unique (hlim lam x) ?_
    have := hlim μ x
    refine this.congr fun n => (h ⟨⟨fun s => ramp x n s,
      (continuous_ramp x n).comp continuous_subtype_val⟩, ⟨1, fun s t => ?_⟩⟩
      (fun s t hst => monotone_ramp x n hst)).symm
    have := ramp_mem x n s; have := ramp_mem x n t
    simp only [Real.dist_eq, abs_le]; constructor <;> linarith
  have hconv : ConvWeak (fun _ => μ) lam := by
    refine ex_12_5a _ _ fun x _ => ?_
    have hpre : (Subtype.val ⁻¹' Icc a x : Set (Icc a b)) = (Subtype.val ⁻¹' (Iic x)ᶜ)ᶜ := by
      ext s
      simp only [mem_preimage, mem_Icc, mem_compl_iff, mem_Iic, not_not]
      exact ⟨fun hs => hs.2, fun hs => ⟨s.2.1, hs⟩⟩
    rw [hpre, probReal_compl_eq_one_sub (hE x), probReal_compl_eq_one_sub (hE x), heq]
    exact tendsto_const_nhds
  exact convWeak_unique hconv fun _ => tendsto_const_nhds

end StokeyLucasPrescott.ConvergenceApplications

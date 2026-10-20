/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.BrouwerApplication
import FixedPointArguments.SchauderBoundedContinuous

/-!
# Applications of the Schauder fixed-point theorem (SLP §17.4)

SLP §17.4, pp. 519–525. Schauder's theorem itself is `theorem_17_4`
(`FixedPointArguments.SchauderBoundedContinuous`); Exercise 17.5 is in
`FixedPointArguments.SchauderAppODE`. The OLG primitives `FPAssumption17_1`, `fpZeta`, `fpPhi`,
`fpZetaInv` and the bounds `fp_bounds` are from `FixedPointArguments.BrouwerApplication`.

**Total variation** (§11.3). `fpTVNorm μ ν` is `‖μ − ν‖_TV = sup Σᵢ |μ(Aᵢ) − ν(Aᵢ)|` over finite
measurable partitions `{Aᵢ}` (`FPIsFinPartition`). `fp_abs_integral_sub_le`: for measurable `h`
with `|h| ≤ C`, `|∫ h dμ − ∫ h dν| ≤ C ‖μ − ν‖_TV` (proved with the Hahn decomposition).

**Results.**
* `FPAssumption17_3` (**Assumption 17.3**, pp. 520–521): `x ↦ π(x, ·)` is uniformly continuous
  into probability measures with the total-variation norm. `fpAssumption17_3_const`: a constant
  (i.i.d.) kernel satisfies it.
* `fpIntOp` the operator `(Tf)(x) = ∫ G[x, x′, f(x′)] π(x, dx′)` ((1), p. 521).
* `lemma_17_5` (**Lemma 17.5**, p. 521): `T(F)` is bounded and equicontinuous.
* `ex_17_6` (**Exercise 17.6**, p. 522): if `G` is also uniformly continuous in its third
  argument (uniformly over `(x, x′)`), `T` is (uniformly) continuous in the sup norm.
* `fp_exists_fixedPoint_intOp` (the combination described on p. 522 and pp. 524–525): with `D`
  nonempty, closed, bounded and convex and `X` totally bounded (e.g. bounded in `ℝˡ`), `T` maps
  `F` into itself and has a fixed point (Schauder, via `totallyBounded_of_equicontinuous` and
  `schauder_closed`).
* `proposition_4` (**Proposition 4**, p. 522): for `X = [a, b] ⊂ ℝ₊₊`, `π` satisfying
  Assumption 17.3 and Assumption 17.1, there is a continuous `f*` bounded away from zero with
  `f*(x) = ∫ φ[x′ζ⁻¹(f*(x′))] π(x, dx′)`. `proposition_4_zero_fixedPoint`: `f ≡ 0` is also a
  solution.
* `fpLabourOp` the operator of Exercise 17.7, `(Sn)(x) = ζ⁻¹[∫ φ(x′ n(x′)) π(x, dx′)]`.
  `ex_17_7_zero` (`S0 = 0`), `ex_17_7_why_of_f`, `ex_17_7_why_of_n` (the "Why?": `n* = ζ⁻¹ ∘ f*`
  and `f* = ζ ∘ n*`), `ex_17_7` (**Exercise 17.7**, corrected): `S` has a continuous fixed point
  bounded away from `0` (and below `L`).

**Corrections.**
* Exercise 17.7 as stated ("the operator has a fixed point") is trivial: `n ≡ 0` is always a
  fixed point (`ex_17_7_zero`, since `φ(0) = 0 = ζ⁻¹(0)`), so the claim needs no Schauder argument;
  the manual's Schauder set `D ⊆ [0, L)` contains `0` and does not exclude it. The meaningful
  statement is existence of a fixed point bounded away from zero, proved as `ex_17_7` (here
  from Proposition 4 through the correspondence `n* = ζ⁻¹ ∘ f*`, which is also the answer to the
  book's "Why?").
* Proposition 4's proof says `Tf` is continuous because `π` is Feller; Lemma 17.5 (whose
  equicontinuity makes each `Tf` uniformly continuous) gives this directly, which is what we use.
* Exercise 17.6 does not need Assumption 17.3 (only that each `π(x, ·)` is a probability
  measure), and "uniformly continuous in its third argument" is read, as in the manual, as
  uniform over `(x, x′)`.
* Lemma 17.5 uses joint continuity of `G` only to make `x′ ↦ G[x, x′, f(x′)]` measurable, and only
  boundedness of `D`.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open Set Filter Topology Metric MeasureTheory BoundedContinuousFunction

/-! ### The total-variation norm -/

/-- A finite measurable partition of `X`: finitely many pairwise disjoint measurable sets whose
union is `X`. -/
def FPIsFinPartition {X : Type*} [MeasurableSpace X] (P : Finset (Set X)) : Prop :=
  (∀ A ∈ P, MeasurableSet A) ∧ (P : Set (Set X)).PairwiseDisjoint id ∧ ⋃ A ∈ P, A = univ

/-- The total-variation norm `‖μ − ν‖_TV = sup Σᵢ |μ(Aᵢ) − ν(Aᵢ)|` over finite measurable
partitions `{Aᵢ}` of `X` (§11.3). -/
noncomputable def fpTVNorm {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : ℝ :=
  ⨆ P : {P : Finset (Set X) // FPIsFinPartition P}, ∑ A ∈ P.1, |μ.real A - ν.real A|

variable {X : Type*}

/-- `{X}` is a finite measurable partition. -/
theorem fpIsFinPartition_univ [MeasurableSpace X] :
    FPIsFinPartition ({univ} : Finset (Set X)) :=
  ⟨by simp, by simp, by simp⟩

/-- The partition sums are bounded by `μ(X) + ν(X)`. -/
theorem fpTVNorm_bddAbove [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    BddAbove (range fun P : {P : Finset (Set X) // FPIsFinPartition P} =>
      ∑ A ∈ P.1, |μ.real A - ν.real A|) := by
  refine ⟨μ.real univ + ν.real univ, ?_⟩
  rintro _ ⟨⟨P, hm, hd, hu⟩, rfl⟩
  have h1 := measureReal_biUnion_finset (μ := μ) (f := id) hd hm
  have h2 := measureReal_biUnion_finset (μ := ν) (f := id) hd hm
  simp only [id] at h1 h2
  rw [hu] at h1 h2
  calc ∑ A ∈ P, |μ.real A - ν.real A| ≤ ∑ A ∈ P, (μ.real A + ν.real A) :=
        Finset.sum_le_sum fun A _ => abs_sub_le_iff.2
          ⟨by linarith [measureReal_nonneg (μ := ν) (s := A)],
            by linarith [measureReal_nonneg (μ := μ) (s := A)]⟩
    _ = μ.real univ + ν.real univ := by rw [Finset.sum_add_distrib, h1, h2]

/-- `‖μ − ν‖_TV ≥ 0`. -/
theorem fpTVNorm_nonneg [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : 0 ≤ fpTVNorm μ ν :=
  le_ciSup_of_le (fpTVNorm_bddAbove μ ν) ⟨{univ}, fpIsFinPartition_univ⟩
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- The two-set partition `{s, sᶜ}` bounds `‖μ − ν‖_TV` from below. -/
theorem fp_le_tvNorm_pair [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {s : Set X} (hs : MeasurableSet s) :
    |μ.real s - ν.real s| + |μ.real sᶜ - ν.real sᶜ| ≤ fpTVNorm μ ν := by
  classical
  by_cases hss : s = sᶜ
  · have he : ∀ x : X, False := fun x => by
      have h : x ∈ s ↔ x ∈ sᶜ := Iff.of_eq (congrArg (x ∈ ·) hss)
      rw [mem_compl_iff] at h
      exact iff_not_self h
    have : IsEmpty X := ⟨he⟩
    rw [Set.eq_empty_of_isEmpty sᶜ, Set.eq_empty_of_isEmpty s]
    simp only [measureReal_empty, sub_self, abs_zero, add_zero]
    exact fpTVNorm_nonneg μ ν
  · refine le_ciSup_of_le (fpTVNorm_bddAbove μ ν) ⟨{s, sᶜ}, ?_, ?_, ?_⟩ ?_
    · intro A hA
      rcases Finset.mem_insert.1 hA with rfl | hA
      · exact hs
      · rw [Finset.mem_singleton.1 hA]
        exact hs.compl
    · rw [Finset.coe_pair]
      exact pairwise_pair.2 fun _ => ⟨disjoint_compl_right, disjoint_compl_left⟩
    · simp
    · simp only
      rw [Finset.sum_pair hss]

/-- If `ν ≤ μ` are finite measures and `|h| ≤ C`, then
`|∫ h dμ − ∫ h dν| ≤ C (μ(X) − ν(X))`. -/
theorem fp_abs_integral_sub_le_of_le [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hle : ν ≤ μ) {h : X → ℝ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) :
    |∫ x, h x ∂μ - ∫ x, h x ∂ν| ≤ C * (μ.real univ - ν.real univ) := by
  have : IsFiniteMeasure (μ - ν) := isFiniteMeasure_of_le μ Measure.sub_le
  have hρ : μ - ν + ν = μ := Measure.sub_add_cancel_of_le hle
  have hint : ∀ (ρ : Measure X) [IsFiniteMeasure ρ], Integrable h ρ := fun ρ _ =>
    (integrable_const C).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have h1 : ∫ x, h x ∂μ = ∫ x, h x ∂(μ - ν) + ∫ x, h x ∂ν := by
    conv_lhs => rw [← hρ]
    exact integral_add_measure (hint _) (hint _)
  have h2 : μ.real univ = (μ - ν).real univ + ν.real univ := by
    conv_lhs => rw [← hρ]
    exact measureReal_add_apply
  rw [h1, add_sub_cancel_right, h2, add_sub_cancel_right]
  have := norm_integral_le_of_norm_le_const (μ := μ - ν) (f := h) (C := C)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  rwa [Real.norm_eq_abs] at this

/-- **Integrals and the total-variation norm.** For finite measures `μ`, `ν` and measurable `h`
with `|h| ≤ C`, `|∫ h dμ − ∫ h dν| ≤ C ‖μ − ν‖_TV` (§11.3, used in (2) on p. 522). -/
theorem fp_abs_integral_sub_le [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |h x| ≤ C) : |∫ x, h x ∂μ - ∫ x, h x ∂ν| ≤ C * fpTVNorm μ ν := by
  obtain ⟨s, hs, hpos, hneg⟩ := hahn_decomposition μ ν
  have hint : ∀ (ρ : Measure X) [IsFiniteMeasure ρ], Integrable h ρ := fun ρ _ =>
    (integrable_const C).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hle1 : ν.restrict s ≤ μ.restrict s := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hpos _ (ht.inter hs) inter_subset_right
  have hle2 : μ.restrict sᶜ ≤ ν.restrict sᶜ := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hneg _ (ht.inter hs.compl) inter_subset_right
  have e1 := fp_abs_integral_sub_le_of_le hle1 hm hC
  have e2 := fp_abs_integral_sub_le_of_le hle2 hm hC
  rw [measureReal_restrict_apply_univ, measureReal_restrict_apply_univ] at e1 e2
  have hsplit : ∫ x, h x ∂μ - ∫ x, h x ∂ν = (∫ x in s, h x ∂μ - ∫ x in s, h x ∂ν) -
      (∫ x in sᶜ, h x ∂ν - ∫ x in sᶜ, h x ∂μ) := by
    rw [← integral_add_compl hs (hint μ), ← integral_add_compl hs (hint ν)]
    ring
  have hTV := fp_le_tvNorm_pair μ ν hs
  have hsub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    simpa only [Real.norm_eq_abs] using norm_sub_le a b
  calc |∫ x, h x ∂μ - ∫ x, h x ∂ν|
      ≤ |∫ x in s, h x ∂μ - ∫ x in s, h x ∂ν| + |∫ x in sᶜ, h x ∂ν - ∫ x in sᶜ, h x ∂μ| := by
        rw [hsplit]; exact hsub _ _
    _ ≤ C * (μ.real s - ν.real s) + C * (ν.real sᶜ - μ.real sᶜ) := add_le_add e1 e2
    _ ≤ C * (|μ.real s - ν.real s| + |μ.real sᶜ - ν.real sᶜ|) := by
        rw [mul_add]
        refine add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _) hC0)
          (mul_le_mul_of_nonneg_left ?_ hC0)
        rw [abs_sub_comm]
        exact le_abs_self _
    _ ≤ C * fpTVNorm μ ν := mul_le_mul_of_nonneg_left hTV hC0

/-! ### Assumption 17.3 and Lemma 17.5 -/

/-- **Assumption 17.3** (pp. 520–521). For every `ε > 0` there is `δ > 0` with
`‖π(x, ·) − π(x̂, ·)‖_TV < ε` whenever `|x − x̂| < δ`. (Each `π(x, ·)` is a probability measure;
this is assumed separately.) -/
def FPAssumption17_3 [PseudoMetricSpace X] [MeasurableSpace X] (π : X → Measure X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x xh : X, dist x xh < δ → fpTVNorm (π x) (π xh) < ε

/-- A constant (serially independent) transition function satisfies Assumption 17.3. -/
theorem fpAssumption17_3_const [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) :
    FPAssumption17_3 (fun _ : X => μ) := by
  intro ε hε
  refine ⟨1, one_pos, fun _ _ _ => ?_⟩
  have : Nonempty {P : Finset (Set X) // FPIsFinPartition P} :=
    ⟨⟨{univ}, fpIsFinPartition_univ⟩⟩
  simp only [fpTVNorm, sub_self, abs_zero, Finset.sum_const_zero, ciSup_const]
  exact hε

/-- The operator `(Tf)(x) = ∫ G[x, x′, f(x′)] π(x, dx′)` ((1), p. 521). -/
noncomputable def fpIntOp [MeasurableSpace X] (π : X → Measure X) (G : X → X → ℝ → ℝ)
    (f : X → ℝ) (x : X) : ℝ :=
  ∫ x', G x x' (f x') ∂(π x)

/-- The integrand `x′ ↦ G[x, x′, f(x′)]` is continuous when `G` is jointly continuous on
`X × X × D` and `f` is continuous with values in `D`. -/
theorem fp_integrand_continuous [TopologicalSpace X] {D : Set ℝ} {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    (x : X) {f : X → ℝ} (hf : Continuous f) (hfD : ∀ x', f x' ∈ D) :
    Continuous fun x' => G x x' (f x') :=
  hGc.comp_continuous (continuous_const.prodMk (continuous_id.prodMk hf)) fun x' =>
    ⟨mem_univ _, mem_univ _, hfD x'⟩

/-- A `D`-valued `G` with `D` bounded is bounded by some `B ≥ 0`. -/
theorem fp_G_bound {D : Set ℝ} (hD : Bornology.IsBounded D) {G : X → X → ℝ → ℝ}
    (hGD : ∀ x x' y, y ∈ D → G x x' y ∈ D) :
    ∃ B, 0 ≤ B ∧ (∀ y ∈ D, |y| ≤ B) ∧ ∀ x x' y, y ∈ D → |G x x' y| ≤ B := by
  obtain ⟨C, hC⟩ := hD.exists_norm_le
  have hyB : ∀ y ∈ D, |y| ≤ max C 0 := fun y hy => by
    have := hC y hy
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  exact ⟨max C 0, le_max_right _ _, hyB, fun x x' y hy => hyB _ (hGD x x' y hy)⟩

/-- **Lemma 17.5** (p. 521). Let `π` satisfy Assumption 17.3, `D ⊆ ℝ` be bounded,
`F` the bounded continuous `D`-valued functions on `X`, and `G : X × X × D → D` continuous and
uniformly continuous in its first argument (uniformly in `(x′, y)`). Then the family
`T(F) = {Tf : f ∈ F}` is bounded and equicontinuous. -/
theorem lemma_17_5 [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {π : X → Measure X} (hπ : ∀ x, IsProbabilityMeasure (π x)) (hA : FPAssumption17_3 π)
    {D : Set ℝ} (hD : Bornology.IsBounded D) {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    (hGD : ∀ x x' y, y ∈ D → G x x' y ∈ D)
    (hGu : ∀ ε > 0, ∃ δ > 0, ∀ x xh : X, dist x xh < δ → ∀ x', ∀ y ∈ D,
      |G x x' y - G xh x' y| < ε) :
    (∃ B, ∀ f : X →ᵇ ℝ, (∀ x', f x' ∈ D) → ∀ x, |fpIntOp π G f x| ≤ B) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ x xh : X, dist x xh < δ → ∀ f : X →ᵇ ℝ, (∀ x', f x' ∈ D) →
        |fpIntOp π G f x - fpIntOp π G f xh| < ε := by
  obtain ⟨B, hB0, -, hGB⟩ := fp_G_bound hD hGD
  have hint : ∀ (x x₀ : X) (f : X →ᵇ ℝ), (∀ x', f x' ∈ D) →
      Integrable (fun x' => G x x' (f x')) (π x₀) := fun x x₀ f hf =>
    (integrable_const B).mono'
      (fp_integrand_continuous hGc x f.continuous hf).measurable.aestronglyMeasurable
      (ae_of_all _ fun x' => by
        rw [Real.norm_eq_abs]; exact hGB _ _ _ (hf x'))
  refine ⟨⟨B, fun f hf x => ?_⟩, fun ε hε => ?_⟩
  · have := norm_integral_le_of_norm_le_const (μ := π x) (C := B)
      (f := fun x' => G x x' (f x'))
      (ae_of_all _ fun x' => by rw [Real.norm_eq_abs]; exact hGB _ _ _ (hf x'))
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  · obtain ⟨δ₁, hδ₁, h₁⟩ := hGu (ε / 3) (by positivity)
    obtain ⟨δ₂, hδ₂, h₂⟩ := hA (ε / (3 * (B + 1))) (by positivity)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x xh hxx f hf => ?_⟩
    have e1 : |∫ x', G x x' (f x') ∂(π x) - ∫ x', G xh x' (f x') ∂(π x)| ≤ ε / 3 := by
      rw [← integral_sub (hint x x f hf) (hint xh x f hf)]
      have := norm_integral_le_of_norm_le_const (μ := π x) (C := ε / 3)
        (f := fun x' => G x x' (f x') - G xh x' (f x'))
        (ae_of_all _ fun x' => by
          rw [Real.norm_eq_abs]
          exact (h₁ x xh (lt_of_lt_of_le hxx (min_le_left _ _)) x' _ (hf x')).le)
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    have e2 : |∫ x', G xh x' (f x') ∂(π x) - ∫ x', G xh x' (f x') ∂(π xh)| ≤
        B * fpTVNorm (π x) (π xh) :=
      fp_abs_integral_sub_le _ _ (fp_integrand_continuous hGc xh f.continuous hf).measurable hB0
        fun x' => hGB _ _ _ (hf x')
    have e3 : B * fpTVNorm (π x) (π xh) ≤ ε / 3 := by
      have hTV := h₂ x xh (lt_of_lt_of_le hxx (min_le_right _ _))
      calc B * fpTVNorm (π x) (π xh) ≤ B * (ε / (3 * (B + 1))) :=
            mul_le_mul_of_nonneg_left hTV.le hB0
        _ ≤ ε / 3 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
    have habs := abs_add_le (∫ x', G x x' (f x') ∂(π x) - ∫ x', G xh x' (f x') ∂(π x))
      (∫ x', G xh x' (f x') ∂(π x) - ∫ x', G xh x' (f x') ∂(π xh))
    simp only [fpIntOp]
    rw [sub_add_sub_cancel] at habs
    linarith

/-- **Exercise 17.6** (p. 522). Under the hypotheses of Lemma 17.5 (only boundedness of `D` and
`π(x, ·)` being probability measures are used), if `G` is uniformly continuous in its third
argument, uniformly in `(x, x′)`, then `T` is (uniformly) continuous in the sup norm. -/
theorem ex_17_6 [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {π : X → Measure X} (hπ : ∀ x, IsProbabilityMeasure (π x)) {D : Set ℝ}
    (hD : Bornology.IsBounded D) {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    (hGD : ∀ x x' y, y ∈ D → G x x' y ∈ D)
    (hGu3 : ∀ ε > 0, ∃ δ > 0, ∀ x x' y y', y ∈ D → y' ∈ D → |y - y'| < δ →
      |G x x' y - G x x' y'| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ f g : X →ᵇ ℝ, (∀ x', f x' ∈ D) → (∀ x', g x' ∈ D) → dist f g < δ →
      ∀ x, |fpIntOp π G f x - fpIntOp π G g x| < ε := by
  obtain ⟨B, -, -, hGB⟩ := fp_G_bound hD hGD
  have hint : ∀ (x x₀ : X) (f : X →ᵇ ℝ), (∀ x', f x' ∈ D) →
      Integrable (fun x' => G x x' (f x')) (π x₀) := fun x x₀ f hf =>
    (integrable_const B).mono'
      (fp_integrand_continuous hGc x f.continuous hf).measurable.aestronglyMeasurable
      (ae_of_all _ fun x' => by
        rw [Real.norm_eq_abs]; exact hGB _ _ _ (hf x'))
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hGu3 (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun f g hf hg hfg x => ?_⟩
  have hpt : ∀ x', |G x x' (f x') - G x x' (g x')| < ε / 2 := fun x' => by
    have := (dist_coe_le_dist (f := f) (g := g) x').trans_lt hfg
    rw [Real.dist_eq] at this
    exact h x x' _ _ (hf x') (hg x') this
  simp only [fpIntOp]
  rw [← integral_sub (hint x x f hf) (hint x x g hg)]
  have := norm_integral_le_of_norm_le_const (μ := π x) (C := ε / 2)
    (f := fun x' => G x x' (f x') - G x x' (g x'))
    (ae_of_all _ fun x' => by rw [Real.norm_eq_abs]; exact (hpt x').le)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
  linarith

/-- **Schauder for the operator (1)** (pp. 522, 524–525). Let `X` be totally bounded (e.g. a
bounded subset of `ℝˡ`), `π` satisfy Assumption 17.3, `D ⊆ ℝ` be nonempty, closed, bounded and
convex, and `G : X × X × D → D` be continuous, uniformly continuous in its first argument and
uniformly continuous in its third. Then `T` maps `F` (the continuous `D`-valued functions) into
itself and has a fixed point in `F`. -/
theorem fp_exists_fixedPoint_intOp [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (hX : TotallyBounded (univ : Set X)) {π : X → Measure X}
    (hπ : ∀ x, IsProbabilityMeasure (π x)) (hA : FPAssumption17_3 π) {D : Set ℝ}
    (hDne : D.Nonempty) (hDcl : IsClosed D) (hDb : Bornology.IsBounded D) (hDc : Convex ℝ D)
    {G : X → X → ℝ → ℝ}
    (hGc : ContinuousOn (fun p : X × X × ℝ => G p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ D))
    (hGD : ∀ x x' y, y ∈ D → G x x' y ∈ D)
    (hGu : ∀ ε > 0, ∃ δ > 0, ∀ x xh : X, dist x xh < δ → ∀ x', ∀ y ∈ D,
      |G x x' y - G xh x' y| < ε)
    (hGu3 : ∀ ε > 0, ∃ δ > 0, ∀ x x' y y', y ∈ D → y' ∈ D → |y - y'| < δ →
      |G x x' y - G x x' y'| < ε) :
    ∃ f : X →ᵇ ℝ, (∀ x, f x ∈ D) ∧ ∀ x, f x = fpIntOp π G f x := by
  classical
  obtain ⟨⟨B, hB⟩, hequi⟩ := lemma_17_5 hπ hA hDb hGc hGD hGu
  have hT6 := ex_17_6 hπ hDb hGc hGD hGu3
  obtain ⟨B', hB'0, hDB', hGB'⟩ := fp_G_bound hDb hGD
  set F : Set (X →ᵇ ℝ) := {f | ∀ x, f x ∈ D} with hF
  have hTc : ∀ f ∈ F, Continuous (fpIntOp π G f) := fun f hf =>
    Metric.continuous_iff.2 fun x ε hε => by
      obtain ⟨δ, hδ, h⟩ := hequi ε hε
      refine ⟨δ, hδ, fun xh hxx => ?_⟩
      rw [Real.dist_eq]
      exact h xh x hxx f hf
  set T : (X →ᵇ ℝ) → (X →ᵇ ℝ) := fun f => if hf : f ∈ F then
    ofNormedAddCommGroup (fpIntOp π G f) (hTc f hf) B
      (fun x => by rw [Real.norm_eq_abs]; exact hB f hf x) else f with hT
  have hTF : ∀ f ∈ F, ⇑(T f) = fpIntOp π G f := fun f hf => by
    simp only [hT, hf, ↓reduceDIte, coe_ofNormedAddCommGroup]
  -- the set `F`
  have hFcl : IsClosed F := by
    have : F = ⋂ x, (fun f : X →ᵇ ℝ => f x) ⁻¹' D := by
      ext f
      simp [hF]
    rw [this]
    exact isClosed_iInter fun x => hDcl.preimage ((continuous_apply x).comp continuous_coe)
  have hFconv : Convex ℝ F := by
    intro f hf g hg a b ha hb hab x
    simpa using hDc (hf x) (hg x) ha hb hab
  have hFb : Bornology.IsBounded F := isBounded_iff_forall_norm_le.2
    ⟨B', fun f hf => (norm_le hB'0).2 fun x => by
      rw [Real.norm_eq_abs]; exact hDB' _ (hf x)⟩
  have hFne : F.Nonempty := by
    obtain ⟨d, hd⟩ := hDne
    exact ⟨const X d, fun _ => hd⟩
  -- `T(F) ⊆ F`
  have hmaps : MapsTo T F F := by
    intro f hf x
    rw [hTF f hf]
    have := hπ x
    refine hDc.integral_mem hDcl (ae_of_all _ fun x' => hGD _ _ _ (hf x')) ?_
    exact (integrable_const B').mono'
      (fp_integrand_continuous hGc x f.continuous hf).measurable.aestronglyMeasurable
      (ae_of_all _ fun x' => by rw [Real.norm_eq_abs]; exact hGB' _ _ _ (hf x'))
  -- `T` is continuous on `F`
  have hcont : ContinuousOn T F := by
    refine Metric.continuousOn_iff.2 fun g hg ε hε => ?_
    obtain ⟨δ, hδ, h⟩ := hT6 (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun f hf hfg => ?_⟩
    have hle : dist (T f) (T g) ≤ ε / 2 := by
      refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun x => ?_
      rw [hTF f hf, hTF g hg, Real.dist_eq]
      exact (h f g hf hg hfg x).le
    linarith
  -- `T(F)` is relatively compact
  have hequiS : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → ∀ g ∈ T '' F, |g x - g y| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hequi ε hε
    refine ⟨δ, hδ, fun x y hxy => ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    rw [hTF f hf]
    exact h x y hxy f hf
  have htb := totallyBounded_of_equicontinuous hX (hFb.subset hmaps.image_subset) hequiS
  obtain ⟨f, hf, hTf⟩ := schauder_closed hFcl hFconv hFne hcont hmaps
    (htb.closure.isCompact_of_isClosed isClosed_closure)
  refine ⟨f, hf, fun x => ?_⟩
  have := congrArg (fun g : X →ᵇ ℝ => g x) hTf
  rw [← this, hTF f hf]

/-! ### Proposition 4 -/

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- **Proposition 4** (p. 522). Let `X = [a, b] ⊂ ℝ₊₊`, `π` a transition function on `X`
satisfying Assumption 17.3, and `H`, `V` satisfy Assumption 17.1. Then there is a continuous,
strictly positive (indeed bounded away from zero) `f* : X → ℝ₊₊` with
`f*(x) = ∫ φ[x′ ζ⁻¹(f*(x′))] π(x, dx′)` for all `x ∈ X`. -/
theorem proposition_4 (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {π : Icc a b → Measure (Icc a b)} (hπ : ∀ x, IsProbabilityMeasure (π x))
    (hA3 : FPAssumption17_3 π) :
    ∃ f : Icc a b →ᵇ ℝ, (∃ ε > 0, ∀ x, ε ≤ f x) ∧
      ∀ x, f x = ∫ x', fpPhi V' ((x' : ℝ) * fpZetaInv L H' (f x')) ∂(π x) := by
  obtain ⟨ε, hε, B, hεB, hup, hlow⟩ := fp_bounds hA ha hab
  set G : Icc a b → Icc a b → ℝ → ℝ := fun _ x' y => fpPhi V' ((x' : ℝ) * fpZetaInv L H' y)
    with hG
  have hX : TotallyBounded (univ : Set (Icc a b)) :=
    (isCompact_iff_isCompact_univ.1 isCompact_Icc).totallyBounded
  -- joint continuity of `(x′, y) ↦ φ(x′ ζ⁻¹(y))` on `[a, b] × [ε, B]`
  have hc2 : ContinuousOn (fun q : ℝ × ℝ => fpPhi V' (q.1 * fpZetaInv L H' q.2))
      (Icc a b ×ˢ Icc ε B) :=
    (fpPhi_continuousOn hA).comp (continuous_fst.continuousOn.mul
      ((fpZetaInv_continuousOn hA).comp continuous_snd.continuousOn
        fun q hq => hε.le.trans hq.2.1))
      fun q hq => mul_nonneg (ha.le.trans hq.1.1) (fpZetaInv_mem hA (hε.le.trans hq.2.1)).1
  have hGc : ContinuousOn (fun p : Icc a b × Icc a b × ℝ => G p.1 p.2.1 p.2.2)
      (univ ×ˢ univ ×ˢ Icc ε B) :=
    hc2.comp ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)).continuousOn
      fun p hp => ⟨p.2.1.2, hp.2.2⟩
  have hGD : ∀ x x' y, y ∈ Icc ε B → G x x' y ∈ Icc ε B := fun _ x' y hy =>
    ⟨(hlow x' x'.2 y hy.1).le, (hup x' x'.2 y (hε.le.trans hy.1)).2⟩
  have hGu : ∀ ε' > 0, ∃ δ > 0, ∀ x xh : Icc a b, dist x xh < δ → ∀ x', ∀ y ∈ Icc ε B,
      |G x x' y - G xh x' y| < ε' := fun ε' hε' =>
    ⟨1, one_pos, fun _ _ _ _ _ _ => by simp only [hG, sub_self, abs_zero]; exact hε'⟩
  have hGu3 : ∀ ε' > 0, ∃ δ > 0, ∀ x x' y y', y ∈ Icc ε B → y' ∈ Icc ε B → |y - y'| < δ →
      |G x x' y - G x x' y'| < ε' := by
    intro ε' hε'
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hc2) ε' hε'
    refine ⟨δ, hδ, fun _ x' y y' hy hy' hyy => ?_⟩
    have hd : dist ((x' : ℝ), y) ((x' : ℝ), y') < δ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]
      exact hyy
    have := h ((x' : ℝ), y) ⟨x'.2, hy⟩ ((x' : ℝ), y') ⟨x'.2, hy'⟩ hd
    rwa [Real.dist_eq] at this
  obtain ⟨f, hfD, hf⟩ := fp_exists_fixedPoint_intOp hX hπ hA3 (nonempty_Icc.2 hεB.le)
    isClosed_Icc (Metric.isBounded_Icc ε B) (convex_Icc ε B) hGc hGD hGu hGu3
  exact ⟨f, ⟨ε, hε, fun x => (hfD x).1⟩, hf⟩

/-- **The trivial solution of Proposition 4's equation.** `f ≡ 0` solves
`f(x) = ∫ φ[x′ ζ⁻¹(f(x′))] π(x, dx′)`, since `ζ⁻¹(0) = 0` and `φ(0) = 0`. -/
theorem proposition_4_zero_fixedPoint (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ}
    (π : Icc a b → Measure (Icc a b)) (x : Icc a b) :
    (0 : ℝ) = ∫ x', fpPhi V' ((x' : ℝ) * fpZetaInv L H' 0) ∂(π x) := by
  simp [fpZetaInv_zero hA, fpPhi_zero]

/-! ### Exercise 17.7 -/

/-- The operator of Exercise 17.7, `(Sn)(x) = ζ⁻¹[∫ φ(x′ n(x′)) π(x, dx′)]` (p. 525). -/
noncomputable def fpLabourOp {a b : ℝ} (π : Icc a b → Measure (Icc a b)) (L : ℝ)
    (H' V' : ℝ → ℝ) (n : Icc a b → ℝ) (x : Icc a b) : ℝ :=
  fpZetaInv L H' (∫ x', fpPhi V' ((x' : ℝ) * n x') ∂(π x))

/-- **Exercise 17.7 is trivial as stated**: `n ≡ 0` is always a fixed point of `S`. -/
theorem ex_17_7_zero (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ}
    (π : Icc a b → Measure (Icc a b)) : fpLabourOp π L H' V' (fun _ => 0) = fun _ => 0 := by
  funext x
  simp [fpLabourOp, fpPhi_zero, fpZetaInv_zero hA]

/-- **Exercise 17.7, "Why?" (from `f*` to `n*`).** If `f*` solves (8) of §17.1, then
`n* = ζ⁻¹ ∘ f*` is a fixed point of `S`. -/
theorem ex_17_7_why_of_f {a b : ℝ} (π : Icc a b → Measure (Icc a b)) {f : Icc a b → ℝ}
    (hf : ∀ x, f x = ∫ x', fpPhi V' ((x' : ℝ) * fpZetaInv L H' (f x')) ∂(π x)) (x : Icc a b) :
    fpZetaInv L H' (f x) = fpLabourOp π L H' V' (fun x => fpZetaInv L H' (f x)) x := by
  simp only [fpLabourOp]
  rw [← hf x]

/-- **Exercise 17.7, "Why?" (from `n*` to `f*`).** If `n* : X → [0, L)` is a fixed point of `S`,
then `f* = ζ ∘ n*` solves (8) of §17.1. -/
theorem ex_17_7_why_of_n (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ} (ha : 0 ≤ a)
    (π : Icc a b → Measure (Icc a b)) {n : Icc a b → ℝ} (hn : ∀ x, n x ∈ Ico 0 L)
    (hfix : ∀ x, n x = fpLabourOp π L H' V' n x) (x : Icc a b) :
    fpZeta H' (n x) =
      ∫ x', fpPhi V' ((x' : ℝ) * fpZetaInv L H' (fpZeta H' (n x'))) ∂(π x) := by
  have hI : ∫ x', fpPhi V' ((x' : ℝ) * fpZetaInv L H' (fpZeta H' (n x'))) ∂(π x) =
      ∫ x', fpPhi V' ((x' : ℝ) * n x') ∂(π x) := by
    congr 1
    funext x'
    rw [fpZetaInv_zeta hA (hn x')]
  rw [hI, hfix x, fpLabourOp]
  exact fpZeta_zetaInv hA (integral_nonneg fun x' =>
    fpPhi_nonneg hA (mul_nonneg (ha.trans x'.2.1) (hn x').1))

/-- **Exercise 17.7, corrected** (p. 525). Under the hypotheses of Proposition 4, the operator
`(Sn)(x) = ζ⁻¹[∫ φ(x′ n(x′)) π(x, dx′)]` has a continuous fixed point `n* : X → (0, L)` that is
bounded away from zero (so it is not the trivial fixed point `0`). -/
theorem ex_17_7 (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {π : Icc a b → Measure (Icc a b)} (hπ : ∀ x, IsProbabilityMeasure (π x))
    (hA3 : FPAssumption17_3 π) :
    ∃ n : Icc a b →ᵇ ℝ, (∃ η > 0, ∀ x, η ≤ n x) ∧ (∀ x, n x < L) ∧
      ∀ x, n x = fpLabourOp π L H' V' n x := by
  obtain ⟨f, ⟨ε, hε, hfε⟩, hf⟩ := proposition_4 hA ha hab hπ hA3
  have hf0 : ∀ x, 0 ≤ f x := fun x => hε.le.trans (hfε x)
  have hcont : Continuous fun x => fpZetaInv L H' (f x) :=
    (fpZetaInv_continuousOn hA).comp_continuous f.continuous hf0
  set n : Icc a b →ᵇ ℝ := ofNormedAddCommGroup (fun x => fpZetaInv L H' (f x)) hcont L
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (fpZetaInv_mem hA (hf0 x)).1]
      exact (fpZetaInv_mem hA (hf0 x)).2.le) with hn
  have hncoe : ⇑n = fun x => fpZetaInv L H' (f x) := coe_ofNormedAddCommGroup _ _ _ _
  refine ⟨n, ⟨fpZetaInv L H' ε, ?_, fun x => ?_⟩, fun x => ?_, fun x => ?_⟩
  · have := fpZetaInv_strictMonoOn hA (mem_Ici.2 le_rfl) (mem_Ici.2 hε.le) hε
    rwa [fpZetaInv_zero hA] at this
  · rw [hncoe]
    exact (fpZetaInv_strictMonoOn hA).monotoneOn (mem_Ici.2 hε.le) (mem_Ici.2 (hf0 x)) (hfε x)
  · rw [hncoe]
    exact (fpZetaInv_mem hA (hf0 x)).2
  · rw [hncoe]
    exact ex_17_7_why_of_f π hf x

end StokeyLucasPrescott.FixedPointArguments

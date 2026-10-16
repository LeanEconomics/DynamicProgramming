/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.Portmanteau

/-!
# Convergence-determining families and uniqueness

SLP §12.1, Theorems 12.4–12.6 and their corollaries, pp. 360–364.

* **Theorem 12.4** (`theorem_12_4`): if `𝒜` is closed under finite intersections and every open
  set is a countable union of members of `𝒜`, then `λₙ(A) → λ(A)` on `𝒜` gives `λₙ ⇒ λ`.
  Finite unions converge by inclusion–exclusion (`tendsto_finite_union`), and then condition (c)
  of Theorem 12.3 holds.
* **Theorem 12.5** (`theorem_12_5`): in a second countable metric space, it suffices that every
  ball `b(x, ε)` contain some `A ∈ 𝒜` with `x ∈ Å`. The book takes `S` a Borel subset of `ℝˡ`;
  every subset of `ℝˡ` is second countable, so the theorem applies to it.
* **Corollary** (`theorem_12_5_cor`): finite intersections of open balls with `λ`-null
  boundaries form a convergence-determining class (`IsConvDetermining`).
* **Theorem 12.6** (`theorem_12_6`): every Borel set lies between a closed and an open set whose
  measures differ by less than `ε`. Proved from Mathlib's regularity of finite measures on
  metric spaces.
* **Corollaries 1–2** (`theorem_12_6_cor1`, `theorem_12_6_cor2`): two probability measures that
  agree on closed sets, or on integrals of bounded continuous functions, are equal; so weak
  limits are unique (`convWeak_unique`), and a convergence-determining class determines measures
  (`IsConvDetermining.eq`, the book's "(Why?)" on p. 362).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

omit [MetricSpace S] [BorelSpace S] in
/-- Finite unions `⋃_{j<m} Aⱼ` of members of `𝒜` converge, by inclusion–exclusion. -/
theorem tendsto_finite_union {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) :
    ∀ m (A : ℕ → Set S), (∀ i, A i ∈ 𝒜) →
      Tendsto (fun n => (ls n).real (⋃ j ∈ Finset.range m, A j)) atTop
        (𝓝 (l.real (⋃ j ∈ Finset.range m, A j))) := by
  intro m
  induction m with
  | zero => intro A _; simp
  | succ m ih =>
    intro A hA
    have hU : (⋃ j ∈ Finset.range (m + 1), A j) = (⋃ j ∈ Finset.range m, A j) ∪ A m := by
      rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    have hI : (⋃ j ∈ Finset.range m, A j) ∩ A m = ⋃ j ∈ Finset.range m, (A j ∩ A m) := by
      rw [iUnion₂_inter]
    have hmU : MeasurableSet (⋃ j ∈ Finset.range m, A j) :=
      Finset.measurableSet_biUnion _ fun j _ => hmeas _ (hA j)
    have key : ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        μ.real (⋃ j ∈ Finset.range (m + 1), A j) = μ.real (⋃ j ∈ Finset.range m, A j) +
          μ.real (A m) - μ.real (⋃ j ∈ Finset.range m, (A j ∩ A m)) := by
      intro μ _
      rw [hU, ← hI]
      have := measureReal_union_add_inter (μ := μ) (s := ⋃ j ∈ Finset.range m, A j)
        (hmeas _ (hA m)) (measure_ne_top μ _) (measure_ne_top μ _)
      linarith
    simp_rw [key]
    exact ((ih A hA).add (h _ (hA m))).sub
      (ih (fun j => A j ∩ A m) fun j => hinter _ (hA j) _ (hA m))

/-- **Theorem 12.4.** If `𝒜` is closed under finite intersections and every open set is a
countable union of members of `𝒜`, then `λₙ(A) → λ(A)` for all `A ∈ 𝒜` implies `λₙ ⇒ λ`. -/
theorem theorem_12_4 {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (hopen : ∀ G, IsOpen G → ∃ T : Set (Set S), T.Countable ∧ T ⊆ 𝒜 ∧ ⋃₀ T = G)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) : ConvWeak ls l := by
  refine (theorem_12_3 ls l).2.1.2 fun G hG ε hε => ?_
  obtain ⟨T, hTc, hT𝒜, hTG⟩ := hopen G hG
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · rw [sUnion_empty] at hTG
    subst hTG
    exact Eventually.of_forall fun n => by simp; linarith
  obtain ⟨A, hAeq⟩ := hTc.exists_eq_range hTne
  have hA : ∀ i, A i ∈ 𝒜 := fun i => hT𝒜 (hAeq ▸ mem_range_self i)
  have hGA : G = ⋃ i, A i := by rw [← hTG, hAeq, sUnion_range]
  -- continuity from below
  set U : ℕ → Set S := fun m => ⋃ j ∈ Finset.range m, A j
  have hmono : Monotone U := fun m m' hmm' => biUnion_subset_biUnion_left
    (Finset.coe_subset.2 (Finset.range_subset_range.2 hmm'))
  have hUG : (⋃ m, U m) = G := by
    rw [hGA]
    ext x
    simp only [U, mem_iUnion, Finset.mem_range]
    exact ⟨fun ⟨_, j, _, hj⟩ => ⟨j, hj⟩, fun ⟨j, hj⟩ => ⟨j + 1, j, by omega, hj⟩⟩
  have hlim : Tendsto (fun m => l.real (U m)) atTop (𝓝 (l.real G)) := by
    have := tendsto_measure_iUnion_atTop (μ := l) hmono
    rw [hUG] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  obtain ⟨m, hm⟩ := (hlim.eventually (lt_mem_nhds (show l.real G - ε / 2 < l.real G by
    linarith))).exists
  filter_upwards [(tendsto_finite_union hmeas hinter h m A hA).eventually
    (lt_mem_nhds (show l.real (U m) - ε / 2 < l.real (U m) by linarith))] with n hn
  have := measureReal_mono (μ := ls n) (show U m ⊆ G from hUG ▸ subset_iUnion U m)
  simp only [U] at hn hm this
  linarith

/-- **Theorem 12.5.** In a second countable metric space (for instance any Borel `S ⊆ ℝˡ`), if
`𝒜` is closed under finite intersections and every ball `b(x, ε)` contains some `A ∈ 𝒜` with
`x ∈ Å`, then `λₙ(A) → λ(A)` for all `A ∈ 𝒜` implies `λₙ ⇒ λ`. -/
theorem theorem_12_5 [SecondCountableTopology S] {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (hball : ∀ x, ∀ ε > 0, ∃ A ∈ 𝒜, x ∈ interior A ∧ A ⊆ Metric.ball x ε)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) : ConvWeak ls l := by
  refine theorem_12_4 hmeas hinter (fun G hG => ?_) h
  -- for `x ∈ G` choose `Aₓ ∈ 𝒜` with `x ∈ Åₓ ⊆ Aₓ ⊆ G`
  have hx : ∀ x : G, ∃ A ∈ 𝒜, (x : S) ∈ interior A ∧ A ⊆ G := fun x => by
    obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.1 hG x x.2
    obtain ⟨A, hA, hxA, hAb⟩ := hball x ε hε
    exact ⟨A, hA, hxA, hAb.trans hεG⟩
  choose A hA hxA hAG using hx
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : G => interior (A x))
    fun _ => isOpen_interior
  have hcover : (⋃ x : G, interior (A x)) = G := by
    refine subset_antisymm (iUnion_subset fun x => interior_subset.trans (hAG x)) fun y hy => ?_
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hxA ⟨y, hy⟩⟩
  refine ⟨A '' T, hTc.image A, image_subset_iff.2 fun x _ => hA x, subset_antisymm ?_ ?_⟩
  · exact sUnion_subset fun _ ⟨x, _, hx⟩ => hx ▸ hAG x
  · intro y hy
    rw [← hcover, ← hTeq] at hy
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 hy
    exact ⟨A x, ⟨x, hxT, rfl⟩, interior_subset hyx⟩

/-- `𝒜` is a **convergence-determining class** (p. 362): `λₙ(A) → λ(A)` for all `A ∈ 𝒜` with
`λ(∂A) = 0` implies `λₙ ⇒ λ`. -/
def IsConvDetermining (𝒜 : Set (Set S)) : Prop :=
  ∀ (ls : ℕ → Measure S) (l : Measure S), (∀ n, IsProbabilityMeasure (ls n)) →
    IsProbabilityMeasure l →
      (∀ A ∈ 𝒜, l (frontier A) = 0 → Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) →
        ConvWeak ls l

omit [MeasurableSpace S] [BorelSpace S] in
/-- The boundary of a finite intersection lies in the union of the boundaries. -/
theorem frontier_iInter_fin_subset {m : ℕ} (s : Fin m → Set S) :
    frontier (⋂ i, s i) ⊆ ⋃ i, frontier (s i) := by
  intro x hx
  rw [frontier, interior_iInter_of_finite] at hx
  obtain ⟨hcl, hint⟩ := hx
  simp only [mem_iInter, not_forall] at hint
  obtain ⟨i, hi⟩ := hint
  exact mem_iUnion.2 ⟨i, closure_mono (iInter_subset s i) hcl, hi⟩

/-- Finite intersections of open balls. -/
def ballInters (S : Type*) [MetricSpace S] : Set (Set S) :=
  {A | ∃ m, ∃ c : Fin m → S, ∃ r : Fin m → ℝ, A = ⋂ i, Metric.ball (c i) (r i)}

/-- **Corollary to Theorem 12.5.** In a second countable metric space, finite intersections of
open balls form a convergence-determining class. -/
theorem theorem_12_5_cor [SecondCountableTopology S] : IsConvDetermining (ballInters S) := by
  intro ls l _ _ h
  -- the finite intersections of balls whose boundaries are `λ`-null
  set 𝒜 : Set (Set S) := {A | ∃ m, ∃ c : Fin m → S, ∃ r : Fin m → ℝ,
    (∀ i, l (frontier (Metric.ball (c i) (r i))) = 0) ∧ A = ⋂ i, Metric.ball (c i) (r i)}
  have hfr : ∀ A ∈ 𝒜, l (frontier A) = 0 := by
    rintro A ⟨m, c, r, hnull, rfl⟩
    refine measure_mono_null (frontier_iInter_fin_subset _) ?_
    exact measure_iUnion_null hnull
  refine theorem_12_5 (𝒜 := 𝒜) (fun A ⟨m, c, r, _, hA⟩ => hA ▸
    MeasurableSet.iInter fun i => Metric.isOpen_ball.measurableSet) ?_ ?_
    (fun A hA => h A (by obtain ⟨m, c, r, -, hA⟩ := hA; exact ⟨m, c, r, hA⟩) (hfr A hA))
  · rintro A ⟨m, c, r, hn, rfl⟩ B ⟨m', c', r', hn', rfl⟩
    refine ⟨m + m', Fin.append c c', Fin.append r r', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hn i
      · simpa using hn' i
    · ext x
      simp only [mem_inter_iff, mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩ i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simpa using h1 i
        · simpa using h2 i
      · intro h
        exact ⟨fun i => by simpa using h (Fin.castAdd m' i),
          fun i => by simpa using h (Fin.natAdd m i)⟩
  · intro x ε hε
    obtain ⟨rs, hrs, hpos⟩ := exists_null_frontiers_thickening l {x}
    obtain ⟨n, hn⟩ := (hrs.eventually (gt_mem_nhds hε)).exists
    refine ⟨Metric.ball x (rs n), ⟨1, fun _ => x, fun _ => rs n, fun _ => ?_, ?_⟩, ?_,
      Metric.ball_subset_ball hn.le⟩
    · simpa [Metric.thickening_singleton] using (hpos n).2
    · ext y; simp
    · rw [Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self (hpos n).1

/-- **Theorem 12.6.** For a probability measure on a metric space, every Borel set `B` lies
between a closed `A` and an open `C` with `λ(C) − λ(A) < ε`. -/
theorem theorem_12_6 (l : Measure S) [IsProbabilityMeasure l] {B : Set S} (hB : MeasurableSet B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A C, IsClosed A ∧ IsOpen C ∧ A ⊆ B ∧ B ⊆ C ∧ l.real C - l.real A < ε := by
  have hε2 : (ENNReal.ofReal (ε / 2)) ≠ 0 := by simp [hε]
  obtain ⟨A, hAB, hA, hlt⟩ := hB.exists_isClosed_lt_add (measure_ne_top l B) hε2
  obtain ⟨C, hBC, hC, hCl⟩ := B.exists_isOpen_lt_of_lt (l B + ENNReal.ofReal (ε / 2))
    (ENNReal.lt_add_right (measure_ne_top l B) hε2)
  refine ⟨A, C, hA, hC, hAB, hBC, ?_⟩
  have h1 : l.real B < l.real A + ε / 2 := by
    have := ENNReal.toReal_strict_mono (by finiteness) hlt
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  have h2 : l.real C < l.real B + ε / 2 := by
    have := ENNReal.toReal_strict_mono (by finiteness) hCl
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  linarith

/-- **Corollary 1 to Theorem 12.6.** Probability measures that agree on closed sets are equal. -/
theorem theorem_12_6_cor1 {l μ : Measure S} [IsProbabilityMeasure l] [IsProbabilityMeasure μ]
    (h : ∀ A, IsClosed A → l A = μ A) : l = μ := by
  have hr : ∀ A, IsClosed A → l.real A = μ.real A := fun A hA => by simp [Measure.real, h A hA]
  have hopen : ∀ C, IsOpen C → l.real C = μ.real C := fun C hC => by
    have := hr Cᶜ hC.isClosed_compl
    rwa [probReal_compl_eq_one_sub hC.measurableSet, probReal_compl_eq_one_sub hC.measurableSet,
      sub_right_inj] at this
  ext B hB
  have hle : ∀ (ν₁ ν₂ : Measure S) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂],
      (∀ A, IsClosed A → ν₁.real A = ν₂.real A) → (∀ C, IsOpen C → ν₁.real C = ν₂.real C) →
        ν₁.real B ≤ ν₂.real B := by
    intro ν₁ ν₂ _ _ hc ho
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨A, C, hA, hC, hAB, hBC, hlt⟩ := theorem_12_6 ν₂ hB hε
    calc ν₁.real B ≤ ν₁.real C := measureReal_mono hBC
      _ = ν₂.real C := ho C hC
      _ < ν₂.real A + ε := by linarith
      _ ≤ ν₂.real B + ε := by linarith [measureReal_mono (μ := ν₂) hAB]
  have h1 := hle l μ hr hopen
  have h2 := hle μ l (fun A hA => (hr A hA).symm) (fun C hC => (hopen C hC).symm)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
    (le_antisymm h1 h2)

/-- **Corollary 2 to Theorem 12.6.** Probability measures with the same integrals of all
bounded continuous functions are equal (Lemma 12.1 and Corollary 1). -/
theorem theorem_12_6_cor2 {l μ : Measure S} [IsProbabilityMeasure l] [IsProbabilityMeasure μ]
    (h : ∀ f : S →ᵇ ℝ, ∫ s, f s ∂l = ∫ s, f s ∂μ) : l = μ := by
  refine theorem_12_6_cor1 fun A hA => ?_
  obtain ⟨f, hc, -, -, h01, hlim⟩ := lemma_12_1 hA
  have heq : ∀ n, ∫ s, f n s ∂l = ∫ s, f n s ∂μ := fun n => h (toBCF (hc n) (h01 n))
  have := tendsto_nhds_unique (hlim l) ((hlim μ).congr fun n => (heq n).symm)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- Weak limits are unique (p. 364). -/
theorem convWeak_unique {ls : ℕ → Measure S} {l μ : Measure S} [IsProbabilityMeasure l]
    [IsProbabilityMeasure μ] (h1 : ConvWeak ls l) (h2 : ConvWeak ls μ) : l = μ :=
  theorem_12_6_cor2 fun f => tendsto_nhds_unique (h1 f) (h2 f)

/-- A convergence-determining class determines probability measures (p. 362, "(Why?)"): apply
the definition to the constant sequence `μ`. -/
theorem IsConvDetermining.eq {𝒜 : Set (Set S)} (h𝒜 : IsConvDetermining 𝒜) {l μ : Measure S}
    [IsProbabilityMeasure l] [IsProbabilityMeasure μ] (h : ∀ A ∈ 𝒜, l A = μ A) : l = μ := by
  have hw : ConvWeak (fun _ => μ) l := h𝒜 (fun _ => μ) l (fun _ => inferInstance) inferInstance
    fun A hA _ => by simp [Measure.real, h A hA]
  exact convWeak_unique hw (fun f => tendsto_const_nhds)

end StokeyLucasPrescott.ConvergenceApplications

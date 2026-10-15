/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib
import StochasticApplications.Correspondences

/-!
# The Measurable Selection Theorem

SLP §7.3, pp. 183–184: measurable selections and Theorem 7.6, which the book cites from
Hildenbrand (1974). It is proved here by **lexicographic minimization**.

A nonempty compact-valued correspondence `Φ : X → ℝᵐ` is *measurable* (`IsMeasCorr`) when
`{x : Φ(x) ∩ F ≠ ∅}` is measurable for every closed `F`. A compact-valued u.h.c. correspondence
on a metric space is measurable, since these sets are closed (`isMeasCorr_of_uhc`). For a
measurable `Φ`, the least `i`-th coordinate `x ↦ min {yᵢ : y ∈ Φ(x)}` is measurable
(`measurable_minCoord`), and the points of `Φ(x)` attaining it again form a measurable
correspondence (`IsMeasCorr.refine`): the key identity expresses the lower inverse through
rational thresholds. Minimizing the coordinates one after the other leaves a single point
whose coordinates are measurable functions (`theorem_7_6`).
-/

namespace StokeyLucasPrescott.StochasticApplications

open Set MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

/-- A **measurable selection** from `Γ` (SLP p. 183): a measurable `h` with `h(x) ∈ Γ(x)`. -/
def IsMeasurableSelection {Y : Type*} [MeasurableSpace Y] (Γ : X → Set Y) (h : X → Y) : Prop :=
  Measurable h ∧ ∀ x, h x ∈ Γ x

/-- A nonempty compact-valued correspondence whose lower inverses of closed sets are
measurable. -/
def IsMeasCorr (Φ : X → Set (Fin m → ℝ)) : Prop :=
  (∀ x, (Φ x).Nonempty ∧ IsCompact (Φ x)) ∧
    ∀ F : Set (Fin m → ℝ), IsClosed F → MeasurableSet {x | (Φ x ∩ F).Nonempty}

/-- The least `i`-th coordinate on `Φ(x)`. -/
noncomputable def minCoord (Φ : X → Set (Fin m → ℝ)) (i : Fin m) (x : X) : ℝ :=
  sInf ((fun y => y i) '' Φ x)

theorem minCoord_mem {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) (x : X) :
    ∃ y ∈ Φ x, y i = minCoord Φ i x := by
  have hK := ((hΦ.1 x).2.image (continuous_apply i))
  exact hK.sInf_mem ((hΦ.1 x).1.image _)

theorem minCoord_le {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) {x : X}
    {y : Fin m → ℝ} (hy : y ∈ Φ x) : minCoord Φ i x ≤ y i :=
  csInf_le ((hΦ.1 x).2.image (continuous_apply i)).bddBelow (mem_image_of_mem _ hy)

/-- The least coordinate is measurable: `{x : min yᵢ ≤ a} = {x : Φ(x) ∩ {yᵢ ≤ a} ≠ ∅}`. -/
theorem measurable_minCoord {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) :
    Measurable (minCoord Φ i) := by
  refine measurable_of_Iic fun a => ?_
  change MeasurableSet {x | minCoord Φ i x ≤ a}
  have heq : {x | minCoord Φ i x ≤ a} = {x | (Φ x ∩ {y | y i ≤ a}).Nonempty} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor
    · intro hx
      obtain ⟨y, hy, hyi⟩ := minCoord_mem hΦ i x
      exact ⟨y, hy, by rw [mem_ofPred_eq, hyi]; exact hx⟩
    · rintro ⟨y, hy, hya⟩
      exact (minCoord_le hΦ i hy).trans hya
  rw [heq]
  exact hΦ.2 _ (isClosed_le (continuous_apply i) continuous_const)

/-- The points of `Φ(x)` minimizing the `i`-th coordinate. -/
def refineCorr (Φ : X → Set (Fin m → ℝ)) (i : Fin m) (x : X) : Set (Fin m → ℝ) :=
  Φ x ∩ {y | y i = minCoord Φ i x}

/-- **The minimizers again form a measurable correspondence.** -/
theorem IsMeasCorr.refine {Φ : X → Set (Fin m → ℝ)} (hΦ : IsMeasCorr Φ) (i : Fin m) :
    IsMeasCorr (refineCorr Φ i) := by
  refine ⟨fun x => ⟨?_, ?_⟩, fun F hF => ?_⟩
  · obtain ⟨y, hy, hyi⟩ := minCoord_mem hΦ i x
    exact ⟨y, hy, hyi⟩
  · exact (hΦ.1 x).2.inter_right (isClosed_eq (continuous_apply i) continuous_const)
  · have heq : {x | (refineCorr Φ i x ∩ F).Nonempty} =
        ⋂ q : ℚ, ({x | (q : ℝ) ≤ minCoord Φ i x} ∪
          ⋃ n : ℕ, {x | (Φ x ∩ (F ∩ {y | y i ≤ q - 1 / ((n : ℝ) + 1)})).Nonempty}) := by
      ext x
      simp only [refineCorr, mem_ofPred_eq, mem_iInter, mem_union, mem_iUnion]
      constructor
      · rintro ⟨y, ⟨hy, hyi⟩, hyF⟩ q
        by_cases hq : (q : ℝ) ≤ minCoord Φ i x
        · exact Or.inl hq
        · push Not at hq
          right
          rw [mem_ofPred_eq] at hyi
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hq)
          exact ⟨n, y, hy, hyF, by rw [mem_ofPred_eq, hyi]; linarith⟩
      · intro hx
        by_contra hne
        set K := Φ x ∩ F
        have hKc : IsCompact K := (hΦ.1 x).2.inter_right hF
        have hall : ∀ y ∈ K, minCoord Φ i x < y i := fun y hy => by
          refine lt_of_le_of_ne (minCoord_le hΦ i hy.1) fun h => hne ⟨y, ⟨hy.1, h.symm⟩, hy.2⟩
        by_cases hKe : K.Nonempty
        · obtain ⟨y₀, hy₀, hmin⟩ := hKc.exists_isMinOn hKe (continuous_apply i).continuousOn
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (hall y₀ hy₀)
          rcases hx q with h | ⟨n, y, hy, hyF, hyq⟩
          · exact absurd h (not_le.2 hq1)
          · have : y₀ i ≤ y i := hmin ⟨hy, hyF⟩
            have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            rw [mem_ofPred_eq] at hyq
            linarith
        · obtain ⟨q, hq⟩ := exists_rat_gt (minCoord Φ i x)
          rcases hx q with h | ⟨n, y, hy, hyF, -⟩
          · exact absurd h (not_le.2 hq)
          · exact hKe ⟨y, hy, hyF⟩
    rw [heq]
    refine MeasurableSet.iInter fun q => ?_
    refine (measurableSet_le measurable_const (measurable_minCoord hΦ i)).union ?_
    exact MeasurableSet.iUnion fun n => hΦ.2 _
      (hF.inter (isClosed_le (continuous_apply i) continuous_const))

/-- The correspondences obtained by minimizing coordinates `0, 1, …, k − 1` in turn. -/
noncomputable def lexCorr (Γ : X → Set (Fin m → ℝ)) : ℕ → X → Set (Fin m → ℝ)
  | 0 => Γ
  | k + 1 => if h : k < m then refineCorr (lexCorr Γ k) ⟨k, h⟩ else lexCorr Γ k

theorem lexCorr_spec {Γ : X → Set (Fin m → ℝ)} (hΓ : IsMeasCorr Γ) (k : ℕ) :
    IsMeasCorr (lexCorr Γ k) ∧ (∀ x, lexCorr Γ k x ⊆ Γ x) ∧
      ∀ i : Fin m, (i : ℕ) < k → ∀ x, ∀ y ∈ lexCorr Γ k x, y i = minCoord (lexCorr Γ i) i x := by
  induction k with
  | zero => exact ⟨hΓ, fun _ => subset_rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    by_cases hk : k < m
    · have hdef : lexCorr Γ (k + 1) = refineCorr (lexCorr Γ k) ⟨k, hk⟩ := by
        simp only [lexCorr, hk, ↓reduceDIte]
      rw [hdef]
      refine ⟨h1.refine _, fun x => inter_subset_left.trans (h2 x), fun i hi x y hy => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
      · exact h3 i hlt x y hy.1
      · have : i = ⟨k, hk⟩ := Fin.ext heq
        subst this
        exact hy.2
    · have hdef : lexCorr Γ (k + 1) = lexCorr Γ k := by simp only [lexCorr, hk, ↓reduceDIte]
      rw [hdef]
      refine ⟨h1, h2, fun i hi => h3 i ?_⟩
      have := i.2
      omega

/-- **A compact-valued u.h.c. correspondence is measurable**: for closed `F`, the set
`{x : Γ(x) ∩ F ≠ ∅}` is closed. -/
theorem isMeasCorr_of_uhc {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {Γ : X → Set (Fin m → ℝ)} (hΓ : ∀ x, IsUHC Γ x) (hK : ∀ x, IsCompact (Γ x)) :
    IsMeasCorr Γ := by
  refine ⟨fun x => ⟨(hΓ x).1, hK x⟩, fun F hF => ?_⟩
  refine IsClosed.measurableSet (IsSeqClosed.isClosed fun xs x hxs hlim => ?_)
  choose ys hys using hxs
  obtain ⟨y, hy, φ, -, hφ⟩ := (hΓ x).2 xs hlim ys fun n => (hys n).1
  exact ⟨y, hy, hF.mem_of_tendsto hφ (Eventually.of_forall fun n => (hys (φ n)).2)⟩

/-- **Theorem 7.6 (Measurable Selection Theorem).** A nonempty compact-valued u.h.c.
correspondence `Γ` from a metric space `X` (with its Borel sets; the book's `X` is a Borel set
in `ℝˡ`) into `ℝᵐ` has a measurable selection. -/
theorem theorem_7_6 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {Γ : X → Set (Fin m → ℝ)} (hΓ : ∀ x, IsUHC Γ x) (hK : ∀ x, IsCompact (Γ x)) :
    ∃ h : X → Fin m → ℝ, IsMeasurableSelection Γ h := by
  have hM := isMeasCorr_of_uhc hΓ hK
  obtain ⟨h1, h2, h3⟩ := lexCorr_spec hM m
  refine ⟨fun x (i : Fin m) => minCoord (lexCorr Γ i) i x, ?_, fun x => ?_⟩
  · exact measurable_pi_iff.2 fun i => measurable_minCoord (lexCorr_spec hM i).1 i
  · obtain ⟨y, hy⟩ := (h1.1 x).1
    have : y = fun (i : Fin m) => minCoord (lexCorr Γ i) i x := funext fun i => h3 i i.2 x y hy
    change (fun (i : Fin m) => minCoord (lexCorr Γ i) i x) ∈ Γ x
    rw [← this]
    exact h2 x hy

/-- **Theorem 7.6 with a target set `T`** (SLP's `T ⊆ ℝᵐ`): if `Γ(x) ⊆ T` for all `x`, the
selection is a measurable map into `T` with its subspace σ-algebra. -/
theorem theorem_7_6_subtype {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {T : Set (Fin m → ℝ)} {Γ : X → Set (Fin m → ℝ)} (hΓ : ∀ x, IsUHC Γ x)
    (hK : ∀ x, IsCompact (Γ x)) (hT : ∀ x, Γ x ⊆ T) :
    ∃ h : X → T, Measurable h ∧ ∀ x, (h x : Fin m → ℝ) ∈ Γ x := by
  obtain ⟨h, hm, hmem⟩ := theorem_7_6 hΓ hK
  exact ⟨fun x => ⟨h x, hT x (hmem x)⟩, hm.subtype_mk, hmem⟩

end StokeyLucasPrescott.StochasticApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# The measurability problem

Miao, §6.2, pp. 161–162 (after Bertsekas and Shreve 1978). A two-period problem: choose
`a₀ ∈ A` and a measurable `π₁ : S → A` to maximise `∫ u(s₁, π₁(s₁)) P(s₀, a₀; ds₁)`
(`po_V0`). Backward induction gives `V₁*(s₁) = sup_a u(s₁, a)` (`po_V1star`) and
`V₀*(s₀) = sup_{a₀} ∫ V₁* dP(s₀, a₀; ·)` (`po_V0star`).

* `two_step_6_2`: the book's two-step argument as a theorem. With `u` measurable and bounded,
  `A` nonempty, `V₁*` **measurable** (needed for the integral in (6.11)) and, for every `ε > 0`, a
  **measurable** ε-maximiser `a₁*` (6.9) (needed for (6.10)), `V₀ = V₀*`. Step 1 (`V₀ ≤ V₀*`) is
  `two_step_6_2_step1` and needs only the measurability of `V₁*`.
* The projection identity, p. 162. **Correction:** the book prints
  `{s₁ : V₁(s₁) < c} = proj_{s₁} {(s₁, a₁) : u(s₁, a₁) < c}`, which is false for a supremum
  (`proj_identity_6_2_misprint`); the correct identity is
  `{V₁* > c} = proj {u > c}` (`proj_identity_6_2`), and so `{V₁* ≤ c}` is the complement of a
  projection.
* Blackwell's point (`blackwell_6_2`): for `u = 1_E` with `E ⊆ S × A` measurable,
  `V₁* = 1_{proj E}`, so `V₁*` is measurable if and only if the projection of `E` is.

**Not formalised:** an actual Borel set `E ⊆ ℝ²` with non-Borel projection (Souslin). Mathlib
v4.34.0 has analytic sets (`MeasureTheory.AnalyticSet`) and Lusin's separation theorem, but no
non-Borel analytic set and no Borel set with a non-Borel projection, so Blackwell's example is
stated for any measurable `E` whose projection is not measurable.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- `V₁*(s₁) = sup_{a₁ ∈ A} u(s₁, a₁)` (Miao, p. 161). -/
noncomputable def po_V1star (u : S × A → ℝ) (s : S) : ℝ := ⨆ a, u (s, a)

/-- `V₀*(s₀) = sup_{a₀ ∈ A} ∫ V₁*(s₁) P(s₀, a₀; ds₁)` (Miao, p. 161). -/
noncomputable def po_V0star (P : Kernel (S × A) S) (u : S × A → ℝ) (s₀ : S) : ℝ :=
  ⨆ a₀, ∫ s₁, po_V1star u s₁ ∂P (s₀, a₀)

/-- `V₀(s₀) = sup_{π = (π₀, π₁)} ∫ u(s₁, π₁(s₁)) P(s₀, π₀; ds₁)` over `π₀ ∈ A` and measurable
`π₁ : S → A` (Miao, p. 161). -/
noncomputable def po_V0 (P : Kernel (S × A) S) (u : S × A → ℝ) (s₀ : S) : ℝ :=
  ⨆ π : A × {f : S → A // Measurable f}, ∫ s₁, u (s₁, π.2.1 s₁) ∂P (s₀, π.1)

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem po_V1star_le [Nonempty A] {u : S × A → ℝ} {B : ℝ} (hB : ∀ x, |u x| ≤ B) (s : S) :
    po_V1star u s ≤ B :=
  ciSup_le fun _ => (le_abs_self _).trans (hB _)

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem po_le_V1star {u : S × A → ℝ} {B : ℝ} (hB : ∀ x, |u x| ≤ B) (s : S) (a : A) :
    u (s, a) ≤ po_V1star u s :=
  le_ciSup (f := fun a => u (s, a)) ⟨B, by rintro _ ⟨a, rfl⟩; exact (le_abs_self _).trans (hB _)⟩ a

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem po_abs_V1star_le [Nonempty A] {u : S × A → ℝ} {B : ℝ} (hB : ∀ x, |u x| ≤ B) (s : S) :
    |po_V1star u s| ≤ B := by
  obtain ⟨a⟩ := ‹Nonempty A›
  refine abs_le.2 ⟨?_, po_V1star_le hB s⟩
  linarith [po_le_V1star hB s a, neg_abs_le (u (s, a)), hB (s, a)]

theorem po_integrable_bdd {μ : Measure S} [IsFiniteMeasure μ] {f : S → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, |f s| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hB s)

theorem po_abs_integral_le {μ : Measure S} [IsProbabilityMeasure μ] {f : S → ℝ} {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) : |∫ s, f s ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
    (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hB s)
  simpa [Real.norm_eq_abs] using this

/-- **Step 1** of Miao, p. 161: if `V₁*` is measurable, then for every plan
`∫ u(s₁, π₁) dP ≤ ∫ V₁* dP ≤ V₀*(s₀)`, so `V₀ ≤ V₀*`. -/
theorem two_step_6_2_step1 [Nonempty A] {P : Kernel (S × A) S} [IsMarkovKernel P]
    {u : S × A → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hV1 : Measurable (po_V1star u)) (s₀ : S) : po_V0 P u s₀ ≤ po_V0star P u s₀ := by
  have : Nonempty {f : S → A // Measurable f} :=
    ⟨⟨fun _ => Classical.arbitrary A, measurable_const⟩⟩
  have hbdd : BddAbove (Set.range fun a₀ => ∫ s₁, po_V1star u s₁ ∂P (s₀, a₀)) :=
    ⟨B, by
      rintro _ ⟨a₀, rfl⟩
      exact (le_abs_self _).trans (po_abs_integral_le (po_abs_V1star_le hB))⟩
  refine ciSup_le fun π => ?_
  have hπm : Measurable fun s₁ => u (s₁, π.2.1 s₁) := hu.comp (measurable_id.prodMk π.2.2)
  refine le_trans (integral_mono (po_integrable_bdd hπm fun s => hB _)
    (po_integrable_bdd hV1 (po_abs_V1star_le hB)) fun s₁ => po_le_V1star hB s₁ _) ?_
  exact le_ciSup hbdd π.1

/-- **The two-step argument of §6.2** (Miao, pp. 161–162) as a theorem: with `A` nonempty, a
Markov kernel `P`, `u` measurable and bounded, `V₁*` measurable, and measurable ε-maximisers
`a₁*` (`u(s₁, a₁*(s₁)) + ε ≥ V₁*(s₁)`, (6.9)) for every `ε > 0`, the Principle of Optimality
`V₀ = V₀*` holds. -/
theorem two_step_6_2 [Nonempty A] {P : Kernel (S × A) S} [IsMarkovKernel P]
    {u : S × A → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hV1 : Measurable (po_V1star u))
    (hsel : ∀ ε : ℝ, 0 < ε → ∃ g : S → A, Measurable g ∧ ∀ s, po_V1star u s ≤ u (s, g s) + ε)
    (s₀ : S) : po_V0 P u s₀ = po_V0star P u s₀ := by
  refine le_antisymm (two_step_6_2_step1 hu hB hV1 s₀) ?_
  have : Nonempty {f : S → A // Measurable f} :=
    ⟨⟨fun _ => Classical.arbitrary A, measurable_const⟩⟩
  have hbdd : BddAbove (Set.range fun π : A × {f : S → A // Measurable f} =>
      ∫ s₁, u (s₁, π.2.1 s₁) ∂P (s₀, π.1)) :=
    ⟨B, by
      rintro _ ⟨π, rfl⟩
      exact (le_abs_self _).trans (po_abs_integral_le fun s => hB _)⟩
  refine ciSup_le fun a₀ => le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨g, hg, hgε⟩ := hsel ε hε
  have hgm : Measurable fun s₁ => u (s₁, g s₁) := hu.comp (measurable_id.prodMk hg)
  have h1 : ∫ s₁, po_V1star u s₁ ∂P (s₀, a₀) ≤ ∫ s₁, (u (s₁, g s₁) + ε) ∂P (s₀, a₀) :=
    integral_mono (po_integrable_bdd hV1 (po_abs_V1star_le hB))
      ((po_integrable_bdd hgm fun s => hB _).add (integrable_const ε)) hgε
  rw [integral_add (po_integrable_bdd hgm fun s => hB _) (integrable_const ε)] at h1
  have hc : ∫ _, ε ∂P (s₀, a₀) = ε := by simp
  rw [hc] at h1
  have h2 : ∫ s₁, u (s₁, g s₁) ∂P (s₀, a₀) ≤ po_V0 P u s₀ :=
    le_ciSup hbdd (a₀, ⟨g, hg⟩)
  linarith

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- **The projection identity**, Miao p. 162, corrected: for `u` bounded above,
`{s₁ : V₁*(s₁) > c} = proj_{s₁} {(s₁, a₁) : u(s₁, a₁) > c}`. -/
theorem proj_identity_6_2 [Nonempty A] {u : S × A → ℝ} {B : ℝ} (hB : ∀ x, |u x| ≤ B) (c : ℝ) :
    {s | c < po_V1star u s} = Prod.fst '' {x | c < u x} := by
  ext s
  simp only [Set.mem_image]
  constructor
  · intro h
    have hbdd : BddAbove (Set.range fun a => u (s, a)) :=
      ⟨B, by rintro _ ⟨a, rfl⟩; exact (le_abs_self _).trans (hB _)⟩
    obtain ⟨a, ha⟩ := (lt_ciSup_iff hbdd).1 h
    exact ⟨(s, a), ha, rfl⟩
  · rintro ⟨⟨s', a⟩, ha, rfl⟩
    exact lt_of_lt_of_le ha (po_le_V1star hB s' a)

/-- **The printed projection identity is false** (Miao, p. 162): with `S` a point, `A = Bool`,
`u(s, a) = 1` if `a` and `0` otherwise, and `c = 1/2`, `{V₁* < c} = ∅` but
`proj {u < c} = S`. -/
theorem proj_identity_6_2_misprint :
    let u : Unit × Bool → ℝ := fun x => if x.2 then 1 else 0
    {s | po_V1star u s < 1 / 2} ≠ Prod.fst '' {x | u x < 1 / 2} := by
  intro u
  have hB : ∀ x, |u x| ≤ 1 := fun x => by
    simp only [u]
    split_ifs <;> norm_num
  have h1 : ∀ s, 1 ≤ po_V1star u s := fun s => by
    have := po_le_V1star hB s true
    simpa [u] using this
  intro h
  have hmem : (((), false) : Unit × Bool).1 ∈ Prod.fst '' {x | u x < 1 / 2} :=
    Set.mem_image_of_mem _ (by simp [u])
  rw [← h] at hmem
  have := h1 ()
  have h2 : po_V1star u () < 1 / 2 := hmem
  linarith

omit [MeasurableSpace A] in
/-- **Blackwell's point** (Miao, p. 162): for `u = 1_E` with `E ⊆ S × A` measurable (and `A`
nonempty), `V₁* = 1_{proj E}`; hence `V₁*` is measurable if and only if the projection
`proj_{s₁} E` is a measurable set. -/
theorem blackwell_6_2 [Nonempty A] (E : Set (S × A)) :
    po_V1star (E.indicator 1) = (Prod.fst '' E).indicator 1 ∧
      (Measurable (po_V1star (E.indicator (1 : S × A → ℝ))) ↔ MeasurableSet (Prod.fst '' E)) := by
  have hB : ∀ x, |E.indicator (1 : S × A → ℝ) x| ≤ 1 := fun x => by
    by_cases hx : x ∈ E <;> simp [hx]
  have heq : po_V1star (E.indicator (1 : S × A → ℝ)) = (Prod.fst '' E).indicator 1 := by
    funext s
    by_cases hs : s ∈ Prod.fst '' E
    · obtain ⟨⟨s', a⟩, ha, rfl⟩ := hs
      rw [Set.indicator_of_mem (Set.mem_image_of_mem Prod.fst ha)]
      refine le_antisymm ((po_V1star_le hB s').trans le_rfl) ?_
      have := po_le_V1star hB s' a
      rwa [Set.indicator_of_mem ha] at this
    · rw [Set.indicator_of_notMem hs]
      refine le_antisymm (ciSup_le fun a => ?_) ?_
      · rw [Set.indicator_of_notMem fun h => hs ⟨(s, a), h, rfl⟩]
      · obtain ⟨a⟩ := ‹Nonempty A›
        have := po_le_V1star hB s a
        rwa [Set.indicator_of_notMem fun h => hs ⟨(s, a), h, rfl⟩] at this
  refine ⟨heq, ?_⟩
  rw [heq]
  exact measurable_indicator_const_iff 1

end Miao.FiniteHorizonDP

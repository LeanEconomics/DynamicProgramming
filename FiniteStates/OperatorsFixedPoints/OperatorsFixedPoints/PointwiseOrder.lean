/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OperatorsFixedPoints.Basics
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Lattice

/-!
# The pointwise order on `ℝ^X`

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.2.2 (pp. 55–59).

Under the pointwise order the infimum and supremum of `{u, v}` are the
pointwise minimum and maximum, and the same holds for finite families
(Exercises 2.2.18–2.2.19). Sublattices are closed under finite suprema and
infima (Exercise 2.2.20); a finite family has a greatest element iff its
pointwise maximum belongs to it (Example 2.2.7, Exercise 2.2.21); order
intervals in a sublattice intersect in order intervals (Exercise 2.2.22).

Lemma 2.2.1 lists the lattice inequalities and identities, Exercise 2.2.23
the `∧ c` bound, Lemma 2.2.2 the key estimate `|max f − max g| ≤ max |f − g|`
with its `min` twin (Exercise 2.2.24), and Lemma 2.2.3 shows the upper envelope
of finitely many contractions is a contraction.
-/

open Finset Set

namespace SargentStachurski.OperatorsFixedPoints

variable {X : Type*}

/-! ### Suprema and infima under the pointwise order (§2.2.2.1) -/

/-- p. 56: the pointwise minimum is the infimum of `{u, v}` in `(ℝ^X, ≤)`. -/
theorem isGLB_pair_pointwise (u v : X → ℝ) : IsGLB {u, v} (fun x => min (u x) (v x)) := by
  have : (fun x => min (u x) (v x)) = u ⊓ v := rfl
  rw [this]
  exact isGLB_pair

/-- Exercise 2.2.18 (p. 56): the pointwise maximum is the supremum of `{u, v}`. -/
theorem isLUB_pair_pointwise (u v : X → ℝ) : IsLUB {u, v} (fun x => max (u x) (v x)) := by
  have : (fun x => max (u x) (v x)) = u ⊔ v := rfl
  rw [this]
  exact isLUB_pair

/-- A sublattice of `ℝ^X` (p. 56): closed under `∨` and `∧`. -/
def IsSublattice (V : Set (X → ℝ)) : Prop := ∀ u ∈ V, ∀ v ∈ V, u ⊔ v ∈ V ∧ u ⊓ v ∈ V

/-- Example 2.2.6 (p. 56): `V₁ = {f ≥ 0}` is a sublattice. -/
theorem isSublattice_nonneg : IsSublattice {f : X → ℝ | ∀ x, 0 ≤ f x} := fun _ hu _ hv =>
  ⟨fun x => le_trans (hu x) (le_max_left _ _), fun x => le_min (hu x) (hv x)⟩

/-- Example 2.2.6 (p. 56): `V₂ = {f ≫ 0}` is a sublattice. -/
theorem isSublattice_pos : IsSublattice {f : X → ℝ | ∀ x, 0 < f x} := fun _ hu _ hv =>
  ⟨fun x => lt_of_lt_of_le (hu x) (le_max_left _ _), fun x => lt_min (hu x) (hv x)⟩

/-- Example 2.2.6 (p. 56): `V₃ = {|f| ≤ 1}` is a sublattice. -/
theorem isSublattice_abs_le_one : IsSublattice {f : X → ℝ | ∀ x, |f x| ≤ 1} := fun u hu v hv =>
  ⟨fun x => by
    rcases le_total (u x) (v x) with h | h
    · simpa [Pi.sup_apply, max_eq_right h] using hv x
    · simpa [Pi.sup_apply, max_eq_left h] using hu x,
  fun x => by
    rcases le_total (u x) (v x) with h | h
    · simpa [Pi.inf_apply, min_eq_left h] using hu x
    · simpa [Pi.inf_apply, min_eq_right h] using hv x⟩

/-- Exercise 2.2.19 (p. 56): the supremum of a finite family is its pointwise maximum, and the
infimum its pointwise minimum. -/
theorem sup'_apply_pointwise {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (v : ι → X → ℝ) (x : X) :
    s.sup' hs v x = s.sup' hs fun i => v i x :=
  Finset.sup'_apply hs v x

theorem inf'_apply_pointwise {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (v : ι → X → ℝ) (x : X) :
    s.inf' hs v x = s.inf' hs fun i => v i x :=
  Finset.inf'_apply hs v x

/-- Exercise 2.2.19 (p. 56): the finite supremum is the least upper bound of the family. -/
theorem isLUB_sup'_image {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (v : ι → X → ℝ) :
    IsLUB (v '' s) (s.sup' hs v) := by
  constructor
  · rintro _ ⟨i, hi, rfl⟩
    exact Finset.le_sup' v hi
  · intro g hg
    exact Finset.sup'_le hs v fun i hi => hg ⟨i, hi, rfl⟩

theorem isGLB_inf'_image {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (v : ι → X → ℝ) :
    IsGLB (v '' s) (s.inf' hs v) := by
  constructor
  · rintro _ ⟨i, hi, rfl⟩
    exact Finset.inf'_le v hi
  · intro g hg
    exact Finset.le_inf' hs v fun i hi => hg ⟨i, hi, rfl⟩

/-- Exercise 2.2.20 (p. 56): a sublattice contains the suprema and infima of its finite subsets. -/
theorem IsSublattice.sup'_mem {V : Set (X → ℝ)} (hV : IsSublattice V) {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {v : ι → X → ℝ} (hv : ∀ i ∈ s, v i ∈ V) : s.sup' hs v ∈ V :=
  Finset.sup'_mem V (fun u hu w hw => (hV u hu w hw).1) s hs v hv

theorem IsSublattice.inf'_mem {V : Set (X → ℝ)} (hV : IsSublattice V) {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {v : ι → X → ℝ} (hv : ∀ i ∈ s, v i ∈ V) : s.inf' hs v ∈ V :=
  Finset.inf'_mem V (fun u hu w hw => (hV u hu w hw).2) s hs v hv

/-- Example 2.2.7 and Exercise 2.2.21 (p. 57), first claim: if the pointwise maximum `v*` of a
finite family belongs to the family, it is the greatest element. -/
theorem isGreatest_of_sup'_mem {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (v : ι → X → ℝ)
    (h : s.sup' hs v ∈ v '' s) : IsGreatest (v '' s) (s.sup' hs v) :=
  ⟨h, (isLUB_sup'_image hs v).1⟩

/-- Example 2.2.7 and Exercise 2.2.21 (p. 57), second claim: if `v*` is not in the family, the
family has no greatest element. -/
theorem not_exists_isGreatest_of_sup'_notMem {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (v : ι → X → ℝ) (h : s.sup' hs v ∉ v '' s) : ¬ ∃ g, IsGreatest (v '' s) g := by
  rintro ⟨g, hg⟩
  have h1 : g = s.sup' hs v := hg.isLUB.unique (isLUB_sup'_image hs v)
  exact h (h1 ▸ hg.1)

/-- Exercise 2.2.22 (p. 57): the intersection of two order intervals of a sublattice is an order
interval of the sublattice, `[a₁, a₂] ∩ [b₁, b₂] = [a₁ ∨ b₁, a₂ ∧ b₂]`. -/
theorem Icc_inter_Icc_sublattice {V : Set (X → ℝ)} (hV : IsSublattice V) {a₁ a₂ b₁ b₂ : X → ℝ}
    (ha₁ : a₁ ∈ V) (ha₂ : a₂ ∈ V) (hb₁ : b₁ ∈ V) (hb₂ : b₂ ∈ V) :
    Icc a₁ a₂ ∩ Icc b₁ b₂ = Icc (a₁ ⊔ b₁) (a₂ ⊓ b₂) ∧ a₁ ⊔ b₁ ∈ V ∧ a₂ ⊓ b₂ ∈ V :=
  ⟨Icc_inter_Icc, (hV a₁ ha₁ b₁ hb₁).1, (hV a₂ ha₂ b₂ hb₂).2⟩

/-! ### Inequalities and identities (§2.2.2.2) -/

/-- Lemma 2.2.1 (i), p. 58: `|f + g| ≤ |f| + |g|`. -/
theorem abs_add_le_pointwise (f g : X → ℝ) : |f + g| ≤ |f| + |g| := fun x => abs_add_le (f x) (g x)

/-- Lemma 2.2.1 (ii), p. 58: `(f ∧ g) + h = (f + h) ∧ (g + h)`. -/
theorem inf_add_pointwise (f g h : X → ℝ) : (f ⊓ g) + h = (f + h) ⊓ (g + h) := by
  funext x
  simp only [Pi.add_apply, Pi.inf_apply]
  exact (min_add_add_right (f x) (g x) (h x)).symm

/-- Lemma 2.2.1 (ii), p. 58: `(f ∨ g) + h = (f + h) ∨ (g + h)`. -/
theorem sup_add_pointwise (f g h : X → ℝ) : (f ⊔ g) + h = (f + h) ⊔ (g + h) := by
  funext x
  simp only [Pi.add_apply, Pi.sup_apply]
  exact (max_add_add_right (f x) (g x) (h x)).symm

/-- Lemma 2.2.1 (iii), p. 58: `(f ∨ g) ∧ h = (f ∧ h) ∨ (g ∧ h)`. -/
theorem sup_inf_pointwise (f g h : X → ℝ) : (f ⊔ g) ⊓ h = (f ⊓ h) ⊔ (g ⊓ h) := inf_sup_right _ _ _

/-- Lemma 2.2.1 (iii), p. 58: `(f ∧ g) ∨ h = (f ∨ h) ∧ (g ∨ h)`. -/
theorem inf_sup_pointwise (f g h : X → ℝ) : (f ⊓ g) ⊔ h = (f ⊔ h) ⊓ (g ⊔ h) := sup_inf_right _ _ _

/-- The `min` form of Mathlib's `abs_max_sub_max_le_abs`: `|min a c − min b c| ≤ |a − b|`. -/
theorem abs_min_sub_min_le_abs' (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
  have h := abs_max_sub_max_le_abs (-a) (-b) (-c)
  rw [max_neg_neg, max_neg_neg, neg_sub_neg, neg_sub_neg, abs_sub_comm (min b c),
    abs_sub_comm b] at h
  exact h

/-- Lemma 2.2.1 (iv), p. 58: `|f ∧ h − g ∧ h| ≤ |f − g|`. -/
theorem abs_inf_sub_inf_le_pointwise (f g h : X → ℝ) : |f ⊓ h - g ⊓ h| ≤ |f - g| := fun x =>
  abs_min_sub_min_le_abs' (f x) (g x) (h x)

/-- Lemma 2.2.1 (v), p. 58: `|f ∨ h − g ∨ h| ≤ |f − g|`. -/
theorem abs_sup_sub_sup_le_pointwise (f g h : X → ℝ) : |f ⊔ h - g ⊔ h| ≤ |f - g| := fun x =>
  abs_max_sub_max_le_abs (f x) (g x) (h x)

/-- The scalar case of (2.3): for `a, b, c ≥ 0`, `(a + b) ∧ c ≤ a ∧ c + b ∧ c`. -/
theorem min_add_le_min_add_min {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    min (a + b) c ≤ min a c + min b c := by
  rcases le_total a c with hac | hac <;> rcases le_total b c with hbc | hbc
  · rw [min_eq_left hac, min_eq_left hbc]
    exact min_le_left _ _
  · rw [min_eq_left hac, min_eq_right hbc]
    exact (min_le_right _ _).trans (by linarith)
  · rw [min_eq_right hac, min_eq_left hbc]
    exact (min_le_right _ _).trans (by linarith)
  · rw [min_eq_right hac, min_eq_right hbc]
    exact (min_le_right _ _).trans (by linarith)

/-- (2.3), p. 58: for `f, g, h ∈ ℝ^X₊`, `(f + g) ∧ h ≤ (f ∧ h) + (g ∧ h)`. -/
theorem inf_add_le_pointwise {f g h : X → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hh : ∀ x, 0 ≤ h x) : (f + g) ⊓ h ≤ f ⊓ h + g ⊓ h := fun x =>
  min_add_le_min_add_min (hf x) (hg x) (hh x)

/-- Exercise 2.2.23 (p. 58): for `a, b, c ≥ 0`, `|a ∧ c − b ∧ c| ≤ |a − b| ∧ c`. -/
theorem abs_min_sub_min_le_min {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |min a c - min b c| ≤ min |a - b| c := by
  refine le_min (abs_min_sub_min_le_abs' a b c) ?_
  rw [abs_sub_le_iff]
  constructor
  · linarith [min_le_right a c, le_min hb hc]
  · linarith [min_le_right b c, le_min ha hc]

/-- Lemma 2.2.2 (p. 58): for finite nonempty `D`, `|max f − max g| ≤ max |f − g|`. -/
theorem abs_sup'_sub_sup'_le {D : Type*} [Fintype D] (hD : (univ : Finset D).Nonempty)
    (f g : D → ℝ) :
    |univ.sup' hD f - univ.sup' hD g| ≤ univ.sup' hD fun z => |f z - g z| := by
  -- `max f − max g ≤ max |f − g|`, then swap the roles
  have key : ∀ f g : D → ℝ,
      univ.sup' hD f - univ.sup' hD g ≤ univ.sup' hD fun z => |f z - g z| := by
    intro f g
    rw [sub_le_iff_le_add]
    refine Finset.sup'_le hD f fun z _ => ?_
    calc f z = (f z - g z) + g z := by ring
      _ ≤ |f z - g z| + g z := add_le_add (le_abs_self _) le_rfl
      _ ≤ (univ.sup' hD fun z => |f z - g z|) + univ.sup' hD g :=
          add_le_add (Finset.le_sup' (fun z => |f z - g z|) (mem_univ z))
            (Finset.le_sup' g (mem_univ z))
  rw [abs_sub_le_iff]
  refine ⟨key f g, ?_⟩
  have := key g f
  simpa [abs_sub_comm] using this

/-- Exercise 2.2.24 (p. 59): `|min f − min g| ≤ max |f − g|`. -/
theorem abs_inf'_sub_inf'_le {D : Type*} [Fintype D] (hD : (univ : Finset D).Nonempty)
    (f g : D → ℝ) :
    |univ.inf' hD f - univ.inf' hD g| ≤ univ.sup' hD fun z => |f z - g z| := by
  -- `min f = −max(−f)`, as in the book's solution
  have h1 : ∀ f : D → ℝ, univ.inf' hD f = -univ.sup' hD fun z => -f z := by
    intro f
    apply le_antisymm
    · rw [le_neg]
      exact Finset.sup'_le hD _ fun z _ => neg_le_neg (Finset.inf'_le f (mem_univ z))
    · refine Finset.le_inf' hD f fun z _ => ?_
      have := Finset.le_sup' (fun z => -f z) (mem_univ z)
      linarith
  rw [h1 f, h1 g, neg_sub_neg]
  have := abs_sup'_sub_sup'_le hD (fun z => -g z) (fun z => -f z)
  simpa only [neg_sub_neg] using this

/-! ### Upper envelopes (p. 59) -/

/-- The upper envelope `Tv = ⋁_σ T_σ v` of a finite family of self-maps (p. 59). -/
noncomputable def upperEnvelope {S : Type*} [Fintype S] (hS : (univ : Finset S).Nonempty)
    (T : S → (X → ℝ) → (X → ℝ)) (v : X → ℝ) : X → ℝ :=
  univ.sup' hS fun σ => T σ v

/-- The upper envelope of self-maps of a sublattice is a self-map of the sublattice (p. 59). -/
theorem upperEnvelope_mapsTo {S : Type*} [Fintype S] (hS : (univ : Finset S).Nonempty)
    {T : S → (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)} (hV : IsSublattice V)
    (hT : ∀ σ, MapsTo (T σ) V V) : MapsTo (upperEnvelope hS T) V V := fun _ hv =>
  hV.sup'_mem hS fun σ _ => hT σ hv

/-- Lemma 2.2.3 (p. 59): if each `T_σ` is a contraction of modulus `λ_σ` on a sublattice `V` in
the supremum norm, then the upper envelope is a contraction of modulus `max_σ λ_σ`. -/
theorem isContractionOn_upperEnvelope [Fintype X] {S : Type*} [Fintype S]
    (hS : (univ : Finset S).Nonempty) {T : S → (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)}
    (hV : IsSublattice V) {L : S → ℝ} (hT : ∀ σ, IsContractionOn (T σ) V (L σ)) :
    IsContractionOn (upperEnvelope hS T) V (univ.sup' hS L) := by
  have hL0 : 0 ≤ univ.sup' hS L := by
    obtain ⟨σ, -⟩ := hS
    exact (hT σ).nonneg.trans (Finset.le_sup' L (mem_univ σ))
  refine ⟨upperEnvelope_mapsTo hS hV fun σ => (hT σ).mapsTo, hL0, ?_, fun u hu v hv => ?_⟩
  · exact (Finset.sup'_lt_iff hS).2 fun σ _ => (hT σ).lt_one
  · rw [pi_norm_le_iff_of_nonneg (mul_nonneg hL0 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    simp only [upperEnvelope, Finset.sup'_apply]
    calc |(univ.sup' hS fun σ => T σ u x) - univ.sup' hS fun σ => T σ v x|
        ≤ univ.sup' hS fun σ => |T σ u x - T σ v x| := abs_sup'_sub_sup'_le hS _ _
      _ ≤ univ.sup' hS fun σ => L σ * ‖u - v‖ := by
          refine Finset.sup'_mono_fun fun σ _ => ?_
          have h1 := (hT σ).norm_sub_le u hu v hv
          have h2 : |T σ u x - T σ v x| ≤ ‖T σ u - T σ v‖ := by
            have := norm_le_pi_norm (T σ u - T σ v) x
            simpa [Real.norm_eq_abs] using this
          exact h2.trans h1
      _ ≤ (univ.sup' hS L) * ‖u - v‖ :=
          Finset.sup'_le hS _ fun σ _ =>
            mul_le_mul_of_nonneg_right (Finset.le_sup' L (mem_univ σ)) (norm_nonneg _)

end SargentStachurski.OperatorsFixedPoints

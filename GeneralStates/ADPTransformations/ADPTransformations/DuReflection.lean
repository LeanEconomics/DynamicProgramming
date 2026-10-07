/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.DuTheorem
import ADPTransformations.IsomorphicADPs

/-!
# Du's theorem for minimization

Sargent and Stachurski, *Dynamic Programming*, Volume 2, proof of Lemma 5.1.11 (ii) (p. 159).

The book obtains the min-results from the max-results "by Exercise 2.2.6". Exercise 2.2.6 turns
min-statements for `(V, 𝕋)` into max-statements for the dual `(V^∂, 𝕋)`, and `V^∂` is not an order
interval of a Banach lattice, so Theorem 4.1.11 does not apply to it directly. Here the reflection
`w ↦ −w` carries the order interval `[−b, −a]` onto `[a, b]^∂`:

* `ADP.reflect` is the ADP `T̃_σ w = −T_σ(−w)` on `[−b, −a]`, anti-isomorphic to `(V, 𝕋)`.
* It satisfies Du's conditions whenever `(V, 𝕋)` does, with concave and convex swapped.
* `theorem_4_1_11_min`: a min-regular ADP on `[a, b]` whose policy operators satisfy Du's
  conditions, with `𝕋` finite, satisfies the fundamental min-optimality properties, and min-VFI,
  min-OPI and min-HPI all converge (Theorems 4.1.11, 5.1.9 and 5.1.10).
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

namespace BanachLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
theorem neg_mem_Icc_neg {a b : E} (v : Icc a b) : -(v : E) ∈ Icc (-b) (-a) :=
  neg_mem_Icc_iff'.1 (by rw [neg_neg]; exact v.2)

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
theorem neg_mem_Icc_of_neg {a b : E} (w : Icc (-b) (-a)) : -(w : E) ∈ Icc a b :=
  neg_mem_Icc_iff'.2 w.2

/-- `w ↦ −w`, an order anti-isomorphism from `[−b, −a]` onto `[a, b]`. -/
def negIcc (a b : E) : Icc (-b) (-a) ≃o (Icc a b)ᵒᵈ where
  toFun w := OrderDual.toDual ⟨-(w : E), neg_mem_Icc_of_neg w⟩
  invFun v := ⟨-((OrderDual.ofDual v : Icc a b) : E), neg_mem_Icc_neg (OrderDual.ofDual v)⟩
  left_inv w := Subtype.ext (neg_neg (w : E))
  right_inv v := by
    change OrderDual.toDual (⟨-(-((OrderDual.ofDual v : Icc a b) : E)), _⟩ : Icc a b) = v
    exact congrArg OrderDual.toDual (Subtype.ext (neg_neg _))
  map_rel_iff' {w w'} := by
    change ((⟨-(w' : E), _⟩ : Icc a b) ≤ ⟨-(w : E), _⟩) ↔ w ≤ w'
    exact neg_le_neg_iff

end BanachLattice

namespace ADP

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] {a b : E}
  {P : Type*}

/-- The reflected ADP `T̃_σ w = −T_σ(−w)` on `[−b, −a]`. -/
def reflect (A : ADP (Icc a b) P) : ADP (Icc (-b) (-a)) P where
  T σ w := ⟨-(A.T σ ⟨-(w : E), BanachLattice.neg_mem_Icc_of_neg w⟩ : E),
    BanachLattice.neg_mem_Icc_neg _⟩
  mono σ _ _ h := neg_le_neg (A.mono σ (show (⟨_, _⟩ : Icc a b) ≤ ⟨_, _⟩ from neg_le_neg h))
  nonempty := A.nonempty

end ADP

namespace BanachLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]

variable {a b : E} {P : Type*}

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
/-- The reflection is anti-isomorphic to the original ADP under `w ↦ −w`. -/
theorem reflect_isAntiIsomorphic (A : ADP (Icc a b) P) :
    A.reflect.IsAntiIsomorphic A (negIcc a b) := fun _ _ =>
  Subtype.ext (neg_neg _)

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
theorem reflect_isFinite {A : ADP (Icc a b) P} (h : A.IsFinite) : A.reflect.IsFinite := by
  have : range A.reflect.T = (fun S : Icc a b → Icc a b => fun w : Icc (-b) (-a) =>
      (⟨-(S ⟨-(w : E), neg_mem_Icc_of_neg w⟩ : E), neg_mem_Icc_neg _⟩ : Icc (-b) (-a))) ''
        range A.T := by
    rw [← Set.range_comp]
    rfl
  change (range A.reflect.T).Finite
  rw [this]
  exact h.image _

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
theorem extendIcc_reflect (A : ADP (Icc a b) P) (σ : P) (w : Icc (-b) (-a)) :
    extendIcc (A.reflect.T σ) w = -extendIcc (A.T σ) (-(w : E)) := by
  rw [extendIcc_apply,
    show -(w : E) = ((⟨-(w : E), neg_mem_Icc_of_neg w⟩ : Icc a b) : E) from rfl, extendIcc_apply]
  rfl

omit [HasSolidNorm E] [CompleteSpace E] in
/-- Du's conditions pass to the reflection, with concave and convex swapped. -/
theorem duConditions_reflect (hab : a ≤ b) {A : ADP (Icc a b) P} {σ : P}
    (h : DuConditions a b (extendIcc (A.T σ))) :
    DuConditions (-b) (-a) (extendIcc (A.reflect.T σ)) := by
  set F := extendIcc (A.T σ)
  have hF : ∀ w ∈ Icc (-b) (-a), extendIcc (A.reflect.T σ) w = -F (-w) := fun w hw =>
    extendIcc_reflect A σ ⟨w, hw⟩
  have hsub : (-a) - (-b) = b - a := by abel
  have ha : -a ∈ Icc (-b) (-a) := ⟨neg_le_neg hab, le_rfl⟩
  have hb : -b ∈ Icc (-b) (-a) := ⟨le_rfl, neg_le_neg hab⟩
  rcases h with ⟨hconc, ε, hε0, hε1, hε⟩ | ⟨hconv, ε, hε0, hε1, hε⟩
  · refine Or.inr ⟨⟨convex_Icc _ _, fun x hx y hy s t hs ht hst => ?_⟩, ε, hε0, hε1, ?_⟩
    · have hxy : s • x + t • y ∈ Icc (-b) (-a) := convex_Icc _ _ hx hy hs ht hst
      have key := hconc.2 (neg_mem_Icc_iff'.2 hx) (neg_mem_Icc_iff'.2 hy) hs ht hst
      rw [hF _ hxy, hF x hx, hF y hy]
      have he : -(s • x + t • y) = s • -x + t • -y := by rw [smul_neg, smul_neg, neg_add]
      calc -F (-(s • x + t • y)) = -F (s • -x + t • -y) := by rw [he]
        _ ≤ -(s • F (-x) + t • F (-y)) := neg_le_neg key
        _ = s • -F (-x) + t • -F (-y) := by rw [smul_neg, smul_neg, neg_add]
    · rw [hF _ ha, neg_neg, hsub]
      calc -F a ≤ -(a + ε • (b - a)) := neg_le_neg hε
        _ = -a - ε • (b - a) := by abel
  · refine Or.inl ⟨⟨convex_Icc _ _, fun x hx y hy s t hs ht hst => ?_⟩, ε, hε0, hε1, ?_⟩
    · have hxy : s • x + t • y ∈ Icc (-b) (-a) := convex_Icc _ _ hx hy hs ht hst
      have key := hconv.2 (neg_mem_Icc_iff'.2 hx) (neg_mem_Icc_iff'.2 hy) hs ht hst
      rw [hF _ hxy, hF x hx, hF y hy]
      have he : -(s • x + t • y) = s • -x + t • -y := by rw [smul_neg, smul_neg, neg_add]
      calc s • -F (-x) + t • -F (-y) = -(s • F (-x) + t • F (-y)) := by
            rw [smul_neg, smul_neg, neg_add]
        _ ≤ -F (s • -x + t • -y) := neg_le_neg key
        _ = -F (-(s • x + t • y)) := by rw [he]
    · rw [hF _ hb, neg_neg, hsub]
      calc -b + ε • (b - a) = -(b - ε • (b - a)) := by abel
        _ ≤ -F b := neg_le_neg hε

/-- **Du's theorem for minimization**: a min-regular ADP on `[a, b]` whose policy operators
satisfy Du's conditions, with `𝕋` finite, satisfies the fundamental min-optimality properties,
and min-VFI, min-OPI and min-HPI all converge. -/
theorem theorem_4_1_11_min (hab : a ≤ b) (A : ADP (Icc a b) P) (hr : A.MinRegular)
    (hdu : ∀ σ, DuConditions a b (extendIcc (A.T σ))) (hfin : A.IsFinite) :
    ∃ hw : A.WellPosed, A.MinFundamentalOptimality hw ∧
      ∃ vstar, A.IsMinValueFunction vstar ∧ A.MinVFIConverges vstar ∧
        ∀ g, A.IsMinSelector g → A.MinOPIConverges g vstar ∧ A.MinHPIConverges hw g vstar := by
  have hanti := reflect_isAntiIsomorphic A
  have h8 := ADP.theorem_5_1_8 hanti
  have hrR : A.reflect.Regular := h8.2.1.2 hr
  obtain ⟨hwR, hFO, vstar, hv, hvfi, hconv⟩ := theorem_4_1_11 (neg_le_neg hab) A.reflect hrR
    (fun σ => duConditions_reflect hab (hdu σ)) (Or.inr (Or.inl (reflect_isFinite hfin)))
  have hw : A.WellPosed := h8.2.2.1.1 hwR
  have h9 := ADP.theorem_5_1_9 hanti hrR hwR hw
  have h10 := ADP.theorem_5_1_10 hanti hrR hwR hw vstar
  refine ⟨hw, h9.2.2.1 hFO, _, h9.2.1 vstar hv, h10.2.2.1.1 hvfi, fun g hg => ⟨?_, ?_⟩⟩
  · exact h10.2.2.2.1.1 (fun g' hg' => (hconv g' hg').1) g hg
  · exact h10.2.2.2.2.1 (fun g' hg' => (hconv g' hg').2) g hg

end BanachLattice

end SargentStachurski.ADPTransformations

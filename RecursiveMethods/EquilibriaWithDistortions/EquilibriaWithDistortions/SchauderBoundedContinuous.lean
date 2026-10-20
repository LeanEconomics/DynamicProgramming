/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.Schauder

/-!
# Schauder's theorem for spaces of bounded continuous functions (SLP Theorem 17.4)

SLP §17.4, p. 520. `X` is a bounded subset of `ℝˡ` and `C(X)` the space of bounded continuous
real functions on `X` with the sup norm (`X →ᵇ ℝ`). A family `G ⊆ C(X)` is *equicontinuous* in
the book's sense (p. 520) if for every `ε > 0` there is `δ > 0` with `|g x − g y| < ε` whenever
`|x − y| < δ`, for all `g ∈ G` (uniform equicontinuity).

* `totallyBounded_of_equicontinuous` (Arzelà–Ascoli, the half needed): on a totally bounded
  metric space `X`, a bounded equicontinuous family in `X →ᵇ ℝ` is totally bounded. Proof: for a
  finite `δ`-net `P ⊆ X`, the evaluation map at `P` sends the family to a bounded, hence totally
  bounded, subset of `ℝ^P`; two members whose values at `P` are `ε/4`-close are `3ε/4`-close
  everywhere.
* `theorem_17_4` (**Theorem 17.4**, Schauder): for `F ⊆ C(X)` nonempty, closed, bounded and convex
  and `T : F → F` continuous with `T(F)` equicontinuous, `T` has a fixed point. The image `T(F)` is
  totally bounded by the lemma above, so relatively compact in the Banach space `C(X)`, and
  `schauder_closed_subtype` applies.

The book's statement is correct as given: `X` need not be closed or compact, because boundedness of
`X ⊆ ℝˡ` already makes `X` totally bounded, which is all the argument uses. (Boundedness of `F` is
used only to bound `T(F)`.)
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Metric Set Filter Topology BoundedContinuousFunction

/-- **Arzelà–Ascoli (total boundedness).** On a totally bounded pseudometric space `X`, a bounded
family `S` of bounded continuous real functions that is equicontinuous in the sense of SLP p. 520
(a single `δ` for each `ε`, uniformly over `S` and over `X`) is totally bounded in the sup norm. -/
theorem totallyBounded_of_equicontinuous {X : Type*} [PseudoMetricSpace X]
    (hX : TotallyBounded (univ : Set X)) {S : Set (X →ᵇ ℝ)} (hS : Bornology.IsBounded S)
    (heq : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → ∀ g ∈ S, |g x - g y| < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set ε' := ε / 4 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδε⟩ := heq ε' hε'0
  obtain ⟨P, -, hPfin, hPcov⟩ := finite_approx_of_totallyBounded hX δ hδ
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hS
  have _ : Fintype P := hPfin.fintype
  set Φ : (X →ᵇ ℝ) → (P → ℝ) := fun g p => g p with hΦ
  have hΦS : TotallyBounded (Φ '' S) := by
    have hb : Bornology.IsBounded (Φ '' S) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨max R 0, ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun p => ?_
      exact (g.norm_coe_le_norm p).trans ((hR g hg).trans (le_max_left _ _))
    exact hb.isCompact_closure.totallyBounded.subset subset_closure
  obtain ⟨u, huS, hufin, hucov⟩ := finite_approx_of_totallyBounded hΦS ε' hε'0
  have hchoice : ∀ y, ∃ g : X →ᵇ ℝ, y ∈ Φ '' S → g ∈ S ∧ Φ g = y := by
    intro y
    by_cases hy : y ∈ Φ '' S
    · obtain ⟨g, hg, rfl⟩ := hy
      exact ⟨g, fun _ => ⟨hg, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose G hG using hchoice
  refine ⟨G '' u, hufin.image G, fun g hg => ?_⟩
  obtain ⟨y, hyu, hgy⟩ := mem_iUnion₂.1 (hucov ⟨g, hg, rfl⟩)
  obtain ⟨hGS, hGy⟩ := hG y (huS hyu)
  refine mem_iUnion₂.2 ⟨G y, mem_image_of_mem G hyu, ?_⟩
  rw [mem_ball]
  have hpt : ∀ p : P, |g p - G y p| < ε' := by
    intro p
    have h1 : dist (Φ g) (Φ (G y)) < ε' := by
      rw [hGy]
      exact hgy
    have h2 := (dist_le_pi_dist (Φ g) (Φ (G y)) p).trans_lt h1
    rwa [Real.dist_eq] at h2
  have hle : dist g (G y) ≤ 3 * ε' := by
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun x => ?_
    obtain ⟨p, hpP, hxp⟩ := mem_iUnion₂.1 (hPcov (mem_univ x))
    have h1 := hδε x p hxp g hg
    have h2 := hδε x p hxp (G y) hGS
    have h3 := hpt ⟨p, hpP⟩
    rw [Real.dist_eq]
    calc |g x - G y x| ≤ |g x - g p| + |g p - G y p| + |G y p - G y x| := by
          have := abs_sub_le (g x) (g p) (G y x)
          have := abs_sub_le (g p) (G y p) (G y x)
          linarith
      _ ≤ 3 * ε' := by
          rw [abs_sub_comm (G y p)]
          linarith
  linarith

/-- **Theorem 17.4 (Schauder fixed-point theorem)**, p. 520. Let `X` be a bounded subset of `ℝˡ`
and `C(X) = X →ᵇ ℝ` with the sup norm. Let `F ⊆ C(X)` be nonempty, closed, bounded and convex,
and `T : F → F` continuous with `T(F)` equicontinuous. Then `T` has a fixed point in `F`. -/
theorem theorem_17_4 {l : ℕ} {X : Set (EuclideanSpace ℝ (Fin l))} (hX : Bornology.IsBounded X)
    {F : Set (X →ᵇ ℝ)} (hne : F.Nonempty) (hcl : IsClosed F) (hbdd : Bornology.IsBounded F)
    (hconv : Convex ℝ F) {T : F → F} (hT : Continuous T)
    (hequi : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ →
      ∀ f : F, |(T f : X →ᵇ ℝ) x - (T f : X →ᵇ ℝ) y| < ε) :
    ∃ f : F, T f = f := by
  have hXtb : TotallyBounded (univ : Set X) := by
    have h := totallyBounded_preimage
      (isUniformEmbedding_subtype_val (p := fun x => x ∈ X)).isUniformInducing
      (hX.isCompact_closure.totallyBounded.subset subset_closure)
    rwa [Subtype.coe_preimage_self] at h
  set S : Set (X →ᵇ ℝ) := range fun f => (T f : X →ᵇ ℝ) with hS
  have hSF : S ⊆ F := by
    rintro _ ⟨f, rfl⟩
    exact (T f).2
  have heqS : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → ∀ g ∈ S, |g x - g y| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hequi ε hε
    refine ⟨δ, hδ, fun x y hxy => ?_⟩
    rintro _ ⟨f, rfl⟩
    exact h x y hxy f
  have htb := totallyBounded_of_equicontinuous hXtb (hbdd.subset hSF) heqS
  exact schauder_closed_subtype hcl hconv hne hT
    (htb.closure.isCompact_of_isClosed isClosed_closure)

end StokeyLucasPrescott.EquilibriaWithDistortions

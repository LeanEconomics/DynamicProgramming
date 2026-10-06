/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.EventuallyContracting

/-!
# Convex and concave RDPs

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.2.3 (pp. 272–274).

An RDP with `V = [v₁, v₂]` is convex if each `B(x, a, ·)` is convex on `V`, (8.36), and
`B(x, a, v₂) ≤ v₂(x) − δ[v₂(x) − v₁(x)]` for some `δ > 0`, (8.37); concave if each `B(x, a, ·)` is
concave, (8.38), and `B(x, a, v₁) ≥ v₁(x) + δ[v₂(x) − v₁(x)]`, (8.39).

* Exercise 8.2.9: the strict inequalities (8.40) and (8.41) give (8.37) and (8.39).
* Proposition 8.2.5: convex and concave RDPs are globally stable, by Du's theorem applied to each
  policy operator, so Theorem 8.1.1 applies.
* §8.2.3.2, Exercises 8.2.10–8.2.11: an MDP restricted to
  `V̂ = [(r₁ − ε)/(1 − β), (r₂ + ε)/(1 − β)]` is both convex and concave.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.RecursiveDecisionProcesses

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- `R` is a convex RDP on `[v₁, v₂]`, (8.36)–(8.37). -/
def IsConvexRDP (v₁ v₂ : X → ℝ) : Prop :=
  v₁ ≤ v₂ ∧ R.V = Icc v₁ v₂ ∧ (∀ x, ∀ a ∈ R.Γ x, ConvexOn ℝ (Icc v₁ v₂) (R.B x a)) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ a ∈ R.Γ x, R.B x a v₂ ≤ v₂ x - δ * (v₂ x - v₁ x)

/-- `R` is a concave RDP on `[v₁, v₂]`, (8.38)–(8.39). -/
def IsConcaveRDP (v₁ v₂ : X → ℝ) : Prop :=
  v₁ ≤ v₂ ∧ R.V = Icc v₁ v₂ ∧ (∀ x, ∀ a ∈ R.Γ x, ConcaveOn ℝ (Icc v₁ v₂) (R.B x a)) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ a ∈ R.Γ x, v₁ x + δ * (v₂ x - v₁ x) ≤ R.B x a v₁

/-- **Exercise 8.2.9** (p. 273), concave case: (8.41) `B(x, a, v₁) > v₁(x)` on `G` gives (8.39). -/
theorem exists_delta_concave {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂)
    (h : ∀ x, ∀ a ∈ R.Γ x, v₁ x < R.B x a v₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ a ∈ R.Γ x, v₁ x + δ * (v₂ x - v₁ x) ≤ R.B x a v₁ := by
  set w : X → ℝ := fun x => (R.Γ x).inf' (R.Γ_nonempty x) fun a => R.B x a v₁
  have hw : ∀ x, v₁ x < w x := fun x => by
    obtain ⟨a, ha, hmin⟩ := (R.Γ x).exists_min_image (fun a => R.B x a v₁) (R.Γ_nonempty x)
    have : w x = R.B x a v₁ :=
      le_antisymm (Finset.inf'_le _ ha) (Finset.le_inf' _ _ fun b hb => hmin b hb)
    rw [this]
    exact h x a ha
  obtain ⟨δ, hδ, hle⟩ := exists_delta_of_lt h12 hw
  refine ⟨δ, hδ, fun x a ha => ?_⟩
  have h1 := hle x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1
  exact h1.trans (Finset.inf'_le _ ha)

/-- **Exercise 8.2.9** (p. 273), convex case: (8.40) `B(x, a, v₂) < v₂(x)` on `G` gives (8.37). -/
theorem exists_delta_convex {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂)
    (h : ∀ x, ∀ a ∈ R.Γ x, R.B x a v₂ < v₂ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ a ∈ R.Γ x, R.B x a v₂ ≤ v₂ x - δ * (v₂ x - v₁ x) := by
  set w : X → ℝ := fun x => -(R.Γ x).sup' (R.Γ_nonempty x) fun a => R.B x a v₂
  have hw : ∀ x, (-v₂) x < w x := fun x => by
    obtain ⟨a, ha, hmax⟩ := (R.Γ x).exists_max_image (fun a => R.B x a v₂) (R.Γ_nonempty x)
    have : (R.Γ x).sup' (R.Γ_nonempty x) (fun a => R.B x a v₂) = R.B x a v₂ :=
      le_antisymm (Finset.sup'_le _ _ fun b hb => hmax b hb)
        (Finset.le_sup' (fun a => R.B x a v₂) ha)
    simp only [w, Pi.neg_apply, this, neg_lt_neg_iff]
    exact h x a ha
  obtain ⟨δ, hδ, hle⟩ := exists_delta_of_lt (neg_le_neg h12) hw
  refine ⟨δ, hδ, fun x a ha => ?_⟩
  have h1 := hle x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul, w] at h1
  have h2 := Finset.le_sup' (fun a => R.B x a v₂) ha
  linarith

/-- Pointwise concavity of `B(x, σ(x), ·)` makes `T_σ` concave on `[v₁, v₂]`. -/
theorem concaveOn_Tσ {v₁ v₂ : X → ℝ} (hc : ∀ x, ∀ a ∈ R.Γ x, ConcaveOn ℝ (Icc v₁ v₂) (R.B x a))
    {σ : X → A} (hσ : R.IsFeasible σ) : ConcaveOn ℝ (Icc v₁ v₂) (R.Tσ σ) :=
  ⟨convex_Icc v₁ v₂, fun v hv w hw a b ha hb hab x => by
    exact (hc x (σ x) (hσ x)).2 hv hw ha hb hab⟩

/-- Pointwise convexity of `B(x, σ(x), ·)` makes `T_σ` convex on `[v₁, v₂]`. -/
theorem convexOn_Tσ {v₁ v₂ : X → ℝ} (hc : ∀ x, ∀ a ∈ R.Γ x, ConvexOn ℝ (Icc v₁ v₂) (R.B x a))
    {σ : X → A} (hσ : R.IsFeasible σ) : ConvexOn ℝ (Icc v₁ v₂) (R.Tσ σ) :=
  ⟨convex_Icc v₁ v₂, fun v hv w hw a b ha hb hab x => by
    exact (hc x (σ x) (hσ x)).2 hv hw ha hb hab⟩

/-- **Proposition 8.2.5** (p. 273), concave case: a concave RDP is globally stable. -/
theorem IsConcaveRDP.isGloballyStable {R : RDP X A} {v₁ v₂ : X → ℝ}
    (h : R.IsConcaveRDP v₁ v₂) : R.IsGloballyStable := by
  obtain ⟨h12, hV, hc, δ, hδ, hB⟩ := h
  intro σ hσ
  rw [hV]
  have hmaps : MapsTo (R.Tσ σ) (Icc v₁ v₂) (Icc v₁ v₂) := hV ▸ R.Tσ_mapsTo hσ
  have hmono : MonotoneOn (R.Tσ σ) (Icc v₁ v₂) := hV ▸ R.Tσ_monotoneOn hσ
  refine du_concave h12 hmaps hmono (R.concaveOn_Tσ hc hσ) hδ fun x => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  exact hB x (σ x) (hσ x)

/-- **Proposition 8.2.5** (p. 273), convex case: a convex RDP is globally stable. -/
theorem IsConvexRDP.isGloballyStable {R : RDP X A} {v₁ v₂ : X → ℝ}
    (h : R.IsConvexRDP v₁ v₂) : R.IsGloballyStable := by
  obtain ⟨h12, hV, hc, δ, hδ, hB⟩ := h
  intro σ hσ
  rw [hV]
  have hmaps : MapsTo (R.Tσ σ) (Icc v₁ v₂) (Icc v₁ v₂) := hV ▸ R.Tσ_mapsTo hσ
  have hmono : MonotoneOn (R.Tσ σ) (Icc v₁ v₂) := hV ▸ R.Tσ_monotoneOn hσ
  refine du_convex h12 hmaps hmono (R.convexOn_Tσ hc hσ) hδ fun x => ?_
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  exact hB x (σ x) (hσ x)

end RDP

/-! ### Application to MDPs (§8.2.3.2) -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The constant bounds (8.42): `v₁ = (r₁ − ε)/(1 − β)` and `v₂ = (r₂ + ε)/(1 − β)`. -/
theorem isBoundedBy_eps {r₁ r₂ ε : ℝ} (hr : ∀ x a, r₁ ≤ M.r x a ∧ M.r x a ≤ r₂) (hε : 0 < ε) :
    M.toRDP.IsBoundedBy (fun _ => (r₁ - ε) / (1 - M.β)) (fun _ => (r₂ + ε) / (1 - M.β)) := by
  have hβ1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hP : ∀ x a (c : ℝ), ∑ x', c * M.P x a x' = c := fun x a c => by
    rw [← Finset.mul_sum, M.P_rowsum, mul_one]
  refine ⟨fun x => ?_, fun _ _ => mem_univ _, fun x a _ => ⟨?_, ?_⟩⟩
  · obtain ⟨a, -⟩ := M.Γ_nonempty x
    have := (hr x a).1.trans (hr x a).2
    exact div_le_div_of_nonneg_right (by linarith) hβ1.le
  · change (r₁ - ε) / (1 - M.β) ≤ M.r x a + M.β * ∑ x', (r₁ - ε) / (1 - M.β) * M.P x a x'
    rw [hP, div_le_iff₀ hβ1]
    have h1 := (hr x a).1
    have : M.β * ((r₁ - ε) / (1 - M.β)) * (1 - M.β) = M.β * (r₁ - ε) := by field_simp
    nlinarith [M.β_pos]
  · change M.r x a + M.β * ∑ x', (r₂ + ε) / (1 - M.β) * M.P x a x' ≤ (r₂ + ε) / (1 - M.β)
    rw [hP, le_div_iff₀ hβ1]
    have h1 := (hr x a).2
    have : M.β * ((r₂ + ε) / (1 - M.β)) * (1 - M.β) = M.β * (r₂ + ε) := by field_simp
    nlinarith [M.β_pos]

/-- The MDP aggregator is affine in `v`. -/
theorem toRDP_B_combo (x : X) (a : A) (v w : X → ℝ) {s t : ℝ} (hst : s + t = 1) :
    M.toRDP.B x a (s • v + t • w) = s • M.toRDP.B x a v + t • M.toRDP.B x a w := by
  simp only [toRDP_B, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : ∑ x', (s * v x' + t * w x') * M.P x a x' =
      s * ∑ x', v x' * M.P x a x' + t * ∑ x', w x' * M.P x a x' := by
    rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [e]
  obtain rfl : t = 1 - s := by linarith
  ring

/-- **Exercises 8.2.10–8.2.11** (p. 274): the MDP RDP restricted to `V̂` of (8.42) satisfies the
strict bounds (8.40)–(8.41) and is both convex and concave, hence globally stable. -/
theorem restrict_isConvex_isConcave {r₁ r₂ ε : ℝ} (hr : ∀ x a, r₁ ≤ M.r x a ∧ M.r x a ≤ r₂)
    (hε : 0 < ε) :
    let R := M.toRDP.restrictIcc (M.isBoundedBy_eps hr hε)
    R.IsConvexRDP (fun _ => (r₁ - ε) / (1 - M.β)) (fun _ => (r₂ + ε) / (1 - M.β)) ∧
      R.IsConcaveRDP (fun _ => (r₁ - ε) / (1 - M.β)) (fun _ => (r₂ + ε) / (1 - M.β)) := by
  intro R
  have hb := M.isBoundedBy_eps hr hε
  have hβ1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hP : ∀ x a (c : ℝ), ∑ x', c * M.P x a x' = c := fun x a c => by
    rw [← Finset.mul_sum, M.P_rowsum, mul_one]
  have haff : ∀ x a, ConvexOn ℝ (Icc (fun _ => (r₁ - ε) / (1 - M.β))
      (fun _ => (r₂ + ε) / (1 - M.β))) (R.B x a) ∧ ConcaveOn ℝ (Icc (fun _ => (r₁ - ε) / (1 - M.β))
      (fun _ => (r₂ + ε) / (1 - M.β))) (R.B x a) := fun x a =>
    ⟨⟨convex_Icc _ _, fun v _ w _ s t _ _ hst => (M.toRDP_B_combo x a v w hst).le⟩,
      ⟨convex_Icc _ _, fun v _ w _ s t _ _ hst => (M.toRDP_B_combo x a v w hst).ge⟩⟩
  -- (8.40) and (8.41)
  have h40 : ∀ x, ∀ a ∈ R.Γ x, R.B x a (fun _ => (r₂ + ε) / (1 - M.β)) < (r₂ + ε) / (1 - M.β) :=
    fun x a _ => by
      change M.r x a + M.β * ∑ x', (r₂ + ε) / (1 - M.β) * M.P x a x' < (r₂ + ε) / (1 - M.β)
      rw [hP, lt_div_iff₀ hβ1]
      have h1 := (hr x a).2
      have : M.β * ((r₂ + ε) / (1 - M.β)) * (1 - M.β) = M.β * (r₂ + ε) := by field_simp
      nlinarith [M.β_pos]
  have h41 : ∀ x, ∀ a ∈ R.Γ x, (r₁ - ε) / (1 - M.β) < R.B x a (fun _ => (r₁ - ε) / (1 - M.β)) :=
    fun x a _ => by
      change (r₁ - ε) / (1 - M.β) < M.r x a + M.β * ∑ x', (r₁ - ε) / (1 - M.β) * M.P x a x'
      rw [hP, div_lt_iff₀ hβ1]
      have h1 := (hr x a).1
      have : M.β * ((r₁ - ε) / (1 - M.β)) * (1 - M.β) = M.β * (r₁ - ε) := by field_simp
      nlinarith [M.β_pos]
  exact ⟨⟨hb.1, rfl, fun x a _ => (haff x a).1, R.exists_delta_convex hb.1 h40⟩,
    ⟨hb.1, rfl, fun x a _ => (haff x a).2, R.exists_delta_concave hb.1 h41⟩⟩

end MDP

end SargentStachurski.RecursiveDecisionProcesses

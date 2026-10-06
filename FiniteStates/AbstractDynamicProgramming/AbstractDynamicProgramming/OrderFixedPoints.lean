/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AbstractDynamicProgramming.LinearValuation
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.FixedPoints

/-!
# Fixed points of order-preserving maps: Knaster–Tarski and Du

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.1.1–§7.1.2.2
(pp. 213–217).

Restated from the `FiniteStates/NonlinearValuation` project (Chapter 7) for use in
Chapters 8–9; each chapter project is self-contained.

* Global stability relative to a set: a unique fixed point in `U` to which the
  iterates from every point of `U` converge.
* Theorem 7.1.1 (Knaster–Tarski) on an order interval `[v₁, v₂]` of `ℝ^X`: the
  fixed points of an order-preserving self-map form a nonempty set with least and
  greatest elements `a ≤ b`, and `Tᵏv₁ ≤ a ≤ b ≤ Tᵏv₂`. The interval is a complete
  lattice because `ℝ^X` is conditionally complete.
* Exercise 7.1.1: when `v₁ ≠ v₂`, the identity has a continuum of fixed points.
* Theorem 7.1.3 (Du): an order-preserving self-map of `[v₁, v₂]` is globally stable
  if it is concave with `Tv₁ ≥ v₁ + δ(v₂ − v₁)` for some `δ > 0` (condition (ii)),
  or with `Tv₁ ≫ v₁` (condition (i)), or convex with the mirror conditions (iii)
  and (iv). The book cites Du (1990) and Zhang (2012); the proof here tracks
  `λₖ = 1 − (1 − δ)ᵏ` with `Tᵏv₁ ≥ (1 − λₖ)v₁ + λₖTᵏv₂`, so that every orbit is
  squeezed between `Tᵏv₁` and `Tᵏv₂`, which are `(1 − δ)ᵏ‖v₂ − v₁‖` apart. The
  convex case follows by the reflection `v ↦ −T(−v)`.
* Exercise 7.1.6: composites of order-preserving concave maps are concave.
* Topological conjugacy preserves global stability (Vol. 1, p. 45), used for the
  Epstein–Zin operators.
-/

open Finset Filter Topology Function

namespace SargentStachurski.AbstractDynamicProgramming

/-! ### Global stability on a set -/

/-- `T` is globally stable on `U`: it has a fixed point `u` in `U`, `u` is the only fixed point in
`U`, and `Tᵏv → u` for every `v ∈ U`. -/
def GloballyStableOn {E : Type*} [TopologicalSpace E] (T : E → E) (U : Set E) : Prop :=
  ∃ u ∈ U, IsFixedPt T u ∧ (∀ v ∈ U, IsFixedPt T v → v = u) ∧
    ∀ v ∈ U, Tendsto (fun k : ℕ => T^[k] v) atTop (𝓝 u)

/-- Global stability on the whole space is global stability on `univ`. -/
theorem globallyStableOn_univ_iff {E : Type*} [TopologicalSpace E] (T : E → E) :
    GloballyStableOn T Set.univ ↔ GloballyStable T := by
  constructor
  · rintro ⟨u, -, hu, huniq, hconv⟩
    exact ⟨u, hu, fun v hv => huniq v (Set.mem_univ v) hv, fun v => hconv v (Set.mem_univ v)⟩
  · rintro ⟨u, hu, huniq, hconv⟩
    exact ⟨u, Set.mem_univ u, hu, fun v _ hv => huniq v hv, fun v _ => hconv v⟩

/-- A globally stable map has a unique fixed point in `U`. -/
theorem GloballyStableOn.existsUnique {E : Type*} [TopologicalSpace E] {T : E → E} {U : Set E}
    (h : GloballyStableOn T U) : ∃! u, u ∈ U ∧ IsFixedPt T u := by
  obtain ⟨u, hu, hfix, huniq, -⟩ := h
  exact ⟨u, ⟨hu, hfix⟩, fun v hv => huniq v hv.1 hv.2⟩

/-- Topological conjugacy (Vol. 1, p. 45): if `Φ` is continuous on `U`, maps `U` into `U'`, has a
two-sided inverse `Ψ` from `U'` onto `U`, and `Φ ∘ T = T' ∘ Φ` on `U`, then global stability of `T`
on `U` gives global stability of `T'` on `U'`. -/
theorem GloballyStableOn.of_conj {E E' : Type*} [TopologicalSpace E] [TopologicalSpace E']
    {T : E → E} {U : Set E} {T' : E' → E'} {U' : Set E'} (Φ : E → E') (Ψ : E' → E)
    (hΦ : Set.MapsTo Φ U U') (hΨ : Set.MapsTo Ψ U' U) (hΦΨ : ∀ u ∈ U', Φ (Ψ u) = u)
    (hΨΦ : ∀ u ∈ U, Ψ (Φ u) = u) (hΦc : ContinuousOn Φ U) (hT : Set.MapsTo T U U)
    (hconj : ∀ u ∈ U, Φ (T u) = T' (Φ u)) (h : GloballyStableOn T U) :
    GloballyStableOn T' U' := by
  obtain ⟨u, hu, hfix, huniq, hconv⟩ := h
  refine ⟨Φ u, hΦ hu, ?_, fun v hv hvfix => ?_, fun v hv => ?_⟩
  · change T' (Φ u) = Φ u
    rw [← hconj u hu, hfix.eq]
  · -- `Ψ v` is a fixed point of `T`
    have h1 : Φ (T (Ψ v)) = Φ (Ψ v) := by rw [hconj _ (hΨ hv), hΦΨ v hv, hvfix.eq]
    have h2 : IsFixedPt T (Ψ v) := by
      change T (Ψ v) = Ψ v
      rw [← hΨΦ _ (hT (hΨ hv)), h1, hΨΦ _ (hΨ hv)]
    rw [← hΦΨ v hv, huniq _ (hΨ hv) h2]
  · -- `T'ᵏ v = Φ (Tᵏ (Ψ v))`
    have hiter : ∀ k, T'^[k] v = Φ (T^[k] (Ψ v)) := by
      intro k
      induction k with
      | zero => simp [hΦΨ v hv]
      | succ k ih =>
        rw [iterate_succ_apply', ih, iterate_succ_apply', hconj _ (hT.iterate k (hΨ hv))]
    simp only [hiter]
    have hlim := hconv (Ψ v) (hΨ hv)
    have hwithin : Tendsto (fun k => T^[k] (Ψ v)) atTop (𝓝[U] u) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k => hT.iterate k (hΨ hv)⟩
    exact ((hΦc u hu).tendsto).comp hwithin

/-- Topological conjugacy preserves global stability in both directions. -/
theorem globallyStableOn_iff_of_conj {E E' : Type*} [TopologicalSpace E] [TopologicalSpace E']
    {T : E → E} {U : Set E} {T' : E' → E'} {U' : Set E'} (Φ : E → E') (Ψ : E' → E)
    (hΦ : Set.MapsTo Φ U U') (hΨ : Set.MapsTo Ψ U' U) (hΦΨ : ∀ u ∈ U', Φ (Ψ u) = u)
    (hΨΦ : ∀ u ∈ U, Ψ (Φ u) = u) (hΦc : ContinuousOn Φ U) (hΨc : ContinuousOn Ψ U')
    (hT : Set.MapsTo T U U) (hconj : ∀ u ∈ U, Φ (T u) = T' (Φ u)) :
    GloballyStableOn T U ↔ GloballyStableOn T' U' := by
  have hT' : Set.MapsTo T' U' U' := fun v hv => by
    rw [← hΦΨ v hv, ← hconj _ (hΨ hv)]
    exact hΦ (hT (hΨ hv))
  have hconj' : ∀ v ∈ U', Ψ (T' v) = T (Ψ v) := fun v hv => by
    rw [← hΦΨ v hv, ← hconj _ (hΨ hv), hΨΦ _ (hT (hΨ hv)), hΨΦ _ (hΨ hv)]
  exact ⟨fun h => h.of_conj Φ Ψ hΦ hΨ hΦΨ hΨΦ hΦc hT hconj,
    fun h => h.of_conj Ψ Φ hΨ hΦ hΨΦ hΦΨ hΨc hT' hconj'⟩

/-! ### Theorem 7.1.1: Knaster–Tarski on an order interval -/

variable {X : Type*}

/-- Iterates of an order-preserving self-map of `[v₁, v₂]` preserve the order. -/
theorem iterate_le_iterate_of_monotoneOn {v₁ v₂ : X → ℝ} {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂))
    {u w : X → ℝ} (hu : u ∈ Set.Icc v₁ v₂) (hw : w ∈ Set.Icc v₁ v₂) (huw : u ≤ w) (k : ℕ) :
    T^[k] u ≤ T^[k] w := by
  induction k with
  | zero => simpa using huw
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact hmono (hmaps.iterate k hu) (hmaps.iterate k hw) ih

/-- **Theorem 7.1.1 (Knaster–Tarski)** (p. 214): an order-preserving self-map `T` of `[v₁, v₂]` has
least and greatest fixed points `a ≤ b`, and `Tᵏv₁ ≤ a ≤ b ≤ Tᵏv₂` for all `k`. -/
theorem knaster_tarski {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂)) :
    ∃ a ∈ Set.Icc v₁ v₂, ∃ b ∈ Set.Icc v₁ v₂, IsFixedPt T a ∧ IsFixedPt T b ∧
      (∀ v ∈ Set.Icc v₁ v₂, IsFixedPt T v → a ≤ v ∧ v ≤ b) ∧
      ∀ k : ℕ, T^[k] v₁ ≤ a ∧ b ≤ T^[k] v₂ := by
  have : Fact (v₁ ≤ v₂) := ⟨h12⟩
  let f : Set.Icc v₁ v₂ →o Set.Icc v₁ v₂ :=
    ⟨fun w => ⟨T w.1, hmaps w.2⟩, fun w w' hww' => hmono w.2 w'.2 hww'⟩
  have hfa : IsFixedPt T f.lfp.1 := congrArg Subtype.val f.isFixedPt_lfp
  have hfb : IsFixedPt T f.gfp.1 := congrArg Subtype.val f.isFixedPt_gfp
  have hv1 : v₁ ∈ Set.Icc v₁ v₂ := ⟨le_rfl, h12⟩
  have hv2 : v₂ ∈ Set.Icc v₁ v₂ := ⟨h12, le_rfl⟩
  refine ⟨f.lfp.1, f.lfp.2, f.gfp.1, f.gfp.2, hfa, hfb, fun v hv hvfix => ?_, fun k => ⟨?_, ?_⟩⟩
  · have hv' : f ⟨v, hv⟩ = ⟨v, hv⟩ := Subtype.ext hvfix
    exact ⟨OrderHom.lfp_le_fixed f hv', OrderHom.le_gfp f hv'.ge⟩
  · have := iterate_le_iterate_of_monotoneOn hmaps hmono hv1 f.lfp.2 f.lfp.2.1 k
    rwa [(hfa.iterate k).eq] at this
  · have := iterate_le_iterate_of_monotoneOn hmaps hmono f.gfp.2 hv2 f.gfp.2.2 k
    rwa [(hfb.iterate k).eq] at this

/-- Exercise 7.1.1 (p. 214): if `v₁ ≠ v₂`, some order-preserving self-map of `[v₁, v₂]` (the
identity) has a continuum of fixed points, the segment `t ↦ v₁ + t(v₂ − v₁)`, `t ∈ [0, 1]`. -/
theorem exists_continuum_fixedPts {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) (hne : v₁ ≠ v₂) :
    ∃ T : (X → ℝ) → (X → ℝ), Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂) ∧
      MonotoneOn T (Set.Icc v₁ v₂) ∧ ∃ φ : ℝ → X → ℝ, Set.InjOn φ (Set.Icc 0 1) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t ∈ Set.Icc v₁ v₂ ∧ IsFixedPt T (φ t) := by
  refine ⟨id, fun v hv => hv, fun _ _ _ _ h => h, fun t => v₁ + t • (v₂ - v₁), ?_, fun t ht => ?_⟩
  · intro s _ t _ hst
    have h1 : (s - t) • (v₂ - v₁) = 0 := by
      have := congrArg (fun w => w - v₁) hst
      simp only [add_sub_cancel_left] at this
      rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.1 h1 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd (sub_eq_zero.1 h).symm hne
  · refine ⟨⟨fun x => ?_, fun x => ?_⟩, rfl⟩
    · have := mul_nonneg ht.1 (sub_nonneg.2 (h12 x))
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linarith
    · have := mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.2 (h12 x))
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linarith

/-! ### Theorem 7.1.3 (Du) -/

/-- **Theorem 7.1.3 (Du)** (p. 217), condition (ii): an order-preserving concave self-map of
`[v₁, v₂]` with `Tv₁ ≥ v₁ + δ(v₂ − v₁)` for some `δ > 0` is globally stable on `[v₁, v₂]`. -/
theorem du_concave {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂))
    (hconc : ConcaveOn ℝ (Set.Icc v₁ v₂) T) {δ : ℝ} (hδ : 0 < δ)
    (hT1 : v₁ + δ • (v₂ - v₁) ≤ T v₁) : GloballyStableOn T (Set.Icc v₁ v₂) := by
  set d := min δ 1 with hd
  have hd0 : 0 < d := lt_min hδ one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  have hdδ : d ≤ δ := min_le_left _ _
  have hv1 : v₁ ∈ Set.Icc v₁ v₂ := ⟨le_rfl, h12⟩
  have hv2 : v₂ ∈ Set.Icc v₁ v₂ := ⟨h12, le_rfl⟩
  have hT1' : ∀ x, v₁ x + d * (v₂ x - v₁ x) ≤ T v₁ x := fun x => by
    have h1 := hT1 x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1
    nlinarith [sub_nonneg.2 (h12 x)]
  set q : ℕ → ℝ := fun k => (1 - d) ^ k with hq
  have hq0 : ∀ k, 0 ≤ q k := fun k => pow_nonneg (by linarith) k
  have hq1 : ∀ k, q k ≤ 1 := fun k => pow_le_one₀ (by linarith) (by linarith)
  -- `Tᵏv₁ ≥ v₁ + (1 − qₖ)(Tᵏv₂ − v₁)`
  have key : ∀ k x, v₁ x + (1 - q k) * (T^[k] v₂ x - v₁ x) ≤ T^[k] v₁ x := by
    intro k
    induction k with
    | zero => intro x; simp [hq]
    | succ k ih =>
      intro x
      have hwk := hmaps.iterate k hv2
      have huk := hmaps.iterate k hv1
      set z : X → ℝ := q k • v₁ + (1 - q k) • T^[k] v₂ with hz
      have hzmem : z ∈ Set.Icc v₁ v₂ :=
        (convex_Icc v₁ v₂) hv1 hwk (hq0 k) (by linarith [hq1 k]) (by ring)
      have hzle : z ≤ T^[k] v₁ := fun y => by
        have := ih y
        simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      have hA := hmono hzmem huk hzle x
      have hB := hconc.2 hv1 hwk (hq0 k) (by linarith [hq1 k]) (by ring : q k + (1 - q k) = 1) x
      have hD := (hmaps hwk).2 x
      rw [iterate_succ_apply', iterate_succ_apply']
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hB
      have hqs : q (k + 1) = q k * (1 - d) := by simp only [hq]; ring
      rw [hqs]
      nlinarith [mul_nonneg (mul_nonneg (hq0 k) hd0.le) (sub_nonneg.2 hD),
        mul_le_mul_of_nonneg_left (hT1' x) (hq0 k)]
  -- the orbits of `v₁` and `v₂` are `qₖ(v₂ − v₁)` apart
  have gap : ∀ k x, T^[k] v₂ x - T^[k] v₁ x ≤ q k * (v₂ x - v₁ x) := fun k x => by
    have h1 := key k x
    have h2 := ((hmaps.iterate k hv2).2 x)
    nlinarith [mul_le_mul_of_nonneg_left (sub_le_sub_right h2 (v₁ x)) (hq0 k)]
  have hqlim : Tendsto q atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  obtain ⟨a, ha, -, -, hafix, -, -, -⟩ := knaster_tarski h12 hmaps hmono
  -- every orbit is squeezed onto `a`
  have hsq : ∀ v ∈ Set.Icc v₁ v₂, ∀ k x,
      a x - q k * (v₂ x - v₁ x) ≤ T^[k] v x ∧ T^[k] v x ≤ a x + q k * (v₂ x - v₁ x) := by
    intro v hv k x
    have hlo := iterate_le_iterate_of_monotoneOn hmaps hmono hv1 hv hv.1 k x
    have hhi := iterate_le_iterate_of_monotoneOn hmaps hmono hv hv2 hv.2 k x
    have halo := iterate_le_iterate_of_monotoneOn hmaps hmono hv1 ha ha.1 k x
    have hahi := iterate_le_iterate_of_monotoneOn hmaps hmono ha hv2 ha.2 k x
    rw [(hafix.iterate k).eq] at halo hahi
    have := gap k x
    constructor <;> linarith
  refine ⟨a, ha, hafix, fun v hv hvfix => ?_, fun v hv => ?_⟩
  · funext x
    have h1 : ∀ k, |v x - a x| ≤ q k * (v₂ x - v₁ x) := fun k => by
      have := hsq v hv k x
      rw [(hvfix.iterate k).eq] at this
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    have h2 : Tendsto (fun k => q k * (v₂ x - v₁ x)) atTop (𝓝 0) := by
      simpa using hqlim.mul_const (v₂ x - v₁ x)
    have h3 : |v x - a x| ≤ 0 := ge_of_tendsto' h2 h1
    exact sub_eq_zero.1 (abs_nonpos_iff.1 h3)
  · rw [tendsto_pi_nhds]
    intro x
    have h2 : Tendsto (fun k => q k * (v₂ x - v₁ x)) atTop (𝓝 0) := by
      simpa using hqlim.mul_const (v₂ x - v₁ x)
    have hl : Tendsto (fun k => a x - q k * (v₂ x - v₁ x)) atTop (𝓝 (a x)) := by
      simpa using (tendsto_const_nhds (x := a x)).sub h2
    have hu : Tendsto (fun k => a x + q k * (v₂ x - v₁ x)) atTop (𝓝 (a x)) := by
      simpa using (tendsto_const_nhds (x := a x)).add h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu (fun k => (hsq v hv k x).1)
      (fun k => (hsq v hv k x).2)

/-- Condition (i) of Theorem 7.1.3 implies condition (ii): if `Tv₁ ≫ v₁` there is a `δ > 0` with
`Tv₁ ≥ v₁ + δ(v₂ − v₁)` (p. 217). -/
theorem exists_delta_of_lt [Finite X] {v₁ v₂ w : X → ℝ} (h12 : v₁ ≤ v₂) (hw : ∀ x, v₁ x < w x) :
    ∃ δ : ℝ, 0 < δ ∧ v₁ + δ • (v₂ - v₁) ≤ w := by
  classical
  have := Fintype.ofFinite X
  set g : X → ℝ := fun x => (w x - v₁ x) / (v₂ x - v₁ x + 1) with hg
  have hgpos : ∀ x, 0 < g x := fun x =>
    div_pos (sub_pos.2 (hw x)) (by linarith [sub_nonneg.2 (h12 x)])
  set S : Finset ℝ := insert 1 (univ.image g) with hS
  have hSne : S.Nonempty := insert_nonempty _ _
  refine ⟨S.min' hSne, ?_, fun x => ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases mem_insert.1 hy with h | h
    · rw [h]; exact one_pos
    · obtain ⟨x, -, rfl⟩ := mem_image.1 h
      exact hgpos x
  · have hle : S.min' hSne ≤ g x :=
      min'_le _ _ (mem_insert_of_mem (mem_image_of_mem g (mem_univ x)))
    have hpos : 0 < S.min' hSne := by
      rw [Finset.lt_min'_iff]
      intro y hy
      rcases mem_insert.1 hy with h | h
      · rw [h]; exact one_pos
      · obtain ⟨x, -, rfl⟩ := mem_image.1 h
        exact hgpos x
    have h0 := sub_nonneg.2 (h12 x)
    have hden : 0 < v₂ x - v₁ x + 1 := by linarith
    have h1 : g x * (v₂ x - v₁ x) ≤ w x - v₁ x := by
      rw [hg]
      simp only
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [sub_pos.2 (hw x)]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_right hle h0]

/-- **Theorem 7.1.3 (Du)** (p. 217), condition (i): an order-preserving concave self-map of
`[v₁, v₂]` with `Tv₁ ≫ v₁` is globally stable on `[v₁, v₂]`. -/
theorem du_concave_of_lt [Finite X] {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂))
    (hconc : ConcaveOn ℝ (Set.Icc v₁ v₂) T) (hT1 : ∀ x, v₁ x < T v₁ x) :
    GloballyStableOn T (Set.Icc v₁ v₂) := by
  obtain ⟨δ, hδ, h⟩ := exists_delta_of_lt h12 hT1
  exact du_concave h12 hmaps hmono hconc hδ h

/-- `w ∈ [−v₂, −v₁]` iff `−w ∈ [v₁, v₂]`. -/
theorem neg_mem_Icc_iff {v₁ v₂ w : X → ℝ} : -w ∈ Set.Icc v₁ v₂ ↔ w ∈ Set.Icc (-v₂) (-v₁) := by
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨neg_le.1 h2, le_neg.1 h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨le_neg.2 h2, neg_le.2 h1⟩

/-- If the reflection `w ↦ −T(−w)` is globally stable on `[−v₂, −v₁]`, then `T` is globally stable
on `[v₁, v₂]`. -/
theorem globallyStableOn_of_reflect {v₁ v₂ : X → ℝ} {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂))
    (h : GloballyStableOn (fun w => -T (-w)) (Set.Icc (-v₂) (-v₁))) :
    GloballyStableOn T (Set.Icc v₁ v₂) := by
  refine h.of_conj (fun w => -w) (fun w => -w) (fun w hw => neg_mem_Icc_iff.2 hw)
    (fun w hw => by rw [← neg_mem_Icc_iff, neg_neg]; exact hw) (fun w _ => neg_neg w)
    (fun w _ => neg_neg w) continuous_neg.continuousOn (fun w hw => ?_) (fun w _ => by simp)
  rw [← neg_mem_Icc_iff]
  simpa using hmaps (neg_mem_Icc_iff.2 hw)

/-- **Theorem 7.1.3 (Du)** (p. 217), condition (iv): an order-preserving convex self-map of
`[v₁, v₂]` with `Tv₂ ≤ v₂ − δ(v₂ − v₁)` for some `δ > 0` is globally stable on `[v₁, v₂]`. -/
theorem du_convex {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂))
    (hconv : ConvexOn ℝ (Set.Icc v₁ v₂) T) {δ : ℝ} (hδ : 0 < δ)
    (hT2 : T v₂ ≤ v₂ - δ • (v₂ - v₁)) : GloballyStableOn T (Set.Icc v₁ v₂) := by
  have hmem : ∀ w ∈ Set.Icc (-v₂) (-v₁), -w ∈ Set.Icc v₁ v₂ := fun w hw => neg_mem_Icc_iff.2 hw
  refine globallyStableOn_of_reflect hmaps (du_concave (neg_le_neg h12) ?_ ?_ ?_ hδ ?_)
  · intro w hw
    rw [← neg_mem_Icc_iff, neg_neg]
    exact hmaps (hmem w hw)
  · intro u hu w hw huw
    exact neg_le_neg (hmono (hmem w hw) (hmem u hu) (neg_le_neg huw))
  · refine ⟨convex_Icc _ _, fun u hu w hw a b ha hb hab => ?_⟩
    have := hconv.2 (hmem u hu) (hmem w hw) ha hb hab
    have h2 : -(a • u + b • w) = a • -u + b • -w := by rw [neg_add, smul_neg, smul_neg]
    change a • -T (-u) + b • -T (-w) ≤ -T (-(a • u + b • w))
    rw [h2, smul_neg, smul_neg, ← neg_add]
    exact neg_le_neg this
  · intro x
    have := hT2 x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.neg_apply, neg_neg]
      at this ⊢
    linarith

/-- **Theorem 7.1.3 (Du)** (p. 217), condition (iii): an order-preserving convex self-map of
`[v₁, v₂]` with `Tv₂ ≪ v₂` is globally stable on `[v₁, v₂]`. -/
theorem du_convex_of_lt [Finite X] {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂))
    (hconv : ConvexOn ℝ (Set.Icc v₁ v₂) T) (hT2 : ∀ x, T v₂ x < v₂ x) :
    GloballyStableOn T (Set.Icc v₁ v₂) := by
  obtain ⟨δ, hδ, h⟩ := exists_delta_of_lt (neg_le_neg h12) (w := -T v₂)
    (fun x => by simpa using hT2 x)
  refine du_convex h12 hmaps hmono hconv hδ fun x => ?_
  have := h x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.neg_apply] at this ⊢
  linarith

/-- Exercise 7.1.6 (p. 217): if `F` and `G` are self-maps of a convex set `D`, `F` is order
preserving and both are concave, then `F ∘ G` is concave on `D`. -/
theorem concaveOn_comp {D : Set (X → ℝ)} {F G : (X → ℝ) → (X → ℝ)} (hG : Set.MapsTo G D D)
    (hFm : MonotoneOn F D) (hF : ConcaveOn ℝ D F) (hGc : ConcaveOn ℝ D G) :
    ConcaveOn ℝ D (F ∘ G) := by
  refine ⟨hF.1, fun u hu w hw a b ha hb hab => ?_⟩
  have h1 := hF.2 (hG hu) (hG hw) ha hb hab
  have hmem : a • G u + b • G w ∈ D := hF.1 (hG hu) (hG hw) ha hb hab
  have h2 := hFm hmem (hG (hF.1 hu hw ha hb hab)) (hGc.2 hu hw ha hb hab)
  exact h1.trans h2

end SargentStachurski.AbstractDynamicProgramming

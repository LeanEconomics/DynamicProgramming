/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Monotone.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Topkis's monotonicity theorem

Topkis (1978), "Minimizing a submodular function on a lattice"; Topkis (1998), *Supermodularity
and Complementarity*; Milgrom and Shannon (1994).

Let the state (or parameter) `x` range over a preorder and the action `a` over a linear order,
with finite feasible sets `Γ(x)` that are **ascending** in the strong set order:
`x ≤ x'`, `a ∈ Γ(x)`, `a' ∈ Γ(x')` give `min a a' ∈ Γ(x)` and `max a a' ∈ Γ(x')`. If the
objective `f(x, a)` has **increasing differences** — `f(x, a') − f(x, a)` is increasing in `x`
for `a ≤ a'` — then:

* `argmax_strongSetOrder`: the argmax sets are ascending in the strong set order;
* `topkis_gmax`, `topkis_lmax`: the greatest and the least maximizers are increasing in `x`;
* `topkis_strict`: with strictly increasing differences every selection from the argmax is
  increasing.

Increasing differences hold for `u(m(x) − g(a))` with `u` concave and `m`, `g` increasing
(`increasingDifferences_concave`: consumption is the residual of a budget), for objectives that
do not mix `x` and `a` (`increasingDifferences_of_sep`), for products of increasing functions
(`increasingDifferences_mul`), and are preserved by sums (`IncreasingDifferences.add`).
-/

open Finset

namespace DPExtensions.MonotonePolicies

variable {X A : Type*} [Preorder X] [LinearOrder A]

/-- `f` has increasing differences: `f(x, a') − f(x, a)` is increasing in `x` for `a ≤ a'`. -/
def IncreasingDifferences (f : X → A → ℝ) : Prop :=
  ∀ ⦃x x' : X⦄, x ≤ x' → ∀ ⦃a a' : A⦄, a ≤ a' → f x a' - f x a ≤ f x' a' - f x' a

/-- `f` has strictly increasing differences. -/
def StrictIncreasingDifferences (f : X → A → ℝ) : Prop :=
  ∀ ⦃x x' : X⦄, x < x' → ∀ ⦃a a' : A⦄, a < a' → f x a' - f x a < f x' a' - f x' a

/-- `Γ` is ascending in the strong set order. -/
def Ascending (Γ : X → Finset A) : Prop :=
  ∀ ⦃x x' : X⦄, x ≤ x' → ∀ a ∈ Γ x, ∀ a' ∈ Γ x', min a a' ∈ Γ x ∧ max a a' ∈ Γ x'

theorem IncreasingDifferences.add {f g : X → A → ℝ} (hf : IncreasingDifferences f)
    (hg : IncreasingDifferences g) : IncreasingDifferences fun x a => f x a + g x a :=
  fun _ _ hx _ _ ha => by linarith [hf hx ha, hg hx ha]

theorem IncreasingDifferences.const_mul {f : X → A → ℝ} (hf : IncreasingDifferences f) {c : ℝ}
    (hc : 0 ≤ c) : IncreasingDifferences fun x a => c * f x a :=
  fun _ _ hx _ _ ha => by nlinarith [hf hx ha]

/-- An objective that does not mix `x` and `a` has increasing differences. -/
theorem increasingDifferences_of_sep (g : X → ℝ) (h : A → ℝ) :
    IncreasingDifferences fun x a => g x + h a :=
  fun _ _ _ _ _ _ => by linarith

/-- `φ(x)ψ(a)` with `φ`, `ψ` increasing has increasing differences. -/
theorem increasingDifferences_mul {φ : X → ℝ} {ψ : A → ℝ} (hφ : Monotone φ) (hψ : Monotone ψ) :
    IncreasingDifferences fun x a => φ x * ψ a := fun _ _ hx _ _ ha => by
  nlinarith [hφ hx, hψ ha]

/-- For concave `u`, increments shrink: `s ≤ t` and `d ≥ 0` give
`u(t + d) − u(t) ≤ u(s + d) − u(s)`. -/
theorem concave_increment {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) {s t d : ℝ} (hst : s ≤ t)
    (hd : 0 ≤ d) : u (t + d) - u t ≤ u (s + d) - u s := by
  rcases eq_or_lt_of_le hd with h0 | hd'
  · subst h0
    simp
  have hden : 0 < t + d - s := by linarith
  set l := d / (t + d - s) with hl
  have hl0 : 0 ≤ l := div_nonneg hd hden.le
  have hl1 : l ≤ 1 := (div_le_one hden).2 (by linarith)
  have e1 : (1 - l) * s + l * (t + d) = s + d := by
    rw [hl]
    field_simp
    ring
  have e2 : l * s + (1 - l) * (t + d) = t := by
    rw [hl]
    field_simp
    ring
  have h1 := hu.2 (Set.mem_univ s) (Set.mem_univ (t + d)) (by linarith : 0 ≤ 1 - l) hl0
    (by ring : 1 - l + l = 1)
  have h2 := hu.2 (Set.mem_univ s) (Set.mem_univ (t + d)) hl0 (by linarith : 0 ≤ 1 - l)
    (by ring : l + (1 - l) = 1)
  simp only [smul_eq_mul] at h1 h2
  rw [e1] at h1
  rw [e2] at h2
  linarith

/-- **Budget-residual objectives**: `u(m(x) − g(a))` with `u` concave and `m`, `g` increasing has
increasing differences. With `m` cash on hand and `g(a)` saving, more cash makes saving more
attractive at the margin. -/
theorem increasingDifferences_concave {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) {m : X → ℝ}
    {g : A → ℝ} (hm : Monotone m) (hg : Monotone g) :
    IncreasingDifferences fun x a => u (m x - g a) := by
  intro x x' hx a a' ha
  have h := concave_increment hu (s := m x - g a') (t := m x' - g a') (d := g a' - g a)
    (by linarith [hm hx]) (by linarith [hg ha])
  have e1 : m x' - g a' + (g a' - g a) = m x' - g a := by ring
  have e2 : m x - g a' + (g a' - g a) = m x - g a := by ring
  rw [e1, e2] at h
  linarith

/-- The maximizers of `f(x, ·)` on `Γ(x)`. -/
noncomputable def argmaxSet (Γ : X → Finset A) (f : X → A → ℝ) (x : X) : Finset A :=
  (Γ x).filter fun a => ∀ b ∈ Γ x, f x b ≤ f x a

omit [Preorder X] [LinearOrder A] in
theorem mem_argmaxSet {Γ : X → Finset A} {f : X → A → ℝ} {x : X} {a : A} :
    a ∈ argmaxSet Γ f x ↔ a ∈ Γ x ∧ ∀ b ∈ Γ x, f x b ≤ f x a := by
  unfold argmaxSet
  exact mem_filter

omit [Preorder X] [LinearOrder A] in
theorem argmaxSet_nonempty {Γ : X → Finset A} (hΓ : ∀ x, (Γ x).Nonempty) (f : X → A → ℝ)
    (x : X) : (argmaxSet Γ f x).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := (Γ x).exists_max_image (f x) (hΓ x)
  exact ⟨a, mem_argmaxSet.2 ⟨ha, hmax⟩⟩

/-- **Topkis**: the argmax sets are ascending in the strong set order. -/
theorem argmax_strongSetOrder {Γ : X → Finset A} (hΓ : Ascending Γ) {f : X → A → ℝ}
    (hf : IncreasingDifferences f) {x x' : X} (hx : x ≤ x') {a a' : A}
    (ha : a ∈ argmaxSet Γ f x) (ha' : a' ∈ argmaxSet Γ f x') :
    min a a' ∈ argmaxSet Γ f x ∧ max a a' ∈ argmaxSet Γ f x' := by
  rw [mem_argmaxSet] at ha ha'
  rcases le_total a a' with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact ⟨mem_argmaxSet.2 ha, mem_argmaxSet.2 ha'⟩
  · rw [min_eq_right h, max_eq_left h]
    obtain ⟨h1, h2⟩ := hΓ hx a ha.1 a' ha'.1
    rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    have i1 := ha.2 a' h1
    have i2 := ha'.2 a h2
    have i3 := hf hx h
    refine ⟨mem_argmaxSet.2 ⟨h1, fun b hb => ?_⟩, mem_argmaxSet.2 ⟨h2, fun b hb => ?_⟩⟩
    · linarith [ha.2 b hb]
    · linarith [ha'.2 b hb]

/-- The greatest maximizer. -/
noncomputable def gmax {Γ : X → Finset A} (hΓ : ∀ x, (Γ x).Nonempty) (f : X → A → ℝ) (x : X) :
    A :=
  (argmaxSet Γ f x).max' (argmaxSet_nonempty hΓ f x)

/-- The least maximizer. -/
noncomputable def lmax {Γ : X → Finset A} (hΓ : ∀ x, (Γ x).Nonempty) (f : X → A → ℝ) (x : X) :
    A :=
  (argmaxSet Γ f x).min' (argmaxSet_nonempty hΓ f x)

omit [Preorder X] in
theorem gmax_mem {Γ : X → Finset A} (hΓ : ∀ x, (Γ x).Nonempty) (f : X → A → ℝ) (x : X) :
    gmax hΓ f x ∈ argmaxSet Γ f x :=
  max'_mem _ _

omit [Preorder X] in
theorem lmax_mem {Γ : X → Finset A} (hΓ : ∀ x, (Γ x).Nonempty) (f : X → A → ℝ) (x : X) :
    lmax hΓ f x ∈ argmaxSet Γ f x :=
  min'_mem _ _

/-- **Topkis's theorem**: the greatest maximizer is increasing. -/
theorem topkis_gmax {Γ : X → Finset A} (hne : ∀ x, (Γ x).Nonempty) (hΓ : Ascending Γ)
    {f : X → A → ℝ} (hf : IncreasingDifferences f) : Monotone (gmax hne f) := by
  intro x x' hx
  have h := (argmax_strongSetOrder hΓ hf hx (gmax_mem hne f x) (gmax_mem hne f x')).2
  exact (le_max_left _ _).trans (le_max' _ _ h)

/-- **Topkis's theorem**: the least maximizer is increasing. -/
theorem topkis_lmax {Γ : X → Finset A} (hne : ∀ x, (Γ x).Nonempty) (hΓ : Ascending Γ)
    {f : X → A → ℝ} (hf : IncreasingDifferences f) : Monotone (lmax hne f) := by
  intro x x' hx
  have h := (argmax_strongSetOrder hΓ hf hx (lmax_mem hne f x) (lmax_mem hne f x')).1
  exact (min'_le _ _ h).trans (min_le_right _ _)

/-- With strictly increasing differences every maximizer at `x` lies below every maximizer at
`x' > x`. -/
theorem topkis_strict {Γ : X → Finset A} (hΓ : Ascending Γ) {f : X → A → ℝ}
    (hf : StrictIncreasingDifferences f) {x x' : X} (hx : x < x') {a a' : A}
    (ha : a ∈ argmaxSet Γ f x) (ha' : a' ∈ argmaxSet Γ f x') : a ≤ a' := by
  by_contra h
  push Not at h
  rw [mem_argmaxSet] at ha ha'
  obtain ⟨h1, h2⟩ := hΓ hx.le a ha.1 a' ha'.1
  rw [min_eq_right h.le] at h1
  rw [max_eq_left h.le] at h2
  linarith [ha.2 a' h1, ha'.2 a h2, hf hx h]

end DPExtensions.MonotonePolicies

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Blackwell's sufficient conditions

SLP §3.2, pp. 54–55.

`B(X)` is the space of bounded functions `f : X → ℝ` with the sup distance
`‖f − g‖ = supₓ |f(x) − g(x)|` (`supDist`).

* `theorem_3_3` (**Blackwell's sufficient conditions**): an operator on `B(X)` that is monotone and
  discounts constants, `T(f + a) ≤ Tf + βa`, satisfies `‖Tf − Tg‖ ≤ β‖f − g‖`.
* `bellmanOp`, `bellmanOp_bdd`, `bellmanOp_mono`, `bellmanOp_add_const`, `bellmanOp_contraction`
  (p. 55): the operator `(Tv)(x) = sup_{y ∈ Γ(x)} [F(x, y) + βv(y)]` of the growth model, with
  nonempty feasible sets and bounded returns, is monotone and discounts, so it is a contraction.
-/

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {X : Type*}

/-- `f` is bounded. -/
def IsBdd (f : X → ℝ) : Prop := ∃ M, ∀ x, |f x| ≤ M

/-- The sup distance `‖f − g‖ = supₓ |f(x) − g(x)|` on `B(X)`. -/
noncomputable def supDist (f g : X → ℝ) : ℝ := ⨆ x, |f x - g x|

theorem bddAbove_absDiff {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) :
    BddAbove (Set.range fun x => |f x - g x|) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨M', hM'⟩ := hg
  refine ⟨M + M', ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (abs_sub _ _).trans (add_le_add (hM x) (hM' x))

theorem abs_le_supDist {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) (x : X) :
    |f x - g x| ≤ supDist f g :=
  le_ciSup (bddAbove_absDiff hf hg) x

theorem supDist_le [Nonempty X] {f g : X → ℝ} {c : ℝ} (h : ∀ x, |f x - g x| ≤ c) :
    supDist f g ≤ c :=
  ciSup_le h

theorem supDist_nonneg [Nonempty X] {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) :
    0 ≤ supDist f g :=
  (abs_nonneg _).trans (abs_le_supDist hf hg (Classical.arbitrary X))

/-- **Theorem 3.3 (Blackwell's sufficient conditions for a contraction).** If `T` on `B(X)`
satisfies (a) monotonicity, `f ≤ g ⇒ Tf ≤ Tg`, and (b) discounting,
`T(f + a) ≤ Tf + βa` for `a ≥ 0`, then `‖Tf − Tg‖ ≤ β‖f − g‖`. -/
theorem theorem_3_3 [Nonempty X] {T : (X → ℝ) → (X → ℝ)} {β : ℝ}
    (hmono : ∀ f g, IsBdd f → IsBdd g → f ≤ g → T f ≤ T g)
    (hdisc : ∀ f, IsBdd f → ∀ a, 0 ≤ a → T (fun x => f x + a) ≤ fun x => T f x + β * a)
    {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) :
    supDist (T f) (T g) ≤ β * supDist f g := by
  set c := supDist f g
  have hc : 0 ≤ c := supDist_nonneg hf hg
  have hshift : ∀ {u : X → ℝ}, IsBdd u → IsBdd fun x => u x + c := fun {u} ⟨M, hM⟩ =>
    ⟨M + |c|, fun x => (abs_add_le _ _).trans (add_le_add (hM x) le_rfl)⟩
  -- `f ≤ g + c` and `g ≤ f + c`
  have h1 : f ≤ fun x => g x + c := fun x => by
    have := abs_le_supDist hf hg x
    linarith [le_abs_self (f x - g x)]
  have h2 : g ≤ fun x => f x + c := fun x => by
    have := abs_le_supDist hf hg x
    linarith [neg_abs_le (f x - g x)]
  have e1 := (hmono _ _ hf (hshift hg) h1).trans (hdisc g hg c hc)
  have e2 := (hmono _ _ hg (hshift hf) h2).trans (hdisc f hf c hc)
  exact supDist_le fun x => abs_le.2 ⟨by linarith [e2 x], by linarith [e1 x]⟩

/-! ### The growth model's operator -/

/-- The operator `(Tv)(x) = sup_{y ∈ Γ(x)} [F(x, y) + βv(y)]`. -/
noncomputable def bellmanOp (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (v : X → ℝ) (x : X) : ℝ :=
  ⨆ y : Γ x, F x y + β * v y

variable {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ}

theorem bddAbove_bellman {M : ℝ} (hF : ∀ x y, |F x y| ≤ M) {v : X → ℝ} (hv : IsBdd v) (x : X) :
    BddAbove (Set.range fun y : Γ x => F x y + β * v y) := by
  obtain ⟨K, hK⟩ := hv
  refine ⟨M + |β| * K, ?_⟩
  rintro _ ⟨y, rfl⟩
  have h1 := (le_abs_self _).trans (hF x y)
  have h2 : β * v y ≤ |β| * K := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK y) (abs_nonneg β))
  linarith

theorem le_bellmanOp {M : ℝ} (hF : ∀ x y, |F x y| ≤ M) {v : X → ℝ} (hv : IsBdd v) {x y : X}
    (hy : y ∈ Γ x) : F x y + β * v y ≤ bellmanOp Γ F β v x :=
  le_ciSup (f := fun y : Γ x => F x y + β * v y) (bddAbove_bellman hF hv x) ⟨y, hy⟩

/-- `T` maps bounded functions to bounded functions. -/
theorem bellmanOp_bdd (hΓ : ∀ x, (Γ x).Nonempty) {M : ℝ} (hF : ∀ x y, |F x y| ≤ M) {v : X → ℝ}
    (hv : IsBdd v) : IsBdd (bellmanOp Γ F β v) := by
  obtain ⟨K, hK⟩ := hv
  refine ⟨M + |β| * K, fun x => ?_⟩
  have := (hΓ x).to_subtype
  have hterm : ∀ y : Γ x, |F x y + β * v y| ≤ M + |β| * K := fun y => by
    refine (abs_add_le _ _).trans (add_le_add (hF x y) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hK y) (abs_nonneg β)
  unfold bellmanOp
  rw [abs_le]
  constructor
  · obtain ⟨y⟩ := (inferInstance : Nonempty (Γ x))
    have := le_ciSup (f := fun y : Γ x => F x y + β * v y) (bddAbove_bellman hF ⟨K, hK⟩ x) y
    linarith [(abs_le.1 (hterm y)).1]
  · exact ciSup_le fun y => (abs_le.1 (hterm y)).2

/-- **Monotonicity** (p. 55). -/
theorem bellmanOp_mono {M : ℝ} (hF : ∀ x y, |F x y| ≤ M) (hβ : 0 ≤ β)
    {v w : X → ℝ} (hw : IsBdd w) (hvw : v ≤ w) : bellmanOp Γ F β v ≤ bellmanOp Γ F β w :=
  fun x => ciSup_mono (bddAbove_bellman hF hw x) fun y =>
    add_le_add le_rfl (mul_le_mul_of_nonneg_left (hvw y) hβ)

/-- `sup (fᵢ + c) = sup fᵢ + c`. -/
theorem ciSup_add_const {ι : Type*} [Nonempty ι] {f : ι → ℝ} (hf : BddAbove (Set.range f))
    (c : ℝ) : ⨆ i, (f i + c) = (⨆ i, f i) + c := by
  have hfc : BddAbove (Set.range fun i => f i + c) := by
    obtain ⟨M, hM⟩ := hf
    exact ⟨M + c, by rintro _ ⟨i, rfl⟩; linarith [hM ⟨i, rfl⟩]⟩
  refine le_antisymm (ciSup_le fun i => by linarith [le_ciSup hf i]) ?_
  have : (⨆ i, f i) ≤ (⨆ i, (f i + c)) - c :=
    ciSup_le fun i => by linarith [le_ciSup hfc i]
  linarith

/-- **Discounting** (p. 55), with equality: `T(v + a) = Tv + βa`. -/
theorem bellmanOp_add_const (hΓ : ∀ x, (Γ x).Nonempty) {M : ℝ} (hF : ∀ x y, |F x y| ≤ M)
    {v : X → ℝ} (hv : IsBdd v) (a : ℝ) :
    bellmanOp Γ F β (fun x => v x + a) = fun x => bellmanOp Γ F β v x + β * a := by
  funext x
  have := (hΓ x).to_subtype
  unfold bellmanOp
  rw [← ciSup_add_const (bddAbove_bellman hF hv x)]
  congr 1
  funext y
  ring

/-- **The growth model's operator is a contraction** on `B(X)` by Blackwell's theorem. -/
theorem bellmanOp_contraction [Nonempty X] (hΓ : ∀ x, (Γ x).Nonempty) {M : ℝ}
    (hF : ∀ x y, |F x y| ≤ M) (hβ : 0 ≤ β) {v w : X → ℝ} (hv : IsBdd v) (hw : IsBdd w) :
    supDist (bellmanOp Γ F β v) (bellmanOp Γ F β w) ≤ β * supDist v w :=
  theorem_3_3 (fun _ _ _ hg hfg => bellmanOp_mono hF hβ hg hfg)
    (fun _ hf a _ => (bellmanOp_add_const hΓ hF hf a).le) hv hw

end StokeyLucasPrescott.MathematicalPreliminaries

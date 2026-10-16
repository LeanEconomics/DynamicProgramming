/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.RealIntervals
import ConvergenceApplications.Parameters
import ConvergenceApplications.Contraction

/-!
# An equilibrium search economy: the value function and the law of motion (SLP §13.8)

SLP §13.8, pp. 404–409, Exercise 13.8 (a)–(c). An island with work force `x ∈ X = [0, x̄]` and
shock `z ∈ Z = [z̲, z̄]` (a monotone Feller transition function `Q`); `θ` is the value of
leaving. The modules `SearchInvariant`, `SearchDemand` and `SearchLeavers` treat (d)–(h).

* **Cutoffs** (`IsSearchCutoff`, `searchCutoff`): for `h(·, y)` continuous, nonincreasing,
  somewhere `≤ 0`, and strictly decreasing wherever it is `≥ 0` (`SearchStrictDec`), the point
  `c(y)` where `h(·, y)` crosses `0` exists (intermediate value theorem,
  `exists_isSearchCutoff_Icc`), is unique (`IsSearchCutoff.unique`), satisfies `h(c, y) ≤ 0` with
  equality if `c > 0` (`searchCutoff_spec_Icc`), is monotone in `h` (`searchCutoff_le_searchCutoff`)
  and continuous in `y` (`continuous_searchCutoff`).
* `SearchPrimitives` (p. 405): `x̄ > 0`, `0 < β < 1`, `f` continuous with (F1), and (F2) for
  `x ∈ [0, x̄)` only (correction below).
* `ex_13_8a_contraction`, **`ex_13_8a`** (p. 408): the operator `T` of (4) maps bounded
  continuous functions to bounded continuous functions (Lemma 12.14) and is a contraction of
  modulus `β`; for every `θ ≥ 0` there is a unique bounded continuous `v ≥ 0` with `v = Tv`;
  `v ≤ max{θ, f(0, z̄)/(1 − β)}`, `θ ≤ v ≤ f + θ` (`searchV_bounds`); `v` is nonincreasing in `x`
  and nondecreasing in `z` (`searchV_anti_mono`, Corollary 1 to Theorem 3.2).
* `searchV_cases`: (3a)–(3c). `searchEV_strictDec`: `x ↦ β ∫ v(x, z′) Q(z, dz′)` is strictly
  decreasing wherever it is `≥ θ` (if `v(x₁, z′) > θ` then `v(x₂, z′) < v(x₁, z′)` for `x₂ > x₁`).
* `searchGC`, `searchGA`, `searchG`: `g_C(z)` solves (5c), `g_A(z)` solves (5a) (neither depends
  on `x`), and `g(x, z) = min{max{x, g_C(z)}, g_A(z)}` (Figure 13.2), with `g_C ≤ g_A`.
* **`ex_13_8b`** (p. 409): `g` satisfies (5a)–(5c) on the regions (2a)–(2c), is nondecreasing in
  `x` and in `z`, and `|g(x, z) − g(x′, z)| ≤ |x − x′|`. `ex_13_8b_unique`: (5a)–(5c) determine
  `g` uniquely; by strict monotonicity there are no flat stretches, so no extreme-solution
  convention is needed.
* **`ex_13_8c`** (p. 409): `g` is continuous on `X × Z`.

**Correction** (NOTE p. 405). (F1) and (F2) are inconsistent at `x = x̄`: `f(x̄, ·) = 0` is not
strictly increasing when `z̲ < z̄` (`ex_13_8_F1F2_inconsistent`). (F2) is imposed on `[0, x̄)`.

Ex. 13.8a assumes `θ > 0`; everything here holds for `θ ≥ 0` (needed for `θ = 0` in Ex. 13.8f).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

/-! ### Cutoffs of a nonincreasing function -/

variable {X Y : Type*}

/-- `c` is a **cutoff** of `h(·, y)` at level `0`: `h(x, y) ≥ 0` for `x < c` and `h(x, y) ≤ 0`
for `x > c`. -/
def IsSearchCutoff [LinearOrder X] (h : X × Y → ℝ) (y : Y) (c : X) : Prop :=
  (∀ x, x < c → 0 ≤ h (x, y)) ∧ ∀ x, c < x → h (x, y) ≤ 0

/-- A chosen cutoff of `h(·, y)` (unique under the hypotheses below, `IsSearchCutoff.unique`). -/
noncomputable def searchCutoff [LinearOrder X] [Nonempty X] (h : X × Y → ℝ) (y : Y) : X :=
  Classical.epsilon (IsSearchCutoff h y)

/-- `h(·, y)` is strictly decreasing to the right of every point where it is nonnegative. -/
def SearchStrictDec [LinearOrder X] (h : X × Y → ℝ) : Prop :=
  ∀ y x₁ x₂, x₁ < x₂ → 0 ≤ h (x₁, y) → h (x₂, y) < h (x₁, y)

variable [LinearOrder X] {h : X × Y → ℝ}

/-- Strictly left of a cutoff, `h > 0`. -/
theorem IsSearchCutoff.pos_of_lt [DenselyOrdered X] (hsd : SearchStrictDec h) {y : Y} {c : X}
    (hc : IsSearchCutoff h y c) {x : X} (hx : x < c) : 0 < h (x, y) := by
  obtain ⟨m, hxm, hmc⟩ := exists_between hx
  have h1 := hc.1 m hmc
  have h2 := hsd y x m hxm (hc.1 x hx)
  linarith

/-- Strictly right of a cutoff, `h < 0`. -/
theorem IsSearchCutoff.neg_of_lt [DenselyOrdered X] (hanti : ∀ y, Antitone fun x => h (x, y))
    (hsd : SearchStrictDec h) {y : Y} {c : X} (hc : IsSearchCutoff h y c) {x : X} (hx : c < x) :
    h (x, y) < 0 := by
  obtain ⟨m, hcm, hmx⟩ := exists_between hx
  rcases lt_or_ge (h (m, y)) 0 with hm | hm
  · exact (hanti y hmx.le).trans_lt hm
  · have := hsd y m x hmx hm
    linarith [hc.2 m hcm]

/-- Cutoffs of two functions are ordered as the functions are. -/
theorem IsSearchCutoff.le_of_le [DenselyOrdered X] {h₁ h₂ : X × Y → ℝ} (hsd₁ : SearchStrictDec h₁)
    (hanti₂ : ∀ y, Antitone fun x => h₂ (x, y)) (hsd₂ : SearchStrictDec h₂) {y₁ y₂ : Y}
    {c₁ c₂ : X} (hc₁ : IsSearchCutoff h₁ y₁ c₁) (hc₂ : IsSearchCutoff h₂ y₂ c₂)
    (hle : ∀ x, h₁ (x, y₁) ≤ h₂ (x, y₂)) : c₁ ≤ c₂ := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨m, h1, h2⟩ := exists_between hlt
  linarith [hc₁.pos_of_lt hsd₁ h2, hc₂.neg_of_lt hanti₂ hsd₂ h1, hle m]

/-- The cutoff is unique. -/
theorem IsSearchCutoff.unique [DenselyOrdered X] (hanti : ∀ y, Antitone fun x => h (x, y))
    (hsd : SearchStrictDec h) {y : Y} {c c' : X} (hc : IsSearchCutoff h y c)
    (hc' : IsSearchCutoff h y c') : c = c' :=
  le_antisymm (hc.le_of_le hsd hanti hsd hc' fun _ => le_rfl)
    (hc'.le_of_le hsd hanti hsd hc fun _ => le_rfl)

/-- The least point is a cutoff if `h` is nonpositive there. -/
theorem isSearchCutoff_of_le_zero (hanti : ∀ y, Antitone fun x => h (x, y)) {y : Y} {c : X}
    (hmin : ∀ x, c ≤ x) (h0 : h (c, y) ≤ 0) : IsSearchCutoff h y c :=
  ⟨fun _ hx => absurd hx (not_lt.2 (hmin _)), fun _ hx => (hanti y hx.le).trans h0⟩

/-- A zero of `h(·, y)` is a cutoff. -/
theorem isSearchCutoff_of_eq_zero (hanti : ∀ y, Antitone fun x => h (x, y)) {y : Y} {c : X}
    (h0 : h (c, y) = 0) : IsSearchCutoff h y c :=
  ⟨fun x hx => by have := hanti y hx.le; simp only at this; linarith,
    fun x hx => by have := hanti y hx.le; simp only at this; linarith⟩

/-- The chosen cutoff is a cutoff when one exists. -/
theorem searchCutoff_isSearchCutoff [Nonempty X] {y : Y} (hex : ∃ c, IsSearchCutoff h y c) :
    IsSearchCutoff h y (searchCutoff h y) :=
  Classical.epsilon_spec hex

/-- The chosen cutoff is the (unique) cutoff. -/
theorem searchCutoff_eq [Nonempty X] [DenselyOrdered X] (hanti : ∀ y, Antitone fun x => h (x, y))
    (hsd : SearchStrictDec h) {y : Y} {c : X} (hc : IsSearchCutoff h y c) :
    searchCutoff h y = c :=
  (searchCutoff_isSearchCutoff ⟨c, hc⟩).unique hanti hsd hc

/-- Intermediate value theorem on a real interval: a continuous `h(·, y)` that is positive at `a`
and nonpositive somewhere has a zero. -/
theorem exists_searchZero_Icc {a b : ℝ} {h : Icc a b × Y → ℝ}
    (hcont : ∀ y, Continuous fun x => h (x, y)) {y : Y} {x₀ : Icc a b} (hx₀ : h (x₀, y) ≤ 0)
    (hb : 0 < h (⟨a, left_mem_Icc.2 (x₀.2.1.trans x₀.2.2)⟩, y)) : ∃ c, h (c, y) = 0 := by
  have hab : a ≤ b := x₀.2.1.trans x₀.2.2
  set k : ℝ → ℝ := fun t => h (projIcc a b hab t, y)
  have hk : Continuous k := (hcont y).comp continuous_projIcc
  have hk0 : k x₀ ≤ 0 := by simp only [k, projIcc_val]; exact hx₀
  have hka : 0 < k a := by
    simp only [k]
    rwa [projIcc_left]
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc' x₀.2.1 hk.continuousOn ⟨hk0, hka.le⟩
  exact ⟨_, ht⟩

/-- Cutoffs exist on a real interval `[a, b]` when `h(·, y)` is continuous, nonincreasing and
somewhere nonpositive. -/
theorem exists_isSearchCutoff_Icc {a b : ℝ} {h : Icc a b × Y → ℝ}
    (hcont : ∀ y, Continuous fun x => h (x, y)) (hanti : ∀ y, Antitone fun x => h (x, y))
    (hlow : ∀ y, ∃ x, h (x, y) ≤ 0) (y : Y) : ∃ c, IsSearchCutoff h y c := by
  obtain ⟨x₀, hx₀⟩ := hlow y
  rcases le_or_gt (h (⟨a, left_mem_Icc.2 (x₀.2.1.trans x₀.2.2)⟩, y)) 0 with hb | hb
  · exact ⟨_, isSearchCutoff_of_le_zero hanti (fun x => x.2.1) hb⟩
  · obtain ⟨c, hc⟩ := exists_searchZero_Icc hcont hx₀ hb
    exact ⟨c, isSearchCutoff_of_eq_zero hanti hc⟩

/-- The value at the cutoff: `h(c, y) ≤ 0`, with equality if `c > a`. -/
theorem searchCutoff_spec_Icc {a b : ℝ} [Nonempty (Icc a b)] {h : Icc a b × Y → ℝ}
    (hcont : ∀ y, Continuous fun x => h (x, y)) (hanti : ∀ y, Antitone fun x => h (x, y))
    (hsd : SearchStrictDec h) (hlow : ∀ y, ∃ x, h (x, y) ≤ 0) (y : Y) :
    h (searchCutoff h y, y) ≤ 0 ∧
      (a < ((searchCutoff h y : Icc a b) : ℝ) → h (searchCutoff h y, y) = 0) := by
  obtain ⟨x₀, hx₀⟩ := hlow y
  rcases le_or_gt (h (⟨a, left_mem_Icc.2 (x₀.2.1.trans x₀.2.2)⟩, y)) 0 with hb | hb
  · rw [searchCutoff_eq hanti hsd (isSearchCutoff_of_le_zero hanti (fun x => x.2.1) hb)]
    exact ⟨hb, fun h => absurd h (lt_irrefl _)⟩
  · obtain ⟨c, hc⟩ := exists_searchZero_Icc hcont hx₀ hb
    rw [searchCutoff_eq hanti hsd (isSearchCutoff_of_eq_zero hanti hc)]
    exact ⟨hc.le, fun _ => hc⟩

/-- The cutoff depends continuously on `y` when `h(x, ·)` is continuous for each `x`. -/
theorem continuous_searchCutoff [Nonempty X] [DenselyOrdered X] [TopologicalSpace X]
    [OrderTopology X] [TopologicalSpace Y] (hanti : ∀ y, Antitone fun x => h (x, y))
    (hsd : SearchStrictDec h) (hex : ∀ y, ∃ c, IsSearchCutoff h y c)
    (hcy : ∀ x, Continuous fun y => h (x, y)) : Continuous (searchCutoff h) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hc := searchCutoff_isSearchCutoff (hex y)
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · obtain ⟨m, hlm, hmc⟩ := exists_between hl
    have hpos := hc.pos_of_lt hsd hmc
    filter_upwards [((hcy m).tendsto y).eventually (lt_mem_nhds hpos)] with y' hy'
    refine hlm.trans_le (not_lt.1 fun hlt => ?_)
    have := (searchCutoff_isSearchCutoff (hex y')).2 m hlt
    linarith
  · obtain ⟨m, hcm, hmu⟩ := exists_between hu
    have hneg := hc.neg_of_lt hanti hsd hcm
    filter_upwards [((hcy m).tendsto y).eventually (gt_mem_nhds hneg)] with y' hy'
    refine (not_lt.1 fun hlt => ?_).trans_lt hmu
    have := (searchCutoff_isSearchCutoff (hex y')).1 m hlt
    linarith

/-- Cutoffs are ordered as the functions are. -/
theorem searchCutoff_le_searchCutoff [Nonempty X] [DenselyOrdered X] {h₁ h₂ : X × Y → ℝ}
    (hsd₁ : SearchStrictDec h₁) (hanti₂ : ∀ y, Antitone fun x => h₂ (x, y))
    (hsd₂ : SearchStrictDec h₂) {y₁ y₂ : Y} (hex₁ : ∃ c, IsSearchCutoff h₁ y₁ c)
    (hex₂ : ∃ c, IsSearchCutoff h₂ y₂ c) (hle : ∀ x, h₁ (x, y₁) ≤ h₂ (x, y₂)) :
    searchCutoff h₁ y₁ ≤ searchCutoff h₂ y₂ :=
  (searchCutoff_isSearchCutoff hex₁).le_of_le hsd₁ hanti₂ hsd₂ (searchCutoff_isSearchCutoff hex₂)
    hle

/-! ### Primitives -/

/-- The primitives of §13.8 (p. 405): `Z = [z̲, z̄]`, `X = [0, x̄]` with `x̄ > 0`, `0 < β < 1`, and
a continuous `f` with (F1) `f(·, z)` strictly decreasing on `[0, x̄]` with `f(x̄, z) = 0`, and
(F2) `f(x, ·)` strictly increasing, **corrected** to `x ∈ [0, x̄)` (`ex_13_8_F1F2_inconsistent`). -/
structure SearchPrimitives (zlo zhi xbar β : ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  hz : zlo ≤ zhi
  hx : 0 < xbar
  hβ0 : 0 < β
  hβ1 : β < 1
  cont : ContinuousOn (Function.uncurry f) (Icc 0 xbar ×ˢ Icc zlo zhi)
  F1 : ∀ z ∈ Icc zlo zhi, StrictAntiOn (fun x => f x z) (Icc 0 xbar)
  F1top : ∀ z ∈ Icc zlo zhi, f xbar z = 0
  F2 : ∀ x ∈ Ico 0 xbar, StrictMonoOn (f x) (Icc zlo zhi)

/-- **Correction (NOTE p. 405).** (F1) and (F2) as stated are inconsistent: if `z̲ < z̄` and
`f(x̄, z) = 0` for all `z`, then `f(x̄, ·)` is not strictly increasing, so (F2) fails at
`x = x̄`. -/
theorem ex_13_8_F1F2_inconsistent {zlo zhi xbar : ℝ} (hz : zlo < zhi) (hx : 0 ≤ xbar)
    (f : ℝ → ℝ → ℝ) (hF1 : ∀ z ∈ Icc zlo zhi, f xbar z = 0) :
    ¬ ∀ x ∈ Icc 0 xbar, StrictMonoOn (f x) (Icc zlo zhi) := fun h => by
  have := h xbar ⟨hx, le_rfl⟩ (left_mem_Icc.2 hz.le) (right_mem_Icc.2 hz.le) hz
  rw [hF1 zlo (left_mem_Icc.2 hz.le), hF1 zhi (right_mem_Icc.2 hz.le)] at this
  exact lt_irrefl _ this

variable {zlo zhi xbar β : ℝ} {f : ℝ → ℝ → ℝ}

/-- `f` is continuous on `X × Z`. -/
theorem SearchPrimitives.continuous_f (hP : SearchPrimitives zlo zhi xbar β f) :
    Continuous fun p : Icc (0 : ℝ) xbar × Icc zlo zhi => f p.1 p.2 :=
  hP.cont.comp_continuous (continuous_subtype_val.prodMap continuous_subtype_val)
    fun p => ⟨p.1.2, p.2.2⟩

/-- (F1): `f(·, z)` is nonincreasing. -/
theorem SearchPrimitives.f_anti (hP : SearchPrimitives zlo zhi xbar β f) (z : Icc zlo zhi) :
    Antitone fun x : Icc (0 : ℝ) xbar => f x z := fun x x' hxx' =>
  (hP.F1 z z.2).antitoneOn x.2 x'.2 hxx'

/-- (F1): `f(·, z)` is strictly decreasing. -/
theorem SearchPrimitives.f_strictAnti (hP : SearchPrimitives zlo zhi xbar β f)
    (z : Icc zlo zhi) : StrictAnti fun x : Icc (0 : ℝ) xbar => f x z := fun x x' hxx' =>
  hP.F1 z z.2 x.2 x'.2 hxx'

/-- (F1): `f(x̄, z) = 0`. -/
theorem SearchPrimitives.f_top (hP : SearchPrimitives zlo zhi xbar β f) (z : Icc zlo zhi) :
    f xbar z = 0 :=
  hP.F1top z z.2

/-- `f ≥ 0` on `X × Z` (from (F1)). -/
theorem SearchPrimitives.f_nonneg (hP : SearchPrimitives zlo zhi xbar β f)
    (p : Icc (0 : ℝ) xbar × Icc zlo zhi) : 0 ≤ f p.1 p.2 := by
  have := (hP.F1 p.2 p.2.2).antitoneOn p.1.2 ⟨hP.hx.le, le_rfl⟩ p.1.2.2
  rwa [hP.f_top p.2] at this

/-- (F2), corrected: `f(x, ·)` is nondecreasing for every `x ∈ [0, x̄]`. -/
theorem SearchPrimitives.f_mono (hP : SearchPrimitives zlo zhi xbar β f) (x : Icc (0 : ℝ) xbar) :
    Monotone fun z : Icc zlo zhi => f x z := fun z z' hzz' => by
  rcases lt_or_eq_of_le x.2.2 with hx | hx
  · exact (hP.F2 x ⟨x.2.1, hx⟩).monotoneOn z.2 z'.2 hzz'
  · simp only [hx, hP.f_top, le_refl]

/-- `f` is largest at `(0, z̄)`. -/
theorem SearchPrimitives.f_le (hP : SearchPrimitives zlo zhi xbar β f)
    (p : Icc (0 : ℝ) xbar × Icc zlo zhi) : f p.1 p.2 ≤ f 0 zhi := by
  have h1 := hP.f_anti p.2 (show (⟨0, le_rfl, hP.hx.le⟩ : Icc (0 : ℝ) xbar) ≤ p.1 from p.1.2.1)
  have h2 := hP.f_mono ⟨0, le_rfl, hP.hx.le⟩
    (show p.2 ≤ (⟨zhi, hP.hz, le_rfl⟩ : Icc zlo zhi) from p.2.2.2)
  simp only at h1 h2
  linarith

/-! ### The operator (4) -/

/-- The right side of (4): `max{θ, f(x, z) + min{θ, β ∫ v(x, z′) Q(z, dz′)}}`. -/
noncomputable def searchRHS (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) (f : ℝ → ℝ → ℝ) (β θ : ℝ)
    (v : Icc (0 : ℝ) xbar × Icc zlo zhi → ℝ) (p : Icc (0 : ℝ) xbar × Icc zlo zhi) : ℝ :=
  max θ (f p.1 p.2 + min θ (β * ∫ z', v (p.1, z') ∂Q p.2))

/-- The solution `v` of (4) (a choice; unique by `ex_13_8a`). -/
noncomputable def searchV (xbar : ℝ) (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) (f : ℝ → ℝ → ℝ)
    (β θ : ℝ) : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ :=
  Classical.epsilon fun v => ∀ p, v p = searchRHS Q f β θ v p

/-- `|max{θ, A + min{θ, a}} − max{θ, A + min{θ, b}}| ≤ |a − b|`. -/
theorem abs_searchMaxMin_le (θ A a b : ℝ) :
    |max θ (A + min θ a) - max θ (A + min θ b)| ≤ |a - b| := by
  have h1 := abs_max_sub_max_le_abs (A + min θ a) (A + min θ b) θ
  have h2 := abs_min_sub_min_le_max θ a θ b
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h2
  rw [max_comm θ, max_comm θ]
  refine h1.trans ?_
  rw [add_sub_add_left_eq_sub]
  exact h2

variable (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) [IsMarkovKernel Q]

omit [IsMarkovKernel Q] in
/-- Sections `z′ ↦ v(x, z′)` of a bounded continuous `v` are integrable. -/
theorem integrable_searchSection (v : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ) (x : Icc (0 : ℝ) xbar)
    (z : Icc zlo zhi) [IsFiniteMeasure (Q z)] : Integrable (fun z' => v (x, z')) (Q z) :=
  (v.compContinuous ⟨fun z' => (x, z'), by fun_prop⟩).integrable _

/-- `|∫ v(x, ·) dQ(z) − ∫ w(x, ·) dQ(z)| ≤ ‖v − w‖`. -/
theorem abs_integral_searchSection_sub_le (v w : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ)
    (x : Icc (0 : ℝ) xbar) (z : Icc zlo zhi) :
    |∫ z', v (x, z') ∂Q z - ∫ z', w (x, z') ∂Q z| ≤ dist v w := by
  rw [← integral_sub (integrable_searchSection Q v x z) (integrable_searchSection Q w x z)]
  have := norm_integral_le_of_norm_le_const (μ := Q z) (C := dist v w)
    (f := fun z' => v (x, z') - w (x, z')) (Eventually.of_forall fun z' => by
      rw [Real.norm_eq_abs, ← Real.dist_eq]; exact dist_coe_le_dist _)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

/-- **Exercise 13.8a** (operator). The operator `T` of (4) maps bounded continuous functions on
`X × Z` to bounded continuous functions (Lemma 12.14, as `Q` is Feller) and is a contraction of
modulus `β`. -/
theorem ex_13_8a_contraction (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (θ : ℝ) : ∃ T : (Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ) → (Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ),
      (∀ v p, T v p = searchRHS Q f β θ v p) ∧ IsContraction T β := by
  have hc : ∀ v : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ, Continuous (searchRHS Q f β θ v) :=
    fun v => continuous_const.max (hP.continuous_f.add (continuous_const.min
      (continuous_const.mul (lemma_12_14_cont Q hF v).1)))
  refine ⟨fun v => mkOfCompact ⟨searchRHS Q f β θ v, hc v⟩, fun v p => rfl,
    hP.hβ0, hP.hβ1, fun v w => ?_⟩
  refine (dist_le (mul_nonneg hP.hβ0.le dist_nonneg)).2 fun p => ?_
  simp only [mkOfCompact_apply, ContinuousMap.coe_mk, Real.dist_eq, searchRHS]
  refine (abs_searchMaxMin_le _ _ _ _).trans ?_
  rw [← mul_sub, abs_mul, abs_of_pos hP.hβ0]
  exact mul_le_mul_of_nonneg_left (abs_integral_searchSection_sub_le Q v w p.1 p.2) hP.hβ0.le

/-- (4) has a bounded continuous solution (Theorem 3.2). -/
theorem exists_searchFixed (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q) (θ : ℝ) :
    ∃ v : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ, ∀ p, v p = searchRHS Q f β θ v p := by
  obtain ⟨T, hT, hC⟩ := ex_13_8a_contraction Q hP hF θ
  obtain ⟨v, hv, -⟩ := theorem_3_2 hC
  exact ⟨v, fun p => by rw [← hT, hv]⟩

/-- `v` solves (4). -/
theorem searchV_eq (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q) (θ : ℝ)
    (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    searchV xbar Q f β θ p = searchRHS Q f β θ (searchV xbar Q f β θ) p :=
  Classical.epsilon_spec (p := fun v : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ =>
    ∀ p, v p = searchRHS Q f β θ v p) (exists_searchFixed Q hP hF θ) p

/-- The solution of (4) is unique among bounded continuous functions. -/
theorem searchV_unique (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q) (θ : ℝ)
    (w : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ) (hw : ∀ p, w p = searchRHS Q f β θ w p) :
    w = searchV xbar Q f β θ := by
  obtain ⟨T, hT, hC⟩ := ex_13_8a_contraction Q hP hF θ
  obtain ⟨v, -, huniq, -⟩ := theorem_3_2 hC
  have h1 : T w = w := ext fun p => by rw [hT, ← hw]
  have h2 : T (searchV xbar Q f β θ) = searchV xbar Q f β θ :=
    ext fun p => by rw [hT, ← searchV_eq Q hP hF θ]
  rw [huniq w h1, huniq _ h2]

/-- Sections `z′ ↦ v(x, z′)` are measurable. -/
theorem measurable_searchSection (v : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ)
    (x : Icc (0 : ℝ) xbar) : Measurable fun z' : Icc zlo zhi => v (x, z') :=
  (v.continuous.comp (continuous_const.prodMk continuous_id)).measurable

/-- `T` maps functions nonincreasing in `x` and nondecreasing in `z` into themselves, so the
fixed point has both properties (Corollary 1 to Theorem 3.2). -/
theorem searchV_anti_mono (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (θ : ℝ) :
    (∀ z, Antitone fun x => searchV xbar Q f β θ (x, z)) ∧
      ∀ x, Monotone fun z => searchV xbar Q f β θ (x, z) := by
  obtain ⟨T, hT, hC⟩ := ex_13_8a_contraction Q hP hF θ
  set S' : Set (Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ) :=
    (⋂ z, ⋂ x, ⋂ x', ⋂ (_ : x ≤ x'), {v | v (x', z) ≤ v (x, z)}) ∩
      ⋂ x, ⋂ z, ⋂ z', ⋂ (_ : z ≤ z'), {v | v (x, z) ≤ v (x, z')}
  have hmem : ∀ v, v ∈ S' ↔ (∀ z, Antitone fun x => v (x, z)) ∧
      ∀ x, Monotone fun z => v (x, z) := fun v => by
    simp only [S', mem_inter_iff, mem_iInter]
    rfl
  have hclosed : IsClosed S' := by
    refine IsClosed.inter (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter
      fun _ => isClosed_iInter fun _ => isClosed_le (continuous_eval_const _)
        (continuous_eval_const _)) ?_
    exact (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_le (continuous_eval_const _) (continuous_eval_const _))
  have hne : S'.Nonempty := ⟨0, (hmem 0).2 ⟨fun _ _ _ _ => le_rfl, fun _ _ _ _ => le_rfl⟩⟩
  have hmaps : MapsTo T S' S' := fun v hv => by
    obtain ⟨hva, hvm⟩ := (hmem v).1 hv
    refine (hmem _).2 ⟨fun z x x' hxx' => ?_, fun x z z' hzz' => ?_⟩
    · simp only [hT, searchRHS]
      refine max_le_max le_rfl (add_le_add (hP.f_anti z hxx') (min_le_min le_rfl
        (mul_le_mul_of_nonneg_left (integral_mono (integrable_searchSection Q v x' z)
          (integrable_searchSection Q v x z) fun z' => hva z' hxx') hP.hβ0.le)))
    · simp only [hT, searchRHS]
      refine max_le_max le_rfl (add_le_add (hP.f_mono x hzz') (min_le_min le_rfl
        (mul_le_mul_of_nonneg_left ?_ hP.hβ0.le)))
      exact hM _ (measurable_searchSection v x) ⟨‖v‖, fun z' => by
        rw [← Real.norm_eq_abs]; exact v.norm_coe_le_norm _⟩ (hvm x) hzz'
  have hfix : T (searchV xbar Q f β θ) = searchV xbar Q f β θ :=
    ext fun p => by rw [hT, ← searchV_eq Q hP hF θ]
  exact (hmem _).1 (corollary_1 hC hfix hne hclosed hmaps hmaps).1

/-- The expected discounted value from tomorrow, `β ∫ v(x, z′) Q(z, dz′)`. -/
noncomputable def searchEV (xbar : ℝ) (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) (f : ℝ → ℝ → ℝ)
    (β θ : ℝ) (p : Icc (0 : ℝ) xbar × Icc zlo zhi) : ℝ :=
  β * ∫ z', searchV xbar Q f β θ (p.1, z') ∂Q p.2

/-- The value of staying with no arrivals, `f(x, z) + β ∫ v(x, z′) Q(z, dz′)`. -/
noncomputable def searchPhi (xbar : ℝ) (Q : Kernel (Icc zlo zhi) (Icc zlo zhi))
    (f : ℝ → ℝ → ℝ) (β θ : ℝ) (p : Icc (0 : ℝ) xbar × Icc zlo zhi) : ℝ :=
  f p.1 p.2 + searchEV xbar Q f β θ p

variable {θ : ℝ}

/-- (4) in terms of `β ∫ v dQ`. -/
theorem searchV_eq' (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    searchV xbar Q f β θ p = max θ (f p.1 p.2 + min θ (searchEV xbar Q f β θ p)) :=
  searchV_eq Q hP hF θ p

/-- `θ ≤ v ≤ f + θ`. -/
theorem searchV_bounds (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    θ ≤ searchV xbar Q f β θ p ∧ searchV xbar Q f β θ p ≤ f p.1 p.2 + θ := by
  rw [searchV_eq' Q hP hF p]
  exact ⟨le_max_left _ _, max_le (by linarith [hP.f_nonneg p])
    (add_le_add le_rfl (min_le_left _ _))⟩

/-- At `x = x̄` everybody leaves: `v(x̄, z) = θ`. -/
theorem searchV_top (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (z : Icc zlo zhi) : searchV xbar Q f β θ (⟨xbar, hP.hx.le, le_rfl⟩, z) = θ := by
  rw [searchV_eq' Q hP hF]
  refine max_eq_left ?_
  simp only [hP.f_top, zero_add]
  exact min_le_left _ _

/-- `(x, z) ↦ β ∫ v(x, z′) Q(z, dz′)` is continuous (Lemma 12.14). -/
theorem continuous_searchEV (hF : IsFeller Q) :
    Continuous (searchEV xbar Q f β θ) :=
  continuous_const.mul (lemma_12_14_cont Q hF (searchV xbar Q f β θ)).1

/-- `x ↦ β ∫ v(x, z′) Q(z, dz′)` is nonincreasing. -/
theorem searchEV_anti (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (z : Icc zlo zhi) :
    Antitone fun x => searchEV xbar Q f β θ (x, z) := fun x x' hxx' =>
  mul_le_mul_of_nonneg_left (integral_mono (integrable_searchSection Q _ x' z)
    (integrable_searchSection Q _ x z) fun z' =>
      (searchV_anti_mono Q hP hF hM θ).1 z' hxx') hP.hβ0.le

/-- `z ↦ β ∫ v(x, z′) Q(z, dz′)` is nondecreasing (`Q` monotone). -/
theorem searchEV_mono (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (x : Icc (0 : ℝ) xbar) :
    Monotone fun z => searchEV xbar Q f β θ (x, z) := fun z z' hzz' =>
  mul_le_mul_of_nonneg_left (hM _ (measurable_searchSection _ x) ⟨‖searchV xbar Q f β θ‖,
    fun z' => by rw [← Real.norm_eq_abs]; exact (searchV xbar Q f β θ).norm_coe_le_norm _⟩
    ((searchV_anti_mono Q hP hF hM θ).2 x) hzz') hP.hβ0.le

/-- `β ∫ v(x̄, z′) Q(z, dz′) = βθ`. -/
theorem searchEV_top (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (z : Icc zlo zhi) : searchEV xbar Q f β θ (⟨xbar, hP.hx.le, le_rfl⟩, z) = β * θ := by
  simp only [searchEV, searchV_top Q hP hF, integral_const, probReal_univ, one_smul]

/-- `βθ ≤ β ∫ v(x, z′) Q(z, dz′) ≤ β (f(0, z̄) + θ)`. -/
theorem searchEV_bounds (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    β * θ ≤ searchEV xbar Q f β θ p ∧ searchEV xbar Q f β θ p ≤ β * (f 0 zhi + θ) := by
  have hint := integrable_searchSection Q (searchV xbar Q f β θ) p.1 p.2
  have h1 : θ ≤ ∫ z', searchV xbar Q f β θ (p.1, z') ∂Q p.2 := by
    have := integral_mono (integrable_const θ) hint fun z' =>
      (searchV_bounds Q hP hF (p.1, z')).1
    simpa only [integral_const, probReal_univ, one_smul] using this
  have h2 : ∫ z', searchV xbar Q f β θ (p.1, z') ∂Q p.2 ≤ f 0 zhi + θ := by
    have := integral_mono hint (integrable_const (f 0 zhi + θ)) fun z' =>
      (searchV_bounds Q hP hF (p.1, z')).2.trans (by linarith [hP.f_le (p.1, z')])
    simpa only [integral_const, probReal_univ, one_smul] using this
  exact ⟨mul_le_mul_of_nonneg_left h1 hP.hβ0.le, mul_le_mul_of_nonneg_left h2 hP.hβ0.le⟩

/-- `x ↦ β ∫ v(x, z′) Q(z, dz′) − θ` is strictly decreasing to the right of every point where it is
nonnegative. -/
theorem searchEV_strictDec (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) :
    SearchStrictDec fun p : Icc (0 : ℝ) xbar × Icc zlo zhi => searchEV xbar Q f β θ p - θ := by
  intro z x₁ x₂ hx h0
  simp only at h0 ⊢
  set v := searchV xbar Q f β θ
  have hkey : ∀ z', θ < v (x₁, z') → v (x₂, z') < v (x₁, z') := fun z' hlt => by
    rw [searchV_eq' Q hP hF] at hlt ⊢
    rw [searchV_eq' Q hP hF]
    have hf := hP.f_strictAnti z' hx
    have hEV := searchEV_anti Q hP hF hM (θ := θ) z' hx.le
    simp only at hf hEV
    have hA1 := (lt_max_iff.1 hlt).resolve_left (lt_irrefl _)
    refine max_lt (hA1.trans_le (le_max_right _ _)) (lt_of_lt_of_le ?_ (le_max_right _ _))
    linarith [min_le_min (le_refl θ) hEV]
  by_contra hge
  rw [not_lt] at hge
  have hint₁ := integrable_searchSection Q v x₁ z
  have hint₂ := integrable_searchSection Q v x₂ z
  have hle : ∫ z', v (x₁, z') ∂Q z ≤ ∫ z', v (x₂, z') ∂Q z := by
    have : searchEV xbar Q f β θ (x₁, z) ≤ searchEV xbar Q f β θ (x₂, z) := by linarith
    exact le_of_mul_le_mul_left this hP.hβ0
  have hnn : 0 ≤ fun z' => v (x₁, z') - v (x₂, z') := fun z' => by
    have := (searchV_anti_mono Q hP hF hM θ).1 z' hx.le
    simp only [Pi.zero_apply, sub_nonneg]; exact this
  have hzero : ∫ z', (v (x₁, z') - v (x₂, z')) ∂Q z = 0 := by
    rw [integral_sub hint₁ hint₂]
    have := integral_nonneg (μ := Q z) hnn
    rw [integral_sub hint₁ hint₂] at this
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hnn (hint₁.sub hint₂)).1 hzero
  have hae' : ∀ᵐ z' ∂Q z, v (x₁, z') ≤ θ := by
    filter_upwards [hae] with z' hz'
    by_contra hlt
    rw [not_le] at hlt
    have := hkey z' hlt
    simp only [Pi.zero_apply, sub_eq_zero] at hz'
    linarith
  have hint_le : ∫ z', v (x₁, z') ∂Q z ≤ θ := by
    have := integral_mono_ae hint₁ (integrable_const θ) hae'
    simpa only [integral_const, probReal_univ, one_smul] using this
  have hEV1 : searchEV xbar Q f β θ (x₁, z) ≤ β * θ :=
    mul_le_mul_of_nonneg_left hint_le hP.hβ0.le
  have hθ0 : θ = 0 := by nlinarith [hP.hβ1]
  have : (ae (Q z)).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨z', hz'⟩ := hae'.exists
  have hv1 : f x₁ z' ≤ v (x₁, z') := by
    rw [searchV_eq' Q hP hF]
    have := (searchEV_bounds Q hP hF (θ := θ) (x₁, z')).1
    rw [hθ0, mul_zero] at this
    simp only [hθ0, min_eq_left this, add_zero]
    exact le_max_right _ _
  have hf := hP.f_strictAnti z' hx
  have hf0 := hP.f_nonneg (x₂, z')
  simp only at hf hf0
  linarith

/-- **Exercise 13.8a.** For every `θ ≥ 0` (the book: `θ > 0`) there is a unique bounded continuous
`v ≥ 0` solving (4); `v ≤ max{θ, f(0, z̄)/(1 − β)}`, indeed `θ ≤ v ≤ f + θ`; and `v` is
nonincreasing in `x` and nondecreasing in `z`. -/
theorem ex_13_8a (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q) (hM : IsMonotoneTF Q)
    (hθ : 0 ≤ θ) :
    (∃! v : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ,
        (∀ p, 0 ≤ v p) ∧ ∀ p, v p = searchRHS Q f β θ v p) ∧
      (∀ p, searchV xbar Q f β θ p ≤ max θ (f 0 zhi / (1 - β))) ∧
      (∀ p, θ ≤ searchV xbar Q f β θ p ∧ searchV xbar Q f β θ p ≤ f p.1 p.2 + θ) ∧
      (∀ z, Antitone fun x => searchV xbar Q f β θ (x, z)) ∧
      ∀ x, Monotone fun z => searchV xbar Q f β θ (x, z) := by
  set v := searchV xbar Q f β θ
  have hvn : ∀ p, 0 ≤ v p := fun p => hθ.trans (searchV_bounds Q hP hF p).1
  have hnorm : ‖v‖ ≤ max θ (f 0 zhi + β * ‖v‖) :=
    (norm_le (le_max_of_le_left hθ)).2 fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hvn p), searchV_eq' Q hP hF]
      refine max_le_max le_rfl (add_le_add (hP.f_le p) ((min_le_right _ _).trans ?_))
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans ((lemma_12_14_cont Q hF v).2 p))
        hP.hβ0.le
  refine ⟨⟨v, ⟨hvn, searchV_eq Q hP hF θ⟩, fun w hw => searchV_unique Q hP hF θ w hw.2⟩,
    fun p => ?_, searchV_bounds Q hP hF, searchV_anti_mono Q hP hF hM θ⟩
  have hp : v p ≤ ‖v‖ :=
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact v.norm_coe_le_norm p)
  rcases le_max_iff.1 hnorm with h | h
  · exact (hp.trans h).trans (le_max_left _ _)
  · refine (hp.trans ?_).trans (le_max_right _ _)
    rw [le_div_iff₀ (sub_pos.2 hP.hβ1)]
    linarith

/-! ### The three cases and the law of motion `g` -/

/-- `(x, z) ↦ f(x, z) + β ∫ v(x, z′) Q(z, dz′)` is continuous. -/
theorem continuous_searchPhi (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q) :
    Continuous (searchPhi xbar Q f β θ) :=
  hP.continuous_f.add (continuous_searchEV Q hF)

/-- `x ↦ f(x, z) + β ∫ v(x, z′) Q(z, dz′)` is nonincreasing. -/
theorem searchPhi_anti (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (z : Icc zlo zhi) :
    Antitone fun x => searchPhi xbar Q f β θ (x, z) := fun _ _ hxx' =>
  add_le_add (hP.f_anti z hxx') (searchEV_anti Q hP hF hM z hxx')

/-- `z ↦ f(x, z) + β ∫ v(x, z′) Q(z, dz′)` is nondecreasing. -/
theorem searchPhi_mono (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (x : Icc (0 : ℝ) xbar) :
    Monotone fun z => searchPhi xbar Q f β θ (x, z) := fun _ _ hzz' =>
  add_le_add (hP.f_mono x hzz') (searchEV_mono Q hP hF hM x hzz')

/-- `x ↦ f(x, z) + β ∫ v(x, z′) Q(z, dz′)` is strictly decreasing. -/
theorem searchPhi_strictDec (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) :
    SearchStrictDec fun p : Icc (0 : ℝ) xbar × Icc zlo zhi => searchPhi xbar Q f β θ p - θ :=
  fun z _ _ hx _ => by
    have h1 := hP.f_strictAnti z hx
    have h2 := searchEV_anti Q hP hF hM (θ := θ) z hx.le
    simp only [searchPhi] at h1 h2 ⊢
    linarith

/-- `f(x̄, z) + β ∫ v(x̄, z′) Q(z, dz′) = βθ`. -/
theorem searchPhi_top (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (z : Icc zlo zhi) : searchPhi xbar Q f β θ (⟨xbar, hP.hx.le, le_rfl⟩, z) = β * θ := by
  rw [searchPhi, searchEV_top Q hP hF, hP.f_top, zero_add]

/-- (3a)–(3c): `v = θ` in Case A, `v = f + β∫v dQ` in Case B, `v = f + θ` in Case C. -/
theorem searchV_cases (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    (searchPhi xbar Q f β θ p < θ → searchV xbar Q f β θ p = θ) ∧
      (searchEV xbar Q f β θ p ≤ θ → θ ≤ searchPhi xbar Q f β θ p →
        searchV xbar Q f β θ p = searchPhi xbar Q f β θ p) ∧
      (θ < searchEV xbar Q f β θ p → searchV xbar Q f β θ p = f p.1 p.2 + θ) := by
  rw [searchV_eq' Q hP hF]
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · refine max_eq_left ((add_le_add le_rfl (min_le_right _ _)).trans h.le)
  · rw [min_eq_right h1]; exact max_eq_right h2
  · rw [min_eq_left h.le]
    refine max_eq_right ?_
    linarith [hP.f_nonneg p]

variable (xbar) in
/-- `g_C(z)`: the solution of (5c), `β ∫ v(g, z′) Q(z, dz′) = θ` (it does not depend on `x`);
`0` if `β ∫ v(0, z′) Q(z, dz′) ≤ θ`. -/
noncomputable def searchGC (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) (f : ℝ → ℝ → ℝ) (β θ : ℝ)
    [Nonempty (Icc (0 : ℝ) xbar)] : Icc zlo zhi → Icc (0 : ℝ) xbar :=
  searchCutoff fun p => searchEV xbar Q f β θ p - θ

variable (xbar) in
/-- `g_A(z)`: the solution of (5a), `f(g, z) + β ∫ v(g, z′) Q(z, dz′) ≤ θ` with equality if
`g > 0` (it does not depend on `x`). -/
noncomputable def searchGA (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) (f : ℝ → ℝ → ℝ) (β θ : ℝ)
    [Nonempty (Icc (0 : ℝ) xbar)] : Icc zlo zhi → Icc (0 : ℝ) xbar :=
  searchCutoff fun p => searchPhi xbar Q f β θ p - θ

variable (xbar) in
/-- The law of motion of the work force, `g(x, z) = min{max{x, g_C(z)}, g_A(z)}`
(Figure 13.2). -/
noncomputable def searchG (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) (f : ℝ → ℝ → ℝ) (β θ : ℝ)
    [Nonempty (Icc (0 : ℝ) xbar)] (p : Icc (0 : ℝ) xbar × Icc zlo zhi) : Icc (0 : ℝ) xbar :=
  min (max p.1 (searchGC xbar Q f β θ p.2)) (searchGA xbar Q f β θ p.2)

/-- `β ∫ v(x̄, z′) Q(z, dz′) − θ ≤ 0`. -/
theorem searchEV_low (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q) (hθ : 0 ≤ θ)
    (z : Icc zlo zhi) : ∃ x, searchEV xbar Q f β θ (x, z) - θ ≤ 0 :=
  ⟨⟨xbar, hP.hx.le, le_rfl⟩, by rw [searchEV_top Q hP hF]; nlinarith [hP.hβ1]⟩

/-- `f(x̄, z) + β ∫ v(x̄, z′) Q(z, dz′) − θ ≤ 0`. -/
theorem searchPhi_low (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q) (hθ : 0 ≤ θ)
    (z : Icc zlo zhi) : ∃ x, searchPhi xbar Q f β θ (x, z) - θ ≤ 0 :=
  ⟨⟨xbar, hP.hx.le, le_rfl⟩, by rw [searchPhi_top Q hP hF]; nlinarith [hP.hβ1]⟩

/-- The hypotheses of the cutoff lemmas for `x ↦ β ∫ v(x, z′) Q(z, dz′) − θ`. -/
theorem searchEV_hyps (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) :
    (∀ z, Continuous fun x => searchEV xbar Q f β θ (x, z) - θ) ∧
      (∀ z, Antitone fun x => searchEV xbar Q f β θ (x, z) - θ) ∧
      SearchStrictDec (fun p : Icc (0 : ℝ) xbar × Icc zlo zhi => searchEV xbar Q f β θ p - θ) ∧
      (∀ z, ∃ x, searchEV xbar Q f β θ (x, z) - θ ≤ 0) ∧
      (∀ x, Continuous fun z => searchEV xbar Q f β θ (x, z) - θ) ∧
      ∀ x, Monotone fun z => searchEV xbar Q f β θ (x, z) - θ :=
  ⟨fun _ => ((continuous_searchEV Q hF).comp (continuous_id.prodMk continuous_const)).sub
      continuous_const,
    fun z _ _ h => by have := searchEV_anti Q hP hF hM (θ := θ) z h; simp only at this ⊢; linarith,
    searchEV_strictDec Q hP hF hM hθ, searchEV_low Q hP hF hθ,
    fun _ => ((continuous_searchEV Q hF).comp (continuous_const.prodMk continuous_id)).sub
      continuous_const,
    fun x _ _ h => by have := searchEV_mono Q hP hF hM (θ := θ) x h; simp only at this ⊢; linarith⟩

/-- The hypotheses of the cutoff lemmas for `x ↦ f(x, z) + β ∫ v(x, z′) Q(z, dz′) − θ`. -/
theorem searchPhi_hyps (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) :
    (∀ z, Continuous fun x => searchPhi xbar Q f β θ (x, z) - θ) ∧
      (∀ z, Antitone fun x => searchPhi xbar Q f β θ (x, z) - θ) ∧
      SearchStrictDec (fun p : Icc (0 : ℝ) xbar × Icc zlo zhi => searchPhi xbar Q f β θ p - θ) ∧
      (∀ z, ∃ x, searchPhi xbar Q f β θ (x, z) - θ ≤ 0) ∧
      (∀ x, Continuous fun z => searchPhi xbar Q f β θ (x, z) - θ) ∧
      ∀ x, Monotone fun z => searchPhi xbar Q f β θ (x, z) - θ :=
  ⟨fun _ => ((continuous_searchPhi Q hP hF).comp (continuous_id.prodMk continuous_const)).sub
      continuous_const,
    fun z _ _ h => by
      have := searchPhi_anti Q hP hF hM (θ := θ) z h; simp only at this ⊢; linarith,
    searchPhi_strictDec Q hP hF hM, searchPhi_low Q hP hF hθ,
    fun _ => ((continuous_searchPhi Q hP hF).comp (continuous_const.prodMk continuous_id)).sub
      continuous_const,
    fun x _ _ h => by
      have := searchPhi_mono Q hP hF hM (θ := θ) x h; simp only at this ⊢; linarith⟩

variable [Nonempty (Icc (0 : ℝ) xbar)]

/-- `g_C(z)` is a cutoff of `x ↦ β ∫ v(x, z′) Q(z, dz′) − θ`. -/
theorem searchGC_isCutoff (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) (z : Icc zlo zhi) :
    IsSearchCutoff (fun p => searchEV xbar Q f β θ p - θ) z (searchGC xbar Q f β θ z) :=
  have H := searchEV_hyps Q hP hF hM hθ
  searchCutoff_isSearchCutoff (exists_isSearchCutoff_Icc H.1 H.2.1 H.2.2.2.1 z)

/-- `g_A(z)` is a cutoff of `x ↦ f(x, z) + β ∫ v(x, z′) Q(z, dz′) − θ`. -/
theorem searchGA_isCutoff (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) (z : Icc zlo zhi) :
    IsSearchCutoff (fun p => searchPhi xbar Q f β θ p - θ) z (searchGA xbar Q f β θ z) :=
  have H := searchPhi_hyps Q hP hF hM hθ
  searchCutoff_isSearchCutoff (exists_isSearchCutoff_Icc H.1 H.2.1 H.2.2.2.1 z)

/-- `β ∫ v(g_C(z), z′) Q(z, dz′) ≤ θ`, with equality if `g_C(z) > 0`. -/
theorem searchGC_spec (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) (z : Icc zlo zhi) :
    searchEV xbar Q f β θ (searchGC xbar Q f β θ z, z) ≤ θ ∧
      (0 < (searchGC xbar Q f β θ z : ℝ) →
        searchEV xbar Q f β θ (searchGC xbar Q f β θ z, z) = θ) := by
  have H := searchEV_hyps Q hP hF hM hθ
  have := searchCutoff_spec_Icc H.1 H.2.1 H.2.2.1 H.2.2.2.1 z
  unfold searchGC
  exact ⟨by linarith [this.1], fun h => by linarith [this.2 h]⟩

/-- `f(g_A(z), z) + β ∫ v(g_A(z), z′) Q(z, dz′) ≤ θ`, with equality if `g_A(z) > 0`. -/
theorem searchGA_spec (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) (z : Icc zlo zhi) :
    searchPhi xbar Q f β θ (searchGA xbar Q f β θ z, z) ≤ θ ∧
      (0 < (searchGA xbar Q f β θ z : ℝ) →
        searchPhi xbar Q f β θ (searchGA xbar Q f β θ z, z) = θ) := by
  have H := searchPhi_hyps Q hP hF hM hθ
  have := searchCutoff_spec_Icc H.1 H.2.1 H.2.2.1 H.2.2.2.1 z
  unfold searchGA
  exact ⟨by linarith [this.1], fun h => by linarith [this.2 h]⟩

/-- `g_C(z) ≤ g_A(z)`. -/
theorem searchGC_le_searchGA (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) (z : Icc zlo zhi) :
    searchGC xbar Q f β θ z ≤ searchGA xbar Q f β θ z :=
  have H := searchEV_hyps Q hP hF hM hθ
  have H' := searchPhi_hyps Q hP hF hM hθ
  (searchGC_isCutoff Q hP hF hM hθ z).le_of_le H.2.2.1 H'.2.1 H'.2.2.1
    (searchGA_isCutoff Q hP hF hM hθ z) fun x => by
      simp only [searchPhi]; linarith [hP.f_nonneg (x, z)]

/-- `g_C` is nondecreasing in `z`. -/
theorem searchGC_mono (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) : Monotone (searchGC xbar Q f β θ) := fun _ _ hzz' =>
  have H := searchEV_hyps Q hP hF hM hθ
  (searchGC_isCutoff Q hP hF hM hθ _).le_of_le H.2.2.1 H.2.1 H.2.2.1
    (searchGC_isCutoff Q hP hF hM hθ _) fun x => H.2.2.2.2.2 x hzz'

/-- `g_A` is nondecreasing in `z`. -/
theorem searchGA_mono (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) : Monotone (searchGA xbar Q f β θ) := fun _ _ hzz' =>
  have H := searchPhi_hyps Q hP hF hM hθ
  (searchGA_isCutoff Q hP hF hM hθ _).le_of_le H.2.2.1 H.2.1 H.2.2.1
    (searchGA_isCutoff Q hP hF hM hθ _) fun x => H.2.2.2.2.2 x hzz'

/-- `g_C` is continuous in `z`. -/
theorem continuous_searchGC (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) : Continuous (searchGC xbar Q f β θ) :=
  have H := searchEV_hyps Q hP hF hM hθ
  continuous_searchCutoff H.2.1 H.2.2.1 (exists_isSearchCutoff_Icc H.1 H.2.1 H.2.2.2.1)
    H.2.2.2.2.1

/-- `g_A` is continuous in `z`. -/
theorem continuous_searchGA (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) : Continuous (searchGA xbar Q f β θ) :=
  have H := searchPhi_hyps Q hP hF hM hθ
  continuous_searchCutoff H.2.1 H.2.2.1 (exists_isSearchCutoff_Icc H.1 H.2.1 H.2.2.2.1)
    H.2.2.2.2.1
omit [IsMarkovKernel Q] in
/-- `g(x, z) = min{max{x, g_C(z)}, g_A(z)}` in coordinates. -/
theorem searchG_coe (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    (searchG xbar Q f β θ p : ℝ) =
      min (max (p.1 : ℝ) (searchGC xbar Q f β θ p.2)) (searchGA xbar Q f β θ p.2) := by
  simp [searchG]

/-- In Case A (2a), `g(x, z) = g_A(z)`. -/
theorem searchG_caseA (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) {x : Icc (0 : ℝ) xbar} {z : Icc zlo zhi}
    (h : searchPhi xbar Q f β θ (x, z) < θ) :
    searchG xbar Q f β θ (x, z) = searchGA xbar Q f β θ z := by
  have hax : searchGA xbar Q f β θ z ≤ x := by
    by_contra hlt
    rw [not_le] at hlt
    have := (searchGA_isCutoff Q hP hF hM hθ z).1 x hlt
    simp only at this
    linarith
  simp only [searchG]
  rw [max_eq_left ((searchGC_le_searchGA Q hP hF hM hθ z).trans hax), min_eq_right hax]

/-- In Case B (2b), `g(x, z) = x`. -/
theorem searchG_caseB (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) {x : Icc (0 : ℝ) xbar} {z : Icc zlo zhi}
    (h1 : searchEV xbar Q f β θ (x, z) ≤ θ) (h2 : θ ≤ searchPhi xbar Q f β θ (x, z)) :
    searchG xbar Q f β θ (x, z) = x := by
  have H := searchEV_hyps Q hP hF hM hθ
  have H' := searchPhi_hyps Q hP hF hM hθ
  have hxa : x ≤ searchGA xbar Q f β θ z := by
    by_contra hlt
    rw [not_le] at hlt
    have := (searchGA_isCutoff Q hP hF hM hθ z).neg_of_lt H'.2.1 H'.2.2.1 hlt
    linarith
  have hcx : searchGC xbar Q f β θ z ≤ x := by
    by_contra hlt
    rw [not_le] at hlt
    have := (searchGC_isCutoff Q hP hF hM hθ z).pos_of_lt H.2.2.1 hlt
    linarith
  simp only [searchG]
  rw [max_eq_left hcx, min_eq_left hxa]

/-- In Case C (2c), `g(x, z) = g_C(z) > x` and `β ∫ v(g_C(z), z′) Q(z, dz′) = θ`. -/
theorem searchG_caseC (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) {x : Icc (0 : ℝ) xbar} {z : Icc zlo zhi}
    (h : θ < searchEV xbar Q f β θ (x, z)) :
    x < searchGC xbar Q f β θ z ∧ searchG xbar Q f β θ (x, z) = searchGC xbar Q f β θ z ∧
      searchEV xbar Q f β θ (searchGC xbar Q f β θ z, z) = θ := by
  have hspec := searchGC_spec Q hP hF hM hθ z
  have hxc : x < searchGC xbar Q f β θ z := by
    by_contra hle
    rw [not_lt] at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at hspec; linarith [hspec.1]
    · have := (searchGC_isCutoff Q hP hF hM hθ z).2 x hlt
      simp only at this
      linarith
  refine ⟨hxc, ?_, hspec.2 (lt_of_le_of_lt x.2.1 hxc)⟩
  simp only [searchG]
  rw [max_eq_right hxc.le, min_eq_left (searchGC_le_searchGA Q hP hF hM hθ z)]

/-- **Exercise 13.8b.** `g` satisfies (5a)–(5c) on the regions (2a)–(2c), is nondecreasing in `x`
and in `z`, and `|g(x, z) − g(x′, z)| ≤ |x − x′|`. -/
theorem ex_13_8b (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q) (hM : IsMonotoneTF Q)
    (hθ : 0 ≤ θ) :
    (∀ x z, searchPhi xbar Q f β θ (x, z) < θ →
        searchPhi xbar Q f β θ (searchG xbar Q f β θ (x, z), z) ≤ θ ∧
          (0 < (searchG xbar Q f β θ (x, z) : ℝ) →
            searchPhi xbar Q f β θ (searchG xbar Q f β θ (x, z), z) = θ)) ∧
      (∀ x z, searchEV xbar Q f β θ (x, z) ≤ θ → θ ≤ searchPhi xbar Q f β θ (x, z) →
        searchG xbar Q f β θ (x, z) = x) ∧
      (∀ x z, θ < searchEV xbar Q f β θ (x, z) →
        searchEV xbar Q f β θ (searchG xbar Q f β θ (x, z), z) = θ) ∧
      (∀ z, Monotone fun x => searchG xbar Q f β θ (x, z)) ∧
      (∀ x, Monotone fun z => searchG xbar Q f β θ (x, z)) ∧
      ∀ z x x', |(searchG xbar Q f β θ (x, z) : ℝ) - searchG xbar Q f β θ (x', z)| ≤
        |(x : ℝ) - x'| := by
  refine ⟨fun x z h => ?_, fun x z h1 h2 => searchG_caseB Q hP hF hM hθ h1 h2,
    fun x z h => ?_, fun z x x' hxx' => min_le_min (max_le_max hxx' le_rfl) le_rfl,
    fun x z z' hzz' => min_le_min (max_le_max le_rfl (searchGC_mono Q hP hF hM hθ hzz'))
      (searchGA_mono Q hP hF hM hθ hzz'), fun z x x' => ?_⟩
  · rw [searchG_caseA Q hP hF hM hθ h]
    exact searchGA_spec Q hP hF hM hθ z
  · obtain ⟨-, h1, h2⟩ := searchG_caseC Q hP hF hM hθ h
    rw [h1, h2]
  · rw [searchG_coe, searchG_coe]
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
    exact abs_max_sub_max_le_abs _ _ _

/-- **Exercise 13.8b** (uniqueness). (5a)–(5c) determine `g`: `x ↦ f(x, z) + β∫v(x, z′)Q(z, dz′)`
is strictly decreasing and `x ↦ β∫v(x, z′)Q(z, dz′)` is strictly decreasing where it is `≥ θ`
(`searchEV_strictDec`), so the solutions of (5a) and (5c) are unique and no extreme-solution
convention is needed. -/
theorem ex_13_8b_unique (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) (g' : Icc (0 : ℝ) xbar × Icc zlo zhi → Icc (0 : ℝ) xbar)
    (h5a : ∀ x z, searchPhi xbar Q f β θ (x, z) < θ →
      searchPhi xbar Q f β θ (g' (x, z), z) ≤ θ ∧
        (0 < (g' (x, z) : ℝ) → searchPhi xbar Q f β θ (g' (x, z), z) = θ))
    (h5b : ∀ x z, searchEV xbar Q f β θ (x, z) ≤ θ → θ ≤ searchPhi xbar Q f β θ (x, z) →
      g' (x, z) = x)
    (h5c : ∀ x z, θ < searchEV xbar Q f β θ (x, z) →
      searchEV xbar Q f β θ (g' (x, z), z) = θ) :
    g' = searchG xbar Q f β θ := by
  have H := searchEV_hyps Q hP hF hM hθ
  have H' := searchPhi_hyps Q hP hF hM hθ
  funext ⟨x, z⟩
  rcases lt_or_ge (searchPhi xbar Q f β θ (x, z)) θ with hA | hA
  · rw [searchG_caseA Q hP hF hM hθ hA]
    obtain ⟨h1, h2⟩ := h5a x z hA
    unfold searchGA
    rcases lt_or_eq_of_le (g' (x, z)).2.1 with hpos | hzero
    · exact (searchCutoff_eq H'.2.1 H'.2.2.1 (isSearchCutoff_of_eq_zero H'.2.1
        (by linarith [h2 hpos]))).symm
    · refine (searchCutoff_eq H'.2.1 H'.2.2.1 (isSearchCutoff_of_le_zero H'.2.1
        (fun y => ?_) (by linarith))).symm
      change (g' (x, z) : ℝ) ≤ y
      rw [← hzero]; exact y.2.1
  · rcases lt_or_ge θ (searchEV xbar Q f β θ (x, z)) with hC | hC
    · rw [(searchG_caseC Q hP hF hM hθ hC).2.1]
      unfold searchGC
      exact (searchCutoff_eq H.2.1 H.2.2.1 (isSearchCutoff_of_eq_zero H.2.1
        (by linarith [h5c x z hC]))).symm
    · rw [searchG_caseB Q hP hF hM hθ hC hA, h5b x z hC hA]

/-- **Exercise 13.8c.** `g` is continuous on `X × Z` (the cutoffs `g_C`, `g_A` are continuous in
`z`, `continuous_searchCutoff`). -/
theorem ex_13_8c (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q) (hM : IsMonotoneTF Q)
    (hθ : 0 ≤ θ) : Continuous (searchG xbar Q f β θ) :=
  (continuous_fst.max ((continuous_searchGC Q hP hF hM hθ).comp continuous_snd)).min
    ((continuous_searchGA Q hP hF hM hθ).comp continuous_snd)

end StokeyLucasPrescott.ConvergenceApplications

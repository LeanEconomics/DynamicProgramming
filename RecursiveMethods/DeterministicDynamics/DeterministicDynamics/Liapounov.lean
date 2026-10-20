/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.EulerEquations

/-!
# Global stability: Liapounov functions

SLP §6.2, pp. 139–143.

* **Lemma 6.2** (`lemma_6_2`): on a compact metric space `X`, let `g : X → X` be continuous with
  `g(x̄) = x̄`, and let `L` be continuous with (b) `L[g(x)] ≥ L(x)`, with equality only at `x̄`.
  Then `x_{t+1} = g(x_t)` converges to `x̄` from every `x₀`. Hypothesis (a) (`L ≤ 0`, zero only at
  `x̄`) is not needed: `L` is bounded on the compact `X` (`lemma_6_2_book` states the book's form).
* **The value loss** `L(x) = (x − x̄)·[v'(x) − v'(x̄)]` (p. 142), in a real inner product space.
  * (a) holds when `v` is strictly concave (`valueLoss_nonpos`).
  * From (3)–(5): (6) `v'(x̄) = F_x(x̄, x̄) = −F_y(x̄, x̄)/β` (`six`), and (7)
    `L(x) − βL[g(x)] ≤ 0`, with equality only at `x̄` (`seven`). So with `β = 1`, `L` satisfies
    (b) (`valueLoss_beta_one`).
  * Condition (8) gives `L[g(x)] ≥ L(x)` (`valueLoss_of_eight`), and strict (8) gives (b).
  * With (b), paths from a compact invariant set converge to `x̄` (`globally_stable`).
* **Exercise 6.4** (quadratic `F` on `ℝ`).
  * (8) holds iff `βbd ≥ (1 + β)²c²/4` (`ex_6_4`).
  * The book's condition `bd − (1 + β)²c²/4 ≥ 0` is not sufficient
    (`ex_6_4_book_condition_fails`).
  * `x̄` is the unique stationary point iff `(1 + β)c + d + βb ≠ 0` (`ex_6_4_stationary`). That can
    fail for a strictly concave `F` (`ex_6_4_not_unique`), but not under the strict form of the
    corrected condition (`ex_6_4_unique_of_eight`).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

/-! ### Lemma 6.2 -/

/-- **Lemma 6.2** (without hypothesis (a)). -/
theorem lemma_6_2 {X : Type*} [MetricSpace X] [CompactSpace X] {g : X → X} (hg : Continuous g)
    {xbar : X} {L : X → ℝ} (hL : Continuous L)
    (hb : ∀ x, L x ≤ L (g x) ∧ (L (g x) = L x → x = xbar)) (x₀ : X) :
    Tendsto (fun t => g^[t] x₀) atTop (𝓝 xbar) := by
  set x : ℕ → X := fun t => g^[t] x₀
  have hstep : ∀ t, x (t + 1) = g (x t) := fun t => Function.iterate_succ_apply' g t x₀
  -- `L(x_t)` rises and is bounded, so it converges
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hL.continuousOn
  have hmono : Monotone fun t => L (x t) := monotone_nat_of_le_succ fun t => by
    rw [hstep]; exact (hb _).1
  have hbdd : BddAbove (range fun t => L (x t)) := ⟨B, by
    rintro _ ⟨t, rfl⟩; exact (le_abs_self _).trans (by simpa using hB (x t) (mem_univ _))⟩
  have hLlim := tendsto_atTop_ciSup hmono hbdd
  set L₀ := ⨆ t, L (x t)
  -- every subsequence has a further subsequence converging to `x̄`
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨y, -, φ, hφ, hy⟩ := isCompact_univ.tendsto_subseq (x := fun n => x (ns n))
    fun _ => mem_univ _
  refine ⟨φ, ?_⟩
  have hsub : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have h1 : L y = L₀ := tendsto_nhds_unique ((hL.tendsto y).comp hy) (hLlim.comp hsub)
  have h2 : L (g y) = L₀ := by
    have hgy : Tendsto (fun n => x (ns (φ n) + 1)) atTop (𝓝 (g y)) := by
      simp only [hstep]
      exact (hg.tendsto y).comp hy
    exact tendsto_nhds_unique ((hL.tendsto (g y)).comp hgy)
      (hLlim.comp ((tendsto_add_atTop_nat 1).comp hsub))
  have : y = xbar := (hb y).2 (h2.trans h1.symm)
  rw [← this]
  exact hy

/-- **Lemma 6.2** as stated in the book, with both (a) and (b). -/
theorem lemma_6_2_book {X : Type*} [MetricSpace X] [CompactSpace X] {g : X → X}
    (hg : Continuous g) {xbar : X} (_hfix : g xbar = xbar) {L : X → ℝ} (hL : Continuous L)
    (_ha : ∀ x, L x ≤ 0 ∧ (L x = 0 → x = xbar))
    (hb : ∀ x, L x ≤ L (g x) ∧ (L (g x) = L x → x = xbar)) (x₀ : X) :
    Tendsto (fun t => g^[t] x₀) atTop (𝓝 xbar) :=
  lemma_6_2 hg hL hb x₀

/-! ### The value loss -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The value loss `L(x) = (x − x̄)·[v'(x) − v'(x̄)]`. -/
def valueLoss (v' : E → E) (xbar x : E) : ℝ := inner ℝ (x - xbar) (v' x - v' xbar)

/-- **(a)** for the value loss: `L ≤ 0`, with equality only at `x̄`, when `v` is strictly concave
with gradient `v'`. -/
theorem valueLoss_nonpos [CompleteSpace E] {X : Set E} {v : E → ℝ} {v' : E → E}
    (hv : StrictConcaveOn ℝ X v)
    (hd : ∀ x ∈ X, HasGradientAt v (v' x) x) {xbar : E} (hxbar : xbar ∈ X) {x : E}
    (hx : x ∈ X) : valueLoss v' xbar x ≤ 0 ∧ (valueLoss v' xbar x = 0 → x = xbar) := by
  -- tangent inequalities, strict off the point of tangency
  have tan : ∀ p ∈ X, ∀ q ∈ X, v q ≤ v p + inner ℝ (v' p) (q - p) := fun p hp q hq => by
    have := concave_le_fderiv hv.concaveOn hp hq (hd p hp).hasFDerivAt
    simpa using this
  have tanlt : ∀ p ∈ X, ∀ q ∈ X, p ≠ q → v q < v p + inner ℝ (v' p) (q - p) :=
    fun p hp q hq hpq => by
      have hm : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q ∈ X :=
        hv.1 hp hq (by norm_num) (by norm_num) (by norm_num)
      have h1 := tan p hp _ hm
      have h2 := hv.2 hp hq hpq (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num)
      have e : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q - p = (1 / 2 : ℝ) • (q - p) := by module
      rw [e, inner_smul_right] at h1
      simp only [smul_eq_mul] at h2
      linarith
  have key : ∀ p ∈ X, ∀ q ∈ X, inner ℝ (p - q) (v' p - v' q) ≤ 0 := fun p hp q hq => by
    have h1 := tan p hp q hq
    have h2 := tan q hq p hp
    have e : inner ℝ (p - q) (v' p - v' q) =
        -(inner ℝ (v' p) (q - p)) - inner ℝ (v' q) (p - q) := by
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    linarith
  refine ⟨key x hx xbar hxbar, fun h0 => by_contra fun hne => ?_⟩
  have h1 := tanlt x hx xbar hxbar hne
  have h2 := tanlt xbar hxbar x hx (Ne.symm hne)
  have e : inner ℝ (x - xbar) (v' x - v' xbar) =
      -(inner ℝ (v' x) (xbar - x)) - inner ℝ (v' xbar) (x - xbar) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  simp only [valueLoss] at h0
  linarith

/-- The facts of p. 142: on a set `A` of pairs containing `(x̄, x̄)` and the graph of `g`,
(3) the gradient `(F_x, F_y)` of `F` is strictly monotone, (4) `F_y[x, g(x)] = −βv'[g(x)]` and
(5) `F_x[x, g(x)] = v'(x)`. -/
structure LossFacts (A : Set (E × E)) (Fx Fy : E → E → E) (v' g : E → E) (β : ℝ) (xbar : E) where
  fix : g xbar = xbar
  mem_bar : (xbar, xbar) ∈ A
  three : ∀ p ∈ A, ∀ q ∈ A,
    inner ℝ (p.1 - q.1) (Fx p.1 p.2 - Fx q.1 q.2) + inner ℝ (p.2 - q.2) (Fy p.1 p.2 - Fy q.1 q.2) ≤
      0 ∧ (inner ℝ (p.1 - q.1) (Fx p.1 p.2 - Fx q.1 q.2) +
        inner ℝ (p.2 - q.2) (Fy p.1 p.2 - Fy q.1 q.2) = 0 → p = q)
  four : ∀ x, (x, g x) ∈ A → Fy x (g x) = -(β • v' (g x))
  five : ∀ x, (x, g x) ∈ A → Fx x (g x) = v' x

namespace LossFacts

variable {A : Set (E × E)} {Fx Fy : E → E → E} {v' g : E → E} {β : ℝ} {xbar : E}
  (H : LossFacts A Fx Fy v' g β xbar)
include H

/-- (6): `v'(x̄) = F_x(x̄, x̄)` and `F_y(x̄, x̄) = −βv'(x̄)`. -/
theorem six : v' xbar = Fx xbar xbar ∧ Fy xbar xbar = -(β • v' xbar) := by
  have hA : (xbar, g xbar) ∈ A := by rw [H.fix]; exact H.mem_bar
  have h4 := H.four xbar hA
  have h5 := H.five xbar hA
  rw [H.fix] at h4 h5
  exact ⟨h5.symm, h4⟩

/-- (7): `L(x) − βL[g(x)] ≤ 0`, with equality only at `x̄`. -/
theorem seven {x : E} (hx : (x, g x) ∈ A) :
    valueLoss v' xbar x - β * valueLoss v' xbar (g x) ≤ 0 ∧
      (valueLoss v' xbar x - β * valueLoss v' xbar (g x) = 0 → x = xbar) := by
  obtain ⟨h6x, h6y⟩ := H.six
  have e : inner ℝ ((x, g x).1 - (xbar, xbar).1) (Fx (x, g x).1 (x, g x).2 - Fx xbar xbar) +
      inner ℝ ((x, g x).2 - (xbar, xbar).2) (Fy (x, g x).1 (x, g x).2 - Fy xbar xbar) =
      valueLoss v' xbar x - β * valueLoss v' xbar (g x) := by
    simp only [H.four x hx, H.five x hx, h6y, ← h6x, valueLoss]
    rw [show -(β • v' (g x)) - -(β • v' xbar) = -(β • (v' (g x) - v' xbar)) by
      rw [smul_sub]; abel, inner_neg_right, inner_smul_right]
    ring
  obtain ⟨h3, h3eq⟩ := H.three (x, g x) hx (xbar, xbar) H.mem_bar
  rw [e] at h3 h3eq
  exact ⟨h3, fun h0 => (Prod.mk.inj (h3eq h0)).1⟩

/-- With `β = 1`, the value loss satisfies (b) of Lemma 6.2. -/
theorem valueLoss_beta_one (hβ : β = 1) {x : E} (hx : (x, g x) ∈ A) :
    valueLoss v' xbar x ≤ valueLoss v' xbar (g x) ∧
      (valueLoss v' xbar (g x) = valueLoss v' xbar x → x = xbar) := by
  obtain ⟨h7, h7eq⟩ := H.seven hx
  rw [hβ, one_mul] at h7 h7eq
  exact ⟨by linarith, fun h => h7eq (by linarith)⟩

/-- (8) gives `L[g(x)] ≥ L(x)` when `β > 0`; strict (8) off `(x̄, x̄)` gives (b). -/
theorem valueLoss_of_eight (hβ : 0 < β)
    (h8 : ∀ p ∈ A, β * inner ℝ (p.1 - xbar) (Fx p.1 p.2 - Fx xbar xbar) +
      inner ℝ (p.2 - xbar) (Fy p.1 p.2 - Fy xbar xbar) ≤ 0) {x : E} (hx : (x, g x) ∈ A) :
    valueLoss v' xbar x ≤ valueLoss v' xbar (g x) := by
  obtain ⟨h6x, h6y⟩ := H.six
  have h := h8 (x, g x) hx
  simp only [H.four x hx, H.five x hx, h6y, ← h6x] at h
  rw [show -(β • v' (g x)) - -(β • v' xbar) = -(β • (v' (g x) - v' xbar)) by
    rw [smul_sub]; abel, inner_neg_right, inner_smul_right] at h
  simp only [valueLoss]
  nlinarith

theorem valueLoss_of_eight_strict (hβ : 0 < β)
    (h8 : ∀ p ∈ A, p ≠ (xbar, xbar) → β * inner ℝ (p.1 - xbar) (Fx p.1 p.2 - Fx xbar xbar) +
      inner ℝ (p.2 - xbar) (Fy p.1 p.2 - Fy xbar xbar) < 0) {x : E} (hx : (x, g x) ∈ A) :
    valueLoss v' xbar x ≤ valueLoss v' xbar (g x) ∧
      (valueLoss v' xbar (g x) = valueLoss v' xbar x → x = xbar) := by
  obtain ⟨h6x, h6y⟩ := H.six
  have e : ∀ p : E × E, p = (x, g x) →
      β * inner ℝ (p.1 - xbar) (Fx p.1 p.2 - Fx xbar xbar) +
        inner ℝ (p.2 - xbar) (Fy p.1 p.2 - Fy xbar xbar) =
      β * (valueLoss v' xbar x - valueLoss v' xbar (g x)) := by
    rintro p rfl
    simp only [H.four x hx, H.five x hx, h6y, ← h6x, valueLoss]
    rw [show -(β • v' (g x)) - -(β • v' xbar) = -(β • (v' (g x) - v' xbar)) by
      rw [smul_sub]; abel, inner_neg_right, inner_smul_right]
    ring
  by_cases hxb : x = xbar
  · subst hxb
    simp [H.fix]
  · have hne : (x, g x) ≠ (xbar, xbar) := fun h => hxb (Prod.mk.inj h).1
    have h := h8 (x, g x) hx hne
    rw [e _ rfl] at h
    have hlt : valueLoss v' xbar x - valueLoss v' xbar (g x) < 0 := by
      by_contra hc
      push Not at hc
      have := mul_nonneg hβ.le hc
      linarith
    exact ⟨by linarith, fun h0 => (by linarith : False).elim⟩

end LossFacts

omit [InnerProductSpace ℝ E] in
/-- **Global stability from a Liapounov function on a compact set.** If `g` maps a compact
`X ⊆ E` into itself continuously, and a continuous `L` satisfies (b) on `X`, then every path
from `X` converges to `x̄`. With the value loss, (b) holds for `β = 1` (`valueLoss_beta_one`) or
under strict (8) (`valueLoss_of_eight_strict`). -/
theorem globally_stable {X : Set E} (hX : IsCompact X) {g : E → E} (hgX : MapsTo g X X)
    (hgc : ContinuousOn g X) {xbar : E} (hxbar : xbar ∈ X) {L : E → ℝ} (hL : ContinuousOn L X)
    (hb : ∀ x ∈ X, L x ≤ L (g x) ∧ (L (g x) = L x → x = xbar)) {x₀ : E} (hx₀ : x₀ ∈ X) :
    Tendsto (fun t => g^[t] x₀) atTop (𝓝 xbar) := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX
  set gX : X → X := fun x => ⟨g x, hgX x.2⟩
  have hgXc : Continuous gX :=
    (hgc.comp_continuous continuous_subtype_val fun x => x.2).subtype_mk _
  have hLX : Continuous fun x : X => L x := hL.comp_continuous continuous_subtype_val fun x => x.2
  have hlim := lemma_6_2 hgXc (xbar := ⟨xbar, hxbar⟩) hLX (fun x => ⟨(hb x x.2).1,
    fun h => Subtype.ext ((hb x x.2).2 h)⟩) ⟨x₀, hx₀⟩
  have hiter : ∀ t, (gX^[t] ⟨x₀, hx₀⟩).1 = g^[t] x₀ := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
  have := (continuous_subtype_val.tendsto _).comp hlim
  simpa [Function.comp_def, hiter] using this

/-! ### Exercise 6.4 -/

/-- The quadratic form of (8) for Exercise 6.4: with `u = x − x̄`, `w = y − x̄`,
`β(x − x̄)[F_x(x, y) − F_x(x̄, x̄)] + (y − x̄)[F_y(x, y) − F_y(x̄, x̄)]`
`= βbu² + (1 + β)cuw + dw²`. -/
theorem ex_6_4_form (a b c d β xbar x y : ℝ) :
    β * ((x - xbar) * ((a + b * (x - xbar) + c * (y - xbar)) - (a + b * 0 + c * 0))) +
      (y - xbar) * ((-(β * a) + c * (x - xbar) + d * (y - xbar)) - (-(β * a) + c * 0 + d * 0)) =
    β * b * (x - xbar) ^ 2 + (1 + β) * c * (x - xbar) * (y - xbar) + d * (y - xbar) ^ 2 := by
  ring

/-- **Exercise 6.4 (corrected).** With `d < 0`, (8) holds for all `(x, y)`
if and only if `βbd − (1 + β)²c²/4 ≥ 0`. -/
theorem ex_6_4 {b c d β : ℝ} (hd : d < 0) :
    (∀ u w : ℝ, β * b * u ^ 2 + (1 + β) * c * u * w + d * w ^ 2 ≤ 0) ↔
      0 ≤ β * b * d - (1 + β) ^ 2 * c ^ 2 / 4 := by
  constructor
  · intro h
    -- take `u = 1`, `w = −(1 + β)c/(2d)`
    have := h (2 * d) (-((1 + β) * c))
    nlinarith
  · intro h u w
    -- complete the square in `w`
    have hdd : 0 < -d := by linarith
    have key : 4 * (-d) * (β * b * u ^ 2 + (1 + β) * c * u * w + d * w ^ 2) =
        -(4 * (β * b * d - (1 + β) ^ 2 * c ^ 2 / 4) * u ^ 2) -
          (2 * d * w + (1 + β) * c * u) ^ 2 := by ring
    have : 4 * (-d) * (β * b * u ^ 2 + (1 + β) * c * u * w + d * w ^ 2) ≤ 0 := by
      rw [key]; nlinarith [sq_nonneg u, sq_nonneg (2 * d * w + (1 + β) * c * u)]
    nlinarith

/-- **Exercise 6.4 (correction).** The book's condition `bd − (1 + β)²c²/4 ≥ 0` does not give (8):
with `b = d = −1`, `c = 1/2`, `β = 1/100`, `F` is strictly concave and the book's condition holds,
but (8) fails at `u = 1`, `w = 1/4`. -/
theorem ex_6_4_book_condition_fails :
    let b : ℝ := -1; let c : ℝ := 1 / 2; let d : ℝ := -1; let β : ℝ := 1 / 100
    b < 0 ∧ d < 0 ∧ 0 < b * d - c ^ 2 ∧ 0 ≤ b * d - (1 + β) ^ 2 * c ^ 2 / 4 ∧
      0 < β * b * 1 ^ 2 + (1 + β) * c * 1 * (1 / 4) + d * (1 / 4) ^ 2 := by
  norm_num

/-- The stationary points of Exercise 6.4: `z` is stationary (`F_y(z, z) + βF_x(z, z) = 0`) iff
`[(1 + β)c + d + βb](z − x̄) = 0`; so `x̄` is the unique stationary point iff
`(1 + β)c + d + βb ≠ 0`. -/
theorem ex_6_4_stationary (a b c d β xbar : ℝ) :
    (∀ z, (-(β * a) + c * (z - xbar) + d * (z - xbar)) + β * (a + b * (z - xbar) + c * (z - xbar))
        = 0 → z = xbar) ↔ (1 + β) * c + d + β * b ≠ 0 := by
  constructor
  · intro h h0
    have := h (xbar + 1) (by linear_combination h0)
    linarith
  · intro h z hz
    have : ((1 + β) * c + d + β * b) * (z - xbar) = 0 := by linear_combination hz
    have := (mul_eq_zero.1 this).resolve_left h
    linarith

/-- **Exercise 6.4 (correction).** Strict concavity does not make `x̄` the unique stationary
point: with `b = −4`, `d = −1`, `β = 1/100`, `c = 104/101`, `F` is strictly concave but
`(1 + β)c + d + βb = 0`, so every point is stationary. -/
theorem ex_6_4_not_unique :
    let b : ℝ := -4; let c : ℝ := 104 / 101; let d : ℝ := -1; let β : ℝ := 1 / 100
    b < 0 ∧ d < 0 ∧ 0 < b * d - c ^ 2 ∧ (1 + β) * c + d + β * b = 0 := by
  norm_num

/-- Under the strict form of the corrected condition, `βbd > (1 + β)²c²/4`, the stationary point is
unique. -/
theorem ex_6_4_unique_of_eight {b c d β : ℝ} (h : (1 + β) ^ 2 * c ^ 2 / 4 < β * b * d) :
    (1 + β) * c + d + β * b ≠ 0 := by
  intro h0
  -- `(1 + β)c = −(d + βb)`, and `(d + βb)² ≥ 4βbd`
  have hsq : (1 + β) ^ 2 * c ^ 2 = (d + β * b) ^ 2 := by
    have : (1 + β) * c = -(d + β * b) := by linarith
    rw [show (1 + β) ^ 2 * c ^ 2 = ((1 + β) * c) ^ 2 by ring, this, neg_sq]
  nlinarith [sq_nonneg (d - β * b)]

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.Sign.Basic

/-!
# Bisection

AKMM, §10.2–10.2.1, pp. 263–265. The bisection method for `f(x) = 0`:

1. bracketing: `sign(f a) ≠ sign(f b)`; for continuous `f` there is a root in `[a, b]`
   (`bisect_bracket_root`);
2. the step: with `c = (a + b)/2`, replace `a` by `c` if `sign(f c) = sign(f a)`, otherwise
   replace `b` by `c` (`bisectStep`, `bisect_sign_eq_iff`);
3. stop when `b − a` is below the tolerance.

Proved: each step halves the bracket (`bisect_length`), the sign change is kept
(`bisect_bracket`), the endpoints converge to a root of a continuous `f` and `f(a_k) → 0`
(`bisect_converges`); the number of steps needed for a tolerance `ε` is any `k > log₂((b−a)/ε)`
(`bisect_iteration_count`), and 10 steps reach `10⁻³` on `[0, 1]` where 9 do not
(`bisect_ten_steps`). The procedure ends even when no root exists: a discontinuous bracketing
function with no zero (`bisect_discontinuous_no_root`).

Departure: the step tests `0 < f a · f c` instead of `sign(f c) = sign(f a)`; the two agree
whenever `f a ≠ 0` (`bisect_sign_eq_iff`), which holds at the start of the book's bracket.
-/

namespace AKMM.ComputationalTools

open Filter Topology

/-- AKMM, p. 264, the comparison in step 2: when `f a ≠ 0`, `sign(f c) = sign(f a)` exactly
when `f a · f c > 0`. -/
theorem bisect_sign_eq_iff {x y : ℝ} (hx : x ≠ 0) :
    SignType.sign y = SignType.sign x ↔ 0 < x * y := by
  rcases lt_or_gt_of_ne hx with h | h <;> rcases lt_trichotomy y 0 with h' | h' | h'
  · simp [sign_neg h, sign_neg h', mul_pos_of_neg_of_neg h h']
  · simp [sign_neg h, h']
  · simp only [sign_neg h, sign_pos h']
    constructor
    · intro e; exact absurd e (by decide)
    · intro e; nlinarith
  · simp only [sign_pos h, sign_neg h']
    constructor
    · intro e; exact absurd e (by decide)
    · intro e; nlinarith
  · simp [sign_pos h, h']
  · simp [sign_pos h, sign_pos h', mul_pos h h']

/-- AKMM, p. 264, step 2: one bisection step on the bracket `(a, b)`, with midpoint
`c = (a + b)/2`; `a` moves to `c` when `f a` and `f c` have the same (nonzero) sign, otherwise
`b` moves to `c`. -/
noncomputable def bisectStep (f : ℝ → ℝ) (ab : ℝ × ℝ) : ℝ × ℝ :=
  if 0 < f ab.1 * f ((ab.1 + ab.2) / 2) then ((ab.1 + ab.2) / 2, ab.2)
  else (ab.1, (ab.1 + ab.2) / 2)

/-- AKMM, p. 264, step 3: the bracket after `k` bisection steps from `(a, b)`. -/
noncomputable def bisect (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | k + 1 => bisectStep f (bisect f a b k)

/-- The step either keeps `b` and moves `a` to the midpoint or keeps `a` and moves `b`. -/
theorem bisectStep_cases (f : ℝ → ℝ) (ab : ℝ × ℝ) :
    (bisectStep f ab = ((ab.1 + ab.2) / 2, ab.2) ∧ 0 < f ab.1 * f ((ab.1 + ab.2) / 2)) ∨
      (bisectStep f ab = (ab.1, (ab.1 + ab.2) / 2) ∧ ¬ 0 < f ab.1 * f ((ab.1 + ab.2) / 2)) := by
  unfold bisectStep
  split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, h⟩

/-- AKMM, p. 264: "each iteration cuts the interval in half": `b_k − a_k = (b − a)/2ᵏ`. -/
theorem bisect_length (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) :
    (bisect f a b k).2 - (bisect f a b k).1 = (b - a) / 2 ^ k := by
  induction k with
  | zero => simp [bisect]
  | succ k ih =>
    simp only [bisect]
    rcases bisectStep_cases f (bisect f a b k) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
      · simp only [pow_succ]
        rw [div_mul_eq_div_div, ← ih]
        ring

/-- The left endpoint never decreases and the right endpoint never increases. -/
theorem bisect_mono (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    (bisect f a b k).1 ≤ (bisect f a b (k + 1)).1 ∧
      (bisect f a b (k + 1)).2 ≤ (bisect f a b k).2 := by
  have hl := bisect_length f a b k
  have hpos : 0 ≤ (b - a) / 2 ^ k := div_nonneg (by linarith) (by positivity)
  simp only [bisect]
  rcases bisectStep_cases f (bisect f a b k) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    constructor <;> dsimp only <;> linarith

/-- AKMM, p. 264: bisection keeps the bracket: if `f a · f b ≤ 0` then `f a_k · f b_k ≤ 0`. -/
theorem bisect_bracket (f : ℝ → ℝ) {a b : ℝ} (hfab : f a * f b ≤ 0) (k : ℕ) :
    f (bisect f a b k).1 * f (bisect f a b k).2 ≤ 0 := by
  induction k with
  | zero => simpa [bisect] using hfab
  | succ k ih =>
    simp only [bisect]
    set p := bisect f a b k
    rcases bisectStep_cases f p with ⟨h, hpos⟩ | ⟨h, hneg⟩ <;> rw [h]
    · dsimp only
      by_contra hc
      rw [not_le] at hc
      have h1 : 0 < (f p.1 * f ((p.1 + p.2) / 2)) * (f ((p.1 + p.2) / 2) * f p.2) :=
        mul_pos hpos hc
      have h2 : (f p.1 * f ((p.1 + p.2) / 2)) * (f ((p.1 + p.2) / 2) * f p.2) =
          (f p.1 * f p.2) * (f ((p.1 + p.2) / 2)) ^ 2 := by ring
      rw [h2] at h1
      nlinarith [sq_nonneg (f ((p.1 + p.2) / 2))]
    · dsimp only
      exact not_lt.mp hneg

/-- The bracket stays inside `[a, b]` and ordered. -/
theorem bisect_mem (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    a ≤ (bisect f a b k).1 ∧ (bisect f a b k).1 ≤ (bisect f a b k).2 ∧
      (bisect f a b k).2 ≤ b := by
  induction k with
  | zero => simp [bisect, hab]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := bisect_mono f hab k
    have hl := bisect_length f a b (k + 1)
    have hpos : 0 ≤ (b - a) / 2 ^ (k + 1) := div_nonneg (by linarith) (by positivity)
    refine ⟨ih.1.trans h1, by linarith, h2.trans ih.2.2⟩

/-- AKMM, p. 264, step 1 (bracketing): "if `f` is continuous, this condition implies that at
least one solution to `f(x) = 0` exists in the bracket `[a, b]`". -/
theorem bisect_bracket_root {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hfab : f a * f b ≤ 0) :
    ∃ x ∈ Set.Icc a b, f x = 0 := by
  rcases lt_trichotomy (f a) 0 with ha | ha | ha
  · have hb : 0 ≤ f b := by nlinarith
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hf ⟨ha.le, hb⟩
    exact ⟨x, hx, hfx⟩
  · exact ⟨a, ⟨le_rfl, hab⟩, ha⟩
  · have hb : f b ≤ 0 := by nlinarith
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab hf ⟨hb, ha.le⟩
    exact ⟨x, hx, hfx⟩

/-- AKMM, pp. 264–265: for continuous `f` with `f a · f b ≤ 0`, both endpoints of the bisection
bracket converge to a root `x ∈ [a, b]`, with `|a_k − x| ≤ (b − a)/2ᵏ`, and `f(a_k) → 0`
("check that `f(a)` is close to zero, and use `a` as the solution"). -/
theorem bisect_converges {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hfab : f a * f b ≤ 0) :
    ∃ x ∈ Set.Icc a b, f x = 0 ∧
      Tendsto (fun k => (bisect f a b k).1) atTop (𝓝 x) ∧
      Tendsto (fun k => (bisect f a b k).2) atTop (𝓝 x) ∧
      (∀ k, |(bisect f a b k).1 - x| ≤ (b - a) / 2 ^ k) ∧
      Tendsto (fun k => f (bisect f a b k).1) atTop (𝓝 0) := by
  set A : ℕ → ℝ := fun k => (bisect f a b k).1
  set B : ℕ → ℝ := fun k => (bisect f a b k).2
  have hAmono : Monotone A := monotone_nat_of_le_succ fun k => (bisect_mono f hab k).1
  have hBanti : Antitone B := antitone_nat_of_succ_le fun k => (bisect_mono f hab k).2
  have hAb : ∀ k, A k ≤ b := fun k => ((bisect_mem f hab k).2.1).trans (bisect_mem f hab k).2.2
  have hbdd : BddAbove (Set.range A) := ⟨b, by rintro _ ⟨k, rfl⟩; exact hAb k⟩
  set x := ⨆ k, A k
  have hA : Tendsto A atTop (𝓝 x) := tendsto_atTop_ciSup hAmono hbdd
  have hlen : Tendsto (fun k : ℕ => (b - a) / 2 ^ k) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (b - a)
    simpa [div_eq_mul_inv, one_div, inv_pow] using h
  have hBeq : B = fun k => A k + (b - a) / 2 ^ k := by
    funext k
    have := bisect_length f a b k
    simp only [A, B]
    linarith
  have hB : Tendsto B atTop (𝓝 x) := by
    rw [hBeq]
    simpa using hA.add hlen
  have hAx : ∀ k, A k ≤ x := fun k => le_ciSup hbdd k
  have hxB : ∀ k, x ≤ B k := fun k =>
    le_of_tendsto hB (eventually_atTop.2 ⟨k, fun _ hj => hBanti hj⟩)
  have hxmem : x ∈ Set.Icc a b :=
    ⟨(bisect_mem f hab 0).1.trans (hAx 0), (hxB 0).trans (bisect_mem f hab 0).2.2⟩
  have hAmem : ∀ k, A k ∈ Set.Icc a b := fun k =>
    ⟨(bisect_mem f hab k).1, hAb k⟩
  have hBmem : ∀ k, B k ∈ Set.Icc a b := fun k =>
    ⟨(bisect_mem f hab k).1.trans (bisect_mem f hab k).2.1, (bisect_mem f hab k).2.2⟩
  have hfA : Tendsto (fun k => f (A k)) atTop (𝓝 (f x)) :=
    (hf x hxmem).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hA, Eventually.of_forall hAmem⟩)
  have hfB : Tendsto (fun k => f (B k)) atTop (𝓝 (f x)) :=
    (hf x hxmem).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hB, Eventually.of_forall hBmem⟩)
  have hprod : f x * f x ≤ 0 :=
    le_of_tendsto (hfA.mul hfB) (Eventually.of_forall fun k => bisect_bracket f hfab k)
  have hfx : f x = 0 := by nlinarith [mul_self_nonneg (f x)]
  refine ⟨x, hxmem, hfx, hA, hB, fun k => ?_, hfx ▸ hfA⟩
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hAx k))]
  have := bisect_length f a b k
  have := hxB k
  simp only [A, B] at *
  linarith

/-- AKMM, p. 265: "we know how many iterations it requires to shrink the starting interval down
the tolerance level": after any `k > log₂((b − a)/ε)` steps the bracket is shorter than `ε`. -/
theorem bisect_iteration_count (f : ℝ → ℝ) {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) {k : ℕ}
    (hk : Real.logb 2 ((b - a) / ε) < k) :
    (bisect f a b k).2 - (bisect f a b k).1 < ε := by
  rw [bisect_length]
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (div_pos (by linarith) hε),
    Real.rpow_natCast] at hk
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hk
  linarith

/-- AKMM, p. 265: "it always ends after a finite number of steps": for every tolerance `ε > 0`
some number of steps brings the bracket below `ε`. -/
theorem bisect_terminates (f : ℝ → ℝ) {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∃ k : ℕ, (bisect f a b k).2 - (bisect f a b k).1 < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.logb 2 ((b - a) / ε))
  exact ⟨k, bisect_iteration_count f hab hε hk⟩

/-- AKMM, p. 265: on `[0, 1]` with accuracy `10⁻³`, "only 10 evaluations in the case of
bisection (because `(1/2)¹⁰ = 1/1024`)": ten steps suffice and nine do not. -/
theorem bisect_ten_steps (f : ℝ → ℝ) :
    (bisect f 0 1 10).2 - (bisect f 0 1 10).1 < 1 / 1000 ∧
      ¬ (bisect f 0 1 9).2 - (bisect f 0 1 9).1 < 1 / 1000 := by
  rw [bisect_length, bisect_length]
  norm_num

/-- The step function of the counterexample: `−1` left of `1/2`, `1` from `1/2` on. -/
noncomputable def bisectJump (x : ℝ) : ℝ := if x < 1 / 2 then -1 else 1

/-- AKMM, p. 265: "the procedure always ends, even when no solutions exist, for example, because
`f(x)` is not continuous": the jump function brackets on `[0, 1]`, has no zero, and the
bisection bracket still shrinks to length `2⁻ᵏ`. -/
theorem bisect_discontinuous_no_root :
    bisectJump 0 * bisectJump 1 < 0 ∧ (∀ x, bisectJump x ≠ 0) ∧
      ∀ k : ℕ, (bisect bisectJump 0 1 k).2 - (bisect bisectJump 0 1 k).1 = 1 / 2 ^ k := by
  refine ⟨by norm_num [bisectJump], fun x => ?_, fun k => by rw [bisect_length]; ring⟩
  unfold bisectJump
  split_ifs <;> norm_num

end AKMM.ComputationalTools

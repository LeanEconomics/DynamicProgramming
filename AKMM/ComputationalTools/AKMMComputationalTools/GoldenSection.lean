/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Golden-section search

AKMM, §10.3.1, pp. 266–267, and §10.3.3, p. 269. A bracket `a < b < c` with `F(a) ≤ F(b)` and
`F(c) ≤ F(b)` contains an interior maximiser of a continuous `F` on `[a, c]`, a local maximum
(`golden_bracket_max`). The step puts `x` in the longer segment at relative distance
`ω* = (3 − √5)/2` from `b` and keeps `(a, x, b)` if `F(x) > F(b)`, else `(x, b, c)` (and the
mirror image when the right segment is longer) (`goldenStep`). Proved:

* `ω*` satisfies `ω*² − 3ω* + 1 = 0`, `ω* = (1 − ω*)²`, `0.38196 < ω* < 0.38197`, and
  `(1 − ω*)/ω*` is the golden ratio `(1 + √5)/2 ≈ 1.61803` (`golden_omega_sq`,
  `golden_omega_bounds`, `golden_ratio_eq`);
* starting from `(c − b)/(c − a) = ω*`, every step keeps the ratio `ω*` (self-similarity),
  keeps the bracket property, and multiplies the bracket length by `1 − ω*`
  (`goldenStep_spec`); after `n` steps the length is `(1 − ω*)ⁿ(c − a)` (`golden_length`,
  correcting the printed `(1 − ω*)ⁿ(c − b)`: `golden_printed_length_counterexample`), so the
  search ends after a pre-set number of steps (`golden_terminates`) and every bracket contains
  a local maximiser (`golden_iterate_max`);
* footnote 3: `ω*` is the only `ω ∈ (0, 1)` for which both outcomes of the step leave brackets
  of the same length (`golden_fn3_unique`);
* §10.3.3: each step removes the fraction `ω* ≈ 0.38` of the bracket, less than bisection's
  one half (`golden_removed_fraction`).
-/

namespace AKMM.ComputationalTools

open Filter Topology

/-- AKMM, p. 267: the constant `ω* = (3 − √5)/2`. -/
noncomputable def omegaStar : ℝ := (3 - √5) / 2

/-- `ω*` is a root of `ω² − 3ω + 1`. -/
theorem golden_omega_sq : omegaStar ^ 2 = 3 * omegaStar - 1 := by
  unfold omegaStar
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- `ω* = (1 − ω*)²`. -/
theorem golden_omega_eq_sq : omegaStar = (1 - omegaStar) ^ 2 := by
  have := golden_omega_sq
  nlinarith

/-- AKMM, p. 267: `ω* ≈ 0.38197`: `0.38196 < ω* < 0.38197`; in particular `0 < ω* < 1/2`. -/
theorem golden_omega_bounds : 0.38196 < omegaStar ∧ omegaStar < 0.38197 := by
  unfold omegaStar
  have h1 : (2.23606 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √5 < (2.23608 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith

theorem golden_omega_pos : 0 < omegaStar := by linarith [golden_omega_bounds.1]

theorem golden_omega_lt_half : omegaStar < 1 / 2 := by linarith [golden_omega_bounds.2]

/-- AKMM, p. 267: "the ratio `(1 − ω*)/ω* ≈ 1.61803` is often called the golden ratio": it is
`(1 + √5)/2`. -/
theorem golden_ratio_eq : (1 - omegaStar) / omegaStar = Real.goldenRatio := by
  have hpos := golden_omega_pos
  rw [div_eq_iff hpos.ne']
  unfold omegaStar Real.goldenRatio
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- A bracket `(a, b, c)` for golden-section search. -/
structure GoldenBracket where
  /-- the left end `a` -/
  a : ℝ
  /-- the middle point `b` -/
  b : ℝ
  /-- the right end `c` -/
  c : ℝ

/-- AKMM, p. 266, step 1: the bracket property `a < b < c`, `F(a) ≤ F(b)`, `F(c) ≤ F(b)`
(weak inequalities, so that it is kept by step 2 when `F(x) = F(b)`). -/
def GoldenBracket.IsBracket (F : ℝ → ℝ) (p : GoldenBracket) : Prop :=
  p.a < p.b ∧ p.b < p.c ∧ F p.a ≤ F p.b ∧ F p.c ≤ F p.b

/-- AKMM, p. 267: the bracket is in golden proportion: its shorter segment is the fraction
`ω*` of its length. -/
def GoldenBracket.IsGolden (p : GoldenBracket) : Prop :=
  p.c - p.b = omegaStar * (p.c - p.a) ∨ p.b - p.a = omegaStar * (p.c - p.a)

/-- AKMM, p. 267, step 2: one golden-section step. If `[a, b]` is the longer segment, take
`x = b − ω*(b − a)` and keep `(a, x, b)` if `F(x) > F(b)`, otherwise `(x, b, c)`; if `[b, c]` is
the longer one, take `x = b + ω*(c − b)` and keep `(b, x, c)` if `F(x) > F(b)`, else
`(a, b, x)`. -/
noncomputable def goldenStep (F : ℝ → ℝ) (p : GoldenBracket) : GoldenBracket :=
  if p.c - p.b < p.b - p.a then
    if F p.b < F (p.b - omegaStar * (p.b - p.a)) then ⟨p.a, p.b - omegaStar * (p.b - p.a), p.b⟩
    else ⟨p.b - omegaStar * (p.b - p.a), p.b, p.c⟩
  else
    if F p.b < F (p.b + omegaStar * (p.c - p.b)) then ⟨p.b, p.b + omegaStar * (p.c - p.b), p.c⟩
    else ⟨p.a, p.b, p.b + omegaStar * (p.c - p.b)⟩

/-- AKMM, p. 267: one step from a golden bracket gives a golden bracket inside the old one, of
length `(1 − ω*)(c − a)`, still with the bracket property ("every time, we can remove the `ω*`
fraction of the segment"). -/
theorem goldenStep_spec (F : ℝ → ℝ) {p : GoldenBracket} (hb : p.IsBracket F)
    (hg : p.IsGolden) :
    (goldenStep F p).IsBracket F ∧ (goldenStep F p).IsGolden ∧
      (goldenStep F p).c - (goldenStep F p).a = (1 - omegaStar) * (p.c - p.a) ∧
      p.a ≤ (goldenStep F p).a ∧ (goldenStep F p).c ≤ p.c := by
  obtain ⟨hab, hbc, hFa, hFc⟩ := hb
  have hω := golden_omega_sq
  have hω0 := golden_omega_pos
  have hω1 := golden_omega_lt_half
  unfold GoldenBracket.IsGolden at hg ⊢
  unfold goldenStep
  generalize omegaStar = ω at *
  obtain ⟨L, hL⟩ : ∃ L, L = p.c - p.a := ⟨_, rfl⟩
  rw [← hL] at hg ⊢
  have hLpos : 0 < L := by linarith
  have hc' : p.c = p.a + L := by linarith
  rcases hg with hg | hg
  · -- the right segment is the short one: `[a, b]` is longer
    have hb' : p.b = p.a + (1 - ω) * L := by linarith
    have hlong : p.c - p.b < p.b - p.a := by rw [hb', hc']; nlinarith
    simp only [hlong, ↓reduceIte]
    split_ifs with hx
    · refine ⟨⟨?_, ?_, ?_, hx.le⟩, Or.inl ?_, ?_, le_rfl, ?_⟩ <;> dsimp only
      · rw [hb']; nlinarith
      · rw [hb']; nlinarith
      · linarith
      · ring
      · rw [hb']; ring
      · linarith
    · rw [not_lt] at hx
      refine ⟨⟨?_, ?_, hx, hFc⟩, Or.inr ?_, ?_, ?_, le_rfl⟩ <;> dsimp only
      · rw [hb']; nlinarith
      · linarith
      · rw [hb', hc']; linear_combination (ω * L) * hω
      · rw [hb', hc']; linear_combination (-L) * hω
      · rw [hb']; nlinarith
  · -- the left segment is the short one: `[b, c]` is longer (or equal)
    have hb' : p.b = p.a + ω * L := by linarith
    have hlong : ¬ p.c - p.b < p.b - p.a := by
      rw [not_lt, hb', hc']; nlinarith
    simp only [hlong, ↓reduceIte]
    split_ifs with hx
    · refine ⟨⟨?_, ?_, ?_, ?_⟩, Or.inr ?_, ?_, ?_, le_rfl⟩ <;> dsimp only
      · rw [hb', hc']; nlinarith
      · rw [hb', hc']; nlinarith
      · exact hx.le
      · linarith
      · ring
      · rw [hb', hc']; ring
      · linarith
    · rw [not_lt] at hx
      refine ⟨⟨?_, ?_, hFa, hx⟩, Or.inl ?_, ?_, le_rfl, ?_⟩ <;> dsimp only
      · linarith
      · rw [hb', hc']; nlinarith
      · rw [hb', hc']; linear_combination (ω * L) * hω
      · rw [hb', hc']; linear_combination (-L) * hω
      · rw [hb', hc']; nlinarith

/-- AKMM, p. 267, step 3: after `n` golden-section steps from a golden bracket, the bracket
is golden, has the bracket property, lies inside the original one and has length
`(1 − ω*)ⁿ(c − a)`. -/
theorem golden_length (F : ℝ → ℝ) {p : GoldenBracket} (hb : p.IsBracket F) (hg : p.IsGolden)
    (n : ℕ) :
    ((goldenStep F)^[n] p).IsBracket F ∧ ((goldenStep F)^[n] p).IsGolden ∧
      ((goldenStep F)^[n] p).c - ((goldenStep F)^[n] p).a = (1 - omegaStar) ^ n * (p.c - p.a) ∧
      p.a ≤ ((goldenStep F)^[n] p).a ∧ ((goldenStep F)^[n] p).c ≤ p.c := by
  induction n with
  | zero => exact ⟨hb, hg, by simp, le_rfl, le_rfl⟩
  | succ n ih =>
    obtain ⟨hb', hg', hl, ha, hc⟩ := ih
    obtain ⟨hb'', hg'', hl', ha', hc'⟩ := goldenStep_spec F hb' hg'
    rw [Function.iterate_succ_apply']
    refine ⟨hb'', hg'', by rw [hl', hl]; ring, ha.trans ha', hc'.trans hc⟩

/-- AKMM, p. 267: printed "the length of the remaining bracket … is `(1 − ω*)ⁿ(c − b)`". From
`(c − b)/(c − a) = ω*` the length after `n` steps is `(1 − ω*)ⁿ(c − a)` (`golden_length`), which
is strictly larger than the printed value for every `n`. -/
theorem golden_printed_length_counterexample {a b c : ℝ} (hac : a < c)
    (hg : c - b = omegaStar * (c - a)) (n : ℕ) :
    (1 - omegaStar) ^ n * (c - b) < (1 - omegaStar) ^ n * (c - a) := by
  have h1 := golden_omega_lt_half
  have hpos : 0 < (1 - omegaStar) ^ n := pow_pos (by linarith) n
  rw [hg]
  apply mul_lt_mul_of_pos_left _ hpos
  have h2 : 0 < c - a := by linarith
  nlinarith

/-- AKMM, p. 267: golden-section search "ends in a pre-set number of iterations": for every
tolerance `ε > 0` there is `n` with `(1 − ω*)ⁿ(c − a) < ε`. -/
theorem golden_terminates {a c ε : ℝ} (hac : a < c) (hε : 0 < ε) :
    ∃ n : ℕ, (1 - omegaStar) ^ n * (c - a) < ε := by
  have h0 := golden_omega_pos
  have h1 := golden_omega_lt_half
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : 0 < c - a))
    (by linarith : 1 - omegaStar < 1)
  refine ⟨n, ?_⟩
  rwa [lt_div_iff₀ (by linarith)] at hn

/-- AKMM, p. 266, step 1: "These properties mean that a (local) maximum point exists between `a`
and `c`": for continuous `F` on `[a, c]` with the bracket property, some `x ∈ (a, c)`
maximises `F` on `[a, c]`, and it is a local maximum of `F`. -/
theorem golden_bracket_max {F : ℝ → ℝ} {p : GoldenBracket} (hb : p.IsBracket F)
    (hF : ContinuousOn F (Set.Icc p.a p.c)) :
    ∃ x ∈ Set.Ioo p.a p.c, IsMaxOn F (Set.Icc p.a p.c) x ∧ IsLocalMax F x := by
  obtain ⟨hab, hbc, hFa, hFc⟩ := hb
  obtain ⟨x, hx, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨p.a, Set.left_mem_Icc.2 (hab.trans hbc).le⟩ hF
  have key : ∃ y ∈ Set.Ioo p.a p.c, IsMaxOn F (Set.Icc p.a p.c) y := by
    by_cases hxi : x ∈ Set.Ioo p.a p.c
    · exact ⟨x, hxi, hmax⟩
    · have hxe : x = p.a ∨ x = p.c := by
        rcases hx with ⟨h1, h2⟩
        rcases eq_or_lt_of_le h1 with h | h
        · exact Or.inl h.symm
        rcases eq_or_lt_of_le h2 with h' | h'
        · exact Or.inr h'
        · exact absurd ⟨h, h'⟩ hxi
      have hFx : F x ≤ F p.b := by rcases hxe with rfl | rfl <;> assumption
      exact ⟨p.b, ⟨hab, hbc⟩, fun y hy => (hmax hy).trans hFx⟩
  obtain ⟨y, hy, hymax⟩ := key
  exact ⟨y, hy, hymax, hymax.isLocalMax (Icc_mem_nhds hy.1 hy.2)⟩

/-- AKMM, pp. 266–267: every bracket produced by golden-section search for a continuous `F`
contains a local maximiser of `F`, within `(1 − ω*)ⁿ(c − a)` of every point of the bracket. -/
theorem golden_iterate_max {F : ℝ → ℝ} {p : GoldenBracket} (hb : p.IsBracket F)
    (hg : p.IsGolden) (hF : ContinuousOn F (Set.Icc p.a p.c)) (n : ℕ) :
    ∃ x ∈ Set.Ioo ((goldenStep F)^[n] p).a ((goldenStep F)^[n] p).c, IsLocalMax F x ∧
      ∀ y ∈ Set.Icc ((goldenStep F)^[n] p).a ((goldenStep F)^[n] p).c,
        |y - x| ≤ (1 - omegaStar) ^ n * (p.c - p.a) := by
  obtain ⟨hbn, -, hl, ha, hc⟩ := golden_length F hb hg n
  obtain ⟨x, hx, -, hloc⟩ :=
    golden_bracket_max hbn (hF.mono (Set.Icc_subset_Icc ha hc))
  refine ⟨x, hx, hloc, fun y hy => ?_⟩
  rw [← hl, abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- AKMM, p. 267, the two possible new brackets: if `c − b = ω(c − a)` and
`x = b − ω(b − a)`, the bracket `(a, x, b)` has length `(1 − ω)(c − a)` and the bracket
`(x, b, c)` has length `ω(2 − ω)(c − a)`. -/
theorem golden_two_lengths {a b c ω : ℝ} (hg : c - b = ω * (c - a)) :
    b - a = (1 - ω) * (c - a) ∧ c - (b - ω * (b - a)) = ω * (2 - ω) * (c - a) := by
  have hb : b = c - ω * (c - a) := by linarith
  subst hb
  constructor <;> ring

/-- AKMM, p. 267, fn. 3: "this result is guaranteed only with this particular value of `ω*`":
for `ω ∈ (0, 1)` the two possible new brackets have the same length (`golden_two_lengths`)
exactly when `ω = ω*`. -/
theorem golden_fn3_unique {ω : ℝ} (h0 : 0 < ω) (h1 : ω < 1) :
    1 - ω = ω * (2 - ω) ↔ ω = omegaStar := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : 2 < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  constructor
  · intro h
    have hq : (ω - (3 - √5) / 2) * (ω - (3 + √5) / 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 hq with hq | hq
    · unfold omegaStar; linarith
    · nlinarith
  · rintro rfl
    have := golden_omega_sq
    nlinarith

/-- AKMM, §10.3.3, p. 269: golden-section search "gets rid of about one-third of the interval in
each iteration, as opposed to half": each step removes the fraction `ω* ≈ 0.382` of the
bracket, which lies between one third and one half. -/
theorem golden_removed_fraction :
    1 - (1 - omegaStar) = omegaStar ∧ 1 / 3 < omegaStar ∧ omegaStar < 1 / 2 := by
  refine ⟨by ring, ?_, golden_omega_lt_half⟩
  linarith [golden_omega_bounds.1]

end AKMM.ComputationalTools

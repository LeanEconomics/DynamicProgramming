/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LawsOfLargeNumbers.ModesOfConvergence

/-!
# Exercise 14.1: convergence in probability without a.e. convergence

SLP p. 420. On `[0, 1)` with Lebesgue measure, list the indicators `f_{ni}` of `[(i−1)/n, i/n)`,
`1 ≤ i ≤ n`, row by row. Rows are indexed here from `0`: the `k`-th function lies in row
`r = row k` (the row whose block `[tri r, tri (r+1))` contains `k`, with `tri r = 0 + 1 + ⋯ + r`) at
position `i = k − tri r ∈ {0, …, r}`, and is the indicator of `[i/(r+1), (i+1)/(r+1))`.

* (a) the sequence converges at no point of `[0, 1)` (`ex_14_1a`);
* (b) it converges to `0` in probability (`ex_14_1b`);
* (c) the diagonal subsequence (the last function of each row, the indicator of
  `[r/(r+1), 1)`) converges to `0` at every point of `[0, 1)`, hence a.e. (`ex_14_1c`).
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The triangular numbers `tri r = 0 + 1 + ⋯ + r`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | r + 1 => tri r + (r + 1)

theorem tri_succ (r : ℕ) : tri (r + 1) = tri r + (r + 1) := rfl

theorem le_tri (r : ℕ) : r ≤ tri r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [tri_succ]; omega

theorem tri_mono : Monotone tri :=
  monotone_nat_of_le_succ fun r => by rw [tri_succ]; omega

theorem exists_row (k : ℕ) : ∃ r, k < tri (r + 1) := ⟨k, by
  have := le_tri (k + 1); omega⟩

/-- The row containing index `k`. -/
def row (k : ℕ) : ℕ := Nat.find (exists_row k)

theorem row_spec (k : ℕ) : tri (row k) ≤ k ∧ k < tri (row k + 1) := by
  refine ⟨?_, Nat.find_spec (exists_row k)⟩
  rcases h : row k with _ | r
  · exact Nat.zero_le _
  · have := Nat.find_min (exists_row k) (show r < row k by omega)
    omega

theorem row_eq {k r : ℕ} (h1 : tri r ≤ k) (h2 : k < tri (r + 1)) : row k = r := by
  obtain ⟨h3, h4⟩ := row_spec k
  rcases lt_trichotomy (row k) r with h | h | h
  · have := tri_mono (show row k + 1 ≤ r by omega); omega
  · exact h
  · have := tri_mono (show r + 1 ≤ row k by omega); omega

/-- The position of index `k` in its row. -/
def pos (k : ℕ) : ℕ := k - tri (row k)

theorem pos_le (k : ℕ) : pos k ≤ row k := by
  have := row_spec k; rw [tri_succ] at this; unfold pos; omega

theorem row_tri_add {r i : ℕ} (hi : i ≤ r) : row (tri r + i) = r ∧ pos (tri r + i) = i := by
  have hr : row (tri r + i) = r := row_eq (by omega) (by rw [tri_succ]; omega)
  exact ⟨hr, by unfold pos; rw [hr]; omega⟩

theorem le_row {k r : ℕ} (hk : tri r ≤ k) : r ≤ row k := by
  by_contra h
  have := tri_mono (show row k + 1 ≤ r by omega)
  have := (row_spec k).2
  omega

/-- The interval `[i/(r+1), (i+1)/(r+1))` of index `k`. -/
def slideSet (k : ℕ) : Set ℝ :=
  Ico ((pos k : ℝ) / (row k + 1)) (((pos k : ℝ) + 1) / (row k + 1))

/-- The `k`-th function of the sequence of Exercise 14.1. -/
noncomputable def sliding (k : ℕ) (ω : ℝ) : ℝ := (slideSet k).indicator 1 ω

/-- Lebesgue measure on `[0, 1)`. -/
noncomputable def unitLeb : Measure ℝ := volume.restrict (Ico 0 1)

theorem sliding_eq_one {k : ℕ} {ω : ℝ} (h : ω ∈ slideSet k) : sliding k ω = 1 := by
  simp [sliding, h]

theorem sliding_eq_zero {k : ℕ} {ω : ℝ} (h : ω ∉ slideSet k) : sliding k ω = 0 := by
  simp [sliding, h]

/-- In every row `r ≥ 1` some function is `1` at `ω` and some is `0`. -/
theorem row_one_zero {ω : ℝ} (hω : ω ∈ Ico (0 : ℝ) 1) {r : ℕ} (hr : 1 ≤ r) :
    (∃ k, tri r ≤ k ∧ sliding k ω = 1) ∧ ∃ k, tri r ≤ k ∧ sliding k ω = 0 := by
  have hr1 : (0 : ℝ) < r + 1 := by positivity
  set i := ⌊ω * (r + 1)⌋₊
  have hx0 : 0 ≤ ω * (r + 1) := mul_nonneg hω.1 hr1.le
  have hxlt : ω * (r + 1) < r + 1 := by nlinarith [hω.2]
  have hil : (i : ℝ) ≤ ω * (r + 1) := Nat.floor_le hx0
  have hiu : ω * (r + 1) < i + 1 := Nat.lt_floor_add_one _
  have hir : i ≤ r := by
    have : (i : ℝ) < r + 1 := lt_of_le_of_lt hil hxlt
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have hmem : ∀ j, j ≤ r → (ω ∈ slideSet (tri r + j) ↔ j = i) := fun j hj => by
    obtain ⟨h1, h2⟩ := row_tri_add hj
    simp only [slideSet, h1, h2, mem_Ico, div_le_iff₀ hr1, lt_div_iff₀ hr1]
    constructor
    · rintro ⟨ha, hb⟩
      have e1 : j ≤ i := Nat.le_floor (by linarith)
      have e2 : i < j + 1 := by
        have : (i : ℝ) < j + 1 := lt_of_le_of_lt hil (by linarith)
        exact_mod_cast this
      omega
    · rintro rfl; constructor <;> linarith
  refine ⟨⟨tri r + i, by omega, sliding_eq_one ((hmem i hir).2 rfl)⟩, ?_⟩
  set j := if i = 0 then 1 else 0
  have hj : j ≤ r := by simp only [j]; split_ifs <;> omega
  have hji : j ≠ i := by simp only [j]; split_ifs <;> omega
  exact ⟨tri r + j, by omega, sliding_eq_zero fun h => hji ((hmem j hj).1 h)⟩

/-- **Exercise 14.1a.** The sequence converges at no point of `[0, 1)`. -/
theorem ex_14_1a {ω : ℝ} (hω : ω ∈ Ico (0 : ℝ) 1) :
    ¬ ∃ L, Tendsto (fun k => sliding k ω) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hL) (1 / 2) (by norm_num))
  obtain ⟨⟨k₁, hk₁, h1⟩, ⟨k₀, hk₀, h0⟩⟩ := row_one_zero hω (le_max_right K 1)
  have e1 := hK k₁ ((le_max_left K 1).trans ((le_tri _).trans hk₁))
  have e0 := hK k₀ ((le_max_left K 1).trans ((le_tri _).trans hk₀))
  rw [h1, Real.dist_eq] at e1
  rw [h0, Real.dist_eq] at e0
  rw [abs_lt] at e1 e0
  linarith [e1.1, e0.2]

/-- **Exercise 14.1b.** The sequence converges to `0` in probability. -/
theorem ex_14_1b : ConvInProb unitLeb sliding fun _ => 0 := by
  intro ε hε
  have hrow : Tendsto row atTop atTop := tendsto_atTop.2 fun r =>
    eventually_atTop.2 ⟨tri r, fun k hk => le_row hk⟩
  have hlen : Tendsto (fun k => ENNReal.ofReal (1 / ((row k : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.comp hrow)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlen
    (fun k => zero_le) fun k => ?_
  have hsub : {ω | ε < |sliding k ω - 0|} ⊆ slideSet k := fun ω hω => by
    by_contra h
    simp only [mem_ofPred_eq, sliding_eq_zero h, sub_zero, abs_zero] at hω
    linarith
  calc unitLeb {ω | ε < |sliding k ω - 0|} ≤ volume (slideSet k) :=
        (Measure.restrict_le_self _).trans (measure_mono hsub)
    _ = ENNReal.ofReal (1 / ((row k : ℝ) + 1)) := by
        rw [slideSet, Real.volume_Ico]
        congr 1
        field_simp
        ring

/-- **Exercise 14.1c.** The diagonal subsequence (the indicator of `[r/(r+1), 1)`, last in row
`r`) converges to `0` at every point of `[0, 1)`, hence a.e. -/
theorem ex_14_1c :
    StrictMono (fun r => tri r + r) ∧
      (∀ ω ∈ Ico (0 : ℝ) 1, Tendsto (fun r => sliding (tri r + r) ω) atTop (𝓝 0)) ∧
      ConvAE unitLeb (fun r => sliding (tri r + r)) fun _ => 0 := by
  have hpt : ∀ ω ∈ Ico (0 : ℝ) 1, Tendsto (fun r => sliding (tri r + r) ω) atTop (𝓝 0) := by
    intro ω hω
    obtain ⟨R, hR⟩ := exists_nat_gt (1 / (1 - ω))
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨R, fun r hr => ?_⟩)
    obtain ⟨h1, h2⟩ := row_tri_add (le_refl r)
    have hr1 : (0 : ℝ) < r + 1 := by positivity
    have h1ω : 0 < 1 - ω := by linarith [hω.2]
    refine (sliding_eq_zero fun h => ?_).symm
    simp only [slideSet, h1, h2, mem_Ico, div_le_iff₀ hr1] at h
    have hR' : (R : ℝ) ≤ r := by exact_mod_cast hr
    rw [div_lt_iff₀ h1ω] at hR
    nlinarith [h.1]
  refine ⟨fun a b hab => ?_, hpt, ?_⟩
  · have := tri_mono hab.le; change tri a + a < tri b + b; omega
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with ω hω
    exact hpt ω hω

end StokeyLucasPrescott.LawsOfLargeNumbers

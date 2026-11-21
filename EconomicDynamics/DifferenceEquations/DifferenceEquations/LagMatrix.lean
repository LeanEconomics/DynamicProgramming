/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DifferenceEquations.LinearSystems

/-!
# The matrix lag-operator formula

Miao, §1.2, pp. 11–12: `(I − ALⁿ)⁻¹ = ∑_{j ≥ 0} AʲLⁿʲ` when all eigenvalues of `A` lie inside
the unit circle, where `LⁿX_t = X_{t−n}` on two-sided sequences `{X_t}_{t ∈ ℤ}`.

The operator identity is made precise on bounded sequences `X : ℤ → (ι → ℝ)`
(`lag_matrix_formula`): the series `Y_t = ∑ⱼ AʲX_{t−nj}` (`lagSeries`) converges for every `t`,
`Y` is bounded, `Y_t − AY_{t−n} = X_t` (that is, `(I − ALⁿ)Y = X`), and `Y` is the only bounded
sequence with this property. So `∑ⱼ AʲLⁿʲ` is the inverse of `I − ALⁿ` on bounded sequences.

The book says "here `n` is any integer". For two-sided sequences this is right: the proof uses
only `t − n(j + 1) = (t − n) − nj`, and works for `n ≤ 0` too (`n = 0` gives
`Y_t = ∑ⱼ AʲX_t = (I − A)⁻¹X_t`, `n < 0` a sum of leads). The geometric decay
`‖Aʲv‖ ≤ K aʲ‖v‖`, `a < 1`, comes from `hasGeomDecay_of_isStableMatrix`.
-/

open Filter Topology

namespace Miao.DifferenceEquations

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑ⱼ AʲLⁿʲX` at date `t`: `∑ⱼ AʲX_{t−nj}`. -/
noncomputable def lagSeries (A : Matrix ι ι ℝ) (n : ℤ) (X : ℤ → ι → ℝ) (t : ℤ) : ι → ℝ :=
  ∑' j : ℕ, (A ^ j) *ᵥ X (t - n * j)

/-- The lag series converges and is bounded by `KC/(1 − a)`. -/
theorem lagSeries_summable (A : Matrix ι ι ℝ) {K a : ℝ} (hA : HasGeomDecay A K a) (n : ℤ)
    {X : ℤ → ι → ℝ} {C : ℝ} (hX : ∀ t, ‖X t‖ ≤ C) (t : ℤ) :
    Summable (fun j : ℕ => (A ^ j) *ᵥ X (t - n * j)) ∧
      ‖lagSeries A n X t‖ ≤ K * C / (1 - a) :=
  summable_geom_series A hA (v := fun j : ℕ => X (t - n * j)) fun _ => hX _

/-- `(I − ALⁿ)Y = X`: `Y_t = X_t + AY_{t−n}`. -/
theorem lagSeries_rec (A : Matrix ι ι ℝ) {K a : ℝ} (hA : HasGeomDecay A K a) (n : ℤ)
    {X : ℤ → ι → ℝ} {C : ℝ} (hX : ∀ t, ‖X t‖ ≤ C) (t : ℤ) :
    lagSeries A n X t = X t + A *ᵥ lagSeries A n X (t - n) := by
  unfold lagSeries
  rw [tsum_geom_series_succ A hA (v := fun j : ℕ => X (t - n * j)) fun _ => hX _]
  simp only [Nat.cast_zero, mul_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  congr 3
  funext j
  congr 2
  ring

/-- Uniqueness: a bounded `Y` with `Y_t = X_t + AY_{t−n}` is the lag series. -/
theorem lagSeries_unique (A : Matrix ι ι ℝ) {K a : ℝ} (hA : HasGeomDecay A K a) (n : ℤ)
    {X Y : ℤ → ι → ℝ} {C D : ℝ} (hX : ∀ t, ‖X t‖ ≤ C) (hY : ∀ t, ‖Y t‖ ≤ D)
    (hrec : ∀ t, Y t = X t + A *ᵥ Y (t - n)) : Y = lagSeries A n X := by
  obtain ⟨ha0, ha1, hK0, hK⟩ := hA
  set E := fun t => Y t - lagSeries A n X t
  have hE : ∀ t, E t = A *ᵥ E (t - n) := fun t => by
    simp only [E, Matrix.mulVec_sub]
    rw [hrec t, lagSeries_rec A ⟨ha0, ha1, hK0, hK⟩ n hX t]
    abel
  have hEk : ∀ (k : ℕ) t, E t = (A ^ k) *ᵥ E (t - n * k) := fun k => by
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [ih t, hE (t - n * k), Matrix.mulVec_mulVec, ← pow_succ]
      congr 2
      push_cast
      ring
  set B := D + K * C / (1 - a)
  have hEB : ∀ t, ‖E t‖ ≤ B := fun t =>
    (norm_sub_le _ _).trans (add_le_add (hY t)
      (lagSeries_summable A ⟨ha0, ha1, hK0, hK⟩ n hX t).2)
  funext t
  rw [← sub_eq_zero]
  have hle : ∀ k : ℕ, ‖E t‖ ≤ K * B * a ^ k := fun k => by
    calc ‖E t‖ = ‖(A ^ k) *ᵥ E (t - n * k)‖ := by rw [← hEk]
      _ ≤ K * a ^ k * ‖E (t - n * k)‖ := hK k _
      _ ≤ K * a ^ k * B := by gcongr; exact hEB _
      _ = K * B * a ^ k := by ring
  have hlim : Tendsto (fun k : ℕ => K * B * a ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul (K * B)
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim hle)

/-- **The matrix lag formula** (Miao, §1.2, pp. 11–12): `(I − ALⁿ)⁻¹ = ∑_{j ≥ 0} AʲLⁿʲ` if all
eigenvalues of `A` are inside the unit circle, for every integer `n`. On bounded sequences
`X`: the series `Y_t = ∑ⱼ AʲX_{t−nj}` converges, `Y` is bounded, `Y − ALⁿY = X`, and every
bounded solution of `Y' − ALⁿY' = X` equals `Y`. -/
theorem lag_matrix_formula (A : Matrix ι ι ℝ) (hA : IsStableMatrix (A.map Complex.ofRealHom))
    (n : ℤ) (X : ℤ → ι → ℝ) (hX : ∃ C, ∀ t, ‖X t‖ ≤ C) :
    (∀ t, Summable (fun j : ℕ => (A ^ j) *ᵥ X (t - n * j))) ∧
      (∃ D, ∀ t, ‖lagSeries A n X t‖ ≤ D) ∧
      (∀ t, lagSeries A n X t - A *ᵥ lagSeries A n X (t - n) = X t) ∧
      ∀ Y : ℤ → ι → ℝ, (∃ D, ∀ t, ‖Y t‖ ≤ D) → (∀ t, Y t - A *ᵥ Y (t - n) = X t) →
        Y = lagSeries A n X := by
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix A hA
  obtain ⟨C, hC⟩ := hX
  refine ⟨fun t => (lagSeries_summable A hKa n hC t).1,
    ⟨_, fun t => (lagSeries_summable A hKa n hC t).2⟩,
    fun t => by rw [lagSeries_rec A hKa n hC t]; abel, fun Y ⟨D, hD⟩ hY => ?_⟩
  exact lagSeries_unique A hKa n hC hD fun t => by rw [← hY t]; abel

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NonlinearValuation.PerronFrobenius

/-!
# The Perron–Frobenius theorem for irreducible matrices

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Theorem 2.3.1
(p. 69), second sentence: if `A ≥ 0` is irreducible, then the right and left
Perron–Frobenius eigenvectors are everywhere positive and unique, and
`ρ(A) > 0`. The `FiniteStates/OperatorsFixedPoints` project proved the
nonnegative case and deferred this part, which Chapter 6 needs through its
corollary Exercise 2.3.2 (iv) (p. 71): an irreducible Markov matrix has a
unique stationary distribution, and it is everywhere positive.

The proofs are elementary once the nonnegative case is available. If `Ae = λe`
with `e ≥ 0` nonzero, pick `y` with `e(y) > 0`; for any `x` some `k ≥ 1` has
`Aᵏ(x, y) > 0`, and `λᵏe(x) = (Aᵏe)(x) ≥ Aᵏ(x, y)e(y) > 0`, so `e ≫ 0` and
`λ > 0`. Uniqueness: a left eigenvector `ε ≫ 0` for `ρ(A)` gives
`λ⟨ε, e'⟩ = ⟨ε, Ae'⟩ = ρ(A)⟨ε, e'⟩` for any nonnegative eigenvector `e'`, so
`λ = ρ(A)`; and if `e, e'` are two such eigenvectors for `ρ(A)`, then
`e' − ce` with `c = min e'/e` is a nonnegative eigenvector with a zero
coordinate, hence zero. These are restated from the `FiniteStates/StochasticDiscounting`
project, where they were first proved.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.NonlinearValuation

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Irreducibility (Vol. 1, p. 69): `A ≥ 0` and every state leads to every other in some
positive number of steps, `∑_{k≥1} Aᵏ ≫ 0`. -/
def Irreducible (A : Matrix X X ℝ) : Prop :=
  (∀ x x', 0 ≤ A x x') ∧ ∀ x x', ∃ k ≥ 1, 0 < (A ^ k) x x'

/-- An everywhere-positive matrix is irreducible (take `k = 1`). -/
theorem irreducible_of_pos {A : Matrix X X ℝ} (hpos : ∀ x x', 0 < A x x') : Irreducible A :=
  ⟨fun x x' => (hpos x x').le, fun x x' => ⟨1, le_rfl, by rw [pow_one]; exact hpos x x'⟩⟩

/-- Irreducibility is preserved by transposition. -/
theorem Irreducible.transpose {A : Matrix X X ℝ} (hA : Irreducible A) : Irreducible Aᵀ :=
  ⟨fun x x' => hA.1 x' x, fun x x' => by
    obtain ⟨k, hk, hpos⟩ := hA.2 x' x
    refine ⟨k, hk, ?_⟩
    rw [← Matrix.transpose_pow, Matrix.transpose_apply]
    exact hpos⟩

/-- `Ae = λe` implies `Aᵏe = λᵏe`. -/
theorem pow_mulVec_eq_of_mulVec_eq {A : Matrix X X ℝ} {e : X → ℝ} {lam : ℝ}
    (he : A *ᵥ e = lam • e) (k : ℕ) : A ^ k *ᵥ e = lam ^ k • e := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, he, smul_smul, ← pow_succ]

/-- For irreducible `A`, a nonnegative nonzero eigenvector is everywhere positive, and its
eigenvalue is positive. -/
theorem Irreducible.pos_of_mulVec_eq_smul {A : Matrix X X ℝ} (hA : Irreducible A) {e : X → ℝ}
    {lam : ℝ} (he0 : ∀ x, 0 ≤ e x) (hene : e ≠ 0) (he : A *ᵥ e = lam • e) :
    (∀ x, 0 < e x) ∧ 0 < lam := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < e y := by
    by_contra h
    exact hene (funext fun x => le_antisymm (not_lt.1 fun hx => h ⟨x, hx⟩) (he0 x))
  -- `λ e(y) = (Ae)(y) ≥ 0` gives `λ ≥ 0`
  have hlam0 : 0 ≤ lam := by
    have h1 : 0 ≤ (A *ᵥ e) y := sum_nonneg fun z _ => mul_nonneg (hA.1 y z) (he0 z)
    rw [he, Pi.smul_apply, smul_eq_mul] at h1
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) hy
    linarith
  -- `λᵏ e(x) = (Aᵏe)(x) ≥ Aᵏ(x, y) e(y) > 0`
  have hpos : ∀ x, 0 < e x := by
    intro x
    obtain ⟨k, -, hkpos⟩ := hA.2 x y
    have h1 : (A ^ k) x y * e y ≤ (A ^ k *ᵥ e) x :=
      single_le_sum (fun z _ => mul_nonneg (pow_nonneg_entries hA.1 k x z) (he0 z)) (mem_univ y)
    rw [pow_mulVec_eq_of_mulVec_eq he, Pi.smul_apply, smul_eq_mul] at h1
    have h2 : 0 < lam ^ k * e x := lt_of_lt_of_le (mul_pos hkpos hy) h1
    rcases (he0 x).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at h2
      exact absurd h2 (lt_irrefl 0)
  refine ⟨hpos, ?_⟩
  rcases hlam0.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk, hkpos⟩ := hA.2 y y
    have h1 : (A ^ k) y y * e y ≤ (A ^ k *ᵥ e) y :=
      single_le_sum (fun z _ => mul_nonneg (pow_nonneg_entries hA.1 k y z) (he0 z)) (mem_univ y)
    rw [pow_mulVec_eq_of_mulVec_eq he, Pi.smul_apply, smul_eq_mul, ← h, zero_pow (by omega),
      zero_mul] at h1
    exact absurd (mul_pos hkpos hy) (not_lt.2 h1)

variable [Nonempty X]

/-- **Theorem 2.3.1, irreducible case** (p. 69): `ρ(A) > 0` for irreducible `A`. -/
theorem Irreducible.specRad_pos {A : Matrix X X ℝ} (hA : Irreducible A) : 0 < specRad A := by
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA.1
  exact (hA.pos_of_mulVec_eq_smul he0 hene he).2

/-- **Theorem 2.3.1, irreducible case** (p. 69): the right Perron–Frobenius eigenvector is
everywhere positive. -/
theorem Irreducible.exists_pos_eigenvector {A : Matrix X X ℝ} (hA : Irreducible A) :
    ∃ e : X → ℝ, (∀ x, 0 < e x) ∧ A *ᵥ e = specRad A • e := by
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA.1
  exact ⟨e, (hA.pos_of_mulVec_eq_smul he0 hene he).1, he⟩

/-- **Theorem 2.3.1, irreducible case** (p. 69): the left Perron–Frobenius eigenvector is
everywhere positive. -/
theorem Irreducible.exists_pos_left_eigenvector {A : Matrix X X ℝ} (hA : Irreducible A) :
    ∃ ε : X → ℝ, (∀ x, 0 < ε x) ∧ ε ᵥ* A = specRad A • ε := by
  obtain ⟨ε, hε, hεA⟩ := hA.transpose.exists_pos_eigenvector
  refine ⟨ε, hε, ?_⟩
  rw [← mulVec_transpose, hεA, specRad_transpose]

/-- For irreducible `A`, the only eigenvalue with a nonnegative nonzero eigenvector is `ρ(A)`:
pair with a positive left eigenvector. -/
theorem Irreducible.eq_specRad_of_mulVec_eq_smul {A : Matrix X X ℝ} (hA : Irreducible A)
    {e' : X → ℝ} {lam : ℝ} (he'0 : ∀ x, 0 ≤ e' x) (hne : e' ≠ 0) (he' : A *ᵥ e' = lam • e') :
    lam = specRad A := by
  obtain ⟨ε, hε, hεA⟩ := hA.exists_pos_left_eigenvector
  have h1 : ε ⬝ᵥ (A *ᵥ e') = (ε ᵥ* A) ⬝ᵥ e' := dotProduct_mulVec ε A e'
  rw [he', hεA, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h1
  have hpos : 0 < ε ⬝ᵥ e' := by
    have he'pos := (hA.pos_of_mulVec_eq_smul he'0 hne he').1
    exact sum_pos (fun x _ => mul_pos (hε x) (he'pos x)) univ_nonempty
  exact mul_right_cancel₀ hpos.ne' h1

/-- **Theorem 2.3.1, irreducible case** (p. 69), uniqueness: a nonnegative nonzero eigenvector
for `ρ(A)` is a positive multiple of any positive one. -/
theorem Irreducible.exists_eq_smul_of_mulVec_eq_smul {A : Matrix X X ℝ} (hA : Irreducible A)
    {e e' : X → ℝ} (he : ∀ x, 0 < e x) (heA : A *ᵥ e = specRad A • e) (he'0 : ∀ x, 0 ≤ e' x)
    (hne : e' ≠ 0) (he'A : A *ᵥ e' = specRad A • e') : ∃ c : ℝ, 0 < c ∧ e' = c • e := by
  obtain ⟨x₀, -, hx₀⟩ := exists_min_image univ (fun x => e' x / e x) univ_nonempty
  set c := e' x₀ / e x₀ with hc
  have he'pos := (hA.pos_of_mulVec_eq_smul he'0 hne he'A).1
  have hcpos : 0 < c := div_pos (he'pos x₀) (he x₀)
  set φ : X → ℝ := e' - c • e with hφ
  have hφ0 : ∀ x, 0 ≤ φ x := by
    intro x
    have := hx₀ x (mem_univ x)
    rw [le_div_iff₀ (he x)] at this
    simp only [hφ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hφA : A *ᵥ φ = specRad A • φ := by
    rw [hφ, mulVec_sub, mulVec_smul, heA, he'A]
    module
  have hφx₀ : φ x₀ = 0 := by
    simp only [hφ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc]
    rw [div_mul_cancel₀ _ (he x₀).ne', sub_self]
  by_cases hφne : φ = 0
  · rw [hφ] at hφne
    exact ⟨c, hcpos, sub_eq_zero.1 hφne⟩
  · exfalso
    have := (hA.pos_of_mulVec_eq_smul hφ0 hφne hφA).1 x₀
    rw [hφx₀] at this
    exact lt_irrefl 0 this

/-- Exercise 2.3.2 (iv), p. 71: an irreducible Markov matrix has exactly one stationary
distribution, and it is everywhere positive. -/
theorem IsMarkov.exists_unique_stationary_of_irreducible {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hirr : Irreducible P) :
    ∃ ψ : X → ℝ, IsDistribution ψ ∧ ψ ᵥ* P = ψ ∧ (∀ x, 0 < ψ x) ∧
      ∀ φ, IsDistribution φ → φ ᵥ* P = φ → φ = ψ := by
  obtain ⟨ψ, hψ0, hψ1, hψP⟩ := hP.exists_stationary
  have hρ : specRad Pᵀ = 1 := by rw [specRad_transpose, hP.specRad_eq_one]
  have hψne : ψ ≠ 0 := by
    intro h
    rw [h] at hψ1
    simp at hψ1
  have hψT : Pᵀ *ᵥ ψ = specRad Pᵀ • ψ := by rw [mulVec_transpose, hψP, hρ, one_smul]
  have hψpos := (hirr.transpose.pos_of_mulVec_eq_smul hψ0 hψne hψT).1
  refine ⟨ψ, ⟨hψ0, hψ1⟩, hψP, hψpos, fun φ hφ hφP => ?_⟩
  have hφne : φ ≠ 0 := by
    intro h
    have := hφ.sum_eq_one
    rw [h] at this
    simp at this
  have hφT : Pᵀ *ᵥ φ = specRad Pᵀ • φ := by rw [mulVec_transpose, hφP, hρ, one_smul]
  obtain ⟨c, -, hφc⟩ :=
    hirr.transpose.exists_eq_smul_of_mulVec_eq_smul hψpos hψT hφ.nonneg hφne hφT
  have hsum : ∑ x, φ x = c * ∑ x, ψ x := by
    rw [hφc]
    simp [mul_sum]
  rw [hφ.sum_eq_one, hψ1, mul_one] at hsum
  rw [hφc, ← hsum, one_smul]

end SargentStachurski.NonlinearValuation

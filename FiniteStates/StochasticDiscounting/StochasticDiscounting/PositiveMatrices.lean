/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDiscounting.Irreducible
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max

/-!
# Everywhere-positive matrices: Dobrushin's estimate and the convergence (2.11)

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Theorem 2.3.1
(p. 69), last sentence: if `A ≫ 0` then, with the Perron–Frobenius vectors
normalised so that `⟨ε, e⟩ = 1`, `ρ(A)^{−t} Aᵗ → e εᵀ`. This completes the
theorem, whose nonnegative and irreducible parts are in `PerronFrobenius` and
`Irreducible`.

The proof conjugates to a Markov matrix. With `e ≫ 0` the right eigenvector,
`P(x, x') = A(x, x')e(x')/(ρ(A)e(x))` is a Markov matrix with positive entries
and `Pᵗ(x, x') = ρ(A)^{−t}Aᵗ(x, x')e(x')/e(x)`. Dobrushin's ℓ¹ estimate,
restated from the `FiniteStates/MarkovDynamics` project (Exercise 3.1.7): if
every entry of a Markov matrix `P` is at least `η > 0`, then `ψPᵗ → ψ*` for
every distribution `ψ`, where `ψ*` is the unique stationary distribution. Taking
`ψ = δₓ` gives `Pᵗ(x, ·) → ψ*`, so `ρ(A)^{−t}Aᵗ(x, x') → e(x)ψ*(x')/e(x')`, and
`ε := ψ*/e` is the left eigenvector with `⟨ε, e⟩ = ∑ψ* = 1`.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.StochasticDiscounting

variable {X : Type*} [Fintype X]

/-- `(ψP)(x') = ∑ ψ(x)P(x, x')`. -/
theorem vecMul_apply_eq (P : Matrix X X ℝ) (ψ : X → ℝ) (x' : X) :
    (ψ ᵥ* P) x' = ∑ x, ψ x * P x x' := rfl

/-- `ψ ↦ ψP` maps distributions to distributions. -/
theorem IsMarkov.isDistribution_vecMul {P : Matrix X X ℝ} (hP : IsMarkov P) {ψ : X → ℝ}
    (hψ : IsDistribution ψ) : IsDistribution (ψ ᵥ* P) where
  nonneg x' := sum_nonneg fun x _ => mul_nonneg (hψ.nonneg x) (hP.nonneg x x')
  sum_eq_one := by
    simp only [vecMul_apply_eq]
    rw [sum_comm]
    simp only [← mul_sum, hP.rowsum, mul_one, hψ.sum_eq_one]

/-- `ψ ↦ ψP` preserves total mass. -/
theorem IsMarkov.sum_vecMul {P : Matrix X X ℝ} (hP : IsMarkov P) (d : X → ℝ) :
    ∑ x', (d ᵥ* P) x' = ∑ x, d x := by
  simp only [vecMul_apply_eq]
  rw [sum_comm]
  simp only [← mul_sum, hP.rowsum, mul_one]

/-- The ℓ¹ norm `‖d‖₁ = ∑ |d(x)|` on `ℝ^X`. -/
def l1 (d : X → ℝ) : ℝ := ∑ x, |d x|

theorem l1_nonneg (d : X → ℝ) : 0 ≤ l1 d := sum_nonneg fun _ _ => abs_nonneg _

/-- The supremum norm is bounded by the ℓ¹ norm. -/
theorem norm_le_l1 (d : X → ℝ) : ‖d‖ ≤ l1 d := by
  rw [pi_norm_le_iff_of_nonneg (l1_nonneg d)]
  intro x
  rw [Real.norm_eq_abs]
  exact single_le_sum (fun y _ => abs_nonneg (d y)) (mem_univ x)

/-- Dobrushin's estimate: if every entry of the Markov matrix `P` is at least `η`, then for `d`
with `∑ d = 0`, `‖dP‖₁ ≤ (1 − nη)‖d‖₁`, where `n = |X|`. -/
theorem l1_vecMul_le {P : Matrix X X ℝ} (hP : IsMarkov P) {η : ℝ} (hη : ∀ x x', η ≤ P x x')
    {d : X → ℝ} (hd : ∑ x, d x = 0) :
    l1 (d ᵥ* P) ≤ (1 - Fintype.card X * η) * l1 d := by
  have hkey : ∀ x', (d ᵥ* P) x' = ∑ x, d x * (P x x' - η) := by
    intro x'
    rw [vecMul_apply_eq]
    have : ∑ x, d x * (P x x' - η) = ∑ x, d x * P x x' - (∑ x, d x) * η := by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [this, hd, zero_mul, sub_zero]
  have hrow : ∀ x, ∑ x', (P x x' - η) = 1 - Fintype.card X * η := by
    intro x
    rw [sum_sub_distrib, hP.rowsum, sum_const, card_univ, nsmul_eq_mul]
  unfold l1
  calc ∑ x', |(d ᵥ* P) x'| ≤ ∑ x', ∑ x, |d x| * (P x x' - η) := by
        refine sum_le_sum fun x' _ => ?_
        rw [hkey]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hη x x'))]
    _ = ∑ x, |d x| * ∑ x', (P x x' - η) := by
        rw [sum_comm]
        simp only [mul_sum]
    _ = (1 - Fintype.card X * η) * ∑ x, |d x| := by
        simp only [hrow]
        rw [← sum_mul, mul_comm]

variable [DecidableEq X]

/-- `ψ ↦ ψPᵗ` preserves total mass. -/
theorem IsMarkov.sum_vecMul_pow {P : Matrix X X ℝ} (hP : IsMarkov P) (d : X → ℝ) (t : ℕ) :
    ∑ x, (d ᵥ* P ^ t) x = ∑ x, d x := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← vecMul_vecMul, hP.sum_vecMul, ih]

/-- `ψPᵗ` is a distribution when `ψ` is. -/
theorem IsMarkov.isDistribution_vecMul_pow {P : Matrix X X ℝ} (hP : IsMarkov P) {ψ : X → ℝ}
    (hψ : IsDistribution ψ) (t : ℕ) : IsDistribution (ψ ᵥ* P ^ t) := by
  induction t with
  | zero => simpa using hψ
  | succ t ih => rw [pow_succ, ← vecMul_vecMul]; exact hP.isDistribution_vecMul ih

/-- The iterated estimate: `‖dPᵗ‖₁ ≤ (1 − nη)ᵗ ‖d‖₁` for `∑ d = 0`. -/
theorem l1_vecMul_pow_le {P : Matrix X X ℝ} (hP : IsMarkov P) {η : ℝ} (hη : ∀ x x', η ≤ P x x')
    (hlam : 0 ≤ 1 - Fintype.card X * η) {d : X → ℝ} (hd : ∑ x, d x = 0) (t : ℕ) :
    l1 (d ᵥ* P ^ t) ≤ (1 - Fintype.card X * η) ^ t * l1 d := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← vecMul_vecMul]
    have hsum : ∑ x, (d ᵥ* P ^ t) x = 0 := by rw [hP.sum_vecMul_pow, hd]
    calc l1 ((d ᵥ* P ^ t) ᵥ* P) ≤ (1 - Fintype.card X * η) * l1 (d ᵥ* P ^ t) :=
          l1_vecMul_le hP hη hsum
      _ ≤ (1 - Fintype.card X * η) * ((1 - Fintype.card X * η) ^ t * l1 d) :=
          mul_le_mul_of_nonneg_left ih hlam
      _ = (1 - Fintype.card X * η) ^ (t + 1) * l1 d := by ring

omit [DecidableEq X] in
/-- Coordinatewise continuity of `φ ↦ φP`: limits pass through `ᵥ*`. -/
theorem tendsto_vecMul {P : Matrix X X ℝ} {u : ℕ → X → ℝ} {a : X → ℝ}
    (h : Tendsto u atTop (𝓝 a)) : Tendsto (fun t => u t ᵥ* P) atTop (𝓝 (a ᵥ* P)) := by
  rw [tendsto_pi_nhds] at h ⊢
  intro x'
  simp only [vecMul_apply_eq]
  exact tendsto_finsetSum _ fun x _ => (h x).mul_const _

/-- A stationary `ψ` is fixed by every power. -/
theorem vecMul_pow_of_vecMul_eq {P : Matrix X X ℝ} {ψ : X → ℝ} (h : ψ ᵥ* P = ψ) (k : ℕ) :
    ψ ᵥ* P ^ k = ψ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, h]

/-- Exercise 3.1.7 (Vol. 1, p. 89), general form: if `P` is a Markov matrix with every entry
positive, then there is a stationary distribution `ψ*`, it is the only one, and `ψPᵗ → ψ*` for
every distribution `ψ`. Dobrushin's estimate makes the orbit of any distribution Cauchy. -/
theorem IsMarkov.tendsto_vecMul_pow_of_pos [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hpos : ∀ x x', 0 < P x x') :
    ∃ ψ' : X → ℝ, IsDistribution ψ' ∧ ψ' ᵥ* P = ψ' ∧
      (∀ φ, IsDistribution φ → φ ᵥ* P = φ → φ = ψ') ∧
      ∀ ψ, IsDistribution ψ → Tendsto (fun t : ℕ => ψ ᵥ* P ^ t) atTop (𝓝 ψ') := by
  -- the smallest entry `η > 0` and the modulus `λ = 1 − nη ∈ [0, 1)`
  obtain ⟨p, -, hp⟩ := exists_min_image (univ : Finset (X × X)) (fun q => P q.1 q.2) univ_nonempty
  set η := P p.1 p.2 with hηdef
  have hη : ∀ x x', η ≤ P x x' := fun x x' => hp (x, x') (mem_univ _)
  have hηpos : 0 < η := hpos _ _
  set n : ℕ := Fintype.card X with hn
  have hnpos : 0 < n := Fintype.card_pos
  set lam : ℝ := 1 - n * η with hlam
  have hlam0 : 0 ≤ lam := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have h1 := hP.rowsum x
    have h2 : ∑ x' : X, η ≤ ∑ x', P x x' := sum_le_sum fun x' _ => hη x x'
    rw [sum_const, card_univ, nsmul_eq_mul, h1] at h2
    rw [hlam]
    linarith
  have hlam1 : lam < 1 := by
    rw [hlam]
    have : (0 : ℝ) < n * η := by positivity
    linarith
  -- the orbit of the uniform distribution is Cauchy
  set ψ₀ : X → ℝ := fun _ => (n : ℝ)⁻¹ with hψ₀
  have hψ₀dist : IsDistribution ψ₀ := ⟨fun _ => by positivity, by
    rw [hψ₀]
    simp only [sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)⟩
  set u : ℕ → X → ℝ := fun t => ψ₀ ᵥ* P ^ t with hu
  have hzero : ∑ x, (ψ₀ - ψ₀ ᵥ* P) x = 0 := by
    simp only [Pi.sub_apply]
    rw [sum_sub_distrib, hP.sum_vecMul, sub_self]
  have hstep : ∀ t, dist (u t) (u (t + 1)) ≤ l1 (ψ₀ - ψ₀ ᵥ* P) * lam ^ t := by
    intro t
    rw [dist_eq_norm, hu]
    have h1 : ψ₀ ᵥ* P ^ t - ψ₀ ᵥ* P ^ (t + 1) = (ψ₀ - ψ₀ ᵥ* P) ᵥ* P ^ t := by
      rw [sub_vecMul, pow_succ', ← vecMul_vecMul]
    simp only
    rw [h1]
    refine (norm_le_l1 _).trans ?_
    rw [mul_comm]
    exact l1_vecMul_pow_le hP hη hlam0 hzero t
  have hcauchy : CauchySeq u := cauchySeq_of_le_geometric lam _ hlam1 hstep
  obtain ⟨ψ', hψ'⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- `ψ'` is a distribution
  have hψ'dist : IsDistribution ψ' := by
    refine ⟨fun x => ?_, ?_⟩
    · exact ge_of_tendsto' (tendsto_pi_nhds.1 hψ' x) fun t =>
        (hP.isDistribution_vecMul_pow hψ₀dist t).nonneg x
    · have h1 : Tendsto (fun t => ∑ x, u t x) atTop (𝓝 (∑ x, ψ' x)) :=
        tendsto_finsetSum _ fun x _ => tendsto_pi_nhds.1 hψ' x
      have h2 : (fun t => ∑ x, u t x) = fun _ => 1 :=
        funext fun t => (hP.isDistribution_vecMul_pow hψ₀dist t).sum_eq_one
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- `ψ'` is stationary: `u (t + 1) = u t ᵥ* P` has limits `ψ'` and `ψ'P`
  have hstat : ψ' ᵥ* P = ψ' := by
    have h1 : Tendsto (fun t => u (t + 1)) atTop (𝓝 ψ') := hψ'.comp (tendsto_add_atTop_nat 1)
    have h2 : (fun t => u (t + 1)) = fun t => u t ᵥ* P := by
      funext t
      rw [hu]
      simp only
      rw [pow_succ, ← vecMul_vecMul]
    rw [h2] at h1
    exact tendsto_nhds_unique (tendsto_vecMul hψ') h1
  -- geometric convergence from any distribution
  have hconv : ∀ ψ, IsDistribution ψ → Tendsto (fun t : ℕ => ψ ᵥ* P ^ t) atTop (𝓝 ψ') := by
    intro ψ hψ
    rw [tendsto_iff_dist_tendsto_zero]
    simp only [dist_eq_norm]
    have hd : ∑ x, (ψ - ψ') x = 0 := by
      simp only [Pi.sub_apply]
      rw [sum_sub_distrib, hψ.sum_eq_one, hψ'dist.sum_eq_one, sub_self]
    refine squeeze_zero (g := fun t : ℕ => lam ^ t * l1 (ψ - ψ')) (fun _ => norm_nonneg _)
      (fun t => ?_) ?_
    · have h1 : ψ ᵥ* P ^ t - ψ' = (ψ - ψ') ᵥ* P ^ t := by
        rw [sub_vecMul, vecMul_pow_of_vecMul_eq hstat]
      rw [h1]
      exact (norm_le_l1 _).trans (l1_vecMul_pow_le hP hη hlam0 hd t)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1).mul_const (l1 (ψ - ψ'))
  refine ⟨ψ', hψ'dist, hstat, fun φ hφ hφs => ?_, hconv⟩
  -- uniqueness: a stationary `φ` is its own orbit, which converges to `ψ'`
  have h1 : Tendsto (fun t : ℕ => φ ᵥ* P ^ t) atTop (𝓝 ψ') := hconv φ hφ
  have h2 : (fun t : ℕ => φ ᵥ* P ^ t) = fun _ => φ :=
    funext fun t => vecMul_pow_of_vecMul_eq hφs t
  rw [h2] at h1
  exact (tendsto_nhds_unique h1 tendsto_const_nhds).symm

/-- The point mass at `x` is a distribution. -/
theorem isDistribution_single (x : X) : IsDistribution (Pi.single x (1 : ℝ)) where
  nonneg y := by
    rw [Pi.single_apply]
    split_ifs <;> norm_num
  sum_eq_one := by simp

/-- `δₓ Pᵗ` is row `x` of `Pᵗ`. -/
theorem single_vecMul_eq_row (M : Matrix X X ℝ) (x : X) : Pi.single x (1 : ℝ) ᵥ* M = M x := by
  funext x'
  rw [vecMul_apply_eq]
  simp [Pi.single_apply]

/-- Rows of powers of a positive Markov matrix converge to the stationary distribution. -/
theorem IsMarkov.tendsto_pow_apply_of_pos [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hpos : ∀ x x', 0 < P x x') :
    ∃ ψ' : X → ℝ, IsDistribution ψ' ∧ ψ' ᵥ* P = ψ' ∧ (∀ x', 0 < ψ' x') ∧
      ∀ x x', Tendsto (fun t : ℕ => (P ^ t) x x') atTop (𝓝 (ψ' x')) := by
  obtain ⟨ψ', hdist, hstat, -, hconv⟩ := hP.tendsto_vecMul_pow_of_pos hpos
  refine ⟨ψ', hdist, hstat, fun x' => ?_, fun x x' => ?_⟩
  · -- `ψ'(x') = ∑ ψ'(x)P(x, x') > 0` since some `ψ'(x) > 0`
    obtain ⟨y, hy⟩ : ∃ y, 0 < ψ' y := by
      by_contra h
      have := hdist.sum_eq_one
      rw [sum_eq_zero fun y _ =>
        le_antisymm (not_lt.1 fun hy => h ⟨y, hy⟩) (hdist.nonneg y)] at this
      exact zero_ne_one this
    have h1 : ψ' y * P y x' ≤ (ψ' ᵥ* P) x' :=
      single_le_sum (fun z _ => mul_nonneg (hdist.nonneg z) (hP.nonneg z x')) (mem_univ y)
    rw [hstat] at h1
    exact lt_of_lt_of_le (mul_pos hy (hpos y x')) h1
  · have := tendsto_pi_nhds.1 (hconv _ (isDistribution_single x)) x'
    simpa only [single_vecMul_eq_row] using this

/-- The conjugate Markov matrix `P(x, x') = A(x, x')e(x')/(ρe(x))` of a positive matrix with
positive eigenvector `e`, `Ae = ρe`. -/
noncomputable def conjMarkov (A : Matrix X X ℝ) (e : X → ℝ) (ρ : ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => A x x' * e x' / (ρ * e x)

omit [Fintype X] [DecidableEq X] in
theorem conjMarkov_apply (A : Matrix X X ℝ) (e : X → ℝ) (ρ : ℝ) (x x' : X) :
    conjMarkov A e ρ x x' = A x x' * e x' / (ρ * e x) := rfl

omit [DecidableEq X] in
/-- The conjugate is a Markov matrix with positive entries. -/
theorem isMarkov_conjMarkov {A : Matrix X X ℝ} (hpos : ∀ x x', 0 < A x x') {e : X → ℝ}
    (he : ∀ x, 0 < e x) {ρ : ℝ} (hρ : 0 < ρ) (heA : A *ᵥ e = ρ • e) :
    IsMarkov (conjMarkov A e ρ) ∧ ∀ x x', 0 < conjMarkov A e ρ x x' := by
  have hpos' : ∀ x x', 0 < conjMarkov A e ρ x x' := fun x x' =>
    div_pos (mul_pos (hpos x x') (he x')) (mul_pos hρ (he x))
  refine ⟨⟨fun x x' => (hpos' x x').le, fun x => ?_⟩, hpos'⟩
  simp only [conjMarkov_apply]
  rw [← sum_div]
  have h1 : ∑ x', A x x' * e x' = ρ * e x := by
    have := congrFun heA x
    simpa [mulVec, dotProduct] using this
  rw [h1]
  exact div_self (mul_pos hρ (he x)).ne'

/-- `Pᵗ(x, x') = ρ^{−t}Aᵗ(x, x')e(x')/e(x)` for the conjugate matrix. -/
theorem conjMarkov_pow_apply (A : Matrix X X ℝ) {e : X → ℝ} (he : ∀ x, 0 < e x) {ρ : ℝ}
    (hρ : 0 < ρ) (t : ℕ) (x x' : X) :
    (conjMarkov A e ρ ^ t) x x' = (A ^ t) x x' * e x' / (ρ ^ t * e x) := by
  induction t generalizing x' with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs with h
    · subst h
      have := (he x).ne'
      field_simp
    · simp
  | succ t ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, sum_mul, sum_div]
    refine sum_congr rfl fun z _ => ?_
    rw [ih, conjMarkov_apply]
    have hz := (he z).ne'
    have hx := (he x).ne'
    have hρ' := hρ.ne'
    field_simp
    ring

/-- **Theorem 2.3.1, everywhere-positive case** (p. 69), the convergence (2.11): for `A ≫ 0`
there are positive right and left eigenvectors `e, ε` for `ρ(A)` with `⟨ε, e⟩ = 1` and
`ρ(A)^{−t} Aᵗ(x, x') → e(x)ε(x')` for all `x, x'`. -/
theorem tendsto_pow_of_pos [Nonempty X] {A : Matrix X X ℝ} (hpos : ∀ x x', 0 < A x x') :
    ∃ e ε : X → ℝ, (∀ x, 0 < e x) ∧ (∀ x, 0 < ε x) ∧ A *ᵥ e = specRad A • e ∧
      ε ᵥ* A = specRad A • ε ∧ ε ⬝ᵥ e = 1 ∧
      ∀ x x', Tendsto (fun t : ℕ => (specRad A)⁻¹ ^ t * (A ^ t) x x') atTop (𝓝 (e x * ε x')) := by
  have hirr := irreducible_of_pos hpos
  have hρ := hirr.specRad_pos
  obtain ⟨e, he, heA⟩ := hirr.exists_pos_eigenvector
  set ρ := specRad A with hρdef
  obtain ⟨hPm, hPpos⟩ := isMarkov_conjMarkov hpos he hρ heA
  obtain ⟨ψ, hψdist, hψstat, hψpos, hψconv⟩ := hPm.tendsto_pow_apply_of_pos hPpos
  refine ⟨e, fun x' => ψ x' / e x', he, fun x' => div_pos (hψpos x') (he x'), heA, ?_, ?_, ?_⟩
  · -- `ε A = ρ ε` from `ψP = ψ`
    funext x'
    have h1 := congrFun hψstat x'
    rw [vecMul_apply_eq] at h1
    simp only [conjMarkov_apply] at h1
    rw [vecMul_apply_eq, Pi.smul_apply, smul_eq_mul]
    have hx' := (he x').ne'
    have hρ' := hρ.ne'
    -- `∑ ψ(x) A(x, x') e(x') / (ρ e(x)) = ψ(x')`
    have h2 : ∑ x, ψ x / e x * A x x' = ρ * (ψ x' / e x') := by
      have h3 : ∑ x, ψ x * (A x x' * e x' / (ρ * e x)) =
          (e x' / ρ) * ∑ x, ψ x / e x * A x x' := by
        rw [mul_sum]
        refine sum_congr rfl fun x _ => ?_
        have hx := (he x).ne'
        field_simp
      rw [h3] at h1
      rw [← h1]
      field_simp
    exact h2
  · -- `⟨ε, e⟩ = ∑ ψ = 1`
    have : ∑ x, ψ x / e x * e x = ∑ x, ψ x := sum_congr rfl fun x _ => div_mul_cancel₀ _ (he x).ne'
    change ∑ x, ψ x / e x * e x = 1
    rw [this]
    exact hψdist.sum_eq_one
  · intro x x'
    have h1 := hψconv x x'
    have h2 : ∀ t : ℕ, ρ⁻¹ ^ t * (A ^ t) x x' = (conjMarkov A e ρ ^ t) x x' * e x / e x' := by
      intro t
      rw [conjMarkov_pow_apply A he hρ]
      have hx := (he x).ne'
      have hx' := (he x').ne'
      have hρt : ρ ^ t ≠ 0 := pow_ne_zero _ hρ.ne'
      field_simp
      rw [one_div, inv_pow, mul_comm ((ρ ^ t)⁻¹), inv_mul_cancel_right₀ hρt]
    simp only [h2]
    have := (h1.mul_const (e x)).div_const (e x')
    convert this using 2
    ring

end SargentStachurski.StochasticDiscounting

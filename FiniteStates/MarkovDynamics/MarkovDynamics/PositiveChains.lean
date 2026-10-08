/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDynamics.MarkovChains
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Everywhere-positive Markov matrices are globally stable on `D(X)`

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Exercise 3.1.7
(p. 89): for a Markov matrix `P ≫ 0`, the map `ψ ↦ ψP` is globally stable on
the distributions `D(X)`. The book's hint is the Perron–Frobenius theorem;
the proof here is Dobrushin's ℓ¹ contraction estimate instead. If every
entry of `P` is at least `ε > 0`, then for any `d` with `∑ d = 0`,
`‖dP‖₁ ≤ (1 − nε)‖d‖₁`, since `(dP)(x') = ∑ₓ d(x)(P(x, x') − ε)`. The orbit
of any distribution is therefore Cauchy, its limit `ψ*` is a stationary
distribution, every stationary distribution equals `ψ*`, and `ψPᵗ → ψ*` at
the geometric rate `(1 − nε)ᵗ`.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDynamics

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The ℓ¹ norm `‖d‖₁ = ∑ |d(x)|` on `ℝ^X`. -/
def l1 (d : X → ℝ) : ℝ := ∑ x, |d x|

omit [DecidableEq X] in
theorem l1_nonneg (d : X → ℝ) : 0 ≤ l1 d := sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq X] in
/-- The supremum norm is bounded by the ℓ¹ norm. -/
theorem norm_le_l1 (d : X → ℝ) : ‖d‖ ≤ l1 d := by
  rw [pi_norm_le_iff_of_nonneg (l1_nonneg d)]
  intro x
  rw [Real.norm_eq_abs]
  exact single_le_sum (fun y _ => abs_nonneg (d y)) (mem_univ x)

omit [DecidableEq X] in
theorem l1_eq_zero_iff (d : X → ℝ) : l1 d = 0 ↔ d = 0 := by
  constructor
  · intro h
    funext x
    have := (sum_eq_zero_iff_of_nonneg fun y _ => abs_nonneg (d y)).1 h x (mem_univ x)
    simpa using this
  · rintro rfl
    simp [l1]

omit [DecidableEq X] in
/-- `ψ ↦ ψP` preserves total mass: `∑ (dP) = ∑ d`. -/
theorem sum_vecMul {P : Matrix X X ℝ} (hP : IsMarkov P) (d : X → ℝ) :
    ∑ x', (d ᵥ* P) x' = ∑ x, d x := by
  have h : ∀ x', (d ᵥ* P) x' = ∑ x, P x x' * d x := fun x' => vecMul_apply P d x'
  simp only [h]
  rw [sum_comm]
  simp only [← sum_mul, hP.rowsum, one_mul]

omit [DecidableEq X] in
/-- Dobrushin's estimate: if every entry of the Markov matrix `P` is at least `ε`, then for `d`
with `∑ d = 0`, `‖dP‖₁ ≤ (1 − nε)‖d‖₁`, where `n = |X|`. -/
theorem l1_vecMul_le {P : Matrix X X ℝ} (hP : IsMarkov P) {ε : ℝ} (hε : ∀ x x', ε ≤ P x x')
    {d : X → ℝ} (hd : ∑ x, d x = 0) :
    l1 (d ᵥ* P) ≤ (1 - Fintype.card X * ε) * l1 d := by
  -- `(dP)(x') = ∑ₓ d(x)(P(x, x') − ε)` because `∑ d = 0`
  have hkey : ∀ x', (d ᵥ* P) x' = ∑ x, d x * (P x x' - ε) := by
    intro x'
    rw [vecMul_apply]
    have : ∑ x, d x * (P x x' - ε) = ∑ x, d x * P x x' - (∑ x, d x) * ε := by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [this, hd, zero_mul, sub_zero]
    exact sum_congr rfl fun x _ => mul_comm _ _
  have hrow : ∀ x, ∑ x', (P x x' - ε) = 1 - Fintype.card X * ε := by
    intro x
    rw [sum_sub_distrib, hP.rowsum, sum_const, card_univ, nsmul_eq_mul]
  unfold l1
  calc ∑ x', |(d ᵥ* P) x'| ≤ ∑ x', ∑ x, |d x| * (P x x' - ε) := by
        refine sum_le_sum fun x' _ => ?_
        rw [hkey]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hε x x'))]
    _ = ∑ x, |d x| * ∑ x', (P x x' - ε) := by
        rw [sum_comm]
        simp only [mul_sum]
    _ = (1 - Fintype.card X * ε) * ∑ x, |d x| := by
        simp only [hrow]
        rw [← sum_mul, mul_comm]

/-- `ψ ↦ ψPᵗ` preserves total mass. -/
theorem sum_vecMul_pow {P : Matrix X X ℝ} (hP : IsMarkov P) (d : X → ℝ) (t : ℕ) :
    ∑ x, (d ᵥ* P ^ t) x = ∑ x, d x := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← vecMul_vecMul, sum_vecMul hP, ih]

/-- The iterated estimate: `‖dPᵗ‖₁ ≤ (1 − nε)ᵗ ‖d‖₁` for `∑ d = 0`. -/
theorem l1_vecMul_pow_le {P : Matrix X X ℝ} (hP : IsMarkov P) {ε : ℝ} (hε : ∀ x x', ε ≤ P x x')
    (hlam : 0 ≤ 1 - Fintype.card X * ε) {d : X → ℝ} (hd : ∑ x, d x = 0) (t : ℕ) :
    l1 (d ᵥ* P ^ t) ≤ (1 - Fintype.card X * ε) ^ t * l1 d := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← vecMul_vecMul]
    have hsum : ∑ x, (d ᵥ* P ^ t) x = 0 := by rw [sum_vecMul_pow hP, hd]
    calc l1 ((d ᵥ* P ^ t) ᵥ* P) ≤ (1 - Fintype.card X * ε) * l1 (d ᵥ* P ^ t) :=
          l1_vecMul_le hP hε hsum
      _ ≤ (1 - Fintype.card X * ε) * ((1 - Fintype.card X * ε) ^ t * l1 d) :=
          mul_le_mul_of_nonneg_left ih hlam
      _ = (1 - Fintype.card X * ε) ^ (t + 1) * l1 d := by ring

omit [DecidableEq X] in
/-- Coordinatewise continuity of `φ ↦ φP`: limits pass through `ᵥ*`. -/
theorem tendsto_vecMul {P : Matrix X X ℝ} {u : ℕ → X → ℝ} {a : X → ℝ}
    (h : Tendsto u atTop (𝓝 a)) : Tendsto (fun t => u t ᵥ* P) atTop (𝓝 (a ᵥ* P)) := by
  rw [tendsto_pi_nhds] at h ⊢
  intro x'
  simp only [vecMul_apply]
  exact tendsto_finsetSum _ fun x _ => (h x).const_mul _

/-- Exercise 3.1.7 (p. 89), general form: if `P` is a Markov matrix with every entry positive,
then `ψ ↦ ψP` is globally stable on `D(X)`: there is a stationary distribution `ψ*`, it is the
only stationary distribution, and `ψPᵗ → ψ*` for every distribution `ψ`. -/
theorem globallyStable_of_pos [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hpos : ∀ x x', 0 < P x x') :
    ∃ ψ' : X → ℝ, IsDistribution ψ' ∧ IsStationary P ψ' ∧
      (∀ φ, IsDistribution φ → IsStationary P φ → φ = ψ') ∧
      ∀ ψ, IsDistribution ψ → Tendsto (fun t : ℕ => ψ ᵥ* P ^ t) atTop (𝓝 ψ') := by
  -- the smallest entry `ε > 0` and the modulus `λ = 1 − nε ∈ [0, 1)`
  obtain ⟨p, -, hp⟩ := exists_min_image (univ : Finset (X × X)) (fun q => P q.1 q.2) univ_nonempty
  set ε := P p.1 p.2 with hεdef
  have hε : ∀ x x', ε ≤ P x x' := fun x x' => hp (x, x') (mem_univ _)
  have hεpos : 0 < ε := hpos _ _
  set n : ℕ := Fintype.card X with hn
  have hnpos : 0 < n := Fintype.card_pos
  set lam : ℝ := 1 - n * ε with hlam
  have hlam0 : 0 ≤ lam := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have h1 := hP.rowsum x
    have h2 : ∑ x' : X, ε ≤ ∑ x', P x x' := sum_le_sum fun x' _ => hε x x'
    rw [sum_const, card_univ, nsmul_eq_mul, h1] at h2
    rw [hlam]
    linarith
  have hlam1 : lam < 1 := by
    rw [hlam]
    have : (0 : ℝ) < n * ε := by positivity
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
    rw [sum_sub_distrib, sum_vecMul hP, sub_self]
  have hstep : ∀ t, dist (u t) (u (t + 1)) ≤ l1 (ψ₀ - ψ₀ ᵥ* P) * lam ^ t := by
    intro t
    rw [dist_eq_norm, hu]
    have h1 : ψ₀ ᵥ* P ^ t - ψ₀ ᵥ* P ^ (t + 1) = (ψ₀ - ψ₀ ᵥ* P) ᵥ* P ^ t := by
      rw [sub_vecMul, pow_succ', ← vecMul_vecMul]
    simp only
    rw [h1]
    refine (norm_le_l1 _).trans ?_
    rw [mul_comm]
    exact l1_vecMul_pow_le hP hε hlam0 hzero t
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
  have hstat : IsStationary P ψ' := by
    have h1 : Tendsto (fun t => u (t + 1)) atTop (𝓝 ψ') := hψ'.comp (tendsto_add_atTop_nat 1)
    have h2 : (fun t => u (t + 1)) = fun t => u t ᵥ* P := by
      funext t
      rw [hu]
      simp only
      rw [pow_succ, ← vecMul_vecMul]
    rw [h2] at h1
    exact (tendsto_nhds_unique h1 (tendsto_vecMul hψ')).symm
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
        rw [sub_vecMul, hstat.vecMul_pow]
      rw [h1]
      exact (norm_le_l1 _).trans (l1_vecMul_pow_le hP hε hlam0 hd t)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1).mul_const (l1 (ψ - ψ'))
  refine ⟨ψ', hψ'dist, hstat, fun φ hφ hφs => ?_, hconv⟩
  -- uniqueness: a stationary `φ` is its own orbit, which converges to `ψ'`
  have h1 : Tendsto (fun t : ℕ => φ ᵥ* P ^ t) atTop (𝓝 ψ') := hconv φ hφ
  have h2 : (fun t : ℕ => φ ᵥ* P ^ t) = fun _ => φ := funext fun t => hφs.vecMul_pow t
  rw [h2] at h1
  exact (tendsto_nhds_unique h1 tendsto_const_nhds).symm

omit [DecidableEq X] in
/-- The map `ψ ↦ ψP` as a self-map of the distributions `D(X)`. -/
def distMap {P : Matrix X X ℝ} (hP : IsMarkov P) (ψ : {ψ : X → ℝ // IsDistribution ψ}) :
    {ψ : X → ℝ // IsDistribution ψ} :=
  ⟨ψ.1 ᵥ* P, hP.isDistribution_vecMul ψ.2⟩

theorem distMap_iterate {P : Matrix X X ℝ} (hP : IsMarkov P) (ψ : {ψ : X → ℝ // IsDistribution ψ})
    (t : ℕ) : ((distMap hP)^[t] ψ).1 = ψ.1 ᵥ* P ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [iterate_succ_apply']
    change ((distMap hP)^[t] ψ).1 ᵥ* P = _
    rw [ih, vecMul_vecMul, pow_succ]

omit [DecidableEq X] in
/-- Exercise 3.1.7 (p. 89) in the vocabulary of §1.2.2: for `P ≫ 0` Markov, `ψ ↦ ψP` is a
globally stable self-map of `D(X)`. -/
theorem globallyStable_distMap [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hpos : ∀ x x', 0 < P x x') : GloballyStable (distMap hP) := by
  classical
  obtain ⟨ψ', hψ'dist, hstat, huniq, hconv⟩ := globallyStable_of_pos hP hpos
  refine ⟨⟨ψ', hψ'dist⟩, Subtype.ext hstat, fun v hv => Subtype.ext (huniq v.1 v.2 ?_),
    fun ψ => ?_⟩
  · exact congrArg Subtype.val hv
  · rw [tendsto_subtype_rng]
    simp only [distMap_iterate]
    exact hconv ψ.1 ψ.2

end SargentStachurski.MarkovDynamics

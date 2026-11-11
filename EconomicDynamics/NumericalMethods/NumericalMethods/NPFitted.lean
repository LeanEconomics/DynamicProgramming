/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NPDiscreteDP
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Smooth approximation: value function interpolation

Miao, *Economic Dynamics in Discrete Time*, §11.6.2 (pp. 380–381).

Value function interpolation (Steps 1–4, p. 380): values `V(k_m, s_i)` on a
capital grid are interpolated to `V̂(k', s_j)` on `[k_min, k_max]`, and Step 3
computes `V₁(k_m, s_i) = sup_{k' ∈ [k_min, k_max]} {u(f(k_m, exp s_i) − k')
+ β ∑_j π_ij V̂₀(k', s_j)}`. We write the interpolant in the form
`V̂(k', s_j) = ∑_m w_m(k') V(k_m, s_j)` with weights `w_m(k') ≥ 0` summing to one
on `[k_min, k_max]` (an "averager", e.g. piecewise linear interpolation; we prove
that the two-node linear interpolation weights qualify). Under this
shape-preserving interpolation the fitted Bellman operator is a contraction of
modulus `β` (Blackwell), so the iteration of Step 4 converges to a unique fixed
point from any initial guess (`np_fitted_contraction`, `np_fitted_converges`).

The book does not state a convergence result for this method ("keep iterating
until convergence"); the theorem above is the one that makes the step sound.
Interpolation schemes that are not averagers (cubic splines, Chebyshev
interpolation) need not give a contraction; that remark is not formalised.
The projection variant (p. 381, residual `R = V̂ − BV̂`) is covered by the
abstract `np_residual_bound` and `np_residual_zero_iff` in `NPDiscreteDP`.
-/

namespace Miao.NumericalMethods.NP

open Finset Filter Topology Function

/-- The data of value function interpolation (Miao, p. 380): capital interval `[k_min, k_max]`,
capital grid, Markov chain for `s = ln z`, utility, technology, discount factor, and interpolation
weights `w_m(k')` that are nonnegative and sum to one on `[k_min, k_max]`; the period utility is
bounded above on the choice interval. -/
structure FittedGrid (nk nz : ℕ) where
  kmin : ℝ
  kmax : ℝ
  kmin_le : kmin ≤ kmax
  kgrid : Fin nk → ℝ
  sgrid : Fin nz → ℝ
  pz : Matrix (Fin nz) (Fin nz) ℝ
  pz_markov : IsMarkov pz
  u : ℝ → ℝ
  f : ℝ → ℝ → ℝ
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  wt : ℝ → Fin nk → ℝ
  wt_nonneg : ∀ k ∈ Set.Icc kmin kmax, ∀ m, 0 ≤ wt k m
  wt_sum : ∀ k ∈ Set.Icc kmin kmax, ∑ m, wt k m = 1
  u_bdd : ∀ x : Fin nk × Fin nz,
    BddAbove (Set.range fun k : Set.Icc kmin kmax => u (f (kgrid x.1) (Real.exp (sgrid x.2)) - k))

namespace FittedGrid

variable {nk nz : ℕ} (G : FittedGrid nk nz)

/-- The interpolated continuation `∑_j π_ij V̂(k', s_j)` with
`V̂(k', s_j) = ∑_m w_m(k') V(k_m, s_j)`
(Steps 2–3, p. 380). -/
noncomputable def cont (V : Fin nk × Fin nz → ℝ) (i : Fin nz) (k : ℝ) : ℝ :=
  ∑ j, G.pz i j * ∑ m, G.wt k m * V (m, j)

/-- The objective of Step 3 at choice `k'`. -/
noncomputable def obj (V : Fin nk × Fin nz → ℝ) (x : Fin nk × Fin nz) (k : Set.Icc G.kmin G.kmax) :
    ℝ :=
  G.u (G.f (G.kgrid x.1) (Real.exp (G.sgrid x.2)) - k) + G.β * G.cont V x.2 k

/-- Step 3 (Miao, p. 380): `V₁(k_m, s_i) = sup_{k' ∈ [k_min, k_max]} {u(f(k_m, exp s_i) − k') +
β ∑_j π_ij V̂₀(k', s_j)}`. -/
noncomputable def fittedBellman (V : Fin nk × Fin nz → ℝ) : Fin nk × Fin nz → ℝ :=
  fun x => ⨆ k : Set.Icc G.kmin G.kmax, G.obj V x k

theorem cont_mono {V W : Fin nk × Fin nz → ℝ} (h : V ≤ W) (i : Fin nz) (k : Set.Icc G.kmin G.kmax) :
    G.cont V i k ≤ G.cont W i k := by
  unfold cont
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (G.pz_markov.nonneg i j)
  exact Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (h (m, j)) (G.wt_nonneg k k.2 m)

theorem cont_add_const (V : Fin nk × Fin nz → ℝ) (c : ℝ) (i : Fin nz)
    (k : Set.Icc G.kmin G.kmax) : G.cont (V + fun _ => c) i k = G.cont V i k + c := by
  unfold cont
  have h1 : ∀ j, ∑ m, G.wt k m * (V + fun _ : Fin nk × Fin nz => c) (m, j) =
      ∑ m, G.wt k m * V (m, j) + c := by
    intro j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, G.wt_sum k k.2,
      one_mul]
  simp only [h1, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, G.pz_markov.rowsum, one_mul]

theorem cont_le_norm (V : Fin nk × Fin nz → ℝ) (i : Fin nz) (k : Set.Icc G.kmin G.kmax) :
    G.cont V i k ≤ ‖V‖ := by
  have hV : V ≤ fun _ => ‖V‖ := fun y => by
    have := norm_le_pi_norm V y
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have h := G.cont_mono hV i k
  have h0 := G.cont_add_const 0 ‖V‖ i k
  have hz : G.cont 0 i k = 0 := by simp [cont]
  rw [zero_add, hz, zero_add] at h0
  exact h.trans h0.le

theorem bddAbove_obj (V : Fin nk × Fin nz → ℝ) (x : Fin nk × Fin nz) :
    BddAbove (Set.range (G.obj V x)) := by
  obtain ⟨Mu, hMu⟩ := G.u_bdd x
  refine ⟨Mu + G.β * ‖V‖, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact add_le_add (hMu ⟨k, rfl⟩)
    (mul_le_mul_of_nonneg_left (G.cont_le_norm V x.2 k) G.β_pos.le)

/-- Value function interpolation with an averaging (shape-preserving) interpolant: the fitted
Bellman operator of Steps 2–3 (Miao, p. 380) is a contraction of modulus `β` in the supremum
norm. -/
theorem np_fitted_contraction : IsContractionOn G.fittedBellman Set.univ G.β := by
  have hne : Nonempty (Set.Icc G.kmin G.kmax) := ⟨⟨G.kmin, Set.left_mem_Icc.2 G.kmin_le⟩⟩
  refine isContractionOn_of_blackwell G.β_pos.le G.β_lt_one ?_ ?_
  · intro V W h x
    exact ciSup_mono (G.bddAbove_obj W x) fun k =>
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (G.cont_mono h x.2 k) G.β_pos.le)
  · intro V c _ x
    refine ciSup_le fun k => ?_
    have h1 : G.obj (V + fun _ => c) x k = G.obj V x k + G.β * c := by
      simp only [obj, G.cont_add_const]
      ring
    rw [h1, Pi.add_apply]
    exact add_le_add (le_ciSup (G.bddAbove_obj V x) k) le_rfl

/-- Step 4 (Miao, p. 380), "keep iterating until convergence": the fitted Bellman operator has a
unique fixed point and its iterates converge to it from every initial guess `V₀`. -/
theorem np_fitted_converges :
    ∃ V : Fin nk × Fin nz → ℝ, IsFixedPt G.fittedBellman V ∧
      (∀ W, IsFixedPt G.fittedBellman W → W = V) ∧
        ∀ V0, Tendsto (fun n : ℕ => G.fittedBellman^[n] V0) atTop (𝓝 V) :=
  G.np_fitted_contraction.globallyStable_univ

end FittedGrid

/-- Piecewise linear interpolation between two nodes `k₁ < k₂`: the weights `(k₂ − k)/(k₂ − k₁)`
and `(k − k₁)/(k₂ − k₁)`. -/
noncomputable def np_linWeights (k1 k2 : ℝ) (k : ℝ) : Fin 2 → ℝ :=
  ![(k2 - k) / (k2 - k1), (k - k1) / (k2 - k1)]

/-- Linear interpolation is an averager on `[k₁, k₂]`: its weights are nonnegative and sum to one,
and it reproduces the data at the nodes. -/
theorem np_linWeights_averager {k1 k2 : ℝ} (h : k1 < k2) :
    (∀ k ∈ Set.Icc k1 k2, ∀ m, 0 ≤ np_linWeights k1 k2 k m) ∧
      (∀ k ∈ Set.Icc k1 k2, ∑ m, np_linWeights k1 k2 k m = 1) ∧
        np_linWeights k1 k2 k1 = ![1, 0] ∧ np_linWeights k1 k2 k2 = ![0, 1] := by
  have hd : 0 < k2 - k1 := sub_pos.2 h
  refine ⟨fun k hk m => ?_, fun k _ => ?_, ?_, ?_⟩
  · fin_cases m
    · exact div_nonneg (by linarith [hk.2]) hd.le
    · exact div_nonneg (by linarith [hk.1]) hd.le
  · simp only [np_linWeights, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  · funext m
    fin_cases m <;> simp [np_linWeights, hd.ne']
  · funext m
    fin_cases m <;> simp [np_linWeights, hd.ne']

/-- A concrete instance of value function interpolation: two capital nodes `0 < 1` with linear
interpolation, one shock state, zero utility and `β = 1/2`. -/
noncomputable def np_fittedGridExample : FittedGrid 2 1 where
  kmin := 0
  kmax := 1
  kmin_le := zero_le_one
  kgrid := ![0, 1]
  sgrid := fun _ => 0
  pz := fun _ _ => 1
  pz_markov := ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
  u := fun _ => 0
  f := fun k _ => k
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  wt := np_linWeights 0 1
  wt_nonneg := (np_linWeights_averager zero_lt_one).1
  wt_sum := (np_linWeights_averager zero_lt_one).2.1
  u_bdd := fun _ => ⟨0, by rintro _ ⟨k, rfl⟩; exact le_rfl⟩

/-- The example's fitted iteration converges (its operator is a `1/2`-contraction). -/
theorem np_fittedGridExample_contraction :
    IsContractionOn np_fittedGridExample.fittedBellman Set.univ (1 / 2) :=
  np_fittedGridExample.np_fitted_contraction

end Miao.NumericalMethods.NP

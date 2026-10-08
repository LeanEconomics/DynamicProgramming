/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.Exponential
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Exponential flows and linear initial value problems

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.2.1–§10.1.2.3 (pp. 312–315).

* The flow `S_t = e^{tA}` has the semigroup property `S₀ = I`, `S_{s+t} = S_t S_s`
  (Example 10.1.2 is the scalar case).
* **Proposition 10.1.3**: `u_t = e^{tA}u₀` is the unique continuously differentiable solution of
  `u̇ = Au` on `[0, ∞)` (the book omits the uniqueness proof; here `e^{−tA}u_t` has derivative
  zero). Exercise 10.1.7 is the row-vector version `φ̇ = φP`.
* Exercise 10.1.8: `e^{tD} = diag(e^{tλ_j})`; (10.15): `e^{tλ} → 0` iff `Re λ < 0`.
* The bound `‖e^A‖ ≤ e^{‖A‖}`.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The semigroup property of `S_t = e^{tA}` (§10.1.2.1): `S₀ = I` and `S_{s+t} = S_t S_s`. -/
theorem exp_smul_semigroup (A : Matrix X X ℝ) (s t : ℝ) :
    NormedSpace.exp ((0 : ℝ) • A) = 1 ∧
      NormedSpace.exp ((s + t) • A) = NormedSpace.exp (t • A) * NormedSpace.exp (s • A) := by
  refine ⟨by rw [zero_smul, NormedSpace.exp_zero], ?_⟩
  rw [add_comm, add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left t |>.smul_right s)

/-- `e^{tA}e^{−tA} = I`. -/
theorem exp_smul_mul_exp_neg_smul (A : Matrix X X ℝ) (t : ℝ) :
    NormedSpace.exp (t • A) * NormedSpace.exp ((-t) • A) = 1 := by
  rw [← (exp_smul_semigroup A (-t) t).2, neg_add_cancel, zero_smul, NormedSpace.exp_zero]

/-- The linear map `M ↦ Mv` as a continuous linear map. -/
noncomputable def mulVecCLM (w : X → ℝ) : Matrix X X ℝ →L[ℝ] (X → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ w
      map_add' := fun M N => Matrix.add_mulVec M N w
      map_smul' := fun a M => Matrix.smul_mulVec a M w }

/-- The entry map `M ↦ M x y` as a continuous linear map. -/
noncomputable def entryCLM (x y : X) : Matrix X X ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Entries of `t ↦ e^{tA}` are differentiable, with `d/dt e^{tA} = Ae^{tA}` entrywise. -/
theorem hasDerivAt_exp_smul_entry (A : Matrix X X ℝ) (t : ℝ) (x y : X) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) x y) ((A * NormedSpace.exp (t • A)) x y) t :=
  (entryCLM x y).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' A t)

/-- Entries of `t ↦ e^{−tA}` are differentiable, with derivative `−Ae^{−tA}`. -/
theorem hasDerivAt_exp_neg_smul_entry (A : Matrix X X ℝ) (t : ℝ) (x y : X) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((-s) • A) x y)
      (-(A * NormedSpace.exp ((-t) • A)) x y) t := by
  have h := (hasDerivAt_exp_smul_entry A (-t) x y).comp t (hasDerivAt_neg t)
  have e : (A * NormedSpace.exp ((-t) • A)) x y * -1 = (-(A * NormedSpace.exp ((-t) • A))) x y := by
    rw [Matrix.neg_apply]
    ring
  exact h.congr_deriv e

omit [DecidableEq X] in
/-- Product rule for `t ↦ M_t v_t`, with `M` differentiable entrywise. -/
theorem hasDerivAt_mulVec_of_entry {M : ℝ → Matrix X X ℝ} {M' : Matrix X X ℝ} {v : ℝ → X → ℝ}
    {v' : X → ℝ} {t : ℝ} (hM : ∀ x y, HasDerivAt (fun s => M s x y) (M' x y) t)
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => M s *ᵥ v s) (M' *ᵥ v t + M t *ᵥ v') t := by
  rw [hasDerivAt_pi]
  intro x
  have hv' : ∀ y, HasDerivAt (fun s => v s y) (v' y) t := hasDerivAt_pi.1 hv
  have h := HasDerivAt.fun_sum (u := univ) fun y _ => (hM x y).mul (hv' y)
  simp only [Pi.add_apply, mulVec, dotProduct]
  convert h using 1
  rw [← Finset.sum_add_distrib]

/-- `t ↦ e^{tA}u₀` has derivative `A e^{tA}u₀` (Proposition 10.1.3, existence). -/
theorem hasDerivAt_exp_smul_mulVec (A : Matrix X X ℝ) (u₀ : X → ℝ) (t : ℝ) :
    HasDerivAt (fun s => NormedSpace.exp (s • A) *ᵥ u₀) (A *ᵥ (NormedSpace.exp (t • A) *ᵥ u₀))
      t := by
  have h := (mulVecCLM u₀).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul' A t)
  rw [Matrix.mulVec_mulVec]
  exact h

/-- **Proposition 10.1.3** (p. 313): `u_t = e^{tA}u₀` is the unique solution of `u̇ = Au` with
`u(0) = u₀` among functions differentiable on `[0, ∞)`. -/
theorem ivp_unique (A : Matrix X X ℝ) (u₀ : X → ℝ) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) *ᵥ u₀)
      (A *ᵥ (NormedSpace.exp (t • A) *ᵥ u₀)) t) ∧
      ∀ u : ℝ → X → ℝ, u 0 = u₀ → (∀ t : ℝ, 0 ≤ t → HasDerivAt u (A *ᵥ u t) t) →
        ∀ t : ℝ, 0 ≤ t → u t = NormedSpace.exp (t • A) *ᵥ u₀ := by
  refine ⟨hasDerivAt_exp_smul_mulVec A u₀, fun u hu0 hu t ht => ?_⟩
  set g : ℝ → X → ℝ := fun s => NormedSpace.exp ((-s) • A) *ᵥ u s
  have hg : ∀ s : ℝ, 0 ≤ s → HasDerivAt g 0 s := fun s hs => by
    have h := hasDerivAt_mulVec_of_entry (M' := -(A * NormedSpace.exp ((-s) • A)))
      (hasDerivAt_exp_neg_smul_entry A s) (hu s hs)
    convert h using 1
    rw [Matrix.neg_mulVec, Matrix.mulVec_mulVec, ← exp_smul_mul_comm A (-s), neg_add_cancel]
  have hcont : ContinuousOn g (Icc 0 t) := fun s hs =>
    (hg s hs.1).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont fun s hs => (hg s hs.1).hasDerivWithinAt
  have h := hconst t ⟨ht, le_rfl⟩
  simp only [g, neg_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, hu0] at h
  calc u t = (NormedSpace.exp (t • A) * NormedSpace.exp ((-t) • A)) *ᵥ u t := by
        rw [exp_smul_mul_exp_neg_smul, Matrix.one_mulVec]
    _ = NormedSpace.exp (t • A) *ᵥ (NormedSpace.exp ((-t) • A) *ᵥ u t) := by
        rw [Matrix.mulVec_mulVec]
    _ = NormedSpace.exp (t • A) *ᵥ u₀ := by rw [h]

/-- **Exercise 10.1.7** (p. 314): the row-vector IVP `φ̇ = φP`, `φ(0) = φ₀`, has the unique solution
`φ_t = φ₀e^{tP}` on `[0, ∞)`. -/
theorem ivp_unique_row (P : Matrix X X ℝ) (φ₀ : X → ℝ) (φ : ℝ → X → ℝ) (hφ0 : φ 0 = φ₀)
    (hφ : ∀ t, 0 ≤ t → HasDerivAt φ (φ t ᵥ* P) t) (t : ℝ) (ht : 0 ≤ t) :
    φ t = φ₀ ᵥ* NormedSpace.exp (t • P) := by
  have h := (ivp_unique Pᵀ φ₀).2 φ hφ0 (fun s hs => by
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
    exact hφ s hs) t ht
  rw [h, ← Matrix.vecMul_transpose, ← Matrix.transpose_smul, Matrix.exp_transpose,
    Matrix.transpose_transpose]

/-- **Exercise 10.1.8** (p. 314): `e^{tD} = diag(e^{tλ₁}, …, e^{tλₙ})` for `D = diag(λ)`. -/
theorem exp_smul_diagonal (d : X → ℝ) (t : ℝ) :
    NormedSpace.exp (t • Matrix.diagonal d) = Matrix.diagonal fun i => Real.exp (t * d i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    have h := congrFun (exp_mulVec_of_eigen_real (A := t • Matrix.diagonal d)
      (w := Pi.single i 1) (c := t * d i) (by
        ext k
        by_cases hk : k = i
        · subst hk; simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
        · simp [Matrix.mulVec, dotProduct, Matrix.diagonal, hk, Pi.single_apply])) i
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
    rw [Matrix.diagonal_apply_eq, ← h]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  · have h := congrFun (exp_mulVec_of_eigen_real (A := t • Matrix.diagonal d)
      (w := Pi.single j 1) (c := t * d j) (by
        ext k
        by_cases hk : k = j
        · subst hk; simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
        · simp [Matrix.mulVec, dotProduct, Matrix.diagonal, hk, Pi.single_apply])) i
    simp only [Pi.smul_apply, Pi.single_eq_of_ne hij, smul_eq_mul, mul_zero] at h
    rw [Matrix.diagonal_apply_ne _ hij, ← h]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- (10.15) (p. 315): for `λ ∈ ℂ`, `e^{tλ} → 0` as `t → ∞` iff `Re λ < 0`. -/
theorem tendsto_exp_mul_zero_iff (c : ℂ) :
    Tendsto (fun t : ℝ => Complex.exp (t * c)) atTop (𝓝 0) ↔ c.re < 0 := by
  have hnorm : ∀ t : ℝ, ‖Complex.exp (t * c)‖ = Real.exp (t * c.re) := fun t => by
    rw [Complex.norm_exp]
    simp
  constructor
  · intro h
    by_contra hre
    push Not at hre
    have h1 := (tendsto_zero_iff_norm_tendsto_zero.1 h).eventually (gt_mem_nhds one_pos)
    obtain ⟨t, ht1, ht⟩ := (h1.and (eventually_ge_atTop (0 : ℝ))).exists
    rw [hnorm] at ht1
    have : 1 ≤ Real.exp (t * c.re) := Real.one_le_exp (mul_nonneg ht hre)
    linarith
  · intro hre
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [hnorm]
    exact Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg hre)

/-- `‖e^A‖ ≤ e^{‖A‖}`, from Exercise 10.1.2. -/
theorem norm_exp_le (A : Matrix X X ℝ) : ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  have : CompleteSpace (Matrix X X ℝ) := FiniteDimensional.complete ℝ _
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).tendsto_sum_nat
  exact le_of_tendsto' h.norm fun m => norm_partialSum_exp_le A m

end SargentStachurski.ContinuousTime

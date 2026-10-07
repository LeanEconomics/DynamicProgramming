/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.Semigroups

/-!
# Intensity matrices and Markov semigroups

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.3 (pp. 318–322).

`Q` is an intensity matrix (10.20) if `Q(x, x') ≥ 0` for `x ≠ x'` and every row sums to zero.

* Example 10.1.4.
* **Proposition 10.1.7**: for `P_t = e^{tQ}`, (i) `Q` is an intensity matrix, (ii) every `P_t`,
  `t ≥ 0`, is stochastic, and (iii) the distributions are invariant for `ψ̇ = ψQ`, are equivalent;
  with Exercises 10.1.13 (`P_t 1 = 1`), 10.1.14 (`Q = θ(K − I)` with `K` stochastic), 10.1.15
  (`P_t ≥ 0`), 10.1.16 and 10.1.17 (the converse, by differentiating at `t = 0`).
* Exercise 10.1.18: `(P_h − I)/h` is an intensity matrix; Exercise 10.1.19:
  `P_h(x, x') = hQ(x, x') + o(h)` for `x ≠ x'`.
* The Chapman–Kolmogorov equation (10.29), the Kolmogorov backward and forward equations, and
  **Proposition 10.1.8**: a differentiable `t ↦ P_t` with `P₀ = I` solving either equation is
  `e^{tQ}`.
-/

open Finset Matrix Filter Topology Function Set Asymptotics

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `Q` is an intensity matrix (10.20): nonnegative off the diagonal, with zero row sums. -/
def IsIntensity (Q : Matrix X X ℝ) : Prop :=
  (∀ x x', x ≠ x' → 0 ≤ Q x x') ∧ ∀ x, ∑ x', Q x x' = 0

omit [Fintype X] [DecidableEq X] in
/-- **Example 10.1.4** (p. 319). -/
theorem isIntensity_example :
    IsIntensity (!![-2, 1, 1; 0, -1, 1; 2, 1, -3] : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine ⟨fun x x' hxx' => ?_, fun x => ?_⟩
  · fin_cases x <;> fin_cases x' <;> simp_all
  · fin_cases x <;> simp [Fin.sum_univ_three] <;> norm_num

/-- An entrywise nonnegative matrix has an entrywise nonnegative exponential. -/
theorem exp_nonneg_of_nonneg {M : Matrix X X ℝ} (hM : ∀ x y, 0 ≤ M x y) (x y : X) :
    0 ≤ NormedSpace.exp M x y := by
  have : CompleteSpace (Matrix X X ℝ) := FiniteDimensional.complete ℝ _
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) M).mapL (entryCLM x y)
  exact h.nonneg fun n => mul_nonneg (by positivity) (pow_nonneg_entries hM n x y)

/-- `e^{cI} = e^c I`. -/
theorem exp_smul_one (c : ℝ) :
    NormedSpace.exp (c • (1 : Matrix X X ℝ)) = Real.exp c • (1 : Matrix X X ℝ) := by
  have : CompleteSpace (Matrix X X ℝ) := FiniteDimensional.complete ℝ _
  rw [Algebra.smul_def, mul_one, show NormedSpace.exp (algebraMap ℝ (Matrix X X ℝ) c) =
    algebraMap ℝ _ (NormedSpace.exp c) from (NormedSpace.algebraMap_exp_comm c).symm,
    Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ]

/-- **Exercise 10.1.13** (p. 320): for an intensity matrix, `P_t 1 = 1`. -/
theorem exp_smul_mulVec_one {Q : Matrix X X ℝ} (hQ : IsIntensity Q) (t : ℝ) :
    NormedSpace.exp (t • Q) *ᵥ (fun _ => 1) = fun _ => 1 := by
  have h : (t • Q) *ᵥ (fun _ => (1 : ℝ)) = (0 : ℝ) • fun _ => 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, ← Finset.mul_sum, hQ.2 x]
  rw [exp_mulVec_of_eigen_real h, Real.exp_zero, one_smul]

/-- The `θ` of Exercise 10.1.14: the largest `|Q(x, x)|`. -/
noncomputable def intensityBound [Nonempty X] (Q : Matrix X X ℝ) : ℝ :=
  univ.sup' univ_nonempty fun x => |Q x x|

/-- The stochastic matrix `K = I + Q/θ` of Exercise 10.1.14 (`K = I` if `θ = 0`). -/
noncomputable def intensityJump [Nonempty X] (Q : Matrix X X ℝ) : Matrix X X ℝ :=
  if intensityBound Q = 0 then 1 else 1 + (intensityBound Q)⁻¹ • Q

/-- **Exercise 10.1.14** (p. 320): `K` is stochastic and `Q = θ(K − I)`. -/
theorem intensityJump_spec [Nonempty X] {Q : Matrix X X ℝ} (hQ : IsIntensity Q) :
    IsMarkov (intensityJump Q) ∧ Q = intensityBound Q • (intensityJump Q - 1) := by
  have hθ0 : 0 ≤ intensityBound Q := (abs_nonneg _).trans (Finset.le_sup' (fun x => |Q x x|)
    (mem_univ (Classical.arbitrary X)))
  have hdiag : ∀ x, |Q x x| ≤ intensityBound Q := fun x =>
    Finset.le_sup' (fun x => |Q x x|) (mem_univ x)
  by_cases hθ : intensityBound Q = 0
  · -- every diagonal entry vanishes, so every row vanishes
    have hQ0 : Q = 0 := by
      ext x x'
      have hxx : Q x x = 0 := abs_eq_zero.1 (le_antisymm (hθ ▸ hdiag x) (abs_nonneg _))
      have hrow := hQ.2 x
      rw [← Finset.add_sum_erase _ _ (mem_univ x), hxx, zero_add] at hrow
      by_cases hx : x = x'
      · subst hx
        exact hxx
      · exact le_antisymm ((Finset.sum_eq_zero_iff_of_nonneg fun y hy =>
          hQ.1 x y (Finset.ne_of_mem_erase hy).symm).1 hrow x' (Finset.mem_erase.2
            ⟨Ne.symm hx, mem_univ _⟩)).le (hQ.1 x x' hx)
    have hJ : intensityJump Q = 1 := by simp [intensityJump, hθ]
    rw [hJ, hθ, zero_smul]
    refine ⟨⟨fun x x' => ?_, fun x => ?_⟩, hQ0⟩
    · rw [Matrix.one_apply]
      split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  · have hθpos : 0 < intensityBound Q := lt_of_le_of_ne hθ0 (Ne.symm hθ)
    have hJ : intensityJump Q = 1 + (intensityBound Q)⁻¹ • Q := by simp [intensityJump, hθ]
    rw [hJ]
    refine ⟨⟨fun x x' => ?_, fun x => ?_⟩, ?_⟩
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
      by_cases hx : x = x'
      · subst hx
        simp only [↓reduceIte]
        have h2 : -intensityBound Q ≤ Q x x := by linarith [neg_abs_le (Q x x), hdiag x]
        have : -1 ≤ (intensityBound Q)⁻¹ * Q x x := by
          rw [le_inv_mul_iff₀ hθpos]
          linarith
        linarith
      · simp only [hx, ↓reduceIte, zero_add]
        exact mul_nonneg (inv_nonneg.2 hθ0) (hQ.1 x x' hx)
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hQ.2 x, mul_zero, add_zero]
      simp [Matrix.one_apply]
    · rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hθ, one_smul]

/-- **Exercise 10.1.15** (p. 320): for an intensity matrix, `P_t ≥ 0` for `t ≥ 0`. -/
theorem exp_smul_nonneg [Nonempty X] {Q : Matrix X X ℝ} (hQ : IsIntensity Q) {t : ℝ} (ht : 0 ≤ t)
    (x y : X) : 0 ≤ NormedSpace.exp (t • Q) x y := by
  obtain ⟨hK, hQK⟩ := intensityJump_spec hQ
  set θ := intensityBound Q
  set K := intensityJump Q
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans (Finset.le_sup' (fun x => |Q x x|)
    (mem_univ (Classical.arbitrary X)))
  have hsplit : t • Q = (t * θ) • K + (-(t * θ)) • (1 : Matrix X X ℝ) := by
    rw [hQK]
    module
  have hcomm : Commute ((t * θ) • K) ((-(t * θ)) • (1 : Matrix X X ℝ)) :=
    ((Commute.one_right K).smul_left _).smul_right _
  rw [hsplit, exp_add_eq hcomm, exp_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply,
    smul_eq_mul]
  exact mul_nonneg (Real.exp_pos _).le (exp_nonneg_of_nonneg (fun a b => mul_nonneg
    (mul_nonneg ht hθ0) (hK.nonneg a b)) x y)

/-- **Proposition 10.1.7** (p. 319): for `P_t = e^{tQ}`, the following are equivalent:
(i) `Q` is an intensity matrix; (ii) `P_t` is stochastic for all `t ≥ 0`; (iii) the set of
distributions is invariant for `ψ̇ = ψQ`: `ψ₀ ∈ D(X) ⇒ ψ₀e^{tQ} ∈ D(X)` for all `t ≥ 0`. -/
theorem intensity_tfae [Nonempty X] (Q : Matrix X X ℝ) :
    [IsIntensity Q, ∀ t : ℝ, 0 ≤ t → IsMarkov (NormedSpace.exp (t • Q)),
      ∀ ψ : X → ℝ, IsDistribution ψ → ∀ t : ℝ, 0 ≤ t →
        IsDistribution (ψ ᵥ* NormedSpace.exp (t • Q))].TFAE := by
  tfae_have 1 → 2 := fun hQ t ht => ⟨exp_smul_nonneg hQ ht, fun x => by
    have := congrFun (exp_smul_mulVec_one hQ t) x
    simpa [Matrix.mulVec, dotProduct] using this⟩
  tfae_have 2 → 3 := fun hP ψ hψ t ht => by
    obtain ⟨h0, h1⟩ := hP t ht
    refine ⟨fun x' => sum_nonneg fun x _ => mul_nonneg (hψ.nonneg x) (h0 x x'), ?_⟩
    simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, h1, hψ.sum_eq_one]
  tfae_have 3 → 1 := by
    intro hinv
    -- row `x` of `P_t` is the distribution `δ_x P_t`
    have hrow : ∀ x, ∀ t : ℝ, 0 ≤ t → IsDistribution fun x' => NormedSpace.exp (t • Q) x x' :=
      fun x t ht => by
        have h := hinv (Pi.single x 1) ⟨fun y => by
          by_cases hy : y = x
          · subst hy; simp
          · simp [hy], by simp⟩ t ht
        have e : (Pi.single x 1 ᵥ* NormedSpace.exp (t • Q)) =
            fun x' => NormedSpace.exp (t • Q) x x' := by
          funext x'
          simp [Matrix.vecMul, dotProduct, Pi.single_apply]
        rwa [e] at h
    refine ⟨fun x x' hxx' => ?_, fun x => ?_⟩
    · -- Exercise 10.1.17: a nonnegative function vanishing at `0` has nonnegative right slope
      have hd := hasDerivAt_exp_smul_entry Q 0 x x'
      rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at hd
      refine ge_of_tendsto hd.tendsto_slope_zero_right ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [zero_add, zero_smul, NormedSpace.exp_zero, Matrix.one_apply_ne hxx', sub_zero,
        smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 (le_of_lt ht)) ((hrow x t (le_of_lt ht)).nonneg x')
    · -- Exercise 10.1.16: the row sum is constant, so its derivative vanishes
      have hd := HasDerivAt.fun_sum (u := univ) fun x' _ => hasDerivAt_exp_smul_entry Q 0 x x'
      simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at hd
      refine tendsto_nhds_unique hd.tendsto_slope_zero_right (tendsto_const_nhds.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [zero_add, zero_smul, NormedSpace.exp_zero, (hrow x t (le_of_lt ht)).sum_eq_one]
      simp [Matrix.one_apply]
  tfae_finish

/-- **Exercise 10.1.18** (p. 321): for `h > 0` and `P_h` stochastic, `(P_h − I)/h` is an intensity
matrix. -/
theorem isIntensity_of_isMarkov {P : Matrix X X ℝ} (hP : IsMarkov P) {h : ℝ} (hh : 0 < h) :
    IsIntensity (h⁻¹ • (P - 1)) := by
  refine ⟨fun x x' hxx' => ?_, fun x => ?_⟩
  · simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_ne hxx', sub_zero,
      smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hh.le) (hP.nonneg x x')
  · simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hP.rowsum x]
    rw [Finset.sum_eq_single x (fun y _ hy => by rw [Matrix.one_apply_ne' hy]) (by simp)]
    simp

/-- **Exercise 10.1.19** (p. 321), (10.28): `P_h(x, x') = hQ(x, x') + o(h)` for `x ≠ x'`. -/
theorem exp_smul_entry_isLittleO (Q : Matrix X X ℝ) {x x' : X} (hxx' : x ≠ x') :
    (fun h : ℝ => NormedSpace.exp (h • Q) x x' - h * Q x x') =o[𝓝 0] fun h => h := by
  have hd := hasDerivAt_exp_smul_entry Q 0 x x'
  rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at hd
  have h := hasDerivAt_iff_isLittleO.1 hd
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_apply_ne hxx', sub_zero,
    smul_eq_mul] at h
  exact h.congr_left fun h => by ring

/-- The Chapman–Kolmogorov equation (10.29): `P_{s+t}(x, x') = ∑_z P_s(x, z)P_t(z, x')`. -/
theorem chapman_kolmogorov (Q : Matrix X X ℝ) (s t : ℝ) (x x' : X) :
    NormedSpace.exp ((s + t) • Q) x x' =
      ∑ z, NormedSpace.exp (s • Q) x z * NormedSpace.exp (t • Q) z x' := by
  rw [exp_smul_add, Matrix.mul_apply]

/-- The Kolmogorov backward equation `Ṗ_t = QP_t`, entrywise. -/
theorem kolmogorov_backward (Q : Matrix X X ℝ) (t : ℝ) (x x' : X) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Q) x x') ((Q * NormedSpace.exp (t • Q)) x x') t :=
  hasDerivAt_exp_smul_entry Q t x x'

/-- The Kolmogorov forward equation `Ṗ_t = P_tQ`, entrywise. -/
theorem kolmogorov_forward (Q : Matrix X X ℝ) (t : ℝ) (x x' : X) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Q) x x')
      ((NormedSpace.exp (t • Q) * Q) x x') t := by
  rw [exp_smul_mul_comm]
  exact hasDerivAt_exp_smul_entry Q t x x'

omit [DecidableEq X] in
/-- Product rule for matrix products, entrywise, within a set. -/
theorem hasDerivWithinAt_mul_entry {M N : ℝ → Matrix X X ℝ} {M' N' : Matrix X X ℝ} {s : Set ℝ}
    {t : ℝ} (hM : ∀ x y, HasDerivWithinAt (fun r => M r x y) (M' x y) s t)
    (hN : ∀ x y, HasDerivWithinAt (fun r => N r x y) (N' x y) s t) (x y : X) :
    HasDerivWithinAt (fun r => (M r * N r) x y) ((M' * N t + M t * N') x y) s t := by
  have h := HasDerivWithinAt.fun_sum (u := univ) fun z _ => (hM x z).mul (hN z y)
  simp only [Matrix.mul_apply, Matrix.add_apply]
  convert h using 1
  rw [← Finset.sum_add_distrib]

omit [Fintype X] in
/-- A matrix function with `g₀ = I`, continuous and with zero right derivative on `[0, ∞)`, is
constantly `I` there. -/
theorem eq_one_of_deriv_zero {g : ℝ → Matrix X X ℝ} (hg0 : g 0 = 1)
    (hg : ∀ t, 0 ≤ t → ∀ x y, HasDerivWithinAt (fun r => g r x y) 0 (Ici 0) t) {t : ℝ}
    (ht : 0 ≤ t) : g t = 1 := by
  ext x y
  have hcont : ContinuousOn (fun r => g r x y) (Icc 0 t) := fun r hr =>
    ((hg r hr.1 x y).continuousWithinAt).mono fun s hs => hs.1
  have hc := constant_of_has_deriv_right_zero hcont fun r hr =>
    (hg r hr.1 x y).mono fun s hs => le_trans hr.1 hs
  rw [hc t ⟨ht, le_rfl⟩, hg0]

/-- **Proposition 10.1.8** (p. 322): if `t ↦ P_t` is differentiable on `[0, ∞)` with `P₀ = I` and
satisfies the backward equation `Ṗ_t = QP_t`, then `P_t = e^{tQ}`. -/
theorem eq_exp_of_backward {Q : Matrix X X ℝ} {P : ℝ → Matrix X X ℝ} (hP0 : P 0 = 1)
    (hP : ∀ t, 0 ≤ t → ∀ x y, HasDerivWithinAt (fun s => P s x y) ((Q * P t) x y) (Ici 0) t)
    {t : ℝ} (ht : 0 ≤ t) : P t = NormedSpace.exp (t • Q) := by
  have hg : ∀ r, 0 ≤ r → ∀ x y, HasDerivWithinAt
      (fun s => (NormedSpace.exp ((-s) • Q) * P s) x y) 0 (Ici 0) r := fun r hr x y => by
    have h := hasDerivWithinAt_mul_entry (M' := -(Q * NormedSpace.exp ((-r) • Q)))
      (N' := Q * P r) (fun a b => (hasDerivAt_exp_neg_smul_entry Q r a b).hasDerivWithinAt)
      (hP r hr) x y
    convert h using 1
    rw [Matrix.neg_mul, ← exp_smul_mul_comm, Matrix.mul_assoc, neg_add_cancel, Matrix.zero_apply]
  have h1 := eq_one_of_deriv_zero (g := fun s => NormedSpace.exp ((-s) • Q) * P s)
    (by simp [hP0]) hg ht
  calc P t = NormedSpace.exp (t • Q) * (NormedSpace.exp ((-t) • Q) * P t) := by
        rw [← Matrix.mul_assoc, exp_smul_mul_exp_neg_smul, Matrix.one_mul]
    _ = NormedSpace.exp (t • Q) := by rw [h1, Matrix.mul_one]

/-- **Proposition 10.1.8** (p. 322): the same with the forward equation `Ṗ_t = P_tQ`. -/
theorem eq_exp_of_forward {Q : Matrix X X ℝ} {P : ℝ → Matrix X X ℝ} (hP0 : P 0 = 1)
    (hP : ∀ t, 0 ≤ t → ∀ x y, HasDerivWithinAt (fun s => P s x y) ((P t * Q) x y) (Ici 0) t)
    {t : ℝ} (ht : 0 ≤ t) : P t = NormedSpace.exp (t • Q) := by
  have hg : ∀ r, 0 ≤ r → ∀ x y, HasDerivWithinAt
      (fun s => (P s * NormedSpace.exp ((-s) • Q)) x y) 0 (Ici 0) r := fun r hr x y => by
    have h := hasDerivWithinAt_mul_entry (M' := P r * Q)
      (N' := -(Q * NormedSpace.exp ((-r) • Q))) (hP r hr)
      (fun a b => (hasDerivAt_exp_neg_smul_entry Q r a b).hasDerivWithinAt) x y
    convert h using 1
    rw [Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel, Matrix.zero_apply]
  have h1 := eq_one_of_deriv_zero (g := fun s => P s * NormedSpace.exp ((-s) • Q))
    (by simp [hP0]) hg ht
  have hinv : NormedSpace.exp ((-t) • Q) * NormedSpace.exp (t • Q) = 1 := by
    have := exp_smul_mul_exp_neg_smul Q (-t)
    rwa [neg_neg] at this
  calc P t = (P t * NormedSpace.exp ((-t) • Q)) * NormedSpace.exp (t • Q) := by
        rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = NormedSpace.exp (t • Q) := by rw [h1, Matrix.one_mul]

end SargentStachurski.ContinuousTime

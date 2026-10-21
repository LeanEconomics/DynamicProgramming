/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TopologyContinuity.ModelLinearModels
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Controllability of the linear control model (MT §4.4.2)

Meyn and Tweedie, §4.4.2, pp. 90–91, and the linear algebra of §4.4.3, pp. 92–93, for the linear
control model LCM(F, G), `xₖ₊₁ = F xₖ + G uₖ₊₁`, with `F` an `n × n` and `G` an `n × p` matrix.

* `ctrbMap F G k`: the linear map `(u₁, …, uₖ) ↦ Σᵢ F^{k−1−i} G uᵢ₊₁`, and `ctrbMatrix F G k`
  the controllability matrix `C_k = [F^{k−1}G | ⋯ | FG | G]` (4.13), with
  `range_ctrbMatrix` (same range) and `rank_ctrbMatrix_eq_iff` (`rank C_k = n` iff the map is
  onto).
* `lcmTrajectory_eq_ctrbMap` (4.14): `x_k = F^k x₀ + C_k (u₁, …, u_k)`.
* `IsCtrbRank F G` (LCM3): `rank C_n = n`.
* **Proposition 4.4.1** (`proposition_4_4_1`, p. 91): the rank condition implies
  controllability, with every state reached from every initial condition in `n` steps.
* Cayley–Hamilton (p. 90): `range_ctrbMap_le_n`, the range of `C_k` is contained in that of
  `C_n` for every `k`; `isControllable_iff_rank` and `isControllable_iff_exists_rank`: `(F, G)`
  is controllable iff `rank C_n = n` iff `rank C_k = n` for some `k`.
* **Proposition 4.4.2** (`proposition_4_4_2`, p. 91): the state space form of AR(k) is
  controllable; `companion_pow_firstUnit_triangular` is the triangular structure of its
  controllability matrix, and `companion_eta_rec` the recursion `η_j = Σᵢ αᵢ η_{j−i}`.
* `gramian F G k = Σ_{i<k} F^i G Gᵀ (F^i)ᵀ` (the variance (4.16)), `gramian_eq` (`Σ_k = C_k C_kᵀ`),
  `rank_gramian` (`rank Σ_k = rank C_k`) and `isControllable_iff_gramian` (p. 93): `Σ_k` has full
  rank for some `k` iff `(F, G)` is controllable, and then for `k = n`.
* `ctrbSubspace_absorbing_step` (p. 93): the range `X₀` of `C_n` is invariant under every step
  `x ↦ F x + G w`.

**Corrections.** The controllability Gramian (4.17), `Σ_{i ≥ 0} F^i G Gᵀ (F^i)ᵀ`, need not
converge: for `F = G = 1` on `ℝ¹` every term is `1` (`gramian_series_counterexample`). Its role
is played by the finite sums `Σ_k`, which have full rank for some `k` iff `(F, G)` is
controllable (`isControllable_iff_gramian`).
-/

namespace MeynTweedie.TopologyContinuity

open Matrix
open scoped Matrix

variable {n p : ℕ}

/-- The linear map `(u₁, …, u_k) ↦ Σᵢ F^{k−1−i} G uᵢ₊₁` of (4.14). -/
noncomputable def ctrbMap (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    (Fin k → Fin p → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  ∑ i : Fin k, (F ^ (k - 1 - (i : ℕ)) * G).mulVecLin ∘ₗ LinearMap.proj i

/-- `C_k u = Σᵢ F^{k−1−i} G uᵢ`. -/
theorem ctrbMap_apply (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (u : Fin k → Fin p → ℝ) :
    ctrbMap F G k u = ∑ i : Fin k, (F ^ (k - 1 - (i : ℕ)) * G) *ᵥ u i := by
  simp [ctrbMap]

/-- The controllability matrix `C_k = [F^{k−1}G | ⋯ | FG | G]` (4.13), MT p. 90: column `(i, j)`
is column `j` of `F^{k−1−i} G`. -/
def ctrbMatrix (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin k × Fin p) ℝ :=
  Matrix.of fun r ij => (F ^ (k - 1 - (ij.1 : ℕ)) * G) r ij.2

/-- `C_k v` is `ctrbMap` applied to the blocks of `v`. -/
theorem ctrbMatrix_mulVec (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (v : Fin k × Fin p → ℝ) : ctrbMatrix F G k *ᵥ v = ctrbMap F G k fun i j => v (i, j) := by
  ext r
  rw [ctrbMap_apply, Finset.sum_apply]
  simp only [mulVec, dotProduct, ctrbMatrix, of_apply, Fintype.sum_prod_type]

/-- The controllability matrix and `ctrbMap` have the same range. -/
theorem range_ctrbMatrix (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    LinearMap.range (ctrbMatrix F G k).mulVecLin = LinearMap.range (ctrbMap F G k) := by
  ext x
  simp only [LinearMap.mem_range, mulVecLin_apply]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, (ctrbMatrix_mulVec F G k v).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨fun ij => u ij.1 ij.2, ctrbMatrix_mulVec F G k _⟩

/-- `rank C_k = n` iff every state is of the form `C_k u`. -/
theorem rank_ctrbMatrix_eq_iff (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) : (ctrbMatrix F G k).rank = n ↔ LinearMap.range (ctrbMap F G k) = ⊤ := by
  rw [Matrix.rank, range_ctrbMatrix]
  constructor
  · intro h
    exact Submodule.eq_top_of_finrank_eq (by rw [h, Module.finrank_fin_fun])
  · intro h
    rw [h, finrank_top, Module.finrank_fin_fun]

/-- (4.14), MT p. 91: `x_k = F^k x₀ + C_k (u₁, …, u_k)`. -/
theorem lcmTrajectory_eq_ctrbMap (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) (x₀ : Fin n → ℝ) (u : Fin k → Fin p → ℝ) :
    lcmTrajectory F G k x₀ u = (F ^ k) *ᵥ x₀ + ctrbMap F G k u := by
  rw [lcmTrajectory_eq, ctrbMap_apply]

/-- The rank condition (LCM3), MT p. 90: the controllability matrix `C_n` has rank `n`. -/
def IsCtrbRank (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) : Prop :=
  (ctrbMatrix F G n).rank = n

/-- If `C_k` is onto, every state is reached from every initial condition in `k` steps. -/
theorem reach_of_range_eq_top {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    {k : ℕ} (h : LinearMap.range (ctrbMap F G k) = ⊤) (x₀ x : Fin n → ℝ) :
    ∃ u : Fin k → Fin p → ℝ, lcmTrajectory F G k x₀ u = x := by
  obtain ⟨u, hu⟩ := LinearMap.range_eq_top.1 h (x - (F ^ k) *ᵥ x₀)
  exact ⟨u, by rw [lcmTrajectory_eq_ctrbMap, hu, add_sub_cancel]⟩

/-- **Proposition 4.4.1** (MT p. 91): if `(F, G)` satisfies the rank condition (LCM3), LCM(F, G)
is controllable; indeed every state is reached from every initial condition in `n` steps. -/
theorem proposition_4_4_1 {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    (h : IsCtrbRank F G) :
    IsControllable F G ∧ ∀ x₀ x, ∃ u : Fin n → Fin p → ℝ, lcmTrajectory F G n x₀ u = x := by
  have h' := (rank_ctrbMatrix_eq_iff F G n).1 h
  exact ⟨fun x₀ x => ⟨n, reach_of_range_eq_top h' x₀ x⟩, reach_of_range_eq_top h'⟩

/-! ### Cayley–Hamilton -/

/-- `F^j G v` lies in the range of `C_k` for `j < k`. -/
theorem pow_mul_mulVec_mem_range (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    {j k : ℕ} (hj : j < k) (v : Fin p → ℝ) :
    (F ^ j * G) *ᵥ v ∈ LinearMap.range (ctrbMap F G k) := by
  refine ⟨Pi.single (⟨k - 1 - j, by omega⟩ : Fin k) v, ?_⟩
  rw [ctrbMap_apply, Finset.sum_eq_single (⟨k - 1 - j, by omega⟩ : Fin k)]
  · have hj' : k - 1 - (k - 1 - j) = j := by omega
    rw [Pi.single_eq_same, Fin.val_mk, hj']
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, mulVec_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Cayley–Hamilton: `F^n = −Σ_{i<n} cᵢ Fⁱ`, with `cᵢ` the coefficients of the characteristic
polynomial. -/
theorem pow_dim_eq_sum (F : Matrix (Fin n) (Fin n) ℝ) :
    F ^ n = -∑ i ∈ Finset.range n, F.charpoly.coeff i • F ^ i := by
  have h := Matrix.aeval_self_charpoly F
  rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Finset.sum_range_succ] at h
  have hc : F.charpoly.coeff n = 1 := by
    have := (Matrix.charpoly_monic F).coeff_natDegree
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [hc, one_smul] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Cayley–Hamilton (MT p. 90): `F^j G v` lies in the range of `C_n` for every `j`. -/
theorem pow_mul_mulVec_mem_range_n (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (j : ℕ) (v : Fin p → ℝ) : (F ^ j * G) *ᵥ v ∈ LinearMap.range (ctrbMap F G n) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases lt_or_ge j n with hj | hj
    · exact pow_mul_mulVec_mem_range F G hj v
    · have hFj : F ^ j = -∑ i ∈ Finset.range n, F.charpoly.coeff i • F ^ (j - n + i) := by
        rw [show j = (j - n) + n by omega, pow_add, pow_dim_eq_sum, mul_neg, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, ← pow_add]
        congr 2
        omega
      rw [hFj, Matrix.neg_mul, neg_mulVec, Matrix.sum_mul, sum_mulVec]
      refine neg_mem (Submodule.sum_mem _ fun i hi => ?_)
      rw [smul_mul, smul_mulVec]
      exact Submodule.smul_mem _ _ (ih (j - n + i) (by rw [Finset.mem_range] at hi; omega))

/-- Cayley–Hamilton (MT p. 90): the range of `C_k` is contained in the range of `C_n`. -/
theorem range_ctrbMap_le_n (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) : LinearMap.range (ctrbMap F G k) ≤ LinearMap.range (ctrbMap F G n) := by
  rintro x ⟨u, rfl⟩
  rw [ctrbMap_apply]
  exact Submodule.sum_mem _ fun i _ => pow_mul_mulVec_mem_range_n F G _ _

/-- The ranges of the `C_k` increase with `k`. -/
theorem range_ctrbMap_mono (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    {k m : ℕ} (hkm : k ≤ m) :
    LinearMap.range (ctrbMap F G k) ≤ LinearMap.range (ctrbMap F G m) := by
  rintro x ⟨u, rfl⟩
  rw [ctrbMap_apply]
  exact Submodule.sum_mem _ fun i _ => pow_mul_mulVec_mem_range F G (by omega) _

/-- MT p. 90: `(F, G)` is controllable iff it satisfies the rank condition (LCM3). -/
theorem isControllable_iff_rank (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    IsControllable F G ↔ IsCtrbRank F G := by
  refine ⟨fun h => (rank_ctrbMatrix_eq_iff F G n).2 ?_, fun h => (proposition_4_4_1 h).1⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨m, u, hu⟩ := h 0 x
  rw [lcmTrajectory_eq_ctrbMap, mulVec_zero, zero_add] at hu
  exact range_ctrbMap_le_n F G m ⟨u, hu⟩

/-- MT pp. 90–91: `(F, G)` is controllable iff `rank C_k = n` for some `k`. -/
theorem isControllable_iff_exists_rank (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) :
    IsControllable F G ↔ ∃ k, (ctrbMatrix F G k).rank = n := by
  rw [isControllable_iff_rank]
  refine ⟨fun h => ⟨n, h⟩, fun ⟨k, hk⟩ => ?_⟩
  rw [IsCtrbRank, rank_ctrbMatrix_eq_iff]
  rw [rank_ctrbMatrix_eq_iff] at hk
  exact eq_top_iff.2 (hk.symm.le.trans (range_ctrbMap_le_n F G k))

/-- For a controllable pair, `C_k` is onto for every `k ≥ n`. -/
theorem range_ctrbMap_eq_top {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    (h : IsControllable F G) {k : ℕ} (hk : n ≤ k) : LinearMap.range (ctrbMap F G k) = ⊤ := by
  have h' := (rank_ctrbMatrix_eq_iff F G n).1 ((isControllable_iff_rank F G).1 h)
  exact eq_top_iff.2 (h'.symm.le.trans (range_ctrbMap_mono F G hk))

/-! ### The autoregression AR(k) (Proposition 4.4.2) -/

/-- The input `G = (1, 0, …, 0)ᵀ` maps `v` to `v₀ e₀`. -/
theorem firstUnit_mulVec {k : ℕ} (v : Fin 1 → ℝ) (i : Fin k) :
    (firstUnit k *ᵥ v) i = if (i : ℕ) = 0 then v 0 else 0 := by
  simp [firstUnit, mulVec, dotProduct]

/-- Below the first row the companion matrix shifts down: `(F w)ᵢ = wᵢ₋₁` for `i ≥ 1`. -/
theorem companion_mulVec_of_ne_zero {k : ℕ} (α : Fin k → ℝ) (w : Fin k → ℝ) (i : Fin k)
    (hi : (i : ℕ) ≠ 0) :
    (companion α *ᵥ w) i = w ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ := by
  simp only [mulVec, dotProduct, companion, of_apply, hi, ite_false]
  rw [Finset.sum_eq_single (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin k)]
  · rw [ite_eq_left (by simp only; omega), one_mul]
  · intro j _ hj
    rw [ite_eq_right (fun hij => hj (Fin.ext (by simp only; omega))), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The first row of the companion matrix: `(F w)₀ = Σⱼ αⱼ wⱼ`. -/
theorem companion_mulVec_zero {k : ℕ} (α : Fin k → ℝ) (w : Fin k → ℝ) (i : Fin k)
    (hi : (i : ℕ) = 0) : (companion α *ᵥ w) i = ∑ j, α j * w j := by
  simp [mulVec, dotProduct, companion, hi]

/-- The vector `e₀ = G 1`. -/
def firstVec (k : ℕ) : Fin k → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0

/-- **The triangular structure** of the controllability matrix of AR(k) (MT p. 91):
`(Fʲ e₀)ᵢ = 0` for `i > j` and `(Fʲ e₀)ⱼ = 1`. -/
theorem companion_pow_firstUnit_triangular {k : ℕ} (α : Fin k → ℝ) (j : ℕ) (i : Fin k) :
    (j < i → (companion α ^ j *ᵥ firstVec k) i = 0) ∧
      ((i : ℕ) = j → (companion α ^ j *ᵥ firstVec k) i = 1) := by
  induction j generalizing i with
  | zero =>
    simp only [pow_zero, one_mulVec, firstVec]
    refine ⟨fun h => ?_, fun h => by simp [h]⟩
    simp only [ite_eq_right_iff]
    intro h'
    omega
  | succ j ih =>
    have hi0 : ∀ hi : (i : ℕ) ≠ 0, (companion α ^ (j + 1) *ᵥ firstVec k) i =
        (companion α ^ j *ᵥ firstVec k) ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ := fun hi => by
      rw [pow_succ', ← mulVec_mulVec, companion_mulVec_of_ne_zero α _ i hi]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hi0 (by omega)]
      exact (ih _).1 (by simp only; omega)
    · rw [hi0 (by omega)]
      exact (ih _).2 (by simp only; omega)

/-- The entries `η_m = (F^m e₀)₀` of the controllability matrix of AR(k) (MT p. 91). -/
noncomputable def companionEta {k : ℕ} (α : Fin k → ℝ) (m : ℕ) (h : 0 < k) : ℝ :=
  (companion α ^ m *ᵥ firstVec k) ⟨0, h⟩

/-- MT p. 91: `(F^j e₀)ᵢ = η_{j−i}` for `i ≤ j`, and the recursion
`η_{m+1} = Σᵢ αᵢ (F^m e₀)ᵢ`, i.e. `η_j = Σ_{i=1}^k αᵢ η_{j−i}` with `η_l = 0` for `l < 0`. -/
theorem companion_eta_rec {k : ℕ} (α : Fin k → ℝ) (h : 0 < k) :
    (∀ (j : ℕ) (i : Fin k), (i : ℕ) ≤ j →
      (companion α ^ j *ᵥ firstVec k) i = companionEta α (j - i) h) ∧
    (∀ m, companionEta α (m + 1) h = ∑ i : Fin k, α i *
      (if (i : ℕ) ≤ m then companionEta α (m - i) h else 0)) := by
  have hentry : ∀ (j : ℕ) (i : Fin k), (i : ℕ) ≤ j →
      (companion α ^ j *ᵥ firstVec k) i = companionEta α (j - i) h := by
    intro j
    induction j with
    | zero =>
      intro i hi
      have : i = ⟨0, h⟩ := Fin.ext (Nat.le_zero.1 hi)
      subst this
      rfl
    | succ j ih =>
      intro i hi
      by_cases hi0 : (i : ℕ) = 0
      · have : i = ⟨0, h⟩ := Fin.ext hi0
        subst this
        simp [companionEta]
      · rw [pow_succ', ← mulVec_mulVec, companion_mulVec_of_ne_zero α _ i hi0,
          ih _ (by simp only; omega)]
        congr 1
        simp only
        omega
  refine ⟨hentry, fun m => ?_⟩
  rw [companionEta, pow_succ', ← mulVec_mulVec, companion_mulVec_zero α _ _ rfl]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  split_ifs with hi
  · exact hentry m i hi
  · exact (companion_pow_firstUnit_triangular α m i).1 (by omega)

/-- **Proposition 4.4.2** (MT p. 91): the linear control model of the AR(k) state space form
(2.1), with the companion matrix `F` and `G = (1, 0, …, 0)ᵀ`, is controllable. -/
theorem proposition_4_4_2 {k : ℕ} (α : Fin k → ℝ) :
    IsCtrbRank (companion α) (firstUnit k) ∧ IsControllable (companion α) (firstUnit k) := by
  have hR : LinearMap.range (ctrbMap (companion α) (firstUnit k) k) = ⊤ := by
    set R := LinearMap.range (ctrbMap (companion α) (firstUnit k) k)
    have hpow : ∀ j < k, companion α ^ j *ᵥ firstVec k ∈ R := fun j hj => by
      have := pow_mul_mulVec_mem_range (companion α) (firstUnit k) hj (fun _ => 1)
      rw [← mulVec_mulVec] at this
      convert this using 2
      ext i
      rw [firstUnit_mulVec]
      rfl
    have hsm : ∀ (l : Fin k) (c : ℝ), Pi.single l c = c • Pi.single l (1 : ℝ) := fun l c => by
      ext j
      by_cases hj : j = l
      · subst hj
        simp
      · simp [hj]
    have hsingle : ∀ m : ℕ, ∀ i : Fin k, (i : ℕ) = m → Pi.single i (1 : ℝ) ∈ R := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro i hi
        have hv : companion α ^ m *ᵥ firstVec k ∈ R := hpow m (hi ▸ i.isLt)
        set w : Fin k → ℝ := companion α ^ m *ᵥ firstVec k - Pi.single i 1 with hwdef
        have hw : w ∈ R := by
          rw [← Finset.univ_sum_single w]
          refine Submodule.sum_mem _ fun l _ => ?_
          by_cases hl : (l : ℕ) < m
          · rw [hsm]
            exact Submodule.smul_mem _ _ (ih l hl l rfl)
          · have hw0 : w l = 0 := by
              rw [hwdef, Pi.sub_apply]
              rcases lt_or_eq_of_le (not_lt.1 hl) with h | h
              · have hli : l ≠ i := fun hli => by rw [hli] at h; omega
                rw [(companion_pow_firstUnit_triangular α m l).1 h, Pi.single_eq_of_ne hli,
                  sub_zero]
              · have hli : l = i := Fin.ext (by omega)
                rw [(companion_pow_firstUnit_triangular α m l).2 h.symm, hli, Pi.single_eq_same,
                  sub_self]
            rw [hw0, Pi.single_zero]
            exact zero_mem _
        have : Pi.single i (1 : ℝ) = companion α ^ m *ᵥ firstVec k - w := by
          rw [hwdef, sub_sub_cancel]
        rw [this]
        exact sub_mem hv hw
    refine eq_top_iff.2 fun x _ => ?_
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (hsingle l l rfl)
  have h : IsCtrbRank (companion α) (firstUnit k) := (rank_ctrbMatrix_eq_iff _ _ k).2 hR
  exact ⟨h, (proposition_4_4_1 h).1⟩

/-! ### The controllability Gramian and the controllable subspace (§4.4.3) -/

/-- The variance (4.16) of `X_k` under (LSS3), `Σ_k = Σ_{i<k} F^i G Gᵀ (F^i)ᵀ` (MT p. 93). -/
def gramian (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ i ∈ Finset.range k, F ^ i * G * Gᵀ * (F ^ i)ᵀ

/-- `Σ_k = C_k C_kᵀ`. -/
theorem gramian_eq (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    gramian F G k = ctrbMatrix F G k * (ctrbMatrix F G k)ᵀ := by
  have h1 : ctrbMatrix F G k * (ctrbMatrix F G k)ᵀ =
      ∑ i : Fin k, (F ^ (k - 1 - (i : ℕ)) * G) * (F ^ (k - 1 - (i : ℕ)) * G)ᵀ := by
    ext r s
    simp only [mul_apply, transpose_apply, ctrbMatrix, of_apply, Fintype.sum_prod_type,
      Matrix.sum_apply]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => (F ^ (k - 1 - i) * G) * (F ^ (k - 1 - i) * G)ᵀ),
    ← Finset.sum_range_reflect, gramian]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show k - 1 - (k - 1 - i) = i by omega, transpose_mul, ← Matrix.mul_assoc]

/-- `rank Σ_k = rank C_k`. -/
theorem rank_gramian (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    (gramian F G k).rank = (ctrbMatrix F G k).rank := by
  rw [gramian_eq, rank_self_mul_transpose]

/-- MT p. 93: the variance `Σ_k` of `X_k` has full rank `n` for some `k` iff `(F, G)` is
controllable, and then it has full rank for `k = n`. -/
theorem isControllable_iff_gramian (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) :
    (IsControllable F G ↔ ∃ k, (gramian F G k).rank = n) ∧
      (IsControllable F G → (gramian F G n).rank = n) := by
  simp_rw [rank_gramian]
  exact ⟨isControllable_iff_exists_rank F G, fun h => (isControllable_iff_rank F G).1 h⟩

/-- MT p. 93: the range `X₀` of `C_n` is invariant under every step: if `x ∈ X₀` then
`F x + G w ∈ X₀`. -/
theorem ctrbSubspace_absorbing_step (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    {x : Fin n → ℝ} (hx : x ∈ LinearMap.range (ctrbMap F G n)) (w : Fin p → ℝ) :
    F *ᵥ x + G *ᵥ w ∈ LinearMap.range (ctrbMap F G n) := by
  obtain ⟨u, rfl⟩ := hx
  refine add_mem ?_ ?_
  · rw [ctrbMap_apply, mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']
    exact pow_mul_mulVec_mem_range_n F G _ _
  · have := pow_mul_mulVec_mem_range_n F G 0 w
    rwa [pow_zero, Matrix.one_mul] at this

/-- **Correction to (4.17)** (MT p. 93): the Gramian series need not converge; for `F = G = 1`
on `ℝ¹` its terms are all `1`. -/
theorem gramian_series_counterexample :
    ¬ Summable fun i : ℕ => (1 : Matrix (Fin 1) (Fin 1) ℝ) ^ i * 1 *
      (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * ((1 : Matrix (Fin 1) (Fin 1) ℝ) ^ i)ᵀ := by
  simp only [one_pow, transpose_one, Matrix.mul_one]
  rw [summable_const_iff]
  exact one_ne_zero

end MeynTweedie.TopologyContinuity

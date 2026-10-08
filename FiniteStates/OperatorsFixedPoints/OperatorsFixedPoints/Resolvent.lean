/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OperatorsFixedPoints.SpectralRadius
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The resolvent series, entrywise

For a square matrix `M` over `ℝ` or `ℂ` and a scalar `z` with `|z|` larger than
a bound `r` on the growth of the entries of `Mᵏ`, the series
`∑ₖ z^{−(k+1)} Mᵏ` converges entry by entry to a two-sided inverse of `zI − M`.
This is the Neumann series of Vol. 1, Theorem 1.2.1, written out at the level
of entries so that no topology on the matrix space is needed: partial sums
telescope, `(zI − M) ∑_{k<K} z^{−(k+1)} Mᵏ = I − z^{−K} Mᴷ`, and the correction
term vanishes entrywise.

The Perron–Frobenius argument of `PerronFrobenius` applies this to a
nonnegative real matrix `A` at a real `t > ρ(A)`, where the entries of the
resolvent are nonnegative, and to its complexification at a complex `z` with
`|z| = t`, where they are dominated by the real ones.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.OperatorsFixedPoints

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- The partial sums `∑_{k<K} z^{−(k+1)} Mᵏ` of the resolvent series. -/
def resPartial (M : Matrix (Fin n) (Fin n) 𝕜) (z : 𝕜) (K : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  ∑ k ∈ range K, (z⁻¹) ^ (k + 1) • M ^ k

/-- The resolvent series, entry by entry: `R(z)ᵢⱼ = ∑ₖ z^{−(k+1)} (Mᵏ)ᵢⱼ`. -/
noncomputable def res (M : Matrix (Fin n) (Fin n) 𝕜) (z : 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => ∑' k : ℕ, (z⁻¹) ^ (k + 1) * (M ^ k) i j

theorem res_apply (M : Matrix (Fin n) (Fin n) 𝕜) (z : 𝕜) (i j : Fin n) :
    res M z i j = ∑' k : ℕ, (z⁻¹) ^ (k + 1) * (M ^ k) i j := rfl

/-- Telescoping: `(zI − M) ∑_{k<K} z^{−(k+1)} Mᵏ = I − z^{−K} Mᴷ`. -/
theorem smul_one_sub_mul_resPartial (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} (hz : z ≠ 0) (K : ℕ) :
    (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) * resPartial M z K = 1 - (z⁻¹) ^ K • M ^ K := by
  induction K with
  | zero => simp [resPartial]
  | succ K ih =>
    have hc : (z⁻¹) ^ (K + 1) • (z • M ^ K) = (z⁻¹) ^ K • M ^ K := by
      rw [smul_smul, pow_succ, mul_assoc, inv_mul_cancel₀ hz, mul_one]
    rw [resPartial, sum_range_succ, ← resPartial, mul_add, ih, Matrix.mul_smul, sub_mul,
      Matrix.smul_mul, one_mul, ← pow_succ', smul_sub, hc]
    abel

/-- Telescoping on the other side: `(∑_{k<K} z^{−(k+1)} Mᵏ)(zI − M) = I − z^{−K} Mᴷ`. -/
theorem resPartial_mul_smul_one_sub (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} (hz : z ≠ 0) (K : ℕ) :
    resPartial M z K * (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) = 1 - (z⁻¹) ^ K • M ^ K := by
  induction K with
  | zero => simp [resPartial]
  | succ K ih =>
    have hc : (z⁻¹) ^ (K + 1) • (z • M ^ K) = (z⁻¹) ^ K • M ^ K := by
      rw [smul_smul, pow_succ, mul_assoc, inv_mul_cancel₀ hz, mul_one]
    rw [resPartial, sum_range_succ, ← resPartial, add_mul, ih, Matrix.smul_mul, mul_sub,
      Matrix.mul_smul, mul_one, ← pow_succ, smul_sub, hc]
    abel

/-- The entry of a partial sum is the partial sum of the entries. -/
theorem resPartial_apply (M : Matrix (Fin n) (Fin n) 𝕜) (z : 𝕜) (K : ℕ) (i j : Fin n) :
    resPartial M z K i j = ∑ k ∈ range K, (z⁻¹) ^ (k + 1) * (M ^ k) i j := by
  simp [resPartial, Matrix.sum_apply]

/-- Under an eventual bound `‖(Mᵏ)ᵢⱼ‖ ≤ rᵏ` with `r < |z|`, the entry series is summable. -/
theorem summable_res_entry (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (i j : Fin n) (hM : ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    Summable fun k : ℕ => (z⁻¹) ^ (k + 1) * (M ^ k) i j := by
  have hz0 : 0 < ‖z‖ := hr.trans_lt hz
  have hq : r / ‖z‖ < 1 := (div_lt_one hz0).2 hz
  have hq0 : 0 ≤ r / ‖z‖ := div_nonneg hr hz0.le
  refine Summable.of_norm_bounded_eventually_nat
    ((summable_geometric_of_lt_one hq0 hq).mul_left ‖z‖⁻¹) (hM.mono fun k hk => ?_)
  rw [norm_mul, norm_pow, norm_inv, div_pow, pow_succ, ← div_eq_mul_inv]
  calc ‖z‖⁻¹ ^ k * ‖z‖⁻¹ * ‖(M ^ k) i j‖ ≤ ‖z‖⁻¹ ^ k * ‖z‖⁻¹ * r ^ k := by gcongr
    _ = ‖z‖⁻¹ * (r ^ k / ‖z‖ ^ k) := by
        rw [div_eq_mul_inv, ← inv_pow]
        ring

/-- The partial sums converge entrywise to the resolvent series. -/
theorem tendsto_resPartial_apply (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (i j : Fin n) (hM : ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    Tendsto (fun K => resPartial M z K i j) atTop (𝓝 (res M z i j)) := by
  simp only [resPartial_apply, res_apply]
  exact (summable_res_entry M hr hz i j hM).hasSum.tendsto_sum_nat

/-- The correction term `z^{−K} (Mᴷ)ᵢⱼ` vanishes. -/
theorem tendsto_inv_pow_mul_apply (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (i j : Fin n) (hM : ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    Tendsto (fun K : ℕ => (z⁻¹) ^ K * (M ^ K) i j) atTop (𝓝 0) := by
  have hz0 : 0 < ‖z‖ := hr.trans_lt hz
  have hq : r / ‖z‖ < 1 := (div_lt_one hz0).2 hz
  have hq0 : 0 ≤ r / ‖z‖ := div_nonneg hr hz0.le
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (hM.mono fun K hK => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq)
  rw [norm_mul, norm_pow, norm_inv, div_pow, div_eq_mul_inv, ← inv_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right hK (by positivity)

/-- The resolvent series is a right inverse: `(zI − M) R(z) = I`. -/
theorem smul_one_sub_mul_res (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) * res M z = 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact absurd hz (not_lt.2 hr)
  ext i j
  -- the partial products converge to both sides
  have h1 : Tendsto (fun K => ((z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) * resPartial M z K) i j)
      atTop (𝓝 (((z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) * res M z) i j)) := by
    simp only [Matrix.mul_apply]
    exact tendsto_finsetSum _ fun l _ =>
      tendsto_const_nhds.mul (tendsto_resPartial_apply M hr hz l j (hM l j))
  have h2 : Tendsto (fun K => ((z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) * resPartial M z K) i j)
      atTop (𝓝 ((1 : Matrix (Fin n) (Fin n) 𝕜) i j)) := by
    simp only [smul_one_sub_mul_resPartial M hz0, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    simpa using tendsto_const_nhds.sub (tendsto_inv_pow_mul_apply M hr hz i j (hM i j))
  exact tendsto_nhds_unique h1 h2

/-- The resolvent series is a left inverse: `R(z)(zI − M) = I`. -/
theorem res_mul_smul_one_sub (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    res M z * (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) = 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact absurd hz (not_lt.2 hr)
  ext i j
  have h1 : Tendsto (fun K => (resPartial M z K * (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M)) i j)
      atTop (𝓝 ((res M z * (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M)) i j)) := by
    simp only [Matrix.mul_apply]
    exact tendsto_finsetSum _ fun l _ =>
      (tendsto_resPartial_apply M hr hz i l (hM i l)).mul tendsto_const_nhds
  have h2 : Tendsto (fun K => (resPartial M z K * (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M)) i j)
      atTop (𝓝 ((1 : Matrix (Fin n) (Fin n) 𝕜) i j)) := by
    simp only [resPartial_mul_smul_one_sub M hz0, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    simpa using tendsto_const_nhds.sub (tendsto_inv_pow_mul_apply M hr hz i j (hM i j))
  exact tendsto_nhds_unique h1 h2

/-! ### The real resolvent of a nonnegative matrix -/

/-- For `A ≥ 0` and `t > 0`, the entries of the resolvent series are nonnegative. -/
theorem res_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j) {t : ℝ} (ht : 0 < t)
    (i j : Fin n) : 0 ≤ res A t i j :=
  tsum_nonneg fun k => mul_nonneg (pow_nonneg (inv_nonneg.2 ht.le) _) (pow_nonneg_entries hA k i j)

/-- For `A ≥ 0` and `t > 0`, each entry of the resolvent dominates the first term `1/t` of the
diagonal series: `R(t)ᵢᵢ ≥ 1/t`. -/
theorem inv_le_res_diag [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j) {t r : ℝ}
    (hr : 0 ≤ r) (ht : r < t) (hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(A ^ k) i j‖ ≤ r ^ k) (i : Fin n) :
    t⁻¹ ≤ res A t i i := by
  have ht0 : 0 < t := hr.trans_lt ht
  have hs := summable_res_entry A hr (by rwa [Real.norm_eq_abs, abs_of_pos ht0]) i i (hM i i)
  rw [res_apply]
  have h0 : (t⁻¹) ^ (0 + 1) * (A ^ 0) i i = t⁻¹ := by simp
  calc t⁻¹ = (t⁻¹) ^ (0 + 1) * (A ^ 0) i i := h0.symm
    _ ≤ ∑' k : ℕ, (t⁻¹) ^ (k + 1) * (A ^ k) i i :=
        hs.le_tsum 0 fun k _ =>
          mul_nonneg (pow_nonneg (inv_nonneg.2 ht0.le) _) (pow_nonneg_entries hA k i i)

end SargentStachurski.OperatorsFixedPoints

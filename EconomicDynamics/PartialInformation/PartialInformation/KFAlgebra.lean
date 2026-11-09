/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.KFMoments
import PartialInformation.LSRiccati

/-!
# The Kalman filter: the covariance algebra of one updating step

Miao, §10.1.1, pp. 329–333: the matrix algebra of one step of the Kalman filter. Fix the date-`t`
matrices `G = G_t`, `D = D_t`, the predicted covariance `P = Σ_{t|t−1}` and the cross covariance
`Cℓ = E[(x_t − x̂_{t|t−1})ε_t']` (by (10.9) this is the shock loading of `ε_t` in `x_t`; see
`KFFilter`). Then

* (10.8) `Ω = GPG' + DD' + GCℓD' + DCℓ'G'` (`kf_Om`), the innovation covariance;
* `M = PG' + CℓD'` (`kf_Mx`), the covariance of the state and the innovation (p. 332);
* (10.10) `K = MΩ⁻¹` (`kf_gain`), the Kalman gain;
* (10.11) `Σ(K) = (I − KG)P(I − KG)' + KDD'K' − (I − KG)CℓD'K' − KDCℓ'(I − KG)'`
  (`kf_joseph`), the covariance of `x_t − x̂_{t|t−1} − Ka_t` for an arbitrary gain `K`;
* `Σ_{t|t} = (I − KG)P − KDCℓ'` (`kf_filtCov`), the book's simplified form at the Kalman gain.

Main results:

* `kf_joseph_expand`: `Σ(K) = P − KM' − MK' + KΩK'`;
* `kf_joseph_complete`: completing the square,
  `Σ(K) = P − MΩ⁻¹M' + (K − K*)Ω(K − K*)'` with `K* = MΩ⁻¹`;
* `eq_10_10`: if `Ω > 0`, the Kalman gain minimises `Σ(K)` in the Loewner order and
  `tr Σ(K)` (the book's criterion `E(x_t − x̂_{t|t})'(x_t − x̂_{t|t})`), uniquely;
  `eq_10_10_foc`: the first-order condition of p. 331 (`kf_trace_perturb` is the expansion of
  `tr Σ(K + sΔ)` whose linear term is the derivative), `KΩ = M`;
* `eq_10_11_gain`: at the Kalman gain (10.11) reduces to `Σ_{t|t} = (I − KG)P − KDCℓ'`;
* `kf_riccati_pred`: the Riccati form of `Σ_{t+1|t} = AΣ_{t|t}A' + CC'` (p. 333).

Correction (p. 331): the printed first-order condition
`0 = −2(ΣG' + DC') + 2K(GΣG' + DD' + GCD' + DC'G)` has the non-conformable terms `DC'` and
`DC'G`; the derivative is `−2(ΣG' + CD') + 2K(GΣG' + DD' + GCD' + DC'G')` (`kf_trace_perturb`).
-/

open Matrix

open scoped MatrixOrder

namespace Miao.PartialInformation

variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y]

/-- (10.8) (Miao, p. 330): the innovation covariance `Ω = GPG' + DD' + GCℓD' + DCℓ'G'`. -/
def kf_Om (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ) (P : Matrix X X ℝ) :
    Matrix Y Y ℝ :=
  G * P * Gᵀ + D * Dᵀ + G * Cl * Dᵀ + D * Clᵀ * Gᵀ

/-- Miao, p. 332: `Cov(x_t, y_t | y^{t−1}) = PG' + CℓD'`. -/
def kf_Mx (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ) (P : Matrix X X ℝ) :
    Matrix X Y ℝ :=
  P * Gᵀ + Cl * Dᵀ

/-- (10.10) (Miao, p. 330): the Kalman gain `K = (PG' + CℓD')Ω⁻¹`. -/
noncomputable def kf_gain (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ)
    (P : Matrix X X ℝ) : Matrix X Y ℝ :=
  kf_Mx G D Cl P * (kf_Om G D Cl P)⁻¹

/-- (10.11) (Miao, p. 331): the error covariance for an arbitrary gain `K`. -/
def kf_joseph (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ) (P : Matrix X X ℝ)
    (K : Matrix X Y ℝ) : Matrix X X ℝ :=
  (1 - K * G) * P * (1 - K * G)ᵀ + K * D * Dᵀ * Kᵀ - (1 - K * G) * Cl * Dᵀ * Kᵀ -
    K * D * Clᵀ * (1 - K * G)ᵀ

/-- Miao, p. 332: `Σ_{t|t} = (I − KG)Σ_{t|t−1} − KDCℓ'` at the Kalman gain. -/
noncomputable def kf_filtCov (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ)
    (P : Matrix X X ℝ) : Matrix X X ℝ :=
  (1 - kf_gain G D Cl P * G) * P - kf_gain G D Cl P * D * Clᵀ

variable (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ) {P : Matrix X X ℝ}

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- `Ω' = Ω` for symmetric `P`. -/
theorem kf_Om_transpose (hP : Pᵀ = P) : (kf_Om G D Cl P)ᵀ = kf_Om G D Cl P := by
  simp only [kf_Om, transpose_add, transpose_mul, transpose_transpose, hP, Matrix.mul_assoc]
  abel

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- `M' = GP + DCℓ'` for symmetric `P`. -/
theorem kf_Mx_transpose (hP : Pᵀ = P) : (kf_Mx G D Cl P)ᵀ = G * P + D * Clᵀ := by
  simp only [kf_Mx, transpose_add, transpose_mul, transpose_transpose, hP]

omit [DecidableEq Y] in
/-- (10.11) expanded: `Σ(K) = P − KM' − MK' + KΩK'`. -/
theorem kf_joseph_expand (hP : Pᵀ = P) (K : Matrix X Y ℝ) :
    kf_joseph G D Cl P K = P - K * (kf_Mx G D Cl P)ᵀ - kf_Mx G D Cl P * Kᵀ +
      K * kf_Om G D Cl P * Kᵀ := by
  rw [kf_Mx_transpose G D Cl hP]
  simp only [kf_joseph, kf_Mx, kf_Om, transpose_sub, transpose_one, transpose_mul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc]
  abel

/-- Completing the square in (10.11): `Σ(K) = P − MΩ⁻¹M' + (K − K*)Ω(K − K*)'`, `K* = MΩ⁻¹`. -/
theorem kf_joseph_complete (hP : Pᵀ = P) (hu : IsUnit (kf_Om G D Cl P).det)
    (K : Matrix X Y ℝ) :
    kf_joseph G D Cl P K = P - kf_Mx G D Cl P * (kf_Om G D Cl P)⁻¹ * (kf_Mx G D Cl P)ᵀ +
      (K - kf_gain G D Cl P) * kf_Om G D Cl P * (K - kf_gain G D Cl P)ᵀ := by
  rw [kf_joseph_expand G D Cl hP]
  have hs : ((kf_Om G D Cl P)⁻¹)ᵀ = (kf_Om G D Cl P)⁻¹ := by
    rw [transpose_nonsing_inv, kf_Om_transpose G D Cl hP]
  simp only [kf_gain, transpose_sub, transpose_mul, hs, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu, nonsing_inv_mul_cancel_left _ _ hu]
  abel

/-- (10.11) at the Kalman gain (Miao, p. 332): `Σ(K*) = (I − K*G)P − K*DCℓ'`. -/
theorem eq_10_11_gain (hP : Pᵀ = P) (hu : IsUnit (kf_Om G D Cl P).det) :
    kf_joseph G D Cl P (kf_gain G D Cl P) = kf_filtCov G D Cl P := by
  rw [kf_joseph_complete G D Cl hP hu]
  simp only [sub_self, Matrix.zero_mul, add_zero]
  simp only [kf_filtCov, kf_gain, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [kf_Mx_transpose G D Cl hP]
  simp only [Matrix.mul_add]
  abel

/-- `Σ_{t|t} = P − MΩ⁻¹M'`. -/
theorem kf_filtCov_eq (hP : Pᵀ = P) (hu : IsUnit (kf_Om G D Cl P).det) :
    kf_filtCov G D Cl P =
      P - kf_Mx G D Cl P * (kf_Om G D Cl P)⁻¹ * (kf_Mx G D Cl P)ᵀ := by
  rw [← eq_10_11_gain G D Cl hP hu, kf_joseph_complete G D Cl hP hu]
  simp only [sub_self, Matrix.zero_mul, add_zero]

omit [Fintype X] [DecidableEq X] [DecidableEq Y] in
/-- `(NΩN')ᵢᵢ = Nᵢ'ΩNᵢ` (row `i` of `N`). -/
theorem kf_diag_sandwich {Z : Type*} (N : Matrix X Z ℝ) [Fintype Z] (W : Matrix Z Z ℝ) (i : X) :
    (N * W * Nᵀ) i i = N i ⬝ᵥ (W *ᵥ N i) := by
  simp only [mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

omit [DecidableEq X] [DecidableEq Y] in
/-- `tr(NΩN') ≥ 0` for `Ω > 0`, with equality iff `N = 0`. -/
theorem kf_trace_sandwich {Z : Type*} [Fintype Z] {W : Matrix Z Z ℝ} (hW : W.PosDef)
    (N : Matrix X Z ℝ) : 0 ≤ trace (N * W * Nᵀ) ∧ (trace (N * W * Nᵀ) = 0 ↔ N = 0) := by
  have hW' := SS.LQProblem.posDef_iff_real.1 hW
  have hnn : ∀ i, 0 ≤ N i ⬝ᵥ (W *ᵥ N i) := by
    intro i
    rcases eq_or_ne (N i) 0 with h | h
    · simp [h]
    · exact (hW'.2 h).le
  have htr : trace (N * W * Nᵀ) = ∑ i, N i ⬝ᵥ (W *ᵥ N i) := by
    simp only [trace, Matrix.diag, kf_diag_sandwich]
  rw [htr]
  refine ⟨Finset.sum_nonneg fun i _ => hnn i, ⟨fun h => ?_, fun h => ?_⟩⟩
  swap
  · have h0 : ∀ i, N i = 0 := fun i => by rw [h]; rfl
    simp [h0]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i] at h
  funext i
  by_contra hne
  have := hW'.2 hne
  rw [h i (Finset.mem_univ i)] at this
  exact lt_irrefl _ this

/-- **(10.10)** (Miao, p. 330): if `Ω > 0`, the Kalman gain `K* = (PG' + CℓD')Ω⁻¹` minimises the
error covariance (10.11) over all gains, in the Loewner order and in trace (the book's criterion
`E(x_t − x̂_{t|t})'(x_t − x̂_{t|t}) = tr Σ_{t|t}`), and is the unique trace minimiser. -/
theorem eq_10_10 (hP : Pᵀ = P) (hΩ : (kf_Om G D Cl P).PosDef) (K : Matrix X Y ℝ) :
    kf_filtCov G D Cl P ≤ kf_joseph G D Cl P K ∧
      trace (kf_filtCov G D Cl P) ≤ trace (kf_joseph G D Cl P K) ∧
      (trace (kf_joseph G D Cl P K) = trace (kf_filtCov G D Cl P) ↔ K = kf_gain G D Cl P) := by
  have hu : IsUnit (kf_Om G D Cl P).det := (isUnit_iff_isUnit_det _).1 hΩ.isUnit
  have hJ := kf_joseph_complete G D Cl hP hu K
  rw [kf_filtCov_eq G D Cl hP hu]
  set N := K - kf_gain G D Cl P
  have hpsd : (N * kf_Om G D Cl P * Nᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      hΩ.posSemidef.mul_mul_conjTranspose_same N
  obtain ⟨h0, hiff⟩ := kf_trace_sandwich hΩ N
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.le_iff, hJ, add_sub_cancel_left]
    exact hpsd
  · rw [hJ, trace_add]
    linarith
  · rw [hJ, trace_add, add_eq_left, hiff, sub_eq_zero]

omit [DecidableEq Y] in
/-- The first-order expansion behind the trace condition of p. 331:
`tr Σ(K + sΔ) = tr Σ(K) + 2s tr(Δ(ΩK' − M')) + s² tr(ΔΩΔ')`; the derivative in `K` is
`2(KΩ − M)` (= `−2(PG' + CℓD') + 2KΩ`). -/
theorem kf_trace_perturb (hP : Pᵀ = P) (K Δ : Matrix X Y ℝ) (s : ℝ) :
    trace (kf_joseph G D Cl P (K + s • Δ)) = trace (kf_joseph G D Cl P K) +
      2 * s * trace (Δ * (kf_Om G D Cl P * Kᵀ - (kf_Mx G D Cl P)ᵀ)) +
      s ^ 2 * trace (Δ * kf_Om G D Cl P * Δᵀ) := by
  rw [kf_joseph_expand G D Cl hP, kf_joseph_expand G D Cl hP]
  set Om := kf_Om G D Cl P
  set M := kf_Mx G D Cl P
  have hOm : Omᵀ = Om := kf_Om_transpose G D Cl hP
  have t1 : trace (M * Δᵀ) = trace (Δ * Mᵀ) := by
    rw [← trace_transpose, transpose_mul, transpose_transpose]
  have t2 : trace (K * Om * Δᵀ) = trace (Δ * (Om * Kᵀ)) := by
    rw [← trace_transpose, transpose_mul, transpose_mul, transpose_transpose, hOm]
  have t3 : trace (Δ * Om * Kᵀ) = trace (Δ * (Om * Kᵀ)) := by rw [Matrix.mul_assoc]
  simp only [transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, trace_add, trace_sub, trace_smul, smul_eq_mul, smul_add, Matrix.mul_sub,
    trace_sub] at *
  rw [t1, t2, t3]
  ring

omit [DecidableEq X] [DecidableEq Y] in
/-- The first-order condition of p. 331: the linear term of `tr Σ(K + sΔ)` vanishes for every
direction `Δ` iff `KΩ = PG' + CℓD'`; for invertible `Ω` this is (10.10), `K = MΩ⁻¹`. -/
theorem eq_10_10_foc (hP : Pᵀ = P) (K : Matrix X Y ℝ) :
    (∀ Δ : Matrix X Y ℝ, trace (Δ * (kf_Om G D Cl P * Kᵀ - (kf_Mx G D Cl P)ᵀ)) = 0) ↔
      K * kf_Om G D Cl P = kf_Mx G D Cl P := by
  set Om := kf_Om G D Cl P
  set M := kf_Mx G D Cl P
  have hOm : Omᵀ = Om := kf_Om_transpose G D Cl hP
  have key : K * Om = M ↔ Om * Kᵀ - Mᵀ = 0 := by
    rw [sub_eq_zero]
    constructor
    · intro h
      rw [← hOm, ← transpose_mul, h]
    · intro h
      rw [← transpose_transpose (K * Om), transpose_mul, hOm, h, transpose_transpose]
  rw [key]
  constructor
  · intro h
    have h0 := h (Om * Kᵀ - Mᵀ)ᵀ
    have := (trace_mul_conjTranspose_self_eq_zero_iff (A := (Om * Kᵀ - Mᵀ)ᵀ)).1
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at this
    exact transpose_eq_zero.1 (this h0)
  · intro h Δ
    rw [h, Matrix.mul_zero, trace_zero]

/-- The Riccati form of `Σ_{t+1|t} = AΣ_{t|t}A' + CC'` (Miao, p. 333):
`AΣ_{t|t}A' + CC' = APA' + CC' − A(GP + DCℓ')'Ω⁻¹(GP + DCℓ')A'`. -/
theorem kf_riccati_pred {E' : Type*} [Fintype E'] (A : Matrix X X ℝ) (C : Matrix X E' ℝ)
    (hP : Pᵀ = P) (hu : IsUnit (kf_Om G D Cl P).det) :
    A * kf_filtCov G D Cl P * Aᵀ + C * Cᵀ = A * P * Aᵀ + C * Cᵀ -
      A * (G * P + D * Clᵀ)ᵀ * (kf_Om G D Cl P)⁻¹ * (G * P + D * Clᵀ) * Aᵀ := by
  rw [kf_filtCov_eq G D Cl hP hu, ← kf_Mx_transpose G D Cl hP, transpose_transpose]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

end Miao.PartialInformation

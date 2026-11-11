/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.VARMoments
import PartialInformation.SSLQAlgebra

/-!
# Second moments of square-integrable random vectors

Miao, §10.1.1, pp. 327–333. The Kalman filter of §10.1.1 is proved here in its
linear-projection (second-moment) reading: every computation of the text that takes an
expectation `E[vw']` of products of the state, the shocks, the estimation errors and the
innovations is an identity between the second-moment matrices `var_mom μ v w = E[vw']` (from the
copied Chapter 2 module `VARMoments`) of square-integrable random vectors.

This module provides the calculus of these matrices:

* `kf_L2 μ v`: every coordinate of `v : Ω → I → ℝ` is in `L²(μ)`; it is preserved by linear
  maps `kf_app M v = Mv`, sums, differences and (for finite `μ`) constants (`kf_L2_app`,
  `kf_L2_add`, `kf_L2_sub`, `kf_L2_const`, `kf_L2_zero`);
* bilinearity: `E[(Mv)w'] = M E[vw']`, `E[v(Nw)'] = E[vw']N'`, additivity in both arguments
  (`kf_mom_app_left`, `kf_mom_app_right`, `kf_mom_add_left`, `kf_mom_add_right`,
  `kf_mom_sub_left`, `kf_mom_sub_right`, `kf_mom_lin2`, `kf_mom_lin_sub`), symmetry
  `E[wv'] = (E[vw'])'` (`kf_mom_transpose`), and `E[vv'] ≥ 0` (`kf_mom_self_psd`);
* means: `kf_mean μ v = E v`, linear (`kf_mean_app`, `kf_mean_add`, `kf_mean_sub`,
  `kf_mean_const`), and `E[c w'] = c (Ew)'`, `E[v c'] = (Ev)c'` for a constant `c`
  (`kf_mom_const_left`, `kf_mom_const_right`);
* `kf_app` is additive and composes (`kf_app_add`, `kf_app_sub`, `kf_app_app`,
  `kf_app_sub_mat`, `kf_app_zero_mat`).
-/

open MeasureTheory Matrix

namespace Miao.PartialInformation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)

/-- Square integrability of a random vector: every coordinate is in `L²(μ)`. -/
def kf_L2 {I : Type*} (v : Ω → I → ℝ) : Prop := ∀ i, MemLp (fun ω => v ω i) 2 μ

/-- The random vector `ω ↦ Mv(ω)`. -/
def kf_app {I J : Type*} [Fintype J] (M : Matrix I J ℝ) (v : Ω → J → ℝ) : Ω → I → ℝ :=
  fun ω => M *ᵥ v ω

/-- The mean vector `Ev`. -/
noncomputable def kf_mean {I : Type*} (v : Ω → I → ℝ) : I → ℝ := fun i => ∫ ω, v ω i ∂μ

variable {μ}
variable {I J K : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
/-- Linear images of square-integrable vectors are square integrable. -/
theorem kf_L2_app {v : Ω → J → ℝ} (hv : kf_L2 μ v) (M : Matrix I J ℝ) :
    kf_L2 μ (kf_app M v) := by
  intro i
  unfold kf_app
  have : (fun ω => (M *ᵥ v ω) i) = fun ω => ∑ j, M i j * v ω j := by
    funext ω
    simp [mulVec, dotProduct]
  rw [this]
  exact memLp_finsetSum _ fun j _ => (hv j).const_mul _

omit [Fintype I] [Fintype J] in
theorem kf_L2_add {v w : Ω → I → ℝ} (hv : kf_L2 μ v) (hw : kf_L2 μ w) : kf_L2 μ (v + w) :=
  fun i => (hv i).add (hw i)

omit [Fintype I] [Fintype J] in
theorem kf_L2_sub {v w : Ω → I → ℝ} (hv : kf_L2 μ v) (hw : kf_L2 μ w) : kf_L2 μ (v - w) :=
  fun i => (hv i).sub (hw i)

omit [Fintype I] [Fintype J] in
theorem kf_L2_const [IsFiniteMeasure μ] (c : I → ℝ) : kf_L2 μ (fun _ : Ω => c) :=
  fun i => memLp_const (c i)

omit [Fintype I] [Fintype J] in
theorem kf_L2_zero : kf_L2 μ (0 : Ω → I → ℝ) := fun _ => MemLp.zero

omit [Fintype I] [Fintype J] in
/-- `E[wv'] = (E[vw'])'`. -/
theorem kf_mom_transpose (v : Ω → I → ℝ) (w : Ω → J → ℝ) :
    var_mom μ w v = (var_mom μ v w)ᵀ := by
  ext i j
  simp only [var_mom, of_apply, transpose_apply, mul_comm]

omit [Fintype I] in
/-- `E[(Mv)w'] = M E[vw']`. -/
theorem kf_mom_app_left {v : Ω → J → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v) (hw : kf_L2 μ w)
    (M : Matrix I J ℝ) : var_mom μ (kf_app M v) w = M * var_mom μ v w := by
  ext i k
  simp only [kf_app, var_mom, of_apply, mul_apply]
  have := var_integral_sum_mul (μ := μ) (M i) (f := fun j ω => v ω j) hv (hw k)
  simpa [mulVec, dotProduct] using this

omit [Fintype I] in
/-- `E[w(Mv)'] = E[wv']M'`. -/
theorem kf_mom_app_right {v : Ω → J → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v) (hw : kf_L2 μ w)
    (M : Matrix I J ℝ) : var_mom μ w (kf_app M v) = var_mom μ w v * Mᵀ := by
  rw [kf_mom_transpose, kf_mom_app_left hv hw, transpose_mul, ← kf_mom_transpose]

omit [Fintype I] [Fintype J] in
theorem kf_mom_add_left {v v' : Ω → I → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v) (hv' : kf_L2 μ v')
    (hw : kf_L2 μ w) : var_mom μ (v + v') w = var_mom μ v w + var_mom μ v' w := by
  ext i k
  simp only [var_mom, of_apply, Pi.add_apply, add_mul, Matrix.add_apply]
  exact integral_add ((hv i).integrable_mul (hw k)) ((hv' i).integrable_mul (hw k))

omit [Fintype I] [Fintype J] in
theorem kf_mom_sub_left {v v' : Ω → I → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v) (hv' : kf_L2 μ v')
    (hw : kf_L2 μ w) : var_mom μ (v - v') w = var_mom μ v w - var_mom μ v' w := by
  ext i k
  simp only [var_mom, of_apply, Pi.sub_apply, sub_mul, Matrix.sub_apply]
  exact integral_sub ((hv i).integrable_mul (hw k)) ((hv' i).integrable_mul (hw k))

omit [Fintype I] [Fintype J] in
theorem kf_mom_add_right {v v' : Ω → I → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v)
    (hv' : kf_L2 μ v') (hw : kf_L2 μ w) :
    var_mom μ w (v + v') = var_mom μ w v + var_mom μ w v' := by
  rw [kf_mom_transpose, kf_mom_add_left hv hv' hw, transpose_add, ← kf_mom_transpose,
    ← kf_mom_transpose]

omit [Fintype I] [Fintype J] in
theorem kf_mom_sub_right {v v' : Ω → I → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v)
    (hv' : kf_L2 μ v') (hw : kf_L2 μ w) :
    var_mom μ w (v - v') = var_mom μ w v - var_mom μ w v' := by
  rw [kf_mom_transpose, kf_mom_sub_left hv hv' hw, transpose_sub, ← kf_mom_transpose,
    ← kf_mom_transpose]

omit [Fintype I] [Fintype J] in
/-- `E[c w'] = c (Ew)'` for a constant vector `c`. -/
theorem kf_mom_const_left (c : I → ℝ) (w : Ω → K → ℝ) :
    var_mom μ (fun _ => c) w = Matrix.of fun i k => c i * kf_mean μ w k := by
  ext i k
  simp only [var_mom, of_apply, kf_mean, integral_const_mul]

omit [Fintype I] in
/-- `E(Mv) = M Ev`. -/
theorem kf_mean_app {v : Ω → J → ℝ} (hv : kf_L2 μ v) [IsFiniteMeasure μ]
    (M : Matrix I J ℝ) : kf_mean μ (kf_app M v) = M *ᵥ kf_mean μ v := by
  funext i
  simp only [kf_app, kf_mean, mulVec, dotProduct]
  rw [integral_finsetSum _ fun j _ => ((hv j).integrable one_le_two).const_mul _]
  simp only [integral_const_mul]

omit [Fintype I] [Fintype J] in
theorem kf_mean_add {v w : Ω → I → ℝ} [IsFiniteMeasure μ] (hv : kf_L2 μ v) (hw : kf_L2 μ w) :
    kf_mean μ (v + w) = kf_mean μ v + kf_mean μ w := by
  funext i
  exact integral_add ((hv i).integrable one_le_two) ((hw i).integrable one_le_two)

omit [Fintype I] [Fintype J] in
theorem kf_mean_sub {v w : Ω → I → ℝ} [IsFiniteMeasure μ] (hv : kf_L2 μ v) (hw : kf_L2 μ w) :
    kf_mean μ (v - w) = kf_mean μ v - kf_mean μ w := by
  funext i
  exact integral_sub ((hv i).integrable one_le_two) ((hw i).integrable one_le_two)

omit [Fintype I] in
theorem kf_app_add (M : Matrix I J ℝ) (v w : Ω → J → ℝ) :
    kf_app M (v + w) = kf_app M v + kf_app M w := by
  funext ω
  simp [kf_app, mulVec_add]

omit [Fintype I] in
theorem kf_app_sub (M : Matrix I J ℝ) (v w : Ω → J → ℝ) :
    kf_app M (v - w) = kf_app M v - kf_app M w := by
  funext ω
  simp [kf_app, mulVec_sub]

omit [Fintype I] in
theorem kf_app_app [Fintype K] (M : Matrix I J ℝ) (N : Matrix J K ℝ) (v : Ω → K → ℝ) :
    kf_app M (kf_app N v) = kf_app (M * N) v := by
  funext ω
  simp [kf_app, mulVec_mulVec]

omit [Fintype I] in
theorem kf_app_zero_mat (v : Ω → J → ℝ) : kf_app (0 : Matrix I J ℝ) v = 0 := by
  funext ω
  simp [kf_app]

omit [Fintype I] in
theorem kf_app_sub_mat (M N : Matrix I J ℝ) (v : Ω → J → ℝ) :
    kf_app (M - N) v = kf_app M v - kf_app N v := by
  funext ω
  simp [kf_app, sub_mulVec]

omit [Fintype I] [Fintype J] in
/-- `E[v c'] = (Ev) c'` for a constant vector `c`. -/
theorem kf_mom_const_right (v : Ω → I → ℝ) (c : K → ℝ) :
    var_mom μ v (fun _ => c) = Matrix.of fun i k => kf_mean μ v i * c k := by
  ext i k
  simp only [var_mom, of_apply, kf_mean, integral_mul_const]

omit [Fintype I] [Fintype J] in
theorem kf_mean_const [IsProbabilityMeasure μ] (c : I → ℝ) : kf_mean μ (fun _ : Ω => c) = c := by
  funext i
  simp [kf_mean]

omit [Fintype I] [Fintype J] in
/-- `E[(Ge + Dc)w'] = G E[ew'] + D E[cw']`. -/
theorem kf_mom_lin2 {L : Type*} [Fintype K] [Fintype L] {e : Ω → K → ℝ} {c : Ω → L → ℝ}
    {Z : Type*} {w : Ω → Z → ℝ} (he : kf_L2 μ e) (hc : kf_L2 μ c) (hw : kf_L2 μ w)
    (G : Matrix I K ℝ) (D : Matrix I L ℝ) :
    var_mom μ (kf_app G e + kf_app D c) w = G * var_mom μ e w + D * var_mom μ c w := by
  rw [kf_mom_add_left (kf_L2_app he G) (kf_L2_app hc D) hw, kf_mom_app_left he hw,
    kf_mom_app_left hc hw]

omit [Fintype I] in
/-- `E[(e − Ka)w'] = E[ew'] − K E[aw']`. -/
theorem kf_mom_lin_sub {e : Ω → I → ℝ} {a : Ω → J → ℝ} {Z : Type*} {w : Ω → Z → ℝ}
    (he : kf_L2 μ e) (ha : kf_L2 μ a) (hw : kf_L2 μ w) (K : Matrix I J ℝ) :
    var_mom μ (e - kf_app K a) w = var_mom μ e w - K * var_mom μ a w := by
  rw [kf_mom_sub_left he (kf_L2_app ha K) hw, kf_mom_app_left ha hw]

omit [Fintype I] [Fintype J] in
/-- A second-moment matrix `E[vv']` is positive semidefinite. -/
theorem kf_mom_self_psd [Finite I] {v : Ω → I → ℝ} (hv : kf_L2 μ v) :
    (var_mom μ v v).PosSemidef := by
  have := Fintype.ofFinite I
  refine SS.LQProblem.posSemidef_iff_real.2 ⟨by rw [← kf_mom_transpose], fun z => ?_⟩
  set M : Matrix Unit I ℝ := Matrix.of fun _ i => z i
  have h := kf_mom_app_right hv (kf_L2_app hv M) M
  rw [kf_mom_app_left hv hv M] at h
  have h1 := congrFun (congrFun h ()) ()
  have hq : (M * var_mom μ v v * Mᵀ) () () = z ⬝ᵥ (var_mom μ v v *ᵥ z) := by
    simp only [M, mul_apply, transpose_apply, of_apply, dotProduct, mulVec, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [← hq, ← h1]
  exact integral_nonneg fun ω => mul_self_nonneg _

end Miao.PartialInformation

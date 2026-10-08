/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PreludeExamples.MarkovOperator

/-!
# Affine maps `v ↦ r + βLv` and the Neumann series

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Theorem A.4.10 and Corollary A.4.11
(pp. 367–368), in the form Chapter 1 uses them: (1.3), (1.17) and (1.44).

An operator `L` on `bX` is *Markov-like* when it maps `bX` into itself, is linear and order
preserving there, and satisfies `|v| ≤ M ⟹ |Lv| ≤ M` (so `‖L‖ ≤ 1`). Markov operators of
stochastic kernels are Markov-like. For `r ∈ bX` and `β ∈ [0, 1)` the map `v ↦ r + βLv` is a
`β`-contraction on `bX`, hence globally stable, and its fixed point is the Neumann series
`∑ₜ βᵗLᵗr = (I − βL)⁻¹r`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Function

namespace SargentStachurski.PreludeExamples

variable {X : Type*} [MeasurableSpace X]

/-- A linear, order preserving operator on `bX` of norm at most one. -/
structure IsMarkovLike (L : (X → ℝ) → X → ℝ) : Prop where
  mapsTo : MapsTo L (bX X) (bX X)
  add : ∀ v ∈ bX X, ∀ w ∈ bX X, L (v + w) = L v + L w
  smul : ∀ a : ℝ, ∀ v ∈ bX X, L (a • v) = a • L v
  mono : ∀ v ∈ bX X, ∀ w ∈ bX X, v ≤ w → L v ≤ L w
  abs_le : ∀ v ∈ bX X, ∀ M : ℝ, (∀ x, |v x| ≤ M) → ∀ x, |L v x| ≤ M

/-- The Markov operator of a stochastic kernel is Markov-like (§A.5.4). -/
theorem isMarkovLike_markovOp (P : Kernel X X) [IsMarkovKernel P] :
    IsMarkovLike (markovOp P) :=
  ⟨fun _ h => markovOp_mem_bX P h, fun _ hv _ hw => markovOp_add P hv hw,
    fun a v _ => markovOp_smul P a v, fun _ hv _ hw h => markovOp_mono P hv hw h,
    fun _ _ _ hM => abs_markovOp_le P hM⟩

namespace IsMarkovLike

variable {L : (X → ℝ) → X → ℝ} (hL : IsMarkovLike L)
include hL

theorem sub {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) : L (v - w) = L v - L w := by
  have hnw : (-1 : ℝ) • w ∈ bX X := by
    obtain ⟨M, hM⟩ := hw.2
    exact ⟨hw.1.const_smul _, M, fun x => by simpa using hM x⟩
  have := hL.add v hv _ hnw
  rw [hL.smul _ w hw] at this
  simpa [sub_eq_add_neg] using this

theorem abs_sub_le {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) {c : ℝ}
    (h : ∀ x, |v x - w x| ≤ c) (x : X) : |L v x - L w x| ≤ c := by
  have hvw : v - w ∈ bX X := ⟨hv.1.sub hw.1, hv.2.sub hw.2⟩
  have := hL.abs_le _ hvw c h x
  rwa [hL.sub hv hw] at this

theorem iterate_mem {r : X → ℝ} (hr : r ∈ bX X) (t : ℕ) : L^[t] r ∈ bX X :=
  hL.mapsTo.iterate t hr

theorem abs_iterate_le {r : X → ℝ} (hr : r ∈ bX X) {M : ℝ} (hM : ∀ x, |r x| ≤ M) (t : ℕ)
    (x : X) : |L^[t] r x| ≤ M := by
  induction t generalizing x with
  | zero => exact hM x
  | succ t ih =>
    rw [iterate_succ_apply']
    exact hL.abs_le _ (hL.iterate_mem hr t) M ih x

end IsMarkovLike

/-- The affine map `v ↦ r + βLv`. -/
def affineOp (r : X → ℝ) (β : ℝ) (L : (X → ℝ) → X → ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => r x + β * L v x

variable {L : (X → ℝ) → X → ℝ} {r : X → ℝ} {β : ℝ}

theorem affineOp_mapsTo (hL : IsMarkovLike L) (hr : r ∈ bX X) (hβ0 : 0 ≤ β) :
    MapsTo (affineOp r β L) (bX X) (bX X) := by
  intro v hv
  obtain ⟨hm, N, hN⟩ := hL.mapsTo hv
  obtain ⟨M, hM⟩ := hr.2
  refine ⟨hr.1.add (measurable_const.mul hm), M + β * N, fun x => ?_⟩
  refine (abs_add_le _ _).trans (add_le_add (hM x) ?_)
  rw [abs_mul, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (hN x) hβ0

theorem affineOp_mono (hL : IsMarkovLike L) (hβ0 : 0 ≤ β) {v w : X → ℝ} (hv : v ∈ bX X)
    (hw : w ∈ bX X) (h : v ≤ w) : affineOp r β L v ≤ affineOp r β L w := fun x =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (hL.mono v hv w hw h x) hβ0)

theorem affineOp_contraction (hL : IsMarkovLike L) (hβ0 : 0 ≤ β) :
    IsSupContraction (bX X) (affineOp r β L) β := by
  intro v hv w hw c h x
  simp only [affineOp, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (hL.abs_sub_le hv hw h x) hβ0

/-- Corollary A.4.11: `v ↦ r + βLv` is globally stable on `bX`. -/
theorem affineOp_globallyStable (hL : IsMarkovLike L) (hr : r ∈ bX X) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    ∃ u ∈ bX X, affineOp r β L u = u ∧ (∀ w ∈ bX X, affineOp r β L w = w → w = u) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => (affineOp r β L)^[n] v) u atTop :=
  (affineOp_contraction hL hβ0).globallyStable hβ0 hβ1 (fun _ h => h.2) isUniformlyClosed_bX
    (affineOp_mapsTo hL hr hβ0) ⟨_, const_mem_bX 0⟩

/-- The `n`-th iterate of `v ↦ r + βLv` from `0` is the partial Neumann sum `∑_{t<n} βᵗLᵗr`. -/
theorem affineOp_iterate_zero (hL : IsMarkovLike L) (hr : r ∈ bX X) (n : ℕ) :
    (affineOp r β L)^[n] (fun _ => 0) = fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x := by
  have hterm : ∀ t, β ^ t • L^[t] r ∈ bX X := fun t => by
    obtain ⟨M, hM⟩ := (hL.iterate_mem hr t).2
    refine ⟨(hL.iterate_mem hr t).1.const_smul _, |β ^ t| * M, fun x => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
  have hsplit : ∀ n, (fun x => ∑ t ∈ Finset.range (n + 1), β ^ t * L^[t] r x) =
      (fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x) + β ^ n • L^[n] r := by
    intro n; funext x; simp [Finset.sum_range_succ]
  have hmem : ∀ n, (fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x) ∈ bX X := by
    intro n
    induction n with
    | zero => simpa using const_mem_bX (X := X) 0
    | succ n ih =>
      rw [hsplit]
      exact ⟨ih.1.add (hterm n).1, ih.2.add (hterm n).2⟩
  -- `L` passes through the partial sums
  have hsumL : ∀ n, L (fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x) =
      fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t + 1] r x := by
    intro n
    induction n with
    | zero =>
      have := hL.smul 0 (fun _ => (0 : ℝ)) (const_mem_bX 0)
      simp only [zero_smul] at this
      simp only [Finset.range_zero, Finset.sum_empty]
      exact this
    | succ n ih =>
      rw [hsplit, hL.add _ (hmem n) _ (hterm n), hL.smul _ _ (hL.iterate_mem hr n), ih]
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_range_succ,
        iterate_succ_apply']
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    funext x
    change r x + β * L (fun y => ∑ t ∈ Finset.range n, β ^ t * L^[t] r y) x = _
    rw [hsumL, Finset.sum_range_succ', Finset.mul_sum, pow_zero, one_mul, iterate_zero_apply,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_succ]
    ring

/-- **The Neumann series** (Theorem A.4.10, as in (1.3), (1.17), (1.44)): the fixed point of
`v ↦ r + βLv` in `bX` is `∑ₜ βᵗLᵗr = (I − βL)⁻¹r`. -/
theorem affineOp_hasSum (hL : IsMarkovLike L) (hr : r ∈ bX X) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u : X → ℝ} (hu : u ∈ bX X) (hfix : affineOp r β L u = u) (x : X) :
    HasSum (fun t => β ^ t * L^[t] r x) (u x) := by
  obtain ⟨M, hM⟩ := hr.2
  have hsum : Summable fun t => β ^ t * L^[t] r x :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one hβ0 hβ1 |>.mul_left M) fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hL.abs_iterate_le hr hM t x) (pow_nonneg hβ0 t)
  obtain ⟨u', -, -, huniq, hlim⟩ := affineOp_globallyStable hL hr hβ0 hβ1
  have hu' := huniq u hu hfix
  have hlimx := (hlim _ (const_mem_bX 0)).tendsto_at x
  simp only [affineOp_iterate_zero hL hr] at hlimx
  rw [← hu'] at hlimx
  exact (tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlimx) ▸ hsum.hasSum

end SargentStachurski.PreludeExamples

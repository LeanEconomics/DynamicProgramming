/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.CUDDefs
import MarkovDriving.DrivingMC
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw

/-! # CUD sequences exist: an i.i.d. uniform sequence is CUD almost surely

The Chentsov theorems (`ChentsovConsistency`) assume a CUD driving sequence. This module shows
the assumption is not vacuous: under the i.i.d. `U[0,1)` measure `iidUniform ℕ`
(`MarkovDriving.DrivingMC`), almost every sequence is completely uniformly distributed
(Knuth's definition of a random sequence; Owen–Tribble 2005).

**Proof.** Fix `d` and a box `B ⊆ [0,1)^d`. The indicators `Y_t = 1{(u_t, …, u_{t+d-1}) ∈ B}`
are identically distributed (shift invariance of the product measure) with mean `vol B`, and
`d`-dependent. For each residue `r < d` the subsequence `q ↦ Y_{dq+r}` uses disjoint blocks of
coordinates, so it is pairwise independent, and Etemadi's strong law (`strong_law_ae_real`)
gives `(1/Q) ∑_{q<Q} Y_{dq+r} → vol B` a.s.; interleaving the `d` subsequences gives the box
frequency (`tendsto_avg_of_interleaved`). Countably many grid boxes `∏ₖ [iₖ/M, jₖ/M)` then
give every box (`isUD_of_grid`, a sandwich with error `2d/M`), and there are countably many `d`.

**Results.**
* `isUD_fin_zero`: in dimension `0` every sequence is uniformly distributed.
* `tendsto_avg_of_interleaved`: averages along the `d` interleaved subsequences determine the
  average of a bounded sequence.
* `abs_prod_sub_prod_le`: `|∏ xₖ - ∏ yₖ| ≤ ∑ |xₖ - yₖ|` on `[0,1]`.
* `isUD_of_grid`: uniform distribution follows from the grid boxes.
* `ae_tendsto_empAvg_box`: for a fixed box, the window frequencies of an i.i.d. uniform
  sequence converge a.s. to the volume.
* `ae_isCUD_iidUniform`: **an i.i.d. `U[0,1)` sequence is CUD almost surely**, and
  `exists_isCUD`: CUD sequences exist.
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology Finset MeasureTheory ProbabilityTheory

/-- In dimension `0` every sequence is uniformly distributed. -/
theorem isUD_fin_zero (x : ℕ → Fin 0 → ℝ) : IsUD x := by
  refine ⟨fun n k => k.elim0, fun a b _ => ?_⟩
  rw [Fin.prod_univ_zero]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  unfold empAvg boxInd
  simp only [Fin.prod_univ_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [div_self (by exact_mod_cast hN.ne')]

/-- Summing over `t < d Q` is summing over the `d` interleaved subsequences. -/
theorem sum_range_mul_eq_sum_interleaved (f : ℕ → ℝ) (d Q : ℕ) :
    ∑ t ∈ range (d * Q), f t = ∑ r ∈ range d, ∑ q ∈ range Q, f (d * q + r) := by
  induction Q with
  | zero =>
    rw [mul_zero, Finset.sum_range_zero]
    exact (Finset.sum_eq_zero fun r _ => Finset.sum_range_zero _).symm
  | succ Q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => (Finset.sum_range_succ _ _).symm

/-- **Interleaving.** If `0 ≤ f ≤ 1` and along each of the `d ≥ 1` interleaved subsequences
`q ↦ f (d q + r)` the averages tend to `L`, then the averages of `f` tend to `L`. -/
theorem tendsto_avg_of_interleaved {f : ℕ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1)
    {d : ℕ} (hd : 0 < d) {L : ℝ}
    (h : ∀ r < d, Tendsto (fun Q => (∑ q ∈ range Q, f (d * q + r)) / Q) atTop (𝓝 L)) :
    Tendsto (fun N => (∑ t ∈ range N, f t) / N) atTop (𝓝 L) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- block averages
  have hg : Tendsto (fun Q => (∑ t ∈ range (d * Q), f t) / Q) atTop (𝓝 (d * L)) := by
    have := tendsto_finsetSum (range d) fun r hr => h r (Finset.mem_range.1 hr)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    refine this.congr fun Q => ?_
    rw [sum_range_mul_eq_sum_interleaved, Finset.sum_div]
  have hgN := hg.comp (Nat.tendsto_div_const_atTop hd.ne')
  -- the ratio `(N / d) / N → 1 / d`
  have hratio : Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / N) atTop (𝓝 (1 / d)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop : Tendsto
        (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0))
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : ((d * (N / d) : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N d
    have h2 : (N : ℝ) < d * ((N / d : ℕ) : ℝ) + d := by
      have : N < d * (N / d) + d := by
        have := Nat.lt_div_mul_add (a := N) hd
        rw [mul_comm]
        exact this
      exact_mod_cast this
    rw [Nat.cast_mul] at h1
    rw [Real.norm_eq_abs, div_sub_div _ _ hNR.ne' hdR.ne', abs_div,
      abs_of_pos (mul_pos hNR hdR), div_le_div_iff₀ (mul_pos hNR hdR) hNR]
    have habs : |((N / d : ℕ) : ℝ) * d - N * 1| ≤ d := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg (((N / d : ℕ) : ℝ) * d - N * 1)]
  -- the remainder
  have hrem : Tendsto (fun N : ℕ => ((∑ t ∈ range N, f t) - ∑ t ∈ range (d * (N / d)), f t) / N)
      atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop : Tendsto
        (fun N : ℕ => (d : ℝ) / N) atTop (𝓝 0))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hsplit := Finset.sum_range_add f (d * (N / d)) (N - d * (N / d))
      rw [Nat.add_sub_cancel' (Nat.mul_div_le N d)] at hsplit
      rw [hsplit, add_sub_cancel_left]
      exact div_nonneg (Finset.sum_nonneg fun t _ => hf0 _) (Nat.cast_nonneg N)
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      have hsplit := Finset.sum_range_add f (d * (N / d)) (N - d * (N / d))
      rw [Nat.add_sub_cancel' (Nat.mul_div_le N d)] at hsplit
      rw [hsplit, add_sub_cancel_left]
      refine div_le_div_of_nonneg_right ?_ hNR.le
      have hlt : N - d * (N / d) ≤ d := by
        have := Nat.lt_div_mul_add (a := N) hd
        rw [mul_comm] at this
        omega
      calc ∑ t ∈ range (N - d * (N / d)), f (d * (N / d) + t)
          ≤ ∑ t ∈ range (N - d * (N / d)), (1 : ℝ) := Finset.sum_le_sum fun t _ => hf1 _
        _ = ((N - d * (N / d) : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        _ ≤ d := by exact_mod_cast hlt
  have hlim := (hgN.mul hratio).add hrem
  rw [mul_one_div, mul_div_cancel_left₀ L hdR.ne', add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply]
  by_cases hQ : N / d = 0
  · rw [hQ, Nat.cast_zero, zero_div, div_zero, zero_mul, zero_add, mul_zero,
      Finset.sum_range_zero, sub_zero]
  · have hQR : ((N / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hQ
    rw [div_mul_div_comm, mul_comm ((N / d : ℕ) : ℝ) (N : ℝ), ← div_mul_div_comm,
      div_self hQR, mul_one, ← add_div, add_sub_cancel]

/-- `|∏ xₖ - ∏ yₖ| ≤ ∑ |xₖ - yₖ|` for factors in `[0,1]`. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) {x y : ι → ℝ}
    (hx : ∀ k, x k ∈ Set.Icc (0 : ℝ) 1) (hy : ∀ k, y k ∈ Set.Icc (0 : ℝ) 1) :
    |∏ k ∈ s, x k - ∏ k ∈ s, y k| ≤ ∑ k ∈ s, |x k - y k| := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, sub_self, abs_zero, Finset.sum_empty]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hpy : ∏ k ∈ s, y k ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨Finset.prod_nonneg fun k _ => (hy k).1,
        Finset.prod_le_one₀ (fun k _ => (hy k).1) fun k _ => (hy k).2⟩
    have e : x a * ∏ k ∈ s, x k - y a * ∏ k ∈ s, y k =
        x a * (∏ k ∈ s, x k - ∏ k ∈ s, y k) + (x a - y a) * ∏ k ∈ s, y k := by ring
    rw [e]
    calc _ ≤ |x a * (∏ k ∈ s, x k - ∏ k ∈ s, y k)| + |(x a - y a) * ∏ k ∈ s, y k| :=
          abs_add_le _ _
      _ ≤ 1 * |∏ k ∈ s, x k - ∏ k ∈ s, y k| + |x a - y a| * 1 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (hx a).1, abs_of_nonneg hpy.1]
          exact add_le_add (mul_le_mul_of_nonneg_right (hx a).2 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hpy.2 (abs_nonneg _))
      _ ≤ _ := by linarith

/-- If `M c - e ≤ D ≤ M c + e` with `M > 0`, then `|D/M - c| ≤ e/M`. -/
theorem abs_div_sub_le {D c M e : ℝ} (hM : 0 < M) (h1 : M * c - e ≤ D) (h2 : D ≤ M * c + e) :
    |D / M - c| ≤ e / M := by
  calc |D / M - c| = |D / M - M * c / M| := by rw [mul_div_cancel_left₀ _ hM.ne']
    _ = |D - M * c| / M := by rw [← sub_div, abs_div, abs_of_pos hM]
    _ ≤ e / M := div_le_div_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) hM.le

/-- **Uniform distribution from grid boxes.** If the points lie in `[0,1)^d` and every grid box
`∏ₖ [iₖ/M, jₖ/M)` (`iₖ ≤ jₖ ≤ M`, `M ≥ 1`) has limiting frequency `∏ₖ (jₖ - iₖ)/M`, then the
sequence is uniformly distributed. -/
theorem isUD_of_grid {d : ℕ} {x : ℕ → Fin d → ℝ} (hx : ∀ n, InUnitCube (x n))
    (hgrid : ∀ M : ℕ, 0 < M → ∀ i j : Fin d → ℕ, (∀ k, i k ≤ j k ∧ j k ≤ M) →
      Tendsto (empAvg (boxInd fun k => Set.Ico ((i k : ℝ) / M) ((j k : ℝ) / M)) x) atTop
        (𝓝 (∏ k, ((j k : ℝ) / M - (i k : ℝ) / M)))) :
    IsUD x := by
  refine ⟨hx, fun a b hab => ?_⟩
  -- for each `M`, a lower and an upper grid box, within `2/M` per side
  have hbox : ∀ M : ℕ, 0 < M →
      (∃ i j : Fin d → ℕ, (∀ k, i k ≤ j k ∧ j k ≤ M) ∧
        (∀ w : Fin d → ℝ, (∀ k, w k ∈ Set.Ico ((i k : ℝ) / M) ((j k : ℝ) / M)) →
          ∀ k, w k ∈ Set.Ico (a k) (b k)) ∧
        |∏ k, ((j k : ℝ) / M - (i k : ℝ) / M) - ∏ k, (b k - a k)| ≤ 2 * d / M) ∧
      (∃ i j : Fin d → ℕ, (∀ k, i k ≤ j k ∧ j k ≤ M) ∧
        (∀ w : Fin d → ℝ, InUnitCube w → (∀ k, w k ∈ Set.Ico (a k) (b k)) →
          ∀ k, w k ∈ Set.Ico ((i k : ℝ) / M) ((j k : ℝ) / M)) ∧
        |∏ k, ((j k : ℝ) / M - (i k : ℝ) / M) - ∏ k, (b k - a k)| ≤ 2 * d / M) := by
    intro M hM
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hsum : ∑ _k : Fin d, (2 : ℝ) / M = 2 * d / M := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hba : ∀ k, b k - a k ∈ Set.Icc (0 : ℝ) 1 := fun k =>
      ⟨sub_nonneg.2 (hab k).2.1, by linarith [(hab k).1, (hab k).2.2]⟩
    constructor
    · -- lower box: `[⌈M a⌉/M, max(⌈M a⌉, ⌊M b⌋)/M)`
      set i : Fin d → ℕ := fun k => ⌈(M : ℝ) * a k⌉₊ with hi
      set j : Fin d → ℕ := fun k => max (i k) ⌊(M : ℝ) * b k⌋₊ with hj
      have hiM : ∀ k, i k ≤ M := fun k => by
        rw [hi]
        apply Nat.ceil_le.2
        have := mul_le_mul_of_nonneg_left ((hab k).2.1.trans (hab k).2.2) hMR.le
        linarith
      have hfloorM : ∀ k, ⌊(M : ℝ) * b k⌋₊ ≤ M := fun k => by
        apply Nat.floor_le_of_le
        have := mul_le_mul_of_nonneg_left (hab k).2.2 hMR.le
        linarith
      refine ⟨i, j, fun k => ⟨le_max_left _ _, max_le (hiM k) (hfloorM k)⟩, ?_, ?_⟩
      · intro w hw k
        have h1 := (hw k).1
        have h2 := (hw k).2
        have hia : a k ≤ (i k : ℝ) / M := by
          rw [le_div_iff₀ hMR]
          linarith [Nat.le_ceil ((M : ℝ) * a k)]
        refine ⟨hia.trans h1, ?_⟩
        have hij : i k < j k := by
          have : (i k : ℝ) < j k := by
            have := lt_of_le_of_lt h1 h2
            rwa [div_lt_div_iff_of_pos_right hMR] at this
          exact_mod_cast this
        have hjk : j k = max (i k) ⌊(M : ℝ) * b k⌋₊ := rfl
        have hjf : j k = ⌊(M : ℝ) * b k⌋₊ := by
          rw [hjk] at hij ⊢
          exact max_eq_right (le_of_lt ((lt_max_iff.1 hij).resolve_left (lt_irrefl _)))
        calc w k < (j k : ℝ) / M := h2
          _ ≤ b k := by
            rw [div_le_iff₀ hMR, hjf]
            linarith [Nat.floor_le (mul_nonneg hMR.le ((hab k).1.trans (hab k).2.1))]
      · have hside : ∀ k, |((j k : ℝ) / M - (i k : ℝ) / M) - (b k - a k)| ≤ 2 / M := by
          intro k
          have hc1 := Nat.le_ceil ((M : ℝ) * a k)
          have hc2 := Nat.ceil_lt_add_one (mul_nonneg hMR.le (hab k).1)
          have hf1 := Nat.floor_le (mul_nonneg hMR.le ((hab k).1.trans (hab k).2.1))
          have hf2 := Nat.lt_floor_add_one ((M : ℝ) * b k)
          have hjmax : (j k : ℝ) = max (i k : ℝ) (⌊(M : ℝ) * b k⌋₊ : ℝ) := by
            rw [show j k = max (i k) ⌊(M : ℝ) * b k⌋₊ from rfl, Nat.cast_max]
          rw [← sub_div]
          have hab' := mul_le_mul_of_nonneg_left (hab k).2.1 hMR.le
          refine abs_div_sub_le hMR ?_ ?_
          · rcases le_total (i k : ℝ) (⌊(M : ℝ) * b k⌋₊ : ℝ) with hle | hle
            · rw [hjmax, max_eq_right hle]
              nlinarith
            · rw [hjmax, max_eq_left hle]
              nlinarith
          · rcases le_total (i k : ℝ) (⌊(M : ℝ) * b k⌋₊ : ℝ) with hle | hle
            · rw [hjmax, max_eq_right hle]
              nlinarith
            · rw [hjmax, max_eq_left hle]
              nlinarith
        refine (abs_prod_sub_prod_le _ (fun k => ?_) hba).trans ?_
        · have hdiff := hside k
          have hnn : (i k : ℝ) / M ≤ (j k : ℝ) / M :=
            div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hMR.le
          have hjM : (j k : ℝ) / M ≤ 1 := by
            rw [div_le_one hMR]
            exact_mod_cast max_le (hiM k) (hfloorM k)
          have hi0 : 0 ≤ (i k : ℝ) / M := by positivity
          exact ⟨sub_nonneg.2 hnn, by linarith⟩
        · rw [← hsum]
          exact Finset.sum_le_sum fun k _ => hside k
    · -- upper box: `[⌊M a⌋/M, min(⌈M b⌉, M)/M)`
      set i : Fin d → ℕ := fun k => ⌊(M : ℝ) * a k⌋₊ with hi
      set j : Fin d → ℕ := fun k => min ⌈(M : ℝ) * b k⌉₊ M with hj
      have hij : ∀ k, i k ≤ j k := fun k => by
        rw [hi, hj]
        refine le_min ?_ ?_
        · have h1 := Nat.floor_le (mul_nonneg hMR.le (hab k).1)
          have h2 := Nat.le_ceil ((M : ℝ) * b k)
          have h3 := mul_le_mul_of_nonneg_left (hab k).2.1 hMR.le
          have : (⌊(M : ℝ) * a k⌋₊ : ℝ) ≤ ⌈(M : ℝ) * b k⌉₊ := by linarith
          exact_mod_cast this
        · apply Nat.floor_le_of_le
          have := mul_le_mul_of_nonneg_left ((hab k).2.1.trans (hab k).2.2) hMR.le
          linarith
      refine ⟨i, j, fun k => ⟨hij k, min_le_right _ _⟩, ?_, ?_⟩
      · intro w hw hwab k
        have ha0 : 0 ≤ (M : ℝ) * a k := mul_nonneg hMR.le (hab k).1
        refine ⟨?_, ?_⟩
        · calc (i k : ℝ) / M ≤ a k := by
                rw [div_le_iff₀ hMR]
                linarith [Nat.floor_le ha0]
            _ ≤ w k := (hwab k).1
        · have hjmin : (j k : ℝ) = min (⌈(M : ℝ) * b k⌉₊ : ℝ) (M : ℝ) := by
            rw [show j k = min ⌈(M : ℝ) * b k⌉₊ M from rfl, Nat.cast_min]
          rw [lt_div_iff₀ hMR, hjmin, lt_min_iff]
          constructor
          · calc w k * M < b k * M := mul_lt_mul_of_pos_right (hwab k).2 hMR
              _ ≤ _ := by linarith [Nat.le_ceil ((M : ℝ) * b k)]
          · calc w k * M < 1 * M := mul_lt_mul_of_pos_right (hw k).2 hMR
              _ = M := one_mul _
      · have hside : ∀ k, |((j k : ℝ) / M - (i k : ℝ) / M) - (b k - a k)| ≤ 2 / M := by
          intro k
          have ha0 : 0 ≤ (M : ℝ) * a k := mul_nonneg hMR.le (hab k).1
          have hf1 := Nat.floor_le ha0
          have hf2 := Nat.lt_floor_add_one ((M : ℝ) * a k)
          have hc1 := Nat.le_ceil ((M : ℝ) * b k)
          have hc2 := Nat.ceil_lt_add_one (mul_nonneg hMR.le ((hab k).1.trans (hab k).2.1))
          have hjmin : (j k : ℝ) = min (⌈(M : ℝ) * b k⌉₊ : ℝ) (M : ℝ) := by
            rw [show j k = min ⌈(M : ℝ) * b k⌉₊ M from rfl, Nat.cast_min]
          have hMb : (M : ℝ) * b k ≤ M := by
            have := mul_le_mul_of_nonneg_left (hab k).2.2 hMR.le
            linarith
          rw [← sub_div]
          refine abs_div_sub_le hMR ?_ ?_
          · rcases le_total (⌈(M : ℝ) * b k⌉₊ : ℝ) (M : ℝ) with hle | hle
            · rw [hjmin, min_eq_left hle]
              nlinarith
            · rw [hjmin, min_eq_right hle]
              nlinarith
          · rcases le_total (⌈(M : ℝ) * b k⌉₊ : ℝ) (M : ℝ) with hle | hle
            · rw [hjmin, min_eq_left hle]
              nlinarith
            · rw [hjmin, min_eq_right hle]
              nlinarith
        refine (abs_prod_sub_prod_le _ (fun k => ?_) hba).trans ?_
        · have hnn : (i k : ℝ) / M ≤ (j k : ℝ) / M :=
            div_le_div_of_nonneg_right (by exact_mod_cast hij k) hMR.le
          have hjM : (j k : ℝ) / M ≤ 1 := by
            rw [div_le_one hMR]
            exact_mod_cast min_le_right _ _
          have hi0 : 0 ≤ (i k : ℝ) / M := by positivity
          exact ⟨sub_nonneg.2 hnn, by linarith⟩
        · rw [← hsum]
          exact Finset.sum_le_sum fun k _ => hside k
  -- the error `2d/M` tends to `0`
  have herr : Tendsto (fun M : ℕ => 2 * (d : ℝ) / M) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨M, hMc, hM⟩ := ((herr.eventually (gt_mem_nhds (sub_pos.2 hc))).and
      (eventually_gt_atTop 0)).exists
    obtain ⟨⟨i, j, hij, hsub, herrb⟩, _⟩ := hbox M hM
    have hlim := hgrid M hM i j hij
    have hc' : c < ∏ k, ((j k : ℝ) / M - (i k : ℝ) / M) := by
      have := (abs_le.1 herrb).1
      linarith
    filter_upwards [hlim.eventually (lt_mem_nhds hc')] with N hN
    refine hN.trans_le (empAvg_le_empAvg (fun n => boxInd_le_boxInd fun h => hsub _ h) N)
  · obtain ⟨M, hMc, hM⟩ := ((herr.eventually (gt_mem_nhds (sub_pos.2 hc))).and
      (eventually_gt_atTop 0)).exists
    obtain ⟨_, ⟨i, j, hij, hsup, herrb⟩⟩ := hbox M hM
    have hlim := hgrid M hM i j hij
    have hc' : ∏ k, ((j k : ℝ) / M - (i k : ℝ) / M) < c := by
      have := (abs_le.1 herrb).2
      linarith
    filter_upwards [hlim.eventually (gt_mem_nhds hc')] with N hN
    exact (empAvg_le_empAvg (fun n => boxInd_le_boxInd fun h => hsup _ (hx n) h) N).trans_lt hN

/-- Box indicators of measurable sides are measurable. -/
theorem measurable_boxInd {d : ℕ} {S : Fin d → Set ℝ} (hS : ∀ k, MeasurableSet (S k)) :
    Measurable (boxInd S) := by
  unfold boxInd
  exact Finset.measurable_prod _ fun k _ =>
    (measurable_const.indicator (hS k)).comp (measurable_pi_apply k)

/-- Under the i.i.d. measure, the window indicator at time `t` has the law of the one at time
`0` (shift invariance). -/
theorem identDistrib_window_boxInd {d : ℕ} {S : Fin d → Set ℝ} (hS : ∀ k, MeasurableSet (S k))
    (t : ℕ) :
    IdentDistrib (fun ω : ℕ → ℝ => boxInd S (window ω d t))
      (fun ω : ℕ → ℝ => boxInd S fun k : Fin d => ω k) (iidUniform ℕ) (iidUniform ℕ) := by
  have hmeas : Measurable fun ω : ℕ → ℝ => boxInd S fun k : Fin d => ω k :=
    (measurable_boxInd hS).comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)
  have hshift : Measurable fun ω : ℕ → ℝ => fun i : ℕ => ω (t + i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  refine ⟨(hmeas.comp hshift).aemeasurable, hmeas.aemeasurable, ?_⟩
  have hmap : (iidUniform ℕ).map (fun ω : ℕ → ℝ => fun i : ℕ => ω (t + i)) = iidUniform ℕ := by
    have := isProbabilityMeasure_uniformIco
    unfold iidUniform
    exact Measure.map_infinitePi_infinitePi_of_inj (add_right_injective t)
  change (iidUniform ℕ).map ((fun ω : ℕ → ℝ => boxInd S fun k : Fin d => ω k) ∘
    fun ω i => ω (t + i)) = _
  rw [← Measure.map_map hmeas hshift, hmap]

/-- Window indicators at times at least `d` apart are independent under the i.i.d. measure. -/
theorem indepFun_window_boxInd {d : ℕ} {S : Fin d → Set ℝ} (hS : ∀ k, MeasurableSet (S k))
    {s t : ℕ} (hst : s + d ≤ t ∨ t + d ≤ s) :
    IndepFun (fun ω : ℕ → ℝ => boxInd S (window ω d s))
      (fun ω : ℕ → ℝ => boxInd S (window ω d t)) (iidUniform ℕ) := by
  have hind : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) (iidUniform ℕ) := by
    have := isProbabilityMeasure_uniformIco
    unfold iidUniform
    exact iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  have hdisj : Disjoint (Finset.Ico s (s + d)) (Finset.Ico t (t + d)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_Ico] at hi hi'
    omega
  have h := hind.indepFun_finset _ _ hdisj fun i => measurable_pi_apply i
  have hφ : ∀ v : ℕ, Measurable fun z : (Finset.Ico v (v + d)) → ℝ =>
      boxInd S fun k : Fin d => z ⟨v + k, Finset.mem_Ico.2 ⟨Nat.le_add_right _ _, by omega⟩⟩ :=
    fun v => (measurable_boxInd hS).comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)
  exact h.comp (hφ s) (hφ t)

/-- The mean of a box indicator under the i.i.d. measure is the volume of the box. -/
theorem integral_boxInd_iidUniform {d : ℕ} {a b : Fin d → ℝ}
    (hab : ∀ k, 0 ≤ a k ∧ a k ≤ b k ∧ b k ≤ 1) :
    ∫ ω, boxInd (fun k => Set.Ico (a k) (b k)) (fun k : Fin d => ω k) ∂(iidUniform ℕ) =
      ∏ k, (b k - a k) := by
  classical
  have := isProbabilityMeasure_uniformIco
  set T : ℕ → Set ℝ := fun i => if h : i < d then Set.Ico (a ⟨i, h⟩) (b ⟨i, h⟩) else Set.univ
    with hT
  set E : Set (ℕ → ℝ) := Set.pi (↑(range d)) T with hE
  have hTm : ∀ i ∈ range d, MeasurableSet (T i) := fun i _ => by
    rw [hT]
    dsimp only
    split_ifs
    · exact measurableSet_Ico
    · exact MeasurableSet.univ
  have hEm : MeasurableSet E := MeasurableSet.pi (Finset.countable_toSet _) hTm
  have hfun : (fun ω : ℕ → ℝ => boxInd (fun k => Set.Ico (a k) (b k)) fun k : Fin d => ω k) =
      E.indicator 1 := by
    funext ω
    rw [boxInd_eq_ite, Set.indicator_apply]
    have hiff : (∀ k : Fin d, ω k ∈ Set.Ico (a k) (b k)) ↔ ω ∈ E := by
      rw [hE, Set.mem_pi]
      constructor
      · intro h i hi
        have hi' : i < d := Finset.mem_range.1 hi
        rw [hT]
        simp only [hi', ↓reduceDIte]
        exact h ⟨i, hi'⟩
      · intro h k
        have := h k (Finset.mem_coe.2 (Finset.mem_range.2 k.isLt))
        rw [hT] at this
        simp only [k.isLt, ↓reduceDIte] at this
        exact this
    by_cases h : ∀ k : Fin d, ω k ∈ Set.Ico (a k) (b k)
    · simp only [h, hiff.1 h, implies_true, ↓reduceIte, Pi.one_apply]
    · simp only [h, mt hiff.2 h, ↓reduceIte]
  rw [hfun, integral_indicator_one hEm, Measure.real, hE]
  unfold iidUniform
  rw [Measure.infinitePi_pi (μ := fun _ : ℕ => uniformIco) hTm, ENNReal.toReal_prod,
    ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hTk : T k = Set.Ico (a k) (b k) := by
    rw [hT]
    simp only [k.isLt, ↓reduceDIte]
  rw [hTk, Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.2 (Set.Ico_subset_Ico (hab k).1 (hab k).2.2), Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.2 (hab k).2.1)]

/-- **Box frequencies of an i.i.d. sequence.** For a fixed box `∏ₖ [aₖ, bₖ)`, almost every
i.i.d. `U[0,1)` sequence has window frequencies tending to the volume. -/
theorem ae_tendsto_empAvg_box (d : ℕ) {a b : Fin d → ℝ}
    (hab : ∀ k, 0 ≤ a k ∧ a k ≤ b k ∧ b k ≤ 1) :
    ∀ᵐ ω ∂(iidUniform ℕ), Tendsto (empAvg (boxInd fun k => Set.Ico (a k) (b k)) (window ω d))
      atTop (𝓝 (∏ k, (b k - a k))) := by
  have := isProbabilityMeasure_iidUniform ℕ
  have hS : ∀ k, MeasurableSet (Set.Ico (a k) (b k)) := fun k => measurableSet_Ico
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Eventually.of_forall fun ω => (isUD_fin_zero _).2 a b hab
  have hr : ∀ r : Fin d, ∀ᵐ ω ∂(iidUniform ℕ), Tendsto (fun Q =>
      (∑ q ∈ range Q, boxInd (fun k => Set.Ico (a k) (b k)) (window ω d (d * q + r))) / Q)
      atTop (𝓝 (∏ k, (b k - a k))) := by
    intro r
    set X : ℕ → (ℕ → ℝ) → ℝ := fun q ω =>
      boxInd (fun k => Set.Ico (a k) (b k)) (window ω d (d * q + r)) with hX
    have hident : ∀ q, IdentDistrib (X q) (X 0) (iidUniform ℕ) (iidUniform ℕ) := fun q =>
      (identDistrib_window_boxInd hS _).trans (identDistrib_window_boxInd hS _).symm
    have hindep : Pairwise fun q q' => IndepFun (X q) (X q') (iidUniform ℕ) := by
      intro q q' hqq'
      refine indepFun_window_boxInd hS ?_
      rcases lt_or_gt_of_ne hqq' with h | h
      · left
        have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h)
        rw [Nat.mul_succ] at this
        omega
      · right
        have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h)
        rw [Nat.mul_succ] at this
        omega
    have hmeas0 : Measurable (X 0) :=
      (measurable_boxInd hS).comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)
    have hint : Integrable (X 0) (iidUniform ℕ) := by
      refine Integrable.of_bound hmeas0.aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (boxInd_nonneg _ _)]
      exact boxInd_le_one _ _
    have hmean : (iidUniform ℕ)[X 0] = ∏ k, (b k - a k) := by
      rw [(identDistrib_window_boxInd hS _).integral_eq]
      exact integral_boxInd_iidUniform hab
    have hlaw := strong_law_ae_real X hint hindep hident
    rw [hmean] at hlaw
    exact hlaw
  filter_upwards [ae_all_iff.2 hr] with ω hω
  exact tendsto_avg_of_interleaved (f := fun t => boxInd (fun k => Set.Ico (a k) (b k))
    (window ω d t)) (fun t => boxInd_nonneg _ _) (fun t => boxInd_le_one _ _) hd
    fun r hr' => hω ⟨r, hr'⟩

/-- **Existence of CUD sequences.** Almost every i.i.d. `U[0,1)` sequence is completely uniformly
distributed. -/
theorem ae_isCUD_iidUniform : ∀ᵐ u ∂(iidUniform ℕ), IsCUD u := by
  have := isProbabilityMeasure_iidUniform ℕ
  have hcube : ∀ᵐ u ∂(iidUniform ℕ), ∀ t, u t ∈ Set.Ico (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro t
    have hmp : (iidUniform ℕ).map (fun u => u t) = uniformIco := by
      have := isProbabilityMeasure_uniformIco
      unfold iidUniform
      exact Measure.infinitePi_map_eval _ t
    have h1 : ∀ᵐ x ∂uniformIco, x ∈ Set.Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico
    rw [← hmp] at h1
    exact ae_of_ae_map (measurable_pi_apply t).aemeasurable h1
  have hgrid : ∀ d : ℕ, ∀ᵐ u ∂(iidUniform ℕ), ∀ p : ℕ × (Fin d → ℕ) × (Fin d → ℕ),
      0 < p.1 → (∀ k, p.2.1 k ≤ p.2.2 k ∧ p.2.2 k ≤ p.1) →
        Tendsto (empAvg (boxInd fun k => Set.Ico ((p.2.1 k : ℝ) / p.1) ((p.2.2 k : ℝ) / p.1))
          (window u d)) atTop (𝓝 (∏ k, ((p.2.2 k : ℝ) / p.1 - (p.2.1 k : ℝ) / p.1))) := by
    intro d
    rw [ae_all_iff]
    rintro ⟨M, i, j⟩
    by_cases hv : 0 < M ∧ ∀ k, i k ≤ j k ∧ j k ≤ M
    · have hMR : (0 : ℝ) < M := by exact_mod_cast hv.1
      have hab : ∀ k, 0 ≤ (i k : ℝ) / M ∧ (i k : ℝ) / M ≤ (j k : ℝ) / M ∧ (j k : ℝ) / M ≤ 1 :=
        fun k => ⟨by positivity, div_le_div_of_nonneg_right (by exact_mod_cast (hv.2 k).1)
          hMR.le, (div_le_one hMR).2 (by exact_mod_cast (hv.2 k).2)⟩
      filter_upwards [ae_tendsto_empAvg_box d hab] with u hu _ _
      exact hu
    · exact Eventually.of_forall fun u h1 h2 => absurd ⟨h1, h2⟩ hv
  change ∀ᵐ u ∂(iidUniform ℕ), ∀ d, IsUD (window u d)
  rw [ae_all_iff]
  intro d
  filter_upwards [hcube, hgrid d] with u hu hg
  exact isUD_of_grid (window_mem hu d) fun M hM i j hij => hg (M, i, j) hM hij

/-- **CUD sequences exist**, so the Chentsov theorems of `ChentsovConsistency` are not
vacuous. -/
theorem exists_isCUD : ∃ u : ℕ → ℝ, IsCUD u := by
  have := isProbabilityMeasure_iidUniform ℕ
  have : (ae (iidUniform ℕ)).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  exact ae_isCUD_iidUniform.exists

end RQMCMarkov.MarkovDriving

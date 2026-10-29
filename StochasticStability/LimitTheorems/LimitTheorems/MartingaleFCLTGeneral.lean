/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.MartingaleFCLTGeneralTools

/-!
# The functional CLT for martingales under (D.8) and (D.9) (MT Theorem D.6.4)

Meyn and Tweedie, Theorem D.6.4, p. 563, under the book's hypotheses: `Mₙ = Σ_{k<n} Dₖ` with
square-integrable martingale differences `Dₖ` (`𝓕ₖ₊₁`-measurable, `E[Dₖ | 𝓕ₖ] = 0`),
(D.8) `(1/n) Σ_{k<n} E[Dₖ² | 𝓕ₖ] → γ²` a.s. and (D.9) `(1/n) Σ_{k<n} E[Dₖ² 1{Dₖ² ≥ εn} | 𝓕ₖ] → 0`
a.s. for every `ε > 0`; no moment bound beyond square integrability and no stationarity. The book
cites Hall and Heyde, Theorem 4.1.

**The proof.** `mPath D n = n^{−1/2} mₙ`.
* Tightness (`modulus_condition_mPath`). For `ε, θ > 0` the increments are truncated at
  `Dₖ² < εn`, recentred, and stopped when the conditional-variance clock leaves the band
  `|clock(j) − j| ≤ θn` (`locInc`, `MartingaleFCLTGeneralTools`). The stopped clock over a block of
  length `L` is at most `L + 2θn` pathwise (`sum_activeW_mul_cvar_le`), so the fourth-moment
  bound `integral_pow_four_sum_le_clock` and Doob's inequality give the block bound
  `measureReal_block_max_locInc_le`; with `ε` small, `θ = 1/m` and `m` large this gives the
  modulus condition for the localised process. By (D.8) (uniformly in time, `ae_tendsto_clockDev`)
  and (D.9) (no large increments, Lenglart), the localised process is uniformly close to
  `mPath D n` in probability (`tendsto_measureReal_norm_mPath_locInc_sub`).
* The squares follow the clock (`tendstoInMeasure_sum_floor_sq_sub_of_lindeberg`):
  `(1/n) Σ_{k<⌊nt⌋} Dₖ² → t` in probability, from the same localisation and Chebyshev's inequality
  for the martingale part of the squares (`measureReal_sq_martingale_part_le`); the pathwise
  bookkeeping is `locInc_good_event` and `abs_avg_sq_sub_lt_of_good`.
* The finite-dimensional distributions (`fidiLin_mPath_of_lindeberg`): the increments localised
  at the clock `2n` (`locWeight`) form a martingale-difference array with `E Σ_{k<n} Yₖ² ≤ 2n`, to
  which `array_fidiLin_polygonal_of_tendstoInMeasure` applies; the localisation is inactive with
  probability `→ 1` (`tendsto_measureReal_exists_locWeight_ne_one`).

**Results.**
* **Theorem D.6.4** (`theorem_D_6_4`): `(γ² n)^{−1/2} mₙ ⇒ B` under (D.8) and (D.9);
  `martingale_fclt_lindeberg_one` is the case `γ² = 1`.
* `tendstoInMeasure_sum_floor_sq_sub_of_lindeberg`: the law of large numbers for the squares in
  probability under (D.8) and (D.9).

**Corrections.** None: the theorem holds as stated (with `M₀ = 0`; a nonzero `M₀` changes
`n^{−1/2} mₙ` by `n^{−1/2} M₀ → 0`).
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### The stopping weights -/

omit [MeasurableSpace Ω] in
/-- Telescoping along an initial segment: if `wₖ ∈ {0, 1}` is antitone and `|Bₖ|, |Bₖ₊₁| ≤ τ`
whenever `wₖ = 1`, then `Σ_{i<L} w_{k₀+i} (B_{k₀+i+1} − B_{k₀+i}) ≤ 2τ`. -/
theorem sum_weight_telescope_le {w B : ℕ → ℝ} (hw01 : ∀ k, w k = 0 ∨ w k = 1)
    (hanti : ∀ k, w (k + 1) = 1 → w k = 1) {τ : ℝ} (hτ : 0 ≤ τ)
    (hB : ∀ k, w k = 1 → |B k| ≤ τ ∧ |B (k + 1)| ≤ τ) (k₀ L : ℕ) :
    ∑ i ∈ Finset.range L, w (k₀ + i) * (B (k₀ + i + 1) - B (k₀ + i)) ≤ 2 * τ := by
  have hdown : ∀ m, w m = 1 → ∀ k ≤ m, w k = 1 := by
    intro m hm k hk
    induction m with
    | zero => rwa [Nat.le_zero.1 hk]
    | succ m ih =>
      rcases Nat.lt_or_eq_of_le hk with h | h
      · exact ih (hanti m hm) (Nat.lt_succ_iff.1 h)
      · rwa [h]
  have key : ∀ L, (∑ i ∈ Finset.range L, w (k₀ + i) * (B (k₀ + i + 1) - B (k₀ + i)) ≤ 2 * τ) ∧
      ((L = 0 ∨ w (k₀ + L - 1) = 1) →
        ∑ i ∈ Finset.range L, w (k₀ + i) * (B (k₀ + i + 1) - B (k₀ + i)) =
          B (k₀ + L) - B k₀) := by
    intro L
    induction L with
    | zero => simp; linarith
    | succ L ih =>
      rw [Finset.sum_range_succ]
      rcases hw01 (k₀ + L) with h0 | h1
      · rw [h0, zero_mul, add_zero]
        refine ⟨ih.1, fun h => ?_⟩
        rcases h with h | h
        · omega
        · rw [show k₀ + (L + 1) - 1 = k₀ + L by omega, h0] at h; norm_num at h
      · have hprev : L = 0 ∨ w (k₀ + L - 1) = 1 := by
          rcases Nat.eq_zero_or_pos L with hL | hL
          · exact Or.inl hL
          · right
            exact hanti _ (by rw [show k₀ + L - 1 + 1 = k₀ + L by omega]; exact h1)
        have hs := ih.2 hprev
        rw [hs, h1, one_mul]
        have hk0 := (hB k₀ (hdown _ h1 k₀ (by omega))).1
        have hkL := (hB (k₀ + L) h1).2
        refine ⟨?_, fun _ => by rw [show k₀ + (L + 1) = k₀ + L + 1 by omega]; ring⟩
        rw [show B (k₀ + L) - B k₀ + (B (k₀ + L + 1) - B (k₀ + L)) =
          B (k₀ + L + 1) - B k₀ by ring]
        calc B (k₀ + L + 1) - B k₀ ≤ |B (k₀ + L + 1)| + |B k₀| := by
              linarith [le_abs_self (B (k₀ + L + 1)), neg_abs_le (B k₀)]
          _ ≤ 2 * τ := by linarith
  exact (key L).1

/-- Properties of the stopping weights: `𝓕ₖ`-measurable, `0` or `1`, antitone; while active the
clock is within `τ` of the time; if the clock stays within `τ` up to `n`, all weights `k < n`
are active. -/
theorem activeW_props (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (a τ : ℝ)
    (hτ : 0 ≤ τ) :
    (∀ k, StronglyMeasurable[ℱ k] (activeW Q ℱ D a τ k)) ∧
      (∀ k ω, activeW Q ℱ D a τ k ω = 0 ∨ activeW Q ℱ D a τ k ω = 1) ∧
      (∀ k ω, activeW Q ℱ D a τ (k + 1) ω = 1 → activeW Q ℱ D a τ k ω = 1) ∧
      (∀ k ω, activeW Q ℱ D a τ k ω = 1 → ∀ i ≤ k + 1, |ctClock Q ℱ D a i ω - i| ≤ τ) ∧
      (∀ n ω, (∀ j ≤ n, |ctClock Q ℱ D a j ω - j| ≤ τ) → ∀ k < n,
        activeW Q ℱ D a τ k ω = 1) := by
  have hmem : ∀ k ω, activeW Q ℱ D a τ k ω = 1 ↔
      ∀ j ∈ Finset.range (k + 1), |ctClock Q ℱ D a (j + 1) ω - (j + 1)| ≤ τ := by
    intro k ω
    unfold activeW
    by_cases h : ∀ j ∈ Finset.range (k + 1), |ctClock Q ℱ D a (j + 1) ω - (j + 1)| ≤ τ
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ∀ j ∈ Finset.range (k + 1),
        |ctClock Q ℱ D a (j + 1) ω - (j + 1)| ≤ τ} from h)]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | ∀ j ∈ Finset.range (k + 1),
        |ctClock Q ℱ D a (j + 1) ω - (j + 1)| ≤ τ} from h)]
      exact ⟨fun h' => absurd h' zero_ne_one, fun h' => absurd h' h⟩
  refine ⟨fun k => ?_, fun k ω => ?_, fun k ω h => ?_, fun k ω h i hi => ?_, ?_⟩
  · have hc : ∀ j ∈ Finset.range (k + 1), Measurable[ℱ k] (ctClock Q ℱ D a (j + 1)) := by
      intro j hj
      refine Finset.measurable_sum _ fun i hi => ?_
      exact (stronglyMeasurable_condExp.measurable).mono (ℱ.mono (by
        have := Finset.mem_range.1 hi; have := Finset.mem_range.1 hj; omega)) le_rfl
    have hset : MeasurableSet[ℱ k] {ω | ∀ j ∈ Finset.range (k + 1),
        |ctClock Q ℱ D a (j + 1) ω - (j + 1)| ≤ τ} := by
      have : {ω | ∀ j ∈ Finset.range (k + 1), |ctClock Q ℱ D a (j + 1) ω - (j + 1)| ≤ τ} =
          ⋂ j ∈ Finset.range (k + 1), {ω | |ctClock Q ℱ D a (j + 1) ω - (j + 1)| ≤ τ} := by
        ext ω; simp
      rw [this]
      exact Finset.measurableSet_biInter _ fun j hj => measurableSet_le
        (continuous_abs.measurable.comp ((hc j hj).sub measurable_const)) measurable_const
    exact (measurable_const.indicator hset).stronglyMeasurable
  · simp only [activeW, Set.indicator_apply]; split_ifs <;> simp
  · rw [hmem] at h ⊢
    exact fun j hj => h j (Finset.mem_range.2 (by have := Finset.mem_range.1 hj; omega))
  · rw [hmem] at h
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [ctClock, hτ]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have := h j (Finset.mem_range.2 (by omega))
      push_cast
      exact this
  · intro n ω h k hk
    rw [hmem]
    intro j hj
    have := h (j + 1) (by have := Finset.mem_range.1 hj; omega)
    push_cast at this
    exact this

/-- **The block clock** of the stopped increments: pathwise,
`Σ_{k₀≤k<k₀+L} activeWₖ · cvarₖ ≤ L + 2τ`. -/
theorem sum_activeW_mul_cvar_le (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (a : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (k₀ L : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range L, activeW Q ℱ D a τ (k₀ + i) ω * cvar Q ℱ D a (k₀ + i) ω ≤
      L + 2 * τ := by
  obtain ⟨-, h01, hanti, hact, -⟩ := activeW_props Q ℱ D a τ hτ
  set B : ℕ → ℝ := fun j => ctClock Q ℱ D a j ω - j with hB
  have hcv : ∀ k, cvar Q ℱ D a k ω = B (k + 1) - B k + 1 := fun k => by
    simp only [hB, ctClock, Finset.sum_range_succ]; push_cast; ring
  have htel := sum_weight_telescope_le (w := fun k => activeW Q ℱ D a τ k ω) (B := B)
    (fun k => h01 k ω) (fun k => hanti k ω) hτ (fun k hk =>
      ⟨hact k ω hk k (Nat.le_succ k), hact k ω hk (k + 1) le_rfl⟩) k₀ L
  have hw1 : ∑ i ∈ Finset.range L, activeW Q ℱ D a τ (k₀ + i) ω ≤ L := by
    calc ∑ i ∈ Finset.range L, activeW Q ℱ D a τ (k₀ + i) ω ≤ ∑ _i ∈ Finset.range L, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by rcases h01 (k₀ + i) ω with h | h <;> rw [h]; norm_num
      _ = L := by simp
  calc ∑ i ∈ Finset.range L, activeW Q ℱ D a τ (k₀ + i) ω * cvar Q ℱ D a (k₀ + i) ω
      = ∑ i ∈ Finset.range L, activeW Q ℱ D a τ (k₀ + i) ω +
        ∑ i ∈ Finset.range L, activeW Q ℱ D a τ (k₀ + i) ω *
          (B (k₀ + i + 1) - B (k₀ + i)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [hcv]; ring
    _ ≤ L + 2 * τ := add_le_add hw1 htel

/-- **The localised increments** `activeW · ctrunc`: `𝓕ₖ₊₁`-measurable, bounded by `2√a`,
martingale differences, with `E[locIncₖ² | 𝓕ₖ] = activeWₖ · cvarₖ`. -/
theorem locInc_props {Q : Measure Ω} [IsProbabilityMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {a τ : ℝ} (ha : 0 < a)
    (hτ : 0 ≤ τ) (k : ℕ) :
    StronglyMeasurable[ℱ (k + 1)] (locInc Q ℱ D a τ k) ∧
      (∀ᵐ ω ∂Q, |locInc Q ℱ D a τ k ω| ≤ 2 * √a) ∧ Q[locInc Q ℱ D a τ k | ℱ k] =ᵐ[Q] 0 ∧
      Q[fun ω => locInc Q ℱ D a τ k ω ^ 2 | ℱ k] =ᵐ[Q]
        (fun ω => activeW Q ℱ D a τ k ω * cvar Q ℱ D a k ω) ∧
      MemLp (locInc Q ℱ D a τ k) 2 Q := by
  obtain ⟨hwF, h01, -, -, -⟩ := activeW_props Q ℱ D a τ hτ
  obtain ⟨hZF, hZb, hZ0, -, -, -⟩ := ctrunc_props hD hL2 h0 ha k
  have hwF' : StronglyMeasurable[ℱ (k + 1)] (activeW Q ℱ D a τ k) :=
    ((hwF k).measurable.mono (ℱ.mono (Nat.le_succ k)) le_rfl).stronglyMeasurable
  have hZm : Measurable (ctrunc Q ℱ D a k) := hZF.measurable.mono (ℱ.le (k + 1)) le_rfl
  have hwab : ∀ ω, |activeW Q ℱ D a τ k ω| ≤ 1 := fun ω => by
    rcases h01 k ω with h | h <;> rw [h] <;> norm_num
  have hb : ∀ᵐ ω ∂Q, |locInc Q ℱ D a τ k ω| ≤ 2 * √a := by
    filter_upwards [hZb] with ω hω
    simp only [locInc]
    rw [abs_mul]
    calc |activeW Q ℱ D a τ k ω| * |ctrunc Q ℱ D a k ω| ≤ 1 * (2 * √a) :=
          mul_le_mul (hwab ω) hω (abs_nonneg _) zero_le_one
      _ = 2 * √a := one_mul _
  have hL2d : MemLp (locInc Q ℱ D a τ k) 2 Q :=
    MemLp.of_bound (((hwF'.measurable.mono (ℱ.le (k + 1)) le_rfl).mul hZm).aestronglyMeasurable)
      (2 * √a) (hb.mono fun ω h => by rwa [Real.norm_eq_abs])
  have hZL2 : MemLp (ctrunc Q ℱ D a k) 2 Q :=
    MemLp.of_bound hZm.aestronglyMeasurable (2 * √a) (hZb.mono fun ω h => by
      rwa [Real.norm_eq_abs])
  refine ⟨(hwF'.measurable.mul hZF.measurable).stronglyMeasurable, hb, ?_, ?_, hL2d⟩
  · have h1 : Q[locInc Q ℱ D a τ k | ℱ k] =ᵐ[Q]
        activeW Q ℱ D a τ k * Q[ctrunc Q ℱ D a k | ℱ k] :=
      condExp_mul_of_stronglyMeasurable_left (hwF k) (hL2d.integrable one_le_two)
        (hZL2.integrable one_le_two)
    filter_upwards [h1, hZ0] with ω e1 e2
    rw [e1, Pi.mul_apply, e2, Pi.zero_apply, mul_zero]
  · have hsq : (fun ω => locInc Q ℱ D a τ k ω ^ 2) =
        activeW Q ℱ D a τ k * ctrunc Q ℱ D a k ^ 2 := by
      ext ω
      simp only [locInc, Pi.mul_apply, Pi.pow_apply]
      rcases h01 k ω with h | h <;> rw [h] <;> ring
    rw [hsq]
    have h1 := condExp_mul_of_stronglyMeasurable_left (μ := Q) (hwF k)
      (f := activeW Q ℱ D a τ k) (g := ctrunc Q ℱ D a k ^ 2)
      (by rw [← hsq]; exact hL2d.integrable_sq) hZL2.integrable_sq
    exact h1

/-! ### The clock and the Lindeberg averages -/

/-- The Lindeberg average `(1/n) Σ_{k<n} E[Dₖ² 1{Dₖ² ≥ εn} | 𝓕ₖ]` of (D.9). -/
noncomputable def lindAvg (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (ε : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (∑ k ∈ Finset.range n, Q[bigSq D (ε * n) k | ℱ k] ω) / n

/-- The deviation of the conditional-variance clock, `max_{j≤n} |Σ_{i<j} E[Dᵢ² | 𝓕ᵢ] − j| / n`. -/
noncomputable def clockDev (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun j => |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j|) / n

/-- Measurability of `lindAvg` and `clockDev`. -/
theorem measurable_lindAvg_clockDev (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (ε : ℝ) (n : ℕ) : Measurable (lindAvg Q ℱ D ε n) ∧ Measurable (clockDev Q ℱ D n) := by
  have hV : ∀ i, Measurable (Q[fun ω => D i ω ^ 2 | ℱ i]) := fun i =>
    (stronglyMeasurable_condExp.measurable).mono (ℱ.le i) le_rfl
  refine ⟨(Finset.measurable_sum _ fun k _ => (stronglyMeasurable_condExp.measurable).mono
    (ℱ.le k) le_rfl).div_const _, ?_⟩
  refine Measurable.div_const ?_ _
  have h := Finset.measurable_sup' (s := Finset.range (n + 1)) Finset.nonempty_range_add_one
    (f := fun j ω => |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j|)
    (fun j _ => continuous_abs.measurable.comp
      ((Finset.measurable_sum _ fun i _ => hV i).sub measurable_const))
  convert h using 1
  funext ω
  rw [Finset.sup'_apply]

/-- Under (D.8), `clockDev → 0` almost surely (uniformity of the clock). -/
theorem ae_tendsto_clockDev {Q : Measure Ω} [IsProbabilityMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ}
    (hcv : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 1)) :
    ∀ᵐ ω ∂Q, Tendsto (fun n => clockDev Q ℱ D n ω) atTop (𝓝 0) := by
  have hpos : ∀ᵐ ω ∂Q, ∀ k, 0 ≤ Q[fun ω => D k ω ^ 2 | ℱ k] ω :=
    ae_all_iff.2 fun k => (condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg (D k ω))).mono
      fun ω h => by simpa using h
  filter_upwards [hcv, hpos] with ω hω h0
  rw [Metric.tendsto_atTop]
  intro θ hθ
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_abs_sum_sub_le h0 hω (half_pos hθ)).and
    (eventually_ge_atTop 1))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h2
  have hle : (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun j => |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j|) ≤ θ / 2 * n :=
    Finset.sup'_le _ _ fun j hj => h1 j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  have hge : 0 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun j => |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j|) :=
    (abs_nonneg _).trans (Finset.le_sup' (fun j => |∑ i ∈ Finset.range j,
      Q[fun ω => D i ω ^ 2 | ℱ i] ω - j|) (Finset.mem_range.2 (Nat.succ_pos n)))
  rw [Real.dist_eq, sub_zero, clockDev, abs_of_nonneg (div_nonneg hge hn0.le),
    div_lt_iff₀ hn0]
  nlinarith

/-! ### The truncated, recentred and stopped process is close to the original one -/

/-- The normalised polygonal process `n^{−1/2} mₙ` of the partial sums of `D`. -/
noncomputable def mPath (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : C(unitInterval, ℝ) :=
  polygonal n fun k => (√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range k, D l ω

/-- **The approximation lemma**: for `ε, θ > 0` the polygonal process of the localised
increments (truncated at `Dₖ² < εn`, recentred, stopped when the clock leaves the band of width
`θn`) is uniformly close to `n^{−1/2} mₙ` in probability. -/
theorem tendsto_measureReal_norm_mPath_locInc_sub {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hcv : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 1))
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hlin : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => lindAvg Q ℱ D ε n ω) atTop (𝓝 0)) {κ : ℝ}
    (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => Q.real {ω | κ ≤
      ‖mPath (fun l ω => locInc Q ℱ D (ε * n) (θ * n) l ω) n ω - mPath D n ω‖}) atTop (𝓝 0) := by
  set ℓ0 := min (θ / 4) (min (√(ε * (θ / 4))) (κ * √ε)) with hℓ0
  have hsε : 0 < √ε := Real.sqrt_pos.2 hε
  have hℓ0p : 0 < ℓ0 := lt_min (by positivity) (lt_min (Real.sqrt_pos.2 (by positivity))
    (by positivity))
  -- the three small probabilities
  have hB1 := tendsto_measureReal_exists_big hD hL2 hε hlin
  have hB2 := tendsto_measureReal_of_ae_tendsto (fun n => (measurable_lindAvg_clockDev Q ℱ D ε n).2)
    (ae_tendsto_clockDev hcv) (half_pos hθ)
  have hB3 := tendsto_measureReal_of_ae_tendsto (fun n => (measurable_lindAvg_clockDev Q ℱ D ε n).1)
    hlin hℓ0p
  have hsum := (hB1.add hB2).add hB3
  simp only [add_zero] at hsum
  -- the almost sure identities
  have hid : ∀ᵐ ω ∂Q, ∀ n : ℕ, 1 ≤ n → ∀ k,
      |Q[truncSq D (ε * n) k | ℱ k] ω| ≤ Q[bigSq D (ε * n) k | ℱ k] ω / √(ε * n) ∧
      |cvar Q ℱ D (ε * n) k ω - Q[fun ω => D k ω ^ 2 | ℱ k] ω| ≤
        Q[bigSq D (ε * n) k | ℱ k] ω + Q[truncSq D (ε * n) k | ℱ k] ω ^ 2 := by
    refine ae_all_iff.2 fun n => ?_
    by_cases hn : 1 ≤ n
    · have ha : 0 < ε * n := mul_pos hε (by exact_mod_cast hn)
      filter_upwards [ae_all_iff.2 fun k => (ctrunc_props hD hL2 h0 ha k).2.2.2.1,
        ae_all_iff.2 fun k => (ctrunc_props hD hL2 h0 ha k).2.2.2.2.1] with ω h1 h2 _ k
      exact ⟨h1 k, h2 k⟩
    · exact Eventually.of_forall fun ω h => absurd h hn
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg)
    (eventually_atTop.2 ⟨1, fun n hn => ?_⟩) hsum
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < ε * n := mul_pos hε hn0
  have hsa : √(ε * n) = √ε * √(n : ℝ) := Real.sqrt_mul hε.le _
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  -- the good event implies closeness
  have hsub : ∀ᵐ ω ∂Q, ω ∈ {ω | κ ≤
      ‖mPath (fun l ω => locInc Q ℱ D (ε * n) (θ * n) l ω) n ω - mPath D n ω‖} →
      ω ∈ ({ω | ∃ k < n, ε * n ≤ D k ω ^ 2} ∪ {ω | θ / 2 ≤ |clockDev Q ℱ D n ω|} ∪
        {ω | ℓ0 ≤ |lindAvg Q ℱ D ε n ω|} : Set Ω) := by
    filter_upwards [hid] with ω hω hbad
    by_contra hgood
    simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_le] at hgood
    obtain ⟨⟨hsmall, hcd⟩, hla⟩ := hgood
    have hω' := hω n hn
    set c : ℕ → ℝ := fun k => Q[truncSq D (ε * n) k | ℱ k] ω with hc
    set L := lindAvg Q ℱ D ε n ω with hL
    have hsumB : ∑ k ∈ Finset.range n, Q[bigSq D (ε * n) k | ℱ k] ω = n * L := by
      simp only [hL, lindAvg]; field_simp
    have hcsum : ∑ k ∈ Finset.range n, |c k| ≤ n * L / √(ε * n) := by
      rw [← hsumB, Finset.sum_div]
      exact Finset.sum_le_sum fun k _ => (hω' k).1
    have hL0 : L < ℓ0 := (le_abs_self L).trans_lt hla
    -- the clock stays in the band
    have hband : ∀ j ≤ n, |ctClock Q ℱ D (ε * n) j ω - j| ≤ θ * n := by
      intro j hj
      have hcd' : (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun j => |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j|) < θ / 2 * n := by
        have := (le_abs_self _).trans_lt hcd
        rwa [clockDev, div_lt_iff₀ hn0] at this
      have h1 : |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j| < θ / 2 * n :=
        (Finset.le_sup' (fun j => |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j|)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hj))).trans_lt hcd'
      have h2 : |ctClock Q ℱ D (ε * n) j ω - ∑ i ∈ Finset.range j,
          Q[fun ω => D i ω ^ 2 | ℱ i] ω| ≤ ∑ i ∈ Finset.range n,
            (Q[bigSq D (ε * n) i | ℱ i] ω + c i ^ 2) := by
        rw [ctClock, ← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => (hω' i).2).trans ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hj)
          fun i _ _ => ?_
        exact le_trans (abs_nonneg _) (hω' i).2
      have h3 : ∑ i ∈ Finset.range n, c i ^ 2 ≤ n * (L ^ 2 / ε) := by
        have e1 : ∑ i ∈ Finset.range n, c i ^ 2 = ∑ i ∈ Finset.range n, |c i| ^ 2 :=
          Finset.sum_congr rfl fun i _ => (sq_abs _).symm
        rw [e1]
        refine (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _).trans ?_
        have hc0 : 0 ≤ ∑ i ∈ Finset.range n, |c i| := Finset.sum_nonneg fun i _ => abs_nonneg _
        calc (∑ i ∈ Finset.range n, |c i|) ^ 2 ≤ (n * L / √(ε * n)) ^ 2 :=
              pow_le_pow_left₀ hc0 hcsum 2
          _ = n * (L ^ 2 / ε) := by
              rw [div_pow, Real.sq_sqrt ha.le]; field_simp
      have hL2' : L ^ 2 < ε * (θ / 4) := by
        have h := hla.trans_le (min_le_right _ _ |>.trans (min_le_left _ _))
        have h' := (sq_lt_sq' (by linarith [abs_nonneg L]) h)
        rwa [sq_abs, Real.sq_sqrt (by positivity)] at h'
      have h4 : L ≤ θ / 4 := hL0.le.trans (min_le_left _ _)
      have h5 : n * (L ^ 2 / ε) ≤ n * (θ / 4) :=
        mul_le_mul_of_nonneg_left (by rw [div_le_iff₀ hε]; linarith) hn0.le
      rw [Finset.sum_add_distrib, hsumB] at h2
      calc |ctClock Q ℱ D (ε * n) j ω - j|
          ≤ |ctClock Q ℱ D (ε * n) j ω - ∑ i ∈ Finset.range j,
              Q[fun ω => D i ω ^ 2 | ℱ i] ω| +
            |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j| := abs_sub_le _ _ _
        _ ≤ θ * n := by nlinarith
    have hact := (activeW_props Q ℱ D (ε * n) (θ * n) (by positivity)).2.2.2.2 n ω hband
    -- the increments agree up to the recentring
    have hinc : ∀ k < n, locInc Q ℱ D (ε * n) (θ * n) k ω - D k ω = -c k := by
      intro k hk
      simp only [locInc, ctrunc, Pi.sub_apply, hact k hk, one_mul, hc, truncSq,
        hsmall k hk, ↓reduceIte]
      ring
    have hnorm : ‖mPath (fun l ω => locInc Q ℱ D (ε * n) (θ * n) l ω) n ω - mPath D n ω‖ ≤
        (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, |c k| := by
      rw [mPath, mPath, ← polygonal_sub]
      refine norm_polygonal_le fun k hk => ?_
      simp only [Pi.sub_apply]
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.2 hsn)]
      refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hsn).le
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hkn : Finset.range k ⊆ Finset.range n := Finset.range_subset_range.2 hk
      rcases Nat.lt_or_eq_of_le hk with hlt | heq
      · refine (Finset.sum_le_sum fun l hl => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
          hkn fun i _ _ => abs_nonneg _)
        rw [hinc l ((Finset.mem_range.1 hl).trans hlt), abs_neg]
      · subst heq
        exact (Finset.sum_le_sum fun l hl => by
          rw [hinc l (Finset.mem_range.1 hl), abs_neg])
    have hfin : (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, |c k| < κ := by
      calc (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, |c k| ≤ (√(n : ℝ))⁻¹ * (n * L / √(ε * n)) :=
            mul_le_mul_of_nonneg_left hcsum (inv_pos.2 hsn).le
        _ = L / √ε := by
            rw [hsa]; field_simp; rw [Real.sq_sqrt hn0.le]
        _ < κ := by
            rw [div_lt_iff₀ hsε]
            exact hL0.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    exact absurd (hbad.trans hnorm) (not_le.2 hfin)
  calc Q.real {ω | κ ≤ ‖mPath (fun l ω => locInc Q ℱ D (ε * n) (θ * n) l ω) n ω - mPath D n ω‖}
      ≤ Q.real ({ω | ∃ k < n, ε * n ≤ D k ω ^ 2} ∪ {ω | θ / 2 ≤ |clockDev Q ℱ D n ω|} ∪
        {ω | ℓ0 ≤ |lindAvg Q ℱ D ε n ω|}) :=
        ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono_ae hsub)
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)

/-! ### Tightness -/

/-- **The block bound for the localised increments**: for `a > 0`, `τ ≥ 0`, every block start
`j`, length `L` and `x > 0`,
`P(max_{i≤L} |Σ_{l<i} locInc_{j+l}| ≥ x) ≤ (8(L + 2τ)² + 12a(L + 2τ))/x⁴`. -/
theorem measureReal_block_max_locInc_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {a τ : ℝ} (ha : 0 < a)
    (hτ : 0 ≤ τ) (j L : ℕ) {x : ℝ} (hx : 0 < x) :
    Q.real {ω | x ≤ (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one
      fun i => |∑ l ∈ Finset.range i, locInc Q ℱ D a τ (j + l) ω|} ≤
      (8 * (L + 2 * τ) ^ 2 + 12 * a * (L + 2 * τ)) / x ^ 4 := by
  set G := shiftFiltration ℱ j with hG
  set d : ℕ → Ω → ℝ := fun i => locInc Q ℱ D a τ (j + i) with hd
  have hp := fun i => locInc_props hD hL2 h0 ha hτ (j + i)
  have hdF : ∀ i, StronglyMeasurable[G (i + 1)] (d i) := fun i => (hp i).1
  have hd0 : ∀ i, Q[d i | G i] =ᵐ[Q] 0 := fun i => (hp i).2.2.1
  have hdb : ∀ i, ∀ᵐ ω ∂Q, |d i ω| ≤ 2 * √a := fun i => (hp i).2.1
  have hdm : ∀ i, Measurable (d i) := fun i => (hdF i).measurable.mono (G.le (i + 1)) le_rfl
  have hclock : ∀ᵐ ω ∂Q, ∑ i ∈ Finset.range L, Q[fun ω => d i ω ^ 2 | G i] ω ≤ L + 2 * τ := by
    filter_upwards [ae_all_iff.2 fun i => (hp i).2.2.2.1] with ω hω
    calc ∑ i ∈ Finset.range L, Q[fun ω => d i ω ^ 2 | G i] ω
        = ∑ i ∈ Finset.range L, activeW Q ℱ D a τ (j + i) ω * cvar Q ℱ D a (j + i) ω :=
          Finset.sum_congr rfl fun i _ => hω i
      _ ≤ L + 2 * τ := sum_activeW_mul_cvar_le Q ℱ D a hτ j L ω
  have h4 := integral_pow_four_sum_le_clock hdF hd0 hdb L (by positivity) hclock
  have hM := martingale_partialSum hdF (fun i => ((hp i).2.2.2.2).integrable one_le_two) hd0
  have hD := measureReal_sup_abs_ge_le hM (p := 4) (by decide)
    (fun i => integrable_pow_sum_of_bdd hdm hdb 4 i) hx L
  refine hD.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  have e : (2 * √a) ^ 2 = 4 * a := by rw [mul_pow, Real.sq_sqrt ha.le]; ring
  calc ∫ ω, (∑ i ∈ Finset.range L, d i ω) ^ 4 ∂Q
      ≤ 8 * (L + 2 * τ) ^ 2 + 3 * (2 * √a) ^ 2 * (L + 2 * τ) := h4
    _ = 8 * (L + 2 * τ) ^ 2 + 12 * a * (L + 2 * τ) := by rw [e]; ring

/-- **Tightness of `n^{−1/2} mₙ` under (D.8) and (D.9)** (the modulus condition): for every
`ε', η > 0` there are `δ > 0` and `N` with `P(w(n^{−1/2} mₙ, δ) ≥ ε') ≤ η` for `n ≥ N`. -/
theorem modulus_condition_mPath {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hcv : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 1))
    (hlin : ∀ ε > 0, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => lindAvg Q ℱ D ε n ω) atTop (𝓝 0)) :
    ∀ ε' : ℝ, 0 < ε' → ∀ η : ℝ≥0∞, 0 < η → ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
      Q {ω | ε' ≤ modulus (mPath D n ω) δ} ≤ η := by
  intro ε' hε' η hη
  by_cases hηt : η = ⊤
  · exact ⟨1, one_pos, 0, fun n _ => hηt ▸ le_top⟩
  have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηt
  set η' := η.toReal with hη'
  set c := ε' / 8 with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (512 / (c ^ 4 * η'))
  have hm0 : 0 < m := Nat.cast_pos.1 ((by positivity : (0 : ℝ) < 512 / (c ^ 4 * η')).trans hm)
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  set ε := c ^ 4 * η' / 192 with hε
  have hε0 : 0 < ε := by positivity
  set θ := 1 / (m : ℝ) with hθ
  have hθ0 : 0 < θ := by positivity
  have hapx := tendsto_measureReal_norm_mPath_locInc_sub hD hL2 h0 hcv hε0 hθ0 (hlin ε hε0)
    (show 0 < ε' / 4 by positivity)
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 hapx) (η' / 2) (by positivity)
  refine ⟨1 / m, by positivity, max N₁ m, fun n hn => ?_⟩
  have hnm : m ≤ n := le_of_max_le_right hn
  have hn1 : 1 ≤ n := hm0.trans_le hnm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnm' : (m : ℝ) ≤ n := by exact_mod_cast hnm
  have ha : 0 < ε * n := by positivity
  set S : ℕ → Ω → ℝ := fun k ω => ∑ l ∈ Finset.range k,
    locInc Q ℱ D (ε * n) (θ * n) l ω with hS
  -- the block condition for the localised process
  have hblock : ∀ j : ℕ, (m : ℝ≥0∞) *
      Q {ω | ∃ i ≤ n / m + 1, c * √(n : ℝ) ≤ |S (j + i) ω - S j ω|} ≤
        ENNReal.ofReal (η' / 2) := by
    intro j
    set L := n / m + 1 with hL
    have hLb : (L : ℝ) ≤ 2 * n / m := by
      have h1 : ((n / m : ℕ) : ℝ) ≤ n / m := Nat.cast_div_le
      have h2 : (1 : ℝ) ≤ n / m := by rw [le_div_iff₀ hm0']; linarith
      have : (L : ℝ) = ((n / m : ℕ) : ℝ) + 1 := by rw [hL]; push_cast; ring
      rw [this]
      calc ((n / m : ℕ) : ℝ) + 1 ≤ n / m + n / m := add_le_add h1 h2
        _ = 2 * n / m := by ring
    have hcB : (L : ℝ) + 2 * (θ * n) ≤ 4 * n / m := by
      rw [hθ]
      calc (L : ℝ) + 2 * (1 / m * n) ≤ 2 * n / m + 2 * n / m := by
            have : 2 * (1 / (m : ℝ) * n) = 2 * n / m := by ring
            linarith
        _ = 4 * n / m := by ring
    have hsub : {ω | ∃ i ≤ L, c * √(n : ℝ) ≤ |S (j + i) ω - S j ω|} ⊆
        {ω | c * √(n : ℝ) ≤ (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one
          fun i => |∑ l ∈ Finset.range i, locInc Q ℱ D (ε * n) (θ * n) (j + l) ω|} := by
      rintro ω ⟨i, hi, hle⟩
      simp only [mem_ofPred_eq]
      simp only [hS] at hle
      rw [Finset.sum_range_add, add_sub_cancel_left] at hle
      exact hle.trans (Finset.le_sup' (fun i => |∑ l ∈ Finset.range i,
        locInc Q ℱ D (ε * n) (θ * n) (j + l) ω|) (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
    have hb := measureReal_block_max_locInc_le hD hL2 h0 ha (by positivity : 0 ≤ θ * n) j L
      (show 0 < c * √(n : ℝ) by positivity)
    have hx4 : (c * √(n : ℝ)) ^ 4 = c ^ 4 * n ^ 2 := by
      rw [mul_pow, show (√(n : ℝ)) ^ 4 = ((√(n : ℝ)) ^ 2) ^ 2 by ring, Real.sq_sqrt hn0.le]
    have hbound : (m : ℝ) * ((8 * (L + 2 * (θ * n)) ^ 2 + 12 * (ε * n) * (L + 2 * (θ * n))) /
        (c * √(n : ℝ)) ^ 4) ≤ η' / 2 := by
      rw [hx4]
      have hB0 : 0 ≤ (L : ℝ) + 2 * (θ * n) := by positivity
      have e1 : 8 * ((L : ℝ) + 2 * (θ * n)) ^ 2 ≤ 8 * (4 * n / m) ^ 2 := by
        gcongr
      have e2 : 12 * (ε * n) * ((L : ℝ) + 2 * (θ * n)) ≤ 12 * (ε * n) * (4 * n / m) := by
        gcongr
      have e3 : (m : ℝ) * ((8 * (4 * n / m) ^ 2 + 12 * (ε * n) * (4 * n / m)) / (c ^ 4 * n ^ 2))
          = 128 / (m * c ^ 4) + 48 * ε / c ^ 4 := by
        field_simp; ring
      have e4 : 128 / (m * c ^ 4) ≤ η' / 4 := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ (by positivity)] at hm
        nlinarith
      have e5 : 48 * ε / c ^ 4 = η' / 4 := by rw [hε]; field_simp; ring
      calc (m : ℝ) * ((8 * (L + 2 * (θ * n)) ^ 2 + 12 * (ε * n) * (L + 2 * (θ * n))) /
            (c ^ 4 * n ^ 2))
          ≤ (m : ℝ) * ((8 * (4 * n / m) ^ 2 + 12 * (ε * n) * (4 * n / m)) / (c ^ 4 * n ^ 2)) := by
            gcongr
        _ ≤ η' / 2 := by rw [e3]; linarith
    calc (m : ℝ≥0∞) * Q {ω | ∃ i ≤ L, c * √(n : ℝ) ≤ |S (j + i) ω - S j ω|}
        ≤ (m : ℝ≥0∞) * Q {ω | c * √(n : ℝ) ≤ (Finset.range (L + 1)).sup'
          Finset.nonempty_range_add_one
          fun i => |∑ l ∈ Finset.range i, locInc Q ℱ D (ε * n) (θ * n) (j + l) ω|} := by
          gcongr
      _ = ENNReal.ofReal (m * Q.real {ω | c * √(n : ℝ) ≤ (Finset.range (L + 1)).sup'
          Finset.nonempty_range_add_one
          fun i => |∑ l ∈ Finset.range i, locInc Q ℱ D (ε * n) (θ * n) (j + l) ω|}) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast, ofReal_measureReal]
      _ ≤ ENNReal.ofReal (η' / 2) := ENNReal.ofReal_le_ofReal
          ((mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg m)).trans hbound)
  have hmod := measure_modulus_polygonal_le Q S hn1 hm0 (ε := ε' / 2) (c := c)
    (by rw [hc]; linarith) hblock
  -- comparison of the moduli
  have hsub : {ω | ε' ≤ modulus (mPath D n ω) (1 / m)} ⊆
      {ω | ε' / 2 ≤ modulus (polygonal n (fun k => (√(n : ℝ))⁻¹ * S k ω)) (1 / m)} ∪
      {ω | ε' / 4 ≤ ‖mPath (fun l ω => locInc Q ℱ D (ε * n) (θ * n) l ω) n ω - mPath D n ω‖} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union] at hω ⊢
    by_contra hne
    push Not at hne
    have h1 := abs_modulus_sub_le (mPath D n ω)
      (mPath (fun l ω => locInc Q ℱ D (ε * n) (θ * n) l ω) n ω) (1 / m)
    rw [norm_sub_rev] at h1
    have h2 : modulus (mPath (fun l ω => locInc Q ℱ D (ε * n) (θ * n) l ω) n ω) (1 / m) =
        modulus (polygonal n (fun k => (√(n : ℝ))⁻¹ * S k ω)) (1 / m) := rfl
    rw [h2] at h1
    have := (abs_sub_lt_iff.1 (h1.trans_lt (by linarith [hne.2] :
      2 * ‖mPath (fun l ω => locInc Q ℱ D (ε * n) (θ * n) l ω) n ω - mPath D n ω‖ < ε' / 2))).1
    linarith [hne.1]
  have h3 : Q {ω | ε' / 4 ≤
      ‖mPath (fun l ω => locInc Q ℱ D (ε * n) (θ * n) l ω) n ω - mPath D n ω‖} ≤
      ENNReal.ofReal (η' / 2) := by
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hN₁ n (le_of_max_le_left hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at this
    exact this.le
  calc Q {ω | ε' ≤ modulus (mPath D n ω) (1 / m)}
      ≤ Q ({ω | ε' / 2 ≤ modulus (polygonal n (fun k => (√(n : ℝ))⁻¹ * S k ω)) (1 / m)} ∪
        {ω | ε' / 4 ≤ ‖mPath (fun l ω => locInc Q ℱ D (ε * n) (θ * n) l ω) n ω -
          mPath D n ω‖}) := measure_mono hsub
    _ ≤ ENNReal.ofReal (η' / 2) + ENNReal.ofReal (η' / 2) :=
        (measure_union_le _ _).trans (add_le_add hmod h3)
    _ = η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves, hη',
          ENNReal.ofReal_toReal hηt]

/-! ### The squared increments: the law of large numbers in probability -/

/-- Convergence in probability to `0` from the real-measure form. -/
theorem tendstoInMeasure_of_measureReal {Q : Measure Ω} [IsFiniteMeasure Q] {f : ℕ → Ω → ℝ}
    (h : ∀ κ > 0, Tendsto (fun n => Q.real {ω | κ ≤ |f n ω|}) atTop (𝓝 0)) :
    TendstoInMeasure Q f atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro κ hκ
  have h1 := ENNReal.tendsto_ofReal (h κ hκ)
  rw [ENNReal.ofReal_zero] at h1
  refine h1.congr fun n => ?_
  rw [ofReal_measureReal]
  congr 1
  ext ω
  simp [Real.norm_eq_abs]

/-- Chebyshev's inequality: `x² P(|T| ≥ x) ≤ E[T²]`. -/
theorem sq_mul_measureReal_le {Q : Measure Ω} [IsFiniteMeasure Q] {T : Ω → ℝ}
    (hT : MemLp T 2 Q) {x : ℝ} (hx : 0 < x) :
    x ^ 2 * Q.real {ω | x ≤ |T ω|} ≤ ∫ ω, T ω ^ 2 ∂Q := by
  have h1 := mul_meas_ge_le_integral_of_nonneg (μ := Q) (f := fun ω => T ω ^ 2)
    (Eventually.of_forall fun ω => sq_nonneg _) hT.integrable_sq (x ^ 2)
  have hset : {ω | x ^ 2 ≤ T ω ^ 2} = {ω | x ≤ |T ω|} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [← sq_abs (T ω)]
    exact pow_le_pow_iff_left₀ hx.le (abs_nonneg _) two_ne_zero
  rwa [hset] at h1

/-- **The martingale part of the squares**: for the localised increments `dₖ` (truncation
`a > 0`, band `τ ≥ 0`) and `m ≤ n`, `E[(Σ_{k<m} (dₖ² − E[dₖ² | 𝓕ₖ]))²] ≤ 8a(n + 2τ)`. -/
theorem integral_sq_sum_locInc_sq_sub_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {a τ : ℝ} (ha : 0 < a)
    (hτ : 0 ≤ τ) {m n : ℕ} (hmn : m ≤ n) :
    ∫ ω, (∑ k ∈ Finset.range m, (locInc Q ℱ D a τ k ω ^ 2 -
      Q[fun ω => locInc Q ℱ D a τ k ω ^ 2 | ℱ k] ω)) ^ 2 ∂Q ≤ 8 * a * (n + 2 * τ) := by
  have hp := fun k => locInc_props hD hL2 h0 ha hτ k
  set d := fun k => locInc Q ℱ D a τ k with hd
  set q : ℕ → Ω → ℝ := fun k => Q[fun ω => d k ω ^ 2 | ℱ k] with hq
  set e : ℕ → Ω → ℝ := fun k ω => d k ω ^ 2 - q k ω with he
  have hdm : ∀ k, Measurable (d k) := fun k => (hp k).1.measurable.mono (ℱ.le (k + 1)) le_rfl
  have hd2b : ∀ k, ∀ᵐ ω ∂Q, d k ω ^ 2 ≤ 4 * a := fun k => by
    filter_upwards [(hp k).2.1] with ω hω
    have : (2 * √a) ^ 2 = 4 * a := by rw [mul_pow, Real.sq_sqrt ha.le]; ring
    rw [← this, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hd2i : ∀ k, Integrable (fun ω => d k ω ^ 2) Q := fun k => ((hp k).2.2.2.2).integrable_sq
  have hq0 : ∀ k, ∀ᵐ ω ∂Q, 0 ≤ q k ω := fun k =>
    (condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg (d k ω))).mono fun ω h => by
      simpa using h
  have hqb : ∀ k, ∀ᵐ ω ∂Q, |q k ω| ≤ 4 * a := fun k =>
    ae_bdd_abs_condExp_of_ae_bdd_abs (μ := Q) (m := ℱ k) (R := 4 * a) ((hd2b k).mono
      fun ω h => by rw [abs_of_nonneg (sq_nonneg _)]; exact h)
  have heb : ∀ k, ∀ᵐ ω ∂Q, |e k ω| ≤ 4 * a := fun k => by
    filter_upwards [hd2b k, hq0 k, hqb k] with ω h1 h2 h3
    simp only [he]
    rw [abs_le]; rw [abs_le] at h3
    constructor <;> nlinarith [sq_nonneg (d k ω)]
  have heF : ∀ k, StronglyMeasurable[ℱ (k + 1)] (e k) := fun k =>
    (((hp k).1.measurable.pow_const 2).sub ((stronglyMeasurable_condExp (m := ℱ k) (μ := Q)
      (f := fun ω => d k ω ^ 2)).measurable.mono (ℱ.mono (Nat.le_succ k)) le_rfl))
      |>.stronglyMeasurable
  have hem : ∀ k, Measurable (e k) := fun k => (heF k).measurable.mono (ℱ.le (k + 1)) le_rfl
  have heL2 : ∀ k, MemLp (e k) 2 Q := fun k =>
    MemLp.of_bound (hem k).aestronglyMeasurable (4 * a) ((heb k).mono fun ω h => by
      rwa [Real.norm_eq_abs])
  have he0 : ∀ k, Q[e k | ℱ k] =ᵐ[Q] 0 := fun k => by
    have h1 : Q[e k | ℱ k] =ᵐ[Q] Q[fun ω => d k ω ^ 2 | ℱ k] - Q[q k | ℱ k] :=
      condExp_sub (hd2i k) integrable_condExp _
    have h2 : Q[q k | ℱ k] = q k :=
      condExp_of_stronglyMeasurable (ℱ.le k) stronglyMeasurable_condExp integrable_condExp
    filter_upwards [h1] with ω e1
    rw [e1, h2, Pi.sub_apply, Pi.zero_apply]
    simp only [hq, sub_self]
  rw [integral_sq_sum_of_martingale heF heL2 he0 m]
  have hee : ∀ k, ∫ ω, e k ω ^ 2 ∂Q ≤ 8 * a * ∫ ω, d k ω ^ 2 ∂Q := fun k => by
    have hEq : ∫ ω, q k ω ∂Q = ∫ ω, d k ω ^ 2 ∂Q := integral_condExp (ℱ.le k)
    calc ∫ ω, e k ω ^ 2 ∂Q ≤ ∫ ω, 4 * a * (d k ω ^ 2 + q k ω) ∂Q := by
          refine integral_mono_ae (heL2 k).integrable_sq
            (((hd2i k).add integrable_condExp).const_mul _) ?_
          filter_upwards [heb k, hq0 k] with ω h1 h2
          have h3 : |e k ω| ≤ d k ω ^ 2 + q k ω := by
            simp only [he]
            rw [abs_le]; constructor <;> nlinarith [sq_nonneg (d k ω)]
          calc e k ω ^ 2 = |e k ω| * |e k ω| := by rw [← sq, sq_abs]
            _ ≤ 4 * a * (d k ω ^ 2 + q k ω) := mul_le_mul h1 h3 (abs_nonneg _) (by positivity)
      _ = 8 * a * ∫ ω, d k ω ^ 2 ∂Q := by
          rw [integral_const_mul, integral_add (hd2i k) integrable_condExp, hEq]; ring
  have hsumd : ∑ k ∈ Finset.range n, ∫ ω, d k ω ^ 2 ∂Q ≤ n + 2 * τ := by
    have e1 : ∀ k, ∫ ω, d k ω ^ 2 ∂Q =
        ∫ ω, activeW Q ℱ D a τ k ω * cvar Q ℱ D a k ω ∂Q := fun k => by
      rw [← integral_condExp (ℱ.le k)]
      exact integral_congr_ae (hp k).2.2.2.1
    simp_rw [e1]
    have hint : ∀ k, Integrable (fun ω => activeW Q ℱ D a τ k ω * cvar Q ℱ D a k ω) Q :=
      fun k => by
        refine (integrable_condExp (m := ℱ k) (f := fun ω => d k ω ^ 2)).congr ?_
        exact (hp k).2.2.2.1
    rw [← integral_finsetSum _ fun k _ => hint k]
    calc ∫ ω, ∑ k ∈ Finset.range n, activeW Q ℱ D a τ k ω * cvar Q ℱ D a k ω ∂Q
        ≤ ∫ _, ((n : ℝ) + 2 * τ) ∂Q := integral_mono (integrable_finsetSum _ fun k _ => hint k)
          (integrable_const _) fun ω => by
            have := sum_activeW_mul_cvar_le Q ℱ D a hτ 0 n ω
            simpa using this
      _ = n + 2 * τ := by simp
  calc ∑ k ∈ Finset.range m, ∫ ω, e k ω ^ 2 ∂Q ≤ ∑ k ∈ Finset.range m, 8 * a * ∫ ω, d k ω ^ 2 ∂Q :=
        Finset.sum_le_sum fun k _ => hee k
    _ ≤ ∑ k ∈ Finset.range n, 8 * a * ∫ ω, d k ω ^ 2 ∂Q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmn) fun k _ _ =>
          mul_nonneg (by positivity) (integral_nonneg fun ω => sq_nonneg _)
    _ = 8 * a * ∑ k ∈ Finset.range n, ∫ ω, d k ω ^ 2 ∂Q := by rw [Finset.mul_sum]
    _ ≤ 8 * a * (n + 2 * τ) := mul_le_mul_of_nonneg_left hsumd (by positivity)

/-- **The good event** (pathwise): if no `Dₖ²`, `k < n`, reaches `εn`, the clock deviation is
below `θ/2` and the Lindeberg average `L` satisfies `L ≤ θ/4`, `L² ≤ εθ/4`, then (given the almost
sure bounds of `ctrunc_props`) all stopping weights `k < n` are `1`, the localised increments are
`Dₖ − E[Dₖ 1{Dₖ² < εn} | 𝓕ₖ]`, the recentring terms sum to at most `nL/√(εn)`, and the
conditional variances deviate from `E[Dₖ² | 𝓕ₖ]` by at most `n(L + L²/ε)` in total. -/
theorem locInc_good_event {Q : Measure Ω} {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} {ε θ : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) {n : ℕ} (hn : 1 ≤ n) {ω : Ω}
    (hω : ∀ k, |Q[truncSq D (ε * n) k | ℱ k] ω| ≤ Q[bigSq D (ε * n) k | ℱ k] ω / √(ε * n) ∧
      |cvar Q ℱ D (ε * n) k ω - Q[fun ω => D k ω ^ 2 | ℱ k] ω| ≤
        Q[bigSq D (ε * n) k | ℱ k] ω + Q[truncSq D (ε * n) k | ℱ k] ω ^ 2)
    (hsmall : ∀ k < n, D k ω ^ 2 < ε * n) (hcd : |clockDev Q ℱ D n ω| < θ / 2)
    (hL1 : lindAvg Q ℱ D ε n ω ≤ θ / 4) (hL2 : lindAvg Q ℱ D ε n ω ^ 2 ≤ ε * (θ / 4)) :
    (∀ k < n, activeW Q ℱ D (ε * n) (θ * n) k ω = 1) ∧
      (∀ k < n, locInc Q ℱ D (ε * n) (θ * n) k ω = D k ω - Q[truncSq D (ε * n) k | ℱ k] ω) ∧
      ∑ k ∈ Finset.range n, |Q[truncSq D (ε * n) k | ℱ k] ω| ≤
        n * lindAvg Q ℱ D ε n ω / √(ε * n) ∧
      ∑ k ∈ Finset.range n, |cvar Q ℱ D (ε * n) k ω - Q[fun ω => D k ω ^ 2 | ℱ k] ω| ≤
        n * (lindAvg Q ℱ D ε n ω + lindAvg Q ℱ D ε n ω ^ 2 / ε) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < ε * n := mul_pos hε hn0
  set c : ℕ → ℝ := fun k => Q[truncSq D (ε * n) k | ℱ k] ω with hc
  set L := lindAvg Q ℱ D ε n ω with hL
  have hsumB : ∑ k ∈ Finset.range n, Q[bigSq D (ε * n) k | ℱ k] ω = n * L := by
    simp only [hL, lindAvg]; field_simp
  have hcsum : ∑ k ∈ Finset.range n, |c k| ≤ n * L / √(ε * n) := by
    rw [← hsumB, Finset.sum_div]
    exact Finset.sum_le_sum fun k _ => (hω k).1
  have hc2 : ∑ i ∈ Finset.range n, c i ^ 2 ≤ n * (L ^ 2 / ε) := by
    have e1 : ∑ i ∈ Finset.range n, c i ^ 2 = ∑ i ∈ Finset.range n, |c i| ^ 2 :=
      Finset.sum_congr rfl fun i _ => (sq_abs _).symm
    rw [e1]
    refine (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _).trans ?_
    have hc0 : 0 ≤ ∑ i ∈ Finset.range n, |c i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    calc (∑ i ∈ Finset.range n, |c i|) ^ 2 ≤ (n * L / √(ε * n)) ^ 2 :=
          pow_le_pow_left₀ hc0 hcsum 2
      _ = n * (L ^ 2 / ε) := by
          rw [div_pow, Real.sq_sqrt ha.le]; field_simp
  have hdev : ∑ k ∈ Finset.range n, |cvar Q ℱ D (ε * n) k ω - Q[fun ω => D k ω ^ 2 | ℱ k] ω| ≤
      n * (L + L ^ 2 / ε) := by
    refine (Finset.sum_le_sum fun k _ => (hω k).2).trans ?_
    rw [Finset.sum_add_distrib, hsumB]
    nlinarith
  have hband : ∀ j ≤ n, |ctClock Q ℱ D (ε * n) j ω - j| ≤ θ * n := by
    intro j hj
    have hcd' : (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun j => |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j|) < θ / 2 * n := by
      have := (le_abs_self _).trans_lt hcd
      rwa [clockDev, div_lt_iff₀ hn0] at this
    have h1 : |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j| < θ / 2 * n :=
      (Finset.le_sup' (fun j => |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j|)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj))).trans_lt hcd'
    have h2 : |ctClock Q ℱ D (ε * n) j ω - ∑ i ∈ Finset.range j,
        Q[fun ω => D i ω ^ 2 | ℱ i] ω| ≤ n * (L + L ^ 2 / ε) := by
      rw [ctClock, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hdev)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hj)
        fun i _ _ => abs_nonneg _
    have h5 : n * (L + L ^ 2 / ε) ≤ n * (θ / 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hn0.le
      have : L ^ 2 / ε ≤ θ / 4 := by rw [div_le_iff₀ hε]; linarith
      linarith
    calc |ctClock Q ℱ D (ε * n) j ω - j|
        ≤ |ctClock Q ℱ D (ε * n) j ω - ∑ i ∈ Finset.range j,
            Q[fun ω => D i ω ^ 2 | ℱ i] ω| +
          |∑ i ∈ Finset.range j, Q[fun ω => D i ω ^ 2 | ℱ i] ω - j| := abs_sub_le _ _ _
      _ ≤ θ * n := by nlinarith
  have hact := (activeW_props Q ℱ D (ε * n) (θ * n) (by positivity)).2.2.2.2 n ω hband
  refine ⟨hact, fun k hk => ?_, hcsum, hdev⟩
  simp only [locInc, ctrunc, Pi.sub_apply, hact k hk, one_mul, truncSq, hsmall k hk,
    ↓reduceIte]

/-- Chebyshev's inequality for the martingale part of the squares of the localised increments:
`P(|(1/n) Σ_{k<m} (dₖ² − E[dₖ² | 𝓕ₖ])| ≥ x) ≤ 24ρ/x²` for truncation `ρn`, band `n`, `m ≤ n`. -/
theorem measureReal_sq_martingale_part_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {ρ : ℝ} (hρ0 : 0 < ρ)
    {n m : ℕ} (hn1 : 1 ≤ n) (hmn : m ≤ n) {x : ℝ} (hx : 0 < x) :
    Q.real {ω | x ≤ |(∑ k ∈ Finset.range m, (locInc Q ℱ D (ρ * n) (1 * n) k ω ^ 2 -
      Q[fun ω => locInc Q ℱ D (ρ * n) (1 * n) k ω ^ 2 | ℱ k] ω)) / (n : ℝ)|} ≤
      24 * ρ / x ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have ha : 0 < ρ * n := mul_pos hρ0 hn0
  have hτ : (0 : ℝ) ≤ 1 * n := by positivity
  set d : ℕ → Ω → ℝ := fun k => locInc Q ℱ D (ρ * n) (1 * n) k with hd
  have hp := fun k => locInc_props hD hL2 h0 ha hτ k
  set T : Ω → ℝ := fun ω => (∑ k ∈ Finset.range m,
    (d k ω ^ 2 - Q[fun ω => d k ω ^ 2 | ℱ k] ω)) / (n : ℝ) with hT
  have hdm : ∀ k, Measurable (d k) := fun k => (hp k).1.measurable.mono (ℱ.le (k + 1)) le_rfl
  have hd2 : ∀ k, ∀ᵐ ω ∂Q, d k ω ^ 2 ≤ 4 * (ρ * n) := fun k => by
    filter_upwards [(hp k).2.1] with ω h
    have : (2 * √(ρ * n)) ^ 2 = 4 * (ρ * n) := by rw [mul_pow, Real.sq_sqrt ha.le]; ring
    rw [← this, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hqb : ∀ k, ∀ᵐ ω ∂Q, |Q[fun ω => d k ω ^ 2 | ℱ k] ω| ≤ 4 * (ρ * n) := fun k =>
    ae_bdd_abs_condExp_of_ae_bdd_abs (μ := Q) (m := ℱ k) (R := 4 * (ρ * n))
      ((hd2 k).mono fun ω h => by rw [abs_of_nonneg (sq_nonneg _)]; exact h)
  have hTL2 : MemLp T 2 Q := by
    refine MemLp.of_bound (((Finset.measurable_sum _ fun k _ => ((hdm k).pow_const 2).sub
      ((stronglyMeasurable_condExp.measurable).mono (ℱ.le k) le_rfl)).div_const _)
      |>.aestronglyMeasurable) (m * (8 * (ρ * n)) / n) ?_
    filter_upwards [ae_all_iff.2 hd2, ae_all_iff.2 hqb] with ω h1 h2
    rw [Real.norm_eq_abs, hT, abs_div, abs_of_pos hn0]
    refine div_le_div_of_nonneg_right ?_ hn0.le
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range m, |d k ω ^ 2 - Q[fun ω => d k ω ^ 2 | ℱ k] ω|
        ≤ ∑ _k ∈ Finset.range m, 8 * (ρ * n) := Finset.sum_le_sum fun k _ => by
          have e2 := h2 k
          have e1 := h1 k
          rw [abs_le] at e2 ⊢
          constructor <;> nlinarith [sq_nonneg (d k ω)]
      _ = m * (8 * (ρ * n)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hTsq : ∫ ω, T ω ^ 2 ∂Q ≤ 24 * ρ := by
    have h1 := integral_sq_sum_locInc_sq_sub_le hD hL2 h0 ha hτ hmn
    have e : ∫ ω, T ω ^ 2 ∂Q = (∫ ω, (∑ k ∈ Finset.range m,
        (d k ω ^ 2 - Q[fun ω => d k ω ^ 2 | ℱ k] ω)) ^ 2 ∂Q) / n ^ 2 := by
      rw [← integral_div]; congr 1; ext ω; simp only [hT, div_pow]
    rw [e, div_le_iff₀ (by positivity)]
    calc ∫ ω, (∑ k ∈ Finset.range m, (d k ω ^ 2 - Q[fun ω => d k ω ^ 2 | ℱ k] ω)) ^ 2 ∂Q
        ≤ 8 * (ρ * n) * (n + 2 * (1 * n)) := h1
      _ = 24 * ρ * n ^ 2 := by ring
  have h1 := sq_mul_measureReal_le hTL2 hx
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact h1.trans hTsq

/-- The pathwise decomposition behind `tendstoInMeasure_sum_floor_sq_sub_of_lindeberg`: on the
good event, `(1/n) Σ_{k<m} Dₖ² − t` differs from the martingale part `T` plus `R` (the
compensator average minus `t`) by at most `η/20 + η/8`. -/
theorem abs_avg_sq_sub_lt_of_good {Q : Measure Ω} {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ}
    {ρ η t : ℝ} (hρ0 : 0 < ρ) (hη : 0 < η) {n m : ℕ} (hn1 : 1 ≤ n) (hmn : m ≤ n) {ω : Ω}
    (hω : ∀ k, (|Q[truncSq D (ρ * n) k | ℱ k] ω| ≤ Q[bigSq D (ρ * n) k | ℱ k] ω / √(ρ * n) ∧
      |cvar Q ℱ D (ρ * n) k ω - Q[fun ω => D k ω ^ 2 | ℱ k] ω| ≤
        Q[bigSq D (ρ * n) k | ℱ k] ω + Q[truncSq D (ρ * n) k | ℱ k] ω ^ 2) ∧
      Q[fun ω => locInc Q ℱ D (ρ * n) (1 * n) k ω ^ 2 | ℱ k] ω =
        activeW Q ℱ D (ρ * n) (1 * n) k ω * cvar Q ℱ D (ρ * n) k ω ∧
      |locInc Q ℱ D (ρ * n) (1 * n) k ω| ≤ 2 * √(ρ * n))
    (hsmall : ∀ k < n, D k ω ^ 2 < ρ * n) (hcd : |clockDev Q ℱ D n ω| < 1 / 2)
    (hL1 : lindAvg Q ℱ D ρ n ω ≤ 1 / 4) (hL2 : lindAvg Q ℱ D ρ n ω ^ 2 ≤ ρ * (1 / 4))
    (hL3 : lindAvg Q ℱ D ρ n ω ≤ η / 40) (hL4 : lindAvg Q ℱ D ρ n ω ^ 2 ≤ ρ * η / 40)
    (hT : |(∑ k ∈ Finset.range m, (locInc Q ℱ D (ρ * n) (1 * n) k ω ^ 2 -
      Q[fun ω => locInc Q ℱ D (ρ * n) (1 * n) k ω ^ 2 | ℱ k] ω)) / (n : ℝ)| < η / 4)
    (hR : |(∑ k ∈ Finset.range m, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / (n : ℝ) - t| < η / 4) :
    |(∑ k ∈ Finset.range m, D k ω ^ 2) / (n : ℝ) - t| < η := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have ha : 0 < ρ * n := mul_pos hρ0 hn0
  obtain ⟨hact, hinc, hcsum, hdev⟩ := locInc_good_event (θ := 1) hρ0 one_pos hn1
    (fun k => (hω k).1) hsmall (by linarith [hcd]) (by linarith) hL2
  set L := lindAvg Q ℱ D ρ n ω with hL
  set d : ℕ → ℝ := fun k => locInc Q ℱ D (ρ * n) (1 * n) k ω with hd
  set c : ℕ → ℝ := fun k => Q[truncSq D (ρ * n) k | ℱ k] ω with hc
  set q : ℕ → ℝ := fun k => Q[fun ω => locInc Q ℱ D (ρ * n) (1 * n) k ω ^ 2 | ℱ k] ω with hq
  set v : ℕ → ℝ := fun k => cvar Q ℱ D (ρ * n) k ω with hv
  set V : ℕ → ℝ := fun k => Q[fun ω => D k ω ^ 2 | ℱ k] ω with hV
  have hDk : ∀ k < n, D k ω ^ 2 = (d k ^ 2 - q k) + (v k - V k) + (2 * d k * c k + c k ^ 2) +
      V k := by
    intro k hk
    have h1 : D k ω = d k + c k := by simp only [hd, hc]; rw [hinc k hk]; ring
    have h2 : q k = v k := by simp only [hq, hv]; rw [(hω k).2.1, hact k hk, one_mul]
    rw [h2, h1]
    ring
  have hsplit : (∑ k ∈ Finset.range m, D k ω ^ 2) / (n : ℝ) - t =
      (∑ k ∈ Finset.range m, (d k ^ 2 - q k)) / (n : ℝ) +
      (∑ k ∈ Finset.range m, (v k - V k)) / (n : ℝ) +
      (∑ k ∈ Finset.range m, (2 * d k * c k + c k ^ 2)) / (n : ℝ) +
      ((∑ k ∈ Finset.range m, V k) / (n : ℝ) - t) := by
    rw [Finset.sum_congr rfl fun k hk => hDk k ((Finset.mem_range.1 hk).trans_le hmn)]
    simp only [Finset.sum_add_distrib]
    ring
  have hLρ : L ^ 2 / ρ ≤ η / 40 := by rw [div_le_iff₀ hρ0]; linarith
  have hb1 : |(∑ k ∈ Finset.range m, (v k - V k)) / (n : ℝ)| ≤ η / 20 := by
    rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 hmn) fun k _ _ => abs_nonneg _).trans (hdev.trans ?_))
    nlinarith
  have hc0 : 0 ≤ ∑ k ∈ Finset.range n, |c k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hcs2 : ∑ k ∈ Finset.range n, c k ^ 2 ≤ n * (L ^ 2 / ρ) := by
    calc ∑ k ∈ Finset.range n, c k ^ 2 = ∑ k ∈ Finset.range n, |c k| ^ 2 :=
          Finset.sum_congr rfl fun k _ => (sq_abs _).symm
      _ ≤ (∑ k ∈ Finset.range n, |c k|) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
      _ ≤ (n * L / √(ρ * n)) ^ 2 := pow_le_pow_left₀ hc0 hcsum 2
      _ = n * (L ^ 2 / ρ) := by rw [div_pow, Real.sq_sqrt ha.le]; field_simp
  have hcs1 : 2 * √(ρ * n) * ∑ k ∈ Finset.range n, |c k| ≤ 2 * (n * L) := by
    calc 2 * √(ρ * n) * ∑ k ∈ Finset.range n, |c k| ≤ 2 * √(ρ * n) * (n * L / √(ρ * n)) :=
          mul_le_mul_of_nonneg_left hcsum (by positivity)
      _ = 2 * (n * L) := by field_simp
  have hb2 : |(∑ k ∈ Finset.range m, (2 * d k * c k + c k ^ 2)) / (n : ℝ)| ≤ η / 8 := by
    rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    calc |∑ k ∈ Finset.range m, (2 * d k * c k + c k ^ 2)|
        ≤ ∑ k ∈ Finset.range n, (2 * (2 * √(ρ * n)) * |c k| + c k ^ 2) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmn)
              fun k _ _ => by positivity))
          refine (abs_add_le _ _).trans ?_
          rw [abs_of_nonneg (sq_nonneg (c k)), abs_mul, abs_mul, abs_two]
          have := (hω k).2.2
          nlinarith [abs_nonneg (c k)]
      _ = 2 * (2 * √(ρ * n) * ∑ k ∈ Finset.range n, |c k|) +
          ∑ k ∈ Finset.range n, c k ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ η / 8 * n := by nlinarith
  rw [hsplit]
  set x1 := (∑ k ∈ Finset.range m, (d k ^ 2 - q k)) / (n : ℝ)
  set x2 := (∑ k ∈ Finset.range m, (v k - V k)) / (n : ℝ)
  set x3 := (∑ k ∈ Finset.range m, (2 * d k * c k + c k ^ 2)) / (n : ℝ)
  set x4 := (∑ k ∈ Finset.range m, V k) / (n : ℝ) - t
  have t1 := abs_add_le (x1 + x2 + x3) x4
  have t2 := abs_add_le (x1 + x2) x3
  have t3 := abs_add_le x1 x2
  linarith

/-- **The squares follow the clock** (from (D.8) and (D.9)): for `0 ≤ t ≤ 1`,
`(1/n) Σ_{k<⌊nt⌋} Dₖ² → t` in probability. -/
theorem tendstoInMeasure_sum_floor_sq_sub_of_lindeberg {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hcv : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 1))
    (hlin : ∀ ε > 0, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => lindAvg Q ℱ D ε n ω) atTop (𝓝 0))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TendstoInMeasure Q (fun (n : ℕ) ω =>
      (∑ k ∈ Finset.range ⌊(n : ℝ) * t⌋₊, D k ω ^ 2) / n - t) atTop 0 := by
  refine tendstoInMeasure_of_measureReal fun η hη => ?_
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ρ := δ * η ^ 2 / 768 with hρ
  have hρ0 : 0 < ρ := by positivity
  set ℓ0 := min (min (1 / 4) (√(ρ / 4))) (min (η / 40) (√(ρ * η / 40))) with hℓ0
  have hℓ0p : 0 < ℓ0 := lt_min (lt_min (by norm_num) (Real.sqrt_pos.2 (by positivity)))
    (lt_min (by positivity) (Real.sqrt_pos.2 (by positivity)))
  have hVm : ∀ k, Measurable (Q[fun ω => D k ω ^ 2 | ℱ k]) := fun k =>
    (stronglyMeasurable_condExp.measurable).mono (ℱ.le k) le_rfl
  set R : ℕ → Ω → ℝ := fun n ω =>
    (∑ k ∈ Finset.range ⌊(n : ℝ) * t⌋₊, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n - t with hR
  have hRm : ∀ n, Measurable (R n) := fun n =>
    ((Finset.measurable_sum _ fun k _ => hVm k).div_const _).sub measurable_const
  have hRae : ∀ᵐ ω ∂Q, Tendsto (fun n => R n ω) atTop (𝓝 0) := by
    filter_upwards [hcv] with ω hω
    have h := (tendsto_sum_floor_div hω ht0).sub_const t
    rw [mul_one, sub_self] at h
    exact h
  have hB1 := tendsto_measureReal_exists_big hD hL2 hρ0 (hlin ρ hρ0)
  have hB2 := tendsto_measureReal_of_ae_tendsto
    (fun n => (measurable_lindAvg_clockDev Q ℱ D ρ n).2) (ae_tendsto_clockDev hcv)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hB3 := tendsto_measureReal_of_ae_tendsto
    (fun n => (measurable_lindAvg_clockDev Q ℱ D ρ n).1) (hlin ρ hρ0) hℓ0p
  have hB4 := tendsto_measureReal_of_ae_tendsto hRm hRae (show 0 < η / 4 by positivity)
  have hsum := ((hB1.add hB2).add hB3).add hB4
  simp only [add_zero] at hsum
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hsum) (δ / 2) (by positivity)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have ha : 0 < ρ * n := mul_pos hρ0 hn0
  have hτ : (0 : ℝ) ≤ 1 * n := by positivity
  set m := ⌊(n : ℝ) * t⌋₊ with hm
  have hmn : m ≤ n := Nat.floor_le_of_le (by nlinarith)
  have hp := fun k => locInc_props hD hL2 h0 ha hτ k
  set Tset := {ω | η / 4 ≤ |(∑ k ∈ Finset.range m, (locInc Q ℱ D (ρ * n) (1 * n) k ω ^ 2 -
      Q[fun ω => locInc Q ℱ D (ρ * n) (1 * n) k ω ^ 2 | ℱ k] ω)) / (n : ℝ)|} with hTset
  have hTprob : Q.real Tset ≤ δ / 2 := by
    refine (measureReal_sq_martingale_part_le hD hL2 h0 hρ0 hn1 hmn
      (show 0 < η / 4 by positivity)).trans (le_of_eq ?_)
    rw [hρ]; field_simp; ring
  have hid : ∀ᵐ ω ∂Q, ∀ k,
      (|Q[truncSq D (ρ * n) k | ℱ k] ω| ≤ Q[bigSq D (ρ * n) k | ℱ k] ω / √(ρ * n) ∧
      |cvar Q ℱ D (ρ * n) k ω - Q[fun ω => D k ω ^ 2 | ℱ k] ω| ≤
        Q[bigSq D (ρ * n) k | ℱ k] ω + Q[truncSq D (ρ * n) k | ℱ k] ω ^ 2) ∧
      Q[fun ω => locInc Q ℱ D (ρ * n) (1 * n) k ω ^ 2 | ℱ k] ω =
        activeW Q ℱ D (ρ * n) (1 * n) k ω * cvar Q ℱ D (ρ * n) k ω ∧
      |locInc Q ℱ D (ρ * n) (1 * n) k ω| ≤ 2 * √(ρ * n) := by
    filter_upwards [ae_all_iff.2 fun k => (ctrunc_props hD hL2 h0 ha k).2.2.2.1,
      ae_all_iff.2 fun k => (ctrunc_props hD hL2 h0 ha k).2.2.2.2.1,
      ae_all_iff.2 fun k => (hp k).2.2.2.1, ae_all_iff.2 fun k => (hp k).2.1]
      with ω h1 h2 h3 h4 k
    exact ⟨⟨h1 k, h2 k⟩, h3 k, h4 k⟩
  have hsqrt : ∀ {L x : ℝ}, 0 ≤ x → |L| < √x → L ^ 2 ≤ x := fun {L x} hx h => by
    have := sq_lt_sq' (by linarith [abs_nonneg L, Real.sqrt_nonneg x]) h
    rw [sq_abs, Real.sq_sqrt hx] at this; exact this.le
  have hsub : ∀ᵐ ω ∂Q, ω ∈ {ω | η ≤ |(∑ k ∈ Finset.range m, D k ω ^ 2) / n - t|} →
      ω ∈ ({ω | ∃ k < n, ρ * n ≤ D k ω ^ 2} ∪ {ω | 1 / 2 ≤ |clockDev Q ℱ D n ω|} ∪
        {ω | ℓ0 ≤ |lindAvg Q ℱ D ρ n ω|} ∪ {ω | η / 4 ≤ |R n ω|} ∪ Tset : Set Ω) := by
    filter_upwards [hid] with ω hω hbad
    by_contra hgood
    simp only [hTset, mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_le] at hgood
    obtain ⟨⟨⟨⟨hsmall, hcd⟩, hla⟩, hRs⟩, hTs⟩ := hgood
    have hla' := (le_abs_self (lindAvg Q ℱ D ρ n ω)).trans_lt hla
    exact absurd hbad (not_le.2 (abs_avg_sq_sub_lt_of_good hρ0 hη hn1 hmn hω hsmall hcd
      (hla'.le.trans ((min_le_left _ _).trans (min_le_left _ _)))
      (by have := hsqrt (show 0 ≤ ρ / 4 by positivity)
            (hla.trans_le ((min_le_left _ _).trans (min_le_right _ _))); linarith)
      (hla'.le.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (hsqrt (by positivity) (hla.trans_le ((min_le_right _ _).trans (min_le_right _ _))))
      hTs hRs))
  have hNn := hN n (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hNn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  calc Q.real {ω | η ≤ |(∑ k ∈ Finset.range m, D k ω ^ 2) / n - t|}
      ≤ Q.real ({ω | ∃ k < n, ρ * n ≤ D k ω ^ 2} ∪ {ω | 1 / 2 ≤ |clockDev Q ℱ D n ω|} ∪
        {ω | ℓ0 ≤ |lindAvg Q ℱ D ρ n ω|} ∪ {ω | η / 4 ≤ |R n ω|} ∪ Tset) :=
        ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono_ae hsub)
    _ ≤ Q.real {ω | ∃ k < n, ρ * n ≤ D k ω ^ 2} + Q.real {ω | 1 / 2 ≤ |clockDev Q ℱ D n ω|} +
        Q.real {ω | ℓ0 ≤ |lindAvg Q ℱ D ρ n ω|} + Q.real {ω | η / 4 ≤ |R n ω|} +
        Q.real Tset := by
        refine (measureReal_union_le _ _).trans (add_le_add ((measureReal_union_le _ _).trans
          (add_le_add ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _)
            le_rfl)) le_rfl)) le_rfl)
    _ < δ := by linarith

/-! ### The finite-dimensional distributions -/

/-- The localisation at the clock `2n` is eventually inactive with vanishing probability:
`P(∃ k < n, 1{Σ_{j≤k} E[Dⱼ² | 𝓕ⱼ] ≤ 2n} ≠ 1) → 0` under (D.8). -/
theorem tendsto_measureReal_exists_locWeight_ne_one {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ}
    (hcv : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => Q.real {ω | ∃ k < n,
      locWeight Q ℱ (fun k ω => D k ω ^ 2) (2 * n) k ω ≠ 1}) atTop (𝓝 0) := by
  have hVm : ∀ k, Measurable (Q[fun ω => D k ω ^ 2 | ℱ k]) := fun k =>
    (stronglyMeasurable_condExp.measurable).mono (ℱ.le k) le_rfl
  have hpos : ∀ᵐ ω ∂Q, ∀ k, 0 ≤ Q[fun ω => D k ω ^ 2 | ℱ k] ω :=
    ae_all_iff.2 fun k => (condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg (D k ω))).mono
      fun ω h => by simpa using h
  set f : ℕ → Ω → ℝ := fun n ω =>
    (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n - 1 with hf
  have hfm : ∀ n, Measurable (f n) := fun n =>
    ((Finset.measurable_sum _ fun k _ => hVm k).div_const _).sub measurable_const
  have hfae : ∀ᵐ ω ∂Q, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
    filter_upwards [hcv] with ω hω
    have := hω.sub_const 1
    rwa [sub_self] at this
  have h1 := tendsto_measureReal_of_ae_tendsto hfm hfae one_pos
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg)
    (eventually_atTop.2 ⟨1, fun n hn => ?_⟩) h1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono_ae ?_)
  have : ∀ᵐ ω ∂Q, ω ∈ {ω | ∃ k < n, locWeight Q ℱ (fun k ω => D k ω ^ 2) (2 * n) k ω ≠ 1} →
      ω ∈ {ω | 1 ≤ |f n ω|} := by
    filter_upwards [hpos] with ω hω hbad
    obtain ⟨k, hk, hne⟩ := hbad
    by_contra hlt
    push Not at hlt
    have hs : ∑ j ∈ Finset.range n, Q[fun ω => D j ω ^ 2 | ℱ j] ω ≤ 2 * n := by
      have := (abs_lt.1 hlt).2
      simp only [hf] at this
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hn0] at this
      linarith
    exact hne (by
      simp only [locWeight]
      exact ite_sum_le_eq_one (q := fun j => Q[fun ω => D j ω ^ 2 | ℱ j] ω) hω hs hk)
  exact this

/-- **The finite-dimensional distributions under (D.8) and (D.9)**: `fidiLin t c (n^{−1/2} mₙ)`
converges in distribution to `fidiLin t c` under Wiener measure. -/
theorem fidiLin_mPath_of_lindeberg [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hcv : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 1))
    (hlin : ∀ ε > 0, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => lindAvg Q ℱ D ε n ω) atTop (𝓝 0))
    {K : ℕ} (t : Fin K → unitInterval) (c : Fin K → ℝ) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (n : ℕ) ω => fidiLin t c (mPath D n ω)) atTop
      (fidiLin t c) (fun _ => Q) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  have hDm : ∀ k, Measurable (D k) := fun k => (hD k).measurable.mono (ℱ.le (k + 1)) le_rfl
  set W : ℕ → Ω → ℝ := fun k ω => D k ω ^ 2 with hW
  set a : ℕ → ℕ → Ω → ℝ := fun n k => locWeight Q ℱ W (2 * n) k with ha
  set Y : ℕ → ℕ → Ω → ℝ := fun n k ω => a n k ω * D k ω with hY
  have ha01 : ∀ n k ω, a n k ω = 0 ∨ a n k ω = 1 := fun n k ω => by
    simp only [ha, locWeight]; split_ifs <;> simp
  have haF : ∀ n k, StronglyMeasurable[ℱ k] (a n k) := fun n k =>
    stronglyMeasurable_locWeight Q ℱ W _ k
  have hYF : ∀ n k, StronglyMeasurable[ℱ (k + 1)] (Y n k) := fun n k =>
    ((((haF n k).measurable.mono (ℱ.mono (Nat.le_succ k)) le_rfl).mul
      (hD k).measurable)).stronglyMeasurable
  have hYle : ∀ n k ω, |Y n k ω| ≤ |D k ω| := fun n k ω => by
    simp only [hY]; rw [abs_mul]
    rcases ha01 n k ω with h | h <;> rw [h] <;> simp
  have hYm : ∀ n k, Measurable (Y n k) := fun n k =>
    (hYF n k).measurable.mono (ℱ.le (k + 1)) le_rfl
  have hYL2 : ∀ n k, MemLp (Y n k) 2 Q := fun n k =>
    (hL2 k).of_le (hYm n k).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hYle n k ω)
  have hY0 : ∀ n k, Q[Y n k | ℱ k] =ᵐ[Q] 0 := fun n k => by
    have h1 : Q[Y n k | ℱ k] =ᵐ[Q] a n k * Q[D k | ℱ k] :=
      condExp_mul_of_stronglyMeasurable_left (haF n k) ((hYL2 n k).integrable one_le_two)
        ((hL2 k).integrable one_le_two)
    filter_upwards [h1, h0 k] with ω e1 e2
    rw [e1, Pi.mul_apply, e2, Pi.zero_apply, mul_zero]
  have hbdd : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, Y n k ω ^ 2 ∂Q ≤ 2 * n := by
    intro n
    have e : ∀ k, ∫ ω, Y n k ω ^ 2 ∂Q = ∫ ω, locWeight Q ℱ W (2 * n) k ω * W k ω ∂Q :=
      fun k => integral_congr_ae (Eventually.of_forall fun ω => by
        simp only [hY, ha, hW]
        rcases ha01 n k ω with h | h <;> simp only [ha] at h <;> rw [h] <;> ring)
    simp_rw [e]
    exact sum_integral_locWeight_mul_le (fun k => (hL2 k).integrable_sq)
      (fun k => Eventually.of_forall fun ω => sq_nonneg _) (by positivity) n
  have hloc := tendsto_measureReal_exists_locWeight_ne_one (ℱ := ℱ) hcv
  -- the hypotheses of the array lemma
  have hvt : ∀ j, TendstoInMeasure Q (fun (n : ℕ) ω =>
      (∑ k ∈ Finset.range ⌊(n : ℝ) * (t j : ℝ)⌋₊, Y n k ω ^ 2) / n - (t j : ℝ)) atTop 0 := by
    intro j
    have hP := tendstoInMeasure_sum_floor_sq_sub_of_lindeberg hD hL2 h0 hcv hlin
      (t j).2.1 (t j).2.2
    refine tendstoInMeasure_of_measureReal fun κ hκ => ?_
    have h1 := tendsto_measureReal_of_tendstoInMeasure hP hκ
    refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg)
      (Eventually.of_forall fun n => ?_) (by simpa using h1.add hloc)
    have hsub : {ω | κ ≤ |(∑ k ∈ Finset.range ⌊(n : ℝ) * (t j : ℝ)⌋₊, Y n k ω ^ 2) / n -
        (t j : ℝ)|} ⊆ {ω | κ ≤ |(∑ k ∈ Finset.range ⌊(n : ℝ) * (t j : ℝ)⌋₊, D k ω ^ 2) / n -
          (t j : ℝ)|} ∪ {ω | ∃ k < n, locWeight Q ℱ W (2 * n) k ω ≠ 1} := by
      intro ω hω
      by_contra hne
      simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_not] at hne hω
      have hfl : ⌊(n : ℝ) * (t j : ℝ)⌋₊ ≤ n := floor_natCast_mul_le n (t j)
      have e : ∑ k ∈ Finset.range ⌊(n : ℝ) * (t j : ℝ)⌋₊, Y n k ω ^ 2 =
          ∑ k ∈ Finset.range ⌊(n : ℝ) * (t j : ℝ)⌋₊, D k ω ^ 2 :=
        Finset.sum_congr rfl fun k hk => by
          simp only [hY, ha]
          rw [hne.2 k ((Finset.mem_range.1 hk).trans_le hfl), one_mul]
      rw [e] at hω
      exact absurd hω hne.1
    exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hmax : TendstoInMeasure Q (fun (n : ℕ) ω => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => Y n k ω ^ 2) / n) atTop 0 := by
    refine tendstoInMeasure_of_measureReal fun κ hκ => ?_
    have hbig := (tendsto_measureReal_exists_big hD hL2 (half_pos hκ) (hlin _ (half_pos hκ))).comp
      (tendsto_add_atTop_nat 1)
    refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg)
      (eventually_atTop.2 ⟨1, fun n hn => ?_⟩) hbig
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    refine measureReal_mono fun ω hω => ?_
    simp only [mem_ofPred_eq] at hω ⊢
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      (fun k => Y n k ω ^ 2)
    rw [hkeq, abs_of_nonneg (by positivity), le_div_iff₀ hn0] at hω
    refine ⟨k, Finset.mem_range.1 hk, ?_⟩
    have h1 : Y n k ω ^ 2 ≤ D k ω ^ 2 := by
      rw [← sq_abs, ← sq_abs (D k ω)]; exact pow_le_pow_left₀ (abs_nonneg _) (hYle n k ω) 2
    push_cast
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : κ / 2 * ((n : ℝ) + 1) ≤ κ * n := by nlinarith
    linarith
  have hA := array_fidiLin_polygonal_of_tendstoInMeasure hYF hYL2 hY0 (by norm_num : (0:ℝ) ≤ 2)
    hbdd t c hvt hmax
  -- the original process agrees with the localised one on a set of probability → 1
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hA ?_ fun n =>
    ((measurable_fidiLin t c).comp (measurable_polygonal_comp (fun k =>
      measurable_const.mul (Finset.measurable_sum _ fun i _ => hDm i)) n)).aemeasurable
  refine tendstoInMeasure_of_measureReal fun κ hκ => ?_
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg)
    (Eventually.of_forall fun n => measureReal_mono fun ω hω => ?_) hloc
  simp only [mem_ofPred_eq, Pi.sub_apply] at hω ⊢
  by_contra hne
  push Not at hne
  have heq : mPath D n ω = polygonal n fun k => (√(n : ℝ))⁻¹ *
      ∑ l ∈ Finset.range k, Y n l ω := by
    rw [mPath]
    refine polygonal_congr fun k hk => ?_
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    rcases Nat.lt_or_ge l n with h | h
    · simp only [hY, ha]; rw [hne l h, one_mul]
    · exact absurd (Finset.mem_range.1 hl) (by omega)
  rw [heq, sub_self, abs_zero] at hω
  exact absurd hω (not_le.2 hκ)

/-! ### Theorem D.6.4 -/

/-- **Theorem D.6.4 with unit variance**: under (D.8) with limit `1` and (D.9),
`n^{−1/2} mₙ ⇒ W`. -/
theorem martingale_fclt_lindeberg_one [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hcv : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 1))
    (hlin : ∀ ε > 0, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => lindAvg Q ℱ D ε n ω) atTop (𝓝 0)) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (n : ℕ) ω => mPath D n ω) atTop id (fun _ => Q)
      wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  have hDm : ∀ k, Measurable (D k) := fun k => (hD k).measurable.mono (ℱ.le (k + 1)) le_rfl
  have hXm : ∀ n, Measurable (mPath D n) := fun n =>
    measurable_polygonal_comp (fun k => measurable_const.mul
      (Finset.measurable_sum _ fun i _ => hDm i)) n
  have htight := isTightMeasureSet_map_of_modulus (Ω := fun _ => Ω) (Q := fun _ => Q)
    (X := fun n => mPath D n) (fun n => (hXm n).aemeasurable)
    (fun η _ => ⟨0, fun n => by
      have he : {ω : Ω | (0 : ℝ) < |mPath D n ω 0|} = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun ω hω => ?_
        rw [mem_ofPred_eq, mPath, polygonal_zero_point, Finset.sum_range_zero, mul_zero,
          abs_zero] at hω
        exact lt_irrefl _ hω
      change Q {ω : Ω | (0 : ℝ) < |mPath D n ω 0|} ≤ η
      rw [he, measure_empty]
      exact zero_le⟩)
    (modulus_condition_mPath hD hL2 h0 hcv hlin)
  exact tendstoInDistribution_of_tight_of_fidiLin_single (fun n => (hXm n).aemeasurable)
    htight wienerMeasure fun _k t c => fidiLin_mPath_of_lindeberg hD hL2 h0 hcv hlin t c

/-- **Theorem D.6.4** (MT p. 563), the functional CLT for martingales, under the book's
hypotheses: let `Mₙ = Σ_{k<n} Dₖ` with `Dₖ` `𝓕ₖ₊₁`-measurable, square integrable,
`E[Dₖ | 𝓕ₖ] = 0`, and suppose
(D.8) `(1/n) Σ_{k<n} E[Dₖ² | 𝓕ₖ] → γ² > 0` almost surely and
(D.9) for every `ε > 0`, `(1/n) Σ_{k<n} E[Dₖ² 1{Dₖ² ≥ εn} | 𝓕ₖ] → 0` almost surely.
Then the interpolated process `mₙ` of (D.7) satisfies `(γ² n)^{−1/2} mₙ ⇒ B`, a standard
Brownian motion (`wienerMeasure`). -/
theorem theorem_D_6_4 [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {γ2 : ℝ} (hγ : 0 < γ2)
    (hcv : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 γ2))
    (hlin : ∀ ε > 0, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => {ω | ε * n ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω | ℱ k] ω) / n) atTop
      (𝓝 0)) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (n : ℕ) ω =>
      polygonal n (fun k => (√(γ2 * n))⁻¹ * ∑ i ∈ Finset.range k, D i ω)) atTop id
      (fun _ => Q) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  set a := (√γ2)⁻¹ with ha
  have hsq : 0 < √γ2 := Real.sqrt_pos.2 hγ
  have ha2 : a ^ 2 = γ2⁻¹ := by rw [ha, inv_pow, Real.sq_sqrt hγ.le]
  have ha2p : 0 < a ^ 2 := by rw [ha2]; positivity
  set D' : ℕ → Ω → ℝ := fun k ω => a * D k ω with hD'
  have hD'm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D' k) := fun k => (hD k).const_mul a
  have hL2' : ∀ k, MemLp (D' k) 2 Q := fun k => (hL2 k).const_mul a
  have h0' : ∀ k, Q[D' k | ℱ k] =ᵐ[Q] 0 := fun k => by
    have := condExp_smul (μ := Q) a (D k) (ℱ k)
    refine this.trans ((h0 k).mono fun ω h => ?_)
    simp [h]
  have hce : ∀ k, Q[fun ω => D' k ω ^ 2 | ℱ k] =ᵐ[Q]
      fun ω => a ^ 2 * Q[fun ω => D k ω ^ 2 | ℱ k] ω := fun k => by
    have e : (fun ω => D' k ω ^ 2) = (a ^ 2) • fun ω => D k ω ^ 2 := by
      ext ω; simp only [hD', Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact condExp_smul (μ := Q) (a ^ 2) (fun ω => D k ω ^ 2) (ℱ k)
  have hcv' : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D' k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 1) := by
    filter_upwards [hcv, ae_all_iff.2 hce] with ω hω hceω
    have h := hω.const_mul (a ^ 2)
    rw [ha2, inv_mul_cancel₀ hγ.ne'] at h
    refine h.congr fun n => ?_
    rw [Finset.sum_congr rfl fun k _ => hceω k, ← Finset.mul_sum, mul_div_assoc, ha2]
  have hlin' : ∀ ε > 0, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => lindAvg Q ℱ D' ε n ω) atTop (𝓝 0) := by
    intro ε hε
    have hε' : 0 < ε / a ^ 2 := by positivity
    have hbig : ∀ (n k : ℕ), bigSq D' (ε * n) k = (a ^ 2) • bigSq D (ε / a ^ 2 * n) k := by
      intro n k
      ext ω
      simp only [bigSq, hD', Pi.smul_apply, smul_eq_mul]
      by_cases h : ε / a ^ 2 * n ≤ D k ω ^ 2
      · have h' : ε * n ≤ (a * D k ω) ^ 2 := by
          rw [mul_pow]
          have := mul_le_mul_of_nonneg_left h ha2p.le
          have ha0 : a ≠ 0 := by positivity
          rwa [show a ^ 2 * (ε / a ^ 2 * n) = ε * n by field_simp] at this
        rw [Set.indicator_of_mem (show ω ∈ {ω | ε * n ≤ (a * D k ω) ^ 2} from h'),
          Set.indicator_of_mem (show ω ∈ {ω | ε / a ^ 2 * n ≤ D k ω ^ 2} from h), mul_pow]
      · have h' : ¬ (ε * n ≤ (a * D k ω) ^ 2) := by
          intro h''
          apply h
          rw [mul_pow] at h''
          rw [div_mul_eq_mul_div, div_le_iff₀ ha2p]
          linarith
        rw [Set.indicator_of_notMem (show ω ∉ {ω | ε * n ≤ (a * D k ω) ^ 2} from h'),
          Set.indicator_of_notMem (show ω ∉ {ω | ε / a ^ 2 * n ≤ D k ω ^ 2} from h), mul_zero]
    have hae : ∀ᵐ ω ∂Q, ∀ (n k : ℕ), Q[bigSq D' (ε * n) k | ℱ k] ω =
        a ^ 2 * Q[bigSq D (ε / a ^ 2 * n) k | ℱ k] ω := by
      refine ae_all_iff.2 fun n => ae_all_iff.2 fun k => ?_
      rw [hbig n k]
      exact condExp_smul (μ := Q) (a ^ 2) (bigSq D (ε / a ^ 2 * n) k) (ℱ k)
    filter_upwards [hlin (ε / a ^ 2) hε', hae] with ω hω hω'
    have h := hω.const_mul (a ^ 2)
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    simp only [lindAvg]
    rw [Finset.sum_congr rfl fun k _ => hω' n k, ← Finset.mul_sum, mul_div_assoc]
    rfl
  have hfun : (fun (n : ℕ) ω => polygonal n (fun k => (√(γ2 * n))⁻¹ *
      ∑ i ∈ Finset.range k, D i ω)) = fun (n : ℕ) ω => mPath D' n ω := by
    funext n ω
    rw [mPath]
    congr 1
    funext k
    simp only [hD', ← Finset.mul_sum, ha]
    rw [Real.sqrt_mul hγ.le, mul_inv]
    ring
  rw [hfun]
  exact martingale_fclt_lindeberg_one hD'm hL2' h0' hcv' hlin'

end MeynTweedie.LimitTheorems

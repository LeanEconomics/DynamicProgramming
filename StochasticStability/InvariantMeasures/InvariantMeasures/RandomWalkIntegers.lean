/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvariantMeasures.DriftCriteria
import InvariantMeasures.CountableClassification
import InvariantMeasures.CountableIrreducibility
import InvariantMeasures.RandomWalkIrreducibility

/-!
# Random walks with bounded range (MT §8.4.3, §8.1.2)

Meyn and Tweedie, §8.4.3, pp. 191–192, and the simple random walk of §8.1.2, p. 176. The walk on
`ℤ` is `matKernel (rwMatrix Γ)`, `P(x, y) = Γ(y − x)`, and the walk on the half line `ℤ₊` is
`matKernel (rwhlMatrix Γ)`, `Φₙ₊₁ = [Φₙ + Wₙ₊₁]⁺` (`SpecificMatrices`). The increment law
`Γ : ℤ → [0, ∞]` is a probability with bounded range: `Γ(w) = 0` for `|w| > r`; its mean is
`β = Σ_{|w| ≤ r} Γ(w) w`.

**Tools.**
* `isPetite_of_finite`: on a countable space a finite set whose points all lead to one state is
  petite ("on a countable space, finite sets are petite", p. 191).
* `lintegral_rw`, `lintegral_rwhl`: `∫ P(x, dy) f(y) = Σ_w Γ(w) f(x + w)`, resp.
  `Σ_w Γ(w) f([x + w]⁺)`; `integral_eq_sum_of_lintegral`: the same for real integrals.
* `exists_root_of_mean_pos`, `exists_root_of_mean_ne_zero`: if `β ≠ 0` and `Γ` charges both
  half-lines, `Σ_w Γ(w) sʷ = 1` has a root `s ∈ (0, ∞)`, `s ≠ 1` (8.53); the proof is the book's,
  `β(s) → ∞` at an end and `β'(1) = β`, with the intermediate value theorem.
* `rw_charges_both_sides`: an irreducible walk on `ℤ` has increments of both signs.

**Results.**
* **Proposition 8.4.4** (`proposition_8_4_4`, p. 191): an irreducible bounded-range walk on `ℤ`
  with mean zero is recurrent (`V(x) = |x|`).
* **Proposition 8.4.5** (`proposition_8_4_5`, p. 191): with non-zero mean it is transient
  (`V(x) = (1 − sˣ)⁺`).
* **Proposition 8.4.6** (`proposition_8_4_6`, p. 192): the bounded-range walk on `ℤ₊` with
  `Γ(−∞, 0) > 0` is recurrent iff `β ≤ 0`.
* Simple random walk on `ℤ₊` (p. 176): `srw_hitProb_zero_eq` and `srw_hitProb_one_eq` are the
  first-step equations `L(0, 0) = p + q L(1, 0)`, `L(1, 0) = p + q L(2, 0)`;
  `hitProb_passage` (skip-free to the left, `L(2, 0) = L(2, 1) L(1, 0)`),
  `srw_hitProb_translate` (`L(x + 1, x) = L(1, 0)`), `srw_quadratic` (8.13),
  `srw_hitProb_one_root` (`L(1, 0) = 1` or `p/q`), and `srw_hitProb_zero`, the conclusion
  `L(0, 0) = L(1, 0) = 1` when `p ≥ q`.

**Corrections.**
* Proposition 8.4.6 needs `Γ(−∞, 0) > 0`: for `Γ = δ₀` (`β = 0`) the walk on `ℤ₊` stays where
  it is, has disjoint absorbing states and is `ψ`-irreducible for no `ψ`, so it is not recurrent
  (`proposition_8_4_6_counterexample`). Without it the walk is never irreducible.
* The transience half of Propositions 8.4.5 and 8.4.6 uses `ΔV = 0` (8.51) off the sublevel set,
  so it rests on Theorem 8.4.2 with `ΔV ≥ 0`, the corrected form (see `DriftCriteria`); the
  book's direct "stochastic comparison" proof for the half line is replaced by the same drift
  argument on `ℤ₊`.
* `theorem_8_3_6_i_counterexample`: the empty set refutes Theorem 8.3.6 (i) as stated: it is
  petite with `L ≡ 1` on it vacuously, but the walk on `ℤ₊` with `Γ = ⅓δ₋₁ + ⅔δ₁` is not
  recurrent.

The skip-free walk (Proposition 8.5.5) is in `SkipFreeWalk`, the walk on `ℝ₊` in
`RandomWalkHalfLine`, and the walk on `ℤ` with general mean-zero increments (Theorem 8.1.5) in
`RandomWalkMeanZero` (`theorem_8_1_5`).
-/

namespace MeynTweedie.InvariantMeasures

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-! ### Finite sets are petite -/

/-- On a countable space, a finite set whose points all lead to a state `z` is petite, with the
sampling distribution `a_{1/2}` and a multiple of `δ_z` (MT p. 191). -/
theorem isPetite_of_finite {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable X] (P : Kernel X X) [IsMarkovKernel P] {C : Set X} (hC : C.Finite) {z : X}
    (hz : ∀ x ∈ C, Leads P x z) : IsPetite P C := by
  have hCm : MeasurableSet C := hC.countable.measurableSet
  have hpos : ∀ x ∈ C, 0 < resolventHalf P x {z} := fun x hx =>
    (resolventHalf_pos_iff P x (measurableSet_singleton z)).2
      ((leads_iff_exists_pow P x z).1 (hz x hx))
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨geomDist 2⁻¹, Measure.dirac z, MeasurableSet.empty, isSamplingDist_geomDist_half,
      by simp, fun x hx => absurd hx (notMem_empty x)⟩
  set δ := hC.toFinset.inf' (by simpa using hne) fun x => resolventHalf P x {z} with hδ
  have hδpos : 0 < δ := (Finset.lt_inf'_iff _).2 fun x hx => hpos x (by simpa using hx)
  refine ⟨geomDist 2⁻¹, δ • Measure.dirac z, hCm, isSamplingDist_geomDist_half,
    smul_measure_ne_zero (by simp) hδpos.ne', fun x hx => Measure.le_intro fun B hB _ => ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB, sampledKernel_geomDist_half]
  by_cases hzB : z ∈ B
  · rw [indicator_of_mem hzB, Pi.one_apply, mul_one]
    exact (Finset.inf'_le _ (by simpa using hx)).trans
      (measure_mono (singleton_subset_iff.2 hzB))
  · rw [indicator_of_notMem hzB, mul_zero]; exact zero_le

/-! ### Integrals against the walk -/

/-- `∫ P(x, dy) f(y) = Σ_w Γ(w) f(x + w)` for the walk on `ℤ`. -/
theorem lintegral_rw (Γ : ℤ → ℝ≥0∞) (x : ℤ) (f : ℤ → ℝ≥0∞) :
    ∫⁻ y, f y ∂matKernel (rwMatrix Γ) x = ∑' w, Γ w * f (x + w) := by
  rw [lintegral_matKernel]
  exact ((Equiv.addLeft x).tsum_eq (fun y => rwMatrix Γ x y * f y)).symm.trans
    (tsum_congr fun w => by simp [rwMatrix])

/-- The entries of the half-line matrix: `P(x, y) = Σ_w Γ(w) 1{[x + w]⁺ = y}`. -/
theorem rwhlMatrix_eq_tsum (Γ : ℤ → ℝ≥0∞) (x y : ℕ) :
    rwhlMatrix Γ x y = ∑' w, Γ w * (if ((x : ℤ) + w).toNat = y then 1 else 0) := by
  unfold rwhlMatrix
  split_ifs with hy
  · refine tsum_congr fun w => ?_
    subst hy
    by_cases hw : w ≤ -(x : ℤ)
    · have : ((x : ℤ) + w).toNat = 0 := Int.toNat_eq_zero.2 (by omega)
      simp [hw, this]
    · have : ((x : ℤ) + w).toNat ≠ 0 := by omega
      simp [hw, this]
  · rw [tsum_eq_single ((y : ℤ) - x)]
    · have : ((x : ℤ) + ((y : ℤ) - x)).toNat = y := by omega
      simp
    · intro w hw
      have : ((x : ℤ) + w).toNat ≠ y := by omega
      simp [this]

/-- `∫ P(x, dy) f(y) = Σ_w Γ(w) f([x + w]⁺)` for the walk on `ℤ₊`. -/
theorem lintegral_rwhl (Γ : ℤ → ℝ≥0∞) (x : ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ y, f y ∂matKernel (rwhlMatrix Γ) x = ∑' w, Γ w * f ((x : ℤ) + w).toNat := by
  rw [lintegral_matKernel]
  simp_rw [rwhlMatrix_eq_tsum, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun w => ?_
  rw [tsum_eq_single ((x : ℤ) + w).toNat fun y hy => by simp [Ne.symm hy]]
  simp

/-- Real integrals from a finite lintegral formula: if `∫ g dμ = Σ_{w ∈ S} Γ(w) g(φ(w))` for every
`g ≥ 0`, then `∫ f dμ = Σ_{w ∈ S} Γ(w) f(φ(w))` for bounded measurable `f ≥ 0`. -/
theorem integral_eq_sum_of_lintegral {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
    [IsFiniteMeasure μ] {S : Finset ℤ} {Γ : ℤ → ℝ≥0∞} (hΓ : ∀ w, Γ w ≠ ∞) {φ : ℤ → Y}
    (h : ∀ g : Y → ℝ≥0∞, ∫⁻ y, g y ∂μ = ∑ w ∈ S, Γ w * g (φ w)) {f : Y → ℝ}
    (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {B : ℝ} (hfB : ∀ y, f y ≤ B) :
    ∫ y, f y ∂μ = ∑ w ∈ S, (Γ w).toReal * f (φ w) := by
  have hint : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable B
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 y)]; exact hfB y)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfm.aestronglyMeasurable, h,
    ENNReal.toReal_sum fun w _ => ENNReal.mul_ne_top (hΓ w) ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf0 _)]

/-! ### The root of `Σ_w Γ(w) sʷ = 1` -/

/-- **The root of (8.53)** (MT p. 192): if `g ≥ 0` on a finite set `S` sums to one, has positive
mean `Σ g(w) w > 0` and charges some `w₀ < 0`, then `Σ_w g(w) ρʷ = 1` for some `ρ ∈ (0, 1)`. -/
theorem exists_root_of_mean_pos {S : Finset ℤ} {g : ℤ → ℝ} (hg0 : ∀ w, 0 ≤ g w)
    (hsum : ∑ w ∈ S, g w = 1) (hβ : 0 < ∑ w ∈ S, g w * w) {w₀ : ℤ} (hw₀S : w₀ ∈ S)
    (hw₀ : w₀ < 0) (hgw₀ : 0 < g w₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∑ w ∈ S, g w * ρ ^ w = 1 := by
  set f : ℝ → ℝ := fun s => ∑ w ∈ S, g w * s ^ w with hf
  have hf1 : f 1 = 1 := by simp [hf, hsum]
  -- `f(s₀) > 1` for small `s₀`
  set s₀ : ℝ := min (g w₀ / 2) (1 / 2) with hs₀
  have hs₀pos : 0 < s₀ := lt_min (by positivity) (by norm_num)
  have hs₀1 : s₀ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hfs₀ : 1 < f s₀ := by
    have hinv : 2 ≤ s₀⁻¹ := by
      rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 2) hs₀pos]
      exact (min_le_right (g w₀ / 2) (1 / 2)).trans (by norm_num)
    have hpow : s₀⁻¹ ≤ s₀ ^ w₀ := by
      have : s₀ ^ w₀ = s₀⁻¹ ^ (-w₀) := by rw [inv_zpow', neg_neg]
      rw [this]
      calc s₀⁻¹ = s₀⁻¹ ^ (1 : ℤ) := (zpow_one _).symm
        _ ≤ s₀⁻¹ ^ (-w₀) := zpow_le_zpow_right₀ (show (1 : ℝ) ≤ s₀⁻¹ by linarith)
            (show (1 : ℤ) ≤ -w₀ by omega)
    have hg2 : 2 ≤ g w₀ * s₀⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hs₀pos]
      linarith [min_le_left (g w₀ / 2) (1 / 2)]
    calc (1 : ℝ) < 2 := by norm_num
      _ ≤ g w₀ * s₀ ^ w₀ := hg2.trans (by gcongr)
      _ ≤ f s₀ := Finset.single_le_sum (f := fun w => g w * s₀ ^ w)
          (fun w _ => mul_nonneg (hg0 w) (zpow_nonneg hs₀pos.le w)) hw₀S
  -- `f(s₁) < 1` for some `s₁ ∈ (s₀, 1)`, as `f'(1) = β > 0`
  have hderiv : HasDerivAt f (∑ w ∈ S, g w * w) 1 := by
    have := HasDerivAt.fun_sum (u := S) (A := fun w s => g w * s ^ w)
      (A' := fun w => g w * ((w : ℝ) * (1 : ℝ) ^ (w - 1)))
      fun w _ => (hasDerivAt_zpow w 1 (Or.inl one_ne_zero)).const_mul (g w)
    simpa using this
  have hsub : Iio (1 : ℝ) ⊆ {1}ᶜ := fun s hs => ne_of_lt hs
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hderiv).mono_left (nhdsWithin_mono 1 hsub)
  obtain ⟨s₁, hs₁pos, hs₁mem⟩ := ((hslope.eventually (lt_mem_nhds hβ)).and
    (Ioo_mem_nhdsLT hs₀1)).exists
  have hfs₁ : f s₁ < 1 := by
    rw [slope_def_field, hf1] at hs₁pos
    have hneg : s₁ - 1 < 0 := by linarith [hs₁mem.2]
    by_contra hc
    push Not at hc
    exact absurd hs₁pos (not_lt.2 (div_nonpos_of_nonneg_of_nonpos (by linarith) hneg.le))
  -- the intermediate value theorem on `[s₀, s₁]`
  have hcont : ContinuousOn f (Icc s₀ s₁) := by
    refine continuousOn_finsetSum _ fun w _ => fun s hs => ?_
    exact ((continuousAt_zpow₀ s w (Or.inl (by linarith [hs.1]))).const_mul
      (g w)).continuousWithinAt
  obtain ⟨ρ, hρ, hfρ⟩ := intermediate_value_Icc' hs₁mem.1.le hcont ⟨hfs₁.le, hfs₀.le⟩
  exact ⟨ρ, hs₀pos.trans_le hρ.1, hρ.2.trans_lt hs₁mem.2, hfρ⟩

/-- **The root of (8.53)** for a non-zero mean: if `g ≥ 0` on `S = [−R, R]` sums to one, has
mean `≠ 0` and charges both `w < 0` and `w > 0`, then `Σ_w g(w) sʷ = 1` for some `s > 0`,
`s ≠ 1`. A negative mean is reduced to a positive one by reflection, `s ↦ s⁻¹`. -/
theorem exists_root_of_mean_ne_zero {R : ℕ} {g : ℤ → ℝ} (hg0 : ∀ w, 0 ≤ g w)
    (hsum : ∑ w ∈ Finset.Icc (-(R : ℤ)) R, g w = 1)
    (hβ : ∑ w ∈ Finset.Icc (-(R : ℤ)) R, g w * w ≠ 0)
    (hneg : ∃ w ∈ Finset.Icc (-(R : ℤ)) R, w < 0 ∧ 0 < g w)
    (hpos : ∃ w ∈ Finset.Icc (-(R : ℤ)) R, 0 < w ∧ 0 < g w) :
    ∃ s : ℝ, 0 < s ∧ s ≠ 1 ∧ ∑ w ∈ Finset.Icc (-(R : ℤ)) R, g w * s ^ w = 1 := by
  set S := Finset.Icc (-(R : ℤ)) R
  have hrefl : ∀ F : ℤ → ℝ, ∑ w ∈ S, F (-w) = ∑ w ∈ S, F w := fun F =>
    Finset.sum_nbij' (fun w => -w) (fun w => -w)
      (fun w hw => by simp only [S, Finset.mem_Icc] at hw ⊢; omega)
      (fun w hw => by simp only [S, Finset.mem_Icc] at hw ⊢; omega)
      (fun w _ => neg_neg w) (fun w _ => neg_neg w) (fun w _ => rfl)
  rcases lt_or_gt_of_ne hβ with hlt | hgt
  · -- reflect: `g'(w) = g(−w)` has positive mean
    obtain ⟨w₀, hw₀S, hw₀, hgw₀⟩ := hpos
    obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_root_of_mean_pos (S := S) (g := fun w => g (-w))
      (fun w => hg0 _) (by rw [hrefl g]; exact hsum)
      (by
        have := hrefl (fun w => g w * w)
        simp only [Int.cast_neg, mul_neg] at this ⊢
        have h2 : ∑ w ∈ S, g (-w) * (w : ℝ) = -∑ w ∈ S, g w * w := by
          rw [← this, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun w _ => by ring
        rw [h2]; linarith)
      (show -w₀ ∈ S by simp only [S, Finset.mem_Icc] at hw₀S ⊢; omega) (by omega)
      (by simpa using hgw₀)
    refine ⟨ρ⁻¹, inv_pos.2 hρ0, fun h => by
      rw [inv_eq_one] at h; exact absurd h hρ1.ne, ?_⟩
    rw [← hrefl (fun w => g w * ρ⁻¹ ^ w)]
    simp only [inv_zpow', neg_neg]
    exact hρ
  · obtain ⟨w₀, hw₀S, hw₀, hgw₀⟩ := hneg
    obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_root_of_mean_pos hg0 hsum hgt hw₀S hw₀ hgw₀
    exact ⟨ρ, hρ0, hρ1.ne, hρ⟩

/-! ### Bounded-range increments -/

/-- The window `[−r, r]` carrying a bounded-range increment law. -/
abbrev window (r : ℕ) : Finset ℤ := Finset.Icc (-(r : ℤ)) r

/-- The mean `β = Σ_{|w| ≤ r} Γ(w) w` of a bounded-range increment law. -/
noncomputable def rwMean (Γ : ℤ → ℝ≥0∞) (r : ℕ) : ℝ := ∑ w ∈ window r, (Γ w).toReal * w

/-- `Γ(w) = 0` off the window. -/
theorem eq_zero_of_notMem_window {Γ : ℤ → ℝ≥0∞} {r : ℕ} (hr : ∀ w : ℤ, (r : ℤ) < |w| → Γ w = 0)
    {w : ℤ} (hw : w ∉ window r) : Γ w = 0 :=
  hr w (by simp only [Finset.mem_Icc, not_and_or, not_le] at hw; rcases hw with h | h <;>
    [exact lt_abs.2 (Or.inr (by omega)); exact lt_abs.2 (Or.inl h)])

/-- A series against a bounded-range `Γ` is a finite sum over the window. -/
theorem tsum_eq_sum_window {Γ : ℤ → ℝ≥0∞} {r : ℕ} (hr : ∀ w : ℤ, (r : ℤ) < |w| → Γ w = 0)
    (F : ℤ → ℝ≥0∞) : ∑' w, Γ w * F w = ∑ w ∈ window r, Γ w * F w :=
  tsum_eq_sum (s := window r) fun w hw => by rw [eq_zero_of_notMem_window hr hw, zero_mul]

/-- The weights of a probability `Γ` are finite. -/
theorem ne_top_of_tsum_eq_one {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1) (w : ℤ) : Γ w ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hΓ ▸ ENNReal.le_tsum w)

/-- `Σ_{|w| ≤ r} Γ(w) = 1` in `ℝ`. -/
theorem sum_window_toReal {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1) {r : ℕ}
    (hr : ∀ w : ℤ, (r : ℤ) < |w| → Γ w = 0) : ∑ w ∈ window r, (Γ w).toReal = 1 := by
  have : ∑ w ∈ window r, Γ w = 1 := by
    have h1 := tsum_eq_sum_window hr (fun _ => (1 : ℝ≥0∞))
    simp only [mul_one] at h1
    rw [← h1, hΓ]
  rw [← ENNReal.toReal_sum fun w _ => ne_top_of_tsum_eq_one hΓ w, this, ENNReal.toReal_one]

/-- On the window, an affine function averages to its value at the mean:
`Σ Γ(w) (a + b w) = a + b β`. -/
theorem sum_window_affine {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1) {r : ℕ}
    (hr : ∀ w : ℤ, (r : ℤ) < |w| → Γ w = 0) (a b : ℝ) :
    ∑ w ∈ window r, (Γ w).toReal * (a + b * w) = a + b * rwMean Γ r := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_window_toReal hΓ hr, one_mul, rwMean,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun w _ => by ring

/-- `Σ Γ(w) ofReal(F(w)) = ofReal(Σ Γ(w) F(w))` for `F ≥ 0`. -/
theorem sum_window_ofReal {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1) {S : Finset ℤ} {F : ℤ → ℝ}
    (hF : ∀ w ∈ S, 0 ≤ F w) :
    ∑ w ∈ S, Γ w * ENNReal.ofReal (F w) = ENNReal.ofReal (∑ w ∈ S, (Γ w).toReal * F w) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun w hw => mul_nonneg ENNReal.toReal_nonneg (hF w hw)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ne_top_of_tsum_eq_one hΓ w)]

/-! ### Irreducibility -/

/-- An irreducible walk on `ℤ` has increments of both signs. -/
theorem rw_charges_both_sides {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1)
    (hirr : haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwMatrix hΓ)
      IsIrreducibleChain (matKernel (rwMatrix Γ))) :
    (∃ w < 0, Γ w ≠ 0) ∧ (∃ w > 0, Γ w ≠ 0) := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwMatrix hΓ)
  have hc := (isIrreducibleChain_iff _).1 hirr
  constructor
  · by_contra h
    push Not at h
    have habs : IsAbsorbing (matKernel (rwMatrix Γ)) (Ici 0) :=
      (isAbsorbing_matKernel_iff _).2 fun x hx y hy => by
        simp only [mem_Ici, not_le] at hx hy
        exact h (y - x) (by omega)
    have h0 := habs.hitProb_compl measurableSet_Ici (self_mem_Ici (a := (0 : ℤ)))
    rcases (hc 0 (-1)).1 with h1 | h1
    · omega
    · exact absurd h0 ((h1.trans_le (hitProb_mono _ (by simp) 0)).ne')
  · by_contra h
    push Not at h
    have habs : IsAbsorbing (matKernel (rwMatrix Γ)) (Iic 0) :=
      (isAbsorbing_matKernel_iff _).2 fun x hx y hy => by
        simp only [mem_Iic, not_le] at hx hy
        exact h (y - x) (by omega)
    have h0 := habs.hitProb_compl measurableSet_Iic (self_mem_Iic (a := (0 : ℤ)))
    rcases (hc 0 1).1 with h1 | h1
    · omega
    · exact absurd h0 ((h1.trans_le (hitProb_mono _ (by simp) 0)).ne')

/-! ### Proposition 8.4.4 and Proposition 8.4.5 -/

/-- `∫ P(x, dy) f(y) = Σ_{|w| ≤ r} Γ(w) f(x + w)` for a bounded-range walk on `ℤ`. -/
theorem lintegral_rw_window {Γ : ℤ → ℝ≥0∞} {r : ℕ} (hr : ∀ w : ℤ, (r : ℤ) < |w| → Γ w = 0)
    (x : ℤ) (f : ℤ → ℝ≥0∞) :
    ∫⁻ y, f y ∂matKernel (rwMatrix Γ) x = ∑ w ∈ window r, Γ w * f (x + w) := by
  rw [lintegral_rw, tsum_eq_sum_window hr]

/-- `Σ Γ(w) |x + w| = |x| + c β` when `|x + w| = c (x + w)` on the window and `|x| = c x`. -/
theorem sum_window_abs {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1) {r : ℕ}
    (hr : ∀ w : ℤ, (r : ℤ) < |w| → Γ w = 0) {x : ℤ} {c : ℝ}
    (hw : ∀ w ∈ window r, |((x + w : ℤ) : ℝ)| = c * x + c * w) (hx : |(x : ℝ)| = c * x) :
    ∑ w ∈ window r, Γ w * ENNReal.ofReal |((x + w : ℤ) : ℝ)| =
      ENNReal.ofReal (|(x : ℝ)| + c * rwMean Γ r) := by
  rw [sum_window_ofReal hΓ fun w _ => abs_nonneg _, Finset.sum_congr rfl fun w hw' => by
    rw [hw w hw'], sum_window_affine hΓ hr, hx]

/-- **Proposition 8.4.4** (MT p. 191): an irreducible random walk on `ℤ` whose increment law has
bounded range and mean zero is recurrent. The test function is `V(x) = |x|`, with
`C = {|x| ≤ r}`. -/
theorem proposition_8_4_4 {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1) {r : ℕ}
    (hr : ∀ w : ℤ, (r : ℤ) < |w| → Γ w = 0)
    (hirr : haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwMatrix hΓ)
      IsIrreducibleChain (matKernel (rwMatrix Γ))) (hβ : rwMean Γ r = 0) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwMatrix hΓ)
    IsRecurrentChain (matKernel (rwMatrix Γ)) Measure.count := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwMatrix hΓ)
  set P := matKernel (rwMatrix Γ)
  have hmax := isMaximalIrreducibility_count P hirr
  have hc := (isIrreducibleChain_iff P).1 hirr
  have hfin : ∀ n : ℕ, IsPetite P {x : ℤ | x.natAbs ≤ n} := fun n =>
    isPetite_of_finite P ((Finset.Icc (-(n : ℤ)) n).finite_toSet.subset fun x hx => by
      simp only [mem_ofPred_eq] at hx
      simp only [Finset.coe_Icc, mem_Icc]; omega) (z := 0) fun x _ => (hc x 0).1
  set V : ℤ → ℝ≥0 := fun x => (x.natAbs : ℝ≥0)
  refine (theorem_8_4_3 P hmax (hfin r) (V := V) (measurable_of_countable _)
    (fun n => ?_) (fun x hx => ?_)).1
  · convert hfin n using 2
    simp [V]
  · rw [drift_nonpos_iff, lintegral_rw_window hr]
    simp only [mem_ofPred_eq, not_le] at hx
    have hcast : ∀ z : ℤ, ((z.natAbs : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal |(z : ℝ)| := fun z => by
      rw [ENNReal.coe_natCast, ← ENNReal.ofReal_natCast, ← Int.cast_natCast, Int.natCast_natAbs,
        Int.cast_abs]
    simp only [V, hcast]
    rcases lt_or_gt_of_ne (show x ≠ 0 by omega) with hx0 | hx0
    · rw [sum_window_abs hΓ hr (c := -1) (fun w hw => by
          simp only [Finset.mem_Icc] at hw
          rw [abs_of_neg (by exact_mod_cast (show x + w < 0 by omega))]; push_cast; ring)
        (by rw [abs_of_neg (by exact_mod_cast hx0)]; ring), hβ, mul_zero, add_zero]
    · rw [sum_window_abs hΓ hr (c := 1) (fun w hw => by
          simp only [Finset.mem_Icc] at hw
          rw [abs_of_nonneg (by exact_mod_cast (show 0 ≤ x + w by omega))]; push_cast; ring)
        (by rw [abs_of_pos (by exact_mod_cast hx0)]; ring), hβ, mul_zero, add_zero]

/-- **Proposition 8.4.5** (MT p. 191): an irreducible random walk on `ℤ` whose increment law has
bounded range and non-zero mean is transient. The test function is `V(x) = (1 − sˣ)⁺` with
`Σ_w Γ(w) sʷ = 1`, `s ≠ 1` (8.53); it has `ΔV ≥ 0` on `{V > 0}`. -/
theorem proposition_8_4_5 {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1) {r : ℕ}
    (hr : ∀ w : ℤ, (r : ℤ) < |w| → Γ w = 0)
    (hirr : haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwMatrix hΓ)
      IsIrreducibleChain (matKernel (rwMatrix Γ))) (hβ : rwMean Γ r ≠ 0) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwMatrix hΓ)
    IsTransientChain (matKernel (rwMatrix Γ)) Measure.count := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwMatrix hΓ)
  set P := matKernel (rwMatrix Γ)
  have hmax := isMaximalIrreducibility_count P hirr
  obtain ⟨⟨wn, hwn, hΓn⟩, ⟨wp, hwp, hΓp⟩⟩ := rw_charges_both_sides hΓ hirr
  have hmem : ∀ w, Γ w ≠ 0 → w ∈ window r := fun w hw => by
    by_contra h; exact hw (eq_zero_of_notMem_window hr h)
  have htop := ne_top_of_tsum_eq_one hΓ
  obtain ⟨s, hs0, hs1, hsr⟩ := exists_root_of_mean_ne_zero (R := r) (g := fun w => (Γ w).toReal)
    (fun w => ENNReal.toReal_nonneg) (sum_window_toReal hΓ hr) hβ
    ⟨wn, hmem wn hΓn, hwn, ENNReal.toReal_pos hΓn (htop wn)⟩
    ⟨wp, hmem wp hΓp, hwp, ENNReal.toReal_pos hΓp (htop wp)⟩
  set V : ℤ → ℝ := fun x => max 0 (1 - s ^ x) with hV
  have hV1 : ∀ x, V x ≤ 1 := fun x =>
    max_le zero_le_one (by linarith [zpow_pos hs0 x])
  refine (theorem_8_4_2 P hmax).2 ⟨V, 0, measurable_of_countable _, fun x => le_max_left _ _,
    ⟨1, hV1⟩, le_rfl, ?_, ?_, fun x hx => ?_⟩
  · refine lt_of_lt_of_le (by simp) (measure_mono (singleton_subset_iff.2
      (show (0 : ℤ) ∈ {x | V x ≤ 0} by simp [V])))
  · obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℤ, s ^ x₁ < 1 := by
      rcases lt_or_gt_of_ne hs1 with h | h
      · exact ⟨1, by rwa [zpow_one]⟩
      · exact ⟨-1, by rw [zpow_neg_one]; exact inv_lt_one_of_one_lt₀ h⟩
    refine lt_of_lt_of_le (by simp) (measure_mono (singleton_subset_iff.2
      (show x₁ ∈ {x | V x ≤ 0}ᶜ by
        simp only [mem_compl_iff, mem_ofPred_eq, not_le, V]
        exact lt_max_of_lt_right (by linarith))))
  · simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hx
    have hVx : V x = 1 - s ^ x := by
      rcases le_total (1 - s ^ x) 0 with h | h
      · exact absurd hx (by simp only [V]; rw [max_eq_left h]; exact lt_irrefl 0)
      · exact max_eq_right h
    rw [driftR, integral_eq_sum_of_lintegral (Γ := Γ) htop (φ := fun w => x + w)
      (fun g => lintegral_rw_window hr x g) (measurable_of_countable _) (fun y => le_max_left _ _)
      hV1, hVx, sub_nonneg]
    calc 1 - s ^ x = ∑ w ∈ window r, (Γ w).toReal * (1 - s ^ x * s ^ w) := by
          rw [Finset.sum_congr rfl fun w _ => by rw [mul_sub, mul_one],
            Finset.sum_sub_distrib, sum_window_toReal hΓ hr]
          congr 1
          calc s ^ x = s ^ x * ∑ w ∈ window r, (Γ w).toReal * s ^ w := by
                rw [show ∑ w ∈ window r, (Γ w).toReal * s ^ w = 1 from hsr, mul_one]
            _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ ∑ w ∈ window r, (Γ w).toReal * V (x + w) := Finset.sum_le_sum fun w _ => by
          refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          rw [← zpow_add₀ hs0.ne']
          exact le_max_right _ _

/-! ### The walk on the half line `ℤ₊` -/

/-- `∫ P(x, dy) f(y) = Σ_{|w| ≤ r} Γ(w) f([x + w]⁺)` for a bounded-range walk on `ℤ₊`. -/
theorem lintegral_rwhl_window {Γ : ℤ → ℝ≥0∞} {r : ℕ} (hr : ∀ w : ℤ, (r : ℤ) < |w| → Γ w = 0)
    (x : ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ y, f y ∂matKernel (rwhlMatrix Γ) x = ∑ w ∈ window r, Γ w * f ((x : ℤ) + w).toNat := by
  rw [lintegral_rwhl, tsum_eq_sum_window hr]

/-- Upward steps of the walk on `ℤ₊`: `Pᵏ(x, x + kw) ≥ Γ(w)ᵏ` for `w ≥ 1`. -/
theorem rwhl_pow_up (Γ : ℤ → ℝ≥0∞) {w : ℕ} (hw : 1 ≤ w) (k x : ℕ) :
    Γ w ^ k ≤ (matKernel (rwhlMatrix Γ) ^ k) x {x + k * w} := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero_apply, zero_mul, add_zero, Measure.dirac_apply_of_mem (mem_singleton x)]
  | succ k ih =>
    have hstep : rwhlMatrix Γ (x + k * w) (x + (k + 1) * w) = Γ w := by
      have h0 : x + (k + 1) * w ≠ 0 := by positivity
      simp only [rwhlMatrix, h0, ite_false]
      congr 1; push_cast; ring
    calc Γ w ^ (k + 1) = Γ w ^ k * Γ w := pow_succ _ _
      _ ≤ (matKernel (rwhlMatrix Γ) ^ k) x {x + k * w} *
          (matKernel (rwhlMatrix Γ) ^ 1) (x + k * w) {x + (k + 1) * w} := by
          rw [matKernel_pow_one_singleton, hstep]; exact mul_le_mul' ih le_rfl
      _ ≤ _ := pow_add_singleton_ge _ k 1 x _ _

/-- With `Γ(w) > 0` for some `w < 0`, every state of the walk on `ℤ₊` reaches `0`, so the walk is
`δ₀`-irreducible (Proposition 4.3.1 on `ℤ₊`). -/
theorem rwhl_isPhiIrreducible_dirac {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1) {wn : ℤ} (hwn : wn < 0)
    (hΓn : Γ wn ≠ 0) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
    IsPhiIrreducible (matKernel (rwhlMatrix Γ)) (Measure.dirac 0) := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
  exact (isPhiIrreducible_dirac_iff _ 0).2 fun x => rwhl_hitProb_zero_pos hwn hΓn x

/-- A `ψ`-irreducible walk on `ℤ₊` charges `{0}`: `ψ{0} > 0`. -/
theorem rwhl_pos_zero {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1) {wn : ℤ} (hwn : wn < 0)
    (hΓn : Γ wn ≠ 0) {ψ : Measure ℕ}
    (hψ : haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
      IsMaximalIrreducibility (matKernel (rwhlMatrix Γ)) ψ) : 0 < ψ {0} := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
  have hac := hψ.2.2 _ (rwhl_isPhiIrreducible_dirac hΓ hwn hΓn)
  rw [pos_iff_ne_zero]
  intro h0
  have := hac h0
  simp at this

/-- **Proposition 8.4.6** (MT p. 192): for a bounded-range increment law with `Γ(w) > 0` for some
`w < 0`, the random walk on `ℤ₊` is recurrent iff its mean is `β ≤ 0`. For `β ≤ 0` the test
function is `V(x) = x` (Theorem 8.4.3); for `β > 0` it is `V(x) = 1 − ρˣ` with
`Σ_w Γ(w) ρʷ = 1`, `ρ < 1`, which has `ΔV = 0` for `x > r` (Theorem 8.4.2). -/
theorem proposition_8_4_6 {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1) {r : ℕ}
    (hr : ∀ w : ℤ, (r : ℤ) < |w| → Γ w = 0) {wn : ℤ} (hwn : wn < 0) (hΓn : Γ wn ≠ 0)
    {ψ : Measure ℕ}
    (hψ : haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
      IsMaximalIrreducibility (matKernel (rwhlMatrix Γ)) ψ) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
    (IsRecurrentChain (matKernel (rwhlMatrix Γ)) ψ ↔ rwMean Γ r ≤ 0) := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
  set P := matKernel (rwhlMatrix Γ)
  have htop := ne_top_of_tsum_eq_one hΓ
  have hmem : ∀ w, Γ w ≠ 0 → w ∈ window r := fun w hw => by
    by_contra h; exact hw (eq_zero_of_notMem_window hr h)
  have hlead : ∀ x, Leads P x 0 := fun x => Or.inr (rwhl_hitProb_zero_pos hwn hΓn x)
  have hfin : ∀ n : ℕ, IsPetite P {x : ℕ | x ≤ n} := fun n =>
    isPetite_of_finite P (Set.finite_Iic n) fun x _ => hlead x
  have hψ0 := rwhl_pos_zero hΓ hwn hΓn hψ
  have hcastN : ∀ (x : ℕ) (w : ℤ), 0 ≤ (x : ℤ) + w →
      ((((x : ℤ) + w).toNat : ℕ) : ℝ) = (x : ℝ) + w := fun x w h => by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h]; push_cast; ring
  constructor
  · -- `β > 0` gives transience
    intro hrec
    by_contra hβ
    push Not at hβ
    obtain ⟨wp, hwp, hΓp⟩ : ∃ w : ℤ, 0 < w ∧ Γ w ≠ 0 := by
      by_contra hc
      push Not at hc
      refine absurd hβ (not_lt.2 (Finset.sum_nonpos fun w _ => ?_))
      rcases le_or_gt w 0 with h | h
      · exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg (by exact_mod_cast h)
      · rw [hc w h, ENNReal.toReal_zero, zero_mul]
    obtain ⟨ρ, hρ0, hρ1, hρr⟩ := exists_root_of_mean_pos (S := window r)
      (g := fun w => (Γ w).toReal) (fun w => ENNReal.toReal_nonneg) (sum_window_toReal hΓ hr)
      hβ (hmem wn hΓn) hwn (ENNReal.toReal_pos hΓn (htop wn))
    set V : ℕ → ℝ := fun x => 1 - ρ ^ x with hV
    have hreach : 0 < ψ {x | r < x} := by
      rw [hψ.pos_iff_hitProb_pos (measurableSet_of_countable _)]
      intro y
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = wp := ⟨wp.toNat, Int.toNat_of_nonneg hwp.le⟩
      have hk1 : 1 ≤ k := by omega
      have h1 : 0 < (P ^ y) y {0} :=
        (ENNReal.pow_pos (pos_iff_ne_zero.2 hΓn) _).trans_le (rwhl_pow_zero_ge Γ hwn y y
          (by nlinarith))
      have h2 : 0 < (P ^ (r + 1)) 0 {0 + (r + 1) * k} := (ENNReal.pow_pos
        (pos_iff_ne_zero.2 (by rw [hk]; exact hΓp)) _).trans_le (rwhl_pow_up Γ hk1 (r + 1) 0)
      have h3 := pow_add_singleton_ge P y (r + 1) y 0 (0 + (r + 1) * k)
      refine (hitProb_pos_iff P (measurableSet_of_countable _) y).2 ⟨y + r, ?_⟩
      rw [show y + r + 1 = y + (r + 1) by omega]
      refine (ENNReal.mul_pos h1.ne' h2.ne').trans_le (h3.trans (measure_mono ?_))
      intro z hz
      rw [mem_singleton_iff.1 hz]
      simp only [mem_ofPred_eq, zero_add]
      nlinarith
    have htr : IsTransientChain P ψ := by
      refine isTransientChain_of_drift P hψ (C := {x | x ≤ r}) (measurableSet_of_countable _)
        (hψ0.trans_le (measure_mono (by simp))) (V := V) (measurable_of_countable _)
        (fun x => by simp only [V]; linarith [pow_le_one₀ hρ0.le hρ1.le (n := x)])
        (M := 1) (fun x => by simp only [V]; linarith [pow_pos hρ0 x]) (r := 1 - ρ ^ r)
        (fun y hy => by
          simp only [V, mem_ofPred_eq] at hy ⊢
          linarith [pow_le_pow_of_le_one hρ0.le hρ1.le hy]) (fun x hx => ?_)
        (hreach.trans_le (measure_mono fun x hx => by
          simp only [V, mem_ofPred_eq] at hx ⊢
          linarith [pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hx]))
      simp only [mem_ofPred_eq, not_le] at hx
      rw [driftR, integral_eq_sum_of_lintegral (Γ := Γ) htop (φ := fun w => ((x : ℤ) + w).toNat)
        (fun g => lintegral_rwhl_window hr x g) (measurable_of_countable _)
        (fun y => by simp only [V]; linarith [pow_le_one₀ hρ0.le hρ1.le (n := y)])
        (B := 1) (fun y => by simp only [V]; linarith [pow_pos hρ0 y]), sub_nonneg]
      refine le_of_eq ?_
      calc V x = ∑ w ∈ window r, (Γ w).toReal * (1 - ρ ^ (x : ℤ) * ρ ^ w) := by
            rw [Finset.sum_congr rfl fun w _ => by rw [mul_sub, mul_one],
              Finset.sum_sub_distrib, sum_window_toReal hΓ hr]
            simp only [V, zpow_natCast]
            congr 1
            calc ρ ^ x = ρ ^ x * ∑ w ∈ window r, (Γ w).toReal * ρ ^ w := by rw [hρr, mul_one]
              _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
        _ = ∑ w ∈ window r, (Γ w).toReal * V ((x : ℤ) + w).toNat := by
            refine Finset.sum_congr rfl fun w hw => ?_
            simp only [Finset.mem_Icc] at hw
            have hpos : 0 ≤ (x : ℤ) + w := by omega
            simp only [V]
            rw [← zpow_add₀ hρ0.ne', ← zpow_natCast, Int.toNat_of_nonneg hpos]
    exact htr.not_isRecurrentChain hrec
  · -- `β ≤ 0` gives recurrence
    intro hβ
    set V : ℕ → ℝ≥0 := fun x => (x : ℝ≥0)
    refine (theorem_8_4_3 P hψ (hfin r) (V := V) (measurable_of_countable _)
      (fun n => ?_) (fun x hx => ?_)).1
    · convert hfin n using 2
      simp [V]
    · rw [drift_nonpos_iff, lintegral_rwhl_window hr]
      simp only [mem_ofPred_eq, not_le] at hx
      have hc : ∀ w ∈ window r, ((V ((x : ℤ) + w).toNat : ℝ≥0) : ℝ≥0∞) =
          ENNReal.ofReal ((x : ℝ) + 1 * w) := fun w hw => by
        simp only [Finset.mem_Icc] at hw
        simp only [V, ENNReal.coe_natCast]
        rw [← ENNReal.ofReal_natCast, hcastN x w (by omega), one_mul]
      rw [Finset.sum_congr rfl fun w hw => by rw [hc w hw],
        sum_window_ofReal hΓ fun w hw => by
          simp only [Finset.mem_Icc] at hw
          rw [one_mul]; exact_mod_cast (show (0 : ℤ) ≤ x + w by omega),
        sum_window_affine hΓ hr, one_mul]
      simp only [V, ENNReal.coe_natCast]
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Every bounded-range walk on `ℤ₊` with `Γ(w) > 0` for some `w < 0` has a maximal
irreducibility measure. -/
theorem rwhl_exists_maximal {Γ : ℤ → ℝ≥0∞} (hΓ : ∑' w, Γ w = 1) {wn : ℤ} (hwn : wn < 0)
    (hΓn : Γ wn ≠ 0) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
    ∃ ψ, IsMaximalIrreducibility (matKernel (rwhlMatrix Γ)) ψ := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix hΓ)
  obtain ⟨ψ, hψ, -⟩ := theorem_4_0_1 _ (rwhl_isPhiIrreducible_dirac hΓ hwn hΓn)
    (by simp)
  exact ⟨ψ, hψ⟩

/-- The increment law `δ₀`. -/
noncomputable def diracInc (w : ℤ) : ℝ≥0∞ := if w = 0 then 1 else 0

/-- `δ₀` is a probability on `ℤ`. -/
theorem tsum_diracInc : ∑' w, diracInc w = 1 := by
  unfold diracInc; exact tsum_ite_eq 0 1

/-- **Correction to Proposition 8.4.6**: the hypothesis `Γ(−∞, 0) > 0` is needed. For `Γ = δ₀` the
mean is `β = 0`, but the walk on `ℤ₊` never moves, `{0}` and `{1}` are disjoint absorbing sets,
and the walk is irreducible for no nonzero measure, so it is not recurrent. -/
theorem proposition_8_4_6_counterexample :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix tsum_diracInc)
    rwMean diracInc 0 = 0 ∧ ∀ ψ, ¬ IsRecurrentChain (matKernel (rwhlMatrix diracInc)) ψ := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix tsum_diracInc)
  refine ⟨by simp [rwMean, window], fun ψ h => ?_⟩
  have h0 : IsAbsorbing (matKernel (rwhlMatrix diracInc)) {0} :=
    (isAbsorbing_matKernel_iff _).2 fun x hx y hy => by
      rw [mem_singleton_iff.1 hx]
      have hy0 : y ≠ 0 := hy
      simp [rwhlMatrix, hy0, diracInc]
  have h1 : IsAbsorbing (matKernel (rwhlMatrix diracInc)) {1} :=
    (isAbsorbing_matKernel_iff _).2 fun x hx y hy => by
      rw [mem_singleton_iff.1 hx]
      have hy1 : y ≠ 1 := hy
      unfold rwhlMatrix
      by_cases hy0 : y = 0
      · simp only [hy0, ite_true, Nat.cast_one]
        refine ENNReal.tsum_eq_zero.2 fun k => ?_
        by_cases hk : k ≤ -1
        · have : k ≠ 0 := by omega
          simp [hk, diracInc, this]
        · simp [hk]
      · have : (y : ℤ) - 1 ≠ 0 := by omega
        simp [hy0, diracInc, this]
  exact h.1.1 (not_isPhiIrreducible_of_disjoint_absorbing (measurableSet_singleton 0)
    (measurableSet_singleton 1) (singleton_nonempty 0) (singleton_nonempty 1) (by simp) h0 h1
    h.1.2.1)

/-! ### Simple random walk on `ℤ₊` -/

/-- The increment law `p δ₋₁ + q δ₁` of the simple (Bernoulli) random walk (MT p. 176). -/
noncomputable def srwInc (p q : ℝ≥0∞) (w : ℤ) : ℝ≥0∞ :=
  if w = -1 then p else if w = 1 then q else 0

/-- `p δ₋₁ + q δ₁` is a probability when `p + q = 1`. -/
theorem tsum_srwInc {p q : ℝ≥0∞} (hpq : p + q = 1) : ∑' w, srwInc p q w = 1 := by
  have : ∀ w, srwInc p q w = (if w = -1 then p else 0) + (if w = 1 then q else 0) := fun w => by
    unfold srwInc; split_ifs <;> simp_all
  simp_rw [this]
  rw [ENNReal.tsum_add, tsum_ite_eq, tsum_ite_eq, hpq]

/-- The simple random walk has range `1`. -/
theorem srwInc_range (p q : ℝ≥0∞) : ∀ w : ℤ, ((1 : ℕ) : ℤ) < |w| → srwInc p q w = 0 :=
  fun w hw => by
    unfold srwInc
    have h1 : w ≠ -1 := by rintro rfl; simp at hw
    have h2 : w ≠ 1 := by rintro rfl; simp at hw
    simp [h1, h2]

/-- The window `[−1, 1]`. -/
theorem window_one : window 1 = {-1, 0, 1} := by decide

/-- The mean of the simple random walk is `q − p`. -/
theorem rwMean_srwInc (p q : ℝ≥0∞) : rwMean (srwInc p q) 1 = q.toReal - p.toReal := by
  rw [rwMean, window_one]
  simp [srwInc]
  ring

/-- The first-step equations of the simple random walk (MT p. 176): `L(0, 0) = p + q L(1, 0)`. -/
theorem srw_hitProb_zero_eq {p q : ℝ≥0∞} (hpq : p + q = 1) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
    hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 0 =
      p + q * hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 1 := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
  have h0 := measurableSet_singleton (0 : ℕ)
  rw [hitProb_first_step _ h0, ← lintegral_indicator h0.compl, lintegral_rwhl_window
    (srwInc_range p q), matKernel_singleton, window_one]
  have hP : rwhlMatrix (srwInc p q) 0 0 = p := by
    simp only [rwhlMatrix, ite_true, Nat.cast_zero, neg_zero]
    rw [tsum_eq_single (-1) fun k hk => by unfold srwInc; split_ifs <;> simp_all]
    simp [srwInc]
  rw [hP]
  simp [srwInc]

/-- The first-step equations of the simple random walk (MT p. 176): `L(1, 0) = p + q L(2, 0)`. -/
theorem srw_hitProb_one_eq {p q : ℝ≥0∞} (hpq : p + q = 1) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
    hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 1 =
      p + q * hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 2 := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
  have h0 := measurableSet_singleton (0 : ℕ)
  rw [hitProb_first_step _ h0, ← lintegral_indicator h0.compl, lintegral_rwhl_window
    (srwInc_range p q), matKernel_singleton, window_one]
  have hP : rwhlMatrix (srwInc p q) 1 0 = p := by
    simp only [rwhlMatrix, ite_true, Nat.cast_one]
    rw [tsum_eq_single (-1) fun k hk => by unfold srwInc; split_ifs <;> simp_all]
    simp [srwInc]
  rw [hP]
  simp [srwInc]

/-- **Simple random walk** (MT p. 176): if `p ≥ q` then `L(0, 0) = L(1, 0) = 1`. -/
theorem srw_hitProb_zero {p q : ℝ≥0∞} (hpq : p + q = 1) (hqp : q ≤ p) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
    hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 0 = 1 ∧
      hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 1 = 1 := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
  set P := matKernel (rwhlMatrix (srwInc p q))
  have hpne : srwInc p q (-1) ≠ 0 := by
    simp only [srwInc, ite_true]
    rintro rfl
    have : q = 0 := le_antisymm hqp zero_le
    rw [this, add_zero] at hpq
    exact zero_ne_one hpq
  rcases eq_or_ne q 0 with hq | hq
  · -- `q = 0`: the walk only moves down
    rw [hq, add_zero] at hpq
    have hstep : ∀ x : ℕ, x ≤ 1 → (1 : ℝ≥0∞) ≤ P x {0} := fun x hx => by
      rw [matKernel_singleton]
      refine le_trans ?_ (rwhl_zero_ge _ (w := -1) (by omega))
      simp [srwInc, hpq]
    refine ⟨le_antisymm (hitProb_le_one _ _ _) ((hstep 0 (by omega)).trans ?_),
      le_antisymm (hitProb_le_one _ _ _) ((hstep 1 le_rfl).trans ?_)⟩ <;>
    · have := pow_le_hitProb P (measurableSet_singleton 0) 0
      simpa using this _
  · -- `q > 0`: the walk is irreducible and recurrent
    have hirr : IsIrreducibleChain P := by
      have : Nonempty ℕ := ⟨0⟩
      rw [isIrreducibleChain_iff]
      have hto : ∀ x, Leads P x 0 := fun x => Or.inr (rwhl_hitProb_zero_pos (by omega) hpne x)
      have hfrom : ∀ y, Leads P 0 y := fun y => by
        refine (leads_iff_exists_pow P 0 y).2 ⟨y, ?_⟩
        have := rwhl_pow_up (srwInc p q) (w := 1) le_rfl y 0
        simp only [zero_add, mul_one, Nat.cast_one, srwInc] at this
        exact (ENNReal.pow_pos (by simpa using pos_iff_ne_zero.2 hq) y).trans_le
          (by simpa using this)
      exact fun x y => ⟨(hto x).trans (hfrom y), (hto y).trans (hfrom x)⟩
    have hmax := isMaximalIrreducibility_count P hirr
    have hrec := (proposition_8_4_6 (tsum_srwInc hpq) (srwInc_range p q) (wn := -1)
      (by norm_num) hpne hmax).2 (by
        rw [rwMean_srwInc, sub_nonpos]
        exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
          (hpq ▸ le_self_add)) hqp)
    rcases proposition_8_1_4 P hirr with h | h
    · exact ⟨h 0 0, h 1 0⟩
    · have := (proposition_8_1_3 P 0).1 (hrec.2 {0} (measurableSet_singleton 0) (by simp) 0)
      exact absurd this (h 0).ne

/-- **Passage through intermediate states** for a chain on `ℤ₊` that never jumps down by more
than one step (`P(z, {w : w + 1 < z}) = 0`): to go from `x + 1` to `0` it must pass `x`, so
`L(x + 1, 0) = L(x + 1, x) L(x, 0)` for `x ≥ 1` (MT p. 176, "skip-free to the left"). -/
theorem hitProb_passage {P : Kernel ℕ ℕ} [IsMarkovKernel P] (hP : ∀ z, P z {w | w + 1 < z} = 0)
    {x : ℕ} (hx : 1 ≤ x) :
    hitProb P {0} (x + 1) = hitProb P {x} (x + 1) * hitProb P {0} x := by
  classical
  have := isMarkovKernel_pathKernel P
  have h0 := measurableSet_singleton (0 : ℕ)
  have hxm := measurableSet_singleton x
  refine le_antisymm ?_ (by
    rw [mul_comm]
    exact hitProb_ge_mul P hxm h0 (fun y hy => by rw [mem_singleton_iff.1 hy]) (x + 1))
  -- the paths with a downward jump of two or more are null
  set N : Set (ℕ → ℕ) := {ω | ∃ n, ω (n + 1) + 1 < ω n} with hNdef
  have hN : pathKernel P (x + 1) N = 0 := by
    have hcov : N ⊆ ⋃ n, ⋃ z : ℕ, {ω : ℕ → ℕ | ω n ∈ ({z} : Set ℕ)} ∩
        shift n ⁻¹' {ω' : ℕ → ℕ | ω' 1 ∈ {w : ℕ | w + 1 < z}} := by
      rintro ω ⟨n, hn⟩
      exact mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨ω n, rfl, by simpa [shift_apply] using hn⟩⟩
    refine measure_mono_null hcov (measure_iUnion_null fun n => measure_iUnion_null fun z => ?_)
    rw [pathKernel_coord_inter_shift P _ n (C := {z})
      (S := {ω' : ℕ → ℕ | ω' 1 ∈ {w : ℕ | w + 1 < z}}) (measurableSet_singleton z)
      (measurable_pi_apply 1 (measurableSet_of_countable _)), lintegral_singleton,
      pathKernel_coord_mem P z 1 (measurableSet_of_countable _), pow_one, hP z, zero_mul]
  have hZ : pathKernel P (x + 1) {ω | ω 0 ∈ ({x + 1} : Set ℕ)ᶜ} = 0 := by
    rw [pathKernel_zero_mem P _ (measurableSet_singleton _).compl, indicator_of_notMem (by simp)]
  have hτ := (proposition_3_4_4 hxm).1
  set S0 : Set (ℕ → ℕ) := {ω | firstReturn {0} ω ≠ ⊤}
  have hS0 : MeasurableSet S0 := measurableSet_firstReturn_ne_top h0
  have hT : MeasurableSet {ω : ℕ → ℕ | firstReturn {x} ω ≠ ⊤} := measurableSet_ne_top hτ
  -- pathwise: a path from `x + 1` to `0` with no big downward jump passes `x`
  have hsub : {ω : ℕ → ℕ | firstReturn {0} ω ≠ ⊤} ⊆
      N ∪ {ω | ω 0 ∈ ({x + 1} : Set ℕ)ᶜ} ∪
        ({ω | firstReturn {x} ω ≠ ⊤} ∩ shiftAt (firstReturn {x}) ⁻¹' S0) := by
    intro ω hω
    by_cases hωN : ω ∈ N
    · exact Or.inl (Or.inl hωN)
    by_cases hω0 : ω 0 = x + 1
    swap
    · exact Or.inl (Or.inr hω0)
    right
    simp only [hNdef, mem_ofPred_eq, not_exists, not_lt] at hωN
    obtain ⟨t, ht1, ht⟩ := (firstReturn_ne_top_iff {0} ω).1 hω
    rw [mem_singleton_iff] at ht
    have hex : ∃ n, ω n ≤ x := ⟨t, by omega⟩
    set s := Nat.find hex
    have hs : ω s ≤ x := Nat.find_spec hex
    have hs0 : s ≠ 0 := by intro h; have := hs; rw [h, hω0] at this; omega
    have hprev : ¬ ω (s - 1) ≤ x := Nat.find_min hex (by omega)
    have hjump := hωN (s - 1)
    rw [show s - 1 + 1 = s by omega] at hjump
    have hsx : ω s = x := by omega
    have hst : s ≤ t := Nat.find_min' hex (by omega)
    have hτx : firstReturn {x} ω ≠ ⊤ := (firstReturn_ne_top_iff {x} ω).2 ⟨s, by omega, hsx⟩
    refine ⟨hτx, ?_⟩
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hτx
    have hmx : ω m = x := by
      have := stoppedState_firstReturn_mem {x} hτx
      rwa [stoppedState_of_eq hm.symm, mem_singleton_iff] at this
    have hms : m ≤ s := by
      have := hittingAfter_le_of_mem (u := fun n (ω : ℕ → ℕ) => ω n) (s := ({x} : Set ℕ))
        (n := 1) (i := s) (ω := ω) (by omega) (mem_singleton_iff.2 hsx)
      rw [← firstReturn, ← hm] at this
      exact WithTop.coe_le_coe.1 this
    have hmt : m < t := by
      rcases lt_or_ge m t with h | h
      · exact h
      · exfalso
        have : m = t := by omega
        rw [this, ht] at hmx
        omega
    simp only [mem_preimage, shiftAt_of_eq hm.symm, S0, mem_ofPred_eq]
    exact (firstReturn_ne_top_iff {0} _).2 ⟨t - m, by omega, by
      rw [shift_apply, show m + (t - m) = t by omega, ht]; rfl⟩
  have hE : pathKernel P (x + 1) ({ω | firstReturn {x} ω ≠ ⊤} ∩
      shiftAt (firstReturn {x}) ⁻¹' S0) = hitProb P {x} (x + 1) * hitProb P {0} x := by
    have hsm := strong_markov_lintegral P (Measure.dirac (x + 1)) hτ MeasurableSet.univ
      (measurable_one.indicator hS0)
    rw [pathMeasure_dirac, univ_inter] at hsm
    simp_rw [lintegral_indicator_one hS0] at hsm
    have hpre : MeasurableSet (shiftAt (firstReturn {x}) ⁻¹' S0) := (measurable_shiftAt hτ) hS0
    have e1 : pathKernel P (x + 1) ({ω | firstReturn {x} ω ≠ ⊤} ∩
        shiftAt (firstReturn {x}) ⁻¹' S0) = ∫⁻ ω in {ω | firstReturn {x} ω ≠ ⊤},
          S0.indicator 1 (shiftAt (firstReturn {x}) ω) ∂pathKernel P (x + 1) := by
      calc pathKernel P (x + 1) ({ω | firstReturn {x} ω ≠ ⊤} ∩
            shiftAt (firstReturn {x}) ⁻¹' S0)
          = ((pathKernel P (x + 1)).restrict {ω | firstReturn {x} ω ≠ ⊤})
              (shiftAt (firstReturn {x}) ⁻¹' S0) := by rw [Measure.restrict_apply hpre, inter_comm]
        _ = ∫⁻ ω in {ω | firstReturn {x} ω ≠ ⊤},
              (shiftAt (firstReturn {x}) ⁻¹' S0).indicator 1 ω ∂pathKernel P (x + 1) :=
            (lintegral_indicator_one hpre).symm
        _ = _ := rfl
    rw [e1, hsm, setLIntegral_congr_fun hT fun ω hω => by
      rw [show stoppedState (firstReturn {x}) ω = x from
        mem_singleton_iff.1 (stoppedState_firstReturn_mem {x} hω)],
      setLIntegral_const, mul_comm]
    rfl
  calc hitProb P {0} (x + 1) ≤ pathKernel P (x + 1) (N ∪ {ω | ω 0 ∈ ({x + 1} : Set ℕ)ᶜ} ∪
        ({ω | firstReturn {x} ω ≠ ⊤} ∩ shiftAt (firstReturn {x}) ⁻¹' S0)) := measure_mono hsub
    _ ≤ pathKernel P (x + 1) N + pathKernel P (x + 1) {ω | ω 0 ∈ ({x + 1} : Set ℕ)ᶜ} +
        pathKernel P (x + 1) ({ω | firstReturn {x} ω ≠ ⊤} ∩
          shiftAt (firstReturn {x}) ⁻¹' S0) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = _ := by rw [hN, hZ, hE, zero_add, zero_add]

/-- The simple random walk never jumps down by more than one step. -/
theorem srw_skipFree_down (p q : ℝ≥0∞) (z : ℕ) :
    matKernel (rwhlMatrix (srwInc p q)) z {w | w + 1 < z} = 0 := by
  rw [← lintegral_indicator_one (measurableSet_of_countable _),
    lintegral_rwhl_window (srwInc_range p q), window_one]
  have h1 : ¬ (((z : ℤ) + -1).toNat + 1 < z) := by omega
  simp [srwInc, h1, (by omega : z ≤ z + 1 + 1)]

/-- Translation invariance of the simple random walk away from `0` (MT p. 176):
`L(x + 1, x) = L(1, 0)`. -/
theorem srw_hitProb_translate {p q : ℝ≥0∞} (hpq : p + q = 1) (x : ℕ) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
    hitProb (matKernel (rwhlMatrix (srwInc p q))) {x} (x + 1) =
      hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 1 := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
  set P := matKernel (rwhlMatrix (srwInc p q))
  have hxm := measurableSet_singleton x
  have h0 := measurableSet_singleton (0 : ℕ)
  -- the step law: `∫ P(y, dz) f(z) = p f(y − 1) + q f(y + 1)` for `y ≥ 1`
  have hstep : ∀ (y : ℕ) (f : ℕ → ℝ≥0∞), ∫⁻ z, f z ∂P (y + 1) = p * f y + q * f (y + 2) := by
    intro y f
    rw [lintegral_rwhl_window (srwInc_range p q), window_one]
    have e2 : ((y : ℤ) + 1 + 1).toNat = y + 2 := by omega
    simp [srwInc, e2]
  have key : ∀ n k : ℕ, tabooKernel P hxm n (x + 1 + k) {x} =
      tabooKernel P h0 n (1 + k) {0} := by
    intro n
    induction n with
    | zero =>
      intro k
      rw [tabooKernel_zero, tabooKernel_zero, matKernel_singleton, matKernel_singleton]
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · rfl
      · have hxne : x ≠ 0 := by omega
        simp only [rwhlMatrix, hxne, ite_false, ite_true]
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [tsum_eq_single (-1) fun w hw => by
            unfold srwInc; split_ifs <;> first | rfl | omega]
          simp [srwInc]
        · rw [ENNReal.tsum_eq_zero.2 fun w => by unfold srwInc; split_ifs <;> first | rfl | omega]
          unfold srwInc
          split_ifs <;> first | rfl | omega
    | succ n ih =>
      intro k
      rw [tabooKernel_succ_apply P hxm n _ hxm, tabooKernel_succ_apply P h0 n _ h0,
        ← lintegral_indicator hxm.compl, ← lintegral_indicator h0.compl,
        show x + 1 + k = (x + k) + 1 by omega, show 1 + k = k + 1 by omega, hstep, hstep]
      congr 1
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp
        · rw [indicator_of_mem (show x + k ∈ ({x} : Set ℕ)ᶜ by simp; omega),
            indicator_of_mem (show k ∈ ({0} : Set ℕ)ᶜ by simp; omega),
            show x + k = x + 1 + (k - 1) by omega, ih, show 1 + (k - 1) = k by omega]
      · rw [indicator_of_mem (show x + k + 2 ∈ ({x} : Set ℕ)ᶜ by
            simp only [mem_compl_iff, mem_singleton_iff]; omega),
          indicator_of_mem (show k + 2 ∈ ({0} : Set ℕ)ᶜ by simp),
          show x + k + 2 = x + 1 + (k + 1) by omega, ih, show 1 + (k + 1) = k + 2 by omega]
  rw [hitProb_eq_tsum P hxm, hitProb_eq_tsum P h0]
  exact tsum_congr fun n => by simpa using key n 0

/-- **(8.13)** for the simple random walk (MT p. 176): `L(1, 0) = p + q L(1, 0)²`, by the
first-step equation, `L(2, 0) = L(2, 1) L(1, 0)` (skip-free to the left) and
`L(2, 1) = L(1, 0)` (translation invariance). -/
theorem srw_quadratic {p q : ℝ≥0∞} (hpq : p + q = 1) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
    hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 1 =
      p + q * hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 1 ^ 2 := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
  conv_lhs => rw [srw_hitProb_one_eq hpq]
  rw [hitProb_passage (srw_skipFree_down p q) le_rfl, srw_hitProb_translate hpq 1, sq]

/-- MT p. 176: the root of (8.13): `L(1, 0) = 1` or `L(1, 0) = p/q`. -/
theorem srw_hitProb_one_root {p q : ℝ≥0∞} (hpq : p + q = 1) (hq : q ≠ 0) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
    hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 1 = 1 ∨
      hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 1 = p / q := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
  set ℓ := hitProb (matKernel (rwhlMatrix (srwInc p q))) {0} 1
  have hℓ := srw_quadratic hpq
  have hpf : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hpq ▸ le_self_add)
  have hqf : q ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hpq ▸ le_add_self)
  have hℓf : ℓ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hitProb_le_one _ _ _)
  have hr := congrArg ENNReal.toReal hℓ
  change ℓ.toReal = (p + q * ℓ ^ 2).toReal at hr
  rw [ENNReal.toReal_add hpf (ENNReal.mul_ne_top hqf (ENNReal.pow_ne_top hℓf)),
    ENNReal.toReal_mul, ENNReal.toReal_pow] at hr
  have hsum := congrArg ENNReal.toReal hpq
  rw [ENNReal.toReal_add hpf hqf, ENNReal.toReal_one] at hsum
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos hq hqf
  have hfac : (q.toReal * ℓ.toReal - p.toReal) * (ℓ.toReal - 1) = 0 := by
    have e : (q.toReal * ℓ.toReal - p.toReal) * (ℓ.toReal - 1) =
        q.toReal * ℓ.toReal ^ 2 - (p.toReal + q.toReal) * ℓ.toReal + p.toReal := by ring
    rw [e, hsum]
    linarith
  rcases mul_eq_zero.1 hfac with h | h
  · right
    rw [← ENNReal.ofReal_toReal hℓf, ← ENNReal.ofReal_toReal (ENNReal.div_ne_top hpf hq),
      ENNReal.toReal_div]
    congr 1
    field_simp
    linarith
  · left
    rw [← ENNReal.ofReal_toReal hℓf, show ℓ.toReal = 1 by linarith, ENNReal.ofReal_one]

/-- `⅓ + ⅔ = 1`. -/
theorem third_add_two_thirds : (3⁻¹ : ℝ≥0∞) + 2 * 3⁻¹ = 1 := by
  calc (3⁻¹ : ℝ≥0∞) + 2 * 3⁻¹ = 3 * 3⁻¹ := by ring
    _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- **Correction to Theorem 8.3.6 (i)**: the empty set is petite and satisfies `L(x, C) = 1` for
every `x ∈ C` vacuously, yet the random walk on `ℤ₊` with `Γ = ⅓δ₋₁ + ⅔δ₁` (mean `⅓ > 0`) is
`ψ`-irreducible and not recurrent. Theorem 8.3.6 (i) needs `C ≠ ∅`. -/
theorem theorem_8_3_6_i_counterexample :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix
      (tsum_srwInc third_add_two_thirds))
    ∃ ψ, IsMaximalIrreducibility (matKernel (rwhlMatrix (srwInc 3⁻¹ (2 * 3⁻¹)))) ψ ∧
      IsPetite (matKernel (rwhlMatrix (srwInc 3⁻¹ (2 * 3⁻¹)))) ∅ ∧
      (∀ x ∈ (∅ : Set ℕ), hitProb (matKernel (rwhlMatrix (srwInc 3⁻¹ (2 * 3⁻¹)))) ∅ x = 1) ∧
      ¬ IsRecurrentChain (matKernel (rwhlMatrix (srwInc 3⁻¹ (2 * 3⁻¹)))) ψ := by
  have hpq := third_add_two_thirds
  have := isMarkovKernel_matKernel (isTransitionMatrix_rwhlMatrix (tsum_srwInc hpq))
  have hpne : srwInc 3⁻¹ (2 * 3⁻¹) (-1) ≠ 0 := by simp [srwInc]
  obtain ⟨ψ, hψ⟩ := rwhl_exists_maximal (tsum_srwInc hpq) (wn := -1) (by norm_num) hpne
  refine ⟨ψ, hψ, ⟨diracDist 1, Measure.dirac 0, MeasurableSet.empty, isSamplingDist_diracDist 1,
    by simp, fun x hx => absurd hx (notMem_empty x)⟩, fun x hx => absurd hx (notMem_empty x),
    fun h => ?_⟩
  have := (proposition_8_4_6 (tsum_srwInc hpq) (srwInc_range _ _) (wn := -1) (by norm_num) hpne
    hψ).1 h
  rw [rwMean_srwInc] at this
  have h3 : (3⁻¹ : ℝ≥0∞).toReal = 3⁻¹ := by simp
  rw [ENNReal.toReal_mul, h3] at this
  norm_num at this

end MeynTweedie.InvariantMeasures

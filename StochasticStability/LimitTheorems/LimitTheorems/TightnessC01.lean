/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.PathSpaceC01
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tightness in `C([0,1], ℝ)`: modulus of continuity, Arzelà–Ascoli, Billingsley's criterion

Generic tightness machinery on the path space, used for the functional CLT (MT, Theorem 17.4.4,
p. 446, and Theorem D.6.4). References are to Billingsley, *Convergence of Probability Measures*
(2nd ed., 1999), §7.

## Modulus of continuity

* `modulus f δ = sup_{dist s t ≤ δ} |f s − f t|` (Billingsley (7.1)); `modulus_nonneg`,
  `abs_sub_le_modulus`, `abs_sub_le_modulus'`, `modulus_le`, `modulus_mono`,
  `modulus_le_two_norm`.
* `abs_modulus_sub_le`: `|w(f,δ) − w(g,δ)| ≤ 2 ‖f − g‖`; hence `continuous_modulus`,
  `measurable_modulus`.
* `exists_modulus_lt`, `tendsto_modulus_zero`: `w(f, δ) → 0` as `δ → 0⁺`.
* `abs_sub_zero_le_mul_modulus`: chaining, `|f t − f 0| ≤ m · w(f, 1/m)`.

## Compact sets (Arzelà–Ascoli, Billingsley Thm 7.2)

* `arzelaAscoliSet a δ ε = {f | |f 0| ≤ a ∧ ∀ j, w(f, δ j) ≤ ε j}`;
  `isCompact_arzelaAscoliSet` (for `δ j > 0`, `ε j → 0`), via Mathlib's
  `BoundedContinuousFunction.arzela_ascoli₂`.

## Tightness criterion (Billingsley Thm 7.3, sufficiency)

* `isTightMeasureSet_of_modulus`: (i) `μₙ {|f 0| > a} ≤ η` for all `n` and (ii) for all
  `ε, η > 0`, some `δ > 0`, `N` with `μₙ {w(f, δ) ≥ ε} ≤ η` for `n ≥ N`, imply tightness.
  `isTightMeasureSet_of_modulus'`: (i) as tightness of the laws of `f 0`.
  `isTightMeasureSet_map_of_modulus`: the version for random elements `Xₙ : Ωₙ → C`.
* Helpers: `exists_delta_measure_modulus_le` (one measure), and
  `exists_delta_measure_modulus_le_of_lt` (finitely many).

## Partial-sum processes (Billingsley Thm 7.4 and (7.12), (8.12) type)

* `modulus_le_three_mul_of_blocks`: if the path moves at most `β` within each block
  `[ih, (i+1)h]` from its left end, then `w(f, h) ≤ 3β`.
* `abs_polygonal_sub_block_le`, `modulus_polygonal_le_of_blocks`: the same for polygonal paths
  in terms of the increments of `s` on index blocks of length `L`.
* `measure_modulus_polygonal_le`, `modulus_condition_polygonal_of_blocks`: for
  `Xₙ = polygonal n (n^{-1/2} S)`, the block condition
  `m · Q {∃ i ≤ n/m + 1, |S (j+i) − S j| ≥ ε √n} ≤ η` (all `n ≥ N`, all `j`) gives (ii).
* `isTightMeasureSet_polygonal_of_blocks`: with `S 0 = 0`, the laws of `Xₙ` are tight.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-- The modulus of continuity `w(f, δ) = sup_{|s − t| ≤ δ} |f s − f t|` of a path
`f ∈ C([0,1], ℝ)` (Billingsley, *Convergence of Probability Measures*, (7.1)). It is `0` for
`δ < 0` (empty supremum). -/
noncomputable def modulus (f : C(unitInterval, ℝ)) (δ : ℝ) : ℝ :=
  ⨆ p : {p : unitInterval × unitInterval // dist p.1 p.2 ≤ δ}, |f p.1.1 - f p.1.2|

/-- The increments of a path are bounded by twice its norm. -/
theorem abs_sub_le_two_norm (f : C(unitInterval, ℝ)) (s t : unitInterval) :
    |f s - f t| ≤ 2 * ‖f‖ := by
  have hs := f.norm_coe_le_norm s
  have ht := f.norm_coe_le_norm t
  rw [Real.norm_eq_abs] at hs ht
  calc |f s - f t| ≤ |f s| + |f t| := abs_sub _ _
    _ ≤ 2 * ‖f‖ := by linarith

/-- The set of increments over pairs at distance `≤ δ` is bounded above. -/
theorem bddAbove_modulus (f : C(unitInterval, ℝ)) (δ : ℝ) :
    BddAbove (range fun p : {p : unitInterval × unitInterval // dist p.1 p.2 ≤ δ} =>
      |f p.1.1 - f p.1.2|) :=
  ⟨2 * ‖f‖, by
    rintro _ ⟨p, rfl⟩
    exact abs_sub_le_two_norm f _ _⟩

/-- The modulus of continuity is nonnegative. -/
theorem modulus_nonneg (f : C(unitInterval, ℝ)) (δ : ℝ) : 0 ≤ modulus f δ :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- An increment over a pair at distance `≤ δ` is bounded by the modulus. -/
theorem abs_sub_le_modulus (f : C(unitInterval, ℝ)) {δ : ℝ} {s t : unitInterval}
    (h : dist s t ≤ δ) : |f s - f t| ≤ modulus f δ :=
  le_ciSup (f := fun p : {p : unitInterval × unitInterval // dist p.1 p.2 ≤ δ} =>
    |f p.1.1 - f p.1.2|) (bddAbove_modulus f δ) ⟨(s, t), h⟩

/-- `|s − t|` form of `abs_sub_le_modulus`. -/
theorem abs_sub_le_modulus' (f : C(unitInterval, ℝ)) {δ : ℝ} {s t : unitInterval}
    (h : |(s : ℝ) - t| ≤ δ) : |f s - f t| ≤ modulus f δ :=
  abs_sub_le_modulus f (by rwa [Subtype.dist_eq, Real.dist_eq])

/-- Bounding the modulus: if every increment over a pair at distance `≤ δ` is at most `C ≥ 0`,
then `modulus f δ ≤ C`. -/
theorem modulus_le (f : C(unitInterval, ℝ)) {δ C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s t : unitInterval, dist s t ≤ δ → |f s - f t| ≤ C) : modulus f δ ≤ C :=
  Real.iSup_le (fun p => h _ _ p.2) hC

/-- The modulus is monotone in `δ`. -/
theorem modulus_mono (f : C(unitInterval, ℝ)) : Monotone (modulus f) := fun _ _ hδ =>
  modulus_le f (modulus_nonneg f _) fun _ _ h => abs_sub_le_modulus f (h.trans hδ)

/-- `modulus f δ ≤ 2 ‖f‖`. -/
theorem modulus_le_two_norm (f : C(unitInterval, ℝ)) (δ : ℝ) : modulus f δ ≤ 2 * ‖f‖ :=
  modulus_le f (by positivity) fun s t _ => abs_sub_le_two_norm f s t

/-- One-sided Lipschitz bound: `modulus f δ ≤ modulus g δ + 2 ‖f − g‖`. -/
theorem modulus_le_modulus_add (f g : C(unitInterval, ℝ)) (δ : ℝ) :
    modulus f δ ≤ modulus g δ + 2 * ‖f - g‖ := by
  refine modulus_le f (by positivity [modulus_nonneg g δ]) fun s t h => ?_
  have hs := (f - g).norm_coe_le_norm s
  have ht := (f - g).norm_coe_le_norm t
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs] at hs ht
  have hg := abs_sub_le_modulus g h
  calc |f s - f t| = |(g s - g t) + ((f s - g s) - (f t - g t))| := by ring_nf
    _ ≤ |g s - g t| + (|f s - g s| + |f t - g t|) :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
    _ ≤ modulus g δ + 2 * ‖f - g‖ := by linarith

/-- The modulus is `2`-Lipschitz in the path: `|w(f,δ) − w(g,δ)| ≤ 2 ‖f − g‖`. -/
theorem abs_modulus_sub_le (f g : C(unitInterval, ℝ)) (δ : ℝ) :
    |modulus f δ - modulus g δ| ≤ 2 * ‖f - g‖ := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [modulus_le_modulus_add f g δ]
  · have := modulus_le_modulus_add g f δ
    rw [← norm_neg (g - f), neg_sub] at this
    linarith

/-- The modulus `f ↦ w(f, δ)` is continuous on `C([0,1], ℝ)`. -/
theorem continuous_modulus (δ : ℝ) : Continuous fun f : C(unitInterval, ℝ) => modulus f δ := by
  refine Metric.continuous_iff.mpr fun f ε hε => ⟨ε / 2, by positivity, fun g hg => ?_⟩
  rw [Real.dist_eq]
  rw [dist_eq_norm] at hg
  have := abs_modulus_sub_le g f δ
  linarith

/-- The modulus is measurable for any Borel σ-algebra on the path space. -/
theorem measurable_modulus [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] (δ : ℝ) :
    Measurable fun f : C(unitInterval, ℝ) => modulus f δ :=
  (continuous_modulus δ).measurable

/-- Uniform continuity: every path has `w(f, δ) < ε` for some `δ > 0`. -/
theorem exists_modulus_lt (f : C(unitInterval, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, modulus f δ < ε := by
  have hu := CompactSpace.uniformContinuous_of_continuous f.continuous
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.mp hu (ε / 2) (by positivity)
  refine ⟨δ / 2, by positivity, ?_⟩
  refine (modulus_le f (C := ε / 2) (by positivity) fun s t hst => ?_).trans_lt (by linarith)
  have := h (lt_of_le_of_lt hst (by linarith))
  rw [Real.dist_eq] at this
  exact this.le

/-- `w(f, δ) → 0` as `δ → 0⁺`. -/
theorem tendsto_modulus_zero (f : C(unitInterval, ℝ)) :
    Tendsto (modulus f) (𝓝[>] 0) (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := exists_modulus_lt f hε
  have : Ioo (0 : ℝ) δ ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT hδ
  filter_upwards [this] with x hx
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (modulus_nonneg f x)]
  exact (modulus_mono f hx.2.le).trans_lt h

/-- Chaining bound: `|f t − f 0| ≤ m · w(f, 1/m)` for `m ≥ 1` (split `[0, t]` into `m` steps of
length `t/m ≤ 1/m`). -/
theorem abs_sub_zero_le_mul_modulus (f : C(unitInterval, ℝ)) (t : unitInterval) {m : ℕ}
    (hm : 0 < m) : |f t - f 0| ≤ m * modulus f (1 / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  let p : ℕ → unitInterval := fun i => ⟨min 1 ((i : ℝ) / m) * t,
    unitInterval.mul_mem ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩ t.2⟩
  have hp0 : p 0 = 0 := by
    apply Subtype.ext
    simp only [p, Nat.cast_zero, zero_div, min_eq_right zero_le_one, zero_mul]
    rfl
  have hpm : p m = t := by
    apply Subtype.ext
    simp only [p, div_self hm'.ne', min_self, one_mul]
  have hstep : ∀ i < m, dist (p (i + 1)) (p i) ≤ 1 / m := by
    intro i hi
    have hi' : ((i + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hi
    have h1 : (i : ℝ) / m ≤ 1 := (div_le_one hm').mpr (by push_cast at hi'; linarith)
    have h2 : ((i + 1 : ℕ) : ℝ) / m ≤ 1 := (div_le_one hm').mpr hi'
    rw [Subtype.dist_eq, Real.dist_eq]
    simp only [p, min_eq_right h1, min_eq_right h2]
    have e : ((i + 1 : ℕ) : ℝ) / m * t - (i : ℝ) / m * t = (1 / m) * t := by
      push_cast
      field_simp
      ring
    rw [e, abs_of_nonneg (by positivity [t.2.1])]
    calc (1 / m : ℝ) * t ≤ 1 / m * 1 := mul_le_mul_of_nonneg_left t.2.2 (by positivity)
      _ = 1 / m := mul_one _
  calc |f t - f 0| = |∑ i ∈ Finset.range m, (f (p (i + 1)) - f (p i))| := by
        rw [Finset.sum_range_sub (fun i => f (p i)), hpm, hp0]
    _ ≤ ∑ i ∈ Finset.range m, |f (p (i + 1)) - f (p i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range m, modulus f (1 / m) :=
        Finset.sum_le_sum fun i hi => abs_sub_le_modulus f (hstep i (Finset.mem_range.mp hi))
    _ = m * modulus f (1 / m) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The Arzelà–Ascoli set `{f | |f 0| ≤ a ∧ ∀ j, w(f, δ j) ≤ ε j}` (Billingsley, Thm 7.2). -/
def arzelaAscoliSet (a : ℝ) (δ ε : ℕ → ℝ) : Set C(unitInterval, ℝ) :=
  {f | |f 0| ≤ a ∧ ∀ j, modulus f (δ j) ≤ ε j}

/-- The Arzelà–Ascoli set is closed. -/
theorem isClosed_arzelaAscoliSet (a : ℝ) (δ ε : ℕ → ℝ) :
    IsClosed (arzelaAscoliSet a δ ε) := by
  have e : arzelaAscoliSet a δ ε =
      {f : C(unitInterval, ℝ) | |f 0| ≤ a} ∩ ⋂ j, {f | modulus f (δ j) ≤ ε j} := by
    ext f
    simp only [arzelaAscoliSet, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [e]
  exact (isClosed_le (continuous_abs.comp (continuous_eval_const 0)) continuous_const).inter
    (isClosed_iInter fun j => isClosed_le (continuous_modulus (δ j)) continuous_const)

/-- Every path in the Arzelà–Ascoli set is bounded by `a + (m+1) ε 0` whenever
`1/(m+1) ≤ δ 0`. -/
theorem abs_le_of_mem_arzelaAscoliSet {a : ℝ} {δ ε : ℕ → ℝ} {m : ℕ}
    (hm : 1 / ((m : ℝ) + 1) ≤ δ 0) {f : C(unitInterval, ℝ)} (hf : f ∈ arzelaAscoliSet a δ ε)
    (x : unitInterval) : |f x| ≤ a + (m + 1) * ε 0 := by
  have h1 := abs_sub_zero_le_mul_modulus f x (m := m + 1) (Nat.succ_pos m)
  push_cast at h1
  have h2 : modulus f (1 / ((m : ℝ) + 1)) ≤ ε 0 := (modulus_mono f hm).trans (hf.2 0)
  have h3 : ((m : ℝ) + 1) * modulus f (1 / ((m : ℝ) + 1)) ≤ (m + 1) * ε 0 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : |f x| ≤ |f 0| + |f x - f 0| := by
    have := abs_add_le (f 0) (f x - f 0)
    rwa [add_sub_cancel] at this
  linarith [hf.1]

/-- **Arzelà–Ascoli** (Billingsley, Thm 7.2, sufficiency): if `δ j > 0` and `ε j → 0`, the set
`{f | |f 0| ≤ a ∧ ∀ j, w(f, δ j) ≤ ε j}` is compact in `C([0,1], ℝ)`. -/
theorem isCompact_arzelaAscoliSet (a : ℝ) {δ ε : ℕ → ℝ} (hδ : ∀ j, 0 < δ j)
    (hε : Tendsto ε atTop (𝓝 0)) : IsCompact (arzelaAscoliSet a δ ε) := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (hδ 0)
  set K := arzelaAscoliSet a δ ε
  set R := a + (m + 1) * ε 0
  let e := (ContinuousMap.isometryEquivBoundedOfCompact unitInterval ℝ).toHomeomorph
  have hA : IsCompact (e '' K) := by
    refine BoundedContinuousFunction.arzela_ascoli₂ (Metric.closedBall (0 : ℝ) R)
      (isCompact_closedBall 0 R) (e '' K) ?_ ?_ ?_
    · exact e.isClosed_image.mpr (isClosed_arzelaAscoliSet a δ ε)
    · rintro _ x ⟨f, hf, rfl⟩
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact abs_le_of_mem_arzelaAscoliSet hm.le hf x
    · refine (Metric.uniformEquicontinuous_iff.mpr fun ε' hε' => ?_).equicontinuous
      obtain ⟨j, hj⟩ := (hε.eventually (gt_mem_nhds hε')).exists
      refine ⟨δ j, hδ j, ?_⟩
      rintro x y hxy ⟨_, f, hf, rfl⟩
      change dist (f x) (f y) < ε'
      rw [Real.dist_eq]
      exact ((abs_sub_le_modulus f hxy.le).trans (hf.2 j)).trans_lt hj
  have := hA.image e.symm.continuous
  rwa [Set.image_image, show (fun f => e.symm (e f)) = id from funext e.symm_apply_apply,
    Set.image_id] at this

/-- A single finite measure on the path space satisfies `μ {w(·, δ) ≥ ε} → 0` as `δ → 0`: for
`ε, η > 0` some `δ > 0` has `μ {f | ε ≤ w(f, δ)} ≤ η`. -/
theorem exists_delta_measure_modulus_le [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] (μ : Measure C(unitInterval, ℝ)) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ > 0, μ {f | ε ≤ modulus f δ} ≤ η := by
  let A : ℕ → Set C(unitInterval, ℝ) := fun m => {f | ε ≤ modulus f (1 / ((m : ℝ) + 1))}
  have hA : Antitone A := by
    intro m m' hmm' f hf
    refine hf.trans (modulus_mono f ?_)
    have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hAm : ∀ m, MeasurableSet (A m) := fun m =>
    measurableSet_le measurable_const (measurable_modulus _)
  have hInter : (⋂ m, A m) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun f hf => ?_
    obtain ⟨δ, hδ, hlt⟩ := exists_modulus_lt f hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    have := mem_iInter.mp hf m
    exact absurd ((this.trans (modulus_mono f hm.le)).trans_lt hlt) (lt_irrefl ε)
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun m => (hAm m).nullMeasurableSet) hA
    ⟨0, measure_ne_top μ _⟩
  rw [hInter, measure_empty] at ht
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds hη)).exists
  exact ⟨1 / ((m : ℝ) + 1), by positivity, hm.le⟩

/-- Finitely many finite measures: for `ε, η > 0` and any `δ₀ > 0` there is `δ ∈ (0, δ₀]` with
`μ n {f | ε ≤ w(f, δ)} ≤ η` for all `n < N`. -/
theorem exists_delta_measure_modulus_le_of_lt [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] (μ : ℕ → Measure C(unitInterval, ℝ))
    [∀ n, IsFiniteMeasure (μ n)] {ε : ℝ} (hε : 0 < ε) {η : ℝ≥0∞} (hη : 0 < η) {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) (N : ℕ) :
    ∃ δ > 0, δ ≤ δ₀ ∧ ∀ n < N, μ n {f | ε ≤ modulus f δ} ≤ η := by
  induction N with
  | zero => exact ⟨δ₀, hδ₀, le_rfl, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ N ih =>
    obtain ⟨δ₁, hδ₁, hδ₁₀, h₁⟩ := ih
    obtain ⟨δ₂, hδ₂, h₂⟩ := exists_delta_measure_modulus_le (μ N) hε hη
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans hδ₁₀, fun n hn => ?_⟩
    have hsub : ∀ δ', min δ₁ δ₂ ≤ δ' → {f : C(unitInterval, ℝ) | ε ≤ modulus f (min δ₁ δ₂)} ⊆
        {f | ε ≤ modulus f δ'} := fun δ' h f hf => hf.trans (modulus_mono f h)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
    · exact (measure_mono (hsub δ₁ (min_le_left _ _))).trans (h₁ n hn)
    · exact (measure_mono (hsub δ₂ (min_le_right _ _))).trans h₂

/-- **Tightness criterion in `C([0,1], ℝ)`** (Billingsley, *Convergence of Probability
Measures*, Thm 7.3, sufficiency). A sequence of finite measures `μ n` on the path space is tight
if (i) the values at `0` are tight: for each `η > 0` some `a` has `μ n {|f 0| > a} ≤ η` for all
`n`; and (ii) for all `ε, η > 0` there are `δ > 0` and `N` with `μ n {w(f, δ) ≥ ε} ≤ η` for all
`n ≥ N` (that is, `lim_{δ→0} limsup_n μ n {w(·, δ) ≥ ε} = 0`). -/
theorem isTightMeasureSet_of_modulus [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {μ : ℕ → Measure C(unitInterval, ℝ)}
    [∀ n, IsFiniteMeasure (μ n)]
    (h0 : ∀ η : ℝ≥0∞, 0 < η → ∃ a : ℝ, ∀ n, μ n {f | a < |f 0|} ≤ η)
    (hw : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η →
      ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, μ n {f | ε ≤ modulus f δ} ≤ η) :
    IsTightMeasureSet (Set.range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro η hη
  set η' : ℝ≥0∞ := min η 1 with hη'
  have hη'0 : 0 < η' := lt_min hη one_pos
  have hη'top : η' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hhalf : 0 < η' / 2 := ENNReal.half_pos hη'0.ne'
  obtain ⟨e, he0, hesum⟩ := ENNReal.exists_pos_sum_of_countable hhalf.ne' ℕ
  obtain ⟨a, ha⟩ := h0 (η' / 2) hhalf
  have hε : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  have hstep : ∀ j : ℕ, ∃ δ > 0, ∀ n, μ n {f | 1 / ((j : ℝ) + 1) ≤ modulus f δ} ≤ e j := by
    intro j
    obtain ⟨δ₀, hδ₀, N, hN⟩ := hw _ (hε j) (e j) (ENNReal.coe_pos.mpr (he0 j))
    obtain ⟨δ, hδ, hδδ₀, hlt⟩ :=
      exists_delta_measure_modulus_le_of_lt μ (hε j) (ENNReal.coe_pos.mpr (he0 j)) hδ₀ N
    refine ⟨δ, hδ, fun n => ?_⟩
    rcases lt_or_ge n N with hn | hn
    · exact hlt n hn
    · exact (measure_mono fun f hf => hf.trans (modulus_mono f hδδ₀)).trans (hN n hn)
  choose δ hδ hδμ using hstep
  have hεlim : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨arzelaAscoliSet a δ (fun j => 1 / ((j : ℝ) + 1)),
    isCompact_arzelaAscoliSet a hδ hεlim, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hsub : (arzelaAscoliSet a δ (fun j => 1 / ((j : ℝ) + 1)))ᶜ ⊆
      {f | a < |f 0|} ∪ ⋃ j : ℕ, {f | 1 / ((j : ℝ) + 1) ≤ modulus f (δ j)} := by
    intro f hf
    simp only [arzelaAscoliSet, mem_compl_iff, mem_ofPred_eq, not_and_or, not_le,
      not_forall] at hf
    rcases hf with hf | ⟨j, hj⟩
    · exact Or.inl hf
    · exact Or.inr (mem_iUnion.mpr ⟨j, hj.le⟩)
  calc μ n (arzelaAscoliSet a δ (fun j => 1 / ((j : ℝ) + 1)))ᶜ
      ≤ μ n ({f | a < |f 0|} ∪ ⋃ j : ℕ, {f | 1 / ((j : ℝ) + 1) ≤ modulus f (δ j)}) :=
        measure_mono hsub
    _ ≤ μ n {f | a < |f 0|} + ∑' j : ℕ, μ n {f | 1 / ((j : ℝ) + 1) ≤ modulus f (δ j)} :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
    _ ≤ η' / 2 + ∑' j, (e j : ℝ≥0∞) :=
        add_le_add (ha n) (ENNReal.tsum_le_tsum fun j => hδμ j n)
    _ ≤ η' / 2 + η' / 2 := add_le_add le_rfl hesum.le
    _ = η' := ENNReal.add_halves η'
    _ ≤ η := min_le_left _ _

/-- Variant of `isTightMeasureSet_of_modulus` with condition (i) stated as tightness of the laws
of `f 0`. -/
theorem isTightMeasureSet_of_modulus' [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {μ : ℕ → Measure C(unitInterval, ℝ)}
    [∀ n, IsFiniteMeasure (μ n)]
    (h0 : IsTightMeasureSet (Set.range fun n => (μ n).map fun f : C(unitInterval, ℝ) => f 0))
    (hw : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η →
      ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, μ n {f | ε ≤ modulus f δ} ≤ η) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_of_modulus (fun η hη => ?_) hw
  obtain ⟨K, hK, hKμ⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp h0) η hη
  obtain ⟨a, ha⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨a, fun n => ?_⟩
  have hev : Measurable fun f : C(unitInterval, ℝ) => f 0 := (continuous_eval_const 0).measurable
  have hsub : {f : C(unitInterval, ℝ) | a < |f 0|} ⊆ (fun f : C(unitInterval, ℝ) => f 0) ⁻¹' Kᶜ :=
    by
    intro f hf hfK
    have := ha hfK
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact absurd hf (not_lt.mpr this)
  refine (measure_mono hsub).trans ?_
  rw [← Measure.map_apply hev hK.isClosed.measurableSet.compl]
  exact hKμ _ ⟨n, rfl⟩

/-- **Tightness criterion for random elements** `Xₙ : Ωₙ → C([0,1], ℝ)` (Billingsley, Thm 7.3):
the laws of `Xₙ` are tight if (i) `Qₙ {|Xₙ(0)| > a} ≤ η` for all `n`, for a suitable `a = a(η)`,
and (ii) for `ε, η > 0` there are `δ > 0` and `N` with `Qₙ {w(Xₙ, δ) ≥ ε} ≤ η` for `n ≥ N`. -/
theorem isTightMeasureSet_map_of_modulus [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {Q : ∀ n, Measure (Ω n)} [∀ n, IsFiniteMeasure (Q n)] {X : ∀ n, Ω n → C(unitInterval, ℝ)}
    (hX : ∀ n, AEMeasurable (X n) (Q n))
    (h0 : ∀ η : ℝ≥0∞, 0 < η → ∃ a : ℝ, ∀ n, Q n {ω | a < |X n ω 0|} ≤ η)
    (hw : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η →
      ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, Q n {ω | ε ≤ modulus (X n ω) δ} ≤ η) :
    IsTightMeasureSet (Set.range fun n => (Q n).map (X n)) := by
  refine isTightMeasureSet_of_modulus (fun η hη => ?_) (fun ε hε η hη => ?_)
  · obtain ⟨a, ha⟩ := h0 η hη
    refine ⟨a, fun n => ?_⟩
    have hm : MeasurableSet {f : C(unitInterval, ℝ) | a < |f 0|} :=
      measurableSet_lt measurable_const (continuous_abs.comp (continuous_eval_const 0)).measurable
    rw [Measure.map_apply_of_aemeasurable (hX n) hm]
    exact ha n
  · obtain ⟨δ, hδ, N, hN⟩ := hw ε hε η hη
    refine ⟨δ, hδ, N, fun n hn => ?_⟩
    have hm : MeasurableSet {f : C(unitInterval, ℝ) | ε ≤ modulus f δ} :=
      measurableSet_le measurable_const (measurable_modulus δ)
    rw [Measure.map_apply_of_aemeasurable (hX n) hm]
    exact hN n hn

/-- **Block bound** (Billingsley, *Convergence of Probability Measures*, Thm 7.4, deterministic
part). If `h > 0` and on every block `[i h, (i+1) h]` the path stays within `β` of its value at the
left end point, then `w(f, h) ≤ 3β`. -/
theorem modulus_le_three_mul_of_blocks (f : C(unitInterval, ℝ)) {h β : ℝ} (hh : 0 < h)
    (hb : ∀ (i : ℕ) (s u : unitInterval), (i : ℝ) * h ≤ s → (s : ℝ) ≤ (i + 1) * h →
      (u : ℝ) = i * h → |f s - f u| ≤ β) :
    modulus f h ≤ 3 * β := by
  have hβ : 0 ≤ β := by
    have h00 : ((0 : unitInterval) : ℝ) = ((0 : ℕ) : ℝ) * h := by
      rw [Set.Icc.coe_zero, Nat.cast_zero, zero_mul]
    have h01 : ((0 : unitInterval) : ℝ) ≤ ((0 : ℕ) + 1) * h := by
      rw [Set.Icc.coe_zero, Nat.cast_zero, zero_add, one_mul]
      exact hh.le
    have := hb 0 0 0 h00.ge h01 h00
    rwa [sub_self, abs_zero] at this
  have key : ∀ s u : unitInterval, (s : ℝ) ≤ u → (u : ℝ) - s ≤ h → |f s - f u| ≤ 3 * β := by
    intro s u hsu hus
    set i := ⌊(s : ℝ) / h⌋₊
    have hi1 : (i : ℝ) * h ≤ s := (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg s.2.1 hh.le))
    have hi2 : (s : ℝ) < (i + 1) * h := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one _)
    let L : unitInterval := ⟨(i : ℝ) * h, by positivity, hi1.trans s.2.2⟩
    have hsL := hb i s L hi1 hi2.le rfl
    by_cases hu : (u : ℝ) ≤ (i + 1) * h
    · have huL := hb i u L (hi1.trans hsu) hu rfl
      calc |f s - f u| ≤ |f s - f L| + |f L - f u| := abs_sub_le _ _ _
        _ = |f s - f L| + |f u - f L| := by rw [abs_sub_comm (f L)]
        _ ≤ 3 * β := by linarith
    · push Not at hu
      let R : unitInterval := ⟨((i : ℝ) + 1) * h, by positivity, hu.le.trans u.2.2⟩
      have hRL := hb i R L (by change (i : ℝ) * h ≤ (i + 1) * h; nlinarith) le_rfl rfl
      have huR := hb (i + 1) u R (by push_cast; exact hu.le)
        (by push_cast; nlinarith) (by push_cast; rfl)
      calc |f s - f u| ≤ |f s - f L| + |f L - f u| := abs_sub_le _ _ _
        _ ≤ |f s - f L| + (|f L - f R| + |f R - f u|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
        _ = |f s - f L| + (|f R - f L| + |f u - f R|) := by
          rw [abs_sub_comm (f L), abs_sub_comm (f R) (f u)]
        _ ≤ 3 * β := by linarith
  refine modulus_le f (by linarith) fun s u hsu => ?_
  rw [Subtype.dist_eq, Real.dist_eq, abs_le] at hsu
  rcases le_total (s : ℝ) u with h1 | h1
  · exact key s u h1 (by linarith [hsu.1])
  · rw [abs_sub_comm]
    exact key u s h1 (by linarith [hsu.2])

/-- On an index block `[iL, (i+1)L]` the polygonal path stays within `β` of `s (iL)` when the
increments `s (iL + l) − s (iL)`, `l ≤ L`, are bounded by `β`. -/
theorem abs_polygonal_sub_block_le {n L i : ℕ} {s : ℕ → ℝ} {β : ℝ}
    (hβ : ∀ l ≤ L, |s (i * L + l) - s (i * L)| ≤ β) {t : unitInterval}
    (h1 : ((i * L : ℕ) : ℝ) ≤ n * t) (h2 : (n : ℝ) * t ≤ ((i * L + L : ℕ) : ℝ)) :
    |polygonal n s t - s (i * L)| ≤ β := by
  have hx := natCast_mul_mem_Icc n t
  set q := i * L
  set m := ⌊(n : ℝ) * t⌋₊ with hm
  have hm1 : q ≤ m := Nat.le_floor h1
  have hm2 : m ≤ q + L := Nat.floor_le_of_le h2
  refine abs_polygonal_sub_le ?_ fun hlt => ?_
  · have := hβ (m - q) (by omega)
    rwa [Nat.add_sub_cancel' hm1] at this
  · have hm3 : m < q + L := by
      have : (m : ℝ) < ((q + L : ℕ) : ℝ) := hlt.trans_le h2
      exact_mod_cast this
    have := hβ (m + 1 - q) (by omega)
    rwa [show q + (m + 1 - q) = m + 1 by omega] at this

/-- Modulus of a polygonal path from its block increments: for `n, L ≥ 1`, if
`|s (iL + l) − s (iL)| ≤ β` for all `l ≤ L` and all blocks with `iL ≤ n`, then
`w(polygonal n s, L/n) ≤ 3β`. -/
theorem modulus_polygonal_le_of_blocks {n L : ℕ} (hn : 0 < n) {s : ℕ → ℝ} {β : ℝ}
    (hL : 0 < L) (hβ : ∀ i, i * L ≤ n → ∀ l ≤ L, |s (i * L + l) - s (i * L)| ≤ β) :
    modulus (polygonal n s) ((L : ℝ) / n) ≤ 3 * β := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  refine modulus_le_three_mul_of_blocks _ (by positivity) fun i t u h1 h2 hu => ?_
  have hiL' : (i : ℝ) * L ≤ n := by
    have hu1 : (i : ℝ) * (L / n) ≤ 1 := hu ▸ u.2.2
    rw [← mul_div_assoc, div_le_one hn'] at hu1
    exact hu1
  have hiL : i * L ≤ n := by exact_mod_cast hiL'
  have hPu : polygonal n s u = s (i * L) := polygonal_apply_of_mul_eq s u (by
    rw [hu]
    push_cast
    field_simp)
  rw [hPu]
  refine abs_polygonal_sub_block_le (hβ i hiL) ?_ ?_
  · push_cast
    have := mul_le_mul_of_nonneg_left h1 hn'.le
    rwa [show (n : ℝ) * (i * (L / n)) = i * L by field_simp] at this
  · push_cast
    have := mul_le_mul_of_nonneg_left h2 hn'.le
    rwa [show (n : ℝ) * ((i + 1) * (L / n)) = i * L + L by field_simp] at this

/-- Probability bound for the modulus of the normalised polygonal partial-sum process (Billingsley,
Thm 7.4 and (7.12)): with `L = n / m + 1` and `3c < ε`,
`Q {w(Xₙ, 1/m) ≥ ε} ≤ η` as soon as `m · Q {max_{i ≤ L} |S (j+i) − S j| ≥ c √n} ≤ η` for every
`j`, where `Xₙ = polygonal n (n^{-1/2} S)`. -/
theorem measure_modulus_polygonal_le {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (S : ℕ → Ω → ℝ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {ε c : ℝ} (hc : 3 * c < ε)
    {η : ℝ≥0∞}
    (hblock : ∀ j : ℕ, (m : ℝ≥0∞) *
      Q {ω | ∃ i ≤ n / m + 1, c * √(n : ℝ) ≤ |S (j + i) ω - S j ω|} ≤ η) :
    Q {ω | ε ≤ modulus (polygonal n (fun k => (√(n : ℝ))⁻¹ * S k ω)) (1 / m)} ≤ η := by
  set L := n / m + 1 with hLdef
  have hL : 0 < L := Nat.succ_pos _
  have hnL : n < m * L := Nat.lt_mul_div_succ n hm
  have hcount : n / L + 1 ≤ m := Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul hL).mpr hnL)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
  have hδ : (1 : ℝ) / m ≤ (L : ℝ) / n := by
    rw [div_le_div_iff₀ hm' hn', one_mul, mul_comm]
    exact_mod_cast hnL.le
  set E : ℕ → Set Ω := fun j => {ω | ∃ i ≤ L, c * √(n : ℝ) ≤ |S (j + i) ω - S j ω|}
  have hsub : {ω | ε ≤ modulus (polygonal n (fun k => (√(n : ℝ))⁻¹ * S k ω)) (1 / m)} ⊆
      ⋃ i ∈ Finset.range (n / L + 1), E (i * L) := by
    intro ω hω
    by_contra hnot
    simp only [mem_iUnion, Finset.mem_range, exists_prop, not_exists, not_and] at hnot
    have hb : ∀ i, i * L ≤ n → ∀ l ≤ L, |(√(n : ℝ))⁻¹ * S (i * L + l) ω -
        (√(n : ℝ))⁻¹ * S (i * L) ω| ≤ c := by
      intro i hi l hl
      have hi' : i < n / L + 1 := Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hL).mpr hi)
      have hnot' := hnot i hi'
      simp only [E, mem_ofPred_eq, not_exists, not_and, not_le] at hnot'
      have hlt := hnot' l hl
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hsqrt), inv_mul_le_iff₀ hsqrt]
      linarith
    have hmod := modulus_polygonal_le_of_blocks (s := fun k => (√(n : ℝ))⁻¹ * S k ω) hn hL hb
    have := (modulus_mono _ hδ).trans hmod
    exact absurd (hω.trans this) (by linarith)
  have hsum : (m : ℝ≥0∞) * ∑ i ∈ Finset.range (n / L + 1), Q (E (i * L)) ≤ m * η := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.range (n / L + 1), (m : ℝ≥0∞) * Q (E (i * L))
        ≤ ∑ _i ∈ Finset.range (n / L + 1), η := Finset.sum_le_sum fun i _ => hblock (i * L)
      _ = (n / L + 1 : ℕ) * η := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ m * η := by
          gcongr
  have hsum' : ∑ i ∈ Finset.range (n / L + 1), Q (E (i * L)) ≤ η :=
    (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hm.ne') (ENNReal.natCast_ne_top m)).mp hsum
  exact (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans hsum')

/-- **Sufficient condition for (ii) for partial-sum processes** (Billingsley, Thm 7.4 / (8.12)
type, non-stationary form). Let `S : ℕ → Ω → ℝ` under `Q`. Suppose that for all `ε, η > 0` there
are `m ≥ 1` (that is, `δ = 1/m`) and `N` such that for all `n ≥ N` and all `j`,
`m · Q {∃ i ≤ n/m + 1, |S (j+i) − S j| ≥ ε √n} ≤ η` (that is,
`lim_{δ→0} limsup_n sup_j δ⁻¹ Q (max_{i ≤ nδ} |S_{j+i} − S_j| ≥ ε √n) = 0`). Then the normalised
polygonal processes `Xₙ = polygonal n (n^{-1/2} S)` satisfy condition (ii) of the tightness
criterion `isTightMeasureSet_map_of_modulus`. -/
theorem modulus_condition_polygonal_of_blocks {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (S : ℕ → Ω → ℝ)
    (hS : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ m : ℕ, 0 < m ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ j : ℕ,
      (m : ℝ≥0∞) * Q {ω | ∃ i ≤ n / m + 1, ε * √(n : ℝ) ≤ |S (j + i) ω - S j ω|} ≤ η) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
      Q {ω | ε ≤ modulus (polygonal n (fun k => (√(n : ℝ))⁻¹ * S k ω)) δ} ≤ η := by
  intro ε hε η hη
  obtain ⟨m, hm, N, hN⟩ := hS (ε / 4) (by positivity) η hη
  refine ⟨1 / m, by positivity, max N 1, fun n hn => ?_⟩
  exact measure_modulus_polygonal_le Q S (by omega) hm (by linarith)
    (hN n ((le_max_left _ _).trans hn))

/-- **Tightness of normalised polygonal partial-sum processes.** If `S 0 = 0`, each `S k` is
measurable and the block condition of `modulus_condition_polygonal_of_blocks` holds, then the laws
of `Xₙ = polygonal n (n^{-1/2} S)` on `C([0,1], ℝ)` are tight. -/
theorem isTightMeasureSet_polygonal_of_blocks [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsFiniteMeasure Q] {S : ℕ → Ω → ℝ} (hSm : ∀ k, Measurable (S k)) (hS0 : ∀ ω, S 0 ω = 0)
    (hS : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ m : ℕ, 0 < m ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ j : ℕ,
      (m : ℝ≥0∞) * Q {ω | ∃ i ≤ n / m + 1, ε * √(n : ℝ) ≤ |S (j + i) ω - S j ω|} ≤ η) :
    IsTightMeasureSet (Set.range fun n : ℕ =>
      Q.map fun ω => polygonal n (fun k => (√(n : ℝ))⁻¹ * S k ω)) := by
  refine isTightMeasureSet_map_of_modulus (Ω := fun _ => Ω) (Q := fun _ => Q)
    (X := fun n ω => polygonal n (fun k => (√(n : ℝ))⁻¹ * S k ω))
    (fun n => (measurable_polygonal_comp (fun k => (hSm k).const_mul _) n).aemeasurable)
    (fun η _ => ⟨0, fun n => ?_⟩) (modulus_condition_polygonal_of_blocks Q S hS)
  have he : {ω : Ω | (0 : ℝ) < |polygonal n (fun k => (√(n : ℝ))⁻¹ * S k ω) 0|} = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun ω hω => ?_
    rw [mem_ofPred_eq, polygonal_zero_point, hS0, mul_zero, abs_zero] at hω
    exact lt_irrefl _ hω
  change Q {ω : Ω | (0 : ℝ) < |polygonal n (fun k => (√(n : ℝ))⁻¹ * S k ω) 0|} ≤ η
  rw [he, measure_empty]
  exact zero_le

end MeynTweedie.LimitTheorems

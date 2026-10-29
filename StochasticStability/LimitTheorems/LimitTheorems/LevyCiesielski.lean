/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The Lévy–Ciesielski construction of Brownian motion (background for MT §17.4, App. D.6)

Meyn and Tweedie use standard Brownian motion on `[0,1]` (MT, App. D.6.2, p. 563) as the limit in
the functional CLT (Theorem D.6.4, Theorem 17.4.4) but do not construct it. Mathlib has the
predicates `IsPreBrownianReal`/`IsBrownianReal` but no existence theorem. This module builds the
process from an i.i.d. Gaussian sequence by the Schauder series
`B(t) = Σ_m ξ_m S_m(t)`; `BrownianMotion.lean` derives its laws and Wiener measure.

**Schauder functions.** `lcTent a h` is the tent on `[a, a+h]`; `schauderLevel n k` is `2^{n/2}`
times the tent on `[k 2^{-n}, (k+1) 2^{-n}]`; `schauder 0 = id` and
`schauder (2ⁿ + k) = schauderLevel n k` (`schauder_two_pow_add`), so the indices `m < 2^N` are
exactly the levels `< N`.

**Covariance identity (Parseval for the Haar basis).**
* `lcBridgeTerm_split`: on one dyadic interval, the Brownian-bridge covariance splits into the two
  half-interval bridge covariances plus the product of the tents.
* `schauder_sum_mul`: `Σ_{m<2^N} S_m(s) S_m(t) = min s t − lcBridge N s t` on `[0,1]`.
* `lcBridge_le`, `tendsto_schauder_sum_mul`: `0 ≤ lcBridge N s t ≤ 2^{-N}`, hence
  `Σ_m S_m(s) S_m(t) = min s t`.

**Gaussian sums.**
* `gaussSeq`: the product of standard Gaussians on `ℕ → ℝ`.
* `gaussSeq_map_sum`: `Σ_{m<M} a_m ξ_m` has law `N(0, Σ_{m<M} a_m²)`.
* `map_eq_gaussianReal_of_tendsto`: an a.s. limit of `N(0, vₙ)` variables with `vₙ → w` is
  `N(0, w)`.

**Uniform convergence.**
* `norm_lcPartial_succ_sub_le`: the sup norm of level block `N` is at most `lcWeight N ω`, with
  `c = (6/5)^N` and `lcWeight N ω = (5/7)^N/2 · (c + Σ_k ξ_{N,k}⁴/c³)` (from `|x| ≤ c + x⁴/c³`).
* `summable_integral_lcWeight`, `ae_mem_lcGood`: the expected weights are summable, so a.s. the
  weights are summable (`lcGood`, a measurable set of full measure).
* `levyPath`: the uniform limit of the partial sums on `lcGood` (and `0` off it), a continuous
  path for every `ω`; `tendsto_lcPartial_levyPath`, `tendsto_lcPartial_apply`, `levyPath_zero`.

This replaces the Kolmogorov–Chentsov route. The Gaussian tail bound is not needed: a fourth
moment bound (`gaussFourth`) and the first Borel–Cantelli argument in expectation suffice.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped ENNReal NNReal

/-- The tent function on `[a, a + h]`: zero outside, slope `±1`, peak `h/2` at the midpoint. -/
def lcTent (a h x : ℝ) : ℝ := max 0 (min (x - a) (a + h - x))

/-- The tent function is nonnegative. -/
lemma lcTent_nonneg (a h x : ℝ) : 0 ≤ lcTent a h x := le_max_left _ _

/-- The tent function on an interval of length `h ≥ 0` is at most `h/2`. -/
lemma lcTent_le (a h x : ℝ) (hh : 0 ≤ h) : lcTent a h x ≤ h / 2 := by
  unfold lcTent
  refine max_le (by linarith) ?_
  rcases le_total (x - a) (a + h - x) with hc | hc
  · rw [min_eq_left hc]; linarith
  · rw [min_eq_right hc]; linarith

/-- The tent function vanishes left of its interval. -/
lemma lcTent_of_le {a h x : ℝ} (hx : x ≤ a) : lcTent a h x = 0 := by
  unfold lcTent
  exact max_eq_left (min_le_of_left_le (by linarith))

/-- The tent function vanishes right of its interval. -/
lemma lcTent_of_ge {a h x : ℝ} (hx : a + h ≤ x) : lcTent a h x = 0 := by
  unfold lcTent
  exact max_eq_left (min_le_of_right_le (by linarith))

/-- On the left half of its interval the tent function is `x - a`. -/
lemma lcTent_of_left {a h x : ℝ} (h1 : a ≤ x) (h2 : x ≤ a + h / 2) : lcTent a h x = x - a := by
  unfold lcTent
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

/-- On the right half of its interval the tent function is `a + h - x`. -/
lemma lcTent_of_right {a h x : ℝ} (h1 : a + h / 2 ≤ x) (h2 : x ≤ a + h) :
    lcTent a h x = a + h - x := by
  unfold lcTent
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- Where the tent function is nonzero, `x` lies in the open interval. -/
lemma lcTent_mem_of_ne_zero {a h x : ℝ} (hx : lcTent a h x ≠ 0) : a < x ∧ x < a + h := by
  constructor
  · by_contra hc; exact hx (lcTent_of_le (not_lt.1 hc))
  · by_contra hc; exact hx (lcTent_of_ge (not_lt.1 hc))

/-- The tent function is continuous. -/
lemma continuous_lcTent (a h : ℝ) : Continuous (lcTent a h) := by
  unfold lcTent; fun_prop

/-- One term of the dyadic Brownian-bridge covariance: for `u ≤ v` it is the covariance of the
Brownian bridge on `[a, a + h]` at the times `u, v` (and zero unless both lie in the interval). -/
noncomputable def lcBridgeTerm (a h u v : ℝ) : ℝ := max 0 (u - a) * max 0 (a + h - v) / h

/-- The bridge term is nonnegative. -/
lemma lcBridgeTerm_nonneg (a h u v : ℝ) (hh : 0 ≤ h) : 0 ≤ lcBridgeTerm a h u v := by
  unfold lcBridgeTerm
  exact div_nonneg (mul_nonneg (le_max_left _ _) (le_max_left _ _)) hh

/-- The bridge covariance on `[a, a + h]` splits into the two bridge covariances on the halves
plus the product of the tent functions: the dyadic refinement step. -/
lemma lcBridgeTerm_split {a h u v : ℝ} (hh : 0 < h) (huv : u ≤ v) :
    lcBridgeTerm a h u v - lcBridgeTerm a (h / 2) u v - lcBridgeTerm (a + h / 2) (h / 2) u v
      = lcTent a h u * lcTent a h v / h := by
  unfold lcBridgeTerm
  rcases le_total u a with hu | hu
  · rw [max_eq_left (by linarith : u - a ≤ 0), max_eq_left (by linarith : u - (a + h / 2) ≤ 0),
      lcTent_of_le hu]
    ring
  rcases le_total (a + h) v with hv | hv
  · rw [max_eq_left (by linarith : a + h - v ≤ 0), max_eq_left (by linarith : a + h / 2 - v ≤ 0),
      max_eq_left (by linarith : a + h / 2 + h / 2 - v ≤ 0), lcTent_of_ge hv]
    ring
  rcases le_total v (a + h / 2) with hv2 | hv2
  · rw [max_eq_right (by linarith : 0 ≤ u - a), max_eq_left (by linarith : u - (a + h / 2) ≤ 0),
      max_eq_right (by linarith : 0 ≤ a + h - v), max_eq_right (by linarith : 0 ≤ a + h / 2 - v),
      lcTent_of_left hu (by linarith), lcTent_of_left (by linarith) hv2]
    field_simp
    ring
  rcases le_total u (a + h / 2) with hu2 | hu2
  · rw [max_eq_right (by linarith : 0 ≤ u - a), max_eq_left (by linarith : u - (a + h / 2) ≤ 0),
      max_eq_right (by linarith : 0 ≤ a + h - v), max_eq_left (by linarith : a + h / 2 - v ≤ 0),
      lcTent_of_left hu hu2, lcTent_of_right hv2 hv]
    field_simp
    ring
  · rw [max_eq_right (by linarith : 0 ≤ u - a), max_eq_right (by linarith : 0 ≤ u - (a + h / 2)),
      max_eq_right (by linarith : 0 ≤ a + h - v), max_eq_left (by linarith : a + h / 2 - v ≤ 0),
      max_eq_right (by linarith : 0 ≤ a + h / 2 + h / 2 - v),
      lcTent_of_right hu2 (by linarith), lcTent_of_right hv2 hv]
    field_simp
    ring

/-- A sum of terms bounded by `B ≥ 0`, at most one of which is nonzero, is at most `B`. -/
lemma lc_sum_le_of_atMostOne {ι : Type*} (s : Finset ι) (f : ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, f i ≤ B) (huniq : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 → i = j) :
    ∑ i ∈ s, f i ≤ B := by
  by_cases h : ∃ i ∈ s, f i ≠ 0
  · obtain ⟨i, hi, hfi⟩ := h
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => by
      by_contra hc; exact hji (huniq j hj i hi hc hfi))]
    exact hf i hi
  · push Not at h
    rw [Finset.sum_eq_zero h]
    exact hB

/-- Splitting a sum over `range (2n)` into even and odd terms. -/
lemma lc_sum_range_two_mul (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (2 * n), f k = ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- Two dyadic intervals `(k h, (k+1) h)` containing ordered points `u ≤ v` coincide. -/
lemma lc_dyadic_unique {h u v : ℝ} (hh : 0 < h) (huv : u ≤ v) {i j : ℕ}
    (hi1 : (i : ℝ) * h < u) (hi2 : v < (i : ℝ) * h + h)
    (hj1 : (j : ℝ) * h < u) (hj2 : v < (j : ℝ) * h + h) : i = j := by
  have h1 : (i : ℝ) < j + 1 := by
    by_contra hc; push Not at hc; nlinarith
  have h2 : (j : ℝ) < i + 1 := by
    by_contra hc; push Not at hc; nlinarith
  have h1' : i < j + 1 := by exact_mod_cast h1
  have h2' : j < i + 1 := by exact_mod_cast h2
  omega

/-- The Schauder function of level `n` and position `k < 2ⁿ`: `2^{n/2}` times the tent on the
dyadic interval `[k/2ⁿ, (k+1)/2ⁿ]`; its peak is `2^{-n/2}/2`. -/
noncomputable def schauderLevel (n k : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (2 ^ n) * lcTent (k / 2 ^ n) (1 / 2 ^ n) x

/-- The Schauder functions in one sequence: `schauder 0 x = x`, and for `m = 2ⁿ + k` with
`k < 2ⁿ`, `schauder m = schauderLevel n k`. -/
noncomputable def schauder (m : ℕ) (x : ℝ) : ℝ :=
  if m = 0 then x else schauderLevel (Nat.log 2 m) (m - 2 ^ Nat.log 2 m) x

/-- The zeroth Schauder function is the identity, `schauder 0 x = x`. -/
lemma schauder_zero_apply (x : ℝ) : schauder 0 x = x := by simp [schauder]

/-- Re-indexing: `schauder (2^N + k) = schauderLevel N k` for `k < 2^N`. -/
lemma schauder_two_pow_add {N k : ℕ} (hk : k < 2 ^ N) :
    schauder (2 ^ N + k) = schauderLevel N k := by
  have hlog : Nat.log 2 (2 ^ N + k) = N :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [pow_succ]; omega)
  funext x
  have hne : 2 ^ N + k ≠ 0 := by positivity
  simp only [schauder, hne, ite_false, hlog, Nat.add_sub_cancel_left]

/-- The Schauder functions of positive level are nonnegative. -/
lemma schauderLevel_nonneg (n k : ℕ) (x : ℝ) : 0 ≤ schauderLevel n k x :=
  mul_nonneg (Real.sqrt_nonneg _) (lcTent_nonneg _ _ _)

/-- Every Schauder function is continuous. -/
lemma continuous_schauder (m : ℕ) : Continuous (schauder m) := by
  unfold schauder
  split_ifs
  · exact continuous_id
  · unfold schauderLevel
    exact continuous_const.mul (continuous_lcTent _ _)

/-- The level-`N` dyadic Brownian-bridge covariance. -/
noncomputable def lcBridge (N : ℕ) (s t : ℝ) : ℝ :=
  ∑ k ∈ range (2 ^ N), lcBridgeTerm (k / 2 ^ N) (1 / 2 ^ N) (min s t) (max s t)

/-- A product of two tent values only depends on the unordered pair of points. -/
lemma lcTent_mul_comm_minmax (a h s t : ℝ) :
    lcTent a h s * lcTent a h t = lcTent a h (min s t) * lcTent a h (max s t) := by
  rcases le_total s t with hst | hst
  · rw [min_eq_left hst, max_eq_right hst]
  · rw [min_eq_right hst, max_eq_left hst, mul_comm]

/-- One dyadic level of the Schauder product series is the drop of the bridge covariance. -/
lemma schauderLevel_sum_mul (N : ℕ) (s t : ℝ) :
    ∑ k ∈ range (2 ^ N), schauderLevel N k s * schauderLevel N k t
      = lcBridge N s t - lcBridge (N + 1) s t := by
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  unfold lcBridge
  rw [show 2 ^ (N + 1) = 2 * 2 ^ N by ring, lc_sum_range_two_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : ((2 * k : ℕ) : ℝ) / 2 ^ (N + 1) = k / 2 ^ N := by
    push_cast; rw [pow_succ]; field_simp
  have e2 : ((2 * k + 1 : ℕ) : ℝ) / 2 ^ (N + 1) = k / 2 ^ N + 1 / 2 ^ N / 2 := by
    push_cast; rw [pow_succ]; field_simp
  have e3 : (1 : ℝ) / 2 ^ (N + 1) = 1 / 2 ^ N / 2 := by rw [pow_succ]; field_simp
  rw [e1, e2, e3, sub_add_eq_sub_sub,
    lcBridgeTerm_split (by positivity) (min_le_max), ← lcTent_mul_comm_minmax]
  unfold schauderLevel
  have hs : Real.sqrt (2 ^ N) * Real.sqrt (2 ^ N) = 2 ^ N := Real.mul_self_sqrt h2.le
  field_simp
  linear_combination (lcTent (k / 2 ^ N) (1 / 2 ^ N) s * lcTent (k / 2 ^ N) (1 / 2 ^ N) t) * hs

/-- **Schauder product series, partial sums.** For `s, t ∈ [0,1]`, the sum of
`schauder m s * schauder m t` over `m < 2^N` (levels `< N`) equals `min s t` minus the level-`N`
bridge covariance. -/
theorem schauder_sum_mul (N : ℕ) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∑ m ∈ range (2 ^ N), schauder m s * schauder m t = min s t - lcBridge N s t := by
  induction N with
  | zero =>
    simp only [pow_zero, Finset.sum_range_one, schauder_zero_apply, lcBridge, Nat.cast_zero,
      div_one, lcBridgeTerm, zero_add, sub_zero]
    rw [max_eq_right (le_min hs.1 ht.1), max_eq_right (by
      have := max_le hs.2 ht.2; linarith)]
    have := min_mul_max s t
    linarith
  | succ N ih =>
    rw [show 2 ^ (N + 1) = 2 ^ N + 2 ^ N by ring, Finset.sum_range_add, ih]
    rw [Finset.sum_congr rfl (fun k hk => by
      rw [schauder_two_pow_add (Finset.mem_range.1 hk)]), schauderLevel_sum_mul]
    ring

/-- The bridge term on an interval of length `h > 0` is at most `h`. -/
lemma lcBridgeTerm_le {a h u v : ℝ} (hh : 0 < h) (huv : u ≤ v) : lcBridgeTerm a h u v ≤ h := by
  unfold lcBridgeTerm
  rcases le_total u a with hu | hu
  · rw [max_eq_left (by linarith : u - a ≤ 0)]; simp [hh.le]
  rcases le_total (a + h) v with hv | hv
  · rw [max_eq_left (by linarith : a + h - v ≤ 0)]; simp [hh.le]
  rw [max_eq_right (by linarith : 0 ≤ u - a), max_eq_right (by linarith : 0 ≤ a + h - v),
    div_le_iff₀ hh]
  nlinarith

/-- A nonzero bridge term forces `a < u` and `v < a + h`. -/
lemma lcBridgeTerm_mem_of_ne_zero {a h u v : ℝ} (hne : lcBridgeTerm a h u v ≠ 0) :
    a < u ∧ v < a + h := by
  unfold lcBridgeTerm at hne
  constructor
  · by_contra hc; push Not at hc
    exact hne (by rw [max_eq_left (by linarith : u - a ≤ 0)]; simp)
  · by_contra hc; push Not at hc
    exact hne (by rw [max_eq_left (by linarith : a + h - v ≤ 0)]; simp)

/-- The bridge covariance is nonnegative. -/
lemma lcBridge_nonneg (N : ℕ) (s t : ℝ) : 0 ≤ lcBridge N s t :=
  Finset.sum_nonneg fun _ _ => lcBridgeTerm_nonneg _ _ _ _ (by positivity)

/-- The level-`N` bridge covariance is at most `2^{-N}` (only one dyadic interval contributes). -/
lemma lcBridge_le (N : ℕ) (s t : ℝ) : lcBridge N s t ≤ 1 / 2 ^ N := by
  have hh : (0 : ℝ) < 1 / 2 ^ N := by positivity
  refine lc_sum_le_of_atMostOne _ _ hh.le (fun k _ => lcBridgeTerm_le hh min_le_max) ?_
  intro i _ j _ hi hj
  obtain ⟨hi1, hi2⟩ := lcBridgeTerm_mem_of_ne_zero hi
  obtain ⟨hj1, hj2⟩ := lcBridgeTerm_mem_of_ne_zero hj
  refine lc_dyadic_unique hh min_le_max (u := min s t) (v := max s t) ?_ ?_ ?_ ?_ <;>
    · rwa [mul_one_div]

/-- **Schauder product series** (Lévy–Ciesielski covariance identity): for `s, t ∈ [0,1]`,
`Σ_m schauder m s * schauder m t = min s t`, as the limit of the partial sums over complete
dyadic levels. -/
theorem tendsto_schauder_sum_mul {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun N => ∑ m ∈ range (2 ^ N), schauder m s * schauder m t) atTop
      (𝓝 (min s t)) := by
  simp_rw [schauder_sum_mul _ hs ht]
  have h0 : Tendsto (fun N : ℕ => (1 : ℝ) / 2 ^ N) atTop (𝓝 0) := by
    simp_rw [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb : Tendsto (fun N => lcBridge N s t) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun N => lcBridge_nonneg N s t) (fun N => lcBridge_le N s t)
  simpa using (tendsto_const_nhds (x := min s t)).sub hb

/-! ### The i.i.d. Gaussian sequence -/

/-- The law of an i.i.d. sequence of standard Gaussians: the product measure on `ℕ → ℝ`. -/
noncomputable def gaussSeq : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ => gaussianReal 0 1)

/-- `gaussSeq` is a probability measure. -/
lemma isProbabilityMeasure_gaussSeq : IsProbabilityMeasure gaussSeq := by
  unfold gaussSeq; infer_instance

/-- Each coordinate of the Gaussian sequence is standard Gaussian. -/
lemma hasLaw_gaussSeq_coord (j : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω j) (gaussianReal 0 1) gaussSeq :=
  (measurePreserving_eval_infinitePi (fun _ => gaussianReal 0 1) j).hasLaw

/-- The scaled coordinates `a m * ω m` are independent under `gaussSeq`. -/
lemma iIndepFun_gaussSeq_mul (a : ℕ → ℝ) :
    iIndepFun (fun m (ω : ℕ → ℝ) => a m * ω m) gaussSeq :=
  iIndepFun_infinitePi (P := fun _ => gaussianReal 0 1) (X := fun m (x : ℝ) => a m * x)
    (fun _ => measurable_const.mul measurable_id)

/-- **Finite Gaussian sums.** `Σ_{m<M} a m ξ_m` for i.i.d. standard Gaussians `ξ` is centred
Gaussian with variance `Σ_{m<M} (a m)²`. -/
theorem gaussSeq_map_sum (a : ℕ → ℝ) (M : ℕ) :
    gaussSeq.map (fun ω => ∑ m ∈ range M, a m * ω m)
      = gaussianReal 0 (∑ m ∈ range M, a m ^ 2).toNNReal := by
  have := isProbabilityMeasure_gaussSeq
  induction M with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Real.toNNReal_zero, gaussianReal_zero_var]
    rw [Measure.map_const, measure_univ, one_smul]
  | succ M ih =>
    have hfun : (fun ω : ℕ → ℝ => ∑ m ∈ range (M + 1), a m * ω m)
        = (fun ω => ∑ m ∈ range M, a m * ω m) + (fun ω => a M * ω M) := by
      funext ω; simp [Finset.sum_range_succ]
    have hind : IndepFun (fun ω : ℕ → ℝ => ∑ m ∈ range M, a m * ω m) (fun ω => a M * ω M)
        gaussSeq := by
      have h := (iIndepFun_gaussSeq_mul a).indepFun_finsetSum_of_notMem
        (fun m => measurable_const.mul (measurable_pi_apply m)) (s := range M) (i := M)
        (by simp)
      have he : (∑ j ∈ range M, fun ω : ℕ → ℝ => a j * ω j)
          = fun ω => ∑ m ∈ range M, a m * ω m := by
        funext ω; simp [Finset.sum_apply]
      rwa [he] at h
    have hX : HasLaw (fun ω : ℕ → ℝ => ∑ m ∈ range M, a m * ω m)
        (gaussianReal 0 (∑ m ∈ range M, a m ^ 2).toNNReal) gaussSeq :=
      ⟨(Finset.measurable_sum _ fun m _ =>
        measurable_const.mul (measurable_pi_apply m)).aemeasurable, ih⟩
    have hY := gaussianReal_const_mul (hasLaw_gaussSeq_coord M) (a M)
    rw [hfun, gaussianReal_add_gaussianReal_of_indepFun hind hX hY]
    congr 1
    · ring
    · rw [Finset.sum_range_succ, Real.toNNReal_add
        (Finset.sum_nonneg fun m _ => sq_nonneg (a m)) (sq_nonneg _)]
      ext
      simp [Real.coe_toNNReal _ (sq_nonneg (a M))]

/-- **Limits of centred Gaussians.** If `Xₙ → Y` almost surely, each `Xₙ` is centred Gaussian with
variance `vₙ`, and `vₙ → w`, then `Y` is centred Gaussian with variance `w` (by characteristic
functions and dominated convergence). -/
theorem map_eq_gaussianReal_of_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {v : ℕ → ℝ≥0} {w : ℝ≥0}
    (hX : ∀ n, AEMeasurable (X n) P) (hlaw : ∀ n, P.map (X n) = gaussianReal 0 (v n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hv : Tendsto v atTop (𝓝 w)) : P.map Y = gaussianReal 0 w := by
  have hY : AEMeasurable Y P := aemeasurable_of_tendsto_metrizable_ae' hX hlim
  refine Measure.ext_of_charFun (funext fun u => ?_)
  have hce : Continuous fun x : ℝ => Complex.exp (u * x * Complex.I) := by fun_prop
  have h1 : Tendsto (fun n => charFun (P.map (X n)) u) atTop (𝓝 (charFun (P.map Y) u)) := by
    simp_rw [charFun_apply_real]
    rw [integral_map hY (by fun_prop)]
    simp_rw [fun n => integral_map (hX n) (f := fun x : ℝ => Complex.exp (u * x * Complex.I))
      (by fun_prop)]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => ?_)
      (integrable_const _) (fun n => ?_) ?_
    · exact hce.comp_aestronglyMeasurable (hX n).aestronglyMeasurable
    · refine Eventually.of_forall fun ω => le_of_eq ?_
      rw [show (u : ℂ) * (X n ω : ℂ) * Complex.I = ((u * X n ω : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    · filter_upwards [hlim] with ω hω
      exact (hce.tendsto _).comp hω
  have h2 : Tendsto (fun n => charFun (P.map (X n)) u) atTop
      (𝓝 (charFun (gaussianReal 0 w) u)) := by
    simp_rw [hlaw, charFun_gaussianReal]
    have hc : Continuous fun r : ℝ => Complex.exp (u * 0 * Complex.I - r * u ^ 2 / 2) := by
      fun_prop
    exact (hc.tendsto _).comp (NNReal.continuous_coe.tendsto _ |>.comp hv)
  exact tendsto_nhds_unique h1 h2

/-! ### Uniform convergence of the series -/

/-- The Schauder functions as continuous functions on `[0,1]`. -/
noncomputable def schauderC (m : ℕ) : C(unitInterval, ℝ) :=
  ⟨fun t => schauder m t, (continuous_schauder m).comp continuous_subtype_val⟩

/-- The Lévy–Ciesielski partial sum over the dyadic levels `< N`:
`Σ_{m<2^N} ω m • schauderC m`. -/
noncomputable def lcPartial (N : ℕ) (ω : ℕ → ℝ) : C(unitInterval, ℝ) :=
  ∑ m ∈ range (2 ^ N), ω m • schauderC m

/-- Evaluation of a partial sum. -/
lemma lcPartial_apply (N : ℕ) (ω : ℕ → ℝ) (t : unitInterval) :
    lcPartial N ω t = ∑ m ∈ range (2 ^ N), ω m * schauder m t := by
  simp [lcPartial, schauderC]

/-- Each partial sum is continuous in the coefficient sequence (product topology). -/
lemma continuous_lcPartial (N : ℕ) : Continuous (lcPartial N) := by
  unfold lcPartial
  exact continuous_finsetSum _ fun m _ => (continuous_apply m).smul continuous_const

/-- The weight bounding the sup norm of the level-`n` block: with `c = (6/5)ⁿ`,
`(5/7)ⁿ/2 · (c + Σ_{k<2ⁿ} ξ_{n,k}⁴ / c³)`. -/
noncomputable def lcWeight (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (5 / 7 : ℝ) ^ n / 2 *
    ((6 / 5 : ℝ) ^ n + ∑ k ∈ range (2 ^ n), ω (2 ^ n + k) ^ 4 / ((6 / 5 : ℝ) ^ n) ^ 3)

/-- The block weights are nonnegative. -/
lemma lcWeight_nonneg (n : ℕ) (ω : ℕ → ℝ) : 0 ≤ lcWeight n ω := by
  unfold lcWeight
  have : 0 ≤ ∑ k ∈ range (2 ^ n), ω (2 ^ n + k) ^ 4 / ((6 / 5 : ℝ) ^ n) ^ 3 :=
    Finset.sum_nonneg fun k _ => by positivity
  positivity

/-- The block weights are measurable. -/
lemma measurable_lcWeight (n : ℕ) : Measurable (lcWeight n) := by
  unfold lcWeight
  refine measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun k _ => ?_))
  exact ((measurable_pi_apply _).pow_const 4).div_const _

/-- `|x| ≤ c + x⁴/c³` for `c > 0`. -/
lemma lc_abs_le_add_pow_four (x : ℝ) {c : ℝ} (hc : 0 < c) : |x| ≤ c + x ^ 4 / c ^ 3 := by
  have hc3 : 0 < c ^ 3 := by positivity
  rw [← Even.pow_abs (by decide : Even 4) x]
  set y := |x| with hy
  have hy0 : 0 ≤ y := abs_nonneg x
  rw [← sub_le_iff_le_add', le_div_iff₀ hc3]
  rcases le_total y c with h | h
  · have : (y - c) * c ^ 3 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hc3.le
    linarith [pow_nonneg hy0 4]
  · have h3 : c ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hc.le h 3
    have h4 : y * c ^ 3 ≤ y * y ^ 3 := mul_le_mul_of_nonneg_left h3 hy0
    have h5 : y ^ 4 = y * y ^ 3 := by ring
    nlinarith

/-- `2^{N/2} · 2^{-N}/2 ≤ (5/7)^N/2`, from `(7/5)² ≤ 2`. -/
lemma lc_sqrt_div_le (N : ℕ) : Real.sqrt (2 ^ N) * (1 / 2 ^ N / 2) ≤ (5 / 7 : ℝ) ^ N / 2 := by
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  have hs : 0 < Real.sqrt (2 ^ N) := Real.sqrt_pos.2 h2
  have hle : (7 / 5 : ℝ) ^ N ≤ Real.sqrt (2 ^ N) := by
    rw [Real.le_sqrt (by positivity) h2.le, ← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) N
  have hsq : Real.sqrt (2 ^ N) * Real.sqrt (2 ^ N) = 2 ^ N := Real.mul_self_sqrt h2.le
  have h75 : (5 / 7 : ℝ) ^ N * (7 / 5) ^ N = 1 := by rw [← mul_pow]; norm_num
  have key : Real.sqrt (2 ^ N) * (1 / 2 ^ N) ≤ (5 / 7 : ℝ) ^ N := by
    rw [show Real.sqrt (2 ^ N) * (1 / 2 ^ N) = 1 / Real.sqrt (2 ^ N) by
      field_simp; exact Real.sq_sqrt h2.le, div_le_iff₀ hs]
    nlinarith [mul_le_mul_of_nonneg_left hle (pow_pos (by norm_num : (0 : ℝ) < 5 / 7) N).le]
  calc Real.sqrt (2 ^ N) * (1 / 2 ^ N / 2) = Real.sqrt (2 ^ N) * (1 / 2 ^ N) / 2 := by ring
    _ ≤ (5 / 7 : ℝ) ^ N / 2 := div_le_div_of_nonneg_right key (by norm_num)

/-- The level-`N` block `lcPartial (N+1) - lcPartial N` as a sum over the positions. -/
lemma lcPartial_succ_sub (N : ℕ) (ω : ℕ → ℝ) :
    lcPartial (N + 1) ω - lcPartial N ω
      = ∑ k ∈ range (2 ^ N), ω (2 ^ N + k) • schauderC (2 ^ N + k) := by
  unfold lcPartial
  rw [show 2 ^ (N + 1) = 2 ^ N + 2 ^ N by ring, Finset.sum_range_add, add_sub_cancel_left]

/-- **Block bound.** The sup norm of the level-`N` block is at most `lcWeight N ω` (disjoint
supports of the level-`N` Schauder functions). -/
theorem norm_lcPartial_succ_sub_le (N : ℕ) (ω : ℕ → ℝ) :
    ‖lcPartial (N + 1) ω - lcPartial N ω‖ ≤ lcWeight N ω := by
  set c : ℝ := (6 / 5 : ℝ) ^ N with hc
  have hc0 : 0 < c := by positivity
  set C : ℝ := c + ∑ k ∈ range (2 ^ N), ω (2 ^ N + k) ^ 4 / c ^ 3 with hC
  have hCk : ∀ k ∈ range (2 ^ N), |ω (2 ^ N + k)| ≤ C := fun k hk => by
    have h1 := lc_abs_le_add_pow_four (ω (2 ^ N + k)) hc0
    have h2 := Finset.single_le_sum (f := fun k => ω (2 ^ N + k) ^ 4 / c ^ 3)
      (fun j _ => by positivity) hk
    rw [hC]
    linarith
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hCk 0 (by simp))
  have hW : lcWeight N ω = (5 / 7 : ℝ) ^ N / 2 * C := rfl
  rw [lcPartial_succ_sub, hW]
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
  simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Real.norm_eq_abs, schauderC, ContinuousMap.coe_mk]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hh : (0 : ℝ) < 1 / 2 ^ N := by positivity
  calc ∑ k ∈ range (2 ^ N), |ω (2 ^ N + k) * schauder (2 ^ N + k) t|
      = ∑ k ∈ range (2 ^ N), |ω (2 ^ N + k)| * schauderLevel N k t := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [schauder_two_pow_add (Finset.mem_range.1 hk), abs_mul,
          abs_of_nonneg (schauderLevel_nonneg _ _ _)]
    _ ≤ C * (Real.sqrt (2 ^ N) * (1 / 2 ^ N / 2)) := by
        refine lc_sum_le_of_atMostOne _ _ (by positivity) (fun k hk => ?_) ?_
        · have h1 := mul_le_mul (hCk k hk) (lcTent_le (k / 2 ^ N) _ (t : ℝ) hh.le)
            (lcTent_nonneg _ _ _) hC0
          have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (2 ^ N))
          rw [schauderLevel]
          linarith
        · intro i _ j _ hi hj
          have hi' : lcTent (i / 2 ^ N) (1 / 2 ^ N) t ≠ 0 := fun h0 => hi (by
            rw [schauderLevel, h0]; ring)
          have hj' : lcTent (j / 2 ^ N) (1 / 2 ^ N) t ≠ 0 := fun h0 => hj (by
            rw [schauderLevel, h0]; ring)
          obtain ⟨hi1, hi2⟩ := lcTent_mem_of_ne_zero hi'
          obtain ⟨hj1, hj2⟩ := lcTent_mem_of_ne_zero hj'
          refine lc_dyadic_unique hh le_rfl (u := (t : ℝ)) (v := (t : ℝ)) ?_ ?_ ?_ ?_ <;>
            · rwa [mul_one_div]
    _ ≤ C * ((5 / 7 : ℝ) ^ N / 2) := mul_le_mul_of_nonneg_left (lc_sqrt_div_le N) hC0
    _ = (5 / 7 : ℝ) ^ N / 2 * C := mul_comm _ _

/-! ### Almost sure summability of the block bounds -/

/-- The fourth moment `∫ x⁴ dN(0,1)` of the standard Gaussian (its value, `3`, is not needed). -/
noncomputable def gaussFourth : ℝ := ∫ x, x ^ 4 ∂gaussianReal 0 1

/-- `x⁴` is integrable for the standard Gaussian. -/
lemma integrable_pow_four_gaussianReal :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) ((4 : ℕ) : ℝ≥0∞)
    (by simp)).integrable_norm_pow (by norm_num)
  simpa [Real.norm_eq_abs, Even.pow_abs (by decide : Even 4)] using h

/-- The fourth power of a coordinate is integrable under `gaussSeq`. -/
lemma integrable_gaussSeq_coord_pow (j : ℕ) :
    Integrable (fun ω : ℕ → ℝ => ω j ^ 4) gaussSeq := by
  have hi := integrable_pow_four_gaussianReal
  rw [← (hasLaw_gaussSeq_coord j).map_eq] at hi
  exact (integrable_map_measure (g := fun x : ℝ => x ^ 4)
    (by fun_prop : Continuous fun x : ℝ => x ^ 4).aestronglyMeasurable
    (measurable_pi_apply j).aemeasurable).1 hi

/-- The fourth moment of each coordinate under `gaussSeq` is `gaussFourth`. -/
lemma integral_gaussSeq_coord_pow (j : ℕ) : ∫ ω, ω j ^ 4 ∂gaussSeq = gaussFourth := by
  unfold gaussFourth
  rw [← (hasLaw_gaussSeq_coord j).map_eq, integral_map (measurable_pi_apply j).aemeasurable
    (by fun_prop)]

/-- The block weights are integrable. -/
lemma integrable_lcWeight (n : ℕ) : Integrable (lcWeight n) gaussSeq := by
  have := isProbabilityMeasure_gaussSeq
  unfold lcWeight
  exact ((integrable_const _).add (integrable_finsetSum _ fun k _ =>
    (integrable_gaussSeq_coord_pow _).div_const _)).const_mul _

/-- The expectation of the level-`n` block weight. -/
lemma integral_lcWeight (n : ℕ) :
    ∫ ω, lcWeight n ω ∂gaussSeq
      = (5 / 7 : ℝ) ^ n / 2 * ((6 / 5 : ℝ) ^ n + 2 ^ n * gaussFourth / ((6 / 5 : ℝ) ^ n) ^ 3) := by
  have := isProbabilityMeasure_gaussSeq
  unfold lcWeight
  rw [integral_const_mul, integral_add (integrable_const _) (integrable_finsetSum _ fun k _ =>
    (integrable_gaussSeq_coord_pow _).div_const _), integral_const, integral_finsetSum _
    fun k _ => (integrable_gaussSeq_coord_pow _).div_const _]
  simp_rw [integral_div, integral_gaussSeq_coord_pow]
  simp [Finset.sum_const, Finset.card_range]
  ring

/-- The expected block weights are summable (two geometric series, ratios `6/7` and `1250/1512`). -/
lemma summable_integral_lcWeight : Summable fun n => ∫ ω, lcWeight n ω ∂gaussSeq := by
  simp_rw [integral_lcWeight]
  have h1 : Summable fun n : ℕ => (1 / 2 : ℝ) * ((5 / 7 : ℝ) * (6 / 5)) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h2 : Summable fun n : ℕ => gaussFourth / 2 * ((5 / 7 : ℝ) * 2 / (6 / 5) ^ 3) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine (h1.add h2).congr fun n => ?_
  have e : ((6 / 5 : ℝ) ^ 3) ^ n = ((6 / 5 : ℝ) ^ n) ^ 3 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [mul_pow (5 / 7 : ℝ) (6 / 5), div_pow (5 / 7 * 2 : ℝ), mul_pow (5 / 7 : ℝ) 2, e]
  ring

/-- The set where the block bounds are summable (it has full measure). -/
def lcGood : Set (ℕ → ℝ) := {ω | ∑' n, ENNReal.ofReal (lcWeight n ω) < ∞}

/-- The total block weight `Σ' ofReal (lcWeight n ω)` is measurable. -/
lemma measurable_lcWeight_tsum :
    Measurable fun ω : ℕ → ℝ => ∑' n, ENNReal.ofReal (lcWeight n ω) :=
  Measurable.tsum fun n => (measurable_lcWeight n).ennreal_ofReal

/-- The good set is measurable. -/
lemma measurableSet_lcGood : MeasurableSet lcGood :=
  measurableSet_lt measurable_lcWeight_tsum measurable_const

/-- Almost every Gaussian sequence lies in `lcGood`. -/
theorem ae_mem_lcGood : ∀ᵐ ω ∂gaussSeq, ω ∈ lcGood := by
  refine ae_lt_top measurable_lcWeight_tsum ?_
  rw [lintegral_tsum fun n => (measurable_lcWeight n).ennreal_ofReal.aemeasurable]
  have he : ∀ n, ∫⁻ ω, ENNReal.ofReal (lcWeight n ω) ∂gaussSeq
      = ENNReal.ofReal (∫ ω, lcWeight n ω ∂gaussSeq) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (integrable_lcWeight n)
      (Eventually.of_forall fun ω => lcWeight_nonneg n ω)).symm
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun ω => lcWeight_nonneg n ω)
    summable_integral_lcWeight]
  exact ENNReal.ofReal_ne_top

/-- On `lcGood` the block weights are summable. -/
lemma summable_lcWeight_of_mem {ω : ℕ → ℝ} (hω : ω ∈ lcGood) :
    Summable fun n => lcWeight n ω := by
  refine summable_of_sum_range_le (c := (∑' n, ENNReal.ofReal (lcWeight n ω)).toReal)
    (fun n => lcWeight_nonneg n ω) fun n => ?_
  have h : ∑ i ∈ range n, lcWeight i ω = (∑ i ∈ range n, ENNReal.ofReal (lcWeight i ω)).toReal := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => lcWeight_nonneg i ω,
      ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => lcWeight_nonneg i ω)]
  rw [h]
  exact ENNReal.toReal_mono hω.ne (ENNReal.sum_le_tsum _)

/-! ### The Lévy–Ciesielski path -/

/-- On `lcGood` the partial sums are uniformly Cauchy. -/
lemma cauchySeq_lcPartial {ω : ℕ → ℝ} (hω : ω ∈ lcGood) :
    CauchySeq fun N => lcPartial N ω := by
  refine cauchySeq_of_summable_dist ((summable_lcWeight_of_mem hω).of_nonneg_of_le
    (fun n => dist_nonneg) fun n => ?_)
  rw [dist_comm, dist_eq_norm]
  exact norm_lcPartial_succ_sub_le n ω

open Classical in
/-- **The Lévy–Ciesielski path.** On `lcGood` it is the uniform limit of the partial sums
`lcPartial N ω`; off `lcGood` (a null set) it is `0`. Its paths are continuous for every `ω`. -/
noncomputable def levyPath (ω : ℕ → ℝ) : C(unitInterval, ℝ) :=
  if ω ∈ lcGood then limUnder atTop (fun N => lcPartial N ω) else 0

/-- On `lcGood` the partial sums converge uniformly to `levyPath ω`. -/
theorem tendsto_lcPartial_levyPath {ω : ℕ → ℝ} (hω : ω ∈ lcGood) :
    Tendsto (fun N => lcPartial N ω) atTop (𝓝 (levyPath ω)) := by
  simp only [levyPath, hω, ite_true]
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_lcPartial hω))

/-- Pointwise form: `Σ_{m<2^N} ω m schauder m t → levyPath ω t` on `lcGood`. -/
theorem tendsto_lcPartial_apply {ω : ℕ → ℝ} (hω : ω ∈ lcGood) (t : unitInterval) :
    Tendsto (fun N => ∑ m ∈ range (2 ^ N), ω m * schauder m t) atTop (𝓝 (levyPath ω t)) := by
  simp_rw [← lcPartial_apply]
  exact ((continuous_eval_const t).tendsto _).comp (tendsto_lcPartial_levyPath hω)

/-- Every Schauder function vanishes at `0`. -/
lemma schauder_apply_zero (m : ℕ) : schauder m 0 = 0 := by
  unfold schauder
  split_ifs
  · rfl
  · rw [schauderLevel, lcTent_of_le (by positivity), mul_zero]

/-- The path starts at `0`, for every `ω`. -/
theorem levyPath_zero (ω : ℕ → ℝ) : levyPath ω 0 = 0 := by
  by_cases hω : ω ∈ lcGood
  · refine tendsto_nhds_unique (tendsto_lcPartial_apply hω 0) ?_
    simp [schauder_apply_zero]
  · simp [levyPath, hω]

end MeynTweedie.LimitTheorems

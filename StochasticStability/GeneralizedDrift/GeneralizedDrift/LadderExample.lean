/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.LadderDrift
import Mathlib.MeasureTheory.Function.Floor

/-!
# The up-or-down ladder chain (MT (19.78)–(19.79))

Meyn and Tweedie, pp. 505–506. With `X = ℤ₊` (here the points `0, 1, 2, …` of `ℝ`; a point
`x ∈ ℝ` behaves like `⌊x⌋₊`) and `0 < p, q < 1`, the ladder chain moves one rung up through
`Λ₀` and one rung down through `Λ₂`, and on `X` it moves down (reflected at `0`) with
probability `p` and up with probability `1 − p` (`exLam p q`, (19.78)–(19.79)); its zero-level
transitions have the form (19.65).

**Results.**
* `exMarg_apply`: the marginal chain `Φ^Λ` is the reflected simple random walk
  (`P(x, x − 1) = p`, `P(x, x + 1) = 1 − p`, `P(0, 0) = p`).
* `exMarg_hasInvariant_iff` (p. 505): `Φ^Λ` has an invariant probability iff `p > ½`; it is the
  geometric law `ν{n} = (1 − r) rⁿ`, `r = (1 − p)/p` (`isInvariant_exNu`).
* `exBeta` and `one_lt_exBeta_iff` (p. 505): `β(x) = 2(1 − q)`, so `β > 1` iff `q < ½`.
* `exLadder_isPositive`: (19.68) holds if `q < ½ < p`, and then (Theorem 19.3.4, with the
  `δ_{(0,0)}`-irreducibility `exLadder_isPhiIrreducible`) the ladder chain is positive.

* The bottom rung (19.80) (`ex80Star`, `isMarkovKernel_ex80`) and the claim of p. 506 that `[0]`
  is not petite (`ex80_rung_zero_not_petite`); the same holds for (19.79)
  (`exLadder_rung_zero_not_petite`), even when that chain is positive. Both follow from
  `not_isPetite_of_bounded_steps`: a set on which a level function `φ` is unbounded is not
  petite when `φ` drops by at most `d` per step (`ladderChainKernel_step_ge`, `twoPoint_Iio`).

**Elsewhere.** The transience of the process on `[0]` for (19.80), quantified, is
`eq_19_81_transient` in `Ladder80Transience`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal NNReal Topology

/-- The move down (reflected at `0`): `⌊x⌋₊ − 1`. -/
noncomputable def exDown (x : ℝ) : ℝ := ((⌊x⌋₊ - 1 : ℕ) : ℝ)

/-- The move up: `⌊x⌋₊ + 1`. -/
noncomputable def exUp (x : ℝ) : ℝ := ((⌊x⌋₊ + 1 : ℕ) : ℝ)

/-- The down move is measurable. -/
theorem measurable_exDown : Measurable exDown :=
  (measurable_from_nat (f := fun n : ℕ => ((n - 1 : ℕ) : ℝ))).comp Nat.measurable_floor

/-- The up move is measurable. -/
theorem measurable_exUp : Measurable exUp :=
  (measurable_from_nat (f := fun n : ℕ => ((n + 1 : ℕ) : ℝ))).comp Nat.measurable_floor

/-- On `ℤ₊`, the moves are `n − 1` (reflected) and `n + 1`. -/
theorem exDown_natCast (n : ℕ) : exDown n = ((n - 1 : ℕ) : ℝ) := by
  rw [exDown, Nat.floor_natCast]

/-- On `ℤ₊`, the up move is `n + 1`. -/
theorem exUp_natCast (n : ℕ) : exUp n = ((n + 1 : ℕ) : ℝ) := by
  rw [exUp, Nat.floor_natCast]

/-- The kernel `a δ_{x−1} + b δ_{x+1}`. -/
noncomputable def twoPoint (a b : ℝ≥0∞) : Kernel ℝ ℝ where
  toFun x := a • Measure.dirac (exDown x) + b • Measure.dirac (exUp x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
    exact (measurable_const.mul ((measurable_one.indicator hs).comp measurable_exDown)).add
      (measurable_const.mul ((measurable_one.indicator hs).comp measurable_exUp))

/-- `(a δ_{x−1} + b δ_{x+1})(B) = a 1_B(x − 1) + b 1_B(x + 1)`. -/
theorem twoPoint_apply (a b : ℝ≥0∞) (x : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    twoPoint a b x B = a * B.indicator 1 (exDown x) + b * B.indicator 1 (exUp x) := by
  change (a • Measure.dirac (exDown x) + b • Measure.dirac (exUp x)) B = _
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hB,
    Measure.dirac_apply' _ hB, smul_eq_mul, smul_eq_mul]

/-- **The kernels (19.78)–(19.79)**: `Λ₀ = pq δ_{x−1} + (1 − p)q δ_{x+1}`,
`Λ₂ = p(1 − q) δ_{x−1} + (1 − p)(1 − q) δ_{x+1}`, `Λₖ = 0` otherwise. -/
noncomputable def exLam (p q : ℝ) (k : ℕ) : Kernel ℝ ℝ :=
  if k = 0 then twoPoint (ENNReal.ofReal (p * q)) (ENNReal.ofReal ((1 - p) * q))
  else if k = 2 then twoPoint (ENNReal.ofReal (p * (1 - q))) (ENNReal.ofReal ((1 - p) * (1 - q)))
  else 0

/-- `Σₖ f(k) Λₖ = f(0) Λ₀ + f(2) Λ₂` for the example. -/
theorem tsum_exLam (p q : ℝ) (f : ℕ → ℝ≥0∞) (x : ℝ) (B : Set ℝ) :
    ∑' k, f k * exLam p q k x B = f 0 * exLam p q 0 x B + f 2 * exLam p q 2 x B := by
  rw [tsum_eq_sum (s := {0, 2}) fun k hk => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [exLam, hk.1, hk.2]]
  rw [Finset.sum_pair (by norm_num)]

/-- **The marginal chain** (MT p. 505): `Λ(x, B) = p 1_B(x − 1) + (1 − p) 1_B(x + 1)`, the
reflected simple random walk. -/
theorem exMarg_apply {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (x : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    ladderMarg (exLam p q) x B = ENNReal.ofReal p * B.indicator 1 (exDown x) +
      ENNReal.ofReal (1 - p) * B.indicator 1 (exUp x) := by
  have h := tsum_exLam p q (fun _ => 1) x B
  simp only [one_mul] at h
  rw [ladderMarg, Kernel.sum_apply' _ _ hB, h]
  simp only [exLam, show (2 : ℕ) ≠ 0 by norm_num, ↓reduceIte]
  rw [twoPoint_apply _ _ _ hB, twoPoint_apply _ _ _ hB]
  have e1 : ENNReal.ofReal (p * q) + ENNReal.ofReal (p * (1 - q)) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg hp0 (by linarith))]; ring_nf
  have e2 : ENNReal.ofReal ((1 - p) * q) + ENNReal.ofReal ((1 - p) * (1 - q)) =
      ENNReal.ofReal (1 - p) := by
    rw [← ENNReal.ofReal_add (mul_nonneg (by linarith) hq0)
      (mul_nonneg (by linarith) (by linarith))]; ring_nf
  calc ENNReal.ofReal (p * q) * B.indicator 1 (exDown x) +
        ENNReal.ofReal ((1 - p) * q) * B.indicator 1 (exUp x) +
        (ENNReal.ofReal (p * (1 - q)) * B.indicator 1 (exDown x) +
        ENNReal.ofReal ((1 - p) * (1 - q)) * B.indicator 1 (exUp x))
      = (ENNReal.ofReal (p * q) + ENNReal.ofReal (p * (1 - q))) * B.indicator 1 (exDown x) +
        (ENNReal.ofReal ((1 - p) * q) + ENNReal.ofReal ((1 - p) * (1 - q))) *
          B.indicator 1 (exUp x) := by ring
    _ = _ := by rw [e1, e2]

/-- The marginal kernel is a Markov kernel. -/
theorem isMarkovKernel_exMarg {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : IsMarkovKernel (ladderMarg (exLam p q)) :=
  ⟨fun x => ⟨by
    rw [exMarg_apply hp0 hp1 hq0 hq1 x MeasurableSet.univ]
    simp only [indicator_univ, Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_add hp0 (by linarith)]
    simp⟩⟩

/-- **`β(x) = 2(1 − q)`** (MT p. 505). -/
theorem exBeta {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq1 : q ≤ 1) (x : ℝ) :
    ladderBeta (exLam p q) x = ENNReal.ofReal (2 * (1 - q)) := by
  rw [ladderBeta, tsum_exLam p q (fun k => (k : ℝ≥0∞)) x univ]
  simp only [Nat.cast_zero, zero_mul, zero_add, exLam, show (2 : ℕ) ≠ 0 by norm_num,
    ↓reduceIte]
  rw [twoPoint_apply _ _ _ MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add (mul_nonneg hp0 (by linarith))
    (mul_nonneg (by linarith) (by linarith)), show ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- **`β > 1` iff `q < ½`** (MT p. 505). -/
theorem one_lt_exBeta_iff {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq1 : q ≤ 1)
    (x : ℝ) : 1 < ladderBeta (exLam p q) x ↔ q < 1 / 2 := by
  rw [exBeta hp0 hp1 hq1, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff']
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; exact ⟨by linarith, by linarith⟩

/-! ### The invariant law of `Φ^Λ` -/

/-- The weights `ν{n} = (1 − r) rⁿ`, `r = (1 − p)/p`. -/
noncomputable def exWeight (p : ℝ) (n : ℕ) : ℝ := (1 - (1 - p) / p) * ((1 - p) / p) ^ n

/-- The geometric law `ν = Σₙ (1 − r) rⁿ δₙ`. -/
noncomputable def exNu (p : ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ => ENNReal.ofReal (exWeight p n) • Measure.dirac (n : ℝ)

/-- Integrals against `ν`. -/
theorem lintegral_exNu (p : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂exNu p = ∑' n : ℕ, ENNReal.ofReal (exWeight p n) * g n := by
  rw [exNu, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ hg, smul_eq_mul]

/-- For `½ < p ≤ 1`, `0 ≤ r < 1`. -/
theorem exRatio_mem {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) :
    0 ≤ (1 - p) / p ∧ (1 - p) / p < 1 := by
  have hp0 : 0 < p := by linarith
  exact ⟨div_nonneg (by linarith) hp0.le, by rw [div_lt_one hp0]; linarith⟩

/-- The weights are non-negative. -/
theorem exWeight_nonneg {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) (n : ℕ) : 0 ≤ exWeight p n := by
  obtain ⟨h0, h1⟩ := exRatio_mem hp hp1
  exact mul_nonneg (by linarith) (pow_nonneg h0 n)

/-- **`ν` is a probability** for `p > ½`. -/
theorem isProbabilityMeasure_exNu {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (exNu p) := by
  obtain ⟨h0, h1⟩ := exRatio_mem hp hp1
  refine ⟨?_⟩
  have hsum : HasSum (fun n => exWeight p n) 1 := by
    have := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 - (1 - p) / p)
    rwa [mul_inv_cancel₀ (by linarith)] at this
  rw [exNu, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (exWeight_nonneg hp hp1) hsum.summable, hsum.tsum_eq,
    ENNReal.ofReal_one]

/-- The balance equations of `ν`: `p(ν₀ + ν₁) = ν₀` and `pν_{n+2} + (1 − p)νₙ = ν_{n+1}`. -/
theorem exWeight_balance {p : ℝ} (hp0 : 0 < p) :
    exWeight p 0 * p + exWeight p 1 * p = exWeight p 0 ∧
      ∀ n, exWeight p (n + 2) * p + exWeight p n * (1 - p) = exWeight p (n + 1) := by
  refine ⟨?_, fun n => ?_⟩
  · simp only [exWeight, pow_zero, pow_one]
    field_simp
    ring
  · simp only [exWeight, pow_succ]
    field_simp
    ring

/-- **`ν` is invariant for `Φ^Λ`** for `½ < p ≤ 1` (MT p. 505). -/
theorem isInvariant_exNu {p q : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsInvariant (ladderMarg (exLam p q)) (exNu p) := by
  have hp0 : 0 < p := by linarith
  have := isMarkovKernel_exMarg hp0.le hp1 hq0 hq1
  obtain ⟨hb0, hb1⟩ := exWeight_balance hp0
  have hw := exWeight_nonneg hp hp1
  ext B hB
  set f : ℕ → ℝ≥0∞ := fun m => B.indicator 1 (m : ℝ) with hf
  rw [Measure.bind_apply hB (Kernel.aemeasurable _), lintegral_exNu p (Kernel.measurable_coe _ hB),
    exNu, Measure.sum_apply _ hB]
  simp_rw [Measure.smul_apply, Measure.dirac_apply' _ hB, smul_eq_mul,
    exMarg_apply hp0.le hp1 hq0 hq1 _ hB, exDown_natCast, exUp_natCast]
  change ∑' n, ENNReal.ofReal (exWeight p n) * (ENNReal.ofReal p * f (n - 1) +
    ENNReal.ofReal (1 - p) * f (n + 1)) = ∑' n, ENNReal.ofReal (exWeight p n) * f n
  have hA : ∑' n, ENNReal.ofReal (exWeight p n) * (ENNReal.ofReal p * f (n - 1)) =
      ENNReal.ofReal (exWeight p 0 * p + exWeight p 1 * p) * f 0 +
        ∑' n, ENNReal.ofReal (exWeight p (n + 2) * p) * f (n + 1) := by
    rw [tsum_eq_zero_add' ENNReal.summable, tsum_eq_zero_add' ENNReal.summable]
    simp only [Nat.zero_sub, Nat.add_sub_cancel, zero_add]
    rw [ENNReal.ofReal_add (mul_nonneg (hw 0) hp0.le) (mul_nonneg (hw 1) hp0.le),
      ENNReal.ofReal_mul (hw 0), ENNReal.ofReal_mul (hw 1)]
    have e : ∀ n : ℕ, ENNReal.ofReal (exWeight p (n + 1 + 1)) * (ENNReal.ofReal p * f (n + 1)) =
        ENNReal.ofReal (exWeight p (n + 2) * p) * f (n + 1) := fun n => by
      rw [ENNReal.ofReal_mul (hw _)]; ring
    simp_rw [e]
    ring
  have hB2 : ∑' n, ENNReal.ofReal (exWeight p n) * (ENNReal.ofReal (1 - p) * f (n + 1)) =
      ∑' n, ENNReal.ofReal (exWeight p n * (1 - p)) * f (n + 1) := tsum_congr fun n => by
    rw [ENNReal.ofReal_mul (hw _)]; ring
  have hR : ∑' n, ENNReal.ofReal (exWeight p n) * f n =
      ENNReal.ofReal (exWeight p 0) * f 0 + ∑' n, ENNReal.ofReal (exWeight p (n + 1)) * f (n + 1) :=
    tsum_eq_zero_add' ENNReal.summable
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, hA, hB2, hR, add_assoc, ← ENNReal.tsum_add, hb0]
  congr 1
  refine tsum_congr fun n => ?_
  rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg (hw _) hp0.le) (mul_nonneg (hw _) (by linarith)),
    hb1 n]

/-- Indicators of singletons of `ℤ₊ ⊂ ℝ`. -/
theorem indicator_natCast_singleton (m k : ℕ) :
    ({(m : ℝ)} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) (k : ℝ) = if k = m then 1 else 0 := by
  by_cases h : k = m
  · subst h; simp
  · rw [indicator_of_notMem (by simpa using h)]; simp [h]

/-- **No invariant probability for `p ≤ ½`** (MT p. 505): an invariant probability of `Φ^Λ` lives
on `ℤ₊`, its masses satisfy the flux balance `p ν_{n+1} = (1 − p) νₙ`, so they do not decrease
when `p ≤ ½` and cannot sum to one. -/
theorem exMarg_not_invariant {p q : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 2) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsInvariant (ladderMarg (exLam p q)) μ) :
    False := by
  have hp1 : p ≤ 1 := by linarith
  have := isMarkovKernel_exMarg hp0.le hp1 hq0 hq1
  set Λ := ladderMarg (exLam p q)
  have hinv : ∀ B, MeasurableSet B → μ B = ∫⁻ x, Λ x B ∂μ := fun B hB => by
    conv_lhs => rw [← hμ]
    exact Measure.bind_apply hB (Kernel.aemeasurable _)
  set N := range fun n : ℕ => (n : ℝ) with hNdef
  have hNm : MeasurableSet N := (countable_range _).measurableSet
  have hN : μ Nᶜ = 0 := by
    rw [hinv _ hNm.compl]
    refine lintegral_eq_zero_iff (Kernel.measurable_coe _ hNm.compl) |>.2 ?_
    refine Eventually.of_forall fun x => ?_
    change Λ x Nᶜ = 0
    rw [exMarg_apply hp0.le hp1 hq0 hq1 x hNm.compl,
      indicator_of_notMem (show exDown x ∉ Nᶜ from fun h => h ⟨_, rfl⟩),
      indicator_of_notMem (show exUp x ∉ Nᶜ from fun h => h ⟨_, rfl⟩)]
    simp
  set c : ℕ → ℝ≥0∞ := fun k => μ {(k : ℝ)} with hc
  have hlint : ∀ g : ℝ → ℝ≥0∞, Measurable g → ∫⁻ x, g x ∂μ = ∑' k : ℕ, g (k : ℝ) * c k :=
      fun g hg => by
    rw [← lintegral_add_compl g hNm, setLIntegral_measure_zero _ _ hN, add_zero, hNdef,
      range_eq_iUnion, lintegral_iUnion (fun k => measurableSet_singleton _)
        (fun i j hij => disjoint_singleton.2 fun h => hij (by exact_mod_cast h))]
    exact tsum_congr fun k => lintegral_singleton g _
  have hcfin : ∀ k, c k ≠ ∞ := fun k => measure_ne_top _ _
  -- the balance equations
  have hsing : ∀ m : ℕ, c m = ∑' k, (ENNReal.ofReal p * (if k - 1 = m then 1 else 0) +
      ENNReal.ofReal (1 - p) * (if k + 1 = m then 1 else 0)) * c k := fun m => by
    change μ {(m : ℝ)} = _
    rw [hinv _ (measurableSet_singleton _), hlint _ (Kernel.measurable_coe _
      (measurableSet_singleton _))]
    refine tsum_congr fun k => ?_
    rw [exMarg_apply hp0.le hp1 hq0 hq1 _ (measurableSet_singleton _), exDown_natCast,
      exUp_natCast, indicator_natCast_singleton, indicator_natCast_singleton]
  have e0 : c 0 = ENNReal.ofReal p * (c 0 + c 1) := by
    conv_lhs => rw [hsing 0]
    rw [tsum_eq_sum (s := {0, 1}) fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [show k - 1 ≠ 0 by omega]]
    rw [Finset.sum_pair (by norm_num)]
    simp only [Nat.zero_sub, Nat.sub_self, ↓reduceIte, mul_one, zero_add,
      show (0 : ℕ) + 1 ≠ 0 by norm_num, show (1 : ℕ) + 1 ≠ 0 by norm_num, mul_zero, add_zero]
    ring
  have eS : ∀ n, c (n + 1) = ENNReal.ofReal p * c (n + 2) + ENNReal.ofReal (1 - p) * c n :=
    fun n => by
    conv_lhs => rw [hsing (n + 1)]
    rw [tsum_eq_sum (s := {n, n + 2}) fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [show k - 1 ≠ n + 1 by omega, show k ≠ n by omega]]
    rw [Finset.sum_pair (by omega)]
    simp only [show n - 1 ≠ n + 1 by omega, show n + 2 - 1 = n + 1 by omega,
      show n + 2 + 1 ≠ n + 1 by omega, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add]
    ring
  -- real forms
  set a : ℕ → ℝ := fun k => (c k).toReal with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => ENNReal.toReal_nonneg
  have ra0 : a 0 = p * (a 0 + a 1) := by
    have := congrArg ENNReal.toReal e0
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0.le,
      ENNReal.toReal_add (hcfin 0) (hcfin 1)] at this
  have raS : ∀ n, a (n + 1) = p * a (n + 2) + (1 - p) * a n := fun n => by
    have := congrArg ENNReal.toReal (eS n)
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hcfin _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hcfin _)), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal (by linarith)]
      at this
  have hflux : ∀ n, p * a (n + 1) = (1 - p) * a n := fun n => by
    induction n with
    | zero => linarith
    | succ n ih => have := raS n; linarith
  have hmono : ∀ n, a 0 ≤ a n := fun n => by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      have h1 := hflux n
      have h2 : p * a n ≤ (1 - p) * a n := mul_le_mul_of_nonneg_right (by linarith) (ha0 n)
      have h3 : a n ≤ a (n + 1) := by nlinarith
      linarith
  -- the masses sum to one
  have htot : ∑' k, c k = 1 := by
    have h := hlint (fun _ => 1) measurable_const
    rw [lintegral_const, measure_univ, one_mul] at h
    simp only [one_mul] at h
    exact h.symm
  have hpart : ∀ M, ∑ k ∈ range M, a k ≤ 1 := fun M => by
    have h1 : ∑ k ∈ range M, c k ≤ 1 := htot ▸ ENNReal.sum_le_tsum _
    have h2 := ENNReal.toReal_mono ENNReal.one_ne_top h1
    rwa [ENNReal.toReal_sum fun k _ => hcfin k, ENNReal.toReal_one] at h2
  have hz : a 0 = 0 := by
    by_contra hne
    have hpos : 0 < a 0 := lt_of_le_of_ne (ha0 0) (Ne.symm hne)
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / a 0)
    have h1 : (M : ℝ) * a 0 ≤ ∑ k ∈ range M, a k := by
      calc (M : ℝ) * a 0 = ∑ _k ∈ range M, a 0 := by simp
        _ ≤ ∑ k ∈ range M, a k := sum_le_sum fun k _ => hmono k
    have h2 : 1 < (M : ℝ) * a 0 := by rwa [div_lt_iff₀ hpos] at hM
    linarith [hpart M]
  have hall : ∀ n, a n = 0 := fun n => by
    induction n with
    | zero => exact hz
    | succ n ih =>
      have := hflux n
      rw [ih, mul_zero] at this
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
  have hc0 : ∀ k, c k = 0 := fun k => by
    have := hall k
    rw [ha, ENNReal.toReal_eq_zero_iff] at this
    exact this.resolve_right (hcfin k)
  simp [hc0] at htot

/-- **`Φ^Λ` has an invariant probability iff `p > ½`** (MT p. 505), for `0 < p ≤ 1`. -/
theorem exMarg_hasInvariant_iff {p q : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsInvariant (ladderMarg (exLam p q)) μ) ↔
      1 / 2 < p := by
  constructor
  · rintro ⟨μ, hμp, hμ⟩
    by_contra h
    exact exMarg_not_invariant hp0 (not_lt.1 h) hq0 hq1 μ hμ
  · intro hp
    exact ⟨exNu p, isProbabilityMeasure_exNu hp hp1, isInvariant_exNu hp hp1 hq0 hq1⟩

/-! ### The ladder chain of the example -/

/-- One step down the ladder and down `X`, with probability at least `p(1 − q)`. -/
theorem exLadder_step_ge {p q : ℝ} (i : ℕ) (x : ℝ) :
    ENNReal.ofReal (p * (1 - q)) ≤
      avgLadderKernel (exLam p q) (i, x) {((i - 1 : ℕ), exDown x)} := by
  have hd : MeasurableSet ({exDown x} : Set ℝ) := measurableSet_singleton _
  have hΛ2 : ENNReal.ofReal (p * (1 - q)) ≤ exLam p q 2 x {exDown x} := by
    simp only [exLam, show (2 : ℕ) ≠ 0 by norm_num, ↓reduceIte]
    rw [twoPoint_apply _ _ _ hd, indicator_of_mem (mem_singleton _), Pi.one_apply, mul_one]
    exact le_self_add
  rw [← singleton_prod_singleton]
  rcases Nat.lt_or_ge i 2 with hi | hi
  · rw [show i - 1 = 0 by omega, eq_3_40_zero _ _ _ _ hd, ladderStar, Kernel.sum_apply' _ _ hd]
    refine hΛ2.trans ?_
    have := ENNReal.le_tsum (f := fun j => exLam p q (j + (i + 1)) x {exDown x}) (1 - i)
    rwa [show 1 - i + (i + 1) = 2 by omega] at this
  · rw [eq_3_40_mid _ _ (by omega) (by omega) _ hd, show i + 1 - (i - 1) = 2 by omega]
    exact hΛ2

/-- **Reaching the origin** of the example ladder: `P^{k+1}((i, x), {(0, 0)}) ≥ (p(1 − q))^{k+1}`
when `i ≤ k` and `⌊x⌋₊ ≤ k`. -/
theorem exLadder_pow_ge {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (k : ℕ) (i : ℕ) (x : ℝ) (hi : i ≤ k) (hx : ⌊x⌋₊ ≤ k) :
    ENNReal.ofReal (p * (1 - q)) ^ (k + 1) ≤
      (avgLadderKernel (exLam p q) ^ (k + 1)) (i, x) {((0 : ℕ), (0 : ℝ))} := by
  have := isMarkovKernel_exMarg hp0 hp1 hq0 hq1
  have := isMarkovKernel_avgLadderKernel (exLam p q)
  induction k generalizing i x with
  | zero =>
    rw [zero_add, pow_one, pow_one]
    have h := exLadder_step_ge (p := p) (q := q) i x
    have hi0 : i = 0 := by omega
    have hx0 : exDown x = 0 := by rw [exDown, show ⌊x⌋₊ = 0 by omega]; simp
    subst hi0
    rw [hx0, Nat.zero_sub] at h
    exact h
  | succ k ih =>
    set y0 : ℕ × ℝ := ((i - 1 : ℕ), exDown x) with hy0
    have hfl : ⌊exDown x⌋₊ = ⌊x⌋₊ - 1 := by rw [exDown, Nat.floor_natCast]
    have hrec := ih (i - 1) (exDown x) (by omega) (by rw [hfl]; omega)
    rw [pow_succ_apply _ (k + 1) _ (measurableSet_singleton _)]
    calc ENNReal.ofReal (p * (1 - q)) ^ (k + 1 + 1)
        = ENNReal.ofReal (p * (1 - q)) ^ (k + 1) * ENNReal.ofReal (p * (1 - q)) := pow_succ _ _
      _ ≤ (avgLadderKernel (exLam p q) ^ (k + 1)) y0 {((0 : ℕ), (0 : ℝ))} *
            avgLadderKernel (exLam p q) (i, x) {y0} :=
          mul_le_mul' hrec (exLadder_step_ge i x)
      _ = ∫⁻ y in {y0}, (avgLadderKernel (exLam p q) ^ (k + 1)) y {((0 : ℕ), (0 : ℝ))}
            ∂avgLadderKernel (exLam p q) (i, x) :=
          (lintegral_singleton (fun y => (avgLadderKernel (exLam p q) ^ (k + 1)) y
            {((0 : ℕ), (0 : ℝ))}) y0).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _

/-- **`δ_{(0,0)}`-irreducibility** of the example ladder for `p > 0`, `q < 1`. -/
theorem exLadder_isPhiIrreducible {p q : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    haveI := isMarkovKernel_exMarg hp0.le hp1 hq0 hq1.le
    haveI := isMarkovKernel_avgLadderKernel (exLam p q)
    IsPhiIrreducible (avgLadderKernel (exLam p q)) (Measure.dirac ((0 : ℕ), (0 : ℝ))) := by
  have := isMarkovKernel_exMarg hp0.le hp1 hq0 hq1.le
  have := isMarkovKernel_avgLadderKernel (exLam p q)
  intro A hA hpos z
  have h0 : ((0 : ℕ), (0 : ℝ)) ∈ A := by
    by_contra h0
    rw [Measure.dirac_apply' _ hA, indicator_of_notMem h0] at hpos
    exact lt_irrefl _ hpos
  set k := max z.1 ⌊z.2⌋₊
  have hpq : 0 < ENNReal.ofReal (p * (1 - q)) :=
    ENNReal.ofReal_pos.2 (mul_pos hp0 (by linarith))
  refine (hitProb_pos_iff _ hA z).2 ⟨k, lt_of_lt_of_le (ENNReal.pow_pos hpq (k + 1)) ?_⟩
  exact (exLadder_pow_ge hp0.le hp1 hq0 hq1.le k z.1 z.2 (le_max_left _ _)
    (le_max_right _ _)).trans (measure_mono (singleton_subset_iff.2 h0))

/-- **The example satisfies (19.68) when `q < ½ < p`, and the ladder chain is then positive**
(MT p. 505, by Theorem 19.3.4). -/
theorem exLadder_isPositive {p q : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq : q < 1 / 2) :
    haveI := isMarkovKernel_exMarg (by linarith) hp1 hq0 (by linarith)
    haveI := isMarkovKernel_avgLadderKernel (exLam p q)
    1 < ∫⁻ w, ladderBeta (exLam p q) w ∂exNu p ∧
      IsPositive (avgLadderKernel (exLam p q))
        (maxIrrMeasure (avgLadderKernel (exLam p q)) (Measure.dirac ((0 : ℕ), (0 : ℝ)))) := by
  have hp0 : 0 < p := by linarith
  have := isMarkovKernel_exMarg hp0.le hp1 hq0 (by linarith)
  have := isMarkovKernel_avgLadderKernel (exLam p q)
  have := isProbabilityMeasure_exNu hp hp1
  have h68 : 1 < ∫⁻ w, ladderBeta (exLam p q) w ∂exNu p := by
    simp_rw [exBeta hp0.le hp1 (by linarith)]
    rw [lintegral_const, measure_univ, mul_one, ← ENNReal.ofReal_one,
      ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    linarith
  refine ⟨h68, theorem_19_3_4 (exLam p q) ?_ (isInvariant_exNu hp hp1 hq0 (by linarith)) h68⟩
  exact isMaximalIrreducibility_maxIrrMeasure _
    (exLadder_isPhiIrreducible hp0 hp1 hq0 (by linarith)) Measure.dirac_ne_zero

variable {X : Type*} [MeasurableSpace X] in
/-- **Sets on which a level function is unbounded are not petite for chains with bounded
downward steps.** If `φ(Φ₁) ≥ φ(x) − d` `P(x, ·)`-a.s. (`d ≥ 0`) and `φ` is unbounded above on
`C`, then `C` is not petite: from far up the chain cannot reach `{φ < M}` in a few steps, so the
minorizing measure `ν_a` charges no `{φ < M}`. -/
theorem not_isPetite_of_bounded_steps (P : Kernel X X) [IsMarkovKernel P] {φ : X → ℝ}
    (hφ : Measurable φ) {d : ℝ} (hd : 0 ≤ d) (hstep : ∀ z, P z {w | φ w < φ z - d} = 0) {C : Set X}
    (hC : ∀ M : ℝ, ∃ z ∈ C, M ≤ φ z) : ¬ IsPetite P C := by
  rintro ⟨a, ν, -, ha, hν0, hle⟩
  have hS : ∀ c : ℝ, MeasurableSet {w | φ w < c} := fun c => measurableSet_lt hφ measurable_const
  -- `n` steps go down by at most `n d`
  have hpow : ∀ (n : ℕ) z, (P ^ n) z {w | φ w < φ z - n * d} = 0 := by
    intro n
    induction n with
    | zero =>
      intro z
      rw [pow_zero_apply, Measure.dirac_apply' _ (hS _)]
      simp
    | succ n ih =>
      intro z
      rw [show n + 1 = 1 + n by ring, pow_add_eq, pow_one, Kernel.comp_apply' _ _ _ (hS _)]
      have hae : ∀ᵐ y ∂P z, φ z - d ≤ φ y := by
        rw [ae_iff]
        simpa only [not_le] using hstep z
      refine (lintegral_congr_ae (g := 0) (hae.mono fun y hy => ?_)).trans lintegral_zero
      refine measure_mono_null (fun w hw => ?_) (ih y)
      simp only [mem_ofPred_eq] at hw ⊢
      push_cast at hw
      linarith
  -- `ν {φ < M} = 0`
  have hνM : ∀ M : ℝ, ν {w | φ w < M} = 0 := by
    intro M
    have htail := ENNReal.tendsto_sum_nat_add a (by rw [ha]; exact ENNReal.one_ne_top)
    refine le_antisymm (ge_of_tendsto' htail fun N => ?_) zero_le
    obtain ⟨z, hz, hzM⟩ := hC (M + N * d)
    calc ν {w | φ w < M} ≤ sampledKernel P a z {w | φ w < M} := hle z hz _
      _ = ∑' n, a n * (P ^ n) z {w | φ w < M} := sampledKernel_apply P a z (hS M)
      _ = ∑' n, a (n + N) * (P ^ (n + N)) z {w | φ w < M} := by
          rw [← ENNReal.summable.sum_add_tsum_nat_add' (f := fun n => a n * (P ^ n) z
            {w | φ w < M}) (k := N)]
          rw [Finset.sum_eq_zero fun n hn => ?_, zero_add]
          have hn' : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.1 hn).le
          refine mul_eq_zero_of_right _ (measure_mono_null (fun w hw => ?_) (hpow n z))
          simp only [mem_ofPred_eq] at hw ⊢
          nlinarith
      _ ≤ ∑' n, a (n + N) := ENNReal.tsum_le_tsum fun n => by
          calc a (n + N) * (P ^ (n + N)) z {w | φ w < M} ≤ a (n + N) * 1 := by
                have := isMarkovKernel_pow P (n + N)
                gcongr
                exact prob_le_one
            _ = a (n + N) := mul_one _
  have hU : (univ : Set X) = ⋃ M : ℕ, {w | φ w < M} := by
    refine (eq_univ_of_forall fun w => ?_).symm
    obtain ⟨M, hM⟩ := exists_nat_gt (φ w)
    exact mem_iUnion.2 ⟨M, hM⟩
  exact hν0 (Measure.measure_univ_eq_zero.1 (by
    rw [hU]; exact measure_iUnion_null fun M => hνM M))

/-- Row `i` of the ladder chain charges `ℤ₊ × B` with `Σ_{k ≤ i} Λₖ(x, B) + Λ*ᵢ(x, B)`. -/
theorem ladderChainKernel_snd_preimage (Λ Λs : ℕ → Kernel ℝ ℝ) (i : ℕ) (x : ℝ) {B : Set ℝ}
    (hB : MeasurableSet B) :
    ladderChainKernel Λ Λs (i, x) (Prod.snd ⁻¹' B) =
      ∑ k ∈ Finset.range (i + 1), Λ k x B + Λs i x B := by
  have hm : ∀ m : ℕ, Prod.mk m ⁻¹' (Prod.snd ⁻¹' B) = B := fun m => by ext y; simp
  rw [ladderChainKernel_apply, ladderRow, FunLike.coe_add, Pi.add_apply, Measure.add_apply,
    Kernel.sum_apply' _ _ (measurable_snd hB), tsum_fintype,
    Kernel.map_apply' _ measurable_prodMk_left x (measurable_snd hB), hm]
  simp_rw [Kernel.map_apply' _ measurable_prodMk_left x (measurable_snd hB), hm]
  rw [Fin.sum_univ_eq_sum_range (fun k => Λ k x B), add_comm]

/-- If no `Λₖ`, `Λ*ᵢ` moves down by more than `d`, neither does the ladder chain. -/
theorem ladderChainKernel_step_ge (Λ Λs : ℕ → Kernel ℝ ℝ) {d : ℝ}
    (hΛ : ∀ k x, Λ k x {w | w < x - d} = 0) (hΛs : ∀ i x, Λs i x {w | w < x - d} = 0)
    (z : ℕ × ℝ) : ladderChainKernel Λ Λs z {w | w.2 < z.2 - d} = 0 := by
  obtain ⟨i, x⟩ := z
  have e : {w : ℕ × ℝ | w.2 < x - d} = Prod.snd ⁻¹' {w | w < x - d} := rfl
  have hB : MeasurableSet {w : ℝ | w < x - d} := measurableSet_lt measurable_id measurable_const
  rw [e, ladderChainKernel_snd_preimage _ _ _ _ hB]
  simp [hΛ, hΛs]

/-- The moves `⌊x⌋₊ ± 1` go down by at most `2`. -/
theorem twoPoint_Iio (a b : ℝ≥0∞) (x : ℝ) : twoPoint a b x {w | w < x - 2} = 0 := by
  have hup : ¬ exUp x < x - 2 := by
    have := Nat.lt_floor_add_one x
    rw [exUp]; push_cast; intro h; linarith
  have hdown : ¬ exDown x < x - 2 := by
    have := Nat.lt_floor_add_one x
    rw [exDown]
    rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h0 | hpos
    · rw [h0] at this ⊢; push_cast at this ⊢; intro h; linarith
    · rw [Nat.cast_sub hpos]; push_cast; intro h; linarith
  have hB : MeasurableSet {w : ℝ | w < x - 2} := measurableSet_lt measurable_id measurable_const
  rw [twoPoint_apply _ _ _ hB,
    indicator_of_notMem (s := {w : ℝ | w < x - 2}) hdown,
    indicator_of_notMem (s := {w : ℝ | w < x - 2}) hup]
  simp

/-- The kernels (19.78) go down by at most `2`. -/
theorem exLam_Iio (p q : ℝ) (k : ℕ) (x : ℝ) : exLam p q k x {w | w < x - 2} = 0 := by
  unfold exLam
  split_ifs
  · exact twoPoint_Iio _ _ x
  · exact twoPoint_Iio _ _ x
  · rfl

/-- **The bottom rung of the up-or-down ladder (19.78)–(19.79) is not petite** (cf. MT p. 506):
from `(0, x)` the position moves by at most `2` per step, so `[0] = 0 × X` is not petite, even
when the chain is positive (`exLadder_isPositive`). -/
theorem exLadder_rung_zero_not_petite {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    haveI := isMarkovKernel_exMarg hp0 hp1 hq0 hq1
    haveI := isMarkovKernel_avgLadderKernel (exLam p q)
    ¬ IsPetite (avgLadderKernel (exLam p q)) {z : ℕ × ℝ | z.1 = 0} := by
  have := isMarkovKernel_exMarg hp0 hp1 hq0 hq1
  have := isMarkovKernel_avgLadderKernel (exLam p q)
  refine not_isPetite_of_bounded_steps _ measurable_snd zero_le_two
    (ladderChainKernel_step_ge _ _ (exLam_Iio p q) fun i x => ?_) fun M => ⟨(0, M), ?_, le_rfl⟩
  · have hB : MeasurableSet {w : ℝ | w < x - 2} := measurableSet_lt measurable_id measurable_const
    rw [ladderStar, Kernel.sum_apply' _ _ hB]
    simp [exLam_Iio]
  · rfl

/-- **The bottom rung of (19.80)** (MT p. 506): `Λ*₀(x, x − 1) = r(1 − q)`,
`Λ*₀(x, x + 1) = (1 − r)(1 − q)`, `Λ*₁` as in (19.65), `Λ*ᵢ = 0` for `i ≥ 2`. -/
noncomputable def ex80Star (p q r : ℝ) (i : ℕ) : Kernel ℝ ℝ :=
  if i = 0 then twoPoint (ENNReal.ofReal (r * (1 - q))) (ENNReal.ofReal ((1 - r) * (1 - q)))
  else if i = 1 then twoPoint (ENNReal.ofReal (p * (1 - q))) (ENNReal.ofReal ((1 - p) * (1 - q)))
  else 0

/-- The total mass of `a δ_{x−1} + b δ_{x+1}` is `a + b`. -/
theorem twoPoint_univ (a b : ℝ≥0∞) (x : ℝ) : twoPoint a b x univ = a + b := by
  rw [twoPoint_apply _ _ _ MeasurableSet.univ]
  simp

/-- `ofReal(st) + ofReal((1 − s)t) = ofReal t` for `0 ≤ s ≤ 1`, `t ≥ 0`. -/
theorem ofReal_split {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) :
    ENNReal.ofReal (s * t) + ENNReal.ofReal ((1 - s) * t) = ENNReal.ofReal t := by
  rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg (by linarith) ht)]
  congr 1; ring

/-- The chain with bottom rung (19.80) is a Markov kernel. -/
theorem isMarkovKernel_ex80 {p q r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsMarkovKernel (ladderChainKernel (exLam p q) (ex80Star p q r)) := by
  have hq' : 0 ≤ 1 - q := by linarith
  have hA : ∀ k x, exLam p q k x univ =
      (if k = 0 then ENNReal.ofReal q else 0) + (if k = 2 then ENNReal.ofReal (1 - q) else 0) := by
    intro k x
    by_cases h0 : k = 0
    · subst h0; simp [exLam, twoPoint_univ, ofReal_split hp0 hp1 hq0]
    by_cases h2 : k = 2
    · subst h2; simp [exLam, twoPoint_univ, ofReal_split hp0 hp1 hq']
    simp [exLam, h0, h2]
  refine isMarkovKernel_ladderChainKernel _ _ fun i x => ?_
  simp_rw [hA]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  unfold ex80Star
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · simp [twoPoint_univ, ofReal_split hr0 hr1 hq', ← ENNReal.ofReal_add hq' hq0]
    · simp [twoPoint_univ, ofReal_split hp0 hp1 hq', ← ENNReal.ofReal_add hq' hq0]
  · simp [show i ≠ 0 by omega, show i ≠ 1 by omega, Finset.mem_range,
      show 2 < i + 1 by omega, ← ENNReal.ofReal_add hq0 hq']

/-- **`[0]` is not petite for the chain (19.80)** (MT p. 506): "here we have an example where
the set `[0]` is not petite". -/
theorem ex80_rung_zero_not_petite {p q r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    haveI := isMarkovKernel_ex80 hp0 hp1 hq0 hq1 hr0 hr1
    ¬ IsPetite (ladderChainKernel (exLam p q) (ex80Star p q r)) {z : ℕ × ℝ | z.1 = 0} := by
  have := isMarkovKernel_ex80 hp0 hp1 hq0 hq1 hr0 hr1
  refine not_isPetite_of_bounded_steps _ measurable_snd zero_le_two
    (ladderChainKernel_step_ge _ _ (exLam_Iio p q) fun i x => ?_) fun M => ⟨(0, M), ?_, le_rfl⟩
  · unfold ex80Star
    split_ifs
    · exact twoPoint_Iio _ _ x
    · exact twoPoint_Iio _ _ x
    · rfl
  · rfl


end MeynTweedie.GeneralizedDrift

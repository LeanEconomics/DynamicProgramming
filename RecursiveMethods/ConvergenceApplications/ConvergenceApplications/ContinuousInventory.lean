/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.ConditionM
import ConvergenceApplications.FellerInvariant

/-!
# A continuous-state (s, S) inventory process

SLP §13.2, pp. 390–391, Exercise 13.2. Demand `z` has distribution `μ` (a probability measure on
`ℝ`, in the book concentrated on `Z = [0, z̄]`), and `0 ≤ s < S`. Inventories follow the law of
motion (1), p. 391 (`invLaw`): `x′ = max(x − z, 0)` if `x > s` and `x′ = max(S − z, 0)` if
`x ≤ s`. The transition function is `P(x, A) = μ({z : x′(x, z) ∈ A})` (`invKernel`, on the state
space `ℝ`; it never leaves `X = [0, ∞)`, `invKernel_Iio_zero`, `invKernel_Ici_zero`), and
`invKernelIcc` is the same process on the state space `[0, S]` (`invLawIcc_val`: for `z ≥ 0` the
law maps `[0, S]` into itself).

## Exercise 13.2a (p. 391)

* `ex_13_2a_markov`: `P` is a transition function (Markov kernel).
* `ex_13_2a_Icc_of_lt`, `ex_13_2a_Icc_of_le`: for `0 < a₁`, `P(x, [a₁, a₂]) = μ([x − a₂, x − a₁])`
  if `x > s` and `μ([S − a₂, S − a₁])` if `x ≤ s`.
* `ex_13_2a_zero_of_lt`, `ex_13_2a_zero_of_le`: `P(x, {0}) = μ([x, ∞))` if `x > s` and `μ([S, ∞))`
  if `x ≤ s` (the book's `μ([x, z̄])`, `μ([S, z̄])`).
* `ex_13_2a_determined` (via `measure_eq_of_intervals`): these interval values suffice — a
  finite kernel without mass on `(−∞, 0)` that agrees with them on `{0}` and on all `[a₁, a₂]`,
  `0 < a₁ ≤ a₂`, is `P`.
* `ex_13_2a_not_feller`: `P` is not Feller in general (`μ = δ₀`, `s = 1`, `S = 2`; `Tf` jumps at
  `x = s = 1` for `f(y) = max(min(y, 2), 0)`).

## Exercise 13.2b (p. 391)

* `ex_13_2b` (corrected, `N = 1`): `P(x, {0}) ≥ μ([S, ∞))` for all `x ≤ S`.
* `ex_13_2b_of_density`: a density lower bound `μ((a, b]) ≥ α(b − a)` on `[0, z̄]` with `S < z̄`
  gives `μ([S, ∞)) > 0`.
* `ex_13_2b_conditionMFor`, `ex_13_2b_conditionM`: on `[0, S]`, `μ([S, ∞)) > 0` gives Condition M
  for `(1, μ([S, ∞)))`, and Conditions M and D via Exercises 11.5a and 11.4c.
* `ex_13_2b_invariant` (the text on p. 391, Theorem 11.12 on `[0, S]`): if `μ([S, ∞)) > 0`, there
  is a unique invariant probability measure `λ*` on `[0, S]` and
  `‖T*ⁿλ₀ − λ*‖ ≤ 2(1 − μ([S, ∞)))ⁿ` for every initial `λ₀` on `[0, S]`.
* `ex_13_2_zero_unreachable`, `ex_13_2_zero_unreachable_kpow`, `ex_13_2b_fails_of_zbar_le_s`
  ("why `s < z̄`?", p. 391): if demand lives on `[0, z̄]` and `z̄ ≤ s < S`, then `Pᴺ(x, {0}) = 0`
  for all `N ≥ 1` and `x`, so Exercise 13.2b fails outright.
* `ex_13_2_invariant_null_above` (p. 391, "`(S, ∞)` is transient", corrected): if `μ(−∞, 0) = 0`
  and `μ((0, ∞)) > 0`, every invariant finite measure gives zero mass to `(S, ∞)`.

## Corrections

* **Exercise 13.2b is false without a condition on `μ`** (p. 391). `ex_13_2b_counterexample`:
  `z̄ = 3`, `μ = δ₁`, `s = 1/2`, `S = 2` (so `s, S < z̄`); the chain alternates `0 ↦ 1 ↦ 0`, so for
  every `N ≥ 1` either `Pᴺ(0, {0}) = 0` or `Pᴺ(1, {0}) = 0`. In the same example Condition M fails
  on `[0, S]` (`ex_13_2b_counterexample_conditionM`) and `T*ⁿδ₀` alternates between `δ₀` and `δ₁`,
  so it converges neither setwise on `{0}`, nor weakly, nor in total variation
  (`ex_13_2b_not_convergent`), contradicting the convergence claim of p. 391. The fix: assume
  `μ([S, ∞)) > 0` (e.g. a density lower bound with `S < z̄`); then `N = 1` works (`ex_13_2b`). The
  manual's proof tacitly assumes this.
* **"`(S, ∞)` is transient"** (p. 391) needs `μ((0, z̄]) > 0`. `ex_13_2_not_transient`: with
  `μ = δ₀`, every `x > s` is absorbing, and for `x > S`, `δ_x` is an invariant probability measure
  concentrated on `(S, ∞)`. Under `μ((0, ∞)) > 0` the claim holds
  (`ex_13_2_invariant_null_above`).
* The book's formulas `μ([x, z̄])` are written here `μ([x, ∞))`, which agrees when `μ` lives on
  `[0, z̄]` and needs no such assumption.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BoundedContinuousFunction

/-! ### The law of motion and the transition function -/

/-- The `(s, S)` law of motion (1), p. 391: next period's inventory `x′` given the current
inventory `x` and demand `z`. -/
noncomputable def invLaw (s S x z : ℝ) : ℝ := if s < x then max (x - z) 0 else max (S - z) 0

/-- The law of motion is jointly Borel in `(x, z)`. -/
theorem measurable_invLaw (s S : ℝ) : Measurable fun p : ℝ × ℝ => invLaw s S p.1 p.2 := by
  unfold invLaw
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) (by fun_prop)
    (by fun_prop)

/-- For fixed `z`, the law of motion is Borel in `x`. -/
theorem measurable_invLaw_left (s S z : ℝ) : Measurable fun x => invLaw s S x z :=
  (measurable_invLaw s S).comp (measurable_id.prodMk measurable_const)

/-- For fixed `x`, the law of motion is Borel in `z`. -/
theorem measurable_invLaw_right (s S x : ℝ) : Measurable (invLaw s S x) :=
  (measurable_invLaw s S).comp measurable_prodMk_left

/-- The **transition function** of Exercise 13.2a (p. 391) on the state space `ℝ`:
`P(x, A) = μ({z : x′(x, z) ∈ A})`, the law of `x′` when demand has distribution `μ`. -/
noncomputable def invKernel (μ : Measure ℝ) [SFinite μ] (s S : ℝ) : Kernel ℝ ℝ where
  toFun x := μ.map (invLaw s S x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp_rw [Measure.map_apply (measurable_invLaw_right s S _) hA]
    exact measurable_measure_prodMk_left (measurable_invLaw s S hA)

/-- `P(x, ·)` is the image of `μ` under `z ↦ x′(x, z)`. -/
theorem invKernel_apply (μ : Measure ℝ) [SFinite μ] (s S x : ℝ) :
    invKernel μ s S x = μ.map (invLaw s S x) := rfl

/-- `P(x, A) = μ({z : x′(x, z) ∈ A})` for Borel `A`. -/
theorem invKernel_apply' (μ : Measure ℝ) [SFinite μ] (s S x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) : invKernel μ s S x A = μ (invLaw s S x ⁻¹' A) := by
  rw [invKernel_apply, Measure.map_apply (measurable_invLaw_right s S x) hA]

/-- **Exercise 13.2a.** `P` is a transition function (a Markov kernel). -/
theorem ex_13_2a_markov (μ : Measure ℝ) [IsProbabilityMeasure μ] (s S : ℝ) :
    IsMarkovKernel (invKernel μ s S) :=
  ⟨fun x => (Measure.isProbabilityMeasure_map_iff
    (measurable_invLaw_right s S x).aemeasurable).2 inferInstance⟩

/-- The process lives on `X = [0, ∞)`: `P(x, [0, ∞)) = 1`. -/
theorem invKernel_Ici_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (s S x : ℝ) :
    invKernel μ s S x (Ici 0) = 1 := by
  rw [invKernel_apply' _ _ _ _ measurableSet_Ici]
  have : invLaw s S x ⁻¹' Ici 0 = univ := by
    ext z
    simp only [mem_preimage, mem_Ici, mem_univ, iff_true, invLaw]
    split_ifs <;> exact le_max_right _ _
  rw [this, measure_univ]

/-- **Exercise 13.2a**, interval formula above `s`: for `0 < a₁`, if `x > s` then
`P(x, [a₁, a₂]) = μ([x − a₂, x − a₁])`. -/
theorem ex_13_2a_Icc_of_lt (μ : Measure ℝ) [SFinite μ] {s S x a₁ a₂ : ℝ} (hx : s < x)
    (ha : 0 < a₁) : invKernel μ s S x (Icc a₁ a₂) = μ (Icc (x - a₂) (x - a₁)) := by
  rw [invKernel_apply' _ _ _ _ measurableSet_Icc]
  congr 1
  ext z
  simp only [mem_preimage, mem_Icc, invLaw, hx, ↓reduceIte]
  rcases le_total (x - z) 0 with h | h
  · rw [max_eq_right h]
    constructor <;> rintro ⟨h1, h2⟩ <;> exfalso <;> linarith
  · rw [max_eq_left h]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Exercise 13.2a**, interval formula at or below `s`: for `0 < a₁`, if `x ≤ s` then
`P(x, [a₁, a₂]) = μ([S − a₂, S − a₁])`. -/
theorem ex_13_2a_Icc_of_le (μ : Measure ℝ) [SFinite μ] {s S x a₁ a₂ : ℝ} (hx : x ≤ s)
    (ha : 0 < a₁) : invKernel μ s S x (Icc a₁ a₂) = μ (Icc (S - a₂) (S - a₁)) := by
  rw [invKernel_apply' _ _ _ _ measurableSet_Icc]
  congr 1
  ext z
  simp only [mem_preimage, mem_Icc, invLaw, not_lt.2 hx, ↓reduceIte]
  rcases le_total (S - z) 0 with h | h
  · rw [max_eq_right h]
    constructor <;> rintro ⟨h1, h2⟩ <;> exfalso <;> linarith
  · rw [max_eq_left h]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Exercise 13.2a**, the atom at zero above `s`: if `x > s` then `P(x, {0}) = μ([x, ∞))`
(the book's `μ([x, z̄])`). -/
theorem ex_13_2a_zero_of_lt (μ : Measure ℝ) [SFinite μ] {s S x : ℝ} (hx : s < x) :
    invKernel μ s S x {0} = μ (Ici x) := by
  rw [invKernel_apply' _ _ _ _ (measurableSet_singleton 0)]
  congr 1
  ext z
  simp only [mem_preimage, mem_singleton_iff, mem_Ici, invLaw, hx, ↓reduceIte]
  rw [max_eq_right_iff]
  constructor <;> intro h <;> linarith

/-- **Exercise 13.2a**, the atom at zero at or below `s`: if `x ≤ s` then
`P(x, {0}) = μ([S, ∞))` (the book's `μ([S, z̄])`). -/
theorem ex_13_2a_zero_of_le (μ : Measure ℝ) [SFinite μ] {s S x : ℝ} (hx : x ≤ s) :
    invKernel μ s S x {0} = μ (Ici S) := by
  rw [invKernel_apply' _ _ _ _ (measurableSet_singleton 0)]
  congr 1
  ext z
  simp only [mem_preimage, mem_singleton_iff, mem_Ici, invLaw, not_lt.2 hx, ↓reduceIte]
  rw [max_eq_right_iff]
  constructor <;> intro h <;> linarith

/-- The process never goes below zero: `P(x, (−∞, 0)) = 0`. -/
theorem invKernel_Iio_zero (μ : Measure ℝ) [SFinite μ] (s S x : ℝ) :
    invKernel μ s S x (Iio 0) = 0 := by
  rw [invKernel_apply' _ _ _ _ measurableSet_Iio]
  have : invLaw s S x ⁻¹' Iio 0 = ∅ := by
    ext z
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt, invLaw]
    split_ifs <;> exact le_max_right _ _
  rw [this, measure_empty]

/-- A finite measure on `ℝ` with no mass on `(−∞, 0)` is determined by its values on `{0}` and
on the closed intervals `[a₁, a₂]` with `0 < a₁ ≤ a₂`. -/
theorem measure_eq_of_intervals {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : ν₁ (Iio 0) = 0) (h₂ : ν₂ (Iio 0) = 0) (h0 : ν₁ {0} = ν₂ {0})
    (hI : ∀ a₁ a₂, 0 < a₁ → a₁ ≤ a₂ → ν₁ (Icc a₁ a₂) = ν₂ (Icc a₁ a₂)) : ν₁ = ν₂ := by
  have hIoc : ∀ b, 0 < b → ν₁ (Ioc 0 b) = ν₂ (Ioc 0 b) := by
    intro b hb
    have hU : Ioc 0 b = ⋃ n : ℕ, Icc (b / (n + 1)) b := by
      ext y
      simp only [mem_Ioc, mem_iUnion, mem_Icc]
      constructor
      · rintro ⟨hy0, hyb⟩
        obtain ⟨n, hn⟩ := exists_nat_gt (b / y)
        refine ⟨n, ?_, hyb⟩
        rw [div_le_iff₀ (by positivity)]
        have := (div_lt_iff₀ hy0).1 hn
        nlinarith
      · rintro ⟨n, h1, h2⟩
        exact ⟨lt_of_lt_of_le (by positivity) h1, h2⟩
    have hmono : Monotone fun n : ℕ => Icc (b / (n + 1)) b := by
      intro m n hmn
      refine Icc_subset_Icc_left (div_le_div_of_nonneg_left hb.le (by positivity) ?_)
      exact_mod_cast Nat.succ_le_succ hmn
    rw [hU, hmono.measure_iUnion, hmono.measure_iUnion]
    congr 1
    funext n
    refine hI _ _ (by positivity) (div_le_self hb.le ?_)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsplit : ∀ ν : Measure ℝ, ν (Iio 0) = 0 → ∀ a b, a ≤ 0 → 0 ≤ b →
      ν (Icc a b) = ν {0} + ν (Ioc 0 b) := by
    intro ν hν a b ha hb
    have hset : Icc a b = Ico a 0 ∪ ({0} ∪ Ioc 0 b) := by
      ext y
      simp only [mem_Icc, mem_union, mem_Ico, mem_singleton_iff, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_trichotomy y 0 with h | h | h
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨h, h2⟩)
      · rintro (⟨h1, h2⟩ | h | ⟨h1, h2⟩)
        · exact ⟨h1, by linarith⟩
        · exact ⟨by linarith, by linarith⟩
        · exact ⟨by linarith, h2⟩
    have hnull : ν (Ico a 0) = 0 := measure_mono_null Ico_subset_Iio_self hν
    have hd1 : Disjoint (Ico a 0) ({0} ∪ Ioc 0 b) := by
      refine Set.disjoint_left.2 fun y hy1 hy2 => ?_
      rcases hy2 with hy | hy
      · exact absurd hy1.2 (by rw [mem_singleton_iff.1 hy]; exact lt_irrefl 0)
      · exact absurd hy1.2 (not_lt.2 hy.1.le)
    have hd2 : Disjoint ({0} : Set ℝ) (Ioc 0 b) :=
      disjoint_singleton_left.2 fun h => lt_irrefl _ h.1
    rw [hset, measure_union hd1 ((measurableSet_singleton 0).union measurableSet_Ioc), hnull,
      zero_add, measure_union hd2 measurableSet_Ioc]
  refine Measure.ext_of_Icc ν₁ ν₂ fun a b hab => ?_
  rcases lt_or_ge b 0 with hb | hb
  · rw [measure_mono_null (Icc_subset_Iio_iff hab |>.2 hb) h₁,
      measure_mono_null (Icc_subset_Iio_iff hab |>.2 hb) h₂]
  rcases lt_or_ge 0 a with ha | ha
  · exact hI a b ha hab
  rw [hsplit ν₁ h₁ a b ha hb, hsplit ν₂ h₂ a b ha hb, h0]
  rcases hb.eq_or_lt with hb0 | hb0
  · rw [← hb0, Ioc_self, measure_empty, measure_empty]
  · rw [hIoc b hb0]

/-- **Exercise 13.2a** ("this suffices to define a transition function"): a finite kernel on `ℝ`
with no mass on `(−∞, 0)` that has the interval values of `P` on `{0}` and on every `[a₁, a₂]`
with `0 < a₁ ≤ a₂` is `P`. -/
theorem ex_13_2a_determined (μ : Measure ℝ) [IsProbabilityMeasure μ] (s S : ℝ) (Q : Kernel ℝ ℝ)
    [IsFiniteKernel Q] (hQ0 : ∀ x, Q x (Iio 0) = 0)
    (hQI : ∀ x a₁ a₂, 0 < a₁ → a₁ ≤ a₂ → Q x (Icc a₁ a₂) =
      if s < x then μ (Icc (x - a₂) (x - a₁)) else μ (Icc (S - a₂) (S - a₁)))
    (hQz : ∀ x, Q x {0} = if s < x then μ (Ici x) else μ (Ici S)) : Q = invKernel μ s S := by
  have := ex_13_2a_markov μ s S
  ext1 x
  refine measure_eq_of_intervals (hQ0 x) (invKernel_Iio_zero μ s S x) ?_ fun a₁ a₂ ha _ => ?_
  · rw [hQz]
    split_ifs with hx
    · exact (ex_13_2a_zero_of_lt μ hx).symm
    · exact (ex_13_2a_zero_of_le μ (not_lt.1 hx)).symm
  · rw [hQI x a₁ a₂ ha ‹_›]
    split_ifs with hx
    · exact (ex_13_2a_Icc_of_lt μ hx ha).symm
    · exact (ex_13_2a_Icc_of_le μ (not_lt.1 hx) ha).symm

/-! ### The Feller property fails -/

/-- **Exercise 13.2a** (Feller): `P` does **not** have the Feller property in general. With
no demand (`μ = δ₀`), `s = 1` and `S = 2`, `P(x, ·) = δ_x` for `x > 1` and `δ₂` for `x ≤ 1`. For
the bounded continuous `f(y) = max(min(y, 2), 0)`, `Tf(x) = f(x) → 1` as `x ↓ 1`, but
`Tf(1) = f(2) = 2`. -/
theorem ex_13_2a_not_feller : ¬ IsFeller (invKernel (Measure.dirac 0) 1 2) := by
  intro hF
  set f : ℝ → ℝ := fun y => max (min y 2) 0 with hf_def
  have hfc : Continuous f := by fun_prop
  have hfb : ∃ M, ∀ y, |f y| ≤ M := ⟨2, fun y => by
    rw [abs_le]
    constructor
    · exact (by norm_num : (-2 : ℝ) ≤ 0).trans (le_max_right _ _)
    · exact max_le (min_le_right _ _) (by norm_num)⟩
  have hT : ∀ x, markovOpR (invKernel (Measure.dirac 0) 1 2) f x = f (invLaw 1 2 x 0) := by
    intro x
    rw [markovOpR, invKernel_apply, Measure.map_dirac' (measurable_invLaw_right _ _ _)]
    exact integral_dirac _ _
  have hc := hF f hfc hfb
  have h1 : markovOpR (invKernel (Measure.dirac 0) 1 2) f 1 = 2 := by
    rw [hT]
    norm_num [invLaw, f]
  have hlim : Tendsto (markovOpR (invKernel (Measure.dirac 0) 1 2) f) (𝓝[>] 1) (𝓝 1) := by
    have h := (hfc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    have hf1 : f 1 = 1 := by norm_num [f]
    rw [hf1] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hT]
    have hx' : (1 : ℝ) < x := hx
    simp only [invLaw, hx', ↓reduceIte, sub_zero]
    rw [max_eq_left (by linarith)]
  have := tendsto_nhds_unique hlim ((hc.tendsto 1).mono_left nhdsWithin_le_nhds)
  rw [h1] at this
  norm_num at this

/-! ### Exercise 13.2b: the counterexample -/

/-- A map swapping two points: `fⁿ(a) = a` for `n` even and `b` for `n` odd. -/
theorem iterate_of_swap {α : Type*} {f : α → α} {a b : α} (hab : f a = b) (hba : f b = a)
    (n : ℕ) : f^[n] a = (if Even n then a else b) ∧ f^[n] b = (if Even n then b else a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1, ih.2]
    by_cases hn : Even n
    · simp [hn, Nat.even_add_one, hab, hba]
    · simp [hn, Nat.even_add_one, hab, hba]

/-- With deterministic demand `z₀` (`μ = δ_{z₀}`) the transition function is deterministic:
`P(x, ·) = δ_{x′(x, z₀)}`. -/
theorem invKernel_dirac (s S z₀ : ℝ) :
    invKernel (Measure.dirac z₀) s S =
      Kernel.deterministic (fun x => invLaw s S x z₀) (measurable_invLaw_left s S z₀) := by
  ext1 x
  rw [invKernel_apply, Measure.map_dirac' (measurable_invLaw_right _ _ _),
    Kernel.deterministic_apply]

/-- In the counterexample (`μ = δ₁`, `s = 1/2`, `S = 2`) the chain alternates `0 ↦ 1 ↦ 0`:
`Pⁿ(0, ·) = δ₀` for `n` even and `δ₁` for `n` odd, and the reverse from `1`. -/
theorem kpow_invKernel_dirac_one (n : ℕ) :
    kpow (invKernel (Measure.dirac 1) (1 / 2) 2) n 0 =
        Measure.dirac (if Even n then 0 else 1) ∧
      kpow (invKernel (Measure.dirac 1) (1 / 2) 2) n 1 =
        Measure.dirac (if Even n then 1 else 0) := by
  rw [invKernel_dirac, kpow_deterministic, kpow_deterministic]
  obtain ⟨h0, h1⟩ := iterate_of_swap (f := fun x => invLaw (1 / 2) 2 x 1) (a := 0) (b := 1)
    (by norm_num [invLaw]) (by norm_num [invLaw]) n
  rw [h0, h1]
  exact ⟨rfl, rfl⟩

/-- `δ_y({0}) = 0` for `y = 1`, and `= 1` for `y = 0`. -/
theorem dirac_real_zero_one : (Measure.dirac (1 : ℝ)).real {0} = 0 ∧
    (Measure.dirac (0 : ℝ)).real {0} = 1 := by
  simp [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ))]

/-- **Correction to Exercise 13.2b** (p. 391): the claim fails without a condition on `μ`. With
`z̄ = 3`, `μ = δ₁` (concentrated on `[0, z̄]`), `s = 1/2 < z̄` and `S = 2 < z̄`, there are no
`N ≥ 1` and `ε > 0` with `Pᴺ(x, {0}) ≥ ε` for all `x ∈ [0, S]`: `Pᴺ(1, {0}) = 0` for `N` even and
`Pᴺ(0, {0}) = 0` for `N` odd. -/
theorem ex_13_2b_counterexample :
    Measure.dirac (1 : ℝ) (Icc 0 3)ᶜ = 0 ∧ (1 / 2 : ℝ) < 3 ∧ (2 : ℝ) < 3 ∧
      ¬ ∃ N : ℕ, 1 ≤ N ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Icc (0 : ℝ) 2,
        ε ≤ (kpow (invKernel (Measure.dirac 1) (1 / 2) 2) N x).real {0} := by
  refine ⟨?_, by norm_num, by norm_num, ?_⟩
  · rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
    norm_num
  rintro ⟨N, -, ε, hε, h⟩
  by_cases hN : Even N
  · have := h 1 ⟨by norm_num, by norm_num⟩
    rw [(kpow_invKernel_dirac_one N).2] at this
    simp only [hN, ↓reduceIte, dirac_real_zero_one.1] at this
    linarith
  · have := h 0 ⟨le_rfl, by norm_num⟩
    rw [(kpow_invKernel_dirac_one N).1] at this
    simp only [hN, ↓reduceIte, dirac_real_zero_one.1] at this
    linarith

/-- A real sequence taking the value `p` at even and `q ≠ p` at odd indices does not converge. -/
theorem not_tendsto_of_alternating {u : ℕ → ℝ} {p q : ℝ} (hpq : p ≠ q)
    (hp : ∀ n, u (2 * n) = p) (hq : ∀ n, u (2 * n + 1) = q) :
    ¬ ∃ c, Tendsto u atTop (𝓝 c) := by
  rintro ⟨c, hc⟩
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have h3 : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have hcp := tendsto_nhds_unique (hc.comp h2)
    (tendsto_const_nhds.congr fun n => (hp n).symm)
  have hcq := tendsto_nhds_unique (hc.comp h3)
    (tendsto_const_nhds.congr fun n => (hq n).symm)
  exact hpq (hcp.symm.trans hcq)

/-- In the counterexample, `T*ⁿδ₀ = δ₀` for `n` even and `δ₁` for `n` odd. -/
theorem adjointOp_invKernel_dirac_one (n : ℕ) :
    adjointOp (kpow (invKernel (Measure.dirac 1) (1 / 2) 2) n) (Measure.dirac 0) =
      Measure.dirac (if Even n then 0 else 1) := by
  rw [adjointOp, Measure.dirac_bind (kpow _ n).measurable, (kpow_invKernel_dirac_one n).1]

/-- **Correction to the text after Exercise 13.2a** (p. 391, `T*ⁿλ → λ*` for every `λ`): in the
counterexample of `ex_13_2b_counterexample`, `T*ⁿδ₀` alternates between `δ₀` and `δ₁`, so it does
not converge setwise on `{0}`, nor weakly, nor in total variation, to any limit. -/
theorem ex_13_2b_not_convergent :
    (¬ ∃ c : ℝ, Tendsto (fun n => (adjointOp (kpow (invKernel (Measure.dirac 1) (1 / 2) 2) n)
      (Measure.dirac 0)).real {0}) atTop (𝓝 c)) ∧
    (¬ ∃ l : Measure ℝ, ConvWeak (fun n => adjointOp (kpow (invKernel (Measure.dirac 1) (1 / 2) 2)
      n) (Measure.dirac 0)) l) ∧
    ¬ ∃ l : Measure ℝ, IsProbabilityMeasure l ∧ Tendsto (fun n => tvDist (adjointOp
      (kpow (invKernel (Measure.dirac 1) (1 / 2) 2) n) (Measure.dirac 0)) l) atTop (𝓝 0) := by
  simp_rw [adjointOp_invKernel_dirac_one]
  have hset : ¬ ∃ c : ℝ, Tendsto (fun n : ℕ => (Measure.dirac
      (if Even n then (0 : ℝ) else 1)).real {0}) atTop (𝓝 c) := by
    refine not_tendsto_of_alternating (p := 1) (q := 0) one_ne_zero (fun n => ?_) fun n => ?_
    · simp only [even_two_mul, ↓reduceIte, dirac_real_zero_one.2]
    · simp only [Nat.not_even_two_mul_add_one, ↓reduceIte, dirac_real_zero_one.1]
  refine ⟨hset, ?_, ?_⟩
  · rintro ⟨l, hl⟩
    set g : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun y => max (min y 1) 0) (by fun_prop) 1 fun y => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (le_max_right _ _),
          max_le (min_le_right _ _) zero_le_one⟩
    refine not_tendsto_of_alternating (u := fun n : ℕ => ∫ y, g y ∂Measure.dirac
      (if Even n then (0 : ℝ) else 1)) (p := 0) (q := 1) zero_ne_one (fun n => ?_)
      (fun n => ?_) ⟨_, hl g⟩
    · simp [g]
    · simp [g]
  · rintro ⟨l, hl, htv⟩
    refine hset ⟨l.real {0}, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    have h2 : Tendsto (fun n : ℕ => tvDist (Measure.dirac (if Even n then (0 : ℝ) else 1)) l / 2)
        atTop (𝓝 0) := by simpa using htv.div_const 2
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h2
    rw [Real.dist_eq]
    have := two_abs_le_tvDist (Measure.dirac (if Even n then (0 : ℝ) else 1)) l
      (measurableSet_singleton 0)
    linarith

/-! ### Why `s < z̄` -/

/-- **"Why `s < z̄`?"** (p. 391): if demand is concentrated on `[0, z̄]` and `z̄ ≤ s < S`, then
`P(x, {0}) = 0` for every `x`: above `s`, `x − z > s − z̄ ≥ 0`; after an order, `S − z > 0`. -/
theorem ex_13_2_zero_unreachable (μ : Measure ℝ) [SFinite μ] {s S zbar : ℝ}
    (hμ : μ (Icc 0 zbar)ᶜ = 0) (hs : zbar ≤ s) (hsS : s < S) (x : ℝ) :
    invKernel μ s S x {0} = 0 := by
  by_cases hx : s < x
  · rw [ex_13_2a_zero_of_lt μ hx]
    have hsub : Ici x ⊆ (Icc 0 zbar)ᶜ := fun z hz hz' => by
      have := hz'.2
      have := mem_Ici.1 hz
      linarith
    exact measure_mono_null hsub hμ
  · rw [ex_13_2a_zero_of_le μ (not_lt.1 hx)]
    have hsub : Ici S ⊆ (Icc 0 zbar)ᶜ := fun z hz hz' => by
      have := hz'.2
      have := mem_Ici.1 hz
      linarith
    exact measure_mono_null hsub hμ

/-- If `z̄ ≤ s < S`, then `Pᴺ(x, {0}) = 0` for all `N ≥ 1` and all `x`. -/
theorem ex_13_2_zero_unreachable_kpow (μ : Measure ℝ) [SFinite μ] {s S zbar : ℝ}
    (hμ : μ (Icc 0 zbar)ᶜ = 0) (hs : zbar ≤ s) (hsS : s < S) {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    kpow (invKernel μ s S) N x {0} = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [kpow_add, Kernel.comp_apply' _ _ _ (measurableSet_singleton 0), kpow_one]
  simp [ex_13_2_zero_unreachable μ hμ hs hsS]

/-- **Exercise 13.2b fails outright when `s ≥ z̄`**: with demand concentrated on `[0, z̄]` and
`0 ≤ z̄ ≤ s < S`, there are no `N ≥ 1` and `ε > 0` with `Pᴺ(x, {0}) ≥ ε` on `[0, S]`. -/
theorem ex_13_2b_fails_of_zbar_le_s (μ : Measure ℝ) [SFinite μ] {s S zbar : ℝ}
    (hμ : μ (Icc 0 zbar)ᶜ = 0) (hz : 0 ≤ zbar) (hs : zbar ≤ s) (hsS : s < S) :
    ¬ ∃ N : ℕ, 1 ≤ N ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Icc (0 : ℝ) S,
      ε ≤ (kpow (invKernel μ s S) N x).real {0} := by
  rintro ⟨N, hN, ε, hε, h⟩
  have := h 0 ⟨le_rfl, by linarith⟩
  rw [measureReal_def, ex_13_2_zero_unreachable_kpow μ hμ hs hsS hN, ENNReal.toReal_zero] at this
  linarith

/-! ### Exercise 13.2b corrected -/

/-- **Exercise 13.2b, corrected** (`N = 1`): `P(x, {0}) ≥ μ([S, ∞))` for all `x ≤ S`, since
`μ([x, ∞)) ≥ μ([S, ∞))`. With `μ([S, ∞)) > 0` this is the claim of the book with `N = 1` and
`ε = μ([S, ∞))`. -/
theorem ex_13_2b (μ : Measure ℝ) [SFinite μ] (s S : ℝ) {x : ℝ} (hx : x ≤ S) :
    μ (Ici S) ≤ invKernel μ s S x {0} := by
  by_cases hxs : s < x
  · rw [ex_13_2a_zero_of_lt μ hxs]
    exact measure_mono (Ici_subset_Ici.2 hx)
  · rw [ex_13_2a_zero_of_le μ (not_lt.1 hxs)]

/-- A density lower bound `μ((a, b]) ≥ α(b − a)` on `[0, z̄]` (as (Z3), p. 392) with `0 ≤ S < z̄`
gives `μ([S, ∞)) ≥ α(z̄ − S) > 0`, so the corrected Exercise 13.2b applies. -/
theorem ex_13_2b_of_density (μ : Measure ℝ) [IsFiniteMeasure μ] {S zbar α : ℝ} (hα : 0 < α)
    (hS : 0 ≤ S) (hSz : S < zbar)
    (hd : ∀ a b, 0 ≤ a → a < b → b ≤ zbar → α * (b - a) ≤ μ.real (Ioc a b)) :
    0 < μ.real (Ici S) :=
  calc 0 < α * (zbar - S) := mul_pos hα (by linarith)
    _ ≤ μ.real (Ioc S zbar) := hd S zbar hS hSz le_rfl
    _ ≤ μ.real (Ici S) := measureReal_mono (Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self)

/-! ### The process on `[0, S]` -/

/-- The law of motion on the state space `[0, S]` (p. 391). For demand `z ≥ 0` it maps `[0, S]`
into itself (`invLawIcc_val`); the projection onto `[0, S]` only makes it total on the
`μ`-null set of negative demands. -/
noncomputable def invLawIcc (s S : ℝ) (hS : 0 ≤ S) (x : Icc (0 : ℝ) S) (z : ℝ) :
    Icc (0 : ℝ) S :=
  projIcc 0 S hS (invLaw s S x z)

/-- For `z ≥ 0` and `x ∈ [0, S]`, `x′(x, z) ∈ [0, S]`, so `invLawIcc` is the law (1). -/
theorem invLawIcc_val {s S : ℝ} (hS : 0 ≤ S) (x : Icc (0 : ℝ) S) {z : ℝ} (hz : 0 ≤ z) :
    (invLawIcc s S hS x z : ℝ) = invLaw s S x z := by
  have hmem : invLaw s S x z ∈ Icc 0 S := by
    have hx := x.2.2
    unfold invLaw
    split_ifs
    · exact ⟨le_max_right _ _, max_le (by linarith) hS⟩
    · exact ⟨le_max_right _ _, max_le (by linarith) hS⟩
  rw [invLawIcc, projIcc_of_mem hS hmem]

/-- `invLawIcc` is jointly Borel. -/
theorem measurable_invLawIcc (s S : ℝ) (hS : 0 ≤ S) :
    Measurable fun p : Icc (0 : ℝ) S × ℝ => invLawIcc s S hS p.1 p.2 :=
  continuous_projIcc.measurable.comp
    ((measurable_invLaw s S).comp (measurable_subtype_coe.prodMap measurable_id))

/-- For fixed `x`, `invLawIcc` is Borel in `z`. -/
theorem measurable_invLawIcc_right (s S : ℝ) (hS : 0 ≤ S) (x : Icc (0 : ℝ) S) :
    Measurable (invLawIcc s S hS x) :=
  (measurable_invLawIcc s S hS).comp measurable_prodMk_left

/-- The transition function of the `(s, S)` process on the state space `[0, S]`. -/
noncomputable def invKernelIcc (μ : Measure ℝ) [SFinite μ] (s S : ℝ) (hS : 0 ≤ S) :
    Kernel (Icc (0 : ℝ) S) (Icc (0 : ℝ) S) where
  toFun x := μ.map (invLawIcc s S hS x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have : (fun x => μ.map (invLawIcc s S hS x) A) =
        fun x => μ (Prod.mk x ⁻¹'
          ((fun p : Icc (0 : ℝ) S × ℝ => invLawIcc s S hS p.1 p.2) ⁻¹' A)) :=
      funext fun x => Measure.map_apply (measurable_invLawIcc_right s S hS x) hA
    rw [this]
    exact measurable_measure_prodMk_left (measurable_invLawIcc s S hS hA)

/-- `P` on `[0, S]` is a Markov kernel. -/
theorem isMarkovKernel_invKernelIcc (μ : Measure ℝ) [IsProbabilityMeasure μ] (s S : ℝ)
    (hS : 0 ≤ S) : IsMarkovKernel (invKernelIcc μ s S hS) :=
  ⟨fun x => (Measure.isProbabilityMeasure_map_iff
    (measurable_invLawIcc_right s S hS x).aemeasurable).2 inferInstance⟩

/-- On `[0, S]`: `P(x, {0}) ≥ μ([S, ∞))` for every `x`. -/
theorem invKernelIcc_zero_ge (μ : Measure ℝ) [SFinite μ] (s S : ℝ) (hS : 0 ≤ S)
    (x : Icc (0 : ℝ) S) : μ (Ici S) ≤ invKernelIcc μ s S hS x {⟨0, left_mem_Icc.2 hS⟩} := by
  change μ (Ici S) ≤ μ.map (invLawIcc s S hS x) _
  rw [Measure.map_apply (measurable_invLawIcc_right s S hS x) (measurableSet_singleton _)]
  refine measure_mono fun z hz => ?_
  have hz' : S ≤ z := hz
  have hx := x.2.2
  have hle : invLaw s S x z ≤ 0 := by
    unfold invLaw
    split_ifs
    · exact max_le (by linarith) le_rfl
    · exact max_le (by linarith) le_rfl
  exact projIcc_of_le_left hS hle

/-- **Exercise 13.2b, corrected, on `[0, S]`**: if `μ([S, ∞)) > 0`, Condition M holds for
`(N, ε) = (1, μ([S, ∞)))`. -/
theorem ex_13_2b_conditionMFor (μ : Measure ℝ) [IsProbabilityMeasure μ] (s S : ℝ)
    (hS : 0 ≤ S) (hpos : 0 < μ.real (Ici S)) :
    ConditionMFor (invKernelIcc μ s S hS) 1 (μ.real (Ici S)) := by
  have := isMarkovKernel_invKernelIcc μ s S hS
  refine ⟨le_rfl, hpos, fun A hA => ?_⟩
  rw [kpow_one]
  have hb : ∀ x, μ.real (Ici S) ≤ (invKernelIcc μ s S hS x).real {⟨0, left_mem_Icc.2 hS⟩} :=
    fun x => ENNReal.toReal_mono (measure_ne_top _ _) (invKernelIcc_zero_ge μ s S hS x)
  by_cases h0 : (⟨0, left_mem_Icc.2 hS⟩ : Icc (0 : ℝ) S) ∈ A
  · exact Or.inl fun x => (hb x).trans (measureReal_mono (singleton_subset_iff.2 h0))
  · exact Or.inr fun x => (hb x).trans (measureReal_mono (singleton_subset_iff.2 h0))

/-- On `[0, S]`, with `μ([S, ∞)) > 0`, Condition M (Exercise 11.5a for 11.4c) and Condition D
(Exercise 11.4c) hold. -/
theorem ex_13_2b_conditionM (μ : Measure ℝ) [IsProbabilityMeasure μ] (s S : ℝ) (hS : 0 ≤ S)
    (hpos : 0 < μ.real (Ici S)) :
    ConditionM (invKernelIcc μ s S hS) ∧ ConditionD (invKernelIcc μ s S hS) := by
  have := isMarkovKernel_invKernelIcc μ s S hS
  have h : ∀ x, μ.real (Ici S) / 2 <
      (kpow (invKernelIcc μ s S hS) 1 x).real {⟨0, left_mem_Icc.2 hS⟩} := fun x => by
    rw [kpow_one]
    exact (half_lt_self hpos).trans_le
      (ENNReal.toReal_mono (measure_ne_top _ _) (invKernelIcc_zero_ge μ s S hS x))
  exact ⟨ex_11_5a_c le_rfl (half_pos hpos) h, ex_11_4c le_rfl (half_pos hpos) h⟩

/-- **The (s, S) process on `[0, S]`** (p. 391, Theorem 11.12 via Exercise 13.2b, corrected).
If `μ([S, ∞)) > 0`, there is a unique invariant probability measure `λ*` on `[0, S]`, and for every
initial probability measure `λ₀` on `[0, S]`, `‖T*ⁿλ₀ − λ*‖ ≤ 2(1 − μ([S, ∞)))ⁿ`. -/
theorem ex_13_2b_invariant (μ : Measure ℝ) [IsProbabilityMeasure μ] (s S : ℝ) (hS : 0 ≤ S)
    (hpos : 0 < μ.real (Ici S)) :
    ∃ lstar : Measure (Icc (0 : ℝ) S), IsProbabilityMeasure lstar ∧
      adjointOp (invKernelIcc μ s S hS) lstar = lstar ∧
      (∀ l : Measure (Icc (0 : ℝ) S), IsProbabilityMeasure l →
        adjointOp (invKernelIcc μ s S hS) l = l → l = lstar) ∧
      ∀ (l₀ : Measure (Icc (0 : ℝ) S)) [IsProbabilityMeasure l₀] (n : ℕ),
        tvDist (adjointOp (kpow (invKernelIcc μ s S hS) n) l₀) lstar ≤
          2 * (1 - μ.real (Ici S)) ^ n := by
  have := isMarkovKernel_invKernelIcc μ s S hS
  have : Nonempty (Icc (0 : ℝ) S) := ⟨⟨0, left_mem_Icc.2 hS⟩⟩
  obtain ⟨lstar, hlp, -, -, hinv, hconv⟩ := theorem_11_12 (ex_13_2b_conditionMFor μ s S hS hpos)
  simp only [Nat.div_one] at hconv
  refine ⟨lstar, hlp, hinv, fun l hl hlinv => ?_, hconv⟩
  have hfix : ∀ n, adjointOp (kpow (invKernelIcc μ s S hS) n) l = l := fun n => by
    rw [← adjointOp_iterate, Function.iterate_fixed hlinv]
  have hle1 : μ.real (Ici S) ≤ 1 := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hlim : Tendsto (fun n : ℕ => 2 * (1 - μ.real (Ici S)) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).const_mul
      (2 : ℝ)
  refine eq_of_tvDist_eq_zero (ge_of_tendsto' hlim fun n => ?_)
  have := hconv l n
  rwa [hfix] at this

/-- With deterministic demand `z₀` the kernel on `[0, S]` is deterministic. -/
theorem invKernelIcc_dirac (s S : ℝ) (hS : 0 ≤ S) (z₀ : ℝ) :
    invKernelIcc (Measure.dirac z₀) s S hS =
      Kernel.deterministic (fun x => invLawIcc s S hS x z₀)
        ((measurable_invLawIcc s S hS).comp (measurable_id.prodMk measurable_const)) := by
  ext1 x
  change (Measure.dirac z₀).map (invLawIcc s S hS x) = _
  rw [Measure.map_dirac' (measurable_invLawIcc_right s S hS x), Kernel.deterministic_apply]

/-- **The counterexample on `[0, S]`**: with `μ = δ₁`, `s = 1/2`, `S = 2`, Condition M fails for
the process on `[0, S]`, so Theorem 11.12 cannot be applied there. For `A = {0}`, from `1`
(`N` even) or `0` (`N` odd) the chain is at `1 ∉ A`; from `0` (`N` even) or `1` (`N` odd) it is
at `0 ∉ Aᶜ`. -/
theorem ex_13_2b_counterexample_conditionM :
    ¬ ConditionM (invKernelIcc (Measure.dirac 1) (1 / 2) 2 (by norm_num)) := by
  rintro ⟨N, ε, -, hε, hM⟩
  set p0 : Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩ with hp0
  set p1 : Icc (0 : ℝ) 2 := ⟨1, by norm_num⟩ with hp1
  have hne : p1 ≠ p0 := fun h => by simpa [p0, p1] using congrArg Subtype.val h
  have hf0 : invLawIcc (1 / 2) 2 (by norm_num) p0 1 = p1 :=
    Subtype.ext (by rw [invLawIcc_val _ _ zero_le_one]; norm_num [invLaw, p0, p1])
  have hf1 : invLawIcc (1 / 2) 2 (by norm_num) p1 1 = p0 :=
    Subtype.ext (by rw [invLawIcc_val _ _ zero_le_one]; norm_num [invLaw, p0, p1])
  obtain ⟨h0, h1⟩ := iterate_of_swap
    (f := fun x => invLawIcc (1 / 2) 2 (by norm_num) x 1) hf0 hf1 N
  have hd : ∀ x, (kpow (invKernelIcc (Measure.dirac 1) (1 / 2) 2 (by norm_num)) N x) =
      Measure.dirac ((fun x => invLawIcc (1 / 2) 2 (by norm_num) x 1)^[N] x) := fun x => by
    rw [invKernelIcc_dirac, kpow_deterministic]
  have hA : ∀ y : Icc (0 : ℝ) 2, (Measure.dirac y).real {p0} = if y = p0 then 1 else 0 :=
    fun y => by
      rw [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
      by_cases hy : y = p0 <;> simp [hy]
  have hAc : ∀ y : Icc (0 : ℝ) 2, (Measure.dirac y).real {p0}ᶜ = if y = p0 then 0 else 1 :=
    fun y => by
      rw [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _).compl]
      by_cases hy : y = p0 <;> simp [hy]
  rcases hM {p0} (measurableSet_singleton _) with h | h
  · by_cases hN : Even N
    · have := h p1
      rw [hd, h1, hA] at this
      simp only [hN, ↓reduceIte, hne] at this
      linarith
    · have := h p0
      rw [hd, h0, hA] at this
      simp only [hN, ↓reduceIte, hne] at this
      linarith
  · by_cases hN : Even N
    · have := h p0
      rw [hd, h0, hAc] at this
      simp only [hN, ↓reduceIte] at this
      linarith
    · have := h p1
      rw [hd, h1, hAc] at this
      simp only [hN, ↓reduceIte] at this
      linarith

/-! ### The NOTE on p. 391: `(S, ∞)` need not be transient -/

/-- **Correction to p. 391** ("`(S, ∞)` is transient"): needs `μ((0, z̄]) > 0`. With no demand
(`μ = δ₀`) and `0 ≤ s`, every `x > s` is absorbing, `P(x, ·) = δ_x`; for `x > S` the point mass
`δ_x` is an invariant probability measure with all its mass on `(S, ∞)`, and the chain started at
`x` stays in `(S, ∞)` forever. -/
theorem ex_13_2_not_transient {s S : ℝ} (hs : 0 ≤ s) (hsS : s < S) :
    (∀ x, s < x → invKernel (Measure.dirac 0) s S x = Measure.dirac x) ∧
      ∀ x, S < x → adjointOp (invKernel (Measure.dirac 0) s S) (Measure.dirac x) =
        Measure.dirac x ∧ Measure.dirac x (Ioi S) = 1 ∧
        ∀ n, kpow (invKernel (Measure.dirac 0) s S) n x (Ioi S) = 1 := by
  have habs : ∀ x, s < x → invKernel (Measure.dirac 0) s S x = Measure.dirac x := by
    intro x hx
    rw [invKernel_dirac, Kernel.deterministic_apply]
    simp only [invLaw, hx, ↓reduceIte, sub_zero]
    rw [max_eq_left (by linarith)]
  refine ⟨habs, fun x hx => ?_⟩
  have hinv : adjointOp (invKernel (Measure.dirac 0) s S) (Measure.dirac x) = Measure.dirac x := by
    rw [adjointOp, Measure.dirac_bind (Kernel.measurable _), habs x (hsS.trans hx)]
  have hmass : Measure.dirac x (Ioi S) = 1 := Measure.dirac_apply_of_mem hx
  refine ⟨hinv, hmass, fun n => ?_⟩
  rw [← Measure.dirac_bind (kpow _ n).measurable x, ← adjointOp, ← adjointOp_iterate,
    Function.iterate_fixed hinv, hmass]

/-- **The transient set** (p. 391, corrected): if demand is nonnegative and positive with
positive probability, `μ((0, ∞)) > 0`, and `0 ≤ s < S`, then every invariant finite measure `λ`
(on `X ⊆ ℝ`) gives zero mass to `(S, ∞)`. For `c ≥ S`, invariance gives
`λ((c, ∞)) = ∫ P(x, (c, ∞)) λ(dx)`, while `P(x, (c, ∞)) ≤ 1_{(c, ∞)}(x) − η 1_{(c, c+δ]}(x)` with
`η = μ([δ, ∞)) > 0`; hence `λ((c, c + δ]) = 0`, and `(S, ∞)` is a countable union of such
intervals. -/
theorem ex_13_2_invariant_null_above (μ : Measure ℝ) [IsProbabilityMeasure μ] {s S : ℝ}
    (hs : 0 ≤ s) (hsS : s < S) (hμ0 : μ (Iio 0) = 0) (hμpos : 0 < μ (Ioi 0))
    (l : Measure ℝ) [IsFiniteMeasure l] (hl : adjointOp (invKernel μ s S) l = l) :
    l (Ioi S) = 0 := by
  have := ex_13_2a_markov μ s S
  -- a demand level `δ > 0` exceeded with positive probability
  obtain ⟨δ, hδ, hη⟩ : ∃ δ : ℝ, 0 < δ ∧ μ (Ici δ) ≠ 0 := by
    by_contra! h
    have hsub : Ioi (0 : ℝ) ⊆ ⋃ n : ℕ, Ici (1 / ((n : ℝ) + 1)) := fun y hy => by
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (mem_Ioi.1 hy)
      exact mem_iUnion.2 ⟨n, hn.le⟩
    have := measure_mono_null hsub (measure_iUnion_null fun n => h _ (by positivity))
    exact hμpos.ne' this
  -- where the next state can exceed `c`
  have hpre : ∀ c, S ≤ c → ∀ x z, c < invLaw s S x z → z < max (x - c) 0 := by
    intro c hc x z hz
    unfold invLaw at hz
    split_ifs at hz
    · rcases lt_max_iff.1 hz with h | h
      · exact lt_max_iff.2 (Or.inl (by linarith))
      · exact absurd h (by linarith)
    · rcases lt_max_iff.1 hz with h | h
      · exact lt_max_iff.2 (Or.inr (by linarith))
      · exact absurd h (by linarith)
  have hstep : ∀ c, S ≤ c → l (Ioc c (c + δ)) = 0 := by
    intro c hc
    have hpt : ∀ x, invKernel μ s S x (Ioi c) + (Ioc c (c + δ)).indicator (fun _ => μ (Ici δ)) x
        ≤ (Ioi c).indicator (fun _ => 1) x := by
      intro x
      rw [invKernel_apply' _ _ _ _ measurableSet_Ioi]
      by_cases hx : c < x
      · rw [indicator_of_mem (mem_Ioi.2 hx)]
        by_cases hxδ : x ≤ c + δ
        · rw [indicator_of_mem (show x ∈ Ioc c (c + δ) from ⟨hx, hxδ⟩)]
          have hsub : invLaw s S x ⁻¹' Ioi c ⊆ Iio δ := fun z hz => by
            have := hpre c hc x z hz
            rw [mem_Iio]
            exact this.trans_le (max_le (by linarith) hδ.le)
          calc μ (invLaw s S x ⁻¹' Ioi c) + μ (Ici δ) ≤ μ (Iio δ) + μ (Ici δ) :=
                add_le_add_left (measure_mono hsub) _
            _ = μ (Iio δ ∪ Ici δ) :=
                (measure_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici).symm
            _ = 1 := by rw [Iio_union_Ici, measure_univ]
        · rw [indicator_of_notMem (fun h => hxδ h.2), add_zero]
          exact prob_le_one
      · rw [indicator_of_notMem (fun h => hx h.1), indicator_of_notMem (s := Ioi c) hx, add_zero,
          nonpos_iff_eq_zero]
        refine measure_mono_null (fun z hz => ?_) hμ0
        have := hpre c hc x z hz
        rw [mem_Iio]
        exact this.trans_le (max_le (by linarith) le_rfl)
    have hint := lintegral_mono (μ := l) hpt
    rw [lintegral_add_left (Kernel.measurable_coe _ measurableSet_Ioi),
      lintegral_indicator_const measurableSet_Ioc, lintegral_indicator_const measurableSet_Ioi,
      one_mul, ← adjointOp_apply _ _ measurableSet_Ioi, hl] at hint
    have h0 : μ (Ici δ) * l (Ioc c (c + δ)) ≤ 0 :=
      ENNReal.le_of_add_le_add_left (measure_ne_top l _) (by rwa [add_zero])
    exact (mul_eq_zero.1 (nonpos_iff_eq_zero.1 h0)).resolve_left hη
  have hk : ∀ k : ℕ, l (Ioc S (S + k * δ)) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hkδ : 0 ≤ (k : ℝ) * δ := by positivity
      rw [← Ioc_union_Ioc_eq_Ioc (b := S + k * δ) (by linarith) (by push_cast; nlinarith)]
      refine measure_union_null ih ?_
      have := hstep (S + k * δ) (by linarith)
      rwa [show S + k * δ + δ = S + ((k + 1 : ℕ) : ℝ) * δ by push_cast; ring] at this
  have hsub : Ioi S ⊆ ⋃ k : ℕ, Ioc S (S + k * δ) := fun y hy => by
    obtain ⟨k, hk⟩ := exists_nat_ge ((y - S) / δ)
    refine mem_iUnion.2 ⟨k, hy, ?_⟩
    rw [div_le_iff₀ hδ] at hk
    linarith
  exact measure_mono_null hsub (measure_iUnion_null hk)

end StokeyLucasPrescott.ConvergenceApplications

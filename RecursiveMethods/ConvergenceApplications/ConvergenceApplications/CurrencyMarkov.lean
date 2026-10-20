/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.RealIntervals

/-!
# The pure currency economy: the Markov process of real balances

SLP §13.5, Exercises 13.5(i) and 13.5(j), p. 400. The household's end-of-period real balances
are `m′ = g(m, z)`, the shocks `z ∈ Z = [z̲, z̄]` are i.i.d. with distribution `μ`, and on
`X = [y, m̄]` the policy and `μ` define the transition function
`P(m, A) = μ{z : g(m, z) ∈ A}` (Theorem 8.9). This file proves the Markov conclusions for an
abstract policy with the properties established in parts (c)–(h); the dynamic-programming parts
are in `CurrencyEconomy.lean`.

* `CurrencyDensity` (the condition `μ((a, b]) ≥ α(b − a)` of §13.3/§13.5 on `[z̲, z̄]`) and
  its consequence `CurrencyEndMass` (every interval `[z̲, z̲ + δ]`, `[z̄ − δ, z̄]` has positive
  mass): `currencyEndMass_of_density`.
* `currencyIidKernel`: the transition function `P(m, ·) = μ ∘ g(m, ·)⁻¹` of a measurable policy
  with i.i.d. shocks; `currencyIidKernel_apply`, `isMarkovKernel_currencyIidKernel`,
  `markovOpR_currencyIidKernel` (`(Tf)(m) = ∫ f[g(m, z)] μ(dz)`), `isFeller_currencyIidKernel`
  (Theorem 9.14: `g` continuous ⇒ Feller), `isMonotoneTF_currencyIidKernel` (`g` nondecreasing in
  `m` ⇒ monotone).
* `currency_kpow_Ici_ge`, `currency_kpow_Iic_ge`: if `P(s, [h(s), ∞)) ≥ p` for a monotone `h`,
  then `Pⁿ(s, [hⁿ(s), ∞)) ≥ pⁿ` (and dually).
* `CurrencyPolicy`: the properties of the policy on `X = [y, m̄]` used in part (i) — continuity
  (c), `g ≥ y`, `g(·, z)` nondecreasing (e), `g(m, ·)` nonincreasing (h), `g(m̄, z̲) = m̄` (f),
  `g(m, z̲) > m` on `[y, m̄)`, and `g(m̄, z̄) < m̄` if `y < m̄`. `currencyPolicy_of_book` derives
  the last two from the book's (e) (`0 ≤ g(m₂, z) − g(m₁, z) < m₂ − m₁`), (f) and (g)
  (`g(y, z̄) = y`). `CurrencyPolicy.le_mb`: `X` is invariant.
* **Exercise 13.5(i)** (`ex_13_5i`): `P` on `X` is monotone and Feller and satisfies Assumption
  12.1, so (Theorem 12.12, `theorem_12_12_real`) it has a unique invariant probability measure
  `λ*` and `T*ⁿλ₀ ⇒ λ*` for every `λ₀`. The case `m̄ = y` (`X = {y}`) is included.
* **Exercise 13.5(j)** (`ex_13_5j`): for an invariant `λ*`, `∫ m λ*(dm) = ∫∫ g(m, z) μ(dz) λ*(dm)`
  (Theorem 8.3 with `f(m) = m`), so (2) `∫ m dλ* = M/p` holds iff
  `∫∫ g(m, z) μ(dz) λ*(dm) = M/p`, iff `p = M/∫ m dλ*`; since `∫ m dλ* ≥ y > 0` and `λ*` is unique
  and does not involve `p`, this is the unique stationary price level
  (`ex_13_5j_price_unique`).

**Correction** (the hypotheses of part (i)). The book derives Assumption 12.1 from the slope bound
`g(m₂, z) − g(m₁, z) < m₂ − m₁` of part (e) and from part (g). Part (e) is false in general
(`ex_13_5e_counterexample`: in the counterexample to part (d), `g(m, z̲) = m + y` on an interval,
with slope exactly `1`). The proof here uses only the weak monotonicity of `g` in `m` and in `z`
together with the two crossing conditions `g(m, z̲) > m` on `[y, m̄)` and `g(m̄, z̄) < m̄`; the
first holds whenever `m̄` is the smallest fixed point of `g(·, z̲)` in `[y, ∞)`. No slope bound and
no part (g) is needed: from `m̄`, the iterates of `g(·, z̄)` decrease to some `q < m̄`; from `y`,
the iterates of `g(·, z̲)` increase to `m̄`; any `c ∈ (q, m̄)` works, with `N` large and `ε` the
`N`-th power of the mass of shocks near `z̲` and near `z̄` (Assumption (Z3)-type mass and the
continuity of `g` in `z`).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-! ### The shock distribution -/

/-- The **density condition** of §§13.3, 13.5 on `Z = [z̲, z̄]`: `μ((a, b]) ≥ α(b − a)` for
`z̲ ≤ a < b ≤ z̄`, with `α > 0`. -/
def CurrencyDensity {zl zh : ℝ} (μ : Measure (Icc zl zh)) (α : ℝ) : Prop :=
  0 < α ∧ ∀ a b : ℝ, zl ≤ a → a < b → b ≤ zh →
    α * (b - a) ≤ μ.real {z : Icc zl zh | a < (z : ℝ) ∧ (z : ℝ) ≤ b}

/-- Every end interval `[z̲, z̲ + δ]` and `[z̄ − δ, z̄]` (`δ > 0`) has positive mass. -/
def CurrencyEndMass {zl zh : ℝ} (μ : Measure (Icc zl zh)) : Prop :=
  (∀ δ : ℝ, 0 < δ → 0 < μ {z : Icc zl zh | (z : ℝ) ≤ zl + δ}) ∧
    ∀ δ : ℝ, 0 < δ → 0 < μ {z : Icc zl zh | zh - δ ≤ (z : ℝ)}

/-- The density condition gives positive mass at both ends. -/
theorem currencyEndMass_of_density {zl zh α : ℝ} {μ : Measure (Icc zl zh)} [IsProbabilityMeasure μ]
    (h : CurrencyDensity μ α) : CurrencyEndMass μ := by
  obtain ⟨hα, hb⟩ := h
  refine ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩
  · by_cases hz : zh ≤ zl + δ
    · have : {z : Icc zl zh | (z : ℝ) ≤ zl + δ} = univ :=
        eq_univ_of_forall fun z => z.2.2.trans hz
      rw [this, measure_univ]
      exact one_pos
    · push Not at hz
      have h1 := hb zl (zl + δ) le_rfl (by linarith) hz.le
      have hpos : 0 < μ.real {z : Icc zl zh | zl < (z : ℝ) ∧ (z : ℝ) ≤ zl + δ} :=
        lt_of_lt_of_le (by nlinarith) h1
      have hne : μ {z : Icc zl zh | zl < (z : ℝ) ∧ (z : ℝ) ≤ zl + δ} ≠ 0 := fun h0 => by
        simp [measureReal_def, h0] at hpos
      exact lt_of_lt_of_le (pos_iff_ne_zero.2 hne) (measure_mono fun z hz => hz.2)
  · by_cases hz : zh - δ ≤ zl
    · have : {z : Icc zl zh | zh - δ ≤ (z : ℝ)} = univ :=
        eq_univ_of_forall fun z => hz.trans z.2.1
      rw [this, measure_univ]
      exact one_pos
    · push Not at hz
      have h1 := hb (zh - δ) zh hz.le (by linarith) le_rfl
      have hpos : 0 < μ.real {z : Icc zl zh | zh - δ < (z : ℝ) ∧ (z : ℝ) ≤ zh} :=
        lt_of_lt_of_le (by nlinarith) h1
      have hne : μ {z : Icc zl zh | zh - δ < (z : ℝ) ∧ (z : ℝ) ≤ zh} ≠ 0 := fun h0 => by
        simp [measureReal_def, h0] at hpos
      exact lt_of_lt_of_le (pos_iff_ne_zero.2 hne) (measure_mono fun z hz => hz.1.le)

/-! ### The transition function of a policy with i.i.d. shocks -/

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- The transition function defined by a measurable policy `G : X × Z → X` and i.i.d. shocks with
distribution `μ` (SLP Theorem 8.9): `P(m, A) = μ{z : G(m, z) ∈ A}`. -/
noncomputable def currencyIidKernel (μ : Measure Z) [SFinite μ] {G : X × Z → X}
    (hG : Measurable G) : Kernel X X where
  toFun m := μ.map fun z => G (m, z)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have : ∀ m, (μ.map fun z => G (m, z)) A = μ (Prod.mk m ⁻¹' (G ⁻¹' A)) := fun m => by
      have hGm : Measurable fun z => G (m, z) := hG.comp measurable_prodMk_left
      rw [Measure.map_apply hGm hA]
      rfl
    simp_rw [this]
    exact measurable_measure_prodMk_left (hG hA)

/-- `P(m, ·)` is the image of `μ` under `z ↦ G(m, z)`. -/
theorem currencyIidKernel_apply (μ : Measure Z) [SFinite μ] {G : X × Z → X} (hG : Measurable G)
    (m : X) : currencyIidKernel μ hG m = μ.map fun z => G (m, z) := rfl

/-- `P(m, A) = μ{z : G(m, z) ∈ A}`. -/
theorem currencyIidKernel_apply' (μ : Measure Z) [SFinite μ] {G : X × Z → X} (hG : Measurable G)
    (m : X) {A : Set X} (hA : MeasurableSet A) :
    currencyIidKernel μ hG m A = μ {z | G (m, z) ∈ A} := by
  have hGm : Measurable fun z => G (m, z) := hG.comp measurable_prodMk_left
  rw [currencyIidKernel_apply, Measure.map_apply hGm hA]
  rfl

/-- `P` is a transition function. -/
theorem isMarkovKernel_currencyIidKernel (μ : Measure Z) [IsProbabilityMeasure μ] {G : X × Z → X}
    (hG : Measurable G) : IsMarkovKernel (currencyIidKernel μ hG) :=
  ⟨fun m => by
    rw [currencyIidKernel_apply]
    infer_instance⟩

/-- `(Tf)(m) = ∫ f[G(m, z)] μ(dz)`. -/
theorem markovOpR_currencyIidKernel (μ : Measure Z) [SFinite μ] {G : X × Z → X}
    (hG : Measurable G) {f : X → ℝ} (hf : Measurable f) (m : X) :
    markovOpR (currencyIidKernel μ hG) f m = ∫ z, f (G (m, z)) ∂μ := by
  have hGm : Measurable fun z => G (m, z) := hG.comp measurable_prodMk_left
  rw [markovOpR, currencyIidKernel_apply, integral_map hGm.aemeasurable hf.aestronglyMeasurable]

/-- **Theorem 9.14** for i.i.d. shocks: if `G` is continuous, `P` has the Feller property. -/
theorem isFeller_currencyIidKernel [TopologicalSpace X] [FirstCountableTopology X]
    [OpensMeasurableSpace X] [TopologicalSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {G : X × Z → X} (hG : Measurable G) (hGc : ∀ z, Continuous fun m => G (m, z)) :
    IsFeller (currencyIidKernel μ hG) := by
  intro f hf ⟨B, hB⟩
  have heq : markovOpR (currencyIidKernel μ hG) f = fun m => ∫ z, f (G (m, z)) ∂μ :=
    funext (markovOpR_currencyIidKernel μ hG hf.measurable)
  rw [heq]
  exact continuous_of_dominated (bound := fun _ => B)
    (fun m => (hf.measurable.comp (hG.comp measurable_prodMk_left)).aestronglyMeasurable)
    (fun m => Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB _)
    (integrable_const B) (Eventually.of_forall fun z => hf.comp (hGc z))

/-- If `G(·, z)` is nondecreasing for every `z`, `P` is monotone. -/
theorem isMonotoneTF_currencyIidKernel [Preorder X] (μ : Measure Z) [IsProbabilityMeasure μ]
    {G : X × Z → X} (hG : Measurable G) (hGm : ∀ z, Monotone fun m => G (m, z)) :
    IsMonotoneTF (currencyIidKernel μ hG) := by
  intro f hf ⟨B, hB⟩ hfm m m' hmm'
  have hGs : ∀ m, Measurable fun z => G (m, z) := fun m => hG.comp measurable_prodMk_left
  rw [markovOpR_currencyIidKernel μ hG hf, markovOpR_currencyIidKernel μ hG hf]
  exact integral_mono (integrable_of_bounded (hf.comp (hGs m)) fun _ => hB _)
    (integrable_of_bounded (hf.comp (hGs m')) fun _ => hB _)
    fun z => hfm (hGm z hmm')

/-! ### Lower bounds on the `n`-step transition function -/

/-- If `P(s, [h(s), ∞)) ≥ p` for all `s`, with `h` nondecreasing, then
`Pⁿ(s, [hⁿ(s), ∞)) ≥ pⁿ`. -/
theorem currency_kpow_Ici_ge {S : Type*} [MeasurableSpace S] [Preorder S] (κ : Kernel S S)
    (hI : ∀ s : S, MeasurableSet (Ici s)) {h : S → S} (hh : Monotone h) {p : ℝ≥0∞}
    (hp : ∀ s, p ≤ κ s (Ici (h s))) (n : ℕ) (s : S) : p ^ n ≤ kpow κ n s (Ici (h^[n] s)) := by
  induction n generalizing s with
  | zero =>
    simp only [pow_zero, Function.iterate_zero, id_eq]
    rw [show kpow κ 0 = Kernel.id from rfl, Kernel.id_apply, Measure.dirac_apply' _ (hI s)]
    simp
  | succ n ih =>
    rw [show kpow κ (n + 1) = kpow κ n ∘ₖ κ from rfl, Kernel.comp_apply' _ _ _ (hI _)]
    calc p ^ (n + 1) = p ^ n * p := pow_succ _ _
      _ ≤ p ^ n * κ s (Ici (h s)) := mul_le_mul_right (hp s) _
      _ = ∫⁻ _ in Ici (h s), p ^ n ∂κ s := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ b in Ici (h s), kpow κ n b (Ici (h^[n + 1] s)) ∂κ s := by
        refine setLIntegral_mono' (hI _) fun b hb => (ih b).trans (measure_mono fun x hx => ?_)
        rw [Function.iterate_succ_apply]
        exact (hh.iterate n hb).trans hx
      _ ≤ ∫⁻ b, kpow κ n b (Ici (h^[n + 1] s)) ∂κ s := setLIntegral_le_lintegral _ _

/-- If `P(s, (−∞, h(s)]) ≥ p` for all `s`, with `h` nondecreasing, then
`Pⁿ(s, (−∞, hⁿ(s)]) ≥ pⁿ`. -/
theorem currency_kpow_Iic_ge {S : Type*} [MeasurableSpace S] [Preorder S] (κ : Kernel S S)
    (hI : ∀ s : S, MeasurableSet (Iic s)) {h : S → S} (hh : Monotone h) {p : ℝ≥0∞}
    (hp : ∀ s, p ≤ κ s (Iic (h s))) (n : ℕ) (s : S) : p ^ n ≤ kpow κ n s (Iic (h^[n] s)) := by
  induction n generalizing s with
  | zero =>
    simp only [pow_zero, Function.iterate_zero, id_eq]
    rw [show kpow κ 0 = Kernel.id from rfl, Kernel.id_apply, Measure.dirac_apply' _ (hI s)]
    simp
  | succ n ih =>
    rw [show kpow κ (n + 1) = kpow κ n ∘ₖ κ from rfl, Kernel.comp_apply' _ _ _ (hI _)]
    calc p ^ (n + 1) = p ^ n * p := pow_succ _ _
      _ ≤ p ^ n * κ s (Iic (h s)) := mul_le_mul_right (hp s) _
      _ = ∫⁻ _ in Iic (h s), p ^ n ∂κ s := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ b in Iic (h s), kpow κ n b (Iic (h^[n + 1] s)) ∂κ s := by
        refine setLIntegral_mono' (hI _) fun b hb => (ih b).trans (measure_mono fun x hx => ?_)
        rw [Function.iterate_succ_apply]
        exact hx.trans (hh.iterate n hb)
      _ ≤ ∫⁻ b, kpow κ n b (Iic (h^[n + 1] s)) ∂κ s := setLIntegral_le_lintegral _ _

/-! ### The policy on `X = [y, m̄]` -/

/-- The left endpoint `a` of `[a, b] ⊆ ℝ`. -/
def currencyLo {a b : ℝ} (hab : a ≤ b) : Icc a b := ⟨a, left_mem_Icc.2 hab⟩

/-- The right endpoint `b` of `[a, b] ⊆ ℝ`. -/
def currencyHi {a b : ℝ} (hab : a ≤ b) : Icc a b := ⟨b, right_mem_Icc.2 hab⟩

/-- `a` is the least element of `[a, b]`. -/
theorem currencyLo_le {a b : ℝ} (hab : a ≤ b) (s : Icc a b) : currencyLo hab ≤ s := s.2.1

/-- `b` is the greatest element of `[a, b]`. -/
theorem le_currencyHi {a b : ℝ} (hab : a ≤ b) (s : Icc a b) : s ≤ currencyHi hab := s.2.2

variable {y mb zl zh : ℝ}

/-- The properties of the policy `g` on `X = [y, m̄]`, `Z = [z̲, z̄]` used in Exercise 13.5(i):
continuity (part (c)), feasibility `g ≥ y`, `g(·, z)` nondecreasing (part (e), weak form),
`g(m, ·)` nonincreasing (part (h)), `g(m̄, z̲) = m̄` (part (f)), and the two crossing conditions
`g(m, z̲) > m` for `y ≤ m < m̄` and `g(m̄, z̄) < m̄` when `y < m̄`. -/
structure CurrencyPolicy (y mb zl zh : ℝ) (g : Icc y mb → Icc zl zh → ℝ) : Prop where
  hy : y ≤ mb
  hz : zl ≤ zh
  cont : Continuous fun p : Icc y mb × Icc zl zh => g p.1 p.2
  ge : ∀ m z, y ≤ g m z
  mono : ∀ z, Monotone fun m => g m z
  anti : ∀ m, Antitone (g m)
  fixed : g (currencyHi hy) (currencyLo hz) = mb
  up : ∀ m : Icc y mb, (m : ℝ) < mb → (m : ℝ) < g m (currencyLo hz)
  down : y < mb → g (currencyHi hy) (currencyHi hz) < mb

variable {g : Icc y mb → Icc zl zh → ℝ}

/-- `X = [y, m̄]` is invariant: `y ≤ g(m, z) ≤ g(m̄, z) ≤ g(m̄, z̲) = m̄` (parts (e), (h), (f)). -/
theorem CurrencyPolicy.le_mb (h : CurrencyPolicy y mb zl zh g) (m : Icc y mb) (z : Icc zl zh) :
    g m z ≤ mb := by
  rw [← h.fixed]
  exact (h.mono z (le_currencyHi h.hy m)).trans (h.anti _ (currencyLo_le h.hz z))

/-- The policy as a map `X × Z → X`. -/
def CurrencyPolicy.toMap (h : CurrencyPolicy y mb zl zh g) (p : Icc y mb × Icc zl zh) :
    Icc y mb :=
  ⟨g p.1 p.2, h.ge _ _, h.le_mb _ _⟩

/-- The policy map `X × Z → X` is continuous (part (c)). -/
theorem CurrencyPolicy.continuous_toMap (h : CurrencyPolicy y mb zl zh g) :
    Continuous h.toMap :=
  h.cont.subtype_mk _

/-- The transition function on `X = [y, m̄]` defined by `g` and `μ`. -/
noncomputable def currencyPolicyKernel (h : CurrencyPolicy y mb zl zh g)
    (μ : Measure (Icc zl zh)) [SFinite μ] : Kernel (Icc y mb) (Icc y mb) :=
  currencyIidKernel μ h.continuous_toMap.measurable

/-- **The book's hypotheses give the crossing conditions.** If `0 ≤ g(m₂, z) − g(m₁, z) <
m₂ − m₁` for `m₁ < m₂` (part (e)), `g(m̄, z̲) = m̄` (part (f)) and `g(y, z̄) = y` (part (g)), then
`g(m, z̲) > m` on `[y, m̄)` and `g(m̄, z̄) < m̄` if `y < m̄`. -/
theorem currencyPolicy_of_book (hy : y ≤ mb) (hz : zl ≤ zh)
    (hcont : Continuous fun p : Icc y mb × Icc zl zh => g p.1 p.2) (hge : ∀ m z, y ≤ g m z)
    (hmono : ∀ z, Monotone fun m => g m z) (hanti : ∀ m, Antitone (g m))
    (hslope : ∀ z (m₁ m₂ : Icc y mb), m₁ < m₂ → g m₂ z - g m₁ z < (m₂ : ℝ) - m₁)
    (hf : g (currencyHi hy) (currencyLo hz) = mb) (hg : g (currencyLo hy) (currencyHi hz) = y) :
    CurrencyPolicy y mb zl zh g := by
  refine ⟨hy, hz, hcont, hge, hmono, hanti, hf, fun m hm => ?_, fun hlt => ?_⟩
  · have := hslope (currencyLo hz) m (currencyHi hy) hm
    change g (currencyHi hy) (currencyLo hz) - g m (currencyLo hz) < mb - m at this
    linarith
  · have := hslope (currencyHi hz) (currencyLo hy) (currencyHi hy) hlt
    change g (currencyHi hy) (currencyHi hz) - g (currencyLo hy) (currencyHi hz) < mb - y at this
    linarith

/-! ### Exercise 13.5(i) -/

/-- The iterates of `g(·, z)` from `m`, as functions of `z`, are continuous. -/
theorem CurrencyPolicy.continuous_iterate (h : CurrencyPolicy y mb zl zh g) (m : Icc y mb)
    (n : ℕ) : Continuous fun z : Icc zl zh => (fun m' => h.toMap (m', z))^[n] m := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact h.continuous_toMap.comp (ih.prodMk continuous_id)

/-- From `y`, the iterates of `g(·, z̲)` increase to `m̄`: for `c < m̄` they eventually exceed
`c`. -/
theorem CurrencyPolicy.eventually_gt_bot (h : CurrencyPolicy y mb zl zh g) {c : ℝ}
    (hc : c < mb) : ∃ N, ∀ n ≥ N,
      c < ((fun m => h.toMap (m, currencyLo h.hz))^[n] (currencyLo h.hy) : ℝ) := by
  set φ : Icc y mb → Icc y mb := fun m => h.toMap (m, currencyLo h.hz)
  have hφm : Monotone φ := fun m m' hmm' => h.mono _ hmm'
  have hφc : Continuous φ := h.continuous_toMap.comp (continuous_id.prodMk continuous_const)
  set a : ℕ → ℝ := fun n => (φ^[n] (currencyLo h.hy) : ℝ)
  have hstep : ∀ n, φ^[n] (currencyLo h.hy) ≤ φ^[n + 1] (currencyLo h.hy) := fun n => by
    induction n with
    | zero => exact currencyLo_le h.hy _
    | succ n ih =>
      rw [Function.iterate_succ_apply' φ n, Function.iterate_succ_apply' φ (n + 1)]
      exact hφm ih
  have ha : Monotone a := monotone_nat_of_le_succ fun n => hstep n
  have hbdd : BddAbove (range a) := ⟨mb, by rintro _ ⟨n, rfl⟩; exact (φ^[n] _).2.2⟩
  set L := ⨆ n, a n
  have hlim : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciSup ha hbdd
  have hLy : y ≤ L := (currencyLo h.hy).2.1.trans (le_ciSup hbdd 0)
  have hLm : L ≤ mb := ciSup_le fun n => (φ^[n] _).2.2
  set L' : Icc y mb := ⟨L, hLy, hLm⟩
  have hlim' : Tendsto (fun n => φ^[n] (currencyLo h.hy)) atTop (𝓝 L') := tendsto_subtype_rng.2 hlim
  have hfix : (φ L' : ℝ) = L := by
    have h1 : Tendsto (fun n => (φ (φ^[n] (currencyLo h.hy)) : ℝ)) atTop (𝓝 (φ L' : ℝ)) :=
      (continuous_subtype_val.tendsto _).comp ((hφc.tendsto _).comp hlim')
    have h2 : Tendsto (fun n => (φ (φ^[n] (currencyLo h.hy)) : ℝ)) atTop (𝓝 L) := by
      have := hlim.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, a, Function.iterate_succ_apply']
    exact tendsto_nhds_unique h1 h2
  have hLeq : L = mb := by
    by_contra hne
    have := h.up L' (lt_of_le_of_ne hLm hne)
    change L < (φ L' : ℝ) at this
    linarith
  rw [← hLeq] at hc
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).1 c hc)
  exact ⟨N, hN⟩

/-- From `m̄`, the iterates of `g(·, z̄)` decrease to a limit `q < m̄` (when `y < m̄`). -/
theorem CurrencyPolicy.exists_lim_top (h : CurrencyPolicy y mb zl zh g) (hlt : y < mb) :
    ∃ q < mb, ∀ c, q < c → ∃ N, ∀ n ≥ N,
      ((fun m => h.toMap (m, currencyHi h.hz))^[n] (currencyHi h.hy) : ℝ) < c := by
  set φ : Icc y mb → Icc y mb := fun m => h.toMap (m, currencyHi h.hz)
  have hφm : Monotone φ := fun m m' hmm' => h.mono _ hmm'
  have hstep : ∀ n, φ^[n + 1] (currencyHi h.hy) ≤ φ^[n] (currencyHi h.hy) := fun n => by
    induction n with
    | zero => exact le_currencyHi h.hy _
    | succ n ih =>
      rw [Function.iterate_succ_apply' φ n, Function.iterate_succ_apply' φ (n + 1)]
      exact hφm ih
  set b : ℕ → ℝ := fun n => (φ^[n] (currencyHi h.hy) : ℝ)
  have hb : Antitone b := antitone_nat_of_succ_le fun n => hstep n
  have hbdd : BddBelow (range b) := ⟨y, by rintro _ ⟨n, rfl⟩; exact (φ^[n] _).2.1⟩
  set q := ⨅ n, b n
  have hlim : Tendsto b atTop (𝓝 q) := tendsto_atTop_ciInf hb hbdd
  have hq : q < mb := by
    have h1 : q ≤ b 1 := ciInf_le hbdd 1
    have h2 : b 1 = g (currencyHi h.hy) (currencyHi h.hz) := rfl
    linarith [h.down hlt]
  refine ⟨q, hq, fun c hc => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 c hc)
  exact ⟨N, hN⟩

/-- **Exercise 13.5(i).** The transition function `P` on `X = [y, m̄]` defined by `g` and `μ` is
monotone and Feller and satisfies Assumption 12.1. Hence (Theorem 12.12) it has a unique invariant
probability measure `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every initial distribution `λ₀`. -/
theorem ex_13_5i (h : CurrencyPolicy y mb zl zh g) (μ : Measure (Icc zl zh))
    [IsProbabilityMeasure μ] (hμ : CurrencyEndMass μ) :
    IsMarkovKernel (currencyPolicyKernel h μ) ∧ IsMonotoneTF (currencyPolicyKernel h μ) ∧
      IsFeller (currencyPolicyKernel h μ) ∧
      (∃ (c : Icc y mb) (ε : ℝ) (N : ℕ), 0 < ε ∧ 1 ≤ N ∧
        ε ≤ (kpow (currencyPolicyKernel h μ) N (currencyLo h.hy)).real (Ici c) ∧
        ε ≤ (kpow (currencyPolicyKernel h μ) N (currencyHi h.hy)).real (Iic c)) ∧
      ∃ lam : Measure (Icc y mb), IsProbabilityMeasure lam ∧
        adjointOp (currencyPolicyKernel h μ) lam = lam ∧
        (∀ ν : Measure (Icc y mb), IsProbabilityMeasure ν →
          adjointOp (currencyPolicyKernel h μ) ν = ν → ν = lam) ∧
        ∀ lam₀ : Measure (Icc y mb), IsProbabilityMeasure lam₀ →
          ConvWeak (fun n => (adjointOp (currencyPolicyKernel h μ))^[n] lam₀) lam := by
  set κ := currencyPolicyKernel h μ
  have hG := h.continuous_toMap
  have hK : IsMarkovKernel κ := isMarkovKernel_currencyIidKernel μ hG.measurable
  have hM : IsMonotoneTF κ := isMonotoneTF_currencyIidKernel μ hG.measurable fun z m m' hmm' =>
    h.mono z hmm'
  have hF : IsFeller κ := isFeller_currencyIidKernel μ hG.measurable fun z =>
    hG.comp (continuous_id.prodMk continuous_const)
  have hA : ∃ (c : Icc y mb) (ε : ℝ) (N : ℕ), 0 < ε ∧ 1 ≤ N ∧
      ε ≤ (kpow κ N (currencyLo h.hy)).real (Ici c) ∧
        ε ≤ (kpow κ N (currencyHi h.hy)).real (Iic c) := by
    rcases h.hy.lt_or_eq with hlt | heq
    · obtain ⟨q, hq, hqN⟩ := h.exists_lim_top hlt
      set c : ℝ := max q y / 2 + mb / 2
      have hcq : q < c := by
        have := le_max_left q y
        simp only [c]; linarith
      have hcm : c < mb := by
        have := max_lt hq hlt
        simp only [c]; linarith
      have hcy : y ≤ c := by
        have := le_max_right q y
        simp only [c]; linarith
      set cX : Icc y mb := ⟨c, hcy, hcm.le⟩
      obtain ⟨N₁, hN₁⟩ := h.eventually_gt_bot hcm
      obtain ⟨N₂, hN₂⟩ := hqN c hcq
      set N := max N₁ N₂ + 1
      have hN1 := hN₁ N (by omega)
      have hN2 := hN₂ N (by omega)
      -- perturbing the shocks near `z̲`
      set Φ := fun z : Icc zl zh => (fun m' => h.toMap (m', z))^[N] (currencyLo h.hy)
      have hΦ : Continuous Φ := h.continuous_iterate _ N
      have hev : ∀ᶠ z in 𝓝 (currencyLo h.hz), c < (Φ z : ℝ) :=
        ((continuous_subtype_val.comp hΦ).tendsto _).eventually (lt_mem_nhds hN1)
      obtain ⟨δ, hδ, hδΦ⟩ := Metric.eventually_nhds_iff.1 hev
      have hzs : zl ≤ min (zl + δ / 2) zh := le_min (by linarith) h.hz
      set zs : Icc zl zh := ⟨min (zl + δ / 2) zh, hzs, min_le_right _ _⟩
      have hΦs : c < (Φ zs : ℝ) := by
        refine hδΦ ?_
        rw [Subtype.dist_eq, Real.dist_eq]
        change |min (zl + δ / 2) zh - zl| < δ
        rw [abs_of_nonneg (by linarith)]
        have := min_le_left (zl + δ / 2) zh
        linarith
      set p₁ := μ {z : Icc zl zh | (z : ℝ) ≤ zl + δ / 2}
      have hp₁ : 0 < p₁ := hμ.1 _ (by linarith)
      have hb₁ : ∀ m, p₁ ≤ κ m (Ici (h.toMap (m, zs))) := fun m => by
        rw [show κ m (Ici (h.toMap (m, zs))) = μ {z | h.toMap (m, z) ∈ Ici (h.toMap (m, zs))}
          from currencyIidKernel_apply' μ hG.measurable m measurableSet_Ici]
        refine measure_mono fun z hz => ?_
        have hle : z ≤ zs := by
          change (z : ℝ) ≤ min (zl + δ / 2) zh
          exact le_min hz z.2.2
        exact h.anti m hle
      have hk₁ := currency_kpow_Ici_ge κ (fun _ => measurableSet_Ici)
        (h := fun m => h.toMap (m, zs)) (fun m m' hmm' => h.mono zs hmm') hb₁ N (currencyLo h.hy)
      have hk₁' : p₁ ^ N ≤ kpow κ N (currencyLo h.hy) (Ici cX) :=
        hk₁.trans (measure_mono fun x hx => (show cX ≤ Φ zs from hΦs.le).trans hx)
      -- perturbing the shocks near `z̄`
      set Ψ := fun z : Icc zl zh => (fun m' => h.toMap (m', z))^[N] (currencyHi h.hy)
      have hΨ : Continuous Ψ := h.continuous_iterate _ N
      have hev' : ∀ᶠ z in 𝓝 (currencyHi h.hz), (Ψ z : ℝ) < c :=
        ((continuous_subtype_val.comp hΨ).tendsto _).eventually (gt_mem_nhds hN2)
      obtain ⟨δ', hδ', hδΨ⟩ := Metric.eventually_nhds_iff.1 hev'
      have hzt : max (zh - δ' / 2) zl ≤ zh := max_le (by linarith) h.hz
      set zt : Icc zl zh := ⟨max (zh - δ' / 2) zl, le_max_right _ _, hzt⟩
      have hΨt : (Ψ zt : ℝ) < c := by
        refine hδΨ ?_
        rw [Subtype.dist_eq, Real.dist_eq]
        change |max (zh - δ' / 2) zl - zh| < δ'
        rw [abs_of_nonpos (by linarith)]
        have := le_max_left (zh - δ' / 2) zl
        linarith
      set p₂ := μ {z : Icc zl zh | zh - δ' / 2 ≤ (z : ℝ)}
      have hp₂ : 0 < p₂ := hμ.2 _ (by linarith)
      have hb₂ : ∀ m, p₂ ≤ κ m (Iic (h.toMap (m, zt))) := fun m => by
        rw [show κ m (Iic (h.toMap (m, zt))) = μ {z | h.toMap (m, z) ∈ Iic (h.toMap (m, zt))}
          from currencyIidKernel_apply' μ hG.measurable m measurableSet_Iic]
        refine measure_mono fun z hz => ?_
        have hle : zt ≤ z := by
          change max (zh - δ' / 2) zl ≤ (z : ℝ)
          exact max_le hz z.2.1
        exact h.anti m hle
      have hk₂ := currency_kpow_Iic_ge κ (fun _ => measurableSet_Iic)
        (h := fun m => h.toMap (m, zt)) (fun m m' hmm' => h.mono zt hmm') hb₂ N (currencyHi h.hy)
      have hk₂' : p₂ ^ N ≤ kpow κ N (currencyHi h.hy) (Iic cX) :=
        hk₂.trans (measure_mono fun x hx => hx.trans (show Ψ zt ≤ cX from hΨt.le))
      -- the constants
      have := ex_8_4a κ N
      have hfin₁ : p₁ ^ N ≠ ∞ := ENNReal.pow_ne_top (measure_ne_top _ _)
      have hfin₂ : p₂ ^ N ≠ ∞ := ENNReal.pow_ne_top (measure_ne_top _ _)
      refine ⟨cX, min (p₁ ^ N).toReal (p₂ ^ N).toReal, N, lt_min ?_ ?_, by omega, ?_, ?_⟩
      · exact ENNReal.toReal_pos (pow_ne_zero _ hp₁.ne') hfin₁
      · exact ENNReal.toReal_pos (pow_ne_zero _ hp₂.ne') hfin₂
      · exact (min_le_left _ _).trans ((ENNReal.toReal_le_toReal hfin₁ (measure_ne_top _ _)).2
          hk₁')
      · exact (min_le_right _ _).trans ((ENNReal.toReal_le_toReal hfin₂ (measure_ne_top _ _)).2
          hk₂')
    · -- `X = {y}`
      refine ⟨currencyLo h.hy, 1, 1, one_pos, le_rfl, ?_, ?_⟩
      · rw [kpow_one, show Ici (currencyLo h.hy) = univ from eq_univ_of_forall (currencyLo_le h.hy),
          probReal_univ]
      · rw [kpow_one, show Iic (currencyLo h.hy) = univ from eq_univ_of_forall fun s =>
            (show (s : ℝ) ≤ y from heq ▸ s.2.2), probReal_univ]
  obtain ⟨c, ε, N, hA⟩ := hA
  refine ⟨hK, hM, hF, ⟨c, ε, N, hA⟩, ?_⟩
  exact theorem_12_12_real h.hy κ hM hF hA.1 hA.2.1 hA.2.2.1 hA.2.2.2

/-! ### Exercise 13.5(j) -/

/-- **Exercise 13.5(j).** For an invariant probability measure `λ*` of `P`,
`∫ m λ*(dm) = ∫∫ g(m, z) μ(dz) λ*(dm)` (Theorem 8.3 with `f(m) = m`). Hence (2),
`∫ m λ*(dm) = M/p`, holds iff `∫∫ g(m, z) μ(dz) λ*(dm) = M/p`, iff `p = M/∫ m λ*(dm)`, and
`∫ m λ*(dm) ≥ y > 0`. -/
theorem ex_13_5j (h : CurrencyPolicy y mb zl zh g) (μ : Measure (Icc zl zh))
    [IsProbabilityMeasure μ] (hy : 0 < y) (lam : Measure (Icc y mb)) [IsProbabilityMeasure lam]
    (hinv : adjointOp (currencyPolicyKernel h μ) lam = lam) {M p : ℝ} (hM : 0 < M) (hp : 0 < p) :
    ∫ m, (m : ℝ) ∂lam = ∫ m, ∫ z, g m z ∂μ ∂lam ∧
      ((∫ m, (m : ℝ) ∂lam = M / p) ↔ ∫ m, ∫ z, g m z ∂μ ∂lam = M / p) ∧
      ((∫ m, (m : ℝ) ∂lam = M / p) ↔ p = M / ∫ m, (m : ℝ) ∂lam) ∧
      y ≤ ∫ m, (m : ℝ) ∂lam := by
  set κ := currencyPolicyKernel h μ
  have hG := h.continuous_toMap
  have : IsMarkovKernel κ := isMarkovKernel_currencyIidKernel μ hG.measurable
  have hbd : ∀ m : Icc y mb, |(m : ℝ)| ≤ |y| + |mb| := fun m => by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le y, abs_nonneg mb, m.2.1]
    · linarith [le_abs_self mb, abs_nonneg y, m.2.2]
  have h83 := theorem_8_3_cor κ lam (f := fun m : Icc y mb => (m : ℝ)) measurable_subtype_coe hbd
  rw [hinv] at h83
  have hT : ∀ m, markovOpR κ (fun m : Icc y mb => (m : ℝ)) m = ∫ z, g m z ∂μ := fun m =>
    markovOpR_currencyIidKernel μ hG.measurable measurable_subtype_coe m
  simp only [hT] at h83
  have hmean : y ≤ ∫ m, (m : ℝ) ∂lam := by
    have := integral_mono (integrable_const y) (integrable_of_bounded measurable_subtype_coe hbd
      (μ := lam)) fun m => m.2.1
    simpa using this
  have hpos : 0 < ∫ m, (m : ℝ) ∂lam := hy.trans_le hmean
  refine ⟨h83.symm, by rw [h83], ⟨fun he => ?_, fun he => ?_⟩, hmean⟩
  · rw [he]; field_simp
  · rw [he]; field_simp

/-- **The stationary price level is unique** (p. 400). Under the hypotheses of part (i), the
invariant measure `λ*` is unique and does not involve `p`; a price level `p > 0` satisfies (2) for
some invariant `λ` iff `p = M/∫ m λ*(dm)`. -/
theorem ex_13_5j_price_unique (h : CurrencyPolicy y mb zl zh g) (μ : Measure (Icc zl zh))
    [IsProbabilityMeasure μ] (hμ : CurrencyEndMass μ) (hy : 0 < y) {M : ℝ} (hM : 0 < M) :
    ∃ lam : Measure (Icc y mb), IsProbabilityMeasure lam ∧
      adjointOp (currencyPolicyKernel h μ) lam = lam ∧ 0 < ∫ m, (m : ℝ) ∂lam ∧
      ∀ p : ℝ, 0 < p → ((∃ ν : Measure (Icc y mb), IsProbabilityMeasure ν ∧
        adjointOp (currencyPolicyKernel h μ) ν = ν ∧ ∫ m, (m : ℝ) ∂ν = M / p) ↔
        p = M / ∫ m, (m : ℝ) ∂lam) := by
  obtain ⟨-, -, -, -, lam, hlam, hinv, huniq, -⟩ := ex_13_5i h μ hμ
  have hj := fun p (hp : 0 < p) => ex_13_5j h μ hy lam hinv hM hp
  refine ⟨lam, hlam, hinv, hy.trans_le (hj 1 one_pos).2.2.2, fun p hp => ⟨?_, fun he => ?_⟩⟩
  · rintro ⟨ν, hν, hνinv, hνp⟩
    rw [huniq ν hν hνinv] at hνp
    exact ((hj p hp).2.2.1).1 hνp
  · exact ⟨lam, hlam, hinv, ((hj p hp).2.2.1).2 he⟩

end StokeyLucasPrescott.ConvergenceApplications

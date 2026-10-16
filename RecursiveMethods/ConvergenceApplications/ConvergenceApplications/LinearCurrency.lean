/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.ConditionM
import ConvergenceApplications.FellerInvariant

/-!
# A pure currency economy with linear utility

SLP §13.6, Exercise 13.6, pp. 401–402. `Z = [0, 1]` (`unitInterval`), `U(c, z) = zc`, shocks
i.i.d. with distribution `μ`, `0 < β < 1`, endowment `y > 0`. Write `H(ζ) = ∫ max{ζ, z′} μ(dz′)`
(`maxInt`) and `δ = μ([ζ, 1])`. The hypothesis `μ ≠ δ₀` is used in the form `∫ z dμ > 0`.

* **The function `H`**: `integrable_max_unit`, `integrable_coe_unit`, `le_maxInt` (`H(ζ) ≥ ζ`),
  `maxInt_mono`, `maxInt_sub_le` (`H(ζ′) − H(ζ) ≤ ζ′ − ζ`), `continuous_maxInt` (`H` is
  1-Lipschitz), `maxInt_zero` (`H(0) = ∫ z dμ`), `maxInt_of_one_le` (`H(ζ) = ζ` for `ζ ≥ 1`).
* **The cutoff equation** (`exists_unique_cutoff`, p. 401): for `0 < b < 1`, `ζ = bH(ζ)` has a
  unique root in `(0, 1)` (`h(ζ) = bH(ζ) − ζ` is continuous and strictly decreasing, `h(0) > 0 >
  h(1)`). It serves §13.6 (`b = β`) and §13.7 (`b = βR`). `delta_pos_of_cutoff`: at the root
  `δ = μ([ζ, 1]) > 0`.
* **The density condition** of §13.5 (`UnitDensityLowerBound`, `μ((a, b]) ≥ α(b − a)`) gives
  `∫ z dμ > 0`, `μ([0, ζ)) > 0` for `ζ > 0` and `μ((a, 1]) > 0` for `a < 1`
  (`unitDensityLowerBound_pos`).
* **Exercise 13.6(a)** (p. 401; `ex_13_6a`, `currency_bellman`): with the unique `ζ ∈ (0, 1)`
  solving `ζ = β∫max{ζ, z′}μ(dz′)` and `A = ζy/(1 − β) > 0`, `v(m, z) = max{ζ, z} m + A`
  (`currencyValue`) satisfies the functional equation (1) (`SatisfiesCurrencyBellman`: `v(m, z)`
  is the greatest value of the objective over `y ≤ m′ ≤ m + y`), the maximum being attained at
  the policy `g(m, z) = m + y` if `z < ζ`, `y` if `z ≥ ζ` (`currencyPolicy`). Conversely
  (`ex_13_6a_unique`), if `v(m, z) = max{ζ, z} m + A` with `ζ ≥ 0` satisfies (1), then
  `ζ = βH(ζ)`, `A = ζy/(1 − β)` and `ζ ∈ (0, 1)`: this characterises `ζ` and `A`.
* **The transition function defined by `g` and `μ`** (Theorem 8.9): `cutoffKernel`,
  `P(m, A) = μ{z : g(m, z) ∈ A}` for a cutoff policy; `cutoffKernel_apply`
  (`P(m, ·) = μ([0, ζ))δ_{φ(m)} + μ([ζ, 1])δ_b`), `isMarkovKernel_cutoffKernel`,
  `kpow_succ_cutoffKernel`, `cutoffKernel_conditionM` (Condition M with `N = 1`, `ε = δ`), and
  `invariant_unique_of_conditionM_one` (via Theorem 11.12: an invariant probability measure is the
  only one, and `‖T*ⁿλ₀ − π‖ ≤ 2(1 − ε)ⁿ`). The §13.6 process is `currencyKernel`.
* **Exercise 13.6(b)** (p. 401; `ex_13_6b`, `ex_13_6b_density`): if `μ([0, ζ)) > 0` (e.g. under
  the density condition), the lattice `{iy : i ≥ 1}` (`currencyLattice`) is an ergodic set
  (`IsKernelErgodicSet`: a nonempty invariant set, `IsKernelInvariantSet`, with no proper nonempty
  invariant subset); every nonempty invariant set contains it, so it is the only ergodic set;
  `P(m, {y}) = δ` for `m ≠ 0` (in particular on `X = [y, ∞)`) and `P(m, {y}) ≥ δ` for all `m`;
  states off the lattice are transient, `Pⁿ(m, {m}) = 0` for `n ≥ 1`; and `X = [y, ∞)` is invariant.
* **Exercise 13.6(c)** (p. 402; `ex_13_6c`): `δ > 0`; Condition M holds with `N = 1`;
  `πᵢ = δ(1 − δ)^{i−1}` on `iy` (`currencyInvariant`, `currencyInvariant_singleton`) is a
  probability measure, is invariant (`currencyInvariant_invariant`) and is the unique invariant
  probability measure; `‖T*ⁿλ₀ − π‖ ≤ 2(1 − δ)ⁿ` for every `λ₀`; `∫ m dπ = y/δ`
  (`currencyInvariant_mean`), so the price level from (2) of §13.5 is `p = M/∫ m dπ = Mδ/y`.

**Correction** (Ex. 13.6(b), p. 401). "The ergodic set consists of `y` and its integer multiples"
needs `μ([0, ζ)) > 0`. This holds under the density condition of §13.5 ("`μ` is as before"), but
not for every `μ ≠ δ₀`: for `μ = δ₁` the cutoff is `ζ = β`, `δ = 1`, everybody spends everything
every period, and the ergodic set is `{y}` (`ex_13_6b_counterexample`). Part (c) is unaffected
(`π = δ_y` when `δ = 1`).

Formalisation notes. The process is defined on all of `ℝ` rather than on `X = [y, ∞)`; `X` is
invariant, and uniqueness of the invariant measure among all probability measures on `ℝ` is the
stronger statement. "`v` satisfies (1)" is the `IsGreatest` statement above; optimality of `v`
for the (unbounded) sequence problem, which the book does not ask for, is not formalised.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable (μ : Measure unitInterval)

/-- `H(ζ) = ∫ max{ζ, z′} μ(dz′)`. -/
noncomputable def maxInt (ζ : ℝ) : ℝ := ∫ z, max ζ (z : ℝ) ∂μ

variable {μ} [IsProbabilityMeasure μ]

/-- `z′ ↦ max{ζ, z′}` is integrable on `Z = [0, 1]`. -/
theorem integrable_max_unit (ζ : ℝ) : Integrable (fun z : unitInterval => max ζ (z : ℝ)) μ :=
  integrable_of_bounded (measurable_const.max measurable_subtype_coe) (M := |ζ| + 1) fun z => by
    have h0 := z.2.1
    have h1 := z.2.2
    rw [abs_le]
    constructor
    · linarith [neg_abs_le ζ, le_max_left ζ (z : ℝ)]
    · exact max_le (by linarith [le_abs_self ζ]) (by linarith [abs_nonneg ζ])

/-- `z′ ↦ z′` is integrable on `Z = [0, 1]`. -/
theorem integrable_coe_unit : Integrable (fun z : unitInterval => (z : ℝ)) μ :=
  integrable_of_bounded measurable_subtype_coe (M := 1) fun z => by
    rw [abs_of_nonneg z.2.1]
    exact z.2.2

/-- `H(ζ) ≥ ζ`. -/
theorem le_maxInt (ζ : ℝ) : ζ ≤ maxInt μ ζ := by
  have := integral_mono (integrable_const ζ) (integrable_max_unit (μ := μ) ζ) fun z =>
    le_max_left _ _
  simpa [maxInt] using this

/-- `H` is nondecreasing. -/
theorem maxInt_mono {ζ ζ' : ℝ} (h : ζ ≤ ζ') : maxInt μ ζ ≤ maxInt μ ζ' :=
  integral_mono (integrable_max_unit ζ) (integrable_max_unit ζ') fun _ => max_le_max_right _ h

/-- `H(ζ′) − H(ζ) ≤ ζ′ − ζ` for `ζ ≤ ζ′`. -/
theorem maxInt_sub_le {ζ ζ' : ℝ} (h : ζ ≤ ζ') : maxInt μ ζ' - maxInt μ ζ ≤ ζ' - ζ := by
  have hle : maxInt μ ζ' ≤ ∫ z, (max ζ (z : ℝ) + (ζ' - ζ)) ∂μ :=
    integral_mono (integrable_max_unit ζ') ((integrable_max_unit ζ).add (integrable_const _))
      fun z => max_le (by linarith [le_max_left ζ (z : ℝ)]) (by linarith [le_max_right ζ (z : ℝ)])
  rw [integral_add (integrable_max_unit ζ) (integrable_const _)] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  unfold maxInt at hle ⊢
  linarith

/-- `H` is `1`-Lipschitz, hence continuous. -/
theorem continuous_maxInt : Continuous (maxInt μ) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun a b => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  rcases le_total a b with hab | hab
  · have h1 := maxInt_sub_le (μ := μ) hab
    have h2 := maxInt_mono (μ := μ) hab
    constructor <;> linarith [abs_nonneg (a - b), neg_abs_le (a - b), le_abs_self (a - b)]
  · have h1 := maxInt_sub_le (μ := μ) hab
    have h2 := maxInt_mono (μ := μ) hab
    constructor <;> linarith [abs_nonneg (a - b), neg_abs_le (a - b), le_abs_self (a - b)]

omit [IsProbabilityMeasure μ] in
/-- `H(0) = ∫ z′ μ(dz′)`. -/
theorem maxInt_zero : maxInt μ 0 = ∫ z, (z : ℝ) ∂μ :=
  integral_congr_ae (Eventually.of_forall fun z => max_eq_right z.2.1)

/-- `H(ζ) = ζ` for `ζ ≥ 1`. -/
theorem maxInt_of_one_le {ζ : ℝ} (h : 1 ≤ ζ) : maxInt μ ζ = ζ := by
  have : maxInt μ ζ = ∫ _z, ζ ∂μ :=
    integral_congr_ae (Eventually.of_forall fun z => max_eq_left (z.2.2.trans h))
  simpa using this

/-- **The cutoff equation** `ζ = b ∫ max{ζ, z′} μ(dz′)` with `0 < b < 1` and `∫ z dμ > 0`
(i.e. `μ ≠ δ₀`) has a unique solution in `(0, 1)`: `h(ζ) = bH(ζ) − ζ` is continuous, strictly
decreasing (`h(ζ′) − h(ζ) ≤ (b − 1)(ζ′ − ζ)`), `h(0) = b∫z dμ > 0` and `h(1) = b − 1 < 0`. -/
theorem exists_unique_cutoff {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hE : 0 < ∫ z, (z : ℝ) ∂μ) :
    ∃! ζ : ℝ, ζ ∈ Ioo (0 : ℝ) 1 ∧ ζ = b * maxInt μ ζ := by
  set f : ℝ → ℝ := fun ζ => b * maxInt μ ζ - ζ with hf_def
  have hf : Continuous f := (continuous_const.mul continuous_maxInt).sub continuous_id
  have h0 : 0 < f 0 := by
    simp only [hf_def, maxInt_zero, sub_zero]
    positivity
  have h1 : f 1 < 0 := by
    simp only [hf_def, maxInt_of_one_le le_rfl, mul_one]
    linarith
  obtain ⟨ζ, hζ, hfζ⟩ := intermediate_value_Ioo' zero_le_one hf.continuousOn ⟨h1, h0⟩
  simp only [hf_def] at hfζ
  refine ⟨ζ, ⟨hζ, by linarith⟩, ?_⟩
  rintro ζ' ⟨-, h'⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hd := mul_le_mul_of_nonneg_left (maxInt_sub_le (μ := μ) hlt.le) hb0.le
    nlinarith [mul_pos (sub_pos.2 hb1) (sub_pos.2 hlt)]
  · have hd := mul_le_mul_of_nonneg_left (maxInt_sub_le (μ := μ) hlt.le) hb0.le
    nlinarith [mul_pos (sub_pos.2 hb1) (sub_pos.2 hlt)]

/-- If `ζ > 0` solves `ζ = bH(ζ)` with `b < 1`, then `δ = μ([ζ, 1]) > 0`: otherwise
`max{ζ, z′} = ζ` a.e., so `ζ = bζ`. -/
theorem delta_pos_of_cutoff {b ζ : ℝ} (hb1 : b < 1) (hζ : 0 < ζ) (h : ζ = b * maxInt μ ζ) :
    0 < μ.real {z : unitInterval | ζ ≤ (z : ℝ)} := by
  by_contra h0
  have hz : μ {z : unitInterval | ζ ≤ (z : ℝ)} = 0 :=
    (measureReal_eq_zero_iff).1 (le_antisymm (not_lt.1 h0) measureReal_nonneg)
  have hae : ∀ᵐ z : unitInterval ∂μ, max ζ (z : ℝ) = ζ := by
    have hnull : μ {z : unitInterval | ¬ max ζ (z : ℝ) = ζ} = 0 := by
      refine measure_mono_null (fun z hz => ?_) hz
      simp only [mem_ofPred_eq] at hz ⊢
      by_contra hlt
      exact hz (max_eq_left (not_le.1 hlt).le)
    exact ae_iff.2 hnull
  have hH : maxInt μ ζ = ζ := by
    rw [maxInt, integral_congr_ae hae]
    simp
  rw [hH] at h
  nlinarith

/-- The **density condition** of §13.3/§13.5 on `Z = [0, 1]`: `μ((a, b]) ≥ α(b − a)` for
`0 ≤ a < b ≤ 1`, with `α > 0`. -/
def UnitDensityLowerBound (μ : Measure unitInterval) (α : ℝ) : Prop :=
  0 < α ∧ ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    α * (b - a) ≤ μ.real {z : unitInterval | a < (z : ℝ) ∧ (z : ℝ) ≤ b}

/-- The consequences of the density condition used in §§13.6–13.7: `∫ z dμ > 0` (so `μ ≠ δ₀`),
`μ([0, ζ)) > 0` for `ζ > 0`, and `μ((a, 1]) > 0` for `a < 1`. -/
theorem unitDensityLowerBound_pos {α : ℝ} (h : UnitDensityLowerBound μ α) :
    0 < ∫ z, (z : ℝ) ∂μ ∧ (∀ ζ : ℝ, 0 < ζ → 0 < μ.real {z : unitInterval | (z : ℝ) < ζ}) ∧
      ∀ a : ℝ, a < 1 → 0 < μ {z : unitInterval | a < (z : ℝ)} := by
  obtain ⟨hα, hb⟩ := h
  have hlow : ∀ ζ : ℝ, 0 < ζ → 0 < μ.real {z : unitInterval | (z : ℝ) < ζ} := by
    intro ζ hζ
    set c := min ζ 1 / 2 with hc
    have hc0 : 0 < c := by positivity
    have hcζ : c < ζ := by
      have := min_le_left ζ 1
      linarith
    have hc1 : c ≤ 1 := by
      have := min_le_right ζ 1
      linarith
    have h1 := hb 0 c le_rfl hc0 hc1
    have h2 : μ.real {z : unitInterval | 0 < (z : ℝ) ∧ (z : ℝ) ≤ c} ≤
        μ.real {z : unitInterval | (z : ℝ) < ζ} :=
      measureReal_mono fun z (hz : 0 < (z : ℝ) ∧ (z : ℝ) ≤ c) =>
        show (z : ℝ) < ζ from hz.2.trans_lt hcζ
    nlinarith
  have hup : ∀ a : ℝ, a < 1 → 0 < μ {z : unitInterval | a < (z : ℝ)} := by
    intro a ha
    set a' := max a 0 with ha'
    have ha'1 : a' < 1 := max_lt ha one_pos
    have h1 := hb a' 1 (le_max_right a 0) ha'1 le_rfl
    have h2 : μ.real {z : unitInterval | a' < (z : ℝ) ∧ (z : ℝ) ≤ 1} ≤
        μ.real {z : unitInterval | a < (z : ℝ)} :=
      measureReal_mono fun z (hz : a' < (z : ℝ) ∧ (z : ℝ) ≤ 1) =>
        show a < (z : ℝ) from (le_max_left a 0).trans_lt hz.1
    have hpos : 0 < μ.real {z : unitInterval | a < (z : ℝ)} := by nlinarith
    exact pos_iff_ne_zero.2 fun h0 => by simp [measureReal_def, h0] at hpos
  refine ⟨?_, hlow, hup⟩
  refine (integral_pos_iff_support_of_nonneg (fun z => z.2.1) integrable_coe_unit).2
    ((hup 0 one_pos).trans_le (measure_mono fun z (hz : 0 < (z : ℝ)) => ?_))
  exact hz.ne'

/-! ### Exercise 13.6(a): the value function -/

/-- The value function of Exercise 13.6(a): `v(m, z) = max{ζ, z} m + A`, i.e. `ζm + A` if
`z < ζ` and `zm + A` if `z ≥ ζ`. -/
noncomputable def currencyValue (ζ A : ℝ) (m : ℝ) (z : unitInterval) : ℝ := max ζ (z : ℝ) * m + A

/-- The policy of Exercise 13.6(a): `g(m, z) = m + y` (spend nothing) if `z < ζ` and `g(m, z) = y`
(spend everything) if `z ≥ ζ`. -/
noncomputable def currencyPolicy (ζ y : ℝ) (m : ℝ) (z : unitInterval) : ℝ :=
  if (z : ℝ) < ζ then m + y else y

/-- `v` **satisfies the functional equation (1)** of §13.6 (p. 401): for every `m ≥ 0` and `z`,
`v(m, z)` is the maximum over `y ≤ m′ ≤ m + y` of `(m + y − m′)z + β ∫ v(m′, z′) μ(dz′)`. -/
def SatisfiesCurrencyBellman (β y : ℝ) (μ : Measure unitInterval)
    (v : ℝ → unitInterval → ℝ) : Prop :=
  ∀ m : ℝ, 0 ≤ m → ∀ z : unitInterval,
    IsGreatest ((fun m' => (m + y - m') * (z : ℝ) + β * ∫ z', v m' z' ∂μ) '' Icc y (m + y))
      (v m z)

/-- `∫ v(m′, z′) μ(dz′) = H(ζ) m′ + A`. -/
theorem integral_currencyValue (ζ A m' : ℝ) :
    ∫ z', currencyValue ζ A m' z' ∂μ = maxInt μ ζ * m' + A := by
  unfold currencyValue
  rw [integral_add ((integrable_max_unit ζ).mul_const m') (integrable_const A), integral_mul_const]
  simp [maxInt]

/-- **Exercise 13.6(a), verification.** If `ζ = βH(ζ)` and `A = ζy + βA` (i.e.
`A = ζy/(1 − β)`), then `v(m, z) = max{ζ, z} m + A` satisfies (1), and the maximum is attained at
the policy `g`: the objective is `(m + y)z + (ζ − z)m′ + βA`, linear in `m′`. -/
theorem currency_bellman {β y ζ A : ℝ} (hcut : ζ = β * maxInt μ ζ) (hA : A = ζ * y + β * A) :
    SatisfiesCurrencyBellman β y μ (currencyValue ζ A) ∧
      ∀ m : ℝ, 0 ≤ m → ∀ z : unitInterval,
        currencyPolicy ζ y m z ∈ Icc y (m + y) ∧
          (m + y - currencyPolicy ζ y m z) * (z : ℝ) +
              β * ∫ z', currencyValue ζ A (currencyPolicy ζ y m z) z' ∂μ =
            currencyValue ζ A m z := by
  have hobj : ∀ m m' : ℝ, ∀ z : unitInterval,
      (m + y - m') * (z : ℝ) + β * ∫ z', currencyValue ζ A m' z' ∂μ =
        (m + y) * z + (ζ - z) * m' + β * A := by
    intro m m' z
    rw [integral_currencyValue]
    linear_combination (-m') * hcut
  have hpol : ∀ m : ℝ, 0 ≤ m → ∀ z : unitInterval,
      currencyPolicy ζ y m z ∈ Icc y (m + y) ∧
        (m + y - currencyPolicy ζ y m z) * (z : ℝ) +
            β * ∫ z', currencyValue ζ A (currencyPolicy ζ y m z) z' ∂μ =
          currencyValue ζ A m z := by
    intro m hm z
    rw [hobj]
    unfold currencyPolicy currencyValue
    by_cases hz : (z : ℝ) < ζ
    · simp only [hz, ↓reduceIte, max_eq_left hz.le]
      exact ⟨⟨by linarith, le_rfl⟩, by linear_combination (-1 : ℝ) * hA⟩
    · simp only [hz, ↓reduceIte, max_eq_right (not_lt.1 hz)]
      exact ⟨⟨le_rfl, by linarith⟩, by linear_combination (-1 : ℝ) * hA⟩
  refine ⟨fun m hm z => ⟨⟨_, (hpol m hm z).1, (hpol m hm z).2⟩, ?_⟩, hpol⟩
  rintro _ ⟨m', ⟨h1, h2⟩, rfl⟩
  simp only
  rw [hobj]
  unfold currencyValue
  by_cases hz : (z : ℝ) < ζ
  · rw [max_eq_left hz.le]
    nlinarith
  · rw [max_eq_right (not_lt.1 hz)]
    nlinarith

/-- **Exercise 13.6(a).** There is a unique `ζ ∈ (0, 1)` with `ζ = β ∫ max{ζ, z′} μ(dz′)`; with
`A = ζy/(1 − β) > 0`, `v(m, z) = max{ζ, z} m + A` satisfies (1), the maximum being attained at
`m′ = m + y` if `z < ζ` and at `m′ = y` if `z ≥ ζ`. -/
theorem ex_13_6a {β y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y)
    (hE : 0 < ∫ z, (z : ℝ) ∂μ) :
    ∃! ζ : ℝ, ζ ∈ Ioo (0 : ℝ) 1 ∧ ζ = β * maxInt μ ζ ∧
      0 < ζ * y / (1 - β) ∧ SatisfiesCurrencyBellman β y μ (currencyValue ζ (ζ * y / (1 - β))) ∧
      ∀ m : ℝ, 0 ≤ m → ∀ z : unitInterval,
        currencyPolicy ζ y m z ∈ Icc y (m + y) ∧
          (m + y - currencyPolicy ζ y m z) * (z : ℝ) +
              β * ∫ z', currencyValue ζ (ζ * y / (1 - β)) (currencyPolicy ζ y m z) z' ∂μ =
            currencyValue ζ (ζ * y / (1 - β)) m z := by
  obtain ⟨ζ, ⟨hζ, hcut⟩, huniq⟩ := exists_unique_cutoff hβ0 hβ1 hE
  have h1β : (1 - β) ≠ 0 := by linarith
  have hA : ζ * y / (1 - β) = ζ * y + β * (ζ * y / (1 - β)) := by
    field_simp
    ring
  refine ⟨ζ, ⟨hζ, hcut, div_pos (mul_pos hζ.1 hy) (by linarith), currency_bellman hcut hA⟩,
    fun ζ' h' => huniq ζ' ⟨h'.1, h'.2.1⟩⟩

/-- **Exercise 13.6(a), characterisation of `ζ` and `A`.** Conversely, if `ζ ≥ 0` and
`v(m, z) = max{ζ, z} m + A` satisfies (1), then `ζ = βH(ζ)` and `A = ζy/(1 − β)`, and `ζ` lies in
`(0, 1)` (so it is the cutoff of `ex_13_6a`). Only the shock `z = 0` is used: there the objective
`β(H(ζ)m′ + A)` is maximised at `m′ = m + y`, so `ζm + A = βH(ζ)(m + y) + βA` for all `m ≥ 0`. -/
theorem ex_13_6a_unique {β y ζ A : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hE : 0 < ∫ z, (z : ℝ) ∂μ)
    (hζ : 0 ≤ ζ) (h : SatisfiesCurrencyBellman β y μ (currencyValue ζ A)) :
    ζ = β * maxInt μ ζ ∧ A = ζ * y / (1 - β) ∧ ζ ∈ Ioo (0 : ℝ) 1 := by
  have hH0 : 0 ≤ maxInt μ ζ := hζ.trans (le_maxInt ζ)
  have key : ∀ m : ℝ, 0 ≤ m → ζ * m + A = β * maxInt μ ζ * (m + y) + β * A := by
    intro m hm
    obtain ⟨⟨m', ⟨h1, h2⟩, hm'⟩, hub⟩ := h m hm 0
    have hub' := hub ⟨m + y, ⟨by linarith, le_rfl⟩, rfl⟩
    simp only [Set.Icc.coe_zero, mul_zero, zero_add, integral_currencyValue] at hm' hub'
    simp only [currencyValue, Set.Icc.coe_zero, max_eq_left hζ] at hm' hub'
    have : β * maxInt μ ζ * m' ≤ β * maxInt μ ζ * (m + y) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hβ0.le hH0)
    nlinarith
  have k0 := key 0 le_rfl
  have k1 := key 1 zero_le_one
  have hcut : ζ = β * maxInt μ ζ := by linarith
  have h1β : (1 - β) ≠ 0 := by linarith
  refine ⟨hcut, by field_simp; linear_combination k0 - y * hcut, ?_, ?_⟩
  · rcases hζ.lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, maxInt_zero] at hcut
      nlinarith
  · by_contra h1
    rw [maxInt_of_one_le (not_lt.1 h1)] at hcut
    nlinarith

/-! ### The transition function defined by a cutoff policy and `μ` -/

omit [IsProbabilityMeasure μ] in
/-- The map `(m, z) ↦ φ(m)` if `z < ζ`, `b` if `z ≥ ζ` is measurable. -/
theorem measurable_cutoffPolicy (ζ : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) (b : ℝ) :
    Measurable fun p : ℝ × unitInterval => if (p.2 : ℝ) < ζ then φ p.1 else b :=
  Measurable.ite (measurableSet_lt (measurable_subtype_coe.comp measurable_snd) measurable_const)
    (hφ.comp measurable_fst) measurable_const

/-- The transition function defined by the cutoff policy `g(m, z) = φ(m)` if `z < ζ`, `b` if
`z ≥ ζ`, and the shock distribution `μ` (SLP Theorem 8.9): `P(m, A) = μ{z : g(m, z) ∈ A}`. -/
noncomputable def cutoffKernel (μ : Measure unitInterval) [IsFiniteMeasure μ] (ζ : ℝ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) (b : ℝ) : Kernel ℝ ℝ where
  toFun m := μ.map fun z : unitInterval => if (z : ℝ) < ζ then φ m else b
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have hG := measurable_cutoffPolicy ζ hφ b
    have : ∀ m, (μ.map fun z : unitInterval => if (z : ℝ) < ζ then φ m else b) A =
        μ (Prod.mk m ⁻¹' ((fun p : ℝ × unitInterval => if (p.2 : ℝ) < ζ then φ p.1 else b) ⁻¹'
          A)) := fun m => by
      have hg : Measurable fun z : unitInterval => if (z : ℝ) < ζ then φ m else b :=
        hG.comp measurable_prodMk_left
      rw [Measure.map_apply hg hA]
      rfl
    simp_rw [this]
    exact measurable_measure_prodMk_left (hG hA)

/-- `P(m, ·) = μ([0, ζ)) δ_{φ(m)} + μ([ζ, 1]) δ_b`. -/
theorem cutoffKernel_apply (ζ : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) (b m : ℝ) :
    cutoffKernel μ ζ hφ b m = μ {z | (z : ℝ) < ζ} • Measure.dirac (φ m) +
      μ {z | ζ ≤ (z : ℝ)} • Measure.dirac b := by
  have hG := measurable_cutoffPolicy ζ hφ b
  have hs : MeasurableSet {z : unitInterval | (z : ℝ) < ζ} :=
    measurableSet_lt measurable_subtype_coe measurable_const
  have hc : {z : unitInterval | ζ ≤ (z : ℝ)} = {z : unitInterval | (z : ℝ) < ζ}ᶜ := by
    ext z
    simp
  ext A hA
  change (μ.map fun z : unitInterval => if (z : ℝ) < ζ then φ m else b) A = _
  have hg : Measurable fun z : unitInterval => if (z : ℝ) < ζ then φ m else b :=
    hG.comp measurable_prodMk_left
  rw [Measure.map_apply hg hA, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ hA, hc]
  by_cases h1 : φ m ∈ A <;> by_cases h2 : b ∈ A
  · have : ((fun z : unitInterval => if (z : ℝ) < ζ then φ m else b) ⁻¹' A) = univ := by
      ext z
      by_cases hz : (z : ℝ) < ζ <;> simp [hz, h1, h2]
    rw [this, ← measure_add_measure_compl hs]
    simp [h1, h2]
  · have : ((fun z : unitInterval => if (z : ℝ) < ζ then φ m else b) ⁻¹' A) =
        {z : unitInterval | (z : ℝ) < ζ} := by
      ext z
      by_cases hz : (z : ℝ) < ζ <;> simp [hz, h1, h2]
    rw [this]
    simp [h1, h2]
  · have : ((fun z : unitInterval => if (z : ℝ) < ζ then φ m else b) ⁻¹' A) =
        {z : unitInterval | (z : ℝ) < ζ}ᶜ := by
      ext z
      by_cases hz : (z : ℝ) < ζ <;> simp [hz, h1, h2]
    rw [this]
    simp [h1, h2]
  · have : ((fun z : unitInterval => if (z : ℝ) < ζ then φ m else b) ⁻¹' A) = ∅ := by
      ext z
      by_cases hz : (z : ℝ) < ζ <;> simp [hz, h1, h2]
    rw [this]
    simp [h1, h2]

/-- The cutoff kernel is a Markov kernel (a transition function). -/
theorem isMarkovKernel_cutoffKernel (ζ : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) (b : ℝ) :
    IsMarkovKernel (cutoffKernel μ ζ hφ b) :=
  ⟨fun m => inferInstanceAs (IsProbabilityMeasure
    (μ.map fun z : unitInterval => if (z : ℝ) < ζ then φ m else b))⟩

/-- `μ([0, ζ)) + μ([ζ, 1]) = 1`. -/
theorem measure_lt_add_measure_ge (ζ : ℝ) :
    μ {z : unitInterval | (z : ℝ) < ζ} + μ {z | ζ ≤ (z : ℝ)} = 1 := by
  have hs : MeasurableSet {z : unitInterval | (z : ℝ) < ζ} :=
    measurableSet_lt measurable_subtype_coe measurable_const
  have hc : {z : unitInterval | ζ ≤ (z : ℝ)} = {z : unitInterval | (z : ℝ) < ζ}ᶜ := by
    ext z
    simp
  rw [hc, measure_add_measure_compl hs, measure_univ]

/-- `μ([0, ζ)) = 1 − δ` in real terms, `δ = μ([ζ, 1])`. -/
theorem measureReal_lt_eq (ζ : ℝ) :
    μ.real {z : unitInterval | (z : ℝ) < ζ} = 1 - μ.real {z | ζ ≤ (z : ℝ)} := by
  have hs : MeasurableSet {z : unitInterval | ζ ≤ (z : ℝ)} :=
    measurableSet_le measurable_const measurable_subtype_coe
  have hc : {z : unitInterval | (z : ℝ) < ζ} = {z : unitInterval | ζ ≤ (z : ℝ)}ᶜ := by
    ext z
    simp
  rw [hc, probReal_compl_eq_one_sub hs]

/-- If `b ∈ A`, then `P(m, A) ≥ μ([ζ, 1])`. -/
theorem cutoffKernel_ge_of_mem (ζ : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) {b : ℝ} (m : ℝ)
    {A : Set ℝ} (hb : b ∈ A) : μ {z | ζ ≤ (z : ℝ)} ≤ cutoffKernel μ ζ hφ b m A := by
  rw [cutoffKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem hb, smul_eq_mul, smul_eq_mul, mul_one]
  exact le_add_self

/-- If `φ(m) ∈ A`, then `P(m, A) ≥ μ([0, ζ))`. -/
theorem cutoffKernel_ge_of_mem' (ζ : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) (b : ℝ) {m : ℝ}
    {A : Set ℝ} (hm : φ m ∈ A) : μ {z | (z : ℝ) < ζ} ≤ cutoffKernel μ ζ hφ b m A := by
  rw [cutoffKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem hm, smul_eq_mul, smul_eq_mul, mul_one]
  exact le_self_add

/-- If `δ = μ([ζ, 1]) > 0`, the cutoff kernel satisfies **Condition M** with `N = 1` and
`ε = δ`: `P(m, {b}) ≥ δ` for all `m`, and `b` lies in `A` or in `Aᶜ`. -/
theorem cutoffKernel_conditionM (ζ : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) (b : ℝ)
    (hδ : 0 < μ.real {z : unitInterval | ζ ≤ (z : ℝ)}) :
    ConditionMFor (cutoffKernel μ ζ hφ b) 1 (μ.real {z : unitInterval | ζ ≤ (z : ℝ)}) := by
  have := isMarkovKernel_cutoffKernel (μ := μ) ζ hφ b
  refine ⟨le_rfl, hδ, fun A _ => ?_⟩
  rw [kpow_one]
  by_cases hb : b ∈ A
  · exact Or.inl fun m => ENNReal.toReal_mono (measure_ne_top _ _)
      (cutoffKernel_ge_of_mem ζ hφ m hb)
  · exact Or.inr fun m => ENNReal.toReal_mono (measure_ne_top _ _)
      (cutoffKernel_ge_of_mem ζ hφ m (A := Aᶜ) hb)

/-- `Pⁿ⁺¹(m, B) = μ([0, ζ)) Pⁿ(φ(m), B) + μ([ζ, 1]) Pⁿ(b, B)`. -/
theorem kpow_succ_cutoffKernel (ζ : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) (b : ℝ) (n : ℕ) (m : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    kpow (cutoffKernel μ ζ hφ b) (n + 1) m B =
      μ {z | (z : ℝ) < ζ} * kpow (cutoffKernel μ ζ hφ b) n (φ m) B +
        μ {z | ζ ≤ (z : ℝ)} * kpow (cutoffKernel μ ζ hφ b) n b B := by
  rw [kpow, Kernel.comp_apply' _ _ _ hB, cutoffKernel_apply, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac,
    smul_eq_mul, smul_eq_mul]

omit [IsProbabilityMeasure μ] in
/-- Under Condition M with `N = 1`, an invariant probability measure `π` is the only one, and
`‖T*ⁿλ₀ − π‖ ≤ 2(1 − ε)ⁿ` for every initial `λ₀` (Theorem 11.12). -/
theorem invariant_unique_of_conditionM_one {S : Type*} [MeasurableSpace S] [Nonempty S]
    {κ : Kernel S S} [IsMarkovKernel κ] {ε : ℝ} (hM : ConditionMFor κ 1 ε) (π : Measure S)
    [IsProbabilityMeasure π] (hπ : adjointOp κ π = π) :
    (∀ l : Measure S, IsProbabilityMeasure l → adjointOp κ l = l → l = π) ∧
      ∀ (l₀ : Measure S) [IsProbabilityMeasure l₀] (n : ℕ),
        tvDist (adjointOp (kpow κ n) l₀) π ≤ 2 * (1 - ε) ^ n := by
  obtain ⟨lstar, hls, -, -, -, hconv⟩ := theorem_11_12 hM
  obtain ⟨-, hε, hMA⟩ := hM
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hε1 : ε ≤ 1 := by
    have := isMarkov_kpow (κ := κ) 1
    rcases hMA ∅ MeasurableSet.empty with h | h
    · have := h s₀
      simp at this
      linarith
    · have := h s₀
      simp at this
      linarith
  have hlim : Tendsto (fun n : ℕ => 2 * (1 - ε) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - ε) (by linarith)
      (by linarith)).const_mul 2
  have hinv : ∀ l : Measure S, IsProbabilityMeasure l → adjointOp κ l = l → l = lstar := by
    intro l hl hfix
    refine eq_of_tvDist_eq_zero (ge_of_tendsto' hlim fun n => ?_)
    have h := hconv l n
    rw [Nat.div_one, ← adjointOp_iterate, Function.iterate_fixed hfix] at h
    exact h
  have hπs : π = lstar := hinv π inferInstance hπ
  subst hπs
  refine ⟨hinv, fun l₀ _ n => ?_⟩
  have h := hconv l₀ n
  rwa [Nat.div_one] at h

/-! ### Exercise 13.6(b): the ergodic set -/

/-- `A` is an **invariant set** of `P` (SLP §11.1): measurable, with `P(s, A) = 1` for `s ∈ A`. -/
def IsKernelInvariantSet {S : Type*} [MeasurableSpace S] (κ : Kernel S S) (A : Set S) : Prop :=
  MeasurableSet A ∧ ∀ s ∈ A, κ s A = 1

/-- `E` is an **ergodic set** of `P` (SLP §11.1): a nonempty invariant set with no proper
nonempty invariant subset. -/
def IsKernelErgodicSet {S : Type*} [MeasurableSpace S] (κ : Kernel S S) (E : Set S) : Prop :=
  IsKernelInvariantSet κ E ∧ E.Nonempty ∧ ∀ A ⊆ E, A.Nonempty → IsKernelInvariantSet κ A → A = E

/-- The transition function of §13.6 on `X = [y, ∞)` (here on all of `ℝ`): from `m`, the next
state is `g(m, z′) = m + y` if `z′ < ζ` and `y` if `z′ ≥ ζ`. -/
noncomputable def currencyKernel (μ : Measure unitInterval) [IsFiniteMeasure μ] (ζ y : ℝ) :
    Kernel ℝ ℝ :=
  cutoffKernel μ ζ (measurable_add_const y) y

/-- The lattice `{iy : i ≥ 1}`. -/
def currencyLattice (y : ℝ) : Set ℝ := range fun i : ℕ => ((i : ℝ) + 1) * y

/-- The lattice is measurable (countable). -/
theorem measurableSet_currencyLattice (y : ℝ) : MeasurableSet (currencyLattice y) :=
  (countable_range _).measurableSet

/-- `y` lies in the lattice. -/
theorem mem_currencyLattice_self (y : ℝ) : y ∈ currencyLattice y := ⟨0, by simp⟩

/-- The lattice is closed under `m ↦ m + y`. -/
theorem add_mem_currencyLattice {y m : ℝ} (hm : m ∈ currencyLattice y) :
    m + y ∈ currencyLattice y := by
  obtain ⟨i, rfl⟩ := hm
  exact ⟨i + 1, by push_cast; ring⟩

/-- In an invariant set, every point charged by `P(s, ·)` (`s ∈ A`) lies in `A`. -/
theorem mem_of_kernelInvariantSet {S : Type*} [MeasurableSpace S] {κ : Kernel S S}
    [IsMarkovKernel κ] {A : Set S} (hA : IsKernelInvariantSet κ A) {s x : S} (hs : s ∈ A)
    (hx : κ s {x} ≠ 0) : x ∈ A := by
  by_contra hxA
  have h1 : κ s Aᶜ = 0 := by
    rw [prob_compl_eq_one_sub hA.1, hA.2 s hs, tsub_self]
  exact hx (measure_mono_null (singleton_subset_iff.2 hxA) h1)

/-- **Exercise 13.6(b).** Let `δ = μ([ζ, 1]) > 0` and suppose `μ([0, ζ)) > 0` (which holds under
the density condition of §13.5). Then:
* the lattice `{iy : i ≥ 1}` is an ergodic set;
* every nonempty invariant set contains it (so it is the only ergodic set);
* `P(m, {y}) = δ` for every `m ≠ 0` (every state reaches `y`), and `P(m, {y}) ≥ δ` for all `m`;
* states off the lattice are transient: `Pⁿ(m, {m}) = 0` for `m ∉ {iy}` and `n ≥ 1`;
* `X = [y, ∞)` is invariant: `P(m, [y, ∞)) = 1` for `m ≥ 0`. -/
theorem ex_13_6b {ζ y : ℝ} (hy : 0 < y) (hδ : 0 < μ.real {z : unitInterval | ζ ≤ (z : ℝ)})
    (hp : 0 < μ.real {z : unitInterval | (z : ℝ) < ζ}) :
    IsKernelErgodicSet (currencyKernel μ ζ y) (currencyLattice y) ∧
      (∀ A : Set ℝ, IsKernelInvariantSet (currencyKernel μ ζ y) A → A.Nonempty →
        currencyLattice y ⊆ A) ∧
      (∀ m : ℝ, m ≠ 0 → (currencyKernel μ ζ y m).real {y} = μ.real {z | ζ ≤ (z : ℝ)}) ∧
      (∀ m : ℝ, μ.real {z | ζ ≤ (z : ℝ)} ≤ (currencyKernel μ ζ y m).real {y}) ∧
      (∀ m : ℝ, m ∉ currencyLattice y → ∀ n : ℕ, 1 ≤ n →
        kpow (currencyKernel μ ζ y) n m {m} = 0) ∧
      ∀ m : ℝ, 0 ≤ m → currencyKernel μ ζ y m (Ici y) = 1 := by
  unfold currencyKernel
  set κ := cutoffKernel μ ζ (measurable_add_const y) y with hκ
  have hMk : IsMarkovKernel κ := isMarkovKernel_cutoffKernel (μ := μ) ζ (measurable_add_const y) y
  have hδ' : μ {z : unitInterval | ζ ≤ (z : ℝ)} ≠ 0 := fun h => by
    simp [measureReal_def, h] at hδ
  have hp' : μ {z : unitInterval | (z : ℝ) < ζ} ≠ 0 := fun h => by
    simp [measureReal_def, h] at hp
  have hsum := measure_lt_add_measure_ge (μ := μ) ζ
  -- every nonempty invariant set contains the lattice
  have hcontains : ∀ A : Set ℝ, IsKernelInvariantSet κ A → A.Nonempty → currencyLattice y ⊆ A := by
    intro A hA ⟨a, ha⟩
    have hyA : y ∈ A := mem_of_kernelInvariantSet hA ha fun h0 => hδ' (le_zero_iff.1
      (h0 ▸ cutoffKernel_ge_of_mem ζ (measurable_add_const y) a (mem_singleton y)))
    have hstep : ∀ s ∈ A, s + y ∈ A := fun s hs => mem_of_kernelInvariantSet hA hs fun h0 => hp'
      (le_zero_iff.1 (h0 ▸ cutoffKernel_ge_of_mem' ζ (measurable_add_const y) y
        (mem_singleton (s + y))))
    rintro _ ⟨i, rfl⟩
    induction i with
    | zero => simpa using hyA
    | succ i ih =>
      have := hstep _ ih
      convert this using 1
      push_cast
      ring
  have hLinv : IsKernelInvariantSet κ (currencyLattice y) := by
    refine ⟨measurableSet_currencyLattice y, fun m hm => ?_⟩
    rw [hκ, cutoffKernel_apply, Measure.add_apply, Measure.smul_apply,
      Measure.smul_apply, Measure.dirac_apply_of_mem (add_mem_currencyLattice hm),
      Measure.dirac_apply_of_mem (mem_currencyLattice_self y)]
    simpa using hsum
  refine ⟨⟨hLinv, ⟨y, mem_currencyLattice_self y⟩, fun A hAL hAne hA =>
    subset_antisymm hAL (hcontains A hA hAne)⟩, hcontains, fun m hm => ?_, fun m => ?_,
    fun m hm n hn => ?_, fun m hm => ?_⟩
  · rw [hκ, cutoffKernel_apply, measureReal_def, Measure.add_apply,
      Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply, Measure.dirac_apply]
    have : m + y ∉ ({y} : Set ℝ) := by simpa using hm
    simp [this, measureReal_def]
  · exact ENNReal.toReal_mono (measure_ne_top _ _)
      (cutoffKernel_ge_of_mem ζ (measurable_add_const y) m (mem_singleton y))
  · -- `Pⁿ(m, ·)` is carried by the lattice and the point `m + ny`
    have key : ∀ n : ℕ, ∀ m : ℝ,
        kpow κ n m (currencyLattice y ∪ {m + n * y})ᶜ = 0 := by
      intro n
      induction n with
      | zero =>
        intro m
        simp [kpow, Kernel.id_apply, Measure.dirac_apply]
      | succ n ih =>
        intro m
        have hB : MeasurableSet (currencyLattice y ∪ {m + ((n + 1 : ℕ) : ℝ) * y})ᶜ :=
          ((measurableSet_currencyLattice y).union (measurableSet_singleton _)).compl
        rw [hκ, kpow_succ_cutoffKernel _ _ _ _ _ hB, ← hκ]
        have h1 := measure_mono_null (μ := kpow κ n (m + y))
          (s := (currencyLattice y ∪ {m + ((n + 1 : ℕ) : ℝ) * y})ᶜ)
          (compl_subset_compl.2 (union_subset_union_right _ (by
            rw [singleton_subset_iff, mem_singleton_iff]
            push_cast
            ring))) (ih (m + y))
        have h2 := measure_mono_null (μ := kpow κ n y)
          (s := (currencyLattice y ∪ {m + ((n + 1 : ℕ) : ℝ) * y})ᶜ)
          (compl_subset_compl.2 (union_subset subset_union_left (singleton_subset_iff.2
            (mem_union_left _ (show y + (n : ℝ) * y ∈ currencyLattice y from
              ⟨n, by ring⟩))))) (ih y)
        rw [h1, h2, mul_zero, mul_zero, add_zero]
    refine measure_mono_null (singleton_subset_iff.2 ?_) (key n m)
    simp only [mem_compl_iff, mem_union, mem_singleton_iff, not_or]
    refine ⟨hm, fun h => ?_⟩
    have : (n : ℝ) * y = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (by exact_mod_cast h0 : n = 0) (by omega)
    · linarith
  · rw [hκ, cutoffKernel_apply, Measure.add_apply, Measure.smul_apply,
      Measure.smul_apply, Measure.dirac_apply_of_mem (show m + y ∈ Ici y by simp [hm]),
      Measure.dirac_apply_of_mem (show y ∈ Ici y from mem_Ici.2 le_rfl)]
    simpa using hsum

/-- **Exercise 13.6(b), missing hypothesis.** Without `μ([0, ζ)) > 0` the claim fails: for
`μ = δ₁` the cutoff is `ζ = β` (`β = βH(β)`, `H(β) = 1`), `μ([0, ζ)) = 0`, so everybody spends
everything every period and `{y}` is a proper invariant subset of `{iy : i ≥ 1}`: the lattice is
not an ergodic set (the ergodic set is `{y}`). -/
theorem ex_13_6b_counterexample {β y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) :
    β ∈ Ioo (0 : ℝ) 1 ∧ β = β * maxInt (Measure.dirac (1 : unitInterval)) β ∧
      ¬ IsKernelErgodicSet (currencyKernel (Measure.dirac (1 : unitInterval)) β y)
        (currencyLattice y) := by
  have hH : maxInt (Measure.dirac (1 : unitInterval)) β = 1 := by
    rw [maxInt, integral_dirac]
    simp [hβ1.le]
  refine ⟨⟨hβ0, hβ1⟩, by rw [hH, mul_one], fun ⟨_, _, hmin⟩ => ?_⟩
  have hinv : IsKernelInvariantSet (currencyKernel (Measure.dirac (1 : unitInterval)) β y) {y} := by
    refine ⟨measurableSet_singleton y, fun m hm => ?_⟩
    rw [mem_singleton_iff] at hm
    subst hm
    rw [currencyKernel, cutoffKernel_apply, Measure.add_apply, Measure.smul_apply,
      Measure.smul_apply, Measure.dirac_apply, Measure.dirac_apply, Measure.dirac_apply,
      Measure.dirac_apply]
    have h1 : (1 : unitInterval) ∉ {z : unitInterval | (z : ℝ) < β} := by simp [hβ1.le]
    have h2 : (1 : unitInterval) ∈ {z : unitInterval | β ≤ (z : ℝ)} := by simp [hβ1.le]
    rw [indicator_of_notMem h1, indicator_of_mem h2]
    simp
  have := hmin {y} (singleton_subset_iff.2 (mem_currencyLattice_self y)) (singleton_nonempty y)
    hinv
  have h2y : 2 * y ∈ currencyLattice y := ⟨1, by norm_num⟩
  rw [← this, mem_singleton_iff] at h2y
  linarith

/-- **Exercise 13.6(b) under the density condition of §13.5.** If `μ((a, b]) ≥ α(b − a)`, then
for the cutoff `ζ ∈ (0, 1)` both `δ = μ([ζ, 1])` and `μ([0, ζ))` are positive, so all conclusions
of `ex_13_6b` hold; in particular `{iy : i ≥ 1}` is the ergodic set. -/
theorem ex_13_6b_density {α β y ζ : ℝ} (hα : UnitDensityLowerBound μ α) (hβ1 : β < 1) (hy : 0 < y)
    (hζ : 0 < ζ) (hcut : ζ = β * maxInt μ ζ) :
    IsKernelErgodicSet (currencyKernel μ ζ y) (currencyLattice y) ∧
      (∀ A : Set ℝ, IsKernelInvariantSet (currencyKernel μ ζ y) A → A.Nonempty →
        currencyLattice y ⊆ A) ∧
      (∀ m : ℝ, m ≠ 0 → (currencyKernel μ ζ y m).real {y} = μ.real {z | ζ ≤ (z : ℝ)}) ∧
      (∀ m : ℝ, μ.real {z | ζ ≤ (z : ℝ)} ≤ (currencyKernel μ ζ y m).real {y}) ∧
      (∀ m : ℝ, m ∉ currencyLattice y → ∀ n : ℕ, 1 ≤ n →
        kpow (currencyKernel μ ζ y) n m {m} = 0) ∧
      ∀ m : ℝ, 0 ≤ m → currencyKernel μ ζ y m (Ici y) = 1 :=
  ex_13_6b hy (delta_pos_of_cutoff hβ1 hζ hcut) ((unitDensityLowerBound_pos hα).2.1 ζ hζ)

/-! ### Exercise 13.6(c): the invariant distribution -/

/-- The geometric distribution on the lattice: mass `πᵢ = δ(1 − δ)^{i−1}` at `iy`, `i ≥ 1`
(indexed here from `i = 0` at `y`). -/
noncomputable def currencyInvariant (δ y : ℝ) : Measure ℝ :=
  Measure.sum fun i : ℕ => ENNReal.ofReal (δ * (1 - δ) ^ i) • Measure.dirac (((i : ℝ) + 1) * y)

/-- `∑ᵢ δ(1 − δ)ⁱ = 1` for `0 < δ ≤ 1`. -/
theorem hasSum_geometric_weights {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) :
    HasSum (fun i : ℕ => δ * (1 - δ) ^ i) 1 := by
  have := (hasSum_geometric_of_lt_one (r := 1 - δ) (by linarith) (by linarith)).mul_left δ
  convert this using 1
  rw [sub_sub_cancel, mul_inv_cancel₀ h0.ne']

/-- The weights `δ(1 − δ)ⁱ` sum to `1` in `ℝ≥0∞`. -/
theorem tsum_ofReal_weights {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) :
    ∑' i : ℕ, ENNReal.ofReal (δ * (1 - δ) ^ i) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg h0.le (pow_nonneg (by linarith) _))
    (hasSum_geometric_weights h0 h1).summable, (hasSum_geometric_weights h0 h1).tsum_eq,
    ENNReal.ofReal_one]

/-- The geometric distribution is a probability measure. -/
theorem isProbabilityMeasure_currencyInvariant {δ : ℝ} (y : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1) :
    IsProbabilityMeasure (currencyInvariant δ y) :=
  ⟨by simp [currencyInvariant, Measure.sum_apply _ MeasurableSet.univ, tsum_ofReal_weights h0 h1]⟩

/-- `π({iy}) = δ(1 − δ)^{i−1}` (here `π({(i + 1)y}) = δ(1 − δ)ⁱ`). -/
theorem currencyInvariant_singleton {δ y : ℝ} (hy : 0 < y) (i : ℕ) :
    currencyInvariant δ y {((i : ℝ) + 1) * y} = ENNReal.ofReal (δ * (1 - δ) ^ i) := by
  rw [currencyInvariant, Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single i]
  · simp
  · intro j hj
    have hne : ((j : ℝ) + 1) * y ∉ ({((i : ℝ) + 1) * y} : Set ℝ) := by
      rw [mem_singleton_iff]
      intro h
      have := mul_right_cancel₀ hy.ne' h
      exact hj (by exact_mod_cast (by linarith : (j : ℝ) = i))
    rw [Measure.smul_apply, Measure.dirac_apply, indicator_of_notMem hne]
    simp

/-- The shift identity behind invariance: if `Wᵢ P = Wᵢ₊₁`, `W₀ = D` and `∑ Wᵢ = 1`, then
`∑ Wᵢ (P aᵢ₊₁ + D a₀) = ∑ Wᵢ aᵢ`. -/
theorem geometric_tsum_shift (W a : ℕ → ℝ≥0∞) (P D : ℝ≥0∞) (hW : ∀ i, W i * P = W (i + 1))
    (hW0 : W 0 = D) (hsum : ∑' i, W i = 1) :
    ∑' i, W i * (P * a (i + 1) + D * a 0) = ∑' i, W i * a i := by
  calc ∑' i, W i * (P * a (i + 1) + D * a 0)
      = ∑' i, (W (i + 1) * a (i + 1) + W i * (D * a 0)) := by
        refine tsum_congr fun i => ?_
        rw [mul_add, ← mul_assoc, hW]
    _ = ∑' i, W (i + 1) * a (i + 1) + (∑' i, W i) * (D * a 0) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ = W 0 * a 0 + ∑' i, W (i + 1) * a (i + 1) := by rw [hsum, one_mul, hW0, add_comm]
    _ = ∑' i, W i * a i := (tsum_eq_zero_add' (f := fun i => W i * a i) ENNReal.summable).symm

/-- **Invariance.** With `δ = μ([ζ, 1]) > 0`, the geometric distribution is invariant:
`π₁ = δ` (every spender lands at `y`) and `πᵢ₊₁ = (1 − δ)πᵢ` (savers move up one rung). -/
theorem currencyInvariant_invariant {ζ y : ℝ}
    (hδ : 0 < μ.real {z : unitInterval | ζ ≤ (z : ℝ)}) :
    adjointOp (currencyKernel μ ζ y) (currencyInvariant (μ.real {z | ζ ≤ (z : ℝ)}) y) =
      currencyInvariant (μ.real {z | ζ ≤ (z : ℝ)}) y := by
  set δ := μ.real {z : unitInterval | ζ ≤ (z : ℝ)} with hδdef
  have h1 : δ ≤ 1 := measureReal_le_one
  have hD : μ {z : unitInterval | ζ ≤ (z : ℝ)} = ENNReal.ofReal δ := by rw [ofReal_measureReal]
  have hP : μ {z : unitInterval | (z : ℝ) < ζ} = ENNReal.ofReal (1 - δ) := by
    rw [hδdef, ← measureReal_lt_eq, ofReal_measureReal]
  ext A hA
  set x : ℕ → ℝ := fun i => ((i : ℝ) + 1) * y with hx
  set a : ℕ → ℝ≥0∞ := fun i => Measure.dirac (x i) A with ha
  set W : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (δ * (1 - δ) ^ i) with hWdef
  have hκ : ∀ i, currencyKernel μ ζ y (x i) A =
      ENNReal.ofReal (1 - δ) * a (i + 1) + ENNReal.ofReal δ * a 0 := by
    intro i
    rw [currencyKernel, cutoffKernel_apply, Measure.add_apply, Measure.smul_apply,
      Measure.smul_apply, smul_eq_mul, smul_eq_mul, hP, hD]
    have e1 : x i + y = x (i + 1) := by
      simp only [hx]
      push_cast
      ring
    have e0 : x 0 = y := by simp [hx]
    simp only [ha, e1, e0]
  rw [adjointOp, Measure.bind_apply hA (Kernel.aemeasurable _), currencyInvariant,
    lintegral_sum_measure, Measure.sum_apply _ hA]
  simp only [lintegral_smul_measure, lintegral_dirac, Measure.smul_apply, smul_eq_mul]
  change ∑' i, W i * currencyKernel μ ζ y (x i) A = ∑' i, W i * a i
  simp only [hκ]
  refine geometric_tsum_shift W a _ _ (fun i => ?_) (by simp [hWdef]) (tsum_ofReal_weights hδ h1)
  change ENNReal.ofReal (δ * (1 - δ) ^ i) * ENNReal.ofReal (1 - δ) =
    ENNReal.ofReal (δ * (1 - δ) ^ (i + 1))
  rw [← ENNReal.ofReal_mul (mul_nonneg hδ.le (pow_nonneg (by linarith) _)), pow_succ, mul_assoc]

/-- **The mean** of the geometric distribution: `∫ m dπ = ∑ᵢ δ(1 − δ)^{i−1} iy = y/δ`. -/
theorem currencyInvariant_mean {δ y : ℝ} (hy : 0 < y) (h0 : 0 < δ) (h1 : δ ≤ 1) :
    ∫ m, m ∂currencyInvariant δ y = y / δ := by
  have hw : ∀ i : ℕ, 0 ≤ δ * (1 - δ) ^ i := fun i => mul_nonneg h0.le (pow_nonneg (by linarith) _)
  have hS : HasSum (fun i : ℕ => δ * (1 - δ) ^ i * (((i : ℝ) + 1) * y)) (y / δ) := by
    have hr : ‖1 - δ‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have := ((hasSum_coe_mul_geometric_of_norm_lt_one hr).add
      (hasSum_geometric_of_lt_one (r := 1 - δ) (by linarith) (by linarith))).mul_left (δ * y)
    convert this using 1
    · funext i
      ring
    · rw [sub_sub_cancel]
      field_simp
      ring
  have hneg : currencyInvariant δ y (Iio 0) = 0 := by
    rw [currencyInvariant, Measure.sum_apply _ measurableSet_Iio]
    refine ENNReal.tsum_eq_zero.2 fun i => ?_
    have : ((i : ℝ) + 1) * y ∉ Iio (0 : ℝ) := by
      rw [mem_Iio, not_lt]
      positivity
    rw [Measure.smul_apply, Measure.dirac_apply, indicator_of_notMem this]
    simp
  have hnn : 0 ≤ᵐ[currencyInvariant δ y] fun m => m :=
    ae_iff.2 (measure_mono_null (fun m hm => mem_Iio.2 (not_le.1 hm)) hneg)
  rw [integral_eq_lintegral_of_nonneg_ae hnn measurable_id.aestronglyMeasurable, currencyInvariant,
    lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [tsum_congr fun i => (ENNReal.ofReal_mul (hw i)).symm,
    ← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hw i) (by positivity)) hS.summable,
    hS.tsum_eq, ENNReal.toReal_ofReal (div_nonneg hy.le h0.le)]

/-- **Exercise 13.6(c).** Let `ζ ∈ (0, 1)` be the cutoff, `ζ = βH(ζ)`, and `δ = μ([ζ, 1])`.
Then `δ > 0`; Condition M holds with `N = 1`, `ε = δ` (`P(m, {y}) ≥ δ`); the geometric
distribution `πᵢ = δ(1 − δ)^{i−1}` on `{iy : i ≥ 1}` is invariant and is the only invariant
probability measure; `‖T*ⁿλ₀ − π‖ ≤ 2(1 − δ)ⁿ` for every initial `λ₀` (Theorem 11.12); the mean is
`∫ m dπ = y/δ`, so the stationary price level from (2) of §13.5, `p = M/∫ m dπ`, is `Mδ/y`. -/
theorem ex_13_6c {β y ζ : ℝ} (hβ1 : β < 1) (hy : 0 < y) (hζ : 0 < ζ)
    (hcut : ζ = β * maxInt μ ζ) :
    let δ := μ.real {z : unitInterval | ζ ≤ (z : ℝ)}
    0 < δ ∧ ConditionMFor (currencyKernel μ ζ y) 1 δ ∧
      IsProbabilityMeasure (currencyInvariant δ y) ∧
      adjointOp (currencyKernel μ ζ y) (currencyInvariant δ y) = currencyInvariant δ y ∧
      (∀ l : Measure ℝ, IsProbabilityMeasure l → adjointOp (currencyKernel μ ζ y) l = l →
        l = currencyInvariant δ y) ∧
      (∀ (l₀ : Measure ℝ) [IsProbabilityMeasure l₀] (n : ℕ),
        tvDist (adjointOp (kpow (currencyKernel μ ζ y) n) l₀) (currencyInvariant δ y) ≤
          2 * (1 - δ) ^ n) ∧
      (∀ i : ℕ, currencyInvariant δ y {((i : ℝ) + 1) * y} = ENNReal.ofReal (δ * (1 - δ) ^ i)) ∧
      ∫ m, m ∂currencyInvariant δ y = y / δ ∧
      ∀ M : ℝ, M / ∫ m, m ∂currencyInvariant δ y = M * δ / y := by
  intro δ
  have hδ : 0 < δ := delta_pos_of_cutoff hβ1 hζ hcut
  have h1 : δ ≤ 1 := measureReal_le_one
  have hMk : IsMarkovKernel (currencyKernel μ ζ y) :=
    isMarkovKernel_cutoffKernel (μ := μ) ζ (measurable_add_const y) y
  have hM : ConditionMFor (currencyKernel μ ζ y) 1 δ :=
    cutoffKernel_conditionM ζ (measurable_add_const y) y hδ
  have hπ := isProbabilityMeasure_currencyInvariant y hδ h1
  have hinv := currencyInvariant_invariant (μ := μ) (y := y) hδ
  have hmean := currencyInvariant_mean hy hδ h1
  obtain ⟨huniq, hconv⟩ := invariant_unique_of_conditionM_one (κ := currencyKernel μ ζ y) hM _ hinv
  refine ⟨hδ, hM, hπ, hinv, huniq, hconv, currencyInvariant_singleton hy, hmean, fun M => ?_⟩
  rw [hmean]
  field_simp

end StokeyLucasPrescott.ConvergenceApplications

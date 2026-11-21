/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.AASmoothAmbiguity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Convex.Deriv

/-!
# Temporal resolution of uncertainty

Miao, §20.2.3, pp. 701–704, and Exercise 20.3 (p. 735): Kreps and Porteus (1978).

Consumption in each period lies in a measurable space `X` (the book: a bounded interval of
`ℝ₊`); period-1 lotteries are probability measures on `X` (`aa_Lott`), and the intertemporal
consumption lotteries used in the definition are finite mixtures of programs `δ[c₀, m]`, valued
by `U₀(d) = E_d[W(c₀, E_m U₁(c₁))]` (`aa_U0`).

* The four choices of p. 701: a time-additive expected-utility maximiser is indifferent between
  choices 1 and 2 (`aa_timeAdditive_indifferent`) and between choices 3 and 4
  (`aa_timeAdditive_indifferent_34`).
* **Definition 20.2.4** (`aa_PrefersEarly`, `aa_PrefersLate`, `definition_20_2_4`).
* **Theorem 20.2.1**: earlier (later) resolution is preferred iff `W(x, ·)` is convex (concave) on
  the set `Y` of expected utilities `E_m U₁` (`theorem_20_2_1`, `theorem_20_2_1_late`), for
  bounded measurable `U₁`. The book says "convex in `y`": only the values `y ∈ Y` matter.
* **Exercise 20.3** and p. 704: for Epstein–Zin utility (20.3), written in the Kreps–Porteus form
  `W̃(c, y) = u(W(c, u⁻¹(y)))`, `u(x) = x^{1−γ}/(1−γ)` (`aa_ezKP`, `aa_ezKP_eq`), on
  `X = [a, b] ⊆ (0, ∞)` with `a < b`: earlier resolution is (weakly) preferred iff `γ ≥ ρ`
  (`ex_20_3`), strictly preferred for every nondegenerate pair of lotteries when `γ > ρ`
  (`aa_ez_strictEarly`), and at `γ = ρ` the agent is indifferent (`aa_ez_indifferent`). The book's
  "iff `γ > ρ`" is the strict version; with the weak preference of Definition 20.2.4 the condition
  is `γ ≥ ρ`.
-/

namespace Miao.RecursiveUtility

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

/-- The period-1 consumption lotteries `M(X)`: Borel probability measures on `X`. -/
def aa_Lott (X : Type*) [MeasurableSpace X] : Set (Measure X) := {m | IsProbabilityMeasure m}

/-- The mixture `αm + (1 − α)m'` of two lotteries. -/
noncomputable def aa_mix (α : ℝ) (m m' : Measure X) : Measure X :=
  ENNReal.ofReal α • m + ENNReal.ofReal (1 - α) • m'

theorem aa_mix_mem {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {m m' : Measure X} (hm : m ∈ aa_Lott X)
    (hm' : m' ∈ aa_Lott X) : aa_mix α m m' ∈ aa_Lott X := by
  have h1 : m Set.univ = 1 := (hm : IsProbabilityMeasure m).measure_univ
  have h2 : m' Set.univ = 1 := (hm' : IsProbabilityMeasure m').measure_univ
  refine ⟨?_⟩
  simp only [aa_mix, Measure.add_apply, Measure.smul_apply, smul_eq_mul, h1, h2, mul_one]
  rw [← ENNReal.ofReal_add hα0 (by linarith)]
  simp

theorem aa_integrable {U₁ : X → ℝ} (hU : Measurable U₁) {C : ℝ} (hC : ∀ x, |U₁ x| ≤ C)
    {m : Measure X} (hm : m ∈ aa_Lott X) : Integrable U₁ m := by
  have : IsProbabilityMeasure m := hm
  exact Integrable.of_bound hU.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => hC x)

/-- `E_{αm + (1−α)m'} U₁ = αE_m U₁ + (1 − α)E_{m'} U₁` for bounded measurable `U₁`. -/
theorem aa_integral_mix {U₁ : X → ℝ} (hU : Measurable U₁) {C : ℝ} (hC : ∀ x, |U₁ x| ≤ C)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {m m' : Measure X} (hm : m ∈ aa_Lott X)
    (hm' : m' ∈ aa_Lott X) :
    ∫ x, U₁ x ∂(aa_mix α m m') = α * ∫ x, U₁ x ∂m + (1 - α) * ∫ x, U₁ x ∂m' := by
  unfold aa_mix
  rw [integral_add_measure ((aa_integrable hU hC hm).smul_measure ENNReal.ofReal_ne_top)
    ((aa_integrable hU hC hm').smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hα0,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- The utility `U₀(d) = E_d[W(c₀, E_m U₁(c₁))]` of a finite intertemporal consumption lottery
`d = ∑ᵢ wᵢ δ[cᵢ, mᵢ]`. -/
noncomputable def aa_U0 (W : X → ℝ → ℝ) (U₁ : X → ℝ) {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (c : ι → X) (m : ι → Measure X) : ℝ :=
  ∑ i, w i * W (c i) (∫ x, U₁ x ∂(m i))

/-- **Definition 20.2.4** (Miao, p. 703): the decision maker prefers earlier resolution of
uncertainty if `αδ[c₀, m] + (1 − α)δ[c₀, m'] ≿ δ[c₀, αm + (1 − α)m']` for all `c₀, m, m', α`. -/
def aa_PrefersEarly (W : X → ℝ → ℝ) (U₁ : X → ℝ) : Prop :=
  ∀ c₀ : X, ∀ m ∈ aa_Lott X, ∀ m' ∈ aa_Lott X, ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    W c₀ (∫ x, U₁ x ∂(aa_mix α m m')) ≤
      α * W c₀ (∫ x, U₁ x ∂m) + (1 - α) * W c₀ (∫ x, U₁ x ∂m')

/-- Preference for later resolution: the reverse ranking. -/
def aa_PrefersLate (W : X → ℝ → ℝ) (U₁ : X → ℝ) : Prop :=
  ∀ c₀ : X, ∀ m ∈ aa_Lott X, ∀ m' ∈ aa_Lott X, ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    α * W c₀ (∫ x, U₁ x ∂m) + (1 - α) * W c₀ (∫ x, U₁ x ∂m') ≤
      W c₀ (∫ x, U₁ x ∂(aa_mix α m m'))

/-- **Definition 20.2.4** (Miao, p. 703) in terms of the recursive utility `U₀` of the two
programs: the early-resolution lottery `αδ[c₀, m] + (1 − α)δ[c₀, m']` (indexed by `Bool`) is
weakly preferred to the late-resolution lottery `δ[c₀, αm + (1 − α)m']` (indexed by `Unit`). -/
theorem definition_20_2_4 (W : X → ℝ → ℝ) (U₁ : X → ℝ) :
    aa_PrefersEarly W U₁ ↔ ∀ c₀ : X, ∀ m ∈ aa_Lott X, ∀ m' ∈ aa_Lott X, ∀ α : ℝ, 0 ≤ α →
      α ≤ 1 → aa_U0 W U₁ (fun _ : Unit => 1) (fun _ => c₀) (fun _ => aa_mix α m m') ≤
        aa_U0 W U₁ (fun b : Bool => if b then α else 1 - α) (fun _ => c₀)
          (fun b => if b then m else m') := by
  simp [aa_U0, aa_PrefersEarly]

/-- The set `Y = {E_m U₁ : m ∈ M(X)}` of expected period-1 utilities. -/
def aa_Y (U₁ : X → ℝ) : Set ℝ := {y | ∃ m ∈ aa_Lott X, y = ∫ x, U₁ x ∂m}

theorem aa_Y_convex {U₁ : X → ℝ} (hU : Measurable U₁) {C : ℝ} (hC : ∀ x, |U₁ x| ≤ C) :
    Convex ℝ (aa_Y U₁) := by
  rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  exact ⟨aa_mix a m m', aa_mix_mem ha (by linarith) hm hm',
    by rw [aa_integral_mix hU hC ha (by linarith) hm hm', smul_eq_mul, smul_eq_mul]⟩

/-- **Theorem 20.2.1** (Miao, p. 704; Kreps and Porteus 1978). For bounded measurable `U₁`, the
decision maker with `U₀(d) = E_d[W(c₀, E_m U₁(c₁))]` prefers earlier resolution of uncertainty iff
`W(x, ·)` is convex on the set `Y` of expected utilities, for every `x`. -/
theorem theorem_20_2_1 (W : X → ℝ → ℝ) {U₁ : X → ℝ} (hU : Measurable U₁) {C : ℝ}
    (hC : ∀ x, |U₁ x| ≤ C) : aa_PrefersEarly W U₁ ↔ ∀ x, ConvexOn ℝ (aa_Y U₁) (W x) := by
  constructor
  · intro h x
    refine ⟨aa_Y_convex hU hC, ?_⟩
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := h x m hm m' hm' a ha (by linarith)
    rw [aa_integral_mix hU hC ha (by linarith) hm hm'] at this
    simpa [smul_eq_mul] using this
  · intro h c₀ m hm m' hm' α hα0 hα1
    rw [aa_integral_mix hU hC hα0 hα1 hm hm']
    have := (h c₀).2 ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩ hα0 (by linarith : 0 ≤ 1 - α) (by ring)
    simpa [smul_eq_mul] using this

/-- **Theorem 20.2.1, later resolution** (Miao, p. 704): later resolution is preferred iff `W(x, ·)`
is concave on `Y` for every `x`. -/
theorem theorem_20_2_1_late (W : X → ℝ → ℝ) {U₁ : X → ℝ} (hU : Measurable U₁) {C : ℝ}
    (hC : ∀ x, |U₁ x| ≤ C) : aa_PrefersLate W U₁ ↔ ∀ x, ConcaveOn ℝ (aa_Y U₁) (W x) := by
  constructor
  · intro h x
    refine ⟨aa_Y_convex hU hC, ?_⟩
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := h x m hm m' hm' a ha (by linarith)
    rw [aa_integral_mix hU hC ha (by linarith) hm hm'] at this
    simpa [smul_eq_mul] using this
  · intro h c₀ m hm m' hm' α hα0 hα1
    rw [aa_integral_mix hU hC hα0 hα1 hm hm']
    have := (h c₀).2 ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩ hα0 (by linarith : 0 ≤ 1 - α) (by ring)
    simpa [smul_eq_mul] using this

/-- Miao, p. 701: a decision maker with time-additive expected utility, `W(x, y) = u(x) + βy`, is
indifferent between choices 1 and 2 (it both prefers earlier and prefers later resolution). -/
theorem aa_timeAdditive_indifferent (u : X → ℝ) (β : ℝ) {U₁ : X → ℝ} (hU : Measurable U₁)
    {C : ℝ} (hC : ∀ x, |U₁ x| ≤ C) :
    aa_PrefersEarly (fun x y => u x + β * y) U₁ ∧ aa_PrefersLate (fun x y => u x + β * y) U₁ := by
  constructor <;>
  · intro c₀ m hm m' hm' α hα0 hα1
    rw [aa_integral_mix hU hC hα0 hα1 hm hm']
    linarith

/-- Miao, p. 701: choices 3 and 4. With time-additive expected utility `u(c₀) + βu(c₁)`,
independent fair coins in both periods (choice 3) and one coin for both periods (choice 4) give the
same utility. -/
theorem aa_timeAdditive_indifferent_34 (u : ℝ → ℝ) (β c c' : ℝ) :
    (1 / 4 : ℝ) * ((u c + β * u c) + (u c + β * u c') + (u c' + β * u c) + (u c' + β * u c')) =
      (1 / 2 : ℝ) * (u c + β * u c) + (1 / 2 : ℝ) * (u c' + β * u c') := by
  ring

/-! ### Epstein–Zin utility (Exercise 20.3) -/

/-- Epstein–Zin utility (20.3) over two periods in the Kreps–Porteus form
`U₀ = W̃(c₀, E_m u(c₁))`, `W̃(c, y) = u(W(c, u⁻¹(y)))` with `u(x) = x^{1−γ}/(1−γ)` and the CES
aggregator `W`. -/
noncomputable def aa_ezKP (β ρ γ c y : ℝ) : ℝ := aa_powU γ (aa_W β ρ c (aa_powUinv γ y))

/-- The Kreps–Porteus form is the Epstein–Zin recursion: `u⁻¹(E u(c₁))` is the certainty equivalent
`M(c₁) = (E c₁^{1−γ})^{1/(1−γ)}`, so `W̃(c₀, E u(c₁)) = u(W(c₀, M(c₁)))`. -/
theorem aa_ezKP_eq {S : Type*} [Fintype S] (β ρ : ℝ) {γ : ℝ} (hγ : γ ≠ 1) (c : ℝ) (p x : S → ℝ) :
    aa_ezKP β ρ γ c (aa_E p fun s => aa_powU γ (x s)) = aa_powU γ (aa_W β ρ c (aa_KP γ p x)) := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  unfold aa_ezKP aa_KP
  congr 2
  unfold aa_powUinv aa_powU
  rw [← aa_E_smul]
  congr 2
  funext s
  field_simp

/-- `F(t) = (h + t^{1/θ})^θ` is strictly convex on `(0, ∞)` for `h > 0`, `θ ∈ (0, 1)`. -/
theorem aa_powF_strictConvexOn {h θ : ℝ} (hh : 0 < h) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    StrictConvexOn ℝ (Ioi 0) (SS.powF h θ) := by
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
    (SS.continuousOn_powF hh.le hθ0.ne') ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  rw [(SS.hasDerivAt_powF hh.le hθ0.ne' hs').deriv, (SS.hasDerivAt_powF hh.le hθ0.ne' ht').deriv]
  have h1 : t ^ (-θ⁻¹) < s ^ (-θ⁻¹) :=
    Real.rpow_lt_rpow_of_neg hs' hst (by have := inv_pos.2 hθ0; linarith)
  have hBt : 0 < 1 + h * t ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos ht' (-θ⁻¹); positivity
  exact Real.rpow_lt_rpow_of_neg hBt (by nlinarith) (by linarith)

/-- `F(t) = (h + t^{1/θ})^θ` is strictly concave on `(0, ∞)` for `h > 0` and `θ > 1` or `θ < 0`. -/
theorem aa_powF_strictConcaveOn {h θ : ℝ} (hh : 0 < h) (hθ : θ < 0 ∨ 1 < θ) :
    StrictConcaveOn ℝ (Ioi 0) (SS.powF h θ) := by
  have hθ0 : θ ≠ 0 := by rcases hθ with h | h <;> [exact h.ne; exact (by linarith : (0:ℝ) < θ).ne']
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
    (SS.continuousOn_powF hh.le hθ0) ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  rw [(SS.hasDerivAt_powF hh.le hθ0 hs').deriv, (SS.hasDerivAt_powF hh.le hθ0 ht').deriv]
  have hBs : 0 < 1 + h * s ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos hs' (-θ⁻¹); positivity
  have hBt : 0 < 1 + h * t ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos ht' (-θ⁻¹); positivity
  rcases hθ with hneg | hpos
  · have h1 : s ^ (-θ⁻¹) < t ^ (-θ⁻¹) :=
      Real.rpow_lt_rpow hs'.le hst (by have := inv_lt_zero.2 hneg; linarith)
    exact Real.rpow_lt_rpow_of_neg hBs (by nlinarith) (by linarith)
  · have h1 : t ^ (-θ⁻¹) < s ^ (-θ⁻¹) :=
      Real.rpow_lt_rpow_of_neg hs' hst (by have := inv_pos.2 (by linarith : (0:ℝ) < θ); linarith)
    exact Real.rpow_lt_rpow hBt.le (by nlinarith) (by linarith)

/-- `W̃(c, y) = β^{θ}(1 − γ)⁻¹ F((1 − γ)y)` with `F(t) = (h + t^{1/θ})^θ`, `θ = (1 − γ)/(1 − ρ)`,
`h = (1 − β)c^{1−ρ}/β`, on the domain `(1 − γ)y > 0`. -/
theorem aa_ezKP_eq_powF {β ρ γ c y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (hc : 0 < c) (hy : 0 < (1 - γ) * y) :
    aa_ezKP β ρ γ c y = β ^ ((1 - γ) / (1 - ρ)) / (1 - γ) *
      SS.powF ((1 - β) * c ^ (1 - ρ) / β) ((1 - γ) / (1 - ρ)) ((1 - γ) * y) := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hr : 1 - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  set t := (1 - γ) * y with htdef
  set θ := (1 - γ) / (1 - ρ) with hθ
  have hθ0 : θ ≠ 0 := div_ne_zero hg hr
  have hA : 0 < (1 - β) * c ^ (1 - ρ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hc _)
  have hbase : 0 < (1 - β) * c ^ (1 - ρ) + β * t ^ θ⁻¹ :=
    add_pos hA (mul_pos hβ0 (Real.rpow_pos_of_pos hy _))
  unfold aa_ezKP aa_powU aa_W aa_powUinv SS.powF
  rw [← htdef, ← Real.rpow_mul hy.le]
  have e1 : (1 - γ)⁻¹ * (1 - ρ) = θ⁻¹ := by rw [hθ, inv_div]; ring
  rw [e1, ← Real.rpow_mul hbase.le]
  have e2 : (1 - ρ)⁻¹ * (1 - γ) = θ := by rw [hθ]; ring
  rw [e2]
  have e3 : (1 - β) * c ^ (1 - ρ) + β * t ^ θ⁻¹ = β * ((1 - β) * c ^ (1 - ρ) / β + t ^ θ⁻¹) := by
    field_simp
  rw [e3, Real.mul_rpow hβ0.le (by positivity)]
  ring

/-- Strict convexity transfers through `y ↦ k F(l y)` with `k > 0`, `l ≠ 0`. -/
theorem aa_strictConvexOn_comp {F : ℝ → ℝ} (hF : StrictConvexOn ℝ (Ioi 0) F) {k l : ℝ}
    (hk : 0 < k) (hl : l ≠ 0) : StrictConvexOn ℝ {y | 0 < l * y} fun y => k * F (l * y) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    rw [show l * (a * x + b * y) = a * (l * x) + b * (l * y) by ring]
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' hx, mul_nonneg hb hy.le]
    · subst ha'
      rw [zero_add] at hab
      subst hab
      simpa using hy
  · intro x hx y hy hxy a b ha hb hab
    have hx' : l * x ∈ Ioi (0 : ℝ) := hx
    have hy' : l * y ∈ Ioi (0 : ℝ) := hy
    have hne : l * x ≠ l * y := fun h => hxy (mul_left_cancel₀ hl h)
    have := hF.2 hx' hy' hne ha hb hab
    simp only [smul_eq_mul] at this ⊢
    rw [show l * (a * x + b * y) = a * (l * x) + b * (l * y) by ring]
    nlinarith

/-- Strict concavity transfers through `y ↦ k F(l y)` with `k > 0`, `l ≠ 0`. -/
theorem aa_strictConcaveOn_comp {F : ℝ → ℝ} (hF : StrictConcaveOn ℝ (Ioi 0) F) {k l : ℝ}
    (hk : 0 < k) (hl : l ≠ 0) : StrictConcaveOn ℝ {y | 0 < l * y} fun y => k * F (l * y) := by
  have := (aa_strictConvexOn_comp hF.neg hk hl).neg
  convert this using 1
  funext y
  simp

/-- The domain `{y : (1 − γ)y > 0}` of the Kreps–Porteus form. -/
theorem aa_ezKP_strict {β ρ γ c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (hc : 0 < c) :
    (ρ < γ → StrictConvexOn ℝ {y | 0 < (1 - γ) * y} (aa_ezKP β ρ γ c)) ∧
      (γ < ρ → StrictConcaveOn ℝ {y | 0 < (1 - γ) * y} (aa_ezKP β ρ γ c)) := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hr : 1 - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  set h := (1 - β) * c ^ (1 - ρ) / β with hh
  have hh0 : 0 < h := div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hc _)) hβ0
  set θ := (1 - γ) / (1 - ρ) with hθ
  have hβθ : 0 < β ^ θ := Real.rpow_pos_of_pos hβ0 _
  have heq : ∀ y ∈ {y : ℝ | 0 < (1 - γ) * y},
      aa_ezKP β ρ γ c y = β ^ θ / (1 - γ) * SS.powF h θ ((1 - γ) * y) := fun y hy =>
    aa_ezKP_eq_powF hβ0 hβ1 hρ hγ hc hy
  -- a function equal on the domain to a strictly convex/concave one
  have transfer_cvx : ∀ g : ℝ → ℝ, StrictConvexOn ℝ {y | 0 < (1 - γ) * y} g →
      (∀ y ∈ {y : ℝ | 0 < (1 - γ) * y}, aa_ezKP β ρ γ c y = g y) →
      StrictConvexOn ℝ {y | 0 < (1 - γ) * y} (aa_ezKP β ρ γ c) := by
    intro g hg' he
    refine ⟨hg'.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
    rw [he x hx, he y hy, he _ (hg'.1 hx hy ha.le hb.le hab)]
    exact hg'.2 hx hy hxy ha hb hab
  have transfer_ccv : ∀ g : ℝ → ℝ, StrictConcaveOn ℝ {y | 0 < (1 - γ) * y} g →
      (∀ y ∈ {y : ℝ | 0 < (1 - γ) * y}, aa_ezKP β ρ γ c y = g y) →
      StrictConcaveOn ℝ {y | 0 < (1 - γ) * y} (aa_ezKP β ρ γ c) := by
    intro g hg' he
    refine ⟨hg'.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
    rw [he x hx, he y hy, he _ (hg'.1 hx hy ha.le hb.le hab)]
    exact hg'.2 hx hy hxy ha hb hab
  constructor
  · intro hργ
    rcases lt_or_gt_of_ne hg with hgn | hgp
    · -- `γ > 1`: `k < 0`, need `F` strictly concave: `θ < 0` (ρ < 1) or `θ > 1` (ρ > 1)
      have hk : 0 < -(β ^ θ / (1 - γ)) := by
        rw [neg_pos]; exact div_neg_of_pos_of_neg hβθ hgn
      have hF : StrictConcaveOn ℝ (Ioi 0) (SS.powF h θ) := by
        refine aa_powF_strictConcaveOn hh0 ?_
        rcases lt_or_gt_of_ne hr with hrn | hrp
        · right; rw [hθ, lt_div_iff_of_neg hrn]; linarith
        · left; exact div_neg_of_neg_of_pos hgn hrp
      refine transfer_cvx _ ((aa_strictConcaveOn_comp hF.neg.neg hk hg).neg) fun y hy => ?_
      · rw [heq y hy]
        simp
    · -- `γ < 1`: `k > 0`, need `F` strictly convex: `θ ∈ (0, 1)`
      have hk : 0 < β ^ θ / (1 - γ) := div_pos hβθ hgp
      have hrp : 0 < 1 - ρ := by linarith
      have hF : StrictConvexOn ℝ (Ioi 0) (SS.powF h θ) :=
        aa_powF_strictConvexOn hh0 (div_pos hgp hrp) (by rw [hθ, div_lt_one hrp]; linarith)
      exact transfer_cvx _ (aa_strictConvexOn_comp hF hk hg) heq
  · intro hγρ
    rcases lt_or_gt_of_ne hg with hgn | hgp
    · -- `γ > 1`, so `ρ > γ > 1`: `θ ∈ (0, 1)`, `F` strictly convex, `k < 0`
      have hk : 0 < -(β ^ θ / (1 - γ)) := by
        rw [neg_pos]; exact div_neg_of_pos_of_neg hβθ hgn
      have hrn : 1 - ρ < 0 := by linarith
      have hF : StrictConvexOn ℝ (Ioi 0) (SS.powF h θ) :=
        aa_powF_strictConvexOn hh0 (div_pos_of_neg_of_neg hgn hrn)
          (by rw [hθ, div_lt_one_of_neg hrn]; linarith)
      refine transfer_ccv _ ((aa_strictConvexOn_comp hF hk hg).neg) fun y hy => ?_
      rw [heq y hy]
      simp
    · -- `γ < 1`: `k > 0`, `F` strictly concave: `θ > 1` (ρ < 1) or `θ < 0` (ρ > 1)
      have hk : 0 < β ^ θ / (1 - γ) := div_pos hβθ hgp
      have hF : StrictConcaveOn ℝ (Ioi 0) (SS.powF h θ) := by
        refine aa_powF_strictConcaveOn hh0 ?_
        rcases lt_or_gt_of_ne hr with hrn | hrp
        · left; exact div_neg_of_pos_of_neg hgp hrn
        · right; rw [hθ, lt_div_iff₀ hrp]; linarith
      exact transfer_ccv _ (aa_strictConcaveOn_comp hF hk hg) heq

/-- At `γ = ρ` the Kreps–Porteus form is affine in `y`: `W̃(c, y) = (1 − β)u(c) + βy`. -/
theorem aa_ezKP_diag {β γ c y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : γ ≠ 1) (hc : 0 < c)
    (hy : 0 < (1 - γ) * y) : aa_ezKP β γ γ c y = (1 - β) * aa_powU γ c + β * y := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hbase : 0 ≤ (1 - β) * c ^ (1 - γ) + β * (((1 - γ) * y) ^ (1 - γ)⁻¹) ^ (1 - γ) := by
    have := Real.rpow_pos_of_pos hc (1 - γ)
    have := Real.rpow_nonneg (Real.rpow_nonneg hy.le (1 - γ)⁻¹) (1 - γ)
    have : 0 < 1 - β := by linarith
    positivity
  unfold aa_ezKP aa_powU aa_W aa_powUinv
  rw [Real.rpow_inv_rpow hbase hg, Real.rpow_inv_rpow hy.le hg]
  field_simp

/-- Consumption on `[a, b]`, `0 < a`: the vNM index `u(x) = x^{1−γ}/(1−γ)` is bounded. -/
theorem aa_powU_bound {a b γ : ℝ} (ha : 0 < a) (x : Icc a b) :
    |aa_powU γ x| ≤ (a ^ (1 - γ) + b ^ (1 - γ)) / |1 - γ| := by
  have hx : 0 < (x : ℝ) := ha.trans_le x.2.1
  unfold aa_powU
  rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hx _)]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  have h1 := Real.rpow_pos_of_pos ha (1 - γ)
  have h2 := Real.rpow_pos_of_pos (ha.trans_le (x.2.1.trans x.2.2)) (1 - γ)
  rcases le_or_gt 0 (1 - γ) with hp | hn
  · have := Real.rpow_le_rpow hx.le x.2.2 hp
    linarith
  · have := Real.rpow_le_rpow_of_nonpos ha x.2.1 hn.le
    linarith

theorem aa_powU_measurable (a b γ : ℝ) : Measurable fun x : Icc a b => aa_powU γ x := by
  unfold aa_powU
  fun_prop

/-- Expected utilities of lotteries on `[a, b]`, `0 < a`, lie in the domain `(1 − γ)y > 0`. -/
theorem aa_Y_subset {a b γ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hγ : γ ≠ 1) :
    aa_Y (fun x : Icc a b => aa_powU γ x) ⊆ {y | 0 < (1 - γ) * y} := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  rintro _ ⟨m, hm, rfl⟩
  have : IsProbabilityMeasure m := hm
  set k := min (a ^ (1 - γ)) (b ^ (1 - γ)) with hk
  have hk0 : 0 < k := lt_min (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos (ha.trans_le hab) _)
  have hlow : ∀ x : Icc a b, k ≤ (1 - γ) * aa_powU γ x := fun x => by
    have hx : 0 < (x : ℝ) := ha.trans_le x.2.1
    unfold aa_powU
    rw [mul_div_cancel₀ _ hg]
    rcases le_or_gt 0 (1 - γ) with hp | hn
    · exact (min_le_left _ _).trans (Real.rpow_le_rpow ha.le x.2.1 hp)
    · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos hx x.2.2 hn.le)
  have hint := aa_integrable (aa_powU_measurable a b γ) (aa_powU_bound ha) hm
  have h1 : k ≤ ∫ x, (1 - γ) * aa_powU γ x ∂m := by
    have := integral_mono (integrable_const k) (hint.const_mul (1 - γ)) hlow
    simpa using this
  rw [integral_const_mul] at h1
  exact hk0.trans_le h1

/-- **Exercise 20.3** (Miao, p. 735; p. 704). An agent with Epstein–Zin utility (20.3) over two
periods, consumption in `[a, b]` with `0 < a < b`, `β ∈ (0, 1)`, `ρ, γ ≠ 1`, prefers earlier
resolution of uncertainty (Definition 20.2.4) iff `γ ≥ ρ`. The book's "iff `γ > ρ`" is the strict
preference (`aa_ez_strictEarly`); at `γ = ρ` the agent is indifferent (`aa_ez_indifferent`). -/
theorem ex_20_3 {a b β ρ γ : ℝ} (ha : 0 < a) (hab : a < b) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ : ρ ≠ 1) (hγ : γ ≠ 1) :
    aa_PrefersEarly (fun c : Icc a b => aa_ezKP β ρ γ c) (fun x : Icc a b => aa_powU γ x) ↔
      ρ ≤ γ := by
  have hU := aa_powU_measurable a b γ
  have hC := aa_powU_bound (γ := γ) (b := b) ha
  have hY := aa_Y_subset ha hab.le hγ
  have hYc := aa_Y_convex hU hC
  rw [theorem_20_2_1 _ hU hC]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    -- strict concavity on two Dirac lotteries contradicts convexity
    have hcc := (aa_ezKP_strict hβ0 hβ1 hρ hγ (c := a) ha).2 hlt
    let xa : Icc a b := ⟨a, le_rfl, hab.le⟩
    let xb : Icc a b := ⟨b, hab.le, le_rfl⟩
    have hda : Measure.dirac xa ∈ aa_Lott (Icc a b) := (inferInstance : IsProbabilityMeasure _)
    have hdb : Measure.dirac xb ∈ aa_Lott (Icc a b) := (inferInstance : IsProbabilityMeasure _)
    have hya : aa_powU γ a ∈ aa_Y (fun x : Icc a b => aa_powU γ x) :=
      ⟨_, hda, by rw [integral_dirac]⟩
    have hyb : aa_powU γ b ∈ aa_Y (fun x : Icc a b => aa_powU γ x) :=
      ⟨_, hdb, by rw [integral_dirac]⟩
    have hne : aa_powU γ a ≠ aa_powU γ b := by
      unfold aa_powU
      intro heq
      have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
      have h2 : a ^ (1 - γ) = b ^ (1 - γ) := by
        have := congrArg (· * (1 - γ)) heq
        simpa [div_mul_cancel₀ _ hg] using this
      have h3 := congrArg (· ^ (1 - γ)⁻¹) h2
      simp only [Real.rpow_rpow_inv ha.le hg, Real.rpow_rpow_inv (ha.trans hab).le hg] at h3
      exact hab.ne h3
    have h1 := (h xa).2 hya hyb (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have h2 := hcc.2 (hY hya) (hY hyb) hne (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    exact absurd h1 (not_le.2 h2)
  · intro hle x
    have hx : 0 < (x : ℝ) := ha.trans_le x.2.1
    rcases hle.lt_or_eq with hlt | heq
    · exact ((aa_ezKP_strict hβ0 hβ1 hρ hγ hx).1 hlt).convexOn.subset hY hYc
    · subst heq
      refine ⟨hYc, fun y₁ hy₁ y₂ hy₂ s t hs ht hst => ?_⟩
      have hm := hYc hy₁ hy₂ hs ht hst
      rw [aa_ezKP_diag hβ0 hβ1 hγ hx (hY hm), aa_ezKP_diag hβ0 hβ1 hγ hx (hY hy₁),
        aa_ezKP_diag hβ0 hβ1 hγ hx (hY hy₂)]
      simp only [smul_eq_mul]
      have : s * ((1 - β) * aa_powU ρ x) + t * ((1 - β) * aa_powU ρ x) =
          (1 - β) * aa_powU ρ x := by rw [← add_mul, hst, one_mul]
      nlinarith

/-- Miao, p. 704: for `γ > ρ` the Epstein–Zin agent strictly prefers earlier resolution whenever
the two lotteries have different expected utilities and `α ∈ (0, 1)`. -/
theorem aa_ez_strictEarly {a b β ρ γ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ : ρ ≠ 1) (hγ : γ ≠ 1) (hργ : ρ < γ) (c₀ : Icc a b) {m m' : Measure (Icc a b)}
    (hm : m ∈ aa_Lott (Icc a b)) (hm' : m' ∈ aa_Lott (Icc a b))
    (hne : ∫ x, aa_powU γ x ∂m ≠ ∫ x, aa_powU γ x ∂m') {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    aa_ezKP β ρ γ c₀ (∫ x, aa_powU γ x ∂(aa_mix α m m')) <
      α * aa_ezKP β ρ γ c₀ (∫ x, aa_powU γ x ∂m) +
        (1 - α) * aa_ezKP β ρ γ c₀ (∫ x, aa_powU γ x ∂m') := by
  have hU := aa_powU_measurable a b γ
  have hC := aa_powU_bound (γ := γ) (b := b) ha
  have hY := aa_Y_subset ha hab hγ
  have hc : 0 < (c₀ : ℝ) := ha.trans_le c₀.2.1
  have hcv := (aa_ezKP_strict hβ0 hβ1 hρ hγ hc).1 hργ
  rw [aa_integral_mix hU hC hα0.le hα1.le hm hm']
  have := hcv.2 (hY ⟨m, hm, rfl⟩) (hY ⟨m', hm', rfl⟩) hne hα0 (by linarith : 0 < 1 - α)
    (by ring)
  simpa [smul_eq_mul] using this

/-- Miao, p. 686: at `γ = ρ` (time-additive expected power utility) the Epstein–Zin agent is
indifferent to the timing of resolution. -/
theorem aa_ez_indifferent {a b β γ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : γ ≠ 1) (c₀ : Icc a b) {m m' : Measure (Icc a b)} (hm : m ∈ aa_Lott (Icc a b))
    (hm' : m' ∈ aa_Lott (Icc a b)) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    aa_ezKP β γ γ c₀ (∫ x, aa_powU γ x ∂(aa_mix α m m')) =
      α * aa_ezKP β γ γ c₀ (∫ x, aa_powU γ x ∂m) +
        (1 - α) * aa_ezKP β γ γ c₀ (∫ x, aa_powU γ x ∂m') := by
  have hU := aa_powU_measurable a b γ
  have hC := aa_powU_bound (γ := γ) (b := b) ha
  have hY := aa_Y_subset ha hab hγ
  have hc : 0 < (c₀ : ℝ) := ha.trans_le c₀.2.1
  have hmix := hY ⟨_, aa_mix_mem hα0 hα1 hm hm', rfl⟩
  rw [aa_ezKP_diag hβ0 hβ1 hγ hc hmix, aa_ezKP_diag hβ0 hβ1 hγ hc (hY ⟨m, hm, rfl⟩),
    aa_ezKP_diag hβ0 hβ1 hγ hc (hY ⟨m', hm', rfl⟩), aa_integral_mix hU hC hα0 hα1 hm hm']
  ring

end Miao.RecursiveUtility

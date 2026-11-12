import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Order.Field
import NeoclassicalGrowth.RBUtility
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import AKMMDynamicOptimization.BalancedGrowthCRRA
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The benchmark static model of labour supply

AKMM, §12.3.1, pp. 331–335 (Chapter 12, R. Rogerson and G. L. Violante).

Preferences `U(c, ℓ) = u(c) − v(ℓ)` with `u(c) = c^{1−σ}/(1 − σ)` (`log c` at `σ = 1`,
`crraU`) and `v(ℓ) = ψℓ^{1+1/γ}/(1 + 1/γ)` (`disutil`); the budget is `c = wℓ + I`.

* The optimum is unique and interior and is characterised by the first-order condition (12.1)
  (`eq_12_1`): for `I ≥ 0` there is exactly one `ℓ > 0` satisfying (12.1); it strictly beats
  every other `ℓ > 0`, and when `I > 0` also `ℓ = 0`.
* Differentiating (12.1) along any differentiable path of wages, non-labour income and optimal
  hours gives one linear identity (`st_path_identity`); it is stated with a net wage
  `(1 − τ)w` and a budget `c = (1 − τ)wℓ + I`, so it serves the dynamic model of §12.4 as well.
  From it: the income elasticity (12.2) (`eq_12_2`), the Marshallian elasticity (12.3)
  (`eq_12_3`), the Hicksian elasticity (12.4) as the response along the compensated path
  `dI = −ℓ dw` (`eq_12_4`), which is the path that keeps utility constant to first order
  (`st_compensated_utility`), and the Slutsky decomposition (`st_slutsky`).
* Footnote 2 is corrected: `ℓ₂ = −σ(1 − s_I)/(w[1/γ + σ(1 − s_I)])` (`st_footnote_2`), with a
  counterexample to the printed value (`st_footnote_2_printed_false`).
* Signs (`st_signs`), the zero-income case (`st_zero_income_signs`), the effects increasing
  in `γ` at `σ = 1` (`st_effects_mono_gamma`), and an explicit solution at `I = 0` that shows
  the path hypotheses are satisfiable (`st_zero_income_path`).
* Taxes and transfers: a change in `1 − τ` acts as a change in `w` and a change in `T` as a
  change in `I` (`st_tax_as_wage`); the balanced-budget rebate `T = τwℓ` gives the response
  `1/(1/γ + σwℓ/c)`, which is the Hicksian elasticity (12.4) exactly when `τ = 0`
  (`st_balanced_budget`, `st_balanced_budget_hicks_at_zero`).

Departure: the book obtains the elasticities by the implicit function theorem; here the
optimal hours are assumed differentiable along the path (and this is shown for `I = 0`).
-/

namespace AKMM.LaborSupply

open Filter Topology

/-- Utility of consumption `u(c) = c^{1−σ}/(1 − σ)`, and `log c` when `σ = 1` (AKMM, p. 332). -/
noncomputable def crraU (σ c : ℝ) : ℝ := if σ = 1 then Real.log c else c ^ (1 - σ) / (1 - σ)

/-- Disutility of work `v(ℓ) = ψℓ^{1+1/γ}/(1 + 1/γ)` (AKMM, p. 332). -/
noncomputable def disutil (ψ γ ℓ : ℝ) : ℝ := ψ * ℓ ^ (1 + 1 / γ) / (1 + 1 / γ)

/-- The static objective `u(wℓ + I) − v(ℓ)` after substituting the budget (AKMM, p. 332). -/
noncomputable def stObj (ψ γ σ w I ℓ : ℝ) : ℝ := crraU σ (w * ℓ + I) - disutil ψ γ ℓ

/-- `u′(c) = c^{−σ}` for `c > 0`, for every `σ` (including the logarithmic case). -/
theorem st_crraU_hasDerivAt {σ c : ℝ} (hc : 0 < c) : HasDerivAt (crraU σ) (c ^ (-σ)) c := by
  by_cases hσ : σ = 1
  · subst hσ
    have h : crraU 1 = Real.log := by
      funext x
      simp only [crraU, ↓reduceIte]
    rw [h, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hc.ne'
  · have h : crraU σ = fun x => x ^ (1 - σ) / (1 - σ) := by
      funext x
      simp only [crraU, hσ, ↓reduceIte]
    rw [h]
    have hs : (1 - σ) ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    have := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).div_const (1 - σ)
    convert this using 1
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp

/-- `v′(ℓ) = ψℓ^{1/γ}` for every `ℓ` (the exponent `1 + 1/γ ≥ 1`), `γ > 0`. -/
theorem st_disutil_hasDerivAt {ψ γ : ℝ} (hγ : 0 < γ) (ℓ : ℝ) :
    HasDerivAt (disutil ψ γ) (ψ * ℓ ^ (1 / γ)) ℓ := by
  have hγ' : 0 < 1 / γ := by positivity
  have hp : (1 : ℝ) ≤ 1 + 1 / γ := by linarith
  have hp0 : (1 + 1 / γ) ≠ 0 := by linarith
  have := ((Real.hasDerivAt_rpow_const (x := ℓ) (Or.inr hp)).const_mul ψ).div_const (1 + 1 / γ)
  refine this.congr_deriv ?_
  rw [show 1 + 1 / γ - 1 = 1 / γ by ring]
  field_simp

/-- The derivative of the static objective: `w(wℓ + I)^{−σ} − ψℓ^{1/γ}`. -/
theorem st_obj_hasDerivAt {ψ γ σ w I ℓ : ℝ} (hγ : 0 < γ) (hc : 0 < w * ℓ + I) :
    HasDerivAt (stObj ψ γ σ w I) (w * (w * ℓ + I) ^ (-σ) - ψ * ℓ ^ (1 / γ)) ℓ := by
  have h1 := (st_crraU_hasDerivAt (σ := σ) hc).comp ℓ
    (((hasDerivAt_id ℓ).const_mul w).add_const I)
  exact (h1.sub (st_disutil_hasDerivAt (ψ := ψ) hγ ℓ)).congr_deriv (by ring)

/-- The marginal value of work factors as `c^{−σ}(w − ψℓ^{1/γ}c^σ)`. -/
theorem st_deriv_factor {ψ γ σ w ℓ c : ℝ} (hc : 0 < c) :
    w * c ^ (-σ) - ψ * ℓ ^ (1 / γ) = c ^ (-σ) * (w - ψ * ℓ ^ (1 / γ) * c ^ σ) := by
  have h : c ^ (-σ) * c ^ σ = 1 := by
    rw [Real.rpow_neg hc.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hc σ).ne']
  linear_combination (ψ * ℓ ^ (1 / γ)) * h

/-- (12.1) in multiplicative form: `ψℓ^{1/γ}/(wℓ + I)^{−σ} = ψℓ^{1/γ}(wℓ + I)^σ`. -/
theorem st_foc_form {ψ γ σ ℓ c : ℝ} (hc : 0 < c) :
    ψ * ℓ ^ (1 / γ) / c ^ (-σ) = ψ * ℓ ^ (1 / γ) * c ^ σ := by
  rw [Real.rpow_neg hc.le, div_inv_eq_mul]

/-- The left side of (12.1), `ψℓ^{1/γ}(wℓ + I)^σ`, is strictly increasing in `ℓ ≥ 0`. -/
theorem st_foc_strictMono {ψ γ σ w I a b : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 < σ)
    (hw : 0 < w) (hI : 0 ≤ I) (ha : 0 ≤ a) (hab : a < b) :
    ψ * a ^ (1 / γ) * (w * a + I) ^ σ < ψ * b ^ (1 / γ) * (w * b + I) ^ σ := by
  have hg : 0 < 1 / γ := by positivity
  have h1 : a ^ (1 / γ) < b ^ (1 / γ) := Real.rpow_lt_rpow ha hab hg
  have hca : 0 ≤ w * a + I := by positivity
  have hcb : 0 < w * b + I := by nlinarith
  have h2 : (w * a + I) ^ σ ≤ (w * b + I) ^ σ :=
    Real.rpow_le_rpow hca (by nlinarith) hσ.le
  have h3 : 0 < (w * b + I) ^ σ := Real.rpow_pos_of_pos hcb σ
  have h4 : 0 ≤ a ^ (1 / γ) := Real.rpow_nonneg ha _
  have h5 : 0 ≤ (w * a + I) ^ σ := Real.rpow_nonneg hca _
  have : a ^ (1 / γ) * (w * a + I) ^ σ < b ^ (1 / γ) * (w * b + I) ^ σ := by
    calc a ^ (1 / γ) * (w * a + I) ^ σ ≤ a ^ (1 / γ) * (w * b + I) ^ σ :=
          mul_le_mul_of_nonneg_left h2 h4
      _ < b ^ (1 / γ) * (w * b + I) ^ σ := mul_lt_mul_of_pos_right h1 h3
  rw [mul_assoc, mul_assoc]
  exact mul_lt_mul_of_pos_left this hψ

/-- **The optimum is unique and interior; (12.1)** (AKMM, p. 332). With `ψ, γ, σ, w > 0` and
`I ≥ 0` there is exactly one `ℓ* > 0` satisfying (12.1), `ψℓ^{1/γ}/(wℓ + I)^{−σ} = w`; it gives
strictly higher utility than every other `ℓ > 0`, and, when `I > 0` (so that `ℓ = 0` is
feasible with `c > 0`), also than `ℓ = 0`: "the individual will always choose `ℓ > 0`". -/
theorem eq_12_1 {ψ γ σ w I : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 < σ) (hw : 0 < w)
    (hI : 0 ≤ I) :
    ∃ ℓs, 0 < ℓs ∧ ψ * ℓs ^ (1 / γ) / (w * ℓs + I) ^ (-σ) = w ∧
      (∀ ℓ, 0 < ℓ → ψ * ℓ ^ (1 / γ) / (w * ℓ + I) ^ (-σ) = w → ℓ = ℓs) ∧
      (∀ ℓ, 0 < ℓ → ℓ ≠ ℓs → stObj ψ γ σ w I ℓ < stObj ψ γ σ w I ℓs) ∧
      (0 < I → stObj ψ γ σ w I 0 < stObj ψ γ σ w I ℓs) := by
  set g : ℝ → ℝ := fun ℓ => ψ * ℓ ^ (1 / γ) * (w * ℓ + I) ^ σ with hgdef
  have hg0 : g 0 = 0 := by
    simp only [hgdef, Real.zero_rpow (one_div_pos.2 hγ).ne', mul_zero, zero_mul]
  -- a point where `g ≥ w`
  set e : ℝ := 1 / γ + σ with he
  have hepos : 0 < e := by positivity
  set ℓ0 : ℝ := (w ^ (1 - σ) / ψ) ^ e⁻¹ with hℓ0
  have hℓ0pos : 0 < ℓ0 := Real.rpow_pos_of_pos (by positivity) _
  have hgℓ0 : w ≤ g ℓ0 := by
    have hb : (w * ℓ0) ^ σ ≤ (w * ℓ0 + I) ^ σ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hσ.le
    have heq : ψ * ℓ0 ^ (1 / γ) * (w * ℓ0) ^ σ = w := by
      rw [Real.mul_rpow hw.le hℓ0pos.le]
      have h1 : ℓ0 ^ (1 / γ) * ℓ0 ^ σ = ℓ0 ^ e := by rw [← Real.rpow_add hℓ0pos]
      have h2 : ℓ0 ^ e = w ^ (1 - σ) / ψ := by
        rw [hℓ0, Real.rpow_inv_rpow (by positivity) hepos.ne']
      have h3 : w ^ σ * w ^ (1 - σ) = w := by
        rw [← Real.rpow_add hw, show σ + (1 - σ) = 1 by ring, Real.rpow_one]
      calc ψ * ℓ0 ^ (1 / γ) * (w ^ σ * ℓ0 ^ σ) = ψ * w ^ σ * (ℓ0 ^ (1 / γ) * ℓ0 ^ σ) := by ring
        _ = w := by
          rw [h1, h2]
          have h4 : ψ * w ^ σ * (w ^ (1 - σ) / ψ) = w ^ σ * w ^ (1 - σ) := by field_simp
          rw [h4, h3]
    have hpos : 0 ≤ ψ * ℓ0 ^ (1 / γ) := by positivity
    calc w = ψ * ℓ0 ^ (1 / γ) * (w * ℓ0) ^ σ := heq.symm
      _ ≤ g ℓ0 := mul_le_mul_of_nonneg_left hb hpos
  have hgcont : ContinuousOn g (Set.Icc 0 ℓ0) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hx0 : 0 ≤ w * x + I := by have := hx.1; positivity
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _
      (Or.inr (one_div_pos.2 hγ).le))).mul
      (Real.continuousAt_rpow_const _ _ (Or.inr hσ.le) |>.comp
        ((continuousAt_const.mul continuousAt_id).add continuousAt_const))
  obtain ⟨ℓs, hℓsI, hgs⟩ : ∃ ℓs ∈ Set.Icc 0 ℓ0, g ℓs = w := by
    have := intermediate_value_Icc hℓ0pos.le hgcont
    exact this ⟨by rw [hg0]; exact hw.le, hgℓ0⟩
  have hℓspos : 0 < ℓs := by
    rcases eq_or_lt_of_le hℓsI.1 with h | h
    · rw [← h, hg0] at hgs; exact absurd hgs hw.ne
    · exact h
  have hmono : ∀ a b, 0 ≤ a → a < b → g a < g b := fun a b ha hab =>
    st_foc_strictMono hψ hγ hσ hw hI ha hab
  -- the derivative of the objective
  have hder : ∀ ℓ, 0 ≤ ℓ → 0 < w * ℓ + I → HasDerivAt (stObj ψ γ σ w I)
      ((w * ℓ + I) ^ (-σ) * (w - g ℓ)) ℓ := by
    intro ℓ _ hc
    have := st_obj_hasDerivAt (ψ := ψ) (σ := σ) hγ hc
    rwa [st_deriv_factor hc] at this
  have hcpos : ∀ ℓ, 0 < ℓ → 0 < w * ℓ + I := fun ℓ hℓ => by positivity
  have hfoc_iff : ∀ ℓ, 0 < ℓ → (ψ * ℓ ^ (1 / γ) / (w * ℓ + I) ^ (-σ) = w ↔ g ℓ = w) :=
    fun ℓ hℓ => by rw [st_foc_form (hcpos ℓ hℓ)]
  refine ⟨ℓs, hℓspos, (hfoc_iff ℓs hℓspos).2 hgs, fun ℓ hℓ hfoc => ?_, fun ℓ hℓ hne => ?_,
    fun hIpos => ?_⟩
  · have hgl := (hfoc_iff ℓ hℓ).1 hfoc
    rcases lt_trichotomy ℓ ℓs with h | h | h
    · have := hmono ℓ ℓs hℓ.le h; linarith
    · exact h
    · have := hmono ℓs ℓ hℓspos.le h; linarith
  · -- increasing on `(0, ℓs]`, decreasing on `[ℓs, ∞)`
    rcases lt_or_gt_of_ne hne with h | h
    · have hsm : StrictMonoOn (stObj ψ γ σ w I) (Set.Ioc 0 ℓs) := by
        apply strictMonoOn_of_deriv_pos (convex_Ioc 0 ℓs)
        · intro x hx
          exact (hder x hx.1.le (hcpos x hx.1)).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Ioc] at hx
          rw [(hder x hx.1.le (hcpos x hx.1)).deriv]
          have := hmono x ℓs hx.1.le hx.2
          exact mul_pos (Real.rpow_pos_of_pos (hcpos x hx.1) _) (by linarith)
      exact hsm ⟨hℓ, h.le⟩ ⟨hℓspos, le_rfl⟩ h
    · have hsa : StrictAntiOn (stObj ψ γ σ w I) (Set.Ici ℓs) := by
        apply strictAntiOn_of_deriv_neg (convex_Ici ℓs)
        · intro x hx
          have hx0 : 0 < x := lt_of_lt_of_le hℓspos hx
          exact (hder x hx0.le (hcpos x hx0)).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Ici] at hx
          have hx0 : 0 < x := lt_trans hℓspos hx
          rw [(hder x hx0.le (hcpos x hx0)).deriv]
          have := hmono ℓs x hℓspos.le hx
          exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (hcpos x hx0) _) (by linarith)
      exact hsa (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h.le) h
  · have hc0 : ∀ x, 0 ≤ x → 0 < w * x + I := fun x hx => by positivity
    have hsm : StrictMonoOn (stObj ψ γ σ w I) (Set.Icc 0 ℓs) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 ℓs)
      · intro x hx
        exact (hder x hx.1 (hc0 x hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hder x hx.1.le (hc0 x hx.1.le)).deriv]
        have := hmono x ℓs hx.1.le hx.2
        exact mul_pos (Real.rpow_pos_of_pos (hc0 x hx.1.le) _) (by linarith)
    exact hsm ⟨le_rfl, hℓspos.le⟩ ⟨hℓspos.le, le_rfl⟩ hℓspos

/-! ### Differentiating (12.1) along a path -/

/-- **The differentiated first-order condition** (AKMM, pp. 333 and 343, (12.12)–(12.14)). Let
`w(s)` (the net wage), `I(s)` and `ℓ(s)` be differentiable at `0` with `w, ℓ, c > 0` there,
`c = wℓ + I`, and let (12.1) hold for all `s` near `0`. Then
`(1/γ)ℓ′/ℓ + σ(w′ℓ + wℓ′ + I′)/c = w′/w`. -/
theorem st_path_identity {ψ γ σ : ℝ} {w I ℓ : ℝ → ℝ} {w' I' ℓ' : ℝ} (hψ : 0 < ψ)
    (hw : 0 < w 0) (hℓ : 0 < ℓ 0) (hc : 0 < w 0 * ℓ 0 + I 0)
    (hdw : HasDerivAt w w' 0) (hdI : HasDerivAt I I' 0) (hdℓ : HasDerivAt ℓ ℓ' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * ℓ s ^ (1 / γ) / (w s * ℓ s + I s) ^ (-σ) = w s) :
    1 / γ * (ℓ' / ℓ 0) + σ * ((w' * ℓ 0 + w 0 * ℓ' + I') / (w 0 * ℓ 0 + I 0)) =
      w' / w 0 := by
  have hdC : HasDerivAt (fun s => w s * ℓ s + I s) (w' * ℓ 0 + w 0 * ℓ' + I') 0 :=
    (hdw.mul hdℓ).add hdI
  have hF : HasDerivAt (fun s => Real.log ψ + 1 / γ * Real.log (ℓ s) +
      σ * Real.log (w s * ℓ s + I s) - Real.log (w s))
      (0 + 1 / γ * (ℓ' / ℓ 0) + σ * ((w' * ℓ 0 + w 0 * ℓ' + I') / (w 0 * ℓ 0 + I 0)) -
        w' / w 0) 0 :=
    (((hasDerivAt_const _ _).add ((hdℓ.log hℓ.ne').const_mul _)).add
      ((hdC.log hc.ne').const_mul _)).sub (hdw.log hw.ne')
  have hℓe : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < ℓ s := hdℓ.continuousAt.eventually (lt_mem_nhds hℓ)
  have hwe : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < w s := hdw.continuousAt.eventually (lt_mem_nhds hw)
  have hce : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < w s * ℓ s + I s :=
    hdC.continuousAt.eventually (lt_mem_nhds hc)
  have hzero : (fun s => Real.log ψ + 1 / γ * Real.log (ℓ s) +
      σ * Real.log (w s * ℓ s + I s) - Real.log (w s)) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hfoc, hℓe, hwe, hce] with s hf hl _ hcs
    rw [st_foc_form hcs] at hf
    have := congrArg Real.log hf
    rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hcs σ).ne',
      Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl _).ne', Real.log_rpow hl,
      Real.log_rpow hcs] at this
    linarith
  have h0 := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero
  have := hF.unique h0
  linarith

/-- `st_path_identity` with denominators cleared:
`wcℓ′ + γσwℓ(w′ℓ + wℓ′ + I′) = γℓcw′`, `c = wℓ + I`. -/
theorem st_path_poly {ψ γ σ : ℝ} {w I ℓ : ℝ → ℝ} {w' I' ℓ' : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hw : 0 < w 0) (hℓ : 0 < ℓ 0) (hc : 0 < w 0 * ℓ 0 + I 0)
    (hdw : HasDerivAt w w' 0) (hdI : HasDerivAt I I' 0) (hdℓ : HasDerivAt ℓ ℓ' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * ℓ s ^ (1 / γ) / (w s * ℓ s + I s) ^ (-σ) = w s) :
    w 0 * (w 0 * ℓ 0 + I 0) * ℓ' + γ * σ * w 0 * ℓ 0 * (w' * ℓ 0 + w 0 * ℓ' + I') =
      γ * ℓ 0 * (w 0 * ℓ 0 + I 0) * w' := by
  have key := st_path_identity hψ hw hℓ hc hdw hdI hdℓ hfoc
  set c := w 0 * ℓ 0 + I 0
  have hc' : c ≠ 0 := hc.ne'
  have hγ' : γ ≠ 0 := hγ.ne'
  have hℓ' : ℓ 0 ≠ 0 := hℓ.ne'
  have hw' : w 0 ≠ 0 := hw.ne'
  field_simp at key
  linear_combination key

/-- The path `s ↦ we^s` has derivative `w` at `0`. -/
theorem st_exp_path (w : ℝ) : HasDerivAt (fun s => w * Real.exp s) w 0 := by
  have := (Real.hasDerivAt_exp 0).const_mul w
  rwa [Real.exp_zero, mul_one] at this

/-- AKMM, (12.3), p. 333: **the Marshallian elasticity**. Along `w(s) = we^s` with `I` fixed,
optimal hours satisfy `d log ℓ/d log w = (1 − σ(1 − s_I))/(1/γ + σ(1 − s_I))`, where
`s_I = I/(wℓ + I)`. -/
theorem eq_12_3 {ψ γ σ w I ℓ' : ℝ} {ℓ : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hw : 0 < w) (hℓ : 0 < ℓ 0) (hc : 0 < w * ℓ 0 + I) (hdℓ : HasDerivAt ℓ ℓ' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ),
      ψ * ℓ s ^ (1 / γ) / (w * Real.exp s * ℓ s + I) ^ (-σ) = w * Real.exp s) :
    HasDerivAt (fun s => Real.log (ℓ s))
      ((1 - σ * (1 - I / (w * ℓ 0 + I))) / (1 / γ + σ * (1 - I / (w * ℓ 0 + I)))) 0 := by
  have hw0 : 0 < w * Real.exp 0 := by rw [Real.exp_zero, mul_one]; exact hw
  have hc0 : 0 < w * Real.exp 0 * ℓ 0 + I := by rwa [Real.exp_zero, mul_one]
  have key := st_path_identity (I := fun _ => I) (I' := 0) hψ hw0 hℓ hc0 (st_exp_path w)
    (hasDerivAt_const _ _) hdℓ hfoc
  rw [Real.exp_zero, mul_one] at key
  refine (hdℓ.log hℓ.ne').congr_deriv ?_
  have ha : 1 - I / (w * ℓ 0 + I) = w * ℓ 0 / (w * ℓ 0 + I) := by field_simp; ring
  have hden : 0 < 1 / γ + σ * (1 - I / (w * ℓ 0 + I)) := by rw [ha]; positivity
  rw [eq_div_iff hden.ne', ha]
  field_simp at key ⊢
  linear_combination key

/-- AKMM, (12.2), p. 333: **the income elasticity**. Along `I(s) = Ie^s` with `w` fixed,
`d log ℓ/d log I = −σs_I/(1/γ + σ(1 − s_I))`. -/
theorem eq_12_2 {ψ γ σ w I ℓ' : ℝ} {ℓ : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hw : 0 < w) (hℓ : 0 < ℓ 0) (hc : 0 < w * ℓ 0 + I) (hdℓ : HasDerivAt ℓ ℓ' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ),
      ψ * ℓ s ^ (1 / γ) / (w * ℓ s + I * Real.exp s) ^ (-σ) = w) :
    HasDerivAt (fun s => Real.log (ℓ s))
      (-σ * (I / (w * ℓ 0 + I)) / (1 / γ + σ * (1 - I / (w * ℓ 0 + I)))) 0 := by
  have hc0 : 0 < w * ℓ 0 + I * Real.exp 0 := by rwa [Real.exp_zero, mul_one]
  have key := st_path_poly (w := fun _ => w) (w' := 0) hψ hγ hw hℓ hc0
    (hasDerivAt_const _ _) (st_exp_path I) hdℓ hfoc
  simp only [Real.exp_zero, mul_one, zero_mul, mul_zero, zero_add] at key
  refine (hdℓ.log hℓ.ne').congr_deriv ?_
  have ha : 1 - I / (w * ℓ 0 + I) = w * ℓ 0 / (w * ℓ 0 + I) := by field_simp; ring
  have hden : 0 < 1 / γ + σ * (1 - I / (w * ℓ 0 + I)) := by rw [ha]; positivity
  have hD : 0 < w * ℓ 0 + I + γ * σ * w * ℓ 0 := by
    have : 0 ≤ γ * σ * w * ℓ 0 := by positivity
    linarith
  have hl : ℓ' = -(γ * σ * ℓ 0 * I) / (w * ℓ 0 + I + γ * σ * w * ℓ 0) := by
    rw [eq_div_iff hD.ne']
    have h : w * (ℓ' * (w * ℓ 0 + I + γ * σ * w * ℓ 0) + γ * σ * ℓ 0 * I) = 0 := by
      linear_combination key
    linarith [(mul_eq_zero.1 h).resolve_left hw.ne']
  rw [hl, ha]
  have h1 : w * ℓ 0 + I ≠ 0 := hc.ne'
  have h2 : ℓ 0 * w + I ≠ 0 := by rw [mul_comm]; exact hc.ne'
  have h3 : I + ℓ 0 * w ≠ 0 := by rw [add_comm]; exact h2
  have h4 : γ ≠ 0 := hγ.ne'
  field_simp

/-- AKMM, footnote 2, p. 333, **corrected**: along `I(s) = I + s` with `w` fixed, the
derivative of optimal hours with respect to non-labour income is
`ℓ₂ = −σ(1 − s_I)/(w[1/γ + σ(1 − s_I)])` (the printed value omits the factor `1/w`). -/
theorem st_footnote_2 {ψ γ σ w I ℓ' : ℝ} {ℓ : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hw : 0 < w) (hℓ : 0 < ℓ 0) (hc : 0 < w * ℓ 0 + I) (hdℓ : HasDerivAt ℓ ℓ' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * ℓ s ^ (1 / γ) / (w * ℓ s + (I + s)) ^ (-σ) = w) :
    ℓ' = -σ * (1 - I / (w * ℓ 0 + I)) / (w * (1 / γ + σ * (1 - I / (w * ℓ 0 + I)))) := by
  have hc0 : 0 < w * ℓ 0 + (I + 0) := by rwa [add_zero]
  have key := st_path_poly (w := fun _ => w) (w' := 0) (I := fun s => I + s) (I' := 1)
    hψ hγ hw hℓ hc0 (hasDerivAt_const _ _) ((hasDerivAt_id 0).const_add I) hdℓ hfoc
  simp only [add_zero, zero_mul, mul_zero, zero_add] at key
  have ha : 1 - I / (w * ℓ 0 + I) = w * ℓ 0 / (w * ℓ 0 + I) := by field_simp; ring
  have hden : 0 < 1 / γ + σ * (1 - I / (w * ℓ 0 + I)) := by rw [ha]; positivity
  have hD : 0 < w * ℓ 0 + I + γ * σ * w * ℓ 0 := by
    have : 0 ≤ γ * σ * w * ℓ 0 := by positivity
    linarith
  have hl : ℓ' = -(γ * σ * ℓ 0) / (w * ℓ 0 + I + γ * σ * w * ℓ 0) := by
    rw [eq_div_iff hD.ne']
    have h : w * (ℓ' * (w * ℓ 0 + I + γ * σ * w * ℓ 0) + γ * σ * ℓ 0) = 0 := by
      linear_combination key
    linarith [(mul_eq_zero.1 h).resolve_left hw.ne']
  rw [hl, ha]
  have h1 : w * ℓ 0 + I ≠ 0 := hc.ne'
  have h2 : ℓ 0 * w + I ≠ 0 := by rw [mul_comm]; exact hc.ne'
  have h3 : I + ℓ 0 * w ≠ 0 := by rw [add_comm]; exact h2
  have h4 : γ ≠ 0 := hγ.ne'
  field_simp

/-- AKMM, (12.4), p. 334: **the Hicksian elasticity**. Along `w(s) = we^s` with income
compensated, `I′(0) = −ℓ·w′(0) = −wℓ` (the wage gain is taken away), optimal hours satisfy
`d log ℓ/d log w = 1/(1/γ + σ(1 − s_I))`. -/
theorem eq_12_4 {ψ γ σ w I' ℓ' : ℝ} {I ℓ : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hw : 0 < w) (hℓ : 0 < ℓ 0) (hc : 0 < w * ℓ 0 + I 0) (hdI : HasDerivAt I I' 0)
    (hcomp : I' = -(w * ℓ 0)) (hdℓ : HasDerivAt ℓ ℓ' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ),
      ψ * ℓ s ^ (1 / γ) / (w * Real.exp s * ℓ s + I s) ^ (-σ) = w * Real.exp s) :
    HasDerivAt (fun s => Real.log (ℓ s))
      (1 / (1 / γ + σ * (1 - I 0 / (w * ℓ 0 + I 0)))) 0 := by
  have hw0 : 0 < w * Real.exp 0 := by rw [Real.exp_zero, mul_one]; exact hw
  have hc0 : 0 < w * Real.exp 0 * ℓ 0 + I 0 := by rwa [Real.exp_zero, mul_one]
  have key := st_path_identity hψ hw0 hℓ hc0 (st_exp_path w) hdI hdℓ hfoc
  rw [Real.exp_zero, mul_one, hcomp] at key
  refine (hdℓ.log hℓ.ne').congr_deriv ?_
  have ha : 1 - I 0 / (w * ℓ 0 + I 0) = w * ℓ 0 / (w * ℓ 0 + I 0) := by field_simp; ring
  have hden : 0 < 1 / γ + σ * (1 - I 0 / (w * ℓ 0 + I 0)) := by rw [ha]; positivity
  rw [eq_div_iff hden.ne', ha]
  field_simp at key ⊢
  linear_combination key

/-- AKMM, p. 334 ("the change in hours … holding utility constant"): along any differentiable
path with (12.1) at `s = 0`, utility changes at rate `c^{−σ}(w′ℓ + I′)`; so it is constant to
first order exactly on the compensated paths `I′ = −ℓw′` used in `eq_12_4`. -/
theorem st_compensated_utility {ψ γ σ : ℝ} {w I ℓ : ℝ → ℝ} {w' I' ℓ' : ℝ} (hγ : 0 < γ)
    (hc : 0 < w 0 * ℓ 0 + I 0) (hdw : HasDerivAt w w' 0) (hdI : HasDerivAt I I' 0)
    (hdℓ : HasDerivAt ℓ ℓ' 0)
    (hfoc : ψ * ℓ 0 ^ (1 / γ) / (w 0 * ℓ 0 + I 0) ^ (-σ) = w 0) :
    HasDerivAt (fun s => stObj ψ γ σ (w s) (I s) (ℓ s))
      ((w 0 * ℓ 0 + I 0) ^ (-σ) * (w' * ℓ 0 + I')) 0 := by
  have hdC : HasDerivAt (fun s => w s * ℓ s + I s) (w' * ℓ 0 + w 0 * ℓ' + I') 0 :=
    (hdw.mul hdℓ).add hdI
  have h1 := (st_crraU_hasDerivAt (σ := σ) hc).comp 0 hdC
  have h2 := (st_disutil_hasDerivAt (ψ := ψ) hγ (ℓ 0)).comp 0 hdℓ
  refine (h1.sub h2).congr_deriv ?_
  rw [st_foc_form hc] at hfoc
  have hinv : (w 0 * ℓ 0 + I 0) ^ (-σ) * (w 0 * ℓ 0 + I 0) ^ σ = 1 := by
    rw [Real.rpow_neg hc.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hc σ).ne']
  have : ψ * ℓ 0 ^ (1 / γ) = w 0 * (w 0 * ℓ 0 + I 0) ^ (-σ) := by
    linear_combination (-(ψ * ℓ 0 ^ (1 / γ))) * hinv + (w 0 * ℓ 0 + I 0) ^ (-σ) * hfoc
  rw [this]
  ring

/-- AKMM, p. 334, **the Slutsky decomposition** `ε^H = ε^M − ((1 − s_I)/s_I)ε_{ℓ,I}`: an
identity between the values (12.2)–(12.4), for `s_I ≠ 0`. -/
theorem st_slutsky {γ σ sI : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) (hs0 : sI ≠ 0) (hs1 : sI < 1) :
    1 / (1 / γ + σ * (1 - sI)) = (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) -
      (1 - sI) / sI * (-σ * sI / (1 / γ + σ * (1 - sI))) := by
  have hden : 0 < 1 / γ + σ * (1 - sI) := by
    have : 0 ≤ σ * (1 - sI) := mul_nonneg hσ (by linarith)
    have : 0 < 1 / γ := by positivity
    linarith
  field_simp
  ring

/-- AKMM, p. 334: the substitution effect `ℓ₁ − ℓ·ℓ₂`, in elasticity form
`(w/ℓ)(ℓ₁ − ℓℓ₂)`, is the Hicksian elasticity (12.4). Here `ℓ₁` is the derivative of hours along
`w + s` and `ℓ₂` along `I + s`. -/
theorem st_substitution_effect {ψ γ σ w I ℓ₁ ℓ₂ : ℝ} {ℓa ℓb : ℝ → ℝ} (hψ : 0 < ψ)
    (hγ : 0 < γ) (hσ : 0 ≤ σ) (hw : 0 < w) (hℓ : 0 < ℓa 0) (hab : ℓb 0 = ℓa 0)
    (hc : 0 < w * ℓa 0 + I) (hda : HasDerivAt ℓa ℓ₁ 0) (hdb : HasDerivAt ℓb ℓ₂ 0)
    (hfa : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * ℓa s ^ (1 / γ) / ((w + s) * ℓa s + I) ^ (-σ) = w + s)
    (hfb : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * ℓb s ^ (1 / γ) / (w * ℓb s + (I + s)) ^ (-σ) = w) :
    w / ℓa 0 * (ℓ₁ - ℓa 0 * ℓ₂) = 1 / (1 / γ + σ * (1 - I / (w * ℓa 0 + I))) := by
  have hw0 : 0 < w + 0 := by rwa [add_zero]
  have hc0 : 0 < (w + 0) * ℓa 0 + I := by rwa [add_zero]
  have ka := st_path_poly (I := fun _ => I) (I' := 0) hψ hγ hw0 hℓ hc0
    ((hasDerivAt_id 0).const_add w) (hasDerivAt_const _ _) hda hfa
  have hc1 : 0 < w * ℓb 0 + (I + 0) := by rw [hab, add_zero]; exact hc
  have kb := st_path_poly (w := fun _ => w) (w' := 0) (I := fun s => I + s) (I' := 1)
    hψ hγ hw (hab ▸ hℓ) hc1 (hasDerivAt_const _ _) ((hasDerivAt_id 0).const_add I) hdb hfb
  simp only [add_zero, zero_mul, mul_zero, zero_add, hab] at ka kb
  have ha : 1 - I / (w * ℓa 0 + I) = w * ℓa 0 / (w * ℓa 0 + I) := by field_simp; ring
  rw [ha]
  have hc' : w * ℓa 0 + I ≠ 0 := hc.ne'
  have hγ' : γ ≠ 0 := hγ.ne'
  have hℓ' : ℓa 0 ≠ 0 := hℓ.ne'
  have hden : w * ℓa 0 + I + γ * σ * (w * ℓa 0) ≠ 0 := by
    have : 0 ≤ γ * σ * (w * ℓa 0) := by positivity
    linarith
  field_simp
  linear_combination ka - ℓa 0 * kb

/-! ### Signs -/

/-- AKMM, pp. 333–334, **signs of the elasticities** (12.2)–(12.4), with `σ ≥ 0`, `γ > 0` and
`s_I < 1`: the income elasticity is negative when `s_I > 0` and `σ > 0`; the Hicksian elasticity
is positive; it is at least the Marshallian one, with equality iff `σ = 0`. -/
theorem st_signs {γ σ sI : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) (hs1 : sI < 1) :
    (0 < σ → 0 < sI → -σ * sI / (1 / γ + σ * (1 - sI)) < 0) ∧
      0 < 1 / (1 / γ + σ * (1 - sI)) ∧
      (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) ≤ 1 / (1 / γ + σ * (1 - sI)) ∧
      ((1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) = 1 / (1 / γ + σ * (1 - sI)) ↔ σ = 0) := by
  have hg : 0 < 1 / γ := by positivity
  have hden : 0 < 1 / γ + σ * (1 - sI) := by
    have : 0 ≤ σ * (1 - sI) := mul_nonneg hσ (by linarith)
    linarith
  refine ⟨fun h1 h2 => div_neg_of_neg_of_pos (by nlinarith) hden, by positivity,
    div_le_div_of_nonneg_right (by nlinarith) hden.le, ⟨fun h => ?_, fun h => by subst h; simp⟩⟩
  rw [div_left_inj' hden.ne'] at h
  have : σ * (1 - sI) = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · exact h'
  · exact absurd h' (by linarith)

/-- AKMM, p. 334: with `I = 0`, `ε^M = (1 − σ)/(1/γ + σ)` is positive iff `σ < 1`, negative iff
`σ > 1`, and zero iff `σ = 1`. -/
theorem st_zero_income_signs {γ σ : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) :
    (0 < (1 - σ) / (1 / γ + σ) ↔ σ < 1) ∧ ((1 - σ) / (1 / γ + σ) < 0 ↔ 1 < σ) ∧
      ((1 - σ) / (1 / γ + σ) = 0 ↔ σ = 1) := by
  have hden : 0 < 1 / γ + σ := by have : 0 < 1 / γ := by positivity
                                  linarith
  refine ⟨⟨fun h => ?_, fun h => div_pos (by linarith) hden⟩,
    ⟨fun h => ?_, fun h => div_neg_of_neg_of_pos (by linarith) hden⟩, ?_⟩
  · have := (div_pos_iff_of_pos_right hden).1 h; linarith
  · by_contra hc
    have := div_nonneg (by linarith [not_lt.1 hc] : 0 ≤ 1 - σ) hden.le
    linarith
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h; left; linarith

/-- AKMM, p. 334: at `σ = 1` and `I = 0` the Marshallian elasticity is zero while the
substitution effect `ε^H` and the income effect `ε^H − ε^M` are equal, both `γ/(1 + γ) > 0`
and strictly increasing in `γ`. -/
theorem st_effects_mono_gamma {γ₁ γ₂ : ℝ} (h₁ : 0 < γ₁) (h₁₂ : γ₁ < γ₂) :
    (1 - 1 * (1 - 0)) / (1 / γ₁ + 1 * (1 - 0)) = 0 ∧
      1 / (1 / γ₁ + 1 * (1 - 0)) = γ₁ / (1 + γ₁) ∧ 0 < γ₁ / (1 + γ₁) ∧
      γ₁ / (1 + γ₁) < γ₂ / (1 + γ₂) := by
  have h₂ : 0 < γ₂ := lt_trans h₁ h₁₂
  refine ⟨by ring, by field_simp; ring, by positivity, ?_⟩
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-! ### An explicit solution: the path hypotheses are satisfiable -/

/-- The optimal hours for `ψ = γ = σ = 1`: the positive root of `wℓ² + Iℓ − w = 0`. -/
noncomputable def stExplicit (w I : ℝ) : ℝ := (Real.sqrt (I ^ 2 + 4 * w ^ 2) - I) / (2 * w)

/-- For `ψ = γ = σ = 1` and `w > 0`, `stExplicit w I` is positive, gives `c > 0`, and solves
(12.1), `ℓ(wℓ + I) = w`, for every `I`. -/
theorem st_explicit_foc {w I : ℝ} (hw : 0 < w) :
    0 < stExplicit w I ∧ 0 < w * stExplicit w I + I ∧
      1 * stExplicit w I ^ (1 / (1 : ℝ)) / (w * stExplicit w I + I) ^ (-(1 : ℝ)) = w := by
  set S := Real.sqrt (I ^ 2 + 4 * w ^ 2) with hS
  have hS2 : S ^ 2 = I ^ 2 + 4 * w ^ 2 := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hm : 0 < S - I := by nlinarith
  have hp : 0 < S + I := by nlinarith
  have hl : 0 < stExplicit w I := div_pos hm (by positivity)
  have hc : w * stExplicit w I + I = (S + I) / 2 := by
    simp only [stExplicit, ← hS]; field_simp; ring
  refine ⟨hl, by rw [hc]; positivity, ?_⟩
  rw [div_one, Real.rpow_one, Real.rpow_neg_one, div_inv_eq_mul, one_mul, hc]
  simp only [stExplicit, ← hS]
  field_simp
  nlinarith

/-- For differentiable paths `w(s) > 0`, `I(s)`, the explicit solution is differentiable along
the path and solves (12.1) for all `s` near `0`. -/
theorem st_explicit_path {w I : ℝ → ℝ} {w' I' : ℝ} (hw : 0 < w 0) (hdw : HasDerivAt w w' 0)
    (hdI : HasDerivAt I I' 0) :
    (∃ ℓ', HasDerivAt (fun s => stExplicit (w s) (I s)) ℓ' 0) ∧
      ∀ᶠ s in 𝓝 (0 : ℝ), 1 * stExplicit (w s) (I s) ^ (1 / (1 : ℝ)) /
        (w s * stExplicit (w s) (I s) + I s) ^ (-(1 : ℝ)) = w s := by
  refine ⟨⟨_, DifferentiableAt.hasDerivAt ?_⟩, ?_⟩
  · have hpos : I 0 ^ 2 + 4 * w 0 ^ 2 ≠ 0 := by positivity
    have hq : HasDerivAt (fun s => I s ^ 2 + 4 * w s ^ 2) _ 0 :=
      (hdI.pow 2).add ((hdw.pow 2).const_mul 4)
    exact (((hq.sqrt hpos).sub hdI).div (hdw.const_mul 2) (by positivity)).differentiableAt
  · filter_upwards [hdw.continuousAt.eventually (lt_mem_nhds hw)] with s hs
    exact (st_explicit_foc hs).2.2

/-- AKMM, footnote 2, p. 333: **the printed `ℓ₂` is false**. With `ψ = γ = σ = 1`, `w = 2`,
`I = 1`, the explicit optimal hours along `I + s` have derivative
`−σ(1 − s_I)/(w[1/γ + σ(1 − s_I)])`, which differs from the printed
`−σ(1 − s_I)/[1/γ + σ(1 − s_I)]`. -/
theorem st_footnote_2_printed_false :
    ∃ ℓ' : ℝ, HasDerivAt (fun s => stExplicit 2 (1 + s)) ℓ' 0 ∧
      ℓ' ≠ -1 * (1 - 1 / (2 * stExplicit 2 1 + 1)) /
        (1 / 1 + 1 * (1 - 1 / (2 * stExplicit 2 1 + 1))) := by
  obtain ⟨⟨ℓ', hd⟩, hfoc⟩ := st_explicit_path (w := fun _ => 2) (I := fun s => 1 + s)
    (by norm_num) (hasDerivAt_const 0 2) ((hasDerivAt_id 0).const_add 1)
  obtain ⟨hl, hc, _⟩ := st_explicit_foc (w := 2) (I := 1) (by norm_num)
  refine ⟨ℓ', hd, fun h => ?_⟩
  have hf := st_footnote_2 (ψ := 1) (γ := 1) (σ := 1) (w := 2) (I := 1)
    (ℓ := fun s => stExplicit 2 (1 + s)) one_pos one_pos zero_le_one two_pos
    (by simpa using hl) (by simpa using hc) hd (by simpa using hfoc)
  simp only [add_zero] at hf
  rw [hf] at h
  set a := 1 - 1 / (2 * stExplicit 2 1 + 1)
  have ha : 0 < a := by
    have : 1 / (2 * stExplicit 2 1 + 1) < 1 := by
      rw [div_lt_one hc]; linarith
    simp only [a]; linarith
  have hd1 : 0 < 1 / 1 + 1 * a := by positivity
  field_simp at h
  nlinarith

/-! ### Taxes and transfers -/

/-- AKMM, p. 335: with a labour-income tax `τ` and transfer `T`, the budget
`c = (1 − τ)wℓ + y + T` makes the problem the benchmark one at the net wage `(1 − τ)w` and
non-labour income `y + T` (so a change in `1 − τ` acts as a change in `w`, and a change in `T`
as a change in `I`); in particular the response of hours to `1 − τ` is the Marshallian
elasticity (12.3). -/
theorem st_tax_as_wage {ψ γ σ τ w y T ℓ' : ℝ} {ℓ : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hσ : 0 ≤ σ) (hτ : τ < 1) (hw : 0 < w) (hℓ : 0 < ℓ 0) (hc : 0 < (1 - τ) * w * ℓ 0 + (y + T))
    (hdℓ : HasDerivAt ℓ ℓ' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * ℓ s ^ (1 / γ) /
      ((1 - τ) * Real.exp s * w * ℓ s + (y + T)) ^ (-σ) = (1 - τ) * Real.exp s * w) :
    (∀ l, crraU σ ((1 - τ) * w * l + (y + T)) - disutil ψ γ l =
      stObj ψ γ σ ((1 - τ) * w) (y + T) l) ∧
    HasDerivAt (fun s => Real.log (ℓ s))
      ((1 - σ * (1 - (y + T) / ((1 - τ) * w * ℓ 0 + (y + T)))) /
        (1 / γ + σ * (1 - (y + T) / ((1 - τ) * w * ℓ 0 + (y + T))))) 0 := by
  refine ⟨fun l => rfl, ?_⟩
  have hnet : 0 < (1 - τ) * w := mul_pos (by linarith) hw
  refine eq_12_3 hψ hγ hσ hnet hℓ hc hdℓ ?_
  filter_upwards [hfoc] with s hs
  rw [show (1 - τ) * w * Real.exp s = (1 - τ) * Real.exp s * w by ring]
  exact hs

/-- AKMM, p. 335, **budget-neutral taxes**: when the transfer rebates the revenue,
`T = τwℓ`, and the tax path is `1 − τ(s) = (1 − τ)e^s`, hours respond to the net wage with
elasticity `1/(1/γ + σwℓ/c)`, `c = wℓ + y`. The income effect of the tax change is removed;
the elasticity is the Hicksian one (12.4) computed with `s_I = y/c` (non-labour income other
than the transfer). -/
theorem st_balanced_budget {ψ γ σ τ w y ℓ' : ℝ} {ℓ : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hσ : 0 ≤ σ) (hτ : τ < 1) (hw : 0 < w) (hℓ : 0 < ℓ 0) (hc : 0 < w * ℓ 0 + y)
    (hdℓ : HasDerivAt ℓ ℓ' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * ℓ s ^ (1 / γ) /
      ((1 - τ) * w * Real.exp s * ℓ s + (y + (1 - (1 - τ) * Real.exp s) * (w * ℓ s))) ^ (-σ) =
        (1 - τ) * w * Real.exp s) :
    HasDerivAt (fun s => Real.log (ℓ s)) (1 / (1 / γ + σ * (w * ℓ 0 / (w * ℓ 0 + y)))) 0 := by
  have hnet : 0 < (1 - τ) * w := mul_pos (by linarith) hw
  have hW0 : 0 < (1 - τ) * w * Real.exp 0 := by rw [Real.exp_zero, mul_one]; exact hnet
  have hc0 : 0 < (1 - τ) * w * Real.exp 0 * ℓ 0 +
      (y + (1 - (1 - τ) * Real.exp 0) * (w * ℓ 0)) := by
    rw [Real.exp_zero, mul_one, mul_one]; linarith
  have hτp : HasDerivAt (fun s => 1 - (1 - τ) * Real.exp s) (-(1 - τ)) 0 := by
    have := (st_exp_path (1 - τ)).const_sub 1
    simpa using this
  have hdI : HasDerivAt (fun s => y + (1 - (1 - τ) * Real.exp s) * (w * ℓ s))
      (-(1 - τ) * (w * ℓ 0) + (1 - (1 - τ) * Real.exp 0) * (w * ℓ')) 0 :=
    (hτp.mul (hdℓ.const_mul w)).const_add y
  have key := st_path_poly (I := fun s => y + (1 - (1 - τ) * Real.exp s) * (w * ℓ s)) hψ hγ
    hW0 hℓ hc0 (st_exp_path ((1 - τ) * w)) hdI hdℓ hfoc
  simp only [Real.exp_zero, mul_one] at key
  have hD : 0 < w * ℓ 0 + y + γ * σ * w * ℓ 0 := by
    have : 0 ≤ γ * σ * w * ℓ 0 := by positivity
    linarith
  have hl : ℓ' = γ * ℓ 0 * (w * ℓ 0 + y) / (w * ℓ 0 + y + γ * σ * w * ℓ 0) := by
    rw [eq_div_iff hD.ne']
    have h : (1 - τ) * w * (ℓ' * (w * ℓ 0 + y + γ * σ * w * ℓ 0) -
        γ * ℓ 0 * (w * ℓ 0 + y)) = 0 := by linear_combination key
    linarith [(mul_eq_zero.1 h).resolve_left hnet.ne']
  refine (hdℓ.log hℓ.ne').congr_deriv ?_
  rw [hl]
  have h1 : w * ℓ 0 + y ≠ 0 := hc.ne'
  have h2 : ℓ 0 * w + y ≠ 0 := by rw [mul_comm]; exact hc.ne'
  have h3 : y + ℓ 0 * w ≠ 0 := by rw [add_comm]; exact h2
  have h4 : γ ≠ 0 := hγ.ne'
  have h5 : ℓ 0 ≠ 0 := hℓ.ne'
  field_simp

/-- AKMM, p. 335: the budget-neutral response of `st_balanced_budget` equals the Hicksian
elasticity (12.4) at `I = y + T` exactly when `τ = 0` (for `σ > 0`): with
`1 − s_I = (1 − τ)wℓ/c`, `1/(1/γ + σwℓ/c) = 1/(1/γ + σ(1 − s_I))` iff `τ = 0`. -/
theorem st_balanced_budget_hicks_iff {γ σ τ w y l : ℝ} (hγ : 0 < γ) (hσ : 0 < σ) (hτ : τ < 1)
    (hw : 0 < w) (hl : 0 < l) (hc : 0 < w * l + y) :
    1 / (1 / γ + σ * (w * l / (w * l + y))) =
        1 / (1 / γ + σ * (1 - (y + τ * w * l) / ((1 - τ) * w * l + (y + τ * w * l)))) ↔
      τ = 0 := by
  have hc' : (1 - τ) * w * l + (y + τ * w * l) = w * l + y := by ring
  rw [hc']
  have ha : 1 - (y + τ * w * l) / (w * l + y) = (1 - τ) * (w * l / (w * l + y)) := by
    field_simp; ring
  rw [ha]
  have hx : 0 < w * l / (w * l + y) := by positivity
  have hg : 0 < 1 / γ := by positivity
  have hd1 : 0 < 1 / γ + σ * (w * l / (w * l + y)) := by positivity
  have hd2 : 0 < 1 / γ + σ * ((1 - τ) * (w * l / (w * l + y))) := by
    have : 0 < (1 - τ) * (w * l / (w * l + y)) := mul_pos (by linarith) hx
    positivity
  rw [div_eq_div_iff hd1.ne' hd2.ne']
  constructor
  · intro h
    have : σ * (w * l / (w * l + y)) * τ = 0 := by linear_combination (-1 : ℝ) * h
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' (by positivity)
    · exact h'
  · intro h; subst h; ring

end AKMM.LaborSupply

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Richer static models and a first look at dynamics

AKMM, §12.3.2–12.3.3, pp. 335–341.

* **Home production.** At an interior optimum the two first-order conditions hold
  (`hp_focs`), and their ratio is (12.5), `g₂/g₁ = w/A` (`eq_12_5`). For the CES aggregator
  `g = [θc_m^η + (1 − θ)c_h^η]^{1/η}` the partial derivatives give
  `g₂/g₁ = ((1 − θ)/θ)(c_h/c_m)^{η−1}` (`hp_ces_partials`). With `I = 0`, (12.6) holds in the
  corrected form `ℓ_h/ℓ_m = ((1 − θ)/θ)^{1/(1−η)}(w/A)^{η/(η−1)}` (`eq_12_6`); the printed
  exponent `1/(η − 1)` on `(1 − θ)/θ` gives a different value unless `θ = 1/2`
  (`eq_12_6_printed_false`). For `0 < η < 1` the ratio is strictly decreasing in `w/A`
  (`hp_ratio_decreasing`).
* **Household labour supply.** At an interior optimum both members' first-order conditions hold
  (`hh_focs`), so `v′(ℓ_f)/v′(ℓ_m) = w_f/w_m` and `ℓ_f/ℓ_m = (w_f/w_m)^γ` (`hh_relative_hours`).
  The cross-wage elasticity of `ℓ_f` with respect to `w_m` is
  `−γσ(1 + γ)E_m/(c + γσ(E_f + E_m)) < 0`, `E_j = w_jℓ_j` (`hh_cross_wage`); and a lower `ℓ_m`
  raises `ℓ_f` (the added-worker effect, `hh_added_worker`, from `st_income_decreasing`).
* **Leisure in utility.** With `Ũ = u(c) + ṽ(ℓ̄ − ℓ)`, `ṽ(l) = l^{1−1/γ}/(1 − 1/γ)`, high
  non-labour income makes `ℓ = 0` optimal (`lt_corner`); the elasticity of disutility
  `ℓv′(ℓ)/v(ℓ) = 1 + 1/γ` is constant in the benchmark (`lt_benchmark_elasticity`), while that of
  `ṽ(ℓ̄ − ℓ)` is `−(1 − 1/γ)ℓ/(ℓ̄ − ℓ)` and tends to `−∞` as `ℓ → ℓ̄` when `γ > 1` but to `+∞`
  when `γ < 1` (`lt_elasticity`, `lt_elasticity_limits`).
* **Two periods.** With `β(1 + r) = 1` the first-order conditions give `c₁ = c₂` and
  `log ℓ₁ − log ℓ₂ = γ(log w₁ − log w₂)` (`tp_frisch`). Footnote 8 is corrected:
  `log ℓ_t = −γ log ψ + γ log w_t − γσ log c_t` (`footnote_8`, `footnote_8_printed_false`).
-/

namespace AKMM.LaborSupply

open Filter Topology

/-- Fermat's rule on `[0, ∞)`: a maximiser `x > 0` of `f` over `ℓ ≥ 0` where `f` has derivative
`f′` satisfies `f′ = 0`. -/
theorem ext_foc_of_max {f : ℝ → ℝ} {x f' : ℝ} (hx : 0 < x)
    (hmax : ∀ y, 0 ≤ y → f y ≤ f x) (hf : HasDerivAt f f' x) : f' = 0 := by
  refine IsLocalMax.hasDerivAt_eq_zero ?_ hf
  filter_upwards [lt_mem_nhds hx] with y hy using hmax y hy.le

/-! ### Home production -/

/-- AKMM, p. 336, **the first-order conditions of the home-production problem**
`max u(g(ℓ_m w + I, Aℓ_h)) − v(ℓ_m + ℓ_h)`: at a maximiser with `ℓ_m, ℓ_h > 0`,
`u′g₁w = v′` and `u′g₂A = v′`. -/
theorem hp_focs {u v : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {w I A lm lh u' v' g₁ g₂ : ℝ} (hlm : 0 < lm)
    (hlh : 0 < lh) (hu : HasDerivAt u u' (g (lm * w + I) (A * lh)))
    (hv : HasDerivAt v v' (lm + lh))
    (hg₁ : HasDerivAt (fun x => g x (A * lh)) g₁ (lm * w + I))
    (hg₂ : HasDerivAt (fun y => g (lm * w + I) y) g₂ (A * lh))
    (hmax : ∀ a b, 0 ≤ a → 0 ≤ b →
      u (g (a * w + I) (A * b)) - v (a + b) ≤ u (g (lm * w + I) (A * lh)) - v (lm + lh)) :
    u' * g₁ * w = v' ∧ u' * g₂ * A = v' := by
  constructor
  · have hd : HasDerivAt (fun a => u (g (a * w + I) (A * lh)) - v (a + lh))
        (u' * (g₁ * w) - v' * 1) lm := by
      have h1 := hu.comp lm (hg₁.comp lm ((hasDerivAt_mul_const w).add_const I))
      have h2 := hv.comp lm ((hasDerivAt_id lm).add_const lh)
      exact (h1.sub h2).congr_deriv (by simp)
    have := ext_foc_of_max hlm (fun a ha => hmax a lh ha hlh.le) hd
    linarith
  · have hd : HasDerivAt (fun b => u (g (lm * w + I) (A * b)) - v (lm + b))
        (u' * (g₂ * A) - v' * 1) lh := by
      have h1 := hu.comp lh (hg₂.comp lh (hasDerivAt_id lh |>.const_mul A))
      have h2 := hv.comp lh ((hasDerivAt_id lh).const_add lm)
      exact (h1.sub h2).congr_deriv (by simp)
    have := ext_foc_of_max hlh (fun b hb => hmax lm b hlm.le hb) hd
    linarith

/-- AKMM, (12.5), p. 336: dividing the two first-order conditions, `g₂/g₁ = w/A`
(`v′ ≠ 0`, `A ≠ 0`). -/
theorem eq_12_5 {u' v' g₁ g₂ w A : ℝ} (hv : v' ≠ 0) (hA : A ≠ 0) (h₁ : u' * g₁ * w = v')
    (h₂ : u' * g₂ * A = v') : g₂ / g₁ = w / A := by
  have hg₁ : g₁ ≠ 0 := by rintro rfl; simp at h₁; exact hv h₁.symm
  rw [div_eq_div_iff hg₁ hA]
  have : u' ≠ 0 := by rintro rfl; simp at h₁; exact hv h₁.symm
  apply mul_left_cancel₀ this
  linear_combination h₂ - h₁

/-- The CES aggregator `g(c_m, c_h) = [θc_m^η + (1 − θ)c_h^η]^{1/η}` (AKMM, p. 336). -/
noncomputable def cesG (θ η cm ch : ℝ) : ℝ := (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η)

/-- AKMM, p. 336: the partial derivatives of the CES aggregator,
`g₁ = θc_m^{η−1}X^{1/η−1}` and `g₂ = (1 − θ)c_h^{η−1}X^{1/η−1}` (`X = θc_m^η + (1 − θ)c_h^η`),
and their ratio `g₂/g₁ = ((1 − θ)/θ)(c_h/c_m)^{η−1}`. -/
theorem hp_ces_partials {θ η cm ch : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη : η ≠ 0)
    (hcm : 0 < cm) (hch : 0 < ch) :
    HasDerivAt (fun x => cesG θ η x ch)
      (θ * cm ^ (η - 1) * (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η - 1)) cm ∧
    HasDerivAt (fun y => cesG θ η cm y)
      ((1 - θ) * ch ^ (η - 1) * (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η - 1)) ch ∧
    (1 - θ) * ch ^ (η - 1) * (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η - 1) /
        (θ * cm ^ (η - 1) * (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η - 1)) =
      (1 - θ) / θ * (ch / cm) ^ (η - 1) := by
  have hX : 0 < θ * cm ^ η + (1 - θ) * ch ^ η := by
    have : 0 < 1 - θ := by linarith
    positivity
  refine ⟨?_, ?_, ?_⟩
  · have hin : HasDerivAt (fun x => θ * x ^ η + (1 - θ) * ch ^ η) (θ * (η * cm ^ (η - 1))) cm :=
      ((Real.hasDerivAt_rpow_const (Or.inl hcm.ne')).const_mul θ).add_const _
    have := (Real.hasDerivAt_rpow_const (p := 1 / η) (Or.inl hX.ne')).comp cm hin
    refine this.congr_deriv ?_
    field_simp
  · have hin : HasDerivAt (fun y => θ * cm ^ η + (1 - θ) * y ^ η)
        ((1 - θ) * (η * ch ^ (η - 1))) ch :=
      ((Real.hasDerivAt_rpow_const (Or.inl hch.ne')).const_mul (1 - θ)).const_add _
    have := (Real.hasDerivAt_rpow_const (p := 1 / η) (Or.inl hX.ne')).comp ch hin
    refine this.congr_deriv ?_
    field_simp
  · have hXp : 0 < (θ * cm ^ η + (1 - θ) * ch ^ η) ^ (1 / η - 1) := Real.rpow_pos_of_pos hX _
    have hcmp : 0 < cm ^ (η - 1) := Real.rpow_pos_of_pos hcm _
    rw [Real.div_rpow hch.le hcm.le]
    field_simp

/-- AKMM, (12.6), p. 336, **corrected**: with `I = 0` (`c_m = wℓ_m`, `c_h = Aℓ_h`),
`((1 − θ)/θ)(Aℓ_h/(wℓ_m))^{η−1} = w/A` implies
`ℓ_h/ℓ_m = ((1 − θ)/θ)^{1/(1−η)}(w/A)^{η/(η−1)}`. -/
theorem eq_12_6 {θ η w A lm lh : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη : η ≠ 1) (hw : 0 < w)
    (hA : 0 < A) (hlm : 0 < lm) (hlh : 0 < lh)
    (h : (1 - θ) / θ * (A * lh / (w * lm)) ^ (η - 1) = w / A) :
    lh / lm = ((1 - θ) / θ) ^ (1 / (1 - η)) * (w / A) ^ (η / (η - 1)) := by
  have hθ' : 0 < 1 - θ := by linarith
  have hη1 : η - 1 ≠ 0 := sub_ne_zero.2 hη
  have hx : 0 < A * lh / (w * lm) := by positivity
  have hk : 0 < (1 - θ) / θ := by positivity
  have hx' : (A * lh / (w * lm)) ^ (η - 1) = (θ / (1 - θ)) * (w / A) := by
    rw [← h]; field_simp
  have hxe : A * lh / (w * lm) = ((θ / (1 - θ)) * (w / A)) ^ (1 / (η - 1)) := by
    rw [← hx', ← Real.rpow_mul hx.le, mul_one_div_cancel hη1, Real.rpow_one]
  have hratio : lh / lm = w / A * (A * lh / (w * lm)) := by field_simp
  rw [hratio, hxe, Real.mul_rpow (by positivity) (by positivity)]
  have h1 : (θ / (1 - θ)) ^ (1 / (η - 1)) = ((1 - θ) / θ) ^ (1 / (1 - η)) := by
    rw [show θ / (1 - θ) = ((1 - θ) / θ)⁻¹ by field_simp, Real.inv_rpow hk.le,
      ← Real.rpow_neg hk.le]
    congr 1
    field_simp
    ring
  have h2 : w / A * (w / A) ^ (1 / (η - 1)) = (w / A) ^ (η / (η - 1)) := by
    have hwA : 0 < w / A := by positivity
    rw [show η / (η - 1) = 1 + 1 / (η - 1) by field_simp; ring, Real.rpow_add hwA,
      Real.rpow_one]
  rw [h1, ← h2]
  ring

/-- AKMM, (12.6), p. 336: **the printed constant is wrong**. The printed
`((1 − θ)/θ)^{1/(η−1)}(w/A)^{η/(η−1)}` equals the correct value of `eq_12_6` only when
`θ = 1/2` (for `0 < θ < 1`, `η ≠ 1`, `w, A > 0`). -/
theorem eq_12_6_printed_false {θ η w A : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη : η ≠ 1)
    (hw : 0 < w) (hA : 0 < A) :
    ((1 - θ) / θ) ^ (1 / (η - 1)) * (w / A) ^ (η / (η - 1)) =
        ((1 - θ) / θ) ^ (1 / (1 - η)) * (w / A) ^ (η / (η - 1)) ↔ θ = 1 / 2 := by
  have hk : 0 < (1 - θ) / θ := div_pos (by linarith) hθ0
  have hz : 0 < (w / A) ^ (η / (η - 1)) := Real.rpow_pos_of_pos (by positivity) _
  rw [mul_left_inj' hz.ne']
  have hη1 : η - 1 ≠ 0 := sub_ne_zero.2 hη
  constructor
  · intro h
    have hl := congrArg Real.log h
    rw [Real.log_rpow hk, Real.log_rpow hk] at hl
    have e : 1 / (1 - η) = -(1 / (η - 1)) := by
      rw [show 1 - η = -(η - 1) by ring, div_neg]
    rw [e] at hl
    have : 1 / (η - 1) * Real.log ((1 - θ) / θ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' (one_div_ne_zero hη1)
    · rcases Real.log_eq_zero.1 h' with h'' | h'' | h''
      · linarith [hk]
      · field_simp at h''; linarith
      · linarith [hk]
  · intro h
    subst h
    norm_num

/-- AKMM, p. 336: for `0 < η < 1` the exponent `η/(η − 1)` is negative, so `ℓ_h/ℓ_m` in (12.6)
is strictly decreasing in `w/A`. -/
theorem hp_ratio_decreasing {θ η x y : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη0 : 0 < η)
    (hη1 : η < 1) (hx : 0 < x) (hxy : x < y) :
    η / (η - 1) < 0 ∧ ((1 - θ) / θ) ^ (1 / (1 - η)) * y ^ (η / (η - 1)) <
      ((1 - θ) / θ) ^ (1 / (1 - η)) * x ^ (η / (η - 1)) := by
  have he : η / (η - 1) < 0 := div_neg_of_pos_of_neg hη0 (by linarith)
  refine ⟨he, mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hx hxy he) ?_⟩
  exact Real.rpow_pos_of_pos (div_pos (by linarith) hθ0) _

/-! ### Household labour supply -/

/-- AKMM, p. 338, **the household's first-order conditions**: at a maximiser with
`ℓ_f, ℓ_m > 0` of `u(w_fℓ_f + w_mℓ_m + I) − v(ℓ_f) − v(ℓ_m)`,
`u′(c)w_f = v′(ℓ_f)` and `u′(c)w_m = v′(ℓ_m)`. -/
theorem hh_focs {u v : ℝ → ℝ} {wf wm I lf lm u' vf vm : ℝ} (hlf : 0 < lf) (hlm : 0 < lm)
    (hu : HasDerivAt u u' (wf * lf + wm * lm + I)) (hvf : HasDerivAt v vf lf)
    (hvm : HasDerivAt v vm lm)
    (hmax : ∀ a b, 0 ≤ a → 0 ≤ b →
      u (wf * a + wm * b + I) - v a - v b ≤ u (wf * lf + wm * lm + I) - v lf - v lm) :
    u' * wf = vf ∧ u' * wm = vm := by
  constructor
  · have hd : HasDerivAt (fun a => u (wf * a + wm * lm + I) - v a - v lm) (u' * wf - vf) lf := by
      have h1 := hu.comp lf ((((hasDerivAt_id lf).const_mul wf).add_const (wm * lm)).add_const I)
      exact ((h1.sub hvf).sub_const (v lm)).congr_deriv (by simp)
    have := ext_foc_of_max hlf (fun a ha => hmax a lm ha hlm.le) hd
    linarith
  · have hd : HasDerivAt (fun b => u (wf * lf + wm * b + I) - v lf - v b) (u' * wm - vm) lm := by
      have h1 := hu.comp lm ((((hasDerivAt_id lm).const_mul wm).const_add (wf * lf)).add_const I)
      exact ((h1.sub_const (v lf)).sub hvm).congr_deriv (by simp)
    have := ext_foc_of_max hlm (fun b hb => hmax lf b hlf.le hb) hd
    linarith

/-- AKMM, p. 338: dividing the first-order conditions, `v′(ℓ_f)/v′(ℓ_m) = w_f/w_m`; with
`v′(ℓ) = ψℓ^{1/γ}`, **relative hours** are `ℓ_f/ℓ_m = (w_f/w_m)^γ`. -/
theorem hh_relative_hours {ψ γ wf wm lf lm lam : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hwf : 0 < wf)
    (hwm : 0 < wm) (hlf : 0 < lf) (hlm : 0 < lm) (hlam : 0 < lam)
    (hf : lam * wf = ψ * lf ^ (1 / γ)) (hm : lam * wm = ψ * lm ^ (1 / γ)) :
    ψ * lf ^ (1 / γ) / (ψ * lm ^ (1 / γ)) = wf / wm ∧ lf / lm = (wf / wm) ^ γ := by
  have h1 : ψ * lf ^ (1 / γ) / (ψ * lm ^ (1 / γ)) = wf / wm := by
    rw [← hf, ← hm]; field_simp
  refine ⟨h1, ?_⟩
  have h2 : (lf / lm) ^ (1 / γ) = wf / wm := by
    rw [Real.div_rpow hlf.le hlm.le, ← h1]; field_simp
  rw [← h2, ← Real.rpow_mul (by positivity), one_div_mul_cancel hγ.ne', Real.rpow_one]

/-- AKMM, p. 338: **the cross-wage effect is negative**. Along `w_m(s) = w_me^s` with both
members' conditions (12.1)-type holding near `0` (`u = c^{1−σ}/(1 − σ)`, `σ > 0`), the
elasticity of `ℓ_f` with respect to `w_m` is `−γσ(1 + γ)E_m/(c + γσ(E_f + E_m)) < 0`,
`E_j = w_jℓ_j`, `c = E_f + E_m + I`. -/
theorem hh_cross_wage {ψ γ σ wf wm I lf' lm' : ℝ} {lf lm : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hσ : 0 < σ) (hwf : 0 < wf) (hwm : 0 < wm) (hlf : 0 < lf 0) (hlm : 0 < lm 0)
    (hc : 0 < wf * lf 0 + wm * lm 0 + I) (hdf : HasDerivAt lf lf' 0) (hdm : HasDerivAt lm lm' 0)
    (hff : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * lf s ^ (1 / γ) /
      (wf * lf s + (wm * Real.exp s * lm s + I)) ^ (-σ) = wf)
    (hfm : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * lm s ^ (1 / γ) /
      (wm * Real.exp s * lm s + (wf * lf s + I)) ^ (-σ) = wm * Real.exp s) :
    HasDerivAt (fun s => Real.log (lf s)) (-(γ * σ * (1 + γ) * (wm * lm 0)) /
      (wf * lf 0 + wm * lm 0 + I + γ * σ * (wf * lf 0 + wm * lm 0))) 0 ∧
    -(γ * σ * (1 + γ) * (wm * lm 0)) /
      (wf * lf 0 + wm * lm 0 + I + γ * σ * (wf * lf 0 + wm * lm 0)) < 0 := by
  have hEm : HasDerivAt (fun s => wm * Real.exp s * lm s + I) (wm * lm 0 + wm * lm') 0 := by
    have := ((st_exp_path wm).mul hdm).add_const I
    refine this.congr_deriv ?_
    rw [Real.exp_zero, mul_one]
  have hEf : HasDerivAt (fun s => wf * lf s + I) (wf * lf') 0 :=
    (hdf.const_mul wf).add_const I
  have hc1 : 0 < wf * lf 0 + (wm * Real.exp 0 * lm 0 + I) := by
    rw [Real.exp_zero, mul_one]; linarith
  have hc2 : 0 < wm * Real.exp 0 * lm 0 + (wf * lf 0 + I) := by
    rw [Real.exp_zero, mul_one]; linarith
  have hwm0 : 0 < wm * Real.exp 0 := by rw [Real.exp_zero, mul_one]; exact hwm
  have kf := st_path_poly (w := fun _ => wf) (w' := 0) hψ hγ hwf hlf hc1
    (hasDerivAt_const _ _) hEm hdf hff
  have km := st_path_poly hψ hγ hwm0 hlm hc2 (st_exp_path wm) hEf hdm hfm
  simp only [Real.exp_zero, mul_one, zero_mul, zero_add, mul_zero] at kf km
  set c := wf * lf 0 + wm * lm 0 + I with hcdef
  have hf : c * lf' + γ * σ * lf 0 * (wf * lf' + (wm * lm 0 + wm * lm')) = 0 := by
    have h : wf * (c * lf' + γ * σ * lf 0 * (wf * lf' + (wm * lm 0 + wm * lm'))) = 0 := by
      rw [hcdef]; linear_combination kf
    exact (mul_eq_zero.1 h).resolve_left hwf.ne'
  have hm : c * lm' + γ * σ * lm 0 * (wm * lm 0 + wm * lm' + wf * lf') = γ * lm 0 * c := by
    have h : wm * (c * lm' + γ * σ * lm 0 * (wm * lm 0 + wm * lm' + wf * lf') -
        γ * lm 0 * c) = 0 := by
      rw [hcdef]; linear_combination km
    linarith [(mul_eq_zero.1 h).resolve_left hwm.ne']
  have hD : 0 < c + γ * σ * (wf * lf 0 + wm * lm 0) := by
    have : 0 ≤ γ * σ * (wf * lf 0 + wm * lm 0) := by positivity
    linarith
  have hgoal : c * (lf' * (c + γ * σ * (wf * lf 0 + wm * lm 0)) +
      γ * σ * (1 + γ) * (wm * lm 0) * lf 0) = 0 := by
    linear_combination (c + γ * σ * wm * lm 0) * hf - (γ * σ * wm * lf 0) * hm
  have hl : lf' = -(γ * σ * (1 + γ) * (wm * lm 0) * lf 0) /
      (c + γ * σ * (wf * lf 0 + wm * lm 0)) := by
    rw [eq_div_iff hD.ne']
    linarith [(mul_eq_zero.1 hgoal).resolve_left hc.ne']
  refine ⟨(hdf.log hlf.ne').congr_deriv ?_, div_neg_of_neg_of_pos ?_ hD⟩
  · rw [hl]; field_simp
  · have : 0 < γ * σ * (1 + γ) * (wm * lm 0) := by positivity
    linarith

/-- AKMM, p. 333 (the income effect): the solution of (12.1) is strictly decreasing in
non-labour income: if `ℓ₁` solves (12.1) at `I₁` and `ℓ₂` at `I₂ > I₁`, then `ℓ₂ < ℓ₁`. -/
theorem st_income_decreasing {ψ γ σ w I₁ I₂ l₁ l₂ : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 < σ)
    (hw : 0 < w) (hl₁ : 0 < l₁) (hc₁ : 0 < w * l₁ + I₁)
    (hc₂ : 0 < w * l₂ + I₂) (hI : I₁ < I₂)
    (h₁ : ψ * l₁ ^ (1 / γ) / (w * l₁ + I₁) ^ (-σ) = w)
    (h₂ : ψ * l₂ ^ (1 / γ) / (w * l₂ + I₂) ^ (-σ) = w) : l₂ < l₁ := by
  rw [st_foc_form hc₁] at h₁
  rw [st_foc_form hc₂] at h₂
  by_contra hle
  have hle' : l₁ ≤ l₂ := not_lt.1 hle
  have a1 : l₁ ^ (1 / γ) ≤ l₂ ^ (1 / γ) := Real.rpow_le_rpow hl₁.le hle' (by positivity)
  have a2 : (w * l₁ + I₁) ^ σ < (w * l₂ + I₂) ^ σ :=
    Real.rpow_lt_rpow hc₁.le (by nlinarith) hσ
  have a3 : 0 < l₁ ^ (1 / γ) := Real.rpow_pos_of_pos hl₁ _
  have a4 : 0 < (w * l₂ + I₂) ^ σ := Real.rpow_pos_of_pos hc₂ _
  have : l₁ ^ (1 / γ) * (w * l₁ + I₁) ^ σ < l₂ ^ (1 / γ) * (w * l₂ + I₂) ^ σ :=
    calc l₁ ^ (1 / γ) * (w * l₁ + I₁) ^ σ < l₁ ^ (1 / γ) * (w * l₂ + I₂) ^ σ :=
          mul_lt_mul_of_pos_left a2 a3
      _ ≤ l₂ ^ (1 / γ) * (w * l₂ + I₂) ^ σ := mul_le_mul_of_nonneg_right a1 a4.le
  have := mul_lt_mul_of_pos_left this hψ
  rw [← mul_assoc, ← mul_assoc] at this
  linarith

/-- AKMM, p. 338, **the added-worker effect**: in the female member's condition the male's
earnings `w_mℓ_m` act as non-labour income, so an exogenous fall in `ℓ_m` raises `ℓ_f`. -/
theorem hh_added_worker {ψ γ σ wf wm I lm₁ lm₂ lf₁ lf₂ : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hσ : 0 < σ) (hwf : 0 < wf) (hwm : 0 < wm) (hlm : lm₂ < lm₁) (hf₂ : 0 < lf₂)
    (hc₁ : 0 < wf * lf₁ + (wm * lm₁ + I)) (hc₂ : 0 < wf * lf₂ + (wm * lm₂ + I))
    (h₁ : ψ * lf₁ ^ (1 / γ) / (wf * lf₁ + (wm * lm₁ + I)) ^ (-σ) = wf)
    (h₂ : ψ * lf₂ ^ (1 / γ) / (wf * lf₂ + (wm * lm₂ + I)) ^ (-σ) = wf) : lf₁ < lf₂ :=
  st_income_decreasing hψ hγ hσ hwf hf₂ hc₂ hc₁ (by nlinarith) h₂ h₁

/-! ### Leisure in the utility function -/

/-- AKMM, p. 339: in the benchmark the elasticity of disutility `ℓv′(ℓ)/v(ℓ) = 1 + 1/γ` is
constant (`ℓ > 0`). -/
theorem lt_benchmark_elasticity {ψ γ l : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hl : 0 < l) :
    l * (ψ * l ^ (1 / γ)) / disutil ψ γ l = 1 + 1 / γ := by
  unfold disutil
  have h : l * l ^ (1 / γ) = l ^ (1 + 1 / γ) := by
    rw [Real.rpow_add hl, Real.rpow_one]
  have hp : 0 < l ^ (1 + 1 / γ) := Real.rpow_pos_of_pos hl _
  have hg : 0 < 1 + 1 / γ := by positivity
  rw [show l * (ψ * l ^ (1 / γ)) = ψ * (l * l ^ (1 / γ)) by ring, h]
  field_simp

/-- AKMM, p. 339: `ṽ(l) = l^{1−1/γ}/(1 − 1/γ)` has `ṽ′(l) = l^{−1/γ}` (`l > 0`, `γ ≠ 1`). -/
theorem lt_vtilde_hasDerivAt {γ l : ℝ} (hγ : γ ≠ 1) (hγ0 : 0 < γ) (hl : 0 < l) :
    HasDerivAt (fun x => x ^ (1 - 1 / γ) / (1 - 1 / γ)) (l ^ (-(1 / γ))) l := by
  have hk : 1 - 1 / γ ≠ 0 := by
    intro h
    have : 1 / γ = 1 := by linarith
    exact hγ (by field_simp at this; linarith)
  have := (Real.hasDerivAt_rpow_const (p := 1 - 1 / γ) (Or.inl hl.ne')).div_const (1 - 1 / γ)
  refine this.congr_deriv ?_
  rw [show 1 - 1 / γ - 1 = -(1 / γ) by ring]
  field_simp

/-- AKMM, p. 339: **with utility of leisure, `ℓ = 0` can be optimal**. For
`Ũ = u(wℓ + I) + ṽ(ℓ̄ − ℓ)` with `I > 0`, if `wI^{−σ} ≤ ℓ̄^{−1/γ}` (non-labour income high
enough) then `ℓ = 0` maximises `Ũ` over `[0, ℓ̄)`. -/
theorem lt_corner {γ σ w I lbar : ℝ} (hγ : γ ≠ 1) (hγ0 : 0 < γ) (hσ : 0 < σ) (hw : 0 < w)
    (hI : 0 < I) (hlbar : 0 < lbar) (hhigh : w * I ^ (-σ) ≤ lbar ^ (-(1 / γ))) :
    ∀ l, 0 ≤ l → l < lbar →
      crraU σ (w * l + I) + (lbar - l) ^ (1 - 1 / γ) / (1 - 1 / γ) ≤
        crraU σ (w * 0 + I) + (lbar - 0) ^ (1 - 1 / γ) / (1 - 1 / γ) := by
  set f : ℝ → ℝ := fun l => crraU σ (w * l + I) + (lbar - l) ^ (1 - 1 / γ) / (1 - 1 / γ)
  have hder : ∀ l, 0 ≤ l → l < lbar →
      HasDerivAt f (w * (w * l + I) ^ (-σ) - (lbar - l) ^ (-(1 / γ))) l := by
    intro l hl0 hl1
    have hc : 0 < w * l + I := by positivity
    have h1 := (st_crraU_hasDerivAt (σ := σ) hc).comp l
      (((hasDerivAt_id l).const_mul w).add_const I)
    have h2 := (lt_vtilde_hasDerivAt hγ hγ0 (by linarith : 0 < lbar - l)).comp l
      ((hasDerivAt_id l).const_sub lbar)
    exact (h1.add h2).congr_deriv (by simp; ring)
  have hanti : AntitoneOn f (Set.Ico 0 lbar) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico 0 lbar)
    · intro x hx
      exact (hder x hx.1 hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      exact (hder x hx.1.le hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hder x hx.1.le hx.2).deriv]
      have a1 : (w * x + I) ^ (-σ) ≤ I ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hI (by nlinarith [hx.1]) (by linarith)
      have a2 : lbar ^ (-(1 / γ)) ≤ (lbar - x) ^ (-(1 / γ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [hx.2]) (by linarith [hx.1])
          (by have : 0 < 1 / γ := by positivity
              linarith)
      have : w * (w * x + I) ^ (-σ) ≤ w * I ^ (-σ) := mul_le_mul_of_nonneg_left a1 hw.le
      linarith
  intro l hl0 hl1
  exact hanti ⟨le_rfl, hlbar⟩ ⟨hl0, hl1⟩ hl0

/-- AKMM, p. 339: the elasticity of `ṽ(ℓ̄ − ℓ)` with respect to time worked,
`−ℓṽ′(ℓ̄ − ℓ)/ṽ(ℓ̄ − ℓ)`, equals `−(1 − 1/γ)ℓ/(ℓ̄ − ℓ)` (`ℓ < ℓ̄`, `γ ≠ 1`); it is not
constant. -/
theorem lt_elasticity {γ l lbar : ℝ} (hγ : γ ≠ 1) (hγ0 : 0 < γ) (hl : l < lbar) :
    -l * (lbar - l) ^ (-(1 / γ)) / ((lbar - l) ^ (1 - 1 / γ) / (1 - 1 / γ)) =
      -(1 - 1 / γ) * l / (lbar - l) := by
  have hx : 0 < lbar - l := by linarith
  have hk : 1 - 1 / γ ≠ 0 := by
    intro h
    have : 1 / γ = 1 := by linarith
    exact hγ (by field_simp at this; linarith)
  have h : (lbar - l) ^ (1 - 1 / γ) = (lbar - l) * (lbar - l) ^ (-(1 / γ)) := by
    rw [show 1 - 1 / γ = 1 + -(1 / γ) by ring, Real.rpow_add hx, Real.rpow_one]
  have hp : 0 < (lbar - l) ^ (-(1 / γ)) := Real.rpow_pos_of_pos hx _
  rw [h]
  field_simp

/-- AKMM, p. 339, **corrected**: "This value approaches minus infinity as `ℓ` approaches `ℓ̄`".
As `ℓ → ℓ̄⁻`, `−(1 − 1/γ)ℓ/(ℓ̄ − ℓ) → −∞` when `γ > 1`, but `→ +∞` when `γ < 1` (then
`ṽ < 0`); in both cases it is unbounded. -/
theorem lt_elasticity_limits {γ lbar : ℝ} (hlbar : 0 < lbar) :
    (1 < γ → Tendsto (fun l => -(1 - 1 / γ) * l / (lbar - l)) (𝓝[<] lbar) atBot) ∧
      (0 < γ → γ < 1 → Tendsto (fun l => -(1 - 1 / γ) * l / (lbar - l)) (𝓝[<] lbar) atTop) := by
  have hbase : Tendsto (fun l => l * (lbar - l)⁻¹) (𝓝[<] lbar) atTop := by
    have h1 : Tendsto (fun l : ℝ => l) (𝓝[<] lbar) (𝓝 lbar) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h2 : Tendsto (fun l : ℝ => lbar - l) (𝓝[<] lbar) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun l : ℝ => lbar - l) (𝓝 lbar) (𝓝 (lbar - lbar)) :=
          tendsto_const_nhds.sub tendsto_id
        rw [sub_self] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      · filter_upwards [self_mem_nhdsWithin] with l hl
        exact sub_pos.2 (Set.mem_Iio.1 hl)
    exact h1.pos_mul_atTop hlbar (tendsto_inv_nhdsGT_zero.comp h2)
  have heq : ∀ l, -(1 - 1 / γ) * l / (lbar - l) = -(1 - 1 / γ) * (l * (lbar - l)⁻¹) :=
    fun l => by rw [div_eq_mul_inv]; ring
  constructor
  · intro hγ
    have hk : -(1 - 1 / γ) < 0 := by
      have : 1 / γ < 1 := by rw [div_lt_one (by linarith)]; exact hγ
      linarith
    simp only [heq]
    exact hbase.const_mul_atTop_of_neg hk
  · intro hγ0 hγ1
    have hk : 0 < -(1 - 1 / γ) := by
      have : 1 < 1 / γ := by rw [lt_div_iff₀ hγ0]; linarith
      linarith
    simp only [heq]
    exact hbase.const_mul_atTop hk

/-! ### A two-period model -/

/-- AKMM, p. 341, **the Frisch elasticity in two periods**: with `β = 1/(1 + r)`, the
first-order conditions `c₁^{−σ} = λ = c₂^{−σ}`, `ψℓ_t^{1/γ} = λw_t` give `c₁ = c₂`,
`(ℓ₁/ℓ₂)^{1/γ} = w₁/w₂` and `log ℓ₁ − log ℓ₂ = γ(log w₁ − log w₂)`. -/
theorem tp_frisch {ψ γ σ lam c₁ c₂ l₁ l₂ w₁ w₂ : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : σ ≠ 0)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (h₁ : c₁ ^ (-σ) = lam) (h₂ : c₂ ^ (-σ) = lam) (h₃ : ψ * l₁ ^ (1 / γ) = lam * w₁)
    (h₄ : ψ * l₂ ^ (1 / γ) = lam * w₂) :
    c₁ = c₂ ∧ (l₁ / l₂) ^ (1 / γ) = w₁ / w₂ ∧
      Real.log l₁ - Real.log l₂ = γ * (Real.log w₁ - Real.log w₂) := by
  have hlam : 0 < lam := by rw [← h₁]; exact Real.rpow_pos_of_pos hc₁ _
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg Real.log (h₁.trans h₂.symm)
    rw [Real.log_rpow hc₁, Real.log_rpow hc₂] at this
    have hl : Real.log c₁ = Real.log c₂ := by
      have := mul_left_cancel₀ (neg_ne_zero.2 hσ) this
      exact this
    exact Real.log_injOn_pos hc₁ hc₂ hl
  · rw [Real.div_rpow hl₁.le hl₂.le]
    have e₁ : l₁ ^ (1 / γ) = lam * w₁ / ψ := by rw [← h₃]; field_simp
    have e₂ : l₂ ^ (1 / γ) = lam * w₂ / ψ := by rw [← h₄]; field_simp
    rw [e₁, e₂]; field_simp
  · have e₁ := congrArg Real.log h₃
    have e₂ := congrArg Real.log h₄
    rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl₁ _).ne', Real.log_rpow hl₁,
      Real.log_mul hlam.ne' hw₁.ne'] at e₁
    rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl₂ _).ne', Real.log_rpow hl₂,
      Real.log_mul hlam.ne' hw₂.ne'] at e₂
    have : 1 / γ * (Real.log l₁ - Real.log l₂) = Real.log w₁ - Real.log w₂ := by linarith
    rw [← this]
    field_simp

/-- AKMM, footnote 8, p. 341, **corrected**: from `c_t^{−σ} = λ` and `ψℓ_t^{1/γ} = λw_t`,
`log ℓ_t = −γ log ψ + γ log w_t − γσ log c_t`. -/
theorem footnote_8 {ψ γ σ lam c l w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hc : 0 < c) (hl : 0 < l)
    (hw : 0 < w) (h₁ : c ^ (-σ) = lam) (h₂ : ψ * l ^ (1 / γ) = lam * w) :
    Real.log l = -γ * Real.log ψ + γ * Real.log w - γ * σ * Real.log c := by
  have hlam : 0 < lam := by rw [← h₁]; exact Real.rpow_pos_of_pos hc _
  have e := congrArg Real.log h₂
  rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl _).ne', Real.log_rpow hl,
    Real.log_mul hlam.ne' hw.ne', ← h₁, Real.log_rpow hc] at e
  have : Real.log l = γ * (1 / γ * Real.log l) := by field_simp
  rw [this]
  have : 1 / γ * Real.log l = -σ * Real.log c + Real.log w - Real.log ψ := by linarith
  rw [this]
  ring

/-- AKMM, footnote 8, p. 341: **the printed equation is false**. The printed
`log ℓ_t = γ/ψ + γ log w_t + γ(1 − σ) log c_t` fails at `ψ = γ = σ = w = 1`, `c = e`,
`λ = e^{−1}`, `ℓ = e^{−1}`, where both first-order conditions hold. -/
theorem footnote_8_printed_false :
    Real.exp 1 ^ (-(1 : ℝ)) = Real.exp (-1) ∧
      1 * Real.exp (-1) ^ (1 / (1 : ℝ)) = Real.exp (-1) * 1 ∧
      Real.log (Real.exp (-1)) ≠
        1 / 1 + 1 * Real.log 1 + 1 * (1 - 1) * Real.log (Real.exp 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.rpow_neg_one, Real.exp_neg]
  · simp
  · rw [Real.log_exp]; norm_num

end AKMM.LaborSupply

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dynamic labour supply elasticities

AKMM, §12.4.1, pp. 341–346.

* **Two-stage budgeting** (12.9)–(12.11): with `I_t = ra_t + T − (a_{t+1} − a_t)` the period
  budget is `c_t = (1 − τ)w_tℓ_t + I_t` (12.10), equivalently `c_t + (1 − τ)w_t(1 − ℓ_t) = Y_t`
  with full income (12.11) (`eq_12_9_to_12_11`). In the deterministic finite-horizon problem
  (12.7), an optimal plan solves, at every `t` and given `a_{t+1}`, the static problem of §12.3
  (`dyn_two_stage`), and its interior hours satisfy (12.13) (`eq_12_13`).
* **Marshallian and Hicksian elasticities**: (12.12) (`eq_12_12`), (12.14) (`eq_12_14`), their
  combination (12.15) (`eq_12_15`), and along paths of the net wage (`eq_12_15_path`); the
  Slutsky equation (12.16) and (12.17) (`eq_12_16`, `eq_12_17`). The compensation must be
  `dI/dw = −(1 − τ)ℓ`; with the printed `+(1 − τ)ℓ` the response is
  `(1 − 2σ(1 − s_I))/(1/γ + σ(1 − s_I))` (`dyn_compensation_sign`).
* **The Frisch elasticity** (12.18)–(12.21) for a general `U`, with `λ` fixed
  (`eq_12_21`), and its values: separable (12.8) `γ` (`dyn_frisch_separable`, also through the
  general theorem along an explicit path, `dyn_frisch_separable_path`), GHH (12.22) `γ`
  (`dyn_frisch_ghh`) with no income effect (`dyn_ghh_no_income_effect`), Cobb–Douglas
  (`dyn_frisch_cd`), power leisure (`dyn_frisch_leisure`), decreasing in hours
  (`dyn_frisch_decreasing_hours`).
* **The ordering** `ε^F ≥ ε^H ≥ ε^M` for (12.8), with equality iff `σ = 0`, the limits as
  `σ → 0`; the printed "equality holding when `σ → ∞`" is false (`dyn_ordering`,
  `dyn_ordering_sigma_zero`, `dyn_ordering_sigma_infty`).
* **(12.23)**: with the Euler equation and (12.13) at two dates,
  `log(ℓ_{t+1}/ℓ_t) = γ log(w_{t+1}/w_t) + γ log((1 − τ_{t+1})/(1 − τ_t)) − γ log(βR)`, so the
  elasticity of relative hours to relative wages (and net-of-tax rates) is `γ` (`eq_12_23`).

Departure: (12.7) is stochastic; `dyn_two_stage` treats the deterministic problem.
-/

namespace AKMM.LaborSupply

open Filter Topology

/-! ### Two-stage budgeting -/

/-- AKMM, (12.9)–(12.11), p. 342: with `R = 1 + r` and `I = ra + T − (a′ − a)`, the period
budget `c + a′ = Ra + (1 − τ)wℓ + T` is `c = (1 − τ)wℓ + I` (12.10), and with full income
`Y = (1 − τ)w + Ra + T − a′` (12.11) it is `c + (1 − τ)w(1 − ℓ) = Y`. -/
theorem eq_12_9_to_12_11 (r τ w T a a' c l : ℝ) :
    (c + a' = (1 + r) * a + (1 - τ) * w * l + T ↔
      c = (1 - τ) * w * l + (r * a + T - (a' - a))) ∧
    (c + a' = (1 + r) * a + (1 - τ) * w * l + T ↔
      c + (1 - τ) * w * (1 - l) = (1 - τ) * w + (1 + r) * a + T - a') := by
  constructor <;> constructor <;> intro h <;> linarith

/-- A feasible plan of the deterministic version of (12.7) over dates `0, …, N`: budgets,
borrowing limit `a_{t+1} ≥ −ā`, `c ≥ 0`, `0 ≤ ℓ ≤ 1`, and `a_{N+1} ≥ 0`. -/
def DynFeasible (R τ T a0 abar : ℝ) (w : ℕ → ℝ) (N : ℕ) (c l a : ℕ → ℝ) : Prop :=
  a 0 = a0 ∧ 0 ≤ a (N + 1) ∧ ∀ t ≤ N, c t + a (t + 1) = R * a t + (1 - τ) * w t * l t + T ∧
    -abar ≤ a (t + 1) ∧ 0 ≤ c t ∧ 0 ≤ l t ∧ l t ≤ 1

/-- AKMM, pp. 342–343, **two-stage budgeting**. If `(c, ℓ, a)` maximises `Σ_{t≤N} β^tU(c_t, ℓ_t)`
over feasible plans (`β > 0`), then at every `t ≤ N`, given the plan's `a_t, a_{t+1}` and so its
`I_t = (R − 1)a_t + T − (a_{t+1} − a_t)`, `(c_t, ℓ_t)` maximises `U(c, ℓ)` subject to
`c = (1 − τ)w_tℓ + I_t`, `c ≥ 0`, `0 ≤ ℓ ≤ 1`: the static problem of §12.3. -/
theorem dyn_two_stage {R τ T a0 abar β : ℝ} {w : ℕ → ℝ} {N : ℕ} {U : ℝ → ℝ → ℝ}
    {c l a : ℕ → ℝ} (hβ : 0 < β) (hfeas : DynFeasible R τ T a0 abar w N c l a)
    (hopt : ∀ c' l' a', DynFeasible R τ T a0 abar w N c' l' a' →
      ∑ t ∈ Finset.range (N + 1), β ^ t * U (c' t) (l' t) ≤
        ∑ t ∈ Finset.range (N + 1), β ^ t * U (c t) (l t))
    {t : ℕ} (ht : t ≤ N) {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hbud : x = (1 - τ) * w t * y + ((R - 1) * a t + T - (a (t + 1) - a t))) :
    U x y ≤ U (c t) (l t) := by
  obtain ⟨ha0, haN, hf⟩ := hfeas
  have hfeas' : DynFeasible R τ T a0 abar w N (Function.update c t x) (Function.update l t y) a :=
    by
    refine ⟨ha0, haN, fun s hs => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hf s hs
    by_cases hst : s = t
    · subst hst
      simp only [Function.update_self]
      exact ⟨by rw [hbud]; ring, h2, hx, hy0, hy1⟩
    · simp only [Function.update_of_ne hst]
      exact ⟨h1, h2, h3, h4, h5⟩
  have hle := hopt _ _ _ hfeas'
  have hmem : t ∈ Finset.range (N + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le ht)
  have hsplit : ∀ f g : ℕ → ℝ, (∀ s, s ≠ t → f s = g s) →
      ∑ s ∈ Finset.range (N + 1), f s - ∑ s ∈ Finset.range (N + 1), g s = f t - g t := by
    intro f g hfg
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem,
      Finset.sum_congr rfl (fun s hs => hfg s (Finset.ne_of_mem_erase hs))]
    ring
  have hd := hsplit (fun s => β ^ s * U (Function.update c t x s) (Function.update l t y s))
    (fun s => β ^ s * U (c s) (l s)) (fun s hs => by
      simp only [Function.update_of_ne hs])
  simp only [Function.update_self] at hd
  have hβt : 0 < β ^ t := pow_pos hβ t
  have : β ^ t * U x y ≤ β ^ t * U (c t) (l t) := by linarith
  exact le_of_mul_le_mul_left this hβt

/-- AKMM, (12.13), p. 343: in the second stage, interior optimal hours of the static problem
with net wage `(1 − τ)w` and income `I` satisfy `c^{−σ}w(1 − τ) = ψℓ^{1/γ}`. -/
theorem eq_12_13 {ψ γ σ τ w I l : ℝ} (hγ : 0 < γ) (hl : 0 < l)
    (hc : 0 < (1 - τ) * w * l + I)
    (hmax : ∀ y, 0 ≤ y → stObj ψ γ σ ((1 - τ) * w) I y ≤ stObj ψ γ σ ((1 - τ) * w) I l) :
    ((1 - τ) * w * l + I) ^ (-σ) * w * (1 - τ) = ψ * l ^ (1 / γ) := by
  have := ext_foc_of_max hl hmax (st_obj_hasDerivAt (ψ := ψ) (σ := σ) hγ hc)
  linarith

/-! ### Marshallian and Hicksian elasticities -/

/-- AKMM, (12.12), p. 343: differentiating `c = (1 − τ)wℓ + I` along `w(s) = we^s` (`I` fixed):
`d log c/d log w = (1 − s_I) + (1 − s_I) d log ℓ/d log w`, `s_I = I/c`. -/
theorem eq_12_12 {τ w I l' : ℝ} {l : ℝ → ℝ} (hl : 0 < l 0) (hc : 0 < (1 - τ) * w * l 0 + I)
    (hdl : HasDerivAt l l' 0) :
    HasDerivAt (fun s => Real.log ((1 - τ) * (w * Real.exp s) * l s + I))
      ((1 - I / ((1 - τ) * w * l 0 + I)) + (1 - I / ((1 - τ) * w * l 0 + I)) * (l' / l 0)) 0 := by
  have hd : HasDerivAt (fun s => (1 - τ) * (w * Real.exp s) * l s + I)
      ((1 - τ) * w * l 0 + (1 - τ) * w * l') 0 := by
    have := (((st_exp_path w).const_mul (1 - τ)).mul hdl).add_const I
    refine this.congr_deriv ?_
    rw [Real.exp_zero, mul_one]
  have hc0 : (1 - τ) * (w * Real.exp 0) * l 0 + I ≠ 0 := by
    rw [Real.exp_zero, mul_one]; exact hc.ne'
  refine (hd.log hc0).congr_deriv ?_
  rw [Real.exp_zero, mul_one]
  have h1 : (1 - τ) * w * l 0 + I ≠ 0 := hc.ne'
  have h2 : l 0 ≠ 0 := hl.ne'
  field_simp
  ring

/-- AKMM, (12.14), p. 343: differentiating (12.13) in logs along the path,
`σ d log c/d log w + (1/γ) d log ℓ/d log w = 1` (`dc`, `dl` the log-derivatives). -/
theorem eq_12_14 {ψ γ σ τ w I l' : ℝ} {l : ℝ → ℝ} (hψ : 0 < ψ) (hτ : τ < 1) (hw : 0 < w)
    (hl : 0 < l 0) (hc : 0 < (1 - τ) * w * l 0 + I) (hdl : HasDerivAt l l' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * l s ^ (1 / γ) /
      ((1 - τ) * w * Real.exp s * l s + I) ^ (-σ) = (1 - τ) * w * Real.exp s) :
    σ * ((1 - I / ((1 - τ) * w * l 0 + I)) + (1 - I / ((1 - τ) * w * l 0 + I)) * (l' / l 0)) +
      1 / γ * (l' / l 0) = 1 := by
  have hnet : 0 < (1 - τ) * w := mul_pos (by linarith) hw
  have hW0 : 0 < (1 - τ) * w * Real.exp 0 := by rw [Real.exp_zero, mul_one]; exact hnet
  have hc0 : 0 < (1 - τ) * w * Real.exp 0 * l 0 + I := by rwa [Real.exp_zero, mul_one]
  have key := st_path_identity (I := fun _ => I) (I' := 0) hψ hW0 hl hc0
    (st_exp_path ((1 - τ) * w)) (hasDerivAt_const _ _) hdl hfoc
  rw [Real.exp_zero, mul_one, div_self hnet.ne'] at key
  have h1 : (1 - τ) * w * l 0 + I ≠ 0 := hc.ne'
  have h2 : l 0 ≠ 0 := hl.ne'
  have hx : ((1 - τ) * w * l 0 + (1 - τ) * w * l' + 0) / ((1 - τ) * w * l 0 + I) =
      (1 - I / ((1 - τ) * w * l 0 + I)) + (1 - I / ((1 - τ) * w * l 0 + I)) * (l' / l 0) := by
    field_simp; ring
  rw [hx] at key
  linarith

/-- AKMM, (12.15), p. 343: combining (12.12) and (12.14) as linear equations in
`x = d log c/d log w` and `ε = d log ℓ/d log w`:
`ε = (1 − σ(1 − s_I))/(1/γ + σ(1 − s_I))`. -/
theorem eq_12_15 {γ σ sI x e : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) (hs : sI < 1)
    (h12 : x = (1 - sI) + (1 - sI) * e) (h14 : σ * x + 1 / γ * e = 1) :
    e = (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) := by
  have hden : 0 < 1 / γ + σ * (1 - sI) := by
    have : 0 ≤ σ * (1 - sI) := mul_nonneg hσ (by linarith)
    have : 0 < 1 / γ := by positivity
    linarith
  rw [eq_div_iff hden.ne']
  subst h12
  linear_combination h14

/-- AKMM, (12.15), p. 343, along paths: the dynamic Marshallian elasticity with respect to the
wage, at net wage `(1 − τ)w` and `I_t` fixed, is (12.3) with `s_I = I/c`. -/
theorem eq_12_15_path {ψ γ σ τ w I l' : ℝ} {l : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hτ : τ < 1) (hw : 0 < w) (hl : 0 < l 0) (hc : 0 < (1 - τ) * w * l 0 + I)
    (hdl : HasDerivAt l l' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * l s ^ (1 / γ) /
      ((1 - τ) * w * Real.exp s * l s + I) ^ (-σ) = (1 - τ) * w * Real.exp s) :
    HasDerivAt (fun s => Real.log (l s))
      ((1 - σ * (1 - I / ((1 - τ) * w * l 0 + I))) /
        (1 / γ + σ * (1 - I / ((1 - τ) * w * l 0 + I)))) 0 :=
  eq_12_3 hψ hγ hσ (mul_pos (by linarith) hw) hl hc hdl hfoc

/-- AKMM, (12.16), p. 344, **the Slutsky equation** `ε^H = ε^M − ε_{ℓ,I}(1 − s_I)/s_I` with the
dynamic `ε_{ℓ,I} = −σs_I/(1/γ + σ(1 − s_I))` (p. 344), and (12.17)
`ε^H = 1/(1/γ + σ(1 − s_I))`. -/
theorem eq_12_16 {γ σ sI : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) (hs0 : sI ≠ 0) (hs1 : sI < 1) :
    (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) -
        (-σ * sI / (1 / γ + σ * (1 - sI))) * ((1 - sI) / sI) =
      1 / (1 / γ + σ * (1 - sI)) := by
  rw [st_slutsky hγ hσ hs0 hs1]
  ring

/-- AKMM, (12.17), p. 344: along `w(s) = we^s` with non-labour income compensated,
`dI/d log w = −(1 − τ)wℓ`, hours respond with the Hicksian elasticity
`1/(1/γ + σ(1 − s_I))`. -/
theorem eq_12_17 {ψ γ σ τ w I' l' : ℝ} {I l : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hτ : τ < 1) (hw : 0 < w) (hl : 0 < l 0) (hc : 0 < (1 - τ) * w * l 0 + I 0)
    (hdI : HasDerivAt I I' 0) (hcomp : I' = -((1 - τ) * w * l 0)) (hdl : HasDerivAt l l' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * l s ^ (1 / γ) /
      ((1 - τ) * w * Real.exp s * l s + I s) ^ (-σ) = (1 - τ) * w * Real.exp s) :
    HasDerivAt (fun s => Real.log (l s))
      (1 / (1 / γ + σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)))) 0 :=
  eq_12_4 hψ hγ hσ (mul_pos (by linarith) hw) hl hc hdI hcomp hdl hfoc

/-- AKMM, p. 344, **the sign of the compensation**: with the printed
`dI/dw = +(1 − τ)ℓ` (non-labour income rising with the wage) hours respond with
`(1 − 2σ(1 − s_I))/(1/γ + σ(1 − s_I))`, not the Hicksian (12.17); the two differ whenever
`σ(1 − s_I) ≠ 0`. -/
theorem dyn_compensation_sign {ψ γ σ τ w I' l' : ℝ} {I l : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hσ : 0 ≤ σ) (hτ : τ < 1) (hw : 0 < w) (hl : 0 < l 0)
    (hc : 0 < (1 - τ) * w * l 0 + I 0) (hdI : HasDerivAt I I' 0)
    (hcomp : I' = (1 - τ) * w * l 0) (hdl : HasDerivAt l l' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * l s ^ (1 / γ) /
      ((1 - τ) * w * Real.exp s * l s + I s) ^ (-σ) = (1 - τ) * w * Real.exp s) :
    HasDerivAt (fun s => Real.log (l s))
      ((1 - 2 * (σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)))) /
        (1 / γ + σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)))) 0 ∧
    (σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)) ≠ 0 →
      (1 - 2 * (σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)))) /
        (1 / γ + σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0))) ≠
      1 / (1 / γ + σ * (1 - I 0 / ((1 - τ) * w * l 0 + I 0)))) := by
  have hnet : 0 < (1 - τ) * w := mul_pos (by linarith) hw
  have hW0 : 0 < (1 - τ) * w * Real.exp 0 := by rw [Real.exp_zero, mul_one]; exact hnet
  have hc0 : 0 < (1 - τ) * w * Real.exp 0 * l 0 + I 0 := by rwa [Real.exp_zero, mul_one]
  have key := st_path_poly hψ hγ hW0 hl hc0 (st_exp_path ((1 - τ) * w)) hdI hdl hfoc
  simp only [Real.exp_zero, mul_one, hcomp] at key
  set W := (1 - τ) * w
  set c := W * l 0 + I 0
  have ha : 1 - I 0 / c = W * l 0 / c := by field_simp; ring
  have hden : 0 < 1 / γ + σ * (1 - I 0 / c) := by rw [ha]; positivity
  have hD : 0 < c + γ * σ * W * l 0 := by
    have : 0 ≤ γ * σ * W * l 0 := by positivity
    linarith
  have hl' : l' = γ * l 0 * (c - 2 * σ * W * l 0) / (c + γ * σ * W * l 0) := by
    rw [eq_div_iff hD.ne']
    have h : W * (l' * (c + γ * σ * W * l 0) - γ * l 0 * (c - 2 * σ * W * l 0)) = 0 := by
      linear_combination key
    linarith [(mul_eq_zero.1 h).resolve_left hnet.ne']
  refine ⟨(hdl.log hl.ne').congr_deriv ?_, fun hne h => hne ?_⟩
  · rw [hl', ha]
    have h1 : c ≠ 0 := hc.ne'
    have h4 : γ ≠ 0 := hγ.ne'
    have h5 : l 0 ≠ 0 := hl.ne'
    field_simp
  · rw [div_left_inj' hden.ne'] at h
    linarith

/-! ### The Frisch elasticity -/

/-- AKMM, (12.18)–(12.21), pp. 344–345, **the Frisch elasticity** for a general period utility.
Let `U_c`, `U_ℓ` be differentiable at `(c, ℓ)` with partial derivatives `U_cc, U_cℓ` and
`U_ℓc, U_ℓℓ`. If along `w(s) = we^s` consumption and hours satisfy (12.18) `U_c = λ` and
(12.19) `−U_ℓ = λ(1 − τ)w` near `0` with `λ` fixed, then
`d log ℓ/d log w = U_ℓ/(ℓU_ℓℓ − ℓU_ℓcU_cℓ/U_cc)`. -/
theorem eq_12_21 {Uc Ul : ℝ × ℝ → ℝ} {Ucc Ucl Ulc Ull lam τ w c' l' : ℝ} {c l : ℝ → ℝ}
    (hUc : HasFDerivAt Uc (Ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Ucl • ContinuousLinearMap.snd ℝ ℝ ℝ) (c 0, l 0))
    (hUl : HasFDerivAt Ul (Ulc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Ull • ContinuousLinearMap.snd ℝ ℝ ℝ) (c 0, l 0))
    (hdc : HasDerivAt c c' 0) (hdl : HasDerivAt l l' 0) (hl : 0 < l 0) (hUcc : Ucc ≠ 0)
    (hden : l 0 * Ull - l 0 * (Ulc * Ucl / Ucc) ≠ 0)
    (h18 : ∀ᶠ s in 𝓝 (0 : ℝ), Uc (c s, l s) = lam)
    (h19 : ∀ᶠ s in 𝓝 (0 : ℝ), -Ul (c s, l s) = lam * (1 - τ) * (w * Real.exp s)) :
    HasDerivAt (fun s => Real.log (l s))
      (Ul (c 0, l 0) / (l 0 * Ull - l 0 * (Ulc * Ucl / Ucc))) 0 := by
  have hp : HasDerivAt (fun s => (c s, l s)) (c', l') 0 := hdc.prodMk hdl
  have d18 := hUc.comp_hasDerivAt (x := (0 : ℝ)) hp
  have d19 := hUl.comp_hasDerivAt (x := (0 : ℝ)) hp
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul] at d18 d19
  have e18 : Ucc * c' + Ucl * l' = 0 := by
    have h0 := (hasDerivAt_const (0 : ℝ) lam).congr_of_eventuallyEq
      (h18.mono fun s hs => (hs : Uc (c s, l s) = lam))
    exact d18.unique h0
  have e19 : -(Ulc * c' + Ull * l') = lam * (1 - τ) * w := by
    have hrhs : HasDerivAt (fun s => lam * (1 - τ) * (w * Real.exp s))
        (lam * (1 - τ) * w) 0 := (st_exp_path w).const_mul _
    have h0 := hrhs.congr_of_eventuallyEq (h19.mono fun s hs => hs)
    exact d19.neg.unique h0
  have hUl0 : -Ul (c 0, l 0) = lam * (1 - τ) * w := by
    have := h19.self_of_nhds
    rwa [Real.exp_zero, mul_one] at this
  have hc' : c' = -(Ucl * l') / Ucc := by
    rw [eq_div_iff hUcc]; linarith
  have hmain : l' * (Ull - Ulc * Ucl / Ucc) = Ul (c 0, l 0) := by
    rw [hc'] at e19
    linear_combination hUl0 - e19
  refine (hdl.log hl.ne').congr_deriv ?_
  rw [div_eq_div_iff hl.ne' hden]
  linear_combination (l 0) * hmain

/-- The Frisch formula (12.21), `U_ℓ/(ℓU_ℓℓ − ℓU_ℓcU_cℓ/U_cc)`. -/
noncomputable def frischF (l Ul Ull Ulc Ucl Ucc : ℝ) : ℝ := Ul / (l * Ull - l * (Ulc * Ucl / Ucc))

/-- AKMM, p. 345: for the separable utility (12.8), with `U_ℓ = −ψℓ^{1/γ}`,
`U_ℓℓ = −(ψ/γ)ℓ^{1/γ−1}` and `U_ℓc = U_cℓ = 0`, (12.21) gives `ε^F = γ`; these are the
partial derivatives (`ℓ > 0`). -/
theorem dyn_frisch_separable {ψ γ Ucc l : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hl : 0 < l) :
    HasDerivAt (fun x => -disutil ψ γ x) (-(ψ * l ^ (1 / γ))) l ∧
      HasDerivAt (fun x => -(ψ * x ^ (1 / γ))) (-(ψ / γ * l ^ (1 / γ - 1))) l ∧
      frischF l (-(ψ * l ^ (1 / γ))) (-(ψ / γ * l ^ (1 / γ - 1))) 0 0 Ucc = γ := by
  refine ⟨(st_disutil_hasDerivAt hγ l).neg, ?_, ?_⟩
  · have := ((Real.hasDerivAt_rpow_const (p := 1 / γ) (Or.inl hl.ne')).const_mul ψ).neg
    exact this.congr_deriv (by ring)
  · unfold frischF
    have h : l * l ^ (1 / γ - 1) = l ^ (1 / γ) := by
      rw [Real.rpow_sub_one hl.ne']; field_simp
    have hp : 0 < l ^ (1 / γ) := Real.rpow_pos_of_pos hl _
    rw [show l * -(ψ / γ * l ^ (1 / γ - 1)) - l * (0 * 0 / Ucc) =
      -(ψ / γ * (l * l ^ (1 / γ - 1))) by ring, h]
    field_simp

/-- AKMM, p. 345, `ε^F = γ` for (12.8) **through the general formula** `eq_12_21`, along an
explicit path: with `λ > 0` fixed, `c(s) = λ^{−1/σ}` and `ℓ(s) = (λ(1 − τ)we^s/ψ)^γ` satisfy
(12.18)–(12.19) for `U_c = c^{−σ}`, `U_ℓ = −ψℓ^{1/γ}`, and `d log ℓ/d log w = γ`. -/
theorem dyn_frisch_separable_path {ψ γ σ lam τ w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 0 < σ)
    (hlam : 0 < lam) (hτ : τ < 1) (hw : 0 < w) :
    HasDerivAt (fun s => Real.log ((lam * (1 - τ) * (w * Real.exp s) / ψ) ^ γ)) γ 0 := by
  set c : ℝ → ℝ := fun _ => lam ^ (-(1 / σ))
  set l : ℝ → ℝ := fun s => (lam * (1 - τ) * (w * Real.exp s) / ψ) ^ γ
  have hc0 : 0 < c 0 := Real.rpow_pos_of_pos hlam _
  have hk : 0 < lam * (1 - τ) * w / ψ := by
    have : 0 < 1 - τ := by linarith
    positivity
  have hl0 : 0 < l 0 := by
    simp only [l, Real.exp_zero, mul_one]; exact Real.rpow_pos_of_pos hk _
  have hdl : HasDerivAt l (γ * l 0) 0 := by
    have hin : HasDerivAt (fun s => lam * (1 - τ) * (w * Real.exp s) / ψ)
        (lam * (1 - τ) * w / ψ) 0 := ((st_exp_path w).const_mul _).div_const ψ
    have hpos : lam * (1 - τ) * (w * Real.exp 0) / ψ ≠ 0 := by
      rw [Real.exp_zero, mul_one]; exact hk.ne'
    have := (Real.hasDerivAt_rpow_const (p := γ) (Or.inl hpos)).comp 0 hin
    refine this.congr_deriv ?_
    simp only [l, Real.exp_zero, mul_one]
    rw [Real.rpow_sub_one hk.ne']
    have : (1 - τ) ≠ 0 := (by linarith : (0 : ℝ) < 1 - τ).ne'
    field_simp
  -- the partial derivatives
  have hUc : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ (-σ))
      ((-σ * c 0 ^ (-σ - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (c 0, l 0) := by
    have := (Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hc0.ne')).hasFDerivAt.comp (c 0, l 0)
      (hasFDerivAt_fst (𝕜 := ℝ) (p := (c 0, l 0)))
    refine this.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
    simp
    ring
  have hUl : HasFDerivAt (fun p : ℝ × ℝ => -(ψ * p.2 ^ (1 / γ)))
      ((0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-(ψ / γ * l 0 ^ (1 / γ - 1))) • ContinuousLinearMap.snd ℝ ℝ ℝ) (c 0, l 0) := by
    have h1 := ((Real.hasDerivAt_rpow_const (p := 1 / γ) (Or.inl hl0.ne')).const_mul ψ).neg
    have := h1.hasFDerivAt.comp (c 0, l 0) (hasFDerivAt_snd (𝕜 := ℝ) (p := (c 0, l 0)))
    refine this.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
    simp [ContinuousLinearMap.toSpanSingleton_apply]
    ring
  have hσ' : -σ * c 0 ^ (-σ - 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.2 hσ.ne') (Real.rpow_pos_of_pos hc0 _).ne'
  have hden : l 0 * -(ψ / γ * l 0 ^ (1 / γ - 1)) -
      l 0 * (0 * 0 / (-σ * c 0 ^ (-σ - 1))) ≠ 0 := by
    have : 0 < ψ / γ * l 0 ^ (1 / γ - 1) := by
      have := Real.rpow_pos_of_pos hl0 (1 / γ - 1); positivity
    have : 0 < l 0 * (ψ / γ * l 0 ^ (1 / γ - 1)) := by positivity
    simp only [mul_zero, zero_div, sub_zero]
    nlinarith
  have h18 : ∀ᶠ s in 𝓝 (0 : ℝ), (fun p : ℝ × ℝ => p.1 ^ (-σ)) (c s, l s) = lam :=
    Eventually.of_forall fun s => by
      simp only [c]
      rw [← Real.rpow_mul hlam.le, show -(1 / σ) * -σ = 1 by field_simp, Real.rpow_one]
  have h19 : ∀ᶠ s in 𝓝 (0 : ℝ), -(fun p : ℝ × ℝ => -(ψ * p.2 ^ (1 / γ))) (c s, l s) =
      lam * (1 - τ) * (w * Real.exp s) := Eventually.of_forall fun s => by
    simp only [l, neg_neg]
    have hx : 0 < lam * (1 - τ) * (w * Real.exp s) / ψ := by
      have : 0 < 1 - τ := by linarith
      positivity
    rw [← Real.rpow_mul hx.le, mul_one_div_cancel hγ.ne', Real.rpow_one]
    field_simp
  have := eq_12_21 hUc hUl (hasDerivAt_const 0 _) hdl hl0 hσ' hden h18 h19
  refine this.congr_deriv ?_
  have hsep := (dyn_frisch_separable (Ucc := -σ * c 0 ^ (-σ - 1)) hψ hγ hl0).2.2
  unfold frischF at hsep
  simpa using hsep

/-! ### GHH preferences -/

/-- AKMM, (12.22), p. 345: the partial derivatives of GHH utility
`U = (c − G(ℓ))^{1−σ}/(1 − σ)`, `G = v` of (12.8), at `x = c − G(ℓ) > 0`:
`U_c = x^{−σ}`, `U_ℓ = −x^{−σ}G′`, `U_cc = −σx^{−σ−1}`, `U_cℓ = U_ℓc = σx^{−σ−1}G′`,
`U_ℓℓ = −σx^{−σ−1}G′² − x^{−σ}G″`, with `G′ = ψℓ^{1/γ}`, `G″ = (ψ/γ)ℓ^{1/γ−1}`. -/
theorem dyn_ghh_partials {ψ γ σ c l : ℝ} (hγ : 0 < γ) (hσ : σ ≠ 1) (hl : 0 < l)
    (hx : 0 < c - disutil ψ γ l) :
    HasDerivAt (fun c' => (c' - disutil ψ γ l) ^ (1 - σ) / (1 - σ))
      ((c - disutil ψ γ l) ^ (-σ)) c ∧
    HasDerivAt (fun l' => (c - disutil ψ γ l') ^ (1 - σ) / (1 - σ))
      (-((c - disutil ψ γ l) ^ (-σ) * (ψ * l ^ (1 / γ)))) l ∧
    HasDerivAt (fun c' => (c' - disutil ψ γ l) ^ (-σ))
      (-σ * (c - disutil ψ γ l) ^ (-σ - 1)) c ∧
    HasDerivAt (fun l' => (c - disutil ψ γ l') ^ (-σ))
      (σ * (c - disutil ψ γ l) ^ (-σ - 1) * (ψ * l ^ (1 / γ))) l ∧
    HasDerivAt (fun c' => -((c' - disutil ψ γ l) ^ (-σ) * (ψ * l ^ (1 / γ))))
      (σ * (c - disutil ψ γ l) ^ (-σ - 1) * (ψ * l ^ (1 / γ))) c ∧
    HasDerivAt (fun l' => -((c - disutil ψ γ l') ^ (-σ) * (ψ * l' ^ (1 / γ))))
      (-σ * (c - disutil ψ γ l) ^ (-σ - 1) * (ψ * l ^ (1 / γ)) ^ 2 -
        (c - disutil ψ γ l) ^ (-σ) * (ψ / γ * l ^ (1 / γ - 1))) l := by
  set x := c - disutil ψ γ l
  have hs : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have hU : HasDerivAt (fun y => y ^ (1 - σ) / (1 - σ)) (x ^ (-σ)) x := by
    have := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx.ne')).div_const (1 - σ)
    refine this.congr_deriv ?_
    rw [show 1 - σ - 1 = -σ by ring]; field_simp
  have hG := st_disutil_hasDerivAt (ψ := ψ) hγ l
  obtain ⟨h1, h2, -⟩ :=
    Miao.NeoclassicalGrowth.rb_ghh_mrs (w := 0) hU hG (Real.rpow_pos_of_pos hx _)
  have hP : HasDerivAt (fun y => y ^ (-σ)) (-σ * x ^ (-σ - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hc1 : HasDerivAt (fun c' => c' - disutil ψ γ l) 1 c := (hasDerivAt_id c).sub_const _
  have hl1 : HasDerivAt (fun l' => c - disutil ψ γ l') (-(ψ * l ^ (1 / γ))) l := hG.const_sub c
  have hG' : HasDerivAt (fun l' => ψ * l' ^ (1 / γ)) (ψ / γ * l ^ (1 / γ - 1)) l := by
    have := (Real.hasDerivAt_rpow_const (p := 1 / γ) (Or.inl hl.ne')).const_mul ψ
    exact this.congr_deriv (by ring)
  have hPc := hP.comp c hc1
  have hPl := hP.comp l hl1
  refine ⟨h1, h2, hPc.congr_deriv (by ring), hPl.congr_deriv (by ring),
    (hPc.mul_const (ψ * l ^ (1 / γ))).neg.congr_deriv (by ring), ?_⟩
  exact (hPl.mul hG').neg.congr_deriv (by simp only [Function.comp_apply]; ring)

/-- AKMM, p. 346: **the Frisch elasticity of GHH utility is `γ`**: (12.21) with the partial
derivatives of `dyn_ghh_partials` equals `γ`. -/
theorem dyn_frisch_ghh {ψ γ σ x l : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hx : 0 < x)
    (hl : 0 < l) :
    frischF l (-(x ^ (-σ) * (ψ * l ^ (1 / γ))))
      (-σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ)) ^ 2 - x ^ (-σ) * (ψ / γ * l ^ (1 / γ - 1)))
      (σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ))) (σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ)))
      (-σ * x ^ (-σ - 1)) = γ := by
  unfold frischF
  have hA : 0 < x ^ (-σ - 1) := Real.rpow_pos_of_pos hx _
  have hB : 0 < x ^ (-σ) := Real.rpow_pos_of_pos hx _
  have h : l * l ^ (1 / γ - 1) = l ^ (1 / γ) := by
    rw [Real.rpow_sub_one hl.ne']; field_simp
  have hp : 0 < l ^ (1 / γ) := Real.rpow_pos_of_pos hl _
  have hden : l * (-σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ)) ^ 2 -
      x ^ (-σ) * (ψ / γ * l ^ (1 / γ - 1))) - l * (σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ)) *
      (σ * x ^ (-σ - 1) * (ψ * l ^ (1 / γ))) / (-σ * x ^ (-σ - 1))) =
      -(x ^ (-σ) * (ψ / γ * l ^ (1 / γ))) := by
    rw [← h]; field_simp; ring
  rw [hden]
  field_simp

/-- AKMM, p. 346: **GHH utility has no income effect**: if `ℓ > 0` maximises
`u(wℓ + I − G(ℓ))` over `ℓ ≥ 0` (`u = c^{1−σ}/(1 − σ)`, at `x > 0`), then `ψℓ^{1/γ} = w`, so
`ℓ = (w/ψ)^γ` whatever `I`; along `we^s`, `d log ℓ/d log w = γ`. Hence
`ε^M = ε^H = ε^F = γ`. -/
theorem dyn_ghh_no_income_effect {ψ γ σ w I l : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : σ ≠ 1)
    (hw : 0 < w) (hl : 0 < l) (hx : 0 < w * l + I - disutil ψ γ l)
    (hmax : ∀ y, 0 ≤ y → (w * y + I - disutil ψ γ y) ^ (1 - σ) / (1 - σ) ≤
      (w * l + I - disutil ψ γ l) ^ (1 - σ) / (1 - σ)) :
    l = (w / ψ) ^ γ ∧
      HasDerivAt (fun s => Real.log ((w * Real.exp s / ψ) ^ γ)) γ 0 := by
  set x := w * l + I - disutil ψ γ l
  have hs : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have hU : HasDerivAt (fun y => y ^ (1 - σ) / (1 - σ)) (x ^ (-σ)) x := by
    have := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx.ne')).div_const (1 - σ)
    refine this.congr_deriv ?_
    rw [show 1 - σ - 1 = -σ by ring]; field_simp
  have hin : HasDerivAt (fun y => w * y + I - disutil ψ γ y) (w - ψ * l ^ (1 / γ)) l := by
    have := (((hasDerivAt_id l).const_mul w).add_const I).sub (st_disutil_hasDerivAt
      (ψ := ψ) hγ l)
    exact this.congr_deriv (by simp)
  have hd := hU.comp l hin
  have h0 := ext_foc_of_max hl hmax hd
  have hfoc : ψ * l ^ (1 / γ) = w := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (Real.rpow_pos_of_pos hx _).ne'
    · linarith
  refine ⟨?_, ?_⟩
  · rw [← hfoc, mul_div_cancel_left₀ _ hψ.ne', ← Real.rpow_mul hl.le, one_div_mul_cancel hγ.ne',
      Real.rpow_one]
  · have hk : ∀ s, Real.log ((w * Real.exp s / ψ) ^ γ) = γ * Real.log (w / ψ) + γ * s := by
      intro s
      rw [Real.log_rpow (by positivity), show w * Real.exp s / ψ = w / ψ * Real.exp s by ring,
        Real.log_mul (by positivity) (Real.exp_pos s).ne', Real.log_exp]
      ring
    simp only [hk]
    exact ((hasDerivAt_id (0 : ℝ)).const_mul γ |>.const_add _).congr_deriv (by simp)

/-! ### Cobb–Douglas and power-leisure utility -/

/-- AKMM, p. 346: the partial derivatives of the Cobb–Douglas utility
`U = c^{(1−ψ)k}(1 − ℓ)^{ψk}/k`, `k = 1 − σ` (that is `(c^{1−ψ}(1 − ℓ)^ψ)^{1−σ}/(1 − σ)`), at
`c > 0`, `x = 1 − ℓ > 0`, with `a = 1 − ψ`, `b = ψ`. -/
theorem dyn_cd_partials {a b k c l : ℝ} (hk : k ≠ 0) (hc : 0 < c) (hx : 0 < 1 - l) :
    HasDerivAt (fun c' => c' ^ (a * k) * (1 - l) ^ (b * k) / k)
      (a * c ^ (a * k - 1) * (1 - l) ^ (b * k)) c ∧
    HasDerivAt (fun l' => c ^ (a * k) * (1 - l') ^ (b * k) / k)
      (-(b * c ^ (a * k) * (1 - l) ^ (b * k - 1))) l ∧
    HasDerivAt (fun c' => a * c' ^ (a * k - 1) * (1 - l) ^ (b * k))
      (a * (a * k - 1) * c ^ (a * k - 1 - 1) * (1 - l) ^ (b * k)) c ∧
    HasDerivAt (fun l' => a * c ^ (a * k - 1) * (1 - l') ^ (b * k))
      (-(a * b * k * c ^ (a * k - 1) * (1 - l) ^ (b * k - 1))) l ∧
    HasDerivAt (fun c' => -(b * c' ^ (a * k) * (1 - l) ^ (b * k - 1)))
      (-(a * b * k * c ^ (a * k - 1) * (1 - l) ^ (b * k - 1))) c ∧
    HasDerivAt (fun l' => -(b * c ^ (a * k) * (1 - l') ^ (b * k - 1)))
      (b * (b * k - 1) * c ^ (a * k) * (1 - l) ^ (b * k - 1 - 1)) l := by
  have dc : ∀ p : ℝ, HasDerivAt (fun c' => c' ^ p) (p * c ^ (p - 1)) c :=
    fun p => Real.hasDerivAt_rpow_const (Or.inl hc.ne')
  have dl : ∀ p : ℝ, HasDerivAt (fun l' => (1 - l') ^ p) (-(p * (1 - l) ^ (p - 1))) l := by
    intro p
    have := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).comp l
      ((hasDerivAt_id l).const_sub 1)
    exact this.congr_deriv (by simp)
  refine ⟨((dc (a * k)).mul_const _).div_const k |>.congr_deriv (by field_simp),
    ((dl (b * k)).const_mul _).div_const k |>.congr_deriv (by field_simp),
    ((dc (a * k - 1)).const_mul a).mul_const _ |>.congr_deriv (by ring),
    ((dl (b * k)).const_mul (a * c ^ (a * k - 1))).congr_deriv (by ring),
    (((dc (a * k)).const_mul b).mul_const _).neg.congr_deriv (by ring),
    ((dl (b * k - 1)).const_mul (b * c ^ (a * k))).neg.congr_deriv (by ring)⟩

/-- AKMM, p. 346: **the Frisch elasticity of Cobb–Douglas utility** is
`ε^F = ((1 − ℓ)/ℓ)(1 − (1 − ψ)(1 − σ))/σ` (with `(1 − ψ)(1 − σ) ≠ 1`, `σ ≠ 0`, `0 < ψ < 1`). -/
theorem dyn_frisch_cd {ψ σ c l : ℝ} (hψ : 0 < ψ) (hψ1 : ψ < 1) (hσ : σ ≠ 0)
    (hak : (1 - ψ) * (1 - σ) ≠ 1) (hc : 0 < c) (hl : 0 < l) (hx : 0 < 1 - l) :
    frischF l (-(ψ * c ^ ((1 - ψ) * (1 - σ)) * (1 - l) ^ (ψ * (1 - σ) - 1)))
      (ψ * (ψ * (1 - σ) - 1) * c ^ ((1 - ψ) * (1 - σ)) * (1 - l) ^ (ψ * (1 - σ) - 1 - 1))
      (-((1 - ψ) * ψ * (1 - σ) * c ^ ((1 - ψ) * (1 - σ) - 1) * (1 - l) ^ (ψ * (1 - σ) - 1)))
      (-((1 - ψ) * ψ * (1 - σ) * c ^ ((1 - ψ) * (1 - σ) - 1) * (1 - l) ^ (ψ * (1 - σ) - 1)))
      ((1 - ψ) * ((1 - ψ) * (1 - σ) - 1) * c ^ ((1 - ψ) * (1 - σ) - 1 - 1) *
        (1 - l) ^ (ψ * (1 - σ))) =
      (1 - l) / l * ((1 - (1 - ψ) * (1 - σ)) / σ) := by
  unfold frischF
  set P := c ^ ((1 - ψ) * (1 - σ))
  set Q := (1 - l) ^ (ψ * (1 - σ))
  set x := 1 - l
  have hP : 0 < P := Real.rpow_pos_of_pos hc _
  have hQ : 0 < Q := Real.rpow_pos_of_pos hx _
  have e1 : c ^ ((1 - ψ) * (1 - σ) - 1) = P / c := Real.rpow_sub_one hc.ne' _
  have e2 : c ^ ((1 - ψ) * (1 - σ) - 1 - 1) = P / c / c := by
    rw [Real.rpow_sub_one hc.ne', e1]
  have e3 : x ^ (ψ * (1 - σ) - 1) = Q / x := Real.rpow_sub_one hx.ne' _
  have e4 : x ^ (ψ * (1 - σ) - 1 - 1) = Q / x / x := by
    rw [Real.rpow_sub_one hx.ne', e3]
  rw [e1, e2, e3, e4]
  have hak' : (1 - ψ) * (1 - σ) - 1 ≠ 0 := sub_ne_zero.2 hak
  have h1ψ : 1 - ψ ≠ 0 := by linarith
  set A := (1 - ψ) * (1 - σ) - 1 with hA
  field_simp
  rw [hA]
  field_simp
  linear_combination (ψ - σ * ψ + σ) * (mul_inv_cancel₀ hσ)

/-- AKMM, p. 346: the partial derivatives of the power-leisure utility
`ψ(1 − ℓ)^{1−γ}/(1 − γ)` (the consumption part does not depend on `ℓ`, so `U_ℓc = 0`):
`U_ℓ = −ψ(1 − ℓ)^{−γ}`, `U_ℓℓ = −ψγ(1 − ℓ)^{−γ−1}`; and the Frisch elasticity is
`((1 − ℓ)/ℓ)(1/γ)`. -/
theorem dyn_frisch_leisure {ψ γ l Ucc : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hγ1 : γ ≠ 1) (hl : 0 < l)
    (hx : 0 < 1 - l) :
    HasDerivAt (fun l' => ψ * (1 - l') ^ (1 - γ) / (1 - γ)) (-(ψ * (1 - l) ^ (-γ))) l ∧
      HasDerivAt (fun l' => -(ψ * (1 - l') ^ (-γ))) (-(ψ * γ * (1 - l) ^ (-γ - 1))) l ∧
      frischF l (-(ψ * (1 - l) ^ (-γ))) (-(ψ * γ * (1 - l) ^ (-γ - 1))) 0 0 Ucc =
        (1 - l) / l * (1 / γ) := by
  have dl : ∀ p : ℝ, HasDerivAt (fun l' => (1 - l') ^ p) (-(p * (1 - l) ^ (p - 1))) l := by
    intro p
    have := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).comp l
      ((hasDerivAt_id l).const_sub 1)
    exact this.congr_deriv (by simp)
  have hs : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  refine ⟨((dl (1 - γ)).const_mul ψ).div_const _ |>.congr_deriv ?_,
    ((dl (-γ)).const_mul ψ).neg.congr_deriv (by ring), ?_⟩
  · rw [show 1 - γ - 1 = -γ by ring]; field_simp
  · unfold frischF
    have e : (1 - l) ^ (-γ) = (1 - l) * (1 - l) ^ (-γ - 1) := by
      rw [Real.rpow_sub_one hx.ne']; field_simp
    have hp : 0 < (1 - l) ^ (-γ - 1) := Real.rpow_pos_of_pos hx _
    rw [e]
    simp only [mul_zero, zero_div, sub_zero]
    field_simp

/-- AKMM, p. 346: "individuals who work more hours are less responsive": a Frisch elasticity of
the form `((1 − ℓ)/ℓ)K`, `K > 0`, is strictly decreasing in `ℓ ∈ (0, 1)`. -/
theorem dyn_frisch_decreasing_hours {K l₁ l₂ : ℝ} (hK : 0 < K) (h₁ : 0 < l₁) (h₁₂ : l₁ < l₂) :
    (1 - l₂) / l₂ * K < (1 - l₁) / l₁ * K := by
  have h₂ : 0 < l₂ := lt_trans h₁ h₁₂
  apply mul_lt_mul_of_pos_right _ hK
  rw [div_lt_div_iff₀ h₂ h₁]
  nlinarith

/-! ### The ordering of the elasticities -/

/-- AKMM, p. 345, **`ε^F ≥ ε^H ≥ ε^M`** for (12.8): with `ε^F = γ`, (12.17) and (12.15)
(`σ ≥ 0`, `s_I < 1`); each equality holds iff `σ = 0` (utility linear in consumption). -/
theorem dyn_ordering {γ σ sI : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) (hs : sI < 1) :
    1 / (1 / γ + σ * (1 - sI)) ≤ γ ∧
      (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) ≤ 1 / (1 / γ + σ * (1 - sI)) ∧
      (1 / (1 / γ + σ * (1 - sI)) = γ ↔ σ = 0) ∧
      ((1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) = 1 / (1 / γ + σ * (1 - sI)) ↔ σ = 0) := by
  obtain ⟨-, -, h3, h4⟩ := st_signs hγ hσ hs
  have hg : 0 < 1 / γ := by positivity
  have hx : 0 ≤ σ * (1 - sI) := mul_nonneg hσ (by linarith)
  refine ⟨?_, h3, ⟨fun h => ?_, fun h => by subst h; simp⟩, h4⟩
  · rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ γ * (σ * (1 - sI)) := mul_nonneg hγ.le hx
    have e : γ * (1 / γ) = 1 := by field_simp
    nlinarith
  · have hden : 0 < 1 / γ + σ * (1 - sI) := by linarith
    rw [div_eq_iff hden.ne'] at h
    have e : γ * (1 / γ) = 1 := by field_simp
    have : γ * (σ * (1 - sI)) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hγ.ne'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact h''
      · exact absurd h'' (by linarith)

/-- AKMM, p. 344: as `σ → 0` the Hicksian and Marshallian elasticities (12.17), (12.15) tend
to the Frisch elasticity `γ` of (12.8). -/
theorem dyn_ordering_sigma_zero {γ a : ℝ} (hγ : 0 < γ) :
    Tendsto (fun σ => 1 / (1 / γ + σ * a)) (𝓝 0) (𝓝 γ) ∧
      Tendsto (fun σ => (1 - σ * a) / (1 / γ + σ * a)) (𝓝 0) (𝓝 γ) := by
  have hne : 1 / γ + 0 * a ≠ 0 := by
    simp only [one_div, zero_mul, add_zero, ne_eq, inv_eq_zero]; exact hγ.ne'
  have hden : ContinuousAt (fun σ : ℝ => 1 / γ + σ * a) 0 := by fun_prop
  have hnum : ContinuousAt (fun σ : ℝ => 1 - σ * a) 0 := by fun_prop
  have h1 := ((continuousAt_const (y := (1 : ℝ))).div hden hne).tendsto
  have h2 := (hnum.div hden hne).tendsto
  refine ⟨?_, ?_⟩
  · convert h1 using 2; simp
  · convert h2 using 2; simp

/-- AKMM, p. 345, **corrected**: "`ε^F ≥ ε^H ≥ ε^M` with equality holding when `σ → ∞`" is
false. As `σ → ∞` (with `1 − s_I = a > 0`) `ε^H → 0` and `ε^M → −1`, while `ε^F = γ`; and
`ε^H < γ` for every `σ > 0`. Equality holds as `σ → 0` (`dyn_ordering_sigma_zero`). -/
theorem dyn_ordering_sigma_infty {γ a : ℝ} (hγ : 0 < γ) (ha : 0 < a) :
    Tendsto (fun σ => 1 / (1 / γ + σ * a)) atTop (𝓝 0) ∧
      Tendsto (fun σ => (1 - σ * a) / (1 / γ + σ * a)) atTop (𝓝 (-1)) ∧
      ∀ σ, 0 < σ → 1 / (1 / γ + σ * a) < γ := by
  have hg : 0 < 1 / γ := by positivity
  have hD : Tendsto (fun σ : ℝ => 1 / γ + σ * a) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const ha)
  have h0 : Tendsto (fun σ => 1 / (1 / γ + σ * a)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hD
  refine ⟨h0, ?_, fun σ hσ => ?_⟩
  · have h2 : Tendsto (fun σ => -1 + (1 + 1 / γ) * (1 / (1 / γ + σ * a))) atTop
        (𝓝 (-1 + (1 + 1 / γ) * 0)) := tendsto_const_nhds.add (h0.const_mul _)
    rw [mul_zero, add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with σ hσ
    have : 0 < 1 / γ + σ * a := by positivity
    field_simp
    ring
  · rw [div_lt_iff₀ (by positivity)]
    have : 0 < γ * (σ * a) := by positivity
    have e : γ * (1 / γ) = 1 := by field_simp
    nlinarith

/-! ### Relative hours across periods -/

/-- AKMM, (12.23), p. 346: with the Euler equation `c_t^{−σ} = βRc_{t+1}^{−σ}` and (12.13) at
`t` and `t + 1`, `log(ℓ_{t+1}/ℓ_t) = γ log(w_{t+1}/w_t) + γ log((1 − τ_{t+1})/(1 − τ_t))
− γ log(βR)`: the elasticity of relative hours with respect to relative wages, and to relative
net-of-tax rates, is `γ`. -/
theorem eq_12_23 {ψ γ σ β R c₀ c₁ l₀ l₁ w₀ w₁ τ₀ τ₁ : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hβR : 0 < β * R) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hl₀ : 0 < l₀) (hl₁ : 0 < l₁) (hw₀ : 0 < w₀)
    (hw₁ : 0 < w₁) (hτ₀ : τ₀ < 1) (hτ₁ : τ₁ < 1)
    (heuler : c₀ ^ (-σ) = β * R * c₁ ^ (-σ))
    (h₀ : ψ * l₀ ^ (1 / γ) = c₀ ^ (-σ) * (1 - τ₀) * w₀)
    (h₁ : ψ * l₁ ^ (1 / γ) = c₁ ^ (-σ) * (1 - τ₁) * w₁) :
    Real.log (l₁ / l₀) = γ * Real.log (w₁ / w₀) + γ * Real.log ((1 - τ₁) / (1 - τ₀)) -
      γ * Real.log (β * R) := by
  have ht₀ : 0 < 1 - τ₀ := by linarith
  have ht₁ : 0 < 1 - τ₁ := by linarith
  have hp₀ : 0 < c₀ ^ (-σ) := Real.rpow_pos_of_pos hc₀ _
  have hp₁ : 0 < c₁ ^ (-σ) := Real.rpow_pos_of_pos hc₁ _
  have e₀ := congrArg Real.log h₀
  have e₁ := congrArg Real.log h₁
  have ee := congrArg Real.log heuler
  rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl₀ _).ne', Real.log_rpow hl₀,
    Real.log_mul (by positivity) hw₀.ne', Real.log_mul hp₀.ne' ht₀.ne'] at e₀
  rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl₁ _).ne', Real.log_rpow hl₁,
    Real.log_mul (by positivity) hw₁.ne', Real.log_mul hp₁.ne' ht₁.ne'] at e₁
  rw [Real.log_mul hβR.ne' hp₁.ne'] at ee
  rw [Real.log_div hl₁.ne' hl₀.ne', Real.log_div hw₁.ne' hw₀.ne',
    Real.log_div ht₁.ne' ht₀.ne']
  have : 1 / γ * (Real.log l₁ - Real.log l₀) = Real.log w₁ - Real.log w₀ +
      (Real.log (1 - τ₁) - Real.log (1 - τ₀)) - Real.log (β * R) := by linarith
  have e : Real.log l₁ - Real.log l₀ = γ * (1 / γ * (Real.log l₁ - Real.log l₀)) := by
    field_simp
  rw [e, this]
  ring

end AKMM.LaborSupply

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Estimating the Frisch elasticity; optimisation frictions

AKMM, §12.4.2, pp. 347–352.

* **The structural equations** as exact identities: (12.24) `log c = −(1/σ) log λ`
  (`eq_12_24`); (12.25) `log ℓ = const + γ log w + γ log λ` with `const = γ log((1 − τ)/ψ)`
  (`eq_12_25`); its first difference (12.26) (`eq_12_26`); the Euler equation with a borrowing
  multiplier in logs (12.27) (`eq_12_27`); the log-normal identity (12.28),
  `log E[λ′] = E[log λ′] + Var(log λ′)/2`, and `Var(ξ) = Var(log λ′)` for the prediction error
  (`eq_12_28`).
* **The first-order approximation** `log(λ − φ) ≈ log λ − φ/λ`: exactly
  `log(λ − φ) = log λ + log(1 − φ/λ)`, with `−x/(1 − x) ≤ log(1 − x) ≤ −x` and the error at most
  `x²/(1 − x)`, `x = φ/λ`, and the derivative `−1/λ` at `φ = 0` (`fe_log_approx`). (12.29) holds
  exactly with `log(1 − φ/λ)` in place of `−φ/λ` and with the constant of (12.27)
  (`eq_12_29`).
* (12.30)–(12.31) (`eq_12_31`) and the consumption-data equation
  `Δ log ℓ = γΔ log w − γσΔ log c` (`fe_consumption_data`).
* **Optimisation frictions** with GHH utility `log(c − ψℓ^{1+1/γ}/(1 + 1/γ))`, `c = wℓ`
  (12.32): the optimum (12.33) `ℓ* = (w/ψ)^γ`, unique (`eq_12_33`), and the optimal utility
  `−log(1 + γ) − γ log ψ + (1 + γ) log w` (`fr_value`); the decomposition of the utility gain and
  (12.34) (`eq_12_34`); the gain is nonnegative and increasing in `ε > 0` (`fr_gain_pos`,
  `fr_gain_strictMono`); its second-order expansion (12.35) with an explicit cubic error bound
  (`eq_12_35`); the threshold `ε_min = (2Δ/(γ(1 + γ)))^{1/2}` and the hours threshold
  `γε_min = (2Δγ/(1 + γ))^{1/2}` (`fr_threshold`).

Departures: (12.28) is stated for a Gaussian law of `log λ′` (the conditional law of the book);
the conditional expectations of (12.27)–(12.31) are represented by their values.
-/

namespace AKMM.LaborSupply

open Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

/-! ### The structural equations -/

/-- AKMM, (12.24), p. 347: `c^{−σ} = λ` gives `log c = −(1/σ) log λ` (`σ ≠ 0`). -/
theorem eq_12_24 {σ c lam : ℝ} (hσ : σ ≠ 0) (hc : 0 < c) (h : c ^ (-σ) = lam) :
    Real.log c = -(1 / σ) * Real.log lam := by
  rw [← h, Real.log_rpow hc]
  field_simp

/-- AKMM, (12.25), p. 347: `ψℓ^{1/γ} = λ(1 − τ)w` gives
`log ℓ = γ log((1 − τ)/ψ) + γ log w + γ log λ`. -/
theorem eq_12_25 {ψ γ τ w l lam : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hτ : τ < 1) (hw : 0 < w)
    (hl : 0 < l) (hlam : 0 < lam) (h : ψ * l ^ (1 / γ) = lam * (1 - τ) * w) :
    Real.log l = γ * Real.log ((1 - τ) / ψ) + γ * Real.log w + γ * Real.log lam := by
  have ht : 0 < 1 - τ := by linarith
  have e := congrArg Real.log h
  rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl _).ne', Real.log_rpow hl,
    Real.log_mul (by positivity) hw.ne', Real.log_mul hlam.ne' ht.ne'] at e
  rw [Real.log_div ht.ne' hψ.ne']
  have : Real.log l = γ * (1 / γ * Real.log l) := by field_simp
  rw [this]
  have : 1 / γ * Real.log l = Real.log lam + Real.log (1 - τ) + Real.log w - Real.log ψ := by
    linarith
  rw [this]
  ring

/-- AKMM, (12.26), p. 348: first-differencing (12.25) (the constant cancels):
`Δ log ℓ = γΔ log w + γΔ log λ`. -/
theorem eq_12_26 {γ k l₀ l₁ w₀ w₁ m₀ m₁ : ℝ} (h₀ : l₀ = k + γ * w₀ + γ * m₀)
    (h₁ : l₁ = k + γ * w₁ + γ * m₁) : l₁ - l₀ = γ * (w₁ - w₀) + γ * (m₁ - m₀) := by
  rw [h₀, h₁]; ring

/-- AKMM, (12.27), p. 348: the Euler equation with borrowing multiplier `φ`,
`λ − φ = βR·E[λ′]`, in logs: `log(λ − φ) = log(βR) + log E[λ′]`. -/
theorem eq_12_27 {β R lam φ m : ℝ} (hβR : 0 < β * R) (hm : 0 < m) (h : lam - φ = β * R * m) :
    Real.log (lam - φ) = Real.log (β * R) + Real.log m := by
  rw [h, Real.log_mul hβR.ne' hm.ne']

/-- AKMM, (12.28), p. 348: **the log-normal identity**. If `log λ′` is Gaussian with mean `μ`
and variance `v`, then `log E[λ′] = E[log λ′] + Var(log λ′)/2`; and the prediction error
`ξ = log λ′ − E[log λ′]` has `Var(ξ) = Var(log λ′)`. -/
theorem eq_12_28 (μ : ℝ) (v : ℝ≥0) :
    Real.log (∫ x, Real.exp x ∂gaussianReal μ v) =
        (∫ x, x ∂gaussianReal μ v) + Var[id; gaussianReal μ v] / 2 ∧
      Var[fun x => x - ∫ y, y ∂gaussianReal μ v; gaussianReal μ v] =
        Var[id; gaussianReal μ v] := by
  refine ⟨?_, ?_⟩
  · have h := congrFun (mgf_id_gaussianReal (μ := μ) (v := v)) 1
    simp only [mgf, id, one_mul, mul_one, one_pow] at h
    rw [h, Real.log_exp, integral_id_gaussianReal, variance_id_gaussianReal]
  · exact variance_sub_const measurable_id.aestronglyMeasurable _

/-- AKMM, p. 348, **the first-order approximation** `log(λ − φ) ≈ log λ − φ/λ` around
`φ = 0`: exactly `log(λ − φ) = log λ + log(1 − φ/λ)`, and for `x = φ/λ ∈ [0, 1)`,
`−x/(1 − x) ≤ log(1 − x) ≤ −x`, so the error `|log(1 − x) + x| ≤ x²/(1 − x)`; and the
derivative of `φ ↦ log(λ − φ)` at `0` is `−1/λ`. -/
theorem fe_log_approx {lam φ : ℝ} (hlam : 0 < lam) (hφ0 : 0 ≤ φ) (hφ : φ < lam) :
    Real.log (lam - φ) = Real.log lam + Real.log (1 - φ / lam) ∧
      -(φ / lam) / (1 - φ / lam) ≤ Real.log (1 - φ / lam) ∧
      Real.log (1 - φ / lam) ≤ -(φ / lam) ∧
      |Real.log (1 - φ / lam) + φ / lam| ≤ (φ / lam) ^ 2 / (1 - φ / lam) ∧
      HasDerivAt (fun x => Real.log (lam - x)) (-(1 / lam)) 0 := by
  have hx1 : φ / lam < 1 := by rw [div_lt_one hlam]; exact hφ
  have hx0 : 0 ≤ φ / lam := div_nonneg hφ0 hlam.le
  have hpos : 0 < 1 - φ / lam := by linarith
  have hne : lam - φ ≠ 0 := (sub_pos.2 hφ).ne'
  have hne' : -φ + lam ≠ 0 := by rw [neg_add_eq_sub]; exact hne
  have up : Real.log (1 - φ / lam) ≤ -(φ / lam) := by
    have := Real.log_le_sub_one_of_pos hpos; linarith
  have lo : -(φ / lam) / (1 - φ / lam) ≤ Real.log (1 - φ / lam) := by
    have := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 - φ / lam)⁻¹ = -(φ / lam) / (1 - φ / lam) := by field_simp; ring
    linarith
  refine ⟨?_, lo, up, ?_, ?_⟩
  · rw [← Real.log_mul hlam.ne' hpos.ne']
    congr 1
    field_simp
  · rw [abs_le]
    have e : -(φ / lam) / (1 - φ / lam) + φ / lam = -((φ / lam) ^ 2 / (1 - φ / lam)) := by
      field_simp; ring
    have hsq : 0 ≤ (φ / lam) ^ 2 / (1 - φ / lam) := by positivity
    constructor <;> linarith
  · have := ((hasDerivAt_id (0 : ℝ)).const_sub lam).log
      (by simp only [id_eq, sub_zero, ne_eq]; exact hlam.ne')
    refine this.congr_deriv ?_
    simp only [id, sub_zero]
    ring

/-- AKMM, (12.29), p. 348, **exactly**: if (12.26) holds and, from (12.27)–(12.28) at `t − 1`,
`log λ_{t−1} + log(1 − φ_{t−1}/λ_{t−1}) = κ + log λ_t − ξ_t + V/2` (`V` the conditional
variance of `ξ_t`, `κ` the constant), then
`Δ log ℓ_t = γΔ log w_t + γ(ξ_t + log(1 − φ_{t−1}/λ_{t−1}) − V/2) − γκ`. Replacing
`log(1 − φ/λ)` by `−φ/λ` (error at most `(φ/λ)²/(1 − φ/λ)`, `fe_log_approx`) and dropping the
constant gives the printed (12.29). -/
theorem eq_12_29 {γ κ V ξ dl dw m₀ m₁ L : ℝ} (h26 : dl = γ * dw + γ * (m₁ - m₀))
    (h27 : m₀ + L = κ + m₁ - ξ + V / 2) :
    dl = γ * dw + γ * (ξ + L - V / 2) - γ * κ := by
  rw [h26]
  have : m₁ - m₀ = ξ + L - V / 2 - κ := by linarith
  rw [this]; ring

/-- AKMM, (12.30)–(12.31), p. 349: writing `Δ log w = E_{t−1}[Δ log w] + ε` in (12.26),
`Δ log ℓ = γE_{t−1}[Δ log w] + γ(ε + Δ log λ)`. -/
theorem eq_12_31 {γ dl dw Edw ε dm : ℝ} (h26 : dl = γ * dw + γ * dm) (h30 : dw = Edw + ε) :
    dl = γ * Edw + γ * (ε + dm) := by
  rw [h26, h30]; ring

/-- AKMM, p. 349, **consumption data**: combining (12.24) (`log λ = −σ log c`) with (12.26),
`Δ log ℓ = γΔ log w − γσΔ log c`. -/
theorem fe_consumption_data {γ σ dl dw m₀ m₁ c₀ c₁ : ℝ} (h26 : dl = γ * dw + γ * (m₁ - m₀))
    (h₀ : m₀ = -σ * c₀) (h₁ : m₁ = -σ * c₁) : dl = γ * dw - γ * σ * (c₁ - c₀) := by
  rw [h26, h₀, h₁]; ring

/-! ### Optimisation frictions -/

/-- The tangent inequality for `x^p`, `p > 1`: `x^p ≥ y^p + py^{p−1}(x − y)` for `x ≥ 0`,
`y > 0`, strict for `x ≠ y`. -/
theorem fr_rpow_tangent {p x y : ℝ} (hp : 1 < p) (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≠ y) :
    y ^ p + p * y ^ (p - 1) * (x - y) < x ^ p := by
  have hs : -1 ≤ x / y - 1 := by have := div_nonneg hx hy.le; linarith
  have hs' : x / y - 1 ≠ 0 := by
    intro h; apply hxy; field_simp at h; linarith
  have := one_add_mul_self_lt_rpow_one_add hs hs' hp
  rw [show 1 + (x / y - 1) = x / y by ring, Real.div_rpow hx hy.le] at this
  have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy p
  rw [lt_div_iff₀ hyp] at this
  have e : y ^ (p - 1) = y ^ p / y := Real.rpow_sub_one hy.ne' p
  rw [e]
  have : y ^ p + p * (y ^ p / y) * (x - y) = (1 + p * (x / y - 1)) * y ^ p := by
    field_simp
  linarith

/-- GHH utility with consumption `c = wℓ` substituted: `log(wℓ − ψℓ^{1+1/γ}/(1 + 1/γ))`
(AKMM, (12.32), p. 350). -/
noncomputable def frV (ψ γ w l : ℝ) : ℝ := Real.log (w * l - disutil ψ γ l)

/-- At `ℓ* = (w/ψ)^γ`: `ψℓ*^{1/γ} = w` and `wℓ* − v(ℓ*) = wℓ*/(1 + γ)`. -/
theorem fr_opt_facts {ψ γ w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hw : 0 < w) :
    ψ * ((w / ψ) ^ γ) ^ (1 / γ) = w ∧
      w * (w / ψ) ^ γ - disutil ψ γ ((w / ψ) ^ γ) = w * (w / ψ) ^ γ / (1 + γ) := by
  have hk : 0 < w / ψ := by positivity
  have h1 : ((w / ψ) ^ γ) ^ (1 / γ) = w / ψ := by
    rw [← Real.rpow_mul hk.le, mul_one_div_cancel hγ.ne', Real.rpow_one]
  refine ⟨by rw [h1]; field_simp, ?_⟩
  unfold disutil
  have h2 : ((w / ψ) ^ γ) ^ (1 + 1 / γ) = (w / ψ) ^ γ * (w / ψ) := by
    rw [Real.rpow_add (Real.rpow_pos_of_pos hk _), Real.rpow_one, h1]
  rw [h2]
  have hp : 0 < (w / ψ) ^ γ := Real.rpow_pos_of_pos hk _
  field_simp
  ring

/-- AKMM, (12.33), p. 351: with `c = wℓ`, `ℓ* = (w/ψ)^γ` (and `c* = wℓ*`) uniquely maximises
the GHH utility `log(wℓ − v(ℓ))` over `ℓ ≥ 0` with `wℓ − v(ℓ) > 0`. -/
theorem eq_12_33 {ψ γ w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hw : 0 < w) :
    0 < w * (w / ψ) ^ γ - disutil ψ γ ((w / ψ) ^ γ) ∧
      ∀ l, 0 ≤ l → l ≠ (w / ψ) ^ γ → 0 < w * l - disutil ψ γ l →
        frV ψ γ w l < frV ψ γ w ((w / ψ) ^ γ) := by
  obtain ⟨h1, h2⟩ := fr_opt_facts hψ hγ hw
  have hk : 0 < w / ψ := by positivity
  set ls := (w / ψ) ^ γ
  have hls : 0 < ls := Real.rpow_pos_of_pos hk _
  refine ⟨by rw [h2]; positivity, fun l hl hne hpos => ?_⟩
  unfold frV
  apply Real.log_lt_log hpos
  -- the tangent inequality for `v`
  have hγ' : 0 < 1 / γ := by positivity
  have hp : 1 < 1 + 1 / γ := by linarith
  have ht := fr_rpow_tangent hp hl hls hne
  rw [show 1 + 1 / γ - 1 = 1 / γ by ring] at ht
  unfold disutil
  have hg : 0 < 1 + 1 / γ := by linarith
  have : ψ * ls ^ (1 + 1 / γ) / (1 + 1 / γ) + w * (l - ls) < ψ * l ^ (1 + 1 / γ) / (1 + 1 / γ) := by
    rw [div_add' _ _ _ hg.ne', div_lt_div_iff_of_pos_right hg, ← h1]
    nlinarith [mul_lt_mul_of_pos_left ht hψ]
  linarith

/-- AKMM, p. 351: the optimal utility is `U(c*, ℓ*) = −log(1 + γ) − γ log ψ + (1 + γ) log w`. -/
theorem fr_value {ψ γ w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hw : 0 < w) :
    frV ψ γ w ((w / ψ) ^ γ) = -Real.log (1 + γ) - γ * Real.log ψ + (1 + γ) * Real.log w := by
  unfold frV
  rw [(fr_opt_facts hψ hγ hw).2]
  have hk : 0 < w / ψ := by positivity
  rw [Real.log_div (by positivity : (0 : ℝ) < w * (w / ψ) ^ γ).ne'
    (by positivity : (0 : ℝ) < 1 + γ).ne', Real.log_mul hw.ne'
    (Real.rpow_pos_of_pos hk _).ne', Real.log_rpow hk, Real.log_div hw.ne' hψ.ne']
  ring

/-- AKMM, p. 351 and (12.34): the gain from a wage rise `w → w(1 + ε)` splits into the gain at
the old hours, `log(1 + ε(1 + γ))` (with consumption updated to `w(1 + ε)ℓ*`), and the gain from
re-optimising hours, `(1 + γ) log(1 + ε) − log(1 + ε(1 + γ))` (12.34); the total is
`(1 + γ) log(1 + ε)`. Here `1 + ε(1 + γ) > 0`. -/
theorem eq_12_34 {ψ γ w ε : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hw : 0 < w) (hε : -1 < ε)
    (hε' : 0 < 1 + ε * (1 + γ)) :
    frV ψ γ (w * (1 + ε)) ((w / ψ) ^ γ) - frV ψ γ w ((w / ψ) ^ γ) =
        Real.log (1 + ε * (1 + γ)) ∧
      frV ψ γ (w * (1 + ε)) ((w * (1 + ε) / ψ) ^ γ) - frV ψ γ (w * (1 + ε)) ((w / ψ) ^ γ) =
        (1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)) := by
  have h1e : 0 < 1 + ε := by linarith
  have hw' : 0 < w * (1 + ε) := by positivity
  have hk : 0 < w / ψ := by positivity
  have hls : 0 < (w / ψ) ^ γ := Real.rpow_pos_of_pos hk _
  have hold : frV ψ γ (w * (1 + ε)) ((w / ψ) ^ γ) =
      Real.log (w * (w / ψ) ^ γ / (1 + γ)) + Real.log (1 + ε * (1 + γ)) := by
    unfold frV
    have e : w * (1 + ε) * (w / ψ) ^ γ - disutil ψ γ ((w / ψ) ^ γ) =
        w * (w / ψ) ^ γ / (1 + γ) * (1 + ε * (1 + γ)) := by
      have := (fr_opt_facts hψ hγ hw).2
      have e2 : disutil ψ γ ((w / ψ) ^ γ) = w * (w / ψ) ^ γ - w * (w / ψ) ^ γ / (1 + γ) := by
        linarith
      rw [e2]; field_simp; ring
    rw [e, Real.log_mul (by positivity) hε'.ne']
  have h0 : frV ψ γ w ((w / ψ) ^ γ) = Real.log (w * (w / ψ) ^ γ / (1 + γ)) := by
    unfold frV; rw [(fr_opt_facts hψ hγ hw).2]
  refine ⟨by rw [hold, h0]; ring, ?_⟩
  rw [hold, fr_value hψ hγ hw', Real.log_mul hw.ne' h1e.ne']
  have : Real.log (w * (w / ψ) ^ γ / (1 + γ)) =
      -Real.log (1 + γ) - γ * Real.log ψ + (1 + γ) * Real.log w := by
    rw [← h0]; exact fr_value hψ hγ hw
  rw [this]; ring

/-- AKMM, p. 351: the gain from re-optimising hours (12.34) is positive for `ε ≠ 0` (it is the
gain of the optimum `ℓ*_ε` over `ℓ*`). -/
theorem fr_gain_pos {γ ε : ℝ} (hγ : 0 < γ) (hε : -1 < ε) (hε0 : ε ≠ 0)
    (hpos : 0 < 1 + ε * (1 + γ)) :
    0 < (1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)) := by
  -- Bernoulli: `(1 + ε)^{1+γ} > 1 + (1 + γ)ε`
  have hB := one_add_mul_self_lt_rpow_one_add (by linarith : (-1 : ℝ) ≤ ε) hε0
    (by linarith : (1 : ℝ) < 1 + γ)
  have h1e : 0 < 1 + ε := by linarith
  have := Real.log_lt_log hpos (by linarith : 1 + ε * (1 + γ) < (1 + ε) ^ (1 + γ))
  rw [Real.log_rpow h1e] at this
  linarith

/-- AKMM, p. 351: the gain `(1 + γ) log(1 + ε) − log(1 + ε(1 + γ))` is strictly increasing in
`ε ≥ 0`, so the agent re-optimises exactly for `ε` above a threshold. -/
theorem fr_gain_strictMono {γ : ℝ} (hγ : 0 < γ) :
    StrictMonoOn (fun ε => (1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)))
      (Set.Ici 0) := by
  have hder : ∀ ε, 0 ≤ ε → HasDerivAt
      (fun ε => (1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)))
      ((1 + γ) * (1 / (1 + ε)) - (1 + γ) / (1 + ε * (1 + γ))) ε := by
    intro ε hε
    have h1 := (((hasDerivAt_id ε).const_add 1).log (by simp; linarith)).const_mul (1 + γ)
    have h2 := (((hasDerivAt_id ε).mul_const (1 + γ)).const_add 1).log
      (by simp; nlinarith)
    exact (h1.sub h2).congr_deriv (by simp)
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x hx
    exact (hder x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := hx
    rw [(hder x hx0.le).deriv]
    have ha : 0 < 1 + x := by linarith
    have hb : 0 < 1 + x * (1 + γ) := by nlinarith
    rw [one_div, ← div_eq_mul_inv, sub_pos, div_lt_div_iff_of_pos_left (by linarith) hb ha]
    nlinarith

/-- AKMM, (12.35), p. 351, **with an explicit error bound**: for `|ε|(1 + γ) < 1`,
`|(1 + γ) log(1 + ε) − log(1 + ε(1 + γ)) − ½γ(1 + γ)ε²|
≤ (1 + γ)|ε|³/(1 − |ε|) + ((1 + γ)|ε|)³/(1 − (1 + γ)|ε|)`. -/
theorem eq_12_35 {γ ε : ℝ} (hγ : 0 < γ) (hε : |ε| * (1 + γ) < 1) :
    |(1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)) - 1 / 2 * γ * (1 + γ) * ε ^ 2| ≤
      (1 + γ) * (|ε| ^ 3 / (1 - |ε|)) + (|ε| * (1 + γ)) ^ 3 / (1 - |ε| * (1 + γ)) := by
  have hg : 1 ≤ 1 + γ := by linarith
  have hε1 : |ε| < 1 := by
    have : |ε| ≤ |ε| * (1 + γ) := le_mul_of_one_le_right (abs_nonneg _) hg
    linarith
  have hA := Real.abs_log_sub_add_sum_range_le (x := -ε) (by rwa [abs_neg]) 2
  have hB := Real.abs_log_sub_add_sum_range_le (x := -(ε * (1 + γ)))
    (by rw [abs_neg, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + γ)]; exact hε) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at hA hB
  rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + γ)] at hB
  norm_num at hA hB
  have key : (1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)) -
      1 / 2 * γ * (1 + γ) * ε ^ 2 =
      (1 + γ) * (-ε + ε ^ 2 / 2 + Real.log (1 + ε)) -
        (-(ε * (1 + γ)) + (ε * (1 + γ)) ^ 2 / 2 + Real.log (1 + ε * (1 + γ))) := by ring
  rw [key]
  have hpos : 0 < 1 + γ := by linarith
  calc _ ≤ |(1 + γ) * (-ε + ε ^ 2 / 2 + Real.log (1 + ε))| +
        |(-(ε * (1 + γ)) + (ε * (1 + γ)) ^ 2 / 2 + Real.log (1 + ε * (1 + γ)))| :=
        abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_pos hpos]
      gcongr

/-- AKMM, p. 352, **the thresholds**: for `ε > 0`, the second-order gain `½γ(1 + γ)ε²` exceeds
the cost `Δ > 0` iff `ε > ε_min = (2Δ/(γ(1 + γ)))^{1/2}`; hours change by
`log ℓ*_ε − log ℓ* = γ log(1 + ε) ≈ γε` (exactly, by (12.33)), and
`γε_min = (2Δγ/(1 + γ))^{1/2}`. -/
theorem fr_threshold {ψ γ w Δ ε : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hw : 0 < w) (hΔ : 0 < Δ)
    (hε : 0 < ε) :
    (Δ < 1 / 2 * γ * (1 + γ) * ε ^ 2 ↔ Real.sqrt (2 * Δ / (γ * (1 + γ))) < ε) ∧
      Real.log ((w * (1 + ε) / ψ) ^ γ) - Real.log ((w / ψ) ^ γ) = γ * Real.log (1 + ε) ∧
      γ * Real.sqrt (2 * Δ / (γ * (1 + γ))) = Real.sqrt (2 * Δ * γ / (1 + γ)) := by
  have hg : 0 < γ * (1 + γ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.sqrt_lt' hε, div_lt_iff₀ hg]
    constructor <;> intro h <;> nlinarith
  · have hk : 0 < w / ψ := by positivity
    have h1e : 0 < 1 + ε := by linarith
    rw [Real.log_rpow (by positivity), Real.log_rpow hk,
      show w * (1 + ε) / ψ = w / ψ * (1 + ε) by ring, Real.log_mul hk.ne' h1e.ne']
    ring
  · rw [show γ = Real.sqrt (γ ^ 2) by rw [Real.sqrt_sq hγ.le], ← Real.sqrt_mul (by positivity),
      Real.sqrt_sq hγ.le]
    congr 1
    field_simp

end AKMM.LaborSupply

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Labour supply and balanced growth

AKMM, §12.5, pp. 352–353, and Appendix 12.A, p. 849.

The planner (12.36) has `F = Z^{1−α}K^αL^{1−α}` and labour-augmenting growth `Z_{t+1} = GZ_t`;
on a balanced path `C, K, Z` grow by the factor `G` and hours `L` are constant. Utility is
`U(C, ℓ)` with leisure `ℓ = 1 − L`.

* **(12.37), "if"** (`eq_12_37_if`): for KPR utility `C^{1−σ}v(ℓ)/(1 − σ)` (`σ ≠ 1`) or
  `log C + v(ℓ)` (`kprU`, with partial derivatives `kpr_partials`), the Euler equation holds at
  every date of a balanced path iff `G^σ = β(MPK + 1 − δ)`, the intratemporal condition iff it
  holds at date `0`, and the resource constraint iff it holds at date `0`: hours can stay
  constant while the economy grows. The reason is the homogeneity of `U_C` (degree `−σ`) and
  of the MRS (degree `1`) in `C` (`kpr_homog`); in a static problem with only labour income the
  wage then has no effect on hours (`kpr_static_hours`).
* **(12.37) as printed is not of the KPR class**: `(C^{1−σ} − 1)v(1 − L)/(1 − σ)` has an MRS
  that is not homogeneous of degree one (`eq_12_37_printed_not_bgp`); the corrected form drops
  the `−1` (or puts it outside: `(C^{1−σ}v − 1)/(1 − σ)`).
* **(12.37), "only if"**, under a stated class. Step 1, (12.A.1)–(12.A.2): if for each leisure
  level the Euler ratio `U_C(gC, ℓ)/U_C(C, ℓ)` does not depend on `C`, for every growth factor
  `g > 0`, then `U_CC C/U_C = −σ(ℓ)` (the book prints `+σ`) and `U(·, ℓ)` is
  `a(ℓ)C^{1−σ(ℓ)}/(1 − σ(ℓ)) + b(ℓ)` or `a(ℓ) log C + b(ℓ)` (`eq_12_A_2`, from AKMM Chapter 4's
  Theorem .4, `theorem_4A_4`). Step 2, (12.A.3): within that class, with `a, σ, b`
  differentiable in `ℓ`, `a > 0`, `σ(ℓ) ≠ 1`, homogeneity of degree one of the MRS forces
  `σ′(ℓ) = 0` and `b′(ℓ) = 0` (`eq_12_A_3`); in the log class it forces `a′(ℓ) = 0`
  (`eq_12_A_3_log`). On the interval of leisure levels `σ` and `b` are then constant, which is
  (12.37) up to an additive constant (`eq_12_37_only_if`).
-/

namespace AKMM.LaborSupply

open Filter Topology

/-! ### Technology -/

/-- Output `Z^{1−α}K^αL^{1−α}` (AKMM, (12.36), p. 352). -/
noncomputable def bgF (α Z K L : ℝ) : ℝ := Z ^ (1 - α) * K ^ α * L ^ (1 - α)

/-- The marginal product of capital `αZ^{1−α}K^{α−1}L^{1−α}`. -/
noncomputable def bgMPK (α Z K L : ℝ) : ℝ := α * Z ^ (1 - α) * K ^ (α - 1) * L ^ (1 - α)

/-- The marginal product of labour `(1 − α)Z^{1−α}K^αL^{−α}`. -/
noncomputable def bgMPL (α Z K L : ℝ) : ℝ := (1 - α) * Z ^ (1 - α) * K ^ α * L ^ (-α)

/-- Scaling `Z` and `K` by `G > 0` scales output and the marginal product of labour by `G`
and leaves the marginal product of capital unchanged (AKMM, (12.A.1), p. 849:
`MPK = α(L/κ)^{1−α}`, `κ = K/Z`). -/
theorem bg_homog {α G Z K L : ℝ} (hG : 0 < G) (hZ : 0 < Z) (hK : 0 < K) :
    bgF α (G * Z) (G * K) L = G * bgF α Z K L ∧
      bgMPK α (G * Z) (G * K) L = bgMPK α Z K L ∧
      bgMPL α (G * Z) (G * K) L = G * bgMPL α Z K L := by
  unfold bgF bgMPK bgMPL
  rw [Real.mul_rpow hG.le hZ.le, Real.mul_rpow hG.le hK.le, Real.mul_rpow hG.le hK.le]
  have e1 : G ^ (1 - α) * G ^ α = G := by
    rw [← Real.rpow_add hG, show 1 - α + α = 1 by ring, Real.rpow_one]
  have e2 : G ^ (1 - α) * G ^ (α - 1) = 1 := by
    rw [← Real.rpow_add hG, show 1 - α + (α - 1) = 0 by ring, Real.rpow_zero]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (Z ^ (1 - α) * K ^ α * L ^ (1 - α)) * e1
  · linear_combination (α * Z ^ (1 - α) * K ^ (α - 1) * L ^ (1 - α)) * e2
  · linear_combination ((1 - α) * Z ^ (1 - α) * K ^ α * L ^ (-α)) * e1

/-! ### KPR utility -/

/-- KPR utility, the corrected (12.37): `C^{1−σ}v(ℓ)/(1 − σ)` for `σ ≠ 1`, `log C + v(ℓ)` for
`σ = 1` (`ℓ = 1 − L` is leisure). -/
noncomputable def kprU (σ : ℝ) (v : ℝ → ℝ) (C l : ℝ) : ℝ :=
  if σ = 1 then Real.log C + v l else C ^ (1 - σ) * v l / (1 - σ)

/-- The marginal utility of consumption of `kprU`. -/
noncomputable def kprUC (σ : ℝ) (v : ℝ → ℝ) (C l : ℝ) : ℝ :=
  if σ = 1 then C ^ (-σ) else C ^ (-σ) * v l

/-- The marginal utility of leisure of `kprU` (`v′` the derivative of `v`). -/
noncomputable def kprUl (σ : ℝ) (v' : ℝ → ℝ) (C l : ℝ) : ℝ :=
  if σ = 1 then v' l else C ^ (1 - σ) * v' l / (1 - σ)

/-- AKMM, (12.37): the partial derivatives of `kprU` are `kprUC` and `kprUl` (`C > 0`). -/
theorem kpr_partials {σ C l : ℝ} {v v' : ℝ → ℝ} (hC : 0 < C) (hv : HasDerivAt v (v' l) l) :
    HasDerivAt (fun x => kprU σ v x l) (kprUC σ v C l) C ∧
      HasDerivAt (fun y => kprU σ v C y) (kprUl σ v' C l) l := by
  by_cases hσ : σ = 1
  · subst hσ
    simp only [kprU, kprUC, kprUl, ↓reduceIte]
    refine ⟨?_, hv.const_add _⟩
    rw [Real.rpow_neg_one]
    exact (Real.hasDerivAt_log hC.ne').add_const _
  · simp only [kprU, kprUC, kprUl, hσ, ↓reduceIte]
    have hs : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    refine ⟨?_, (hv.const_mul (C ^ (1 - σ))).div_const (1 - σ)⟩
    have := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hC.ne')).mul_const (v l)).div_const
      (1 - σ)
    refine this.congr_deriv ?_
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp

/-- The marginal rate of substitution `U_ℓ/U_C` of KPR utility: `Cv′(ℓ)/((1 − σ)v(ℓ))`, or
`Cv′(ℓ)` when `σ = 1`. -/
theorem kpr_mrs {σ C l : ℝ} {v v' : ℝ → ℝ} (hC : 0 < C) (hv : σ ≠ 1 → v l ≠ 0) :
    kprUl σ v' C l / kprUC σ v C l =
      if σ = 1 then C * v' l else C * v' l / ((1 - σ) * v l) := by
  by_cases hσ : σ = 1
  · subst hσ
    simp only [kprUC, kprUl, ↓reduceIte, Real.rpow_neg_one]
    field_simp
  · simp only [kprUC, kprUl, hσ, ↓reduceIte]
    have hs : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    have hvl := hv hσ
    have e : C ^ (1 - σ) = C * C ^ (-σ) := by
      rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hC, Real.rpow_one]
    have hp : 0 < C ^ (-σ) := Real.rpow_pos_of_pos hC _
    rw [e]
    field_simp

/-- AKMM, p. 353, **homogeneity of KPR utility**: `U_C(GC, ℓ) = G^{−σ}U_C(C, ℓ)` and
`U_ℓ(GC, ℓ) = G^{1−σ}U_ℓ(C, ℓ)` for `G, C > 0`, so the MRS `U_ℓ/U_C` is homogeneous of degree
one in `C`. -/
theorem kpr_homog {σ G C l : ℝ} {v v' : ℝ → ℝ} (hG : 0 < G) (hC : 0 < C) :
    kprUC σ v (G * C) l = G ^ (-σ) * kprUC σ v C l ∧
      kprUl σ v' (G * C) l = G ^ (1 - σ) * kprUl σ v' C l := by
  by_cases hσ : σ = 1
  · subst hσ
    simp only [kprUC, kprUl, ↓reduceIte, Real.mul_rpow hG.le hC.le, sub_self, Real.rpow_zero,
      one_mul, and_true]
  · simp only [kprUC, kprUl, hσ, ↓reduceIte, Real.mul_rpow hG.le hC.le]
    constructor <;> ring

/-- AKMM, p. 353: "in a static setting with only labour income … a higher wage rate has no
effect on desired hours": with KPR utility the static condition `MRS(wL, 1 − L) = w`
(`C = wL`) holds iff `MRS(L, 1 − L) = 1`, which does not involve `w`. -/
theorem kpr_static_hours {σ w L : ℝ} {v v' : ℝ → ℝ} (hw : 0 < w) (hL : 0 < L)
    (hv : kprUC σ v L (1 - L) ≠ 0) :
    kprUl σ v' (w * L) (1 - L) / kprUC σ v (w * L) (1 - L) = w ↔
      kprUl σ v' L (1 - L) / kprUC σ v L (1 - L) = 1 := by
  obtain ⟨h1, h2⟩ := kpr_homog (σ := σ) (v := v) (v' := v') (l := 1 - L) hw hL
  rw [h1, h2]
  have hp : 0 < w ^ (-σ) := Real.rpow_pos_of_pos hw _
  have e : w ^ (1 - σ) = w * w ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hw, Real.rpow_one]
  rw [e, show w * w ^ (-σ) * kprUl σ v' L (1 - L) / (w ^ (-σ) * kprUC σ v L (1 - L)) =
    w * (kprUl σ v' L (1 - L) / kprUC σ v L (1 - L)) by field_simp]
  constructor
  · intro h; exact (mul_eq_left₀ hw.ne').1 h
  · intro h; rw [h, mul_one]

/-- AKMM, (12.37), p. 353, **"if"**: on a balanced path `Z_t = GᵗZ₀`, `K_t = GᵗK₀`,
`C_t = GᵗC₀` with constant hours `L ∈ (0, 1)`, and KPR utility (`v(1 − L) > 0` if `σ ≠ 1`):
(i) the Euler equation `U_C(C_t) = βU_C(C_{t+1})(MPK_{t+1} + 1 − δ)` holds at every `t` iff
`G^σ = β(MPK₀ + 1 − δ)`; (ii) the intratemporal condition `U_ℓ(C_t)/U_C(C_t) = MPL_t` holds at
every `t` iff it holds at `t = 0`; (iii) the resource constraint
`C_t + K_{t+1} = F(Z_t, K_t, L) + (1 − δ)K_t` holds at every `t` iff it holds at `t = 0`. -/
theorem eq_12_37_if {σ α β δ G Z₀ K₀ C₀ L : ℝ} {v v' : ℝ → ℝ} (hG : 0 < G) (hZ : 0 < Z₀)
    (hK : 0 < K₀) (hC : 0 < C₀) (hv : σ ≠ 1 → 0 < v (1 - L)) :
    ((∀ t : ℕ, kprUC σ v (G ^ t * C₀) (1 - L) = β * kprUC σ v (G ^ (t + 1) * C₀) (1 - L) *
        (bgMPK α (G ^ (t + 1) * Z₀) (G ^ (t + 1) * K₀) L + 1 - δ)) ↔
      G ^ σ = β * (bgMPK α Z₀ K₀ L + 1 - δ)) ∧
    ((∀ t : ℕ, kprUl σ v' (G ^ t * C₀) (1 - L) / kprUC σ v (G ^ t * C₀) (1 - L) =
        bgMPL α (G ^ t * Z₀) (G ^ t * K₀) L) ↔
      kprUl σ v' C₀ (1 - L) / kprUC σ v C₀ (1 - L) = bgMPL α Z₀ K₀ L) ∧
    ((∀ t : ℕ, G ^ t * C₀ + G ^ (t + 1) * K₀ =
        bgF α (G ^ t * Z₀) (G ^ t * K₀) L + (1 - δ) * (G ^ t * K₀)) ↔
      C₀ + G * K₀ = bgF α Z₀ K₀ L + (1 - δ) * K₀) := by
  have hGt : ∀ t : ℕ, 0 < G ^ t := fun t => pow_pos hG t
  have hUC0 : 0 < kprUC σ v C₀ (1 - L) := by
    by_cases hσ : σ = 1
    · simp only [kprUC, hσ, ↓reduceIte]; exact Real.rpow_pos_of_pos hC _
    · simp only [kprUC, hσ, ↓reduceIte]
      exact mul_pos (Real.rpow_pos_of_pos hC _) (hv hσ)
  have hGs : G ^ σ * G ^ (-σ) = 1 := by
    rw [← Real.rpow_add hG, add_neg_cancel, Real.rpow_zero]
  -- the Euler equation at date `t` is equivalent to the date-free condition
  have euler_t : ∀ t : ℕ, (kprUC σ v (G ^ t * C₀) (1 - L) = β *
      kprUC σ v (G ^ (t + 1) * C₀) (1 - L) *
        (bgMPK α (G ^ (t + 1) * Z₀) (G ^ (t + 1) * K₀) L + 1 - δ) ↔
      G ^ σ = β * (bgMPK α Z₀ K₀ L + 1 - δ)) := by
    intro t
    rw [(kpr_homog (v' := v') (hGt t) hC).1, (bg_homog (α := α) (L := L) (hGt (t + 1)) hZ hK).2.1,
      pow_succ, (kpr_homog (v' := v') (mul_pos (hGt t) hG) hC).1,
      Real.mul_rpow (hGt t).le hG.le]
    have hp : 0 < (G ^ t) ^ (-σ) := Real.rpow_pos_of_pos (hGt t) _
    constructor
    · intro h
      have h' : 1 = β * G ^ (-σ) * (bgMPK α Z₀ K₀ L + 1 - δ) := by
        have := mul_pos hp hUC0
        apply mul_left_cancel₀ this.ne'
        linear_combination h
      linear_combination G ^ σ * h' + (β * (bgMPK α Z₀ K₀ L + 1 - δ)) * hGs
    · intro h
      linear_combination ((G ^ t) ^ (-σ) * kprUC σ v C₀ (1 - L) * G ^ (-σ)) * h -
        ((G ^ t) ^ (-σ) * kprUC σ v C₀ (1 - L)) * hGs
  refine ⟨⟨fun h => (euler_t 0).1 (h 0), fun h t => (euler_t t).2 h⟩, ?_, ?_⟩
  · have intra_t : ∀ t : ℕ, (kprUl σ v' (G ^ t * C₀) (1 - L) /
        kprUC σ v (G ^ t * C₀) (1 - L) = bgMPL α (G ^ t * Z₀) (G ^ t * K₀) L ↔
        kprUl σ v' C₀ (1 - L) / kprUC σ v C₀ (1 - L) = bgMPL α Z₀ K₀ L) := by
      intro t
      obtain ⟨h1, h2⟩ := kpr_homog (σ := σ) (v := v) (v' := v') (l := 1 - L) (hGt t) hC
      rw [h1, h2, (bg_homog (α := α) (L := L) (hGt t) hZ hK).2.2]
      have hp : 0 < (G ^ t) ^ (-σ) := Real.rpow_pos_of_pos (hGt t) _
      have e : (G ^ t) ^ (1 - σ) = G ^ t * (G ^ t) ^ (-σ) := by
        rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add (hGt t), Real.rpow_one]
      rw [e, show G ^ t * (G ^ t) ^ (-σ) * kprUl σ v' C₀ (1 - L) /
        ((G ^ t) ^ (-σ) * kprUC σ v C₀ (1 - L)) =
          G ^ t * (kprUl σ v' C₀ (1 - L) / kprUC σ v C₀ (1 - L)) by field_simp]
      exact mul_right_inj' (hGt t).ne'
    exact ⟨fun h => by simpa using h 0, fun h t => (intra_t t).2 h⟩
  · have res_t : ∀ t : ℕ, (G ^ t * C₀ + G ^ (t + 1) * K₀ =
        bgF α (G ^ t * Z₀) (G ^ t * K₀) L + (1 - δ) * (G ^ t * K₀) ↔
        C₀ + G * K₀ = bgF α Z₀ K₀ L + (1 - δ) * K₀) := by
      intro t
      rw [(bg_homog (α := α) (L := L) (hGt t) hZ hK).1, pow_succ]
      constructor
      · intro h
        apply mul_left_cancel₀ (hGt t).ne'
        linear_combination h
      · intro h
        linear_combination (G ^ t) * h
    exact ⟨fun h => by simpa using h 0, fun h t => (res_t t).2 h⟩

/-- AKMM, (12.37), p. 353, **the printed form is not consistent with balanced growth**. For
`U = (C^{1−σ} − 1)v(ℓ)/(1 − σ)` (`σ ≠ 1`, `v(ℓ) ≠ 0`, `v′(ℓ) ≠ 0`) the partial derivatives
are `U_C = C^{−σ}v`, `U_ℓ = (C^{1−σ} − 1)v′/(1 − σ)`, and the MRS is not homogeneous of degree
one: `MRS(2·1, ℓ) ≠ 2·MRS(1, ℓ)` (`MRS(1, ℓ) = 0`). So constant hours with growing wages are
impossible. -/
theorem eq_12_37_printed_not_bgp {σ l v₀ v₁ : ℝ} {v : ℝ → ℝ} (hσ : σ ≠ 1)
    (hv : HasDerivAt v v₁ l) (hv0 : v l = v₀) (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0) :
    (∀ C, 0 < C → HasDerivAt (fun x => (x ^ (1 - σ) - 1) * v l / (1 - σ))
      (C ^ (-σ) * v₀) C) ∧
    (∀ C, HasDerivAt (fun y => (C ^ (1 - σ) - 1) * v y / (1 - σ))
      ((C ^ (1 - σ) - 1) * v₁ / (1 - σ)) l) ∧
    (((2 : ℝ) * 1) ^ (1 - σ) - 1) * v₁ / (1 - σ) / (((2 : ℝ) * 1) ^ (-σ) * v₀) ≠
      2 * (((1 : ℝ) ^ (1 - σ) - 1) * v₁ / (1 - σ) / ((1 : ℝ) ^ (-σ) * v₀)) := by
  have hs : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  refine ⟨fun C hC => ?_, fun C => ?_, ?_⟩
  · have := (((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hC.ne')).sub_const 1).mul_const
      (v l)).div_const (1 - σ)
    refine this.congr_deriv ?_
    rw [show 1 - σ - 1 = -σ by ring, hv0]
    field_simp
  · exact (hv.const_mul _).div_const _
  · simp only [Real.one_rpow, sub_self, zero_mul, zero_div, mul_zero, mul_one]
    have h2 : (2 : ℝ) ^ (1 - σ) ≠ 1 := by
      intro h
      have := congrArg Real.log h
      rw [Real.log_rpow two_pos, Real.log_one] at this
      rcases mul_eq_zero.1 this with h' | h'
      · exact hs h'
      · exact absurd h' (Real.log_pos one_lt_two).ne'
    have hp : 0 < (2 : ℝ) ^ (-σ) := Real.rpow_pos_of_pos two_pos _
    have : ((2 : ℝ) ^ (1 - σ) - 1) ≠ 0 := sub_ne_zero.2 h2
    exact div_ne_zero (div_ne_zero (mul_ne_zero this hv₁) hs) (mul_ne_zero hp.ne' hv₀)

/-! ### Appendix 12.A: "only if" -/

/-- AKMM, (12.A.1)–(12.A.2), p. 849, **corrected sign**. Fix a leisure level and let
`u = U(·, ℓ)` have `u′ > 0` and second derivative `u″` on `(0, ∞)`. If on every balanced path
the Euler ratio is the same at every consumption level — for every growth factor `1 + γ > 0`
there is `M` with `u′((1 + γ)C) = Mu′(C)` for all `C > 0` — then for some `σ`:
`Cu″(C)/u′(C) = −σ` (the book prints `+σ`), `u′(C) = u′(1)C^{−σ}`, and `u` is
`u′(1)C^{1−σ}/(1 − σ) + b` (`σ ≠ 1`) or `u′(1) log C + u(1)` (`σ = 1`): the candidate forms with
`v¹(ℓ) = u′(1)`. Proved with AKMM Chapter 4's Theorem .4. -/
theorem eq_12_A_2 {u u' u'' : ℝ → ℝ} (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu' : ∀ c, 0 < c → HasDerivAt u' (u'' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hbgp : ∀ γ, -1 < γ → ∃ M, ∀ c, 0 < c → u' ((1 + γ) * c) = M * u' c) :
    ∃ σ, (∀ c, 0 < c → c * u'' c / u' c = -σ) ∧ (∀ c, 0 < c → u' c = u' 1 * c ^ (-σ)) ∧
      (σ = 1 → ∀ c, 0 < c → u c = u' 1 * Real.log c + u 1) ∧
      (σ ≠ 1 → ∃ b, ∀ c, 0 < c → u c = u' 1 * c ^ (1 - σ) / (1 - σ) + b) := by
  obtain ⟨hform, hlog, hpow⟩ := AKMM.DynamicOptimization.theorem_4A_4 hu hu' hpos hbgp
  set σ := -u'' 1 / u' 1
  refine ⟨σ, fun c hc => ?_, hform, hlog, hpow⟩
  have h1 : 0 < u' 1 := hpos 1 one_pos
  -- `u″(c) = −σu′(1)c^{−σ−1}` by uniqueness of the derivative
  have hd : HasDerivAt (fun x => u' 1 * x ^ (-σ)) (u' 1 * (-σ * c ^ (-σ - 1))) c :=
    (Real.hasDerivAt_rpow_const (Or.inl hc.ne')).const_mul _
  have heq : (fun x => u' 1 * x ^ (-σ)) =ᶠ[𝓝 c] u' := by
    filter_upwards [lt_mem_nhds hc] with x hx using (hform x hx).symm
  have hu'' : u'' c = u' 1 * (-σ * c ^ (-σ - 1)) := (hu' c hc).unique (hd.congr_of_eventuallyEq
    heq.symm)
  rw [hu'', hform c hc, Real.rpow_sub_one hc.ne']
  have hp : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  field_simp

/-- The leisure derivative of the candidate `a(ℓ)C^{1−s(ℓ)}/(1 − s(ℓ)) + b(ℓ)` (`C > 0`,
`s(ℓ) ≠ 1`): `C^{1−s}(a′/(1 − s) + as′/(1 − s)² − (as′/(1 − s)) log C) + b′`. -/
theorem kpr_candidate_deriv {a s b : ℝ → ℝ} {a' s' b' l C : ℝ} (ha : HasDerivAt a a' l)
    (hs : HasDerivAt s s' l) (hb : HasDerivAt b b' l) (hs1 : s l ≠ 1) (hC : 0 < C) :
    HasDerivAt (fun x => a x * C ^ (1 - s x) / (1 - s x) + b x)
      (C ^ (1 - s l) * (a' / (1 - s l) + a l * s' / (1 - s l) ^ 2 -
        a l * s' / (1 - s l) * Real.log C) + b') l := by
  have hm : 1 - s l ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have hpow : HasDerivAt (fun x => C ^ (1 - s x)) (C ^ (1 - s l) * (-s' * Real.log C)) l := by
    have he : (fun x => C ^ (1 - s x)) = fun x => Real.exp ((1 - s x) * Real.log C) := by
      funext x; rw [Real.rpow_def_of_pos hC, mul_comm]
    rw [he]
    have := (((hs.const_sub 1).mul_const (Real.log C))).exp
    refine this.congr_deriv ?_
    rw [Real.rpow_def_of_pos hC, mul_comm (Real.log C)]
  have := ((ha.mul hpow).div (hs.const_sub 1) hm).add hb
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- AKMM, (12.A.3), p. 849: **the intratemporal condition forces `σ′ = 0` and `v²′ = 0`**.
Let `U(C, x) = a(x)C^{1−s(x)}/(1 − s(x)) + b(x)` near leisure `ℓ`, with `a, s, b`
differentiable at `ℓ`, `a(ℓ) > 0`, `s(ℓ) ≠ 1`, `U_C(C, ℓ) = a(ℓ)C^{−s(ℓ)}` and `U_ℓ(C)` the
leisure derivative. If the MRS is homogeneous of degree one in `C` —
`U_ℓ(gC)U_C(C) = gU_ℓ(C)U_C(gC)` for all `g, C > 0`, which is what the intratemporal condition
along balanced paths with growing wages requires — then `s′(ℓ) = 0` and `b′(ℓ) = 0`. -/
theorem eq_12_A_3 {a s b : ℝ → ℝ} {a' s' b' l : ℝ} {Ul : ℝ → ℝ} (ha : HasDerivAt a a' l)
    (hs : HasDerivAt s s' l) (hb : HasDerivAt b b' l) (hapos : 0 < a l) (hs1 : s l ≠ 1)
    (hUl : ∀ C, 0 < C → HasDerivAt (fun x => a x * C ^ (1 - s x) / (1 - s x) + b x) (Ul C) l)
    (hhom : ∀ g, 0 < g → ∀ C, 0 < C →
      Ul (g * C) * (a l * C ^ (-s l)) = g * Ul C * (a l * (g * C) ^ (-s l))) :
    s' = 0 ∧ b' = 0 := by
  have hm : 1 - s l ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  set m := 1 - s l with hmdef
  set A1 := a' / m + a l * s' / m ^ 2
  set A2 := -(a l * s' / m)
  have hUlf : ∀ C, 0 < C → Ul C = C ^ m * (A1 + A2 * Real.log C) + b' := by
    intro C hC
    have := (hUl C hC).unique (kpr_candidate_deriv ha hs hb hs1 hC)
    rw [this]; ring
  -- `U_ℓ(g) = g^m U_ℓ(1)`
  have hscale : ∀ g, 0 < g → Ul g = g ^ m * Ul 1 := by
    intro g hg
    have h := hhom g hg 1 one_pos
    simp only [mul_one, Real.one_rpow] at h
    have hp : 0 < g ^ (-s l) := Real.rpow_pos_of_pos hg _
    have e : g ^ m = g * g ^ (-s l) := by
      rw [hmdef, show 1 - s l = 1 + -s l by ring, Real.rpow_add hg, Real.rpow_one]
    rw [e]
    apply mul_right_cancel₀ hapos.ne'
    linear_combination h
  -- evaluate at `g = e^{t/m}`
  have key : ∀ t : ℝ, Real.exp t * (A2 * (t / m)) + b' * (1 - Real.exp t) = 0 := by
    intro t
    have hg : 0 < Real.exp (t / m) := Real.exp_pos _
    have h := hscale _ hg
    rw [hUlf _ hg, hUlf 1 one_pos, Real.log_exp, Real.log_one, Real.one_rpow, ← Real.exp_mul,
      div_mul_cancel₀ _ hm] at h
    linear_combination h
  have k1 := key 1
  have k2 := key 2
  have he : 2 < Real.exp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [hexp2] at k2
  set e := Real.exp 1
  have hX : A2 / m * (e * (e - 1)) = 0 := by
    linear_combination k2 - (e + 1) * k1
  have hA2 : A2 = 0 := by
    have hne : e * (e - 1) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
    have := (mul_eq_zero.1 hX).resolve_right hne
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h hm
  have hb' : b' = 0 := by
    rw [hA2] at k1
    have : b' * (1 - e) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right (by linarith)
  refine ⟨?_, hb'⟩
  have : a l * s' / m = 0 := by linarith
  rcases div_eq_zero_iff.1 this with h | h
  · exact (mul_eq_zero.1 h).resolve_left hapos.ne'
  · exact absurd h hm

/-- AKMM, p. 849, "the derivation for the log case is similar": for
`U(C, x) = a(x) log C + b(x)` with `a(ℓ) > 0`, homogeneity of degree one of the MRS in `C`
forces `a′(ℓ) = 0` (`v¹` constant, not `v²`), so `U = a log C + b(ℓ)` is (12.37) with `σ = 1`
up to the positive factor `a`. -/
theorem eq_12_A_3_log {a b : ℝ → ℝ} {a' b' l : ℝ} (ha : HasDerivAt a a' l)
    (hb : HasDerivAt b b' l) (hapos : 0 < a l) {Ul : ℝ → ℝ}
    (hUl : ∀ C, 0 < C → HasDerivAt (fun x => a x * Real.log C + b x) (Ul C) l)
    (hhom : ∀ g, 0 < g → ∀ C, 0 < C → Ul (g * C) * (a l / C) = g * Ul C * (a l / (g * C))) :
    a' = 0 := by
  have hUlf : ∀ C, 0 < C → Ul C = a' * Real.log C + b' := fun C hC =>
    (hUl C hC).unique ((ha.mul_const _).add hb)
  have h := hhom (Real.exp 1) (Real.exp_pos 1) 1 one_pos
  rw [mul_one, hUlf _ (Real.exp_pos 1), hUlf 1 one_pos, Real.log_exp, Real.log_one] at h
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  field_simp at h
  nlinarith [hapos]

/-- AKMM, (12.37), p. 353, **"only if"** under the stated class: if at every leisure level
`ℓ ∈ (0, 1)` the candidate `a(ℓ)C^{1−s(ℓ)}/(1 − s(ℓ)) + b(ℓ)` of `eq_12_A_2` satisfies the
hypotheses of `eq_12_A_3`, then `s ≡ σ` and `b ≡ b₀` are constant on `(0, 1)`: `U` is the KPR
form `C^{1−σ}a(ℓ)/(1 − σ)` up to an additive constant. -/
theorem eq_12_37_only_if {a s b a' s' b' : ℝ → ℝ} {Ul : ℝ → ℝ → ℝ}
    (ha : ∀ l ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt a (a' l) l)
    (hs : ∀ l ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt s (s' l) l)
    (hb : ∀ l ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt b (b' l) l)
    (hapos : ∀ l ∈ Set.Ioo (0 : ℝ) 1, 0 < a l) (hs1 : ∀ l ∈ Set.Ioo (0 : ℝ) 1, s l ≠ 1)
    (hUl : ∀ l ∈ Set.Ioo (0 : ℝ) 1, ∀ C, 0 < C →
      HasDerivAt (fun x => a x * C ^ (1 - s x) / (1 - s x) + b x) (Ul l C) l)
    (hhom : ∀ l ∈ Set.Ioo (0 : ℝ) 1, ∀ g, 0 < g → ∀ C, 0 < C →
      Ul l (g * C) * (a l * C ^ (-s l)) = g * Ul l C * (a l * (g * C) ^ (-s l))) :
    ∃ σ b₀, ∀ l ∈ Set.Ioo (0 : ℝ) 1, s l = σ ∧ b l = b₀ := by
  have hzero : ∀ l ∈ Set.Ioo (0 : ℝ) 1, s' l = 0 ∧ b' l = 0 := fun l hl =>
    eq_12_A_3 (ha l hl) (hs l hl) (hb l hl) (hapos l hl) (hs1 l hl) (hUl l hl) (hhom l hl)
  have hmid : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨s (1 / 2), b (1 / 2), fun l hl => ⟨?_, ?_⟩⟩
  · exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo 0 1).isPreconnected
      (fun y hy => (hs y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [(hs y hy).deriv, (hzero y hy).1]; rfl) hl hmid
  · exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo 0 1).isPreconnected
      (fun y hy => (hb y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [(hb y hy).deriv, (hzero y hy).2]; rfl) hl hmid

/-- The hypotheses of `eq_12_37_only_if` are satisfiable: for `a ≡ 1`, `s ≡ 2`, `b ≡ 0`
(`U = −C^{−1}`) the leisure derivative is `0` and the homogeneity condition holds. -/
theorem eq_12_37_only_if_instance :
    ∀ l ∈ Set.Ioo (0 : ℝ) 1, ∀ C, 0 < C →
      HasDerivAt (fun x => (fun _ => (1 : ℝ)) x * C ^ (1 - (fun _ => (2 : ℝ)) x) /
        (1 - (fun _ => (2 : ℝ)) x) + (fun _ => (0 : ℝ)) x) 0 l ∧
      ∀ g, 0 < g → (0 : ℝ) * (1 * C ^ (-(2 : ℝ))) = g * 0 * (1 * (g * C) ^ (-(2 : ℝ))) := by
  intro l _ C _
  exact ⟨hasDerivAt_const l _, fun g _ => by ring⟩

end AKMM.LaborSupply

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Taxes, income effects, business cycles and human capital

AKMM, §12.6–12.7, pp. 353–359.

* **Prescott** (12.38)–(12.39): from the household's intratemporal conditions
  `1/C = μ(1 + τ_c)`, `ψL^{1/γ} = μ(1 − τ_ℓ)w` and `w = (1 − α)Y/L` (`bg_mpl_eq`),
  `L = [(1 − τ)(1 − α)/(χψ)]^{γ/(1+γ)}` with `τ = (τ_ℓ + τ_c)/(1 + τ_c)` and `χ = C/Y`
  (`eq_12_39`). The U.S./Italy ratio is `[(0.60/0.81)/(0.36/0.69)]^{γ/(1+γ)}`; at `γ = 1` it lies
  in `(1.19, 1.20)`, not `1.42`; `1.42` is the limit `γ → ∞` (`eq_12_39_us_italy`).
* **Income effects** (§12.6.1): in the benchmark the ratio of the income to the substitution
  effect is `(ε^H − ε^M)/ε^H = σ(1 − s_I)` (`ti_effect_ratio`). With subsistence consumption
  `log(C − C̄)` the problem is the benchmark at `σ = 1` with income `−C̄`; the ratio is
  `C/(C − C̄) > 1`, decreasing in `C` and tending to `1` (`ti_subsistence`), and hours fall with
  the wage (`ti_subsistence_marshallian`). With `σ > 1` and no non-labour income the ratio is
  `σ > 1` at every wage, and along wages growing by `G` hours fall at the constant factor
  `G^{(1−σ)/(1/γ+σ)}` (`ti_sigma_gt_one`).
* **Business cycles** (12.40): `log L_t = const − (γ/(1 + γ)) log(C_t/Y_t)` (`eq_12_40`); the
  coefficient is `1/2` at `γ = 1` and tends to `1` as `γ → ∞` (`ti_cycle_coefficient`); without
  capital (`Y = ZL`, `C = Y`) hours do not depend on productivity (`ti_no_capital`).
* **Imai–Keane** (12.41): with `w_t = (1 + κΣ_{j<t}ℓ_j)w₀`, the marginal effect of `ℓ_s` on the
  present value of earnings is `R^{−s}(1 − τ)[w_s + κw₀Σ_{j=1}^{T−s}R^{−j}ℓ_{s+j}]`
  (`ik_marginal_earnings`), and the first-order conditions of the lifetime problem give (12.41)
  (`eq_12_41`).

Departure: (12.41) is derived for perfect foresight (no expectation operator).
-/

namespace AKMM.LaborSupply

open Filter Topology

/-! ### Prescott (2004) -/

/-- With Cobb–Douglas technology the marginal product of labour is `(1 − α)Y/L`. -/
theorem bg_mpl_eq {α Z K L : ℝ} (hL : 0 < L) :
    bgMPL α Z K L = (1 - α) * bgF α Z K L / L := by
  unfold bgMPL bgF
  have e : L ^ (1 - α) = L * L ^ (-α) := by
    rw [show 1 - α = 1 + -α by ring, Real.rpow_add hL, Real.rpow_one]
  rw [e]
  field_simp

/-- AKMM, (12.39), p. 354: from `1/C = μ(1 + τ_c)`, `ψL^{1/γ} = μ(1 − τ_ℓ)w` and
`w = (1 − α)Y/L`, with `χ = C/Y` and `τ = (τ_ℓ + τ_c)/(1 + τ_c)` (so that
`1 − τ = (1 − τ_ℓ)/(1 + τ_c)`): `L = [(1 − τ)(1 − α)/(χψ)]^{γ/(1+γ)}`. -/
theorem eq_12_39 {ψ γ α τl τc μ C Y L w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hτc : 0 < 1 + τc)
    (hC : 0 < C) (hY : 0 < Y) (hL : 0 < L)
    (hc : 1 / C = μ * (1 + τc)) (hl : ψ * L ^ (1 / γ) = μ * (1 - τl) * w)
    (hw : w = (1 - α) * Y / L) :
    1 - (τl + τc) / (1 + τc) = (1 - τl) / (1 + τc) ∧
      L = ((1 - (τl + τc) / (1 + τc)) * (1 - α) / (C / Y * ψ)) ^ (γ / (1 + γ)) := by
  have htax : 1 - (τl + τc) / (1 + τc) = (1 - τl) / (1 + τc) := by field_simp; ring
  refine ⟨htax, ?_⟩
  have hμ : μ = 1 / (C * (1 + τc)) := by
    rw [eq_div_iff (by positivity)]
    have := hc; field_simp at this; linarith
  have key : L ^ ((1 + γ) / γ) = (1 - (τl + τc) / (1 + τc)) * (1 - α) / (C / Y * ψ) := by
    have e : L ^ ((1 + γ) / γ) = L * L ^ (1 / γ) := by
      rw [show (1 + γ) / γ = 1 + 1 / γ by rw [add_div, div_self hγ.ne', add_comm],
        Real.rpow_add hL, Real.rpow_one]
    have hl' : L ^ (1 / γ) = μ * (1 - τl) * w / ψ := by rw [← hl]; field_simp
    rw [e, hl', hμ, hw, htax]
    field_simp
  have hpos : 0 < (1 - (τl + τc) / (1 + τc)) * (1 - α) / (C / Y * ψ) := by
    rw [← key]; exact Real.rpow_pos_of_pos hL _
  rw [← key, ← Real.rpow_mul hL.le, show (1 + γ) / γ * (γ / (1 + γ)) = 1 by field_simp,
    Real.rpow_one]

/-- AKMM, p. 354, **the U.S./Italy ratio, corrected**. By (12.39) with common `α, ψ, γ`, hours
in two countries are in the ratio `[((1 − τ₁)/χ₁)/((1 − τ₂)/χ₂)]^{γ/(1+γ)}`. With
`τ = 0.40, 0.64` and `χ = 0.81, 0.69` the base `r = (0.60/0.81)/(0.36/0.69)` lies in
`(1.41, 1.43)`; at `γ = 1` the ratio is `r^{1/2} ∈ (1.19, 1.20)`, not the printed `1.42`, which
is the limit as `γ → ∞`. -/
theorem eq_12_39_us_italy :
    (1.41 : ℝ) < (0.60 / 0.81) / (0.36 / 0.69) ∧ (0.60 / 0.81) / (0.36 / 0.69) < (1.43 : ℝ) ∧
      (1.19 : ℝ) < ((0.60 / 0.81) / (0.36 / 0.69) : ℝ) ^ ((1 : ℝ) / (1 + 1)) ∧
      ((0.60 / 0.81) / (0.36 / 0.69) : ℝ) ^ ((1 : ℝ) / (1 + 1)) < 1.20 ∧
      Tendsto (fun γ : ℝ => ((0.60 / 0.81) / (0.36 / 0.69) : ℝ) ^ (γ / (1 + γ))) atTop
        (𝓝 ((0.60 / 0.81) / (0.36 / 0.69))) := by
  set r : ℝ := (0.60 / 0.81) / (0.36 / 0.69) with hr
  have hr1 : (1.41 : ℝ) < r := by rw [hr]; norm_num
  have hr2 : r < (1.43 : ℝ) := by rw [hr]; norm_num
  have hsq : r ^ ((1 : ℝ) / (1 + 1)) = Real.sqrt r := by
    rw [show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  refine ⟨hr1, hr2, ?_, ?_, ?_⟩
  · rw [hsq, Real.lt_sqrt (by norm_num)]
    rw [hr]; norm_num
  · rw [hsq, Real.sqrt_lt' (by norm_num)]
    rw [hr]; norm_num
  · have hexp : Tendsto (fun γ : ℝ => γ / (1 + γ)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun γ : ℝ => 1 - 1 / (1 + γ)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_left _ _ tendsto_id))
      rw [sub_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with γ hγ
      have : 0 < 1 + γ := by linarith
      field_simp; ring
    have hc := ((continuous_const.rpow continuous_id
      (fun _ => Or.inl (by rw [hr]; norm_num : (0 : ℝ) < r).ne')).tendsto (1 : ℝ)).comp hexp
    simpa [Function.comp_def, Real.rpow_one] using hc

/-! ### Income and substitution effects -/

/-- AKMM, pp. 355–356: in the benchmark the size of the income effect relative to the
substitution effect, `(ε^H − ε^M)/ε^H`, is `σ(1 − s_I)`. -/
theorem ti_effect_ratio {γ σ sI : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) (hs : sI < 1) :
    (1 / (1 / γ + σ * (1 - sI)) - (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI))) /
      (1 / (1 / γ + σ * (1 - sI))) = σ * (1 - sI) := by
  have hden : 0 < 1 / γ + σ * (1 - sI) := by
    have : 0 ≤ σ * (1 - sI) := mul_nonneg hσ (by linarith)
    have : 0 < 1 / γ := by positivity
    linarith
  have e : 1 / (1 / γ + σ * (1 - sI)) - (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) =
      σ * (1 - sI) / (1 / γ + σ * (1 - sI)) := by ring
  rw [e, div_div_div_cancel_right₀ hden.ne', div_one]

/-- AKMM, p. 355, **subsistence consumption**: `log(C − C̄)` with `C = wL` is the benchmark with
`σ = 1` and non-labour income `−C̄`, so `s_I = −C̄/(C − C̄)` and the income/substitution ratio
`σ(1 − s_I) = C/(C − C̄)` exceeds `1`, decreases in `C` and tends to `1` as `C → ∞`. -/
theorem ti_subsistence {Cbar : ℝ} (hCbar : 0 < Cbar) :
    (∀ C, Cbar < C → 1 * (1 - -Cbar / (C - Cbar)) = C / (C - Cbar)) ∧
      (∀ C, Cbar < C → 1 < C / (C - Cbar)) ∧
      StrictAntiOn (fun C => C / (C - Cbar)) (Set.Ioi Cbar) ∧
      Tendsto (fun C => C / (C - Cbar)) atTop (𝓝 1) := by
  refine ⟨fun C hC => ?_, fun C hC => ?_, fun x hx y hy hxy => ?_, ?_⟩
  · have : C - Cbar ≠ 0 := by linarith
    field_simp; ring
  · rw [one_lt_div (by linarith)]; linarith
  · have hx' : 0 < x - Cbar := sub_pos.2 hx
    have hy' : 0 < y - Cbar := sub_pos.2 hy
    simp only
    rw [div_lt_div_iff₀ hy' hx']
    nlinarith
  · have h : Tendsto (fun C => 1 + Cbar * (1 / (C - Cbar))) atTop (𝓝 (1 + Cbar * 0)) :=
      tendsto_const_nhds.add ((tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_id)).const_mul Cbar)
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop Cbar] with C hC
    have : C - Cbar ≠ 0 := by linarith
    field_simp; ring

/-- AKMM, p. 355: with subsistence consumption, **hours fall with the wage**: along `w(s) = we^s`
with (12.1) for `u = log` and income `−C̄` near `0`, `d log L/d log w = −C̄/(C + (C − C̄)/γ) < 0`,
`C = wL`. -/
theorem ti_subsistence_marshallian {ψ γ w Cbar L' : ℝ} {L : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hw : 0 < w) (hCbar : 0 < Cbar) (hL : 0 < L 0) (hc : 0 < w * L 0 + -Cbar)
    (hdL : HasDerivAt L L' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * L s ^ (1 / γ) /
      (w * Real.exp s * L s + -Cbar) ^ (-(1 : ℝ)) = w * Real.exp s) :
    HasDerivAt (fun s => Real.log (L s))
      (-Cbar / (w * L 0 + (w * L 0 - Cbar) / γ)) 0 ∧
      -Cbar / (w * L 0 + (w * L 0 - Cbar) / γ) < 0 := by
  have h := eq_12_3 hψ hγ zero_le_one hw hL hc hdL hfoc
  have hc' : w * L 0 - Cbar ≠ 0 := by linarith
  have hD : 0 < w * L 0 + (w * L 0 - Cbar) / γ := by
    have : 0 < (w * L 0 - Cbar) / γ := div_pos (by linarith) hγ
    have : 0 < w * L 0 := by positivity
    linarith
  refine ⟨h.congr_deriv ?_, div_neg_of_neg_of_pos (by linarith) hD⟩
  rw [div_eq_div_iff (by
    have : 1 - -Cbar / (w * L 0 + -Cbar) = w * L 0 / (w * L 0 - Cbar) := by
      rw [← sub_eq_add_neg]; field_simp; ring
    rw [this]; positivity) hD.ne']
  rw [← sub_eq_add_neg]
  field_simp
  ring

/-- AKMM, p. 355, **`σ > 1`** (Boppart–Krusell): with no non-labour income the
income/substitution ratio is `σ > 1` at every wage; the optimal hours
`ℓ(w) = (w^{1−σ}/ψ)^{1/(1/γ+σ)}` solve (12.1) with `I = 0`, and along wages `Gᵗw₀` hours change
by the constant factor `G^{(1−σ)/(1/γ+σ)} < 1` (`G > 1`): they fall at a constant rate. -/
theorem ti_sigma_gt_one {ψ γ σ G w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 1 < σ) (hG : 1 < G)
    (hw : 0 < w) :
    1 < σ * (1 - 0) ∧
      ψ * ((w ^ (1 - σ) / ψ) ^ (1 / γ + σ)⁻¹) ^ (1 / γ) /
        (w * (w ^ (1 - σ) / ψ) ^ (1 / γ + σ)⁻¹ + 0) ^ (-σ) = w ∧
      ((G * w) ^ (1 - σ) / ψ) ^ (1 / γ + σ)⁻¹ =
        G ^ ((1 - σ) / (1 / γ + σ)) * (w ^ (1 - σ) / ψ) ^ (1 / γ + σ)⁻¹ ∧
      G ^ ((1 - σ) / (1 / γ + σ)) < 1 := by
  have he : 0 < 1 / γ + σ := by have : 0 < 1 / γ := by positivity
                                linarith
  have hk : 0 < w ^ (1 - σ) / ψ := by positivity
  set l := (w ^ (1 - σ) / ψ) ^ (1 / γ + σ)⁻¹
  have hl : 0 < l := Real.rpow_pos_of_pos hk _
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · rw [add_zero, st_foc_form (by positivity), Real.mul_rpow hw.le hl.le]
    have h1 : l ^ (1 / γ) * l ^ σ = w ^ (1 - σ) / ψ := by
      rw [← Real.rpow_add hl, Real.rpow_inv_rpow hk.le he.ne']
    have h3 : w ^ σ * w ^ (1 - σ) = w := by
      rw [← Real.rpow_add hw, show σ + (1 - σ) = 1 by ring, Real.rpow_one]
    calc ψ * l ^ (1 / γ) * (w ^ σ * l ^ σ) = ψ * w ^ σ * (l ^ (1 / γ) * l ^ σ) := by ring
      _ = w := by
        rw [h1]
        have h4 : ψ * w ^ σ * (w ^ (1 - σ) / ψ) = w ^ σ * w ^ (1 - σ) := by field_simp
        rw [h4, h3]
  · have hG0 : 0 < G := by linarith
    rw [Real.mul_rpow hG0.le hw.le, mul_div_assoc, Real.mul_rpow (by positivity) hk.le,
      ← Real.rpow_mul hG0.le, div_eq_mul_inv]
    rfl
  · exact Real.rpow_lt_one_of_one_lt_of_neg hG (div_neg_of_neg_of_pos (by linarith) he)

/-! ### Business cycles -/

/-- AKMM, (12.40), p. 356: when (12.39) holds with a time-varying consumption-output ratio
`χ_t`, `log L_t = const − (γ/(1 + γ)) log(C_t/Y_t)` with
`const = (γ/(1 + γ)) log((1 − τ)(1 − α)/ψ)`. -/
theorem eq_12_40 {ψ γ α τ χ L : ℝ} (hψ : 0 < ψ) (hα : α < 1) (hτ : τ < 1)
    (hχ : 0 < χ) (hL : L = ((1 - τ) * (1 - α) / (χ * ψ)) ^ (γ / (1 + γ))) :
    Real.log L = γ / (1 + γ) * Real.log ((1 - τ) * (1 - α) / ψ) - γ / (1 + γ) * Real.log χ := by
  have h1 : 0 < (1 - τ) * (1 - α) := mul_pos (by linarith) (by linarith)
  rw [hL, Real.log_rpow (by positivity), show (1 - τ) * (1 - α) / (χ * ψ) =
    (1 - τ) * (1 - α) / ψ / χ by field_simp, Real.log_div (by positivity) hχ.ne']
  ring

/-- AKMM, p. 356: the coefficient `γ/(1 + γ)` of (12.40) is `1/2` at `γ = 1` (half the
infinite-elasticity response) and tends to `1` as `γ → ∞` (indivisible labour). -/
theorem ti_cycle_coefficient :
    (1 : ℝ) / (1 + 1) = 1 / 2 ∧ Tendsto (fun γ : ℝ => γ / (1 + γ)) atTop (𝓝 1) := by
  refine ⟨by norm_num, ?_⟩
  have h1 : Tendsto (fun γ : ℝ => 1 - 1 / (1 + γ)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ _ tendsto_id))
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with γ hγ
  have : 0 < 1 + γ := by linarith
  field_simp; ring

/-- AKMM, p. 356, **no capital**: with `Y = ZL` (so `w = Z`) and `C = Y`, the intratemporal
condition `ψL^{1/γ} = (1 − τ)w/C` gives `L = ((1 − τ)/ψ)^{γ/(1+γ)}` for every productivity
`Z > 0`: hours are invariant to productivity. -/
theorem ti_no_capital {ψ γ τ Z L : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hZ : 0 < Z)
    (hL : 0 < L) (hfoc : ψ * L ^ (1 / γ) = (1 - τ) * Z / (Z * L)) :
    L = ((1 - τ) / ψ) ^ (γ / (1 + γ)) := by
  have key : L ^ ((1 + γ) / γ) = (1 - τ) / ψ := by
    rw [show (1 + γ) / γ = 1 + 1 / γ by rw [add_div, div_self hγ.ne', add_comm],
      Real.rpow_add hL, Real.rpow_one]
    have : L ^ (1 / γ) = (1 - τ) / (ψ * L) := by
      rw [eq_div_iff (by positivity)]
      have h2 : ψ * L ^ (1 / γ) = (1 - τ) / L := by rw [hfoc]; field_simp
      rw [show L ^ (1 / γ) * (ψ * L) = ψ * L ^ (1 / γ) * L by ring, h2]
      field_simp
    rw [this]; field_simp
  rw [← key, ← Real.rpow_mul hL.le, show (1 + γ) / γ * (γ / (1 + γ)) = 1 by field_simp,
    Real.rpow_one]

/-! ### Imai–Keane: dynamic returns to work -/

/-- The wage with learning by doing, `w_t = (1 + κΣ_{j<t}ℓ_j)w₀` (AKMM, p. 357). -/
noncomputable def ikWage (κ w₀ : ℝ) (l : ℕ → ℝ) (t : ℕ) : ℝ :=
  (1 + κ * ∑ j ∈ Finset.range t, l j) * w₀

/-- The present value of after-tax earnings `Σ_{t≤T} R^{−t}(1 − τ)w_tℓ_t`. -/
noncomputable def ikEarnings (R τ κ w₀ : ℝ) (T : ℕ) (l : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (T + 1), (R⁻¹) ^ t * ((1 - τ) * ikWage κ w₀ l t * l t)

/-- AKMM, p. 357, **the return to an hour of work**: for `s ≤ T`, the derivative of the present
value of earnings with respect to `ℓ_s` is
`R^{−s}(1 − τ)[w_s + κw₀Σ_{j=1}^{T−s}R^{−j}ℓ_{s+j}]`: the wage plus the human-capital term. -/
theorem ik_marginal_earnings {R τ κ w₀ : ℝ} {T s : ℕ} (hs : s ≤ T) (l : ℕ → ℝ) :
    HasDerivAt (fun x => ikEarnings R τ κ w₀ T (Function.update l s x))
      ((R⁻¹) ^ s * ((1 - τ) * (ikWage κ w₀ l s + κ * w₀ *
        ∑ j ∈ Finset.range (T - s), (R⁻¹) ^ (j + 1) * l (s + j + 1)))) (l s) := by
  classical
  have hu : ∀ j, HasDerivAt (fun x => Function.update l s x j) (if j = s then 1 else 0) (l s) := by
    intro j
    by_cases hj : j = s
    · subst hj
      simp only [Function.update_self, ↓reduceIte]
      exact hasDerivAt_id _
    · simp only [Function.update_of_ne hj, hj, ↓reduceIte]
      exact hasDerivAt_const _ _
  have hw : ∀ t, HasDerivAt (fun x => ikWage κ w₀ (Function.update l s x) t)
      ((κ * ∑ j ∈ Finset.range t, (if j = s then (1 : ℝ) else 0)) * w₀) (l s) := by
    intro t
    have := ((HasDerivAt.fun_sum (u := Finset.range t) (fun j _ => hu j)).const_mul κ).const_add 1
    exact this.mul_const w₀ |>.congr_deriv (by ring)
  have hsum := HasDerivAt.fun_sum (u := Finset.range (T + 1)) (fun t _ =>
    ((((hw t).const_mul (1 - τ)).mul (hu t)).const_mul ((R⁻¹) ^ t)))
  refine hsum.congr_deriv ?_
  simp only [Function.update_eq_self]
  -- split the sum
  have hind : ∀ t, (∑ j ∈ Finset.range t, (if j = s then (1 : ℝ) else 0)) =
      if s < t then 1 else 0 := by
    intro t
    rw [Finset.sum_ite_eq' (Finset.range t) s (fun _ => (1 : ℝ))]
    simp only [Finset.mem_range]
  simp only [hind]
  have hsplit : ∀ t ∈ Finset.range (T + 1),
      (R⁻¹) ^ t * ((1 - τ) * ((κ * (if s < t then (1 : ℝ) else 0)) * w₀) * l t +
        (1 - τ) * ikWage κ w₀ l t * (if t = s then 1 else 0)) =
      (if s < t then (R⁻¹) ^ t * ((1 - τ) * κ * w₀ * l t) else 0) +
        (if t = s then (R⁻¹) ^ t * ((1 - τ) * ikWage κ w₀ l t) else 0) := by
    intro t _
    split_ifs <;> ring
  have hmem : s ∈ Finset.range (T + 1) := Finset.mem_range.2 (by omega)
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range (T + 1)) s]
  simp only [hmem, ↓reduceIte]
  -- reindex the human-capital term
  have hT : T + 1 = (s + 1) + (T - s) := by omega
  rw [hT, Finset.sum_range_add]
  have hzero : ∑ x ∈ Finset.range (s + 1),
      (if s < x then (R⁻¹) ^ x * ((1 - τ) * κ * w₀ * l x) else 0) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      rw [Finset.mem_range] at hx
      have : ¬ s < x := by omega
      simp only [this, ↓reduceIte]
  rw [hzero, zero_add]
  have hterm : ∀ j ∈ Finset.range (T - s),
      (if s < s + 1 + j then (R⁻¹) ^ (s + 1 + j) * ((1 - τ) * κ * w₀ * l (s + 1 + j)) else 0) =
        (R⁻¹) ^ s * ((1 - τ) * κ * w₀) * ((R⁻¹) ^ (j + 1) * l (s + j + 1)) := by
    intro j _
    have h1 : s < s + 1 + j := by omega
    have h2 : (R⁻¹) ^ (s + j + 1) = (R⁻¹) ^ s * (R⁻¹) ^ (j + 1) := by rw [← pow_add, add_assoc]
    simp only [h1, ↓reduceIte]
    rw [show s + 1 + j = s + j + 1 by ring, h2]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/-- AKMM, (12.41), p. 357: with perfect foresight, the lifetime problem's first-order conditions
with multiplier `μ` on the present-value budget, `β^s c_s^{−σ} = μR^{−s}` and
`β^sψℓ_s^{1/γ} = μ·∂(PV earnings)/∂ℓ_s`, give, with `λ_s = c_s^{−σ}`,
`ψℓ_s^{1/γ} = λ_s(1 − τ)[w_s + κw₀Σ_{j=1}^{T−s}R^{−j}ℓ_{s+j}]`. -/
theorem eq_12_41 {R τ κ w₀ β σ ψ γ μ cs D : ℝ} {T s : ℕ} (hs : s ≤ T) (l : ℕ → ℝ)
    (hβ : 0 < β)
    (hD : HasDerivAt (fun x => ikEarnings R τ κ w₀ T (Function.update l s x)) D (l s))
    (hc : β ^ s * cs ^ (-σ) = μ * (R⁻¹) ^ s) (hl : β ^ s * (ψ * l s ^ (1 / γ)) = μ * D) :
    ψ * l s ^ (1 / γ) = cs ^ (-σ) * (1 - τ) * (ikWage κ w₀ l s + κ * w₀ *
      ∑ j ∈ Finset.range (T - s), (R⁻¹) ^ (j + 1) * l (s + j + 1)) := by
  have hD' := hD.unique (ik_marginal_earnings hs l)
  rw [hD'] at hl
  have hβs : 0 < β ^ s := pow_pos hβ s
  apply mul_left_cancel₀ hβs.ne'
  rw [hl]
  have : μ * (R⁻¹) ^ s = β ^ s * cs ^ (-σ) := hc.symm
  linear_combination (1 - τ) * (ikWage κ w₀ l s + κ * w₀ *
      ∑ j ∈ Finset.range (T - s), (R⁻¹) ^ (j + 1) * l (s + j + 1)) * this

end AKMM.LaborSupply

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Indivisible labour, heterogeneity, and intensive and extensive margins

AKMM, §12.8, pp. 359–367.

* **Lotteries** (§12.8.1): with `U = u(c) − ψv(ℓ)`, the lottery objective
  `eU(c, ℓ̄) + (1 − e)U(c, 0) = u(c) − ψ̃e − ψv(0)` with `ψ̃ = ψ(v(ℓ̄) − v(0))` (the book drops
  `ψ`), linear in `e` (`il_lottery`); equal consumption is optimal for concave `u`
  (`il_full_insurance`); an interior `e*` with `u′(Aℓ̄e*)Aℓ̄ = ψ̃` solves the planner's problem
  (`il_planner`). **The aggregate Frisch elasticity is infinite**: with `λ` fixed, employment
  jumps from `0` to `1` at the wage `ψ̃/(λℓ̄)` (`il_frisch_infinite`); at `e* = 1` small wage
  changes leave it unchanged (fn. 16).
* **Decentralisation without lotteries** (§12.8.2, Ljungqvist–Sargent), in a finite version
  with `N` equal periods, no discounting and `r = 0`: pointwise maximisation of the Lagrangian
  with a common multiplier is sufficient (`il_lagrange_suff`); with `u′(c*)Aℓ̄ = ψ̃`, every
  work schedule `e_t ∈ {0, 1}` with `Σe_t = Ne*` and `c_t = c*` is optimal — only the total
  matters, not the timing (`il_ljungqvist_sargent`).
* **Heterogeneous `ψ`** (§12.8.3): `ṽ(e) = ∫₀^{F⁻¹(e)} ψf(ψ)dψ` has `ṽ′(e) = F⁻¹(e)`
  (`il_vtilde_deriv`) and is strictly convex (`il_vtilde_convex`), with the uniform example
  `ṽ(e) = e²/2` (`il_vtilde_uniform`); with `λ` fixed the aggregate Frisch elasticity is
  `xf(x)/F(x)`, `x = λwℓ̄`, determined by the distribution (`il_hetero_frisch`).
* **Intensive and extensive margins** (§12.8.4): (12.44) `ℓ_e = max(0, ℓ − ℓ_f)`; with a
  fixed cost or `ℓ_e = ℓ^θ` (`θ > 1`) splitting hours lowers efficiency units (the 25 + 25
  versus 50 example) (`il_concentrate`), and hours in `(0, ℓ_f]` are dominated by `ℓ = 0`
  (`il_small_hours`). **Rogerson–Wallenius**: for the pointwise problem
  `max_ℓ a·max(0, ℓ − ℓ_f) − ψℓ^{1+1/γ}/(1 + 1/γ)`, `a = μwz`, there is a threshold
  `a* = ψ((1 + γ)ℓ_f)^{1/γ}`: below it `ℓ = 0` is the unique optimum, above it `ℓ = (a/ψ)^γ`
  is, and these hours are increasing in `a` and jump from `0` to `(1 + γ)ℓ_f` at the threshold
  (`il_rw_threshold`); over the life cycle hours are positive exactly when `z(t) > z*`
  (`il_rw_life_cycle`), and with `r = 0` and no discounting pointwise optimality with
  `μ = u′(c)` gives the lifetime optimum (`il_lagrange_suff`).

Departures: the continuous-time problems of §12.8.2 and §12.8.4 are formalised with `N` equal
periods (the book uses continuous time "to avoid the integer constraint"); the
Ljungqvist–Sargent result therefore assumes `Ne*` is an integer.
-/

namespace AKMM.LaborSupply

open Filter Topology

/-! ### Lotteries -/

/-- AKMM, p. 360, **the lottery objective**: with `U = u(c) − ψv(ℓ)`,
`eU(c, ℓ̄) + (1 − e)U(c, 0) = u(c) − ψ̃e − ψv(0)` with `ψ̃ = ψ(v(ℓ̄) − v(0))`, linear in `e`. -/
theorem il_lottery (u v : ℝ → ℝ) (ψ c e lbar : ℝ) :
    e * (u c - ψ * v lbar) + (1 - e) * (u c - ψ * v 0) =
      u c - ψ * (v lbar - v 0) * e - ψ * v 0 := by ring

/-- AKMM, p. 360: with separable utility and concave `u`, giving everyone the same consumption
is optimal: `eu(c₁) + (1 − e)u(c₀) ≤ u(ec₁ + (1 − e)c₀)`. -/
theorem il_full_insurance {u : ℝ → ℝ} {e c₀ c₁ : ℝ} (hu : ConcaveOn ℝ (Set.Ioi 0) u)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    e * u c₁ + (1 - e) * u c₀ ≤ u (e * c₁ + (1 - e) * c₀) := by
  have := hu.2 (Set.mem_Ioi.2 hc₁) (Set.mem_Ioi.2 hc₀) he0 (by linarith : 0 ≤ 1 - e)
    (by ring)
  simpa [smul_eq_mul] using this

/-- AKMM, p. 360, **the planner with indivisible labour**: if `u` has supergradient `μ` at
`c* = Aℓ̄e*` (as a concave differentiable `u` does with `μ = u′(c*)`) and `μAℓ̄ = ψ̃`, then `e*`
maximises `u(Aℓ̄e) − ψ̃e` over `e ∈ (0, 1]`. -/
theorem il_planner {u : ℝ → ℝ} {A lbar ψt μ es : ℝ}
    (hsup : ∀ x, 0 < x → u x ≤ u (A * lbar * es) + μ * (x - A * lbar * es))
    (hfoc : μ * (A * lbar) = ψt) (hpos : 0 < A * lbar) :
    ∀ e, 0 < e → u (A * lbar * e) - ψt * e ≤ u (A * lbar * es) - ψt * es := by
  intro e he
  have := hsup (A * lbar * e) (mul_pos hpos he)
  rw [← hfoc]
  nlinarith

/-- AKMM, p. 361, **the aggregate Frisch elasticity is infinite**: with `λ > 0` fixed, the
aggregate supply problem `max_{e ∈ [0, 1]} (λwℓ̄ − ψ̃)e` has the unique solution `e = 1` when
`w > ψ̃/(λℓ̄)` and `e = 0` when `w < ψ̃/(λℓ̄)`, and every `e` is optimal at the threshold: an
arbitrarily small wage change around it moves employment from `0` to `1`. When `e = 1` is
optimal at `w`, it stays optimal at all nearby wages, so the elasticity is then zero (fn. 16). -/
theorem il_frisch_infinite {lam lbar ψt : ℝ} (hlam : 0 < lam) (hlbar : 0 < lbar) :
    (∀ w, ψt / (lam * lbar) < w → ∀ e, e < 1 →
      (lam * w * lbar - ψt) * e < (lam * w * lbar - ψt) * 1) ∧
    (∀ w, w < ψt / (lam * lbar) → ∀ e, 0 < e →
      (lam * w * lbar - ψt) * e < (lam * w * lbar - ψt) * 0) ∧
    (∀ e, (lam * (ψt / (lam * lbar)) * lbar - ψt) * e = 0) ∧
    (∀ w, ψt / (lam * lbar) < w → ∀ᶠ w' in 𝓝 w, ψt / (lam * lbar) < w') := by
  have hk : 0 < lam * lbar := mul_pos hlam hlbar
  refine ⟨fun w hw e he => ?_, fun w hw e he => ?_, fun e => ?_, fun w hw => lt_mem_nhds hw⟩
  · have : 0 < lam * w * lbar - ψt := by
      rw [div_lt_iff₀ hk] at hw; linarith
    nlinarith
  · have : lam * w * lbar - ψt < 0 := by
      rw [lt_div_iff₀ hk] at hw; linarith
    nlinarith
  · field_simp; ring

/-! ### Decentralisation: Ljungqvist and Sargent -/

/-- AKMM, pp. 361–362 and 366–367, **pointwise maximisation is sufficient** (no discounting,
`r = 0`, `N` periods). Let `u` have supergradient `μ` at `c` (`u(x) ≤ u(c) + μ(x − c)`), let the
plan consume `c` in every period and choose `x_t` with `Nc = Σ_t y_t(x_t)`, and let each `x_t`
maximise `μy_t(x) − d_t(x)` over `S_t`. Then for every plan `(c′, x′)` with `x′_t ∈ S_t` and
`Σc′_t = Σy_t(x′_t)`, `Σ_t [u(c′_t) − d_t(x′_t)] ≤ Σ_t [u(c) − d_t(x_t)]`. -/
theorem il_lagrange_suff {X : Type*} {N : ℕ} {u : ℝ → ℝ} {c μ : ℝ} {y d : Fin N → X → ℝ}
    {S : Fin N → Set X} {x : Fin N → X}
    (hsup : ∀ z, 0 < z → u z ≤ u c + μ * (z - c))
    (hbud : N * c = ∑ t, y t (x t))
    (hpt : ∀ t, ∀ z ∈ S t, μ * y t z - d t z ≤ μ * y t (x t) - d t (x t))
    {c' : Fin N → ℝ} {x' : Fin N → X} (hc' : ∀ t, 0 < c' t) (hx' : ∀ t, x' t ∈ S t)
    (hbud' : ∑ t, c' t = ∑ t, y t (x' t)) :
    ∑ t, (u (c' t) - d t (x' t)) ≤ ∑ t, (u c - d t (x t)) := by
  have h1 : ∑ t, (u (c' t) - d t (x' t)) ≤
      ∑ t, (u c + μ * (c' t - c) - d t (x' t)) :=
    Finset.sum_le_sum fun t _ => by linarith [hsup (c' t) (hc' t)]
  have h2 : ∑ t, (u c + μ * (c' t - c) - d t (x' t)) =
      ∑ _t : Fin N, (u c - μ * c) + ∑ t, (μ * y t (x' t) - d t (x' t)) := by
    rw [← Finset.sum_add_distrib]
    have : ∑ t, μ * (c' t - c) = ∑ t, μ * y t (x' t) - ∑ _t : Fin N, μ * c := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, hbud']
    have e1 : ∑ t, (u c + μ * (c' t - c) - d t (x' t)) =
        ∑ t : Fin N, u c + ∑ t, μ * (c' t - c) - ∑ t, d t (x' t) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    rw [e1, this]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  have h3 : ∑ t, (μ * y t (x' t) - d t (x' t)) ≤ ∑ t, (μ * y t (x t) - d t (x t)) :=
    Finset.sum_le_sum fun t _ => hpt t (x' t) (hx' t)
  have h4 : ∑ _t : Fin N, (u c - μ * c) + ∑ t, (μ * y t (x t) - d t (x t)) =
      ∑ t, (u c - d t (x t)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, ← hbud]
    ring
  linarith

/-- AKMM, p. 362, **Ljungqvist–Sargent: indifference over timing**. With `N` equal periods,
no discounting, `r = 0`, wage `A`, `U(c, eℓ̄) = u(c) − ψv(eℓ̄)`, `e_t ∈ {0, 1}`: if `u` has
supergradient `μ` at `c*` with `μAℓ̄ = ψ(v(ℓ̄) − v(0))` (the planner's condition), then every
schedule `e` with `Nc* = Σ_t e_tℓ̄A` — whatever the timing — together with `c_t = c*` is optimal
among all plans satisfying the lifetime budget `Σc′_t = Σe′_tℓ̄A`. -/
theorem il_ljungqvist_sargent {N : ℕ} {u v : ℝ → ℝ} {ψ A lbar cs μ : ℝ}
    (hsup : ∀ z, 0 < z → u z ≤ u cs + μ * (z - cs))
    (hfoc : μ * (A * lbar) = ψ * (v lbar - v 0)) {e : Fin N → ℝ}
    (he : ∀ t, e t = 0 ∨ e t = 1) (hbud : N * cs = ∑ t, e t * lbar * A)
    {c' e' : Fin N → ℝ} (hc' : ∀ t, 0 < c' t) (he' : ∀ t, e' t = 0 ∨ e' t = 1)
    (hbud' : ∑ t, c' t = ∑ t, e' t * lbar * A) :
    ∑ t, (u (c' t) - ψ * v (e' t * lbar)) ≤ ∑ t, (u cs - ψ * v (e t * lbar)) := by
  refine il_lagrange_suff (S := fun _ => {z : ℝ | z = 0 ∨ z = 1}) (y := fun _ z => z * lbar * A)
    (d := fun _ z => ψ * v (z * lbar)) hsup hbud ?_ hc' he' hbud'
  intro t z hz
  -- `μ·zℓ̄A − ψv(zℓ̄)` is the same for `z = 0` and `z = 1`
  have hval : ∀ z : ℝ, z = 0 ∨ z = 1 → μ * (z * lbar * A) - ψ * v (z * lbar) = -(ψ * v 0) := by
    intro z hz
    rcases hz with rfl | rfl
    · simp only [zero_mul, mul_zero, zero_sub]
    · simp only [one_mul]; linear_combination hfoc
  rw [hval z hz, hval (e t) (he t)]

/-! ### Heterogeneity in the disutility of work -/

/-- AKMM, p. 363, **`ṽ′(e) = F⁻¹(e)`**: let `F` have density `f` (continuous), `Q` a local
inverse of `F` near `e` continuous at `e`, with `f(Q(e)) > 0`. Then
`ṽ(e) = ∫₀^{Q(e)} ψf(ψ)dψ` has derivative `Q(e)` at `e`. -/
theorem il_vtilde_deriv {F f Q : ℝ → ℝ} {e : ℝ} (hf : Continuous f) (hQ : ContinuousAt Q e)
    (hF : HasDerivAt F (f (Q e)) (Q e)) (hfpos : f (Q e) ≠ 0)
    (hFQ : ∀ᶠ y in 𝓝 e, F (Q y) = y) :
    HasDerivAt (fun y => ∫ x in (0 : ℝ)..Q y, x * f x) (Q e) e := by
  have hQd : HasDerivAt Q (f (Q e))⁻¹ e := HasDerivAt.of_local_left_inverse hQ hF hfpos hFQ
  have hI := ((continuous_id.mul hf).integral_hasStrictDerivAt 0 (Q e)).hasDerivAt
  have := hI.comp e hQd
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply, id_eq]
  field_simp

/-- AKMM, p. 363, **`ṽ` is strictly convex**: if on `(0, 1)` `ṽ` has derivative `Q(e)` and `Q`
(the quantile function `F⁻¹`) is strictly increasing, then `ṽ` is strictly convex there. -/
theorem il_vtilde_convex {vt Q : ℝ → ℝ} (hd : ∀ e ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt vt (Q e) e)
    (hQ : StrictMonoOn Q (Set.Ioo 0 1)) : StrictConvexOn ℝ (Set.Ioo 0 1) vt := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioo 0 1)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioo]
    intro x hx y hy hxy
    rw [(hd x hx).deriv, (hd y hy).deriv]
    exact hQ hx hy hxy

/-- AKMM, p. 363: the uniform distribution on `[0, 1]` (`F = f·id`, `f ≡ 1`, `Q = id`)
satisfies the hypotheses of `il_vtilde_deriv`, and `ṽ(e) = e²/2`, strictly convex. -/
theorem il_vtilde_uniform (e : ℝ) :
    HasDerivAt (fun y => ∫ x in (0 : ℝ)..id y, x * (fun _ => (1 : ℝ)) x) (id e) e ∧
      (∫ x in (0 : ℝ)..e, x * (fun _ => (1 : ℝ)) x) = e ^ 2 / 2 ∧
      StrictConvexOn ℝ (Set.Ioo 0 1) (fun y => ∫ x in (0 : ℝ)..id y, x * (fun _ => (1 : ℝ)) x) := by
  have hd : ∀ e, HasDerivAt (fun y => ∫ x in (0 : ℝ)..id y, x * (fun _ => (1 : ℝ)) x) (id e) e :=
    fun e => il_vtilde_deriv (F := id) continuous_const continuousAt_id
      (by simpa using hasDerivAt_id (id e)) one_ne_zero (Eventually.of_forall fun _ => rfl)
  refine ⟨hd e, by simp [integral_id], ?_⟩
  exact il_vtilde_convex (fun e _ => hd e) (strictMono_id.strictMonoOn _)

/-- AKMM, p. 363: **the aggregate Frisch elasticity with heterogeneity** is finite and set by
the distribution: with `λ` fixed, the planner employs everyone with `ψ < λwℓ̄`, so `e = F(λwℓ̄)`,
and along `w(s) = we^s`, `d log e/d log w = xf(x)/F(x)`, `x = λwℓ̄`. -/
theorem il_hetero_frisch {F f : ℝ → ℝ} {lam w lbar : ℝ}
    (hF : HasDerivAt F (f (lam * w * lbar)) (lam * w * lbar)) (hFpos : 0 < F (lam * w * lbar)) :
    HasDerivAt (fun s => Real.log (F (lam * (w * Real.exp s) * lbar)))
      (lam * w * lbar * f (lam * w * lbar) / F (lam * w * lbar)) 0 := by
  have hin : HasDerivAt (fun s => lam * (w * Real.exp s) * lbar) (lam * w * lbar) 0 := by
    have := ((st_exp_path w).const_mul lam).mul_const lbar
    exact this.congr_deriv (by ring)
  have h0 : lam * (w * Real.exp 0) * lbar = lam * w * lbar := by rw [Real.exp_zero, mul_one]
  have hF' : HasDerivAt F (f (lam * w * lbar)) (lam * (w * Real.exp 0) * lbar) := by
    rw [h0]; exact hF
  have hFpos' : (F ∘ fun s => lam * (w * Real.exp s) * lbar) 0 ≠ 0 := by
    simp only [Function.comp_apply, h0]; exact hFpos.ne'
  have := (hF'.comp 0 hin).log hFpos'
  refine this.congr_deriv ?_
  simp only [Function.comp_apply, h0]
  ring

/-! ### Intensive and extensive margins -/

/-- AKMM, (12.44), p. 365: efficiency units with a fixed time cost, `max(0, ℓ − ℓ_f)`. -/
noncomputable def effHours (lf l : ℝ) : ℝ := max 0 (l - lf)

/-- AKMM, pp. 365–366, **concentrating hours**: with a fixed cost `ℓ_f > 0`, splitting `ℓ > ℓ_f`
into two halves gives fewer efficiency units; with `ℓ_e = ℓ^θ`, `θ > 1`, so does any split
`2(ℓ/2)^θ < ℓ^θ`, e.g. `2·25^θ < 50^θ`. -/
theorem il_concentrate {lf l θ : ℝ} (hlf : 0 < lf) (hl : lf < l) (hθ : 1 < θ) :
    2 * effHours lf (l / 2) < effHours lf l ∧ 2 * (l / 2) ^ θ < l ^ θ ∧
      2 * (25 : ℝ) ^ θ < (50 : ℝ) ^ θ := by
  have hpow : ∀ x : ℝ, 0 < x → 2 * (x / 2) ^ θ < x ^ θ := by
    intro x hx
    rw [Real.div_rpow hx.le (by norm_num)]
    have h2 : (2 : ℝ) < 2 ^ θ := by
      have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hθ
      simpa using this
    have hxp : 0 < x ^ θ := Real.rpow_pos_of_pos hx _
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨?_, hpow l (by linarith), ?_⟩
  · unfold effHours
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ l - lf)]
    rcases le_or_gt (l / 2 - lf) 0 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h.le]; linarith
  · have := hpow 50 (by norm_num)
    norm_num at this ⊢
    exact this

/-- AKMM, pp. 365–366: with a fixed cost, hours `ℓ ∈ (0, ℓ_f]` produce no efficiency units and
are strictly worse than not working, for strictly increasing disutility `v`. -/
theorem il_small_hours {u v : ℝ → ℝ} {I w z lf l : ℝ} (hv : StrictMono v) (hl0 : 0 < l)
    (hl : l ≤ lf) : u (I + w * z * effHours lf l) - v l < u (I + w * z * effHours lf 0) - v 0 := by
  unfold effHours
  rw [max_eq_left (by linarith : l - lf ≤ 0), max_eq_left (by linarith : (0 : ℝ) - lf ≤ 0)]
  have := hv hl0
  linarith

/-- AKMM, p. 366–367, **the Rogerson–Wallenius threshold**. For the pointwise problem
`J(a, ℓ) = a·max(0, ℓ − ℓ_f) − ψℓ^{1+1/γ}/(1 + 1/γ)` (`a = μwz > 0`), with
`a* = ψ((1 + γ)ℓ_f)^{1/γ}`: if `a < a*`, `ℓ = 0` is the unique maximiser over `ℓ ≥ 0`; if
`a > a*`, `ℓ(a) = (a/ψ)^γ > ℓ_f` is; and `ℓ(a*) = (1 + γ)ℓ_f`, so hours jump at the threshold
(extensive margin) and increase with `a` above it (intensive margin). -/
theorem il_rw_threshold {ψ γ lf a : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hlf : 0 < lf) (ha : 0 < a) :
    (a < ψ * ((1 + γ) * lf) ^ (1 / γ) → ∀ l, 0 < l →
      a * effHours lf l - disutil ψ γ l < a * effHours lf 0 - disutil ψ γ 0) ∧
    (ψ * ((1 + γ) * lf) ^ (1 / γ) < a → lf < (a / ψ) ^ γ ∧ ∀ l, 0 ≤ l → l ≠ (a / ψ) ^ γ →
      a * effHours lf l - disutil ψ γ l < a * effHours lf ((a / ψ) ^ γ) -
        disutil ψ γ ((a / ψ) ^ γ)) ∧
    ((ψ * ((1 + γ) * lf) ^ (1 / γ) / ψ) ^ γ = (1 + γ) * lf) ∧
    StrictMonoOn (fun a => (a / ψ) ^ γ) (Set.Ioi 0) := by
  set la := (a / ψ) ^ γ with hla
  have hk : 0 < a / ψ := by positivity
  have hlapos : 0 < la := Real.rpow_pos_of_pos hk _
  obtain ⟨hfoc, hval⟩ := fr_opt_facts hψ hγ ha
  rw [← hla] at hfoc hval
  have hγ' : 0 < 1 / γ := by positivity
  have hd0 : disutil ψ γ 0 = 0 := by
    unfold disutil
    have hp0 : (1 + 1 / γ) ≠ 0 := by positivity
    rw [Real.zero_rpow hp0]
    simp
  have heff0 : effHours lf 0 = 0 := by unfold effHours; simp; linarith
  have hdpos : ∀ l, 0 < l → 0 < disutil ψ γ l := fun l hl => by
    unfold disutil; have : 0 < 1 + 1 / γ := by positivity
    have := Real.rpow_pos_of_pos hl (1 + 1 / γ); positivity
  -- the tangent inequality: `v(ℓ) ≥ v(ℓ_a) + a(ℓ − ℓ_a)`, strict for `ℓ ≠ ℓ_a`
  have htan : ∀ l, 0 ≤ l → l ≠ la → disutil ψ γ la + a * (l - la) < disutil ψ γ l := by
    intro l hl hne
    have hp : 1 < 1 + 1 / γ := by linarith
    have ht := fr_rpow_tangent hp hl hlapos hne
    rw [show 1 + 1 / γ - 1 = 1 / γ by ring] at ht
    unfold disutil
    have hg : 0 < 1 + 1 / γ := by linarith
    rw [div_add' _ _ _ hg.ne', div_lt_div_iff_of_pos_right hg, ← hfoc]
    nlinarith [mul_lt_mul_of_pos_left ht hψ]
  -- the value of working: `W(a) = aℓ_a/(1 + γ) − aℓ_f`
  have hW : a * (la - lf) - disutil ψ γ la = a * la / (1 + γ) - a * lf := by linarith
  -- `ℓ_a > (1 + γ)ℓ_f` iff `a > a*`
  have hthr : ∀ b, 0 < b → (ψ * ((1 + γ) * lf) ^ (1 / γ) < b ↔ (1 + γ) * lf < (b / ψ) ^ γ) := by
    intro b hb
    have hq : 0 < (1 + γ) * lf := by positivity
    constructor
    · intro h
      have h1 : ((1 + γ) * lf) ^ (1 / γ) < b / ψ := by rw [lt_div_iff₀ hψ]; linarith
      have := Real.rpow_lt_rpow (Real.rpow_nonneg hq.le _) h1 hγ
      rwa [← Real.rpow_mul hq.le, one_div_mul_cancel hγ.ne', Real.rpow_one] at this
    · intro h
      have := Real.rpow_lt_rpow hq.le h (by positivity : 0 < 1 / γ)
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hγ.ne', Real.rpow_one,
        lt_div_iff₀ hψ] at this
      linarith
  refine ⟨fun hlow l hl => ?_, fun hhigh => ?_, ?_, ?_⟩
  · rw [heff0, hd0, mul_zero, sub_zero]
    rcases le_or_gt l lf with h | h
    · unfold effHours; rw [max_eq_left (by linarith)]
      simp only [mul_zero, zero_sub, neg_lt_zero]; exact hdpos l hl
    · unfold effHours; rw [max_eq_right (by linarith)]
      have hla' : la ≤ (1 + γ) * lf := by
        by_contra hc; exact absurd ((hthr a ha).2 (not_le.1 hc)) (not_lt.2 hlow.le)
      have hWneg : a * la / (1 + γ) - a * lf ≤ 0 := by
        rw [div_sub' (by positivity), div_nonpos_iff]
        right; constructor <;> nlinarith
      rcases eq_or_ne l la with heq | hne
      · rw [heq]
        have : a * la / (1 + γ) - a * lf < 0 ∨ a * la / (1 + γ) - a * lf = 0 :=
          lt_or_eq_of_le hWneg
        rcases this with h' | h'
        · linarith
        · -- `W(a) = 0` means `ℓ_a = (1 + γ)ℓ_f`, i.e. `a = a*`, excluded
          exfalso
          have : la = (1 + γ) * lf := by
            have hγ1 : (0 : ℝ) < 1 + γ := by linarith
            field_simp at h'
            nlinarith
          have hle := (hthr a ha).1
          have : ψ * ((1 + γ) * lf) ^ (1 / γ) = a := by
            rw [← this, hla, ← Real.rpow_mul hk.le, mul_one_div_cancel hγ.ne', Real.rpow_one]
            field_simp
          linarith
      · have := htan l hl.le hne
        linarith
  · have hla_gt : (1 + γ) * lf < la := (hthr a ha).1 hhigh
    have hlf : lf < la := by nlinarith
    refine ⟨hlf, fun l hl hne => ?_⟩
    have heffa : effHours lf la = la - lf := by unfold effHours; rw [max_eq_right (by linarith)]
    rw [heffa, hW]
    have hWpos : 0 < a * la / (1 + γ) - a * lf := by
      rw [div_sub' (by positivity)]
      apply div_pos _ (by positivity)
      nlinarith
    rcases le_or_gt l lf with h | h
    · unfold effHours; rw [max_eq_left (by linarith)]
      rcases eq_or_lt_of_le hl with h0 | h0
      · rw [← h0, hd0]; linarith
      · have := hdpos l h0; linarith
    · unfold effHours; rw [max_eq_right (by linarith)]
      have := htan l hl hne
      linarith
  · have hq : 0 < (1 + γ) * lf := by positivity
    rw [mul_div_cancel_left₀ _ hψ.ne', ← Real.rpow_mul hq.le, one_div_mul_cancel hγ.ne',
      Real.rpow_one]
  · intro x hx y hy hxy
    exact Real.rpow_lt_rpow (div_pos hx hψ).le (div_lt_div_of_pos_right hxy hψ) hγ

/-- AKMM, pp. 366–367, **the life-cycle profile** of Rogerson–Wallenius: with productivity
`z(t) ≥ 0`, multiplier `μ > 0` and wage `w > 0`, put `z* = a*/(μw)`. At every date with
`z(t) < z*` the unique optimal hours are `0`; at every date with `z(t) > z*` they are
`(μwz(t)/ψ)^γ > ℓ_f`, increasing in `z(t)`. In particular hours are zero at `t = 0` and `t = T`
when `z(0) = z(T) = 0`. -/
theorem il_rw_life_cycle {ψ γ lf μ w : ℝ} {z : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hlf : 0 < lf)
    (hμ : 0 < μ) (hw : 0 < w) (t : ℝ) (hz : 0 < z t) :
    (z t < ψ * ((1 + γ) * lf) ^ (1 / γ) / (μ * w) → ∀ l, 0 < l →
      μ * w * z t * effHours lf l - disutil ψ γ l < μ * w * z t * effHours lf 0 - disutil ψ γ 0) ∧
    (ψ * ((1 + γ) * lf) ^ (1 / γ) / (μ * w) < z t → lf < (μ * w * z t / ψ) ^ γ ∧
      ∀ l, 0 ≤ l → l ≠ (μ * w * z t / ψ) ^ γ →
        μ * w * z t * effHours lf l - disutil ψ γ l <
          μ * w * z t * effHours lf ((μ * w * z t / ψ) ^ γ) -
            disutil ψ γ ((μ * w * z t / ψ) ^ γ)) := by
  have hmw : 0 < μ * w := mul_pos hμ hw
  have ha : 0 < μ * w * z t := mul_pos hmw hz
  obtain ⟨h1, h2, -, -⟩ := il_rw_threshold hψ hγ hlf ha
  refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
  · rw [lt_div_iff₀ hmw] at h; linarith
  · rw [div_lt_iff₀ hmw] at h; linarith

end AKMM.LaborSupply

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Life-cycle profiles in the Imai–Keane model (Figure 12.6)

AKMM, §12.7, pp. 357–358, Figure 12.6. The model is the one of p. 357 with perfect foresight:
the wage `w_t = (1 + κΣ_{j<t}ℓ_j)w₀` (`ikWage`), the human-capital term
`H_t = κw₀Σ_{j=1}^{T−t}R^{−j}ℓ_{t+j}` (`ikfHC`) and the return to work `w_t + H_t`
(`ikfReturn`), linked to hours by (12.41), `ψℓ_t^{1/γ} = λ_t(1 − τ)(w_t + H_t)` (`eq_12_41`),
and the Euler equation `λ_t = βRλ_{t+1}`.

* **Backward induction for the human-capital term**: `H_T = 0` and
  `H_t = R^{−1}(κw₀ℓ_{t+1} + H_{t+1})` (`ikf_hc_last`, `ikf_hc_succ`); hence
  `H_t − H_{t+1} = R^{−1}(κw₀ℓ_{t+1} − (R − 1)H_{t+1})` (`ikf_hc_diff`). The wage rises by
  `κw₀ℓ_t` each period and never falls (`ikf_wage_succ`, `ikf_wage_step`); the return to work
  exceeds the wage before `T` and equals it at `T` (`ikf_return_vs_wage`).
* **"The human capital term … declines with age"** (p. 358): true for every hours path when
  `R ≤ 1` (`ikf_hc_antitone`, strict steps `ikf_hc_step_le_one`); for any `R > 0` at every age
  from which future hours do not exceed next period's (the declining phase of hours,
  `ikf_hc_step_peak`), and for constant hours, which is the text's argument "as clear from the
  sum" (`ikf_hc_const_hours`). It is **not** true in general when `R > 1`: in an explicit
  three-period economy (`R = 10`, `β = 1/10`, `σ = 2`, `γ = ψ = κ = w₀ = 1`, `τ = 0`) the
  optimum, proved globally optimal, has `H₀ < H₁` (`ikf_hc_rises`).
* **Hours profiles**: along any interior path satisfying (12.41) and the Euler equation, hours
  are nondecreasing when `R ≥ 1` and `βR ≤ 1`, strictly increasing if moreover `R > 1` or
  `βR < 1` (`ikf_hours_up`, `ikf_hours_up_strict`); nonincreasing when `R ≤ 1` and `βR ≥ 1`,
  strictly if `R < 1` or `βR > 1` (`ikf_hours_down`, `ikf_hours_down_strict`). At `R = β = 1`
  hours and the return to work are constant, the wage rises linearly and the human-capital term
  falls linearly to zero (`ikf_flat`): exactly "hours relatively flat while wages grow steeply"
  with a flat return to work, and a naive regression of hours on current wages recovers an
  elasticity of zero (`ikf_naive_gamma`, `ikf_flat_naive`). Instances: `ikf_instance_up`,
  `ikf_instance_down`, `ikf_instance_flat`.

Departures: the hump in hours and the fall of the wage late in life in Figure 12.6 are not
features of the model of p. 357 (the wage never falls; hours are monotone whenever `R − 1` and
`1 − βR` have the same weak sign); they are calibrated features of the plotted curves.
-/

namespace AKMM.LaborSupply

/-- The human-capital term of (12.41), `H_t = κw₀Σ_{j=1}^{T−t}R^{−j}ℓ_{t+j}` (AKMM, p. 357). -/
noncomputable def ikfHC (R κ w₀ : ℝ) (T : ℕ) (l : ℕ → ℝ) (t : ℕ) : ℝ :=
  κ * w₀ * ∑ j ∈ Finset.range (T - t), (R⁻¹) ^ (j + 1) * l (t + j + 1)

/-- The return to work, wage plus human-capital term (AKMM, p. 357, Figure 12.6). -/
noncomputable def ikfReturn (R κ w₀ : ℝ) (T : ℕ) (l : ℕ → ℝ) (t : ℕ) : ℝ :=
  ikWage κ w₀ l t + ikfHC R κ w₀ T l t

/-- AKMM, p. 358, Figure 12.6: the human-capital term is zero in the last period (and after). -/
theorem ikf_hc_last (R κ w₀ : ℝ) {T t : ℕ} (l : ℕ → ℝ) (ht : T ≤ t) :
    ikfHC R κ w₀ T l t = 0 := by
  unfold ikfHC
  rw [Nat.sub_eq_zero_of_le ht, Finset.sum_range_zero, mul_zero]

/-- AKMM, p. 358 (backward induction for (12.41)): for `t < T`,
`H_t = R^{−1}(κw₀ℓ_{t+1} + H_{t+1})`. -/
theorem ikf_hc_succ (R κ w₀ : ℝ) {T t : ℕ} (l : ℕ → ℝ) (ht : t < T) :
    ikfHC R κ w₀ T l t = R⁻¹ * (κ * w₀ * l (t + 1) + ikfHC R κ w₀ T l (t + 1)) := by
  unfold ikfHC
  rw [show T - t = (T - (t + 1)) + 1 by omega, Finset.sum_range_succ']
  have hs : ∀ j ∈ Finset.range (T - (t + 1)), (R⁻¹) ^ (j + 1 + 1) * l (t + (j + 1) + 1) =
      R⁻¹ * ((R⁻¹) ^ (j + 1) * l (t + 1 + j + 1)) := by
    intro j _
    rw [show t + (j + 1) + 1 = t + 1 + j + 1 by ring]
    ring
  rw [Finset.sum_congr rfl hs, ← Finset.mul_sum]
  simp only [zero_add, pow_one, add_zero]
  ring

/-- AKMM, p. 358: the one-period change of the human-capital term,
`H_t − H_{t+1} = R^{−1}(κw₀ℓ_{t+1} − (R − 1)H_{t+1})` for `t < T`, `R ≠ 0`. -/
theorem ikf_hc_diff {R : ℝ} (κ w₀ : ℝ) {T t : ℕ} (l : ℕ → ℝ) (hR : R ≠ 0) (ht : t < T) :
    ikfHC R κ w₀ T l t - ikfHC R κ w₀ T l (t + 1) =
      R⁻¹ * (κ * w₀ * l (t + 1) - (R - 1) * ikfHC R κ w₀ T l (t + 1)) := by
  rw [ikf_hc_succ R κ w₀ l ht]
  field_simp
  ring

/-- AKMM, p. 357: the wage rises by `κw₀ℓ_t`, `w_{t+1} = w_t + κw₀ℓ_t`. -/
theorem ikf_wage_succ (κ w₀ : ℝ) (l : ℕ → ℝ) (t : ℕ) :
    ikWage κ w₀ l (t + 1) = ikWage κ w₀ l t + κ * w₀ * l t := by
  unfold ikWage
  rw [Finset.sum_range_succ]
  ring

/-- AKMM, p. 357, Figure 12.6: with `κw₀ ≥ 0` and `ℓ_t ≥ 0` the wage never falls, and it
rises strictly when `κw₀ > 0` and `ℓ_t > 0`. -/
theorem ikf_wage_step {κ w₀ : ℝ} {l : ℕ → ℝ} {t : ℕ} (hκ : 0 ≤ κ * w₀) (hl : 0 ≤ l t) :
    ikWage κ w₀ l t ≤ ikWage κ w₀ l (t + 1) ∧
      (0 < κ * w₀ → 0 < l t → ikWage κ w₀ l t < ikWage κ w₀ l (t + 1)) := by
  rw [ikf_wage_succ]
  exact ⟨by nlinarith, fun h1 h2 => by nlinarith⟩

/-- AKMM, p. 358: the human-capital term is nonnegative when `R > 0`, `κw₀ ≥ 0` and hours are
nonnegative up to `T`. -/
theorem ikf_hc_nonneg {R κ w₀ : ℝ} {T : ℕ} {l : ℕ → ℝ} (hR : 0 < R) (hκ : 0 ≤ κ * w₀)
    (hl : ∀ s ≤ T, 0 ≤ l s) (t : ℕ) : 0 ≤ ikfHC R κ w₀ T l t := by
  unfold ikfHC
  refine mul_nonneg hκ (Finset.sum_nonneg fun j hj => ?_)
  rw [Finset.mem_range] at hj
  exact mul_nonneg (pow_nonneg (inv_nonneg.2 hR.le) _) (hl _ (by omega))

/-- AKMM, p. 357, Figure 12.6: the return to work equals the wage in the last period, and
exceeds it before when `κw₀ > 0` and next period's hours are positive. -/
theorem ikf_return_vs_wage {R κ w₀ : ℝ} {T : ℕ} {l : ℕ → ℝ} (hR : 0 < R) (hκ : 0 < κ * w₀)
    (hl : ∀ s ≤ T, 0 ≤ l s) :
    ikfReturn R κ w₀ T l T = ikWage κ w₀ l T ∧
      ∀ t < T, 0 < l (t + 1) → ikWage κ w₀ l t < ikfReturn R κ w₀ T l t := by
  refine ⟨by rw [ikfReturn, ikf_hc_last R κ w₀ l le_rfl, add_zero], fun t ht hpos => ?_⟩
  rw [ikfReturn, ikf_hc_succ R κ w₀ l ht]
  have h0 := ikf_hc_nonneg hR hκ.le hl (t + 1)
  have : 0 < R⁻¹ * (κ * w₀ * l (t + 1) + ikfHC R κ w₀ T l (t + 1)) :=
    mul_pos (inv_pos.2 hR) (by nlinarith)
  linarith

/-- AKMM, p. 358, "the human capital term is high early on, but it declines with age", one step,
for `0 < R ≤ 1`: `H_{t+1} ≤ H_t`, strictly when `κw₀ > 0` and `ℓ_{t+1} > 0`. -/
theorem ikf_hc_step_le_one {R κ w₀ : ℝ} {T t : ℕ} {l : ℕ → ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hκ : 0 ≤ κ * w₀) (hl : ∀ s ≤ T, 0 ≤ l s) (ht : t < T) :
    ikfHC R κ w₀ T l (t + 1) ≤ ikfHC R κ w₀ T l t ∧
      (0 < κ * w₀ → 0 < l (t + 1) → ikfHC R κ w₀ T l (t + 1) < ikfHC R κ w₀ T l t) := by
  have hd := ikf_hc_diff κ w₀ l hR.ne' ht
  have hH := ikf_hc_nonneg hR hκ hl (t + 1)
  have hlt := hl (t + 1) (by omega)
  have hRi : 0 < R⁻¹ := inv_pos.2 hR
  have hA : 0 ≤ κ * w₀ * l (t + 1) - (R - 1) * ikfHC R κ w₀ T l (t + 1) := by nlinarith
  refine ⟨by nlinarith [mul_nonneg hRi.le hA], fun h1 h2 => ?_⟩
  have hA' : 0 < κ * w₀ * l (t + 1) - (R - 1) * ikfHC R κ w₀ T l (t + 1) := by nlinarith
  nlinarith [mul_pos hRi hA']

/-- AKMM, p. 358, "the human capital term … declines with age": for `0 < R ≤ 1`, `κw₀ ≥ 0` and
nonnegative hours, the human-capital term is antitone in age over the whole life cycle. -/
theorem ikf_hc_antitone {R κ w₀ : ℝ} {T : ℕ} {l : ℕ → ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hκ : 0 ≤ κ * w₀) (hl : ∀ s ≤ T, 0 ≤ l s) : Antitone (ikfHC R κ w₀ T l) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rcases lt_or_ge n T with hn | hn
  · exact (ikf_hc_step_le_one hR hR1 hκ hl hn).1
  · rw [ikf_hc_last R κ w₀ l (by omega)]
    exact ikf_hc_nonneg hR hκ hl n

/-- The geometric identity `(R − 1)Σ_{j<n}R^{−(j+1)} = 1 − R^{−n}` used for the human-capital
term (AKMM, p. 358). -/
theorem ikf_geom {R : ℝ} (hR : R ≠ 0) (n : ℕ) :
    (R - 1) * ∑ j ∈ Finset.range n, (R⁻¹) ^ (j + 1) = 1 - (R⁻¹) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have : R * (R⁻¹) ^ (n + 1) = (R⁻¹) ^ n := by
      rw [pow_succ]; field_simp
    linear_combination this

/-- AKMM, p. 358, the decline of the human-capital term for any `R > 0`, in the declining phase
of hours: if no hours after `t + 1` exceed `ℓ_{t+1}`, then `H_{t+1} ≤ H_t`, strictly when
`κw₀ > 0` and `ℓ_{t+1} > 0`. (For `R ≤ 1` no condition is needed: `ikf_hc_step_le_one`.) -/
theorem ikf_hc_step_peak {R κ w₀ : ℝ} {T t : ℕ} {l : ℕ → ℝ} (hR : 0 < R) (hκ : 0 ≤ κ * w₀)
    (hl : ∀ s ≤ T, 0 ≤ l s) (ht : t < T) (hpeak : ∀ s, t + 1 < s → s ≤ T → l s ≤ l (t + 1)) :
    ikfHC R κ w₀ T l (t + 1) ≤ ikfHC R κ w₀ T l t ∧
      (0 < κ * w₀ → 0 < l (t + 1) → ikfHC R κ w₀ T l (t + 1) < ikfHC R κ w₀ T l t) := by
  rcases le_total R 1 with hR1 | hR1
  · exact ikf_hc_step_le_one hR hR1 hκ hl ht
  have hd := ikf_hc_diff κ w₀ l hR.ne' ht
  have hRi : 0 < R⁻¹ := inv_pos.2 hR
  set n := T - (t + 1) with hn
  have hbound : ikfHC R κ w₀ T l (t + 1) ≤
      κ * w₀ * (l (t + 1) * ∑ j ∈ Finset.range n, (R⁻¹) ^ (j + 1)) := by
    unfold ikfHC
    refine mul_le_mul_of_nonneg_left ?_ hκ
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_range] at hj
    have h1 := hpeak (t + 1 + j + 1) (by omega) (by omega)
    have h2 : 0 ≤ (R⁻¹) ^ (j + 1) := pow_nonneg hRi.le _
    nlinarith
  have hg := ikf_geom hR.ne' n
  have hpow : 0 < (R⁻¹) ^ n := pow_pos hRi n
  have hlt := hl (t + 1) (by omega)
  -- `(R − 1)H_{t+1} ≤ κw₀ℓ_{t+1}(1 − R^{−n})`
  have hkey : (R - 1) * ikfHC R κ w₀ T l (t + 1) ≤
      κ * w₀ * l (t + 1) * (1 - (R⁻¹) ^ n) := by
    have := mul_le_mul_of_nonneg_left hbound (by linarith : (0 : ℝ) ≤ R - 1)
    rw [← hg] at *
    nlinarith
  have hA : κ * w₀ * l (t + 1) * (R⁻¹) ^ n ≤
      κ * w₀ * l (t + 1) - (R - 1) * ikfHC R κ w₀ T l (t + 1) := by nlinarith
  refine ⟨?_, fun h1 h2 => ?_⟩
  · have : 0 ≤ κ * w₀ * l (t + 1) * (R⁻¹) ^ n := mul_nonneg (mul_nonneg hκ hlt) hpow.le
    nlinarith [mul_nonneg hRi.le (le_trans this hA)]
  · have : 0 < κ * w₀ * l (t + 1) * (R⁻¹) ^ n := mul_pos (mul_pos h1 h2) hpow
    nlinarith [mul_pos hRi (lt_of_lt_of_le this hA)]

/-- AKMM, p. 358, "the return to working more in order to increase future wages is larger when
the individual is young … as clear from the sum in equation (12.41)": with constant positive
hours and `κw₀ > 0`, the human-capital term strictly decreases every period, for every `R > 0`.
-/
theorem ikf_hc_const_hours {R κ w₀ ℓ : ℝ} {T t : ℕ} {l : ℕ → ℝ} (hR : 0 < R)
    (hκ : 0 < κ * w₀) (hℓ : 0 < ℓ) (hl : ∀ s ≤ T, l s = ℓ) (ht : t < T) :
    ikfHC R κ w₀ T l (t + 1) < ikfHC R κ w₀ T l t := by
  have hl0 : ∀ s ≤ T, 0 ≤ l s := fun s hs => (hl s hs).symm ▸ hℓ.le
  refine (ikf_hc_step_peak hR hκ.le hl0 ht fun s _ hs => ?_).2 hκ ?_
  · rw [hl s hs, hl (t + 1) (by omega)]
  · rw [hl (t + 1) (by omega)]; exact hℓ

/-- AKMM, (12.41), p. 357: along an interior path satisfying (12.41), the return to work is
positive at every age `s ≤ T` (when `ψ > 0`, `τ < 1`, `λ_s > 0`, `ℓ_s > 0`). -/
theorem ikf_return_pos {R κ w₀ ψ γ τ : ℝ} {T : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ) (hτ : τ < 1)
    (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn R κ w₀ T l s)
    {s : ℕ} (hs : s ≤ T) : 0 < ikfReturn R κ w₀ T l s := by
  have h1 : 0 < ψ * l s ^ (1 / γ) := mul_pos hψ (Real.rpow_pos_of_pos (hl s hs) _)
  rw [hfoc s hs] at h1
  exact pos_of_mul_pos_right h1 (mul_pos (hlam s hs) (by linarith)).le

/-- AKMM, p. 358, Figure 12.6, hours over the life cycle: along any interior path satisfying
(12.41) and the Euler equation `λ_t = βRλ_{t+1}`, if `R ≥ 1` and `βR ≤ 1`, hours never fall:
`ℓ_t ≤ ℓ_{t+1}`. -/
theorem ikf_hours_up {R β κ w₀ ψ γ τ : ℝ} {T t : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ)
    (hγ : 0 < γ) (hτ : τ < 1) (hR1 : 1 ≤ R) (hβR : β * R ≤ 1) (hκ : 0 ≤ κ * w₀)
    (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (heul : ∀ s < T, lam s = β * R * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn R κ w₀ T l s)
    (ht : t < T) : l t ≤ l (t + 1) := by
  refine le_of_not_gt fun h => ?_
  have hR : 0 < R := by linarith
  have h1 := Real.rpow_lt_rpow (hl (t + 1) (by omega)).le h (by positivity : 0 < 1 / γ)
  have hf0 := hfoc t ht.le
  have hf1 := hfoc (t + 1) ht
  have hτ' : 0 < 1 - τ := by linarith
  have hQ0 := ikf_return_pos hψ hτ hl hlam hfoc ht.le
  have hl1 := hlam (t + 1) ht
  have hlt : lam t ≤ lam (t + 1) := by rw [heul t ht]; nlinarith
  -- `λ_{t+1}Q_{t+1} < λ_tQ_t ≤ λ_{t+1}Q_t`
  have hA : lam (t + 1) * ikfReturn R κ w₀ T l (t + 1) < lam t * ikfReturn R κ w₀ T l t := by
    have : lam (t + 1) * (1 - τ) * ikfReturn R κ w₀ T l (t + 1) <
        lam t * (1 - τ) * ikfReturn R κ w₀ T l t := by nlinarith
    nlinarith
  have hQ : ikfReturn R κ w₀ T l (t + 1) < ikfReturn R κ w₀ T l t := by nlinarith
  have hD : ikfReturn R κ w₀ T l (t + 1) - ikfReturn R κ w₀ T l t =
      κ * w₀ * (l t - R⁻¹ * l (t + 1)) + (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) := by
    unfold ikfReturn; rw [ikf_wage_succ, ikf_hc_succ R κ w₀ l ht]; ring
  have hRi : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have hRi0 : 0 < R⁻¹ := inv_pos.2 hR
  have hH := ikf_hc_nonneg hR hκ (fun s hs => (hl s hs).le) (t + 1)
  have hB : 0 ≤ l t - R⁻¹ * l (t + 1) := by nlinarith [hl (t + 1) (by omega)]
  nlinarith [mul_nonneg hκ hB, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - R⁻¹) hH]

/-- AKMM, p. 358, Figure 12.6: under the hypotheses of `ikf_hours_up`, hours rise strictly if
moreover `R > 1` (with `κw₀ > 0`) or `βR < 1`. -/
theorem ikf_hours_up_strict {R β κ w₀ ψ γ τ : ℝ} {T t : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ)
    (hγ : 0 < γ) (hτ : τ < 1) (hR1 : 1 ≤ R) (hβR : β * R ≤ 1) (hκ : 0 ≤ κ * w₀)
    (hstrict : (1 < R ∧ 0 < κ * w₀) ∨ β * R < 1)
    (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (heul : ∀ s < T, lam s = β * R * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn R κ w₀ T l s)
    (ht : t < T) : l t < l (t + 1) := by
  refine lt_of_not_ge fun h => ?_
  have hR : 0 < R := by linarith
  have h1 := Real.rpow_le_rpow (hl (t + 1) (by omega)).le h (by positivity : 0 ≤ 1 / γ)
  have hf0 := hfoc t ht.le
  have hf1 := hfoc (t + 1) ht
  have hτ' : 0 < 1 - τ := by linarith
  have hQ0 := ikf_return_pos hψ hτ hl hlam hfoc ht.le
  have hl1 := hlam (t + 1) ht
  have hA : lam (t + 1) * ikfReturn R κ w₀ T l (t + 1) ≤ lam t * ikfReturn R κ w₀ T l t := by
    have : lam (t + 1) * (1 - τ) * ikfReturn R κ w₀ T l (t + 1) ≤
        lam t * (1 - τ) * ikfReturn R κ w₀ T l t := by nlinarith
    nlinarith
  have hD : ikfReturn R κ w₀ T l (t + 1) - ikfReturn R κ w₀ T l t =
      κ * w₀ * (l t - R⁻¹ * l (t + 1)) + (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) := by
    unfold ikfReturn; rw [ikf_wage_succ, ikf_hc_succ R κ w₀ l ht]; ring
  have hRi : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have hRi0 : 0 < R⁻¹ := inv_pos.2 hR
  have hH := ikf_hc_nonneg hR hκ (fun s hs => (hl s hs).le) (t + 1)
  have hlt1 := hl (t + 1) (by omega)
  have hH' : 0 ≤ (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) :=
    mul_nonneg (by linarith) hH
  rcases hstrict with ⟨hR1', hκ'⟩ | hβR'
  · have hlt : lam t ≤ lam (t + 1) := by rw [heul t ht]; nlinarith
    have hQ : ikfReturn R κ w₀ T l (t + 1) ≤ ikfReturn R κ w₀ T l t := by nlinarith
    have hRi1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR1'
    have hB : 0 < l t - R⁻¹ * l (t + 1) := by nlinarith
    nlinarith [mul_pos hκ' hB]
  · have hlt : lam t < lam (t + 1) := by rw [heul t ht]; nlinarith
    have hQ : ikfReturn R κ w₀ T l (t + 1) < ikfReturn R κ w₀ T l t := by nlinarith
    have hB : 0 ≤ l t - R⁻¹ * l (t + 1) := by nlinarith
    nlinarith [mul_nonneg hκ hB]

/-- AKMM, p. 358, Figure 12.6, hours over the life cycle: along any interior path satisfying
(12.41) and the Euler equation, if `0 < R ≤ 1` and `βR ≥ 1`, hours never rise:
`ℓ_{t+1} ≤ ℓ_t`. -/
theorem ikf_hours_down {R β κ w₀ ψ γ τ : ℝ} {T t : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ)
    (hγ : 0 < γ) (hτ : τ < 1) (hR : 0 < R) (hR1 : R ≤ 1) (hβR : 1 ≤ β * R) (hκ : 0 ≤ κ * w₀)
    (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (heul : ∀ s < T, lam s = β * R * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn R κ w₀ T l s)
    (ht : t < T) : l (t + 1) ≤ l t := by
  refine le_of_not_gt fun h => ?_
  have h1 := Real.rpow_lt_rpow (hl t ht.le).le h (by positivity : 0 < 1 / γ)
  have hf0 := hfoc t ht.le
  have hf1 := hfoc (t + 1) ht
  have hτ' : 0 < 1 - τ := by linarith
  have hQ1 := ikf_return_pos hψ hτ hl hlam hfoc (s := t + 1) ht
  have hl1 := hlam (t + 1) ht
  have hlt : lam (t + 1) ≤ lam t := by rw [heul t ht]; nlinarith
  have hA : lam t * ikfReturn R κ w₀ T l t < lam (t + 1) * ikfReturn R κ w₀ T l (t + 1) := by
    have : lam t * (1 - τ) * ikfReturn R κ w₀ T l t <
        lam (t + 1) * (1 - τ) * ikfReturn R κ w₀ T l (t + 1) := by nlinarith
    nlinarith
  have hl0 := hlam t ht.le
  have hQ : ikfReturn R κ w₀ T l t < ikfReturn R κ w₀ T l (t + 1) := by nlinarith
  have hD : ikfReturn R κ w₀ T l (t + 1) - ikfReturn R κ w₀ T l t =
      κ * w₀ * (l t - R⁻¹ * l (t + 1)) + (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) := by
    unfold ikfReturn; rw [ikf_wage_succ, ikf_hc_succ R κ w₀ l ht]; ring
  have hRi : 1 ≤ R⁻¹ := one_le_inv₀ hR |>.2 hR1
  have hH := ikf_hc_nonneg hR hκ (fun s hs => (hl s hs).le) (t + 1)
  have hB : l t - R⁻¹ * l (t + 1) ≤ 0 := by nlinarith [hl (t + 1) (by omega)]
  nlinarith [mul_nonneg hκ (by linarith : (0 : ℝ) ≤ -(l t - R⁻¹ * l (t + 1))),
    mul_nonneg (by linarith : (0 : ℝ) ≤ R⁻¹ - 1) hH]

/-- AKMM, p. 358, Figure 12.6: under the hypotheses of `ikf_hours_down`, hours fall strictly if
moreover `R < 1` (with `κw₀ > 0`) or `βR > 1`. -/
theorem ikf_hours_down_strict {R β κ w₀ ψ γ τ : ℝ} {T t : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ)
    (hγ : 0 < γ) (hτ : τ < 1) (hR : 0 < R) (hR1 : R ≤ 1) (hβR : 1 ≤ β * R) (hκ : 0 ≤ κ * w₀)
    (hstrict : (R < 1 ∧ 0 < κ * w₀) ∨ 1 < β * R)
    (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (heul : ∀ s < T, lam s = β * R * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn R κ w₀ T l s)
    (ht : t < T) : l (t + 1) < l t := by
  refine lt_of_not_ge fun h => ?_
  have h1 := Real.rpow_le_rpow (hl t ht.le).le h (by positivity : 0 ≤ 1 / γ)
  have hf0 := hfoc t ht.le
  have hf1 := hfoc (t + 1) ht
  have hτ' : 0 < 1 - τ := by linarith
  have hQ1 := ikf_return_pos hψ hτ hl hlam hfoc (s := t + 1) ht
  have hl1 := hlam (t + 1) ht
  have hl0 := hlam t ht.le
  have hA : lam t * ikfReturn R κ w₀ T l t ≤ lam (t + 1) * ikfReturn R κ w₀ T l (t + 1) := by
    have : lam t * (1 - τ) * ikfReturn R κ w₀ T l t ≤
        lam (t + 1) * (1 - τ) * ikfReturn R κ w₀ T l (t + 1) := by nlinarith
    nlinarith
  have hD : ikfReturn R κ w₀ T l (t + 1) - ikfReturn R κ w₀ T l t =
      κ * w₀ * (l t - R⁻¹ * l (t + 1)) + (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) := by
    unfold ikfReturn; rw [ikf_wage_succ, ikf_hc_succ R κ w₀ l ht]; ring
  have hRi : 1 ≤ R⁻¹ := one_le_inv₀ hR |>.2 hR1
  have hH := ikf_hc_nonneg hR hκ (fun s hs => (hl s hs).le) (t + 1)
  have hH' : (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hH
  have hlt1 := hl (t + 1) (by omega)
  rcases hstrict with ⟨hR1', hκ'⟩ | hβR'
  · have hlt : lam (t + 1) ≤ lam t := by rw [heul t ht]; nlinarith
    have hQ : ikfReturn R κ w₀ T l t ≤ ikfReturn R κ w₀ T l (t + 1) := by nlinarith
    have hRi1 : 1 < R⁻¹ := one_lt_inv₀ hR |>.2 hR1'
    have hB : l t - R⁻¹ * l (t + 1) < 0 := by nlinarith
    nlinarith [mul_pos hκ' (by linarith : (0 : ℝ) < -(l t - R⁻¹ * l (t + 1)))]
  · have hlt : lam (t + 1) < lam t := by rw [heul t ht]; nlinarith
    have hQ : ikfReturn R κ w₀ T l t < ikfReturn R κ w₀ T l (t + 1) := by nlinarith
    have hB : l t - R⁻¹ * l (t + 1) ≤ 0 := by nlinarith
    nlinarith [mul_nonneg hκ (by linarith : (0 : ℝ) ≤ -(l t - R⁻¹ * l (t + 1)))]

/-- AKMM, p. 358, Figure 12.6, "hours are relatively flat while wages grow steeply" and the
return to work is "much flatter": at `R = β = 1`, along any interior path satisfying (12.41) and
the Euler equation, for every `t ≤ T`: hours are constant, `ℓ_t = ℓ₀`; the wage rises linearly,
`w_t = (1 + κℓ₀t)w₀`; the human-capital term falls linearly to zero, `H_t = κw₀ℓ₀(T − t)`; and
the return to work is constant, `w_t + H_t = (1 + κℓ₀T)w₀`. -/
theorem ikf_flat {κ w₀ ψ γ τ : ℝ} {T : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hτ : τ < 1) (hκ : 0 ≤ κ * w₀) (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (heul : ∀ s < T, lam s = 1 * 1 * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn 1 κ w₀ T l s) :
    ∀ t ≤ T, l t = l 0 ∧ ikWage κ w₀ l t = (1 + κ * l 0 * t) * w₀ ∧
      ikfHC 1 κ w₀ T l t = κ * w₀ * l 0 * ((T : ℝ) - t) ∧
      ikfReturn 1 κ w₀ T l t = (1 + κ * l 0 * T) * w₀ := by
  have hstep : ∀ s < T, l (s + 1) = l s := fun s hs =>
    le_antisymm
      (ikf_hours_down hψ hγ hτ one_pos le_rfl (by norm_num) hκ hl hlam heul hfoc hs)
      (ikf_hours_up hψ hγ hτ le_rfl (by norm_num) hκ hl hlam heul hfoc hs)
  have hconst : ∀ t ≤ T, l t = l 0 := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ n ih => intro hn; rw [hstep n (by omega), ih (by omega)]
  have hwage : ∀ t ≤ T, ikWage κ w₀ l t = (1 + κ * l 0 * t) * w₀ := by
    intro t ht
    unfold ikWage
    rw [Finset.sum_congr rfl fun j hj => hconst j (by rw [Finset.mem_range] at hj; omega),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hhc : ∀ t ≤ T, ikfHC 1 κ w₀ T l t = κ * w₀ * l 0 * ((T : ℝ) - t) := by
    intro t ht
    unfold ikfHC
    rw [Finset.sum_congr rfl fun j hj => by
        rw [inv_one, one_pow, one_mul, hconst (t + j + 1) (by rw [Finset.mem_range] at hj; omega)],
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub ht]
    ring
  intro t ht
  refine ⟨hconst t ht, hwage t ht, hhc t ht, ?_⟩
  rw [ikfReturn, hwage t ht, hhc t ht]
  ring

/-- AKMM, p. 358, "naively estimating `γ` from the relation between current wages and current
hours would lead one to underestimate its true value": if the same hours `ℓ` satisfy
`ℓ = A w^g` at two different wages `0 < w < w′` (`A ≠ 0`), the fitted elasticity is `g = 0`. -/
theorem ikf_naive_gamma {A g w w' ℓ : ℝ} (hA : A ≠ 0) (hw : 0 < w) (hww : w < w')
    (h0 : ℓ = A * w ^ g) (h1 : ℓ = A * w' ^ g) : g = 0 := by
  have he : w ^ g = w' ^ g := mul_left_cancel₀ hA (h0.symm.trans h1)
  rcases lt_trichotomy g 0 with hg | hg | hg
  · exact absurd he (Real.rpow_lt_rpow_of_neg hw hww hg).ne'
  · exact hg
  · exact absurd he (Real.rpow_lt_rpow hw.le hww hg).ne

/-- AKMM, p. 358: at `R = β = 1` with `κ > 0`, `w₀ > 0` and `T ≥ 1`, the profile of `ikf_flat`
makes the naive estimate of the elasticity of hours with respect to the current wage zero,
whatever the true `γ > 0`: if `ℓ_t = Aw_t^g` for all `t ≤ T`, `A ≠ 0`, then `g = 0`. -/
theorem ikf_flat_naive {κ w₀ ψ γ τ A g : ℝ} {T : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hτ : τ < 1) (hκ : 0 < κ) (hw₀ : 0 < w₀) (hT : 1 ≤ T) (hl : ∀ s ≤ T, 0 < l s)
    (hlam : ∀ s ≤ T, 0 < lam s) (heul : ∀ s < T, lam s = 1 * 1 * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn 1 κ w₀ T l s)
    (hA : A ≠ 0) (hfit : ∀ t ≤ T, l t = A * ikWage κ w₀ l t ^ g) : g = 0 := by
  have hf := ikf_flat hψ hγ hτ (mul_pos hκ hw₀).le hl hlam heul hfoc
  have h0 := hf 0 (Nat.zero_le _)
  have h1 := hf 1 hT
  have hl0 := hl 0 (Nat.zero_le _)
  refine ikf_naive_gamma hA (w := ikWage κ w₀ l 0) (w' := ikWage κ w₀ l 1) ?_ ?_
    (hfit 0 (Nat.zero_le _)) (h1.1 ▸ hfit 1 hT)
  · rw [h0.2.1]; norm_num; exact hw₀
  · rw [h0.2.1, h1.2.1]; push_cast
    nlinarith [mul_pos (mul_pos hκ hl0) hw₀]

/-- AKMM, p. 358, Figure 12.6: the hypotheses of `ikf_hours_up_strict` are satisfiable
(`T = 1`, `R = 2`, `β = 1/2`, `λ ≡ 1`, `ψ = γ = κ = w₀ = 1`, `τ = 0`, `ℓ = (3, 4)`). -/
theorem ikf_instance_up :
    let l : ℕ → ℝ := fun t => if t = 0 then 3 else 4
    (∀ s ≤ 1, (1 : ℝ) * l s ^ (1 / (1 : ℝ)) = 1 * (1 - 0) * ikfReturn 2 1 1 1 l s) ∧
      (1 : ℝ) = 1 / 2 * 2 * 1 ∧ l 0 < l 1 := by
  intro l
  refine ⟨fun s hs => ?_, by norm_num, by norm_num [l]⟩
  interval_cases s <;>
    simp [l, ikfReturn, ikfHC, ikWage] <;> norm_num

/-- AKMM, p. 358, Figure 12.6: the hypotheses of `ikf_hours_down_strict` are satisfiable
(`T = 1`, `R = 1/2`, `β = 2`, `λ ≡ 1`, `ψ = 3`, `γ = κ = w₀ = 1`, `τ = 0`,
`ℓ = (5/7, 4/7)`). -/
theorem ikf_instance_down :
    let l : ℕ → ℝ := fun t => if t = 0 then 5 / 7 else 4 / 7
    (∀ s ≤ 1, (3 : ℝ) * l s ^ (1 / (1 : ℝ)) = 1 * (1 - 0) * ikfReturn (1 / 2) 1 1 1 l s) ∧
      (1 : ℝ) = 2 * (1 / 2) * 1 ∧ l 1 < l 0 := by
  intro l
  refine ⟨fun s hs => ?_, by norm_num, by norm_num [l]⟩
  interval_cases s <;>
    simp [l, ikfReturn, ikfHC, ikWage] <;> norm_num

/-- AKMM, p. 358, Figure 12.6: the hypotheses of `ikf_flat` are satisfiable
(`T = 1`, `R = β = 1`, `λ ≡ 1`, `ψ = 2`, `γ = κ = w₀ = 1`, `τ = 0`, `ℓ ≡ 1`). -/
theorem ikf_instance_flat :
    (∀ s ≤ 1, (2 : ℝ) * (fun _ => (1 : ℝ)) s ^ (1 / (1 : ℝ)) =
      1 * (1 - 0) * ikfReturn 1 1 1 1 (fun _ => 1) s) := by
  intro s hs
  interval_cases s <;>
    simp [ikfReturn, ikfHC, ikWage] <;> norm_num

/-- The hours of the counterexample of `ikf_hc_rises`: `ℓ = (103/77, 20/7, 400/77)`. -/
noncomputable def ikfCexHours (t : ℕ) : ℝ :=
  if t = 0 then 103 / 77 else if t = 1 then 20 / 7 else 400 / 77

/-- AKMM, p. 358, "the human capital term … declines with age" **fails for `R > 1`** in
general. Three periods (`T = 2`), `R = 10`, `β = 1/10`, `u = crraU 2` (`σ = 2`),
`v = disutil 1 1` (`ψ = γ = 1`), `κ = w₀ = 1`, `τ = 0`: the plan `c ≡ 1`,
`ℓ = (103/77, 20/7, 400/77)` (i) satisfies (12.41) with `λ ≡ 1` and the Euler equation,
(ii) is globally optimal among all plans `(c, ℓ)` with `c > 0` that satisfy the same lifetime
budget, and (iii) has `H₀ = 26/77 < 40/77 = H₁`: the human-capital term rises from age 0 to 1. -/
theorem ikf_hc_rises :
    (∀ s ≤ 2, (1 : ℝ) * ikfCexHours s ^ (1 / (1 : ℝ)) =
      1 * (1 - 0) * ikfReturn 10 1 1 2 ikfCexHours s) ∧
    (1 : ℝ) = 1 / 10 * 10 * 1 ∧
    (∀ c l : ℕ → ℝ, (∀ t ≤ 2, 0 < c t) →
      ∑ t ∈ Finset.range 3, (10⁻¹ : ℝ) ^ t * c t - ikEarnings 10 0 1 1 2 l ≤
        ∑ t ∈ Finset.range 3, (10⁻¹ : ℝ) ^ t * 1 - ikEarnings 10 0 1 1 2 ikfCexHours →
      ∑ t ∈ Finset.range 3, (10⁻¹ : ℝ) ^ t * (crraU 2 (c t) - disutil 1 1 (l t)) ≤
        ∑ t ∈ Finset.range 3, (10⁻¹ : ℝ) ^ t * (crraU 2 1 - disutil 1 1 (ikfCexHours t))) ∧
    ikfHC 10 1 1 2 ikfCexHours 0 = 26 / 77 ∧ ikfHC 10 1 1 2 ikfCexHours 1 = 40 / 77 := by
  refine ⟨fun s hs => ?_, by norm_num, fun c l hc hbud => ?_, ?_, ?_⟩
  · interval_cases s <;>
      simp [ikfCexHours, ikfReturn, ikfHC, ikWage, Finset.sum_range_succ] <;> norm_num
  · have hu : ∀ x : ℝ, 0 < x → crraU 2 x ≤ x - 2 := by
      intro x hx
      have : crraU 2 x = -x⁻¹ := by
        unfold crraU
        simp only [show (2 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
        rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
        ring
      rw [this]
      have : x⁻¹ * x = 1 := inv_mul_cancel₀ hx.ne'
      nlinarith [sq_nonneg (x - 1), inv_pos.2 hx]
    have hu1 : crraU 2 1 = -1 := by
      unfold crraU
      simp only [show (2 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
      rw [Real.one_rpow]
      norm_num
    have hv : ∀ x : ℝ, disutil 1 1 x = x ^ 2 / 2 := by
      intro x
      unfold disutil
      rw [show (1 : ℝ) + 1 / 1 = 2 by norm_num, Real.rpow_two]
      ring
    have h0 := hu (c 0) (hc 0 (by norm_num))
    have h1 := hu (c 1) (hc 1 (by norm_num))
    have h2 := hu (c 2) (hc 2 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, ikEarnings, ikWage, hv, hu1,
      ikfCexHours] at hbud ⊢
    norm_num at hbud ⊢
    nlinarith [sq_nonneg (l 0 - 103 / 77 - (l 1 - 20 / 7) / 10 - (l 2 - 400 / 77) / 100),
      sq_nonneg (l 1 - 20 / 7 - 11 / 90 * (l 2 - 400 / 77)), sq_nonneg (l 2 - 400 / 77)]
  · simp [ikfCexHours, ikfHC, Finset.sum_range_succ]; norm_num
  · simp [ikfCexHours, ikfHC]; norm_num

end AKMM.LaborSupply

set_option linter.style.longLine false
#print axioms AKMM.LaborSupply.crraU
#print axioms AKMM.LaborSupply.disutil
#print axioms AKMM.LaborSupply.stObj
#print axioms AKMM.LaborSupply.st_crraU_hasDerivAt
#print axioms AKMM.LaborSupply.st_disutil_hasDerivAt
#print axioms AKMM.LaborSupply.st_obj_hasDerivAt
#print axioms AKMM.LaborSupply.st_deriv_factor
#print axioms AKMM.LaborSupply.st_foc_form
#print axioms AKMM.LaborSupply.st_foc_strictMono
#print axioms AKMM.LaborSupply.eq_12_1
#print axioms AKMM.LaborSupply.st_path_identity
#print axioms AKMM.LaborSupply.st_path_poly
#print axioms AKMM.LaborSupply.st_exp_path
#print axioms AKMM.LaborSupply.eq_12_3
#print axioms AKMM.LaborSupply.eq_12_2
#print axioms AKMM.LaborSupply.st_footnote_2
#print axioms AKMM.LaborSupply.eq_12_4
#print axioms AKMM.LaborSupply.st_compensated_utility
#print axioms AKMM.LaborSupply.st_slutsky
#print axioms AKMM.LaborSupply.st_substitution_effect
#print axioms AKMM.LaborSupply.st_signs
#print axioms AKMM.LaborSupply.st_zero_income_signs
#print axioms AKMM.LaborSupply.st_effects_mono_gamma
#print axioms AKMM.LaborSupply.stExplicit
#print axioms AKMM.LaborSupply.st_explicit_foc
#print axioms AKMM.LaborSupply.st_explicit_path
#print axioms AKMM.LaborSupply.st_footnote_2_printed_false
#print axioms AKMM.LaborSupply.st_tax_as_wage
#print axioms AKMM.LaborSupply.st_balanced_budget
#print axioms AKMM.LaborSupply.st_balanced_budget_hicks_iff
#print axioms AKMM.LaborSupply.ext_foc_of_max
#print axioms AKMM.LaborSupply.hp_focs
#print axioms AKMM.LaborSupply.eq_12_5
#print axioms AKMM.LaborSupply.cesG
#print axioms AKMM.LaborSupply.hp_ces_partials
#print axioms AKMM.LaborSupply.eq_12_6
#print axioms AKMM.LaborSupply.eq_12_6_printed_false
#print axioms AKMM.LaborSupply.hp_ratio_decreasing
#print axioms AKMM.LaborSupply.hh_focs
#print axioms AKMM.LaborSupply.hh_relative_hours
#print axioms AKMM.LaborSupply.hh_cross_wage
#print axioms AKMM.LaborSupply.st_income_decreasing
#print axioms AKMM.LaborSupply.hh_added_worker
#print axioms AKMM.LaborSupply.lt_benchmark_elasticity
#print axioms AKMM.LaborSupply.lt_vtilde_hasDerivAt
#print axioms AKMM.LaborSupply.lt_corner
#print axioms AKMM.LaborSupply.lt_elasticity
#print axioms AKMM.LaborSupply.lt_elasticity_limits
#print axioms AKMM.LaborSupply.tp_frisch
#print axioms AKMM.LaborSupply.footnote_8
#print axioms AKMM.LaborSupply.footnote_8_printed_false
#print axioms AKMM.LaborSupply.eq_12_9_to_12_11
#print axioms AKMM.LaborSupply.DynFeasible
#print axioms AKMM.LaborSupply.dyn_two_stage
#print axioms AKMM.LaborSupply.eq_12_13
#print axioms AKMM.LaborSupply.eq_12_12
#print axioms AKMM.LaborSupply.eq_12_14
#print axioms AKMM.LaborSupply.eq_12_15
#print axioms AKMM.LaborSupply.eq_12_15_path
#print axioms AKMM.LaborSupply.eq_12_16
#print axioms AKMM.LaborSupply.eq_12_17
#print axioms AKMM.LaborSupply.dyn_compensation_sign
#print axioms AKMM.LaborSupply.eq_12_21
#print axioms AKMM.LaborSupply.frischF
#print axioms AKMM.LaborSupply.dyn_frisch_separable
#print axioms AKMM.LaborSupply.dyn_frisch_separable_path
#print axioms AKMM.LaborSupply.dyn_ghh_partials
#print axioms AKMM.LaborSupply.dyn_frisch_ghh
#print axioms AKMM.LaborSupply.dyn_ghh_no_income_effect
#print axioms AKMM.LaborSupply.dyn_cd_partials
#print axioms AKMM.LaborSupply.dyn_frisch_cd
#print axioms AKMM.LaborSupply.dyn_frisch_leisure
#print axioms AKMM.LaborSupply.dyn_frisch_decreasing_hours
#print axioms AKMM.LaborSupply.dyn_ordering
#print axioms AKMM.LaborSupply.dyn_ordering_sigma_zero
#print axioms AKMM.LaborSupply.dyn_ordering_sigma_infty
#print axioms AKMM.LaborSupply.eq_12_23
#print axioms AKMM.LaborSupply.eq_12_24
#print axioms AKMM.LaborSupply.eq_12_25
#print axioms AKMM.LaborSupply.eq_12_26
#print axioms AKMM.LaborSupply.eq_12_27
#print axioms AKMM.LaborSupply.eq_12_28
#print axioms AKMM.LaborSupply.fe_log_approx
#print axioms AKMM.LaborSupply.eq_12_29
#print axioms AKMM.LaborSupply.eq_12_31
#print axioms AKMM.LaborSupply.fe_consumption_data
#print axioms AKMM.LaborSupply.fr_rpow_tangent
#print axioms AKMM.LaborSupply.frV
#print axioms AKMM.LaborSupply.fr_opt_facts
#print axioms AKMM.LaborSupply.eq_12_33
#print axioms AKMM.LaborSupply.fr_value
#print axioms AKMM.LaborSupply.eq_12_34
#print axioms AKMM.LaborSupply.fr_gain_pos
#print axioms AKMM.LaborSupply.fr_gain_strictMono
#print axioms AKMM.LaborSupply.eq_12_35
#print axioms AKMM.LaborSupply.fr_threshold
#print axioms AKMM.LaborSupply.bgF
#print axioms AKMM.LaborSupply.bgMPK
#print axioms AKMM.LaborSupply.bgMPL
#print axioms AKMM.LaborSupply.bg_homog
#print axioms AKMM.LaborSupply.kprU
#print axioms AKMM.LaborSupply.kprUC
#print axioms AKMM.LaborSupply.kprUl
#print axioms AKMM.LaborSupply.kpr_partials
#print axioms AKMM.LaborSupply.kpr_mrs
#print axioms AKMM.LaborSupply.kpr_homog
#print axioms AKMM.LaborSupply.kpr_static_hours
#print axioms AKMM.LaborSupply.eq_12_37_if
#print axioms AKMM.LaborSupply.eq_12_37_printed_not_bgp
#print axioms AKMM.LaborSupply.eq_12_A_2
#print axioms AKMM.LaborSupply.kpr_candidate_deriv
#print axioms AKMM.LaborSupply.eq_12_A_3
#print axioms AKMM.LaborSupply.eq_12_A_3_log
#print axioms AKMM.LaborSupply.eq_12_37_only_if
#print axioms AKMM.LaborSupply.eq_12_37_only_if_instance
#print axioms AKMM.LaborSupply.bg_mpl_eq
#print axioms AKMM.LaborSupply.eq_12_39
#print axioms AKMM.LaborSupply.eq_12_39_us_italy
#print axioms AKMM.LaborSupply.ti_effect_ratio
#print axioms AKMM.LaborSupply.ti_subsistence
#print axioms AKMM.LaborSupply.ti_subsistence_marshallian
#print axioms AKMM.LaborSupply.ti_sigma_gt_one
#print axioms AKMM.LaborSupply.eq_12_40
#print axioms AKMM.LaborSupply.ti_cycle_coefficient
#print axioms AKMM.LaborSupply.ti_no_capital
#print axioms AKMM.LaborSupply.ikWage
#print axioms AKMM.LaborSupply.ikEarnings
#print axioms AKMM.LaborSupply.ik_marginal_earnings
#print axioms AKMM.LaborSupply.eq_12_41
#print axioms AKMM.LaborSupply.il_lottery
#print axioms AKMM.LaborSupply.il_full_insurance
#print axioms AKMM.LaborSupply.il_planner
#print axioms AKMM.LaborSupply.il_frisch_infinite
#print axioms AKMM.LaborSupply.il_lagrange_suff
#print axioms AKMM.LaborSupply.il_ljungqvist_sargent
#print axioms AKMM.LaborSupply.il_vtilde_deriv
#print axioms AKMM.LaborSupply.il_vtilde_convex
#print axioms AKMM.LaborSupply.il_vtilde_uniform
#print axioms AKMM.LaborSupply.il_hetero_frisch
#print axioms AKMM.LaborSupply.effHours
#print axioms AKMM.LaborSupply.il_concentrate
#print axioms AKMM.LaborSupply.il_small_hours
#print axioms AKMM.LaborSupply.il_rw_threshold
#print axioms AKMM.LaborSupply.il_rw_life_cycle
#print axioms AKMM.LaborSupply.ikfHC
#print axioms AKMM.LaborSupply.ikfReturn
#print axioms AKMM.LaborSupply.ikf_hc_last
#print axioms AKMM.LaborSupply.ikf_hc_succ
#print axioms AKMM.LaborSupply.ikf_hc_diff
#print axioms AKMM.LaborSupply.ikf_wage_succ
#print axioms AKMM.LaborSupply.ikf_wage_step
#print axioms AKMM.LaborSupply.ikf_hc_nonneg
#print axioms AKMM.LaborSupply.ikf_return_vs_wage
#print axioms AKMM.LaborSupply.ikf_hc_step_le_one
#print axioms AKMM.LaborSupply.ikf_hc_antitone
#print axioms AKMM.LaborSupply.ikf_geom
#print axioms AKMM.LaborSupply.ikf_hc_step_peak
#print axioms AKMM.LaborSupply.ikf_hc_const_hours
#print axioms AKMM.LaborSupply.ikf_return_pos
#print axioms AKMM.LaborSupply.ikf_hours_up
#print axioms AKMM.LaborSupply.ikf_hours_up_strict
#print axioms AKMM.LaborSupply.ikf_hours_down
#print axioms AKMM.LaborSupply.ikf_hours_down_strict
#print axioms AKMM.LaborSupply.ikf_flat
#print axioms AKMM.LaborSupply.ikf_naive_gamma
#print axioms AKMM.LaborSupply.ikf_flat_naive
#print axioms AKMM.LaborSupply.ikf_instance_up
#print axioms AKMM.LaborSupply.ikf_instance_down
#print axioms AKMM.LaborSupply.ikf_instance_flat
#print axioms AKMM.LaborSupply.ikfCexHours
#print axioms AKMM.LaborSupply.ikf_hc_rises

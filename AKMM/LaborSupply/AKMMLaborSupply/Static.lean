/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

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

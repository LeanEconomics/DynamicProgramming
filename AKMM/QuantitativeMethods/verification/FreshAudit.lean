import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import PartialInformation.KFMoments
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.Matrix.LDL
import RationalExpectations.VARMoments
import NeoclassicalGrowth.RBUtility
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import StructuralEstimation.MLLikelihood
import Mathlib.Probability.Independence.Basic
import PartialInformation.KFExamples
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The static fiscal model and its multiplier

AKMM, §8.2, (8.1)–(8.3), pp. 218–219; §8.4, (8.5)–(8.6) and footnote 3, pp. 222–223; §8.6.2,
p. 231; Appendix 8.A.2, p. 842.

A planner chooses `c, ℓ, G > 0` to maximise `U = log c − ℓ^{1+ψ}/(1+ψ) + γη log G` (8.1) subject
to `c + G = Aℓ`. We prove:

* the planner problem has the unique solution `ℓ* = (1+γη)^{1/(1+ψ)}`, `c* = Aℓ*/(1+γη)`,
  `G* = γηc*` (`sm_planner_optimal`, `sm_planner_unique`), and a feasible point satisfies the two
  first-order conditions `A/c = ℓ^ψ`, `G = γηc` iff it is that solution (`sm_foc_iff`);
* eliminating `c = y − G` and `ℓ = y/A`, the first-order conditions are equivalent to the supply
  curve (8.2) and the fiscal rule (8.3) (`eq_8_2_8_3`); (8.2)–(8.3) have the unique solution
  `y = A(1+γη)^{1/(1+ψ)}`, `G = γη/(1+γη)·y` (`sm_equilibrium_unique`), and the rule is
  increasing in `y` and `η` (`sm_fiscal_rule_monotone`);
* the fiscal multiplier computed as `(dy/dη)/(dG/dη)` (`sm_multiplier_eta`) and as the slope of
  the supply curve, the derivative of the local inverse of `y ↦ G` along (8.2)
  (`sm_supply_slope`), both equal `1/(1 + ψ(1 − Ḡ/ȳ)) = (1+χ)⁻¹χ ȳ/Ḡ` (`sm_multiplier_formula`,
  Appendix 8.A.2), which lies in `(0, 1)` (`sm_multiplier_mem_Ioo`);
* Appendix 8.A.2: `∂y/∂A = (1+χ)⁻¹ȳ/Ā` (`sm_supply_dA`) and the solved total differential
  (`appendix_8A_2_total_differential`); at `η̄ = 1`, `Ḡ/ȳ = γ/(1+γ)` and `χ = γ/(1+ψ)`
  (`appendix_8A_2_steady`);
* (8.5)–(8.6): the elasticities of `y` with respect to `A` and `G` are `1/(1+χ)` and `χ/(1+χ)`
  (`eq_8_5`), the derivative of `log(G/y)` in `log η` at `η = 1` is `1/(1+γ)` (`eq_8_6`), and
  footnote 3's conversion from logs to levels (`fn_3`);
* the multiplier falls as `ψ` rises (`sm_multiplier_antitone_psi`, §8.8, p. 234).

Departure: the book's total differential is a statement about the implicit function defined by
(8.2); here it is the strict derivative of an explicit local inverse given by the inverse function
theorem.
-/

namespace AKMM.QuantitativeMethods

open Filter Topology

/-- AKMM, (8.1), p. 218: the period utility `log c − ℓ^{1+ψ}/(1+ψ) + γη log G`. -/
noncomputable def sm_utility (ψ γ η c ℓ G : ℝ) : ℝ :=
  Real.log c - ℓ ^ (1 + ψ) / (1 + ψ) + γ * η * Real.log G

/-- AKMM, p. 218: the planner's labour `ℓ* = (1+γη)^{1/(1+ψ)}`. -/
noncomputable def sm_lstar (ψ γ η : ℝ) : ℝ := (1 + γ * η) ^ (1 + ψ)⁻¹

/-- AKMM, p. 218: the planner's consumption `c* = Aℓ*/(1+γη)`. -/
noncomputable def sm_cstar (ψ γ η A : ℝ) : ℝ := A * sm_lstar ψ γ η / (1 + γ * η)

/-- AKMM, p. 218: the planner's spending `G* = γηc*`. -/
noncomputable def sm_Gstar (ψ γ η A : ℝ) : ℝ := γ * η * sm_cstar ψ γ η A

/-- Positive reals: `a = b^{1/p}` iff `a^p = b`. -/
theorem sm_eq_rpow_inv_iff {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : p ≠ 0) :
    a = b ^ p⁻¹ ↔ a ^ p = b := by
  constructor
  · rintro rfl
    exact Real.rpow_inv_rpow hb.le hp
  · rintro rfl
    exact (Real.rpow_rpow_inv ha.le hp).symm

theorem sm_lstar_pos {ψ γ η : ℝ} (hγη : 0 < γ * η) : 0 < sm_lstar ψ γ η :=
  Real.rpow_pos_of_pos (by linarith) _

theorem sm_lstar_rpow {ψ γ η : ℝ} (hψ : 0 < ψ) (hγη : 0 < γ * η) :
    sm_lstar ψ γ η ^ (1 + ψ) = 1 + γ * η :=
  Real.rpow_inv_rpow (by linarith) (by linarith)

/-- `ℓ*^ψ = (1+γη)/ℓ*`. -/
theorem sm_lstar_rpow_psi {ψ γ η : ℝ} (hψ : 0 < ψ) (hγη : 0 < γ * η) :
    sm_lstar ψ γ η ^ ψ = (1 + γ * η) / sm_lstar ψ γ η := by
  have hl := sm_lstar_pos (ψ := ψ) hγη
  rw [← sm_lstar_rpow hψ hγη, Real.rpow_add hl, Real.rpow_one]
  field_simp

/-- The planner's solution is feasible: `c* + G* = Aℓ*`, all positive. -/
theorem sm_star_feasible {ψ γ η A : ℝ} (hγη : 0 < γ * η) (hA : 0 < A) :
    0 < sm_cstar ψ γ η A ∧ 0 < sm_Gstar ψ γ η A ∧
      sm_cstar ψ γ η A + sm_Gstar ψ γ η A = A * sm_lstar ψ γ η := by
  have hl := sm_lstar_pos (ψ := ψ) hγη
  have hc : 0 < sm_cstar ψ γ η A := by unfold sm_cstar; positivity
  refine ⟨hc, by unfold sm_Gstar; positivity, ?_⟩
  unfold sm_Gstar sm_cstar
  field_simp

/-- **The planner's first-order conditions** (AKMM, p. 218): a feasible point `c + G = Aℓ` with
`c, ℓ, G > 0` satisfies `A/c = ℓ^ψ` and `G = γηc` iff it is `(c*, ℓ*, G*)`. -/
theorem sm_foc_iff {ψ γ η A c ℓ G : ℝ} (hψ : 0 < ψ) (hγη : 0 < γ * η) (hA : 0 < A)
    (hc : 0 < c) (hℓ : 0 < ℓ) (hfeas : c + G = A * ℓ) :
    (A / c = ℓ ^ ψ ∧ G = γ * η * c) ↔
      (c = sm_cstar ψ γ η A ∧ ℓ = sm_lstar ψ γ η ∧ G = sm_Gstar ψ γ η A) := by
  have hl := sm_lstar_pos (ψ := ψ) hγη
  constructor
  · rintro ⟨h1, h2⟩
    have hA' : A = c * ℓ ^ ψ := by field_simp at h1; linarith
    have hpow : ℓ ^ (1 + ψ) = 1 + γ * η := by
      rw [Real.rpow_add hℓ, Real.rpow_one]
      have : c * (1 + γ * η) = c * (ℓ * ℓ ^ ψ) := by rw [h2] at hfeas; rw [hA'] at hfeas; linarith
      have := mul_left_cancel₀ hc.ne' this
      linarith
    have hlℓ : ℓ = sm_lstar ψ γ η :=
      (sm_eq_rpow_inv_iff hℓ (by linarith) (by linarith)).2 hpow
    have hcc : c = sm_cstar ψ γ η A := by
      unfold sm_cstar
      rw [← hlℓ]
      field_simp
      rw [h2] at hfeas
      linarith
    exact ⟨hcc, hlℓ, by rw [h2, hcc]; rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨?_, rfl⟩
    rw [sm_lstar_rpow_psi hψ hγη]
    unfold sm_cstar
    field_simp

/-- `ℓ^{1+ψ} ≥ ℓ*^{1+ψ} + (1+ψ)ℓ*^{1+ψ}(ℓ/ℓ* − 1)` (Bernoulli). -/
theorem sm_rpow_tangent {ψ m ℓ : ℝ} (hψ : 0 < ψ) (hm : 0 < m) (hℓ : 0 ≤ ℓ) :
    m ^ (1 + ψ) + (1 + ψ) * m ^ (1 + ψ) * (ℓ / m - 1) ≤ ℓ ^ (1 + ψ) := by
  have hb := one_add_mul_self_le_rpow_one_add (s := ℓ / m - 1) (by
    have : 0 ≤ ℓ / m := by positivity
    linarith) (p := 1 + ψ) (by linarith)
  rw [show 1 + (ℓ / m - 1) = ℓ / m by ring, Real.div_rpow hℓ hm.le] at hb
  have hmp : 0 < m ^ (1 + ψ) := Real.rpow_pos_of_pos hm _
  rw [le_div_iff₀ hmp] at hb
  nlinarith

/-- **The planner problem** (AKMM, p. 218): `(c*, ℓ*, G*)` maximises (8.1) subject to
`c + G = Aℓ`. -/
theorem sm_planner_optimal {ψ γ η A c ℓ G : ℝ} (hψ : 0 < ψ) (hγη : 0 < γ * η) (hA : 0 < A)
    (hc : 0 < c) (hℓ : 0 ≤ ℓ) (hG : 0 < G) (hfeas : c + G = A * ℓ) :
    sm_utility ψ γ η c ℓ G ≤
      sm_utility ψ γ η (sm_cstar ψ γ η A) (sm_lstar ψ γ η) (sm_Gstar ψ γ η A) := by
  obtain ⟨hcs, hGs, hfs⟩ := sm_star_feasible (ψ := ψ) hγη hA
  have hl := sm_lstar_pos (ψ := ψ) hγη
  set cs := sm_cstar ψ γ η A with hcs_def
  set ls := sm_lstar ψ γ η with hls_def
  set Gs := sm_Gstar ψ γ η A with hGs_def
  have h1 := Real.log_le_sub_one_of_pos (div_pos hc hcs)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hG hGs)
  rw [Real.log_div hc.ne' hcs.ne'] at h1
  rw [Real.log_div hG.ne' hGs.ne'] at h2
  have h3 := sm_rpow_tangent hψ hl hℓ
  rw [sm_lstar_rpow hψ hγη] at h3
  have hGc : Gs = γ * η * cs := rfl
  have hcl : cs * (1 + γ * η) = A * ls := by
    simp only [hcs_def, hls_def, sm_cstar]; field_simp
  unfold sm_utility
  rw [sm_lstar_rpow hψ hγη]
  -- U − U* ≤ (c − c*)/c* − (1+γη)(ℓ/ℓ* − 1) + γη(G − G*)/G* = 0
  have key : (c / cs - 1) + γ * η * (G / Gs - 1) = (1 + γ * η) * (ℓ / ls - 1) := by
    have e1 : (c / cs - 1) + γ * η * (G / Gs - 1) = (c + G - (cs + Gs)) / cs := by
      have hγ0 : γ ≠ 0 := left_ne_zero_of_mul hγη.ne'
      have hη0 : η ≠ 0 := right_ne_zero_of_mul hγη.ne'
      have hcs0 := hcs.ne'
      rw [hGc]; field_simp; ring
    rw [e1, hfeas, hfs]
    have hAe : A = cs * (1 + γ * η) / ls := by rw [hcl]; field_simp
    rw [hAe]; field_simp
  have hp : 0 < 1 + ψ := by linarith
  have h4 : γ * η * Real.log G - γ * η * Real.log Gs ≤ γ * η * (G / Gs - 1) := by
    rw [← mul_sub]; exact mul_le_mul_of_nonneg_left h2 hγη.le
  have h5 : (1 + γ * η) + (1 + ψ) * (1 + γ * η) * (ℓ / ls - 1) ≤ ℓ ^ (1 + ψ) := h3
  have h6 : (1 + γ * η) / (1 + ψ) + (1 + γ * η) * (ℓ / ls - 1) ≤ ℓ ^ (1 + ψ) / (1 + ψ) := by
    rw [le_div_iff₀ hp]
    have : ((1 + γ * η) / (1 + ψ) + (1 + γ * η) * (ℓ / ls - 1)) * (1 + ψ) =
        (1 + γ * η) + (1 + ψ) * (1 + γ * η) * (ℓ / ls - 1) := by field_simp
    linarith
  linarith

/-- **Uniqueness of the planner's solution** (AKMM, p. 218): a feasible point attaining the
maximum of (8.1) is `(c*, ℓ*, G*)`. -/
theorem sm_planner_unique {ψ γ η A c ℓ G : ℝ} (hψ : 0 < ψ) (hγη : 0 < γ * η) (hA : 0 < A)
    (hc : 0 < c) (hℓ : 0 ≤ ℓ) (hG : 0 < G) (hfeas : c + G = A * ℓ)
    (hmax : sm_utility ψ γ η (sm_cstar ψ γ η A) (sm_lstar ψ γ η) (sm_Gstar ψ γ η A) ≤
      sm_utility ψ γ η c ℓ G) :
    c = sm_cstar ψ γ η A ∧ ℓ = sm_lstar ψ γ η ∧ G = sm_Gstar ψ γ η A := by
  obtain ⟨hcs, hGs, hfs⟩ := sm_star_feasible (ψ := ψ) hγη hA
  have hl := sm_lstar_pos (ψ := ψ) hγη
  set cs := sm_cstar ψ γ η A with hcs_def
  set ls := sm_lstar ψ γ η with hls_def
  set Gs := sm_Gstar ψ γ η A with hGs_def
  have hGc : Gs = γ * η * cs := rfl
  have hcl : cs * (1 + γ * η) = A * ls := by
    simp only [hcs_def, hls_def, sm_cstar]; field_simp
  have h3 := sm_rpow_tangent hψ hl hℓ
  rw [sm_lstar_rpow hψ hγη] at h3
  have hp : 0 < 1 + ψ := by linarith
  have key : (c / cs - 1) + γ * η * (G / Gs - 1) = (1 + γ * η) * (ℓ / ls - 1) := by
    have e1 : (c / cs - 1) + γ * η * (G / Gs - 1) = (c + G - (cs + Gs)) / cs := by
      have hγ0 : γ ≠ 0 := left_ne_zero_of_mul hγη.ne'
      have hη0 : η ≠ 0 := right_ne_zero_of_mul hγη.ne'
      have hcs0 := hcs.ne'
      rw [hGc]; field_simp; ring
    rw [e1, hfeas, hfs]
    have hAe : A = cs * (1 + γ * η) / ls := by rw [hcl]; field_simp
    rw [hAe]; field_simp
  have h6 : (1 + γ * η) / (1 + ψ) + (1 + γ * η) * (ℓ / ls - 1) ≤ ℓ ^ (1 + ψ) / (1 + ψ) := by
    rw [le_div_iff₀ hp]
    have : ((1 + γ * η) / (1 + ψ) + (1 + γ * η) * (ℓ / ls - 1)) * (1 + ψ) =
        (1 + γ * η) + (1 + ψ) * (1 + γ * η) * (ℓ / ls - 1) := by field_simp
    linarith
  unfold sm_utility at hmax
  rw [sm_lstar_rpow hψ hγη] at hmax
  have h1 := Real.log_le_sub_one_of_pos (div_pos hc hcs)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hG hGs)
  rw [Real.log_div hc.ne' hcs.ne'] at h1
  rw [Real.log_div hG.ne' hGs.ne'] at h2
  have h4 : γ * η * Real.log G - γ * η * Real.log Gs ≤ γ * η * (G / Gs - 1) := by
    rw [← mul_sub]; exact mul_le_mul_of_nonneg_left h2 hγη.le
  have hceq : c = cs := by
    by_contra hne
    have hs := Real.log_lt_sub_one_of_pos (div_pos hc hcs)
      (fun h => hne (by field_simp at h; linarith))
    rw [Real.log_div hc.ne' hcs.ne'] at hs
    linarith
  have hGeq : G = Gs := by
    by_contra hne
    have hs := Real.log_lt_sub_one_of_pos (div_pos hG hGs)
      (fun h => hne (by field_simp at h; linarith))
    rw [Real.log_div hG.ne' hGs.ne'] at hs
    have : γ * η * Real.log G - γ * η * Real.log Gs < γ * η * (G / Gs - 1) := by
      rw [← mul_sub]; exact mul_lt_mul_of_pos_left hs hγη
    linarith
  refine ⟨hceq, ?_, hGeq⟩
  have : A * ℓ = A * ls := by rw [← hfeas, ← hfs, hceq, hGeq]
  exact mul_left_cancel₀ hA.ne' this

/-- **(8.2) and (8.3)** (AKMM, pp. 218–219): with `c = y − G > 0` and `ℓ = y/A`, the first-order
conditions `A/c = ℓ^ψ`, `G = γηc` are equivalent to the supply curve `y = A(1 − G/y)^{−1/(1+ψ)}`
and the fiscal rule `G = γη/(1+γη)·y`. -/
theorem eq_8_2_8_3 {ψ γ η A y G : ℝ} (hψ : 0 < ψ) (hγη : 0 < γ * η) (hA : 0 < A)
    (hy : 0 < y) (hGy : G < y) :
    (A / (y - G) = (y / A) ^ ψ ∧ G = γ * η * (y - G)) ↔
      (y = A * (1 - G / y) ^ (-(1 + ψ)⁻¹) ∧ G = γ * η / (1 + γ * η) * y) := by
  have hs : 0 < 1 - G / y := by rw [sub_pos, div_lt_one hy]; exact hGy
  have hq : 0 < y / A := div_pos hy hA
  have hp : (1 + ψ) ≠ 0 := by linarith
  have hfr : G = γ * η * (y - G) ↔ G = γ * η / (1 + γ * η) * y := by
    constructor
    · intro h; field_simp; linarith
    · intro h; rw [h]; field_simp; ring
  rw [hfr]
  refine and_congr ?_ Iff.rfl
  -- (8.2) ⟺ (y/A)^{1+ψ} = (1 − G/y)⁻¹
  have h82 : y = A * (1 - G / y) ^ (-(1 + ψ)⁻¹) ↔ (y / A) ^ (1 + ψ) = (1 - G / y)⁻¹ := by
    rw [Real.rpow_neg hs.le, ← Real.inv_rpow hs.le]
    rw [← sm_eq_rpow_inv_iff hq (inv_pos.2 hs) hp]
    constructor
    · intro h; exact (div_eq_iff hA.ne').2 (by rw [mul_comm]; exact h)
    · intro h; rw [mul_comm]; exact (div_eq_iff hA.ne').1 h
  rw [h82, Real.rpow_add hq, Real.rpow_one]
  have hyG : y - G = y * (1 - G / y) := by field_simp
  rw [hyG]
  constructor
  · intro h; rw [← h]; field_simp
  · intro h
    have : (y / A) ^ ψ = (1 - G / y)⁻¹ / (y / A) := by
      rw [← h]; field_simp
    rw [this]; field_simp

/-- AKMM, p. 219: the equilibrium of (8.2)–(8.3), `y = A(1+γη)^{1/(1+ψ)}`. -/
noncomputable def sm_ystar (ψ γ η A : ℝ) : ℝ := A * (1 + γ * η) ^ (1 + ψ)⁻¹

/-- `y* = Aℓ*` and `G* = γη/(1+γη)·y*`. -/
theorem sm_ystar_eq {ψ γ η A : ℝ} (hγη : 0 < γ * η) :
    sm_ystar ψ γ η A = A * sm_lstar ψ γ η ∧
      sm_Gstar ψ γ η A = γ * η / (1 + γ * η) * sm_ystar ψ γ η A := by
  have : (1 + γ * η) ≠ 0 := by linarith
  refine ⟨rfl, ?_⟩
  unfold sm_Gstar sm_cstar sm_ystar sm_lstar
  field_simp

/-- **The equilibrium in `(G, y)` space** (AKMM, p. 219, Figure 8.1): for `0 < G < y`, (8.2) and
(8.3) hold iff `y = A(1+γη)^{1/(1+ψ)}` and `G = γη/(1+γη)·y`; this is the planner's
`(Aℓ*, G*)`. -/
theorem sm_equilibrium_unique {ψ γ η A y G : ℝ} (hγη : 0 < γ * η) (hy : 0 < y) :
    (y = A * (1 - G / y) ^ (-(1 + ψ)⁻¹) ∧ G = γ * η / (1 + γ * η) * y) ↔
      (y = sm_ystar ψ γ η A ∧ G = sm_Gstar ψ γ η A) := by
  have hX : 0 < 1 + γ * η := by linarith
  have hsG : ∀ y', 1 - γ * η / (1 + γ * η) * y' / y' = (1 + γ * η)⁻¹ ∨ y' = 0 := by
    intro y'
    rcases eq_or_ne y' 0 with h | h
    · exact Or.inr h
    · left; field_simp; ring
  constructor
  · rintro ⟨h1, h2⟩
    have hs : 1 - G / y = (1 + γ * η)⁻¹ := by
      rcases hsG y with h | h
      · rw [h2]; exact h
      · exact absurd h hy.ne'
    rw [hs, Real.inv_rpow hX.le, Real.rpow_neg hX.le, inv_inv] at h1
    have hyst : y = sm_ystar ψ γ η A := h1
    refine ⟨hyst, ?_⟩
    rw [h2, hyst, (sm_ystar_eq (ψ := ψ) (A := A) hγη).2]
  · rintro ⟨h1, h2⟩
    have h2' : G = γ * η / (1 + γ * η) * y := by
      rw [h2, h1, (sm_ystar_eq (ψ := ψ) (A := A) hγη).2]
    refine ⟨?_, h2'⟩
    have hs : 1 - G / y = (1 + γ * η)⁻¹ := by
      rcases hsG y with h | h
      · rw [h2']; exact h
      · exact absurd h hy.ne'
    rw [hs, Real.inv_rpow hX.le, Real.rpow_neg hX.le, inv_inv]
    exact h1

/-- AKMM, p. 219: the fiscal rule (8.3) — "`G_t` increases if `y_t` or `η_t` increase": for
`γ > 0`, `γη/(1+γη)·y` is strictly increasing in `y > 0` (for `η > 0`) and in `η > 0`
(for `y > 0`). -/
theorem sm_fiscal_rule_monotone {γ η η' y y' : ℝ} (hγ : 0 < γ) (hη : 0 < η) (hy : 0 < y) :
    (y < y' → γ * η / (1 + γ * η) * y < γ * η / (1 + γ * η) * y') ∧
      (η < η' → γ * η / (1 + γ * η) * y < γ * η' / (1 + γ * η') * y) := by
  have hX : 0 < 1 + γ * η := by positivity
  refine ⟨fun h => mul_lt_mul_of_pos_left h (by positivity), fun h => ?_⟩
  have hη' : 0 < η' := hη.trans h
  have hX' : 0 < 1 + γ * η' := by positivity
  apply mul_lt_mul_of_pos_right _ hy
  rw [div_lt_div_iff₀ hX hX']
  nlinarith [mul_lt_mul_of_pos_left h hγ]

/-- AKMM, p. 842: `χ = (1/(1+ψ))·(Ḡ/ȳ)/(1 − Ḡ/ȳ)`, written in terms of the share `s = Ḡ/ȳ`. -/
noncomputable def sm_chi (ψ s : ℝ) : ℝ := (1 + ψ)⁻¹ * (s / (1 - s))

/-- **The fiscal multiplier** (AKMM, p. 842, and §8.6.2, p. 231): with `s = Ḡ/ȳ ∈ (0, 1)`,
`(1+χ)⁻¹χ ȳ/Ḡ = 1/(1 + ψ(1 − s))`. -/
theorem sm_multiplier_formula {ψ s : ℝ} (hψ : 0 < ψ) (hs0 : 0 < s) (hs1 : s < 1) :
    (1 + sm_chi ψ s)⁻¹ * sm_chi ψ s * s⁻¹ = 1 / (1 + ψ * (1 - s)) := by
  unfold sm_chi
  have h1 : 0 < 1 - s := by linarith
  have h2 : 0 < 1 + ψ := by linarith
  have h3 : 0 < 1 + ψ * (1 - s) := by nlinarith
  field_simp
  ring

/-- AKMM, p. 231: "the fiscal multiplier will be between zero and one": for `ψ > 0` and
`0 < s < 1`, `0 < 1/(1 + ψ(1 − s)) < 1`. -/
theorem sm_multiplier_mem_Ioo {ψ s : ℝ} (hψ : 0 < ψ) (hs1 : s < 1) :
    1 / (1 + ψ * (1 - s)) ∈ Set.Ioo 0 1 := by
  have h : 0 < ψ * (1 - s) := mul_pos hψ (by linarith)
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by linarith)]
  linarith

/-- **The multiplier from fiscal shocks** (AKMM, p. 219): along the equilibrium of
(8.2)–(8.3) as a function of `η` (for fixed `A`), `dy/dη` and `dG/dη` exist, `dG/dη ≠ 0`, and
`(dy/dη)/(dG/dη) = 1/(1 + ψ(1 − Ḡ/ȳ))`, the slope of the supply curve (`sm_supply_slope`). -/
theorem sm_multiplier_eta {ψ γ η A : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hγη : 0 < γ * η)
    (hA : 0 < A) :
    ∃ dy dG : ℝ, HasDerivAt (fun e => sm_ystar ψ γ e A) dy η ∧
      HasDerivAt (fun e => sm_Gstar ψ γ e A) dG η ∧ dG ≠ 0 ∧
      dy / dG = 1 / (1 + ψ * (1 - sm_Gstar ψ γ η A / sm_ystar ψ γ η A)) := by
  set X := 1 + γ * η with hX_def
  have hX : 0 < X := by linarith
  set q := (1 + ψ)⁻¹ with hq_def
  have hq : 0 < q := inv_pos.2 (by linarith)
  set R := X ^ q with hR_def
  have hR : 0 < R := Real.rpow_pos_of_pos hX _
  have hlin : HasDerivAt (fun e : ℝ => 1 + γ * e) γ η := by
    simpa using ((hasDerivAt_id η).const_mul γ).const_add 1
  have hpow : HasDerivAt (fun e : ℝ => (1 + γ * e) ^ q) (γ * q * X ^ (q - 1)) η :=
    hlin.rpow_const (Or.inl hX.ne')
  have hXq1 : X ^ (q - 1) = R / X := Real.rpow_sub_one hX.ne' q
  have hy : HasDerivAt (fun e => sm_ystar ψ γ e A) (A * (γ * q * X ^ (q - 1))) η := by
    unfold sm_ystar; exact hpow.const_mul A
  have hsh : HasDerivAt (fun e : ℝ => γ * e / (1 + γ * e)) (γ / X ^ 2) η := by
    have := ((hasDerivAt_id η).const_mul γ).div hlin hX.ne'
    convert this using 1
    · funext e; simp
    · simp only [id, mul_one]; rw [hX_def]; field_simp; ring
  have hGfun : (fun e => sm_Gstar ψ γ e A) = fun e => γ * e / (1 + γ * e) * sm_ystar ψ γ e A := by
    funext e
    unfold sm_Gstar sm_cstar sm_ystar sm_lstar
    ring
  have hG : HasDerivAt (fun e => γ * e / (1 + γ * e) * sm_ystar ψ γ e A) _ η := hsh.mul hy
  rw [← hGfun] at hG
  refine ⟨_, _, hy, hG, ?_, ?_⟩
  · rw [hXq1]
    unfold sm_ystar
    rw [← hR_def]
    positivity
  · have hy0 : 0 < sm_ystar ψ γ η A := by unfold sm_ystar; positivity
    have hGy : sm_Gstar ψ γ η A / sm_ystar ψ γ η A = γ * η / X := by
      rw [(sm_ystar_eq (ψ := ψ) (A := A) hγη).2, hX_def]
      field_simp
    rw [hGy, hXq1]
    unfold sm_ystar
    simp only [← hX_def, ← hq_def, ← hR_def]
    rw [hq_def, hX_def]
    have h1 : 0 < 1 + ψ := by linarith
    have h2 : 1 + ψ + γ * η ≠ 0 := by linarith
    have hR0 : R ≠ 0 := hR.ne'
    have hγ0 : γ ≠ 0 := hγ.ne'
    have hA0 : A ≠ 0 := hA.ne'
    field_simp
    ring_nf
    field_simp
    ring

/-- The supply curve (8.2) in polynomial form: for `0 < G < y`, (8.2) holds iff
`y − A^{1+ψ}y^{−ψ} = G`. -/
theorem sm_supply_poly_iff {ψ A y G : ℝ} (hψ : 0 < ψ) (hA : 0 < A) (hy : 0 < y) (hGy : G < y) :
    y = A * (1 - G / y) ^ (-(1 + ψ)⁻¹) ↔ y - A ^ (1 + ψ) * y ^ (-ψ) = G := by
  have hs : 0 < 1 - G / y := by rw [sub_pos, div_lt_one hy]; exact hGy
  have hq : 0 < y / A := div_pos hy hA
  have hp : (1 + ψ) ≠ 0 := by linarith
  rw [Real.rpow_neg hs.le, ← Real.inv_rpow hs.le]
  have : y = A * (1 - G / y)⁻¹ ^ (1 + ψ)⁻¹ ↔ y / A = (1 - G / y)⁻¹ ^ (1 + ψ)⁻¹ := by
    constructor
    · intro h; exact (div_eq_iff hA.ne').2 (by rw [mul_comm]; exact h)
    · intro h; rw [mul_comm]; exact (div_eq_iff hA.ne').1 h
  rw [this, sm_eq_rpow_inv_iff hq (inv_pos.2 hs) hp]
  have hK : A ^ (1 + ψ) * y ^ (-ψ) = y / (y / A) ^ (1 + ψ) := by
    rw [Real.div_rpow hy.le hA.le, Real.rpow_neg hy.le, Real.rpow_add hy, Real.rpow_one]
    have := Real.rpow_pos_of_pos hy ψ
    have := Real.rpow_pos_of_pos hA (1 + ψ)
    field_simp
  rw [hK]
  have hP : 0 < (y / A) ^ (1 + ψ) := Real.rpow_pos_of_pos hq _
  generalize (y / A) ^ (1 + ψ) = P at hP ⊢
  constructor
  · intro h; rw [h]; field_simp; ring
  · intro h
    have : 1 - G / y = P⁻¹ := by rw [← h]; field_simp; ring
    rw [this, inv_inv]

/-- **The fiscal multiplier as the slope of the supply curve** (AKMM, p. 219): at a point
`0 < Ḡ < ȳ` of (8.2), there is a function `φ` with `φ(Ḡ) = ȳ` whose graph is the supply curve
near `Ḡ` (`0 < G < φ(G)` and (8.2) holds at `(G, φ(G))`), and `φ` has strict derivative
`1/(1 + ψ(1 − Ḡ/ȳ))` at `Ḡ`. -/
theorem sm_supply_slope {ψ A ybar Gbar : ℝ} (hψ : 0 < ψ) (hA : 0 < A) (hy : 0 < ybar)
    (hG : 0 < Gbar) (hGy : Gbar < ybar)
    (h82 : ybar = A * (1 - Gbar / ybar) ^ (-(1 + ψ)⁻¹)) :
    ∃ φ : ℝ → ℝ, φ Gbar = ybar ∧
      (∀ᶠ G in 𝓝 Gbar, 0 < G ∧ G < φ G ∧ φ G = A * (1 - G / φ G) ^ (-(1 + ψ)⁻¹)) ∧
      HasStrictDerivAt φ (1 / (1 + ψ * (1 - Gbar / ybar))) Gbar := by
  set g : ℝ → ℝ := fun y => y - A ^ (1 + ψ) * y ^ (-ψ) with hg_def
  have hpoly := (sm_supply_poly_iff hψ hA hy hGy).1 h82
  have hd : HasStrictDerivAt g (1 - A ^ (1 + ψ) * (-ψ * ybar ^ (-ψ - 1))) ybar :=
    (hasStrictDerivAt_id ybar).sub
      ((Real.hasStrictDerivAt_rpow_const_of_ne hy.ne' (-ψ)).const_mul _)
  -- `A^{1+ψ} ȳ^{−ψ−1} = 1 − Ḡ/ȳ`
  have hkey : A ^ (1 + ψ) * ybar ^ (-ψ - 1) = 1 - Gbar / ybar := by
    have h1 : A ^ (1 + ψ) * ybar ^ (-ψ) = ybar - Gbar := by linarith [hpoly]
    rw [Real.rpow_sub_one hy.ne', ← mul_div_assoc, h1]
    field_simp
  have hd' : 1 - A ^ (1 + ψ) * (-ψ * ybar ^ (-ψ - 1)) = 1 + ψ * (1 - Gbar / ybar) := by
    rw [← hkey]; ring
  rw [hd'] at hd
  have hs : 0 < 1 - Gbar / ybar := by rw [sub_pos, div_lt_one hy]; exact hGy
  have hne : 1 + ψ * (1 - Gbar / ybar) ≠ 0 := by nlinarith
  have hgy : g ybar = Gbar := hpoly
  set φ := hd.localInverse g _ ybar hne with hφ
  have hinv := hd.to_localInverse hne
  rw [hgy] at hinv
  have hφG : φ Gbar = ybar := by
    have := (hd.eventually_left_inverse hne).self_of_nhds
    rw [hgy] at this; exact this
  refine ⟨φ, hφG, ?_, by rw [one_div]; exact hinv⟩
  have hcont : ContinuousAt φ Gbar := hinv.hasDerivAt.continuousAt
  have hright := hd.eventually_right_inverse hne
  rw [hgy] at hright
  have hpos : ∀ᶠ G in 𝓝 Gbar, 0 < φ G :=
    hcont.eventually (lt_mem_nhds (by rw [hφG]; exact hy))
  have hdiff : ∀ᶠ G in 𝓝 Gbar, G < φ G := by
    have hc2 : ContinuousAt (fun G => φ G - G) Gbar := hcont.sub continuousAt_id
    have := hc2.eventually (lt_mem_nhds (show (0 : ℝ) < φ Gbar - Gbar by
      rw [hφG]; linarith))
    exact this.mono fun G hG => by linarith
  have hGpos : ∀ᶠ G in 𝓝 Gbar, 0 < G := lt_mem_nhds hG
  filter_upwards [hpos, hdiff, hGpos, hright] with G h1 h2 h3 h4
  refine ⟨h3, h2, ?_⟩
  exact (sm_supply_poly_iff hψ hA h1 h2).2 h4

/-- **Appendix 8.A.2, `∂y/∂A`** (AKMM, p. 842): at a point `0 < Ḡ < ȳ` of (8.2) with TFP `Ā`,
holding `G = Ḡ`, output as a function of `A` near `Ā` (the local inverse of
`y ↦ y(1 − Ḡ/y)^{1/(1+ψ)}`, which is (8.19)) has strict derivative `(1+χ)⁻¹ȳ/Ā`. -/
theorem sm_supply_dA {ψ Abar ybar Gbar : ℝ} (hψ : 0 < ψ) (hy : 0 < ybar) (hG : 0 < Gbar)
    (hGy : Gbar < ybar) (h82 : ybar = Abar * (1 - Gbar / ybar) ^ (-(1 + ψ)⁻¹)) :
    ∃ φ : ℝ → ℝ, φ Abar = ybar ∧
      (∀ᶠ A in 𝓝 Abar, φ A * (1 - Gbar / φ A) ^ (1 + ψ)⁻¹ = A) ∧
      HasStrictDerivAt φ ((1 + sm_chi ψ (Gbar / ybar))⁻¹ * (ybar / Abar)) Abar := by
  set q := (1 + ψ)⁻¹ with hq_def
  set s := Gbar / ybar with hs_def
  have hs1 : 0 < 1 - s := by rw [sub_pos, hs_def, div_lt_one hy]; exact hGy
  have hp : 0 < 1 + ψ := by linarith
  -- `Ā = ȳ(1 − s)^q`
  have hAbar : Abar = ybar * (1 - s) ^ q := by
    have h1 : (1 - s) ^ (-q) = ((1 - s) ^ q)⁻¹ := Real.rpow_neg hs1.le q
    rw [h1] at h82
    have : 0 < (1 - s) ^ q := Real.rpow_pos_of_pos hs1 q
    field_simp at h82
    linarith
  set a : ℝ → ℝ := fun y => y * (1 - Gbar / y) ^ q with ha_def
  have hin : HasStrictDerivAt (fun y : ℝ => 1 - Gbar / y) (Gbar / ybar ^ 2) ybar := by
    have := ((hasStrictDerivAt_inv hy.ne').const_mul Gbar).const_sub 1
    convert this using 1
    · funext y; simp [div_eq_mul_inv]
    · field_simp
  have hpow : HasStrictDerivAt (fun y : ℝ => (1 - Gbar / y) ^ q)
      (q * (1 - s) ^ (q - 1) * (Gbar / ybar ^ 2)) ybar := by
    have h := (Real.hasStrictDerivAt_rpow_const_of_ne hs1.ne' q).comp ybar hin
    convert h using 1
    rfl
  have hd : HasStrictDerivAt a (1 * (1 - s) ^ q + ybar * (q * (1 - s) ^ (q - 1) *
      (Gbar / ybar ^ 2))) ybar := (hasStrictDerivAt_id ybar).mul hpow
  have hR : 0 < (1 - s) ^ q := Real.rpow_pos_of_pos hs1 q
  have hq1 : (1 - s) ^ (q - 1) = (1 - s) ^ q / (1 - s) := Real.rpow_sub_one hs1.ne' q
  have hval : 1 * (1 - s) ^ q + ybar * (q * (1 - s) ^ (q - 1) * (Gbar / ybar ^ 2)) =
      (1 - s) ^ q * (1 + q * s / (1 - s)) := by
    rw [hq1, hs_def]; field_simp
  rw [hval] at hd
  have hne : (1 - s) ^ q * (1 + q * s / (1 - s)) ≠ 0 := by
    have : 0 ≤ q * s / (1 - s) := by
      have hs0 : 0 ≤ s := by rw [hs_def]; positivity
      positivity
    positivity
  have hay : a ybar = Abar := by rw [hAbar]
  set φ := hd.localInverse a _ ybar hne with hφ
  have hinv := hd.to_localInverse hne
  rw [hay] at hinv
  have hφA : φ Abar = ybar := by
    have := (hd.eventually_left_inverse hne).self_of_nhds
    rw [hay] at this; exact this
  have hright := hd.eventually_right_inverse hne
  rw [hay] at hright
  refine ⟨φ, hφA, hright, ?_⟩
  convert hinv using 1
  unfold sm_chi
  rw [hAbar]
  field_simp
  rw [hq_def]
  field_simp

/-- **Appendix 8.A.2, the total differential** (AKMM, p. 842): for `1 + χ ≠ 0`,
`dy = (ȳ/Ā)dA + χ((ȳ/Ḡ)dG − dy)` iff `dy = (1+χ)⁻¹((ȳ/Ā)dA + χ(ȳ/Ḡ)dG)`; and the two partial
derivatives `sm_supply_dA` and `sm_supply_slope` are these coefficients:
`1/(1 + ψ(1 − Ḡ/ȳ)) = (1+χ)⁻¹χ ȳ/Ḡ`. -/
theorem appendix_8A_2_total_differential {ψ χ ybar Abar Gbar dA dG dy : ℝ}
    (hχ : 1 + χ ≠ 0) (hψ : 0 < ψ) (hG : 0 < Gbar) (hGy : Gbar < ybar) :
    (dy = ybar / Abar * dA + χ * (ybar / Gbar * dG - dy) ↔
      dy = (1 + χ)⁻¹ * (ybar / Abar * dA + χ * (ybar / Gbar) * dG)) ∧
      1 / (1 + ψ * (1 - Gbar / ybar)) =
        (1 + sm_chi ψ (Gbar / ybar))⁻¹ * sm_chi ψ (Gbar / ybar) * (ybar / Gbar) := by
  have hy : 0 < ybar := hG.trans hGy
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · rw [eq_inv_mul_iff_mul_eq₀ hχ]; linarith
  · rw [eq_inv_mul_iff_mul_eq₀ hχ] at h; linarith
  · have := sm_multiplier_formula hψ (div_pos hG hy) (by rw [div_lt_one hy]; exact hGy)
    rw [← this, inv_div]

/-- **Appendix 8.A.2 at the steady state** (AKMM, p. 842): with `η̄ = 1`, (8.3) gives
`Ḡ/ȳ = γ/(1+γ)`; then `χ = γ/(1+ψ)` and the multiplier is `(1+γ)/(1+γ+ψ)`. -/
theorem appendix_8A_2_steady {ψ γ A : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hA : 0 < A) :
    sm_Gstar ψ γ 1 A / sm_ystar ψ γ 1 A = γ / (1 + γ) ∧
      sm_chi ψ (γ / (1 + γ)) = γ / (1 + ψ) ∧
      1 / (1 + ψ * (1 - γ / (1 + γ))) = (1 + γ) / (1 + γ + ψ) := by
  have hγ1 : 0 < γ * 1 := by linarith
  have hy : 0 < sm_ystar ψ γ 1 A := by unfold sm_ystar; positivity
  have h1 : 0 < 1 + ψ := by linarith
  have h2 : 0 < 1 + γ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [(sm_ystar_eq (ψ := ψ) (A := A) hγ1).2]; field_simp
  · unfold sm_chi; field_simp; ring
  · have : 1 + ψ * (1 - γ / (1 + γ)) = (1 + γ + ψ) / (1 + γ) := by field_simp; ring
    rw [this, one_div_div]

/-- **(8.5)** (AKMM, p. 222): the log-linear supply curve `ŷ = χ/(1+χ)·Ĝ + 1/(1+χ)·Â` is
`ŷ = Â + χ(Ĝ − ŷ)`, and its coefficients are the elasticities of output: with
`m = 1/(1 + ψ(1 − s))` (the slope, `sm_supply_slope`) and `a = (1+χ)⁻¹ȳ/Ā` (`sm_supply_dA`),
`m·Ḡ/ȳ = χ/(1+χ)` and `a·Ā/ȳ = 1/(1+χ)`, for `s = Ḡ/ȳ ∈ (0, 1)` and `χ = χ(ψ, s)`. -/
theorem eq_8_5 {ψ χ ybar Abar Gbar yh Gh Ah : ℝ} (hχ : 1 + χ ≠ 0) (hψ : 0 < ψ)
    (hA : 0 < Abar) (hG : 0 < Gbar) (hGy : Gbar < ybar) :
    (yh = χ / (1 + χ) * Gh + 1 / (1 + χ) * Ah ↔ yh = Ah + χ * (Gh - yh)) ∧
      1 / (1 + ψ * (1 - Gbar / ybar)) * (Gbar / ybar) =
        sm_chi ψ (Gbar / ybar) / (1 + sm_chi ψ (Gbar / ybar)) ∧
      (1 + sm_chi ψ (Gbar / ybar))⁻¹ * (ybar / Abar) * (Abar / ybar) =
        1 / (1 + sm_chi ψ (Gbar / ybar)) := by
  have hy : 0 < ybar := hG.trans hGy
  have hs1 : Gbar / ybar < 1 := by rw [div_lt_one hy]; exact hGy
  have hc : 0 ≤ sm_chi ψ (Gbar / ybar) := by
    unfold sm_chi
    have : 0 < 1 - Gbar / ybar := by linarith
    positivity
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · rw [h]; field_simp; ring
  · field_simp; linarith
  · rw [sm_multiplier_formula hψ (div_pos hG hy) hs1 |>.symm]
    have : 1 + sm_chi ψ (Gbar / ybar) ≠ 0 := by linarith
    field_simp
  · field_simp

/-- **(8.5) in logs** (AKMM, p. 222): if `φ` is the supply curve near `Ḡ` with
`φ(Ḡ) = ȳ > 0` and slope `m` (as in `sm_supply_slope`), then `x ↦ log φ(eˣ)` has derivative
`mḠ/ȳ` at `log Ḡ`: the coefficient of `Ĝ` in (8.5) is the elasticity. -/
theorem eq_8_5_log {φ : ℝ → ℝ} {m ybar Gbar : ℝ} (hG : 0 < Gbar) (hy : 0 < ybar)
    (hφ : φ Gbar = ybar) (hd : HasStrictDerivAt φ m Gbar) :
    HasDerivAt (fun x => Real.log (φ (Real.exp x))) (m * Gbar / ybar) (Real.log Gbar) := by
  have he : HasDerivAt Real.exp Gbar (Real.log Gbar) := by
    simpa [Real.exp_log hG] using Real.hasDerivAt_exp (Real.log Gbar)
  have hφ' : HasDerivAt φ m (Real.exp (Real.log Gbar)) := by
    rw [Real.exp_log hG]; exact hd.hasDerivAt
  have hc := hφ'.comp (Real.log Gbar) he
  have hl := (Real.hasDerivAt_log (by
    simp only [Function.comp_apply]; rw [Real.exp_log hG, hφ]; exact hy.ne')).comp
    (Real.log Gbar) hc
  convert hl using 1
  · rfl
  · change m * Gbar / ybar = (φ (Real.exp (Real.log Gbar)))⁻¹ * (m * Gbar)
    rw [Real.exp_log hG, hφ]
    field_simp

/-- **(8.6)** (AKMM, p. 223): by (8.3), `log G − log y = log(γη/(1+γη))`; its derivative in
`log η` at `η = 1` is `1/(1+γ)`, so `Ĝ = ŷ + η̂/(1+γ)`. -/
theorem eq_8_6 {γ η y G : ℝ} (hγ : 0 < γ) (hη : 0 < η) (hy : 0 < y)
    (h83 : G = γ * η / (1 + γ * η) * y) :
    Real.log G - Real.log y = Real.log (γ * η / (1 + γ * η)) ∧
      HasDerivAt (fun x => Real.log (γ * Real.exp x / (1 + γ * Real.exp x))) (1 / (1 + γ)) 0 := by
  have hX : 0 < 1 + γ * η := by positivity
  refine ⟨?_, ?_⟩
  · rw [h83, Real.log_mul (by positivity) hy.ne']; ring
  · have hfun : (fun x => Real.log (γ * Real.exp x / (1 + γ * Real.exp x))) =
        fun x => Real.log γ + x - Real.log (1 + γ * Real.exp x) := by
      funext x
      have : 0 < 1 + γ * Real.exp x := by positivity
      rw [Real.log_div (by positivity) this.ne', Real.log_mul hγ.ne' (Real.exp_pos x).ne',
        Real.log_exp]
    rw [hfun]
    have h1 : HasDerivAt (fun x => 1 + γ * Real.exp x) (γ * Real.exp 0) 0 :=
      ((Real.hasDerivAt_exp 0).const_mul γ).const_add 1
    have h2 := h1.log (by positivity)
    have h3 := ((hasDerivAt_id (0 : ℝ)).const_add (Real.log γ)).sub h2
    convert h3 using 1
    · rfl
    · simp only [Real.exp_zero, mul_one]
      have : 0 < 1 + γ := by linarith
      field_simp
      ring

/-- **Footnote 3** (AKMM, p. 223): the fiscal multiplier in levels is the effect in logs scaled
by `ȳ/Ḡ`: `(χ/(1+χ))·(ȳ/Ḡ) = (1+χ)⁻¹χ ȳ/Ḡ`, the multiplier of Appendix 8.A.2. -/
theorem fn_3 (χ ybar Gbar : ℝ) :
    χ / (1 + χ) * (ybar / Gbar) = (1 + χ)⁻¹ * χ * (ybar / Gbar) := by
  rw [div_eq_inv_mul]

/-- AKMM, p. 234: "the multiplier will be larger if households are more willing to vary their
labor supply": in the static model the multiplier `1/(1 + ψ(1 − s))` is strictly decreasing in
the inverse Frisch elasticity `ψ ≥ 0`, for `0 < s < 1`. -/
theorem sm_multiplier_antitone_psi {ψ ψ' s : ℝ} (hψ : 0 ≤ ψ) (hψψ : ψ < ψ') (hs1 : s < 1) :
    1 / (1 + ψ' * (1 - s)) < 1 / (1 + ψ * (1 - s)) := by
  have h1 : 0 < 1 - s := by linarith
  have h2 : 0 < 1 + ψ * (1 - s) := by nlinarith
  apply one_div_lt_one_div_of_lt h2
  nlinarith

end AKMM.QuantitativeMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The identification challenge, natural experiments and the recursive form

AKMM, §8.2, p. 219 (the identification challenge); §8.3, p. 220 (natural experiments: an
instrument `z` correlated with `G` but not with `A`); §8.4, (8.5)–(8.6) and (8.8)–(8.9),
pp. 222–224; and §8.7, p. 232 ("any changes in `G/y` are due to fiscal shocks").

The log-linear system (8.5)–(8.6) is
`ŷ = χ/(1+χ)·Ĝ + 1/(1+χ)·Â`, `Ĝ = ŷ + η̂/(1+γ)`. Random vectors are square-integrable maps
`Ω → I → ℝ`, and second moments `E[vw']` are Miao's `var_mom` with the calculus of
`PartialInformation.KFMoments` (`kf_L2`, `kf_app`, `kf_mom_app_left`, `kf_mom_app_right`).

* (8.5)–(8.6) iff (8.8)–(8.9) with `ĝ = Ĝ − ŷ` (`eq_8_8_8_9`), and the solved system expresses
  `(ŷ, Ĝ)` in terms of the structural shocks `(η̂, Â)` through `id_impact` (`id_solution`), so
  `Ĝ` is correlated with `Â` (`id_G_correlated_with_A`): the endogeneity of p. 223.
* **The identification challenge**: with uncorrelated shocks, the least-squares slope of `ŷ` on
  `Ĝ` equals the causal effect `χ/(1+χ)` iff `Var(Â) = 0` (`id_ols_slope`).
* **Natural experiments** (§8.3): an instrument `z` uncorrelated with `Â` and correlated with
  `η̂` recovers it, `Cov(ŷ, z)/Cov(Ĝ, z) = χ/(1+χ)` (`id_iv`).
* **The restriction identifies** (§8.4, p. 223): imposing the coefficient `1` on `ŷ` in (8.6),
  `Var(ĝ) = Var(η̂)/(1+γ)²` and `χ` are functions of the second moments of `(ŷ, Ĝ)`
  (`id_restriction_identifies`); and `ĝ = Ĝ − ŷ` is uncorrelated with `Â`, so movements in
  `G/y` are fiscal shocks (`id_g_exogenous`, §8.7, p. 232).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Matrix Miao.PartialInformation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **(8.8)–(8.9)** (AKMM, pp. 223–224): for `1 + χ ≠ 0` and `1 + γ ≠ 0`, the system
(8.5)–(8.6) holds iff, with `ĝ = Ĝ − ŷ`, `ŷ = χĝ + Â` and `ĝ = η̂/(1+γ)`. -/
theorem eq_8_8_8_9 {χ γ yh Gh Ah eh : ℝ} (hχ : 1 + χ ≠ 0) :
    (yh = χ / (1 + χ) * Gh + 1 / (1 + χ) * Ah ∧ Gh = yh + 1 / (1 + γ) * eh) ↔
      (yh = χ * (Gh - yh) + Ah ∧ Gh - yh = 1 / (1 + γ) * eh) := by
  have h1 : yh = χ / (1 + χ) * Gh + 1 / (1 + χ) * Ah ↔ yh = χ * (Gh - yh) + Ah := by
    constructor
    · intro h; rw [h]; field_simp; ring
    · intro h; field_simp; linarith
  rw [h1]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨h, by linarith⟩
  · rintro ⟨h, h'⟩; exact ⟨h, by linarith⟩

/-- AKMM, (8.8)–(8.9): the impact matrix from the structural shocks `(η̂, Â)` to the observables
`(ŷ, Ĝ)`: `ŷ = χη̂/(1+γ) + Â`, `Ĝ = (1+χ)η̂/(1+γ) + Â`. -/
noncomputable def id_impact (γ χ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![χ / (1 + γ), 1; (1 + χ) / (1 + γ), 1]

/-- AKMM, p. 223: the solution of (8.5)–(8.6). For `1 + χ ≠ 0`, `(ŷ, Ĝ)` solves the system with
shocks `(η̂, Â)` iff `(ŷ, Ĝ) = id_impact γ χ · (η̂, Â)`. -/
theorem id_solution {χ γ yh Gh Ah eh : ℝ} (hχ : 1 + χ ≠ 0) :
    (yh = χ / (1 + χ) * Gh + 1 / (1 + χ) * Ah ∧ Gh = yh + 1 / (1 + γ) * eh) ↔
      ![yh, Gh] = id_impact γ χ *ᵥ ![eh, Ah] := by
  rw [eq_8_8_8_9 hχ]
  have hv : ∀ a b c d : ℝ, ![a, b] = ![c, d] ↔ a = c ∧ b = d := by
    intro a b c d
    constructor
    · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨rfl, rfl⟩; rfl
  have hm : id_impact γ χ *ᵥ ![eh, Ah] = ![χ / (1 + γ) * eh + Ah, (1 + χ) / (1 + γ) * eh + Ah] := by
    ext i; fin_cases i <;> simp [id_impact, mulVec, dotProduct, Fin.sum_univ_two]
  rw [hm, hv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [h1, h2]; ring
    · have : Gh = yh + 1 / (1 + γ) * eh := by linarith
      rw [this, h1, h2]; ring
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [h1, h2]; ring
    · rw [h1, h2]; ring

/-- Second moments of the observables: `E[(Me)(Me)'] = M E[ee'] M'`. -/
theorem id_mom_obs {e : Ω → Fin 2 → ℝ} (he : kf_L2 μ e) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    var_mom μ (kf_app M e) (kf_app M e) = M * var_mom μ e e * Mᵀ := by
  rw [kf_mom_app_left he (kf_L2_app he M), kf_mom_app_right he he]
  rw [Matrix.mul_assoc]

/-- AKMM, p. 223: "`G_t` is correlated with `A_t`": with uncorrelated shocks of variances
`σ²_η, σ²_A`, `Cov(Ĝ, Â) = σ²_A`. -/
theorem id_G_correlated_with_A {e : Ω → Fin 2 → ℝ} (he : kf_L2 μ e) {γ χ sη sA : ℝ}
    (hD : var_mom μ e e = !![sη, 0; 0, sA]) :
    var_mom μ (kf_app (id_impact γ χ) e) e 1 1 = sA := by
  rw [kf_mom_app_left he he, hD]
  simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The identification challenge** (AKMM, p. 219): with uncorrelated shocks of variances
`σ²_η, σ²_A ≥ 0`, `a = σ²_η/(1+γ)²`, the moments are `Cov(ŷ, Ĝ) = χ(1+χ)a + σ²_A`,
`Var(Ĝ) = (1+χ)²a + σ²_A`; when `Var(Ĝ) > 0` and `1 + χ > 0`, the least-squares slope
`Cov(ŷ, Ĝ)/Var(Ĝ)` equals the causal effect `χ/(1+χ)` iff `σ²_A = 0`. -/
theorem id_ols_slope {e : Ω → Fin 2 → ℝ} (he : kf_L2 μ e) {γ χ sη sA : ℝ}
    (hD : var_mom μ e e = !![sη, 0; 0, sA]) (hγ : 1 + γ ≠ 0) (hχ : 0 < 1 + χ) :
    let V := var_mom μ (kf_app (id_impact γ χ) e) (kf_app (id_impact γ χ) e)
    V 0 1 = χ * (1 + χ) * (sη / (1 + γ) ^ 2) + sA ∧
      V 1 1 = (1 + χ) ^ 2 * (sη / (1 + γ) ^ 2) + sA ∧
      (0 < V 1 1 → (V 0 1 / V 1 1 = χ / (1 + χ) ↔ sA = 0)) := by
  intro V
  have hV : V = id_impact γ χ * !![sη, 0; 0, sA] * (id_impact γ χ)ᵀ := by
    simp only [V]; rw [id_mom_obs he, hD]
  have h01 : V 0 1 = χ * (1 + χ) * (sη / (1 + γ) ^ 2) + sA := by
    rw [hV]; simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
  have h11 : V 1 1 = (1 + χ) ^ 2 * (sη / (1 + γ) ^ 2) + sA := by
    rw [hV]; simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
  refine ⟨h01, h11, fun hpos => ?_⟩
  rw [div_eq_div_iff hpos.ne' hχ.ne', h01, h11]
  constructor
  · intro h
    have : sA * (1 + χ - χ) = 0 := by nlinarith
    simpa using this
  · intro h; rw [h]; ring

/-- **Natural experiments** (AKMM, §8.3, p. 220): an instrument `z` uncorrelated with the TFP
shock (`Cov(Â, z) = 0`) and correlated with the fiscal shock (`Cov(η̂, z) ≠ 0`) identifies the
causal effect: `Cov(ŷ, z)/Cov(Ĝ, z) = χ/(1+χ)`. -/
theorem id_iv {ι : Type*} {e : Ω → Fin 2 → ℝ} {z : Ω → ι → ℝ} (he : kf_L2 μ e)
    (hz : kf_L2 μ z) {γ χ : ℝ} (hγ : 1 + γ ≠ 0) (hχ : 1 + χ ≠ 0) (j : ι)
    (hexog : var_mom μ e z 1 j = 0) (hrel : var_mom μ e z 0 j ≠ 0) :
    var_mom μ (kf_app (id_impact γ χ) e) z 0 j / var_mom μ (kf_app (id_impact γ χ) e) z 1 j =
      χ / (1 + χ) := by
  rw [kf_mom_app_left he hz]
  simp only [id_impact, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, hexog, mul_zero, add_zero]
  field_simp

/-- **The restriction identifies `χ`** (AKMM, §8.4, p. 223): with the coefficient on `ŷ` in
(8.6) restricted to `1` and uncorrelated shocks, the second moments `V` of `(ŷ, Ĝ)` determine
`Var(ĝ) = σ²_η/(1+γ)² = V₁₁ − 2V₀₁ + V₀₀` and, when it is nonzero,
`χ = (V₁₁ − V₀₁)/(V₁₁ − 2V₀₁ + V₀₀) − 1`. -/
theorem id_restriction_identifies {e : Ω → Fin 2 → ℝ} (he : kf_L2 μ e) {γ χ sη sA : ℝ}
    (hD : var_mom μ e e = !![sη, 0; 0, sA]) (hγ : 1 + γ ≠ 0) :
    let V := var_mom μ (kf_app (id_impact γ χ) e) (kf_app (id_impact γ χ) e)
    V 1 1 - 2 * V 0 1 + V 0 0 = sη / (1 + γ) ^ 2 ∧
      (sη ≠ 0 → χ = (V 1 1 - V 0 1) / (V 1 1 - 2 * V 0 1 + V 0 0) - 1) := by
  intro V
  have hV : V = id_impact γ χ * !![sη, 0; 0, sA] * (id_impact γ χ)ᵀ := by
    simp only [V]; rw [id_mom_obs he, hD]
  have h00 : V 0 0 = χ ^ 2 * (sη / (1 + γ) ^ 2) + sA := by
    rw [hV]; simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
  have h01 : V 0 1 = χ * (1 + χ) * (sη / (1 + γ) ^ 2) + sA := by
    rw [hV]; simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
  have h11 : V 1 1 = (1 + χ) ^ 2 * (sη / (1 + γ) ^ 2) + sA := by
    rw [hV]; simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
  have hvar : V 1 1 - 2 * V 0 1 + V 0 0 = sη / (1 + γ) ^ 2 := by rw [h00, h01, h11]; ring
  refine ⟨hvar, fun hs => ?_⟩
  rw [hvar, h01, h11]
  have : sη / (1 + γ) ^ 2 ≠ 0 := div_ne_zero hs (pow_ne_zero 2 hγ)
  field_simp
  ring

/-- AKMM, §8.4, p. 224 and §8.7, p. 232: `ĝ = Ĝ − ŷ = η̂/(1+γ)` is uncorrelated with `Â`, "so
we can attribute any movements in `g_t` to fiscal shocks". -/
theorem id_g_exogenous {e : Ω → Fin 2 → ℝ} (he : kf_L2 μ e) {γ χ sη sA : ℝ}
    (hD : var_mom μ e e = !![sη, 0; 0, sA]) :
    var_mom μ (kf_app (!![(-1 : ℝ), 1] * id_impact γ χ) e) e 0 1 = 0 := by
  rw [kf_mom_app_left he he, hD]
  simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]

end AKMM.QuantitativeMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Structural VARs: the reduced form and the identification problem

AKMM, §8.4, (8.4) and (8.7), pp. 222–223, with footnote 4.

The structural system (8.4) is `B₀Yₜ = B₁Yₜ₋₁ + ⋯ + B_JYₜ₋J + εₜ` with `Var(εₜ) = I`. We prove:

* premultiplying by `B₀⁻¹` gives the reduced form (8.7) `Yₜ = A₁Yₜ₋₁ + ⋯ + uₜ` with
  `A_j = B₀⁻¹B_j`, `uₜ = B₀⁻¹εₜ`, and conversely (`eq_8_7`, `eq_8_7_process`);
* the normalisation `Var(εₜ) = I` is without loss of generality (`sv_normalisation`);
* `Var(uₜ) = B₀⁻¹B₀⁻¹'` (`sv_var_u`);
* **non-identification by rotations**: for an orthogonal `F` the rotated model `b F'`, `Fε` has
  the same reduced-form residuals and `bF'(bF')' = bb'` (`sv_rotation`, `sv_rotation_shocks`);
  conversely every `b'` with `b'b'' = bb'` is `bF'` for an orthogonal `F` when `b` is invertible
  (`sv_rotation_converse`); so `Var(u)` does not determine `B₀⁻¹` (`sv_not_identified`);
* **the restriction count** (footnote 4): the symmetric `n × n` matrices form a space of
  dimension `n(n+1)/2` (`sv_finrank_symm`), the unrestricted `B₀` has `n²` entries, and the
  difference is `n(n−1)/2`, `= 1` for `n = 2` (`sv_restriction_count`).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Matrix Miao.PartialInformation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **(8.7)** (AKMM, p. 223): for invertible `B₀`, the structural equation
`B₀y = Σⱼ Bⱼxⱼ + ε` (`xⱼ` the lags) holds iff the reduced form
`y = Σⱼ (B₀⁻¹Bⱼ)xⱼ + B₀⁻¹ε` holds. -/
theorem eq_8_7 {J : Type*} [Fintype J] {B0 : Matrix n n ℝ} (hB0 : IsUnit B0.det)
    (B : J → Matrix n n ℝ) (y ε : n → ℝ) (x : J → n → ℝ) :
    B0 *ᵥ y = ∑ j, B j *ᵥ x j + ε ↔ y = ∑ j, (B0⁻¹ * B j) *ᵥ x j + B0⁻¹ *ᵥ ε := by
  have hl : B0⁻¹ * B0 = 1 := nonsing_inv_mul B0 hB0
  have hr : B0 * B0⁻¹ = 1 := mul_nonsing_inv B0 hB0
  constructor
  · intro h
    have := congrArg (fun v => B0⁻¹ *ᵥ v) h
    simp only [mulVec_mulVec, hl, one_mulVec, mulVec_add, mulVec_sum] at this
    exact this
  · intro h
    rw [h, mulVec_add, mulVec_sum, mulVec_mulVec, hr, one_mulVec]
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, hr, Matrix.one_mul]

/-- **(8.4) ⟹ (8.7) along a path** (AKMM, pp. 222–223): if
`B₀Y_{t+J} = Σ_{j<J} B_{j+1}Y_{t+J−1−j} + ε_{t+J}` for all `t`, then
`Y_{t+J} = Σ_j A_{j+1}Y_{t+J−1−j} + u_{t+J}` with `A = B₀⁻¹B`, `u = B₀⁻¹ε`, and conversely. -/
theorem eq_8_7_process {J : ℕ} {B0 : Matrix n n ℝ} (hB0 : IsUnit B0.det)
    (B : Fin J → Matrix n n ℝ) (Y ε : ℕ → n → ℝ) :
    (∀ t, B0 *ᵥ Y (t + J) = ∑ j : Fin J, B j *ᵥ Y (t + J - 1 - j) + ε (t + J)) ↔
      ∀ t, Y (t + J) = ∑ j : Fin J, (B0⁻¹ * B j) *ᵥ Y (t + J - 1 - j) + B0⁻¹ *ᵥ ε (t + J) :=
  forall_congr' fun t => eq_8_7 hB0 B (Y (t + J)) (ε (t + J)) fun j => Y (t + J - 1 - j)

/-- **`Var(uₜ) = B₀⁻¹B₀⁻¹'`** (AKMM, p. 223): if `Var(εₜ) = I` then the reduced-form residual
`uₜ = B₀⁻¹εₜ` has second-moment matrix `B₀⁻¹(B₀⁻¹)'`. -/
theorem sv_var_u {ε : Ω → n → ℝ} (hε : kf_L2 μ ε) (hI : var_mom μ ε ε = 1)
    (B0 : Matrix n n ℝ) :
    var_mom μ (kf_app B0⁻¹ ε) (kf_app B0⁻¹ ε) = B0⁻¹ * (B0⁻¹)ᵀ := by
  rw [kf_mom_app_left hε (kf_L2_app hε _), kf_mom_app_right hε hε, hI, Matrix.one_mul]

/-- **Rotations** (AKMM, p. 223): if `bb' = Var(u)` and `F'F = I`, then
`(bF')(bF')' = Var(u)`. -/
theorem sv_rotation {b S F : Matrix n n ℝ} (hb : b * bᵀ = S)
    (hF : F ∈ Matrix.orthogonalGroup n ℝ) : (b * Fᵀ) * (b * Fᵀ)ᵀ = S := by
  rw [Matrix.mem_orthogonalGroup_iff'] at hF
  rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Fᵀ, hF,
    Matrix.one_mul, hb]

/-- **Observational equivalence** (AKMM, p. 223): rotating the structural shocks, `ε' = Fε`
with `F` orthogonal, gives shocks with `Var(ε') = I` and the impact matrix `bF'` produces the same
reduced-form residuals: `(bF')ε' = bε`. -/
theorem sv_rotation_shocks {ε : Ω → n → ℝ} (hε : kf_L2 μ ε) (hI : var_mom μ ε ε = 1)
    {b F : Matrix n n ℝ} (hF : F ∈ Matrix.orthogonalGroup n ℝ) :
    var_mom μ (kf_app F ε) (kf_app F ε) = 1 ∧
      kf_app (b * Fᵀ) (kf_app F ε) = kf_app b ε := by
  have hF' := hF
  rw [Matrix.mem_orthogonalGroup_iff] at hF
  rw [Matrix.mem_orthogonalGroup_iff'] at hF'
  refine ⟨?_, ?_⟩
  · rw [kf_mom_app_left hε (kf_L2_app hε _), kf_mom_app_right hε hε, hI, Matrix.one_mul, hF]
  · funext ω
    simp only [kf_app, mulVec_mulVec, Matrix.mul_assoc, hF', Matrix.mul_one]

/-- **Every observationally equivalent impact matrix is a rotation** (AKMM, p. 223): if `b` is
invertible and `b'b'' = bb'`, then `b' = bF'` for some orthogonal `F`. -/
theorem sv_rotation_converse {b b' : Matrix n n ℝ} (hb : IsUnit b.det)
    (h : b' * b'ᵀ = b * bᵀ) : ∃ F ∈ Matrix.orthogonalGroup n ℝ, b' = b * Fᵀ := by
  refine ⟨(b⁻¹ * b')ᵀ, ?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff', transpose_transpose, transpose_mul]
    calc b⁻¹ * b' * (b'ᵀ * b⁻¹ᵀ) = b⁻¹ * (b' * b'ᵀ) * b⁻¹ᵀ := by simp only [Matrix.mul_assoc]
      _ = (b⁻¹ * b) * (b⁻¹ * b)ᵀ := by
          rw [h, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul b hb, transpose_one, Matrix.one_mul]
  · rw [transpose_transpose, ← Matrix.mul_assoc, mul_nonsing_inv b hb, Matrix.one_mul]

/-- **`Var(u)` does not identify `B₀⁻¹`** (AKMM, p. 223): the identity and the permutation
`[[0, 1], [1, 0]]` are different impact matrices with the same `bb' = I`. -/
theorem sv_not_identified :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ =
        !![(0 : ℝ), 1; 1, 0] * (!![(0 : ℝ), 1; 1, 0])ᵀ ∧
      (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ !![(0 : ℝ), 1; 1, 0] := by
  refine ⟨?_, fun h => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have := congrFun (congrFun h 0) 0
    simp at this

/-- The symmetric `n × n` matrices, `M' = M`. -/
def sv_symm (k : ℕ) : Submodule ℝ (Matrix (Fin k) (Fin k) ℝ) where
  carrier := {M | Mᵀ = M}
  add_mem' := by
    intro a b ha hb
    change (a + b)ᵀ = a + b
    rw [transpose_add]
    exact congrArg₂ (· + ·) ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c M hM
    change (c • M)ᵀ = c • M
    rw [transpose_smul]
    exact congrArg (c • ·) hM

/-- The index set `{(i, j) : i ≤ j}` of the distinct entries of a symmetric matrix. -/
abbrev sv_upper (k : ℕ) := {p : Fin k × Fin k // p.1 ≤ p.2}

/-- `#{(i, j) : i ≤ j} = k(k+1)/2`, as `2·# = k(k+1)`. -/
theorem sv_card_upper (k : ℕ) : 2 * Fintype.card (sv_upper k) = k * (k + 1) := by
  rw [Fintype.card_subtype]
  have hc : (Finset.univ.filter fun p : Fin k × Fin k => p.1 ≤ p.2).card =
      ∑ i : Fin k, (k - i) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun j : Fin k => i ≤ j) = Finset.Ici i := by
      ext j; simp
    rw [this, Fin.card_Ici]
  have h2 : ∑ i ∈ Finset.range k, (k - i) = ∑ i ∈ Finset.range k, (i + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    omega
  rw [hc, Fin.sum_univ_eq_sum_range (fun i => k - i) k, h2, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have h3 := Finset.sum_range_id_mul_two k
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel] at h3
    nlinarith [h3]

/-- The linear map reading off the entries `M_{ij}`, `i ≤ j`. -/
def sv_upperMap (k : ℕ) : sv_symm k →ₗ[ℝ] (sv_upper k → ℝ) where
  toFun M p := (M : Matrix (Fin k) (Fin k) ℝ) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sv_upperMap_bijective (k : ℕ) : Function.Bijective (sv_upperMap k) := by
  constructor
  · intro M N h
    apply Subtype.ext
    ext i j
    rcases le_total i j with hij | hij
    · exact congrFun h ⟨(i, j), hij⟩
    · have h1 := congrFun h ⟨(j, i), hij⟩
      simp only [sv_upperMap, LinearMap.coe_mk] at h1
      have hM : (M : Matrix (Fin k) (Fin k) ℝ)ᵀ = M := M.2
      have hN : (N : Matrix (Fin k) (Fin k) ℝ)ᵀ = N := N.2
      rw [← hM, ← hN, transpose_apply, transpose_apply]
      exact h1
  · intro f
    refine ⟨⟨Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else
      f ⟨(j, i), (lt_of_not_ge h).le⟩, ?_⟩, ?_⟩
    · ext i j
      simp only [transpose_apply, of_apply]
      rcases lt_trichotomy i j with hij | rfl | hij
      · simp [not_le.2 hij, hij.le]
      · rfl
      · simp [not_le.2 hij, hij.le]
    · funext p
      change (if h : p.1.1 ≤ p.1.2 then f ⟨(p.1.1, p.1.2), h⟩ else _) = f p
      rw [dite_eq_left_of_eq_true (eq_true p.2)]

/-- **The distinct entries of `Var(u)`** (AKMM, p. 223 and footnote 4): the symmetric `n × n`
matrices form a space of dimension `n(n+1)/2` (here `2·dim = n(n+1)`). -/
theorem sv_finrank_symm (k : ℕ) : 2 * Module.finrank ℝ (sv_symm k) = k * (k + 1) := by
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ (sv_upperMap_bijective k)),
    Module.finrank_fintype_fun_eq_card, sv_card_upper]

/-- **The restriction count** (AKMM, p. 223, footnote 4): `B₀` has `n²` unknowns, `Var(u)`
supplies `n(n+1)/2` equations, so `n² − n(n+1)/2 = n(n−1)/2` restrictions are needed: one for
`n = 2`. -/
theorem sv_restriction_count (k : ℕ) :
    Module.finrank ℝ (Matrix (Fin k) (Fin k) ℝ) = k ^ 2 ∧
      2 * (k ^ 2 - Module.finrank ℝ (sv_symm k)) = k * (k - 1) ∧
      2 ^ 2 - Module.finrank ℝ (sv_symm 2) = 1 := by
  have h := sv_finrank_symm k
  have h2 := sv_finrank_symm 2
  refine ⟨by simp [Module.finrank_matrix, sq], ?_, by norm_num at h2 ⊢; omega⟩
  have hle : Module.finrank ℝ (sv_symm k) ≤ k ^ 2 := by nlinarith
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]
    zify [hle] at h ⊢
    linarith

/-- **The normalisation `Var(εₜ) = I`** (AKMM, p. 222): "it is without loss of generality to
assume that the covariance matrix of `εₜ` is the identity as we can rescale the `B_j`'s". If the
structural shocks are uncorrelated with variances `dᵢ > 0`, then with `S = diag(1/√dᵢ)` the
rescaled shocks `Sε` have `Var(Sε) = I`, and `B₀y = Σⱼ Bⱼxⱼ + ε` iff
`(SB₀)y = Σⱼ (SBⱼ)xⱼ + Sε`. -/
theorem sv_normalisation {ε : Ω → n → ℝ} (hε : kf_L2 μ ε) {d : n → ℝ} (hd : ∀ i, 0 < d i)
    (hD : var_mom μ ε ε = diagonal d) {J : Type*} [Fintype J] (B0 : Matrix n n ℝ)
    (B : J → Matrix n n ℝ) (y e : n → ℝ) (x : J → n → ℝ) :
    var_mom μ (kf_app (diagonal fun i => 1 / Real.sqrt (d i)) ε)
        (kf_app (diagonal fun i => 1 / Real.sqrt (d i)) ε) = 1 ∧
      (B0 *ᵥ y = ∑ j, B j *ᵥ x j + e ↔
        ((diagonal fun i => 1 / Real.sqrt (d i)) * B0) *ᵥ y =
          ∑ j, ((diagonal fun i => 1 / Real.sqrt (d i)) * B j) *ᵥ x j +
            (diagonal fun i => 1 / Real.sqrt (d i)) *ᵥ e) := by
  set S : Matrix n n ℝ := diagonal fun i => 1 / Real.sqrt (d i) with hS
  have hSinv : IsUnit S.det := by
    rw [hS, det_diagonal]
    exact (Finset.prod_pos fun i _ => by
      have := Real.sqrt_pos.2 (hd i); positivity).ne'.isUnit
  refine ⟨?_, ?_⟩
  · rw [kf_mom_app_left hε (kf_L2_app hε _), kf_mom_app_right hε hε, hD, hS,
      diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    have h1 := Real.sqrt_pos.2 (hd i)
    have h2 := Real.mul_self_sqrt (hd i).le
    field_simp
    linarith
  · constructor
    · intro h
      rw [← mulVec_mulVec, h, mulVec_add, mulVec_sum]
      simp only [mulVec_mulVec]
    · intro h
      have hinj : Function.Injective (S *ᵥ ·) := Matrix.mulVec_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det S).2 hSinv)
      apply hinj
      simp only
      rw [mulVec_mulVec, h, mulVec_add, mulVec_sum]
      simp only [mulVec_mulVec]

end AKMM.QuantitativeMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive (Cholesky) identification

AKMM, §8.4, the box "Recursive identification", p. 224, the system (8.8)–(8.9), and the
normalisation of footnote 6, p. 227.

* **The Cholesky decomposition**: a positive definite `Σ` is `LL'` for a lower-triangular `L` with
  positive diagonal (`ch_exists`, from Mathlib's LDL decomposition), and that `L` is unique
  (`ch_unique`; not in Mathlib).
* **Recursive identification**: if the impact matrix `B₀⁻¹` is lower triangular with positive
  diagonal and `Var(εₜ) = I`, then the Cholesky factor of `Var(uₜ)` is `B₀⁻¹`
  (`ch_recursive_identification`).
* The book's statement omits the sign normalisation: without "positive diagonal" the
  triangular factor is determined only up to the signs of its columns
  (`ch_sign_counterexample`).
* (8.8)–(8.9) ordered as `(ĝ, ŷ)`: the impact matrix `[[σ_g, 0], [χσ_g, σ_A]]` is lower
  triangular, so `χ = L₂₁/L₁₁` for the Cholesky factor `L` of `Var(ĝ, ŷ)` (`ch_fiscal_example`).
* Footnote 6's weights: for `Σ = LL'` with `L` lower triangular, `Σ_{i1}/Σ₁₁ = L_{i1}/L₁₁`
  (`ch_first_column`).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Matrix Miao.PartialInformation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

variable {n : Type*} [Fintype n] [LinearOrder n]

omit [Fintype n] in
/-- A lower-triangular matrix: `L i j = 0` for `i < j`. -/
theorem ch_lower_apply {L : Matrix n n ℝ} (hL : L.IsLowerTriangular) {i j : n} (h : i < j) :
    L i j = 0 :=
  hL (by simpa using h)

/-- The diagonal of a product of lower-triangular matrices. -/
theorem ch_lower_mul_diag {L M : Matrix n n ℝ} (hL : L.IsLowerTriangular)
    (hM : M.IsLowerTriangular) (i : n) : (L * M) i i = L i i * M i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [ch_lower_apply hM h, mul_zero]
    · rw [ch_lower_apply hL h, zero_mul]
  · simp

/-- **Uniqueness of the Cholesky factor**: two lower-triangular matrices with positive diagonal
and `L₁L₁' = L₂L₂'` are equal. -/
theorem ch_unique {L1 L2 : Matrix n n ℝ} (h1 : L1.IsLowerTriangular) (h2 : L2.IsLowerTriangular)
    (hp1 : ∀ i, 0 < L1 i i) (hp2 : ∀ i, 0 < L2 i i) (h : L1 * L1ᵀ = L2 * L2ᵀ) : L1 = L2 := by
  have hdet : IsUnit L2.det := by
    rw [det_of_isLowerTriangular L2 h2]
    exact (Finset.prod_pos fun i _ => hp2 i).ne'.isUnit
  have : Invertible L2 := invertibleOfIsUnitDet L2 hdet
  have hinv : L2⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular h2
  set Q := L2⁻¹ * L1 with hQ
  have hQl : Q.IsLowerTriangular := hinv.mul h1
  have hL1 : L1 = L2 * Q := by rw [hQ, ← Matrix.mul_assoc, mul_nonsing_inv L2 hdet, one_mul]
  have hQQ : Q * Qᵀ = 1 := by
    rw [hQ, transpose_mul]
    calc L2⁻¹ * L1 * (L1ᵀ * L2⁻¹ᵀ) = L2⁻¹ * (L1 * L1ᵀ) * L2⁻¹ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (L2⁻¹ * L2) * (L2⁻¹ * L2)ᵀ := by
          rw [h, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul L2 hdet, transpose_one, Matrix.one_mul]
  have hQinv : Q⁻¹ = Qᵀ := inv_eq_right_inv hQQ
  have hQdet : IsUnit Q.det := isUnit_det_of_right_inverse hQQ
  have : Invertible Q := invertibleOfIsUnitDet Q hQdet
  have hQtl : Qᵀ.IsLowerTriangular := by
    rw [← hQinv]; exact blockTriangular_inv_of_blockTriangular hQl
  -- `Q` is diagonal
  have hoff : ∀ i j, i ≠ j → Q i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact ch_lower_apply hQl h
    · have := ch_lower_apply hQtl h
      rwa [transpose_apply] at this
  -- its diagonal entries are positive
  have hpos : ∀ i, 0 < Q i i := by
    intro i
    have := ch_lower_mul_diag h2 hQl i
    rw [← hL1] at this
    have h1i := hp1 i
    rw [this] at h1i
    exact pos_of_mul_pos_right h1i (hp2 i).le
  -- and square to one
  have hone : ∀ i, Q i i = 1 := by
    intro i
    have := congrFun (congrFun hQQ i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by
      rw [transpose_apply, hoff i k (Ne.symm hk), zero_mul]) (by simp)] at this
    rw [transpose_apply, one_apply_eq] at this
    nlinarith [hpos i]
  have hQ1 : Q = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [hone, one_apply_eq]
    · rw [hoff i j hij, one_apply_ne hij]
  rw [hL1, hQ1, Matrix.mul_one]

/-- **The Cholesky decomposition**: a positive definite real matrix is `LL'` for a
lower-triangular `L` with positive diagonal. -/
theorem ch_exists [WellFoundedLT n] [LocallyFiniteOrderBot n] {S : Matrix n n ℝ}
    (hS : S.PosDef) : ∃ L : Matrix n n ℝ, L.IsLowerTriangular ∧ (∀ i, 0 < L i i) ∧
      L * Lᵀ = S := by
  set d := LDL.diagEntries hS with hd
  have hD : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    have hU : IsUnit (LDL.lowerInv hS) := isUnit_of_invertible _
    rw [← star_eq_conjTranspose]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hU).2 hS
  have hdpos : ∀ i, 0 < d i := by
    intro i
    have := hD.diag_pos (i := i)
    simpa [LDL.diag, hd] using this
  set L0 := LDL.lower hS * diagonal (fun i => Real.sqrt (d i)) with hL0
  have hL0l : L0.IsLowerTriangular := (LDL.isLowerTriangular_lower hS).mul
    (blockTriangular_diagonal _)
  have hL0S : L0 * L0ᵀ = S := by
    have hsq : diagonal (fun i => Real.sqrt (d i)) * (diagonal fun i => Real.sqrt (d i))ᵀ =
        LDL.diag hS := by
      rw [diagonal_transpose, diagonal_mul_diagonal, LDL.diag]
      congr 1
      funext i
      rw [← hd, Real.mul_self_sqrt (hdpos i).le]
    have hLDL := LDL.lower_conj_diag hS
    rw [conjTranspose_eq_transpose_of_trivial] at hLDL
    rw [hL0, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), hsq,
      ← Matrix.mul_assoc, hLDL]
  -- the diagonal of `L0` is nonzero
  have hne : ∀ i, L0 i i ≠ 0 := by
    have hdet : S.det ≠ 0 := (hS.det_pos).ne'
    rw [← hL0S, det_mul, det_transpose, det_of_isLowerTriangular L0 hL0l] at hdet
    intro i hi
    apply hdet
    have h0 : ∏ j, L0 j j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [h0, zero_mul]
  set sg : n → ℝ := fun i => if 0 < L0 i i then 1 else -1 with hsg
  have hsg2 : ∀ i, sg i * sg i = 1 := by intro i; simp only [hsg]; split_ifs <;> norm_num
  refine ⟨L0 * diagonal sg, hL0l.mul (blockTriangular_diagonal _), fun i => ?_, ?_⟩
  · rw [mul_diagonal]
    simp only [hsg]
    split_ifs with h
    · linarith
    · have := lt_of_le_of_ne (not_lt.1 h) (hne i); linarith
  · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal sg), diagonal_transpose,
      diagonal_mul_diagonal]
    have : (diagonal fun i => sg i * sg i) = (1 : Matrix n n ℝ) := by
      rw [show (fun i => sg i * sg i) = fun _ => (1 : ℝ) from funext hsg2]; rfl
    rw [this, Matrix.one_mul, hL0S]

/-- **Recursive identification** (AKMM, p. 224): if the variables are ordered so that the
impact matrix `B₀⁻¹` is lower triangular with positive diagonal, and `Var(εₜ) = I`, then every
lower-triangular `L` with positive diagonal and `LL' = Var(uₜ)` (the Cholesky factor) is
`B₀⁻¹`. -/
theorem ch_recursive_identification {ε : Ω → n → ℝ} (hε : kf_L2 μ ε) (hI : var_mom μ ε ε = 1)
    {B0 L : Matrix n n ℝ} (hB : B0⁻¹.IsLowerTriangular) (hBp : ∀ i, 0 < B0⁻¹ i i)
    (hL : L.IsLowerTriangular) (hLp : ∀ i, 0 < L i i)
    (hLS : L * Lᵀ = var_mom μ (kf_app B0⁻¹ ε) (kf_app B0⁻¹ ε)) : L = B0⁻¹ := by
  rw [sv_var_u hε hI] at hLS
  exact ch_unique hL hB hLp hBp hLS

/-- **The sign normalisation is needed** (AKMM, p. 224): "a Cholesky decomposition of
`Var(uₜ)` gives `B₀⁻¹`" needs the diagonal of `B₀⁻¹` to be positive. Flipping the sign of a
column of a lower-triangular `L` gives another lower-triangular factor of the same `LL'`, and a
different one when that diagonal entry is nonzero. -/
theorem ch_sign_counterexample {L : Matrix n n ℝ} (hL : L.IsLowerTriangular)
    (k : n) (hk : L k k ≠ 0) :
    let L' := L * diagonal (fun i => if i = k then -1 else 1)
    L'.IsLowerTriangular ∧ L' * L'ᵀ = L * Lᵀ ∧ L' ≠ L := by
  intro L'
  refine ⟨hL.mul (blockTriangular_diagonal _), ?_, fun h => hk ?_⟩
  · simp only [L']
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_transpose,
      diagonal_mul_diagonal]
    have : (diagonal fun i => (if i = k then (-1 : ℝ) else 1) * if i = k then -1 else 1) =
        (1 : Matrix n n ℝ) := by
      rw [show (fun i => (if i = k then (-1 : ℝ) else 1) * if i = k then -1 else 1) =
        fun _ => (1 : ℝ) from funext fun i => by split_ifs <;> norm_num]
      rfl
    rw [this, Matrix.one_mul]
  · have := congrFun (congrFun h k) k
    simp only [L', mul_diagonal, ↓reduceIte] at this
    linarith

/-- **Footnote 6's weights** (AKMM, p. 227): if `Σ = LL'` with `L` lower triangular and `1` the
first variable (the least index), then `Σ_{i1} = L_{i1}L₁₁` and `Σ₁₁ = L₁₁²`, so
`Σ_{i1}/Σ₁₁ = L_{i1}/L₁₁`: the first column of `L` normalised to have first element `1`. -/
theorem ch_first_column {L S : Matrix n n ℝ} (hL : L.IsLowerTriangular) (hS : S = L * Lᵀ)
    (i1 : n) (hmin : ∀ j, i1 ≤ j) (i : n) :
    S i i1 = L i i1 * L i1 i1 ∧ S i1 i1 = L i1 i1 ^ 2 ∧ S i i1 / S i1 i1 = L i i1 / L i1 i1 := by
  have hcol : ∀ i, S i i1 = L i i1 * L i1 i1 := by
    intro i
    rw [hS, Matrix.mul_apply, Finset.sum_eq_single i1]
    · rfl
    · intro k _ hk
      rw [transpose_apply, ch_lower_apply hL (lt_of_le_of_ne (hmin k) (Ne.symm hk)), mul_zero]
    · simp
  refine ⟨hcol i, by rw [hcol i1, sq], ?_⟩
  rw [hcol i, hcol i1]
  rcases eq_or_ne (L i1 i1) 0 with h | h
  · simp [h]
  · field_simp

/-- **The fiscal example** (AKMM, (8.8)–(8.9), p. 224): ordering the variables as `(ĝ, ŷ)` and
normalising the shocks to unit variance, `ĝ = σ_g ε₁` and `ŷ = χσ_g ε₁ + σ_A ε₂`; the impact
matrix `[[σ_g, 0], [χσ_g, σ_A]]` is lower triangular with positive diagonal, so it is the
Cholesky factor of `Var(ĝ, ŷ)`, and `χ = L₂₁/L₁₁`. -/
theorem ch_fiscal_example {ε : Ω → Fin 2 → ℝ} (hε : kf_L2 μ ε) (hI : var_mom μ ε ε = 1)
    {χ σg σA : ℝ} (hg : 0 < σg) (hA : 0 < σA) {L : Matrix (Fin 2) (Fin 2) ℝ}
    (hL : L.IsLowerTriangular) (hLp : ∀ i, 0 < L i i)
    (hLS : L * Lᵀ = var_mom μ (kf_app !![σg, 0; χ * σg, σA] ε)
      (kf_app !![σg, 0; χ * σg, σA] ε)) :
    L = !![σg, 0; χ * σg, σA] ∧ χ = L 1 0 / L 0 0 := by
  have hb : (!![σg, 0; χ * σg, σA] : Matrix (Fin 2) (Fin 2) ℝ).IsLowerTriangular := by
    intro i j hij
    rw [OrderDual.toDual_lt_toDual] at hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hbp : ∀ i, 0 < (!![σg, 0; χ * σg, σA] : Matrix (Fin 2) (Fin 2) ℝ) i i := by
    intro i; fin_cases i <;> simp [hg, hA]
  have hV : var_mom μ (kf_app !![σg, 0; χ * σg, σA] ε) (kf_app !![σg, 0; χ * σg, σA] ε) =
      !![σg, 0; χ * σg, σA] * (!![σg, 0; χ * σg, σA])ᵀ := by
    rw [kf_mom_app_left hε (kf_L2_app hε _), kf_mom_app_right hε hε, hI, Matrix.one_mul]
  rw [hV] at hLS
  have hLeq := ch_unique hL hb hLp hbp hLS
  refine ⟨hLeq, ?_⟩
  rw [hLeq]
  simp [hg.ne']

end AKMM.QuantitativeMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# VARs and local projections

AKMM, the box "Defining the fiscal multiplier in a dynamic economy", p. 220; the box "From
natural experiments to impulse response functions: local projection", p. 221; §8.5,
pp. 225–227, with footnote 6.

* **Dynamic multipliers** (box, p. 220): the peak and cumulative multipliers; when the output
  response is proportional to the spending response, `y_h = mG_h` with `m ≥ 0`, both equal `m`
  (`vl_peak_multiplier_prop`, `vl_cum_multiplier_prop`).
* **VAR impulse responses** (p. 226): for `yₜ = A₁yₜ₋₁ + uₜ`, a shock `v` to `uₜ` moves
  `y_{t+h}` by `A₁ʰv`, the identity on impact (`vl_var1_irf`, from Miao's
  `var_impulse_response`); the companion form of a VAR(J) (`vl_companion`, `vl_companion_rec`,
  the book's `J = 2` display `vl_companion_two`) and its impulse responses as the upper-left
  block of `𝒜ʰ` (`vl_companion_irf`).
* **Population estimands** (p. 226). The outcome `Y = y_{t+h}` and the regressor `yₜ` are
  written `Y = Θuₜ + Ψv + Mw`, `yₜ = uₜ + Nw`, with `w` the lags, `v` the later innovations,
  `uₜ ⟂ w`, `v ⟂ w`, `v ⟂ uₜ`, `Σ = E[uₜuₜ']`. The book's "least squares equates with a
  conditional expectation" for Gaussian data is taken in its linear-projection form.
  * The local projection on `y_{1,t}` (controlling for `w`) has coefficients
    `β_i = (ΘΣ)_{i1}/Σ₁₁`, and they exist (`vl_lp_estimand`, `vl_lp_exists`).
  * The VAR projection on `yₜ` has coefficient matrix `Γ` with `ΓΣ = ΘΣ`, so `Γ = Θ` for
    invertible `Σ` (`vl_var_estimand`, `vl_var_exists`); the two differ when the innovations are
    correlated (`vl_lp_differs`).
  * **Plagborg-Møller–Wolf** (footnote 6): `β_i = Σⱼ Γ_{ij}(L_{j1}/L₁₁)` with `L` the Cholesky
    factor of `Σ` (`fn_6`).
  * **The LP box** (p. 221): if `y_{1,t} = zₜ` is uncorrelated with the other innovations, the
    local projection is the impulse response, `β_i = Θ_{i1}` (`vl_lp_exogenous`).
  * For a VAR(1), `Θ = A₁ʰ` and `M = A₁ʰ⁺¹`, so the VAR estimand is `A₁ʰ` and the LP estimand
    is `A₁ʰΣe₁/Σ₁₁` (`vl_var1_estimands`).

Departure: the expectations of p. 226 are Gaussian conditional expectations; here they are the
population linear projections, which coincide with them for Gaussian data (not formalised).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Matrix Miao.PartialInformation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Dynamic multipliers -/

/-- AKMM, p. 220 (Mountford–Uhlig): the cumulative multiplier over horizons `0, …, H`,
`Σ_h y_h / Σ_h G_h`. -/
noncomputable def vl_cumMult (y G : ℕ → ℝ) (H : ℕ) : ℝ :=
  (∑ h ∈ Finset.range (H + 1), y h) / ∑ h ∈ Finset.range (H + 1), G h

/-- AKMM, p. 220 (Blanchard–Perotti): the peak multiplier over horizons `0, …, H`,
`max_h y_h / max_h G_h`. -/
noncomputable def vl_peakMult (y G : ℕ → ℝ) (H : ℕ) : ℝ :=
  (Finset.range (H + 1)).sup' Finset.nonempty_range_add_one y /
    (Finset.range (H + 1)).sup' Finset.nonempty_range_add_one G

/-- AKMM, p. 220: if `y_h = mG_h` and `Σ G_h ≠ 0`, the cumulative multiplier is `m`. -/
theorem vl_cum_multiplier_prop {y G : ℕ → ℝ} {m : ℝ} (H : ℕ) (hy : ∀ h, y h = m * G h)
    (hG : ∑ h ∈ Finset.range (H + 1), G h ≠ 0) : vl_cumMult y G H = m := by
  unfold vl_cumMult
  simp only [hy, ← Finset.mul_sum]
  field_simp

/-- AKMM, p. 220: if `y_h = mG_h` with `m ≥ 0` and the peak spending response is nonzero, the
peak multiplier is `m`. -/
theorem vl_peak_multiplier_prop {y G : ℕ → ℝ} {m : ℝ} (H : ℕ) (hy : ∀ h, y h = m * G h)
    (hm : 0 ≤ m) (hG : (Finset.range (H + 1)).sup' Finset.nonempty_range_add_one G ≠ 0) :
    vl_peakMult y G H = m := by
  unfold vl_peakMult
  have hne : (Finset.range (H + 1)).Nonempty := Finset.nonempty_range_add_one
  obtain ⟨h1, hh1, e1⟩ := Finset.exists_mem_eq_sup' hne G
  obtain ⟨h2, hh2, e2⟩ := Finset.exists_mem_eq_sup' hne y
  have hle1 : G h2 ≤ G h1 := e1 ▸ Finset.le_sup' G hh2
  have hle2 : y h1 ≤ y h2 := e2 ▸ Finset.le_sup' y hh1
  rw [e1] at hG ⊢
  rw [e2]
  have : y h2 = m * G h1 := le_antisymm (by rw [hy]; exact mul_le_mul_of_nonneg_left hle1 hm)
    (by rw [← hy]; exact hle2)
  rw [this]
  field_simp

/-! ### VAR impulse responses and the companion form -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The VAR(1) impulse response** (AKMM, p. 226): for `yₜ₊₁ = A₁yₜ + uₜ₊₁`, if `u'` differs
from `u` only by `v` at date `s + 1` (and `y'₀ = y₀`), then `y'_{s+1+h} − y_{s+1+h} = A₁ʰv`; at
`h = 0` this is `v` itself: the reduced-form shock moves a single variable on impact. -/
theorem vl_var1_irf {A : Matrix n n ℝ} {y y' u u' : ℕ → n → ℝ}
    (hrec : ∀ t, y (t + 1) = A *ᵥ y t + u (t + 1))
    (hrec' : ∀ t, y' (t + 1) = A *ᵥ y' t + u' (t + 1)) (h0 : y' 0 = y 0) (s : ℕ) (v : n → ℝ)
    (hu : ∀ t, u' t = if t = s + 1 then u t + v else u t) :
    (∀ h, y' (s + 1 + h) - y (s + 1 + h) = (A ^ h) *ᵥ v) ∧ y' (s + 1) - y (s + 1) = v := by
  have h1 : ∀ t, y (t + 1) = A *ᵥ y t + (1 : Matrix n n ℝ) *ᵥ u (t + 1) := by
    intro t; rw [one_mulVec]; exact hrec t
  have h2 : ∀ t, y' (t + 1) = A *ᵥ y' t + (1 : Matrix n n ℝ) *ᵥ u' (t + 1) := by
    intro t; rw [one_mulVec]; exact hrec' t
  have := (Miao.RationalExpectations.var_impulse_response h1 h2 h0 s v hu).2
  have hh : ∀ h, y' (s + 1 + h) - y (s + 1 + h) = (A ^ h) *ᵥ v := by
    intro h; rw [this h, Matrix.mul_one]
  refine ⟨hh, ?_⟩
  simpa using hh 0

/-- AKMM, p. 226: the companion matrix of a VAR with `m + 1` lags, on the stacked state
`(yₜ, yₜ₋₁, …, yₜ₋ₘ)` indexed by `Fin (m+1) × n`: the first block row is `(A₁, …, A_{m+1})`,
below it identity blocks shift the lags. -/
def vl_companion {m : ℕ} (A : Fin (m + 1) → Matrix n n ℝ) :
    Matrix (Fin (m + 1) × n) (Fin (m + 1) × n) ℝ :=
  Matrix.of fun p q => if p.1 = 0 then A q.1 p.2 q.2 else
    if (q.1 : ℕ) + 1 = p.1 ∧ p.2 = q.2 then 1 else 0

/-- The stacked state `(y_{t+m}, …, y_t)`: block `r` is `y_{t+m−r}`. -/
def vl_stack {m : ℕ} (y : ℕ → n → ℝ) (t : ℕ) : Fin (m + 1) × n → ℝ :=
  fun p => y (t + m - p.1) p.2

/-- The loading of the innovation on the first block. -/
def vl_load (m : ℕ) : Matrix (Fin (m + 1) × n) n ℝ :=
  Matrix.of fun p k => if p.1 = 0 ∧ p.2 = k then 1 else 0

/-- **The companion form** (AKMM, p. 226): if
`y_{t+m+1} = Σ_{c ≤ m} A_{c+1}y_{t+m−c} + u_{t+m+1}` for all `t`, the stacked state is a
first-order system `xₜ₊₁ = 𝒜xₜ + (u_{t+m+1}, 0, …, 0)`. -/
theorem vl_companion_rec {m : ℕ} {A : Fin (m + 1) → Matrix n n ℝ} {y u : ℕ → n → ℝ}
    (hrec : ∀ t, y (t + m + 1) = ∑ c : Fin (m + 1), A c *ᵥ y (t + m - c) + u (t + m + 1))
    (t : ℕ) :
    vl_stack (m := m) y (t + 1) = vl_companion A *ᵥ vl_stack y t + vl_load m *ᵥ u (t + m + 1) := by
  funext p
  obtain ⟨r, i⟩ := p
  simp only [vl_stack, vl_companion, vl_load, mulVec, dotProduct, of_apply, Pi.add_apply,
    Fintype.sum_prod_type]
  by_cases hr : r = 0
  · subst hr
    simp only [↓reduceIte, true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, Fin.val_zero, Nat.sub_zero]
    rw [show t + 1 + m = t + m + 1 by ring, hrec t]
    simp only [Pi.add_apply, Finset.sum_apply, mulVec, dotProduct]
  · simp only [hr, ↓reduceIte, false_and, zero_mul, Finset.sum_const_zero, add_zero]
    obtain ⟨r', hr'⟩ : ∃ r' : Fin (m + 1), (r' : ℕ) + 1 = r := by
      refine ⟨⟨(r : ℕ) - 1, by omega⟩, ?_⟩
      have : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
      simp only; omega
    rw [Finset.sum_eq_single r']
    · simp only [hr', true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      congr 1
      omega
    · intro c _ hc
      refine Finset.sum_eq_zero fun k _ => ?_
      have : ¬ ((c : ℕ) + 1 = r) := fun h => hc (Fin.ext (by omega))
      simp [this]
    · simp

omit [Fintype n] in
/-- **The `J = 2` companion matrix** (AKMM, p. 226): `𝒜 = [[A₁, A₂], [I, 0]]`, entrywise. -/
theorem vl_companion_two (A : Fin 2 → Matrix n n ℝ) (i k : n) :
    vl_companion A (0, i) (0, k) = A 0 i k ∧ vl_companion A (0, i) (1, k) = A 1 i k ∧
      vl_companion A (1, i) (0, k) = (1 : Matrix n n ℝ) i k ∧
      vl_companion A (1, i) (1, k) = 0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [vl_companion, one_apply]
  · simp [vl_companion]

/-- **Impulse responses of a VAR(J)** (AKMM, p. 226): if two solutions of the VAR with `m + 1`
lags have the same initial values `y₀, …, y_m` and their innovations differ only by `v` at date
`s + m + 1`, then `y'_{s+m+1+h} − y_{s+m+1+h} = Σ_k (𝒜ʰ)_{(0,i),(0,k)}v_k`: the IRFs are the
upper-left `n × n` block of `𝒜ʰ`, which is the identity at `h = 0`. -/
theorem vl_companion_irf {m : ℕ} {A : Fin (m + 1) → Matrix n n ℝ} {y y' u u' : ℕ → n → ℝ}
    (hrec : ∀ t, y (t + m + 1) = ∑ c : Fin (m + 1), A c *ᵥ y (t + m - c) + u (t + m + 1))
    (hrec' : ∀ t, y' (t + m + 1) = ∑ c : Fin (m + 1), A c *ᵥ y' (t + m - c) + u' (t + m + 1))
    (h0 : ∀ r ≤ m, y' r = y r) (s : ℕ) (v : n → ℝ)
    (hu : ∀ t, u' t = if t = s + m + 1 then u t + v else u t) (h : ℕ) (i : n) :
    y' (s + m + 1 + h) i - y (s + m + 1 + h) i =
      ∑ k, (vl_companion A ^ h) (0, i) (0, k) * v k := by
  have e1 : ∀ t, vl_stack (m := m) y (t + 1) =
      vl_companion A *ᵥ vl_stack y t + vl_load m *ᵥ (fun t => u (t + m)) (t + 1) := by
    intro t; beta_reduce; rw [vl_companion_rec hrec t, show t + 1 + m = t + m + 1 by ring]
  have e2 : ∀ t, vl_stack (m := m) y' (t + 1) =
      vl_companion A *ᵥ vl_stack y' t + vl_load m *ᵥ (fun t => u' (t + m)) (t + 1) := by
    intro t; beta_reduce; rw [vl_companion_rec hrec' t, show t + 1 + m = t + m + 1 by ring]
  have hst0 : vl_stack (m := m) y' 0 = vl_stack y 0 := by
    funext p; simp only [vl_stack]; exact congrFun (h0 _ (by omega)) _
  have hshock : ∀ t, (fun t => u' (t + m)) t =
      if t = s + 1 then (fun t => u (t + m)) t + v else (fun t => u (t + m)) t := by
    intro t
    simp only
    rw [hu]
    by_cases ht : t = s + 1
    · subst ht; simp [show s + 1 + m = s + m + 1 by ring]
    · have : t + m ≠ s + m + 1 := by omega
      simp [ht, this]
  have := (Miao.RationalExpectations.var_impulse_response e1 e2 hst0 s v hshock).2 h
  have hc := congrFun this (0, i)
  simp only [vl_stack, Pi.sub_apply, Fin.val_zero, Nat.sub_zero] at hc
  rw [show s + 1 + h + m = s + m + 1 + h by ring] at hc
  rw [hc, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single (0, k)]
  · simp [vl_load]
  · intro q _ hq
    have : ¬ (q.1 = 0 ∧ q.2 = k) := fun hh => hq (Prod.ext hh.1 hh.2)
    simp [vl_load, this]
  · simp

/-! ### Population estimands of local projections and VARs -/

/-- The coefficient matrix that puts `β` on the regressor `y_{1,t}` (column `i₁`) and zero on
the others. -/
def vl_col (β : n → ℝ) (i1 : n) : Matrix n n ℝ := Matrix.of fun i k => if k = i1 then β i else 0

variable {J K : Type*} [Fintype J] [Fintype K]

omit [DecidableEq n] in
/-- The second moments of a projection residual `e = Y − Byₜ − aw`, with
`Y = Θuₜ + Ψv + Mw` and `yₜ = uₜ + Nw`: `E[euₜ'] = ΘΣ − BΣ`, `E[ew'] = (M − BN − a)E[ww']` and
`E[eyₜ'] = E[euₜ'] + E[ew']N'`. -/
theorem vl_mom_resid {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M : Matrix n J ℝ)
    (N : Matrix n J ℝ) (B : Matrix n n ℝ) (a : Matrix n J ℝ) :
    var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
        kf_app a w) u = Θ * var_mom μ u u - B * var_mom μ u u ∧
      var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
        kf_app a w) w = (M - B * N - a) * var_mom μ w w ∧
      var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
        kf_app a w) (u + kf_app N w) =
        var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
          kf_app a w) u +
        var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
          kf_app a w) w * Nᵀ := by
  have hwu : var_mom μ w u = 0 := by rw [kf_mom_transpose, huw, transpose_zero]
  have hyt : kf_L2 μ (u + kf_app N w) := kf_L2_add hu (kf_L2_app hw N)
  have hY : kf_L2 μ (kf_app Θ u + kf_app Ψ v + kf_app M w) :=
    kf_L2_add (kf_L2_add (kf_L2_app hu Θ) (kf_L2_app hv Ψ)) (kf_L2_app hw M)
  have hBy : kf_L2 μ (kf_app B (u + kf_app N w)) := kf_L2_app hyt B
  have he1 : kf_L2 μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w)) :=
    kf_L2_sub hY hBy
  have hmomu : ∀ {z : Ω → n → ℝ}, kf_L2 μ z →
      var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
        kf_app a w) z = Θ * var_mom μ u z + Ψ * var_mom μ v z + M * var_mom μ w z -
          B * (var_mom μ u z + N * var_mom μ w z) - a * var_mom μ w z := by
    intro z hz
    rw [kf_mom_sub_left he1 (kf_L2_app hw a) hz, kf_mom_sub_left hY hBy hz,
      kf_mom_add_left (kf_L2_add (kf_L2_app hu Θ) (kf_L2_app hv Ψ)) (kf_L2_app hw M) hz,
      kf_mom_add_left (kf_L2_app hu Θ) (kf_L2_app hv Ψ) hz, kf_mom_app_left hu hz,
      kf_mom_app_left hv hz, kf_mom_app_left hw hz, kf_mom_app_left hyt hz,
      kf_mom_add_left hu (kf_L2_app hw N) hz, kf_mom_app_left hw hz, kf_mom_app_left hw hz]
  have hmomw : ∀ {z : Ω → J → ℝ}, kf_L2 μ z →
      var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app B (u + kf_app N w) -
        kf_app a w) z = Θ * var_mom μ u z + Ψ * var_mom μ v z + M * var_mom μ w z -
          B * (var_mom μ u z + N * var_mom μ w z) - a * var_mom μ w z := by
    intro z hz
    rw [kf_mom_sub_left he1 (kf_L2_app hw a) hz, kf_mom_sub_left hY hBy hz,
      kf_mom_add_left (kf_L2_add (kf_L2_app hu Θ) (kf_L2_app hv Ψ)) (kf_L2_app hw M) hz,
      kf_mom_add_left (kf_L2_app hu Θ) (kf_L2_app hv Ψ) hz, kf_mom_app_left hu hz,
      kf_mom_app_left hv hz, kf_mom_app_left hw hz, kf_mom_app_left hyt hz,
      kf_mom_add_left hu (kf_L2_app hw N) hz, kf_mom_app_left hw hz, kf_mom_app_left hw hz]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmomu hu, hvu, hwu]; simp
  · rw [hmomw hw, huw, hvw]; simp only [Matrix.mul_zero, zero_add, add_zero]
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc]
  · rw [kf_mom_add_right hu (kf_L2_app hw N) (kf_L2_sub he1 (kf_L2_app hw a)),
      kf_mom_app_right hw (kf_L2_sub he1 (kf_L2_app hw a))]

/-- **The local-projection estimand** (AKMM, p. 226): if `β, a` are population least-squares
coefficients of the regression of `Y = y_{t+h}` on `y_{1,t}` and the lags `w` (the residual is
orthogonal to `y_{1,t}` and to `w`) and `Σ₁₁ ≠ 0`, then `β_i = (ΘΣ)_{i1}/Σ₁₁`. -/
theorem vl_lp_estimand {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ)
    (i1 : n) (h11 : var_mom μ u u i1 i1 ≠ 0) (β : n → ℝ) (a : Matrix n J ℝ)
    (horth1 : ∀ i, var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) (u + kf_app N w) i i1 = 0)
    (horthw : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) w = 0) (i : n) :
    β i = (Θ * var_mom μ u u) i i1 / var_mom μ u u i1 i1 := by
  obtain ⟨h1, -, h3⟩ := vl_mom_resid hu hv hw huw hvw hvu Θ Ψ M N (vl_col β i1) a
  rw [h3, horthw, Matrix.zero_mul, add_zero, h1] at horth1
  have := horth1 i
  rw [Matrix.sub_apply, Matrix.mul_apply (M := vl_col β i1)] at this
  simp only [vl_col, of_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at this
  field_simp
  linarith

/-- The local projection exists (AKMM, p. 226): `β_i = (ΘΣ)_{i1}/Σ₁₁`, `a = M − (βe₁')N` give a
residual orthogonal to `y_{1,t}` and to `w`. -/
theorem vl_lp_exists {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ)
    (i1 : n) (h11 : var_mom μ u u i1 i1 ≠ 0) :
    let β : n → ℝ := fun i => (Θ * var_mom μ u u) i i1 / var_mom μ u u i1 i1
    let a := M - vl_col β i1 * N
    (∀ i, var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) (u + kf_app N w) i i1 = 0) ∧
    var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) w = 0 := by
  intro β a
  obtain ⟨h1, h2, h3⟩ := vl_mom_resid hu hv hw huw hvw hvu Θ Ψ M N (vl_col β i1) a
  have hw0 : (M - vl_col β i1 * N - a) = 0 := by simp only [a]; abel
  rw [hw0, Matrix.zero_mul] at h2
  refine ⟨fun i => ?_, h2⟩
  rw [h3, h2, Matrix.zero_mul, add_zero, h1, Matrix.sub_apply, Matrix.mul_apply (M := vl_col β i1)]
  simp only [vl_col, of_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, β]
  field_simp
  ring

/-- **The VAR estimand** (AKMM, p. 226): if `Γ, a` are population least-squares coefficients of
the regression of `Y` on all of `yₜ` and the lags `w`, then `ΓΣ = ΘΣ`; so `Γ = Θ` when `Σ` is
invertible: the VAR measures the response to `uₜ = e₁` with `y_{j,t}`, `j ≥ 2`, held at zero. -/
theorem vl_var_estimand {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ)
    (Γ : Matrix n n ℝ) (a : Matrix n J ℝ)
    (horth : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Γ (u + kf_app N w) -
      kf_app a w) (u + kf_app N w) = 0)
    (horthw : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Γ (u + kf_app N w) -
      kf_app a w) w = 0) :
    Γ * var_mom μ u u = Θ * var_mom μ u u ∧ (IsUnit (var_mom μ u u).det → Γ = Θ) := by
  obtain ⟨h1, -, h3⟩ := vl_mom_resid hu hv hw huw hvw hvu Θ Ψ M N Γ a
  rw [h3, horthw, Matrix.zero_mul, add_zero, h1] at horth
  have hΓ : Γ * var_mom μ u u = Θ * var_mom μ u u := (sub_eq_zero.1 horth).symm
  refine ⟨hΓ, fun hdet => ?_⟩
  have := congrArg (· * (var_mom μ u u)⁻¹) hΓ
  simpa [Matrix.mul_assoc, mul_nonsing_inv _ hdet] using this

omit [DecidableEq n] in
/-- The VAR projection exists (AKMM, p. 226): `Γ = Θ`, `a = M − ΘN`. -/
theorem vl_var_exists {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ) :
    var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Θ (u + kf_app N w) -
      kf_app (M - Θ * N) w) (u + kf_app N w) = 0 ∧
    var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Θ (u + kf_app N w) -
      kf_app (M - Θ * N) w) w = 0 := by
  obtain ⟨h1, h2, h3⟩ := vl_mom_resid hu hv hw huw hvw hvu Θ Ψ M N Θ (M - Θ * N)
  have hw0 : (M - Θ * N - (M - Θ * N)) = 0 := sub_self _
  rw [hw0, Matrix.zero_mul] at h2
  refine ⟨?_, h2⟩
  rw [h3, h2, Matrix.zero_mul, add_zero, h1, sub_self]

/-- **Footnote 6** (Plagborg-Møller and Wolf 2021; AKMM, p. 227): the local projection is a
combination of the VAR impulse responses. If `β` is the LP estimand and `Γ` the VAR estimand,
`Σ = LL'` with `L` lower triangular (`L₁₁ ≠ 0`) and `i₁` the first variable, then
`β_i = Σⱼ Γ_{ij} wⱼ` with weights `wⱼ = L_{j1}/L₁₁` (so `w₁ = 1`), summed over the `n`
variables. -/
theorem fn_6 [LinearOrder n] {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ)
    (i1 : n) (hmin : ∀ j, i1 ≤ j) {L : Matrix n n ℝ} (hL : L.IsLowerTriangular)
    (hLS : var_mom μ u u = L * Lᵀ) (hL11 : L i1 i1 ≠ 0) (β : n → ℝ) (a : Matrix n J ℝ)
    (horth1 : ∀ i, var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) (u + kf_app N w) i i1 = 0)
    (horthw : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) w = 0)
    (Γ : Matrix n n ℝ) (a' : Matrix n J ℝ)
    (horth' : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Γ (u + kf_app N w) -
      kf_app a' w) (u + kf_app N w) = 0)
    (horthw' : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w - kf_app Γ (u + kf_app N w) -
      kf_app a' w) w = 0) (i : n) :
    β i = ∑ j, Γ i j * (L j i1 / L i1 i1) ∧ L i1 i1 / L i1 i1 = 1 := by
  have h11 : var_mom μ u u i1 i1 ≠ 0 := by
    rw [(ch_first_column hL hLS i1 hmin i1).2.1]; exact pow_ne_zero 2 hL11
  have hβ := vl_lp_estimand hu hv hw huw hvw hvu Θ Ψ M N i1 h11 β a horth1 horthw i
  have hΓ := (vl_var_estimand hu hv hw huw hvw hvu Θ Ψ M N Γ a' horth' horthw').1
  refine ⟨?_, div_self hL11⟩
  rw [hβ, ← hΓ, Matrix.mul_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_div_assoc, (ch_first_column hL hLS i1 hmin j).2.2]

/-- **The LP box** (AKMM, p. 221): if the shock of interest `y_{1,t} = z_t` is uncorrelated with
the other innovations (`Σ_{j1} = 0` for `j ≠ 1`), the local projection of `y_{i,t+h}` on `z_t`
is the impulse response `Θ_{i1}`. -/
theorem vl_lp_exogenous {u : Ω → n → ℝ} {v : Ω → K → ℝ} {w : Ω → J → ℝ} (hu : kf_L2 μ u)
    (hv : kf_L2 μ v) (hw : kf_L2 μ w) (huw : var_mom μ u w = 0) (hvw : var_mom μ v w = 0)
    (hvu : var_mom μ v u = 0) (Θ : Matrix n n ℝ) (Ψ : Matrix n K ℝ) (M N : Matrix n J ℝ)
    (i1 : n) (h11 : var_mom μ u u i1 i1 ≠ 0) (hexo : ∀ j, j ≠ i1 → var_mom μ u u j i1 = 0)
    (β : n → ℝ) (a : Matrix n J ℝ)
    (horth1 : ∀ i, var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) (u + kf_app N w) i i1 = 0)
    (horthw : var_mom μ (kf_app Θ u + kf_app Ψ v + kf_app M w -
      kf_app (vl_col β i1) (u + kf_app N w) - kf_app a w) w = 0) (i : n) :
    β i = Θ i i1 := by
  rw [vl_lp_estimand hu hv hw huw hvw hvu Θ Ψ M N i1 h11 β a horth1 horthw i, Matrix.mul_apply,
    Finset.sum_eq_single i1 (fun j _ hj => by rw [hexo j hj, mul_zero]) (by simp)]
  field_simp

/-- **The VAR(1) estimands** (AKMM, p. 226): for `y_{s+1} = Ay_s + u_{s+1}`, the outcome
`y_{t+1+h}` and the regressor `y_{t+1}` have the representation of `vl_mom_resid` with
`Θ = Aʰ`, `M = Aʰ⁺¹`, `N = A`, `w = y_t` and `v` the innovations `u_{t+1+h−k}`, `k < h`:
`y_{t+1+h} = Aʰu_{t+1} + Σ_{k<h} Aᵏu_{t+1+h−k} + Aʰ⁺¹y_t` and `y_{t+1} = u_{t+1} + Ay_t`. -/
theorem vl_var1_estimands {A : Matrix n n ℝ} {y u : ℕ → Ω → n → ℝ}
    (hrec : ∀ s ω, y (s + 1) ω = A *ᵥ y s ω + u (s + 1) ω) (t h : ℕ) :
    y (t + 1 + h) = kf_app (A ^ h) (u (t + 1)) +
        kf_app (Matrix.of fun r (q : Fin h × n) => (A ^ (q.1 : ℕ)) r q.2)
          (fun ω (q : Fin h × n) => u (t + 1 + h - q.1) ω q.2) +
        kf_app (A ^ (h + 1)) (y t) ∧
      y (t + 1) = u (t + 1) + kf_app A (y t) := by
  refine ⟨?_, ?_⟩
  · funext ω
    have hr : ∀ s, (fun s => y s ω) (s + 1) = A *ᵥ (fun s => y s ω) s +
        (1 : Matrix n n ℝ) *ᵥ (fun s => u s ω) (s + 1) := by
      intro s; rw [one_mulVec]; exact hrec s ω
    have hma := Miao.RationalExpectations.var_ma_shift (x := fun s => y s ω)
      (e := fun s => u s ω) (Φ := A) (Sg := 1) hr (t + 1) h
    simp only [Matrix.mul_one] at hma
    rw [hma, hrec t ω]
    simp only [kf_app, Pi.add_apply, mulVec_add, mulVec_mulVec, ← pow_succ]
    funext r
    simp only [Pi.add_apply, mulVec, dotProduct, of_apply, Fintype.sum_prod_type,
      Finset.sum_apply]
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ k, (A ^ i) r k * u (t + 1 + h - i) ω k) h]
    ring
  · funext ω
    rw [hrec t ω]
    simp only [kf_app, Pi.add_apply]
    rw [add_comm]

/-- **The two estimands differ** (AKMM, p. 226: "these two estimation techniques as described
above are estimating different things"): with `Θ = I` and correlated innovations
`Σ = [[1, 1/2], [1/2, 1]]`, the LP coefficient of `y₂` on `y₁` is `(ΘΣ)₂₁/Σ₁₁ = 1/2`, while the
VAR response `Θ₂₁` is `0`. -/
theorem vl_lp_differs :
    let S : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / 2; 1 / 2, 1]
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) * S) 1 0 / S 0 0 = 1 / 2 ∧
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  intro S
  constructor
  · simp [S]
  · simp

end AKMM.QuantitativeMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The dynamic fiscal model, its steady state and its calibration

AKMM, §8.6, (8.10)–(8.18), pp. 229–231; §8.6.2, p. 231; §8.8, pp. 234–237; Appendix 8.A.1,
p. 842.

* (8.11) from the accumulation equation (`eq_8_11`) and from the budgets with `T = G`
  (`fm_budget_resource`).
* The firm's first-order conditions (8.16)–(8.17) are the marginal products of `Akᵅℓ^{1−α}`
  (`eq_8_16_8_17`), the labour condition (8.15) is the first-order condition of the household's
  labour choice (`eq_8_15`), and (8.18) is the planner's condition for `G`, with the unique
  solution `G = γη/(1+γη)·x` (`eq_8_18`).
* The AR(1) processes (8.12)–(8.13) have unit mean (`eq_8_12_mean`).
* **The equilibrium** (8.10)–(8.18) (`fm_IsEquilibrium`), with the deterministic steady state as
  an equilibrium when the shocks are zero (`fm_steady_isEquilibrium`).
* **Appendix 8.A.1**: the steady state exists and is unique, with `r̄ = 1/β − 1 + δ`,
  `ȳ/k̄ = r̄/α`, `k̄/ℓ̄ = (ȳ/k̄)^{1/(α−1)}`, `ȳ/ℓ̄ = (r̄/α)^{α/(α−1)}`, `w̄ = (1−α)ȳ/ℓ̄`,
  `c̄ = w̄ℓ̄^{−ψ}`, `Ḡ = γc̄` and the scalar equation for `ℓ̄` (`appendix_8A_1`,
  `appendix_8A_1_ratios`, `fm_steady_exists`). The printed rule `Ḡ = (η̄c̄γ)^{−γ₁}` is a misprint
  (`appendix_8A_1_printed_G`).
* **§8.6.2**: with capital and investment fixed, the multiplier is between zero and one
  (`fm_fixed_investment_multiplier`).
* **Calibration** (§8.8): `β = (1 + αȳ/k̄ − δ)⁻¹` (`fm_beta_calibration`), the Frisch elasticity
  `1/ψ` (`fm_frisch`, from Miao's `rb_u39_frisch`), `dℓ/dc = −(1/ψ)ℓ/c` (`fm_dl_dc`), the
  lottery formula and its inversion for `ψ` (`fm_lottery`), `γ = Ḡ/c̄` (`fm_gamma_calibration`),
  and the scale invariance of the multiplier in a linear solution (`fm_multiplier_scale`).

Departure: the household's Euler equation (8.14) is stated by the book from Chapter 7 and enters
the equilibrium definition as stated; it is not re-derived.
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Filter Topology

/-! ### The first-order conditions -/

/-- **(8.16)–(8.17)** (AKMM, p. 230): for `y = Akᵅℓ^{1−α}` with `k, ℓ > 0`, the marginal
products are `∂y/∂k = αy/k` and `∂y/∂ℓ = (1−α)y/ℓ`, and they exhaust output,
`(αy/k)k + ((1−α)y/ℓ)ℓ = y`. -/
theorem eq_8_16_8_17 {A α k ℓ : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) :
    HasDerivAt (fun x => A * x ^ α * ℓ ^ (1 - α)) (α * (A * k ^ α * ℓ ^ (1 - α)) / k) k ∧
      HasDerivAt (fun x => A * k ^ α * x ^ (1 - α))
        ((1 - α) * (A * k ^ α * ℓ ^ (1 - α)) / ℓ) ℓ ∧
      α * (A * k ^ α * ℓ ^ (1 - α)) / k * k +
        (1 - α) * (A * k ^ α * ℓ ^ (1 - α)) / ℓ * ℓ = A * k ^ α * ℓ ^ (1 - α) := by
  refine ⟨?_, ?_, by field_simp; ring⟩
  · have := ((Real.hasDerivAt_rpow_const (Or.inl hk.ne') (p := α)).const_mul A).mul_const
      (ℓ ^ (1 - α))
    convert this using 1
    rw [Real.rpow_sub_one hk.ne']
    field_simp
  · have := (Real.hasDerivAt_rpow_const (Or.inl hℓ.ne') (p := 1 - α)).const_mul (A * k ^ α)
    convert this using 1
    rw [Real.rpow_sub_one hℓ.ne']
    field_simp

/-- **(8.11)** (AKMM, p. 229): `k_{t+1} = (1 − δ)k_t + I_t` and `y_t = c_t + I_t + G_t` give
`y_t = c_t + k_{t+1} − (1 − δ)k_t + G_t`. -/
theorem eq_8_11 {y c I G k k' δ : ℝ} (hk : k' = (1 - δ) * k + I) (hy : y = c + I + G) :
    y = c + k' - (1 - δ) * k + G := by
  rw [hy, hk]; ring

/-- AKMM, pp. 229–230: the household budget `c + k' = (1 + r − δ)k + wℓ − T` (the book prints
`K_t` for `k_t`), the government budget `T = G` and zero profits `y = rk + wℓ` give the resource
constraint (8.11). -/
theorem fm_budget_resource {y c k k' r w ℓ T G δ : ℝ}
    (hb : c + k' = (1 + r - δ) * k + w * ℓ - T) (hT : T = G) (hπ : y = r * k + w * ℓ) :
    y = c + k' - (1 - δ) * k + G := by
  rw [hπ]; rw [hT] at hb; linarith

/-- **(8.15)** (AKMM, p. 230): the household's labour choice. With other income `x` and wage
`w > 0`, `ℓ ↦ log(x + wℓ) − ℓ^{1+ψ}/(1+ψ)` has derivative `w/c − ℓ^ψ` at `ℓ > 0`
(`c = x + wℓ > 0`), which vanishes iff `w/c = ℓ^ψ`. -/
theorem eq_8_15 {ψ x w ℓ : ℝ} (hψ : 0 < ψ) (hℓ : 0 < ℓ) (hc : 0 < x + w * ℓ) :
    HasDerivAt (fun l => Real.log (x + w * l) - l ^ (1 + ψ) / (1 + ψ))
      (w / (x + w * ℓ) - ℓ ^ ψ) ℓ ∧
      (w / (x + w * ℓ) - ℓ ^ ψ = 0 ↔ w / (x + w * ℓ) = ℓ ^ ψ) := by
  refine ⟨?_, sub_eq_zero⟩
  have h1 : HasDerivAt (fun l => x + w * l) w ℓ := by
    simpa using ((hasDerivAt_id ℓ).const_mul w).const_add x
  have h2 := h1.log hc.ne'
  have h3 := (Real.hasDerivAt_rpow_const (Or.inl hℓ.ne') (p := 1 + ψ)).div_const (1 + ψ)
  convert h2.sub h3 using 1
  rw [show 1 + ψ - 1 = ψ by ring]
  field_simp

/-- **(8.18)** (AKMM, p. 230): the planner's choice of `G` given resources `x = c + G`.
`G ↦ log(x − G) + γη log G` has derivative `−1/c + γη/G`, which vanishes iff `γη/G = 1/c`, and
on `0 < G < x` this holds exactly at `G = γη/(1+γη)·x`. -/
theorem eq_8_18 {γ η x G : ℝ} (hγη : 0 < γ * η) (hG : 0 < G) (hGx : G < x) :
    HasDerivAt (fun g => Real.log (x - g) + γ * η * Real.log g)
      (-(1 / (x - G)) + γ * η / G) G ∧
      (γ * η / G = 1 / (x - G) ↔ G = γ * η / (1 + γ * η) * x) := by
  have hc : 0 < x - G := by linarith
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun g => x - g) (-1) G := by
      simpa using (hasDerivAt_id G).const_sub x
    have h2 := (h1.log hc.ne').add ((Real.hasDerivAt_log hG.ne').const_mul (γ * η))
    convert h2 using 1
    field_simp
  · have hX : 0 < 1 + γ * η := by linarith
    constructor
    · intro h
      field_simp at h
      field_simp
      linarith
    · intro h
      have hγ0 : γ ≠ 0 := left_ne_zero_of_mul hγη.ne'
      have hη0 : η ≠ 0 := right_ne_zero_of_mul hγη.ne'
      have hx0 : x ≠ 0 := by linarith
      rw [h]
      field_simp
      ring

/-- **(8.12)–(8.13)** (AKMM, p. 230): the AR(1) `Aₜ₊₁ = (1 − ρ) + ρAₜ + εₜ₊₁` with integrable
`A₀`, `εₜ`, `E A₀ = 1` and `E εₜ = 0` on a probability space has `E Aₜ = 1` for all `t`; and `1`
is its deterministic steady state, the unique one for `ρ ≠ 1`. -/
theorem eq_8_12_mean {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ρ : ℝ} {A ε : ℕ → Ω → ℝ}
    (hrec : ∀ t ω, A (t + 1) ω = (1 - ρ) + ρ * A t ω + ε (t + 1) ω)
    (hA : ∀ t, Integrable (A t) μ) (hε : ∀ t, Integrable (ε t) μ) (h0 : ∫ ω, A 0 ω ∂μ = 1)
    (hε0 : ∀ t, ∫ ω, ε t ω ∂μ = 0) :
    (∀ t, ∫ ω, A t ω ∂μ = 1) ∧ (1 - ρ) + ρ * 1 = (1 : ℝ) ∧
      (ρ ≠ 1 → ∀ a : ℝ, (1 - ρ) + ρ * a = a → a = 1) := by
  refine ⟨fun t => ?_, by ring, fun hρ a ha => ?_⟩
  · induction t with
    | zero => exact h0
    | succ t ih =>
      have e : ∫ ω, A (t + 1) ω ∂μ = ∫ ω, ((1 - ρ) + ρ * A t ω) + ε (t + 1) ω ∂μ := by
        simp only [hrec t]
      have hi1 : Integrable (fun ω => (1 - ρ) + ρ * A t ω) μ :=
        (integrable_const _).add ((hA t).const_mul ρ)
      rw [e, integral_add hi1 (hε _), integral_add (integrable_const (1 - ρ))
        ((hA t).const_mul ρ), integral_const_mul, ih, hε0]
      simp
  · have : (1 - ρ) * (a - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (by linarith) hρ
    · linarith

/-! ### The equilibrium and its steady state -/

/-- **The equilibrium** (AKMM, p. 230): processes `k, c, y, ℓ, G, r, w, A, η` (adapted to `ℱ`)
with the shocks `ε_A, ε_η` satisfying (8.10)–(8.18), with (8.14) as an almost-sure equality of
conditional expectations. -/
def fm_IsEquilibrium {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (α β δ ψ γ ρA ρη : ℝ) (k c y ℓ G r w A η εA εη : ℕ → Ω → ℝ) :
    Prop :=
  (∀ t ω, y t ω = A t ω * k t ω ^ α * ℓ t ω ^ (1 - α)) ∧
    (∀ t ω, y t ω = c t ω + k (t + 1) ω - (1 - δ) * k t ω + G t ω) ∧
    (∀ t ω, A (t + 1) ω = (1 - ρA) + ρA * A t ω + εA (t + 1) ω) ∧
    (∀ t ω, η (t + 1) ω = (1 - ρη) + ρη * η t ω + εη (t + 1) ω) ∧
    (∀ t, (fun ω => 1 / c t ω) =ᵐ[μ]
      μ[fun ω => β * ((1 + r (t + 1) ω - δ) * (1 / c (t + 1) ω)) | ℱ t]) ∧
    (∀ t ω, w t ω / c t ω = ℓ t ω ^ ψ) ∧
    (∀ t ω, r t ω = α * y t ω / k t ω) ∧
    (∀ t ω, w t ω = (1 - α) * y t ω / ℓ t ω) ∧
    (∀ t ω, γ * η t ω / G t ω = 1 / c t ω)

/-- **The steady state** (AKMM, Appendix 8.A.1, p. 842): `Ā = η̄ = 1` and (8.10)–(8.18) with
constant values. -/
def fm_IsSteady (α β δ ψ γ k c y ℓ G r w : ℝ) : Prop :=
  0 < k ∧ 0 < c ∧ 0 < ℓ ∧ 0 < G ∧ y = k ^ α * ℓ ^ (1 - α) ∧ y = c + δ * k + G ∧
    1 = β * (1 + r - δ) ∧ w / c = ℓ ^ ψ ∧ r = α * y / k ∧ w = (1 - α) * y / ℓ ∧
    γ / G = 1 / c

/-- AKMM, p. 842: `r̄ = 1/β − 1 + δ`. -/
noncomputable def fm_r (β δ : ℝ) : ℝ := 1 / β - 1 + δ

/-- AKMM, p. 842: `k̄/ℓ̄ = (r̄/α)^{1/(α−1)}`. -/
noncomputable def fm_kl (α β δ : ℝ) : ℝ := (fm_r β δ / α) ^ (α - 1)⁻¹

/-- AKMM, p. 842: `ℓ̄`, the root of `(ȳ/ℓ̄ − δk̄/ℓ̄)ℓ̄ = (1+γ)w̄ℓ̄^{−ψ}`. -/
noncomputable def fm_l (α β δ ψ γ : ℝ) : ℝ :=
  ((1 + γ) * ((1 - α) * fm_kl α β δ ^ α) / (fm_kl α β δ ^ α - δ * fm_kl α β δ)) ^ (1 + ψ)⁻¹

/-- The hypotheses on the parameters used for the steady state. -/
def fm_Params (α β δ ψ γ : ℝ) : Prop :=
  0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧ 0 ≤ δ ∧ 0 < ψ ∧ 0 < γ

theorem fm_r_pos {α β δ : ℝ} (hp : 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧ 0 ≤ δ) :
    α * δ < fm_r β δ := by
  obtain ⟨ha0, ha1, hb0, hb1, hd⟩ := hp
  have : 1 < 1 / β := by rw [lt_div_iff₀ hb0]; linarith
  unfold fm_r
  nlinarith

/-- `κ = k̄/ℓ̄ > 0`, `κ^{α−1} = r̄/α`, `κᵅ = κ·r̄/α`, and `κᵅ − δκ > 0`. -/
theorem fm_kl_props {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    0 < fm_kl α β δ ∧ fm_kl α β δ ^ (α - 1) = fm_r β δ / α ∧
      fm_kl α β δ ^ α = fm_kl α β δ * (fm_r β δ / α) ∧
      0 < fm_kl α β δ ^ α - δ * fm_kl α β δ := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩ := hp
  have hr := fm_r_pos ⟨ha0, ha1, hb0, hb1, hd⟩
  have hrpos : 0 < fm_r β δ / α := div_pos (by nlinarith) ha0
  have hκ : 0 < fm_kl α β δ := Real.rpow_pos_of_pos hrpos _
  have h1 : fm_kl α β δ ^ (α - 1) = fm_r β δ / α :=
    Real.rpow_inv_rpow hrpos.le (by linarith)
  have h2 : fm_kl α β δ ^ α = fm_kl α β δ * (fm_r β δ / α) := by
    rw [← h1, ← Real.rpow_one_add' hκ.le (by linarith)]
    ring_nf
  refine ⟨hκ, h1, h2, ?_⟩
  rw [h2]
  have : δ < fm_r β δ / α := by rw [lt_div_iff₀ ha0]; linarith
  nlinarith

/-- `kᵅℓ^{1−α} = (k/ℓ)ᵅℓ` for `k, ℓ > 0`. -/
theorem fm_cd_ratio {α k ℓ : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) :
    k ^ α * ℓ ^ (1 - α) = (k / ℓ) ^ α * ℓ := by
  rw [Real.div_rpow hk.le hℓ.le, Real.rpow_sub hℓ, Real.rpow_one]
  have := Real.rpow_pos_of_pos hℓ α
  field_simp

/-- **Appendix 8.A.1** (AKMM, p. 842): every steady state is given by the book's formulas:
`r̄ = 1/β − 1 + δ`, `k̄ = κℓ̄` with `κ = (r̄/α)^{1/(α−1)}`, `ȳ = κᵅℓ̄`, `w̄ = (1−α)κᵅ`,
`c̄ = w̄ℓ̄^{−ψ}`, `Ḡ = γc̄` and `ℓ̄ = ((1+γ)w̄/(κᵅ − δκ))^{1/(1+ψ)}`. -/
theorem appendix_8A_1 {α β δ ψ γ k c y ℓ G r w : ℝ} (hp : fm_Params α β δ ψ γ)
    (hs : fm_IsSteady α β δ ψ γ k c y ℓ G r w) :
    r = fm_r β δ ∧ ℓ = fm_l α β δ ψ γ ∧ k = fm_kl α β δ * ℓ ∧ y = fm_kl α β δ ^ α * ℓ ∧
      w = (1 - α) * fm_kl α β δ ^ α ∧ c = w * ℓ ^ (-ψ) ∧ G = γ * c := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩ := hp
  obtain ⟨hk, hc, hℓ, hG, hY, hR, hE, hL, hr, hw, hGc⟩ := hs
  obtain ⟨hκ, hκ1, -, hden⟩ := fm_kl_props ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩
  have hr' : r = fm_r β δ := by unfold fm_r; field_simp; linarith
  -- the capital–labour ratio
  have hx : 0 < k / ℓ := div_pos hk hℓ
  have hy : y = (k / ℓ) ^ α * ℓ := by rw [hY, fm_cd_ratio hk hℓ]
  have hyk : y / k = (k / ℓ) ^ (α - 1) := by
    rw [hy, Real.rpow_sub_one hx.ne']; field_simp
  have hyk' : y / k = fm_r β δ / α := by
    rw [← hr', hr]; field_simp
  have hkl : k / ℓ = fm_kl α β δ :=
    (sm_eq_rpow_inv_iff hx (div_pos (by nlinarith [fm_r_pos ⟨ha0, ha1, hb0, hb1, hd⟩]) ha0)
      (by linarith)).2 (by rw [← hyk, hyk'])
  have hk' : k = fm_kl α β δ * ℓ := by rw [← hkl]; field_simp
  have hy' : y = fm_kl α β δ ^ α * ℓ := by rw [hy, hkl]
  have hw' : w = (1 - α) * fm_kl α β δ ^ α := by rw [hw, hy']; field_simp
  have hc' : c = w * ℓ ^ (-ψ) := by
    rw [Real.rpow_neg hℓ.le]
    have := Real.rpow_pos_of_pos hℓ ψ
    field_simp at hL ⊢
    linarith
  have hG' : G = γ * c := by field_simp at hGc; linarith
  refine ⟨hr', ?_, hk', hy', hw', hc', hG'⟩
  -- the scalar equation for ℓ
  have hpow : ℓ ^ (1 + ψ) = (1 + γ) * ((1 - α) * fm_kl α β δ ^ α) /
      (fm_kl α β δ ^ α - δ * fm_kl α β δ) := by
    rw [eq_div_iff hden.ne', Real.rpow_add hℓ, Real.rpow_one]
    have hlψ := Real.rpow_pos_of_pos hℓ ψ
    have hR' := hR
    rw [hy', hk', hG', hc', hw', Real.rpow_neg hℓ.le] at hR'
    field_simp at hR'
    nlinarith [hR']
  exact (sm_eq_rpow_inv_iff hℓ (by
    have : 0 < (1 - α) * fm_kl α β δ ^ α := mul_pos (by linarith) (Real.rpow_pos_of_pos hκ α)
    positivity) (by linarith)).2 hpow

/-- **The steady state exists** (AKMM, Appendix 8.A.1, p. 842): the book's formulas satisfy
(8.10)–(8.18) at `Ā = η̄ = 1`. With `appendix_8A_1`, the steady state is unique. -/
theorem fm_steady_exists {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    fm_IsSteady α β δ ψ γ (fm_kl α β δ * fm_l α β δ ψ γ)
      ((1 - α) * fm_kl α β δ ^ α * fm_l α β δ ψ γ ^ (-ψ))
      (fm_kl α β δ ^ α * fm_l α β δ ψ γ) (fm_l α β δ ψ γ)
      (γ * ((1 - α) * fm_kl α β δ ^ α * fm_l α β δ ψ γ ^ (-ψ))) (fm_r β δ)
      ((1 - α) * fm_kl α β δ ^ α) := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩ := hp
  obtain ⟨hκ, -, hκα, hden⟩ := fm_kl_props ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩
  set κ := fm_kl α β δ with hκ_def
  set ℓ := fm_l α β δ ψ γ with hℓ_def
  have hpa : 0 < κ ^ α := Real.rpow_pos_of_pos hκ α
  have hwpos : 0 < (1 - α) * κ ^ α := mul_pos (by linarith) hpa
  have hbase : 0 < (1 + γ) * ((1 - α) * κ ^ α) / (κ ^ α - δ * κ) := by positivity
  have hℓ : 0 < ℓ := Real.rpow_pos_of_pos hbase _
  have hℓp : ℓ ^ (1 + ψ) = (1 + γ) * ((1 - α) * κ ^ α) / (κ ^ α - δ * κ) :=
    Real.rpow_inv_rpow hbase.le (by linarith)
  have hlψ : 0 < ℓ ^ ψ := Real.rpow_pos_of_pos hℓ ψ
  have hneg : ℓ ^ (-ψ) = (ℓ ^ ψ)⁻¹ := Real.rpow_neg hℓ.le ψ
  have hc : 0 < (1 - α) * κ ^ α * ℓ ^ (-ψ) := by rw [hneg]; positivity
  have h1a : (1 - α) ≠ 0 := by linarith
  refine ⟨mul_pos hκ hℓ, hc, hℓ, mul_pos hγ hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fm_cd_ratio (mul_pos hκ hℓ) hℓ]; field_simp
  · rw [hneg]
    rw [Real.rpow_add hℓ, Real.rpow_one] at hℓp
    field_simp
    rw [eq_div_iff hden.ne'] at hℓp
    nlinarith [hℓp]
  · unfold fm_r; field_simp; ring
  · rw [hneg]; field_simp
  · rw [hκα, fm_r]; field_simp
  · field_simp
  · field_simp

/-- **The ratios of Appendix 8.A.1** (AKMM, p. 842): at the steady state, `ȳ/k̄ = r̄/α`,
`k̄/ℓ̄ = (ȳ/k̄)^{1/(α−1)}` and `ȳ/ℓ̄ = (ȳ/k̄)(k̄/ℓ̄) = (r̄/α)^{α/(α−1)}`. -/
theorem appendix_8A_1_ratios {α β δ ψ γ k c y ℓ G r w : ℝ} (hp : fm_Params α β δ ψ γ)
    (hs : fm_IsSteady α β δ ψ γ k c y ℓ G r w) :
    y / k = r / α ∧ k / ℓ = (y / k) ^ (α - 1)⁻¹ ∧ y / ℓ = y / k * (k / ℓ) ∧
      y / ℓ = (r / α) ^ (α / (α - 1)) := by
  obtain ⟨hr, -, hk, hy, -, -, -⟩ := appendix_8A_1 hp hs
  obtain ⟨ha0, ha1, hb0, hb1, hd, -, -⟩ := hp
  obtain ⟨hk0, -, hℓ, -, -, -, -, -, hrr, -, -⟩ := hs
  have hyk : y / k = r / α := by rw [hrr]; field_simp
  refine ⟨hyk, ?_, by field_simp, ?_⟩
  · rw [hyk, hr, hk]; unfold fm_kl; field_simp
  · rw [hy, hr]
    unfold fm_kl
    rw [← Real.rpow_mul (div_pos (by nlinarith [fm_r_pos ⟨ha0, ha1, hb0, hb1, hd⟩]) ha0).le]
    field_simp

/-- **The printed government rule** (AKMM, p. 842): the book prints `Ḡ = (η̄c̄γ)^{−γ₁}`; by
(8.18) at `η̄ = 1` the rule is `Ḡ = γc̄` (as in the main text, `γ = Ḡ/c̄`, p. 236). The printed
rule agrees with it for all `c̄ > 0` only if `γ₁ = −1`. -/
theorem appendix_8A_1_printed_G {γ g1 : ℝ} (hγ : 0 < γ)
    (h : ∀ c : ℝ, 0 < c → (1 * c * γ) ^ (-g1) = γ * c) : g1 = -1 := by
  have h1 := h (Real.exp 1 / γ) (by positivity)
  rw [show 1 * (Real.exp 1 / γ) * γ = Real.exp 1 by field_simp,
    show γ * (Real.exp 1 / γ) = Real.exp 1 by field_simp] at h1
  have h2 := congrArg Real.log h1
  rw [Real.log_rpow (Real.exp_pos 1), Real.log_exp] at h2
  linarith

/-- **The steady state is an equilibrium** (AKMM, pp. 230–231, 842): with zero shocks, the
constant processes at a steady state satisfy (8.10)–(8.18). -/
theorem fm_steady_isEquilibrium {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {α β δ ψ γ ρA ρη k c y ℓ G r w : ℝ}
    (hs : fm_IsSteady α β δ ψ γ k c y ℓ G r w) :
    fm_IsEquilibrium μ ℱ α β δ ψ γ ρA ρη (fun _ _ => k) (fun _ _ => c) (fun _ _ => y)
      (fun _ _ => ℓ) (fun _ _ => G) (fun _ _ => r) (fun _ _ => w) (fun _ _ => 1)
      (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) := by
  obtain ⟨hk, hc, hℓ, hG, hY, hR, hE, hL, hr, hw, hGc⟩ := hs
  refine ⟨fun _ _ => by rw [hY, one_mul], fun _ _ => by rw [hR]; ring,
    fun _ _ => by ring, fun _ _ => by ring, fun t => ?_, fun _ _ => hL, fun _ _ => hr,
    fun _ _ => hw, fun _ _ => by rw [mul_one]; exact hGc⟩
  rw [condExp_const (ℱ.le t)]
  refine Filter.Eventually.of_forall fun _ => ?_
  change 1 / c = β * ((1 + r - δ) * (1 / c))
  rw [← mul_assoc, ← hE, one_mul]

/-! ### The multiplier with investment fixed -/

/-- **§8.6.2** (AKMM, p. 231): with `k` and investment `I` fixed (`Z = Akᵅ > 0`), the period
equilibrium `y = Zℓ^{1−α}`, `c = y − I − G`, `w/c = ℓ^ψ`, `w = (1−α)y/ℓ` is parametrised by
`ℓ`: `y(ℓ) = Zℓ^{1−α}`, `G(ℓ) = Zℓ^{1−α} − I − (1−α)Zℓ^{−α−ψ}`. At `ℓ̄ > 0`, `G` has a positive
strict derivative, so near `Ḡ = G(ℓ̄)` there is a local inverse `φ`, and output as a function of
spending, `y ∘ φ`, has derivative `y′(ℓ̄)/G′(ℓ̄) ∈ (0, 1)`: the multiplier is between zero and
one. -/
theorem fm_fixed_investment_multiplier {α ψ Z I lbar : ℝ} (ha0 : 0 ≤ α) (ha1 : α < 1)
    (hψ : 0 < ψ) (hZ : 0 < Z) (hl : 0 < lbar) :
    let yf : ℝ → ℝ := fun l => Z * l ^ (1 - α)
    let Gf : ℝ → ℝ := fun l => Z * l ^ (1 - α) - I - (1 - α) * Z * l ^ (-α - ψ)
    (∀ l, 0 < l → (1 - α) * yf l / l / (yf l - I - Gf l) = l ^ ψ) ∧
    ∃ φ : ℝ → ℝ, ∃ m : ℝ, φ (Gf lbar) = lbar ∧ (∀ᶠ g in 𝓝 (Gf lbar), Gf (φ g) = g) ∧
      HasStrictDerivAt (yf ∘ φ) m (Gf lbar) ∧ 0 < m ∧ m < 1 := by
  intro yf Gf
  have h1a : 0 < 1 - α := by linarith
  refine ⟨fun l hl0 => ?_, ?_⟩
  · simp only [yf, Gf]
    have e1 : Z * l ^ (1 - α) - I - (Z * l ^ (1 - α) - I - (1 - α) * Z * l ^ (-α - ψ)) =
        (1 - α) * Z * l ^ (-α - ψ) := by ring
    rw [e1, Real.rpow_sub hl0, Real.rpow_one, Real.rpow_sub hl0, Real.rpow_neg hl0.le]
    have := Real.rpow_pos_of_pos hl0 α
    have := Real.rpow_pos_of_pos hl0 ψ
    field_simp
  · set dy := (1 - α) * Z * lbar ^ (1 - α - 1) with hdy
    set dG := (1 - α) * Z * lbar ^ (1 - α - 1) +
      (1 - α) * Z * (α + ψ) * lbar ^ (-α - ψ - 1) with hdG
    have hyd : HasStrictDerivAt yf dy lbar := by
      have := (Real.hasStrictDerivAt_rpow_const_of_ne hl.ne' (1 - α)).const_mul Z
      exact this.congr_deriv (by rw [hdy]; ring)
    have hGd : HasStrictDerivAt Gf dG lbar := by
      have h1 := (Real.hasStrictDerivAt_rpow_const_of_ne hl.ne' (1 - α)).const_mul Z
      have h2 := (Real.hasStrictDerivAt_rpow_const_of_ne hl.ne' (-α - ψ)).const_mul
        ((1 - α) * Z)
      have h3 : HasStrictDerivAt (fun l => Z * l ^ (1 - α) - I - (1 - α) * Z * l ^ (-α - ψ))
          (Z * ((1 - α) * lbar ^ (1 - α - 1)) - (1 - α) * Z * ((-α - ψ) * lbar ^ (-α - ψ - 1)))
          lbar := (h1.sub_const I).sub h2
      exact HasStrictDerivAt.congr_deriv h3 (by rw [hdG]; ring)
    have hdy0 : 0 < dy := by rw [hdy]; have := Real.rpow_pos_of_pos hl (1 - α - 1); positivity
    have hextra : 0 < (1 - α) * Z * (α + ψ) * lbar ^ (-α - ψ - 1) := by
      have := Real.rpow_pos_of_pos hl (-α - ψ - 1)
      have : 0 < α + ψ := by linarith
      positivity
    have hdG0 : dG ≠ 0 := by rw [hdG]; linarith
    set φ := hGd.localInverse Gf dG lbar hdG0
    have hφ := hGd.to_localInverse hdG0
    have hφG : φ (Gf lbar) = lbar := (hGd.eventually_left_inverse hdG0).self_of_nhds
    refine ⟨φ, dy * dG⁻¹, hφG, hGd.eventually_right_inverse hdG0, ?_, ?_, ?_⟩
    · have hyd' : HasStrictDerivAt yf dy (φ (Gf lbar)) := by rw [hφG]; exact hyd
      exact hyd'.comp (Gf lbar) hφ
    · have : 0 < dG := by rw [hdG]; linarith
      positivity
    · have hpos : 0 < dG := by rw [hdG]; linarith
      rw [← div_eq_mul_inv, div_lt_one hpos, hdG]
      linarith

/-! ### Calibration (§8.8) -/

/-- **The discount factor** (AKMM, p. 235): from (8.14) and (8.16) in the steady state,
`1 = β(1 + r̄ − δ)` and `r̄ = αȳ/k̄` give `β = (1 + αȳ/k̄ − δ)⁻¹`. -/
theorem fm_beta_calibration {α β δ r y k : ℝ} (hE : 1 = β * (1 + r - δ))
    (hr : r = α * y / k) : β = (1 + α * y / k - δ)⁻¹ := by
  rw [← hr]
  have : 1 + r - δ ≠ 0 := fun h => by rw [h, mul_zero] at hE; exact one_ne_zero hE
  field_simp
  linarith

/-- **The Frisch elasticity is `1/ψ`** (AKMM, p. 235): holding the marginal utility of
consumption `λ = 1/c` fixed, (8.15) `λw = ℓ^ψ` holds iff `ℓ = (λw)^{1/ψ}`, and along
`w(s) = weˢ`, `log ℓ(s) = log ℓ + s/ψ`. From Miao's `rb_u39_frisch` with `χ = 1`. -/
theorem fm_frisch {ψ lam w ℓ : ℝ} (hψ : 0 < ψ) (hlam : 0 < lam) (hw : 0 < w) (hℓ : 0 < ℓ) :
    (ℓ ^ ψ = lam * w ↔ ℓ = (lam * w) ^ ψ⁻¹) ∧
      ∀ s : ℝ, Real.log ((lam * (w * Real.exp s)) ^ ψ⁻¹) =
        Real.log ((lam * w) ^ ψ⁻¹) + s / ψ := by
  obtain ⟨h1, h2⟩ := Miao.NeoclassicalGrowth.rb_u39_frisch (χ := 1) hψ one_pos hlam hw hℓ
  refine ⟨?_, fun s => ?_⟩
  · simpa using h1
  · simpa using h2 s

/-- **`dℓ/dc = −(1/ψ)ℓ/c`** (AKMM, p. 235): solving (8.15) for `ℓ(c) = (w/c)^{1/ψ}` and
differentiating with respect to `c`. -/
theorem fm_dl_dc {ψ w c : ℝ} (hψ : 0 < ψ) (hw : 0 < w) (hc : 0 < c) :
    HasDerivAt (fun x => (w / x) ^ ψ⁻¹) (-(1 / ψ) * ((w / c) ^ ψ⁻¹ / c)) c := by
  have h1 : HasDerivAt (fun x => w / x) (-(w / c ^ 2)) c := by
    have := (hasDerivAt_inv hc.ne').const_mul w
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp
  have h2 := h1.rpow_const (p := ψ⁻¹) (Or.inl (div_pos hw hc).ne')
  convert h2 using 1
  rw [Real.rpow_sub_one (div_pos hw hc).ne']
  field_simp

/-- **The lottery calibration** (AKMM, p. 235): a windfall `W` raises consumption by the annuity
value `dc = (r/(1+r))W`; with `dℓ = −(1/ψ)(ℓ/c)dc`, annual earnings change by
`Δ = 4w dℓ = −(4/ψ)(wℓ/c)(r/(1+r))W`; for `Δ ≠ 0` this gives
`ψ = −(4/Δ)(wℓ/c)(r/(1+r))W`. -/
theorem fm_lottery {ψ w ℓ c r W Δ : ℝ} (hψ : ψ ≠ 0) (hc : c ≠ 0) (hr : 1 + r ≠ 0)
    (hΔ : Δ = 4 * w * (-(1 / ψ) * (ℓ / c) * (r / (1 + r) * W))) (hΔ0 : Δ ≠ 0) :
    Δ = -(4 / ψ) * (w * ℓ / c) * (r / (1 + r)) * W ∧
      ψ = -(4 / Δ) * (w * ℓ / c) * (r / (1 + r)) * W := by
  refine ⟨by rw [hΔ]; field_simp, ?_⟩
  rw [hΔ]
  rw [hΔ] at hΔ0
  have : w * ℓ * r * W ≠ 0 := by
    intro h
    apply hΔ0
    field_simp
    linear_combination (-4) * h
  have hw0 : w ≠ 0 := by intro h; apply this; simp [h]
  have hl0 : ℓ ≠ 0 := by intro h; apply this; simp [h]
  have hr0 : r ≠ 0 := by intro h; apply this; simp [h]
  have hW0 : W ≠ 0 := by intro h; apply this; simp [h]
  field_simp

/-- **`γ = Ḡ/c̄`** (AKMM, p. 236): in the steady state (8.18) becomes `γ = Ḡ/c̄`. -/
theorem fm_gamma_calibration {γ G c : ℝ} (hG : 0 < G) (hc : 0 < c) (h : γ * 1 / G = 1 / c) :
    γ = G / c := by
  field_simp at h ⊢
  linarith

/-- AKMM, p. 236: "the linear solution scales one-for-one with the size of the shocks so the
magnitude of the fiscal shock will not affect the fiscal multiplier": responses scaled by
`s ≠ 0` have the same cumulative multiplier. -/
theorem fm_multiplier_scale {y G : ℕ → ℝ} (H : ℕ) {s : ℝ} (hs : s ≠ 0) :
    vl_cumMult (fun h => s * y h) (fun h => s * G h) H = vl_cumMult y G H := by
  unfold vl_cumMult
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_mul_left _ _ hs]

end AKMM.QuantitativeMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The linearised fiscal model and the claims of Figure 8.4

AKMM, §8.6.1–8.6.2, pp. 229–231; §8.8 and Figure 8.4, pp. 234–236; §8.9, p. 238.

The model of §8.6 ((8.10)–(8.18), `FiscalModel`) is linearised around its steady state, as the
book does for Figure 8.4, and its impulse response to a spending shock `η̂ₜ = ρᵗ` is solved in
closed form. Spending follows (8.18), `G = γηc`, so `Ĝ = η̂ + ĉ`.

* **The linearisation**: the static equations are exactly log-linear (`fd_static_exact`); the
  resource constraint and the Euler equation are linearised by their derivatives at the steady
  state (`fd_resource_linear`, `fd_euler_linear`); the coefficients are the steady-state ratios
  (`fd_ratios`). The linearised impulse-response system is `fd_IsIRF`.
* **The saddle path**: the stable root `λ ∈ (0, 1/(1+κ))` (`fd_lam_props`, `fd_lam_lt_one`),
  the closed-form response `k̂ₜ₊₁ = λk̂ₜ − φρᵗ`, `ĉₜ = pk̂ₜ + qρᵗ` solves the system
  (`fd_irf_solves`), is bounded (`fd_k_bound`) and is the only bounded solution (`fd_irf_unique`).
* **The signs of Figure 8.4 (left)**: for `0 ≤ ρ < 1/(1+κ)`, on impact consumption falls, hours
  and output rise, spending rises by less than the shock, investment falls (`fd_impact_signs`);
  consumption stays below and capital below steady state at every date (`fd_c_k_neg`).
  **Correction**: investment falls on impact only when `ρ < 1/(1+κ)`, `κ = βr̄(1−α)/(ψ+α)`; it
  rises for `1/(1+κ) < ρ ≤ 1`, e.g. for a permanent shock (`fd_investment_correction`).
* **Multipliers**: output rises by less than spending over every horizon, so every cumulative
  multiplier is below one (`fd_cum_lt`, `fd_mult_lt_one`); the impact multiplier is in `(0, 1)`
  (`fd_impact_mult`, `fd_impact_mult_mem`).
* **Persistence (§8.6.2; Fig. 8.4, right)**: the impact multiplier is strictly increasing in `ρ`
  on `[0, 1/(1+κ)]` (`fd_impact_mult_strictMonoOn_rho`); the cumulative multiplier converges as
  the horizon grows (`fd_mult_tendsto`) and its limit, the whole-horizon multiplier, is strictly
  increasing in `ρ` wherever cumulative spending rises (`fd_multInf_strictMono`, with
  `fd_inf_closed`, `fd_key`, `fd_det`, `fd_GInf_pos_top`).
* **Labour supply (Fig. 8.4, right)**: for `δ ≤ 1` the stable root rises with `ψ`
  (`fd_pencil`, `fd_le_lam`, `fd_f0_nonneg`, `fd_lam_mono_psi`) and the impact multiplier is
  strictly larger for smaller `ψ` (`fd_impact_mult_Phi`, `fd_impact_mult_antitone_psi`).

Not formalised: the 12-quarter multiplier of the figure is monotone in `ρ` and `ψ` only
numerically (the proofs above cover the impact and whole-horizon multipliers); "close to zero",
"after 5 quarters, output falls below steady state" and the relative sizes of the responses are
calibrated numbers.
-/

namespace AKMM.QuantitativeMethods

open Filter Topology Finset

/-! ### The coefficients of the linearised model -/

/-- AKMM, p. 842: the steady-state output–capital ratio `ȳ/k̄ = r̄/α`. -/
noncomputable def fd_Y (α β δ : ℝ) : ℝ := fm_r β δ / α

/-- AKMM, p. 842: the steady-state consumption–capital ratio `c̄/k̄ = (ȳ/k̄ − δ)/(1+γ)`. -/
noncomputable def fd_C (α β δ γ : ℝ) : ℝ := (fd_Y α β δ - δ) / (1 + γ)

/-- The steady-state spending–capital ratio `Ḡ/k̄ = γc̄/k̄`. -/
noncomputable def fd_g (α β δ γ : ℝ) : ℝ := γ * fd_C α β δ γ

/-- `κ = βr̄(1−α)/(ψ+α)`, the coefficient of the reduced Euler equation. -/
noncomputable def fd_kap (α β δ ψ : ℝ) : ℝ := β * fm_r β δ * (1 - α) / (ψ + α)

/-- `m = 1 − δ + r̄(1+ψ)/(ψ+α)`, the coefficient on `k̂ₜ` in the reduced capital equation. -/
noncomputable def fd_m (α β δ ψ : ℝ) : ℝ := 1 - δ + fm_r β δ * (1 + ψ) / (ψ + α)

/-- `n = (ȳ/k̄)(1−α)/(ψ+α) + (1+γ)c̄/k̄`, the coefficient on `−ĉₜ` in the capital equation. -/
noncomputable def fd_n (α β δ ψ γ : ℝ) : ℝ :=
  fd_Y α β δ * (1 - α) / (ψ + α) + (1 + γ) * fd_C α β δ γ

/-- The middle coefficient `B = (1+κ)m + 1 + nκψ` of the characteristic polynomial
`(1+κ)λ² − Bλ + m`. -/
noncomputable def fd_B (α β δ ψ γ : ℝ) : ℝ :=
  (1 + fd_kap α β δ ψ) * fd_m α β δ ψ + 1 + fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ)

/-- **The stable root** `λ`: the smaller root of `(1+κ)λ² − Bλ + m`. -/
noncomputable def fd_lam (α β δ ψ γ : ℝ) : ℝ :=
  (fd_B α β δ ψ γ - Real.sqrt (fd_B α β δ ψ γ ^ 2 - 4 * (1 + fd_kap α β δ ψ) * fd_m α β δ ψ)) /
    (2 * (1 + fd_kap α β δ ψ))

/-- The saddle-path slope `p = (m − λ)/n` of consumption in capital. -/
noncomputable def fd_p (α β δ ψ γ : ℝ) : ℝ :=
  (fd_m α β δ ψ - fd_lam α β δ ψ γ) / fd_n α β δ ψ γ

/-- `D(ρ) = m − λ(1+κ)ρ`. -/
noncomputable def fd_D (α β δ ψ γ ρ : ℝ) : ℝ :=
  fd_m α β δ ψ - fd_lam α β δ ψ γ * (1 + fd_kap α β δ ψ) * ρ

/-- The saddle-path coefficient `q = −pg/D(ρ)` of consumption on the spending shock. -/
noncomputable def fd_q (α β δ ψ γ ρ : ℝ) : ℝ :=
  -(fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ

/-- `φ = nq + g`: the fall in next period's capital per unit of the shock. -/
noncomputable def fd_phi (α β δ ψ γ ρ : ℝ) : ℝ :=
  fd_n α β δ ψ γ * fd_q α β δ ψ γ ρ + fd_g α β δ γ

/-- The impulse response of capital, `k̂₀ = 0`, `k̂ₜ₊₁ = λk̂ₜ − φρᵗ`. -/
noncomputable def fd_k (α β δ ψ γ ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t

/-- The impulse response of consumption, `ĉₜ = pk̂ₜ + qρᵗ`. -/
noncomputable def fd_c (α β δ ψ γ ρ : ℝ) (t : ℕ) : ℝ :=
  fd_p α β δ ψ γ * fd_k α β δ ψ γ ρ t + fd_q α β δ ψ γ ρ * ρ ^ t

/-- The impulse response of hours, `ℓ̂ₜ = (αk̂ₜ − ĉₜ)/(ψ+α)`. -/
noncomputable def fd_l (α β δ ψ γ ρ : ℝ) (t : ℕ) : ℝ :=
  (α * fd_k α β δ ψ γ ρ t - fd_c α β δ ψ γ ρ t) / (ψ + α)

/-- The impulse response of output, `ŷₜ = αk̂ₜ + (1−α)ℓ̂ₜ`. -/
noncomputable def fd_y (α β δ ψ γ ρ : ℝ) (t : ℕ) : ℝ :=
  α * fd_k α β δ ψ γ ρ t + (1 - α) * fd_l α β δ ψ γ ρ t

/-- The impulse response of spending, `Ĝₜ = η̂ₜ + ĉₜ` with `η̂ₜ = ρᵗ`. -/
noncomputable def fd_G (α β δ ψ γ ρ : ℝ) (t : ℕ) : ℝ := ρ ^ t + fd_c α β δ ψ γ ρ t

/-! ### Signs of the coefficients -/

/-- The coefficients: `r̄ > 0`, `ȳ/k̄ > δ`, `c̄/k̄ > 0`, `Ḡ/k̄ > 0`, `κ > 0`, `m > 1`,
`0 < Ḡ/k̄ < n`,
`(1+γ)c̄/k̄ = ȳ/k̄ − δ` and `βr̄ = 1 − β + βδ`. -/
theorem fd_coef {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    0 < fm_r β δ ∧ δ < fd_Y α β δ ∧ 0 < fd_C α β δ γ ∧ 0 < fd_g α β δ γ ∧
      0 < fd_kap α β δ ψ ∧ 1 < fd_m α β δ ψ ∧ fd_g α β δ γ < fd_n α β δ ψ γ ∧
      (1 + γ) * fd_C α β δ γ = fd_Y α β δ - δ ∧ β * fm_r β δ = 1 - β + β * δ := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩ := hp
  have hr := fm_r_pos ⟨ha0, ha1, hb0, hb1, hd⟩
  have hr0 : 0 < fm_r β δ := by nlinarith
  have hY : δ < fd_Y α β δ := by unfold fd_Y; rw [lt_div_iff₀ ha0]; linarith
  have hC : 0 < fd_C α β δ γ := by unfold fd_C; apply div_pos <;> linarith
  have hg : 0 < fd_g α β δ γ := by unfold fd_g; positivity
  have hpa : 0 < ψ + α := by linarith
  have hbr : β * fm_r β δ = 1 - β + β * δ := by unfold fm_r; field_simp
  refine ⟨hr0, hY, hC, hg, ?_, ?_, ?_, ?_, hbr⟩
  · unfold fd_kap; apply div_pos _ hpa; have : 0 < 1 - α := by linarith
    positivity
  · unfold fd_m
    have h1 : fm_r β δ < fm_r β δ * (1 + ψ) / (ψ + α) := by
      rw [lt_div_iff₀ hpa]; nlinarith
    have h2 : 1 < 1 - δ + fm_r β δ := by
      unfold fm_r; have : 1 < 1 / β := by rw [lt_div_iff₀ hb0]; linarith
      linarith
    linarith
  · unfold fd_n fd_g
    have : 0 < fd_Y α β δ * (1 - α) / (ψ + α) := by
      apply div_pos _ hpa; have : 0 < 1 - α := by linarith
      have : 0 < fd_Y α β δ := by linarith
      positivity
    nlinarith
  · unfold fd_C; field_simp

/-- The coefficients are the steady-state ratios (AKMM, Appendix 8.A.1, p. 842): at a steady
state, `ȳ/k̄ = fd_Y`, `c̄/k̄ = fd_C` and `Ḡ/k̄ = fd_g`. -/
theorem fd_ratios {α β δ ψ γ k c y ℓ G r w : ℝ} (hp : fm_Params α β δ ψ γ)
    (hs : fm_IsSteady α β δ ψ γ k c y ℓ G r w) :
    y / k = fd_Y α β δ ∧ c / k = fd_C α β δ γ ∧ G / k = fd_g α β δ γ := by
  obtain ⟨hr, -, -, -, -, -, hG⟩ := appendix_8A_1 hp hs
  obtain ⟨hyk, -, -, -⟩ := appendix_8A_1_ratios hp hs
  obtain ⟨hk, -, -, -, -, hR, -⟩ := hs
  have hγ := hp.2.2.2.2.2.2
  have hyk' : y / k = fd_Y α β δ := by rw [hyk, hr]; rfl
  have hck : c / k = fd_C α β δ γ := by
    unfold fd_C
    rw [← hyk', eq_div_iff (by linarith)]
    rw [hR, hG]
    field_simp
    ring
  refine ⟨hyk', hck, ?_⟩
  unfold fd_g
  rw [← hck, hG]
  ring

/-- **The stable root** (AKMM, §8.6.1, p. 231, "a linear approximation around the deterministic
steady state"): `0 < λ`, `(1+κ)λ < 1` and `(m − λ)(1 − (1+κ)λ) = nκψλ`. -/
theorem fd_lam_props {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    0 < fd_lam α β δ ψ γ ∧ (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ < 1 ∧
      (fd_m α β δ ψ - fd_lam α β δ ψ γ) * (1 - (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ) =
        fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ) * fd_lam α β δ ψ γ := by
  obtain ⟨-, -, -, -, hκ, hm, hgn, -, -⟩ := fd_coef hp
  have hg := (fd_coef hp).2.2.2.1
  have hψ : 0 < ψ := hp.2.2.2.2.2.1
  set κ := fd_kap α β δ ψ
  set m := fd_m α β δ ψ
  set n := fd_n α β δ ψ γ
  set B := fd_B α β δ ψ γ with hB
  have hBd : B = (1 + κ) * m + 1 + n * (κ * ψ) := rfl
  have hn : 0 < n := by linarith
  have hw : 0 < n * (κ * ψ) := by positivity
  have ha : 0 < 1 + κ := by linarith
  have ham : 1 < (1 + κ) * m := by nlinarith
  have hdisc : 0 ≤ B ^ 2 - 4 * (1 + κ) * m := by
    rw [hBd]; nlinarith [sq_nonneg ((1 + κ) * m - 1)]
  set s := Real.sqrt (B ^ 2 - 4 * (1 + κ) * m) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = B ^ 2 - 4 * (1 + κ) * m := Real.sq_sqrt hdisc
  have hlam : fd_lam α β δ ψ γ = (B - s) / (2 * (1 + κ)) := rfl
  have hBpos : 0 < B := by nlinarith
  have hsB : s < B := by nlinarith
  have hB2 : 2 < B := by rw [hBd]; linarith
  have hsB2 : B - 2 < s := by nlinarith
  rw [hlam]
  refine ⟨div_pos (by linarith) (by positivity), ?_, ?_⟩
  · rw [mul_div_assoc', div_lt_one (by positivity)]; nlinarith
  · field_simp
    nlinarith

/-- The relations among the coefficients used below: `(ψ+α)(m − 1 + δ) = (ȳ/k̄)α(1+ψ)`,
`(ψ+α)n = (ȳ/k̄)(1−α) + (ψ+α)(1+γ)c̄/k̄`, `κ(ψ+α) = βr̄(1−α)`, `(ȳ/k̄)α = r̄`, and for `ρ ≤ 1`:
`pn = m − λ`, `p(1 − (1+κ)λ) = λκψ`, `D > 0`, `qD = −pg`, `φD = gλ(1 − (1+κ)ρ)`, `p > 0`. -/
theorem fd_rel {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ : ρ ≤ 1) :
    (ψ + α) * (fd_m α β δ ψ - 1 + δ) = fd_Y α β δ * α * (1 + ψ) ∧
      (ψ + α) * fd_n α β δ ψ γ = fd_Y α β δ * (1 - α) + (ψ + α) * ((1 + γ) * fd_C α β δ γ) ∧
      fd_kap α β δ ψ * (ψ + α) = β * fm_r β δ * (1 - α) ∧ fd_Y α β δ * α = fm_r β δ ∧
      fd_p α β δ ψ γ * fd_n α β δ ψ γ = fd_m α β δ ψ - fd_lam α β δ ψ γ ∧
      fd_p α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ) =
        fd_lam α β δ ψ γ * (fd_kap α β δ ψ * ψ) ∧
      0 < fd_D α β δ ψ γ ρ ∧
      fd_q α β δ ψ γ ρ * fd_D α β δ ψ γ ρ = -(fd_p α β δ ψ γ * fd_g α β δ γ) ∧
      fd_phi α β δ ψ γ ρ * fd_D α β δ ψ γ ρ =
        fd_g α β δ γ * fd_lam α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * ρ) ∧
      0 < fd_p α β δ ψ γ := by
  obtain ⟨hr0, hY, hC, hg, hκ, hm, hgn, hCY, hbr⟩ := fd_coef hp
  obtain ⟨hl0, hl1, hchar⟩ := fd_lam_props hp
  have ha0 : 0 < α := hp.1
  have hψ : 0 < ψ := hp.2.2.2.2.2.1
  have hpa : 0 < ψ + α := by linarith
  have hn : 0 < fd_n α β δ ψ γ := by linarith
  have hpn : fd_p α β δ ψ γ * fd_n α β δ ψ γ = fd_m α β δ ψ - fd_lam α β δ ψ γ := by
    unfold fd_p; field_simp
  have hD : 0 < fd_D α β δ ψ γ ρ := by
    unfold fd_D
    have hprod : 0 < fd_lam α β δ ψ γ * (1 + fd_kap α β δ ψ) := by positivity
    have : fd_lam α β δ ψ γ * (1 + fd_kap α β δ ψ) * ρ ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hρ hprod.le]
    linarith
  have hlm : fd_lam α β δ ψ γ < fd_m α β δ ψ := by nlinarith
  have hp0 : 0 < fd_p α β δ ψ γ := by unfold fd_p; exact div_pos (by linarith) hn
  have hq : fd_q α β δ ψ γ ρ * fd_D α β δ ψ γ ρ = -(fd_p α β δ ψ γ * fd_g α β δ γ) := by
    unfold fd_q; field_simp
  refine ⟨?_, ?_, ?_, ?_, hpn, ?_, hD, hq, ?_, hp0⟩
  · unfold fd_m fd_Y; field_simp; ring
  · unfold fd_n; field_simp
  · unfold fd_kap; field_simp
  · unfold fd_Y; field_simp
  · have h2 : fd_p α β δ ψ γ * fd_n α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ) =
        fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ) * fd_lam α β δ ψ γ := by rw [hpn]; exact hchar
    have : fd_n α β δ ψ γ * (fd_p α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ) -
        fd_lam α β δ ψ γ * (fd_kap α β δ ψ * ψ)) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  · unfold fd_phi
    unfold fd_D at hq ⊢
    linear_combination fd_n α β δ ψ γ * hq - fd_g α β δ γ * hpn

/-- **The linearised equilibrium** (AKMM, (8.10)–(8.18) linearised around the steady state,
§8.6.1, p. 231), as the impulse response to a fiscal shock `η̂ₜ = ρᵗ` (AKMM, p. 236), in log
deviations `k̂, ĉ, ŷ, ℓ̂, Ĝ` with `k̂₀ = 0`: production (8.10) `ŷ = αk̂ + (1−α)ℓ̂`; the labour
condition (8.15) with (8.17), `ŷ = ĉ + (1+ψ)ℓ̂`; the spending rule (8.18), `Ĝ = η̂ + ĉ`; the
resource constraint (8.11) divided by `k̄`, `(ȳ/k̄)ŷ = (c̄/k̄)ĉ + k̂ₜ₊₁ − (1−δ)k̂ₜ + (Ḡ/k̄)Ĝ`; and
the Euler equation (8.14) with (8.16), `ĉₜ₊₁ − ĉₜ = βr̄(ŷₜ₊₁ − k̂ₜ₊₁)` (perfect foresight after
the shock, as in an impulse response). -/
def fd_IsIRF (α β δ ψ γ ρ : ℝ) (k c y l G : ℕ → ℝ) : Prop :=
  k 0 = 0 ∧ ∀ t, y t = α * k t + (1 - α) * l t ∧ y t = c t + (1 + ψ) * l t ∧
    G t = ρ ^ t + c t ∧
    fd_Y α β δ * y t = fd_C α β δ γ * c t + (k (t + 1) - (1 - δ) * k t) + fd_g α β δ γ * G t ∧
    c (t + 1) - c t = β * fm_r β δ * (y (t + 1) - k (t + 1))

/-- **The saddle-path impulse response solves the linearised model** (AKMM, §8.6.1, p. 231 and
Figure 8.4, p. 236): for `ρ ≤ 1`, the paths `k̂ₜ₊₁ = λk̂ₜ − φρᵗ`, `ĉₜ = pk̂ₜ + qρᵗ`,
`ℓ̂ₜ = (αk̂ₜ − ĉₜ)/(ψ+α)`, `ŷₜ = αk̂ₜ + (1−α)ℓ̂ₜ`, `Ĝₜ = ρᵗ + ĉₜ` satisfy `fd_IsIRF`. -/
theorem fd_irf_solves {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ : ρ ≤ 1) :
    fd_IsIRF α β δ ψ γ ρ (fd_k α β δ ψ γ ρ) (fd_c α β δ ψ γ ρ) (fd_y α β δ ψ γ ρ)
      (fd_l α β δ ψ γ ρ) (fd_G α β δ ψ γ ρ) := by
  obtain ⟨R1, R2, R4, R9, R5, R6, hD, R7, R8, -⟩ := fd_rel hp hρ
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  obtain ⟨hl0, -, -⟩ := fd_lam_props hp
  refine ⟨rfl, fun t => ⟨rfl, ?_, rfl, ?_, ?_⟩⟩
  · unfold fd_y fd_l; field_simp; ring
  · have hk1 : fd_k α β δ ψ γ ρ (t + 1) =
        fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t := rfl
    have hy : (ψ + α) * fd_y α β δ ψ γ ρ t =
        α * (1 + ψ) * fd_k α β δ ψ γ ρ t - (1 - α) * fd_c α β δ ψ γ ρ t := by
      unfold fd_y fd_l; field_simp; ring
    have R3 : fd_g α β δ γ = γ * fd_C α β δ γ := rfl
    apply mul_left_cancel₀ hpa.ne'
    unfold fd_G
    rw [hk1]
    unfold fd_c at hy ⊢
    unfold fd_phi
    linear_combination fd_Y α β δ * hy - fd_k α β δ ψ γ ρ t * R1 +
      (fd_p α β δ ψ γ * fd_k α β δ ψ γ ρ t + fd_q α β δ ψ γ ρ * ρ ^ t) * R2 -
      (ψ + α) * fd_k α β δ ψ γ ρ t * R5 -
      (ψ + α) * (fd_p α β δ ψ γ * fd_k α β δ ψ γ ρ t + fd_q α β δ ψ γ ρ * ρ ^ t) * R3
  · have hk1 : fd_k α β δ ψ γ ρ (t + 1) =
        fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t := rfl
    have hy : (ψ + α) * fd_y α β δ ψ γ ρ (t + 1) =
        α * (1 + ψ) * fd_k α β δ ψ γ ρ (t + 1) - (1 - α) * fd_c α β δ ψ γ ρ (t + 1) := by
      unfold fd_y fd_l; field_simp; ring
    have hpq : fd_p α β δ ψ γ * fd_phi α β δ ψ γ ρ =
        -(fd_q α β δ ψ γ ρ * fd_lam α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * ρ)) :=
      mul_right_cancel₀ hD.ne' (by
        linear_combination fd_p α β δ ψ γ * R8 +
          fd_lam α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * ρ) * R7)
    have hE : fd_lam α β δ ψ γ * ((1 + fd_kap α β δ ψ) * fd_c α β δ ψ γ ρ (t + 1) -
        fd_c α β δ ψ γ ρ t + fd_kap α β δ ψ * ψ * fd_k α β δ ψ γ ρ (t + 1)) = 0 := by
      unfold fd_c
      rw [hk1]
      linear_combination (-(fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t -
        fd_phi α β δ ψ γ ρ * ρ ^ t)) * R6 - ρ ^ t * hpq
    have hE0 := (mul_eq_zero.1 hE).resolve_left hl0.ne'
    apply mul_left_cancel₀ hpa.ne'
    linear_combination (ψ + α) * hE0 - β * fm_r β δ * hy -
      (ψ * fd_k α β δ ψ γ ρ (t + 1) + fd_c α β δ ψ γ ρ (t + 1)) * R4

/-- The stable root is below one: `λ < 1`. -/
theorem fd_lam_lt_one {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) : fd_lam α β δ ψ γ < 1 := by
  obtain ⟨hl0, hl1, -⟩ := fd_lam_props hp
  have hκ := (fd_coef hp).2.2.2.2.1
  nlinarith

/-- **The impulse response is bounded** for `0 ≤ ρ ≤ 1`: `|k̂ₜ| ≤ |φ|/(1 − λ)`. -/
theorem fd_k_bound {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1)
    (t : ℕ) : |fd_k α β δ ψ γ ρ t| ≤ |fd_phi α β δ ψ γ ρ| / (1 - fd_lam α β δ ψ γ) := by
  have hl0 := (fd_lam_props hp).1
  have hl1 := fd_lam_lt_one hp
  have h1 : 0 < 1 - fd_lam α β δ ψ γ := by linarith
  induction t with
  | zero => simp only [fd_k, abs_zero]; positivity
  | succ t ih =>
    have hk1 : fd_k α β δ ψ γ ρ (t + 1) =
        fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t := rfl
    have hpow : |ρ ^ t| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hρ0 t)]; exact pow_le_one₀ hρ0 hρ
    rw [hk1]
    calc |fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t|
        ≤ fd_lam α β δ ψ γ * |fd_k α β δ ψ γ ρ t| + |fd_phi α β δ ψ γ ρ| := by
          have := abs_sub (fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t)
            (fd_phi α β δ ψ γ ρ * ρ ^ t)
          rw [abs_mul, abs_mul, abs_of_pos hl0] at this
          nlinarith [abs_nonneg (fd_phi α β δ ψ γ ρ)]
      _ ≤ fd_lam α β δ ψ γ * (|fd_phi α β δ ψ γ ρ| / (1 - fd_lam α β δ ψ γ)) +
          |fd_phi α β δ ψ γ ρ| := by gcongr
      _ = |fd_phi α β δ ψ γ ρ| / (1 - fd_lam α β δ ψ γ) := by field_simp; ring

/-- **The saddle path is the unique bounded solution** (AKMM, §8.6.1, p. 231): for `0 ≤ ρ ≤ 1`,
every solution of the linearised model with `k̂` and `ĉ` bounded is the saddle-path impulse
response. The deviation `zₜ = ĉₜ − pk̂ₜ − qρᵗ` from the saddle path satisfies
`zₜ₊₁ = (m/((1+κ)λ))zₜ` with `m/((1+κ)λ) > 1`, so it is bounded only if it is zero. -/
theorem fd_irf_unique {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1)
    {k c y l G : ℕ → ℝ} (hirf : fd_IsIRF α β δ ψ γ ρ k c y l G)
    (hbdd : ∃ M, ∀ t, |k t| ≤ M ∧ |c t| ≤ M) :
    k = fd_k α β δ ψ γ ρ ∧ c = fd_c α β δ ψ γ ρ ∧ l = fd_l α β δ ψ γ ρ ∧
      y = fd_y α β δ ψ γ ρ ∧ G = fd_G α β δ ψ γ ρ := by
  obtain ⟨R1, R2, R4, -, R5, R6, hD, R7, R8, hp0⟩ := fd_rel hp hρ
  have R3 : fd_g α β δ γ = γ * fd_C α β δ γ := rfl
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  obtain ⟨hl0, hl1, -⟩ := fd_lam_props hp
  have hm := (fd_coef hp).2.2.2.2.2.1
  obtain ⟨hk0, hall⟩ := hirf
  unfold fd_D at R7 hD
  set lam := fd_lam α β δ ψ γ
  set a := 1 + fd_kap α β δ ψ
  set m := fd_m α β δ ψ
  set n := fd_n α β δ ψ γ
  set p := fd_p α β δ ψ γ
  set q := fd_q α β δ ψ γ ρ
  set g := fd_g α β δ γ
  set κ := fd_kap α β δ ψ
  -- the reduced system
  have hyl : ∀ t, (ψ + α) * y t = α * (1 + ψ) * k t - (1 - α) * c t := fun t => by
    obtain ⟨h1, h2, -⟩ := hall t
    linear_combination (1 + ψ) * h1 - (1 - α) * h2
  have hk : ∀ t, k (t + 1) = m * k t - n * c t - g * ρ ^ t := fun t => by
    obtain ⟨-, -, h3, h4, -⟩ := hall t
    apply mul_left_cancel₀ hpa.ne'
    rw [h3] at h4
    linear_combination -(ψ + α) * h4 + fd_Y α β δ * hyl t - k t * R1 + c t * R2 -
      (ψ + α) * c t * R3
  have hc : ∀ t, a * c (t + 1) = c t - κ * ψ * k (t + 1) := fun t => by
    obtain ⟨-, -, -, -, h5⟩ := hall t
    apply mul_left_cancel₀ hpa.ne'
    linear_combination (ψ + α) * h5 + β * fm_r β δ * hyl (t + 1) +
      (ψ * k (t + 1) + c (t + 1)) * R4
  -- the deviation from the saddle path
  set z : ℕ → ℝ := fun t => c t - p * k t - q * ρ ^ t with hzdef
  have hz : ∀ t, a * lam * z (t + 1) = m * z t := fun t => by
    simp only [hzdef]
    linear_combination lam * hc t + k (t + 1) * R6 - p * hk t + c t * R5 + ρ ^ t * R7
  have hκ := (fd_coef hp).2.2.2.2.1
  have hal : 0 < a * lam := by positivity
  set μ := m / (a * lam) with hμ
  have hμ1 : 1 < μ := by rw [hμ, lt_div_iff₀ hal]; linarith
  have hzt : ∀ t, z t = μ ^ t * z 0 := fun t => by
    induction t with
    | zero => simp
    | succ t ih =>
      have : z (t + 1) = μ * z t := by
        rw [hμ, div_mul_eq_mul_div, eq_div_iff hal.ne']; linear_combination hz t
      rw [this, ih]; ring
  obtain ⟨M, hM⟩ := hbdd
  have hzb : ∀ t, |z t| ≤ M + p * M + |q| := fun t => by
    obtain ⟨h1, h2⟩ := hM t
    have hpow : |ρ ^ t| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hρ0 t)]; exact pow_le_one₀ hρ0 hρ
    have e1 : |z t| ≤ |c t| + |p * k t| + |q * ρ ^ t| := by
      simp only [hzdef]
      linarith [abs_sub (c t - p * k t) (q * ρ ^ t), abs_sub (c t) (p * k t)]
    rw [abs_mul, abs_mul, abs_of_pos hp0] at e1
    nlinarith [abs_nonneg q, abs_nonneg (k t), abs_nonneg (ρ ^ t)]
  have hz0 : z 0 = 0 := by
    by_contra hne
    have hpos : 0 < |z 0| := abs_pos.2 hne
    obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hμ1).eventually_gt_atTop
      ((M + p * M + |q|) / |z 0|)).exists
    have := hzb t
    rw [hzt t, abs_mul, abs_of_pos (pow_pos (by linarith) t)] at this
    rw [div_lt_iff₀ hpos] at ht
    linarith
  have hcz : ∀ t, c t = p * k t + q * ρ ^ t := fun t => by
    have := hzt t
    rw [hz0, mul_zero] at this
    simp only [hzdef] at this
    linarith
  have hkk : k = fd_k α β δ ψ γ ρ := by
    funext t
    induction t with
    | zero => exact hk0
    | succ t ih =>
      have hk1 : fd_k α β δ ψ γ ρ (t + 1) =
          lam * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t := rfl
      rw [hk1, ← ih, hk t, hcz t]
      unfold fd_phi
      linear_combination (-k t) * R5
  have hcc : c = fd_c α β δ ψ γ ρ := by
    funext t; rw [hcz t, hkk]; rfl
  have hll : l = fd_l α β δ ψ γ ρ := by
    funext t
    obtain ⟨h1, h2, -⟩ := hall t
    unfold fd_l
    rw [← hkk, ← hcc, eq_div_iff hpa.ne']
    linear_combination h1 - h2
  refine ⟨hkk, hcc, hll, ?_, ?_⟩
  · funext t
    rw [(hall t).1, hkk, hll]; rfl
  · funext t
    rw [(hall t).2.2.1, hcc]; rfl

/-! ### The signs of the impulse responses -/

/-- For `0 ≤ ρ` and `(1+κ)ρ ≤ 1`: `q < 0`, `φ ≥ 0`, and `D − pg ≥ p(n − g) > 0`. -/
theorem fd_q_phi {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) :
    fd_q α β δ ψ γ ρ < 0 ∧ 0 ≤ fd_phi α β δ ψ γ ρ ∧
      fd_p α β δ ψ γ * (fd_n α β δ ψ γ - fd_g α β δ γ) ≤
        fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ ∧
      0 < fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ := by
  have hκ := (fd_coef hp).2.2.2.2.1
  have hρ1 : ρ ≤ 1 := by nlinarith
  obtain ⟨-, -, -, -, R5, -, hD, R7, R8, hp0⟩ := fd_rel hp hρ1
  obtain ⟨-, -, -, hg, -, -, hgn, -, -⟩ := fd_coef hp
  have hl0 := (fd_lam_props hp).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    rw [not_lt] at h
    nlinarith [mul_pos hp0 hg]
  · by_contra h
    rw [not_le] at h
    have h1 : 0 ≤ 1 - (1 + fd_kap α β δ ψ) * ρ := by linarith
    nlinarith [mul_nonneg hg.le (mul_nonneg hl0.le h1)]
  · unfold fd_D
    nlinarith [mul_le_mul_of_nonneg_left hρ hl0.le]
  · unfold fd_D
    nlinarith [mul_le_mul_of_nonneg_left hρ hl0.le, mul_pos hp0 (sub_pos.2 hgn)]

/-- Capital never rises above its steady state: for `0 ≤ ρ`, `(1+κ)ρ ≤ 1`, `k̂ₜ ≤ 0`. -/
theorem fd_k_nonpos {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) (t : ℕ) : fd_k α β δ ψ γ ρ t ≤ 0 := by
  have hl0 := (fd_lam_props hp).1
  have hφ := (fd_q_phi hp hρ0 hρ).2.1
  induction t with
  | zero => exact le_refl _
  | succ t ih =>
    have hk1 : fd_k α β δ ψ γ ρ (t + 1) =
        fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ t - fd_phi α β δ ψ γ ρ * ρ ^ t := rfl
    rw [hk1]
    nlinarith [mul_nonneg hφ (pow_nonneg hρ0 t)]

/-- **Consumption falls and stays below steady state, and capital is run down** (AKMM, p. 236,
"consumes less, and invests less"; p. 238, "a persistent decrease in consumption"): for
`0 ≤ ρ` and `(1+κ)ρ < 1`, `ĉₜ < 0` for all `t` and `k̂ₜ₊₁ < 0` for all `t`. -/
theorem fd_c_k_neg {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ < 1) (t : ℕ) :
    fd_c α β δ ψ γ ρ t < 0 ∧ fd_k α β δ ψ γ ρ (t + 1) < 0 := by
  have hρ1 : ρ ≤ 1 := by nlinarith [(fd_coef hp).2.2.2.2.1]
  obtain ⟨-, -, -, -, -, -, hD, -, R8, hp0⟩ := fd_rel hp hρ1
  obtain ⟨hq, hφ0, -, -⟩ := fd_q_phi hp hρ0 hρ.le
  have hl0 := (fd_lam_props hp).1
  have hg := (fd_coef hp).2.2.2.1
  have hφ : 0 < fd_phi α β δ ψ γ ρ := by
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_pos hg (mul_pos hl0 (by linarith : 0 < 1 - (1 + fd_kap α β δ ψ) * ρ))]
  have hk : ∀ t, fd_k α β δ ψ γ ρ (t + 1) < 0 := fun t => by
    induction t with
    | zero =>
      change fd_lam α β δ ψ γ * 0 - fd_phi α β δ ψ γ ρ * ρ ^ 0 < 0
      simp only [mul_zero, pow_zero, mul_one, zero_sub, neg_neg_iff_pos]; exact hφ
    | succ t ih =>
      have hk1 : fd_k α β δ ψ γ ρ (t + 1 + 1) = fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ (t + 1) -
          fd_phi α β δ ψ γ ρ * ρ ^ (t + 1) := rfl
      rw [hk1]
      nlinarith [mul_nonneg hφ0 (pow_nonneg hρ0 (t + 1))]
  refine ⟨?_, hk t⟩
  unfold fd_c
  cases t with
  | zero => simp only [fd_k, mul_zero, pow_zero, mul_one, zero_add]; exact hq
  | succ t =>
    nlinarith [mul_pos hp0 (neg_pos.2 (hk t)), mul_nonpos_of_nonpos_of_nonneg hq.le
      (pow_nonneg hρ0 (t + 1))]

/-- **The impact responses** (AKMM, Figure 8.4, left, p. 236: "the economy works more, consumes
less, and invests less … the increase in labor supply raises output"): for `0 ≤ ρ` and
`(1+κ)ρ < 1`, on impact `ĉ₀ < 0`, `ℓ̂₀ > 0`, `ŷ₀ > 0`, `0 < Ĝ₀ < 1`, and investment
`Î₀ = k̂₁ − (1−δ)k̂₀ = k̂₁ < 0`. -/
theorem fd_impact_signs {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ < 1) :
    fd_c α β δ ψ γ ρ 0 < 0 ∧ 0 < fd_l α β δ ψ γ ρ 0 ∧ 0 < fd_y α β δ ψ γ ρ 0 ∧
      0 < fd_G α β δ ψ γ ρ 0 ∧ fd_G α β δ ψ γ ρ 0 < 1 ∧
      fd_k α β δ ψ γ ρ 1 - (1 - δ) * fd_k α β δ ψ γ ρ 0 < 0 := by
  have hρ1 : ρ ≤ 1 := by nlinarith [(fd_coef hp).2.2.2.2.1]
  obtain ⟨-, -, -, -, -, -, hD, R7, -, hp0⟩ := fd_rel hp hρ1
  obtain ⟨hq, -, -, hDp⟩ := fd_q_phi hp hρ0 hρ.le
  obtain ⟨hc0, hk1⟩ := fd_c_k_neg hp hρ0 hρ 0
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have ha1 : 0 < 1 - α := by linarith [hp.2.1]
  have hc0' : fd_c α β δ ψ γ ρ 0 = fd_q α β δ ψ γ ρ := by
    simp only [fd_c, fd_k, mul_zero, pow_zero, mul_one, zero_add]
  have hl : 0 < fd_l α β δ ψ γ ρ 0 := by
    unfold fd_l; rw [hc0']; simp only [fd_k, mul_zero, zero_sub]
    exact div_pos (by linarith) hpa
  refine ⟨hc0, hl, ?_, ?_, ?_, ?_⟩
  · unfold fd_y; simp only [fd_k, mul_zero, zero_add]; positivity
  · unfold fd_G; rw [hc0', pow_zero]
    have hg := (fd_coef hp).2.2.2.1
    by_contra h
    rw [not_lt] at h
    nlinarith
  · unfold fd_G; rw [hc0', pow_zero]; linarith
  · simp only [fd_k, mul_zero, sub_zero] at hk1 ⊢; linarith

/-- **Correction: investment rises when the shock is persistent enough** (AKMM, p. 236, "invests
less"). The impact response of investment is `Î₀ = k̂₁ = −φ` with
`φD = gλ(1 − (1+κ)ρ)`: investment falls iff `(1+κ)ρ < 1`, is unchanged at `(1+κ)ρ = 1`, and
rises for `1/(1+κ) < ρ ≤ 1`. Since `κ > 0`, that interval is non-empty: it contains the
permanent shock `ρ = 1`. -/
theorem fd_investment_correction {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ1 : ρ ≤ 1) :
    (fd_k α β δ ψ γ ρ 1 < 0 ↔ (1 + fd_kap α β δ ψ) * ρ < 1) ∧
      (fd_k α β δ ψ γ ρ 1 = 0 ↔ (1 + fd_kap α β δ ψ) * ρ = 1) ∧
      (0 < fd_k α β δ ψ γ ρ 1 ↔ 1 < (1 + fd_kap α β δ ψ) * ρ) ∧
      1 < (1 + fd_kap α β δ ψ) * 1 := by
  obtain ⟨-, -, -, -, -, -, hD, -, R8, -⟩ := fd_rel hp hρ1
  have hl0 := (fd_lam_props hp).1
  have hg := (fd_coef hp).2.2.2.1
  have hκ := (fd_coef hp).2.2.2.2.1
  have hk1 : fd_k α β δ ψ γ ρ 1 = -fd_phi α β δ ψ γ ρ := by
    simp only [fd_k, mul_zero, pow_zero, mul_one, zero_sub]
  have hgl : 0 < fd_g α β δ γ * fd_lam α β δ ψ γ := mul_pos hg hl0
  have hφ : fd_phi α β δ ψ γ ρ = fd_g α β δ γ * fd_lam α β δ ψ γ *
      (1 - (1 + fd_kap α β δ ψ) * ρ) / fd_D α β δ ψ γ ρ := by
    rw [eq_div_iff hD.ne']; exact R8
  rw [hk1, hφ]
  refine ⟨?_, ?_, ?_, by linarith⟩
  · rw [neg_lt_zero, div_pos_iff_of_pos_right hD]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · rw [neg_eq_zero, div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · rcases mul_eq_zero.1 h with h | h
        · linarith
        · linarith
      · linarith
    · intro h; left; rw [h, sub_self, mul_zero]
  · rw [neg_pos, div_neg_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · nlinarith
    · intro h; right; exact ⟨by nlinarith, hD⟩

/-! ### Fiscal multipliers -/

/-- **The cumulative fiscal multiplier over `H` periods** (AKMM, p. 236, "integrating the output
and spending responses over the first 12 quarters"): `Σₜ<H Δyₜ / Σₜ<H ΔGₜ`, with the level
responses per unit of capital `Δyₜ/k̄ = (ȳ/k̄)ŷₜ` and `ΔGₜ/k̄ = (Ḡ/k̄)Ĝₜ`. The figure plots
`H = 12`;
`H = 1` is the impact multiplier. -/
noncomputable def fd_mult (α β δ ψ γ ρ : ℝ) (H : ℕ) : ℝ :=
  (∑ t ∈ range H, fd_Y α β δ * fd_y α β δ ψ γ ρ t) /
    ∑ t ∈ range H, fd_g α β δ γ * fd_G α β δ ψ γ ρ t

/-- **Output rises by less than spending, over every horizon** (AKMM, §8.6.2, p. 231, and
p. 236): for `0 ≤ ρ`, `(1+κ)ρ ≤ 1` and `H ≥ 1`, `Σₜ<H Δyₜ < Σₜ<H ΔGₜ`. By the resource constraint
the gap is `Σₜ<H Δcₜ + Σₜ<H ΔIₜ`; consumption is below steady state and the cumulative investment
response is `k̄(k̂_H + δΣₜ<H k̂ₜ) ≤ 0`. -/
theorem fd_cum_lt {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) {H : ℕ} (hH : 1 ≤ H) :
    ∑ t ∈ range H, fd_Y α β δ * fd_y α β δ ψ γ ρ t <
      ∑ t ∈ range H, fd_g α β δ γ * fd_G α β δ ψ γ ρ t := by
  have hρ1 : ρ ≤ 1 := by nlinarith [(fd_coef hp).2.2.2.2.1]
  obtain ⟨-, hall⟩ := fd_irf_solves hp hρ1
  obtain ⟨hq, -, -, -⟩ := fd_q_phi hp hρ0 hρ
  have hp0 := (fd_rel hp hρ1).2.2.2.2.2.2.2.2.2
  have hC := (fd_coef hp).2.2.1
  have hd := hp.2.2.2.2.1
  have hc : ∀ t, fd_c α β δ ψ γ ρ t ≤ 0 := fun t => by
    unfold fd_c
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hp0.le (fd_k_nonpos hp hρ0 hρ t),
      mul_nonpos_of_nonpos_of_nonneg hq.le (pow_nonneg hρ0 t)]
  have hc0 : fd_c α β δ ψ γ ρ 0 < 0 := by
    simp only [fd_c, fd_k, mul_zero, pow_zero, mul_one, zero_add]; exact hq
  have hdiff : ∑ t ∈ range H, fd_Y α β δ * fd_y α β δ ψ γ ρ t -
      ∑ t ∈ range H, fd_g α β δ γ * fd_G α β δ ψ γ ρ t =
      fd_C α β δ γ * ∑ t ∈ range H, fd_c α β δ ψ γ ρ t +
        (fd_k α β δ ψ γ ρ H + δ * ∑ t ∈ range H, fd_k α β δ ψ γ ρ t) := by
    have hk := Finset.sum_range_sub (fd_k α β δ ψ γ ρ) H
    have h0 : fd_k α β δ ψ γ ρ 0 = 0 := rfl
    rw [h0, sub_zero] at hk
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← hk, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [(hall t).2.2.2.1]
    ring
  have hsc : ∑ t ∈ range H, fd_c α β δ ψ γ ρ t < 0 := by
    obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have := Finset.sum_nonpos fun t (_ : t ∈ range H') => hc (t + 1)
    linarith
  have hsk : ∑ t ∈ range H, fd_k α β δ ψ γ ρ t ≤ 0 :=
    Finset.sum_nonpos fun t _ => fd_k_nonpos hp hρ0 hρ t
  have := fd_k_nonpos hp hρ0 hρ H
  nlinarith [mul_neg_of_pos_of_neg hC hsc, mul_nonpos_of_nonneg_of_nonpos hd hsk]

/-- **The cumulative multiplier is below one** whenever cumulative spending rises. -/
theorem fd_mult_lt_one {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) {H : ℕ} (hH : 1 ≤ H)
    (hG : 0 < ∑ t ∈ range H, fd_g α β δ γ * fd_G α β δ ψ γ ρ t) :
    fd_mult α β δ ψ γ ρ H < 1 := by
  unfold fd_mult
  rw [div_lt_one hG]
  exact fd_cum_lt hp hρ0 hρ hH

/-- **The impact multiplier** (AKMM, Figure 8.4, p. 236): for `ρ ≤ 1`,
`Δy₀/ΔG₀ = (ȳ/k̄)(1−α)p/((ψ+α)(D(ρ) − pg))`, with `D(ρ) = m − λ(1+κ)ρ`. -/
theorem fd_impact_mult {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ : ρ ≤ 1) :
    fd_mult α β δ ψ γ ρ 1 = fd_Y α β δ * (1 - α) * fd_p α β δ ψ γ /
      ((ψ + α) * (fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ)) := by
  obtain ⟨-, -, -, -, -, -, hD, R7, -, -⟩ := fd_rel hp hρ
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have hg := (fd_coef hp).2.2.2.1
  have hq : fd_q α β δ ψ γ ρ = -(fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ := rfl
  unfold fd_mult fd_y fd_l fd_G fd_c
  simp only [Finset.sum_range_one, fd_k, mul_zero, zero_add, pow_zero, mul_one, zero_sub]
  rw [hq]
  rcases eq_or_ne (fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ) 0 with h | h
  · have h' : fd_D α β δ ψ γ ρ = fd_p α β δ ψ γ * fd_g α β δ γ := by linarith
    rw [h, mul_zero, div_zero, h']
    have : 1 + -(fd_p α β δ ψ γ * fd_g α β δ γ) / (fd_p α β δ ψ γ * fd_g α β δ γ) = 0 := by
      rw [← h']; field_simp; ring
    rw [this, mul_zero, div_zero]
  · have e : 1 + -(fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ =
        (fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ := by
      field_simp; ring
    rw [e, div_eq_div_iff (by positivity) (mul_ne_zero hpa.ne' h)]
    field_simp

/-- **The impact multiplier is between zero and one** (AKMM, §8.6.2, p. 231): for `0 ≤ ρ` and
`(1+κ)ρ ≤ 1`, `0 < Δy₀/ΔG₀ < 1`. -/
theorem fd_impact_mult_mem {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) :
    0 < fd_mult α β δ ψ γ ρ 1 ∧ fd_mult α β δ ψ γ ρ 1 < 1 := by
  have hρ1 : ρ ≤ 1 := by nlinarith [(fd_coef hp).2.2.2.2.1]
  have hp0 := (fd_rel hp hρ1).2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, hDp⟩ := fd_q_phi hp hρ0 hρ
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have ha1 : 0 < 1 - α := by linarith [hp.2.1]
  have hY : 0 < fd_Y α β δ := by linarith [(fd_coef hp).2.1, hp.2.2.2.2.1]
  have hpos : 0 < fd_mult α β δ ψ γ ρ 1 := by rw [fd_impact_mult hp hρ1]; positivity
  refine ⟨hpos, ?_⟩
  have hG : 0 < ∑ t ∈ range 1, fd_g α β δ γ * fd_G α β δ ψ γ ρ t := by
    obtain ⟨-, -, -, -, -, -, hD, -, -, -⟩ := fd_rel hp hρ1
    have hg := (fd_coef hp).2.2.2.1
    have hq : fd_q α β δ ψ γ ρ = -(fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ := rfl
    simp only [Finset.sum_range_one, fd_G, fd_c, fd_k, mul_zero, zero_add, pow_zero, mul_one]
    have : 1 + fd_q α β δ ψ γ ρ =
        (fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ := by
      rw [hq]; field_simp; ring
    rw [this]
    positivity
  exact fd_mult_lt_one hp hρ0 hρ (le_refl 1) hG

/-- **The impact multiplier increases with the persistence of the shock** (AKMM, §8.6.2,
p. 231, "the fiscal multiplier is increasing in the persistence of the shock to spending";
Figure 8.4, right): `ρ ↦ Δy₀/ΔG₀` is strictly increasing on `0 ≤ ρ ≤ 1/(1+κ)`. -/
theorem fd_impact_mult_strictMonoOn_rho {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    StrictMonoOn (fun ρ => fd_mult α β δ ψ γ ρ 1) {ρ | 0 ≤ ρ ∧ (1 + fd_kap α β δ ψ) * ρ ≤ 1} := by
  intro ρ1 h1 ρ2 h2 h12
  have hκ := (fd_coef hp).2.2.2.2.1
  have hr1 : ρ1 ≤ 1 := by nlinarith [h1.1, h1.2]
  have hr2 : ρ2 ≤ 1 := by nlinarith [h2.1, h2.2]
  simp only
  rw [fd_impact_mult hp hr1, fd_impact_mult hp hr2]
  have hp0 := (fd_rel hp hr1).2.2.2.2.2.2.2.2.2
  have hD1 := (fd_q_phi hp h1.1 h1.2).2.2.2
  have hD2 := (fd_q_phi hp h2.1 h2.2).2.2.2
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have ha1 : 0 < 1 - α := by linarith [hp.2.1]
  have hY : 0 < fd_Y α β δ := by linarith [(fd_coef hp).2.1, hp.2.2.2.2.1]
  have hl0 := (fd_lam_props hp).1
  have hDD : fd_D α β δ ψ γ ρ2 < fd_D α β δ ψ γ ρ1 := by
    unfold fd_D
    have : 0 < fd_lam α β δ ψ γ * (1 + fd_kap α β δ ψ) := by positivity
    nlinarith
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  exact mul_lt_mul_of_pos_left (by linarith) hpa

/-! ### The cumulative multiplier over the whole horizon -/

/-- `Σₜ k̂ₜ = −φ/((1−λ)(1−ρ))`, the cumulative capital response over the whole horizon. -/
noncomputable def fd_KInf (α β δ ψ γ ρ : ℝ) : ℝ :=
  -fd_phi α β δ ψ γ ρ / ((1 - fd_lam α β δ ψ γ) * (1 - ρ))

/-- `Σₜ ŷₜ = A₁Σₜk̂ₜ + A₂Σₜρᵗ` with `A₁ = (α(1+ψ) − (1−α)p)/(ψ+α)`, `A₂ = −(1−α)q/(ψ+α)`. -/
noncomputable def fd_yInf (α β δ ψ γ ρ : ℝ) : ℝ :=
  (α * (1 + ψ) - (1 - α) * fd_p α β δ ψ γ) / (ψ + α) * fd_KInf α β δ ψ γ ρ -
    (1 - α) * fd_q α β δ ψ γ ρ / (ψ + α) * (1 / (1 - ρ))

/-- `Σₜ Ĝₜ = pΣₜk̂ₜ + (1+q)Σₜρᵗ`. -/
noncomputable def fd_GInf (α β δ ψ γ ρ : ℝ) : ℝ :=
  fd_p α β δ ψ γ * fd_KInf α β δ ψ γ ρ + (1 + fd_q α β δ ψ γ ρ) * (1 / (1 - ρ))

/-- **The cumulative multiplier over the whole horizon**, `Σₜ Δyₜ / Σₜ ΔGₜ`. -/
noncomputable def fd_multInf (α β δ ψ γ ρ : ℝ) : ℝ :=
  fd_Y α β δ * fd_yInf α β δ ψ γ ρ / (fd_g α β δ γ * fd_GInf α β δ ψ γ ρ)

/-- The capital response dies out: for `0 ≤ ρ < 1`, `k̂ₜ → 0`. -/
theorem fd_k_tendsto {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    Tendsto (fd_k α β δ ψ γ ρ) atTop (𝓝 0) := by
  have hl0 := (fd_lam_props hp).1
  have hl1 := fd_lam_lt_one hp
  set lam := fd_lam α β δ ψ γ
  set φ := fd_phi α β δ ψ γ ρ
  set ν := (1 + max lam ρ) / 2 with hν
  have hmx : max lam ρ < 1 := max_lt hl1 hρ
  have hνl : lam < ν := by have := le_max_left lam ρ; rw [hν]; linarith
  have hνρ : ρ ≤ ν := by have := le_max_right lam ρ; rw [hν]; linarith
  have hν1 : ν < 1 := by rw [hν]; linarith
  have hν0 : 0 ≤ ν := by linarith
  have hνl' : 0 ≤ ν - lam := by linarith
  have hb : ∀ t : ℕ, |fd_k α β δ ψ γ ρ t| ≤ |φ| / (ν - lam) * ν ^ t := by
    intro t
    induction t with
    | zero => simp only [fd_k, abs_zero, pow_zero, mul_one]; exact div_nonneg (abs_nonneg _) hνl'
    | succ t ih =>
      have hk1 : fd_k α β δ ψ γ ρ (t + 1) = lam * fd_k α β δ ψ γ ρ t - φ * ρ ^ t := rfl
      rw [hk1]
      have h1 : |lam * fd_k α β δ ψ γ ρ t - φ * ρ ^ t| ≤
          lam * |fd_k α β δ ψ γ ρ t| + |φ| * ρ ^ t := by
        have := abs_sub (lam * fd_k α β δ ψ γ ρ t) (φ * ρ ^ t)
        rwa [abs_mul, abs_mul, abs_of_pos hl0, abs_of_nonneg (pow_nonneg hρ0 t)] at this
      have h2 : ρ ^ t ≤ ν ^ t := pow_le_pow_left₀ hρ0 hνρ t
      have h3 : lam * |fd_k α β δ ψ γ ρ t| ≤ lam * (|φ| / (ν - lam) * ν ^ t) :=
        mul_le_mul_of_nonneg_left ih hl0.le
      have h4 : |φ| * ρ ^ t ≤ |φ| * ν ^ t := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      have h5 : lam * (|φ| / (ν - lam) * ν ^ t) + |φ| * ν ^ t = |φ| / (ν - lam) * ν ^ (t + 1) := by
        have : ν - lam ≠ 0 := by linarith
        field_simp; ring
      linarith
  have hlim : Tendsto (fun t => |φ| / (ν - lam) * ν ^ t) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hν0 hν1).const_mul (|φ| / (ν - lam))
    rwa [mul_zero] at this
  exact squeeze_zero_norm (fun t => by rw [Real.norm_eq_abs]; exact hb t) hlim

/-- `(1 − λ)Σₜ<H k̂ₜ = −φΣₜ<H ρᵗ − k̂_H`. -/
theorem fd_sum_k {α β δ ψ γ ρ : ℝ} (H : ℕ) :
    (1 - fd_lam α β δ ψ γ) * ∑ t ∈ range H, fd_k α β δ ψ γ ρ t =
      -fd_phi α β δ ψ γ ρ * ∑ t ∈ range H, ρ ^ t - fd_k α β δ ψ γ ρ H := by
  induction H with
  | zero => simp [fd_k]
  | succ H ih =>
    have hk1 : fd_k α β δ ψ γ ρ (H + 1) =
        fd_lam α β δ ψ γ * fd_k α β δ ψ γ ρ H - fd_phi α β δ ψ γ ρ * ρ ^ H := rfl
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hk1]
    linear_combination ih

/-- **The cumulative multiplier converges as the horizon grows** (AKMM, p. 236): for
`0 ≤ ρ < 1` and `Σₜ Ĝₜ ≠ 0`, `Σₜ<H Δyₜ / Σₜ<H ΔGₜ → fd_multInf` as `H → ∞`. -/
theorem fd_mult_tendsto {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hG : fd_GInf α β δ ψ γ ρ ≠ 0) :
    Tendsto (fun H => fd_mult α β δ ψ γ ρ H) atTop (𝓝 (fd_multInf α β δ ψ γ ρ)) := by
  have hl1 := fd_lam_lt_one hp
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have hg := (fd_coef hp).2.2.2.1
  have hR : Tendsto (fun H => ∑ t ∈ range H, ρ ^ t) atTop (𝓝 (1 / (1 - ρ))) := by
    have := (hasSum_geometric_of_lt_one hρ0 hρ).tendsto_sum_nat
    rwa [one_div]
  have hK : Tendsto (fun H => ∑ t ∈ range H, fd_k α β δ ψ γ ρ t) atTop
      (𝓝 (fd_KInf α β δ ψ γ ρ)) := by
    have h1 : 1 - fd_lam α β δ ψ γ ≠ 0 := by linarith
    have e : ∀ H, ∑ t ∈ range H, fd_k α β δ ψ γ ρ t =
        (-fd_phi α β δ ψ γ ρ * ∑ t ∈ range H, ρ ^ t - fd_k α β δ ψ γ ρ H) /
          (1 - fd_lam α β δ ψ γ) :=
      fun H => by rw [eq_div_iff h1, mul_comm, fd_sum_k]
    simp_rw [e]
    have hlim := ((hR.const_mul (-fd_phi α β δ ψ γ ρ)).sub
      (fd_k_tendsto hp hρ0 hρ)).div_const (1 - fd_lam α β δ ψ γ)
    have hv : (-fd_phi α β δ ψ γ ρ * (1 / (1 - ρ)) - 0) / (1 - fd_lam α β δ ψ γ) =
        fd_KInf α β δ ψ γ ρ := by
      unfold fd_KInf
      have : 1 - ρ ≠ 0 := by linarith
      field_simp
      ring
    rwa [hv] at hlim
  have hy : ∀ H, ∑ t ∈ range H, fd_Y α β δ * fd_y α β δ ψ γ ρ t = fd_Y α β δ *
      ((α * (1 + ψ) - (1 - α) * fd_p α β δ ψ γ) / (ψ + α) * ∑ t ∈ range H, fd_k α β δ ψ γ ρ t -
        (1 - α) * fd_q α β δ ψ γ ρ / (ψ + α) * ∑ t ∈ range H, ρ ^ t) := fun H => by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold fd_y fd_l fd_c
    field_simp
    ring
  have hGs : ∀ H, ∑ t ∈ range H, fd_g α β δ γ * fd_G α β δ ψ γ ρ t = fd_g α β δ γ *
      (fd_p α β δ ψ γ * ∑ t ∈ range H, fd_k α β δ ψ γ ρ t +
        (1 + fd_q α β δ ψ γ ρ) * ∑ t ∈ range H, ρ ^ t) := fun H => by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold fd_G fd_c
    ring
  unfold fd_mult fd_multInf fd_yInf fd_GInf
  simp_rw [hy, hGs]
  refine Tendsto.div (tendsto_const_nhds.mul ((hK.const_mul _).sub (hR.const_mul _)))
    (tendsto_const_nhds.mul ((hK.const_mul _).add (hR.const_mul _))) ?_
  exact mul_ne_zero hg.ne' hG

/-- The numerator `N(ρ) = (1−α)p(1−λ) − A₀λ(1 − (1+κ)ρ)`, `A₀ = α(1+ψ) − (1−α)p`, of the
whole-horizon multiplier; affine in `ρ`. -/
noncomputable def fd_N (α β δ ψ γ ρ : ℝ) : ℝ :=
  (1 - α) * fd_p α β δ ψ γ * (1 - fd_lam α β δ ψ γ) -
    (α * (1 + ψ) - (1 - α) * fd_p α β δ ψ γ) * fd_lam α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * ρ)

/-- The denominator `Q(ρ) = (D(ρ) − pg)(1−λ) − pgλ(1 − (1+κ)ρ)` of the whole-horizon
multiplier; affine in `ρ`. -/
noncomputable def fd_Q (α β δ ψ γ ρ : ℝ) : ℝ :=
  (fd_D α β δ ψ γ ρ - fd_p α β δ ψ γ * fd_g α β δ γ) * (1 - fd_lam α β δ ψ γ) -
    fd_p α β δ ψ γ * fd_g α β δ γ * fd_lam α β δ ψ γ * (1 - (1 + fd_kap α β δ ψ) * ρ)

/-- The closed forms: for `ρ < 1`, `Σₜ Ĝₜ = Q(ρ)/(D(1−λ)(1−ρ))` and
`Σₜ ŷₜ = gN(ρ)/((ψ+α)D(1−λ)(1−ρ))`. -/
theorem fd_inf_closed {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ : ρ < 1) :
    fd_GInf α β δ ψ γ ρ = fd_Q α β δ ψ γ ρ /
        (fd_D α β δ ψ γ ρ * (1 - fd_lam α β δ ψ γ) * (1 - ρ)) ∧
      fd_yInf α β δ ψ γ ρ = fd_g α β δ γ * fd_N α β δ ψ γ ρ /
        ((ψ + α) * fd_D α β δ ψ γ ρ * (1 - fd_lam α β δ ψ γ) * (1 - ρ)) := by
  obtain ⟨-, -, -, -, -, -, hD, -, R8, -⟩ := fd_rel hp hρ.le
  have hl1 := fd_lam_lt_one hp
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have h1 : 1 - fd_lam α β δ ψ γ ≠ 0 := by linarith
  have h2 : 1 - ρ ≠ 0 := by linarith
  have hφ : fd_phi α β δ ψ γ ρ = fd_g α β δ γ * fd_lam α β δ ψ γ *
      (1 - (1 + fd_kap α β δ ψ) * ρ) / fd_D α β δ ψ γ ρ := by
    rw [eq_div_iff hD.ne']; exact R8
  have hq : fd_q α β δ ψ γ ρ = -(fd_p α β δ ψ γ * fd_g α β δ γ) / fd_D α β δ ψ γ ρ := rfl
  constructor
  · unfold fd_GInf fd_KInf fd_Q
    rw [hφ, hq]
    field_simp
    ring
  · unfold fd_yInf fd_KInf fd_N
    rw [hφ, hq]
    field_simp
    ring

/-- The identity behind the monotonicity: `α(1+ψ)(n − g) − (1−α)(m − 1) = α(1+ψ)c̄/k̄ + (1−α)δ`. -/
theorem fd_key {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    α * (1 + ψ) * (fd_n α β δ ψ γ - fd_g α β δ γ) - (1 - α) * (fd_m α β δ ψ - 1) =
      α * (1 + ψ) * fd_C α β δ γ + (1 - α) * δ := by
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have ha := hp.1
  unfold fd_n fd_g fd_m fd_Y
  field_simp
  ring

/-- The cross difference of the affine maps `N` and `Q`:
`N(ρ₂)Q(ρ₁) − N(ρ₁)Q(ρ₂) = (ρ₂ − ρ₁)(1+κ)λ(1−λ)p(α(1+ψ)c̄/k̄ + (1−α)δ)`. -/
theorem fd_det {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) (ρ₁ ρ₂ : ℝ) :
    fd_N α β δ ψ γ ρ₂ * fd_Q α β δ ψ γ ρ₁ - fd_N α β δ ψ γ ρ₁ * fd_Q α β δ ψ γ ρ₂ =
      (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ * (1 - fd_lam α β δ ψ γ) *
        fd_p α β δ ψ γ * (α * (1 + ψ) * fd_C α β δ γ + (1 - α) * δ) := by
  have R5 := (fd_rel (ρ := 0) hp zero_le_one).2.2.2.2.1
  have key := fd_key hp
  unfold fd_N fd_Q fd_D
  linear_combination (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ *
    (1 - fd_lam α β δ ψ γ) * (-(α * (1 + ψ))) * R5 + (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) *
    fd_lam α β δ ψ γ * (1 - fd_lam α β δ ψ γ) * fd_p α β δ ψ γ * key

/-- **The whole-horizon cumulative multiplier increases with persistence** (AKMM, §8.6.2,
p. 231; Figure 8.4, right, p. 236: "as `ρ_η` increases … a larger multiplier"). Let
`0 ≤ ρ₁ < ρ₂ ≤ 1/(1+κ)` and suppose cumulative spending rises at `ρ₁`, `Σₜ Ĝₜ > 0`. Then it rises
at `ρ₂` too, and `Σₜ Δyₜ/Σₜ ΔGₜ` is strictly larger at `ρ₂`. Both `N` and `Q` are affine in `ρ`,
and `N(ρ₂)Q(ρ₁) − N(ρ₁)Q(ρ₂) = (ρ₂ − ρ₁)(1+κ)λ(1−λ)p(α(1+ψ)c̄/k̄ + (1−α)δ) > 0`. -/
theorem fd_multInf_strictMono {α β δ ψ γ ρ₁ ρ₂ : ℝ} (hp : fm_Params α β δ ψ γ) (h0 : 0 ≤ ρ₁)
    (h12 : ρ₁ < ρ₂) (h2 : (1 + fd_kap α β δ ψ) * ρ₂ ≤ 1) (hG : 0 < fd_GInf α β δ ψ γ ρ₁) :
    0 < fd_GInf α β δ ψ γ ρ₂ ∧ fd_multInf α β δ ψ γ ρ₁ < fd_multInf α β δ ψ γ ρ₂ := by
  have hκ := (fd_coef hp).2.2.2.2.1
  have hr2 : ρ₂ < 1 := by nlinarith
  have hr1 : ρ₁ < 1 := by linarith
  obtain ⟨-, -, -, -, R5, -, hD1, -, -, hp0⟩ := fd_rel hp hr1.le
  have hD2 := (fd_rel hp hr2.le).2.2.2.2.2.2.1
  obtain ⟨-, -, -, hg, -, -, hgn, -, -⟩ := fd_coef hp
  have hl0 := (fd_lam_props hp).1
  have hl1 := fd_lam_lt_one hp
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have hY : 0 < fd_Y α β δ := by linarith [(fd_coef hp).2.1, hp.2.2.2.2.1]
  have hC := (fd_coef hp).2.2.1
  have hd := hp.2.2.2.2.1
  have ha0 := hp.1
  have ha1 : 0 < 1 - α := by linarith [hp.2.1]
  obtain ⟨hG1, -⟩ := fd_inf_closed hp hr1
  obtain ⟨hG2, -⟩ := fd_inf_closed hp hr2
  have hpos1 : 0 < fd_D α β δ ψ γ ρ₁ * (1 - fd_lam α β δ ψ γ) * (1 - ρ₁) := by
    have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
    have : 0 < 1 - ρ₁ := by linarith
    positivity
  have hpos2 : 0 < fd_D α β δ ψ γ ρ₂ * (1 - fd_lam α β δ ψ γ) * (1 - ρ₂) := by
    have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
    have : 0 < 1 - ρ₂ := by linarith
    positivity
  have hQ1 : 0 < fd_Q α β δ ψ γ ρ₁ := by
    rw [hG1] at hG; exact (div_pos_iff_of_pos_right hpos1).1 hG
  -- `Q` is affine and positive at `1/(1+κ)`
  have hmlpg : 0 < fd_m α β δ ψ - fd_lam α β δ ψ γ - fd_p α β δ ψ γ * fd_g α β δ γ := by
    nlinarith [mul_pos hp0 (sub_pos.2 hgn)]
  have hQaff : (1 - (1 + fd_kap α β δ ψ) * ρ₁) * fd_Q α β δ ψ γ ρ₂ =
      (1 - (1 + fd_kap α β δ ψ) * ρ₂) * fd_Q α β δ ψ γ ρ₁ + (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) *
        (1 - fd_lam α β δ ψ γ) * (fd_m α β δ ψ - fd_lam α β δ ψ γ -
          fd_p α β δ ψ γ * fd_g α β δ γ) := by
    unfold fd_Q fd_D; ring
  have hQ2 : 0 < fd_Q α β δ ψ γ ρ₂ := by
    have e1 : 0 < 1 - (1 + fd_kap α β δ ψ) * ρ₁ := by nlinarith
    have e2 : 0 ≤ (1 - (1 + fd_kap α β δ ψ) * ρ₂) * fd_Q α β δ ψ γ ρ₁ :=
      mul_nonneg (by linarith) hQ1.le
    have e3 : 0 < (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) * (1 - fd_lam α β δ ψ γ) *
        (fd_m α β δ ψ - fd_lam α β δ ψ γ - fd_p α β δ ψ γ * fd_g α β δ γ) := by
      have : 0 < ρ₂ - ρ₁ := by linarith
      have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
      have : 0 < 1 + fd_kap α β δ ψ := by linarith
      positivity
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos e1.le h]
  refine ⟨by rw [hG2]; positivity, ?_⟩
  have hdet := fd_det hp ρ₁ ρ₂
  have hdpos : 0 < (ρ₂ - ρ₁) * (1 + fd_kap α β δ ψ) * fd_lam α β δ ψ γ *
      (1 - fd_lam α β δ ψ γ) * fd_p α β δ ψ γ * (α * (1 + ψ) * fd_C α β δ γ + (1 - α) * δ) := by
    have : 0 < ρ₂ - ρ₁ := by linarith
    have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
    have : 0 < 1 + fd_kap α β δ ψ := by linarith
    have : 0 < α * (1 + ψ) * fd_C α β δ γ + (1 - α) * δ := by
      have : 0 < 1 + ψ := by linarith [hp.2.2.2.2.2.1]
      have := mul_nonneg ha1.le hd
      positivity
    positivity
  have hm : ∀ ρ, ρ < 1 → 0 < fd_Q α β δ ψ γ ρ →
      fd_multInf α β δ ψ γ ρ = fd_Y α β δ * fd_N α β δ ψ γ ρ / ((ψ + α) * fd_Q α β δ ψ γ ρ) := by
    intro ρ hρ hQ
    obtain ⟨e1, e2⟩ := fd_inf_closed hp hρ
    have hDρ := (fd_rel hp hρ.le).2.2.2.2.2.2.1
    have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
    have : 0 < 1 - ρ := by linarith
    unfold fd_multInf
    rw [e1, e2]
    field_simp
  rw [hm ρ₁ hr1 hQ1, hm ρ₂ hr2 hQ2, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hfin := mul_pos (mul_pos hY hpa) (hdet ▸ hdpos)
  linear_combination hfin

/-- The hypothesis of `fd_multInf_strictMono` holds near the top of the range: at
`ρ = 1/(1+κ)`, cumulative spending rises, `Σₜ Ĝₜ > 0` (and `Σₜ Ĝₜ` is affine in `ρ` up to a
positive factor). -/
theorem fd_GInf_pos_top {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) :
    0 < fd_GInf α β δ ψ γ (1 / (1 + fd_kap α β δ ψ)) := by
  have hκ := (fd_coef hp).2.2.2.2.1
  have hr : 1 / (1 + fd_kap α β δ ψ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  obtain ⟨-, -, -, -, R5, -, hD, -, -, hp0⟩ := fd_rel hp hr.le
  obtain ⟨-, -, -, hg, -, -, hgn, -, -⟩ := fd_coef hp
  have hl1 := fd_lam_lt_one hp
  rw [(fd_inf_closed hp hr).1]
  have : 0 < 1 - 1 / (1 + fd_kap α β δ ψ) := by linarith
  have : 0 < 1 - fd_lam α β δ ψ γ := by linarith
  have hQ : fd_Q α β δ ψ γ (1 / (1 + fd_kap α β δ ψ)) = (1 - fd_lam α β δ ψ γ) *
      (fd_p α β δ ψ γ * (fd_n α β δ ψ γ - fd_g α β δ γ)) := by
    unfold fd_Q fd_D
    have : (1 + fd_kap α β δ ψ) * (1 / (1 + fd_kap α β δ ψ)) = 1 := by field_simp
    linear_combination -(1 - fd_lam α β δ ψ γ) * R5 -
      fd_lam α β δ ψ γ * (1 - fd_lam α β δ ψ γ - fd_p α β δ ψ γ * fd_g α β δ γ) * this
  rw [hQ]
  have : 0 < fd_p α β δ ψ γ * (fd_n α β δ ψ γ - fd_g α β δ γ) := mul_pos hp0 (by linarith)
  positivity

/-! ### The multiplier and the labour supply elasticity -/

/-- **The characteristic polynomial is a pencil in `ψ`**: with `θ = r̄(1−α)`,
`(ψ+α)[(m − x)(1 − (1+κ)x) − nκψx] = ψf₀(x) + αf₁(x)`, where
`f₀(x) = (1/β − x)(1 − x) − βθ(ȳ/k̄ − δ)x` (inelastic labour, `ψ → ∞`) and
`f₁(x) = (1/β + θ/α − x)(1 − (1 + βθ/α)x)` (`ψ = 0`) do not depend on `ψ`. -/
theorem fd_pencil {α β δ ψ γ : ℝ} (hp : fm_Params α β δ ψ γ) (x : ℝ) :
    (ψ + α) * ((fd_m α β δ ψ - x) * (1 - (1 + fd_kap α β δ ψ) * x) -
      fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ) * x) =
      ψ * ((1 / β - x) * (1 - x) - β * (fm_r β δ * (1 - α)) * (fd_Y α β δ - δ) * x) +
        α * ((1 / β + fm_r β δ * (1 - α) / α - x) *
          (1 - (1 + β * (fm_r β δ * (1 - α)) / α) * x)) := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ, hγ⟩ := hp
  have hpa : 0 < ψ + α := by linarith
  unfold fd_m fd_kap fd_n fd_C fd_Y fm_r
  field_simp
  ring

/-- Below the stable root: if `0 ≤ x ≤ 1` and `(m − x)(1 − (1+κ)x) − nκψx ≥ 0`, then `x ≤ λ`. -/
theorem fd_le_lam {α β δ ψ γ x : ℝ} (hp : fm_Params α β δ ψ γ) (hx : x ≤ 1)
    (hF : 0 ≤ (fd_m α β δ ψ - x) * (1 - (1 + fd_kap α β δ ψ) * x) -
      fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ) * x) : x ≤ fd_lam α β δ ψ γ := by
  obtain ⟨hl0, -, hchar⟩ := fd_lam_props hp
  have hl1 := fd_lam_lt_one hp
  obtain ⟨-, -, -, hg, hκ, hm, hgn, -, -⟩ := fd_coef hp
  have hψ := hp.2.2.2.2.2.1
  have hw : 0 < fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ) := by
    have : 0 < fd_n α β δ ψ γ := by linarith
    positivity
  set a := 1 + fd_kap α β δ ψ
  set m := fd_m α β δ ψ
  set w := fd_n α β δ ψ γ * (fd_kap α β δ ψ * ψ)
  set lam := fd_lam α β δ ψ γ
  -- `F(1) < 0` places `1` between the roots
  have h1 : (1 - lam) * (a * (1 + lam) - (a * m + 1 + w)) < 0 := by nlinarith
  have h2 : a * (1 + lam) - (a * m + 1 + w) < 0 := by
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam) h]
  by_contra hlt
  rw [not_le] at hlt
  have : (m - x) * (1 - a * x) - w * x = (x - lam) * (a * (x + lam) - (a * m + 1 + w)) := by
    linear_combination hchar
  have h3 : a * (x + lam) - (a * m + 1 + w) < 0 := by nlinarith
  nlinarith [mul_neg_of_pos_of_neg (by linarith : 0 < x - lam) h3]

/-- `f₀ ≥ 0` on `[0, 1/(1 + βθ/α)]` (for `δ ≤ 1`), where
`f₀(x) = (1/β − x)(1 − x) − βθ(ȳ/k̄ − δ)x` and `θ = r̄(1−α)`. At `x₁ = α/(α + βθ)`,
`(α + βθ)²f₀(x₁) = θβ(1−α)(1−δ)(1 − β(1 − δ + αδ)) ≥ 0`; `f₀(1) < 0` and convexity do the rest. -/
theorem fd_f0_nonneg {α β δ ψ γ x : ℝ} (hp : fm_Params α β δ ψ γ) (hδ : δ ≤ 1)
    (hx : x * (α + β * (fm_r β δ * (1 - α))) ≤ α) :
    0 ≤ (1 / β - x) * (1 - x) - β * (fm_r β δ * (1 - α)) * (fd_Y α β δ - δ) * x := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩ := hp
  obtain ⟨hr0, hY, -, -, -, -, -, -, hbr⟩ := fd_coef ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩
  set r := fm_r β δ
  set θ := r * (1 - α)
  have hθ : 0 < θ := by have : 0 < 1 - α := by linarith
                        positivity
  have hb1' : 1 < 1 / β := by rw [lt_div_iff₀ hb0]; linarith
  set f0 : ℝ → ℝ := fun x => (1 / β - x) * (1 - x) - β * θ * (fd_Y α β δ - δ) * x
  change 0 ≤ f0 x
  have hden : 0 < α + β * θ := by positivity
  set x1 := α / (α + β * θ) with hx1def
  have hlx : x ≤ x1 := by rw [hx1def, le_div_iff₀ hden]; exact hx
  have hx1lt : x1 < 1 := by
    rw [hx1def, div_lt_one hden]
    have : 0 < β * θ := by positivity
    linarith
  have hfx1 : 0 ≤ f0 x1 := by
    have e : f0 x1 = θ * β * (1 - α) * (1 - δ) * (1 - β * (1 - δ + α * δ)) /
        (α + β * θ) ^ 2 := by
      have hYr : fd_Y α β δ = r / α := rfl
      have hE : α + β * θ - α * β - β * (r - α * δ) * (α + β * θ) =
          β * (1 - α) * (1 - δ) * (1 - β * (1 - δ + α * δ)) := by
        simp only [θ]
        linear_combination (1 - α - α - (β * r + (1 - β + β * δ)) * (1 - α) +
          α * β * δ * (1 - α)) * hbr
      have hf : f0 x1 = θ * (α + β * θ - α * β - β * (r - α * δ) * (α + β * θ)) /
          (α + β * θ) ^ 2 := by
        simp only [f0, hx1def]
        rw [hYr]
        field_simp
        ring
      rw [hf, hE]
      ring
    rw [e]
    have : 0 ≤ 1 - β * (1 - δ + α * δ) := by
      have : 1 - δ + α * δ ≤ 1 := by nlinarith
      have : β * (1 - δ + α * δ) ≤ β * 1 := by
        apply mul_le_mul_of_nonneg_left this hb0.le
      linarith
    have : 0 ≤ 1 - δ := by linarith
    have : 0 < 1 - α := by linarith
    positivity
  have hf01 : f0 1 < 0 := by
    have e : f0 1 = -(β * θ * (fd_Y α β δ - δ)) := by simp only [f0]; ring
    have : 0 < β * θ * (fd_Y α β δ - δ) := by
      have : 0 < fd_Y α β δ - δ := by linarith
      positivity
    linarith
  -- convexity of `f₀`
  have hb : 1 + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ)) < 0 := by
    have e1 : f0 1 - f0 x1 = (1 - x1) * (1 + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))) := by
      simp only [f0]; ring
    have : (1 - x1) * (1 + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))) < 0 := by linarith
    by_contra h
    rw [not_lt] at h
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x1) h
    linarith
  have e2 : f0 x - f0 x1 = (x - x1) * (x + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))) := by
    simp only [f0]; ring
  have h4 := mul_nonneg (by linarith : (0 : ℝ) ≤ x1 - x)
    (by linarith : (0 : ℝ) ≤ -(x + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))))
  have h5 : (x - x1) * (x + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))) =
      (x1 - x) * -(x + x1 - (1 + 1 / β + β * θ * (fd_Y α β δ - δ))) := by ring
  linarith

/-- **The stable root rises with `ψ`** (for `δ ≤ 1`): a less elastic labour supply makes capital
adjust more slowly. The proof uses the pencil `fd_pencil`: `f₀` is nonnegative at `λ(ψ₁)`, so
the characteristic polynomial for `ψ₂ > ψ₁` is nonnegative at `λ(ψ₁)`. The assumption `δ ≤ 1`
gives `f₀(1/(1 + βθ/α)) ≥ 0`. -/
theorem fd_lam_mono_psi {α β δ ψ₁ ψ₂ γ : ℝ} (hp : fm_Params α β δ ψ₁ γ) (hψ : ψ₁ ≤ ψ₂)
    (hδ : δ ≤ 1) : fd_lam α β δ ψ₁ γ ≤ fd_lam α β δ ψ₂ γ := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩ := hp
  have hp2 : fm_Params α β δ ψ₂ γ := ⟨ha0, ha1, hb0, hb1, hd, by linarith, hγ⟩
  have hp1 : fm_Params α β δ ψ₁ γ := ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩
  obtain ⟨hl0, -, hchar⟩ := fd_lam_props hp1
  have hl1 := fd_lam_lt_one hp1
  obtain ⟨hr0, hY, -, -, -, -, -, -, hbr⟩ := fd_coef hp1
  set lam := fd_lam α β δ ψ₁ γ
  set r := fm_r β δ
  set θ := r * (1 - α)
  have hθ : 0 < θ := by have : 0 < 1 - α := by linarith
                        positivity
  set f0 : ℝ → ℝ := fun x => (1 / β - x) * (1 - x) - β * θ * (fd_Y α β δ - δ) * x
  set f1 : ℝ → ℝ := fun x => (1 / β + θ / α - x) * (1 - (1 + β * θ / α) * x)
  have hpen1 := fd_pencil hp1 lam
  have hpen2 := fd_pencil hp2 lam
  have hF1 : ψ₁ * f0 lam + α * f1 lam = 0 := by
    simp only [f0, f1]; rw [← hpen1]; rw [hchar]; ring
  -- `f₀(lam) ≥ 0`
  have hb1' : 1 < 1 / β := by rw [lt_div_iff₀ hb0]; linarith
  have hf0 : 0 ≤ f0 lam := by
    by_contra hneg
    rw [not_le] at hneg
    have hf1 : 0 < f1 lam := by nlinarith
    have hm1 : 0 < 1 / β + θ / α - lam := by
      have : 0 < θ / α := div_pos hθ ha0
      linarith
    have hx1 : 0 < 1 - (1 + β * θ / α) * lam := by
      by_contra h
      rw [not_lt] at h
      have := mul_nonpos_of_nonneg_of_nonpos hm1.le h
      simp only [f1] at hf1
      linarith
    have hden : 0 < α + β * θ := by positivity
    have hlx : lam * (α + β * θ) ≤ α := by
      have e : (1 + β * θ / α) * lam = (α + β * θ) * lam / α := by field_simp
      rw [e] at hx1
      have : (α + β * θ) * lam / α < 1 := by linarith
      rw [div_lt_one ha0] at this
      linarith
    exact absurd (fd_f0_nonneg hp1 hδ hlx) (not_le.2 hneg)
  -- the characteristic polynomial at `ψ₂` is nonnegative at `lam`
  have hpa2 : 0 < ψ₂ + α := by linarith
  apply fd_le_lam hp2 hl1.le
  have : (ψ₂ + α) * ((fd_m α β δ ψ₂ - lam) * (1 - (1 + fd_kap α β δ ψ₂) * lam) -
      fd_n α β δ ψ₂ γ * (fd_kap α β δ ψ₂ * ψ₂) * lam) = (ψ₂ - ψ₁) * f0 lam := by
    rw [hpen2]; simp only [f0, f1] at hF1 ⊢; linear_combination hF1
  have h2 : 0 ≤ (ψ₂ + α) * ((fd_m α β δ ψ₂ - lam) * (1 - (1 + fd_kap α β δ ψ₂) * lam) -
      fd_n α β δ ψ₂ γ * (fd_kap α β δ ψ₂ * ψ₂) * lam) := by
    rw [this]; exact mul_nonneg (by linarith) hf0
  exact (mul_nonneg_iff_of_pos_left hpa2).1 h2

/-- The impact multiplier as `(ȳ/k̄)(1−α)/Φ` with
`Φ = (ȳ/k̄)(1−α) + (ψ+α)c̄/k̄ + (1 − (1+κ)ρ)·(ψ+α)n·λ/(m − λ)`, for `0 ≤ ρ ≤ 1/(1+κ)`. -/
theorem fd_impact_mult_Phi {α β δ ψ γ ρ : ℝ} (hp : fm_Params α β δ ψ γ) (hρ0 : 0 ≤ ρ)
    (hρ : (1 + fd_kap α β δ ψ) * ρ ≤ 1) :
    fd_mult α β δ ψ γ ρ 1 = fd_Y α β δ * (1 - α) /
      (fd_Y α β δ * (1 - α) + (ψ + α) * fd_C α β δ γ + (1 - (1 + fd_kap α β δ ψ) * ρ) *
        ((ψ + α) * fd_n α β δ ψ γ) * (fd_lam α β δ ψ γ / (fd_m α β δ ψ - fd_lam α β δ ψ γ))) := by
  have hρ1 : ρ ≤ 1 := by nlinarith [(fd_coef hp).2.2.2.2.1]
  obtain ⟨-, R2, -, -, R5, -, -, -, -, hp0⟩ := fd_rel hp hρ1
  obtain ⟨hl0, hl1, -⟩ := fd_lam_props hp
  obtain ⟨-, hY, hC, hg, hκ, hm, hgn, -, -⟩ := fd_coef hp
  have hlm : 0 < fd_m α β δ ψ - fd_lam α β δ ψ γ := by nlinarith
  have hn : 0 < fd_n α β δ ψ γ := by linarith
  have hpa : 0 < ψ + α := by linarith [hp.1, hp.2.2.2.2.2.1]
  have ha1 : 0 < 1 - α := by linarith [hp.2.1]
  have hY0 : 0 < fd_Y α β δ := by linarith [hp.2.2.2.2.1]
  have hDp := (fd_q_phi hp hρ0 hρ).2.2.2
  have R3 : fd_g α β δ γ = γ * fd_C α β δ γ := rfl
  have hτ : 0 ≤ 1 - (1 + fd_kap α β δ ψ) * ρ := by linarith
  have hΦ : 0 < fd_Y α β δ * (1 - α) + (ψ + α) * fd_C α β δ γ + (1 - (1 + fd_kap α β δ ψ) * ρ) *
      ((ψ + α) * fd_n α β δ ψ γ) * (fd_lam α β δ ψ γ / (fd_m α β δ ψ - fd_lam α β δ ψ γ)) := by
    have : 0 ≤ (1 - (1 + fd_kap α β δ ψ) * ρ) * ((ψ + α) * fd_n α β δ ψ γ) *
        (fd_lam α β δ ψ γ / (fd_m α β δ ψ - fd_lam α β δ ψ γ)) := by positivity
    have : 0 < fd_Y α β δ * (1 - α) + (ψ + α) * fd_C α β δ γ := by positivity
    linarith
  rw [fd_impact_mult hp hρ1, div_eq_div_iff (by positivity) hΦ.ne']
  have hp' : fd_p α β δ ψ γ = (fd_m α β δ ψ - fd_lam α β δ ψ γ) / fd_n α β δ ψ γ := rfl
  unfold fd_D
  rw [hp']
  field_simp
  linear_combination -(fd_m α β δ ψ - fd_lam α β δ ψ γ) * R2 +
    (fd_m α β δ ψ - fd_lam α β δ ψ γ) * (ψ + α) * R3

/-- **The impact multiplier is larger when labour supply is more elastic** (AKMM, Figure 8.4,
right, p. 236: "if `ψ` is smaller, so labor supply is more elastic, … the fiscal multiplier is
larger"; §8.8, p. 234). For `δ ≤ 1`, `ψ₁ < ψ₂` and `0 ≤ ρ ≤ 1/(1+κ(ψ₁))`,
`Δy₀/ΔG₀` at `ψ₂` is strictly smaller than at `ψ₁`. In `fd_impact_mult_Phi`, every term of `Φ`
is nondecreasing in `ψ` and `(ψ+α)c̄/k̄` is strictly increasing: `κ` and `m` fall with `ψ` and the
stable root `λ` rises (`fd_lam_mono_psi`). -/
theorem fd_impact_mult_antitone_psi {α β δ ψ₁ ψ₂ γ ρ : ℝ} (hp : fm_Params α β δ ψ₁ γ)
    (hψ : ψ₁ < ψ₂) (hδ : δ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : (1 + fd_kap α β δ ψ₁) * ρ ≤ 1) :
    fd_mult α β δ ψ₂ γ ρ 1 < fd_mult α β δ ψ₁ γ ρ 1 := by
  obtain ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩ := hp
  have hp1 : fm_Params α β δ ψ₁ γ := ⟨ha0, ha1, hb0, hb1, hd, hψ1, hγ⟩
  have hp2 : fm_Params α β δ ψ₂ γ := ⟨ha0, ha1, hb0, hb1, hd, by linarith, hγ⟩
  have hpa1 : 0 < ψ₁ + α := by linarith
  have hpa2 : 0 < ψ₂ + α := by linarith
  obtain ⟨hr0, hY, hC, -, hκ1, hm1, hgn1, -, -⟩ := fd_coef hp1
  have hκ2 := (fd_coef hp2).2.2.2.2.1
  have hgn2 := (fd_coef hp2).2.2.2.2.2.2.1
  have hg := (fd_coef hp1).2.2.2.1
  -- `κ` and `m` fall with `ψ`
  have hκ : fd_kap α β δ ψ₂ ≤ fd_kap α β δ ψ₁ := by
    unfold fd_kap
    apply div_le_div_of_nonneg_left _ hpa1 (by linarith)
    have : 0 < 1 - α := by linarith
    positivity
  have hm : fd_m α β δ ψ₂ ≤ fd_m α β δ ψ₁ := by
    unfold fd_m
    have : fm_r β δ * (1 + ψ₂) / (ψ₂ + α) ≤ fm_r β δ * (1 + ψ₁) / (ψ₁ + α) := by
      rw [div_le_div_iff₀ hpa2 hpa1]
      nlinarith [mul_pos hr0 (by linarith : (0 : ℝ) < 1 - α)]
    linarith
  have hρ2 : (1 + fd_kap α β δ ψ₂) * ρ ≤ 1 := by nlinarith
  rw [fd_impact_mult_Phi hp2 hρ0 hρ2, fd_impact_mult_Phi hp1 hρ0 hρ]
  have hl := fd_lam_mono_psi hp1 hψ.le hδ
  have hl01 := (fd_lam_props hp1).1
  have hl11 := fd_lam_lt_one hp1
  have hl12 := fd_lam_lt_one hp2
  have hlm1 : 0 < fd_m α β δ ψ₁ - fd_lam α β δ ψ₁ γ := by linarith
  have hlm2 : 0 < fd_m α β δ ψ₂ - fd_lam α β δ ψ₂ γ := by
    linarith [(fd_coef hp2).2.2.2.2.2.1]
  have hY0 : 0 < fd_Y α β δ := by linarith
  have ha1' : 0 < 1 - α := by linarith
  -- the four factors
  have hA : fd_Y α β δ * (1 - α) + (ψ₁ + α) * fd_C α β δ γ <
      fd_Y α β δ * (1 - α) + (ψ₂ + α) * fd_C α β δ γ := by nlinarith
  have hB0 : 0 ≤ 1 - (1 + fd_kap α β δ ψ₁) * ρ := by linarith
  have hB : 1 - (1 + fd_kap α β δ ψ₁) * ρ ≤ 1 - (1 + fd_kap α β δ ψ₂) * ρ := by nlinarith
  have hn1 : (ψ₁ + α) * fd_n α β δ ψ₁ γ = fd_Y α β δ * (1 - α) + (ψ₁ + α) * ((1 + γ) *
      fd_C α β δ γ) := (fd_rel (ρ := 0) hp1 zero_le_one).2.1
  have hn2 : (ψ₂ + α) * fd_n α β δ ψ₂ γ = fd_Y α β δ * (1 - α) + (ψ₂ + α) * ((1 + γ) *
      fd_C α β δ γ) := (fd_rel (ρ := 0) hp2 zero_le_one).2.1
  have hCc0 : 0 ≤ (ψ₁ + α) * fd_n α β δ ψ₁ γ := by rw [hn1]; positivity
  have hCc : (ψ₁ + α) * fd_n α β δ ψ₁ γ ≤ (ψ₂ + α) * fd_n α β δ ψ₂ γ := by
    rw [hn1, hn2]
    have : (ψ₁ + α) * ((1 + γ) * fd_C α β δ γ) ≤ (ψ₂ + α) * ((1 + γ) * fd_C α β δ γ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hE0 : 0 ≤ fd_lam α β δ ψ₁ γ / (fd_m α β δ ψ₁ - fd_lam α β δ ψ₁ γ) := by positivity
  have hE : fd_lam α β δ ψ₁ γ / (fd_m α β δ ψ₁ - fd_lam α β δ ψ₁ γ) ≤
      fd_lam α β δ ψ₂ γ / (fd_m α β δ ψ₂ - fd_lam α β δ ψ₂ γ) := by
    rw [div_le_div_iff₀ hlm1 hlm2]
    nlinarith [mul_le_mul hl hm (by linarith [(fd_coef hp2).2.2.2.2.2.1]) (by linarith)]
  have hprod := mul_le_mul (mul_le_mul hB hCc hCc0 (by linarith)) hE hE0
    (mul_nonneg (by linarith) (by linarith))
  have hΦ1 : 0 < fd_Y α β δ * (1 - α) + (ψ₁ + α) * fd_C α β δ γ +
      (1 - (1 + fd_kap α β δ ψ₁) * ρ) * ((ψ₁ + α) * fd_n α β δ ψ₁ γ) *
        (fd_lam α β δ ψ₁ γ / (fd_m α β δ ψ₁ - fd_lam α β δ ψ₁ γ)) := by
    have := mul_nonneg (mul_nonneg hB0 hCc0) hE0
    have : 0 < fd_Y α β δ * (1 - α) + (ψ₁ + α) * fd_C α β δ γ := by positivity
    linarith
  apply div_lt_div_of_pos_left (by positivity) hΦ1
  linarith

/-! ### The linearisation -/

/-- **The static equations are exactly log-linear** (AKMM, (8.10), (8.15) with (8.17), and
(8.18), p. 230): if `y = kᵅℓ^{1−α}`, `w/c = ℓ^ψ` with `w = (1−α)y/ℓ`, and `G = γηc` hold at a
point and at the steady state (`η̄ = 1`), then in log deviations `ŷ = αk̂ + (1−α)ℓ̂`,
`ŷ = ĉ + (1+ψ)ℓ̂` and `Ĝ = η̂ + ĉ`, exactly. -/
theorem fd_static_exact {α ψ γ k ℓ c y G η kb ℓb cb yb Gb : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ)
    (hc : 0 < c) (hη : 0 < η) (hkb : 0 < kb) (hℓb : 0 < ℓb) (hcb : 0 < cb) (hγ : 0 < γ)
    (hy : y = k ^ α * ℓ ^ (1 - α)) (hyb : yb = kb ^ α * ℓb ^ (1 - α))
    (hL : (1 - α) * y / ℓ / c = ℓ ^ ψ) (hLb : (1 - α) * yb / ℓb / cb = ℓb ^ ψ) (ha : α < 1)
    (hG : G = γ * η * c) (hGb : Gb = γ * 1 * cb) :
    Real.log (y / yb) = α * Real.log (k / kb) + (1 - α) * Real.log (ℓ / ℓb) ∧
      Real.log (y / yb) = Real.log (c / cb) + (1 + ψ) * Real.log (ℓ / ℓb) ∧
      Real.log (G / Gb) = Real.log η + Real.log (c / cb) := by
  have hy0 : 0 < y := by rw [hy]; positivity
  have hyb0 : 0 < yb := by rw [hyb]; positivity
  have e1 : y / yb = (k / kb) ^ α * (ℓ / ℓb) ^ (1 - α) := by
    rw [hy, hyb, Real.div_rpow hk.le hkb.le, Real.div_rpow hℓ.le hℓb.le]
    have := Real.rpow_pos_of_pos hkb α
    have := Real.rpow_pos_of_pos hℓb (1 - α)
    field_simp
  have h1a : 0 < 1 - α := by linarith
  -- `(1−α)y = cℓ^{1+ψ}`
  have e2 : y / yb = (c / cb) * (ℓ / ℓb) ^ (1 + ψ) := by
    have h1 : (1 - α) * y = c * ℓ ^ (1 + ψ) := by
      rw [Real.rpow_add hℓ, Real.rpow_one]
      field_simp at hL
      linarith
    have h2 : (1 - α) * yb = cb * ℓb ^ (1 + ψ) := by
      rw [Real.rpow_add hℓb, Real.rpow_one]
      field_simp at hLb
      linarith
    rw [Real.div_rpow hℓ.le hℓb.le]
    have := Real.rpow_pos_of_pos hℓb (1 + ψ)
    have hy' : y = c * ℓ ^ (1 + ψ) / (1 - α) := by rw [← h1]; field_simp
    have hyb' : yb = cb * ℓb ^ (1 + ψ) / (1 - α) := by rw [← h2]; field_simp
    rw [hy', hyb']
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
      Real.log_rpow (by positivity)]
  · rw [e2, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
  · rw [hG, hGb, mul_one]
    have : γ * η * c / (γ * cb) = η * (c / cb) := by field_simp
    rw [this, Real.log_mul hη.ne' (by positivity)]

/-- **The linearised resource constraint** (AKMM, (8.11), p. 229): with the steady state
`ȳ = c̄ + δk̄ + Ḡ`, the map `s ↦ ȳe^{s ŷ} − c̄e^{s ĉ} − k̄e^{s k̂′} + (1−δ)k̄e^{s k̂} − Ḡe^{s Ĝ}`
(the resource constraint along the log deviation `s·(ŷ, ĉ, k̂′, k̂, Ĝ)`) vanishes at `s = 0` and
has derivative `ȳŷ − c̄ĉ − k̄k̂′ + (1−δ)k̄k̂ − ḠĜ` there; dividing by `k̄` gives the resource row
of `fd_IsIRF`. -/
theorem fd_resource_linear {yb cb kb Gb δ dy dc dk' dk dG : ℝ}
    (hs : yb = cb + δ * kb + Gb) :
    (fun s : ℝ => yb * Real.exp (s * dy) - cb * Real.exp (s * dc) - kb * Real.exp (s * dk') +
        (1 - δ) * kb * Real.exp (s * dk) - Gb * Real.exp (s * dG)) 0 = 0 ∧
      HasDerivAt (fun s : ℝ => yb * Real.exp (s * dy) - cb * Real.exp (s * dc) -
        kb * Real.exp (s * dk') + (1 - δ) * kb * Real.exp (s * dk) - Gb * Real.exp (s * dG))
        (yb * dy - cb * dc - kb * dk' + (1 - δ) * kb * dk - Gb * dG) 0 := by
  refine ⟨by simp only [zero_mul, Real.exp_zero, mul_one]; rw [hs]; ring, ?_⟩
  have hE : ∀ d : ℝ, HasDerivAt (fun s : ℝ => Real.exp (s * d)) d 0 := fun d => by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const d).exp
    simpa using this
  have := (((((hE dy).const_mul yb).sub ((hE dc).const_mul cb)).sub
    ((hE dk').const_mul kb)).add ((hE dk).const_mul ((1 - δ) * kb))).sub ((hE dG).const_mul Gb)
  exact this

/-- **The linearised Euler equation** (AKMM, (8.14) with (8.16), p. 230): with
`β(1 + r̄ − δ) = 1`, the map `s ↦ β(1 + r̄e^{s(ŷ′−k̂′)} − δ)e^{s(ĉ−ĉ′)}` (the Euler equation
`1 = β(1 + r′ − δ)c/c′` with `r′ = r̄e^{ŷ′−k̂′}`, along the log deviation) equals `1` at `s = 0`
and has derivative `βr̄(ŷ′ − k̂′) + ĉ − ĉ′` there; setting it to zero gives the Euler row of
`fd_IsIRF`. -/
theorem fd_euler_linear {β δ rb dy' dk' dc dc' : ℝ} (hE : β * (1 + rb - δ) = 1) :
    (fun s : ℝ => β * (1 + rb * Real.exp (s * (dy' - dk')) - δ) * Real.exp (s * (dc - dc'))) 0 =
        1 ∧
      HasDerivAt (fun s : ℝ => β * (1 + rb * Real.exp (s * (dy' - dk')) - δ) *
        Real.exp (s * (dc - dc'))) (β * rb * (dy' - dk') + (dc - dc')) 0 := by
  refine ⟨by simp only [zero_mul, Real.exp_zero, mul_one]; exact hE, ?_⟩
  have hX : ∀ d : ℝ, HasDerivAt (fun s : ℝ => Real.exp (s * d)) d 0 := fun d => by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const d).exp
    simpa using this
  have h1 := ((((hX (dy' - dk')).const_mul rb).const_add 1).sub_const δ).const_mul β
  have h2 := h1.mul (hX (dc - dc'))
  convert h2 using 1
  · simp only [zero_mul, Real.exp_zero, mul_one]
    linear_combination -(dc - dc') * hE

end AKMM.QuantitativeMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Structural estimation of the static model

AKMM, §8.7, (8.19)–(8.20) and the likelihood, pp. 231–232.

* **(8.19)–(8.20)**: for `0 < G < y`, (8.2)–(8.3) hold iff `A = y(1 − G/y)^{1/(1+ψ)}` and
  `η = (G/y)/(γ(1 − G/y))` (`eq_8_19_8_20`); the map `(A, η) ↦ (y, G)` is a bijection of the
  positive quadrant onto `{0 < G < y}` with this inverse (`sl_bijection`).
* **The likelihood**: for discretely distributed independent shocks, the probability of observing
  `(y, G)` is `p_A(A)p_η(η)` at the shocks given by (8.19)–(8.20) (`sl_likelihood_discrete`), and
  the log likelihood of a sample is the sum of the logs (`sl_loglik`).
* **Correction**: for densities, the density of `(y, G)` carries the Jacobian of
  `(y, G) ↦ (A, η)`. Its partial derivatives and determinant
  `(1 − s)^{1/(1+ψ) − 2}/(γy)`, `s = G/y`, are computed (`sl_jacobian`); the determinant depends on
  `ψ` (`sl_jacobian_depends_on_psi`), so the printed `Prob(G, y | ψ, γ) = p_A(A)p_η(η)` is not
  the likelihood of `(y, G)` (the change-of-variables formula itself is not formalised).
* **The implied multiplier** (p. 232): by Miao's invariance theorem, the multiplier
  `(1+γ)/(1+γ+ψ)` at the maximum-likelihood estimate maximises the profile likelihood of the
  multiplier (`sl_multiplier_mle`).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory ProbabilityTheory

/-- **(8.19)–(8.20)** (AKMM, p. 232): for `0 < G < y` and `γ > 0`, (8.2) and (8.3) hold iff
`A = y(1 − G/y)^{1/(1+ψ)}` and `η = (G/y)/(γ(1 − G/y))`. -/
theorem eq_8_19_8_20 {ψ γ η A y G : ℝ} (hγ : 0 < γ) (hy : 0 < y) (hG : 0 < G)
    (hGy : G < y) :
    (y = A * (1 - G / y) ^ (-(1 + ψ)⁻¹) ∧ G = γ * η / (1 + γ * η) * y) ↔
      (A = y * (1 - G / y) ^ (1 + ψ)⁻¹ ∧ η = G / y / (γ * (1 - G / y))) := by
  have hs1 : 0 < 1 - G / y := by rw [sub_pos, div_lt_one hy]; exact hGy
  have hs0 : 0 < G / y := div_pos hG hy
  have hGs : G = G / y * y := by field_simp
  set s := G / y with hs_def
  set R := (1 - s) ^ (1 + ψ)⁻¹ with hR_def
  have hR : 0 < R := Real.rpow_pos_of_pos hs1 _
  have hneg : (1 - s) ^ (-(1 + ψ)⁻¹) = R⁻¹ := Real.rpow_neg hs1.le _
  rw [hneg]
  refine and_congr ?_ ?_
  · constructor
    · intro h; rw [h]; field_simp
    · intro h; rw [h]; field_simp
  · rw [hGs]
    constructor
    · intro h
      have h' : s = γ * η / (1 + γ * η) := mul_right_cancel₀ hy.ne' h
      have h1 : 1 + γ * η ≠ 0 := by
        intro h0; rw [h0, div_zero] at h'; linarith
      have h2 : s * (1 + γ * η) = γ * η := by rw [h']; field_simp
      rw [eq_div_iff (by positivity)]
      linear_combination -h2
    · intro h
      have hX : 1 + γ * η = (1 - s)⁻¹ := by
        rw [h]; field_simp; ring
      rw [hX, h]
      field_simp

/-- **The shocks are recovered from the data** (AKMM, p. 232): `(A, η) ↦ (y*, G*)` maps the
positive quadrant into `{0 < G < y}`, and (8.19)–(8.20) invert it. -/
theorem sl_bijection {ψ γ A η : ℝ} (hγ : 0 < γ) (hA : 0 < A) (hη : 0 < η) :
    0 < sm_Gstar ψ γ η A ∧ sm_Gstar ψ γ η A < sm_ystar ψ γ η A ∧
      A = sm_ystar ψ γ η A * (1 - sm_Gstar ψ γ η A / sm_ystar ψ γ η A) ^ (1 + ψ)⁻¹ ∧
      η = sm_Gstar ψ γ η A / sm_ystar ψ γ η A /
        (γ * (1 - sm_Gstar ψ γ η A / sm_ystar ψ γ η A)) := by
  have hγη : 0 < γ * η := mul_pos hγ hη
  have hy : 0 < sm_ystar ψ γ η A := by unfold sm_ystar; positivity
  have hG : 0 < sm_Gstar ψ γ η A := (sm_star_feasible (ψ := ψ) hγη hA).2.1
  have hGy : sm_Gstar ψ γ η A < sm_ystar ψ γ η A := by
    rw [(sm_ystar_eq (ψ := ψ) (A := A) hγη).2]
    have : γ * η / (1 + γ * η) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  have h := (sm_equilibrium_unique (ψ := ψ) (A := A) hγη hy (G := sm_Gstar ψ γ η A)).2
    ⟨rfl, rfl⟩
  obtain ⟨h1, h2⟩ := (eq_8_19_8_20 hγ hy hG hGy).1 h
  exact ⟨hG, hGy, h1, h2⟩

/-- **The likelihood of an observation** (AKMM, p. 232), for discrete shocks: if
`y = y*(A, η)` and `G = G*(A, η)` pointwise, `A, η > 0`, and `A`, `η` are independent, then for
data `0 < G₀ < y₀`, `Pr(y = y₀, G = G₀) = Pr(A = A₀)·Pr(η = η₀)` with `(A₀, η₀)` given by
(8.19)–(8.20) at `(y₀, G₀)`. -/
theorem sl_likelihood_discrete {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ψ γ : ℝ} (hγ : 0 < γ) {A η y G : Ω → ℝ}
    (hApos : ∀ ω, 0 < A ω) (hηpos : ∀ ω, 0 < η ω)
    (hy : ∀ ω, y ω = sm_ystar ψ γ (η ω) (A ω)) (hG : ∀ ω, G ω = sm_Gstar ψ γ (η ω) (A ω))
    (hind : IndepFun A η μ) {y0 G0 : ℝ} (hy0 : 0 < y0) (hG0 : 0 < G0) (hGy0 : G0 < y0) :
    μ {ω | y ω = y0 ∧ G ω = G0} =
      μ {ω | A ω = y0 * (1 - G0 / y0) ^ (1 + ψ)⁻¹} *
        μ {ω | η ω = G0 / y0 / (γ * (1 - G0 / y0))} := by
  have hset : {ω | y ω = y0 ∧ G ω = G0} =
      A ⁻¹' {y0 * (1 - G0 / y0) ^ (1 + ψ)⁻¹} ∩ η ⁻¹' {G0 / y0 / (γ * (1 - G0 / y0))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    obtain ⟨-, -, h1, h2⟩ := sl_bijection hγ (hApos ω) (hηpos ω)
    rw [hy, hG]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨h1, h2⟩
    · rintro ⟨hA0, hη0⟩
      have h82 := (eq_8_19_8_20 hγ hy0 hG0 hGy0 (A := A ω) (η := η ω)).2 ⟨hA0, hη0⟩
      have hγη : 0 < γ * η ω := mul_pos hγ (hηpos ω)
      obtain ⟨e1, e2⟩ := (sm_equilibrium_unique (ψ := ψ) (A := A ω) hγη hy0).1 h82
      exact ⟨e1.symm, e2.symm⟩
  rw [hset]
  exact hind.measure_inter_preimage_eq_mul _ _ (MeasurableSet.singleton _)
    (MeasurableSet.singleton _)

/-- **The sample likelihood** (AKMM, p. 232): with positive likelihoods, the log of
`∏ₜ p_A(Aₜ)p_η(ηₜ)` is `Σₜ (log p_A(Aₜ) + log p_η(ηₜ))`. -/
theorem sl_loglik {T : ℕ} (pA pη : ℝ → ℝ) (A η : ℕ → ℝ) (hA : ∀ t, 0 < pA (A t))
    (hη : ∀ t, 0 < pη (η t)) :
    Real.log (∏ t ∈ Finset.range T, (pA (A t) * pη (η t))) =
      ∑ t ∈ Finset.range T, (Real.log (pA (A t)) + Real.log (pη (η t))) := by
  rw [Real.log_prod (fun t _ => (mul_pos (hA t) (hη t)).ne')]
  exact Finset.sum_congr rfl fun t _ => Real.log_mul (hA t).ne' (hη t).ne'

/-- **The Jacobian of (8.19)–(8.20)** (AKMM, p. 232, corrected): at `0 < G < y`, with
`s = G/y` and `q = 1/(1+ψ)`, the map `(y, G) ↦ (A, η)` has partial derivatives
`∂A/∂y = (1−s)^q + qs(1−s)^{q−1}`, `∂A/∂G = −q(1−s)^{q−1}`, `∂η/∂y = −s/(γy(1−s)²)`,
`∂η/∂G = 1/(γy(1−s)²)`, and Jacobian determinant `(1−s)^q/(γy(1−s)²)`. The density of `(y, G)` is
`p_A(A)p_η(η)` times this determinant, not `p_A(A)p_η(η)` as printed. -/
theorem sl_jacobian {ψ γ y G : ℝ} (hγ : 0 < γ) (hy : 0 < y) (hG : 0 < G)
    (hGy : G < y) :
    HasDerivAt (fun y' => y' * (1 - G / y') ^ (1 + ψ)⁻¹)
      ((1 - G / y) ^ (1 + ψ)⁻¹ + (1 + ψ)⁻¹ * (G / y) * (1 - G / y) ^ ((1 + ψ)⁻¹ - 1)) y ∧
    HasDerivAt (fun G' => y * (1 - G' / y) ^ (1 + ψ)⁻¹)
      (-((1 + ψ)⁻¹ * (1 - G / y) ^ ((1 + ψ)⁻¹ - 1))) G ∧
    HasDerivAt (fun y' => G / y' / (γ * (1 - G / y')))
      (-(G / y / (γ * y * (1 - G / y) ^ 2))) y ∧
    HasDerivAt (fun G' => G' / y / (γ * (1 - G' / y))) (1 / (γ * y * (1 - G / y) ^ 2)) G ∧
    ((1 - G / y) ^ (1 + ψ)⁻¹ + (1 + ψ)⁻¹ * (G / y) * (1 - G / y) ^ ((1 + ψ)⁻¹ - 1)) *
        (1 / (γ * y * (1 - G / y) ^ 2)) -
      (-((1 + ψ)⁻¹ * (1 - G / y) ^ ((1 + ψ)⁻¹ - 1))) * (-(G / y / (γ * y * (1 - G / y) ^ 2))) =
      (1 - G / y) ^ (1 + ψ)⁻¹ / (γ * y * (1 - G / y) ^ 2) := by
  set q := (1 + ψ)⁻¹ with hq
  have hs : 0 < 1 - G / y := by rw [sub_pos, div_lt_one hy]; exact hGy
  have hyG : 0 < y - G := by linarith
  have hq1 : (1 - G / y) ^ (q - 1) = (1 - G / y) ^ q / (1 - G / y) := Real.rpow_sub_one hs.ne' q
  -- `∂A/∂y`
  have hin : HasDerivAt (fun y' : ℝ => 1 - G / y') (G / y ^ 2) y := by
    have := ((hasDerivAt_inv hy.ne').const_mul G).const_sub 1
    convert this using 1
    · funext y'; simp [div_eq_mul_inv]
    · field_simp
  have hAy := (hasDerivAt_id y).mul (hin.rpow_const (p := q) (Or.inl hs.ne'))
  -- `∂A/∂G`
  have hinG : HasDerivAt (fun G' : ℝ => 1 - G' / y) (-(1 / y)) G := by
    have := ((hasDerivAt_id G).div_const y).const_sub 1
    convert this using 1
    simp
  have hAG := (hinG.rpow_const (p := q) (Or.inl hs.ne')).const_mul y
  -- `∂η/∂y`: near `y`, `η = G/(γ(y' − G))`
  have hηy0 : HasDerivAt (fun y' => G / (γ * (y' - G))) (-(G * γ) / (γ * (y - G)) ^ 2) y := by
    have h1 : HasDerivAt (fun y' => γ * (y' - G)) γ y := by
      simpa using ((hasDerivAt_id y).sub_const G).const_mul γ
    have := (h1.inv (by positivity)).const_mul G
    convert this using 1
    · funext y'; simp [div_eq_mul_inv]
    · ring
  have hηy : HasDerivAt (fun y' => G / y' / (γ * (1 - G / y')))
      (-(G * γ) / (γ * (y - G)) ^ 2) y := by
    refine hηy0.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hy] with y' hy'
    rcases eq_or_ne (y' - G) 0 with h | h
    · rw [show y' = G by linarith]
      simp [div_self hG.ne']
    · field_simp
  -- `∂η/∂G`
  have hηG0 : HasDerivAt (fun G' => G' / (γ * (y - G'))) (y / (γ * (y - G) ^ 2)) G := by
    have h1 : HasDerivAt (fun G' => γ * (y - G')) (-γ) G := by
      simpa using ((hasDerivAt_id G).const_sub y).const_mul γ
    have := (hasDerivAt_id G).div h1 (by positivity)
    convert this using 1
    · rfl
    · simp only [id]; field_simp; ring
  have hηG : HasDerivAt (fun G' => G' / y / (γ * (1 - G' / y))) (y / (γ * (y - G) ^ 2)) G := by
    refine hηG0.congr_of_eventuallyEq ?_
    filter_upwards with G'
    rcases eq_or_ne (y - G') 0 with h | h
    · rw [show G' = y by linarith]
      simp [div_self hy.ne']
    · field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert hAy using 1
    · rfl
    · rw [hq1, id_eq]
      field_simp
  · convert hAG using 1
    field_simp
  · convert hηy using 1
    field_simp
  · convert hηG using 1
    field_simp
  · rw [hq1]
    field_simp
    ring

/-- **The Jacobian depends on `ψ`** (AKMM, p. 232): at `y = 1`, `G = 1/2`, `γ = 1` the
determinant `(1−s)^q/(γy(1−s)²)` differs between `ψ = 1` and `ψ = 3`, so omitting it changes the
likelihood as a function of `ψ`. -/
theorem sl_jacobian_depends_on_psi :
    (1 - (1 / 2 : ℝ) / 1) ^ ((1 + (1 : ℝ))⁻¹) / (1 * 1 * (1 - (1 / 2 : ℝ) / 1) ^ 2) ≠
      (1 - (1 / 2 : ℝ) / 1) ^ ((1 + (3 : ℝ))⁻¹) / (1 * 1 * (1 - (1 / 2 : ℝ) / 1) ^ 2) := by
  intro h
  have hpos : (0 : ℝ) < 1 * 1 * (1 - (1 / 2 : ℝ) / 1) ^ 2 := by norm_num
  rw [div_left_inj' hpos.ne'] at h
  have : (1 - (1 / 2 : ℝ) / 1) ^ ((1 + (1 : ℝ))⁻¹) < (1 - (1 / 2 : ℝ) / 1) ^ ((1 + (3 : ℝ))⁻¹) :=
    Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- **The implied multiplier** (AKMM, p. 232): "once we have estimated the parameters, we can
differentiate (8.2) to find the implied fiscal multiplier". For any likelihood `L` on
`θ = (ψ, γ)` maximised at `θ̂`, the multiplier `m(θ) = (1+γ)/(1+γ+ψ)` (Appendix 8.A.2 at
`η̄ = 1`) at `θ̂` maximises the profile likelihood of the multiplier (Miao's invariance
theorem `ml_invariance_profile`). -/
theorem sl_multiplier_mle (L : ℝ × ℝ → ℝ) (θhat : ℝ × ℝ) (hmax : ∀ θ, L θ ≤ L θhat) :
    Miao.StructuralEstimation.ml_profileLikelihood L (fun θ => (1 + θ.2) / (1 + θ.2 + θ.1))
        ((1 + θhat.2) / (1 + θhat.2 + θhat.1)) = L θhat ∧
      ∀ m ∈ Set.range (fun θ : ℝ × ℝ => (1 + θ.2) / (1 + θ.2 + θ.1)),
        Miao.StructuralEstimation.ml_profileLikelihood L
          (fun θ => (1 + θ.2) / (1 + θ.2 + θ.1)) m ≤
        Miao.StructuralEstimation.ml_profileLikelihood L
          (fun θ => (1 + θ.2) / (1 + θ.2 + θ.1)) ((1 + θhat.2) / (1 + θhat.2 + θhat.1)) :=
  Miao.StructuralEstimation.ml_invariance_profile L _ θhat hmax

end AKMM.QuantitativeMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Kalman-filter likelihood of the linearised model

AKMM, §8.7, (8.21)–(8.22) and the likelihood, pp. 232–233, with footnote 9.

The linearised model `X̂ₜ₊₁ = AX̂ₜ + Bεₜ₊₁`, `Ŷₜ = CX̂ₜ` is Miao's time-invariant Kalman system
(`KFSystem.const`) with no controls, no measurement input and no measurement noise
(`kl_system`, `kl_model`). Miao's filter is proved as recursive linear projection from second
moments; the Gaussian reading of the book (conditional laws are normal) is not formalised.

* The innovation `Yₜ − CX_{t|t−1}` has mean zero and covariance `CP_{t|t−1}C'` (`kl_innovations`,
  `kl_Om`): the book's "mean `CX_{t|t−1}` and covariance `CP_{t|t−1}C'`".
* **The prediction-error decomposition**: the joint density is the product of the one-step
  conditional densities (`kl_chain_rule`), and the log of the Gaussian likelihood
  `∏ₜ N(Yₜ | CX_{t|t−1}, CP_{t|t−1}C')` is
  `−(n_YT/2)log 2π − ½Σ log|CPC'| − ½Σ aₜ'(CPC')⁻¹aₜ` (`kl_likelihood`, from Miao's
  Example 10.1.4).
* **Footnote 9**: for stable `A` the invariant initial covariance `P = APA' + BB'` exists and is
  unique (`fn_9`, from Miao's `kf_step1_cov`).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Matrix Miao.PartialInformation

variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y]

/-- **(8.21)–(8.22)** (AKMM, p. 233) as a Kalman system: transition `A`, shock loading `B`,
measurement `C`, no controls (`Fin 0`), no measurement input or noise, initial mean `x₀` and
covariance `P₀`. -/
def kl_system (A : Matrix X X ℝ) (B : Matrix X E ℝ) (C : Matrix Y X ℝ) (x0 : X → ℝ)
    (P0 : Matrix X X ℝ) : KFSystem X (Fin 0) Y E :=
  KFSystem.const A 0 B C 0 0 x0 P0

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- AKMM, (8.21)–(8.22): the book's model `X̂ₜ₊₁ = AX̂ₜ + Bεₜ₊₁`, `Ŷₜ = CX̂ₜ` gives the state and
measurement equations (10.1)–(10.2) of the Kalman system with zero controls and input. -/
theorem kl_model {Ω : Type*} {A : Matrix X X ℝ} {B : Matrix X E ℝ} {C : Matrix Y X ℝ}
    {x0 : X → ℝ} {P0 : Matrix X X ℝ} {x : ℕ → Ω → X → ℝ} {yv : ℕ → Ω → Y → ℝ}
    {ε : ℕ → Ω → E → ℝ} (hx : ∀ t, x (t + 1) = kf_app A (x t) + kf_app B (ε (t + 1)))
    (hy : ∀ t, yv t = kf_app C (x t)) :
    (∀ t, x (t + 1) = kf_app ((kl_system A B C x0 P0).A t) (x t) +
      kf_app ((kl_system A B C x0 P0).B t) (0 : Ω → Fin 0 → ℝ) +
      kf_app ((kl_system A B C x0 P0).C t) (ε (t + 1))) ∧
    (∀ t, yv t = kf_app ((kl_system A B C x0 P0).G t) (x t) + 0 +
      kf_app ((kl_system A B C x0 P0).D t) (ε t)) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [hx t]
    simp only [kl_system, KFSystem.const, kf_app_zero_mat, add_zero]
  · rw [hy t]
    simp only [kl_system, KFSystem.const, kf_app_zero_mat, add_zero]

omit [DecidableEq X] in
/-- AKMM, p. 233: with no measurement noise the innovation covariance (10.8) is
`Ω_{t|t−1} = CP_{t|t−1}C'`. -/
theorem kl_Om (A : Matrix X X ℝ) (B : Matrix X E ℝ) (C : Matrix Y X ℝ) (x0 : X → ℝ)
    (P0 : Matrix X X ℝ) [DecidableEq X] (t : ℕ) :
    (kl_system A B C x0 P0).Om t = C * (kl_system A B C x0 P0).Spred t * Cᵀ := by
  simp [KFSystem.Om, kf_Om, kl_system, KFSystem.const]

/-- **The predictive distribution of `Yₜ`** (AKMM, p. 233), second-moment version: under
(8.21)–(8.22) with white-noise shocks (`E εₜ = 0`, `E εₛεₜ' = δₛₜI`) uncorrelated with the
initial state, the innovation `Yₜ − CX_{t|t−1}` is square integrable with mean zero and
`E aₜaₜ' = CP_{t|t−1}C'`. -/
theorem kl_innovations {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [DecidableEq E] {A : Matrix X X ℝ} {B : Matrix X E ℝ}
    {C : Matrix Y X ℝ} {x0 : X → ℝ} {P0 : Matrix X X ℝ} {x : ℕ → Ω → X → ℝ}
    {yv : ℕ → Ω → Y → ℝ} {ε : ℕ → Ω → E → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app A (x t) + kf_app B (ε (t + 1)))
    (hy : ∀ t, yv t = kf_app C (x t))
    (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t)) (hm0 : kf_mean μ (x 0) = x0)
    (hmε : ∀ t, kf_mean μ (ε t) = 0)
    (hS0 : var_mom μ (x 0 - fun _ => x0) (x 0 - fun _ => x0) = P0)
    (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
    (h0ε : ∀ t, var_mom μ (x 0 - fun _ => x0) (ε t) = 0)
    (hΩ : ∀ t, IsUnit ((kl_system A B C x0 P0).Om t).det) (t : ℕ) :
    (kl_system A B C x0 P0).innov yv 0 0 t =
        yv t - kf_app C ((kl_system A B C x0 P0).xpred yv 0 0 t) ∧
      kf_L2 μ ((kl_system A B C x0 P0).innov yv 0 0 t) ∧
      kf_mean μ ((kl_system A B C x0 P0).innov yv 0 0 t) = 0 ∧
      var_mom μ ((kl_system A B C x0 P0).innov yv 0 0 t)
        ((kl_system A B C x0 P0).innov yv 0 0 t) =
        C * (kl_system A B C x0 P0).Spred t * Cᵀ := by
  obtain ⟨hx', hy'⟩ := kl_model (x0 := x0) (P0 := P0) hx hy
  have h1 := (kl_system A B C x0 P0).kf_innov_L2 μ (h := 0) (u := 0) hx' hy' hL0 hLε hm0 hmε
    hS0 hεε h0ε hΩ t
  have h2 := ((kl_system A B C x0 P0).eq_10_8 μ (h := 0) (u := 0) hx' hy' hL0 hLε hm0 hmε hS0
    hεε h0ε hΩ t).1
  refine ⟨?_, h1.1, h1.2, by rw [h2, kl_Om]⟩
  simp only [KFSystem.innov, Pi.zero_apply, sub_zero]
  rfl

/-- AKMM, p. 233: the density `N(Y | m, Σ)` of the multivariate normal at `Y`. -/
noncomputable def kl_normal (m : Y → ℝ) (S : Matrix Y Y ℝ) (yv : Y → ℝ) : ℝ :=
  kf_gaussDens S (yv - m)

/-- **The prediction-error decomposition** (AKMM, p. 233): if `pₜ > 0` is the joint density of
`(Y₁, …, Yₜ)` at the data, `p₀ = 1`, and `pₜ₊₁/pₜ` is the conditional density of `Yₜ₊₁` given
`Y₁, …, Yₜ`, the product of the conditional densities is the joint density. -/
theorem kl_chain_rule (p : ℕ → ℝ) (hp : ∀ t, 0 < p t) (h0 : p 0 = 1) (T : ℕ) :
    ∏ t ∈ Finset.range T, (p (t + 1) / p t) = p T := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [(hp T).ne']

omit [DecidableEq X] in
/-- **The likelihood** (AKMM, p. 233): for data `Y₁, …, Y_T`, predictions `X_{t|t−1}` and
covariances `P_{t|t−1}` with `|CPC'| > 0`, the log of
`∏_{t=1}^T N(Yₜ | CX_{t|t−1}, CP_{t|t−1}C')` is
`−(n_YT/2) log 2π − ½Σₜ log|CPₜC'| − ½Σₜ aₜ'(CPₜC')⁻¹aₜ` with `aₜ = Yₜ − CX_{t|t−1}`. -/
theorem kl_likelihood (C : Matrix Y X ℝ) (P : ℕ → Matrix X X ℝ) (xhat : ℕ → X → ℝ)
    (yv : ℕ → Y → ℝ) (T : ℕ) (hdet : ∀ t, 0 < (C * P t * Cᵀ).det) :
    Real.log (∏ t ∈ Finset.Icc 1 T, kl_normal (C *ᵥ xhat t) (C * P t * Cᵀ) (yv t)) =
      -(Fintype.card Y * T / 2) * Real.log (2 * Real.pi) -
        1 / 2 * ∑ t ∈ Finset.Icc 1 T, Real.log (C * P t * Cᵀ).det -
        1 / 2 * ∑ t ∈ Finset.Icc 1 T,
          (yv t - C *ᵥ xhat t) ⬝ᵥ ((C * P t * Cᵀ)⁻¹ *ᵥ (yv t - C *ᵥ xhat t)) := by
  have hpos : ∀ t, 0 < kl_normal (C *ᵥ xhat t) (C * P t * Cᵀ) (yv t) := by
    intro t
    unfold kl_normal kf_gaussDens
    have h2 : 0 < 2 * Real.pi := by positivity
    have := Real.rpow_pos_of_pos h2 (-(Fintype.card Y : ℝ) / 2)
    have := Real.rpow_pos_of_pos (hdet t) (-(1 : ℝ) / 2)
    positivity
  rw [Real.log_prod (fun t _ => (hpos t).ne')]
  exact (example_10_1_4 (fun t => C * P t * Cᵀ) (fun t => yv t - C *ᵥ xhat t) T hdet).2

omit [Fintype Y] [DecidableEq Y] in
/-- **Footnote 9** (AKMM, p. 233): drawing `X₁` from the invariant distribution. For stable `A`,
the invariant covariance `P_{1|0} = AP_{1|0}A' + BB'` exists and is unique (Miao's
`kf_step1_cov`), and the invariant mean is `X_{1|0} = 0` (`kf_step1_mean`). -/
theorem fn_9 {A : Matrix X X ℝ} (hA : ls_Stable A) (B : Matrix X E ℝ) :
    var_lyapSol A (B * Bᵀ) = A * var_lyapSol A (B * Bᵀ) * Aᵀ + B * Bᵀ ∧
      (∀ P : Matrix X X ℝ, P = A * P * Aᵀ + B * Bᵀ → P = var_lyapSol A (B * Bᵀ)) ∧
      ∀ m : X → ℝ, A *ᵥ m = m → m = 0 := by
  obtain ⟨h1, h2, -, -⟩ := kf_step1_cov hA (B * Bᵀ)
  exact ⟨h1, h2, fun m hm => kf_step1_mean hA hm⟩

end AKMM.QuantitativeMethods

set_option linter.style.longLine false
#print axioms AKMM.QuantitativeMethods.sm_utility
#print axioms AKMM.QuantitativeMethods.sm_lstar
#print axioms AKMM.QuantitativeMethods.sm_cstar
#print axioms AKMM.QuantitativeMethods.sm_Gstar
#print axioms AKMM.QuantitativeMethods.sm_eq_rpow_inv_iff
#print axioms AKMM.QuantitativeMethods.sm_lstar_pos
#print axioms AKMM.QuantitativeMethods.sm_lstar_rpow
#print axioms AKMM.QuantitativeMethods.sm_lstar_rpow_psi
#print axioms AKMM.QuantitativeMethods.sm_star_feasible
#print axioms AKMM.QuantitativeMethods.sm_foc_iff
#print axioms AKMM.QuantitativeMethods.sm_rpow_tangent
#print axioms AKMM.QuantitativeMethods.sm_planner_optimal
#print axioms AKMM.QuantitativeMethods.sm_planner_unique
#print axioms AKMM.QuantitativeMethods.eq_8_2_8_3
#print axioms AKMM.QuantitativeMethods.sm_ystar
#print axioms AKMM.QuantitativeMethods.sm_ystar_eq
#print axioms AKMM.QuantitativeMethods.sm_equilibrium_unique
#print axioms AKMM.QuantitativeMethods.sm_fiscal_rule_monotone
#print axioms AKMM.QuantitativeMethods.sm_chi
#print axioms AKMM.QuantitativeMethods.sm_multiplier_formula
#print axioms AKMM.QuantitativeMethods.sm_multiplier_mem_Ioo
#print axioms AKMM.QuantitativeMethods.sm_multiplier_eta
#print axioms AKMM.QuantitativeMethods.sm_supply_poly_iff
#print axioms AKMM.QuantitativeMethods.sm_supply_slope
#print axioms AKMM.QuantitativeMethods.sm_supply_dA
#print axioms AKMM.QuantitativeMethods.appendix_8A_2_total_differential
#print axioms AKMM.QuantitativeMethods.appendix_8A_2_steady
#print axioms AKMM.QuantitativeMethods.eq_8_5
#print axioms AKMM.QuantitativeMethods.eq_8_5_log
#print axioms AKMM.QuantitativeMethods.eq_8_6
#print axioms AKMM.QuantitativeMethods.fn_3
#print axioms AKMM.QuantitativeMethods.sm_multiplier_antitone_psi
#print axioms AKMM.QuantitativeMethods.eq_8_8_8_9
#print axioms AKMM.QuantitativeMethods.id_impact
#print axioms AKMM.QuantitativeMethods.id_solution
#print axioms AKMM.QuantitativeMethods.id_mom_obs
#print axioms AKMM.QuantitativeMethods.id_G_correlated_with_A
#print axioms AKMM.QuantitativeMethods.id_ols_slope
#print axioms AKMM.QuantitativeMethods.id_iv
#print axioms AKMM.QuantitativeMethods.id_restriction_identifies
#print axioms AKMM.QuantitativeMethods.id_g_exogenous
#print axioms AKMM.QuantitativeMethods.eq_8_7
#print axioms AKMM.QuantitativeMethods.eq_8_7_process
#print axioms AKMM.QuantitativeMethods.sv_var_u
#print axioms AKMM.QuantitativeMethods.sv_rotation
#print axioms AKMM.QuantitativeMethods.sv_rotation_shocks
#print axioms AKMM.QuantitativeMethods.sv_rotation_converse
#print axioms AKMM.QuantitativeMethods.sv_not_identified
#print axioms AKMM.QuantitativeMethods.sv_symm
#print axioms AKMM.QuantitativeMethods.sv_upper
#print axioms AKMM.QuantitativeMethods.sv_card_upper
#print axioms AKMM.QuantitativeMethods.sv_upperMap
#print axioms AKMM.QuantitativeMethods.sv_upperMap_bijective
#print axioms AKMM.QuantitativeMethods.sv_finrank_symm
#print axioms AKMM.QuantitativeMethods.sv_restriction_count
#print axioms AKMM.QuantitativeMethods.sv_normalisation
#print axioms AKMM.QuantitativeMethods.ch_lower_apply
#print axioms AKMM.QuantitativeMethods.ch_lower_mul_diag
#print axioms AKMM.QuantitativeMethods.ch_unique
#print axioms AKMM.QuantitativeMethods.ch_exists
#print axioms AKMM.QuantitativeMethods.ch_recursive_identification
#print axioms AKMM.QuantitativeMethods.ch_sign_counterexample
#print axioms AKMM.QuantitativeMethods.ch_first_column
#print axioms AKMM.QuantitativeMethods.ch_fiscal_example
#print axioms AKMM.QuantitativeMethods.vl_cumMult
#print axioms AKMM.QuantitativeMethods.vl_peakMult
#print axioms AKMM.QuantitativeMethods.vl_cum_multiplier_prop
#print axioms AKMM.QuantitativeMethods.vl_peak_multiplier_prop
#print axioms AKMM.QuantitativeMethods.vl_var1_irf
#print axioms AKMM.QuantitativeMethods.vl_companion
#print axioms AKMM.QuantitativeMethods.vl_stack
#print axioms AKMM.QuantitativeMethods.vl_load
#print axioms AKMM.QuantitativeMethods.vl_companion_rec
#print axioms AKMM.QuantitativeMethods.vl_companion_two
#print axioms AKMM.QuantitativeMethods.vl_companion_irf
#print axioms AKMM.QuantitativeMethods.vl_col
#print axioms AKMM.QuantitativeMethods.vl_mom_resid
#print axioms AKMM.QuantitativeMethods.vl_lp_estimand
#print axioms AKMM.QuantitativeMethods.vl_lp_exists
#print axioms AKMM.QuantitativeMethods.vl_var_estimand
#print axioms AKMM.QuantitativeMethods.vl_var_exists
#print axioms AKMM.QuantitativeMethods.fn_6
#print axioms AKMM.QuantitativeMethods.vl_lp_exogenous
#print axioms AKMM.QuantitativeMethods.vl_var1_estimands
#print axioms AKMM.QuantitativeMethods.vl_lp_differs
#print axioms AKMM.QuantitativeMethods.eq_8_16_8_17
#print axioms AKMM.QuantitativeMethods.eq_8_11
#print axioms AKMM.QuantitativeMethods.fm_budget_resource
#print axioms AKMM.QuantitativeMethods.eq_8_15
#print axioms AKMM.QuantitativeMethods.eq_8_18
#print axioms AKMM.QuantitativeMethods.eq_8_12_mean
#print axioms AKMM.QuantitativeMethods.fm_IsEquilibrium
#print axioms AKMM.QuantitativeMethods.fm_IsSteady
#print axioms AKMM.QuantitativeMethods.fm_r
#print axioms AKMM.QuantitativeMethods.fm_kl
#print axioms AKMM.QuantitativeMethods.fm_l
#print axioms AKMM.QuantitativeMethods.fm_Params
#print axioms AKMM.QuantitativeMethods.fm_r_pos
#print axioms AKMM.QuantitativeMethods.fm_kl_props
#print axioms AKMM.QuantitativeMethods.fm_cd_ratio
#print axioms AKMM.QuantitativeMethods.appendix_8A_1
#print axioms AKMM.QuantitativeMethods.fm_steady_exists
#print axioms AKMM.QuantitativeMethods.appendix_8A_1_ratios
#print axioms AKMM.QuantitativeMethods.appendix_8A_1_printed_G
#print axioms AKMM.QuantitativeMethods.fm_steady_isEquilibrium
#print axioms AKMM.QuantitativeMethods.fm_fixed_investment_multiplier
#print axioms AKMM.QuantitativeMethods.fm_beta_calibration
#print axioms AKMM.QuantitativeMethods.fm_frisch
#print axioms AKMM.QuantitativeMethods.fm_dl_dc
#print axioms AKMM.QuantitativeMethods.fm_lottery
#print axioms AKMM.QuantitativeMethods.fm_gamma_calibration
#print axioms AKMM.QuantitativeMethods.fm_multiplier_scale
#print axioms AKMM.QuantitativeMethods.fd_Y
#print axioms AKMM.QuantitativeMethods.fd_C
#print axioms AKMM.QuantitativeMethods.fd_g
#print axioms AKMM.QuantitativeMethods.fd_kap
#print axioms AKMM.QuantitativeMethods.fd_m
#print axioms AKMM.QuantitativeMethods.fd_n
#print axioms AKMM.QuantitativeMethods.fd_B
#print axioms AKMM.QuantitativeMethods.fd_lam
#print axioms AKMM.QuantitativeMethods.fd_p
#print axioms AKMM.QuantitativeMethods.fd_D
#print axioms AKMM.QuantitativeMethods.fd_q
#print axioms AKMM.QuantitativeMethods.fd_phi
#print axioms AKMM.QuantitativeMethods.fd_k
#print axioms AKMM.QuantitativeMethods.fd_c
#print axioms AKMM.QuantitativeMethods.fd_l
#print axioms AKMM.QuantitativeMethods.fd_y
#print axioms AKMM.QuantitativeMethods.fd_G
#print axioms AKMM.QuantitativeMethods.fd_coef
#print axioms AKMM.QuantitativeMethods.fd_ratios
#print axioms AKMM.QuantitativeMethods.fd_lam_props
#print axioms AKMM.QuantitativeMethods.fd_rel
#print axioms AKMM.QuantitativeMethods.fd_IsIRF
#print axioms AKMM.QuantitativeMethods.fd_irf_solves
#print axioms AKMM.QuantitativeMethods.fd_lam_lt_one
#print axioms AKMM.QuantitativeMethods.fd_k_bound
#print axioms AKMM.QuantitativeMethods.fd_irf_unique
#print axioms AKMM.QuantitativeMethods.fd_q_phi
#print axioms AKMM.QuantitativeMethods.fd_k_nonpos
#print axioms AKMM.QuantitativeMethods.fd_c_k_neg
#print axioms AKMM.QuantitativeMethods.fd_impact_signs
#print axioms AKMM.QuantitativeMethods.fd_investment_correction
#print axioms AKMM.QuantitativeMethods.fd_mult
#print axioms AKMM.QuantitativeMethods.fd_cum_lt
#print axioms AKMM.QuantitativeMethods.fd_mult_lt_one
#print axioms AKMM.QuantitativeMethods.fd_impact_mult
#print axioms AKMM.QuantitativeMethods.fd_impact_mult_mem
#print axioms AKMM.QuantitativeMethods.fd_impact_mult_strictMonoOn_rho
#print axioms AKMM.QuantitativeMethods.fd_KInf
#print axioms AKMM.QuantitativeMethods.fd_yInf
#print axioms AKMM.QuantitativeMethods.fd_GInf
#print axioms AKMM.QuantitativeMethods.fd_multInf
#print axioms AKMM.QuantitativeMethods.fd_k_tendsto
#print axioms AKMM.QuantitativeMethods.fd_sum_k
#print axioms AKMM.QuantitativeMethods.fd_mult_tendsto
#print axioms AKMM.QuantitativeMethods.fd_N
#print axioms AKMM.QuantitativeMethods.fd_Q
#print axioms AKMM.QuantitativeMethods.fd_inf_closed
#print axioms AKMM.QuantitativeMethods.fd_key
#print axioms AKMM.QuantitativeMethods.fd_det
#print axioms AKMM.QuantitativeMethods.fd_multInf_strictMono
#print axioms AKMM.QuantitativeMethods.fd_GInf_pos_top
#print axioms AKMM.QuantitativeMethods.fd_pencil
#print axioms AKMM.QuantitativeMethods.fd_le_lam
#print axioms AKMM.QuantitativeMethods.fd_f0_nonneg
#print axioms AKMM.QuantitativeMethods.fd_lam_mono_psi
#print axioms AKMM.QuantitativeMethods.fd_impact_mult_Phi
#print axioms AKMM.QuantitativeMethods.fd_impact_mult_antitone_psi
#print axioms AKMM.QuantitativeMethods.fd_static_exact
#print axioms AKMM.QuantitativeMethods.fd_resource_linear
#print axioms AKMM.QuantitativeMethods.fd_euler_linear
#print axioms AKMM.QuantitativeMethods.eq_8_19_8_20
#print axioms AKMM.QuantitativeMethods.sl_bijection
#print axioms AKMM.QuantitativeMethods.sl_likelihood_discrete
#print axioms AKMM.QuantitativeMethods.sl_loglik
#print axioms AKMM.QuantitativeMethods.sl_jacobian
#print axioms AKMM.QuantitativeMethods.sl_jacobian_depends_on_psi
#print axioms AKMM.QuantitativeMethods.sl_multiplier_mle
#print axioms AKMM.QuantitativeMethods.kl_system
#print axioms AKMM.QuantitativeMethods.kl_model
#print axioms AKMM.QuantitativeMethods.kl_Om
#print axioms AKMM.QuantitativeMethods.kl_innovations
#print axioms AKMM.QuantitativeMethods.kl_normal
#print axioms AKMM.QuantitativeMethods.kl_chain_rule
#print axioms AKMM.QuantitativeMethods.kl_likelihood
#print axioms AKMM.QuantitativeMethods.fn_9

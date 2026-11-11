/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

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

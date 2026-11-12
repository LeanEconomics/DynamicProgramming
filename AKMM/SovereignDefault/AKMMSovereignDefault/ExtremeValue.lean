/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Exp
import AKMMSovereignDefault.BondPrice

/-!
# Extreme-value smoothing: logit choice probabilities and (24.A.6)

AKMM, Appendix 24.A.1, Method 3, (24.A.5)–(24.A.6), pp. 900–901 (Dvorkin, Sanchez, Sapriza
and Yurdagul, 2021).

With i.i.d. standard Gumbel shocks `ε_k` (c.d.f. `G(x) = exp(−e^{−x})`, density
`g(x) = e^{−x} exp(−e^{−x})`) added to the values `v_k` of finitely many alternatives, the
probability that alternative `h` is chosen is
`P_h(v) = ∫ g(x) Π_{k≠h} G(x + v_h − v_k) dx`
(condition on `ε_h = x`; the other shocks are independent).

* `∫ e^{−x} exp(−c e^{−x}) dx = 1/c` for `c > 0` (`ev_integral`), by the fundamental theorem of
  calculus on `ℝ`.
* **Logit** (`ev_logit`): `P_h(v) = e^{v_h}/Σ_k e^{v_k}`; the probabilities are positive, sum
  to one and are continuous in the values (`ev_logit_pos`, `ev_logit_sum`,
  `ev_logit_continuous`), so small changes in values move choice probabilities only a little,
  the smoothing the text describes.
* **Default and borrowing probabilities** (`ev_conditional_borrow`): with the default option
  and the debt choices as alternatives, the borrowing probabilities conditional on repayment
  are again logit over the debt choices (independence of irrelevant alternatives).
* **(24.A.6)** (`eq_24_A_6_logit`): with logit default and borrowing probabilities the bond
  price exists, is unique and lies in `[0, δ/(δ + r)]` (via `eq_24_A_6`).

The conditioning formula is derived from the product of the Gumbel laws in `GumbelProduct`
(`ev_logit_of_gumbel`).
-/

namespace AKMM.SovereignDefault

open MeasureTheory Filter Topology Finset

/-- The standard Gumbel c.d.f. `G(x) = exp(−e^{−x})`. -/
noncomputable def ev_gumbelCDF (x : ℝ) : ℝ := Real.exp (-Real.exp (-x))

/-- The standard Gumbel density `g(x) = e^{−x} exp(−e^{−x})`. -/
noncomputable def ev_gumbelPDF (x : ℝ) : ℝ := Real.exp (-x) * Real.exp (-Real.exp (-x))

/-- AKMM, p. 900: the probability that alternative `h` has the largest `v_k + ε_k`, given
i.i.d. Gumbel shocks: `P_h(v) = ∫ g(x) Π_{k≠h} G(x + v_h − v_k) dx`. -/
noncomputable def ev_choiceProb {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (h : ι) :
    ℝ :=
  ∫ x, ev_gumbelPDF x * ∏ k ∈ univ.erase h, ev_gumbelCDF (x + v h - v k)

/-- The antiderivative `exp(−c e^{−x})/c` of `e^{−x} exp(−c e^{−x})`. -/
theorem ev_hasDerivAt {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (fun x => Real.exp (-(c * Real.exp (-x))) / c)
      (Real.exp (-x) * Real.exp (-(c * Real.exp (-x)))) x := by
  have h1 : HasDerivAt (fun x => -(c * Real.exp (-x))) (c * Real.exp (-x)) x := by
    have := (((hasDerivAt_neg x).exp).const_mul c).neg
    convert this using 1
    ring
  have := (h1.exp).div_const c
  convert this using 1
  field_simp

/-- The density `e^{−x} exp(−c e^{−x})` is nonnegative and continuous. -/
theorem ev_density_continuous (c : ℝ) :
    Continuous fun x => Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) := by
  fun_prop

/-- The limits of the antiderivative and the integrability of `e^{−x} exp(−c e^{−x})`. -/
theorem ev_integrable {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => Real.exp (-(c * Real.exp (-x))) / c) atBot (𝓝 0) ∧
      Tendsto (fun x => Real.exp (-(c * Real.exp (-x))) / c) atTop (𝓝 (1 / c)) ∧
      Integrable fun x => Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) := by
  set F : ℝ → ℝ := fun x => Real.exp (-(c * Real.exp (-x))) / c with hF
  set f : ℝ → ℝ := fun x => Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) with hf
  have hd : ∀ x, HasDerivAt F (f x) x := ev_hasDerivAt hc
  have hpos : ∀ x, 0 ≤ f x := fun x => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have htop : Tendsto F atTop (𝓝 (1 / c)) := by
    have h1 : Tendsto (fun x : ℝ => -(c * Real.exp (-x))) atTop (𝓝 (-(c * 0))) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul c).neg
    have h2 := (Real.continuous_exp.tendsto _).comp h1
    simp only [mul_zero, neg_zero, Real.exp_zero] at h2
    simpa [hF, one_div] using h2.div_const c
  have hbot : Tendsto F atBot (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.exp (-x)) atBot atTop :=
      Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
    have h1 : Tendsto (fun x : ℝ => -(c * Real.exp (-x))) atBot atBot :=
      tendsto_neg_atTop_atBot.comp (h0.const_mul_atTop hc)
    have h2 := Real.tendsto_exp_atBot.comp h1
    simpa [hF] using h2.div_const c
  have hFnn : ∀ x, 0 ≤ F x := fun x => div_nonneg (Real.exp_pos _).le hc.le
  have hint : Integrable f := by
    have hIoi : IntegrableOn f (Set.Ioi 0) :=
      integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hd x) (fun x _ => hpos x) htop
    have hIic : IntegrableOn f (Set.Iic 0) := by
      refine integrableOn_Iic_of_intervalIntegral_norm_bounded (F 0) 0
        (a := fun n : ℕ => -(n : ℝ)) (l := atTop)
        (fun n => (ev_density_continuous c).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) ?_
      refine Eventually.of_forall fun n => ?_
      have hn : -(n : ℝ) ≤ 0 := neg_nonpos.2 (Nat.cast_nonneg n)
      have heq : ∫ x in -(n : ℝ)..0, ‖f x‖ = ∫ x in -(n : ℝ)..0, f x :=
        intervalIntegral.integral_congr fun x _ => by
          simp only [Real.norm_eq_abs, abs_of_nonneg (hpos x)]
      rw [heq, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
        ((ev_density_continuous c).intervalIntegrable _ _)]
      linarith [hFnn (-(n : ℝ))]
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hIic.union hIoi
  exact ⟨hbot, htop, hint⟩

/-- `∫ e^{−x} exp(−c e^{−x}) dx = 1/c` for `c > 0`. -/
theorem ev_integral {c : ℝ} (hc : 0 < c) :
    ∫ x, Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) = 1 / c := by
  obtain ⟨hbot, htop, hint⟩ := ev_integrable hc
  rw [integral_of_hasDerivAt_of_tendsto (ev_hasDerivAt hc) hint hbot htop, sub_zero]

/-- **Logit choice probabilities** (AKMM, p. 900, Method 3): with i.i.d. Gumbel shocks the
probability that alternative `h` is chosen is `e^{v_h}/Σ_k e^{v_k}`. -/
theorem ev_logit {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (h : ι) :
    ev_choiceProb v h = Real.exp (v h) / ∑ k, Real.exp (v k) := by
  set c := ∑ k, Real.exp (v k - v h) with hc
  have hcpos : 0 < c := by
    rw [hc, ← add_sum_erase _ _ (mem_univ h)]
    exact add_pos_of_pos_of_nonneg (Real.exp_pos _)
      (sum_nonneg fun _ _ => (Real.exp_pos _).le)
  have hpt : ∀ x, ev_gumbelPDF x * ∏ k ∈ univ.erase h, ev_gumbelCDF (x + v h - v k) =
      Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) := by
    intro x
    unfold ev_gumbelPDF ev_gumbelCDF
    rw [← Real.exp_sum, mul_assoc, ← Real.exp_add]
    congr 2
    rw [hc, ← add_sum_erase _ _ (mem_univ h), sub_self, Real.exp_zero, add_mul, one_mul,
      sum_mul, neg_add, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [← Real.exp_add]
    congr 2
    ring
  unfold ev_choiceProb
  simp only [hpt]
  rw [ev_integral hcpos, hc]
  have hS : ∑ k, Real.exp (v k - v h) = (∑ k, Real.exp (v k)) / Real.exp (v h) := by
    rw [sum_div]
    exact sum_congr rfl fun k _ => by rw [Real.exp_sub]
  rw [hS, one_div, inv_div]

/-- The logit probabilities are positive. -/
theorem ev_logit_pos {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) (h : ι) :
    0 < Real.exp (v h) / ∑ k, Real.exp (v k) :=
  div_pos (Real.exp_pos _) (sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty)

/-- The logit probabilities sum to one. -/
theorem ev_logit_sum {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) :
    ∑ h, Real.exp (v h) / ∑ k, Real.exp (v k) = 1 := by
  rw [← sum_div, div_self (sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty).ne']

/-- The logit probabilities are continuous in the values (the smoothing of Method 3: a small
change in values never makes a choice probability jump). -/
theorem ev_logit_continuous {ι : Type*} [Fintype ι] [Nonempty ι] (h : ι) :
    Continuous fun v : ι → ℝ => Real.exp (v h) / ∑ k, Real.exp (v k) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun v => ?_
  exact (sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty).ne'

/-- AKMM, p. 900: with the default option (`none`) and the debt choices (`some h`) as
alternatives, the borrowing probabilities conditional on repayment,
`P(some h)/(1 − P(none))`, are logit over the debt choices. -/
theorem ev_conditional_borrow {ι : Type*} [Fintype ι] [Nonempty ι] (vD : ℝ) (W : ι → ℝ)
    (h : ι) :
    let v : Option ι → ℝ := fun o => o.elim vD W
    (Real.exp (v (some h)) / ∑ k, Real.exp (v k)) /
        (1 - Real.exp (v none) / ∑ k, Real.exp (v k)) =
      Real.exp (W h) / ∑ k, Real.exp (W k) := by
  intro v
  have hsum : ∑ k, Real.exp (v k) = Real.exp vD + ∑ k, Real.exp (W k) := by
    rw [Fintype.sum_option]
    rfl
  have hW : 0 < ∑ k, Real.exp (W k) := sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty
  have hT : 0 < Real.exp vD + ∑ k, Real.exp (W k) := add_pos (Real.exp_pos _) hW
  rw [hsum]
  change (Real.exp (W h) / _) / (1 - Real.exp vD / _) = _
  rw [show 1 - Real.exp vD / (Real.exp vD + ∑ k, Real.exp (W k)) =
      (∑ k, Real.exp (W k)) / (Real.exp vD + ∑ k, Real.exp (W k)) by field_simp; ring,
    div_div_div_cancel_right₀ hT.ne']

/-- **AKMM, (24.A.6)**, p. 900, with logit probabilities: if the default probability is
`e^{V^D}/(e^{V^D} + Σ_h e^{W_h})` and the borrowing probabilities are `e^{W_h}/Σ e^{W}`
(values `VDv`, `Wv` at each state), the bond price exists, is unique and lies in
`[0, δ/(δ + r)]`. -/
theorem eq_24_A_6_logit {Bd Y : Type*} [Fintype Bd] [Fintype Y] [Nonempty Bd]
    {P : Matrix Y Y ℝ} (hP : SargentStachurski.RecursiveDecisionProcesses.IsMarkov P)
    {r δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : -1 < r) (hδr : 0 < δ + r)
    (VDv : Bd → Y → ℝ) (Wv : Bd → Y → Bd → ℝ) :
    ∃! q : Bd → Y → ℝ, Function.IsFixedPt (bp_op P r δ
        (fun m j => Real.exp (VDv m j) / (Real.exp (VDv m j) + ∑ k, Real.exp (Wv m j k)))
        (fun m j h => Real.exp (Wv m j h) / ∑ k, Real.exp (Wv m j k))) q ∧
      ∀ m y, 0 ≤ q m y ∧ q m y ≤ δ / (δ + r) := by
  refine eq_24_A_6 ⟨hP, fun m j => ?_, fun m j => ?_, fun m j h => (ev_logit_pos _ h).le,
    fun m j => ev_logit_sum _, hδ0, hδ1, hr, hδr⟩
  · exact div_nonneg (Real.exp_pos _).le (add_pos (Real.exp_pos _)
      (sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty)).le
  · rw [div_le_one (add_pos (Real.exp_pos _) (sum_pos (fun _ _ => Real.exp_pos _)
      univ_nonempty))]
    exact le_add_of_nonneg_right (sum_nonneg fun _ _ => (Real.exp_pos _).le)

end AKMM.SovereignDefault

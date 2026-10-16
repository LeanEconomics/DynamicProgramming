/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.CurrencyPolicy

/-!
# The pure currency economy: counterexamples to Exercise 13.5(d) and 13.5(e)

SLP §13.5, Exercise 13.5(d), (e), (f), pp. 399–400. The example of the NOTE on part (d):
`U(c, z) = z(1 − e^{−c})` (`currencyCexU`) on `ℝ₊ × [z̲, 1]`, `0 < z̲ ≤ 1`.

* `currencyCex_hyp`, `currencyCex_diffHyp`, `currencyCex_increasingDiff`: every assumption of
  §13.5 holds (bounded, smooth, strictly increasing and strictly concave in `c`,
  `U₁(c, z) = z e^{−c}` strictly increasing in `z`).
* `currencyCex_v_increment`, `currencyCex_W_increment`: the deviation bound "keep `m′`, consume
  `d` more", `v(x + d, z) − v(x, z) ≥ z e^{−x}(1 − e^{−d})`, hence
  `W(x + d) − W(x) ≥ e^{−x}(1 − e^{−d}) ∫ z dμ`. No derivative of `v` is needed.

**Correction 1** (Exercise 13.5(d), p. 399; `ex_13_5d_counterexample`,
`ex_13_5d_counterexample_uniform`). "For each `z` there is `φ(z) > 0` with `g(·, z) = y` on
`[0, φ(z)]`" is false: if `z̲ < βe^{−y} ∫ z dμ` (for `μ` uniform on `[z̲, 1]` this follows from
`z̲ < βe^{−y}/2`, `currencyCex_uniform`), then `g(m, z̲) > y` for every `m > 0`. Spending
nothing instead of everything gains `β[W(y + m) − W(y)] − U(m, z̲) ≥ (1 − e^{−m})(βe^{−y}∫ z dμ −
z̲) > 0`. This confirms the NOTE in ch13.md. Corrected statement: `ex_13_5d_corrected`.

**Correction 2** (Exercise 13.5(e), p. 400; new; `ex_13_5e_counterexample`). In the same
example, `g(m, z̲) = m + y` (the household consumes nothing) for
`0 ≤ m ≤ m* = log(βe^{−y} ∫ z dμ / z̲) > 0`. So `c(·, z̲)` is not strictly increasing and
`g(m₂, z̲) − g(m₁, z̲) = m₂ − m₁` on `[0, m*]`, against `g(m₂, z) − g(m₁, z) < m₂ − m₁`. The
manual's proof uses the first-order condition with equality, which fails at the corner `c = 0`.
Corrected statement: `ex_13_5e_corrected`. The NOTE's remark that "the Markov analysis only uses
`φ(z̄) ≥ y` and the slopes" is therefore not enough: the slopes fail too; part (i) is proved
without them (`CurrencyMarkov.lean`, `CurrencyStationary.lean`).

**Correction 3** (solutions manual, Exercise 13.5(f); `ex_13_5f_mbar_eq_y`). With `β ≤ z̲`,
`g(y, z̲) = y`: `m̄ = y`, `X = {y}` and `λ* = δ_y`. The manual's step "`U₁(y, z̲) <
β∫v₁(y, ·)dμ`, since if not, `g(m, z) = y` for all `m` and `z`" is false. The book's claim
(`m̄ > 0`) survives, with `m̄ ≥ y` (`ex_13_5f`).

* The uniform distribution on `[a, b]` (`currencyUniform`): a probability measure
  (`isProbabilityMeasure_currencyUniform`) with `μ((a′, b′]) = (b′ − a′)/(b − a)`
  (`currencyUniform_density`) and mean `(a + b)/2` (`integral_currencyUniform`).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- The utility of the counterexample: `U(c, z) = z(1 − e^{−c})`. -/
noncomputable def currencyCexU (c z : ℝ) : ℝ := z * cexU c

/-- `1 − e⁰ = 0`. -/
theorem currency_cexU_zero : cexU 0 = 0 := by simp [cexU]

/-- `U(c, z) = z(1 − e^{−c})` on `ℝ₊ × [z̲, z̄]` with `0 < z̲` satisfies all the hypotheses of
§13.5: it is bounded, continuous (indeed smooth), strictly increasing and strictly concave in
`c`. -/
theorem currencyCex_hyp {β y zl zh : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hzl : 0 < zl)
    (hz : zl ≤ zh) : CurrencyHyp currencyCexU β y zl zh where
  β_pos := hβ0
  β_lt := hβ1
  y_pos := hy
  hz := hz
  U_cont := (continuous_snd.mul (continuous_const.sub
    (Real.continuous_exp.comp continuous_fst.neg))).continuousOn
  U_bdd := ⟨zh, fun c hc z hz' => by
    have h1 : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 : 0 < Real.exp (-c) := Real.exp_pos _
    have hz0 : 0 ≤ z := by linarith [hz'.1]
    simp only [currencyCexU, cexU]
    rw [abs_of_nonneg (mul_nonneg hz0 (by linarith))]
    nlinarith [hz'.2]⟩
  U_mono := fun z hz' c _ c' _ hcc' => by
    have hz0 : 0 < z := by linarith [hz'.1]
    have := Real.exp_lt_exp.2 (neg_lt_neg hcc')
    simp only [currencyCexU, cexU]
    nlinarith
  U_conc := fun z hz' => by
    have hz0 : 0 < z := by linarith [hz'.1]
    refine ⟨convex_Ici 0, fun x hx x' hx' hne a b ha hb hab => ?_⟩
    have := cexU_strictConcave.2 hx hx' hne ha hb hab
    simp only [smul_eq_mul, currencyCexU] at this ⊢
    nlinarith [mul_lt_mul_of_pos_left this hz0]

/-- `U₁(c, z) = z e^{−c}` is strictly increasing in `z`, in difference form. -/
theorem currencyCex_increasingDiff {zl zh : ℝ} : CurrencyIncreasingDiff currencyCexU zl zh := by
  intro c c' _ hcc' z z' _ hzz' _
  have := Real.exp_lt_exp.2 (neg_lt_neg hcc')
  simp only [currencyCexU, cexU]
  nlinarith

/-- `U(c, z) = z(1 − e^{−c})` is differentiable in `c` with `U₁(c, z) = z e^{−c}`, strictly
increasing in `z`: the differentiability hypotheses of §13.5 hold as well. -/
theorem currencyCex_diffHyp {zl zh : ℝ} :
    CurrencyDiffHyp currencyCexU (fun c z => z * Real.exp (-c)) zl zh where
  deriv := fun z _ c _ => by
    have h1 := ((hasDerivAt_neg c).exp.const_sub 1).const_mul z
    have e : (fun c => currencyCexU c z) = fun x => z * (1 - Real.exp (-x)) := by
      funext x; simp [currencyCexU, cexU]
    rw [e]
    convert h1 using 1
    ring
  mono := fun c _ z₁ _ z₂ _ h => mul_lt_mul_of_pos_right h (Real.exp_pos _)

variable {β y zl zh : ℝ} (μ : Measure (Icc zl zh)) [IsProbabilityMeasure μ]

/-- **The deviation bound.** With `U(c, z) = z(1 − e^{−c})`: at `x + d` the household can keep
the end-of-period balances chosen at `x` and consume `d` more, so
`v(x + d, z) − v(x, z) ≥ U(c + d, z) − U(c, z) = z e^{−c}(1 − e^{−d}) ≥ z e^{−x}(1 − e^{−d})`,
where `c = c(x, z) ≤ x`. -/
theorem currencyCex_v_increment (h : CurrencyHyp currencyCexU β y zl zh) (hzl : 0 ≤ zl)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ currencyCexU β y) (cash_boundedDP h μ) v = v) (x : Ici (0 : ℝ))
    {d : ℝ} (hd : 0 ≤ d) (z : Icc zl zh) :
    (z : ℝ) * Real.exp (-(x : ℝ)) * (1 - Real.exp (-d)) ≤
      v (⟨(x : ℝ) + d, mem_Ici.2 (add_nonneg x.2 hd)⟩, z) - v (x, z) := by
  obtain ⟨a1, a2, e1, -⟩ := cashPolicy_spec μ h hv (x, z)
  obtain ⟨-, -, -, o2⟩ := cashPolicy_spec μ h hv
    (⟨(x : ℝ) + d, mem_Ici.2 (add_nonneg x.2 hd)⟩, z)
  dsimp only at a2 e1 o2
  set g := (cashPolicy μ currencyCexU β y v (x, z) : ℝ)
  have i2 := o2 g a1 (by linarith)
  have q : (x : ℝ) + d + y - g = ((x : ℝ) + y - g) + d := by ring
  rw [q] at i2
  set c := (x : ℝ) + y - g
  have hcx : c ≤ x := by simp only [c]; linarith
  have hz0 : 0 ≤ (z : ℝ) := hzl.trans z.2.1
  simp only [currencyCexU, cexU] at e1 i2
  rw [show -(c + d) = -c + -d by ring, Real.exp_add] at i2
  have he : Real.exp (-(x : ℝ)) ≤ Real.exp (-c) := Real.exp_le_exp.2 (by linarith)
  have hd1 : 0 ≤ 1 - Real.exp (-d) := by
    have := Real.exp_le_one_iff.2 (by linarith : -d ≤ 0)
    linarith
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hd1) hz0
  nlinarith

/-- Integrating the deviation bound: `W(x + d) − W(x) ≥ e^{−x}(1 − e^{−d}) ∫ z′ μ(dz′)`. -/
theorem currencyCex_W_increment (h : CurrencyHyp currencyCexU β y zl zh) (hzl : 0 ≤ zl)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ currencyCexU β y) (cash_boundedDP h μ) v = v) {x d : ℝ}
    (hx : 0 ≤ x) (hd : 0 ≤ d) :
    Real.exp (-x) * (1 - Real.exp (-d)) * ∫ z, (z : ℝ) ∂μ ≤
      cashW μ v (x + d) - cashW μ v x := by
  have hint := integrable_section_v μ v
  have hcoe : Integrable (fun z : Icc zl zh => (z : ℝ)) μ :=
    integrable_of_bounded measurable_subtype_coe (M := |zl| + |zh|) fun z => by
      rw [abs_le]
      constructor <;> linarith [z.2.1, z.2.2, neg_abs_le zl, le_abs_self zh, abs_nonneg zl,
        abs_nonneg zh]
  rw [show cashW μ v (x + d) = cashW μ v
      ((⟨x + d, mem_Ici.2 (add_nonneg hx hd)⟩ : Ici (0 : ℝ)) : ℝ) from rfl,
    show cashW μ v x = cashW μ v ((⟨x, mem_Ici.2 hx⟩ : Ici (0 : ℝ)) : ℝ) from rfl,
    cashW_of_mem, cashW_of_mem, ← integral_sub (hint _) (hint _), ← integral_const_mul]
  refine integral_mono (hcoe.const_mul _) ((hint _).sub (hint _)) fun z => ?_
  have := currencyCex_v_increment μ h hzl hv ⟨x, mem_Ici.2 hx⟩ hd z
  dsimp only at this ⊢
  linarith

/-- **Exercise 13.5(d) is false** (the NOTE on p. 399). Take `U(c, z) = z(1 − e^{−c})` on
`ℝ₊ × [z̲, 1]`, `0 < z̲ ≤ 1`, and any shock distribution `μ` with `z̲ < βe^{−y} ∫ z μ(dz)` (for `μ`
uniform this is implied by `z̲ < βe^{−y}/2`: `currencyCex_uniform`). All the assumptions of §13.5
hold (`currencyCex_hyp`, `currencyCex_increasingDiff`), but at `z̲` the household never spends all
its money: `g(m, z̲) > y` for every `m > 0`, so there is no `φ(z̲) > 0` with `g(·, z̲) = y` on
`[0, φ(z̲)]`. Proof: spending nothing instead of everything gains
`β[W(y + m) − W(y)] − U(m, z̲) ≥ (1 − e^{−m})(βe^{−y} ∫ z dμ − z̲) > 0`. -/
theorem ex_13_5d_counterexample {β y zl : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y)
    (hzl : 0 < zl) (hzl1 : zl ≤ 1) (μ : Measure (Icc zl 1)) [IsProbabilityMeasure μ]
    (hsmall : zl < β * Real.exp (-y) * ∫ z, (z : ℝ) ∂μ) :
    ∃ v : Ici (0 : ℝ) × Icc zl 1 →ᵇ ℝ,
      bellman (cashModel μ currencyCexU β y)
        (cash_boundedDP (currencyCex_hyp hβ0 hβ1 hy hzl hzl1) μ) v = v ∧
      (∀ m : Ici (0 : ℝ), 0 < (m : ℝ) →
        y < cashPolicy μ currencyCexU β y v (m, ⟨zl, le_rfl, hzl1⟩)) ∧
      ¬ ∃ φ : ℝ, 0 < φ ∧ ∀ m : Ici (0 : ℝ), (m : ℝ) ≤ φ →
        (cashPolicy μ currencyCexU β y v (m, ⟨zl, le_rfl, hzl1⟩) : ℝ) = y := by
  set h := currencyCex_hyp hβ0 hβ1 hy hzl hzl1
  obtain ⟨v, hv, -, -⟩ := ex_13_5a h μ
  set zL : Icc zl 1 := ⟨zl, le_rfl, hzl1⟩
  have hmain : ∀ m : Ici (0 : ℝ), 0 < (m : ℝ) →
      y < cashPolicy μ currencyCexU β y v (m, zL) := by
    intro m hm
    by_contra hle
    push Not at hle
    obtain ⟨a1, -, e1, o1⟩ := cashPolicy_spec μ h hv (m, zL)
    dsimp only at e1 o1
    have hg : (cashPolicy μ currencyCexU β y v (m, zL) : ℝ) = y := le_antisymm hle a1
    rw [hg] at e1
    have i1 := o1 ((m : ℝ) + y) (by linarith) le_rfl
    rw [show (m : ℝ) + y - ((m : ℝ) + y) = 0 by ring, show (m : ℝ) + y - y = m by ring] at *
    have hW := currencyCex_W_increment μ h hzl.le hv hy.le (le_of_lt hm)
    rw [show y + (m : ℝ) = (m : ℝ) + y by ring] at hW
    have hzz : ((zL : Icc zl 1) : ℝ) = zl := rfl
    rw [hzz] at e1 i1
    simp only [currencyCexU, currency_cexU_zero, mul_zero, zero_add] at e1 i1
    simp only [cexU] at e1
    have hm1 : 0 < 1 - Real.exp (-(m : ℝ)) := by
      have := Real.exp_lt_exp.2 (by linarith : -(m : ℝ) < 0)
      rw [Real.exp_zero] at this
      linarith
    have hkey := mul_lt_mul_of_pos_left hsmall hm1
    nlinarith [mul_le_mul_of_nonneg_left hW hβ0.le]
  refine ⟨v, hv, hmain, ?_⟩
  rintro ⟨φ, hφ, hφg⟩
  have := hmain ⟨φ, mem_Ici.2 hφ.le⟩ hφ
  rw [hφg ⟨φ, mem_Ici.2 hφ.le⟩ le_rfl] at this
  exact lt_irrefl _ this

/-- **Exercise 13.5(e) is false** in the same example. For `m ≤ m* = log(βe^{−y}∫ z dμ / z̲) > 0`,
the household at `z̲` consumes nothing: `g(m, z̲) = m + y`. So `c(·, z̲) = 0` on `[0, m*]` is not
strictly increasing, and `g(m₂, z̲) − g(m₁, z̲) = m₂ − m₁` there, against
`g(m₂, z) − g(m₁, z) < m₂ − m₁`. Proof: for `d ∈ [0, m]`, consuming `d` instead of `0` loses
`β[W(m + y) − W(m + y − d)] − z̲(1 − e^{−d}) ≥ (1 − e^{−d})(βe^{−(m+y)}∫ z dμ − z̲) ≥ 0`. -/
theorem ex_13_5e_counterexample {β y zl : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y)
    (hzl : 0 < zl) (hzl1 : zl ≤ 1) (μ : Measure (Icc zl 1)) [IsProbabilityMeasure μ]
    (hsmall : zl < β * Real.exp (-y) * ∫ z, (z : ℝ) ∂μ) :
    ∃ v : Ici (0 : ℝ) × Icc zl 1 →ᵇ ℝ,
      bellman (cashModel μ currencyCexU β y)
        (cash_boundedDP (currencyCex_hyp hβ0 hβ1 hy hzl hzl1) μ) v = v ∧
      ∃ mstar : ℝ, 0 < mstar ∧
        (∀ m : Ici (0 : ℝ), (m : ℝ) ≤ mstar →
          (cashPolicy μ currencyCexU β y v (m, ⟨zl, le_rfl, hzl1⟩) : ℝ) = m + y) ∧
        (¬ ∀ m₁ m₂ : Ici (0 : ℝ), m₁ < m₂ →
          (cashPolicy μ currencyCexU β y v (m₂, ⟨zl, le_rfl, hzl1⟩) : ℝ) -
            cashPolicy μ currencyCexU β y v (m₁, ⟨zl, le_rfl, hzl1⟩) < (m₂ : ℝ) - m₁) ∧
        ¬ StrictMono fun m : Ici (0 : ℝ) =>
          (m : ℝ) + y - cashPolicy μ currencyCexU β y v (m, ⟨zl, le_rfl, hzl1⟩) := by
  set h := currencyCex_hyp hβ0 hβ1 hy hzl hzl1
  obtain ⟨v, hv, -, -⟩ := ex_13_5a h μ
  set zL : Icc zl 1 := ⟨zl, le_rfl, hzl1⟩
  set E := ∫ z, (z : ℝ) ∂μ
  have hK : 0 < β * Real.exp (-y) * E := hzl.trans hsmall
  set mstar := Real.log (β * Real.exp (-y) * E / zl)
  have hratio : 1 < β * Real.exp (-y) * E / zl := (one_lt_div hzl).2 hsmall
  have hmstar : 0 < mstar := Real.log_pos hratio
  have hexp : Real.exp (-mstar) = zl / (β * Real.exp (-y) * E) := by
    rw [Real.exp_neg, Real.exp_log (by linarith), inv_div]
  have hcorner : ∀ m : Ici (0 : ℝ), (m : ℝ) ≤ mstar →
      (cashPolicy μ currencyCexU β y v (m, zL) : ℝ) = m + y := by
    intro m hm
    refine cashPolicy_eq_of_ge μ h hv (m, zL) (by linarith [m.2.out]) le_rfl ?_
    obtain ⟨a1, a2, e1, -⟩ := cashPolicy_spec μ h hv (m, zL)
    dsimp only at a2 e1 ⊢
    rw [e1]
    set g := (cashPolicy μ currencyCexU β y v (m, zL) : ℝ)
    set d := (m : ℝ) + y - g
    have hd0 : 0 ≤ d := by simp only [d]; linarith
    have hg0 : 0 ≤ g := by linarith
    have hW := currencyCex_W_increment μ h hzl.le hv hg0 hd0
    rw [show g + d = (m : ℝ) + y by simp only [d]; ring] at hW
    have hzz : ((zL : Icc zl 1) : ℝ) = zl := rfl
    rw [hzz, show (m : ℝ) + y - ((m : ℝ) + y) = 0 by ring]
    simp only [currencyCexU, currency_cexU_zero, mul_zero, zero_add]
    simp only [cexU]
    have hd1 : 0 ≤ 1 - Real.exp (-d) := by
      have := Real.exp_le_one_iff.2 (by linarith : -d ≤ 0)
      linarith
    -- `e^{−g} ≥ e^{−(m + y)} ≥ e^{−m*} e^{−y}`
    have he1 : Real.exp (-((m : ℝ) + y)) ≤ Real.exp (-g) := Real.exp_le_exp.2 (by linarith)
    have he2 : Real.exp (-mstar) * Real.exp (-y) ≤ Real.exp (-((m : ℝ) + y)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    rw [hexp] at he2
    have hE0 : 0 < E := by
      by_contra hneg
      push Not at hneg
      have : β * Real.exp (-y) * E ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_pos hβ0 (Real.exp_pos _)).le hneg
      linarith
    have hzle : zl ≤ β * Real.exp (-g) * E := by
      have hy' := Real.exp_pos (-y)
      have h3 : zl / (β * Real.exp (-y) * E) * Real.exp (-y) * (β * E) = zl := by
        field_simp
      have h4 : zl / (β * Real.exp (-y) * E) * Real.exp (-y) ≤ Real.exp (-g) := he2.trans he1
      have h5 := mul_le_mul_of_nonneg_right h4 (mul_nonneg hβ0.le hE0.le)
      nlinarith
    have := mul_le_mul_of_nonneg_left hW hβ0.le
    nlinarith [mul_le_mul_of_nonneg_right hzle hd1]
  refine ⟨v, hv, mstar, hmstar, hcorner, fun hs => ?_, fun hsm => ?_⟩
  · have := hs ⟨0, mem_Ici.2 le_rfl⟩ ⟨mstar, mem_Ici.2 hmstar.le⟩ hmstar
    rw [hcorner ⟨mstar, mem_Ici.2 hmstar.le⟩ le_rfl,
      hcorner ⟨0, mem_Ici.2 le_rfl⟩ hmstar.le] at this
    change mstar + y - (0 + y) < mstar - 0 at this
    linarith
  · have := hsm (show (⟨0, mem_Ici.2 le_rfl⟩ : Ici (0 : ℝ)) < ⟨mstar, mem_Ici.2 hmstar.le⟩
      from hmstar)
    dsimp only at this
    rw [hcorner ⟨mstar, mem_Ici.2 hmstar.le⟩ le_rfl,
      hcorner ⟨0, mem_Ici.2 le_rfl⟩ hmstar.le] at this
    change (0 : ℝ) + y - (0 + y) < mstar + y - (mstar + y) at this
    linarith

/-! ### The top of the ergodic set can be `y` -/

/-- **`m̄ = y` can occur** (the remark on part (f); against the solutions manual's step
"`U₁(y, z̲) < β∫v₁(y, ·)dμ`, since if not, `g(m, z) = y` for all `m` and `z`"). With
`U(c, z) = z(1 − e^{−c})` on `[z̲, 1]` and `β ≤ z̲`, the household spends everything at `(y, z̲)`:
`g(y, z̲) = y`, because `βW′(y) ≤ βU₁(y, 1) = βe^{−y} ≤ z̲e^{−y} = U₁(y, z̲)`. So `y` is the
smallest fixed point `m̄` of `g(·, z̲)` in `[y, ∞)`, `X = [y, m̄] = {y}` and `λ* = δ_y`. Part (f)
itself (a fixed point `m̄ > 0`) remains true (`ex_13_5f`, with `m̄ ≥ y > 0`). -/
theorem ex_13_5f_mbar_eq_y {β y zl : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y)
    (hzl : 0 < zl) (hzl1 : zl ≤ 1) (hβzl : β ≤ zl) (μ : Measure (Icc zl 1))
    [IsProbabilityMeasure μ] {v : Ici (0 : ℝ) × Icc zl 1 →ᵇ ℝ}
    (hv : bellman (cashModel μ currencyCexU β y)
      (cash_boundedDP (currencyCex_hyp hβ0 hβ1 hy hzl hzl1) μ) v = v) :
    (cashPolicy μ currencyCexU β y v (⟨y, mem_Ici.2 hy.le⟩, ⟨zl, le_rfl, hzl1⟩) : ℝ) = y := by
  set h := currencyCex_hyp hβ0 hβ1 hy hzl hzl1
  have hd := currencyCex_diffHyp (zl := zl) (zh := 1)
  refine cash_spend_all μ h hd hv _ hy ?_
  have hK := cashW_deriv_le μ h hd hv
  have hK0 := cashW_deriv_pos μ h hd hv hy
  change β * cvDerivR (cashW μ v) y ≤ zl * Real.exp (-y)
  change cvDerivR (cashW μ v) y ≤ 1 * Real.exp (-y) at hK
  have he := Real.exp_pos (-y)
  nlinarith

/-! ### The uniform distribution -/

/-- The uniform distribution on `[a, b]`, as a measure on the subtype. -/
noncomputable def currencyUniform (a b : ℝ) : Measure (Icc a b) :=
  (ENNReal.ofReal (b - a))⁻¹ • Measure.comap Subtype.val volume

/-- `μ(A) = λ(A)/(b − a)` for the uniform distribution. -/
theorem currencyUniform_apply {a b : ℝ} (A : Set (Icc a b)) :
    currencyUniform a b A = (ENNReal.ofReal (b - a))⁻¹ * volume (Subtype.val '' A) := by
  rw [currencyUniform, Measure.smul_apply, comap_subtype_coe_apply measurableSet_Icc, smul_eq_mul]

/-- The uniform distribution is a probability measure. -/
theorem isProbabilityMeasure_currencyUniform {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (currencyUniform a b) := by
  refine ⟨?_⟩
  rw [currencyUniform_apply, image_univ, Subtype.range_coe, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by simp [hab]) ENNReal.ofReal_ne_top

/-- The uniform distribution satisfies the density condition with `α = 1/(b − a)`:
`μ((a′, b′]) = (b′ − a′)/(b − a)`. -/
theorem currencyUniform_density {a b : ℝ} (hab : a < b) :
    CurrencyDensity (currencyUniform a b) (1 / (b - a)) := by
  have hba : 0 < b - a := by linarith
  refine ⟨by positivity, fun a' b' ha' hab' hb' => le_of_eq ?_⟩
  have himg : Subtype.val '' {z : Icc a b | a' < (z : ℝ) ∧ (z : ℝ) ≤ b'} = Ioc a' b' := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, by linarith [hx.1], by linarith [hx.2]⟩, hx, rfl⟩
  rw [measureReal_def, currencyUniform_apply, himg, Real.volume_Ioc, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  ring

/-- `∫ z dμ = (a + b)/2` for the uniform distribution. -/
theorem integral_currencyUniform {a b : ℝ} (hab : a < b) :
    ∫ z, (z : ℝ) ∂currencyUniform a b = (a + b) / 2 := by
  rw [currencyUniform, integral_smul_measure, integral_subtype_comap measurableSet_Icc (fun x => x),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le, integral_id,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
  have : b - a ≠ 0 := by linarith
  field_simp
  ring

/-- **The NOTE's instance.** With `μ` uniform on `[z̲, 1]`, `0 < z̲ < 1` and `z̲ < βe^{−y}/2`, the
hypotheses of `ex_13_5d_counterexample` and `ex_13_5e_counterexample` hold: `μ` is a probability
measure satisfying the density condition `μ((a, b]) = (b − a)/(1 − z̲)`, and
`z̲ < βe^{−y} ∫ z dμ = βe^{−y}(1 + z̲)/2`. -/
theorem currencyCex_uniform {β y zl : ℝ} (hβ0 : 0 < β) (hzl : 0 < zl) (hzl1 : zl < 1)
    (hsmall : zl < β * Real.exp (-y) / 2) :
    IsProbabilityMeasure (currencyUniform zl 1) ∧
      CurrencyDensity (currencyUniform zl 1) (1 / (1 - zl))
      ∧ zl < β * Real.exp (-y) * ∫ z, (z : ℝ) ∂currencyUniform zl 1 := by
  refine ⟨isProbabilityMeasure_currencyUniform hzl1, currencyUniform_density hzl1, ?_⟩
  rw [integral_currencyUniform hzl1]
  have : 0 < β * Real.exp (-y) := mul_pos hβ0 (Real.exp_pos _)
  nlinarith

/-- **The NOTE's counterexample to Exercise 13.5(d), exactly.** `U(c, z) = z(1 − e^{−c})` on
`ℝ₊ × [z̲, 1]`, `μ` uniform on `[z̲, 1]` (which satisfies the density condition),
`0 < z̲ < 1`, `z̲ < βe^{−y}/2`: the value function exists and at `z̲` the household never spends all
its money, `g(m, z̲) > y` for all `m > 0`, so no `φ(z̲) > 0` exists. -/
theorem ex_13_5d_counterexample_uniform {β y zl : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y)
    (hzl : 0 < zl) (hzl1 : zl < 1) (hsmall : zl < β * Real.exp (-y) / 2) :
    ∃ _ : IsProbabilityMeasure (currencyUniform zl 1),
      CurrencyDensity (currencyUniform zl 1) (1 / (1 - zl)) ∧
      ∃ v : Ici (0 : ℝ) × Icc zl 1 →ᵇ ℝ,
        bellman (cashModel (currencyUniform zl 1) currencyCexU β y)
          (cash_boundedDP (currencyCex_hyp hβ0 hβ1 hy hzl hzl1.le) (currencyUniform zl 1)) v = v ∧
        (∀ m : Ici (0 : ℝ), 0 < (m : ℝ) →
          y < cashPolicy (currencyUniform zl 1) currencyCexU β y v (m, ⟨zl, le_rfl, hzl1.le⟩)) ∧
        ¬ ∃ φ : ℝ, 0 < φ ∧ ∀ m : Ici (0 : ℝ), (m : ℝ) ≤ φ →
          (cashPolicy (currencyUniform zl 1) currencyCexU β y v
            (m, ⟨zl, le_rfl, hzl1.le⟩) : ℝ) = y := by
  obtain ⟨hP, hD, hE⟩ := currencyCex_uniform hβ0 hzl hzl1 hsmall
  exact ⟨hP, hD, ex_13_5d_counterexample hβ0 hβ1 hy hzl hzl1.le _ hE⟩

end StokeyLucasPrescott.ConvergenceApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.TighterLimitCounterexample

/-!
# A tighter limit can lower the MPC when `βR = 1` (CRRA with income risk)

AKMM, §11.3.4, p. 306: "their marginal propensity to consume … increases" when the credit limit
tightens. `TighterLimitCounterexample` refutes this two periods before the end for an impatient
CRRA household (`θ = 2`). Here it is refuted in the book's own case `βR = 1` (`θ = 1`), with log
utility, so patience does not rescue the claim for CRRA with income risk.

## The counterexample

Log utility (`σ = 1`, `M` the harmonic mean), `β = 1`, `R = 1` (so `βR = 1`, `θ = 1`), loose limit
`a₁ = 1/2`, tight limit `a₂ = 499/1000`, three incomes `503/1000`, `8/10`, `9/2` with probabilities
`1/10000`, `3/10`, `6999/10000`, and `d = 3/1000` (`ctb_H`, `ctb_valid`). Between cash in hand
`19778/15625` and `1278143/1000000` the loose household's consumption two periods before the end
rises by about `1.7·10⁻⁹` more than the tight one's (`ctb_counterexample`, `ctb_not_tight_mpc`).

A patient household fails too: `ctb_P` has log utility, `β = 1`, `R = 2` (so `βR = 2`,
`θ = 1/2`), `a₁ = 1/20`, `a₂ = 49/1000`, incomes `51/1000`, `35/100`, `81/20` with probabilities
`1/100000`, `3/10`, `69999/100000` (`ctb_P_valid`, `ctb_P_theta`), and between cash in hand
`5394/10000` and `5412/10000` the comparison fails by about `2·10⁻¹⁰` (`ctb_P_counterexample`,
`ctb_P_not_tight_mpc`). So no restriction on `βR` restores the claim for CRRA with risk.

With `θ ≤ 1` the top income state is never constrained next period, which rules out the
two-state mechanism of `ctc_H`. A middle state can still sit just past next period's kink while
the rare lowest state is constrained: the middle state's value-function prudence then carries the
risk of the rare state two periods ahead and is unboundedly large as that state's cash
approaches `0`, while the MPC stays bounded away from `0`.

The proof brackets the four consumption levels by the signs of Euler gaps at rational points
(`ctc_lt_step`, `ctc_step_lt`): next period's consumption is bracketed state by state
(`ctb_c1_gt`, `ctb_c1_lt`, and the limit `ctb_c1_le`), and those brackets bracket the current
consumption through the monotone harmonic mean (`ctb_cons2_gt`, `ctb_cons2_lt`).
-/

namespace AKMM.Consumption

open CfnHousehold

/-- The counterexample household with `βR = 1`: log utility, `β = 1`, `R = 1`, limit `a₁ = 1/2`,
incomes `503/1000`, `8/10`, `9/2` with probabilities `1/10000`, `3/10`, `6999/10000`. -/
noncomputable def ctb_H : CfnHousehold (Fin 3) :=
  cfn_crra 1 1 ![1 / 10000, 3 / 10, 6999 / 10000] ![503 / 1000, 8 / 10, 9 / 2] 1 (1 / 2)
    (3 / 1000) (9 / 2)

/-- The household satisfies the standing assumptions. -/
theorem ctb_valid : ctb_H.Valid := by
  refine cfn_crra_valid one_pos one_pos (fun i => ?_) ?_ le_rfl (by norm_num) (by norm_num)
    (fun i => ?_) (fun i => ?_)
  · fin_cases i <;> norm_num
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    norm_num
  · fin_cases i <;> norm_num
  · fin_cases i <;> norm_num

/-- For CRRA, `θ = (βR)^{−1/σ} = 1` here: `βR = 1`. -/
theorem ctb_theta : ctb_H.θ = 1 ∧ ctb_H.R = 1 := by
  simp only [ctb_H, cfn_crra]
  norm_num

/-- The household with a tighter limit `a₂ ∈ [0, 1/2]` satisfies the standing assumptions. -/
theorem ctb_tight_valid {b₂ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 2) : (ctb_H.tighten b₂).Valid :=
  cfn_tighten_valid ctb_valid h0 h2

/-- The Euler right-hand side is the harmonic mean of next period's consumptions. -/
theorem ctb_cont (b₂ : ℝ) (cn : ℝ → ℝ) (s : ℝ) :
    (ctb_H.tighten b₂).cont cn s = 1 / (1 / 10000 / cn (s + 503 / 1000) +
      3 / 10 / cn (s + 8 / 10) + 6999 / 10000 / cn (s + 9 / 2)) := by
  simp only [cont, CfnHousehold.tighten, ctb_H, cfn_crra, LeanEconomics.powerMean,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Real.rpow_neg_one, one_mul]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- A lower bracket on next period's consumption (one period before the end). -/
theorem ctb_c1_gt {b₂ z ℓ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 2) (hℓ : ℓ < z + b₂)
    (he : ℓ < 1 / (1 / 10000 / (z - ℓ + 503 / 1000) + 3 / 10 / (z - ℓ + 8 / 10) +
      6999 / 10000 / (z - ℓ + 9 / 2))) : ℓ < (ctb_H.tighten b₂).cons 1 z := by
  have hV := ctb_tight_valid h0 h2
  have hR : (ctb_H.tighten b₂).R = 1 := rfl
  have hb : (ctb_H.tighten b₂).b = b₂ := rfl
  change ℓ < (ctb_H.tighten b₂).step ((ctb_H.tighten b₂).cons 0) z
  refine ctc_lt_step hV (cfn_cons_good hV 0) (by rw [hR, hb, div_one]; exact hℓ) ?_
  rw [ctb_cont]
  simpa only [cons] using he

/-- An upper bracket on next period's consumption (one period before the end). -/
theorem ctb_c1_lt {b₂ z η : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 2)
    (he : 1 / (1 / 10000 / (z - η + 503 / 1000) + 3 / 10 / (z - η + 8 / 10) +
      6999 / 10000 / (z - η + 9 / 2)) < η) : (ctb_H.tighten b₂).cons 1 z < η := by
  have hV := ctb_tight_valid h0 h2
  change (ctb_H.tighten b₂).step ((ctb_H.tighten b₂).cons 0) z < η
  refine ctc_step_lt hV (cfn_cons_good hV 0) ?_
  rw [ctb_cont]
  simpa only [cons] using he

/-- Next period's consumption is at most its borrowing limit `z + a₂`. -/
theorem ctb_c1_le {b₂ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 2) (z : ℝ) :
    (ctb_H.tighten b₂).cons 1 z ≤ z + b₂ := by
  have h := (cfn_cons_kkt (ctb_tight_valid h0 h2) 0 z).1
  have hR : (ctb_H.tighten b₂).R = 1 := rfl
  have hb : (ctb_H.tighten b₂).b = b₂ := rfl
  rwa [hR, hb, div_one] at h

/-- The harmonic mean is monotone: lower bounds on the entries bound it below. -/
theorem ctb_harm_mono {a₁ a₂ a₃ ℓ₁ ℓ₂ ℓ₃ : ℝ} (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂) (h₃ : 0 < ℓ₃)
    (k₁ : ℓ₁ ≤ a₁) (k₂ : ℓ₂ ≤ a₂) (k₃ : ℓ₃ ≤ a₃) :
    1 / (1 / 10000 / ℓ₁ + 3 / 10 / ℓ₂ + 6999 / 10000 / ℓ₃) ≤
      1 / (1 / 10000 / a₁ + 3 / 10 / a₂ + 6999 / 10000 / a₃) := by
  have p : 0 < 1 / 10000 / a₁ + 3 / 10 / a₂ + 6999 / 10000 / a₃ := by
    have : 0 < a₁ := lt_of_lt_of_le h₁ k₁
    have : 0 < a₂ := lt_of_lt_of_le h₂ k₂
    have : 0 < a₃ := lt_of_lt_of_le h₃ k₃
    positivity
  refine one_div_le_one_div_of_le p ?_
  gcongr

/-- **A lower bound** on consumption two periods before the end from lower bounds on next
period's consumption in the three states. -/
theorem ctb_cons2_gt {b₂ x c ℓ₁ ℓ₂ ℓ₃ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 2) (hc : c < x + b₂)
    (p₁ : 0 < ℓ₁) (p₂ : 0 < ℓ₂) (p₃ : 0 < ℓ₃)
    (k₁ : ℓ₁ < (ctb_H.tighten b₂).cons 1 (x - c + 503 / 1000))
    (k₂ : ℓ₂ < (ctb_H.tighten b₂).cons 1 (x - c + 8 / 10))
    (k₃ : ℓ₃ < (ctb_H.tighten b₂).cons 1 (x - c + 9 / 2))
    (hm : c < 1 / (1 / 10000 / ℓ₁ + 3 / 10 / ℓ₂ + 6999 / 10000 / ℓ₃)) :
    c < (ctb_H.tighten b₂).cons 2 x := by
  have hV := ctb_tight_valid h0 h2
  have hR : (ctb_H.tighten b₂).R = 1 := rfl
  have hb : (ctb_H.tighten b₂).b = b₂ := rfl
  change c < (ctb_H.tighten b₂).step ((ctb_H.tighten b₂).cons 1) x
  refine ctc_lt_step hV (cfn_cons_good hV 1) (by rw [hR, hb, div_one]; exact hc) ?_
  rw [ctb_cont]
  exact lt_of_lt_of_le hm (ctb_harm_mono p₁ p₂ p₃ k₁.le k₂.le k₃.le)

/-- **An upper bound** on consumption two periods before the end from upper bounds on next
period's consumption in the three states. -/
theorem ctb_cons2_lt {b₂ x c η₁ η₂ η₃ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 2) (hc : c ≤ x + b₂)
    (k₁ : (ctb_H.tighten b₂).cons 1 (x - c + 503 / 1000) ≤ η₁)
    (k₂ : (ctb_H.tighten b₂).cons 1 (x - c + 8 / 10) ≤ η₂)
    (k₃ : (ctb_H.tighten b₂).cons 1 (x - c + 9 / 2) ≤ η₃)
    (hm : 1 / (1 / 10000 / η₁ + 3 / 10 / η₂ + 6999 / 10000 / η₃) < c) :
    (ctb_H.tighten b₂).cons 2 x < c := by
  have hV := ctb_tight_valid h0 h2
  have hd : (ctb_H.tighten b₂).d = 3 / 1000 := rfl
  change (ctb_H.tighten b₂).step ((ctb_H.tighten b₂).cons 1) x < c
  refine ctc_step_lt hV (cfn_cons_good hV 1) ?_
  rw [ctb_cont]
  have q₁ := (cfn_cons_good hV 1).1 (x - c + 503 / 1000) (by rw [hd]; linarith)
  have q₂ := (cfn_cons_good hV 1).1 (x - c + 8 / 10) (by rw [hd]; linarith)
  have q₃ := (cfn_cons_good hV 1).1 (x - c + 9 / 2) (by rw [hd]; linarith)
  exact lt_of_le_of_lt (ctb_harm_mono q₁ q₂ q₃ k₁ k₂ k₃) hm

/-- The loose household is the tightening to its own limit. -/
theorem ctb_tighten_self : ctb_H.tighten (1 / 2) = ctb_H := rfl

/-- **Counterexample to AKMM, p. 306, with `βR = 1`** (CRRA utility with income risk, two periods
before the end). Between cash in hand `19778/15625` and `1278143/1000000` the tight household
(`a₂ = 499/1000`) raises its consumption by less than the loose one (`a₁ = 1/2`). -/
theorem ctb_counterexample :
    (ctb_H.tighten (499 / 1000)).cons 2 (1278143 / 1000000) -
        (ctb_H.tighten (499 / 1000)).cons 2 (19778 / 15625)
      < ctb_H.cons 2 (1278143 / 1000000) - ctb_H.cons 2 (19778 / 15625) := by
  have hL1 : ctb_H.cons 2 (19778 / 15625) < 1728907476101 / 1000000000000 := by
    rw [← ctb_tighten_self]
    refine ctb_cons2_lt (η₂ := 20896495894631 / 25000000000000)
      (η₃ := 319147660580041 / 100000000000000) (by norm_num) le_rfl (by norm_num)
      (ctb_c1_le (by norm_num) le_rfl _) (ctb_c1_lt (by norm_num) le_rfl ?_).le
      (ctb_c1_lt (by norm_num) le_rfl ?_).le ?_ <;> norm_num
  have hL2 : 1735689480651 / 1000000000000 < ctb_H.cons 2 (1278143 / 1000000) := by
    rw [← ctb_tighten_self]
    refine ctb_cons2_gt (ℓ₁ := 54545351934899 / 100000000000000)
      (ℓ₂ := 84062985163003 / 100000000000000) (ℓ₃ := 159735204491643 / 50000000000000)
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ctb_c1_gt (by norm_num) le_rfl ?_ ?_) (ctb_c1_gt (by norm_num) le_rfl ?_ ?_)
      (ctb_c1_gt (by norm_num) le_rfl ?_ ?_) ?_ <;> norm_num
  have hT1 : 864453508301 / 500000000000 < (ctb_H.tighten (499 / 1000)).cons 2 (19778 / 15625) := by
    refine ctb_cons2_gt (ℓ₁ := 53888498339799 / 100000000000000)
      (ℓ₂ := 83586023527201 / 100000000000000) (ℓ₃ := 319147687212691 / 100000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ctb_c1_gt (by norm_num) (by norm_num) ?_ ?_) (ctb_c1_gt (by norm_num) (by norm_num) ?_ ?_)
      (ctb_c1_gt (by norm_num) (by norm_num) ?_ ?_) ?_ <;> norm_num
  have hT2 : (ctb_H.tighten (499 / 1000)).cons 2 (1278143 / 1000000) <
      1735689019481 / 1000000000000 := by
    refine ctb_cons2_lt (η₂ := 5253939004291 / 6250000000000)
      (η₃ := 319470435707549 / 100000000000000) (by norm_num) (by norm_num) (by norm_num)
      (ctb_c1_le (by norm_num) (by norm_num) _) (ctb_c1_lt (by norm_num) (by norm_num) ?_).le
      (ctb_c1_lt (by norm_num) (by norm_num) ?_).le ?_ <;> norm_num
  linarith

/-- **Correction to AKMM, p. 306, in the book's case `βR = 1`.** For CRRA utility with income
risk the MPC comparison fails two periods before the end even when `βR = 1` (`θ = 1`): for
`ctb_H` and `a₂ = 499/1000` the fall `c₂ − c̃₂` is not nonincreasing. -/
theorem ctb_not_tight_mpc :
    ¬ ∀ x x', ctb_H.d ≤ x → x ≤ x' →
      ctb_H.cons 2 x' - ctb_H.cons 2 x ≤
        (ctb_H.tighten (499 / 1000)).cons 2 x' - (ctb_H.tighten (499 / 1000)).cons 2 x := by
  intro h
  have := h (19778 / 15625) (1278143 / 1000000)
    (by change (3 : ℝ) / 1000 ≤ 19778 / 15625; norm_num) (by norm_num)
  linarith [ctb_counterexample]

/-! ### A patient household: `βR = 2` -/

/-- A patient counterexample household: log utility, `β = 1`, `R = 2` (so `βR = 2`, `θ = 1/2`),
limit `a₁ = 1/20`, incomes `51/1000`, `35/100`, `81/20` with probabilities `1/100000`, `3/10`,
`69999/100000`, `d = 1/1000`. -/
noncomputable def ctb_P : CfnHousehold (Fin 3) :=
  cfn_crra 1 1 ![1 / 100000, 3 / 10, 69999 / 100000] ![51 / 1000, 35 / 100, 81 / 20] 2 (1 / 20)
    (1 / 1000) (81 / 20)

/-- The patient household satisfies the standing assumptions. -/
theorem ctb_P_valid : ctb_P.Valid := by
  refine cfn_crra_valid one_pos one_pos (fun i => ?_) ?_ (by norm_num) (by norm_num)
    (by norm_num) (fun i => ?_) (fun i => ?_)
  · fin_cases i <;> norm_num
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    norm_num
  · fin_cases i <;> norm_num
  · fin_cases i <;> norm_num

/-- For the patient household `θ = (βR)^{−1/σ} = 1/2`: `βR = 2 > 1`. -/
theorem ctb_P_theta : ctb_P.θ = 1 / 2 ∧ ctb_P.R = 2 := by
  simp only [ctb_P, cfn_crra]
  norm_num [Real.rpow_neg_one]

/-- The patient household with a tighter limit `a₂ ∈ [0, 1/20]` satisfies the assumptions. -/
theorem ctb_P_tight_valid {b₂ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 20) :
    (ctb_P.tighten b₂).Valid :=
  cfn_tighten_valid ctb_P_valid h0 h2

/-- The patient household's Euler right-hand side: half the harmonic mean. -/
theorem ctb_P_cont (b₂ : ℝ) (cn : ℝ → ℝ) (s : ℝ) :
    (ctb_P.tighten b₂).cont cn s = 1 / 2 / (1 / 100000 / cn (2 * s + 51 / 1000) +
      3 / 10 / cn (2 * s + 35 / 100) + 69999 / 100000 / cn (2 * s + 81 / 20)) := by
  simp only [cont, CfnHousehold.tighten, ctb_P, cfn_crra, LeanEconomics.powerMean,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Real.rpow_neg_one, one_mul]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- A lower bracket on the patient household's next-period consumption. -/
theorem ctb_P_c1_gt {b₂ z ℓ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 20) (hℓ : ℓ < z + b₂ / 2)
    (he : ℓ < 1 / 2 / (1 / 100000 / (2 * (z - ℓ) + 51 / 1000) +
      3 / 10 / (2 * (z - ℓ) + 35 / 100) + 69999 / 100000 / (2 * (z - ℓ) + 81 / 20))) :
    ℓ < (ctb_P.tighten b₂).cons 1 z := by
  have hV := ctb_P_tight_valid h0 h2
  have hR : (ctb_P.tighten b₂).R = 2 := rfl
  have hb : (ctb_P.tighten b₂).b = b₂ := rfl
  change ℓ < (ctb_P.tighten b₂).step ((ctb_P.tighten b₂).cons 0) z
  refine ctc_lt_step hV (cfn_cons_good hV 0) (by rw [hR, hb]; exact hℓ) ?_
  rw [ctb_P_cont]
  simpa only [cons] using he

/-- An upper bracket on the patient household's next-period consumption. -/
theorem ctb_P_c1_lt {b₂ z η : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 20)
    (he : 1 / 2 / (1 / 100000 / (2 * (z - η) + 51 / 1000) +
      3 / 10 / (2 * (z - η) + 35 / 100) + 69999 / 100000 / (2 * (z - η) + 81 / 20)) < η) :
    (ctb_P.tighten b₂).cons 1 z < η := by
  have hV := ctb_P_tight_valid h0 h2
  change (ctb_P.tighten b₂).step ((ctb_P.tighten b₂).cons 0) z < η
  refine ctc_step_lt hV (cfn_cons_good hV 0) ?_
  rw [ctb_P_cont]
  simpa only [cons] using he

/-- The patient household's next-period consumption is at most `z + a₂/2`. -/
theorem ctb_P_c1_le {b₂ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 20) (z : ℝ) :
    (ctb_P.tighten b₂).cons 1 z ≤ z + b₂ / 2 := by
  have h := (cfn_cons_kkt (ctb_P_tight_valid h0 h2) 0 z).1
  have hR : (ctb_P.tighten b₂).R = 2 := rfl
  have hb : (ctb_P.tighten b₂).b = b₂ := rfl
  rwa [hR, hb] at h

/-- Half the harmonic mean with the patient household's weights is monotone. -/
theorem ctb_P_harm_mono {a₁ a₂ a₃ ℓ₁ ℓ₂ ℓ₃ : ℝ} (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂) (h₃ : 0 < ℓ₃)
    (k₁ : ℓ₁ ≤ a₁) (k₂ : ℓ₂ ≤ a₂) (k₃ : ℓ₃ ≤ a₃) :
    1 / 2 / (1 / 100000 / ℓ₁ + 3 / 10 / ℓ₂ + 69999 / 100000 / ℓ₃) ≤
      1 / 2 / (1 / 100000 / a₁ + 3 / 10 / a₂ + 69999 / 100000 / a₃) := by
  have p : 0 < 1 / 100000 / a₁ + 3 / 10 / a₂ + 69999 / 100000 / a₃ := by
    have : 0 < a₁ := lt_of_lt_of_le h₁ k₁
    have : 0 < a₂ := lt_of_lt_of_le h₂ k₂
    have : 0 < a₃ := lt_of_lt_of_le h₃ k₃
    positivity
  refine div_le_div_of_nonneg_left (by norm_num) p ?_
  gcongr

/-- **A lower bound** on the patient household's consumption two periods before the end. -/
theorem ctb_P_cons2_gt {b₂ x c ℓ₁ ℓ₂ ℓ₃ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 20)
    (hc : c < x + b₂ / 2) (p₁ : 0 < ℓ₁) (p₂ : 0 < ℓ₂) (p₃ : 0 < ℓ₃)
    (k₁ : ℓ₁ < (ctb_P.tighten b₂).cons 1 (2 * (x - c) + 51 / 1000))
    (k₂ : ℓ₂ < (ctb_P.tighten b₂).cons 1 (2 * (x - c) + 35 / 100))
    (k₃ : ℓ₃ < (ctb_P.tighten b₂).cons 1 (2 * (x - c) + 81 / 20))
    (hm : c < 1 / 2 / (1 / 100000 / ℓ₁ + 3 / 10 / ℓ₂ + 69999 / 100000 / ℓ₃)) :
    c < (ctb_P.tighten b₂).cons 2 x := by
  have hV := ctb_P_tight_valid h0 h2
  have hR : (ctb_P.tighten b₂).R = 2 := rfl
  have hb : (ctb_P.tighten b₂).b = b₂ := rfl
  change c < (ctb_P.tighten b₂).step ((ctb_P.tighten b₂).cons 1) x
  refine ctc_lt_step hV (cfn_cons_good hV 1) (by rw [hR, hb]; exact hc) ?_
  rw [ctb_P_cont]
  exact lt_of_lt_of_le hm (ctb_P_harm_mono p₁ p₂ p₃ k₁.le k₂.le k₃.le)

/-- **An upper bound** on the patient household's consumption two periods before the end. -/
theorem ctb_P_cons2_lt {b₂ x c η₁ η₂ η₃ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 1 / 20)
    (hc : c ≤ x + b₂ / 2)
    (k₁ : (ctb_P.tighten b₂).cons 1 (2 * (x - c) + 51 / 1000) ≤ η₁)
    (k₂ : (ctb_P.tighten b₂).cons 1 (2 * (x - c) + 35 / 100) ≤ η₂)
    (k₃ : (ctb_P.tighten b₂).cons 1 (2 * (x - c) + 81 / 20) ≤ η₃)
    (hm : 1 / 2 / (1 / 100000 / η₁ + 3 / 10 / η₂ + 69999 / 100000 / η₃) < c) :
    (ctb_P.tighten b₂).cons 2 x < c := by
  have hV := ctb_P_tight_valid h0 h2
  have hd : (ctb_P.tighten b₂).d = 1 / 1000 := rfl
  change (ctb_P.tighten b₂).step ((ctb_P.tighten b₂).cons 1) x < c
  refine ctc_step_lt hV (cfn_cons_good hV 1) ?_
  rw [ctb_P_cont]
  have q₁ := (cfn_cons_good hV 1).1 (2 * (x - c) + 51 / 1000) (by rw [hd]; linarith)
  have q₂ := (cfn_cons_good hV 1).1 (2 * (x - c) + 35 / 100) (by rw [hd]; linarith)
  have q₃ := (cfn_cons_good hV 1).1 (2 * (x - c) + 81 / 20) (by rw [hd]; linarith)
  exact lt_of_le_of_lt (ctb_P_harm_mono q₁ q₂ q₃ k₁ k₂ k₃) hm

/-- The patient loose household is the tightening to its own limit. -/
theorem ctb_P_tighten_self : ctb_P.tighten (1 / 20) = ctb_P := rfl

/-- **Counterexample to AKMM, p. 306, for a patient household** (`βR = 2`, CRRA with income
risk, two periods before the end). Between cash in hand `5394/10000` and `5412/10000` the tight
household (`a₂ = 49/1000`) raises its consumption by less than the loose one (`a₁ = 1/20`). -/
theorem ctb_P_counterexample :
    (ctb_P.tighten (49 / 1000)).cons 2 (5412 / 10000) -
        (ctb_P.tighten (49 / 1000)).cons 2 (5394 / 10000)
      < ctb_P.cons 2 (5412 / 10000) - ctb_P.cons 2 (5394 / 10000) := by
  have hL1 : ctb_P.cons 2 (5394 / 10000) < 2570301021797 / 5000000000000 := by
    rw [← ctb_P_tighten_self]
    refine ctb_P_cons2_lt (η₂ := 425133437921129 / 1000000000000000)
      (η₃ := 2622579372407809 / 1000000000000000) (by norm_num) le_rfl (by norm_num)
      (ctb_P_c1_le (by norm_num) le_rfl _) (ctb_P_c1_lt (by norm_num) le_rfl ?_).le
      (ctb_P_c1_lt (by norm_num) le_rfl ?_).le ?_ <;> norm_num
  have hL2 : 5151220345829 / 10000000000000 < ctb_P.cons 2 (5412 / 10000) := by
    rw [← ctb_P_tighten_self]
    refine ctb_P_cons2_gt (ℓ₁ := 128155930834199 / 1000000000000000)
      (ℓ₂ := 426295604228227 / 1000000000000000) (ℓ₃ := 2623368199956711 / 1000000000000000)
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ctb_P_c1_gt (by norm_num) le_rfl ?_ ?_) (ctb_P_c1_gt (by norm_num) le_rfl ?_ ?_)
      (ctb_P_c1_gt (by norm_num) le_rfl ?_ ?_) ?_ <;> norm_num
  have hT1 : 102812027469 / 200000000000 <
      (ctb_P.tighten (49 / 1000)).cons 2 (5394 / 10000) := by
    refine ctb_P_cons2_gt (ℓ₁ := 126179725309999 / 1000000000000000)
      (ℓ₂ := 425133545542351 / 1000000000000000) (ℓ₃ := 655644861005621 / 250000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (ctb_P_c1_gt (by norm_num) (by norm_num) ?_ ?_)
      (ctb_P_c1_gt (by norm_num) (by norm_num) ?_ ?_)
      (ctb_P_c1_gt (by norm_num) (by norm_num) ?_ ?_) ?_ <;> norm_num
  have hT2 : (ctb_P.tighten (49 / 1000)).cons 2 (5412 / 10000) <
      5151219673691 / 10000000000000 := by
    refine ctb_P_cons2_lt (η₂ := 426295708168461 / 1000000000000000)
      (η₃ := 2623368271781801 / 1000000000000000) (by norm_num) (by norm_num) (by norm_num)
      (ctb_P_c1_le (by norm_num) (by norm_num) _)
      (ctb_P_c1_lt (by norm_num) (by norm_num) ?_).le
      (ctb_P_c1_lt (by norm_num) (by norm_num) ?_).le ?_ <;> norm_num
  linarith

/-- **Correction to AKMM, p. 306, for patient households.** The MPC comparison also fails two
periods before the end when `βR > 1` (`θ = 1/2 < 1`): for `ctb_P` and `a₂ = 49/1000` the fall
`c₂ − c̃₂` is not nonincreasing. -/
theorem ctb_P_not_tight_mpc :
    ¬ ∀ x x', ctb_P.d ≤ x → x ≤ x' →
      ctb_P.cons 2 x' - ctb_P.cons 2 x ≤
        (ctb_P.tighten (49 / 1000)).cons 2 x' - (ctb_P.tighten (49 / 1000)).cons 2 x := by
  intro h
  have := h (5394 / 10000) (5412 / 10000)
    (by change (1 : ℝ) / 1000 ≤ 5394 / 10000; norm_num) (by norm_num)
  linarith [ctb_P_counterexample]

end AKMM.Consumption

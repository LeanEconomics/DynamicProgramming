/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.TighterLimitPerfectForesight

/-!
# A tighter limit can lower the MPC two periods before the end (CRRA with income risk)

AKMM, §11.3.4, p. 306: "their marginal propensity to consume (the slope of the consumption
function) increases" when the credit limit tightens from `a₁` to `a₂`. For the household of
`ConsumptionShape` this is proved one period before the end for every certainty equivalent
(`cfn_tight_mpc_last`), at every horizon for the expectation with `θ ≥ 1` (quadratic utility,
`cta_tight_mpc`) and at every horizon without income risk (`ctp_tight_mpc`). Here it is shown
to be **false** two periods before the end for CRRA utility with income risk.

## The counterexample

Log utility (`σ = 1`, so `M` is the harmonic mean), `β = 1/2`, `R = 1` (so `θ = 2`), loose limit
`a₁ = 2`, tight limit `a₂ = 197/100`, income `2003/1000` with probability `1/3000` and
`5003/1000` otherwise, lowest cash in hand `d = 3/1000` (`ctc_H`, `ctc_valid`). Between cash in
hand `43/4` and `279/25` the loose household's consumption two periods before the end rises by
more than the tight household's (`ctc_counterexample`), by about `2.5·10⁻⁷`; so the fall
`c₂ − c̃₂` is not nonincreasing and the MPC comparison fails (`ctc_not_tight_mpc`).

The four consumption levels are not computed in closed form. Each is bracketed by the sign of
its Euler gap at a rational point (`ctc_lt_step`, `ctc_step_lt`): consumption is the unique zero
of the increasing gap `c − θM(cₙ(R(x − c) + yᵢ))`. Next period's consumption in the low state
is the constrained `z + a` (`ctc_step_top`), and in the high state it is in turn bracketed by
the sign of its own Euler gap. All the checks are rational inequalities (`ctc_cons2_gt`,
`ctc_cons2_lt`).

## Why it fails

In the interval the low income state is constrained next period and the high one is not, for
both households. Differentiating the Euler equation in the limit `a` (not formalised) gives
`∂c₂/∂a = π·(∂c₂/∂x)/R²`, where `π` is the share of the constrained states in
`E|V₁″(Rs + yᵢ)|`, the curvature of next period's value function. As cash rises, the weight of
the high state in `π` falls at the rate of the absolute prudence of `V₁′` there. Just past the
kink that prudence includes the low-income risk two periods ahead and exceeds the prudence
`(1 + σ)/c₁` of the constrained state, so `π` rises. For an impatient enough household (here
`θ = 2`) the fall of the MPC is too small to absorb this, and `∂c₂/∂a` rises with cash in hand.
The same example refutes horizontal domination, the invariant without risk (`ctc_not_hor`).
-/

namespace AKMM.Consumption

open CfnHousehold

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-! ### Bracketing consumption by the sign of the Euler gap -/

/-- **A lower bracket.** If `c` is below the borrowing limit and below the Euler right-hand side
at saving `x − c`, then the Kuhn–Tucker consumption at `x` exceeds `c`. -/
theorem ctc_lt_step (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x c : ℝ}
    (htop : c < x + H.b / H.R) (heu : c < H.cont cn (x - c)) : c < H.step cn x := by
  have hK := cfn_step_kkt hV hg x
  by_contra hle
  push Not at hle
  have he := hK.2.2 (lt_of_le_of_lt hle htop)
  have hs : -(H.b / H.R) ≤ x - c := by linarith
  have hm := cfn_cont_mono hV hg hs (by linarith : x - c ≤ x - H.step cn x)
  linarith

/-- **An upper bracket.** If `c` exceeds the Euler right-hand side at saving `x − c`, then the
Kuhn–Tucker consumption at `x` is below `c`. -/
theorem ctc_step_lt (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x c : ℝ}
    (heu : H.cont cn (x - c) < c) : H.step cn x < c := by
  have hK := cfn_step_kkt hV hg x
  by_contra hle
  push Not at hle
  have hs : -(H.b / H.R) ≤ x - H.step cn x := cfn_save_ge hK.1
  have hm := cfn_cont_mono hV hg hs (by linarith : x - H.step cn x ≤ x - c)
  linarith [hK.2.1]

/-- **The constrained branch.** If the borrowing limit is below the Euler right-hand side at the
lowest saving `−a/R`, the household is constrained: it consumes `x + a/R`. -/
theorem ctc_step_top (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x : ℝ}
    (htop : x + H.b / H.R ≤ H.cont cn (-(H.b / H.R))) : H.step cn x = x + H.b / H.R := by
  refine cfn_step_eq_of_kkt hV hg ⟨le_rfl, ?_, fun h => absurd h (lt_irrefl _)⟩
  rwa [show x - (x + H.b / H.R) = -(H.b / H.R) by ring]

/-! ### The household -/

/-- The counterexample household: log utility (`σ = 1`), `β = 1/2`, `R = 1`, borrowing limit
`a₁ = 2`, income `2003/1000` with probability `1/3000` and `5003/1000` otherwise, `d = 3/1000`. -/
noncomputable def ctc_H : CfnHousehold (Fin 2) :=
  cfn_crra (1 / 2) 1 ![1 / 3000, 2999 / 3000] ![2003 / 1000, 5003 / 1000] 1 2 (3 / 1000)
    (5003 / 1000)

/-- The counterexample household satisfies the standing assumptions. -/
theorem ctc_valid : ctc_H.Valid := by
  refine cfn_crra_valid (by norm_num) one_pos (fun i => ?_) ?_ le_rfl (by norm_num) (by norm_num)
    (fun i => ?_) (fun i => ?_)
  · fin_cases i <;> norm_num
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · fin_cases i <;> norm_num
  · fin_cases i <;> norm_num

/-- The household with the tighter limit `a₂ ∈ [0, 2]` satisfies the standing assumptions. -/
theorem ctc_tight_valid {b₂ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 2) : (ctc_H.tighten b₂).Valid :=
  cfn_tighten_valid ctc_valid h0 h2

/-- With log utility, `β = 1/2` and `R = 1` the Euler right-hand side is twice the harmonic mean
of next period's consumptions. -/
theorem ctc_cont (b₂ : ℝ) (cn : ℝ → ℝ) (s : ℝ) :
    (ctc_H.tighten b₂).cont cn s =
      2 / (1 / 3000 / cn (s + 2003 / 1000) + 2999 / 3000 / cn (s + 5003 / 1000)) := by
  simp only [cont, CfnHousehold.tighten, ctc_H, cfn_crra, LeanEconomics.powerMean,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.rpow_neg_one, one_mul]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- **A lower bound** on consumption two periods before the end, from a lower bound `ℓ` on next
period's consumption in the high state; next period's low state is constrained. -/
theorem ctc_cons2_gt {b₂ x c ℓ : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 2) (hc : c < x + b₂)
    (hcon : x - c + 2003 / 1000 + b₂ ≤
      2 / (1 / 3000 / (-b₂ + 2003 / 1000) + 2999 / 3000 / (-b₂ + 5003 / 1000)))
    (hℓ0 : 0 < ℓ) (hℓ : ℓ < x - c + 5003 / 1000 + b₂)
    (hℓe : ℓ < 2 / (1 / 3000 / (x - c + 5003 / 1000 - ℓ + 2003 / 1000) +
      2999 / 3000 / (x - c + 5003 / 1000 - ℓ + 5003 / 1000)))
    (hm : c < 2 / (1 / 3000 / (x - c + 2003 / 1000 + b₂) + 2999 / 3000 / ℓ)) :
    c < (ctc_H.tighten b₂).cons 2 x := by
  have hV := ctc_tight_valid h0 h2
  have hR : (ctc_H.tighten b₂).R = 1 := rfl
  have hb : (ctc_H.tighten b₂).b = b₂ := rfl
  change c < (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 1) x
  refine ctc_lt_step hV (cfn_cons_good hV 1) (by rw [hR, hb, div_one]; exact hc) ?_
  rw [ctc_cont]
  have e0 : (ctc_H.tighten b₂).cons 1 (x - c + 2003 / 1000) = x - c + 2003 / 1000 + b₂ := by
    change (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 0) _ = _
    rw [ctc_step_top hV (cfn_cons_good hV 0), hR, hb, div_one]
    rw [ctc_cont, hR, hb, div_one]
    simpa only [cons] using hcon
  have e1 : ℓ < (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) := by
    change ℓ < (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 0) _
    refine ctc_lt_step hV (cfn_cons_good hV 0) (by rw [hR, hb, div_one]; exact hℓ) ?_
    rw [ctc_cont]
    simpa only [cons] using hℓe
  rw [e0]
  have hz : 0 < x - c + 2003 / 1000 + b₂ := by linarith
  have ha : 0 < (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) := lt_trans hℓ0 e1
  have hle : 2999 / 3000 / (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) ≤ 2999 / 3000 / ℓ :=
    div_le_div_of_nonneg_left (by norm_num) hℓ0 e1.le
  have hp : 0 < 1 / 3000 / (x - c + 2003 / 1000 + b₂) +
      2999 / 3000 / (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) := by positivity
  calc c < 2 / (1 / 3000 / (x - c + 2003 / 1000 + b₂) + 2999 / 3000 / ℓ) := hm
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hp (by linarith)

/-- **An upper bound** on consumption two periods before the end, from an upper bound `η` on next
period's consumption in the high state; next period's low state is constrained. -/
theorem ctc_cons2_lt {b₂ x c η : ℝ} (h0 : 0 ≤ b₂) (h2 : b₂ ≤ 2) (hc : c ≤ x + b₂)
    (hcon : x - c + 2003 / 1000 + b₂ ≤
      2 / (1 / 3000 / (-b₂ + 2003 / 1000) + 2999 / 3000 / (-b₂ + 5003 / 1000)))
    (hηe : 2 / (1 / 3000 / (x - c + 5003 / 1000 - η + 2003 / 1000) +
      2999 / 3000 / (x - c + 5003 / 1000 - η + 5003 / 1000)) < η)
    (hm : 2 / (1 / 3000 / (x - c + 2003 / 1000 + b₂) + 2999 / 3000 / η) < c) :
    (ctc_H.tighten b₂).cons 2 x < c := by
  have hV := ctc_tight_valid h0 h2
  have hR : (ctc_H.tighten b₂).R = 1 := rfl
  have hb : (ctc_H.tighten b₂).b = b₂ := rfl
  have hd : (ctc_H.tighten b₂).d = 3 / 1000 := rfl
  change (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 1) x < c
  refine ctc_step_lt hV (cfn_cons_good hV 1) ?_
  rw [ctc_cont]
  have e0 : (ctc_H.tighten b₂).cons 1 (x - c + 2003 / 1000) = x - c + 2003 / 1000 + b₂ := by
    change (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 0) _ = _
    rw [ctc_step_top hV (cfn_cons_good hV 0), hR, hb, div_one]
    rw [ctc_cont, hR, hb, div_one]
    simpa only [cons] using hcon
  have e1 : (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) < η := by
    change (ctc_H.tighten b₂).step ((ctc_H.tighten b₂).cons 0) _ < η
    refine ctc_step_lt hV (cfn_cons_good hV 0) ?_
    rw [ctc_cont]
    simpa only [cons] using hηe
  rw [e0]
  have ha : 0 < (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) :=
    (cfn_cons_good hV 1).1 _ (by rw [hd]; linarith)
  have hz : 0 < x - c + 2003 / 1000 + b₂ := by linarith
  have hle : 2999 / 3000 / η ≤ 2999 / 3000 / (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000) :=
    div_le_div_of_nonneg_left (by norm_num) ha e1.le
  have hp : 0 < 1 / 3000 / (x - c + 2003 / 1000 + b₂) + 2999 / 3000 / η := by
    have : 0 < η := lt_trans ha e1
    positivity
  calc 2 / (1 / 3000 / (x - c + 2003 / 1000 + b₂) +
        2999 / 3000 / (ctc_H.tighten b₂).cons 1 (x - c + 5003 / 1000))
      ≤ 2 / (1 / 3000 / (x - c + 2003 / 1000 + b₂) + 2999 / 3000 / η) :=
        div_le_div_of_nonneg_left (by norm_num) hp (by linarith)
    _ < c := hm

/-! ### The counterexample -/

/-- The loose household is the tightening to its own limit. -/
theorem ctc_tighten_self : ctc_H.tighten 2 = ctc_H := rfl

/-- **Counterexample to AKMM, p. 306, two periods before the end** (CRRA utility with income
risk). Between cash in hand `43/4` and `279/25` the tight household (`a₂ = 197/100`) raises its
consumption by less than the loose one (`a₁ = 2`). -/
theorem ctc_counterexample :
    (ctc_H.tighten (197 / 100)).cons 2 (279 / 25) - (ctc_H.tighten (197 / 100)).cons 2 (43 / 4)
      < ctc_H.cons 2 (279 / 25) - ctc_H.cons 2 (43 / 4) := by
  have hL1 : ctc_H.cons 2 (43 / 4) < 295299987 / 25000000 := by
    rw [← ctc_tighten_self]
    refine ctc_cons2_lt (η := 590798579987 / 100000000000) (by norm_num) le_rfl ?_ ?_ ?_ ?_ <;>
      norm_num
  have hL2 : 3016612953 / 250000000 < ctc_H.cons 2 (279 / 25) := by
    rw [← ctc_tighten_self]
    refine ctc_cons2_gt (ℓ := 603513439297 / 100000000000) (by norm_num) le_rfl ?_ ?_ ?_ ?_ ?_
      ?_ <;> norm_num
  have hT1 : 1181196963 / 100000000 < (ctc_H.tighten (197 / 100)).cons 2 (43 / 4) := by
    refine ctc_cons2_gt (ℓ := 36925072523 / 6250000000) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
      ?_ ?_ <;> norm_num
  have hT2 : (ctc_H.tighten (197 / 100)).cons 2 (279 / 25) < 1206642171 / 100000000 := by
    refine ctc_cons2_lt (η := 603515765609 / 100000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
      ?_ <;> norm_num
  linarith

/-- **Correction to AKMM, p. 306.** For CRRA utility with income risk a tighter borrowing limit
does not raise the MPC on every interval two periods before the end: the comparison that holds
one period before the end for every certainty equivalent (`cfn_tight_mpc_last`) fails at
`n = 2` for the household `ctc_H` (log utility, `β = 1/2`, `R = 1`) and `a₂ = 197/100`. -/
theorem ctc_not_tight_mpc :
    ¬ ∀ x x', ctc_H.d ≤ x → x ≤ x' →
      ctc_H.cons 2 x' - ctc_H.cons 2 x ≤
        (ctc_H.tighten (197 / 100)).cons 2 x' - (ctc_H.tighten (197 / 100)).cons 2 x := by
  intro h
  have := h (43 / 4) (279 / 25) (by change (3 : ℝ) / 1000 ≤ 43 / 4; norm_num) (by norm_num)
  linarith [ctc_counterexample]

/-- **Horizontal domination fails with income risk.** The invariant that proves the comparison
without risk (`ctp_Hor`, `ctp_tight_mpc`) does not hold two periods before the end for `ctc_H`:
with it, `ctp_mpc_of_hor` would give the comparison that `ctc_not_tight_mpc` refutes. -/
theorem ctc_not_hor :
    ¬ ctp_Hor (ctc_H.cons 2) ((ctc_H.tighten (197 / 100)).cons 2) ctc_H.d := by
  intro hP
  exact ctc_not_tight_mpc fun x x' hx hxx =>
    ctp_mpc_of_hor ctc_valid (by norm_num) (by change (197 : ℝ) / 100 ≤ 2; norm_num) 2 hP hx hxx

end AKMM.Consumption

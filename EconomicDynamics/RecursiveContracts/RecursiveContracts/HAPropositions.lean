/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.HAModel
import RecursiveContracts.HAIntegrals
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Hidden action: the dynamics of the optimal contract

Miao, §22.2, pp. 785–787: Propositions 22.2.1–22.2.3 and their consequences, for an optimal
contract `(a(v), c(v, ·), w(v, ·))` with multipliers `λ(v)`, `μ(v)` satisfying the first-order
conditions (22.17)–(22.20) of `RecursiveContracts.HAModel` on the output interval
`[y_lo, y_hi]`. At a fixed promised value `v` we write `p = f(· | a(v))`, `q = f_a(· | a(v))`,
`c = c(v, ·)`, `w = w(v, ·)`; `dφ = φ′` and `dP = P′`.

* (22.21), (22.22) and **Proposition 22.2.1** (`eq_22_21`, `eq_22_22`, `proposition_22_2_1`):
  some output `ŷ(v)` has `w(v, ŷ(v)) = v`, and there the agent gets the "first-best" income
  `1/φ′(c(v, ŷ(v))) = λ(v)` (`ha_first_best_income`).
* **Proposition 22.2.2** (`proposition_22_2_2`): `μ(v) > 0` (`ha_mu_pos`), the payment and the
  promised value are strictly increasing in output (`ha_c_strictMonoOn`, `ha_w_strictMonoOn`),
  the differentiated (22.20) and (22.17) (`ha_eq_22_20_deriv`, `ha_eq_22_17_deriv`), `c_y` and
  `w_y` have the same sign (`ha_cy_pos_iff_wy_pos`), and the reward dynamics after `ŷ(v)`
  (`ha_contract_dynamics`).
* **Proposition 22.2.3** (`proposition_22_2_3`, corrected): the inverse Euler equation, its
  inverted form (`ha_inverse_euler_inv`), the martingale property of `P′(v_t)`
  (`ha_marginal_value_martingale`), Jensen's inequality `φ′(c_t) ≤ E_t φ′(c_{t+1})`, strict
  when the next payment schedule is not flat (`ha_jensen`, `ha_jensen_strict`,
  `ha_jensen_strict_of_mu_pos`), and Rogerson's conclusion: the agent would not borrow at the
  gross interest rate `1/β` (`ha_no_borrow`) but would save (`ha_wants_to_save`,
  `ha_rogerson_save`).

Departures (see `docs/HA-corrections.md`): Proposition 22.2.3 integrates against
`f(y′ | a(w(v, y)))`, the effort recommended next period, not `f(y′ | a(v))` as printed
(`ha_proposition_22_2_3_printed_false`); Proposition 22.2.2's strict `c_y > 0`, `w_y > 0` need the
likelihood ratio's derivative to be positive at `y` (otherwise `c_y = 0` can occur:
`ha_cy_eq_zero_of_ry_zero`, `ha_flat_mlrc_density`), and the MLRC is used in its strict form;
"promised `w(v, y) > y`" on p. 787 reads `w(v, y) > v`.
-/

namespace Miao.RecursiveContracts

open MeasureTheory Filter Topology

/-- Miao, p. 785: with `φ′ > 0` strictly decreasing (`φ` strictly concave), `1/φ′` is strictly
increasing. -/
theorem ha_one_div_strictMono {dφ : ℝ → ℝ} (hdφ : StrictAnti dφ) (hpos : ∀ x, 0 < dφ x) :
    StrictMono fun x => 1 / dφ x :=
  fun _ y hxy => one_div_lt_one_div_of_lt (hpos y) (hdφ hxy)

/-! ## Proposition 22.2.1 -/

/-- Miao, (22.21), p. 785: integrating (22.17) against `f(y | a(v))` and using the envelope
condition `P′(v) = −λ(v)`, `∫ f = 1` and `∫ f_a = 0`:
`P′(v) = −∫ f(y | a(v)) / φ′(c(v, y)) dy`. -/
theorem eq_22_21 {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP p q c : ℝ → ℝ} {v lam μ : ℝ}
    (henv : dP v = -lam)
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hpc : Continuous p) (hqc : Continuous q) :
    dP v = -∫ y in ylo..yhi, 1 / dφ (c y) * p y := by
  have hcongr : ∫ y in ylo..yhi, 1 / dφ (c y) * p y = ∫ y in ylo..yhi, (lam * p y + μ * q y) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le hle] at hy
    have := (hp y hy).ne'
    rw [h17 y hy]
    field_simp
  rw [hcongr, intervalIntegral.integral_add
    ((show Continuous fun y => lam * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => μ * q y by fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hp1, hq0, henv]
  ring

/-- Miao, (22.22), p. 785: by the mean value theorem for integrals, `P′(v) = −1/φ′(c(v, ŷ(v)))`
for some output `ŷ(v)`, when `c(v, ·)` and `φ′ > 0` are continuous. -/
theorem eq_22_22 {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP p q c : ℝ → ℝ} {v lam μ : ℝ}
    (henv : dP v = -lam)
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hpc : Continuous p) (hqc : Continuous q)
    (hc : Continuous c) (hdφc : Continuous dφ) (hdφpos : ∀ x, 0 < dφ x) :
    ∃ yh ∈ Set.Icc ylo yhi, dP v = -1 / dφ (c yh) := by
  have hg : Continuous fun y => 1 / dφ (c y) :=
    continuous_const.div (hdφc.comp hc) (fun y => (hdφpos (c y)).ne')
  obtain ⟨yh, hyh, heq⟩ :=
    ha_integral_mean_value hle hg hpc (fun y hy => (hp y hy).le) hp1
  refine ⟨yh, hyh, ?_⟩
  rw [eq_22_21 hle henv h17 hp hp1 hq0 hpc hqc, heq, neg_div]

/-- **Proposition 22.2.1** (Miao, p. 785). For every promised value `v` there is an output level
`ŷ(v)` with `v = w(v, ŷ(v))`. Hypotheses: the envelope condition `P′(v) = −λ(v)`, (22.17) and
(22.20) on the output interval, `P` strictly concave (`P′` strictly decreasing), `φ′ > 0`
continuous, `c(v, ·)` continuous, and `f(· | a(v)) > 0` a continuous density with
`∫ f_a(· | a(v)) = 0`. -/
theorem proposition_22_2_1 {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP p q c w : ℝ → ℝ}
    {v lam μ : ℝ} (henv : dP v = -lam)
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y)) (hdP : StrictAnti dP)
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hpc : Continuous p) (hqc : Continuous q)
    (hc : Continuous c) (hdφc : Continuous dφ) (hdφpos : ∀ x, 0 < dφ x) :
    ∃ yh ∈ Set.Icc ylo yhi, v = w yh := by
  obtain ⟨yh, hyh, h22⟩ := eq_22_22 hle henv h17 hp hp1 hq0 hpc hqc hc hdφc hdφpos
  exact ⟨yh, hyh, hdP.injective (h22.trans (h20 yh hyh).symm)⟩

/-- Miao, p. 787: at the output `ŷ(v)` of Proposition 22.2.1 the agent is paid the "first-best"
income level associated with the multiplier `λ(v)`: `1/φ′(c(v, ŷ(v))) = λ(v)`, and the next
contract is the current one, `w(v, ŷ(v)) = v`. -/
theorem ha_first_best_income {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP p q c w : ℝ → ℝ}
    {v lam μ : ℝ} (henv : dP v = -lam)
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y)) (hdP : StrictAnti dP)
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hpc : Continuous p) (hqc : Continuous q)
    (hc : Continuous c) (hdφc : Continuous dφ) (hdφpos : ∀ x, 0 < dφ x) :
    ∃ yh ∈ Set.Icc ylo yhi, v = w yh ∧ 1 / dφ (c yh) = lam := by
  obtain ⟨yh, hyh, h22⟩ := eq_22_22 hle henv h17 hp hp1 hq0 hpc hqc hc hdφc hdφpos
  refine ⟨yh, hyh, hdP.injective (h22.trans (h20 yh hyh).symm), ?_⟩
  rw [henv, neg_div] at h22
  linarith

/-! ## Proposition 22.2.2 -/

/-- **Proposition 22.2.2** (Miao, pp. 786–787), the multiplier part: `μ(v) > 0`. The book's proof:
if `μ ≤ 0`, then by (22.17), the MLRC and the concavity of `φ`, `c(v, ·)` is decreasing; by
(22.20) and the strict concavity of `P` so is `w(v, ·)`, so `y − c(v, y) + β P(w(v, y))` is
increasing (`P` is decreasing); its covariance with `f_a / f` is then nonnegative, the
agent's second-order condition `soc < 0` makes the second term of (22.18) nonnegative, so both
vanish and `μ = 0`; then `c(v, ·)`, `w(v, ·)` are constant and (22.18) gives `∫ y f_a = 0`,
contradicting the (strict) MLRC. -/
theorem ha_mu_pos {ylo yhi β soc lam μ : ℝ} (hlt : ylo < yhi) (hβ : 0 ≤ β)
    {dφ P dP p q c w : ℝ → ℝ} (hdφ : StrictAnti dφ) (hdφpos : ∀ x, 0 < dφ x)
    (hdP : StrictAnti dP) (hP : Antitone P) (hPc : Continuous P) (hc : Continuous c)
    (hw : Continuous w) (hqc : Continuous q)
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hq0 : ∫ y in ylo..yhi, q y = 0)
    (hmlrc : StrictMonoOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y))
    (h18 : 0 = (∫ y in ylo..yhi, (y - c y + β * P (w y)) * q y) + μ * soc) (hsoc : soc < 0) :
    0 < μ := by
  by_contra hμ'
  have hμ : μ ≤ 0 := not_lt.1 hμ'
  have hΦ := ha_one_div_strictMono hdφ hdφpos
  have hqr : ∀ y ∈ Set.Icc ylo yhi, q y = q y / p y * p y := by
    intro y hy
    have := (hp y hy).ne'
    field_simp
  -- `c(v, ·)` and `w(v, ·)` are decreasing
  have hcanti : ∀ y1 ∈ Set.Icc ylo yhi, ∀ y2 ∈ Set.Icc ylo yhi, y1 ≤ y2 → c y2 ≤ c y1 := by
    intro y1 hy1 y2 hy2 h12
    have hr := hmlrc.monotoneOn hy1 hy2 h12
    have : 1 / dφ (c y2) ≤ 1 / dφ (c y1) := by
      rw [h17 y1 hy1, h17 y2 hy2]
      nlinarith
    exact hΦ.le_iff_le.1 this
  have hwanti : ∀ y1 ∈ Set.Icc ylo yhi, ∀ y2 ∈ Set.Icc ylo yhi, y1 ≤ y2 → w y2 ≤ w y1 := by
    intro y1 hy1 y2 hy2 h12
    have h1 : 1 / dφ (c y2) ≤ 1 / dφ (c y1) := hΦ.monotone (hcanti y1 hy1 y2 hy2 h12)
    have : dP (w y1) ≤ dP (w y2) := by
      rw [h20 y1 hy1, h20 y2 hy2, neg_div, neg_div]
      exact neg_le_neg h1
    exact hdP.le_iff_ge.1 this
  have hgmono : MonotoneOn (fun y => y - c y + β * P (w y)) (Set.Icc ylo yhi) := by
    intro y1 hy1 y2 hy2 h12
    have h1 := hcanti y1 hy1 y2 hy2 h12
    have h2 : P (w y1) ≤ P (w y2) := hP (hwanti y1 hy1 y2 hy2 h12)
    have h3 := mul_le_mul_of_nonneg_left h2 hβ
    simp only
    linarith
  have hnonneg := ha_mlrc_integral_nonneg hlt.le hgmono hmlrc.monotoneOn hqr
    (fun y hy => (hp y hy).le) hq0 (by fun_prop) hqc
  have hμsoc : 0 ≤ μ * soc := mul_nonneg_of_nonpos_of_nonpos hμ hsoc.le
  have hμ0 : μ = 0 := by
    have : μ * soc = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hsoc.ne
  -- with `μ = 0`, `c(v, ·)` and `w(v, ·)` are constant
  have hcconst : ∀ y ∈ Set.Icc ylo yhi, c y = c ylo := by
    intro y hy
    have hylo : ylo ∈ Set.Icc ylo yhi := ⟨le_rfl, hlt.le⟩
    apply hΦ.injective
    change 1 / dφ (c y) = 1 / dφ (c ylo)
    rw [h17 y hy, h17 ylo hylo, hμ0, zero_mul, zero_mul]
  have hwconst : ∀ y ∈ Set.Icc ylo yhi, w y = w ylo := by
    intro y hy
    have hylo : ylo ∈ Set.Icc ylo yhi := ⟨le_rfl, hlt.le⟩
    apply hdP.injective
    rw [h20 y hy, h20 ylo hylo, hcconst y hy]
  set K := c ylo - β * P (w ylo) with hK
  have hcongr : ∫ y in ylo..yhi, (y - c y + β * P (w y)) * q y =
      ∫ y in ylo..yhi, (y * q y - K * q y) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le hlt.le] at hy
    rw [hcconst y hy, hwconst y hy, hK]
    ring
  have hpos := ha_mlrc_integral_pos hlt (g := fun y => y) (strictMono_id.strictMonoOn _) hmlrc
    hqr hp hq0 continuous_id hqc
  rw [hcongr, intervalIntegral.integral_sub
    ((show Continuous fun y => y * q y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => K * q y by fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul, hq0, hμ0] at h18
  linarith

/-- Miao, p. 787 (consequence of Proposition 22.2.2 and (22.17)): with `μ(v) > 0` and the strict
MLRC, the payment `c(v, ·)` is strictly increasing in output. -/
theorem ha_c_strictMonoOn {ylo yhi lam μ : ℝ} {dφ p q c : ℝ → ℝ} (hdφ : StrictAnti dφ)
    (hdφpos : ∀ x, 0 < dφ x) (hμ : 0 < μ)
    (hmlrc : StrictMonoOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y)) :
    StrictMonoOn c (Set.Icc ylo yhi) := by
  intro y1 hy1 y2 hy2 h12
  have hr := hmlrc hy1 hy2 h12
  have : 1 / dφ (c y1) < 1 / dφ (c y2) := by
    rw [h17 y1 hy1, h17 y2 hy2]
    exact add_lt_add_right (mul_lt_mul_of_pos_left hr hμ) lam
  exact (ha_one_div_strictMono hdφ hdφpos).lt_iff_lt.1 this

/-- Miao, p. 787 (consequence of Proposition 22.2.2 and (22.20)): with `μ(v) > 0` and the strict
MLRC, the promised value `w(v, ·)` is strictly increasing in output. -/
theorem ha_w_strictMonoOn {ylo yhi lam μ : ℝ} {dφ dP p q c w : ℝ → ℝ} (hdφ : StrictAnti dφ)
    (hdφpos : ∀ x, 0 < dφ x) (hdP : StrictAnti dP) (hμ : 0 < μ)
    (hmlrc : StrictMonoOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y)) :
    StrictMonoOn w (Set.Icc ylo yhi) := by
  intro y1 hy1 y2 hy2 h12
  have hc := ha_c_strictMonoOn hdφ hdφpos hμ hmlrc h17 hy1 hy2 h12
  have h1 : 1 / dφ (c y1) < 1 / dφ (c y2) := ha_one_div_strictMono hdφ hdφpos hc
  have : dP (w y2) < dP (w y1) := by
    rw [h20 y1 hy1, h20 y2 hy2, neg_div, neg_div]
    exact neg_lt_neg h1
  exact hdP.lt_iff_gt.1 this

/-- Miao, p. 786 (first display of the proof of Proposition 22.2.2): differentiating (22.20) in
output, `P″(w(v, y)) w_y(v, y) = φ″(c(v, y)) / φ′(c(v, y))² · c_y(v, y)`. -/
theorem ha_eq_22_20_deriv {dφ dP c w : ℝ → ℝ} {y cy wy ddφ ddP : ℝ}
    (hc : HasDerivAt c cy y) (hw : HasDerivAt w wy y) (hdφd : HasDerivAt dφ ddφ (c y))
    (hdPd : HasDerivAt dP ddP (w y)) (hne : dφ (c y) ≠ 0)
    (h20 : ∀ᶠ y' in 𝓝 y, dP (w y') = -1 / dφ (c y')) :
    ddP * wy = ddφ / dφ (c y) ^ 2 * cy := by
  have h1 : HasDerivAt (fun y' => dP (w y')) (ddP * wy) y := hdPd.comp y hw
  have h2 : HasDerivAt (fun y' => -1 / dφ (c y'))
      ((0 * dφ (c y) - -1 * (ddφ * cy)) / dφ (c y) ^ 2) y :=
    (hasDerivAt_const y (-1 : ℝ)).div (hdφd.comp y hc) hne
  rw [h1.unique (h2.congr_of_eventuallyEq h20)]
  field_simp
  ring

/-- Miao, p. 786 ("By (22.17) and concavity of `φ`"): differentiating (22.17) in output,
`−φ″(c(v, y)) / φ′(c(v, y))² · c_y(v, y) = μ(v) r_y(y)` for the likelihood ratio
`r = f_a / f`. -/
theorem ha_eq_22_17_deriv {dφ c r : ℝ → ℝ} {y cy ry ddφ lam μ : ℝ}
    (hc : HasDerivAt c cy y) (hr : HasDerivAt r ry y) (hdφd : HasDerivAt dφ ddφ (c y))
    (hne : dφ (c y) ≠ 0) (h17 : ∀ᶠ y' in 𝓝 y, 1 / dφ (c y') = lam + μ * r y') :
    -ddφ / dφ (c y) ^ 2 * cy = μ * ry := by
  have h1 : HasDerivAt (fun y' => lam + μ * r y') (μ * ry) y := (hr.const_mul μ).const_add lam
  have h2 : HasDerivAt (fun y' => 1 / dφ (c y'))
      ((0 * dφ (c y) - 1 * (ddφ * cy)) / dφ (c y) ^ 2) y :=
    (hasDerivAt_const y (1 : ℝ)).div (hdφd.comp y hc) hne
  rw [(h1.congr_of_eventuallyEq h17).unique h2]
  field_simp
  ring

/-- Miao, p. 786: "Since `P` and `φ` are strictly concave, `c_y` and `w_y` have the same sign"
(`P″ < 0`, `φ″ < 0`). -/
theorem ha_cy_pos_iff_wy_pos {dφ dP c w : ℝ → ℝ} {y cy wy ddφ ddP : ℝ}
    (hc : HasDerivAt c cy y) (hw : HasDerivAt w wy y) (hdφd : HasDerivAt dφ ddφ (c y))
    (hdPd : HasDerivAt dP ddP (w y)) (hne : dφ (c y) ≠ 0)
    (h20 : ∀ᶠ y' in 𝓝 y, dP (w y') = -1 / dφ (c y')) (hddφ : ddφ < 0) (hddP : ddP < 0) :
    (0 < cy ↔ 0 < wy) := by
  have heq := ha_eq_22_20_deriv hc hw hdφd hdPd hne h20
  have hk : ddφ / dφ (c y) ^ 2 < 0 := div_neg_of_neg_of_pos hddφ (by positivity)
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **Proposition 22.2.2** (Miao, p. 786), corrected. Suppose `c(v, ·)`, `w(v, ·)` and the
likelihood ratio `r = f_a / f` are differentiable at an interior output `y`, `φ″ < 0`,
`P″ < 0` there and, in addition to the book's hypotheses, `r_y(y) > 0`. Then `μ(v) > 0`,
`c_y(v, y) > 0` and `w_y(v, y) > 0`. (With only the strict MLRC, `r_y(y) = 0` is possible and
then `c_y(v, y) = w_y(v, y) = 0`: `ha_cy_eq_zero_of_ry_zero`, `ha_flat_mlrc_density`.) -/
theorem proposition_22_2_2 {ylo yhi β soc lam μ : ℝ} (hlt : ylo < yhi) (hβ : 0 ≤ β)
    {dφ P dP p q c w : ℝ → ℝ} (hdφ : StrictAnti dφ) (hdφpos : ∀ x, 0 < dφ x)
    (hdP : StrictAnti dP) (hP : Antitone P) (hPc : Continuous P) (hc : Continuous c)
    (hw : Continuous w) (hqc : Continuous q)
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hq0 : ∫ y in ylo..yhi, q y = 0)
    (hmlrc : StrictMonoOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y))
    (h18 : 0 = (∫ y in ylo..yhi, (y - c y + β * P (w y)) * q y) + μ * soc) (hsoc : soc < 0)
    {y cy wy ry ddφ ddP : ℝ} (hy : y ∈ Set.Ioo ylo yhi) (hcd : HasDerivAt c cy y)
    (hwd : HasDerivAt w wy y) (hrd : HasDerivAt (fun y' => q y' / p y') ry y)
    (hdφd : HasDerivAt dφ ddφ (c y)) (hdPd : HasDerivAt dP ddP (w y)) (hddφ : ddφ < 0)
    (hddP : ddP < 0) (hry : 0 < ry) :
    0 < μ ∧ 0 < cy ∧ 0 < wy := by
  have hμ := ha_mu_pos hlt hβ hdφ hdφpos hdP hP hPc hc hw hqc hp hq0 hmlrc h17 h20 h18 hsoc
  have hnhds : Set.Icc ylo yhi ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
  have h17e : ∀ᶠ y' in 𝓝 y, 1 / dφ (c y') = lam + μ * (q y' / p y') :=
    Filter.eventually_of_mem hnhds h17
  have h20e : ∀ᶠ y' in 𝓝 y, dP (w y') = -1 / dφ (c y') := Filter.eventually_of_mem hnhds h20
  have hne : dφ (c y) ≠ 0 := (hdφpos (c y)).ne'
  have hform := ha_eq_22_17_deriv (r := fun y' => q y' / p y') hcd hrd hdφd hne h17e
  have hk : 0 < -ddφ / dφ (c y) ^ 2 := div_pos (neg_pos.2 hddφ) (by positivity)
  have hcy : 0 < cy := by
    by_contra hcy
    have : -ddφ / dφ (c y) ^ 2 * cy ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (not_lt.1 hcy)
    nlinarith [mul_pos hμ hry]
  exact ⟨hμ, hcy, (ha_cy_pos_iff_wy_pos hcd hwd hdφd hdPd hne h20e hddφ hddP).1 hcy⟩

/-- Miao, p. 786, the correction to Proposition 22.2.2: by the differentiated (22.17), at an
output where the likelihood ratio has `r_y = 0` the payment has `c_y = 0`, whatever `μ(v)`. -/
theorem ha_cy_eq_zero_of_ry_zero {dφ c r : ℝ → ℝ} {y cy ddφ lam μ : ℝ}
    (hc : HasDerivAt c cy y) (hr : HasDerivAt r 0 y) (hdφd : HasDerivAt dφ ddφ (c y))
    (hne : dφ (c y) ≠ 0) (hddφ : ddφ ≠ 0) (h17 : ∀ᶠ y' in 𝓝 y, 1 / dφ (c y') = lam + μ * r y') :
    cy = 0 := by
  have h := ha_eq_22_17_deriv hc hr hdφd hne h17
  rw [mul_zero] at h
  have hk : -ddφ / dφ (c y) ^ 2 ≠ 0 := div_ne_zero (neg_ne_zero.2 hddφ) (by positivity)
  exact (mul_eq_zero.1 h).resolve_left hk

/-- Miao, p. 786, counterexample to the strict `c_y > 0` of Proposition 22.2.2 under the strict
MLRC alone: the densities `f(y | a) = 1 + a (y − 1/2)³` on `[0, 1]`, `|a| ≤ 1`, are positive and
integrate to one, `f_a(y | a) = (y − 1/2)³` (they are linear in `a`,
`ha_linearDensity_hasDerivAt`), and the likelihood ratio `r = f_a / f` is strictly increasing
on `[0, 1]` with `r_y(1/2) = 0`; by `ha_cy_eq_zero_of_ry_zero`, `c_y(v, 1/2) = 0`. -/
theorem ha_flat_mlrc_density {a : ℝ} (ha : |a| ≤ 1) :
    (∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + a * (y - 1 / 2) ^ 3) ∧
    (∫ y in (0 : ℝ)..1, (1 + a * (y - 1 / 2) ^ 3)) = 1 ∧
    StrictMonoOn (fun y => (y - 1 / 2) ^ 3 / (1 + a * (y - 1 / 2) ^ 3)) (Set.Icc 0 1) ∧
    HasDerivAt (fun y => (y - 1 / 2) ^ 3 / (1 + a * (y - 1 / 2) ^ 3)) 0 (1 / 2) := by
  have hpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + a * (y - 1 / 2) ^ 3 := by
    intro y hy
    have hz : |y - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hb : |a * (y - 1 / 2) ^ 3| ≤ 1 / 8 := by
      rw [abs_mul, abs_pow]
      calc |a| * |y - 1 / 2| ^ 3 ≤ 1 * (1 / 2) ^ 3 :=
            mul_le_mul ha (pow_le_pow_left₀ (abs_nonneg _) hz 3) (by positivity) zero_le_one
        _ = 1 / 8 := by norm_num
    linarith [neg_abs_le (a * (y - 1 / 2) ^ 3)]
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rw [intervalIntegral.integral_add intervalIntegrable_const
      ((show Continuous fun y : ℝ => a * (y - 1 / 2) ^ 3 by fun_prop).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ 3) (1 / 2), integral_pow]
    norm_num
  · intro s hs t ht hst
    have h3 : (s - 1 / 2) ^ 3 < (t - 1 / 2) ^ 3 :=
      (Odd.strictMono_pow (by decide : Odd 3)) (by linarith)
    rw [div_lt_div_iff₀ (hpos s hs) (hpos t ht)]
    nlinarith
  · have hN : HasDerivAt (fun y : ℝ => (y - 1 / 2) ^ 3)
        ((3 : ℕ) * ((1 : ℝ) / 2 - 1 / 2) ^ (3 - 1) * 1) (1 / 2) :=
      ((hasDerivAt_id (1 / 2 : ℝ)).sub_const (1 / 2)).pow 3
    have hD : HasDerivAt (fun y : ℝ => 1 + a * (y - 1 / 2) ^ 3)
        (a * ((3 : ℕ) * ((1 : ℝ) / 2 - 1 / 2) ^ (3 - 1) * 1)) (1 / 2) :=
      (hN.const_mul a).const_add 1
    have hne : (1 : ℝ) + a * (1 / 2 - 1 / 2) ^ 3 ≠ 0 := by norm_num
    exact (hN.div hD hne).congr_deriv (by norm_num)

/-- Miao, p. 787: the dynamics after observing output `y`: with `μ(v) > 0` and the strict MLRC, if
`y > ŷ(v)` the agent is paid more than the "first-best" income `c(v, ŷ(v))` and promised more
than `v` (the book prints "`w(v, y) > y`"); if `y < ŷ(v)`, less and less. -/
theorem ha_contract_dynamics {ylo yhi lam μ v yh : ℝ} {dφ dP p q c w : ℝ → ℝ}
    (hdφ : StrictAnti dφ) (hdφpos : ∀ x, 0 < dφ x) (hdP : StrictAnti dP) (hμ : 0 < μ)
    (hmlrc : StrictMonoOn (fun y => q y / p y) (Set.Icc ylo yhi))
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y)) (hyh : yh ∈ Set.Icc ylo yhi)
    (hv : v = w yh) :
    ∀ y ∈ Set.Icc ylo yhi, (yh < y → c yh < c y ∧ v < w y) ∧ (y < yh → c y < c yh ∧ w y < v) := by
  intro y hy
  have hc := ha_c_strictMonoOn hdφ hdφpos hμ hmlrc h17
  have hw := ha_w_strictMonoOn hdφ hdφpos hdP hμ hmlrc h17 h20
  rw [hv]
  exact ⟨fun h => ⟨hc hyh hy h, hw hyh hy h⟩, fun h => ⟨hc hy hyh h, hw hy hyh h⟩⟩

/-! ## Proposition 22.2.3: the inverse Euler equation -/

/-- **Proposition 22.2.3** (Inverse Euler equation, Miao, p. 787), corrected:
`1/φ′(c(v, y)) = ∫ 1/φ′(c(w(v, y), y′)) f(y′ | a(w(v, y))) dy′`. The proof: (22.21) at the
promised value `w(v, y)` combined with (22.20). The density integrated against is that of
next period's recommended effort `a(w(v, y))`; the book prints `f(y′ | a(v))`
(`ha_proposition_22_2_3_printed_false`). Hypotheses hold at every promised value: the envelope
condition, (22.17), (22.20), and `f(· | a(v)) > 0` continuous densities with
`∫ f_a(· | a(v)) = 0`. -/
theorem proposition_22_2_3 {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi) :
    1 / dφ (c v y) = ∫ y' in ylo..yhi, 1 / dφ (c (w v y) y') * f (a (w v y)) y' := by
  have h21 := eq_22_21 hle (henv (w v y)) (h17 (w v y)) (hf (w v y)) (hf1 (w v y)) (hfa0 (w v y))
    (hfc (w v y)) (hfac (w v y))
  rw [h20 v y hy, neg_div] at h21
  exact neg_inj.1 h21

/-- Miao, p. 787 ("By this proposition"): the inverse Euler equation inverted,
`φ′(c(v, y)) = (∫ 1/φ′(c(w(v, y), y′)) f(y′ | a(w(v, y))) dy′)⁻¹`. -/
theorem ha_inverse_euler_inv {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi) :
    dφ (c v y) = (∫ y' in ylo..yhi, 1 / dφ (c (w v y) y') * f (a (w v y)) y')⁻¹ := by
  rw [← proposition_22_2_3 hle henv h17 h20 hf hf1 hfa0 hfc hfac v y hy, one_div, inv_inv]

/-- Miao, pp. 785–787 (the step shared by Propositions 22.2.1 and 22.2.3): the marginal value
`P′(v_t)` of the promised value is a martingale,
`P′(v) = ∫ P′(w(v, y)) f(y | a(v)) dy`, from (22.20) and (22.21). -/
theorem ha_marginal_value_martingale {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP p q c w : ℝ → ℝ}
    {v lam μ : ℝ} (henv : dP v = -lam)
    (h17 : ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c y) = lam + μ * (q y / p y))
    (h20 : ∀ y ∈ Set.Icc ylo yhi, dP (w y) = -1 / dφ (c y))
    (hp : ∀ y ∈ Set.Icc ylo yhi, 0 < p y) (hp1 : ∫ y in ylo..yhi, p y = 1)
    (hq0 : ∫ y in ylo..yhi, q y = 0) (hpc : Continuous p) (hqc : Continuous q) :
    dP v = ∫ y in ylo..yhi, dP (w y) * p y := by
  rw [eq_22_21 hle henv h17 hp hp1 hq0 hpc hqc, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le hle] at hy
  rw [h20 y hy, neg_div, neg_mul]

/-- Miao, p. 787 ("It follows from Jensen's inequality"): `φ′(c(v, y)) ≤ E φ′(c(w(v, y), y′))`,
the expectation under next period's density `f(· | a(w(v, y)))`, for `φ′ > 0` continuous and
continuous payment schedules. -/
theorem ha_jensen {ylo yhi : ℝ} (hle : ylo ≤ yhi) {dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (hc : ∀ v, Continuous (c v)) (hdφc : Continuous dφ)
    (hdφpos : ∀ x, 0 < dφ x) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi) :
    dφ (c v y) ≤ ∫ y' in ylo..yhi, dφ (c (w v y) y') * f (a (w v y)) y' := by
  rw [ha_inverse_euler_inv hle henv h17 h20 hf hf1 hfa0 hfc hfac v y hy]
  exact ha_inv_expect_inv_le hle (hdφc.comp (hc (w v y))) (fun y' => hdφpos _) (hfc (w v y))
    (fun y' hy' => (hf (w v y) y' hy').le) (hf1 (w v y))

/-- Miao, p. 787: the strict inequality `φ′(c(v, y)) < E φ′(c(w(v, y), y′))` printed in the book
holds when next period's payment schedule `c(w(v, y), ·)` is not constant on the output
interval (and `φ′` is strictly decreasing). -/
theorem ha_jensen_strict {ylo yhi : ℝ} (hlt : ylo < yhi) {dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (hc : ∀ v, Continuous (c v)) (hdφc : Continuous dφ)
    (hdφpos : ∀ x, 0 < dφ x) (hdφ : StrictAnti dφ) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi)
    (hnc : ∃ y₁ ∈ Set.Icc ylo yhi, ∃ y₂ ∈ Set.Icc ylo yhi, c (w v y) y₁ ≠ c (w v y) y₂) :
    dφ (c v y) < ∫ y' in ylo..yhi, dφ (c (w v y) y') * f (a (w v y)) y' := by
  rw [ha_inverse_euler_inv hlt.le henv h17 h20 hf hf1 hfa0 hfc hfac v y hy]
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := hnc
  exact ha_inv_expect_inv_lt hlt (hdφc.comp (hc (w v y))) (fun y' => hdφpos _) (hfc (w v y))
    (hf (w v y)) (hf1 (w v y)) ⟨y₁, hy₁, y₂, hy₂, fun h => hne (hdφ.injective h)⟩

/-- Miao, p. 787: the strict Jensen inequality holds in the model: if next period's multiplier
`μ(w(v, y))` is positive (Proposition 22.2.2) and the MLRC holds strictly at `a(w(v, y))`, then
`c(w(v, y), ·)` is strictly increasing, hence not constant, so
`φ′(c(v, y)) < E φ′(c(w(v, y), y′))`. -/
theorem ha_jensen_strict_of_mu_pos {ylo yhi : ℝ} (hlt : ylo < yhi) {dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (hc : ∀ v, Continuous (c v)) (hdφc : Continuous dφ)
    (hdφpos : ∀ x, 0 < dφ x) (hdφ : StrictAnti dφ) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi)
    (hμ : 0 < μ (w v y))
    (hmlrc : StrictMonoOn (fun y' => fa (a (w v y)) y' / f (a (w v y)) y') (Set.Icc ylo yhi)) :
    dφ (c v y) < ∫ y' in ylo..yhi, dφ (c (w v y) y') * f (a (w v y)) y' := by
  have hmono := ha_c_strictMonoOn hdφ hdφpos hμ hmlrc (h17 (w v y))
  refine ha_jensen_strict hlt henv h17 h20 hf hf1 hfa0 hfc hfac hc hdφc hdφpos hdφ v y hy
    ⟨ylo, ⟨le_rfl, hlt.le⟩, yhi, ⟨hlt.le, le_rfl⟩, ?_⟩
  exact (hmono ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt).ne

/-! ## Rogerson's saving implication -/

/-- Miao, p. 787 (the concavity step behind the saving implication): for `φ` with strictly
decreasing derivative `φ′` and `x < z`, the strict tangent inequalities
`φ′(z) (z − x) < φ(z) − φ(x) < φ′(x) (z − x)`. -/
theorem ha_tangent_lt {φ dφ : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : StrictAnti dφ)
    {x z : ℝ} (hxz : x < z) :
    dφ z * (z - x) < φ z - φ x ∧ φ z - φ x < dφ x * (z - x) := by
  have hcont : ContinuousOn φ (Set.Icc x z) :=
    fun t _ => (hφ t).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope φ dφ hxz hcont (fun t _ => hφ t)
  have hpos : 0 < z - x := sub_pos.2 hxz
  have heq : φ z - φ x = dφ ξ * (z - x) := by
    rw [hslope]
    field_simp
  rw [heq]
  exact ⟨mul_lt_mul_of_pos_right (hdφ hξ.2) hpos, mul_lt_mul_of_pos_right (hdφ hξ.1) hpos⟩

/-- Miao, p. 787: "the agent would not wish to borrow money at the gross interest rate `1/β`".
If `φ′(c₀) ≤ E φ′(c′)` (Jensen's inequality above, with today's payment `c₀ = c(v, y)`, next
period's schedule `c′ = c(w(v, y), ·)` and density `p = f(· | a(w(v, y)))`), then borrowing
any `b > 0` today and repaying `b/β` tomorrow strictly lowers the agent's utility
`φ(c₀) + β E φ(c′)`, efforts held fixed. -/
theorem ha_no_borrow {ylo yhi β c₀ b : ℝ} (hle : ylo ≤ yhi) (hβ : 0 < β) (hb : 0 < b)
    {φ dφ c' p : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : StrictAnti dφ)
    (hdφc : Continuous dφ) (hc' : Continuous c') (hp : Continuous p)
    (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ p y)
    (heuler : dφ c₀ ≤ ∫ y in ylo..yhi, dφ (c' y) * p y) :
    φ (c₀ + b) + β * ∫ y in ylo..yhi, φ (c' y - b / β) * p y <
      φ c₀ + β * ∫ y in ylo..yhi, φ (c' y) * p y := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  have h1 := (ha_tangent_lt hφ hdφ (show c₀ < c₀ + b by linarith)).2
  rw [add_sub_cancel_left] at h1
  have hbβ : 0 < b / β := div_pos hb hβ
  have hpt : ∀ y ∈ Set.Icc ylo yhi,
      φ (c' y - b / β) * p y ≤ φ (c' y) * p y - b / β * (dφ (c' y) * p y) := by
    intro y hy
    have h2 := (ha_tangent_lt hφ hdφ (show c' y - b / β < c' y by linarith)).1
    rw [sub_sub_cancel] at h2
    nlinarith [hp0 y hy]
  have hint := intervalIntegral.integral_mono_on (μ := volume) hle
    ((show Continuous fun y => φ (c' y - b / β) * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => φ (c' y) * p y - b / β * (dφ (c' y) * p y) by
      fun_prop).intervalIntegrable ylo yhi) hpt
  rw [intervalIntegral.integral_sub
    ((show Continuous fun y => φ (c' y) * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => b / β * (dφ (c' y) * p y) by fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul] at hint
  have h3 := mul_le_mul_of_nonneg_left hint hβ.le
  have h4 : β * (b / β) = b := by field_simp
  rw [mul_sub, ← mul_assoc, h4] at h3
  have h5 := mul_le_mul_of_nonneg_left heuler hb.le
  linarith

/-- Miao, p. 787: "but the agent would wish to save money" (Rogerson 1985a). If
`φ′(c₀) < E φ′(c′)` (the strict Jensen inequality), then saving some `s > 0` today at the gross
interest rate `1/β` strictly raises the agent's utility `φ(c₀) + β E φ(c′)`, efforts held fixed. -/
theorem ha_wants_to_save {ylo yhi β c₀ : ℝ} (hle : ylo ≤ yhi) (hβ : 0 < β)
    {φ dφ c' p : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : StrictAnti dφ)
    (hdφc : Continuous dφ) (hc' : Continuous c') (hp : Continuous p)
    (hp0 : ∀ y ∈ Set.Icc ylo yhi, 0 ≤ p y)
    (heuler : dφ c₀ < ∫ y in ylo..yhi, dφ (c' y) * p y) :
    ∃ s > 0, φ c₀ + β * ∫ y in ylo..yhi, φ (c' y) * p y <
      φ (c₀ - s) + β * ∫ y in ylo..yhi, φ (c' y + s / β) * p y := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  set F : ℝ → ℝ := fun s => (∫ y in ylo..yhi, dφ (c' y + s / β) * p y) - dφ (c₀ - s) with hF
  have hJ : Continuous fun z : ℝ × ℝ => dφ (c' z.2 + z.1 / β) * p z.2 := by fun_prop
  have hFc : Continuous F :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun s y => dφ (c' y + s / β) * p y) hJ ylo yhi).sub (by fun_prop)
  have hF0 : 0 < F 0 := by
    simp only [hF, zero_div, add_zero, sub_zero]
    linarith
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < F s := hFc.continuousAt.eventually (eventually_gt_nhds hF0)
  obtain ⟨s, hFs, hs⟩ : ∃ s, 0 < F s ∧ 0 < s :=
    ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  refine ⟨s, hs, ?_⟩
  have h1 := (ha_tangent_lt hφ hdφ (show c₀ - s < c₀ by linarith)).2
  rw [sub_sub_cancel] at h1
  have hsβ : 0 < s / β := div_pos hs hβ
  have hpt : ∀ y ∈ Set.Icc ylo yhi,
      φ (c' y) * p y + s / β * (dφ (c' y + s / β) * p y) ≤ φ (c' y + s / β) * p y := by
    intro y hy
    have h2 := (ha_tangent_lt hφ hdφ (show c' y < c' y + s / β by linarith)).1
    rw [add_sub_cancel_left] at h2
    nlinarith [hp0 y hy]
  have hint := intervalIntegral.integral_mono_on (μ := volume) hle
    ((show Continuous fun y => φ (c' y) * p y + s / β * (dφ (c' y + s / β) * p y) by
      fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => φ (c' y + s / β) * p y by fun_prop).intervalIntegrable ylo yhi) hpt
  rw [intervalIntegral.integral_add
    ((show Continuous fun y => φ (c' y) * p y by fun_prop).intervalIntegrable ylo yhi)
    ((show Continuous fun y => s / β * (dφ (c' y + s / β) * p y) by
      fun_prop).intervalIntegrable ylo yhi),
    intervalIntegral.integral_const_mul] at hint
  have h3 := mul_le_mul_of_nonneg_left hint hβ.le
  have h4 : β * (s / β) = s := by field_simp
  rw [mul_add, ← mul_assoc, h4] at h3
  have hFs' : dφ (c₀ - s) < ∫ y in ylo..yhi, dφ (c' y + s / β) * p y := by
    simp only [hF] at hFs
    linarith
  have h5 := mul_lt_mul_of_pos_left hFs' hs
  linarith

/-- Miao, p. 787, Rogerson's result in the model: when next period's multiplier `μ(w(v, y))` is
positive and the MLRC holds strictly there, the agent, paid `c(v, y)` today and facing the
schedule `c(w(v, y), ·)` tomorrow, would gain from saving some `s > 0` at the gross interest
rate `1/β`. -/
theorem ha_rogerson_save {ylo yhi β : ℝ} (hlt : ylo < yhi) (hβ : 0 < β) {φ dφ dP : ℝ → ℝ}
    {c w f fa : ℝ → ℝ → ℝ} {a lam μ : ℝ → ℝ} (henv : ∀ v, dP v = -lam v)
    (h17 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 1 / dφ (c v y) = lam v + μ v * (fa (a v) y / f (a v) y))
    (h20 : ∀ v, ∀ y ∈ Set.Icc ylo yhi, dP (w v y) = -1 / dφ (c v y))
    (hf : ∀ v, ∀ y ∈ Set.Icc ylo yhi, 0 < f (a v) y) (hf1 : ∀ v, ∫ y in ylo..yhi, f (a v) y = 1)
    (hfa0 : ∀ v, ∫ y in ylo..yhi, fa (a v) y = 0) (hfc : ∀ v, Continuous (f (a v)))
    (hfac : ∀ v, Continuous (fa (a v))) (hc : ∀ v, Continuous (c v))
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφc : Continuous dφ) (hdφpos : ∀ x, 0 < dφ x)
    (hdφ : StrictAnti dφ) (v y : ℝ) (hy : y ∈ Set.Icc ylo yhi) (hμ : 0 < μ (w v y))
    (hmlrc : StrictMonoOn (fun y' => fa (a (w v y)) y' / f (a (w v y)) y') (Set.Icc ylo yhi)) :
    ∃ s > 0, φ (c v y) + β * ∫ y' in ylo..yhi, φ (c (w v y) y') * f (a (w v y)) y' <
      φ (c v y - s) + β * ∫ y' in ylo..yhi, φ (c (w v y) y' + s / β) * f (a (w v y)) y' :=
  ha_wants_to_save hlt.le hβ hφ hdφ hdφc (hc (w v y)) (hfc (w v y))
    (fun y' hy' => (hf (w v y) y' hy').le)
    (ha_jensen_strict_of_mu_pos hlt henv h17 h20 hf hf1 hfa0 hfc hfac hc hdφc hdφpos hdφ v y hy
      hμ hmlrc)

/-- Miao, p. 787, counterexample to Proposition 22.2.3 as printed (integrating against
`f(y′ | a(v))`). Take outputs in `[0, 1]`, the densities `f(y | a) = 1 + a (2y − 1)` (positive
for `|a| < 1`, integrating to one, with increasing likelihood ratio), and next period's
schedule with `1/φ′(c(w(v, y), y′)) = y′` (e.g. `φ = log`, `c(w(v, y), y′) = y′`). Then
`∫ y′ f(y′ | a) dy′ = 1/2 + a/6`, so the corrected right side (with `a = a(w(v, y))`) and the
printed one (with `a = a(v)`) differ whenever the recommended effort changes,
`a(w(v, y)) ≠ a(v)`: both cannot equal `1/φ′(c(v, y))`. -/
theorem ha_proposition_22_2_3_printed_false {a₀ a₁ : ℝ} (hne : a₀ ≠ a₁) :
    (∫ y in (0 : ℝ)..1, y * (1 + a₁ * (2 * y - 1))) ≠
      ∫ y in (0 : ℝ)..1, y * (1 + a₀ * (2 * y - 1)) := by
  have key : ∀ a : ℝ, ∫ y in (0 : ℝ)..1, y * (1 + a * (2 * y - 1)) = 1 / 2 + a / 6 := by
    intro a
    have hrw : (fun y : ℝ => y * (1 + a * (2 * y - 1))) = fun y => (1 - a) * y + 2 * a * y ^ 2 := by
      funext y
      ring
    rw [hrw, intervalIntegral.integral_add
      ((show Continuous fun y : ℝ => (1 - a) * y by fun_prop).intervalIntegrable 0 1)
      ((show Continuous fun y : ℝ => 2 * a * y ^ 2 by fun_prop).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
      integral_pow]
    ring
  rw [key, key]
  intro h
  exact hne (by linarith)

end Miao.RecursiveContracts

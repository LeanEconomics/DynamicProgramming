/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMMoney.OLGDemand
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Fiat money in the Samuelson endowment economy: the classification of equilibria

AKMM, §17.2.1, pp. 496–499. Every cohort has endowment `(ω_y, ω_o)` and utility
`log c_y + log c_o`; the initial old own the money stock `M`. A sequence of money prices
`p_{m,t} ≥ 0` is an equilibrium if at every date holding the whole stock `M` is optimal for the
young (the market-clearing condition (17.4)).

* `olgIsEquilibrium`; the young's problem in money units (`olg_moneyOptimal_iff_pos`, and the
  cases `p_{m,t} = 0`: `olg_moneyOptimal_zero_pos`, `olg_moneyOptimal_zero_zero`).
* `eq_17_5`: an equilibrium is either `p ≡ 0` or a positive solution of (17.5); `eq_17_5_div`
  gives the printed form `p_{m,t+1} = ω_o p_{m,t}/(ω_y − 2Mp_{m,t})`.
* `olg_classification`: the positive solutions are exactly
  `p_{m,t} = 1/(M(2/(ω_y − ω_o) + c(ω_y/ω_o)ᵗ))`, `c ≥ 0`, and exist only when `ω_y > ω_o`.
* `olg_continuum`: for `ω_y > ω_o` the equilibrium initial prices are exactly `[0, p̄_m]`,
  `p̄_m = (ω_y − ω_o)/(2M)`; `olg_unique_given_p0`: each one determines the equilibrium;
  `olg_no_monetary`: for `ω_y ≤ ω_o` the only equilibrium is `p ≡ 0`.
* `olg_stationary`, `olg_decreasing_to_zero`: `p̄_m` gives the stationary equilibrium; every
  `p_{m,0} ∈ (0, p̄_m)` gives a strictly decreasing path converging to zero.
* The map of Figure 17.2: fixed points (`olg_map_fixed_iff`), monotonicity on `[0, p̃_m)`
  (`olg_map_strictMonoOn`), slopes `ω_o/ω_y` and `ω_y/ω_o` (`olg_map_hasDerivAt`,
  `olg_map_slopes`), and the domain restriction `p < p̃_m = ω_y/(2M)` (`olg_map_domain`).
* The real form `m_{t+1} = ω_o m_t/(ω_y − 2m_t)` and nominal neutrality (`eq_17_5_real`,
  `olg_nominal_neutral`).
-/

open Filter Topology

namespace AKMM.Money

/-- AKMM, (17.1), p. 497: lifetime utility of a young agent holding `M′` units of money at money
prices `p_{m,t}, p_{m,t+1}`. -/
noncomputable def olgMoneyUtil (ωy ωo pt pt1 M' : ℝ) : ℝ :=
  Real.log (ωy - pt * M') + Real.log (ωo + pt1 * M')

/-- AKMM, (17.1), p. 497: feasible money holdings, `M′ ≥ 0` and `c_y > 0`. -/
def olgMoneyFeasible (ωy pt M' : ℝ) : Prop := 0 ≤ M' ∧ pt * M' < ωy

/-- AKMM, (17.1), p. 497: optimal money holdings of the young. -/
def olgMoneyOptimal (ωy ωo pt pt1 M' : ℝ) : Prop :=
  olgMoneyFeasible ωy pt M' ∧
    ∀ M'', olgMoneyFeasible ωy pt M'' → olgMoneyUtil ωy ωo pt pt1 M'' ≤ olgMoneyUtil ωy ωo pt pt1 M'

/-- AKMM, (17.4), p. 498: an equilibrium of the endowment economy with money stock `M`: money
prices are nonnegative and at every date the young optimally buy the whole stock. -/
def olgIsEquilibrium (ωy ωo M : ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ t, 0 ≤ p t) ∧ ∀ t, olgMoneyOptimal ωy ωo (p t) (p (t + 1)) M

/-- The money-unit utility is the real-saving utility at `s = p_{m,t}M′`,
`R = p_{m,t+1}/p_{m,t}`. -/
theorem olg_moneyUtil_eq {ωy ωo pt pt1 : ℝ} (hpt : pt ≠ 0) (M' : ℝ) :
    olgMoneyUtil ωy ωo pt pt1 M' = olgUtil ωy ωo (pt1 / pt) (pt * M') := by
  unfold olgMoneyUtil olgUtil
  congr 2
  field_simp

/-- AKMM, (17.3), p. 498: with `p_{m,t} > 0`, `M′` is optimal iff `p_{m,t}M′` equals the demand
at the return `p_{m,t+1}/p_{m,t}`. -/
theorem olg_moneyOptimal_iff_pos {ωy ωo pt pt1 M' : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo)
    (hpt : 0 < pt) (hpt1 : 0 ≤ pt1) :
    olgMoneyOptimal ωy ωo pt pt1 M' ↔ 0 ≤ M' ∧ pt * M' = olgDemand ωy ωo (pt1 / pt) := by
  have hR : 0 ≤ pt1 / pt := div_nonneg hpt1 hpt.le
  obtain ⟨hopt, huniq⟩ := eq_17_3 hωy hωo hR
  constructor
  · rintro ⟨⟨h0, h1⟩, h⟩
    refine ⟨h0, huniq _ ⟨⟨mul_nonneg hpt.le h0, h1⟩, fun s' hs' => ?_⟩⟩
    have := h (s' / pt) ⟨div_nonneg hs'.1 hpt.le, by rw [mul_div_cancel₀ _ hpt.ne']; exact hs'.2⟩
    rwa [olg_moneyUtil_eq hpt.ne', olg_moneyUtil_eq hpt.ne', mul_div_cancel₀ _ hpt.ne'] at this
  · rintro ⟨h0, h⟩
    refine ⟨⟨h0, by rw [h]; exact hopt.1.2⟩, fun M'' hM'' => ?_⟩
    rw [olg_moneyUtil_eq hpt.ne', olg_moneyUtil_eq hpt.ne', h]
    exact hopt.2 _ ⟨mul_nonneg hpt.le hM''.1, hM''.2⟩

/-- AKMM, p. 498: if money is free today but valued tomorrow there is no optimal choice. -/
theorem olg_moneyOptimal_zero_pos {ωy ωo pt1 M' : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo)
    (hpt1 : 0 < pt1) : ¬ olgMoneyOptimal ωy ωo 0 pt1 M' := by
  rintro ⟨⟨h0, -⟩, h⟩
  have := h (M' + 1) ⟨by linarith, by simpa using hωy⟩
  unfold olgMoneyUtil at this
  have hlt : Real.log (ωo + pt1 * M') < Real.log (ωo + pt1 * (M' + 1)) :=
    Real.log_lt_log (by positivity) (by nlinarith)
  simp only [zero_mul, sub_zero] at this
  linarith

/-- AKMM, p. 498 and footnote 4: if money is worthless today and tomorrow, any holding is
optimal (the money stock can be passed on). -/
theorem olg_moneyOptimal_zero_zero {ωy ωo M' : ℝ} (hωy : 0 < ωy) :
    olgMoneyOptimal ωy ωo 0 0 M' ↔ 0 ≤ M' := by
  constructor
  · exact fun h => h.1.1
  · intro h
    refine ⟨⟨h, by simpa using hωy⟩, fun M'' _ => ?_⟩
    simp [olgMoneyUtil]

/-- One step of an equilibrium: holding `M > 0` is optimal at `(p_{m,t}, p_{m,t+1})` iff both
prices are zero, or both are positive and `p_{m,t+1}(ω_y − 2Mp_{m,t}) = ω_o p_{m,t}`. -/
theorem olg_step_iff {ωy ωo M pt pt1 : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hpt : 0 ≤ pt) (hpt1 : 0 ≤ pt1) :
    olgMoneyOptimal ωy ωo pt pt1 M ↔
      (pt = 0 ∧ pt1 = 0) ∨ (0 < pt ∧ 0 < pt1 ∧ pt1 * (ωy - 2 * M * pt) = ωo * pt) := by
  constructor
  · intro h
    rcases hpt.lt_or_eq with hp | hp
    · right
      obtain ⟨-, hd⟩ := (olg_moneyOptimal_iff_pos hωy hωo hp hpt1).1 h
      have hdpos : 0 < olgDemand ωy ωo (pt1 / pt) := by rw [← hd]; positivity
      unfold olgDemand at hd hdpos
      split_ifs at hd hdpos with hc
      · exact absurd hdpos (lt_irrefl 0)
      · have hR : 0 < pt1 / pt := by
          by_contra hn
          have : pt1 / pt = 0 := le_antisymm (not_lt.1 hn) (div_nonneg hpt1 hp.le)
          rw [this] at hc
          exact hc (by simp; linarith)
        have h1 : 0 < pt1 := by
          rcases hpt1.lt_or_eq with h' | h'
          · exact h'
          · rw [← h', zero_div] at hR; exact absurd hR (lt_irrefl 0)
        refine ⟨hp, h1, ?_⟩
        field_simp at hd
        linear_combination -hd
    · left
      subst hp
      refine ⟨rfl, ?_⟩
      by_contra hn
      exact olg_moneyOptimal_zero_pos hωy hωo (lt_of_le_of_ne hpt1 (Ne.symm hn)) h
  · rintro (⟨rfl, rfl⟩ | ⟨hp, hp1, he⟩)
    · exact (olg_moneyOptimal_zero_zero hωy).2 hM.le
    · refine (olg_moneyOptimal_iff_pos hωy hωo hp hpt1).2 ⟨hM.le, ?_⟩
      unfold olgDemand
      have hlt : ωo * pt < pt1 * ωy := by nlinarith [mul_pos (mul_pos hM hp) hp1]
      have hc : ¬ (pt1 / pt * ωy ≤ ωo) := by
        rw [not_le, div_mul_eq_mul_div, lt_div_iff₀ hp]; linarith
      simp only [hc, ↓reduceIte]
      field_simp
      linear_combination -he

/-- **AKMM, (17.5)**, p. 498: an equilibrium is either `p ≡ 0` (money never valued) or a
positive solution of `p_{m,t+1}(ω_y − 2Mp_{m,t}) = ω_o p_{m,t}`; conversely each is an
equilibrium. -/
theorem eq_17_5 {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M) (p : ℕ → ℝ) :
    olgIsEquilibrium ωy ωo M p ↔ (∀ t, p t = 0) ∨
      ∀ t, 0 < p t ∧ p (t + 1) * (ωy - 2 * M * p t) = ωo * p t := by
  constructor
  · rintro ⟨hnn, hopt⟩
    have hstep := fun t => (olg_step_iff hωy hωo hM (hnn t) (hnn (t + 1))).1 (hopt t)
    rcases (hnn 0).lt_or_eq with h0 | h0
    · right
      have hpos : ∀ t, 0 < p t := by
        intro t
        induction t with
        | zero => exact h0
        | succ n ih =>
          rcases hstep n with ⟨h, -⟩ | ⟨-, h, -⟩
          · exact absurd h ih.ne'
          · exact h
      intro t
      rcases hstep t with ⟨h, -⟩ | ⟨-, -, h⟩
      · exact absurd h (hpos t).ne'
      · exact ⟨hpos t, h⟩
    · left
      intro t
      induction t with
      | zero => exact h0.symm
      | succ n ih =>
        rcases hstep n with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd ih h.ne'
  · rintro (h | h)
    · refine ⟨fun t => (h t).ge, fun t => ?_⟩
      rw [h t, h (t + 1)]
      exact (olg_moneyOptimal_zero_zero hωy).2 hM.le
    · refine ⟨fun t => (h t).1.le, fun t => ?_⟩
      exact (olg_step_iff hωy hωo hM (h t).1.le (h (t + 1)).1.le).2
        (Or.inr ⟨(h t).1, (h (t + 1)).1, (h t).2⟩)

/-- AKMM, (17.5) and p. 499: along a monetary equilibrium `p_{m,t} < p̃_m = ω_y/(2M)` and
`p_{m,t+1} = ω_o p_{m,t}/(ω_y − 2Mp_{m,t})`. -/
theorem eq_17_5_div {ωy ωo M pt pt1 : ℝ} (hωo : 0 < ωo) (hpt : 0 < pt) (hpt1 : 0 < pt1)
    (h : pt1 * (ωy - 2 * M * pt) = ωo * pt) :
    2 * M * pt < ωy ∧ pt1 = ωo * pt / (ωy - 2 * M * pt) := by
  have hpos : 0 < ωy - 2 * M * pt := by
    by_contra hn
    have : pt1 * (ωy - 2 * M * pt) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpt1.le (not_lt.1 hn)
    nlinarith
  refine ⟨by linarith, ?_⟩
  rw [eq_div_iff hpos.ne', h]

/-- AKMM, p. 499: in real balances `m_t = p_{m,t}M` the equilibrium condition reads
`m_{t+1}(ω_y − 2m_t) = ω_o m_t`, i.e. `m_{t+1} = ω_o m_t/(ω_y − 2m_t)`. -/
theorem eq_17_5_real {ωy ωo M pt pt1 : ℝ} (hM : M ≠ 0) :
    pt1 * (ωy - 2 * M * pt) = ωo * pt ↔ M * pt1 * (ωy - 2 * (M * pt)) = ωo * (M * pt) := by
  constructor
  · intro h; linear_combination M * h
  · intro h
    have : M * (pt1 * (ωy - 2 * M * pt) - ωo * pt) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hM
    · linarith

/-- The closed form of the positive solutions: `Y_t = 2/(ω_y − ω_o) + c(ω_y/ω_o)ᵗ` satisfies
`ω_o Y_{t+1} = ω_y Y_t − 2`. -/
theorem olg_closed_form_step {ωy ωo : ℝ} (hωo : 0 < ωo) (hgap : ωo < ωy) (c : ℝ) (t : ℕ) :
    ωo * (2 / (ωy - ωo) + c * (ωy / ωo) ^ (t + 1)) =
      ωy * (2 / (ωy - ωo) + c * (ωy / ωo) ^ t) - 2 := by
  have h1 : ωy - ωo ≠ 0 := by linarith
  rw [pow_succ]
  field_simp
  ring

/-- **AKMM, pp. 498–499: the classification of equilibria.** With `ω_y, ω_o, M > 0`, `p` is an
equilibrium iff `p ≡ 0`, or `ω_y > ω_o` and for some `c ≥ 0`,
`p_{m,t} = 1/(M(2/(ω_y − ω_o) + c(ω_y/ω_o)ᵗ))` for all `t`. -/
theorem olg_classification {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (p : ℕ → ℝ) :
    olgIsEquilibrium ωy ωo M p ↔ (∀ t, p t = 0) ∨ (ωo < ωy ∧ ∃ c, 0 ≤ c ∧
      ∀ t, p t = (M * (2 / (ωy - ωo) + c * (ωy / ωo) ^ t))⁻¹) := by
  rw [eq_17_5 hωy hωo hM]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun ⟨hgap, c, hc, hp⟩ t => ?_⟩
  · set y : ℕ → ℝ := fun t => (M * p t)⁻¹ with hy
    have hypos : ∀ t, 0 < y t := fun t => inv_pos.2 (mul_pos hM (h t).1)
    have hrec : ∀ t, ωo * y (t + 1) = ωy * y t - 2 := fun t => by
      obtain ⟨hp, he⟩ := h t
      have hp1 := (h (t + 1)).1
      simp only [hy]
      field_simp
      linear_combination -he
    have hgap : ωo < ωy := by
      by_contra hn
      have hle : ωy ≤ ωo := not_lt.1 hn
      have hdec : ∀ t, y (t + 1) ≤ y t - 2 / ωo := fun t => by
        have := hrec t
        rw [le_sub_iff_add_le, ← mul_le_mul_iff_of_pos_left hωo, mul_add,
          mul_div_cancel₀ _ hωo.ne']
        nlinarith [hypos t]
      have hlin : ∀ t : ℕ, y t ≤ y 0 - t * (2 / ωo) := by
        intro t
        induction t with
        | zero => simp
        | succ n ih => have := hdec n; push_cast; linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (y 0 / (2 / ωo))
      have h2 : 0 < 2 / ωo := by positivity
      have := hlin n
      have := hypos n
      rw [div_lt_iff₀ h2] at hn
      linarith
    refine ⟨hgap, y 0 - 2 / (ωy - ωo), ?_, ?_⟩
    · set lam := ωy / ωo with hlam
      set yb := 2 / (ωy - ωo) with hyb
      have hl1 : 1 < lam := (one_lt_div hωo).2 hgap
      have hfix : ωo * yb = ωy * yb - 2 := by
        simp only [hyb]; field_simp [(by linarith : ωy - ωo ≠ 0)]; ring
      have hd : ∀ t, y t - yb = (y 0 - yb) * lam ^ t := by
        intro t
        induction t with
        | zero => simp
        | succ n ih =>
          have e : y (n + 1) - yb = lam * (y n - yb) := by
            have := hrec n
            simp only [hlam]
            field_simp
            linear_combination this - hfix
          rw [e, ih, pow_succ]; ring
      by_contra hneg
      have hd0 : y 0 - yb < 0 := not_le.1 hneg
      have hyb0 : 0 < yb := div_pos two_pos (by linarith)
      obtain ⟨n, hn⟩ := exists_nat_gt (yb / (-(y 0 - yb)) / (lam - 1))
      have hb : 1 + (n : ℝ) * (lam - 1) ≤ lam ^ n := by
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ lam - 1 by linarith) n
        simpa using this
      have hk : (y 0 - yb) * lam ^ n ≤ (y 0 - yb) * (1 + n * (lam - 1)) :=
        mul_le_mul_of_nonpos_left hb hd0.le
      have hn' : yb < (-(y 0 - yb)) * (n * (lam - 1)) := by
        rw [div_lt_iff₀ (by linarith), div_lt_iff₀ (by linarith)] at hn
        nlinarith
      have := hd n
      have := hypos n
      nlinarith
    · intro t
      have hd : ∀ t, y t = 2 / (ωy - ωo) + (y 0 - 2 / (ωy - ωo)) * (ωy / ωo) ^ t := by
        intro t
        induction t with
        | zero => simp
        | succ n ih =>
          have h1 := hrec n
          have h2 := olg_closed_form_step hωo hgap (y 0 - 2 / (ωy - ωo)) n
          apply mul_left_cancel₀ hωo.ne'
          rw [h1, h2, ih]
      rw [← hd t]
      simp only [hy]
      have := (h t).1
      field_simp
  · have hpos : ∀ t, 0 < 2 / (ωy - ωo) + c * (ωy / ωo) ^ t := fun t => by
      have : 0 < 2 / (ωy - ωo) := div_pos two_pos (by linarith)
      have : 0 ≤ c * (ωy / ωo) ^ t := mul_nonneg hc (pow_nonneg (by positivity) t)
      linarith
    have hstep := olg_closed_form_step hωo hgap c t
    refine ⟨by rw [hp t]; exact inv_pos.2 (mul_pos hM (hpos t)), ?_⟩
    rw [hp t, hp (t + 1)]
    set A := 2 / (ωy - ωo) + c * (ωy / ωo) ^ t with hA
    set B := 2 / (ωy - ωo) + c * (ωy / ωo) ^ (t + 1) with hB
    have hA0 : A ≠ 0 := (hpos t).ne'
    have hB0 : B ≠ 0 := (hpos (t + 1)).ne'
    have hM0 := hM.ne'
    calc (M * B)⁻¹ * (ωy - 2 * M * (M * A)⁻¹) = (ωy * A - 2) / (M * B * A) := by
          field_simp
      _ = ωo * B / (M * B * A) := by rw [← hstep]
      _ = ωo * (M * A)⁻¹ := by field_simp

/-- AKMM, p. 499: if `ω_y ≤ ω_o` the only equilibrium is the nonmonetary one, `p ≡ 0`. -/
theorem olg_no_monetary {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hle : ωy ≤ ωo) (p : ℕ → ℝ) : olgIsEquilibrium ωy ωo M p ↔ ∀ t, p t = 0 := by
  rw [olg_classification hωy hωo hM]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact absurd h (not_lt.2 hle)
  · exact Or.inl

/-- AKMM, p. 499: the nonmonetary equilibrium `p ≡ 0` always exists. -/
theorem olg_nonmonetary_exists {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M) :
    olgIsEquilibrium ωy ωo M (fun _ => 0) :=
  (eq_17_5 hωy hωo hM _).2 (Or.inl fun _ => rfl)

/-- **AKMM, p. 499: the continuum of equilibria.** If `ω_y > ω_o`, `p_{m,0}` is the initial price
of an equilibrium iff `p_{m,0} ∈ [0, p̄_m]`, `p̄_m = (ω_y − ω_o)/(2M)`. -/
theorem olg_continuum {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hgap : ωo < ωy) (p0 : ℝ) :
    (∃ p, olgIsEquilibrium ωy ωo M p ∧ p 0 = p0) ↔ 0 ≤ p0 ∧ p0 ≤ (ωy - ωo) / (2 * M) := by
  have hd : 0 < ωy - ωo := by linarith
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases (olg_classification hωy hωo hM p).1 hp with h | ⟨-, c, hc, h⟩
    · rw [h 0]; exact ⟨le_rfl, by positivity⟩
    · rw [h 0, pow_zero, mul_one]
      have hy : 0 < 2 / (ωy - ωo) := div_pos two_pos hd
      refine ⟨(inv_pos.2 (by positivity)).le, ?_⟩
      rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
      have : 2 * M / (ωy - ωo) = M * (2 / (ωy - ωo)) := by ring
      rw [this]
      nlinarith
  · rintro ⟨h0, h1⟩
    rcases h0.lt_or_eq with hp | hp
    · refine ⟨fun t => (M * (2 / (ωy - ωo) + ((M * p0)⁻¹ - 2 / (ωy - ωo)) *
        (ωy / ωo) ^ t))⁻¹, (olg_classification hωy hωo hM _).2 (Or.inr ⟨hgap, _, ?_,
          fun _ => rfl⟩), ?_⟩
      · rw [sub_nonneg, le_inv_comm₀ (div_pos two_pos hd) (by positivity), inv_div]
        rw [le_div_iff₀ (by positivity)] at h1
        rw [le_div_iff₀ two_pos]; linarith
      · simp only [pow_zero, mul_one, add_sub_cancel]
        field_simp
    · exact ⟨fun _ => 0, olg_nonmonetary_exists hωy hωo hM, hp⟩

/-- AKMM, p. 499: an equilibrium is determined by its initial price `p_{m,0}`. -/
theorem olg_unique_given_p0 {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p p' : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (hp' : olgIsEquilibrium ωy ωo M p')
    (h0 : p 0 = p' 0) : p = p' := by
  rcases (eq_17_5 hωy hωo hM p).1 hp with h | h <;>
    rcases (eq_17_5 hωy hωo hM p').1 hp' with h' | h'
  · funext t; rw [h, h']
  · exact absurd (h 0 ▸ h0) (h' 0).1.ne
  · exact absurd (h' 0 ▸ h0) (h 0).1.ne'
  · funext t
    induction t with
    | zero => exact h0
    | succ n ih =>
      rw [(eq_17_5_div hωo (h n).1 (h (n + 1)).1 (h n).2).2,
        (eq_17_5_div hωo (h' n).1 (h' (n + 1)).1 (h' n).2).2, ih]

/-- AKMM, p. 498: for `ω_y > ω_o` the constant price `p̄_m = (ω_y − ω_o)/(2M) > 0` is an
equilibrium (the stationary monetary equilibrium). -/
theorem olg_stationary {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hgap : ωo < ωy) :
    0 < (ωy - ωo) / (2 * M) ∧ olgIsEquilibrium ωy ωo M (fun _ => (ωy - ωo) / (2 * M)) := by
  have hd : 0 < ωy - ωo := by linarith
  refine ⟨by positivity, (eq_17_5 hωy hωo hM _).2 (Or.inr fun _ => ⟨by positivity, ?_⟩)⟩
  field_simp
  ring

/-- AKMM, p. 499: every equilibrium with `0 < p_{m,0} < p̄_m` has strictly decreasing prices
converging to zero: money loses its value in the limit. -/
theorem olg_decreasing_to_zero {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (h0 : 0 < p 0)
    (h1 : p 0 < (ωy - ωo) / (2 * M)) : StrictAnti p ∧ Tendsto p atTop (𝓝 0) := by
  rcases (olg_classification hωy hωo hM p).1 hp with h | ⟨hgap, c, hc, h⟩
  · exact absurd (h 0) h0.ne'
  have hd : 0 < ωy - ωo := by linarith
  have hl : 1 < ωy / ωo := (one_lt_div hωo).2 hgap
  have hcpos : 0 < c := by
    rcases hc.lt_or_eq with hc' | hc'
    · exact hc'
    · subst hc'
      rw [h 0] at h1
      simp only [zero_mul, add_zero] at h1
      rw [show (M * (2 / (ωy - ωo)))⁻¹ = (ωy - ωo) / (2 * M) by field_simp] at h1
      exact absurd h1 (lt_irrefl _)
  have hY : ∀ t, 0 < 2 / (ωy - ωo) + c * (ωy / ωo) ^ t := fun t => by
    have : 0 < 2 / (ωy - ωo) := div_pos two_pos hd
    positivity
  refine ⟨strictAnti_nat_of_succ_lt fun n => ?_, ?_⟩
  · rw [h n, h (n + 1)]
    apply inv_strictAnti₀ (mul_pos hM (hY n))
    apply mul_lt_mul_of_pos_left _ hM
    have : (ωy / ωo) ^ n < (ωy / ωo) ^ (n + 1) := pow_lt_pow_right₀ hl (Nat.lt_succ_self n)
    nlinarith
  · have hT : Tendsto (fun t : ℕ => M * (2 / (ωy - ωo) + c * (ωy / ωo) ^ t)) atTop atTop :=
      Tendsto.const_mul_atTop hM (tendsto_atTop_add_const_left _ _
        ((tendsto_pow_atTop_atTop_of_one_lt hl).const_mul_atTop hcpos))
    have := tendsto_inv_atTop_zero.comp hT
    exact this.congr fun t => (h t).symm

/-! ### The map of Figure 17.2 in real balances -/

/-- AKMM, p. 499: the equilibrium map in real balances, `f(m) = ω_o m/(ω_y − 2m)`. -/
noncomputable def olgMap (ωy ωo m : ℝ) : ℝ := ωo * m / (ωy - 2 * m)

/-- AKMM, p. 498: on `[0, ω_y/2)` the fixed points of the map are `0` and
`m̄ = (ω_y − ω_o)/2` (the latter a positive fixed point only when `ω_y > ω_o`). -/
theorem olg_map_fixed_iff {ωy ωo m : ℝ} (hm0 : 0 ≤ m) (hm : 2 * m < ωy) :
    olgMap ωy ωo m = m ↔ m = 0 ∨ m = (ωy - ωo) / 2 := by
  unfold olgMap
  have hp : 0 < ωy - 2 * m := by linarith
  rw [div_eq_iff hp.ne']
  constructor
  · intro h
    have : m * (2 * m - (ωy - ωo)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact Or.inl h'
    · right; linarith
  · rintro (rfl | rfl) <;> ring

/-- AKMM, p. 499: the map is strictly increasing on `[0, ω_y/2)`. -/
theorem olg_map_strictMonoOn {ωy ωo : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) :
    StrictMonoOn (olgMap ωy ωo) (Set.Ico 0 (ωy / 2)) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨-, hy1⟩ := hy
  unfold olgMap
  have h1 : 0 < ωy - 2 * x := by linarith
  have h2 : 0 < ωy - 2 * y := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith [mul_lt_mul_of_pos_left hxy (mul_pos hωo hωy)]

/-- AKMM, p. 499: the slope of the map is `f′(m) = ω_oω_y/(ω_y − 2m)²` for `2m ≠ ω_y`. -/
theorem olg_map_hasDerivAt {ωy ωo m : ℝ} (hm : ωy - 2 * m ≠ 0) :
    HasDerivAt (olgMap ωy ωo) (ωo * ωy / (ωy - 2 * m) ^ 2) m := by
  have h1 : HasDerivAt (fun x => ωo * x) ωo m :=
    ((hasDerivAt_id' m).const_mul ωo).congr_deriv (by ring)
  have h2 : HasDerivAt (fun x => ωy - 2 * x) (-2) m :=
    (HasDerivAt.const_sub ωy ((hasDerivAt_id' m).const_mul 2)).congr_deriv (by ring)
  have := h1.div h2 hm
  refine this.congr_deriv ?_
  field_simp
  ring

/-- AKMM, p. 499: the slope is `ω_o/ω_y` at `0` (below one in case (i)) and `ω_y/ω_o` at the
monetary steady state `m̄ = (ω_y − ω_o)/2` (above one in case (i)); in case (ii) the slope at
the origin is at least one. -/
theorem olg_map_slopes {ωy ωo : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) :
    HasDerivAt (olgMap ωy ωo) (ωo / ωy) 0 ∧
      HasDerivAt (olgMap ωy ωo) (ωy / ωo) ((ωy - ωo) / 2) ∧
      (ωo < ωy → ωo / ωy < 1 ∧ 1 < ωy / ωo) ∧ (ωy ≤ ωo → 1 ≤ ωo / ωy) := by
  refine ⟨?_, ?_, fun h => ⟨(div_lt_one hωy).2 h, (one_lt_div hωo).2 h⟩,
    fun h => (one_le_div hωy).2 h⟩
  · have := olg_map_hasDerivAt (ωo := ωo) (m := 0) (by simpa using hωy.ne')
    refine this.congr_deriv ?_
    rw [mul_zero, sub_zero, sq]
    field_simp
  · have := olg_map_hasDerivAt (ωy := ωy) (ωo := ωo) (m := (ωy - ωo) / 2)
      (by ring_nf; exact hωo.ne')
    refine this.congr_deriv ?_
    have : ωy - 2 * ((ωy - ωo) / 2) = ωo := by ring
    rw [this]
    field_simp

/-- AKMM, p. 499: for `p_{m,t} ≥ p̃_m = ω_y/(2M)` no positive `p_{m,t+1}` solves (17.5): next
period's price would be "infinite or negative". -/
theorem olg_map_domain {ωy ωo M pt pt1 : ℝ} (hωo : 0 < ωo) (hpt : 0 < pt) (hpt1 : 0 < pt1)
    (hge : ωy ≤ 2 * M * pt) : pt1 * (ωy - 2 * M * pt) ≠ ωo * pt := by
  intro h
  have : pt1 * (ωy - 2 * M * pt) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpt1.le (by linarith)
  nlinarith

/-- AKMM, p. 499: the equilibrium determines only the real value of the money stock: `p` is an
equilibrium with stock `M` iff `p_{m,t}M/M′` is one with stock `M′`. -/
theorem olg_nominal_neutral {ωy ωo M M' : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hM' : 0 < M') (p : ℕ → ℝ) :
    olgIsEquilibrium ωy ωo M p ↔ olgIsEquilibrium ωy ωo M' (fun t => p t * M / M') := by
  rw [eq_17_5 hωy hωo hM, eq_17_5 hωy hωo hM']
  have hk : 0 < M / M' := div_pos hM hM'
  have e : ∀ t, 2 * M' * (p t * M / M') = 2 * M * p t := fun t => by field_simp
  have e2 : ∀ t, p (t + 1) * M / M' * (ωy - 2 * M * p t) =
      M / M' * (p (t + 1) * (ωy - 2 * M * p t)) := fun t => by ring
  refine or_congr ⟨fun h t => by rw [h t]; ring, fun h t => ?_⟩
    ⟨fun h t => ⟨by have := (h t).1; positivity, ?_⟩, fun h t => ⟨?_, ?_⟩⟩
  · rcases div_eq_zero_iff.1 (h t) with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact h''
      · exact absurd h'' hM.ne'
    · exact absurd h' hM'.ne'
  · rw [e t, e2 t, (h t).2]; ring
  · have h1 := (h t).1
    rw [mul_div_assoc] at h1
    exact (mul_pos_iff_of_pos_right hk).1 h1
  · have h1 := (h t).2
    rw [e t, e2 t, show ωo * (p t * M / M') = M / M' * (ωo * p t) by ring] at h1
    exact mul_left_cancel₀ hk.ne' h1

end AKMM.Money

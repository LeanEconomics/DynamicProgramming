/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMMoney.OLGEquilibrium
import OverlappingGenerations.OXExamples

/-!
# Welfare across the equilibria of the fiat-money endowment economy

AKMM, §17.2.2, p. 500 (the comparisons the text "leave[s] as an exercise"), with the link to
Miao, Chapter 16 (the `OverlappingGenerations` dependency).

* `olgIndirect`: utility at the optimum as a function of the return, `log((Rω_y + ω_o)²/(4R))`;
  it is strictly increasing on `R ≥ ω_o/ω_y` (`olg_indirect_strictMonoOn`), the "key insight":
  a higher return on saving is better.
* `olg_cohort_util_eq`: in every equilibrium the utility of cohort `t` is
  `olgIndirect (ω_o/(ω_y − 2m_t))`, `m_t = p_{m,t}M` (autarky included).
* `olg_ranking`: equilibria are ranked by `p_{m,0}`: a larger `p_{m,0} ≤ p̄_m` gives strictly
  higher utility to every cohort and to the initial old. Hence every monetary equilibrium
  Pareto-improves on autarky (`olg_monetary_improves_autarky`) and every equilibrium other than
  the stationary monetary one is Pareto-dominated by it (`olg_stationary_dominates`).
* `olg_stationary_welfare`: the stationary utility `2 log((ω_y + ω_o)/2) > log ω_y + log ω_o`;
  `olg_smoothing_hurts_old`: for `ω_y < ω_o` the smoothed allocation would hurt the initial old.
* `olg_return_limit`: the long-run gross return is `ω_o/ω_y < 1` along non-stationary
  equilibria and `1` in the stationary one.
* The Miao link: the book's economy is Miao's Samuelson economy with log utility, `β = 1` and
  `g_n = g_m = 1` (`olgMiao`); its monetary equilibria are exactly the paths of
  `olg_classification` (`olg_miao_paths`); the stationary monetary equilibrium is Pareto optimal
  and autarky is Pareto optimal iff `ω_y ≤ ω_o` (`olg_miao_stationary_pareto`,
  `olg_miao_autarky_pareto_iff`, from Miao's Propositions 16.1.2–16.1.3).
-/

open Filter Topology Miao.OverlappingGenerations

namespace AKMM.Money

/-- AKMM, p. 500: utility at the interior optimum as a function of the gross return `R`,
`log c_y + log c_o = log((Rω_y + ω_o)²/(4R))`. -/
noncomputable def olgIndirect (ωy ωo R : ℝ) : ℝ := Real.log ((R * ωy + ωo) ^ 2 / (4 * R))

/-- At the interior optimum `olgUtil` equals `olgIndirect`; at the corner return
`R = ω_o/ω_y`, `olgIndirect` is the autarky utility `log ω_y + log ω_o`. -/
theorem olg_indirect_eq {ωy ωo R : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hR : 0 < R) :
    olgUtil ωy ωo R ((ωy - ωo / R) / 2) = olgIndirect ωy ωo R ∧
      olgIndirect ωy ωo (ωo / ωy) = Real.log ωy + Real.log ωo := by
  constructor
  · unfold olgUtil olgIndirect
    have h1 : ωy - (ωy - ωo / R) / 2 = (R * ωy + ωo) / (2 * R) := by field_simp; ring
    have h2 : ωo + R * ((ωy - ωo / R) / 2) = (R * ωy + ωo) / 2 := by field_simp; ring
    have h3 : 0 < R * ωy + ωo := by positivity
    rw [h1, h2, ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  · unfold olgIndirect
    rw [← Real.log_mul hωy.ne' hωo.ne']
    congr 1
    field_simp
    ring

/-- **AKMM, p. 500** ("a higher return on saving is better for the consumer"): the indirect
utility is strictly increasing in the return on `[ω_o/ω_y, ∞)`. -/
theorem olg_indirect_strictMonoOn {ωy ωo : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) :
    StrictMonoOn (olgIndirect ωy ωo) (Set.Ici (ωo / ωy)) := by
  intro R1 h1 R2 h2 hlt
  have h1' : ωo / ωy ≤ R1 := h1
  have hR1 : 0 < R1 := lt_of_lt_of_le (div_pos hωo hωy) h1'
  have hR2 : 0 < R2 := hR1.trans hlt
  have hk : ωo ≤ R1 * ωy := by rwa [div_le_iff₀ hωy] at h1'
  unfold olgIndirect
  apply Real.log_lt_log (by positivity)
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hk2 : ωo * ωo < (R1 * ωy) * (R2 * ωy) := by
    have : R1 * ωy < R2 * ωy := mul_lt_mul_of_pos_right hlt hωy
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left hk2 (sub_pos.2 hlt)]

/-- AKMM, p. 500: the lifetime utility of cohort `t` along a price path. -/
noncomputable def olgCohortUtil (ωy ωo M : ℝ) (p : ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.log (ωy - M * p t) + Real.log (ωo + M * p (t + 1))

/-- AKMM, p. 500: in every equilibrium the utility of cohort `t` is the indirect utility at the
return `ω_o/(ω_y − 2m_t)`, `m_t = p_{m,t}M` (in autarky `m_t = 0`, return `ω_o/ω_y`). -/
theorem olg_cohort_util_eq {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (t : ℕ) :
    olgCohortUtil ωy ωo M p t = olgIndirect ωy ωo (ωo / (ωy - 2 * (M * p t))) ∧
      2 * (M * p t) < ωy := by
  rcases (eq_17_5 hωy hωo hM p).1 hp with h | h
  · simp only [olgCohortUtil, h, mul_zero, sub_zero, add_zero]
    exact ⟨(olg_indirect_eq hωy hωo (div_pos hωo hωy)).2.symm, hωy⟩
  · obtain ⟨hlt, heq⟩ := eq_17_5_div hωo (h t).1 (h (t + 1)).1 (h t).2
    have hx := mul_pos hM (h t).1
    have hd : 0 < ωy - 2 * (M * p t) := by linarith
    refine ⟨?_, by linarith⟩
    unfold olgCohortUtil olgIndirect
    have hc1 : 0 < ωy - M * p t := by linarith
    have hc2 : 0 < ωo + M * p (t + 1) := by have := (h (t + 1)).1; positivity
    have hMp1 : M * p (t + 1) = ωo * (M * p t) / (ωy - 2 * (M * p t)) := by
      rw [heq, mul_div_assoc', show 2 * M * p t = 2 * (M * p t) by ring]; ring
    rw [← Real.log_mul hc1.ne' hc2.ne', hMp1]
    congr 1
    generalize M * p t = x at *
    have hd' := hd.ne'
    have hd2 : ωy - x * 2 ≠ 0 := by rw [mul_comm]; exact hd'
    have hωo' := hωo.ne'
    field_simp
    ring

/-- The equilibrium return `ω_o/(ω_y − 2m)` is strictly increasing in real balances
`m ∈ [0, ω_y/2)` and at least `ω_o/ω_y`. -/
theorem olg_return_strictMonoOn {ωy ωo : ℝ} (hωo : 0 < ωo) :
    StrictMonoOn (fun m => ωo / (ωy - 2 * m)) (Set.Ico 0 (ωy / 2)) ∧
      ∀ m ∈ Set.Ico 0 (ωy / 2), ωo / ωy ≤ ωo / (ωy - 2 * m) := by
  refine ⟨fun x hx y hy hxy => ?_, fun m hm => ?_⟩
  · obtain ⟨-, hy1⟩ := hy
    exact div_lt_div_of_pos_left hωo (by linarith) (by linarith)
  · obtain ⟨hm0, hm1⟩ := hm
    exact div_le_div_of_nonneg_left hωo.le (by linarith) (by linarith)

/-- **AKMM, p. 500: equilibria are ranked by the initial value of money.** If `p, p′` are
equilibria with `p_{m,0} < p′_{m,0}`, then real balances are higher under `p′` at every date,
every cohort `t ≥ 0` is strictly better off under `p′`, and so are the initial old. -/
theorem olg_ranking {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p p' : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (hp' : olgIsEquilibrium ωy ωo M p')
    (h0 : p 0 < p' 0) :
    (∀ t, p t < p' t) ∧ (∀ t, olgCohortUtil ωy ωo M p t < olgCohortUtil ωy ωo M p' t) ∧
      ωo + M * p 0 < ωo + M * p' 0 := by
  have hlt : ∀ t, p t < p' t := by
    rcases (eq_17_5 hωy hωo hM p').1 hp' with h' | h'
    · exact absurd (h' 0 ▸ h0) (not_lt.2 (hp.1 0))
    intro t
    induction t with
    | zero => exact h0
    | succ n ih =>
      rcases (eq_17_5 hωy hωo hM p).1 hp with h | h
      · rw [h]; exact (h' (n + 1)).1
      · rw [(eq_17_5_div hωo (h n).1 (h (n + 1)).1 (h n).2).2,
          (eq_17_5_div hωo (h' n).1 (h' (n + 1)).1 (h' n).2).2]
        have hm := olg_map_strictMonoOn hωy hωo
          (a := M * p n) (b := M * p' n)
          ⟨(mul_pos hM (h n).1).le, by linarith [(eq_17_5_div hωo (h n).1 (h (n + 1)).1 (h n).2).1]⟩
          ⟨(mul_pos hM (h' n).1).le,
            by linarith [(eq_17_5_div hωo (h' n).1 (h' (n + 1)).1 (h' n).2).1]⟩
          (mul_lt_mul_of_pos_left ih hM)
        unfold olgMap at hm
        have e : ∀ x, ωo * x / (ωy - 2 * M * x) = (ωo * (M * x) / (ωy - 2 * (M * x))) / M :=
          fun x => by field_simp
        rw [e, e]
        exact div_lt_div_of_pos_right hm hM
  refine ⟨hlt, fun t => ?_, by nlinarith [hlt 0]⟩
  obtain ⟨e1, l1⟩ := olg_cohort_util_eq hωy hωo hM hp t
  obtain ⟨e2, l2⟩ := olg_cohort_util_eq hωy hωo hM hp' t
  obtain ⟨hmono, hge⟩ := olg_return_strictMonoOn hωo
  have m1 : M * p t ∈ Set.Ico 0 (ωy / 2) := ⟨mul_nonneg hM.le (hp.1 t), by linarith⟩
  have m2 : M * p' t ∈ Set.Ico 0 (ωy / 2) := ⟨mul_nonneg hM.le (hp'.1 t), by linarith⟩
  rw [e1, e2]
  exact olg_indirect_strictMonoOn hωy hωo (hge _ m1) (hge _ m2)
    (hmono m1 m2 (mul_lt_mul_of_pos_left (hlt t) hM))

/-- AKMM, p. 500: every monetary equilibrium (stationary or not) is a strict Pareto improvement
on autarky: every cohort and the initial old are strictly better off. -/
theorem olg_monetary_improves_autarky {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (h0 : 0 < p 0) :
    (∀ t, Real.log ωy + Real.log ωo < olgCohortUtil ωy ωo M p t) ∧ ωo < ωo + M * p 0 := by
  have h := olg_ranking hωy hωo hM (olg_nonmonetary_exists hωy hωo hM) hp h0
  refine ⟨fun t => ?_, by simpa using h.2.2⟩
  have := h.2.1 t
  simpa [olgCohortUtil] using this

/-- AKMM, p. 500: every equilibrium with `p_{m,0} < p̄_m` (autarky and the non-stationary
monetary equilibria) is Pareto-dominated by the stationary monetary equilibrium, which is a
feasible allocation; these equilibria are therefore Pareto inefficient. -/
theorem olg_stationary_dominates {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hgap : ωo < ωy) {p : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p)
    (h0 : p 0 < (ωy - ωo) / (2 * M)) :
    (∀ t, olgCohortUtil ωy ωo M p t <
      olgCohortUtil ωy ωo M (fun _ => (ωy - ωo) / (2 * M)) t) ∧
      ωo + M * p 0 < ωo + M * ((ωy - ωo) / (2 * M)) :=
  let h := olg_ranking hωy hωo hM hp (olg_stationary hωy hωo hM hgap).2 h0
  ⟨h.2.1, h.2.2⟩

/-- AKMM, p. 500: in the stationary monetary equilibrium every cohort obtains
`2 log((ω_y + ω_o)/2)`, which exceeds autarky utility `log ω_y + log ω_o` when `ω_y ≠ ω_o`. -/
theorem olg_stationary_welfare {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hne : ωy ≠ ωo) (t : ℕ) :
    olgCohortUtil ωy ωo M (fun _ => (ωy - ωo) / (2 * M)) t = 2 * Real.log ((ωy + ωo) / 2) ∧
      Real.log ωy + Real.log ωo < 2 * Real.log ((ωy + ωo) / 2) := by
  constructor
  · unfold olgCohortUtil
    have e1 : ωy - M * ((ωy - ωo) / (2 * M)) = (ωy + ωo) / 2 := by field_simp; ring
    have e2 : ωo + M * ((ωy - ωo) / (2 * M)) = (ωy + ωo) / 2 := by field_simp; ring
    rw [e1, e2]; ring
  · rw [← Real.log_mul hωy.ne' hωo.ne', two_mul, ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_lt_log (by positivity)
    have : 0 < (ωy - ωo) ^ 2 := by positivity
    nlinarith

/-- AKMM, p. 500: when `ω_y < ω_o` the smoothed allocation `((ω_y + ω_o)/2, (ω_y + ω_o)/2)`
would make the initial old (consumption `ω_o` in autarky) worse off. -/
theorem olg_smoothing_hurts_old {ωy ωo : ℝ} (hlt : ωy < ωo) : (ωy + ωo) / 2 < ωo := by linarith

/-- AKMM, p. 500: the gross return on saving `p_{m,t+1}/p_{m,t}` tends to `ω_o/ω_y < 1` along
every equilibrium with `0 < p_{m,0} < p̄_m`, and equals `1` in the stationary one. -/
theorem olg_return_limit {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (h0 : 0 < p 0)
    (h1 : p 0 < (ωy - ωo) / (2 * M)) :
    Tendsto (fun t => p (t + 1) / p t) atTop (𝓝 (ωo / ωy)) ∧
      (ωo < ωy → (ωy - ωo) / (2 * M) / ((ωy - ωo) / (2 * M)) = 1) := by
  refine ⟨?_, fun hgap => div_self (by have h : 0 < ωy - ωo := (by linarith); positivity)⟩
  rcases (eq_17_5 hωy hωo hM p).1 hp with h | h
  · exact absurd (h 0) h0.ne'
  have hr : ∀ t, p (t + 1) / p t = ωo / (ωy - 2 * M * p t) := fun t => by
    rw [(eq_17_5_div hωo (h t).1 (h (t + 1)).1 (h t).2).2]
    field_simp [(h t).1.ne']
  simp only [hr]
  have hlim := (olg_decreasing_to_zero hωy hωo hM hp h0 h1).2
  have : Tendsto (fun t => ωy - 2 * M * p t) atTop (𝓝 (ωy - 2 * M * 0)) :=
    tendsto_const_nhds.sub (hlim.const_mul (2 * M))
  rw [mul_zero, sub_zero] at this
  exact (tendsto_const_nhds.div this hωy.ne')

/-! ### The link with Miao, Chapter 16 -/

/-- AKMM, §17.2.1 as Miao's Samuelson economy (Miao, §16.1): log utility with `β = 1`,
endowments `(ω_y, ω_o)`, no population or money growth, one agent per cohort, stock `M`. -/
noncomputable def olgMiao (ωy ωo M : ℝ) (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M) :
    OXEconomy where
  ox_P := ox_logPrefs 1 one_pos le_rfl
  ox_e1 := ωy
  ox_e2 := ωo
  ox_gn := 1
  ox_gm := 1
  ox_N0 := 1
  ox_M0 := M
  ox_e1_pos := hωy
  ox_e2_pos := hωo
  ox_gn_pos := one_pos
  ox_gm_pos := one_pos
  ox_N0_pos := one_pos
  ox_M0_pos := hM

/-- The book's model matches Miao's: every monetary equilibrium of `olgMiao` (Miao's notion,
dates `t ≥ 1`) has real balances `m̂_{n+1} = 1/(2/(ω_y − ω_o) + c(ω_y/ω_o)ⁿ)`, `c ≥ 0`, and
`ω_y > ω_o` — the paths of `olg_classification`. -/
theorem olg_miao_paths {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {q cy co m : ℕ → ℝ} (h : (olgMiao ωy ωo M hωy hωo hM).ox_IsMonetary q cy co m) :
    ωo < ωy ∧ ∃ c, 0 ≤ c ∧ ∀ n : ℕ, ((olgMiao ωy ωo M hωy hωo hM).ox_mhat q (n + 1))⁻¹ =
      2 / (ωy - ωo) + c * (ωy / ωo) ^ n := by
  have := (olgMiao ωy ωo M hωy hωo hM).ox_log_paths rfl rfl rfl h
  simpa [olgMiao] using this

/-- AKMM, p. 500 (via Miao's Proposition 16.1.3): for `ω_y > ω_o` the stationary monetary
equilibrium allocation `c_y = (ω_y + ω_o)/2 = c_o` is Pareto optimal. -/
theorem olg_miao_stationary_pareto {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hgap : ωo < ωy) :
    (olgMiao ωy ωo M hωy hωo hM).ox_ParetoOptimal (fun _ => (ωy + ωo) / 2)
      (fun _ => (ωy + ωo) / 2) := by
  set E := olgMiao ωy ωo M hωy hωo hM
  have hgap' : E.ox_e2 < E.ox_gn * E.ox_e1 := by simp [E, olgMiao, hgap]
  have hc := E.ox_log_construct rfl rfl rfl hgap' le_rfl
  have hd : ωy - ωo ≠ 0 := by linarith
  have e1 : ∀ t : ℕ, E.ox_e1 - (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
      0 * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t - 1))⁻¹ = (ωy + ωo) / 2 := fun t => by
    simp only [E, olgMiao, zero_mul, add_zero, one_mul, mul_one]
    field_simp; ring
  have e2 : ∀ t : ℕ, E.ox_e2 + E.ox_gn * (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
      0 * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t + 1 - 1))⁻¹ = (ωy + ωo) / 2 := fun t => by
    simp only [E, olgMiao, zero_mul, add_zero, one_mul, mul_one]
    field_simp; ring
  simp only [e1, e2] at hc
  have hR : E.ox_Raut * E.ox_gm < E.ox_gn := by
    rw [E.ox_log_Raut rfl rfl]
    simp only [E, olgMiao, mul_one]
    exact (div_lt_one hωy).2 hgap
  exact (E.proposition_16_1_3 hR hc (fun _ _ => ⟨rfl, rfl⟩)).2 le_rfl

/-- AKMM, p. 500 (via Miao's Proposition 16.1.2): the autarky allocation is Pareto optimal iff
`ω_y ≤ ω_o`; in particular it is inefficient whenever money can be valued. -/
theorem olg_miao_autarky_pareto_iff {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M) :
    (olgMiao ωy ωo M hωy hωo hM).ox_ParetoOptimal (fun _ => ωy) (fun _ => ωo) ↔ ωy ≤ ωo := by
  set E := olgMiao ωy ωo M hωy hωo hM
  refine (E.proposition_16_1_2 E.ox_autarky_isEquilibrium).trans ?_
  rw [E.ox_log_Raut rfl rfl]
  exact one_le_div hωy

end AKMM.Money

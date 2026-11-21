/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.OXPreferences

/-!
# The Samuelson (1958) exchange economy with fiat money

Miao, §16.1, pp. 530–532: two-period-lived agents, `N_t = g_n N_{t−1}` young at `t`, endowments
`(e₁, e₂)`, money supply `M_t = g_m M_{t−1}` distributed as lump-sum transfers to the old.

* `OXEconomy`: the primitives (`OXPrefs`, `e₁, e₂, g_n, g_m, N₀, M₀ > 0`); `ox_N`, `ox_M`.
* The value of money `q_t = 1/p_t ≥ 0` (`q_t = 0` is the book's `p_t = ∞`). Budget sets
  (16.1)–(16.2) (`ox_Budget`, `eq_16_1_16_2` in the book's price form), optimal choices
  (`ox_Optimal`), the initial old (`ox_OldOptimal`, `ox_oldOptimal_iff`), equilibrium with the
  market-clearing conditions (16.3) (`ox_IsEquilibrium`), monetary and nonmonetary equilibria.
* Autarky is the unique nonmonetary equilibrium (`ox_autarky_isEquilibrium`,
  `ox_nonmonetary_autarky`).
* The Euler equation (16.4) (`eq_16_4`), the autarky interest rate (16.5) (`ox_Raut`,
  `eq_16_5`: the unique gross rate at which `(e₁, e₂)` is optimal), equilibrium consumption
  `c_t^t = e₁ − m̂_t`, `c_{t+1}^t = e₂ + g_n m̂_{t+1}` and (16.6) (`ox_monetary_alloc`,
  `eq_16_6`), (16.7) (`eq_16_7`).
* The equilibrium difference equation in saving: every sequence `m̂_t ∈ (0, e₁)` solving
  `u'(e₁ − m̂_t) = β(g_n m̂_{t+1}/(g_m m̂_t))u'(e₂ + g_n m̂_{t+1})` is a monetary equilibrium
  (`ox_ofSaving_isMonetary`), and every monetary equilibrium arises this way.

**Departures.** (i) The initial old's budget is printed with `y₂`; it is `e₂`. (ii) In a
nonmonetary equilibrium money holdings are indeterminate (money has no value); we let the young
hold the money stock so that `M_t = N_t m_t^t` still holds, where the book writes `m_t^t = 0`.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- Miao, §16.1, pp. 530–531: the primitives of the Samuelson exchange economy. -/
structure OXEconomy where
  /-- Preferences. -/
  ox_P : OXPrefs
  /-- Endowment of the young. -/
  ox_e1 : ℝ
  /-- Endowment of the old. -/
  ox_e2 : ℝ
  /-- Population growth factor `g_n`. -/
  ox_gn : ℝ
  /-- Money growth factor `g_m`. -/
  ox_gm : ℝ
  /-- Initial old population `N₀`. -/
  ox_N0 : ℝ
  /-- Initial money stock `M₀ = N₀ m₀⁰`. -/
  ox_M0 : ℝ
  ox_e1_pos : 0 < ox_e1
  ox_e2_pos : 0 < ox_e2
  ox_gn_pos : 0 < ox_gn
  ox_gm_pos : 0 < ox_gm
  ox_N0_pos : 0 < ox_N0
  ox_M0_pos : 0 < ox_M0

/-- A concrete economy (log utility, `β = 1`, `e = (2, 1)`, `g_n = g_m = N₀ = M₀ = 1`): the
hypotheses of `OXEconomy` are satisfiable. -/
noncomputable def ox_exampleEconomy : OXEconomy where
  ox_P := ox_logPrefs 1 one_pos le_rfl
  ox_e1 := 2
  ox_e2 := 1
  ox_gn := 1
  ox_gm := 1
  ox_N0 := 1
  ox_M0 := 1
  ox_e1_pos := two_pos
  ox_e2_pos := one_pos
  ox_gn_pos := one_pos
  ox_gm_pos := one_pos
  ox_N0_pos := one_pos
  ox_M0_pos := one_pos

/-- The example economy has `e₁ = 2`, `e₂ = 1`. -/
theorem ox_exampleEconomy_spec : ox_exampleEconomy.ox_e1 = 2 ∧ ox_exampleEconomy.ox_e2 = 1 :=
  ⟨rfl, rfl⟩

namespace OXEconomy

variable (E : OXEconomy)

/-- Population of generation `t`: `N_t = N₀ g_nᵗ`. -/
def ox_N (t : ℕ) : ℝ := E.ox_N0 * E.ox_gn ^ t

/-- Money stock after the date-`t` transfer: `M_t = M₀ g_mᵗ`. -/
def ox_M (t : ℕ) : ℝ := E.ox_M0 * E.ox_gm ^ t

/-- The per-capita transfer to an old agent of generation `t` (in money): `(g_m − 1)M_t/N_t`. -/
noncomputable def ox_τ (t : ℕ) : ℝ := (E.ox_gm - 1) * E.ox_M t / E.ox_N t

/-- Lifetime utility. -/
def ox_EU (c1 c2 : ℝ) : ℝ := E.ox_P.ox_U c1 c2

/-- Miao, (16.5), p. 531: the autarky interest rate `R_aut = u'(e₁)/(βu'(e₂))`. -/
noncomputable def ox_Raut : ℝ := E.ox_P.ox_du E.ox_e1 / (E.ox_P.ox_β * E.ox_P.ox_du E.ox_e2)

/-- Miao, (16.1)–(16.2), p. 531, with `q_t = 1/p_t` the value of money: the budget set of a
young agent of generation `t ≥ 1` (consumption positive). -/
def ox_Budget (q : ℕ → ℝ) (t : ℕ) (c1 c2 m : ℝ) : Prop :=
  0 ≤ m ∧ 0 < c1 ∧ 0 < c2 ∧ c1 + q t * m ≤ E.ox_e1 ∧
    c2 ≤ E.ox_e2 + q (t + 1) * m + q (t + 1) * E.ox_τ t

/-- Optimal choice of generation `t`: in the budget set and utility-maximal there. -/
def ox_Optimal (q : ℕ → ℝ) (t : ℕ) (c1 c2 m : ℝ) : Prop :=
  E.ox_Budget q t c1 c2 m ∧
    ∀ c1' c2' m', E.ox_Budget q t c1' c2' m' → E.ox_EU c1' c2' ≤ E.ox_EU c1 c2

/-- Miao, p. 531: the initial old's resources `e₂ + m₀⁰/p₁ + (g_m − 1)M₀/(N₀p₁)`. -/
noncomputable def ox_oldBudget (q : ℕ → ℝ) : ℝ :=
  E.ox_e2 + q 1 * (E.ox_M0 / E.ox_N0) + q 1 * ((E.ox_gm - 1) * E.ox_M0 / E.ox_N0)

/-- The initial old maximise `u(c₁⁰)` subject to their budget. -/
def ox_OldOptimal (q : ℕ → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ c ≤ E.ox_oldBudget q ∧
    ∀ c', 0 < c' → c' ≤ E.ox_oldBudget q → E.ox_P.ox_u c' ≤ E.ox_P.ox_u c

/-- Miao, p. 531: an equilibrium. `q_t ≥ 0` is the value of money at `t ≥ 1`, `cy t = c_t^t`,
`co t = c_{t+1}^t` (so `co 0 = c₁⁰` is the initial old's consumption), `m t = m_t^t`. Every
generation optimises, money and goods markets clear (16.3). -/
def ox_IsEquilibrium (q cy co m : ℕ → ℝ) : Prop :=
  (∀ t, 1 ≤ t → 0 ≤ q t) ∧ (∀ t, 1 ≤ t → E.ox_Optimal q t (cy t) (co t) (m t)) ∧
    E.ox_OldOptimal q (co 0) ∧ (∀ t, 1 ≤ t → E.ox_M t = E.ox_N t * m t) ∧
    ∀ t, 1 ≤ t → E.ox_N t * cy t + E.ox_N (t - 1) * co (t - 1) =
      E.ox_N t * E.ox_e1 + E.ox_N (t - 1) * E.ox_e2

/-- Miao, p. 531: a monetary equilibrium (finite positive prices: `q_t > 0` for all `t ≥ 1`). -/
def ox_IsMonetary (q cy co m : ℕ → ℝ) : Prop :=
  E.ox_IsEquilibrium q cy co m ∧ ∀ t, 1 ≤ t → 0 < q t

/-- Miao, p. 531: a nonmonetary equilibrium (`p_t = ∞`, i.e. `q_t = 0`). -/
def ox_IsNonmonetary (q cy co m : ℕ → ℝ) : Prop :=
  E.ox_IsEquilibrium q cy co m ∧ ∀ t, 1 ≤ t → q t = 0

/-- Miao, p. 532: real balances per young `m̂_t = M_t/(N_t p_t) = q_t M_t/N_t`. -/
noncomputable def ox_mhat (q : ℕ → ℝ) (t : ℕ) : ℝ := q t * E.ox_M t / E.ox_N t

theorem ox_N_pos (t : ℕ) : 0 < E.ox_N t := mul_pos E.ox_N0_pos (pow_pos E.ox_gn_pos t)

theorem ox_M_pos (t : ℕ) : 0 < E.ox_M t := mul_pos E.ox_M0_pos (pow_pos E.ox_gm_pos t)

theorem ox_N_succ (t : ℕ) : E.ox_N (t + 1) = E.ox_N t * E.ox_gn := by
  simp only [ox_N, pow_succ]; ring

theorem ox_M_succ (t : ℕ) : E.ox_M (t + 1) = E.ox_M t * E.ox_gm := by
  simp only [ox_M, pow_succ]; ring

/-- Miao, (16.1)–(16.2), p. 531: in the book's price notation `p_t = 1/q_t > 0`, the budget set
is `c_t^t + m_t^t/p_t ≤ e₁`, `c_{t+1}^t ≤ e₂ + m_t^t/p_{t+1} + (g_m − 1)M_t/(N_t p_{t+1})`. -/
theorem eq_16_1_16_2 (p : ℕ → ℝ) (t : ℕ) (c1 c2 m : ℝ) :
    E.ox_Budget (fun s => 1 / p s) t c1 c2 m ↔
      0 ≤ m ∧ 0 < c1 ∧ 0 < c2 ∧ c1 + m / p t ≤ E.ox_e1 ∧
        c2 ≤ E.ox_e2 + m / p (t + 1) + (E.ox_gm - 1) * E.ox_M t / (E.ox_N t * p (t + 1)) := by
  unfold ox_Budget ox_τ
  have h1 : 1 / p t * m = m / p t := by ring
  have h2 : 1 / p (t + 1) * m = m / p (t + 1) := by ring
  have h3 : 1 / p (t + 1) * ((E.ox_gm - 1) * E.ox_M t / E.ox_N t) =
      (E.ox_gm - 1) * E.ox_M t / (E.ox_N t * p (t + 1)) := by
    rw [div_mul_div_comm, one_mul, mul_comm (p (t + 1))]
  rw [h1, h2, h3]

/-- Miao, p. 531: since `u` is strictly increasing, the initial old consume their resources:
`c₁⁰ = e₂ + m₀⁰/p₁ + (g_m − 1)M₀/(N₀p₁)`. -/
theorem ox_oldOptimal_iff (q : ℕ → ℝ) (hb : 0 < E.ox_oldBudget q) (c : ℝ) :
    E.ox_OldOptimal q c ↔ c = E.ox_oldBudget q := by
  constructor
  · rintro ⟨hc, hcb, hmax⟩
    by_contra hne
    have hlt : c < E.ox_oldBudget q := lt_of_le_of_ne hcb hne
    exact absurd (hmax _ hb le_rfl) (not_le.2 (E.ox_P.ox_u_lt hc hlt))
  · rintro rfl
    exact ⟨hb, le_rfl, fun c' hc' hcb => E.ox_P.ox_u_strictMonoOn.monotoneOn hc' hb hcb⟩

/-- An optimal choice exhausts both budget constraints (`u` is strictly increasing). -/
theorem ox_optimal_binds {q : ℕ → ℝ} {t : ℕ} {c1 c2 m : ℝ} (h : E.ox_Optimal q t c1 c2 m) :
    c1 = E.ox_e1 - q t * m ∧ c2 = E.ox_e2 + q (t + 1) * m + q (t + 1) * E.ox_τ t := by
  obtain ⟨⟨hm, h1, h2, hb1, hb2⟩, hmax⟩ := h
  constructor
  · by_contra hne
    have hlt : c1 < E.ox_e1 - q t * m := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · linarith
    have := hmax (E.ox_e1 - q t * m) c2 m ⟨hm, by linarith, h2, by linarith, hb2⟩
    have hu := E.ox_P.ox_u_lt h1 hlt
    unfold ox_EU OXPrefs.ox_U at this
    linarith
  · by_contra hne
    have hlt : c2 < E.ox_e2 + q (t + 1) * m + q (t + 1) * E.ox_τ t := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · linarith
    have := hmax c1 _ m ⟨hm, h1, by linarith, hb1, le_rfl⟩
    have hu := mul_lt_mul_of_pos_left (E.ox_P.ox_u_lt h2 hlt) E.ox_P.ox_β_pos
    unfold ox_EU OXPrefs.ox_U at this
    linarith

/-- Miao, p. 531: autarky with valueless money (`p_t = ∞`) is an equilibrium, the nonmonetary
equilibrium. -/
theorem ox_autarky_isEquilibrium :
    E.ox_IsNonmonetary (fun _ => 0) (fun _ => E.ox_e1) (fun _ => E.ox_e2)
      (fun t => E.ox_M t / E.ox_N t) := by
  have hb : E.ox_oldBudget (fun _ => 0) = E.ox_e2 := by simp [ox_oldBudget]
  refine ⟨⟨fun _ _ => le_rfl, fun t _ => ⟨⟨?_, E.ox_e1_pos, E.ox_e2_pos, by simp, by simp⟩, ?_⟩,
    (E.ox_oldOptimal_iff _ (by rw [hb]; exact E.ox_e2_pos) _).2 hb.symm, fun t _ => ?_,
    fun t _ => rfl⟩, fun _ _ => rfl⟩
  · exact (div_pos (E.ox_M_pos t) (E.ox_N_pos t)).le
  · rintro c1' c2' m' ⟨_, h1, h2, hb1, hb2⟩
    simp only [zero_mul, add_zero] at hb1 hb2
    have u1 := E.ox_P.ox_u_strictMonoOn.monotoneOn h1 E.ox_e1_pos hb1
    have u2 := E.ox_P.ox_u_strictMonoOn.monotoneOn h2 E.ox_e2_pos hb2
    unfold ox_EU OXPrefs.ox_U
    nlinarith [E.ox_P.ox_β_pos]
  · field_simp [(E.ox_N_pos t).ne']

/-- Miao, p. 531: in every nonmonetary equilibrium the allocation is autarky,
`c_t^t = e₁`, `c_{t+1}^t = e₂` (`t ≥ 1`) and `c₁⁰ = e₂`. -/
theorem ox_nonmonetary_autarky {q cy co m : ℕ → ℝ} (h : E.ox_IsNonmonetary q cy co m) :
    (∀ t, 1 ≤ t → cy t = E.ox_e1 ∧ co t = E.ox_e2) ∧ co 0 = E.ox_e2 := by
  obtain ⟨⟨_, hopt, hold, _, _⟩, hq⟩ := h
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := E.ox_optimal_binds (hopt t ht)
    simp only [hq t ht, hq (t + 1) (by omega), zero_mul, sub_zero, add_zero] at h1 h2
    exact ⟨h1, h2⟩
  · have hb : E.ox_oldBudget q = E.ox_e2 := by simp [ox_oldBudget, hq 1 le_rfl]
    rw [E.ox_oldOptimal_iff q (by rw [hb]; exact E.ox_e2_pos)] at hold
    rw [hold, hb]

/-- Real balances per young in terms of individual holdings: `m̂_t = q_t m_t^t` when the money
market clears. -/
theorem ox_mhat_eq {q m : ℕ → ℝ} {t : ℕ} (hclear : E.ox_M t = E.ox_N t * m t) :
    E.ox_mhat q t = q t * m t := by
  unfold ox_mhat; rw [hclear]; field_simp [(E.ox_N_pos t).ne']

/-- The old's resources in terms of next period's real balances: with `m_t^t = M_t/N_t`,
`e₂ + q_{t+1}m_t^t + q_{t+1}(g_m − 1)M_t/N_t = e₂ + g_n m̂_{t+1}`. -/
theorem ox_old_resources (q : ℕ → ℝ) (t : ℕ) :
    E.ox_e2 + q (t + 1) * (E.ox_M t / E.ox_N t) + q (t + 1) * E.ox_τ t =
      E.ox_e2 + E.ox_gn * E.ox_mhat q (t + 1) := by
  unfold ox_mhat ox_τ
  rw [E.ox_M_succ, E.ox_N_succ]
  have := (E.ox_N_pos t).ne'
  have := E.ox_gn_pos.ne'
  field_simp
  ring

/-- The initial old's resources: `c₁⁰ = e₂ + g_n m̂₁`. -/
theorem ox_oldBudget_eq (q : ℕ → ℝ) : E.ox_oldBudget q = E.ox_e2 + E.ox_gn * E.ox_mhat q 1 := by
  have h := E.ox_old_resources q 0
  simp only [ox_N, ox_M, ox_τ, pow_zero, mul_one, zero_add] at h
  rw [← h]; unfold ox_oldBudget; ring

/-- Miao, p. 532: in a monetary equilibrium `m_t^t = M_t/N_t > 0`, `m̂_t ∈ (0, e₁)`,
`c_t^t = e₁ − m̂_t`, `c_{t+1}^t = e₂ + g_n m̂_{t+1}` (`t ≥ 1`) and `c₁⁰ = e₂ + g_n m̂₁`. -/
theorem ox_monetary_alloc {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) :
    (∀ t, 1 ≤ t → m t = E.ox_M t / E.ox_N t ∧ 0 < E.ox_mhat q t ∧ E.ox_mhat q t < E.ox_e1 ∧
      cy t = E.ox_e1 - E.ox_mhat q t ∧ co t = E.ox_e2 + E.ox_gn * E.ox_mhat q (t + 1)) ∧
      co 0 = E.ox_e2 + E.ox_gn * E.ox_mhat q 1 := by
  obtain ⟨⟨_, hopt, hold, hclear, _⟩, hq⟩ := h
  refine ⟨fun t ht => ?_, ?_⟩
  · have hm : m t = E.ox_M t / E.ox_N t := by
      rw [hclear t ht]; field_simp [(E.ox_N_pos t).ne']
    have hmh := E.ox_mhat_eq (q := q) (hclear t ht)
    obtain ⟨h1, h2⟩ := E.ox_optimal_binds (hopt t ht)
    have hc1 := (hopt t ht).1.2.1
    have hpos : 0 < E.ox_mhat q t := by
      unfold ox_mhat; exact div_pos (mul_pos (hq t ht) (E.ox_M_pos t)) (E.ox_N_pos t)
    refine ⟨hm, hpos, by linarith, by rw [h1, hmh], ?_⟩
    rw [h2, hm, E.ox_old_resources]
  · have hb : 0 < E.ox_oldBudget q := by
      rw [E.ox_oldBudget_eq]
      have : 0 < E.ox_mhat q 1 := by
        unfold ox_mhat; exact div_pos (mul_pos (hq 1 le_rfl) (E.ox_M_pos 1)) (E.ox_N_pos 1)
      nlinarith [E.ox_e2_pos, E.ox_gn_pos]
    rw [(E.ox_oldOptimal_iff q hb _).1 hold, E.ox_oldBudget_eq]

/-- Miao, (16.4), p. 531: in a monetary equilibrium the Euler equation
`u'(c_t^t)/(βu'(c_{t+1}^t)) = p_t/p_{t+1} = R_{t+1}` holds, with `p_t/p_{t+1} = q_{t+1}/q_t`. -/
theorem eq_16_4 {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {t : ℕ} (ht : 1 ≤ t) :
    E.ox_P.ox_du (cy t) / (E.ox_P.ox_β * E.ox_P.ox_du (co t)) = q (t + 1) / q t := by
  have hopt := h.1.2.1 t ht
  have hqt := h.2 t ht
  have hqt1 := h.2 (t + 1) (by omega)
  obtain ⟨hm, hmpos, -, -, -⟩ := (E.ox_monetary_alloc h).1 t ht
  obtain ⟨b1, b2⟩ := E.ox_optimal_binds hopt
  obtain ⟨⟨_, h1, h2, _, _⟩, hmax⟩ := hopt
  have hmt : 0 < m t := by rw [hm]; exact div_pos (E.ox_M_pos t) (E.ox_N_pos t)
  have hfoc := E.ox_P.ox_foc (a := q t) (b := q (t + 1)) h1 h2 (by
    filter_upwards [OXPrefs.ox_eventually_pos (cy t) (-q t) h1,
      OXPrefs.ox_eventually_pos (co t) (q (t + 1)) h2,
      OXPrefs.ox_eventually_pos (m t) 1 hmt] with s hs1 hs2 hs3
    refine hmax _ _ (m t + s) ⟨by linarith, by linarith, hs2, ?_, ?_⟩
    · linarith
    · linarith)
  have hd1 := E.ox_P.ox_du_pos _ h1
  have hd2 := E.ox_P.ox_du_pos _ h2
  have hβ := E.ox_P.ox_β_pos
  rw [div_eq_div_iff (by positivity) hqt.ne']
  linarith

/-- Miao, (16.5), p. 531: `R_aut = u'(e₁)/(βu'(e₂))` is the implicit interest rate of the
nonmonetary equilibrium: for a gross rate `R > 0`, autarky `(e₁, e₂)` maximises utility on the
budget line `c₁ + c₂/R ≤ e₁ + e₂/R` iff `R = R_aut`. -/
theorem eq_16_5 {R : ℝ} (hR : 0 < R) :
    (∀ c1 c2, 0 < c1 → 0 < c2 → c1 + c2 / R ≤ E.ox_e1 + E.ox_e2 / R →
      E.ox_EU c1 c2 ≤ E.ox_EU E.ox_e1 E.ox_e2) ↔ R = E.ox_Raut := by
  have hd1 := E.ox_P.ox_du_pos _ E.ox_e1_pos
  have hd2 := E.ox_P.ox_du_pos _ E.ox_e2_pos
  have hβ := E.ox_P.ox_β_pos
  constructor
  · intro hmax
    have hfoc := E.ox_P.ox_foc (a := 1) (b := R) E.ox_e1_pos E.ox_e2_pos (by
      filter_upwards [OXPrefs.ox_eventually_pos E.ox_e1 (-1) E.ox_e1_pos,
        OXPrefs.ox_eventually_pos E.ox_e2 R E.ox_e2_pos] with s hs1 hs2
      refine hmax _ _ (by linarith) hs2 (le_of_eq ?_)
      field_simp; ring)
    unfold ox_Raut
    rw [eq_div_iff (by positivity)]
    linarith
  · intro hRe c1 c2 h1 h2 hline
    refine E.ox_P.ox_line_optimal E.ox_e1_pos E.ox_e2_pos hR ?_ h1 h2 hline
    rw [hRe]; unfold ox_Raut; field_simp

/-- Miao, (16.7), p. 538: `R_{t+1} = p_t/p_{t+1} = g_n m̂_{t+1}/(g_m m̂_t)` whenever `q_t > 0`. -/
theorem eq_16_7 (q : ℕ → ℝ) {t : ℕ} (hq : 0 < q t) :
    q (t + 1) / q t = E.ox_gn * E.ox_mhat q (t + 1) / (E.ox_gm * E.ox_mhat q t) := by
  unfold ox_mhat
  rw [E.ox_M_succ, E.ox_N_succ]
  have := (E.ox_N_pos t).ne'
  have := (E.ox_M_pos t).ne'
  have := E.ox_gn_pos.ne'
  have := E.ox_gm_pos.ne'
  have := hq.ne'
  field_simp

/-- Ratio bound used in (16.6): `u'(e₁ − a)/(βu'(e₂ + b)) > R_aut` for `0 < a < e₁`, `b > 0`. -/
theorem ox_Raut_lt {a b : ℝ} (ha : 0 < a) (hae : a < E.ox_e1) (hb : 0 < b) :
    E.ox_Raut < E.ox_P.ox_du (E.ox_e1 - a) / (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + b)) := by
  have hd1 := E.ox_P.ox_du_lt (x := E.ox_e1 - a) (y := E.ox_e1) (by linarith) (by linarith)
  have hd2 := E.ox_P.ox_du_lt (x := E.ox_e2) (y := E.ox_e2 + b) E.ox_e2_pos (by linarith)
  have p1 := E.ox_P.ox_du_pos _ E.ox_e1_pos
  have p2 := E.ox_P.ox_du_pos _ (show 0 < E.ox_e2 + b by linarith [E.ox_e2_pos])
  have p3 := E.ox_P.ox_du_pos _ E.ox_e2_pos
  have hβ := E.ox_P.ox_β_pos
  unfold ox_Raut
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have : E.ox_P.ox_du E.ox_e1 * E.ox_P.ox_du (E.ox_e2 + b) <
      E.ox_P.ox_du (E.ox_e1 - a) * E.ox_P.ox_du E.ox_e2 := by nlinarith
  nlinarith

/-- Miao, (16.6), p. 532: in a monetary equilibrium,
`u'(e₁ − m̂_t)/(βu'(e₂ + g_n m̂_{t+1})) = R_{t+1} > R_aut` for all `t ≥ 1`. -/
theorem eq_16_6 {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {t : ℕ} (ht : 1 ≤ t) :
    E.ox_P.ox_du (E.ox_e1 - E.ox_mhat q t) /
        (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * E.ox_mhat q (t + 1))) = q (t + 1) / q t ∧
      E.ox_Raut < q (t + 1) / q t := by
  obtain ⟨-, hpos, hlt, hcy, hco⟩ := (E.ox_monetary_alloc h).1 t ht
  obtain ⟨-, hpos1, -, -, -⟩ := (E.ox_monetary_alloc h).1 (t + 1) (by omega)
  have he := E.eq_16_4 h ht
  rw [hcy, hco] at he
  exact ⟨he, he ▸ E.ox_Raut_lt hpos hlt (mul_pos E.ox_gn_pos hpos1)⟩

/-- The Euler relation of the saving difference equation: `a, b ∈ (0, e₁)` and
`u'(e₁ − a) = β(g_n b/(g_m a))u'(e₂ + g_n b)`. -/
def ox_EulerRel (a b : ℝ) : Prop :=
  0 < a ∧ a < E.ox_e1 ∧ 0 < b ∧ b < E.ox_e1 ∧
    E.ox_P.ox_du (E.ox_e1 - a) =
      E.ox_P.ox_β * (E.ox_gn * b / (E.ox_gm * a)) * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * b)

/-- The value of money implied by a saving path: `q_t = m̂_t N_t/M_t`. -/
noncomputable def ox_qOf (mh : ℕ → ℝ) (t : ℕ) : ℝ := mh t * E.ox_N t / E.ox_M t

theorem ox_mhat_qOf (mh : ℕ → ℝ) (t : ℕ) : E.ox_mhat (E.ox_qOf mh) t = mh t := by
  unfold ox_mhat ox_qOf
  field_simp [(E.ox_N_pos t).ne', (E.ox_M_pos t).ne']

/-- The young's budget line at positive money values: every choice in the budget set satisfies
`c₁ + c₂/R ≤ e₁ + (e₂ + q_{t+1}τ_t)/R`, `R = q_{t+1}/q_t`. -/
theorem ox_budget_line {q : ℕ → ℝ} {t : ℕ} (hq : 0 < q t) (hq1 : 0 < q (t + 1)) {c1 c2 m : ℝ}
    (hb : E.ox_Budget q t c1 c2 m) :
    c1 + c2 / (q (t + 1) / q t) ≤
      E.ox_e1 + (E.ox_e2 + q (t + 1) * E.ox_τ t) / (q (t + 1) / q t) := by
  obtain ⟨_, _, _, hb1, hb2⟩ := hb
  have hR : 0 < q (t + 1) / q t := div_pos hq1 hq
  have : c2 / (q (t + 1) / q t) ≤ (E.ox_e2 + q (t + 1) * m + q (t + 1) * E.ox_τ t) /
      (q (t + 1) / q t) := div_le_div_of_nonneg_right hb2 hR.le
  have he : (E.ox_e2 + q (t + 1) * m + q (t + 1) * E.ox_τ t) / (q (t + 1) / q t) =
      (E.ox_e2 + q (t + 1) * E.ox_τ t) / (q (t + 1) / q t) + q t * m := by
    field_simp; ring
  linarith

/-- Miao, pp. 531–532 (the equilibrium difference equation in saving): every sequence `m̂_t` with
`ox_EulerRel (m̂_t) (m̂_{t+1})` for all `t ≥ 1` is a monetary equilibrium, with
`q_t = m̂_t N_t/M_t`,
`c_t^t = e₁ − m̂_t`, `c_{t+1}^t = e₂ + g_n m̂_{t+1}`, `m_t^t = M_t/N_t`. -/
theorem ox_ofSaving_isMonetary {mh : ℕ → ℝ}
    (hrel : ∀ t, 1 ≤ t → E.ox_EulerRel (mh t) (mh (t + 1))) :
    E.ox_IsMonetary (E.ox_qOf mh) (fun t => E.ox_e1 - mh t)
      (fun t => E.ox_e2 + E.ox_gn * mh (t + 1)) (fun t => E.ox_M t / E.ox_N t) := by
  have hq : ∀ t, 1 ≤ t → 0 < E.ox_qOf mh t := fun t ht =>
    div_pos (mul_pos (hrel t ht).1 (E.ox_N_pos t)) (E.ox_M_pos t)
  have hco : ∀ t, 0 < E.ox_e2 + E.ox_gn * mh (t + 1) := fun t => by
    have := (hrel (t + 1) (by omega)).1
    nlinarith [E.ox_e2_pos, E.ox_gn_pos]
  have hres : ∀ t, E.ox_e2 + E.ox_qOf mh (t + 1) * (E.ox_M t / E.ox_N t) +
      E.ox_qOf mh (t + 1) * E.ox_τ t = E.ox_e2 + E.ox_gn * mh (t + 1) := fun t => by
    rw [E.ox_old_resources, E.ox_mhat_qOf]
  have hyoung : ∀ t, E.ox_qOf mh t * (E.ox_M t / E.ox_N t) = mh t := fun t => by
    rw [← E.ox_mhat_qOf mh t]; unfold ox_mhat; ring
  refine ⟨⟨fun t ht => (hq t ht).le, fun t ht => ?_, ?_, fun t _ => ?_, fun t ht => ?_⟩, hq⟩
  · obtain ⟨h0, he, -, -, heul⟩ := hrel t ht
    have hb : E.ox_Budget (E.ox_qOf mh) t (E.ox_e1 - mh t) (E.ox_e2 + E.ox_gn * mh (t + 1))
        (E.ox_M t / E.ox_N t) :=
      ⟨(div_pos (E.ox_M_pos t) (E.ox_N_pos t)).le, by linarith, hco t,
        by rw [hyoung]; linarith, by rw [hres]⟩
    refine ⟨hb, fun c1' c2' m' hb' => ?_⟩
    have hqt := hq t ht
    have hqt1 := hq (t + 1) (by omega)
    have hR : 0 < E.ox_qOf mh (t + 1) / E.ox_qOf mh t := div_pos hqt1 hqt
    have hReq := E.eq_16_7 (E.ox_qOf mh) hqt
    rw [E.ox_mhat_qOf, E.ox_mhat_qOf] at hReq
    refine E.ox_P.ox_line_optimal (by linarith) (hco t) hR ?_ hb'.2.1 hb'.2.2.1 ?_
    · rw [hReq]; exact heul
    · have hl := E.ox_budget_line hqt hqt1 hb'
      have he2 : E.ox_e1 + (E.ox_e2 + E.ox_qOf mh (t + 1) * E.ox_τ t) /
          (E.ox_qOf mh (t + 1) / E.ox_qOf mh t) = (E.ox_e1 - mh t) +
          (E.ox_e2 + E.ox_gn * mh (t + 1)) / (E.ox_qOf mh (t + 1) / E.ox_qOf mh t) := by
        rw [← hres t, ← hyoung t]
        field_simp
        ring
      linarith
  · have hpos : 0 < E.ox_oldBudget (E.ox_qOf mh) := by
      rw [E.ox_oldBudget_eq, E.ox_mhat_qOf]; exact hco 0
    refine (E.ox_oldOptimal_iff _ hpos _).2 ?_
    rw [E.ox_oldBudget_eq, E.ox_mhat_qOf]
  · field_simp [(E.ox_N_pos t).ne']
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [E.ox_N_succ]
    ring

/-- Conversely, every monetary equilibrium satisfies the saving difference equation:
`ox_EulerRel (m̂_t) (m̂_{t+1})` for all `t ≥ 1`. -/
theorem ox_monetary_eulerRel {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {t : ℕ}
    (ht : 1 ≤ t) : E.ox_EulerRel (E.ox_mhat q t) (E.ox_mhat q (t + 1)) := by
  obtain ⟨-, hpos, hlt, -, -⟩ := (E.ox_monetary_alloc h).1 t ht
  obtain ⟨-, hpos1, hlt1, -, -⟩ := (E.ox_monetary_alloc h).1 (t + 1) (by omega)
  refine ⟨hpos, hlt, hpos1, hlt1, ?_⟩
  have he := (E.eq_16_6 h ht).1
  rw [E.eq_16_7 q (h.2 t ht)] at he
  have hd := E.ox_P.ox_du_pos _ (show 0 < E.ox_e2 + E.ox_gn * E.ox_mhat q (t + 1) by
    nlinarith [E.ox_e2_pos, E.ox_gn_pos])
  have hβ := E.ox_P.ox_β_pos
  rw [div_eq_iff (by positivity)] at he
  rw [he]; ring

end OXEconomy

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMMoney.OLGEquilibrium

/-!
# Two fiat currencies: Kareken–Wallace exchange-rate indeterminacy

AKMM, §17.4.1, pp. 524–526. In the endowment OLG economy of §17.2 the young can save in two
currencies `a, b` with prices `p_{a,t}, p_{b,t}` (no short sales), stocks `M_a, M_b > 0`.

* `kwOptimal`, `kwIsEquilibrium`: the young's problem and equilibrium.
* `kw_dominated`: a currency with a strictly lower return is not held.
* `kw_equal_returns_util`, `kw_optimal_iff`: with equal returns only total real saving matters
  and the problem is the one-currency problem (17.3).
* `kw_structure`: in every equilibrium each currency is valued at all dates or at none, and if
  both are valued their returns are equal at all dates; `kw_e_constant`: then the exchange rate
  `e_t = p_{a,t}/p_{b,t}` is constant.
* `kw_indeterminate`: every `e > 0` (and every one-currency equilibrium path for total real
  balances) gives an equilibrium: the exchange rate is not determined; `kw_unvalued`: so is the
  equilibrium in which one currency is never valued.
* Growing stocks: `kw_gresham` (`eM_{a,t}/M_t → 1` and `γ_t → γ_a` for `γ_a > γ_b`, Gresham's
  law), `kw_limit_formula` (the steady state of the modified demand is
  `p_bM = (ω_y − γω_o)/(1 + γ)`), `kw_limit_lower` (it is lower for faster money growth, so the
  `e = 0` equilibrium has the higher limit), `kw_limit_eq_mg` (it is the money-growth stationary
  value of §17.2.3).

**Not formalised.** That an equilibrium path with growing stocks exists and converges to the
limit; the book defers the proof to the appendix of Kareken and Wallace (1981).
-/

open Filter Topology

namespace AKMM.Money

/-- AKMM, p. 524: utility of a young agent holding `(M_a′, M_b′)`. -/
noncomputable def kwUtil (ωy ωo pa pb pa1 pb1 Ma Mb : ℝ) : ℝ :=
  Real.log (ωy - pa * Ma - pb * Mb) + Real.log (ωo + pa1 * Ma + pb1 * Mb)

/-- AKMM, p. 524: feasible holdings, `M_a′, M_b′ ≥ 0` and `c_y > 0`. -/
def kwFeasible (ωy pa pb Ma Mb : ℝ) : Prop := 0 ≤ Ma ∧ 0 ≤ Mb ∧ pa * Ma + pb * Mb < ωy

/-- AKMM, p. 524: optimal holdings. -/
def kwOptimal (ωy ωo pa pb pa1 pb1 Ma Mb : ℝ) : Prop :=
  kwFeasible ωy pa pb Ma Mb ∧ ∀ Ma' Mb', kwFeasible ωy pa pb Ma' Mb' →
    kwUtil ωy ωo pa pb pa1 pb1 Ma' Mb' ≤ kwUtil ωy ωo pa pb pa1 pb1 Ma Mb

/-- AKMM, p. 525: an equilibrium with constant stocks `M_a, M_b`: prices are nonnegative and the
young hold both stocks at every date. -/
def kwIsEquilibrium (ωy ωo Ma Mb : ℝ) (pa pb : ℕ → ℝ) : Prop :=
  (∀ t, 0 ≤ pa t ∧ 0 ≤ pb t) ∧ ∀ t, kwOptimal ωy ωo (pa t) (pb t) (pa (t + 1)) (pb (t + 1)) Ma Mb

/-- AKMM, p. 524: if currency `a` has a strictly lower return than `b`
(`p_{a,t+1}/p_{a,t} < p_{b,t+1}/p_{b,t}`), holding `M_a′ > 0` is not optimal. -/
theorem kw_dominated {ωy ωo pa pb pa1 pb1 Ma Mb : ℝ} (hωo : 0 < ωo) (hpa : 0 < pa) (hpb : 0 < pb)
    (hpa1 : 0 ≤ pa1) (hpb1 : 0 ≤ pb1) (hret : pa1 / pa < pb1 / pb) (hMa : 0 < Ma) :
    ¬ kwOptimal ωy ωo pa pb pa1 pb1 Ma Mb := by
  rintro ⟨⟨-, hMb, hc⟩, h⟩
  have hfeas : kwFeasible ωy pa pb 0 (Mb + pa * Ma / pb) := by
    refine ⟨le_rfl, by positivity, ?_⟩
    have : pa * 0 + pb * (Mb + pa * Ma / pb) = pa * Ma + pb * Mb := by field_simp; ring
    rw [this]; exact hc
  have := h _ _ hfeas
  unfold kwUtil at this
  have e1 : ωy - pa * 0 - pb * (Mb + pa * Ma / pb) = ωy - pa * Ma - pb * Mb := by
    field_simp; ring
  have hgain : pa1 * Ma < pb1 * (pa * Ma / pb) := by
    rw [div_lt_div_iff₀ hpa hpb] at hret
    rw [mul_div_assoc', lt_div_iff₀ hpb]
    nlinarith
  have hlt : Real.log (ωo + pa1 * Ma + pb1 * Mb) <
      Real.log (ωo + pa1 * 0 + pb1 * (Mb + pa * Ma / pb)) :=
    Real.log_lt_log (by positivity) (by nlinarith)
  rw [e1] at this
  linarith

/-- AKMM, p. 525: with equal returns `R` only total real saving `s = p_aM_a′ + p_bM_b′` matters:
the two-currency utility is the one-currency utility `log(ω_y − s) + log(ω_o + Rs)`. -/
theorem kw_equal_returns_util {ωy ωo pa pb pa1 pb1 R : ℝ} (hpa : pa ≠ 0) (hpb : pb ≠ 0)
    (ha : pa1 / pa = R) (hb : pb1 / pb = R) (Ma Mb : ℝ) :
    kwUtil ωy ωo pa pb pa1 pb1 Ma Mb = olgUtil ωy ωo R (pa * Ma + pb * Mb) := by
  unfold kwUtil olgUtil
  have h1 : pa1 = R * pa := by rw [← ha]; field_simp
  have h2 : pb1 = R * pb := by rw [← hb]; field_simp
  rw [h1, h2]
  ring_nf

/-- AKMM, p. 525: with equal returns `R` and positive prices, `(M_a′, M_b′) ≥ 0` is optimal iff
total real saving equals the one-currency demand (17.3); the split is indeterminate. -/
theorem kw_optimal_iff {ωy ωo pa pb pa1 pb1 R Ma Mb : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo)
    (hpa : 0 < pa) (hpb : 0 < pb) (hR : 0 ≤ R) (ha : pa1 / pa = R) (hb : pb1 / pb = R)
    (hMa : 0 ≤ Ma) (hMb : 0 ≤ Mb) :
    kwOptimal ωy ωo pa pb pa1 pb1 Ma Mb ↔ pa * Ma + pb * Mb = olgDemand ωy ωo R := by
  obtain ⟨hopt, huniq⟩ := eq_17_3 hωy hωo hR
  constructor
  · rintro ⟨⟨-, -, hc⟩, h⟩
    refine huniq _ ⟨⟨by positivity, hc⟩, fun s' hs' => ?_⟩
    have := h (s' / pa) 0 ⟨div_nonneg hs'.1 hpa.le, le_rfl, by
      rw [mul_div_cancel₀ _ hpa.ne', mul_zero, add_zero]; exact hs'.2⟩
    rwa [kw_equal_returns_util hpa.ne' hpb.ne' ha hb, kw_equal_returns_util hpa.ne' hpb.ne' ha hb,
      mul_div_cancel₀ _ hpa.ne', mul_zero, add_zero] at this
  · intro h
    refine ⟨⟨hMa, hMb, by rw [h]; exact hopt.1.2⟩, fun Ma' Mb' hf => ?_⟩
    rw [kw_equal_returns_util hpa.ne' hpb.ne' ha hb, kw_equal_returns_util hpa.ne' hpb.ne' ha hb, h]
    exact hopt.2 _ ⟨by have := hf.1; have := hf.2.1; positivity, hf.2.2⟩

/-- The problem is symmetric in the two currencies. -/
theorem kw_optimal_comm {ωy ωo pa pb pa1 pb1 Ma Mb : ℝ} :
    kwOptimal ωy ωo pa pb pa1 pb1 Ma Mb ↔ kwOptimal ωy ωo pb pa pb1 pa1 Mb Ma := by
  have hu : ∀ x y, kwUtil ωy ωo pa pb pa1 pb1 x y = kwUtil ωy ωo pb pa pb1 pa1 y x := fun x y => by
    unfold kwUtil; ring_nf
  have hf : ∀ x y, kwFeasible ωy pa pb x y ↔ kwFeasible ωy pb pa y x := fun x y => by
    unfold kwFeasible; constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2, h1, by linarith⟩
  unfold kwOptimal
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(hf _ _).1 h1, fun x y hxy => by rw [← hu, ← hu]; exact h2 y x ((hf _ _).2 hxy)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(hf _ _).2 h1, fun x y hxy => by rw [hu, hu]; exact h2 y x ((hf _ _).1 hxy)⟩

/-- AKMM, p. 524: if currency `a` is free today but valued tomorrow there is no optimum. -/
theorem kw_zero_pos {ωy ωo pb pa1 pb1 Ma Mb : ℝ} (hωo : 0 < ωo) (hpa1 : 0 < pa1)
    (hpb1 : 0 ≤ pb1) : ¬ kwOptimal ωy ωo 0 pb pa1 pb1 Ma Mb := by
  rintro ⟨⟨hMa, hMb, hc⟩, h⟩
  have := h (Ma + 1) Mb ⟨by linarith, hMb, by simpa using hc⟩
  unfold kwUtil at this
  have hlt : Real.log (ωo + pa1 * Ma + pb1 * Mb) < Real.log (ωo + pa1 * (Ma + 1) + pb1 * Mb) :=
    Real.log_lt_log (by positivity) (by nlinarith)
  simp only [zero_mul, sub_zero] at this
  linarith

/-- AKMM, p. 524: if currency `a` is valued today but worthless tomorrow, holding it is not
optimal. -/
theorem kw_pos_zero {ωy ωo pa pb pb1 Ma Mb : ℝ} (hpa : 0 < pa) (hMa : 0 < Ma) :
    ¬ kwOptimal ωy ωo pa pb 0 pb1 Ma Mb := by
  rintro ⟨⟨-, hMb, hc⟩, h⟩
  have := h 0 Mb ⟨le_rfl, hMb, by nlinarith⟩
  unfold kwUtil at this
  have hlt : Real.log (ωy - pa * Ma - pb * Mb) < Real.log (ωy - pa * 0 - pb * Mb) :=
    Real.log_lt_log (by nlinarith) (by nlinarith)
  simp only [zero_mul, add_zero, mul_zero, sub_zero] at this hlt
  linarith

/-- **AKMM, pp. 524–525: the structure of equilibria.** With `M_a, M_b > 0`, in every
equilibrium each currency is valued at all dates or at none, and if both are valued their
returns are equal at every date. -/
theorem kw_structure {ωy ωo Ma Mb : ℝ} (hωo : 0 < ωo) (hMa : 0 < Ma) (hMb : 0 < Mb)
    {pa pb : ℕ → ℝ} (h : kwIsEquilibrium ωy ωo Ma Mb pa pb) :
    ((∀ t, pa t = 0) ∨ ∀ t, 0 < pa t) ∧ ((∀ t, pb t = 0) ∨ ∀ t, 0 < pb t) ∧
      ((∀ t, 0 < pa t) → (∀ t, 0 < pb t) → ∀ t, pa (t + 1) / pa t = pb (t + 1) / pb t) := by
  obtain ⟨hnn, hopt⟩ := h
  have hopt' : ∀ t, kwOptimal ωy ωo (pb t) (pa t) (pb (t + 1)) (pa (t + 1)) Mb Ma :=
    fun t => kw_optimal_comm.1 (hopt t)
  have dich : ∀ (p q : ℕ → ℝ) (M M' : ℝ), 0 < M → (∀ t, 0 ≤ p t) → (∀ t, 0 ≤ q t) →
      (∀ t, kwOptimal ωy ωo (p t) (q t) (p (t + 1)) (q (t + 1)) M M') →
      (∀ t, p t = 0) ∨ ∀ t, 0 < p t := by
    intro p q M M' hM hp hq ho
    have up : ∀ t, p t = 0 → p (t + 1) = 0 := fun t ht => by
      by_contra hn
      have := ho t
      rw [ht] at this
      exact kw_zero_pos hωo (lt_of_le_of_ne (hp _) (Ne.symm hn)) (hq _) this
    have up' : ∀ t, 0 < p t → 0 < p (t + 1) := fun t ht => by
      by_contra hn
      have h0 : p (t + 1) = 0 := le_antisymm (not_lt.1 hn) (hp _)
      have := ho t
      rw [h0] at this
      exact kw_pos_zero ht hM this
    rcases (hp 0).lt_or_eq with h0 | h0
    · right; intro t; induction t with
        | zero => exact h0
        | succ n ih => exact up' n ih
    · left; intro t; induction t with
        | zero => exact h0.symm
        | succ n ih => exact up n ih
  refine ⟨dich pa pb Ma Mb hMa (fun t => (hnn t).1) (fun t => (hnn t).2) hopt,
    dich pb pa Mb Ma hMb (fun t => (hnn t).2) (fun t => (hnn t).1) hopt', fun ha hb t => ?_⟩
  rcases lt_trichotomy (pa (t + 1) / pa t) (pb (t + 1) / pb t) with hlt | heq | hgt
  · exact absurd (hopt t) (kw_dominated hωo (ha t) (hb t) (hnn _).1 (hnn _).2 hlt hMa)
  · exact heq
  · exact absurd (hopt' t) (kw_dominated hωo (hb t) (ha t) (hnn _).2 (hnn _).1 hgt hMb)

/-- AKMM, p. 525: with equal returns at all dates the exchange rate `e_t = p_{a,t}/p_{b,t}` is
constant. -/
theorem kw_e_constant {pa pb : ℕ → ℝ} (ha : ∀ t, 0 < pa t) (hb : ∀ t, 0 < pb t)
    (h : ∀ t, pa (t + 1) / pa t = pb (t + 1) / pb t) (t : ℕ) : pa t / pb t = pa 0 / pb 0 := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    have h' := h n
    rw [div_eq_div_iff (ha n).ne' (hb n).ne'] at h'
    rw [div_eq_div_iff (hb (n + 1)).ne' (hb n).ne']
    linear_combination h'

/-- **AKMM, p. 525: the exchange rate is indeterminate.** Let `x` be a positive equilibrium path
of total real balances in the one-currency economy ((17.5) with stock `1`). For every `e > 0`
the prices `p_{b,t} = x_t/(eM_a + M_b)`, `p_{a,t} = ep_{b,t}` form an equilibrium with both
stocks held. -/
theorem kw_indeterminate {ωy ωo Ma Mb e : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hMa : 0 < Ma)
    (hMb : 0 < Mb) (he : 0 < e) {x : ℕ → ℝ} (hx : olgIsEquilibrium ωy ωo 1 x) (hx0 : 0 < x 0) :
    kwIsEquilibrium ωy ωo Ma Mb (fun t => e * (x t / (e * Ma + Mb)))
      (fun t => x t / (e * Ma + Mb)) := by
  have hK : 0 < e * Ma + Mb := by positivity
  have hpos : ∀ t, 0 < x t := by
    rcases (eq_17_5 hωy hωo one_pos x).1 hx with h | h
    · exact absurd (h 0) hx0.ne'
    · exact fun t => (h t).1
  refine ⟨fun t => ⟨by have := hpos t; positivity, by have := hpos t; positivity⟩, fun t => ?_⟩
  have hR : 0 ≤ x (t + 1) / x t := div_nonneg (hpos _).le (hpos t).le
  have hd := ((olg_moneyOptimal_iff_pos hωy hωo (hpos t) (hpos (t + 1)).le).1 (hx.2 t)).2
  rw [mul_one] at hd
  have hxt := (hpos t).ne'
  rw [kw_optimal_iff hωy hωo (by have := hpos t; positivity) (by have := hpos t; positivity) hR
    (by field_simp) (by field_simp) hMa.le hMb.le]
  rw [← hd]
  field_simp

/-- AKMM, p. 525: the equilibria in which currency `a` is never valued are the one-currency
equilibria for `b` (for instance `e = 0`). -/
theorem kw_unvalued {ωy ωo Ma Mb : ℝ} (hMa : 0 ≤ Ma) {pb : ℕ → ℝ}
    (h : olgIsEquilibrium ωy ωo Mb pb) : kwIsEquilibrium ωy ωo Ma Mb (fun _ => 0) pb := by
  have hu : ∀ t x y, kwUtil ωy ωo 0 (pb t) 0 (pb (t + 1)) x y =
      olgMoneyUtil ωy ωo (pb t) (pb (t + 1)) y := fun t x y => by
    unfold kwUtil olgMoneyUtil; ring_nf
  refine ⟨fun t => ⟨le_rfl, h.1 t⟩, fun t => ⟨⟨hMa, (h.2 t).1.1, by simpa using (h.2 t).1.2⟩,
    fun x y hxy => ?_⟩⟩
  rw [hu, hu]
  exact (h.2 t).2 y ⟨hxy.2.1, by simpa using hxy.2.2⟩

/-- AKMM, p. 525: the modified demand with transfers `p_{b,t+1}(γ_t − 1)M_t` to the old is the
one-currency demand with old-age income `ω_o + p_{b,t+1}(γ_t − 1)M_t`; at an interior solution
`p_{b,t}M_t = (ω_y − (ω_o + p_{b,t+1}(γ_t − 1)M_t)/(p_{b,t+1}/p_{b,t}))/2`. -/
theorem kw_modified_demand {ωy W R : ℝ} (hint : W < R * ωy) :
    olgDemand ωy W R = (ωy - W / R) / 2 := by
  unfold olgDemand
  simp only [not_le.2 hint, ↓reduceIte]

/-- **AKMM, p. 526: the long-run real value of total money.** With constant growth `γ > 0`, a
stationary solution of the modified demand (`p_{b,t+1}/p_{b,t} = 1/γ`, transfer value
`(γ − 1)x/γ`) is `x = (ω_y − γω_o)/(1 + γ)`. -/
theorem kw_limit_formula {ωy ωo γ x : ℝ} (hγ : 0 < γ) :
    x = (ωy - (ωo + (γ - 1) * x / γ) / (1 / γ)) / 2 ↔ x = (ωy - γ * ωo) / (1 + γ) := by
  have e : (ωo + (γ - 1) * x / γ) / (1 / γ) = γ * ωo + (γ - 1) * x := by field_simp
  rw [e, eq_div_iff (two_ne_zero), eq_div_iff (by linarith : (1 : ℝ) + γ ≠ 0)]
  constructor <;> intro h <;> linear_combination h

/-- AKMM, p. 526: the limit `(ω_y − γω_o)/(1 + γ)` is strictly decreasing in `γ`: the value of
the money stock when only the slower-growing currency is valued (`e = 0`) is higher. -/
theorem kw_limit_lower {ωy ωo γa γb : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hγb : 0 < γb)
    (hγ : γb < γa) : (ωy - γa * ωo) / (1 + γa) < (ωy - γb * ωo) / (1 + γb) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The Kareken–Wallace limit is the stationary value of §17.2.3 with `γ = 1 + μ`
(`mg_stationary_iff`). -/
theorem kw_limit_eq_mg (ωy ωo μ : ℝ) :
    (ωy - (1 + μ) * ωo) / (1 + (1 + μ)) = (ωy - (1 + μ) * ωo) / (2 + μ) := by ring_nf

/-- **AKMM, p. 526: Gresham's law.** With `M_{a,t} = M_{a,0}γ_aᵗ`, `M_{b,t} = M_{b,0}γ_bᵗ`,
`γ_a > γ_b > 0` and `e > 0`, the share of currency `a` in the total stock
`M_t = eM_{a,t} + M_{b,t}` tends to one and the growth factor `γ_t = M_{t+1}/M_t` tends to
`γ_a`. -/
theorem kw_gresham {e Ma0 Mb0 γa γb : ℝ} (he : 0 < e) (hMa : 0 < Ma0) (hMb : 0 < Mb0)
    (hγb : 0 < γb) (hγ : γb < γa) :
    Tendsto (fun t : ℕ => e * Ma0 * γa ^ t / (e * Ma0 * γa ^ t + Mb0 * γb ^ t)) atTop (𝓝 1) ∧
      Tendsto (fun t : ℕ => (e * Ma0 * γa ^ (t + 1) + Mb0 * γb ^ (t + 1)) /
        (e * Ma0 * γa ^ t + Mb0 * γb ^ t)) atTop (𝓝 γa) := by
  have hγa : 0 < γa := hγb.trans hγ
  set k := Mb0 / (e * Ma0) with hk
  have hk0 : 0 < k := by positivity
  have hr : Tendsto (fun t : ℕ => (γb / γa) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hγa).2 hγ)
  have hden : Tendsto (fun t : ℕ => 1 + k * (γb / γa) ^ t) atTop (𝓝 1) := by
    simpa using (hr.const_mul k).const_add 1
  have e1 : ∀ t : ℕ, e * Ma0 * γa ^ t / (e * Ma0 * γa ^ t + Mb0 * γb ^ t) =
      1 / (1 + k * (γb / γa) ^ t) := fun t => by
    have := pow_pos hγa t
    rw [hk, div_pow]
    field_simp
  have e2 : ∀ t : ℕ, (e * Ma0 * γa ^ (t + 1) + Mb0 * γb ^ (t + 1)) /
      (e * Ma0 * γa ^ t + Mb0 * γb ^ t) =
        (γa + k * γb * (γb / γa) ^ t) / (1 + k * (γb / γa) ^ t) := fun t => by
    have := pow_pos hγa t
    have := pow_pos hγb t
    rw [hk, div_pow, pow_succ, pow_succ]
    field_simp
  constructor
  · simp only [e1]
    simpa using hden.inv₀ one_ne_zero
  · simp only [e2]
    have hnum : Tendsto (fun t : ℕ => γa + k * γb * (γb / γa) ^ t) atTop (𝓝 γa) := by
      simpa using (hr.const_mul (k * γb)).const_add γa
    have := hnum.div hden one_ne_zero
    rw [div_one] at this
    exact this

end AKMM.Money

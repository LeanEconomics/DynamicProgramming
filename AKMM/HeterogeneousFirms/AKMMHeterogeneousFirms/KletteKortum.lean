/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.QualityLadders
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Klette–Kortum in discrete time (AKMM §22.8)

AKMM, §22.8, pp. 686–692. A unit mass of products `j` is a probability space `(Ω, P)`; the book's
law of large numbers is the identification of cross-section averages with `∫ · ∂P`.

* **The intratemporal problem (22.35)–(22.36)**: equal expenditure shares `c = E/p` maximise
  `∫ log(qc)` subject to `∫ pc ≤ E` (`eq_22_36`); `PC = E` and the normalisation (22.37)
  (`kk_price_index`, `eq_22_37`).
* **(22.38)**: the balanced-growth Euler equation `1/(1+r) = β/(1+γ)` (`eq_22_38`).
* **Limit pricing (22.39)–(22.40)**: consumers buy the leader iff `p ≤ λw` (from the
  quality-ladder condition (13.A.26) of AKMM Chapter 13, `AKMM.Growth.eq_13_A_26`, at `φ = 0`)
  (`kk_limit_price_iff`); with unit-elastic demand profit rises with the price, so `p = λw` is
  optimal (`eq_22_39`); profit `(1 − 1/λ)C` (`eq_22_40`); `w₀ = 1` (`kk_wage_normalisation`).
* **The Bellman equation (22.41)–(22.43)**: the four scenarios have probabilities summing to one
  and expected future lines `1 + η − μ` (`eq_22_41`); detrending gives (22.42) (`eq_22_42`); for
  convex `R` the first-order condition `R'(η) = βv` gives the optimum (`eq_22_43`).
* **Equilibrium (22.44)–(22.46)**: with entry using `c_e` units of labour per entrant (corrected
  from the printed `ν`), the equilibrium `(C₀, μ)` given `η` is unique, in closed form
  (`kk_equilibrium`).
* **Growth**: with `J_t = J₀ + Σ_{s<t} Bernoulli(μ)`, the wage grows by `λ^μ`:
  `log w_{t+1} − log w_t = μ log λ` exactly (`kk_growth`).
* **Gibrat's law**: a firm with `n` lines expects `n(1 + η − μ)` lines next period, so all firms
  grow at `η − μ = −ν` (`kk_gibrat`); with new-product creation `ξ`, `ξ − ν` (`kk_gibrat_xi`).
-/

open MeasureTheory

namespace AKMM.HeterogeneousFirms

variable {Ω : Type*} [MeasurableSpace Ω]

/-- AKMM, (22.35)–(22.36), p. 687: **equal expenditure shares**. With log preferences over a unit
mass of goods, prices `p > 0`, qualities `q > 0` and spending `E > 0`, any positive consumption
plan `c` with `∫ pc ≤ E` gives `∫ log(qc) ≤ ∫ log(qE/p)`: the plan `c = E/p` is optimal. -/
theorem eq_22_36 {P : Measure Ω} [IsProbabilityMeasure P] {p q c : Ω → ℝ} {E : ℝ} (hE : 0 < E)
    (hp : ∀ j, 0 < p j) (hq : ∀ j, 0 < q j) (hc : ∀ j, 0 < c j)
    (hpc : Integrable (fun j => p j * c j) P)
    (hlc : Integrable (fun j => Real.log (q j * c j)) P)
    (hlo : Integrable (fun j => Real.log (q j * (E / p j))) P)
    (hbud : ∫ j, p j * c j ∂P ≤ E) :
    ∫ j, Real.log (q j * c j) ∂P ≤ ∫ j, Real.log (q j * (E / p j)) ∂P := by
  have hpt : ∀ j, Real.log (q j * c j) ≤ Real.log (q j * (E / p j)) + (p j * c j / E - 1) :=
    fun j => by
      have hpj := hp j; have hqj := hq j; have hcj := hc j
      have h := Real.log_le_sub_one_of_pos (show 0 < p j * c j / E by positivity)
      have e : Real.log (q j * c j) = Real.log (q j * (E / p j)) + Real.log (p j * c j / E) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1; field_simp
      linarith
  have h2 : Integrable (fun j => p j * c j / E - 1) P :=
    (hpc.div_const E).sub (integrable_const 1)
  have h : ∫ j, Real.log (q j * c j) ∂P ≤
      ∫ j, (Real.log (q j * (E / p j)) + (p j * c j / E - 1)) ∂P :=
    integral_mono hlc (hlo.add h2) hpt
  rw [integral_add hlo h2,
    integral_sub (hpc.div_const E) (integrable_const 1), integral_div] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  have : (∫ j, p j * c j ∂P) / E - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hE]; exact hbud
  linarith

/-- AKMM, p. 687: at `c = E/p`, consumption is `C = E·exp(∫(log q − log p))`, so with the price
index `P = exp(∫(log p − log q))`, `PC = E`. -/
theorem kk_price_index {P : Measure Ω} {p q : Ω → ℝ} {E : ℝ} (hE : 0 < E) (hp : ∀ j, 0 < p j)
    (hq : ∀ j, 0 < q j) (hlq : Integrable (fun j => Real.log (q j)) P)
    (hlp : Integrable (fun j => Real.log (p j)) P) [IsProbabilityMeasure P] :
    Real.exp (∫ j, Real.log (q j * (E / p j)) ∂P) =
        E * Real.exp (∫ j, (Real.log (q j) - Real.log (p j)) ∂P) ∧
      Real.exp (∫ j, (Real.log (p j) - Real.log (q j)) ∂P) *
        (E * Real.exp (∫ j, (Real.log (q j) - Real.log (p j)) ∂P)) = E := by
  have e : ∀ j, Real.log (q j * (E / p j)) = Real.log E + (Real.log (q j) - Real.log (p j)) :=
    fun j => by
      rw [Real.log_mul (hq j).ne' (div_pos hE (hp j)).ne', Real.log_div hE.ne' (hp j).ne']; ring
  have hqp : Integrable (fun j => Real.log (q j) - Real.log (p j)) P := hlq.sub hlp
  have hpq : Integrable (fun j => Real.log (p j) - Real.log (q j)) P := hlp.sub hlq
  constructor
  · rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_add (integrable_const _)
      hqp]
    simp only [integral_const, probReal_univ, one_smul]
    rw [Real.exp_add, Real.exp_log hE]
  · rw [mul_left_comm, ← Real.exp_add, ← integral_add hpq hqp]
    simp

/-- AKMM, (22.37), p. 687: the normalisation `P = 1` holds iff `∫ log p = ∫ log q`. -/
theorem eq_22_37 {P : Measure Ω} {p q : Ω → ℝ} (hlq : Integrable (fun j => Real.log (q j)) P)
    (hlp : Integrable (fun j => Real.log (p j)) P) :
    Real.exp (∫ j, (Real.log (p j) - Real.log (q j)) ∂P) = 1 ↔
      ∫ j, Real.log (p j) ∂P = ∫ j, Real.log (q j) ∂P := by
  rw [Real.exp_eq_one_iff, integral_sub hlp hlq, sub_eq_zero]

/-- AKMM, (22.38), p. 688: **the balanced-growth Euler equation**. If `1/C_t = β(1+r)/C_{t+1}`
and `C_{t+1} = (1+γ)C_t` with `C_t > 0`, then `1/(1+r) = β/(1+γ)`. -/
theorem eq_22_38 {β r γ Ct : ℝ} (hC : 0 < Ct) (hγ : 0 < 1 + γ) (hr : 0 < 1 + r)
    (h : 1 / Ct = β * (1 + r) * (1 / ((1 + γ) * Ct))) : 1 / (1 + r) = β / (1 + γ) := by
  field_simp at h ⊢
  linarith

/-- AKMM, (22.39), p. 688: **limit pricing**. A leader of quality `λq'` priced at `p` beats the
follower of quality `q'` priced at marginal cost `w` (quality-adjusted prices
`p/(λq') ≤ w/q'`) iff `p ≤ λw`. This is the quality-ladder condition (13.A.26) of Chapter 13 at
`φ = 0` (marginal cost `ψq' = w`). -/
theorem kk_limit_price_iff {lam w q' p : ℝ} (hlam : 0 < lam) (hw : 0 < w) (hq' : 0 < q') :
    p / (lam * q') ≤ w / q' ↔ p ≤ lam * w := by
  have h := AKMM.Growth.eq_13_A_26 (φ := 0) (ψ := w / q') (by norm_num) (div_pos hw hq')
    hlam hq' (p := p)
  simp only [sub_zero, div_one, Real.rpow_one, Real.rpow_zero] at h
  rw [show w / q' * q' / q' = w / q' by field_simp] at h
  rw [h, show w / q' * (lam * q') = lam * w by field_simp, div_le_one (by positivity)]

/-- AKMM, (22.39)–(22.40), p. 688: **the optimal price is the limit price**. With unit-elastic
demand `c = C/p`, the leader's profit `(p − w)C/p` is increasing in `p`, so among the prices that
keep the follower out (`p ≤ λw`) it is maximised at `p = λw`, where it equals `(1 − 1/λ)C`. -/
theorem eq_22_39 {lam w C p : ℝ} (hlam : 1 < lam) (hw : 0 < w) (hC : 0 < C) (hp : 0 < p)
    (hpl : p ≤ lam * w) :
    (p - w) * (C / p) ≤ (lam * w - w) * (C / (lam * w)) := by
  have hlw : 0 < lam * w := by nlinarith
  have e1 : (p - w) * (C / p) = C - w * C / p := by field_simp
  have e2 : (lam * w - w) * (C / (lam * w)) = C - w * C / (lam * w) := by field_simp
  rw [e1, e2]
  have : w * C / (lam * w) ≤ w * C / p := div_le_div_of_nonneg_left (by positivity) hp hpl
  linarith

/-- AKMM, (22.40), p. 688: the profit at the limit price is `π = (1 − 1/λ)C`. -/
theorem eq_22_40 {lam w C : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    (lam * w - w) * (C / (lam * w)) = (1 - 1 / lam) * C := by
  field_simp

/-- AKMM, p. 689: from (22.37) and (22.39), `log(λw₀) = ∫ log q₀`; with `q₀ = λ`, `w₀ = 1`. -/
theorem kk_wage_normalisation {lam w0 : ℝ} (hlam : 0 < lam) (hw : 0 < w0)
    (h : Real.log (lam * w0) = Real.log lam) : w0 = 1 := by
  rw [Real.log_mul hlam.ne' hw.ne'] at h
  have : Real.log w0 = 0 := by linarith
  rcases Real.log_eq_zero.mp this with h0 | h1 | hm
  · linarith
  · exact h1
  · linarith

/-- AKMM, (22.41), p. 689: **the four scenarios**. Innovating with probability `η` and losing the
line with probability `μ`, independently: the probabilities sum to one and the expected number
of lines next period is `2η(1−μ) + 0·μ(1−η) + 1·μη + 1·(1−μ)(1−η) = 1 + η − μ`. -/
theorem eq_22_41 (η μ : ℝ) :
    η * (1 - μ) + μ * (1 - η) + μ * η + (1 - μ) * (1 - η) = 1 ∧
      2 * (η * (1 - μ)) + 0 * (μ * (1 - η)) + 1 * (μ * η) + 1 * ((1 - μ) * (1 - η)) =
        1 + η - μ := by
  constructor <;> ring

/-- AKMM, (22.42), p. 689: **detrending**. If `V_t = (1+γ)^t v`, `π_t = (1 − 1/λ)C₀(1+γ)^t`,
`w_t = (1+γ)^t` and `1/(1+r) = β/(1+γ)`, then the Bellman equation (22.41) at a given `η`,
`V_t = π_t − w_tR(η) + (1+η−μ)V_{t+1}/(1+r)`, holds iff
`v = (1 − 1/λ)C₀ − R(η) + β(1+η−μ)v`. -/
theorem eq_22_42 {γ r β lam C0 R η μ v : ℝ} (hγ : 0 < 1 + γ) (hr : 1 / (1 + r) = β / (1 + γ))
    (t : ℕ) :
    (1 + γ) ^ t * v = (1 - 1 / lam) * C0 * (1 + γ) ^ t - (1 + γ) ^ t * R +
        1 / (1 + r) * (1 + η - μ) * ((1 + γ) ^ (t + 1) * v) ↔
      v = (1 - 1 / lam) * C0 - R + β * (1 + η - μ) * v := by
  rw [hr]
  have hg : 0 < (1 + γ) ^ t := pow_pos hγ t
  constructor
  · intro h
    have : (1 + γ) ^ t * v = (1 + γ) ^ t * ((1 - 1 / lam) * C0 - R + β * (1 + η - μ) * v) := by
      rw [h, pow_succ]; field_simp
    exact mul_left_cancel₀ hg.ne' this
  · intro h
    conv_lhs => rw [h]
    rw [pow_succ]; field_simp

/-- AKMM, (22.43), p. 689: **the innovation first-order condition**. If `R` is convex and
`R'(η*) = βv`, then `η*` maximises `−R(η) + βηv`, the part of (22.42) that depends on `η`. -/
theorem eq_22_43 {R : ℝ → ℝ} (hR : ConvexOn ℝ Set.univ R) {β v ηs : ℝ}
    (hd : HasDerivAt R (β * v) ηs) (η : ℝ) : -R η + β * η * v ≤ -R ηs + β * ηs * v := by
  rcases lt_trichotomy η ηs with h | h | h
  · have := hR.slope_le_of_hasDerivAt (Set.mem_univ η) (Set.mem_univ ηs) h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    nlinarith
  · rw [h]
  · have := hR.le_slope_of_hasDerivAt (Set.mem_univ ηs) (Set.mem_univ η) h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith

/-- AKMM, (22.42)–(22.46), pp. 689–690, with the entry labour corrected to `c_eν`: **the
equilibrium given `η`**. With free entry `v = c_e` (22.44), `μ = η + ν` (22.45), the Bellman
equation (22.42) and the labour market `C₀/λ + R(η) + c_e(μ − η) = L`, the pair `(C₀, μ)` is
unique: `μ = ((λ−1)(L − R + c_eη) − R − c_e(1 − β(1+η)))/(c_e(β + λ − 1))` and
`C₀ = λ(L − R − c_e(μ − η))`. -/
theorem kk_equilibrium {lam β ce L R η C0 μ : ℝ} (hlam : 1 < lam) (hβ : 0 < β) (hce : 0 < ce) :
    (ce = (1 - 1 / lam) * C0 - R + β * (1 + η - μ) * ce ∧ C0 / lam + R + ce * (μ - η) = L) ↔
      (μ = ((lam - 1) * (L - R + ce * η) - R - ce * (1 - β * (1 + η))) /
          (ce * (β + lam - 1)) ∧
        C0 = lam * (L - R - ce * (μ - η))) := by
  have hl0 : lam ≠ 0 := by linarith
  have hd : ce * (β + lam - 1) ≠ 0 := by
    have : 0 < β + lam - 1 := by linarith
    positivity
  have key : ∀ X : ℝ, (1 - 1 / lam) * (lam * X) = (lam - 1) * X := fun X => by field_simp
  constructor
  · rintro ⟨h1, h2⟩
    have hC : C0 = lam * (L - R - ce * (μ - η)) := by
      rw [← h2]; field_simp; ring
    refine ⟨?_, hC⟩
    rw [eq_div_iff hd]
    rw [hC, key] at h1
    linear_combination h1
  · rintro ⟨h1, h2⟩
    rw [eq_div_iff hd] at h1
    refine ⟨?_, by rw [h2, mul_div_cancel_left₀ _ hl0]; ring⟩
    rw [h2, key]
    linear_combination h1

/-- AKMM, (22.46), p. 690: the printed entry labour `ν` differs from the `c_eν` units entrants
hire (p. 689) whenever `c_e ≠ 1` and `ν ≠ 0`. -/
theorem kk_labour_printed_false {C0 lam R ν ce : ℝ} (hce : ce ≠ 1) (hν : ν ≠ 0) :
    C0 / lam + R + ν ≠ C0 / lam + R + ce * ν := by
  intro h
  have : (ce - 1) * ν = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hce (by linarith)
  · exact hν h1

/-- AKMM, p. 690: **the growth rate**. Let `log q_t(j) = J_t(j) log λ` with `J_t = J₀ + Σ_{s<t}Xₛ`,
each `Xₛ` a Bernoulli trial with mean `μ` (`∫Xₛ = μ`), and `log w_t = ∫ log q_t − log λ`
(from (22.37) and (22.39)). Then `log w_{t+1} − log w_t = μ log λ`: the gross growth rate is
exactly `λ^μ` (the book's `γ ≈ μ log λ`). -/
theorem kk_growth {P : Measure Ω} [IsProbabilityMeasure P] {lam μ : ℝ} {J0 : Ω → ℝ}
    {X : ℕ → Ω → ℝ} (hJ0 : Integrable J0 P) (hX : ∀ s, Integrable (X s) P)
    (hμ : ∀ s, ∫ j, X s j ∂P = μ) {w : ℕ → ℝ}
    (hw : ∀ t, Real.log (w t) =
      ∫ j, (J0 j + ∑ s ∈ Finset.range t, X s j) * Real.log lam ∂P - Real.log lam) (t : ℕ) :
    Real.log (w (t + 1)) - Real.log (w t) = μ * Real.log lam := by
  have hI : ∀ t, Integrable (fun j => J0 j + ∑ s ∈ Finset.range t, X s j) P := fun t =>
    hJ0.add (integrable_finsetSum _ fun s _ => hX s)
  have hE : ∀ t, ∫ j, (J0 j + ∑ s ∈ Finset.range t, X s j) * Real.log lam ∂P =
      (∫ j, J0 j ∂P + t * μ) * Real.log lam := fun t => by
    rw [integral_mul_const, integral_add hJ0 (integrable_finsetSum _ fun s _ => hX s),
      integral_finsetSum _ fun s _ => hX s]
    simp [hμ]
  rw [hw, hw, hE, hE]
  push_cast
  ring

/-- AKMM, p. 691: **Gibrat's law**. A firm with `n` lines; each line `l` is lost with
probability `μ` (`∫Lₗ = μ`) and generates a new line with probability `η` (`∫Gₗ = η`). The
expected number of lines next period is `n(1 + η − μ)`, and with `μ = η + ν` the expected growth
rate `η − μ = −ν` is the same for all sizes. -/
theorem kk_gibrat {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {η μ ν : ℝ}
    {Lo Ga : ℕ → Ω → ℝ} (hL : ∀ l, Integrable (Lo l) P) (hG : ∀ l, Integrable (Ga l) P)
    (hLμ : ∀ l, ∫ j, Lo l j ∂P = μ) (hGη : ∀ l, ∫ j, Ga l j ∂P = η) (hμ : μ = η + ν) :
    ∫ j, ((n : ℝ) - ∑ l ∈ Finset.range n, Lo l j + ∑ l ∈ Finset.range n, Ga l j) ∂P =
        n * (1 + η - μ) ∧ η - μ = -ν := by
  refine ⟨?_, by rw [hμ]; ring⟩
  have hLs : Integrable (fun j => ∑ l ∈ Finset.range n, Lo l j) P :=
    integrable_finsetSum _ fun l _ => hL l
  have hGs : Integrable (fun j => ∑ l ∈ Finset.range n, Ga l j) P :=
    integrable_finsetSum _ fun l _ => hG l
  have h1 : Integrable (fun j => (n : ℝ) - ∑ l ∈ Finset.range n, Lo l j) P :=
    (integrable_const _).sub hLs
  rw [integral_add h1 hGs, integral_sub (integrable_const _) hLs,
    integral_finsetSum _ fun l _ => hL l, integral_finsetSum _ fun l _ => hG l]
  simp [hLμ, hGη]
  ring

/-- AKMM, p. 692: with new-product creation `ξ` (`μ = η + ν − ξ`), the expected growth rate
`η − μ` is `ξ − ν`, positive when `ξ > ν`. -/
theorem kk_gibrat_xi {η μ ν ξ : ℝ} (hμ : μ = η + ν - ξ) : η - μ = ξ - ν := by
  rw [hμ]; ring

end AKMM.HeterogeneousFirms

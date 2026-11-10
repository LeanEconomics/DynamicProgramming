/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RMDecentral

/-!
# Incorporating fiscal policy

Miao, §14.1.2, pp. 467–471. No long-run growth; firms own capital; consumption, distribution,
labour income and corporate income taxes `τˢ, τᵈ, τⁿ, τᶜ`, lump-sum taxes `T`, one-period
government bonds `B` with gross return `R`.

* The household's first-order conditions (p. 468) give the consumption Euler equation
  `u_C(t)/(1 + τˢ_t) = βR_tu_C(t + 1)/(1 + τˢ_{t+1})` and the labour condition
  `−u_N/u_C = (1 − τⁿ)w/(1 + τˢ)` (`rm_fiscal_euler`, `rm_fiscal_labour`); the share condition is
  the firm's value recursion `V_t = (1 − τᵈ_t)D_t + βΛ_{t+1}/Λ_t V_{t+1}`
  (`rm_fiscal_value_recursion`).
* The firm's first-order condition for capital (14.20), with `Q = 1 − τᵈ` (14.19), from the
  variation of `K_{t+1}` (`eq_14_20`).
* **Proposition 14.1.1**: the one-step identity
  `Q_tK_{t+1} = βΛ_{t+1}/Λ_t[(1 − τᵈ_{t+1})D_{t+1} + Q_{t+1}K_{t+2}]` (`rm_prop_14_1_1_step`),
  the forward solution `Q_tK_{t+1} = ∑_{j≥1} βʲΛ_{t+j}/Λ_t (1 − τᵈ_{t+j})D_{t+j}` under the
  transversality condition (`rm_prop_14_1_1_sum`), the equality of the ex-dividend value with
  `Q_tK_{t+1}` (`rm_prop_14_1_1_exdiv`), and the proposition
  `V_t − (1 − τᵈ_t)D_t = (1 − τᵈ_t)K_{t+1}` (`proposition_14_1_1`).
* **(14.21)**: with constant `τᵈ ≠ 1` and `τᶜ`, (14.19)–(14.20) are equivalent to
  `1 = βΛ_{t+1}/Λ_t[(1 − δ) + τᶜδ + (1 − τᶜ)F_K]` (`eq_14_21`).
* **Permanent changes in `τᵈ`** (p. 470) with lump-sum taxes balancing the budget do not affect
  the allocation: any equilibrium for `τᵈ` gives an equilibrium for any other constant `τᵈ' ≠ 1`
  with the same allocation, the same `Λ, w, R, D, B`, price of capital `Q' = 1 − τᵈ'`, equity
  value `V' = (1 − τᵈ')(D + K_{+1})` and lump-sum taxes `T' = T + (τᵈ − τᵈ')D`
  (`rm_distribution_tax_neutral`).
* **Temporary changes in `τᵈ`**: with a time-varying distribution tax, (14.19)–(14.20) become
  `(1 − τᵈ_t)/(1 − τᵈ_{t+1}) = βΛ_{t+1}/Λ_t[(1 − δ) + τᶜδ + (1 − τᶜ)F_K]`
  (`rm_temporary_distribution_tax`), which agrees with (14.21) only when `τᵈ_t = τᵈ_{t+1}`
  (`rm_temporary_distribution_tax_distorts`): an anticipated change distorts investment.
* **Walras' law and Ricardian equivalence**: with the government budget constraint, the resource
  constraint and `ψ ≡ 1`, the household's budget constraint holds (`rm_walras`); so the
  equilibrium conditions involve `(B, T)` only through the government budget constraint, and any
  other debt and lump-sum tax path satisfying it supports the same equilibrium
  (`rm_ricardian`).

**Corrections.**
1. The proof of Proposition 14.1.1 drops the factor `1 − τᵈ_{t+1}` on `D_{t+1}`: the printed
   step `Q_tK_{t+1} = βΛ_{t+1}/Λ_t(D_{t+1} + Q_{t+1}K_{t+2})` contradicts the true one unless
   `τᵈ_{t+1}D_{t+1} = 0` (`rm_prop_14_1_1_misprint`), and the printed sum
   `∑ βʲΛ_{t+j}/Λ_t D_{t+j}` must be `∑ βʲΛ_{t+j}/Λ_t (1 − τᵈ_{t+j})D_{t+j}`. The
   proposition itself is correct. (The proof also writes `w_tN_{t+1}` for `w_{t+1}N_{t+1}`.)
2. The government budget constraint prints corporate revenue `τᶜ(F − wN)`, but the dividend
   definition gives the firm a depreciation allowance, so corporate revenue is
   `τᶜ(F − wN − δK)`. With the printed constraint, Walras' law fails: the household budget,
   the printed government budget and the resource constraint together force `τᶜδK = 0`
   (`rm_gov_budget_misprint`). `RMFiscalEq` uses the corrected constraint.
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-- The tax rates of §14.1.2: consumption `τs`, distribution `τd`, labour `τn`, corporate `τc`. -/
structure RMTaxes where
  τs : ℕ → ℝ
  τd : ℕ → ℝ
  τn : ℕ → ℝ
  τc : ℕ → ℝ

/-- Quantities and prices of §14.1.2. `lam` is the household's multiplier `Λ`. -/
structure RMFiscalPath where
  C : ℕ → ℝ
  N : ℕ → ℝ
  K : ℕ → ℝ
  I : ℕ → ℝ
  G : ℕ → ℝ
  w : ℕ → ℝ
  R : ℕ → ℝ
  lam : ℕ → ℝ
  V : ℕ → ℝ
  D : ℕ → ℝ
  Q : ℕ → ℝ
  B : ℕ → ℝ
  T : ℕ → ℝ

/-- The government budget constraint (Miao, p. 469, corporate revenue corrected to
`τᶜ(F − wN − δK)`). -/
def rmGovBudget (F : ℝ → ℝ → ℝ) (δ : ℝ) (τ : RMTaxes) (p : RMFiscalPath) (t : ℕ) : Prop :=
  p.G t + p.B t = p.B (t + 1) / p.R t + τ.τs t * p.C t + τ.τd t * p.D t +
    τ.τc t * (F (p.K t) (p.N t) - p.w t * p.N t - δ * p.K t) + τ.τn t * p.w t * p.N t + p.T t

/-- The equilibrium system of §14.1.2 (Miao, pp. 468–469): the household's first-order
conditions, the dividend definition, (14.18), the firm's labour condition `w = F_N`, (14.19),
(14.20), the government budget constraint (corrected) and the resource constraint. -/
def RMFiscalEq (uC uN F FK FN : ℝ → ℝ → ℝ) (β δ : ℝ) (τ : RMTaxes) (p : RMFiscalPath) :
    Prop :=
  ∀ t, uC (p.C t) (p.N t) = (1 + τ.τs t) * p.lam t ∧
    -uN (p.C t) (p.N t) = (1 - τ.τn t) * p.lam t * p.w t ∧
    p.lam t * (p.V t - (1 - τ.τd t) * p.D t) = β * p.lam (t + 1) * p.V (t + 1) ∧
    p.lam t = β * p.lam (t + 1) * p.R t ∧
    p.D t = (1 - τ.τc t) * (F (p.K t) (p.N t) - p.w t * p.N t) - p.I t +
      τ.τc t * δ * p.K t ∧
    p.K (t + 1) = (1 - δ) * p.K t + p.I t ∧
    p.w t = FN (p.K t) (p.N t) ∧
    p.Q t = 1 - τ.τd t ∧
    p.Q t = β * p.lam (t + 1) / p.lam t * ((1 - δ) * p.Q (t + 1) +
      (1 - τ.τd (t + 1)) * τ.τc (t + 1) * δ +
      (1 - τ.τd (t + 1)) * (1 - τ.τc (t + 1)) * FK (p.K (t + 1)) (p.N (t + 1))) ∧
    rmGovBudget F δ τ p t ∧
    p.C t + p.I t + p.G t = F (p.K t) (p.N t)

/-! ### Household and firm first-order conditions -/

/-- Miao, p. 468: the `C` and `B` conditions give
`u_C(t)/(1 + τˢ_t) = βR_tu_C(t + 1)/(1 + τˢ_{t+1})`. -/
theorem rm_fiscal_euler {uc0 uc1 τs0 τs1 l0 l1 β R : ℝ} (h0 : 1 + τs0 ≠ 0) (h1 : 1 + τs1 ≠ 0)
    (hc0 : uc0 = (1 + τs0) * l0) (hc1 : uc1 = (1 + τs1) * l1) (hb : l0 = β * l1 * R) :
    uc0 / (1 + τs0) = β * R * (uc1 / (1 + τs1)) := by
  rw [hc0, hc1]; field_simp; rw [hb]; ring

/-- Miao, p. 468: the `C` and `N` conditions give `−u_N/u_C = (1 − τⁿ)w/(1 + τˢ)`. -/
theorem rm_fiscal_labour {uc un τs τn l w : ℝ} (hs : 1 + τs ≠ 0) (hl : l ≠ 0)
    (hc : uc = (1 + τs) * l) (hn : -un = (1 - τn) * l * w) :
    -un / uc = (1 - τn) * w / (1 + τs) := by
  rw [hn, hc]; field_simp

/-- Miao, p. 468: the share condition is the firm's value recursion
`V_t = (1 − τᵈ_t)D_t + βΛ_{t+1}/Λ_t V_{t+1}` (the firm's objective). -/
theorem rm_fiscal_value_recursion {l0 l1 V0 V1 D0 τd0 β : ℝ} (hl : l0 ≠ 0)
    (h : l0 * (V0 - (1 - τd0) * D0) = β * l1 * V1) :
    V0 = (1 - τd0) * D0 + β * l1 / l0 * V1 := by
  field_simp; linarith

/-- **(14.19)–(14.20)** (Miao, p. 469): if raising `K_{t+1}` to `x` (cutting date-`t` dividends
one-for-one and raising date-`t+1` dividends by `(1 − τᶜ)F(x, N) + (1 − δ + τᶜδ)x`) leaves the
after-tax value `−(1 − τᵈ_t)x + m(1 − τᵈ_{t+1})[(1 − τᶜ)F(x, N) + (1 − δ + τᶜδ)x]` at a local
maximum at `K_{t+1}`, with `m = βΛ_{t+1}/Λ_t`, then (14.20) holds with `Q = 1 − τᵈ`. -/
theorem eq_14_20 {F FK : ℝ → ℝ → ℝ} {m δ K1 N1 τd0 τd1 τc1 : ℝ}
    (hF : HasDerivAt (fun x => F x N1) (FK K1 N1) K1)
    (hmax : IsLocalMax (fun x => -(1 - τd0) * x +
      m * (1 - τd1) * ((1 - τc1) * F x N1 + (1 - δ + τc1 * δ) * x)) K1) :
    1 - τd0 = m * ((1 - δ) * (1 - τd1) + (1 - τd1) * τc1 * δ +
      (1 - τd1) * (1 - τc1) * FK K1 N1) := by
  have hd : HasDerivAt (fun x => -(1 - τd0) * x +
      m * (1 - τd1) * ((1 - τc1) * F x N1 + (1 - δ + τc1 * δ) * x))
      (-(1 - τd0) * 1 + m * (1 - τd1) * ((1 - τc1) * FK K1 N1 + (1 - δ + τc1 * δ) * 1)) K1 :=
    ((hasDerivAt_id K1).const_mul _).add
      (((hF.const_mul (1 - τc1)).add ((hasDerivAt_id K1).const_mul _)).const_mul _)
  have := hmax.hasDerivAt_eq_zero hd
  linear_combination -this

/-! ### Proposition 14.1.1 -/

/-- Miao, p. 469 (proof of Proposition 14.1.1, corrected): multiplying (14.20) by `K_{t+1}` and
using `F = F_KK + F_NN`, `w = F_N`, (14.18), (14.19) and the dividend definition,
`Q_tK_{t+1} = βΛ_{t+1}/Λ_t[(1 − τᵈ_{t+1})D_{t+1} + Q_{t+1}K_{t+2}]`. -/
theorem rm_prop_14_1_1_step {F FK FN : ℝ → ℝ → ℝ} {β δ : ℝ} {τ : RMTaxes} {p : RMFiscalPath}
    (t : ℕ)
    (h20 : p.Q t = β * p.lam (t + 1) / p.lam t * ((1 - δ) * p.Q (t + 1) +
      (1 - τ.τd (t + 1)) * τ.τc (t + 1) * δ +
      (1 - τ.τd (t + 1)) * (1 - τ.τc (t + 1)) * FK (p.K (t + 1)) (p.N (t + 1))))
    (h19 : p.Q (t + 1) = 1 - τ.τd (t + 1)) (hw : p.w (t + 1) = FN (p.K (t + 1)) (p.N (t + 1)))
    (hE : F (p.K (t + 1)) (p.N (t + 1)) = FK (p.K (t + 1)) (p.N (t + 1)) * p.K (t + 1) +
      FN (p.K (t + 1)) (p.N (t + 1)) * p.N (t + 1))
    (hacc : p.K (t + 1 + 1) = (1 - δ) * p.K (t + 1) + p.I (t + 1))
    (hD : p.D (t + 1) = (1 - τ.τc (t + 1)) * (F (p.K (t + 1)) (p.N (t + 1)) -
      p.w (t + 1) * p.N (t + 1)) - p.I (t + 1) + τ.τc (t + 1) * δ * p.K (t + 1)) :
    p.Q t * p.K (t + 1) = β * p.lam (t + 1) / p.lam t *
      ((1 - τ.τd (t + 1)) * p.D (t + 1) + p.Q (t + 1) * p.K (t + 2)) := by
  rw [show t + 2 = t + 1 + 1 by ring, hacc, hD, h20, h19, hw, hE]
  ring

/-- Correction to Miao, p. 469: the printed step `Q_tK_{t+1} = βΛ_{t+1}/Λ_t(D_{t+1} +
Q_{t+1}K_{t+2})` and the true one hold together only if `τᵈ_{t+1}D_{t+1} = 0`. -/
theorem rm_prop_14_1_1_misprint {m D1 Q1K2 τd1 QK : ℝ} (hm : m ≠ 0)
    (htrue : QK = m * ((1 - τd1) * D1 + Q1K2)) (hprinted : QK = m * (D1 + Q1K2)) :
    τd1 * D1 = 0 := by
  have : m * (τd1 * D1) = 0 := by linear_combination htrue - hprinted
  exact (mul_eq_zero.1 this).resolve_left hm

/-- Miao, p. 470 (Proposition 14.1.1, the forward solution, corrected): if the one-step identity
holds at every date and the transversality condition `lim β^TΛ_TQ_TK_{T+1} = 0` holds, then
`Q_tK_{t+1} = ∑_{j≥1} βʲΛ_{t+j}/Λ_t (1 − τᵈ_{t+j})D_{t+j}` (limit of partial sums). -/
theorem rm_prop_14_1_1_sum {β : ℝ} {lam Y D τd : ℕ → ℝ} (hβ : 0 < β) (hl : ∀ s, lam s ≠ 0)
    (hstep : ∀ s, Y s = β * lam (s + 1) / lam s * ((1 - τd (s + 1)) * D (s + 1) + Y (s + 1)))
    (htvc : Tendsto (fun s => β ^ s * lam s * Y s) atTop (𝓝 0)) (t : ℕ) :
    Tendsto (fun T => ∑ j ∈ Finset.range T,
      β ^ (j + 1) * lam (t + j + 1) / lam t * ((1 - τd (t + j + 1)) * D (t + j + 1))) atTop
      (𝓝 (Y t)) := by
  have hstep' : ∀ s, lam s * Y s =
      β * lam (s + 1) * ((1 - τd (s + 1)) * D (s + 1)) + β * lam (s + 1) * Y (s + 1) := by
    intro s; rw [hstep s]; field_simp [hl s]
  have hpart : ∀ T, lam t * Y t = ∑ j ∈ Finset.range T,
      β ^ (j + 1) * lam (t + j + 1) * ((1 - τd (t + j + 1)) * D (t + j + 1)) +
      β ^ T * lam (t + T) * Y (t + T) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, ih, show t + (T + 1) = t + T + 1 by ring]
      have := hstep' (t + T)
      linear_combination β ^ T * this
  have hT : ∀ T, ∑ j ∈ Finset.range T,
      β ^ (j + 1) * lam (t + j + 1) / lam t * ((1 - τd (t + j + 1)) * D (t + j + 1)) =
      Y t - (β ^ t)⁻¹ * (β ^ (t + T) * lam (t + T) * Y (t + T)) / lam t := by
    intro T
    have h := hpart T
    have hsum : ∑ j ∈ Finset.range T,
        β ^ (j + 1) * lam (t + j + 1) / lam t * ((1 - τd (t + j + 1)) * D (t + j + 1)) =
        (∑ j ∈ Finset.range T,
          β ^ (j + 1) * lam (t + j + 1) * ((1 - τd (t + j + 1)) * D (t + j + 1))) / lam t := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hS : (∑ j ∈ Finset.range T,
        β ^ (j + 1) * lam (t + j + 1) * ((1 - τd (t + j + 1)) * D (t + j + 1))) =
        lam t * Y t - β ^ T * lam (t + T) * Y (t + T) := by linarith [h]
    rw [hsum, hS, pow_add]
    field_simp [hl t, (pow_pos hβ t).ne']
  simp only [hT]
  have h1 : Tendsto (fun T => β ^ (t + T) * lam (t + T) * Y (t + T)) atTop (𝓝 0) := by
    have := (tendsto_add_atTop_iff_nat t).2 htvc
    exact this.congr (fun T => by rw [add_comm T t])
  have := ((h1.const_mul (β ^ t)⁻¹).div_const (lam t)).const_sub (Y t)
  simpa using this

/-- Miao, p. 470 (Proposition 14.1.1, "`Q_tK_{t+1}` is the ex-dividend equity value"): if the
ex-dividend value `X_t = V_t − (1 − τᵈ_t)D_t` satisfies the share condition, `Y_t = Q_tK_{t+1}`
satisfies the one-step identity, and both `β^TΛ_TV_T` and `β^TΛ_TQ_TK_{T+1}` tend to zero, then
`V_t − (1 − τᵈ_t)D_t = Q_tK_{t+1}`. -/
theorem rm_prop_14_1_1_exdiv {β : ℝ} {lam V D Y τd : ℕ → ℝ} (hβ : 0 < β)
    (hl : ∀ s, lam s ≠ 0)
    (hψ : ∀ s, lam s * (V s - (1 - τd s) * D s) = β * lam (s + 1) * V (s + 1))
    (hstep : ∀ s, Y s = β * lam (s + 1) / lam s * ((1 - τd (s + 1)) * D (s + 1) + Y (s + 1)))
    (hnb : Tendsto (fun s => β ^ s * lam s * V s) atTop (𝓝 0))
    (htvc : Tendsto (fun s => β ^ s * lam s * Y s) atTop (𝓝 0)) (t : ℕ) :
    V t - (1 - τd t) * D t = Y t := by
  set e : ℕ → ℝ := fun s => β ^ s * lam s * (V s - (1 - τd s) * D s - Y s) with he
  have hsucc : ∀ s, e (s + 1) = e s := by
    intro s
    have h1 := hψ s
    have h2 : lam s * Y s = β * lam (s + 1) * ((1 - τd (s + 1)) * D (s + 1) + Y (s + 1)) := by
      rw [hstep s]; field_simp [hl s]
    simp only [he, pow_succ]
    linear_combination (-(β ^ s)) * h1 + β ^ s * h2
  have hconst : ∀ s, e s = e 0 := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [hsucc, ih]
  have hlim : Tendsto e atTop (𝓝 0) := by
    have hX : Tendsto (fun s => β ^ s * lam s * (V s - (1 - τd s) * D s)) atTop (𝓝 0) := by
      have := (tendsto_add_atTop_iff_nat 1).2 hnb
      refine this.congr (fun s => ?_)
      rw [mul_assoc (β ^ s), hψ s, pow_succ]; ring
    have := hX.sub htvc
    simp only [sub_zero] at this
    exact this.congr (fun s => by simp only [he]; ring)
  have h0 : e 0 = 0 := by
    have : Tendsto e atTop (𝓝 (e 0)) := by
      rw [show e = fun _ => e 0 from funext hconst]; exact tendsto_const_nhds
    exact tendsto_nhds_unique this hlim
  have := hconst t
  rw [h0] at this
  simp only [he] at this
  have hne : β ^ t * lam t ≠ 0 := mul_ne_zero (pow_pos hβ t).ne' (hl t)
  have := (mul_eq_zero.1 this).resolve_left hne
  linarith

/-- **Proposition 14.1.1** (Miao, p. 469, McGrattan and Prescott 2005): in an equilibrium of
§14.1.2 in which `F = F_KK + F_NN` along the path, `Λ_t ≠ 0`, and the transversality conditions
`lim β^TΛ_TQ_TK_{T+1} = 0` and `lim β^TΛ_TV_T = 0` hold, the ex-dividend equity value is
`V_t − (1 − τᵈ_t)D_t = (1 − τᵈ_t)K_{t+1}`. -/
theorem proposition_14_1_1 {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ : ℝ} {τ : RMTaxes}
    {p : RMFiscalPath} (hβ : 0 < β) (heq : RMFiscalEq uC uN F FK FN β δ τ p)
    (hl : ∀ s, p.lam s ≠ 0)
    (hE : ∀ s, F (p.K s) (p.N s) = FK (p.K s) (p.N s) * p.K s + FN (p.K s) (p.N s) * p.N s)
    (hnb : Tendsto (fun s => β ^ s * p.lam s * p.V s) atTop (𝓝 0))
    (htvc : Tendsto (fun s => β ^ s * p.lam s * (p.Q s * p.K (s + 1))) atTop (𝓝 0)) (t : ℕ) :
    p.V t - (1 - τ.τd t) * p.D t = (1 - τ.τd t) * p.K (t + 1) := by
  have hstep : ∀ s, p.Q s * p.K (s + 1) = β * p.lam (s + 1) / p.lam s *
      ((1 - τ.τd (s + 1)) * p.D (s + 1) + p.Q (s + 1) * p.K (s + 1 + 1)) := fun s =>
    rm_prop_14_1_1_step s (heq s).2.2.2.2.2.2.2.2.1 (heq (s + 1)).2.2.2.2.2.2.2.1
      (heq (s + 1)).2.2.2.2.2.2.1 (hE (s + 1)) (heq (s + 1)).2.2.2.2.2.1
      (heq (s + 1)).2.2.2.2.1
  have := rm_prop_14_1_1_exdiv (Y := fun s => p.Q s * p.K (s + 1)) hβ hl
    (fun s => (heq s).2.2.1) hstep hnb htvc t
  rw [this, (heq t).2.2.2.2.2.2.2.1]

/-! ### Distribution taxes -/

/-- **(14.21)** (Miao, p. 470): with constant `τᵈ ≠ 1` and `τᶜ`, (14.19) and (14.20) are
equivalent to `1 = βΛ_{t+1}/Λ_t[(1 − δ) + τᶜδ + (1 − τᶜ)F_K(K_{t+1}, N_{t+1})]`. -/
theorem eq_14_21 {m δ τd τc FK1 : ℝ} (hτ : 1 - τd ≠ 0) :
    (1 - τd = m * ((1 - δ) * (1 - τd) + (1 - τd) * τc * δ + (1 - τd) * (1 - τc) * FK1)) ↔
      1 = m * ((1 - δ) + τc * δ + (1 - τc) * FK1) := by
  constructor
  · intro h
    have : (1 - τd) * 1 = (1 - τd) * (m * ((1 - δ) + τc * δ + (1 - τc) * FK1)) := by
      linear_combination h
    exact mul_left_cancel₀ hτ this
  · intro h; linear_combination (1 - τd) * h

/-- Miao, pp. 470–471 (temporary changes): with a time-varying distribution tax (14.19)–(14.20)
are equivalent to `(1 − τᵈ_t)/(1 − τᵈ_{t+1}) = βΛ_{t+1}/Λ_t[(1 − δ) + τᶜδ + (1 − τᶜ)F_K]`. -/
theorem rm_temporary_distribution_tax {m δ τd0 τd1 τc FK1 : ℝ} (hτ : 1 - τd1 ≠ 0) :
    (1 - τd0 = m * ((1 - δ) * (1 - τd1) + (1 - τd1) * τc * δ + (1 - τd1) * (1 - τc) * FK1)) ↔
      (1 - τd0) / (1 - τd1) = m * ((1 - δ) + τc * δ + (1 - τc) * FK1) := by
  rw [div_eq_iff hτ]
  constructor <;> intro h <;> linear_combination h

/-- Miao, pp. 470–471: a temporary (anticipated) change in the distribution tax distorts the
investment decision: the time-varying condition agrees with (14.21) only if `τᵈ_t = τᵈ_{t+1}`. -/
theorem rm_temporary_distribution_tax_distorts {m δ τd0 τd1 τc FK1 : ℝ} (hτ : 1 - τd1 ≠ 0)
    (htv : (1 - τd0) / (1 - τd1) = m * ((1 - δ) + τc * δ + (1 - τc) * FK1))
    (h21 : 1 = m * ((1 - δ) + τc * δ + (1 - τc) * FK1)) : τd0 = τd1 := by
  rw [← h21, div_eq_one_iff_eq hτ] at htv
  linarith

/-- **A permanent change in the distribution tax is neutral** (Miao, p. 470): take an
equilibrium with constant `τᵈ ≠ 1`, constant `τᶜ`, and lump-sum taxes balancing the budget.
For any constant `τᵈ' ≠ 1`, the same allocation with the same `Λ, w, R, D, B`, the price of
capital `Q' = 1 − τᵈ'`, equity value `V'_t = (1 − τᵈ')(D_t + K_{t+1})` and lump-sum taxes
`T'_t = T_t + (τᵈ − τᵈ')D_t` is an equilibrium for `τᵈ'`. (Requires `F = F_KK + F_NN`.) -/
theorem rm_distribution_tax_neutral {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ td td' tc : ℝ}
    {τs τn : ℕ → ℝ} {p : RMFiscalPath}
    (heq : RMFiscalEq uC uN F FK FN β δ ⟨τs, fun _ => td, τn, fun _ => tc⟩ p)
    (hτ : 1 - td ≠ 0) (hl : ∀ s, p.lam s ≠ 0)
    (hE : ∀ s, F (p.K s) (p.N s) = FK (p.K s) (p.N s) * p.K s + FN (p.K s) (p.N s) * p.N s) :
    RMFiscalEq uC uN F FK FN β δ ⟨τs, fun _ => td', τn, fun _ => tc⟩
      { p with V := fun s => (1 - td') * (p.D s + p.K (s + 1)), Q := fun _ => 1 - td',
               T := fun s => p.T s + (td - td') * p.D s } := by
  -- the τᵈ-free capital condition `Λ_tK_{t+1} = βΛ_{t+1}(D_{t+1} + K_{t+2})`
  have hkey : ∀ s, p.lam s * p.K (s + 1) =
      β * p.lam (s + 1) * (p.D (s + 1) + p.K (s + 1 + 1)) := by
    intro s
    have h := rm_prop_14_1_1_step (F := F) (FK := FK) (FN := FN) (β := β) (δ := δ)
      (τ := ⟨τs, fun _ => td, τn, fun _ => tc⟩) (p := p) s (heq s).2.2.2.2.2.2.2.2.1
      (heq (s + 1)).2.2.2.2.2.2.2.1 (heq (s + 1)).2.2.2.2.2.2.1 (hE (s + 1))
      (heq (s + 1)).2.2.2.2.2.1 (heq (s + 1)).2.2.2.2.1
    rw [(heq s).2.2.2.2.2.2.2.1, (heq (s + 1)).2.2.2.2.2.2.2.1] at h
    simp only at h
    rw [show s + 2 = s + 1 + 1 by ring] at h
    field_simp [hl s] at h
    linear_combination h
  intro t
  obtain ⟨h1, h2, -, h4, h5, h6, h7, -, h9, h10, h11⟩ := heq t
  simp only at h1 h2 h4 h5 h6 h7 h9 h10 h11 ⊢
  refine ⟨h1, h2, ?_, h4, h5, h6, h7, trivial, ?_, ?_, h11⟩
  · have := hkey t
    linear_combination (1 - td') * this
  · -- (14.20) for `τᵈ'` from (14.20) for `τᵈ`
    have h9' := h9
    rw [(heq t).2.2.2.2.2.2.2.1, (heq (t + 1)).2.2.2.2.2.2.2.1] at h9'
    simp only at h9'
    have h21 := (eq_14_21 hτ).1 h9'
    linear_combination (1 - td') * h21
  · simp only [rmGovBudget] at h10 ⊢
    linear_combination h10

/-! ### Government budget, Walras' law and Ricardian equivalence -/

/-- **Walras' law** (Miao, pp. 468–469): with the (corrected) government budget constraint, the
dividend definition and the resource constraint, the household's budget constraint with
`ψ_t = ψ_{t+1} = 1` holds:
`(1 + τˢ)C + (V − (1 − τᵈ)D) + B_{t+1}/R = V + (1 − τⁿ)wN + B − T`. -/
theorem rm_walras {F : ℝ → ℝ → ℝ} {δ : ℝ} {τ : RMTaxes} {p : RMFiscalPath} (t : ℕ)
    (hgov : rmGovBudget F δ τ p t)
    (hD : p.D t = (1 - τ.τc t) * (F (p.K t) (p.N t) - p.w t * p.N t) - p.I t +
      τ.τc t * δ * p.K t)
    (hres : p.C t + p.I t + p.G t = F (p.K t) (p.N t)) :
    (1 + τ.τs t) * p.C t + 1 * (p.V t - (1 - τ.τd t) * p.D t) + p.B (t + 1) / p.R t =
      1 * p.V t + (1 - τ.τn t) * p.w t * p.N t + p.B t - p.T t := by
  simp only [rmGovBudget] at hgov
  linear_combination -hgov + hres - hD

/-- Correction to Miao, p. 469: with the printed government budget constraint (corporate revenue
`τᶜ(F − wN)`), the household's budget constraint, the dividend definition and the resource
constraint together force `τᶜ_tδK_t = 0`. -/
theorem rm_gov_budget_misprint {F : ℝ → ℝ → ℝ} {δ : ℝ} {τ : RMTaxes} {p : RMFiscalPath}
    (t : ℕ)
    (hgov : p.G t + p.B t = p.B (t + 1) / p.R t + τ.τs t * p.C t + τ.τd t * p.D t +
      τ.τc t * (F (p.K t) (p.N t) - p.w t * p.N t) + τ.τn t * p.w t * p.N t + p.T t)
    (hhh : (1 + τ.τs t) * p.C t + (p.V t - (1 - τ.τd t) * p.D t) + p.B (t + 1) / p.R t =
      p.V t + (1 - τ.τn t) * p.w t * p.N t + p.B t - p.T t)
    (hD : p.D t = (1 - τ.τc t) * (F (p.K t) (p.N t) - p.w t * p.N t) - p.I t +
      τ.τc t * δ * p.K t)
    (hres : p.C t + p.I t + p.G t = F (p.K t) (p.N t)) : τ.τc t * δ * p.K t = 0 := by
  linear_combination -hgov - hhh - hD + hres

/-- **Ricardian equivalence** (Miao, §14.1.2): the equilibrium conditions involve the debt and
lump-sum tax paths only through the government budget constraint. Hence if `p` is an
equilibrium and `(B', T')` is any other path satisfying the government budget constraint with
the same allocation, prices and distortionary taxes, then `p` with `(B', T')` is an equilibrium,
and the household's budget constraint holds along it. -/
theorem rm_ricardian {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ : ℝ} {τ : RMTaxes} {p : RMFiscalPath}
    (heq : RMFiscalEq uC uN F FK FN β δ τ p) {B' T' : ℕ → ℝ}
    (hgov : ∀ t, rmGovBudget F δ τ { p with B := B', T := T' } t) :
    RMFiscalEq uC uN F FK FN β δ τ { p with B := B', T := T' } ∧
      ∀ t, (1 + τ.τs t) * p.C t + 1 * (p.V t - (1 - τ.τd t) * p.D t) + B' (t + 1) / p.R t =
        1 * p.V t + (1 - τ.τn t) * p.w t * p.N t + B' t - T' t := by
  have h : RMFiscalEq uC uN F FK FN β δ τ { p with B := B', T := T' } := by
    intro t
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11⟩ := heq t
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hgov t, h11⟩
  refine ⟨h, fun t => ?_⟩
  exact rm_walras (p := { p with B := B', T := T' }) t (hgov t) (h t).2.2.2.2.1
    (h t).2.2.2.2.2.2.2.2.2.2

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RMFiscal
import NeoclassicalGrowth.RMSteady

/-!
# Exercises 14.1 and 14.2

Miao, §14.4, p. 507.

**Exercise 14.1.** The model of §14.1.2 in two further market arrangements in which households
own capital, rent it to firms at `R^k` and pay a capital income tax `τᵏ` on `(R^k − δ)K`
(the counterpart of the corporate tax with its depreciation allowance):

* sequential markets with one-period bonds (`RMHKPath`, `RMHKEq`); the household's
  first-order condition for `K_{t+1}` is `Λ_t = βΛ_{t+1}[(1 − δ) + R^k_{t+1} − τᵏ_{t+1}(R^k_{t+1} −
  δ)]`;
* an Arrow–Debreu market at date 0 (`RMADPath`, `RMADEq`), with date-0 prices `q_t`, the
  first-order conditions `βᵗu_C = λq_t(1 + τˢ_t)`, `−βᵗu_N = λq_t(1 − τⁿ_t)w_t`,
  `q_t = q_{t+1}[(1 − δ) + R^k_{t+1} − τᵏ_{t+1}(R^k_{t+1} − δ)]`.

With `τᵏ = τᶜ` and a constant distribution tax, the three arrangements (with the one of §14.1.2,
`RMFiscalEq`) have exactly the same equilibrium allocations: each is equivalent to the
allocation system `RMFiscalAlloc` (`ex_14_1_firm`, `ex_14_1_hk`, `ex_14_1_ad`), hence to each
other (`ex_14_1`).

**Exercise 14.2.** The steady state of §14.1.2 (`ex_14_2`): `R = 1/β`, the modified golden rule
with taxes `1 = β[(1 − δ) + τᶜδ + (1 − τᶜ)F_K]`, i.e. `F_K = (1/β − 1)/(1 − τᶜ) + δ`
(`ex_14_2_mgr`), `−u_N/u_C = (1 − τⁿ)F_N/(1 + τˢ)`, `I = δK`, `C + δK + G = F`, `Q = 1 − τᵈ`,
`V = (1 − τᵈ)D/(1 − β)`, and the government budget `G + (1 − β)B = revenue + T`. With constant
returns the dividends are `D = (1/β − 1)K` and the equity value `V = (1 − τᵈ)K/β`
(`ex_14_2_value`). The capital–labour ratio is unique (`rm_steady_ratio_exists_unique` applies),
independent of `τᵈ, τˢ, τⁿ`, and decreasing in `τᶜ` (`ex_14_2_corporate_tax`). For Cobb–Douglas
the ratio is `((α/r))^{1/(1−α)}` with `r = (1/β − 1)/(1 − τᶜ) + δ` (`ex_14_2_cd`). A concrete
steady state shows that the equilibrium system is satisfiable (`rm_fiscal_eq_example`).

**Departures.** Equilibria are described by their first-order conditions (as in the text). In
the Arrow–Debreu arrangement the government balances its budget date by date with lump-sum
taxes (by Ricardian equivalence, `rm_ricardian`, the timing of lump-sum taxes does not matter).
The equivalence uses a constant distribution tax: with a time-varying `τᵈ` the firm-ownership
arrangement has the distorted condition of `rm_temporary_distribution_tax`.
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-- The allocation system common to the three arrangements: the consumption Euler equation with
the after-tax return on capital, the labour condition, (14.18) and the resource constraint. -/
def RMFiscalAlloc (uC uN F FK FN : ℝ → ℝ → ℝ) (β δ : ℝ) (τs τn τc : ℕ → ℝ)
    (C N K I G : ℕ → ℝ) : Prop :=
  ∀ t, uC (C t) (N t) / (1 + τs t) = β * (uC (C (t + 1)) (N (t + 1)) / (1 + τs (t + 1))) *
      ((1 - δ) + τc (t + 1) * δ + (1 - τc (t + 1)) * FK (K (t + 1)) (N (t + 1))) ∧
    -uN (C t) (N t) / uC (C t) (N t) = (1 - τn t) / (1 + τs t) * FN (K t) (N t) ∧
    K (t + 1) = (1 - δ) * K t + I t ∧ C t + I t + G t = F (K t) (N t)

/-! ### The arrangement of §14.1.2 -/

/-- **Exercise 14.1** (Miao, p. 507), the arrangement of §14.1.2 (firms own capital): with a
constant distribution tax `τᵈ ≠ 1`, an allocation is an equilibrium allocation iff it satisfies
`RMFiscalAlloc`. (`u_C ≠ 0`, `1 + τˢ ≠ 0`, `β > 0`, and `F = F_KK + F_NN` along the allocation.) -/
theorem ex_14_1_firm {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ td : ℝ} {τs τn τc : ℕ → ℝ}
    {C N K I G : ℕ → ℝ} (hβ : 0 < β) (htd : 1 - td ≠ 0) (hs : ∀ t, 1 + τs t ≠ 0)
    (huc : ∀ t, uC (C t) (N t) ≠ 0)
    (hE : ∀ t, F (K t) (N t) = FK (K t) (N t) * K t + FN (K t) (N t) * N t) :
    (∃ p : RMFiscalPath, RMFiscalEq uC uN F FK FN β δ ⟨τs, fun _ => td, τn, τc⟩ p ∧
      p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G) ↔
      RMFiscalAlloc uC uN F FK FN β δ τs τn τc C N K I G := by
  constructor
  · rintro ⟨p, heq, rfl, rfl, rfl, rfl, rfl⟩ t
    obtain ⟨h1, h2, -, -, -, h6, h7, h8, h9, -, h11⟩ := heq t
    obtain ⟨h1', -⟩ := heq (t + 1)
    have h8' := (heq (t + 1)).2.2.2.2.2.2.2.1
    simp only at h1 h2 h6 h7 h8 h9 h11 h1' h8'
    have hl : p.lam t ≠ 0 := fun h => huc t (by rw [h1, h, mul_zero])
    rw [h8, h8'] at h9
    have h21 := (eq_14_21 htd).1 h9
    refine ⟨?_, ?_, h6, h11⟩
    · rw [h1, h1', mul_div_cancel_left₀ _ (hs t), mul_div_cancel_left₀ _ (hs (t + 1))]
      field_simp at h21
      linear_combination h21
    · rw [rm_fiscal_labour (hs t) hl h1 h2, h7]; ring
  · intro h
    set lam : ℕ → ℝ := fun t => uC (C t) (N t) / (1 + τs t) with hlam
    have hl : ∀ t, lam t ≠ 0 := fun t => div_ne_zero (huc t) (hs t)
    set w : ℕ → ℝ := fun t => FN (K t) (N t) with hw
    set D : ℕ → ℝ := fun t => (1 - τc t) * (F (K t) (N t) - w t * N t) - I t + τc t * δ * K t
      with hD
    refine ⟨⟨C, N, K, I, G, w, fun t => lam t / (β * lam (t + 1)), lam,
      fun t => (1 - td) * (D t + K (t + 1)), D, fun _ => 1 - td, fun _ => 0,
      fun t => G t - τs t * C t - td * D t -
        τc t * (F (K t) (N t) - w t * N t - δ * K t) - τn t * w t * N t⟩,
      fun t => ?_, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨e1, e2, e3, e4⟩ := h t
    obtain ⟨-, -, e3', -⟩ := h (t + 1)
    have heul : lam t = β * lam (t + 1) *
        ((1 - δ) + τc (t + 1) * δ + (1 - τc (t + 1)) * FK (K (t + 1)) (N (t + 1))) := by
      simp only [hlam]; rw [e1]
    have hkey : lam t * K (t + 1) = β * lam (t + 1) * (D (t + 1) + K (t + 1 + 1)) := by
      simp only [hD, hw]
      rw [e3', hE (t + 1), heul]; ring
    refine ⟨?_, ?_, ?_, ?_, rfl, e3, rfl, rfl, ?_, ?_, e4⟩
    · simp only [hlam]; field_simp [hs t]
    · simp only [hlam, hw]
      rw [div_eq_iff (huc t)] at e2
      linear_combination e2
    · simp only
      linear_combination (1 - td) * hkey
    · simp only
      field_simp [hl (t + 1), hβ.ne']
    · simp only
      have := (eq_14_21 (m := β * lam (t + 1) / lam t) (δ := δ) (τc := τc (t + 1))
        (FK1 := FK (K (t + 1)) (N (t + 1))) htd).2 (by field_simp [hl t]; linear_combination heul)
      exact this
    · simp only [rmGovBudget, zero_div]; ring

/-! ### Households own capital -/

/-- Quantities and prices when households own capital: rental rate `Rk`, bond return `R`. -/
structure RMHKPath where
  C : ℕ → ℝ
  N : ℕ → ℝ
  K : ℕ → ℝ
  I : ℕ → ℝ
  G : ℕ → ℝ
  w : ℕ → ℝ
  Rk : ℕ → ℝ
  R : ℕ → ℝ
  lam : ℕ → ℝ
  B : ℕ → ℝ
  T : ℕ → ℝ

/-- **Exercise 14.1**, households own capital: the household's first-order conditions for
`C, N, K_{t+1}, B_{t+1}` (budget `(1 + τˢ)C + I + B_{t+1}/R = (1 − τⁿ)wN + R^kK − τᵏ(R^k − δ)K +
B − T`), the firm's static conditions `R^k = F_K`, `w = F_N`, (14.18), the government budget
constraint and the resource constraint. -/
def RMHKEq (uC uN F FK FN : ℝ → ℝ → ℝ) (β δ : ℝ) (τs τn τk : ℕ → ℝ) (p : RMHKPath) : Prop :=
  ∀ t, uC (p.C t) (p.N t) = (1 + τs t) * p.lam t ∧
    -uN (p.C t) (p.N t) = (1 - τn t) * p.lam t * p.w t ∧
    p.lam t = β * p.lam (t + 1) *
      ((1 - δ) + p.Rk (t + 1) - τk (t + 1) * (p.Rk (t + 1) - δ)) ∧
    p.lam t = β * p.lam (t + 1) * p.R t ∧
    p.Rk t = FK (p.K t) (p.N t) ∧ p.w t = FN (p.K t) (p.N t) ∧
    p.K (t + 1) = (1 - δ) * p.K t + p.I t ∧
    p.G t + p.B t = p.B (t + 1) / p.R t + τs t * p.C t + τk t * (p.Rk t - δ) * p.K t +
      τn t * p.w t * p.N t + p.T t ∧
    p.C t + p.I t + p.G t = F (p.K t) (p.N t)

/-- **Exercise 14.1** (Miao, p. 507), households own capital: with `τᵏ = τᶜ`, an allocation is an
equilibrium allocation iff it satisfies `RMFiscalAlloc`. -/
theorem ex_14_1_hk {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ : ℝ} {τs τn τc : ℕ → ℝ}
    {C N K I G : ℕ → ℝ} (hβ : 0 < β) (hs : ∀ t, 1 + τs t ≠ 0)
    (huc : ∀ t, uC (C t) (N t) ≠ 0) :
    (∃ p : RMHKPath, RMHKEq uC uN F FK FN β δ τs τn τc p ∧
      p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G) ↔
      RMFiscalAlloc uC uN F FK FN β δ τs τn τc C N K I G := by
  constructor
  · rintro ⟨p, heq, rfl, rfl, rfl, rfl, rfl⟩ t
    obtain ⟨h1, h2, h3, -, -, h6, h7, -, h9⟩ := heq t
    obtain ⟨h1', -, -, -, h5', -⟩ := heq (t + 1)
    have hl : p.lam t ≠ 0 := fun h => huc t (by rw [h1, h, mul_zero])
    refine ⟨?_, ?_, h7, h9⟩
    · rw [h1, h1', ← h5']
      field_simp [hs t, hs (t + 1)]
      linear_combination h3
    · rw [rm_fiscal_labour (hs t) hl h1 h2, h6]; ring
  · intro h
    set lam : ℕ → ℝ := fun t => uC (C t) (N t) / (1 + τs t) with hlam
    have hl : ∀ t, lam t ≠ 0 := fun t => div_ne_zero (huc t) (hs t)
    refine ⟨⟨C, N, K, I, G, fun t => FN (K t) (N t), fun t => FK (K t) (N t),
      fun t => lam t / (β * lam (t + 1)), lam, fun _ => 0,
      fun t => G t - τs t * C t - τc t * (FK (K t) (N t) - δ) * K t -
        τn t * FN (K t) (N t) * N t⟩, fun t => ?_, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨e1, e2, e3, e4⟩ := h t
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, e3, ?_, e4⟩
    · simp only [hlam]; field_simp [hs t]
    · simp only [hlam]
      rw [div_eq_iff (huc t)] at e2
      linear_combination e2
    · simp only [hlam]; rw [e1]; ring
    · simp only
      field_simp [hl (t + 1), hβ.ne']
    · simp only [zero_div]; ring

/-! ### Arrow–Debreu -/

/-- Quantities and prices of the Arrow–Debreu arrangement: date-0 prices `q`, multiplier `lam0`.
-/
structure RMADPath where
  C : ℕ → ℝ
  N : ℕ → ℝ
  K : ℕ → ℝ
  I : ℕ → ℝ
  G : ℕ → ℝ
  w : ℕ → ℝ
  Rk : ℕ → ℝ
  q : ℕ → ℝ
  lam0 : ℝ
  T : ℕ → ℝ

/-- **Exercise 14.1**, Arrow–Debreu (households own capital, date-0 market): the household's
first-order conditions, the firm's conditions, (14.18), date-by-date government budget balance
and the resource constraint. -/
def RMADEq (uC uN F FK FN : ℝ → ℝ → ℝ) (β δ : ℝ) (τs τn τk : ℕ → ℝ) (p : RMADPath) : Prop :=
  ∀ t, β ^ t * uC (p.C t) (p.N t) = p.lam0 * p.q t * (1 + τs t) ∧
    -(β ^ t * uN (p.C t) (p.N t)) = p.lam0 * p.q t * (1 - τn t) * p.w t ∧
    p.q t = p.q (t + 1) * ((1 - δ) + p.Rk (t + 1) - τk (t + 1) * (p.Rk (t + 1) - δ)) ∧
    p.Rk t = FK (p.K t) (p.N t) ∧ p.w t = FN (p.K t) (p.N t) ∧
    p.K (t + 1) = (1 - δ) * p.K t + p.I t ∧
    p.G t = τs t * p.C t + τk t * (p.Rk t - δ) * p.K t + τn t * p.w t * p.N t + p.T t ∧
    p.C t + p.I t + p.G t = F (p.K t) (p.N t)

/-- **Exercise 14.1** (Miao, p. 507), Arrow–Debreu: with `τᵏ = τᶜ`, an allocation is an
equilibrium allocation iff it satisfies `RMFiscalAlloc`. -/
theorem ex_14_1_ad {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ : ℝ} {τs τn τc : ℕ → ℝ}
    {C N K I G : ℕ → ℝ} (hβ : 0 < β) (hs : ∀ t, 1 + τs t ≠ 0)
    (huc : ∀ t, uC (C t) (N t) ≠ 0) :
    (∃ p : RMADPath, RMADEq uC uN F FK FN β δ τs τn τc p ∧
      p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G) ↔
      RMFiscalAlloc uC uN F FK FN β δ τs τn τc C N K I G := by
  constructor
  · rintro ⟨p, heq, rfl, rfl, rfl, rfl, rfl⟩ t
    obtain ⟨h1, h2, h3, -, h5, h6, -, h8⟩ := heq t
    obtain ⟨h1', -, -, h4', -⟩ := heq (t + 1)
    have hb : β ^ t ≠ 0 := (pow_pos hβ t).ne'
    refine ⟨?_, ?_, h6, h8⟩
    · rw [← h4']
      have hu0 : uC (p.C t) (p.N t) = p.lam0 * p.q t * (1 + τs t) / β ^ t := by
        field_simp; linear_combination h1
      have hu1 : uC (p.C (t + 1)) (p.N (t + 1)) =
          p.lam0 * p.q (t + 1) * (1 + τs (t + 1)) / β ^ (t + 1) := by
        field_simp; linear_combination h1'
      rw [hu0, hu1, h3, pow_succ]
      field_simp [hs t, hs (t + 1)]
      ring
    · rw [← h5, div_eq_iff (huc t)]
      have hd : (1 + τs t) * (1 + τs t)⁻¹ = 1 := mul_inv_cancel₀ (hs t)
      have : β ^ t * (-uN (p.C t) (p.N t)) =
          β ^ t * ((1 - τn t) / (1 + τs t) * p.w t * uC (p.C t) (p.N t)) := by
        linear_combination h2 - ((1 - τn t) / (1 + τs t) * p.w t) * h1 -
          (p.lam0 * p.q t * p.w t * (1 - τn t)) * hd
      exact mul_left_cancel₀ hb this
  · intro h
    refine ⟨⟨C, N, K, I, G, fun t => FN (K t) (N t), fun t => FK (K t) (N t),
      fun t => β ^ t * uC (C t) (N t) / (1 + τs t), 1,
      fun t => G t - τs t * C t - τc t * (FK (K t) (N t) - δ) * K t -
        τn t * FN (K t) (N t) * N t⟩, fun t => ?_, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨e1, e2, e3, e4⟩ := h t
    refine ⟨?_, ?_, ?_, rfl, rfl, e3, ?_, e4⟩
    · simp only; field_simp [hs t]
    · simp only
      rw [div_eq_iff (huc t)] at e2
      linear_combination β ^ t * e2
    · simp only
      linear_combination β ^ t * e1
    · simp only; ring

/-- **Exercise 14.1** (Miao, p. 507): the three arrangements (firms own capital with a constant
distribution tax; households own capital with sequential markets; Arrow–Debreu), with
`τᵏ = τᶜ`, have the same equilibrium allocations. -/
theorem ex_14_1 {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ td : ℝ} {τs τn τc : ℕ → ℝ}
    {C N K I G : ℕ → ℝ} (hβ : 0 < β) (htd : 1 - td ≠ 0) (hs : ∀ t, 1 + τs t ≠ 0)
    (huc : ∀ t, uC (C t) (N t) ≠ 0)
    (hE : ∀ t, F (K t) (N t) = FK (K t) (N t) * K t + FN (K t) (N t) * N t) :
    ((∃ p : RMFiscalPath, RMFiscalEq uC uN F FK FN β δ ⟨τs, fun _ => td, τn, τc⟩ p ∧
      p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G) ↔
      (∃ p : RMHKPath, RMHKEq uC uN F FK FN β δ τs τn τc p ∧
        p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G)) ∧
    ((∃ p : RMHKPath, RMHKEq uC uN F FK FN β δ τs τn τc p ∧
      p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G) ↔
      (∃ p : RMADPath, RMADEq uC uN F FK FN β δ τs τn τc p ∧
        p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G)) := by
  rw [ex_14_1_firm hβ htd hs huc hE, ex_14_1_hk hβ hs huc, ex_14_1_ad hβ hs huc]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-! ### Exercise 14.2: the steady state -/

/-- The constant path with the given values. -/
def rmConstPath (C N K I G w R lam V D Q B T : ℝ) : RMFiscalPath :=
  ⟨fun _ => C, fun _ => N, fun _ => K, fun _ => I, fun _ => G, fun _ => w, fun _ => R,
    fun _ => lam, fun _ => V, fun _ => D, fun _ => Q, fun _ => B, fun _ => T⟩

/-- **Exercise 14.2** (Miao, p. 507): the steady state of §14.1.2. With constant taxes, `β ∈
(0, 1)`, `1 + τˢ ≠ 0`, `τᵈ ≠ 1` and `u_C ≠ 0`, a constant path is an equilibrium iff
`Λ = u_C/(1 + τˢ)`, `w = F_N`, `−u_N/u_C = (1 − τⁿ)F_N/(1 + τˢ)`, `R = 1/β`,
`1 = β[(1 − δ) + τᶜδ + (1 − τᶜ)F_K]`, `Q = 1 − τᵈ`, `I = δK`, the dividend definition,
`V = (1 − τᵈ)D/(1 − β)`, `C + δK + G = F` and the government budget
`G + (1 − β)B = τˢC + τᵈD + τᶜ(F − wN − δK) + τⁿwN + T`. -/
theorem ex_14_2 {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ ts td tn tc : ℝ}
    {C N K I G w R lam V D Q B T : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs : 1 + ts ≠ 0)
    (htd : 1 - td ≠ 0) (huc : uC C N ≠ 0) :
    RMFiscalEq uC uN F FK FN β δ ⟨fun _ => ts, fun _ => td, fun _ => tn, fun _ => tc⟩
        (rmConstPath C N K I G w R lam V D Q B T) ↔
      lam = uC C N / (1 + ts) ∧ w = FN K N ∧
        -uN C N / uC C N = (1 - tn) * FN K N / (1 + ts) ∧ R = 1 / β ∧
        1 = β * ((1 - δ) + tc * δ + (1 - tc) * FK K N) ∧ Q = 1 - td ∧ I = δ * K ∧
        D = (1 - tc) * (F K N - w * N) - I + tc * δ * K ∧ V = (1 - td) * D / (1 - β) ∧
        C + δ * K + G = F K N ∧
        G + (1 - β) * B = ts * C + td * D + tc * (F K N - w * N - δ * K) + tn * w * N + T := by
  have hb1 : 1 - β ≠ 0 := by linarith
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h 0
    simp only [rmConstPath, rmGovBudget] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    have hl : lam ≠ 0 := fun h => huc (by rw [h1, h, mul_zero])
    have hR : R = 1 / β := by
      field_simp
      have : lam * 1 = lam * (β * R) := by linear_combination h4
      linarith [mul_left_cancel₀ hl this]
    have hI : I = δ * K := by linarith
    refine ⟨by field_simp; linarith, h7, ?_, hR, ?_, h8, hI, h5, ?_, by linarith, ?_⟩
    · rw [rm_fiscal_labour hs hl h1 h2, h7]
    · rw [h8] at h9
      have hβl : β * lam / lam = β := by field_simp
      rw [hβl] at h9
      exact (eq_14_21 (m := β) htd).1 h9
    · field_simp
      have : lam * (V - (1 - td) * D) = lam * (β * V) := by linear_combination h3
      have := mul_left_cancel₀ hl this
      linarith
    · rw [hR] at h10
      field_simp at h10
      linear_combination h10
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ t
    have hl : lam ≠ 0 := by rw [h1]; exact div_ne_zero huc hs
    simp only [rmConstPath, rmGovBudget]
    refine ⟨by rw [h1]; field_simp, ?_, ?_, by rw [h4]; field_simp, h8, by linarith, h2, h6,
      ?_, ?_, by linarith⟩
    · rw [div_eq_iff huc] at h3
      rw [h3, h1, h2]; field_simp
    · rw [h9]; field_simp; ring
    · rw [h6]
      have hβl : β * lam / lam = β := by field_simp
      rw [hβl]
      linear_combination (1 - td) * h5
    · rw [h4]; field_simp; linear_combination h11

/-- **Exercise 14.2**, a concrete steady state (so `RMFiscalEq` is satisfiable): linear utility
`u = C − N`, `F(K, N) = (1/β − 1 + δ)K + N`, zero distortionary taxes, `I = δK`,
`C = (1/β − 1)K + N`, `w = 1`, `R = 1/β`, `Λ = Q = 1`, `D = (1/β − 1)K`,
`V = D/(1 − β)`, `B = T = G = 0`. -/
theorem rm_fiscal_eq_example {β δ K N : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    RMFiscalEq (fun _ _ => 1) (fun _ _ => -1) (fun k n => (1 / β - 1 + δ) * k + n)
      (fun _ _ => 1 / β - 1 + δ) (fun _ _ => 1) β δ
      ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
      (rmConstPath ((1 / β - 1) * K + N) N K (δ * K) 0 1 (1 / β) 1
        ((1 / β - 1) * K / (1 - β)) ((1 / β - 1) * K) 1 0 0) := by
  refine (ex_14_2 (uC := fun _ _ => 1) hβ0 hβ1 (by norm_num) (by norm_num)
    (by norm_num)).2 ⟨by norm_num, rfl, by norm_num, rfl, ?_, by norm_num, rfl, by ring,
      by ring, by ring, by ring⟩
  field_simp
  ring

/-- **Exercise 14.2**: the steady-state modified golden rule with a corporate tax,
`F_K = (1/β − 1)/(1 − τᶜ) + δ` (for `τᶜ ≠ 1`). -/
theorem ex_14_2_mgr {β δ tc FK : ℝ} (hβ : 0 < β) (htc : 1 - tc ≠ 0) :
    1 = β * ((1 - δ) + tc * δ + (1 - tc) * FK) ↔ FK = (1 / β - 1) / (1 - tc) + δ := by
  constructor
  · intro h; field_simp; linear_combination -h
  · intro h; rw [h]; field_simp; ring

/-- **Exercise 14.2**: with constant returns (`F = F_KK + F_NN`, `w = F_N`) dividends are
`D = (1/β − 1)K` and the equity value `V = (1 − τᵈ)D/(1 − β) = (1 − τᵈ)K/β`, the steady-state
form of Proposition 14.1.1 (`V − (1 − τᵈ)D = (1 − τᵈ)K`). -/
theorem ex_14_2_value {β δ td tc K N F FK FN w I D V : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hE : F = FK * K + FN * N) (hw : w = FN) (hI : I = δ * K)
    (hmgr : 1 = β * ((1 - δ) + tc * δ + (1 - tc) * FK))
    (hD : D = (1 - tc) * (F - w * N) - I + tc * δ * K) (hV : V = (1 - td) * D / (1 - β)) :
    D = (1 / β - 1) * K ∧ V = (1 - td) * K / β ∧ V - (1 - td) * D = (1 - td) * K := by
  have hb1 : 1 - β ≠ 0 := by linarith
  have hD' : D = (1 / β - 1) * K := by
    rw [hD, hE, hw, hI]; field_simp; linear_combination (-K) * hmgr
  refine ⟨hD', ?_, ?_⟩
  · rw [hV, hD']; field_simp
  · rw [hV, hD']; field_simp; ring

/-- **Exercise 14.2**, comparative statics: the steady-state target
`r(τᶜ) = (1/β − 1)/(1 − τᶜ) + δ` does not involve `τᵈ, τˢ, τⁿ` and is increasing in `τᶜ < 1`, so
a higher corporate tax lowers the capital–labour ratio when `F_K(·, 1)` is strictly
decreasing. -/
theorem ex_14_2_corporate_tax {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0))
    {β δ tc1 tc2 x1 x2 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (htc : tc1 < tc2) (htc2 : tc2 < 1)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (h1 : f x1 = (1 / β - 1) / (1 - tc1) + δ)
    (h2 : f x2 = (1 / β - 1) / (1 - tc2) + δ) : x2 < x1 := by
  refine rm_steady_ratio_anti hanti hx1 hx2 h1 h2 ?_
  have hb : 0 < 1 / β - 1 := by rw [sub_pos, lt_div_iff₀ hβ0]; linarith
  have : (1 / β - 1) / (1 - tc1) < (1 / β - 1) / (1 - tc2) :=
    div_lt_div_of_pos_left hb (by linarith) (by linarith)
  linarith

/-- **Exercise 14.2**, Cobb–Douglas: with `r = (1/β − 1)/(1 − τᶜ) + δ > 0`, the ratio
`x = (α/r)^{1/(1−α)}` solves the modified golden rule `F_K(xN, N) = r` for every `N > 0`. -/
theorem ex_14_2_cd {α r N : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hN : 0 < N) :
    rmCDK α ((α / r) ^ (1 / (1 - α)) * N) N = r := by
  have hx : 0 < (α / r) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos (div_pos hα0 hr) _
  have hxa : ((α / r) ^ (1 / (1 - α))) ^ (α - 1) = r / α := by
    rw [← Real.rpow_mul (div_pos hα0 hr).le, show 1 / (1 - α) * (α - 1) = -1 by
      field_simp [show 1 - α ≠ 0 by linarith]; ring, Real.rpow_neg_one, inv_div]
  have := (rm_cd_homog α hN hx one_pos).2.1
  rw [show N * (α / r) ^ (1 / (1 - α)) = (α / r) ^ (1 / (1 - α)) * N by ring, mul_one] at this
  rw [this]
  simp only [rmCDK, Real.one_rpow, mul_one, hxa]
  field_simp

end Miao.NeoclassicalGrowth

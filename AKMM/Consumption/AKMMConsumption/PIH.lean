/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.Basics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The permanent income hypothesis

AKMM, §11.3.2, (11.17)–(11.29), fn. 14–15, pp. 297–301, and the PIH part of §11.3.3,
(11.30), p. 302.

Random variables live in a real normed space `V` with Miao's conditional expectations
`E : CondExpSystem ℝ V` (linear, contractive, iterated expectations); Mathlib's conditional
expectations on `L¹(Ω, F, Pr)` given a filtration are an instance (`condExpSystemL1_real`), and so
is the identity (`pih_detSystem`), which is the deterministic case. Processes are `ℕ → V`. The
gross rate is `R = 1 + r` and `q = (1 + r)⁻¹`.

* **(11.18)** quadratic utility `u′(c) = b₁ − b₂c` and `βR = 1` turn the Euler equation into
  Hall's martingale `cₜ = Eₜcₜ₊₁` (`eq_11_18`); **(11.19)** `Eₜcₜ₊ⱼ = cₜ` (`eq_11_19`).
* The budget iterated `J` periods and conditioned on `Eₜ` (`pih_budget_iter`,
  `pih_budget_condexp`); **(11.20)** with (11.10) in expectation, `cₜ = (r/(1 + r))[aₜ +
  Σⱼ qʲEₜyₜ₊ⱼ]` (`eq_11_20`); **(11.21)** the deterministic case (`eq_11_21`) and certainty
  equivalence: (11.20) is (11.21)'s rule `pih_rule` applied to the forecasts
  (`pih_certainty_equivalence`).
* **(11.22)–(11.24)** consumption changes by the annuity value of the news in total wealth
  (`eq_11_22`, `eq_11_23`, `eq_11_24`).
* **(11.25)–(11.27)** permanent and transitory income: (11.26) (`eq_11_26`), the news
  `(Eₜ₊₁ − Eₜ)yₜ₊₁₊ⱼ = vₜ₊₁ + [j = 0]uₜ₊₁` (`pih_news_perm_trans`) and
  `Δcₜ₊₁ = (r/(1 + r))uₜ₊₁ + vₜ₊₁` (`eq_11_27`).
* **(11.29)** saving for a rainy day: `sₜ = yₜ − (r/(1 + r))Σⱼ qʲEₜyₜ₊ⱼ` and
  `sₜ = −Σ_{j≥1} qʲEₜΔyₜ₊ⱼ` (`eq_11_29`, `pih_rainy_day`).
* **§11.3.3** a random walk income gives `cₜ = (r/(1 + r))aₜ + yₜ` and `aₜ₊₁ = aₜ`
  (`pih_random_walk`); i.i.d. income with mean `ȳ` gives **(11.30)** and
  `aₜ₊₁ = aₜ + yₜ − ȳ` (`eq_11_30`).

Departures: the Euler equation behind (11.18) is a hypothesis (the book states it); the
transversality condition (11.10) is used in expectation, `qᴶEₜaₜ₊ᴶ → 0`; the constant `1` of
`V` is a vector `one` with `Eₜ one = one`. Dates are written `t + 1` and `t` instead of `t` and
`t − 1`.
-/

namespace AKMM.Consumption

open Filter Topology Miao.RationalExpectations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The deterministic case: `Eₜ = id` is a system of conditional expectations. -/
def pih_detSystem (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : CondExpSystem ℝ V where
  E := fun _ => ContinuousLinearMap.id ℝ V
  norm_le := fun _ => ContinuousLinearMap.norm_id_le
  tower_le := fun _ _ _ => ContinuousLinearMap.id_comp _
  tower_ge := fun _ _ _ => ContinuousLinearMap.id_comp _

/-- `1 − (1 + r)⁻¹ = r/(1 + r)`. -/
theorem pih_one_sub_q {r : ℝ} (hr : 0 < r) : 1 - (1 + r)⁻¹ = r / (1 + r) := by
  have : (1 + r) ≠ 0 := by linarith
  field_simp
  ring

/-- `(r/(1 + r))(1 − (1 + r)⁻¹)⁻¹ = 1`: the annuity factor inverts the geometric sum. -/
theorem pih_annuity_inv {r : ℝ} (hr : 0 < r) : r / (1 + r) * (1 - (1 + r)⁻¹)⁻¹ = 1 := by
  rw [pih_one_sub_q hr, mul_inv_cancel₀ (div_pos hr (by linarith)).ne']

/-! ### Hall's martingale -/

/-- **AKMM, (11.18), p. 298 (Hall 1978).** With quadratic utility, `u′(c) = b₁ − b₂c` (`b₂ ≠ 0`),
and `βR = 1`, the Euler equation `u′(cₜ) = βREₜu′(cₜ₊₁)` gives `cₜ = Eₜcₜ₊₁`: consumption is a
martingale. -/
theorem eq_11_18 (E : CondExpSystem ℝ V) {β R b₁ b₂ : ℝ} (hb₂ : b₂ ≠ 0) (hβR : β * R = 1)
    {one : V} (hone : ∀ t, E.E t one = one) {c : ℕ → V}
    (heuler : ∀ t, b₁ • one - b₂ • c t = (β * R) • E.E t (b₁ • one - b₂ • c (t + 1))) (t : ℕ) :
    c t = E.E t (c (t + 1)) := by
  have h := heuler t
  rw [hβR, one_smul, map_sub, map_smul, map_smul, hone] at h
  have h2 : b₂ • c t = b₂ • E.E t (c (t + 1)) := by
    have := congrArg (fun x => b₁ • one - x) h
    simpa using this
  exact smul_right_injective V hb₂ h2

/-- **AKMM, (11.19), p. 298.** From the martingale property and the law of iterated expectations,
`Eₜcₜ₊ⱼ = cₜ` for every `j ≥ 0`. -/
theorem eq_11_19 (E : CondExpSystem ℝ V) {c : ℕ → V} (hmart : ∀ t, c t = E.E t (c (t + 1)))
    (t j : ℕ) : E.E t (c (t + j)) = c t := by
  induction j with
  | zero =>
    rw [add_zero]
    conv_lhs => rw [hmart t]
    rw [E.idem, ← hmart t]
  | succ j ih =>
    rw [← add_assoc, ← E.tower_le_apply (Nat.le_add_right t j) (c (t + j + 1)), ← hmart (t + j), ih]

/-! ### The annuity rule (11.20) -/

/-- AKMM, p. 298: the budget `aₜ₊₁ = R(yₜ + aₜ − cₜ)` iterated `J` periods, in `V`. -/
theorem pih_budget_iter {R : ℝ} (hR : R ≠ 0) {y c a : ℕ → V}
    (hb : ∀ t, a (t + 1) = R • (y t + a t - c t)) (t J : ℕ) :
    ∑ j ∈ Finset.range J, R⁻¹ ^ j • c (t + j) =
      a t + ∑ j ∈ Finset.range J, R⁻¹ ^ j • y (t + j) - R⁻¹ ^ J • a (t + J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, show t + (J + 1) = t + J + 1 by ring,
      hb (t + J), smul_smul, pow_succ, mul_assoc, inv_mul_cancel₀ hR, mul_one]
    simp only [smul_sub, smul_add]
    abel

/-- AKMM, p. 298: the iterated budget conditioned on `Eₜ`,
`Σ_{j≤J} R⁻ʲEₜcₜ₊ⱼ = aₜ + Σ_{j≤J} R⁻ʲEₜyₜ₊ⱼ − R^{−(J+1)}Eₜaₜ₊ⱼ₊₁` (`aₜ` known at `t`). -/
theorem pih_budget_condexp (E : CondExpSystem ℝ V) {R : ℝ} (hR : R ≠ 0) {y c a : ℕ → V}
    (hb : ∀ t, a (t + 1) = R • (y t + a t - c t)) (t : ℕ) (ha : E.E t (a t) = a t) (J : ℕ) :
    ∑ j ∈ Finset.range J, R⁻¹ ^ j • E.E t (c (t + j)) =
      a t + ∑ j ∈ Finset.range J, R⁻¹ ^ j • E.E t (y (t + j)) -
        R⁻¹ ^ J • E.E t (a (t + J)) := by
  have h := congrArg (E.E t) (pih_budget_iter hR hb t J)
  simp only [map_sub, map_add, map_sum, map_smul, ha] at h
  exact h

/-- The rule of (11.20)–(11.21): `(r/(1 + r))[a + Σⱼ (1 + r)⁻ʲzⱼ]` applied to forecasts `z`. -/
noncomputable def pih_rule (r : ℝ) (a : V) (z : ℕ → V) : V :=
  (r / (1 + r)) • (a + ∑' j, ((1 + r)⁻¹) ^ j • z j)

/-- **AKMM, (11.20), p. 298: the stochastic permanent income hypothesis.** With `r > 0`, the
martingale property (11.18), the budget, `aₜ` known at `t`, a convergent present value of
expected income and (11.10) in expectation (`(1 + r)^{−J}Eₜaₜ₊ᴶ → 0`):
`cₜ = (r/(1 + r))[aₜ + Σⱼ (1 + r)⁻ʲEₜyₜ₊ⱼ]`, the annuity value of total wealth. -/
theorem eq_11_20 (E : CondExpSystem ℝ V) {r : ℝ} (hr : 0 < r) {y c a : ℕ → V}
    (hmart : ∀ t, c t = E.E t (c (t + 1))) (hb : ∀ t, a (t + 1) = (1 + r) • (y t + a t - c t))
    (t : ℕ) (ha : E.E t (a t) = a t)
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j • E.E t (y (t + j)))
    (htvc : Tendsto (fun J => ((1 + r)⁻¹) ^ J • E.E t (a (t + J))) atTop (𝓝 0)) :
    c t = pih_rule r (a t) fun j => E.E t (y (t + j)) := by
  set q := (1 + r)⁻¹ with hq
  have hq0 : 0 ≤ q := inv_nonneg.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hiter := pih_budget_condexp E (show (1 + r) ≠ 0 by linarith) hb t ha
  simp_rw [eq_11_19 E hmart t, ← Finset.sum_smul] at hiter
  have hL : Tendsto (fun J => (∑ j ∈ Finset.range J, q ^ j) • c t) atTop
      (𝓝 ((1 - q)⁻¹ • c t)) :=
    (hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat.smul_const _
  have hR : Tendsto (fun J => a t + ∑ j ∈ Finset.range J, q ^ j • E.E t (y (t + j)) -
      q ^ J • E.E t (a (t + J))) atTop (𝓝 (a t + ∑' j, q ^ j • E.E t (y (t + j)) - 0)) :=
    (tendsto_const_nhds.add hy.hasSum.tendsto_sum_nat).sub htvc
  have heq : (1 - q)⁻¹ • c t = a t + ∑' j, q ^ j • E.E t (y (t + j)) := by
    rw [← sub_zero (a t + _)]
    exact tendsto_nhds_unique (hL.congr fun J => hiter J) hR
  have h1q : 1 - q = r / (1 + r) := by rw [hq]; field_simp; ring
  have hne : (1 - q) ≠ 0 := by linarith
  unfold pih_rule
  rw [← hq, ← heq, smul_smul, ← h1q, mul_inv_cancel₀ hne, one_smul]

/-- **AKMM, (11.21), p. 298.** Deterministic income (`Eₜ = id`), quadratic utility and
`βR = 1`: the Euler equation gives `cₜ₊₁ = cₜ` and
`cₜ = (r/(1 + r))[aₜ + Σⱼ (1 + r)⁻ʲyₜ₊ⱼ]`. -/
theorem eq_11_21 {r : ℝ} (hr : 0 < r) {y c a : ℕ → ℝ} (hconst : ∀ t, c (t + 1) = c t)
    (hb : ∀ t, a (t + 1) = (1 + r) * (y t + a t - c t)) (t : ℕ)
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j * y (t + j))
    (htvc : Tendsto (fun J => ((1 + r)⁻¹) ^ J * a (t + J)) atTop (𝓝 0)) :
    c t = r / (1 + r) * (a t + ∑' j, ((1 + r)⁻¹) ^ j * y (t + j)) := by
  have := eq_11_20 (pih_detSystem ℝ) hr (y := y) (c := c) (a := a)
    (fun s => (hconst s).symm) (fun s => by rw [hb s, smul_eq_mul]) t rfl
    (by simpa [pih_detSystem] using hy) (by simpa [pih_detSystem] using htvc)
  simpa [pih_rule, pih_detSystem] using this

/-- **AKMM, p. 298: certainty equivalence.** The stochastic rule (11.20) is the deterministic
rule (11.21) with the conditional expectations `Eₜyₜ₊ⱼ` in place of the incomes: the two
solutions are `pih_rule` applied to the realised and to the forecast income paths. -/
theorem pih_certainty_equivalence (E : CondExpSystem ℝ V) {r : ℝ} (hr : 0 < r) {y c a : ℕ → V}
    (hmart : ∀ t, c t = E.E t (c (t + 1))) (hb : ∀ t, a (t + 1) = (1 + r) • (y t + a t - c t))
    (t : ℕ) (ha : E.E t (a t) = a t)
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j • E.E t (y (t + j)))
    (htvc : Tendsto (fun J => ((1 + r)⁻¹) ^ J • E.E t (a (t + J))) atTop (𝓝 0))
    {yd cd ad : ℕ → V} (hconst : ∀ s, cd (s + 1) = cd s)
    (hbd : ∀ s, ad (s + 1) = (1 + r) • (yd s + ad s - cd s))
    (hyd : Summable fun j => ((1 + r)⁻¹) ^ j • yd (t + j))
    (htvcd : Tendsto (fun J => ((1 + r)⁻¹) ^ J • ad (t + J)) atTop (𝓝 0)) :
    c t = pih_rule r (a t) (fun j => E.E t (y (t + j))) ∧
      cd t = pih_rule r (ad t) (fun j => yd (t + j)) :=
  ⟨eq_11_20 E hr hmart hb t ha hy htvc,
    eq_11_20 (pih_detSystem V) hr (fun s => (hconst s).symm) hbd t rfl hyd htvcd⟩

/-! ### News: (11.22)–(11.24) -/

/-- Total wealth `ϖₜ = aₜ + Σⱼ (1 + r)⁻ʲEₜyₜ₊ⱼ`. -/
noncomputable def pih_wealth (E : CondExpSystem ℝ V) (r : ℝ) (y a : ℕ → V) (t : ℕ) : V :=
  a t + ∑' j, ((1 + r)⁻¹) ^ j • E.E t (y (t + j))

/-- **AKMM, (11.22), p. 299.** If (11.20) holds at `t + 1` and consumption is a martingale,
`Δcₜ₊₁ = cₜ₊₁ − Eₜcₜ₊₁ = (r/(1 + r))[ϖₜ₊₁ − Eₜϖₜ₊₁]`. -/
theorem eq_11_22 (E : CondExpSystem ℝ V) {r : ℝ} {y c a : ℕ → V}
    (hmart : ∀ t, c t = E.E t (c (t + 1))) (t : ℕ)
    (h20 : c (t + 1) = (r / (1 + r)) • pih_wealth E r y a (t + 1)) :
    c (t + 1) - c t = c (t + 1) - E.E t (c (t + 1)) ∧
      c (t + 1) - c t = (r / (1 + r)) • (pih_wealth E r y a (t + 1) -
        E.E t (pih_wealth E r y a (t + 1))) := by
  refine ⟨by rw [← hmart t], ?_⟩
  rw [hmart t, h20, map_smul, smul_sub]

/-- **AKMM, (11.23), p. 299.** If `aₜ₊₁` is known at `t` (`Eₜaₜ₊₁ = aₜ₊₁`) and the present value
of expected income at `t + 1` converges, the innovation in total wealth is the discounted sum of
the revisions in expected income: `ϖₜ₊₁ − Eₜϖₜ₊₁ = Σⱼ (1 + r)⁻ʲ(Eₜ₊₁ − Eₜ)yₜ₊₁₊ⱼ`. -/
theorem eq_11_23 (E : CondExpSystem ℝ V) {r : ℝ} {y a : ℕ → V} (t : ℕ)
    (ha : E.E t (a (t + 1)) = a (t + 1))
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j • E.E (t + 1) (y (t + 1 + j))) :
    pih_wealth E r y a (t + 1) - E.E t (pih_wealth E r y a (t + 1)) =
      ∑' j, ((1 + r)⁻¹) ^ j • (E.E (t + 1) (y (t + 1 + j)) - E.E t (y (t + 1 + j))) := by
  have hmap : E.E t (∑' j, ((1 + r)⁻¹) ^ j • E.E (t + 1) (y (t + 1 + j))) =
      ∑' j, ((1 + r)⁻¹) ^ j • E.E t (y (t + 1 + j)) := by
    rw [(E.E t).map_tsum hy]
    simp only [map_smul, E.tower_le_apply (Nat.le_succ t)]
  have hy' : Summable fun j => ((1 + r)⁻¹) ^ j • E.E t (y (t + 1 + j)) := by
    have := (E.E t).summable hy
    simpa only [Function.comp_def, map_smul, E.tower_le_apply (Nat.le_succ t)] using this
  unfold pih_wealth
  rw [map_add, ha, hmap]
  simp_rw [smul_sub]
  rw [hy.tsum_sub hy']
  abel

/-- **AKMM, (11.24), p. 299.** Combining (11.22) and (11.23): under the PIH the change in
consumption is the annuity value of the news,
`Δcₜ₊₁ = (r/(1 + r))Σⱼ (1 + r)⁻ʲ(Eₜ₊₁ − Eₜ)yₜ₊₁₊ⱼ`. -/
theorem eq_11_24 (E : CondExpSystem ℝ V) {r : ℝ} {y c a : ℕ → V}
    (hmart : ∀ t, c t = E.E t (c (t + 1))) (t : ℕ)
    (h20 : c (t + 1) = (r / (1 + r)) • pih_wealth E r y a (t + 1))
    (ha : E.E t (a (t + 1)) = a (t + 1))
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j • E.E (t + 1) (y (t + 1 + j))) :
    c (t + 1) - c t = (r / (1 + r)) •
      ∑' j, ((1 + r)⁻¹) ^ j • (E.E (t + 1) (y (t + 1 + j)) - E.E t (y (t + 1 + j))) := by
  rw [(eq_11_22 E hmart t h20).2, eq_11_23 E t ha hy]

/-! ### Permanent and transitory shocks: (11.25)–(11.27) -/

omit [NormedSpace ℝ V] in
/-- **AKMM, (11.26), p. 299.** From (11.25), `yₜ₊₁ = yₜ + uₜ₊₁ − uₜ + vₜ₊₁`. -/
theorem eq_11_26 {y yp u v : ℕ → V} (hy : ∀ t, y t = yp t + u t)
    (hyp : ∀ t, yp (t + 1) = yp t + v (t + 1)) (t : ℕ) :
    y (t + 1) = y t + u (t + 1) - u t + v (t + 1) := by
  rw [hy, hy, hyp]; abel

/-- AKMM, p. 299: the permanent component is a martingale, `Eₛypₛ₊ₖ = ypₛ`, when `ypₛ` is known
at `s` and future permanent shocks have conditional mean zero. -/
theorem pih_perm_martingale (E : CondExpSystem ℝ V) {yp v : ℕ → V}
    (hyp : ∀ t, yp (t + 1) = yp t + v (t + 1)) (hypm : ∀ s, E.E s (yp s) = yp s)
    (hv : ∀ s τ, s < τ → E.E s (v τ) = 0) (s k : ℕ) : E.E s (yp (s + k)) = yp s := by
  induction k with
  | zero => simpa using hypm s
  | succ k ih => rw [← add_assoc, hyp, map_add, ih, hv s _ (by omega), add_zero]

/-- AKMM, p. 300 ("after some algebra"): under (11.25), with `Eₛxτ = xτ` for `τ ≤ s` and
`Eₛxτ = 0` for `τ > s` (`x = u, v`) and `ypₛ` known at `s`, the revision in expected income is
`(Eₜ₊₁ − Eₜ)yₜ₊₁₊ⱼ = vₜ₊₁ + [j = 0]uₜ₊₁`. -/
theorem pih_news_perm_trans (E : CondExpSystem ℝ V) {y yp u v : ℕ → V}
    (hy : ∀ t, y t = yp t + u t) (hyp : ∀ t, yp (t + 1) = yp t + v (t + 1))
    (hypm : ∀ s, E.E s (yp s) = yp s) (hu0 : ∀ s, E.E s (u s) = u s)
    (hu : ∀ s τ, s < τ → E.E s (u τ) = 0) (hv : ∀ s τ, s < τ → E.E s (v τ) = 0) (t j : ℕ) :
    E.E (t + 1) (y (t + 1 + j)) = yp (t + 1) + (if j = 0 then u (t + 1) else 0) ∧
      E.E t (y (t + 1 + j)) = yp t ∧
      E.E (t + 1) (y (t + 1 + j)) - E.E t (y (t + 1 + j)) =
        v (t + 1) + (if j = 0 then u (t + 1) else 0) := by
  have h1 : E.E (t + 1) (y (t + 1 + j)) = yp (t + 1) + (if j = 0 then u (t + 1) else 0) := by
    rw [hy, map_add, pih_perm_martingale E hyp hypm hv]
    split_ifs with hj
    · subst hj; rw [add_zero, hu0]
    · rw [hu _ _ (by omega)]
  have h2 : E.E t (y (t + 1 + j)) = yp t := by
    rw [hy, map_add, show t + 1 + j = t + (1 + j) by ring, pih_perm_martingale E hyp hypm hv,
      hu _ _ (by omega), add_zero]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2, hyp]
  abel

/-- **AKMM, (11.27), p. 300.** Under the PIH ((11.20) at `t + 1`, `aₜ₊₁` known at `t`, `r > 0`)
and the income process (11.25), `Δcₜ₊₁ = (r/(1 + r))uₜ₊₁ + vₜ₊₁`: the annuity value of the
transitory shock and the full permanent shock. -/
theorem eq_11_27 (E : CondExpSystem ℝ V) {r : ℝ} (hr : 0 < r) {y yp u v c a : ℕ → V}
    (hy : ∀ t, y t = yp t + u t) (hyp : ∀ t, yp (t + 1) = yp t + v (t + 1))
    (hypm : ∀ s, E.E s (yp s) = yp s) (hu0 : ∀ s, E.E s (u s) = u s)
    (hu : ∀ s τ, s < τ → E.E s (u τ) = 0) (hv : ∀ s τ, s < τ → E.E s (v τ) = 0)
    (hmart : ∀ t, c t = E.E t (c (t + 1))) (t : ℕ)
    (h20 : c (t + 1) = (r / (1 + r)) • pih_wealth E r y a (t + 1))
    (ha : E.E t (a (t + 1)) = a (t + 1)) :
    c (t + 1) - c t = (r / (1 + r)) • u (t + 1) + v (t + 1) := by
  set q := (1 + r)⁻¹ with hq
  have hq0 : 0 ≤ q := inv_nonneg.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hg := summable_geometric_of_lt_one hq0 hq1
  have hnews := pih_news_perm_trans E hy hyp hypm hu0 hu hv t
  have hδ : Summable fun j : ℕ => q ^ j • (if j = 0 then u (t + 1) else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [Finset.mem_singleton] at hj; simp [hj]
  have hsy : Summable fun j => q ^ j • E.E (t + 1) (y (t + 1 + j)) := by
    simp_rw [(hnews _).1, smul_add]
    exact (hg.smul_const _).add hδ
  rw [eq_11_24 E hmart t h20 ha hsy]
  simp_rw [(hnews _).2.2, smul_add]
  rw [(hg.smul_const _).tsum_add hδ, hg.tsum_smul_const _, tsum_geometric_of_lt_one hq0 hq1,
    tsum_eq_single (f := fun j : ℕ => q ^ j • (if j = 0 then u (t + 1) else 0)) 0
      (fun j hj => by simp [hj])]
  simp only [pow_zero, ↓reduceIte, one_smul, smul_add, smul_smul]
  rw [hq, pih_annuity_inv hr, one_smul]
  abel

/-! ### Saving for a rainy day (11.29) -/

/-- **AKMM, (11.29), p. 301.** Saving `sₜ = (r/(1 + r))aₜ + yₜ − cₜ`, with consumption from
(11.20), is `yₜ − (r/(1 + r))Σⱼ (1 + r)⁻ʲEₜyₜ₊ⱼ`. -/
theorem eq_11_29 (E : CondExpSystem ℝ V) {r : ℝ} {y c a : ℕ → V} (t : ℕ)
    (h20 : c t = pih_rule r (a t) fun j => E.E t (y (t + j))) :
    (r / (1 + r)) • a t + y t - c t =
      y t - (r / (1 + r)) • ∑' j, ((1 + r)⁻¹) ^ j • E.E t (y (t + j)) := by
  rw [h20, pih_rule, smul_add]
  abel

/-- **AKMM, p. 301: saving for the rainy day (Campbell 1987).** With (11.20), `yₜ` known at `t`
and a convergent present value of expected income, `r > 0`:
`sₜ = −Σ_{j≥1} (1 + r)⁻ʲEₜΔyₜ₊ⱼ`, the discounted sum of expected declines in income. -/
theorem pih_rainy_day (E : CondExpSystem ℝ V) {r : ℝ} (hr : 0 < r) {y c a : ℕ → V} (t : ℕ)
    (h20 : c t = pih_rule r (a t) fun j => E.E t (y (t + j))) (hyt : E.E t (y t) = y t)
    (hy : Summable fun j => ((1 + r)⁻¹) ^ j • E.E t (y (t + j))) :
    (r / (1 + r)) • a t + y t - c t =
      -∑' j, ((1 + r)⁻¹) ^ (j + 1) • (E.E t (y (t + (j + 1))) - E.E t (y (t + j))) := by
  rw [eq_11_29 E t h20]
  set q := (1 + r)⁻¹ with hq
  set Y : ℕ → V := fun j => E.E t (y (t + j)) with hY
  have hs1 : Summable fun j => q ^ (j + 1) • Y (j + 1) := (summable_nat_add_iff 1).2 hy
  have hs2 : Summable fun j => q ^ (j + 1) • Y j := by
    simp_rw [pow_succ, mul_comm _ q, ← smul_smul]; exact hy.const_smul q
  have h0 : ∑' j, q ^ j • Y j = q ^ 0 • Y 0 + ∑' j, q ^ (j + 1) • Y (j + 1) :=
    hy.tsum_eq_zero_add
  have h2 : ∑' j, q ^ (j + 1) • Y j = q • ∑' j, q ^ j • Y j := by
    rw [← hy.tsum_const_smul q]
    simp_rw [smul_smul, ← pow_succ']
    rfl
  have hsplit : ∑' j, q ^ (j + 1) • (Y (j + 1) - Y j) =
      (∑' j, q ^ j • Y j - Y 0) - q • ∑' j, q ^ j • Y j := by
    simp_rw [smul_sub]
    rw [hs1.tsum_sub hs2, h2, h0, pow_zero, one_smul]
    abel
  change y t - (r / (1 + r)) • ∑' j, q ^ j • Y j = -∑' j, q ^ (j + 1) • (Y (j + 1) - Y j)
  rw [hsplit]
  have hY0 : Y 0 = y t := by simp [hY, hyt]
  have h1q : r / (1 + r) = 1 - q := by rw [hq]; field_simp; ring
  rw [hY0, h1q, sub_smul, one_smul]
  abel

/-! ### Borrowing constraints in the PIH: random walk and i.i.d. income -/

/-- **AKMM, p. 302: random-walk income.** If `Eₜyₜ₊ⱼ = yₜ` for all `j`, (11.20) gives
`cₜ = (r/(1 + r))aₜ + yₜ`, and the budget gives `aₜ₊₁ = aₜ`: wealth is constant, so the zero
debt limit never binds from positive wealth. -/
theorem pih_random_walk (E : CondExpSystem ℝ V) {r : ℝ} (hr : 0 < r) {y c a : ℕ → V} (t : ℕ)
    (hrw : ∀ j, E.E t (y (t + j)) = y t)
    (h20 : c t = pih_rule r (a t) fun j => E.E t (y (t + j)))
    (hb : a (t + 1) = (1 + r) • (y t + a t - c t)) :
    c t = (r / (1 + r)) • a t + y t ∧ a (t + 1) = a t := by
  have hq0 : 0 ≤ (1 + r)⁻¹ := inv_nonneg.2 (by linarith)
  have hq1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hc : c t = (r / (1 + r)) • a t + y t := by
    rw [h20, pih_rule]
    simp_rw [hrw]
    rw [((summable_geometric_of_lt_one hq0 hq1)).tsum_smul_const _,
      tsum_geometric_of_lt_one hq0 hq1, smul_add, smul_smul]
    rw [pih_annuity_inv hr, one_smul]
  refine ⟨hc, ?_⟩
  rw [hb, hc]
  have hr1 : (1 + r) ≠ 0 := by linarith
  simp only [smul_sub, smul_add, smul_smul]
  rw [show (1 + r) * (r / (1 + r)) = r by field_simp]
  module

/-- **AKMM, (11.30), p. 302: i.i.d. income.** If `yₜ` is known at `t` and `Eₜyₜ₊ⱼ = ȳ` for
`j ≥ 1` (a constant `ȳ · one`), (11.20) gives `cₜ = ȳ/(1 + r) + (r/(1 + r))(aₜ + yₜ)`, and the
budget gives `aₜ₊₁ = aₜ + yₜ − ȳ`: wealth is a random walk without drift. -/
theorem eq_11_30 (E : CondExpSystem ℝ V) {r ybar : ℝ} (hr : 0 < r) {one : V} {y c a : ℕ → V}
    (t : ℕ) (hyt : E.E t (y t) = y t) (hiid : ∀ j, E.E t (y (t + (j + 1))) = ybar • one)
    (h20 : c t = pih_rule r (a t) fun j => E.E t (y (t + j)))
    (hb : a (t + 1) = (1 + r) • (y t + a t - c t)) :
    c t = (ybar / (1 + r)) • one + (r / (1 + r)) • (a t + y t) ∧
      a (t + 1) = a t + y t - ybar • one := by
  set q := (1 + r)⁻¹ with hq
  have hq0 : 0 ≤ q := inv_nonneg.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hg := summable_geometric_of_lt_one hq0 hq1
  have hsum : ∑' j, q ^ j • E.E t (y (t + j)) = y t + (q * (1 - q)⁻¹ * ybar) • one := by
    have hs : Summable fun j => q ^ j • E.E t (y (t + j)) := by
      rw [← summable_nat_add_iff 1]
      simp_rw [hiid]
      exact (hg.comp_injective (add_left_injective 1)).smul_const _
    rw [hs.tsum_eq_zero_add]
    simp_rw [hiid]
    rw [(((summable_nat_add_iff 1).2 hg)).tsum_smul_const _]
    simp only [pow_zero, one_smul, add_zero, hyt]
    congr 1
    rw [smul_smul]
    congr 1
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have hc : c t = (ybar / (1 + r)) • one + (r / (1 + r)) • (a t + y t) := by
    rw [h20, pih_rule, hsum, smul_add, smul_add, smul_smul]
    have : r / (1 + r) * (q * (1 - q)⁻¹ * ybar) = ybar / (1 + r) := by
      rw [mul_comm q, ← mul_assoc, ← mul_assoc, pih_annuity_inv hr, one_mul, hq]
      field_simp
    rw [this]
    module
  refine ⟨hc, ?_⟩
  rw [hb, hc]
  simp only [smul_sub, smul_add, smul_smul]
  rw [show (1 + r) * (ybar / (1 + r)) = ybar by field_simp,
    show (1 + r) * (r / (1 + r)) = r by field_simp]
  module

end AKMM.Consumption

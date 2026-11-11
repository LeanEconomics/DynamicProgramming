/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Credible government policies: the one-period economy

Miao, §21.4.1, pp. 758–761 (after Stokey 1991 and Ljungqvist–Sargent 2004, Ch. 22).

* `cg_CE u`: competitive equilibria `(x, y)` with `u(x, x, y) = max_a u(a, x, y)`; `cg_IsRamsey`
  (a Ramsey plan maximises `r(x, y) = u(x, x, y)` over competitive equilibria) and `cg_IsNash`
  (competitive, with `y` a best response to `x`). The repeated-economy modules take the set `C`
  of competitive equilibria as a primitive, so that the examples can give it by a table.
* `cg_vN_le_vR`: `v^N ≤ v^R` (p. 759).
* Example 21.4.1 (Barro–Gordon): the household forecast, the Ramsey outcome `π = 0`, the unique
  Nash outcome `π = aλ`, `y = y_n` in both, and the time inconsistency of the Ramsey outcome.
* Example 21.4.2 (Stokey's discrete monetary policy): `(x_L, y_L)` is the Ramsey outcome,
  `(x_M, y_M)` the unique Nash outcome, and the Ramsey outcome is not time consistent. The
  actions are `Fin 3` with `0, 1, 2 = H, M, L`; `cg_r422 x y = r(x, y)`.
* Exercise 21.6 (a)–(b): `Fin 2` with `0, 1 = L, H`; the Ramsey plan is `(x_H, y_H)` and there is
  no pure-strategy Nash equilibrium. Parts (c)–(f) are in `CGExamples`.
-/

namespace Miao.DynamicGames

variable {X Y : Type*}

/-- Competitive equilibria of the one-period economy (Miao, p. 758): given `(x, y)`, the
representative household's choice `a = x` solves `max_a u(a, x, y)`. -/
def cg_CE (u : X → X → Y → ℝ) : Set (X × Y) := {q | ∀ a, u a q.1 q.2 ≤ u q.1 q.1 q.2}

/-- Miao, p. 758: `(x, y) ∈ C` iff `u(x, x, y) = max_{a ∈ X} u(a, x, y)`. -/
theorem cg_mem_CE (u : X → X → Y → ℝ) (x : X) (y : Y) :
    (x, y) ∈ cg_CE u ↔ ∀ a, u a x y ≤ u x x y := Iff.rfl

/-- A Ramsey plan (Miao, p. 759): `(x^R, y^R)` maximises `r` over competitive equilibria. -/
def cg_IsRamsey (C : Set (X × Y)) (r : X → Y → ℝ) (x : X) (y : Y) : Prop :=
  (x, y) ∈ C ∧ ∀ q ∈ C, r q.1 q.2 ≤ r x y

/-- A Nash equilibrium (Miao, p. 759): `(x^N, y^N) ∈ C` and `y^N` maximises `r(x^N, ·)`. -/
def cg_IsNash (C : Set (X × Y)) (r : X → Y → ℝ) (x : X) (y : Y) : Prop :=
  (x, y) ∈ C ∧ ∀ y', r x y' ≤ r x y

/-- Miao, p. 759: `v^N ≤ max_{(x, y) ∈ C, y = H(x)} r(x, y) ≤ max_{(x, y) ∈ C} r(x, y) = v^R`. -/
theorem cg_vN_le_vR {C : Set (X × Y)} {r : X → Y → ℝ} {xN xR : X} {yN yR : Y}
    (hN : cg_IsNash C r xN yN) (hR : cg_IsRamsey C r xR yR) : r xN yN ≤ r xR yR :=
  hR.2 (xN, yN) hN.1

/-- The government's objective in Example 21.4.1, `λ(y − y_n) − π²/2` with the Phillips curve
`y = y_n + a(π − π^e)`, as a function of the forecast `π^e` and the inflation rate `π`. -/
noncomputable def cg_bgGov (lam a yn infe infl : ℝ) : ℝ :=
  lam * ((yn + a * (infl - infe)) - yn) - infl ^ 2 / 2

/-- The household's payoff `−(π − ξ)²` from the forecast `ξ` in Example 21.4.1. -/
noncomputable def cg_bgHH (infl ξ : ℝ) : ℝ := -(infl - ξ) ^ 2

/-- The competitive equilibria `ξ = π^e = π` of Example 21.4.1. -/
def cg_bgC : Set (ℝ × ℝ) := {q | q.1 = q.2}

/-- **Example 21.4.1** (Barro–Gordon, Miao, pp. 759–760), the household: `ξ = π` uniquely
maximises `−(π − ξ)²`, so the competitive equilibria are `π^e = π`. -/
theorem example_21_4_1_household (infl ξ : ℝ) :
    cg_bgHH infl ξ ≤ cg_bgHH infl infl ∧ (cg_bgHH infl ξ = cg_bgHH infl infl → ξ = infl) := by
  unfold cg_bgHH
  refine ⟨by nlinarith [sq_nonneg (infl - ξ)], fun h => ?_⟩
  have : (infl - ξ) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith

/-- **Example 21.4.1** (Miao, p. 760), the Ramsey plan: with `π^e = π` the government's best
choice is `π = π^e = 0`, with `y = y_n`. -/
theorem example_21_4_1_ramsey (lam a yn : ℝ) :
    cg_IsRamsey cg_bgC (cg_bgGov lam a yn) 0 0 ∧
      (∀ x y, cg_IsRamsey cg_bgC (cg_bgGov lam a yn) x y → x = 0 ∧ y = 0) ∧
      yn + a * (0 - 0) = yn := by
  refine ⟨⟨rfl, ?_⟩, fun x y h => ?_, by ring⟩
  · rintro ⟨x, y⟩ (hq : x = y)
    subst hq
    simp only [cg_bgGov]
    nlinarith [sq_nonneg x]
  · obtain ⟨hxy, hmax⟩ := h
    have hxy' : x = y := hxy
    subst hxy'
    have := hmax (0, 0) rfl
    simp only [cg_bgGov] at this
    have h2 : x ^ 2 = 0 := by nlinarith [sq_nonneg x]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
    exact ⟨this, this⟩

/-- **Example 21.4.1** (Miao, p. 760), the Nash equilibrium: taking `π^e` as given the
government sets `π = aλ`, so the unique Nash outcome is `π^e = π = aλ`, with `y = y_n`. -/
theorem example_21_4_1_nash {lam a : ℝ} (yn : ℝ) :
    (∀ infe infl, cg_bgGov lam a yn infe infl ≤ cg_bgGov lam a yn infe (a * lam)) ∧
      cg_IsNash cg_bgC (cg_bgGov lam a yn) (a * lam) (a * lam) ∧
      (∀ x y, cg_IsNash cg_bgC (cg_bgGov lam a yn) x y → x = a * lam ∧ y = a * lam) ∧
      yn + a * (a * lam - a * lam) = yn := by
  have hbr : ∀ infe infl, cg_bgGov lam a yn infe infl ≤ cg_bgGov lam a yn infe (a * lam) := by
    intro infe infl
    simp only [cg_bgGov]
    nlinarith [sq_nonneg (infl - a * lam)]
  refine ⟨hbr, ⟨rfl, hbr _⟩, fun x y h => ?_, by ring⟩
  obtain ⟨hxy, hmax⟩ := h
  have hxy' : x = y := hxy
  subst hxy'
  have := hmax (a * lam)
  simp only [cg_bgGov] at this
  have h2 : (x - a * lam) ^ 2 = 0 := by nlinarith [sq_nonneg (x - a * lam)]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  exact ⟨by linarith, by linarith⟩

/-- **Example 21.4.1** (Miao, p. 760): the Ramsey outcome is not time consistent. After the
forecast `π^e = 0` the government gains by setting `π = aλ > 0`; and `v^N < v^R`. -/
theorem example_21_4_1_time_inconsistent {lam a : ℝ} (hl : 0 < lam) (ha : 0 < a) (yn : ℝ) :
    0 < a * lam ∧ cg_bgGov lam a yn 0 0 < cg_bgGov lam a yn 0 (a * lam) ∧
      cg_bgGov lam a yn (a * lam) (a * lam) < cg_bgGov lam a yn 0 0 := by
  have h := mul_pos ha hl
  refine ⟨h, ?_, ?_⟩ <;> simp only [cg_bgGov] <;> nlinarith

/-- The government's payoffs `r(x_i, y_j)` of Example 21.4.2 (Miao, p. 760), with
`0, 1, 2 = H, M, L`: rows are `x`, columns `y`. -/
noncomputable def cg_r422 (x y : Fin 3) : ℝ :=
  if x = 0 then (if y = 0 then 0 else if y = 1 then 7 else -1)
  else if x = 1 then (if y = 1 then 8 else -1)
  else (if y = 0 then 1 else if y = 1 then 30 else 97 / 10)

/-- The competitive equilibria `(x_H, y_H), (x_M, y_M), (x_L, y_L)` of Example 21.4.2. -/
def cg_C422 : Set (Fin 3 × Fin 3) := {q | q.1 = q.2}

/-- **Example 21.4.2** (Stokey 1991; Miao, pp. 760–761). `(x_L, y_L)` is the (unique) Ramsey
outcome, `(x_M, y_M)` the unique Nash outcome, and the Ramsey outcome is not time consistent:
given `x_L` the government gains by deviating to `y_M` (`30 > 9.7`). -/
theorem example_21_4_2 :
    cg_IsRamsey cg_C422 cg_r422 2 2 ∧
      (∀ x y, cg_IsRamsey cg_C422 cg_r422 x y → x = 2 ∧ y = 2) ∧
      cg_IsNash cg_C422 cg_r422 1 1 ∧
      (∀ x y, cg_IsNash cg_C422 cg_r422 x y → x = 1 ∧ y = 1) ∧
      cg_r422 2 2 < cg_r422 2 1 := by
  refine ⟨⟨rfl, ?_⟩, fun x y h => ?_, ⟨rfl, fun y' => ?_⟩, fun x y h => ?_, ?_⟩
  · rintro ⟨x, y⟩ (hq : x = y)
    subst hq
    fin_cases x <;> norm_num [cg_r422]
  · obtain ⟨hxy, hmax⟩ := h
    have hxy' : x = y := hxy
    subst hxy'
    have := hmax (2, 2) rfl
    fin_cases x
    · norm_num [cg_r422] at this
    · norm_num [cg_r422] at this
    · exact ⟨rfl, rfl⟩
  · fin_cases y' <;> norm_num [cg_r422]
  · obtain ⟨hxy, hmax⟩ := h
    have hxy' : x = y := hxy
    subst hxy'
    fin_cases x
    · have := hmax 1; norm_num [cg_r422] at this
    · exact ⟨rfl, rfl⟩
    · have := hmax 1; norm_num [cg_r422] at this
  · norm_num [cg_r422]

/-- The government's payoffs `u(x_i, x_i, y_j)` of Exercise 21.6 (Miao, p. 771), with
`0, 1 = L, H`: rows are `x`, columns `y`. -/
noncomputable def cg_r216 (x y : Fin 2) : ℝ :=
  if x = 0 then (if y = 0 then 0 else 1) else (if y = 0 then 15 else 10)

/-- The competitive equilibria `(x_L, y_L), (x_H, y_H)` of Exercise 21.6. -/
def cg_C216 : Set (Fin 2 × Fin 2) := {q | q.1 = q.2}

/-- **Exercise 21.6 (a)** (Miao, p. 771): the Ramsey plan is `(x_H, y_H)`, with value `10`. -/
theorem ex_21_6_a :
    cg_IsRamsey cg_C216 cg_r216 1 1 ∧
      (∀ x y, cg_IsRamsey cg_C216 cg_r216 x y → x = 1 ∧ y = 1) ∧ cg_r216 1 1 = 10 := by
  refine ⟨⟨rfl, ?_⟩, fun x y h => ?_, by norm_num [cg_r216]⟩
  · rintro ⟨x, y⟩ (hq : x = y)
    subst hq
    fin_cases x <;> norm_num [cg_r216]
  · obtain ⟨hxy, hmax⟩ := h
    have hxy' : x = y := hxy
    subst hxy'
    have := hmax (1, 1) rfl
    fin_cases x
    · norm_num [cg_r216] at this
    · exact ⟨rfl, rfl⟩

/-- **Exercise 21.6 (b)** (Miao, p. 771): the one-period economy has no pure-strategy Nash
equilibrium. -/
theorem ex_21_6_b : ∀ x y, ¬ cg_IsNash cg_C216 cg_r216 x y := by
  rintro x y ⟨hxy, hmax⟩
  have hxy' : x = y := hxy
  subst hxy'
  fin_cases x
  · have := hmax 1; norm_num [cg_r216] at this
  · have := hmax 0; norm_num [cg_r216] at this

end Miao.DynamicGames

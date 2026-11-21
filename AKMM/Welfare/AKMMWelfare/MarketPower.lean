/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Monopolistic competition

AKMM, §6.3.5, pp. 172–175 (Dixit and Stiglitz, 1977). A continuum of goods carrying a measure
`μ` (the book's `[0, 1]` with Lebesgue measure is one instance), the CES aggregate
`C = (∫ c(i)^{1−1/ε} di)^{ε/(ε−1)}`, `ε ≠ 1`, `ε > 0`.

* (6.4): the two forms of the first-order condition agree (`eq_6_4`); under it
  `∫ p(i)c(i) di = λC` (`ds_expenditure`), `λ = P ≡ (∫ p(i)^{1−ε} di)^{1/(1−ε)}`
  (`ds_price_index`), the demand function `c(i) = C(p(i)/P)^{−ε}` (`ds_demand`), and `P` is
  homogeneous of degree one (`ds_price_index_homogeneous`).
* The firm's problem `max_c PC^{1/ε}c^{1−1/ε} − (w/A)c` (`dsProfit`, with revenue
  `p(c)c`: `ds_revenue`): for `ε > 1` the solution is `c = C(w/(A(1 − 1/ε)P))^{−ε}` with the price
  `p = (ε/(ε − 1))w/A`, a markup `µ = ε/(ε − 1) > 1`, and profit `(µ − 1)(w/A)c`
  (`ds_firm_optimum`). Fn. 10: for `ε < 1` profits are unbounded (`ds_no_max_lt_one`); for
  `ε = 1` no maximum exists and the supremum is the revenue `PC` (`ds_no_max_eq_one`).
* The symmetric equilibrium: `c = C`, `P = 1` give `w = A(1 − 1/ε)` (`ds_symmetric_wage`); with
  log utility the labour condition is `A(1 − 1/ε) = Cv′(C/A)` (`ds_equilibrium_condition`),
  which has at most one solution when `v′` is positive and nondecreasing
  (`ds_rhs_strictMono`, `ds_unique`); the planner's condition is `A = Cv′(C/A)`
  (`ds_planner_foc`), and equilibrium output is too low (`ds_underproduction`).
-/

namespace AKMM.Welfare

open MeasureTheory

/-- The identity behind (6.4) and the revenue: for `x, C > 0`,
`(x/C)^{−1/ε}·x = C^{1/ε}x^{1−1/ε}`. -/
theorem ds_rpow_ratio {ε x C : ℝ} (hx : 0 < x) (hC : 0 < C) :
    (x / C) ^ (-1 / ε) * x = C ^ (1 / ε) * x ^ (1 - 1 / ε) := by
  rw [Real.div_rpow hx.le hC.le, sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one,
    show -1 / ε = -(1 / ε) by ring, Real.rpow_neg hx.le, Real.rpow_neg hC.le]
  field_simp

/-- **AKMM, (6.4), p. 173.** With `S = ∫ c^{1−1/ε} > 0`, `C = S^{ε/(ε−1)}` and `x = c(i) > 0`,
the derivative form of the first-order condition
`λ(ε/(ε − 1))S^{ε/(ε−1)−1}(1 − 1/ε)x^{−1/ε}` equals `λ(x/C)^{−1/ε}`. -/
theorem eq_6_4 {ε S x lam : ℝ} (hε0 : ε ≠ 0) (hε1 : ε ≠ 1) (hS : 0 < S) (hx : 0 < x) :
    lam * (ε / (ε - 1)) * S ^ (ε / (ε - 1) - 1) * (1 - 1 / ε) * x ^ (-1 / ε) =
      lam * (x / S ^ (ε / (ε - 1))) ^ (-1 / ε) := by
  have hε1' : ε - 1 ≠ 0 := sub_ne_zero.2 hε1
  rw [Real.div_rpow hx.le (Real.rpow_nonneg hS.le _), ← Real.rpow_mul hS.le]
  have e1 : ε / (ε - 1) - 1 = 1 / (ε - 1) := by field_simp; ring
  have e2 : ε / (ε - 1) * (-1 / ε) = -(1 / (ε - 1)) := by field_simp
  have e3 : ε / (ε - 1) * (1 - 1 / ε) = 1 := by field_simp
  rw [e1, e2, Real.rpow_neg hS.le, div_inv_eq_mul]
  calc lam * (ε / (ε - 1)) * S ^ (1 / (ε - 1)) * (1 - 1 / ε) * x ^ (-1 / ε) =
      lam * (ε / (ε - 1) * (1 - 1 / ε)) * (x ^ (-1 / ε) * S ^ (1 / (ε - 1))) := by ring
    _ = _ := by rw [e3, mul_one]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **AKMM, p. 173: expenditure.** If `p(i) = λ(c(i)/C)^{−1/ε}` for all `i`, with `c > 0`,
`S = ∫ c^{1−1/ε} > 0` and `C = S^{ε/(ε−1)}`, then `∫ p(i)c(i) di = λC`: `λ` is the unit price of
the basket. -/
theorem ds_expenditure {μ : Measure Ω} {ε lam : ℝ} {c p : Ω → ℝ} (hε0 : ε ≠ 0) (hε1 : ε ≠ 1)
    (hc : ∀ i, 0 < c i) (hS : 0 < ∫ i, c i ^ (1 - 1 / ε) ∂μ)
    (hfoc : ∀ i, p i = lam * (c i / (∫ i, c i ^ (1 - 1 / ε) ∂μ) ^ (ε / (ε - 1))) ^ (-1 / ε)) :
    ∫ i, p i * c i ∂μ = lam * (∫ i, c i ^ (1 - 1 / ε) ∂μ) ^ (ε / (ε - 1)) := by
  set S := ∫ i, c i ^ (1 - 1 / ε) ∂μ with hSdef
  have hC : 0 < S ^ (ε / (ε - 1)) := Real.rpow_pos_of_pos hS _
  have e : (fun i => p i * c i) = fun i => (lam * (S ^ (ε / (ε - 1))) ^ (1 / ε)) *
      c i ^ (1 - 1 / ε) := by
    funext i
    rw [hfoc i, mul_assoc, ds_rpow_ratio (hc i) hC]
    ring
  rw [e, integral_const_mul, ← hSdef, ← Real.rpow_mul hS.le, mul_assoc]
  congr 1
  have hε1' : ε - 1 ≠ 0 := sub_ne_zero.2 hε1
  rw [← Real.rpow_add_one hS.ne']
  congr 1
  field_simp
  ring

/-- **AKMM, p. 173: the price index.** Under the first-order condition of `ds_expenditure` with
`λ > 0`, `λ = P ≡ (∫ p(i)^{1−ε} di)^{1/(1−ε)}`. -/
theorem ds_price_index {μ : Measure Ω} {ε lam : ℝ} {c p : Ω → ℝ} (hε0 : ε ≠ 0) (hε1 : ε ≠ 1)
    (hlam : 0 < lam) (hc : ∀ i, 0 < c i) (hS : 0 < ∫ i, c i ^ (1 - 1 / ε) ∂μ)
    (hfoc : ∀ i, p i = lam * (c i / (∫ i, c i ^ (1 - 1 / ε) ∂μ) ^ (ε / (ε - 1))) ^ (-1 / ε)) :
    (∫ i, p i ^ (1 - ε) ∂μ) ^ (1 / (1 - ε)) = lam := by
  set S := ∫ i, c i ^ (1 - 1 / ε) ∂μ with hSdef
  have hε1' : ε - 1 ≠ 0 := sub_ne_zero.2 hε1
  have hε1'' : 1 - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε1)
  have e : (fun i => p i ^ (1 - ε)) = fun i => (lam ^ (1 - ε) * S⁻¹) * c i ^ (1 - 1 / ε) := by
    funext i
    rw [hfoc i, Real.mul_rpow hlam.le (Real.rpow_nonneg (div_nonneg (hc i).le
      (Real.rpow_nonneg hS.le _)) _), ← Real.rpow_mul (div_nonneg (hc i).le
      (Real.rpow_nonneg hS.le _)), Real.div_rpow (hc i).le (Real.rpow_nonneg hS.le _),
      ← Real.rpow_mul hS.le]
    have e1 : -1 / ε * (1 - ε) = 1 - 1 / ε := by field_simp; ring
    have e2 : ε / (ε - 1) * (1 - 1 / ε) = 1 := by field_simp
    rw [e1, e2, Real.rpow_one]
    ring
  rw [e, integral_const_mul, ← hSdef, mul_assoc, inv_mul_cancel₀ hS.ne', mul_one,
    ← Real.rpow_mul hlam.le, mul_one_div_cancel hε1'', Real.rpow_one]

/-- **AKMM, p. 174: the demand function.** Under the first-order condition with `λ = P > 0`,
`c(i) = C(p(i)/P)^{−ε}`. -/
theorem ds_demand {ε lam C x px : ℝ} (hε0 : ε ≠ 0) (hlam : 0 < lam) (hC : 0 < C) (hx : 0 < x)
    (hfoc : px = lam * (x / C) ^ (-1 / ε)) : x = C * (px / lam) ^ (-ε) := by
  rw [hfoc, mul_div_cancel_left₀ _ hlam.ne', ← Real.rpow_mul (div_nonneg hx.le hC.le),
    show -1 / ε * -ε = 1 by field_simp, Real.rpow_one]
  field_simp

/-- **AKMM, p. 173: `P` is homogeneous of degree one** in the prices: scaling every price by
`s > 0` scales `P` by `s` (for `ε ≠ 1`, positive prices, `∫ p^{1−ε} ≥ 0`). -/
theorem ds_price_index_homogeneous {μ : Measure Ω} {ε s : ℝ} {p : Ω → ℝ} (hε1 : ε ≠ 1)
    (hs : 0 < s) (hp : ∀ i, 0 < p i) (hI : 0 ≤ ∫ i, p i ^ (1 - ε) ∂μ) :
    (∫ i, (s * p i) ^ (1 - ε) ∂μ) ^ (1 / (1 - ε)) =
      s * (∫ i, p i ^ (1 - ε) ∂μ) ^ (1 / (1 - ε)) := by
  have hε1'' : 1 - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε1)
  have e : (fun i => (s * p i) ^ (1 - ε)) = fun i => s ^ (1 - ε) * p i ^ (1 - ε) := by
    funext i; rw [Real.mul_rpow hs.le (hp i).le]
  rw [e, integral_const_mul, Real.mul_rpow (Real.rpow_nonneg hs.le _) hI,
    ← Real.rpow_mul hs.le, mul_one_div_cancel hε1'', Real.rpow_one]

/-- The monopolist's profit as a function of output, with the inverse demand substituted:
`PC^{1/ε}c^{1−1/ε} − (w/A)c` (AKMM, p. 174). -/
noncomputable def dsProfit (ε P C w A c : ℝ) : ℝ := P * C ^ (1 / ε) * c ^ (1 - 1 / ε) - w / A * c

/-- AKMM, p. 174: with the inverse demand `p = P(c/C)^{−1/ε}`, revenue `pc` is
`PC^{1/ε}c^{1−1/ε}`, so `dsProfit` is the firm's objective `pc − w ℓ` with `c = Aℓ`. -/
theorem ds_revenue {ε P C w A c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    P * (c / C) ^ (-1 / ε) * c - w * (c / A) = dsProfit ε P C w A c := by
  rw [dsProfit, mul_assoc, ds_rpow_ratio hc hC]
  ring

/-- **AKMM, p. 175: the firm's optimum for `ε > 1`.** With `P, C, w, A > 0`, the output
`c⋆ = C(w/(A(1 − 1/ε)P))^{−ε}` maximises `dsProfit` over `c > 0`; its price is
`P(c⋆/C)^{−1/ε} = (ε/(ε − 1))w/A`, a markup `µ = ε/(ε − 1) > 1` over marginal cost `w/A`, and the
maximal profit is `(µ − 1)(w/A)c⋆`. -/
theorem ds_firm_optimum {ε P C w A : ℝ} (hε : 1 < ε) (hP : 0 < P) (hC : 0 < C) (hw : 0 < w)
    (hA : 0 < A) :
    let cs := C * (w / (A * (1 - 1 / ε) * P)) ^ (-ε)
    (∀ c, 0 < c → dsProfit ε P C w A c ≤ dsProfit ε P C w A cs) ∧
      P * (cs / C) ^ (-1 / ε) = ε / (ε - 1) * (w / A) ∧ 1 < ε / (ε - 1) ∧
      dsProfit ε P C w A cs = (ε / (ε - 1) - 1) * (w / A) * cs := by
  intro cs
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  have hθ0 : 0 < 1 - 1 / ε := by rw [sub_pos, div_lt_one (by linarith)]; exact hε
  have hθ1 : 1 - 1 / ε < 1 := sub_lt_self 1 (by positivity)
  set X := w / (A * (1 - 1 / ε) * P) with hX
  have hXpos : 0 < X := by positivity
  have hcs : 0 < cs := mul_pos hC (Real.rpow_pos_of_pos hXpos _)
  -- the price at `cs`
  have hprice : (cs / C) ^ (-1 / ε) = X := by
    rw [show cs / C = X ^ (-ε) from mul_div_cancel_left₀ _ hC.ne', ← Real.rpow_mul hXpos.le,
      show -ε * (-1 / ε) = 1 by field_simp, Real.rpow_one]
  -- the first-order condition `Kθc⋆^{θ−1} = w/A`
  have hfoc : P * C ^ (1 / ε) * (1 - 1 / ε) * cs ^ (-1 / ε) = w / A := by
    have : cs ^ (-1 / ε) = C ^ (-1 / ε) * X := by
      have hCp : C ^ (-1 / ε) ≠ 0 := (Real.rpow_pos_of_pos hC _).ne'
      rw [← hprice, Real.div_rpow hcs.le hC.le]
      field_simp
    rw [this, show -1 / ε = -(1 / ε) by ring, Real.rpow_neg hC.le, hX]
    have : C ^ (1 / ε) ≠ 0 := (Real.rpow_pos_of_pos hC _).ne'
    have : 1 - 1 / ε ≠ 0 := hθ0.ne'
    field_simp
  refine ⟨fun c hc => ?_, ?_, ?_, ?_⟩
  · -- Bernoulli: `c^θ ≤ c⋆^θ + θc⋆^{θ−1}(c − c⋆)`
    have hb := rpow_one_add_le_one_add_mul_self (s := c / cs - 1)
      (by have := div_pos hc hcs; linarith) hθ0.le hθ1.le
    rw [add_sub_cancel] at hb
    have hb2 : c ^ (1 - 1 / ε) ≤ cs ^ (1 - 1 / ε) +
        (1 - 1 / ε) * cs ^ (-1 / ε) * (c - cs) := by
      have h1 : c ^ (1 - 1 / ε) = cs ^ (1 - 1 / ε) * (c / cs) ^ (1 - 1 / ε) := by
        rw [Real.div_rpow hc.le hcs.le]; field_simp
      have h2 : cs ^ (-1 / ε) * cs = cs ^ (1 - 1 / ε) := by
        rw [sub_eq_add_neg, Real.rpow_add hcs, Real.rpow_one, show -1 / ε = -(1 / ε) by ring]
        ring
      rw [h1]
      have hpos := Real.rpow_pos_of_pos hcs (1 - 1 / ε)
      calc cs ^ (1 - 1 / ε) * (c / cs) ^ (1 - 1 / ε) ≤
          cs ^ (1 - 1 / ε) * (1 + (1 - 1 / ε) * (c / cs - 1)) :=
            mul_le_mul_of_nonneg_left hb hpos.le
        _ = cs ^ (1 - 1 / ε) + (1 - 1 / ε) * (cs ^ (-1 / ε) * cs) * (c / cs - 1) := by
            rw [h2]; ring
        _ = _ := by field_simp
    have hK : 0 < P * C ^ (1 / ε) := mul_pos hP (Real.rpow_pos_of_pos hC _)
    unfold dsProfit
    have := mul_le_mul_of_nonneg_left hb2 hK.le
    have e : P * C ^ (1 / ε) * ((1 - 1 / ε) * cs ^ (-1 / ε) * (c - cs)) = w / A * (c - cs) := by
      rw [← hfoc]; ring
    nlinarith
  · rw [hprice, hX]
    field_simp
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [dsProfit, mul_assoc P, ← ds_rpow_ratio hcs hC, ← mul_assoc, hprice, hX]
    field_simp

/-- **AKMM, fn. 10, p. 175: `ε < 1`.** For `0 < ε < 1` (and `P, C > 0`) profits are unbounded
above: they can be made arbitrarily large by producing little at a high price. -/
theorem ds_no_max_lt_one {ε P C w A : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hP : 0 < P)
    (hC : 0 < C) (hw : 0 ≤ w) (hA : 0 < A) :
    ∀ M : ℝ, ∃ c, 0 < c ∧ M < dsProfit ε P C w A c := by
  intro M
  have hθ : 1 - 1 / ε < 0 := by rw [sub_neg, lt_div_iff₀ hε0]; linarith
  have hK : 0 < P * C ^ (1 / ε) := mul_pos hP (Real.rpow_pos_of_pos hC _)
  set N := (|M| + w / A + 1) / (P * C ^ (1 / ε)) with hN
  have hNpos : 0 < N := by positivity
  set c0 := N ^ (1 / (1 - 1 / ε)) with hc0
  have hc0pos : 0 < c0 := Real.rpow_pos_of_pos hNpos _
  refine ⟨min 1 c0, lt_min one_pos hc0pos, ?_⟩
  have hm := lt_min one_pos hc0pos
  have hpow : N ≤ (min 1 c0) ^ (1 - 1 / ε) := by
    have h1 : c0 ^ (1 - 1 / ε) = N := by
      rw [hc0, ← Real.rpow_mul hNpos.le, one_div_mul_cancel hθ.ne, Real.rpow_one]
    rw [← h1]
    exact Real.rpow_le_rpow_of_nonpos hm (min_le_right _ _) hθ.le
  unfold dsProfit
  have h1 : P * C ^ (1 / ε) * N ≤ P * C ^ (1 / ε) * (min 1 c0) ^ (1 - 1 / ε) :=
    mul_le_mul_of_nonneg_left hpow hK.le
  have h2 : P * C ^ (1 / ε) * N = |M| + w / A + 1 := by rw [hN]; field_simp
  have h3 : w / A * min 1 c0 ≤ w / A := by
    have := min_le_left 1 c0
    have : 0 ≤ w / A := div_nonneg hw hA.le
    nlinarith
  linarith [le_abs_self M]

/-- **AKMM, fn. 10, p. 175: `ε = 1`.** Revenue is `PC` whatever the output, so with `w, A > 0`
profit is below `PC` at every `c > 0`, but comes arbitrarily close: no maximum exists, and the
supremum is the revenue. -/
theorem ds_no_max_eq_one {P C w A : ℝ} (hw : 0 < w) (hA : 0 < A) :
    (∀ c, 0 < c → dsProfit 1 P C w A c < P * C) ∧
      ∀ η, 0 < η → ∃ c, 0 < c ∧ P * C - η < dsProfit 1 P C w A c := by
  have e : ∀ c, dsProfit 1 P C w A c = P * C - w / A * c := fun c => by
    simp [dsProfit]
  refine ⟨fun c hc => ?_, fun η hη => ⟨η / (2 * (w / A)), by positivity, ?_⟩⟩
  · rw [e]
    have : 0 < w / A * c := by positivity
    linarith
  rw [e]
  have : w / A * (η / (2 * (w / A))) = η / 2 := by field_simp
  linarith

/-- **AKMM, p. 175: the symmetric equilibrium wage.** With `c = C`, `P = 1`, the inverse demand
gives `p = 1`, and the markup `p = (ε/(ε − 1))w/A` gives `w = A(1 − 1/ε)`, below the marginal
product `A`. -/
theorem ds_symmetric_wage {ε C w A p : ℝ} (hε : 1 < ε) (hC : 0 < C) (hA : 0 < A)
    (hinv : p = 1 * (C / C) ^ (-1 / ε)) (hmark : p = ε / (ε - 1) * (w / A)) :
    p = 1 ∧ w = A * (1 - 1 / ε) ∧ w < A := by
  have hp : p = 1 := by rw [hinv, div_self hC.ne', Real.one_rpow, one_mul]
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  refine ⟨hp, ?_, ?_⟩
  · rw [hp] at hmark
    field_simp at hmark ⊢
    linarith
  · have hw : w = A * (1 - 1 / ε) := by
      rw [hp] at hmark; field_simp at hmark ⊢; linarith
    rw [hw]
    have : 0 < 1 / ε := by positivity
    nlinarith

/-- **AKMM, p. 175: the equilibrium condition.** With `u = log`, `L = C/A` and the labour
first-order condition `u′(C)w = v′(L)`, `w = A(1 − 1/ε)` gives `A(1 − 1/ε) = Cv′(C/A)`. -/
theorem ds_equilibrium_condition {ε C A w dvL : ℝ} (hC : 0 < C) (hw : w = A * (1 - 1 / ε))
    (hfoc : 1 / C * w = dvL) : A * (1 - 1 / ε) = C * dvL := by
  rw [← hfoc, ← hw]
  field_simp

/-- AKMM, p. 175: if `v′` is positive and nondecreasing on `(0, ∞)` (`v` convex and increasing)
and `A > 0`, then `C ↦ Cv′(C/A)` is strictly increasing on `(0, ∞)`. -/
theorem ds_rhs_strictMono {dv : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hpos : ∀ x, 0 < x → 0 < dv x) (hmono : MonotoneOn dv (Set.Ioi 0)) :
    StrictMonoOn (fun C => C * dv (C / A)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : 0 < x / A := div_pos hx hA
  have hy' : 0 < y / A := div_pos hy hA
  have h1 : dv (x / A) ≤ dv (y / A) := hmono hx' hy' (div_le_div_of_nonneg_right hxy.le hA.le)
  have h2 := hpos _ hx'
  calc x * dv (x / A) < y * dv (x / A) := mul_lt_mul_of_pos_right hxy h2
    _ ≤ y * dv (y / A) := mul_le_mul_of_nonneg_left h1 (le_of_lt hy)

/-- **AKMM, p. 175: uniqueness.** When `C ↦ Cv′(C/A)` is strictly increasing, the equation
`A(1 − 1/ε) = Cv′(C/A)` has at most one positive solution. -/
theorem ds_unique {dv : ℝ → ℝ} {A ε C₁ C₂ : ℝ}
    (hsm : StrictMonoOn (fun C => C * dv (C / A)) (Set.Ioi 0)) (h1 : 0 < C₁) (h2 : 0 < C₂)
    (he1 : A * (1 - 1 / ε) = C₁ * dv (C₁ / A)) (he2 : A * (1 - 1 / ε) = C₂ * dv (C₂ / A)) :
    C₁ = C₂ :=
  hsm.injOn h1 h2 (show C₁ * dv (C₁ / A) = C₂ * dv (C₂ / A) by rw [← he1, ← he2])

/-- **AKMM, p. 175: the planner.** If `C > 0` maximises `log C − v(C/A)` over `(0, ∞)` and `v`
has derivative `v′(C/A)` at `C/A`, then `A = Cv′(C/A)`. -/
theorem ds_planner_foc {v : ℝ → ℝ} {A C dvL : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hd : HasDerivAt v dvL (C / A))
    (hmax : ∀ x, 0 < x → Real.log x - v (x / A) ≤ Real.log C - v (C / A)) : A = C * dvL := by
  have hloc : IsLocalMax (fun x => Real.log x - v (x / A)) C :=
    Filter.mem_of_superset (Ioi_mem_nhds hC) fun x hx => hmax x hx
  have hder : HasDerivAt (fun x => Real.log x - v (x / A)) (C⁻¹ - dvL * (1 / A)) C := by
    have hin : HasDerivAt (fun x : ℝ => x / A) (1 / A) C := by
      simpa using (hasDerivAt_id C).div_const A
    exact (Real.hasDerivAt_log hC.ne').sub (hd.comp C hin)
  have := hloc.hasDerivAt_eq_zero hder
  field_simp at this
  linarith

/-- **AKMM, p. 175: under-production.** If `C_M` solves `A(1 − 1/ε) = C_Mv′(C_M/A)`, `C_P` solves
`A = C_Pv′(C_P/A)`, `C ↦ Cv′(C/A)` is strictly increasing, `ε > 0` and `A > 0`, then
`C_M < C_P`: equilibrium output (and hours `C/A`) are too low. -/
theorem ds_underproduction {dv : ℝ → ℝ} {A ε CM CP : ℝ} (hA : 0 < A) (hε : 0 < ε)
    (hsm : StrictMonoOn (fun C => C * dv (C / A)) (Set.Ioi 0)) (hM : 0 < CM) (hP : 0 < CP)
    (heM : A * (1 - 1 / ε) = CM * dv (CM / A)) (heP : A = CP * dv (CP / A)) : CM < CP := by
  have hlt : CM * dv (CM / A) < CP * dv (CP / A) := by
    rw [← heM, ← heP]
    have : 0 < A * (1 / ε) := by positivity
    nlinarith
  exact (hsm.lt_iff_lt hM hP).1 hlt

end AKMM.Welfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.BPTree
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Asset pricing with a stochastic discount factor

Miao, §13.8, pp. 446–449 (the SDF, (13.30), (13.31), the Hansen–Jagannathan bound, CAPM,
factor pricing, the CCAPM SDF) and Exercise 13.9 (p. 454). Conditional moments at a node are
moments under a finite conditional distribution `w` on the successor states `Ω`
(`w ≥ 0`, `∑ w = 1`): `bp_E`, `bp_Cov`, `bp_Var`, `bp_sd`.

* `eq_13_30`: `p_j = E[M f_j]` gives `E[M R_j] = 1` for `R_j = f_j/p_j`.
* `bp_riskfree`: `R_f = 1/E[M]`; `bp_excess`: `E[(R_j − R_f) M] = 0`.
* `eq_13_31`: `E[R_j − R_f] = −Cov(M, R_j − R_f)/E[M]`.
* `bp_cov_ge_neg_sd`: `Cov(X, Y) ≥ −σ(X)σ(Y)`; `bp_hansen_jagannathan`:
  `σ(M)/E[M] ≥ E[R_j − R_f]/σ(R_j − R_f)`.
* CAPM, `M = a + bR_m`: `bp_capm_market` (`E[R_m − R_f] = −b Var(R_m)/E[M]`), `bp_capm_asset`
  (`E[R_j − R_f] = −b Cov(R_m, R_j)/E[M]`), `bp_capm` (`E[R_j − R_f] = β_j E[R_m − R_f]` with
  `β_j = Cov(R_j, R_m)/Var(R_m)`).
* Factor pricing, `M = a + ∑ b_k F_k` (13.32): `eq_13_32_cov` and `bp_factor_pricing`
  (`E[R_j − R_f] = ∑ β_{jk} λ_k`).
* CCAPM: `bp_ccapm_euler` derives the representative agent's Euler equation
  `p u'(C) = β E[u'(C') f]` from optimality (a local maximum along the one-asset perturbation),
  hence the SDF `M = βu'(C')/u'(C)` (`bp_ccapm_sdf`).
* Exercise 13.9 (`ex_13_9_wealth`, `ex_13_9_sdf`): with log utility the wealth portfolio (the
  claim to aggregate consumption) has price `βC_t/(1 − β)`, return `R_w = C_{t+1}/(βC_t)` and
  `M = 1/R_w`. CAPM: `ex_13_9_capm_two_states` (exact when the conditional distribution has two
  states); `ex_13_9_capm_counterexample` (fails with three states).

**Corrections.**
* p. 448, CAPM: the book defines `β_{jt} = Cov_t[R_{j,t+1}, M_{t+1}]/Var_t(M_{t+1})`. With
  `M = a + bR_m` this is `Cov(R_j, R_m)/(b Var(R_m))`, and the stated relation
  `E[R_j − R_f] = β_j E[R_m − R_f]` holds only for `b = 1`; the book's own gloss ("the regression
  coefficient of the asset return `j` on the market portfolio return") is the correct
  `β_j = Cov(R_j, R_m)/Var(R_m)` (`bp_capm`). Counterexample: `bp_capm_book_beta_counterexample`.
* Exercise 13.9, "derive the CAPM": with log utility `M = 1/R_w`, which is not affine in `R_w`
  in general, so the CAPM in `R_w` holds exactly only when `1/R_w` is affine in `R_w` on the
  support (e.g. two states, `ex_13_9_capm_two_states`) and fails otherwise
  (`ex_13_9_capm_counterexample`); in general it is an approximation.
-/

open Filter Topology

namespace Miao.CompleteMarkets

/-- Conditional expectation under the finite distribution `w`. -/
def bp_E {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) : ℝ := ∑ ω, w ω * X ω

/-- Conditional covariance. -/
def bp_Cov {Ω : Type*} [Fintype Ω] (w X Y : Ω → ℝ) : ℝ :=
  bp_E w (fun ω => X ω * Y ω) - bp_E w X * bp_E w Y

/-- Conditional variance. -/
def bp_Var {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) : ℝ := bp_Cov w X X

/-- Conditional volatility `σ(X)`. -/
noncomputable def bp_sd {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) : ℝ := Real.sqrt (bp_Var w X)

variable {Ω : Type*} [Fintype Ω]

theorem bp_E_add (w X Y : Ω → ℝ) : bp_E w (fun ω => X ω + Y ω) = bp_E w X + bp_E w Y := by
  simp only [bp_E, mul_add, Finset.sum_add_distrib]

theorem bp_E_sub (w X Y : Ω → ℝ) : bp_E w (fun ω => X ω - Y ω) = bp_E w X - bp_E w Y := by
  simp only [bp_E, mul_sub, Finset.sum_sub_distrib]

theorem bp_E_mul_left (w X : Ω → ℝ) (a : ℝ) : bp_E w (fun ω => a * X ω) = a * bp_E w X := by
  simp only [bp_E, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

theorem bp_E_const (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (a : ℝ) : bp_E w (fun _ => a) = a := by
  simp only [bp_E, ← Finset.sum_mul, hw, one_mul]

theorem bp_E_finsetSum {K : Type*} (A : Finset K) (w : Ω → ℝ) (X : K → Ω → ℝ) :
    bp_E w (fun ω => ∑ k ∈ A, X k ω) = ∑ k ∈ A, bp_E w (X k) := by
  simp only [bp_E, Finset.mul_sum]
  exact Finset.sum_comm

/-- The covariance in deviation form `Cov(X, Y) = E[(X − EX)(Y − EY)]`. -/
theorem bp_Cov_eq_dev (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (X Y : Ω → ℝ) :
    bp_Cov w X Y = bp_E w (fun ω => (X ω - bp_E w X) * (Y ω - bp_E w Y)) := by
  have h : (fun ω => (X ω - bp_E w X) * (Y ω - bp_E w Y)) =
      fun ω => X ω * Y ω - (bp_E w Y * X ω + (bp_E w X * Y ω - bp_E w X * bp_E w Y)) := by
    funext ω
    ring
  rw [h, bp_E_sub, bp_E_add, bp_E_sub, bp_E_mul_left, bp_E_mul_left, bp_E_const w hw]
  unfold bp_Cov
  ring

theorem bp_Cov_comm (w X Y : Ω → ℝ) : bp_Cov w X Y = bp_Cov w Y X := by
  unfold bp_Cov
  simp only [mul_comm (X _), mul_comm (bp_E w X)]

/-- `Cov(a + bX, Y) = b Cov(X, Y)`. -/
theorem bp_Cov_affine_left (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (a b : ℝ) (X Y : Ω → ℝ) :
    bp_Cov w (fun ω => a + b * X ω) Y = b * bp_Cov w X Y := by
  unfold bp_Cov
  have h1 : (fun ω => (a + b * X ω) * Y ω) = fun ω => a * Y ω + b * (X ω * Y ω) := by
    funext ω
    ring
  rw [h1, bp_E_add, bp_E_mul_left, bp_E_mul_left, bp_E_add, bp_E_const w hw, bp_E_mul_left]
  ring

/-- `Cov(X, Y − c) = Cov(X, Y)` for a constant `c`. -/
theorem bp_Cov_sub_const (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (X Y : Ω → ℝ) (c : ℝ) :
    bp_Cov w X (fun ω => Y ω - c) = bp_Cov w X Y := by
  unfold bp_Cov
  have h1 : (fun ω => X ω * (Y ω - c)) = fun ω => X ω * Y ω - c * X ω := by
    funext ω
    ring
  rw [h1, bp_E_sub, bp_E_sub, bp_E_mul_left, bp_E_const w hw]
  ring

/-- `Cov(∑ₖ bₖ Fₖ, Y) = ∑ₖ bₖ Cov(Fₖ, Y)`. -/
theorem bp_Cov_sum_left {K : Type*} [Fintype K] (w X : Ω → ℝ) (b : K → ℝ) (F : K → Ω → ℝ) :
    bp_Cov w (fun ω => ∑ k, b k * F k ω) X = ∑ k, b k * bp_Cov w (F k) X := by
  unfold bp_Cov
  have h1 : (fun ω => (∑ k, b k * F k ω) * X ω) = fun ω => ∑ k, b k * (F k ω * X ω) := by
    funext ω
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h1, bp_E_finsetSum, bp_E_finsetSum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [bp_E_mul_left, bp_E_mul_left]
  ring

theorem bp_Var_nonneg (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw : ∑ ω, w ω = 1) (X : Ω → ℝ) :
    0 ≤ bp_Var w X := by
  unfold bp_Var
  rw [bp_Cov_eq_dev w hw]
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hw0 ω) (mul_self_nonneg _))

/-- The Cauchy–Schwarz inequality `Cov(X, Y)² ≤ Var(X) Var(Y)`. -/
theorem bp_Cov_sq_le (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw : ∑ ω, w ω = 1) (X Y : Ω → ℝ) :
    bp_Cov w X Y ^ 2 ≤ bp_Var w X * bp_Var w Y := by
  unfold bp_Var
  rw [bp_Cov_eq_dev w hw, bp_Cov_eq_dev w hw, bp_Cov_eq_dev w hw]
  unfold bp_E
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => Real.sqrt (w ω) * (X ω - bp_E w X)) (fun ω => Real.sqrt (w ω) * (Y ω - bp_E w Y))
  have e1 : ∀ ω, Real.sqrt (w ω) * (X ω - bp_E w X) * (Real.sqrt (w ω) * (Y ω - bp_E w Y)) =
      w ω * ((X ω - bp_E w X) * (Y ω - bp_E w Y)) := by
    intro ω
    have := Real.mul_self_sqrt (hw0 ω)
    linear_combination ((X ω - bp_E w X) * (Y ω - bp_E w Y)) * this
  have e2 : ∀ (Z : Ω → ℝ) (c : ℝ) ω, (Real.sqrt (w ω) * (Z ω - c)) ^ 2 =
      w ω * ((Z ω - c) * (Z ω - c)) := by
    intro Z c ω
    rw [mul_pow, Real.sq_sqrt (hw0 ω)]
    ring
  simp only [e1, e2] at h
  exact h

/-- `Cov(X, Y) ≥ −σ(X)σ(Y)` (Miao, p. 447). -/
theorem bp_cov_ge_neg_sd (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw : ∑ ω, w ω = 1)
    (X Y : Ω → ℝ) : -(bp_sd w X * bp_sd w Y) ≤ bp_Cov w X Y := by
  have h := Real.abs_le_sqrt (bp_Cov_sq_le w hw0 hw X Y)
  rw [Real.sqrt_mul (bp_Var_nonneg w hw0 hw X)] at h
  unfold bp_sd
  linarith [neg_abs_le (bp_Cov w X Y)]

/-- Miao, (13.30), p. 446: if `p_j = E[M f_j]` and `R_j = f_j/p_j`, then `E[M R_j] = 1`. -/
theorem eq_13_30 (w M f : Ω → ℝ) (p : ℝ) (hp : p ≠ 0) (hpr : p = bp_E w (fun ω => M ω * f ω)) :
    bp_E w (fun ω => M ω * (f ω / p)) = 1 := by
  have : (fun ω => M ω * (f ω / p)) = fun ω => (1 / p) * (M ω * f ω) := by
    funext ω
    ring
  rw [this, bp_E_mul_left, ← hpr]
  field_simp

/-- Miao, p. 446: the riskfree rate `R_f = 1/E[M]`. -/
theorem bp_riskfree (w M : Ω → ℝ) (Rf : ℝ) (h : bp_E w (fun ω => M ω * Rf) = 1) :
    Rf = 1 / bp_E w M := by
  have : bp_E w (fun ω => M ω * Rf) = Rf * bp_E w M := by
    rw [← bp_E_mul_left]
    congr 1
    funext ω
    ring
  rw [this] at h
  have hM : bp_E w M ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  field_simp
  linarith

/-- Miao, p. 447: the conditional expected excess return weighted by the SDF vanishes,
`E[(R_j − R_f) M] = 0`. -/
theorem bp_excess (w M R : Ω → ℝ) (Rf : ℝ) (hR : bp_E w (fun ω => M ω * R ω) = 1)
    (hf : bp_E w (fun ω => M ω * Rf) = 1) : bp_E w (fun ω => (R ω - Rf) * M ω) = 0 := by
  have : (fun ω => (R ω - Rf) * M ω) = fun ω => M ω * R ω - M ω * Rf := by
    funext ω
    ring
  rw [this, bp_E_sub, hR, hf, sub_self]

/-- Miao, (13.31), p. 447: `E[R_j − R_f] = −Cov(M, R_j − R_f)/E[M]`. -/
theorem eq_13_31 (w M R : Ω → ℝ) (Rf : ℝ) (hR : bp_E w (fun ω => M ω * R ω) = 1)
    (hf : bp_E w (fun ω => M ω * Rf) = 1) (hM : bp_E w M ≠ 0) :
    bp_E w (fun ω => R ω - Rf) = -bp_Cov w M (fun ω => R ω - Rf) / bp_E w M := by
  have hx := bp_excess w M R Rf hR hf
  unfold bp_Cov
  have : (fun ω => M ω * (R ω - Rf)) = fun ω => (R ω - Rf) * M ω := by
    funext ω
    ring
  rw [this, hx]
  field_simp
  ring

/-- Miao, p. 447 (Hansen–Jagannathan): the Sharpe ratio of any asset is bounded by the market
price of risk, `σ(M)/E[M] ≥ E[R_j − R_f]/σ(R_j − R_f)`. -/
theorem bp_hansen_jagannathan (w : Ω → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hw : ∑ ω, w ω = 1)
    (M R : Ω → ℝ) (Rf : ℝ) (hR : bp_E w (fun ω => M ω * R ω) = 1)
    (hf : bp_E w (fun ω => M ω * Rf) = 1) (hM : 0 < bp_E w M)
    (hsd : 0 < bp_sd w (fun ω => R ω - Rf)) :
    bp_E w (fun ω => R ω - Rf) / bp_sd w (fun ω => R ω - Rf) ≤ bp_sd w M / bp_E w M := by
  rw [eq_13_31 w M R Rf hR hf hM.ne']
  have hc := bp_cov_ge_neg_sd w hw0 hw M (fun ω => R ω - Rf)
  rw [div_div, div_le_div_iff₀ (mul_pos hM hsd) hM]
  have : 0 ≤ bp_sd w M := Real.sqrt_nonneg _
  nlinarith

/-- CAPM, Miao, p. 448: with `M = a + bR_m`, `E[R_m − R_f] = −b Var(R_m)/E[M]`. -/
theorem bp_capm_market (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (M Rm : Ω → ℝ) (a b Rf : ℝ)
    (hMdef : ∀ ω, M ω = a + b * Rm ω) (hRm : bp_E w (fun ω => M ω * Rm ω) = 1)
    (hf : bp_E w (fun ω => M ω * Rf) = 1) (hM : bp_E w M ≠ 0) :
    bp_E w (fun ω => Rm ω - Rf) = -b * bp_Var w Rm / bp_E w M := by
  rw [eq_13_31 w M Rm Rf hRm hf hM, bp_Cov_sub_const w hw, show M = fun ω => a + b * Rm ω from
    funext hMdef, bp_Cov_affine_left w hw]
  unfold bp_Var
  ring

/-- CAPM, Miao, p. 448: with `M = a + bR_m`, `E[R_j − R_f] = −b Cov(R_m, R_j)/E[M]`. -/
theorem bp_capm_asset (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (M Rm R : Ω → ℝ) (a b Rf : ℝ)
    (hMdef : ∀ ω, M ω = a + b * Rm ω) (hR : bp_E w (fun ω => M ω * R ω) = 1)
    (hf : bp_E w (fun ω => M ω * Rf) = 1) (hM : bp_E w M ≠ 0) :
    bp_E w (fun ω => R ω - Rf) = -b * bp_Cov w Rm R / bp_E w M := by
  rw [eq_13_31 w M R Rf hR hf hM, bp_Cov_sub_const w hw, show M = fun ω => a + b * Rm ω from
    funext hMdef, bp_Cov_affine_left w hw]
  ring

/-- **CAPM** (Sharpe–Lintner, Miao, p. 448, corrected beta): with `M = a + bR_m` and
`Var(R_m) ≠ 0`, `E[R_j − R_f] = β_j E[R_m − R_f]` where
`β_j = Cov(R_j, R_m)/Var(R_m)` is the regression coefficient of `R_j` on `R_m`. -/
theorem bp_capm (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (M Rm R : Ω → ℝ) (a b Rf : ℝ)
    (hMdef : ∀ ω, M ω = a + b * Rm ω) (hRm : bp_E w (fun ω => M ω * Rm ω) = 1)
    (hR : bp_E w (fun ω => M ω * R ω) = 1) (hf : bp_E w (fun ω => M ω * Rf) = 1)
    (hM : bp_E w M ≠ 0) (hV : bp_Var w Rm ≠ 0) :
    bp_E w (fun ω => R ω - Rf) =
      bp_Cov w R Rm / bp_Var w Rm * bp_E w (fun ω => Rm ω - Rf) := by
  rw [bp_capm_asset w hw M Rm R a b Rf hMdef hR hf hM,
    bp_capm_market w hw M Rm a b Rf hMdef hRm hf hM, bp_Cov_comm w R Rm]
  field_simp

/-- The weights `(1/2, 1/2)` on two states. -/
noncomputable def bp_half : Fin 2 → ℝ := fun _ => 1 / 2

/-- Counterexample to the book's CAPM beta `β_j = Cov(R_j, M)/Var(M)` (Miao, p. 448): two
equally likely states, `R_m = (1, 3)`, `M = 9/8 − R_m/4 = (7/8, 3/8)`, `R_f = 8/5`. The SDF
prices `R_m` and `R_f`, but for `j = m` the book's beta is `−4`, not `1`, and
`E[R_m − R_f] = 2/5 ≠ −4 · 2/5`. -/
theorem bp_capm_book_beta_counterexample :
    let Rm : Fin 2 → ℝ := ![1, 3]
    let M : Fin 2 → ℝ := fun ω => 9 / 8 + (-1 / 4) * Rm ω
    bp_E bp_half (fun ω => M ω * Rm ω) = 1 ∧ bp_E bp_half (fun ω => M ω * (8 / 5)) = 1 ∧
      bp_E bp_half (fun ω => Rm ω - 8 / 5) ≠
        bp_Cov bp_half Rm M / bp_Var bp_half M * bp_E bp_half (fun ω => Rm ω - 8 / 5) := by
  intro Rm M
  simp only [bp_E, bp_Cov, bp_Var, bp_half, Fin.sum_univ_two, Rm, M, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- Miao, p. 449, factor pricing: with `M = a + ∑ₖ bₖ Fₖ` (13.32),
`−Cov(M, R_j − R_f) = −∑ₖ bₖ Var(Fₖ) · Cov(Fₖ, R_j)/Var(Fₖ)`. -/
theorem eq_13_32_cov {K : Type*} [Fintype K] (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (M R : Ω → ℝ)
    (a Rf : ℝ) (b : K → ℝ) (F : K → Ω → ℝ) (hMdef : ∀ ω, M ω = a + ∑ k, b k * F k ω)
    (hVF : ∀ k, bp_Var w (F k) ≠ 0) :
    -bp_Cov w M (fun ω => R ω - Rf) = -∑ k, b k * bp_Cov w (F k) R ∧
      -∑ k, b k * bp_Cov w (F k) R =
        -∑ k, b k * bp_Var w (F k) * (bp_Cov w (F k) R / bp_Var w (F k)) := by
  refine ⟨?_, ?_⟩
  · rw [bp_Cov_sub_const w hw, show M = fun ω => a + 1 * ∑ k, b k * F k ω by
      funext ω
      rw [hMdef, one_mul], bp_Cov_affine_left w hw, one_mul, bp_Cov_sum_left]
  · congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    field_simp [hVF k]

/-- **Factor pricing model** (Miao, p. 449): with `M = a + ∑ₖ bₖ Fₖ`,
`E[R_j − R_f] = ∑ₖ β_{jk} λ_k`, `β_{jk} = Cov(Fₖ, R_j)/Var(Fₖ)`,
`λ_k = −bₖ Var(Fₖ)/E[M]`. -/
theorem bp_factor_pricing {K : Type*} [Fintype K] (w : Ω → ℝ) (hw : ∑ ω, w ω = 1)
    (M R : Ω → ℝ) (a Rf : ℝ) (b : K → ℝ) (F : K → Ω → ℝ)
    (hMdef : ∀ ω, M ω = a + ∑ k, b k * F k ω) (hVF : ∀ k, bp_Var w (F k) ≠ 0)
    (hR : bp_E w (fun ω => M ω * R ω) = 1) (hf : bp_E w (fun ω => M ω * Rf) = 1)
    (hM : bp_E w M ≠ 0) :
    bp_E w (fun ω => R ω - Rf) =
      ∑ k, bp_Cov w (F k) R / bp_Var w (F k) * (-b k * bp_Var w (F k) / bp_E w M) := by
  rw [eq_13_31 w M R Rf hR hf hM, (eq_13_32_cov w hw M R a Rf b F hMdef hVF).1, neg_div,
    Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  field_simp [hVF k]

/-- The CCAPM Euler equation from optimality (Miao, p. 449). The representative agent consumes
`C` today and `C'_ω` tomorrow; buying `ε` units of an asset with price `p` and payoff `f` gives
utility `u(C − pε) + β E[u(C' + fε)]`. If `ε = 0` is a local maximum and `u` is differentiable,
then `p u'(C) = β E[u'(C') f]`. -/
theorem bp_ccapm_euler (w : Ω → ℝ) (u u' : ℝ → ℝ) (hu : ∀ x, HasDerivAt u (u' x) x)
    (β C p : ℝ) (C' f : Ω → ℝ)
    (hmax : IsLocalMax (fun ε => u (C - p * ε) + β * bp_E w (fun ω => u (C' ω + f ω * ε))) 0) :
    p * u' C = β * bp_E w (fun ω => u' (C' ω) * f ω) := by
  have h1 : HasDerivAt (fun ε => u (C - p * ε)) (u' C * (-p)) 0 := by
    have hin : HasDerivAt (fun ε : ℝ => C - p * ε) (-p) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul p |>.const_sub C
    exact (hu C).comp_of_eq 0 hin (by ring)
  have h2 : ∀ ω, HasDerivAt (fun ε => w ω * u (C' ω + f ω * ε)) (w ω * (u' (C' ω) * f ω)) 0 := by
    intro ω
    have hin : HasDerivAt (fun ε : ℝ => C' ω + f ω * ε) (f ω) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (f ω)).const_add (C' ω)
    exact ((hu (C' ω)).comp_of_eq 0 hin (by ring)).const_mul (w ω)
  have h3 : HasDerivAt (fun ε => bp_E w (fun ω => u (C' ω + f ω * ε)))
      (bp_E w (fun ω => u' (C' ω) * f ω)) 0 := by
    unfold bp_E
    have := HasDerivAt.sum (u := Finset.univ) (fun ω _ => h2 ω)
    convert this using 1
    funext ε
    simp
  have h := hmax.hasDerivAt_eq_zero (h1.add (h3.const_mul β))
  linarith

/-- The CCAPM stochastic discount factor (Miao, p. 449): the Euler equation `p u'(C) =
β E[u'(C') f]` with `u'(C) ≠ 0` says `p = E[M f]` with `M = βu'(C')/u'(C)`. -/
theorem bp_ccapm_sdf (w : Ω → ℝ) (u' : ℝ → ℝ) (β C p : ℝ) (C' f : Ω → ℝ) (hC : u' C ≠ 0)
    (heul : p * u' C = β * bp_E w (fun ω => u' (C' ω) * f ω)) :
    p = bp_E w (fun ω => β * u' (C' ω) / u' C * f ω) := by
  have : (fun ω => β * u' (C' ω) / u' C * f ω) = fun ω => β / u' C * (u' (C' ω) * f ω) := by
    funext ω
    ring
  rw [this, bp_E_mul_left, ← mul_div_right_comm, ← heul]
  field_simp

/-- **Exercise 13.9** (Miao, p. 454), the wealth portfolio. With log utility and aggregate
consumption `C > 0` on the event tree, the claim to aggregate consumption with price
`p^w_t = βC_t/(1 − β)` satisfies the Euler equation
`u'(C_t) p^w_t = β E_t[u'(C_{t+1})(p^w_{t+1} + C_{t+1})]`, and its return is
`R_{w,t+1} = (p^w_{t+1} + C_{t+1})/p^w_t = C_{t+1}/(βC_t)`. -/
theorem ex_13_9_wealth {S : Type*} [Fintype S] (T : BPTree S) (β : ℝ) (hβ : 0 < β)
    (hβ1 : β < 1) (C : List S → ℝ) (hC : ∀ h, 0 < C h) (h : List S) :
    1 / C h * (β * C h / (1 - β)) =
        β * bp_condExp T 1 (fun g => 1 / C g * (β * C g / (1 - β) + C g)) h ∧
      ∀ s, (β * C (s :: h) / (1 - β) + C (s :: h)) / (β * C h / (1 - β)) =
        C (s :: h) / (β * C h) := by
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  refine ⟨?_, fun s => ?_⟩
  · have : (fun g => 1 / C g * (β * C g / (1 - β) + C g)) = fun _ => 1 / (1 - β) := by
      funext g
      have := (hC g).ne'
      field_simp
      ring
    rw [this, bp_condExp_const]
    have := (hC h).ne'
    field_simp
  · have := (hC h).ne'
    have := (hC (s :: h)).ne'
    have := hβ.ne'
    field_simp
    ring

/-- **Exercise 13.9** (Miao, p. 454): with log utility the SDF is the inverse of the return on
the wealth portfolio, `M_{t+1} = βu'(C_{t+1})/u'(C_t) = βC_t/C_{t+1} = 1/R_{w,t+1}`. -/
theorem ex_13_9_sdf (β Ct Ct1 : ℝ) (hβ : 0 < β) (hCt : 0 < Ct) (hCt1 : 0 < Ct1) :
    β * (1 / Ct1) / (1 / Ct) = 1 / (Ct1 / (β * Ct)) := by
  have := hCt.ne'
  have := hCt1.ne'
  have := hβ.ne'
  field_simp

/-- Exercise 13.9, CAPM in the two-state case: if the conditional distribution has two states
and `R_w` takes different values in them, `M = 1/R_w` is affine in `R_w`, so
`E[R_j − R_f] = β_j E[R_w − R_f]` with `β_j = Cov(R_j, R_w)/Var(R_w)`. -/
theorem ex_13_9_capm_two_states (w : Fin 2 → ℝ) (hw : ∑ ω, w ω = 1) (Rw R : Fin 2 → ℝ)
    (Rf : ℝ) (hRw : ∀ ω, 0 < Rw ω) (hne : Rw 0 ≠ Rw 1)
    (hRm : bp_E w (fun ω => 1 / Rw ω * Rw ω) = 1) (hR : bp_E w (fun ω => 1 / Rw ω * R ω) = 1)
    (hf : bp_E w (fun ω => 1 / Rw ω * Rf) = 1) (hM : bp_E w (fun ω => 1 / Rw ω) ≠ 0)
    (hV : bp_Var w Rw ≠ 0) :
    bp_E w (fun ω => R ω - Rf) = bp_Cov w R Rw / bp_Var w Rw * bp_E w (fun ω => Rw ω - Rf) := by
  set b := (1 / Rw 1 - 1 / Rw 0) / (Rw 1 - Rw 0) with hb
  set a := 1 / Rw 0 - b * Rw 0 with ha
  have hsub : Rw 1 - Rw 0 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hMdef : ∀ ω, 1 / Rw ω = a + b * Rw ω := by
    intro ω
    fin_cases ω
    · simp [ha]
    · change 1 / Rw 1 = a + b * Rw 1
      have := (hRw 0).ne'
      have := (hRw 1).ne'
      simp only [ha, hb]
      field_simp
      ring
  exact bp_capm w hw (fun ω => 1 / Rw ω) Rw R a b Rf hMdef hRm hR hf hM hV

/-- The weights `(1/3, 1/3, 1/3)` on three states. -/
noncomputable def bp_third : Fin 3 → ℝ := fun _ => 1 / 3

/-- Counterexample to an exact CAPM in Exercise 13.9: three equally likely states,
`R_w = (1, 2, 4)`, `M = 1/R_w`, `R_f = 12/7` and the Arrow security of state 0, `R_j = (3, 0, 0)`.
`M` prices `R_w`, `R_f` and `R_j`, but `E[R_j − R_f] = −5/7` while
`β_j E[R_w − R_f] = −26/49`. -/
theorem ex_13_9_capm_counterexample :
    let Rw : Fin 3 → ℝ := ![1, 2, 4]
    let R : Fin 3 → ℝ := ![3, 0, 0]
    bp_E bp_third (fun ω => 1 / Rw ω * Rw ω) = 1 ∧
      bp_E bp_third (fun ω => 1 / Rw ω * R ω) = 1 ∧
      bp_E bp_third (fun ω => 1 / Rw ω * (12 / 7)) = 1 ∧
      bp_E bp_third (fun ω => R ω - 12 / 7) ≠
        bp_Cov bp_third R Rw / bp_Var bp_third Rw * bp_E bp_third (fun ω => Rw ω - 12 / 7) := by
  intro Rw R
  simp only [bp_E, bp_Cov, bp_Var, bp_third, Fin.sum_univ_three, Rw, R, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num

end Miao.CompleteMarkets

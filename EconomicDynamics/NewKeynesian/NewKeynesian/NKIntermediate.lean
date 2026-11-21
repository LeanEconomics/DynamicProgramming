/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The basic DNK model: intermediate goods firms and Calvo pricing (Miao §19.1.3)

Miao, §19.1.3, pp. 619–621. Firm `j` produces `Y^j = A(N^j)^{1−α}`, `α ∈ [0, 1)` (19.8), and
faces the demand curve (19.6). Write `w = W/P` for the real wage.

* Cost minimisation: the labour requirement `N = (Y/A)^{1/(1−α)}` (`nk_labor_req`), the real
  total cost `TC(Y) = w(Y/A)^{1/(1−α)}` (`nk_TC`) and the real marginal cost
  `MC = TC'(Y) = w/(A(1 − α)N^{−α}) = w/(A(1 − α)(Y/A)^{−α/(1−α)})` (`nk_MC_deriv`), equal to the
  Lagrange multiplier of the constraint (19.8) (`nk_MC_lagrange`).
* (19.9), the average marginal cost (`nk_MCavg`), and (19.10):
  `MC^j = MC(Y/Y^j)^{−α/(1−α)} = MC(P^j/P)^{εα/(α−1)}` (`eq_19_10`); firms with higher prices
  have lower marginal costs when `α > 0` (`nk_MC_antitone`).
* Calvo pricing. The derivative of the period-`t + k` profit
  `P*Y_{t+k|t}/P_{t+k} − TC_{t+k}(Y_{t+k|t})`, `Y_{t+k|t} = (P*/P_{t+k})^{−ε}Y_{t+k}`, is
  `(1 − ε)P*^{−ε−1}(Y_{t+k}/P_{t+k}^{1−ε})(P* − μMC_{t+k|t}P_{t+k})`, `μ = ε/(ε − 1)`
  (`nk_calvo_term_deriv`); for an objective with finitely many (date, state) terms and weights
  `w_k` (the products `θ^kβ^kΛ_{t+k}/Λ_t` times probabilities), the first-order condition is the
  printed one (`nk_calvo_foc`).
* (19.11), the optimal reset price, solves the first-order condition, for a summable family of
  terms indexed by any type (dates and states) (`eq_19_11`); (19.12), the marginal cost of a
  firm that reset its price at `t` (`eq_19_12`).

**Departure.** The derivative of the infinite-horizon objective is not formalised: the
first-order condition is derived for objectives with finitely many terms (`nk_calvo_foc`), and
(19.11) is derived from the first-order condition for infinitely many terms (`eq_19_11`).
-/

namespace Miao.NewKeynesian

/-- Miao, p. 619: the labour needed for output `Y` under (19.8): `Y = AN^{1−α}` iff
`N = (Y/A)^{1/(1−α)}` (`A, N, Y > 0`, `α < 1`). -/
theorem nk_labor_req {A N Y α : ℝ} (hA : 0 < A) (hN : 0 < N) (hY0 : 0 < Y) (hα : α < 1) :
    Y = A * N ^ (1 - α) ↔ N = (Y / A) ^ (1 / (1 - α)) := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  constructor
  · intro h
    rw [h, mul_div_cancel_left₀ _ hA.ne', ← Real.rpow_mul hN.le,
      show (1 - α) * (1 / (1 - α)) = 1 by field_simp, Real.rpow_one]
  · intro h
    have hY : 0 ≤ Y / A := (div_pos hY0 hA).le
    rw [h, ← Real.rpow_mul hY, show 1 / (1 - α) * (1 - α) = 1 by field_simp, Real.rpow_one]
    field_simp

/-- Miao, p. 619: the real total cost `TC(Y) = w(Y/A)^{1/(1−α)}` of output `Y` at real wage
`w = W/P`. -/
noncomputable def nk_TC (w A α Y : ℝ) : ℝ := w * (Y / A) ^ (1 / (1 - α))

/-- **(19.9)** (Miao, p. 620): the real marginal cost `MC = w/(A(1 − α)(Y/A)^{−α/(1−α)})`. -/
noncomputable def nk_MCavg (w A α Y : ℝ) : ℝ := w / (A * (1 - α) * (Y / A) ^ (-α / (1 - α)))

/-- Miao, p. 620: the real marginal cost is the derivative of the total cost:
`TC'(Y) = w/(A(1 − α)(Y/A)^{−α/(1−α)})` for `Y, A > 0`, `α < 1`. -/
theorem nk_MC_deriv {w A α Y : ℝ} (hA : 0 < A) (hY : 0 < Y) (hα : α < 1) :
    HasDerivAt (nk_TC w A α) (nk_MCavg w A α Y) Y := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have hq : 0 < Y / A := div_pos hY hA
  have hd := (((hasDerivAt_id Y).div_const A).rpow_const (p := 1 / (1 - α))
    (Or.inl hq.ne')).const_mul w
  refine hd.congr_deriv ?_
  simp only [id, nk_MCavg]
  have e : 1 / (1 - α) - 1 = -(-α / (1 - α)) := by field_simp; ring
  rw [e, Real.rpow_neg hq.le]
  have := Real.rpow_pos_of_pos hq (-α / (1 - α))
  field_simp

/-- Miao, p. 620: `MC` is the Lagrange multiplier of the cost-minimisation problem: the
first-order condition `w = λA(1 − α)N^{−α}` gives `λ = MC` at `N = (Y/A)^{1/(1−α)}`. -/
theorem nk_MC_lagrange {w A α Y lam : ℝ} (hA : 0 < A) (hY : 0 < Y) (hα : α < 1)
    (hfoc : w = lam * (A * (1 - α) * ((Y / A) ^ (1 / (1 - α))) ^ (-α))) :
    lam = nk_MCavg w A α Y ∧
      nk_MCavg w A α Y = w / (A * (1 - α) * ((Y / A) ^ (1 / (1 - α))) ^ (-α)) := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have h1p : (0 : ℝ) < 1 - α := by linarith
  have hq : 0 < Y / A := div_pos hY hA
  have e : ((Y / A) ^ (1 / (1 - α))) ^ (-α) = (Y / A) ^ (-α / (1 - α)) := by
    rw [← Real.rpow_mul hq.le]
    congr 1
    ring
  have hpos : 0 < A * (1 - α) * (Y / A) ^ (-α / (1 - α)) := by
    have := Real.rpow_pos_of_pos hq (-α / (1 - α))
    positivity
  rw [e] at hfoc ⊢
  refine ⟨?_, rfl⟩
  rw [nk_MCavg, hfoc]
  field_simp

/-- Miao, p. 620: with `MC^j` the marginal cost at output `Y^j` and `MC` the average (19.9),
`MC^j = MC(Y/Y^j)^{−α/(1−α)}`. -/
theorem nk_MC_ratio {w A α Y Yj : ℝ} (hA : 0 < A) (hY : 0 < Y) (hYj : 0 < Yj) :
    nk_MCavg w A α Yj = nk_MCavg w A α Y * (Y / Yj) ^ (-α / (1 - α)) := by
  have hq : 0 < Y / A := div_pos hY hA
  have hqj : 0 < Yj / A := div_pos hYj hA
  simp only [nk_MCavg]
  rw [show Y / Yj = (Y / A) / (Yj / A) by field_simp, Real.div_rpow hq.le hqj.le]
  have := Real.rpow_pos_of_pos hq (-α / (1 - α))
  have := Real.rpow_pos_of_pos hqj (-α / (1 - α))
  by_cases h : A * (1 - α) = 0
  · simp [h]
  · field_simp

/-- **(19.10)** (Miao, p. 620): `MC^j = MC(Y/Y^j)^{−α/(1−α)} = MC(P^j/P)^{εα/(α−1)}` for a firm on
the demand curve `Y^j = (P^j/P)^{−ε}Y`. -/
theorem eq_19_10 {w A α ε Y Pj P : ℝ} (hA : 0 < A) (hY : 0 < Y) (hPj : 0 < Pj) (hP : 0 < P)
    (hα : α < 1) :
    nk_MCavg w A α ((Pj / P) ^ (-ε) * Y) =
        nk_MCavg w A α Y * (Y / ((Pj / P) ^ (-ε) * Y)) ^ (-α / (1 - α)) ∧
      nk_MCavg w A α ((Pj / P) ^ (-ε) * Y) =
        nk_MCavg w A α Y * (Pj / P) ^ (ε * α / (α - 1)) := by
  have hq : 0 < Pj / P := div_pos hPj hP
  have hd : 0 < (Pj / P) ^ (-ε) * Y := mul_pos (Real.rpow_pos_of_pos hq _) hY
  have h1 := nk_MC_ratio (w := w) (α := α) hA hY hd
  refine ⟨h1, ?_⟩
  rw [h1]
  congr 1
  have e : Y / ((Pj / P) ^ (-ε) * Y) = (Pj / P) ^ ε := by
    rw [Real.rpow_neg hq.le]
    have := Real.rpow_pos_of_pos hq ε
    field_simp
  rw [e, ← Real.rpow_mul hq.le]
  congr 1
  have : (1 : ℝ) - α ≠ 0 := by linarith
  have : α - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Miao, p. 620: "firms with relatively high prices have relatively low real marginal costs":
for `0 < α < 1`, `ε > 0` and `MC > 0`, `P^j ↦ MC(P^j/P)^{εα/(α−1)}` is strictly decreasing. -/
theorem nk_MC_antitone {α ε P MC : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hP : 0 < P)
    (hMC : 0 < MC) {p1 p2 : ℝ} (hp1 : 0 < p1) (h12 : p1 < p2) :
    MC * (p2 / P) ^ (ε * α / (α - 1)) < MC * (p1 / P) ^ (ε * α / (α - 1)) := by
  have hexp : ε * α / (α - 1) < 0 := div_neg_of_pos_of_neg (mul_pos hε hα0) (by linarith)
  have := Real.rpow_lt_rpow_of_neg (div_pos hp1 hP) (div_lt_div_of_pos_right h12 hP) hexp
  exact mul_lt_mul_of_pos_left this hMC

/-- Miao, p. 621: the derivative of the period-`t + k` real profit of a firm that resets its
price to `x = P*` at `t`, `x·Y_{t+k|t}/P_{t+k} − TC(Y_{t+k|t})` with
`Y_{t+k|t} = (x/P_{t+k})^{−ε}Y_{t+k}` and `TC' = MC_{t+k|t}` at `Y_{t+k|t}`, is
`(1 − ε)x^{−ε−1}(Y_{t+k}/P_{t+k}^{1−ε})(x − μMC_{t+k|t}P_{t+k})`, `μ = ε/(ε − 1)`. -/
theorem nk_calvo_term_deriv {ε Pk Yk x MC : ℝ} {TC : ℝ → ℝ} (hε : 1 < ε) (hPk : 0 < Pk)
    (hx : 0 < x) (hTC : HasDerivAt TC MC ((x / Pk) ^ (-ε) * Yk)) :
    HasDerivAt (fun z => z * ((z / Pk) ^ (-ε) * Yk) / Pk - TC ((z / Pk) ^ (-ε) * Yk))
      ((1 - ε) * x ^ (-ε - 1) * (Yk / Pk ^ (1 - ε) * (x - ε / (ε - 1) * MC * Pk))) x := by
  have hq : 0 < x / Pk := div_pos hx hPk
  have hin : HasDerivAt (fun z => (z / Pk) ^ (-ε) * Yk)
      ((1 / Pk * (-ε * (x / Pk) ^ (-ε - 1))) * Yk) x := by
    have := ((hasDerivAt_id x).div_const Pk).rpow_const (p := -ε) (Or.inl hq.ne')
    exact (this.mul_const Yk).congr_deriv (by simp only [id]; ring)
  have hrev : HasDerivAt (fun z => z ^ (1 - ε) * (Pk ^ (ε - 1) * Yk))
      ((1 - ε) * x ^ (1 - ε - 1) * (Pk ^ (ε - 1) * Yk)) x :=
    (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).mul_const _
  have hev : (fun z => z * ((z / Pk) ^ (-ε) * Yk) / Pk) =ᶠ[nhds x]
      fun z => z ^ (1 - ε) * (Pk ^ (ε - 1) * Yk) := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    have hz' : (0 : ℝ) < z := hz
    rw [Real.div_rpow hz'.le hPk.le, Real.rpow_neg hz'.le, Real.rpow_neg hPk.le,
      Real.rpow_sub hz', Real.rpow_sub hPk, Real.rpow_one, Real.rpow_one]
    have := Real.rpow_pos_of_pos hz' ε
    have := Real.rpow_pos_of_pos hPk ε
    field_simp
  have h := (hrev.congr_of_eventuallyEq hev).sub (hTC.comp x hin)
  refine h.congr_deriv ?_
  have hε1 : ε - 1 ≠ 0 := by linarith
  rw [show (1 : ℝ) - ε - 1 = -ε by ring, Real.div_rpow hx.le hPk.le,
    show -ε - 1 = -ε + -1 by ring, Real.rpow_add hx, Real.rpow_add hPk, Real.rpow_neg_one,
    Real.rpow_neg_one, Real.rpow_sub hPk, Real.rpow_sub hPk, Real.rpow_one, Real.rpow_neg hx.le,
    Real.rpow_neg hPk.le]
  have := Real.rpow_pos_of_pos hx ε
  have := Real.rpow_pos_of_pos hPk ε
  field_simp
  ring

/-- Miao, p. 621: the first-order condition of the reset-price problem with finitely many
(date, state) terms `k ∈ K` and weights `w_k` (`θ^kβ^kΛ_{t+k}/Λ_t` times probabilities). The
objective `∑_k w_k(xY_{k|t}/P_k − TC_k(Y_{k|t}))` has derivative
`(1 − ε)x^{−ε−1}∑_k w_k(Y_k/P_k^{1−ε})(x − μMC_{k|t}P_k)`, and it vanishes iff the printed
condition `∑_k w_k(Y_k/P_k^{1−ε})(x − μMC_{k|t}P_k) = 0` holds. -/
theorem nk_calvo_foc {K : Type*} (S : Finset K) {ε x : ℝ} {wt Pk Yk MC : K → ℝ}
    {TC : K → ℝ → ℝ} (hε : 1 < ε) (hPk : ∀ k, 0 < Pk k) (hx : 0 < x)
    (hTC : ∀ k, HasDerivAt (TC k) (MC k) ((x / Pk k) ^ (-ε) * Yk k)) :
    HasDerivAt (fun z => ∑ k ∈ S, wt k *
        (z * ((z / Pk k) ^ (-ε) * Yk k) / Pk k - TC k ((z / Pk k) ^ (-ε) * Yk k)))
      ((1 - ε) * x ^ (-ε - 1) *
        ∑ k ∈ S, wt k * (Yk k / Pk k ^ (1 - ε) * (x - ε / (ε - 1) * MC k * Pk k))) x ∧
    ((1 - ε) * x ^ (-ε - 1) *
        ∑ k ∈ S, wt k * (Yk k / Pk k ^ (1 - ε) * (x - ε / (ε - 1) * MC k * Pk k)) = 0 ↔
      ∑ k ∈ S, wt k * (Yk k / Pk k ^ (1 - ε) * (x - ε / (ε - 1) * MC k * Pk k)) = 0) := by
  refine ⟨?_, ?_⟩
  · have h := HasDerivAt.fun_sum (u := S) fun k _ =>
      (nk_calvo_term_deriv hε (hPk k) hx (hTC k)).const_mul (wt k)
    convert h using 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · have hne : (1 - ε) * x ^ (-ε - 1) ≠ 0 :=
      mul_ne_zero (by linarith) (Real.rpow_pos_of_pos hx _).ne'
    exact ⟨fun h => (mul_eq_zero.1 h).resolve_left hne, fun h => by rw [h, mul_zero]⟩

/-- **(19.11)** (Miao, p. 621): the optimal reset price. If the first-order condition
`∑_k w_k(Y_k/P_k^{1−ε})(P* − μMC_{k|t}P_k) = 0` holds for a summable family of (date, state)
terms (`w_k = θ^kβ^kΛ_{t+k}` times probabilities) and `∑_k w_kP_k^{ε−1}Y_k ≠ 0`, then
`P* = (ε/(ε − 1)) ∑_k w_kP_k^εY_kMC_{k|t} / ∑_k w_kP_k^{ε−1}Y_k`. -/
theorem eq_19_11 {K : Type*} {ε x : ℝ} {wt Pk Yk MC : K → ℝ} (hPk : ∀ k, 0 < Pk k)
    (hs1 : Summable fun k => wt k * Pk k ^ (ε - 1) * Yk k)
    (hs2 : Summable fun k => wt k * Pk k ^ ε * Yk k * MC k)
    (hfoc : ∑' k, wt k * (Yk k / Pk k ^ (1 - ε) * (x - ε / (ε - 1) * MC k * Pk k)) = 0)
    (hden : ∑' k, wt k * Pk k ^ (ε - 1) * Yk k ≠ 0) :
    x = ε / (ε - 1) * (∑' k, wt k * Pk k ^ ε * Yk k * MC k) /
      ∑' k, wt k * Pk k ^ (ε - 1) * Yk k := by
  have hterm : ∀ k, wt k * (Yk k / Pk k ^ (1 - ε) * (x - ε / (ε - 1) * MC k * Pk k)) =
      x * (wt k * Pk k ^ (ε - 1) * Yk k) - ε / (ε - 1) * (wt k * Pk k ^ ε * Yk k * MC k) :=
    fun k => by
      have hp := hPk k
      rw [Real.rpow_sub hp, Real.rpow_sub hp, Real.rpow_one]
      have := Real.rpow_pos_of_pos hp ε
      field_simp
  simp only [hterm] at hfoc
  rw [Summable.tsum_sub (hs1.mul_left x) (hs2.mul_left _), tsum_mul_left, tsum_mul_left]
    at hfoc
  rw [eq_div_iff hden]
  linarith

/-- **(19.12)** (Miao, p. 621): the real marginal cost in `t + k` of a firm that reset its price
to `P*` in `t` is `MC_{t+k|t} = MC_{t+k}(P*/P_{t+k})^{εα/(α−1)}` (from (19.10), with
`Y_{t+k|t} = (P*/P_{t+k})^{−ε}Y_{t+k}`). -/
theorem eq_19_12 {w A α ε Yk Pstar Pk : ℝ} (hA : 0 < A) (hY : 0 < Yk) (hPs : 0 < Pstar)
    (hPk : 0 < Pk) (hα : α < 1) :
    nk_MCavg w A α ((Pstar / Pk) ^ (-ε) * Yk) =
      nk_MCavg w A α Yk * (Pstar / Pk) ^ (ε * α / (α - 1)) :=
  (eq_19_10 hA hY hPs hPk hα).2

end Miao.NewKeynesian

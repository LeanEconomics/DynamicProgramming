/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The reset price: the firm's Bellman equation, the first-order condition and (18.7)

AKMM, §18.3, pp. 539–540, and Appendix 18.A.1, p. 871. A firm with relative price `p` earns
`u′(C)(p − w/A) p^{−ε} Y` this period; if it cannot reset next period (probability `θ`) its
relative price becomes `p/(1 + π′)`. The envelope condition of the Bellman equation is
(App. 18.A.1)

  `V_p(p, S) = u′(C) Y [p^{−ε} − ε p^{−ε−1}(p − w/A)] + βθ E[V_p(p/(1 + π′), S′)/(1 + π′)]`,

and the reset price solves `V_p(p^R, S) = 0`. We work along a perfect-foresight aggregate path
(dates `n`, `λₙ = u′(Cₙ)Yₙ`, `mₙ = wₙ/Aₙ`, gross inflation `Πₙ = 1 + πₙ`).

* `rp_bracket_deriv`: the bracket is the derivative of `(q − m) q^{−ε}`.
* `rp_iterate`, `rp_series`: iterating the envelope condition `K` times, and in the limit,
  `V_p(p) = ∑_k (βθ)^k λ_{n+k} G_k [·](p G_k)` with `G_k = P_n/P_{n+k}`
  (`rpDefl`), provided the remainder vanishes; `rp_series_envelope`: the series solves the
  envelope condition.
* `rp_term_eq`, `rp_foc_rearranged`, `eq_18_7`: the first-order condition rearranges to
  `p^R ∑ (βθ)^k λ (P_{n+k}/P_n)^{ε−1} = μ ∑ (βθ)^k λ (P_{n+k}/P_n)^ε m`, so `p^R = p^N/p^D`
  with `p^N = μ m λ + θβ (1 + π′)^ε p^N′` and `p^D = λ + θβ (1 + π′)^{ε−1} p^D′`
  (`rp_pN_rec`, `rp_pD_rec`).

**Correction.** The book's combined condition omits the factor `G_k = ∏(1 + π_s)^{−1}` that the
envelope condition produces at each step (the derivative of `p_{t,τ}` with respect to `p^R_t`),
so its rearranged form carries `(P_τ/P_t)^ε` and `(P_τ/P_t)^{1+ε}`, and the recursions (18.7)
carry `(1 + π)^{1+ε}` and `(1 + π)^ε`. The correct exponents are `ε` and `ε − 1`. On a
constant-inflation path the two reset prices coincide iff inflation is zero
(`rp_constant_correct`, `rp_constant_printed`, `rp_printed_ne_iff`); the log-linearisation
(18.A.1) is unaffected, because both conditions agree to first order around zero inflation.
-/

namespace AKMM.NominalFrictions

open Filter Topology Finset

/-- AKMM, p. 539: the bracket `p^{−ε} − ε p^{−ε−1}(p − m)`, the marginal profit per unit of
demand. -/
noncomputable def rpBracket (ε m q : ℝ) : ℝ := q ^ (-ε) - ε * q ^ (-ε - 1) * (q - m)

/-- AKMM, p. 539: the cumulative deflator `G_k = P_n/P_{n+k} = ∏_{s=n+1}^{n+k} (1 + π_s)^{−1}`
along a path of gross inflation rates `Π`. -/
noncomputable def rpDefl (Pi : ℕ → ℝ) (n k : ℕ) : ℝ := ∏ j ∈ range k, (Pi (n + 1 + j))⁻¹

/-- AKMM, App. 18.A.1, p. 871: the `k`-th term of the iterated envelope condition,
`(βθ)^k λ_{n+k} G_k [·](p G_k)`. -/
noncomputable def rpTerm (β θ ε : ℝ) (lam mc Pi : ℕ → ℝ) (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (β * θ) ^ k * lam (n + k) * rpDefl Pi n k * rpBracket ε (mc (n + k)) (p * rpDefl Pi n k)

/-- AKMM, App. 18.A.1, p. 871: the envelope condition of the firm's Bellman equation along a
perfect-foresight path, for a family `Vp n p` of marginal values. -/
def RPEnvelope (β θ ε : ℝ) (lam mc Pi : ℕ → ℝ) (Vp : ℕ → ℝ → ℝ) : Prop :=
  ∀ n p, Vp n p = lam n * rpBracket ε (mc n) p + β * θ * (Vp (n + 1) (p / Pi (n + 1)) / Pi (n + 1))

/-- AKMM, p. 539: the bracket is the derivative of the per-unit-demand profit
`(q − m) q^{−ε}` at `q > 0`. -/
theorem rp_bracket_deriv {ε m q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun z => (z - m) * z ^ (-ε)) (rpBracket ε m q) q := by
  have h1 : HasDerivAt (fun z : ℝ => z - m) 1 q := by simpa using (hasDerivAt_id q).sub_const m
  have h2 := Real.hasDerivAt_rpow_const (p := -ε) (Or.inl hq.ne')
  have h := h1.mul h2
  convert h using 1
  unfold rpBracket
  ring

/-- `G_0 = 1`. -/
theorem rp_defl_zero (Pi : ℕ → ℝ) (n : ℕ) : rpDefl Pi n 0 = 1 := by simp [rpDefl]

/-- `G_{k+1} = G_k/(1 + π_{n+1+k})`. -/
theorem rp_defl_succ (Pi : ℕ → ℝ) (n k : ℕ) :
    rpDefl Pi n (k + 1) = rpDefl Pi n k / Pi (n + 1 + k) := by
  rw [rpDefl, rpDefl, prod_range_succ, div_eq_mul_inv]

/-- `G^{(n)}_{k+1} = G^{(n+1)}_k/(1 + π_{n+1})`. -/
theorem rp_defl_succ' (Pi : ℕ → ℝ) (n k : ℕ) :
    rpDefl Pi n (k + 1) = rpDefl Pi (n + 1) k / Pi (n + 1) := by
  rw [rpDefl, prod_range_succ', rpDefl, div_eq_mul_inv]
  simp only [add_zero]
  congr 1
  refine prod_congr rfl fun _ _ => ?_
  congr 2
  ring

/-- `G_k > 0` when inflation factors are positive. -/
theorem rp_defl_pos {Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s) (n k : ℕ) : 0 < rpDefl Pi n k :=
  prod_pos fun _ _ => inv_pos.2 (hPi _)

/-- **AKMM, App. 18.A.1, p. 871**: iterating the envelope condition `K` times,
`V_p(n, p) = ∑_{k<K} (βθ)^k λ_{n+k} G_k [·](p G_k) + (βθ)^K G_K V_p(n + K, p G_K)`. -/
theorem rp_iterate {β θ ε : ℝ} {lam mc Pi : ℕ → ℝ} {Vp : ℕ → ℝ → ℝ}
    (hV : RPEnvelope β θ ε lam mc Pi Vp) (n : ℕ) (p : ℝ) (K : ℕ) :
    Vp n p = ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k +
      (β * θ) ^ K * rpDefl Pi n K * Vp (n + K) (p * rpDefl Pi n K) := by
  induction K with
  | zero => simp [rp_defl_zero]
  | succ K ih =>
    rw [ih, hV (n + K) (p * rpDefl Pi n K), sum_range_succ, rp_defl_succ]
    have e1 : n + K + 1 = n + (K + 1) := by ring
    have e2 : n + 1 + K = n + K + 1 := by ring
    rw [e2, e1, add_assoc]
    congr 1
    unfold rpTerm
    rw [mul_div_assoc]
    ring

/-- **AKMM, App. 18.A.1, p. 871**: if the remainder `(βθ)^K G_K V_p(n + K, p G_K)` vanishes
(e.g. bounded marginal values with `βθ G_k` bounded below one), the envelope condition gives
`V_p(n, p) = ∑_{k ≥ 0} (βθ)^k λ_{n+k} G_k [·](p G_k)` as the limit of partial sums. -/
theorem rp_series {β θ ε : ℝ} {lam mc Pi : ℕ → ℝ} {Vp : ℕ → ℝ → ℝ}
    (hV : RPEnvelope β θ ε lam mc Pi Vp) (n : ℕ) (p : ℝ)
    (hrem : Tendsto (fun K => (β * θ) ^ K * rpDefl Pi n K * Vp (n + K) (p * rpDefl Pi n K))
      atTop (𝓝 0)) :
    Tendsto (fun K => ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k) atTop (𝓝 (Vp n p)) := by
  have h : ∀ K, ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k = Vp n p -
      (β * θ) ^ K * rpDefl Pi n K * Vp (n + K) (p * rpDefl Pi n K) := by
    intro K; rw [rp_iterate hV n p K]; ring
  simp_rw [h]
  simpa using (tendsto_const_nhds (x := Vp n p)).sub hrem

/-- AKMM, App. 18.A.1, p. 871: the first `k + 1` terms from date `n` are the date-`n` term and
`βθ/(1 + π_{n+1})` times the terms from date `n + 1` at the price `p/(1 + π_{n+1})`. -/
theorem rp_term_succ {β θ ε : ℝ} {lam mc Pi : ℕ → ℝ} (n : ℕ) (p : ℝ) (k : ℕ) :
    rpTerm β θ ε lam mc Pi n p (k + 1) =
      β * θ * (rpTerm β θ ε lam mc Pi (n + 1) (p / Pi (n + 1)) k / Pi (n + 1)) := by
  unfold rpTerm
  rw [rp_defl_succ']
  have e : n + (k + 1) = n + 1 + k := by ring
  rw [e, pow_succ]
  have e2 : p * (rpDefl Pi (n + 1) k / Pi (n + 1)) = p / Pi (n + 1) * rpDefl Pi (n + 1) k := by
    ring
  rw [e2]
  ring

/-- AKMM, App. 18.A.1, p. 871: the series `∑_k (βθ)^k λ G_k [·](p G_k)` (when summable at
every date and price) solves the envelope condition, so `RPEnvelope` has this concrete
instance. -/
theorem rp_series_envelope {β θ ε : ℝ} {lam mc Pi : ℕ → ℝ}
    (hs : ∀ n p, Summable (rpTerm β θ ε lam mc Pi n p)) :
    RPEnvelope β θ ε lam mc Pi (fun n p => ∑' k, rpTerm β θ ε lam mc Pi n p k) := by
  intro n p
  dsimp only
  rw [(hs n p).tsum_eq_zero_add]
  simp_rw [rp_term_succ]
  rw [tsum_mul_left, tsum_div_const]
  unfold rpTerm
  simp [rp_defl_zero]

/-- AKMM, pp. 539–540 (termwise rearrangement): with `μ = ε/(ε − 1)`,
`(βθ)^k λ G [·](p G) = (1 − ε) p^{−ε−1}(p · (βθ)^k λ G^{1−ε} − μ (βθ)^k λ m G^{−ε})`,
where `G^{1−ε} = (P_{n+k}/P_n)^{ε−1}` and `G^{−ε} = (P_{n+k}/P_n)^ε`. -/
theorem rp_term_eq {β θ ε : ℝ} (hε : 1 < ε) {lam mc Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s)
    (n : ℕ) {p : ℝ} (hp : 0 < p) (k : ℕ) :
    rpTerm β θ ε lam mc Pi n p k = (1 - ε) * p ^ (-ε - 1) *
      (p * ((β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε)) -
        ε / (ε - 1) * ((β * θ) ^ k * lam (n + k) * mc (n + k) * rpDefl Pi n k ^ (-ε))) := by
  have hG := rp_defl_pos hPi n k
  set G := rpDefl Pi n k
  have hε1 : ε - 1 ≠ 0 := by linarith
  unfold rpTerm rpBracket
  rw [Real.mul_rpow hp.le hG.le, Real.mul_rpow hp.le hG.le]
  have a1 : p ^ (-ε) = p ^ (-ε - 1) * p := by
    rw [← Real.rpow_add_one hp.ne']; ring_nf
  have a2 : G ^ (1 - ε) = G * G ^ (-ε) := by
    rw [show 1 - ε = -ε + 1 by ring, Real.rpow_add_one hG.ne']; ring
  have a3 : G ^ (-ε) = G ^ (-ε - 1) * G := by
    rw [← Real.rpow_add_one hG.ne']; ring_nf
  rw [a2, a1, a3]
  field_simp
  ring

/-- **AKMM, pp. 539–540 (corrected)**: if the first-order condition holds (the partial sums of
`rpTerm` tend to `V_p = 0`) and the two weighted sums converge to `D` and `N/μ`, then
`p^R D = μ (N/μ)`: `p^R ∑ (βθ)^k λ (P_{n+k}/P_n)^{ε−1} = μ ∑ (βθ)^k λ (P_{n+k}/P_n)^ε m`. -/
theorem rp_foc_rearranged {β θ ε : ℝ} (hε : 1 < ε) {lam mc Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s)
    (n : ℕ) {p D B : ℝ} (hp : 0 < p)
    (hfoc : Tendsto (fun K => ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k) atTop (𝓝 0))
    (hD : Tendsto (fun K => ∑ k ∈ range K, (β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε))
      atTop (𝓝 D))
    (hB : Tendsto (fun K => ∑ k ∈ range K,
      (β * θ) ^ k * lam (n + k) * mc (n + k) * rpDefl Pi n k ^ (-ε)) atTop (𝓝 B)) :
    p * D = ε / (ε - 1) * B := by
  have hsum : ∀ K, ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k = (1 - ε) * p ^ (-ε - 1) *
      (p * ∑ k ∈ range K, (β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε) -
        ε / (ε - 1) * ∑ k ∈ range K,
          (β * θ) ^ k * lam (n + k) * mc (n + k) * rpDefl Pi n k ^ (-ε)) := by
    intro K
    rw [mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun k _ => rp_term_eq hε hPi n hp k
  have hlim : Tendsto (fun K => ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k) atTop
      (𝓝 ((1 - ε) * p ^ (-ε - 1) * (p * D - ε / (ε - 1) * B))) := by
    simp_rw [hsum]
    exact ((hD.const_mul p).sub (hB.const_mul _)).const_mul _
  have h0 := tendsto_nhds_unique hlim hfoc
  have hc : (1 - ε) * p ^ (-ε - 1) ≠ 0 :=
    mul_ne_zero (by linarith) (Real.rpow_pos_of_pos hp _).ne'
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h hc
  · linarith

/-- AKMM, (18.7), p. 540: the denominator `p^D_n = ∑_k (βθ)^k λ_{n+k} (P_{n+k}/P_n)^{ε−1}`. -/
noncomputable def rpD (β θ ε : ℝ) (lam Pi : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' k, (β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε)

/-- AKMM, (18.7), p. 540: the numerator
`p^N_n = ∑_k (βθ)^k λ_{n+k} (P_{n+k}/P_n)^ε μ m_{n+k}`, `μ = ε/(ε − 1)`. -/
noncomputable def rpN (β θ ε : ℝ) (lam mc Pi : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' k, (β * θ) ^ k * lam (n + k) * (ε / (ε - 1) * mc (n + k)) * rpDefl Pi n k ^ (-ε)

/-- **AKMM, (18.7), p. 540 (corrected)**: under the first-order condition, with summable
weights and `p^D_n ≠ 0`, the reset price is `p^R_n = p^N_n/p^D_n`. -/
theorem eq_18_7 {β θ ε : ℝ} (hε : 1 < ε) {lam mc Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s)
    (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hfoc : Tendsto (fun K => ∑ k ∈ range K, rpTerm β θ ε lam mc Pi n p k) atTop (𝓝 0))
    (hsD : Summable fun k => (β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε))
    (hsN : Summable fun k => (β * θ) ^ k * lam (n + k) * mc (n + k) * rpDefl Pi n k ^ (-ε))
    (hD0 : rpD β θ ε lam Pi n ≠ 0) :
    p = rpN β θ ε lam mc Pi n / rpD β θ ε lam Pi n := by
  have h := rp_foc_rearranged hε hPi n hp hfoc hsD.hasSum.tendsto_sum_nat
    hsN.hasSum.tendsto_sum_nat
  have hN : rpN β θ ε lam mc Pi n = ε / (ε - 1) *
      ∑' k, (β * θ) ^ k * lam (n + k) * mc (n + k) * rpDefl Pi n k ^ (-ε) := by
    rw [rpN, ← tsum_mul_left]
    congr 1; funext k; ring
  rw [eq_div_iff hD0, hN, rpD]
  exact h

/-- **AKMM, (18.7), p. 540 (corrected)**:
`p^D_n = λ_n + θβ (1 + π_{n+1})^{ε−1} p^D_{n+1}` (the book prints the exponent `ε`). -/
theorem rp_pD_rec {β θ ε : ℝ} {lam Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s) (n : ℕ)
    (hs : Summable fun k => (β * θ) ^ k * lam (n + k) * rpDefl Pi n k ^ (1 - ε)) :
    rpD β θ ε lam Pi n = lam n + θ * β * Pi (n + 1) ^ (ε - 1) * rpD β θ ε lam Pi (n + 1) := by
  rw [rpD, hs.tsum_eq_zero_add, rpD, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero, rp_defl_zero, Real.one_rpow, mul_one]
  congr 1
  congr 1; funext k
  have hG := rp_defl_pos hPi (n + 1) k
  have hP := hPi (n + 1)
  rw [rp_defl_succ', Real.div_rpow hG.le hP.le]
  have e : n + (k + 1) = n + 1 + k := by ring
  rw [e, pow_succ]
  rw [div_eq_mul_inv, ← Real.rpow_neg hP.le, neg_sub]
  ring

/-- **AKMM, (18.7), p. 540 (corrected)**:
`p^N_n = μ m_n λ_n + θβ (1 + π_{n+1})^ε p^N_{n+1}` (the book prints the exponent `1 + ε`). -/
theorem rp_pN_rec {β θ ε : ℝ} {lam mc Pi : ℕ → ℝ} (hPi : ∀ s, 0 < Pi s) (n : ℕ)
    (hs : Summable fun k =>
      (β * θ) ^ k * lam (n + k) * (ε / (ε - 1) * mc (n + k)) * rpDefl Pi n k ^ (-ε)) :
    rpN β θ ε lam mc Pi n = ε / (ε - 1) * mc n * lam n +
      θ * β * Pi (n + 1) ^ ε * rpN β θ ε lam mc Pi (n + 1) := by
  rw [rpN, hs.tsum_eq_zero_add, rpN, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero, rp_defl_zero, Real.one_rpow, mul_one]
  rw [mul_comm (lam n)]
  congr 1
  congr 1; funext k
  have hG := rp_defl_pos hPi (n + 1) k
  have hP := hPi (n + 1)
  rw [rp_defl_succ', Real.div_rpow hG.le hP.le]
  have e : n + (k + 1) = n + 1 + k := by ring
  rw [e, pow_succ]
  rw [Real.rpow_neg hP.le ε, div_inv_eq_mul]
  ring

/-- On a constant-inflation path `Π > 0`, `G_k = Π^{−k}` and `G_k^r = (Π^{−r})^k`. -/
theorem rp_defl_const_rpow {Pc : ℝ} (hP : 0 < Pc) (n k : ℕ) (r : ℝ) :
    rpDefl (fun _ => Pc) n k ^ r = (Pc ^ (-r)) ^ k := by
  have e : rpDefl (fun _ => Pc) n k = (Pc⁻¹) ^ k := by simp [rpDefl]
  rw [e, ← Real.rpow_pow_comm (inv_pos.2 hP).le, Real.inv_rpow hP.le, Real.rpow_neg hP.le]

/-- **AKMM, (18.7), p. 540, constant inflation (corrected)**: with `λ ≡ 1`, `m ≡ m`, gross
inflation `Π`, `a = βθ` and `aΠ^ε < 1`, the correct weights give
`p^R = μ m (1 − aΠ^{ε−1})/(1 − aΠ^ε)`. -/
theorem rp_constant_correct {β θ ε m Pc : ℝ} (hε : 1 < ε) (hP : 0 < Pc) (ha : 0 ≤ β * θ)
    (h1 : β * θ * Pc ^ (ε - 1) < 1) (h2 : β * θ * Pc ^ ε < 1) :
    rpN β θ ε (fun _ => 1) (fun _ => m) (fun _ => Pc) 0 / rpD β θ ε (fun _ => 1) (fun _ => Pc) 0
      = ε / (ε - 1) * m * (1 - β * θ * Pc ^ (ε - 1)) / (1 - β * θ * Pc ^ ε) := by
  have hq1 : 0 ≤ β * θ * Pc ^ (ε - 1) := mul_nonneg ha (Real.rpow_pos_of_pos hP _).le
  have hq2 : 0 ≤ β * θ * Pc ^ ε := mul_nonneg ha (Real.rpow_pos_of_pos hP _).le
  have hD : rpD β θ ε (fun _ => 1) (fun _ => Pc) 0 = (1 - β * θ * Pc ^ (ε - 1))⁻¹ := by
    rw [rpD]
    simp_rw [rp_defl_const_rpow hP, mul_one, neg_sub, ← mul_pow]
    exact tsum_geometric_of_lt_one hq1 h1
  have hN : rpN β θ ε (fun _ => 1) (fun _ => m) (fun _ => Pc) 0 =
      ε / (ε - 1) * m * (1 - β * θ * Pc ^ ε)⁻¹ := by
    rw [rpN]
    simp only [rp_defl_const_rpow hP, neg_neg, mul_one]
    have e : ∀ k : ℕ, (β * θ) ^ k * (ε / (ε - 1) * m) * (Pc ^ ε) ^ k =
        ε / (ε - 1) * m * (β * θ * Pc ^ ε) ^ k := by intro k; rw [mul_pow]; ring
    simp_rw [e]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq2 h2]
  rw [hD, hN]
  have h1' : 1 - β * θ * Pc ^ (ε - 1) ≠ 0 := by linarith
  have h2' : 1 - β * θ * Pc ^ ε ≠ 0 := by linarith
  field_simp

/-- **AKMM, (18.7), p. 540, as printed, constant inflation**: the printed recursions
`p^N = μ m + θβ Π^{1+ε} p^N`, `p^D = 1 + θβ Π^ε p^D` have the constant solutions
`p^N = μm/(1 − aΠ^{1+ε})`, `p^D = 1/(1 − aΠ^ε)`, so the printed reset price is
`μ m (1 − aΠ^ε)/(1 − aΠ^{1+ε})`. -/
theorem rp_constant_printed {β θ ε m Pc pN pD : ℝ} (h1 : β * θ * Pc ^ (1 + ε) ≠ 1)
    (h2 : β * θ * Pc ^ ε ≠ 1)
    (hN : pN = ε / (ε - 1) * m + θ * β * Pc ^ (1 + ε) * pN)
    (hD : pD = 1 + θ * β * Pc ^ ε * pD) :
    pN / pD = ε / (ε - 1) * m * (1 - β * θ * Pc ^ ε) / (1 - β * θ * Pc ^ (1 + ε)) := by
  have h1' : 1 - β * θ * Pc ^ (1 + ε) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have h2' : 1 - β * θ * Pc ^ ε ≠ 0 := sub_ne_zero.2 (Ne.symm h2)
  have eN : pN = ε / (ε - 1) * m / (1 - β * θ * Pc ^ (1 + ε)) := by
    rw [eq_div_iff h1']; linear_combination hN
  have eD : pD = 1 / (1 - β * θ * Pc ^ ε) := by
    rw [eq_div_iff h2']; linear_combination hD
  rw [eN, eD]
  field_simp

/-- **AKMM, (18.7), p. 540 (correction)**: on a constant-inflation path with `βθ > 0`,
`m ≠ 0`, the printed and the correct reset prices coincide iff inflation is zero (`Π = 1`). -/
theorem rp_printed_ne_iff {β θ ε m Pc : ℝ} (hε : 1 < ε) (hP : 0 < Pc) (ha : 0 < β * θ)
    (hm : m ≠ 0) (h1 : β * θ * Pc ^ (1 + ε) < 1) (h2 : β * θ * Pc ^ ε < 1) :
    ε / (ε - 1) * m * (1 - β * θ * Pc ^ (ε - 1)) / (1 - β * θ * Pc ^ ε) =
        ε / (ε - 1) * m * (1 - β * θ * Pc ^ ε) / (1 - β * θ * Pc ^ (1 + ε)) ↔ Pc = 1 := by
  have h1' : 1 - β * θ * Pc ^ (1 + ε) ≠ 0 := by linarith
  have h2' : 1 - β * θ * Pc ^ ε ≠ 0 := by linarith
  have hμ : ε / (ε - 1) ≠ 0 := div_ne_zero (by linarith) (by linarith)
  have eA : Pc ^ ε = Pc ^ (ε - 1) * Pc := by
    rw [← Real.rpow_add_one hP.ne']; ring_nf
  have eB : Pc ^ (1 + ε) = Pc ^ (ε - 1) * Pc ^ 2 := by
    rw [show 1 + ε = (ε - 1) + 2 by ring, Real.rpow_add hP]
    norm_cast
  have hx : 0 < Pc ^ (ε - 1) := Real.rpow_pos_of_pos hP _
  rw [div_eq_div_iff h2' h1']
  constructor
  · intro h
    have key : ε / (ε - 1) * m * (β * θ * Pc ^ (ε - 1) * (Pc - 1) ^ 2) = 0 := by
      rw [eA, eB] at h; linear_combination -h
    have : (Pc - 1) ^ 2 = 0 := by
      rcases mul_eq_zero.1 key with h | h
      · exact absurd h (mul_ne_zero hμ hm)
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h (mul_pos ha hx).ne'
        · exact h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · rintro rfl
    simp

end AKMM.NominalFrictions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.SequenceLemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Renewal sequences (MT §2.4.1, §8.1, §13.2)

Meyn and Tweedie, §13.2.1, p. 320 (and the renewal equation (8.12) used on p. 367). For an
increment law `p` on `{1, 2, …}` the renewal sequence is `u = ∑ₖ p^{∗k}`; it is the probability
of a renewal at time `n` for the undelayed renewal process.

**Increment laws and convolution powers.**
* `IsIncrementLaw p`: `p ≥ 0`, `p(0) = 0` and `∑ p = 1` (a proper law on `ℤ₊` with no mass at 0).
* `deltaSeq` (the unit mass `δ₀`), `realConv_deltaSeq_left/right`.
* `realConvPow p k = p^{∗k}`, with `realConvPow_zero`, `realConvPow_succ`
  (`p^{∗(k+1)} = p ∗ p^{∗k}`) and
  `realConvPow_eq_zero_of_lt` (`p^{∗k}(n) = 0` for `n < k`, since `p(0) = 0`).

**The renewal sequence.**
* `realRenewalSeq p = u`, defined as the coefficients of `(1 − P)⁻¹`, `P = ∑ p(n) Xⁿ`.
* `realRenewalSeq_eq_sum_realConvPow`: `u(n) = ∑_{k ≤ n} p^{∗k}(n) = ∑_{k ≥ 0} p^{∗k}(n)`
  (MT p. 320).
* The renewal equation: `realRenewalSeq_zero` (`u(0) = 1`), `realRenewalSeq_eq` (`u = δ₀ + p ∗ u`),
  `realRenewalSeq_succ` (`u(n) = ∑_{j=1}^n p(j) u(n − j)` for `n ≥ 1`), and the power-series forms
  `one_sub_mul_mk_realRenewalSeq`, `mk_realRenewalSeq_mul_one_sub` (`(1 − P) U = 1`).
* `realRenewalSeq_nonneg`, `realRenewalSeq_le_one`: `0 ≤ u(n) ≤ 1`.
* `delayedRenewal a p = a ∗ u`, the delayed renewal sequence (MT p. 320).

**Tails and the mean.**
* `renewalTail p n = ∑_{j > n} p(j) = 1 − ∑_{j ≤ n} p(j)` (`renewalTail_eq_tsum`), nonnegative, at
  most `1`, equal to `1` at `0`, tending to `0`; `mk_renewalTail`: its power series is
  `(1 − P)/(1 − X)`.
* `realConv_renewalTail_renewal`: the key identity `∑_{i=0}^n (∑_{j>i} p(j)) u(n − i) = 1` behind
  (13.35).
* `incrMean p = m_p = ∑ n p(n)` (13.28); `sum_range_renewalTail` (`∑_{i<N} tail(i) =
  ∑_{j ≤ N} j p(j) + N tail(N)`), `hasSum_renewalTail` (`∑ tail = m_p` when `m_p < ∞`),
  `tendsto_sum_renewalTail_atTop` (the partial sums diverge when `m_p = ∞`),
  `summable_renewalTail_iff`, `one_le_incrMean`.

**Generating functions** (on the complex unit disc).
* `genFunC a z = ∑ a(n) zⁿ`; `genFunC_realConv` (the generating function of a convolution is the
  product), `genFunC_deltaSeq`.
* `renewal_genFunC`: `U(z) = 1/(1 − P(z))` for `|z| < 1` (the renewal equation (8.12)), with
  `one_sub_genFunC_ne_zero`; `delayedRenewal_genFunC`: `(a ∗ u)ˆ(z) = A(z)/(1 − P(z))`.

**Corrections.** None.
-/

namespace MeynTweedie.VUniformErgodicity

open Finset Filter Topology

/-! ### Increment laws and convolution powers -/

/-- An **increment law** (MT p. 320, §2.4.1): a probability `p` on `ℤ₊` with `p(0) = 0`. -/
structure IsIncrementLaw (p : ℕ → ℝ) : Prop where
  /-- The law is nonnegative. -/
  nonneg : ∀ n, 0 ≤ p n
  /-- There is no mass at `0`. -/
  zero : p 0 = 0
  /-- The total mass is `1`. -/
  hasSum : HasSum p 1

/-- The unit mass at `0`, `δ₀(n) = 1` if `n = 0` and `0` otherwise. -/
def deltaSeq (n : ℕ) : ℝ := if n = 0 then 1 else 0

/-- The power series of `δ₀` is `1`. -/
theorem mk_deltaSeq : PowerSeries.mk deltaSeq = 1 := by
  ext n
  simp [deltaSeq, PowerSeries.coeff_one]

/-- `δ₀ ∗ a = a`. -/
theorem realConv_deltaSeq_left (a : ℕ → ℝ) : realConv deltaSeq a = a := by
  funext n
  rw [realConv_eq_coeff, mk_deltaSeq, one_mul, PowerSeries.coeff_mk]

/-- `a ∗ δ₀ = a`. -/
theorem realConv_deltaSeq_right (a : ℕ → ℝ) : realConv a deltaSeq = a := by
  rw [realConv_comm, realConv_deltaSeq_left]

/-- The `k`-fold convolution power `p^{∗k}` (with `p^{∗0} = δ₀`), MT p. 320. -/
noncomputable def realConvPow (p : ℕ → ℝ) (k n : ℕ) : ℝ :=
  PowerSeries.coeff n (PowerSeries.mk p ^ k)

/-- `p^{∗0} = δ₀`. -/
theorem realConvPow_zero (p : ℕ → ℝ) : realConvPow p 0 = deltaSeq := by
  funext n
  simp [realConvPow, deltaSeq, PowerSeries.coeff_one]

/-- `p^{∗(k+1)} = p ∗ p^{∗k}`. -/
theorem realConvPow_succ (p : ℕ → ℝ) (k : ℕ) :
    realConvPow p (k + 1) = realConv p (realConvPow p k) := by
  funext n
  have h : PowerSeries.mk (realConvPow p k) = PowerSeries.mk p ^ k := by
    ext m; simp [realConvPow]
  rw [realConv_eq_coeff, h, realConvPow, pow_succ, mul_comm]

/-- If `p(0) = 0` then the power series `P = ∑ p(n) Xⁿ` is divisible by `X`. -/
theorem X_dvd_mk_of_zero {p : ℕ → ℝ} (hp0 : p 0 = 0) : PowerSeries.X ∣ PowerSeries.mk p := by
  rw [PowerSeries.X_dvd_iff, PowerSeries.constantCoeff_mk, hp0]

/-- For `p(0) = 0`, `p^{∗k}(n) = 0` when `n < k`: `k` renewals take at least `k` time steps. -/
theorem realConvPow_eq_zero_of_lt {p : ℕ → ℝ} (hp0 : p 0 = 0) {k n : ℕ} (h : n < k) :
    realConvPow p k n = 0 := by
  obtain ⟨Q, hQ⟩ := X_dvd_mk_of_zero hp0
  rw [realConvPow, hQ, mul_pow, PowerSeries.coeff_X_pow_mul']
  simp [not_le.2 h]

/-! ### The renewal sequence -/

/-- The **renewal sequence** `u = ∑ₖ p^{∗k}` of an increment law (MT p. 320), defined as the
coefficient sequence of `(1 − P)⁻¹` where `P = ∑ p(n) Xⁿ`. -/
noncomputable def realRenewalSeq (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  PowerSeries.coeff n (1 - PowerSeries.mk p)⁻¹

/-- The power series of the renewal sequence is `(1 − P)⁻¹`. -/
theorem mk_realRenewalSeq (p : ℕ → ℝ) :
    PowerSeries.mk (realRenewalSeq p) = (1 - PowerSeries.mk p)⁻¹ := by
  ext n
  simp [realRenewalSeq]

/-- **The renewal equation in power-series form**: `(1 − P) U = 1` when `p(0) = 0`. -/
theorem one_sub_mul_mk_realRenewalSeq {p : ℕ → ℝ} (hp0 : p 0 = 0) :
    (1 - PowerSeries.mk p) * PowerSeries.mk (realRenewalSeq p) = 1 := by
  rw [mk_realRenewalSeq]
  refine PowerSeries.mul_inv_cancel _ ?_
  simp [hp0]

/-- `U (1 − P) = 1` when `p(0) = 0`. -/
theorem mk_realRenewalSeq_mul_one_sub {p : ℕ → ℝ} (hp0 : p 0 = 0) :
    PowerSeries.mk (realRenewalSeq p) * (1 - PowerSeries.mk p) = 1 := by
  rw [mul_comm, one_sub_mul_mk_realRenewalSeq hp0]

/-- **The renewal equation** `u = δ₀ + p ∗ u` (MT (8.12)). -/
theorem realRenewalSeq_eq {p : ℕ → ℝ} (hp0 : p 0 = 0) (n : ℕ) :
    realRenewalSeq p n = deltaSeq n + realConv p (realRenewalSeq p) n := by
  have h : PowerSeries.mk (realRenewalSeq p) =
      PowerSeries.mk deltaSeq + PowerSeries.mk p * PowerSeries.mk (realRenewalSeq p) := by
    rw [mk_deltaSeq]
    linear_combination one_sub_mul_mk_realRenewalSeq hp0
  have := congrArg (PowerSeries.coeff n) h
  rwa [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← realConv_eq_coeff] at this

/-- `u(0) = 1` (MT p. 320). -/
theorem realRenewalSeq_zero {p : ℕ → ℝ} (hp0 : p 0 = 0) : realRenewalSeq p 0 = 1 := by
  rw [realRenewalSeq_eq hp0, realConv_eq_sum_range]
  simp [deltaSeq, hp0]

/-- **The renewal equation** for `n ≥ 1`: `u(n + 1) = ∑_{j=1}^{n+1} p(j) u(n + 1 − j)`. -/
theorem realRenewalSeq_succ {p : ℕ → ℝ} (hp0 : p 0 = 0) (n : ℕ) :
    realRenewalSeq p (n + 1) = ∑ j ∈ range (n + 1), p (j + 1) * realRenewalSeq p (n - j) := by
  rw [realRenewalSeq_eq hp0, realConv_eq_sum_range, sum_range_succ']
  simp [deltaSeq, hp0]

/-- For `n ≥ 1`, `u(n) = (p ∗ u)(n)`. -/
theorem realRenewalSeq_eq_realConv_of_pos {p : ℕ → ℝ} (hp0 : p 0 = 0) {n : ℕ} (hn : 0 < n) :
    realRenewalSeq p n = realConv p (realRenewalSeq p) n := by
  rw [realRenewalSeq_eq hp0]
  simp [deltaSeq, hn.ne']

/-- **`u = ∑ₖ p^{∗k}`** (MT p. 320): `u(n) = ∑_{k=0}^n p^{∗k}(n)`; the terms with `k > n`
vanish by `realConvPow_eq_zero_of_lt`. -/
theorem realRenewalSeq_eq_sum_realConvPow {p : ℕ → ℝ} (hp0 : p 0 = 0) (n : ℕ) :
    realRenewalSeq p n = ∑ k ∈ range (n + 1), realConvPow p k n := by
  set P := PowerSeries.mk p
  set U := PowerSeries.mk (realRenewalSeq p)
  have hgeom : (∑ k ∈ range (n + 1), P ^ k) = U - P ^ (n + 1) * U := by
    have h1 := geom_sum_mul P (n + 1)
    have h2 := mk_realRenewalSeq_mul_one_sub hp0
    calc (∑ k ∈ range (n + 1), P ^ k)
        = (∑ k ∈ range (n + 1), P ^ k) * (U * (1 - P)) := by rw [h2, mul_one]
      _ = U - P ^ (n + 1) * U := by linear_combination (-U) * h1
  have hzero : PowerSeries.coeff n (P ^ (n + 1) * U) = 0 := by
    obtain ⟨Q, hQ⟩ := X_dvd_mk_of_zero hp0
    have hP : P = PowerSeries.X * Q := hQ
    rw [hP, mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul']
    simp
  have := congrArg (PowerSeries.coeff n) hgeom
  rw [map_sum, map_sub, hzero, sub_zero, PowerSeries.coeff_mk] at this
  rw [← this]
  rfl

/-- The renewal sequence is nonnegative. -/
theorem realRenewalSeq_nonneg {p : ℕ → ℝ} (hp : IsIncrementLaw p) (n : ℕ) :
    0 ≤ realRenewalSeq p n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [realRenewalSeq_zero hp.zero]
    · rw [realRenewalSeq_succ hp.zero]
      exact sum_nonneg fun j _ => mul_nonneg (hp.nonneg _) (ih _ (by omega))

/-- `∑_{j ≤ n} p(j) ≤ 1` for an increment law. -/
theorem sum_range_le_one {p : ℕ → ℝ} (hp : IsIncrementLaw p) (n : ℕ) :
    ∑ j ∈ range n, p j ≤ 1 :=
  sum_le_hasSum _ (fun i _ => hp.nonneg i) hp.hasSum

/-- The renewal sequence is at most `1` (it is a probability). -/
theorem realRenewalSeq_le_one {p : ℕ → ℝ} (hp : IsIncrementLaw p) (n : ℕ) :
    realRenewalSeq p n ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [realRenewalSeq_zero hp.zero]
    · rw [realRenewalSeq_succ hp.zero]
      calc ∑ j ∈ range (n + 1), p (j + 1) * realRenewalSeq p (n - j)
          ≤ ∑ j ∈ range (n + 1), p (j + 1) :=
            sum_le_sum fun j _ => mul_le_of_le_one_right (hp.nonneg _) (ih _ (by omega))
        _ = ∑ k ∈ range (n + 2), p k := by rw [sum_range_succ' p (n + 1), hp.zero, add_zero]
        _ ≤ 1 := sum_range_le_one hp _

/-- The **delayed renewal sequence** `a ∗ u` for a delay law `a` (MT p. 320): the probability of a
renewal at time `n` when the first renewal has law `a`. -/
noncomputable def delayedRenewal (a p : ℕ → ℝ) : ℕ → ℝ := realConv a (realRenewalSeq p)

/-! ### Tails and the mean of the increment law -/

/-- The **tail** `∑_{j > n} p(j) = 1 − ∑_{j ≤ n} p(j)` of the increment law (MT (13.34)). -/
def renewalTail (p : ℕ → ℝ) (n : ℕ) : ℝ := 1 - ∑ j ∈ range (n + 1), p j

/-- `tail(n + 1) = tail(n) − p(n + 1)`. -/
theorem renewalTail_succ (p : ℕ → ℝ) (n : ℕ) :
    renewalTail p (n + 1) = renewalTail p n - p (n + 1) := by
  simp only [renewalTail, sum_range_succ _ (n + 1)]
  ring

/-- `tail(0) = 1` when `p(0) = 0`. -/
theorem renewalTail_zero {p : ℕ → ℝ} (hp0 : p 0 = 0) : renewalTail p 0 = 1 := by
  simp [renewalTail, hp0]

/-- The tails are nonnegative. -/
theorem renewalTail_nonneg {p : ℕ → ℝ} (hp : IsIncrementLaw p) (n : ℕ) : 0 ≤ renewalTail p n :=
  sub_nonneg.2 (sum_range_le_one hp _)

/-- The tails are at most `1`. -/
theorem renewalTail_le_one {p : ℕ → ℝ} (hp : IsIncrementLaw p) (n : ℕ) : renewalTail p n ≤ 1 :=
  sub_le_self _ (sum_nonneg fun i _ => hp.nonneg i)

/-- `tail(n) = ∑_{j ≥ 0} p(j + n + 1)`. -/
theorem renewalTail_eq_tsum {p : ℕ → ℝ} (hp : IsIncrementLaw p) (n : ℕ) :
    renewalTail p n = ∑' j, p (j + (n + 1)) := by
  have h := hp.hasSum.summable.sum_add_tsum_nat_add (n + 1)
  rw [hp.hasSum.tsum_eq] at h
  rw [renewalTail]
  linarith

/-- The tails tend to `0`. -/
theorem tendsto_renewalTail {p : ℕ → ℝ} (hp : IsIncrementLaw p) :
    Tendsto (renewalTail p) atTop (𝓝 0) := by
  have h := (hp.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  rw [sub_self] at h2
  exact h2

/-- The power series of the tails is `(1 − P) · (1 − X)⁻¹`, i.e. `tail = (δ₀ − p) ∗ 1`. -/
theorem mk_renewalTail (p : ℕ → ℝ) :
    PowerSeries.mk (renewalTail p) = (1 - PowerSeries.mk p) * PowerSeries.mk (fun _ => 1) := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (1 - PowerSeries.mk p) *
        PowerSeries.coeff j (PowerSeries.mk (fun _ => (1 : ℝ))))]
  simp [renewalTail, PowerSeries.coeff_one, sum_sub_distrib]

/-- **The tail–renewal identity** `∑_{i=0}^n tail(i) u(n − i) = 1` (MT (13.35), with the
normalisation `m_p` removed): in power series, `(1 − P)/(1 − X) · (1 − P)⁻¹ = 1/(1 − X)`. -/
theorem realConv_renewalTail_renewal {p : ℕ → ℝ} (hp0 : p 0 = 0) (n : ℕ) :
    realConv (renewalTail p) (realRenewalSeq p) n = 1 := by
  rw [realConv_eq_coeff, mk_renewalTail, mul_comm (1 - PowerSeries.mk p), mul_assoc,
    one_sub_mul_mk_realRenewalSeq hp0, mul_one, PowerSeries.coeff_mk]

/-- The **mean** `m_p = ∑ n p(n)` of the increment law (MT (13.28)). When the series diverges
(`m_p = ∞` in the book) the Lean `tsum` is `0`. -/
noncomputable def incrMean (p : ℕ → ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) * p n

/-- `∑_{i < N} tail(i) = ∑_{j ≤ N} j p(j) + N tail(N)`. -/
theorem sum_range_renewalTail (p : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range N, renewalTail p i = ∑ j ∈ range (N + 1), (j : ℝ) * p j + N * renewalTail p N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun j => (j : ℝ) * p j) (N + 1), renewalTail_succ]
    push_cast
    ring

/-- The mean of an increment law is at least `1` (all mass sits on `n ≥ 1`). -/
theorem one_le_incrMean {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hm : Summable fun n : ℕ => (n : ℝ) * p n) : 1 ≤ incrMean p := by
  rw [← hp.hasSum.tsum_eq]
  refine Summable.tsum_le_tsum (fun n => ?_) hp.hasSum.summable hm
  rcases n with _ | n
  · simp [hp.zero]
  · have := hp.nonneg (n + 1)
    push_cast
    nlinarith

/-- **`∑ tail = m_p`** when the mean is finite. -/
theorem hasSum_renewalTail {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hm : Summable fun n : ℕ => (n : ℝ) * p n) : HasSum (renewalTail p) (incrMean p) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (renewalTail_nonneg hp)]
  simp_rw [sum_range_renewalTail]
  have hA : Tendsto (fun N => ∑ j ∈ range (N + 1), (j : ℝ) * p j) atTop (𝓝 (incrMean p)) :=
    (hm.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hB : Tendsto (fun N : ℕ => (N : ℝ) * renewalTail p N) atTop (𝓝 0) := by
    have hup : Tendsto (fun N => incrMean p - ∑ j ∈ range (N + 1), (j : ℝ) * p j) atTop
        (𝓝 0) := by
      have := (tendsto_const_nhds (x := incrMean p)).sub hA
      rwa [sub_self] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun N => mul_nonneg (Nat.cast_nonneg N) (renewalTail_nonneg hp N)) (fun N => ?_)
    have hsplit := hm.sum_add_tsum_nat_add (N + 1)
    have hshift := (summable_nat_add_iff (N + 1)).2 hm
    have hle : (N : ℝ) * renewalTail p N ≤
        ∑' j, ((j + (N + 1) : ℕ) : ℝ) * p (j + (N + 1)) := by
      rw [renewalTail_eq_tsum hp, ← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun j => ?_)
        (((summable_nat_add_iff (N + 1)).2 hp.hasSum.summable).mul_left _) hshift
      refine mul_le_mul_of_nonneg_right ?_ (hp.nonneg _)
      push_cast
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    simp only [incrMean] at hsplit ⊢
    linarith
  simpa using hA.add hB

/-- When the mean is infinite, the partial sums of the tails diverge. -/
theorem tendsto_sum_renewalTail_atTop {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hm : ¬ Summable fun n : ℕ => (n : ℝ) * p n) :
    Tendsto (fun N => ∑ i ∈ range N, renewalTail p i) atTop atTop := by
  have h := ((not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => mul_nonneg (Nat.cast_nonneg n) (hp.nonneg n))).1 hm).comp (tendsto_add_atTop_nat 1)
  refine tendsto_atTop_mono (fun N => ?_) h
  rw [sum_range_renewalTail]
  have := mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (renewalTail_nonneg hp N)
  simp only [Function.comp_apply]
  linarith

/-- The tails are summable exactly when the mean is finite. -/
theorem summable_renewalTail_iff {p : ℕ → ℝ} (hp : IsIncrementLaw p) :
    Summable (renewalTail p) ↔ Summable fun n : ℕ => (n : ℝ) * p n := by
  refine ⟨fun h => ?_, fun hm => (hasSum_renewalTail hp hm).summable⟩
  by_contra hm
  have h1 := tendsto_sum_renewalTail_atTop hp hm
  have h2 := h.hasSum.tendsto_sum_nat
  exact not_tendsto_atTop_of_tendsto_nhds h2 h1

/-! ### Generating functions -/

/-- The **generating function** `A(z) = ∑ a(n) zⁿ` of a real sequence, at a complex point. -/
noncomputable def genFunC (a : ℕ → ℝ) (z : ℂ) : ℂ := ∑' n, (a n : ℂ) * z ^ n

/-- The norm of a term of a generating function. -/
theorem norm_genFunC_term (a : ℕ → ℝ) (z : ℂ) (n : ℕ) :
    ‖(a n : ℂ) * z ^ n‖ = |a n| * ‖z‖ ^ n := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- A bounded sequence has an absolutely convergent generating function inside the unit disc. -/
theorem summable_abs_mul_pow_of_bounded {a : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |a n| ≤ C) {z : ℂ}
    (hz : ‖z‖ < 1) : Summable fun n => |a n| * ‖z‖ ^ n := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) n))
    (fun n => mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (norm_nonneg _) n))
    ((summable_geometric_of_lt_one (norm_nonneg _) hz).mul_left C)

/-- **The generating function of a convolution is the product** of the generating functions,
where both series converge absolutely. -/
theorem genFunC_realConv {a b : ℕ → ℝ} {z : ℂ} (ha : Summable fun n => |a n| * ‖z‖ ^ n)
    (hb : Summable fun n => |b n| * ‖z‖ ^ n) :
    genFunC (realConv a b) z = genFunC a z * genFunC b z := by
  have hna : Summable fun n => ‖(a n : ℂ) * z ^ n‖ := by simpa [norm_genFunC_term] using ha
  have hnb : Summable fun n => ‖(b n : ℂ) * z ^ n‖ := by simpa [norm_genFunC_term] using hb
  simp only [genFunC]
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]
  refine tsum_congr fun n => ?_
  rw [realConv, Complex.ofReal_sum, sum_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [mem_antidiagonal] at hx
  rw [← hx, pow_add]
  push_cast
  ring

/-- The generating function of `δ₀` is `1`. -/
theorem genFunC_deltaSeq (z : ℂ) : genFunC deltaSeq z = 1 := by
  rw [genFunC, tsum_eq_single 0 (fun n hn => by simp [deltaSeq, hn])]
  simp [deltaSeq]

/-- The generating function of an increment law converges absolutely on the closed unit disc. -/
theorem summable_incr_genFunC {p : ℕ → ℝ} (hp : IsIncrementLaw p) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable fun n => |p n| * ‖z‖ ^ n := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) n)) (fun n => ?_)
    hp.hasSum.summable
  rw [abs_of_nonneg (hp.nonneg n)]
  exact mul_le_of_le_one_right (hp.nonneg n) (pow_le_one₀ (norm_nonneg _) hz)

/-- The renewal sequence has an absolutely convergent generating function on the unit disc. -/
theorem summable_renewal_genFunC {p : ℕ → ℝ} (hp : IsIncrementLaw p) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n => |realRenewalSeq p n| * ‖z‖ ^ n :=
  summable_abs_mul_pow_of_bounded (fun n => by
    rw [abs_of_nonneg (realRenewalSeq_nonneg hp n)]; exact realRenewalSeq_le_one hp n) hz

/-- `U(z) (1 − P(z)) = 1` on the open unit disc. -/
theorem renewal_genFunC_mul {p : ℕ → ℝ} (hp : IsIncrementLaw p) {z : ℂ} (hz : ‖z‖ < 1) :
    genFunC (realRenewalSeq p) z * (1 - genFunC p z) = 1 := by
  have hu := summable_renewal_genFunC hp hz
  have hpz := summable_incr_genFunC hp hz.le
  have hconv : realConv (realRenewalSeq p) p = realRenewalSeq p - deltaSeq := by
    funext n
    rw [realConv_comm, Pi.sub_apply, realRenewalSeq_eq hp.zero n]
    ring
  have hsum : Summable fun n => |realConv (realRenewalSeq p) p n| * ‖z‖ ^ n := by
    have h := summable_abs_mul_pow_of_bounded (C := 2) (a := realRenewalSeq p - deltaSeq)
      (fun n => by
        have h1 := realRenewalSeq_nonneg hp n
        have h2 := realRenewalSeq_le_one hp n
        simp only [Pi.sub_apply, deltaSeq]
        split_ifs <;> rw [abs_le] <;> constructor <;> linarith) hz
    rwa [← hconv] at h
  have h1 := genFunC_realConv hu hpz
  have hδ : Summable fun n => ‖(deltaSeq n : ℂ) * z ^ n‖ := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp [deltaSeq, Finset.mem_singleton.not.1 hn]
  have hnu : Summable fun n => ‖(realRenewalSeq p n : ℂ) * z ^ n‖ := by
    simpa [norm_genFunC_term] using hu
  have hsplit : genFunC (realRenewalSeq p - deltaSeq) z =
      genFunC (realRenewalSeq p) z - genFunC deltaSeq z := by
    simp only [genFunC]
    rw [← hnu.of_norm.tsum_sub hδ.of_norm]
    refine tsum_congr fun n => ?_
    rw [Pi.sub_apply]
    push_cast
    ring
  rw [hconv, hsplit, genFunC_deltaSeq] at h1
  linear_combination h1

/-- `1 − P(z) ≠ 0` on the open unit disc. -/
theorem one_sub_genFunC_ne_zero {p : ℕ → ℝ} (hp : IsIncrementLaw p) {z : ℂ} (hz : ‖z‖ < 1) :
    1 - genFunC p z ≠ 0 :=
  right_ne_zero_of_mul_eq_one (renewal_genFunC_mul hp hz)

/-- **`U(z) = 1/(1 − P(z))`** for `|z| < 1` (the renewal equation (8.12) in generating-function
form, used in MT p. 367). -/
theorem renewal_genFunC {p : ℕ → ℝ} (hp : IsIncrementLaw p) {z : ℂ} (hz : ‖z‖ < 1) :
    genFunC (realRenewalSeq p) z = 1 / (1 - genFunC p z) :=
  eq_one_div_of_mul_eq_one_left (renewal_genFunC_mul hp hz)

/-- **Delayed renewal generating function**: for a delay law `a` with `∑ |a(n)| |z|ⁿ < ∞` and
`|z| < 1`, the generating function of `a ∗ u` is `A(z)/(1 − P(z))`. -/
theorem delayedRenewal_genFunC {a p : ℕ → ℝ} (hp : IsIncrementLaw p) {z : ℂ} (hz : ‖z‖ < 1)
    (ha : Summable fun n => |a n| * ‖z‖ ^ n) :
    genFunC (delayedRenewal a p) z = genFunC a z / (1 - genFunC p z) := by
  rw [delayedRenewal, genFunC_realConv ha (summable_renewal_genFunC hp hz), renewal_genFunC hp hz,
    mul_one_div]

end MeynTweedie.VUniformErgodicity

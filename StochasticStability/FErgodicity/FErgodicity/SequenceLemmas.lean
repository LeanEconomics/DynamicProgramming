/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Results on sequences and numbers (MT Appendix D.7)

Meyn and Tweedie, Appendix D.7, pp. 563–565: convolutions of sequences on `ℤ₊` and their limits,
two summation identities for generating functions, and two facts about greatest common divisors.
These are used by the renewal theory of §13.2, §14.5 and §15.1.

**Convolution.**
* `realConv a b`: the convolution `a ∗ b (n) = ∑_{j=0}^n a(j) b(n − j)` of two real sequences
  (MT p. 563); `realConv_eq_sum_range`, `realConv_eq_coeff` and `mk_realConv` (it is the
  coefficient sequence of the product of the power series), `realConv_comm`, `realConv_assoc`,
  `realConv_nonneg`, and linearity (`realConv_add_left`, `realConv_sub_left`, `realConv_smul_left`
  and their right-hand versions).

**Limits of convolutions.**
* **Lemma D.7.1** (`lemma_D_7_1`, p. 564): for nonnegative `a`, `b` with `∑ a < ∞` and
  `b(n) → b(∞)`, `a ∗ b (n) → b(∞) ∑ a`. The general form `tendsto_realConv_of_summable_abs` only
  needs `∑ |a| < ∞` (no sign condition on either sequence).

**Generating functions.**
* **Lemma D.7.2 (i)** (`lemma_D_7_2_i`, p. 564): for `c ≥ 0` and `r > 1`,
  `∑ₙ (∑_{m ≥ n} c(m)) rⁿ ≤ r/(r − 1) ∑ₘ c(m) rᵐ`, so the tail series converges when
  `∑ c(m) rᵐ` does; `lemma_D_7_2_i_converse` is the other direction ("converge or diverge
  together"); the partial-sum identity behind it is `tailSum_partial_identity`.
* **Lemma D.7.2 (ii)** (`lemma_D_7_2_ii`, p. 564): for `a, b ≥ 0` and `r ≥ 0`,
  `∑ (a ∗ b)(n) rⁿ = (∑ a(n) rⁿ)(∑ b(n) rⁿ)`.

**Greatest common divisors.**
* **Lemma D.7.3** (`lemma_D_7_3`, p. 565): Bézout, `a m + b n = gcd(m, n)` for some integers.
* **Lemma D.7.4** (`lemma_D_7_4_gcd`, p. 565): an additively closed `S ⊆ ℕ` with a positive
  element has a g.c.d. `g` (characterised by its universal property) and contains `n g` for all
  large `n`. The case used for aperiodic renewal laws, where every common divisor is `1`, is
  `natAddClosed_eventually_mem`. The proof is that of `lemma_D_7_4` in the Chapter 5 project
  (`PseudoAtoms/Period.lean`), restated without the `setGcd`/`IsAddClosed` vocabulary so that the
  two can live in one library.

**Corrections.** None.
-/

namespace MeynTweedie.FErgodicity

open Finset Filter Topology

/-! ### Convolution of sequences -/

/-- The **convolution** `a ∗ b (n) = ∑_{j=0}^n a(j) b(n − j)` of two real sequences on `ℤ₊`
(MT p. 563, also §2.4.1). -/
def realConv (a b : ℕ → ℝ) (n : ℕ) : ℝ := ∑ x ∈ antidiagonal n, a x.1 * b x.2

/-- The convolution as a sum over `j = 0, …, n`. -/
theorem realConv_eq_sum_range (a b : ℕ → ℝ) (n : ℕ) :
    realConv a b n = ∑ k ∈ range (n + 1), a k * b (n - k) :=
  Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j) n

/-- The convolution is the coefficient sequence of the product of the formal power series. -/
theorem realConv_eq_coeff (a b : ℕ → ℝ) (n : ℕ) :
    realConv a b n = PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) := by
  simp [realConv, PowerSeries.coeff_mul]

/-- The power series of a convolution is the product of the power series. -/
theorem mk_realConv (a b : ℕ → ℝ) :
    PowerSeries.mk (realConv a b) = PowerSeries.mk a * PowerSeries.mk b := by
  ext n
  rw [PowerSeries.coeff_mk, realConv_eq_coeff]

/-- Convolution is commutative. -/
theorem realConv_comm (a b : ℕ → ℝ) : realConv a b = realConv b a := by
  funext n
  rw [realConv_eq_coeff, realConv_eq_coeff, mul_comm]

/-- Convolution is associative. -/
theorem realConv_assoc (a b c : ℕ → ℝ) : realConv (realConv a b) c = realConv a (realConv b c) := by
  funext n
  rw [realConv_eq_coeff, realConv_eq_coeff, mk_realConv, mk_realConv, mul_assoc]

/-- The convolution of nonnegative sequences is nonnegative. -/
theorem realConv_nonneg {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (n : ℕ) :
    0 ≤ realConv a b n :=
  sum_nonneg fun _ _ => mul_nonneg (ha _) (hb _)

/-- Convolution is additive in the left factor. -/
theorem realConv_add_left (a b c : ℕ → ℝ) : realConv (a + b) c = realConv a c + realConv b c := by
  funext n
  simp [realConv, add_mul, sum_add_distrib]

/-- Convolution is additive in the right factor. -/
theorem realConv_add_right (a b c : ℕ → ℝ) : realConv a (b + c) = realConv a b + realConv a c := by
  funext n
  simp [realConv, mul_add, sum_add_distrib]

/-- Convolution is subtractive in the left factor. -/
theorem realConv_sub_left (a b c : ℕ → ℝ) : realConv (a - b) c = realConv a c - realConv b c := by
  funext n
  simp [realConv, sub_mul, sum_sub_distrib]

/-- Convolution is subtractive in the right factor. -/
theorem realConv_sub_right (a b c : ℕ → ℝ) : realConv a (b - c) = realConv a b - realConv a c := by
  funext n
  simp [realConv, mul_sub, sum_sub_distrib]

/-- Convolution is homogeneous in the left factor. -/
theorem realConv_smul_left (t : ℝ) (a b : ℕ → ℝ) : realConv (t • a) b = t • realConv a b := by
  funext n
  simp [realConv, mul_sum, mul_assoc]

/-- Convolution is homogeneous in the right factor. -/
theorem realConv_smul_right (t : ℝ) (a b : ℕ → ℝ) : realConv a (t • b) = t • realConv a b := by
  funext n
  simp only [realConv, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun x _ => by ring

/-- Convolution with the constant sequence `1` gives the partial sums. -/
theorem realConv_one_right (a : ℕ → ℝ) (n : ℕ) :
    realConv a (fun _ => 1) n = ∑ k ∈ range (n + 1), a k := by
  simp [realConv_eq_sum_range]

/-- The convolution is monotone in the right factor when the left factor is nonnegative. -/
theorem realConv_mono_right {a b c : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hbc : ∀ n, b n ≤ c n) (n : ℕ) :
    realConv a b n ≤ realConv a c n :=
  sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (hbc _) (ha _)

/-- `|a ∗ b (n)| ≤ |a| ∗ |b| (n)`. -/
theorem abs_realConv_le (a b : ℕ → ℝ) (n : ℕ) :
    |realConv a b n| ≤ realConv (fun k => |a k|) (fun k => |b k|) n := by
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  simp [realConv, abs_mul]

/-! ### Lemma D.7.1: limits of convolutions -/

/-- **Lemma D.7.1, general form.** If `∑ |a(n)| < ∞` and `b(n) → b(∞)`, then
`a ∗ b (n) → b(∞) ∑ a(n)`. No sign conditions are needed. -/
theorem tendsto_realConv_of_summable_abs {a b : ℕ → ℝ} {L : ℝ} (ha : Summable fun n => |a n|)
    (hb : Tendsto b atTop (𝓝 L)) :
    Tendsto (realConv a b) atTop (𝓝 (L * ∑' n, a n)) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, |b n| ≤ C := by
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto b hb).exists_norm_le
    exact ⟨C, fun n => by simpa [Real.norm_eq_abs] using hC (b n) ⟨n, rfl⟩⟩
  set F : ℕ → ℕ → ℝ := fun n k => if k ≤ n then a k * b (n - k) else 0 with hF
  have hconv : realConv a b = fun n => ∑' k, F n k := by
    funext n
    rw [realConv_eq_sum_range, tsum_eq_sum (s := range (n + 1))]
    · refine sum_congr rfl fun k hk => ?_
      simp [hF, Nat.lt_succ_iff.1 (mem_range.1 hk)]
    · intro k hk
      simp only [mem_range, not_lt] at hk
      simp [hF, show ¬ k ≤ n by omega]
  have hlim : Tendsto (fun n => ∑' k, F n k) atTop (𝓝 (∑' k, a k * L)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun k => |a k| * C)
      (ha.mul_right C) (fun k => ?_) (Eventually.of_forall fun n k => ?_)
    · have h1 : Tendsto (fun n => a k * b (n - k)) atTop (𝓝 (a k * L)) :=
        (hb.comp (tendsto_sub_atTop_nat k)).const_mul (a k)
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop k] with n hn
      simp [hF, hn]
    · simp only [hF]
      split_ifs
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
      · simpa using mul_nonneg (abs_nonneg (a k)) ((abs_nonneg _).trans (hC 0))
  rw [hconv]
  convert hlim using 2
  rw [tsum_mul_right, mul_comm]

/-- **Lemma D.7.1** (MT p. 564). If `a, b ≥ 0`, `b(n) → b(∞)` and `∑ a(j) < ∞`, then
`a ∗ b (n) → b(∞) ∑ a(j)`. -/
theorem lemma_D_7_1 {a b : ℕ → ℝ} {L : ℝ} (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (hb : Tendsto b atTop (𝓝 L)) :
    Tendsto (realConv a b) atTop (𝓝 (L * ∑' n, a n)) :=
  tendsto_realConv_of_summable_abs (by simpa [abs_of_nonneg (ha _)] using hsum) hb

/-! ### Lemma D.7.2: generating functions of tails and convolutions -/

/-- The tail sums of a summable sequence satisfy `T(n) = c(n) + T(n + 1)`. -/
theorem tailSum_succ {c : ℕ → ℝ} (hc : Summable c) (n : ℕ) :
    ∑' m, c (m + n) = c n + ∑' m, c (m + (n + 1)) := by
  rw [((summable_nat_add_iff n).2 hc).tsum_eq_zero_add, zero_add]
  congr 1
  exact tsum_congr fun m => by rw [add_assoc, add_comm 1 n]

/-- The partial-sum identity behind Lemma D.7.2 (i): with `T(n) = ∑_{m ≥ n} c(m)`,
`(r − 1) ∑_{n < N} T(n) rⁿ = ∑_{n < N} c(n) (r^{n+1} − 1) + T(N) (r^N − 1)`. -/
theorem tailSum_partial_identity {c : ℕ → ℝ} (hc : Summable c) (r : ℝ) (N : ℕ) :
    (∑ n ∈ range N, (∑' m, c (m + n)) * r ^ n) * (r - 1) =
      ∑ n ∈ range N, c n * (r ^ (n + 1) - 1) + (∑' m, c (m + N)) * (r ^ N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, add_mul, ih, sum_range_succ, tailSum_succ hc N]
    ring

/-- **Lemma D.7.2 (i)** (MT p. 564). For `c ≥ 0` and `r > 1`, if `∑ c(m) rᵐ < ∞` then the tail
series `∑ₙ (∑_{m ≥ n} c(m)) rⁿ` converges and is at most `r/(r − 1) ∑ₘ c(m) rᵐ`. -/
theorem lemma_D_7_2_i {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {r : ℝ} (hr : 1 < r)
    (hsum : Summable fun n => c n * r ^ n) :
    Summable (fun n => (∑' m, c (m + n)) * r ^ n) ∧
      ∑' n, (∑' m, c (m + n)) * r ^ n ≤ r / (r - 1) * ∑' n, c n * r ^ n := by
  have hcs : Summable c :=
    hsum.of_nonneg_of_le hc (fun n => le_mul_of_one_le_right (hc n) (one_le_pow₀ hr.le))
  have hr0 : 0 ≤ r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hT0 : ∀ n, 0 ≤ ∑' m, c (m + n) := fun n => tsum_nonneg fun m => hc _
  have hterm0 : ∀ n, 0 ≤ (∑' m, c (m + n)) * r ^ n := fun n => mul_nonneg (hT0 n) (pow_nonneg hr0 n)
  have hbound : ∀ N, ∑ n ∈ range N, (∑' m, c (m + n)) * r ^ n ≤
      r / (r - 1) * ∑' n, c n * r ^ n := by
    intro N
    have hid := tailSum_partial_identity hcs r N
    have h1 : ∑ n ∈ range N, c n * (r ^ (n + 1) - 1) ≤ r * ∑ n ∈ range N, c n * r ^ n := by
      rw [mul_sum]
      refine sum_le_sum fun n _ => ?_
      have := hc n
      rw [pow_succ]
      nlinarith
    have h3 : (∑' m, c (m + N)) * r ^ N ≤ ∑' m, c (m + N) * r ^ (m + N) := by
      rw [← tsum_mul_right]
      refine Summable.tsum_le_tsum (fun m => ?_) (((summable_nat_add_iff N).2 hcs).mul_right _)
        ((summable_nat_add_iff N).2 hsum)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr.le (by omega)) (hc _)
    have h4 := hsum.sum_add_tsum_nat_add N
    have hS : ∑ n ∈ range N, c n * r ^ n ≤ ∑' n, c n * r ^ n :=
      hsum.sum_le_tsum _ (fun n _ => mul_nonneg (hc n) (pow_nonneg hr0 n))
    have hTN := hT0 N
    rw [div_mul_eq_mul_div, le_div_iff₀ hr1]
    nlinarith
  exact ⟨summable_of_sum_range_le hterm0 hbound, Real.tsum_le_of_sum_range_le hterm0 hbound⟩

/-- **Lemma D.7.2 (i), converse direction** (MT p. 564): for a summable `c ≥ 0` and `r ≥ 0`, if the
tail series `∑ₙ (∑_{m ≥ n} c(m)) rⁿ` converges, so does `∑ c(n) rⁿ` (so the two series converge
or diverge together). -/
theorem lemma_D_7_2_i_converse {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (hcs : Summable c) {r : ℝ}
    (hr : 0 ≤ r) (hsum : Summable fun n => (∑' m, c (m + n)) * r ^ n) :
    Summable fun n => c n * r ^ n := by
  refine hsum.of_nonneg_of_le (fun n => mul_nonneg (hc n) (pow_nonneg hr n)) fun n => ?_
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr n)
  simpa using ((summable_nat_add_iff n).2 hcs).le_tsum 0 (fun m _ => hc _)

/-- The weighted convolution splits along the antidiagonal:
`(a ∗ b)(n) rⁿ = ∑_{k + l = n} (a(k) rᵏ)(b(l) rˡ)`. -/
theorem realConv_mul_pow (a b : ℕ → ℝ) (r : ℝ) (n : ℕ) :
    realConv a b n * r ^ n = ∑ kl ∈ antidiagonal n, (a kl.1 * r ^ kl.1) * (b kl.2 * r ^ kl.2) := by
  rw [realConv, sum_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [mem_antidiagonal] at hx
  rw [← hx, pow_add]
  ring

/-- **Lemma D.7.2 (ii)** (MT p. 564). For `a, b ≥ 0` and `r ≥ 0` with `∑ a(n) rⁿ` and
`∑ b(n) rⁿ` finite, `∑ (a ∗ b)(n) rⁿ = (∑ a(n) rⁿ)(∑ b(n) rⁿ)`. -/
theorem lemma_D_7_2_ii {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) {r : ℝ}
    (hr : 0 ≤ r) (hsa : Summable fun n => a n * r ^ n) (hsb : Summable fun n => b n * r ^ n) :
    HasSum (fun n => realConv a b n * r ^ n) ((∑' n, a n * r ^ n) * ∑' n, b n * r ^ n) := by
  have hna : Summable fun n => ‖a n * r ^ n‖ :=
    hsa.congr fun n => (Real.norm_of_nonneg (mul_nonneg (ha n) (pow_nonneg hr n))).symm
  have hnb : Summable fun n => ‖b n * r ^ n‖ :=
    hsb.congr fun n => (Real.norm_of_nonneg (mul_nonneg (hb n) (pow_nonneg hr n))).symm
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hna hnb).of_norm
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]
  simp_rw [realConv_mul_pow]
  exact hs.hasSum

/-! ### Lemmas D.7.3 and D.7.4: greatest common divisors -/

/-- **Lemma D.7.3** (MT p. 565, Bézout). For naturals `m, n` there are integers `a, b` with
`a m + b n = gcd(m, n)`. -/
theorem lemma_D_7_3 (m n : ℕ) : ∃ a b : ℤ, a * m + b * n = Nat.gcd m n :=
  ⟨Nat.gcdA m n, Nat.gcdB m n, by rw [Nat.gcd_eq_gcd_ab]; ring⟩

/-- Positive multiples `(q + 1) b` of an element of an additively closed set lie in it. -/
theorem natAddClosed_succ_mul_mem {S : Set ℕ} (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) {b : ℕ}
    (hb : b ∈ S) (q : ℕ) : (q + 1) * b ∈ S := by
  induction q with
  | zero => simpa using hb
  | succ q ih => rw [add_mul, one_mul]; exact hS _ ih _ hb

/-- Multiples `q b` of an element of `S ∪ {0}` lie in `S ∪ {0}` (`S` additively closed). -/
theorem natAddClosed_mul_mem_zero {S : Set ℕ} (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) {b : ℕ}
    (hb : b = 0 ∨ b ∈ S) (q : ℕ) : q * b = 0 ∨ q * b ∈ S := by
  rcases hb with rfl | hb
  · left; simp
  · rcases q with _ | q
    · left; simp
    · exact Or.inr (natAddClosed_succ_mul_mem hS hb q)

/-- The sum of an element of `S ∪ {0}` and an element of `S` lies in `S` (`S` additively
closed). -/
theorem natAddClosed_add_mem_of_zero {S : Set ℕ} (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) {a b : ℕ}
    (ha : a = 0 ∨ a ∈ S) (hb : b ∈ S) : a + b ∈ S := by
  rcases ha with rfl | ha
  · simpa using hb
  · exact hS _ ha _ hb

/-- **The g.c.d. as a least difference.** If `S ⊆ ℕ` is additively closed with a positive element,
the least positive difference `g = b − a` of elements of `S ∪ {0}` (with `b ∈ S`) divides every
element of `S`, and every common divisor of `S` divides it. -/
theorem natAddClosed_gcd_witness {S : Set ℕ} (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) {s₀ : ℕ}
    (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) :
    ∃ g a, 0 < g ∧ (a = 0 ∨ a ∈ S) ∧ a + g ∈ S ∧ (∀ s ∈ S, g ∣ s) ∧
      ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ g := by
  set T : Set ℕ := {g | 0 < g ∧ ∃ a, (a = 0 ∨ a ∈ S) ∧ a + g ∈ S} with hT
  have hTne : T.Nonempty := ⟨s₀, hpos, 0, Or.inl rfl, by simpa using hs₀⟩
  obtain ⟨hgpos, a, ha, hag⟩ := Nat.sInf_mem hTne
  set g := sInf T
  refine ⟨g, a, hgpos, ha, hag, fun s hs => ?_, fun d hd => ?_⟩
  · by_contra hdvd
    have hr : 0 < s % g := Nat.pos_of_ne_zero fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
    have hrT : s % g ∈ T := by
      refine ⟨hr, s / g * (a + g), natAddClosed_mul_mem_zero hS (Or.inr hag) _, ?_⟩
      have hsplit : s / g * (a + g) + s % g = s / g * a + s := by
        have := Nat.div_add_mod s g
        nlinarith [this]
      rw [hsplit]
      exact natAddClosed_add_mem_of_zero hS (natAddClosed_mul_mem_zero hS ha _) hs
    exact absurd (Nat.sInf_le hrT) (not_le.2 (Nat.mod_lt s hgpos))
  · have h1 : d ∣ a := by
      rcases ha with rfl | ha
      · exact dvd_zero d
      · exact hd a ha
    exact (Nat.dvd_add_right h1).1 (hd _ hag)

/-- **Lemma D.7.4** (MT p. 565). Let `S ⊆ ℕ` be closed under addition with a positive element.
Then `S` has a greatest common divisor `g > 0` (it divides every element and every common divisor
divides it), and `n g ∈ S` for all large enough `n`. -/
theorem lemma_D_7_4_gcd {S : Set ℕ} (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) {s₀ : ℕ} (hs₀ : s₀ ∈ S)
    (hpos : 0 < s₀) :
    ∃ g, 0 < g ∧ (∀ s ∈ S, g ∣ s) ∧ (∀ d, (∀ s ∈ S, d ∣ s) → d ∣ g) ∧
      ∃ N, ∀ n ≥ N, n * g ∈ S := by
  obtain ⟨g, a, hg, ha, hag, hdvd, hmax⟩ := natAddClosed_gcd_witness hS hs₀ hpos
  refine ⟨g, hg, hdvd, hmax, ?_⟩
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨1, fun n hn => ?_⟩
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact natAddClosed_succ_mul_mem hS (by simpa using hag) q
  · have haS : a ∈ S := ha.resolve_left ha0
    obtain ⟨k, hk⟩ := hdvd a haS
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => ha0 (by rw [hk, h, mul_zero])
    refine ⟨k * k, fun n hn => ?_⟩
    have hx : k ≤ n / k := (Nat.le_div_iff_mul_le hk0).2 hn
    have hr : n % k < k := Nat.mod_lt n hk0
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt (hr.trans_le hx)
    have hsplit : n * g = (t + 1) * a + n % k * (a + g) := by
      have h1 := Nat.div_add_mod n k
      rw [ht] at h1
      rw [hk]
      nlinarith [h1]
    rw [hsplit]
    rcases Nat.eq_zero_or_pos (n % k) with h0 | h0
    · rw [h0, zero_mul, add_zero]; exact natAddClosed_succ_mul_mem hS haS t
    · obtain ⟨r, hr'⟩ := Nat.exists_eq_add_of_lt h0
      rw [hr', zero_add]
      exact hS _ (natAddClosed_succ_mul_mem hS haS t) _ (natAddClosed_succ_mul_mem hS hag r)

/-- **Lemma D.7.4 with g.c.d. one.** An additively closed `S ⊆ ℕ` with a positive element, whose
only common divisor is `1`, contains every large enough natural number. -/
theorem natAddClosed_eventually_mem {S : Set ℕ} (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) {s₀ : ℕ}
    (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) (hgcd : ∀ d, (∀ s ∈ S, d ∣ s) → d = 1) :
    ∃ N, ∀ n ≥ N, n ∈ S := by
  obtain ⟨g, -, hdvd, -, N, hN⟩ := lemma_D_7_4_gcd hS hs₀ hpos
  have hg1 : g = 1 := hgcd g hdvd
  exact ⟨N, fun n hn => by simpa [hg1] using hN n hn⟩

end MeynTweedie.FErgodicity

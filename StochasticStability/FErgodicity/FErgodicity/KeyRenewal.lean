/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.RenewalTheorem

/-!
# Key renewal theorems on `ℤ₊` (MT §14.5)

Meyn and Tweedie, §14.5, pp. 354–358, state renewal theorems for a renewal measure on `ℝ₊`:
Blackwell's theorem (Theorem 14.5.1, quoted from Feller) and the Uniform Key Renewal Theorem
(Theorem 14.5.2, for spread-out increments, proved via the forward recurrence time skeleton). This
module proves the corresponding results for renewal sequences on `ℤ₊`, which is the form the
discrete-time atom arguments use. On `ℤ₊` direct Riemann integrability reduces to summability,
and spread-out reduces to aperiodicity.

* `key_renewal_theorem` (discrete key renewal theorem): for `∑ |b| < ∞`,
  `(u ∗ b)(n) → m_p⁻¹ ∑ b`, the analogue of (14.34) with `Γ₀ = δ₀`.
* `delayed_key_renewal_theorem`: for a delay law `a`, `(a ∗ u ∗ b)(n) → m_p⁻¹ ∑ b`, the analogue
  of (14.34).
* `blackwell_renewal_theorem` (discrete form of Theorem 14.5.1, (14.35)): for a delay law `a`
  and `h ∈ ℕ`, the expected number of renewals in `[n, n + h)` tends to `h/m_p`.
* `uniform_key_renewal_theorem` (discrete form of Theorem 14.5.2 (i), (14.36)): for a summable
  `f ≥ 0`, `(a ∗ u ∗ g)(n) → m_p⁻¹ ∑ g` uniformly over `|g| ≤ f`.
* `uniform_key_renewal_two_delays` (discrete form of Proposition 14.5.5): for two delay laws,
  `sup_{|g| ≤ f} |(a ∗ u ∗ g)(n) − (b ∗ u ∗ g)(n)| → 0`.

**Not formalised.** The continuous-time statements themselves (Theorem 14.5.1, Theorem 14.5.2,
Propositions 14.5.3–14.5.5 for measures on `ℝ₊`): they need the spread-out renewal measure and the
total-variation ergodic theory of the forward recurrence time `δ`-skeleton (Chapters 5, 10 and 13);
Theorem 14.5.1 is moreover only quoted from Feller in the book.

**Corrections.** None.
-/

namespace MeynTweedie.FErgodicity

open Finset Filter Topology

/-- **The key renewal theorem on `ℤ₊`.** For an aperiodic increment law and a sequence `b` with
`∑ |b(n)| < ∞`, `(u ∗ b)(n) → m_p⁻¹ ∑ b(n)` (the discrete analogue of (14.34), MT p. 354). -/
theorem key_renewal_theorem {p b : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (hb : Summable fun n => |b n|) :
    Tendsto (realConv (realRenewalSeq p) b) atTop (𝓝 ((incrMean p)⁻¹ * ∑' n, b n)) := by
  rw [realConv_comm]
  exact tendsto_realConv_of_summable_abs hb (renewal_theorem hp hap)

/-- **The delayed key renewal theorem on `ℤ₊`** ((14.34)). For a delay law `a`,
`(a ∗ u ∗ b)(n) → m_p⁻¹ ∑ b(n)` whenever `∑ |b(n)| < ∞`. -/
theorem delayed_key_renewal_theorem {a p b : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p) (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1)
    (hb : Summable fun n => |b n|) :
    Tendsto (realConv (delayedRenewal a p) b) atTop (𝓝 ((incrMean p)⁻¹ * ∑' n, b n)) := by
  rw [realConv_comm]
  exact tendsto_realConv_of_summable_abs hb (delayedRenewal_tendsto_of_hasSum hp hap ha ha1)

/-- **Blackwell's renewal theorem on `ℤ₊`** (discrete form of Theorem 14.5.1, (14.35)). For a
delay law `a` and `h ∈ ℕ`, the expected number of renewals `∑_{k < h} (a ∗ u)(n + k)` in the
window `[n, n + h)` tends to `h / m_p`. -/
theorem blackwell_renewal_theorem {a p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1) (h : ℕ) :
    Tendsto (fun n => ∑ k ∈ range h, delayedRenewal a p (n + k)) atTop
      (𝓝 (h * (incrMean p)⁻¹)) := by
  have hlim := delayedRenewal_tendsto_of_hasSum hp hap ha ha1
  have h1 : Tendsto (fun n => ∑ k ∈ range h, delayedRenewal a p (n + k)) atTop
      (𝓝 (∑ k ∈ range h, (incrMean p)⁻¹)) :=
    tendsto_finsetSum _ fun k _ => hlim.comp (tendsto_add_atTop_nat k)
  simpa using h1

/-- **The uniform key renewal theorem on `ℤ₊`** (discrete form of Theorem 14.5.2 (i), (14.36)).
Let `a` be a delay law and `f ≥ 0` summable. Then `(a ∗ u ∗ g)(n) → m_p⁻¹ ∑ g` uniformly over all
`g` with `|g| ≤ f`. On `ℤ₊`, conditions (14.37)–(14.39) all follow from `∑ f < ∞`. -/
theorem uniform_key_renewal_theorem {a p f : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p) (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1) (hf : ∀ n, 0 ≤ f n)
    (hfs : Summable f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g : ℕ → ℝ, (∀ j, |g j| ≤ f j) →
      |realConv (delayedRenewal a p) g n - (incrMean p)⁻¹ * ∑' j, g j| ≤ ε := by
  set c := (incrMean p)⁻¹
  set w := delayedRenewal a p
  have hc0 : 0 ≤ c := inv_nonneg.2 (tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg n)
    (hp.nonneg n))
  have hw : Tendsto w atTop (𝓝 c) := delayedRenewal_tendsto_of_hasSum hp hap ha ha1
  -- the two `g`-free error terms
  have hdev : Tendsto (fun n => |w n - c|) atTop (𝓝 0) := by
    have := (hw.sub (tendsto_const_nhds (x := c))).abs
    simpa using this
  have h1 : Tendsto (realConv f fun n => |w n - c|) atTop (𝓝 0) := by
    simpa using lemma_D_7_1 hf hfs hdev
  have h2 : Tendsto (fun n => c * ∑' j, f (j + (n + 1))) atTop (𝓝 0) := by
    have htail : Tendsto (fun n => ∑' j, f (j + n)) atTop (𝓝 0) := tendsto_sum_nat_add f
    simpa using (htail.comp (tendsto_add_atTop_nat 1)).const_mul c
  filter_upwards [(tendsto_order.1 h1).2 (ε / 2) (by linarith),
    (tendsto_order.1 h2).2 (ε / 2) (by linarith)] with n hn1 hn2 g hg
  have hgs : Summable g := Summable.of_norm_bounded hfs fun j => by
    rw [Real.norm_eq_abs]; exact hg j
  have hsplit := hgs.sum_add_tsum_nat_add (n + 1)
  have hconv : realConv w g n = ∑ j ∈ range (n + 1), g j * w (n - j) := by
    rw [realConv_comm, realConv_eq_sum_range]
  have heq : realConv w g n - c * ∑' j, g j =
      ∑ j ∈ range (n + 1), g j * (w (n - j) - c) - c * ∑' j, g (j + (n + 1)) := by
    rw [hconv, ← hsplit, mul_add, mul_sum]
    simp only [mul_sub, sum_sub_distrib]
    ring_nf
  have hA : |∑ j ∈ range (n + 1), g j * (w (n - j) - c)| ≤
      realConv f (fun n => |w n - c|) n := by
    rw [realConv_eq_sum_range]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hg j) (abs_nonneg _)
  have hB : |c * ∑' j, g (j + (n + 1))| ≤ c * ∑' j, f (j + (n + 1)) := by
    rw [abs_mul, abs_of_nonneg hc0]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    have hfs' := (summable_nat_add_iff (n + 1)).2 hfs
    refine (Real.norm_eq_abs _ ▸ norm_tsum_le_tsum_norm ?_).trans ?_
    · exact hfs'.of_nonneg_of_le (fun j => norm_nonneg _) fun j => by
        rw [Real.norm_eq_abs]; exact hg _
    · exact Summable.tsum_le_tsum (fun j => by rw [Real.norm_eq_abs]; exact hg _)
        (hfs'.of_nonneg_of_le (fun j => norm_nonneg _) fun j => by
          rw [Real.norm_eq_abs]; exact hg _) hfs'
  rw [heq]
  calc |∑ j ∈ range (n + 1), g j * (w (n - j) - c) - c * ∑' j, g (j + (n + 1))|
      ≤ |∑ j ∈ range (n + 1), g j * (w (n - j) - c)| + |c * ∑' j, g (j + (n + 1))| :=
        abs_sub _ _
    _ ≤ ε := by linarith

/-- **Two delays, uniformly** (discrete form of Proposition 14.5.5). For delay laws `a, b` and a
summable `f ≥ 0`, `sup_{|g| ≤ f} |(a ∗ u ∗ g)(n) − (b ∗ u ∗ g)(n)| → 0`. -/
theorem uniform_key_renewal_two_delays {a b p f : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p) (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1) (hb : ∀ n, 0 ≤ b n)
    (hb1 : HasSum b 1) (hf : ∀ n, 0 ≤ f n) (hfs : Summable f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g : ℕ → ℝ, (∀ j, |g j| ≤ f j) →
      |realConv (delayedRenewal a p) g n - realConv (delayedRenewal b p) g n| ≤ ε := by
  filter_upwards [uniform_key_renewal_theorem hp hap ha ha1 hf hfs (half_pos hε),
    uniform_key_renewal_theorem hp hap hb hb1 hf hfs (half_pos hε)] with n h1 h2 g hg
  have e1 := h1 g hg
  have e2 := h2 g hg
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

end MeynTweedie.FErgodicity

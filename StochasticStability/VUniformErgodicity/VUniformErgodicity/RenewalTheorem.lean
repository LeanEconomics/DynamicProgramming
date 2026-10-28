/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.RenewalSequences
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The renewal theorem (MT §13.2)

Meyn and Tweedie, §13.2.1–13.2.2, pp. 320–323: for an aperiodic increment law `p` with mean
`m_p`, the renewal sequence satisfies `u(n) → 1/m_p`, and so does every delayed renewal sequence
`a ∗ u`. The book proves this by coupling two renewal processes (Proposition 13.2.1, which rests
on the positive Harris recurrence of the linked forward recurrence time chain of §10.3.1). We give
instead the classical analytic proof of Erdős, Feller and Pollard, which needs no probability space
and also covers `m_p = ∞`:

1. along a subsequence with `u(nₖ) → λ = lim sup u`, the renewal equation forces
   `u(nₖ − j) → λ` for every `j` with `p(j) > 0` (`tendsto_shift_of_limsup`), hence for every `j`
   in the additive semigroup they generate, hence (aperiodicity and Lemma D.7.4) for all `j ≥ N₀`
   (`exists_shift_closure`);
2. the identity `∑_{i ≤ n} tail(i) u(n − i) = 1` then gives `λ ∑_{i<N} tail(i) ≤ 1` for all `N`,
   so `λ ≤ 1/m_p` (`limsup_mul_sum_renewalTail_le`);
3. the same argument at `μ = lim inf u` gives `1 ≤ μ m_p` when `m_p < ∞`
   (`one_le_liminf_mul_incrMean`).

**Definitions.**
* `IsAperiodicLaw p`: the only common divisor of `{n : p(n) > 0}` is `1`, i.e.
  `g.c.d.{n : p(n) > 0} = 1` (MT p. 321).
* `equilibriumLaw p = e`, `e(n) = m_p⁻¹ ∑_{j > n} p(j)` (13.34).

**Results.**
* `renewal_theorem_of_summable`: `u(n) → 1/m_p` when `m_p < ∞`.
* `renewal_theorem_of_not_summable`: `u(n) → 0` when `m_p = ∞`.
* `renewal_theorem`: both at once, `u(n) → m_p⁻¹` (in Lean `m_p = 0` and `0⁻¹ = 0` when the mean
  series diverges).
* `delayedRenewal_tendsto`: `a ∗ u (n) → (∑ a) / m_p` for any summable `a ≥ 0` (MT (13.20)).
* **Theorem 13.2.2** (`theorem_13_2_2`, p. 322): `|a ∗ u (n) − b ∗ u (n)| → 0` for delay laws
  `a`, `b`. (Proved without the book's hypothesis `m_p < ∞`, as the book remarks on p. 322.)
* `equilibriumLaw_hasSum` (`e` is a probability) and `realConv_equilibriumLaw_renewal`
  (`e ∗ u ≡ 1/m_p`, (13.35)).
* **Theorem 13.2.3** (`theorem_13_2_3`, p. 323): `|a ∗ u (n) − 1/m_p| → 0` for a delay law `a`,
  when `m_p < ∞`.

**Not formalised.** Proposition 13.2.1 (the coupling time `T_ab` is almost surely finite) and the
coupling identity (13.32)–(13.33): they are steps of the book's probabilistic proof, which is
replaced here by the analytic proof; their probabilistic content (independent renewal processes on
one probability space, the linked forward recurrence chain `V*`) belongs to the Markov chain
chapters.

**Corrections.** None.
-/

namespace MeynTweedie.VUniformErgodicity

open Finset Filter Topology

/-- An increment law is **aperiodic** (MT p. 321) when `g.c.d.{n : p(n) > 0} = 1`, i.e. the only
natural number dividing every `n` with `p(n) > 0` is `1`. -/
def IsAperiodicLaw (p : ℕ → ℝ) : Prop := ∀ d : ℕ, (∀ n, 0 < p n → d ∣ n) → d = 1

/-- An increment law has a positive atom at some `j ≥ 1`. -/
theorem exists_pos_incr {p : ℕ → ℝ} (hp : IsIncrementLaw p) : ∃ j, 0 < j ∧ 0 < p j := by
  by_contra h
  push Not at h
  have hzero : p = fun _ => 0 := by
    funext j
    rcases j with _ | j
    · exact hp.zero
    · exact le_antisymm (h _ (Nat.succ_pos j)) (hp.nonneg _)
  have h1 := hp.hasSum
  rw [hzero] at h1
  exact one_ne_zero (h1.unique hasSum_zero)

/-! ### Splitting the renewal equation -/

/-- **The renewal equation split at `j ≤ N ≤ n`**:
`u(n) = p(j) u(n − j) + ∑_{k ≤ N, k ≠ j} p(k) u(n − k) + ∑_{N < k ≤ n} p(k) u(n − k)`. -/
theorem realRenewalSeq_split {p : ℕ → ℝ} (hp0 : p 0 = 0) {j N n : ℕ} (hjN : j ≤ N) (hNn : N ≤ n)
    (hn : 0 < n) :
    realRenewalSeq p n = p j * realRenewalSeq p (n - j) +
      ∑ k ∈ (range (N + 1)).erase j, p k * realRenewalSeq p (n - k) +
      ∑ k ∈ Ico (N + 1) (n + 1), p k * realRenewalSeq p (n - k) := by
  rw [realRenewalSeq_eq_realConv_of_pos hp0 hn, realConv_eq_sum_range,
    ← sum_range_add_sum_Ico _ (show N + 1 ≤ n + 1 by omega),
    ← add_sum_erase (range (N + 1)) (fun k => p k * realRenewalSeq p (n - k)) (a := j)
      (mem_range.2 (by omega))]

/-- The mass of `p` on `(N, n]` is at most the tail `∑_{j > N} p(j)`. -/
theorem sum_Ico_incr_le_tail {p : ℕ → ℝ} (hp : IsIncrementLaw p) {N n : ℕ} (hNn : N ≤ n) :
    ∑ k ∈ Ico (N + 1) (n + 1), p k ≤ renewalTail p N := by
  have h := sum_range_add_sum_Ico p (show N + 1 ≤ n + 1 by omega)
  have h1 := sum_range_le_one hp (n + 1)
  rw [renewalTail]
  linarith

/-- `0 ≤ λ ≤ 1` for a limit point `λ` of the renewal sequence. -/
theorem limit_mem_unit {p : ℕ → ℝ} (hp : IsIncrementLaw p) {φ : ℕ → ℕ} {L : ℝ}
    (hlim : Tendsto (fun k => realRenewalSeq p (φ k)) atTop (𝓝 L)) : 0 ≤ L ∧ L ≤ 1 :=
  ⟨ge_of_tendsto' hlim fun _ => realRenewalSeq_nonneg hp _,
    le_of_tendsto' hlim fun _ => realRenewalSeq_le_one hp _⟩

/-! ### Shifting a convergent subsequence -/

/-- **The shift step at the upper limit.** Suppose `u(n) ≤ λ + ε` eventually for every `ε > 0`
(so `λ ≥ lim sup u`) and `u(φ k) → λ` along `φ k → ∞`. Then `u(φ k − j) → λ` for every `j` with
`p(j) > 0`. -/
theorem tendsto_shift_of_limsup {p : ℕ → ℝ} (hp : IsIncrementLaw p) {L : ℝ}
    (hup : ∀ ε > 0, ∀ᶠ n in atTop, realRenewalSeq p n ≤ L + ε) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) (hlim : Tendsto (fun k => realRenewalSeq p (φ k)) atTop (𝓝 L))
    {j : ℕ} (hj : 0 < p j) :
    Tendsto (fun k => realRenewalSeq p (φ k - j)) atTop (𝓝 L) := by
  have hφj : Tendsto (fun k => φ k - j) atTop atTop := (tendsto_sub_atTop_nat j).comp hφ
  have hL := limit_mem_unit hp hlim
  have hj0 : 0 < j := Nat.pos_of_ne_zero fun h => by rw [h, hp.zero] at hj; exact lt_irrefl _ hj
  have hpj1 : p j ≤ 1 := by
    have := sum_range_le_one hp (j + 1)
    have := single_le_sum (fun i _ => hp.nonneg i) (mem_range.2 (Nat.lt_succ_self j))
    linarith
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · set δ := L - a with hδ
    have hδ0 : 0 < δ := by linarith
    set ε := δ * p j / 4 with hε
    have hε0 : 0 < ε := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((eventually_ge_atTop j).and ((tendsto_order.1 (tendsto_renewalTail hp)).2 ε hε0))
    obtain ⟨M, hM⟩ := eventually_atTop.1 (hup ε hε0)
    have hjN : j ≤ N := (hN N le_rfl).1
    have htail : renewalTail p N < ε := (hN N le_rfl).2
    filter_upwards [hφ.eventually (eventually_ge_atTop (M + N)),
      (tendsto_order.1 hlim).1 (L - ε) (by linarith)] with k hk1 hk2
    set n := φ k
    have hsplit := realRenewalSeq_split hp.zero hjN (show N ≤ n by omega) (by omega)
    have hA : ∑ k ∈ (range (N + 1)).erase j, p k * realRenewalSeq p (n - k) ≤
        (1 - p j) * (L + ε) := by
      calc ∑ k ∈ (range (N + 1)).erase j, p k * realRenewalSeq p (n - k)
          ≤ ∑ k ∈ (range (N + 1)).erase j, p k * (L + ε) := by
            refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hM _ ?_) (hp.nonneg _)
            have := mem_range.1 (mem_of_mem_erase hi)
            omega
        _ = (∑ k ∈ range (N + 1), p k - p j) * (L + ε) := by
            rw [← sum_mul, ← add_sum_erase (range (N + 1)) p (a := j) (mem_range.2 (by omega))]
            ring
        _ ≤ (1 - p j) * (L + ε) := by
            have := sum_range_le_one hp (N + 1)
            exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hB : ∑ k ∈ Ico (N + 1) (n + 1), p k * realRenewalSeq p (n - k) ≤ ε := by
      calc ∑ k ∈ Ico (N + 1) (n + 1), p k * realRenewalSeq p (n - k)
          ≤ ∑ k ∈ Ico (N + 1) (n + 1), p k :=
            sum_le_sum fun i _ => mul_le_of_le_one_right (hp.nonneg _) (realRenewalSeq_le_one hp _)
        _ ≤ renewalTail p N := sum_Ico_incr_le_tail hp (by omega)
        _ ≤ ε := htail.le
    set x := realRenewalSeq p (n - j)
    by_contra hx
    push Not at hx
    have h1 : p j * x ≤ p j * a := mul_le_mul_of_nonneg_left hx (hp.nonneg j)
    have h2 : 0 ≤ p j * ε := mul_nonneg (hp.nonneg j) hε0.le
    nlinarith
  · have hε0 : 0 < (b - L) / 2 := by linarith
    filter_upwards [hφj.eventually (hup _ hε0)] with k hk
    linarith

/-- **The shift step at the lower limit.** Suppose `u(n) ≥ μ − ε` eventually for every `ε > 0`
(so `μ ≤ lim inf u`) and `u(φ k) → μ` along `φ k → ∞`. Then `u(φ k − j) → μ` for every `j` with
`p(j) > 0`. -/
theorem tendsto_shift_of_liminf {p : ℕ → ℝ} (hp : IsIncrementLaw p) {L : ℝ}
    (hlow : ∀ ε > 0, ∀ᶠ n in atTop, L - ε ≤ realRenewalSeq p n) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) (hlim : Tendsto (fun k => realRenewalSeq p (φ k)) atTop (𝓝 L))
    {j : ℕ} (hj : 0 < p j) :
    Tendsto (fun k => realRenewalSeq p (φ k - j)) atTop (𝓝 L) := by
  have hφj : Tendsto (fun k => φ k - j) atTop atTop := (tendsto_sub_atTop_nat j).comp hφ
  have hL := limit_mem_unit hp hlim
  have hj0 : 0 < j := Nat.pos_of_ne_zero fun h => by rw [h, hp.zero] at hj; exact lt_irrefl _ hj
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hε0 : 0 < (L - a) / 2 := by linarith
    filter_upwards [hφj.eventually (hlow _ hε0)] with k hk
    linarith
  · set δ := b - L with hδ
    have hδ0 : 0 < δ := by linarith
    set ε := δ * p j / 4 with hε
    have hε0 : 0 < ε := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((eventually_ge_atTop j).and ((tendsto_order.1 (tendsto_renewalTail hp)).2 ε hε0))
    obtain ⟨M, hM⟩ := eventually_atTop.1 (hlow ε hε0)
    have hjN : j ≤ N := (hN N le_rfl).1
    have htail : renewalTail p N < ε := (hN N le_rfl).2
    filter_upwards [hφ.eventually (eventually_ge_atTop (M + N)),
      (tendsto_order.1 hlim).2 (L + ε) (by linarith)] with k hk1 hk2
    set n := φ k
    have hsplit := realRenewalSeq_split hp.zero hjN (show N ≤ n by omega) (by omega)
    set S := ∑ k ∈ range (N + 1), p k with hS
    have hS1 : S ≤ 1 := sum_range_le_one hp (N + 1)
    have hS2 : 1 - ε ≤ S := by
      have : renewalTail p N = 1 - S := rfl
      linarith
    have hSj : p j ≤ S :=
      single_le_sum (fun i _ => hp.nonneg i) (mem_range.2 (show j < N + 1 by omega))
    have hA : (S - p j) * (L - ε) ≤
        ∑ k ∈ (range (N + 1)).erase j, p k * realRenewalSeq p (n - k) := by
      calc (S - p j) * (L - ε) = ∑ k ∈ (range (N + 1)).erase j, p k * (L - ε) := by
            rw [← sum_mul, hS, ← add_sum_erase (range (N + 1)) p (a := j) (mem_range.2 (by omega))]
            ring
        _ ≤ ∑ k ∈ (range (N + 1)).erase j, p k * realRenewalSeq p (n - k) := by
            refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hM _ ?_) (hp.nonneg _)
            have := mem_range.1 (mem_of_mem_erase hi)
            omega
    have hB : 0 ≤ ∑ k ∈ Ico (N + 1) (n + 1), p k * realRenewalSeq p (n - k) :=
      sum_nonneg fun i _ => mul_nonneg (hp.nonneg _) (realRenewalSeq_nonneg hp _)
    set x := realRenewalSeq p (n - j)
    by_contra hx
    push Not at hx
    have h1 : p j * b ≤ p j * x := mul_le_mul_of_nonneg_left hx (hp.nonneg j)
    have h3 : (S - p j) * ε ≤ ε := by nlinarith
    have h4 : (1 - ε - p j) * L ≤ (S - p j) * L := mul_le_mul_of_nonneg_right (by linarith) hL.1
    have h5 : ε * L ≤ ε := mul_le_of_le_one_right hε0.le hL.2
    nlinarith

/-- **Closure of the shift property** (aperiodicity and Lemma D.7.4). If shifting by any `j` with
`p(j) > 0` preserves convergence to `λ` of subsequences of `u`, then there is `N₀` such that
`u(φ k − (N₀ + i)) → λ` for every `i` and every such subsequence. -/
theorem exists_shift_closure {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    {L : ℝ}
    (hshift : ∀ j, 0 < p j → ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
      Tendsto (fun k => realRenewalSeq p (φ k)) atTop (𝓝 L) →
      Tendsto (fun k => realRenewalSeq p (φ k - j)) atTop (𝓝 L)) :
    ∃ N₀, ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
      Tendsto (fun k => realRenewalSeq p (φ k)) atTop (𝓝 L) →
      ∀ i, Tendsto (fun k => realRenewalSeq p (φ k - (N₀ + i))) atTop (𝓝 L) := by
  set S : Set ℕ := {j | ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
      Tendsto (fun k => realRenewalSeq p (φ k)) atTop (𝓝 L) →
      Tendsto (fun k => realRenewalSeq p (φ k - j)) atTop (𝓝 L)} with hSdef
  have hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S := by
    intro a ha b hb φ hφ hlim
    have h1 := hb (fun k => φ k - a) ((tendsto_sub_atTop_nat a).comp hφ) (ha φ hφ hlim)
    simpa [Nat.sub_sub] using h1
  obtain ⟨j, hj0, hj⟩ := exists_pos_incr hp
  have hgcd : ∀ d, (∀ s ∈ S, d ∣ s) → d = 1 :=
    fun d hd => hap d fun n hn => hd n (hshift n hn)
  obtain ⟨N₀, hN₀⟩ := natAddClosed_eventually_mem hadd (hshift j hj) hj0 hgcd
  exact ⟨N₀, fun φ hφ hlim i => hN₀ (N₀ + i) (Nat.le_add_right _ _) φ hφ hlim⟩

/-- A real sequence that is frequently within every `ε` of `λ` has a subsequence tending to `λ`. -/
theorem exists_subseq_tendsto_of_frequently {v : ℕ → ℝ} {L : ℝ}
    (h : ∀ ε > 0, ∃ᶠ n in atTop, |v n - L| < ε) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ Tendsto (fun k => v (φ k)) atTop (𝓝 L) := by
  obtain ⟨φ, hmono, hφ⟩ := extraction_forall_of_frequently
    (P := fun k n => |v n - L| < 1 / ((k : ℝ) + 1)) fun k => h _ (by positivity)
  refine ⟨φ, hmono.tendsto_atTop, ?_⟩
  have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hφ k).le) h0

/-! ### Bounds at the upper and lower limits -/

/-- The renewal sequence is bounded above (by `1`). -/
theorem realRenewalSeq_isBoundedUnder_le {p : ℕ → ℝ} (hp : IsIncrementLaw p) :
    IsBoundedUnder (· ≤ ·) atTop (realRenewalSeq p) :=
  isBoundedUnder_of ⟨1, realRenewalSeq_le_one hp⟩

/-- The renewal sequence is bounded below (by `0`). -/
theorem realRenewalSeq_isBoundedUnder_ge {p : ℕ → ℝ} (hp : IsIncrementLaw p) :
    IsBoundedUnder (· ≥ ·) atTop (realRenewalSeq p) :=
  isBoundedUnder_of ⟨0, realRenewalSeq_nonneg hp⟩

/-- **The upper bound.** With `λ = lim sup u`, `λ ∑_{i<N} tail(i) ≤ 1` for every `N`. -/
theorem limsup_mul_sum_renewalTail_le {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (N : ℕ) : limsup (realRenewalSeq p) atTop * ∑ i ∈ range N, renewalTail p i ≤ 1 := by
  set L := limsup (realRenewalSeq p) atTop
  have hbdd := realRenewalSeq_isBoundedUnder_le hp
  have hcob := (realRenewalSeq_isBoundedUnder_ge hp).isCoboundedUnder_le
  have hup : ∀ ε > 0, ∀ᶠ n in atTop, realRenewalSeq p n ≤ L + ε := fun ε hε =>
    (eventually_lt_of_limsup_lt (by linarith : L < L + ε) hbdd).mono fun n h => h.le
  have hfreq : ∀ ε > 0, ∃ᶠ n in atTop, |realRenewalSeq p n - L| < ε := by
    intro ε hε
    refine ((frequently_lt_of_lt_limsup hcob (by linarith : L - ε < L)).and_eventually
      (hup (ε / 2) (by linarith))).mono fun n hn => ?_
    rw [abs_lt]
    constructor <;> linarith [hn.1, hn.2]
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_of_frequently hfreq
  obtain ⟨N₀, hN₀⟩ := exists_shift_closure hp hap
    (fun j hj φ hφ hlim => tendsto_shift_of_limsup hp hup hφ hlim hj)
  have hsum : Tendsto (fun k => ∑ i ∈ range N, renewalTail p i * realRenewalSeq p (φ k - (N₀ + i)))
      atTop (𝓝 (∑ i ∈ range N, renewalTail p i * L)) :=
    tendsto_finsetSum _ fun i _ => (hN₀ φ hφ hlim i).const_mul _
  rw [mul_comm, sum_mul]
  refine le_of_tendsto hsum ?_
  filter_upwards [hφ.eventually (eventually_ge_atTop (N₀ + N))] with k hk
  set n := φ k - N₀
  have hid := realConv_renewalTail_renewal hp.zero n
  rw [realConv_eq_sum_range] at hid
  calc ∑ i ∈ range N, renewalTail p i * realRenewalSeq p (φ k - (N₀ + i))
      = ∑ i ∈ range N, renewalTail p i * realRenewalSeq p (n - i) := by
        refine sum_congr rfl fun i _ => ?_
        rw [Nat.sub_sub]
    _ ≤ ∑ i ∈ range (n + 1), renewalTail p i * realRenewalSeq p (n - i) := by
        refine sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun i _ _ => ?_
        exact mul_nonneg (renewalTail_nonneg hp i) (realRenewalSeq_nonneg hp _)
    _ = 1 := hid

/-- **The lower bound.** With `μ = lim inf u` and `m_p < ∞`, `1 ≤ μ m_p`. -/
theorem one_le_liminf_mul_incrMean {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (hm : Summable fun n : ℕ => (n : ℝ) * p n) :
    1 ≤ liminf (realRenewalSeq p) atTop * incrMean p := by
  set L := liminf (realRenewalSeq p) atTop
  have hbdd := realRenewalSeq_isBoundedUnder_ge hp
  have hcob := (realRenewalSeq_isBoundedUnder_le hp).isCoboundedUnder_ge
  have hlow : ∀ ε > 0, ∀ᶠ n in atTop, L - ε ≤ realRenewalSeq p n := fun ε hε =>
    (eventually_lt_of_lt_liminf (by linarith : L - ε < L) hbdd).mono fun n h => h.le
  have hfreq : ∀ ε > 0, ∃ᶠ n in atTop, |realRenewalSeq p n - L| < ε := by
    intro ε hε
    refine ((frequently_lt_of_liminf_lt hcob (by linarith : L < L + ε)).and_eventually
      (hlow (ε / 2) (by linarith))).mono fun n hn => ?_
    rw [abs_lt]
    constructor <;> linarith [hn.1, hn.2]
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_of_frequently hfreq
  obtain ⟨N₀, hN₀⟩ := exists_shift_closure hp hap
    (fun j hj φ hφ hlim => tendsto_shift_of_liminf hp hlow hφ hlim hj)
  have htail := hasSum_renewalTail hp hm
  have hN : ∀ N, 1 ≤ L * ∑ i ∈ range N, renewalTail p i +
      (incrMean p - ∑ i ∈ range N, renewalTail p i) := by
    intro N
    have hsum : Tendsto (fun k =>
        ∑ i ∈ range N, renewalTail p i * realRenewalSeq p (φ k - (N₀ + i)) +
        (incrMean p - ∑ i ∈ range N, renewalTail p i)) atTop
        (𝓝 (∑ i ∈ range N, renewalTail p i * L + (incrMean p - ∑ i ∈ range N, renewalTail p i))) :=
      (tendsto_finsetSum _ fun i _ => (hN₀ φ hφ hlim i).const_mul _).add tendsto_const_nhds
    rw [mul_comm, sum_mul]
    refine ge_of_tendsto hsum ?_
    filter_upwards [hφ.eventually (eventually_ge_atTop (N₀ + N))] with k hk
    set n := φ k - N₀
    have hid := realConv_renewalTail_renewal hp.zero n
    rw [realConv_eq_sum_range, ← sum_range_add_sum_Ico _ (show N ≤ n + 1 by omega)] at hid
    have hIco : ∑ i ∈ Ico N (n + 1), renewalTail p i * realRenewalSeq p (n - i) ≤
        ∑ i ∈ Ico N (n + 1), renewalTail p i :=
      sum_le_sum fun i _ =>
        mul_le_of_le_one_right (renewalTail_nonneg hp i) (realRenewalSeq_le_one hp _)
    have hm' :
        ∑ i ∈ range N, renewalTail p i + ∑ i ∈ Ico N (n + 1), renewalTail p i ≤ incrMean p := by
      rw [sum_range_add_sum_Ico _ (show N ≤ n + 1 by omega)]
      exact sum_le_hasSum _ (fun i _ => renewalTail_nonneg hp i) htail
    have heq : ∑ i ∈ range N, renewalTail p i * realRenewalSeq p (φ k - (N₀ + i)) =
        ∑ i ∈ range N, renewalTail p i * realRenewalSeq p (n - i) := by
      refine sum_congr rfl fun i _ => ?_
      rw [Nat.sub_sub]
    rw [heq]
    linarith
  have hs : Tendsto (fun N => L * ∑ i ∈ range N, renewalTail p i +
      (incrMean p - ∑ i ∈ range N, renewalTail p i)) atTop
      (𝓝 (L * incrMean p + (incrMean p - incrMean p))) :=
    (htail.tendsto_sum_nat.const_mul L).add (tendsto_const_nhds.sub htail.tendsto_sum_nat)
  rw [sub_self, add_zero] at hs
  exact ge_of_tendsto' hs hN

/-! ### The renewal theorem -/

/-- **The renewal theorem, finite mean** (Erdős–Feller–Pollard; MT Theorem 13.2.3 with `a = δ₀`).
For an aperiodic increment law with finite mean `m_p`, `u(n) → 1/m_p`. -/
theorem renewal_theorem_of_summable {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p) (hm : Summable fun n : ℕ => (n : ℝ) * p n) :
    Tendsto (realRenewalSeq p) atTop (𝓝 (incrMean p)⁻¹) := by
  have hm1 := one_le_incrMean hp hm
  have hm0 : 0 < incrMean p := by linarith
  have htail := hasSum_renewalTail hp hm
  have hsup : limsup (realRenewalSeq p) atTop ≤ (incrMean p)⁻¹ := by
    have h := le_of_tendsto' (htail.tendsto_sum_nat.const_mul (limsup (realRenewalSeq p) atTop))
      (limsup_mul_sum_renewalTail_le hp hap)
    rw [← one_div, le_div_iff₀ hm0]
    exact h
  have hinf : (incrMean p)⁻¹ ≤ liminf (realRenewalSeq p) atTop := by
    rw [← one_div, div_le_iff₀ hm0]
    exact one_le_liminf_mul_incrMean hp hap hm
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup (realRenewalSeq_isBoundedUnder_le hp)
    (realRenewalSeq_isBoundedUnder_ge hp)

/-- **The renewal theorem, infinite mean.** For an aperiodic increment law with
`∑ n p(n) = ∞`, `u(n) → 0`. -/
theorem renewal_theorem_of_not_summable {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p) (hm : ¬ Summable fun n : ℕ => (n : ℝ) * p n) :
    Tendsto (realRenewalSeq p) atTop (𝓝 0) := by
  have hsup : limsup (realRenewalSeq p) atTop ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨N, hN⟩ := ((tendsto_sum_renewalTail_atTop hp hm).eventually_gt_atTop
      (1 / limsup (realRenewalSeq p) atTop)).exists
    have h := limsup_mul_sum_renewalTail_le hp hap N
    rw [div_lt_iff₀ hpos] at hN
    linarith
  have hinf : 0 ≤ liminf (realRenewalSeq p) atTop :=
    le_liminf_of_le (realRenewalSeq_isBoundedUnder_le hp).isCoboundedUnder_ge
      (Eventually.of_forall (realRenewalSeq_nonneg hp))
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup (realRenewalSeq_isBoundedUnder_le hp)
    (realRenewalSeq_isBoundedUnder_ge hp)

/-- **The renewal theorem** (Erdős–Feller–Pollard; MT §13.2). For an aperiodic increment law,
`u(n) → m_p⁻¹`, where `m_p = ∑ n p(n) ∈ [1, ∞]`. When the mean is infinite the Lean `tsum` is `0`
and `0⁻¹ = 0`, so the statement reads `u(n) → 0`, matching `1/∞ = 0`. -/
theorem renewal_theorem {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p) :
    Tendsto (realRenewalSeq p) atTop (𝓝 (incrMean p)⁻¹) := by
  by_cases hm : Summable fun n : ℕ => (n : ℝ) * p n
  · exact renewal_theorem_of_summable hp hap hm
  · have h0 : incrMean p = 0 := tsum_eq_zero_of_not_summable hm
    rw [h0, inv_zero]
    exact renewal_theorem_of_not_summable hp hap hm

/-! ### Delayed renewal sequences -/

/-- **The delayed renewal theorem** (MT (13.20), via Lemma D.7.1). For a summable delay sequence
`a ≥ 0`, `a ∗ u (n) → m_p⁻¹ ∑ a`. -/
theorem delayedRenewal_tendsto {a p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) :
    Tendsto (delayedRenewal a p) atTop (𝓝 ((incrMean p)⁻¹ * ∑' n, a n)) :=
  lemma_D_7_1 ha hsum (renewal_theorem hp hap)

/-- The delayed renewal theorem for a delay **law** `a` (`a ≥ 0`, `∑ a = 1`):
`a ∗ u (n) → m_p⁻¹`. -/
theorem delayedRenewal_tendsto_of_hasSum {a p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p) (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1) :
    Tendsto (delayedRenewal a p) atTop (𝓝 (incrMean p)⁻¹) := by
  have h := delayedRenewal_tendsto hp hap ha ha1.summable
  rwa [ha1.tsum_eq, mul_one] at h

/-- **Theorem 13.2.2** (MT p. 322). For delay laws `a, b` and an aperiodic increment law `p`,
`|a ∗ u (n) − b ∗ u (n)| → 0`. The book assumes `m_p < ∞` and notes (p. 322, §18.1.1) that the
result holds without it; the analytic proof gives that general form directly. -/
theorem theorem_13_2_2 {a b p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1) (hb : ∀ n, 0 ≤ b n) (hb1 : HasSum b 1) :
    Tendsto (fun n => |delayedRenewal a p n - delayedRenewal b p n|) atTop (𝓝 0) := by
  have h := (delayedRenewal_tendsto_of_hasSum hp hap ha ha1).sub
    (delayedRenewal_tendsto_of_hasSum hp hap hb hb1)
  rw [sub_self] at h
  simpa using h.abs

/-- The **equilibrium distribution** `e(n) = m_p⁻¹ ∑_{j > n} p(j)` (MT (13.34)). -/
noncomputable def equilibriumLaw (p : ℕ → ℝ) (n : ℕ) : ℝ := renewalTail p n / incrMean p

/-- The equilibrium distribution is nonnegative. -/
theorem equilibriumLaw_nonneg {p : ℕ → ℝ} (hp : IsIncrementLaw p) (n : ℕ) :
    0 ≤ equilibriumLaw p n :=
  div_nonneg (renewalTail_nonneg hp n) (tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg n)
    (hp.nonneg n))

/-- The equilibrium distribution is a probability when `m_p < ∞` (MT p. 322). -/
theorem equilibriumLaw_hasSum {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hm : Summable fun n : ℕ => (n : ℝ) * p n) : HasSum (equilibriumLaw p) 1 := by
  have hm0 : incrMean p ≠ 0 := by linarith [one_le_incrMean hp hm]
  have h := (hasSum_renewalTail hp hm).div_const (incrMean p)
  rwa [div_self hm0] at h

/-- **The equilibrium renewal identity** (MT (13.35)): `e ∗ u (n) = 1/m_p` for every `n`, so the
renewal process started in equilibrium has constant renewal probability. -/
theorem realConv_equilibriumLaw_renewal {p : ℕ → ℝ} (hp : IsIncrementLaw p) (n : ℕ) :
    realConv (equilibriumLaw p) (realRenewalSeq p) n = (incrMean p)⁻¹ := by
  have h : equilibriumLaw p = (incrMean p)⁻¹ • renewalTail p := by
    funext k
    simp [equilibriumLaw, div_eq_inv_mul]
  rw [h, realConv_smul_left, Pi.smul_apply, realConv_renewalTail_renewal hp.zero, smul_eq_mul,
    mul_one]

/-- **Theorem 13.2.3** (MT p. 323). For a delay law `a` and an aperiodic increment law `p` with
finite mean `m_p`, `|a ∗ u (n) − 1/m_p| → 0`. -/
theorem theorem_13_2_3 {a p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (_hm : Summable fun n : ℕ => (n : ℝ) * p n) (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1) :
    Tendsto (fun n => |delayedRenewal a p n - (incrMean p)⁻¹|) atTop (𝓝 0) := by
  have h := (delayedRenewal_tendsto_of_hasSum hp hap ha ha1).sub
    (tendsto_const_nhds (x := (incrMean p)⁻¹))
  rw [sub_self] at h
  simpa using h.abs

end MeynTweedie.VUniformErgodicity

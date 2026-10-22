/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.LinkedRenewal
import FErgodicity.RegularSets

/-!
# Sums of transition probabilities (MT §13.4)

Meyn and Tweedie, §13.4, pp. 329–333.

**Renewal sequences** (§13.4.1).
* `IsDelayLaw a`: a probability on `ℤ₊` (a delay distribution; `a(0) > 0` is allowed).
* `realConv_renewalTail_seqDiff_eq`: `ā ∗ Δv = v − a ∗ v`, with `ā(k) = Σ_{j>k} a(j)` and
  `Δv(k) = v(k) − v(k − 1)`, the identity (13.70).
* `hasSum_renewalTail_of_delay`: `Σ_k ā(k) = m_a = Σ_k k a(k)`.
* `abs_sub_realConv_summable` (13.71)–(13.72): if `m_a < ∞` and `Σ |Δv| < ∞`, then
  `Σₙ |v(n) − a ∗ v(n)| ≤ m_a Σ |Δv|`.
* `renewalVar p = Var(u)` (13.69), finite by `summable_seqDiff_realRenewalSeq` (`LinkedRenewal`).
* **Proposition 13.4.1** (`proposition_13_4_1`, p. 329): for an aperiodic `p` with `m_p < ∞` and
  delay laws `a`, `b` with finite means, `Σₙ |a ∗ u (n) − b ∗ u (n)| < ∞`, with the bound
  `(m_a + m_b) Var(u)`.
* `hasSum_mul_renewalTail`: `Σ_k k p̄(k) = (s_p − m_p)/2`, so the equilibrium law has mean
  `m_e = (s_p − m_p)/(2m_p)` (`hasSum_mul_equilibriumLaw`, p. 331), and
  `summable_mul_equilibriumLaw_iff`: `m_e < ∞` iff `s_p < ∞` (p. 331).
* **Proposition 13.4.2** (`proposition_13_4_2`, p. 332): if `s_p = Σ n² p(n) < ∞`, then
  `Σₙ |u(n) − m_p⁻¹| ≤ Var(u)(s_p − m_p)/(2m_p)`.

**Chains with an atom** (§13.4.2).
* `IsRegularMeasure P ψ λ` (`E_λ[τ_B] < ∞` for every `B ∈ B⁺(X)`, p. 332) and `IsRegularChain`
  (`X` is a countable union of regular sets) are the definitions of Chapter 11, in `RegularSets`;
  `IsRegularChain.isRegularMeasure_dirac`: in a regular chain every state is regular.
* `lintegral_meanReturnTime_eq_tsum`, `hasSum_renewalTail_entryLaw`, `entryLaw_mean`: the entry
  law `a_λ` has mean `E_λ[τ_α] = Σₙ P_λ(τ_α ≥ n + 1)`.
* `tvNorm_comp_pow_succ_le_atom`: the total variation form of (13.47),
  `‖λPⁿ⁺¹ − Pⁿ⁺¹(α, ·)‖ ≤ P_λ(τ_α ≥ n + 1) + |a_λ ∗ u − u| ∗ t₁ (n + 1)`.
* `summable_tvNorm_atom` ((13.77)–(13.80)):
  `Σₙ ‖λPⁿ⁺¹ − Pⁿ⁺¹(α, ·)‖ ≤ E_λ[τ_α](1 + Var(u) E_α[τ_α])`; `tsum_ofReal_tvNorm_le`, its
  pointwise form in `[0, ∞]`.
* **Theorem 13.4.3** (`theorem_13_4_3`, p. 332): (13.75) for regular `λ`, `μ`;
  `theorem_13_4_3_states`: (13.76) when every state is regular, and `theorem_13_4_3_regular`:
  (13.76) for a regular chain.
* `tsum_tsum_add_succ`, `tsum_mul_tabooKernel_le`, `lintegral_meanReturnTime_ne_top_of_sq`: if
  `E_α[τ_α²] < ∞`, then `E_π[τ_α] < ∞` (π is regular, p. 333).
* **Theorem 13.4.5** (`theorem_13_4_5`, p. 333): (13.83), `Σₙ ‖λPⁿ − π‖ < ∞` for regular `λ`.

**Hypotheses.** Theorems 13.4.3 and 13.4.5 are stated in the book for positive Harris chains;
positivity and aperiodicity suffice here, since a regular initial law reaches the atom almost
surely. Regularity is used only through `E_λ[τ_α] < ∞`.

Theorem 13.4.4 (chains without an atom) is in `SumsNoAtom`.

**Corrections.** None.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

/-! ### Delay laws and their tails -/

/-- A **delay law**: a probability `a` on `ℤ₊` (MT p. 320; `a(0) > 0` is allowed). -/
structure IsDelayLaw (a : ℕ → ℝ) : Prop where
  /-- The law is nonnegative. -/
  nonneg : ∀ n, 0 ≤ a n
  /-- The total mass is `1`. -/
  hasSum : HasSum a 1

/-- An increment law is a delay law. -/
theorem IsIncrementLaw.isDelayLaw {p : ℕ → ℝ} (hp : IsIncrementLaw p) : IsDelayLaw p :=
  ⟨hp.nonneg, hp.hasSum⟩

/-- The tails of a delay law are nonnegative. -/
theorem renewalTail_nonneg_of_delay {a : ℕ → ℝ} (ha : IsDelayLaw a) (n : ℕ) :
    0 ≤ renewalTail a n :=
  sub_nonneg.2 (sum_le_hasSum _ (fun i _ => ha.nonneg i) ha.hasSum)

/-- `ā(n) = Σ_{j > n} a(j)`. -/
theorem renewalTail_eq_tsum_of_delay {a : ℕ → ℝ} (ha : IsDelayLaw a) (n : ℕ) :
    renewalTail a n = ∑' j, a (j + (n + 1)) := by
  have h := ha.hasSum.summable.sum_add_tsum_nat_add (n + 1)
  rw [ha.hasSum.tsum_eq] at h
  rw [renewalTail]
  linarith

/-- **`Σ ā = m_a`** for a delay law with finite mean. -/
theorem hasSum_renewalTail_of_delay {a : ℕ → ℝ} (ha : IsDelayLaw a)
    (hm : Summable fun n : ℕ => (n : ℝ) * a n) :
    HasSum (renewalTail a) (∑' n : ℕ, (n : ℝ) * a n) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (renewalTail_nonneg_of_delay ha)]
  simp_rw [sum_range_renewalTail]
  have hA : Tendsto (fun N => ∑ j ∈ range (N + 1), (j : ℝ) * a j) atTop
      (𝓝 (∑' n : ℕ, (n : ℝ) * a n)) :=
    (hm.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hB : Tendsto (fun N : ℕ => (N : ℝ) * renewalTail a N) atTop (𝓝 0) := by
    have hup : Tendsto (fun N => (∑' n : ℕ, (n : ℝ) * a n) -
        ∑ j ∈ range (N + 1), (j : ℝ) * a j) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := ∑' n : ℕ, (n : ℝ) * a n)).sub hA
      rwa [sub_self] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun N => mul_nonneg (Nat.cast_nonneg N) (renewalTail_nonneg_of_delay ha N)) (fun N => ?_)
    have hsplit := hm.sum_add_tsum_nat_add (N + 1)
    have hshift := (summable_nat_add_iff (N + 1)).2 hm
    have hle : (N : ℝ) * renewalTail a N ≤
        ∑' j, ((j + (N + 1) : ℕ) : ℝ) * a (j + (N + 1)) := by
      rw [renewalTail_eq_tsum_of_delay ha, ← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun j => ?_)
        (((summable_nat_add_iff (N + 1)).2 ha.hasSum.summable).mul_left _) hshift
      refine mul_le_mul_of_nonneg_right ?_ (ha.nonneg _)
      push_cast
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith
  simpa using hA.add hB

/-- The differenced tails: `Δā = δ₀ − a`. -/
theorem seqDiff_renewalTail_eq (a : ℕ → ℝ) : seqDiff (renewalTail a) = deltaSeq - a := by
  funext n
  rcases n with _ | n
  · simp [seqDiff_zero, renewalTail, deltaSeq]
  · rw [seqDiff_succ, renewalTail_succ]
    simp [deltaSeq]

/-- **(13.70)**: `ā ∗ Δv = v − a ∗ v`. -/
theorem realConv_renewalTail_seqDiff_eq (a v : ℕ → ℝ) :
    realConv (renewalTail a) (seqDiff v) = v - realConv a v := by
  rw [← realConv_oneSubXSeq, ← realConv_assoc, realConv_comm (renewalTail a) oneSubXSeq,
    realConv_oneSubXSeq, seqDiff_renewalTail_eq, realConv_sub_left, realConv_deltaSeq_left]

/-- `Σ (f ∗ g) = (Σ f)(Σ g)` for nonnegative summable sequences. -/
theorem hasSum_realConv_of_nonneg {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (hsf : Summable f) (hsg : Summable g) :
    HasSum (realConv f g) ((∑' n, f n) * ∑' n, g n) := by
  have h := lemma_D_7_2_ii hf hg zero_le_one (by simpa using hsf) (by simpa using hsg)
  simpa using h

/-- **(13.71)–(13.72)**: if `a` is a delay law with mean `m_a < ∞` and `Σ |Δv| < ∞`, then
`Σₙ |v(n) − a ∗ v(n)| ≤ m_a Σ |Δv|`. -/
theorem abs_sub_realConv_summable {a v : ℕ → ℝ} (ha : IsDelayLaw a)
    (hm : Summable fun n : ℕ => (n : ℝ) * a n) (hv : Summable fun n => |seqDiff v n|) :
    Summable (fun n => |v n - realConv a v n|) ∧
      ∑' n, |v n - realConv a v n| ≤ (∑' n : ℕ, (n : ℝ) * a n) * ∑' n, |seqDiff v n| := by
  have htail := hasSum_renewalTail_of_delay ha hm
  have hconv := hasSum_realConv_of_nonneg (renewalTail_nonneg_of_delay ha) (fun n => abs_nonneg _)
    htail.summable hv
  rw [htail.tsum_eq] at hconv
  have hle : ∀ n, |v n - realConv a v n| ≤ realConv (renewalTail a) (fun k => |seqDiff v k|) n :=
    fun n => by
      have h := congrFun (realConv_renewalTail_seqDiff_eq a v) n
      rw [Pi.sub_apply] at h
      rw [← h, realConv, realConv]
      refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, abs_of_nonneg (renewalTail_nonneg_of_delay ha _)]
  have hs : Summable fun n => |v n - realConv a v n| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle hconv.summable
  exact ⟨hs, (hs.tsum_le_tsum hle hconv.summable).trans_eq hconv.tsum_eq⟩

/-- The variation `Var(u) = Σₙ |u(n) − u(n − 1)|` of the renewal sequence (13.69). -/
noncomputable def renewalVar (p : ℕ → ℝ) : ℝ := ∑' n, |seqDiff (realRenewalSeq p) n|

/-- **Proposition 13.4.1** (MT p. 329): for an aperiodic increment law `p` with finite mean and
delay laws `a`, `b` with finite means, `Σₙ |a ∗ u (n) − b ∗ u (n)| < ∞`; indeed the sum is at most
`(m_a + m_b) Var(u)`. -/
theorem proposition_13_4_1 {a b p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (hmp : Summable fun n : ℕ => (n : ℝ) * p n) (ha : IsDelayLaw a)
    (hma : Summable fun n : ℕ => (n : ℝ) * a n) (hb : IsDelayLaw b)
    (hmb : Summable fun n : ℕ => (n : ℝ) * b n) :
    Summable (fun n => |delayedRenewal a p n - delayedRenewal b p n|) ∧
      ∑' n, |delayedRenewal a p n - delayedRenewal b p n| ≤
        ((∑' n : ℕ, (n : ℝ) * a n) + ∑' n : ℕ, (n : ℝ) * b n) * renewalVar p := by
  have hv := summable_seqDiff_realRenewalSeq hp hap hmp
  obtain ⟨hsa, hla⟩ := abs_sub_realConv_summable ha hma hv
  obtain ⟨hsb, hlb⟩ := abs_sub_realConv_summable hb hmb hv
  have hle : ∀ n, |delayedRenewal a p n - delayedRenewal b p n| ≤
      |realRenewalSeq p n - realConv a (realRenewalSeq p) n| +
        |realRenewalSeq p n - realConv b (realRenewalSeq p) n| := fun n => by
    unfold delayedRenewal
    calc |realConv a (realRenewalSeq p) n - realConv b (realRenewalSeq p) n|
        = |(realRenewalSeq p n - realConv b (realRenewalSeq p) n) -
            (realRenewalSeq p n - realConv a (realRenewalSeq p) n)| := by ring_nf
      _ ≤ _ := (abs_sub _ _).trans (le_of_eq (add_comm _ _))
  have hs := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle (hsa.add hsb)
  refine ⟨hs, (hs.tsum_le_tsum hle (hsa.add hsb)).trans ?_⟩
  rw [hsa.tsum_add hsb, add_mul]
  exact add_le_add hla hlb

/-! ### Proposition 13.4.2 -/

/-- `Σ_{j<N} j p̄(j) = Σ_{i ≤ N} (i(i−1)/2) p(i) + (N(N−1)/2) p̄(N)`. -/
theorem sum_range_mul_renewalTail (p : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ range N, (j : ℝ) * renewalTail p j =
      ∑ i ∈ range (N + 1), ((i : ℝ) * ((i : ℝ) - 1) / 2) * p i +
        ((N : ℝ) * ((N : ℝ) - 1) / 2) * renewalTail p N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun i => ((i : ℝ) * ((i : ℝ) - 1) / 2) * p i)
      (N + 1), renewalTail_succ]
    push_cast
    ring

/-- **`Σ_k k p̄(k) = (s_p − m_p)/2`** when `s_p = Σ n² p(n) < ∞`. -/
theorem hasSum_mul_renewalTail {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hs : Summable fun n : ℕ => (n : ℝ) ^ 2 * p n) :
    HasSum (fun n : ℕ => (n : ℝ) * renewalTail p n)
      (((∑' n : ℕ, (n : ℝ) ^ 2 * p n) - ∑' n : ℕ, (n : ℝ) * p n) / 2) := by
  have hm : Summable fun n : ℕ => (n : ℝ) * p n :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg n) (hp.nonneg n))
      (fun n => by
        refine mul_le_mul_of_nonneg_right ?_ (hp.nonneg n)
        rcases n with _ | n
        · simp
        · have : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
          nlinarith) hs
  set c : ℕ → ℝ := fun i => ((i : ℝ) * ((i : ℝ) - 1) / 2) * p i
  have hc : ∀ i, c i = ((i : ℝ) ^ 2 * p i - (i : ℝ) * p i) / 2 := fun i => by simp only [c]; ring
  have hcs : HasSum c (((∑' n : ℕ, (n : ℝ) ^ 2 * p n) - ∑' n : ℕ, (n : ℝ) * p n) / 2) := by
    rw [show c = fun i : ℕ => ((i : ℝ) ^ 2 * p i - (i : ℝ) * p i) / 2 from funext hc]
    exact (hs.hasSum.sub hm.hasSum).div_const 2
  have hcnn : ∀ i, 0 ≤ c i := fun i => by
    simp only [c]
    rcases i with _ | i
    · simp
    · refine mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_) zero_le_two) (hp.nonneg _)
      push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => mul_nonneg (Nat.cast_nonneg n)
    (renewalTail_nonneg hp n))]
  simp_rw [sum_range_mul_renewalTail]
  have hA := (hcs.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hB : Tendsto (fun N : ℕ => ((N : ℝ) * ((N : ℝ) - 1) / 2) * renewalTail p N) atTop
      (𝓝 0) := by
    have hup : Tendsto (fun N => (∑' i, c i) - ∑ i ∈ range (N + 1), c i) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := ∑' i, c i)).sub
        ((hcs.summable.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1))
      rwa [sub_self] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun N => ?_)
      (fun N => ?_)
    · rcases N with _ | N
      · simp
      · refine mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_) zero_le_two)
          (renewalTail_nonneg hp _)
        push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    · have hsplit := hcs.summable.sum_add_tsum_nat_add (N + 1)
      have hle : ((N : ℝ) * ((N : ℝ) - 1) / 2) * renewalTail p N ≤ ∑' j, c (j + (N + 1)) := by
        rw [renewalTail_eq_tsum hp, ← tsum_mul_left]
        refine Summable.tsum_le_tsum (fun j => ?_)
          (((summable_nat_add_iff (N + 1)).2 hp.hasSum.summable).mul_left _)
          ((summable_nat_add_iff (N + 1)).2 hcs.summable)
        simp only [c]
        refine mul_le_mul_of_nonneg_right ?_ (hp.nonneg _)
        push_cast
        have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have h1 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith
      linarith
  simpa using hA.add hB

/-- The mean of the equilibrium law: `m_e = (s_p − m_p)/(2m_p)` (MT p. 331). -/
theorem hasSum_mul_equilibriumLaw {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hs : Summable fun n : ℕ => (n : ℝ) ^ 2 * p n) :
    HasSum (fun n : ℕ => (n : ℝ) * equilibriumLaw p n)
      (((∑' n : ℕ, (n : ℝ) ^ 2 * p n) - incrMean p) / (2 * incrMean p)) := by
  have h := (hasSum_mul_renewalTail hp hs).div_const (incrMean p)
  rw [div_div] at h
  refine h.congr_fun fun n => ?_
  simp only [equilibriumLaw]
  ring

/-- MT p. 331: for `m_p < ∞`, the equilibrium law has finite mean iff `s_p = Σ n² p(n) < ∞`. -/
theorem summable_mul_equilibriumLaw_iff {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hm : Summable fun n : ℕ => (n : ℝ) * p n) :
    Summable (fun n : ℕ => (n : ℝ) * equilibriumLaw p n) ↔
      Summable fun n : ℕ => (n : ℝ) ^ 2 * p n := by
  refine ⟨fun he => ?_, fun hs => (hasSum_mul_equilibriumLaw hp hs).summable⟩
  have hm1 : 0 < incrMean p := by linarith [one_le_incrMean hp hm]
  set c : ℕ → ℝ := fun i => ((i : ℝ) * ((i : ℝ) - 1) / 2) * p i
  have hcnn : ∀ i, 0 ≤ c i := fun i => by
    simp only [c]
    rcases i with _ | i
    · simp
    · refine mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_) zero_le_two) (hp.nonneg _)
      push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have htn : ∀ n : ℕ, 0 ≤ (n : ℝ) * renewalTail p n := fun n =>
    mul_nonneg (Nat.cast_nonneg n) (renewalTail_nonneg hp n)
  have ht : Summable fun n : ℕ => (n : ℝ) * renewalTail p n := by
    have := he.mul_left (incrMean p)
    refine this.congr fun n => ?_
    simp only [equilibriumLaw]
    field_simp
  have hcs : Summable c := by
    refine summable_of_sum_range_le hcnn (c := ∑' n : ℕ, (n : ℝ) * renewalTail p n) fun N => ?_
    calc ∑ i ∈ range N, c i ≤ ∑ i ∈ range (N + 1), c i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_succ N))
            fun i _ _ => hcnn i
      _ ≤ ∑ j ∈ range N, (j : ℝ) * renewalTail p j := by
          rw [sum_range_mul_renewalTail]
          refine le_add_of_nonneg_right ?_
          rcases N with _ | N
          · simp
          · refine mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_) zero_le_two)
              (renewalTail_nonneg hp _)
            push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      _ ≤ _ := sum_le_hasSum _ (fun j _ => htn j) ht.hasSum
  refine ((hcs.mul_left 2).add hm).congr fun n => ?_
  simp only [c]
  ring

/-- **Proposition 13.4.2** (MT p. 332): if `p` is aperiodic with `s_p = Σ n² p(n) < ∞`, then
`Σₙ |u(n) − m_p⁻¹| ≤ Var(u)(s_p − m_p)/(2m_p) < ∞`. -/
theorem proposition_13_4_2 {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (hs : Summable fun n : ℕ => (n : ℝ) ^ 2 * p n) :
    Summable (fun n => |realRenewalSeq p n - (incrMean p)⁻¹|) ∧
      ∑' n, |realRenewalSeq p n - (incrMean p)⁻¹| ≤
        renewalVar p * (((∑' n : ℕ, (n : ℝ) ^ 2 * p n) - incrMean p) / (2 * incrMean p)) := by
  have hm : Summable fun n : ℕ => (n : ℝ) * p n :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg n) (hp.nonneg n))
      (fun n => by
        refine mul_le_mul_of_nonneg_right ?_ (hp.nonneg n)
        rcases n with _ | n
        · simp
        · have : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
          nlinarith) hs
  have he : IsDelayLaw (equilibriumLaw p) :=
    ⟨equilibriumLaw_nonneg hp, equilibriumLaw_hasSum hp hm⟩
  have hme := hasSum_mul_equilibriumLaw hp hs
  have hv := summable_seqDiff_realRenewalSeq hp hap hm
  obtain ⟨hsum, hle⟩ := abs_sub_realConv_summable he hme.summable hv
  simp_rw [realConv_equilibriumLaw_renewal hp] at hsum hle
  refine ⟨hsum, hle.trans_eq ?_⟩
  rw [hme.tsum_eq, renewalVar, mul_comm]

/-! ### Chains with an atom (§13.4.2) -/

variable {X : Type*} [MeasurableSpace X]

/-- In a regular chain (a countable union of regular sets, Chapter 11) every state is a regular
initial measure. -/
theorem IsRegularChain.isRegularMeasure_dirac {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (h : IsRegularChain P ψ) (x : X) :
    IsRegularMeasure P ψ (Measure.dirac x) := by
  obtain ⟨C, hC, hU⟩ := h
  have hx : x ∈ ⋃ n, C n := hU ▸ mem_univ x
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx
  intro B hB hψB
  obtain ⟨M, hM, hle⟩ := (hC n).2 B hB hψB
  rw [lintegral_dirac' _ (measurable_meanReturnTime P hB)]
  exact ne_top_of_le_ne_top hM (hle x hn)

/-- `E_μ[τ_A] = Σₙ P_μ(τ_A ≥ n + 1)`. -/
theorem lintegral_meanReturnTime_eq_tsum (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (μ : Measure X) :
    ∫⁻ x, meanReturnTime P A x ∂μ = ∑' n, tabooSeq P hA μ n univ := by
  simp_rw [meanReturnTime_eq_tsum P hA]
  rw [lintegral_tsum fun n => (Kernel.measurable_coe _ MeasurableSet.univ).aemeasurable]
  exact tsum_congr fun n => by rw [tabooSeq, measure_kernel_apply _ _ MeasurableSet.univ]

/-- The entry law of a probability `λ` with `P_λ(τ_α < ∞) = 1` is an increment law. -/
theorem isIncrementLaw_entryLaw_of (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (μ : Measure X) [IsProbabilityMeasure μ]
    (hL : ∫⁻ x, hitProb P α x ∂μ = 1) : IsIncrementLaw (entryLaw P hα μ) := by
  refine ⟨entryLaw_nonneg P hα μ, rfl, ?_⟩
  have h := hasSum_entryLaw P hα μ
  rwa [hL, ENNReal.toReal_one] at h

/-- The tails of the entry law are `P_λ(τ_α ≥ n + 1)`, and they sum to `E_λ[τ_α]`. -/
theorem hasSum_renewalTail_entryLaw (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (μ : Measure X) [IsProbabilityMeasure μ]
    (hE : ∫⁻ x, meanReturnTime P α x ∂μ ≠ ∞) :
    HasSum (renewalTail (entryLaw P hα μ)) (∫⁻ x, meanReturnTime P α x ∂μ).toReal := by
  have hfin : ∀ n, tabooSeq P hα μ n univ ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (measure_ne_top μ univ) (tabooSeq_apply_le P hα μ n univ)
  have heq : renewalTail (entryLaw P hα μ) = fun n => (tabooSeq P hα μ n univ).toReal := by
    funext n
    rw [tabooSeq_univ_toReal P hα μ n, measureReal_def, measure_univ, ENNReal.toReal_one]
    rfl
  rw [heq, lintegral_meanReturnTime_eq_tsum P hα μ, ENNReal.tsum_toReal_eq hfin]
  exact ENNReal.hasSum_toReal (by rw [← lintegral_meanReturnTime_eq_tsum P hα μ]; exact hE)

/-- `E_λ[τ_α] < ∞` forces `P_λ(τ_α < ∞) = 1`. -/
theorem lintegral_hitProb_eq_one_of_lintegral_meanReturnTime (P : Kernel X X) [IsMarkovKernel P]
    {α : Set X} (hα : MeasurableSet α) (μ : Measure X) [IsProbabilityMeasure μ]
    (hE : ∫⁻ x, meanReturnTime P α x ∂μ ≠ ∞) : ∫⁻ x, hitProb P α x ∂μ = 1 := by
  have hmeas : Measurable (meanReturnTime P α) := by
    rw [show meanReturnTime P α = fun x => tabooPotKernel P hα x univ from
      funext (meanReturnTime_eq_tabooPotKernel P hα)]
    exact Kernel.measurable_coe _ MeasurableSet.univ
  have hae : ∀ᵐ x ∂μ, meanReturnTime P α x ≠ ∞ := (ae_lt_top hmeas hE).mono fun x hx => hx.ne
  rw [lintegral_congr_ae (hae.mono fun x hx => hitProb_eq_one_of_meanReturnTime_ne_top hα hx),
    lintegral_one, measure_univ]

/-- The mean of the entry law is `E_λ[τ_α]`. -/
theorem entryLaw_mean (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (μ : Measure X) [IsProbabilityMeasure μ]
    (hE : ∫⁻ x, meanReturnTime P α x ∂μ ≠ ∞) :
    Summable (fun n : ℕ => (n : ℝ) * entryLaw P hα μ n) ∧
      ∑' n : ℕ, (n : ℝ) * entryLaw P hα μ n = (∫⁻ x, meanReturnTime P α x ∂μ).toReal := by
  have hp := isIncrementLaw_entryLaw_of P hα μ
    (lintegral_hitProb_eq_one_of_lintegral_meanReturnTime P hα μ hE)
  have h1 := hasSum_renewalTail_entryLaw P hα μ hE
  have hm := (summable_renewalTail_iff hp).1 h1.summable
  exact ⟨hm, ((hasSum_renewalTail hp hm).unique h1)⟩

/-- **The total variation form of (13.47)**: for a finite `λ` and `n ≥ 0`,
`‖λPⁿ⁺¹ − Pⁿ⁺¹(α, ·)‖ ≤ P_λ(τ_α ≥ n + 1) + |a_λ ∗ u − u| ∗ t₁ (n + 1)`. -/
theorem tvNorm_comp_pow_succ_le_atom {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ) :
    tvNorm ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) ((P ^ (n + 1) : Kernel X X) a) ≤
      (tabooSeq P hα.1 μ n univ).toReal +
        realConv (fun k => |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k -
          atomRenewal P α a k|) (lastExitSeq P hα.1 a 1) (n + 1) := by
  have := isMarkovKernel_pow P (n + 1)
  set g := fun k => realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - atomRenewal P α a k
  set T : ℕ → Measure X := fun k => tabooKernel P hα.1 k a
  have hTfin : ∀ k B, T k B ≠ ∞ := fun k B =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (tabooKernel_apply_le_one P hα.1 k a B)
  have hE : ∀ B, tabooSeq P hα.1 μ n B ≠ ∞ := fun B =>
    ne_top_of_le_ne_top (measure_ne_top μ univ) (tabooSeq_apply_le P hα.1 μ n B)
  set σ₁ : Measure X := tabooSeq P hα.1 μ n +
    ∑ k ∈ range (n + 1), ENNReal.ofReal (g k) • T (n - k)
  set σ₂ : Measure X := ∑ k ∈ range (n + 1), ENNReal.ofReal (-g k) • T (n - k)
  have hσ₁B : ∀ B, σ₁ B = tabooSeq P hα.1 μ n B +
      ∑ k ∈ range (n + 1), ENNReal.ofReal (g k) * T (n - k) B := fun B => by
    simp only [σ₁, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  have hσ₂B : ∀ B, σ₂ B = ∑ k ∈ range (n + 1), ENNReal.ofReal (-g k) * T (n - k) B := fun B => by
    simp only [σ₂, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  have hsum1 : ∀ B, ∑ k ∈ range (n + 1), ENNReal.ofReal (g k) * T (n - k) B ≠ ∞ := fun B =>
    ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)
  have hsum2 : ∀ B, ∑ k ∈ range (n + 1), ENNReal.ofReal (-g k) * T (n - k) B ≠ ∞ := fun B =>
    ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)
  have : IsFiniteMeasure σ₁ := ⟨by
    rw [hσ₁B]; exact lt_top_iff_ne_top.2 (ENNReal.add_ne_top.2 ⟨hE _, hsum1 _⟩)⟩
  have : IsFiniteMeasure σ₂ := ⟨by rw [hσ₂B]; exact lt_top_iff_ne_top.2 (hsum2 _)⟩
  have hσ₁R : ∀ B, σ₁.real B = (tabooSeq P hα.1 μ n B).toReal +
      ∑ k ∈ range (n + 1), (ENNReal.ofReal (g k)).toReal * (T (n - k) B).toReal := fun B => by
    rw [measureReal_def, hσ₁B, ENNReal.toReal_add (hE B) (hsum1 B), ENNReal.toReal_sum fun k _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)]
    simp_rw [ENNReal.toReal_mul]
  have hσ₂R : ∀ B, σ₂.real B =
      ∑ k ∈ range (n + 1), (ENNReal.ofReal (-g k)).toReal * (T (n - k) B).toReal := fun B => by
    rw [measureReal_def, hσ₂B, ENNReal.toReal_sum fun k _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTfin _ _)]
    simp_rw [ENNReal.toReal_mul]
  have hind : ∀ B, MeasurableSet B → ∀ y, B.indicator (1 : X → ℝ≥0∞) y ≤ 1 := fun B _ y => by
    by_cases hy : y ∈ B <;> simp [hy]
  refine (tvNorm_le_of_sub_eq (σ₁ := σ₁) (σ₂ := σ₂) fun B hB => ?_).trans (le_of_eq ?_)
  · have h1 := lintegral_comp_pow_succ_atom_toReal hα ha μ ENNReal.one_ne_top (hind B hB) n
    have h2 := lintegral_pow_succ_atom_toReal hα ha ENNReal.one_ne_top (hind B hB) n
    simp only [lintegral_indicator_one hB] at h1 h2
    rw [measureReal_def, measureReal_def, h1, h2, hσ₁R, hσ₂R, add_sub_assoc,
      ← Pi.sub_apply (realConv _ _), ← realConv_sub_left, realConv_lastExitSeq_succ]
    simp only [lintegral_indicator_one hB]
    have hk : ∀ k ∈ range (n + 1), (realConv (entryLaw P hα.1 μ) (atomRenewal P α a) -
        atomRenewal P α a) k * (T (n - k) B).toReal =
        (ENNReal.ofReal (g k)).toReal * (T (n - k) B).toReal -
          (ENNReal.ofReal (-g k)).toReal * (T (n - k) B).toReal := fun k _ => by
      rw [← sub_mul, toReal_ofReal_sub_ofReal_neg]
      rfl
    rw [Finset.sum_congr rfl hk, Finset.sum_sub_distrib]
    ring
  · rw [hσ₁R, hσ₂R, realConv_lastExitSeq_succ, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_mul, toReal_ofReal_add_ofReal_neg]
    simp only [T, Pi.one_apply, lintegral_one]
    rfl

/-- **The summability bound** behind Theorem 13.4.3: if `α` is an atom with `L(α, α) = 1`,
`E_α[τ_α] < ∞` and an aperiodic return-time law, and `λ` is a probability with
`E_λ[τ_α] < ∞`, then `Σₙ ‖λPⁿ⁺¹ − Pⁿ⁺¹(α, ·)‖ ≤ E_λ[τ_α](1 + Var(u) E_α[τ_α]) < ∞`. -/
theorem summable_tvNorm_atom {P : Kernel X X} [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {a : X} (ha : a ∈ α) (hLa : hitProb P α a = 1) (hEa : meanReturnTime P α a ≠ ∞)
    (hap : IsAperiodicLaw (entryLaw P hα.1 (Measure.dirac a))) (μ : Measure X)
    [IsProbabilityMeasure μ] (hE : ∫⁻ x, meanReturnTime P α x ∂μ ≠ ∞) :
    Summable (fun n => tvNorm ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) ((P ^ (n + 1) : Kernel X X) a)) ∧
      ∑' n, tvNorm ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) ((P ^ (n + 1) : Kernel X X) a) ≤
        (∫⁻ x, meanReturnTime P α x ∂μ).toReal *
          (1 + renewalVar (entryLaw P hα.1 (Measure.dirac a)) *
            (meanReturnTime P α a).toReal) := by
  set p := entryLaw P hα.1 (Measure.dirac a)
  set Eμ := (∫⁻ x, meanReturnTime P α x ∂μ).toReal
  set Ea := (meanReturnTime P α a).toReal
  have hp := isIncrementLaw_entryLaw P hα.1 hLa
  have hmp : Summable fun n : ℕ => (n : ℝ) * p n := by
    have h1 : HasSum (renewalTail p) Ea := by
      rw [show renewalTail p = fun n => (tabooKernel P hα.1 n a univ).toReal from
        funext (renewalTail_entryLaw P hα.1 a)]
      exact hasSum_tabooKernel_univ P hα.1 a hEa
    exact (summable_renewalTail_iff hp).1 h1.summable
  have hu : atomRenewal P α a = realRenewalSeq p := atomRenewal_eq_realRenewalSeq hα ha
  have hv := summable_seqDiff_realRenewalSeq hp hap hmp
  obtain ⟨hma, hmean⟩ := entryLaw_mean P hα.1 μ hE
  have hdelay : IsDelayLaw (entryLaw P hα.1 μ) := (isIncrementLaw_entryLaw_of P hα.1 μ
    (lintegral_hitProb_eq_one_of_lintegral_meanReturnTime P hα.1 μ hE)).isDelayLaw
  obtain ⟨hgs, hgle⟩ := abs_sub_realConv_summable hdelay hma hv
  -- the sequence `|a_λ ∗ u − u|`
  set w := fun k => |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - atomRenewal P α a k|
  have hw : w = fun k => |realRenewalSeq p k - realConv (entryLaw P hα.1 μ) (realRenewalSeq p) k|
    := by funext k; simp only [w, hu]; rw [abs_sub_comm]
  have hws : Summable w := by rw [hw]; exact hgs
  have hwle : ∑' k, w k ≤ Eμ * renewalVar p := by
    rw [hw]
    refine hgle.trans_eq ?_
    rw [hmean]
    rfl
  -- the tails `t₁`
  have ht : HasSum (lastExitSeq P hα.1 a 1) Ea := by
    have h := hasSum_tabooKernel_univ P hα.1 a hEa
    refine (hasSum_nat_add_iff' 1).1 ?_
    simpa [lastExitSeq_succ] using h
  have hconv := hasSum_realConv_of_nonneg (fun k => abs_nonneg _)
    (lastExitSeq_nonneg P hα.1 a 1) hws ht.summable
  have hconv1 := (summable_nat_add_iff 1).2 hconv.summable
  have hT := hasSum_renewalTail_entryLaw P hα.1 μ hE
  have hTeq : renewalTail (entryLaw P hα.1 μ) = fun n => (tabooSeq P hα.1 μ n univ).toReal := by
    funext n
    rw [tabooSeq_univ_toReal P hα.1 μ n, measureReal_def, measure_univ, ENNReal.toReal_one]
    rfl
  rw [hTeq] at hT
  have hbd := fun n => tvNorm_comp_pow_succ_le_atom hα ha μ n
  have hsb : Summable fun n => (tabooSeq P hα.1 μ n univ).toReal +
      realConv w (lastExitSeq P hα.1 a 1) (n + 1) := hT.summable.add hconv1
  have hs := Summable.of_nonneg_of_le (fun n => tvNorm_nonneg _ _) hbd hsb
  refine ⟨hs, (hs.tsum_le_tsum hbd hsb).trans ?_⟩
  rw [hT.summable.tsum_add hconv1, hT.tsum_eq]
  have h1 : ∑' n, realConv w (lastExitSeq P hα.1 a 1) (n + 1) ≤
      (∑' k, w k) * ∑' k, lastExitSeq P hα.1 a 1 k := by
    rw [← hconv.tsum_eq, hconv.summable.tsum_eq_zero_add]
    exact le_add_of_nonneg_left (realConv_nonneg (fun k => abs_nonneg _)
      (lastExitSeq_nonneg P hα.1 a 1) 0)
  rw [ht.tsum_eq] at h1
  have hEa0 : 0 ≤ Ea := ENNReal.toReal_nonneg
  have h2 : (∑' k, w k) * Ea ≤ Eμ * renewalVar p * Ea := mul_le_mul_of_nonneg_right hwle hEa0
  nlinarith

/-- The pointwise summability bound: `Σₙ ‖Pⁿ⁺¹(x, ·) − Pⁿ⁺¹(α, ·)‖ ≤ E_x[τ_α](1 + Var(u)E_α[τ_α])`,
in `[0, ∞]`. -/
theorem tsum_ofReal_tvNorm_le {P : Kernel X X} [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {a : X} (ha : a ∈ α) (hLa : hitProb P α a = 1) (hEa : meanReturnTime P α a ≠ ∞)
    (hap : IsAperiodicLaw (entryLaw P hα.1 (Measure.dirac a))) (x : X) :
    ∑' n, ENNReal.ofReal (tvNorm ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) a)) ≤
      meanReturnTime P α x * ENNReal.ofReal (1 + renewalVar (entryLaw P hα.1 (Measure.dirac a)) *
        (meanReturnTime P α a).toReal) := by
  have hV : 0 ≤ renewalVar (entryLaw P hα.1 (Measure.dirac a)) :=
    tsum_nonneg fun _ => abs_nonneg _
  have hc : ENNReal.ofReal (1 + renewalVar (entryLaw P hα.1 (Measure.dirac a)) *
      (meanReturnTime P α a).toReal) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  by_cases hx : meanReturnTime P α x = ∞
  · rw [hx, ENNReal.top_mul hc]; exact le_top
  · have hEx : ∫⁻ y, meanReturnTime P α y ∂Measure.dirac x ≠ ∞ := by
      rwa [lintegral_dirac' _ (measurable_meanReturnTime P hα.1)]
    obtain ⟨hs, hle⟩ := summable_tvNorm_atom hα ha hLa hEa hap (Measure.dirac x) hEx
    simp_rw [dirac_kernel, lintegral_dirac' _ (measurable_meanReturnTime P hα.1)] at hs hle
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => tvNorm_nonneg _ _) hs,
      ← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hle

/-- **Theorem 13.4.3** (MT p. 332): for a positive aperiodic chain with an accessible atom and
regular initial distributions `λ`, `μ`,
`∫ λ(dx) ∫ μ(dy) Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞` (13.75). -/
theorem theorem_13_4_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsRegularMeasure P ψ μ) (hν : IsRegularMeasure P ψ ν) :
    ∫⁻ x, ∫⁻ y, ∑' n, ENNReal.ofReal (tvNorm ((P ^ (n + 1) : Kernel X X) x)
      ((P ^ (n + 1) : Kernel X X) y)) ∂ν ∂μ ≠ ∞ := by
  obtain ⟨a, ha⟩ : α.Nonempty := nonempty_of_measure_ne_zero h.2.2.ne'
  obtain ⟨π, hπp, hπ⟩ := hpos.2
  have hrec := proposition_10_1_1 hpos
  have hrep := eq_smul_atomMeasure_of_accessible h hrec ha hπ
  have hEa := meanReturnTime_ne_top_of_rep P h.1.1 a hrep
  have hLa := (h.isRecurrentChain_iff ha).1 hrec
  have hap' := isAperiodicLaw_entryLaw h hap ha
  set c := ENNReal.ofReal (1 + renewalVar (entryLaw P h.1.1 (Measure.dirac a)) *
    (meanReturnTime P α a).toReal)
  set F : X → ℝ≥0∞ := fun x => meanReturnTime P α x * c
  have hF : Measurable F := (measurable_meanReturnTime P h.1.1).mul_const c
  have hpt := tsum_ofReal_tvNorm_le h.1 ha hLa hEa hap'
  have hpair : ∀ x y, ∑' n, ENNReal.ofReal (tvNorm ((P ^ (n + 1) : Kernel X X) x)
      ((P ^ (n + 1) : Kernel X X) y)) ≤ F x + F y := fun x y => by
    refine le_trans ?_ (add_le_add (hpt x) (hpt y))
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun n => ?_
    have := isMarkovKernel_pow P (n + 1)
    rw [← ENNReal.ofReal_add (tvNorm_nonneg _ _) (tvNorm_nonneg _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc tvNorm ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y)
        ≤ tvNorm ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) a) +
          tvNorm ((P ^ (n + 1) : Kernel X X) a) ((P ^ (n + 1) : Kernel X X) y) :=
          tvNorm_triangle _ _ _
      _ = _ := by rw [tvNorm_comm ((P ^ (n + 1) : Kernel X X) a)]
  have hbound : ∫⁻ x, ∫⁻ y, ∑' n, ENNReal.ofReal (tvNorm ((P ^ (n + 1) : Kernel X X) x)
      ((P ^ (n + 1) : Kernel X X) y)) ∂ν ∂μ ≤ ∫⁻ x, F x ∂μ + ∫⁻ y, F y ∂ν := by
    calc _ ≤ ∫⁻ x, ∫⁻ y, (F x + F y) ∂ν ∂μ :=
          lintegral_mono fun x => lintegral_mono fun y => hpair x y
      _ = ∫⁻ x, (F x + ∫⁻ y, F y ∂ν) ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [lintegral_add_left' measurable_const.aemeasurable, lintegral_const, measure_univ,
            mul_one]
      _ = ∫⁻ x, F x ∂μ + ∫⁻ y, F y ∂ν := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  refine ne_top_of_le_ne_top ?_ hbound
  refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
  · rw [lintegral_mul_const _ (measurable_meanReturnTime P h.1.1)]
    exact ENNReal.mul_ne_top (hμ α h.1.1 h.2.2) ENNReal.ofReal_ne_top
  · rw [lintegral_mul_const _ (measurable_meanReturnTime P h.1.1)]
    exact ENNReal.mul_ne_top (hν α h.1.1 h.2.2) ENNReal.ofReal_ne_top

/-- **Theorem 13.4.3**, (13.76): for a positive aperiodic chain with an accessible atom all of whose
states are regular, `Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞` for all `x`, `y`. -/
theorem theorem_13_4_3_states {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α)
    (hreg : ∀ z, IsRegularMeasure P ψ (Measure.dirac z)) (x y : X) :
    Summable fun n => tvNorm ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y) := by
  obtain ⟨a, ha⟩ : α.Nonempty := nonempty_of_measure_ne_zero h.2.2.ne'
  obtain ⟨π, hπp, hπ⟩ := hpos.2
  have hrec := proposition_10_1_1 hpos
  have hrep := eq_smul_atomMeasure_of_accessible h hrec ha hπ
  have hEa := meanReturnTime_ne_top_of_rep P h.1.1 a hrep
  have hLa := (h.isRecurrentChain_iff ha).1 hrec
  have hap' := isAperiodicLaw_entryLaw h hap ha
  have hE : ∀ z, ∫⁻ w, meanReturnTime P α w ∂Measure.dirac z ≠ ∞ := fun z => hreg z α h.1.1 h.2.2
  have hs : ∀ z, Summable fun n =>
      tvNorm ((P ^ (n + 1) : Kernel X X) z) ((P ^ (n + 1) : Kernel X X) a) := fun z => by
    have := (summable_tvNorm_atom h.1 ha hLa hEa hap' (Measure.dirac z) (hE z)).1
    simpa [dirac_kernel] using this
  refine Summable.of_nonneg_of_le (fun n => tvNorm_nonneg _ _) (fun n => ?_) ((hs x).add (hs y))
  have := isMarkovKernel_pow P (n + 1)
  calc tvNorm ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y)
      ≤ tvNorm ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) a) +
        tvNorm ((P ^ (n + 1) : Kernel X X) a) ((P ^ (n + 1) : Kernel X X) y) :=
        tvNorm_triangle _ _ _
    _ = _ := by rw [tvNorm_comm ((P ^ (n + 1) : Kernel X X) a)]

/-- **Theorem 13.4.3**, (13.76): for a positive aperiodic regular chain with an accessible atom,
`Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞` for all `x`, `y`. -/
theorem theorem_13_4_3_regular {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α)
    (hreg : IsRegularChain P ψ) (x y : X) :
    Summable fun n => tvNorm ((P ^ (n + 1) : Kernel X X) x) ((P ^ (n + 1) : Kernel X X) y) :=
  theorem_13_4_3_states hpos hap h hreg.isRegularMeasure_dirac x y

/-! ### Theorem 13.4.5 -/

/-- `Σ_k Σₙ f(n + k + 1) = Σ_m m f(m)` in `[0, ∞]`. -/
theorem tsum_tsum_add_succ (f : ℕ → ℝ≥0∞) :
    ∑' k, ∑' n, f (n + (k + 1)) = ∑' m : ℕ, (m : ℝ≥0∞) * f m := by
  have h1 : ∀ k, ∑' n, f (n + (k + 1)) = ∑' m, (Set.Ioi k).indicator f m := fun k => by
    have hsum := (ENNReal.summable
      (f := fun n => (Set.Ioi k).indicator f (n + (k + 1)))).sum_add_tsum_nat_add'
    rw [← hsum]
    have hz : ∑ i ∈ range (k + 1), (Set.Ioi k).indicator f i = 0 :=
      Finset.sum_eq_zero fun i hi => indicator_of_notMem (by
        simp only [Finset.mem_range] at hi
        simp only [Set.mem_Ioi, not_lt]
        omega) _
    rw [hz, zero_add]
    exact tsum_congr fun n => (indicator_of_mem (by simp only [Set.mem_Ioi]; omega) _).symm
  have h2 : ∀ m : ℕ, (m : ℝ≥0∞) * f m = ∑' k, (Set.Iio m).indicator (fun _ => f m) k := fun m => by
    rw [tsum_eq_sum (s := range m) fun k hk => indicator_of_notMem (by
      simp only [Finset.mem_range, not_lt] at hk
      simp only [Set.mem_Iio, not_lt]
      exact hk) _]
    rw [Finset.sum_congr rfl fun k hk => indicator_of_mem (by
      simpa only [Finset.mem_range, Set.mem_Iio] using hk) _, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  simp_rw [h1, h2]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun m => tsum_congr fun k => ?_
  by_cases hkm : k < m
  · rw [indicator_of_mem (show m ∈ Set.Ioi k from hkm),
      indicator_of_mem (show k ∈ Set.Iio m from hkm)]
  · rw [indicator_of_notMem (show m ∉ Set.Ioi k from hkm),
      indicator_of_notMem (show k ∉ Set.Iio m from hkm)]

/-- `Σ_m m P_a(τ_A ≥ m + 1) ≤ E_a[τ_A²]`. -/
theorem tsum_mul_tabooKernel_le (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (a : X) :
    ∑' m : ℕ, (m : ℝ≥0∞) * tabooKernel P hA m a univ ≤
      ∫⁻ ω, (ENat.toENNReal (firstReturn A ω)) ^ 2 ∂pathKernel P a := by
  have hS : ∀ m, tabooKernel P hA m a univ =
      ∫⁻ ω, {ω : ℕ → X | WithTop.some (m + 1) ≤ firstReturn A ω}.indicator 1 ω ∂pathKernel P a :=
    fun m => by
      rw [← tabooProb_eq_tabooKernel P hA m a MeasurableSet.univ, tabooProb,
        lintegral_indicator_one (measurableSet_le_firstReturn hA (m + 1))]
      congr 1
      ext ω
      simp
  simp_rw [hS]
  calc ∑' m : ℕ, (m : ℝ≥0∞) * ∫⁻ ω, {ω : ℕ → X | WithTop.some (m + 1) ≤ firstReturn A ω}.indicator 1
        ω ∂pathKernel P a
      = ∫⁻ ω, ∑' m : ℕ, (m : ℝ≥0∞) *
          {ω : ℕ → X | WithTop.some (m + 1) ≤ firstReturn A ω}.indicator 1
          ω ∂pathKernel P a := by
        rw [lintegral_tsum fun m => ((measurable_one.indicator
          (measurableSet_le_firstReturn hA (m + 1))).const_mul _).aemeasurable]
        exact tsum_congr fun m => (lintegral_const_mul _ (measurable_one.indicator
          (measurableSet_le_firstReturn hA (m + 1)))).symm
    _ ≤ ∫⁻ ω, (ENat.toENNReal (firstReturn A ω)) ^ 2 ∂pathKernel P a := by
        refine lintegral_mono fun ω => ?_
        cases h : firstReturn A ω with
        | top =>
          have htop : (ENat.toENNReal (⊤ : ℕ∞)) ^ 2 = ⊤ := by
            rw [ENat.toENNReal_top, ENNReal.top_pow two_ne_zero]
          exact le_top.trans_eq htop.symm
        | coe N =>
          rw [tsum_eq_sum (s := range N) fun m hm => by
            simp only [Finset.mem_range, not_lt] at hm
            have hnot : ω ∉ {ω : ℕ → X | WithTop.some (m + 1) ≤ firstReturn A ω} := by
              intro hh
              change WithTop.some (m + 1) ≤ firstReturn A ω at hh
              rw [h] at hh
              have := WithTop.coe_le_coe.1 hh
              omega
            rw [indicator_of_notMem hnot, mul_zero]]
          calc ∑ m ∈ range N, (m : ℝ≥0∞) *
                {ω : ℕ → X | WithTop.some (m + 1) ≤ firstReturn A ω}.indicator 1 ω
              ≤ ∑ m ∈ range N, (N : ℝ≥0∞) := Finset.sum_le_sum fun m hm => by
                simp only [Finset.mem_range] at hm
                calc (m : ℝ≥0∞) * _ ≤ (m : ℝ≥0∞) * 1 := by
                      gcongr
                      unfold Set.indicator
                      split_ifs <;> simp
                  _ ≤ N := by rw [mul_one]; exact_mod_cast hm.le
            _ = (ENat.toENNReal (N : WithTop ℕ)) ^ 2 := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sq]
                exact congrArg (· * _) (ENat.toENNReal_coe N).symm |>.trans
                  (congrArg _ (ENat.toENNReal_coe N).symm)

/-- `∫_{αᶜ} _αPᵏ⁺¹(x, dy) E_y[τ_α] = Σₙ _αPⁿ⁺ᵏ⁺²(x, X)`. -/
theorem setLIntegral_compl_meanReturnTime (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (k : ℕ) (x : X) :
    ∫⁻ w in Aᶜ, meanReturnTime P A w ∂tabooKernel P hA k x =
      ∑' n, tabooKernel P hA (n + (k + 1)) x univ := by
  simp_rw [meanReturnTime_eq_tsum P hA]
  rw [lintegral_tsum fun n => (Kernel.measurable_coe _ MeasurableSet.univ).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [tabooKernel_add_succ P hA k n x, measure_kernel_apply _ _ MeasurableSet.univ]

/-- If `E_α[τ_α²] < ∞` and `π = π(α) μ°_α`, then `E_π[τ_α] < ∞`: the invariant probability is
regular (MT p. 333). -/
theorem lintegral_meanReturnTime_ne_top_of_sq {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα.1 a)
    (h2 : ∫⁻ ω, (ENat.toENNReal (firstReturn α ω)) ^ 2 ∂pathKernel P a ≠ ∞) :
    ∫⁻ x, meanReturnTime P α x ∂π ≠ ∞ := by
  have hEa := meanReturnTime_ne_top_of_rep P hα.1 a hπ
  have hconst : ∀ w ∈ α, meanReturnTime P α w = meanReturnTime P α a := fun w hw => by
    rw [meanReturnTime_eq_tabooPotKernel P hα.1, meanReturnTime_eq_tabooPotKernel P hα.1,
      hα.tabooPotKernel_eq hw ha]
  have hk : ∀ k, ∫⁻ w, meanReturnTime P α w ∂tabooKernel P hα.1 k a =
      meanReturnTime P α a * tabooKernel P hα.1 k a α +
        ∑' n, tabooKernel P hα.1 (n + (k + 1)) a univ := fun k => by
    rw [← lintegral_add_compl _ hα.1, setLIntegral_congr_fun hα.1 hconst, setLIntegral_const,
      setLIntegral_compl_meanReturnTime]
  have h1 : ∫⁻ x, meanReturnTime P α x ∂π =
      π α * (meanReturnTime P α a * hitProb P α a +
        ∑' m : ℕ, (m : ℝ≥0∞) * tabooKernel P hα.1 m a univ) := by
    conv_lhs => rw [hπ]
    rw [lintegral_smul_measure, smul_eq_mul, atomMeasure, tabooPotKernel, Kernel.sum_apply,
      lintegral_sum_measure]
    simp_rw [hk]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ← hitProb_eq_tsum P hα.1 a,
      tsum_tsum_add_succ (fun m => tabooKernel P hα.1 m a univ)]
  rw [h1]
  refine ENNReal.mul_ne_top (measure_ne_top π α) (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hEa
    (ne_top_of_le_ne_top ENNReal.one_ne_top (hitProb_le_one P α a)), ?_⟩)
  exact ne_top_of_le_ne_top h2 (tsum_mul_tabooKernel_le P hα.1 a)

/-- **Theorem 13.4.5** (MT p. 333): for a positive aperiodic chain with an accessible atom `α`
with `E_α[τ_α²] < ∞` (13.82), every regular initial distribution `λ` satisfies
`Σₙ ‖λPⁿ − π‖ < ∞` (13.83). -/
theorem theorem_13_4_5 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) {α : Set X} (h : IsAccessibleAtom P ψ α)
    {a : X} (ha : a ∈ α)
    (h2 : ∫⁻ ω, (ENat.toENNReal (firstReturn α ω)) ^ 2 ∂pathKernel P a ≠ ∞)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : IsRegularMeasure P ψ μ) :
    Summable fun n => tvNorm ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) π := by
  have hrec := proposition_10_1_1 hpos
  have hrep := eq_smul_atomMeasure_of_accessible h hrec ha hπ
  have hEa := meanReturnTime_ne_top_of_rep P h.1.1 a hrep
  have hLa := (h.isRecurrentChain_iff ha).1 hrec
  have hap' := isAperiodicLaw_entryLaw h hap ha
  have hEπ := lintegral_meanReturnTime_ne_top_of_sq h.1 ha hrep h2
  have hsμ := (summable_tvNorm_atom h.1 ha hLa hEa hap' μ (hμ α h.1.1 h.2.2)).1
  have hsπ := (summable_tvNorm_atom h.1 ha hLa hEa hap' π hEπ).1
  refine Summable.of_nonneg_of_le (fun n => tvNorm_nonneg _ _) (fun n => ?_) (hsμ.add hsπ)
  have := isMarkovKernel_pow P (n + 1)
  calc tvNorm ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) π
      = tvNorm ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) ((P ^ (n + 1) : Kernel X X) ∘ₘ π) := by
        rw [(hπ.pow (n + 1) :)]
    _ ≤ tvNorm ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) ((P ^ (n + 1) : Kernel X X) a) +
        tvNorm ((P ^ (n + 1) : Kernel X X) a) ((P ^ (n + 1) : Kernel X X) ∘ₘ π) :=
        tvNorm_triangle _ _ _
    _ = _ := by rw [tvNorm_comm ((P ^ (n + 1) : Kernel X X) a)]

end MeynTweedie.FErgodicity

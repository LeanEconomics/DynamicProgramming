/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.IIDLIL
import Mathlib.Probability.StrongLaw
import Mathlib.Algebra.Order.Floor.Semifield


/-!
# The LIL for one-dependent sequences and random indices (MT §17.2–17.3)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/DependentLIL.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Tools that carry the Hartman–Wintner LIL (`IIDLIL`) from i.i.d. cycle sums to sums along a chain:
the random-index replacement of MT (17.17)–(17.20) and (17.33)–(17.36) for the LIL, the
negligibility of the remainders between regeneration times, and the LIL for the one-dependent
cycle sums of a split `m`-skeleton (MT Theorem 17.3.1, the blocking step (17.36), p. 442).

**Deterministic transfer.**
* `LILBound.of_tendsto_sub`, `HasLIL.of_tendsto_sub`: perturbations that are
  `o(√(n log log n))` do not change the LIL; `tendsto_div_lilScale_of_sqrt`: `o(√n)` suffices.
* **The random-index step** (`LILBound.comp_index`, `HasLIL.comp_index`): if `HasLIL s γ`,
  `γ ≥ 0`, and the integer indices `Tₙ` have increments at most `1` (as the number of completed
  regeneration cycles by time `n` has) with `Tₙ/n → c > 0`, then `HasLIL (s ∘ T) (√c γ)`;
  `exists_eq_of_succ_le`.
* `hasLIL_of_approx`: an LIL from LILs of approximating splittings with converging constants.
* `lilAlternating`, `hasLIL_lilAlternating`, `not_hasLIL_lilAlternating_two_mul`: without the
  unit-step hypothesis the random-index step fails (indices `Tₙ = 2n` see only the even terms of
  the alternating sequence `±√(2 m log log m)`).
* `hasLIL_iff_nat`, `measurableSet_eventually_atTop`, `measurableSet_frequently_atTop`,
  `measurableSet_hasLIL`: the LIL event of measurable processes is measurable.

**Remainders.** `ae_tendsto_sq_div_of_identDistrib`: identically distributed `Zⱼ ∈ L²` satisfy
`Zⱼ²/(j + 1) → 0` almost surely (Borel–Cantelli on `P(Zⱼ² > ε (j + 1))`), so maxima of cycle sums
over a cycle are `o(√n)`.

**One-dependent sequences.**
* `IsOneDependent`: `(ξ₀, …, ξₙ)` is independent of `(ξ_{n+2}, ξ_{n+3}, …)` for every `n`;
  `IsStationarySeq`: shifts have the law of the sequence.
* `iIndepFun_of_indepFun_succ`, `iIndepFun_windowSum`: window sums separated by gaps are
  independent; `IsStationarySeq.identDistrib_comp`, `IsStationarySeq.identDistrib_coord`.
* `IsOneDependent.integral_mul_eq_zero`, `IsOneDependent.integral_sq_sum`:
  `E[(Σ_{j<L} ξⱼ)²] = L γ₀ + 2 (L − 1) γ₁`.
* **The LIL for stationary one-dependent sequences** (`hasLIL_oneDependent`): for a centred
  stationary one-dependent `ξⱼ ∈ L²`, `σ̄² = γ₀ + 2γ₁ ≥ 0` and `Sₙ` obeys the LIL with constant
  `σ̄` almost surely. Blocks of `L + 1` terms separated by single terms are i.i.d.; the i.i.d. LIL
  applies to the block sums (constant `√((L + 1)γ₀ + 2Lγ₁)`) and to the separating terms
  (constant `√γ₀`), and `L → ∞`.
* `tendsto_natDiv_div`, `succ_div_le_div_add_one`: integer division.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Deterministic transfer of the LIL -/

/-- `lilScale n > 0` eventually. -/
theorem eventually_lilScale_pos : ∀ᶠ n : ℕ in atTop, 0 < lilScale n := by
  filter_upwards [eventually_le_log 3] with n hn using lilScale_pos hn

/-- `LILBound` is preserved by perturbations that are `o(√(n log log n))`. -/
theorem LILBound.of_tendsto_sub {s s' : ℕ → ℝ} {γ : ℝ} (h : LILBound s γ)
    (hd : Tendsto (fun n => (s' n - s n) / lilScale n) atTop (𝓝 0)) : LILBound s' γ := by
  intro ε hε
  obtain ⟨h1, h2⟩ := h (ε / 2) (by positivity)
  have hd' : ∀ᶠ n in atTop, |s' n - s n| ≤ ε / 2 * lilScale n := by
    filter_upwards [(Metric.tendsto_nhds.1 hd) (ε / 2) (by positivity), eventually_lilScale_pos]
      with n hn hp
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hp, div_lt_iff₀ hp] at hn
    exact hn.le
  refine ⟨?_, ?_⟩
  · filter_upwards [h1, hd'] with n hn1 hn2
    have := (abs_le.1 hn2).2
    have e : (γ + ε / 2) * lilScale n + ε / 2 * lilScale n = (γ + ε) * lilScale n := by ring
    linarith
  · refine (h2.and_eventually hd').mono fun n hn => ?_
    have := (abs_le.1 hn.2).1
    have e : (γ - ε / 2) * lilScale n - ε / 2 * lilScale n = (γ - ε) * lilScale n := by ring
    linarith

/-- `HasLIL` is preserved by perturbations that are `o(√(n log log n))`. -/
theorem HasLIL.of_tendsto_sub {s s' : ℕ → ℝ} {γ : ℝ} (h : HasLIL s γ)
    (hd : Tendsto (fun n => (s' n - s n) / lilScale n) atTop (𝓝 0)) : HasLIL s' γ := by
  refine ⟨h.1.of_tendsto_sub hd, h.2.of_tendsto_sub ?_⟩
  have := hd.neg
  rw [neg_zero] at this
  refine this.congr fun n => ?_
  ring

/-- `o(√n)` is `o(√(n log log n))`. -/
theorem tendsto_div_lilScale_of_sqrt {x : ℕ → ℝ}
    (h : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ * x n) atTop (𝓝 0)) :
    Tendsto (fun n => x n / lilScale n) atTop (𝓝 0) := by
  have hn := h.norm
  rw [norm_zero] at hn
  refine squeeze_zero_norm' ?_ hn
  filter_upwards [eventually_le_log 3] with n hn
  have h1 := sqrt_le_lilScale hn
  have h2 : 0 < √(n : ℝ) := by
    have := one_le_of_three_le_log (Nat.cast_nonneg _) hn
    exact Real.sqrt_pos.2 (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (lilScale_pos hn),
    abs_of_pos (inv_pos.2 h2), inv_mul_eq_div]
  exact div_le_div_of_nonneg_left (abs_nonneg _) h2 h1

/-- An integer sequence with increments at most `1` that tends to infinity takes every value
beyond its start. -/
theorem exists_eq_of_succ_le {T : ℕ → ℕ} (hT1 : ∀ n, T (n + 1) ≤ T n + 1)
    (hTt : Tendsto T atTop atTop) {m : ℕ} (hm : T 0 ≤ m) : ∃ n, T n = m := by
  classical
  have hex : ∃ n, m ≤ T n := (hTt.eventually_ge_atTop m).exists
  set n₀ := Nat.find hex with hn₀
  have h1 : m ≤ T n₀ := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos n₀ with h | h
  · rw [h] at h1
    exact ⟨0, le_antisymm hm h1⟩
  · have h2 := Nat.find_min hex (show n₀ - 1 < n₀ by omega)
    have h3 := hT1 (n₀ - 1)
    rw [Nat.sub_add_cancel h] at h3
    exact ⟨n₀, by omega⟩

/-- **The random-index step for the LIL** (deterministic form of MT (17.33)–(17.36)): if `s`
satisfies `LILBound s γ` with `γ ≥ 0`, and the integer indices `Tₙ` have increments at most `1`
and `Tₙ/n → c > 0`, then `LILBound (s ∘ T) (√c γ)`. -/
theorem LILBound.comp_index {s : ℕ → ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (h : LILBound s γ) {T : ℕ → ℕ}
    (hT1 : ∀ n, T (n + 1) ≤ T n + 1) {c : ℝ} (hc : 0 < c)
    (hT : Tendsto (fun n => (T n : ℝ) / n) atTop (𝓝 c)) :
    LILBound (fun n => s (T n)) (√c * γ) := by
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have hTt : Tendsto (fun n => (T n : ℝ)) atTop atTop := by
    refine (hT.pos_mul_atTop hc tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hTtN : Tendsto T atTop atTop := tendsto_natCast_atTop_iff.1 hTt
  have hρ := tendsto_lilScale_div hc hT
  intro ε hε
  set ε₁ := ε / (2 * √c) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁c : ε₁ * √c = ε / 2 := by rw [hε₁]; field_simp
  obtain ⟨h1, h2⟩ := h ε₁ hε₁0
  -- eventually `lilScale (T n) = ρₙ lilScale n` with `ρₙ` close to `√c`
  have hup : ∀ᶠ n in atTop, (γ + ε₁) * (lilScale (T n) / lilScale n) < √c * γ + ε := by
    have := hρ.const_mul (γ + ε₁)
    refine this.eventually (gt_mem_nhds ?_)
    nlinarith
  have hlow : ∀ᶠ n in atTop, √c * γ - ε < (γ - ε₁) * (lilScale (T n) / lilScale n) := by
    have := hρ.const_mul (γ - ε₁)
    refine this.eventually (lt_mem_nhds ?_)
    nlinarith
  refine ⟨?_, ?_⟩
  · filter_upwards [hTtN.eventually h1, hup, eventually_lilScale_pos] with n hn1 hn2 hp
    have hp' : lilScale n ≠ 0 := hp.ne'
    calc s (T n) ≤ (γ + ε₁) * lilScale (T n) := hn1
      _ = (γ + ε₁) * (lilScale (T n) / lilScale n) * lilScale n := by field_simp
      _ ≤ (√c * γ + ε) * lilScale n := mul_le_mul_of_nonneg_right hn2.le hp.le
  · rw [Filter.frequently_atTop]
    intro N
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hlow.and eventually_lilScale_pos)
    obtain ⟨m, hm1, hm2⟩ := Filter.frequently_atTop.1 h2 (N + N₂ + T 0)
    obtain ⟨n, hn⟩ := exists_eq_of_succ_le hT1 hTtN (show T 0 ≤ m by omega)
    have hTn : T n ≤ T 0 + n := by
      clear hn
      induction n with
      | zero => omega
      | succ n ih => have := hT1 n; omega
    have hnN : N + N₂ ≤ n := by omega
    obtain ⟨hn3, hp⟩ := hN₂ n (by omega)
    refine ⟨n, by omega, ?_⟩
    have hp' : lilScale n ≠ 0 := hp.ne'
    simp only [hn] at hn3 ⊢
    calc (√c * γ - ε) * lilScale n ≤ (γ - ε₁) * (lilScale m / lilScale n) * lilScale n :=
          mul_le_mul_of_nonneg_right hn3.le hp.le
      _ = (γ - ε₁) * lilScale m := by field_simp
      _ ≤ s m := hm2

/-- **The random-index step for the LIL**: `HasLIL s γ` with `γ ≥ 0`, indices with increments at
most `1` and `Tₙ/n → c > 0` give `HasLIL (s ∘ T) (√c γ)`. -/
theorem HasLIL.comp_index {s : ℕ → ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (h : HasLIL s γ) {T : ℕ → ℕ}
    (hT1 : ∀ n, T (n + 1) ≤ T n + 1) {c : ℝ} (hc : 0 < c)
    (hT : Tendsto (fun n => (T n : ℝ) / n) atTop (𝓝 c)) :
    HasLIL (fun n => s (T n)) (√c * γ) :=
  ⟨h.1.comp_index hγ hT1 hc hT, h.2.comp_index hγ hT1 hc hT⟩

/-! ### Measurability of the LIL event -/

/-- `HasLIL` through the countably many `ε = 1/(k + 1)`. -/
theorem hasLIL_iff_nat (s : ℕ → ℝ) (γ : ℝ) :
    HasLIL s γ ↔ ∀ k : ℕ,
      ((∀ᶠ n in atTop, s n ≤ (γ + 1 / ((k : ℝ) + 1)) * lilScale n) ∧
        ∃ᶠ n in atTop, (γ - 1 / ((k : ℝ) + 1)) * lilScale n ≤ s n) ∧
      ((∀ᶠ n in atTop, -s n ≤ (γ + 1 / ((k : ℝ) + 1)) * lilScale n) ∧
        ∃ᶠ n in atTop, (γ - 1 / ((k : ℝ) + 1)) * lilScale n ≤ -s n) := by
  constructor
  · intro h k
    exact ⟨h.1 _ (by positivity), h.2 _ (by positivity)⟩
  · intro h
    exact ⟨lilBound_of_nat fun k => (h k).1, lilBound_of_nat fun k => (h k).2⟩

/-- The event `{∀ᶠ n, pₙ}` of measurable events is measurable. -/
theorem measurableSet_eventually_atTop {Ω : Type*} [MeasurableSpace Ω] {p : ℕ → Ω → Prop}
    (hp : ∀ n, MeasurableSet {ω | p n ω}) : MeasurableSet {ω | ∀ᶠ n in atTop, p n ω} := by
  have e : {ω | ∀ᶠ n in atTop, p n ω} = ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), {ω | p n ω} := by
    ext ω
    simp only [mem_ofPred_eq, eventually_atTop, mem_iUnion, mem_iInter]
  rw [e]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => hp n

/-- The event `{∃ᶠ n, pₙ}` of measurable events is measurable. -/
theorem measurableSet_frequently_atTop {Ω : Type*} [MeasurableSpace Ω] {p : ℕ → Ω → Prop}
    (hp : ∀ n, MeasurableSet {ω | p n ω}) : MeasurableSet {ω | ∃ᶠ n in atTop, p n ω} := by
  have e : {ω | ∃ᶠ n in atTop, p n ω} = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), {ω | p n ω} := by
    ext ω
    simp only [mem_ofPred_eq, frequently_atTop, mem_iUnion, mem_iInter, exists_prop]
  rw [e]
  exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _ => hp n

/-- The LIL event of measurable processes is measurable. -/
theorem measurableSet_hasLIL {Ω : Type*} [MeasurableSpace Ω] {f : ℕ → Ω → ℝ}
    (hf : ∀ n, Measurable (f n)) (γ : ℝ) : MeasurableSet {ω | HasLIL (fun n => f n ω) γ} := by
  have e : {ω | HasLIL (fun n => f n ω) γ} = ⋂ k : ℕ,
      (({ω | ∀ᶠ n in atTop, f n ω ≤ (γ + 1 / ((k : ℝ) + 1)) * lilScale n} ∩
        {ω | ∃ᶠ n in atTop, (γ - 1 / ((k : ℝ) + 1)) * lilScale n ≤ f n ω}) ∩
      ({ω | ∀ᶠ n in atTop, -f n ω ≤ (γ + 1 / ((k : ℝ) + 1)) * lilScale n} ∩
        {ω | ∃ᶠ n in atTop, (γ - 1 / ((k : ℝ) + 1)) * lilScale n ≤ -f n ω})) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_inter_iff]
    exact hasLIL_iff_nat _ γ
  rw [e]
  refine MeasurableSet.iInter fun k => ((measurableSet_eventually_atTop fun n => ?_).inter
    (measurableSet_frequently_atTop fun n => ?_)).inter
    ((measurableSet_eventually_atTop fun n => ?_).inter
    (measurableSet_frequently_atTop fun n => ?_))
  · exact measurableSet_le (hf n) measurable_const
  · exact measurableSet_le measurable_const (hf n)
  · exact measurableSet_le (hf n).neg measurable_const
  · exact measurableSet_le measurable_const (hf n).neg

/-! ### Square-integrable identically distributed remainders -/

/-- **Identically distributed square-integrable variables are `o(√j)`** (Borel–Cantelli on
`P(Zⱼ² > ε (j + 1))`): almost surely `Zⱼ²/(j + 1) → 0`. -/
theorem ae_tendsto_sq_div_of_identDistrib {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Z : ℕ → Ω → ℝ}
    (hident : ∀ j, IdentDistrib (Z j) (Z 0) Q Q) (hL2 : MemLp (Z 0) 2 Q) :
    ∀ᵐ ω ∂Q, Tendsto (fun j : ℕ => Z j ω ^ 2 / ((j : ℝ) + 1)) atTop (𝓝 0) := by
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂Q, ∀ᶠ j in atTop, Z j ω ^ 2 ≤ ((j : ℝ) + 1) / ((k : ℝ) + 1) := by
    intro k
    set E : ℕ → Set Ω := fun j => {ω | ((j : ℝ) + 1) / ((k : ℝ) + 1) < Z j ω ^ 2} with hE
    have hW : Integrable (fun ω => ((k : ℝ) + 1) * Z 0 ω ^ 2) Q := hL2.integrable_sq.const_mul _
    have hW0 : 0 ≤ fun ω => ((k : ℝ) + 1) * Z 0 ω ^ 2 := fun ω => by positivity
    let _ : MeasureSpace Ω := ⟨Q⟩
    have : IsProbabilityMeasure (volume : Measure Ω) := ‹IsProbabilityMeasure Q›
    have hsum : ∑' j : ℕ, Q {ω | ((k : ℝ) + 1) * Z 0 ω ^ 2 ∈ Ioi (j : ℝ)} < ∞ :=
      tsum_prob_mem_Ioi_lt_top hW hW0
    have hle : ∀ j, Q (E j) ≤ Q {ω | ((k : ℝ) + 1) * Z 0 ω ^ 2 ∈ Ioi (j : ℝ)} := fun j => by
      have hs : MeasurableSet {x : ℝ | ((j : ℝ) + 1) / ((k : ℝ) + 1) < x ^ 2} :=
        measurableSet_lt measurable_const (measurable_id.pow_const 2)
      have h1 : Q (E j) = Q (Z 0 ⁻¹' {x : ℝ | ((j : ℝ) + 1) / ((k : ℝ) + 1) < x ^ 2}) :=
        (hident j).measure_mem_eq hs
      rw [h1]
      refine measure_mono fun ω hω => ?_
      simp only [mem_preimage, mem_ofPred_eq, mem_Ioi] at hω ⊢
      rw [div_lt_iff₀ (by positivity)] at hω
      linarith
    have hne : ∑' j, Q (E j) ≠ ∞ :=
      ((ENNReal.tsum_le_tsum hle).trans_lt hsum).ne
    filter_upwards [ae_eventually_notMem hne] with ω hω
    filter_upwards [hω] with j hj
    simp only [hE, mem_ofPred_eq, not_lt] at hj
    exact hj
  filter_upwards [ae_all_iff.2 hk] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk'⟩ := exists_nat_one_div_lt hε
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hω k)
  refine ⟨J, fun j hj => ?_⟩
  have h1 := hJ j hj
  have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (sq_nonneg _) hpos.le),
    div_lt_iff₀ hpos]
  have : ((j : ℝ) + 1) / ((k : ℝ) + 1) = 1 / ((k : ℝ) + 1) * ((j : ℝ) + 1) := by ring
  rw [this] at h1
  nlinarith

/-! ### Independence from successive independence -/

/-- A sequence each of whose initial segments `(B₀, …, Bᵢ)` is independent of the next term
`B_{i+1}` is independent. -/
theorem iIndepFun_of_indepFun_succ {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {B : ℕ → Ω → ℝ}
    (h : ∀ i, IndepFun (fun ω (j : Fin (i + 1)) => B j ω) (B (i + 1)) Q) :
    iIndepFun B Q := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  set A : ℕ → Set ℝ := fun i => if i ∈ S then sets i else univ with hA
  have hAm : ∀ i, MeasurableSet (A i) := fun i => by
    simp only [hA]; split_ifs with hi
    · exact hsets i hi
    · exact MeasurableSet.univ
  -- the product formula on initial segments
  have hseg : ∀ N, Q (⋂ i ∈ Finset.range N, B i ⁻¹' A i) =
      ∏ i ∈ Finset.range N, Q (B i ⁻¹' A i) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.prod_range_succ, ← ih, Finset.range_add_one, Finset.set_biInter_insert,
        inter_comm]
      rcases Nat.eq_zero_or_pos N with h0 | hN
      · subst h0; simp
      · obtain ⟨i, rfl⟩ : ∃ i, N = i + 1 := ⟨N - 1, by omega⟩
        have hrect : (⋂ j ∈ Finset.range (i + 1), B j ⁻¹' A j) =
            (fun ω (j : Fin (i + 1)) => B j ω) ⁻¹' Set.pi univ (fun j => A j) := by
          ext ω
          simp only [mem_iInter, Finset.mem_range, mem_preimage, Set.mem_pi, mem_univ,
            true_imp_iff]
          constructor
          · intro hω j; exact hω j j.2
          · intro hω j hj; exact hω ⟨j, hj⟩
        rw [hrect]
        exact (h i).measure_inter_preimage_eq_mul _ _
          (MeasurableSet.univ_pi fun j => hAm j) (hAm (i + 1))
  -- reduce to an initial segment
  set N := S.sup id + 1 with hN
  have hSN : S ⊆ Finset.range N := fun i hi => Finset.mem_range.2
    (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have h1 : (⋂ i ∈ S, B i ⁻¹' sets i) = ⋂ i ∈ Finset.range N, B i ⁻¹' A i := by
    ext ω
    simp only [mem_iInter, mem_preimage, hA]
    constructor
    · intro hω i _
      split_ifs with hi
      · exact hω i hi
      · exact mem_univ _
    · intro hω i hi
      have := hω i (hSN hi)
      simpa only [hi, ite_true] using this
  have h2 : ∏ i ∈ Finset.range N, Q (B i ⁻¹' A i) = ∏ i ∈ S, Q (B i ⁻¹' sets i) := by
    rw [← Finset.prod_subset hSN fun i _ hi => by simp only [hA, hi, ite_false,
      preimage_univ, measure_univ]]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp only [hA, hi, ite_true]
  rw [h1, hseg, h2]

/-! ### One-dependent stationary sequences -/

/-- A sequence is **one-dependent** when its past `(ξ₀, …, ξₙ)` is independent of its future
`(ξ_{n+2}, ξ_{n+3}, …)` for every `n` (MT §17.3.2, the split `m`-skeleton cycle sums). -/
def IsOneDependent {Ω : Type*} [MeasurableSpace Ω] (ξ : ℕ → Ω → ℝ) (Q : Measure Ω) : Prop :=
  ∀ n, IndepFun (fun ω (i : Fin (n + 1)) => ξ i ω) (fun ω (i : ℕ) => ξ (n + 2 + i) ω) Q

/-- A sequence is **stationary** when every shift `(ξ_{c+j})ⱼ` has the law of `(ξⱼ)ⱼ`. -/
def IsStationarySeq {Ω : Type*} [MeasurableSpace Ω] (ξ : ℕ → Ω → ℝ) (Q : Measure Ω) : Prop :=
  ∀ c, IdentDistrib (fun ω j => ξ (c + j) ω) (fun ω j => ξ j ω) Q Q

/-- Window sums `Σ_{j<L} ξ_{ip+o+j}` of a one-dependent sequence along windows separated by at
least one index (`L + 1 ≤ p`) are independent. -/
theorem iIndepFun_windowSum {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ξ : ℕ → Ω → ℝ} (hξ : IsOneDependent ξ Q) {p o L : ℕ}
    (hL : 1 ≤ L) (hp : L + 1 ≤ p) :
    iIndepFun (fun i ω => ∑ j ∈ Finset.range L, ξ (i * p + o + j) ω) Q := by
  refine iIndepFun_of_indepFun_succ fun i => ?_
  set n := i * p + o + L - 1 with hn
  have h := hξ n
  set F : (Fin (n + 1) → ℝ) → (Fin (i + 1) → ℝ) := fun v k =>
    ∑ j ∈ Finset.range L, (if hh : (k : ℕ) * p + o + j < n + 1 then v ⟨_, hh⟩ else 0) with hF
  set G : (ℕ → ℝ) → ℝ := fun w => ∑ j ∈ Finset.range L, w (p - L - 1 + j) with hG
  have hFm : Measurable F := by
    refine measurable_pi_iff.2 fun k => Finset.measurable_sum _ fun j _ => ?_
    by_cases hh : (k : ℕ) * p + o + j < n + 1
    · simp only [hh, dite_true]; exact measurable_pi_apply _
    · simp only [hh, dite_false]; exact measurable_const
  have hGm : Measurable G := Finset.measurable_sum _ fun j _ => measurable_pi_apply _
  have hc := h.comp hFm hGm
  convert hc using 1
  · ext ω k
    simp only [Function.comp_apply, hF]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hk : (k : ℕ) * p ≤ i * p := Nat.mul_le_mul_right p (Nat.lt_succ_iff.1 k.2)
    have hj' := Finset.mem_range.1 hj
    have hlt : (k : ℕ) * p + o + j < n + 1 := by
      rw [hn]
      generalize (k : ℕ) * p = u at hk ⊢
      generalize i * p = v at hk ⊢
      omega
    simp only [hlt, dite_true]
  · ext ω
    simp only [Function.comp_apply, hG]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    congr 1
    rw [hn, Nat.succ_mul]
    generalize i * p = v
    omega

/-- Under stationarity, functionals of shifted windows have the law of the unshifted ones. -/
theorem IsStationarySeq.identDistrib_comp {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {ξ : ℕ → Ω → ℝ} (hst : IsStationarySeq ξ Q) {u : (ℕ → ℝ) → ℝ} (hu : Measurable u)
    (c : ℕ) :
    IdentDistrib (fun ω => u fun j => ξ (c + j) ω) (fun ω => u fun j => ξ j ω) Q Q :=
  (hst c).comp hu

/-- Under stationarity every `ξⱼ` has the law of `ξ₀`. -/
theorem IsStationarySeq.identDistrib_coord {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {ξ : ℕ → Ω → ℝ} (hst : IsStationarySeq ξ Q) (j : ℕ) : IdentDistrib (ξ j) (ξ 0) Q Q := by
  have h := hst.identDistrib_comp (u := fun v => v 0) (measurable_pi_apply 0) j
  simpa only [add_zero] using h

/-- For a centred square-integrable one-dependent sequence, `E[ξⱼ ξⱼ'] = 0` for `j + 2 ≤ j'`. -/
theorem IsOneDependent.integral_mul_eq_zero {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ξ : ℕ → Ω → ℝ} (hξ : IsOneDependent ξ Q)
    (hL2 : ∀ j, MemLp (ξ j) 2 Q) (h0 : ∀ j, ∫ ω, ξ j ω ∂Q = 0) {j j' : ℕ} (h : j + 2 ≤ j') :
    ∫ ω, ξ j ω * ξ j' ω ∂Q = 0 := by
  have hφ : Measurable fun v : Fin (j + 1) → ℝ => v (Fin.last j) := measurable_pi_apply _
  have hψ : Measurable fun w : ℕ → ℝ => w (j' - j - 2) := measurable_pi_apply _
  have hind := (hξ j).comp hφ hψ
  have e1 : ((fun v : Fin (j + 1) → ℝ => v (Fin.last j)) ∘
      fun ω (i : Fin (j + 1)) => ξ i ω) = ξ j := by
    ext ω; simp
  have e2 : ((fun w : ℕ → ℝ => w (j' - j - 2)) ∘ fun ω (i : ℕ) => ξ (j + 2 + i) ω) = ξ j' := by
    ext ω; simp only [Function.comp_apply]; congr 1; omega
  rw [e1, e2] at hind
  rw [hind.integral_fun_mul_eq_mul_integral (hL2 j).aestronglyMeasurable
    (hL2 j').aestronglyMeasurable, h0 j, zero_mul]

/-- The variance of a block of a centred stationary one-dependent sequence:
`E[(Σ_{j<L} ξⱼ)²] = L γ₀ + 2 (L − 1) γ₁` for `L ≥ 1`, `γ₀ = E[ξ₀²]`, `γ₁ = E[ξ₀ ξ₁]`. -/
theorem IsOneDependent.integral_sq_sum {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ξ : ℕ → Ω → ℝ} (hξ : IsOneDependent ξ Q)
    (hst : IsStationarySeq ξ Q) (hL2 : MemLp (ξ 0) 2 Q) (h0 : ∫ ω, ξ 0 ω ∂Q = 0) {L : ℕ}
    (hL : 1 ≤ L) :
    ∫ ω, (∑ j ∈ Finset.range L, ξ j ω) ^ 2 ∂Q =
      L * ∫ ω, ξ 0 ω ^ 2 ∂Q + 2 * ((L : ℝ) - 1) * ∫ ω, ξ 0 ω * ξ 1 ω ∂Q := by
  have hL2j : ∀ j, MemLp (ξ j) 2 Q := fun j => (hst.identDistrib_coord j).memLp_iff.2 hL2
  have h0j : ∀ j, ∫ ω, ξ j ω ∂Q = 0 := fun j =>
    (hst.identDistrib_coord j).integral_eq.trans h0
  have hsq : ∀ j, ∫ ω, ξ j ω ^ 2 ∂Q = ∫ ω, ξ 0 ω ^ 2 ∂Q := fun j =>
    ((hst.identDistrib_coord j).comp (measurable_id.pow_const 2)).integral_eq
  have hcov : ∀ j, ∫ ω, ξ j ω * ξ (j + 1) ω ∂Q = ∫ ω, ξ 0 ω * ξ 1 ω ∂Q := fun j => by
    have h := (hst.identDistrib_comp (u := fun v => v 0 * v 1)
      ((measurable_pi_apply 0).mul (measurable_pi_apply 1)) j).integral_eq
    simpa only [add_zero] using h
  induction L, hL using Nat.le_induction with
  | base =>
    simp only [Finset.sum_range_one, Nat.cast_one, one_mul, sub_self, mul_zero, zero_mul,
      add_zero]
  | succ L hL ih =>
    have hS : MemLp (fun ω => ∑ j ∈ Finset.range L, ξ j ω) 2 Q :=
      memLp_finsetSum _ fun j _ => hL2j j
    have hcross : ∫ ω, (∑ j ∈ Finset.range L, ξ j ω) * ξ L ω ∂Q =
        ∫ ω, ξ 0 ω * ξ 1 ω ∂Q := by
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum (Finset.range L) (f := fun j ω => ξ j ω * ξ L ω)
        fun j _ => (hL2j j).integrable_mul (hL2j L)]
      obtain ⟨l, rfl⟩ : ∃ l, L = l + 1 := ⟨L - 1, by omega⟩
      rw [Finset.sum_range_succ, Finset.sum_eq_zero fun j hj =>
        hξ.integral_mul_eq_zero hL2j h0j (by have := Finset.mem_range.1 hj; omega),
        zero_add, hcov l]
    have hexp : (fun ω => (∑ j ∈ Finset.range (L + 1), ξ j ω) ^ 2) = fun ω =>
        (∑ j ∈ Finset.range L, ξ j ω) ^ 2 +
          (2 * ((∑ j ∈ Finset.range L, ξ j ω) * ξ L ω) + ξ L ω ^ 2) := by
      ext ω; rw [Finset.sum_range_succ]; ring
    have hi1 : Integrable (fun ω => (∑ j ∈ Finset.range L, ξ j ω) ^ 2) Q := hS.integrable_sq
    have hi2 : Integrable (fun ω => 2 * ((∑ j ∈ Finset.range L, ξ j ω) * ξ L ω)) Q :=
      (hS.integrable_mul (hL2j L)).const_mul 2
    have hi3 : Integrable (fun ω => ξ L ω ^ 2) Q := (hL2j L).integrable_sq
    have hi23 : Integrable (fun ω => 2 * ((∑ j ∈ Finset.range L, ξ j ω) * ξ L ω) +
        ξ L ω ^ 2) Q := hi2.add hi3
    rw [hexp, integral_add hi1 hi23, integral_add hi2 hi3, integral_const_mul,
      hcross, ih, hsq L]
    push_cast
    ring

/-- **Combining approximate LILs**: if for every `L` the sequence splits as
`sₙ = a_L(n) + b_L(n) + R_L(n)` with `HasLIL a_L c_L`, `HasLIL b_L d_L`,
`R_L = o(√(n log log n))`, `c_L → σ` and `d_L → 0`, then `HasLIL s σ`. -/
theorem hasLIL_of_approx {s : ℕ → ℝ} {σ : ℝ} {a b R : ℕ → ℕ → ℝ} {c d : ℕ → ℝ}
    (hsplit : ∀ L n, s n = a L n + b L n + R L n) (ha : ∀ L, HasLIL (a L) (c L))
    (hb : ∀ L, HasLIL (b L) (d L))
    (hR : ∀ L, Tendsto (fun n => R L n / lilScale n) atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 σ)) (hd : Tendsto d atTop (𝓝 0)) : HasLIL s σ := by
  -- one half, for a general splitting
  have key : ∀ (s' : ℕ → ℝ) (a' b' R' : ℕ → ℕ → ℝ),
      (∀ L n, s' n = a' L n + b' L n + R' L n) → (∀ L, LILBound (a' L) (c L)) →
      (∀ L, HasLIL (b' L) (d L)) →
      (∀ L, Tendsto (fun n => R' L n / lilScale n) atTop (𝓝 0)) → LILBound s' σ := by
    intro s' a' b' R' hs ha' hb' hR' ε hε
    obtain ⟨L, hL1, hL2⟩ := ((hc.eventually (Metric.ball_mem_nhds σ (show 0 < ε / 8 by
      positivity))).and (hd.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / 8 by
      positivity)))).exists
    rw [Real.dist_eq] at hL1 hL2
    rw [sub_zero] at hL2
    have hcL := abs_lt.1 hL1
    have hdL := abs_lt.1 hL2
    obtain ⟨ha1, ha2⟩ := ha' L (ε / 8) (by positivity)
    have hb1 := ((hb' L).1 (ε / 8) (by positivity)).1
    have hb2 := ((hb' L).2 (ε / 8) (by positivity)).1
    have hR1 : ∀ᶠ n in atTop, |R' L n| ≤ ε / 8 * lilScale n := by
      filter_upwards [(Metric.tendsto_nhds.1 (hR' L)) (ε / 8) (by positivity),
        eventually_lilScale_pos] with n hn hp
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hp, div_lt_iff₀ hp] at hn
      exact hn.le
    refine ⟨?_, ?_⟩
    · filter_upwards [ha1, hb1, hR1] with n h1 h2 h3
      have h4 := (abs_le.1 h3).2
      have h5 := lilScale_nonneg n
      have hk : c L + ε / 8 + (d L + ε / 8) + ε / 8 ≤ σ + ε := by linarith [hcL.2, hdL.2]
      have h6 := mul_le_mul_of_nonneg_right hk h5
      rw [hs L n]
      linarith
    · refine (ha2.and_eventually (hb2.and hR1)).mono fun n hn => ?_
      obtain ⟨h1, h2, h3⟩ := hn
      beta_reduce at h2
      have h4 := (abs_le.1 h3).1
      have h5 := lilScale_nonneg n
      have hk : σ - ε ≤ c L - ε / 8 - (d L + ε / 8) - ε / 8 := by linarith [hcL.1, hdL.2]
      have h6 := mul_le_mul_of_nonneg_right hk h5
      rw [hs L n]
      linarith
  refine ⟨key s a b R hsplit (fun L => (ha L).1) hb hR, key (fun n => -s n)
    (fun L n => -a L n) (fun L n => -b L n) (fun L n => -R L n) (fun L n => by
      rw [hsplit L n]; ring) (fun L => (ha L).2) (fun L => ⟨(hb L).2, ?_⟩) fun L => ?_⟩
  · simpa only [neg_neg] using (hb L).1
  · have := (hR L).neg
    rw [neg_zero] at this
    refine this.congr fun n => ?_
    rw [neg_div]

/-- `(n / k)/n → 1/k` for integer division by `k ≥ 1`. -/
theorem tendsto_natDiv_div {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => ((n / k : ℕ) : ℝ) / n) atTop (𝓝 (1 / (k : ℝ))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := (tendsto_nat_floor_mul_div_atTop (show (0 : ℝ) ≤ 1 / k by positivity)).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [one_div_mul_eq_div, Nat.floor_div_eq_div]

/-- `(n + 1)/k ≤ n/k + 1` for integer division. -/
theorem succ_div_le_div_add_one (n k : ℕ) : (n + 1) / k ≤ n / k + 1 := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp
  · calc (n + 1) / k ≤ (n + k) / k := Nat.div_le_div_right (by omega)
      _ = n / k + 1 := Nat.add_div_right n h

/-- **The LIL for stationary one-dependent sequences**: for a centred stationary one-dependent
sequence `ξⱼ ∈ L²` with `γ₀ = E[ξ₀²]`, `γ₁ = E[ξ₀ ξ₁]`, `σ̄² = γ₀ + 2γ₁ ≥ 0` and almost surely
`Sₙ = Σ_{j<n} ξⱼ` obeys the LIL with constant `σ̄`. This is the LIL needed for the one-dependent
cycle sums of the split `m`-skeleton (MT Theorem 17.3.1 and (17.36), p. 442). The proof is the
blocking argument: blocks of `L + 1` terms separated by single terms are i.i.d., the
Hartman–Wintner LIL applies to both, and `L → ∞`. -/
theorem hasLIL_oneDependent {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ξ : ℕ → Ω → ℝ} (hm : ∀ j, Measurable (ξ j))
    (hξ : IsOneDependent ξ Q) (hst : IsStationarySeq ξ Q) (hL2 : MemLp (ξ 0) 2 Q)
    (h0 : ∫ ω, ξ 0 ω ∂Q = 0) :
    0 ≤ ∫ ω, ξ 0 ω ^ 2 ∂Q + 2 * ∫ ω, ξ 0 ω * ξ 1 ω ∂Q ∧
      ∀ᵐ ω ∂Q, HasLIL (fun n => ∑ j ∈ Finset.range n, ξ j ω)
        (√(∫ ω, ξ 0 ω ^ 2 ∂Q + 2 * ∫ ω, ξ 0 ω * ξ 1 ω ∂Q)) := by
  set γ₀ := ∫ ω, ξ 0 ω ^ 2 ∂Q with hγ₀
  set γ₁ := ∫ ω, ξ 0 ω * ξ 1 ω ∂Q with hγ₁
  have hL2j : ∀ j, MemLp (ξ j) 2 Q := fun j => (hst.identDistrib_coord j).memLp_iff.2 hL2
  have h0j : ∀ j, ∫ ω, ξ j ω ∂Q = 0 := fun j =>
    (hst.identDistrib_coord j).integral_eq.trans h0
  have hγ₀0 : 0 ≤ γ₀ := integral_nonneg fun ω => sq_nonneg _
  -- the blocks, the gaps and the remainders, for block length `L + 1` and period `L + 2`
  set B : ℕ → ℕ → Ω → ℝ := fun L i ω => ∑ j ∈ Finset.range (L + 1), ξ (i * (L + 2) + 0 + j) ω
    with hB
  set G : ℕ → ℕ → Ω → ℝ := fun L i ω => ∑ j ∈ Finset.range 1, ξ (i * (L + 2) + (L + 1) + j) ω
    with hG
  set H : ℕ → ℕ → Ω → ℝ := fun L q ω => ∑ j ∈ Finset.range (L + 1), |ξ (q * (L + 2) + j) ω|
    with hH
  have hBm : ∀ L i, Measurable (B L i) := fun L i => Finset.measurable_sum _ fun j _ => hm _
  have hGm : ∀ L i, Measurable (G L i) := fun L i => Finset.measurable_sum _ fun j _ => hm _
  have hBid : ∀ L i, IdentDistrib (B L i) (B L 0) Q Q := fun L i => by
    have h := hst.identDistrib_comp (u := fun v => ∑ j ∈ Finset.range (L + 1), v j)
      (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) (i * (L + 2))
    have e1 : B L i = fun ω => ∑ j ∈ Finset.range (L + 1), ξ (i * (L + 2) + j) ω := by
      ext ω; simp only [hB, add_zero]
    have e2 : B L 0 = fun ω => ∑ j ∈ Finset.range (L + 1), ξ j ω := by
      ext ω; simp only [hB, zero_mul, zero_add]
    rw [e1, e2]; exact h
  have hGid : ∀ L i, IdentDistrib (G L i) (G L 0) Q Q := fun L i => by
    have h := hst.identDistrib_comp (u := fun v => ∑ j ∈ Finset.range 1, v (L + 1 + j))
      (Finset.measurable_sum _ fun j _ => measurable_pi_apply _) (i * (L + 2))
    have e1 : G L i = fun ω => ∑ j ∈ Finset.range 1, ξ (i * (L + 2) + (L + 1 + j)) ω := by
      ext ω; simp only [hG, add_assoc]
    have e2 : G L 0 = fun ω => ∑ j ∈ Finset.range 1, ξ (L + 1 + j) ω := by
      ext ω; simp only [hG, zero_mul, zero_add]
    rw [e1, e2]; exact h
  have hHid : ∀ L q, IdentDistrib (H L q) (H L 0) Q Q := fun L q => by
    have h := hst.identDistrib_comp (u := fun v => ∑ j ∈ Finset.range (L + 1), |v j|)
      (Finset.measurable_sum _ fun j _ => continuous_abs.measurable.comp (measurable_pi_apply j))
      (q * (L + 2))
    have e2 : H L 0 = fun ω => ∑ j ∈ Finset.range (L + 1), |ξ j ω| := by
      ext ω; simp only [hH, zero_mul, zero_add]
    rw [e2]; exact h
  have hB0 : ∀ L, B L 0 = fun ω => ∑ j ∈ Finset.range (L + 1), ξ j ω := fun L => by
    ext ω; simp only [hB, zero_mul, zero_add]
  have hG0 : ∀ L, G L 0 = ξ (L + 1) := fun L => by
    ext ω; simp only [hG, zero_mul, zero_add, Finset.sum_range_one, add_zero]
  have hBL2 : ∀ L, MemLp (B L 0) 2 Q := fun L => by
    rw [hB0]; exact memLp_finsetSum _ fun j _ => hL2j j
  have hBmean : ∀ L, ∫ ω, B L 0 ω ∂Q = 0 := fun L => by
    rw [hB0, integral_finsetSum _ fun j _ => (hL2j j).integrable one_le_two]
    exact Finset.sum_eq_zero fun j _ => h0j j
  have hBvar : ∀ L, ∫ ω, B L 0 ω ^ 2 ∂Q = (L + 1) * γ₀ + 2 * L * γ₁ := fun L => by
    rw [hB0, hξ.integral_sq_sum hst hL2 h0 (by omega : 1 ≤ L + 1)]
    push_cast; ring
  have hGvar : ∀ L, ∫ ω, G L 0 ω ^ 2 ∂Q = γ₀ := fun L => by
    rw [hG0]; exact ((hst.identDistrib_coord (L + 1)).comp (measurable_id.pow_const 2)).integral_eq
  have hHL2 : ∀ L, MemLp (H L 0) 2 Q := fun L =>
    memLp_finsetSum _ fun j _ => (hL2j _).abs
  -- the almost sure statements, for all `L`
  have hae : ∀ᵐ ω ∂Q, ∀ L : ℕ,
      HasLIL (fun q => ∑ i ∈ Finset.range q, B L i ω) (√((L + 1) * γ₀ + 2 * L * γ₁)) ∧
      HasLIL (fun q => ∑ i ∈ Finset.range q, G L i ω) (√γ₀) ∧
      Tendsto (fun q : ℕ => H L q ω ^ 2 / ((q : ℝ) + 1)) atTop (𝓝 0) := by
    refine ae_all_iff.2 fun L => ?_
    have hBind : iIndepFun (B L) Q :=
      iIndepFun_windowSum hξ (p := L + 2) (o := 0) (L := L + 1) (by omega) (by omega)
    have hGind : iIndepFun (G L) Q :=
      iIndepFun_windowSum hξ (p := L + 2) (o := L + 1) (L := 1) le_rfl (by omega)
    have hGL2 : MemLp (G L 0) 2 Q := by rw [hG0]; exact hL2j _
    have hGmean : ∫ ω, G L 0 ω ∂Q = 0 := by rw [hG0]; exact h0j _
    have h1 := hasLIL_iid hBind (hBm L) (hBid L) (hBL2 L) (hBmean L)
    have h2 := hasLIL_iid hGind (hGm L) (hGid L) hGL2 hGmean
    have h3 := ae_tendsto_sq_div_of_identDistrib (hHid L) (hHL2 L)
    rw [hBvar] at h1
    rw [hGvar] at h2
    filter_upwards [h1, h2, h3] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- the asymptotic variance
  have hvL0 : ∀ L : ℕ, 0 ≤ ((L : ℝ) + 1) * γ₀ + 2 * L * γ₁ := fun L => by
    rw [← hBvar L]; exact integral_nonneg fun ω => sq_nonneg _
  have hlimv : Tendsto (fun L : ℕ => (((L : ℝ) + 1) * γ₀ + 2 * L * γ₁) / ((L : ℝ) + 2)) atTop
      (𝓝 (γ₀ + 2 * γ₁)) := by
    have h := (tendsto_const_nhds (x := γ₀ + 2 * γ₁)).sub ((tendsto_const_nhds
      (x := γ₀ + 4 * γ₁)).div_atTop (tendsto_natCast_atTop_atTop.atTop_add
      (tendsto_const_nhds (x := (2 : ℝ)))))
    rw [sub_zero] at h
    refine h.congr fun L => ?_
    have : (L : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  have hσ0 : 0 ≤ γ₀ + 2 * γ₁ :=
    ge_of_tendsto hlimv (Eventually.of_forall fun L => div_nonneg (hvL0 L) (by positivity))
  refine ⟨hσ0, ?_⟩
  set c : ℕ → ℝ := fun L => √(1 / ((L + 2 : ℕ) : ℝ)) * √(((L : ℝ) + 1) * γ₀ + 2 * L * γ₁)
    with hc
  set d : ℕ → ℝ := fun L => √(1 / ((L + 2 : ℕ) : ℝ)) * √γ₀ with hd
  have hct : Tendsto c atTop (𝓝 √(γ₀ + 2 * γ₁)) := by
    refine ((Real.continuous_sqrt.tendsto _).comp hlimv).congr fun L => ?_
    simp only [Function.comp_apply, hc]
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    push_cast
    field_simp
  have hdt : Tendsto d atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℕ => √(1 / ((L + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
      have h2 : Tendsto (fun L : ℕ => 1 / ((L + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp
          (tendsto_add_atTop_nat 2))
      have := (Real.continuous_sqrt.tendsto 0).comp h2
      rwa [Real.sqrt_zero] at this
    have := h1.mul_const √γ₀
    rwa [zero_mul] at this
  filter_upwards [hae] with ω hω
  set a : ℕ → ℕ → ℝ := fun L n => ∑ i ∈ Finset.range (n / (L + 2)), B L i ω with ha
  set b : ℕ → ℕ → ℝ := fun L n => ∑ i ∈ Finset.range (n / (L + 2)), G L i ω with hb
  set R : ℕ → ℕ → ℝ := fun L n => ∑ j ∈ Finset.range n, ξ j ω - (a L n + b L n) with hR
  have hab : ∀ L n, a L n + b L n = ∑ j ∈ Finset.range (n / (L + 2) * (L + 2)), ξ j ω := by
    intro L n
    rw [sum_range_mul_eq (fun j => ξ j ω), ha, hb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hB, hG, add_zero, Finset.sum_range_one]
    exact (Finset.sum_range_succ (fun x => ξ (i * (L + 2) + x) ω) (L + 1)).symm
  have hRb : ∀ L n, |R L n| ≤ H L (n / (L + 2)) ω := by
    intro L n
    have hle : n / (L + 2) * (L + 2) ≤ n := Nat.div_mul_le_self n (L + 2)
    have hlt : n - n / (L + 2) * (L + 2) ≤ L + 1 := by
      have := Nat.lt_div_mul_add (a := n) (show 0 < L + 2 by omega)
      omega
    have e : R L n = ∑ j ∈ Finset.range (n - n / (L + 2) * (L + 2)),
        ξ (n / (L + 2) * (L + 2) + j) ω := by
      change ∑ j ∈ Finset.range n, ξ j ω - (a L n + b L n) = _
      rw [hab, ← Finset.sum_range_add_sum_Ico _ hle, Finset.sum_Ico_eq_sum_range]
      ring
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hlt)
      fun j _ _ => abs_nonneg _
  refine hasLIL_of_approx (a := a) (b := b) (R := R) (c := c) (d := d)
    (fun L n => by rw [hR]; ring) (fun L => ?_) (fun L => ?_) (fun L => ?_) hct hdt
  · exact (hω L).1.comp_index (Real.sqrt_nonneg _) (fun n => succ_div_le_div_add_one n (L + 2))
      (by positivity) (tendsto_natDiv_div (by omega))
  · exact (hω L).2.1.comp_index (Real.sqrt_nonneg _) (fun n => succ_div_le_div_add_one n (L + 2))
      (by positivity) (tendsto_natDiv_div (by omega))
  · refine tendsto_div_lilScale_of_sqrt ?_
    have hq : Tendsto (fun n : ℕ => n / (L + 2)) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro N
      exact ⟨N * (L + 2), fun n hn => (Nat.le_div_iff_mul_le (by omega)).2 hn⟩
    have hu := ((hω L).2.2.comp hq).const_mul 2
    rw [mul_zero] at hu
    have hsq := (Real.continuous_sqrt.tendsto 0).comp hu
    rw [Real.sqrt_zero] at hsq
    refine squeeze_zero_norm' ?_ hsq
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hqn : ((n / (L + 2) : ℕ) : ℝ) + 1 ≤ 2 * n := by
      have h1 : n / (L + 2) ≤ n := Nat.div_le_self n _
      have h2 : ((n / (L + 2) : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
      have h3 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hH0 : 0 ≤ H L (n / (L + 2)) ω := Finset.sum_nonneg fun j _ => abs_nonneg _
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hn0))]
    have h1 : (√(n : ℝ))⁻¹ * |R L n| ≤ (√(n : ℝ))⁻¹ * H L (n / (L + 2)) ω :=
      mul_le_mul_of_nonneg_left (hRb L n) (inv_nonneg.2 (Real.sqrt_nonneg _))
    refine h1.trans ?_
    set h := H L (n / (L + 2)) ω with hh
    set q : ℝ := ((n / (L + 2) : ℕ) : ℝ) with hq'
    have hq1 : (0 : ℝ) < q + 1 := by positivity
    have e1 : (√(n : ℝ))⁻¹ * h = √(h ^ 2 / n) := by
      rw [Real.sqrt_div' _ hn0.le, Real.sqrt_sq hH0, inv_mul_eq_div]
    rw [e1]
    apply Real.sqrt_le_sqrt
    have e2 : 2 * (h ^ 2 / (q + 1)) = 2 * h ^ 2 / (q + 1) := by ring
    rw [e2, div_le_div_iff₀ hn0 hq1]
    have := mul_le_mul_of_nonneg_left hqn (sq_nonneg h)
    linarith

/-! ### The unit-step hypothesis of the random-index step cannot be dropped -/

/-- The alternating sequence `sₘ = ±√(2 m log log m)` (`+` for odd `m`, `−` for even `m`). -/
noncomputable def lilAlternating (m : ℕ) : ℝ := if Odd m then lilScale m else -lilScale m

/-- The alternating sequence obeys the LIL with constant `1`. -/
theorem hasLIL_lilAlternating : HasLIL lilAlternating 1 := by
  have hup : ∀ ε > 0, ∀ n, |lilAlternating n| ≤ (1 + ε) * lilScale n := fun ε hε n => by
    have h0 := lilScale_nonneg n
    have : |lilAlternating n| = lilScale n := by
      unfold lilAlternating; split_ifs
      · exact abs_of_nonneg h0
      · rw [abs_neg]; exact abs_of_nonneg h0
    rw [this]; nlinarith
  refine ⟨fun ε hε => ⟨Eventually.of_forall fun n => (le_abs_self _).trans (hup ε hε n), ?_⟩,
    fun ε hε => ⟨Eventually.of_forall fun n => (neg_le_abs _).trans (hup ε hε n), ?_⟩⟩
  · rw [Filter.frequently_atTop]
    intro N
    refine ⟨2 * N + 1, by omega, ?_⟩
    have hodd : Odd (2 * N + 1) := ⟨N, rfl⟩
    simp only [lilAlternating, hodd, ite_true]
    have := lilScale_nonneg (2 * N + 1)
    nlinarith
  · rw [Filter.frequently_atTop]
    intro N
    refine ⟨2 * N, by omega, ?_⟩
    have hev : ¬ Odd (2 * N) := by rw [Nat.not_odd_iff_even]; exact ⟨N, by ring⟩
    simp only [lilAlternating, hev, ite_false, neg_neg]
    have := lilScale_nonneg (2 * N)
    nlinarith

/-- **The random-index step needs increments at most `1`**: along `Tₙ = 2n` (so `Tₙ/n → 2`) the
alternating sequence, which obeys the LIL with constant `1`, does not obey the LIL with constant
`√2`: `s(Tₙ) = −√(2 · 2n log log 2n)` is never large and positive. Hence the hypothesis
`T (n + 1) ≤ T n + 1` of `HasLIL.comp_index` (satisfied by the number of completed cycles) cannot
be dropped from a random-index LIL with `Tₙ/n → c` only. -/
theorem not_hasLIL_lilAlternating_two_mul :
    ¬ HasLIL (fun n => lilAlternating (2 * n)) (√2 * 1) := by
  intro h
  obtain ⟨-, h2⟩ := h.1 1 one_pos
  have hs : 1 < √2 * 1 := by
    rw [mul_one, show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt zero_le_one one_lt_two
  obtain ⟨n, hn, hpos⟩ := (h2.and_eventually eventually_lilScale_pos).exists
  have hev : ¬ Odd (2 * n) := by rw [Nat.not_odd_iff_even]; exact ⟨n, by ring⟩
  simp only [lilAlternating, hev, ite_false] at hn
  have := lilScale_nonneg (2 * n)
  nlinarith

end MeynTweedie.GeneralizedDrift

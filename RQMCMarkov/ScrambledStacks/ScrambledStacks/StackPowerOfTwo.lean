/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.StackDyadic

/-! # The symmetric two-state chain at `T = 2^k`: bounded error for every scramble

Post #3 reports that "in the five-state chain normality cannot be rejected for the per-state
Sobol sequences ((ii) and (iii))", while "the RQMC estimators are typically not normally
distributed". For the symmetric two-state chain `p₁₁ = p₂₂ = p` (`symChain p`, `π = (1/2, 1/2)`)
and **any** `p ∈ [0, 1)`, dyadic or not, the occupation error is bounded along `T = 2^k`, for
every flip table (Owen scrambling and digital shift alike, no good event needed).

**Self-consistent bound** (`abs_occCount_symChain_pow_two_le`). Write `N_0 + N_1 = T = 2H`,
`H = 2^{k-1}`, `N_0 = H ± d`. The departures from `0` going to `1` and from `1` going to `0`
are threshold counts (`transCount_zero_one_eq`, `transCount_one_zero_eq`):
`N_{01} = N_0 − (N_0 p + E_0(N_0))`, `N_{10} = N_1 (1−p) + E_1(N_1)`, where `E_i(N)` is the
counting error of the first `N` points of stack `i`. Flow balance gives `|N_{01} − N_{10}| ≤ 1`,
so `2(1−p) d ≤ 1 + |E_0(N_0)| + |E_1(N_1)|`. Each `E_i(H)` is one aligned block (error `≤ 1`),
and `N_i` differs from `H` by a segment of length `d` (segment lemma, error `≤ 2⌊log₂ d⌋ + 3`):
`2(1−p) d ≤ 9 + 4 ⌊log₂ d⌋`, which bounds `d` (`exists_le_of_mul_le_log`).

**No CLT along all `T`** (`not_tendstoInDistribution_symChain_owen`,
`not_tendstoInDistribution_symChain_shift`, and for the post's style of non-dyadic chain
`not_tendstoInDistribution_symChain_twoThirds_owen`): along `T = 2^k` the error takes at most
`⌊2C⌋ + 1` values, so no normalisation `(N_0(T) − T/2 − b_T)/a_T` converges in distribution to a
law without atoms along all `T`.

**Correction** (post #3, "normality cannot be rejected"): for the per-state Sobol stacks the
error law does not converge along all `T`, even for non-dyadic transition probabilities such
as `p = 2/3`; normality can only hold along sequences of `T` with growing variance (in
simulations, not formalised: variance `≈ 1.9` at every `T = 2^k`, growing like `log T` at
`T = ⌊0.6 · 2^k⌋ + 1`).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Finset Matrix Filter Topology

/-! ### A self-consistent logarithmic bound -/

/-- **`c d ≤ A + B ⌊log₂ d⌋` bounds `d`**: for `c > 0`, `B ≥ 0` there is `D` with `d ≤ D`
whenever `c d ≤ A + B ⌊log₂ d⌋`. -/
theorem exists_le_of_mul_le_log {c A B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) :
    ∃ D : ℝ, ∀ d : ℕ, c * d ≤ A + B * Nat.log 2 d → (d : ℝ) ≤ D := by
  have hε : 0 < c / (4 * (B + 1)) := by positivity
  obtain ⟨d₀, hd₀⟩ := (tendsto_natCast_atTop_atTop.eventually
    (Real.isLittleO_log_id_atTop.bound hε)).exists_forall_of_atTop
  refine ⟨max d₀ (2 * (A + B) / c), fun d hd => ?_⟩
  rcases lt_or_ge d (max d₀ 1) with hsmall | hlarge
  · have : (d : ℝ) ≤ d₀ ∨ d = 0 := by
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · exact Or.inr h0
      · left
        have : d < d₀ := by omega
        exact_mod_cast this.le
    rcases this with h | h
    · exact h.trans (le_max_left _ _)
    · rw [h, Nat.cast_zero]
      exact (Nat.cast_nonneg d₀).trans (le_max_left _ _)
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hlog := hd₀ d (by omega)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (Real.log_nonneg hdR),
    abs_of_nonneg (by linarith)] at hlog
  have h2 := natLog_two_add_one_le (by omega : 0 < d)
  have h3 : B * Nat.log 2 d ≤ B * (2 * Real.log d + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hB
  have h4 : B * (2 * Real.log d) ≤ c / 2 * d := by
    have h5 : B * (2 * Real.log d) ≤ (B + 1) * (2 * (c / (4 * (B + 1)) * d)) := by
      have := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ 2 * (B + 1))
      nlinarith [Real.log_nonneg hdR]
    have h6 : (B + 1) * (2 * (c / (4 * (B + 1)) * d)) = c / 2 * d := by
      field_simp
      ring
    linarith
  have : c / 2 * d ≤ A + B := by nlinarith
  refine le_trans ?_ (le_max_right _ _)
  rw [le_div_iff₀ hc]
  linarith

/-! ### The symmetric two-state chain -/

/-- The symmetric two-state chain `p₁₁ = p₂₂ = p`. -/
noncomputable def symChain (p : ℝ) : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then p else 1 - p

/-- `symChain p` is stochastic for `p ∈ [0,1]`. -/
theorem isStochastic_symChain {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsStochastic (symChain p) where
  nonneg i j := by unfold symChain; split_ifs <;> linarith
  sum_eq_one i := by
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [symChain]

/-- The first cumulative sum of a row of a two-state matrix is its first entry. -/
theorem cumProb_one_fin_two (P : Fin 2 → Fin 2 → ℝ) (i : Fin 2) : cumProb P i 1 = P i 0 := by
  have h := cumProb_succ P i 0
  simp only [Fin.val_zero, zero_add, cumProb_zero] at h
  exact h

/-- Threshold counts as counting errors: `#{k < N : u k ≤ x} = N x + segErr u x 0 N`. -/
theorem card_filter_le_eq_add_segErr (u : ℕ → ℝ) (x : ℝ) (N : ℕ) :
    (((range N).filter fun k => u k ≤ x).card : ℝ) = N * x + segErr u x 0 N := by
  rw [segErr_eq_card]
  simp only [zero_add]
  ring

/-- **Departures `0 → 1` of a two-state stack path**: `N_{01}(T) = N_0 − #{k < N_0 : u k ≤
cs_{0,1}}`. -/
theorem transCount_zero_one_eq {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (x₀ : Fin 2)
    (f : Fin 2 → ℕ → ℕ → Bool) (T : ℕ) :
    (transCount (stackPath P x₀ (scrambledStack f)) 0 1 T : ℝ) =
      occCount (stackPath P x₀ (scrambledStack f)) 0 T -
        (((range (occCount (stackPath P x₀ (scrambledStack f)) 0 T)).filter
          fun k => scrambledVdc (f 0) k ≤ cumProb P 0 1).card : ℝ) := by
  set N := occCount (stackPath P x₀ (scrambledStack f)) 0 T
  rw [transCount_stackDrive]
  have h := card_filter_step_eq_eq_sub P 0 (scrambledStack f 0) (range N) 1
  have h2 : (range N).filter (fun k => (step P 0 (scrambledStack f 0 k) : ℕ) < (1 : Fin 2) + 1) =
      range N := filter_true_of_mem fun k _ => (step P 0 (scrambledStack f 0 k)).isLt
  have h1 : (range N).filter (fun k => (step P 0 (scrambledStack f 0 k) : ℕ) < (1 : Fin 2)) =
      (range N).filter fun k => scrambledVdc (f 0) k ≤ cumProb P 0 1 :=
    filter_congr fun k _ => step_lt_iff hP 0 (scrambledVdc_mem_Icc (f 0) k).2 le_rfl
  rw [h2, h1, card_range] at h
  exact h

/-- **Departures `1 → 0` of a two-state stack path**: `N_{10}(T) = #{k < N_1 : u k ≤
cs_{1,1}}`. -/
theorem transCount_one_zero_eq {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (x₀ : Fin 2)
    (f : Fin 2 → ℕ → ℕ → Bool) (T : ℕ) :
    (transCount (stackPath P x₀ (scrambledStack f)) 1 0 T : ℝ) =
        (((range (occCount (stackPath P x₀ (scrambledStack f)) 1 T)).filter
          fun k => scrambledVdc (f 1) k ≤ cumProb P 1 1).card : ℝ) := by
  set N := occCount (stackPath P x₀ (scrambledStack f)) 1 T
  rw [transCount_stackDrive]
  have h := card_filter_step_eq_eq_sub P 1 (scrambledStack f 1) (range N) 0
  have h0 : (range N).filter (fun k => (step P 1 (scrambledStack f 1 k) : ℕ) < (0 : Fin 2)) =
      ∅ := filter_eq_empty_iff.2 fun k _ hk => Nat.not_lt_zero _ hk
  have h1 : (range N).filter (fun k => (step P 1 (scrambledStack f 1 k) : ℕ) < (0 : Fin 2) + 1) =
      (range N).filter fun k => scrambledVdc (f 1) k ≤ cumProb P 1 1 :=
    filter_congr fun k _ => step_lt_iff hP 1 (scrambledVdc_mem_Icc (f 1) k).2 le_rfl
  rw [h0, h1, card_empty, Nat.cast_zero, sub_zero] at h
  exact h

/-- **Initial segments of different lengths** differ by a segment:
`|E(N) − E(H)| ≤ 2 ⌊log₂ |N − H|⌋ + 3`. -/
theorem abs_segErr_zero_sub_le (f : ℕ → ℕ → Bool) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (N H : ℕ) : |segErr (scrambledVdc f) x 0 N - segErr (scrambledVdc f) x 0 H| ≤
      2 * (Nat.log 2 (N - H + (H - N)) : ℝ) + 3 := by
  rcases le_total H N with hHN | hNH
  · have e : N = H + (N - H) := by omega
    have hd : N - H + (H - N) = N - H := by omega
    rw [hd, e, segErr_add, zero_add, add_sub_cancel_left]
    have := abs_segErr_scrambledVdc_log_le f hx0 hx1 H (N - H)
    simpa only [Nat.add_sub_cancel_left] using this
  · have e : H = N + (H - N) := by omega
    have hd : N - H + (H - N) = H - N := by omega
    rw [hd, e, segErr_add, zero_add, sub_add_cancel_left, abs_neg]
    have := abs_segErr_scrambledVdc_log_le f hx0 hx1 N (H - N)
    simpa only [Nat.add_sub_cancel_left] using this

/-- **The occupation error at `T = 2^k` is bounded, for every flip table** (any `p ∈ [0,1)`):
there is `C` (depending only on `p`) with `|N_0(2^k) − 2^k/2| ≤ C` for all `k`, all flip
tables and both starting states. -/
theorem abs_occCount_symChain_pow_two_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃ C : ℝ, ∀ (f : Fin 2 → ℕ → ℕ → Bool) (x₀ : Fin 2) (k : ℕ),
      |(occCount (stackPath (symChain p) x₀ (scrambledStack f)) 0 (2 ^ k) : ℝ) - 2 ^ k / 2| ≤
        C := by
  obtain ⟨D, hD⟩ := exists_le_of_mul_le_log (c := 2 * (1 - p)) (A := 9) (B := 4)
    (by linarith) (by norm_num)
  refine ⟨max D 1, fun f x₀ k => ?_⟩
  have hP := isStochastic_symChain hp0 hp1.le
  set path := stackPath (symChain p) x₀ (scrambledStack f) with hpath
  set N0 := occCount path 0 (2 ^ k) with hN0
  set N1 := occCount path 1 (2 ^ k) with hN1
  have hsum : N0 + N1 = 2 ^ k := by
    have := sum_occCount path (2 ^ k)
    rwa [Fin.sum_univ_two] at this
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `T = 1`
    have h1 : N0 ≤ 1 := by rw [pow_zero] at hsum; omega
    refine le_trans ?_ (le_max_right _ _)
    rw [pow_zero, abs_le]
    have : (N0 : ℝ) ≤ 1 := by exact_mod_cast h1
    constructor <;> [linarith [Nat.cast_nonneg (α := ℝ) N0]; linarith]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set H := 2 ^ m with hH
  have hsum' : N0 + N1 = 2 * H := by rw [hsum, pow_succ, mul_comm]
  set d := N0 - H + (H - N0) with hd
  have hd1 : N1 - H + (H - N1) = d := by omega
  -- flow balance
  have hflow :
      |(transCount path 0 1 (2 ^ (m + 1)) : ℝ) - transCount path 1 0 (2 ^ (m + 1))| ≤ 1 := by
    have h := abs_flowBalance_le path 0 (2 ^ (m + 1))
    rw [Fin.sum_univ_two, Fin.sum_univ_two, abs_le] at h
    push_cast at h
    have hz1 : -1 ≤ (transCount path 0 1 (2 ^ (m + 1)) : ℤ) - transCount path 1 0 (2 ^ (m + 1)) :=
      by omega
    have hz2 : (transCount path 0 1 (2 ^ (m + 1)) : ℤ) - transCount path 1 0 (2 ^ (m + 1)) ≤ 1 :=
      by omega
    rw [abs_le]
    constructor
    · exact_mod_cast hz1
    · exact_mod_cast hz2
  -- the two threshold identities
  have hc0 : cumProb (symChain p) 0 1 = p := by rw [cumProb_one_fin_two]; simp [symChain]
  have hc1 : cumProb (symChain p) 1 1 = 1 - p := by rw [cumProb_one_fin_two]; simp [symChain]
  have h01 := transCount_zero_one_eq hP x₀ f (2 ^ (m + 1))
  have h10 := transCount_one_zero_eq hP x₀ f (2 ^ (m + 1))
  rw [hc0, card_filter_le_eq_add_segErr] at h01
  rw [hc1, card_filter_le_eq_add_segErr] at h10
  set E0 := segErr (scrambledVdc (f 0)) p 0 N0
  set E1 := segErr (scrambledVdc (f 1)) (1 - p) 0 N1
  -- the errors at `H` (one aligned block) and the segments of length `d`
  have hB0 : |segErr (scrambledVdc (f 0)) p 0 H| ≤ 1 := by
    have := abs_segErr_scrambledVdc_block_le (f 0) m 0 hp0 hp1.le
    rwa [zero_mul] at this
  have hB1 : |segErr (scrambledVdc (f 1)) (1 - p) 0 H| ≤ 1 := by
    have := abs_segErr_scrambledVdc_block_le (f 1) m 0 (x := 1 - p) (by linarith)
      (by linarith)
    rwa [zero_mul] at this
  have hS0 := abs_segErr_zero_sub_le (f 0) hp0 hp1.le N0 H
  have hS1 := abs_segErr_zero_sub_le (f 1) (x := 1 - p) (by linarith) (by linarith) N1 H
  rw [← hd] at hS0
  rw [hd1] at hS1
  have hE0 : |E0| ≤ 1 + (2 * (Nat.log 2 d : ℝ) + 3) := by
    have := abs_sub_abs_le_abs_sub E0 (segErr (scrambledVdc (f 0)) p 0 H)
    linarith
  have hE1 : |E1| ≤ 1 + (2 * (Nat.log 2 d : ℝ) + 3) := by
    have := abs_sub_abs_le_abs_sub E1 (segErr (scrambledVdc (f 1)) (1 - p) 0 H)
    linarith
  -- `|N0 − N1| = 2 d` and `|N0 − H| = d`
  have hdabs : |(N0 : ℝ) - H| = d := by
    rcases le_total H N0 with h | h
    · have e : (d : ℝ) = N0 - H := by
        rw [hd, show H - N0 = 0 by omega, add_zero, Nat.cast_sub h]
      rw [e, abs_of_nonneg (by linarith)]
    · have e : (d : ℝ) = H - N0 := by
        rw [hd, show N0 - H = 0 by omega, zero_add, Nat.cast_sub h]
      rw [e, abs_of_nonpos (by linarith), neg_sub]
  have hN1R : (N1 : ℝ) = 2 * H - N0 := by
    have : ((N0 + N1 : ℕ) : ℝ) = ((2 * H : ℕ) : ℝ) := by rw [hsum']
    push_cast at this
    linarith
  -- the self-consistent inequality
  have key : (1 - p) * ((N0 : ℝ) - N1) =
      ((transCount path 0 1 (2 ^ (m + 1)) : ℝ) - transCount path 1 0 (2 ^ (m + 1))) + E0 + E1 := by
    rw [h01, h10]
    ring
  have hineq : 2 * (1 - p) * d ≤ 9 + 4 * Nat.log 2 d := by
    have h1 : |(1 - p) * ((N0 : ℝ) - N1)| = 2 * (1 - p) * d := by
      rw [hN1R, show (N0 : ℝ) - (2 * H - N0) = 2 * ((N0 : ℝ) - H) by ring, abs_mul, abs_mul,
        abs_of_pos (by linarith : (0 : ℝ) < 1 - p), abs_two, hdabs]
      ring
    have h2 := abs_add_le (((transCount path 0 1 (2 ^ (m + 1)) : ℝ) -
      transCount path 1 0 (2 ^ (m + 1))) + E0) E1
    have h3 := abs_add_le ((transCount path 0 1 (2 ^ (m + 1)) : ℝ) -
      transCount path 1 0 (2 ^ (m + 1))) E0
    rw [← key, h1] at h2
    linarith
  have hdD := hD d hineq
  rw [show ((2 : ℝ) ^ (m + 1)) / 2 = H by rw [hH, pow_succ]; push_cast; ring, hdabs]
  exact hdD.trans (le_max_left _ _)

/-- Along a subsequence `T = 2^k`, convergence in distribution is inherited. -/
theorem tendstoInDistribution_comp_pow_two {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {W : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution W atTop Z (fun _ => μ) μ') :
    TendstoInDistribution (fun k => W (2 ^ k)) atTop Z (fun _ => μ) μ' where
  forall_aemeasurable k := h.forall_aemeasurable (2 ^ k)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- **No CLT along all `T` for the symmetric chain**, under any randomisation of the flip
tables: if every realisation of `ω ↦ f ω` is a flip table, no normalisation
`(N_0(T) − T/2 − b_T)/a_T` converges in distribution to a law without atoms. -/
theorem not_tendstoInDistribution_symChain {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (x₀ : Fin 2)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (F : Ω → Fin 2 → ℕ → ℕ → Bool) (a b : ℕ → ℝ) {Z : Ω' → ℝ} (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath (symChain p) x₀ (scrambledStack (F ω))) 0 T : ℝ) - T / 2 - b T) /
        a T) atTop Z (fun _ => μ) μ' := by
  intro h
  obtain ⟨C, hC⟩ := abs_occCount_symChain_pow_two_le hp0 hp1
  have h2 := tendstoInDistribution_comp_pow_two h
  refine not_tendstoInDistribution_of_abs_sub_le (μ := μ)
    (Y := fun k ω => (occCount (stackPath (symChain p) x₀ (scrambledStack (F ω))) 0 (2 ^ k) : ℤ))
    (y := fun k => (2 : ℝ) ^ k / 2) (C := C)
    (fun k => Eventually.of_forall fun ω => by simpa only [Int.cast_natCast] using hC (F ω) x₀ k)
    (fun k => a (2 ^ k)) (fun k => b (2 ^ k)) hZ ?_
  simpa only [Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat] using h2

/-- **No CLT along all `T`, Owen scrambling** (post #3, code (iii)), for any `p ∈ [0,1)`. -/
theorem not_tendstoInDistribution_symChain_owen {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (x₀ : Fin 2) (a b : ℕ → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Z : Ω' → ℝ} (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath (symChain p) x₀ (scrambledStack (owenTable ω))) 0 T : ℝ) - T / 2 -
        b T) / a T) atTop Z (fun _ => owenMeasure 2) μ' :=
  not_tendstoInDistribution_symChain hp0 hp1 x₀ owenTable a b hZ

/-- **No CLT along all `T`, digital shift** (post #3, code (ii)), for any `p ∈ [0,1)`. -/
theorem not_tendstoInDistribution_symChain_shift {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (x₀ : Fin 2) (a b : ℕ → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Z : Ω' → ℝ} (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath (symChain p) x₀ (scrambledStack (shiftFlips ω))) 0 T : ℝ) - T / 2 -
        b T) / a T) atTop Z (fun _ => shiftMeasure 2) μ' :=
  not_tendstoInDistribution_symChain hp0 hp1 x₀ shiftFlips a b hZ

/-- **The non-dyadic chain `p = 2/3`**: no normalisation of `N_0(T) − T/2` is asymptotically
`N(0,1)` along all `T` under Owen scrambling. -/
theorem not_tendstoInDistribution_symChain_twoThirds_owen (x₀ : Fin 2) (a b : ℕ → ℝ) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath (symChain (2 / 3)) x₀ (scrambledStack (owenTable ω))) 0 T : ℝ) -
        T / 2 - b T) / a T) atTop id (fun _ => owenMeasure 2) (gaussianReal 0 1) :=
  not_tendstoInDistribution_symChain_owen (by norm_num) (by norm_num) x₀ a b
    map_id_gaussianReal_singleton

end RQMCMarkov.ScrambledStacks

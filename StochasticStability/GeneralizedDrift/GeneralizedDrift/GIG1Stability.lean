/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.GIG1Drift
import GeneralizedDrift.GIG1Invariant
import GeneralizedDrift.GIG1Embedding

/-!
# The GI/G/1 queue: the invariant measure (10.52) when `λ > µ` (MT §19.3.3)

Meyn and Tweedie, Theorem 19.3.5, second part (p. 506) and its proof (pp. 507–508): when the
mean interarrival time `λ` exceeds the mean service time `µ`, the GI/G/1 ladder chain
`gig1Ladder H G` has the invariant measure `π̃` of (10.52).

**Where the book's argument fails.**
* (19.77), "`E_{0,y}[τ_{[0]}] < ∞` for `ν`-a.e. `y`", is justified by saying that this quantity
  "does not depend on the detailed hitting distribution on `[0]`". The return time to `[0]` is
  indeed the same for the chain with the structure (19.65), but positivity of that chain
  (Theorem 19.3.4) only gives finiteness for almost every point of its own invariant law on
  `[0]`, which need not dominate `ν` or `H`.
* The busy-period decomposition (19.84), `E_{0,y}[τ_{[0]}] = 1 + η Σ_{n ≥ 0} G^{n∗}[0, y]`, is
  false for the GI/G/1 queue (`eq_19_84_counterexample`, a D/D/1 queue with `λ = 1`,
  `µ = 3/5`): it fails both as printed (sum from `n = 0`, at `y = 6/5`) and with the sum from
  `n = 1` (at `y = 3/2`). Rearranging the order of service gives independent sub-busy-periods
  only for Poisson arrivals; with renewal arrivals the residual interarrival time at the start of
  each sub-busy-period depends on the past.

**The correct statement and its proof.** `theorem_19_3_5_ii`: if `µ < λ` (`λ = ∞` allowed),
then (19.82) holds, `∫ H(dy) E_{(0,y)}[τ_{[0]}] < ∞`, so `π̃(X) < ∞` and `π̃` is invariant
(Theorem 10.5.4, `theorem_10_5_4_invariant`).
* `lintegral_meanReturnTime_gig1`: (19.82) is the mean number of customers in a busy period of
  the queue built from its primitives (`gig1_isMarkovChain`, `law_eq_pathMeasure`).
* `queueN_ne_zero_iff`, `arrT_lt_sum_of_busy`: while every arrival finds the server busy,
  `Tₙ < s₀ + ⋯ + s_{n−1}`; `mem_wE_of_le_firstReturn`: so the busy period is dominated by the
  first passage `τ'` of the walk with increments `Uⱼ = (sⱼ − aⱼ + c)⁺` below the line `cn`.
* Wald's bound: `wald_pathwise` (`c min(τ', N) ≤ c + Σ_{j < min(τ', N)} Uⱼ`),
  `lintegral_wE_indicator` (`E[Uᵢ 1{τ' > i}] = E[U₀] P(τ' > i)`, from the independence of past
  and future, `gig1_law_past_future`), `tsum_wE_le` (`E[τ'] ≤ c/(c − E U₀)`), and
  `exists_wald_trunc` (`E U₀ < c` for some `c`, from `µ < λ` by monotone convergence).
* `gig1Tilde_univ_le`: `π̃(X) ≤ ∫ H(dy) (1 + E_{(0,y)}[τ_{[0]}])`, since the `k`-th term of
  (10.52) is the expected number of visits to rung `k` before the return to `[0]`.

**Hypotheses.** Service times `> 0` (`H(−∞, 0] = 0`) with finite mean, interarrival times
`≥ 0`, as in `gig1_isMarkovChain`. (19.77) is obtained for `H`-a.e. `y`, which is what (19.82)
needs.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- A customer arriving at `Tₙ`, `n ≥ 1`, finds someone in the system iff the previous customer
is still there: `Nₙ ≠ 0 ↔ Tₙ < D_{n−1}`. -/
theorem queueN_ne_zero_iff {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) {n : ℕ} (hn : 1 ≤ n) :
    queueN a s n ≠ 0 ↔ arrT a n < depT a s (n - 1) := by
  rw [queueN, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨m, hm⟩
    rw [Finset.mem_filter, Finset.mem_range] at hm
    exact hm.2.trans_le (depT_mono hs (by omega))
  · intro h
    exact ⟨n - 1, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h⟩⟩

/-- **A busy period without idling** (pathwise): if the customers arriving at `T₁, …, Tᵢ` all
find the server busy, then `Dₙ = s₀ + ⋯ + sₙ` for `n ≤ i` and `Tₙ < s₀ + ⋯ + s_{n−1}` for
`1 ≤ n ≤ i`. -/
theorem arrT_lt_sum_of_busy {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) {i : ℕ}
    (h : ∀ n, 1 ≤ n → n ≤ i → queueN a s n ≠ 0) :
    ∀ n, 1 ≤ n → n ≤ i → arrT a n < ∑ j ∈ Finset.range n, s j := by
  have hD : ∀ n, n ≤ i → depT a s n = ∑ j ∈ Finset.range (n + 1), s j := by
    intro n
    induction n with
    | zero => intro _; simp [depT]
    | succ n ih =>
      intro hn
      have hb := (queueN_ne_zero_iff hs (n := n + 1) (by omega)).1 (h (n + 1) (by omega) hn)
      simp only [Nat.add_sub_cancel] at hb
      rw [depT, max_eq_left hb.le, ih (by omega), Finset.sum_range_succ _ (n + 1)]
  intro n h1 h2
  have hb := (queueN_ne_zero_iff hs h1).1 (h n h1 h2)
  rwa [hD (n - 1) (by omega), show n - 1 + 1 = n by omega] at hb

/-- The D/D/1 example: unit interarrival times. -/
def ddArr : ℕ → ℝ := fun _ => 1

/-- Service `y` for the first customer, `3/5` for the others. -/
noncomputable def ddServ (y : ℝ) : ℕ → ℝ := fun i => if i = 0 then y else 3 / 5

theorem ddServ_pos {y : ℝ} (hy : 0 < y) (i : ℕ) : 0 < ddServ y i := by
  unfold ddServ; split_ifs <;> norm_num [hy]

/-- **Correction: the busy-period decomposition (19.84) fails for the GI/G/1 queue** (MT p. 507).
With deterministic interarrival times `1` (`G = δ₁`, `λ = 1`) and services `3/5` (`H = δ_{3/5}`,
`µ = 3/5`), a busy period started by a service `3/5` has one customer (`η = 1`), and a service
`y ∈ {6/5, 3/2}` sees one arrival during `[0, y]` (`Σ_{n ≥ 1} G^{n∗}[0, y] = 1`, so
`Σ_{n ≥ 0} G^{n∗}[0, y] = 2`). But the busy period started by `y = 6/5` has `2` customers
(`N₁ ≠ 0`, `N₂ = 0`), while (19.84) as printed gives `1 + η · 2 = 3`; and the one started by
`y = 3/2` has `3` customers (`N₁, N₂ ≠ 0`, `N₃ = 0`), while (19.84) with the sum from `n = 1`
gives `1 + η · 1 = 2`. The rearrangement of service order behind (19.84) produces independent
sub-busy-periods only for Poisson arrivals. -/
theorem eq_19_84_counterexample :
    queueN ddArr (ddServ (3 / 5)) 1 = 0 ∧
    (∀ y ∈ ({6 / 5, 3 / 2} : Set ℝ), arrT ddArr 1 ≤ y ∧ y < arrT ddArr 2) ∧
    (queueN ddArr (ddServ (6 / 5)) 1 ≠ 0 ∧ queueN ddArr (ddServ (6 / 5)) 2 = 0) ∧
    (queueN ddArr (ddServ (3 / 2)) 1 ≠ 0 ∧ queueN ddArr (ddServ (3 / 2)) 2 ≠ 0 ∧
      queueN ddArr (ddServ (3 / 2)) 3 = 0) := by
  have h1 := ddServ_pos (y := 3 / 5) (by norm_num)
  have h2 := ddServ_pos (y := 6 / 5) (by norm_num)
  have h3 := ddServ_pos (y := 3 / 2) (by norm_num)
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · by_contra h
    have := (queueN_ne_zero_iff h1 le_rfl).1 h
    norm_num [arrT, depT, ddArr, ddServ] at this
  · rintro y (rfl | rfl) <;> norm_num [arrT, ddArr, Finset.sum_range_succ]
  · rw [queueN_ne_zero_iff h2 le_rfl]
    norm_num [arrT, depT, ddArr, ddServ]
  · by_contra h
    have := (queueN_ne_zero_iff h2 (by norm_num)).1 h
    norm_num [arrT, depT, ddArr, ddServ, Finset.sum_range_succ] at this
  · rw [queueN_ne_zero_iff h3 le_rfl]
    norm_num [arrT, depT, ddArr, ddServ]
  · rw [queueN_ne_zero_iff h3 (by norm_num)]
    norm_num [arrT, depT, ddArr, ddServ, Finset.sum_range_succ]
  · by_contra h
    have := (queueN_ne_zero_iff h3 (by norm_num)).1 h
    norm_num [arrT, depT, ddArr, ddServ, Finset.sum_range_succ] at this

/-! ### Wald's bound for the busy period -/

/-- The truncated increments `Uⱼ = (sⱼ − aⱼ + c)⁺` on the canonical space `(a, s)`. -/
noncomputable def wU (c : ℝ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (ω.2 j - ω.1 j + c)

/-- `{τ' > i}`: `Σ_{j<n} Uⱼ > cn` for `1 ≤ n ≤ i`. -/
def wE (c : ℝ) (i : ℕ) : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {ω | ∀ n, 1 ≤ n → n ≤ i → ENNReal.ofReal c * n < ∑ j ∈ Finset.range n, wU c ω j}

theorem measurable_wU (c : ℝ) (j : ℕ) : Measurable fun ω => wU c ω j := by
  have h1 : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => ω.2 j := (measurable_pi_apply j).comp
    measurable_snd
  have h2 : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => ω.1 j := (measurable_pi_apply j).comp
    measurable_fst
  unfold wU; fun_prop

theorem measurableSet_wE (c : ℝ) (i : ℕ) : MeasurableSet (wE c i) := by
  have e : wE c i = ⋂ n ∈ Finset.Icc 1 i,
      {ω | ENNReal.ofReal c * n < ∑ j ∈ Finset.range n, wU c ω j} := by
    ext ω
    simp only [wE, mem_ofPred_eq, mem_iInter, Finset.mem_Icc]
    exact ⟨fun h n hn => h n hn.1 hn.2, fun h n h1 h2 => h n ⟨h1, h2⟩⟩
  rw [e]
  exact Finset.measurableSet_biInter _ fun n _ => measurableSet_lt measurable_const
    (Finset.measurable_sum _ fun j _ => measurable_wU c j)

theorem wE_anti {c : ℝ} {i i' : ℕ} (h : i ≤ i') : wE c i' ⊆ wE c i :=
  fun _ hω n h1 h2 => hω n h1 (h2.trans h)

theorem wE_zero (c : ℝ) : wE c 0 = univ := by
  ext ω; simp only [wE, mem_ofPred_eq, mem_univ, iff_true]; intro n h1 h2; omega

/-- **The pathwise Wald inequality**: `c · min(τ', N) ≤ c + Σ_{j < min(τ', N)} Uⱼ`, with
`min(τ', N) = Σ_{i<N} 1{τ' > i}`. -/
theorem wald_pathwise (c : ℝ) (N : ℕ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    ENNReal.ofReal c * ∑ i ∈ Finset.range N, (wE c i).indicator 1 ω ≤
      ENNReal.ofReal c + ∑ i ∈ Finset.range N, (wE c i).indicator (fun ω => wU c ω i) ω := by
  induction N with
  | zero => simp
  | succ N ih =>
    by_cases hN : ω ∈ wE c N
    · have hall : ∀ i ∈ Finset.range (N + 1), ω ∈ wE c i := fun i hi =>
        wE_anti (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hN
      rw [Finset.sum_congr rfl fun i hi =>
          indicator_of_mem (hall i hi) (1 : (ℕ → ℝ) × (ℕ → ℝ) → ℝ≥0∞),
        Finset.sum_congr rfl fun i hi => indicator_of_mem (hall i hi) (fun ω => wU c ω i)]
      simp only [Pi.one_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · subst h0; simp
      · have h := hN N hpos le_rfl
        rw [Finset.sum_range_succ]
        push_cast
        calc ENNReal.ofReal c * (N + 1) = ENNReal.ofReal c * N + ENNReal.ofReal c := by ring
          _ ≤ ∑ j ∈ Finset.range N, wU c ω j + ENNReal.ofReal c := add_le_add h.le le_rfl
          _ ≤ ENNReal.ofReal c + (∑ j ∈ Finset.range N, wU c ω j + wU c ω N) := by
              rw [add_comm]; exact add_le_add le_rfl le_self_add
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, indicator_of_notMem hN,
        indicator_of_notMem hN, add_zero, add_zero]
      exact ih

/-- `{τ' > i}` depends only on the first `i` interarrival and service times. -/
theorem mem_wE_truncSeq_iff (c : ℝ) (i : ℕ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    (truncSeq i ω.1, truncSeq i ω.2) ∈ wE c i ↔ ω ∈ wE c i := by
  have h : ∀ n, n ≤ i → ∑ j ∈ Finset.range n, wU c (truncSeq i ω.1, truncSeq i ω.2) j =
      ∑ j ∈ Finset.range n, wU c ω j := fun n hn => Finset.sum_congr rfl fun j hj => by
    have hj' : j < i := (Finset.mem_range.1 hj).trans_le hn
    simp [wU, truncSeq, hj']
  simp only [wE, mem_ofPred_eq]
  exact ⟨fun H n h1 h2 => (h n h2) ▸ H n h1 h2, fun H n h1 h2 => (h n h2).symm ▸ H n h1 h2⟩

/-- **Wald's step**: `E[Uᵢ 1{τ' > i}] = E[U₀] P(τ' > i)`, since `{τ' > i}` depends on the first
`i` coordinates and `Uᵢ` on the `i`-th (`gig1_law_past_future`). -/
theorem lintegral_wE_indicator (G H : Measure ℝ) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] (c : ℝ) (i : ℕ) :
    ∫⁻ ω, (wE c i).indicator (fun ω => wU c ω i) ω ∂((Measure.infinitePi fun _ : ℕ => G).prod
      (Measure.infinitePi fun _ : ℕ => H)) =
      (Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H) (wE c i) *
        ∫⁻ ω, wU c ω 0 ∂((Measure.infinitePi fun _ : ℕ => G).prod
          (Measure.infinitePi fun _ : ℕ => H)) := by
  set μ := (Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H) with hμ
  cases i with
  | zero =>
    rw [wE_zero, indicator_univ, measure_univ, one_mul]
  | succ k =>
    have hlaw := gig1_law_past_future G H (k + 1) k
    rw [← hμ] at hlaw
    set T : (ℕ → ℝ) × (ℕ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
      fun ω => (truncSeq (k + 1) ω.1, truncSeq (k + 1) ω.2) with hT
    have hTm : Measurable T := ((measurable_truncSeq _).comp measurable_fst).prodMk
      ((measurable_truncSeq _).comp measurable_snd)
    have hFm : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
        ((truncSeq (k + 1) ω.1, truncSeq (k + 1) ω.2),
          (tailSeq (k + 1) ω.1, tailSeq (k + 1) ω.2)) :=
      hTm.prodMk (((measurable_tailSeq _).comp measurable_fst).prodMk
        ((measurable_tailSeq _).comp measurable_snd))
    set g : ((ℕ → ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ≥0∞ :=
      fun q => (wE c (k + 1)).indicator 1 q.1 * wU c q.2 0 with hg
    have hgm : Measurable g :=
      ((measurable_one.indicator (measurableSet_wE c (k + 1))).comp measurable_fst).mul
        ((measurable_wU c 0).comp measurable_snd)
    have hpt : ∀ ω, (wE c (k + 1)).indicator (fun ω => wU c ω (k + 1)) ω =
        g ((truncSeq (k + 1) ω.1, truncSeq (k + 1) ω.2),
          (tailSeq (k + 1) ω.1, tailSeq (k + 1) ω.2)) := fun ω => by
      simp only [hg]
      by_cases hω : ω ∈ wE c (k + 1)
      · rw [indicator_of_mem hω, indicator_of_mem ((mem_wE_truncSeq_iff c _ ω).2 hω),
          Pi.one_apply, one_mul]
        simp [wU, tailSeq]
      · rw [indicator_of_notMem hω, indicator_of_notMem (fun h =>
          hω ((mem_wE_truncSeq_iff c _ ω).1 h)), zero_mul]
    simp_rw [hpt]
    rw [← lintegral_map hgm hFm, hlaw, lintegral_prod_mul
      ((measurable_one.indicator (measurableSet_wE c (k + 1))).aemeasurable)
      (measurable_wU c 0).aemeasurable, lintegral_indicator_one (measurableSet_wE c (k + 1)),
      Measure.map_apply hTm (measurableSet_wE c (k + 1))]
    congr 1
    congr 1
    ext ω
    exact mem_wE_truncSeq_iff c _ ω

/-- **Wald's bound** for the truncated walk: if `m = E[U₀] < c`, then
`Σᵢ P(τ' > i) ≤ c/(c − m)`. -/
theorem tsum_wE_le (G H : Measure ℝ) [IsProbabilityMeasure G] [IsProbabilityMeasure H] (c : ℝ)
    (hm : ∫⁻ ω, wU c ω 0 ∂((Measure.infinitePi fun _ : ℕ => G).prod
      (Measure.infinitePi fun _ : ℕ => H)) < ENNReal.ofReal c) :
    ∑' i, (Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H) (wE c i) ≤
      ENNReal.ofReal c / (ENNReal.ofReal c -
        ∫⁻ ω, wU c ω 0 ∂((Measure.infinitePi fun _ : ℕ => G).prod
        (Measure.infinitePi fun _ : ℕ => H))) := by
  set μ := (Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H) with hμ
  set m := ∫⁻ ω, wU c ω 0 ∂μ with hmdef
  have hmt : m ≠ ∞ := ne_top_of_lt hm
  have hcm : ENNReal.ofReal c - m ≠ 0 := (tsub_pos_of_lt hm).ne'
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  set A := ∑ i ∈ Finset.range N, μ (wE c i) with hA
  have hAt : A ≠ ∞ := ENNReal.sum_ne_top.2 fun i _ => measure_ne_top μ _
  have hint := lintegral_mono (μ := μ) (wald_pathwise c N)
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ =>
      measurable_one.indicator (measurableSet_wE c i)),
    lintegral_finsetSum _ fun i _ => measurable_one.indicator (measurableSet_wE c i),
    lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_finsetSum _ fun i _ => (measurable_wU c i).indicator (measurableSet_wE c i)]
    at hint
  have h1 : ∀ i, ∫⁻ a, (wE c i).indicator 1 a ∂μ = μ (wE c i) := fun i =>
    lintegral_indicator_one (measurableSet_wE c i)
  rw [Finset.sum_congr rfl (fun i _ => h1 i),
    Finset.sum_congr rfl (fun i _ => lintegral_wE_indicator G H c i)] at hint
  rw [← Finset.sum_mul, ← hA, ← hmdef] at hint
  rw [ENNReal.le_div_iff_mul_le (Or.inl hcm) (Or.inr ENNReal.ofReal_ne_top), mul_comm,
    ENNReal.sub_mul (fun _ _ => hAt), tsub_le_iff_right, mul_comm m A]
  exact hint

/-- `∫ f(s₀) dμ = ∫ f dH` and `∫ f(a₀) dμ = ∫ f dG` on the canonical space. -/
theorem lintegral_coord_zero_prod (G H : Measure ℝ) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (ω.2 0) ∂((Measure.infinitePi fun _ : ℕ => G).prod
      (Measure.infinitePi fun _ : ℕ => H)) = ∫⁻ x, f x ∂H ∧
    ∫⁻ ω, f (ω.1 0) ∂((Measure.infinitePi fun _ : ℕ => G).prod
      (Measure.infinitePi fun _ : ℕ => H)) = ∫⁻ x, f x ∂G := by
  have h2 : Measurable fun s : ℕ → ℝ => f (s 0) := hf.comp (measurable_pi_apply 0)
  constructor
  · rw [lintegral_prod (f := fun ω : (ℕ → ℝ) × (ℕ → ℝ) => f (ω.2 0))
      (h2.comp measurable_snd).aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    rw [← lintegral_map hf (measurable_pi_apply 0), Measure.infinitePi_map_eval]
  · rw [lintegral_prod (f := fun ω : (ℕ → ℝ) × (ℕ → ℝ) => f (ω.1 0))
      (h2.comp measurable_fst).aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    rw [← lintegral_map hf (measurable_pi_apply 0), Measure.infinitePi_map_eval]

/-- **The truncation level** (from `µ < λ`): some `c > 0` has `E[(s₀ − a₀ + c)⁺] < c`. -/
theorem exists_wald_trunc (G H : Measure ℝ) [IsProbabilityMeasure G] [IsProbabilityMeasure H]
    (hG0 : G (Iio 0) = 0) (hlt : renMean H < renMean G) :
    ∃ c : ℝ, 0 < c ∧ ∫⁻ ω, wU c ω 0 ∂((Measure.infinitePi fun _ : ℕ => G).prod
      (Measure.infinitePi fun _ : ℕ => H)) < ENNReal.ofReal c := by
  set f : ℕ → ℝ → ℝ≥0∞ := fun n a => ENNReal.ofReal (min a ((n : ℝ) + 1)) with hfdef
  have hfm : ∀ n, Measurable (f n) := fun n => by rw [hfdef]; fun_prop
  have hmono : Monotone f := fun m n hmn a => ENNReal.ofReal_le_ofReal
    (min_le_min le_rfl (by exact_mod_cast Nat.add_le_add_right hmn 1))
  have hsup : ∀ a, ⨆ n, f n a = ENNReal.ofReal a := fun a => by
    refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
    obtain ⟨n, hn⟩ := exists_nat_ge a
    exact le_iSup_of_le n (le_of_eq (by rw [hfdef]; simp only; rw [min_eq_left (by linarith)]))
  have hlam : ⨆ n, ∫⁻ a, f n a ∂G = renMean G := by
    rw [← lintegral_iSup hfm hmono]
    simp_rw [hsup]
  rw [← hlam] at hlt
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
  set c : ℝ := (n : ℝ) + 1 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, ?_⟩
  have hI : ∫⁻ a, ENNReal.ofReal (c - a) ∂G + ∫⁻ a, f n a ∂G = ENNReal.ofReal c := by
    rw [← lintegral_add_left (by fun_prop)]
    rw [lintegral_congr_ae (g := fun _ => ENNReal.ofReal c) ((ae_nonneg_of_Iio hG0).mono
      fun a ha => ?_), lintegral_const, measure_univ, mul_one]
    simp only [hfdef, ← hc]
    rcases le_total a c with h | h
    · rw [min_eq_left h, ← ENNReal.ofReal_add (by linarith) ha]; congr 1; ring
    · rw [min_eq_right h, ENNReal.ofReal_of_nonpos (by linarith), zero_add]
  have hIt : ∫⁻ a, ENNReal.ofReal (c - a) ∂G ≠ ∞ := by
    intro h; rw [h, top_add] at hI; exact ENNReal.ofReal_ne_top hI.symm
  have hm : ∫⁻ ω, wU c ω 0 ∂((Measure.infinitePi fun _ : ℕ => G).prod
      (Measure.infinitePi fun _ : ℕ => H)) ≤ renMean H + ∫⁻ a, ENNReal.ofReal (c - a) ∂G := by
    calc ∫⁻ ω, wU c ω 0 ∂((Measure.infinitePi fun _ : ℕ => G).prod
          (Measure.infinitePi fun _ : ℕ => H))
        ≤ ∫⁻ ω, (ENNReal.ofReal (ω.2 0) + ENNReal.ofReal (c - ω.1 0))
          ∂((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)) :=
          lintegral_mono fun ω => by
            rw [wU, show ω.2 0 - ω.1 0 + c = ω.2 0 + (c - ω.1 0) by ring]
            exact ENNReal.ofReal_add_le
      _ = renMean H + ∫⁻ a, ENNReal.ofReal (c - a) ∂G := by
          rw [lintegral_add_left (f := fun ω : (ℕ → ℝ) × (ℕ → ℝ) => ENNReal.ofReal (ω.2 0))
            (ENNReal.measurable_ofReal.comp ((measurable_pi_apply 0).comp measurable_snd)),
            (lintegral_coord_zero_prod G H ENNReal.measurable_ofReal).1,
            (lintegral_coord_zero_prod G H (f := fun a => ENNReal.ofReal (c - a))
              (by fun_prop)).2]
  calc _ ≤ renMean H + ∫⁻ a, ENNReal.ofReal (c - a) ∂G := hm
    _ < ∫⁻ a, f n a ∂G + ∫⁻ a, ENNReal.ofReal (c - a) ∂G := ENNReal.add_lt_add_right hIt hn
    _ = ENNReal.ofReal c := by rw [add_comm]; exact hI

/-- `(Σ xⱼ)⁺ ≤ Σ xⱼ⁺`. -/
theorem ofReal_sum_range_le (x : ℕ → ℝ) (n : ℕ) :
    ENNReal.ofReal (∑ j ∈ Finset.range n, x j) ≤ ∑ j ∈ Finset.range n, ENNReal.ofReal (x j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact ENNReal.ofReal_add_le.trans (add_le_add ih le_rfl)

/-- **The busy period is dominated by the truncated walk** (pathwise): if the first `n`
customers after the one starting the busy period all find the server busy (`τ_{[0]} ≥ n + 1`),
then `τ' > n`. -/
theorem mem_wE_of_le_firstReturn {c : ℝ} (hc : 0 < c) {ω : (ℕ → ℝ) × (ℕ → ℝ)}
    (hs : ∀ i, 0 < ω.2 i) {n : ℕ}
    (h : WithTop.some (n + 1) ≤
      firstReturn (rung 0) (fun k => (queueN ω.1 ω.2 k, queueR ω.1 ω.2 k))) :
    ω ∈ wE c n := by
  rw [le_firstReturn_iff] at h
  have hb : ∀ j, 1 ≤ j → j ≤ n → queueN ω.1 ω.2 j ≠ 0 := fun j h1 h2 hj =>
    h j h1 (by omega) (by simp [rung, hj])
  have hlt := arrT_lt_sum_of_busy hs hb
  intro j h1 h2
  have hsum : ∑ l ∈ Finset.range j, (ω.2 l - ω.1 l + c) =
      ∑ l ∈ Finset.range j, ω.2 l - arrT ω.1 j + c * j := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, arrT]; ring
  have hpos : c * j < ∑ l ∈ Finset.range j, (ω.2 l - ω.1 l + c) := by
    rw [hsum]; linarith [hlt j h1 h2]
  calc ENNReal.ofReal c * j = ENNReal.ofReal (c * j) := by
        rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_natCast]
    _ < ENNReal.ofReal (∑ l ∈ Finset.range j, (ω.2 l - ω.1 l + c)) :=
        (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hpos)).2 hpos
    _ ≤ ∑ l ∈ Finset.range j, wU c ω l := ofReal_sum_range_le _ j

/-- **(19.82) from the queue** (MT p. 506): `∫ H(dy) E_{(0,y)}[τ_{[0]}]` is the mean number of
customers in a busy period of the queue started from empty, `E[τ_{[0]}(Φ)]` for `Φ₀ ∼ δ₀ ⊗ H`. -/
theorem lintegral_meanReturnTime_gig1 (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] [IsMarkovKernel (gig1Ladder H G)] (hH0 : H (Iic 0) = 0)
    (hG0 : G (Iio 0) = 0) :
    ∫⁻ y, meanReturnTime (gig1Ladder H G) (rung 0) (0, y) ∂H =
      ∫⁻ ω, ENat.toENNReal (firstReturn (rung 0)
        (fun k => (queueN ω.1 ω.2 k, queueR ω.1 ω.2 k)))
        ∂((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)) := by
  have hmc := gig1_isMarkovChain H G hH0 hG0
  have hlaw := law_eq_pathMeasure (gig1Ladder H G) ((Measure.dirac 0).prod H) hmc
  have hpath : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
      fun k => (queueN ω.1 ω.2 k, queueR ω.1 ω.2 k) := measurable_pi_iff.2 hmc.measurable
  have hfr := measurable_toENNReal_firstReturn (X := ℕ × ℝ) (measurableSet_rung 0)
  have := isMarkovKernel_pathKernel (gig1Ladder H G)
  rw [← lintegral_map hfr hpath, hlaw, pathMeasure_eq_comp,
    Measure.lintegral_bind (Kernel.aemeasurable _) hfr.aemeasurable, Measure.dirac_prod,
    lintegral_map hfr.lintegral_kernel measurable_prodMk_left]
  rfl

/-- `π̃(X) ≤ ∫ H(dy) (1 + E_{(0,y)}[τ_{[0]}])`: the `k`-th term of (10.52) is the expected
number of visits to rung `k` before the return to `[0]` (`ladderS_eq_pow`, (10.42)). -/
theorem gig1Tilde_univ_le (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    [IsMarkovKernel (gig1Ladder H G)] :
    gig1Tilde H G univ ≤ ∫⁻ y, (1 + meanReturnTime (gig1Ladder H G) (rung 0) (0, y)) ∂H := by
  have hP : IsMarkovKernel (ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G)) :=
    ‹IsMarkovKernel (gig1Ladder H G)›
  have hk : ∀ k : ℕ, ((((ladS (gig1Lambda H G) (gig1LambdaStar H G)) ^ k : Kernel ℝ ℝ) ∘ₘ
      H).map (Prod.mk k)) univ =
      ∫⁻ y, ((ladS (gig1Lambda H G) (gig1LambdaStar H G)) ^ k) y univ ∂H := fun k => by
    rw [Measure.map_apply measurable_prodMk_left MeasurableSet.univ, preimage_univ,
      Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
  rw [gig1Tilde, Measure.sum_apply _ MeasurableSet.univ, tsum_congr hk]
  rw [← lintegral_tsum fun k => (Kernel.measurable_coe _ MeasurableSet.univ).aemeasurable]
  refine lintegral_mono fun y => ?_
  rw [tsum_eq_zero_add' ENNReal.summable, pow_zero_apply, measure_univ]
  refine add_le_add le_rfl ?_
  set U := tabooPotKernel (ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G))
    (measurableSet_rung 0) ((0 : ℕ), y)
  have hterm : ∀ k : ℕ, ((ladS (gig1Lambda H G) (gig1LambdaStar H G)) ^ (k + 1)) y univ =
      U ({k + 1} ×ˢ univ) := fun k => by
    rw [← ladderS_eq_pow _ _ (Nat.le_add_left 1 k), ladderS_apply _ _ _ _ MeasurableSet.univ]
  simp_rw [hterm]
  rw [← measure_iUnion (fun i j hij => ?_) fun k => (measurableSet_singleton _).prod
    MeasurableSet.univ, meanReturnTime_eq_tabooPotKernel _ (measurableSet_rung 0)]
  · exact measure_mono (subset_univ _)
  · refine Set.disjoint_left.2 fun p hp hq => hij ?_
    simp only [mem_prod, mem_singleton_iff] at hp hq
    omega

/-- **Theorem 19.3.5, second part, corrected** (MT p. 506): for the GI/G/1 queue with service
times `> 0` of mean `µ` and interarrival times `≥ 0` of mean `λ > µ` (`λ = ∞` allowed), the mean
number of customers in a busy period is finite, (19.82):
`∫ H(dy) E_{(0,y)}[τ_{[0]}] < ∞`; hence `π̃(X) < ∞` and the measure `π̃` of (10.52) is invariant
(Theorem 10.5.4). The proof replaces (19.77) and (19.84)–(19.85) by Wald's bound for the
truncated random walk `Σ (sⱼ − aⱼ)` that dominates the busy period. -/
theorem theorem_19_3_5_ii (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    [IsMarkovKernel (gig1Ladder H G)] (hH0 : H (Iic 0) = 0) (hG0 : G (Iio 0) = 0)
    (hlt : renMean H < renMean G) :
    ∫⁻ y, meanReturnTime (gig1Ladder H G) (rung 0) (0, y) ∂H ≠ ∞ ∧
      gig1Tilde H G univ ≠ ∞ ∧ IsInvariant (gig1Ladder H G) (gig1Tilde H G) := by
  set μ := (Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)
  obtain ⟨c, hc, hm⟩ := exists_wald_trunc G H hG0 hlt
  have hW := tsum_wE_le G H c hm
  have hWt : ∑' i, μ (wE c i) ≠ ∞ := ne_top_of_le_ne_top
    (ENNReal.div_ne_top ENNReal.ofReal_ne_top (tsub_pos_of_lt hm).ne') hW
  have h82 : ∫⁻ y, meanReturnTime (gig1Ladder H G) (rung 0) (0, y) ∂H ≤ ∑' i, μ (wE c i) := by
    rw [lintegral_meanReturnTime_gig1 H G hH0 hG0]
    calc ∫⁻ ω, ENat.toENNReal (firstReturn (rung 0)
          (fun k => (queueN ω.1 ω.2 k, queueR ω.1 ω.2 k))) ∂μ
        ≤ ∫⁻ ω, ∑' n, (wE c n).indicator 1 ω ∂μ :=
          lintegral_mono_ae ((ae_good_queue G H hG0 hH0).mono fun ω hω => by
            rw [coe_eq_tsum_le]
            refine ENNReal.tsum_le_tsum fun n => ?_
            by_cases h : WithTop.some (n + 1) ≤ firstReturn (rung 0)
                (fun k => (queueN ω.1 ω.2 k, queueR ω.1 ω.2 k))
            · rw [indicator_of_mem (show n ∈ {n : ℕ | WithTop.some (n + 1) ≤ firstReturn (rung 0)
                (fun k => (queueN ω.1 ω.2 k, queueR ω.1 ω.2 k))} from h),
                indicator_of_mem (mem_wE_of_le_firstReturn hc hω.2 h)]
              exact le_rfl
            · rw [indicator_of_notMem (show n ∉ {n : ℕ | WithTop.some (n + 1) ≤ firstReturn
                (rung 0) (fun k => (queueN ω.1 ω.2 k, queueR ω.1 ω.2 k))} from h)]
              exact zero_le)
      _ = ∑' n, μ (wE c n) := by
          rw [lintegral_tsum fun n =>
            (measurable_one.indicator (measurableSet_wE c n)).aemeasurable]
          exact tsum_congr fun n => lintegral_indicator_one (measurableSet_wE c n)
  have h82t : ∫⁻ y, meanReturnTime (gig1Ladder H G) (rung 0) (0, y) ∂H ≠ ∞ :=
    ne_top_of_le_ne_top hWt h82
  have htilde : gig1Tilde H G univ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (gig1Tilde_univ_le H G)
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h82t⟩
  have : IsMarkovKernel (ladderChainKernel (gig1Lambda H G) (gig1LambdaStar H G)) :=
    ‹IsMarkovKernel (gig1Ladder H G)›
  exact ⟨h82t, htilde, theorem_10_5_4_invariant H G htilde⟩

end MeynTweedie.GeneralizedDrift

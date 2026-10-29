/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PseudoAtoms.Regeneration
import PseudoAtoms.SpecificKernels
import PseudoAtoms.LadderChains

/-!
# The forward and backward recurrence time skeletons (MT §3.5.3)

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/RenewalSkeletons.lean`), with the namespace changed to
`MeynTweedie.PseudoAtoms` and the imports to `PseudoAtoms.*`. The ladder kernel `ladderKernel` is
renamed `ladderChainKernel` here, since `ladderKernel` already names the Chapter 5 counterexample
kernel in `PseudoAtoms`.

Meyn and Tweedie, §3.5.3, pp. 69–70: "no matter what the structure of the renewal sequence", the
`δ`-skeletons `V⁺_δ`, `V⁻_δ` of the forward and backward recurrence time processes are Markov
chains. The proofs regenerate the i.i.d. renewal sequence at the random index of the renewal in
progress at `nδ` (`isMarkovChain_of_regeneration`).

Hypotheses: the increment law `Γ` lives on `[0, ∞)` and is not concentrated at `0`
(`Γ(−∞, 0) = 0`, `Γ(0, ∞) > 0`), so the epochs increase to infinity almost surely, and
`δ ≥ 0`.

**Forward chain.** `fwdSkel δ n = V⁺(nδ)` for the renewal process with first epoch `x` and
increments `y` (law `μ ⊗ Γ^{⊗ℕ}`).
* `fwdSkeleton_isMarkovChain`: a Markov chain with kernel `fwdSkelKernel Γ δ`;
  `fwdSkeleton_isMarkovChain_delayed` (initial law `μ` on `(0, ∞)`) and
  `fwdSkeleton_isMarkovChain_undelayed` (no delay, initial law `Γ`).
* `fwdSkelKernel_of_lt`: `P^δ(x, {x − δ}) = 1` for `x > δ` (MT p. 69).
* `eq_3_39`: **(3.39), corrected**: `P^δ(x, A) = ∫_{[0, δ−x]} U(dt) Γ(A + [δ − x] − t)` for
  `x ≤ δ`, `A ⊆ (0, ∞)` — `eq_3_39_corrected` of `SpecificKernels`, where
  `eq_3_39_counterexample` shows the printed sign is wrong.

**Backward chain.** `bwdSkel δ n = V⁻(nδ)` for the renewal process with no delay.
* `bwdSkeleton_isMarkovChain`: a Markov chain with kernel `bwdSkelKernel Γ δ` (from age `a`,
  the item in progress has law `Γ` conditioned on `(a, ∞)`) and initial state `0`.
* `bwdSkelKernel_apply_add`: `P(V⁻(nδ) = x + δ | V⁻((n−1)δ) = x) = Γ(x + δ, ∞)/Γ(x, ∞)`.
* `bwdSkelKernel_apply_of_subset`: the second display of p. 70, corrected: for `A ⊆ [0, δ)`,
  `P(V⁻(nδ) ∈ A | x) =
    Γ(x, ∞)⁻¹ ∫_{(x, x+δ]} Γ(du) ∫ U(ds) 1{δ − (u−x) − s ∈ A} Γ(δ − (u−x) − s, ∞)`.

**Corrections.** The backward display of p. 70 divides by `[Γ(x, ∞)]⁻¹`; the correct
normalisation is division by `Γ(x, ∞)` (`bwdSkelKernel_apply_of_subset`); counterexample
`bwd_display_counterexample` (`Γ = ½δ₁ + ½δ₂`, `δ = x = 1`: the true `P(1, {0})` is `1`, the
printed normalisation gives `1/4`). The display also writes `U(dv − (u − x) − δ)`, the
reflection of the correct `U(δ − (u − x) − dv)` (not formalised separately, since the
differential notation is informal).
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- `sInf {m | P m} = k` in `ℕ`: either `k` is the least `m` with `P m`, or no `m` has `P m`
and `k = 0`. -/
theorem natSInf_eq_iff (P : ℕ → Prop) (k : ℕ) :
    sInf {m | P m} = k ↔ (P k ∧ ∀ m < k, ¬ P m) ∨ ((∀ m, ¬ P m) ∧ k = 0) := by
  by_cases h : ∃ m, P m
  · have hmem : P (sInf {m | P m}) := Nat.sInf_mem h
    have hmin : ∀ m < sInf {m | P m}, ¬ P m := fun m hm => Nat.notMem_of_lt_sInf hm
    constructor
    · rintro rfl
      exact Or.inl ⟨hmem, hmin⟩
    · rintro (⟨hk, hk'⟩ | ⟨hn, -⟩)
      · refine le_antisymm (Nat.sInf_le hk) ?_
        by_contra hlt
        exact hk' _ (not_le.1 hlt) hmem
      · obtain ⟨m, hm⟩ := h
        exact absurd hm (hn m)
  · push Not at h
    have he : {m | P m} = ∅ := by
      ext m
      simp [h m]
    rw [he, Nat.sInf_empty]
    constructor
    · rintro rfl
      exact Or.inr ⟨h, rfl⟩
    · rintro (⟨hk, -⟩ | ⟨-, rfl⟩)
      · exact absurd hk (h k)
      · rfl

/-- The first index satisfying a measurable condition is a measurable random index. -/
theorem measurableSet_natSInf_eq {Ω : Type*} [MeasurableSpace Ω] {P : Ω → ℕ → Prop}
    (hP : ∀ m, MeasurableSet {ω | P ω m}) (k : ℕ) :
    MeasurableSet {ω | sInf {m | P ω m} = k} := by
  have h : {ω | sInf {m | P ω m} = k} =
      ({ω | P ω k} ∩ ⋂ m, ⋂ (_ : m < k), {ω | P ω m}ᶜ) ∪
        ((⋂ m, {ω | P ω m}ᶜ) ∩ {_ω | k = 0}) := by
    ext ω
    simp only [mem_ofPred_eq, natSInf_eq_iff, mem_union, mem_inter_iff, mem_iInter, mem_compl_iff]
  rw [h]
  exact ((hP k).inter (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    (hP m).compl)).union ((MeasurableSet.iInter fun m => (hP m).compl).inter
      (MeasurableSet.const _))

/-- The forward recurrence time `V⁺(t)` is measurable in the renewal epochs. -/
theorem measurable_fwdTimeCts {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℕ → ℝ}
    (hZ : ∀ k, Measurable fun ω => Z ω k) (t : ℝ) : Measurable fun ω => fwdTimeCts (Z ω) t := by
  refine measurable_of_Iio fun c => ?_
  have h : (fun ω => fwdTimeCts (Z ω) t) ⁻¹' Iio c =
      (⋃ k, {ω | 1 ≤ k ∧ t < Z ω k ∧ Z ω k - t < c}) ∪
        ((⋂ k, {ω | 1 ≤ k → Z ω k ≤ t}) ∩ {_ω | 0 < c}) := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_union, mem_iUnion, mem_ofPred_eq, mem_inter_iff,
      mem_iInter]
    set S := {d | ∃ n, 1 ≤ n ∧ t < Z ω n ∧ d = Z ω n - t}
    have hbdd : BddBelow S := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
    change sInf S < c ↔ _
    by_cases hne : S.Nonempty
    · rw [csInf_lt_iff hbdd hne]
      constructor
      · rintro ⟨d, ⟨n, hn, htn, rfl⟩, hd⟩
        exact Or.inl ⟨n, hn, htn, hd⟩
      · rintro (⟨n, hn, htn, hd⟩ | ⟨hall, -⟩)
        · exact ⟨_, ⟨n, hn, htn, rfl⟩, hd⟩
        · obtain ⟨d, n, hn, htn, rfl⟩ := hne
          exact absurd (hall n hn) (not_le.2 htn)
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, Real.sInf_empty]
      constructor
      · intro hc
        refine Or.inr ⟨fun n hn => ?_, hc⟩
        by_contra hlt
        have : Z ω n - t ∈ S := ⟨n, hn, not_le.1 hlt, rfl⟩
        rw [hne] at this
        exact this
      · rintro (⟨n, hn, htn, hd⟩ | ⟨-, hc⟩)
        · have : Z ω n - t ∈ S := ⟨n, hn, htn, rfl⟩
          rw [hne] at this
          exact absurd this (notMem_empty _)
        · exact hc
  rw [h]
  refine (MeasurableSet.iUnion fun k => ?_).union ((MeasurableSet.iInter fun k => ?_).inter
    (MeasurableSet.const _))
  · exact (MeasurableSet.const _).inter ((measurableSet_lt measurable_const (hZ k)).inter
      (measurableSet_lt ((hZ k).sub measurable_const) measurable_const))
  · by_cases hk : 1 ≤ k
    · simp only [hk, true_implies]
      exact measurableSet_le (hZ k) measurable_const
    · simp only [hk, false_implies, ofPred_true, MeasurableSet.univ]

/-- `Z_{m+1} = x + S₁ + ⋯ + Sₘ`. -/
theorem resEpoch_succ_eq (x : ℝ) (w : ℕ → ℝ) (m : ℕ) :
    resEpoch x w (m + 1) = x + ∑ i ∈ Finset.range m, w i := rfl

/-- The first `k + 1` epochs only use the first `k` increments. -/
theorem resEpoch_truncSeq_of_le {x : ℝ} {w : ℕ → ℝ} {k m : ℕ} (hm : m ≤ k + 1) :
    resEpoch x (truncSeq k w) m = resEpoch x w m := by
  cases m with
  | zero => rfl
  | succ m =>
    simp only [resEpoch_succ_eq]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i < k := by simp at hi; omega
    simp [truncSeq, this]

/-- With the increments truncated at `k`, the epochs stop at `Z_{k+1}`. -/
theorem resEpoch_truncSeq_of_ge {x : ℝ} {w : ℕ → ℝ} {k m : ℕ} (hm : k + 1 ≤ m) :
    resEpoch x (truncSeq k w) m = resEpoch x w (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [resEpoch_succ_eq]
  congr 1
  rw [← Finset.sum_range_add_sum_Ico _ (show k ≤ m by omega)]
  have h0 : ∑ i ∈ Finset.Ico k m, truncSeq k w i = 0 :=
    Finset.sum_eq_zero fun i hi => by simp [truncSeq, (Finset.mem_Ico.1 hi).1]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [truncSeq, Finset.mem_range.1 hi]

/-- If the epoch `Z_{k+1}` lies beyond `t`, then `V⁺(t)` only depends on the first `k`
increments. -/
theorem fwdTimeCts_truncSeq {x t : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {k : ℕ}
    (ht : t < resEpoch x w (k + 1)) :
    fwdTimeCts (resEpoch x (truncSeq k w)) t = fwdTimeCts (resEpoch x w) t := by
  set S1 := {d | ∃ n, 1 ≤ n ∧ t < resEpoch x w n ∧ d = resEpoch x w n - t}
  set S2 := {d | ∃ n, 1 ≤ n ∧ t < resEpoch x (truncSeq k w) n ∧
    d = resEpoch x (truncSeq k w) n - t}
  have hb1 : BddBelow S1 := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  have hb2 : BddBelow S2 := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  have hm1 : resEpoch x w (k + 1) - t ∈ S1 := ⟨k + 1, by omega, ht, rfl⟩
  have hm2 : resEpoch x w (k + 1) - t ∈ S2 :=
    ⟨k + 1, by omega, by rwa [resEpoch_truncSeq_of_le le_rfl],
      by rw [resEpoch_truncSeq_of_le le_rfl]⟩
  change sInf S2 = sInf S1
  refine le_antisymm (le_csInf ⟨_, hm1⟩ ?_) (le_csInf ⟨_, hm2⟩ ?_)
  · rintro d ⟨n, hn, htn, rfl⟩
    by_cases hnk : n ≤ k + 1
    · exact csInf_le hb2 ⟨n, hn, by rwa [resEpoch_truncSeq_of_le hnk],
        by rw [resEpoch_truncSeq_of_le hnk]⟩
    · have := resEpoch_mono (x := x) hw (show 1 ≤ k + 1 by omega) (show k + 1 ≤ n by omega)
      exact (csInf_le hb2 hm2).trans (by linarith)
  · rintro d ⟨n, hn, htn, rfl⟩
    by_cases hnk : n ≤ k + 1
    · rw [resEpoch_truncSeq_of_le hnk] at htn ⊢
      exact csInf_le hb1 ⟨n, hn, htn, rfl⟩
    · rw [resEpoch_truncSeq_of_ge (by omega)]
      exact csInf_le hb1 hm1

/-- One step of the forward `δ`-skeleton: the forward recurrence time at `δ` for epochs
`x, x + y₀, x + y₀ + y₁, …`. -/
noncomputable def fwdSkelStep (δ : ℝ) (q : ℝ × (ℕ → ℝ)) : ℝ := fwdTimeCts (resEpoch q.1 q.2) δ

/-- The forward skeleton step is measurable. -/
theorem measurable_fwdSkelStep (δ : ℝ) : Measurable (fwdSkelStep δ) :=
  measurable_fwdTimeCts (Z := fun q : ℝ × (ℕ → ℝ) => resEpoch q.1 q.2)
    (fun k => measurable_resEpoch k) δ

/-- The transition kernel `P^δ` of the forward recurrence time `δ`-skeleton:
`P^δ(x, A) = Γ^{⊗ℕ}{y : V⁺_δ starting from x, driven by y, lies in A}`. -/
noncomputable def fwdSkelKernel (Γ : Measure ℝ) (δ : ℝ) : Kernel ℝ ℝ :=
  recursionKernel (Measure.infinitePi fun _ : ℕ => Γ) (fwdSkelStep δ)

/-- The forward recurrence time `δ`-skeleton `V⁺_δ(n) = V⁺(nδ)` of the renewal process with
first epoch `x` and increments `y` (MT (RT3), p. 69), on the canonical space. -/
noncomputable def fwdSkel (δ : ℝ) (n : ℕ) (p : ℝ × (ℕ → ℝ)) : ℝ :=
  fwdTimeCts (resEpoch p.1 p.2) (n * δ)

/-- Each `V⁺_δ(n)` is measurable. -/
theorem measurable_fwdSkel (δ : ℝ) (n : ℕ) : Measurable (fwdSkel δ n) :=
  measurable_fwdTimeCts (Z := fun q : ℝ × (ℕ → ℝ) => resEpoch q.1 q.2)
    (fun k => measurable_resEpoch k) _

/-- The number of increments used up to the first epoch after `nδ`. -/
noncomputable def fwdIndex (δ : ℝ) (n : ℕ) (p : ℝ × (ℕ → ℝ)) : ℕ :=
  sInf {m | (n : ℝ) * δ < resEpoch p.1 p.2 (m + 1)}

/-- The index `fwdIndex` is a measurable random index. -/
theorem measurableSet_fwdIndex_eq (δ : ℝ) (n k : ℕ) :
    MeasurableSet {p : ℝ × (ℕ → ℝ) | fwdIndex δ n p = k} :=
  measurableSet_natSInf_eq
    (P := fun (p : ℝ × (ℕ → ℝ)) m => (n : ℝ) * δ < resEpoch p.1 p.2 (m + 1))
    (fun m => measurableSet_lt measurable_const (measurable_resEpoch (m + 1))) k

/-- If the partial sums diverge, some epoch exceeds any level. -/
theorem exists_resEpoch_gt {x : ℝ} {w : ℕ → ℝ}
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) (c : ℝ) :
    ∃ m, c < resEpoch x w (m + 1) := by
  obtain ⟨m, hm⟩ := (hdiv.eventually_gt_atTop (c - x)).exists
  exact ⟨m, by rw [resEpoch_succ_eq]; linarith⟩

/-- With nonnegative increments and divergent epochs, `V⁺(t)` is the first epoch after `t`
minus `t`. -/
theorem fwdTimeCts_eq_resEpoch {x t : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) :
    fwdTimeCts (resEpoch x w) t =
      resEpoch x w (sInf {m | t < resEpoch x w (m + 1)} + 1) - t := by
  have hex := exists_resEpoch_gt (x := x) hdiv t
  set τ := sInf {m | t < resEpoch x w (m + 1)}
  have hτ : t < resEpoch x w (τ + 1) := Nat.sInf_mem hex
  refine IsLeast.csInf_eq ⟨⟨τ + 1, by omega, hτ, rfl⟩, ?_⟩
  rintro d ⟨m, hm, htm, rfl⟩
  have hle : τ ≤ m - 1 := Nat.sInf_le (show t < resEpoch x w (m - 1 + 1) by
    rwa [show m - 1 + 1 = m by omega])
  have := resEpoch_mono (x := x) hw (show 1 ≤ τ + 1 by omega) (show τ + 1 ≤ m by omega)
  linarith

/-- **Regeneration of the forward chain.** `V⁺_δ(n + 1)` is the skeleton step from `V⁺_δ(n)`
driven by the increments after the first epoch beyond `nδ`. -/
theorem fwdSkel_succ {δ : ℝ} (hδ : 0 ≤ δ) {p : ℝ × (ℕ → ℝ)} (hw : ∀ i, 0 ≤ p.2 i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, p.2 i) atTop atTop) (n : ℕ) :
    fwdSkel δ (n + 1) p = fwdSkelStep δ (fwdSkel δ n p, tailSeq (fwdIndex δ n p) p.2) := by
  obtain ⟨x, w⟩ := p
  simp only at hw hdiv
  set τ := fwdIndex δ n (x, w) with hτdef
  have hex := exists_resEpoch_gt (x := x) hdiv ((n : ℝ) * δ)
  have hτ : (n : ℝ) * δ < resEpoch x w (τ + 1) := Nat.sInf_mem hex
  have hmin : ∀ m < τ, resEpoch x w (m + 1) ≤ (n : ℝ) * δ := fun m hm =>
    not_lt.1 (Nat.notMem_of_lt_sInf hm)
  have hW : fwdSkel δ n (x, w) = resEpoch x w (τ + 1) - n * δ :=
    fwdTimeCts_eq_resEpoch hw hdiv
  set W := fwdSkel δ n (x, w) with hWdef
  have htail : ∀ j, resEpoch W (tailSeq τ w) (j + 1) =
      resEpoch x w (τ + 1 + j) - n * δ := fun j => by
    rw [hW, resEpoch_succ_eq, show τ + 1 + j = τ + j + 1 by omega, resEpoch_succ_eq,
      resEpoch_succ_eq, Finset.sum_range_add]
    simp only [tailSeq]
    ring
  rw [show fwdSkel δ (n + 1) (x, w) = fwdTimeCts (resEpoch x w) (((n + 1 : ℕ) : ℝ) * δ)
    from rfl, show fwdSkelStep δ (W, tailSeq τ w) = fwdTimeCts (resEpoch W (tailSeq τ w)) δ
    from rfl]
  unfold fwdTimeCts
  congr 1
  ext d
  simp only [mem_ofPred_eq]
  push_cast
  constructor
  · rintro ⟨m, hm, htm, rfl⟩
    have hmτ : τ + 1 ≤ m := by
      by_contra hlt
      have := hmin (m - 1) (by omega)
      rw [show m - 1 + 1 = m by omega] at this
      nlinarith
    refine ⟨m - τ, by omega, ?_, ?_⟩
    · rw [show m - τ = (m - τ - 1) + 1 by omega, htail,
        show τ + 1 + (m - τ - 1) = m by omega]
      linarith
    · rw [show m - τ = (m - τ - 1) + 1 by omega, htail,
        show τ + 1 + (m - τ - 1) = m by omega]
      ring
  · rintro ⟨j, hj, htj, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [htail] at htj ⊢
    refine ⟨τ + 1 + j, by omega, by linarith, by ring⟩

/-- On `X₀ × ℝ^ℕ` with law `μ ⊗ Γ^{⊗ℕ}`, the pair (initial state, first `k` increments) is
independent of the increments from `k` on, which are again `Γ^{⊗ℕ}`. -/
theorem prod_map_trunc_tail {X₀ : Type*} [MeasurableSpace X₀] (μ : Measure X₀) [SFinite μ]
    (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (k : ℕ) :
    (μ.prod (Measure.infinitePi fun _ : ℕ => Γ)).map
        (fun p => ((p.1, truncSeq k p.2), tailSeq k p.2)) =
      ((μ.prod (Measure.infinitePi fun _ : ℕ => Γ)).map (fun p => (p.1, truncSeq k p.2))).prod
        (Measure.infinitePi fun _ : ℕ => Γ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hAB : Measurable fun w : ℕ → ℝ => (truncSeq k w, tailSeq k w) :=
    (measurable_truncSeq k).prodMk (measurable_tailSeq k)
  have h1 : (μ.prod ν).map (Prod.map id fun w : ℕ → ℝ => (truncSeq k w, tailSeq k w)) =
      μ.prod ((ν.map (truncSeq k)).prod ν) := by
    rw [← Measure.map_prod_map _ _ measurable_id hAB, Measure.map_id, infinitePi_map_trunc_tail]
  have hmp := (measurePreserving_prodAssoc μ (ν.map (truncSeq k)) ν).symm
  have h2 : (fun p : X₀ × (ℕ → ℝ) => ((p.1, truncSeq k p.2), tailSeq k p.2)) =
      (MeasurableEquiv.prodAssoc (α := X₀) (β := ℕ → ℝ) (γ := ℕ → ℝ)).symm ∘
        (Prod.map id fun w : ℕ → ℝ => (truncSeq k w, tailSeq k w)) := by
    funext p
    rfl
  have h3 : (μ.prod ν).map (fun p => (p.1, truncSeq k p.2)) = μ.prod (ν.map (truncSeq k)) := by
    conv_rhs => rw [← Measure.map_id (μ := μ)]
    rw [Measure.map_prod_map _ _ measurable_id (measurable_truncSeq k)]
    rfl
  rw [h2, ← Measure.map_map hmp.measurable (measurable_id.prodMap hAB), h1, hmp.map_eq, h3]

/-- Almost surely the increments are nonnegative and their partial sums diverge. -/
theorem ae_good_prod {X₀ : Type*} [MeasurableSpace X₀] (μ : Measure X₀) [IsProbabilityMeasure μ]
    (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) :
    ∀ᵐ p ∂(μ.prod (Measure.infinitePi fun _ : ℕ => Γ)),
      Tendsto (fun n => ∑ i ∈ Finset.range n, p.2 i) atTop atTop ∧ ∀ i, 0 ≤ p.2 i :=
  (measurePreserving_snd (μ := μ)
    (ν := Measure.infinitePi fun _ : ℕ => Γ)).quasiMeasurePreserving.ae
    (tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos)

/-- **The forward recurrence time `δ`-skeleton is a Markov chain** (MT p. 69), for any
increment law `Γ` on `[0, ∞)` that is not concentrated at `0`, and any delay. Its kernel is
`fwdSkelKernel` (see `eq_3_39` and `fwdSkelKernel_of_lt`). -/
theorem fwdSkeleton_isMarkovChain (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 ≤ δ) :
    IsMarkovChain (fwdSkelKernel Γ δ)
      ((μ.prod (Measure.infinitePi fun _ : ℕ => Γ)).map (fwdSkel δ 0))
      (μ.prod (Measure.infinitePi fun _ : ℕ => Γ)) (fwdSkel δ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hgood := ae_good_prod μ Γ hΓ0 hΓpos
  refine isMarkovChain_of_regeneration (μ.prod ν) ν _ (fwdSkel δ) (measurable_fwdSkel δ) rfl
    (fwdIndex δ) (measurableSet_fwdIndex_eq δ) (fun _ k p => (p.1, truncSeq k p.2))
    (fun _ k => measurable_fst.prodMk ((measurable_truncSeq k).comp measurable_snd))
    (fun _ k p => tailSeq k p.2) (fun _ k => (measurable_tailSeq k).comp measurable_snd)
    (fun _ k => prod_map_trunc_tail μ Γ k) (S := univ) MeasurableSet.univ
    (fun n k => ?_) (measurable_fwdSkelStep δ) (fun n => ?_) _ (fun x => ?_)
  · refine ⟨{b | (n : ℝ) * δ < resEpoch b.1 b.2 (k + 1) ∧
        ∀ m < k, resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ}, ?_,
      fun b j => fwdTimeCts (resEpoch b.1 b.2) ((j : ℕ) * δ), ?_, ?_⟩
    · have hset : {b : ℝ × (ℕ → ℝ) | ∀ m < k, resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ} =
          ⋂ m, ⋂ (_ : m < k), {b | resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ} := by
        ext b
        simp
      have hT2 : MeasurableSet
          {b : ℝ × (ℕ → ℝ) | ∀ m < k, resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ} := by
        rw [hset]
        exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
          measurableSet_le (measurable_resEpoch (m + 1)) measurable_const
      exact (measurableSet_lt measurable_const (measurable_resEpoch (k + 1))).inter hT2
    · exact measurable_pi_iff.2 fun j => measurable_fwdTimeCts
        (Z := fun q : ℝ × (ℕ → ℝ) => resEpoch q.1 q.2) (fun k => measurable_resEpoch k) _
    · filter_upwards [hgood] with p ⟨hdiv, hw⟩
      obtain ⟨x, w⟩ := p
      simp only at hdiv hw
      have hex := exists_resEpoch_gt (x := x) hdiv ((n : ℝ) * δ)
      have hiff : fwdIndex δ n (x, w) = k ↔ ((n : ℝ) * δ < resEpoch x w (k + 1) ∧
          ∀ m < k, resEpoch x w (m + 1) ≤ (n : ℝ) * δ) := by
        unfold fwdIndex
        rw [natSInf_eq_iff]
        simp only [not_lt]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact h
          · obtain ⟨m, hm⟩ := hex
            exact absurd hm (not_lt.2 (h m))
        · exact Or.inl
      refine ⟨?_, fun hk j => ?_⟩
      · rw [hiff]
        simp only [mem_univ, and_true]
        rw [resEpoch_truncSeq_of_le le_rfl]
        refine and_congr_right fun _ => forall₂_congr fun m hm => ?_
        rw [resEpoch_truncSeq_of_le (by omega)]
      · have hk' := (hiff.1 hk).1
        have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.2
        have hjn : ((j : ℕ) : ℝ) * δ ≤ (n : ℝ) * δ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ
        exact (fwdTimeCts_truncSeq hw (lt_of_le_of_lt hjn hk')).symm
  · filter_upwards [hgood] with p ⟨hdiv, hw⟩
    exact fwdSkel_succ hδ hw hdiv n
  · simp only [mem_univ, ofPred_true, cond_univ]
    exact recursionKernel_apply ν (measurable_fwdSkelStep δ) x

/-- Under `Γ^{⊗ℕ}`, the partial sum `S_j = y₀ + ⋯ + y_{j−1}` and the next increment `y_j` are
independent with laws `Γ^{j∗}` and `Γ`. -/
theorem infinitePi_map_partialSum_next (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (j : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun w => (∑ i ∈ Finset.range j, w i, w j)) =
      (convPow Γ j).prod Γ := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hg : Measurable fun u : Fin (j + 1) → ℝ => (Fin.init u, u (Fin.last j)) :=
    (measurable_pi_iff.2 fun i => measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hf : Measurable fun w : ℕ → ℝ => fun i : Fin (j + 1) => w i :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hν : ν.map (fun w : ℕ → ℝ => ((fun i : Fin j => w i), w j)) =
      (Measure.pi fun _ : Fin j => Γ).prod Γ := by
    have hc : (fun w : ℕ → ℝ => ((fun i : Fin j => w i), w j)) =
        (fun u : Fin (j + 1) → ℝ => (Fin.init u, u (Fin.last j))) ∘
          (fun w : ℕ → ℝ => fun i : Fin (j + 1) => w i) := by
      funext w
      rfl
    rw [hc, ← Measure.map_map hg hf, infinitePi_map_fin, pi_map_init_last]
  have hs : Measurable fun u : Fin j → ℝ => ∑ i, u i := measurable_sum_fin (G := ℝ) j
  have hc2 : (fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j)) =
      Prod.map (fun u : Fin j → ℝ => ∑ i, u i) id ∘
        (fun w : ℕ → ℝ => ((fun i : Fin j => w i), w j)) := by
    funext w
    simp [Fin.sum_univ_eq_sum_range (fun i => w i)]
  rw [hc2, ← Measure.map_map (hs.prodMap measurable_id)
    ((measurable_pi_iff.2 fun i => measurable_pi_apply _).prodMk (measurable_pi_apply j)), hν,
    ← Measure.map_prod_map _ _ hs measurable_id, Measure.map_id]
  rfl

/-- MT p. 69: for `x > δ`, `P^δ(x, ·) = δ_{x−δ}`. -/
theorem fwdSkelKernel_of_lt (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : δ < x) :
    fwdSkelKernel Γ δ x = Measure.dirac (x - δ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  rw [fwdSkelKernel, recursionKernel_apply ν (measurable_fwdSkelStep δ) x]
  have hae : (fun w => fwdSkelStep δ (x, w)) =ᵐ[ν] fun _ => x - δ := by
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨hdiv, hw⟩
    have h0 : fwdTimeCts (resEpoch x w) 0 = x := by
      rw [fwdTimeCts_eq_resEpoch hw hdiv]
      have : sInf {m | (0 : ℝ) < resEpoch x w (m + 1)} = 0 :=
        le_antisymm (Nat.sInf_le (show (0 : ℝ) < resEpoch x w (0 + 1) by
          simp only [resEpoch_succ_eq, Finset.range_zero, Finset.sum_empty, add_zero]
          linarith)) (Nat.zero_le _)
      rw [this]
      simp [resEpoch_succ_eq]
    have := fwdTimeCts_add_of_lt (resEpoch x w) hδ (h0 ▸ hx)
    rw [zero_add, h0] at this
    exact this
  rw [Measure.map_congr hae, Measure.map_const, measure_univ, one_smul]

/-- Decomposing `{V⁺(δ) ∈ A}` over the index `j` of the last epoch before `δ`. -/
theorem indicator_fwdTimeCts_eq_tsum {x δ : ℝ} (hxδ : x ≤ δ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) {A : Set ℝ}
    (hA0 : A ⊆ Ioi 0) :
    A.indicator (1 : ℝ → ℝ≥0∞) (fwdTimeCts (resEpoch x w) δ) =
      ∑' j, {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j) := by
  have hex := exists_resEpoch_gt (x := x) hdiv δ
  set τ := sInf {m | δ < resEpoch x w (m + 1)} with hτdef
  have hτ : δ < resEpoch x w (τ + 1) := Nat.sInf_mem hex
  have hmin : ∀ m < τ, resEpoch x w (m + 1) ≤ δ := fun m hm =>
    not_lt.1 (Nat.notMem_of_lt_sInf hm)
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, resEpoch_succ_eq] at hτ
    simp at hτ
    linarith
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, τ = j₀ + 1 := ⟨τ - 1, by omega⟩
  rw [fwdTimeCts_eq_resEpoch hw hdiv, ← hτdef, tsum_eq_single j₀ fun j hj => ?_]
  · have e : resEpoch x w (τ + 1) - δ = x + ∑ i ∈ Finset.range j₀, w i + w j₀ - δ := by
      rw [hj₀, resEpoch_succ_eq, Finset.sum_range_succ]
      ring
    have h1 : x + ∑ i ∈ Finset.range j₀, w i ≤ δ := by
      have := hmin j₀ (by omega)
      rwa [resEpoch_succ_eq] at this
    rw [e]
    by_cases hA : x + ∑ i ∈ Finset.range j₀, w i + w j₀ - δ ∈ A
    · rw [indicator_of_mem hA, indicator_of_mem (show (∑ i ∈ Finset.range j₀, w i, w j₀) ∈
        {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A} from ⟨h1, hA⟩)]
      rfl
    · rw [indicator_of_notMem hA, indicator_of_notMem (show (∑ i ∈ Finset.range j₀, w i, w j₀) ∉
        {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A} from fun h => hA h.2)]
  · refine indicator_of_notMem ?_ _
    rintro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · have h3 := hmin (j + 1) (by omega)
      rw [resEpoch_succ_eq, Finset.sum_range_succ] at h3
      have := hA0 h2
      simp only [mem_Ioi] at this
      linarith
    · have h3 := resEpoch_mono (x := x) hw (show 1 ≤ τ + 1 by omega)
        (show τ + 1 ≤ j + 1 by omega)
      simp only [resEpoch_succ_eq] at h3 hτ
      simp only at h1
      linarith

/-- `Γ^{j∗}` is concentrated on `[0, ∞)` when `Γ` is. -/
theorem convPow_Iio_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (j : ℕ) : convPow Γ j (Iio 0) = 0 := by
  have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hm : convPow Γ j = (Measure.infinitePi fun _ : ℕ => Γ).map
      (fun w : ℕ → ℝ => ∑ i ∈ Finset.range j, w i) := by
    have := congrArg (Measure.map Prod.fst) (infinitePi_map_partialSum_next Γ j)
    rw [Measure.map_map measurable_fst hpair, Measure.map_fst_prod, measure_univ,
      one_smul] at this
    exact this.symm
  rw [hm, Measure.map_apply (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
    measurableSet_Iio]
  refine measure_mono_null (t := ⋃ i, {w : ℕ → ℝ | w i < 0}) (fun w hw => ?_) ?_
  · by_contra hc
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hc
    simp only [mem_preimage, mem_Iio] at hw
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.range j) => hc i
    linarith
  · refine measure_iUnion_null fun i => ?_
    have : {w : ℕ → ℝ | w i < 0} = (fun w : ℕ → ℝ => w i) ⁻¹' Iio 0 := rfl
    rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio,
      Measure.infinitePi_map_eval, hΓ0]

/-- One term of (3.39): the contribution of the `j`-th renewal. -/
theorem lintegral_partialSum_pair (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) {δ x : ℝ} {A : Set ℝ} (hA : MeasurableSet A) (j : ℕ) :
    ∫⁻ w, {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j) ∂(Measure.infinitePi fun _ : ℕ => Γ) =
      ∫⁻ s in Icc 0 (δ - x), Γ ((fun a => a + (δ - x) - s) '' A) ∂(convPow Γ j) := by
  set E : Set (ℝ × ℝ) := {q | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A} with hEdef
  have hE : MeasurableSet E :=
    (measurableSet_le (measurable_const.add measurable_fst) measurable_const).inter
      ((((measurable_const.add measurable_fst).add measurable_snd).sub measurable_const) hA)
  have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hcp := isProbabilityMeasure_convPow Γ j
  have h1 : ∫⁻ w, E.indicator (1 : ℝ × ℝ → ℝ≥0∞) (∑ i ∈ Finset.range j, w i, w j)
      ∂(Measure.infinitePi fun _ : ℕ => Γ) = ((convPow Γ j).prod Γ) E := by
    rw [← infinitePi_map_partialSum_next Γ j, Measure.map_apply hpair hE,
      ← lintegral_indicator_one (hpair hE)]
    rfl
  rw [h1, Measure.prod_apply hE, ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr_ae ?_
  have hnn : ∀ᵐ s ∂(convPow Γ j), 0 ≤ s := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by
      ext a
      simp
    rw [this, convPow_Iio_zero Γ hΓ0 j]
  filter_upwards [hnn] with s hs
  by_cases hsx : x + s ≤ δ
  · rw [indicator_of_mem (show s ∈ Icc 0 (δ - x) from ⟨hs, by linarith⟩)]
    congr 1
    ext y
    simp only [mem_preimage, mem_ofPred_eq, hEdef, mem_image]
    constructor
    · rintro ⟨-, hy⟩
      exact ⟨x + s + y - δ, hy, by ring⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hsx, ?_⟩
      have : x + s + (a + (δ - x) - s) - δ = a := by ring
      rw [this]
      exact ha
  · rw [indicator_of_notMem (show s ∉ Icc 0 (δ - x) from fun h => hsx (by linarith [h.2]))]
    convert measure_empty (μ := Γ)
    ext y
    simp only [mem_preimage, mem_ofPred_eq, hEdef, mem_empty_iff_false, iff_false]
    exact fun h => hsx h.1

/-- **(3.39), corrected** (MT p. 70). For `x ≤ δ` and `A ⊆ (0, ∞)`,
`P^δ(x, A) = ∫_{[0, δ−x]} U(dt) Γ(A + [δ − x] − t)` (`eq_3_39_corrected`). -/
theorem eq_3_39 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) {δ x : ℝ} (hxδ : x ≤ δ) {A : Set ℝ} (hA : MeasurableSet A)
    (hA0 : A ⊆ Ioi 0) : fwdSkelKernel Γ δ x A = eq_3_39_corrected Γ δ x A := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hE : MeasurableSet {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A} :=
    (measurableSet_le (measurable_const.add measurable_fst) measurable_const).inter
      ((((measurable_const.add measurable_fst).add measurable_snd).sub measurable_const) hA)
  have hpair : ∀ j, Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) := fun j =>
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  rw [fwdSkelKernel, recursionKernel_apply' ν (measurable_fwdSkelStep δ) x hA,
    ← lintegral_indicator_one (s := {w | fwdSkelStep δ (x, w) ∈ A})
      (((measurable_fwdSkelStep δ).comp measurable_prodMk_left) hA)]
  have hae : ∀ᵐ w ∂ν, {w | fwdSkelStep δ (x, w) ∈ A}.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) w =
      ∑' j, {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j) := by
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨hdiv, hw⟩
    rw [← indicator_fwdTimeCts_eq_tsum hxδ hw hdiv hA0]
    by_cases h : fwdSkelStep δ (x, w) ∈ A
    · rw [indicator_of_mem (show w ∈ {w | fwdSkelStep δ (x, w) ∈ A} from h),
        indicator_of_mem (show fwdTimeCts (resEpoch x w) δ ∈ A from h)]
      rfl
    · rw [indicator_of_notMem (show w ∉ {w | fwdSkelStep δ (x, w) ∈ A} from h),
        indicator_of_notMem (show fwdTimeCts (resEpoch x w) δ ∉ A from h)]
  have hmj : ∀ j, AEMeasurable (fun w : ℕ → ℝ =>
      {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j)) ν := fun j =>
    (Measurable.indicator measurable_one hE |>.comp (hpair j)).aemeasurable
  rw [lintegral_congr_ae hae, lintegral_tsum hmj]
  refine (tsum_congr fun j => lintegral_partialSum_pair Γ hΓ0 hA j).trans ?_
  rw [eq_3_39_corrected, renewalMeasure, ← lintegral_indicator measurableSet_Icc,
    lintegral_sum_measure]
  refine tsum_congr fun j => ?_
  rw [lintegral_indicator measurableSet_Icc]

/-- With a positive first epoch `x`, `V⁺(0) = x`. -/
theorem fwdTimeCts_zero_of_pos {x : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) (hx : 0 < x) :
    fwdTimeCts (resEpoch x w) 0 = x := by
  rw [fwdTimeCts_eq_resEpoch hw hdiv]
  have : sInf {m | (0 : ℝ) < resEpoch x w (m + 1)} = 0 :=
    le_antisymm (Nat.sInf_le (show (0 : ℝ) < resEpoch x w (0 + 1) by
      simp only [resEpoch_succ_eq, Finset.range_zero, Finset.sum_empty, add_zero]
      exact hx)) (Nat.zero_le _)
  rw [this]
  simp [resEpoch_succ_eq]

/-- The forward skeleton of the delayed renewal process with delay law `μ` on `(0, ∞)` is a
Markov chain with kernel `P^δ` and initial law `μ`. -/
theorem fwdSkeleton_isMarkovChain_delayed (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iic 0) = 0) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsMarkovChain (fwdSkelKernel Γ δ) μ (μ.prod (Measure.infinitePi fun _ : ℕ => Γ))
      (fwdSkel δ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have h := fwdSkeleton_isMarkovChain Γ hΓ0 hΓpos μ hδ
  have hx : ∀ᵐ p ∂(μ.prod ν), 0 < p.1 :=
    (measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae (by
      rw [ae_iff]
      have : {a : ℝ | ¬ 0 < a} = Iic 0 := by
        ext a
        simp
      rw [this, hμ])
  have hae : fwdSkel δ 0 =ᵐ[μ.prod ν] Prod.fst := by
    filter_upwards [hx, ae_good_prod μ Γ hΓ0 hΓpos] with p hp ⟨hdiv, hw⟩
    change fwdTimeCts (resEpoch p.1 p.2) (((0 : ℕ) : ℝ) * δ) = p.1
    rw [Nat.cast_zero, zero_mul]
    exact fwdTimeCts_zero_of_pos hw hdiv hp
  rwa [Measure.map_congr hae, Measure.map_fst_prod, measure_univ, one_smul] at h

/-- The forward skeleton of the renewal process with no delay (a renewal at time `0`) is a
Markov chain with kernel `P^δ` and initial law `Γ` (for `Γ` concentrated on `(0, ∞)`). -/
theorem fwdSkeleton_isMarkovChain_undelayed (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iic 0) = 0) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsMarkovChain (fwdSkelKernel Γ δ) Γ
      ((Measure.dirac (0 : ℝ)).prod (Measure.infinitePi fun _ : ℕ => Γ)) (fwdSkel δ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hΓ0' : Γ (Iio 0) = 0 := measure_mono_null Iio_subset_Iic_self hΓ0
  have hΓpos : 0 < Γ (Ioi 0) := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hΓ0, tsub_zero]
    exact one_pos
  have h := fwdSkeleton_isMarkovChain Γ hΓ0' hΓpos (Measure.dirac 0) hδ
  have hpos : ∀ᵐ p ∂((Measure.dirac (0 : ℝ)).prod ν), 0 < p.2 0 ∧ p.1 = 0 := by
    have h1' : ∀ᵐ w ∂ν, 0 < w 0 := by
      rw [ae_iff]
      have : {w : ℕ → ℝ | ¬ 0 < w 0} = (fun w : ℕ → ℝ => w 0) ⁻¹' Iic 0 := by
        ext w
        simp
      rw [this, ← Measure.map_apply (measurable_pi_apply 0) measurableSet_Iic,
        Measure.infinitePi_map_eval, hΓ0]
    have h1 : ∀ᵐ p ∂((Measure.dirac (0 : ℝ)).prod ν), 0 < p.2 0 :=
      (measurePreserving_snd (μ := Measure.dirac (0 : ℝ)) (ν := ν)).quasiMeasurePreserving.ae h1'
    have h2 : ∀ᵐ p ∂((Measure.dirac (0 : ℝ)).prod ν), p.1 = 0 :=
      (measurePreserving_fst (μ := Measure.dirac (0 : ℝ)) (ν := ν)).quasiMeasurePreserving.ae
        ((ae_dirac_iff (measurableSet_singleton (0 : ℝ))).2 rfl)
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1, hp2⟩
  have hae : fwdSkel δ 0 =ᵐ[(Measure.dirac (0 : ℝ)).prod ν] fun p => p.2 0 := by
    filter_upwards [hpos, ae_good_prod (Measure.dirac (0 : ℝ)) Γ hΓ0' hΓpos]
      with p ⟨hp, hp1⟩ ⟨hdiv, hw⟩
    obtain ⟨x, w⟩ := p
    simp only at hp hp1 hdiv hw
    subst hp1
    change fwdTimeCts (resEpoch 0 w) (((0 : ℕ) : ℝ) * δ) = w 0
    rw [Nat.cast_zero, zero_mul, fwdTimeCts_eq_resEpoch hw hdiv]
    have : sInf {m | (0 : ℝ) < resEpoch 0 w (m + 1)} = 1 := by
      rw [natSInf_eq_iff]
      left
      refine ⟨?_, fun m hm => ?_⟩
      · simp [resEpoch_succ_eq, hp]
      · obtain rfl : m = 0 := by omega
        simp [resEpoch_succ_eq]
    rw [this]
    simp [resEpoch_succ_eq]
  have hm : ((Measure.dirac (0 : ℝ)).prod ν).map (fun p => p.2 0) = Γ := by
    rw [show (fun p : ℝ × (ℕ → ℝ) => p.2 0) = (fun w : ℕ → ℝ => w 0) ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_pi_apply 0) measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul, Measure.infinitePi_map_eval]
  rwa [Measure.map_congr hae, hm] at h

/-- The backward recurrence time `V⁻(t)` is measurable in the renewal epochs. -/
theorem measurable_bwdTimeCts {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℕ → ℝ}
    (hZ : ∀ k, Measurable fun ω => Z ω k) (t : ℝ) : Measurable fun ω => bwdTimeCts (Z ω) t := by
  refine measurable_of_Iio fun c => ?_
  have h : (fun ω => bwdTimeCts (Z ω) t) ⁻¹' Iio c =
      (⋃ k, {ω | 1 ≤ k ∧ Z ω k ≤ t ∧ t - Z ω k < c}) ∪
        ((⋂ k, {ω | 1 ≤ k → t < Z ω k}) ∩ {_ω | 0 < c}) := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_union, mem_iUnion, mem_ofPred_eq, mem_inter_iff,
      mem_iInter]
    set S := {d | ∃ n, 1 ≤ n ∧ Z ω n ≤ t ∧ d = t - Z ω n}
    have hbdd : BddBelow S := ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
    change sInf S < c ↔ _
    by_cases hne : S.Nonempty
    · rw [csInf_lt_iff hbdd hne]
      constructor
      · rintro ⟨d, ⟨n, hn, htn, rfl⟩, hd⟩
        exact Or.inl ⟨n, hn, htn, hd⟩
      · rintro (⟨n, hn, htn, hd⟩ | ⟨hall, -⟩)
        · exact ⟨_, ⟨n, hn, htn, rfl⟩, hd⟩
        · obtain ⟨d, n, hn, htn, rfl⟩ := hne
          exact absurd (hall n hn) (not_lt.2 htn)
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, Real.sInf_empty]
      constructor
      · intro hc
        refine Or.inr ⟨fun n hn => ?_, hc⟩
        by_contra hlt
        have : t - Z ω n ∈ S := ⟨n, hn, not_lt.1 hlt, rfl⟩
        rw [hne] at this
        exact this
      · rintro (⟨n, hn, htn, hd⟩ | ⟨-, hc⟩)
        · have : t - Z ω n ∈ S := ⟨n, hn, htn, rfl⟩
          rw [hne] at this
          exact absurd this (notMem_empty _)
        · exact hc
  rw [h]
  refine (MeasurableSet.iUnion fun k => ?_).union ((MeasurableSet.iInter fun k => ?_).inter
    (MeasurableSet.const _))
  · exact (MeasurableSet.const _).inter ((measurableSet_le (hZ k) measurable_const).inter
      (measurableSet_lt (measurable_const.sub (hZ k)) measurable_const))
  · by_cases hk : 1 ≤ k
    · simp only [hk, true_implies]
      exact measurableSet_lt measurable_const (hZ k)
    · simp only [hk, false_implies, ofPred_true, MeasurableSet.univ]

/-- If `Z_{k+2}` lies beyond `t`, then `V⁻(t)` only depends on the first `k` increments. -/
theorem bwdTimeCts_truncSeq {x t : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {k : ℕ}
    (ht : t < resEpoch x w (k + 2)) :
    bwdTimeCts (resEpoch x (truncSeq k w)) t = bwdTimeCts (resEpoch x w) t := by
  unfold bwdTimeCts
  congr 1
  ext d
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, htm, rfl⟩
    by_cases hmk : m ≤ k + 1
    · rw [resEpoch_truncSeq_of_le hmk] at htm ⊢
      exact ⟨m, hm, htm, rfl⟩
    · rw [resEpoch_truncSeq_of_ge (by omega)] at htm ⊢
      exact ⟨k + 1, by omega, htm, rfl⟩
  · rintro ⟨m, hm, htm, rfl⟩
    have hmk : m ≤ k + 1 := by
      by_contra hlt
      have := resEpoch_mono (x := x) hw (show 1 ≤ k + 2 by omega) (show k + 2 ≤ m by omega)
      linarith
    exact ⟨m, hm, by rwa [resEpoch_truncSeq_of_le hmk], by rw [resEpoch_truncSeq_of_le hmk]⟩

/-- With nonnegative increments and divergent epochs, `V⁻(t)` is `t` minus the last epoch
before `t`. -/
theorem bwdTimeCts_eq_resEpoch {x t : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) (hxt : x ≤ t) :
    bwdTimeCts (resEpoch x w) t = t - resEpoch x w (sInf {m | t < resEpoch x w (m + 1)}) := by
  have hex := exists_resEpoch_gt (x := x) hdiv t
  set τ := sInf {m | t < resEpoch x w (m + 1)}
  have hτ : t < resEpoch x w (τ + 1) := Nat.sInf_mem hex
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0] at hτ
    simp [resEpoch_succ_eq] at hτ
    linarith
  have hτle : resEpoch x w τ ≤ t := by
    have := Nat.notMem_of_lt_sInf (s := {m | t < resEpoch x w (m + 1)})
      (show τ - 1 < τ by omega)
    simp only [mem_ofPred_eq, not_lt] at this
    rwa [show τ - 1 + 1 = τ by omega] at this
  refine IsLeast.csInf_eq ⟨⟨τ, by omega, hτle, rfl⟩, ?_⟩
  rintro d ⟨m, hm, hmt, rfl⟩
  have hmτ : m ≤ τ := by
    by_contra hlt
    have := resEpoch_mono (x := x) hw (show 1 ≤ τ + 1 by omega) (show τ + 1 ≤ m by omega)
    linarith
  have := resEpoch_mono (x := x) hw hm hmτ
  linarith

/-- With the increments truncated at `k` and all epochs before `t`, `V⁻(t) = t − Z_{k+1}`. -/
theorem bwdTimeCts_truncSeq_of_le {t : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {k : ℕ}
    (h0 : 0 ≤ t) (hle : ∀ m < k, resEpoch 0 w (m + 2) ≤ t) :
    bwdTimeCts (resEpoch 0 (truncSeq k w)) t = t - resEpoch 0 w (k + 1) := by
  have hw' : ∀ i, 0 ≤ truncSeq k w i := fun i => by
    unfold truncSeq
    split_ifs
    · exact hw i
    · exact le_rfl
  have hall : ∀ m, 1 ≤ m → resEpoch 0 (truncSeq k w) m ≤ resEpoch 0 w (k + 1) := fun m hm => by
    by_cases hmk : m ≤ k + 1
    · rw [← resEpoch_truncSeq_of_le (k := k) (le_refl (k + 1))]
      exact resEpoch_mono hw' hm hmk
    · rw [resEpoch_truncSeq_of_ge (by omega)]
  have hk1 : resEpoch 0 w (k + 1) ≤ t := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa [resEpoch_succ_eq] using h0
    · have := hle (k - 1) (by omega)
      rwa [show k - 1 + 2 = k + 1 by omega] at this
  refine IsLeast.csInf_eq ⟨⟨k + 1, by omega, by rwa [resEpoch_truncSeq_of_le le_rfl],
    by rw [resEpoch_truncSeq_of_le le_rfl]⟩, ?_⟩
  rintro d ⟨m, hm, hmt, rfl⟩
  have := hall m hm
  linarith

/-- One step of the backward `δ`-skeleton: the age at `δ` when the current item started at
`−a` and has length `y₀`, followed by items `y₁, y₂, …`. -/
noncomputable def bwdSkelStep (δ : ℝ) (q : ℝ × (ℕ → ℝ)) : ℝ :=
  bwdTimeCts (resEpoch (-q.1) q.2) δ

/-- The backward skeleton step is measurable. -/
theorem measurable_bwdSkelStep (δ : ℝ) : Measurable (bwdSkelStep δ) :=
  measurable_bwdTimeCts (Z := fun q : ℝ × (ℕ → ℝ) => resEpoch (-q.1) q.2)
    (fun k => (measurable_resEpoch k).comp (measurable_fst.neg.prodMk measurable_snd)) δ

/-- The backward recurrence time `δ`-skeleton `V⁻_δ(n) = V⁻(nδ)` of the renewal process with no
delay (MT (RT4), p. 69), on the canonical space `ℝ^ℕ` of increments. -/
noncomputable def bwdSkel (δ : ℝ) (n : ℕ) (w : ℕ → ℝ) : ℝ :=
  bwdTimeCts (resEpoch 0 w) (n * δ)

/-- Each `V⁻_δ(n)` is measurable. -/
theorem measurable_bwdSkel (δ : ℝ) (n : ℕ) : Measurable (bwdSkel δ n) :=
  measurable_bwdTimeCts (Z := fun w : ℕ → ℝ => resEpoch 0 w)
    (fun k => (measurable_resEpoch k).comp (measurable_const.prodMk measurable_id)) _

/-- The number of complete items before the item in progress at `nδ`. -/
noncomputable def bwdIndex (δ : ℝ) (n : ℕ) (w : ℕ → ℝ) : ℕ :=
  sInf {m | (n : ℝ) * δ < resEpoch 0 w (m + 2)}

/-- The index `bwdIndex` is a measurable random index. -/
theorem measurableSet_bwdIndex_eq (δ : ℝ) (n k : ℕ) :
    MeasurableSet {w : ℕ → ℝ | bwdIndex δ n w = k} :=
  measurableSet_natSInf_eq (P := fun (w : ℕ → ℝ) m => (n : ℝ) * δ < resEpoch 0 w (m + 2))
    (fun m => measurableSet_lt measurable_const
      ((measurable_resEpoch (m + 2)).comp (measurable_const.prodMk measurable_id))) k

/-- The item in progress at `nδ` ends after `nδ`, and the earlier ones end before. -/
theorem bwdIndex_spec {δ : ℝ} (hδ : 0 ≤ δ) {w : ℕ → ℝ} (n : ℕ)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) :
    (n : ℝ) * δ < resEpoch 0 w (bwdIndex δ n w + 2) ∧
      ∀ m < bwdIndex δ n w, resEpoch 0 w (m + 2) ≤ (n : ℝ) * δ := by
  obtain ⟨m, hm⟩ := exists_resEpoch_gt (x := 0) hdiv ((n : ℝ) * δ)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [resEpoch_succ_eq, Finset.range_zero, Finset.sum_empty, add_zero] at hm
    have : 0 ≤ (n : ℝ) * δ := mul_nonneg n.cast_nonneg hδ
    linarith
  have hex : ∃ m', (n : ℝ) * δ < resEpoch 0 w (m' + 2) :=
    ⟨m - 1, by rwa [show m - 1 + 2 = m + 1 by omega]⟩
  exact ⟨Nat.sInf_mem hex, fun m hm => not_lt.1 (Nat.notMem_of_lt_sInf hm)⟩

/-- `V⁻_δ(n) = nδ − Z_{k+1}`, `k = bwdIndex`. -/
theorem bwdSkel_eq {δ : ℝ} (hδ : 0 ≤ δ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) (n : ℕ) :
    bwdSkel δ n w = (n : ℝ) * δ - resEpoch 0 w (bwdIndex δ n w + 1) := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) * δ := mul_nonneg n.cast_nonneg hδ
  obtain ⟨h1, h2⟩ := bwdIndex_spec hδ n hdiv
  unfold bwdSkel
  rw [bwdTimeCts_eq_resEpoch hw hdiv h0]
  congr 2
  rw [natSInf_eq_iff]
  left
  refine ⟨h1, fun m hm => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simpa [resEpoch_succ_eq] using h0
  · have := h2 (m - 1) (by omega)
    rw [show m - 1 + 2 = m + 1 by omega] at this
    exact not_lt.2 this

/-- **Regeneration of the backward chain.** `V⁻_δ(n + 1)` is the skeleton step from
`V⁻_δ(n)` driven by the item in progress and the later items. -/
theorem bwdSkel_succ {δ : ℝ} (hδ : 0 ≤ δ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) (n : ℕ) :
    bwdSkel δ (n + 1) w = bwdSkelStep δ (bwdSkel δ n w, tailSeq (bwdIndex δ n w) w) := by
  set k := bwdIndex δ n w
  obtain ⟨h1, h2⟩ := bwdIndex_spec hδ n hdiv
  have hA := bwdSkel_eq hδ hw hdiv n
  set a := bwdSkel δ n w with hadef
  have hR : ∀ j, resEpoch (-a) (tailSeq k w) (j + 1) = resEpoch 0 w (k + 1 + j) - n * δ :=
    fun j => by
    rw [hA, resEpoch_succ_eq, show k + 1 + j = k + j + 1 by omega, resEpoch_succ_eq,
      resEpoch_succ_eq, Finset.sum_range_add]
    simp only [tailSeq]
    ring
  have hk1 : resEpoch 0 w (k + 1) ≤ (n : ℝ) * δ := by
    have := bwdIndex_spec hδ n hdiv
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h]
      simpa [resEpoch_succ_eq] using mul_nonneg n.cast_nonneg hδ
    · have := h2 (k - 1) (by omega)
      rwa [show k - 1 + 2 = k + 1 by omega] at this
  rw [show bwdSkel δ (n + 1) w = bwdTimeCts (resEpoch 0 w) (((n + 1 : ℕ) : ℝ) * δ) from rfl,
    show bwdSkelStep δ (a, tailSeq k w) = bwdTimeCts (resEpoch (-a) (tailSeq k w)) δ
      from rfl]
  unfold bwdTimeCts
  push_cast
  set SL := {d | ∃ m, 1 ≤ m ∧ resEpoch 0 w m ≤ ((n : ℝ) + 1) * δ ∧
    d = ((n : ℝ) + 1) * δ - resEpoch 0 w m}
  set SR := {d | ∃ j, 1 ≤ j ∧ resEpoch (-a) (tailSeq k w) j ≤ δ ∧
    d = δ - resEpoch (-a) (tailSeq k w) j}
  have hbL : BddBelow SL := ⟨0, by rintro d ⟨m, -, hm, rfl⟩; linarith⟩
  have hbR : BddBelow SR := ⟨0, by rintro d ⟨m, -, hm, rfl⟩; linarith⟩
  have hmemR : ((n : ℝ) + 1) * δ - resEpoch 0 w (k + 1) ∈ SR :=
    ⟨1, le_rfl, by rw [hR 0]; simp only [add_zero]; nlinarith,
      by rw [hR 0]; simp only [add_zero]; ring⟩
  have hsub : SR ⊆ SL := by
    rintro d ⟨j, hj, hjd, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hR] at hjd ⊢
    exact ⟨k + 1 + j, by omega, by linarith, by ring⟩
  refine le_antisymm (le_csInf ⟨_, hmemR⟩ fun d hd => csInf_le hbL (hsub hd))
    (le_csInf ⟨_, hsub hmemR⟩ ?_)
  rintro d ⟨m, hm, hmd, rfl⟩
  by_cases hmk : k + 1 ≤ m
  · refine csInf_le hbR ⟨m - k, by omega, ?_, ?_⟩
    · rw [show m - k = (m - k - 1) + 1 by omega, hR, show k + 1 + (m - k - 1) = m by omega]
      linarith
    · rw [show m - k = (m - k - 1) + 1 by omega, hR, show k + 1 + (m - k - 1) = m by omega]
      ring
  · have := resEpoch_mono (x := 0) hw hm (show m ≤ k + 1 by omega)
    exact (csInf_le hbR hmemR).trans (by linarith)

/-- The transition kernel of the backward recurrence time `δ`-skeleton: from age `a`, the
length of the item in progress has the law `Γ` conditioned on exceeding `a`. -/
noncomputable def bwdSkelKernel (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (δ : ℝ) :
    Kernel ℝ ℝ where
  toFun a := ((Measure.infinitePi fun _ : ℕ => Γ)[|{y | a < y 0}]).map
    fun y => bwdSkelStep δ (a, y)
  measurable' := Measure.measurable_of_measurable_coe _ fun B hB => by
    have hS : MeasurableSet {q : ℝ × (ℕ → ℝ) | q.1 < q.2 0} :=
      measurableSet_lt measurable_fst ((measurable_pi_apply 0).comp measurable_snd)
    have e : ∀ a, (((Measure.infinitePi fun _ : ℕ => Γ)[|{y | a < y 0}]).map
        fun y => bwdSkelStep δ (a, y)) B =
        ∫⁻ y, B.indicator 1 (bwdSkelStep δ (a, y))
          ∂((Measure.infinitePi fun _ : ℕ => Γ)[|{y | (a, y) ∈
            {q : ℝ × (ℕ → ℝ) | q.1 < q.2 0}}]) := fun a => by
      have hm : Measurable fun y => bwdSkelStep δ (a, y) :=
        (measurable_bwdSkelStep δ).comp measurable_prodMk_left
      rw [Measure.map_apply hm hB, ← lintegral_indicator_one (hm hB)]
      rfl
    simp_rw [e]
    exact measurable_lintegral_cond _ hS
      (g := fun q => B.indicator 1 (bwdSkelStep δ q))
      ((measurable_one.indicator hB).comp (measurable_bwdSkelStep δ))

/-- With a renewal at time `0`, `V⁻(0) = 0` almost surely. -/
theorem bwdSkel_zero_ae (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) (δ : ℝ) :
    bwdSkel δ 0 =ᵐ[Measure.infinitePi fun _ : ℕ => Γ] fun _ => 0 := by
  filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨hdiv, hw⟩
  unfold bwdSkel
  rw [Nat.cast_zero, zero_mul, bwdTimeCts_eq_resEpoch hw hdiv le_rfl]
  set τ := sInf {m | (0 : ℝ) < resEpoch 0 w (m + 1)}
  have hle : resEpoch 0 w τ ≤ 0 := by
    have hex := exists_resEpoch_gt (x := 0) hdiv 0
    have hτ0 : τ ≠ 0 := by
      intro h0
      have hmem : (0 : ℝ) < resEpoch 0 w (τ + 1) := Nat.sInf_mem hex
      rw [h0] at hmem
      simp [resEpoch_succ_eq] at hmem
    have := Nat.notMem_of_lt_sInf (s := {m | (0 : ℝ) < resEpoch 0 w (m + 1)})
      (show τ - 1 < τ by omega)
    simp only [mem_ofPred_eq, not_lt] at this
    rwa [show τ - 1 + 1 = τ by omega] at this
  have hge : 0 ≤ resEpoch 0 w τ := by
    rcases Nat.eq_zero_or_pos τ with h | h
    · rw [h]
      rfl
    · obtain ⟨t, ht⟩ : ∃ t, τ = t + 1 := ⟨τ - 1, by omega⟩
      rw [ht, resEpoch_succ_eq, zero_add]
      exact Finset.sum_nonneg fun i _ => hw i
  linarith

/-- **The backward recurrence time `δ`-skeleton is a Markov chain** (MT p. 69), for any
increment law `Γ` on `[0, ∞)` that is not concentrated at `0`, with kernel `bwdSkelKernel`
and initial state `0`. -/
theorem bwdSkeleton_isMarkovChain (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsMarkovChain (bwdSkelKernel Γ δ) (Measure.dirac 0) (Measure.infinitePi fun _ : ℕ => Γ)
      (bwdSkel δ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hgood := tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos
  have h0 : ν.map (bwdSkel δ 0) = Measure.dirac 0 := by
    rw [Measure.map_congr (bwdSkel_zero_ae Γ hΓ0 hΓpos δ), Measure.map_const, measure_univ,
      one_smul]
  refine isMarkovChain_of_regeneration ν ν _ (bwdSkel δ) (measurable_bwdSkel δ) h0
    (bwdIndex δ) (measurableSet_bwdIndex_eq δ) (fun _ k w => truncSeq k w)
    (fun _ k => measurable_truncSeq k) (fun _ k w => tailSeq k w)
    (fun _ k => measurable_tailSeq k) (fun _ k => infinitePi_map_trunc_tail Γ k)
    (S := {q : ℝ × (ℕ → ℝ) | q.1 < q.2 0})
    (measurableSet_lt measurable_fst ((measurable_pi_apply 0).comp measurable_snd))
    (fun n k => ?_) (measurable_bwdSkelStep δ) (fun n => ?_) _ (fun x => rfl)
  · have hset : {b : ℕ → ℝ | ∀ m < k, resEpoch 0 b (m + 2) ≤ (n : ℝ) * δ} =
        ⋂ m, ⋂ (_ : m < k), {b | resEpoch 0 b (m + 2) ≤ (n : ℝ) * δ} := by
      ext b
      simp
    refine ⟨{b : ℕ → ℝ | ∀ m < k, resEpoch 0 b (m + 2) ≤ (n : ℝ) * δ}, ?_,
      fun b j => bwdTimeCts (resEpoch 0 b) ((j : ℕ) * δ), ?_, ?_⟩
    · rw [hset]
      exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
        measurableSet_le ((measurable_resEpoch (m + 2)).comp
          (measurable_const.prodMk measurable_id)) measurable_const
    · exact measurable_pi_iff.2 fun j => measurable_bwdTimeCts
        (Z := fun w : ℕ → ℝ => resEpoch 0 w)
        (fun k => (measurable_resEpoch k).comp (measurable_const.prodMk measurable_id)) _
    · filter_upwards [hgood] with w ⟨hdiv, hw⟩
      have h0n : (0 : ℝ) ≤ (n : ℝ) * δ := mul_nonneg n.cast_nonneg hδ
      have hex : ∃ m, (n : ℝ) * δ < resEpoch 0 w (m + 2) :=
        ⟨bwdIndex δ n w, (bwdIndex_spec hδ n hdiv).1⟩
      have hiff : bwdIndex δ n w = k ↔ ((n : ℝ) * δ < resEpoch 0 w (k + 2) ∧
          ∀ m < k, resEpoch 0 w (m + 2) ≤ (n : ℝ) * δ) := by
        unfold bwdIndex
        rw [natSInf_eq_iff]
        simp only [not_lt]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact h
          · obtain ⟨m, hm⟩ := hex
            exact absurd hm (not_lt.2 (h m))
        · exact Or.inl
      have hT : (truncSeq k w ∈ {b : ℕ → ℝ | ∀ m < k, resEpoch 0 b (m + 2) ≤ (n : ℝ) * δ}) ↔
          ∀ m < k, resEpoch 0 w (m + 2) ≤ (n : ℝ) * δ := by
        simp only [mem_ofPred_eq]
        exact forall₂_congr fun m hm => by rw [resEpoch_truncSeq_of_le (by omega)]
      refine ⟨?_, fun hk j => ?_⟩
      · rw [hiff]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨hT.2 h2, ?_⟩
          simp only [Fin.val_last]
          rw [bwdTimeCts_truncSeq_of_le hw h0n h2]
          simp only [tailSeq, add_zero]
          rw [show k + 2 = k + 1 + 1 by omega, resEpoch_succ_eq, Finset.sum_range_succ] at h1
          rw [resEpoch_succ_eq]
          linarith
        · rintro ⟨h2', h1⟩
          have h2 := hT.1 h2'
          refine ⟨?_, h2⟩
          simp only [Fin.val_last] at h1
          rw [bwdTimeCts_truncSeq_of_le hw h0n h2] at h1
          simp only [tailSeq, add_zero] at h1
          rw [show k + 2 = k + 1 + 1 by omega, resEpoch_succ_eq, Finset.sum_range_succ]
          rw [resEpoch_succ_eq] at h1
          linarith
      · have hk' := (hiff.1 hk).1
        have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.2
        have hjn : ((j : ℕ) : ℝ) * δ ≤ (n : ℝ) * δ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ
        exact (bwdTimeCts_truncSeq hw (lt_of_le_of_lt hjn hk')).symm
  · filter_upwards [hgood] with w ⟨hdiv, hw⟩
    exact bwdSkel_succ hδ hw hdiv n

/-- If the second epoch lies beyond `t ≥ c`, then `V⁻(t) = t − c`. -/
theorem bwdTimeCts_first {c t : ℝ} {z : ℕ → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, z i) atTop atTop) (hct : c ≤ t)
    (hnext : t < c + z 0) : bwdTimeCts (resEpoch c z) t = t - c := by
  rw [bwdTimeCts_eq_resEpoch hz hdiv hct]
  have : sInf {m | t < resEpoch c z (m + 1)} = 1 := by
    rw [natSInf_eq_iff]
    left
    refine ⟨by simpa [resEpoch_succ_eq] using hnext, fun m hm => ?_⟩
    obtain rfl : m = 0 := by omega
    simpa [resEpoch_succ_eq] using hct
  rw [this]
  simp [resEpoch_succ_eq]

/-- If the item in progress outlasts the next `δ`, the age grows by `δ`. -/
theorem bwdSkelStep_of_gt {δ x : ℝ} (hx : 0 ≤ x) {y : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, y i) atTop atTop) (hδ : 0 ≤ δ)
    (hxy : x + δ < y 0) : bwdSkelStep δ (x, y) = x + δ := by
  unfold bwdSkelStep
  rw [bwdTimeCts_first hy hdiv (by linarith) (by linarith)]
  ring

/-- If the item in progress ends within the next `δ`, the age is less than `x + δ`. -/
theorem bwdSkelStep_lt {δ x : ℝ} (hx : 0 ≤ x) {y : ℕ → ℝ} (hxy : x < y 0)
    (hyx : y 0 ≤ x + δ) :
    bwdSkelStep δ (x, y) < x + δ := by
  unfold bwdSkelStep
  have h2 : resEpoch (-x) y 2 ≤ δ := by
    simp only [show (2 : ℕ) = 1 + 1 by norm_num, resEpoch_succ_eq, Finset.sum_range_one]
    linarith
  have hS : BddBelow {d | ∃ n, 1 ≤ n ∧ resEpoch (-x) y n ≤ δ ∧ d = δ - resEpoch (-x) y n} :=
    ⟨0, by rintro d ⟨n, -, hn, rfl⟩; linarith⟩
  have := csInf_le hS ⟨2, by norm_num, h2, rfl⟩
  change bwdTimeCts (resEpoch (-x) y) δ ≤ _ at this
  refine lt_of_le_of_lt this ?_
  simp only [show (2 : ℕ) = 1 + 1 by norm_num, resEpoch_succ_eq, Finset.sum_range_one]
  linarith

/-- If the item in progress ends within the next `δ`, the age at `δ` is computed from the
renewal process started at its end. -/
theorem bwdSkelStep_split {δ x : ℝ} (hx : 0 ≤ x) {y : ℕ → ℝ} (hxy : x < y 0) (hyx : y 0 ≤ x + δ) :
    bwdSkelStep δ (x, y) = bwdTimeCts (resEpoch (y 0 - x) (tailSeq 1 y)) δ := by
  have hR : ∀ m, resEpoch (y 0 - x) (tailSeq 1 y) (m + 1) = resEpoch (-x) y (m + 2) := fun m => by
    rw [show m + 2 = m + 1 + 1 by omega, resEpoch_succ_eq, resEpoch_succ_eq,
      Finset.sum_range_succ']
    simp only [tailSeq]
    have : ∑ i ∈ Finset.range m, y (1 + i) = ∑ i ∈ Finset.range m, y (i + 1) :=
      Finset.sum_congr rfl fun i _ => by rw [add_comm]
    rw [this]
    ring
  unfold bwdSkelStep bwdTimeCts
  set SL := {d | ∃ n, 1 ≤ n ∧ resEpoch (-x) y n ≤ δ ∧ d = δ - resEpoch (-x) y n}
  set SR := {d | ∃ n, 1 ≤ n ∧ resEpoch (y 0 - x) (tailSeq 1 y) n ≤ δ ∧
    d = δ - resEpoch (y 0 - x) (tailSeq 1 y) n}
  have hbL : BddBelow SL := ⟨0, by rintro d ⟨m, -, hm, rfl⟩; linarith⟩
  have hbR : BddBelow SR := ⟨0, by rintro d ⟨m, -, hm, rfl⟩; linarith⟩
  have hR0 : resEpoch (y 0 - x) (tailSeq 1 y) 1 = y 0 - x := by simp [resEpoch_succ_eq]
  have hmemR : δ - (y 0 - x) ∈ SR := ⟨1, le_rfl, by rw [hR0]; linarith, by rw [hR0]⟩
  have hsub : SR ⊆ SL := by
    rintro d ⟨j, hj, hjd, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hR] at hjd ⊢
    exact ⟨j + 2, by omega, hjd, rfl⟩
  refine le_antisymm (le_csInf ⟨_, hmemR⟩ fun d hd => csInf_le hbL (hsub hd))
    (le_csInf ⟨_, hsub hmemR⟩ ?_)
  rintro d ⟨m, hm, hmd, rfl⟩
  by_cases hm2 : 2 ≤ m
  · refine csInf_le hbR ⟨m - 1, by omega, ?_, ?_⟩
    · rw [show m - 1 = (m - 2) + 1 by omega, hR, show m - 2 + 2 = m by omega]
      exact hmd
    · rw [show m - 1 = (m - 2) + 1 by omega, hR, show m - 2 + 2 = m by omega]
  · obtain rfl : m = 1 := by omega
    refine (csInf_le hbR hmemR).trans ?_
    simp only [resEpoch_succ_eq, Finset.range_zero, Finset.sum_empty, add_zero]
    linarith

/-- `Γ^{⊗ℕ}{y : y₀ ∈ B} = Γ(B)`. -/
theorem infinitePi_measure_head (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {B : Set ℝ}
    (hB : MeasurableSet B) :
    (Measure.infinitePi fun _ : ℕ => Γ) {y | y 0 ∈ B} = Γ B := by
  have : {y : ℕ → ℝ | y 0 ∈ B} = (fun y : ℕ → ℝ => y 0) ⁻¹' B := rfl
  rw [this, ← Measure.map_apply (measurable_pi_apply 0) hB, Measure.infinitePi_map_eval]

/-- MT p. 70: `P(V⁻(nδ) = x + δ | V⁻((n − 1)δ) = x) = Γ(x + δ, ∞)/Γ(x, ∞)`. -/
theorem bwdSkelKernel_apply_add (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    bwdSkelKernel Γ δ x {x + δ} = Γ (Ioi (x + δ)) / Γ (Ioi x) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hm : Measurable fun y => bwdSkelStep δ (x, y) :=
    (measurable_bwdSkelStep δ).comp measurable_prodMk_left
  have hD : MeasurableSet {y : ℕ → ℝ | x < y 0} :=
    measurableSet_lt measurable_const (measurable_pi_apply 0)
  change ((ν[|{y | x < y 0}]).map fun y => bwdSkelStep δ (x, y)) {x + δ} = _
  have hνD : ν {y | x < y 0} = Γ (Ioi x) := infinitePi_measure_head Γ measurableSet_Ioi
  rw [Measure.map_apply hm (measurableSet_singleton _), cond_apply hD, hνD]
  have hset : ({y : ℕ → ℝ | x < y 0} ∩ (fun y => bwdSkelStep δ (x, y)) ⁻¹' {x + δ} : Set _)
      =ᵐ[ν] {y | y 0 ∈ Ioi (x + δ)} := by
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with y ⟨hdiv, hy⟩
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, mem_Ioi,
      eq_iff_iff]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hle
      exact absurd h2 (bwdSkelStep_lt hx h1 (not_lt.1 hle)).ne
    · intro h
      exact ⟨by linarith, bwdSkelStep_of_gt hx hy hdiv hδ h⟩
  rw [measure_congr hset, infinitePi_measure_head Γ measurableSet_Ioi, ENNReal.div_eq_inv_mul]

/-- `∫ U(ds) 1{δ − c − s ∈ A} Γ(δ − c − s, ∞)`: the law of the age at `δ` after a renewal
at `c`. -/
noncomputable def bwdInner (Γ : Measure ℝ) (δ c : ℝ) (A : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ s, A.indicator (fun v => Γ (Ioi v)) (δ - c - s) ∂renewalMeasure Γ

/-- Decomposing `{V⁻(δ) ∈ A}` over the index `j` of the last epoch before `δ`. -/
theorem indicator_bwdTimeCts_eq_tsum {c δ : ℝ} (hcδ : c ≤ δ) {z : ℕ → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, z i) atTop atTop) {A : Set ℝ}
    (hA0 : A ⊆ Ico 0 δ) :
    A.indicator (1 : ℝ → ℝ≥0∞) (bwdTimeCts (resEpoch c z) δ) =
      ∑' j, {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, z i, z j) := by
  have hex := exists_resEpoch_gt (x := c) hdiv δ
  set τ := sInf {m | δ < resEpoch c z (m + 1)} with hτdef
  have hτ : δ < resEpoch c z (τ + 1) := Nat.sInf_mem hex
  have hmin : ∀ m < τ, resEpoch c z (m + 1) ≤ δ := fun m hm =>
    not_lt.1 (Nat.notMem_of_lt_sInf hm)
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, resEpoch_succ_eq] at hτ
    simp at hτ
    linarith
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, τ = j₀ + 1 := ⟨τ - 1, by omega⟩
  rw [bwdTimeCts_eq_resEpoch hz hdiv hcδ, ← hτdef, tsum_eq_single j₀ fun j hj => ?_]
  · have hnext : δ < c + ∑ i ∈ Finset.range j₀, z i + z j₀ := by
      rw [hj₀, resEpoch_succ_eq, Finset.sum_range_succ] at hτ
      linarith
    have e : δ - resEpoch c z τ = δ - c - ∑ i ∈ Finset.range j₀, z i := by
      rw [hj₀, resEpoch_succ_eq]
      ring
    rw [e]
    by_cases hA : δ - c - ∑ i ∈ Finset.range j₀, z i ∈ A
    · rw [indicator_of_mem hA, indicator_of_mem (show (∑ i ∈ Finset.range j₀, z i, z j₀) ∈
        {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2} from ⟨hA, hnext⟩)]
      rfl
    · rw [indicator_of_notMem hA, indicator_of_notMem (show (∑ i ∈ Finset.range j₀, z i, z j₀) ∉
        {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2} from fun h => hA h.1)]
  · refine indicator_of_notMem ?_ _
    rintro ⟨h1, h2⟩
    simp only at h1 h2
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · have h3 := hmin (j + 1) (by omega)
      rw [resEpoch_succ_eq, Finset.sum_range_succ] at h3
      linarith
    · have h3 := resEpoch_mono (x := c) hz (show 1 ≤ τ + 1 by omega)
        (show τ + 1 ≤ j + 1 by omega)
      simp only [resEpoch_succ_eq] at h3 hτ
      have := (hA0 h1).1
      linarith

/-- One term of the backward-chain display: the contribution of the `j`-th renewal. -/
theorem lintegral_partialSum_pair_bwd (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {δ c : ℝ}
    {A : Set ℝ} (hA : MeasurableSet A) (j : ℕ) :
    ∫⁻ w, {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j) ∂(Measure.infinitePi fun _ : ℕ => Γ) =
      ∫⁻ s, A.indicator (fun v => Γ (Ioi v)) (δ - c - s) ∂(convPow Γ j) := by
  set E : Set (ℝ × ℝ) := {q | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2} with hEdef
  have hE : MeasurableSet E :=
    ((measurable_const.sub measurable_fst) hA).inter
      (measurableSet_lt measurable_const ((measurable_const.add measurable_fst).add
        measurable_snd))
  have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hcp := isProbabilityMeasure_convPow Γ j
  have h1 : ∫⁻ w, E.indicator (1 : ℝ × ℝ → ℝ≥0∞) (∑ i ∈ Finset.range j, w i, w j)
      ∂(Measure.infinitePi fun _ : ℕ => Γ) = ((convPow Γ j).prod Γ) E := by
    rw [← infinitePi_map_partialSum_next Γ j, Measure.map_apply hpair hE,
      ← lintegral_indicator_one (hpair hE)]
    rfl
  rw [h1, Measure.prod_apply hE]
  refine lintegral_congr fun s => ?_
  by_cases hs : δ - c - s ∈ A
  · rw [indicator_of_mem hs]
    congr 1
    ext t
    simp only [mem_preimage, hEdef, mem_ofPred_eq, mem_Ioi]
    constructor
    · rintro ⟨-, h⟩
      linarith
    · intro h
      exact ⟨hs, by linarith⟩
  · rw [indicator_of_notMem hs]
    convert measure_empty (μ := Γ)
    ext t
    simp only [mem_preimage, hEdef, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact fun h => hs h.1

/-- After a renewal at `c ≤ δ`, the age at `δ` lies in `A ⊆ [0, δ)` with probability
`∫ U(ds) 1{δ − c − s ∈ A} Γ(δ − c − s, ∞)`. -/
theorem bwd_inner (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) {δ c : ℝ} (hcδ : c ≤ δ) {A : Set ℝ} (hA : MeasurableSet A)
    (hA0 : A ⊆ Ico 0 δ) :
    (Measure.infinitePi fun _ : ℕ => Γ) {z | bwdTimeCts (resEpoch c z) δ ∈ A} =
      bwdInner Γ δ c A := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hE : MeasurableSet {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2} :=
    ((measurable_const.sub measurable_fst) hA).inter
      (measurableSet_lt measurable_const ((measurable_const.add measurable_fst).add
        measurable_snd))
  have hpair : ∀ j, Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) := fun j =>
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hbm : Measurable fun z : ℕ → ℝ => bwdTimeCts (resEpoch c z) δ :=
    measurable_bwdTimeCts (Z := fun z : ℕ → ℝ => resEpoch c z)
      (fun k => (measurable_resEpoch k).comp (measurable_const.prodMk measurable_id)) δ
  rw [← lintegral_indicator_one (s := {z | bwdTimeCts (resEpoch c z) δ ∈ A}) (hbm hA)]
  have hae : ∀ᵐ z ∂ν, {z | bwdTimeCts (resEpoch c z) δ ∈ A}.indicator
      (1 : (ℕ → ℝ) → ℝ≥0∞) z =
      ∑' j, {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, z i, z j) := by
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with z ⟨hdiv, hz⟩
    rw [← indicator_bwdTimeCts_eq_tsum hcδ hz hdiv hA0]
    by_cases h : bwdTimeCts (resEpoch c z) δ ∈ A
    · rw [indicator_of_mem (show z ∈ {z | bwdTimeCts (resEpoch c z) δ ∈ A} from h),
        indicator_of_mem h]
      rfl
    · rw [indicator_of_notMem (show z ∉ {z | bwdTimeCts (resEpoch c z) δ ∈ A} from h),
        indicator_of_notMem h]
  have hmj : ∀ j, AEMeasurable (fun w : ℕ → ℝ =>
      {q : ℝ × ℝ | δ - c - q.1 ∈ A ∧ δ < c + q.1 + q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j)) ν := fun j =>
    (Measurable.indicator measurable_one hE |>.comp (hpair j)).aemeasurable
  rw [lintegral_congr_ae hae, lintegral_tsum hmj]
  refine (tsum_congr fun j => lintegral_partialSum_pair_bwd Γ hA j).trans ?_
  rw [bwdInner, renewalMeasure, lintegral_sum_measure]

/-- Under `Γ^{⊗ℕ}`, the first increment and the rest are independent with laws `Γ` and
`Γ^{⊗ℕ}`. -/
theorem infinitePi_map_head_tail (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun y => (y 0, tailSeq 1 y)) =
      Γ.prod (Measure.infinitePi fun _ : ℕ => Γ) := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hc : (fun y : ℕ → ℝ => (y 0, tailSeq 1 y)) =
      Prod.map (fun b : ℕ → ℝ => b 0) id ∘ fun y => (truncSeq 1 y, tailSeq 1 y) := by
    funext y
    simp [truncSeq]
  have h0 : (ν.map (truncSeq 1)).map (fun b : ℕ → ℝ => b 0) = Γ := by
    rw [Measure.map_map (measurable_pi_apply 0) (measurable_truncSeq 1)]
    have : ((fun b : ℕ → ℝ => b 0) ∘ truncSeq 1) = fun y : ℕ → ℝ => y 0 := by
      funext y
      simp [truncSeq]
    rw [this, Measure.infinitePi_map_eval]
  rw [hc, ← Measure.map_map ((measurable_pi_apply 0).prodMap measurable_id)
    ((measurable_truncSeq 1).prodMk (measurable_tailSeq 1)), infinitePi_map_trunc_tail,
    ← Measure.map_prod_map _ _ (measurable_pi_apply 0) measurable_id, Measure.map_id, h0]

/-- **The backward-chain display of MT p. 70, corrected.** For `A ⊆ [0, δ)`,
`P(V⁻(nδ) ∈ A | V⁻((n−1)δ) = x) =
  Γ(x, ∞)⁻¹ ∫_{(x, x+δ]} Γ(du) ∫ U(ds) 1{δ − (u − x) − s ∈ A} Γ(δ − (u − x) − s, ∞)`:
the normalisation is a division by `Γ(x, ∞)`, not by `[Γ(x, ∞)]⁻¹`. -/
theorem bwdSkelKernel_apply_of_subset (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x)
    {A : Set ℝ} (hA : MeasurableSet A) (hA0 : A ⊆ Ico 0 δ) :
    bwdSkelKernel Γ δ x A =
      (Γ (Ioi x))⁻¹ * ∫⁻ u in Ioc x (x + δ), bwdInner Γ δ (u - x) A ∂Γ := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hm : Measurable fun y => bwdSkelStep δ (x, y) :=
    (measurable_bwdSkelStep δ).comp measurable_prodMk_left
  have hD : MeasurableSet {y : ℕ → ℝ | x < y 0} :=
    measurableSet_lt measurable_const (measurable_pi_apply 0)
  have hνD : ν {y | x < y 0} = Γ (Ioi x) := infinitePi_measure_head Γ measurableSet_Ioi
  change ((ν[|{y | x < y 0}]).map fun y => bwdSkelStep δ (x, y)) A = _
  rw [Measure.map_apply hm hA, cond_apply hD, hνD]
  congr 1
  set G : Set (ℝ × (ℕ → ℝ)) :=
    {q | q.1 ∈ Ioc x (x + δ) ∧ bwdTimeCts (resEpoch (q.1 - x) q.2) δ ∈ A} with hGdef
  have hbm : Measurable fun q : ℝ × (ℕ → ℝ) => bwdTimeCts (resEpoch (q.1 - x) q.2) δ :=
    measurable_bwdTimeCts (Z := fun q : ℝ × (ℕ → ℝ) => resEpoch (q.1 - x) q.2)
      (fun k => (measurable_resEpoch k).comp
        ((measurable_fst.sub measurable_const).prodMk measurable_snd)) δ
  have hG : MeasurableSet G := (measurable_fst measurableSet_Ioc).inter (hbm hA)
  have hht : Measurable fun y : ℕ → ℝ => (y 0, tailSeq 1 y) :=
    (measurable_pi_apply 0).prodMk (measurable_tailSeq 1)
  have hset : ({y : ℕ → ℝ | x < y 0} ∩ (fun y => bwdSkelStep δ (x, y)) ⁻¹' A : Set _)
      =ᵐ[ν] (fun y : ℕ → ℝ => (y 0, tailSeq 1 y)) ⁻¹' G := by
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with y ⟨hdiv, hy⟩
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, hGdef, mem_Ioc, eq_iff_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hle : y 0 ≤ x + δ := by
        by_contra hlt
        rw [bwdSkelStep_of_gt hx hy hdiv hδ (not_le.1 hlt)] at h2
        have := (hA0 h2).2
        linarith
      refine ⟨⟨h1, hle⟩, ?_⟩
      rwa [← bwdSkelStep_split hx h1 hle]
    · rintro ⟨⟨h1, hle⟩, h2⟩
      exact ⟨h1, by rwa [bwdSkelStep_split hx h1 hle]⟩
  rw [measure_congr hset, ← Measure.map_apply hht hG, infinitePi_map_head_tail,
    Measure.prod_apply hG, ← lintegral_indicator measurableSet_Ioc]
  refine lintegral_congr fun u => ?_
  by_cases hu : u ∈ Ioc x (x + δ)
  · rw [indicator_of_mem hu, ← bwd_inner Γ hΓ0 hΓpos (by linarith [hu.2]) hA hA0]
    congr 1
    ext z
    simp only [mem_preimage, hGdef, mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
  · rw [indicator_of_notMem hu]
    convert measure_empty (μ := ν)
    ext z
    simp only [mem_preimage, hGdef, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact fun h => absurd h hu

/-- The increment law `Γ = ½δ₁ + ½δ₂` of the counterexample to the backward display. -/
noncomputable def halfOneTwo : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac 1 + (2⁻¹ : ℝ≥0∞) • Measure.dirac 2

/-- `Γ(A) = ½·1_A(1) + ½·1_A(2)`. -/
theorem halfOneTwo_apply {A : Set ℝ} (hA : MeasurableSet A) :
    halfOneTwo A = 2⁻¹ * A.indicator 1 1 + 2⁻¹ * A.indicator 1 2 := by
  simp [halfOneTwo, Measure.dirac_apply' _ hA]

/-- `½δ₁ + ½δ₂` is a probability measure. -/
theorem isProbabilityMeasure_halfOneTwo : IsProbabilityMeasure halfOneTwo :=
  ⟨by
    rw [halfOneTwo_apply MeasurableSet.univ]
    simp only [indicator_univ, Pi.one_apply, mul_one]
    exact ENNReal.inv_two_add_inv_two⟩

/-- `∫ f dΓ = ½f(1) + ½f(2)`. -/
theorem lintegral_halfOneTwo (f : ℝ → ℝ≥0∞) :
    ∫⁻ u, f u ∂halfOneTwo = 2⁻¹ * f 1 + 2⁻¹ * f 2 := by
  rw [halfOneTwo, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  rfl

/-- `Γ^{j∗}` is the law of `y₀ + ⋯ + y_{j−1}` under `Γ^{⊗ℕ}`. -/
theorem convPow_eq_map (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (j : ℕ) :
    convPow Γ j = (Measure.infinitePi fun _ : ℕ => Γ).map
      (fun w : ℕ → ℝ => ∑ i ∈ Finset.range j, w i) := by
  have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have := congrArg (Measure.map Prod.fst) (infinitePi_map_partialSum_next Γ j)
  rw [Measure.map_map measurable_fst hpair, Measure.map_fst_prod, measure_univ,
    one_smul] at this
  exact this.symm

/-- **Correction to the backward display of MT p. 70.** With `Γ = ½δ₁ + ½δ₂`, `δ = 1` and
age `x = 1`, the item in progress has length `2` and ends exactly one time unit later, so the
age moves surely to `0`: `P(1, {0}) = 1`. The printed normalisation, dividing by
`[Γ(x, ∞)]⁻¹`, i.e. multiplying by `Γ(x, ∞) = ½`, gives `1/4 ≠ 1`. -/
theorem bwd_display_counterexample :
    (@bwdSkelKernel halfOneTwo isProbabilityMeasure_halfOneTwo 1) 1 {0} = 1 ∧
      halfOneTwo (Ioi 1) * ∫⁻ u in Ioc 1 (1 + 1), bwdInner halfOneTwo 1 (u - 1) {0}
        ∂halfOneTwo ≠ 1 := by
  have := isProbabilityMeasure_halfOneTwo
  have hI0 : halfOneTwo (Iio 0) = 0 := by
    rw [halfOneTwo_apply measurableSet_Iio]
    norm_num [indicator]
  have hI1 : halfOneTwo (Iio 1) = 0 := by
    rw [halfOneTwo_apply measurableSet_Iio]
    norm_num [indicator]
  have hO0 : halfOneTwo (Ioi 0) = 1 := by
    rw [halfOneTwo_apply measurableSet_Ioi]
    norm_num [indicator]
    exact ENNReal.inv_two_add_inv_two
  have hO1 : halfOneTwo (Ioi 1) = 2⁻¹ := by
    rw [halfOneTwo_apply measurableSet_Ioi]
    norm_num [indicator]
  have hpos : 0 < halfOneTwo (Ioi 0) := by rw [hO0]; exact one_pos
  have hU : renewalMeasure halfOneTwo {0} = 1 := by
    rw [renewalMeasure, Measure.sum_apply _ (measurableSet_singleton 0),
      tsum_eq_single 0 fun j hj => ?_]
    · rw [convPow_eq_map, Measure.map_apply (Finset.measurable_sum _ fun i _ =>
        measurable_pi_apply i) (measurableSet_singleton 0)]
      simp
    · rw [convPow_eq_map, Measure.map_apply (Finset.measurable_sum _ fun i _ =>
        measurable_pi_apply i) (measurableSet_singleton 0)]
      refine measure_mono_null (t := ⋃ i, {w : ℕ → ℝ | w i < 1}) (fun w hw => ?_) ?_
      · by_contra hc
        simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hc
        simp only [mem_preimage, mem_singleton_iff] at hw
        have h1 : ∑ i ∈ Finset.range j, w i ≥ ∑ i ∈ Finset.range j, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => hc i
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
        have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
        linarith
      · refine measure_iUnion_null fun i => ?_
        have : {w : ℕ → ℝ | w i < 1} = (fun w : ℕ → ℝ => w i) ⁻¹' Iio 1 := rfl
        rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio,
          Measure.infinitePi_map_eval, hI1]
  have hinner : bwdInner halfOneTwo 1 (2 - 1) {0} = 1 := by
    rw [bwdInner]
    have : (fun s : ℝ => ({0} : Set ℝ).indicator (fun v => halfOneTwo (Ioi v)) (1 - (2 - 1) - s))
        = ({0} : Set ℝ).indicator 1 := by
      funext s
      by_cases hs : s = 0
      · subst hs
        norm_num [hO0]
      · have : (1 : ℝ) - (2 - 1) - s ≠ 0 := by
          intro h
          apply hs
          linarith
        simp [hs, this]
    rw [this, lintegral_indicator_one (measurableSet_singleton 0), hU]
  have hint : ∫⁻ u in Ioc 1 (1 + 1), bwdInner halfOneTwo 1 (u - 1) {0} ∂halfOneTwo = 2⁻¹ := by
    rw [← lintegral_indicator measurableSet_Ioc, lintegral_halfOneTwo]
    rw [indicator_of_notMem (show (1 : ℝ) ∉ Ioc 1 (1 + 1) by simp),
      indicator_of_mem (show (2 : ℝ) ∈ Ioc 1 (1 + 1) by norm_num), hinner]
    simp
  refine ⟨?_, ?_⟩
  · rw [bwdSkelKernel_apply_of_subset halfOneTwo hI0 hpos zero_le_one zero_le_one
      (measurableSet_singleton 0) (by simp), hint, hO1, inv_inv]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  · rw [hint, hO1]
    intro h
    have h2 : (2⁻¹ : ℝ≥0∞) * 2⁻¹ < 1 := by
      calc (2⁻¹ : ℝ≥0∞) * 2⁻¹ ≤ 2⁻¹ * 1 := by gcongr; exact ENNReal.inv_le_one.2 (by norm_num)
        _ < 1 := by rw [mul_one]; exact ENNReal.inv_lt_one.2 (by norm_num)
    exact absurd h h2.ne

end MeynTweedie.PseudoAtoms

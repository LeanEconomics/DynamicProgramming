/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.MixedDrift
import GeneralizedDrift.LadderChains

/-!
# A mixed drift criterion for the ladder chain (MT §19.3.2)

Meyn and Tweedie, §19.3.2, pp. 502–506. The ladder chain `ladderChainKernel Λ Λ*` on `ℤ₊ × ℝ`
((3.40), (10.37)) with the homogeneous zero-level transitions (19.65),
`Λ*ᵢ(x, A) = Σ_{j ≥ i+1} Λⱼ(x, A)` (`ladderStar`); the book's "`j = k + 1`" is `j = i + 1`.

**Results.**
* `avgLadderKernel_snd_preimage`, `avgLadderKernel_pow_map_snd` ((19.66), p. 502): the position
  `Φ^Λ` on the rung is a Markov chain with kernel `Λ = Σⱼ Λⱼ` (`ladderMarg`):
  `Pⁿ(i, x; ℤ₊ × B) = Λⁿ(x, B)`.
* `lintegral_fst_ladderKernel`: the expected next rung from `(i, w)` is
  `m(i, w) = Σ_{k ≤ i} (i + 1 − k) Λₖ(w, X)`; `meanRung_add_truncBeta_le`: with the truncated
  ladder heights `h_d(w) = Σₖ min(k, d + 1) Λₖ(w, X)` (`truncBeta`, increasing to
  `β(w) = Σₖ k Λₖ(w, X)`, (19.67)), `m(i, w) + h_d(w) ≤ i + 1 + (d + 1) 1{i < d}` — this is the
  drift `ΔV(i, w) = 1 − h_i(w)` of `V(i, w) = i` and its monotonicity (19.69).
* `cesaro_truncBeta_bound` ((19.70) and (19.74)): summing the drift along the path,
  `Σ_{k<n} ∫ Λᵏ(x, dw) h_d(w) ≤ i + n + (d + 1) Σ_{k<n} Pᵏ(i, x; {rung < d})`.
* `tendsto_cesaro_low_of_isNull` ((19.75)): if the chain is null, the rungs below `d` are null in
  the Cesàro sense, at every `x` where the ergodic theorem holds for `Φ^Λ` (Theorem 18.2.2 for a
  petite cover, and the ergodic theorem (13.62) for `Φ^Λ`).
* **Theorem 19.3.4** (`theorem_19_3_4`, p. 503): if the chain is `ψ`-irreducible, has the
  structure (19.65), and `Φ^Λ` has an invariant probability `ν` with `∫ ν(dw) β(w) > 1` (19.68),
  then the chain is positive: it has an invariant probability.

**Proof.** The book's argument, with the truncation organised differently: instead of `ΔV(d, ·)`
and the sets `D_v` of (19.73), the bound uses `h_d ≤ d + 1`, and (19.70) is replaced by the
summed inequality above; the contradiction is `∫ ν h_d ≤ 1` for all `d`, against (19.68).
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal NNReal Topology

/-- **The homogeneous zero-level transitions** (19.65): `Λ*ᵢ = Σ_{j ≥ i+1} Λⱼ`. -/
noncomputable def ladderStar (Λ : ℕ → Kernel ℝ ℝ) (i : ℕ) : Kernel ℝ ℝ :=
  Kernel.sum fun j => Λ (j + (i + 1))

/-- **The marginal kernel** `Λ = Σⱼ Λⱼ` of the position on the rung (MT p. 502). -/
noncomputable def ladderMarg (Λ : ℕ → Kernel ℝ ℝ) : Kernel ℝ ℝ := Kernel.sum Λ

/-- **The expected change in ladder height** (19.67): `β(w) = Σⱼ j Λⱼ(w, X)`. -/
noncomputable def ladderBeta (Λ : ℕ → Kernel ℝ ℝ) (w : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, (j : ℝ≥0∞) * Λ j w univ

/-- The truncated heights `h_d(w) = Σₖ min(k, d + 1) Λₖ(w, X)`. -/
noncomputable def truncBeta (Λ : ℕ → Kernel ℝ ℝ) (d : ℕ) (w : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ((min k (d + 1) : ℕ) : ℝ≥0∞) * Λ k w univ

/-- The ladder chain with the structure (19.65). -/
noncomputable abbrev avgLadderKernel (Λ : ℕ → Kernel ℝ ℝ) : Kernel (ℕ × ℝ) (ℕ × ℝ) :=
  ladderChainKernel Λ (ladderStar Λ)

/-- Row `i` charges `ℤ₊ × B` with `Λ(x, B)`. -/
theorem avgLadderKernel_snd_preimage (Λ : ℕ → Kernel ℝ ℝ) (i : ℕ) (x : ℝ) {B : Set ℝ}
    (hB : MeasurableSet B) :
    avgLadderKernel Λ (i, x) (Prod.snd ⁻¹' B) = ladderMarg Λ x B := by
  have hm : ∀ m : ℕ, Prod.mk m ⁻¹' (Prod.snd ⁻¹' B) = B := fun m => by ext y; simp
  rw [ladderChainKernel_apply, ladderRow, FunLike.coe_add, Pi.add_apply, Measure.add_apply,
    Kernel.sum_apply' _ _ (measurable_snd hB), tsum_fintype,
    Kernel.map_apply' _ measurable_prodMk_left x (measurable_snd hB), hm, ladderStar,
    Kernel.sum_apply' _ _ hB, ladderMarg, Kernel.sum_apply' _ _ hB]
  simp_rw [Kernel.map_apply' _ measurable_prodMk_left x (measurable_snd hB), hm]
  rw [Fin.sum_univ_eq_sum_range (fun k => Λ k x B), add_comm]
  exact ENNReal.summable.sum_add_tsum_nat_add' (f := fun k => Λ k x B) (k := i + 1)

/-- Under (19.65) the ladder chain is a Markov kernel when `Λ` is. -/
theorem isMarkovKernel_avgLadderKernel (Λ : ℕ → Kernel ℝ ℝ) [IsMarkovKernel (ladderMarg Λ)] :
    IsMarkovKernel (avgLadderKernel Λ) :=
  ⟨fun p => ⟨by
    rw [← preimage_univ (f := Prod.snd), show p = (p.1, p.2) from rfl,
      avgLadderKernel_snd_preimage Λ p.1 p.2 MeasurableSet.univ, measure_univ]⟩⟩

/-- **(19.66)**, MT p. 502: the position on the rung moves by `Λ`:
`Pⁿ(i, x; ℤ₊ × ·) = Λⁿ(x, ·)`. -/
theorem avgLadderKernel_pow_map_snd (Λ : ℕ → Kernel ℝ ℝ) [IsMarkovKernel (ladderMarg Λ)] (n : ℕ)
    (z : ℕ × ℝ) : ((avgLadderKernel Λ ^ n) z).map Prod.snd = (ladderMarg Λ ^ n) z.2 := by
  have := isMarkovKernel_avgLadderKernel Λ
  induction n generalizing z with
  | zero =>
    rw [pow_zero_apply, pow_zero_apply]
    ext B hB
    rw [Measure.map_apply measurable_snd hB, Measure.dirac_apply' _ (measurable_snd hB),
      Measure.dirac_apply' _ hB]
    rfl
  | succ n ih =>
    ext B hB
    rw [Measure.map_apply measurable_snd hB, pow_succ_apply' _ n z (measurable_snd hB),
      pow_succ_apply' _ n z.2 hB, ← ih z,
      lintegral_map (Kernel.measurable_coe _ hB) measurable_snd]
    refine lintegral_congr fun y => ?_
    rw [show y = (y.1, y.2) from rfl, avgLadderKernel_snd_preimage Λ y.1 y.2 hB]

/-- The expected next rung from `(i, w)`: `m(i, w) = Σ_{k ≤ i} (i + 1 − k) Λₖ(w, X)`. -/
theorem lintegral_fst_ladderKernel (Λ : ℕ → Kernel ℝ ℝ) (i : ℕ) (w : ℝ) :
    ∫⁻ p, (p.1 : ℝ≥0∞) ∂avgLadderKernel Λ (i, w) =
      ∑' k : ℕ, ((if k ≤ i then i + 1 - k else 0 : ℕ) : ℝ≥0∞) * Λ k w univ := by
  have hf : Measurable fun p : ℕ × ℝ => (p.1 : ℝ≥0∞) := measurable_from_nat.comp measurable_fst
  have hmap : ∀ (κ : Kernel ℝ ℝ) (m : ℕ), ∫⁻ p, (p.1 : ℝ≥0∞) ∂(κ.map (Prod.mk m)) w =
      (m : ℝ≥0∞) * κ w univ := fun κ m => by
    rw [Kernel.map_apply _ measurable_prodMk_left, lintegral_map hf measurable_prodMk_left]
    change ∫⁻ _a, (m : ℝ≥0∞) ∂κ w = _
    rw [lintegral_const]
  rw [ladderChainKernel_apply, ladderRow, FunLike.coe_add, Pi.add_apply,
    lintegral_add_measure, hmap, Nat.cast_zero, zero_mul, zero_add, Kernel.sum_apply,
    lintegral_sum_measure, tsum_fintype]
  simp_rw [hmap]
  rw [Fin.sum_univ_eq_sum_range (fun k => ((i + 1 - k : ℕ) : ℝ≥0∞) * Λ k w univ),
    tsum_eq_sum (s := range (i + 1)) fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      simp [show ¬ k ≤ i by omega]]
  refine sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  simp [show k ≤ i by omega]

/-- `Σₖ Λₖ(w, X) = Λ(w, X)`. -/
theorem tsum_ladder_univ (Λ : ℕ → Kernel ℝ ℝ) (w : ℝ) :
    ∑' k, Λ k w univ = ladderMarg Λ w univ := by
  rw [ladderMarg, Kernel.sum_apply' _ _ MeasurableSet.univ]

/-- **The drift of `V(i, w) = i`** ((19.69) and the formula for `ΔV`, MT p. 503):
`m(i, w) + h_d(w) ≤ i + 1 + (d + 1) 1{i < d}`, where `m(i, w)` is the expected next rung. For
`i ≥ d` this is `ΔV(i, w) = 1 − h_i(w) ≤ 1 − h_d(w)`. -/
theorem meanRung_add_truncBeta_le (Λ : ℕ → Kernel ℝ ℝ) [IsMarkovKernel (ladderMarg Λ)]
    (i d : ℕ) (w : ℝ) :
    ∫⁻ p, (p.1 : ℝ≥0∞) ∂avgLadderKernel Λ (i, w) + truncBeta Λ d w ≤
      ((i + 1 + if i < d then d + 1 else 0 : ℕ) : ℝ≥0∞) := by
  rw [lintegral_fst_ladderKernel, truncBeta, ← ENNReal.tsum_add]
  calc ∑' k, (((if k ≤ i then i + 1 - k else 0 : ℕ) : ℝ≥0∞) * Λ k w univ +
        ((min k (d + 1) : ℕ) : ℝ≥0∞) * Λ k w univ)
      ≤ ∑' k, ((i + 1 + if i < d then d + 1 else 0 : ℕ) : ℝ≥0∞) * Λ k w univ := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [← add_mul]
        refine mul_le_mul' ?_ le_rfl
        rw [← Nat.cast_add]
        refine Nat.cast_le.2 ?_
        split_ifs <;> omega
    _ = ((i + 1 + if i < d then d + 1 else 0 : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_left, tsum_ladder_univ, measure_univ, mul_one]

/-- The truncated heights are measurable. -/
theorem measurable_truncBeta (Λ : ℕ → Kernel ℝ ℝ) (d : ℕ) : Measurable (truncBeta Λ d) :=
  Measurable.tsum fun _ => measurable_const.mul (Kernel.measurable_coe _ MeasurableSet.univ)

/-- `h_d ≤ d + 1`. -/
theorem truncBeta_le (Λ : ℕ → Kernel ℝ ℝ) [IsMarkovKernel (ladderMarg Λ)] (d : ℕ) (w : ℝ) :
    truncBeta Λ d w ≤ d + 1 := by
  calc truncBeta Λ d w ≤ ∑' k, ((d + 1 : ℕ) : ℝ≥0∞) * Λ k w univ :=
        ENNReal.tsum_le_tsum fun k => mul_le_mul' (Nat.cast_le.2 (min_le_right _ _)) le_rfl
    _ = d + 1 := by
        rw [ENNReal.tsum_mul_left, tsum_ladder_univ, measure_univ, mul_one]; push_cast; rfl

/-- **The summed drift** ((19.70), (19.74)): for `z = (i, x)`,
`E_z[V(Φₙ)] + Σ_{k<n} ∫ Λᵏ(x, dw) h_d(w) ≤ i + n + (d + 1) Σ_{k<n} Pᵏ(z, {rung < d})`. -/
theorem cesaro_truncBeta_bound (Λ : ℕ → Kernel ℝ ℝ) [IsMarkovKernel (ladderMarg Λ)] (d : ℕ)
    (z : ℕ × ℝ) (n : ℕ) :
    ∫⁻ p, (p.1 : ℝ≥0∞) ∂(avgLadderKernel Λ ^ n) z +
        ∑ k ∈ range n, ∫⁻ w, truncBeta Λ d w ∂(ladderMarg Λ ^ k) z.2 ≤
      z.1 + n + (d + 1) * ∑ k ∈ range n, (avgLadderKernel Λ ^ k) z {p | p.1 < d} := by
  have := isMarkovKernel_avgLadderKernel Λ
  have hf : Measurable fun p : ℕ × ℝ => (p.1 : ℝ≥0∞) := measurable_from_nat.comp measurable_fst
  have hlow : MeasurableSet {p : ℕ × ℝ | p.1 < d} := measurable_fst (measurableSet_Iio)
  induction n with
  | zero =>
    rw [pow_zero_apply, lintegral_dirac' z hf]
    simp
  | succ n ih =>
    have := isMarkovKernel_pow (avgLadderKernel Λ) n
    have hstep : ∫⁻ p, (p.1 : ℝ≥0∞) ∂(avgLadderKernel Λ ^ (n + 1)) z +
        ∫⁻ w, truncBeta Λ d w ∂(ladderMarg Λ ^ n) z.2 ≤
        ∫⁻ p, (p.1 : ℝ≥0∞) ∂(avgLadderKernel Λ ^ n) z + 1 +
          (d + 1) * (avgLadderKernel Λ ^ n) z {p | p.1 < d} := by
      rw [pow_add_eq, pow_one, Kernel.lintegral_comp _ _ _ hf, ← avgLadderKernel_pow_map_snd Λ n z,
        lintegral_map (measurable_truncBeta Λ d) measurable_snd,
        ← lintegral_add_left (Measurable.lintegral_kernel hf)]
      calc ∫⁻ y, (∫⁻ p, (p.1 : ℝ≥0∞) ∂avgLadderKernel Λ y + truncBeta Λ d y.2)
            ∂(avgLadderKernel Λ ^ n) z
          ≤ ∫⁻ y, ((y.1 : ℝ≥0∞) + 1 + {p : ℕ × ℝ | p.1 < d}.indicator (fun _ => (d + 1 : ℝ≥0∞))
              y) ∂(avgLadderKernel Λ ^ n) z := by
            refine lintegral_mono fun y => ?_
            have h := meanRung_add_truncBeta_le Λ y.1 d y.2
            rw [show (y.1, y.2) = y from rfl] at h
            refine h.trans (le_of_eq ?_)
            by_cases hy : y.1 < d
            · rw [indicator_of_mem (show y ∈ {p : ℕ × ℝ | p.1 < d} from hy)]
              simp only [hy, ↓reduceIte]
              push_cast; ring
            · rw [indicator_of_notMem (show y ∉ {p : ℕ × ℝ | p.1 < d} from hy)]
              simp only [hy, ↓reduceIte]
              push_cast; ring
        _ = ∫⁻ p, (p.1 : ℝ≥0∞) ∂(avgLadderKernel Λ ^ n) z + 1 +
              (d + 1) * (avgLadderKernel Λ ^ n) z {p | p.1 < d} := by
            rw [lintegral_add_right _ (measurable_const.indicator hlow),
              lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
              lintegral_indicator_const hlow]
    calc ∫⁻ p, (p.1 : ℝ≥0∞) ∂(avgLadderKernel Λ ^ (n + 1)) z +
          ∑ k ∈ range (n + 1), ∫⁻ w, truncBeta Λ d w ∂(ladderMarg Λ ^ k) z.2
        = (∫⁻ p, (p.1 : ℝ≥0∞) ∂(avgLadderKernel Λ ^ (n + 1)) z +
            ∫⁻ w, truncBeta Λ d w ∂(ladderMarg Λ ^ n) z.2) +
          ∑ k ∈ range n, ∫⁻ w, truncBeta Λ d w ∂(ladderMarg Λ ^ k) z.2 := by
          rw [sum_range_succ]; ring
      _ ≤ (∫⁻ p, (p.1 : ℝ≥0∞) ∂(avgLadderKernel Λ ^ n) z + 1 +
            (d + 1) * (avgLadderKernel Λ ^ n) z {p | p.1 < d}) +
          ∑ k ∈ range n, ∫⁻ w, truncBeta Λ d w ∂(ladderMarg Λ ^ k) z.2 := add_le_add hstep le_rfl
      _ = (∫⁻ p, (p.1 : ℝ≥0∞) ∂(avgLadderKernel Λ ^ n) z +
            ∑ k ∈ range n, ∫⁻ w, truncBeta Λ d w ∂(ladderMarg Λ ^ k) z.2) + 1 +
          (d + 1) * (avgLadderKernel Λ ^ n) z {p | p.1 < d} := by ring
      _ ≤ (z.1 + n + (d + 1) * ∑ k ∈ range n, (avgLadderKernel Λ ^ k) z {p | p.1 < d}) + 1 +
          (d + 1) * (avgLadderKernel Λ ^ n) z {p | p.1 < d} := by gcongr
      _ = z.1 + (n + 1 : ℕ) + (d + 1) * ∑ k ∈ range (n + 1),
            (avgLadderKernel Λ ^ k) z {p | p.1 < d} := by
          rw [sum_range_succ]; push_cast; ring

/-- `Pᵏ(z, ℤ₊ × B) = Λᵏ(z₂, B)`. -/
theorem avgLadderKernel_pow_snd_preimage (Λ : ℕ → Kernel ℝ ℝ) [IsMarkovKernel (ladderMarg Λ)]
    (k : ℕ) (z : ℕ × ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    (avgLadderKernel Λ ^ k) z (Prod.snd ⁻¹' B) = (ladderMarg Λ ^ k) z.2 B := by
  rw [← avgLadderKernel_pow_map_snd Λ k z, Measure.map_apply measurable_snd hB]

/-- **The rungs of a null ladder chain are null** ((19.75), MT p. 504): if the chain is null and
the Cesàro ergodic theorem holds for `Φ^Λ` at `x` (with limit `ν`), then the Cesàro averages of
`Pᵏ(i, x; {rung < d})` tend to `0`. The proof is the book's: Theorem 18.2.2 makes the sets of a
petite cover `C_M ↑ ℤ₊ × X` null, and the part of `{rung < d}` outside `C_M` lies over a set whose
`ν`-measure is small. -/
theorem tendsto_cesaro_low_of_isNull (Λ : ℕ → Kernel ℝ ℝ) [IsMarkovKernel (ladderMarg Λ)]
    [IsMarkovKernel (avgLadderKernel Λ)] {ψ : Measure (ℕ × ℝ)}
    (hψ : IsMaximalIrreducibility (avgLadderKernel Λ) ψ)
    (hnull : IsNull (avgLadderKernel Λ) ψ) {ν : Measure ℝ} [IsProbabilityMeasure ν] {x : ℝ}
    (hconv : ∀ g : ℝ → ℝ, Measurable g → ∀ K : ℝ, (∀ y, |g y| ≤ K) →
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ y, g y ∂(ladderMarg Λ ^ k) x) atTop
        (𝓝 (∫ y, g y ∂ν)))
    (i d : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n,
      ((avgLadderKernel Λ ^ k) (i, x) {p | p.1 < d}).toReal) atTop (𝓝 0) := by
  have hpowL : ∀ k, IsMarkovKernel (avgLadderKernel Λ ^ k) := isMarkovKernel_pow _
  have hpowM : ∀ k, IsMarkovKernel (ladderMarg Λ ^ k) := isMarkovKernel_pow _
  obtain ⟨c, ψc, -, Cs, hmono, hpet, hcov⟩ := proposition_5_5_5_iii_cover _ hψ
  have hCm : ∀ M, MeasurableSet (Cs M) := fun M => (hpet M).1
  set S : ℕ → Set ℝ := fun M => {y | ∀ j < d, (j, y) ∈ Cs M} with hSdef
  have hSm : ∀ M, MeasurableSet (S M) := fun M => by
    have : S M = ⋂ j ∈ Finset.range d, (fun y : ℝ => (j, y)) ⁻¹' Cs M := by
      ext y; simp [hSdef]
    rw [this]
    exact Finset.measurableSet_biInter _ fun j _ => measurable_prodMk_left (hCm M)
  have hSanti : Antitone fun M => (S M)ᶜ := fun M M' hMM' y hy hy' =>
    hy fun j hj => hmono hMM' (hy' j hj)
  have hScov : ⋂ M, (S M)ᶜ = ∅ := by
    ext y
    simp only [mem_iInter, mem_compl_iff, mem_empty_iff_false, iff_false, not_forall, not_not]
    have hj : ∀ j : ℕ, ∃ M, (j, y) ∈ Cs M := fun j => by
      have : (j, y) ∈ ⋃ M, Cs M := hcov ▸ mem_univ _
      exact mem_iUnion.1 this
    choose Mf hMf using hj
    exact ⟨(Finset.range d).sup Mf, fun j hj => hmono (Finset.le_sup (Finset.mem_range.2 hj))
      (hMf j)⟩
  have hνS : Tendsto (fun M => ν.real (S M)ᶜ) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := ν) (fun M => (hSm M).compl.nullMeasurableSet)
      hSanti ⟨0, measure_ne_top _ _⟩
    rw [hScov, measure_empty] at h
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at this
    exact this
  have hsub : ∀ M k, (avgLadderKernel Λ ^ k) (i, x) {p | p.1 < d} ≤
      (avgLadderKernel Λ ^ k) (i, x) (Cs M) + (ladderMarg Λ ^ k) x (S M)ᶜ := fun M k => by
    rw [← avgLadderKernel_pow_snd_preimage Λ k (i, x) (hSm M).compl]
    refine (measure_mono fun p hp => ?_).trans (measure_union_le _ _)
    by_cases hpC : p ∈ Cs M
    · exact Or.inl hpC
    · refine Or.inr fun hpS => hpC ?_
      exact hpS p.1 hp
  -- the three Cesàro averages
  set cav : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * ∑ k ∈ range n,
    ((avgLadderKernel Λ ^ k) (i, x) {p | p.1 < d}).toReal with hcav
  have hc0 : ∀ n, 0 ≤ cav n := fun n => mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))
    (sum_nonneg fun k _ => ENNReal.toReal_nonneg)
  have ha : ∀ M, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n,
      ((avgLadderKernel Λ ^ k) (i, x) (Cs M)).toReal) atTop (𝓝 0) := fun M => by
    have h := hnull.tendsto_pow_of_isPetite ⟨c, _, hpet M⟩ (i, x)
    have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h'
    exact h'.cesaro
  have hb : ∀ M, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n,
      ((ladderMarg Λ ^ k) x (S M)ᶜ).toReal) atTop (𝓝 (ν.real (S M)ᶜ)) := fun M => by
    have h := hconv ((S M)ᶜ.indicator 1) (measurable_one.indicator (hSm M).compl) 1
      (fun y => by
        by_cases hy : y ∈ (S M)ᶜ
        · simp [indicator_of_mem hy]
        · simp [indicator_of_notMem hy])
    rw [integral_indicator_one (hSm M).compl] at h
    refine h.congr fun n => ?_
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [integral_indicator_one (hSm M).compl]
    rfl
  have hle : ∀ M n, cav n ≤ (n : ℝ)⁻¹ * ∑ k ∈ range n,
      ((avgLadderKernel Λ ^ k) (i, x) (Cs M)).toReal +
      (n : ℝ)⁻¹ * ∑ k ∈ range n, ((ladderMarg Λ ^ k) x (S M)ᶜ).toReal := fun M n => by
    rw [hcav, ← mul_add, ← sum_add_distrib]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => ?_) (inv_nonneg.2 (Nat.cast_nonneg n))
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
      (hsub M k)
  refine tendsto_order.2 ⟨fun a ha0 => Eventually.of_forall fun n => lt_of_lt_of_le ha0 (hc0 n),
    fun ε hε => ?_⟩
  obtain ⟨M, hM⟩ := ((hνS.eventually (gt_mem_nhds (half_pos hε))).exists)
  have h1 := (ha M).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))
  have h2 := (hb M).eventually
    (gt_mem_nhds (by linarith : ν.real (S M)ᶜ < ν.real (S M)ᶜ + ε / 4))
  filter_upwards [h1, h2] with n hn1 hn2
  linarith [hle M n]

/-- **`Φ^Λ` is irreducible** (MT p. 502): if the ladder chain is `ψ`-irreducible, `Λ` is
`ψ*`-irreducible with `ψ*(B) = ψ(ℤ₊ × B)`. -/
theorem ladderMarg_isPhiIrreducible (Λ : ℕ → Kernel ℝ ℝ) [IsMarkovKernel (ladderMarg Λ)]
    {ψ : Measure (ℕ × ℝ)} (hψ : haveI := isMarkovKernel_avgLadderKernel Λ
      IsPhiIrreducible (avgLadderKernel Λ) ψ) :
    IsPhiIrreducible (ladderMarg Λ) (ψ.map Prod.snd) := by
  have := isMarkovKernel_avgLadderKernel Λ
  intro B hB hpos x
  rw [Measure.map_apply measurable_snd hB] at hpos
  obtain ⟨n, hn⟩ := (hitProb_pos_iff _ (measurable_snd hB) ((0 : ℕ), x)).1
    (hψ _ (measurable_snd hB) hpos ((0 : ℕ), x))
  refine (hitProb_pos_iff _ hB x).2 ⟨n, ?_⟩
  rwa [← avgLadderKernel_pow_snd_preimage Λ (n + 1) ((0 : ℕ), x) hB]

/-- **Theorem 19.3.4** (MT p. 503): if the ladder chain is `ψ`-irreducible and has the structure
(19.65), and the marginal chain `Φ^Λ` admits an invariant probability `ν` with
`∫ ν(dw) β(w) > 1` (19.68), then the ladder chain is positive: it admits an invariant
probability measure. -/
theorem theorem_19_3_4 (Λ : ℕ → Kernel ℝ ℝ) [IsMarkovKernel (ladderMarg Λ)]
    {ψ : Measure (ℕ × ℝ)}
    (hψ : haveI := isMarkovKernel_avgLadderKernel Λ; IsMaximalIrreducibility (avgLadderKernel Λ) ψ)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : IsInvariant (ladderMarg Λ) ν)
    (h68 : 1 < ∫⁻ w, ladderBeta Λ w ∂ν) :
    haveI := isMarkovKernel_avgLadderKernel Λ
    IsPositive (avgLadderKernel Λ) ψ := by
  have := isMarkovKernel_avgLadderKernel Λ
  have hpowL : ∀ k, IsMarkovKernel (avgLadderKernel Λ ^ k) := isMarkovKernel_pow _
  have hpowM : ∀ k, IsMarkovKernel (ladderMarg Λ ^ k) := isMarkovKernel_pow _
  -- the marginal chain is positive
  have hirr := ladderMarg_isPhiIrreducible Λ hψ.2.1
  have hne : ψ.map Prod.snd ≠ 0 := fun h => by
    have := congrArg (fun μ : Measure ℝ => μ univ) h
    simp only [Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ,
      Measure.coe_zero, Pi.zero_apply] at this
    exact hψ.1 (Measure.measure_univ_eq_zero.1 this)
  have hψ' := isMaximalIrreducibility_maxIrrMeasure _ hirr hne
  have hposΛ : IsPositive (ladderMarg Λ) (maxIrrMeasure (ladderMarg Λ) (ψ.map Prod.snd)) :=
    ⟨hψ', ν, inferInstance, hν⟩
  obtain ⟨N, -, hψN, hconv⟩ := tendsto_cesaro_integral_of_isPositive hψ' hposΛ hν
  obtain ⟨x, hx⟩ : ∃ x, x ∉ N := by
    by_contra h
    push Not at h
    rw [eq_univ_of_forall h] at hψN
    exact hψ'.1 (Measure.measure_univ_eq_zero.1 hψN)
  by_contra hnp
  have hnull := (isPositive_or_isNull hψ).resolve_left hnp
  -- for every `d`, `∫ ν h_d ≤ 1`
  have hd : ∀ d : ℕ, ∫⁻ w, truncBeta Λ d w ∂ν ≤ 1 := by
    intro d
    have hfin : ∀ w, truncBeta Λ d w ≠ ∞ := fun w =>
      ne_top_of_le_ne_top (by simp) (truncBeta_le Λ d w)
    set g : ℝ → ℝ := fun w => (truncBeta Λ d w).toReal with hg
    have hgm : Measurable g := (measurable_truncBeta Λ d).ennreal_toReal
    have hgb : ∀ w, |g w| ≤ d + 1 := fun w => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      have := ENNReal.toReal_mono (by simp) (truncBeta_le Λ d w)
      rwa [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast,
        ENNReal.toReal_one] at this
    have hint : ∀ (μ : Measure ℝ), ∫ w, g w ∂μ = (∫⁻ w, truncBeta Λ d w ∂μ).toReal := fun μ =>
      integral_toReal (measurable_truncBeta Λ d).aemeasurable
        (Eventually.of_forall fun w => (hfin w).lt_top)
    have hlim1 := hconv x hx g hgm (d + 1) hgb
    have hlim2 := (tendsto_cesaro_low_of_isNull Λ hψ hnull (hconv x hx) 0 d).const_mul ((d : ℝ) + 1)
    rw [mul_zero] at hlim2
    have hlim3 : Tendsto (fun n : ℕ => (1 : ℝ) + ((d : ℝ) + 1) * ((n : ℝ)⁻¹ * ∑ k ∈ range n,
        ((avgLadderKernel Λ ^ k) ((0 : ℕ), x) {p | p.1 < d}).toReal)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hlim2
    rw [add_zero] at hlim3
    have hbound : ∀ n : ℕ, 0 < n → (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ w, g w ∂(ladderMarg Λ ^ k) x ≤
        1 + ((d : ℝ) + 1) * ((n : ℝ)⁻¹ * ∑ k ∈ range n,
          ((avgLadderKernel Λ ^ k) ((0 : ℕ), x) {p | p.1 < d}).toReal) := fun n hn => by
      have hB := cesaro_truncBeta_bound Λ d ((0 : ℕ), x) n
      have hB' : ∑ k ∈ range n, ∫⁻ w, truncBeta Λ d w ∂(ladderMarg Λ ^ k) x ≤
          (n : ℝ≥0∞) + (d + 1) *
            ∑ k ∈ range n, (avgLadderKernel Λ ^ k) ((0 : ℕ), x) {p | p.1 < d} := by
        refine le_trans le_add_self (hB.trans (le_of_eq ?_))
        simp
      have hfinS : ∀ k, ∫⁻ w, truncBeta Λ d w ∂(ladderMarg Λ ^ k) x ≠ ∞ := fun k =>
        ne_top_of_le_ne_top (b := ((d : ℝ≥0∞) + 1)) (by simp) (by
          calc ∫⁻ w, truncBeta Λ d w ∂(ladderMarg Λ ^ k) x
              ≤ ∫⁻ _w, ((d : ℝ≥0∞) + 1) ∂(ladderMarg Λ ^ k) x := lintegral_mono (truncBeta_le Λ d)
            _ = (d : ℝ≥0∞) + 1 := by rw [lintegral_const, measure_univ, mul_one])
      have hreal := ENNReal.toReal_mono (by
        refine ENNReal.add_ne_top.2 ⟨by simp, ENNReal.mul_ne_top (by simp)
          (ENNReal.sum_ne_top.2 fun k _ => measure_ne_top _ _)⟩) hB'
      rw [ENNReal.toReal_sum fun k _ => hfinS k, ENNReal.toReal_add (by simp)
        (ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 fun k _ => measure_ne_top _ _)),
        ENNReal.toReal_mul, ENNReal.toReal_sum fun k _ => measure_ne_top _ _] at hreal
      simp only [ENNReal.toReal_natCast, ENNReal.toReal_add (ENNReal.natCast_ne_top d)
        ENNReal.one_ne_top, ENNReal.toReal_one] at hreal
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      simp_rw [hint]
      rw [inv_mul_le_iff₀ hn']
      have e : (n : ℝ) * (1 + ((d : ℝ) + 1) * ((n : ℝ)⁻¹ * ∑ k ∈ range n,
          ((avgLadderKernel Λ ^ k) ((0 : ℕ), x) {p | p.1 < d}).toReal)) = n + ((d : ℝ) + 1) *
          ∑ k ∈ range n, ((avgLadderKernel Λ ^ k) ((0 : ℕ), x) {p | p.1 < d}).toReal := by
        field_simp
      rw [e]
      exact hreal
    have hle : ∫ w, g w ∂ν ≤ 1 :=
      le_of_tendsto_of_tendsto' hlim1 hlim3 fun n => by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; simp
        · exact hbound n h0
    rw [hint] at hle
    have hfinν : ∫⁻ w, truncBeta Λ d w ∂ν ≠ ∞ := ne_top_of_le_ne_top (b := ((d : ℝ≥0∞) + 1))
      (by simp) (by
        calc ∫⁻ w, truncBeta Λ d w ∂ν ≤ ∫⁻ _w, ((d : ℝ≥0∞) + 1) ∂ν :=
              lintegral_mono (truncBeta_le Λ d)
          _ = (d : ℝ≥0∞) + 1 := by rw [lintegral_const, measure_univ, mul_one])
    rw [← ENNReal.ofReal_toReal hfinν, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hle
  -- hence `∫ ν β ≤ 1`
  set a : ℕ → ℝ≥0∞ := fun k => ∫⁻ w, Λ k w univ ∂ν with ha
  have hmk : ∀ k, Measurable fun w => Λ k w univ := fun k =>
    Kernel.measurable_coe _ MeasurableSet.univ
  have hβ : ∫⁻ w, ladderBeta Λ w ∂ν = ∑' k : ℕ, (k : ℝ≥0∞) * a k := by
    simp only [ladderBeta]
    rw [lintegral_tsum (f := fun (k : ℕ) (w : ℝ) => (k : ℝ≥0∞) * Λ k w univ)
      fun k => (measurable_const.mul (hmk k)).aemeasurable]
    exact tsum_congr fun k => lintegral_const_mul _ (hmk k)
  have htb : ∀ d, ∫⁻ w, truncBeta Λ d w ∂ν = ∑' k : ℕ, ((min k (d + 1) : ℕ) : ℝ≥0∞) * a k :=
      fun d => by
    simp only [truncBeta]
    rw [lintegral_tsum (f := fun (k : ℕ) (w : ℝ) => ((min k (d + 1) : ℕ) : ℝ≥0∞) * Λ k w univ)
      fun k => (measurable_const.mul (hmk k)).aemeasurable]
    exact tsum_congr fun k => lintegral_const_mul _ (hmk k)
  have hle : ∫⁻ w, ladderBeta Λ w ∂ν ≤ 1 := by
    rw [hβ]
    refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    calc ∑ k ∈ range N, (k : ℝ≥0∞) * a k = ∑ k ∈ range N, ((min k (N + 1) : ℕ) : ℝ≥0∞) * a k := by
          refine sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          rw [min_eq_left (by omega)]
      _ ≤ ∑' k, ((min k (N + 1) : ℕ) : ℝ≥0∞) * a k := ENNReal.sum_le_tsum _
      _ = ∫⁻ w, truncBeta Λ N w ∂ν := (htb N).symm
      _ ≤ 1 := hd N
  exact absurd h68 (not_lt.2 hle)

end MeynTweedie.GeneralizedDrift

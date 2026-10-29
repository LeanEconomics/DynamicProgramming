/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeometricErgodicity.LadderInvariant
import GeometricErgodicity.ModelInvariant

/-!
# The minimal invariant measure of the GI/M/1 queue (MT §10.3.3), and loose ends of §10.3, §10.5

Meyn and Tweedie, pp. 237–241, 248.

**GI/M/1** (`gim1Kernel p`, `QueueInvariant`), with the atom `α = {0}` and its minimal measure
`μ°_α = atomMeasure` of Theorem 10.2.1. The GI/M/1 chain is the ladder chain of §10.5.3 with
one-point rungs: `gim1LadderKernel p` has `Λₖ(x, ·) = p(k) δ₀`, and
`gim1Ladder_eq_map` shows that it moves exactly as the GI/M/1 chain embedded by `i ↦ (i, 0)`.
* `tabooKernel_map_of_comp`, `tabooPotKernel_map_of_comp`: taboo probabilities transfer along such
  an embedding.
* `gim1Alpha p = μ°_α(1)`, the book's `s_α`; `gim1_minimal_geom` (10.24):
  `μ°_α(k) = s_αᵏ` for `k ≥ 1`, the consequence of the last-exit decomposition (10.22) and the
  translation invariance (10.23) (here via `ladderS_eq_pow`).
* `gim1Alpha_root` (10.25): `s_α = Σⱼ p(j) s_αʲ`; `gim1Alpha_le_of_root`: `s_α ≤ s` for every
  `s ∈ [0, ∞]` with `Σⱼ p(j) sʲ ≤ s` (minimality, from `ladS_minimal`); hence
  `gim1Alpha_le_one` and `gim1Alpha_pos` (`p(0) > 0`): `s_α` is the minimal root in `(0, 1]`.
* `gim1Alpha_lt_one_of_mean`: `Σⱼ j p(j) > 1` forces `s_α < 1`;
  `gim1Alpha_eq_one_of_mean_le` (p. 240): for a `ψ`-irreducible chain with `p(0) > 0`,
  `Σⱼ j p(j) ≤ 1` forces `s_α = 1`.
* **Proposition 10.3.2, the recurrent case** (`proposition_10_3_2_mean_one`, p. 241): if
  `Σⱼ j p(j) = 1` (and `p(0) > 0`, `{0}` accessible), the chain is recurrent, its minimal invariant
  measure is `μ ≡ 1`, and every subinvariant measure is a multiple of `μ ≡ 1`.

**Forward recurrence time chain** (p. 237).
* `fwdRec_tabooKernel` : the taboo formula `₁Pⁿ(1, j) = p(j + n − 1)` (in the shifted indexing
  of `ForwardRecurrence`: `_0Pᵐ⁺¹(0, j) = p(j + m + 1)`), for every `j`.
  **Correction:** the book restricts it to `j ≤ n`, "zero otherwise"; the formula holds for all
  `j`, and the restriction is false: `fwdRec_tabooKernel_counterexample` (`p = δ₂`, `n = 1`,
  `j = 2` in the book's indexing).

**M/G/1** (p. 238). `mg1_invariant_unique`: the invariant equations determine an invariant
measure, finite on points, from its value at `0`, whether the chain is transient or recurrent;
`mg1_invariant_unique_smul`: invariant measures are unique up to constant multiples.

**Random walk** (p. 248). `randomWalk_null_recurrent`: a `ψ`-irreducible random walk on `ℝ` with
spread-out increments of mean zero and finite variance is null recurrent.
-/

namespace MeynTweedie.GeometricErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Taboo probabilities along an embedding -/

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- If `P'(f x) = P(x) ∘ f⁻¹` and `f⁻¹ A' = A`, then `_{A'}P'ⁿ(f x, ·) = _APⁿ(x, ·) ∘ f⁻¹`. -/
theorem tabooKernel_map_of_comp (P : Kernel X X) (P' : Kernel Y Y) {f : X → Y}
    (hf : Measurable f) (hP : ∀ x, P' (f x) = (P x).map f) {A : Set X} {A' : Set Y}
    (hA : MeasurableSet A) (hA' : MeasurableSet A') (hpre : f ⁻¹' A' = A) (n : ℕ) (x : X) :
    tabooKernel P' hA' n (f x) = (tabooKernel P hA n x).map f := by
  induction n generalizing x with
  | zero => rw [tabooKernel_zero, tabooKernel_zero, hP]
  | succ n ih =>
    ext B hB
    rw [tabooKernel_succ_eq', tabooKernel_succ_eq', Measure.map_apply hf hB, Kernel.comp_apply',
      Kernel.comp_apply' _ _ _ (hf hB), comp_indKernel_eq_restrict, comp_indKernel_eq_restrict,
      hP, Measure.restrict_map hf hA'.compl, preimage_compl, hpre,
      lintegral_map (Kernel.measurable_coe _ hB) hf]
    · refine lintegral_congr fun y => ?_
      rw [ih, Measure.map_apply hf hB]
    · exact hB

/-- The same for `U_A`. -/
theorem tabooPotKernel_map_of_comp (P : Kernel X X) (P' : Kernel Y Y) {f : X → Y}
    (hf : Measurable f) (hP : ∀ x, P' (f x) = (P x).map f) {A : Set X} {A' : Set Y}
    (hA : MeasurableSet A) (hA' : MeasurableSet A') (hpre : f ⁻¹' A' = A) (x : X) :
    tabooPotKernel P' hA' (f x) = (tabooPotKernel P hA x).map f := by
  ext B hB
  rw [tabooPotKernel, Kernel.sum_apply' _ _ hB, Measure.map_apply hf hB, tabooPotKernel,
    Kernel.sum_apply' _ _ (hf hB)]
  refine tsum_congr fun n => ?_
  rw [tabooKernel_map_of_comp P P' hf hP hA hA' hpre n x, Measure.map_apply hf hB]

/-- Points with the same transition law have the same taboo probabilities. -/
theorem tabooKernel_eq_of_eq (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) {z z' : X}
    (h : P z = P z') (n : ℕ) : tabooKernel P hA n z = tabooKernel P hA n z' := by
  cases n with
  | zero => rw [tabooKernel_zero, h]
  | succ n =>
    simp only [tabooKernel_succ_eq', Kernel.comp_apply, h]

/-! ### The GI/M/1 chain as a ladder chain -/

/-- The rung kernels of the GI/M/1 chain seen as a ladder chain: `Λₖ(x, ·) = p(k) δ₀`. -/
noncomputable def gim1Lam (p : ℕ → ℝ≥0∞) (k : ℕ) : Kernel ℝ ℝ :=
  Kernel.const ℝ (p k • Measure.dirac 0)

/-- The bottom kernels: `Λ*ᵢ(x, ·) = (Σ_{k > i} p(k)) δ₀`. -/
noncomputable def gim1LamStar (p : ℕ → ℝ≥0∞) (i : ℕ) : Kernel ℝ ℝ :=
  Kernel.const ℝ ((∑' k, (Ioi i).indicator p k) • Measure.dirac 0)

/-- The GI/M/1 chain as a ladder chain with one-point rungs. -/
noncomputable abbrev gim1LadderKernel (p : ℕ → ℝ≥0∞) : Kernel (ℕ × ℝ) (ℕ × ℝ) :=
  ladderChainKernel (gim1Lam p) (gim1LamStar p)

/-- The embedding `i ↦ (i, 0)`. -/
def rungEmb (i : ℕ) : ℕ × ℝ := (i, 0)

/-- The embedding is measurable. -/
theorem measurable_rungEmb : Measurable rungEmb := measurable_id.prodMk measurable_const

/-- `(P(i, ·) ∘ e⁻¹)(j × A) = δ₀(A) P(i, j)`. -/
theorem gim1_map_rungEmb_apply (p : ℕ → ℝ≥0∞) (i j : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    (gim1Kernel p i).map rungEmb ({j} ×ˢ A) = Measure.dirac (0 : ℝ) A * gim1Matrix p i j := by
  rw [Measure.map_apply measurable_rungEmb ((measurableSet_singleton j).prod hA),
    Measure.dirac_apply' _ hA]
  by_cases h0 : (0 : ℝ) ∈ A
  · have : rungEmb ⁻¹' ({j} ×ˢ A) = {j} := by ext k; simp [rungEmb, h0]
    rw [this, gim1Kernel, matKernel_singleton, indicator_of_mem h0, Pi.one_apply, one_mul]
  · have : rungEmb ⁻¹' ({j} ×ˢ A) = ∅ := by ext k; simp [rungEmb, h0]
    rw [this, measure_empty, indicator_of_notMem h0, zero_mul]

/-- The ladder version moves as the GI/M/1 chain: `P'(i, x; ·) = P(i, ·) ∘ e⁻¹` for every `x`. -/
theorem gim1Ladder_eq_map (p : ℕ → ℝ≥0∞) (z : ℕ × ℝ) :
    gim1LadderKernel p z = (gim1Kernel p z.1).map rungEmb := by
  obtain ⟨i, x⟩ := z
  refine ext_nat_prod fun j A hA => ?_
  rw [gim1_map_rungEmb_apply p i j hA]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [eq_3_40_zero _ _ i x hA, gim1LamStar, Kernel.const_apply, Measure.smul_apply, smul_eq_mul,
      mul_comm]
    simp [gim1Matrix]
  · by_cases hji : j ≤ i + 1
    · rw [eq_3_40_mid _ _ hj hji x hA, gim1Lam, Kernel.const_apply, Measure.smul_apply,
        smul_eq_mul, mul_comm]
      simp [gim1Matrix, show j ≠ 0 by omega, hji]
    · rw [eq_3_40_up _ _ (by omega) x hA]
      simp [gim1Matrix, show j ≠ 0 by omega, hji]

/-- `e⁻¹([0]) = {0}`. -/
theorem rungEmb_preimage_rung_zero : rungEmb ⁻¹' rung 0 = {0} := by
  ext k; simp [rungEmb, rung]

/-- `U'_{[0]}(e(i), ·) = U_{0}(i, ·) ∘ e⁻¹`. -/
theorem gim1_tabooPot_map (p : ℕ → ℝ≥0∞) (i : ℕ) :
    tabooPotKernel (gim1LadderKernel p) (measurableSet_rung 0) (rungEmb i) =
      (tabooPotKernel (gim1Kernel p) (measurableSet_singleton 0) i).map rungEmb :=
  tabooPotKernel_map_of_comp _ _ measurable_rungEmb (fun i => gim1Ladder_eq_map p (i, 0))
    (measurableSet_singleton 0) (measurableSet_rung 0) rungEmb_preimage_rung_zero i

/-- The book's `s_α = μ°_α(1)`, the mean number of visits to `1` before the return to `0`. -/
noncomputable def gim1Alpha (p : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  atomMeasure (gim1Kernel p) (measurableSet_singleton 0) 0 {1}

/-- `μ°_α(k) = U'_{[0]}(0, 0; k × {0})`. -/
theorem atomMeasure_gim1_eq (p : ℕ → ℝ≥0∞) (k : ℕ) :
    atomMeasure (gim1Kernel p) (measurableSet_singleton 0) 0 {k} =
      tabooPotKernel (gim1LadderKernel p) (measurableSet_rung 0) (0, 0) ({k} ×ˢ {(0 : ℝ)}) := by
  rw [show ((0 : ℕ), (0 : ℝ)) = rungEmb 0 from rfl, gim1_tabooPot_map, Measure.map_apply
    measurable_rungEmb ((measurableSet_singleton k).prod (measurableSet_singleton 0))]
  congr 1
  ext j; simp [rungEmb]

/-- `S(y, ·) = s_α δ₀` for every `y`. -/
theorem gim1_ladS (p : ℕ → ℝ≥0∞) (y : ℝ) :
    ladS (gim1Lam p) (gim1LamStar p) y = gim1Alpha p • Measure.dirac 0 := by
  ext B hB
  have hP : gim1LadderKernel p (0, y) = gim1LadderKernel p (0, 0) := by
    rw [gim1Ladder_eq_map, gim1Ladder_eq_map]
  have hU : tabooPotKernel (gim1LadderKernel p) (measurableSet_rung 0) (0, y) =
      tabooPotKernel (gim1LadderKernel p) (measurableSet_rung 0) (0, 0) := by
    rw [tabooPotKernel, Kernel.sum_apply, Kernel.sum_apply]
    congr 1
    funext n
    exact tabooKernel_eq_of_eq _ _ hP n
  rw [ladderS_apply _ _ 1 y hB, hU, show ((0 : ℕ), (0 : ℝ)) = rungEmb 0 from rfl,
    gim1_tabooPot_map, Measure.map_apply measurable_rungEmb
      ((measurableSet_singleton 1).prod hB), Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hB, gim1Alpha, atomMeasure]
  by_cases h0 : (0 : ℝ) ∈ B
  · have : rungEmb ⁻¹' ({1} ×ˢ B) = {1} := by ext k; simp [rungEmb, h0]
    rw [this, indicator_of_mem h0, Pi.one_apply, mul_one]
  · have : rungEmb ⁻¹' ({1} ×ˢ B) = ∅ := by ext k; simp [rungEmb, h0]
    rw [this, measure_empty, indicator_of_notMem h0, mul_zero]

/-- `Sᵏ(0, ·) = s_αᵏ δ₀`. -/
theorem gim1_ladS_pow (p : ℕ → ℝ≥0∞) (k : ℕ) :
    (ladS (gim1Lam p) (gim1LamStar p) ^ k) 0 = gim1Alpha p ^ k • Measure.dirac 0 := by
  induction k with
  | zero => rw [pow_zero_apply, pow_zero, one_smul]
  | succ k ih =>
    rw [pow_succ']
    change (ladS (gim1Lam p) (gim1LamStar p) ∘ₖ (ladS (gim1Lam p) (gim1LamStar p) ^ k)) 0 = _
    ext B hB
    rw [Kernel.comp_apply' _ _ _ hB, ih, lintegral_smul_measure, lintegral_dirac,
      gim1_ladS, Measure.smul_apply, Measure.smul_apply]
    simp only [smul_eq_mul]
    ring

/-- **(10.24)** (MT p. 240): `μ°_α(k) = s_αᵏ` for `k ≥ 1`. -/
theorem gim1_minimal_geom (p : ℕ → ℝ≥0∞) {k : ℕ} (hk : 1 ≤ k) :
    atomMeasure (gim1Kernel p) (measurableSet_singleton 0) 0 {k} = gim1Alpha p ^ k := by
  rw [atomMeasure_gim1_eq, ← ladderS_apply _ _ k 0 (measurableSet_singleton 0),
    ladderS_eq_pow _ _ hk, gim1_ladS_pow, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_singleton 0), mul_one]

/-- `Sᵏ(0, ℝ) = s_αᵏ`, and the same for the constant kernel `s δ₀`. -/
theorem const_pow_univ (s : ℝ≥0∞) (k : ℕ) (y : ℝ) :
    ((Kernel.const ℝ (s • Measure.dirac (0 : ℝ))) ^ k) y univ = s ^ k := by
  induction k generalizing y with
  | zero => rw [pow_zero_apply, pow_zero, measure_univ]
  | succ k ih =>
    rw [pow_succ_apply' _ k y MeasurableSet.univ]
    simp_rw [Kernel.const_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [lintegral_const, ih, pow_succ, mul_comm]

/-- **(10.25)** (MT p. 240): `s_α = Σⱼ p(j) s_αʲ`. -/
theorem gim1Alpha_root (p : ℕ → ℝ≥0∞) : gim1Gen p (gim1Alpha p) = gim1Alpha p := by
  have h := congrArg (fun κ : Kernel ℝ ℝ => κ 0 {0}) (ladS_eq (gim1Lam p) (gim1LamStar p))
  rw [gim1_ladS, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_singleton 0),
    mul_one, Kernel.sum_apply' _ _ (measurableSet_singleton 0)] at h
  rw [gim1Gen]
  conv_rhs => rw [h]
  refine tsum_congr fun k => ?_
  rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton 0)]
  simp_rw [gim1Lam, Kernel.const_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_singleton (0 : ℝ)), mul_one]
  rw [lintegral_const, gim1_ladS_pow, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]

/-- Minimality (MT p. 240): `s_α ≤ s` for every `s ∈ [0, ∞]` with `Σⱼ p(j) sʲ ≤ s`. -/
theorem gim1Alpha_le_of_root (p : ℕ → ℝ≥0∞) {s : ℝ≥0∞} (hs : gim1Gen p s ≤ s) :
    gim1Alpha p ≤ s := by
  set Sstar := Kernel.const ℝ (s • Measure.dirac (0 : ℝ))
  have hsup : ∀ y B, MeasurableSet B →
      (Kernel.sum fun k => gim1Lam p k ∘ₖ (Sstar ^ k)) y B ≤ Sstar y B := by
    intro y B hB
    rw [Kernel.sum_apply' _ _ hB]
    have e : ∀ k, (gim1Lam p k ∘ₖ (Sstar ^ k)) y B =
        p k * s ^ k * Measure.dirac (0 : ℝ) B := fun k => by
      rw [Kernel.comp_apply' _ _ _ hB]
      simp_rw [gim1Lam, Kernel.const_apply, Measure.smul_apply, smul_eq_mul]
      rw [lintegral_const, const_pow_univ]
      ring
    simp_rw [e]
    rw [ENNReal.tsum_mul_right, Kernel.const_apply, Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' hs le_rfl
  have := ladS_minimal (gim1Lam p) (gim1LamStar p) Sstar hsup 0 {0} (measurableSet_singleton 0)
  rwa [gim1_ladS, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_singleton 0),
    mul_one, Kernel.const_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_singleton 0), mul_one] at this

/-- `s_α ≤ 1`, since `1` solves (10.25). -/
theorem gim1Alpha_le_one {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) : gim1Alpha p ≤ 1 :=
  gim1Alpha_le_of_root p (by simp [gim1Gen, hp])

/-- `s_α ≥ p(0) > 0`. -/
theorem gim1Alpha_pos {p : ℕ → ℝ≥0∞} (hp0 : 0 < p 0) : 0 < gim1Alpha p := by
  refine lt_of_lt_of_le hp0 ?_
  rw [gim1Alpha, atomMeasure, tabooPotKernel, Kernel.sum_apply' _ _ (measurableSet_singleton 1)]
  refine le_trans ?_ (ENNReal.le_tsum 0)
  rw [tabooKernel_zero, gim1Kernel, matKernel_singleton]
  simp [gim1Matrix]

/-- If `Σⱼ j p(j) > 1` then `s_α < 1`. -/
theorem gim1Alpha_lt_one_of_mean {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) (hp0 : 0 < p 0)
    (hmean : 1 < ∑' j : ℕ, (j : ℝ≥0∞) * p j) : gim1Alpha p < 1 := by
  obtain ⟨s, -, hs1, hroot⟩ := exists_gim1_root hp hp0 hmean
  exact lt_of_le_of_lt (gim1Alpha_le_of_root p hroot.le) hs1

/-- (MT p. 240) For a `ψ`-irreducible chain with `p(0) > 0`, if `Σⱼ j p(j) ≤ 1` then `s_α = 1`. -/
theorem gim1Alpha_eq_one_of_mean_le {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) (hp0 : 0 < p 0)
    {ψ : Measure ℕ}
    (hψ : haveI := isMarkovKernel_matKernel (isTransitionMatrix_gim1 hp);
      IsMaximalIrreducibility (gim1Kernel p) ψ)
    (hmean : ∑' j : ℕ, (j : ℝ≥0∞) * p j ≤ 1) : gim1Alpha p = 1 := by
  refine le_antisymm (gim1Alpha_le_one hp) (not_lt.1 fun hlt => ?_)
  have := isMarkovKernel_matKernel (isTransitionMatrix_gim1 hp)
  have hinv := isInvariant_gim1_geom hp hlt (gim1Alpha_root p)
  set μ := pointMeasure fun k => gim1Alpha p ^ k
  have hμu : μ univ = (1 - gim1Alpha p)⁻¹ := by rw [pointMeasure_univ, ENNReal.tsum_geometric]
  have hμfin : μ univ ≠ ∞ := by rw [hμu]; exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hlt).ne'
  have hμ0 : μ univ ≠ 0 := by rw [hμu]; simp
  have hpos : IsPositive (gim1Kernel p) ψ := ⟨hψ, (μ univ)⁻¹ • μ,
    ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hμ0 hμfin]⟩, hinv.smul _⟩
  exact absurd ((proposition_10_3_2 hp hp0 hψ).1 hpos) (not_lt.2 hmean)

/-- **Proposition 10.3.2, the recurrent case** (MT pp. 240–241): if `Σⱼ j p(j) = 1`, `p(0) > 0` and
`{0}` is an accessible atom, the chain is recurrent, its minimal invariant measure is `μ ≡ 1`, and
every subinvariant measure is a multiple of `μ ≡ 1`. -/
theorem proposition_10_3_2_mean_one {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) (hp0 : 0 < p 0)
    {ψ : Measure ℕ}
    (hat : haveI := isMarkovKernel_matKernel (isTransitionMatrix_gim1 hp);
      IsAccessibleAtom (gim1Kernel p) ψ {0})
    (hmean : ∑' j : ℕ, (j : ℝ≥0∞) * p j = 1) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_gim1 hp)
    IsRecurrentChain (gim1Kernel p) ψ ∧
      atomMeasure (gim1Kernel p) (measurableSet_singleton 0) 0 = pointMeasure (fun _ => 1) ∧
      ∀ μ, IsSubinvariantMeasure (gim1Kernel p) μ → μ = μ {0} • pointMeasure (fun _ => 1) := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_gim1 hp)
  have hs1 := gim1Alpha_eq_one_of_mean_le hp hp0 hat.2.1 hmean.le
  set M := atomMeasure (gim1Kernel p) (measurableSet_singleton 0) 0
  set L := hitProb (gim1Kernel p) {0} 0
  have hM0 : M {0} = L := atomMeasure_self _ _ 0
  have hMk : ∀ k, 1 ≤ k → M {k} = 1 := fun k hk => by
    rw [gim1_minimal_geom p hk, hs1, one_pow]
  have hMpt : M = pointMeasure fun i => M {i} :=
    Measure.ext_of_singleton fun i => (pointMeasure_singleton (fun i => M {i}) i).symm
  -- subinvariance in column `0` forces `L = 1`
  have hsub := (isSubinvariant_atomMeasure (isAtom_singleton (gim1Kernel p) 0)
    (mem_singleton 0))
  change IsSubinvariant (gim1Kernel p) M at hsub
  rw [hMpt, gim1Kernel, isSubinvariant_matKernel_pointMeasure_iff] at hsub
  have hc := hsub 0
  rw [tsum_eq_zero_add' ENNReal.summable, hM0] at hc
  simp_rw [hMk _ (Nat.succ_pos _), one_mul] at hc
  have hcol := gim1_col_zero_one p
  rw [hmean, tsum_eq_zero_add' ENNReal.summable] at hcol
  have hM00 : gim1Matrix p 0 0 + p 0 = 1 := by
    rw [← hp, tsum_eq_zero_add' ENNReal.summable (f := p), add_comm]
    congr 1
    simp only [gim1Matrix, ite_true]
    rw [tsum_indicator_Ioi]
  have hfin00 : gim1Matrix p 0 0 ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hM00 ▸ le_self_add)
  have htail : ∑' i, gim1Matrix p (i + 1) 0 = p 0 := by
    have h2 : gim1Matrix p 0 0 + ∑' i, gim1Matrix p (i + 1) 0 = gim1Matrix p 0 0 + p 0 := by
      rw [hcol, hM00]
    exact (ENNReal.add_right_inj hfin00).1 h2
  rw [htail] at hc
  have hLle : L ≤ 1 := hitProb_le_one _ _ _
  have hLfin : L ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hLle
  have hL1 : L = 1 := by
    refine le_antisymm hLle ?_
    have h3 : L * gim1Matrix p 0 0 + p 0 ≤ L * gim1Matrix p 0 0 + L * p 0 := by
      rw [← mul_add, hM00, mul_one]; exact hc
    have h4 := (ENNReal.add_le_add_iff_left (ENNReal.mul_ne_top hLfin hfin00)).1 h3
    have hp0fin : p 0 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hp ▸ ENNReal.le_tsum 0)
    calc 1 = p 0 / p 0 := (ENNReal.div_self hp0.ne' hp0fin).symm
      _ ≤ L * p 0 / p 0 := ENNReal.div_le_div_right h4 _
      _ = L := ENNReal.mul_div_cancel_right hp0.ne' hp0fin
  have hrec : IsRecurrentChain (gim1Kernel p) ψ :=
    (IsAccessibleAtom.isRecurrentChain_iff hat (mem_singleton 0)).2 hL1
  have hMone : M = pointMeasure fun _ => 1 := by
    refine Measure.ext_of_singleton fun i => ?_
    rw [pointMeasure_singleton]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hM0, hL1]
    · exact hMk i hi
  refine ⟨hrec, hMone, fun μ hμ => ?_⟩
  have := hμ.eq_smul_atomMeasure hat hrec (mem_singleton 0)
  calc μ = μ {0} • M := this
    _ = μ {0} • pointMeasure (fun _ => 1) := by rw [hMone]

/-! ### The forward recurrence time chain: the taboo formula -/

/-- The taboo formula (MT p. 237): `₁Pⁿ(1, j) = p(j + n − 1)`, here in the shifted indexing of
`ForwardRecurrence` (renewal state `0`): `_0Pᵐ⁺¹(0, j) = p(j + m + 1)` for every `j`. -/
theorem fwdRec_tabooKernel {p : Measure ℕ} [IsProbabilityMeasure p] (hp0 : p {0} = 0)
    (m j : ℕ) :
    tabooKernel (fwdRecKernel p) (measurableSet_singleton 0) m 0 {j} = p {j + m + 1} := by
  induction m generalizing j with
  | zero => rw [tabooKernel_zero, fwdRec_zero_singleton hp0]
  | succ m ih =>
    rw [tabooKernel_succ_eq, Kernel.comp_apply' _ _ _ (measurableSet_singleton j),
      comp_indKernel_eq_restrict, lintegral_countable', tsum_eq_single (j + 1)]
    · rw [fwdRec_succ, Measure.dirac_apply_of_mem (mem_singleton j), one_mul,
        Measure.restrict_apply (measurableSet_singleton _),
        inter_eq_left.2 (fun y hy => by simp_all), ih (j + 1)]
      congr 2
      omega
    · intro y hy
      rcases Nat.eq_zero_or_pos y with rfl | hpos
      · rw [Measure.restrict_apply (measurableSet_singleton 0)]
        simp
      · obtain ⟨i, rfl⟩ : ∃ i, y = i + 1 := ⟨y - 1, by omega⟩
        rw [fwdRec_succ, Measure.dirac_apply' _ (measurableSet_singleton j),
          indicator_of_notMem (show i ∉ ({j} : Set ℕ) by simp only [mem_singleton_iff]; omega),
          zero_mul]

/-- **Correction** to MT p. 237: the book restricts the taboo formula to `j ≤ n`, "zero
otherwise". For `p = δ₂` (the book's renewal law putting mass `1` at `2`), the book's `n = 1`,
`j = 2` (here `m = 0`, `j = 1`) gives `₁P¹(1, 2) = P(1, 2) = 1 ≠ 0`. -/
theorem fwdRec_tabooKernel_counterexample :
    tabooKernel (fwdRecKernel (Measure.dirac 2)) (measurableSet_singleton 0) 0 0 {1} = 1 := by
  rw [fwdRec_tabooKernel (by simp) 0 1]
  simp

/-! ### The M/G/1 queue: uniqueness of invariant measures -/

/-- The `j`-th invariant equation of the M/G/1 chain, isolating `π(j + 1)`:
`Σᵢ π(i) P(i, j) = Σ_{i ≤ j} π(i) P(i, j) + π(j + 1) q(0)`. -/
theorem mg1_col_split (q : ℕ → ℝ≥0∞) (m : ℕ → ℝ≥0∞) (j : ℕ) :
    ∑' i, m i * mg1Matrix q i j =
      ∑ i ∈ Finset.range (j + 1), m i * mg1Matrix q i j + m (j + 1) * q 0 := by
  rw [tsum_split _ (j + 2), ENNReal.tsum_eq_zero.2 (fun i => by
    simp [mg1Matrix, show ¬ (i + (j + 2) ≤ j + 1) by omega]),
    add_zero, Finset.sum_range_succ]
  simp [mg1Matrix]

/-- (MT p. 238) "We always get a unique invariant measure, regardless of the transience or
recurrence of the chain": two solutions of the invariant equations, finite on points, that agree
at `0` agree everywhere (`q(0) > 0`). -/
theorem mg1_invariant_unique {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (hq0 : q 0 ≠ 0)
    {m m' : ℕ → ℝ≥0∞} (hm : ∀ j, ∑' i, m i * mg1Matrix q i j = m j)
    (hm' : ∀ j, ∑' i, m' i * mg1Matrix q i j = m' j) (hfin : ∀ i, m i ≠ ∞) (h0 : m 0 = m' 0) :
    m = m' := by
  have hq0t : q 0 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hq ▸ ENNReal.le_tsum 0)
  have key : ∀ k, ∀ i ≤ k, m i = m' i := by
    intro k
    induction k with
    | zero => intro i hi; rw [show i = 0 by omega]; exact h0
    | succ k ih =>
      intro i hi
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · exact ih i (by omega)
      · rw [show i = k + 1 by omega]
        have e := hm k
        have e' := hm' k
        rw [mg1_col_split] at e e'
        have hR : ∑ i ∈ Finset.range (k + 1), m i * mg1Matrix q i k =
            ∑ i ∈ Finset.range (k + 1), m' i * mg1Matrix q i k :=
          Finset.sum_congr rfl fun i hi => by
            simp only [Finset.mem_range] at hi; rw [ih i (by omega)]
        rw [hR] at e
        have hRfin : ∑ i ∈ Finset.range (k + 1), m' i * mg1Matrix q i k ≠ ∞ :=
          ne_top_of_le_ne_top (hfin k) (le_self_add.trans_eq e)
        have e2 : ∑ i ∈ Finset.range (k + 1), m' i * mg1Matrix q i k + m (k + 1) * q 0 =
            ∑ i ∈ Finset.range (k + 1), m' i * mg1Matrix q i k + m' (k + 1) * q 0 := by
          rw [e, e', ih k le_rfl]
        exact (ENNReal.mul_left_inj hq0 hq0t).1 ((ENNReal.add_right_inj hRfin).1 e2)
  funext i
  exact key i i le_rfl

/-- Uniqueness up to constant multiples (MT p. 238): an M/G/1 invariant measure `π` finite on
points is `π(0)/π'(0)` times any invariant measure `π'` with `0 < π'(0) < ∞`. -/
theorem mg1_invariant_unique_smul {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (hq0 : q 0 ≠ 0)
    {π π' : Measure ℕ} (hπ : IsInvariant (mg1Kernel q) π) (hπ' : IsInvariant (mg1Kernel q) π')
    (hfin : ∀ i, π {i} ≠ ∞) (h0 : π' {0} ≠ 0) (h0' : π' {0} ≠ ∞) :
    π = (π {0} / π' {0}) • π' := by
  set c := π {0} / π' {0}
  have hpt : ∀ μ : Measure ℕ, μ = pointMeasure fun i => μ {i} := fun μ =>
    Measure.ext_of_singleton fun i => (pointMeasure_singleton (fun i => μ {i}) i).symm
  have hm := hπ
  have hm' := hπ'
  rw [hpt π, mg1Kernel, isInvariant_matKernel_pointMeasure_iff] at hm
  rw [hpt π', mg1Kernel, isInvariant_matKernel_pointMeasure_iff] at hm'
  have hc' : ∀ j, ∑' i, c * π' {i} * mg1Matrix q i j = c * π' {j} := fun j => by
    simp_rw [mul_assoc]
    rw [ENNReal.tsum_mul_left, hm' j]
  have huniq := mg1_invariant_unique hq hq0 hm hc' hfin
    (by rw [ENNReal.div_mul_cancel h0 h0'])
  refine Measure.ext_of_singleton fun i => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  exact congrFun huniq i

/-! ### Random walk -/

/-- (MT p. 248) A `ψ`-irreducible random walk on `ℝ` with spread-out increments of mean zero and
finite variance is null recurrent: recurrent (Propositions 6.3.2, 9.4.5, Theorem 9.2.2) and never
positive (Proposition 10.5.1). -/
theorem randomWalk_null_recurrent (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hs : IsSpreadOut Γ) (hW2 : Integrable (fun w => w ^ 2) Γ) (hβ : ∫ w, w ∂Γ = 0)
    {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_randomWalkKernel Γ;
      IsMaximalIrreducibility (randomWalkKernel Γ) ψ) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    IsRecurrentChain (randomWalkKernel Γ) ψ ∧ IsNull (randomWalkKernel Γ) ψ := by
  have := isMarkovKernel_randomWalkKernel Γ
  have hT := (proposition_6_3_2 Γ).2 hs
  have hH : IsHarris (randomWalkKernel Γ) ψ :=
    (theorem_9_2_2_ii hψ hT).2 (proposition_9_4_5 Γ hW2 hβ)
  exact ⟨hH.isRecurrentChain, hψ, fun ⟨π, hπ, hinv⟩ =>
    proposition_10_5_1 Γ ψ ⟨hψ, π, hπ, hinv⟩⟩

end MeynTweedie.GeometricErgodicity


/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.RenewalTheorem
import GeneralizedDrift.LinkedRenewal
import GeneralizedDrift.RandomWalkMeanZero
import GeneralizedDrift.CountableIrreducibility
import GeneralizedDrift.SpecificKernels
import GeneralizedDrift.StrongMarkov
import GeneralizedDrift.NonEvanescence
import GeneralizedDrift.HarrisProperties
import GeneralizedDrift.TopologicalRecurrence

/-!
# Coupling renewal processes for null chains (MT §18.1.1, Theorem 18.1.1)

Copied for Chapter 19 from the Chapter 18 project
(`Positivity/OrnsteinCoupling.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to this project's modules.

Meyn and Tweedie, pp. 464–467. For an aperiodic increment law `p` on `ℤ₊` (`p(0) = 0`, possibly
with infinite mean), delay laws `a`, `b` and the renewal sequence `u` of `p`, Theorem 18.1.1 states
(18.6) `|a ∗ u − b ∗ u|(n) → 0` and (18.7) `|a ∗ u − b ∗ u| ∗ p̄ (n) → 0` (`p̄` the tail of `p`).

**The coupling.** The book's Ornstein coupling is built as a Markov chain on `ℕ × ℕ`.
* `lazyLaw p = ½δ₀ + ½p`, the modified law `p₀` of p. 467 (with `p₀(0) = ½`); `lazyLaw_Ioi`:
  `q(n, ∞) = ½ tail(n)`.
* `ornsteinWeight`, `ornsteinLaw p M = ρ`: the joint law of a pair of increments `(S, S')`: if
  `S > M` then `S' = S`, otherwise `S, S'` are independent draws of `q` conditioned on `[0, M]`
  (p. 465). `ornsteinLaw_map_fst`, `ornsteinLaw_map_snd`: both marginals are `q`;
  `ornsteinLaw_map_swap`: `ρ` is symmetric.
* `pairKernel p M`: the chain `(Tⱼ, T'ⱼ) ↦ (Tⱼ + S, T'ⱼ + S')` of the two sequences of renewal
  epochs; `lazyRenewalKernel p`: the chain `Tⱼ ↦ Tⱼ + S` of one of them.
* `pathKernel_map_lump`, `pathKernel_lump_apply`: a map `f` with `K(y, ·) ∘ f⁻¹ = Q(f y, ·)`
  sends the paths of `K` to those of `Q` (lumping); the coordinates of `pairKernel` are
  `lazyRenewalKernel` chains (`pairKernel_map_fst`, `pairKernel_map_snd`) and their difference is
  the random walk with increment law `Γ = diffLaw p M` (`pairKernel_map_diff`).
* `diffLaw_map_neg`, `diffLaw_abs_gt`, `integral_diffLaw`: `Γ` is symmetric, carried by
  `[−M, M]`, of mean zero; `exists_aperiodic_level` chooses `M` as in (18.8);
  `isIrreducibleChain_diffWalk`: the walk `Φ*` is then irreducible on `ℤ`, and
  `hitProb_diffWalk_eq_one`: recurrent (Theorem 8.1.5), so `pairKernel_firstHit_ne_top`: the
  coupling time `T_ab` (the first common epoch) is finite almost surely.

**Renewal quantities of the lazy chain.**
* `tsum_lazyRenewalKernel_pow`: `Σⱼ Rʲ(t, {k}) = 2u(k − t)` (`u₀ = u/(1 − p₀(0))`, p. 467).
* `ageEvent n k = {∃ j, Tⱼ = k ≤ n < Tⱼ₊₁}`, the event that the age `V⁻(n)` is `n − k`;
  `pathKernel_ageEvent`, `pathMeasure_fst_ageEvent`: its probability is `(a ∗ u)(k) tail(n − k)`,
  the formula behind (18.10).

**The coupling inequality.** `pathMeasure_age_inter_coupledBy`: after `T_ab` the two ages have the
same law (the strong Markov property at `T_ab`); `sum_abs_age_sub_le`: the total variation of the
two age laws is at most `2 P(T_ab > n)` ((18.9)–(18.10)); `tendsto_pathMeasure_coupledBy_compl`:
`P(T_ab > n) → 0`.

**Results.**
* **Theorem 18.1.1** (p. 465): (18.6) `theorem_18_1_1_i` (this is Theorem 13.2.2, whose analytic
  proof already covers `m_p = ∞`); (18.7) `theorem_18_1_1_ii`,
  `|a ∗ u − b ∗ u| ∗ p̄ (n) → 0` with the tail `p̄(m) = Σ_{j > m} p(j)`.
* `tendsto_realConv_abs_sub_delayedRenewal_incr`: the same with `p` in place of `p̄` (immediate
  from (18.6), since `p` is summable; the remark at the end of §18.1.1).

**Corrections.** None.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-! ### Lumping -/

/-- **Lumping.** If `f` maps the chain `K` to the chain `Q` step by step,
`K(y, ·) ∘ f⁻¹ = Q(f y, ·)`, then the image of `P^K_y` under `ω ↦ f ∘ ω` is `P^Q_{f y}`. -/
theorem pathKernel_map_lump {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (K : Kernel Y Y) [IsMarkovKernel K] (Q : Kernel Z Z) [IsMarkovKernel Q] {f : Y → Z}
    (hf : Measurable f) (hKQ : ∀ y, (K y).map f = Q (f y)) (y : Y) :
    (pathKernel K y).map (fun ω n => f (ω n)) = pathKernel Q (f y) := by
  have := isMarkovKernel_pathKernel K
  have hch : IsMarkovChain Q (Measure.dirac (f y)) (pathKernel K y) (fun n ω => f (ω n)) := by
    refine isMarkovChain_of_step Q (Measure.dirac (f y)) (𝓖 := natFilt (X := Y))
      (fun n => hf.comp (measurable_coord_natFilt n)) ?_ ?_
    · have h0 := pathKernel_map_zero K y
      have : (fun ω : ℕ → Y => f (ω 0)) = f ∘ fun ω => ω 0 := rfl
      rw [this, ← Measure.map_map hf (measurable_pi_apply 0), h0]
      exact Measure.map_dirac' hf y
    · intro n G hG g hg
      rw [← pathMeasure_dirac K y]
      have h1 := setLIntegral_succ K (Measure.dirac y) hG (hg.comp hf)
      simp only [Function.comp_apply] at h1
      rw [h1]
      refine setLIntegral_congr_fun ((natFilt (X := Y)).le n _ hG) fun ω _ => ?_
      rw [← hKQ, lintegral_map hg hf]
  have := law_eq_pathMeasure Q (Measure.dirac (f y)) hch
  rw [pathMeasure_dirac] at this
  exact this

/-- Lumping in terms of events: `P^K_y(f ∘ Φ ∈ E) = P^Q_{f y}(E)`. -/
theorem pathKernel_lump_apply {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (K : Kernel Y Y) [IsMarkovKernel K] (Q : Kernel Z Z) [IsMarkovKernel Q] {f : Y → Z}
    (hf : Measurable f) (hKQ : ∀ y, (K y).map f = Q (f y)) (y : Y) {E : Set (ℕ → Z)}
    (hE : MeasurableSet E) :
    pathKernel K y {ω | (fun n => f (ω n)) ∈ E} = pathKernel Q (f y) E := by
  rw [← pathKernel_map_lump K Q hf hKQ y, Measure.map_apply _ hE]
  · rfl
  · exact measurable_pi_iff.2 fun n => hf.comp (measurable_pi_apply n)

/-! ### The lazy increment law -/

/-- The **lazy increment law** `q = ½δ₀ + ½p`: the book's modified distribution `p₀` with
`p₀(0) = ½` (MT p. 467). -/
noncomputable def lazyLaw (p : ℕ → ℝ) : Measure ℕ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • lawMeasure p

/-- `q{0} = ½`. -/
theorem lazyLaw_zero {p : ℕ → ℝ} (hp : IsIncrementLaw p) : lazyLaw p {0} = 2⁻¹ := by
  rw [lazyLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, lawMeasure_zero hp,
    Measure.dirac_apply_of_mem (mem_singleton 0)]
  simp

/-- `q{s} = ½ p(s)` for `s ≠ 0`. -/
theorem lazyLaw_of_ne {p : ℕ → ℝ} {s : ℕ} (hs : s ≠ 0) :
    lazyLaw p {s} = 2⁻¹ * ENNReal.ofReal (p s) := by
  rw [lazyLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, lawMeasure_singleton,
    Measure.dirac_apply' _ (measurableSet_singleton s),
    indicator_of_notMem (by simpa using Ne.symm hs)]
  simp

/-- `q` is a probability. -/
theorem isProbabilityMeasure_lazyLaw {p : ℕ → ℝ} (hp : IsIncrementLaw p) :
    IsProbabilityMeasure (lazyLaw p) := by
  have := isProbabilityMeasure_lawMeasure hp
  refine ⟨?_⟩
  rw [lazyLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
    measure_univ]
  simp [ENNReal.inv_two_add_inv_two]

/-- `p(Ioi m) = Σ_{s > m} p(s) = tail(m)`. -/
theorem lawMeasure_Ioi {p : ℕ → ℝ} (hp : IsIncrementLaw p) (m : ℕ) :
    lawMeasure p (Ioi m) = ENNReal.ofReal (renewalTail p m) := by
  have h1 : lawMeasure p (Ioi m) =
      ∑' n, (Ioi m).indicator (fun n => ENNReal.ofReal (p n)) n := by
    rw [lawMeasure, Measure.sum_apply _ measurableSet_Ioi]
    refine tsum_congr fun n => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ioi, smul_eq_mul]
    by_cases hn : n ∈ Ioi m <;> simp [hn]
  have h2 : ∑' n, (Ioi m).indicator (fun n => ENNReal.ofReal (p n)) n =
      ∑' j, ENNReal.ofReal (p (j + (m + 1))) := by
    rw [← (ENNReal.summable (f := fun n => (Ioi m).indicator
      (fun n => ENNReal.ofReal (p n)) (n + (m + 1)))).sum_add_tsum_nat_add']
    have h0 : ∑ i ∈ Finset.range (m + 1),
        (Ioi m).indicator (fun n => ENNReal.ofReal (p n)) i = 0 :=
      Finset.sum_eq_zero fun i hi => indicator_of_notMem (by
        simp only [mem_Ioi, not_lt]; exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) _
    rw [h0, zero_add]
    exact tsum_congr fun j => indicator_of_mem (by simp only [mem_Ioi]; omega) _
  have h3 : Summable fun j => p (j + (m + 1)) :=
    hp.hasSum.summable.comp_injective (add_left_injective (m + 1))
  rw [h1, h2, ← ENNReal.ofReal_tsum_of_nonneg (fun j => hp.nonneg _) h3,
    renewalTail_eq_tsum hp]

/-- `q(Ioi m) = ½ tail(m)`: the lazy step does not reach beyond `m`. -/
theorem lazyLaw_Ioi {p : ℕ → ℝ} (hp : IsIncrementLaw p) (m : ℕ) :
    lazyLaw p (Ioi m) = 2⁻¹ * ENNReal.ofReal (renewalTail p m) := by
  rw [lazyLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, lawMeasure_Ioi hp,
    Measure.dirac_apply' _ measurableSet_Ioi, indicator_of_notMem (by simp)]
  simp

/-- `q(Iic M) > 0`. -/
theorem lazyLaw_Iic_ne_zero {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) :
    lazyLaw p (Iic M) ≠ 0 := by
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (singleton_subset_iff.2 (Nat.zero_le M))))
  rw [lazyLaw_zero hp]
  exact ENNReal.inv_pos.2 ENNReal.ofNat_ne_top

/-- `q(Iic M) < ∞`. -/
theorem lazyLaw_Iic_ne_top {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) :
    lazyLaw p (Iic M) ≠ ∞ := by
  have := isProbabilityMeasure_lazyLaw hp
  exact measure_ne_top _ _

/-- `Σ_{z ≤ M} q{z} = q(Iic M)`. -/
theorem tsum_indicator_lazyLaw_Iic (p : ℕ → ℝ) (M : ℕ) :
    ∑' z, (Iic M).indicator (fun z => lazyLaw p {z}) z = lazyLaw p (Iic M) :=
  Measure.tsum_indicator_apply_singleton _ _ measurableSet_Iic

/-! ### The Ornstein coupling -/

/-- The point masses of the **Ornstein coupling** at level `M` of two copies of the lazy law `q`
(MT p. 465): if the first increment exceeds `M` the second equals it; otherwise both are
independent draws of `q` conditioned on `[0, M]`. -/
noncomputable def ornsteinWeight (p : ℕ → ℝ) (M : ℕ) (z : ℕ × ℕ) : ℝ≥0∞ :=
  if M < z.1 then (if z.1 = z.2 then lazyLaw p {z.1} else 0)
  else if z.2 ≤ M then lazyLaw p {z.1} * lazyLaw p {z.2} / lazyLaw p (Iic M) else 0

/-- The **Ornstein coupling** `ρ` on `ℕ × ℕ`, the joint law of a pair of increments
`(S, S')`. -/
noncomputable def ornsteinLaw (p : ℕ → ℝ) (M : ℕ) : Measure (ℕ × ℕ) :=
  Measure.sum fun z => ornsteinWeight p M z • Measure.dirac z

/-- `ρ{z} = w(z)`. -/
theorem ornsteinLaw_singleton (p : ℕ → ℝ) (M : ℕ) (z : ℕ × ℕ) :
    ornsteinLaw p M {z} = ornsteinWeight p M z :=
  Measure.sum_smul_dirac_singleton

/-- `ρ(S) = Σ_{z ∈ S} w(z)`. -/
theorem ornsteinLaw_apply (p : ℕ → ℝ) (M : ℕ) (S : Set (ℕ × ℕ)) :
    ornsteinLaw p M S = ∑' z, S.indicator (ornsteinWeight p M) z := by
  rw [← Measure.tsum_indicator_apply_singleton _ _ (Set.to_countable S).measurableSet]
  simp_rw [ornsteinLaw_singleton]

/-- The weights are symmetric. -/
theorem ornsteinWeight_swap (p : ℕ → ℝ) (M : ℕ) (z : ℕ × ℕ) :
    ornsteinWeight p M z.swap = ornsteinWeight p M z := by
  obtain ⟨a, b⟩ := z
  simp only [ornsteinWeight, Prod.swap_prod_mk]
  by_cases ha : M < a <;> by_cases hb : M < b
  · by_cases hab : a = b
    · subst hab; rfl
    · simp [ha, hb, hab, Ne.symm hab]
  · have hab : a ≠ b := by omega
    simp only [ha, hb, ↓reduceIte, show ¬ a ≤ M by omega, hab]
  · have hab : a ≠ b := by omega
    simp only [ha, hb, ↓reduceIte, show ¬ b ≤ M by omega, Ne.symm hab]
  · simp only [ha, hb, ↓reduceIte, not_lt.1 ha, not_lt.1 hb]
    rw [mul_comm]

/-- A nonzero weight sits on the diagonal or in `[0, M]²`. -/
theorem ornsteinWeight_ne_zero {p : ℕ → ℝ} {M : ℕ} {z : ℕ × ℕ} (h : ornsteinWeight p M z ≠ 0) :
    z.1 = z.2 ∨ (z.1 ≤ M ∧ z.2 ≤ M) := by
  unfold ornsteinWeight at h
  by_cases ha : M < z.1
  · by_cases hab : z.1 = z.2
    · exact Or.inl hab
    · simp [ha, hab] at h
  · by_cases hb : z.2 ≤ M
    · exact Or.inr ⟨not_lt.1 ha, hb⟩
    · simp [ha, hb] at h

/-- The first marginal of the weights: `Σ_{z₂} w(s, z₂) = q{s}`. -/
theorem tsum_ornsteinWeight_snd {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M s : ℕ) :
    ∑' z₂, ornsteinWeight p M (s, z₂) = lazyLaw p {s} := by
  by_cases hs : M < s
  · have h : (fun z₂ => ornsteinWeight p M (s, z₂)) =
        fun z₂ => if z₂ = s then lazyLaw p {s} else 0 := funext fun z₂ => by
      by_cases h : z₂ = s
      · subst h; simp [ornsteinWeight, hs]
      · simp [ornsteinWeight, hs, h, Ne.symm h]
    rw [h, tsum_ite_eq s]
  · have h : (fun z₂ => ornsteinWeight p M (s, z₂)) = fun z₂ => lazyLaw p {s} /
        lazyLaw p (Iic M) * (Iic M).indicator (fun z => lazyLaw p {z}) z₂ := funext fun z₂ => by
      by_cases hz : z₂ ≤ M
      · simp only [ornsteinWeight, hs, hz, ↓reduceIte, indicator_of_mem (show z₂ ∈ Iic M from hz)]
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
      · simp [ornsteinWeight, hs, hz]
    rw [h, ENNReal.tsum_mul_left, tsum_indicator_lazyLaw_Iic,
      ENNReal.div_mul_cancel (lazyLaw_Iic_ne_zero hp M) (lazyLaw_Iic_ne_top hp M)]

/-- `ρ` has first marginal `q`. -/
theorem ornsteinLaw_map_fst {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) :
    (ornsteinLaw p M).map Prod.fst = lazyLaw p := by
  refine Measure.ext_of_singleton fun s => ?_
  rw [Measure.map_apply measurable_fst (measurableSet_singleton s), ornsteinLaw_apply,
    ENNReal.tsum_prod', ← tsum_ornsteinWeight_snd hp M s]
  have h : (fun a => ∑' b, (Prod.fst ⁻¹' {s}).indicator (ornsteinWeight p M) (a, b)) =
      fun a => if a = s then ∑' b, ornsteinWeight p M (s, b) else 0 := funext fun a => by
    by_cases ha : a = s
    · subst ha
      simp only [↓reduceIte]
      exact tsum_congr fun b => indicator_of_mem (by simp) _
    · simp only [ha, ↓reduceIte]
      exact ENNReal.tsum_eq_zero.2 fun b => indicator_of_notMem (by simpa using ha) _
  rw [h, tsum_ite_eq s]

/-- `ρ` is invariant under exchanging the coordinates. -/
theorem ornsteinLaw_map_swap (p : ℕ → ℝ) (M : ℕ) :
    (ornsteinLaw p M).map Prod.swap = ornsteinLaw p M := by
  refine Measure.ext_of_singleton fun z => ?_
  have hpre : Prod.swap ⁻¹' {z} = {z.swap} := by
    ext w
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h => by rw [← h, Prod.swap_swap], fun h => by rw [h, Prod.swap_swap]⟩
  rw [Measure.map_apply measurable_swap (measurableSet_singleton z), hpre,
    ornsteinLaw_singleton, ornsteinLaw_singleton, ornsteinWeight_swap]

/-- `ρ` has second marginal `q`: the two increment sequences have the same law. -/
theorem ornsteinLaw_map_snd {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) :
    (ornsteinLaw p M).map Prod.snd = lazyLaw p := by
  rw [← ornsteinLaw_map_swap p M, Measure.map_map measurable_snd measurable_swap]
  exact ornsteinLaw_map_fst hp M

/-- `ρ` is a probability. -/
theorem isProbabilityMeasure_ornsteinLaw {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) :
    IsProbabilityMeasure (ornsteinLaw p M) := by
  have := isProbabilityMeasure_lazyLaw hp
  refine ⟨?_⟩
  have h := congrArg (fun μ : Measure ℕ => μ univ) (ornsteinLaw_map_fst hp M)
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
    measure_univ] at h
  exact h

/-! ### The chains -/

/-- The **lazy renewal chain** on `ℕ`: from `t` jump to `t + S` with `S ~ q`. Its path is the
sequence of renewal epochs of a delayed renewal process with increments `q`. -/
noncomputable def lazyRenewalKernel (p : ℕ → ℝ) : Kernel ℕ ℕ :=
  ⟨fun t => (lazyLaw p).map (t + ·), measurable_of_countable _⟩

/-- `R(t, ·) = q(· − t)`. -/
theorem lazyRenewalKernel_apply (p : ℕ → ℝ) (t : ℕ) :
    lazyRenewalKernel p t = (lazyLaw p).map (t + ·) := rfl

/-- The lazy renewal chain is a Markov kernel. -/
theorem isMarkovKernel_lazyRenewalKernel {p : ℕ → ℝ} (hp : IsIncrementLaw p) :
    IsMarkovKernel (lazyRenewalKernel p) := by
  have := isProbabilityMeasure_lazyLaw hp
  exact ⟨fun t => by rw [lazyRenewalKernel_apply]; infer_instance⟩

/-- The **coupled pair chain** on `ℕ × ℕ`: from `(t, t')` jump to `(t + S, t' + S')` with
`(S, S') ~ ρ`. Its two coordinates are the renewal epochs of the two coupled processes. -/
noncomputable def pairKernel (p : ℕ → ℝ) (M : ℕ) : Kernel (ℕ × ℕ) (ℕ × ℕ) :=
  ⟨fun y => (ornsteinLaw p M).map (fun z => (y.1 + z.1, y.2 + z.2)), measurable_of_countable _⟩

/-- `K(y, ·)` is `ρ` translated by `y`. -/
theorem pairKernel_apply (p : ℕ → ℝ) (M : ℕ) (y : ℕ × ℕ) :
    pairKernel p M y = (ornsteinLaw p M).map (fun z => (y.1 + z.1, y.2 + z.2)) := rfl

/-- The pair chain is a Markov kernel. -/
theorem isMarkovKernel_pairKernel {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) :
    IsMarkovKernel (pairKernel p M) := by
  have := isProbabilityMeasure_ornsteinLaw hp M
  exact ⟨fun t => by rw [pairKernel_apply]; infer_instance⟩

/-- The difference `t − t'` of the two coordinates, in `ℤ`. -/
def pairDiff (y : ℕ × ℕ) : ℤ := (y.1 : ℤ) - y.2

/-- The law `Γ` of the increment difference `S − S'` under `ρ`. -/
noncomputable def diffLaw (p : ℕ → ℝ) (M : ℕ) : Measure ℤ := (ornsteinLaw p M).map pairDiff

/-- The first coordinate of the pair chain is the lazy renewal chain. -/
theorem pairKernel_map_fst {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) (y : ℕ × ℕ) :
    (pairKernel p M y).map Prod.fst = lazyRenewalKernel p y.1 := by
  rw [pairKernel_apply, Measure.map_map measurable_fst (measurable_of_countable _),
    lazyRenewalKernel_apply, ← ornsteinLaw_map_fst hp M,
    Measure.map_map (measurable_of_countable _) measurable_fst]
  rfl

/-- The second coordinate of the pair chain is the lazy renewal chain. -/
theorem pairKernel_map_snd {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) (y : ℕ × ℕ) :
    (pairKernel p M y).map Prod.snd = lazyRenewalKernel p y.2 := by
  rw [pairKernel_apply, Measure.map_map measurable_snd (measurable_of_countable _),
    lazyRenewalKernel_apply, ← ornsteinLaw_map_snd hp M,
    Measure.map_map (measurable_of_countable _) measurable_snd]
  rfl

/-- The difference of the coordinates of the pair chain is the random walk on `ℤ` with
increment law `Γ`. -/
theorem pairKernel_map_diff (p : ℕ → ℝ) (M : ℕ) (y : ℕ × ℕ) :
    (pairKernel p M y).map pairDiff = randomWalkKernel (diffLaw p M) (pairDiff y) := by
  rw [randomWalkKernel_apply, diffLaw, pairKernel_apply,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext z
  simp only [Function.comp_apply, pairDiff]
  push_cast
  ring

/-! ### The difference walk is recurrent -/

/-- **A finite aperiodicity level** (the choice of `M` in (18.8), MT p. 466): for an aperiodic
increment law there is `M` such that `1` is the only common divisor of `{n ≤ M : p(n) > 0}`. -/
theorem exists_aperiodic_level {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p) :
    ∃ M, ∀ d : ℕ, (∀ n ≤ M, 0 < p n → d ∣ n) → d = 1 := by
  classical
  set g : ℕ → ℕ := fun M => ((Finset.range (M + 1)).filter fun n => 0 < p n).gcd id with hg
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, 0 < p n₀ := by
    by_contra h
    push Not at h
    have h0 : ∀ n, p n = 0 := fun n => le_antisymm (h n) (hp.nonneg n)
    have h1 : HasSum p 0 := by rw [show p = fun _ => 0 from funext h0]; exact hasSum_zero
    exact zero_ne_one (h1.unique hp.hasSum)
  have hn₀pos : 0 < n₀ := Nat.pos_of_ne_zero fun h => by
    rw [h, hp.zero] at hn₀; exact lt_irrefl _ hn₀
  have hmem : ∀ {M n}, n ≤ M → 0 < p n → n ∈ (Finset.range (M + 1)).filter fun n => 0 < p n :=
    fun hn hpn => Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hn), hpn⟩
  have hdvd : ∀ {M n}, n ≤ M → 0 < p n → g M ∣ n := fun hn hpn =>
    Finset.gcd_dvd (f := id) (hmem hn hpn)
  have hgpos : ∀ M, n₀ ≤ M → 0 < g M := fun M hM =>
    Nat.pos_of_dvd_of_pos (hdvd hM hn₀) hn₀pos
  have hex : ∃ k, ∃ M, n₀ ≤ M ∧ g M = k := ⟨g n₀, n₀, le_rfl, rfl⟩
  obtain ⟨M, hM, hMk⟩ := Nat.find_spec hex
  have hall : ∀ n, 0 < p n → Nat.find hex ∣ n := fun n hpn => by
    set M' := max M n
    have hsub : ((Finset.range (M + 1)).filter fun n => 0 < p n) ⊆
        (Finset.range (M' + 1)).filter fun n => 0 < p n := fun i hi => by
      obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
      exact hmem (le_trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi1)) (le_max_left _ _)) hi2
    have h1 : g M' ∣ g M := Finset.gcd_mono hsub
    have h2 : Nat.find hex ≤ g M' := Nat.find_min' hex ⟨M', le_trans hM (le_max_left _ _), rfl⟩
    have h4 : g M' ≤ g M := Nat.le_of_dvd (hgpos M hM) h1
    rw [hMk] at h4
    have h3 : g M' = Nat.find hex := le_antisymm h4 h2
    exact h3 ▸ hdvd (le_max_right _ _) hpn
  have hk1 : Nat.find hex = 1 := hap _ hall
  refine ⟨M, fun d hd => ?_⟩
  have : d ∣ g M := Finset.dvd_gcd fun n hn => by
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
    exact hd n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn1)) hn2
  rw [hMk, hk1] at this
  exact Nat.dvd_one.1 this

/-- `Γ` is a probability. -/
theorem isProbabilityMeasure_diffLaw {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) :
    IsProbabilityMeasure (diffLaw p M) := by
  have := isProbabilityMeasure_ornsteinLaw hp M
  rw [diffLaw]
  infer_instance

/-- `Γ` is carried by `[−M, M]`. -/
theorem diffLaw_abs_gt (p : ℕ → ℝ) (M : ℕ) : diffLaw p M {w | (M : ℤ) < |w|} = 0 := by
  rw [diffLaw, Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    ornsteinLaw_apply]
  refine ENNReal.tsum_eq_zero.2 fun z => ?_
  by_cases hz : ornsteinWeight p M z = 0
  · simp [hz]
  · refine indicator_of_notMem ?_ _
    simp only [mem_preimage, mem_ofPred_eq, not_lt, pairDiff]
    rcases ornsteinWeight_ne_zero hz with h | ⟨h1, h2⟩
    · rw [h, sub_self, abs_zero]; exact Int.natCast_nonneg M
    · rw [abs_le]; constructor <;> omega

/-- `Γ` is symmetric. -/
theorem diffLaw_map_neg (p : ℕ → ℝ) (M : ℕ) : (diffLaw p M).map Neg.neg = diffLaw p M := by
  rw [diffLaw, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  conv_rhs => rw [← ornsteinLaw_map_swap p M,
    Measure.map_map (measurable_of_countable _) measurable_swap]
  congr 1
  funext z
  simp [pairDiff]

/-- The increments `S − S'` are integrable. -/
theorem integrable_diffLaw {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) :
    Integrable (fun z : ℤ => (z : ℝ)) (diffLaw p M) := by
  have := isProbabilityMeasure_diffLaw hp M
  refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (M : ℝ) ?_
  rw [ae_iff]
  refine measure_mono_null (fun w hw => ?_) (diffLaw_abs_gt p M)
  simp only [mem_ofPred_eq, Real.norm_eq_abs, not_le] at hw ⊢
  exact_mod_cast hw

/-- **The difference walk has mean zero**: `Γ` is symmetric. -/
theorem integral_diffLaw (p : ℕ → ℝ) (M : ℕ) :
    ∫ z, (z : ℝ) ∂diffLaw p M = 0 := by
  have h : ∫ z, (z : ℝ) ∂diffLaw p M = ∫ z, ((-z : ℤ) : ℝ) ∂diffLaw p M := by
    conv_lhs => rw [← diffLaw_map_neg p M]
    rw [integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  simp only [Int.cast_neg, integral_neg] at h
  linarith

/-- Both `±n` are charged by `Γ` when `1 ≤ n ≤ M` and `p(n) > 0`. -/
theorem diffLaw_singleton_pos {p : ℕ → ℝ} (hp : IsIncrementLaw p) {M n : ℕ} (hn : n ≤ M)
    (hn0 : n ≠ 0) (hpn : 0 < p n) :
    diffLaw p M {(n : ℤ)} ≠ 0 ∧ diffLaw p M {-(n : ℤ)} ≠ 0 := by
  have hq : lazyLaw p {n} ≠ 0 := by
    rw [lazyLaw_of_ne hn0]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
      (ENNReal.ofReal_pos.2 hpn).ne'
  have hq0 : lazyLaw p {0} ≠ 0 := by
    rw [lazyLaw_zero hp]; exact ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  have hc := lazyLaw_Iic_ne_top hp M
  have hm : ∀ w : ℤ, Measurable fun z : ℕ × ℕ => pairDiff z := fun _ => measurable_of_countable _
  constructor
  · rw [diffLaw, Measure.map_apply (hm n) (measurableSet_singleton _)]
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (singleton_subset_iff.2
      (show (n, 0) ∈ pairDiff ⁻¹' {(n : ℤ)} by simp [pairDiff]))))
    rw [ornsteinLaw_singleton, ornsteinWeight]
    simp only [not_lt.2 hn, ↓reduceIte, Nat.zero_le]
    exact ENNReal.div_pos (mul_ne_zero hq hq0) hc
  · rw [diffLaw, Measure.map_apply (hm n) (measurableSet_singleton _)]
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (singleton_subset_iff.2
      (show (0, n) ∈ pairDiff ⁻¹' {-(n : ℤ)} by simp [pairDiff]))))
    rw [ornsteinLaw_singleton, ornsteinWeight]
    simp only [not_lt.2 (Nat.zero_le M), ↓reduceIte, hn]
    exact ENNReal.div_pos (mul_ne_zero hq0 hq) hc

/-- With `M` as in `exists_aperiodic_level`, the difference walk with increment law `Γ` is
irreducible on `ℤ`: `Γ` charges `±n` for each `n ≤ M` with `p(n) > 0`, and these generate `ℤ`.
This is where (18.8) and the laziness of `q` are used (MT pp. 466–467). -/
theorem isIrreducibleChain_diffWalk {p : ℕ → ℝ} (hp : IsIncrementLaw p) {M : ℕ}
    (hM : ∀ d : ℕ, (∀ n ≤ M, 0 < p n → d ∣ n) → d = 1) :
    haveI := isProbabilityMeasure_diffLaw hp M
    haveI := isMarkovKernel_randomWalkKernel (diffLaw p M)
    IsIrreducibleChain (randomWalkKernel (diffLaw p M)) := by
  have := isProbabilityMeasure_diffLaw hp M
  have := isMarkovKernel_randomWalkKernel (diffLaw p M)
  set Γ' : ℤ → ℝ≥0∞ := fun k => diffLaw p M {k} with hΓ'
  have heq : matKernel (rwMatrix Γ') = randomWalkKernel (diffLaw p M) := matKernel_rwMatrix _
  have : IsMarkovKernel (matKernel (rwMatrix Γ')) := by rw [heq]; infer_instance
  obtain ⟨n₀, hn₀M, hn₀⟩ : ∃ n₀ ≤ M, 0 < p n₀ := by
    by_contra h
    push Not at h
    exact zero_ne_one (hM 0 fun n hn hpn => absurd hpn (not_lt.2 (h n hn)))
  have hn₀0 : n₀ ≠ 0 := fun h => by rw [h, hp.zero] at hn₀; exact lt_irrefl _ hn₀
  obtain ⟨ha, hb⟩ := diffLaw_singleton_pos hp hn₀M hn₀0 hn₀
  have hgroup : rwSupportGroup Γ' = ⊤ := by
    obtain ⟨d, hd⟩ := rw_closure_eq_zmultiples Γ'
    have hd1 : d = 1 := hM d fun n hn hpn => by
      have hn0 : n ≠ 0 := fun h => by rw [h, hp.zero] at hpn; exact lt_irrefl _ hpn
      have hmem : (n : ℤ) ∈ rwSupportGroup Γ' :=
        AddSubgroup.subset_closure (diffLaw_singleton_pos hp hn hn0 hpn).1
      rw [hd, AddSubgroup.mem_zmultiples_iff] at hmem
      obtain ⟨k, hk⟩ := hmem
      exact Int.natCast_dvd_natCast.1 ⟨k, by rw [← hk, smul_eq_mul, mul_comm]⟩
    rw [hd, hd1, Nat.cast_one, Int.zmultiples_one]
  have hcl := rw_commClass_eq (Γ := Γ') (a := n₀) (b := -(n₀ : ℤ))
    (by exact_mod_cast Nat.pos_of_ne_zero hn₀0) ha (by omega) hb
  have hall : ∀ x y : ℤ, ∃ n, 0 < (randomWalkKernel (diffLaw p M) ^ n) x {y} := fun x y => by
    have hy : y ∈ commClass (matKernel (rwMatrix Γ')) x := by
      rw [hcl x, hgroup]; trivial
    obtain ⟨n, hn⟩ := (leads_iff_exists_pow _ x y).1 hy.1
    exact ⟨n, heq ▸ hn⟩
  refine (isIrreducibleChain_iff _).2 fun x y => ⟨?_, ?_⟩
  · exact (leads_iff_exists_pow _ x y).2 (hall x y)
  · exact (leads_iff_exists_pow _ y x).2 (hall y x)

/-- **The difference walk is recurrent** (Theorem 8.1.5, used as Proposition 8.4.4 in MT p. 465):
from every `d ∈ ℤ` it reaches `0` almost surely. -/
theorem hitProb_diffWalk_eq_one {p : ℕ → ℝ} (hp : IsIncrementLaw p) {M : ℕ}
    (hM : ∀ d : ℕ, (∀ n ≤ M, 0 < p n → d ∣ n) → d = 1) (x : ℤ) :
    haveI := isProbabilityMeasure_diffLaw hp M
    haveI := isMarkovKernel_randomWalkKernel (diffLaw p M)
    hitProb (randomWalkKernel (diffLaw p M)) {0} x = 1 := by
  have := isProbabilityMeasure_diffLaw hp M
  have := isMarkovKernel_randomWalkKernel (diffLaw p M)
  have hirr := isIrreducibleChain_diffWalk hp hM
  have hrec := theorem_8_1_5 (diffLaw p M) (integrable_diffLaw hp M) (integral_diffLaw p M) hirr
  exact hitProb_eq_one_of_recurrent _ hirr ((isRecurrentChain_count_iff _ hirr).1 hrec)
    (A := {0}) ⟨0, mem_singleton 0⟩ x

/-! ### The coupling time -/

/-- The diagonal `{t = t'}`: a common renewal epoch of the two coupled processes. -/
def pairDiag : Set (ℕ × ℕ) := {y | y.1 = y.2}

/-- `y ∈ Δ` iff `t − t' = 0`. -/
theorem mem_pairDiag_iff (y : ℕ × ℕ) : y ∈ pairDiag ↔ pairDiff y = 0 := by
  simp only [pairDiag, mem_ofPred_eq, pairDiff, sub_eq_zero, Nat.cast_inj]

/-- **The coupling is successful**: from every pair of starting epochs, the coupled pair chain
reaches the diagonal almost surely, `P(T_ab < ∞) = 1` (MT p. 466). -/
theorem pairKernel_firstHit_ne_top {p : ℕ → ℝ} (hp : IsIncrementLaw p) {M : ℕ}
    (hM : ∀ d : ℕ, (∀ n ≤ M, 0 < p n → d ∣ n) → d = 1) (y : ℕ × ℕ) :
    haveI := isMarkovKernel_pairKernel hp M
    pathKernel (pairKernel p M) y {ω | firstHit pairDiag ω ≠ ⊤} = 1 := by
  have := isMarkovKernel_pairKernel hp M
  have := isProbabilityMeasure_diffLaw hp M
  have := isMarkovKernel_randomWalkKernel (diffLaw p M)
  have := isMarkovKernel_pathKernel (pairKernel p M)
  have := isMarkovKernel_pathKernel (randomWalkKernel (diffLaw p M))
  have hset : {ω : ℕ → ℕ × ℕ | firstHit pairDiag ω ≠ ⊤} =
      {ω | (fun n => pairDiff (ω n)) ∈ {ω' : ℕ → ℤ | ∃ n, ω' n ∈ ({0} : Set ℤ)}} := by
    ext ω
    simp only [mem_ofPred_eq, firstHit, ne_eq, hittingAfter_eq_top_iff, not_forall, not_not,
      mem_singleton_iff, ← mem_pairDiag_iff]
    constructor
    · rintro ⟨n, -, hn⟩; exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, Nat.zero_le n, hn⟩
  have hmeas : MeasurableSet {ω' : ℕ → ℤ | ∃ n, ω' n ∈ ({0} : Set ℤ)} := by
    have : {ω' : ℕ → ℤ | ∃ n, ω' n ∈ ({0} : Set ℤ)} = ⋃ n, (fun ω' : ℕ → ℤ => ω' n) ⁻¹' {0} := by
      ext ω'; simp
    rw [this]
    exact MeasurableSet.iUnion fun n => measurable_pi_apply n (measurableSet_singleton 0)
  rw [hset, pathKernel_lump_apply (pairKernel p M) (randomWalkKernel (diffLaw p M))
    (measurable_of_countable _) (pairKernel_map_diff p M) y hmeas, ← hitProbZero_eq_exists]
  exact le_antisymm prob_le_one ((hitProb_diffWalk_eq_one hp hM (pairDiff y)).symm.le.trans
    (hitProb_le_hitProbZero _ _ _))

/-! ### The lazy renewal chain -/

/-- The lazy renewal chain never moves down. -/
theorem lazyRenewalKernel_Iio (p : ℕ → ℝ) (t : ℕ) : lazyRenewalKernel p t (Iio t) = 0 := by
  rw [lazyRenewalKernel_apply, Measure.map_apply (measurable_of_countable _) measurableSet_Iio]
  convert measure_empty (μ := lazyLaw p)
  ext s
  simp

/-- `Rʲ(t, Iio t) = 0`. -/
theorem lazyRenewalKernel_pow_Iio (p : ℕ → ℝ) (j t : ℕ) :
    (lazyRenewalKernel p ^ j) t (Iio t) = 0 := by
  induction j generalizing t with
  | zero =>
    rw [pow_zero_apply, Measure.dirac_apply' _ measurableSet_Iio, indicator_of_notMem (by simp)]
  | succ j ih =>
    rw [pow_succ_apply _ _ _ measurableSet_Iio, lazyRenewalKernel_apply,
      lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
    refine (lintegral_eq_zero_iff (measurable_of_countable _)).2 ?_
    exact Filter.Eventually.of_forall fun s =>
      measure_mono_null (Iio_subset_Iio (Nat.le_add_right t s)) (ih (t + s))

/-- One step of the lazy renewal chain: `∫ f dR(t, ·) = ½ f(t) + ½ Σₛ p(s) f(t + s)`. -/
theorem lintegral_lazyRenewalKernel (p : ℕ → ℝ) (t : ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ z, f z ∂lazyRenewalKernel p t =
      2⁻¹ * f t + 2⁻¹ * ∑' s, ENNReal.ofReal (p s) * f (t + s) := by
  rw [lazyRenewalKernel_apply, lintegral_map (measurable_of_countable _)
    (measurable_of_countable _), lazyLaw, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac, lawMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, add_zero, smul_eq_mul]

/-- The candidate potential `V(t) = 2u(k − t)` for `t ≤ k`, `0` for `t > k`. -/
noncomputable def lazyPot (p : ℕ → ℝ) (k t : ℕ) : ℝ≥0∞ :=
  if t ≤ k then 2 * ENNReal.ofReal (realRenewalSeq p (k - t)) else 0

/-- `V` is finite. -/
theorem lazyPot_ne_top (p : ℕ → ℝ) (k t : ℕ) : lazyPot p k t ≠ ∞ := by
  unfold lazyPot
  split_ifs
  · exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

/-- `Σₛ p(s) V(t + s) = 2 (p ∗ u)(k − t)` for `t ≤ k`. -/
theorem tsum_mul_lazyPot {p : ℕ → ℝ} (hp : IsIncrementLaw p) {k t : ℕ} (ht : t ≤ k) :
    ∑' s, ENNReal.ofReal (p s) * lazyPot p k (t + s) =
      2 * ENNReal.ofReal (realConv p (realRenewalSeq p) (k - t)) := by
  rw [tsum_eq_sum (s := Finset.range (k - t + 1)) fun s hs => by
    have : ¬ t + s ≤ k := by
      intro h; exact hs (Finset.mem_range.2 (by omega))
    simp [lazyPot, this]]
  rw [realConv_eq_sum_range, ENNReal.ofReal_sum_of_nonneg fun s _ =>
    mul_nonneg (hp.nonneg s) (realRenewalSeq_nonneg hp _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : t + s ≤ k := by have := Finset.mem_range.1 hs; omega
  simp only [lazyPot, hs', ↓reduceIte]
  rw [ENNReal.ofReal_mul (hp.nonneg s), show k - (t + s) = k - t - s by omega]
  ring

/-- **The potential equation** `V = 1_{k} + RV`: in renewal terms, the renewal equation
`u = δ₀ + p ∗ u` for the lazy chain, where `q` adds a step of length `0` with probability `½`. -/
theorem lazyPot_eq {p : ℕ → ℝ} (hp : IsIncrementLaw p) (k t : ℕ) :
    lazyPot p k t = (if t = k then 1 else 0) + ∫⁻ z, lazyPot p k z ∂lazyRenewalKernel p t := by
  rw [lintegral_lazyRenewalKernel]
  by_cases ht : t ≤ k
  · rw [tsum_mul_lazyPot hp ht]
    have hu := realRenewalSeq_eq hp.zero (k - t)
    simp only [lazyPot, ht, ↓reduceIte]
    have h2 : (2⁻¹ : ℝ≥0∞) * 2 = 1 := ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
    rw [← mul_assoc, ← mul_assoc, h2, one_mul, one_mul]
    by_cases htk : t = k
    · subst htk
      simp only [Nat.sub_self, realRenewalSeq_zero hp.zero, deltaSeq, ↓reduceIte] at hu ⊢
      rw [show realConv p (realRenewalSeq p) 0 = 0 by linarith, ENNReal.ofReal_zero,
        ENNReal.ofReal_one, add_zero, mul_one, one_add_one_eq_two]
    · have hn : k - t ≠ 0 := by omega
      simp only [deltaSeq, hn, ↓reduceIte, zero_add] at hu
      simp only [htk, ↓reduceIte]
      rw [← hu, zero_add, two_mul]
  · have hz : ∀ s, lazyPot p k (t + s) = 0 := fun s => by
      simp only [lazyPot, show ¬ (t + s ≤ k) by omega, ↓reduceIte]
    simp only [hz, mul_zero, tsum_zero]
    simp [lazyPot, ht, show t ≠ k by omega]

/-- The partial potentials `Σ_{j<N} Rʲ(t, {k})` are bounded by `V(t)`. -/
theorem sum_range_lazyRenewalKernel_pow_le {p : ℕ → ℝ} (hp : IsIncrementLaw p) (k N t : ℕ) :
    ∑ j ∈ Finset.range N, (lazyRenewalKernel p ^ j) t {k} ≤ lazyPot p k t := by
  induction N generalizing t with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ', pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton k)]
    have hsum : ∑ j ∈ Finset.range N, (lazyRenewalKernel p ^ (j + 1)) t {k} =
        ∫⁻ z, ∑ j ∈ Finset.range N, (lazyRenewalKernel p ^ j) z {k} ∂lazyRenewalKernel p t := by
      rw [lintegral_finsetSum _ fun j _ => Kernel.measurable_coe _ (measurableSet_singleton k)]
      exact Finset.sum_congr rfl fun j _ => pow_succ_apply _ _ _ (measurableSet_singleton k)
    rw [hsum, lazyPot_eq hp k t, add_comm]
    refine add_le_add ?_ (lintegral_mono fun z => ih z)
    by_cases htk : t = k <;> simp [htk]

/-- The potential satisfies `G = 1_{k} + RG`. -/
theorem tsum_lazyRenewalKernel_pow_eq (p : ℕ → ℝ) (k t : ℕ) :
    ∑' j, (lazyRenewalKernel p ^ j) t {k} = (if t = k then 1 else 0) +
      ∫⁻ z, ∑' j, (lazyRenewalKernel p ^ j) z {k} ∂lazyRenewalKernel p t := by
  rw [tsum_eq_zero_add' ENNReal.summable, pow_zero_apply,
    Measure.dirac_apply' _ (measurableSet_singleton k),
    lintegral_tsum fun j => (Kernel.measurable_coe _ (measurableSet_singleton k)).aemeasurable]
  congr 1
  · by_cases htk : t = k <;> simp [htk]
  · exact tsum_congr fun j => pow_succ_apply _ _ _ (measurableSet_singleton k)

/-- **The lazy renewal potential** `Σⱼ Rʲ(t, {k}) = 2u(k − t)` for `t ≤ k` (and `0` for
`t > k`): the expected number of indices `j` with `Tⱼ = k` is twice the renewal probability, as
each renewal epoch is repeated a geometric number of times (`u₀ = u/(1 − p)` in MT p. 467). -/
theorem tsum_lazyRenewalKernel_pow {p : ℕ → ℝ} (hp : IsIncrementLaw p) (k t : ℕ) :
    ∑' j, (lazyRenewalKernel p ^ j) t {k} = lazyPot p k t := by
  set G : ℕ → ℝ≥0∞ := fun t => ∑' j, (lazyRenewalKernel p ^ j) t {k} with hG
  have hle : ∀ t, G t ≤ lazyPot p k t := fun t =>
    ENNReal.tsum_le_of_sum_range_le fun N => sum_range_lazyRenewalKernel_pow_le hp k N t
  have hgt : ∀ t, k < t → G t = 0 := fun t ht => ENNReal.tsum_eq_zero.2 fun j =>
    measure_mono_null (singleton_subset_iff.2 (show k ∈ Iio t from ht))
      (lazyRenewalKernel_pow_Iio p j t)
  have key : ∀ n t, k - t = n → t ≤ k → G t = lazyPot p k t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t hn ht
      have hsum : ∑' s, ENNReal.ofReal (p s) * G (t + s) =
          ∑' s, ENNReal.ofReal (p s) * lazyPot p k (t + s) := tsum_congr fun s => by
        rcases Nat.eq_zero_or_pos s with rfl | hs
        · simp [hp.zero]
        · by_cases hts : t + s ≤ k
          · rw [ih (k - (t + s)) (by omega) (t + s) rfl hts]
          · rw [hgt _ (by omega)]
            simp only [lazyPot, hts, ↓reduceIte]
      have hGt : G t = (if t = k then 1 else 0) + ∫⁻ z, G z ∂lazyRenewalKernel p t :=
        tsum_lazyRenewalKernel_pow_eq p k t
      rw [lintegral_lazyRenewalKernel, hsum] at hGt
      have hVt := lazyPot_eq hp k t
      rw [lintegral_lazyRenewalKernel] at hVt
      set c := (if t = k then (1 : ℝ≥0∞) else 0) +
        2⁻¹ * ∑' s, ENNReal.ofReal (p s) * lazyPot p k (t + s) with hc
      have hV' : lazyPot p k t = 2⁻¹ * lazyPot p k t + c := by
        conv_lhs => rw [hVt]
        rw [hc]; ring
      have hG' : G t = 2⁻¹ * G t + c := by
        conv_lhs => rw [hGt]
        rw [hc]; ring
      have hfinV := lazyPot_ne_top p k t
      have hfinG : G t ≠ ∞ := ne_top_of_le_ne_top hfinV (hle t)
      have hsolve : ∀ x : ℝ≥0∞, x ≠ ∞ → x = 2⁻¹ * x + c → x = 2 * c := fun x hx h => by
        have h1 : 2⁻¹ * x + 2⁻¹ * x = 2⁻¹ * x + c := by rw [← h, ← two_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
        have h2 : 2⁻¹ * x = c := (ENNReal.add_right_inj (ENNReal.mul_ne_top
          (ENNReal.inv_ne_top.2 two_ne_zero) hx)).1 h1
        rw [← h2, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      rw [hsolve _ hfinG hG', hsolve _ hfinV hV']
  by_cases ht : t ≤ k
  · exact key (k - t) t rfl ht
  · change G t = _
    rw [hgt t (by omega)]
    simp only [lazyPot, ht, ↓reduceIte]

/-! ### Two-time probabilities and monotone paths -/

/-- `{Φⱼ ∈ B}` is an event. -/
theorem measurableSet_coord {X : Type*} [MeasurableSpace X] (j : ℕ) {B : Set X}
    (hB : MeasurableSet B) : MeasurableSet {ω : ℕ → X | ω j ∈ B} :=
  measurable_pi_apply j hB

/-- `P_x(Φⱼ = y, Φⱼ₊₁ ∈ B) = Pʲ(x, {y}) P(y, B)`. -/
theorem pathKernel_coord_eq_inter_succ {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (Q : Kernel X X) [IsMarkovKernel Q] (x : X) (j : ℕ) (y : X)
    {B : Set X} (hB : MeasurableSet B) :
    pathKernel Q x ({ω | ω j = y} ∩ {ω | ω (j + 1) ∈ B}) = (Q ^ j) x {y} * Q y B := by
  have hG : MeasurableSet[natFilt j] {ω : ℕ → X | ω j = y} :=
    measurableSet_coord_natFilt le_rfl (measurableSet_singleton y)
  have hGm : MeasurableSet {ω : ℕ → X | ω j = y} := (natFilt (X := X)).le j _ hG
  have h := setLIntegral_succ Q (Measure.dirac x) hG (measurable_one.indicator hB)
  rw [pathMeasure_dirac] at h
  have hl : ∫⁻ ω in {ω | ω j = y}, B.indicator 1 (ω (j + 1)) ∂pathKernel Q x =
      pathKernel Q x ({ω | ω j = y} ∩ {ω | ω (j + 1) ∈ B}) := by
    have : (fun ω : ℕ → X => B.indicator (1 : X → ℝ≥0∞) (ω (j + 1))) =
        {ω : ℕ → X | ω (j + 1) ∈ B}.indicator 1 := by
      ext ω; by_cases hω : ω (j + 1) ∈ B <;> simp [hω]
    rw [this, lintegral_indicator_one (measurableSet_coord (j + 1) hB),
      Measure.restrict_apply (measurableSet_coord (j + 1) hB), inter_comm]
  have hr : ∫⁻ ω in {ω | ω j = y}, ∫⁻ z, B.indicator 1 z ∂Q (ω j) ∂pathKernel Q x =
      ∫⁻ _ in {ω | ω j = y}, Q y B ∂pathKernel Q x := by
    refine setLIntegral_congr_fun hGm fun ω hω => ?_
    rw [lintegral_indicator_one hB]
    simp only [mem_ofPred_eq] at hω
    rw [hω]
  rw [← hl, h, hr, setLIntegral_const, mul_comm]
  congr 1
  exact pathKernel_coord_mem Q x j (measurableSet_singleton y)

/-- The lazy renewal chain has nondecreasing paths, almost surely. -/
theorem ae_monotone_lazyRenewal {p : ℕ → ℝ} (hp : IsIncrementLaw p) (t : ℕ) :
    haveI := isMarkovKernel_lazyRenewalKernel hp
    ∀ᵐ ω ∂pathKernel (lazyRenewalKernel p) t, ∀ j, ω j ≤ ω (j + 1) := by
  have := isMarkovKernel_lazyRenewalKernel hp
  refine ae_all_iff.2 fun j => ?_
  rw [ae_iff]
  have hset : {ω : ℕ → ℕ | ¬ ω j ≤ ω (j + 1)} =
      ⋃ s, ({ω | ω j = s} ∩ {ω | ω (j + 1) ∈ Iio s}) := by
    ext ω; simp
  rw [hset]
  refine measure_iUnion_null fun s => ?_
  rw [pathKernel_coord_eq_inter_succ _ t j s measurableSet_Iio, lazyRenewalKernel_Iio, mul_zero]

/-! ### Ages -/

/-- The event that the last renewal epoch at or before time `n` is `k`,
`∃ j, Tⱼ = k ≤ n < Tⱼ₊₁`. For `k ≤ n` it is the event `{V⁻(n) = n − k}` for the backward
recurrence (age) chain of MT p. 466. -/
def ageEvent (n k : ℕ) : Set (ℕ → ℕ) := {ω | ∃ j, ω j = k ∧ n < ω (j + 1)}

/-- `ageEvent n k` is the union over `j` of the two-time events. -/
theorem ageEvent_eq_iUnion (n k : ℕ) :
    ageEvent n k = ⋃ j, ({ω : ℕ → ℕ | ω j = k} ∩ {ω | ω (j + 1) ∈ Ioi n}) := by
  ext ω; simp [ageEvent]

/-- Ages are events. -/
theorem measurableSet_ageEvent (n k : ℕ) : MeasurableSet (ageEvent n k) := by
  rw [ageEvent_eq_iUnion]
  exact MeasurableSet.iUnion fun j => (measurableSet_coord j (measurableSet_singleton k)).inter
    (measurableSet_coord (j + 1) measurableSet_Ioi)

/-- On a nondecreasing path, the index in `ageEvent n k` is unique. -/
theorem ageEvent_index_unique {ω : ℕ → ℕ} (hω : ∀ j, ω j ≤ ω (j + 1)) {n k i j : ℕ}
    (hk : k ≤ n) (hi : ω i = k ∧ n < ω (i + 1)) (hj : ω j = k ∧ n < ω (j + 1)) : i = j := by
  have hmono : Monotone ω := monotone_nat_of_le_succ hω
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨hj1, hj2⟩ := hj
  by_contra hij
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have := hmono (show i + 1 ≤ j by omega); omega
  · have := hmono (show j + 1 ≤ i by omega); omega

/-- On a nondecreasing path, the events `ageEvent n k`, `k ≤ n`, are disjoint. -/
theorem ageEvent_disjoint {ω : ℕ → ℕ} (hω : ∀ j, ω j ≤ ω (j + 1)) {n k k' : ℕ} (hk : k ≤ n)
    (hk' : k' ≤ n) (h : ω ∈ ageEvent n k) (h' : ω ∈ ageEvent n k') : k = k' := by
  have hmono : Monotone ω := monotone_nat_of_le_succ hω
  obtain ⟨i, hi1, hi2⟩ := h
  obtain ⟨j, hj1, hj2⟩ := h'
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := hmono (show i + 1 ≤ j by omega); omega
  · omega
  · have := hmono (show j + 1 ≤ i by omega); omega

/-- `R(k, (n, ∞)) = ½ tail(n − k)` for `k ≤ n`. -/
theorem lazyRenewalKernel_Ioi {p : ℕ → ℝ} (hp : IsIncrementLaw p) {n k : ℕ} (hk : k ≤ n) :
    lazyRenewalKernel p k (Ioi n) = 2⁻¹ * ENNReal.ofReal (renewalTail p (n - k)) := by
  rw [lazyRenewalKernel_apply, Measure.map_apply (measurable_of_countable _) measurableSet_Ioi,
    ← lazyLaw_Ioi hp]
  congr 1
  ext s
  simp only [mem_preimage, mem_Ioi]
  omega

/-- **The age distribution**: for `k ≤ n`, the lazy renewal chain from `t` has
`P_t(the last epoch ≤ n is k) = u(k − t) tail(n − k)` (`0` for `t > k`); this is the law of the
age `V⁻(n)` used in (18.10). -/
theorem pathKernel_ageEvent {p : ℕ → ℝ} (hp : IsIncrementLaw p) {n k : ℕ} (hk : k ≤ n)
    (t : ℕ) :
    haveI := isMarkovKernel_lazyRenewalKernel hp
    pathKernel (lazyRenewalKernel p) t (ageEvent n k) =
      lazyPot p k t * (2⁻¹ * ENNReal.ofReal (renewalTail p (n - k))) := by
  have := isMarkovKernel_lazyRenewalKernel hp
  have hmono := ae_monotone_lazyRenewal hp t
  rw [ageEvent_eq_iUnion, measure_iUnion₀]
  · simp_rw [pathKernel_coord_eq_inter_succ _ t _ k measurableSet_Ioi, lazyRenewalKernel_Ioi hp hk]
    rw [ENNReal.tsum_mul_right, tsum_lazyRenewalKernel_pow hp]
  · intro i j hij
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hmono)
    simp only [mem_ofPred_eq]
    intro hω'
    obtain ⟨⟨hi1, hi2⟩, hj1, hj2⟩ := hω
    exact hij (ageEvent_index_unique hω' hk ⟨hi1, hi2⟩ ⟨hj1, hj2⟩)
  · exact fun j => ((measurableSet_coord j (measurableSet_singleton k)).inter
      (measurableSet_coord (j + 1) measurableSet_Ioi)).nullMeasurableSet

/-! ### The coupling inequality -/

/-- The renewal epochs of the first process, `ω ↦ (Tⱼ)ⱼ`. -/
def fstPath (ω : ℕ → ℕ × ℕ) : ℕ → ℕ := fun n => (ω n).1

/-- The renewal epochs of the second process, `ω ↦ (T'ⱼ)ⱼ`. -/
def sndPath (ω : ℕ → ℕ × ℕ) : ℕ → ℕ := fun n => (ω n).2

/-- Nondecreasing paths. -/
def monoPaths : Set (ℕ → ℕ) := {ω | ∀ j, ω j ≤ ω (j + 1)}

/-- Nondecreasing paths form an event. -/
theorem measurableSet_monoPaths : MeasurableSet monoPaths := by
  have : monoPaths = ⋂ j, {ω : ℕ → ℕ | ω j ≤ ω (j + 1)} := by ext; simp [monoPaths]
  rw [this]
  exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply j)
    (measurable_pi_apply (j + 1))

/-- Both coordinates of the pair chain are nondecreasing, almost surely. -/
theorem pairKernel_ae_mono {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) (y : ℕ × ℕ) :
    haveI := isMarkovKernel_pairKernel hp M
    ∀ᵐ ω ∂pathKernel (pairKernel p M) y, fstPath ω ∈ monoPaths ∧ sndPath ω ∈ monoPaths := by
  have := isMarkovKernel_pairKernel hp M
  have := isMarkovKernel_lazyRenewalKernel hp
  have := isMarkovKernel_pathKernel (lazyRenewalKernel p)
  have h1 : pathKernel (pairKernel p M) y {ω | fstPath ω ∈ monoPathsᶜ} = 0 := by
    rw [show {ω | fstPath ω ∈ monoPathsᶜ} = {ω | (fun n => Prod.fst (ω n)) ∈ monoPathsᶜ} from rfl,
      pathKernel_lump_apply _ _ measurable_fst (pairKernel_map_fst hp M) y
        measurableSet_monoPaths.compl]
    exact ae_iff.1 (ae_monotone_lazyRenewal hp y.1)
  have h2 : pathKernel (pairKernel p M) y {ω | sndPath ω ∈ monoPathsᶜ} = 0 := by
    rw [show {ω | sndPath ω ∈ monoPathsᶜ} = {ω | (fun n => Prod.snd (ω n)) ∈ monoPathsᶜ} from rfl,
      pathKernel_lump_apply _ _ measurable_snd (pairKernel_map_snd hp M) y
        measurableSet_monoPaths.compl]
    exact ae_iff.1 (ae_monotone_lazyRenewal hp y.2)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_union_null h1 h2)
  simp only [mem_ofPred_eq, not_and_or] at hω
  rcases hω with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- From a diagonal state, the two ages have the same law: the two coordinates are lazy renewal
chains started at the same epoch. -/
theorem pathKernel_age_fst_eq_snd {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ) {y : ℕ × ℕ}
    (hy : y ∈ pairDiag) (n k : ℕ) :
    haveI := isMarkovKernel_pairKernel hp M
    pathKernel (pairKernel p M) y {ω | fstPath ω ∈ ageEvent n k} =
      pathKernel (pairKernel p M) y {ω | sndPath ω ∈ ageEvent n k} := by
  have := isMarkovKernel_pairKernel hp M
  have := isMarkovKernel_lazyRenewalKernel hp
  rw [show {ω | fstPath ω ∈ ageEvent n k} = {ω | (fun n => Prod.fst (ω n)) ∈ ageEvent n k}
      from rfl, show {ω | sndPath ω ∈ ageEvent n k} = {ω | (fun n => Prod.snd (ω n)) ∈
        ageEvent n k} from rfl,
    pathKernel_lump_apply _ _ measurable_fst (pairKernel_map_fst hp M) y
      (measurableSet_ageEvent n k),
    pathKernel_lump_apply _ _ measurable_snd (pairKernel_map_snd hp M) y
      (measurableSet_ageEvent n k)]
  have : y.1 = y.2 := hy
  rw [this]

/-- The age events are unchanged by the shift to the coupling time, once the common epoch is at
most `n` (the renewal property at `T_ab`, MT p. 466). -/
theorem mem_ageEvent_shift_iff {f : ℕ → ℕ} (hf : f ∈ monoPaths) {j n k : ℕ} (hj : f j ≤ n) :
    shift j f ∈ ageEvent n k ↔ f ∈ ageEvent n k := by
  have hmono : Monotone f := monotone_nat_of_le_succ hf
  constructor
  · rintro ⟨i, hi1, hi2⟩
    exact ⟨j + i, hi1, by simpa [shift, add_assoc] using hi2⟩
  · rintro ⟨i, hi1, hi2⟩
    have hij : j ≤ i := by
      by_contra h
      have := hmono (show i + 1 ≤ j by omega)
      omega
    refine ⟨i - j, ?_, ?_⟩
    · simp only [shift_apply]; rw [Nat.add_sub_cancel' hij]; exact hi1
    · simp only [shift_apply]; rw [show j + (i - j + 1) = i + 1 by omega]; exact hi2

/-- `fstPath` is measurable. -/
theorem measurable_fstPath : Measurable fstPath :=
  measurable_pi_iff.2 fun n => measurable_fst.comp (measurable_pi_apply n)

/-- `sndPath` is measurable. -/
theorem measurable_sndPath : Measurable sndPath :=
  measurable_pi_iff.2 fun n => measurable_snd.comp (measurable_pi_apply n)

/-- The diagonal is measurable. -/
theorem measurableSet_pairDiag : MeasurableSet pairDiag := (Set.to_countable _).measurableSet

/-- The **coupling event** at time `n`: the two processes have had a common renewal epoch
`T_ab ≤ n`. -/
def coupledBy (n : ℕ) : Set (ℕ → ℕ × ℕ) :=
  {ω | stoppedState (firstHit pairDiag) ω ∈ {y : ℕ × ℕ | y.1 ≤ n}} ∩
    {ω | firstHit pairDiag ω ≠ ⊤}

/-- The coupling event is measurable. -/
theorem measurableSet_coupledBy (n : ℕ) : MeasurableSet (coupledBy n) := by
  have hτ := (proposition_3_4_4 measurableSet_pairDiag).2
  exact (hτ.measurableSpace_le _ (measurableSet_stoppedField_stoppedState hτ
    (Set.to_countable _).measurableSet)).inter (measurableSet_ne_top
      (proposition_3_4_4 measurableSet_pairDiag).2)

/-- A null event under every `P_y` is null under `P_μ`. -/
theorem pathMeasure_null_of_forall {Y : Type*} [MeasurableSpace Y] (K : Kernel Y Y)
    [IsMarkovKernel K] (μ : Measure Y) {S : Set (ℕ → Y)} (hS : MeasurableSet S)
    (h : ∀ y, pathKernel K y S = 0) : pathMeasure K μ S = 0 := by
  rw [pathMeasure_eq_comp, Measure.bind_apply hS (Kernel.aemeasurable _)]
  simp [h]

/-- The set of paths with both coordinates nondecreasing. -/
def pairMono : Set (ℕ → ℕ × ℕ) := {ω | fstPath ω ∈ monoPaths ∧ sndPath ω ∈ monoPaths}

/-- `pairMono` is an event. -/
theorem measurableSet_pairMono : MeasurableSet pairMono :=
  (measurable_fstPath measurableSet_monoPaths).inter (measurable_sndPath measurableSet_monoPaths)

/-- Both coordinates are nondecreasing `P_μ`-a.s. -/
theorem pathMeasure_pairMono_compl {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ)
    (μ : Measure (ℕ × ℕ)) :
    haveI := isMarkovKernel_pairKernel hp M
    pathMeasure (pairKernel p M) μ pairMonoᶜ = 0 := by
  have := isMarkovKernel_pairKernel hp M
  exact pathMeasure_null_of_forall _ μ measurableSet_pairMono.compl fun y =>
    ae_iff.1 (pairKernel_ae_mono hp M y)

/-- **Equality after coupling**: on the event that the coupling has happened by time `n`, the two
age events have the same probability (the decomposition over `T_ab` on MT p. 466). -/
theorem pathMeasure_age_inter_coupledBy {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ)
    (μ : Measure (ℕ × ℕ)) [IsProbabilityMeasure μ] (n k : ℕ) :
    haveI := isMarkovKernel_pairKernel hp M
    pathMeasure (pairKernel p M) μ ({ω | fstPath ω ∈ ageEvent n k} ∩ coupledBy n) =
      pathMeasure (pairKernel p M) μ ({ω | sndPath ω ∈ ageEvent n k} ∩ coupledBy n) := by
  have := isMarkovKernel_pairKernel hp M
  have hτ := (proposition_3_4_4 measurableSet_pairDiag).2
  set τ := firstHit pairDiag with hτdef
  set P := pathMeasure (pairKernel p M) μ with hP
  have hA : MeasurableSet[hτ.measurableSpace]
      {ω | stoppedState τ ω ∈ {y : ℕ × ℕ | y.1 ≤ n}} :=
    measurableSet_stoppedField_stoppedState hτ (Set.to_countable _).measurableSet
  have hC := measurableSet_coupledBy n
  have hEA : MeasurableSet {ω | fstPath ω ∈ ageEvent n k} :=
    measurable_fstPath (measurableSet_ageEvent n k)
  have hEB : MeasurableSet {ω | sndPath ω ∈ ageEvent n k} :=
    measurable_sndPath (measurableSet_ageEvent n k)
  have hmono := pathMeasure_pairMono_compl hp M μ
  -- the strong Markov property at `τ` for each of the two age events
  have hside : ∀ (g : (ℕ → ℕ × ℕ) → ℕ → ℕ), Measurable g →
      (∀ ω j, g (shift j ω) = shift j (g ω)) →
      (∀ ω, ω ∈ pairMono → g ω ∈ monoPaths) →
      (∀ ω, τ ω ≠ ⊤ → g ω (τ ω).untopA = (stoppedState τ ω).1) →
      P ({ω | g ω ∈ ageEvent n k} ∩ coupledBy n) =
        ∫⁻ ω in coupledBy n, pathKernel (pairKernel p M) (stoppedState τ ω)
          {ω' | g ω' ∈ ageEvent n k} ∂P := by
    intro g hg hgshift hgmono hgstop
    have hE : MeasurableSet {ω | g ω ∈ ageEvent n k} := hg (measurableSet_ageEvent n k)
    have hSM := strong_markov_lintegral (pairKernel p M) μ hτ hA
      (measurable_one.indicator hE)
    change ∫⁻ ω in coupledBy n, {ω | g ω ∈ ageEvent n k}.indicator 1 (shiftAt τ ω) ∂P =
      ∫⁻ ω in coupledBy n, ∫⁻ ω', {ω | g ω ∈ ageEvent n k}.indicator 1 ω'
        ∂pathKernel (pairKernel p M) (stoppedState τ ω) ∂P at hSM
    have hR : ∫⁻ ω in coupledBy n, pathKernel (pairKernel p M) (stoppedState τ ω)
        {ω' | g ω' ∈ ageEvent n k} ∂P = ∫⁻ ω in coupledBy n, ∫⁻ ω',
          {ω | g ω ∈ ageEvent n k}.indicator 1 ω' ∂pathKernel (pairKernel p M)
            (stoppedState τ ω) ∂P := by
      simp_rw [lintegral_indicator_one hE]
    have hL : ∫⁻ ω in coupledBy n, {ω | g ω ∈ ageEvent n k}.indicator 1 (shiftAt τ ω) ∂P =
        ∫⁻ ω in coupledBy n, {ω | g ω ∈ ageEvent n k}.indicator 1 ω ∂P := by
      refine setLIntegral_congr_fun_ae hC ?_
      have hae : ∀ᵐ ω ∂P, ω ∈ pairMono := by
        rw [ae_iff]; exact hmono
      filter_upwards [hae] with ω hω hωC
      have hne : τ ω ≠ ⊤ := hωC.2
      have hle : (stoppedState τ ω).1 ≤ n := hωC.1
      have h1 : g (shiftAt τ ω) = shift (τ ω).untopA (g ω) := hgshift ω _
      have h2 := mem_ageEvent_shift_iff (k := k) (hgmono ω hω)
        (show g ω (τ ω).untopA ≤ n by rw [hgstop ω hne]; exact hle)
      by_cases hmem : g ω ∈ ageEvent n k
      · have hmem' : g (shiftAt τ ω) ∈ ageEvent n k := by rw [h1]; exact h2.2 hmem
        rw [indicator_of_mem (show shiftAt τ ω ∈ {ω | g ω ∈ ageEvent n k} from hmem'),
          indicator_of_mem (show ω ∈ {ω | g ω ∈ ageEvent n k} from hmem)]
        rfl
      · have hmem' : g (shiftAt τ ω) ∉ ageEvent n k := by rw [h1]; exact fun h => hmem (h2.1 h)
        rw [indicator_of_notMem (show shiftAt τ ω ∉ {ω | g ω ∈ ageEvent n k} from hmem'),
          indicator_of_notMem (show ω ∉ {ω | g ω ∈ ageEvent n k} from hmem)]
    rw [hR, ← hSM, hL, lintegral_indicator_one hE, Measure.restrict_apply hE]
  have hfst := hside fstPath measurable_fstPath (fun ω j => rfl) (fun ω hω => hω.1)
    (fun ω _ => rfl)
  have hsnd := hside sndPath measurable_sndPath (fun ω j => rfl) (fun ω hω => hω.2)
    (fun ω hne => (stoppedState_firstHit_mem pairDiag hne).symm)
  rw [hfst, hsnd]
  refine setLIntegral_congr_fun hC fun ω hω => ?_
  exact pathKernel_age_fst_eq_snd hp M (stoppedState_firstHit_mem pairDiag hω.2) n k

/-- `P_μ(T_ab ≤ n) → 1`: the complement of the coupling event has vanishing probability. -/
theorem tendsto_pathMeasure_coupledBy_compl {p : ℕ → ℝ} (hp : IsIncrementLaw p) {M : ℕ}
    (hM : ∀ d : ℕ, (∀ n ≤ M, 0 < p n → d ∣ n) → d = 1) (μ : Measure (ℕ × ℕ))
    [IsProbabilityMeasure μ] :
    haveI := isMarkovKernel_pairKernel hp M
    Tendsto (fun n => pathMeasure (pairKernel p M) μ (coupledBy n)ᶜ) atTop (𝓝 0) := by
  have := isMarkovKernel_pairKernel hp M
  have := isProbabilityMeasure_pathMeasure (pairKernel p M) μ
  have hmono : Monotone coupledBy := fun m n hmn ω hω => ⟨le_trans hω.1 hmn, hω.2⟩
  have hU : ⋃ n, coupledBy n = {ω | firstHit pairDiag ω ≠ ⊤} := by
    ext ω
    simp only [mem_iUnion, coupledBy, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨_, h⟩ => h.2, fun h => ⟨_, le_rfl, h⟩⟩
  have hτ := (proposition_3_4_4 measurableSet_pairDiag).2
  have h1 : pathMeasure (pairKernel p M) μ {ω | firstHit pairDiag ω ≠ ⊤} = 1 := by
    rw [pathMeasure_eq_comp, Measure.bind_apply (measurableSet_ne_top hτ)
      (Kernel.aemeasurable _)]
    simp_rw [pairKernel_firstHit_ne_top hp hM]
    simp
  have ht := tendsto_measure_iUnion_atTop (μ := pathMeasure (pairKernel p M) μ) hmono
  rw [hU, h1] at ht
  have h2 := ENNReal.Tendsto.sub tendsto_const_nhds ht (Or.inl ENNReal.one_ne_top)
  rw [tsub_self] at h2
  refine h2.congr fun n => ?_
  rw [Function.comp_apply, prob_compl_eq_one_sub (measurableSet_coupledBy n)]

/-- The age events before coupling have total probability at most `P(T_ab > n)`. -/
theorem sum_age_diff_coupledBy_le {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ)
    (μ : Measure (ℕ × ℕ)) (n : ℕ) {g : (ℕ → ℕ × ℕ) → ℕ → ℕ} (hg : Measurable g)
    (hgmono : ∀ ω, ω ∈ pairMono → g ω ∈ monoPaths) :
    haveI := isMarkovKernel_pairKernel hp M
    ∑ k ∈ Finset.range (n + 1),
        pathMeasure (pairKernel p M) μ ({ω | g ω ∈ ageEvent n k} \ coupledBy n) ≤
      pathMeasure (pairKernel p M) μ (coupledBy n)ᶜ := by
  have := isMarkovKernel_pairKernel hp M
  have hmono := pathMeasure_pairMono_compl hp M μ
  rw [← measure_biUnion_finset₀]
  · exact measure_mono (iUnion₂_subset fun k _ => sdiff_subset_compl _ _)
  · intro k hk k' hk' hkk'
    refine measure_mono_null (fun ω hω => ?_) hmono
    intro hω'
    exact hkk' (ageEvent_disjoint (hgmono ω hω') (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk')) hω.1.1 hω.2.1)
  · exact fun k _ => ((hg (measurableSet_ageEvent n k)).diff
      (measurableSet_coupledBy n)).nullMeasurableSet

/-- **The coupling inequality** (18.9)–(18.10): the total variation distance between the age
distributions of the two coupled processes at time `n` is at most `2 P(T_ab > n)`. -/
theorem sum_abs_age_sub_le {p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ)
    (μ : Measure (ℕ × ℕ)) [IsProbabilityMeasure μ] (n : ℕ) :
    haveI := isMarkovKernel_pairKernel hp M
    ∑ k ∈ Finset.range (n + 1),
        |(pathMeasure (pairKernel p M) μ {ω | fstPath ω ∈ ageEvent n k}).toReal -
          (pathMeasure (pairKernel p M) μ {ω | sndPath ω ∈ ageEvent n k}).toReal| ≤
      2 * (pathMeasure (pairKernel p M) μ (coupledBy n)ᶜ).toReal := by
  have := isMarkovKernel_pairKernel hp M
  have := isProbabilityMeasure_pathMeasure (pairKernel p M) μ
  set P := pathMeasure (pairKernel p M) μ with hP
  have hC := measurableSet_coupledBy n
  have hsplit : ∀ {E : Set (ℕ → ℕ × ℕ)}, MeasurableSet E →
      (P E).toReal = (P (E ∩ coupledBy n)).toReal + (P (E \ coupledBy n)).toReal := fun hE => by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_inter_add_sdiff _ hC]
  have hk : ∀ k, |(P {ω | fstPath ω ∈ ageEvent n k}).toReal -
      (P {ω | sndPath ω ∈ ageEvent n k}).toReal| ≤
        (P ({ω | fstPath ω ∈ ageEvent n k} \ coupledBy n)).toReal +
          (P ({ω | sndPath ω ∈ ageEvent n k} \ coupledBy n)).toReal := fun k => by
    rw [hsplit (E := {ω | fstPath ω ∈ ageEvent n k})
        (measurable_fstPath (measurableSet_ageEvent n k)),
      hsplit (E := {ω | sndPath ω ∈ ageEvent n k})
        (measurable_sndPath (measurableSet_ageEvent n k)),
      pathMeasure_age_inter_coupledBy hp M μ n k]
    have h1 := (P ({ω | fstPath ω ∈ ageEvent n k} \ coupledBy n)).toReal_nonneg
    have h2 := (P ({ω | sndPath ω ∈ ageEvent n k} \ coupledBy n)).toReal_nonneg
    rw [abs_le]; constructor <;> linarith
  have hsum : ∀ {g : (ℕ → ℕ × ℕ) → ℕ → ℕ}, Measurable g →
      (∀ ω, ω ∈ pairMono → g ω ∈ monoPaths) →
      ∑ k ∈ Finset.range (n + 1), (P ({ω | g ω ∈ ageEvent n k} \ coupledBy n)).toReal ≤
        (P (coupledBy n)ᶜ).toReal := fun hg hgm => by
    rw [← ENNReal.toReal_sum fun k _ => measure_ne_top _ _]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (sum_age_diff_coupledBy_le hp M μ n hg hgm)
  calc _ ≤ ∑ k ∈ Finset.range (n + 1),
        ((P ({ω | fstPath ω ∈ ageEvent n k} \ coupledBy n)).toReal +
          (P ({ω | sndPath ω ∈ ageEvent n k} \ coupledBy n)).toReal) :=
        Finset.sum_le_sum fun k _ => hk k
    _ = _ := Finset.sum_add_distrib
    _ ≤ (P (coupledBy n)ᶜ).toReal + (P (coupledBy n)ᶜ).toReal :=
        add_le_add (hsum measurable_fstPath fun ω hω => hω.1)
          (hsum measurable_sndPath fun ω hω => hω.2)
    _ = _ := by ring

/-! ### Delayed laws and the identification of the ages -/

/-- The law of a delay sequence `a ≥ 0`, `Σ a = 1`, is a probability. -/
theorem isProbabilityMeasure_lawMeasure_of_hasSum {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (ha1 : HasSum a 1) : IsProbabilityMeasure (lawMeasure a) := by
  refine ⟨?_⟩
  rw [measure_univ_eq_tsum_singleton]
  simp_rw [lawMeasure_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg ha ha1.summable, ha1.tsum_eq, ENNReal.ofReal_one]

/-- `∫ f d(Σ a(t) δₜ) = Σ a(t) f(t)`. -/
theorem lintegral_lawMeasure_eq_tsum (a : ℕ → ℝ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ t, f t ∂lawMeasure a = ∑' t, ENNReal.ofReal (a t) * f t := by
  rw [lawMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- `a ∗ u ≥ 0`. -/
theorem delayedRenewal_nonneg {a p : ℕ → ℝ} (hp : IsIncrementLaw p) (ha : ∀ n, 0 ≤ a n)
    (k : ℕ) : 0 ≤ delayedRenewal a p k := by
  rw [delayedRenewal, realConv_eq_sum_range]
  exact Finset.sum_nonneg fun t _ => mul_nonneg (ha t) (realRenewalSeq_nonneg hp _)

/-- `Σₜ a(t) V(t) = 2 (a ∗ u)(k)`. -/
theorem tsum_mul_lazyPot_delay {a p : ℕ → ℝ} (hp : IsIncrementLaw p) (ha : ∀ n, 0 ≤ a n)
    (k : ℕ) :
    ∑' t, ENNReal.ofReal (a t) * lazyPot p k t = 2 * ENNReal.ofReal (delayedRenewal a p k) := by
  rw [tsum_eq_sum (s := Finset.range (k + 1)) fun t ht => by
    have : ¬ t ≤ k := fun h => ht (Finset.mem_range.2 (Nat.lt_succ_of_le h))
    simp [lazyPot, this]]
  rw [delayedRenewal, realConv_eq_sum_range, ENNReal.ofReal_sum_of_nonneg fun t _ =>
    mul_nonneg (ha t) (realRenewalSeq_nonneg hp _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
  simp only [lazyPot, ht', ↓reduceIte]
  rw [ENNReal.ofReal_mul (ha t)]
  ring

/-- `2x · (½ y) = xy` in `ℝ≥0∞`, for reals `x ≥ 0`. -/
theorem pot_half_mul {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    2 * ENNReal.ofReal x * (2⁻¹ * ENNReal.ofReal y) = ENNReal.ofReal (x * y) := by
  rw [ENNReal.ofReal_mul hx, mul_mul_mul_comm,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- **The age law of a delayed process**: with independent delays `S₀ ~ a`, `S'₀ ~ b`, the first
coordinate has `P(the last epoch ≤ n is k) = (a ∗ u)(k) tail(n − k)` (MT (18.10)). -/
theorem pathMeasure_fst_ageEvent {a b p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hb1 : HasSum b 1)
    {n k : ℕ} (hk : k ≤ n) :
    haveI := isMarkovKernel_pairKernel hp M
    pathMeasure (pairKernel p M) ((lawMeasure a).prod (lawMeasure b))
        {ω | fstPath ω ∈ ageEvent n k} =
      ENNReal.ofReal (delayedRenewal a p k * renewalTail p (n - k)) := by
  have := isMarkovKernel_pairKernel hp M
  have := isMarkovKernel_lazyRenewalKernel hp
  have := isProbabilityMeasure_lawMeasure_of_hasSum hb hb1
  have hE : MeasurableSet {ω | fstPath ω ∈ ageEvent n k} :=
    measurable_fstPath (measurableSet_ageEvent n k)
  rw [pathMeasure_eq_comp, Measure.bind_apply hE (Kernel.aemeasurable _)]
  have hy : ∀ y : ℕ × ℕ, pathKernel (pairKernel p M) y {ω | fstPath ω ∈ ageEvent n k} =
      lazyPot p k y.1 * (2⁻¹ * ENNReal.ofReal (renewalTail p (n - k))) := fun y => by
    rw [show {ω | fstPath ω ∈ ageEvent n k} = {ω | (fun n => Prod.fst (ω n)) ∈ ageEvent n k}
      from rfl, pathKernel_lump_apply _ _ measurable_fst (pairKernel_map_fst hp M) y
        (measurableSet_ageEvent n k), pathKernel_ageEvent hp hk]
  simp_rw [hy]
  rw [lintegral_prod _ (measurable_of_countable _).aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [lintegral_mul_const _ (measurable_of_countable _), lintegral_lawMeasure_eq_tsum,
    tsum_mul_lazyPot_delay hp ha]
  exact pot_half_mul (delayedRenewal_nonneg hp ha k) _

/-- The same for the second coordinate, with the delay `b`. -/
theorem pathMeasure_snd_ageEvent {a b p : ℕ → ℝ} (hp : IsIncrementLaw p) (M : ℕ)
    (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1) (hb : ∀ n, 0 ≤ b n)
    {n k : ℕ} (hk : k ≤ n) :
    haveI := isMarkovKernel_pairKernel hp M
    pathMeasure (pairKernel p M) ((lawMeasure a).prod (lawMeasure b))
        {ω | sndPath ω ∈ ageEvent n k} =
      ENNReal.ofReal (delayedRenewal b p k * renewalTail p (n - k)) := by
  have := isMarkovKernel_pairKernel hp M
  have := isMarkovKernel_lazyRenewalKernel hp
  have := isProbabilityMeasure_lawMeasure_of_hasSum ha ha1
  have hE : MeasurableSet {ω | sndPath ω ∈ ageEvent n k} :=
    measurable_sndPath (measurableSet_ageEvent n k)
  rw [pathMeasure_eq_comp, Measure.bind_apply hE (Kernel.aemeasurable _)]
  have hy : ∀ y : ℕ × ℕ, pathKernel (pairKernel p M) y {ω | sndPath ω ∈ ageEvent n k} =
      lazyPot p k y.2 * (2⁻¹ * ENNReal.ofReal (renewalTail p (n - k))) := fun y => by
    rw [show {ω | sndPath ω ∈ ageEvent n k} = {ω | (fun n => Prod.snd (ω n)) ∈ ageEvent n k}
      from rfl, pathKernel_lump_apply _ _ measurable_snd (pairKernel_map_snd hp M) y
        (measurableSet_ageEvent n k), pathKernel_ageEvent hp hk]
  set c := 2⁻¹ * ENNReal.ofReal (renewalTail p (n - k)) with hc
  simp_rw [hy]
  rw [lintegral_prod _ (measurable_of_countable _).aemeasurable]
  have hinner : ∫⁻ y, lazyPot p k y * c ∂lawMeasure b =
      2 * ENNReal.ofReal (delayedRenewal b p k) * c := by
    rw [lintegral_mul_const _ (measurable_of_countable _), lintegral_lawMeasure_eq_tsum,
      tsum_mul_lazyPot_delay hp hb]
  simp only [hinner]
  rw [lintegral_const, measure_univ, mul_one, hc]
  exact pot_half_mul (delayedRenewal_nonneg hp hb k) _

/-! ### Theorem 18.1.1 -/

/-- **Theorem 18.1.1**, (18.7) (MT p. 465): for an aperiodic increment law `p` (finite mean not
needed) and delay laws `a`, `b`, `|a ∗ u − b ∗ u| ∗ p̄ (n) → 0`, where
`p̄(m) = tail(m) = Σ_{j > m} p(j)`. This is the total variation distance between the age
distributions at time `n`, (18.10); the proof is the book's Ornstein coupling of the increments,
with the lazy law `p⁰` of p. 467. -/
theorem theorem_18_1_1_ii {a b p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1) (hb : ∀ n, 0 ≤ b n) (hb1 : HasSum b 1) :
    Tendsto (realConv (fun k => |delayedRenewal a p k - delayedRenewal b p k|) (renewalTail p))
      atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := exists_aperiodic_level hp hap
  have := isMarkovKernel_pairKernel hp M
  have := isProbabilityMeasure_lawMeasure_of_hasSum ha ha1
  have := isProbabilityMeasure_lawMeasure_of_hasSum hb hb1
  set μ := (lawMeasure a).prod (lawMeasure b) with hμ
  have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_pathMeasure_coupledBy_compl hp hM μ)
  rw [ENNReal.toReal_zero] at hlim
  have hlim2 := hlim.const_mul 2
  rw [mul_zero] at hlim2
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim2
  · rw [realConv_eq_sum_range]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (renewalTail_nonneg hp _)
  · refine le_trans (le_of_eq ?_) (sum_abs_age_sub_le hp M μ n)
    rw [realConv_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [pathMeasure_fst_ageEvent hp M ha hb hb1 hk', pathMeasure_snd_ageEvent hp M ha ha1 hb hk',
      ENNReal.toReal_ofReal (mul_nonneg (delayedRenewal_nonneg hp ha k)
        (renewalTail_nonneg hp _)),
      ENNReal.toReal_ofReal (mul_nonneg (delayedRenewal_nonneg hp hb k)
        (renewalTail_nonneg hp _)), ← sub_mul, abs_mul,
      abs_of_nonneg (renewalTail_nonneg hp _)]

/-- **Theorem 18.1.1**, (18.6) (MT p. 465): `|a ∗ u − b ∗ u|(n) → 0` for an aperiodic increment
law, with or without finite mean. This is Theorem 13.2.2, whose analytic proof does not use
`m_p < ∞`. -/
theorem theorem_18_1_1_i {a b p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p)
    (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1) (hb : ∀ n, 0 ≤ b n) (hb1 : HasSum b 1) :
    Tendsto (fun n => |delayedRenewal a p n - delayedRenewal b p n|) atTop (𝓝 0) :=
  theorem_13_2_2 hp hap ha ha1 hb hb1

/-- A companion of (18.7) with the increment law `p` in place of its tail:
`|a ∗ u − b ∗ u| ∗ p (n) → 0`. This follows from (18.6) by dominated convergence (Lemma D.7.1),
since `p` is summable; for the tail `p̄`, which is not summable in the null case, it is the
content of Theorem 18.1.1 (`theorem_18_1_1_ii`). -/
theorem tendsto_realConv_abs_sub_delayedRenewal_incr {a b p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p)
    (ha : ∀ n, 0 ≤ a n) (ha1 : HasSum a 1) (hb : ∀ n, 0 ≤ b n) (hb1 : HasSum b 1) :
    Tendsto (realConv (fun k => |delayedRenewal a p k - delayedRenewal b p k|) p)
      atTop (𝓝 0) := by
  rw [realConv_comm]
  have h := lemma_D_7_1 hp.nonneg hp.hasSum.summable (theorem_18_1_1_i hp hap ha ha1 hb hb1)
  rwa [zero_mul] at h

end MeynTweedie.GeneralizedDrift

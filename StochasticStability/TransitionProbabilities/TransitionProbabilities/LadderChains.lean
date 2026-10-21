/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TransitionProbabilities.Kernels
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi

/-!
# Ladder chains and the GI/G/1 queue (MT §3.5.4)

Meyn and Tweedie, §3.5.4, pp. 70–71.

* `ladderKernel Λ Λ*`: the ladder chain (3.40) on `ℤ₊ × ℝ`, with row `i` putting `Λ*ᵢ(x, ·)` on
  rung `0` and `Λ_{i−j+1}(x, ·)` on rungs `j = 1, …, i + 1`: `eq_3_40_zero`, `eq_3_40_mid`,
  `eq_3_40_up`. It is translation invariant above rung `0` and skip-free to the right
  (`ladderKernel_translate`, the matrix display of p. 71), and it is a Markov kernel when every
  row has mass one (`isMarkovKernel_ladderKernel`).
* The GI/G/1 kernels: `resEpoch` (the service renewal process started at residual service `x`),
  `ladderP` (3.41), `gig1Lambda` with **(3.42)** (`eq_3_42`), `gig1LambdaStar` with **(3.43)**
  (`eq_3_43`), and the ladder chain `gig1Ladder`. Its row masses are `Σₖ Λₖ(x, ℝ)`
  (`gig1Ladder_rowSum`), so it is Markov when that sum is one (`isMarkovKernel_gig1Ladder`).
  The sum is one when service and interarrival times are nonnegative and services are not
  almost surely zero (`gig1Lambda_tsum_univ`, by the strong law of large numbers applied to the
  truncated services), so `gig1Ladder` is then a Markov kernel
  (`isMarkovKernel_gig1Ladder_of_pos`).

**See also.** That the embedded GI/G/1 process `(Nₙ, Rₙ)` built from the primitives of the
queue is a Markov chain with kernel `gig1Ladder` ("it is easy to verify", p. 71) is
`gig1_isMarkovChain` in `GIG1Embedding`. The book's reference to "(3.41)" for the form of `Φ` on
p. 71 means the ladder structure (3.40).
-/

namespace MeynTweedie.TransitionProbabilities

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

/-- Row `i` of the ladder chain (3.40): mass `Λ*ᵢ(x, ·)` on rung `0` and `Λ_{i+1−j}(x, ·)` on
rung `j = 1, …, i + 1` (written with `k = i + 1 − j ∈ {0, …, i}`). -/
noncomputable def ladderRow (Λ Λs : ℕ → Kernel ℝ ℝ) (i : ℕ) : Kernel ℝ (ℕ × ℝ) :=
  (Λs i).map (Prod.mk 0) + Kernel.sum fun k : Fin (i + 1) => (Λ k).map (Prod.mk (i + 1 - k))

/-- The ladder chain on `ℤ₊ × ℝ` (MT (3.40), p. 70) built from substochastic kernels
`Λₖ`, `Λ*ᵢ` on `ℝ`: `P(i, x; j × A) = Λ_{i−j+1}(x, A)` for `1 ≤ j ≤ i + 1`,
`P(i, x; 0 × A) = Λ*ᵢ(x, A)` and `0` above rung `i + 1`. -/
noncomputable def ladderKernel (Λ Λs : ℕ → Kernel ℝ ℝ) : Kernel (ℕ × ℝ) (ℕ × ℝ) where
  toFun p := ladderRow Λ Λs p.1 p.2
  measurable' := measurable_from_prod_countable_right fun i => (ladderRow Λ Λs i).measurable

/-- The ladder kernel at `(i, x)` is row `i` at `x`. -/
theorem ladderKernel_apply (Λ Λs : ℕ → Kernel ℝ ℝ) (i : ℕ) (x : ℝ) :
    ladderKernel Λ Λs (i, x) = ladderRow Λ Λs i x := rfl

/-- Placing a kernel on rung `m`: its mass on `{j} × A` is `κ(x, A)` if `j = m`, else `0`. -/
theorem map_prodMk_apply_prod (κ : Kernel ℝ ℝ) (m j : ℕ) (x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    κ.map (Prod.mk m) x ({j} ×ˢ A) = if j = m then κ x A else 0 := by
  rw [Kernel.map_apply' _ measurable_prodMk_left x ((measurableSet_singleton j).prod hA)]
  by_cases h : j = m
  · subst h
    simp only [ite_true]
    congr 1
    ext y
    simp
  · simp only [h, ite_false]
    convert measure_empty (μ := κ x)
    ext y
    simp only [mem_preimage, mem_prod, mem_singleton_iff, mem_empty_iff_false, iff_false,
      not_and]
    exact fun h' => absurd h'.symm h

/-- The mass that row `i` puts on `{j} × A`. -/
theorem ladderRow_apply_prod (Λ Λs : ℕ → Kernel ℝ ℝ) (i j : ℕ) (x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ladderRow Λ Λs i x ({j} ×ˢ A) = (if j = 0 then Λs i x A else 0) +
      ∑ k : Fin (i + 1), if j = i + 1 - k then Λ k x A else 0 := by
  rw [ladderRow, FunLike.coe_add, Pi.add_apply, Measure.add_apply,
    Kernel.sum_apply' _ _ ((measurableSet_singleton j).prod hA), tsum_fintype,
    map_prodMk_apply_prod _ _ _ _ hA]
  simp_rw [map_prodMk_apply_prod _ _ _ _ hA]

/-- (3.40), rung `0`: `P(i, x; 0 × A) = Λ*ᵢ(x, A)`. -/
theorem eq_3_40_zero (Λ Λs : ℕ → Kernel ℝ ℝ) (i : ℕ) (x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) : ladderKernel Λ Λs (i, x) ({0} ×ˢ A) = Λs i x A := by
  rw [ladderKernel_apply, ladderRow_apply_prod _ _ _ _ _ hA]
  simp only [ite_true]
  rw [Finset.sum_eq_zero fun k _ => ?_, add_zero]
  have : (k : ℕ) ≤ i := Nat.lt_succ_iff.1 k.2
  simp only [ite_eq_right_iff]
  intro h
  omega

/-- (3.40), rungs `1, …, i + 1`: `P(i, x; j × A) = Λ_{i−j+1}(x, A)`. -/
theorem eq_3_40_mid (Λ Λs : ℕ → Kernel ℝ ℝ) {i j : ℕ} (hj : 1 ≤ j) (hji : j ≤ i + 1) (x : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ladderKernel Λ Λs (i, x) ({j} ×ˢ A) = Λ (i + 1 - j) x A := by
  rw [ladderKernel_apply, ladderRow_apply_prod _ _ _ _ _ hA]
  simp only [show j ≠ 0 by omega, ite_false, zero_add]
  rw [Finset.sum_eq_single ⟨i + 1 - j, by omega⟩]
  · have h : j = i + 1 - (i + 1 - j) := by omega
    simp [← h]
  · intro k _ hk
    simp only [ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext (by simp only; omega)) hk
  · simp

/-- (3.40), skip-free to the right: `P(i, x; j × A) = 0` for `j > i + 1`. -/
theorem eq_3_40_up (Λ Λs : ℕ → Kernel ℝ ℝ) {i j : ℕ} (hji : i + 1 < j) (x : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) : ladderKernel Λ Λs (i, x) ({j} ×ˢ A) = 0 := by
  rw [ladderKernel_apply, ladderRow_apply_prod _ _ _ _ _ hA]
  simp only [show j ≠ 0 by omega, ite_false, zero_add]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [ite_eq_right_iff]
  intro h
  omega

/-- Translation invariance away from rung `0` (MT p. 71): `P(i + 1, x; (j + 1) × A) =
P(i, x; j × A)` for `j ≥ 1`, as in the matrix display of p. 71. -/
theorem ladderKernel_translate (Λ Λs : ℕ → Kernel ℝ ℝ) {i j : ℕ} (hj : 1 ≤ j) (x : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ladderKernel Λ Λs (i + 1, x) ({j + 1} ×ˢ A) = ladderKernel Λ Λs (i, x) ({j} ×ˢ A) := by
  by_cases hji : j ≤ i + 1
  · rw [eq_3_40_mid Λ Λs (by omega) (by omega) x hA, eq_3_40_mid Λ Λs hj hji x hA]
    rw [show i + 1 + 1 - (j + 1) = i + 1 - j by omega]
  · rw [eq_3_40_up Λ Λs (by omega) x hA, eq_3_40_up Λ Λs (by omega) x hA]

/-- The ladder chain is a Markov kernel when each row has total mass one,
`Λ*ᵢ(x, ℝ) + Σ_{k ≤ i} Λₖ(x, ℝ) = 1`. -/
theorem isMarkovKernel_ladderKernel (Λ Λs : ℕ → Kernel ℝ ℝ)
    (h : ∀ i x, Λs i x univ + ∑ k ∈ Finset.range (i + 1), Λ k x univ = 1) :
    IsMarkovKernel (ladderKernel Λ Λs) := by
  refine ⟨fun p => ⟨?_⟩⟩
  obtain ⟨i, x⟩ := p
  rw [ladderKernel_apply, ladderRow, FunLike.coe_add, Pi.add_apply, Measure.add_apply,
    Kernel.sum_apply' _ _ MeasurableSet.univ, tsum_fintype,
    Kernel.map_apply' _ measurable_prodMk_left x MeasurableSet.univ, preimage_univ]
  simp_rw [Kernel.map_apply' _ measurable_prodMk_left x MeasurableSet.univ, preimage_univ]
  rw [← h i x, Fin.sum_univ_eq_sum_range (fun k => Λ k x univ)]

/-- Renewal epochs of the service process started with residual service `x` (MT p. 71):
`Z₀ = 0`, `Z₁ = x` and `Z_{k+1} = x + S₁ + ⋯ + Sₖ`, with service times `uᵢ = S_{i+1}`. -/
def resEpoch (x : ℝ) (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => x + ∑ i ∈ Finset.range k, u i

/-- Each renewal epoch is jointly measurable in `(x, u)`. -/
theorem measurable_resEpoch (k : ℕ) :
    Measurable fun p : ℝ × (ℕ → ℝ) => resEpoch p.1 p.2 k := by
  cases k with
  | zero => exact measurable_const
  | succ k =>
    exact measurable_fst.add (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp measurable_snd)

/-- The points `(x, t, u)` at which exactly `n` services are completed in `[0, t]` and the
residual service `R_t = Z_{n+1} − t` lies in `B`. -/
def gig1Set (n : ℕ) (B : Set ℝ) : Set (ℝ × (ℝ × (ℕ → ℝ))) :=
  {q | resEpoch q.1 q.2.2 n ≤ q.2.1 ∧ q.2.1 < resEpoch q.1 q.2.2 (n + 1) ∧
    resEpoch q.1 q.2.2 (n + 1) - q.2.1 ∈ B}

/-- The set `gig1Set n B` is measurable. -/
theorem measurableSet_gig1Set (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet (gig1Set n B) := by
  have hZ : ∀ k, Measurable fun q : ℝ × (ℝ × (ℕ → ℝ)) => resEpoch q.1 q.2.2 k := fun k =>
    (measurable_resEpoch k).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have ht : Measurable fun q : ℝ × (ℝ × (ℕ → ℝ)) => q.2.1 := measurable_fst.comp measurable_snd
  exact (measurableSet_le (hZ n) ht).inter ((measurableSet_lt ht (hZ (n + 1))).inter
    (((hZ (n + 1)).sub ht) hB))

/-- (3.41), MT p. 71: `Pⁿₜ(x, y) = P(Zₙ ≤ t < Z_{n+1}, R_t ≤ y | R₀ = x)`, with i.i.d.
service times of law `H`. -/
noncomputable def ladderP (H : Measure ℝ) (n : ℕ) (t x y : ℝ) : ℝ≥0∞ :=
  Measure.infinitePi (fun _ : ℕ => H)
    {u | resEpoch x u n ≤ t ∧ t < resEpoch x u (n + 1) ∧ resEpoch x u (n + 1) - t ≤ y}

/-- The measure `Λₙ(x, ·)`: `n` service completions during an interarrival time `T ∼ G`,
with the residual service at `T` distributed over `·`. -/
noncomputable def gig1LambdaMeasure (H G : Measure ℝ) (n : ℕ) (x : ℝ) : Measure ℝ :=
  ((G.prod (Measure.infinitePi fun _ : ℕ => H)).restrict
    {p | resEpoch x p.2 n ≤ p.1 ∧ p.1 < resEpoch x p.2 (n + 1)}).map
      fun p => resEpoch x p.2 (n + 1) - p.1

/-- `Λₙ(x, B)` is the `G ⊗ H^{⊗ℕ}` measure of the section of `gig1Set n B` at `x`. -/
theorem gig1LambdaMeasure_apply (H G : Measure ℝ) [IsProbabilityMeasure H] (n : ℕ) (x : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    gig1LambdaMeasure H G n x B =
      (G.prod (Measure.infinitePi fun _ : ℕ => H)) (Prod.mk x ⁻¹' gig1Set n B) := by
  have hZ : ∀ k, Measurable fun p : ℝ × (ℕ → ℝ) => resEpoch x p.2 k := fun k =>
    (measurable_resEpoch k).comp (measurable_const.prodMk measurable_snd)
  have hE : MeasurableSet {p : ℝ × (ℕ → ℝ) | resEpoch x p.2 n ≤ p.1 ∧
      p.1 < resEpoch x p.2 (n + 1)} :=
    (measurableSet_le (hZ n) measurable_fst).inter (measurableSet_lt measurable_fst (hZ (n + 1)))
  have hR : Measurable fun p : ℝ × (ℕ → ℝ) => resEpoch x p.2 (n + 1) - p.1 :=
    (hZ (n + 1)).sub measurable_fst
  rw [gig1LambdaMeasure, Measure.map_apply hR hB, Measure.restrict_apply (hR hB)]
  congr 1
  ext p
  simp only [gig1Set, mem_inter_iff, mem_preimage, mem_ofPred_eq]
  tauto

/-- The GI/G/1 kernel `Λₙ` on `ℝ` (MT (3.42), p. 71). -/
noncomputable def gig1Lambda (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G] (n : ℕ) :
    Kernel ℝ ℝ where
  toFun := gig1LambdaMeasure H G n
  measurable' := Measure.measurable_of_measurable_coe _ fun B hB => by
    simp_rw [gig1LambdaMeasure_apply H G n _ hB]
    exact measurable_measure_prodMk_left (measurableSet_gig1Set n hB)

/-- **(3.42)**, MT p. 71: `Λₙ(x, (−∞, y]) = ∫ Pⁿₜ(x, y) G(dt)`. -/
theorem eq_3_42 (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G] (n : ℕ) (x y : ℝ) :
    gig1Lambda H G n x (Iic y) = ∫⁻ t, ladderP H n t x y ∂G := by
  change gig1LambdaMeasure H G n x (Iic y) = _
  rw [gig1LambdaMeasure_apply H G n x measurableSet_Iic, Measure.prod_apply
    (measurable_prodMk_left (measurableSet_gig1Set n measurableSet_Iic))]
  rfl

/-- The GI/G/1 kernel `Λ*ₙ` (MT (3.43), p. 71): if more than `n` services are completed
before the next arrival the queue empties and the next service starts afresh with law `H`. -/
noncomputable def gig1LambdaStar (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G]
    (n : ℕ) : Kernel ℝ ℝ where
  toFun x := (∑' j, gig1Lambda H G (j + n + 1) x univ) • H
  measurable' := Measure.measurable_of_measurable_coe _ fun B hB => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact (Measurable.tsum fun j => Kernel.measurable_coe _ MeasurableSet.univ).mul_const _

/-- **(3.43)**, MT p. 71: `Λ*ₙ(x, (−∞, y]) = [Σ_{j ≥ n+1} Λⱼ(x, ℝ)] H(−∞, y]`. -/
theorem eq_3_43 (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G] (n : ℕ) (x y : ℝ) :
    gig1LambdaStar H G n x (Iic y) =
      (∑' j, gig1Lambda H G (j + n + 1) x univ) * H (Iic y) := rfl

/-- The GI/G/1 ladder chain `(Nₙ, Rₙ)` (MT p. 71): the ladder kernel (3.40) with the
kernels (3.42)–(3.43). -/
noncomputable def gig1Ladder (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G] :
    Kernel (ℕ × ℝ) (ℕ × ℝ) :=
  ladderKernel (gig1Lambda H G) (gig1LambdaStar H G)

/-- `Σ_{i<k} f(i) + Σᵢ f(i + k) = Σᵢ f(i)` in `ℝ≥0∞`. -/
theorem ennreal_sum_add_tsum_nat_add (f : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑ i ∈ Finset.range k, f i + ∑' i, f (i + k) = ∑' i, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_assoc, ← ih]
    congr 1
    rw [tsum_eq_zero_add' (f := fun i => f (i + k)) ENNReal.summable]
    simp only [zero_add]
    congr 1
    refine tsum_congr fun i => ?_
    congr 1
    omega

/-- Each row of the GI/G/1 ladder chain has mass `Σₖ Λₖ(x, ℝ)`, the probability that the
number of services completed during an interarrival time is finite. -/
theorem gig1Ladder_rowSum (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G] (i : ℕ)
    (x : ℝ) :
    gig1LambdaStar H G i x univ + ∑ k ∈ Finset.range (i + 1), gig1Lambda H G k x univ =
      ∑' k, gig1Lambda H G k x univ := by
  change (∑' j, gig1Lambda H G (j + i + 1) x univ) • H univ + _ = _
  have h := ennreal_sum_add_tsum_nat_add (fun k => gig1Lambda H G k x univ) (i + 1)
  simp only [← add_assoc] at h
  rw [measure_univ, smul_eq_mul, mul_one, add_comm, h]

/-- The GI/G/1 ladder chain is a Markov kernel when, from every residual service `x`,
only finitely many services fit into an interarrival time almost surely. -/
theorem isMarkovKernel_gig1Ladder (H G : Measure ℝ) [IsProbabilityMeasure H] [SFinite G]
    (h : ∀ x, ∑' k, gig1Lambda H G k x univ = 1) : IsMarkovKernel (gig1Ladder H G) :=
  isMarkovKernel_ladderKernel _ _ fun i x => by rw [gig1Ladder_rowSum, h]

/-- The truncation `w ↦ max(0, min(w, 1))`. -/
noncomputable def clamp01 (w : ℝ) : ℝ := max 0 (min w 1)

/-- The truncation is continuous. -/
theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The truncation lies below a nonnegative argument. -/
theorem clamp01_le {w : ℝ} (hw : 0 ≤ w) : clamp01 w ≤ w :=
  max_le hw (min_le_left _ _)

/-- The truncation is nonnegative. -/
theorem clamp01_nonneg (w : ℝ) : 0 ≤ clamp01 w := le_max_left _ _

/-- The truncation is bounded by `1`. -/
theorem norm_clamp01_le (w : ℝ) : ‖clamp01 w‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [clamp01_nonneg w], max_le zero_le_one (min_le_right _ _)⟩

/-- For i.i.d. service times with `H(−∞, 0) = 0` and `H(0, ∞) > 0`, almost surely all
service times are nonnegative and their partial sums tend to infinity (strong law of large numbers
for the truncations `min(Sᵢ, 1)`). -/
theorem tendsto_partialSum_atTop_ae (H : Measure ℝ) [IsProbabilityMeasure H]
    (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0)) :
    ∀ᵐ u ∂(Measure.infinitePi fun _ : ℕ => H),
      Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop atTop ∧ ∀ i, 0 ≤ u i := by
  set ν := Measure.infinitePi fun _ : ℕ => H
  set X : ℕ → (ℕ → ℝ) → ℝ := fun i u => clamp01 (u i) with hX
  have hc : Measurable clamp01 := continuous_clamp01.measurable
  have hXm : ∀ i, Measurable (X i) := fun i => hc.comp (measurable_pi_apply i)
  have hind : Pairwise fun i j => IndepFun (X i) (X j) ν := fun i j hij =>
    (iIndepFun_infinitePi (P := fun _ : ℕ => H) (X := fun _ => clamp01) (fun _ => hc)).indepFun
      hij
  have hlaw : ∀ i, ν.map (X i) = H.map clamp01 := fun i => by
    rw [show X i = clamp01 ∘ fun u : ℕ → ℝ => u i from rfl,
      ← Measure.map_map hc (measurable_pi_apply i), Measure.infinitePi_map_eval]
  have hident : ∀ i, IdentDistrib (X i) (X 0) ν ν := fun i =>
    ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩
  have hint : Integrable (X 0) ν :=
    Integrable.of_bound (hXm 0).aestronglyMeasurable 1 (ae_of_all _ fun u => norm_clamp01_le _)
  have hslln := strong_law_ae X hint hind hident
  have hm : 0 < ∫ u, X 0 u ∂ν := by
    have hmap : ν.map (fun u => u 0) = H := Measure.infinitePi_map_eval _ 0
    have h1 : ∫ u, X 0 u ∂ν = ∫ w, clamp01 w ∂H := by
      rw [show ∫ w, clamp01 w ∂H = ∫ w, clamp01 w ∂(ν.map fun u => u 0) by rw [hmap],
        integral_map (measurable_pi_apply 0).aemeasurable hc.aestronglyMeasurable]
    have hnn0 : 0 ≤ clamp01 := fun w => clamp01_nonneg w
    rw [h1, integral_pos_iff_support_of_nonneg hnn0
      (Integrable.of_bound hc.aestronglyMeasurable 1 (ae_of_all _ norm_clamp01_le))]
    refine hHpos.trans_le (measure_mono fun w hw => ?_)
    simp only [Function.mem_support, clamp01, ne_eq]
    have hw' : (0 : ℝ) < w := hw
    exact (lt_max_of_lt_right (lt_min hw' one_pos)).ne'
  have hnn : ∀ᵐ u ∂ν, ∀ i, 0 ≤ u i := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have : {u : ℕ → ℝ | ¬ 0 ≤ u i} = (fun u : ℕ → ℝ => u i) ⁻¹' Iio 0 := by
      ext u
      simp
    rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio,
      Measure.infinitePi_map_eval, hH0]
  filter_upwards [hslln, hnn] with u h1 h2
  refine ⟨?_, h2⟩
  have h3 : Tendsto (fun n : ℕ => (n : ℝ) * ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i u)) atTop
      atTop := tendsto_natCast_atTop_atTop.atTop_mul_pos hm h1
  have h4 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, X i u) atTop atTop := by
    refine h3.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ this, one_mul]
  refine tendsto_atTop_mono (fun n => Finset.sum_le_sum fun i _ => clamp01_le (h2 i)) h4

/-- With nonnegative service times the renewal epochs `Z₁ ≤ Z₂ ≤ ⋯` increase. -/
theorem resEpoch_mono {x : ℝ} {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a ≤ b) : resEpoch x u a ≤ resEpoch x u b := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [resEpoch]
  have h : ∑ i ∈ Finset.range a, u i ≤ ∑ i ∈ Finset.range b, u i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun i _ _ => hu i
  linarith

/-- If the epochs increase to infinity, then for `t ≥ 0` exactly one `k` has
`Zₖ ≤ t < Z_{k+1}`. -/
theorem tsum_indicator_resEpoch_eq_one {x t : ℝ} {u : ℕ → ℝ} (ht : 0 ≤ t)
    (hu : ∀ i, 0 ≤ u i) (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop atTop) :
    ∑' k, {v : ℕ → ℝ | resEpoch x v k ≤ t ∧ t < resEpoch x v (k + 1)}.indicator 1 u =
      (1 : ℝ≥0∞) := by
  classical
  have hex : ∃ k, t < resEpoch x u k := by
    obtain ⟨n, hn⟩ := (hdiv.eventually_gt_atTop (t - x)).exists
    exact ⟨n + 1, by simp only [resEpoch]; linarith⟩
  set k₀ := Nat.find hex with hk₀
  have hk₀pos : k₀ ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [← hk₀, h] at this
    simp only [resEpoch] at this
    linarith
  have hmin : ∀ m < k₀, resEpoch x u m ≤ t := fun m hm => not_lt.1 (Nat.find_min hex hm)
  have hk₀spec : t < resEpoch x u k₀ := Nat.find_spec hex
  rw [tsum_eq_single (k₀ - 1) fun m hm => ?_]
  · rw [indicator_of_mem]
    · rfl
    · exact ⟨hmin _ (by omega), by rw [show k₀ - 1 + 1 = k₀ by omega]; exact hk₀spec⟩
  · rw [indicator_of_notMem]
    rintro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · exact absurd (hmin (m + 1) (by omega)) (not_le.2 h2)
    · have := resEpoch_mono (x := x) hu (show 1 ≤ k₀ by omega) (show k₀ ≤ m by omega)
      linarith

/-- The rows of the GI/G/1 ladder chain have mass one, `Σₖ Λₖ(x, ℝ) = 1`, when service and
interarrival times are nonnegative and services are not almost surely `0`. -/
theorem gig1Lambda_tsum_univ (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0))
    (hG0 : G (Iio 0) = 0) (x : ℝ) : ∑' k, gig1Lambda H G k x univ = 1 := by
  set ν := Measure.infinitePi fun _ : ℕ => H
  set S : ℕ → Set (ℝ × (ℕ → ℝ)) := fun k => Prod.mk x ⁻¹' gig1Set k univ with hS
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    measurable_prodMk_left (measurableSet_gig1Set k MeasurableSet.univ)
  have hk : ∀ k, gig1Lambda H G k x univ = ∫⁻ t, ν (Prod.mk t ⁻¹' S k) ∂G := fun k => by
    change gig1LambdaMeasure H G k x univ = _
    rw [gig1LambdaMeasure_apply H G k x MeasurableSet.univ, Measure.prod_apply (hSm k)]
  simp_rw [hk]
  rw [← lintegral_tsum fun k => (measurable_measure_prodMk_left (hSm k)).aemeasurable]
  have hae : ∀ᵐ t ∂G, ∑' k, ν (Prod.mk t ⁻¹' S k) = 1 := by
    have hG : ∀ᵐ t ∂G, 0 ≤ t := by
      rw [ae_iff]
      have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by
        ext a
        simp
      rw [this, hG0]
    filter_upwards [hG] with t ht
    have hsec : ∀ k, Prod.mk t ⁻¹' S k =
        {v : ℕ → ℝ | resEpoch x v k ≤ t ∧ t < resEpoch x v (k + 1)} := fun k => by
      ext v
      simp [hS, gig1Set]
    have hmeas : ∀ k, MeasurableSet
        {v : ℕ → ℝ | resEpoch x v k ≤ t ∧ t < resEpoch x v (k + 1)} := fun k => by
      rw [← hsec]
      exact measurable_prodMk_left (hSm k)
    simp_rw [hsec, ← lintegral_indicator_one (hmeas _)]
    rw [← lintegral_tsum fun k => (measurable_one.indicator (hmeas k)).aemeasurable]
    rw [lintegral_congr_ae ((tendsto_partialSum_atTop_ae H hH0 hHpos).mono fun u hu =>
      tsum_indicator_resEpoch_eq_one ht hu.2 hu.1)]
    simp
  rw [lintegral_congr_ae hae]
  simp

/-- The GI/G/1 ladder chain `gig1Ladder H G` is a Markov kernel when service and interarrival
times are nonnegative and services are not almost surely `0`. -/
theorem isMarkovKernel_gig1Ladder_of_pos (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0))
    (hG0 : G (Iio 0) = 0) : IsMarkovKernel (gig1Ladder H G) :=
  isMarkovKernel_gig1Ladder H G (gig1Lambda_tsum_univ H G hH0 hHpos hG0)

end MeynTweedie.TransitionProbabilities

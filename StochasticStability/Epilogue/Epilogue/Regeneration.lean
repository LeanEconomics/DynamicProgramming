/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.ModelKernels
import Mathlib.Probability.ConditionalProbability

/-!
# Regeneration at random indices

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/Regeneration.lean`), with the namespace changed to
`MeynTweedie.Epilogue` and the imports to `InvariantMeasures.*`.

The tool behind the Markov property of the renewal skeletons and of the GI/G/1 ladder chain
(MT §§3.5.3–3.5.4): an i.i.d. sequence starts afresh after a random index that is determined by
its past, and a process that is a function of the past and of such a fresh future is a Markov
chain.

* `truncSeq`, `tailSeq`, `indepFun_truncSeq_tailSeq`, `infinitePi_map_tailSeq`,
  `infinitePi_map_trunc_tail`: under `Γ^{⊗ℕ}` the first `k` terms and the tail from `k` on are
  independent, and the tail is again `Γ^{⊗ℕ}`.
* `lintegral_regeneration`: splitting over the values of the random index, the future at the
  index has, given the past, the law `ν` conditioned on the event that defines the index.
* `isMarkovChain_of_regeneration`: such a process is a Markov chain (via
  `isMarkovChain_of_step` on its natural filtration `pastFilt`).
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The first `k` terms of a sequence, padded with zeros. -/
def truncSeq (k : ℕ) (w : ℕ → ℝ) : ℕ → ℝ := fun i => if i < k then w i else 0

/-- The sequence from index `k` on, `(w_k, w_{k+1}, …)`. -/
def tailSeq (k : ℕ) (w : ℕ → ℝ) : ℕ → ℝ := fun i => w (k + i)

/-- Truncation is measurable. -/
theorem measurable_truncSeq (k : ℕ) : Measurable (truncSeq k) :=
  measurable_pi_iff.2 fun i => by
    unfold truncSeq
    split_ifs
    · exact measurable_pi_apply i
    · exact measurable_const

/-- The tail map is measurable. -/
theorem measurable_tailSeq (k : ℕ) : Measurable (tailSeq k) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (k + i)

/-- The coordinates of an i.i.d. sequence `Γ^{⊗ℕ}` are independent. -/
theorem iIndep_coords (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    iIndep (fun i => MeasurableSpace.comap (fun w : ℕ → ℝ => w i) inferInstance)
      (Measure.infinitePi fun _ : ℕ => Γ) :=
  (iIndepFun_iff_iIndep _ _ _).1
    (iIndepFun_infinitePi (P := fun _ : ℕ => Γ) (X := fun _ => id) (fun _ => measurable_id))

/-- Under `Γ^{⊗ℕ}` the first `k` terms and the tail from `k` on are independent. -/
theorem indepFun_truncSeq_tailSeq (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (k : ℕ) :
    IndepFun (truncSeq k) (tailSeq k) (Measure.infinitePi fun _ : ℕ => Γ) := by
  set m : ℕ → MeasurableSpace (ℕ → ℝ) :=
    fun i => MeasurableSpace.comap (fun w : ℕ → ℝ => w i) inferInstance
  have hle : ∀ i, m i ≤ MeasurableSpace.pi := fun i => (measurable_pi_apply i).comap_le
  have hind := indep_iSup_of_disjoint hle (iIndep_coords Γ)
    (S := Iio k) (T := Ici k) (by
      rw [Set.disjoint_left]
      intro i hi hi'
      exact absurd (mem_Ici.1 hi') (not_le.2 (mem_Iio.1 hi)))
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
  · simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, iSup_le_iff]
    intro i
    by_cases hi : i < k
    · simp only [truncSeq, hi, ite_true]
      exact le_iSup₂ (f := fun j (_ : j ∈ Iio k) => m j) i hi
    · simp only [truncSeq, hi, ite_false]
      exact (measurable_const (a := (0 : ℝ))).comap_le.trans bot_le
  · simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, iSup_le_iff]
    intro i
    exact le_iSup₂ (f := fun j (_ : j ∈ Ici k) => m j) (k + i) (by simp)

/-- The tail of an i.i.d. sequence is again i.i.d. with the same law. -/
theorem infinitePi_map_tailSeq (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Γ).map (tailSeq k) = Measure.infinitePi fun _ : ℕ => Γ := by
  have h := (iIndep_coords Γ).precomp (g := fun i => k + i) (fun a b hab => by simpa using hab)
  have h' : iIndepFun (fun i (w : ℕ → ℝ) => w (k + i)) (Measure.infinitePi fun _ : ℕ => Γ) :=
    (iIndepFun_iff_iIndep _ _ _).2 h
  have := h'.map_fun_eq_infinitePi_map (fun i => measurable_pi_apply (k + i))
  rw [show tailSeq k = fun w i => w (k + i) from rfl, this]
  congr 1
  funext i
  exact Measure.infinitePi_map_eval _ _

/-- Under `Γ^{⊗ℕ}`, the pair (first `k` terms, tail from `k`) has law
`(law of the first k terms) ⊗ Γ^{⊗ℕ}`. -/
theorem infinitePi_map_trunc_tail (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun w => (truncSeq k w, tailSeq k w)) =
      ((Measure.infinitePi fun _ : ℕ => Γ).map (truncSeq k)).prod
        (Measure.infinitePi fun _ : ℕ => Γ) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_truncSeq k).aemeasurable
    (measurable_tailSeq k).aemeasurable).1 (indepFun_truncSeq_tailSeq Γ k),
    infinitePi_map_tailSeq]

variable {Ω β γ Y : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace Y]

/-- An integral against the conditional measure `ν[|D]` on a section `D = Sₓ` of a set. -/
theorem lintegral_cond_eq (ν : Measure γ) {S : Set (Y × γ)} (hS : MeasurableSet S)
    (g : Y × γ → ℝ≥0∞) (x : Y) :
    ∫⁻ y, g (x, y) ∂(ν[|{y | (x, y) ∈ S}]) =
      (ν {y | (x, y) ∈ S})⁻¹ * ∫⁻ y, S.indicator g (x, y) ∂ν := by
  have hSx : MeasurableSet {y | (x, y) ∈ S} := measurable_prodMk_left hS
  rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul, ← lintegral_indicator hSx]
  congr 1

/-- `x ↦ ∫ g(x, y) ν[|Sₓ](dy)` is measurable. -/
theorem measurable_lintegral_cond (ν : Measure γ) [SFinite ν] {S : Set (Y × γ)}
    (hS : MeasurableSet S) {g : Y × γ → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x => ∫⁻ y, g (x, y) ∂(ν[|{y | (x, y) ∈ S}]) := by
  simp_rw [lintegral_cond_eq ν hS g]
  exact (measurable_measure_prodMk_left hS).inv.mul (hg.indicator hS).lintegral_prod_right'

/-- `ν(Sₓ) ∫ g(x, ·) dν[|Sₓ] = ∫_{Sₓ} g(x, ·) dν`, also when `ν(Sₓ) = 0`. -/
theorem mul_lintegral_cond (ν : Measure γ) [IsFiniteMeasure ν] {S : Set (Y × γ)}
    (hS : MeasurableSet S) (g : Y × γ → ℝ≥0∞) (x : Y) :
    ν {y | (x, y) ∈ S} * ∫⁻ y, g (x, y) ∂(ν[|{y | (x, y) ∈ S}]) =
      ∫⁻ y, S.indicator g (x, y) ∂ν := by
  rw [lintegral_cond_eq ν hS g, ← mul_assoc]
  by_cases h0 : ν {y | (x, y) ∈ S} = 0
  · have hSx : MeasurableSet {y | (x, y) ∈ S} := measurable_prodMk_left hS
    have : ∫⁻ y, S.indicator g (x, y) ∂ν = 0 := by
      have he : (fun y => S.indicator g (x, y)) = {y | (x, y) ∈ S}.indicator (fun y => g (x, y)) :=
        by
        ext y
        by_cases hy : (x, y) ∈ S <;> simp [hy]
      rw [he, lintegral_indicator hSx]
      exact setLIntegral_measure_zero _ _ h0
    rw [this, mul_zero]
  · rw [ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]

/-- **Regeneration at a random index.** Let `τ` be a random index such that, for each `k`, the
event `{τ = k}` is (almost surely) determined by a "past" `Bₖ` together with the event that the
"future" `Fₖ` lies in the section `S_{V}` of a set `S`, where `V` is a function of the past on
`{τ = k}`; and let the future be independent of the past with law `ν`. Then the future at `τ`,
given the past, has the conditional law `ν[|S_V]`:
`∫ g(V, F_τ) dP = ∫ ∫ g(V, y) ν[|S_V](dy) dP`. -/
theorem lintegral_regeneration (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure γ)
    [IsProbabilityMeasure ν] (τ : Ω → ℕ) (hτ : ∀ k, MeasurableSet {ω | τ ω = k})
    (B : ℕ → Ω → β) (hB : ∀ k, Measurable (B k)) (Fu : ℕ → Ω → γ)
    (hFu : ∀ k, Measurable (Fu k))
    (hlaw : ∀ k, P.map (fun ω => (B k ω, Fu k ω)) = (P.map (B k)).prod ν)
    (V : Ω → Y) {S : Set (Y × γ)} (hS : MeasurableSet S)
    (hpast : ∀ k, ∃ T : Set β, MeasurableSet T ∧ ∃ h : β → Y, Measurable h ∧
      ∀ᵐ ω ∂P, (τ ω = k ↔ (B k ω ∈ T ∧ (h (B k ω), Fu k ω) ∈ S)) ∧
        (τ ω = k → V ω = h (B k ω)))
    {g : Y × γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (V ω, Fu (τ ω) ω) ∂P =
      ∫⁻ ω, ∫⁻ y, g (V ω, y) ∂(ν[|{y | (V ω, y) ∈ S}]) ∂P := by
  have hU : (univ : Set Ω) = ⋃ k, {ω | τ ω = k} := by
    ext ω
    simp
  have hdisj : Pairwise fun a b => Disjoint {ω : Ω | τ ω = a} {ω : Ω | τ ω = b} :=
    fun a b hab => Set.disjoint_left.2 fun ω ha hb => hab (ha.symm.trans hb)
  have split : ∀ F : Ω → ℝ≥0∞, ∫⁻ ω, F ω ∂P = ∑' k, ∫⁻ ω in {ω | τ ω = k}, F ω ∂P := fun F => by
    rw [← setLIntegral_univ, hU, lintegral_iUnion hτ hdisj]
  rw [split, split]
  refine tsum_congr fun k => ?_
  obtain ⟨T, hT, h, hh, hae⟩ := hpast k
  set c : Y → ℝ≥0∞ := fun x => ∫⁻ y, g (x, y) ∂(ν[|{y | (x, y) ∈ S}]) with hc
  have hcm : Measurable c := measurable_lintegral_cond ν hS hg
  have hSB : MeasurableSet {q : β × γ | (h q.1, q.2) ∈ S} :=
    ((hh.comp measurable_fst).prodMk measurable_snd) hS
  have hE : MeasurableSet (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}) :=
    (measurable_fst hT).inter hSB
  have hBF : Measurable fun ω => (B k ω, Fu k ω) := (hB k).prodMk (hFu k)
  have hL : ∫⁻ ω in {ω | τ ω = k}, g (V ω, Fu (τ ω) ω) ∂P =
      ∫⁻ ω, (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
        (fun q => g (h q.1, q.2)) (B k ω, Fu k ω) ∂P := by
    rw [← lintegral_indicator (hτ k)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω ⟨h1, h2⟩
    by_cases hk : τ ω = k
    · have hm : (B k ω, Fu k ω) ∈ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S} := h1.1 hk
      rw [indicator_of_mem (show ω ∈ {ω | τ ω = k} from hk), indicator_of_mem hm, h2 hk, hk]
    · have hm : (B k ω, Fu k ω) ∉ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S} :=
        fun hm => hk (h1.2 hm)
      rw [indicator_of_notMem (show ω ∉ {ω | τ ω = k} from hk), indicator_of_notMem hm]
  have hR : ∫⁻ ω in {ω | τ ω = k}, c (V ω) ∂P =
      ∫⁻ ω, (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
        (fun q => c (h q.1)) (B k ω, Fu k ω) ∂P := by
    rw [← lintegral_indicator (hτ k)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω ⟨h1, h2⟩
    by_cases hk : τ ω = k
    · have hm : (B k ω, Fu k ω) ∈ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S} := h1.1 hk
      rw [indicator_of_mem (show ω ∈ {ω | τ ω = k} from hk), indicator_of_mem hm, h2 hk]
    · have hm : (B k ω, Fu k ω) ∉ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S} :=
        fun hm => hk (h1.2 hm)
      rw [indicator_of_notMem (show ω ∉ {ω | τ ω = k} from hk), indicator_of_notMem hm]
  change _ = ∫⁻ ω in {ω | τ ω = k}, c (V ω) ∂P
  rw [hL, hR]
  have hf1 : Measurable ((Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
      (fun q : β × γ => g (h q.1, q.2))) :=
    (hg.comp ((hh.comp measurable_fst).prodMk measurable_snd)).indicator hE
  have hf2 : Measurable ((Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
      (fun q : β × γ => c (h q.1))) :=
    (hcm.comp (hh.comp measurable_fst)).indicator hE
  rw [← lintegral_map hf1 hBF, ← lintegral_map hf2 hBF, hlaw k,
    lintegral_prod _ hf1.aemeasurable, lintegral_prod _ hf2.aemeasurable]
  refine lintegral_congr fun b => ?_
  by_cases hb : b ∈ T
  · have e1 : ∀ y, (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
        (fun q : β × γ => g (h q.1, q.2)) (b, y) = S.indicator g (h b, y) := fun y => by
      by_cases hy : (h b, y) ∈ S
      · rw [indicator_of_mem (show (b, y) ∈ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}
          from ⟨hb, hy⟩), indicator_of_mem hy]
      · rw [indicator_of_notMem (fun hm => hy hm.2), indicator_of_notMem hy]
    have e2 : ∀ y, (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator
        (fun q : β × γ => c (h q.1)) (b, y) =
          {y | (h b, y) ∈ S}.indicator (fun _ => c (h b)) y := fun y => by
      by_cases hy : (h b, y) ∈ S
      · rw [indicator_of_mem (show (b, y) ∈ Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}
          from ⟨hb, hy⟩), indicator_of_mem (show y ∈ {y | (h b, y) ∈ S} from hy)]
      · rw [indicator_of_notMem (fun hm => hy hm.2),
          indicator_of_notMem (show y ∉ {y | (h b, y) ∈ S} from hy)]
    simp_rw [e1, e2]
    rw [lintegral_indicator_const (s := {y | (h b, y) ∈ S}) (measurable_prodMk_left hS), mul_comm,
      hc,
      mul_lintegral_cond ν hS g (h b)]
  · have e : ∀ F : β × γ → ℝ≥0∞, ∀ y,
        (Prod.fst ⁻¹' T ∩ {q : β × γ | (h q.1, q.2) ∈ S}).indicator F (b, y) = 0 :=
      fun F y => indicator_of_notMem (fun hm => hb hm.1) _
    simp_rw [e]

/-- An integral over `v⁻¹(C)` as an integral against the indicator of `C ∘ v`. -/
theorem setLIntegral_preimage_eq {Z : Type*} [MeasurableSpace Z] (P : Measure Ω) {v : Ω → Z}
    (hv : Measurable v) {C : Set Z} (hC : MeasurableSet C) (F : Ω → ℝ≥0∞) :
    ∫⁻ ω in v ⁻¹' C, F ω ∂P = ∫⁻ ω, C.indicator 1 (v ω) * F ω ∂P := by
  rw [← lintegral_indicator (hv hC)]
  refine lintegral_congr fun ω => ?_
  by_cases h : v ω ∈ C
  · rw [indicator_of_mem (show ω ∈ v ⁻¹' C from h), indicator_of_mem h, Pi.one_apply, one_mul]
  · rw [indicator_of_notMem (show ω ∉ v ⁻¹' C from h), indicator_of_notMem h, zero_mul]

variable {X : Type*} [MeasurableSpace X] in
/-- The natural filtration `σ(Ψ₀, …, Ψₙ)` of a process. -/
def pastFilt (Ψ : ℕ → Ω → X) (hΨ : ∀ n, Measurable (Ψ n)) :
    MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq n := MeasurableSpace.comap (fun ω (j : Fin (n + 1)) => Ψ j ω) inferInstance
  mono' m n hmn := by
    have hproj : Measurable fun v : Fin (n + 1) → X => fun j : Fin (m + 1) =>
        v (Fin.castLE (by omega) j) := measurable_pi_iff.2 fun j => measurable_pi_apply _
    have h : (fun ω (j : Fin (m + 1)) => Ψ j ω) =
        (fun v : Fin (n + 1) → X => fun j : Fin (m + 1) => v (Fin.castLE (by omega) j)) ∘
          (fun ω (j : Fin (n + 1)) => Ψ j ω) := rfl
    change MeasurableSpace.comap (fun ω (j : Fin (m + 1)) => Ψ j ω) _ ≤
      MeasurableSpace.comap (fun ω (j : Fin (n + 1)) => Ψ j ω) _
    rw [h, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hproj.comap_le
  le' n := (measurable_pi_iff.2 fun j : Fin (n + 1) => hΨ j).comap_le

variable {X : Type*} [MeasurableSpace X] in
/-- **A process that regenerates is a Markov chain.** Suppose that at each time `n` there is
a random index `τₙ` at which the process regenerates: given the past `σ(Ψ₀, …, Ψₙ)`, the future
noise `F_{n,τₙ}` has law `ν` conditioned on the section `S_{Ψₙ}`, and `Ψₙ₊₁ = Φ(Ψₙ, F_{n,τₙ})`
(all hypotheses almost surely). Then `Ψ` is a Markov chain with kernel
`Q(x, ·) = ν[|Sₓ] ∘ Φ(x, ·)⁻¹`. -/
theorem isMarkovChain_of_regeneration (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure γ)
    [IsProbabilityMeasure ν] (μ : Measure X) (Ψ : ℕ → Ω → X) (hΨ : ∀ n, Measurable (Ψ n))
    (h0 : P.map (Ψ 0) = μ) (τ : ℕ → Ω → ℕ) (hτ : ∀ n k, MeasurableSet {ω | τ n ω = k})
    (B : ℕ → ℕ → Ω → β) (hB : ∀ n k, Measurable (B n k)) (Fu : ℕ → ℕ → Ω → γ)
    (hFu : ∀ n k, Measurable (Fu n k))
    (hlaw : ∀ n k, P.map (fun ω => (B n k ω, Fu n k ω)) = (P.map (B n k)).prod ν)
    {S : Set (X × γ)} (hS : MeasurableSet S)
    (hpast : ∀ n k, ∃ T : Set β, MeasurableSet T ∧ ∃ h : β → (Fin (n + 1) → X), Measurable h ∧
      ∀ᵐ ω ∂P, (τ n ω = k ↔ (B n k ω ∈ T ∧ (h (B n k ω) (Fin.last n), Fu n k ω) ∈ S)) ∧
        (τ n ω = k → ∀ j : Fin (n + 1), Ψ j ω = h (B n k ω) j))
    {Φ : X × γ → X} (hΦ : Measurable Φ)
    (hstep : ∀ n, ∀ᵐ ω ∂P, Ψ (n + 1) ω = Φ (Ψ n ω, Fu n (τ n ω) ω))
    (Q : Kernel X X) (hQ : ∀ x, Q x = (ν[|{y | (x, y) ∈ S}]).map fun y => Φ (x, y)) :
    IsMarkovChain Q μ P Ψ := by
  refine isMarkovChain_of_step Q μ (𝓖 := pastFilt Ψ hΨ) (fun n => ?_) h0
    (fun n G hG f hf => ?_)
  · exact (measurable_pi_apply (Fin.last n)).comp
      (comap_measurable (fun ω (j : Fin (n + 1)) => Ψ j ω))
  obtain ⟨C, hC, rfl⟩ := hG
  set pv : Ω → (Fin (n + 1) → X) := fun ω j => Ψ j ω with hpvdef
  have hpv : Measurable pv := measurable_pi_iff.2 fun j => hΨ j
  set S' : Set ((Fin (n + 1) → X) × γ) := {q | (q.1 (Fin.last n), q.2) ∈ S} with hS'def
  have hS' : MeasurableSet S' :=
    (((measurable_pi_apply (Fin.last n)).comp measurable_fst).prodMk measurable_snd) hS
  set g : (Fin (n + 1) → X) × γ → ℝ≥0∞ :=
    fun q => C.indicator 1 q.1 * f (Φ (q.1 (Fin.last n), q.2)) with hgdef
  have hg : Measurable g :=
    ((measurable_one.indicator hC).comp measurable_fst).mul
      (hf.comp (hΦ.comp (((measurable_pi_apply (Fin.last n)).comp measurable_fst).prodMk
        measurable_snd)))
  have hreg := lintegral_regeneration P ν (τ n) (hτ n) (B n) (hB n) (Fu n) (hFu n) (hlaw n) pv
    hS' (g := g) (fun k => by
      obtain ⟨T, hT, h, hh, hae⟩ := hpast n k
      refine ⟨T, hT, h, hh, ?_⟩
      filter_upwards [hae] with ω ⟨h1, h2⟩
      exact ⟨h1, fun hk => funext fun j => h2 hk j⟩) hg
  change ∫⁻ ω in pv ⁻¹' C, f (Ψ (n + 1) ω) ∂P = ∫⁻ ω in pv ⁻¹' C, ∫⁻ y, f y ∂Q (Ψ n ω) ∂P
  rw [setLIntegral_preimage_eq P hpv hC, setLIntegral_preimage_eq P hpv hC]
  have hL : ∫⁻ ω, C.indicator 1 (pv ω) * f (Ψ (n + 1) ω) ∂P =
      ∫⁻ ω, g (pv ω, Fu n (τ n ω) ω) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hstep n] with ω hω
    rw [hω]
    rfl
  rw [hL, hreg]
  refine lintegral_congr fun ω => ?_
  have hΦx : Measurable fun y => Φ (Ψ n ω, y) := hΦ.comp measurable_prodMk_left
  rw [hQ, lintegral_map hf hΦx]
  change ∫⁻ y, C.indicator 1 (pv ω) * f (Φ (Ψ n ω, y)) ∂(ν[|{y | (Ψ n ω, y) ∈ S}]) = _
  exact lintegral_const_mul _ (hf.comp hΦx)

end MeynTweedie.Epilogue

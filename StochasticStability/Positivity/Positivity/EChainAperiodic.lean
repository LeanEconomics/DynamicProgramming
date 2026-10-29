/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.EChainPositivity

/-!
# e-chains: aperiodicity and convergence (MT §18.4.2, Theorem 18.4.4 (ii))

Meyn and Tweedie, pp. 475–477. `X` is a locally compact, second-countable, metrizable Hausdorff
space with its Borel σ-algebra; `Π = eChainLimit he`.

**Definition.** `IsTopAperiodic P x` (p. 475): `Pᵏ(x, O) > 0` for every open `O ∋ x` and all large
`k`.

**Tools.**
* `exists_subseq_tendsto_of_equicontinuousAt`: the Ascoli step, a pointwise convergent
  subsequence with continuous limit; `IsEChain.equicontinuousAt`.
* `integral_comp_kernel_of_bdd`, `abs_integral_lt_integral_abs` (the strict triangle inequality
  for a function taking both signs), `setLIntegral_pos_of_pos`,
  `exists_pow_pos_of_eChainLimit_pos`.
* `sign_of_integral_abs_eq`: the sign step of the proof of Proposition 18.4.3.

**Results.**
* **Proposition 18.4.3** (`proposition_18_4_3`, p. 475): for an e-chain bounded in probability on
  average with a reachable aperiodic `x*` and `π = Π(x*, ·)`, `Pᵏ(y, ·) → π` weakly for every
  `y ∈ supp π` (18.26); the core is `tendsto_pow_cc_of_mem_support`.
* **Theorem 18.4.4 (ii)** (`theorem_18_4_4_ii`, p. 477): then `Pᵏ(x, ·) → π` weakly for every `x`
  (18.29); `theorem_18_4_4_ii_converse`: if (18.29) holds for every `x`, every state of `supp π` is
  reachable, aperiodic and topologically recurrent.

**Method.** The book proves (18.26) for `f ∈ C_c(X)` with `∫ f dπ = 0`; here the argument is run
for `Pᵏf − π(f)`, which is equicontinuous and bounded but not compactly supported, so that every
`f ∈ C_c(X)` is covered; weak convergence then follows since the limit is a probability. The set
`O_ε` of Theorem 18.4.4 is taken as a union of equicontinuity neighbourhoods of the points of
`supp π`, and `lim_N P̄_N(x, O_ε) = 1` comes from (D.6) for the limit kernel (`Π(x, ·) = π`).
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BoundedContinuousFunction CompactlySupported

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]

/-! ### Subsequences of an equicontinuous bounded sequence -/

omit [MeasurableSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **The Ascoli step** of the proof of Proposition 18.4.3 (MT p. 476): a uniformly bounded
sequence of real functions, equicontinuous at every point of a separable space, has along every
sequence of indices a pointwise convergent subsequence; the limit is continuous. -/
theorem exists_subseq_tendsto_of_equicontinuousAt {F : ℕ → X → ℝ} {B : ℝ}
    (hB : ∀ k x, |F k x| ≤ B) (hF : ∀ x, EquicontinuousAt F x) (ψ : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → ℝ, Continuous g ∧
      ∀ x, Tendsto (fun i => F (ψ (φ i)) x) atTop (𝓝 (g x)) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨id, strictMono_id, fun x => isEmptyElim x, continuous_of_discreteTopology,
      fun x => isEmptyElim x⟩
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq X
  set s : ℕ → (ℕ → ℝ) := fun n d => F (ψ n) (D d)
  have hK : IsCompact (univ.pi fun _ : ℕ => Icc (-B) B) := isCompact_univ_pi fun _ => isCompact_Icc
  have hs : ∀ n, s n ∈ univ.pi fun _ : ℕ => Icc (-B) B := fun n d _ => abs_le.1 (hB _ _)
  obtain ⟨c, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hs
  have hcoord : ∀ d, Tendsto (fun i => s (φ i) d) atTop (𝓝 (c d)) := fun d =>
    ((continuous_apply d).tendsto c).comp hlim
  have hcauchy : ∀ x, CauchySeq fun i => F (ψ (φ i)) x := fun x => by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    have hU := (hF x) _ (Metric.dist_mem_uniformity (show (0 : ℝ) < ε / 3 by positivity))
    obtain ⟨_, ⟨d, rfl⟩, hd⟩ := hD.inter_nhds_nonempty hU
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hcoord d).cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    have h2 : dist (F (ψ (φ m)) x) (F (ψ (φ m)) (D d)) < ε / 3 := hd (ψ (φ m))
    have h3 : dist (F (ψ (φ n)) x) (F (ψ (φ n)) (D d)) < ε / 3 := hd (ψ (φ n))
    calc dist (F (ψ (φ m)) x) (F (ψ (φ n)) x)
        ≤ dist (F (ψ (φ m)) x) (F (ψ (φ m)) (D d)) +
          dist (F (ψ (φ m)) (D d)) (F (ψ (φ n)) (D d)) +
          dist (F (ψ (φ n)) (D d)) (F (ψ (φ n)) x) := dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
          rw [dist_comm (F (ψ (φ n)) (D d))]
          exact add_lt_add (add_lt_add h2 h1) h3
      _ = ε := by ring
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨φ, hφ, g, ?_, hg⟩
  have h1 : Tendsto (fun i => F (ψ (φ i))) atTop (𝓝 g) := tendsto_pi_nhds.2 hg
  refine continuous_iff_continuousAt.2 fun x => h1.continuousAt_of_equicontinuousAt ?_
  exact (hF x).comp (ψ ∘ φ)

omit [T2Space X] [SecondCountableTopology X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- For an e-chain, `{Pᵏ f}` is equicontinuous at every point for `f ∈ C_c(X)`. -/
theorem IsEChain.equicontinuousAt {P : Kernel X X} (he : IsEChain P) (f : C_c(X, ℝ)) (x : X) :
    EquicontinuousAt (fun k : ℕ => fun y => ∫ z, f z ∂(P ^ k) y) x := by
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have h := he f (map_continuous f) f.hasCompactSupport K hK x (mem_of_mem_nhds hxK)
  intro U hU
  have := h U hU
  rwa [nhdsWithin_eq_nhds.2 hxK] at this

/-! ### Integration tools -/

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- `(μP)(f) = μ(Pf)` for bounded measurable `f`. -/
theorem integral_comp_kernel_of_bdd (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) :
    ∫ y, f y ∂(P ∘ₘ μ) = ∫ x, (∫ y, f y ∂P x) ∂μ := by
  rw [← Measure.snd_compProd μ P, Measure.snd,
    integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,
    Measure.integral_compProd (f := fun z : X × X => f z.2)
      (Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable B
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z.2))]

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- **Strict triangle inequality**: if `h` takes both signs on sets of positive measure,
`|∫ h dμ| < ∫ |h| dμ`. -/
theorem abs_integral_lt_integral_abs {μ : Measure X} {h : X → ℝ} (hi : Integrable h μ)
    (hp : 0 < μ {y | 0 < h y}) (hn : 0 < μ {y | h y < 0}) :
    |∫ y, h y ∂μ| < ∫ y, |h y| ∂μ := by
  have hip : Integrable (fun y => max (h y) 0) μ := hi.pos_part
  have hin : Integrable (fun y => max (-h y) 0) μ := hi.neg.pos_part
  have hpos : 0 < ∫ y, max (h y) 0 ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (f := fun y => max (h y) 0)
      (fun y => le_max_right _ _) hip]
    refine hp.trans_le (measure_mono fun y hy => ?_)
    simp only [mem_ofPred_eq] at hy
    simp only [Function.mem_support]
    exact (lt_max_of_lt_left hy).ne'
  have hneg : 0 < ∫ y, max (-h y) 0 ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (f := fun y => max (-h y) 0)
      (fun y => le_max_right _ _) hin]
    refine hn.trans_le (measure_mono fun y hy => ?_)
    simp only [mem_ofPred_eq] at hy
    simp only [Function.mem_support]
    exact (lt_max_of_lt_left (neg_pos.2 hy)).ne'
  have e1 : ∫ y, h y ∂μ = ∫ y, max (h y) 0 ∂μ - ∫ y, max (-h y) 0 ∂μ := by
    rw [← integral_sub hip hin]
    congr 1; funext y
    rcases le_total (h y) 0 with hy | hy
    · rw [max_eq_right hy, max_eq_left (neg_nonneg.2 hy)]; ring
    · rw [max_eq_left hy, max_eq_right (neg_nonpos.2 hy)]; ring
  have e2 : ∫ y, |h y| ∂μ = ∫ y, max (h y) 0 ∂μ + ∫ y, max (-h y) 0 ∂μ := by
    rw [← integral_add hip hin]
    congr 1; funext y
    rcases le_total (h y) 0 with hy | hy
    · rw [max_eq_right hy, max_eq_left (neg_nonneg.2 hy), abs_of_nonpos hy]; ring
    · rw [max_eq_left hy, max_eq_right (neg_nonpos.2 hy), abs_of_nonneg hy]; ring
  rw [e1, e2, abs_lt]
  constructor <;> linarith

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- A positive function has positive set-integral over a set of positive measure. -/
theorem setLIntegral_pos_of_pos {μ : Measure X} {N : Set X} (hN : MeasurableSet N)
    (hμN : 0 < μ N) {f : X → ℝ≥0∞} (hf : Measurable f) (hpos : ∀ y ∈ N, 0 < f y) :
    0 < ∫⁻ y in N, f y ∂μ := by
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [lintegral_eq_zero_iff hf] at h0
  have h1 : ∀ᵐ y ∂μ, y ∈ N → f y = 0 := (ae_restrict_iff' hN).1 h0
  have h2 : μ {y | ¬ (y ∈ N → f y = 0)} = 0 := ae_iff.1 h1
  have : μ N = 0 := measure_mono_null (fun y hy => by
    simp only [mem_ofPred_eq, Classical.not_imp]
    exact ⟨hy, (hpos y hy).ne'⟩) h2
  exact hμN.ne' this

/-! ### Topological aperiodicity -/

/-- A state `x` is **(topologically) aperiodic** (MT p. 475): `Pᵏ(x, O) > 0` for every open
neighbourhood `O` of `x` and all large `k`. -/
def IsTopAperiodic (P : Kernel X X) (x : X) : Prop :=
  ∀ O : Set X, IsOpen O → x ∈ O → ∃ K : ℕ, ∀ k, K ≤ k → 0 < (P ^ k : Kernel X X) x O

/-- If `Π(x, O) > 0` for an open `O`, then `Pᵏ(x, O) > 0` for some `k` ((D.6)). -/
theorem exists_pow_pos_of_eChainLimit_pos {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    {x : X} {O : Set X} (hO : IsOpen O) (h : 0 < eChainLimit he x O) :
    ∃ k, 0 < (P ^ k : Kernel X X) x O := by
  have hlim := eChainLimit_open_le he hO x
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf (h.trans_le hlim))
  have hpos := hN (N + 1) (Nat.le_succ N)
  rw [cesaroKernel_apply P _ x hO.measurableSet] at hpos
  obtain ⟨i, -, hpi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (pos_iff_ne_zero.1
    (pos_of_mul_pos_right hpos zero_le))
  exact ⟨i, pos_iff_ne_zero.2 hpi⟩

/-- **The sign step** of Proposition 18.4.3 (MT p. 476): if `π = Π(x*, ·)` with `x*` reachable
and aperiodic, and a bounded continuous `g` has `∫ |Pˡg| dπ = ∫ |g| dπ` for all `ℓ`, then `g` does
not change sign on `supp π`: `π{g > 0} = 0` or `π{g < 0} = 0`. -/
theorem sign_of_integral_abs_eq {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (hb : IsBoundedInProbabilityOnAverage P) {x₀ : X} (hx : IsReachable P x₀)
    (hap : IsTopAperiodic P x₀) {g : X → ℝ} (hgc : Continuous g) {B : ℝ}
    (hgB : ∀ x, |g x| ≤ B)
    (hv : ∀ ℓ, ∫ x, |kfunR (P ^ ℓ) g x| ∂eChainLimit he x₀ = ∫ x, |g x| ∂eChainLimit he x₀) :
    eChainLimit he x₀ {x | 0 < g x} = 0 ∨ eChainLimit he x₀ {x | g x < 0} = 0 := by
  set π := eChainLimit he x₀ with hπdef
  have hπp : IsProbabilityMeasure π := ⟨(theorem_12_4_1_iii he).1 hb x₀⟩
  have hπinv : IsInvariant P π := ((theorem_12_4_1_ii he).2 x₀).1
  have hF := he.isWeakFeller
  have hgm := hgc.measurable
  by_contra hboth
  push Not at hboth
  obtain ⟨hp, hn⟩ := hboth
  have hOp : IsOpen {x | 0 < g x} := isOpen_lt continuous_const hgc
  have hOn : IsOpen {x | g x < 0} := isOpen_lt hgc continuous_const
  obtain ⟨kp, hkp⟩ := exists_pow_pos_of_eChainLimit_pos he hOp (pos_iff_ne_zero.2 hp)
  obtain ⟨kn, hkn⟩ := exists_pow_pos_of_eChainLimit_pos he hOn (pos_iff_ne_zero.2 hn)
  set N := {x | 0 < (P ^ kp : Kernel X X) x {x | 0 < g x}} ∩
    {x | 0 < (P ^ kn : Kernel X X) x {x | g x < 0}} with hNdef
  have hN : IsOpen N := ((hF.pow kp) _ hOp).isOpen_preimage 0 |>.inter
    (((hF.pow kn) _ hOn).isOpen_preimage 0)
  obtain ⟨K, hK⟩ := hap N hN ⟨hkp, hkn⟩
  set ℓ := K + kp + kn with hℓ
  have hpos : ∀ {A : Set X} {k₁ k₂ : ℕ}, MeasurableSet A → K ≤ k₁ →
      (∀ z ∈ N, 0 < (P ^ k₂ : Kernel X X) z A) → 0 < (P ^ (k₁ + k₂) : Kernel X X) x₀ A :=
    fun hA hk h => by
      rw [Kernel.pow_add_apply_eq_lintegral P _ _ x₀ hA]
      exact (setLIntegral_pos_of_pos hN.measurableSet (hK _ hk)
        (Kernel.measurable_coe _ hA) h).trans_le (setLIntegral_le_lintegral _ _)
  have hℓp : 0 < (P ^ ℓ : Kernel X X) x₀ {x | 0 < g x} := by
    rw [show ℓ = (K + kn) + kp by omega]
    exact hpos hOp.measurableSet (by omega) fun z hz => hz.1
  have hℓn : 0 < (P ^ ℓ : Kernel X X) x₀ {x | g x < 0} := by
    rw [show ℓ = (K + kp) + kn by omega]
    exact hpos hOn.measurableSet (by omega) fun z hz => hz.2
  set N' := {x | 0 < (P ^ ℓ : Kernel X X) x {x | 0 < g x}} ∩
    {x | 0 < (P ^ ℓ : Kernel X X) x {x | g x < 0}} with hN'def
  have hN' : IsOpen N' := ((hF.pow ℓ) _ hOp).isOpen_preimage 0 |>.inter
    (((hF.pow ℓ) _ hOn).isOpen_preimage 0)
  have hπN' : 0 < π N' := hx.measure_pos hπinv hN' ⟨hℓp, hℓn⟩
  have := isMarkovKernel_pow P ℓ
  have hgi : ∀ z, Integrable g ((P ^ ℓ : Kernel X X) z) := fun z =>
    Integrable.of_bound hgm.aestronglyMeasurable B
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hgB y)
  -- the defect `Pˡ|g| − |Pˡ g| ≥ 0` is positive on `N'`
  set D : X → ℝ := fun z => kfunR (P ^ ℓ) (fun y => |g y|) z - |kfunR (P ^ ℓ) g z| with hD
  have hDnn : ∀ z, 0 ≤ D z := fun z => sub_nonneg.2 (abs_integral_le_integral_abs)
  have hDpos : ∀ z ∈ N', 0 < D z := fun z hz =>
    sub_pos.2 (abs_integral_lt_integral_abs (hgi z) hz.1 hz.2)
  have hgma : Measurable fun y => |g y| := continuous_abs.measurable.comp hgm
  have hkm : Measurable fun z => |kfunR (P ^ ℓ) g z| :=
    continuous_abs.measurable.comp (measurable_kfunR _ hgm)
  have hDm : Measurable D := (measurable_kfunR _ hgma).sub hkm
  have hDb : ∀ z, |D z| ≤ 2 * B := fun z => by
    have h1 := abs_kfunR_le (P ^ ℓ) (f := fun y => |g y|) (fun y => by
      rw [abs_abs]; exact hgB y) z
    have h2 := abs_kfunR_le (P ^ ℓ) hgB z
    rw [abs_of_nonneg (hDnn z)]
    have := le_abs_self (kfunR (P ^ ℓ) (fun y => |g y|) z)
    simp only [hD]
    linarith [abs_nonneg (kfunR (P ^ ℓ) g z)]
  have hDi : Integrable D π := Integrable.of_bound hDm.aestronglyMeasurable (2 * B)
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hDb z)
  have hint : ∫ z, D z ∂π = 0 := by
    have hcomp : ∫ z, kfunR (P ^ ℓ) (fun y => |g y|) z ∂π = ∫ y, |g y| ∂π := by
      change ∫ z, (∫ y, |g y| ∂(P ^ ℓ : Kernel X X) z) ∂π = _
      rw [← integral_comp_kernel_of_bdd (P ^ ℓ) π hgma (fun y => by
        rw [abs_abs]; exact hgB y), (hπinv.pow ℓ :)]
    have hi1 : Integrable (kfunR (P ^ ℓ) (fun y => |g y|)) π :=
      Integrable.of_bound (measurable_kfunR _ hgma).aestronglyMeasurable B
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact abs_kfunR_le _ (fun y => by rw [abs_abs]; exact hgB y) z)
    have hi2 : Integrable (fun z => |kfunR (P ^ ℓ) g z|) π :=
      Integrable.of_bound hkm.aestronglyMeasurable B
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_abs]; exact abs_kfunR_le _ hgB z)
    rw [hD, integral_sub hi1 hi2, hcomp, hv ℓ, sub_self]
  have hsupp : 0 < π (Function.support D) :=
    hπN'.trans_le (measure_mono fun z hz => (hDpos z hz).ne')
  have := (integral_pos_iff_support_of_nonneg hDnn hDi).2 hsupp
  rw [hint] at this
  exact lt_irrefl _ this

/-! ### Proposition 18.4.3 -/

/-- **The core of Proposition 18.4.3**: for `f ∈ C_c(X)` and `y ∈ supp π`, `Pᵏf(y) → π(f)`. With
`Fₖ = Pᵏf − π(f)`, `∫ |Fₖ| dπ` decreases to some `v`; along a subsequence `Fₙᵢ → g` pointwise
(Ascoli), and `∫ |Pˡg| dπ = v = ∫ |g| dπ`, `∫ g dπ = 0` (18.27); so `g` does not change sign and
vanishes on `supp π`. -/
theorem tendsto_pow_cc_of_mem_support {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (hb : IsBoundedInProbabilityOnAverage P) {x₀ : X} (hx : IsReachable P x₀)
    (hap : IsTopAperiodic P x₀) (f : C_c(X, ℝ)) {y : X} (hy : y ∈ (eChainLimit he x₀).support) :
    Tendsto (fun k => ∫ z, f z ∂(P ^ k : Kernel X X) y) atTop
      (𝓝 (∫ z, f z ∂eChainLimit he x₀)) := by
  set π := eChainLimit he x₀ with hπdef
  have hπp : IsProbabilityMeasure π := ⟨(theorem_12_4_1_iii he).1 hb x₀⟩
  have hπinv : IsInvariant P π := ((theorem_12_4_1_ii he).2 x₀).1
  have hfm := (map_continuous f).measurable
  obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc f
  set c := ∫ z, f z ∂π with hc
  have hcB : |c| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := π) (f := f) (C := B)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)
    simpa using this
  set F : ℕ → X → ℝ := fun k x => kfunR (P ^ k) f x - c with hFdef
  have hpow := isMarkovKernel_pow P
  have hFm : ∀ k, Measurable (F k) := fun k => (measurable_kfunR _ hfm).sub_const c
  have hFB : ∀ k x, |F k x| ≤ 2 * B := fun k x => by
    have := abs_kfunR_le (P ^ k) hB x
    calc |F k x| ≤ |kfunR (P ^ k) f x| + |c| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hfi : ∀ μ : Measure X, IsFiniteMeasure μ → Integrable f μ := fun μ _ =>
    Integrable.of_bound hfm.aestronglyMeasurable B
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)
  have hint : ∀ {μ : Measure X} [IsFiniteMeasure μ] {h : X → ℝ}, Measurable h →
      ∀ C : ℝ, (∀ x, |h x| ≤ C) → Integrable h μ := fun hm C hC =>
    Integrable.of_bound hm.aestronglyMeasurable C
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hC z)
  -- `F (k + ℓ) = Pˡ F k`
  have hstep : ∀ k ℓ x, F (k + ℓ) x = ∫ z, F k z ∂(P ^ ℓ : Kernel X X) x := fun k ℓ x => by
    have e1 : kfunR (P ^ (k + ℓ)) f x = ∫ z, kfunR (P ^ k) f z ∂(P ^ ℓ : Kernel X X) x := by
      rw [kfunR, pow_add]
      change ∫ w, f w ∂((P ^ k : Kernel X X) ∘ₖ (P ^ ℓ : Kernel X X)) x = _
      rw [Kernel.integral_comp (hfi _ inferInstance)]
      rfl
    simp only [hFdef]
    rw [e1, integral_sub (hint (measurable_kfunR _ hfm) B (abs_kfunR_le _ hB))
      (integrable_const c), integral_const, probReal_univ, one_smul]
  -- `∫ F k dπ = 0`
  have hzero : ∀ k, ∫ x, F k x ∂π = 0 := fun k => by
    simp only [hFdef]
    rw [integral_sub (hint (measurable_kfunR _ hfm) B (abs_kfunR_le _ hB)) (integrable_const c),
      integral_const, probReal_univ, one_smul]
    change ∫ x, (∫ y, f y ∂(P ^ k : Kernel X X) x) ∂π - c = 0
    rw [← integral_comp_kernel_of_bdd (P ^ k) π hfm hB, (hπinv.pow k :), sub_self]
  -- `a k = ∫ |F k| dπ` decreases
  set a : ℕ → ℝ := fun k => ∫ x, |F k x| ∂π with ha
  have haF : ∀ k, Integrable (fun x => |F k x|) π := fun k =>
    hint (continuous_abs.measurable.comp (hFm k)) (2 * B) fun x => by rw [abs_abs]; exact hFB k x
  have hanti : Antitone a := antitone_nat_of_succ_le fun k => by
    have h1 : ∀ x, |F (k + 1) x| ≤ ∫ z, |F k z| ∂P x := fun x => by
      rw [hstep k 1 x, pow_one]
      exact abs_integral_le_integral_abs
    calc a (k + 1) ≤ ∫ x, (∫ z, |F k z| ∂P x) ∂π :=
          integral_mono (haF (k + 1)) (hint (measurable_kfunR P
            (continuous_abs.measurable.comp (hFm k))) (2 * B)
            (abs_kfunR_le P fun x => by rw [abs_abs]; exact hFB k x)) h1
      _ = a k := by
          rw [← integral_comp_kernel_of_bdd P π (f := fun z => |F k z|)
            (continuous_abs.measurable.comp (hFm k))
            (fun x => by rw [abs_abs]; exact hFB k x), (hπinv :)]
  have hbdd : BddBelow (Set.range a) := ⟨0, by
    rintro _ ⟨k, rfl⟩; exact integral_nonneg fun x => abs_nonneg _⟩
  set v := ⨅ k, a k with hv
  have ha_lim : Tendsto a atTop (𝓝 v) := tendsto_atTop_ciInf hanti hbdd
  -- equicontinuity of `F`
  have hFeq : ∀ x, EquicontinuousAt F x := fun x => by
    have h := he.equicontinuousAt f x
    rw [Metric.equicontinuousAt_iff_right] at h ⊢
    intro ε hε
    filter_upwards [h ε hε] with z hz k
    have := hz k
    simp only [hFdef, kfunR, Real.dist_eq] at this ⊢
    rwa [show ∫ y, f y ∂(P ^ k : Kernel X X) x - c - (∫ y, f y ∂(P ^ k : Kernel X X) z - c) =
      ∫ y, f y ∂(P ^ k : Kernel X X) x - ∫ y, f y ∂(P ^ k : Kernel X X) z by ring]
  -- the subsequence argument
  have hFy : Tendsto (fun k => F k y) atTop (𝓝 0) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨φ, hφ, g, hgc, hconv⟩ := exists_subseq_tendsto_of_equicontinuousAt hFB hFeq ns
    set n : ℕ → ℕ := fun i => ns (φ i) with hn
    have hnt : Tendsto n atTop atTop := hns.comp hφ.tendsto_atTop
    have hgB : ∀ x, |g x| ≤ 2 * B := fun x =>
      le_of_tendsto' ((continuous_abs.tendsto _).comp (hconv x)) fun i => hFB _ x
    have hgm := hgc.measurable
    set Q : ℕ → X → ℝ := fun ℓ x => kfunR (P ^ ℓ) g x with hQ
    have hQconv : ∀ ℓ x, Tendsto (fun i => F (n i + ℓ) x) atTop (𝓝 (Q ℓ x)) := fun ℓ x => by
      simp_rw [hstep _ ℓ x]
      exact tendsto_integral_of_dominated_convergence (fun _ => 2 * B)
        (fun i => (hFm _).aestronglyMeasurable) (integrable_const _)
        (fun i => Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hFB _ z)
        (Eventually.of_forall fun z => hconv z)
    have hQB : ∀ ℓ x, |Q ℓ x| ≤ 2 * B := fun ℓ x => abs_kfunR_le _ hgB x
    have hQm : ∀ ℓ, Measurable (Q ℓ) := fun ℓ => measurable_kfunR _ hgm
    have hQint : ∀ ℓ, ∫ x, Q ℓ x ∂π = 0 := fun ℓ => by
      have h := tendsto_integral_of_dominated_convergence (μ := π) (fun _ => 2 * B)
        (fun i => (hFm (n i + ℓ)).aestronglyMeasurable) (integrable_const _)
        (fun i => Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hFB _ z)
        (Eventually.of_forall fun z => hQconv ℓ z)
      simp_rw [hzero] at h
      exact (tendsto_nhds_unique h tendsto_const_nhds).symm.symm
    have hQabs : ∀ ℓ, ∫ x, |Q ℓ x| ∂π = v := fun ℓ => by
      have h := tendsto_integral_of_dominated_convergence (μ := π) (fun _ => 2 * B)
        (fun i => (continuous_abs.measurable.comp (hFm (n i + ℓ))).aestronglyMeasurable)
        (integrable_const _)
        (fun i => Eventually.of_forall fun z => by
          simp only [Function.comp_apply, Real.norm_eq_abs, abs_abs]; exact hFB _ z)
        (Eventually.of_forall fun z => (continuous_abs.tendsto _).comp (hQconv ℓ z))
      have h2 : Tendsto (fun i => a (n i + ℓ)) atTop (𝓝 v) :=
        ha_lim.comp (tendsto_atTop_mono (fun i => Nat.le_add_right _ _) hnt)
      exact tendsto_nhds_unique h h2
    have hQ0 : ∀ x, Q 0 x = g x := fun x => by
      simp only [hQ, kfunR]
      rw [pow_zero_apply, integral_dirac]
    have hgabs : ∫ x, |g x| ∂π = v := by
      have := hQabs 0; simp_rw [hQ0] at this; exact this
    have hgint : ∫ x, g x ∂π = 0 := by
      have := hQint 0; simp_rw [hQ0] at this; exact this
    have hsign := sign_of_integral_abs_eq he hb hx hap hgc hgB fun ℓ => by
      rw [hgabs]; exact hQabs ℓ
    -- `g = 0` on `supp π`
    have hg0 : g y = 0 := by
      have hgi : Integrable g π := hint hgm (2 * B) hgB
      have hae : g =ᵐ[π] 0 := by
        rcases hsign with h | h
        · have hle : g ≤ᵐ[π] 0 := by
            rw [EventuallyLE, ae_iff]
            simpa [not_le] using h
          have h1 : ∫ x, -g x ∂π = 0 := by rw [integral_neg, hgint, neg_zero]
          have h2 := (integral_eq_zero_iff_of_nonneg_ae (hle.mono fun x hx => by
            simpa using hx) hgi.neg).1 h1
          exact h2.mono fun x hx => by simpa using hx
        · have hle : 0 ≤ᵐ[π] g := by
            rw [EventuallyLE, ae_iff]
            simpa [not_le] using h
          exact (integral_eq_zero_iff_of_nonneg_ae hle hgi).1 hgint
      by_contra hne
      have hU : IsOpen {x | g x ≠ 0} := isOpen_ne_fun hgc continuous_const
      have hpos := (Measure.mem_support_iff_forall y).1 hy _ (hU.mem_nhds hne)
      have h0 : π {x | ¬ g x = (0 : X → ℝ) x} = 0 := ae_iff.1 hae
      exact hpos.ne' h0
    exact ⟨φ, by rw [← hg0]; exact hconv y⟩
  have := hFy.add_const c
  simp only [hFdef, sub_add_cancel, zero_add] at this
  exact this

/-- **Proposition 18.4.3** (MT p. 475): for an e-chain bounded in probability on average with a
reachable aperiodic state `x*` and `π = Π(x*, ·)`, `Pᵏ(y, ·) → π` weakly for every `y ∈ supp π`,
(18.26). -/
theorem proposition_18_4_3 {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (hb : IsBoundedInProbabilityOnAverage P) {x₀ : X} (hx : IsReachable P x₀)
    (hap : IsTopAperiodic P x₀) {y : X} (hy : y ∈ (eChainLimit he x₀).support) (f : X →ᵇ ℝ) :
    Tendsto (fun k => ∫ z, f z ∂(P ^ k : Kernel X X) y) atTop
      (𝓝 (∫ z, f z ∂eChainLimit he x₀)) := by
  have hπp : IsProbabilityMeasure (eChainLimit he x₀) := ⟨(theorem_12_4_1_iii he).1 hb x₀⟩
  have : ∀ n, IsProbabilityMeasure ((P ^ n : Kernel X X) y) := fun n => by
    have := isMarkovKernel_pow P n; infer_instance
  exact tendsto_integral_bcf_of_cc (fun g => tendsto_pow_cc_of_mem_support he hb hx hap g hy) f

/-! ### Theorem 18.4.4 (ii) -/

/-- **Theorem 18.4.4 (ii)**, direct half (MT p. 477): for an e-chain bounded in probability on
average with a reachable aperiodic state `x*`, `Pᵏ(x, ·) → π` weakly for every `x`, where
`π = Π(x*, ·)` is the unique invariant probability, (18.29). The set
`O_ε ⊇ supp π` on which `|Pᵏf − π(f)| < ε` eventually is open (equicontinuity), has
`π(O_ε) = 1`, and the chain from `x` enters it at some time `N₀` with probability `≥ 1 − ε`. -/
theorem theorem_18_4_4_ii {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (hb : IsBoundedInProbabilityOnAverage P) {x₀ : X} (hx : IsReachable P x₀)
    (hap : IsTopAperiodic P x₀) (x : X) (f : X →ᵇ ℝ) :
    Tendsto (fun k => ∫ z, f z ∂(P ^ k : Kernel X X) x) atTop
      (𝓝 (∫ z, f z ∂eChainLimit he x₀)) := by
  set π := eChainLimit he x₀ with hπdef
  have hπp : IsProbabilityMeasure π := ⟨(theorem_12_4_1_iii he).1 hb x₀⟩
  have hNE := proposition_12_1_1 hb
  have hconst := eChainLimit_eq_of_isReachable he hNE hx
  have : ∀ n, IsProbabilityMeasure ((P ^ n : Kernel X X) x) := fun n => by
    have := isMarkovKernel_pow P n; infer_instance
  refine tendsto_integral_bcf_of_cc (fun g => ?_) f
  have hpow := isMarkovKernel_pow P
  have hgm := (map_continuous g).measurable
  obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc g
  set c := ∫ z, g z ∂π with hc
  have hcB : |c| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := π) (f := g) (C := B)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)
    simpa using this
  set F : ℕ → X → ℝ := fun k y => kfunR (P ^ k) g y - c with hFdef
  have hFm : ∀ k, Measurable (F k) := fun k => (measurable_kfunR _ hgm).sub_const c
  have hFB : ∀ k y, |F k y| ≤ 2 * B := fun k y => by
    have := abs_kfunR_le (P ^ k) hB y
    calc |F k y| ≤ |kfunR (P ^ k) g y| + |c| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hstep : ∀ k ℓ y, F (k + ℓ) y = ∫ z, F k z ∂(P ^ ℓ : Kernel X X) y := fun k ℓ y => by
    have hgi : Integrable g ((P ^ k : Kernel X X) ∘ₖ (P ^ ℓ : Kernel X X) <| y) :=
      Integrable.of_bound hgm.aestronglyMeasurable B
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)
    have e1 : kfunR (P ^ (k + ℓ)) g y = ∫ z, kfunR (P ^ k) g z ∂(P ^ ℓ : Kernel X X) y := by
      rw [kfunR, pow_add]
      change ∫ w, g w ∂((P ^ k : Kernel X X) ∘ₖ (P ^ ℓ : Kernel X X)) y = _
      rw [Kernel.integral_comp hgi]
      rfl
    simp only [hFdef]
    rw [e1, integral_sub (Integrable.of_bound (measurable_kfunR _ hgm).aestronglyMeasurable B
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact abs_kfunR_le _ hB z))
      (integrable_const c), integral_const, probReal_univ, one_smul]
  -- convergence on `supp π`
  have hsupp : ∀ y ∈ π.support, Tendsto (fun k => F k y) atTop (𝓝 0) := fun y hy => by
    have h := tendsto_pow_cc_of_mem_support he hb hx hap g hy
    have := h.sub_const c
    rw [← hπdef, ← hc, sub_self] at this
    exact this
  rw [← sub_zero c]
  suffices hF0 : Tendsto (fun k => F k x) atTop (𝓝 0) by
    have := hF0.add_const c
    simp only [hFdef, sub_add_cancel, zero_add] at this
    simpa [kfunR] using this
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε := δ / (2 * B + 4) with hε
  have hε0 : 0 < ε := by positivity
  -- the open set `O_ε`
  have hnb : ∀ y : X, ∃ U ∈ 𝓝 y, ∀ z ∈ U, ∀ k, |F k z - F k y| < ε := fun y => by
    have h := Metric.equicontinuousAt_iff_right.1 (he.equicontinuousAt g y) ε hε0
    obtain ⟨U, hU, hUs⟩ := (Filter.eventually_iff_exists_mem.1 h)
    refine ⟨U, hU, fun z hz k => ?_⟩
    have := hUs z hz k
    rw [Real.dist_eq, abs_sub_comm] at this
    simpa [hFdef, kfunR] using this
  choose U hU hUprop using hnb
  set O := ⋃ y ∈ π.support, interior (U y) with hO
  have hOopen : IsOpen O := isOpen_biUnion fun y _ => isOpen_interior
  have hsuppO : π.support ⊆ O := fun y hy =>
    mem_iUnion₂.2 ⟨y, hy, mem_interior_iff_mem_nhds.2 (hU y)⟩
  have hOev : ∀ z ∈ O, ∀ᶠ k in atTop, |F k z| < 2 * ε := fun z hz => by
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hz
    filter_upwards [(Metric.tendsto_nhds.1 (hsupp y hy)) ε hε0] with k hk
    have h1 := hUprop y z (interior_subset hzy) k
    rw [Real.dist_eq, sub_zero] at hk
    calc |F k z| ≤ |F k z - F k y| + |F k y| := by
          have := abs_sub_abs_le_abs_sub (F k z) (F k y); linarith
      _ < ε + ε := add_lt_add h1 hk
      _ = 2 * ε := by ring
  have hπO : π O = 1 := by
    have h1 : π Oᶜ = 0 := measure_mono_null (compl_subset_compl.2 hsuppO)
      Measure.measure_compl_support
    exact (prob_compl_eq_zero_iff hOopen.measurableSet).1 h1
  -- the chain enters `O_ε`
  obtain ⟨i, hi⟩ : ∃ i, 1 - ENNReal.ofReal ε < (P ^ i : Kernel X X) x O := by
    have hlim := eChainLimit_open_le he hOopen x
    rw [hconst x, hπO] at hlim
    have hlt : 1 - ENNReal.ofReal ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
      (ENNReal.ofReal_pos.2 hε0).ne'
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf (hlt.trans_le hlim))
    have h := hN (N + 1) (Nat.le_succ N)
    rw [cesaroKernel_apply P _ x hOopen.measurableSet] at h
    by_contra hall
    push Not at hall
    have hsum : ∑ i ∈ Finset.Icc 1 (N + 1), (P ^ i : Kernel X X) x O ≤
        (N + 1 : ℕ) * (1 - ENNReal.ofReal ε) := by
      calc ∑ i ∈ Finset.Icc 1 (N + 1), (P ^ i : Kernel X X) x O
          ≤ ∑ i ∈ Finset.Icc 1 (N + 1), (1 - ENNReal.ofReal ε) :=
            Finset.sum_le_sum fun i _ => hall i
        _ = (N + 1 : ℕ) * (1 - ENNReal.ofReal ε) := by simp
    have : ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 (N + 1), (P ^ i : Kernel X X) x O ≤
        1 - ENNReal.ofReal ε := by
      calc _ ≤ ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * ((N + 1 : ℕ) * (1 - ENNReal.ofReal ε)) := by
            gcongr
        _ = 1 - ENNReal.ofReal ε := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _),
              one_mul]
    exact absurd h (not_lt.2 this)
  have hiO : (P ^ i : Kernel X X) x Oᶜ ≤ ENNReal.ofReal ε := by
    rw [prob_compl_eq_one_sub hOopen.measurableSet]
    exact tsub_le_iff_tsub_le.1 hi.le
  -- dominated convergence for the excess on `O`
  set h : ℕ → X → ℝ := fun k z => O.indicator (fun z => max (|F k z| - 2 * ε) 0) z with hh
  have hhm : ∀ k, Measurable (h k) := fun k =>
    ((continuous_abs.measurable.comp (hFm k)).sub_const _).max measurable_const |>.indicator
      hOopen.measurableSet
  have hlimh : Tendsto (fun k => ∫ z, h k z ∂(P ^ i : Kernel X X) x) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := (P ^ i : Kernel X X) x)
      (F := h) (f := fun _ => 0) (fun _ => 2 * B) (fun k => (hhm k).aestronglyMeasurable)
      (integrable_const _)
      (fun k => Eventually.of_forall fun z => by
        simp only [hh, Real.norm_eq_abs]
        by_cases hz : z ∈ O
        · rw [indicator_of_mem hz, abs_of_nonneg (le_max_right _ _)]
          exact max_le (by linarith [hFB k z, hε0]) (by linarith)
        · rw [indicator_of_notMem hz, abs_zero]; linarith)
      (Eventually.of_forall fun z => by
        by_cases hz : z ∈ O
        · refine tendsto_const_nhds.congr' ?_
          filter_upwards [hOev z hz] with k hk
          simp only [hh, indicator_of_mem hz]
          exact (max_eq_right (by linarith)).symm
        · simp only [hh, indicator_of_notMem hz]; exact tendsto_const_nhds)
    simpa using this
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hlimh) ε hε0
  refine ⟨i + K, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hk : K ≤ n - i := by omega
  have hn' : n = (n - i) + i := by omega
  rw [hn', hstep (n - i) i x]
  have hK' := hK (n - i) hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun z => by
    simp only [hh]; exact indicator_nonneg (fun z _ => le_max_right _ _) z)] at hK'
  have hFi : Integrable (F (n - i)) ((P ^ i : Kernel X X) x) :=
    Integrable.of_bound (hFm _).aestronglyMeasurable (2 * B)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hFB _ z)
  have hbound : ∀ z, |F (n - i) z| ≤ 2 * B * Oᶜ.indicator 1 z + 2 * ε + h (n - i) z := fun z => by
    simp only [hh]
    by_cases hz : z ∈ O
    · rw [indicator_of_notMem (show z ∉ Oᶜ from fun h => h hz), indicator_of_mem hz]
      have := le_max_left (|F (n - i) z| - 2 * ε) 0
      linarith
    · rw [indicator_of_mem (show z ∈ Oᶜ from hz), indicator_of_notMem hz, Pi.one_apply]
      linarith [hFB (n - i) z]
  calc |∫ z, F (n - i) z ∂(P ^ i : Kernel X X) x|
      ≤ ∫ z, |F (n - i) z| ∂(P ^ i : Kernel X X) x := abs_integral_le_integral_abs
    _ ≤ ∫ z, (2 * B * Oᶜ.indicator 1 z + 2 * ε + h (n - i) z) ∂(P ^ i : Kernel X X) x := by
        refine integral_mono hFi.abs ?_ hbound
        refine ((((integrable_const 1).indicator hOopen.measurableSet.compl).const_mul
          (2 * B)).add (integrable_const _)).add ?_
        exact Integrable.of_bound (hhm _).aestronglyMeasurable (2 * B)
          (Eventually.of_forall fun z => by
            simp only [hh, Real.norm_eq_abs]
            by_cases hz : z ∈ O
            · rw [indicator_of_mem hz, abs_of_nonneg (le_max_right _ _)]
              exact max_le (by linarith [hFB (n - i) z, hε0]) (by linarith)
            · rw [indicator_of_notMem hz, abs_zero]; linarith)
    _ = 2 * B * ((P ^ i : Kernel X X) x).real Oᶜ + 2 * ε +
          ∫ z, h (n - i) z ∂(P ^ i : Kernel X X) x := by
        rw [integral_add, integral_add, integral_const_mul, integral_indicator_one
          hOopen.measurableSet.compl, integral_const, probReal_univ, one_smul]
        · exact ((integrable_const 1).indicator hOopen.measurableSet.compl).const_mul _
        · exact integrable_const _
        · exact (((integrable_const 1).indicator hOopen.measurableSet.compl).const_mul
            _).add (integrable_const _)
        · exact Integrable.of_bound (hhm _).aestronglyMeasurable (2 * B)
            (Eventually.of_forall fun z => by
              simp only [hh, Real.norm_eq_abs]
              by_cases hz : z ∈ O
              · rw [indicator_of_mem hz, abs_of_nonneg (le_max_right _ _)]
                exact max_le (by linarith [hFB (n - i) z, hε0]) (by linarith)
              · rw [indicator_of_notMem hz, abs_zero]; linarith)
    _ < 2 * B * ε + 2 * ε + ε := by
        have h1 : ((P ^ i : Kernel X X) x).real Oᶜ ≤ ε := by
          rw [measureReal_def]
          exact ENNReal.toReal_le_of_le_ofReal hε0.le hiO
        have : 2 * B * ((P ^ i : Kernel X X) x).real Oᶜ ≤ 2 * B * ε :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
        linarith
    _ ≤ δ := by
        have h4 : (0 : ℝ) < 2 * B + 4 := by linarith
        have h5 : ε * (2 * B + 4) = δ := by rw [hε]; field_simp
        nlinarith [hε0]

/-- **Theorem 18.4.4 (ii)**, converse (MT p. 477, "straightforward"): if `Pᵏ(x, ·) → π` weakly for
every `x`, every state of `supp π` is reachable, aperiodic and (topologically) recurrent: for an
open `O ∋ x*` there is `f ∈ C_c(X)`, `0 ≤ f ≤ 1_O`, with `π(f) > 0`, and `Pᵏ(y, O) ≥ Pᵏf(y)` is
eventually at least `π(f)/2`. -/
theorem theorem_18_4_4_ii_converse {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π]
    (h : ∀ x (f : X →ᵇ ℝ), Tendsto (fun k => ∫ z, f z ∂(P ^ k : Kernel X X) x) atTop
      (𝓝 (∫ z, f z ∂π))) {x₀ : X} (hx : x₀ ∈ π.support) :
    IsReachable P x₀ ∧ IsTopAperiodic P x₀ ∧ IsTopRecurrent P x₀ := by
  have hpow := isMarkovKernel_pow P
  have key : ∀ O : Set X, IsOpen O → x₀ ∈ O → ∃ c : ℝ, 0 < c ∧ ∀ y, ∀ᶠ k in atTop,
      ENNReal.ofReal c ≤ (P ^ k : Kernel X X) y O := fun O hO hxO => by
    have hπO : 0 < π O := (Measure.mem_support_iff_forall x₀).1 hx O (hO.mem_nhds hxO)
    obtain ⟨K, hKO, hK, hπK⟩ := hO.exists_lt_isCompact hπO
    obtain ⟨f, hf1, hf0, hfc, hf01⟩ :=
      exists_continuous_one_zero_of_isCompact hK hO.isClosed_compl
        (disjoint_compl_right_iff_subset.2 hKO)
    set fc : C_c(X, ℝ) := ⟨f, hfc⟩
    have hfi : ∀ μ : Measure X, IsFiniteMeasure μ → Integrable f μ := fun μ _ =>
      Integrable.of_bound (map_continuous f).aestronglyMeasurable 1
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hf01 z).1]; exact (hf01 z).2)
    have hpos : 0 < ∫ z, f z ∂π := by
      have h1 : π.real K ≤ ∫ z, f z ∂π :=
        measureReal_le_integral_of_indicator_le hK.measurableSet (hfi π inferInstance)
          fun y => by
            by_cases hy : y ∈ K
            · rw [indicator_of_mem hy, Pi.one_apply]; exact (hf1 hy).ge
            · rw [indicator_of_notMem hy]; exact (hf01 y).1
      have h2 : 0 < π.real K := ENNReal.toReal_pos hπK.ne' (measure_ne_top _ _)
      linarith
    refine ⟨(∫ z, f z ∂π) / 2, by positivity, fun y => ?_⟩
    have hconv := h y fc.toBoundedContinuousFunction
    simp only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] at hconv
    filter_upwards [hconv.eventually (lt_mem_nhds (half_lt_self hpos))] with k hk
    have hle : ENNReal.ofReal (∫ z, f z ∂(P ^ k : Kernel X X) y) ≤ (P ^ k : Kernel X X) y O := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top ((P ^ k : Kernel X X) y) O),
        ← measureReal_def]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← integral_indicator_one hO.measurableSet]
      refine integral_mono (hfi _ inferInstance)
        ((integrable_const 1).indicator hO.measurableSet) fun z => ?_
      by_cases hz : z ∈ O
      · rw [indicator_of_mem hz, Pi.one_apply]; exact (hf01 z).2
      · rw [indicator_of_notMem hz]; exact (hf0 hz).le
    exact (ENNReal.ofReal_le_ofReal hk.le).trans hle
  refine ⟨fun O hO hxO y => ?_, fun O hO hxO => ?_, fun O hO hxO => ?_⟩
  · obtain ⟨c, hc, hev⟩ := key O hO hxO
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hev y)
    rw [potKernel_pos_iff P hO.measurableSet y]
    exact ⟨N, (ENNReal.ofReal_pos.2 hc).trans_le (hN (N + 1) (Nat.le_succ N))⟩
  · obtain ⟨c, hc, hev⟩ := key O hO hxO
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hev x₀)
    exact ⟨N, fun k hk => (ENNReal.ofReal_pos.2 hc).trans_le (hN k hk)⟩
  · obtain ⟨c, hc, hev⟩ := key O hO hxO
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hev x₀)
    rw [potKernel_apply P x₀ hO.measurableSet, eq_top_iff]
    calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, ENNReal.ofReal c :=
          (ENNReal.tsum_const_eq_top_of_ne_zero (ENNReal.ofReal_pos.2 hc).ne').symm
      _ ≤ ∑' n : ℕ, (P ^ (n + N + 1) : Kernel X X) x₀ O :=
          ENNReal.tsum_le_tsum fun n => hN _ (by omega)
      _ ≤ ∑' n : ℕ, (P ^ (n + 1) : Kernel X X) x₀ O :=
          ENNReal.tsum_comp_le_tsum_of_injective (f := fun n => n + N)
            (fun a b hab => by simpa using hab) (fun m => (P ^ (m + 1) : Kernel X X) x₀ O)

end MeynTweedie.Positivity

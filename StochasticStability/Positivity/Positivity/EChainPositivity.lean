/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.TChainPositivity
import Positivity.EChainCriteria

/-!
# Positivity and e-chains: reachability (MT §18.4.1, Theorem 18.4.4 (i))

Meyn and Tweedie, pp. 473–477. `X` is a locally compact, second-countable, metrizable Hausdorff
space with its Borel σ-algebra; `Π = eChainLimit he` is the limit kernel of Theorem 12.4.1.

**Tools.**
* `IsEChain.isWeakFeller`: an e-chain is weak Feller.
* `IsReachable.hitProb_pos`, `IsReachable.measure_pos`: a reachable state is reached from
  everywhere and lies in the support of every invariant probability.
* `harmonic_eq_of_isReachable`: for a non-evanescent weak Feller chain with a reachable state,
  bounded continuous harmonic functions are constant (the martingale argument of p. 474).
* `eChainLimit_eq_of_isReachable`: `Π(y, ·) = Π(x*, ·)` for every `y`.
* `limsup_cesaro_le`: Cesàro means of a sequence tending to `0` tend to `0`.

**Results.**
* **Lemma 18.4.1** (`lemma_18_4_1`, p. 474): for a weak Feller chain with a reachable `x*` and an
  open `O ∋ x*` with compact closure, `{Φ → ∞} = {Φ ∈ O i.o.}ᶜ` almost surely.
* **Proposition 18.4.2** (`proposition_18_4_2`, p. 474): for a non-evanescent e-chain with a
  reachable `x*`: (i) a unique invariant probability `π` with `P̄ₖ(x, ·) → π` weakly ⇔ (ii) bounded
  in probability on average ⇔ (iii) `x*` positive, read as `IsCesaroPositive`
  (`lim sup P̄ⁿ(x*, O) > 0`); `IsCesaroPositive.isTopPositive`: this implies positivity in the
  sense of p. 473.
* **Theorem 18.4.4 (i)** (`theorem_18_4_4_i`, p. 476): an e-chain bounded in probability on
  average has a unique invariant probability iff it has a reachable state.

**Hypotheses.**
* Proposition 18.4.2 (iii): the book's "`x*` is positive" (p. 473: `lim sup Pⁿ(x*, O) > 0` for every
  neighbourhood `O`) is used in the proof only through "`Π(x*, X) > 0`", which needs the Cesàro
  averages: positivity of `lim sup Pⁿ` along a sparse set of times does not bound the Cesàro limit
  `Π(x*, ·)` from below. The equivalence is proved with (iii) in the Cesàro form; the Cesàro form
  implies the book's form (`IsCesaroPositive.isTopPositive`).
* **Open question.** Whether the book's form alone suffices is not settled. Precisely: for a
  non-evanescent e-chain with a reachable `x*` and `Π(·, X) ≡ 0`, can `lim sup Pⁿ(x*, O) > 0`
  hold for every open `O ∋ x*` while the Cesàro averages `P̄ⁿ(x*, O) → 0`? If not, `IsTopPositive`
  can replace `IsCesaroPositive` in Proposition 18.4.2 (iii) and Theorem 18.0.2 (ii) (c).
  It cannot happen (not formalised here) when `X` is countable and discrete (a positive state is
  positive recurrent on the closed class of `x*`, Theorem 18.2.1) or when `x*` is isolated
  (`{x*}` is then an accessible atom, so the chain is `δ_{x*}`-irreducible and not null by
  Theorem 18.2.2 (ii)). In general, the approximate renewal argument at an equicontinuity
  neighbourhood of `x*` loses control because the errors add up over many renewals.
* The converse half of Theorem 18.4.4 (i) ("a unique invariant probability gives a reachable
  state") is not proved in the book ("follows immediately from Proposition 18.4.2"); the proof
  here takes a point of `supp π`.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]

/-! ### e-chains are Feller -/

/-- An e-chain is weak Feller: `Pf` is continuous for `f ∈ C_c(X)` (the case `k = 1` of the
equicontinuity), and `P(·, O)` is a supremum of such `Pf` by inner regularity. -/
theorem IsEChain.isWeakFeller {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P) :
    IsWeakFeller P := by
  intro O hO x t ht
  obtain ⟨K, hKO, hK, htK⟩ := hO.exists_lt_isCompact ht
  obtain ⟨f, hf1, hf0, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hK hO.isClosed_compl
      (disjoint_compl_right_iff_subset.2 hKO)
  obtain ⟨K', hK', hxK'⟩ := exists_compact_mem_nhds x
  have heq := he f (map_continuous f) hfc K' hK'
  have hcont : ContinuousAt (fun x => ∫ y, f y ∂(P ^ 1 : Kernel X X) x) x :=
    ((heq x (mem_of_mem_nhds hxK')).continuousWithinAt 1).continuousAt hxK'
  simp only [pow_one] at hcont
  have hfi : ∀ z, Integrable f (P z) := fun z =>
    (map_continuous f).integrable_of_hasCompactSupport hfc
  have hKf : ∀ z, P z K ≤ ENNReal.ofReal (∫ y, f y ∂P z) := fun z => by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ K), ← measureReal_def]
    exact ENNReal.ofReal_le_ofReal (measureReal_le_integral_of_indicator_le hK.measurableSet
      (hfi z) fun y => by
        by_cases hy : y ∈ K
        · rw [indicator_of_mem hy, Pi.one_apply]; exact (hf1 hy).ge
        · rw [indicator_of_notMem hy]; exact (hf01 y).1)
  have hfO : ∀ z, ENNReal.ofReal (∫ y, f y ∂P z) ≤ P z O := fun z => by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (P z) O), ← measureReal_def]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← integral_indicator_one hO.measurableSet]
    refine integral_mono (hfi z) ((integrable_const 1).indicator hO.measurableSet) fun y => ?_
    by_cases hy : y ∈ O
    · rw [indicator_of_mem hy, Pi.one_apply]; exact (hf01 y).2
    · rw [indicator_of_notMem hy]; exact (hf0 hy).le
  have htt : t ≠ ∞ := ne_top_of_lt (htK.trans_le prob_le_one)
  have hlt : t.toReal < ∫ y, f y ∂P x := by
    have := htK.trans_le (hKf x)
    rwa [← ENNReal.ofReal_toReal htt, ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      ENNReal.toReal_nonneg] at this
  filter_upwards [hcont.eventually (lt_mem_nhds hlt)] with z hz
  calc t = ENNReal.ofReal t.toReal := (ENNReal.ofReal_toReal htt).symm
    _ < ENNReal.ofReal (∫ y, f y ∂P z) := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        ENNReal.toReal_nonneg).2 hz
    _ ≤ P z O := hfO z

/-! ### Lemma 18.4.1 -/

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- A reachable state is reached from everywhere: `L(y, O) > 0` for every open `O ∋ x*`. -/
theorem IsReachable.hitProb_pos {P : Kernel X X} [IsMarkovKernel P] {x₀ : X}
    (hx : IsReachable P x₀) {O : Set X} (hO : IsOpen O) (hxO : x₀ ∈ O) (y : X) :
    0 < hitProb P O y :=
  (hitProb_pos_iff P hO.measurableSet y).2
    ((potKernel_pos_iff P hO.measurableSet y).1 (hx O hO hxO y))

omit [T2Space X] in
/-- **Lemma 18.4.1** (MT p. 474): for a weak Feller chain with a reachable state `x*` and an open
neighbourhood `O` of `x*` with compact closure, `{Φ → ∞} = {Φ ∈ O i.o.}ᶜ`, `P_μ`-a.s. for every
initial law. -/
theorem lemma_18_4_1 {P : Kernel X X} [IsMarkovKernel P] (hF : IsWeakFeller P) {x₀ : X}
    (hx : IsReachable P x₀) {O : Set X} (hO : IsOpen O) (hxO : x₀ ∈ O)
    (hOc : IsCompact (closure O)) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂pathMeasure P μ, ω ∈ tendsToInfty ↔ ω ∉ ioSet O := by
  set Kx := CompactExhaustion.choice X
  have hstep : ∀ n, ∀ᵐ ω ∂pathMeasure P μ, ω ∈ ioSet (Kx n) → ω ∈ ioSet O := fun n => by
    rcases (Kx n).eq_empty_or_nonempty with h | hne
    · refine Eventually.of_forall fun ω hω => ?_
      rw [h] at hω
      obtain ⟨k, -, hk⟩ := hω 0
      exact absurd hk (notMem_empty _)
    obtain ⟨z, hz, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne (Kx.isCompact n)
      ((proposition_6_1_1_iii hF hO).2.2.lowerSemicontinuousOn _)
    rw [isMinOn_iff] at hmin
    exact theorem_9_1_3_ae P μ hO.measurableSet (hx.hitProb_pos hO hxO z) fun y hy =>
      (hmin y hy).trans (hitProb_le_hitProbZero P O y)
  filter_upwards [ae_all_iff.2 hstep] with ω hω
  constructor
  · intro hinf hio
    exact hinf (closure O) hOc (ioSet_mono subset_closure hio)
  · intro hnio
    rw [tendsToInfty_eq_iInter Kx]
    exact mem_iInter.2 fun n h => hnio (hω n h)

/-! ### Harmonic functions and the limit kernel -/

omit [T2Space X] in
/-- **Bounded continuous harmonic functions are constant** for a non-evanescent weak Feller chain
with a reachable state (the martingale argument of Proposition 18.4.2, MT p. 474): `g(Φₖ)` is a
bounded martingale, it converges almost surely, and since `Φ` visits every neighbourhood of `x*`
infinitely often (Lemma 18.4.1) the limit is `g(x*)`; taking expectations, `g(y) = g(x*)`. -/
theorem harmonic_eq_of_isReachable {P : Kernel X X} [IsMarkovKernel P] (hF : IsWeakFeller P)
    (hNE : IsNonEvanescent P) {x₀ : X} (hx : IsReachable P x₀) {g : X → NNReal}
    (hgm : Measurable g) (hgc : Continuous fun x => (g x : ℝ))
    (hharm : ∀ x, ∫⁻ y, (g y : ℝ≥0∞) ∂P x = g x) {B : NNReal} (hB : ∀ x, g x ≤ B) (y : X) :
    g y = g x₀ := by
  have := isMarkovKernel_pathKernel P
  have hfin : ∫⁻ z, (g z : ℝ≥0∞) ∂Measure.dirac y ≠ ∞ := by
    rw [lintegral_dirac' _ hgm.coe_nnreal_ennreal]
    exact ENNReal.coe_ne_top
  have hconv := ae_tendsto_killedV P (Measure.dirac y) hgm MeasurableSet.empty
    (fun z _ => (hharm z).le) hfin
  rw [pathMeasure_dirac] at hconv
  -- neighbourhoods of `x*` on which `g` is close to `g(x*)`
  have hnbhd : ∀ m : ℕ, ∃ O : Set X, IsOpen O ∧ x₀ ∈ O ∧ IsCompact (closure O) ∧
      ∀ z ∈ O, |(g z : ℝ) - g x₀| < 1 / (m + 1) := fun m => by
    obtain ⟨U, hU, hxU, hUc⟩ := exists_isOpen_mem_isCompact_closure x₀
    set V := {z | |(g z : ℝ) - g x₀| < 1 / (m + 1)}
    have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
    have hxV : x₀ ∈ V := show |(g x₀ : ℝ) - g x₀| < 1 / (m + 1) by
      rw [sub_self, abs_zero]; positivity
    refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
      hUc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left),
      fun z hz => hz.2⟩
  choose O hO hxO hOc hOg using hnbhd
  have hio : ∀ m, ∀ᵐ ω ∂pathKernel P y, ω ∈ ioSet (O m) := fun m => by
    have h := lemma_18_4_1 hF hx (hO m) (hxO m) (hOc m) (Measure.dirac y)
    rw [pathMeasure_dirac] at h
    have hne : ∀ᵐ ω ∂pathKernel P y, ω ∉ tendsToInfty := by
      rw [ae_iff]; simpa using hNE y
    filter_upwards [h, hne] with ω h1 h2
    by_contra h3
    exact h2 (h1.2 h3)
  have hlim : ∀ᵐ ω ∂pathKernel P y, Tendsto (fun k => (g (ω k) : ℝ)) atTop (𝓝 (g x₀)) := by
    filter_upwards [hconv, ae_all_iff.2 hio] with ω ⟨c, hc⟩ hω
    have hk : ∀ k, killedV g ∅ k ω = (g (ω k) : ℝ) := fun k => by
      simp [killedV, avoidSet]
    simp_rw [hk] at hc
    have hceq : c = g x₀ := by
      refine eq_of_abs_sub_le_all fun ε hε => ?_
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      by_contra hgt
      push Not at hgt
      have h1 : ∀ᶠ k in atTop, |(g (ω k) : ℝ) - c| < ε - 1 / (m + 1) :=
        (Metric.tendsto_nhds.1 hc) _ (by linarith)
      obtain ⟨N, hN⟩ := eventually_atTop.1 h1
      obtain ⟨k, hkN, hkO⟩ := hω m N
      have h2 := hN k hkN
      have h3 := hOg m (ω k) hkO
      have h4 := abs_sub_le c (g (ω k) : ℝ) (g x₀)
      have h5 : |c - (g (ω k) : ℝ)| = |(g (ω k) : ℝ) - c| := abs_sub_comm _ _
      linarith
    rw [← hceq]; exact hc
  -- expectations
  have hpow : ∀ k z, ∫⁻ w, (g w : ℝ≥0∞) ∂(P ^ k : Kernel X X) z = g z := fun k => by
    induction k with
    | zero => intro z; rw [pow_zero_apply, lintegral_dirac' _ hgm.coe_nnreal_ennreal]
    | succ k ih =>
      intro z
      rw [pow_succ]
      change ∫⁻ w, (g w : ℝ≥0∞) ∂((P ^ k : Kernel X X) ∘ₖ P) z = _
      rw [Kernel.lintegral_comp _ _ _ hgm.coe_nnreal_ennreal]
      simp_rw [ih]
      exact hharm z
  have hexp : ∀ k, ∫⁻ ω, (g (ω k) : ℝ≥0∞) ∂pathKernel P y = g y := fun k => by
    rw [← lintegral_map hgm.coe_nnreal_ennreal (measurable_pi_apply k), pathKernel_map_coord,
      hpow k y]
  have hdom := tendsto_lintegral_of_dominated_convergence (μ := pathKernel P y)
    (fun _ => (B : ℝ≥0∞))
    (F := fun k ω => (g (ω k) : ℝ≥0∞)) (f := fun _ => (g x₀ : ℝ≥0∞))
    (fun k => hgm.coe_nnreal_ennreal.comp (measurable_pi_apply k))
    (fun k => Eventually.of_forall fun ω => ENNReal.coe_le_coe.2 (hB _))
    (by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.coe_ne_top)
    (by
      filter_upwards [hlim] with ω hω
      have := ENNReal.tendsto_ofReal hω
      simp only [ENNReal.ofReal_coe_nnreal] at this
      exact this)
  simp_rw [hexp, lintegral_const, measure_univ, mul_one] at hdom
  exact_mod_cast tendsto_nhds_unique tendsto_const_nhds hdom

/-- **The limit kernel does not depend on the starting point** (the first step of the proof of
Proposition 18.4.2, MT pp. 474–475): for a non-evanescent e-chain with a reachable state `x*`,
`Π(y, ·) = Π(x*, ·)` for every `y`, since `y ↦ Π(y, f)` is a bounded continuous harmonic function
for `f ∈ C_c(X)` (`PΠ = Π`). -/
theorem eChainLimit_eq_of_isReachable {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (hNE : IsNonEvanescent P) {x₀ : X} (hx : IsReachable P x₀) (y : X) :
    eChainLimit he y = eChainLimit he x₀ := by
  have hfinK := isFiniteKernel_eChainLimit he
  have hF := he.isWeakFeller
  refine ext_of_integral_cc (integral_cc_eq_of_nonneg fun f hf0 => ?_)
  set G : X → ℝ≥0∞ := fun x => ∫⁻ z, ENNReal.ofReal (f z) ∂eChainLimit he x with hG
  have hfm : Measurable fun z => ENNReal.ofReal (f z) :=
    (map_continuous f).measurable.ennreal_ofReal
  obtain ⟨B, hB0, hB⟩ := exists_abs_le_cc f
  have hGB : ∀ x, G x ≤ ENNReal.ofReal B := fun x => by
    calc G x ≤ ∫⁻ _, ENNReal.ofReal B ∂eChainLimit he x :=
          lintegral_mono fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hB z))
      _ = ENNReal.ofReal B * eChainLimit he x univ := lintegral_const _
      _ ≤ ENNReal.ofReal B * 1 := by gcongr; exact (theorem_12_4_1_i he).1 x
      _ = ENNReal.ofReal B := mul_one _
  have hGfin : ∀ x, G x ≠ ∞ := fun x => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hGB x)
  have hGint : ∀ x, (G x).toReal = ∫ z, f z ∂eChainLimit he x := fun x => by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0)
      (map_continuous f).aestronglyMeasurable]
  set g : X → NNReal := fun x => (G x).toNNReal with hgdef
  have hgG : ∀ x, (g x : ℝ≥0∞) = G x := fun x => ENNReal.coe_toNNReal (hGfin x)
  have hGm : Measurable G := hfm.lintegral_kernel
  have hgm : Measurable g := hGm.ennreal_toNNReal
  have hgc : Continuous fun x => (g x : ℝ) := by
    have h := continuous_integral_limMeasure he (cesaroConverges_eChainSubseq he) f
    refine h.congr fun x => ?_
    change _ = ((G x).toNNReal : ℝ)
    rw [ENNReal.coe_toNNReal_eq_toReal, hGint]
    rfl
  have hharm : ∀ x, ∫⁻ z, (g z : ℝ≥0∞) ∂P x = g x := fun x => by
    simp_rw [hgG]
    rw [hG]
    rw [← Kernel.lintegral_comp _ _ _ hfm, eChainLimit_comp_kernel he]
  have hbd : ∀ x, g x ≤ (ENNReal.ofReal B).toNNReal := fun x =>
    ENNReal.toNNReal_mono ENNReal.ofReal_ne_top (hGB x)
  have := harmonic_eq_of_isReachable hF hNE hx hgm hgc hharm hbd y
  rw [← hGint, ← hGint]
  have h2 := congrArg (fun r : NNReal => (r : ℝ)) this
  simp only [hgdef, ENNReal.coe_toNNReal_eq_toReal] at h2
  exact h2

/-! ### Proposition 18.4.2 -/

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- An invariant probability charges every open neighbourhood of a reachable state (a reachable
state lies in the support of every invariant probability, MT p. 475). -/
theorem IsReachable.measure_pos {P : Kernel X X} [IsMarkovKernel P] {x₀ : X}
    (hx : IsReachable P x₀) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {O : Set X} (hO : IsOpen O) (hxO : x₀ ∈ O) : 0 < π O := by
  have hK := hπ.resolvent (ε := 2⁻¹) (ENNReal.inv_lt_one.2 (by norm_num))
  have hpos : ∀ y, 0 < resolventHalf P y O := fun y => by
    obtain ⟨n, hn⟩ := (potKernel_pos_iff P hO.measurableSet y).1 (hx O hO hxO y)
    rw [resolventHalf_apply P y hO.measurableSet]
    refine lt_of_lt_of_le ?_ (ENNReal.le_tsum (n + 1))
    exact ENNReal.mul_pos hn.ne' (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have h1 : ∫⁻ y, resolventHalf P y O ∂π = 0 := by
    rw [← Measure.bind_apply hO.measurableSet (Kernel.aemeasurable _)]
    exact (congrArg (fun ρ : Measure X => ρ O) hK).trans h0
  rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hO.measurableSet)] at h1
  obtain ⟨y, hy⟩ := h1.exists
  exact (hpos y).ne' hy

/-- `x*` is **positive in the Cesàro sense**: `lim sup P̄ⁿ(x*, O) > 0` for every open
neighbourhood `O` of `x*`. -/
def IsCesaroPositive (P : Kernel X X) (x : X) : Prop :=
  ∀ O : Set X, IsOpen O → x ∈ O → 0 < limsup (fun n => cesaroKernel P n x O) atTop

/-- Cesàro positivity of `x*` gives `Π(x*, X) > 0`. -/
theorem IsCesaroPositive.eChainMass_pos {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    {x₀ : X} (hpos : IsCesaroPositive P x₀) : 0 < eChainMass he x₀ := by
  have hfinK := isFiniteKernel_eChainLimit he
  obtain ⟨O, hO, hxO, hOc⟩ := exists_isOpen_mem_isCompact_closure x₀
  obtain ⟨f, hf01, hfC⟩ := exists_cc_indicator_le hOc
  have hle : ∀ n, cesaroKernel P n x₀ O ≤ ENNReal.ofReal (cesaroFun P n f x₀) := fun n => by
    have := isFiniteKernel_cesaroKernel P n
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ O), ← measureReal_def]
    refine ENNReal.ofReal_le_ofReal (measureReal_le_integral_of_indicator_le hO.measurableSet
      ((map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport) fun y => ?_)
    by_cases hy : y ∈ O
    · rw [indicator_of_mem hy]
      have := hfC y
      rwa [indicator_of_mem (subset_closure hy)] at this
    · rw [indicator_of_notMem hy]; exact (hf01 y).1
  have hlim := ENNReal.tendsto_ofReal ((theorem_12_4_1_i he).2 f x₀)
  have h1 : limsup (fun n => cesaroKernel P n x₀ O) atTop ≤
      ENNReal.ofReal (∫ y, f y ∂eChainLimit he x₀) :=
    (limsup_le_limsup (Eventually.of_forall hle)).trans_eq hlim.limsup_eq
  exact (hpos O hO hxO).trans_le (h1.trans (ofReal_integral_le_univ (map_continuous f).measurable
    hf01))

/-- **Proposition 18.4.2** (MT p. 474), for a non-evanescent e-chain with a reachable state `x*`:
(i) there is a unique invariant probability `π` and `P̄ₖ(x, ·) → π` weakly for every `x`;
(ii) the chain is bounded in probability on average; (iii) `x*` is positive, in the Cesàro form
`IsCesaroPositive` used by the proof. The statement is `(i) ↔ (ii)` and `(ii) ↔ (iii)`. -/
theorem proposition_18_4_2 {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (hNE : IsNonEvanescent P) {x₀ : X} (hx : IsReachable P x₀) :
    ((∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π ∧
        (∀ μ : Measure X, IsProbabilityMeasure μ → IsInvariant P μ → μ = π) ∧
        ∀ x (f : X →ᵇ ℝ), Tendsto (fun n => ∫ y, f y ∂cesaroKernel P (n + 1) x) atTop
          (𝓝 (∫ y, f y ∂π))) ↔ IsBoundedInProbabilityOnAverage P) ∧
      (IsBoundedInProbabilityOnAverage P ↔ IsCesaroPositive P x₀) := by
  have hfinK := isFiniteKernel_eChainLimit he
  have hconst := eChainLimit_eq_of_isReachable he hNE hx
  set π := eChainLimit he x₀ with hπdef
  -- bounded on average gives (i)
  have hBA : IsBoundedInProbabilityOnAverage P → ∃ π : Measure X, IsProbabilityMeasure π ∧
      IsInvariant P π ∧ (∀ μ : Measure X, IsProbabilityMeasure μ → IsInvariant P μ → μ = π) ∧
      ∀ x (f : X →ᵇ ℝ), Tendsto (fun n => ∫ y, f y ∂cesaroKernel P (n + 1) x) atTop
        (𝓝 (∫ y, f y ∂π)) := fun hb => by
    obtain ⟨hM, -, hinv, hconv⟩ := theorem_12_0_1_ii he hb
    refine ⟨π, inferInstance, hinv x₀, fun μ _ hμ => ?_, fun x f => ?_⟩
    · rw [← eChainLimit_comp_measure he hμ]
      ext A hA
      rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
      simp_rw [hconst]
      rw [lintegral_const, measure_univ, mul_one]
    · have h := hconv f x
      rwa [hconst x] at h
  refine ⟨⟨fun hA => ?_, hBA⟩, ⟨fun hb O hO hxO => ?_, fun hpos => ?_⟩⟩
  · -- (i) ⇒ (ii)
    obtain ⟨π', hπ', -, -, hconv⟩ := hA
    refine (theorem_12_4_1_iii he).2 fun x => ?_
    have hfin : IsFiniteMeasure (eChainLimit he x) := inferInstance
    have heq : eChainLimit he x = π' := ext_of_integral_cc fun f => by
      have h1 := ((theorem_12_4_1_i he).2 f x).comp (tendsto_add_atTop_nat 1)
      have h2 := hconv x f.toBoundedContinuousFunction
      simp only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] at h2
      exact tendsto_nhds_unique h1 h2
    rw [heq, measure_univ]
  · -- (ii) ⇒ (iii)
    have h1 := (theorem_12_4_1_iii he).1 hb
    have hπp : IsProbabilityMeasure π := ⟨h1 x₀⟩
    have hπO := hx.measure_pos ((theorem_12_4_1_ii he).2 x₀).1 hO hxO
    exact (hπO.trans_le (eChainLimit_open_le he hO x₀)).trans_le
      (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault))
  · -- (iii) ⇒ (ii)
    refine (theorem_12_4_1_iii he).2 fun y => ?_
    have hm := hpos.eChainMass_pos he
    have : Nonempty X := ⟨x₀⟩
    obtain ⟨z, -, hz⟩ := theorem_12_4_3_i (P := P) he
    have hzeq : eChainMass he z = eChainMass he x₀ := by
      simp only [eChainMass]; rw [hconst z]
    rw [hzeq] at hz
    have hy : eChainMass he y = eChainMass he x₀ := by
      simp only [eChainMass]; rw [hconst y]
    change eChainMass he y = 1
    rw [hy]
    exact hz.resolve_left hm.ne'

omit [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
/-- The Cesàro means of a `[0, 1]`-sequence that is eventually at most `q` have `limsup ≤ q`. -/
theorem limsup_cesaro_le (a : ℕ → ℝ≥0∞) (ha : ∀ i, a i ≤ 1) {N : ℕ} {q : ℝ≥0∞}
    (hq : ∀ i, N ≤ i → a i ≤ q) :
    atTop.limsup (fun n : ℕ => (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 n, a i) ≤ q := by
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have ht : Tendsto (fun n : ℕ => (N : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top N)) (a := (N : ℝ≥0∞))
    rwa [mul_zero] at this
  have hev : ∀ᶠ n : ℕ in atTop, (N : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ ≤ η :=
    ht.eventually (Iic_mem_nhds (by exact_mod_cast hη))
  have hb : ∀ n : ℕ, (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 n, a i ≤ q + N * (n : ℝ≥0∞)⁻¹ := by
    intro n
    calc (n : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.Icc 1 n, a i
        ≤ (n : ℝ≥0∞)⁻¹ * (n * q + (min n N : ℕ)) := by
          gcongr; exact sum_Icc_le_of_eventually_le a ha hq n
      _ ≤ q + N * (n : ℝ≥0∞)⁻¹ := by
          rw [mul_add, ← mul_assoc, mul_comm _ ((min n N : ℕ) : ℝ≥0∞)]
          gcongr
          · exact mul_le_of_le_one_left' (ENNReal.inv_mul_le_one _)
          · exact_mod_cast min_le_right n N
  exact limsup_le_of_le (by isBoundedDefault)
    (hev.mono fun n hn => (hb n).trans (add_le_add_right hn q))

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
/-- Cesàro positivity implies positivity in the sense of MT p. 473: if `Pⁿ(x*, O) → 0` then also
`P̄ⁿ(x*, O) → 0`. In particular (i)–(iii) of Proposition 18.4.2 make `x*` positive. -/
theorem IsCesaroPositive.isTopPositive {P : Kernel X X} [IsMarkovKernel P] {x₀ : X}
    (h : IsCesaroPositive P x₀) : IsTopPositive P x₀ := by
  intro O hO hxO
  by_contra h0
  have hlim := tendsto_zero_iff_limsup_eq_zero.2 (nonpos_iff_eq_zero.1 (not_lt.1 h0))
  have hc := h O hO hxO
  have hle : limsup (fun n => cesaroKernel P n x₀ O) atTop ≤ 0 := by
    refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hlim) η
      (by exact_mod_cast hη))
    have := limsup_cesaro_le (fun i => (P ^ i : Kernel X X) x₀ O)
      (fun i => by have := isMarkovKernel_pow P i; exact prob_le_one) (N := N) (q := η) hN
    simp_rw [cesaroKernel_apply P _ x₀ hO.measurableSet]
    simpa using this
  exact absurd hc (not_lt.2 hle)

/-! ### Theorem 18.4.4 (i) -/

/-- **Theorem 18.4.4 (i)** (MT p. 476): an e-chain that is bounded in probability on average has a
unique invariant probability iff it has a reachable state. If a reachable state exists, the chain
is non-evanescent (Proposition 12.1.1) and Proposition 18.4.2 applies. Conversely, every
`Π(x, ·)` is an invariant probability, hence equal to the unique `π`, and a point of `supp π` is
reachable: `π(O) = Π(y, O) ≤ liminf P̄ⁿ(y, O)` by (D.6). -/
theorem theorem_18_4_4_i {P : Kernel X X} [IsMarkovKernel P] (he : IsEChain P)
    (hb : IsBoundedInProbabilityOnAverage P) :
    (∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π ∧
      ∀ μ : Measure X, IsProbabilityMeasure μ → IsInvariant P μ → μ = π) ↔
      ∃ x₀, IsReachable P x₀ := by
  have hfinK := isFiniteKernel_eChainLimit he
  constructor
  · rintro ⟨π, hπp, hπ, huniq⟩
    have h1 := (theorem_12_4_1_iii he).1 hb
    have hPi : ∀ y, eChainLimit he y = π := fun y => by
      have : IsProbabilityMeasure (eChainLimit he y) := ⟨h1 y⟩
      exact huniq _ this ((theorem_12_4_1_ii he).2 y).1
    obtain ⟨x₀, hx₀⟩ : π.support.Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty] at hemp
      have := Measure.measure_compl_support (μ := π)
      rw [hemp, compl_empty, measure_univ] at this
      exact one_ne_zero this
    refine ⟨x₀, fun O hO hxO y => ?_⟩
    have hπO : 0 < π O := (Measure.mem_support_iff_forall x₀).1 hx₀ O (hO.mem_nhds hxO)
    have hlim := eChainLimit_open_le he hO y
    rw [hPi y] at hlim
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf (hπO.trans_le hlim))
    have hpos := hN (N + 1) (Nat.le_succ N)
    rw [cesaroKernel_apply P _ y hO.measurableSet] at hpos
    obtain ⟨i, hi, hpi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (pos_iff_ne_zero.1
      (pos_of_mul_pos_right hpos zero_le))
    rw [Finset.mem_Icc] at hi
    rw [potKernel_pos_iff P hO.measurableSet y]
    refine ⟨i - 1, ?_⟩
    rw [Nat.sub_add_cancel hi.1]
    exact pos_iff_ne_zero.2 hpi
  · rintro ⟨x₀, hx⟩
    obtain ⟨π, hπp, hπ, huniq, -⟩ :=
      (proposition_18_4_2 he (proposition_12_1_1 hb) hx).1.2 hb
    exact ⟨π, hπp, hπ, huniq⟩

end MeynTweedie.Positivity

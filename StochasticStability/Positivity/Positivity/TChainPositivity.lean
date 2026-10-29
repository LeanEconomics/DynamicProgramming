/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.PositivityPn
import Positivity.BoundedInProbability
import Positivity.TopologicalRecurrence
import Positivity.FosterCriterion
import Positivity.AperiodicErgodic

/-!
# Positivity and T-chains (MT §18.3, Theorem 18.0.2 (i))

Meyn and Tweedie, pp. 463–464, 471–473. `X` is a locally compact, second-countable Hausdorff
space with its Borel σ-algebra.

**T-chains bounded in probability** (§18.3.1).
* `IsPositiveHarris.isBoundedInProbability`: a positive Harris chain is bounded in probability
  (no T-chain property is used): on each cycle class the `d`-step laws converge in total variation
  to `dπ(· ∩ Dᵢ)` ((18.24)–(18.25)), a single compact `K` with `π(Kᶜ)` small serves all classes,
  and Fatou's lemma takes care of the time spent outside the classes.
  `eventually_of_forall_mul_add` combines the residue classes.
* `IsBoundedInProbability.isPositiveHarris`: a bounded in probability T-chain is positive Harris.
* `exists_isMaximalIrreducibility_of_isReachable`: a reachable state makes a T-chain
  `ψ`-irreducible (Proposition 6.2.1).
* **Theorem 18.3.2** (`theorem_18_3_2`, p. 472).
* **Proposition 18.3.1** (`proposition_18_3_1`, p. 472), for the discrete topology on a countable
  space (`isTChain_of_discreteTopology`); `isPositiveHarris_iff_isPositive_of_countable`.

**Positive and null states** (§18.3.2).
* `IsTopNull`, `IsTopPositive` (p. 473); `exists_isOpen_isPetite_nhds`.
* **Proposition 18.3.3** (`proposition_18_3_3`, p. 473): for a T-chain with a reachable `x*`, the
  chain is positive iff `x*` is positive; `isTopNull_iff_isNull`: `x*` is null iff the chain is.
* **Theorem 18.0.2 (i)** (`theorem_18_0_2_i`, p. 463): positive Harris ⇔ bounded in probability
  ⇔ non-evanescent with `x*` positive, and (18.4) in the aperiodic case.

**Hypotheses.** The book takes "positive Harris" in Theorem 18.0.2 (i); its `x*` "positive" is
the topological notion of p. 473. The proof of Theorem 18.3.2 uses Theorem 18.2.2 (ii) for a
possibly periodic chain (`IsNull.tendsto_pow_of_isPetite`).
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- If every residue class `n ≡ r (mod d)` eventually satisfies `p`, so does `n`. -/
theorem eventually_of_forall_mul_add {p : ℕ → Prop} {d : ℕ} (hd : 0 < d)
    (h : ∀ r < d, ∀ᶠ n in atTop, p (d * n + r)) : ∀ᶠ n in atTop, p n := by
  have hN : ∀ r < d, ∃ N, ∀ n ≥ N, p (d * n + r) := fun r hr => eventually_atTop.1 (h r hr)
  choose! N hN using hN
  set N₀ := (Finset.range d).sup N with hN₀
  refine eventually_atTop.2 ⟨d * N₀, fun n hn => ?_⟩
  have hr : n % d < d := Nat.mod_lt n hd
  have hk : N (n % d) ≤ n / d := by
    have h1 : N (n % d) ≤ N₀ := Finset.le_sup (f := N) (Finset.mem_range.2 hr)
    have h2 : N₀ ≤ n / d := (Nat.le_div_iff_mul_le hd).2 (by rw [mul_comm]; exact hn)
    omega
  have := hN (n % d) hr (n / d) hk
  rwa [Nat.div_add_mod] at this

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X]

/-- **Positive Harris chains are bounded in probability** (the "only if" half of
Theorem 18.3.2, MT p. 472). For a compact `K` with `π(Kᶜ)` small, on each cycle class the
`d`-step laws converge in total variation to `πᵢ = dπ(· ∩ Dᵢ)` (Theorem 13.3.3 for the skeleton
on the class, as in (18.25)), and from outside the classes the chain enters them (Harris
recurrence); Fatou's lemma combines the two. No T-chain property is needed. -/
theorem IsPositiveHarris.isBoundedInProbability {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hph : IsPositiveHarris P ψ) : IsBoundedInProbability P := by
  intro x ε hε
  by_cases hε1 : 1 ≤ ε
  · exact ⟨∅, isCompact_empty, by rw [tsub_eq_zero_of_le hε1]; exact zero_le⟩
  push Not at hε1
  obtain ⟨π, hπp, hπ⟩ := hph.2.2
  have hrec := proposition_10_1_1 hph.2
  obtain ⟨d, hper⟩ := exists_isPeriod P hph.1.1
  obtain ⟨D, hD⟩ := hper.2.1
  have hd : 0 < d := hper.1
  have : NeZero d := ⟨hd.ne'⟩
  set e := ε.toReal with he
  have hεt : ε ≠ ∞ := ne_top_of_lt hε1
  have he0 : 0 < e := ENNReal.toReal_pos hε.ne' hεt
  have he1 : e < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hε1; simpa using this
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨K, hK, hKπ⟩ := exists_isCompact_measureReal_compl_lt (⟨π, hπp⟩ : ProbabilityMeasure X)
    (δ := e / (4 * d)) (by positivity)
  simp only [ProbabilityMeasure.coe_mk] at hKπ
  have hKm := hK.measurableSet
  refine ⟨K, hK, ?_⟩
  set U := ⋃ j, D j with hUdef
  have hU : MeasurableSet U := MeasurableSet.iUnion hD.measurableSet
  -- on the classes
  have hclass : ∀ z ∈ U, ∀ᶠ n in atTop, 1 - e / 2 ≤ ((P ^ n : Kernel X X) z K).toReal :=
    fun z hz => by
      obtain ⟨j, hj⟩ := mem_iUnion.1 hz
      refine eventually_of_forall_mul_add hd fun r _ => ?_
      have := isMarkovKernel_pow P r
      have hμ : (P ^ r : Kernel X X) z (D (j + r))ᶜ = 0 := hD.pow_compl_eq_zero r hj
      have hconv := hD.tendsto_tvNorm_pow_mul hd hper hph hπ (j + r) ((P ^ r : Kernel X X) z) hμ
      have hcI := hD.isProbabilityMeasure_cycleInv hd hrec hπ (j + r)
      have hπiK : 1 - e / 4 < (cycleInv π D (j + r)).real K := by
        have hc : (cycleInv π D (j + r)).real Kᶜ ≤ d * π.real Kᶜ := by
          rw [cycleInv, measureReal_def, measureReal_def, Measure.smul_apply,
            Measure.restrict_apply hKm.compl, smul_eq_mul, ENNReal.toReal_mul]
          rw [ENNReal.toReal_natCast]
          exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top π _)
            (measure_mono Set.inter_subset_left)) (Nat.cast_nonneg _)
        have h2 : (d : ℝ) * π.real Kᶜ < e / 4 := by
          have := mul_lt_mul_of_pos_left hKπ hdpos
          rwa [show (d : ℝ) * (e / (4 * d)) = e / 4 by field_simp] at this
        have h3 := probReal_compl_eq_one_sub (μ := cycleInv π D (j + r)) hKm
        linarith
      filter_upwards [hconv.eventually (gt_mem_nhds (show (0 : ℝ) < e / 4 by positivity))]
        with n hn
      have := isMarkovKernel_pow P (d * n + r)
      have heq : (P ^ (d * n) : Kernel X X) ∘ₘ (P ^ r : Kernel X X) z =
          (P ^ (d * n + r) : Kernel X X) z := by
        rw [← dirac_kernel (P ^ r : Kernel X X) z, Measure.comp_assoc, ← pow_add_eq,
          dirac_kernel, add_comm r]
      rw [heq] at hn
      have habs := abs_measureReal_sub_le_tvNorm ((P ^ (d * n + r) : Kernel X X) z)
        (cycleInv π D (j + r)) hKm
      rw [measureReal_def] at habs
      have := neg_abs_le ((((P ^ (d * n + r) : Kernel X X) z) K).toReal -
        (cycleInv π D (j + r)).real K)
      linarith
  -- from `x`, through the time spent outside the classes
  have hleave := hD.tendsto_compl_iUnion hd hph.1 (Measure.dirac x)
  obtain ⟨m, hm⟩ := (ENNReal.tendsto_nhds_zero.1 hleave (ENNReal.ofReal (e / 4))
    (ENNReal.ofReal_pos.2 (by positivity))).exists
  simp only [dirac_kernel] at hm
  have := isMarkovKernel_pow P (m + 1)
  have hliminf : ∀ z ∈ U, ENNReal.ofReal (1 - e / 2) ≤
      liminf (fun n => (P ^ n : Kernel X X) z K) atTop := fun z hz => by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hclass z hz] with n hn
    have := isMarkovKernel_pow P n
    rw [← ENNReal.ofReal_toReal (measure_ne_top ((P ^ n : Kernel X X) z) K)]
    exact ENNReal.ofReal_le_ofReal hn
  have hfatou : ENNReal.ofReal (1 - e / 2) * (P ^ (m + 1) : Kernel X X) x U ≤
      liminf (fun n => (P ^ (n + (m + 1)) : Kernel X X) x K) atTop := by
    calc ENNReal.ofReal (1 - e / 2) * (P ^ (m + 1) : Kernel X X) x U
        = ∫⁻ _ in U, ENNReal.ofReal (1 - e / 2) ∂(P ^ (m + 1) : Kernel X X) x := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ z in U, liminf (fun n => (P ^ n : Kernel X X) z K) atTop
            ∂(P ^ (m + 1) : Kernel X X) x := setLIntegral_mono'  hU fun z hz => hliminf z hz
      _ ≤ ∫⁻ z, liminf (fun n => (P ^ n : Kernel X X) z K) atTop
            ∂(P ^ (m + 1) : Kernel X X) x := setLIntegral_le_lintegral _ _
      _ ≤ liminf (fun n => ∫⁻ z, (P ^ n : Kernel X X) z K ∂(P ^ (m + 1) : Kernel X X) x)
            atTop := lintegral_liminf_le fun n => Kernel.measurable_coe _ hKm
      _ = liminf (fun n => (P ^ (n + (m + 1)) : Kernel X X) x K) atTop := by
          congr 1
          funext n
          rw [show n + (m + 1) = m + 1 + n by ring,
            Kernel.pow_add_apply_eq_lintegral P (m + 1) n x hKm]
  rw [liminf_nat_add (fun n => (P ^ n : Kernel X X) x K) (m + 1)] at hfatou
  refine le_trans ?_ hfatou
  have hUx : ENNReal.ofReal (1 - e / 4) ≤ (P ^ (m + 1) : Kernel X X) x U := by
    have h1 := prob_compl_eq_one_sub (μ := (P ^ (m + 1) : Kernel X X) x) hU
    have h2 : (P ^ (m + 1) : Kernel X X) x U = 1 - (P ^ (m + 1) : Kernel X X) x Uᶜ := by
      rw [h1, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
    rw [h2, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
    exact tsub_le_tsub_left hm _
  calc 1 - ε = ENNReal.ofReal (1 - e) := by
        rw [ENNReal.ofReal_sub _ he0.le, ENNReal.ofReal_one, he, ENNReal.ofReal_toReal hεt]
    _ ≤ ENNReal.ofReal ((1 - e / 2) * (1 - e / 4)) := ENNReal.ofReal_le_ofReal (by nlinarith)
    _ = ENNReal.ofReal (1 - e / 2) * ENNReal.ofReal (1 - e / 4) :=
        ENNReal.ofReal_mul (by linarith)
    _ ≤ _ := by gcongr

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X] in
/-- A T-chain with a reachable state is `ψ`-irreducible (Proposition 6.2.1). -/
theorem exists_isMaximalIrreducibility_of_isReachable {P : Kernel X X} [IsMarkovKernel P]
    (hT : IsTChain P) {x₀ : X} (hx : IsReachable P x₀) :
    ∃ ψ : Measure X, IsMaximalIrreducibility P ψ := by
  obtain ⟨a, T, -, hTc, hpos⟩ := hT
  refine ⟨maxIrrMeasure P (T x₀),
    isMaximalIrreducibility_maxIrrMeasure P (proposition_6_2_1 hTc hx) fun h => ?_⟩
  have := hpos x₀
  rw [h, Measure.coe_zero, Pi.zero_apply] at this
  exact lt_irrefl _ this

/-- **Bounded in probability T-chains are positive Harris** (the "if" half of Theorem 18.3.2,
MT p. 472): boundedness gives non-evanescence (Proposition 12.1.1), hence Harris recurrence
(Theorem 9.2.2); compact sets are petite (Theorem 6.2.5), and a compact set with
`liminf Pⁿ(x, C) > 0` is not null, so the chain is not null (Theorem 18.2.2 (ii)). -/
theorem IsBoundedInProbability.isPositiveHarris {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (hT : IsTChain P)
    (hb : IsBoundedInProbability P) : IsPositiveHarris P ψ := by
  have hNE := proposition_12_1_1 hb.onAverage
  have hH := (theorem_9_2_2_ii hψ hT).2 hNE
  refine ⟨hH, ?_⟩
  by_contra hnp
  have hnull := (isPositive_or_isNull hψ).resolve_left hnp
  obtain ⟨x⟩ : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hψ.1 (Measure.eq_zero_of_isEmpty ψ)
  obtain ⟨C, hC, hlim⟩ := hb x 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)
  have hCp := theorem_6_2_5_ii hψ.2.1 hψ.1 hT hC
  have h0 := hnull.tendsto_pow_of_isPetite hCp x
  rw [h0.liminf_eq] at hlim
  have : (0 : ℝ≥0∞) < 1 - 2⁻¹ := by
    rw [ENNReal.one_sub_inv_two]; exact ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  exact absurd hlim (not_le.2 this)

/-- **Theorem 18.3.2** (MT p. 472): a T-chain with a reachable state is positive Harris iff it is
bounded in probability (`ψ` is any maximal irreducibility measure, which exists by
`exists_isMaximalIrreducibility_of_isReachable`). -/
theorem theorem_18_3_2 {P : Kernel X X} [IsMarkovKernel P] (hT : IsTChain P) {x₀ : X}
    (hx : IsReachable P x₀) {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) :
    IsPositiveHarris P ψ ↔ IsBoundedInProbability P := by
  have := hx
  exact ⟨fun h => h.isBoundedInProbability, fun h => h.isPositiveHarris hψ hT⟩

/-! ### Positive and null states for T-chains (§18.3.2) -/

/-- A state `x*` is **(topologically) null** (MT p. 473) if `Pⁿ(x*, O) → 0` for some open
neighbourhood `O`. -/
def IsTopNull (P : Kernel X X) (x : X) : Prop :=
  ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ Tendsto (fun n => (P ^ n : Kernel X X) x O) atTop (𝓝 0)

/-- A state `x*` is **(topologically) positive** (MT p. 473) if `lim sup Pⁿ(x*, O) > 0` for every
open neighbourhood `O`. -/
def IsTopPositive (P : Kernel X X) (x : X) : Prop :=
  ∀ O : Set X, IsOpen O → x ∈ O → 0 < limsup (fun n => (P ^ n : Kernel X X) x O) atTop

/-- Every point of a T-chain with a reachable state has an open petite neighbourhood (an open
neighbourhood with compact closure, Theorem 6.2.5). -/
theorem exists_isOpen_isPetite_nhds {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hT : IsTChain P) (x : X) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ IsPetite P O := by
  obtain ⟨O, hO, hxO, hK⟩ := exists_isOpen_mem_isCompact_closure x
  exact ⟨O, hO, hxO, (theorem_6_2_5_ii hψ.2.1 hψ.1 hT hK).subset hO.measurableSet
    subset_closure⟩

/-- **Proposition 18.3.3** (MT p. 473): for a T-chain and a reachable state `x*`, the chain is
positive iff `x*` is positive. -/
theorem proposition_18_3_3 {P : Kernel X X} [IsMarkovKernel P] (hT : IsTChain P) {x₀ : X}
    (hx : IsReachable P x₀) {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) :
    IsPositive P ψ ↔ IsTopPositive P x₀ := by
  constructor
  · intro hpos O hO hxO
    have hsupp := (lemma_6_1_4 hψ x₀).1 hx
    have hψO : 0 < ψ O := (Measure.mem_support_iff_forall x₀).1 hsupp O (hO.mem_nhds hxO)
    exact hpos.isPositiveSet hO.measurableSet hψO x₀ hxO
  · intro htop
    by_contra hnp
    have hnull := (isPositive_or_isNull hψ).resolve_left hnp
    obtain ⟨O, hO, hxO, hOp⟩ := exists_isOpen_isPetite_nhds hψ hT x₀
    have h := htop O hO hxO
    rw [(tendsto_zero_iff_limsup_eq_zero.1 (hnull.tendsto_pow_of_isPetite hOp x₀))] at h
    exact lt_irrefl _ h

/-- For a T-chain and a reachable state, `x*` is null iff the chain is null; so `x*` is either
positive or null (MT p. 473). -/
theorem isTopNull_iff_isNull {P : Kernel X X} [IsMarkovKernel P] (hT : IsTChain P) {x₀ : X}
    (hx : IsReachable P x₀) {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) :
    IsTopNull P x₀ ↔ IsNull P ψ := by
  constructor
  · rintro ⟨O, hO, hxO, h0⟩
    refine (isPositive_or_isNull hψ).resolve_left fun hpos => ?_
    have h := (proposition_18_3_3 hT hx hψ).1 hpos O hO hxO
    rw [tendsto_zero_iff_limsup_eq_zero.1 h0] at h
    exact lt_irrefl _ h
  · intro hnull
    obtain ⟨O, hO, hxO, hOp⟩ := exists_isOpen_isPetite_nhds hψ hT x₀
    exact ⟨O, hO, hxO, hnull.tendsto_pow_of_isPetite hOp x₀⟩

/-- **Theorem 18.0.2 (i)** (MT p. 463): for a T-chain with a reachable state `x*`, the following
are equivalent: (a) the chain is positive Harris; (b) it is bounded in probability; (c) it is
non-evanescent and `x*` is positive. If they hold and the chain is aperiodic, (18.4)
`‖Pᵏ(x, ·) − π‖ → 0` for every `x`. -/
theorem theorem_18_0_2_i {P : Kernel X X} [IsMarkovKernel P] (hT : IsTChain P) {x₀ : X}
    (hx : IsReachable P x₀) {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) :
    (IsPositiveHarris P ψ ↔ IsBoundedInProbability P) ∧
      (IsPositiveHarris P ψ ↔ IsNonEvanescent P ∧ IsTopPositive P x₀) ∧
      (IsPositiveHarris P ψ → IsAperiodic P ψ → ∀ {π : Measure X} [IsProbabilityMeasure π],
        IsInvariant P π → ∀ x, Tendsto (fun k => tvNorm ((P ^ k : Kernel X X) x) π) atTop
          (𝓝 0)) := by
  refine ⟨theorem_18_3_2 hT hx hψ, ⟨fun h => ⟨(theorem_9_2_2_ii hψ hT).1 h.1,
    (proposition_18_3_3 hT hx hψ).1 h.2⟩, fun ⟨hNE, hpos⟩ => ⟨(theorem_9_2_2_ii hψ hT).2 hNE,
    (proposition_18_3_3 hT hx hψ).2 hpos⟩⟩, fun h hap π _ hπ x => theorem_13_3_3_dirac h hap hπ x⟩

/-! ### Countable spaces (Proposition 18.3.1) -/

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X] in
/-- With the discrete topology every chain is a T-chain: `P` is its own continuous component
("where the continuous component properties are always satisfied", MT p. 472). -/
theorem isTChain_of_discreteTopology [DiscreteTopology X] (P : Kernel X X) [IsMarkovKernel P] :
    IsTChain P := by
  refine ⟨diracDist 1, P, isSamplingDist_diracDist 1, ⟨fun x => prob_le_one, fun x => ?_,
    fun A _ => continuous_of_discreteTopology.lowerSemicontinuous⟩, fun x => by simp⟩
  rw [sampledKernel_diracDist, pow_one]

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- **Proposition 18.3.1** (MT p. 472): for an irreducible chain on a countable space (discrete
topology), positive Harris recurrence is equivalent to boundedness in probability. -/
theorem proposition_18_3_1 [DiscreteTopology X] [Countable X] [Nonempty X] {P : Kernel X X}
    [IsMarkovKernel P] (hirr : IsIrreducibleChain P) :
    IsPositiveHarris P Measure.count ↔ IsBoundedInProbability P := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hx : IsReachable P x₀ := (isOpenSetIrreducible_iff_irreducible P).2 hirr x₀
  exact theorem_18_3_2 (isTChain_of_discreteTopology P) hx (isMaximalIrreducibility_count P hirr)

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] in
/-- On a countable space an irreducible positive chain is positive Harris
(`isHarris_of_countable`), so Proposition 18.3.1 also reads "positive iff bounded in
probability". -/
theorem isPositiveHarris_iff_isPositive_of_countable [Countable X] [MeasurableSingletonClass X]
    [Nonempty X] {P : Kernel X X} [IsMarkovKernel P] (hirr : IsIrreducibleChain P) :
    IsPositiveHarris P Measure.count ↔ IsPositive P Measure.count :=
  ⟨fun h => h.2, fun h => ⟨isHarris_of_countable hirr (proposition_10_1_1 h), h⟩⟩

end MeynTweedie.Positivity

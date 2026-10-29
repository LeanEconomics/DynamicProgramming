/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.HarrisLLN
import LimitTheorems.UniqueInvariant

/-!
# The ratio limit theorem for general Harris chains (MT Theorem 17.3.2)

Meyn and Tweedie, Theorem 17.3.2, p. 436, without any minorization: for a Harris chain with a
σ-finite invariant measure `π` (finite or not), `Sₙ(f)/Sₙ(g) → π(f)/π(g)` almost surely from
every initial state.

The book proves (i) ⇔ (ii) through the Chacon–Ornstein theorem and (iii) ⇒ (i) through the
split `m`-skeleton (17.21). Neither is needed: the maximal ergodic lemma of `BirkhoffErgodic`
holds for the shift on the stationary path measure `P_π = ∫ P_x π(dx)` even when `π` is
infinite, and combined with the zero–one law of a Harris chain (Theorem 17.1.5,
Proposition 17.1.6) it gives the ratio limit directly (Hopf's argument).

**Tools.**
* `pathKernel_shift_one_preimage`: `P_x(θ⁻¹B) = ∫ P(x, dy) P_y(B)`;
  `measurePreserving_shift_one_of_isInvariant`: for any invariant measure `π` the shift preserves
  `P_π`; `pathMeasure_map_coord_one`, `integrable_coord_one`, `integral_coord_one`: under `P_π`
  the law of `Φ₁` is `π`.
* `harris_dichotomy`: for a Harris chain, a strictly invariant event is null for every `P_x` or
  has probability one for every `P_x`.
* `ae_bddAbove_pathSum_of_integral_neg`: for a Harris chain with an invariant `π` and
  `g ∈ L¹(π)` with `π(g) < 0`, `Sₙ(g)` is bounded above, `P_x`-a.s. for every `x`.
* `ae_tendsto_pathSum_atTop`: `Sₙ(h) → ∞` a.s. for `h ≥ 0` with `π(h) > 0` (Theorem 10.4.9 and
  Theorem 9.1.4); `tendsto_div_of_bddAbove_sub`: the deterministic ratio criterion;
  `ratio_lln_of_harris_nonneg`: the ratio limit for a nonnegative denominator.
* `HasRatioLimit P π`: statement (i); `hitProb_eq_one_of_hasRatioLimit`: under (i),
  `L(x, A) = 1` whenever `0 < π(A) < ∞`; `IsHarris.of_isMaximalIrreducibility`.

**Results.**
* **Theorem 17.3.2** (iii) ⇒ (i) (`theorem_17_3_2_harris`, `theorem_17_3_2_harris_measure`):
  for every Harris chain and every nonzero σ-finite invariant `π`, `Sₙ(f)/Sₙ(g) → π(f)/π(g)`
  almost surely from every initial law, for `f, g ∈ L¹(π)` with `π(g) ≠ 0`. This removes the
  minorization hypothesis of `theorem_17_3_2` in `SplitLimitTheorems`.
* (i) ⇒ (iii) (`theorem_17_3_2_i_iii`), and `theorem_17_3_2_i_iff_iii`: for a chain with a
  nonzero σ-finite invariant measure, (i) holds iff the chain is Harris (no irreducibility is
  assumed: (i) itself makes `π` an irreducibility measure).
* (iii) ⇒ (ii) (`theorem_17_3_2_iii_ii`) and, for a recurrent chain, (ii) ⇒ (iii)
  (`theorem_17_3_2_ii_iii`), through the maximal Harris set of Theorem 9.1.5.
* `theorem_17_3_2_tfae`: (i) ⇔ (ii) ⇔ (iii) for a recurrent chain.

**Corrections.**
* (i) asks `∫ g dπ ≠ 0` (p. 436), as used here.
* (ii) ⇒ (iii) is false as stated: `theorem_17_3_2_counterexample` is the identity chain on
  `Bool` with `π = δ_true`, whose invariant σ-field is `P_x`-trivial for every `x` while (i) and
  (iii) fail. Triviality of the invariant σ-field says nothing about irreducibility or recurrence;
  the corrected statement assumes the chain recurrent (`theorem_17_3_2_tfae`). Irreducibility
  alone is not enough either: `theorem_17_3_2_counterexample_irreducible` (in
  `GapsTransientWalk`) is a transient `ψ`-irreducible walk on `ℤ` with (ii) but not (iii). The
  proof of (i) ⇔ (iii) does not need this hypothesis.

**Hypotheses.** A countably generated σ-algebra on `X`, for Theorems 9.1.4, 9.1.5, 10.4.9 and
17.1.5, as in the book.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The path measure of a σ-finite invariant measure -/

/-- One step of the Markov property for events: `P_x(θ⁻¹B) = ∫ P(x, dy) P_y(B)`. -/
theorem pathKernel_shift_one_preimage (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {B : Set (ℕ → X)} (hB : MeasurableSet B) :
    pathKernel P x (shift 1 ⁻¹' B) = ∫⁻ y, pathKernel P y B ∂P x := by
  have hi : Measurable (B.indicator (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hB
  have h := markov_lintegral_univ P (Measure.dirac x) 1 hi
  rw [pathMeasure_dirac] at h
  simp_rw [lintegral_indicator_one hB] at h
  have hpre : MeasurableSet (shift 1 ⁻¹' B) := measurable_shift 1 hB
  have e1 : ∫⁻ ω, B.indicator 1 (shift 1 ω) ∂pathKernel P x =
      pathKernel P x (shift 1 ⁻¹' B) := by
    change ∫⁻ ω, (shift 1 ⁻¹' B).indicator 1 ω ∂pathKernel P x = _
    rw [lintegral_indicator_one hpre]
  rw [← e1, h, ← lintegral_map (Kernel.measurable_coe _ hB) (measurable_pi_apply 1),
    pathKernel_map_coord, pow_one]

/-- For an invariant measure `π` (not necessarily finite), the shift `θ¹` preserves
`P_π = ∫ P_x π(dx)` (MT p. 231, for σ-finite `π`). -/
theorem measurePreserving_shift_one_of_isInvariant {P : Kernel X X} [IsMarkovKernel P]
    {π : Measure X} (hπ : IsInvariant P π) :
    MeasurePreserving (shift 1) (pathMeasure P π) (pathMeasure P π) := by
  have := isMarkovKernel_pathKernel P
  refine ⟨measurable_shift 1, Measure.ext fun B hB => ?_⟩
  rw [Measure.map_apply (measurable_shift 1) hB, pathMeasure_eq_comp,
    Measure.bind_apply (measurable_shift 1 hB) (Kernel.aemeasurable _),
    Measure.bind_apply hB (Kernel.aemeasurable _)]
  simp_rw [pathKernel_shift_one_preimage P _ hB]
  have hb := Measure.lintegral_bind (m := π) (μ := ⇑P) (f := fun y => pathKernel P y B)
    (Kernel.aemeasurable P) (Kernel.measurable_coe _ hB).aemeasurable
  rw [← hb]
  change ∫⁻ y, pathKernel P y B ∂(P ∘ₘ π) = _
  rw [hπ]

/-- For an invariant measure `π`, the law of `Φ₁` under `P_π` is `π`. -/
theorem pathMeasure_map_coord_one {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    (hπ : IsInvariant P π) : (pathMeasure P π).map (fun ω => ω 1) = π := by
  have e : (fun ω : ℕ → X => ω 1) = (fun ω => ω 0) ∘ shift 1 := rfl
  rw [e, ← Measure.map_map (measurable_pi_apply 0) (measurable_shift 1),
    (measurePreserving_shift_one_of_isInvariant hπ).map_eq, pathMeasure_map_zero]

/-- `ω ↦ g(ω₁)` is `P_π`-integrable for `g ∈ L¹(π)`, `π` invariant. -/
theorem integrable_coord_one {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    (hπ : IsInvariant P π) {g : X → ℝ} (hgm : Measurable g) (hgi : Integrable g π) :
    Integrable (fun ω : ℕ → X => g (ω 1)) (pathMeasure P π) := by
  have hm : Measurable fun ω : ℕ → X => ω 1 := measurable_pi_apply 1
  rw [← pathMeasure_map_coord_one hπ] at hgi
  exact (integrable_map_measure hgm.aestronglyMeasurable hm.aemeasurable).1 hgi

/-- `∫ g(ω₁) dP_π = ∫ g dπ` for invariant `π`. -/
theorem integral_coord_one {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    (hπ : IsInvariant P π) {g : X → ℝ} (hgm : Measurable g) :
    ∫ ω, g (ω 1) ∂pathMeasure P π = ∫ y, g y ∂π := by
  have hm : Measurable fun ω : ℕ → X => ω 1 := measurable_pi_apply 1
  rw [← integral_map hm.aemeasurable hgm.aestronglyMeasurable, pathMeasure_map_coord_one hπ]

/-! ### The zero–one law of a Harris chain -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- For a Harris chain, a strictly invariant event has `P_x`-probability `0` for every `x` or `1`
for every `x` (Theorem 17.1.5 and Proposition 17.1.6). -/
theorem harris_dichotomy {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {E : Set (ℕ → X)} (hEm : MeasurableSet E) (hE : shift 1 ⁻¹' E = E) :
    (∀ x, pathKernel P x E = 0) ∨ ∀ x, pathKernel P x E = 1 := by
  by_cases h : ∀ x, pathKernel P x E = 0
  · exact Or.inl h
  · push Not at h
    obtain ⟨x₀, hx₀⟩ := h
    have h1 : pathMeasure P (Measure.dirac x₀) E = 1 := by
      rcases ergodic_pathMeasure hH (Measure.dirac x₀) E hEm hE with h0 | h1
      · rw [pathMeasure_dirac] at h0; exact absurd h0 hx₀
      · exact h1
    exact Or.inr (proposition_17_1_6 hH hEm (isShiftInvariant_of_preimage hE) _ h1)

/-! ### Hopf's argument on the σ-finite stationary path measure -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The maximal ergodic lemma for a Harris chain with a σ-finite invariant measure.** If
`g ∈ L¹(π)` has `∫ g dπ < 0`, then the partial sums `Sₙ(g)` are bounded above, almost surely
from every initial state. The event that they are unbounded is strictly invariant, so by the
zero–one law it is null for every `P_x` or has probability one for every `P_x`; in the second
case it is `P_π`-conull, and the maximal ergodic lemma under the (possibly infinite) stationary
measure `P_π` gives `∫ g dπ ≥ 0`. -/
theorem ae_bddAbove_pathSum_of_integral_neg {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hH : IsHarris P ψ) {π : Measure X} (hπ : IsInvariant P π) {g : X → ℝ}
    (hgm : Measurable g) (hgi : Integrable g π) (hneg : ∫ y, g y ∂π < 0) (x : X) :
    ∀ᵐ ω ∂pathKernel P x, BddAbove (range fun n => pathSum g n ω) := by
  have := isMarkovKernel_pathKernel P
  have hT := measurePreserving_shift_one_of_isInvariant hπ
  set F : (ℕ → X) → ℝ := fun ω => g (ω 1) with hF
  have hFm : Measurable F := hgm.comp (measurable_pi_apply 1)
  have hFi : Integrable F (pathMeasure P π) := integrable_coord_one hπ hgm hgi
  have hUm : MeasurableSet (upSet (shift 1) F) := measurableSet_upSet hT.measurable hFm
  have hU : shift 1 ⁻¹' upSet (shift 1) F = upSet (shift 1) F := preimage_upSet _ F
  have key : ∀ y, pathKernel P y (upSet (shift 1) F) = 0 := by
    rcases harris_dichotomy hH hUm hU with h0 | h1
    · exact h0
    · exfalso
      have hc : pathMeasure P π (upSet (shift 1) F)ᶜ = 0 :=
        pathMeasure_eq_zero_of_forall P π hUm.compl fun y => (prob_compl_eq_zero_iff hUm).2 (h1 y)
      have hae : ∀ᵐ ω ∂pathMeasure P π, ω ∈ upSet (shift 1) F := by
        rw [ae_iff]; exact hc
      have hnn := integral_upSet_nonneg hT hFm hFi MeasurableSet.univ (preimage_univ)
      rw [univ_inter, Measure.restrict_eq_self_of_ae_mem hae, hF,
        integral_coord_one hπ hgm] at hnn
      linarith
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (key x)] with ω hω
  have e : (fun n => pathSum g n ω) = fun n => birkhoffSum (shift 1) F n ω :=
    funext fun n => pathSum_eq_birkhoffSum g n ω
  rw [e]
  exact not_not.1 hω

omit [MeasurableSpace X] in
/-- If `h ≥ 0` exceeds `ε > 0` infinitely often along the path, then `Sₙ(h) → ∞`. -/
theorem tendsto_pathSum_atTop_of_mem_ioSet {h : X → ℝ} (hh0 : ∀ y, 0 ≤ h y) {ε : ℝ}
    (hε : 0 < ε) {ω : ℕ → X} (hω : ω ∈ ioSet {y | ε < h y}) :
    Tendsto (fun n => pathSum h n ω) atTop atTop := by
  have hns : ¬ Summable (fun k => h (ω (k + 1))) := by
    intro hs
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.tendsto_atTop_zero.eventually (gt_mem_nhds hε))
    obtain ⟨k, hk, hkA⟩ := hω (N + 1)
    have h1 := hN (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at h1
    exact absurd hkA (not_lt.2 h1.le)
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun k => hh0 _)).1 hns

variable [MeasurableSpace.CountablyGenerated X] in
/-- For a Harris chain with a nonzero σ-finite invariant measure `π` and `h ≥ 0` with
`π(h) > 0`, `Sₙ(h) → ∞` almost surely from every initial state: `π ≪ ψ` (Theorem 10.4.9), so
`{h > ε} ∈ B⁺(X)` for some `ε > 0`, which is visited infinitely often (Theorem 9.1.4). -/
theorem ae_tendsto_pathSum_atTop {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0)
    {h : X → ℝ} (hhm : Measurable h) (hhi : Integrable h π) (hh0 : ∀ y, 0 ≤ h y)
    (hpos : 0 < ∫ y, h y ∂π) (x : X) :
    ∀ᵐ ω ∂pathKernel P x, Tendsto (fun n => pathSum h n ω) atTop atTop := by
  have := isMarkovKernel_pathKernel P
  have hsupp : 0 < π (Function.support h) :=
    (integral_pos_iff_support_of_nonneg (fun y => hh0 y) hhi).1 hpos
  have hun : Function.support h = ⋃ n : ℕ, {y | 1 / ((n : ℝ) + 1) < h y} := by
    ext y
    simp only [Function.mem_support, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro hy
      have hy' : 0 < h y := lt_of_le_of_ne (hh0 y) (Ne.symm hy)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hy'
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩
      exact (lt_trans (by positivity) hn).ne'
  rw [hun] at hsupp
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion hsupp
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hAm : MeasurableSet {y | ε < h y} := measurableSet_lt measurable_const hhm
  have hac := (theorem_10_4_9_equiv hH.isRecurrentChain hπ hπ0).1
  have hψA : 0 < ψ {y | ε < h y} := pos_iff_ne_zero.2 fun h0 => hn.ne' (hac h0)
  have hQ := theorem_9_1_4 hH hAm hψA x
  have hio := measurableSet_ioSet (X := X) hAm
  have hc : pathKernel P x (ioSet {y | ε < h y})ᶜ = 0 := (prob_compl_eq_zero_iff hio).2 hQ
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hc] with ω hω
  exact tendsto_pathSum_atTop_of_mem_ioSet hh0 hε0 (not_not.1 hω)

/-! ### The ratio limit -/

/-- A deterministic criterion for `tₙ/sₙ → r`: `sₙ → ∞`, `tₙ − a sₙ` is bounded above for every
rational `a > r` and `b sₙ − tₙ` is bounded above for every rational `b < r`. -/
theorem tendsto_div_of_bddAbove_sub {t s : ℕ → ℝ} (hs : Tendsto s atTop atTop) {r : ℝ}
    (hup : ∀ a : ℚ, r < a → BddAbove (range fun n => t n - a * s n))
    (hlo : ∀ b : ℚ, (b : ℝ) < r → BddAbove (range fun n => b * s n - t n)) :
    Tendsto (fun n => t n / s n) atTop (𝓝 r) := by
  rw [tendsto_order]
  refine ⟨fun b' hb' => ?_, fun a' ha' => ?_⟩
  · obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hb'
    obtain ⟨C, hC⟩ := hlo b hb2
    have hd : 0 < (b : ℝ) - b' := sub_pos.2 hb1
    filter_upwards [hs.eventually_gt_atTop ((|C| + 1) / ((b : ℝ) - b')),
      hs.eventually_gt_atTop 0] with n hn1 hn2
    have hCn : (b : ℝ) * s n - t n ≤ C := hC ⟨n, rfl⟩
    have h3 : |C| + 1 < s n * ((b : ℝ) - b') := (div_lt_iff₀ hd).1 hn1
    rw [lt_div_iff₀ hn2]
    have := le_abs_self C
    nlinarith
  · obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn ha'
    obtain ⟨C, hC⟩ := hup a ha1
    have hd : 0 < a' - (a : ℝ) := sub_pos.2 ha2
    filter_upwards [hs.eventually_gt_atTop ((|C| + 1) / (a' - (a : ℝ))),
      hs.eventually_gt_atTop 0] with n hn1 hn2
    have hCn : t n - (a : ℝ) * s n ≤ C := hC ⟨n, rfl⟩
    have h3 : |C| + 1 < s n * (a' - (a : ℝ)) := (div_lt_iff₀ hd).1 hn1
    rw [div_lt_iff₀ hn2]
    have := le_abs_self C
    nlinarith

omit [MeasurableSpace X] in
/-- `Sₙ(f − a h) = Sₙ(f) − a Sₙ(h)`. -/
theorem pathSum_sub_mul (f h : X → ℝ) (a : ℝ) (n : ℕ) (ω : ℕ → X) :
    pathSum (fun y => f y - a * h y) n ω = pathSum f n ω - a * pathSum h n ω := by
  unfold pathSum
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

omit [MeasurableSpace X] in
/-- `Sₙ(b h − f) = b Sₙ(h) − Sₙ(f)`. -/
theorem pathSum_mul_sub (f h : X → ℝ) (b : ℝ) (n : ℕ) (ω : ℕ → X) :
    pathSum (fun y => b * h y - f y) n ω = b * pathSum h n ω - pathSum f n ω := by
  unfold pathSum
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

variable [MeasurableSpace.CountablyGenerated X] in
/-- The ratio limit theorem with a nonnegative denominator: for a Harris chain with a nonzero
σ-finite invariant measure `π`, `f, h ∈ L¹(π)`, `h ≥ 0` and `π(h) > 0`,
`Sₙ(f)/Sₙ(h) → π(f)/π(h)` almost surely from every initial state. -/
theorem ratio_lln_of_harris_nonneg {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0)
    {f h : X → ℝ} (hfm : Measurable f) (hhm : Measurable h) (hfi : Integrable f π)
    (hhi : Integrable h π) (hh0 : ∀ y, 0 ≤ h y) (hpos : 0 < ∫ y, h y ∂π) (x : X) :
    ∀ᵐ ω ∂pathKernel P x, Tendsto (fun n => pathSum f n ω / pathSum h n ω) atTop
      (𝓝 ((∫ y, f y ∂π) / ∫ y, h y ∂π)) := by
  set r := (∫ y, f y ∂π) / ∫ y, h y ∂π with hr
  have hup : ∀ a : ℚ, ∀ᵐ ω ∂pathKernel P x,
      r < a → BddAbove (range fun n => pathSum f n ω - a * pathSum h n ω) := by
    intro a
    by_cases ha : r < a
    · have hint : ∫ y, (f y - a * h y) ∂π < 0 := by
        rw [integral_sub hfi (hhi.const_mul _), integral_const_mul]
        have := (div_lt_iff₀ hpos).1 ha
        linarith
      filter_upwards [ae_bddAbove_pathSum_of_integral_neg hH hπ.2
        (g := fun y => f y - (a : ℝ) * h y) (hfm.sub (measurable_const.mul hhm))
        (hfi.sub (hhi.const_mul _)) hint x] with ω hω _
      have e : (fun n => pathSum (fun y => f y - (a : ℝ) * h y) n ω) =
          fun n => pathSum f n ω - a * pathSum h n ω := funext fun n => pathSum_sub_mul f h a n ω
      rw [e] at hω
      exact hω
    · exact Eventually.of_forall fun ω h' => absurd h' ha
  have hlo : ∀ b : ℚ, ∀ᵐ ω ∂pathKernel P x,
      (b : ℝ) < r → BddAbove (range fun n => b * pathSum h n ω - pathSum f n ω) := by
    intro b
    by_cases hb : (b : ℝ) < r
    · have hint : ∫ y, ((b : ℝ) * h y - f y) ∂π < 0 := by
        rw [integral_sub (hhi.const_mul _) hfi, integral_const_mul]
        have := (lt_div_iff₀ hpos).1 hb
        linarith
      filter_upwards [ae_bddAbove_pathSum_of_integral_neg hH hπ.2
        (g := fun y => (b : ℝ) * h y - f y) ((measurable_const.mul hhm).sub hfm)
        ((hhi.const_mul _).sub hfi) hint x] with ω hω _
      have e : (fun n => pathSum (fun y => (b : ℝ) * h y - f y) n ω) =
          fun n => b * pathSum h n ω - pathSum f n ω := funext fun n => pathSum_mul_sub f h b n ω
      rw [e] at hω
      exact hω
    · exact Eventually.of_forall fun ω h' => absurd h' hb
  filter_upwards [ae_all_iff.2 hup, ae_all_iff.2 hlo,
    ae_tendsto_pathSum_atTop hH hπ hπ0 hhm hhi hh0 hpos x] with ω h1 h2 h3
  exact tendsto_div_of_bddAbove_sub h3 h1 h2

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 17.3.2** (iii) ⇒ (i) (MT p. 436) for every Harris chain: if `π` is a nonzero
σ-finite invariant measure (finite or not), then for `f, g ∈ L¹(π)` with `π(g) ≠ 0`,
`Sₙ(f)/Sₙ(g) → π(f)/π(g)` almost surely from every initial state. No minorization is assumed
(compare `theorem_17_3_2`, for a one-step minorization, and `theorem_17_3_2_positive`, for an
invariant probability); the proof is Hopf's maximal-lemma argument on `P_π`, which replaces the
book's split `m`-skeleton (17.21). -/
theorem theorem_17_3_2_harris {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0)
    {f g : X → ℝ} (hfm : Measurable f) (hgm : Measurable g) (hfi : Integrable f π)
    (hgi : Integrable g π) (hg : ∫ y, g y ∂π ≠ 0) (x : X) :
    ∀ᵐ ω ∂pathKernel P x, Tendsto (fun n => pathSum f n ω / pathSum g n ω) atTop
      (𝓝 ((∫ y, f y ∂π) / ∫ y, g y ∂π)) := by
  have hhm : Measurable fun y => |g y| := continuous_abs.measurable.comp hgm
  have hpos : 0 < ∫ y, |g y| ∂π := lt_of_lt_of_le (abs_pos.2 hg) abs_integral_le_integral_abs
  have hh0 : ∀ y, 0 ≤ |g y| := fun y => abs_nonneg _
  filter_upwards [ratio_lln_of_harris_nonneg hH hπ hπ0 hfm hhm hfi hgi.abs hh0 hpos x,
    ratio_lln_of_harris_nonneg hH hπ hπ0 hgm hhm hgi hgi.abs hh0 hpos x,
    ae_tendsto_pathSum_atTop hH hπ hπ0 hhm hgi.abs hh0 hpos x] with ω h1 h2 h3
  have h4 := h1.div h2 (div_ne_zero hg hpos.ne')
  rw [div_div_div_cancel_right₀ hpos.ne'] at h4
  refine h4.congr' ?_
  filter_upwards [h3.eventually_gt_atTop 0] with n hn
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hn.ne']

variable [MeasurableSpace.CountablyGenerated X] in
/-- `theorem_17_3_2_harris` for every initial distribution. -/
theorem theorem_17_3_2_harris_measure {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0)
    {f g : X → ℝ} (hfm : Measurable f) (hgm : Measurable g) (hfi : Integrable f π)
    (hgi : Integrable g π) (hg : ∫ y, g y ∂π ≠ 0) (μ : Measure X) :
    ∀ᵐ ω ∂pathMeasure P μ, Tendsto (fun n => pathSum f n ω / pathSum g n ω) atTop
      (𝓝 ((∫ y, f y ∂π) / ∫ y, g y ∂π)) :=
  ae_pathMeasure_of_forall P μ
    (measurableSet_tendsto_fun (fun n => (measurable_pathSum hfm n).div (measurable_pathSum hgm n))
      measurable_const)
    fun x => theorem_17_3_2_harris hH hπ hπ0 hfm hgm hfi hgi hg x

/-! ### The converse: the ratio limit forces Harris recurrence -/

/-- Statement (i) of Theorem 17.3.2 (MT p. 436, with `∫ g dπ ≠ 0`): `Sₙ(f)/Sₙ(g) → π(f)/π(g)`,
`P_x`-a.s. for every `x`, for all `f, g ∈ L¹(π)` with
`π(g) ≠ 0`. -/
def HasRatioLimit (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) : Prop :=
  ∀ f g : X → ℝ, Measurable f → Measurable g → Integrable f π → Integrable g π →
    ∫ y, g y ∂π ≠ 0 → ∀ x, ∀ᵐ ω ∂pathKernel P x,
      Tendsto (fun n => pathSum f n ω / pathSum g n ω) atTop (𝓝 ((∫ y, f y ∂π) / ∫ y, g y ∂π))

/-- Under the ratio limit property, every set `A` with `0 < π(A) < ∞` is reached from every
state: `L(x, A) = 1`. Take `f = g = 1_A`: the ratio `Sₙ(1_A)/Sₙ(1_A)` tends to `1`, so `Sₙ(1_A)`
is eventually nonzero. -/
theorem hitProb_eq_one_of_hasRatioLimit {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    (hR : HasRatioLimit P π) {A : Set X} (hA : MeasurableSet A) (h0 : 0 < π A)
    (hfin : π A < ∞) (x : X) : hitProb P A x = 1 := by
  have := isMarkovKernel_pathKernel P
  set f : X → ℝ := A.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hA
  have hfi : Integrable f π := (integrable_indicator_iff hA).2 (integrableOn_const hfin.ne)
  have hne : ∫ y, f y ∂π ≠ 0 := by
    rw [hf, integral_indicator_one hA, measureReal_def]
    exact (ENNReal.toReal_pos h0.ne' hfin.ne).ne'
  have h := hR f f hfm hfm hfi hfi hne x
  rw [div_self hne] at h
  have hT : MeasurableSet {ω : ℕ → X | firstReturn A ω ≠ ⊤} := measurableSet_firstReturn_ne_top hA
  unfold hitProb
  rw [← prob_compl_eq_zero_iff hT, measure_eq_zero_iff_ae_notMem]
  filter_upwards [h] with ω hω
  intro hc
  have hzero : ∀ n, pathSum f n ω = 0 := by
    intro n
    unfold pathSum
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : ω (k + 1) ∉ A := fun hk => hc ((firstReturn_ne_top_iff A ω).2 ⟨k + 1, by omega, hk⟩)
    rw [hf, indicator_of_notMem hk]
  have h0' : Tendsto (fun n => pathSum f n ω / pathSum f n ω) atTop (𝓝 0) := by
    simp only [hzero, div_zero]
    exact tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique hω h0')

/-- **Theorem 17.3.2** (i) ⇒ (iii) (MT p. 436): if a nonzero σ-finite invariant measure `π` has
the ratio limit property, the chain is Harris, with maximal irreducibility measure `ψ` given by
(4.10) from `π`. The book's argument: by the ratio limit, `L(x, A) = 1` for every `x` and every
`A` with `π(A) > 0`, so `π` is an irreducibility measure, `ψ ≪ π` (Proposition 10.1.2), and every
`A ∈ B⁺(X)` is Harris recurrent (Proposition 9.1.1). -/
theorem theorem_17_3_2_i_iii {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0) (hR : HasRatioLimit P π) :
    IsHarris P (maxIrrMeasure P π) := by
  have := hπ.1
  have hL : ∀ A, MeasurableSet A → 0 < π A → ∀ x, hitProb P A x = 1 := by
    intro A hA h0 x
    obtain ⟨B, hBm, hBA, hB0, hBfin⟩ := Measure.exists_subset_measure_lt_top hA h0
    exact le_antisymm (hitProb_le_one P A x)
      ((hitProb_eq_one_of_hasRatioLimit hR hBm hB0 hBfin x).symm.le.trans (hitProb_mono P hBA x))
  have hirr : IsPhiIrreducible P π := fun A hA h0 x => by rw [hL A hA h0 x]; exact one_pos
  have hψ := isMaximalIrreducibility_maxIrrMeasure P hirr hπ0
  have hac : maxIrrMeasure P π ≪ π := proposition_10_1_2_ii hψ.2.1 (le_of_eq hπ.2) hπ0
  refine ⟨hψ, fun A hA hψA => (proposition_9_1_1 P hA fun x _ => hL A hA ?_ x).2⟩
  exact pos_iff_ne_zero.2 fun h0 => hψA.ne' (hac h0)

/-- Harris recurrence does not depend on the choice of the maximal irreducibility measure. -/
theorem IsHarris.of_isMaximalIrreducibility {P : Kernel X X} [IsMarkovKernel P]
    {ψ ψ' : Measure X} (hH : IsHarris P ψ') (hψ : IsMaximalIrreducibility P ψ) :
    IsHarris P ψ :=
  ⟨hψ, fun A hA h0 => hH.2 A hA (pos_iff_ne_zero.2 fun h' => h0.ne' (hH.1.2.2 ψ hψ.2.1 h'))⟩

/-! ### The invariant σ-field -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 17.3.2** (iii) ⇒ (ii) (MT p. 436): for a Harris chain the invariant σ-field is
`P_x`-trivial for every `x` (indeed `P_μ`-trivial for every `μ`: Theorem 17.1.5 and
Proposition 17.1.4). -/
theorem theorem_17_3_2_iii_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) (μ : Measure X) [IsProbabilityMeasure μ] {A : Set (ℕ → X)}
    (hA : MeasurableSet A) (hinv : IsInvariantRV P (A.indicator 1)) :
    pathMeasure P μ A = 0 ∨ pathMeasure P μ A = 1 :=
  (proposition_17_1_4 P).1 (fun _ hm ⟨_, hC⟩ hh => theorem_17_1_5 hH hm hC hh) μ
    inferInstance A hA (hinv μ inferInstance)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 17.3.2** (ii) ⇒ (iii) (MT p. 436), for a recurrent chain: if the invariant σ-field
is `P_x`-trivial for every `x`, the chain is Harris. With the maximal Harris set `H` of
Theorem 9.1.5, `Q(·, A) = 1` on `H` for `A ∈ B⁺(X)`; from any `x` the chain enters `H` with
positive probability, so `Q(x, A) = ∫ Pⁿ(x, dy) Q(y, A) > 0`, and triviality of the invariant
event `{Φ ∈ A i.o.}` gives `Q(x, A) = 1`. -/
theorem theorem_17_3_2_ii_iii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hrec : IsRecurrentChain P ψ)
    (htriv : ∀ x, ∀ A : Set (ℕ → X), MeasurableSet A → IsInvariantRV P (A.indicator 1) →
      pathKernel P x A = 0 ∨ pathKernel P x A = 1) :
    IsHarris P ψ := by
  obtain ⟨H, hHmax, -, hψH⟩ := theorem_9_1_5 hrec
  obtain ⟨hHm, -, -, -, hHQ⟩ := hHmax
  have hψ := hrec.1
  have hψH' : 0 < ψ H := by
    refine pos_iff_ne_zero.2 fun h0 => hψ.1 (Measure.measure_univ_eq_zero.1 ?_)
    refine le_antisymm ?_ (zero_le)
    calc ψ univ = ψ (H ∪ Hᶜ) := by rw [union_compl_self]
      _ ≤ ψ H + ψ Hᶜ := measure_union_le _ _
      _ = 0 := by rw [h0, hψH, add_zero]
  refine ⟨hψ, fun A hA hψA x _ => ?_⟩
  have hinv : IsInvariantRV P ((ioSet A).indicator 1) := isInvariantRV_of_shift P fun k ω => by
    by_cases hω : ω ∈ ioSet A
    · rw [indicator_of_mem hω, indicator_of_mem ((isShiftInvariant_ioSet A k ω).2 hω)]; rfl
    · rw [indicator_of_notMem hω,
        indicator_of_notMem fun h => hω ((isShiftInvariant_ioSet A k ω).1 h)]
  rcases htriv x (ioSet A) (measurableSet_ioSet hA) hinv with h0 | h1
  · exfalso
    obtain ⟨n, hn⟩ := (hitProb_pos_iff P hHm x).1 (hψ.2.1 H hHm hψH' x)
    have hQ := harrisQ_eq_lintegral_pow P hA x (n + 1)
    have hle : (P ^ (n + 1)) x H ≤ harrisQ P A x := by
      rw [hQ, ← setLIntegral_one]
      calc ∫⁻ _ in H, (1 : ℝ≥0∞) ∂(P ^ (n + 1)) x
          = ∫⁻ y in H, harrisQ P A y ∂(P ^ (n + 1)) x :=
            setLIntegral_congr_fun hHm fun y hy => (hHQ A hA hψA y hy).symm
        _ ≤ ∫⁻ y, harrisQ P A y ∂(P ^ (n + 1)) x := setLIntegral_le_lintegral _ _
    exact (hn.trans_le hle).ne' h0
  · exact h1

/-! ### Theorem 17.3.2 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 17.3.2** (i) ⇔ (iii) (MT p. 436) for any chain with a nonzero σ-finite invariant
measure `π`: the ratio limit property holds iff the chain is Harris. -/
theorem theorem_17_3_2_i_iff_iii {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0) :
    HasRatioLimit P π ↔ ∃ ψ, IsHarris P ψ :=
  ⟨fun hR => ⟨_, theorem_17_3_2_i_iii hπ hπ0 hR⟩, fun ⟨_, hH⟩ _ _ hfm hgm hfi hgi hg x =>
    theorem_17_3_2_harris hH hπ hπ0 hfm hgm hfi hgi hg x⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 17.3.2** (MT p. 436), corrected: for a recurrent chain with a nonzero σ-finite
invariant measure `π`, the following are equivalent: (i) the ratio limit property; (ii) the
invariant σ-field is `P_x`-trivial for every `x`; (iii) the chain is Harris. The recurrence
hypothesis is needed only for (ii) ⇒ (iii) (`theorem_17_3_2_counterexample`). -/
theorem theorem_17_3_2_tfae {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hrec : IsRecurrentChain P ψ) {π : Measure X} (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0) :
    List.TFAE [HasRatioLimit P π,
      ∀ x, ∀ A : Set (ℕ → X), MeasurableSet A → IsInvariantRV P (A.indicator 1) →
        pathKernel P x A = 0 ∨ pathKernel P x A = 1,
      IsHarris P ψ] := by
  tfae_have 1 → 3 := fun hR =>
    (theorem_17_3_2_i_iii hπ hπ0 hR).of_isMaximalIrreducibility hrec.1
  tfae_have 3 → 1 := fun hH _ _ hfm hgm hfi hgi hg x =>
    theorem_17_3_2_harris hH hπ hπ0 hfm hgm hfi hgi hg x
  tfae_have 3 → 2 := fun hH x A hA hinv => by
    have h := theorem_17_3_2_iii_ii hH (Measure.dirac x) hA hinv
    rwa [pathMeasure_dirac] at h
  tfae_have 2 → 3 := theorem_17_3_2_ii_iii hrec
  tfae_finish

/-- **Correction to Theorem 17.3.2** (ii) ⇒ (iii) and (ii) ⇒ (i): the identity chain on `Bool`
with the invariant probability `δ_true` has a `P_x`-trivial invariant σ-field for every `x`
(each `P_x` is a point mass on path space), but the ratio limit fails (from `false`,
`Sₙ(1_{true}) = 0`) and the chain is not Harris. Statement (ii) needs an irreducibility and
recurrence hypothesis, as in `theorem_17_3_2_tfae`. -/
theorem theorem_17_3_2_counterexample :
    IsInvariantMeasure (Kernel.id : Kernel Bool Bool) (Measure.dirac true) ∧
      (∀ x : Bool, ∀ A : Set (ℕ → Bool), MeasurableSet A →
        pathKernel Kernel.id x A = 0 ∨ pathKernel Kernel.id x A = 1) ∧
      ¬ HasRatioLimit (Kernel.id : Kernel Bool Bool) (Measure.dirac true) ∧
      ¬ ∃ ψ, IsHarris (Kernel.id : Kernel Bool Bool) ψ := by
  obtain ⟨hinv, htriv, -⟩ := theorem_17_1_7_counterexample
  refine ⟨⟨inferInstance, hinv⟩, htriv, fun hR => ?_, ?_⟩
  · have := isMarkovKernel_pathKernel (Kernel.id : Kernel Bool Bool)
    set f : Bool → ℝ := ({true} : Set Bool).indicator 1 with hf
    have hfm : Measurable f := measurable_one.indicator (measurableSet_singleton true)
    have hfi : Integrable f (Measure.dirac true) :=
      (integrable_const (1 : ℝ)).indicator (measurableSet_singleton true)
    have hint : ∫ y, f y ∂(Measure.dirac true) = 1 := by
      rw [integral_dirac, hf, indicator_of_mem (mem_singleton true)]; rfl
    have h := hR f f hfm hfm hfi hfi (by rw [hint]; exact one_ne_zero) false
    obtain ⟨ω, hω, hc⟩ := (h.and (ae_eq_const_pathKernel_id false)).exists
    have hzero : ∀ n, pathSum f n ω = 0 := fun n => by
      unfold pathSum
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hc, hf, indicator_of_notMem (by simp)]
    rw [hint, div_one] at hω
    simp only [hzero, div_zero] at hω
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hω).symm
  · rintro ⟨ψ, hψ, -⟩
    obtain ⟨ψ', hmax, hprob, -, -, -, -⟩ := theorem_4_0_1 _ hψ.2.1 hψ.1
    obtain ⟨-, hno⟩ := proposition_4_2_2_zero_counterexample
    exact hno ⟨ψ', hprob, hmax.2.1⟩

end MeynTweedie.LimitTheorems

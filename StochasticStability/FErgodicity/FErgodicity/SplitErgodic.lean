/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.AtomErgodic
import FErgodicity.SplitInvariant

/-!
# Ergodicity of strongly aperiodic chains through splitting (MT §13.3.1)

Meyn and Tweedie, Theorem 13.3.1 (ii), pp. 326–327. `M : Minorization P` is a minorization
(5.2) on a set `C` with constant `δ` and probability `ν`, `P̌ = M.splitKernel` the split kernel on
`X̌ = X × Bool` and `α̌ = C₁ = M.checkAlpha` its atom.

**The split chain reaches its atom.** The book takes from Proposition 10.4.2 that the split
chain is positive Harris; what the regenerative argument needs is that `α̌` is reached almost
surely from every state.
* `Minorization.escape_eq_lintegral_baseK`: the escape probability `e(y) = 1 − Ľ(y, α̌)` is
  `e(y) = ∫ Q(y, dx) g(x)` with `g(x) = (1 − δ1_C(x)) e(x₀)`;
* `Minorization.lintegral_P_escapeFn`: `Pg = g + δ 1_C ν(g)`, since `P = Q ∘ splitK`;
* `Minorization.lintegral_pow_escapeFn`: `Pⁿg = g + ν(g) Σ_{k<n} Pᵏ(δ1_C)`;
* `Minorization.hitProb_checkAlpha_eq_one`: if `L(x, C) = 1` for every `x`, then
  `Ľ(y, α̌) = 1` for every `y ∈ X̌`. Since `g ≤ 1` and `U(x, C) = ∞`, `ν(g) = 0`; then `g` is
  harmonic, `g ≤ (1 − δ) sup g` on `C` and, by the first-entrance decomposition at `C`,
  everywhere, so `g = 0`.

**Results.**
* `split_comp_pow_map_fst`, `tvNorm_le_split` (13.57): `‖λPⁿ − π‖ ≤ ‖λ*P̌ⁿ − π*‖`.
* **Theorem 13.3.1 (ii)** (`theorem_13_3_1_ii`, p. 326), in the corrected form: a positive Harris
  chain with a minorization `P(x, ·) ≥ δν` on a set `C ∈ B⁺(X)` with `ν(C) > 0` satisfies
  `‖λPⁿ − π‖ → 0` for every initial probability `λ`.

**Correction.** Theorem 13.3.1 is stated for "positive Harris recurrent and strongly aperiodic"
chains, with strong aperiodicity defined (p. 114) as the existence of a `ν₁`-small set `A` with
`ν₁(A) > 0`, with no requirement that `A ∈ B⁺(X)`. The proof splits the chain on `A`, and the
atom `α̌ = A₁` must be accessible (Proposition 13.2.4, Theorem 13.3.1 (i)), which needs
`ψ(A) > 0`. Without it the theorem is false: `theorem_13_3_1_counterexample` in
`CountableErgodic` is a positive Harris chain of period `2` with a transient `ν₁`-small state.
The corrected statement adds `ψ(C) > 0`; it holds in particular when the chain is aperiodic
(Theorem 13.3.3).
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

namespace Minorization

variable {P : Kernel X X}

/-- The escape probability `e(y) = 1 − Ľ(y, α̌)` satisfies the first-step equation
`e(y) = ∫_{α̌ᶜ} P̌(y, dz) e(z)`. -/
theorem escape_first_step (M : Minorization P) [IsMarkovKernel P] (y : X × Bool) :
    haveI := M.isMarkovKernel_splitKernel
    1 - hitProb M.splitKernel M.checkAlpha y =
      ∫⁻ z in M.checkAlphaᶜ, (1 - hitProb M.splitKernel M.checkAlpha z) ∂M.splitKernel y := by
  have := M.isMarkovKernel_splitKernel
  have hm := M.measurableSet_checkAlpha
  have hfin : ∫⁻ z in M.checkAlphaᶜ, hitProb M.splitKernel M.checkAlpha z ∂M.splitKernel y ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.one_ne_top) (by
      calc ∫⁻ z in M.checkAlphaᶜ, hitProb M.splitKernel M.checkAlpha z ∂M.splitKernel y
          ≤ ∫⁻ _ in M.checkAlphaᶜ, 1 ∂M.splitKernel y :=
            lintegral_mono fun z => hitProb_le_one _ _ z
        _ ≤ 1 := by rw [setLIntegral_one]; exact prob_le_one)
  rw [lintegral_sub (measurable_hitProb _ hm) hfin
      (Eventually.of_forall fun z => hitProb_le_one _ _ z), setLIntegral_one,
    hitProb_first_step M.splitKernel hm y, tsub_add_eq_tsub_tsub, prob_compl_eq_one_sub hm]

/-- The function `g(x) = (1 − δ 1_C(x)) e(x₀)` on `X`. -/
noncomputable def escapeFn (M : Minorization P) [IsMarkovKernel P] (x : X) : ℝ≥0∞ :=
  haveI := M.isMarkovKernel_splitKernel
  (1 - M.splitProb x) * (1 - hitProb M.splitKernel M.checkAlpha (x, false))

/-- `g` is measurable. -/
theorem measurable_escapeFn (M : Minorization P) [IsMarkovKernel P] : Measurable M.escapeFn := by
  have := M.isMarkovKernel_splitKernel
  exact (measurable_const.sub M.measurable_splitProb).mul (measurable_const.sub
    ((measurable_hitProb _ M.measurableSet_checkAlpha).comp
      (measurable_id.prodMk measurable_const)))

/-- `g ≤ 1`. -/
theorem escapeFn_le_one (M : Minorization P) [IsMarkovKernel P] (x : X) : M.escapeFn x ≤ 1 :=
  mul_le_one' tsub_le_self tsub_le_self

/-- `e(y) = ∫ Q(y, dx) g(x)`. -/
theorem escape_eq_lintegral_baseK (M : Minorization P) [IsMarkovKernel P] (y : X × Bool) :
    haveI := M.isMarkovKernel_splitKernel
    1 - hitProb M.splitKernel M.checkAlpha y = ∫⁻ x, M.escapeFn x ∂M.baseK y := by
  have := M.isMarkovKernel_splitKernel
  have hm := M.measurableSet_checkAlpha
  rw [M.escape_first_step y, ← lintegral_indicator hm.compl, splitKernel_apply,
    M.lintegral_split _ (f := M.checkAlphaᶜ.indicator fun z =>
      1 - hitProb M.splitKernel M.checkAlpha z)
      ((measurable_const.sub (measurable_hitProb _ hm)).indicator hm.compl)]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ M.C
  · simp [escapeFn, checkAlpha, hx, indicator]
  · simp [escapeFn, checkAlpha, hx, indicator, M.splitProb_of_notMem hx]

/-- `Pg = g + δ 1_C ν(g)`. -/
theorem lintegral_P_escapeFn (M : Minorization P) [IsMarkovKernel P] (x : X) :
    ∫⁻ y, M.escapeFn y ∂P x = M.escapeFn x + M.splitProb x * ∫⁻ y, M.escapeFn y ∂M.ν := by
  have := M.isMarkovKernel_splitKernel
  have hmeas : Measurable fun z => ∫⁻ y, M.escapeFn y ∂M.baseK z :=
    M.measurable_escapeFn.lintegral_kernel
  have hP : P x = (M.baseK ∘ₖ M.splitK) x := by rw [M.baseK_comp_splitK]
  rw [hP, Kernel.lintegral_comp _ _ _ M.measurable_escapeFn, M.lintegral_splitK x hmeas,
    ← M.escape_eq_lintegral_baseK (x, false), baseK_apply_true]
  rfl

/-- `∫ δ1_C dPᵏ(x, ·) = δ Pᵏ(x, C)`. -/
theorem lintegral_splitProb (M : Minorization P) (μ : Measure X) :
    ∫⁻ y, M.splitProb y ∂μ = M.δ * μ M.C := by
  unfold splitProb
  exact lintegral_indicator_const M.measurableSet_C M.δ

/-- `Pⁿg = g + ν(g) Σ_{k<n} Pᵏ(δ 1_C)`. -/
theorem lintegral_pow_escapeFn (M : Minorization P) [IsMarkovKernel P] (n : ℕ) (x : X) :
    ∫⁻ y, M.escapeFn y ∂(P ^ n : Kernel X X) x = M.escapeFn x +
      (∫⁻ y, M.escapeFn y ∂M.ν) * ∑ k ∈ range n, ∫⁻ y, M.splitProb y ∂(P ^ k : Kernel X X) x := by
  induction n with
  | zero => rw [pow_zero_apply, lintegral_dirac' _ M.measurable_escapeFn, range_zero,
      Finset.sum_empty, mul_zero, add_zero]
  | succ n ih =>
    rw [pow_succ']
    change ∫⁻ y, M.escapeFn y ∂(P ∘ₖ (P ^ n : Kernel X X)) x = _
    rw [Kernel.lintegral_comp _ _ _ M.measurable_escapeFn]
    simp_rw [M.lintegral_P_escapeFn]
    rw [lintegral_add_left M.measurable_escapeFn, lintegral_mul_const _ M.measurable_splitProb, ih,
      Finset.sum_range_succ, mul_add, add_assoc, mul_comm (∫⁻ y, M.splitProb y ∂_)]

/-- `ν(g) = 0` when `U(x, C) = ∞` for some `x`. -/
theorem lintegral_ν_escapeFn_eq_zero (M : Minorization P) [IsMarkovKernel P] {x : X}
    (hU : potKernel P x M.C = ∞) : ∫⁻ y, M.escapeFn y ∂M.ν = 0 := by
  set c := ∫⁻ y, M.escapeFn y ∂M.ν
  have hle : ∀ n, c * ∑ k ∈ range n, ∫⁻ y, M.splitProb y ∂(P ^ k : Kernel X X) x ≤ 1 := fun n => by
    have := isMarkovKernel_pow P n
    calc c * ∑ k ∈ range n, ∫⁻ y, M.splitProb y ∂(P ^ k : Kernel X X) x
        ≤ M.escapeFn x + c * ∑ k ∈ range n, ∫⁻ y, M.splitProb y ∂(P ^ k : Kernel X X) x :=
          le_add_self
      _ = ∫⁻ y, M.escapeFn y ∂(P ^ n : Kernel X X) x := (M.lintegral_pow_escapeFn n x).symm
      _ ≤ ∫⁻ _, 1 ∂(P ^ n : Kernel X X) x := lintegral_mono M.escapeFn_le_one
      _ = 1 := by rw [lintegral_one, measure_univ]
  have htop : ∑' k, ∫⁻ y, M.splitProb y ∂(P ^ k : Kernel X X) x = ∞ := by
    refine top_unique ?_
    rw [← ENNReal.mul_top M.δ_pos.ne', ← hU, potKernel_apply P x M.measurableSet_C,
      ← ENNReal.tsum_mul_left]
    calc ∑' k, M.δ * (P ^ (k + 1) : Kernel X X) x M.C
        = ∑' k, ∫⁻ y, M.splitProb y ∂(P ^ (k + 1) : Kernel X X) x :=
          tsum_congr fun k => (M.lintegral_splitProb _).symm
      _ ≤ ∑' k, ∫⁻ y, M.splitProb y ∂(P ^ k : Kernel X X) x :=
          ENNReal.tsum_comp_le_tsum_of_injective (f := fun k => k + 1) (add_left_injective 1)
            (fun k => ∫⁻ y, M.splitProb y ∂(P ^ k : Kernel X X) x)
  have h1 : c * ∑' k, ∫⁻ y, M.splitProb y ∂(P ^ k : Kernel X X) x ≤ 1 := by
    rw [ENNReal.tsum_eq_iSup_nat, ENNReal.mul_iSup]
    exact iSup_le hle
  rw [htop] at h1
  by_contra hc
  rw [ENNReal.mul_top hc] at h1
  exact absurd h1 (by simp)

/-- `_CPⁿ⁺¹(x, X) → 0` when `L(x, C) = 1`. -/
theorem tendsto_tabooKernel_univ (P : Kernel X X) [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) {x : X} (hL : hitProb P C x = 1) :
    Tendsto (fun n => tabooKernel P hC n x univ) atTop (𝓝 0) := by
  have hadd : ∀ n, tabooKernel P hC n x univ =
      1 - ∑ j ∈ range n, tabooKernel P hC j x C := fun n => by
    have h := tabooSeq_univ_add_sum P hC (Measure.dirac x) n
    simp only [tabooSeq, dirac_kernel, measure_univ] at h
    exact ENNReal.eq_sub_of_add_eq (ENNReal.sum_ne_top.2 fun j _ =>
      ne_top_of_le_ne_top ENNReal.one_ne_top (tabooKernel_apply_le_one P hC j x C)) h
  simp_rw [hadd]
  have hs : Tendsto (fun n => ∑ j ∈ range n, tabooKernel P hC j x C) atTop (𝓝 1) := by
    rw [← hL, hitProb_eq_tsum P hC x]
    exact ENNReal.tendsto_nat_tsum _
  have := ENNReal.Tendsto.sub tendsto_const_nhds hs (Or.inl ENNReal.one_ne_top)
  rwa [tsub_self] at this

/-- **The split chain reaches its atom.** If `L(x, C) = 1` for every `x`, then the split chain
reaches `α̌ = C₁` almost surely from every state: `Ľ(y, α̌) = 1` for every `y ∈ X̌`. -/
theorem hitProb_checkAlpha_eq_one (M : Minorization P) [IsMarkovKernel P]
    (hL : ∀ x, hitProb P M.C x = 1) (y : X × Bool) :
    haveI := M.isMarkovKernel_splitKernel
    hitProb M.splitKernel M.checkAlpha y = 1 := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_resid
  have hC := M.measurableSet_C
  have hQ := (proposition_9_1_1 P hC fun x _ => hL x).1
  have hU : ∀ x, potKernel P x M.C = ∞ := fun x =>
    potKernel_eq_top_of_harrisQ_pos P hC (by rw [hQ x, hL x]; exact one_pos)
  have hν := M.lintegral_ν_escapeFn_eq_zero (hU y.1)
  -- `g` is harmonic
  have hharm : ∀ n x, ∫⁻ z, M.escapeFn z ∂(P ^ n : Kernel X X) x = M.escapeFn x := fun n x => by
    rw [M.lintegral_pow_escapeFn n x, hν, zero_mul, add_zero]
  set S := ⨆ x, M.escapeFn x with hS
  have hS1 : S ≤ 1 := iSup_le M.escapeFn_le_one
  have hSt : S ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hS1
  -- on `C`, `g ≤ (1 − δ) S`
  have hCbound : ∀ w ∈ M.C, M.escapeFn w ≤ (1 - M.δ) * S := fun w hw => by
    rw [escapeFn, M.splitProb_of_mem hw, M.escape_eq_lintegral_baseK, baseK_apply_false]
    gcongr
    calc ∫⁻ z, M.escapeFn z ∂M.resid w ≤ ∫⁻ _, S ∂M.resid w :=
          lintegral_mono fun z => le_iSup (fun x => M.escapeFn x) z
      _ = S := by rw [lintegral_const, measure_univ, mul_one]
  -- everywhere, `g ≤ (1 − δ) S`
  have hall : ∀ x, M.escapeFn x ≤ (1 - M.δ) * S := fun x => by
    have hbd : ∀ n, M.escapeFn x ≤ S * tabooKernel P hC n x univ + (1 - M.δ) * S := fun n => by
      rw [← hharm (n + 1) x, pow_succ_eq_firstEntrance P hC n x, lintegral_add_measure,
        lintegral_finsetSum_measure]
      refine add_le_add ?_ ?_
      · calc ∫⁻ z, M.escapeFn z ∂tabooKernel P hC n x ≤ ∫⁻ _, S ∂tabooKernel P hC n x :=
              lintegral_mono fun z => le_iSup (fun x => M.escapeFn x) z
          _ = S * tabooKernel P hC n x univ := lintegral_const S
      · have hj : ∀ j ∈ range n, ∫⁻ z, M.escapeFn z ∂((P ^ (n - j) : Kernel X X) ∘ₘ
            (tabooKernel P hC j x).restrict M.C) ≤ (1 - M.δ) * S * tabooKernel P hC j x M.C :=
          fun j _ => by
            rw [Measure.lintegral_bind (Kernel.aemeasurable _) M.measurable_escapeFn.aemeasurable]
            simp_rw [hharm]
            calc ∫⁻ w in M.C, M.escapeFn w ∂tabooKernel P hC j x
                ≤ ∫⁻ _ in M.C, (1 - M.δ) * S ∂tabooKernel P hC j x := setLIntegral_mono
                  measurable_const hCbound
              _ = (1 - M.δ) * S * tabooKernel P hC j x M.C := setLIntegral_const _ _
        refine (Finset.sum_le_sum hj).trans ?_
        rw [← Finset.mul_sum]
        refine mul_le_of_le_one_right zero_le ?_
        have h := tabooSeq_univ_add_sum P hC (Measure.dirac x) n
        simp only [tabooSeq, dirac_kernel, measure_univ] at h
        exact h ▸ le_add_self
    have hlim : Tendsto (fun n => S * tabooKernel P hC n x univ + (1 - M.δ) * S) atTop
        (𝓝 (S * 0 + (1 - M.δ) * S)) :=
      (ENNReal.Tendsto.const_mul (tendsto_tabooKernel_univ P hC (hL x)) (Or.inr hSt)).add
        tendsto_const_nhds
    rw [mul_zero, zero_add] at hlim
    exact ge_of_tendsto' hlim hbd
  -- hence `S = 0`
  have hS0 : S = 0 := by
    have h1 : S ≤ (1 - M.δ) * S := iSup_le hall
    have h2 : M.δ * S + (1 - M.δ) * S = S := by
      rw [← add_mul, add_tsub_cancel_of_le M.δ_lt_one.le, one_mul]
    have h3 : M.δ * S + (1 - M.δ) * S ≤ 0 + (1 - M.δ) * S := by rw [h2, zero_add]; exact h1
    have h4 := (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top
      (ENNReal.sub_ne_top ENNReal.one_ne_top) hSt)).1 h3
    rcases mul_eq_zero.1 (nonpos_iff_eq_zero.1 h4) with h | h
    · exact absurd h M.δ_pos.ne'
    · exact h
  have hg0 : ∀ x, M.escapeFn x = 0 := fun x =>
    nonpos_iff_eq_zero.1 (hS0 ▸ le_iSup (fun x => M.escapeFn x) x)
  have he := M.escape_eq_lintegral_baseK y
  simp_rw [hg0, lintegral_zero] at he
  exact le_antisymm (hitProb_le_one _ _ y) (tsub_eq_zero_iff_le.1 he)

/-- The return-time law of `α̌` is aperiodic when `ν(C) > 0`: `P̌(α̌, α̌) = δ ν(C) > 0`. -/
theorem isAperiodicLaw_entryLaw_checkAlpha (M : Minorization P) [IsMarkovKernel P]
    (hνC : 0 < M.ν M.C) {c : X} :
    haveI := M.isMarkovKernel_splitKernel
    IsAperiodicLaw
      (entryLaw M.splitKernel M.measurableSet_checkAlpha (Measure.dirac (c, true))) := by
  have := M.isMarkovKernel_splitKernel
  have := M.isProbabilityMeasure_ν
  intro d hd
  refine Nat.dvd_one.1 (hd 1 ?_)
  rw [show (1 : ℕ) = 0 + 1 from rfl, entryLaw_dirac_succ, tabooKernel_zero, splitKernel_apply_true,
    checkAlpha, M.split_apply_true _ M.measurableSet_C, inter_self]
  refine ENNReal.toReal_pos (ENNReal.mul_pos M.δ_pos.ne' hνC.ne').ne' ?_
  exact ENNReal.mul_ne_top M.δ_ne_top (measure_ne_top _ _)

end Minorization

/-! ### Transfer to the original chain -/

/-- (5.10) and (5.4): `(λ*P̌ⁿ)` has marginal `λPⁿ`. -/
theorem split_comp_pow_map_fst {P : Kernel X X} (M : Minorization P) (n : ℕ) (μ : Measure X) :
    ((M.splitKernel ^ n : Kernel (X × Bool) (X × Bool)) ∘ₘ M.split μ).map Prod.fst =
      (P ^ n : Kernel X X) ∘ₘ μ := by
  rw [M.split_comp_splitKernel_pow, M.split_map_fst]

/-- **(13.57)**: `‖λPⁿ − π‖ ≤ ‖λ*P̌ⁿ − π*‖`, since the original chain is the marginal of the
split chain. -/
theorem tvNorm_le_split {P : Kernel X X} [IsMarkovKernel P] (M : Minorization P) (n : ℕ)
    (μ π : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure π] :
    tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) π ≤
      tvNorm ((M.splitKernel ^ n : Kernel (X × Bool) (X × Bool)) ∘ₘ M.split μ) (M.split π) := by
  have := M.isMarkovKernel_splitKernel
  have := isMarkovKernel_pow M.splitKernel n
  have : IsFiniteMeasure (M.split μ) := ⟨by rw [M.split_univ]; exact measure_lt_top μ univ⟩
  have : IsFiniteMeasure (M.split π) := ⟨by rw [M.split_univ]; exact measure_lt_top π univ⟩
  have h := tvNorm_map_le measurable_fst
    ((M.splitKernel ^ n : Kernel (X × Bool) (X × Bool)) ∘ₘ M.split μ) (M.split π)
  rwa [split_comp_pow_map_fst, M.split_map_fst] at h

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.3.1 (ii)** (MT p. 326), corrected: a positive Harris chain with a minorization
`P(x, ·) ≥ δν` on a set `C ∈ B⁺(X)` with `ν(C) > 0` satisfies `‖λPⁿ − π‖ → 0` for every initial
probability `λ`, where `π` is the invariant probability. -/
theorem theorem_13_3_1_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (M : Minorization P) (hψC : 0 < ψ M.C) (hνC : 0 < M.ν M.C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) π) atTop (𝓝 0) := by
  have := M.isMarkovKernel_splitKernel
  obtain ⟨c, hc⟩ : M.C.Nonempty := nonempty_of_measure_ne_zero hψC.ne'
  have hca : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  have hacc := ((M.theorem_5_1_3_ii ψ).2 hph.1.1.2.1 hψC).2.2 _
    (M.isMaximalIrreducibility_split hph.1.1)
  have hrec := M.isRecurrentChain_split_of_isRecurrentChain (proposition_10_1_1 hph.2)
  have : IsProbabilityMeasure (M.split π) := M.isProbabilityMeasure_split π
  have : IsProbabilityMeasure (M.split μ) := M.isProbabilityMeasure_split μ
  have hπs : IsInvariant M.splitKernel (M.split π) := (proposition_10_4_1_ii M).2 hπ
  have hL : ∀ x, hitProb P M.C x = 1 := hph.1.hitProb_eq_one M.measurableSet_C hψC
  have hLs := M.hitProb_checkAlpha_eq_one hL
  have hrep := eq_smul_atomMeasure_of_accessible hacc hrec hca hπs
  have herg := tendsto_atomRenewal_of_aperiodicLaw M.isAtom_checkAlpha hca hrep (hLs _)
    (M.isAperiodicLaw_entryLaw_checkAlpha hνC)
  have hμs : ∫⁻ y, hitProb M.splitKernel M.checkAlpha y ∂M.split μ = 1 := by
    simp_rw [hLs]
    rw [lintegral_one, measure_univ]
  have hsplit := tendsto_tvNorm_of_ergodic_atom M.isAtom_checkAlpha hca hrep herg (M.split μ) hμs
  exact squeeze_zero (fun n => tvNorm_nonneg _ _) (fun n => tvNorm_le_split M n μ π) hsplit

end MeynTweedie.FErgodicity

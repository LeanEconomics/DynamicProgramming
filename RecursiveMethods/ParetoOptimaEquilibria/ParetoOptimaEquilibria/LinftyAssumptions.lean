/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.LinftyPrices
import ParetoOptimaEquilibria.WelfareSecond

/-!
# Inner product prices on `L∞`: Assumptions 15.8, 15.9, Exercise 15.12 and Theorem 15.8

SLP §15.4, pp. 468–469. The commodity space is `S = L∞(Z, 𝒵, μ)` (`Lp ℝ ⊤ μ`, one good).

* `LinftyNullSeq μ A`: `A_n ↓ 0` (p. 468).
* **Assumptions 15.8, 15.9** (`Assumption15_8`, `Assumption15_9`, p. 468).
* `supportsAllocation_of_limit_bounds`: the argument of Theorem 15.6, stated once for any normed
  space and any limit functional `ν`; it is reused for Theorems 15.8 and 15.9.
* **Theorem 15.8** (`theorem_15_8`, p. 469): the `L¹` part `ψ` of Lemma 15.7 supports a Pareto
  optimum supported by `φ`; `theorem_15_8_inner_product` combines it with Lemma 15.7.
* **Exercise 15.12** (p. 469): expected utility `u(x) = ∫ U(x(z)) dμᵢ(z)`
  (`linftyExpectedUtility`) with `μᵢ ≪ μ`: Assumption 15.3 (`ex_15_12_assumption15_3`) and
  Assumption 15.9 (`ex_15_12_assumption15_9`) hold for every continuous `U`; Assumption 15.2
  holds for concave `U` (`ex_15_12_assumption15_2`; all three: `ex_15_12`) but not in general
  (`ex_15_12_counterexample`).

**Corrections.**
* Exercise 15.12 is false for Assumption 15.2 as stated: `ex_15_12_counterexample`
  (`Z = {0, 1}`, uniform `μ = μᵢ`, `U(c) = c³`, `x = (2, 0)`, `x′ = (0, 1.9)`, `θ = 1/2`), as the
  transcription's NOTE says and the manual concedes. Corrected statement:
  `ex_15_12_assumption15_2` (`U` concave). The 15.3 and 15.9 parts are true as stated, for any
  finite `μᵢ ≪ μ`, and need only continuity of `U`. (The manual's 15.3 step needs uniform
  continuity of `U` on a bounded interval, unstated; its 15.9 step should read
  `μ(⋂ Aₙ) = lim μ(Aₙ) = 0`, hence `μᵢ(⋂ Aₙ) = 0` by `μᵢ ≪ μ`.)
* Theorem 15.8 assumes 15.1–15.5, 15.8, 15.9; only 15.1, 15.2, 15.8 and 15.9 are used. The
  book's proof "parallels exactly that of Theorem 15.6", whose mixing step needs
  quasi-concavity (hence 15.3) when `uᵢ(x̂ᵢ) = uᵢ(x)`. Here mixing is used only when
  `uᵢ(z) = uᵢ(xᵢ⁰) < uᵢ(x̂ᵢ)`, where 15.2 alone suffices (`supportsAllocation_of_limit_bounds`).
* As for Theorem 15.6, Theorem 15.8 needs a strictly preferred point for every consumer, and it
  does not assert `ψ ≠ 0`.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open MeasureTheory Filter Topology Set

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `A_n ↓ 0` (p. 468): `(A_n) ⊆ 𝒵` is nested decreasing with `μ(A_n) → 0`. -/
structure LinftyNullSeq (μ : Measure Z) (A : ℕ → Set Z) : Prop where
  measurableSet : ∀ n, MeasurableSet (A n)
  antitone : Antitone A
  tendsto_measure : Tendsto (fun n => μ (A n)) atTop (𝓝 0)

/-- **Assumption 15.8** (p. 468): if `x ∈ Xᵢ` and `A_n ↓ 0` then `x^{A_n} ∈ Xᵢ` for all large `n`;
likewise for each `Yⱼ`. -/
def Assumption15_8 (μ : Measure Z) (X : ι → Set (Lp ℝ ⊤ μ)) (Y : κ → Set (Lp ℝ ⊤ μ)) : Prop :=
  (∀ i, ∀ x ∈ X i, ∀ A, LinftyNullSeq μ A → ∀ᶠ n in atTop, linftyTrunc μ (A n) x ∈ X i) ∧
    ∀ j, ∀ y ∈ Y j, ∀ A, LinftyNullSeq μ A → ∀ᶠ n in atTop, linftyTrunc μ (A n) y ∈ Y j

/-- **Assumption 15.9** (p. 468): if `x, x′ ∈ Xᵢ`, `uᵢ(x) > uᵢ(x′)` and `A_n ↓ 0` then
`uᵢ(x^{A_n}) > uᵢ(x′)` for all large `n` (`uᵢ` is defined on all of `S`; with Assumption 15.8,
`x^{A_n} ∈ Xᵢ` eventually, which is the book's implicit reading). -/
def Assumption15_9 (μ : Measure Z) (X : ι → Set (Lp ℝ ⊤ μ)) (u : ι → Lp ℝ ⊤ μ → ℝ) : Prop :=
  ∀ i, ∀ x ∈ X i, ∀ x' ∈ X i, u i x' < u i x → ∀ A, LinftyNullSeq μ A →
    ∀ᶠ n in atTop, u i x' < u i (linftyTrunc μ (A n) x)

/-- **The common core of Theorems 15.6, 15.8 and 15.9** (steps 1–3 of the proof of Theorem 15.6).
Let `φ` support the feasible allocation `[(xᵢ), (yⱼ)]` and let `ν ∈ S*` satisfy
`φ(xᵢ) ≤ ν(z)` whenever `z ∈ Xᵢ` is strictly preferred to `xᵢ`, and `ν(w) ≤ φ(yⱼ)` for
`w ∈ Yⱼ`. If every consumer has a strictly preferred point `x̂ᵢ ∈ Xᵢ`, then `ν` also supports
the allocation. Only Assumptions 15.1 and 15.2 are used: for `uᵢ(z) = uᵢ(xᵢ)` the mixture
`θx̂ᵢ + (1 − θ)z` is strictly preferred by 15.2 alone, so no quasi-concavity (15.3) is needed. -/
theorem supportsAllocation_of_limit_bounds {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S} {y : κ → S}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (hF : Feasible X Y x y)
    {φ ν : StrongDual ℝ S} (hsat : ∀ i, ∃ xhat ∈ X i, u i (x i) < u i xhat)
    (hX : ∀ i, ∀ z ∈ X i, u i (x i) < u i z → φ (x i) ≤ ν z)
    (hY : ∀ j, ∀ w ∈ Y j, ν w ≤ φ (y j)) : SupportsAllocation X u Y x y ν := by
  have hX' : ∀ i, ∀ z ∈ X i, u i (x i) ≤ u i z → φ (x i) ≤ ν z := by
    intro i z hz hle
    rcases hle.lt_or_eq with hlt | heq
    · exact hX i z hz hlt
    · obtain ⟨xhat, hxhat, hsat'⟩ := hsat i
      have hzx : u i z < u i xhat := by
        rw [← heq]
        exact hsat'
      have hc : Continuous fun θ : ℝ => θ * ν xhat + (1 - θ) * ν z := by fun_prop
      have ht : Tendsto (fun θ : ℝ => θ * ν xhat + (1 - θ) * ν z) (𝓝[>] 0) (𝓝 (ν z)) := by
        have := hc.tendsto 0
        simp only [zero_mul, sub_zero, one_mul, zero_add] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
      have hmem : θ • xhat + (1 - θ) • z ∈ X i :=
        h1 i hxhat hz hθ.1.le (by linarith [hθ.2]) (by ring)
      have hlt : u i (x i) < u i (θ • xhat + (1 - θ) • z) := by
        rw [heq]
        exact h2 i xhat hxhat z hz hzx θ hθ.1 hθ.2
      have := hX i _ hmem hlt
      rwa [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
  obtain ⟨hxX, hyY, hsum⟩ := hF
  have hxi : ∀ i, φ (x i) ≤ ν (x i) := fun i => hX' i (x i) (hxX i) le_rfl
  have hyj : ∀ j, ν (y j) ≤ φ (y j) := fun j => hY j (y j) (hyY j)
  have heq : ∑ i, x i = ∑ j, y j := sub_eq_zero.1 hsum
  have e1 := congrArg ν heq
  have e2 := congrArg φ heq
  simp only [map_sum] at e1 e2
  have hA0 : 0 ≤ ∑ i, (ν (x i) - φ (x i)) :=
    Finset.sum_nonneg fun i _ => sub_nonneg.2 (hxi i)
  have hB0 : 0 ≤ ∑ j, (φ (y j) - ν (y j)) :=
    Finset.sum_nonneg fun j _ => sub_nonneg.2 (hyj j)
  have htot : ∑ i, (ν (x i) - φ (x i)) + ∑ j, (φ (y j) - ν (y j)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linarith
  have hA : ∑ i, (ν (x i) - φ (x i)) = 0 := by linarith
  have hB : ∑ j, (φ (y j) - ν (y j)) = 0 := by linarith
  have hxeq : ∀ i, ν (x i) = φ (x i) := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.2 (hxi i)).1 hA i
      (Finset.mem_univ i)
    linarith
  have hyeq : ∀ j, ν (y j) = φ (y j) := fun j => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sub_nonneg.2 (hyj j)).1 hB j
      (Finset.mem_univ j)
    linarith
  refine ⟨fun i z hz hle => ?_, fun j w hw => ?_⟩
  · rw [hxeq i]
    exact hX' i z hz hle
  · rw [hyeq j]
    exact hY j w hw

/-- **Theorem 15.8** (p. 469). Under Assumptions 15.1, 15.2, 15.8 and 15.9, if `φ ∈ L∞(μ)*` supports
the feasible allocation (conditions (4) and (5)) and every consumer has a strictly preferred
point, then so does any `ψ` with `ψ(x) = lim_n φ(x^{A_n})` along some `A_n ↓ 0` (in particular
the `ψ` of Lemma 15.7). Assumptions 15.3–15.5 are not needed. -/
theorem theorem_15_8 {X : ι → Set (Lp ℝ ⊤ μ)} {u : ι → Lp ℝ ⊤ μ → ℝ} {Y : κ → Set (Lp ℝ ⊤ μ)}
    {x : ι → Lp ℝ ⊤ μ} {y : κ → Lp ℝ ⊤ μ} (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u)
    (h8 : Assumption15_8 μ X Y) (h9 : Assumption15_9 μ X u) (hF : Feasible X Y x y)
    {φ : StrongDual ℝ (Lp ℝ ⊤ μ)} (hφ : SupportsAllocation X u Y x y φ)
    (hsat : ∀ i, ∃ xhat ∈ X i, u i (x i) < u i xhat) {A : ℕ → Set Z} (hA : LinftyNullSeq μ A)
    {ψ : StrongDual ℝ (Lp ℝ ⊤ μ)}
    (hψ : ∀ z, Tendsto (fun n => φ (linftyTrunc μ (A n) z)) atTop (𝓝 (ψ z))) :
    SupportsAllocation X u Y x y ψ := by
  refine supportsAllocation_of_limit_bounds (φ := φ) h1 h2 hF hsat (fun i z hz hlt => ?_)
    (fun j w hw => ?_)
  · refine ge_of_tendsto (hψ z) ?_
    filter_upwards [h8.1 i z hz A hA, h9 i z hz (x i) (hF.1 i) hlt A hA] with n hn1 hn2
    exact hφ.1 i _ hn1 hn2.le
  · refine le_of_tendsto (hψ w) ?_
    filter_upwards [h8.2 j w hw A hA] with n hn
    exact hφ.2 j _ hn

/-- **Theorem 15.8 with Lemma 15.7**: the supporting `φ` can be replaced by a supporting
`ψ(x) = ∫ p x dμ` with `p ∈ L¹(μ)` and `‖ψ‖ ≤ ‖φ‖`. -/
theorem theorem_15_8_inner_product [IsFiniteMeasure μ] {X : ι → Set (Lp ℝ ⊤ μ)}
    {u : ι → Lp ℝ ⊤ μ → ℝ} {Y : κ → Set (Lp ℝ ⊤ μ)} {x : ι → Lp ℝ ⊤ μ} {y : κ → Lp ℝ ⊤ μ}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (h8 : Assumption15_8 μ X Y)
    (h9 : Assumption15_9 μ X u) (hF : Feasible X Y x y) {φ : StrongDual ℝ (Lp ℝ ⊤ μ)}
    (hφ : SupportsAllocation X u Y x y φ) (hsat : ∀ i, ∃ xhat ∈ X i, u i (x i) < u i xhat) :
    ∃ ψ : StrongDual ℝ (Lp ℝ ⊤ μ), ‖ψ‖ ≤ ‖φ‖ ∧ SupportsAllocation X u Y x y ψ ∧
      ∃ p : Z → ℝ, Integrable p μ ∧ ∀ z, ψ z = ∫ w, p w * z w ∂μ := by
  obtain ⟨A, hAm, hAa, hAt, ψ, hψn, hψ, -, p, hp, hψp⟩ := lemma_15_7 φ
  exact ⟨ψ, hψn, theorem_15_8 h1 h2 h8 h9 hF hφ hsat ⟨hAm, hAa, hAt⟩ hψ, p, hp, hψp⟩

/-! ### Exercise 15.12 -/

/-- Expected utility `u(x) = ∫ U(x(z)) dν(z)` on `L∞(μ)` (Exercise 15.12; `ν = μᵢ`). -/
noncomputable def linftyExpectedUtility (ν : Measure Z) (U : ℝ → ℝ) (x : Lp ℝ ⊤ μ) : ℝ :=
  ∫ z, U (x z) ∂ν

/-- For `ν ≪ μ` and `x ∈ L∞(μ)`: `|x(z)| ≤ ‖x‖` for `ν`-a.e. `z`. -/
theorem ae_abs_le_norm_linfty_of_ac {ν : Measure Z} (hνμ : ν ≪ μ) (x : Lp ℝ ⊤ μ) :
    ∀ᵐ z ∂ν, |x z| ≤ ‖x‖ :=
  hνμ.ae_le (ae_abs_le_norm_linfty x)

/-- A continuous `U : ℝ → ℝ` is bounded on `[−R, R]`. -/
theorem exists_abs_le_of_continuous {U : ℝ → ℝ} (hU : Continuous U) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ c, |c| ≤ R → |U c| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hU.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun c hc =>
    (Real.norm_eq_abs _ ▸ hC c (abs_le.1 hc)).trans (le_max_left _ _)⟩

/-- For continuous `U`, finite `ν ≪ μ` and `x ∈ L∞(μ)`, `U ∘ x` is `ν`-integrable (so expected
utility is well defined on equivalence classes). -/
theorem integrable_comp_linfty {ν : Measure Z} [IsFiniteMeasure ν] (hνμ : ν ≪ μ) {U : ℝ → ℝ}
    (hU : Continuous U) (x : Lp ℝ ⊤ μ) : Integrable (fun z => U (x z)) ν := by
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_continuous hU ‖x‖
  refine Integrable.of_bound
    (hU.comp_stronglyMeasurable (Lp.stronglyMeasurable x)).aestronglyMeasurable M ?_
  filter_upwards [ae_abs_le_norm_linfty_of_ac hνμ x] with z hz
  rw [Real.norm_eq_abs]
  exact hM _ hz

/-- **Exercise 15.12, Assumption 15.3 part**: for continuous `U` and finite `ν ≪ μ`, expected
utility is continuous on `L∞(μ)` (`U` is uniformly continuous on a bounded interval containing
the essential ranges, the step left implicit in the manual). -/
theorem ex_15_12_continuous {ν : Measure Z} [IsFiniteMeasure ν] (hνμ : ν ≪ μ) {U : ℝ → ℝ}
    (hU : Continuous U) : Continuous (linftyExpectedUtility (μ := μ) ν U) := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  set R := ‖x₀‖ + 1 with hR
  have huc := (isCompact_Icc (a := -R) (b := R)).uniformContinuousOn_of_continuous
    hU.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  set r := ν.real univ with hr
  have hr0 : 0 ≤ r := measureReal_nonneg
  set ε' := ε / (r + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδU⟩ := huc ε' hε'0
  refine ⟨min δ 1, by positivity, fun x hx => ?_⟩
  rw [dist_eq_norm] at hx
  have hae : ∀ᵐ z ∂ν, ‖U (x z) - U (x₀ z)‖ ≤ ε' := by
    filter_upwards [hνμ.ae_le (Lp.coeFn_sub x x₀), ae_abs_le_norm_linfty_of_ac hνμ (x - x₀),
      ae_abs_le_norm_linfty_of_ac hνμ x₀] with z h1 h2 h3
    rw [h1, Pi.sub_apply] at h2
    have h4 : |x z| ≤ R := by
      have := abs_sub_abs_le_abs_sub (x z) (x₀ z)
      linarith [min_le_right δ 1]
    have := hδU (x z) (abs_le.1 h4) (x₀ z) (abs_le.1 (by linarith))
      (by rw [Real.dist_eq]; linarith [min_le_left δ 1])
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.le
  rw [Real.dist_eq, linftyExpectedUtility, linftyExpectedUtility,
    ← integral_sub (integrable_comp_linfty hνμ hU x) (integrable_comp_linfty hνμ hU x₀),
    ← Real.norm_eq_abs]
  calc ‖∫ z, (U (x z) - U (x₀ z)) ∂ν‖ ≤ ε' * r := norm_integral_le_of_norm_le_const hae
    _ < ε := by
      rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

/-- Expected utility is continuous along event truncations: `u(x^{A_n}) → u(x)` when `A_n ↓ 0`
(dominated convergence; `μ(⋂ A_n) = 0`, hence `ν(⋂ A_n) = 0` by absolute continuity). -/
theorem ex_15_12_tendsto {ν : Measure Z} [IsFiniteMeasure ν] (hνμ : ν ≪ μ) {U : ℝ → ℝ}
    (hU : Continuous U) {A : ℕ → Set Z} (hA : LinftyNullSeq μ A) (x : Lp ℝ ⊤ μ) :
    Tendsto (fun n => linftyExpectedUtility ν U (linftyTrunc μ (A n) x)) atTop
      (𝓝 (linftyExpectedUtility ν U x)) := by
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_continuous hU ‖x‖
  refine tendsto_integral_of_dominated_convergence (fun _ => M)
    (fun n => (integrable_comp_linfty hνμ hU _).aestronglyMeasurable) (integrable_const M)
    (fun n => ?_) ?_
  · filter_upwards [ae_abs_le_norm_linfty_of_ac hνμ (linftyTrunc μ (A n) x)] with z hz
    rw [Real.norm_eq_abs]
    exact hM _ (hz.trans (norm_linftyRestrict_le _ x))
  · have hall : ∀ᵐ z ∂ν, ∀ n, linftyTrunc μ (A n) x z = (A n)ᶜ.indicator x z :=
      hνμ.ae_le (ae_all_iff.2 fun n => coeFn_linftyRestrict (hA.measurableSet n).compl x)
    have hμnull : μ (⋂ n, A n) = 0 :=
      le_antisymm (ge_of_tendsto' hA.tendsto_measure fun n => measure_mono (iInter_subset _ n))
        zero_le
    have hnot : ∀ᵐ z ∂ν, z ∉ ⋂ n, A n := measure_eq_zero_iff_ae_notMem.1 (hνμ hμnull)
    filter_upwards [hall, hnot] with z h1 h2
    obtain ⟨N, hN⟩ : ∃ N, z ∉ A N := by simpa only [mem_iInter, not_forall] using h2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [h1 n, indicator_of_mem (show z ∈ (A n)ᶜ from fun h => hN (hA.antitone hn h))]

omit [Fintype ι] in
/-- **Exercise 15.12, Assumption 15.9 part**: expected utilities with continuous `Uᵢ` and finite
`μᵢ ≪ μ` satisfy Assumption 15.9 (on any `Xᵢ`). -/
theorem ex_15_12_assumption15_9 {X : ι → Set (Lp ℝ ⊤ μ)} {ν : ι → Measure Z}
    [∀ i, IsFiniteMeasure (ν i)] (hνμ : ∀ i, ν i ≪ μ) {U : ι → ℝ → ℝ}
    (hU : ∀ i, Continuous (U i)) :
    Assumption15_9 μ X (fun i => linftyExpectedUtility (ν i) (U i)) := by
  intro i x _ x' _ hlt A hA
  exact (ex_15_12_tendsto (hνμ i) (hU i) hA x).eventually (lt_mem_nhds hlt)

omit [Fintype ι] in
/-- **Exercise 15.12, Assumption 15.3 part**: expected utilities with continuous `Uᵢ` and finite
`μᵢ ≪ μ` satisfy Assumption 15.3. -/
theorem ex_15_12_assumption15_3 {X : ι → Set (Lp ℝ ⊤ μ)} {ν : ι → Measure Z}
    [∀ i, IsFiniteMeasure (ν i)] (hνμ : ∀ i, ν i ≪ μ) {U : ι → ℝ → ℝ}
    (hU : ∀ i, Continuous (U i)) :
    Assumption15_3 X (fun i => linftyExpectedUtility (ν i) (U i)) :=
  fun i => (ex_15_12_continuous (hνμ i) (hU i)).continuousOn

/-- For concave `U`, expected utility is concave: `θu(x) + (1 − θ)u(x′) ≤ u(θx + (1 − θ)x′)`. -/
theorem ex_15_12_concave {ν : Measure Z} [IsFiniteMeasure ν] (hνμ : ν ≪ μ) {U : ℝ → ℝ}
    (hU : ConcaveOn ℝ univ U) (hUc : Continuous U) (x x' : Lp ℝ ⊤ μ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    θ * linftyExpectedUtility ν U x + (1 - θ) * linftyExpectedUtility ν U x' ≤
      linftyExpectedUtility ν U (θ • x + (1 - θ) • x') := by
  rw [linftyExpectedUtility, linftyExpectedUtility, linftyExpectedUtility,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_comp_linfty hνμ hUc x).const_mul θ)
      ((integrable_comp_linfty hνμ hUc x').const_mul (1 - θ))]
  refine integral_mono_ae (((integrable_comp_linfty hνμ hUc x).const_mul θ).add
    ((integrable_comp_linfty hνμ hUc x').const_mul (1 - θ))) (integrable_comp_linfty hνμ hUc _) ?_
  filter_upwards [hνμ.ae_le (Lp.coeFn_add (θ • x) ((1 - θ) • x')),
    hνμ.ae_le (Lp.coeFn_smul θ x), hνμ.ae_le (Lp.coeFn_smul (1 - θ) x')] with z h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply]
  have := hU.2 (mem_univ (x z)) (mem_univ (x' z)) hθ0 (show (0 : ℝ) ≤ 1 - θ by linarith)
    (show θ + (1 - θ) = 1 by ring)
  simpa only [smul_eq_mul] using this

omit [Fintype ι] in
/-- **Exercise 15.12, Assumption 15.2 part, corrected**: with each `Uᵢ` concave (and continuous),
expected utility satisfies Assumption 15.2. (False for merely 15.2-satisfying `Uᵢ`:
`ex_15_12_counterexample`.) -/
theorem ex_15_12_assumption15_2 {X : ι → Set (Lp ℝ ⊤ μ)} {ν : ι → Measure Z}
    [∀ i, IsFiniteMeasure (ν i)] (hνμ : ∀ i, ν i ≪ μ) {U : ι → ℝ → ℝ}
    (hU : ∀ i, ConcaveOn ℝ univ (U i)) (hUc : ∀ i, Continuous (U i)) :
    Assumption15_2 X (fun i => linftyExpectedUtility (ν i) (U i)) := by
  intro i z _ z' _ hlt θ hθ0 hθ1
  have := ex_15_12_concave (hνμ i) (hU i) (hUc i) z z' hθ0.le hθ1.le
  nlinarith

open scoped ENNReal

omit [Fintype ι] in
/-- **Exercise 15.12, corrected** (p. 469): if each `Uᵢ` is concave and continuous and each `μᵢ` is
a finite measure with `μᵢ ≪ μ`, then the expected utilities `uᵢ(x) = ∫ Uᵢ ∘ x dμᵢ` satisfy
Assumptions 15.2, 15.3 and 15.9 (on any `Xᵢ`). -/
theorem ex_15_12 {X : ι → Set (Lp ℝ ⊤ μ)} {ν : ι → Measure Z}
    [∀ i, IsFiniteMeasure (ν i)] (hνμ : ∀ i, ν i ≪ μ) {U : ι → ℝ → ℝ}
    (hU : ∀ i, ConcaveOn ℝ univ (U i)) (hUc : ∀ i, Continuous (U i)) :
    Assumption15_2 X (fun i => linftyExpectedUtility (ν i) (U i)) ∧
      Assumption15_3 X (fun i => linftyExpectedUtility (ν i) (U i)) ∧
      Assumption15_9 μ X (fun i => linftyExpectedUtility (ν i) (U i)) :=
  ⟨ex_15_12_assumption15_2 hνμ hU hUc, ex_15_12_assumption15_3 hνμ hUc,
    ex_15_12_assumption15_9 hνμ hUc⟩

/-- The uniform probability measure on `Z = {0, 1}`. -/
noncomputable def finTwoUniform : Measure (Fin 2) := (2⁻¹ : ℝ≥0∞) • Measure.count

/-- `finTwoUniform` is a probability measure. -/
theorem isProbabilityMeasure_finTwoUniform : IsProbabilityMeasure finTwoUniform := by
  constructor
  rw [finTwoUniform, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  simp [ENNReal.inv_mul_cancel]

/-- Every point of `{0, 1}` has positive mass, so `a.e.` means everywhere. -/
theorem ae_finTwoUniform_iff {p : Fin 2 → Prop} :
    (∀ᵐ z ∂finTwoUniform, p z) ↔ ∀ z, p z := by
  rw [finTwoUniform, Measure.ae_ennreal_smul_measure_eq (by norm_num), Measure.ae_count_iff]

/-- Expected utility on `{0, 1}`: `u(x) = (U(x(0)) + U(x(1))) / 2`. -/
theorem finTwoUniform_expectedUtility (U : ℝ → ℝ) (x : Lp ℝ ⊤ finTwoUniform) :
    linftyExpectedUtility finTwoUniform U x = (U (x 0) + U (x 1)) / 2 := by
  have : IsProbabilityMeasure finTwoUniform := isProbabilityMeasure_finTwoUniform
  rw [linftyExpectedUtility, integral_fintype Integrable.of_finite, Fin.sum_univ_two]
  simp [finTwoUniform, measureReal_def, Measure.smul_apply]
  ring

/-- Every function on `{0, 1}` is in `L∞`. -/
theorem memLp_finTwoUniform (f : Fin 2 → ℝ) : MemLp f ⊤ finTwoUniform := by
  have : IsProbabilityMeasure finTwoUniform := isProbabilityMeasure_finTwoUniform
  exact MemLp.of_discrete

/-- The element `(a, b)` of `L∞({0, 1})`. -/
noncomputable def finTwoVec (a b : ℝ) : Lp ℝ ⊤ finTwoUniform :=
  (memLp_finTwoUniform ![a, b]).toLp ![a, b]

/-- `(a, b)` evaluates to `a` at `0` and `b` at `1`. -/
theorem finTwoVec_apply (a b : ℝ) (z : Fin 2) : finTwoVec a b z = ![a, b] z :=
  ae_finTwoUniform_iff.1 (memLp_finTwoUniform ![a, b]).coeFn_toLp z

/-- **Exercise 15.12 is false for Assumption 15.2** (NOTE p. 469). On `Z = {0, 1}` with the
uniform probability `μ = μᵢ`, `Xᵢ = L∞` satisfies 15.1 and 15.8 and `U(c) = c³` satisfies
Assumptions 15.2 and 15.3 on `ℝ`, but `u(x) = ∫ U ∘ x dμ` violates Assumption 15.2:
`x = (2, 0)`, `x′ = (0, 1.9)`, `u(x) = 4 > u(x′) = 3.4295`, yet `u(x/2 + x′/2) ≈ 0.929`. -/
theorem ex_15_12_counterexample :
    Assumption15_1 (fun _ : Unit => (univ : Set (Lp ℝ ⊤ finTwoUniform))) ∧
    Assumption15_8 finTwoUniform (fun _ : Unit => (univ : Set (Lp ℝ ⊤ finTwoUniform)))
      (fun _ : Unit => (univ : Set (Lp ℝ ⊤ finTwoUniform))) ∧
    Assumption15_2 (fun _ : Unit => (univ : Set ℝ)) (fun _ => fun c : ℝ => c ^ 3) ∧
    Assumption15_3 (fun _ : Unit => (univ : Set ℝ)) (fun _ => fun c : ℝ => c ^ 3) ∧
    ¬ Assumption15_2 (fun _ : Unit => (univ : Set (Lp ℝ ⊤ finTwoUniform)))
      (fun _ => linftyExpectedUtility finTwoUniform fun c : ℝ => c ^ 3) := by
  refine ⟨fun _ => convex_univ, ⟨fun _ _ _ _ _ => Eventually.of_forall fun _ => mem_univ _,
    fun _ _ _ _ _ => Eventually.of_forall fun _ => mem_univ _⟩, ?_,
    fun _ => (continuous_pow 3).continuousOn, ?_⟩
  · intro _ z _ z' _ hlt θ hθ0 hθ1
    have hmono : StrictMono fun c : ℝ => c ^ 3 := Odd.strictMono_pow (by decide)
    have hzz : z' < z := hmono.lt_iff_lt.1 hlt
    exact hmono (by simp only [smul_eq_mul]; nlinarith)
  · intro h
    have key := h () (finTwoVec 2 0) (mem_univ _) (finTwoVec 0 (19 / 10)) (mem_univ _) ?_
      (1 / 2) (by norm_num) (by norm_num)
    · have hmid : ∀ z, ((1 / 2 : ℝ) • finTwoVec 2 0 + (1 - 1 / 2 : ℝ) • finTwoVec 0 (19 / 10) :
          Lp ℝ ⊤ finTwoUniform) z = ![1, 19 / 20] z := by
        have : IsProbabilityMeasure finTwoUniform := isProbabilityMeasure_finTwoUniform
        intro z
        have h1 := ae_finTwoUniform_iff.1 (Lp.coeFn_add ((1 / 2 : ℝ) • finTwoVec 2 0)
          ((1 - 1 / 2 : ℝ) • finTwoVec 0 (19 / 10))) z
        have h2 := ae_finTwoUniform_iff.1 (Lp.coeFn_smul (1 / 2 : ℝ) (finTwoVec 2 0)) z
        have h3 := ae_finTwoUniform_iff.1
          (Lp.coeFn_smul (1 - 1 / 2 : ℝ) (finTwoVec 0 (19 / 10))) z
        rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, finTwoVec_apply,
          finTwoVec_apply]
        fin_cases z <;> norm_num
      simp only [finTwoUniform_expectedUtility, hmid, finTwoVec_apply] at key
      norm_num at key
    · simp only [finTwoUniform_expectedUtility, finTwoVec_apply]
      norm_num

end StokeyLucasPrescott.ParetoOptimaEquilibria

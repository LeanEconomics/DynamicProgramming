/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.MCRateRMSE
import Mathlib.Probability.CentralLimitTheorem

/-! # The √T central limit theorem for plain MC (post #3)

Post #3: "With MC of a Markov Chain the empirical transition matrix converges at `O(1/√T)`
(Meyn & Tweedie, Chpt 17)." Almost surely the error is of the larger order
`√(log log T / T)` (`MCRate`, `MCRateDriven`); `MCRateRMSE` proves `O(1/√T)` for the
root-mean-square error. This module proves the distributional form of the same scale, the
**central limit theorem**: for the post's MC (one i.i.d. sequence `u ∼ iidUniform ℕ` driving
`drivenPath P x₀ u`), from any start,

`(N_ij(T) − p_ij N_i(T))/√T ⇒ N(0, π_i p_ij (1 − p_ij))`,

whenever `N_i(T)/T → π_i > 0` (here: Poisson's equation `h − Ph = 1_{i} − π_i` has a bounded
solution, the hypothesis of `ae_tendsto_occCount_mc`; e.g. `P` irreducible).

**Route** (Meyn and Tweedie, §17.2, through the stack representation):
1. `departureIncrement_iid`: in the i.i.d.-stack model the departures from `i` are i.i.d.
   `ξ_k = g(step P i (V i k)) − (Pg)(i)`, centred, bounded, with variance `σ_i²(g)`
   (`rowVariance`), and `D_i(g, T) = Σ_{k < N_i(T)} ξ_k` (`departureDiscrepancy_mc_eq`).
2. `tendstoInDistribution_sum_floor_mul`: Mathlib's i.i.d. CLT
   (`tendstoInDistribution_inv_sqrt_mul_sum_sub`) along the deterministic index `⌊cT⌋`
   (`tendstoInDistribution_comp_of_tendsto`), rescaled by `√⌊cT⌋/√T → √c` with Slutsky
   (`TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`):
   `(1/√T) Σ_{k<⌊cT⌋} ξ_k ⇒ N(0, c v)`.
3. The random index: `N_i(T)/T → c` a.s. (`ae_abs_occCount_mc_le_mul`,
   `tendsto_div_of_forall_abs_sub_le`), so `(S_{N_i(T)} − S_{⌊cT⌋})/√T → 0` in probability
   (`lil_tendstoInMeasure_anscombe`, Kolmogorov's inequality), and the limit is unchanged
   (`tendstoInDistribution_of_tendstoInMeasure_sub`):
   `tendstoInDistribution_departureDiscrepancy_stack`.
4. Transfer to the driven path: the statistic is a measurable path functional
   (`measurable_departureDiscrepancy_div`) and the path laws agree
   (`map_drivenPath_eq_map_stackPath_path`): `tendstoInDistribution_departureDiscrepancy_driven`.

## Main results

* `tendstoInDistribution_departureDiscrepancy_driven`: `D_i(g, T)/√T ⇒ N(0, π_i σ_i²(g))`.
* `tendstoInDistribution_transCount_driven`: `(N_ij(T) − p_ij N_i(T))/√T ⇒
  N(0, π_i p_ij (1 − p_ij))`; `tendstoInDistribution_transCount_driven_of_irreducible`: the same
  for irreducible `P` with stationary `π`.
* `tendstoInDistribution_transCount_twoStateStay78`: for the `7/8`-chain,
  `(N_00(T) − (7/8) N_0(T))/√T ⇒ N(0, 7/128)`.

**Correction** (post #3, "converges at `O(1/√T)`"). The `1/√T` rate is the CLT (and RMSE)
scale: `√T (N_ij(T)/T − p_ij N_i(T)/T)` has a non-degenerate Gaussian limit when
`0 < p_ij < 1`, so the fluctuations of the empirical transition counts are of exact order
`1/√T` *in distribution*; almost surely they are not `O(1/√T)` (LIL,
`ae_not_tendsto_transCount_driven`).
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Finset Matrix Topology

variable {n : ℕ}

/-- The `k`-th **MC departure increment** of state `i` in the stack model:
`ξ_k = g(step P i (V i k)) − (Pg)(i)`. -/
noncomputable def departureIncrement (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ) {Ω : Type*}
    (V : Ω → Fin n → ℕ → ℝ) (i : Fin n) (k : ℕ) (ω : Ω) : ℝ :=
  g (step P i (V ω i k)) - (P *ᵥ g) i

/-- **The departure increments of one stack are i.i.d.**, centred, square integrable, with
variance `σ_i²(g)`. -/
theorem departureIncrement_iid {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V)
    {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (g : Fin n → ℝ) (i : Fin n) :
    iIndepFun (departureIncrement P g V i) Q ∧
      (∀ k, Measurable (departureIncrement P g V i k)) ∧
      (∀ k, IdentDistrib (departureIncrement P g V i k) (departureIncrement P g V i 0) Q Q) ∧
      MemLp (departureIncrement P g V i 0) 2 Q ∧
      ∫ ω, departureIncrement P g V i 0 ω ∂Q = 0 ∧
      Var[departureIncrement P g V i 0; Q] = rowVariance P g i := by
  set c := (P *ᵥ g) i with hc
  set ψ : ℝ → ℝ := fun u => g (step P i u) - c with hψdef
  have hψ : Measurable ψ := (measurable_of_finite fun j => g j - c).comp (measurable_step P i)
  have hind : iIndepFun (departureIncrement P g V i) Q :=
    (hV.indep i).comp (fun _ => ψ) fun _ => hψ
  have hm : ∀ k, Measurable (departureIncrement P g V i k) := fun k =>
    hψ.comp (hV.measurable i k)
  have hident : ∀ k, IdentDistrib (departureIncrement P g V i k)
      (departureIncrement P g V i 0) Q Q := fun k =>
    (IdentDistrib.mk (hV.measurable i k).aemeasurable (hV.measurable i 0).aemeasurable
      (by rw [hV.law i k, hV.law i 0])).comp hψ
  have hL2 : MemLp (departureIncrement P g V i 0) 2 Q := by
    refine MemLp.of_bound (hm 0).aestronglyMeasurable (∑ j, |g j - c|)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact single_le_sum (f := fun j => |g j - c|) (fun j _ => abs_nonneg _) (mem_univ _)
  have h0 : ∫ ω, departureIncrement P g V i 0 ω ∂Q = 0 := by
    rw [show (fun ω => departureIncrement P g V i 0 ω) = fun ω =>
      (fun j => g j - c) (step P i (V ω i 0)) from rfl,
      integral_comp_step hV hP i 0 (fun j => g j - c)]
    exact sum_mul_sub_mulVec_eq_zero hP g i
  have hvar : ∫ ω, departureIncrement P g V i 0 ω ^ 2 ∂Q = rowVariance P g i :=
    integral_comp_step hV hP i 0 (fun j => (g j - c) ^ 2)
  refine ⟨hind, hm, hident, hL2, h0, ?_⟩
  rw [variance_of_integral_eq_zero (hm 0).aemeasurable h0]
  exact hvar

/-- **Convergence in distribution along a subsequence**: if `X_m ⇒ Z` and `f T → ∞`, then
`X_{f T} ⇒ Z`. -/
theorem tendstoInDistribution_comp_of_tendsto {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => Q) Q') {f : ℕ → ℕ}
    (hf : Tendsto f atTop atTop) :
    TendstoInDistribution (fun T => X (f T)) atTop Z (fun _ => Q) Q' :=
  ⟨fun T => h.forall_aemeasurable (f T), h.aemeasurable_limit, h.tendsto.comp hf⟩

/-- **The deterministic-index CLT, rescaled**: for i.i.d. centred `ξ_k ∈ L²` with variance
`v` and `c > 0`, `(1/√T) Σ_{k < ⌊cT⌋} ξ_k ⇒ N(0, c v)`. -/
theorem tendstoInDistribution_sum_floor_mul {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hident : ∀ k, IdentDistrib (X k) (X 0) Q Q) (hL2 : MemLp (X 0) 2 Q)
    (h0 : ∫ ω, X 0 ω ∂Q = 0) {c : ℝ} (hc : 0 < c) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (c * Var[X 0; Q]).toNNReal) Q') :
    TendstoInDistribution (fun (T : ℕ) ω => (√(T : ℝ))⁻¹ * ∑ k ∈ range ⌊c * T⌋₊, X k ω) atTop
      Z (fun _ => Q) Q' := by
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have hvar0 : 0 ≤ Var[X 0; Q] := variance_nonneg _ _
  -- the standardised limit `Z / √c ∼ N(0, v)`
  have hZ1 : HasLaw (fun ω => Z ω / √c) (gaussianReal 0 Var[X 0; Q].toNNReal) Q' := by
    have := gaussianReal_div_const hZ (√c)
    rw [zero_div] at this
    convert this using 2
    ext
    rw [NNReal.coe_div, Real.coe_toNNReal _ hvar0, Real.coe_toNNReal _ (by positivity),
      NNReal.coe_mk, Real.sq_sqrt hc.le]
    field_simp
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ1 hL2 hind hident
  rw [h0] at hclt
  simp only [mul_zero, sub_zero] at hclt
  set m : ℕ → ℕ := fun T => ⌊c * T⌋₊ with hm
  have hmt : Tendsto m atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc)
  have hX := tendstoInDistribution_comp_of_tendsto hclt hmt
  -- the deterministic scale `√(m T) / √T → √c`
  have hmdiv : Tendsto (fun T : ℕ => (m T : ℝ) / T) atTop (𝓝 c) :=
    (tendsto_nat_floor_mul_div_atTop hc.le).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ha : Tendsto (fun T : ℕ => √(m T : ℝ) / √(T : ℝ)) atTop (𝓝 √c) := by
    have := (Real.continuous_sqrt.tendsto c).comp hmdiv
    refine this.congr fun T => ?_
    simp only [Function.comp_apply]
    exact Real.sqrt_div (Nat.cast_nonneg _) _
  have haM : TendstoInMeasure Q (fun (T : ℕ) (_ : Ω) => √(m T : ℝ) / √(T : ℝ)) atTop
      (fun _ => √c) :=
    tendstoInMeasure_of_tendsto_ae (fun T => aestronglyMeasurable_const)
      (Eventually.of_forall fun _ => ha)
  have hS := hX.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop) haM (fun T => aemeasurable_const)
  convert hS using 1
  · funext T ω
    change (√(T : ℝ))⁻¹ * ∑ k ∈ range (m T), X k ω =
      √(m T : ℝ) / √(T : ℝ) * ((√(m T : ℝ))⁻¹ * ∑ k ∈ range (m T), X k ω)
    by_cases hT : m T = 0
    · rw [hT, range_zero, sum_empty, mul_zero, mul_zero, mul_zero]
    · have hs : 0 < √(m T : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hT)
      field_simp
  · funext ω
    field_simp

/-- **Linear growth from a uniform `o(T)` bound**: if for every `ε > 0` there is `K` with
`|a T − T c| ≤ K + ε T` for all `T`, then `a T / T → c`. -/
theorem tendsto_div_of_forall_abs_sub_le {a : ℕ → ℝ} {c : ℝ}
    (h : ∀ ε > 0, ∃ K, ∀ T : ℕ, |a T - T * c| ≤ K + ε * T) :
    Tendsto (fun T : ℕ => a T / T) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := h (ε / 2) (by positivity)
  obtain ⟨T0, hT0⟩ := exists_nat_gt (2 * |K| / ε)
  refine ⟨T0 + 1, fun T hT => ?_⟩
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hTge : (T0 : ℝ) + 1 ≤ T := by exact_mod_cast hT
  rw [Real.dist_eq]
  have e : a T / T - c = (a T - T * c) / T := by field_simp
  rw [e, abs_div, abs_of_pos hTpos, div_lt_iff₀ hTpos]
  have h1 := hK T
  have h2 : 2 * |K| < ε * T := by
    rw [div_lt_iff₀ hε] at hT0
    nlinarith
  linarith [le_abs_self K]

/-- `x ↦ N_i(x, T)` is measurable on the path space (as a natural number). -/
theorem measurable_occCount_nat (i : Fin n) (T : ℕ) :
    Measurable fun x : ℕ → Fin n => occCount x i T :=
  measurable_to_countable' fun k => by
    have := measurable_occCount_real i T (measurableSet_singleton (k : ℝ))
    convert this using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Nat.cast_inj]

/-- `x ↦ (1/√T) D_i(g, T)` is measurable on the path space. -/
theorem measurable_departureDiscrepancy_div (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ) (i : Fin n)
    (T : ℕ) : Measurable fun x : ℕ → Fin n => (√(T : ℝ))⁻¹ * departureDiscrepancy P g x i T := by
  have e : (fun x : ℕ → Fin n => (√(T : ℝ))⁻¹ * departureDiscrepancy P g x i T) = fun x =>
      (√(T : ℝ))⁻¹ * incrementSum (fun a b => if a = i then g b - (P *ᵥ g) i else 0) x T :=
    funext fun x => by rw [departureDiscrepancy_eq_incrementSum]
  rw [e]
  exact (measurable_incrementSum _ T).const_mul _

/-- **The √T CLT for the MC departure discrepancies, i.i.d. stacks.** If Poisson's equation
`h − Ph = 1_{i} − c` has a bounded solution and `c > 0` (so `N_i(T)/T → c` a.s.), then for
the i.i.d.-stack path `(1/√T) D_i(g, T) ⇒ N(0, c σ_i²(g))`. -/
theorem tendstoInDistribution_departureDiscrepancy_stack {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {i : Fin n} {c M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c) (hM : ∀ k, |h k| ≤ M)
    (hc : 0 < c) (g : Fin n → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (c * rowVariance P g i).toNNReal) Q') :
    haveI := isProbabilityMeasure_iidUniform (Fin n × ℕ)
    TendstoInDistribution (fun (T : ℕ) (w : Fin n × ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      departureDiscrepancy P g (stackPath P x₀ (Function.curry w)) i T) atTop Z
      (fun _ => iidUniform (Fin n × ℕ)) Q' := by
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  have hV := isIIDStacks_iidUniform (n := n)
  obtain ⟨hind, hm, hident, hL2, h0, hvar⟩ := departureIncrement_iid hV hP g i
  set Y := departureIncrement P g (fun w : Fin n × ℕ → ℝ => Function.curry w) i
  rw [← hvar] at hZ
  have hdet := tendstoInDistribution_sum_floor_mul hind hident hL2 h0 hc hZ
  set K : ℕ → (Fin n × ℕ → ℝ) → ℕ := fun T w => occCount (stackPath P x₀ (Function.curry w)) i T
  have hKm : ∀ T, Measurable (K T) := fun T =>
    (measurable_occCount_nat i T).comp (measurable_stackPath P x₀)
  have hK : ∀ᵐ w ∂iidUniform (Fin n × ℕ), Tendsto (fun T => (K T w : ℝ) / T) atTop (𝓝 c) := by
    filter_upwards [ae_abs_occCount_mc_le_mul hV hP x₀ hh hM] with w hw
    exact tendsto_div_of_forall_abs_sub_le hw
  have hans := lil_tendstoInMeasure_anscombe hind hm hident hL2 h0 hKm hc hK
  have e : (fun (T : ℕ) (w : Fin n × ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      departureDiscrepancy P g (stackPath P x₀ (Function.curry w)) i T) =
      fun (T : ℕ) (w : Fin n × ℕ → ℝ) => (√(T : ℝ))⁻¹ * ∑ k ∈ range (K T w), Y k w :=
    funext fun T => funext fun w => by
      rw [departureDiscrepancy_mc_eq P x₀ (fun w : Fin n × ℕ → ℝ => Function.curry w) g i w T]
      rfl
  have hmeas : ∀ T : ℕ, AEMeasurable (fun w => (√(T : ℝ))⁻¹ * ∑ k ∈ range (K T w), Y k w)
      (iidUniform (Fin n × ℕ)) := fun T => by
    have := ((measurable_departureDiscrepancy_div P g i T).comp
      (measurable_stackPath P x₀)).aemeasurable (μ := iidUniform (Fin n × ℕ))
    rw [show ((fun x : ℕ → Fin n => (√(T : ℝ))⁻¹ * departureDiscrepancy P g x i T) ∘
      fun w : Fin n × ℕ → ℝ => stackPath P x₀ (Function.curry w)) =
      fun w => (√(T : ℝ))⁻¹ * ∑ k ∈ range (K T w), Y k w from congrFun e T] at this
    exact this
  rw [e]
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z hdet ?_ hmeas
  convert hans using 1
  funext T w
  simp only [Pi.sub_apply]
  ring

/-- **The √T CLT for the MC departure discrepancies, MC driving** (one i.i.d. sequence, post
#3's construction). Under the hypotheses of `tendstoInDistribution_departureDiscrepancy_stack`,
for `u ∼ iidUniform ℕ`, `(1/√T) D_i(g, T) ⇒ N(0, c σ_i²(g))`. The two path laws agree
(`map_drivenPath_eq_map_stackPath_path`), so the laws of the statistic agree for every `T`. -/
theorem tendstoInDistribution_departureDiscrepancy_driven {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {i : Fin n} {c M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c) (hM : ∀ k, |h k| ≤ M)
    (hc : 0 < c) (g : Fin n → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (c * rowVariance P g i).toNNReal) Q') :
    haveI := isProbabilityMeasure_iidUniform ℕ
    TendstoInDistribution (fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      departureDiscrepancy P g (drivenPath P x₀ u) i T) atTop Z (fun _ => iidUniform ℕ) Q' := by
  have := isProbabilityMeasure_iidUniform ℕ
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  have hst := tendstoInDistribution_departureDiscrepancy_stack hP x₀ hh hM hc g hZ
  have hF := measurable_departureDiscrepancy_div P g i
  have hlaw : ∀ T : ℕ, (iidUniform (Fin n × ℕ)).map (fun w =>
      (√(T : ℝ))⁻¹ * departureDiscrepancy P g (stackPath P x₀ (Function.curry w)) i T) =
      (iidUniform ℕ).map (fun u =>
        (√(T : ℝ))⁻¹ * departureDiscrepancy P g (drivenPath P x₀ u) i T) := fun T => by
    have e1 := Measure.map_map (μ := iidUniform ℕ) (hF T) (measurable_drivenPath P x₀)
    have e2 := Measure.map_map (μ := iidUniform (Fin n × ℕ)) (hF T) (measurable_stackPath P x₀)
    rw [map_drivenPath_eq_map_stackPath_path hP x₀] at e1
    exact e2.symm.trans e1
  exact ⟨fun T => ((hF T).comp (measurable_drivenPath P x₀)).aemeasurable,
    hst.aemeasurable_limit, hst.tendsto.congr fun T => Subtype.ext (hlaw T)⟩

/-- **The √T CLT for the MC transition counts** (post #3's empirical transition matrix, at the
CLT scale). If Poisson's equation `h − Ph = 1_{i} − c` has a bounded solution and `c > 0`
(`c = π_i`), then for MC driving by one i.i.d. sequence, from any start,
`(N_ij(T) − p_ij N_i(T))/√T ⇒ N(0, π_i p_ij (1 − p_ij))`. -/
theorem tendstoInDistribution_transCount_driven {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {i : Fin n} {c M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c) (hM : ∀ k, |h k| ≤ M)
    (hc : 0 < c) (j : Fin n) {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (c * (P i j * (1 - P i j))).toNNReal) Q') :
    haveI := isProbabilityMeasure_iidUniform ℕ
    TendstoInDistribution (fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      ((transCount (drivenPath P x₀ u) i j T : ℝ) - P i j * occCount (drivenPath P x₀ u) i T))
      atTop Z (fun _ => iidUniform ℕ) Q' := by
  rw [← rowVariance_indicator hP i j] at hZ
  have e : (fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      ((transCount (drivenPath P x₀ u) i j T : ℝ) - P i j * occCount (drivenPath P x₀ u) i T)) =
      fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ * departureDiscrepancy P
        (fun k => if k = j then 1 else 0) (drivenPath P x₀ u) i T :=
    funext fun T => funext fun u => by
      rw [transCount_sub_eq_departureDiscrepancy (P : Matrix (Fin n) (Fin n) ℝ)]
  rw [e]
  exact tendstoInDistribution_departureDiscrepancy_driven hP x₀ hh hM hc _ hZ

/-- **The √T CLT for irreducible chains.** For an irreducible stochastic `P` with stationary
distribution `π` (so `π_i > 0`), MC driving gives
`(N_ij(T) − p_ij N_i(T))/√T ⇒ N(0, π_i p_ij (1 − p_ij))` from any start. -/
theorem tendstoInDistribution_transCount_driven_of_irreducible
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsStochastic P) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j)
    {μ : Fin n → ℝ} (hμ : IsStationaryDistribution P μ) (x₀ i j : Fin n) {Ω' : Type*}
    [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (μ i * (P i j * (1 - P i j))).toNNReal) Q') :
    haveI := isProbabilityMeasure_iidUniform ℕ
    TendstoInDistribution (fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      ((transCount (drivenPath P x₀ u) i j T : ℝ) - P i j * occCount (drivenPath P x₀ u) i T))
      atTop Z (fun _ => iidUniform ℕ) Q' := by
  have : Nonempty (Fin n) := ⟨x₀⟩
  obtain ⟨h, hh⟩ := exists_poisson hP.nonneg hP.sum_eq_one hirr hμ
    (fun k => if k = i then (1 : ℝ) else 0)
  rw [dotProduct_indicator] at hh
  exact tendstoInDistribution_transCount_driven hP x₀ hh (M := ∑ k, |h k|)
    (fun k => single_le_sum (f := fun k => |h k|) (fun _ _ => abs_nonneg _) (mem_univ k))
    (hμ.pos hP.nonneg hirr i) j hZ

/-- **A concrete instance** (two-state chain with stay probability `7/8`, `π = (1/2, 1/2)`):
for MC driving from any start, `(N_00(T) − (7/8) N_0(T))/√T ⇒ N(0, 7/128)`, realised by the
identity on `(ℝ, N(0, 7/128))`. -/
theorem tendstoInDistribution_transCount_twoStateStay78 (x₀ : Fin 2) :
    haveI := isProbabilityMeasure_iidUniform ℕ
    TendstoInDistribution (fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      ((transCount (drivenPath twoStateStay78 x₀ u) 0 0 T : ℝ) -
        7 / 8 * occCount (drivenPath twoStateStay78 x₀ u) 0 T))
      atTop id (fun _ => iidUniform ℕ) (gaussianReal 0 (7 / 128 : ℝ).toNNReal) := by
  have h00 : twoStateStay78 0 0 = 7 / 8 := by simp only [twoStateStay78, ite_true]
  have hv : (1 / 2 : ℝ) * (twoStateStay78 0 0 * (1 - twoStateStay78 0 0)) = 7 / 128 := by
    rw [h00]
    norm_num
  have hZ : HasLaw id (gaussianReal 0 ((1 / 2 : ℝ) * (twoStateStay78 0 0 *
      (1 - twoStateStay78 0 0))).toNNReal) (gaussianReal 0 (7 / 128 : ℝ).toNNReal) := by
    rw [hv]
    exact HasLaw.id
  have := tendstoInDistribution_transCount_driven_of_irreducible isStochastic_twoStateStay78
    irreducible_twoStateStay78 isStationaryDistribution_twoStateStay78 x₀ 0 0 hZ
  rw [h00] at this
  exact this

end RQMCMarkov.MarkovDriving

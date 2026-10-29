/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.PoissonInvariance

/-!
# Poisson's equation for periodic chains: the resolvent (MT §17.4.1, §17.7)

Meyn and Tweedie, proof of Theorem 17.4.2 (pp. 445–446) and Theorem 17.7.1 (pp. 459–460).
`PoissonEquation` and `PoissonInvariance` prove Theorems 17.4.2 and 17.7.1 for aperiodic chains;
here the aperiodicity assumption is dropped, as the book does, by passing through the resolvent
`K = K_{a_ε} = (1 − ε) Σᵢ εⁱ Pⁱ` (`resolvent P ε`, (3.26)), which is strongly aperiodic for every
`ψ`-irreducible chain (Proposition 5.4.5).

**The resolvent identity.**
* `resolvent_eq_dirac_add_comp`, (17.40): `K_{a_ε}(x, ·) = (1 − ε) δₓ + ε (K_{a_ε} ∘ P)(x, ·)`,
  i.e. `K_{a_ε} = εK_{a_ε}P + (1 − ε)I` (`PK_{a_ε} = K_{a_ε}P`, "first `P`, then `K_{a_ε}`"),
  and `integral_resolvent_eq`, its form for integrals.
* `isPoissonSolution_of_resolvent`, (17.41)–(17.42): if `ĥ − K_{a_ε}ĥ = g − c`, then
  `ĝ = ε(1 − ε)⁻¹ K_{a_ε}ĥ` solves `ĝ − Pĝ = g − c`.

**(V3) for the resolvent** (p. 445), with `ε = 1/2`:
* `lintegral_resolvent_half_add_le`: `PV + f ≤ V + b 1_C` gives `KV + Kf ≤ V + b K(·, C)`;
  `half_le_lintegral_resolvent_half`: `Kf ≥ f/2`.
* `driftV3_resolvent_half`: `K` satisfies (V3) with `4V`, `f`, `4b` and
  `C' = {K(·, C) ≥ (4b + 1)⁻¹}`; `isPetite_resolvent_half_level`: `C'` is petite for `K`
  (Proposition 5.5.6 (i) and Proposition 5.5.4 (i)); `resolvent_half_irreducible_aperiodic`:
  `K` is `ψ`-irreducible and aperiodic; `resolvent_half_hypotheses` collects these.
* `exists_poisson_of_resolvent_half`: the bound `|ĝ| ≤ R(4b + 5)(V + 1)` for `ĝ = Kĥ`.

**Results.**
* **Theorem 17.4.2** (`theorem_17_4_2_periodic`, p. 445): for every `ψ`-irreducible chain,
  periodic or not, (V3) with `V` finite, `f ≥ 1`, `C` petite and `π(V) < ∞` give `R < ∞` and,
  for every `|g| ≤ f`, a measurable solution of Poisson's equation with `|ĝ| ≤ R(V + 1)`.
* **Theorem 17.7.1** (`theorem_17_7_1_periodic`, p. 459): the same without `π(V) < ∞`.

**Deviations from the book.** The book takes a general `ε ∈ (0, 1)`; the identity (17.40) and
the transfer (17.42) are proved for every `ε`, and the drift for the resolvent for `ε = 1/2`,
which is all the theorems need. The book obtains (V3) for `K` with the set
`Cₙ = {K(·, C) ≥ 1/n}`; here `n` is chosen explicitly, `1/n = (4b + 1)⁻¹`.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- **(17.40)**, measure form: `K_{a_ε}(x, ·) = (1 − ε) δₓ + ε (K_{a_ε} ∘ P)(x, ·)`, where
`(K_{a_ε} ∘ₖ P)(x, ·) = ∫ P(x, dy) K_{a_ε}(y, ·)` is "first `P`, then `K_{a_ε}`". -/
theorem resolvent_eq_dirac_add_comp (P : Kernel X X) [IsMarkovKernel P] (ε : ℝ≥0∞) (x : X) :
    resolvent P ε x = (1 - ε) • Measure.dirac x + ε • (resolvent P ε ∘ₖ P) x := by
  ext A hA
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Kernel.comp_apply' _ _ _ hA, resolvent_apply P ε x hA]
  simp_rw [resolvent_apply P ε _ hA]
  rw [lintegral_const_mul _ (Measurable.tsum fun i =>
      (Kernel.measurable_coe _ hA).const_mul _),
    lintegral_tsum fun i => ((Kernel.measurable_coe _ hA).const_mul _).aemeasurable,
    tsum_eq_zero_add' ENNReal.summable, pow_zero, one_mul, pow_zero_apply]
  have hterm : ∀ i, ε ^ (i + 1) * (P ^ (i + 1)) x A =
      ε * ∫⁻ y, ε ^ i * (P ^ i) y A ∂P x := fun i => by
    rw [lintegral_const_mul _ (Kernel.measurable_coe _ hA), add_comm i 1,
      Kernel.pow_add_apply_eq_lintegral P 1 i x hA, pow_one, pow_add, pow_one]
    ring
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left]
  ring

/-- **(17.40)** for integrals: `K_{a_ε}h(x) = (1 − ε) h(x) + ε (K_{a_ε} ∘ P) h(x)` for `h`
integrable for `K_{a_ε}(x, ·)`, `0 < ε < 1`. -/
theorem integral_resolvent_eq (P : Kernel X X) [IsMarkovKernel P] {ε : ℝ≥0∞} (hε0 : 0 < ε)
    (hε1 : ε < 1) {h : X → ℝ} (hhm : Measurable h) {x : X} (hi : Integrable h (resolvent P ε x)) :
    Integrable h ((resolvent P ε ∘ₖ P) x) ∧
      ∫ y, h y ∂resolvent P ε x =
        (1 - ε).toReal * h x + ε.toReal * ∫ y, h y ∂(resolvent P ε ∘ₖ P) x := by
  have hεt : ε ≠ ∞ := (hε1.trans ENNReal.one_lt_top).ne
  have heq := resolvent_eq_dirac_add_comp P ε x
  rw [heq] at hi
  have h1 := hi.left_of_add_measure
  have h2 := hi.right_of_add_measure
  have h2' : Integrable h ((resolvent P ε ∘ₖ P) x) := (integrable_smul_measure hε0.ne' hεt).1 h2
  refine ⟨h2', ?_⟩
  rw [heq, integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac' _ _ hhm.stronglyMeasurable, smul_eq_mul, smul_eq_mul]


/-- **(17.42)**, the transfer of Poisson's equation from the resolvent to `P` (MT p. 445): for
`0 < ε < 1`, if `ĥ` solves Poisson's equation (17.41) `ĥ − K_{a_ε}ĥ = g − c` for `K_{a_ε}`, then
`ĝ = ε (1 − ε)⁻¹ K_{a_ε}ĥ` solves `ĝ − Pĝ = g − c` for `P`. -/
theorem isPoissonSolution_of_resolvent (P : Kernel X X) [IsMarkovKernel P] {ε : ℝ≥0∞}
    (hε0 : 0 < ε) (hε1 : ε < 1) {g h : X → ℝ} {c : ℝ}
    (hsol : IsPoissonSolution (resolvent P ε) g h c) (hhm : Measurable h) :
    IsPoissonSolution P g
      (fun x => ε.toReal / (1 - ε).toReal * kernelInt (resolvent P ε) h x) c := by
  have := isMarkovKernel_resolvent P hε1
  set K := resolvent P ε with hK
  have hεt : ε ≠ ∞ := (hε1.trans ENNReal.one_lt_top).ne
  have he0 : 0 < ε.toReal := ENNReal.toReal_pos hε0.ne' hεt
  have he1 : ε.toReal < 1 := by
    have := (ENNReal.toReal_lt_toReal hεt ENNReal.one_ne_top).2 hε1
    rwa [ENNReal.toReal_one] at this
  have h1e : (1 - ε).toReal = 1 - ε.toReal := by
    rw [ENNReal.toReal_sub_of_le hε1.le ENNReal.one_ne_top, ENNReal.toReal_one]
  intro x
  obtain ⟨hcomp, hid⟩ := integral_resolvent_eq P hε0 hε1 hhm (hsol x).1
  have hnorm : Integrable (fun y => ∫ z, ‖h z‖ ∂K y) (P x) :=
    (integrable_comp_iff hhm.aestronglyMeasurable).1 hcomp |>.2
  have hKi : Integrable (kernelInt K h) (P x) :=
    hnorm.mono' (measurable_kernelInt K hhm).aestronglyMeasurable
      (Eventually.of_forall fun y => norm_integral_le_integral_norm _)
  refine ⟨hKi.const_mul _, ?_⟩
  have hPK : ∫ y, ε.toReal / (1 - ε).toReal * kernelInt K h y ∂P x =
      ε.toReal / (1 - ε).toReal * ∫ y, h y ∂(K ∘ₖ P) x := by
    rw [integral_const_mul, Kernel.integral_comp hcomp]
    rfl
  have hP := (hsol x).2
  simp only [kernelInt] at hP ⊢
  change ε.toReal / (1 - ε).toReal * ∫ y, h y ∂K x -
    ∫ y, ε.toReal / (1 - ε).toReal * kernelInt K h y ∂P x = g x - c
  rw [hPK, h1e]
  rw [h1e] at hid
  have h1e0 : (1 - ε.toReal) ≠ 0 := by linarith
  field_simp
  linear_combination (1 - ε.toReal) * hP + hid


/-- `K_{a_{1/2}}f(x) = Σᵢ 2⁻¹ 2⁻ⁱ Pⁱf(x)`. -/
theorem lintegral_resolvent_half_eq (P : Kernel X X) (f : X → ℝ≥0∞) (x : X) :
    ∫⁻ y, f y ∂resolvent P 2⁻¹ x =
      ∑' i, (1 - 2⁻¹) * (2⁻¹ : ℝ≥0∞) ^ i * ∫⁻ y, f y ∂(P ^ i : Kernel X X) x :=
  lintegral_sampledKernel_eq P _ x f

/-- **The resolvent under (V3)** (MT p. 445): if `PV + f ≤ V + b 1_C` with `V` finite and
`b < ∞`, then `K V + K f ≤ V + b K(·, C)` for `K = K_{a_{1/2}}`. -/
theorem lintegral_resolvent_half_add_le {P : Kernel X X} [IsMarkovKernel P] {V f : X → ℝ≥0∞}
    {b : ℝ≥0∞} {C : Set X} (hV : Measurable V) (hf : Measurable f) (hC : MeasurableSet C)
    (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C) (x : X) :
    ∫⁻ y, V y ∂resolvent P 2⁻¹ x + ∫⁻ y, f y ∂resolvent P 2⁻¹ x ≤
      V x + b * resolvent P 2⁻¹ x C := by
  set a : ℕ → ℝ≥0∞ := fun i => (1 - 2⁻¹) * (2⁻¹ : ℝ≥0∞) ^ i with hadef
  set s : ℕ → ℝ≥0∞ := fun i => ∫⁻ y, V y ∂(P ^ i : Kernel X X) x with hsdef
  set F : ℕ → ℝ≥0∞ := fun i => ∫⁻ y, f y ∂(P ^ i : Kernel X X) x with hFdef
  set c : ℕ → ℝ≥0∞ := fun i => (P ^ i : Kernel X X) x C with hcdef
  have ha0 : a 0 = 2⁻¹ := by rw [hadef]; simp only [pow_zero, mul_one, ENNReal.one_sub_inv_two]
  have ha : ∀ i, a (i + 1) = 2⁻¹ * a i := fun i => by rw [hadef]; simp only; ring
  have hat : ∀ i, a i ≠ ∞ := fun i => ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by simp))
  -- one step of the drift under `Pⁱ(x, ·)`
  have hF1 : ∀ i, s (i + 1) + F i ≤ s i + b * c i := by
    intro i
    have := isMarkovKernel_pow P i
    have hs1 : s (i + 1) = ∫⁻ y, ∫⁻ z, V z ∂P y ∂(P ^ i : Kernel X X) x := by
      rw [hsdef]; simp only
      rw [pow_succ']
      exact Kernel.lintegral_comp P (P ^ i) x hV
    rw [hs1, hFdef, hsdef, hcdef]
    simp only
    rw [← lintegral_add_right _ hf, ← lintegral_indicator_const hC b,
      ← lintegral_add_right _ (measurable_const.indicator hC)]
    exact lintegral_mono fun y => hdrift y
  have hc1 : ∀ i, c i ≤ 1 := fun i => by
    have := isMarkovKernel_pow P i
    exact prob_le_one
  have hs : ∀ i, s i ≠ ∞ := by
    intro i
    induction i with
    | zero =>
      rw [hsdef]; simp only
      rw [pow_zero_apply, lintegral_dirac' x hV]; exact hVfin x
    | succ i ih =>
      refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ih, hb⟩) ?_
      calc s (i + 1) ≤ s (i + 1) + F i := le_self_add
        _ ≤ s i + b * c i := hF1 i
        _ ≤ s i + b := add_le_add le_rfl (mul_le_of_le_one_right' (hc1 i))
  have hs0 : s 0 = V x := by
    rw [hsdef]; simp only
    rw [pow_zero_apply, lintegral_dirac' x hV]
  -- the truncated inequality
  have htrunc : ∀ N, ∑ i ∈ Finset.range N, (a i * s i + a i * F i) ≤
      V x + b * resolvent P 2⁻¹ x C := by
    intro N
    set T := ∑ i ∈ Finset.range N, a i * s (i + 1) with hT
    set FN := ∑ i ∈ Finset.range N, a i * F i with hFN
    set CN := ∑ i ∈ Finset.range N, a i * c i with hCN
    have hTt : T ≠ ∞ := ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top (hat i) (hs (i + 1))
    have hsum1 : T + FN ≤ ∑ i ∈ Finset.range N, a i * s i + b * CN := by
      rw [hT, hFN, hCN, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      calc a i * s (i + 1) + a i * F i = a i * (s (i + 1) + F i) := (mul_add _ _ _).symm
        _ ≤ a i * (s i + b * c i) := mul_le_mul' le_rfl (hF1 i)
        _ = a i * s i + b * (a i * c i) := by ring
    have hA : ∑ i ∈ Finset.range (N + 1), a i * s i = 2⁻¹ * V x + 2⁻¹ * T := by
      rw [Finset.sum_range_succ', ha0, hs0, hT, Finset.mul_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ha i, mul_assoc]
    have hmono : ∑ i ∈ Finset.range N, a i * s i ≤ ∑ i ∈ Finset.range (N + 1), a i * s i := by
      rw [Finset.sum_range_succ]; exact le_self_add
    have h2 : T + FN ≤ 2⁻¹ * V x + 2⁻¹ * T + b * CN := by
      calc T + FN ≤ _ := hsum1
        _ ≤ ∑ i ∈ Finset.range (N + 1), a i * s i + b * CN := add_le_add hmono le_rfl
        _ = _ := by rw [hA]
    have hhalf : T = 2⁻¹ * T + 2⁻¹ * T := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    have h3 : 2⁻¹ * T + FN ≤ 2⁻¹ * V x + b * CN := by
      have h2' : 2⁻¹ * T + (2⁻¹ * T + FN) ≤ 2⁻¹ * T + (2⁻¹ * V x + b * CN) := by
        calc 2⁻¹ * T + (2⁻¹ * T + FN) = T + FN := by rw [← add_assoc, ← hhalf]
          _ ≤ 2⁻¹ * V x + 2⁻¹ * T + b * CN := h2
          _ = 2⁻¹ * T + (2⁻¹ * V x + b * CN) := by ring
      exact (ENNReal.add_le_add_iff_left (ENNReal.mul_ne_top (by simp) hTt)).1 h2'
    have hCN : CN ≤ resolvent P 2⁻¹ x C := by
      rw [resolvent, sampledKernel_apply P _ x hC]
      exact ENNReal.sum_le_tsum _
    calc ∑ i ∈ Finset.range N, (a i * s i + a i * F i)
        = ∑ i ∈ Finset.range N, a i * s i + FN := by rw [Finset.sum_add_distrib]
      _ ≤ 2⁻¹ * V x + 2⁻¹ * T + FN := add_le_add (hmono.trans hA.le) le_rfl
      _ = 2⁻¹ * V x + (2⁻¹ * T + FN) := by ring
      _ ≤ 2⁻¹ * V x + (2⁻¹ * V x + b * CN) := add_le_add le_rfl h3
      _ = V x + b * CN := by rw [← add_assoc, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
      _ ≤ V x + b * resolvent P 2⁻¹ x C := add_le_add le_rfl (mul_le_mul' le_rfl hCN)
  rw [lintegral_resolvent_half_eq, lintegral_resolvent_half_eq, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_of_sum_range_le htrunc


/-- `K_{a_{1/2}}f ≥ f/2`. -/
theorem half_le_lintegral_resolvent_half (P : Kernel X X) {f : X → ℝ≥0∞} (hf : Measurable f)
    (x : X) : 2⁻¹ * f x ≤ ∫⁻ y, f y ∂resolvent P 2⁻¹ x := by
  rw [lintegral_resolvent_half_eq]
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum 0)
  rw [pow_zero, mul_one, ENNReal.one_sub_inv_two, pow_zero_apply, lintegral_dirac' x hf]

/-- **(V3) for the resolvent** (MT p. 445, proof of Theorem 17.4.2): if `PV + f ≤ V + b 1_C` with
`V` finite, `b < ∞` and `f ≥ 1`, then `K = K_{a_{1/2}}` satisfies (V3) with the function `4V`,
the same `f`, the constant `4b` and the set `C' = {x : K(x, C) ≥ δ}`, `δ = (4b + 1)⁻¹`. -/
theorem driftV3_resolvent_half {P : Kernel X X} [IsMarkovKernel P] {V f : X → ℝ≥0∞}
    {b : ℝ≥0∞} {C : Set X} (hV : Measurable V) (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    (hC : MeasurableSet C) (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C) :
    DriftV3 (resolvent P 2⁻¹) (fun x => 4 * V x) f (4 * b)
      {x | (4 * b + 1)⁻¹ ≤ resolvent P 2⁻¹ x C} := by
  have := isMarkovKernel_resolvent P (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
  set δ : ℝ≥0∞ := (4 * b + 1)⁻¹ with hδ
  set C' := {x | δ ≤ resolvent P 2⁻¹ x C} with hC'
  intro x
  have hmain := lintegral_resolvent_half_add_le hV hf hC hVfin hb hdrift x
  have hKf := half_le_lintegral_resolvent_half P hf x
  have hfx : f x ≠ ∞ := by
    have h := hdrift x
    have hrhs : V x + C.indicator (fun _ => b) x ≠ ∞ := ENNReal.add_ne_top.2 ⟨hVfin x, by
      by_cases hx : x ∈ C
      · rw [indicator_of_mem hx]; exact hb
      · rw [indicator_of_notMem hx]; exact ENNReal.zero_ne_top⟩
    exact ne_top_of_le_ne_top hrhs (le_trans le_add_self h)
  set ι := C'.indicator (fun _ => b) x with hι
  have hι4 : C'.indicator (fun _ => 4 * b) x = 4 * ι := by
    by_cases hx : x ∈ C'
    · rw [hι, indicator_of_mem hx, indicator_of_mem hx]
    · rw [hι, indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  have hKC : b * resolvent P 2⁻¹ x C ≤ b * δ + ι := by
    by_cases hx : x ∈ C'
    · rw [hι, indicator_of_mem hx]
      exact (mul_le_of_le_one_right' prob_le_one).trans le_add_self
    · rw [hι, indicator_of_notMem hx, add_zero]
      exact mul_le_mul' le_rfl (not_le.1 hx).le
  have hbδ : 4 * (b * δ) ≤ 1 := by
    have hne : 4 * b + 1 ≠ 0 := by simp
    have hnt : 4 * b + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hb, by simp⟩
    rw [← mul_assoc]
    calc 4 * b * δ ≤ (4 * b + 1) * δ := mul_le_mul' le_self_add le_rfl
      _ = 1 := ENNReal.mul_inv_cancel hne hnt
  have h1 : ∫⁻ y, V y ∂resolvent P 2⁻¹ x + 2⁻¹ * f x ≤ V x + b * δ + ι :=
    (add_le_add le_rfl hKf).trans (hmain.trans (by rw [add_assoc]; exact add_le_add le_rfl hKC))
  have h4 := mul_le_mul' (le_refl (4 : ℝ≥0∞)) h1
  have h22 : (4 : ℝ≥0∞) * (2⁻¹ * f x) = f x + f x := by
    rw [← two_mul, ← mul_assoc, show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_assoc 2 2,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  rw [mul_add, h22, mul_add, mul_add] at h4
  have h5 : 4 * ∫⁻ y, V y ∂resolvent P 2⁻¹ x + f x + f x ≤ 4 * V x + 4 * ι + f x :=
    calc 4 * ∫⁻ y, V y ∂resolvent P 2⁻¹ x + f x + f x
        = 4 * ∫⁻ y, V y ∂resolvent P 2⁻¹ x + (f x + f x) := by rw [add_assoc]
      _ ≤ 4 * V x + 4 * (b * δ) + 4 * ι := h4
      _ ≤ 4 * V x + 1 + 4 * ι := add_le_add (add_le_add le_rfl hbδ) le_rfl
      _ ≤ 4 * V x + f x + 4 * ι := add_le_add (add_le_add le_rfl (hf1 x)) le_rfl
      _ = 4 * V x + 4 * ι + f x := by ring
  rw [lintegral_const_mul _ hV, hι4]
  exact (ENNReal.add_le_add_iff_right hfx).1 h5


/-- The resolvent `K_{a_{1/2}}` of a `ψ`-irreducible chain on a countably generated space is
`ψ`-irreducible (with `ψ` maximal) and aperiodic, indeed strongly aperiodic (Proposition 5.4.5),
with a small set in `B⁺(X)`. -/
theorem resolvent_half_irreducible_aperiodic [MeasurableSpace.CountablyGenerated X]
    {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) :
    haveI := isMarkovKernel_resolvent P (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
    IsMaximalIrreducibility (resolvent P 2⁻¹) ψ ∧ IsAperiodic (resolvent P 2⁻¹) ψ := by
  have hε0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hε1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have := isMarkovKernel_resolvent P hε1
  have hψK := isMaximalIrreducibility_resolvent P hψ hε0 hε1
  obtain ⟨M, hMc, hψC⟩ := theorem_5_2_3_resolvent P hψ hε0 hε1
  have := M.isProbabilityMeasure_ν
  have hνC : M.ν M.C = 1 := (prob_compl_eq_zero_iff M.measurableSet_C).1 hMc
  exact ⟨hψK, isAperiodic_of_minorization hψK M hψC (by rw [hνC]; exact one_pos)⟩

/-- **Petite sets for the resolvent** (MT p. 445, via Theorem 5.5.6 and Proposition 5.5.4): if
`C` is petite for `P`, then for every `δ > 0` the set `{x : K_{a_{1/2}}(x, C) ≥ δ}` is petite
for the `K_{a_{1/2}}`-chain. -/
theorem isPetite_resolvent_half_level [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {C : Set X}
    (hpet : IsPetite P C) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    IsPetite (resolvent P 2⁻¹) {x | δ ≤ resolvent P 2⁻¹ x C} := by
  have hε0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hε1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  obtain ⟨a, ν, hC⟩ := hpet
  obtain ⟨ν', hν'⟩ := (proposition_5_5_6_i P hψ hC).2 2⁻¹ hε0 hε1
  have hCK : IsPetiteSet (resolvent P 2⁻¹) (diracDist 1) ν' C :=
    ⟨hν'.1, isSamplingDist_diracDist 1, hν'.2.2.1, fun x hx => by
      rw [sampledKernel_diracDist, pow_one]
      have := hν'.2.2.2 x hx
      rwa [sampledKernel_geomDist] at this⟩
  have hm : MeasurableSet {x | δ ≤ resolvent P 2⁻¹ x C} :=
    measurableSet_le measurable_const (Kernel.measurable_coe _ hν'.1)
  obtain ⟨δ', -, h⟩ := proposition_5_5_4_i (resolvent P 2⁻¹) hCK hm (isSamplingDist_diracDist 1)
    ⟨δ, hδ, fun x hx => by rw [sampledKernel_diracDist, pow_one]; exact hx⟩
  exact ⟨_, _, h⟩

/-- **(17.42) with bounds**: a solution `ĥ` of Poisson's equation for `K = K_{a_{1/2}}` with
`|ĥ| ≤ R (4V + 1)` gives the solution `ĝ = K ĥ` for `P` with `|ĝ| ≤ R (4b + 5)(V + 1)`, when
`PV + f ≤ V + b 1_C`, `V` finite, `b < ∞`. -/
theorem exists_poisson_of_resolvent_half {P : Kernel X X} [IsMarkovKernel P] {V f : X → ℝ≥0∞}
    {b : ℝ≥0∞} {C : Set X} (hV : Measurable V) (hf : Measurable f) (hC : MeasurableSet C)
    (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C) {g h : X → ℝ} {c R : ℝ}
    (hR : 0 ≤ R) (hsol : IsPoissonSolution (resolvent P 2⁻¹) g h c) (hhm : Measurable h)
    (hbd : ∀ x, |h x| ≤ R * ((4 * V x).toReal + 1)) :
    ∃ gh : X → ℝ, IsPoissonSolution P g gh c ∧ Measurable gh ∧
      ∀ x, |gh x| ≤ R * (4 * b.toReal + 5) * ((V x).toReal + 1) := by
  have hε0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hε1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have := isMarkovKernel_resolvent P hε1
  set K := resolvent P 2⁻¹ with hK
  have hcoef : (2⁻¹ : ℝ≥0∞).toReal / (1 - 2⁻¹ : ℝ≥0∞).toReal = 1 := by
    rw [ENNReal.one_sub_inv_two]
    exact div_self (ENNReal.toReal_pos (by simp) (by simp)).ne'
  have hP := isPoissonSolution_of_resolvent P hε0 hε1 hsol hhm
  rw [hcoef] at hP
  simp only [one_mul] at hP
  refine ⟨kernelInt K h, hP, measurable_kernelInt K hhm, fun x => ?_⟩
  -- `K(4V)(x) ≤ 4V(x) + 4b`
  have hKV : ∫⁻ y, 4 * V y ∂K x ≤ 4 * V x + 4 * b := by
    have h1 := lintegral_resolvent_half_add_le hV hf hC hVfin hb hdrift x
    have h2 : ∫⁻ y, V y ∂K x ≤ V x + b :=
      le_self_add.trans (h1.trans (add_le_add le_rfl (mul_le_of_le_one_right' prob_le_one)))
    rw [lintegral_const_mul _ hV, ← mul_add]
    exact mul_le_mul' le_rfl h2
  have hpt : ∀ y, ENNReal.ofReal |h y| ≤ ENNReal.ofReal R * (4 * V y + 1) := fun y => by
    refine (ENNReal.ofReal_le_ofReal (hbd y)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hR, ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one,
      ENNReal.ofReal_toReal (ENNReal.mul_ne_top (by simp) (hVfin y)), ENNReal.ofReal_one]
  have h3 := ofReal_abs_integral_le_lintegral (μ := K x) hpt
  rw [lintegral_const_mul _ ((hV.const_mul 4).add_const 1),
    lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one] at h3
  have h4 : ENNReal.ofReal |kernelInt K h x| ≤
      ENNReal.ofReal R * (4 * V x + 4 * b + 1) :=
    h3.trans (mul_le_mul' le_rfl (add_le_add hKV le_rfl))
  have hfin : ENNReal.ofReal R * (4 * V x + 4 * b + 1) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (by simp) (hVfin x), ENNReal.mul_ne_top (by simp) hb⟩, by simp⟩)
  have h5 := ENNReal.toReal_mono hfin h4
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_ofReal hR,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) (hVfin x),
      ENNReal.mul_ne_top (by simp) hb⟩) (by simp),
    ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (hVfin x)) (ENNReal.mul_ne_top (by simp) hb),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_one] at h5
  refine h5.trans ?_
  have hv := ENNReal.toReal_nonneg (a := V x)
  have hb0 := ENNReal.toReal_nonneg (a := b)
  have : ((4 : ℝ≥0∞)).toReal = 4 := by norm_num
  rw [this]
  have hle : 4 * (V x).toReal + 4 * b.toReal + 1 ≤ (4 * b.toReal + 5) * ((V x).toReal + 1) := by
    nlinarith
  calc R * (4 * (V x).toReal + 4 * b.toReal + 1) ≤ R * ((4 * b.toReal + 5) * ((V x).toReal + 1)) :=
        mul_le_mul_of_nonneg_left hle hR
    _ = R * (4 * b.toReal + 5) * ((V x).toReal + 1) := by ring


variable [MeasurableSpace.CountablyGenerated X]

/-- The resolvent `K = K_{a_{1/2}}` inherits the hypotheses of Theorem 17.4.2: it is
`ψ`-irreducible and aperiodic, has the invariant probability `π`, and satisfies (V3) with `4V`,
`f`, `4b` and a petite set. -/
theorem resolvent_half_hypotheses {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C) (hV : Measurable V)
    (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C) :
    haveI := isMarkovKernel_resolvent P (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
    IsMaximalIrreducibility (resolvent P 2⁻¹) ψ ∧ IsAperiodic (resolvent P 2⁻¹) ψ ∧
      ∃ C' : Set X, IsPetite (resolvent P 2⁻¹) C' ∧
        DriftV3 (resolvent P 2⁻¹) (fun x => 4 * V x) f (4 * b) C' := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hpet; exact h.1
  obtain ⟨hψK, hapK⟩ := resolvent_half_irreducible_aperiodic hψ
  have hδ : (0 : ℝ≥0∞) < (4 * b + 1)⁻¹ :=
    ENNReal.inv_pos.2 (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hb, by simp⟩)
  exact ⟨hψK, hapK, _, isPetite_resolvent_half_level hψ hpet hδ,
    driftV3_resolvent_half hV hf hf1 hCm hVfin hb hdrift⟩

/-- **Theorem 17.4.2** (MT p. 445), general case: for a `ψ`-irreducible chain (periodic or not)
with (V3) for an everywhere finite `V`, `f ≥ 1`, a petite `C`, and `π(V) < ∞`, there is `R < ∞`
such that for every `|g| ≤ f` Poisson's equation `ĝ − Pĝ = g − π(g)` has a measurable solution
with `|ĝ| ≤ R (V + 1)`. The proof is the book's: Theorem 17.4.2 for the aperiodic resolvent
`K_{a_{1/2}}` (`theorem_17_4_2`), then (17.42). -/
theorem theorem_17_4_2_periodic {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C) (hV : Measurable V)
    (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) (hπV : ∫⁻ x, V x ∂π ≠ ∞) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ g : X → ℝ, Measurable g → (∀ x, ENNReal.ofReal |g x| ≤ f x) →
      ∃ gh : X → ℝ, IsPoissonSolution P g gh (∫ y, g y ∂π) ∧ Measurable gh ∧
        ∀ x, |gh x| ≤ R * ((V x).toReal + 1) := by
  have hε1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have := isMarkovKernel_resolvent P hε1
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hpet; exact h.1
  obtain ⟨hψK, hapK, C', hpetK, hdriftK⟩ :=
    resolvent_half_hypotheses hψ hf hf1 hpet hV hVfin hb hdrift
  have hV' : Measurable fun x => 4 * V x := hV.const_mul 4
  have hπV' : ∫⁻ x, 4 * V x ∂π ≠ ∞ := by
    rw [lintegral_const_mul _ hV]; exact ENNReal.mul_ne_top (by simp) hπV
  obtain ⟨R, hR0, hR⟩ := theorem_17_4_2 hψK hapK hf hf1 hpetK hV'
    (fun x => ENNReal.mul_ne_top (by simp) (hVfin x)) (ENNReal.mul_ne_top (by simp) hb) hdriftK
    (hπ.resolvent hε1) hπV'
  refine ⟨R * (4 * b.toReal + 5), mul_nonneg hR0 (by positivity), fun g hgm hgf => ?_⟩
  obtain ⟨hsolK, hghm, hbd⟩ := hR g hgm hgf
  exact exists_poisson_of_resolvent_half hV hf hCm hVfin hb hdrift hR0 hsolK hghm hbd

/-- **Theorem 17.7.1** (MT p. 459), general case: for a `ψ`-irreducible chain (periodic or not)
with (V3) for an everywhere finite `V`, `f ≥ 1` and a petite `C`, without `π(V) < ∞`, there is
`B < ∞` such that for every `|g| ≤ f` Poisson's equation `ĝ − Pĝ = g − π(g)` has a measurable
solution with `|ĝ| ≤ B (V + 1)`. As in the book, the aperiodic Theorem 17.7.1
(`theorem_17_7_1`) is applied to the resolvent `K_{a_{1/2}}`, and (17.42) gives `ĝ`. -/
theorem theorem_17_7_1_periodic {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x)
    {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C) (hV : Measurable V)
    (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g : X → ℝ, Measurable g → (∀ x, ENNReal.ofReal |g x| ≤ f x) →
      ∃ gh : X → ℝ, IsPoissonSolution P g gh (∫ y, g y ∂π) ∧ Measurable gh ∧
        ∀ x, |gh x| ≤ B * ((V x).toReal + 1) := by
  have hε1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have := isMarkovKernel_resolvent P hε1
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hpet; exact h.1
  obtain ⟨hψK, hapK, C', hpetK, hdriftK⟩ :=
    resolvent_half_hypotheses hψ hf hf1 hpet hV hVfin hb hdrift
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := π)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  obtain ⟨R, hR0, hR⟩ := theorem_17_7_1 hψK hapK hf hf1 hpetK (hV.const_mul 4)
    (fun x => ENNReal.mul_ne_top (by simp) (hVfin x)) (ENNReal.mul_ne_top (by simp) hb) hdriftK
    (hπ.resolvent hε1) x₀
  refine ⟨R * (4 * b.toReal + 5), mul_nonneg hR0 (by positivity), fun g hgm hgf => ?_⟩
  obtain ⟨hsolK, hghm, hbd⟩ := hR g hgm hgf
  exact exists_poisson_of_resolvent_half hV hf hCm hVfin hb hdrift hR0 hsolK hghm hbd

end MeynTweedie.LimitTheorems

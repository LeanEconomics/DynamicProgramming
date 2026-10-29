/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.UniformErgodic

/-!
# Geometric ergodicity and the structure of `π` (MT §16.3.2, Theorem 16.3.2)

Meyn and Tweedie, §16.3.2, pp. 410–411. `ψ` is a maximal irreducibility measure, the state space
is countably generated, and geometric ergodicity is (V4) for a petite set (Theorem 15.0.1 (iii)).

* `firstHit_le_firstReturn`: `σ_A ≤ τ_A`; `toENNReal_le_tpow`: `t ≤ (r − 1)⁻¹ rᵗ`.
* `ofReal_exp_meanHitTime_le`: **Jensen's inequality** for `σ_A`,
  `exp(β E_x[σ_A]) ≤ E_x[e^{βσ_A}]` with `e^β = r` (by the tangent line of the exponential at
  `E_x[σ_A]`).
* `exists_lintegral_tpow_firstHit_le`: under (V4) every `B ∈ B⁺(X)` has
  `E_x[r^{σ_B}] ≤ c V(x)` for some `r ∈ (1, 2]` (Theorem 15.3.3).
* **Theorem 16.3.2** (`theorem_16_3_2`, p. 410), (16.32): `∫ π(dy) e^{β V_B(y)} < ∞` for
  `V_B(y) = E_y[σ_B]` and some `β > 0`, for every `B ∈ B⁺(X)` (in particular for petite
  `C ∈ B⁺(X)`).
* `pow_skipFree`: if the chain is `g`-skip-free to the left (16.31) with `k ≥ 1`, then
  `Pʲ(x, {g ≤ g(x) − jk}) = 0`.
* **Theorem 16.3.2, (16.33)** (`theorem_16_3_2_skipFree`): for a `g`-skip-free chain,
  `∫ π(dy) e^{β' g(y)} < ∞` for some `β' > 0`.

**Hypotheses.** The book takes `B = C` petite in (16.32) and `g` unbounded off petite sets in
(16.33); neither is needed here: Theorem 15.3.3 bounds `E_x[r^{τ_B}]` by `c(B) V(x)` for every
`B ∈ B⁺(X)`, and some sublevel set `{g ≤ b}` is always in `B⁺(X)`.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- `σ_A ≤ τ_A`. -/
theorem firstHit_le_firstReturn (A : Set X) (ω : ℕ → X) : firstHit A ω ≤ firstReturn A ω := by
  by_cases h : ω 0 ∈ A
  · rw [(firstHit_eq_zero_iff A ω).2 h]; exact bot_le
  · rw [firstHit_eq_firstReturn A h]

/-- Bernoulli's inequality on `ℕ ∪ {∞}`: `t ≤ (r − 1)⁻¹ rᵗ` for `1 < r < ∞`. -/
theorem toENNReal_le_tpow {r : ℝ≥0∞} (hr : 1 < r) (hrt : r ≠ ∞) (t : WithTop ℕ) :
    ENat.toENNReal t ≤ (r - 1)⁻¹ * tpow r t := by
  have h0 : r - 1 ≠ 0 := (tsub_pos_of_lt hr).ne'
  have ht : r - 1 ≠ ∞ := ENNReal.sub_ne_top hrt
  cases t with
  | top =>
    rw [tpow_top, ENNReal.mul_top (ENNReal.inv_ne_zero.2 ht)]
    exact le_top
  | coe n =>
    rw [tpow_some, toENNReal_some n]
    calc (n : ℝ≥0∞) = (r - 1)⁻¹ * ((r - 1) * n) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
      _ ≤ (r - 1)⁻¹ * r ^ n := mul_le_mul' le_rfl (sub_one_mul_le_pow hr.le n)

/-- **Jensen's inequality for `σ_A`** (MT p. 410): `exp(β E_x[σ_A]) ≤ E_x[r^{σ_A}]` for
`1 < r < ∞`, `β = log r`. -/
theorem ofReal_exp_meanHitTime_le (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {r : ℝ≥0∞} (hr : 1 < r) (hrt : r ≠ ∞) (x : X) :
    ENNReal.ofReal (Real.exp (Real.log r.toReal * (meanHitTime P A x).toReal)) ≤
      ∫⁻ ω, tpow r (firstHit A ω) ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  set K := ∫⁻ ω, tpow r (firstHit A ω) ∂pathKernel P x with hK
  rcases eq_or_ne K ∞ with hKt | hKt
  · rw [hKt]; exact le_top
  have hσm : Measurable fun ω : ℕ → X => tpow r (firstHit A ω) :=
    measurable_tpow_comp (measurableSet_lt_firstHit hA) hr
  have hfin : ∀ᵐ ω ∂pathKernel P x, firstHit A ω ≠ ⊤ :=
    (ae_lt_top hσm hKt).mono fun ω hω h => by rw [h, tpow_top] at hω; exact lt_irrefl _ hω
  have hσe : Measurable fun ω : ℕ → X => ENat.toENNReal (firstHit A ω) :=
    measurable_toENNReal_firstHit hA
  have hmean : meanHitTime P A x ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2
      (tsub_pos_of_lt hr).ne') hKt) ?_
    rw [meanHitTime, ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne')]
    exact lintegral_mono fun ω => toENNReal_le_tpow hr hrt _
  set s := r.toReal with hs
  have hs1 : 1 < s := by rw [hs, ← ENNReal.toReal_one]; exact ENNReal.toReal_strict_mono hrt hr
  set β := Real.log s with hβ
  have hβ0 : 0 < β := Real.log_pos hs1
  set f : (ℕ → X) → ℝ := fun ω => (ENat.toENNReal (firstHit A ω)).toReal with hf
  have hfm : Measurable f := hσe.ennreal_toReal
  have hfint : Integrable f (pathKernel P x) := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    change ∫⁻ ω, ‖f ω‖ₑ ∂pathKernel P x < ∞
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) (lt_top_iff_ne_top.2 hmean)
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  set m := (meanHitTime P A x).toReal with hm
  have hfm' : ∫ ω, f ω ∂pathKernel P x = m := by
    rw [hf, integral_toReal hσe.aemeasurable (hfin.mono fun ω hω => by
      cases h : firstHit A ω with
      | top => exact absurd h hω
      | coe n => rw [toENNReal_some]; exact ENNReal.natCast_lt_top n), hm, meanHitTime]
  -- the tangent line at `m`
  set g : (ℕ → X) → ℝ := fun ω => max (Real.exp (β * m) * (1 + β * (f ω - m))) 0 with hg
  have hgle : ∀ ω, g ω ≤ Real.exp (β * f ω) := fun ω => by
    refine max_le ?_ (Real.exp_pos _).le
    have h := Real.add_one_le_exp (β * (f ω - m))
    have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos (β * m)).le
    rw [← Real.exp_add] at h2
    calc Real.exp (β * m) * (1 + β * (f ω - m)) = Real.exp (β * m) * (β * (f ω - m) + 1) := by
          ring
      _ ≤ Real.exp (β * m + β * (f ω - m)) := h2
      _ = Real.exp (β * f ω) := by ring_nf
  have hlin : Integrable (fun ω => Real.exp (β * m) * (1 + β * (f ω - m))) (pathKernel P x) :=
    ((integrable_const 1).add ((hfint.sub (integrable_const m)).const_mul β)).const_mul _
  have hgint : Integrable g (pathKernel P x) := hlin.sup (integrable_const 0)
  have hint_lin : ∫ ω, Real.exp (β * m) * (1 + β * (f ω - m)) ∂pathKernel P x =
      Real.exp (β * m) := by
    rw [integral_const_mul, integral_add (f := fun _ => (1 : ℝ)) (g := fun ω => β * (f ω - m))
      (integrable_const 1) ((hfint.sub (integrable_const m)).const_mul β), integral_const_mul,
      integral_sub (f := f) (g := fun _ => m) hfint (integrable_const m), hfm', integral_const,
      integral_const, probReal_univ, one_smul, one_smul, sub_self, mul_zero, add_zero, mul_one]
  calc ENNReal.ofReal (Real.exp (β * m))
      = ENNReal.ofReal (∫ ω, Real.exp (β * m) * (1 + β * (f ω - m)) ∂pathKernel P x) := by
        rw [hint_lin]
    _ ≤ ENNReal.ofReal (∫ ω, g ω ∂pathKernel P x) :=
        ENNReal.ofReal_le_ofReal (integral_mono hlin hgint fun ω => le_max_left _ _)
    _ = ∫⁻ ω, ENNReal.ofReal (g ω) ∂pathKernel P x :=
        ofReal_integral_eq_lintegral_ofReal hgint (Eventually.of_forall fun ω => le_max_right _ _)
    _ ≤ ∫⁻ ω, tpow r (firstHit A ω) ∂pathKernel P x := by
        refine lintegral_mono_ae (hfin.mono fun ω hω => ?_)
        refine (ENNReal.ofReal_le_ofReal (hgle ω)).trans (le_of_eq ?_)
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hω
        rw [hf]
        simp only
        rw [← hn, toENNReal_some, ENNReal.toReal_natCast, tpow_some, mul_comm,
          Real.exp_nat_mul, hβ, Real.exp_log (by linarith), ENNReal.ofReal_pow (by linarith),
          hs, ENNReal.ofReal_toReal hrt]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Geometric moments of hitting times** (from Theorem 15.3.3): under (V4) for a petite set,
every `B ∈ B⁺(X)` has `E_x[r^{σ_B}] ≤ c V(x)` for some `r ∈ (1, 2]`, `c < ∞`. -/
theorem exists_lintegral_tpow_firstHit_le {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    {x₀ : X} (hx₀ : V x₀ ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X}
    (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {B : Set X} (hB : MeasurableSet B)
    (hψB : 0 < ψ B) :
    ∃ r : ℝ≥0∞, 1 < r ∧ r ≤ 2 ∧ ∃ c : ℝ≥0∞, c ≠ ∞ ∧
      ∀ x, ∫⁻ ω, tpow r (firstHit B ω) ∂pathKernel P x ≤ c * V x := by
  obtain ⟨-, hreg⟩ := theorem_15_3_3 hψ hV hV1 hρ hb hC h hx₀
  obtain ⟨r, hr, c, hc, hbd⟩ := hreg B hB hψB
  refine ⟨min r 2, lt_min hr ENNReal.one_lt_two, min_le_right _ _, c, hc, fun x => ?_⟩
  calc ∫⁻ ω, tpow (min r 2) (firstHit B ω) ∂pathKernel P x
      ≤ kendallMoment P B (min r 2) x :=
        lintegral_mono fun ω => tpow_mono (le_min hr.le one_le_two) (firstHit_le_firstReturn B ω)
    _ ≤ geomTaboo P B (min r 2) V x :=
        kendallMoment_le_geomTaboo P B (le_min hr.le one_le_two) hV1 x
    _ ≤ geomTaboo P B r V x := geomTaboo_mono_r P B (min_le_left _ _) V x
    _ ≤ c * V x := hbd x

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 16.3.2, (16.32)** (MT p. 410): if `Φ` is geometrically ergodic, (V4) holding for a
petite set and a `V` finite somewhere, then for every invariant probability `π` and every
`B ∈ B⁺(X)` (in particular every petite `C ∈ B⁺(X)`), `V_B(y) = E_y[σ_B]` is `π`-a.e. finite
and `∫ π(dy) e^{β V_B(y)} < ∞` for some `β > 0`. -/
theorem theorem_16_3_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) {x₀ : X} (hx₀ : V x₀ ≠ ∞) {ρ b : ℝ≥0∞}
    (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C)
    (μ : Measure X) [IsProbabilityMeasure μ] (hμ : IsInvariant P μ) {B : Set X}
    (hB : MeasurableSet B) (hψB : 0 < ψ B) :
    ∃ β : ℝ, 0 < β ∧ (∀ᵐ x ∂μ, meanHitTime P B x ≠ ∞) ∧
      ∫⁻ x, ENNReal.ofReal (Real.exp (β * (meanHitTime P B x).toReal)) ∂μ ≠ ∞ := by
  obtain ⟨-, hgeo⟩ := geometric_ergodic_of_driftV4 hψ hap hV hV1 hρ hb hC h hx₀
  have hμV := (hgeo μ hμ).1
  obtain ⟨r, hr, hr2, c, hc, hbd⟩ :=
    exists_lintegral_tpow_firstHit_le hψ hV hV1 hx₀ hρ hb hC h hB hψB
  have hrt : r ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hr2
  have hs1 : 1 < r.toReal := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_strict_mono hrt hr
  refine ⟨Real.log r.toReal, Real.log_pos hs1, ?_, ?_⟩
  · have hVae : ∀ᵐ x ∂μ, V x < ∞ := ae_lt_top hV hμV
    refine hVae.mono fun x hx => ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2
      (tsub_pos_of_lt hr).ne') (ENNReal.mul_ne_top hc hx.ne)) ?_
    calc meanHitTime P B x
        ≤ ∫⁻ ω, (r - 1)⁻¹ * tpow r (firstHit B ω) ∂pathKernel P x :=
          lintegral_mono fun ω => toENNReal_le_tpow hr hrt _
      _ = (r - 1)⁻¹ * ∫⁻ ω, tpow r (firstHit B ω) ∂pathKernel P x :=
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne')
      _ ≤ (r - 1)⁻¹ * (c * V x) := mul_le_mul' le_rfl (hbd x)
  · refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hc hμV) ?_
    rw [← lintegral_const_mul _ hV]
    exact lintegral_mono fun x =>
      (ofReal_exp_meanHitTime_le P hB hr hrt x).trans (hbd x)

/-! ### The skip-free case -/

/-- **Skip-free chains** (16.31): if `P(x, {g ≤ g(x) − k}) = 0` for every `x`, then
`Pʲ(x, {g ≤ g(x) − jk}) = 0` for every `j ≥ 1`. -/
theorem pow_skipFree {P : Kernel X X} [IsMarkovKernel P] {g : X → ℝ} (hg : Measurable g)
    {k : ℕ} (hskip : ∀ x, P x {y | g y ≤ g x - k} = 0) (j : ℕ) (x : X) :
    (P ^ (j + 1)) x {y | g y ≤ g x - (j + 1 : ℕ) * k} = 0 := by
  induction j with
  | zero => simpa using hskip x
  | succ j ih =>
    have hm : MeasurableSet {y | g y ≤ g x - ((j + 1 + 1 : ℕ) : ℝ) * k} :=
      measurableSet_le hg measurable_const
    rw [pow_succ_apply' P (j + 1) x hm]
    refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ hm)).2 ?_
    have hae : ∀ᵐ y ∂(P ^ (j + 1)) x, g x - ((j + 1 : ℕ) : ℝ) * k < g y := by
      rw [ae_iff]
      refine measure_mono_null (fun y hy => ?_) ih
      simpa using hy
    filter_upwards [hae] with y hy
    refine measure_mono_null (fun z hz => ?_) (hskip y)
    simp only [mem_ofPred_eq] at hz ⊢
    push_cast at hz hy
    linarith

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 16.3.2, (16.33)** (MT p. 410): if `Φ` is geometrically ergodic and `g`-skip-free to
the left (16.31), `P(x, {g ≤ g(x) − k}) = 0`, `k ≥ 1`, then `∫ π(dy) e^{β' g(y)} < ∞` for some
`β' > 0`, for every invariant probability `π`. -/
theorem theorem_16_3_2_skipFree {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) {x₀ : X} (hx₀ : V x₀ ≠ ∞) {ρ b : ℝ≥0∞}
    (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C)
    (μ : Measure X) [IsProbabilityMeasure μ] (hμ : IsInvariant P μ) {g : X → ℝ}
    (hg : Measurable g) {k : ℕ} (hk : 0 < k) (hskip : ∀ x, P x {y | g y ≤ g x - k} = 0) :
    ∃ β : ℝ, 0 < β ∧ ∫⁻ x, ENNReal.ofReal (Real.exp (β * g x)) ∂μ ≠ ∞ := by
  obtain ⟨-, hgeo⟩ := geometric_ergodic_of_driftV4 hψ hap hV hV1 hρ hb hC h hx₀
  have hμV := (hgeo μ hμ).1
  -- a sublevel set `{g ≤ b₀}` in `B⁺(X)`
  have hψu : ψ univ ≠ 0 := fun h0 => hψ.1 (Measure.measure_univ_eq_zero.1 h0)
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ℕ, ψ {y | g y ≤ b₀} ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hψu
    have hcov : (univ : Set X) = ⋃ n : ℕ, {y | g y ≤ n} := by
      ext y
      simp only [mem_univ, mem_iUnion, mem_ofPred_eq, true_iff]
      obtain ⟨n, hn⟩ := exists_nat_ge (g y)
      exact ⟨n, hn⟩
    rw [hcov]
    exact measure_iUnion_null hall
  set D := {y | g y ≤ (b₀ : ℝ)} with hD
  have hDm : MeasurableSet D := measurableSet_le hg measurable_const
  obtain ⟨r, hr, hr2, c, hc, hbd⟩ :=
    exists_lintegral_tpow_firstHit_le hψ hV hV1 hx₀ hρ hb hC h hDm (pos_iff_ne_zero.2 hb₀)
  have hrt : r ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hr2
  set s := r.toReal with hs
  have hs1 : 1 < s := by rw [hs, ← ENNReal.toReal_one]; exact ENNReal.toReal_strict_mono hrt hr
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set β := Real.log s / k with hβ
  have hβ0 : 0 < β := div_pos (Real.log_pos hs1) hkpos
  -- the pointwise bound `e^{β(g(x) − b₀)} ≤ 1 + E_x[r^{σ_D}]`
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (β * (g x - b₀))) ≤
      1 + ∫⁻ ω, tpow r (firstHit D ω) ∂pathKernel P x := fun x => by
    have := isMarkovKernel_pathKernel P
    rcases le_or_gt (g x) b₀ with hlt | hge
    · refine le_add_right ?_
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2
        (mul_nonpos_of_nonneg_of_nonpos hβ0.le (by linarith)))
    refine le_add_left ?_
    set n := ⌊(g x - b₀) / k⌋₊ with hn
    have hnk : (n : ℝ) * k ≤ g x - b₀ :=
      (le_div_iff₀ hkpos).1 (Nat.floor_le (div_nonneg (by linarith) hkpos.le))
    -- no visit to `D` before time `n + 1`
    have hnull : ∀ j ≤ n, (P ^ j) x D = 0 := fun j hj => by
      rcases Nat.eq_zero_or_eq_succ_pred j with h0 | hj1
      · rw [h0, pow_zero_apply, Measure.dirac_apply' _ hDm, indicator_of_notMem]
        simp only [hD, mem_ofPred_eq, not_le]; exact hge
      rw [hj1]
      refine measure_mono_null (fun y hy => ?_) (pow_skipFree hg hskip (j.pred) x)
      simp only [hD, mem_ofPred_eq] at hy ⊢
      have hjn : j.pred + 1 ≤ n := by
        change j.pred.succ ≤ n
        rw [← hj1]; exact hj
      have hj' : ((j.pred + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hjn
      have : ((j.pred + 1 : ℕ) : ℝ) * k ≤ n * k := mul_le_mul_of_nonneg_right hj' hkpos.le
      linarith
    have hσ : ∀ᵐ ω ∂pathKernel P x, ((n + 1 : ℕ) : WithTop ℕ) ≤ firstHit D ω := by
      have hbad : pathKernel P x (⋃ j ∈ Finset.range (n + 1), {ω : ℕ → X | ω j ∈ D}) = 0 :=
        measure_biUnion_null_iff (Finset.range (n + 1)).countable_toSet |>.2 fun j hj => by
          rw [pathKernel_coord_mem P x j hDm]
          exact hnull j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) hbad
      simp only [mem_ofPred_eq, not_le] at hω
      have hne : firstHit D ω ≠ ⊤ := ne_top_of_lt hω
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hne
      have hmem := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := D)
        (n := 0) (ω := ω) hne
      rw [← firstHit, ← hm] at hmem
      rw [← hm] at hω
      have hmn : m < n + 1 := WithTop.coe_lt_coe.mp hω
      simp only [mem_iUnion, Finset.mem_range, mem_ofPred_eq]
      exact ⟨m, hmn, hmem⟩
    calc ENNReal.ofReal (Real.exp (β * (g x - b₀))) ≤ ENNReal.ofReal (s ^ (n + 1)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Real.exp_log (show 0 < s by linarith), ← Real.exp_nat_mul]
          refine Real.exp_le_exp.2 ?_
          have h1 : (g x - b₀) / k < n + 1 := Nat.lt_floor_add_one _
          have h2 : β * (g x - b₀) = Real.log s * ((g x - b₀) / k) := by
            rw [hβ]; field_simp
          rw [h2]
          push_cast
          nlinarith [Real.log_pos hs1]
      _ = r ^ (n + 1) := by rw [ENNReal.ofReal_pow (by linarith), hs, ENNReal.ofReal_toReal hrt]
      _ ≤ ∫⁻ ω, tpow r (firstHit D ω) ∂pathKernel P x := by
          calc r ^ (n + 1) = ∫⁻ _ω, r ^ (n + 1) ∂pathKernel P x := by
                rw [lintegral_const, measure_univ, mul_one]
            _ ≤ ∫⁻ ω, tpow r (firstHit D ω) ∂pathKernel P x :=
                lintegral_mono_ae (hσ.mono fun ω hω => by
                  rw [← tpow_coe]; exact tpow_mono hr.le hω)
  refine ⟨β, hβ0, ?_⟩
  have hsplit : ∀ x, ENNReal.ofReal (Real.exp (β * g x)) =
      ENNReal.ofReal (Real.exp (β * b₀)) * ENNReal.ofReal (Real.exp (β * (g x - b₀))) :=
    fun x => by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; ring_nf
  simp_rw [hsplit]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ?_ (lintegral_mono hpt))
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hc hμV) ?_⟩
  rw [← lintegral_const_mul _ hV]
  exact lintegral_mono hbd

end MeynTweedie.VUniformErgodicity

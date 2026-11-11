/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.INExercises
import Applications.INMPStrong
import Mathlib.Probability.Independence.Basic

/-!
# The inventory process under the (s, S) policy: Exercise 8.5

Miao, §8.5, p. 275, and Exercise 5, p. 288 ("Section 8.4" there is a misprint for §8.5).
Under the (s, S) policy the stocks follow `x_{t+1} = x_t − z_{t+1}` if `s < x_t` and
`x_{t+1} = S − z_{t+1}` if `x_t ≤ s`, i.e. `x_{t+1} = y(x_t) − z_{t+1}` with
`y = in_ssPolicy s S`.

* `in_invKernel φ s S`: the transition function `P(x, A) = φ{z : y(x) − z ∈ A}`
  (`ex_8_5_transition`); it is a Markov kernel (`in_invKernel_isMarkov`).
* `ex_8_5_markov`: the Markov property: if the history `W` (e.g. `(x_0, …, x_t)`) is
  independent of the next demand `Z` with law `φ`, then
  `P(W ∈ B, y(x_t) − Z ∈ A) = ∫_{W ∈ B} P(x_t, A) dP`.
* `ex_8_5_absorbing`: `(−∞, S]` is absorbing; `in_invKernelX` is the chain on
  `in_Stock S = (−∞, S]` (`ex_8_5_transitionX`).
* `ex_8_5_minorization`: if `θ = φ(z > S − s) > 0`, then `P²(x, ·) ≥ θ ν` on `(−∞, S]`
  with `ν` the law of `S − z` (two large demands in a row are not needed: one demand above
  `S − s` forces an order).
* **Exercise 8.5** (`ex_8_5`): under `θ > 0` the chain on `(−∞, S]` has a unique stationary
  distribution `π`, and `dTV(λ₀Pⁿ, π) ≤ (1 − θ/2)^⌊n/2⌋` (Condition M and **Theorem 3.3.1**,
  as the book suggests on p. 276).
* `ex_8_5_counterexample`: without a condition on the demand the stationary distribution need
  not be unique: for `z ≡ 0` and `s < S` both `δ_S` and `δ_{(s+S)/2}` are stationary.

**Departures.** (1) The exercise claims uniqueness unconditionally; it is false for degenerate
demand (above), and we prove it under `φ(z > S − s) > 0`. (2) We work on the absorbing set
`(−∞, S]`, where the chain started from any `x₀ ≤ S` lives (stocks above `S` only occur
initially and are not ordered back up to). (3) The transition function on `(−∞, S]` uses
`min(y(x) − z, S)`, equal to `y(x) − z` for almost every `z ≥ 0`.
-/

namespace Miao.Applications

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- The order-up-to rule `y = in_ssPolicy s S` is measurable. -/
theorem in_ssPolicy_measurable (s S : ℝ) : Measurable (in_ssPolicy s S) := by
  unfold in_ssPolicy
  exact Measurable.ite measurableSet_Iic measurable_const measurable_id

/-- The transition function of the inventory process under the (s, S) policy (Miao,
Exercise 8.5): `P(x, ·)` is the law of `y(x) − z`, `z ∼ φ`. -/
noncomputable def in_invKernel (φ : Measure ℝ) [IsProbabilityMeasure φ] (s S : ℝ) :
    Kernel ℝ ℝ where
  toFun x := φ.map (fun z => in_ssPolicy s S x - z)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have hE : MeasurableSet {p : ℝ × ℝ | in_ssPolicy s S p.1 - p.2 ∈ A} :=
      (((in_ssPolicy_measurable s S).comp measurable_fst).sub measurable_snd) hA
    have : (fun x => (φ.map (fun z => in_ssPolicy s S x - z)) A) =
        fun x => φ (Prod.mk x ⁻¹' {p : ℝ × ℝ | in_ssPolicy s S p.1 - p.2 ∈ A}) := by
      funext x
      have hm : Measurable fun z : ℝ => in_ssPolicy s S x - z := measurable_const.sub measurable_id
      rw [Measure.map_apply hm hA]
      rfl
    rw [this]
    exact measurable_measure_prodMk_left hE

/-- **Exercise 8.5** (Miao, p. 288), the transition function:
`P(x, A) = φ{z : S − z ∈ A}` for `x ≤ s` and `P(x, A) = φ{z : x − z ∈ A}` for `x > s`. -/
theorem ex_8_5_transition (φ : Measure ℝ) [IsProbabilityMeasure φ] (s S x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    in_invKernel φ s S x A = φ {z | in_ssPolicy s S x - z ∈ A} ∧
      (x ≤ s → in_invKernel φ s S x A = φ {z | S - z ∈ A}) ∧
      (s < x → in_invKernel φ s S x A = φ {z | x - z ∈ A}) := by
  have h : in_invKernel φ s S x A = φ {z | in_ssPolicy s S x - z ∈ A} := by
    change (φ.map _) A = _
    have hm : Measurable fun z : ℝ => in_ssPolicy s S x - z := measurable_const.sub measurable_id
    rw [Measure.map_apply hm hA]
    rfl
  refine ⟨h, fun hx => ?_, fun hx => ?_⟩
  · rw [h]; unfold in_ssPolicy; simp only [hx, ↓reduceIte]
  · rw [h]; unfold in_ssPolicy; simp only [not_le.2 hx, ↓reduceIte]

/-- The transition function is a Markov kernel. -/
theorem in_invKernel_isMarkov (φ : Measure ℝ) [IsProbabilityMeasure φ] (s S : ℝ) :
    IsMarkovKernel (in_invKernel φ s S) :=
  ⟨fun x => by change IsProbabilityMeasure (φ.map _); infer_instance⟩

/-- **Exercise 8.5** (Miao, p. 288), the Markov property: let the history `W` (for instance
`(x_0, …, x_t)`, a function of `x_0, z_1, …, z_t`) be independent of the next demand `Z` with
law `φ`, and `x_t = X(W)`. Then `x_{t+1} = y(x_t) − Z` satisfies
`P(W ∈ B, x_{t+1} ∈ A) = ∫_{W ∈ B} P(x_t, A) dP`: given the past, `x_{t+1}` has law
`P(x_t, ·)`. -/
theorem ex_8_5_markov (φ : Measure ℝ) [IsProbabilityMeasure φ] (s S : ℝ) {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → E} {X : E → ℝ} {Z : Ω → ℝ} (hW : Measurable W) (hX : Measurable X)
    (hZ : Measurable Z) (hind : IndepFun W Z P) (hlaw : P.map Z = φ) {B : Set E} {A : Set ℝ}
    (hB : MeasurableSet B) (hA : MeasurableSet A) :
    P {ω | W ω ∈ B ∧ in_ssPolicy s S (X (W ω)) - Z ω ∈ A} =
      ∫⁻ ω in W ⁻¹' B, in_invKernel φ s S (X (W ω)) A ∂P := by
  set E' : Set (E × ℝ) := {p | p.1 ∈ B ∧ in_ssPolicy s S (X p.1) - p.2 ∈ A}
  have hE' : MeasurableSet E' :=
    (measurable_fst hB).inter
      ((((in_ssPolicy_measurable s S).comp (hX.comp measurable_fst)).sub measurable_snd) hA)
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hZ.aemeasurable).1 hind
  have h1 : P {ω | W ω ∈ B ∧ in_ssPolicy s S (X (W ω)) - Z ω ∈ A} =
      (P.map fun ω => (W ω, Z ω)) E' := by
    rw [Measure.map_apply (hW.prodMk hZ) hE']
    rfl
  rw [h1, hprod, hlaw, Measure.prod_apply hE']
  have h2 : (fun w => φ (Prod.mk w ⁻¹' E')) =
      B.indicator fun w => in_invKernel φ s S (X w) A := by
    funext w
    by_cases hw : w ∈ B
    · rw [Set.indicator_of_mem hw, (ex_8_5_transition φ s S (X w) hA).1]
      congr 1
      ext z
      simp [E', hw]
    · rw [Set.indicator_of_notMem hw]
      have : Prod.mk w ⁻¹' E' = ∅ := by ext z; simp [E', hw]
      rw [this, measure_empty]
  have hf : Measurable fun w => in_invKernel φ s S (X w) A :=
    (Kernel.measurable_coe _ hA).comp hX
  rw [h2, lintegral_indicator hB, setLIntegral_map hB hf hW]

/-- The absorbing set `(−∞, S]`: from `x ≤ S` the next stock is `≤ S` almost surely. -/
theorem ex_8_5_absorbing (φ : Measure ℝ) [IsProbabilityMeasure φ] (hz : ∀ᵐ z ∂φ, 0 ≤ z)
    {s S x : ℝ} (hx : x ≤ S) : in_invKernel φ s S x (Set.Iic S) = 1 := by
  rw [(ex_8_5_transition φ s S x measurableSet_Iic).1]
  have hy : in_ssPolicy s S x ≤ S := by
    unfold in_ssPolicy; split_ifs
    · exact le_rfl
    · exact hx
  have : {z | in_ssPolicy s S x - z ∈ Set.Iic S} =ᵐ[φ] (Set.univ : Set ℝ) := by
    filter_upwards [hz] with z hz'
    simp only [Set.mem_Iic, Set.mem_univ, eq_iff_iff, iff_true]
    linarith
  rw [measure_congr this, measure_univ]

/-- The state space `(−∞, S]` of the inventory chain. -/
abbrev in_Stock (S : ℝ) := {x : ℝ // x ≤ S}

/-- The next stock on `(−∞, S]`: `min(y(x) − z, S)`. -/
noncomputable def in_nextX (s S x z : ℝ) : in_Stock S :=
  ⟨min (in_ssPolicy s S x - z) S, min_le_right _ _⟩

theorem in_nextX_measurable (s S : ℝ) :
    Measurable fun p : in_Stock S × ℝ => in_nextX s S p.1.1 p.2 :=
  ((((in_ssPolicy_measurable s S).comp (measurable_subtype_coe.comp measurable_fst)).sub
    measurable_snd).min measurable_const).subtype_mk

theorem in_nextX_measurable_right (s S x : ℝ) : Measurable (in_nextX s S x) :=
  ((measurable_const.sub measurable_id).min measurable_const).subtype_mk

/-- The transition function on `(−∞, S]`. -/
noncomputable def in_invKernelX (φ : Measure ℝ) [IsProbabilityMeasure φ] (s S : ℝ) :
    Kernel (in_Stock S) (in_Stock S) where
  toFun x := φ.map (in_nextX s S x.1)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have hE : MeasurableSet {p : in_Stock S × ℝ | in_nextX s S p.1.1 p.2 ∈ A} :=
      in_nextX_measurable s S hA
    have : (fun x : in_Stock S => (φ.map (in_nextX s S x.1)) A) =
        fun x => φ (Prod.mk x ⁻¹' {p : in_Stock S × ℝ | in_nextX s S p.1.1 p.2 ∈ A}) := by
      funext x
      rw [Measure.map_apply (in_nextX_measurable_right s S x.1) hA]
      rfl
    rw [this]
    exact measurable_measure_prodMk_left hE

/-- The chain on `(−∞, S]` is a Markov kernel. -/
theorem in_invKernelX_isMarkov (φ : Measure ℝ) [IsProbabilityMeasure φ] (s S : ℝ) :
    IsMarkovKernel (in_invKernelX φ s S) :=
  ⟨fun x => by change IsProbabilityMeasure (φ.map _); infer_instance⟩

/-- **Exercise 8.5**: the transition function on `(−∞, S]`; for `z ≥ 0` the next stock is
`y(x) − z`. -/
theorem ex_8_5_transitionX (φ : Measure ℝ) [IsProbabilityMeasure φ] (hz : ∀ᵐ z ∂φ, 0 ≤ z)
    (s S : ℝ) (x : in_Stock S) {A : Set (in_Stock S)} (hA : MeasurableSet A) :
    in_invKernelX φ s S x A = φ {z | in_nextX s S x z ∈ A} ∧
      ∀ᵐ z ∂φ, (in_nextX s S x z : ℝ) = in_ssPolicy s S x - z := by
  refine ⟨?_, ?_⟩
  · change (φ.map _) A = _
    rw [Measure.map_apply (in_nextX_measurable_right s S x.1) hA]
    rfl
  · have hy : in_ssPolicy s S x ≤ S := by
      unfold in_ssPolicy; split_ifs
      · exact le_rfl
      · exact x.2
    filter_upwards [hz] with z hz'
    exact min_eq_left (by linarith)

theorem in_ssPolicy_self (s S : ℝ) : in_ssPolicy s S s = S := by simp [in_ssPolicy]

/-- A demand above `S − s` forces an order next period. -/
theorem in_nextX_reset {s S : ℝ} (x : in_Stock S) {z : ℝ} (hz : S - s < z) :
    in_ssPolicy s S (in_nextX s S x z) = S := by
  have hy : in_ssPolicy s S x ≤ S := by
    unfold in_ssPolicy; split_ifs
    · exact le_rfl
    · exact x.2
  have h : ((in_nextX s S x z : in_Stock S) : ℝ) ≤ s :=
    (min_le_left _ _).trans (by linarith)
  unfold in_ssPolicy
  simp only [h, ↓reduceIte]

/-- After a forced order, the next stock has the law `ν` of `S − z`. -/
theorem in_kernelX_reset (φ : Measure ℝ) [IsProbabilityMeasure φ] {s S : ℝ} (y : in_Stock S)
    (hy : in_ssPolicy s S y = S) : in_invKernelX φ s S y = φ.map (in_nextX s S s) := by
  change φ.map (in_nextX s S y.1) = _
  congr 1
  funext z
  apply Subtype.ext
  change min (in_ssPolicy s S y - z) S = min (in_ssPolicy s S s - z) S
  rw [hy, in_ssPolicy_self]

/-- **Exercise 8.5**, the minorization condition: with `θ = φ(z > S − s)`,
`P²(x, A) ≥ θ ν(A)` on `(−∞, S]`, `ν` the law of `S − z`. -/
theorem ex_8_5_minorization (φ : Measure ℝ) [IsProbabilityMeasure φ] {s S : ℝ}
    (hθ : 0 < φ.real {z | S - s < z}) :
    MinorizationFor (in_invKernelX φ s S) 2 (φ.real {z | S - s < z})
      (φ.map (in_nextX s S s)) := by
  have hK := in_invKernelX_isMarkov φ s S
  refine ⟨by norm_num, hθ, by infer_instance, fun x A hA => ?_⟩
  set κ := in_invKernelX φ s S
  set E := {z : ℝ | S - s < z}
  have hEm : MeasurableSet E := measurableSet_Ioi
  have key : (φ.map (in_nextX s S s)) A * φ E ≤ kpow κ 2 x A := by
    have e2 : kpow κ 2 = kpow κ 1 ∘ₖ κ := rfl
    rw [e2, gp_kpow_one, Kernel.comp_apply' _ _ _ hA]
    change _ ≤ ∫⁻ y, κ y A ∂(φ.map (in_nextX s S x.1))
    rw [lintegral_map (Kernel.measurable_coe _ hA) (in_nextX_measurable_right s S x.1),
      ← setLIntegral_const]
    calc ∫⁻ _ in E, (φ.map (in_nextX s S s)) A ∂φ
        = ∫⁻ z in E, κ (in_nextX s S x.1 z) A ∂φ := by
          refine setLIntegral_congr_fun hEm fun z hz => ?_
          rw [in_kernelX_reset φ _ (in_nextX_reset x hz)]
      _ ≤ ∫⁻ z, κ (in_nextX s S x.1 z) A ∂φ := setLIntegral_le_lintegral _ _
  have hk2 := gp_isMarkov_kpow (κ := κ) 2
  have := ENNReal.toReal_mono (measure_ne_top _ _) key
  rw [ENNReal.toReal_mul] at this
  rw [measureReal_def, measureReal_def, measureReal_def]
  linarith

/-- **Exercise 8.5** (Miao, p. 288). If demand exceeds `S − s` with positive probability, the
inventory chain on `(−∞, S]` under the (s, S) policy has a unique stationary distribution `π`,
and `dTV(λ₀Pⁿ, π) ≤ (1 − θ/2)^⌊n/2⌋` for every initial distribution `λ₀` (Condition M,
**Theorem 3.3.1**). -/
theorem ex_8_5 (φ : Measure ℝ) [IsProbabilityMeasure φ] {s S : ℝ}
    (hθ : 0 < φ.real {z | S - s < z}) :
    ∃! pm : Measure (in_Stock S), IsProbabilityMeasure pm ∧
      adjointOp (in_invKernelX φ s S) pm = pm ∧
      ∀ (l₀ : Measure (in_Stock S)) [IsProbabilityMeasure l₀] (n : ℕ),
        dTV (adjointOp (kpow (in_invKernelX φ s S) n) l₀) pm ≤
          (1 - φ.real {z | S - s < z} / 2) ^ (n / 2) := by
  have hK := in_invKernelX_isMarkov φ s S
  set κ := in_invKernelX φ s S
  set θ := φ.real {z | S - s < z}
  have hM := proposition_3_3_1_forward (ex_8_5_minorization φ hθ)
  have : Nonempty (in_Stock S) := ⟨⟨S, le_rfl⟩⟩
  obtain ⟨pm, hpm, hinv, -, hrate⟩ := theorem_3_3_1_invariant hM
  refine ⟨pm, ⟨hpm, hinv, hrate⟩, ?_⟩
  rintro pm' ⟨hpm', hinv', -⟩
  have hθ1 : θ ≤ 1 := measureReal_le_one
  have hfix : ∀ n, adjointOp (kpow κ n) pm' = pm' := fun n => by
    rw [← gp_adjointOp_iterate]
    exact Function.iterate_fixed hinv' n
  have hd : ∀ k : ℕ, dTV pm' pm ≤ (1 - θ / 2) ^ k := fun k => by
    have := hrate pm' (2 * k)
    rwa [hfix, Nat.mul_div_cancel_left _ (by norm_num)] at this
  have ht : Tendsto (fun k : ℕ => (1 - θ / 2) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have h0 : dTV pm' pm ≤ 0 := ge_of_tendsto' ht hd
  ext A hA
  have h1 := (gp_abs_le_dTV pm' pm hA).trans h0
  have h2 : pm'.real A = pm.real A := by
    have := abs_nonneg (pm'.real A - pm.real A)
    have : |pm'.real A - pm.real A| = 0 := le_antisymm h1 this
    linarith [abs_eq_zero.1 this]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h2

/-- **Exercise 8.5 needs a condition on demand** (Miao, p. 288): with no demand (`z ≡ 0`) and
`s < S`, both `δ_S` and `δ_{(s+S)/2}` are stationary for the inventory chain, so the
stationary distribution is not unique. -/
theorem ex_8_5_counterexample {s S : ℝ} (hsS : s < S) :
    adjointOp (in_invKernelX (Measure.dirac 0) s S) (Measure.dirac ⟨S, le_rfl⟩) =
        Measure.dirac ⟨S, le_rfl⟩ ∧
      adjointOp (in_invKernelX (Measure.dirac 0) s S)
          (Measure.dirac ⟨(s + S) / 2, by linarith⟩) =
        Measure.dirac ⟨(s + S) / 2, by linarith⟩ ∧
      (Measure.dirac (⟨S, le_rfl⟩ : in_Stock S)) ≠ Measure.dirac ⟨(s + S) / 2, by linarith⟩ := by
  have hfix : ∀ x : in_Stock S, s < x.1 →
      adjointOp (in_invKernelX (Measure.dirac 0) s S) (Measure.dirac x) = Measure.dirac x := by
    intro x hx
    change (Measure.dirac x).bind _ = _
    rw [Measure.dirac_bind (Kernel.measurable _)]
    change (Measure.dirac 0).map (in_nextX s S x.1) = _
    rw [Measure.map_dirac' (in_nextX_measurable_right s S x.1)]
    congr 1
    apply Subtype.ext
    simp only [in_nextX, in_ssPolicy, not_le.2 hx, ↓reduceIte, sub_zero]
    exact min_eq_left x.2
  refine ⟨hfix _ hsS, hfix _ (by simp only; linarith), fun h => ?_⟩
  have hm : MeasurableSet {x : in_Stock S | x.1 = S} :=
    measurable_subtype_coe (measurableSet_singleton S)
  have := congrArg (fun μ : Measure (in_Stock S) => μ {x | x.1 = S}) h
  simp only [Measure.dirac_apply' _ hm, Set.indicator, Set.mem_ofPred_eq] at this
  have hne : ¬ ((s + S) / 2 = S) := by intro h'; linarith
  simp [hne] at this

end Miao.Applications

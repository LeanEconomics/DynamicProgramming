/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDP.PolicyKernels

/-!
# Exercise 9.16: the endogenous state need not be a Markov process

SLP §9.6, p. 286. `X = [0, 1]`, `Z = {0, 1}` with `Q(0, 0) = Q(1, 1) = 0.9`, and
`g(x, z) = θx + (1 − θ)z`. The book asks to show that `x_t` is not a first-order Markov process:
`Pr(x_{t+1} ∈ A | x_t, x_{t−1}) ≠ Pr(x_{t+1} ∈ A | x_t)`.

The Markov property of `x` is stated as a factorization of the joint law (as in Chapter 8): the
law of `(x_t, x_{t+1}, x_{t+2})` is the law of `(x_t, x_{t+1})` followed by a transition function
`R(x_{t+1}, ·)` (`IsMarkovAt`). The shocks are `z₀` (given) and the history `(z₁, …, z_t)`;
`x_t = xP t` uses `z₀, …, z_{t−1}`.

**Correction.** The claim depends on `θ`:

* for `θ < 1/2` it is false (`ex_9_16_markov`): `x_{t+1} = θx_t + (1 − θ)z_t` lies in `[0, θ]`
  when `z_t = 0` and in `[1 − θ, 1]` when `z_t = 1`, so `z_t = 1{x_{t+1} ≥ 1 − θ}` and `x` is a
  Markov process, with `R(y, ·)` the law of `θy + (1 − θ)z′`, `z′ ~ Q(1{y ≥ 1 − θ}, ·)`;
* for `θ = (√5 − 1)/2` it is true (`ex_9_16`): from `x₀ = 0`, `z₀ = 0`, the shock histories
  `(1, 1, 0)` and `(0, 0, 1)` both give `x₄ = 1 − θ` (as `θ² + θ = 1`) but differ in `x₃` and in
  `z₃`, so `Pr(x₅ = θ(1 − θ) | x₃, x₄)` is `0.9` on one and `0.1` on the other, and no `R` exists.
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- `Q(z, ·)`: stay with probability `0.9`, switch with probability `0.1`. -/
noncomputable def flipMeasure (b : Bool) : Measure Bool :=
  (9 / 10 : ℝ≥0∞) • Measure.dirac b + (1 / 10 : ℝ≥0∞) • Measure.dirac (!b)

/-- The transition function of the two-state shock. -/
noncomputable def flipKernel : Kernel Bool Bool := Kernel.ofFunOfCountable flipMeasure

theorem flipKernel_apply (b : Bool) : flipKernel b = flipMeasure b := rfl

theorem isMarkovKernel_flipKernel : IsMarkovKernel flipKernel :=
  ⟨fun b => ⟨by
    rw [flipKernel_apply, flipMeasure]
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.add_div]
    norm_num [ENNReal.div_self]⟩⟩

theorem flipKernel_singleton (b c : Bool) :
    flipKernel b {c} = if c = b then 9 / 10 else 1 / 10 := by
  rw [flipKernel_apply, flipMeasure]
  cases b <;> cases c <;> simp

/-- The value of a shock, `0` or `1`. -/
def bv (z : Bool) : ℝ := if z then 1 else 0

theorem measurable_bv : Measurable bv := measurable_of_countable _

/-- `x_t` along the shock history: `x₀` given, `x_{t+1} = θx_t + (1 − θ)z_t`. -/
noncomputable def xP (θ x₀ : ℝ) (z₀ : Bool) : (t : ℕ) → (Fin t → Bool) → ℝ
  | 0, _ => x₀
  | t + 1, h => θ * xP θ x₀ z₀ t (Fin.init h) + (1 - θ) * bv (lastState z₀ (Fin.init h))

theorem measurable_xP (θ x₀ : ℝ) (z₀ : Bool) (t : ℕ) : Measurable (xP θ x₀ z₀ t) :=
  measurable_of_countable _

/-- `x_{t+1}` as a function of the history `(z₁, …, z_t)`. -/
noncomputable def xNext (θ x₀ : ℝ) (z₀ : Bool) (t : ℕ) (h : Fin t → Bool) : ℝ :=
  θ * xP θ x₀ z₀ t h + (1 - θ) * bv (lastState z₀ h)

/-- `(x_t, x_{t+1})` as a function of `(z₁, …, z_t)`. -/
noncomputable def xPair (θ x₀ : ℝ) (z₀ : Bool) (t : ℕ) (h : Fin t → Bool) : ℝ × ℝ :=
  (xP θ x₀ z₀ t h, xNext θ x₀ z₀ t h)

/-- `((x_t, x_{t+1}), x_{t+2})` as a function of `(z₁, …, z_{t+1})`. -/
noncomputable def xTriple (θ x₀ : ℝ) (z₀ : Bool) (t : ℕ) (h : Fin (t + 1) → Bool) :
    (ℝ × ℝ) × ℝ :=
  (xPair θ x₀ z₀ t (Fin.init h),
    θ * xNext θ x₀ z₀ t (Fin.init h) + (1 - θ) * bv (lastState z₀ h))

/-- **The Markov property of `x` at date `t`**: the joint law of `(x_t, x_{t+1}, x_{t+2})` is the
law of `(x_t, x_{t+1})` followed by a transition function `R(x_{t+1}, ·)`. -/
def IsMarkovAt (θ x₀ : ℝ) (z₀ : Bool) (t : ℕ) : Prop :=
  ∃ R : Kernel ℝ ℝ, IsMarkovKernel R ∧
    (hist flipKernel (t + 1) z₀).map (xTriple θ x₀ z₀ t) =
      ((hist flipKernel t z₀).map (xPair θ x₀ z₀ t)) ⊗ₘ R.comap Prod.snd measurable_snd

/-! ### `θ < 1/2`: `x` is a Markov process -/

/-- Decoding the last shock: `1{y ≥ 1 − θ}`. -/
noncomputable def decodeZ (θ y : ℝ) : Bool := if 1 - θ ≤ y then true else false

theorem measurable_decodeZ (θ : ℝ) : Measurable (decodeZ θ) :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

/-- `R(y, ·)`: the law of `θy + (1 − θ)z′` with `z′ ~ Q(1{y ≥ 1 − θ}, ·)`. -/
noncomputable def xKernel (θ : ℝ) : Kernel ℝ ℝ :=
  (Kernel.deterministic id measurable_id ×ₖ
    flipKernel.comap (decodeZ θ) (measurable_decodeZ θ)).map fun p => θ * p.1 + (1 - θ) * bv p.2

theorem measurable_xKernel_fun (θ : ℝ) :
    Measurable fun p : ℝ × Bool => θ * p.1 + (1 - θ) * bv p.2 :=
  (measurable_const.mul measurable_fst).add
    (measurable_const.mul (measurable_bv.comp measurable_snd))

theorem xKernel_apply (θ y : ℝ) :
    xKernel θ y = (flipKernel (decodeZ θ y)).map fun z' => θ * y + (1 - θ) * bv z' := by
  have := isMarkovKernel_flipKernel
  rw [xKernel, Kernel.map_apply _ (measurable_xKernel_fun θ), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.comap_apply, Measure.dirac_prod,
    Measure.map_map (measurable_xKernel_fun θ) measurable_prodMk_left]
  rfl

theorem isMarkovKernel_xKernel (θ : ℝ) : IsMarkovKernel (xKernel θ) := by
  have := isMarkovKernel_flipKernel
  unfold xKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_xKernel_fun θ)

theorem xP_mem_Icc {θ x₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx₀ : x₀ ∈ Icc (0 : ℝ) 1)
    (z₀ : Bool) (t : ℕ) (h : Fin t → Bool) : xP θ x₀ z₀ t h ∈ Icc (0 : ℝ) 1 := by
  induction t with
  | zero => exact hx₀
  | succ t ih =>
    have hb : bv (lastState z₀ (Fin.init h)) ∈ Icc (0 : ℝ) 1 := by
      unfold bv; split_ifs <;> norm_num
    obtain ⟨h1, h2⟩ := ih (Fin.init h)
    constructor <;> simp only [xP] <;> nlinarith [hb.1, hb.2]

/-- For `θ < 1/2` the last shock is recovered from `x_{t+1}`. -/
theorem decodeZ_xNext {θ x₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hx₀ : x₀ ∈ Icc (0 : ℝ) 1)
    (z₀ : Bool) (t : ℕ) (h : Fin t → Bool) :
    decodeZ θ (xNext θ x₀ z₀ t h) = lastState z₀ h := by
  obtain ⟨h1, h2⟩ := xP_mem_Icc hθ0 (by linarith) hx₀ z₀ t h
  unfold decodeZ xNext
  cases hz : lastState z₀ h
  · simp only [bv, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
    simp only [ite_eq_right_iff, Bool.true_eq_false, imp_false, not_le]
    nlinarith
  · simp only [bv, ↓reduceIte, mul_one]
    simp only [ite_eq_left_iff, not_le, Bool.false_eq_true, imp_false, not_lt]
    nlinarith

/-- **Exercise 9.16, correction (`θ < 1/2`).** For `0 ≤ θ < 1/2` and `x₀ ∈ [0, 1]`, `x` is a
Markov process: at every date the law of `(x_t, x_{t+1}, x_{t+2})` factors through
`R(x_{t+1}, ·)`. -/
theorem ex_9_16_markov {θ x₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hx₀ : x₀ ∈ Icc (0 : ℝ) 1)
    (z₀ : Bool) (t : ℕ) : IsMarkovAt θ x₀ z₀ t := by
  have hQ := isMarkovKernel_flipKernel
  have hR := isMarkovKernel_xKernel θ
  refine ⟨xKernel θ, hR, ?_⟩
  have := ex_8_8a flipKernel t
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_of_countable _),
    hist_succ_lintegral_last flipKernel t z₀ (f := fun h => f (xTriple θ x₀ z₀ t h))
      (hf.comp (measurable_of_countable _)),
    Measure.lintegral_compProd hf,
    lintegral_map (hf.lintegral_kernel_prod_right' (κ := (xKernel θ).comap Prod.snd
      measurable_snd)) (measurable_of_countable _)]
  refine lintegral_congr fun h => ?_
  have hm : Measurable fun z' : Bool => θ * xNext θ x₀ z₀ t h + (1 - θ) * bv z' :=
    measurable_of_countable _
  simp only [xTriple, Fin.init_snoc, lastState_snoc, Kernel.comap_apply, xKernel_apply]
  have hp2 : (xPair θ x₀ z₀ t h).2 = xNext θ x₀ z₀ t h := rfl
  rw [hp2, lintegral_map (f := fun y => f (xPair θ x₀ z₀ t h, y)) (hf.comp measurable_prodMk_left)
    hm, decodeZ_xNext hθ0 hθ hx₀ z₀ t h]

/-! ### `θ = (√5 − 1)/2`: `x` is not a Markov process -/

/-- The golden-section `θ`, with `θ² + θ = 1`. -/
noncomputable def θg : ℝ := (Real.sqrt 5 - 1) / 2

theorem θg_sq : θg ^ 2 = 1 - θg := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold θg
  nlinarith

theorem θg_bounds : 3 / 5 < θg ∧ θg < 13 / 20 := by
  have h1 : (11 / 5 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 5 < 23 / 10 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold θg
  constructor <;> linarith

theorem xP3_eq (h : Fin 3 → Bool) :
    xP θg 0 false 3 h = θg * (1 - θg) * bv (h 0) + (1 - θg) * bv (h 1) := by
  simp only [xP, lastState, Fin.init]
  have e0 : ((Fin.last 0).castSucc.castSucc : Fin 3) = 0 := rfl
  have e1 : ((Fin.last 1).castSucc : Fin 3) = 1 := rfl
  rw [e0, e1]
  simp only [bv, Bool.false_eq_true, ↓reduceIte]
  ring

theorem xNext3_eq (h : Fin 3 → Bool) :
    xNext θg 0 false 3 h = θg * xP θg 0 false 3 h + (1 - θg) * bv (h 2) := rfl

theorem bv_false : bv false = 0 := rfl

theorem bv_true : bv true = 1 := rfl

/-- On `(x₃, x₄) = (θ, 1 − θ)`, the history is `(1, 1, 0)`: in particular `z₃ = 0`. -/
theorem decode_A {h : Fin 3 → Bool} (hA : xPair θg 0 false 3 h = (θg, 1 - θg)) :
    h 2 = false := by
  obtain ⟨hb1, hb2⟩ := θg_bounds
  have hsq := θg_sq
  have e1 : xP θg 0 false 3 h = θg := congrArg Prod.fst hA
  have e2 : xNext θg 0 false 3 h = 1 - θg := congrArg Prod.snd hA
  rw [xNext3_eq, e1] at e2
  rw [xP3_eq] at e1
  cases h0 : h 0 <;> cases h1 : h 1 <;> cases h2 : h 2 <;>
    simp only [h0, h1, h2, bv_false, bv_true] at e1 e2 <;> first | rfl | nlinarith

/-- On `(x₃, x₄) = (0, 1 − θ)`, the history is `(0, 0, 1)`: in particular `z₃ = 1`. -/
theorem decode_B {h : Fin 3 → Bool} (hB : xPair θg 0 false 3 h = (0, 1 - θg)) :
    h 2 = true := by
  obtain ⟨hb1, hb2⟩ := θg_bounds
  have e1 : xP θg 0 false 3 h = 0 := congrArg Prod.fst hB
  have e2 : xNext θg 0 false 3 h = 1 - θg := congrArg Prod.snd hB
  rw [xNext3_eq, e1] at e2
  rw [xP3_eq] at e1
  cases h0 : h 0 <;> cases h1 : h 1 <;> cases h2 : h 2 <;>
    simp only [h0, h1, h2, bv_false, bv_true] at e1 e2 <;> first | rfl | nlinarith

theorem mem_A : xPair θg 0 false 3 ![true, true, false] = (θg, 1 - θg) := by
  have hsq := θg_sq
  have e1 : xP θg 0 false 3 ![true, true, false] = θg := by
    rw [xP3_eq]
    change θg * (1 - θg) * bv true + (1 - θg) * bv true = θg
    rw [bv_true]
    nlinarith
  refine Prod.ext e1 ?_
  change xNext θg 0 false 3 ![true, true, false] = 1 - θg
  rw [xNext3_eq, e1]
  change θg * θg + (1 - θg) * bv false = 1 - θg
  rw [bv_false]
  nlinarith

theorem mem_B : xPair θg 0 false 3 ![false, false, true] = (0, 1 - θg) := by
  have e1 : xP θg 0 false 3 ![false, false, true] = 0 := by
    rw [xP3_eq]
    change θg * (1 - θg) * bv false + (1 - θg) * bv false = 0
    rw [bv_false]
    ring
  refine Prod.ext e1 ?_
  change xNext θg 0 false 3 ![false, false, true] = 1 - θg
  rw [xNext3_eq, e1]
  change θg * 0 + (1 - θg) * bv true = 1 - θg
  rw [bv_true]
  ring

/-- The law of `(x₃, x₄, x₅)` on `{(x₃, x₄) = p} × {x₅ ∈ S}`. -/
theorem triple_rect (p : ℝ × ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    (hist flipKernel 4 false).map (xTriple θg 0 false 3) ({p} ×ˢ S) =
      ∫⁻ h, (xPair θg 0 false 3 ⁻¹' {p}).indicator (fun h => flipKernel (lastState false h)
        {z' | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈ S}) h ∂hist flipKernel 3 false := by
  have hQ := isMarkovKernel_flipKernel
  have hm : MeasurableSet ({p} ×ˢ S) := (measurableSet_singleton p).prod hS
  rw [Measure.map_apply (measurable_of_countable _) hm, ← lintegral_indicator_one
    ((measurable_of_countable _) hm), hist_succ_lintegral_last flipKernel 3 false
    (measurable_of_countable _)]
  refine lintegral_congr fun h => ?_
  by_cases hp : h ∈ xPair θg 0 false 3 ⁻¹' {p}
  · rw [indicator_of_mem hp, ← lintegral_indicator_one (Set.toFinite _).measurableSet]
    refine lintegral_congr fun z' => ?_
    rw [mem_preimage, mem_singleton_iff] at hp
    have hiff : Fin.snoc h z' ∈ xTriple θg 0 false 3 ⁻¹' ({p} ×ˢ S) ↔
        z' ∈ {z' : Bool | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈ S} := by
      simp only [mem_preimage, mem_prod, mem_singleton_iff, xTriple, Fin.init_snoc,
        lastState_snoc, hp, true_and]
      rfl
    by_cases hz : z' ∈ {z' : Bool | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈ S}
    · rw [indicator_of_mem (hiff.2 hz), indicator_of_mem hz]
      rfl
    · rw [indicator_of_notMem (fun h' => hz (hiff.1 h')), indicator_of_notMem hz]
  · rw [indicator_of_notMem hp]
    refine (lintegral_congr fun z' => ?_).trans lintegral_zero
    rw [indicator_of_notMem]
    simp only [mem_preimage, mem_prod, mem_singleton_iff, xTriple, Fin.init_snoc, not_and]
    rw [mem_preimage, mem_singleton_iff] at hp
    exact fun h' => absurd h' hp

/-- **Exercise 9.16** (for `θ = (√5 − 1)/2`). From `x₀ = 0`, `z₀ = 0`, the process `x` is not
Markov at date 3: no transition function `R` makes the law of `(x₃, x₄, x₅)` the law of
`(x₃, x₄)` followed by `R(x₄, ·)`. -/
theorem ex_9_16 : ¬IsMarkovAt θg 0 false 3 := by
  rintro ⟨R, hR, heq⟩
  have hQ := isMarkovKernel_flipKernel
  have h3 := ex_8_8a flipKernel 3
  obtain ⟨hb1, hb2⟩ := θg_bounds
  set v := θg * (1 - θg)
  -- both sides on `{p} × {v}`
  have hside : ∀ (p : ℝ × ℝ) (c : ℝ≥0∞), (∀ h : Fin 3 → Bool, xPair θg 0 false 3 h = p →
      flipKernel (lastState false h) {z' | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈
        ({v} : Set ℝ)} = c) →
      c * hist flipKernel 3 false (xPair θg 0 false 3 ⁻¹' {p}) =
        R p.2 {v} * hist flipKernel 3 false (xPair θg 0 false 3 ⁻¹' {p}) := by
    intro p c hc
    have e := congrArg (fun μ : Measure ((ℝ × ℝ) × ℝ) => μ ({p} ×ˢ {v})) heq
    rw [triple_rect p (measurableSet_singleton v), Measure.compProd_apply_prod
      (measurableSet_singleton p) (measurableSet_singleton v), lintegral_singleton,
      Measure.map_apply (measurable_of_countable _) (measurableSet_singleton p),
      Kernel.comap_apply] at e
    rw [← e, ← lintegral_indicator_const ((measurable_of_countable _)
      (measurableSet_singleton p))]
    refine lintegral_congr fun h => ?_
    by_cases hp : h ∈ xPair θg 0 false 3 ⁻¹' {p}
    · rw [indicator_of_mem hp, indicator_of_mem hp, hc h hp]
    · rw [indicator_of_notMem hp, indicator_of_notMem hp]
  -- the conditional probabilities on the two histories
  have hA := hside (θg, 1 - θg) (9 / 10) fun h hh => by
    have h2 := decode_A hh
    have hx : xNext θg 0 false 3 h = 1 - θg := congrArg Prod.snd hh
    have hset : {z' : Bool | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈ ({v} : Set ℝ)} =
        {false} := by
      ext z'
      cases z'
      · simp [hx, v, bv]
      · simp [hx, v, bv]
        nlinarith
    rw [hset, show lastState false h = h 2 from rfl, h2, flipKernel_singleton]
    simp
  have hB := hside (0, 1 - θg) (1 / 10) fun h hh => by
    have h2 := decode_B hh
    have hx : xNext θg 0 false 3 h = 1 - θg := congrArg Prod.snd hh
    have hset : {z' : Bool | θg * xNext θg 0 false 3 h + (1 - θg) * bv z' ∈ ({v} : Set ℝ)} =
        {false} := by
      ext z'
      cases z'
      · simp [hx, v, bv]
      · simp [hx, v, bv]
        nlinarith
    rw [hset, show lastState false h = h 2 from rfl, h2, flipKernel_singleton]
    simp
  -- the histories `(1, 1, 0)` and `(0, 0, 1)` have positive probability
  have hpos : ∀ z z' : Bool, flipKernel z {z'} ≠ 0 := fun z z' => by
    rw [flipKernel_singleton]; split_ifs <;> norm_num
  have hHA : hist flipKernel 3 false (xPair θg 0 false 3 ⁻¹' {(θg, 1 - θg)}) ≠ 0 := fun h0 =>
    hist_singleton_ne_zero flipKernel hpos 3 false ![true, true, false]
      (measure_mono_null (singleton_subset_iff.2 mem_A) h0)
  have hHB : hist flipKernel 3 false (xPair θg 0 false 3 ⁻¹' {(0, 1 - θg)}) ≠ 0 := fun h0 =>
    hist_singleton_ne_zero flipKernel hpos 3 false ![false, false, true]
      (measure_mono_null (singleton_subset_iff.2 mem_B) h0)
  have r1 := (ENNReal.mul_left_inj hHA (measure_ne_top _ _)).1 hA
  have r2 := (ENNReal.mul_left_inj hHB (measure_ne_top _ _)).1 hB
  have := r1.trans r2.symm
  have := congrArg ENNReal.toReal this
  norm_num at this

end StokeyLucasPrescott.StochasticDP

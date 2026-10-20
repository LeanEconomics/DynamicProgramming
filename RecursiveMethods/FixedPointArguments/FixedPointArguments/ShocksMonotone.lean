/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.ShocksSchauder
import FixedPointArguments.MonotoneRRA

/-!
# Partially observed shocks: monotonicity, Proposition 8 and Exercise 17.14

SLP §17.6, pp. 539–541. Assumption 17.4 is `MonoAssumption17_4Pos` (relative risk aversion
`≤ 1` on `ℝ₊₊`) from `FixedPointArguments.MonotoneRRA`; the operator and weighted averages are
from `FixedPointArguments.ShocksContraction` and `FixedPointArguments.ShocksSchauder`.

* **Exercise 17.14c** (p. 540): `ex_17_14c_phi` (`0 ≤ yφ'(y)/φ(y) ≤ 1`, via `shocks_V''_nonpos`)
  and `ex_17_14c` (`−1 ≤ θξ'(θ)/ξ(θ) ≤ 0` for `ξ = φ_f` on `int Θ`, by differentiating under the
  integral, `ShocksBounds.ex_17_13_deriv`, which is also **Exercise 17.13** in derivative form);
  monotone forms `ShocksBounds.phiF_antitoneOn` (`ξ` nonincreasing) and
  `ShocksBounds.phiF_mul_monotoneOn` (`θξ(θ)` nondecreasing, the book's hint for (d)).
* `shocks_phi_monotoneOn`, `ShocksBounds.opT_monotone`: under Assumption 17.4 `φ` is
  nondecreasing and `T` is monotone (p. 539).
* **Exercise 17.14a** (`ex_17_14a_deriv`, `ex_17_14a`) and the counterexample to its "only if"
  (`ex_17_14a_counterexample`).
* **Exercise 17.14b** (`ex_17_14b`, with `ex_17_14b_chain`; weak form `ex_17_14b_le`).
* **Exercise 17.14d, corrected** (`ex_17_14d`, monotone form; `ex_17_14d_deriv`, derivative form):
  with the correct weights, `J(z)/z` is nonincreasing on `Z`. Tools: `shocksWAvg_mono`,
  `shocksWAvg_right_antitone`, `shocksWAvg_left_antitone`, and the change of variables
  `shocksWAvg_div` (`θ = x/z`).
* **Proposition 8, corrected** (`proposition_8`, p. 540): under Assumptions 17.1, 17.4, 17.5 **and
  17.6**, for every strictly positive fixed point `f` of `T`, `ρ(z) = z/ζ⁻¹(f(z))` is strictly
  increasing on `Z`.
* `proposition_8_general_counterexample`: under Assumption 17.5 alone the step (d) fails.

**Correction (Proposition 8, missing Assumption 17.6).** The book's `J` is the uniform-weights
formula of Exercise 17.12, valid (with the corrected weights `2θ/(b² − a²)`) only under
Assumption 17.6, which Proposition 8 omits. Under Assumption 17.5 alone the conclusion of
Exercise 17.14d fails (`proposition_8_general_counterexample`: a bimodal `g` and `ξ = 1/θ` give
`J(4/3)/(4/3) = 3/5 < 21/31 = J(10/7)/(10/7)`). This refutes the proof; the proposition itself
is refuted in `FixedPointArguments.ShocksProposition8` (`proposition_8_false`, an actual fixed
point of `T` in the same economy). The corrected theorem `proposition_8` assumes Assumption 17.6
and uses the correct weights.

**Correction (Exercise 17.14a, "if and only if").** `ρ` strictly increasing does not imply
`zη'/η < 1` everywhere: `ρ(z) = 1 + (z − 1)³` (`ex_17_14a_counterexample`) has `zη'/η = 1` at
`z = 1`. True: `zη'/η < 1` ⇒ `ρ` strictly increasing (`ex_17_14a`); and differentiability of `η`
is an assumption (the book does not show it).

**Correction (Exercise 17.14, (d) gives `≤ 1` but (b) needs `< 1`).** (b) is true as stated with
`ηζ'/ζ ≥ 1` (the manual's `> 1` fails where `H'' = 0`, `proposition_1_elasticity_counterexample`),
but (d) delivers only `zJ'/J ≤ 1`, so the chain (d) ⇒ (b) ⇒ (a) does not close. We close it
without derivatives: `J(z)/z = (η/z) H'(η)` nonincreasing and `H'` strictly increasing force
`η(z)/z` strictly decreasing (`proposition_8`).

**Correction (Exercise 17.14d with the correct weights).** The manual's four-case computation uses
the uniform weights; with the correct weights (d) still holds (`ex_17_14d`), as the transcription's
NOTE claims; our proof is the single monotonicity argument after `θ = x/z`.

**p. 541** ("Assumption 17.2 is a very mild strengthening of Assumption 17.4"): neither implies the
other; see `assumption17_2Pos_not_imp_17_4Pos_counterexample`,
`assumption17_4Pos_not_imp_17_2Pos_counterexample` and `monoAssumption17_2Pos_of_17_4Pos` in
`FixedPointArguments.MonotoneRRA` (17.4 plus a uniform positive lower bound on relative risk
aversion implies 17.2).
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology BoundedContinuousFunction

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-! ### Exercise 17.14 (c): elasticity of `φ` -/

/-- Under the (repaired) Assumption 17.1, `V'' ≤ 0` on `ℝ₊₊` (`V'` is decreasing). -/
theorem shocks_V''_nonpos (hV : Assumption17_1VR V V' V'') {y : ℝ} (hy : 0 < y) : V'' y ≤ 0 := by
  refine (hV.V'_deriv y hy).hasDerivWithinAt.nonpos_of_antitoneOn ?_ hV.V'_strictAntiOn.antitoneOn
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨y + min (ε / 2) y, ⟨hball ?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (lt_min (half_pos hε) hy)]
    exact (min_le_left _ _).trans_lt (half_lt_self hε)
  · exact mem_Ioi.2 (by have := lt_min (half_pos hε) hy; linarith)
  · have := lt_min (half_pos hε) hy; linarith

/-- **Exercise 17.14c, first part** (p. 540). Under Assumptions 17.1 (repaired) and 17.4 (on
`ℝ₊₊`), `0 ≤ y φ'(y)/φ(y) ≤ 1` for `y > 0`, where `φ'(y) = V'(y) + y V''(y)`: indeed
`y φ'/φ = 1 − (−yV''/V')` and `0 ≤ −yV''/V' ≤ 1`. -/
theorem ex_17_14c_phi (hV : Assumption17_1VR V V' V'') (h4 : MonoAssumption17_4Pos V' V'')
    {y : ℝ} (hy : 0 < y) :
    0 ≤ y * (V' y + y * V'' y) / olgPhi V' y ∧ y * (V' y + y * V'' y) / olgPhi V' y ≤ 1 := by
  have hV' := hV.V'_pos hy
  have hφ : 0 < olgPhi V' y := mul_pos hy hV'
  have h1 := h4 y hy
  have h2 := shocks_V''_nonpos hV hy
  simp only [monoRRA] at h1
  rw [div_le_iff₀ hV'] at h1
  constructor
  · apply div_nonneg _ hφ.le
    nlinarith
  · rw [div_le_one hφ, olgPhi]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) h2]

/-- The pointwise form of Exercise 17.14c: `0 ≤ y φ'(y) ≤ φ(y)` for `y > 0`. -/
theorem shocks_phi_elasticity (hV : Assumption17_1VR V V' V'') (h4 : MonoAssumption17_4Pos V' V'')
    {y : ℝ} (hy : 0 < y) :
    0 ≤ y * (V' y + y * V'' y) ∧ y * (V' y + y * V'' y) ≤ olgPhi V' y := by
  have hφ : 0 < olgPhi V' y := mul_pos hy (hV.V'_pos hy)
  obtain ⟨h1, h2⟩ := ex_17_14c_phi hV h4 hy
  refine ⟨?_, (div_le_one hφ).1 h2⟩
  have := mul_nonneg h1 hφ.le
  rwa [div_mul_cancel₀ _ hφ.ne'] at this

/-- Under Assumptions 17.1 and 17.4, `φ` is nondecreasing on `ℝ₊₊`. -/
theorem shocks_phi_monotoneOn (hV : Assumption17_1VR V V' V'') (h4 : MonoAssumption17_4Pos V' V'') :
    MonotoneOn (olgPhi V') (Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) hV.phi_continuousOn
    (fun y hy => (hV.phi_hasDerivAt (interior_subset hy)).differentiableAt.differentiableWithinAt)
    fun y hy => ?_
  rw [interior_Ioi] at hy
  rw [(hV.phi_hasDerivAt hy).deriv]
  have := (shocks_phi_elasticity hV h4 hy).1
  exact nonneg_of_mul_nonneg_right (by linarith) hy

/-! ### Exercise 17.14 (a) and (b) -/

/-- **Exercise 17.14a, the derivative** (manual): `ρ(z) = z/η(z)` has
`ρ'(z) = (1/η)(1 − zη'/η)`; so `ρ'(z) > 0 ↔ zη'(z)/η(z) < 1` pointwise. -/
theorem ex_17_14a_deriv {η : ℝ → ℝ} {z η' : ℝ} (hη : HasDerivAt η η' z) (hpos : 0 < η z) :
    HasDerivAt (fun w => w / η w) (1 / η z * (1 - z * η' / η z)) z := by
  have := (hasDerivAt_id' z).div hη hpos.ne'
  convert this using 1
  field_simp

/-- **Exercise 17.14a, the true direction.** If `zη'/η < 1` on `[p, q]` (`η > 0` differentiable),
then `ρ = z/η` is strictly increasing there. -/
theorem ex_17_14a {η η' : ℝ → ℝ} {p q : ℝ} (hη : ∀ z ∈ Icc p q, HasDerivAt η (η' z) z)
    (hpos : ∀ z ∈ Icc p q, 0 < η z) (hlt : ∀ z ∈ Icc p q, z * η' z / η z < 1) :
    StrictMonoOn (fun w => w / η w) (Icc p q) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc p q) (fun z hz =>
    (ex_17_14a_deriv (hη z hz) (hpos z hz)).continuousAt.continuousWithinAt) fun z hz => ?_
  have hz := interior_subset hz
  rw [(ex_17_14a_deriv (hη z hz) (hpos z hz)).deriv]
  exact mul_pos (one_div_pos.2 (hpos z hz)) (sub_pos.2 (hlt z hz))

/-- The counterexample of Exercise 17.14a: `η(z) = z/(1 + (z − 1)³)`. -/
noncomputable def shocksEtaEx (z : ℝ) : ℝ := z / (1 + (z - 1) ^ 3)

/-- **Correction (Exercise 17.14a, "only if").** `ρ(z) = z/η(z) = 1 + (z − 1)³` is strictly
increasing on `[1/2, 3/2]` with `η > 0` differentiable, yet at `z = 1`, `zη'/η = 1`, not `< 1`.
Correct statements: `ex_17_14a` (`zη'/η < 1` ⇒ `ρ` strictly increasing) and, conversely, `ρ`
increasing ⇒ `zη'/η ≤ 1` (from `ex_17_14a_deriv`). -/
theorem ex_17_14a_counterexample :
    StrictMonoOn (fun w => w / shocksEtaEx w) (Icc (1 / 2) (3 / 2)) ∧
      (∀ z ∈ Icc (1 / 2 : ℝ) (3 / 2), 0 < shocksEtaEx z) ∧ HasDerivAt shocksEtaEx 1 1 ∧
      ¬ (1 * 1 / shocksEtaEx 1 < 1) := by
  have hρpos : ∀ z ∈ Icc (1 / 2 : ℝ) (3 / 2), 0 < 1 + (z - 1) ^ 3 := fun z hz => by
    nlinarith [hz.1, hz.2, sq_nonneg (z - 1)]
  have heq : ∀ z ∈ Icc (1 / 2 : ℝ) (3 / 2), z / shocksEtaEx z = 1 + (z - 1) ^ 3 := fun z hz => by
    have hz0 : 0 < z := by linarith [hz.1]
    simp only [shocksEtaEx]
    field_simp [(hρpos z hz).ne', hz0.ne']
  refine ⟨fun x hx y hy hxy => ?_, fun z hz => div_pos (by linarith [hz.1]) (hρpos z hz), ?_, ?_⟩
  · simp only
    rw [heq x hx, heq y hy]
    have := Odd.strictMono_pow (R := ℝ) (n := 3) ⟨1, rfl⟩ (sub_lt_sub_right hxy 1)
    linarith
  · have h1 : HasDerivAt (fun z : ℝ => 1 + (z - 1) ^ 3) (3 * (1 - 1) ^ 2) 1 := by
      have := ((hasDerivAt_id (1 : ℝ)).sub_const 1).pow 3
      simpa using this.const_add 1
    have h2 : HasDerivAt shocksEtaEx ((1 * (1 + (1 - 1) ^ 3) - 1 * (3 * (1 - 1) ^ 2)) /
        (1 + (1 - 1) ^ 3) ^ 2) 1 := (hasDerivAt_id' (1 : ℝ)).div h1 (by norm_num)
    norm_num at h2
    exact h2
  · norm_num [shocksEtaEx]

/-- The chain rule for `J = ζ ∘ η`: `J'(z) = ζ'(η(z)) η'(z)`. -/
theorem ex_17_14b_chain (hH : Assumption17_1H L H H' H'') {η : ℝ → ℝ} {z η' : ℝ}
    (hη : HasDerivAt η η' z) (hηL : η z ∈ Ioo 0 L) :
    HasDerivAt (fun w => olgZeta H' (η w)) ((H' (η z) + η z * H'' (η z)) * η') z :=
  (hH.zeta_hasDerivAt hηL).comp z hη

/-- **Exercise 17.14b** (p. 540), true as stated. With `J = ζ ∘ η`, `J' = ζ'(η) η'`,
`zJ'/J = (ηζ'(η)/ζ(η)) (zη'/η)` and `ηζ'/ζ ≥ 1` (`zeta_elasticity_ge_one`), so `zJ'/J < 1`
implies `zη'/η < 1`. (The manual claims `ηζ'/ζ > 1`, which fails where `H'' = 0`:
`proposition_1_elasticity_counterexample`; `≥ 1` suffices.) -/
theorem ex_17_14b (hH : Assumption17_1H L H H' H'') {η : ℝ → ℝ} {z η' : ℝ} (hz : 0 < z)
    (hηL : η z ∈ Ioo 0 L)
    (hJ : z * ((H' (η z) + η z * H'' (η z)) * η') / olgZeta H' (η z) < 1) :
    z * η' / η z < 1 := by
  have hE := zeta_elasticity_ge_one hH hηL
  have hζ : 0 < olgZeta H' (η z) := hH.zeta_pos hηL
  have e : z * ((H' (η z) + η z * H'' (η z)) * η') / olgZeta H' (η z) =
      η z * (H' (η z) + η z * H'' (η z)) / olgZeta H' (η z) * (z * η' / η z) := by
    field_simp [hηL.1.ne']
  rw [e] at hJ
  by_contra h
  push Not at h
  nlinarith

/-- **Exercise 17.14b, weak version** (what Exercise 17.14d feeds it): `zJ'/J ≤ 1` implies
`zη'/η ≤ 1`. -/
theorem ex_17_14b_le (hH : Assumption17_1H L H H' H'') {η : ℝ → ℝ} {z η' : ℝ} (hz : 0 < z)
    (hηL : η z ∈ Ioo 0 L)
    (hJ : z * ((H' (η z) + η z * H'' (η z)) * η') / olgZeta H' (η z) ≤ 1) :
    z * η' / η z ≤ 1 := by
  have hE := zeta_elasticity_ge_one hH hηL
  have e : z * ((H' (η z) + η z * H'' (η z)) * η') / olgZeta H' (η z) =
      η z * (H' (η z) + η z * H'' (η z)) / olgZeta H' (η z) * (z * η' / η z) := by
    field_simp [hηL.1.ne']
  rw [e] at hJ
  by_contra h
  push Not at h
  nlinarith

/-! ### Exercise 17.14 (c): `ξ = φ_f` is nonincreasing and `θ ξ(θ)` nondecreasing -/

variable {θlo θhi : ℝ}

/-- `t ↦ clamp(t)/t` is nonincreasing on `ℝ₊₊`: it equals `max(θ̲/t, min(1, θ̄/t))`. -/
theorem shocksClamp_div_antitoneOn (h0 : 0 < θlo) (hθ : θlo ≤ θhi) :
    AntitoneOn (fun t => shocksClamp θlo θhi t / t) (Ioi 0) := by
  have e : ∀ t, 0 < t → shocksClamp θlo θhi t / t = max (θlo / t) (min 1 (θhi / t)) :=
    fun t ht => by
      rw [shocksClamp, ← max_div_div_right ht.le, ← min_div_div_right ht.le, div_self ht.ne']
  intro s hs t ht hst
  simp only
  rw [e s hs, e t ht]
  exact max_le_max (div_le_div_of_nonneg_left h0.le hs hst)
    (min_le_min le_rfl (div_le_div_of_nonneg_left (h0.le.trans hθ) hs hst))

/-- The derivative of the integrand in `θ̃` (on `int Θ`). -/
noncomputable def shocksIntegrandDeriv {Z : Type*} (L : ℝ) (H' V' V'' : ℝ → ℝ) (θlo θhi : ℝ)
    (f : Z → ℝ)
    (θ : ℝ) (ω : ℝ × Z) : ℝ :=
  (V' (shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ) +
      shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ *
        V'' (shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ)) *
    (-(shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2)) / θ ^ 2)

/-- The clamp is monotone. -/
theorem shocksClamp_monotone : Monotone (shocksClamp θlo θhi) := fun _ _ h =>
  max_le_max le_rfl (min_le_min_right _ h)

namespace ShocksBounds

variable {Z : Type*} {l₀ l : ℝ} (hS : ShocksBounds L θlo θhi l₀ H H' H'' V V' V'') {f : Z → ℝ}
include hS

/-- The integrand is nonincreasing in `θ̃` (Assumption 17.4: `φ` nondecreasing). -/
theorem integrand_antitone (h4 : MonoAssumption17_4Pos V' V'') (hf : ∀ z, 0 < f z)
    (ω : ℝ × Z) : Antitone fun θt => shocksIntegrand L H' V' θlo θhi f θt ω := by
  intro s t hst
  have hc := shocksClamp_mem hS.θlo_le ω.1
  have hm := hS.hH.zetaInv_pos (hf ω.2)
  have hcs := hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le s).1
  have hct := hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le t).1
  have hc0 := hS.θlo_pos.trans_le hc.1
  refine shocks_phi_monotoneOn hS.hV h4 (mem_Ioi.2 (mul_pos (div_pos hc0 hct) hm))
    (mem_Ioi.2 (mul_pos (div_pos hc0 hcs) hm)) ?_
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hc0.le hcs
    (shocksClamp_monotone hst)) hm.le

/-- `θ̃ ↦ θ̃ φ[(θ′/θ̃) ζ⁻¹(f(z′))]` is nondecreasing on `ℝ₊₊`: it equals
`c V'(c/clamp θ̃) / (clamp θ̃/θ̃)`, `c = clamp θ′ · ζ⁻¹(f(z′))`, with `V'` decreasing. -/
theorem integrand_mul_monotoneOn (hf : ∀ z, 0 < f z) (ω : ℝ × Z) :
    MonotoneOn (fun θt => θt * shocksIntegrand L H' V' θlo θhi f θt ω) (Ioi 0) := by
  intro s hs t ht hst
  have hs0 : 0 < s := hs
  have ht0 : 0 < t := ht
  have hc := shocksClamp_mem hS.θlo_le ω.1
  have hm := hS.hH.zetaInv_pos (hf ω.2)
  have hcs := hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le s).1
  have hct := hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le t).1
  have hc0 := hS.θlo_pos.trans_le hc.1
  set c := shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2)
  have hcpos : 0 < c := mul_pos hc0 hm
  have e : ∀ u, 0 < u → u * shocksIntegrand L H' V' θlo θhi f u ω =
      c * V' (c / shocksClamp θlo θhi u) / (shocksClamp θlo θhi u / u) := fun u hu => by
    have hcu := hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le u).1
    simp only [shocksIntegrand, olgPhi, shocksRatio]
    rw [show shocksClamp θlo θhi ω.1 / shocksClamp θlo θhi u * olgZetaInv L H' (f ω.2) =
      c / shocksClamp θlo θhi u by simp only [c]; ring]
    field_simp
  simp only
  rw [e s hs0, e t ht0]
  have hV : V' (c / shocksClamp θlo θhi s) ≤ V' (c / shocksClamp θlo θhi t) :=
    hS.hV.V'_strictAntiOn.antitoneOn (div_pos hcpos hct) (div_pos hcpos hcs)
      (div_le_div_of_nonneg_left hcpos.le hcs (shocksClamp_monotone hst))
  exact div_le_div₀ (mul_nonneg hcpos.le (hS.hV.V'_pos (div_pos hcpos hct)).le)
    (mul_le_mul_of_nonneg_left hV hcpos.le) (div_pos hct ht0)
    (shocksClamp_div_antitoneOn hS.θlo_pos hS.θlo_le hs ht hst)

variable [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] {B : ℝ}

/-- **Exercise 17.14c, second part, monotone form** (p. 540): under Assumption 17.4,
`ξ = φ_f` is nonincreasing on `ℝ₊₊`. -/
theorem phiF_antitoneOn (h4 : MonoAssumption17_4Pos V' V'') (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (hfc : Continuous f) (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z))
    [IsProbabilityMeasure μ] : Antitone (shocksPhiF L H' V' θlo θhi μ f) := fun s t hst =>
  integral_mono (hS.integrable_integrand hl hB hfc hfl μ t)
    (hS.integrable_integrand hl hB hfc hfl μ s) fun ω =>
      hS.integrand_antitone h4 (fun z => (hS.zeta_pos hl).trans_le (hfl z)) ω hst

/-- **Exercise 17.14c, second part, monotone form**: `θ ↦ θ ξ(θ)` is nondecreasing on `ℝ₊₊`
(the book's hint for (d)). -/
theorem phiF_mul_monotoneOn (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (hfc : Continuous f) (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z))
    [IsProbabilityMeasure μ] :
    MonotoneOn (fun θ => θ * shocksPhiF L H' V' θlo θhi μ f θ) (Ioi 0) := by
  intro s hs t ht hst
  simp only [shocksPhiF]
  rw [← integral_const_mul, ← integral_const_mul]
  exact integral_mono ((hS.integrable_integrand hl hB hfc hfl μ s).const_mul s)
    ((hS.integrable_integrand hl hB hfc hfl μ t).const_mul t) fun ω =>
      hS.integrand_mul_monotoneOn (fun z => (hS.zeta_pos hl).trans_le (hfl z)) ω hs ht hst

omit [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
/-- On `int Θ` the integrand is `φ(c/θ̃)`, `c = clamp θ′ · ζ⁻¹(f(z′))`, with derivative
`φ'(c/θ̃) · (−c/θ̃²)`. -/
theorem integrand_hasDerivAt (hf : ∀ z, 0 < f z) (ω : ℝ × Z) {θ : ℝ}
    (hθ : θ ∈ Ioo θlo θhi) :
    HasDerivAt (fun θt => shocksIntegrand L H' V' θlo θhi f θt ω)
      ((V' (shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ) +
          shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ *
            V'' (shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ)) *
        (-(shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2)) / θ ^ 2)) θ := by
  set c := shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2)
  have hθ0 : 0 < θ := hS.θlo_pos.trans hθ.1
  have hc : 0 < c := mul_pos (hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le ω.1).1)
    (hS.hH.zetaInv_pos (hf ω.2))
  have h1 : HasDerivAt (fun t => c / t) (-c / θ ^ 2) θ := by
    have := (hasDerivAt_inv hθ0.ne').const_mul c
    convert this using 1
    · ext t; rw [div_eq_mul_inv]
    · field_simp
  have h2 := (hS.hV.phi_hasDerivAt (div_pos hc hθ0)).comp θ h1
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
  simp only [Function.comp, shocksIntegrand, shocksRatio,
    shocksClamp_of_mem (Ioo_subset_Icc_self ht), c]
  ring_nf

omit [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
/-- On `int Θ`, `|∂_θ̃ integrand| ≤ M θ̄ L/θ̲²` and `θ̃ ∂_θ̃ integrand = −y φ'(y)`, `y = c/θ̃`. -/
theorem integrandDeriv_bound (hl : l ∈ Ioc 0 l₀) : ∃ K, 0 ≤ K ∧
    ∀ (f : Z → ℝ), (∀ z, olgZeta H' l ≤ f z) → ∀ θ ∈ Icc θlo θhi, ∀ ω : ℝ × Z,
      |shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω| ≤ K := by
  obtain ⟨ha, hab⟩ := hS.ratio_bounds
  have hpos : ∀ y ∈ Icc (θlo / θhi * l) (θhi / θlo * L), 0 < y := fun y hy =>
    (mul_pos ha hl.1).trans_le hy.1
  have hc : ContinuousOn (fun y => V' y + y * V'' y) (Icc (θlo / θhi * l) (θhi / θlo * L)) :=
    (hS.hV.V'_continuousOn.mono fun y hy => hpos y hy).add
      (continuousOn_id.mul (hS.hV.V''_cont.mono fun y hy => hpos y hy))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hl' : l ∈ Ioo 0 L := ⟨hl.1, hl.2.trans_lt hS.l₀_mem.2⟩
  have hθ0 := hS.θlo_pos
  have hθhi : 0 < θhi := hθ0.trans_le hS.θlo_le
  refine ⟨max M 0 * (θhi * L / θlo ^ 2), mul_nonneg (le_max_right _ _)
    (by have := hS.hH.L_pos; positivity), fun f hfl θ hθ ω => ?_⟩
  have hy0 : 0 ≤ f ω.2 := (hS.zeta_pos hl).le.trans (hfl ω.2)
  have hm := hS.hH.zetaInv_mem hy0
  have hlm : l ≤ olgZetaInv L H' (f ω.2) := by
    have := hS.hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 (hS.zeta_pos hl).le)
      (mem_Ici.2 hy0) (hfl ω.2)
    rwa [hS.hH.zetaInv_zeta (Ioo_subset_Ico_self hl')] at this
  have hcm := shocksClamp_mem hS.θlo_le ω.1
  have hθpos : 0 < θ := hθ0.trans_le hθ.1
  have hr : shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ =
      shocksRatio θlo θhi ω.1 θ * olgZetaInv L H' (f ω.2) := by
    simp only [shocksRatio, shocksClamp_of_mem hθ]; ring
  have hrm := shocksRatio_mem hθ0 hS.θlo_le ω.1 θ
  have hmem : shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ ∈
      Icc (θlo / θhi * l) (θhi / θlo * L) := by
    rw [hr]
    exact ⟨mul_le_mul hrm.1 hlm hl.1.le (ha.le.trans hrm.1),
      mul_le_mul hrm.2 hm.2.le hm.1 (ha.le.trans hab)⟩
  have h1 := (hM _ hmem).trans (le_max_left M 0)
  rw [Real.norm_eq_abs] at h1
  simp only [shocksIntegrandDeriv]
  rw [abs_mul]
  refine mul_le_mul h1 ?_ (abs_nonneg _) (le_max_right _ _)
  rw [abs_div, abs_neg, abs_of_nonneg (mul_nonneg (hθ0.le.trans hcm.1) hm.1),
    abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : θlo ^ 2 ≤ θ ^ 2 := by nlinarith [hθ.1]
  have h3 : shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) ≤ θhi * L :=
    mul_le_mul hcm.2 hm.2.le hm.1 hθhi.le
  nlinarith [mul_le_mul h3 h2 (by positivity) (by have := hS.hH.L_pos; positivity)]

/-- **Exercise 17.13, derivative form** (p. 537), and the derivative of `ξ = φ_f`: on `int Θ`,
`φ_f` is differentiable (under the integral sign), with `φ_f'(θ̃) = ∫ ∂_θ̃ integrand dμ`, and
`|φ_f'| ≤ K` with `K` independent of `f ∈ F` and of `μ`. -/
theorem ex_17_13_deriv (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) :
    ∃ K, 0 ≤ K ∧ ∀ (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] (f : Z → ℝ),
      Continuous f → (∀ z, olgZeta H' l ≤ f z) → ∀ θ ∈ Ioo θlo θhi,
        Integrable (shocksIntegrandDeriv L H' V' V'' θlo θhi f θ) μ ∧
        HasDerivAt (shocksPhiF L H' V' θlo θhi μ f)
          (∫ ω, shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ∂μ) θ ∧
        |∫ ω, shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ∂μ| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := hS.integrandDeriv_bound (Z := Z) hl
  refine ⟨K, hK0, fun μ _ f hfc hfl θ hθ => ?_⟩
  have hpos : ∀ z, 0 < f z := fun z => (hS.zeta_pos hl).trans_le (hfl z)
  have hcont := hS.continuous_integrand hfc hpos
  have hθ0 : 0 < θ := hS.θlo_pos.trans hθ.1
  have hF'c : Continuous (shocksIntegrandDeriv L H' V' V'' θlo θhi f θ) := by
    have hcc : Continuous fun ω : ℝ × Z => shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) :=
      (continuous_shocksClamp.comp continuous_fst).mul
        (hS.hH.zetaInv_continuousOn.comp_continuous (hfc.comp continuous_snd)
          fun ω => mem_Ici.2 (hpos _).le)
    have hcpos : ∀ ω : ℝ × Z, 0 < shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2) / θ :=
      fun ω => div_pos (mul_pos (hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le ω.1).1)
        (hS.hH.zetaInv_pos (hpos ω.2))) hθ0
    have hy : Continuous fun ω : ℝ × Z => shocksClamp θlo θhi ω.1 *
        olgZetaInv L H' (f ω.2) / θ := hcc.div_const θ
    exact ((hS.hV.V'_continuousOn.comp_continuous hy hcpos).add
      (hy.mul (hS.hV.V''_cont.comp_continuous hy hcpos))).mul (hcc.neg.div_const _)
  obtain ⟨hint, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun θt ω => shocksIntegrand L H' V' θlo θhi f θt ω)
    (F' := shocksIntegrandDeriv L H' V' V'' θlo θhi f) (bound := fun _ => K)
    (Ioo_mem_nhds hθ.1 hθ.2)
    (Eventually.of_forall fun t =>
      (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (hS.integrable_integrand hl hB hfc hfl μ θ) hF'c.aestronglyMeasurable
    (ae_of_all _ fun ω t ht => by
      rw [Real.norm_eq_abs]; exact hK f hfl t (Ioo_subset_Icc_self ht) ω)
    (integrable_const K)
    (ae_of_all _ fun ω t ht => hS.integrand_hasDerivAt hpos ω ht)
  refine ⟨hint, hder, ?_⟩
  rw [← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := K)
    (f := shocksIntegrandDeriv L H' V' V'' θlo θhi f θ)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hK f hfl θ (Ioo_subset_Icc_self hθ) ω)
  simpa using this

/-- **Exercise 17.14c, second part** (p. 540): under Assumptions 17.1 and 17.4, on `int Θ`,
`−1 ≤ θ ξ'(θ)/ξ(θ) ≤ 0` for `ξ = φ_f`, since `θ ξ'(θ) = −∫ y φ'(y) dμ` with
`0 ≤ y φ'(y) ≤ φ(y)` (`shocks_phi_elasticity`). -/
theorem ex_17_14c (h4 : MonoAssumption17_4Pos V' V'') (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) {θ : ℝ} (hθ : θ ∈ Ioo θlo θhi) :
    ∃ ξ', HasDerivAt (shocksPhiF L H' V' θlo θhi μ f) ξ' θ ∧
      -1 ≤ θ * ξ' / shocksPhiF L H' V' θlo θhi μ f θ ∧
      θ * ξ' / shocksPhiF L H' V' θlo θhi μ f θ ≤ 0 := by
  obtain ⟨K, -, hK⟩ := hS.ex_17_13_deriv (Z := Z) hl hB
  obtain ⟨hint, hder, -⟩ := hK μ f hfc hfl θ hθ
  have hpos : ∀ z, 0 < f z := fun z => (hS.zeta_pos hl).trans_le (hfl z)
  have hθ0 : 0 < θ := hS.θlo_pos.trans hθ.1
  have hξ := hS.zeta_pos hl |>.trans_le (hS.phiF_mem hl hB hfc hfl μ θ).1
  -- pointwise: `θ ∂ = −y φ'(y)` with `0 ≤ y φ'(y) ≤ φ(y)`
  have hpt : ∀ ω : ℝ × Z, -shocksIntegrand L H' V' θlo θhi f θ ω ≤
      θ * shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ∧
      θ * shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ≤ 0 := fun ω => by
    set c := shocksClamp θlo θhi ω.1 * olgZetaInv L H' (f ω.2)
    have hc : 0 < c := mul_pos (hS.θlo_pos.trans_le (shocksClamp_mem hS.θlo_le ω.1).1)
      (hS.hH.zetaInv_pos (hpos ω.2))
    have hy : 0 < c / θ := div_pos hc hθ0
    obtain ⟨e1, e2⟩ := shocks_phi_elasticity hS.hV h4 hy
    have e : θ * shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω =
        -(c / θ * (V' (c / θ) + c / θ * V'' (c / θ))) := by
      simp only [shocksIntegrandDeriv, c]; field_simp
    have e' : shocksIntegrand L H' V' θlo θhi f θ ω = olgPhi V' (c / θ) := by
      simp only [shocksIntegrand, shocksRatio, shocksClamp_of_mem (Ioo_subset_Icc_self hθ), c]
      ring_nf
    rw [e, e']
    constructor <;> linarith
  have hlow : -shocksPhiF L H' V' θlo θhi μ f θ ≤
      θ * ∫ ω, shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ∂μ := by
    rw [← integral_const_mul, shocksPhiF, ← integral_neg]
    exact integral_mono (hS.integrable_integrand hl hB hfc hfl μ θ).neg (hint.const_mul θ)
      fun ω => (hpt ω).1
  have hup : θ * ∫ ω, shocksIntegrandDeriv L H' V' V'' θlo θhi f θ ω ∂μ ≤ 0 := by
    rw [← integral_const_mul]
    exact integral_nonpos fun ω => (hpt ω).2
  refine ⟨_, hder, ?_, ?_⟩
  · rw [le_div_iff₀ hξ]; linarith
  · exact div_nonpos_of_nonpos_of_nonneg hup hξ.le

/-- **Monotonicity of `T`** (p. 539): under Assumption 17.4, `f ≤ g` implies `Tf ≤ Tg` (on
`F = {f ≥ ζ(l)}`), as in §17.5, since `ζ⁻¹` is increasing and `φ` nondecreasing. -/
theorem opT_monotone (h4 : MonoAssumption17_4Pos V' V'') (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)] {g : Z → ℝ}
    (hfc : Continuous f) (hgc : Continuous g) (hfl : ∀ z, olgZeta H' l ≤ f z)
    (hfg : ∀ z, f z ≤ g z) (z : Z) :
    shocksOpT L H' V' θlo θhi μ ν f z ≤ shocksOpT L H' V' θlo θhi μ ν g z := by
  have hgl : ∀ z, olgZeta H' l ≤ g z := fun z => (hfl z).trans (hfg z)
  have hzl := hS.zeta_pos hl
  have hpt : ∀ θt (ω : ℝ × Z), shocksIntegrand L H' V' θlo θhi f θt ω ≤
      shocksIntegrand L H' V' θlo θhi g θt ω := fun θt ω => by
    have hr := shocksRatio_mem hS.θlo_pos hS.θlo_le ω.1 θt
    have hr0 : 0 < shocksRatio θlo θhi ω.1 θt := hS.ratio_bounds.1.trans_le hr.1
    have hf0 := hzl.trans_le (hfl ω.2)
    have hg0 := hzl.trans_le (hgl ω.2)
    exact shocks_phi_monotoneOn hS.hV h4 (mem_Ioi.2 (mul_pos hr0 (hS.hH.zetaInv_pos hf0)))
      (mem_Ioi.2 (mul_pos hr0 (hS.hH.zetaInv_pos hg0))) (mul_le_mul_of_nonneg_left
        (hS.hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 hf0.le) (mem_Ici.2 hg0.le) (hfg ω.2))
        hr0.le)
  have hφ : ∀ θt, shocksPhiF L H' V' θlo θhi μ f θt ≤ shocksPhiF L H' V' θlo θhi μ g θt :=
    fun θt => integral_mono (hS.integrable_integrand hl hB hfc hfl μ θt)
      (hS.integrable_integrand hl hB hgc hgl μ θt) (hpt θt)
  exact integral_mono ((hS.phiFBCF hl hB hfc hfl μ).integrable (ν z))
    ((hS.phiFBCF hl hB hgc hgl μ).integrable (ν z)) hφ

end ShocksBounds

/-! ### Monotonicity of weighted averages -/

variable {q q₁ q₂ : ℝ → ℝ} {a b c d : ℝ}

/-- If `q ≤ C` on `[a, b]`, then `wavg(q; a, b) ≤ C` (`0 < a ≤ b`, `q` continuous). -/
theorem shocksWAvg_le_of_le (hq : ContinuousOn q (Icc a b)) (ha : 0 < a) (hab : a ≤ b)
    {C : ℝ} (hC : ∀ θ ∈ Icc a b, q θ ≤ C) : shocksWAvg q a b ≤ C := by
  rcases hab.eq_or_lt with h | h
  · subst h; simpa [shocksWAvg] using hC a ⟨le_rfl, le_rfl⟩
  have hW : 0 < ∫ θ in a..b, θ := by rw [shocks_integral_id]; nlinarith
  rw [shocksWAvg_of_lt h, div_le_iff₀ hW, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on h.le
    ((continuousOn_id.mul hq).intervalIntegrable_of_Icc h.le)
    ((continuous_const.mul continuous_id).intervalIntegrable _ _) fun θ hθ => ?_
  have := hC θ hθ
  have h0 : 0 < θ := ha.trans_le hθ.1
  nlinarith

/-- If `C ≤ q` on `[a, b]`, then `C ≤ wavg(q; a, b)`. -/
theorem le_shocksWAvg_of_le (hq : ContinuousOn q (Icc a b)) (ha : 0 < a) (hab : a ≤ b)
    {C : ℝ} (hC : ∀ θ ∈ Icc a b, C ≤ q θ) : C ≤ shocksWAvg q a b := by
  rcases hab.eq_or_lt with h | h
  · subst h; simpa [shocksWAvg] using hC a ⟨le_rfl, le_rfl⟩
  have hW : 0 < ∫ θ in a..b, θ := by rw [shocks_integral_id]; nlinarith
  rw [shocksWAvg_of_lt h, le_div_iff₀ hW, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on h.le
    ((continuous_const.mul continuous_id).intervalIntegrable _ _)
    ((continuousOn_id.mul hq).intervalIntegrable_of_Icc h.le) fun θ hθ => ?_
  have := hC θ hθ
  have h0 : 0 < θ := ha.trans_le hθ.1
  nlinarith

/-- The weighted average is monotone in the function. -/
theorem shocksWAvg_mono (hq₁ : ContinuousOn q₁ (Icc a b)) (hq₂ : ContinuousOn q₂ (Icc a b))
    (ha : 0 < a) (hab : a ≤ b) (h : ∀ θ ∈ Icc a b, q₁ θ ≤ q₂ θ) :
    shocksWAvg q₁ a b ≤ shocksWAvg q₂ a b := by
  rcases hab.eq_or_lt with h' | h'
  · subst h'; simpa [shocksWAvg] using h a ⟨le_rfl, le_rfl⟩
  have hW : 0 < ∫ θ in a..b, θ := by rw [shocks_integral_id]; nlinarith
  rw [shocksWAvg_of_lt h', shocksWAvg_of_lt h']
  refine div_le_div_of_nonneg_right ?_ hW.le
  refine intervalIntegral.integral_mono_on h'.le
    ((continuousOn_id.mul hq₁).intervalIntegrable_of_Icc h'.le)
    ((continuousOn_id.mul hq₂).intervalIntegrable_of_Icc h'.le) fun θ hθ => ?_
  exact mul_le_mul_of_nonneg_left (h θ hθ) (ha.trans_le hθ.1).le

/-- For nonincreasing `q`, extending the interval to the right lowers the average. -/
theorem shocksWAvg_right_antitone (hq : ContinuousOn q (Icc a d)) (hqa : AntitoneOn q (Icc a d))
    (ha : 0 < a) (hab : a ≤ b) {b' : ℝ} (hbb : b ≤ b') (hbd : b' ≤ d) :
    shocksWAvg q a b' ≤ shocksWAvg q a b := by
  rcases (hab.trans hbb).eq_or_lt with h | hab'
  · have h1 : b = b' := le_antisymm hbb (h ▸ hab)
    subst h1; exact le_rfl
  have hW : 0 < ∫ θ in a..b', θ := by rw [shocks_integral_id]; nlinarith
  have hsub : Icc a b ⊆ Icc a d := Icc_subset_Icc le_rfl (hbb.trans hbd)
  have hM : q b ≤ shocksWAvg q a b := le_shocksWAvg_of_le (hq.mono hsub) ha hab fun θ hθ =>
    hqa (hsub hθ) (hsub ⟨hab, le_rfl⟩) hθ.2
  have hdiff := shocksWAvg_extend_right hq ha hab hbb hbd hab'
  have hnum : ∫ θ in b..b', θ * (q θ - shocksWAvg q a b) ≤ 0 := by
    have := intervalIntegral.integral_mono_on (f := fun θ => θ * (q θ - shocksWAvg q a b))
      (g := fun _ => (0 : ℝ)) hbb (shocks_intervalIntegrable hq hab hbb hbd _)
      intervalIntegrable_const fun θ hθ => by
        have h0 : 0 < θ := ha.trans_le (hab.trans hθ.1)
        have : q θ ≤ q b := hqa ⟨hab, hbb.trans hbd⟩ ⟨hab.trans hθ.1, hθ.2.trans hbd⟩ hθ.1
        nlinarith
    simpa using this
  have : shocksWAvg q a b' - shocksWAvg q a b ≤ 0 := by
    rw [hdiff]; exact div_nonpos_of_nonpos_of_nonneg hnum hW.le
  linarith

/-- For nonincreasing `q`, extending the interval to the left raises the average. -/
theorem shocksWAvg_left_antitone (hq : ContinuousOn q (Icc c b)) (hqa : AntitoneOn q (Icc c b))
    {A : ℝ} (hA : 0 < A) (hcA : c ≤ A) (hAa : A ≤ a) (hab : a ≤ b) :
    shocksWAvg q a b ≤ shocksWAvg q A b := by
  rcases (hAa.trans hab).eq_or_lt with h | hAb
  · have h1 : A = a := le_antisymm hAa (h ▸ hab)
    subst h1; exact le_rfl
  have ha : 0 < a := hA.trans_le hAa
  have hW : 0 < ∫ θ in A..b, θ := by rw [shocks_integral_id]; nlinarith
  have hsub : Icc a b ⊆ Icc c b := Icc_subset_Icc (hcA.trans hAa) le_rfl
  have hM : shocksWAvg q a b ≤ q a := shocksWAvg_le_of_le (hq.mono hsub) ha hab fun θ hθ =>
    hqa (hsub ⟨le_rfl, hab⟩) (hsub hθ) hθ.1
  have hdiff := shocksWAvg_extend_left hq hA hcA hAa hab hAb
  have hnum : 0 ≤ ∫ θ in A..a, θ * (q θ - shocksWAvg q a b) := by
    have := intervalIntegral.integral_mono_on (g := fun θ => θ * (q θ - shocksWAvg q a b))
      (f := fun _ => (0 : ℝ)) hAa intervalIntegrable_const
      (shocks_intervalIntegrable hq hcA hAa hab _) fun θ hθ => by
        have h0 : 0 < θ := hA.trans_le hθ.1
        have : q a ≤ q θ := hqa ⟨hcA.trans hθ.1, hθ.2.trans hab⟩ ⟨hcA.trans hAa, hab⟩ hθ.2
        nlinarith
    simpa using this
  have : 0 ≤ shocksWAvg q A b - shocksWAvg q a b := by
    rw [hdiff]; exact div_nonneg hnum hW.le
  linarith

/-- **Change of variables `θ = x/z`** in the weighted average:
`wavg(ξ; a, b)/z = wavg(x ↦ ξ(x/z)/z; za, zb)` (`z > 0`, `0 < a ≤ b`). -/
theorem shocksWAvg_div {ξ : ℝ → ℝ} (hξ : ContinuousOn ξ (Icc a b)) {z : ℝ} (hz : 0 < z)
    (ha : 0 < a) (hab : a ≤ b) :
    shocksWAvg ξ a b / z = shocksWAvg (fun x => ξ (x / z) / z) (z * a) (z * b) := by
  rcases hab.eq_or_lt with h | h
  · subst h
    simp [shocksWAvg, mul_div_cancel_left₀ _ hz.ne']
  have hzab : z * a < z * b := mul_lt_mul_of_pos_left h hz
  rw [shocksWAvg_of_lt h, shocksWAvg_of_lt hzab, shocks_integral_id, shocks_integral_id]
  have e : ∫ x in z * a..z * b, x * (ξ (x / z) / z) = z * ∫ θ in a..b, θ * ξ θ := by
    have h1 := intervalIntegral.integral_comp_div (f := fun θ => θ * ξ θ) (a := z * a)
      (b := z * b) hz.ne'
    rw [mul_div_cancel_left₀ _ hz.ne', mul_div_cancel_left₀ _ hz.ne', smul_eq_mul] at h1
    rw [← h1]
    congr 1
    ext x
    ring
  rw [e]
  have hW : 0 < b ^ 2 - a ^ 2 := by nlinarith
  field_simp

/-! ### Exercise 17.14 (d) and Proposition 8 (uniform shocks, correct weights) -/

variable {xlo xhi : ℝ}

/-- `z a(z) = max{x̲, z θ̲}` for `z > 0`. -/
theorem mul_shocksA {z : ℝ} (hz : 0 < z) : z * shocksA xlo θlo z = max xlo (z * θlo) := by
  rw [shocksA, mul_max_of_nonneg _ _ hz.le, mul_div_cancel₀ _ hz.ne']

/-- `z b(z) = min{x̄, z θ̄}` for `z > 0`. -/
theorem mul_shocksB {z : ℝ} (hz : 0 < z) : z * shocksB xhi θhi z = min xhi (z * θhi) := by
  rw [shocksB, mul_min_of_nonneg _ _ hz.le, mul_div_cancel₀ _ hz.ne']

/-- **Exercise 17.14d, corrected (monotone form)** (p. 540). Under Assumptions 17.5–17.6, with the
correct weights, let `J(z) = wavg(ξ; a(z), b(z)) = E[ξ(θ) | z]`. If `ξ` is continuous and
nonincreasing on `ℝ₊₊` and `θ ↦ θ ξ(θ)` is nondecreasing there (Exercise 17.14c), then `J(z)/z`
is nonincreasing on `Z`, i.e. "`zJ'/J ≤ 1`" (`ex_17_14d_deriv`). Proof: substituting `θ = x/z`,
`J(z)/z = wavg(x ↦ ξ(x/z)/z; max{x̲, zθ̲}, min{x̄, zθ̄})`, the integrand is nonincreasing in `x`
and in `z`, and both endpoints are nondecreasing in `z`. -/
theorem ex_17_14d (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    {ξ : ℝ → ℝ} (hξc : ContinuousOn ξ (Ioi 0)) (hξa : AntitoneOn ξ (Ioi 0))
    (hu : MonotoneOn (fun θ => θ * ξ θ) (Ioi 0)) :
    AntitoneOn (fun z => shocksWAvg ξ (shocksA xlo θlo z) (shocksB xhi θhi z) / z)
      (Icc (xlo / θhi) (xhi / θlo)) := by
  intro z hz z' hz' hzz
  have hθhi : 0 < θhi := hθ0.trans hθ
  have hz0 : 0 < z := (div_pos hx0 hθhi).trans_le hz.1
  have hz0' : 0 < z' := hz0.trans_le hzz
  obtain ⟨h1, h2, h3⟩ := shocksA_shocksB_mem hx0 hx hθ0 hθ hz
  obtain ⟨h1', h2', h3'⟩ := shocksA_shocksB_mem hx0 hx hθ0 hθ hz'
  have ha0 : 0 < shocksA xlo θlo z := hθ0.trans_le h1
  have ha0' : 0 < shocksA xlo θlo z' := hθ0.trans_le h1'
  simp only
  rw [shocksWAvg_div (hξc.mono fun θ hθ => ha0.trans_le hθ.1) hz0 ha0 h2,
    shocksWAvg_div (hξc.mono fun θ hθ => ha0'.trans_le hθ.1) hz0' ha0' h2',
    mul_shocksA hz0, mul_shocksB hz0, mul_shocksA hz0', mul_shocksB hz0']
  set α := max xlo (z * θlo)
  set β := min xhi (z * θhi)
  set α' := max xlo (z' * θlo)
  set β' := min xhi (z' * θhi)
  have hα0 : 0 < α := hx0.trans_le (le_max_left _ _)
  have hαα : α ≤ α' := max_le_max le_rfl (mul_le_mul_of_nonneg_right hzz hθ0.le)
  have hββ : β ≤ β' := min_le_min le_rfl (mul_le_mul_of_nonneg_right hzz hθhi.le)
  have hαβ : α ≤ β := by
    have := mul_le_mul_of_nonneg_left h2 hz0.le
    rwa [mul_shocksA hz0, mul_shocksB hz0] at this
  have hαβ' : α' ≤ β' := by
    have := mul_le_mul_of_nonneg_left h2' hz0'.le
    rwa [mul_shocksA hz0', mul_shocksB hz0'] at this
  have hqc : ∀ w, 0 < w → ContinuousOn (fun x => ξ (x / w) / w) (Ioi 0) := fun w hw =>
    (hξc.comp (continuousOn_id.div_const w) fun x hx => div_pos hx hw).div_const w
  have hqa : AntitoneOn (fun x => ξ (x / z) / z) (Ioi 0) := fun x hx y hy hxy =>
    div_le_div_of_nonneg_right (hξa (div_pos hx hz0) (div_pos hy hz0)
      (div_le_div_of_nonneg_right hxy hz0.le)) hz0.le
  have hsub : Icc α β' ⊆ Ioi 0 := fun x hx => hα0.trans_le hx.1
  calc shocksWAvg (fun x => ξ (x / z') / z') α' β'
      ≤ shocksWAvg (fun x => ξ (x / z) / z) α' β' := by
        refine shocksWAvg_mono ((hqc z' hz0').mono fun x hx => hα0.trans_le (hαα.trans hx.1))
          ((hqc z hz0).mono fun x hx => hα0.trans_le (hαα.trans hx.1)) (hα0.trans_le hαα)
          hαβ' fun x hx => ?_
        have hx0' : 0 < x := hα0.trans_le (hαα.trans hx.1)
        have hu' := hu (div_pos hx0' hz0') (div_pos hx0' hz0)
          (div_le_div_of_nonneg_left hx0'.le hz0 hzz)
        simp only at hu'
        rw [div_le_div_iff₀ hz0' hz0]
        have e1 : x / z' * ξ (x / z') = x * (ξ (x / z') / z') := by ring
        have e2 : x / z * ξ (x / z) = x * (ξ (x / z) / z) := by ring
        rw [e1, e2] at hu'
        have := le_of_mul_le_mul_left hu' hx0'
        rw [div_le_div_iff₀ hz0' hz0] at this
        exact this
    _ ≤ shocksWAvg (fun x => ξ (x / z) / z) α β' :=
        shocksWAvg_left_antitone ((hqc z hz0).mono hsub) (hqa.mono hsub) hα0 le_rfl hαα hαβ'
    _ ≤ shocksWAvg (fun x => ξ (x / z) / z) α β :=
        shocksWAvg_right_antitone ((hqc z hz0).mono hsub) (hqa.mono hsub) hα0 hαβ hββ le_rfl

/-- Interior points of `[p, q]` are accumulation points of `[p, q]`. -/
theorem shocks_accPt_Icc {p r z : ℝ} (hz : z ∈ Ioo p r) : AccPt z (𝓟 (Icc p r)) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hd : 0 < min (ε / 2) ((r - z) / 2) := lt_min (half_pos hε) (by linarith [hz.2])
  refine ⟨z + min (ε / 2) ((r - z) / 2), ⟨hball ?_, ?_, ?_⟩, by linarith⟩
  · rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hd]
    exact (min_le_left _ _).trans_lt (half_lt_self hε)
  · linarith [hz.1]
  · linarith [min_le_right (ε / 2) ((r - z) / 2)]

/-- **Exercise 17.14d, derivative form**: wherever `J` is differentiable in `int Z`,
`zJ'(z)/J(z) ≤ 1` (from `ex_17_14d`). This is `≤ 1`, not the strict `< 1` that Exercise 17.14b
assumes; the chain is closed in `proposition_8` without derivatives. -/
theorem ex_17_14d_deriv (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    {ξ : ℝ → ℝ} (hξc : ContinuousOn ξ (Ioi 0)) (hξa : AntitoneOn ξ (Ioi 0))
    (hu : MonotoneOn (fun θ => θ * ξ θ) (Ioi 0)) {z J' : ℝ}
    (hz : z ∈ Ioo (xlo / θhi) (xhi / θlo))
    (hJ : HasDerivAt (fun w => shocksWAvg ξ (shocksA xlo θlo w) (shocksB xhi θhi w)) J' z)
    (hJpos : 0 < shocksWAvg ξ (shocksA xlo θlo z) (shocksB xhi θhi z)) :
    z * J' / shocksWAvg ξ (shocksA xlo θlo z) (shocksB xhi θhi z) ≤ 1 := by
  have hz0 : 0 < z := (div_pos hx0 (hθ0.trans hθ)).trans hz.1
  have hd := hJ.div (hasDerivAt_id' z) hz0.ne'
  have := hd.hasDerivWithinAt.nonpos_of_antitoneOn (shocks_accPt_Icc hz)
    (ex_17_14d hx0 hx hθ0 hθ hξc hξa hu)
  rw [div_le_iff₀ hJpos, one_mul]
  have hz2 : 0 < z ^ 2 := by positivity
  rw [div_nonpos_iff] at this
  rcases this with ⟨_, h⟩ | ⟨h, _⟩
  · linarith
  · nlinarith

/-- **Proposition 8, corrected** (p. 540). Let `H` satisfy Assumption 17.1, `V` the (repaired)
Assumption 17.1 and Assumption 17.4, and let `Ψ`, `G` be **uniform** (Assumptions 17.5 **and
17.6**), with the correct conditional law `G(·|z)` and any law `μ` of `(θ′, z′)`. If `f > 0` is a
continuous fixed point of `T` (equivalently `η = ζ⁻¹ ∘ f` solves (3)), then the price function
`ρ(z) = z/η(z)` is strictly increasing on `Z`.

Proof (no derivatives): by `ex_17_14c` (monotone form) `ξ = φ_f` is nonincreasing and `θξ(θ)`
nondecreasing, so by `ex_17_14d` `J(z)/z = ζ(η(z))/z = (η(z)/z) H'(η(z))` is nonincreasing; if
`z < z'` but `η(z')/z' ≥ η(z)/z`, then `η(z') > η(z)`, so `H'(η(z')) > H'(η(z))` (strict
convexity) and `J(z')/z' > J(z)/z`, a contradiction. This closes the gap between Exercise 17.14d
(`≤ 1`) and 17.14b (`< 1`) noted in the transcription, without needing `H'' > 0`. -/
theorem proposition_8 (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    (hθ2 : θhi < 2) (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (h4 : MonoAssumption17_4Pos V' V'') (μ : Measure (ℝ × Icc (xlo / θhi) (xhi / θlo)))
    [IsProbabilityMeasure μ] (f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ) (hfpos : ∀ z, 0 < f z)
    (hfix : ∀ z, f z = shocksOpT L H' V' θlo θhi μ (fun z => shocksCondLaw xlo xhi θlo θhi
      (shocksUnif xlo xhi) (shocksUnif θlo θhi) z.1) f z) :
    StrictMono fun z : Icc (xlo / θhi) (xhi / θlo) => (z : ℝ) / olgZetaInv L H' (f z) := by
  obtain ⟨l₀, hS⟩ := shocksBounds_exists hθ0 hθ.le hH hV
  have hne : (univ : Set (Icc (xlo / θhi) (xhi / θlo))).Nonempty :=
    ⟨⟨_, left_mem_Icc.2 (div_le_div₀ (hx0.trans hx).le hx.le hθ0 hθ.le)⟩, mem_univ _⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn hne f.continuous.continuousOn
  set l := min l₀ (olgZetaInv L H' (f m))
  have hl : l ∈ Ioc 0 l₀ := ⟨lt_min hS.l₀_mem.1 (hH.zetaInv_pos (hfpos m)), min_le_left _ _⟩
  have hlL : l ∈ Ico 0 L := ⟨hl.1.le, hl.2.trans_lt hS.l₀_mem.2⟩
  have hfl : ∀ z, olgZeta H' l ≤ f z := fun z =>
    calc olgZeta H' l ≤ olgZeta H' (olgZetaInv L H' (f m)) :=
          hH.zeta_strictMonoOn.monotoneOn hlL (hH.zetaInv_mem (hfpos m).le) (min_le_right _ _)
      _ = f m := hH.zeta_zetaInv (hfpos m).le
      _ ≤ f z := isMinOn_iff.1 hm z (mem_univ z)
  obtain ⟨B, -, hB⟩ := hS.exists_integrand_le (Z := Icc (xlo / θhi) (xhi / θlo)) hl
  set ξ := shocksPhiF L H' V' θlo θhi μ f
  have hJ := ex_17_14d hx0 hx hθ0 hθ (ξ := ξ)
    (hS.continuous_phiF hl hB f.continuous hfl μ).continuousOn
    ((hS.phiF_antitoneOn h4 hl hB f.continuous hfl μ).antitoneOn _)
    (hS.phiF_mul_monotoneOn hl hB f.continuous hfl μ)
  have hfJ : ∀ z : Icc (xlo / θhi) (xhi / θlo),
      f z = shocksWAvg ξ (shocksA xlo θlo z) (shocksB xhi θhi z) := fun z => by
    rw [hfix z]
    exact shocksUnif_integral_condLaw hx0 hx hθ0 hθ hθ2 z.2 ξ
  have hη : ∀ z, olgZetaInv L H' (f z) ∈ Ioo 0 L := fun z =>
    ⟨hH.zetaInv_pos (hfpos z), (hH.zetaInv_mem (hfpos z).le).2⟩
  have hζ : ∀ z, f z = olgZetaInv L H' (f z) * H' (olgZetaInv L H' (f z)) := fun z =>
    (hH.zeta_zetaInv (hfpos z).le).symm
  have hθhi : 0 < θhi := hθ0.trans hθ
  intro z z' hzz'
  have hzz : (z : ℝ) < z' := hzz'
  have hz0 : 0 < (z : ℝ) := (div_pos hx0 hθhi).trans_le z.2.1
  have hz0' : 0 < (z' : ℝ) := hz0.trans hzz
  simp only
  by_contra hcon
  push Not at hcon
  have hηp := (hη z).1
  have hηp' := (hη z').1
  rw [div_le_div_iff₀ hηp' hηp] at hcon
  -- `z' η ≤ z η'`, hence `η < η'`
  have hlt : olgZetaInv L H' (f z) < olgZetaInv L H' (f z') := by
    by_contra h
    push Not at h
    have h1 := mul_lt_mul_of_pos_right hzz hηp
    have h2 := mul_le_mul_of_nonneg_left h hz0.le
    linarith
  have hH' : H' (olgZetaInv L H' (f z)) < H' (olgZetaInv L H' (f z')) :=
    hH.H'_strictMonoOn (Ioo_subset_Ico_self (hη z)) (Ioo_subset_Ico_self (hη z')) hlt
  have hH'0 : 0 < H' (olgZetaInv L H' (f z)) := hH.H'_pos (hη z)
  have hanti := hJ z.2 z'.2 hzz.le
  simp only at hanti
  rw [← hfJ z, ← hfJ z', hζ z, hζ z', div_le_div_iff₀ hz0' hz0] at hanti
  have h3 := mul_le_mul_of_nonneg_right hcon hH'0.le
  have h4 := mul_lt_mul_of_pos_left hH' (mul_pos hz0 hηp')
  nlinarith

/-! ### Without Assumption 17.6 the step (d) fails -/

/-- `∫_p^q (c₀ + c₁ θ + c₂ θ²) dθ`. -/
theorem shocks_integral_quad (c₀ c₁ c₂ p r : ℝ) :
    ∫ θ in p..r, (c₀ + c₁ * θ + c₂ * θ ^ 2) =
      c₀ * (r - p) + c₁ * ((r ^ 2 - p ^ 2) / 2) + c₂ * ((r ^ 3 - p ^ 3) / 3) := by
  have i1 : IntervalIntegrable (fun θ : ℝ => c₀ + c₁ * θ) volume p r :=
    (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ : ℝ => c₂ * θ ^ 2) volume p r :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun θ : ℝ => c₁ * θ) volume p r :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_add intervalIntegrable_const
    i3, intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow, smul_eq_mul]
  norm_num
  ring

/-- `∫ 1_{[p, r]} F = ∫_p^r F`. -/
theorem shocks_integral_indicator_Icc {p r : ℝ} (hpr : p ≤ r) (F : ℝ → ℝ) :
    ∫ θ, (Icc p r).indicator F θ = ∫ θ in p..r, F θ := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hpr]

/-- The two bumps of the bimodal density. -/
noncomputable def shocksExBump1 (θ : ℝ) : ℝ :=
  (Icc (1 : ℝ) (11 / 10)).indicator (fun θ => 11 / 10 - θ) θ

/-- The second bump. -/
noncomputable def shocksExBump2 (θ : ℝ) : ℝ :=
  (Icc (7 / 5 : ℝ) (3 / 2)).indicator (fun θ => θ - 7 / 5) θ

/-- A bimodal density on `Θ = [1, 3/2]`, `g = 100 (bump₁ + bump₂)`, continuous on `Θ`. -/
noncomputable def shocksExBimodal (θ : ℝ) : ℝ := 100 * (shocksExBump1 θ + shocksExBump2 θ)

/-- Integrals of `k(θ) × bump` reduce to interval integrals. -/
theorem shocksExBump_integrals :
    ∫ θ, shocksExBump1 θ = 1 / 200 ∧ ∫ θ, shocksExBump2 θ = 1 / 200 ∧
      ∫ θ, shocksExBump1 θ * θ = 31 / 6000 ∧ ∫ θ, shocksExBump2 θ * θ = 44 / 6000 := by
  have e1 : (fun θ => shocksExBump1 θ * θ) = (Icc (1 : ℝ) (11 / 10)).indicator
      (fun θ => 0 + 11 / 10 * θ + -1 * θ ^ 2) := by
    ext θ; simp only [shocksExBump1]
    by_cases h : θ ∈ Icc (1 : ℝ) (11 / 10)
    · rw [indicator_of_mem h, indicator_of_mem h]; ring
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
  have e2 : (fun θ => shocksExBump2 θ * θ) = (Icc (7 / 5 : ℝ) (3 / 2)).indicator
      (fun θ => 0 + -(7 / 5) * θ + 1 * θ ^ 2) := by
    ext θ; simp only [shocksExBump2]
    by_cases h : θ ∈ Icc (7 / 5 : ℝ) (3 / 2)
    · rw [indicator_of_mem h, indicator_of_mem h]; ring
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
  have e3 : (fun θ : ℝ => 11 / 10 - θ) = fun θ => 11 / 10 + -1 * θ + 0 * θ ^ 2 := by
    ext θ; ring
  have e4 : (fun θ : ℝ => θ - 7 / 5) = fun θ => -(7 / 5) + 1 * θ + 0 * θ ^ 2 := by
    ext θ; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [shocksExBump1]
    rw [shocks_integral_indicator_Icc (by norm_num), e3, shocks_integral_quad]; norm_num
  · simp only [shocksExBump2]
    rw [shocks_integral_indicator_Icc (by norm_num), e4, shocks_integral_quad]; norm_num
  · rw [e1, shocks_integral_indicator_Icc (by norm_num), shocks_integral_quad]; norm_num
  · rw [e2, shocks_integral_indicator_Icc (by norm_num), shocks_integral_quad]; norm_num

/-- The bimodal example satisfies Assumption 17.5 (with `x ~ U[1, 2]`). -/
theorem shocksExBimodal_assumption :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal := by
  have hU := shocksUnif_assumption17_5 (xlo := 1) (xhi := 2) (θlo := 1) (θhi := 3 / 2) one_pos
    one_lt_two one_pos (by norm_num) (by norm_num)
  have hb1 : ∀ θ, 0 ≤ shocksExBump1 θ := fun θ => indicator_nonneg (fun θ hθ => by
    simp only [mem_Icc] at hθ; linarith) θ
  have hb2 : ∀ θ, 0 ≤ shocksExBump2 θ := fun θ => indicator_nonneg (fun θ hθ => by
    simp only [mem_Icc] at hθ; linarith) θ
  have i1 : Integrable shocksExBump1 :=
    (continuousOn_const.sub continuousOn_id |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have i2 : Integrable shocksExBump2 :=
    (continuousOn_id.sub continuousOn_const |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  obtain ⟨j1, j2, -, -⟩ := shocksExBump_integrals
  refine ⟨one_pos, one_lt_two, one_pos, by norm_num, by norm_num, hU.ψ_nonneg,
    fun θ => mul_nonneg (by norm_num) (add_nonneg (hb1 θ) (hb2 θ)), hU.ψ_zero,
    fun θ hθ => ?_, hU.ψ_cont, ?_, hU.ψ_int, ?_⟩
  · have h1 : θ ∉ Icc (1 : ℝ) (11 / 10) := fun h => hθ ⟨h.1, by linarith [h.2]⟩
    have h2 : θ ∉ Icc (7 / 5 : ℝ) (3 / 2) := fun h => hθ ⟨by linarith [h.1], h.2⟩
    simp [shocksExBimodal, shocksExBump1, shocksExBump2, indicator_of_notMem h1,
      indicator_of_notMem h2]
  · refine (Continuous.continuousOn (f := fun θ : ℝ => 100 * (max (11 / 10 - θ) 0 +
      max (θ - 7 / 5) 0)) (by fun_prop)).congr fun θ hθ => ?_
    simp only [shocksExBimodal, shocksExBump1, shocksExBump2]
    by_cases h1 : θ ≤ 11 / 10
    · rw [indicator_of_mem (show θ ∈ Icc (1 : ℝ) (11 / 10) from ⟨hθ.1, h1⟩),
        indicator_of_notMem (show θ ∉ Icc (7 / 5 : ℝ) (3 / 2) from fun h => by linarith [h.1]),
        max_eq_left (by linarith), max_eq_right (by linarith)]
    · by_cases h2 : 7 / 5 ≤ θ
      · rw [indicator_of_notMem (show θ ∉ Icc (1 : ℝ) (11 / 10) from fun h => h1 h.2),
          indicator_of_mem (show θ ∈ Icc (7 / 5 : ℝ) (3 / 2) from ⟨h2, hθ.2⟩),
          max_eq_right (by linarith), max_eq_left (by linarith)]
      · rw [indicator_of_notMem (show θ ∉ Icc (1 : ℝ) (11 / 10) from fun h => h1 h.2),
          indicator_of_notMem (show θ ∉ Icc (7 / 5 : ℝ) (3 / 2) from fun h => h2 h.1),
          max_eq_right (by linarith), max_eq_right (by linarith)]
  · simp only [shocksExBimodal]
    rw [integral_const_mul, integral_add i1 i2, j1, j2]
    norm_num

/-- In the bimodal example, `E[θ⁻¹ | z] = ∫ g ψ(z·) / π(z)`. -/
theorem shocksExBimodal_integral_inv {z : ℝ} (hzZ : 1 / (3 / 2) < z ∧ z < 2 / 1)
    (hπ : 0 < shocksPi (shocksUnif 1 2) shocksExBimodal z) :
    ∫ θ, θ⁻¹ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z =
      (∫ θ, shocksExBimodal θ * shocksUnif 1 2 (z * θ)) /
        shocksPi (shocksUnif 1 2) shocksExBimodal z := by
  rw [shocksExBimodal_assumption.integral_condLaw hzZ hπ, ← integral_div]
  congr 1
  ext θ
  by_cases h : θ = 0
  · subst h
    have : shocksExBimodal 0 = 0 :=
      shocksExBimodal_assumption.g_zero 0 (fun h => by linarith [h.1])
    simp [shocksCondDens, this]
  · simp only [shocksCondDens]
    field_simp

/-- **Correction (Proposition 8 needs Assumption 17.6; NOTE verified).** Without Assumption 17.6
the key step (d) fails for the true conditional law. Take `x ~ U[1, 2]` and the bimodal density
`g = 100 (bump on [1, 11/10] + bump on [7/5, 3/2])` (Assumption 17.5 holds), and `ξ(θ) = 1/θ`
(nonincreasing with `θξ(θ) = 1` nondecreasing, i.e. `θξ'/ξ = −1`, allowed by Exercise 17.14c).
Then `J(z) = E[ξ(θ) | z]` has `J(4/3)/(4/3) = 3/5 < 21/31 = J(10/7)/(10/7)`: `J(z)/z` is not
nonincreasing, so the conclusion of Exercise 17.14d (monotone form; `zJ'/J ≤ 1` cannot hold
throughout `(4/3, 10/7)` where `J` is differentiable): as `z` rises from `4/3` to `10/7`, the
support `[θ̲, x̄/z]` of `G(·|z)` loses the upper bump. This refutes the proof strategy under
Assumption 17.5 alone. (`ξ = 1/θ` corresponds to the limiting linear `V`; an actual fixed point
of `T` in this economy refuting Proposition 8 itself is `proposition_8_counterexample` in
`FixedPointArguments.ShocksProposition8`.) -/
theorem proposition_8_general_counterexample :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal ∧
      AntitoneOn (fun θ : ℝ => θ⁻¹) (Ioi 0) ∧ MonotoneOn (fun θ : ℝ => θ * θ⁻¹) (Ioi 0) ∧
      (1 : ℝ) / (3 / 2) < 4 / 3 ∧ (4 / 3 : ℝ) < 10 / 7 ∧ (10 / 7 : ℝ) < 2 / 1 ∧
      (∫ θ, θ⁻¹ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal (4 / 3)) / (4 / 3) <
        (∫ θ, θ⁻¹ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal (10 / 7)) /
          (10 / 7) := by
  have hA := shocksExBimodal_assumption
  obtain ⟨j1, j2, j3, j4⟩ := shocksExBump_integrals
  have i1 : Integrable shocksExBump1 :=
    (continuousOn_const.sub continuousOn_id |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have i2 : Integrable shocksExBump2 :=
    (continuousOn_id.sub continuousOn_const |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have i3 : Integrable fun θ => shocksExBump1 θ * θ := by
    have : (fun θ => shocksExBump1 θ * θ) =
        (Icc (1 : ℝ) (11 / 10)).indicator fun θ => (11 / 10 - θ) * θ := by
      ext θ; simp only [shocksExBump1]
      by_cases h : θ ∈ Icc (1 : ℝ) (11 / 10)
      · rw [indicator_of_mem h, indicator_of_mem h]
      · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
    rw [this]
    exact (Continuous.continuousOn (by fun_prop) |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have i4 : Integrable fun θ => shocksExBump2 θ * θ := by
    have : (fun θ => shocksExBump2 θ * θ) =
        (Icc (7 / 5 : ℝ) (3 / 2)).indicator fun θ => (θ - 7 / 5) * θ := by
      ext θ; simp only [shocksExBump2]
      by_cases h : θ ∈ Icc (7 / 5 : ℝ) (3 / 2)
      · rw [indicator_of_mem h, indicator_of_mem h]
      · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
    rw [this]
    exact (Continuous.continuousOn (by fun_prop) |>.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have hψ1 : ∀ x ∈ Icc (1 : ℝ) 2, shocksUnif 1 2 x = 1 := fun x hx => by
    rw [shocksUnif, indicator_of_mem hx]; norm_num
  have hψ0 : ∀ x, 2 < x → shocksUnif 1 2 x = 0 := fun x hx => by
    rw [shocksUnif, indicator_of_notMem fun h => by linarith [h.2]]
  have hgΘ : ∀ θ, θ ∉ Icc (1 : ℝ) (3 / 2) → shocksExBimodal θ = 0 := hA.g_zero
  -- at `z₁ = 4/3`, `ψ(z₁θ) = 1` on `Θ`
  have a1 : ∀ θ, shocksExBimodal θ * shocksUnif 1 2 (4 / 3 * θ) = shocksExBimodal θ := fun θ => by
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · rw [hψ1 _ ⟨by linarith [h.1], by linarith [h.2]⟩, mul_one]
    · rw [hgΘ θ h, zero_mul]
  have b1 : ∀ θ, shocksExBimodal θ * θ * shocksUnif 1 2 (4 / 3 * θ) =
      100 * (shocksExBump1 θ * θ + shocksExBump2 θ * θ) := fun θ => by
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · rw [hψ1 _ ⟨by linarith [h.1], by linarith [h.2]⟩, mul_one, shocksExBimodal]; ring
    · have h1 : θ ∉ Icc (1 : ℝ) (11 / 10) := fun h' => h ⟨h'.1, by linarith [h'.2]⟩
      have h2 : θ ∉ Icc (7 / 5 : ℝ) (3 / 2) := fun h' => h ⟨by linarith [h'.1], h'.2⟩
      simp [hgΘ θ h, shocksExBump1, shocksExBump2, indicator_of_notMem h1,
        indicator_of_notMem h2]
  -- at `z₂ = 10/7`, only the lower bump is seen
  have a2 : ∀ θ, shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) = 100 * shocksExBump1 θ :=
    fun θ => by
      simp only [shocksExBimodal, shocksExBump1, shocksExBump2]
      by_cases h1 : θ ∈ Icc (1 : ℝ) (11 / 10)
      · rw [indicator_of_mem h1, indicator_of_notMem (fun h => by linarith [h.1, h1.2]),
          hψ1 _ ⟨by linarith [h1.1], by linarith [h1.2]⟩]
        ring
      · rw [indicator_of_notMem h1]
        by_cases h2 : θ ∈ Icc (7 / 5 : ℝ) (3 / 2)
        · rw [indicator_of_mem h2]
          rcases h2.1.eq_or_lt with h3 | h3
          · rw [← h3]; ring
          · rw [hψ0 _ (by linarith)]; ring
        · rw [indicator_of_notMem h2]; ring
  have b2 : ∀ θ, shocksExBimodal θ * θ * shocksUnif 1 2 (10 / 7 * θ) =
      100 * (shocksExBump1 θ * θ) := fun θ => by
    have := a2 θ
    calc shocksExBimodal θ * θ * shocksUnif 1 2 (10 / 7 * θ) =
        shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) * θ := by ring
      _ = 100 * (shocksExBump1 θ * θ) := by rw [this]; ring
  have π1 : shocksPi (shocksUnif 1 2) shocksExBimodal (4 / 3) = 5 / 4 := by
    simp only [shocksPi]
    simp_rw [b1]
    rw [integral_const_mul, integral_add i3 i4, j3, j4]; norm_num
  have π2 : shocksPi (shocksUnif 1 2) shocksExBimodal (10 / 7) = 31 / 60 := by
    simp only [shocksPi]
    simp_rw [b2]
    rw [integral_const_mul, j3]; norm_num
  have N1 : ∫ θ, shocksExBimodal θ * shocksUnif 1 2 (4 / 3 * θ) = 1 := by
    simp_rw [a1]; exact hA.g_int
  have N2 : ∫ θ, shocksExBimodal θ * shocksUnif 1 2 (10 / 7 * θ) = 1 / 2 := by
    simp_rw [a2]; rw [integral_const_mul, j1]; norm_num
  refine ⟨hA, fun x hx y hy hxy => inv_anti₀ hx hxy, fun x hx y hy _ => by
    simp only; rw [mul_inv_cancel₀ (ne_of_gt hx), mul_inv_cancel₀ (ne_of_gt hy)],
    by norm_num, by norm_num, by norm_num, ?_⟩
  rw [shocksExBimodal_integral_inv ⟨by norm_num, by norm_num⟩ (by rw [π1]; norm_num),
    shocksExBimodal_integral_inv ⟨by norm_num, by norm_num⟩ (by rw [π2]; norm_num), π1, π2,
    N1, N2]
  norm_num

end StokeyLucasPrescott.FixedPointArguments

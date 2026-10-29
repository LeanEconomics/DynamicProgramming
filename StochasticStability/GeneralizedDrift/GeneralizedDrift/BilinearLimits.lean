/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.BilinearDrift
import GeneralizedDrift.CLTMoment
import GeneralizedDrift.MartingaleLILApplications

/-!
# Theorem 19.2.6: the limit theorems for the bilinear model (MT §19.2.4)

Meyn and Tweedie, Theorem 19.2.6, p. 496: the a.s. LLN for `Yₖ²` and the CLT and LIL for the
processes `θ` and `Y`.

* `theorem_19_2_6_limits`: under the hypotheses of `theorem_19_2_6`, the chain is positive
  Harris; `(1/N) Σ_{k ≤ N} Yₖ² → ∫ y² dπ` almost surely from every initial state; and every
  measurable `g` with `g² ≤ K(θ² + y²)` (so `g = θ` and `g = Y`) satisfies, from every initial
  state, the CLT `N^{−1/2} Σ (g(Φₖ) − π(g)) ⇒ N(0, γ_g²)` and the LIL with constant `γ_g`, `γ_g²`
  the series (17.3).
* `sq_le_exp_div`: `θ² ≤ exp(2s|θ|)/(2s²)`; `DriftV4.const_mul`: (V4) is preserved by scaling.

**Proof.** The Harris property and a (V4) function are where the book's "geometrically ergodic"
comes from: `theorem_19_2_3_driftV4` (Theorem 15.2.4 applied to the `f`-Kendall petite set of the
proof of Theorem 19.2.3, then Theorem 11.3.4) gives positive Harris recurrence and an everywhere
finite `W ≥ ε³y² + exp(2s|θ|) + 1` solving (V4) for a petite set. A multiple of `W` dominates
`g²`, so Theorem 17.0.1 (`theorem_17_0_1`, `theorem_17_0_1_iv`,
`theorem_17_0_1_iv_lil_poisson`, copied from the Chapter 17 project) applies.

**Hypotheses.** As for `theorem_19_2_6`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- `θ² ≤ exp(2s|θ|)/(2s²)` for `s > 0`. -/
theorem sq_le_exp_div {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    θ ^ 2 ≤ (2 * s ^ 2)⁻¹ * Real.exp (2 * s * |θ|) := by
  have h := Real.pow_div_factorial_le_exp (x := 2 * s * |θ|) (by positivity) 2
  rw [show (Nat.factorial 2 : ℝ) = 2 by norm_num, mul_pow, mul_pow, sq_abs] at h
  rw [← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  nlinarith

/-- (V4) is preserved by scaling `V`. -/
theorem DriftV4.const_mul {X : Type*} [MeasurableSpace X] {P : Kernel X X} {V : X → ℝ≥0∞}
    (hV : Measurable V) {ρ b : ℝ≥0∞} {C : Set X} (h : DriftV4 P V ρ b C) (c : ℝ≥0∞) :
    DriftV4 P (fun x => c * V x) ρ (c * b) C := fun x => by
  rw [lintegral_const_mul _ hV]
  calc c * ∫⁻ y, V y ∂P x ≤ c * (ρ * V x + C.indicator (fun _ => b) x) := mul_le_mul' le_rfl (h x)
    _ = ρ * (c * V x) + C.indicator (fun _ => c * b) x := by
        by_cases hx : x ∈ C
        · rw [indicator_of_mem hx, indicator_of_mem hx]; ring
        · rw [indicator_of_notMem hx, indicator_of_notMem hx]; ring

/-- **Theorem 19.2.6, the limit theorems** (MT p. 496): under the hypotheses of
`theorem_19_2_6`, the chain is positive Harris, the LLN `(1/N) Σ Yₖ² → ∫ y² dπ` holds almost surely
from every initial state, and every measurable `g` with `g² ≤ K(θ² + y²)` (in particular the
processes `θ` and `Y`) satisfies the CLT, `N^{−1/2} Σ (g(Φₖ) − π(g)) ⇒ N(0, γ_g²)`, and the LIL,
both from every initial state, with `γ_g²` the series (17.3) (Theorem 17.0.1). -/
theorem theorem_19_2_6_limits (Γz Γw : Measure ℝ) [IsProbabilityMeasure Γz]
    [IsProbabilityMeasure Γw] {α : ℝ} (hα : |α| < 1) [IsMarkovKernel (dblKernel Γz Γw α)]
    {ψ : Measure (ℝ × ℝ)} (hψ : IsMaximalIrreducibility (dblKernel Γz Γw α) ψ)
    (hap : IsAperiodic (dblKernel Γz Γw α) ψ) (hT : IsTChain (dblKernel Γz Γw α))
    (hζ : ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz < 1)
    (hW : ∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw ≠ ∞) :
    IsPositiveHarris (dblKernel Γz Γw α) ψ ∧ ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      IsInvariant (dblKernel Γz Γw α) π ∧
      (∀ x, ∀ᵐ ω ∂pathKernel (dblKernel Γz Γw α) x, Tendsto
        (fun n => pathSum (fun z => z.2 ^ 2) n ω / n) atTop (𝓝 (∫ z, z.2 ^ 2 ∂π))) ∧
      ∀ g : ℝ × ℝ → ℝ, Measurable g → ∀ K : ℝ, (∀ z, g z ^ 2 ≤ K * (z.1 ^ 2 + z.2 ^ 2)) →
        (∀ {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
          {Z : Ω' → ℝ},
          HasLaw Z (gaussianReal 0 (asymptoticVariance (dblKernel Γz Γw α) π g).toNNReal) P' →
          ∀ x, haveI := isMarkovKernel_pathKernel (dblKernel Γz Γw α)
          TendstoInDistribution (fun (n : ℕ) ω =>
            (√(n : ℝ))⁻¹ * pathSum (fun x => g x - ∫ y, g y ∂π) n ω)
            atTop Z (fun _ => pathKernel (dblKernel Γz Γw α) x) P') ∧
        ∀ x, ∀ᵐ ω ∂pathKernel (dblKernel Γz Γw α) x,
          HasLIL (fun n => pathSum (fun y => g y - ∫ z, g z ∂π) n ω)
            (√(asymptoticVariance (dblKernel Γz Γw α) π g)) := by
  obtain ⟨-, π, hπp, hπ, -, -, hπy, -⟩ := theorem_19_2_6 Γz Γw hα hψ hap hT hζ hW
  set ζ := ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z| - 2)) ∂Γz with hζdef
  have hζt : ζ ≠ ∞ := ne_top_of_lt hζ
  have hs := dblS_pos hα
  have hM : ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z|)) ∂Γz ≠ ∞ := by
    have e : ∫⁻ z, ENNReal.ofReal (Real.exp (2 * dblS α * |z|)) ∂Γz =
        ENNReal.ofReal (Real.exp 2) * ζ := by
      rw [hζdef, ← lintegral_const_mul _ (by fun_prop)]
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      ring_nf
    rw [e]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hζt
  have hζ1 : ζ.toReal < 1 := by
    have := (ENNReal.toReal_lt_toReal hζt ENNReal.one_ne_top).2 hζ
    simpa using this
  obtain ⟨ε, hε, hlam⟩ := exists_dblLam_lt_one hα ENNReal.toReal_nonneg hζ1
    (ENNReal.toReal_nonneg (a := ∫⁻ w, ENNReal.ofReal (w ^ 2) ∂Γw))
  have hε3 : 0 < ε ^ 3 := pow_pos hε 3
  set V : ℝ × ℝ → ℝ≥0 := fun x => (ε ^ 3 * x.2 ^ 2 + Real.exp (2 * dblS α * |x.1|)).toNNReal
    with hVdef
  have hVm : Measurable V := by rw [hVdef]; fun_prop
  have hVcoe : ∀ x, (V x : ℝ≥0∞) =
      ENNReal.ofReal (ε ^ 3 * x.2 ^ 2 + Real.exp (2 * dblS α * |x.1|)) := fun x => rfl
  have hVV : ∀ k ω, (V (ω k) : ℝ≥0∞) ≤ dblVs α ε k ω := by
    intro k ω
    rw [hVcoe, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (p := ε ^ 3) hε3.le]
    unfold dblVs dblC
    exact add_le_add (le_self_add.trans le_self_add) le_rfl
  have hvc : ∀ K : Set (ℝ × ℝ), IsCompact K → ∃ M : ℝ≥0∞, M ≠ ∞ ∧
      ∀ x ∈ K, ENNReal.ofReal (dblV0 α ε x) ≤ M := fun K hK => by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_dblV0 α ε).continuousOn
    exact ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun x hx => ENNReal.ofReal_le_ofReal
      ((le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hC x hx))⟩
  have hdrift := dbl_drift Γz Γw hα hζt hW hM hε
  obtain ⟨hph, Wf, hWm, hVW, ⟨B, hB, hWB⟩, ρ, b, hρ, hb, C, hC, h4⟩ :=
    theorem_19_2_3_driftV4 hψ hT (Vs := dblVs α ε)
    (fun k => (measurable_dblVs_natFilt α ε k).mono ((natFilt (X := ℝ × ℝ)).le k) le_rfl)
    hVm (isCoercive_dblV hα hε) hVV (v := fun x => ENNReal.ofReal (dblV0 α ε x))
    (dblVs_zero α hε.le) hvc (ENNReal.ofReal_lt_one.2 hlam) ENNReal.ofReal_ne_top hdrift
  have hW1 : ∀ x, 1 ≤ Wf x := fun x => le_add_self.trans (hVW x)
  have hWfin : ∀ x, Wf x ≠ ∞ := fun x => ne_top_of_le_ne_top (ENNReal.mul_ne_top hB
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩)) (hWB x)
  have hint : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) π :=
    integrable_of_ofReal_abs_le (f := fun z => ENNReal.ofReal (z.2 ^ 2)) (by fun_prop)
      (fun z => by rw [abs_of_nonneg (sq_nonneg _)]) hπy
  refine ⟨hph, π, hπp, hπ, fun x => (theorem_17_0_1 hph hπ).1 _ (by fun_prop) hint x,
    fun g hg K hK => ?_⟩
  have hK0 : 0 ≤ K := by
    have h := hK (1, 1)
    nlinarith [sq_nonneg (g (1, 1))]
  set c0 : ℝ := (ε ^ 3)⁻¹ + (2 * dblS α ^ 2)⁻¹ with hc0
  set c : ℝ≥0∞ := ENNReal.ofReal (K * c0) + 1 with hcdef
  have hc1 : 1 ≤ c := le_add_self
  have hct : c ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
  have hgle : ∀ z, ENNReal.ofReal (g z ^ 2) ≤ c * Wf z := fun z => by
    have hθ := sq_le_exp_div hs z.1
    have hy : z.2 ^ 2 = (ε ^ 3)⁻¹ * (ε ^ 3 * z.2 ^ 2) := by field_simp
    have hA : 0 ≤ ε ^ 3 * z.2 ^ 2 := by positivity
    have hE : 0 ≤ Real.exp (2 * dblS α * |z.1|) := (Real.exp_pos _).le
    have hc00 : 0 ≤ (ε ^ 3)⁻¹ := by positivity
    have hc01 : 0 ≤ (2 * dblS α ^ 2)⁻¹ := by positivity
    have hreal : g z ^ 2 ≤ K * c0 * (ε ^ 3 * z.2 ^ 2 + Real.exp (2 * dblS α * |z.1|)) := by
      refine (hK z).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hK0
      rw [hc0]
      nlinarith [mul_nonneg hc00 hE, mul_nonneg hc01 hA]
    calc ENNReal.ofReal (g z ^ 2)
        ≤ ENNReal.ofReal (K * c0) * (V z : ℝ≥0∞) := by
          rw [hVcoe, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal hreal
      _ ≤ c * Wf z := mul_le_mul' le_self_add (le_self_add.trans (hVW z))
  have hW'm : Measurable fun x => c * Wf x := hWm.const_mul _
  have hW'1 : ∀ x, 1 ≤ c * Wf x := fun x => (hW1 x).trans (le_mul_of_one_le_left' hc1)
  have hW'fin : ∀ x, c * Wf x ≠ ∞ := fun x => ENNReal.mul_ne_top hct (hWfin x)
  have h4' := h4.const_mul hWm c
  have hcb : c * b ≠ ∞ := ENNReal.mul_ne_top hct hb
  exact ⟨fun hZ x => theorem_17_0_1_iv hph hap hW'm hW'1 hW'fin hρ hcb hC h4' hπ hg hgle hZ x,
    fun x => theorem_17_0_1_iv_lil_poisson hph hap hW'm hW'1 hW'fin hρ hcb hC h4' hπ hg hgle x⟩

end MeynTweedie.GeneralizedDrift

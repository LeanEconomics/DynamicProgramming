/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.OLGProposition2
import FixedPointArguments.ShocksModel

/-!
# Partially observed shocks: Proposition 6 by the contraction mapping theorem

SLP §17.6, pp. 534–535: the operator (4) and Proposition 6 (Exercise 17.9). The OLG primitives
(`Assumption17_1H`, the repaired `Assumption17_1VR` and `Assumption17_2R`, `olgZeta`, `olgPhi`,
`olgZetaInv`, the kernel `olgG` and its bounds) are from `FixedPointArguments.OLGModel` and
`FixedPointArguments.OLGProposition2`; the information structure from
`FixedPointArguments.ShocksModel`.

**The operator (4).** By the NOTE on p. 535, `∫_Z ∫_Θ h(θ′, z′) G(dθ′|z′) π(dz′)` is the expectation
of `h` under the joint law `μ` of `(θ′, z′)`, so (4) reads
`(Tf)(z) = ∫ φ_f(θ̃) G(dθ̃|z)`, `φ_f(θ̃) = ∫ φ[(θ′/θ̃) ζ⁻¹(f(z′))] dμ(θ′, z′)`
(`shocksOpT`, `shocksPhiF`, `shocksIntegrand`). Here `Z` is any compact metric space, `μ` any
probability measure on `ℝ × Z` and `ν z = G(·|z)` any weakly continuous family of probability
measures on `ℝ`; `θ′`, `θ̃` are clamped to `Θ` (`shocksClamp`), which changes nothing on the
supports. The ratio `θ′/θ̃ ∈ [θ̲/θ̄, θ̄/θ̲]` (`shocksRatio_mem`) plays the role of `x′` in §17.2, so
the integrand is the OLG kernel `olgG` at `x′ = θ′/θ̃` (`shocksIntegrand_eq_olgG`).

* `ShocksBounds`: the standing hypotheses, with `l₀` such that `H'(l₀) < C = (θ̲/θ̄)V'((θ̄/θ̲)L)`
  (the manual's `C`); `shocksBounds_exists`.
* Step 1 of Exercise 17.9 (and Steps 1–2 of Exercise 17.11): `ShocksBounds.integrand_ge`,
  `ShocksBounds.exists_integrand_le`, `ShocksBounds.opT_mem` (`T` maps continuous `f ≥ ζ(l)` to
  continuous `ζ(l) ≤ Tf ≤ B`; continuity of `Tf` is the weak continuity of `G(·|z)`).
* **Exercise 17.9** (`ShocksBounds.ex_17_9`, p. 535): `T̂g = ln T(e^g)` is a contraction of
  modulus `β` (mean value theorem: `ShocksBounds.abs_log_integrand_sub_le`; integrated:
  `ShocksBounds.opT_exp_le`); `ShocksBounds.unique_fixedPoint_ge`.
* **Proposition 6** (`proposition_6`, p. 535), corrected: exactly one strictly positive continuous
  fixed point; `proposition_6_islands`: the same for the islands model with `μ` the joint law
  (`shocksJointLaw`) and `G(·|z)` the conditional law of `FixedPointArguments.ShocksModel`.

**Correction (Proposition 6, "a unique fixed point in `C(Z)`").** `T0 = 0`
(`shocksOpT_zero`, `proposition_6_zero_fixedPoint`), so `T` has two fixed points in `C(Z)`
(`proposition_6_counterexample`); `T` is also not defined on functions with negative values.
The proof gives uniqueness among strictly positive (equivalently, by compactness, bounded away
from zero) fixed points, via the sets `[ζ(l), ∞)`, `l ↓ 0`, as in `proposition_2`.

**Correction (Proposition 6, hypotheses).** Assumption 17.2 contradicts Assumption 17.1
(`assumption17_2_counterexample`, `assumption17_2R_inconsistent` in
`FixedPointArguments.OLGProposition2`), so Proposition 6 as stated is vacuous; it is proved here
under the repaired assumptions. The continuity of `Tf` needs Exercise 17.8b, including the
endpoints of `Z` (the convention `G(·|z̲) = δ_{θ̄}`, `G(·|z̄) = δ_{θ̲}`) and `π > 0` on `int Z`.

**Correction (manual, Exercise 17.9).** The final inequalities drop `β`
("`(T̂g)(z) − (T̂h)(z) ≤ β sup{g(z) − h(z)} ≤ ‖g − h‖`") and write `sup(g − h)` for
`sup|g − h|`; the mean value theorem is applied at `z′`. The manual's weights `w` are replaced
by the equivalent pointwise bound `φ[⋯e^{g}⋯] ≤ e^{β‖g − h‖} φ[⋯e^{h}⋯]`.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

/-- Clamping to `Θ = [θ̲, θ̄]`: `t ↦ max θ̲ (min t θ̄)`. -/
def shocksClamp (θlo θhi t : ℝ) : ℝ := max θlo (min t θhi)

variable {θlo θhi : ℝ}

/-- The clamp lands in `Θ`. -/
theorem shocksClamp_mem (hθ : θlo ≤ θhi) (t : ℝ) : shocksClamp θlo θhi t ∈ Icc θlo θhi :=
  ⟨le_max_left _ _, max_le hθ (min_le_right _ _)⟩

/-- The clamp is the identity on `Θ`. -/
theorem shocksClamp_of_mem {t : ℝ} (ht : t ∈ Icc θlo θhi) : shocksClamp θlo θhi t = t := by
  simp [shocksClamp, ht.1, ht.2]

/-- The clamp is continuous. -/
theorem continuous_shocksClamp : Continuous (shocksClamp θlo θhi) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The ratio `θ′/θ̃` (both clamped to `Θ`). -/
noncomputable def shocksRatio (θlo θhi θ' θt : ℝ) : ℝ :=
  shocksClamp θlo θhi θ' / shocksClamp θlo θhi θt

/-- `θ′/θ̃ ∈ [θ̲/θ̄, θ̄/θ̲]`. -/
theorem shocksRatio_mem (h0 : 0 < θlo) (hθ : θlo ≤ θhi) (θ' θt : ℝ) :
    shocksRatio θlo θhi θ' θt ∈ Icc (θlo / θhi) (θhi / θlo) := by
  have h1 := shocksClamp_mem hθ θ'
  have h2 := shocksClamp_mem hθ θt
  have h3 : 0 < shocksClamp θlo θhi θt := h0.trans_le h2.1
  exact ⟨div_le_div₀ (h0.le.trans h1.1) h1.1 h3 h2.2,
    div_le_div₀ (h0.le.trans hθ) h1.2 h0 h2.1⟩

/-- `θ′/θ̃` is continuous in `(θ′, θ̃)`. -/
theorem continuous_shocksRatio (h0 : 0 < θlo) :
    Continuous fun p : ℝ × ℝ => shocksRatio θlo θhi p.1 p.2 :=
  (continuous_shocksClamp.comp continuous_fst).div (continuous_shocksClamp.comp continuous_snd)
    fun _ => (h0.trans_le (le_max_left _ _)).ne'

variable {Z : Type*} {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- The integrand of (4), `φ[(θ′/θ̃) ζ⁻¹(f(z′))]`, at `θ̃` and `ω = (θ′, z′)`. -/
noncomputable def shocksIntegrand (L : ℝ) (H' V' : ℝ → ℝ) (θlo θhi : ℝ) (f : Z → ℝ) (θt : ℝ)
    (ω : ℝ × Z) : ℝ :=
  olgPhi V' (shocksRatio θlo θhi ω.1 θt * olgZetaInv L H' (f ω.2))

/-- `φ_f(θ̃) = ∫ φ[(θ′/θ̃) ζ⁻¹(f(z′))] dμ(θ′, z′)` (p. 537), `μ` the law of `(θ′, z′)`. -/
noncomputable def shocksPhiF [MeasurableSpace Z] (L : ℝ) (H' V' : ℝ → ℝ) (θlo θhi : ℝ)
    (μ : Measure (ℝ × Z))
    (f : Z → ℝ) (θt : ℝ) : ℝ :=
  ∫ ω, shocksIntegrand L H' V' θlo θhi f θt ω ∂μ

/-- The operator (4), `(Tf)(z) = ∫ φ_f(θ̃) G(dθ̃|z)`, with `ν z = G(·|z)`. -/
noncomputable def shocksOpT [MeasurableSpace Z] (L : ℝ) (H' V' : ℝ → ℝ) (θlo θhi : ℝ)
    (μ : Measure (ℝ × Z))
    (ν : Z → Measure ℝ) (f : Z → ℝ) (z : Z) : ℝ :=
  ∫ θt, shocksPhiF L H' V' θlo θhi μ f θt ∂ν z

/-- The integrand is the OLG kernel `olgG` at the ratio `r = θ′/θ̃ ∈ [θ̲/θ̄, θ̄/θ̲]`. -/
theorem shocksIntegrand_eq_olgG (h0 : 0 < θlo) (hθ : θlo ≤ θhi) (f : Z → ℝ) (θt : ℝ)
    (ω : ℝ × Z) :
    shocksIntegrand L H' V' θlo θhi f θt ω =
      olgG L H' V' (⟨_, shocksRatio_mem h0 hθ ω.1 θt⟩ : Icc (θlo / θhi) (θhi / θlo))
        ⟨_, shocksRatio_mem h0 hθ ω.1 θt⟩ (f ω.2) :=
  rfl

variable [MeasurableSpace Z] in
/-- **The zero fixed point.** `T0 = 0`, since `ζ⁻¹(0) = 0` and `φ(0) = 0`. -/
theorem shocksOpT_zero (hH : Assumption17_1H L H H' H'') (μ : Measure (ℝ × Z))
    (ν : Z → Measure ℝ) (z : Z) : shocksOpT L H' V' θlo θhi μ ν (fun _ => 0) z = 0 := by
  simp [shocksOpT, shocksPhiF, shocksIntegrand, hH.zetaInv_zero, olgPhi]

/-- The standing hypotheses for §17.6: `0 < θ̲ ≤ θ̄`, `H` as in Assumption 17.1, `V` as in the
repaired Assumption 17.1 (`V` continuous on `ℝ₊`, `C²` on `ℝ₊₊`), and `l₀ ∈ (0, L)` with
`H'(l₀) < C = (θ̲/θ̄) V'((θ̄/θ̲) L)` (the manual's constant `C`, Exercise 17.9). -/
structure ShocksBounds (L θlo θhi l₀ : ℝ) (H H' H'' V V' V'' : ℝ → ℝ) : Prop where
  θlo_pos : 0 < θlo
  θlo_le : θlo ≤ θhi
  hH : Assumption17_1H L H H' H''
  hV : Assumption17_1VR V V' V''
  l₀_mem : l₀ ∈ Ioo 0 L
  l₀_lt : H' l₀ < θlo / θhi * V' (θhi / θlo * L)

/-- A suitable `l₀` always exists. -/
theorem shocksBounds_exists (h0 : 0 < θlo) (hθ : θlo ≤ θhi) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') : ∃ l₀, ShocksBounds L θlo θhi l₀ H H' H'' V V' V'' := by
  have hC : 0 < θlo / θhi * V' (θhi / θlo * L) :=
    mul_pos (div_pos h0 (h0.trans_le hθ)) (hV.V'_pos (mul_pos (div_pos (h0.trans_le hθ) h0)
      hH.L_pos))
  obtain ⟨l₀, hl₀, hlt⟩ := hH.exists_H'_lt hC
  exact ⟨l₀, h0, hθ, hH, hV, hl₀, hlt⟩

namespace ShocksBounds

variable {l₀ l : ℝ} (hS : ShocksBounds L θlo θhi l₀ H H' H'' V V' V'')
include hS

/-- `0 < θ̲/θ̄ ≤ θ̄/θ̲`. -/
theorem ratio_bounds : 0 < θlo / θhi ∧ θlo / θhi ≤ θhi / θlo := by
  have h1 : 0 < θhi := hS.θlo_pos.trans_le hS.θlo_le
  refine ⟨div_pos hS.θlo_pos h1, ?_⟩
  rw [div_le_div_iff₀ h1 hS.θlo_pos]
  nlinarith [hS.θlo_pos, hS.θlo_le]

/-- `ζ(l) > 0` for `l ∈ (0, l₀]`. -/
theorem zeta_pos (hl : l ∈ Ioc 0 l₀) : 0 < olgZeta H' l :=
  hS.hH.zeta_pos ⟨hl.1, hl.2.trans_lt hS.l₀_mem.2⟩

/-- **(7) for §17.6** (Exercise 17.9). If `f(z′) ≥ ζ(l)`, `0 < l ≤ l₀`, then the integrand is
`≥ ζ(l)`. -/
theorem integrand_ge (hl : l ∈ Ioc 0 l₀) {f : Z → ℝ} {θt : ℝ} {ω : ℝ × Z}
    (hf : olgZeta H' l ≤ f ω.2) : olgZeta H' l ≤ shocksIntegrand L H' V' θlo θhi f θt ω := by
  rw [shocksIntegrand_eq_olgG hS.θlo_pos hS.θlo_le]
  exact olgG_ge hS.ratio_bounds.1 hS.ratio_bounds.2 hS.hH hS.hV hS.l₀_mem hS.l₀_lt hl hf _ _

/-- The integrand is bounded above on `{f ≥ ζ(l)}`: its argument lies in
`[(θ̲/θ̄) l, (θ̄/θ̲) L]`. -/
theorem exists_integrand_le (hl : l ∈ Ioc 0 l₀) : ∃ B, 0 < B ∧ ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B := by
  obtain ⟨ha, hab⟩ := hS.ratio_bounds
  have hl' : l ∈ Ioo 0 L := ⟨hl.1, hl.2.trans_lt hS.l₀_mem.2⟩
  have hK : IsCompact (Icc (θlo / θhi * l) (θhi / θlo * L)) := isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hS.hV.phi_continuousOn.mono
    fun y hy => (mul_pos ha hl.1).trans_le hy.1)
  have hBpos : 0 < max B (olgZeta H' l) + 1 := by
    have := le_max_right B (olgZeta H' l)
    linarith [hS.zeta_pos hl]
  refine ⟨max B (olgZeta H' l) + 1, hBpos, fun f θt ω hf => ?_⟩
  have hy0 : 0 ≤ f ω.2 := (hS.zeta_pos hl).le.trans hf
  have hm := hS.hH.zetaInv_mem hy0
  have hlm : l ≤ olgZetaInv L H' (f ω.2) := by
    have := hS.hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 (hS.zeta_pos hl).le)
      (mem_Ici.2 hy0) hf
    rwa [hS.hH.zetaInv_zeta (Ioo_subset_Ico_self hl')] at this
  have hr := shocksRatio_mem hS.θlo_pos hS.θlo_le ω.1 θt
  have hmem : shocksRatio θlo θhi ω.1 θt * olgZetaInv L H' (f ω.2) ∈
      Icc (θlo / θhi * l) (θhi / θlo * L) :=
    ⟨mul_le_mul hr.1 hlm hl.1.le (ha.le.trans hr.1),
      mul_le_mul hr.2 hm.2.le hm.1 (ha.le.trans hab)⟩
  have := hB _ hmem
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans ((le_max_left _ _).trans (le_add_of_nonneg_right
    zero_le_one)))

variable [TopologicalSpace Z] in
/-- The integrand is jointly continuous in `(θ̃, θ′, z′)` for continuous `f > 0`. -/
theorem continuous_integrand {f : Z → ℝ} (hfc : Continuous f) (hf : ∀ z, 0 < f z) :
    Continuous fun p : ℝ × (ℝ × Z) => shocksIntegrand L H' V' θlo θhi f p.1 p.2 := by
  have h1 : Continuous fun p : ℝ × (ℝ × Z) => shocksRatio θlo θhi p.2.1 p.1 :=
    (continuous_shocksRatio hS.θlo_pos).comp ((continuous_fst.comp continuous_snd).prodMk
      continuous_fst)
  have h2 : Continuous fun p : ℝ × (ℝ × Z) => olgZetaInv L H' (f p.2.2) :=
    hS.hH.zetaInv_continuousOn.comp_continuous (hfc.comp (continuous_snd.comp continuous_snd))
      fun p => mem_Ici.2 (hf _).le
  refine hS.hV.phi_continuousOn.comp_continuous (h1.mul h2) fun p => ?_
  exact mul_pos (hS.ratio_bounds.1.trans_le (shocksRatio_mem hS.θlo_pos hS.θlo_le _ _).1)
    (hS.hH.zetaInv_pos (hf _))

variable [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] {B : ℝ}
  {f : Z → ℝ}

omit [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
/-- With `0 < l ≤ l₀` and `f ≥ ζ(l)`, `|integrand| ≤ B`. -/
theorem abs_integrand_le (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (θt : ℝ) (ω : ℝ × Z) :
    |shocksIntegrand L H' V' θlo θhi f θt ω| ≤ B := by
  rw [abs_of_pos ((hS.zeta_pos hl).trans_le (hS.integrand_ge hl (hfl ω.2)))]
  exact hB f θt ω (hfl ω.2)

/-- The integrand is integrable in `ω` for every finite `μ`. -/
theorem integrable_integrand (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsFiniteMeasure μ] (θt : ℝ) :
    Integrable (fun ω => shocksIntegrand L H' V' θlo θhi f θt ω) μ := by
  have hpos : ∀ z, 0 < f z := fun z => (hS.zeta_pos hl).trans_le (hfl z)
  refine (integrable_const B).mono' ?_ (ae_of_all _ fun ω => ?_)
  · exact ((hS.continuous_integrand hfc hpos).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hS.abs_integrand_le hl hB hfl θt ω

/-- `ζ(l) ≤ φ_f ≤ B`. -/
theorem phiF_mem (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] (θt : ℝ) :
    shocksPhiF L H' V' θlo θhi μ f θt ∈ Icc (olgZeta H' l) B := by
  have hi := hS.integrable_integrand hl hB hfc hfl μ θt
  constructor
  · have := integral_mono (integrable_const (olgZeta H' l)) hi fun ω =>
      hS.integrand_ge hl (hfl ω.2) (θt := θt)
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this
  · have := integral_mono hi (integrable_const B) fun ω => hB f θt ω (hfl ω.2)
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this

/-- `φ_f` is continuous (dominated convergence). -/
theorem continuous_phiF (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] :
    Continuous (shocksPhiF L H' V' θlo θhi μ f) := by
  have hpos : ∀ z, 0 < f z := fun z => (hS.zeta_pos hl).trans_le (hfl z)
  have hc := hS.continuous_integrand hfc hpos
  refine continuous_of_dominated (bound := fun _ => B) (fun θt => ?_) (fun θt => ae_of_all _
    fun ω => ?_) (integrable_const B) (ae_of_all _ fun ω => ?_)
  · exact (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hS.abs_integrand_le hl hB hfl θt ω
  · exact hc.comp (continuous_id.prodMk continuous_const)

/-- `φ_f` as a bounded continuous function. -/
noncomputable def phiFBCF (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] : ℝ →ᵇ ℝ :=
  ofNormedAddCommGroup (shocksPhiF L H' V' θlo θhi μ f) (hS.continuous_phiF hl hB hfc hfl μ) B
    fun θt => by
      have h := hS.phiF_mem hl hB hfc hfl μ θt
      rw [Real.norm_eq_abs, abs_of_pos ((hS.zeta_pos hl).trans_le h.1)]
      exact h.2

/-- Evaluation of `phiFBCF`. -/
theorem phiFBCF_apply (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ] (θt : ℝ) :
    hS.phiFBCF hl hB hfc hfl μ θt = shocksPhiF L H' V' θlo θhi μ f θt :=
  rfl

/-- **Exercise 17.11, steps 1–2** (and the first step of Exercise 17.9): with
`D = [ζ(l), B]`, `0 < l ≤ l₀`, `T` maps continuous `D`-valued `f` to continuous `D`-valued `Tf`
(continuity from the weak continuity of `z ↦ G(·|z)`, Exercise 17.8b). -/
theorem opT_mem (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B) (hfc : Continuous f)
    (hfl : ∀ z, olgZeta H' l ≤ f z) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z) :
    Continuous (shocksOpT L H' V' θlo θhi μ ν f) ∧
      ∀ z, shocksOpT L H' V' θlo θhi μ ν f z ∈ Icc (olgZeta H' l) B := by
  refine ⟨hν (hS.phiFBCF hl hB hfc hfl μ), fun z => ⟨?_, ?_⟩⟩
  · have := integral_mono (integrable_const (olgZeta H' l))
      ((hS.phiFBCF hl hB hfc hfl μ).integrable (ν z)) fun θt =>
        (hS.phiF_mem hl hB hfc hfl μ θt).1
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this
  · have := integral_mono ((hS.phiFBCF hl hB hfc hfl μ).integrable (ν z))
      (integrable_const B) fun θt => (hS.phiF_mem hl hB hfc hfl μ θt).2
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this

omit [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
/-- **Exercise 17.9, the mean-value step.** Under the repaired Assumption 17.2, for
`e^g, e^h ≥ ζ(l)` the log-integrand is `β`-Lipschitz in the log-argument:
`|ln φ[(θ′/θ̃) ζ⁻¹(e^{g(z′)})] − ln φ[(θ′/θ̃) ζ⁻¹(e^{h(z′)})]| ≤ β |g(z′) − h(z′)|`. -/
theorem abs_log_integrand_sub_le {β : ℝ} (h2 : Assumption17_2R β V' V'') (hl : l ∈ Ioc 0 l₀)
    {g h : Z → ℝ} (hg : ∀ z, olgZeta H' l ≤ Real.exp (g z))
    (hh : ∀ z, olgZeta H' l ≤ Real.exp (h z)) (θt : ℝ) (ω : ℝ × Z) :
    |Real.log (shocksIntegrand L H' V' θlo θhi (fun z => Real.exp (g z)) θt ω) -
      Real.log (shocksIntegrand L H' V' θlo θhi (fun z => Real.exp (h z)) θt ω)| ≤
        β * |g ω.2 - h ω.2| := by
  obtain ⟨ha, hab⟩ := hS.ratio_bounds
  have hzl := hS.zeta_pos hl
  have hyp := olgG_hyp ha hab hS.hH hS.hV hS.l₀_mem hS.l₀_lt hl
    (κ := Kernel.deterministic (id : Icc (θlo / θhi) (θhi / θlo) → _) measurable_id)
    isFellerKernel_deterministic_id
  rw [shocksIntegrand_eq_olgG hS.θlo_pos hS.θlo_le, shocksIntegrand_eq_olgG hS.θlo_pos hS.θlo_le]
  exact abs_log_G_sub_le hyp (fun y hy => hzl.trans_le hy)
    (fun x x' y hy => (olgG_hasDerivAt ha hS.hH hS.hV x x' (hzl.trans_le hy)).hasDerivWithinAt)
    (fun x x' y hy => olgG_elasticity_le ha hS.hH hS.hV h2 x x' (hzl.trans_le hy)) _ _
    ⟨_, hg ω.2, Real.log_exp _⟩ ⟨_, hh ω.2, Real.log_exp _⟩

/-- **Exercise 17.9, integrated.** If `|g − h| ≤ d` then
`T(e^g) ≤ e^{βd} T(e^h)` pointwise. (This is the book's weighted-average step; the weights `w`
of the manual are not needed.) -/
theorem opT_exp_le {β : ℝ} (hβ : 0 ≤ β) (h2 : Assumption17_2R β V' V'') (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    {g h : Z → ℝ} (hgc : Continuous g) (hhc : Continuous h)
    (hg : ∀ z, olgZeta H' l ≤ Real.exp (g z)) (hh : ∀ z, olgZeta H' l ≤ Real.exp (h z))
    {d : ℝ} (hd : ∀ z, |g z - h z| ≤ d) (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)] (z : Z) :
    shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (g z)) z ≤
      Real.exp (β * d) * shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (h z)) z := by
  have hzl := hS.zeta_pos hl
  have hegc : Continuous fun z => Real.exp (g z) := Real.continuous_exp.comp hgc
  have hehc : Continuous fun z => Real.exp (h z) := Real.continuous_exp.comp hhc
  have hpt : ∀ θt ω, shocksIntegrand L H' V' θlo θhi (fun z => Real.exp (g z)) θt ω ≤
      Real.exp (β * d) * shocksIntegrand L H' V' θlo θhi (fun z => Real.exp (h z)) θt ω :=
    fun θt ω => by
      have hA := hzl.trans_le (hS.integrand_ge hl (f := fun z => Real.exp (g z)) (hg ω.2)
        (θt := θt))
      have hB' := hzl.trans_le (hS.integrand_ge hl (f := fun z => Real.exp (h z)) (hh ω.2)
        (θt := θt))
      have := (abs_sub_le_iff.1 (hS.abs_log_integrand_sub_le h2 hl hg hh θt ω)).1
      have h3 : β * |g ω.2 - h ω.2| ≤ β * d := mul_le_mul_of_nonneg_left (hd ω.2) hβ
      rw [← Real.exp_log hA, ← Real.exp_log hB', ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
  have hφ : ∀ θt, shocksPhiF L H' V' θlo θhi μ (fun z => Real.exp (g z)) θt ≤
      Real.exp (β * d) * shocksPhiF L H' V' θlo θhi μ (fun z => Real.exp (h z)) θt := fun θt => by
    simp only [shocksPhiF]
    rw [← integral_const_mul]
    exact integral_mono (hS.integrable_integrand hl hB hegc hg μ θt)
      ((hS.integrable_integrand hl hB hehc hh μ θt).const_mul _) (hpt θt)
  simp only [shocksOpT]
  rw [← integral_const_mul]
  exact integral_mono ((hS.phiFBCF hl hB hegc hg μ).integrable (ν z))
    (((hS.phiFBCF hl hB hehc hh μ).integrable (ν z)).const_mul _) hφ

end ShocksBounds

/-! ### Proposition 6 by the contraction mapping theorem -/

namespace ShocksBounds

variable {l₀ l B : ℝ} (hS : ShocksBounds L θlo θhi l₀ H H' H'' V V' V'')
  [MetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
include hS

/-- `T(e^g) ∈ [ζ(l), B]` and is continuous for `g ∈ F̂`. -/
theorem opT_exp_mem (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z)
    (g : olgF Z (olgDhat (Ici (olgZeta H' l)))) :
    Continuous (shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (g.1 z))) ∧
      ∀ z, shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (g.1 z)) z ∈
        Icc (olgZeta H' l) B :=
  hS.opT_mem hl hB (f := fun z => Real.exp (g.1 z)) (Real.continuous_exp.comp g.1.continuous)
    (fun z => exp_mem_of_mem_olgDhat (fun _ hy => (hS.zeta_pos hl).trans_le hy) (g.2 z)) μ ν hν

variable [CompactSpace Z]

/-- The logarithmic operator `T̂g = ln T(e^g)` of Exercise 17.9, on
`F̂ = {g ∈ C(Z) : e^g ≥ ζ(l)}` (`D = [ζ(l), ∞)`, `0 < l ≤ l₀`). -/
noncomputable def opThat (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z)
    (g : olgF Z (olgDhat (Ici (olgZeta H' l)))) : olgF Z (olgDhat (Ici (olgZeta H' l))) :=
  ⟨mkOfCompact ⟨fun z => Real.log (shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (g.1 z)) z),
    (hS.opT_exp_mem hl hB μ ν hν g).1.log fun z =>
      ((hS.zeta_pos hl).trans_le ((hS.opT_exp_mem hl hB μ ν hν g).2 z).1).ne'⟩,
    fun z => ⟨_, ((hS.opT_exp_mem hl hB μ ν hν g).2 z).1, rfl⟩⟩

/-- Evaluation of `opThat`. -/
theorem opThat_apply (hl : l ∈ Ioc 0 l₀) (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
    olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z)
    (g : olgF Z (olgDhat (Ici (olgZeta H' l)))) (z : Z) :
    (hS.opThat hl hB μ ν hν g).1 z =
      Real.log (shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (g.1 z)) z) :=
  rfl

/-- **Exercise 17.9** (p. 535): under the repaired Assumption 17.2, `T̂` is a contraction of
modulus `β` on `F̂`. (The manual's final lines drop `β` and write `sup(g − h)` for
`sup|g − h|`.) -/
theorem ex_17_9 {β : ℝ} (h2 : Assumption17_2R β V' V'') (hl : l ∈ Ioc 0 l₀)
    (hB : ∀ (f : Z → ℝ) θt (ω : ℝ × Z),
      olgZeta H' l ≤ f ω.2 → shocksIntegrand L H' V' θlo θhi f θt ω ≤ B)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z) :
    LipschitzWith β.toNNReal (hS.opThat hl hB μ ν hν) := by
  have hβ := h2.β_nonneg
  have hDpos : Ici (olgZeta H' l) ⊆ Ioi 0 := fun y hy => (hS.zeta_pos hl).trans_le hy
  refine LipschitzWith.of_dist_le_mul fun g h => ?_
  simp only [Subtype.dist_eq]
  rw [Real.coe_toNNReal β hβ, BoundedContinuousFunction.dist_le (mul_nonneg hβ dist_nonneg)]
  intro z
  have hg : ∀ z, olgZeta H' l ≤ Real.exp (g.1 z) := fun z => exp_mem_of_mem_olgDhat hDpos (g.2 z)
  have hh : ∀ z, olgZeta H' l ≤ Real.exp (h.1 z) := fun z => exp_mem_of_mem_olgDhat hDpos (h.2 z)
  have hd1 : ∀ z, |g.1 z - h.1 z| ≤ dist g.1 h.1 := fun z => by
    rw [← Real.dist_eq]; exact dist_coe_le_dist z
  have hd2 : ∀ z, |h.1 z - g.1 z| ≤ dist g.1 h.1 := fun z => by
    rw [abs_sub_comm]; exact hd1 z
  have hTg := ((hS.opT_exp_mem hl hB μ ν hν g).2 z).1
  have hTh := ((hS.opT_exp_mem hl hB μ ν hν h).2 z).1
  have hpg := (hS.zeta_pos hl).trans_le hTg
  have hph := (hS.zeta_pos hl).trans_le hTh
  have e1 := hS.opT_exp_le hβ h2 hl hB g.1.continuous h.1.continuous hg hh hd1 μ ν z
  have e2 := hS.opT_exp_le hβ h2 hl hB h.1.continuous g.1.continuous hh hg hd2 μ ν z
  have L1 := Real.log_le_log hpg e1
  have L2 := Real.log_le_log hph e2
  rw [Real.log_mul (Real.exp_pos _).ne' hph.ne', Real.log_exp] at L1
  rw [Real.log_mul (Real.exp_pos _).ne' hpg.ne', Real.log_exp] at L2
  rw [opThat_apply, opThat_apply, Real.dist_eq, abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Lemma 17.2 for §17.6**: for `0 < l ≤ l₀`, `T` has exactly one fixed point among the
continuous `f ≥ ζ(l)`. -/
theorem unique_fixedPoint_ge {β : ℝ} (h2 : Assumption17_2R β V' V'') (hl : l ∈ Ioc 0 l₀)
    (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z) [Nonempty Z] :
    ∃! f : Z →ᵇ ℝ, (∀ z, olgZeta H' l ≤ f z) ∧
      ∀ z, f z = shocksOpT L H' V' θlo θhi μ ν f z := by
  obtain ⟨B, -, hB⟩ := hS.exists_integrand_le (Z := Z) hl
  have hDpos : Ici (olgZeta H' l) ⊆ Ioi 0 := fun y hy => (hS.zeta_pos hl).trans_le hy
  have : CompleteSpace (olgF Z (olgDhat (Ici (olgZeta H' l)))) := ex_17_4b isClosed_Ici hDpos
  have : Nonempty (olgF Z (olgDhat (Ici (olgZeta H' l)))) :=
    ⟨⟨const Z (Real.log (olgZeta H' l)), fun _ => ⟨_, mem_Ici.2 le_rfl, rfl⟩⟩⟩
  have hK : ContractingWith β.toNNReal (hS.opThat hl hB μ ν hν) :=
    ⟨Real.toNNReal_lt_one.2 h2.β_lt_one, hS.ex_17_9 h2 hl hB μ ν hν⟩
  set gs := ContractingWith.fixedPoint _ hK
  have hfix : hS.opThat hl hB μ ν hν gs = gs := ContractingWith.fixedPoint_isFixedPt hK
  have hmem : ∀ z, olgZeta H' l ≤ Real.exp (gs.1 z) := fun z =>
    exp_mem_of_mem_olgDhat hDpos (gs.2 z)
  let fs : Z →ᵇ ℝ := mkOfCompact ⟨fun z => Real.exp (gs.1 z),
    Real.continuous_exp.comp gs.1.continuous⟩
  have hfs : ∀ z, fs z = Real.exp (gs.1 z) := fun _ => rfl
  refine ⟨fs, ⟨fun z => by rw [hfs]; exact hmem z, fun z => ?_⟩, ?_⟩
  · have h1 : (hS.opThat hl hB μ ν hν gs).1 z = gs.1 z := by rw [hfix]
    rw [opThat_apply] at h1
    have hpos : 0 < shocksOpT L H' V' θlo θhi μ ν (fun z => Real.exp (gs.1 z)) z :=
      (hS.zeta_pos hl).trans_le ((hS.opT_mem hl hB (f := fun z => Real.exp (gs.1 z))
        (Real.continuous_exp.comp gs.1.continuous)
        hmem μ ν hν).2 z).1
    rw [hfs, ← h1, Real.exp_log hpos]
    rfl
  · rintro f ⟨hfD, hfix'⟩
    have hfpos : ∀ z, 0 < f z := fun z => (hS.zeta_pos hl).trans_le (hfD z)
    let lf : olgF Z (olgDhat (Ici (olgZeta H' l))) := ⟨mkOfCompact ⟨fun z => Real.log (f z),
      f.continuous.log fun z => (hfpos z).ne'⟩, fun z => ⟨f z, hfD z, rfl⟩⟩
    have hexp : (fun z => Real.exp (lf.1 z)) = ⇑f := by
      ext z; exact Real.exp_log (hfpos z)
    have hlf : hS.opThat hl hB μ ν hν lf = lf := by
      apply Subtype.ext
      ext z
      rw [opThat_apply, hexp, ← hfix' z]
      rfl
    have : lf = gs := ContractingWith.fixedPoint_unique hK hlf
    ext z
    rw [hfs, ← this]
    change f z = Real.exp (Real.log (f z))
    rw [Real.exp_log (hfpos z)]

end ShocksBounds

/-- **Proposition 6** (p. 535), corrected. Let `H` satisfy Assumption 17.1, `V` the repaired
Assumptions 17.1 and 17.2 (`Assumption17_1VR`, `Assumption17_2R`), `0 < θ̲ ≤ θ̄`, `Z` a compact
metric space, `μ` any probability law of `(θ′, z′)` and `z ↦ ν z = G(·|z)` weakly continuous
probability measures (Exercise 17.8b). Then `T` of (4) has exactly one **strictly positive**
continuous fixed point. (By `proposition_6_zero_fixedPoint` the zero function is another fixed
point, so "a unique fixed point in `C(Z)`" is false; see `proposition_6_counterexample`.)

The uniqueness among strictly positive fixed points uses the sets `[ζ(l), ∞)`, `0 < l ≤ l₀`, as
in `proposition_2`: a positive continuous fixed point has a positive minimum on compact `Z`. -/
theorem proposition_6 [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] [Nonempty Z] (h0 : 0 < θlo) (hθ : θlo ≤ θhi)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'') {β : ℝ}
    (h2 : Assumption17_2R β V' V'') (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z) :
    ∃! f : Z →ᵇ ℝ, (∀ z, 0 < f z) ∧ ∀ z, f z = shocksOpT L H' V' θlo θhi μ ν f z := by
  obtain ⟨l₀, hS⟩ := shocksBounds_exists h0 hθ hH hV
  obtain ⟨f₀, ⟨hf₀D, hf₀fix⟩, -⟩ := hS.unique_fixedPoint_ge h2 ⟨hS.l₀_mem.1, le_rfl⟩ μ ν hν
  have hz0 := hS.zeta_pos ⟨hS.l₀_mem.1, le_rfl⟩
  refine ⟨f₀, ⟨fun z => hz0.trans_le (hf₀D z), hf₀fix⟩, ?_⟩
  rintro f ⟨hfpos, hffix⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn univ_nonempty f.continuous.continuousOn
  set l := min l₀ (olgZetaInv L H' (f m))
  have hl : l ∈ Ioc 0 l₀ := ⟨lt_min hS.l₀_mem.1 (hH.zetaInv_pos (hfpos m)), min_le_left _ _⟩
  have hlL : l ∈ Ico 0 L := ⟨hl.1.le, hl.2.trans_lt hS.l₀_mem.2⟩
  have hzl : olgZeta H' l ≤ f m :=
    calc olgZeta H' l ≤ olgZeta H' (olgZetaInv L H' (f m)) :=
          hH.zeta_strictMonoOn.monotoneOn hlL (hH.zetaInv_mem (hfpos m).le) (min_le_right _ _)
      _ = f m := hH.zeta_zetaInv (hfpos m).le
  have hzl0 : olgZeta H' l ≤ olgZeta H' l₀ :=
    hH.zeta_strictMonoOn.monotoneOn hlL (Ioo_subset_Ico_self hS.l₀_mem) (min_le_left _ _)
  obtain ⟨g, -, hg⟩ := hS.unique_fixedPoint_ge h2 hl μ ν hν
  have e1 := hg f ⟨fun z => hzl.trans (isMinOn_iff.1 hm z (mem_univ z)), hffix⟩
  have e2 := hg f₀ ⟨fun z => hzl0.trans (hf₀D z), hf₀fix⟩
  rw [e1, e2]

/-- **Correction (Proposition 6: the zero fixed point).** `f ≡ 0` solves (4). -/
theorem proposition_6_zero_fixedPoint [TopologicalSpace Z] [MeasurableSpace Z]
    (hH : Assumption17_1H L H H' H'') (μ : Measure (ℝ × Z)) (ν : Z → Measure ℝ) (z : Z) :
    (0 : Z →ᵇ ℝ) z = shocksOpT L H' V' θlo θhi μ ν (0 : Z →ᵇ ℝ) z := by
  have := shocksOpT_zero (θlo := θlo) (θhi := θhi) (V' := V') hH μ ν z
  rw [BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  exact this.symm

/-- **Correction (Proposition 6, "a unique fixed point in `C(Z)`" is false).** Under the
hypotheses of `proposition_6`, `T` has (at least) two fixed points in `C(Z)`: `0` and the
strictly positive `f*`. -/
theorem proposition_6_counterexample [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] [Nonempty Z] (h0 : 0 < θlo) (hθ : θlo ≤ θhi)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'') {β : ℝ}
    (h2 : Assumption17_2R β V' V'') (μ : Measure (ℝ × Z)) [IsProbabilityMeasure μ]
    (ν : Z → Measure ℝ) [∀ z, IsProbabilityMeasure (ν z)]
    (hν : ∀ h : ℝ →ᵇ ℝ, Continuous fun z => ∫ θ, h θ ∂ν z) :
    ¬ ∃! f : Z →ᵇ ℝ, ∀ z, f z = shocksOpT L H' V' θlo θhi μ ν f z := by
  rintro ⟨g, -, hg⟩
  obtain ⟨f, ⟨hfpos, hffix⟩, -⟩ := proposition_6 h0 hθ hH hV h2 μ ν hν
  have e1 := hg f hffix
  have e2 := hg 0 (proposition_6_zero_fixedPoint hH μ ν)
  obtain ⟨z⟩ := ‹Nonempty Z›
  have := hfpos z
  rw [e1, ← e2] at this
  simp at this

/-! ### Proposition 6 for the islands model -/

/-- The joint law of `(θ′, z′)`, `z′ = x′/θ′` (projected onto `Z`), when `x′ ~ ψ` and `θ′ ~ g`
are independent. -/
noncomputable def shocksJointLaw (xlo xhi θlo θhi : ℝ) (hZ : xlo / θhi ≤ xhi / θlo)
    (ψ g : ℝ → ℝ) : Measure (ℝ × Icc (xlo / θhi) (xhi / θlo)) :=
  Measure.map (fun p : ℝ × ℝ => (p.2, projIcc (xlo / θhi) (xhi / θlo) hZ (p.1 / p.2)))
    ((volume.withDensity fun x => ENNReal.ofReal (ψ x)).prod
      (volume.withDensity fun θ => ENNReal.ofReal (g θ)))

variable {xlo xhi : ℝ} {ψ g : ℝ → ℝ}

/-- A probability density gives a probability measure. -/
theorem shocks_isProbabilityMeasure_withDensity {ρ : ℝ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable ρ) (hρ1 : ∫ x, ρ x = 1) :
    IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (ρ x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hρi (ae_of_all _ hρ0), hρ1, ENNReal.ofReal_one]

/-- A function continuous on `[a, b]` and zero off it is integrable. -/
theorem shocks_integrable_of_zero_off {a b : ℝ} {f : ℝ → ℝ} (hc : ContinuousOn f (Icc a b))
    (h0 : ∀ x ∉ Icc a b, f x = 0) : Integrable f := by
  have : f = (Icc a b).indicator f := by
    ext x
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, h0 x hx]
  rw [this]
  exact (hc.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc

/-- The joint law is a probability measure. -/
theorem isProbabilityMeasure_shocksJointLaw (hA : ShocksAssumption17_5 xlo xhi θlo θhi ψ g)
    (hZ : xlo / θhi ≤ xhi / θlo) :
    IsProbabilityMeasure (shocksJointLaw xlo xhi θlo θhi hZ ψ g) := by
  have h1 := shocks_isProbabilityMeasure_withDensity hA.ψ_nonneg
    (shocks_integrable_of_zero_off hA.ψ_cont hA.ψ_zero) hA.ψ_int
  have h2 := shocks_isProbabilityMeasure_withDensity hA.g_nonneg
    (shocks_integrable_of_zero_off hA.g_cont hA.g_zero) hA.g_int
  exact (Measure.isProbabilityMeasure_map_iff (measurable_snd.prodMk
    (continuous_projIcc.measurable.comp (measurable_fst.div measurable_snd))).aemeasurable).2
    inferInstance

/-- **Proposition 6 for the islands model** (p. 535), corrected: under Assumption 17.1 for `H`,
the repaired Assumptions 17.1 and 17.2 for `V`, Assumption 17.5 with `ψ > 0` on `X` and `g > 0`
on `Θ` (so that `π > 0` on `int Z` and Exercise 17.8b applies), the operator (4) on `C(Z)`, with
`μ` the joint law of `(θ′, z′)` and `G(·|z)` the conditional law of `θ̃` given `z`, has exactly one
strictly positive continuous fixed point. -/
theorem proposition_6_islands (hA : ShocksAssumption17_5 xlo xhi θlo θhi ψ g)
    (hψ : ∀ x ∈ Icc xlo xhi, 0 < ψ x) (hg : ∀ θ ∈ Icc θlo θhi, 0 < g θ)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'') {β : ℝ}
    (h2 : Assumption17_2R β V' V'') (hZ : xlo / θhi ≤ xhi / θlo) :
    ∃! f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∀ z, 0 < f z) ∧
      ∀ z, f z = shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
        (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z := by
  have hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z :=
    fun z hz => hA.pi_pos hψ hg hz
  have := isProbabilityMeasure_shocksJointLaw hA hZ
  have : ∀ z : Icc (xlo / θhi) (xhi / θlo),
      IsProbabilityMeasure (shocksCondLaw xlo xhi θlo θhi ψ g z.1) := fun z =>
    hA.isProbabilityMeasure_condLaw' hπ z.1
  have : Nonempty (Icc (xlo / θhi) (xhi / θlo)) := ⟨⟨_, left_mem_Icc.2 hZ⟩⟩
  exact proposition_6 hA.θlo_pos hA.θlo_lt.le hH hV h2 _ _
    fun h => (hA.ex_17_8b hπ h).domRestrict

end StokeyLucasPrescott.FixedPointArguments

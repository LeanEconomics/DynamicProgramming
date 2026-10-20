/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.SchauderApplication

/-!
# Partially observed shocks: the information structure

SLP §17.6, pp. 531–537: the islands model with monetary shocks `x ∈ X = [x̲, x̄]` and real
shocks `θ ∈ Θ = [θ̲, θ̄]`, independent with densities `ψ`, `g`, and the ratio
`z = x/θ ∈ Z = [x̲/θ̄, x̄/θ̲]`.
Densities are functions on `ℝ` vanishing off `X`, `Θ`; integrals are Lebesgue integrals on `ℝ`.

* **Assumption 17.5** (`ShocksAssumption17_5`, p. 532). `shocksPi` is the density
  `π(z) = ∫ g(θ) θ ψ(zθ) dθ` of `z` (p. 534; `integral_pi`: it integrates to `1`).
* `shocksA`, `shocksB`: `a(z) = max{x̲/z, θ̲}`, `b(z) = min{x̄/z, θ̄}` ((5), p. 536);
  `mem_Icc_shocksA_shocksB_iff`: `θ ∈ Θ ∧ zθ ∈ X ↔ θ ∈ [a(z), b(z)]`.
* **Exercise 17.8a**, corrected. `ShocksAssumption17_5.joint`: the joint density of `(θ, z)` is
  `g(θ) θ ψ(zθ)` (change of variables `x = zθ` and Fubini). `ex_17_8a_disintegration`:
  `E h(θ, z) = ∫ π(z) ∫ h(θ, z) g(θ|z) dθ dz` with `g(θ|z) = g(θ) θ ψ(zθ)/π(z)`
  (`shocksCondDens`), so `g(·|z)` is the conditional density; `ex_17_8a`: where `π(z) > 0` it is a
  probability density vanishing off `[a(z), b(z)]` and continuous on `[a(z), b(z)]`.
* `shocksCondLaw`: the conditional law `G(·|z)` (density `g(·|z)` on `int Z`, `δ_{θ̄}` at `z̲`,
  `δ_{θ̲}` at `z̄`). `ShocksAssumption17_5.pi_pos`: `π > 0` on `int Z` if `ψ > 0` on `X` and
  `g > 0` on `Θ`.
* **Exercise 17.8b** (`ShocksAssumption17_5.ex_17_8b`): if `π > 0` on `int Z`, `z ↦ G(·|z)` is
  weakly continuous on `Z` (dominated convergence inside, shrinking supports at the endpoints).
* **Exercise 17.10** (`ex_17_10`, p. 536; no answer in the manual): `G(·|z_n) → G(·|z̲)` weakly but
  `‖G(·|z_n) − G(·|z̲)‖_TV ≥ 1`, and `G(·|z_n)` has no total-variation limit at all.
* **Assumption 17.6** (uniform `Ψ`, `G`): `shocksUnif`, `shocksUnif_assumption17_5`.
* **Exercise 17.12, corrected** (`ex_17_12`): under Assumption 17.6, `g(θ|z) = 2θ/(b(z)² − a(z)²)`
  on `[a(z), b(z)]`.
* The NOTE on p. 533: `p533_ratio_of_price` (what the argument proves) and `p533_counterexample`.

**Correction (Exercise 17.12 is false).** Under Assumption 17.6 the conditional law of `θ` given
`z` has density proportional to `θ` on `[a(z), b(z)]` (the Jacobian of `x = zθ`; the book's own
`π(z)` contains it), not the uniform density. `ex_17_12_counterexample`: with `x ~ U[1, 2]`,
`θ ~ U[1, 3/2]`, the uniform family does not disintegrate the joint law (for
`h = θ·1{z ∈ [1, 4/3]}` it gives `25/48` instead of `19/36`). The manual's "proof" treats `x` as
uniform along the null set `{x = zθ}` (a Borel–Kolmogorov-type error). The support `[a(z), b(z)]`
in (5) is correct. Consequently the weights in (6a), (7) and in `J` of Proposition 8 must be
`2θ/(b² − a²)`; Proposition 7 and Exercise 17.14d are proved with these weights in
`FixedPointArguments.ShocksSchauder` and `FixedPointArguments.ShocksMonotone`.

**Correction (manual, Exercise 17.8a).** The manual's density `g(θ)ψ(θz)/π(z)` omits the factor
`θ` and does not integrate to `1` (`ex_17_8a_manual_counterexample`: `4/5` in the example at
`z = 1`).

**Correction (Exercise 17.8a, hypotheses).** (i) `g(·|z)` needs `π(z) > 0`, which Assumption 17.5
does not guarantee at interior points: `ex_17_8a_pi_zero_counterexample` (`π(3/4) = 0` with
`Z = [2/3, 2]`); positivity of `ψ` on `X` and `g` on `Θ` suffices (`pi_pos`). (ii) "`G(·|z)` has a
continuous density" is false when, as Assumption 17.6 requires, the densities are continuous only on
`X` and `Θ`: `ex_17_8a_continuity_counterexample` (in the example at `z = 4/5`, `g(·|z)` jumps at
`a(z) = 5/4 ∈ int Θ`, and no function continuous on `Θ` equals it a.e.). The density is continuous
on `[a(z), b(z)]`. (iii) Part (b) needs the endpoint convention `G(·|z̲) = δ_{θ̄}`,
`G(·|z̄) = δ_{θ̲}` (the only possible weak limits).

**Correction (p. 533).** The argument shows only that equal prices imply equal ratios `x/θ`
(`p533_ratio_of_price`); it does not show that an equilibrium price is a function `ρ(x/θ)`:
`p533_counterexample` satisfies every premise used there, yet the price is not a function of
`x/θ`. The existence results that follow concern equilibria of the form `ρ(x/θ)` only (whether a
price revealing more than `x/θ` can satisfy (1) is not settled here).
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology BoundedContinuousFunction

/-- **Assumption 17.5** (p. 532). The monetary shock `x` lies in `X = [x̲, x̄]`, `0 < x̲ < x̄`, and
the real shock `θ` in `Θ = [θ̲, θ̄]`, `0 < θ̲ < θ̄ < 2`; `x` and `θ` are independent with densities
`ψ` and `g` (taken on all of `ℝ`, zero off `X` and `Θ`), continuous on `X` and `Θ`. -/
structure ShocksAssumption17_5 (xlo xhi θlo θhi : ℝ) (ψ g : ℝ → ℝ) : Prop where
  xlo_pos : 0 < xlo
  xlo_lt : xlo < xhi
  θlo_pos : 0 < θlo
  θlo_lt : θlo < θhi
  θhi_lt : θhi < 2
  ψ_nonneg : ∀ x, 0 ≤ ψ x
  g_nonneg : ∀ θ, 0 ≤ g θ
  ψ_zero : ∀ x ∉ Icc xlo xhi, ψ x = 0
  g_zero : ∀ θ ∉ Icc θlo θhi, g θ = 0
  ψ_cont : ContinuousOn ψ (Icc xlo xhi)
  g_cont : ContinuousOn g (Icc θlo θhi)
  ψ_int : ∫ x, ψ x = 1
  g_int : ∫ θ, g θ = 1

/-- The density of `z = x/θ` (p. 534): `π(z) = ∫ g(θ) θ ψ(zθ) dθ`. -/
noncomputable def shocksPi (ψ g : ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ, g θ * θ * ψ (z * θ)

/-- The lower end `a(z) = max{x̲/z, θ̲}` of the support of `G(·|z)` ((5), p. 536). -/
noncomputable def shocksA (xlo θlo z : ℝ) : ℝ := max (xlo / z) θlo

/-- The upper end `b(z) = min{x̄/z, θ̄}` of the support of `G(·|z)` ((5), p. 536). -/
noncomputable def shocksB (xhi θhi z : ℝ) : ℝ := min (xhi / z) θhi

/-- The conditional density `g(θ|z) = g(θ) θ ψ(zθ)/π(z)` of `θ` given `z = x/θ` (Exercise 17.8a,
corrected: the factor `θ` is the Jacobian of `x = zθ`). -/
noncomputable def shocksCondDens (ψ g : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  g θ * θ * ψ (z * θ) / shocksPi ψ g z

/-- The conditional law `G(·|z)` of `θ` given `z = x/θ`: density `g(θ|z)` for `z ∈ int Z`, and the
endpoint convention `G(·|z̲) = δ_{θ̄}`, `G(·|z̄) = δ_{θ̲}` (the weak limits, Exercise 17.8b). -/
noncomputable def shocksCondLaw (xlo xhi θlo θhi : ℝ) (ψ g : ℝ → ℝ) (z : ℝ) : Measure ℝ :=
  if xlo / θhi < z ∧ z < xhi / θlo then
    volume.withDensity fun θ => ENNReal.ofReal (shocksCondDens ψ g z θ)
  else if z ≤ xlo / θhi then Measure.dirac θhi else Measure.dirac θlo

variable {xlo xhi θlo θhi : ℝ} {ψ g : ℝ → ℝ}

/-- For `z > 0`: `θ ∈ Θ` and `zθ ∈ X` iff `θ ∈ [a(z), b(z)]`. -/
theorem mem_Icc_shocksA_shocksB_iff {z θ : ℝ} (hz : 0 < z) :
    (θ ∈ Icc θlo θhi ∧ z * θ ∈ Icc xlo xhi) ↔ θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z) := by
  simp only [shocksA, shocksB, mem_Icc, max_le_iff, le_min_iff, div_le_iff₀ hz,
    le_div_iff₀ hz]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, h1⟩, by linarith, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h2, h4⟩, by linarith, by linarith⟩

/-- A function continuous on `[a, b]` and zero off it is measurable. -/
theorem shocks_measurable_of_zero_off {a b : ℝ} {f : ℝ → ℝ} (hc : ContinuousOn f (Icc a b))
    (h0 : ∀ x ∉ Icc a b, f x = 0) : Measurable f := by
  classical
  have : f = (Icc a b).piecewise f (fun _ => 0) := by
    ext x
    by_cases hx : x ∈ Icc a b
    · simp [hx]
    · simp [hx, h0 x hx]
  rw [this]
  exact hc.measurable_piecewise continuousOn_const measurableSet_Icc

/-- A function continuous on `[a, b]` and zero off it is bounded. -/
theorem shocks_exists_bound_of_zero_off {a b : ℝ} {f : ℝ → ℝ} (hc : ContinuousOn f (Icc a b))
    (h0 : ∀ x ∉ Icc a b, f x = 0) : ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc a b
  · exact (Real.norm_eq_abs _ ▸ hC x hx).trans (le_max_left _ _)
  · rw [h0 x hx, abs_zero]; exact le_max_right _ _

/-- On `int Z`, `z > 0` and `a(z) < b(z)`. -/
theorem shocksA_lt_shocksB (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi)
    {z : ℝ} (hzZ : xlo / θhi < z ∧ z < xhi / θlo) :
    0 < z ∧ shocksA xlo θlo z < shocksB xhi θhi z := by
  have hz0 : 0 < z := (div_pos hx0 (hθ0.trans hθ)).trans hzZ.1
  refine ⟨hz0, ?_⟩
  simp only [shocksA, shocksB, max_lt_iff, lt_min_iff]
  refine ⟨⟨div_lt_div_of_pos_right hx hz0, ?_⟩, ?_, hθ⟩
  · rw [lt_div_iff₀ hz0]; rw [lt_div_iff₀ hθ0] at hzZ
    linarith [hzZ.2]
  · rw [div_lt_iff₀ hz0]; rw [div_lt_iff₀ (hθ0.trans hθ)] at hzZ
    linarith [hzZ.1]

namespace ShocksAssumption17_5

variable (hA : ShocksAssumption17_5 xlo xhi θlo θhi ψ g)
include hA

/-- `ψ` is measurable. -/
theorem ψ_meas : Measurable ψ := shocks_measurable_of_zero_off hA.ψ_cont hA.ψ_zero
/-- `g` is measurable. -/
theorem g_meas : Measurable g := shocks_measurable_of_zero_off hA.g_cont hA.g_zero

/-- If `θ ∈ Θ` and `zθ ∈ X` then `z ∈ Z = [x̲/θ̄, x̄/θ̲]`. -/
theorem mem_Z_of {θ z : ℝ} (hθ : θ ∈ Icc θlo θhi) (hx : z * θ ∈ Icc xlo xhi) :
    z ∈ Icc (xlo / θhi) (xhi / θlo) := by
  have hθ0 : 0 < θ := hA.θlo_pos.trans_le hθ.1
  have hz : z = z * θ / θ := by field_simp
  have hzθ : 0 < z * θ := hA.xlo_pos.trans_le hx.1
  rw [hz]
  exact ⟨div_le_div₀ hzθ.le hx.1 hθ0 hθ.2, div_le_div₀ (hA.xlo_pos.trans hA.xlo_lt).le hx.2
    hA.θlo_pos hθ.1⟩

/-- The joint density of `(θ, z)` is integrable when multiplied by a bounded measurable `h`. -/
theorem integrable_joint {h : ℝ × ℝ → ℝ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ p, |h p| ≤ C) :
    Integrable (fun p : ℝ × ℝ => h p * (g p.1 * p.1 * ψ (p.2 * p.1)))
      (volume.prod volume) := by
  obtain ⟨Cg, hCg0, hCg⟩ := shocks_exists_bound_of_zero_off hA.g_cont hA.g_zero
  obtain ⟨Cψ, hCψ0, hCψ⟩ := shocks_exists_bound_of_zero_off hA.ψ_cont hA.ψ_zero
  set S : Set (ℝ × ℝ) := Icc θlo θhi ×ˢ Icc (xlo / θhi) (xhi / θlo)
  have hS : volume.prod volume S < ⊤ := by
    rw [Measure.prod_prod]
    simp only [Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hmeas : Measurable (fun p : ℝ × ℝ => h p * (g p.1 * p.1 * ψ (p.2 * p.1))) :=
    hm.mul ((hA.g_meas.comp measurable_fst).mul measurable_fst |>.mul
      (hA.ψ_meas.comp (measurable_snd.mul measurable_fst)))
  refine (integrableOn_const (C := C * (Cg * θhi * Cψ)) hS.ne).integrable_indicator
    (measurableSet_Icc.prod measurableSet_Icc) |>.mono' hmeas.aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs]
  by_cases hp : p ∈ S
  · rw [indicator_of_mem hp]
    have hθ := hp.1
    have h1 : 0 ≤ p.1 := hA.θlo_pos.le.trans hθ.1
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h1]
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC p)
    exact mul_le_mul (hC p) (mul_le_mul (mul_le_mul (hCg _) hθ.2 h1 hCg0) (hCψ _)
      (abs_nonneg _) (mul_nonneg hCg0 (hA.θlo_pos.le.trans hA.θlo_lt.le)))
      (by positivity) hC0
  · rw [indicator_of_notMem hp]
    simp only [S, mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · simp [hA.g_zero _ hp]
    · by_cases hθ : p.1 ∈ Icc θlo θhi
      · have : p.2 * p.1 ∉ Icc xlo xhi := fun hx => hp (hA.mem_Z_of hθ hx)
        simp [hA.ψ_zero _ this]
      · simp [hA.g_zero _ hθ]

/-- Change of variables `x = zθ` for fixed `θ` (the Jacobian is `θ`). -/
theorem inner_change {h : ℝ × ℝ → ℝ} (θ : ℝ) :
    g θ * ∫ x, ψ x * h (θ, x / θ) = ∫ z, h (θ, z) * (g θ * θ * ψ (z * θ)) := by
  by_cases hθ : θ ∈ Icc θlo θhi
  · have hθ0 : 0 < θ := hA.θlo_pos.trans_le hθ.1
    have e : ∫ x, ψ x * h (θ, x / θ) = θ * ∫ z, ψ (z * θ) * h (θ, z) := by
      have := Measure.integral_comp_div (fun z => ψ (z * θ) * h (θ, z)) θ
      simp only [div_mul_cancel₀ _ hθ0.ne', abs_of_pos hθ0, smul_eq_mul] at this
      exact this
    rw [e, ← mul_assoc,
      ← integral_const_mul]
    congr 1
    ext z
    ring
  · simp [hA.g_zero θ hθ]

/-- **Exercise 17.8a, joint law.** -/
theorem joint {h : ℝ × ℝ → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ p, |h p| ≤ C) :
    ∫ θ, g θ * ∫ x, ψ x * h (θ, x / θ) = ∫ z, ∫ θ, h (θ, z) * (g θ * θ * ψ (z * θ)) := by
  simp_rw [hA.inner_change]
  exact integral_integral_swap (hA.integrable_joint hm hC)

/-- The joint density `g(θ) θ ψ(zθ)` is bounded by a constant times the indicator of `Θ`. -/
theorem exists_joint_bound : ∃ K, 0 ≤ K ∧ ∀ z θ,
    |g θ * θ * ψ (z * θ)| ≤ (Icc θlo θhi).indicator (fun _ => K) θ := by
  obtain ⟨Cg, hCg0, hCg⟩ := shocks_exists_bound_of_zero_off hA.g_cont hA.g_zero
  obtain ⟨Cψ, hCψ0, hCψ⟩ := shocks_exists_bound_of_zero_off hA.ψ_cont hA.ψ_zero
  refine ⟨Cg * θhi * Cψ, by positivity [(hA.θlo_pos.trans hA.θlo_lt).le], fun z θ => ?_⟩
  by_cases hθ : θ ∈ Icc θlo θhi
  · rw [indicator_of_mem hθ]
    have h1 : 0 ≤ θ := hA.θlo_pos.le.trans hθ.1
    rw [abs_mul, abs_mul, abs_of_nonneg h1]
    exact mul_le_mul (mul_le_mul (hCg _) hθ.2 h1 hCg0) (hCψ _) (abs_nonneg _)
      (mul_nonneg hCg0 (hA.θlo_pos.le.trans hA.θlo_lt.le))
  · rw [indicator_of_notMem hθ]
    simp [hA.g_zero _ hθ]

/-- The joint density is measurable in `θ`. -/
theorem measurable_joint (z : ℝ) : Measurable (fun θ => g θ * θ * ψ (z * θ)) :=
  (hA.g_meas.mul measurable_id).mul (hA.ψ_meas.comp (measurable_const.mul measurable_id))

/-- For fixed `z`, `θ ↦ k(θ) g(θ) θ ψ(zθ)` is integrable for bounded measurable `k`. -/
theorem integrable_slice {k : ℝ → ℝ} (hk : Measurable k) {C : ℝ} (hC : ∀ θ, |k θ| ≤ C)
    (z : ℝ) : Integrable (fun θ => k θ * (g θ * θ * ψ (z * θ))) := by
  obtain ⟨K, hK0, hK⟩ := hA.exists_joint_bound
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine (integrableOn_const (s := Icc θlo θhi) (C := C * K)
    (by simp)).integrable_indicator measurableSet_Icc |>.mono'
    (hk.mul (hA.measurable_joint z)).aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hθ : θ ∈ Icc θlo θhi
  · rw [indicator_of_mem hθ]
    have := hK z θ
    rw [indicator_of_mem hθ] at this
    exact mul_le_mul (hC θ) this (abs_nonneg _) hC0
  · rw [indicator_of_notMem hθ]
    simp [hA.g_zero _ hθ]

/-- The joint density is integrable in `θ`. -/
theorem integrable_joint_slice (z : ℝ) : Integrable (fun θ => g θ * θ * ψ (z * θ)) :=
  (hA.integrable_slice (k := fun _ => 1) measurable_const (C := 1) (fun _ => by simp) z).congr
    (ae_of_all _ fun θ => by simp)

/-- The joint density `g(θ) θ ψ(zθ)` is nonnegative. -/
theorem joint_nonneg (z θ : ℝ) : 0 ≤ g θ * θ * ψ (z * θ) := by
  by_cases hθ : θ ∈ Icc θlo θhi
  · exact mul_nonneg (mul_nonneg (hA.g_nonneg θ) (hA.θlo_pos.le.trans hθ.1)) (hA.ψ_nonneg _)
  · simp [hA.g_zero _ hθ]

/-- The joint density vanishes off `[a(z), b(z)]` (for `z > 0`). -/
theorem joint_eq_zero {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∉ Icc (shocksA xlo θlo z) (shocksB xhi θhi z)) : g θ * θ * ψ (z * θ) = 0 := by
  rw [← mem_Icc_shocksA_shocksB_iff hz, not_and_or] at hθ
  rcases hθ with h | h
  · simp [hA.g_zero _ h]
  · simp [hA.ψ_zero _ h]

/-- `π(z) ≥ 0`. -/
theorem pi_nonneg (z : ℝ) : 0 ≤ shocksPi ψ g z :=
  integral_nonneg fun θ => hA.joint_nonneg z θ

/-- **`π` is a probability density** (p. 534): `∫ π = 1`. -/
theorem integral_pi : ∫ z, shocksPi ψ g z = 1 := by
  have h := hA.joint (h := fun _ => 1) measurable_const (C := 1) (fun _ => by simp)
  simp only [one_mul, mul_one, hA.ψ_int, hA.g_int] at h
  exact h.symm

/-- `π(z) > 0` forces `z > 0`. -/
theorem pos_of_pi_pos {z : ℝ} (hz : 0 < shocksPi ψ g z) : 0 < z := by
  by_contra h
  push Not at h
  have : shocksPi ψ g z = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun θ => ?_)
    by_cases hθ : θ ∈ Icc θlo θhi
    · have : z * θ ∉ Icc xlo xhi := fun hx => by
        have := mul_nonpos_of_nonpos_of_nonneg h (hA.θlo_pos.le.trans hθ.1)
        linarith [hx.1, hA.xlo_pos]
      simp [hA.ψ_zero _ this]
    · simp [hA.g_zero _ hθ]
  linarith

/-- The conditional density is measurable in `θ`. -/
theorem measurable_condDens (z : ℝ) : Measurable (shocksCondDens ψ g z) :=
  ((hA.g_meas.mul measurable_id).mul (hA.ψ_meas.comp (measurable_const.mul
    measurable_id))).div_const _

/-- **Exercise 17.8a** (p. 534), corrected. Where `π(z) > 0`, `G(·|z)` has the density
`g(θ|z) = g(θ) θ ψ(zθ)/π(z)`: it is nonnegative, integrates to `1`, vanishes off
`[a(z), b(z)]` and is continuous on `[a(z), b(z)]`. (It is the conditional density by
`ex_17_8a_disintegration`.) -/
theorem ex_17_8a {z : ℝ} (hz : 0 < shocksPi ψ g z) :
    (∀ θ, 0 ≤ shocksCondDens ψ g z θ) ∧ ∫ θ, shocksCondDens ψ g z θ = 1 ∧
      (∀ θ ∉ Icc (shocksA xlo θlo z) (shocksB xhi θhi z), shocksCondDens ψ g z θ = 0) ∧
      ContinuousOn (shocksCondDens ψ g z) (Icc (shocksA xlo θlo z) (shocksB xhi θhi z)) := by
  have hz0 := hA.pos_of_pi_pos hz
  refine ⟨fun θ => div_nonneg (hA.joint_nonneg z θ) hz.le, ?_, fun θ hθ => ?_, ?_⟩
  · simp only [shocksCondDens]
    rw [integral_div]
    exact div_self hz.ne'
  · simp [shocksCondDens, hA.joint_eq_zero hz0 hθ]
  · have hsub : ∀ θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z),
        θ ∈ Icc θlo θhi ∧ z * θ ∈ Icc xlo xhi := fun θ hθ =>
      (mem_Icc_shocksA_shocksB_iff hz0).2 hθ
    refine ContinuousOn.div_const (((hA.g_cont.mono fun θ hθ => (hsub θ hθ).1).mul
      continuousOn_id).mul (hA.ψ_cont.comp (continuousOn_const.mul continuousOn_id)
        fun θ hθ => (hsub θ hθ).2)) _

/-- **Exercise 17.8a, disintegration.** `E[h(θ, z)] = ∫ π(z) ∫ h(θ, z) g(θ|z) dθ dz` for bounded
measurable `h`: `g(·|z)` is the conditional density of `θ` given `z`. -/
theorem ex_17_8a_disintegration {h : ℝ × ℝ → ℝ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ p, |h p| ≤ C) :
    ∫ θ, g θ * ∫ x, ψ x * h (θ, x / θ) =
      ∫ z, shocksPi ψ g z * ∫ θ, h (θ, z) * shocksCondDens ψ g z θ := by
  rw [hA.joint hm hC]
  congr 1
  ext z
  have hint : Integrable (fun θ => h (θ, z) * (g θ * θ * ψ (z * θ))) :=
    hA.integrable_slice (hm.comp (measurable_id.prodMk measurable_const)) (fun θ => hC _) z
  by_cases hz : shocksPi ψ g z = 0
  · rw [hz, zero_mul]
    have h0 : (fun θ => g θ * θ * ψ (z * θ)) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun θ => hA.joint_nonneg z θ)
        (hA.integrable_joint_slice z)).1 hz
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h0] with θ hθ
    simp only [Pi.zero_apply] at hθ ⊢
    rw [hθ, mul_zero]
  · simp only [shocksCondDens, mul_div_assoc']
    rw [integral_div, mul_div_cancel₀ _ hz]

/-- On `int Z` with `π(z) > 0`, `G(·|z)` is a probability measure. -/
theorem isProbabilityMeasure_condLaw {z : ℝ} (hzZ : xlo / θhi < z ∧ z < xhi / θlo)
    (hz : 0 < shocksPi ψ g z) :
    IsProbabilityMeasure (shocksCondLaw xlo xhi θlo θhi ψ g z) := by
  obtain ⟨hnn, h1, -, -⟩ := hA.ex_17_8a hz
  constructor
  simp only [shocksCondLaw, hzZ, and_self, ↓reduceIte]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ hnn), h1, ENNReal.ofReal_one]
  exact (hA.integrable_joint_slice z).div_const (shocksPi ψ g z)

/-- On `int Z`, integrals against `G(·|z)` are integrals against `g(·|z)`. -/
theorem integral_condLaw {z : ℝ} (hzZ : xlo / θhi < z ∧ z < xhi / θlo)
    (hz : 0 < shocksPi ψ g z) (k : ℝ → ℝ) :
    ∫ θ, k θ ∂shocksCondLaw xlo xhi θlo θhi ψ g z = ∫ θ, k θ * shocksCondDens ψ g z θ := by
  obtain ⟨hnn, -, -, -⟩ := hA.ex_17_8a hz
  simp only [shocksCondLaw, hzZ, and_self, ↓reduceIte]
  rw [integral_withDensity_eq_integral_toReal_smul (hA.measurable_condDens z).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  ext θ
  rw [ENNReal.toReal_ofReal (hnn θ), smul_eq_mul, mul_comm]

/-- With `ψ > 0` on `X` and `g > 0` on `Θ`, `π(z) > 0` on `int Z` (the hypothesis missing from
Exercise 17.8a). -/
theorem pi_pos (hψ : ∀ x ∈ Icc xlo xhi, 0 < ψ x) (hg : ∀ θ ∈ Icc θlo θhi, 0 < g θ) {z : ℝ}
    (hzZ : xlo / θhi < z ∧ z < xhi / θlo) : 0 < shocksPi ψ g z := by
  obtain ⟨hz0, hab⟩ := shocksA_lt_shocksB hA.xlo_pos hA.xlo_lt hA.θlo_pos hA.θlo_lt hzZ
  refine (integral_pos_iff_support_of_nonneg (fun θ => hA.joint_nonneg z θ)
    (hA.integrable_joint_slice z)).2 ?_
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (shocksA xlo θlo z) (shocksB xhi θhi z))
    fun θ hθ => ?_)
  · simp [hab]
  · have h := (mem_Icc_shocksA_shocksB_iff hz0).2 (Ioo_subset_Icc_self hθ)
    exact (mul_pos (mul_pos (hg θ h.1) (hA.θlo_pos.trans_le h.1.1)) (hψ _ h.2)).ne'

/-- `ψ` is continuous at every point other than `x̲`, `x̄`. -/
theorem ψ_continuousAt {y : ℝ} (h1 : y ≠ xlo) (h2 : y ≠ xhi) : ContinuousAt ψ y := by
  by_cases hy : y ∈ Icc xlo xhi
  · exact hA.ψ_cont.continuousAt (Icc_mem_nhds (lt_of_le_of_ne hy.1 (Ne.symm h1))
      (lt_of_le_of_ne hy.2 h2))
  · have : ψ =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hy] with x hx
      exact hA.ψ_zero x hx
    exact continuousAt_const.congr this.symm

/-- `z ↦ ∫ k(θ) g(θ) θ ψ(zθ) dθ` is continuous at `z₀ > 0` (dominated convergence; the
integrand is continuous in `z` except at the two values `θ = x̲/z₀, x̄/z₀`). -/
theorem continuousAt_slice {k : ℝ → ℝ} (hk : Measurable k) {C : ℝ} (hC : ∀ θ, |k θ| ≤ C)
    {z₀ : ℝ} (hz₀ : 0 < z₀) :
    ContinuousAt (fun z => ∫ θ, k θ * (g θ * θ * ψ (z * θ))) z₀ := by
  obtain ⟨K, hK0, hK⟩ := hA.exists_joint_bound
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine continuousAt_of_dominated
    (bound := (Icc θlo θhi).indicator (fun _ => C * K))
    (Eventually.of_forall fun z => (hk.mul (hA.measurable_joint z)).aestronglyMeasurable)
    (Eventually.of_forall fun z => ae_of_all _ fun θ => ?_)
    ((integrableOn_const (s := Icc θlo θhi) (C := C * K) (by simp)).integrable_indicator
      measurableSet_Icc) ?_
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hθ : θ ∈ Icc θlo θhi
    · rw [indicator_of_mem hθ]
      have := hK z θ
      rw [indicator_of_mem hθ] at this
      exact mul_le_mul (hC θ) this (abs_nonneg _) hC0
    · rw [indicator_of_notMem hθ]
      simp [hA.g_zero _ hθ]
  · have hfin : volume ({xlo / z₀, xhi / z₀} : Set ℝ) = 0 :=
      (Set.toFinite _).measure_zero volume
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hfin] with θ hθ
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hθ
    have h1 : z₀ * θ ≠ xlo := fun h => hθ.1 (by rw [← h]; field_simp)
    have h2 : z₀ * θ ≠ xhi := fun h => hθ.2 (by rw [← h]; field_simp)
    exact continuousAt_const.mul (continuousAt_const.mul
      (ContinuousAt.comp (g := ψ) (f := fun x => x * θ) (hA.ψ_continuousAt h1 h2)
        (continuousAt_id.mul continuousAt_const)))

/-- If `h` is within `ε` of `h(θ₀)` on `[a(z), b(z)]`, then `∫ h g(·|z)` is within `ε` of
`h(θ₀)`. -/
theorem abs_integral_condDens_sub_le {z : ℝ} (hz : 0 < shocksPi ψ g z) (h : ℝ →ᵇ ℝ)
    (θ₀ : ℝ) {ε : ℝ}
    (hh : ∀ θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z), |h θ - h θ₀| ≤ ε) :
    |(∫ θ, h θ * shocksCondDens ψ g z θ) - h θ₀| ≤ ε := by
  obtain ⟨hnn, h1, h0, -⟩ := hA.ex_17_8a hz
  have hcd : Integrable (shocksCondDens ψ g z) := (hA.integrable_joint_slice z).div_const _
  have hint : Integrable (fun θ => h θ * shocksCondDens ψ g z θ) :=
    hcd.bdd_mul (c := ‖h‖) h.continuous.aestronglyMeasurable
      (ae_of_all _ fun θ => h.norm_coe_le_norm θ)
  have e : (∫ θ, h θ * shocksCondDens ψ g z θ) - h θ₀ =
      ∫ θ, (h θ - h θ₀) * shocksCondDens ψ g z θ := by
    simp_rw [sub_mul]
    rw [integral_sub hint (hcd.const_mul _), integral_const_mul, h1, mul_one]
  rw [e, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hcd.const_mul ε) (ae_of_all _ fun θ => ?_)).trans
    (by rw [integral_const_mul, h1, mul_one])
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn θ)]
  by_cases hθ : θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z)
  · exact mul_le_mul_of_nonneg_right (hh θ hθ) (hnn θ)
  · rw [h0 θ hθ]; simp

/-- **Exercise 17.8b** (p. 534), with the hypothesis `π > 0` on `int Z` (see `pi_pos`) and the
endpoint convention of `shocksCondLaw`: if `z_n → z` in `Z` then `G(·|z_n) → G(·|z)` weakly,
i.e. `z ↦ ∫ h dG(·|z)` is continuous on `Z` for every bounded continuous `h`. At interior points
this is dominated convergence; at `z̲` (resp. `z̄`) the support `[a(z), b(z)]` of `G(·|z)` lies in
`[x̲/z, θ̄]` (resp. `[θ̲, x̄/z]`), which shrinks to `{θ̄}` (resp. `{θ̲}`). -/
theorem ex_17_8b (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z)
    (h : ℝ →ᵇ ℝ) :
    ContinuousOn (fun z => ∫ θ, h θ ∂shocksCondLaw xlo xhi θlo θhi ψ g z)
      (Icc (xlo / θhi) (xhi / θlo)) := by
  set zlo := xlo / θhi
  set zhi := xhi / θlo
  have hθhi : 0 < θhi := hA.θlo_pos.trans hA.θlo_lt
  have hzlo : 0 < zlo := div_pos hA.xlo_pos hθhi
  have hZ : zlo < zhi := div_lt_div₀ hA.xlo_lt hA.θlo_lt.le (hA.xlo_pos.trans hA.xlo_lt).le
    hA.θlo_pos
  -- the value of the integral on the interior
  have hint : ∀ z, zlo < z ∧ z < zhi → ∫ θ, h θ ∂shocksCondLaw xlo xhi θlo θhi ψ g z =
      (∫ θ, h θ * (g θ * θ * ψ (z * θ))) / shocksPi ψ g z := fun z hz => by
    rw [hA.integral_condLaw hz (hπ z hz)]
    simp only [shocksCondDens, mul_div_assoc']
    exact integral_div _ _
  have hlo : ∫ θ, h θ ∂shocksCondLaw xlo xhi θlo θhi ψ g zlo = h θhi := by
    have h1 : ¬ (xlo / θhi < zlo ∧ zlo < xhi / θlo) := fun h => lt_irrefl _ h.1
    simp only [shocksCondLaw, h1, ↓reduceIte, le_refl, integral_dirac, zlo]
  have hhi : ∫ θ, h θ ∂shocksCondLaw xlo xhi θlo θhi ψ g zhi = h θlo := by
    have h1 : ¬ (xlo / θhi < zhi ∧ zhi < xhi / θlo) := fun h => lt_irrefl _ h.2
    have h2 : ¬ zhi ≤ xlo / θhi := not_le.mpr hZ
    simp only [shocksCondLaw, h1, h2, ↓reduceIte, integral_dirac]
  intro z₀ hz₀
  rcases eq_or_lt_of_le hz₀.1 with h1 | h1
  · -- the lower endpoint
    rw [← h1]
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hh⟩ := Metric.continuousAt_iff.1 (h.continuous.continuousAt (x := θhi))
      (ε / 2) (half_pos hε)
    have hc : ContinuousAt (fun z => xlo / z) zlo := continuousAt_const.div continuousAt_id
      hzlo.ne'
    obtain ⟨δ₂, hδ₂, hd⟩ := Metric.continuousAt_iff.1 hc δ₁ hδ₁
    refine ⟨min δ₂ (zhi - zlo), lt_min hδ₂ (sub_pos.2 hZ), fun z hz hdist => ?_⟩
    rw [hlo]
    rcases eq_or_lt_of_le hz.1 with h2 | h2
    · rw [← h2, hlo, dist_self]; exact hε
    have hzhi : z < zhi := by
      have := (abs_lt.1 (Real.dist_eq _ _ ▸ hdist)).2
      linarith [min_le_right δ₂ (zhi - zlo)]
    have hzz : zlo < z ∧ z < zhi := ⟨h2, hzhi⟩
    rw [Real.dist_eq, hA.integral_condLaw hzz (hπ z hzz)]
    have hxz : dist (xlo / z) (xlo / zlo) < δ₁ := hd (hdist.trans_le (min_le_left _ _))
    have hθ' : xlo / zlo = θhi := by simp only [zlo]; field_simp [hA.xlo_pos.ne']
    rw [hθ'] at hxz
    refine (hA.abs_integral_condDens_sub_le (hπ z hzz) h θhi
      fun θ hθ => ?_).trans_lt (half_lt_self hε)
    refine (le_of_lt (Real.dist_eq _ _ ▸ hh ?_))
    rw [Real.dist_eq, abs_lt]
    have ha : xlo / z ≤ θ := (le_max_left _ _).trans hθ.1
    have hb : θ ≤ θhi := hθ.2.trans (min_le_right _ _)
    rw [Real.dist_eq, abs_lt] at hxz
    constructor <;> linarith
  rcases eq_or_lt_of_le hz₀.2 with h3 | h3
  · -- the upper endpoint
    rw [h3]
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hh⟩ := Metric.continuousAt_iff.1 (h.continuous.continuousAt (x := θlo))
      (ε / 2) (half_pos hε)
    have hc : ContinuousAt (fun z => xhi / z) zhi := continuousAt_const.div continuousAt_id
      (hzlo.trans hZ).ne'
    obtain ⟨δ₂, hδ₂, hd⟩ := Metric.continuousAt_iff.1 hc δ₁ hδ₁
    refine ⟨min δ₂ (zhi - zlo), lt_min hδ₂ (sub_pos.2 hZ), fun z hz hdist => ?_⟩
    rw [hhi]
    rcases eq_or_lt_of_le hz.2 with h2 | h2
    · rw [h2, hhi, dist_self]; exact hε
    have hzlo' : zlo < z := by
      have := (abs_lt.1 (Real.dist_eq _ _ ▸ hdist)).1
      linarith [min_le_right δ₂ (zhi - zlo)]
    have hzz : zlo < z ∧ z < zhi := ⟨hzlo', h2⟩
    rw [Real.dist_eq, hA.integral_condLaw hzz (hπ z hzz)]
    have hxz : dist (xhi / z) (xhi / zhi) < δ₁ := hd (hdist.trans_le (min_le_left _ _))
    have hθ' : xhi / zhi = θlo := by
      simp only [zhi]; field_simp [(hA.xlo_pos.trans hA.xlo_lt).ne']
    rw [hθ'] at hxz
    refine (hA.abs_integral_condDens_sub_le (hπ z hzz) h θlo
      fun θ hθ => ?_).trans_lt (half_lt_self hε)
    refine (le_of_lt (Real.dist_eq _ _ ▸ hh ?_))
    rw [Real.dist_eq, abs_lt]
    have ha : θlo ≤ θ := (le_max_right _ _).trans hθ.1
    have hb : θ ≤ xhi / z := hθ.2.trans (min_le_left _ _)
    rw [Real.dist_eq, abs_lt] at hxz
    constructor <;> linarith
  · -- interior points
    have hzz : zlo < z₀ ∧ z₀ < zhi := ⟨h1, h3⟩
    have hk1 : ContinuousAt (fun z => ∫ θ, h θ * (g θ * θ * ψ (z * θ))) z₀ :=
      hA.continuousAt_slice h.continuous.measurable (C := ‖h‖) (fun θ => by
        rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm θ) (hzlo.trans h1)
    have hk2 : ContinuousAt (shocksPi ψ g) z₀ := by
      have := hA.continuousAt_slice (k := fun _ => 1) measurable_const (C := 1)
        (fun _ => by simp) (hzlo.trans h1)
      simp only [one_mul] at this
      exact this
    refine ((hk1.div hk2 (hπ z₀ hzz).ne').congr ?_).continuousWithinAt
    filter_upwards [Ioo_mem_nhds h1 h3] with z hz
    exact (hint z hz).symm

/-- Every `G(·|z)` is a probability measure (given `π > 0` on `int Z`). -/
theorem isProbabilityMeasure_condLaw' (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo →
    0 < shocksPi ψ g z) (z : ℝ) :
    IsProbabilityMeasure (shocksCondLaw xlo xhi θlo θhi ψ g z) := by
  by_cases h : xlo / θhi < z ∧ z < xhi / θlo
  · exact hA.isProbabilityMeasure_condLaw h (hπ z h)
  · simp only [shocksCondLaw, h, ↓reduceIte]
    split_ifs <;> exact Measure.dirac.isProbabilityMeasure

end ShocksAssumption17_5

/-! ### Assumption 17.6: uniform shocks -/

/-- The uniform density on `[a, b]`. -/
noncomputable def shocksUnif (a b : ℝ) : ℝ → ℝ := (Icc a b).indicator fun _ => (b - a)⁻¹

/-- `∫_{[a, b]} θ dθ = (b² − a²)/2`. -/
theorem shocks_setIntegral_Icc_id {a b : ℝ} (hab : a ≤ b) :
    ∫ θ in Icc a b, θ = (b ^ 2 - a ^ 2) / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_id]

/-- **Assumption 17.6** (p. 536) is compatible with Assumption 17.5: uniform `Ψ` and `G`
satisfy Assumption 17.5. -/
theorem shocksUnif_assumption17_5 {xlo xhi θlo θhi : ℝ} (hx0 : 0 < xlo) (hx : xlo < xhi)
    (hθ0 : 0 < θlo) (hθ : θlo < θhi) (hθ2 : θhi < 2) :
    ShocksAssumption17_5 xlo xhi θlo θhi (shocksUnif xlo xhi) (shocksUnif θlo θhi) := by
  have key : ∀ a b : ℝ, a < b → (∀ x, 0 ≤ shocksUnif a b x) ∧
      (∀ x ∉ Icc a b, shocksUnif a b x = 0) ∧ ContinuousOn (shocksUnif a b) (Icc a b) ∧
      ∫ x, shocksUnif a b x = 1 := fun a b hab => by
    refine ⟨fun x => indicator_nonneg (fun _ _ => (inv_pos.2 (sub_pos.2 hab)).le) x,
      fun x hx => indicator_of_notMem hx _,
      continuousOn_const.congr fun x hx => indicator_of_mem hx _, ?_⟩
    rw [shocksUnif, integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
      Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_pos.2 hab).le,
      mul_inv_cancel₀ (sub_pos.2 hab).ne']
  obtain ⟨a1, a2, a3, a4⟩ := key xlo xhi hx
  obtain ⟨b1, b2, b3, b4⟩ := key θlo θhi hθ
  exact ⟨hx0, hx, hθ0, hθ, hθ2, a1, b1, a2, b2, a3, b3, a4, b4⟩

/-- Under Assumption 17.6 the joint density of `(θ, z)` is `θ/((θ̄ − θ̲)(x̄ − x̲))` on
`[a(z), b(z)]` (`z > 0`). -/
theorem shocksUnif_joint {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    shocksUnif θlo θhi θ * θ * shocksUnif xlo xhi (z * θ) =
      (Icc (shocksA xlo θlo z) (shocksB xhi θhi z)).indicator
        (fun θ => (θhi - θlo)⁻¹ * (xhi - xlo)⁻¹ * θ) θ := by
  by_cases h : θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z)
  · obtain ⟨h1, h2⟩ := (mem_Icc_shocksA_shocksB_iff hz).2 h
    rw [indicator_of_mem h, shocksUnif, shocksUnif, indicator_of_mem h1, indicator_of_mem h2]
    ring
  · rw [indicator_of_notMem h]
    rw [← mem_Icc_shocksA_shocksB_iff hz, not_and_or] at h
    rcases h with h | h
    · simp [shocksUnif, indicator_of_notMem h]
    · simp [shocksUnif, indicator_of_notMem h]

/-- Under Assumption 17.6, `π(z) = (b² − a²)/(2(θ̄ − θ̲)(x̄ − x̲))` where `a(z) ≤ b(z)`. -/
theorem shocksUnif_pi {z : ℝ} (hz : 0 < z) (hab : shocksA xlo θlo z ≤ shocksB xhi θhi z) :
    shocksPi (shocksUnif xlo xhi) (shocksUnif θlo θhi) z =
      (θhi - θlo)⁻¹ * (xhi - xlo)⁻¹ *
        ((shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2) / 2) := by
  simp only [shocksPi]
  simp_rw [shocksUnif_joint hz]
  rw [integral_indicator measurableSet_Icc, integral_const_mul, shocks_setIntegral_Icc_id hab]

/-- **Exercise 17.12, corrected** (p. 536). Under Assumptions 17.5 and 17.6, for `z ∈ int Z`
the conditional density of `θ` given `z` is `2θ/(b(z)² − a(z)²)` on `[a(z), b(z)]` (and `0`
elsewhere): **not** uniform. -/
theorem ex_17_12 (hx0 : 0 < xlo) (hx : xlo < xhi) (hθ0 : 0 < θlo) (hθ : θlo < θhi) {z : ℝ}
    (hzZ : xlo / θhi < z ∧ z < xhi / θlo) (θ : ℝ) :
    shocksCondDens (shocksUnif xlo xhi) (shocksUnif θlo θhi) z θ =
      (Icc (shocksA xlo θlo z) (shocksB xhi θhi z)).indicator
        (fun θ => 2 * θ / (shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2)) θ := by
  obtain ⟨hz0, hab⟩ := shocksA_lt_shocksB hx0 hx hθ0 hθ hzZ
  have ha0 : 0 < shocksA xlo θlo z := hθ0.trans_le (le_max_right _ _)
  have hd : 0 < shocksB xhi θhi z ^ 2 - shocksA xlo θlo z ^ 2 := by nlinarith
  rw [shocksCondDens, shocksUnif_joint hz0, shocksUnif_pi hz0 hab.le]
  by_cases h : θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z)
  · rw [indicator_of_mem h, indicator_of_mem h]
    have h1 : 0 < θhi - θlo := sub_pos.2 hθ
    have h2 : 0 < xhi - xlo := sub_pos.2 hx
    field_simp
  · rw [indicator_of_notMem h, indicator_of_notMem h, zero_div]

/-! ### The example economy `x ~ U[1, 2]`, `θ ~ U[1, 3/2]` -/

/-- The example economy satisfies Assumptions 17.5 and 17.6. -/
theorem shocksEx_assumption :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) :=
  shocksUnif_assumption17_5 one_pos one_lt_two one_pos (by norm_num) (by norm_num)

/-- In the example, `a(z) = 1` and `b(z) = 3/2` for `z ∈ [1, 4/3]`. -/
theorem shocksEx_ab {z : ℝ} (hz : z ∈ Icc (1 : ℝ) (4 / 3)) :
    shocksA 1 1 z = 1 ∧ shocksB 2 (3 / 2) z = 3 / 2 := by
  have hz0 : 0 < z := one_pos.trans_le hz.1
  refine ⟨max_eq_right ?_, min_eq_right ?_⟩
  · rw [div_le_one hz0]; exact hz.1
  · rw [le_div_iff₀ hz0]; linarith [hz.2]

/-- In the example, `π(z) = 5/4` for `z ∈ [1, 4/3]`. -/
theorem shocksEx_pi {z : ℝ} (hz : z ∈ Icc (1 : ℝ) (4 / 3)) :
    shocksPi (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) z = 5 / 4 := by
  have hz0 : 0 < z := one_pos.trans_le hz.1
  obtain ⟨ha, hb⟩ := shocksEx_ab hz
  rw [shocksUnif_pi hz0 (by rw [ha, hb]; norm_num), ha, hb]
  norm_num

/-- **Correction (manual, Exercise 17.8a).** The manual's density `g(θ)ψ(θz)/π(z)` omits the
Jacobian factor `θ` and does not integrate to `1`: in the example at `z = 1` it integrates to
`4/5`. -/
theorem ex_17_8a_manual_counterexample :
    ∫ θ, shocksUnif 1 (3 / 2) θ * shocksUnif 1 2 (θ * 1) /
      shocksPi (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) 1 = 4 / 5 := by
  rw [shocksEx_pi ⟨le_rfl, by norm_num⟩, integral_div]
  have e : (fun θ : ℝ => shocksUnif 1 (3 / 2) θ * shocksUnif 1 2 (θ * 1)) =
      (Icc (1 : ℝ) (3 / 2)).indicator fun _ => 2 := by
    ext θ
    by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
    · have h' : θ * 1 ∈ Icc (1 : ℝ) 2 := by rw [mul_one]; exact ⟨h.1, by linarith [h.2]⟩
      simp only [shocksUnif, indicator_of_mem h, indicator_of_mem h']
      norm_num
    · simp [shocksUnif, indicator_of_notMem h]
  rw [e, integral_indicator measurableSet_Icc, setIntegral_const, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

/-- **Correction (Exercise 17.12 is false).** The book's claim, that `G(·|z)` is the uniform
distribution on `[a(z), b(z)]`, fails in the example: the uniform family does not disintegrate
the joint law of `(θ, z)`. With `h(θ, z) = θ·1{z ∈ [1, 4/3]}` (on `θ ∈ [1, 3/2]`) the true
expectation is `19/36` while the uniform family gives `25/48`. -/
theorem ex_17_12_counterexample : ¬ ∀ h : ℝ × ℝ → ℝ, Measurable h → (∃ C, ∀ p, |h p| ≤ C) →
    ∫ θ, shocksUnif 1 (3 / 2) θ * ∫ x, shocksUnif 1 2 x * h (θ, x / θ) =
      ∫ z, shocksPi (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) z *
        ((shocksB 2 (3 / 2) z - shocksA 1 1 z)⁻¹ *
          ∫ θ in Icc (shocksA 1 1 z) (shocksB 2 (3 / 2) z), h (θ, z)) := by
  intro H
  set h₀ : ℝ × ℝ → ℝ := fun p =>
    (Icc (1 : ℝ) (4 / 3)).indicator (fun _ => 1) p.2 * (Icc (1 : ℝ) (3 / 2)).indicator id p.1
  have hm : Measurable h₀ :=
    ((measurable_const.indicator measurableSet_Icc).comp measurable_snd).mul
      ((measurable_id.indicator measurableSet_Icc).comp measurable_fst)
  have hb : ∀ p, |h₀ p| ≤ 3 / 2 := fun p => by
    simp only [h₀]
    by_cases h1 : p.2 ∈ Icc (1 : ℝ) (4 / 3)
    · by_cases h2 : p.1 ∈ Icc (1 : ℝ) (3 / 2)
      · rw [indicator_of_mem h1, indicator_of_mem h2, one_mul, id, abs_of_pos
          (one_pos.trans_le h2.1)]
        exact h2.2
      · rw [indicator_of_notMem h2]; norm_num
    · rw [indicator_of_notMem h1]; norm_num
  have key := H h₀ hm ⟨3 / 2, hb⟩
  rw [shocksEx_assumption.joint hm hb] at key
  have L : ∀ z, ∫ θ, h₀ (θ, z) * (shocksUnif 1 (3 / 2) θ * θ * shocksUnif 1 2 (z * θ)) =
      (Icc (1 : ℝ) (4 / 3)).indicator (fun _ => 19 / 12) z := fun z => by
    by_cases hz : z ∈ Icc (1 : ℝ) (4 / 3)
    · have hz0 : 0 < z := one_pos.trans_le hz.1
      obtain ⟨ha, hb'⟩ := shocksEx_ab hz
      have e : (fun θ => h₀ (θ, z) * (shocksUnif 1 (3 / 2) θ * θ * shocksUnif 1 2 (z * θ))) =
          (Icc (1 : ℝ) (3 / 2)).indicator fun θ => 2 * θ ^ 2 := by
        ext θ
        rw [shocksUnif_joint hz0, ha, hb']
        by_cases h : θ ∈ Icc (1 : ℝ) (3 / 2)
        · simp only [h₀, indicator_of_mem hz, indicator_of_mem h, id]
          norm_num
          ring
        · simp [h₀, indicator_of_notMem h]
      rw [e, indicator_of_mem hz, integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
        intervalIntegral.integral_const_mul, integral_pow]
      norm_num
    · simp [h₀, indicator_of_notMem hz]
  have R : ∀ z, shocksPi (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) z *
      ((shocksB 2 (3 / 2) z - shocksA 1 1 z)⁻¹ *
        ∫ θ in Icc (shocksA 1 1 z) (shocksB 2 (3 / 2) z), h₀ (θ, z)) =
      (Icc (1 : ℝ) (4 / 3)).indicator (fun _ => 25 / 16) z := fun z => by
    by_cases hz : z ∈ Icc (1 : ℝ) (4 / 3)
    · obtain ⟨ha, hb'⟩ := shocksEx_ab hz
      rw [shocksEx_pi hz, ha, hb', indicator_of_mem hz,
        setIntegral_congr_fun measurableSet_Icc (g := id) fun θ hθ => by
          simp [h₀, indicator_of_mem hz, indicator_of_mem hθ]]
      rw [show (fun x : ℝ => id x) = fun x => x from rfl, shocks_setIntegral_Icc_id (by norm_num)]
      norm_num
    · simp [h₀, indicator_of_notMem hz]
  simp_rw [L, R] at key
  rw [integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc,
    setIntegral_const, setIntegral_const, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by norm_num)] at key
  norm_num at key

/-- A property holding a.e. on `[p, q]` holds at some point of every measurable `S ⊆ [p, q]` of
positive measure. -/
theorem shocks_exists_mem_of_ae_restrict_Icc {p q : ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ x ∂volume.restrict (Icc p q), P x) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Icc p q) (hpos : volume S ≠ 0) : ∃ x ∈ S, P x := by
  have h' : ∀ᵐ x ∂volume.restrict S, P x := ae_restrict_of_ae_restrict_of_subset hS h
  have hmem : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hSm
  have : (ae (volume.restrict S)).NeBot := ae_neBot.2 (by rwa [Ne, Measure.restrict_eq_zero])
  obtain ⟨x, hx1, hx2⟩ := (h'.and hmem).exists
  exact ⟨x, hx2, hx1⟩

/-- In the example, at `z = 4/5` the conditional density is `(32/11) θ` on `[5/4, 3/2]`. -/
theorem shocksEx_condDens_four_fifths (θ : ℝ) :
    shocksCondDens (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) (4 / 5) θ =
      (Icc (5 / 4 : ℝ) (3 / 2)).indicator (fun θ => 32 / 11 * θ) θ := by
  rw [ex_17_12 one_pos one_lt_two one_pos (by norm_num) (by norm_num) θ]
  have ha : shocksA 1 1 (4 / 5) = 5 / 4 := by norm_num [shocksA]
  have hb : shocksB 2 (3 / 2) (4 / 5) = 3 / 2 := by norm_num [shocksB]
  rw [ha, hb]
  congr 1
  ext θ
  ring

/-- **Correction (Exercise 17.8a, "continuous density").** Under Assumption 17.5 the densities are
continuous on `X` and `Θ` only (Assumption 17.6, uniform densities, is the book's own example),
and then `G(·|z)` need **not** have a density continuous on `Θ`: in the example, at
`z = 4/5 ∈ int Z`, `g(·|z)` jumps from `0` to `40/11` at `θ = a(z) = 5/4 ∈ int Θ`, and no
function continuous on `Θ` agrees with it a.e. (The density is continuous on `[a(z), b(z)]`,
`ex_17_8a`.) -/
theorem ex_17_8a_continuity_counterexample : ¬ ∃ c : ℝ → ℝ, ContinuousOn c (Icc 1 (3 / 2)) ∧
    ∀ᵐ θ ∂volume.restrict (Icc 1 (3 / 2)),
      c θ = shocksCondDens (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) (4 / 5) θ := by
  rintro ⟨c, hc, hae⟩
  have hcont : ContinuousAt c (5 / 4) :=
    hc.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨δ, hδ, hcδ⟩ := Metric.continuousAt_iff.1 hcont (20 / 11) (by norm_num)
  set δ' := min δ (1 / 4)
  have hδ' : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'1 : δ' ≤ 1 / 4 := min_le_right _ _
  obtain ⟨θ₁, hθ₁, e₁⟩ := shocks_exists_mem_of_ae_restrict_Icc hae (S := Ioo (5 / 4 - δ') (5 / 4))
    measurableSet_Ioo (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
    (by simp [hδ'])
  obtain ⟨θ₂, hθ₂, e₂⟩ := shocks_exists_mem_of_ae_restrict_Icc hae (S := Ioo (5 / 4) (5 / 4 + δ'))
    measurableSet_Ioo (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
    (by simp [hδ'])
  rw [shocksEx_condDens_four_fifths, indicator_of_notMem (fun h => by linarith [h.1, hθ₁.2])]
    at e₁
  rw [shocksEx_condDens_four_fifths, indicator_of_mem
    (show θ₂ ∈ Icc (5 / 4 : ℝ) (3 / 2) from ⟨hθ₂.1.le, by linarith [hθ₂.2]⟩)] at e₂
  have d₁ := hcδ (x := θ₁) (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hθ₁.1, hθ₁.2, min_le_left δ (1 / 4)])
  have d₂ := hcδ (x := θ₂) (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hθ₂.1, hθ₂.2, min_le_left δ (1 / 4)])
  rw [Real.dist_eq, e₁, abs_lt] at d₁
  rw [Real.dist_eq, e₂, abs_lt] at d₂
  linarith [hθ₂.1]

/-- The unnormalised density of the example with `π = 0` on part of `int Z`. -/
noncomputable def shocksExG0 (θ : ℝ) : ℝ :=
  (Icc (1 : ℝ) (3 / 2)).indicator (fun θ => max 0 ((θ - 1) * (5 / 4 - θ))) θ

/-- A continuous density on `Θ = [1, 3/2]` vanishing on `[5/4, 3/2]`. -/
noncomputable def shocksExG (θ : ℝ) : ℝ := shocksExG0 θ / ∫ t, shocksExG0 t

/-- The normalising constant of `shocksExG` is positive. -/
theorem shocksExG0_integral_pos : 0 < ∫ t, shocksExG0 t := by
  have hc : ContinuousOn (fun θ : ℝ => max 0 ((θ - 1) * (5 / 4 - θ))) (Icc 1 (3 / 2)) :=
    Continuous.continuousOn (by fun_prop)
  have hint : Integrable shocksExG0 :=
    (hc.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  refine (integral_pos_iff_support_of_nonneg (fun θ => indicator_nonneg
    (fun _ _ => le_max_left _ _) θ) hint).2 ?_
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo 1 (5 / 4)) fun θ hθ => ?_)
  · simp only [Real.volume_Ioo]
    norm_num
  · rw [Function.mem_support]
    change (Icc (1 : ℝ) (3 / 2)).indicator _ θ ≠ 0
    rw [indicator_of_mem
      (show θ ∈ Icc (1 : ℝ) (3 / 2) from ⟨hθ.1.le, by linarith [hθ.2]⟩)]
    exact (lt_max_of_lt_right (mul_pos (by linarith [hθ.1]) (by linarith [hθ.2]))).ne'

/-- **Correction (Exercise 17.8a, missing hypothesis `π(z) > 0`).** Assumption 17.5 allows `π`
to vanish at interior points of `Z`, where the formula for `g(·|z)` is `0/0` and `G(·|z)` is not
determined by the joint law: with `x ~ U[1, 2]` and `g ∝ max{0, (θ − 1)(5/4 − θ)}` on
`Θ = [1, 3/2]`, the joint density `g(θ) θ ψ(zθ)` vanishes identically at `z = 3/4 ∈ int Z`. -/
theorem ex_17_8a_pi_zero_counterexample :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExG ∧
      (1 / (3 / 2) : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 2 / 1 ∧
      (∀ θ, shocksExG θ * θ * shocksUnif 1 2 (3 / 4 * θ) = 0) ∧
      shocksPi (shocksUnif 1 2) shocksExG (3 / 4) = 0 := by
  have hpos := shocksExG0_integral_pos
  have hU := shocksUnif_assumption17_5 (xlo := 1) (xhi := 2) (θlo := 1) (θhi := 3 / 2) one_pos
    one_lt_two one_pos (by norm_num) (by norm_num)
  have hzero : ∀ θ, shocksExG θ * θ * shocksUnif 1 2 (3 / 4 * θ) = 0 := fun θ => by
    by_cases h : θ ∈ Ioo (1 : ℝ) (5 / 4)
    · have : 3 / 4 * θ ∉ Icc (1 : ℝ) 2 := fun h' => by linarith [h'.1, h.2]
      simp [shocksUnif, indicator_of_notMem this]
    · have : shocksExG0 θ = 0 := by
        by_cases h' : θ ∈ Icc (1 : ℝ) (3 / 2)
        · simp only [shocksExG0, indicator_of_mem h']
          refine max_eq_left ?_
          simp only [mem_Ioo, not_and_or, not_lt] at h
          rcases h with h | h
          · nlinarith [h'.1]
          · nlinarith [h'.2]
        · simp [shocksExG0, indicator_of_notMem h']
      simp [shocksExG, this]
  refine ⟨⟨one_pos, one_lt_two, one_pos, by norm_num, by norm_num, hU.ψ_nonneg,
    fun θ => div_nonneg (indicator_nonneg (fun _ _ => le_max_left _ _) θ) hpos.le,
    hU.ψ_zero, fun θ hθ => by simp [shocksExG, shocksExG0, indicator_of_notMem hθ],
    hU.ψ_cont, ?_, hU.ψ_int, ?_⟩, by norm_num, by norm_num, hzero, ?_⟩
  · refine ContinuousOn.div_const ?_ _
    refine (Continuous.continuousOn (f := fun θ : ℝ => max 0 ((θ - 1) * (5 / 4 - θ)))
      (by fun_prop)).congr fun θ hθ => ?_
    simp [shocksExG0, indicator_of_mem hθ]
  · simp only [shocksExG]
    rw [integral_div, div_self hpos.ne']
  · simp only [shocksPi, hzero, integral_zero]

/-! ### Exercise 17.10 -/

/-- In the example, `π > 0` on `int Z`. -/
theorem shocksEx_pi_pos (z : ℝ) (hz : 1 / (3 / 2) < z ∧ z < 2 / 1) :
    0 < shocksPi (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) z :=
  shocksEx_assumption.pi_pos (fun x hx => by rw [shocksUnif, indicator_of_mem hx]; norm_num)
    (fun θ hθ => by rw [shocksUnif, indicator_of_mem hθ]; norm_num) hz

/-- The sequence `z_n = 2/3 + 1/(3(n + 1)) ↓ z̲ = 2/3` of Exercise 17.10. -/
noncomputable def shocksExSeq (n : ℕ) : ℝ := 2 / 3 + 1 / ((n : ℝ) + 1) / 3

/-- `z_n ∈ int Z = (2/3, 2)`. -/
theorem shocksExSeq_mem (n : ℕ) : 1 / (3 / 2) < shocksExSeq n ∧ shocksExSeq n < 2 / 1 := by
  have h1 : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  have h2 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(n.cast_nonneg :
    (0 : ℝ) ≤ n)])
  simp only [shocksExSeq, one_div]
  constructor <;> norm_num <;> linarith

/-- `z_n → 2/3`. -/
theorem shocksExSeq_tendsto : Tendsto shocksExSeq atTop (𝓝 (2 / 3)) := by
  have := (tendsto_const_nhds (x := (2 / 3 : ℝ))).add
    (tendsto_one_div_add_atTop_nhds_zero_nat.div_const 3)
  change Tendsto (fun n : ℕ => 2 / 3 + 1 / ((n : ℝ) + 1) / 3) atTop (𝓝 (2 / 3))
  simpa using this

/-- In the example, `G(·|z_n)` gives mass `0` to every set on which its density vanishes. -/
theorem shocksEx_condLaw_seq_eq_zero (n : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    (h0 : ∀ θ ∈ s, θ ∉ Icc (shocksA 1 1 (shocksExSeq n)) (shocksB 2 (3 / 2) (shocksExSeq n))) :
    shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) (shocksExSeq n) s = 0 := by
  have hm := shocksExSeq_mem n
  obtain ⟨-, -, hz, -⟩ := shocksEx_assumption.ex_17_8a (shocksEx_pi_pos _ hm)
  simp only [shocksCondLaw, hm, and_self, ↓reduceIte]
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 0) fun θ hθ => by
    rw [hz θ (h0 θ hθ), ENNReal.ofReal_zero]]
  simp

/-- **Exercise 17.10** (p. 536; no answer in the manual). With `x ~ U[1, 2]`, `θ ~ U[1, 3/2]`
(so `Z = [2/3, 2]`) and `z_n ↓ z̲ = 2/3`: `G(·|z_n) → G(·|z̲) = δ_{3/2}` weakly
(Exercise 17.8b), but `‖G(·|z_n) − G(·|z̲)‖_TV ≥ 1` for all `n` (each `G(·|z_n)` has a density, so
gives `{3/2}` mass `0`); indeed `G(·|z_n)` has **no** limit in total variation. So the analogue of
Assumption 17.3 fails. -/
theorem ex_17_10 :
    (∀ n, shocksExSeq n ∈ Icc (1 / (3 / 2) : ℝ) (2 / 1)) ∧
      Tendsto shocksExSeq atTop (𝓝 (1 / (3 / 2))) ∧
      (∀ h : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ θ, h θ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2)
        (shocksUnif 1 (3 / 2)) (shocksExSeq n)) atTop
        (𝓝 (∫ θ, h θ ∂shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2))
          (1 / (3 / 2))))) ∧
      (∀ n, 1 ≤ fpTVNorm (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2))
        (shocksExSeq n)) (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2))
          (1 / (3 / 2)))) ∧
      ¬ ∃ ν₀ : Measure ℝ, IsFiniteMeasure ν₀ ∧ Tendsto (fun n => fpTVNorm (shocksCondLaw 1 2 1
        (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2)) (shocksExSeq n)) ν₀) atTop (𝓝 0) := by
  set ν := shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) (shocksUnif 1 (3 / 2))
  have hA := shocksEx_assumption
  have hprob : ∀ z, IsProbabilityMeasure (ν z) := hA.isProbabilityMeasure_condLaw' shocksEx_pi_pos
  have hmem : ∀ n, shocksExSeq n ∈ Icc (1 / (3 / 2) : ℝ) (2 / 1) := fun n =>
    ⟨(shocksExSeq_mem n).1.le, (shocksExSeq_mem n).2.le⟩
  have hlim : Tendsto shocksExSeq atTop (𝓝 (1 / (3 / 2))) := by
    convert shocksExSeq_tendsto using 2; norm_num
  have hνlo : ν (1 / (3 / 2)) = Measure.dirac (3 / 2) := by
    have h1 : ¬ ((1 : ℝ) / (3 / 2) < 1 / (3 / 2) ∧ (1 : ℝ) / (3 / 2) < 2 / 1) :=
      fun h => lt_irrefl _ h.1
    simp only [ν, shocksCondLaw, h1, ↓reduceIte, le_refl]
  have hsing : ∀ n, ν (shocksExSeq n) {3 / 2} = 0 := fun n => by
    simp only [ν, shocksCondLaw, shocksExSeq_mem n, and_self, ↓reduceIte]
    exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  refine ⟨hmem, hlim, fun h => ?_, fun n => ?_, ?_⟩
  · have hc := hA.ex_17_8b shocksEx_pi_pos h
    exact (hc _ ⟨le_rfl, by norm_num⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hmem⟩)
  · have := fp_le_tvNorm_pair (ν (shocksExSeq n)) (ν (1 / (3 / 2)))
      (measurableSet_singleton (3 / 2 : ℝ))
    rw [Measure.real, Measure.real, hsing n, hνlo,
      Measure.dirac_apply_of_mem (mem_singleton _)] at this
    simp only [ENNReal.toReal_zero, ENNReal.toReal_one, zero_sub, abs_neg, abs_one] at this
    rw [hνlo]
    linarith [abs_nonneg ((ν (shocksExSeq n)).real {3 / 2}ᶜ -
      (Measure.dirac (3 / 2 : ℝ)).real {3 / 2}ᶜ)]
  · rintro ⟨ν₀, hν₀, hTV⟩
    -- setwise convergence
    have hset : ∀ s, MeasurableSet s →
        Tendsto (fun n => (ν (shocksExSeq n)).real s) atTop (𝓝 (ν₀.real s)) := fun s hs => by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hTV
      rw [Real.norm_eq_abs]
      have := fp_le_tvNorm_pair (ν (shocksExSeq n)) ν₀ hs
      linarith [abs_nonneg ((ν (shocksExSeq n)).real sᶜ - ν₀.real sᶜ)]
    have hzero : ∀ s, MeasurableSet s → (∀ᶠ n in atTop, ν (shocksExSeq n) s = 0) →
        ν₀ s = 0 := fun s hs hev => by
      have h1 := hset s hs
      have h2 : Tendsto (fun n => (ν (shocksExSeq n)).real s) atTop (𝓝 0) :=
        tendsto_const_nhds.congr' (hev.mono fun n hn => by simp [measureReal_def, hn])
      have := tendsto_nhds_unique h1 h2
      rwa [measureReal_eq_zero_iff] at this
    have hone : ν₀.real univ = 1 := by
      have h1 := hset univ MeasurableSet.univ
      simp only [probReal_univ] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    have hS : ν₀ {3 / 2} = 0 := hzero _ (measurableSet_singleton _)
      (Eventually.of_forall hsing)
    have hI : ν₀ (Ioi (3 / 2)) = 0 := hzero _ measurableSet_Ioi (Eventually.of_forall fun n =>
      shocksEx_condLaw_seq_eq_zero n measurableSet_Ioi fun θ hθ h => by
        linarith [h.2.trans (min_le_right _ _), mem_Ioi.1 hθ])
    have hinv : Tendsto (fun n => 1 / shocksExSeq n) atTop (𝓝 (3 / 2)) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).div shocksExSeq_tendsto (by norm_num)
      convert this using 2; norm_num
    have hL : ∀ k : ℕ, ν₀ (Iio (3 / 2 - 1 / ((k : ℝ) + 1))) = 0 := fun k => by
      have hk : 3 / 2 - 1 / ((k : ℝ) + 1) < 3 / 2 := by
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      refine hzero _ measurableSet_Iio ?_
      filter_upwards [hinv.eventually (eventually_gt_nhds hk)] with n hn
      exact shocksEx_condLaw_seq_eq_zero n measurableSet_Iio fun θ hθ h => by
        linarith [(le_max_left _ _).trans h.1, mem_Iio.1 hθ]
    have hIio : ν₀ (Iio (3 / 2)) = 0 := by
      have : Iio (3 / 2 : ℝ) = ⋃ k : ℕ, Iio (3 / 2 - 1 / ((k : ℝ) + 1)) := by
        ext θ
        simp only [mem_Iio, mem_iUnion]
        constructor
        · intro hθ
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hθ)
          exact ⟨k, by linarith⟩
        · rintro ⟨k, hk⟩
          have : 0 < 1 / ((k : ℝ) + 1) := by positivity
          linarith
      rw [this]
      exact measure_iUnion_null hL
    have huniv : ν₀ univ = 0 := by
      have : (univ : Set ℝ) = Iio (3 / 2) ∪ {3 / 2} ∪ Ioi (3 / 2) := by
        ext θ
        simp only [mem_univ, mem_union, mem_Iio, mem_singleton_iff, mem_Ioi, true_iff]
        rcases lt_trichotomy θ (3 / 2) with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      rw [this]
      exact measure_union_null (measure_union_null hIio hS) hI
    rw [measureReal_def, huniv] at hone
    norm_num at hone

/-! ### The NOTE on p. 533 -/

/-- **What p. 533 proves.** If labour depends on the state only through the price
(`n = N ∘ p`, from (1)) and the market clears ((2): `n p = x/θ`), then equal prices imply equal
ratios: `z = x/θ` is a function of the price. -/
theorem p533_ratio_of_price {S : Type*} (p n z : S → ℝ) (N : ℝ → ℝ) (hn : ∀ s, n s = N (p s))
    (h2 : ∀ s, n s * p s = z s) {s s' : S} (hp : p s = p s') : z s = z s' := by
  rw [← h2, ← h2, hn, hn, hp]

/-- **Correction (p. 533).** The converse, "any equilibrium price is of the form `ρ(x/θ)`", does
not follow from those premises: on `X × Θ = [1, 2] × [1, 3/2]`,
`p(x, θ) = x/θ + 10·1{θ > 5/4}` and `n = (x/θ)/p` satisfy `n = N ∘ p` and (2), yet `p` is not a
function of `x/θ` (the price reveals more than `z`). (Whether such a `p` can also satisfy (1) is
not settled; the book's existence results are about equilibria of the form `ρ(x/θ)` only.) -/
theorem p533_counterexample : ∃ (p n : ℝ × ℝ → ℝ) (N : ℝ → ℝ),
    (∀ s ∈ Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) (3 / 2), 0 < p s ∧ 0 < n s ∧ n s = N (p s) ∧
      n s * p s = s.1 / s.2) ∧
    ¬ ∃ ρ : ℝ → ℝ, ∀ s ∈ Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) (3 / 2), p s = ρ (s.1 / s.2) := by
  classical
  set p : ℝ × ℝ → ℝ := fun s => s.1 / s.2 + if 5 / 4 < s.2 then 10 else 0
  set N : ℝ → ℝ := fun q => (q - if 5 < q then 10 else 0) / q
  refine ⟨p, fun s => N (p s), N, fun s hs => ?_, ?_⟩
  · have hx : 0 < s.1 := one_pos.trans_le hs.1.1
    have hθ : 0 < s.2 := one_pos.trans_le hs.2.1
    have hz : s.1 / s.2 ≤ 2 := by
      rw [div_le_iff₀ hθ]; nlinarith [hs.1.2, hs.2.1]
    have hz0 : 0 < s.1 / s.2 := div_pos hx hθ
    have hp0 : 0 < p s := by simp only [p]; split_ifs <;> linarith
    have hN : N (p s) = s.1 / s.2 / p s := by
      simp only [N, p]
      split_ifs with h1 h2 h2 <;> first | (exfalso; linarith) | ring
    refine ⟨hp0, show 0 < N (p s) by rw [hN]; positivity, rfl,
      show N (p s) * p s = _ by rw [hN, div_mul_cancel₀ _ hp0.ne']⟩
  · rintro ⟨ρ, hρ⟩
    have h1 := hρ (6 / 5, 6 / 5) ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
    have h2 := hρ (7 / 5, 7 / 5) ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
    simp only [p] at h1 h2
    norm_num at h1 h2
    rw [← h1] at h2
    norm_num at h2

end StokeyLucasPrescott.FixedPointArguments

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.VUniformErgodic
import VUniformErgodicity.ModelNonlinearModels

/-!
# The simple adaptive control model (MT §16.5.2, Proposition 16.5.2)

Meyn and Tweedie, §16.5.2, pp. 416–418. The closed loop SAC model (2.22)–(2.25) is
`sacKernel Γ α σ_z σ_w` on the state `(Σ, θ̃, Y)`, with disturbance `(Z, W) ∼ Γ = μ_Z ⊗ μ_W`:
`Y' = θ̃Y + W`, `θ̃' = αθ̃ − αΣY'Y/(ΣY² + σ_w²) + Z`, `Σ' = σ_z² + α²σ_w²Σ/(ΣY² + σ_w²)`.
`Σ` stays in `[σ_z², σ_z²/(1 − α²)]` (`sacStep_sigma_mem`), the set `sacSet α σ_z`.

* `sacV ε (Σ, θ̃, y) = θ̃⁴ + ε θ̃² y² + ε² y²`, the function (16.44).
* `sq_add_le_young`, `pow_four_add_le_young`: `(a + b)² ≤ (1 + δ)a² + (1 + δ⁻¹)b²` and
  `(a + b)⁴ ≤ (1 + δ)³a⁴ + (1 + δ⁻¹)³b⁴`.
* `sac_theta_eq`: `θ̃' = Z + u − vW` with `u = ασ_w²θ̃/D`, `v = αΣY/D`, `D = ΣY² + σ_w²`.
* (16.45), `P y² = θ̃²y² + σ_w²`, is used inside `sac_drift`; for the Gaussian chain it is
  `lintegral_sacGaussian_Ysq` in `AdaptiveControlKalman`.
* `sac_drift`: **the drift of Proposition 16.5.2**: (16.46)–(16.47) combined, for any
  `max(σ_z², α⁴) < ρ` there are `ε₀ > 0` and `R < ∞` with `PV ≤ ρV + R` on `sacSet`, for
  `V = sacV ε₀`. The book bounds `Pθ̃²y²` and `Pθ̃⁴` separately ((16.46), (16.47)); here
  `θ̃'²Y'²` and `θ̃'⁴` are bounded pointwise by Young's inequality before integrating, which gives
  the same leading coefficients `σ_z²` and `α⁴` up to the factor `1 + δ`.

* `measurableSet_sacSet`, `isAbsorbing_sacSet`, `isCompact_sacV_le`: `sacSet` is an absorbing set
  on which the sublevel sets of `V` are compact.
* **Proposition 16.5.2** (`proposition_16_5_2`, p. 417): the chain restricted to `sacSet` is
  `V`-uniformly ergodic for `V = sacV ε₀ + 1`, and `E_x[Y_k²] → ∫ y² dπ` geometrically (16.48).
* `eq_16_49`, `sac_performance_bounds` (p. 417): the formula (16.49) and the bounds on
  `E_π[Y₀²]`, from the two expectation identities obtained from (2.23)–(2.24).

**Hypotheses.** The disturbances are independent, centred, with `E[Z²] = σ_z²`, `E[W²] = σ_w²`
and finite fourth moments (the Gaussian case (SAC2) is an instance, `memLp_id_gaussianReal`);
`σ_z ≠ 0`, `σ_w ≠ 0`, `|α| < 1` and `σ_z² < 1` (the condition of Proposition 16.5.2). As for
the other models, `ψ`-irreducibility, aperiodicity and the petiteness of compact sets of the
restricted chain are hypotheses here: for Gaussian disturbances they are derived in
`AdaptiveControlKalman` (`proposition_16_5_2_gaussian`) from Proposition 7.4.3 and
Theorem 6.2.5 (ii).

**Elsewhere.** The two expectation identities behind (16.49) rest on the filtering
interpretation `θ̃ₖ = θₖ − E[θₖ | Y₀, …, Yₖ]`, `Σₖ = E[θ̃ₖ² | Y₀, …, Yₖ]`; `eq_16_49` derives
(16.49) from them. For Gaussian disturbances `AdaptiveControlKalman` proves that the steady state
is a Kalman law and derives the identities and (16.49) (`eq_16_49_gaussian`). Figure 16.1 is a
simulation.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

/-! ### The function (16.44) and elementary inequalities -/

/-- **The function (16.44)**: `V(Σ, θ̃, y) = θ̃⁴ + ε θ̃² y² + ε² y²`. -/
def sacV (ε : ℝ) (x : ℝ × ℝ × ℝ) : ℝ := x.2.1 ^ 4 + ε * x.2.1 ^ 2 * x.2.2 ^ 2 + ε ^ 2 * x.2.2 ^ 2

/-- The invariant set `[σ_z², σ_z²/(1 − α²)] × ℝ²` of the SAC model (MT p. 36). -/
def sacSet (α σz : ℝ) : Set (ℝ × ℝ × ℝ) := Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) ×ˢ univ

/-- `V ≥ 0` for `ε ≥ 0`. -/
theorem sacV_nonneg {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ × ℝ × ℝ) : 0 ≤ sacV ε x := by
  unfold sacV; positivity

/-- **Young's inequality**: `(a + b)² ≤ (1 + δ)a² + (1 + δ⁻¹)b²` for `δ > 0`. -/
theorem sq_add_le_young (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (a + b) ^ 2 ≤ (1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2 := by
  have h : 0 ≤ (δ * a - b) ^ 2 / δ := by positivity
  have e : (δ * a - b) ^ 2 / δ = δ * a ^ 2 - 2 * a * b + 1 / δ * b ^ 2 := by
    field_simp; ring
  nlinarith

/-- `(a + b)⁴ ≤ (1 + δ)³a⁴ + (1 + δ⁻¹)³b⁴` for `δ > 0`. -/
theorem pow_four_add_le_young (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (a + b) ^ 4 ≤ (1 + δ) ^ 3 * a ^ 4 + (1 + 1 / δ) ^ 3 * b ^ 4 := by
  have h1 := sq_add_le_young a b hδ
  have h2 := sq_add_le_young ((1 + δ) * a ^ 2) ((1 + 1 / δ) * b ^ 2) hδ
  have hsq : (a + b) ^ 4 = ((a + b) ^ 2) ^ 2 := by ring
  have h3 : ((a + b) ^ 2) ^ 2 ≤ ((1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  calc (a + b) ^ 4 ≤ ((1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2) ^ 2 := hsq ▸ h3
    _ ≤ (1 + δ) * ((1 + δ) * a ^ 2) ^ 2 + (1 + 1 / δ) * ((1 + 1 / δ) * b ^ 2) ^ 2 := h2
    _ = (1 + δ) ^ 3 * a ^ 4 + (1 + 1 / δ) ^ 3 * b ^ 4 := by ring

/-- **The estimation error update** (MT p. 416): `θ̃' = Z + u − vW` with `u = ασ_w²θ̃/D`,
`v = αΣY/D`, `D = ΣY² + σ_w² ≠ 0`. -/
theorem sac_theta_eq {α σz σw S t y z w : ℝ} (hD : S * y ^ 2 + σw ^ 2 ≠ 0) :
    (sacStep α σz σw ((S, t, y), (z, w))).2.1 =
      z + (α * σw ^ 2 * t / (S * y ^ 2 + σw ^ 2) - α * S * y / (S * y ^ 2 + σw ^ 2) * w) := by
  simp only [sacStep]
  field_simp
  ring

/-! ### The drift -/

/-- **The bounds on `u` and `v`** (MT p. 416): for `Σ ∈ [σ_z², Σ_max]`, `D = ΣY² + σ_w²`,
`u = ασ_w²θ̃/D` and `v = αΣY/D`: `u² ≤ α²θ̃²`, `u⁴ ≤ α⁴θ̃⁴`, `u²y²σ_z² ≤ α²σ_w²θ̃²`,
`v² ≤ α²Σ_max/(4σ_w²)` and `v²y² ≤ α²`. -/
theorem sac_uv_bounds {α σz σw S Smax t y : ℝ} (hσz : σz ≠ 0) (hσw : σw ≠ 0)
    (hS1 : σz ^ 2 ≤ S) (hS2 : S ≤ Smax) :
    (α * σw ^ 2 * t / (S * y ^ 2 + σw ^ 2)) ^ 2 ≤ α ^ 2 * t ^ 2 ∧
    (α * σw ^ 2 * t / (S * y ^ 2 + σw ^ 2)) ^ 4 ≤ α ^ 4 * t ^ 4 ∧
    (α * σw ^ 2 * t / (S * y ^ 2 + σw ^ 2)) ^ 2 * y ^ 2 * σz ^ 2 ≤ α ^ 2 * σw ^ 2 * t ^ 2 ∧
    (α * S * y / (S * y ^ 2 + σw ^ 2)) ^ 2 ≤ α ^ 2 * Smax / (4 * σw ^ 2) ∧
    (α * S * y / (S * y ^ 2 + σw ^ 2)) ^ 2 * y ^ 2 ≤ α ^ 2 := by
  have hσz2 : 0 < σz ^ 2 := by positivity
  have hσw2 : 0 < σw ^ 2 := by positivity
  have hS0 : 0 < S := lt_of_lt_of_le hσz2 hS1
  obtain ⟨D, hD⟩ : ∃ D, D = S * y ^ 2 + σw ^ 2 := ⟨_, rfl⟩
  rw [← hD]
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hSy : 0 ≤ S * y ^ 2 := mul_nonneg hS0.le hy2
  have hD0 : 0 < D := by rw [hD]; linarith
  have hDσ : σw ^ 2 ≤ D := by rw [hD]; linarith
  have hDS : S * y ^ 2 ≤ D := by rw [hD]; linarith
  have hD2 : 4 * (S * y ^ 2) * σw ^ 2 ≤ D ^ 2 := by
    rw [hD, show (S * y ^ 2 + σw ^ 2) ^ 2 = (S * y ^ 2 - σw ^ 2) ^ 2 + 4 * (S * y ^ 2) * σw ^ 2
      by ring]
    linarith [sq_nonneg (S * y ^ 2 - σw ^ 2)]
  have hD20 : 0 < D ^ 2 := by positivity
  have hU1 : (α * σw ^ 2 * t / D) ^ 2 ≤ α ^ 2 * t ^ 2 := by
    rw [div_pow, div_le_iff₀ hD20]
    have h1 : (σw ^ 2) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hσw2.le hDσ 2
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (α * t))
    calc (α * σw ^ 2 * t) ^ 2 = (α * t) ^ 2 * (σw ^ 2) ^ 2 := by ring
      _ ≤ (α * t) ^ 2 * D ^ 2 := h2
      _ = α ^ 2 * t ^ 2 * D ^ 2 := by ring
  refine ⟨hU1, ?_, ?_, ?_, ?_⟩
  · have h := pow_le_pow_left₀ (sq_nonneg _) hU1 2
    calc (α * σw ^ 2 * t / D) ^ 4 = ((α * σw ^ 2 * t / D) ^ 2) ^ 2 := by ring
      _ ≤ (α ^ 2 * t ^ 2) ^ 2 := h
      _ = α ^ 4 * t ^ 4 := by ring
  · rw [div_pow, show (α * σw ^ 2 * t) ^ 2 / D ^ 2 * y ^ 2 * σz ^ 2 =
      (α * t) ^ 2 * ((σw ^ 2) ^ 2 * (y ^ 2 * σz ^ 2)) / D ^ 2 by ring, div_le_iff₀ hD20]
    have h3 : y ^ 2 * σz ^ 2 ≤ S * y ^ 2 := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right hS1 hy2
    have h4 : S * y ^ 2 * σw ^ 2 ≤ D ^ 2 := by
      have := mul_le_mul hDS hDσ hσw2.le hD0.le
      nlinarith
    have h1 : (σw ^ 2) ^ 2 * (y ^ 2 * σz ^ 2) ≤ σw ^ 2 * D ^ 2 := by
      have h5 := mul_le_mul_of_nonneg_left h3 (mul_nonneg hσw2.le hσw2.le)
      have h6 := mul_le_mul_of_nonneg_left h4 hσw2.le
      calc (σw ^ 2) ^ 2 * (y ^ 2 * σz ^ 2) = σw ^ 2 * σw ^ 2 * (y ^ 2 * σz ^ 2) := by ring
        _ ≤ σw ^ 2 * σw ^ 2 * (S * y ^ 2) := h5
        _ = σw ^ 2 * (S * y ^ 2 * σw ^ 2) := by ring
        _ ≤ σw ^ 2 * D ^ 2 := h6
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (α * t))
    calc (α * t) ^ 2 * ((σw ^ 2) ^ 2 * (y ^ 2 * σz ^ 2)) ≤ (α * t) ^ 2 * (σw ^ 2 * D ^ 2) := h2
      _ = α ^ 2 * σw ^ 2 * t ^ 2 * D ^ 2 := by ring
  · rw [div_pow, div_le_div_iff₀ hD20 (by positivity)]
    have h1 : S * (4 * (S * y ^ 2) * σw ^ 2) ≤ S * D ^ 2 := mul_le_mul_of_nonneg_left hD2 hS0.le
    have h2 : S * D ^ 2 ≤ Smax * D ^ 2 := mul_le_mul_of_nonneg_right hS2 hD20.le
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (sq_nonneg α)
    calc (α * S * y) ^ 2 * (4 * σw ^ 2) = α ^ 2 * (S * (4 * (S * y ^ 2) * σw ^ 2)) := by ring
      _ ≤ α ^ 2 * (Smax * D ^ 2) := h3
      _ = α ^ 2 * Smax * D ^ 2 := by ring
  · rw [div_pow, show (α * S * y) ^ 2 / D ^ 2 * y ^ 2 = α ^ 2 * (S * y ^ 2) ^ 2 / D ^ 2 by ring,
      div_le_iff₀ hD20]
    have h1 : (S * y ^ 2) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hSy hDS 2
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg α)


/-- **The choice of constants** in Proposition 16.5.2: with `g = ρ − max(σ_z², α⁴)`,
`δ ≤ min(1, g/28)`, `ε ≤ g/2` and `εK₃ ≤ g/2`, the leading coefficients are below `ρ`. -/
theorem sac_coeffs {α σz ρ g δ ε K3 : ℝ} (hσzρ : σz ^ 2 ≤ ρ - g) (hαρ : α ^ 4 ≤ ρ - g)
    (hα4 : α ^ 4 ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδg : δ ≤ g / 28) (hε0 : 0 < ε)
    (hεg : ε ≤ g / 2) (hεK : ε * K3 ≤ g / 2) (hρ1 : ρ < 1) :
    (1 + δ) ^ 3 * α ^ 4 + ε * K3 ≤ ρ ∧ ε * (1 + δ) * σz ^ 2 + ε ^ 2 ≤ ρ * ε := by
  have hα40 : 0 ≤ α ^ 4 := by positivity
  have hg : 0 ≤ g := by linarith
  constructor
  · have h1 : (1 + δ) ^ 3 ≤ 1 + 7 * δ := by nlinarith [mul_pos hδ0 hδ0]
    have h2 := mul_le_mul_of_nonneg_right h1 hα40
    have h3 : 7 * δ * α ^ 4 ≤ 7 * δ := by nlinarith
    nlinarith
  · have hσz1 : σz ^ 2 ≤ 1 := by linarith
    have h1 : δ * σz ^ 2 ≤ δ := by nlinarith [sq_nonneg σz]
    have h2 : (1 + δ) * σz ^ 2 + ε ≤ ρ := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hε0.le
    nlinarith

/-- **The drift of Proposition 16.5.2** (MT pp. 416–417, (16.45)–(16.47)): for independent
centred disturbances with `E[Z²] = σ_z²`, `E[W²] = σ_w²` and finite fourth moments, `|α| < 1`,
`σ_z, σ_w ≠ 0`, and any `ρ > max(σ_z², α⁴)`, there are `ε₀ > 0` and `R < ∞` with
`E[V(Φ₁) | Φ₀ = x] ≤ ρ V(x) + R` for every `x ∈ [σ_z², σ_z²/(1 − α²)] × ℝ²`,
`V = sacV ε₀` (in the form `PV ≤ ρV + R` with `V + 1`). -/
theorem sac_drift {α σz σw : ℝ} (hα : |α| < 1) (hσz : σz ≠ 0) (hσw : σw ≠ 0)
    (μZ μW : Measure ℝ) [IsProbabilityMeasure μZ] [IsProbabilityMeasure μW]
    (hZ2 : Integrable (fun z => z ^ 2) μZ) (hZ2' : ∫ z, z ^ 2 ∂μZ = σz ^ 2)
    (hZ4 : Integrable (fun z => z ^ 4) μZ)
    (hW1 : Integrable (fun w => w) μW) (hW1' : ∫ w, w ∂μW = 0)
    (hW2 : Integrable (fun w => w ^ 2) μW) (hW2' : ∫ w, w ^ 2 ∂μW = σw ^ 2)
    (hW4 : Integrable (fun w => w ^ 4) μW) {ρ : ℝ} (hρ : max (σz ^ 2) (α ^ 4) < ρ)
    (hρ1 : ρ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ sacSet α σz,
      ∫⁻ y, ENNReal.ofReal (sacV ε y + 1) ∂sacKernel (μZ.prod μW) α σz σw x ≤
        ENNReal.ofReal (ρ * sacV ε x + R + 1) := by
  have hα2 : α ^ 2 < 1 := by
    have h1 : α ^ 2 = |α| ^ 2 := (sq_abs α).symm
    rw [h1]; nlinarith [abs_nonneg α]
  have hσz2 : 0 < σz ^ 2 := by positivity
  have hσw2 : 0 < σw ^ 2 := by positivity
  set Smax := σz ^ 2 / (1 - α ^ 2) with hSmax
  have hSmax0 : 0 ≤ Smax := div_nonneg hσz2.le (by linarith)
  set M4Z := ∫ z, z ^ 4 ∂μZ with hM4Z
  set M4W := ∫ w, w ^ 4 ∂μW with hM4W
  have hM4Z0 : 0 ≤ M4Z := integral_nonneg fun z => by positivity
  have hM4W0 : 0 ≤ M4W := integral_nonneg fun w => by positivity
  set Kv := α ^ 2 * Smax / (4 * σw ^ 2) with hKv
  have hKv0 : 0 ≤ Kv := by positivity
  set g := ρ - max (σz ^ 2) (α ^ 4) with hg
  have hg0 : 0 < g := by linarith
  have hσzρ : σz ^ 2 ≤ ρ - g := by rw [hg]; linarith [le_max_left (σz ^ 2) (α ^ 4)]
  have hαρ : α ^ 4 ≤ ρ - g := by rw [hg]; linarith [le_max_right (σz ^ 2) (α ^ 4)]
  have hα4 : α ^ 4 ≤ 1 := by nlinarith
  set δ := min 1 (g / 28) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδg : δ ≤ g / 28 := min_le_right _ _
  set c := 1 + 1 / δ with hc
  have hc1 : 1 ≤ c := by rw [hc]; have : 0 < 1 / δ := by positivity
                         linarith
  set K3 := 4 * c * α ^ 2 * σw ^ 2 * (1 / σz ^ 2 + 2) with hK3
  have hK30 : 0 ≤ K3 := by positivity
  set ε := min (g / 2) (g / (2 * (K3 + 1))) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
  have hεg : ε ≤ g / 2 := min_le_left _ _
  have hεK : ε * K3 ≤ g / 2 := by
    have h1 : ε ≤ g / (2 * (K3 + 1)) := min_le_right _ _
    have h2 : ε * K3 ≤ g / (2 * (K3 + 1)) * K3 := mul_le_mul_of_nonneg_right h1 hK30
    have h3 : g / (2 * (K3 + 1)) * K3 ≤ g / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    linarith
  set R := 8 * c ^ 3 * (M4Z + Kv ^ 2 * M4W) + ε * (1 + δ) * σz ^ 2 * σw ^ 2 +
    4 * ε * c * Kv * M4W + ε ^ 2 * σw ^ 2 + 8 * ε * c * α ^ 2 * σw ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨ε, hε0, R, hR0, fun x hx => ?_⟩
  obtain ⟨S, t, y⟩ := x
  simp only [sacSet, mem_prod, mem_Icc, mem_univ, and_true] at hx
  obtain ⟨hS1, hS2⟩ := hx
  obtain ⟨hU1, hU2, hU3, hV1, hV2⟩ := sac_uv_bounds (α := α) (t := t) hσz hσw hS1 hS2
  have hS0 : 0 < S := lt_of_lt_of_le hσz2 hS1
  have hD0 : 0 < S * y ^ 2 + σw ^ 2 := by positivity
  obtain ⟨u, hu⟩ : ∃ u, u = α * σw ^ 2 * t / (S * y ^ 2 + σw ^ 2) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = α * S * y / (S * y ^ 2 + σw ^ 2) := ⟨_, rfl⟩
  rw [← hu] at hU1 hU2 hU3
  rw [← hv] at hV1 hV2
  rw [← hKv] at hV1
  have hc0 : 0 ≤ c := by linarith
  have hε0' : 0 ≤ ε := hε0.le
  -- the pointwise bound
  set Bf : ℝ × ℝ → ℝ := fun p => (1 + δ) ^ 3 * u ^ 4 + 8 * c ^ 3 * (p.1 ^ 4 * 1) +
    8 * c ^ 3 * v ^ 4 * (1 * p.2 ^ 4) + ε * (1 + δ) * (p.1 ^ 2 * (t * y + p.2) ^ 2) +
    4 * ε * c * (1 * ((u ^ 2 + v ^ 2 * p.2 ^ 2) * (t ^ 2 * y ^ 2 + p.2 ^ 2))) +
    ε ^ 2 * (1 * (t * y + p.2) ^ 2) with hBf
  have hpt : ∀ p : ℝ × ℝ, sacV ε (sacStep α σz σw ((S, t, y), p)) ≤ Bf p := fun p => by
    obtain ⟨z, w⟩ := p
    have hθ := sac_theta_eq (α := α) (σz := σz) (t := t) (z := z) (w := w) hD0.ne'
    rw [← hu, ← hv] at hθ
    have hY : (sacStep α σz σw ((S, t, y), (z, w))).2.2 = t * y + w := rfl
    unfold sacV
    rw [hθ, hY]
    simp only [hBf, mul_one, one_mul]
    -- the fourth power
    have h4 : (z + (u - v * w)) ^ 4 ≤
        (1 + δ) ^ 3 * u ^ 4 + 8 * c ^ 3 * z ^ 4 + 8 * c ^ 3 * v ^ 4 * w ^ 4 := by
      have e : z + (u - v * w) = u + (z + -(v * w)) := by ring
      rw [e]
      have h1 := pow_four_add_le_young u (z + -(v * w)) hδ0
      have h2 := pow_four_add_le_young z (-(v * w)) one_pos
      have h2' : (z + -(v * w)) ^ 4 ≤ 8 * z ^ 4 + 8 * (v ^ 4 * w ^ 4) := by
        have e2 : (-(v * w)) ^ 4 = v ^ 4 * w ^ 4 := by ring
        rw [e2] at h2; norm_num at h2; linarith
      have hc3 : 0 ≤ c ^ 3 := by positivity
      have h3 := mul_le_mul_of_nonneg_left h2' hc3
      rw [← hc] at h1
      linarith
    -- the square
    have h2 : (z + (u - v * w)) ^ 2 ≤ (1 + δ) * z ^ 2 + c * (2 * u ^ 2 + 2 * (v ^ 2 * w ^ 2)) := by
      have h1 := sq_add_le_young z (u - v * w) hδ0
      have h3 := sq_add_le_young u (-(v * w)) one_pos
      have e2 : (-(v * w)) ^ 2 = v ^ 2 * w ^ 2 := by ring
      rw [e2, ← sub_eq_add_neg] at h3
      norm_num at h3
      rw [← hc] at h1
      have h4 := mul_le_mul_of_nonneg_left h3 hc0
      linarith
    have hY2 : (t * y + w) ^ 2 ≤ 2 * (t ^ 2 * y ^ 2) + 2 * w ^ 2 := by
      have := sq_add_le_young (t * y) w one_pos
      norm_num at this
      linarith
    have hprod : (z + (u - v * w)) ^ 2 * (t * y + w) ^ 2 ≤
        (1 + δ) * (z ^ 2 * (t * y + w) ^ 2) +
          4 * c * ((u ^ 2 + v ^ 2 * w ^ 2) * (t ^ 2 * y ^ 2 + w ^ 2)) := by
      have hQ := mul_le_mul_of_nonneg_right h2 (sq_nonneg (t * y + w))
      have hR' : c * (2 * u ^ 2 + 2 * (v ^ 2 * w ^ 2)) * (t * y + w) ^ 2 ≤
          c * (2 * u ^ 2 + 2 * (v ^ 2 * w ^ 2)) * (2 * (t ^ 2 * y ^ 2) + 2 * w ^ 2) :=
        mul_le_mul_of_nonneg_left hY2 (by positivity)
      linarith
    have hfin := mul_le_mul_of_nonneg_left hprod hε0'
    linarith
  -- the one-dimensional integrals
  have hW0 : Integrable (fun _ : ℝ => (1 : ℝ)) μW := integrable_const 1
  have hZ0 : Integrable (fun _ : ℝ => (1 : ℝ)) μZ := integrable_const 1
  have e5 : (fun w : ℝ => (t * y + w) ^ 2) = fun w => ((t * y) ^ 2 + 2 * (t * y) * w) + w ^ 2 := by
    funext w; ring
  have i5a : Integrable (fun w : ℝ => (t * y) ^ 2 + 2 * (t * y) * w) μW :=
    (integrable_const _).add (hW1.const_mul _)
  have hK5int : Integrable (fun w => (t * y + w) ^ 2) μW := by rw [e5]; exact i5a.add hW2
  have hK5 : ∫ w, (t * y + w) ^ 2 ∂μW = t ^ 2 * y ^ 2 + σw ^ 2 := by
    rw [e5, integral_add (f := fun w => (t * y) ^ 2 + 2 * (t * y) * w) (g := fun w => w ^ 2)
      i5a hW2, integral_add (f := fun _ => (t * y) ^ 2) (g := fun w => 2 * (t * y) * w)
      (integrable_const _) (hW1.const_mul _), integral_const, integral_const_mul, hW1', hW2',
      probReal_univ, one_smul]
    ring
  have e4 : (fun w : ℝ => (u ^ 2 + v ^ 2 * w ^ 2) * (t ^ 2 * y ^ 2 + w ^ 2)) = fun w =>
      ((u ^ 2 * (t ^ 2 * y ^ 2) + u ^ 2 * w ^ 2) + v ^ 2 * (t ^ 2 * y ^ 2) * w ^ 2) +
        v ^ 2 * w ^ 4 := by
    funext w; ring
  have i4a : Integrable (fun w : ℝ => u ^ 2 * (t ^ 2 * y ^ 2) + u ^ 2 * w ^ 2) μW :=
    (integrable_const _).add (hW2.const_mul _)
  have i4b : Integrable (fun w : ℝ => (u ^ 2 * (t ^ 2 * y ^ 2) + u ^ 2 * w ^ 2) +
      v ^ 2 * (t ^ 2 * y ^ 2) * w ^ 2) μW := i4a.add (hW2.const_mul _)
  have hK4int : Integrable (fun w => (u ^ 2 + v ^ 2 * w ^ 2) * (t ^ 2 * y ^ 2 + w ^ 2)) μW := by
    rw [e4]; exact i4b.add (hW4.const_mul _)
  have hK4 : ∫ w, (u ^ 2 + v ^ 2 * w ^ 2) * (t ^ 2 * y ^ 2 + w ^ 2) ∂μW =
      u ^ 2 * (t ^ 2 * y ^ 2) + u ^ 2 * σw ^ 2 + v ^ 2 * (t ^ 2 * y ^ 2) * σw ^ 2 +
        v ^ 2 * M4W := by
    rw [e4, integral_add (f := fun w => (u ^ 2 * (t ^ 2 * y ^ 2) + u ^ 2 * w ^ 2) +
      v ^ 2 * (t ^ 2 * y ^ 2) * w ^ 2) (g := fun w => v ^ 2 * w ^ 4) i4b (hW4.const_mul _),
      integral_add (f := fun w => u ^ 2 * (t ^ 2 * y ^ 2) + u ^ 2 * w ^ 2)
        (g := fun w => v ^ 2 * (t ^ 2 * y ^ 2) * w ^ 2) i4a (hW2.const_mul _),
      integral_add (f := fun _ => u ^ 2 * (t ^ 2 * y ^ 2)) (g := fun w => u ^ 2 * w ^ 2)
        (integrable_const _) (hW2.const_mul _), integral_const, integral_const_mul,
      integral_const_mul, integral_const_mul, hW2', probReal_univ, one_smul]
  -- the integrals on the product
  set Γ := μZ.prod μW with hΓ
  have i1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 4 * 1) Γ := hZ4.mul_prod hW0
  have i2 : Integrable (fun p : ℝ × ℝ => 1 * p.2 ^ 4) Γ := hZ0.mul_prod hW4
  have i3 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * (t * y + p.2) ^ 2) Γ := hZ2.mul_prod hK5int
  have i4 : Integrable (fun p : ℝ × ℝ => 1 * ((u ^ 2 + v ^ 2 * p.2 ^ 2) *
      (t ^ 2 * y ^ 2 + p.2 ^ 2))) Γ := hZ0.mul_prod hK4int
  have i5 : Integrable (fun p : ℝ × ℝ => 1 * (t * y + p.2) ^ 2) Γ := hZ0.mul_prod hK5int
  have hJ1 : ∫ p, p.1 ^ 4 * 1 ∂Γ = M4Z := by
    rw [integral_prod_mul (fun z => z ^ 4) (fun _ => (1 : ℝ)), integral_const, probReal_univ,
      one_smul, mul_one]
  have hJ2 : ∫ p, 1 * p.2 ^ 4 ∂Γ = M4W := by
    rw [integral_prod_mul (fun _ => (1 : ℝ)) (fun w => w ^ 4), integral_const, probReal_univ,
      one_smul, one_mul]
  have hJ3 : ∫ p, p.1 ^ 2 * (t * y + p.2) ^ 2 ∂Γ = σz ^ 2 * (t ^ 2 * y ^ 2 + σw ^ 2) := by
    rw [integral_prod_mul (fun z => z ^ 2) (fun w => (t * y + w) ^ 2), hZ2', hK5]
  have hJ4 : ∫ p, 1 * ((u ^ 2 + v ^ 2 * p.2 ^ 2) * (t ^ 2 * y ^ 2 + p.2 ^ 2)) ∂Γ =
      u ^ 2 * (t ^ 2 * y ^ 2) + u ^ 2 * σw ^ 2 + v ^ 2 * (t ^ 2 * y ^ 2) * σw ^ 2 +
        v ^ 2 * M4W := by
    rw [integral_prod_mul (fun _ => (1 : ℝ))
      (fun w => (u ^ 2 + v ^ 2 * w ^ 2) * (t ^ 2 * y ^ 2 + w ^ 2)), integral_const,
      probReal_univ, one_smul, one_mul, hK4]
  have hJ5 : ∫ p, 1 * (t * y + p.2) ^ 2 ∂Γ = t ^ 2 * y ^ 2 + σw ^ 2 := by
    rw [integral_prod_mul (fun _ => (1 : ℝ)) (fun w => (t * y + w) ^ 2), integral_const,
      probReal_univ, one_smul, one_mul, hK5]
  -- the integral of the bound
  have b1 : Integrable (fun p : ℝ × ℝ => (1 + δ) ^ 3 * u ^ 4 + 8 * c ^ 3 * (p.1 ^ 4 * 1)) Γ :=
    (integrable_const _).add (i1.const_mul _)
  have b2 : Integrable (fun p : ℝ × ℝ => (1 + δ) ^ 3 * u ^ 4 + 8 * c ^ 3 * (p.1 ^ 4 * 1) +
      8 * c ^ 3 * v ^ 4 * (1 * p.2 ^ 4)) Γ := b1.add (i2.const_mul _)
  have b3 : Integrable (fun p : ℝ × ℝ => (1 + δ) ^ 3 * u ^ 4 + 8 * c ^ 3 * (p.1 ^ 4 * 1) +
      8 * c ^ 3 * v ^ 4 * (1 * p.2 ^ 4) + ε * (1 + δ) * (p.1 ^ 2 * (t * y + p.2) ^ 2)) Γ :=
    b2.add (i3.const_mul _)
  have b4 : Integrable (fun p : ℝ × ℝ => (1 + δ) ^ 3 * u ^ 4 + 8 * c ^ 3 * (p.1 ^ 4 * 1) +
      8 * c ^ 3 * v ^ 4 * (1 * p.2 ^ 4) + ε * (1 + δ) * (p.1 ^ 2 * (t * y + p.2) ^ 2) +
      4 * ε * c * (1 * ((u ^ 2 + v ^ 2 * p.2 ^ 2) * (t ^ 2 * y ^ 2 + p.2 ^ 2)))) Γ :=
    b3.add (i4.const_mul _)
  have hBint : Integrable Bf Γ := b4.add (i5.const_mul _)
  have hBval : ∫ p, Bf p ∂Γ = (1 + δ) ^ 3 * u ^ 4 + 8 * c ^ 3 * M4Z + 8 * c ^ 3 * v ^ 4 * M4W +
      ε * (1 + δ) * (σz ^ 2 * (t ^ 2 * y ^ 2 + σw ^ 2)) +
      4 * ε * c * (u ^ 2 * (t ^ 2 * y ^ 2) + u ^ 2 * σw ^ 2 + v ^ 2 * (t ^ 2 * y ^ 2) * σw ^ 2 +
        v ^ 2 * M4W) + ε ^ 2 * (t ^ 2 * y ^ 2 + σw ^ 2) := by
    rw [hBf, integral_add b4 (i5.const_mul _), integral_add b3 (i4.const_mul _),
      integral_add b2 (i3.const_mul _), integral_add b1 (i2.const_mul _),
      integral_add (integrable_const _) (i1.const_mul _), integral_const, probReal_univ, one_smul,
      integral_const_mul (8 * c ^ 3) (fun p : ℝ × ℝ => p.1 ^ 4 * 1),
      integral_const_mul (8 * c ^ 3 * v ^ 4) (fun p : ℝ × ℝ => 1 * p.2 ^ 4),
      integral_const_mul (ε * (1 + δ)) (fun p : ℝ × ℝ => p.1 ^ 2 * (t * y + p.2) ^ 2),
      integral_const_mul (4 * ε * c)
        (fun p : ℝ × ℝ => 1 * ((u ^ 2 + v ^ 2 * p.2 ^ 2) * (t ^ 2 * y ^ 2 + p.2 ^ 2))),
      integral_const_mul (ε ^ 2) (fun p : ℝ × ℝ => 1 * (t * y + p.2) ^ 2),
      hJ1, hJ2, hJ3, hJ4, hJ5]
  -- the coefficients
  obtain ⟨hco4, hco2⟩ := sac_coeffs hσzρ hαρ hα4 hδ0 hδ1 hδg hε0 hεg hεK hρ1
  have hBnn : ∀ p, 0 ≤ Bf p := fun p => (sacV_nonneg hε0.le _).trans (hpt p)
  have hVm : Measurable fun x : ℝ × ℝ × ℝ => ENNReal.ofReal (sacV ε x + 1) := by
    unfold sacV; fun_prop
  calc ∫⁻ x, ENNReal.ofReal (sacV ε x + 1) ∂sacKernel Γ α σz σw (S, t, y)
      = ∫⁻ p, ENNReal.ofReal (sacV ε (sacStep α σz σw ((S, t, y), p)) + 1) ∂Γ := by
        rw [sacKernel, recursionKernel_apply _ (measurable_sacStep α σz σw),
          lintegral_map hVm (show Measurable fun p : ℝ × ℝ => sacStep α σz σw ((S, t, y), p)
            from (measurable_sacStep α σz σw).comp measurable_prodMk_left)]
    _ ≤ ∫⁻ p, ENNReal.ofReal (Bf p + 1) ∂Γ :=
        lintegral_mono fun p => ENNReal.ofReal_le_ofReal (by linarith [hpt p])
    _ = ENNReal.ofReal (∫ p, (Bf p + 1) ∂Γ) :=
        (ofReal_integral_eq_lintegral_ofReal (hBint.add (integrable_const 1))
          (Eventually.of_forall fun p => by
            change (0 : ℝ) ≤ Bf p + 1
            linarith [hBnn p])).symm
    _ = ENNReal.ofReal (∫ p, Bf p ∂Γ + 1) := by
        rw [integral_add hBint (integrable_const 1), integral_const, probReal_univ, one_smul]
    _ ≤ ENNReal.ofReal (ρ * sacV ε (S, t, y) + R + 1) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hBval]
        unfold sacV
        simp only
        -- the term-by-term bounds
        have h4εc : (0 : ℝ) ≤ 4 * ε * c := mul_nonneg (mul_nonneg (by norm_num) hε0.le) hc0
        have f1 := mul_le_mul_of_nonneg_left hU2 (by positivity : (0 : ℝ) ≤ (1 + δ) ^ 3)
        have hv4 : v ^ 4 ≤ Kv ^ 2 := by
          have := pow_le_pow_left₀ (sq_nonneg v) hV1 2
          calc v ^ 4 = (v ^ 2) ^ 2 := by ring
            _ ≤ Kv ^ 2 := this
        have f2 := mul_le_mul_of_nonneg_left hv4
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hc0 3)) hM4W0 :
          (0 : ℝ) ≤ 8 * c ^ 3 * M4W)
        have hu3 : u ^ 2 * (t ^ 2 * y ^ 2) ≤ α ^ 2 * σw ^ 2 / σz ^ 2 * t ^ 4 := by
          have h := mul_le_mul_of_nonneg_left hU3 (sq_nonneg t)
          rw [div_mul_eq_mul_div, le_div_iff₀ hσz2]
          linarith only [h]
        have f3 := mul_le_mul_of_nonneg_left hu3 h4εc
        have f4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hU1 hσw2.le)
          h4εc
        have hv5 : v ^ 2 * (t ^ 2 * y ^ 2) * σw ^ 2 ≤ α ^ 2 * t ^ 2 * σw ^ 2 := by
          have h := mul_le_mul_of_nonneg_left hV2 (mul_nonneg (sq_nonneg t) hσw2.le)
          linarith only [h]
        have f5 := mul_le_mul_of_nonneg_left hv5 h4εc
        have f6 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hV1 hM4W0)
          h4εc
        have ht2 : t ^ 2 ≤ t ^ 4 + 1 := by
          have h := sq_nonneg (t ^ 2 - 1)
          linarith only [h, sq_nonneg t]
        have f7 := mul_le_mul_of_nonneg_left ht2
          (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε0.le)
          hc0) (sq_nonneg α)) (sq_nonneg σw) : (0 : ℝ) ≤ 8 * ε * c * α ^ 2 * σw ^ 2)
        have g1 := mul_le_mul_of_nonneg_right hco4 (by positivity : (0 : ℝ) ≤ t ^ 4)
        have g2 := mul_le_mul_of_nonneg_right hco2 (by positivity : (0 : ℝ) ≤ t ^ 2 * y ^ 2)
        have g3 : 0 ≤ ρ * ε ^ 2 * y ^ 2 := by
          have : 0 < ρ := lt_of_le_of_lt (le_max_left _ _) hρ |>.trans_le' hσz2.le
          positivity
        rw [hK3] at g1
        rw [hR]
        have e1 : 4 * ε * c * (α ^ 2 * σw ^ 2 / σz ^ 2 * t ^ 4) =
            4 * ε * c * α ^ 2 * σw ^ 2 * (1 / σz ^ 2) * t ^ 4 := by ring
        rw [e1] at f3
        linarith only [f1, f2, f3, f4, f5, f6, f7, g1, g2, g3]

/-! ### Proposition 16.5.2 -/

/-- `sacSet` is measurable. -/
theorem measurableSet_sacSet (α σz : ℝ) : MeasurableSet (sacSet α σz) :=
  measurableSet_Icc.prod MeasurableSet.univ

/-- `sacSet` is absorbing (MT p. 36, `sacKernel_apply_Icc`). -/
theorem isAbsorbing_sacSet (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {α σz σw : ℝ}
    (hα : |α| < 1) (hσw : σw ≠ 0) : IsAbsorbing (sacKernel Γ α σz σw) (sacSet α σz) := by
  rintro ⟨S, th, Y⟩ hx
  simp only [sacSet, mem_prod, mem_univ, and_true] at hx
  exact sacKernel_apply_Icc Γ hα hσw hx

/-- The SAC chain restricted to `sacSet` is a Markov kernel. -/
theorem isMarkovKernel_sacRestrict {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0)
    (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] :
    IsMarkovKernel (restrictKernel (sacKernel Γ α σz σw) (measurableSet_sacSet α σz)) :=
  isMarkovKernel_restrictKernel _ _ (isAbsorbing_sacSet Γ hα hσw)

/-- The sublevel sets of `V` within `sacSet` are compact. -/
theorem isCompact_sacV_le {α σz ε : ℝ} (hε : 0 < ε) (L : ℝ) :
    IsCompact {x : sacSet α σz | sacV ε x.1 ≤ L} := by
  rw [Subtype.isCompact_iff]
  have himg : Subtype.val '' {x : sacSet α σz | sacV ε x.1 ≤ L} =
      sacSet α σz ∩ {x | sacV ε x ≤ L} := by
    ext x
    simp only [mem_image, mem_ofPred_eq, Subtype.exists, exists_and_right, exists_eq_right,
      mem_inter_iff]
    tauto
  rw [himg]
  have hc : Continuous (sacV ε) := by unfold sacV; fun_prop
  refine Metric.isCompact_of_isClosed_isBounded ((isClosed_Icc.prod isClosed_univ).inter
    (isClosed_le hc continuous_const)) ?_
  set B : ℝ := max (|σz ^ 2| + |σz ^ 2 / (1 - α ^ 2)|) (1 + |L| + |L| / ε ^ 2) with hB
  refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ × ℝ)) (r := B)).subset ?_
  rintro ⟨S, t, y⟩ ⟨hS, hV⟩
  simp only [sacSet, mem_prod, mem_Icc, mem_univ, and_true] at hS
  simp only [mem_ofPred_eq, sacV] at hV
  rw [Metric.mem_closedBall, dist_zero_right]
  have ht4 : t ^ 4 ≤ |L| := by
    have : 0 ≤ ε * t ^ 2 * y ^ 2 := by positivity
    have : 0 ≤ ε ^ 2 * y ^ 2 := by positivity
    linarith [le_abs_self L]
  have hy2 : y ^ 2 ≤ |L| / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : 0 ≤ t ^ 4 := by positivity
    have : 0 ≤ ε * t ^ 2 * y ^ 2 := by positivity
    linarith [le_abs_self L]
  have hS' : |S| ≤ |σz ^ 2| + |σz ^ 2 / (1 - α ^ 2)| := by
    rw [abs_le]; constructor <;> cases abs_cases (σz ^ 2) <;>
      cases abs_cases (σz ^ 2 / (1 - α ^ 2)) <;> linarith
  have ht : |t| ≤ 1 + |L| := by
    rcases le_or_gt |t| 1 with h | h
    · linarith [abs_nonneg L]
    · have h1 : |t| ≤ t ^ 4 := by
        have e : t ^ 4 = |t| ^ 4 := (Even.pow_abs ⟨2, rfl⟩ t).symm
        rw [e]
        nlinarith [pow_le_pow_right₀ h.le (show 1 ≤ 4 by norm_num)]
      linarith
  have hy : |y| ≤ 1 + |L| / ε ^ 2 := by
    rcases le_or_gt |y| 1 with h | h
    · have : 0 ≤ |L| / ε ^ 2 := by positivity
      linarith
    · have h1 : |y| ≤ y ^ 2 := by rw [← sq_abs]; nlinarith
      linarith
  have hnorm : ‖((S, t, y) : ℝ × ℝ × ℝ)‖ = max |S| (max |t| |y|) := by
    rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [hnorm]
  refine max_le (hS'.trans (le_max_left _ _)) (max_le ?_ ?_)
  · refine ht.trans (le_trans ?_ (le_max_right _ _))
    have : 0 ≤ |L| / ε ^ 2 := by positivity
    linarith
  · refine hy.trans (le_trans ?_ (le_max_right _ _))
    linarith [abs_nonneg L]

/-- **Proposition 16.5.2** (MT p. 417): for the SAC model with independent centred disturbances
(`E[Z²] = σ_z²`, `E[W²] = σ_w²`, finite fourth moments), `|α| < 1`, `σ_z, σ_w ≠ 0` and
`σ_z² < 1`, the chain on `[σ_z², σ_z²/(1 − α²)] × ℝ²` is `V`-uniformly ergodic for
`V = sacV ε₀ + 1` (16.44) and some `ε₀ > 0`, when it is `ψ`-irreducible and aperiodic with
compact sets petite: every invariant probability `π` has `Σ rⁿ |||Pⁿ − 1 ⊗ π|||_V < ∞`, and
(16.48), `|E_x[Y_k²] − ∫ y² dπ| ≤ R r⁻ᵏ V(x)`: `E_x[Y_k²] → ∫ y² dπ` at a geometric rate. -/
theorem proposition_16_5_2 {α σz σw : ℝ} (hα : |α| < 1) (hσz : σz ≠ 0) (hσw : σw ≠ 0)
    (hσz1 : σz ^ 2 < 1)
    (μZ μW : Measure ℝ) [IsProbabilityMeasure μZ] [IsProbabilityMeasure μW]
    (hZ2 : Integrable (fun z => z ^ 2) μZ) (hZ2' : ∫ z, z ^ 2 ∂μZ = σz ^ 2)
    (hZ4 : Integrable (fun z => z ^ 4) μZ)
    (hW1 : Integrable (fun w => w) μW) (hW1' : ∫ w, w ∂μW = 0)
    (hW2 : Integrable (fun w => w ^ 2) μW) (hW2' : ∫ w, w ^ 2 ∂μW = σw ^ 2)
    (hW4 : Integrable (fun w => w ^ 4) μW) {ψ : Measure (sacSet α σz)}
    (hψ : haveI := isMarkovKernel_sacRestrict (σz := σz) hα hσw (μZ.prod μW)
      IsMaximalIrreducibility (restrictKernel (sacKernel (μZ.prod μW) α σz σw)
        (measurableSet_sacSet α σz)) ψ)
    (hap : IsAperiodic (restrictKernel (sacKernel (μZ.prod μW) α σz σw)
      (measurableSet_sacSet α σz)) ψ)
    (hcpt : ∀ K : Set (sacSet α σz), IsCompact K →
      IsPetite (restrictKernel (sacKernel (μZ.prod μW) α σz σw) (measurableSet_sacSet α σz)) K) :
    haveI := isMarkovKernel_sacRestrict (σz := σz) hα hσw (μZ.prod μW)
    ∃ ε : ℝ, 0 < ε ∧
      IsPositive (restrictKernel (sacKernel (μZ.prod μW) α σz σw) (measurableSet_sacSet α σz)) ψ ∧
      ∀ (μ : Measure (sacSet α σz)) [IsProbabilityMeasure μ],
        IsInvariant (restrictKernel (sacKernel (μZ.prod μW) α σz σw)
          (measurableSet_sacSet α σz)) μ →
        IsVUniformlyErgodic (fun x : sacSet α σz => ENNReal.ofReal (sacV ε x.1 + 1))
          (restrictKernel (sacKernel (μZ.prod μW) α σz σw) (measurableSet_sacSet α σz)) μ ∧
        (∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∑' n, r ^ n * vErgDist
          (fun x : sacSet α σz => ENNReal.ofReal (sacV ε x.1 + 1))
          (restrictKernel (sacKernel (μZ.prod μW) α σz σw) (measurableSet_sacSet α σz)) μ n ≠ ∞) ∧
        ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ ∀ (x : sacSet α σz) (k : ℕ),
          ENNReal.ofReal |∫ z, z.1.2.2 ^ 2 ∂(restrictKernel (sacKernel (μZ.prod μW) α σz σw)
            (measurableSet_sacSet α σz) ^ k) x - ∫ z, z.1.2.2 ^ 2 ∂μ| ≤
            R * r⁻¹ ^ k * ENNReal.ofReal (sacV ε x.1 + 1) := by
  have hAbs := isAbsorbing_sacSet (μZ.prod μW) hα hσw (σz := σz)
  have hM := isMarkovKernel_sacRestrict (σz := σz) hα hσw (μZ.prod μW)
  have hMP := isMarkovKernel_sacKernel (μZ.prod μW) α σz σw
  set Q := restrictKernel (sacKernel (μZ.prod μW) α σz σw) (measurableSet_sacSet α σz) with hQ
  -- choose `ρ` with `max(σ_z², α⁴) < ρ < 1`
  have hα2 : α ^ 2 < 1 := by
    have h1 : α ^ 2 = |α| ^ 2 := (sq_abs α).symm
    rw [h1]; nlinarith [abs_nonneg α]
  have hα4 : α ^ 4 < 1 := by nlinarith [sq_nonneg α]
  set ρ := (max (σz ^ 2) (α ^ 4) + 1) / 2 with hρ
  have hρ1 : max (σz ^ 2) (α ^ 4) < ρ := by
    have := max_lt hσz1 hα4; rw [hρ]; linarith
  have hρ2 : ρ < 1 := by have := max_lt hσz1 hα4; rw [hρ]; linarith
  have hρ0 : 0 ≤ ρ := by
    have : 0 ≤ max (σz ^ 2) (α ^ 4) := le_trans (sq_nonneg σz) (le_max_left _ _)
    rw [hρ]; linarith
  obtain ⟨ε, hε, R, hR, hdrift⟩ :=
    sac_drift hα hσz hσw μZ μW hZ2 hZ2' hZ4 hW1 hW1' hW2 hW2' hW4 hρ1 hρ2
  set W : sacSet α σz → ℝ≥0∞ := fun x => ENNReal.ofReal (sacV ε x.1 + 1) with hW
  have hVc : Continuous (sacV ε) := by unfold sacV; fun_prop
  have hgm : Measurable fun y : ℝ × ℝ × ℝ => ENNReal.ofReal (sacV ε y + 1) :=
    (hVc.measurable.add_const 1).ennreal_ofReal
  have hWm : Measurable W := hgm.comp measurable_subtype_coe
  have hW1' : ∀ x, 1 ≤ W x := fun x => by
    rw [hW, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [sacV_nonneg hε.le x.1])
  have hWt : ∀ x, W x ≠ ∞ := fun x => ENNReal.ofReal_ne_top
  -- (15.35) for the restricted chain
  have hPW : ∀ x : sacSet α σz, ∫⁻ y, W y ∂Q x ≤ ENNReal.ofReal ρ * W x + ENNReal.ofReal (R + 1) :=
    fun x => by
      rw [hQ, lintegral_restrictKernel _ (measurableSet_sacSet α σz) hAbs x hgm]
      refine (hdrift x.1 x.2).trans ?_
      rw [hW, ← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_add (by
        have := sacV_nonneg hε.le x.1; positivity) (by linarith)]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith
  have hU : IsUnboundedOffPetite Q W := fun ℓ hℓ => by
    obtain ⟨a, ν, -, ha, hν, hle⟩ := hcpt _ (isCompact_sacV_le hε ℓ.toReal)
    refine ⟨a, ν, measurableSet_le hWm measurable_const, ha, hν, fun x hx => hle x ?_⟩
    have hx' : W x ≤ ℓ := hx
    have h1 : sacV ε x.1 + 1 ≤ ℓ.toReal := (ENNReal.ofReal_le_iff_le_toReal hℓ).1 hx'
    change sacV ε x.1 ≤ ℓ.toReal
    linarith
  obtain ⟨ρ', b', hρ', hb', C, hC, hd⟩ := (lemma_15_2_8 hWm hW1').2 ⟨hU, _, _,
    ENNReal.ofReal_lt_one.2 hρ2, ENNReal.ofReal_ne_top, hPW⟩
  rcases isEmpty_or_nonempty (sacSet α σz) with hX | ⟨⟨x₀⟩⟩
  · exact absurd (Measure.eq_zero_of_isEmpty ψ) hψ.1
  refine ⟨ε, hε, (geometric_ergodic_of_driftV4 hψ hap hWm hW1' hρ' hb' hC hd (hWt x₀)).1,
    fun μ _ hμ => ?_⟩
  obtain ⟨hsum, hlim⟩ := theorem_16_1_2 hψ hap hWm hW1' hWt hρ' hb' hC hd μ hμ
  obtain ⟨hμW, r, hr, -, R', hR', hbd⟩ :=
    vErgDist_le_of_driftV4 hψ hap hWm hW1' hWt hρ' hb' hC hd μ hμ
  refine ⟨⟨hμ, hlim⟩, hsum, (ENNReal.ofReal (ε ^ 2))⁻¹ * R', ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.2 (by simp [hε.ne'])) hR', r, hr, fun x k => ?_⟩
  -- (16.48)
  have := isMarkovKernel_pow Q k
  have hc : (ENNReal.ofReal (ε ^ 2))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp [hε.ne'])
  have hyb : ∀ z : sacSet α σz, ENNReal.ofReal |z.1.2.2 ^ 2| ≤
      (ENNReal.ofReal (ε ^ 2))⁻¹ * W z := fun z => by
    rw [hW, abs_of_nonneg (sq_nonneg _), ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    have := sacV_nonneg hε.le z.1
    have h1 : 0 ≤ z.1.2.1 ^ 4 + ε * z.1.2.1 ^ 2 * z.1.2.2 ^ 2 := by
      have : 0 ≤ ε * z.1.2.1 ^ 2 * z.1.2.2 ^ 2 := by positivity
      positivity
    unfold sacV
    nlinarith
  have hym : Measurable fun z : sacSet α σz => z.1.2.2 ^ 2 :=
    ((measurable_snd.comp measurable_snd).comp measurable_subtype_coe).pow_const 2
  have hint : ∀ (m : Measure (sacSet α σz)), ∫⁻ z, W z ∂m ≠ ∞ →
      Integrable (fun z : sacSet α σz => z.1.2.2 ^ 2) m := fun m hm =>
    integrable_of_ofReal_abs_le (f := fun z => (ENNReal.ofReal (ε ^ 2))⁻¹ * W z) hym hyb (by
      rw [lintegral_const_mul' _ _ hc]; exact ENNReal.mul_ne_top hc hm)
  have hV0 : W x ≠ 0 := (zero_lt_one.trans_le (hW1' x)).ne'
  have hQk : ∫⁻ z, W z ∂(Q ^ k) x ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hR' (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2
        (zero_lt_one.trans hr).ne'))) (hbd k)) (hWt x), hμW⟩)
      (lintegral_pow_le_vErgDist hWm Q μ k hV0 (hWt x))
  calc ENNReal.ofReal |∫ z, z.1.2.2 ^ 2 ∂(Q ^ k) x - ∫ z, z.1.2.2 ^ 2 ∂μ|
      ≤ (ENNReal.ofReal (ε ^ 2))⁻¹ * fNorm W ((Q ^ k) x) μ :=
        ofReal_abs_integral_sub_le_mul_fNorm hc hym hyb (hint _ hQk) (hint μ hμW)
    _ ≤ (ENNReal.ofReal (ε ^ 2))⁻¹ * (vErgDist W Q μ k * W x) :=
        mul_le_mul' le_rfl (fNorm_pow_le_vErgDist_mul Q μ k hV0 (hWt x))
    _ ≤ (ENNReal.ofReal (ε ^ 2))⁻¹ * (R' * r⁻¹ ^ k * W x) :=
        mul_le_mul' le_rfl (mul_le_mul' (hbd k) le_rfl)
    _ = (ENNReal.ofReal (ε ^ 2))⁻¹ * R' * r⁻¹ ^ k * W x := by ring

/-! ### The steady state performance (16.49) -/

/-- **(16.49)** (MT p. 417): if `E_π[Y²] = E_π[ΣY²] + σ_w²` and
`σ_z² E_π[Y²] = E_π[ΣY²] − α²σ_w² E_π[Σ]` (the two expectations of (2.23)–(2.24) under `P_π`),
then `E_π[Y²] = σ_w²/(1 − σ_z²) (1 + α² E_π[Σ])`, where `E_π[Σ] = E_π[|θ̃|²]`. -/
theorem eq_16_49 {a b c α σz σw : ℝ} (hσz : σz ^ 2 ≠ 1) (h1 : a = b + σw ^ 2)
    (h2 : σz ^ 2 * a = b - α ^ 2 * σw ^ 2 * c) :
    a = σw ^ 2 / (1 - σz ^ 2) * (1 + α ^ 2 * c) := by
  have h3 : (1 - σz ^ 2) * a = σw ^ 2 * (1 + α ^ 2 * c) := by linear_combination h1 - h2
  have h4 : 1 - σz ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hσz)
  field_simp
  linear_combination h3

/-- **The bounds on the steady state performance** (MT p. 417): with
`E_π[Σ] ∈ [σ_z², σ_z²/(1 − α²)]`,
`σ_w²/(1 − σ_z²) (1 + α²σ_z²) ≤ E_π[Y²] ≤ σ_w²/(1 − σ_z²) (1 + α²σ_z²/(1 − α²))`. -/
theorem sac_performance_bounds {a c α σz σw : ℝ} (hσz1 : σz ^ 2 < 1)
    (ha : a = σw ^ 2 / (1 - σz ^ 2) * (1 + α ^ 2 * c))
    (hc : c ∈ Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2))) :
    σw ^ 2 / (1 - σz ^ 2) * (1 + α ^ 2 * σz ^ 2) ≤ a ∧
      a ≤ σw ^ 2 / (1 - σz ^ 2) * (1 + α ^ 2 * (σz ^ 2 / (1 - α ^ 2))) := by
  have hk : 0 ≤ σw ^ 2 / (1 - σz ^ 2) := div_nonneg (sq_nonneg _) (by linarith)
  rw [ha]
  exact ⟨mul_le_mul_of_nonneg_left (by nlinarith [hc.1, sq_nonneg α]) hk,
    mul_le_mul_of_nonneg_left (by nlinarith [hc.2, sq_nonneg α]) hk⟩


end MeynTweedie.VUniformErgodicity

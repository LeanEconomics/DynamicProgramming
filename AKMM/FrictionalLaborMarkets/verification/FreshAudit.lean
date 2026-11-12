import OperatorsFixedPoints.Basics
import SearchAndMatching.JDBasics
import Mathlib.Analysis.SpecificLimits.Normed
import SearchAndMatching.DMMatching
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Applications.ODMcCall
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import AdditionalApplications.ContinuationValues
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A simple model of unemployment (the lake model)

AKMM, §20.3, pp. 595–597. Workers are employed or unemployed, the labour force is `1`, an
unemployed worker finds a job with probability `λ` and an employed worker loses it with
probability `σ`, both in `(0, 1)`. Unemployment follows `u_{t+1} = (1 − λ)u_t + σ(1 − u_t)`
(20.1).

* `eq_20_1`, `lakeNext`: the law of motion; `eq_20_2`: the unique steady state `ū = σ/(λ + σ)`,
  decreasing in `λ` and increasing in `σ` (`lake_ubar_anti_lam`, `lake_ubar_mono_sigma`).
* `lake_diff`, `lake_gap`: `u_{t+1} − u_t = (1 − λ − σ)(u_t − u_{t−1})` and
  `u_{t+1} − ū = (1 − λ − σ)(u_t − ū)`; `lake_abs_lt_one`: `|1 − λ − σ| < 1`.
* `lake_isContraction`, `lake_globallyStable`: the map is a contraction of modulus
  `|1 − λ − σ|` and globally stable (Sargent–Stachurski's `IsContractionOn`, `GloballyStable`);
  `lake_closed_form`, `lake_tendsto`, `lake_cauchy`: `u_t − ū = (1 − λ − σ)ᵗ(u_0 − ū)` (via
  Miao's `jd_affine_sol`), so `u_t → ū` and `(u_t)` is Cauchy.
* `lake_duration_series`, `lake_duration_recursion`: the expected duration of unemployment is
  `D = Σ_k (k + 1)λ(1 − λ)ᵏ = 1/λ`, and `D = 1/λ` is the unique solution of
  `D = λ·1 + (1 − λ)(1 + D)`.

Departure: the book says `|1 − λ − σ| ∈ (0, 1)`; it is `0` when `λ + σ = 1`
(`lake_abs_eq_zero_example`), so the correct range is `[0, 1)`. The numerical illustration
(`ū ≈ 7.0%`, `7.2%` after six months) is not formalised.
-/

namespace AKMM.FrictionalLaborMarkets

open Filter Topology

/-- AKMM, (20.1), p. 595: the lake-model map `u ↦ (1 − λ)u + σ(1 − u)`. -/
def lakeNext (lam σ u : ℝ) : ℝ := (1 - lam) * u + σ * (1 - u)

/-- AKMM, (20.1), p. 595: the law of motion is affine, `u_{t+1} = (1 − λ − σ)u_t + σ`. -/
theorem eq_20_1 (lam σ u : ℝ) : lakeNext lam σ u = (1 - lam - σ) * u + σ := by
  unfold lakeNext; ring

/-- AKMM, (20.2), p. 596: `ū = σ/(λ + σ)` is the unique steady state of (20.1). -/
theorem eq_20_2 {lam σ : ℝ} (h : 0 < lam + σ) (u : ℝ) :
    lakeNext lam σ u = u ↔ u = σ / (lam + σ) := by
  rw [eq_div_iff h.ne', lakeNext]
  constructor <;> intro hu <;> linarith

/-- AKMM, p. 596: the steady-state unemployment rate decreases in the job-finding probability. -/
theorem lake_ubar_anti_lam {σ lam₁ lam₂ : ℝ} (hσ : 0 < σ) (h₁ : 0 < lam₁) (h : lam₁ < lam₂) :
    σ / (lam₂ + σ) < σ / (lam₁ + σ) :=
  div_lt_div_of_pos_left hσ (by linarith) (by linarith)

/-- AKMM, p. 596: the steady-state unemployment rate increases in the separation probability. -/
theorem lake_ubar_mono_sigma {lam σ₁ σ₂ : ℝ} (hlam : 0 < lam) (h₁ : 0 < σ₁) (h : σ₁ < σ₂) :
    σ₁ / (lam + σ₁) < σ₂ / (lam + σ₂) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- AKMM, p. 596: `u_{t+1} − u_t = (1 − λ − σ)(u_t − u_{t−1})`. -/
theorem lake_diff {lam σ : ℝ} {u : ℕ → ℝ} (hu : ∀ t, u (t + 1) = lakeNext lam σ (u t)) (t : ℕ) :
    u (t + 2) - u (t + 1) = (1 - lam - σ) * (u (t + 1) - u t) := by
  rw [hu (t + 1), hu t, eq_20_1, eq_20_1]; ring

/-- AKMM, p. 596: `u_{t+1} − ū = (1 − λ − σ)(u_t − ū)`. -/
theorem lake_gap {lam σ : ℝ} (h : 0 < lam + σ) (u : ℝ) :
    lakeNext lam σ u - σ / (lam + σ) = (1 - lam - σ) * (u - σ / (lam + σ)) := by
  rw [eq_20_1]; field_simp; ring

/-- AKMM, p. 596: for `λ, σ ∈ (0, 1)`, `|1 − λ − σ| < 1`. -/
theorem lake_abs_lt_one {lam σ : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hs0 : 0 < σ)
    (hs1 : σ < 1) : |1 - lam - σ| < 1 := by
  rw [abs_lt]; constructor <;> linarith

/-- AKMM, p. 596 (correction): `|1 − λ − σ|` can be `0`, e.g. `λ = σ = 1/2`, so the printed
range `(0, 1)` should be `[0, 1)`. -/
theorem lake_abs_eq_zero_example : |1 - (1 / 2 : ℝ) - 1 / 2| = 0 := by norm_num

/-- AKMM, p. 596: the lake map is a contraction of modulus `|1 − λ − σ|` on `ℝ`. -/
theorem lake_isContraction {lam σ : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hs0 : 0 < σ)
    (hs1 : σ < 1) :
    SargentStachurski.OperatorsFixedPoints.IsContractionOn (lakeNext lam σ) Set.univ
      |1 - lam - σ| where
  mapsTo := fun _ _ ↦ trivial
  nonneg := abs_nonneg _
  lt_one := lake_abs_lt_one hl0 hl1 hs0 hs1
  norm_sub_le := fun u _ v _ ↦ by
    rw [eq_20_1, eq_20_1, Real.norm_eq_abs, Real.norm_eq_abs,
      show (1 - lam - σ) * u + σ - ((1 - lam - σ) * v + σ) = (1 - lam - σ) * (u - v) by ring,
      abs_mul]

/-- AKMM, p. 596: the lake map is globally stable: a unique steady state to which every path
converges. -/
theorem lake_globallyStable {lam σ : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hs0 : 0 < σ)
    (hs1 : σ < 1) : SargentStachurski.OperatorsFixedPoints.GloballyStable (lakeNext lam σ) :=
  (lake_isContraction hl0 hl1 hs0 hs1).globallyStable_univ

/-- AKMM, p. 596: the closed form `u_t − ū = (1 − λ − σ)ᵗ(u_0 − ū)`. -/
theorem lake_closed_form {lam σ : ℝ} (h : 0 < lam + σ) {u : ℕ → ℝ}
    (hu : ∀ t, u (t + 1) = lakeNext lam σ (u t)) (t : ℕ) :
    u t - σ / (lam + σ) = (1 - lam - σ) ^ t * (u 0 - σ / (lam + σ)) := by
  have ha : (1 - lam - σ) ≠ 1 := by intro h'; linarith
  have hu' : ∀ t, u (t + 1) = (1 - lam - σ) * u t + σ := fun t ↦ by rw [hu t, eq_20_1]
  have e : σ / (1 - (1 - lam - σ)) = σ / (lam + σ) := by congr 1; ring
  have := Miao.SearchAndMatching.jd_affine_sol ha hu' t
  rwa [e] at this

/-- AKMM, p. 596: the unemployment rate converges to its steady state `σ/(λ + σ)`. -/
theorem lake_tendsto {lam σ : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hs0 : 0 < σ) (hs1 : σ < 1)
    {u : ℕ → ℝ} (hu : ∀ t, u (t + 1) = lakeNext lam σ (u t)) :
    Tendsto u atTop (𝓝 (σ / (lam + σ))) := by
  have hu' : ∀ t, u (t + 1) = (1 - lam - σ) * u t + σ := fun t ↦ by rw [hu t, eq_20_1]
  have e : σ / (1 - (1 - lam - σ)) = σ / (lam + σ) := by congr 1; ring
  have := Miao.SearchAndMatching.jd_affine_tendsto (lake_abs_lt_one hl0 hl1 hs0 hs1) hu'
  rwa [e] at this

/-- AKMM, p. 596: the unemployment rate is a Cauchy sequence. -/
theorem lake_cauchy {lam σ : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hs0 : 0 < σ) (hs1 : σ < 1)
    {u : ℕ → ℝ} (hu : ∀ t, u (t + 1) = lakeNext lam σ (u t)) : CauchySeq u :=
  (lake_tendsto hl0 hl1 hs0 hs1 hu).cauchySeq

/-- AKMM, p. 596: the expected duration of unemployment computed as a series,
`D = λ·1 + (1 − λ)λ·2 + (1 − λ)²λ·3 + ⋯ = 1/λ`. -/
theorem lake_duration_series {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1) :
    HasSum (fun k : ℕ ↦ lam * (1 - lam) ^ k * ((k : ℝ) + 1)) (1 / lam) := by
  have hr : ‖(1 - lam : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h2 := hasSum_geometric_of_lt_one (r := 1 - lam) (by linarith) (by linarith)
  have h3 := (h1.add h2).mul_left lam
  have e : lam * ((1 - lam) / (1 - (1 - lam)) ^ 2 + (1 - (1 - lam))⁻¹) = 1 / lam := by
    rw [show 1 - (1 - lam) = lam by ring]
    field_simp; ring
  rw [e] at h3
  convert h3 using 1
  funext k; ring

/-- AKMM, p. 597: the recursive formulation `D = λ·1 + (1 − λ)(1 + D)` has the unique solution
`D = 1/λ`. -/
theorem lake_duration_recursion {lam : ℝ} (hl0 : 0 < lam) (D : ℝ) :
    D = lam * 1 + (1 - lam) * (1 + D) ↔ D = 1 / lam := by
  rw [eq_div_iff hl0.ne']
  constructor <;> intro h <;> nlinarith

end AKMM.FrictionalLaborMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The matching function and labour-market dynamics

AKMM, §20.4.1, pp. 597–599, and the definition (20.21) of p. 604. The matching function
`M(u, v)` is positive, strictly increasing in both arguments and has constant returns to scale on
the open orthant (`MatchFn`); the book's bounds `M(u, v) ≤ u`, `M(u, v) ≤ v` are the separate
property `MatchFn.Bounded`, because the Cobb–Douglas function (20.23) used from §20.6 on violates
them (`cd_not_bounded`).

* `lamW`, `lamF`, `eq_20_3`: `λ_w(θ) = M(1, θ)`, `λ_f(θ) = M(1/θ, 1)`, and the meeting
  probabilities `M(u, v)/u = λ_w(v/u)`, `M(u, v)/v = λ_f(v/u)` (`match_rate_worker`,
  `match_rate_firm`); `match_lamW_eq`: `λ_w(θ) = θλ_f(θ)`; `λ_w` increasing, `λ_f` decreasing
  (`match_lamW_strictMonoOn`, `match_lamF_strictAntiOn`); probabilities in `(0, 1]` under the
  bounds (`match_lamW_le_one`, `match_lamF_le_one`).
* `eq_20_4`: the law of motion; `eq_20_5`, `eq_20_6`: for constant `v > 0` the steady state `ū`
  solves `M(ū, v) + σū = σ`; it is unique (`match_ubar_unique`) and, when `u ↦ M(u, v)` is
  continuous and the bounds hold, exists in `(0, 1)` (`match_ubar_exists`); the Beveridge curve
  slopes down (`match_beveridge_anti`). As printed, (20.6) reads `M(v, ū) + σū = σ`, which is
  not equivalent (`eq_20_6_misprint`).
* `match_euler`: Euler's theorem `M = M₁u + M₂v` for a differentiable CRS matching function
  (used in 20.A.3); `matchElast`: the elasticity `η(u, v) = 1 − M₂v/M` (20.21), and
  `match_elast_eq`: `η(u, v) = −θλ_f′(θ)/λ_f(θ)` at `θ = v/u`.
* Instances: Miao's matching functions (`MatchFn.ofMiao`); the Cobb–Douglas function
  `χu^ηv^{1−η}` (20.23) via Miao's `dm_cdMatching`, with `λ_w = χθ^{1−η}`, `λ_f = χθ^{−η}`
  (`eq_20_23`); `skewMatch`, `M(u, v) = uv/(u + 2v)`, which satisfies the bounds and is
  asymmetric.
-/

namespace AKMM.FrictionalLaborMarkets

open Filter Topology

/-- AKMM, p. 597: a **matching function** `M(u, v)`: positive, strictly increasing in both
arguments and with constant returns to scale on the open orthant. -/
structure MatchFn where
  /-- the matching function -/
  M : ℝ → ℝ → ℝ
  /-- positivity on the open orthant -/
  pos : ∀ u v : ℝ, 0 < u → 0 < v → 0 < M u v
  /-- constant returns to scale -/
  homog : ∀ t u v : ℝ, 0 < t → 0 < u → 0 < v → M (t * u) (t * v) = t * M u v
  /-- strictly increasing in `u` -/
  mono_u : ∀ u u' v : ℝ, 0 < u → u < u' → 0 < v → M u v < M u' v
  /-- strictly increasing in `v` -/
  mono_v : ∀ u v v' : ℝ, 0 < u → 0 < v → v < v' → M u v < M u v'

/-- AKMM, p. 597: the bounds `M(u, v) ≤ u` and `M(u, v) ≤ v`. -/
def MatchFn.Bounded (MF : MatchFn) : Prop :=
  ∀ u v : ℝ, 0 < u → 0 < v → MF.M u v ≤ u ∧ MF.M u v ≤ v

/-- Every matching function of Miao (Ch. 18), which is also concave, is one in AKMM's sense. -/
def MatchFn.ofMiao (MF : Miao.SearchAndMatching.DMMatchingFn) : MatchFn where
  M := MF.M
  pos := MF.pos
  homog := MF.homog
  mono_u := MF.mono_u
  mono_v := MF.mono_v

/-- AKMM, (20.3), p. 598: the job-finding probability `λ_w(θ) = M(1, θ)`. -/
def lamW (MF : MatchFn) (θ : ℝ) : ℝ := MF.M 1 θ

/-- AKMM, p. 598: the job-filling probability `λ_f(θ) = M(1/θ, 1)`. -/
noncomputable def lamF (MF : MatchFn) (θ : ℝ) : ℝ := MF.M θ⁻¹ 1

/-- AKMM, (20.3), p. 598: a worker meets a firm with probability `M(u, v)/u = M(1, θ)`. -/
theorem match_rate_worker (MF : MatchFn) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    MF.M u v / u = lamW MF (v / u) := by
  have h := MF.homog u 1 (v / u) hu one_pos (div_pos hv hu)
  rw [mul_one, mul_div_cancel₀ v hu.ne'] at h
  rw [lamW, h]; field_simp

/-- AKMM, p. 598: a vacancy meets a worker with probability `M(u, v)/v = M(1/θ, 1)`. -/
theorem match_rate_firm (MF : MatchFn) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    MF.M u v / v = lamF MF (v / u) := by
  have h := MF.homog v (u / v) 1 hv (div_pos hu hv) one_pos
  rw [mul_one, mul_div_cancel₀ u hv.ne'] at h
  rw [lamF, inv_div, h]; field_simp

/-- AKMM, (20.3), p. 598: both meeting probabilities, with `θ = v/u`. -/
theorem eq_20_3 (MF : MatchFn) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    MF.M u v / u = lamW MF (v / u) ∧ MF.M u v / v = lamF MF (v / u) :=
  ⟨match_rate_worker MF hu hv, match_rate_firm MF hu hv⟩

/-- AKMM, p. 598: `λ_w(θ) = θλ_f(θ)`. -/
theorem match_lamW_eq (MF : MatchFn) {θ : ℝ} (hθ : 0 < θ) : lamW MF θ = θ * lamF MF θ := by
  have h := MF.homog θ θ⁻¹ 1 hθ (inv_pos.mpr hθ) one_pos
  rw [mul_inv_cancel₀ hθ.ne', mul_one] at h
  rw [lamW, lamF, h]

/-- AKMM, p. 598: `λ_w(θ) > 0`. -/
theorem match_lamW_pos (MF : MatchFn) {θ : ℝ} (hθ : 0 < θ) : 0 < lamW MF θ :=
  MF.pos _ _ one_pos hθ

/-- AKMM, p. 598: `λ_f(θ) > 0`. -/
theorem match_lamF_pos (MF : MatchFn) {θ : ℝ} (hθ : 0 < θ) : 0 < lamF MF θ :=
  MF.pos _ _ (inv_pos.mpr hθ) one_pos

/-- AKMM, p. 598: `λ_w` is increasing in `θ`. -/
theorem match_lamW_strictMonoOn (MF : MatchFn) : StrictMonoOn (lamW MF) (Set.Ioi 0) :=
  fun _ hx _ _ hxy ↦ MF.mono_v _ _ _ one_pos hx hxy

/-- AKMM, p. 598: `λ_f` is decreasing in `θ`. -/
theorem match_lamF_strictAntiOn (MF : MatchFn) : StrictAntiOn (lamF MF) (Set.Ioi 0) :=
  fun _ hx _ hy hxy ↦
    MF.mono_u _ _ _ (inv_pos.mpr (Set.mem_Ioi.mp hy)) (inv_strictAnti₀ hx hxy) one_pos

/-- AKMM, p. 597: under the bounds `λ_w(θ) ≤ 1` is a probability. -/
theorem match_lamW_le_one (MF : MatchFn) (hB : MF.Bounded) {θ : ℝ} (hθ : 0 < θ) :
    lamW MF θ ≤ 1 := (hB 1 θ one_pos hθ).1

/-- AKMM, p. 597: under the bounds `λ_f(θ) ≤ 1` is a probability. -/
theorem match_lamF_le_one (MF : MatchFn) (hB : MF.Bounded) {θ : ℝ} (hθ : 0 < θ) :
    lamF MF θ ≤ 1 := (hB θ⁻¹ 1 (inv_pos.mpr hθ) one_pos).2

/-- AKMM, (20.4), p. 598: the law of motion of unemployment,
`u_{t+1} = (1 − λ_w(θ_t))u_t + σ(1 − u_t)`; in terms of matches,
`u_{t+1} = u_t − M(u_t, v_t) + σ(1 − u_t)`. -/
theorem eq_20_4 (MF : MatchFn) {σ u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (1 - lamW MF (v / u)) * u + σ * (1 - u) = u - MF.M u v + σ * (1 - u) := by
  rw [← match_rate_worker MF hu hv]; field_simp

/-- AKMM, (20.5)–(20.6), p. 598: for constant `v > 0`, `ū > 0` is a steady state of (20.4),
`ū = σ/(λ_w(v/ū) + σ)`, iff `M(ū, v) + σū = σ` (the Beveridge curve). -/
theorem eq_20_5 (MF : MatchFn) {σ u v : ℝ} (hσ : 0 < σ) (hu : 0 < u) (hv : 0 < v) :
    u = σ / (lamW MF (v / u) + σ) ↔ MF.M u v + σ * u = σ := by
  have hl := match_lamW_pos MF (div_pos hv hu)
  rw [eq_div_iff (by linarith), ← match_rate_worker MF hu hv]
  constructor <;> intro h
  · field_simp at h; linarith
  · field_simp; linarith

/-- AKMM, (20.6), p. 598, corrected: the steady state is `M(ū, v) + σū = σ`; the steady state of
(20.4) is `ū = (1 − λ_w)ū + σ(1 − ū)`. -/
theorem eq_20_6 (MF : MatchFn) {σ u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (1 - lamW MF (v / u)) * u + σ * (1 - u) = u ↔ MF.M u v + σ * u = σ := by
  rw [eq_20_4 MF hu hv]
  constructor <;> intro h <;> linarith

/-- An asymmetric matching function satisfying all of AKMM's assumptions, `M(u, v) = uv/(u + 2v)`.
-/
noncomputable def skewMatch : MatchFn where
  M u v := u * v / (u + 2 * v)
  pos u v hu hv := by positivity
  homog t u v ht hu hv := by field_simp
  mono_u u u' v hu huu hv := by
    rw [div_lt_div_iff₀ (by positivity) (by linarith)]
    nlinarith [mul_pos hv hv, mul_pos (mul_pos hv hv) (sub_pos.mpr huu)]
  mono_v u v v' hu hv hvv := by
    rw [div_lt_div_iff₀ (by positivity) (by linarith)]
    nlinarith [mul_pos hu hu, mul_pos (mul_pos hu hu) (sub_pos.mpr hvv)]

/-- `skewMatch` satisfies AKMM's bounds `M ≤ u`, `M ≤ v`. -/
theorem skewMatch_bounded : skewMatch.Bounded := by
  intro u v hu hv
  change u * v / (u + 2 * v) ≤ u ∧ u * v / (u + 2 * v) ≤ v
  constructor
  · rw [div_le_iff₀ (by positivity)]; nlinarith [mul_pos hu hv]
  · rw [div_le_iff₀ (by positivity)]; nlinarith [mul_pos hv hv]

/-- AKMM, (20.6), p. 598, as printed: `M(v, ū) + σū = σ` is not the steady-state condition. With
`M = skewMatch`, `σ = 2/5`, `v = 1`, the steady state of (20.4) is `ū = 1/2`, but
`M(v, ū) + σū ≠ σ`. -/
theorem eq_20_6_misprint :
    (1 - lamW skewMatch (1 / (1 / 2))) * (1 / 2) + 2 / 5 * (1 - 1 / 2) = (1 / 2 : ℝ) ∧
      skewMatch.M 1 (1 / 2) + 2 / 5 * (1 / 2) ≠ (2 / 5 : ℝ) := by
  refine ⟨?_, ?_⟩
  · simp only [lamW, skewMatch]; norm_num
  · simp only [skewMatch]; norm_num

/-- AKMM, p. 599: the left-hand side `u ↦ M(u, v) + σu` of (20.6) is strictly increasing. -/
theorem match_bc_strictMonoOn (MF : MatchFn) {σ v : ℝ} (hσ : 0 ≤ σ) (hv : 0 < v) :
    StrictMonoOn (fun u ↦ MF.M u v + σ * u) (Set.Ioi 0) := by
  intro x hx y _ hxy
  have := MF.mono_u x y v hx hxy hv
  have : σ * x ≤ σ * y := mul_le_mul_of_nonneg_left hxy.le hσ
  simp only; linarith

/-- AKMM, p. 599: the steady state `ū` of (20.6) is unique. -/
theorem match_ubar_unique (MF : MatchFn) {σ v u₁ u₂ : ℝ} (hσ : 0 ≤ σ) (hv : 0 < v)
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) (h₁ : MF.M u₁ v + σ * u₁ = σ) (h₂ : MF.M u₂ v + σ * u₂ = σ) :
    u₁ = u₂ :=
  (match_bc_strictMonoOn MF hσ hv).injOn hu₁ hu₂ (h₁.trans h₂.symm)

/-- AKMM, p. 598 ("it is straightforward to show that there exists a unique steady-state value"):
if `u ↦ M(u, v)` is continuous on `u > 0` and the bounds hold, (20.6) has a solution
`ū ∈ (0, 1)`. Continuity is an added hypothesis. -/
theorem match_ubar_exists (MF : MatchFn) (hB : MF.Bounded) {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hc : ContinuousOn (fun u ↦ MF.M u v) (Set.Ioi 0)) :
    ∃ u ∈ Set.Ioo (0 : ℝ) 1, MF.M u v + σ * u = σ := by
  set u₀ := σ / (2 * (1 + σ)) with hu₀
  have hu₀p : 0 < u₀ := by positivity
  have hu₀1 : u₀ < 1 := by rw [hu₀, div_lt_one (by positivity)]; linarith
  have hlow : MF.M u₀ v + σ * u₀ < σ := by
    have h1 := (hB u₀ v hu₀p hv).1
    have : (1 + σ) * u₀ = σ / 2 := by rw [hu₀]; field_simp
    nlinarith
  have hhigh : σ < MF.M 1 v + σ * 1 := by have := MF.pos 1 v one_pos hv; linarith
  have hcont : ContinuousOn (fun u ↦ MF.M u v + σ * u) (Set.Icc u₀ 1) :=
    ((hc.mono fun x hx ↦ lt_of_lt_of_le hu₀p hx.1).add
      ((continuous_const.mul continuous_id).continuousOn))
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc hu₀1.le hcont ⟨hlow.le, hhigh.le⟩
  refine ⟨u, ⟨hu₀p.trans_le hu.1, lt_of_le_of_ne hu.2 ?_⟩, heq⟩
  rintro rfl
  simp only at heq
  linarith

/-- AKMM, p. 599: (20.6) is a negative relationship between `v` and `ū` (the Beveridge curve):
more vacancies give a strictly lower steady-state unemployment rate. -/
theorem match_beveridge_anti (MF : MatchFn) {σ v₁ v₂ u₁ u₂ : ℝ} (hσ : 0 ≤ σ) (hv₁ : 0 < v₁)
    (hv : v₁ < v₂) (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) (h₁ : MF.M u₁ v₁ + σ * u₁ = σ)
    (h₂ : MF.M u₂ v₂ + σ * u₂ = σ) : u₂ < u₁ := by
  by_contra hc
  have hle := not_lt.mp hc
  have a := MF.mono_v u₂ v₁ v₂ hu₂ hv₁ hv
  rcases hle.lt_or_eq with hlt | heq
  · have b := MF.mono_u u₁ u₂ v₁ hu₁ hlt hv₁
    nlinarith [mul_le_mul_of_nonneg_left hlt.le hσ]
  · subst heq; linarith

/-- AKMM, 20.A.3, p. 881: **Euler's theorem** for a constant-returns matching function that is
differentiable at `(u, v)`: `M(u, v) = M₁(u, v)u + M₂(u, v)v`, with `M₁ = M′(1, 0)`,
`M₂ = M′(0, 1)`. -/
theorem match_euler (MF : MatchFn) {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    {M' : ℝ × ℝ →L[ℝ] ℝ} (hM : HasFDerivAt (fun p : ℝ × ℝ ↦ MF.M p.1 p.2) M' (u, v)) :
    MF.M u v = M' (1, 0) * u + M' (0, 1) * v := by
  have hray : HasDerivAt (fun t : ℝ ↦ ((t * u, t * v) : ℝ × ℝ)) (u, v) 1 := by
    have h1 := (hasDerivAt_id (1 : ℝ)).mul_const u
    have h2 := (hasDerivAt_id (1 : ℝ)).mul_const v
    simpa using h1.prodMk h2
  have hM1 : HasFDerivAt (fun p : ℝ × ℝ ↦ MF.M p.1 p.2) M' ((1 : ℝ) * u, (1 : ℝ) * v) := by
    simpa using hM
  have hcomp := hM1.comp_hasDerivAt (1 : ℝ) hray
  have hlin : HasDerivAt (fun t : ℝ ↦ t * MF.M u v) (MF.M u v) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (MF.M u v)
  have heq : (fun t : ℝ ↦ (fun p : ℝ × ℝ ↦ MF.M p.1 p.2) (t * u, t * v)) =ᶠ[𝓝 1]
      fun t ↦ t * MF.M u v := by
    filter_upwards [lt_mem_nhds one_pos] with t ht
    exact MF.homog t u v ht hu hv
  have huniq := (hcomp.congr_of_eventuallyEq heq.symm).unique hlin
  have e : M' (u, v) = M' (1, 0) * u + M' (0, 1) * v := by
    have : ((u, v) : ℝ × ℝ) = u • ((1 : ℝ), (0 : ℝ)) + v • ((0 : ℝ), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
  rw [← huniq, ← e]

/-- AKMM, (20.21), p. 604: the elasticity of the matching function, `η(u, v) = 1 − M₂v/M`, where
`M₂` is the partial derivative in `v`. -/
noncomputable def matchElast (MF : MatchFn) (M₂ u v : ℝ) : ℝ := 1 - M₂ * v / MF.M u v

/-- AKMM, (20.21) and p. 608: under constant returns, `M₂(u, v) = λ_f(θ) + θλ_f′(θ)` at
`θ = v/u`, where `λ_f′` is the derivative of `λ_f`. -/
theorem match_M2 (MF : MatchFn) {u v d : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hd : HasDerivAt (lamF MF) d (v / u)) :
    HasDerivAt (fun y ↦ MF.M u y) (lamF MF (v / u) + v / u * d) v := by
  have hθ : HasDerivAt (fun y : ℝ ↦ y / u) u⁻¹ v := by
    simpa using (hasDerivAt_id v).div_const u
  have h := (hasDerivAt_id v).mul (hd.comp v hθ)
  have heq : (fun y ↦ MF.M u y) =ᶠ[𝓝 v] fun y ↦ id y * (lamF MF ∘ fun y ↦ y / u) y := by
    filter_upwards [lt_mem_nhds hv] with y hy
    simp only [id, Function.comp]
    rw [← match_rate_firm MF hu hy]; field_simp
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [id, Function.comp]; field_simp

/-- AKMM, (20.21) and p. 608: the elasticity of the matching function equals the negative of the
elasticity of `λ_f`: with `M₂ = λ_f(θ) + θd` (`match_M2`, `d = λ_f′(θ)`),
`η(u, v) = −θd/λ_f(θ)` at `θ = v/u`. -/
theorem match_elast_eq (MF : MatchFn) {u v : ℝ} (d : ℝ) (hu : 0 < u) (hv : 0 < v) :
    matchElast MF (lamF MF (v / u) + v / u * d) u v = -(v / u) * d / lamF MF (v / u) := by
  have hl := match_lamF_pos MF (div_pos hv hu)
  have hM : MF.M u v = v * lamF MF (v / u) := by
    rw [← match_rate_firm MF hu hv]; field_simp
  rw [matchElast, hM]
  field_simp
  ring

/-- AKMM, (20.23), p. 608: the Cobb–Douglas matching function `M(u, v) = χu^ηv^{1−η}`,
`χ > 0`, `η ∈ (0, 1)` (Miao's `dm_cdMatching`). -/
noncomputable def cdMatch (χ η : ℝ) (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) : MatchFn :=
  MatchFn.ofMiao (Miao.SearchAndMatching.dm_cdMatching χ η hχ hη0 hη1)

/-- AKMM, (20.23), p. 608: with Cobb–Douglas matching `λ_w(θ) = χθ^{1−η}` and
`λ_f(θ) = χθ^{−η}`. -/
theorem eq_20_23 {χ η : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) {θ : ℝ} (hθ : 0 < θ) :
    lamW (cdMatch χ η hχ hη0 hη1) θ = χ * θ ^ (1 - η) ∧
      lamF (cdMatch χ η hχ hη0 hη1) θ = χ * θ ^ (-η) := by
  refine ⟨?_, ?_⟩
  · simp [lamW, cdMatch, MatchFn.ofMiao, Miao.SearchAndMatching.dm_cdMatching]
  · simp only [lamF, cdMatch, MatchFn.ofMiao, Miao.SearchAndMatching.dm_cdMatching,
      Real.one_rpow, mul_one]
    rw [Real.inv_rpow hθ.le, Real.rpow_neg hθ.le]

/-- AKMM, p. 608: with Cobb–Douglas matching the elasticity of `λ_f` is `−η`: the derivative of
`λ_f(θ) = χθ^{−η}` is `−ηλ_f(θ)/θ`. -/
theorem cd_lamF_hasDerivAt {χ η : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) {θ : ℝ}
    (hθ : 0 < θ) :
    HasDerivAt (lamF (cdMatch χ η hχ hη0 hη1)) (-η * lamF (cdMatch χ η hχ hη0 hη1) θ / θ) θ := by
  have heq : (fun x ↦ χ * x ^ (-η)) =ᶠ[𝓝 θ] lamF (cdMatch χ η hχ hη0 hη1) := by
    filter_upwards [lt_mem_nhds hθ] with x hx
    exact ((eq_20_23 hχ hη0 hη1 hx).2).symm
  have h := ((Real.hasDerivAt_rpow_const (p := -η) (Or.inl hθ.ne')).const_mul
    χ).congr_of_eventuallyEq heq.symm
  refine h.congr_deriv ?_
  rw [(eq_20_23 hχ hη0 hη1 hθ).2, Real.rpow_sub_one hθ.ne']
  field_simp

/-- AKMM, (20.23), p. 608: the Cobb–Douglas function violates the bound `M(u, v) ≤ u` of p. 597
(at `u = 1`, `v = (2/χ)^{1/(1−η)}`, where `λ_w = 2 > 1`). -/
theorem cd_not_bounded {χ η : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) :
    ¬ (cdMatch χ η hχ hη0 hη1).Bounded := by
  intro hB
  set θ := (2 / χ) ^ (1 - η)⁻¹ with hθ
  have hθp : 0 < θ := by positivity
  have h1 := match_lamW_le_one _ hB hθp
  rw [(eq_20_23 hχ hη0 hη1 hθp).1, hθ, ← Real.rpow_mul (by positivity),
    inv_mul_cancel₀ (by linarith), Real.rpow_one] at h1
  field_simp at h1
  linarith

end AKMM.FrictionalLaborMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Market equilibrium under endogenous vacancy creation

AKMM, §20.4.2, pp. 599–602, §20.4.3, pp. 603–604, and Appendices 20.A.1–20.A.2, pp. 879–880.
Productivity `z` follows a Markov chain on a finite set `Z` with transition weights `P z z'`;
the conditional expectation is `dmpEx P f z = Σ_{z'} P z z' f(z')`, and the market tightness
`θ(z)`, the wage `w(z)` and the values `J, V, W, U` are functions of `z`. (The book allows a
general Markov process; the derivations use only the linearity of `E`. A deterministic `z` is
the case `Z = Unit`.)

* `eq_20_10`: (20.8)–(20.9) give `κ/λ_f(θ) = βE[J(z′)]`.
* `eq_20_15`: given the continuation values, a wage `w` maximises the generalised Nash product
  (20.13), over wages with nonnegative surpluses, iff `(1 − γ)(W̃ − U) = γ(J̃ − V)` (by Miao's
  `jd_nash_iff`); `eq_20_A_1`: with positive surpluses the first-order condition of 20.A.1 is
  equivalent to (20.15).
* `dmp_J_div`: from the six equilibrium equations, `J(z)/(1 − γ) = z − b +
  (1 − σ − γλ_w(θ(z)))/(1 − γ) · κ/λ_f(θ(z))`; `eq_20_16`: the job-creation difference equation.
* `eq_20_A_2`: the wage `w = b + γ(z − b) + βE[(1 − γ)λ_w(θ)(W′ − U′)] = b + γ(z − b) + γθκ`.
* `eq_20_18`, `eq_20_19`: the two-equation system in `(θ, S)` with
  `S_t = E_t[W − U + J − V]`.

Departure: the book's Nash problem has no constraint; the maximisation is over wages giving both
parties a nonnegative surplus (where the Nash product is defined).
-/

namespace AKMM.FrictionalLaborMarkets

variable {Z : Type*} [Fintype Z]

/-- The conditional expectation `E[f(z′) | z] = Σ_{z'} P(z, z′) f(z′)`. -/
def dmpEx (P : Z → Z → ℝ) (f : Z → ℝ) (z : Z) : ℝ := ∑ z', P z z' * f z'

/-- Linearity of the conditional expectation: sums. -/
theorem dmp_ex_add (P : Z → Z → ℝ) (f g : Z → ℝ) (z : Z) :
    dmpEx P (fun z' ↦ f z' + g z') z = dmpEx P f z + dmpEx P g z := by
  simp only [dmpEx, mul_add, Finset.sum_add_distrib]

/-- Linearity of the conditional expectation: constant multiples. -/
theorem dmp_ex_mul (P : Z → Z → ℝ) (c : ℝ) (f : Z → ℝ) (z : Z) :
    dmpEx P (fun z' ↦ c * f z') z = c * dmpEx P f z := by
  simp only [dmpEx, Finset.mul_sum]; congr 1; funext z'; ring

/-- The conditional expectation depends only on the values of the integrand. -/
theorem dmp_ex_congr (P : Z → Z → ℝ) {f g : Z → ℝ} (h : ∀ z', f z' = g z') (z : Z) :
    dmpEx P f z = dmpEx P g z := by
  simp only [dmpEx, h]

/-- AKMM, (20.10), p. 600: the vacancy value (20.8) and free entry (20.9) give
`κ/λ_f(θ(z)) = βE[J(z′)]`. -/
theorem eq_20_10 (MF : MatchFn) (P : Z → Z → ℝ) {κ β : ℝ} {θ : Z → ℝ} {J V : Z → ℝ}
    (hθ : ∀ z, 0 < θ z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0) (z : Z) : κ / lamF MF (θ z) = β * dmpEx P J z := by
  have hl := match_lamF_pos MF (hθ z)
  have h := h8 z
  rw [h9 z, dmp_ex_congr P (g := fun z' ↦ lamF MF (θ z) * J z') (fun z' ↦ by rw [h9 z']; ring),
    dmp_ex_mul] at h
  rw [div_eq_iff hl.ne']
  linarith

/-- AKMM, (20.13)–(20.15), p. 601: with worker surplus `W̃(w) − U = a + w` and firm surplus
`J̃(w) − V = c − w` (the continuation values do not depend on `w`), a wage with nonnegative
surpluses maximises the generalised Nash product `(W̃ − U)^γ(J̃ − V)^{1−γ}` over all such wages
iff `(1 − γ)(W̃ − U) = γ(J̃ − V)`. -/
theorem eq_20_15 {γ a c w : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hW : 0 ≤ a + w) (hF : 0 ≤ c - w) :
    (∀ w', 0 ≤ a + w' → 0 ≤ c - w' →
      (a + w') ^ γ * (c - w') ^ (1 - γ) ≤ (a + w) ^ γ * (c - w) ^ (1 - γ)) ↔
      (1 - γ) * (a + w) = γ * (c - w) := by
  have h := Miao.SearchAndMatching.jd_nash_iff (a := a) (c := c) (w := w) hγ0 hγ1 one_pos
    (by simpa using hW) hF
  simp only [one_mul, mul_one] at h
  exact h

/-- AKMM, 20.A.1, p. 879: the generalised Nash product `f(w) = (a + w)^γ(c − w)^{1−γ}` has
derivative `γ(a + w)^{γ−1}(c − w)^{1−γ} − (1 − γ)(a + w)^γ(c − w)^{−γ}` (using
`∂W̃/∂w = 1`, `∂J̃/∂w = −1`), and with positive surpluses the first-order condition `f′(w) = 0` is
equivalent to (20.15). -/
theorem eq_20_A_1 {γ a c w : ℝ} (hW : 0 < a + w) (hF : 0 < c - w) :
    HasDerivAt (fun x ↦ (a + x) ^ γ * (c - x) ^ (1 - γ))
      (γ * (a + w) ^ (γ - 1) * (c - w) ^ (1 - γ) - (1 - γ) * (a + w) ^ γ * (c - w) ^ (-γ)) w ∧
    (γ * (a + w) ^ (γ - 1) * (c - w) ^ (1 - γ) - (1 - γ) * (a + w) ^ γ * (c - w) ^ (-γ) = 0 ↔
      (1 - γ) * (a + w) = γ * (c - w)) := by
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun x ↦ (a + x) ^ γ) (1 * γ * (a + w) ^ (γ - 1)) w :=
      ((hasDerivAt_id w).const_add a).rpow_const (Or.inl hW.ne')
    have h2 : HasDerivAt (fun x ↦ (c - x) ^ (1 - γ)) (-1 * (1 - γ) * (c - w) ^ (1 - γ - 1)) w :=
      ((hasDerivAt_id w).const_sub c).rpow_const (Or.inl hF.ne')
    refine (h1.mul h2).congr_deriv ?_
    rw [show 1 - γ - 1 = -γ by ring]; ring
  · have e1 : (a + w) ^ (γ - 1) = (a + w) ^ γ / (a + w) := Real.rpow_sub_one hW.ne' γ
    have e2 : (c - w) ^ (-γ) = (c - w) ^ (1 - γ) / (c - w) := by
      rw [← Real.rpow_sub_one hF.ne']; ring_nf
    have p1 : 0 < (a + w) ^ γ := Real.rpow_pos_of_pos hW γ
    have p2 : 0 < (c - w) ^ (1 - γ) := Real.rpow_pos_of_pos hF _
    rw [e1, e2]
    have key : γ * ((a + w) ^ γ / (a + w)) * (c - w) ^ (1 - γ) -
        (1 - γ) * (a + w) ^ γ * ((c - w) ^ (1 - γ) / (c - w)) =
        ((a + w) ^ γ * (c - w) ^ (1 - γ) / ((a + w) * (c - w))) *
          (γ * (c - w) - (1 - γ) * (a + w)) := by
      field_simp
    rw [key, mul_eq_zero]
    have : (a + w) ^ γ * (c - w) ^ (1 - γ) / ((a + w) * (c - w)) ≠ 0 := by positivity
    constructor
    · rintro (h | h)
      · exact absurd h this
      · linarith
    · intro h; right; linarith

/-- AKMM, (20.16) and (20.42) for the basic model, p. 601: the six equilibrium equations (20.7),
(20.8), (20.9), (20.11), (20.12), (20.15) give `J(z)/(1 − γ) = z − b +
(1 − σ − γλ_w(θ(z)))/(1 − γ) · κ/λ_f(θ(z))`. -/
theorem dmp_J_div (MF : MatchFn) (P : Z → Z → ℝ) {κ β σ γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z + β * dmpEx P (fun z' ↦ (1 - σ) * J z' + σ * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    J z / (1 - γ) = zv z - b + (1 - σ - γ * lamW MF (θ z)) / (1 - γ) * (κ / lamF MF (θ z)) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have hJ := h7 z
  rw [dmp_ex_congr P (g := fun z' ↦ (1 - σ) * J z') (fun z' ↦ by rw [h9 z']; ring),
    dmp_ex_mul] at hJ
  have hWU : W z - U z = w z - b + β * ((1 - σ - lamW MF (θ z)) * dmpEx P J z * γ / (1 - γ)) := by
    rw [h11 z, h12 z]
    have e : ∀ z', (1 - σ) * W z' + σ * U z' - (lamW MF (θ z) * W z' +
        (1 - lamW MF (θ z)) * U z') = ((1 - σ - lamW MF (θ z)) * γ / (1 - γ)) * J z' := by
      intro z'
      have := h15 z'
      rw [h9 z'] at this
      have hw : W z' - U z' = γ * J z' / (1 - γ) := by
        rw [eq_div_iff hγ]; linarith
      calc _ = (1 - σ - lamW MF (θ z)) * (W z' - U z') := by ring
        _ = _ := by rw [hw]; ring
    have := dmp_ex_congr P e z
    rw [dmp_ex_mul] at this
    have hsub : dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z -
        dmpEx P (fun z' ↦ lamW MF (θ z) * W z' + (1 - lamW MF (θ z)) * U z') z =
        dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z' - (lamW MF (θ z) * W z' +
          (1 - lamW MF (θ z)) * U z')) z := by
      simp only [dmpEx, ← Finset.sum_sub_distrib, mul_sub]
    calc _ = w z - b + β * (dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z -
        dmpEx P (fun z' ↦ lamW MF (θ z) * W z' + (1 - lamW MF (θ z)) * U z') z) := by ring
      _ = _ := by rw [hsub, this]; ring
  have hsum : J z / (1 - γ) = J z + (W z - U z) := by
    have := h15 z
    rw [h9 z] at this
    field_simp; linarith
  rw [hsum, hJ, hWU, show κ / lamF MF (θ z) = β * dmpEx P J z from h10]
  field_simp
  ring

/-- AKMM, (20.16), p. 601: the **job-creation difference equation**
`κ/((1 − γ)λ_f(θ_t)) = βE[z_{t+1} − b + (1 − σ − γλ_w(θ_{t+1}))/(1 − γ) · κ/λ_f(θ_{t+1})]`,
derived from the six equilibrium equations (20.7), (20.8), (20.9), (20.11), (20.12), (20.15). -/
theorem eq_20_16 (MF : MatchFn) (P : Z → Z → ℝ) {κ β σ γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z + β * dmpEx P (fun z' ↦ (1 - σ) * J z' + σ * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    κ / ((1 - γ) * lamF MF (θ z)) = β * dmpEx P (fun z' ↦ zv z' - b +
      (1 - σ - γ * lamW MF (θ z')) / (1 - γ) * (κ / lamF MF (θ z'))) z := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have e := dmp_ex_congr P (fun z' ↦ (dmp_J_div MF P hγ1 hθ h7 h8 h9 h11 h12 h15 z').symm) z
  rw [e, show (fun z' ↦ J z' / (1 - γ)) = fun z' ↦ (1 - γ)⁻¹ * J z' by
    funext z'; ring, dmp_ex_mul, mul_left_comm, ← h10]
  field_simp

/-- AKMM, (20.A.2), p. 879: the equilibrium wage. From (20.7), (20.9), (20.11), (20.12) and
(20.15), `w = b + γ(z − b) + βE[(1 − γ)λ_w(θ)(W(z′) − U(z′))]`, and with (20.10),
`w = b + γ(z − b) + γθκ`. -/
theorem eq_20_A_2 (MF : MatchFn) (P : Z → Z → ℝ) {κ β σ γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z + β * dmpEx P (fun z' ↦ (1 - σ) * J z' + σ * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    w z = b + γ * (zv z - b) + β * dmpEx P (fun z' ↦ (1 - γ) * lamW MF (θ z) *
      (W z' - U z')) z ∧
    w z = b + γ * (zv z - b) + γ * θ z * κ := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have hJdiv := dmp_J_div MF P hγ1 hθ h7 h8 h9 h11 h12 h15 z
  have hJ := h7 z
  rw [dmp_ex_congr P (g := fun z' ↦ (1 - σ) * J z') (fun z' ↦ by rw [h9 z']; ring),
    dmp_ex_mul] at hJ
  have hWU : ∀ z', (1 - γ) * lamW MF (θ z) * (W z' - U z') = lamW MF (θ z) * γ * J z' := by
    intro z'
    have := h15 z'
    rw [h9 z', sub_zero] at this
    linear_combination lamW MF (θ z) * this
  have hE : β * dmpEx P (fun z' ↦ (1 - γ) * lamW MF (θ z) * (W z' - U z')) z =
      γ * θ z * κ := by
    rw [dmp_ex_congr P hWU, show (fun z' ↦ lamW MF (θ z) * γ * J z') =
      fun z' ↦ (lamW MF (θ z) * γ) * J z' from rfl, dmp_ex_mul,
      match_lamW_eq MF (hθ z)]
    have hl := match_lamF_pos MF (hθ z)
    have : β * dmpEx P J z = κ / lamF MF (θ z) := h10.symm
    calc _ = θ z * γ * lamF MF (θ z) * (β * dmpEx P J z) := by ring
      _ = _ := by rw [this]; field_simp
  have hw : w z = b + γ * (zv z - b) + γ * θ z * κ := by
    have hl := match_lamF_pos MF (hθ z)
    have hβJ : β * dmpEx P J z = κ / lamF MF (θ z) := h10.symm
    have hK : lamF MF (θ z) * (κ / lamF MF (θ z)) = κ := by field_simp
    have h1 : J z = (1 - γ) * (zv z - b) + (1 - σ) * (κ / lamF MF (θ z)) -
        γ * θ z * (lamF MF (θ z) * (κ / lamF MF (θ z))) := by
      have := hJdiv
      rw [match_lamW_eq MF (hθ z), div_eq_iff hγ] at this
      rw [this]; field_simp; ring
    rw [hK] at h1
    have h2 : J z = zv z - w z + (1 - σ) * (κ / lamF MF (θ z)) := by
      rw [hJ, ← hβJ]; ring
    linarith
  exact ⟨by rw [hE]; exact hw, hw⟩

/-- AKMM, p. 603: the expected surplus `S(z) = E[W(z′) − U(z′) + J(z′) − V(z′)]`. -/
def dmpSurplus (P : Z → Z → ℝ) (J V W U : Z → ℝ) (z : Z) : ℝ :=
  dmpEx P (fun z' ↦ W z' - U z' + J z' - V z') z

/-- AKMM, (20.18), p. 603: `κ = λ_f(θ)(1 − γ)βS`. -/
theorem eq_20_18 (MF : MatchFn) (P : Z → Z → ℝ) {κ β γ : ℝ} (hγ1 : γ < 1)
    {θ J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0) (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    κ = lamF MF (θ z) * (1 - γ) * β * dmpSurplus P J V W U z := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have hl := match_lamF_pos MF (hθ z)
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have e : ∀ z', W z' - U z' + J z' - V z' = (1 - γ)⁻¹ * J z' := by
    intro z'
    have := h15 z'
    rw [h9 z'] at this ⊢
    field_simp; linarith
  rw [dmpSurplus, dmp_ex_congr P e, dmp_ex_mul]
  rw [div_eq_iff hl.ne'] at h10
  field_simp
  linarith

/-- AKMM, (20.19), p. 604: `S_t = E_t[z_{t+1} − b + βS_{t+1}(1 − σ − γλ_w(θ_{t+1}))]`. -/
theorem eq_20_19 (MF : MatchFn) (P : Z → Z → ℝ) {κ β σ γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z + β * dmpEx P (fun z' ↦ (1 - σ) * J z' + σ * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    dmpSurplus P J V W U z = dmpEx P (fun z' ↦ zv z' - b +
      β * dmpSurplus P J V W U z' * (1 - σ - γ * lamW MF (θ z'))) z := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  refine dmp_ex_congr P (fun z' ↦ ?_) z
  have hJ := dmp_J_div MF P hγ1 hθ h7 h8 h9 h11 h12 h15 z'
  have h18 := eq_20_18 MF P hγ1 hθ h8 h9 h15 z'
  have hl := match_lamF_pos MF (hθ z')
  have e : W z' - U z' + J z' - V z' = J z' / (1 - γ) := by
    have := h15 z'
    rw [h9 z'] at this ⊢
    field_simp; linarith
  rw [e, hJ]
  have hk : κ / lamF MF (θ z') = (1 - γ) * β * dmpSurplus P J V W U z' := by
    rw [div_eq_iff hl.ne', h18]; ring
  rw [hk]
  field_simp

end AKMM.FrictionalLaborMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The steady state and the transition dynamics of the DMP model

AKMM, §20.4.2, pp. 601–602, with footnotes 6–7. With constant productivity `z` the job-creation
equation (20.16) is the first-order difference equation
`κ/((1 − γ)λ_f(θ_t)) = β[z − b + (1 − σ − γλ_w(θ_{t+1}))/(1 − γ) · κ/λ_f(θ_{t+1})]`
(`jcLHS θ_t = β · jcRHS θ_{t+1}`).

* `eq_20_17`, `ss_phi_strictAntiOn`, `ss_unique`: multiplying (20.17) by `λ_f(θ̄)` gives
  `jcPhi(θ̄) = 0` with `jcPhi` strictly decreasing when `z > b`, so there is at most one steady
  state.
* `ss_exists`, `ss_exists_of_tendsto`, `ss_cd_existsUnique`: existence, which the book does not
  argue, holds if `λ_f` is continuous, `λ_f(θ) → 0` as `θ → ∞` and the steady-state map is
  positive somewhere (for instance if `λ_f → ∞` as `θ → 0`); the Cobb–Douglas case (20.23) has a
  unique steady state for every `z > b`.
* `ss_theta_mono_z`, `ss_ubar_strictAntiOn`, `ss_vbar_strictMonoOn`: a fall in `z` lowers `θ̄`,
  raises `ū` and lowers `v̄ = θ̄ū` (Figure 20.5, p. 602).
* Footnote 6: `fn6_rhs_hasDerivAt`, `fn6_rhs_strictMonoOn`: with `η = −θλ_f′/λ_f` the right side
  of (20.16) has derivative `κ((1 − σ)η − γλ_w)/((1 − γ)λ_w)`, so it is increasing where
  `(1 − σ)η − γλ_w > 0`, and then `θ_{t+1}` is an increasing function of `θ_t`
  (`fn6_next_strictMono`).
* Footnote 7: `fn7_slope`, `fn7_slope_gt_one`: at `θ̄`, `dθ_{t+1}/dθ_t = η/(β((1 − σ)η − γλ_w))`,
  which exceeds `1`; `fn7_diverge_above`, `fn7_diverge_below`, `fn7_jump`: any path with
  `θ_0 ≠ θ̄` moves monotonically away from `θ̄`, so the only path converging to `θ̄` is the
  constant one, and after a permanent shock `θ` jumps at once to its new steady state.

Departures: existence of `θ̄` is proved under the stated limit conditions (the book asserts it);
the divergence of footnote 7 is proved globally from the monotonicity of footnote 6 on an interval
containing the path, rather than from the local slope.
-/

namespace AKMM.FrictionalLaborMarkets

open Filter Topology

/-- The left side of (20.16), `κ/((1 − γ)λ_f(θ))`. -/
noncomputable def jcLHS (MF : MatchFn) (κ γ θ : ℝ) : ℝ := κ / ((1 - γ) * lamF MF θ)

/-- The bracket on the right side of (20.16), `z − b + (1 − σ − γλ_w(θ))/(1 − γ) · κ/λ_f(θ)`. -/
noncomputable def jcRHS (MF : MatchFn) (z b σ γ κ θ : ℝ) : ℝ :=
  z - b + (1 - σ - γ * lamW MF θ) / (1 - γ) * (κ / lamF MF θ)

/-- (20.17) multiplied by `λ_f(θ)`: `β[(z − b)λ_f(θ) + (1 − σ − γλ_w(θ))κ/(1 − γ)] − κ/(1 − γ)`. -/
noncomputable def jcPhi (MF : MatchFn) (z b σ γ κ β θ : ℝ) : ℝ :=
  β * ((z - b) * lamF MF θ + (1 - σ - γ * lamW MF θ) * κ / (1 - γ)) - κ / (1 - γ)

/-- The identity behind p. 601: `λ_f(θ)(β·jcRHS(θ) − jcLHS(θ)) = jcPhi(θ)`. -/
theorem ss_phi_eq (MF : MatchFn) {z b σ γ κ β θ : ℝ} (hγ1 : γ < 1) (hθ : 0 < θ) :
    lamF MF θ * (β * jcRHS MF z b σ γ κ θ - jcLHS MF κ γ θ) = jcPhi MF z b σ γ κ β θ := by
  have hl := match_lamF_pos MF hθ
  have hγ : (1 - γ) ≠ 0 := by linarith
  unfold jcRHS jcLHS jcPhi
  field_simp

/-- AKMM, (20.17), p. 601: `θ̄` is a steady state of (20.16) iff `jcPhi(θ̄) = 0` ("multiplying by
`λ_f(θ̄)` on both sides"). -/
theorem eq_20_17 (MF : MatchFn) {z b σ γ κ β θ : ℝ} (hγ1 : γ < 1) (hθ : 0 < θ) :
    jcLHS MF κ γ θ = β * jcRHS MF z b σ γ κ θ ↔ jcPhi MF z b σ γ κ β θ = 0 := by
  have hl := match_lamF_pos MF hθ
  rw [← ss_phi_eq MF hγ1 hθ, mul_eq_zero, or_iff_right hl.ne', sub_eq_zero, eq_comm]

/-- AKMM, p. 601: the right side of (20.17) multiplied by `λ_f` is decreasing in `θ`: `jcPhi` is
strictly decreasing (when `z > b`, `κ, β > 0`, `γ ∈ [0, 1)`). -/
theorem ss_phi_strictAntiOn (MF : MatchFn) {z b σ γ κ β : ℝ} (hzb : b < z) (hκ : 0 < κ)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    StrictAntiOn (jcPhi MF z b σ γ κ β) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hf := match_lamF_strictAntiOn MF hx hy hxy
  have hw := match_lamW_strictMonoOn MF hx hy hxy
  have h1γ : 0 < 1 - γ := by linarith
  unfold jcPhi
  have e1 : (z - b) * lamF MF y < (z - b) * lamF MF x := mul_lt_mul_of_pos_left hf (by linarith)
  have e2 : (1 - σ - γ * lamW MF y) * κ / (1 - γ) ≤ (1 - σ - γ * lamW MF x) * κ / (1 - γ) := by
    apply div_le_div_of_nonneg_right _ h1γ.le
    apply mul_le_mul_of_nonneg_right _ hκ.le
    nlinarith
  nlinarith

/-- AKMM, p. 601: (20.17) has at most one solution `θ̄ > 0`. -/
theorem ss_unique (MF : MatchFn) {z b σ γ κ β θ₁ θ₂ : ℝ} (hzb : b < z) (hκ : 0 < κ)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (h₁ : jcLHS MF κ γ θ₁ = β * jcRHS MF z b σ γ κ θ₁)
    (h₂ : jcLHS MF κ γ θ₂ = β * jcRHS MF z b σ γ κ θ₂) : θ₁ = θ₂ := by
  rw [eq_20_17 MF hγ1 hθ₁] at h₁
  rw [eq_20_17 MF hγ1 hθ₂] at h₂
  exact (ss_phi_strictAntiOn MF hzb hκ hβ hγ0 hγ1).injOn hθ₁ hθ₂ (h₁.trans h₂.symm)

/-- AKMM, p. 601 (existence, added): if `λ_f` is continuous on `θ > 0`, `λ_f(θ) → 0` as `θ → ∞`,
`β(1 − σ) < 1`, and `jcPhi(θ₁) ≥ 0` at some `θ₁ > 0`, then (20.17) has a solution `θ̄ ≥ θ₁`. -/
theorem ss_exists (MF : MatchFn) {z b σ γ κ β θ₁ : ℝ} (hzb : b < z) (hκ : 0 < κ)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hσ : 0 ≤ σ) (hβ1 : β < 1)
    (hc : ContinuousOn (lamF MF) (Set.Ioi 0)) (hlim : Tendsto (lamF MF) atTop (𝓝 0))
    (hθ₁ : 0 < θ₁) (h₁ : 0 ≤ jcPhi MF z b σ γ κ β θ₁) :
    ∃ θ, θ₁ ≤ θ ∧ jcLHS MF κ γ θ = β * jcRHS MF z b σ γ κ θ := by
  have h1γ : 0 < 1 - γ := by linarith
  -- a point where `jcPhi < 0`
  set ε := (1 - β * (1 - σ)) * κ / (1 - γ) / (2 * β * (z - b) + 1) with hε
  have hεp : 0 < ε := by
    have : 0 < 1 - β * (1 - σ) := by nlinarith
    positivity
  obtain ⟨θ₂, hθ₂⟩ := (eventually_atTop.mp ((hlim.eventually (gt_mem_nhds hεp)).and
    (eventually_gt_atTop θ₁)))
  obtain ⟨hθ₂ε, hθ₂1⟩ := hθ₂ θ₂ le_rfl
  have hθ₂p : 0 < θ₂ := hθ₁.trans hθ₂1
  have hneg : jcPhi MF z b σ γ κ β θ₂ < 0 := by
    have hw := match_lamW_pos MF hθ₂p
    have hf := match_lamF_pos MF hθ₂p
    unfold jcPhi
    have e1 : (1 - σ - γ * lamW MF θ₂) * κ / (1 - γ) ≤ (1 - σ) * κ / (1 - γ) := by
      apply div_le_div_of_nonneg_right _ h1γ.le
      nlinarith [mul_nonneg (mul_nonneg hγ0 hw.le) hκ.le]
    have e2 : (z - b) * lamF MF θ₂ ≤ (z - b) * ε := by nlinarith
    have e3 : β * ((z - b) * ε) < (1 - β * (1 - σ)) * κ / (1 - γ) := by
      rw [hε]
      have hA : 0 < (1 - β * (1 - σ)) * κ / (1 - γ) := by
        have : 0 < 1 - β * (1 - σ) := by nlinarith
        positivity
      rw [show β * ((z - b) * ((1 - β * (1 - σ)) * κ / (1 - γ) / (2 * β * (z - b) + 1))) =
        (1 - β * (1 - σ)) * κ / (1 - γ) * (β * (z - b) / (2 * β * (z - b) + 1)) by ring]
      have : β * (z - b) / (2 * β * (z - b) + 1) < 1 := by
        rw [div_lt_one (by nlinarith)]; nlinarith
      nlinarith
    have e4 : β * ((1 - σ) * κ / (1 - γ)) - κ / (1 - γ) = -((1 - β * (1 - σ)) * κ / (1 - γ)) := by
      ring
    nlinarith
  have hcont : ContinuousOn (jcPhi MF z b σ γ κ β) (Set.Icc θ₁ θ₂) := by
    have hcf : ContinuousOn (lamF MF) (Set.Icc θ₁ θ₂) :=
      hc.mono fun x hx ↦ lt_of_lt_of_le hθ₁ hx.1
    have hcw : ContinuousOn (lamW MF) (Set.Icc θ₁ θ₂) := by
      have : ContinuousOn (fun x ↦ x * lamF MF x) (Set.Icc θ₁ θ₂) := continuousOn_id.mul hcf
      refine this.congr fun x hx ↦ ?_
      exact match_lamW_eq MF (lt_of_lt_of_le hθ₁ hx.1)
    unfold jcPhi
    fun_prop
  obtain ⟨θ, hθ, heq⟩ := isPreconnected_Icc.intermediate_value₂ (Set.left_mem_Icc.mpr hθ₂1.le)
    (Set.right_mem_Icc.mpr hθ₂1.le) continuousOn_const hcont h₁ hneg.le
  exact ⟨θ, hθ.1, (eq_20_17 MF hγ1 (hθ₁.trans_le hθ.1)).mpr heq.symm⟩

/-- AKMM, p. 601 (existence, added): if moreover `λ_f(θ) → ∞` as `θ → 0⁺` (as for Cobb–Douglas
matching), (20.17) has a solution. -/
theorem ss_exists_of_tendsto (MF : MatchFn) {z b σ γ κ β : ℝ} (hzb : b < z) (hκ : 0 < κ)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hβ1 : β < 1)
    (hc : ContinuousOn (lamF MF) (Set.Ioi 0)) (hlim : Tendsto (lamF MF) atTop (𝓝 0))
    (hlim0 : Tendsto (lamF MF) (𝓝[>] 0) atTop) :
    ∃ θ, 0 < θ ∧ jcLHS MF κ γ θ = β * jcRHS MF z b σ γ κ θ := by
  have h1γ : 0 < 1 - γ := by linarith
  set C := (κ / (1 - γ) + β * γ * lamW MF 1 * κ / (1 - γ) + 1) / (β * (z - b)) with hC
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), C ≤ lamF MF θ ∧ θ ∈ Set.Ioo 0 1 :=
    (hlim0.eventually (eventually_ge_atTop C)).and (Ioo_mem_nhdsGT one_pos)
  obtain ⟨θ₁, hθ₁C, hθ₁0, hθ₁1⟩ := hev.exists
  have hphi : 0 ≤ jcPhi MF z b σ γ κ β θ₁ := by
    have hw : lamW MF θ₁ ≤ lamW MF 1 :=
      (match_lamW_strictMonoOn MF (Set.mem_Ioi.mpr hθ₁0) (Set.mem_Ioi.mpr one_pos) hθ₁1).le
    have hw0 := match_lamW_pos MF hθ₁0
    unfold jcPhi
    have hbz : 0 < β * (z - b) := by nlinarith
    have hCf : β * (z - b) * C ≤ β * (z - b) * lamF MF θ₁ :=
      mul_le_mul_of_nonneg_left hθ₁C hbz.le
    rw [hC, mul_div_cancel₀ _ hbz.ne'] at hCf
    have e : β * ((1 - σ - γ * lamW MF θ₁) * κ / (1 - γ)) ≥
        -(β * γ * lamW MF 1 * κ / (1 - γ)) + β * ((1 - σ) * κ / (1 - γ)) := by
      have hg : γ * lamW MF θ₁ ≤ γ * lamW MF 1 := mul_le_mul_of_nonneg_left hw hγ0
      have : β * ((1 - σ - γ * lamW MF θ₁) * κ / (1 - γ)) - β * ((1 - σ) * κ / (1 - γ)) =
          -(β * (γ * lamW MF θ₁) * κ / (1 - γ)) := by ring
      have : β * (γ * lamW MF θ₁) * κ / (1 - γ) ≤ β * γ * lamW MF 1 * κ / (1 - γ) := by
        apply div_le_div_of_nonneg_right _ h1γ.le
        have := mul_le_mul_of_nonneg_left hg hβ.le
        nlinarith
      linarith
    have : 0 ≤ β * ((1 - σ) * κ / (1 - γ)) := by
      have : 0 ≤ 1 - σ := by linarith
      positivity
    nlinarith
  obtain ⟨θ, hθ, h⟩ := ss_exists MF hzb hκ hβ hγ0 hγ1 hσ hβ1 hc hlim hθ₁0 hphi
  exact ⟨θ, hθ₁0.trans_le hθ, h⟩

/-- The Cobb–Douglas `λ_f(θ) = χθ^{−η}` is continuous, tends to `0` as `θ → ∞` and to `∞` as
`θ → 0⁺`. -/
theorem ss_cd_lamF_limits {χ η : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) :
    ContinuousOn (lamF (cdMatch χ η hχ hη0 hη1)) (Set.Ioi 0) ∧
      Tendsto (lamF (cdMatch χ η hχ hη0 hη1)) atTop (𝓝 0) ∧
      Tendsto (lamF (cdMatch χ η hχ hη0 hη1)) (𝓝[>] 0) atTop := by
  have heq : ∀ θ ∈ Set.Ioi (0 : ℝ), χ * θ ^ (-η) = lamF (cdMatch χ η hχ hη0 hη1) θ :=
    fun θ hθ ↦ ((eq_20_23 hχ hη0 hη1 hθ).2).symm
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousOn.congr (f := fun θ ↦ χ * θ ^ (-η)) ?_ fun θ hθ ↦ (heq θ hθ).symm
    exact continuousOn_const.mul (fun θ hθ ↦
      (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hθ))).continuousWithinAt)
  · have h := (tendsto_rpow_neg_atTop hη0).const_mul χ
    rw [mul_zero] at h
    exact h.congr' ((eventually_gt_atTop 0).mono fun θ hθ ↦ heq θ hθ)
  · have h := (tendsto_rpow_neg_nhdsGT_zero (by linarith : -η < 0)).const_mul_atTop hχ
    exact h.congr' (eventually_nhdsWithin_of_forall fun θ hθ ↦ heq θ hθ)

/-- AKMM, (20.17), p. 601, with Cobb–Douglas matching (20.23): for every `z > b` there is exactly
one steady state `θ̄ > 0`. -/
theorem ss_cd_existsUnique {χ η z b σ γ κ β : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∃! θ, 0 < θ ∧ jcLHS (cdMatch χ η hχ hη0 hη1) κ γ θ =
      β * jcRHS (cdMatch χ η hχ hη0 hη1) z b σ γ κ θ := by
  obtain ⟨hc, hlim, hlim0⟩ := ss_cd_lamF_limits hχ hη0 hη1
  obtain ⟨θ, hθ, h⟩ := ss_exists_of_tendsto _ hzb hκ hβ hγ0 hγ1 hσ hσ1 hβ1 hc hlim hlim0
  exact ⟨θ, ⟨hθ, h⟩, fun θ' ⟨hθ', h'⟩ ↦ ss_unique _ hzb hκ hβ hγ0 hγ1 hθ' hθ h' h⟩

/-- AKMM, p. 602 (Figure 20.5): when `z` goes down, `θ̄` goes down: steady states are strictly
increasing in `z`. -/
theorem ss_theta_mono_z (MF : MatchFn) {z₁ z₂ b σ γ κ β θ₁ θ₂ : ℝ} (hz : z₁ < z₂)
    (hzb : b < z₁) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (h₁ : jcLHS MF κ γ θ₁ = β * jcRHS MF z₁ b σ γ κ θ₁)
    (h₂ : jcLHS MF κ γ θ₂ = β * jcRHS MF z₂ b σ γ κ θ₂) : θ₁ < θ₂ := by
  rw [eq_20_17 MF hγ1 hθ₁] at h₁
  rw [eq_20_17 MF hγ1 hθ₂] at h₂
  have hl := match_lamF_pos MF hθ₁
  have hgt : 0 < jcPhi MF z₂ b σ γ κ β θ₁ := by
    have : jcPhi MF z₂ b σ γ κ β θ₁ - jcPhi MF z₁ b σ γ κ β θ₁ = β * (z₂ - z₁) * lamF MF θ₁ := by
      unfold jcPhi; ring
    have : 0 < β * (z₂ - z₁) * lamF MF θ₁ := by have := sub_pos.mpr hz; positivity
    linarith
  by_contra hcon
  rcases (not_lt.mp hcon).lt_or_eq with hlt | heq
  · have := ss_phi_strictAntiOn MF (σ := σ) (hzb.trans hz) hκ hβ hγ0 hγ1 hθ₂ hθ₁ hlt
    linarith
  · rw [heq] at h₂; linarith

/-- AKMM, p. 602 (Figure 20.5): steady-state unemployment `ū = σ/(λ_w(θ̄) + σ)` is strictly
decreasing in `θ̄`. -/
theorem ss_ubar_strictAntiOn (MF : MatchFn) {σ : ℝ} (hσ : 0 < σ) :
    StrictAntiOn (fun θ ↦ σ / (lamW MF θ + σ)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have := match_lamW_strictMonoOn MF hx hy hxy
  have := match_lamW_pos MF hx
  exact div_lt_div_of_pos_left hσ (by linarith) (by linarith)

/-- AKMM, p. 602 (Figure 20.5): steady-state vacancies `v̄ = θ̄ū` are strictly increasing in
`θ̄`; with `ss_theta_mono_z`, a fall in `z` gives smaller `v` and larger `u`. -/
theorem ss_vbar_strictMonoOn (MF : MatchFn) {σ : ℝ} (hσ : 0 < σ) :
    StrictMonoOn (fun θ ↦ θ * (σ / (lamW MF θ + σ))) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have hf := match_lamF_strictAntiOn MF hx hy hxy
  have hfy := match_lamF_pos MF hy0
  have hfx := match_lamF_pos MF hx0
  simp only
  rw [match_lamW_eq MF hx0, match_lamW_eq MF hy0, ← mul_div_assoc, ← mul_div_assoc,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (mul_pos hx0 hy0) (sub_pos.mpr hf), mul_pos hσ (sub_pos.mpr hxy)]

/-- AKMM, footnote 6, p. 602: if `λ_f` has derivative `d` at `θ > 0`, the left side of (20.16)
has derivative `κη/((1 − γ)λ_w(θ))` with `η = −θd/λ_f(θ)`. -/
theorem fn6_lhs_hasDerivAt (MF : MatchFn) {κ γ θ d : ℝ} (hγ1 : γ < 1) (hθ : 0 < θ)
    (hd : HasDerivAt (lamF MF) d θ) :
    HasDerivAt (jcLHS MF κ γ) (κ * (-θ * d / lamF MF θ) / ((1 - γ) * lamW MF θ)) θ := by
  have hl := match_lamF_pos MF hθ
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h := (hasDerivAt_const θ κ).div (hd.const_mul (1 - γ)) (by positivity)
  refine h.congr_deriv ?_
  rw [match_lamW_eq MF hθ]
  field_simp
  ring

/-- AKMM, footnote 6, p. 602: if `λ_f` has derivative `d` at `θ > 0`, the right side of (20.16)
has derivative `κ((1 − σ)η − γλ_w(θ))/((1 − γ)λ_w(θ))` with `η = −θd/λ_f(θ)`. -/
theorem fn6_rhs_hasDerivAt (MF : MatchFn) {z b σ γ κ θ d : ℝ} (hγ1 : γ < 1) (hθ : 0 < θ)
    (hd : HasDerivAt (lamF MF) d θ) :
    HasDerivAt (jcRHS MF z b σ γ κ)
      (κ * ((1 - σ) * (-θ * d / lamF MF θ) - γ * lamW MF θ) / ((1 - γ) * lamW MF θ)) θ := by
  have hl := match_lamF_pos MF hθ
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h1 := ((hd.inv hl.ne').const_mul ((1 - σ) * κ / (1 - γ))).const_add (z - b)
  have h2 := h1.sub ((hasDerivAt_id θ).const_mul (γ * κ / (1 - γ)))
  have heq : (fun x ↦ z - b + (1 - σ) * κ / (1 - γ) * (lamF MF x)⁻¹ - γ * κ / (1 - γ) * id x)
      =ᶠ[𝓝 θ] jcRHS MF z b σ γ κ := by
    filter_upwards [lt_mem_nhds hθ] with x hx
    have hlx := match_lamF_pos MF hx
    rw [jcRHS, match_lamW_eq MF hx]
    simp only [id]
    field_simp
    ring
  refine (h2.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  rw [match_lamW_eq MF hθ]
  field_simp

/-- AKMM, footnote 6, p. 602: where `(1 − σ)η(θ) − γλ_w(θ) > 0` on an interval, the right side
of (20.16) is strictly increasing there. -/
theorem fn6_rhs_strictMonoOn (MF : MatchFn) {z b σ γ κ a c : ℝ} (hκ : 0 < κ) (hγ1 : γ < 1)
    (ha : 0 ≤ a) {d : ℝ → ℝ} (hd : ∀ θ ∈ Set.Ioo a c, HasDerivAt (lamF MF) (d θ) θ)
    (hcond : ∀ θ ∈ Set.Ioo a c, 0 < (1 - σ) * (-θ * d θ / lamF MF θ) - γ * lamW MF θ) :
    StrictMonoOn (jcRHS MF z b σ γ κ) (Set.Ioo a c) := by
  have hpos : ∀ θ ∈ Set.Ioo a c, 0 < θ := fun θ hθ ↦ lt_of_le_of_lt ha hθ.1
  have hder : ∀ θ ∈ Set.Ioo a c, HasDerivAt (jcRHS MF z b σ γ κ)
      (κ * ((1 - σ) * (-θ * d θ / lamF MF θ) - γ * lamW MF θ) / ((1 - γ) * lamW MF θ)) θ :=
    fun θ hθ ↦ fn6_rhs_hasDerivAt MF hγ1 (hpos θ hθ) (hd θ hθ)
  refine strictMonoOn_of_deriv_pos (convex_Ioo a c)
    (fun θ hθ ↦ (hder θ hθ).continuousAt.continuousWithinAt) fun θ hθ ↦ ?_
  rw [interior_Ioo] at hθ
  rw [(hder θ hθ).deriv]
  have := match_lamW_pos MF (hpos θ hθ)
  have := hcond θ hθ
  have : 0 < 1 - γ := by linarith
  positivity

/-- AKMM, p. 601: the left side of (20.16) is strictly increasing in `θ_t`. -/
theorem ss_lhs_strictMonoOn (MF : MatchFn) {κ γ : ℝ} (hκ : 0 < κ) (hγ1 : γ < 1) :
    StrictMonoOn (jcLHS MF κ γ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hf := match_lamF_strictAntiOn MF hx hy hxy
  have := match_lamF_pos MF hy
  have : 0 < 1 - γ := by linarith
  unfold jcLHS
  exact div_lt_div_of_pos_left hκ (by positivity) (by nlinarith)

/-- AKMM, footnote 7, p. 602: where the right side of (20.16) is increasing (footnote 6),
`θ_{t+1}` is an increasing function of `θ_t`. -/
theorem fn6_next_strictMono (MF : MatchFn) {z b σ γ κ β : ℝ} {I : Set ℝ} (hκ : 0 < κ)
    (hγ1 : γ < 1) (hβ : 0 < β) (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I)
    {θ θ' φ φ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') (hφ : φ ∈ I) (hφ' : φ' ∈ I)
    (h : jcLHS MF κ γ θ = β * jcRHS MF z b σ γ κ φ)
    (h' : jcLHS MF κ γ θ' = β * jcRHS MF z b σ γ κ φ') (hlt : θ < θ') : φ < φ' := by
  have := ss_lhs_strictMonoOn MF hκ hγ1 hθ hθ' hlt
  rw [h, h'] at this
  exact (hmono.lt_iff_lt hφ hφ').mp (lt_of_mul_lt_mul_left this hβ.le)

/-- AKMM, footnote 7, p. 602: if the transition `θ_t ↦ θ_{t+1} = φ(θ_t)` is differentiable at the
steady state, its slope is `L/(βR)`, `L` and `R` the derivatives of the two sides of (20.16). -/
theorem fn7_slope (MF : MatchFn) {z b σ γ κ β θ L R φ' : ℝ} {φ : ℝ → ℝ} (hβ : β ≠ 0)
    (hR : R ≠ 0) (hφ : HasDerivAt φ φ' θ) (hfix : φ θ = θ)
    (hL : HasDerivAt (jcLHS MF κ γ) L θ) (hRd : HasDerivAt (jcRHS MF z b σ γ κ) R θ)
    (hpath : ∀ᶠ x in 𝓝 θ, jcLHS MF κ γ x = β * jcRHS MF z b σ γ κ (φ x)) :
    φ' = L / (β * R) := by
  have hR' : HasDerivAt (jcRHS MF z b σ γ κ) R (φ θ) := by rwa [hfix]
  have h := (hR'.comp θ hφ).const_mul β
  have h2 := hL.congr_of_eventuallyEq (hpath.mono fun x hx ↦ hx.symm)
  have := h2.unique h
  rw [eq_div_iff (mul_ne_zero hβ hR), this]
  ring

/-- AKMM, footnote 7, p. 602: at the steady state, `dθ_{t+1}/dθ_t = η/(β((1 − σ)η − γλ_w)) > 1`
when `(1 − σ)η − γλ_w > 0` (footnote 6), `β ∈ (0, 1)`, `σ ≥ 0` and `γλ_w ≥ 0`. -/
theorem fn7_slope_gt_one {η σ γ lw β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    (hγ : 0 ≤ γ * lw) (hη : 0 < η) (hcond : 0 < (1 - σ) * η - γ * lw) :
    1 < η / (β * ((1 - σ) * η - γ * lw)) := by
  rw [one_lt_div (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right hβ1 hcond, mul_nonneg hσ hη.le]

/-- AKMM, footnote 7, p. 602, the steady-state slope as a quotient of the derivatives of
footnote 6: `(κη/((1 − γ)λ_w))/(β · κ((1 − σ)η − γλ_w)/((1 − γ)λ_w)) =
η/(β((1 − σ)η − γλ_w))`. -/
theorem fn7_slope_eq {κ η σ γ lw β : ℝ} (hκ : 0 < κ) (hγ1 : γ < 1) (hlw : 0 < lw)
    (hβ : 0 < β) :
    κ * η / ((1 - γ) * lw) / (β * (κ * ((1 - σ) * η - γ * lw) / ((1 - γ) * lw))) =
      η / (β * ((1 - σ) * η - γ * lw)) := by
  have : (1 - γ) ≠ 0 := by linarith
  field_simp

/-- One step of the divergence of footnote 7: above the steady state, `θ_{t+1} > θ_t`. -/
theorem fn7_step_above (MF : MatchFn) {z b σ γ κ β θbar : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Ioi 0)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I) (hbar : 0 < θbar)
    (hss : jcLHS MF κ γ θbar = β * jcRHS MF z b σ γ κ θbar) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I)
    (hpath : jcLHS MF κ γ x = β * jcRHS MF z b σ γ κ y) (hxb : θbar < x) : x < y := by
  have hx0 : 0 < x := hI hx
  have hphi := ss_phi_strictAntiOn MF (σ := σ) hzb hκ hβ hγ0 hγ1 (Set.mem_Ioi.mpr hbar)
    (Set.mem_Ioi.mpr hx0) hxb
  rw [(eq_20_17 MF hγ1 hbar).mp hss, ← ss_phi_eq MF hγ1 hx0] at hphi
  have hl := match_lamF_pos MF hx0
  have h1 : β * jcRHS MF z b σ γ κ x < β * jcRHS MF z b σ γ κ y := by
    rw [← hpath]; nlinarith
  exact (hmono.lt_iff_lt hx hy).mp (lt_of_mul_lt_mul_left h1 hβ.le)

/-- One step of the divergence of footnote 7: below the steady state, `θ_{t+1} < θ_t`. -/
theorem fn7_step_below (MF : MatchFn) {z b σ γ κ β θbar : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Ioi 0)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I) (hbar : 0 < θbar)
    (hss : jcLHS MF κ γ θbar = β * jcRHS MF z b σ γ κ θbar) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I)
    (hpath : jcLHS MF κ γ x = β * jcRHS MF z b σ γ κ y) (hxb : x < θbar) : y < x := by
  have hx0 : 0 < x := hI hx
  have hphi := ss_phi_strictAntiOn MF (σ := σ) hzb hκ hβ hγ0 hγ1 (Set.mem_Ioi.mpr hx0)
    (Set.mem_Ioi.mpr hbar) hxb
  rw [(eq_20_17 MF hγ1 hbar).mp hss, ← ss_phi_eq MF hγ1 hx0] at hphi
  have hl := match_lamF_pos MF hx0
  have h1 : β * jcRHS MF z b σ γ κ y < β * jcRHS MF z b σ γ κ x := by
    rw [← hpath]; nlinarith
  exact (hmono.lt_iff_lt hy hx).mp (lt_of_mul_lt_mul_left h1 hβ.le)

/-- AKMM, footnote 7, p. 602: a path of (20.16) staying in a set `I` where the right side is
increasing, and starting above `θ̄`, increases strictly and stays above `θ̄`. -/
theorem fn7_diverge_above (MF : MatchFn) {z b σ γ κ β θbar : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Ioi 0)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I) (hbar : 0 < θbar)
    (hss : jcLHS MF κ γ θbar = β * jcRHS MF z b σ γ κ θbar) {θ : ℕ → ℝ} (hθI : ∀ t, θ t ∈ I)
    (hpath : ∀ t, jcLHS MF κ γ (θ t) = β * jcRHS MF z b σ γ κ (θ (t + 1)))
    (h0 : θbar < θ 0) : StrictMono θ ∧ ∀ t, θbar < θ t := by
  have hall : ∀ t, θbar < θ t := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih => exact ih.trans (fn7_step_above MF hI hzb hκ hβ hγ0 hγ1 hmono hbar hss
        (hθI n) (hθI (n + 1)) (hpath n) ih)
  exact ⟨strictMono_nat_of_lt_succ fun n ↦ fn7_step_above MF hI hzb hκ hβ hγ0 hγ1 hmono hbar
    hss (hθI n) (hθI (n + 1)) (hpath n) (hall n), hall⟩

/-- AKMM, footnote 7, p. 602: a path starting below `θ̄` decreases strictly and stays below. -/
theorem fn7_diverge_below (MF : MatchFn) {z b σ γ κ β θbar : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Ioi 0)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I) (hbar : 0 < θbar)
    (hss : jcLHS MF κ γ θbar = β * jcRHS MF z b σ γ κ θbar) {θ : ℕ → ℝ} (hθI : ∀ t, θ t ∈ I)
    (hpath : ∀ t, jcLHS MF κ γ (θ t) = β * jcRHS MF z b σ γ κ (θ (t + 1)))
    (h0 : θ 0 < θbar) : StrictAnti θ ∧ ∀ t, θ t < θbar := by
  have hall : ∀ t, θ t < θbar := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih => exact (fn7_step_below MF hI hzb hκ hβ hγ0 hγ1 hmono hbar hss
        (hθI n) (hθI (n + 1)) (hpath n) ih).trans ih
  exact ⟨strictAnti_nat_of_succ_lt fun n ↦ fn7_step_below MF hI hzb hκ hβ hγ0 hγ1 hmono hbar
    hss (hθI n) (hθI (n + 1)) (hpath n) (hall n), hall⟩

/-- AKMM, p. 602 and footnote 7: the only path of (20.16) in `I` converging to `θ̄` is the
constant path; so after a permanent change in `z`, `θ` must jump at once to the new `θ̄`. -/
theorem fn7_jump (MF : MatchFn) {z b σ γ κ β θbar : ℝ} {I : Set ℝ} (hI : I ⊆ Set.Ioi 0)
    (hzb : b < z) (hκ : 0 < κ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hmono : StrictMonoOn (jcRHS MF z b σ γ κ) I) (hbar : 0 < θbar)
    (hss : jcLHS MF κ γ θbar = β * jcRHS MF z b σ γ κ θbar) {θ : ℕ → ℝ} (hθI : ∀ t, θ t ∈ I)
    (hpath : ∀ t, jcLHS MF κ γ (θ t) = β * jcRHS MF z b σ γ κ (θ (t + 1)))
    (hlim : Tendsto θ atTop (𝓝 θbar)) (t : ℕ) : θ t = θbar := by
  -- the shifted path has the same properties; show its first term is `θ̄`
  have key : ∀ s : ℕ → ℝ, (∀ t, s t ∈ I) →
      (∀ t, jcLHS MF κ γ (s t) = β * jcRHS MF z b σ γ κ (s (t + 1))) →
      Tendsto s atTop (𝓝 θbar) → s 0 = θbar := by
    intro s hsI hs hslim
    rcases lt_trichotomy (s 0) θbar with h | h | h
    · obtain ⟨hanti, -⟩ := fn7_diverge_below MF hI hzb hκ hβ hγ0 hγ1 hmono hbar hss hsI hs h
      have : θbar ≤ s 0 := le_of_tendsto hslim (Eventually.of_forall fun n ↦ hanti.antitone
        (Nat.zero_le n))
      linarith
    · exact h
    · obtain ⟨hmon, -⟩ := fn7_diverge_above MF hI hzb hκ hβ hγ0 hγ1 hmono hbar hss hsI hs h
      have : s 0 ≤ θbar := ge_of_tendsto hslim (Eventually.of_forall fun n ↦ hmon.monotone
        (Nat.zero_le n))
      linarith
  have := key (fun n ↦ θ (n + t)) (fun n ↦ hθI _) (fun n ↦ by
    simpa [add_right_comm] using hpath (n + t)) ((tendsto_add_atTop_iff_nat t).mpr hlim)
  simpa using this

end AKMM.FrictionalLaborMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Efficiency and the Hosios condition

AKMM, §20.4.3, pp. 603–605, and Appendix 20.A.3, pp. 880–881. The constrained planner maximises
`E₀ Σ βᵗ(z_t(1 − u_t) + bu_t − κθ_tu_t)` subject to `1 − u_{t+1} = (1 − σ)(1 − u_t) +
M(u_t, θ_tu_t)`. Uncertainty is an event tree on a finite set of nodes `N` with transition weights
`P n n'` (`dmpEx`); at node `n`, `M₁ n`, `M₂ n` are the partial derivatives of `M` at
`(u_n, v_n)`, `v_n = θ_nu_n`.

* `eq_20_A_1`'s planner analogue `planner_foc_theta`: the derivative of the Lagrangian in `θ_t`
  vanishes iff `κ = βμ_tM₂` (20.A.1).
* `planner_foc_u`: the derivative of the Lagrangian in `u_{t+1}` vanishes iff
  `μ_t = E_t[z_{t+1} − b + κθ_{t+1} + βμ_{t+1}(1 − σ − M₁ − θ_{t+1}M₂)]` (20.A.2 corrected:
  there is no leading `β`); `eq_20_A_3`: with (20.A.1) at `t + 1`,
  `μ_t = E_t[z_{t+1} − b + βμ_{t+1}(1 − σ − M₁)]`. `eq_20_A_2_misprint`: the printed
  `μ_t = βE_t[⋯]` is incompatible with the corrected condition when `κ > 0`, `β < 1`.
* `eq_20_20`, `eq_20_22`: the static efficiency conditions are `η(u, v) = γ` and
  `M₁u/M = γ`; `hosios_node`: under Euler's theorem (constant returns) the two conditions
  (20.A.4) `M₂ = (1 − γ)λ_f(θ)` and (20.A.5) `M₁ = γλ_w(θ)` both hold iff `η(u, v) = γ`.
* `hosios`: **the Hosios condition** (20.A.3, p. 881): under constant returns, if
  `η(u_n, v_n) = γ` at every node, then `(θ, μ)` solves the planner's first-order conditions
  (20.A.1), (20.A.3) iff `(θ, S = μ)` solves the equilibrium system (20.18), (20.19);
  `hosios_necessary`: conversely the coincidence of (20.A.1) and (20.18) with `S > 0` forces
  (20.A.4).
* `hosios_cd`: with Cobb–Douglas `M = u^ηv^{1−η}` (p. 605), `η(u, v) = η`, and (20.20), (20.22)
  hold iff `η = γ`; `hosios_nonCRS`: for `M = u^av^c`, `η(u, v) = γ` gives (20.A.4) but
  (20.A.5) holds iff `a + c = 1`; `hosios_nonCRS_example`: `a = 1/2`, `c = 1/4`.

Departure: as in the book, efficiency is established at the level of first-order conditions
(the planner's problem is not convex, so sufficiency of the first-order conditions is not
claimed).
-/

namespace AKMM.FrictionalLaborMarkets

variable {N : Type*} [Fintype N]

/-- AKMM, (20.A.1), p. 880: the terms of the Lagrangian containing `θ_t` (divided by `βᵗ`) are
`−κθu_t + βμ_tM(u_t, θu_t)`; if `y ↦ M(u_t, y)` has derivative `M₂` at `θu_t`, the derivative in
`θ` vanishes iff `κ = βμ_tM₂`. -/
theorem planner_foc_theta {M : ℝ → ℝ → ℝ} {κ β μ u θ M₂ : ℝ} (hu : 0 < u)
    (hM : HasDerivAt (fun y ↦ M u y) M₂ (θ * u)) :
    HasDerivAt (fun x ↦ -κ * x * u + β * μ * M u (x * u)) (-κ * u + β * μ * M₂ * u) θ ∧
      (-κ * u + β * μ * M₂ * u = 0 ↔ κ = β * μ * M₂) := by
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun x ↦ -κ * x * u) (-κ * u) θ := by
      simpa using ((hasDerivAt_id θ).const_mul (-κ)).mul_const u
    have h2 : HasDerivAt (fun x ↦ M u (x * u)) (M₂ * u) θ := by
      have := hM.comp θ (by simpa using (hasDerivAt_id θ).mul_const u :
        HasDerivAt (fun x : ℝ ↦ x * u) u θ)
      simpa [Function.comp_def] using this
    have := h1.add (h2.const_mul (β * μ))
    refine this.congr_deriv ?_
    ring
  · constructor
    · intro h
      have : (β * μ * M₂ - κ) * u = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    · intro h; rw [h]; ring

/-- AKMM, (20.A.2), p. 881, corrected: the terms of the Lagrangian containing `u_{t+1} = x`
(divided by `βᵗ`) are `βμ_tx + βE_t[z′(1 − x) + bx − κθ′x + βμ′((1 − σ)(1 − x) + M(x, θ′x))]`.
If `x ↦ M(x, θ_{n'}x)` has derivative `M₁ n' + θ_{n'}M₂ n'` at `u`, the derivative vanishes iff
`μ_t = E_t[z′ − b + κθ′ + βμ′(1 − σ − M₁ − θ′M₂)]`. -/
theorem planner_foc_u (P : N → N → ℝ) {M : ℝ → ℝ → ℝ} {κ β σ b u μ₀ : ℝ} (hβ : 0 < β)
    {z θ μ M₁ M₂ : N → ℝ} (n : N)
    (hM : ∀ n', HasDerivAt (fun x ↦ M x (θ n' * x)) (M₁ n' + θ n' * M₂ n') u) :
    HasDerivAt (fun x ↦ β * μ₀ * x + β * dmpEx P (fun n' ↦ z n' * (1 - x) + b * x -
        κ * θ n' * x + β * μ n' * ((1 - σ) * (1 - x) + M x (θ n' * x))) n)
      (β * μ₀ - β * dmpEx P (fun n' ↦ z n' - b + κ * θ n' +
        β * μ n' * (1 - σ - M₁ n' - θ n' * M₂ n')) n) u ∧
    (β * μ₀ - β * dmpEx P (fun n' ↦ z n' - b + κ * θ n' +
        β * μ n' * (1 - σ - M₁ n' - θ n' * M₂ n')) n = 0 ↔
      μ₀ = dmpEx P (fun n' ↦ z n' - b + κ * θ n' +
        β * μ n' * (1 - σ - M₁ n' - θ n' * M₂ n')) n) := by
  refine ⟨?_, ?_⟩
  · have hterm : ∀ n', HasDerivAt (fun x ↦ z n' * (1 - x) + b * x - κ * θ n' * x +
        β * μ n' * ((1 - σ) * (1 - x) + M x (θ n' * x)))
        (-(z n' - b + κ * θ n' + β * μ n' * (1 - σ - M₁ n' - θ n' * M₂ n'))) u := by
      intro n'
      have h1 : HasDerivAt (fun x : ℝ ↦ z n' * (1 - x) + b * x - κ * θ n' * x)
          (z n' * (0 - 1) + b * 1 - κ * θ n' * 1) u :=
        ((((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id' u)).const_mul (z n')).add
          ((hasDerivAt_id' u).const_mul b)).sub ((hasDerivAt_id' u).const_mul (κ * θ n'))
      have h2 : HasDerivAt (fun x : ℝ ↦ (1 - σ) * (1 - x) + M x (θ n' * x))
          ((1 - σ) * (0 - 1) + (M₁ n' + θ n' * M₂ n')) u :=
        (((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id' u)).const_mul (1 - σ)).add (hM n')
      have := h1.add (h2.const_mul (β * μ n'))
      refine this.congr_deriv ?_
      ring
    have hsum : HasDerivAt (fun x ↦ dmpEx P (fun n' ↦ z n' * (1 - x) + b * x -
        κ * θ n' * x + β * μ n' * ((1 - σ) * (1 - x) + M x (θ n' * x))) n)
        (dmpEx P (fun n' ↦ -(z n' - b + κ * θ n' +
          β * μ n' * (1 - σ - M₁ n' - θ n' * M₂ n'))) n) u := by
      unfold dmpEx
      exact HasDerivAt.fun_sum fun n' _ ↦ (hterm n').const_mul (P n n')
    have := ((hasDerivAt_id u).const_mul (β * μ₀)).add (hsum.const_mul β)
    refine this.congr_deriv ?_
    have e := dmp_ex_mul P (-1) (fun n' ↦ z n' - b + κ * θ n' +
      β * μ n' * (1 - σ - M₁ n' - θ n' * M₂ n')) n
    simp only [neg_one_mul] at e
    rw [e]; ring
  · constructor
    · intro h
      have : β * (μ₀ - dmpEx P (fun n' ↦ z n' - b + κ * θ n' +
          β * μ n' * (1 - σ - M₁ n' - θ n' * M₂ n')) n) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    · intro h; rw [← h]; ring

/-- AKMM, (20.A.3), p. 881: using (20.A.1) at `t + 1`, the corrected (20.A.2) becomes
`μ_t = E_t[z_{t+1} − b + βμ_{t+1}(1 − σ − M₁)]`. -/
theorem eq_20_A_3 (P : N → N → ℝ) {κ β σ b : ℝ} {z θ μ M₁ M₂ : N → ℝ}
    (h1 : ∀ n, κ = β * μ n * M₂ n) (n : N) :
    dmpEx P (fun n' ↦ z n' - b + κ * θ n' + β * μ n' * (1 - σ - M₁ n' - θ n' * M₂ n')) n =
      dmpEx P (fun n' ↦ z n' - b + β * μ n' * (1 - σ - M₁ n')) n := by
  refine dmp_ex_congr P (fun n' ↦ ?_) n
  rw [h1 n']; ring

/-- AKMM, (20.A.2)–(20.A.3), p. 881, as printed (`μ_t = βE_t[⋯]`): together with the correct
stationarity condition `μ_t = E_t[⋯]` (`planner_foc_u`) it forces `μ_t = 0`, contradicting
(20.A.1) when `κ > 0` and `β < 1`. -/
theorem eq_20_A_2_misprint {κ β μ₀ M₂ e : ℝ} (hκ : 0 < κ) (hβ1 : β < 1)
    (hcorrect : μ₀ = e) (hprinted : μ₀ = β * e) (hA1 : κ = β * μ₀ * M₂) : False := by
  have : μ₀ = 0 := by
    have : (1 - β) * μ₀ = 0 := by linear_combination hprinted - β * hcorrect
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  rw [this] at hA1
  linarith

/-- AKMM, (20.20)–(20.21), p. 604: the static efficiency condition `M₂ = (M/v)(1 − γ)` is
`η(u, v) = γ`. -/
theorem eq_20_20 (MF : MatchFn) {u v γ M₂ : ℝ} (hu : 0 < u) (hv : 0 < v) :
    M₂ = MF.M u v / v * (1 - γ) ↔ matchElast MF M₂ u v = γ := by
  have hM := MF.pos u v hu hv
  rw [matchElast]
  constructor
  · intro h; rw [h]; field_simp; ring
  · intro h; field_simp at h ⊢; linarith

/-- AKMM, (20.22), p. 605: the efficiency condition for the opportunity cost of search,
`M₁(u, v)u/M(u, v) = γ` (printed with `u_t` for `u_{t+1}`), is `M₁ = γλ_w`, `λ_w = M/u`. -/
theorem eq_20_22 (MF : MatchFn) {u v γ M₁ : ℝ} (hu : 0 < u) (hv : 0 < v) :
    M₁ * u / MF.M u v = γ ↔ M₁ = γ * lamW MF (v / u) := by
  have hM := MF.pos u v hu hv
  rw [← match_rate_worker MF hu hv, div_eq_iff hM.ne']
  constructor <;> intro h
  · field_simp; linarith
  · rw [h]; field_simp

/-- AKMM, 20.A.3, p. 881: with Euler's theorem `M = M₁u + M₂v` (constant returns), (20.A.4)
`M₂ = (1 − γ)λ_f(θ)` and (20.A.5) `M₁ = γλ_w(θ)` both hold iff `η(u, v) = γ`. -/
theorem hosios_node (MF : MatchFn) {u v γ M₁ M₂ : ℝ} (hu : 0 < u) (hv : 0 < v)
    (heuler : MF.M u v = M₁ * u + M₂ * v) :
    (M₂ = (1 - γ) * lamF MF (v / u) ∧ M₁ = γ * lamW MF (v / u)) ↔
      matchElast MF M₂ u v = γ := by
  have hM := MF.pos u v hu hv
  rw [← match_rate_firm MF hu hv, ← match_rate_worker MF hu hv, matchElast]
  constructor
  · rintro ⟨h2, -⟩
    rw [h2]; field_simp; ring
  · intro h
    have h2 : M₂ * v = (1 - γ) * MF.M u v := by field_simp at h; linarith
    refine ⟨?_, ?_⟩
    · field_simp; linarith
    · field_simp; nlinarith

/-- **The Hosios condition** (AKMM, 20.A.3, p. 881). Under constant returns (Euler's theorem at
every node), if `η(u_n, v_n) = γ` at every node, then `(θ, μ)` satisfies the planner's
first-order conditions (20.A.1) and (20.A.3) iff `(θ, S = μ)` satisfies the equilibrium
conditions (20.18) and (20.19). -/
theorem hosios (MF : MatchFn) (P : N → N → ℝ) {κ β σ γ b : ℝ} {z u θ μ M₁ M₂ : N → ℝ}
    (hu : ∀ n, 0 < u n) (hθ : ∀ n, 0 < θ n)
    (heuler : ∀ n, MF.M (u n) (θ n * u n) = M₁ n * u n + M₂ n * (θ n * u n))
    (hη : ∀ n, matchElast MF (M₂ n) (u n) (θ n * u n) = γ) :
    ((∀ n, κ = β * μ n * M₂ n) ∧
      ∀ n, μ n = dmpEx P (fun n' ↦ z n' - b + β * μ n' * (1 - σ - M₁ n')) n) ↔
    ((∀ n, κ = lamF MF (θ n) * (1 - γ) * β * μ n) ∧
      ∀ n, μ n = dmpEx P (fun n' ↦ z n' - b + β * μ n' * (1 - σ - γ * lamW MF (θ n'))) n) := by
  have hnode : ∀ n, M₂ n = (1 - γ) * lamF MF (θ n) ∧ M₁ n = γ * lamW MF (θ n) := by
    intro n
    have hv : 0 < θ n * u n := mul_pos (hθ n) (hu n)
    have := (hosios_node MF (hu n) hv (heuler n)).mpr (hη n)
    rwa [mul_div_cancel_right₀ _ (hu n).ne'] at this
  have e1 : ∀ n, β * μ n * M₂ n = lamF MF (θ n) * (1 - γ) * β * μ n := by
    intro n; rw [(hnode n).1]; ring
  have e2 : ∀ n, dmpEx P (fun n' ↦ z n' - b + β * μ n' * (1 - σ - M₁ n')) n =
      dmpEx P (fun n' ↦ z n' - b + β * μ n' * (1 - σ - γ * lamW MF (θ n'))) n := by
    intro n
    exact dmp_ex_congr P (fun n' ↦ by rw [(hnode n').2]) n
  simp only [e1, e2]

/-- AKMM, 20.A.3, p. 881 ("only if" for (20.A.4)): if (20.A.1) and (20.18) both hold at a node
with `S = μ > 0` and `β > 0`, then `M₂ = (1 − γ)λ_f(θ)`. -/
theorem hosios_necessary (MF : MatchFn) {κ β γ μ θ M₂ : ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (h1 : κ = β * μ * M₂) (h18 : κ = lamF MF θ * (1 - γ) * β * μ) :
    M₂ = (1 - γ) * lamF MF θ := by
  have : β * μ * (M₂ - (1 - γ) * lamF MF θ) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (by positivity)
  · linarith

/-- The Cobb–Douglas matching function `u^ηv^{1−η}` with its partial derivatives
`M₁ = ηu^{η−1}v^{1−η}`, `M₂ = (1 − η)u^ηv^{−η}` (AKMM, p. 605). -/
theorem hosios_cd_partials {η u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (fun x ↦ x ^ η * v ^ (1 - η)) (η * u ^ (η - 1) * v ^ (1 - η)) u ∧
      HasDerivAt (fun y ↦ u ^ η * y ^ (1 - η)) (u ^ η * ((1 - η) * v ^ (1 - η - 1))) v := by
  refine ⟨?_, ?_⟩
  · exact (Real.hasDerivAt_rpow_const (Or.inl hu.ne')).mul_const _
  · exact (Real.hasDerivAt_rpow_const (Or.inl hv.ne')).const_mul _

/-- AKMM, p. 605: with Cobb–Douglas matching `M = u^ηv^{1−η}`, the elasticity (20.21) is `η`
and the conditions (20.20) `M₂ = (M/v)(1 − γ)` and (20.22) `M₁u/M = γ` both hold iff `η = γ`. -/
theorem hosios_cd {η γ u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    1 - u ^ η * ((1 - η) * v ^ (1 - η - 1)) * v / (u ^ η * v ^ (1 - η)) = η ∧
    ((u ^ η * ((1 - η) * v ^ (1 - η - 1)) = u ^ η * v ^ (1 - η) / v * (1 - γ) ∧
      η * u ^ (η - 1) * v ^ (1 - η) * u / (u ^ η * v ^ (1 - η)) = γ) ↔ η = γ) := by
  have hv1 : v ^ (1 - η - 1) = v ^ (1 - η) / v := Real.rpow_sub_one hv.ne' _
  have hu1 : u ^ (η - 1) = u ^ η / u := Real.rpow_sub_one hu.ne' _
  have pu : 0 < u ^ η := Real.rpow_pos_of_pos hu _
  have pv : 0 < v ^ (1 - η) := Real.rpow_pos_of_pos hv _
  rw [hv1, hu1]
  refine ⟨by field_simp; ring, ?_⟩
  constructor
  · rintro ⟨-, h⟩
    field_simp at h; linarith
  · intro h; subst h
    constructor <;> field_simp

/-- AKMM, 20.A.3, p. 881 (non-constant returns): for `M = u^av^c` with `a, c > 0`, the
elasticity is `η(u, v) = 1 − c`; setting `γ = η(u, v)` gives (20.A.4) `M₂ = (1 − γ)M/v`, but
(20.A.5) `M₁ = γM/u` holds iff `a + c = 1`. -/
theorem hosios_nonCRS {a c u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    1 - u ^ a * (c * v ^ (c - 1)) * v / (u ^ a * v ^ c) = 1 - c ∧
    u ^ a * (c * v ^ (c - 1)) = (1 - (1 - c)) * (u ^ a * v ^ c / v) ∧
    (a * u ^ (a - 1) * v ^ c = (1 - c) * (u ^ a * v ^ c / u) ↔ a + c = 1) := by
  have hv1 : v ^ (c - 1) = v ^ c / v := Real.rpow_sub_one hv.ne' _
  have hu1 : u ^ (a - 1) = u ^ a / u := Real.rpow_sub_one hu.ne' _
  have pu : 0 < u ^ a := Real.rpow_pos_of_pos hu _
  have pv : 0 < v ^ c := Real.rpow_pos_of_pos hv _
  rw [hv1, hu1]
  refine ⟨by field_simp, by field_simp; ring, ?_⟩
  constructor
  · intro h
    have : (a - (1 - c)) * (u ^ a * v ^ c / u) = 0 := by rw [sub_mul, ← h]; ring
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h (by positivity)
  · intro h
    rw [show 1 - c = a by linarith]; ring

/-- AKMM, 20.A.3, p. 881: an explicit failure of the Hosios condition without constant returns.
For `M = u^{1/2}v^{1/4}` at `(u, v) = (1, 1)`: `M = 1`, `M₁ = 1/2`, `M₂ = 1/4`, `η = 3/4`; with
`γ = η = 3/4`, (20.A.4) `M₂ = (1 − γ)M/v` holds and (20.A.5) `M₁ = γM/u` fails. -/
theorem hosios_nonCRS_example :
    HasDerivAt (fun x : ℝ ↦ x ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (1 / 4 : ℝ)) (1 / 2) 1 ∧
    HasDerivAt (fun y : ℝ ↦ (1 : ℝ) ^ (1 / 2 : ℝ) * y ^ (1 / 4 : ℝ)) (1 / 4) 1 ∧
    (1 : ℝ) - 1 / 4 * 1 / 1 = 3 / 4 ∧ (1 / 4 : ℝ) = (1 - 3 / 4) * (1 / 1) ∧
    (1 / 2 : ℝ) ≠ 3 / 4 * (1 / 1) := by
  refine ⟨?_, ?_, by norm_num, by norm_num, by norm_num⟩
  · have := (Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (x := 1) (Or.inl one_ne_zero)).mul_const
      ((1 : ℝ) ^ (1 / 4 : ℝ))
    simpa using this
  · have := (Real.hasDerivAt_rpow_const (p := (1 / 4 : ℝ)) (x := 1) (Or.inl one_ne_zero)).const_mul
      ((1 : ℝ) ^ (1 / 2 : ℝ))
    simpa using this

end AKMM.FrictionalLaborMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The log-linearised solution and rigid wages

AKMM, §20.6.1, pp. 607–608, §20.6.4, p. 611, and 20.A.4, pp. 881–882. With Cobb–Douglas
matching (20.23), `θ_t = θ̄e^{θ̂_t}`, `z_t = z̄e^{ẑ_t}`, the job-creation equation (20.16) reads
`llL(θ̂_t) = E[llR(ẑ_{t+1}, θ̂_{t+1})]` (`ll_lhs_eq`, `ll_rhs_eq`), and its log-linearisation is
`Aθ̂_t = E[z̄ẑ_{t+1} + Bθ̂_{t+1}]` (20.25). The coefficients are stated as exact derivatives at the
steady state.

* `eq_20_25`: `A = κθ̄^ηη/((1 − γ)βχ)`, `∂llR/∂ẑ = z̄` and
  `B = (1 − σ)κθ̄^ηη/((1 − γ)χ) − γκθ̄/(1 − γ)`; the printed `+γκθ̄/(1 − γ)` is wrong
  (`eq_20_25_misprint`).
* `ll_undetermined`: the guess `θ̂ = Cẑ` with `E[ẑ_{t+1}] = ρẑ_t` solves (20.25) iff
  `C = ρz̄/(A − ρB)`; `eq_20_26`: with `z̄ = 1` this is
  `(1 − γ)[κθ̄^ηη/χ(1/(ρβ) − (1 − σ)) + κγθ̄]^{−1}`; the printed `B` would give `−κγθ̄`
  (`eq_20_26_printed_B`).
* Comparative statics of the coefficient `llCoeff` (p. 608), for given `θ̄`: it is larger for a
  smaller `κ`, `γ` or `σ` and a larger `χ`, `ρ` or `β` (`ll_cs_kappa` … `ll_cs_sigma`); for a
  smaller `η` only when `θ̄^ηη` increases in `η`, e.g. `θ̄ ≥ 1` (`ll_cs_eta`); with `θ̄ = e^{−4}`
  it fails (`ll_cs_eta_counterexample`).
* `eq_20_A_4_example`: the worked example of 20.A.4 (capital accumulation) as derivatives.
* Rigid wages (§20.6.4): `eq_20_27_deriv`, `eq_20_27`: `θ̂ = [κθ̄^ηη/χ(1/(ρβ) − (1 − σ))]^{−1}ẑ`,
  and `ll_rigid_gt`: the rigid-wage coefficient exceeds the Nash coefficient for `γ ∈ (0, 1)`.

Departures: the book writes `E[z_{t+1}] = ρz_t` for `E[ẑ_{t+1}] = ρẑ_t`; the comparative statics
in `η` need `θ̄^ηη` increasing in `η` (true at the calibrated `θ̄ = 1`).
-/

namespace AKMM.FrictionalLaborMarkets

open Real

/-- `(θ̄e^x)^η = θ̄^η e^{ηx}`. -/
theorem ll_rpow_exp {θb η : ℝ} (hθ : 0 < θb) (x : ℝ) :
    (θb * exp x) ^ η = θb ^ η * exp (η * x) := by
  rw [Real.mul_rpow hθ.le (exp_pos x).le, ← Real.exp_mul, mul_comm x η]

/-- The left side of (20.16) divided by `β`, with Cobb–Douglas matching, in logs:
`κ(θ̄e^x)^η/((1 − γ)βχ)`. -/
noncomputable def llL (κ γ β χ η θb x : ℝ) : ℝ := κ * (θb * exp x) ^ η / ((1 - γ) * β * χ)

/-- The bracket on the right of (20.16), with Cobb–Douglas matching, in logs:
`z̄e^{ẑ} − b + (1 − σ)κ(θ̄e^x)^η/((1 − γ)χ) − γκθ̄e^x/(1 − γ)`. -/
noncomputable def llR (zb b σ γ κ χ η θb zh x : ℝ) : ℝ :=
  zb * exp zh - b + (1 - σ) * κ * (θb * exp x) ^ η / ((1 - γ) * χ) -
    γ * κ * (θb * exp x) / (1 - γ)

/-- AKMM, p. 608: with Cobb–Douglas matching (20.23), `llL` is the left side of (20.16) divided
by `β`. -/
theorem ll_lhs_eq {χ η κ γ β θb : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) (hγ1 : γ < 1)
    (hβ : 0 < β) (hθ : 0 < θb) (x : ℝ) :
    llL κ γ β χ η θb x = jcLHS (cdMatch χ η hχ hη0 hη1) κ γ (θb * exp x) / β := by
  have hp : 0 < θb * exp x := mul_pos hθ (exp_pos x)
  have hγ : (1 - γ) ≠ 0 := by linarith
  rw [llL, jcLHS, (eq_20_23 hχ hη0 hη1 hp).2, Real.rpow_neg hp.le]
  have : 0 < (θb * exp x) ^ η := by positivity
  field_simp

/-- AKMM, p. 608: with Cobb–Douglas matching (20.23), `llR` is the bracket of (20.16) (using
`λ_w/λ_f = θ`). -/
theorem ll_rhs_eq {χ η κ γ σ b zb θb : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1)
    (hγ1 : γ < 1) (hθ : 0 < θb) (zh x : ℝ) :
    llR zb b σ γ κ χ η θb zh x =
      jcRHS (cdMatch χ η hχ hη0 hη1) (zb * exp zh) b σ γ κ (θb * exp x) := by
  have hp : 0 < θb * exp x := mul_pos hθ (exp_pos x)
  have hγ : (1 - γ) ≠ 0 := by linarith
  rw [llR, jcRHS, match_lamW_eq _ hp, (eq_20_23 hχ hη0 hη1 hp).2, Real.rpow_neg hp.le]
  have : 0 < (θb * exp x) ^ η := by positivity
  field_simp
  ring

/-- AKMM, (20.25), p. 608: the log-linearisation coefficients as exact derivatives at the steady
state: `d llL/dθ̂ = A = κθ̄^ηη/((1 − γ)βχ)`, `∂llR/∂ẑ = z̄` and
`∂llR/∂θ̂ = B = (1 − σ)κθ̄^ηη/((1 − γ)χ) − γκθ̄/(1 − γ)`. -/
theorem eq_20_25 {κ γ β χ η θb zb b σ : ℝ} (hθ : 0 < θb) :
    HasDerivAt (llL κ γ β χ η θb) (κ * θb ^ η * η / ((1 - γ) * β * χ)) 0 ∧
    HasDerivAt (fun zh ↦ llR zb b σ γ κ χ η θb zh 0) zb 0 ∧
    HasDerivAt (llR zb b σ γ κ χ η θb 0)
      ((1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) 0 := by
  have hpow : ∀ x, (θb * exp x) ^ η = θb ^ η * exp (η * x) := ll_rpow_exp hθ
  have hE : HasDerivAt (fun x ↦ θb ^ η * exp (η * x)) (θb ^ η * η) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul η).exp.const_mul (θb ^ η)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · have h := hE.const_mul κ |>.div_const ((1 - γ) * β * χ)
    have e : llL κ γ β χ η θb = fun x ↦ κ * (θb ^ η * exp (η * x)) / ((1 - γ) * β * χ) := by
      funext x; rw [llL, hpow]
    rw [e]; refine h.congr_deriv ?_; ring
  · have h := ((hasDerivAt_exp (0 : ℝ)).const_mul zb).sub_const
      (b - (1 - σ) * κ * (θb * exp 0) ^ η / ((1 - γ) * χ) + γ * κ * (θb * exp 0) / (1 - γ))
    simp only [exp_zero, mul_one] at h ⊢
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun zh ↦ ?_)
    simp only [llR, exp_zero, mul_one]; ring
  · have h1 := (hE.const_mul ((1 - σ) * κ)).div_const ((1 - γ) * χ)
    have h2 := (((hasDerivAt_exp (0 : ℝ)).const_mul θb).const_mul (γ * κ)).div_const (1 - γ)
    have h := (h1.sub h2).const_add (zb * exp 0 - b)
    have e : llR zb b σ γ κ χ η θb 0 = fun x ↦ zb * exp 0 - b +
        ((1 - σ) * κ * (θb ^ η * exp (η * x)) / ((1 - γ) * χ) -
          γ * κ * (θb * exp x) / (1 - γ)) := by
      funext x; rw [llR, hpow]; ring
    rw [e]; refine h.congr_deriv ?_
    simp only [exp_zero, mul_one]; ring

/-- AKMM, (20.25), p. 608, as printed: `B` is printed with `+γκθ̄/(1 − γ)`; it exceeds the
derivative of `eq_20_25` by `2γκθ̄/(1 − γ) > 0`. -/
theorem eq_20_25_misprint {κ γ χ η θb σ : ℝ} (hκ : 0 < κ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ : 0 < θb) :
    (1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) + γ * κ * θb / (1 - γ) ≠
      (1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ) := by
  intro h
  have h1 : 0 < 1 - γ := by linarith
  have : 0 < γ * κ * θb / (1 - γ) := by positivity
  linarith

/-- AKMM, p. 608 (method of undetermined coefficients): with `E[ẑ_{t+1}] = ρẑ_t`, the guess
`θ̂_t = Cẑ_t` solves `Aθ̂_t = E[z̄ẑ_{t+1} + Bθ̂_{t+1}]` for every `ẑ_t` iff `C = ρz̄/(A − ρB)`. -/
theorem ll_undetermined {A B C ρ zb : ℝ} (h : A - ρ * B ≠ 0) :
    (∀ zh : ℝ, A * (C * zh) = zb * (ρ * zh) + B * (C * (ρ * zh))) ↔ C = ρ * zb / (A - ρ * B) := by
  rw [eq_div_iff h]
  constructor
  · intro hz; have := hz 1; linarith
  · intro hc zh; linear_combination zh * hc

/-- The coefficient of (20.26), `(1 − γ)[κθ̄^ηη/χ · (1/(ρβ) − (1 − σ)) + κγθ̄]^{−1}`. -/
noncomputable def llCoeff (κ γ η χ ρ β σ θb : ℝ) : ℝ :=
  (1 - γ) / (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) + κ * γ * θb)

/-- AKMM, (20.26), p. 608: with `z̄ = 1`, `ρz̄/(A − ρB)` for the coefficients of `eq_20_25` is
the coefficient `llCoeff` of (20.26). -/
theorem eq_20_26 {κ γ β χ η θb ρ σ : ℝ} (hγ1 : γ < 1) (hβ : 0 < β) (hχ : 0 < χ) (hρ : 0 < ρ) :
    ρ * 1 / (κ * θb ^ η * η / ((1 - γ) * β * χ) -
      ρ * ((1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ))) =
      llCoeff κ γ η χ ρ β σ θb := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  rw [llCoeff]
  by_cases hD : κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) + κ * γ * θb = 0
  · have e : κ * θb ^ η * η / ((1 - γ) * β * χ) -
        ρ * ((1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) =
        ρ / (1 - γ) * (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) + κ * γ * θb) := by
      field_simp; ring
    rw [e, hD]; simp
  · field_simp
    ring

/-- AKMM, (20.26), p. 608: with the printed sign of `B` the same computation gives
`(1 − γ)[κθ̄^ηη/χ(1/(ρβ) − (1 − σ)) − κγθ̄]^{−1}`, not (20.26). -/
theorem eq_20_26_printed_B {κ γ β χ η θb ρ σ : ℝ} (hγ1 : γ < 1) (hβ : 0 < β) (hχ : 0 < χ)
    (hρ : 0 < ρ) :
    ρ * 1 / (κ * θb ^ η * η / ((1 - γ) * β * χ) -
      ρ * ((1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) + γ * κ * θb / (1 - γ))) =
      (1 - γ) / (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) - κ * γ * θb) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  by_cases hD : κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) - κ * γ * θb = 0
  · have e : κ * θb ^ η * η / ((1 - γ) * β * χ) -
        ρ * ((1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) + γ * κ * θb / (1 - γ)) =
        ρ / (1 - γ) * (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) - κ * γ * θb) := by
      field_simp; ring
    rw [e, hD]; simp
  · field_simp
    ring

/-- `1/(ρβ) − (1 − σ) > 0` when `ρ, β ∈ (0, 1]`, `ρβ < 1` and `σ ≥ 0`. -/
theorem ll_gap_pos {ρ β σ : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1) (hσ : 0 ≤ σ) :
    0 < 1 / (ρ * β) - (1 - σ) := by
  have : 1 < 1 / (ρ * β) := by rw [lt_div_iff₀ (by positivity)]; linarith
  linarith

/-- AKMM, p. 608: a smaller `κ` makes the response of `θ` larger (for given `θ̄`). -/
theorem ll_cs_kappa {κ₁ κ₂ γ η χ ρ β σ θb : ℝ} (hκ : 0 < κ₁) (h : κ₁ < κ₂) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1)
    (hσ : 0 ≤ σ) (hθ : 0 < θb) :
    llCoeff κ₂ γ η χ ρ β σ θb < llCoeff κ₁ γ η χ ρ β σ θb := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  set D := θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) + γ * θb with hD
  have hDp : 0 < D := by positivity
  have e : ∀ κ, llCoeff κ γ η χ ρ β σ θb = (1 - γ) / (κ * D) := fun κ ↦ by
    rw [llCoeff, hD]; ring_nf
  rw [e, e]
  exact div_lt_div_of_pos_left (by linarith) (by positivity) (by nlinarith)

/-- AKMM, p. 608: a smaller bargaining power `γ` makes the response of `θ` larger. -/
theorem ll_cs_gamma {κ γ₁ γ₂ η χ ρ β σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ₁) (h : γ₁ < γ₂)
    (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1)
    (hσ : 0 ≤ σ) (hθ : 0 < θb) :
    llCoeff κ γ₂ η χ ρ β σ θb < llCoeff κ γ₁ η χ ρ β σ θb := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  set E := κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) with hE
  have hEp : 0 < E := by positivity
  have hk1 : 0 ≤ κ * γ₁ * θb := mul_nonneg (mul_nonneg hκ.le hγ0) hθ.le
  have hk2 : 0 ≤ κ * γ₂ * θb := mul_nonneg (mul_nonneg hκ.le (hγ0.trans h.le)) hθ.le
  unfold llCoeff
  rw [← hE]
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos hκ hθ]

/-- `θ̄^ηη` is strictly increasing in `η > 0` when `θ̄ ≥ 1`. -/
theorem ll_rpow_mul_strictMono {θb η₁ η₂ : ℝ} (hθ : 1 ≤ θb) (hη : 0 < η₁) (h : η₁ < η₂) :
    θb ^ η₁ * η₁ < θb ^ η₂ * η₂ := by
  have h1 : θb ^ η₁ ≤ θb ^ η₂ := Real.rpow_le_rpow_of_exponent_le hθ h.le
  have h0 : 0 < θb ^ η₁ := Real.rpow_pos_of_pos (by linarith) _
  nlinarith

/-- AKMM, p. 608: a smaller `η` makes the response larger, provided `θ̄^ηη` increases in `η`
(here `θ̄ ≥ 1`, as at the calibrated `θ̄ = 1`). -/
theorem ll_cs_eta {κ γ η₁ η₂ χ ρ β σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hη : 0 < η₁) (h : η₁ < η₂) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1)
    (hσ : 0 ≤ σ) (hθ : 1 ≤ θb) :
    llCoeff κ γ η₂ χ ρ β σ θb < llCoeff κ γ η₁ χ ρ β σ θb := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hm := ll_rpow_mul_strictMono hθ hη h
  have hθ0 : 0 < θb := by linarith
  have hp : 0 < θb ^ η₁ := Real.rpow_pos_of_pos hθ0 _
  have hp2 : 0 < θb ^ η₂ := Real.rpow_pos_of_pos hθ0 _
  unfold llCoeff
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : κ * θb ^ η₁ * η₁ / χ < κ * θb ^ η₂ * η₂ / χ := by
    apply div_lt_div_of_pos_right _ hχ; nlinarith
  nlinarith

/-- AKMM, p. 608 (counterexample): for small `θ̄` a smaller `η` lowers the response. With
`θ̄ = e^{−4}`, `θ̄^ηη` is larger at `η = 1/2` than at `η = 3/4`, so the coefficient is smaller at
`η = 1/2`. -/
theorem ll_cs_eta_counterexample {κ γ χ ρ β σ : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1) (hσ : 0 ≤ σ) :
    llCoeff κ γ (1 / 2) χ ρ β σ (exp (-4)) < llCoeff κ γ (3 / 4) χ ρ β σ (exp (-4)) := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have e1 : exp (-4) ^ (1 / 2 : ℝ) = exp (-2) := by
    rw [← Real.exp_mul]; norm_num
  have e2 : exp (-4) ^ (3 / 4 : ℝ) = exp (-3) := by
    rw [← Real.exp_mul]; norm_num
  have key : exp (-3) * (3 / 4) < exp (-2) * (1 / 2) := by
    have : exp (-2) = exp (-3) * exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    have := Real.exp_one_gt_d9
    have : 0 < exp (-3) := exp_pos _
    nlinarith
  unfold llCoeff
  rw [e1, e2]
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : κ * exp (-3) * (3 / 4) / χ < κ * exp (-2) * (1 / 2) / χ := by
    apply div_lt_div_of_pos_right _ hχ; nlinarith
  nlinarith

/-- AKMM, p. 608: a larger `χ` makes the response larger. -/
theorem ll_cs_chi {κ γ η χ₁ χ₂ ρ β σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hχ : 0 < χ₁) (h : χ₁ < χ₂) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1)
    (hσ : 0 ≤ σ) (hθ : 0 < θb) :
    llCoeff κ γ η χ₁ ρ β σ θb < llCoeff κ γ η χ₂ ρ β σ θb := by
  have hχ2 : 0 < χ₂ := hχ.trans h
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  unfold llCoeff
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : κ * θb ^ η * η / χ₂ < κ * θb ^ η * η / χ₁ := div_lt_div_of_pos_left (by positivity) hχ h
  nlinarith

/-- AKMM, p. 608: a larger persistence `ρ` makes the response larger. -/
theorem ll_cs_rho {κ γ η χ ρ₁ ρ₂ β σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ₁) (h : ρ₁ < ρ₂) (hβ : 0 < β) (hρβ : ρ₂ * β < 1)
    (hσ : 0 ≤ σ) (hθ : 0 < θb) :
    llCoeff κ γ η χ ρ₁ β σ θb < llCoeff κ γ η χ ρ₂ β σ θb := by
  have hg := ll_gap_pos (hρ.trans h) hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  unfold llCoeff
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : 1 / (ρ₂ * β) < 1 / (ρ₁ * β) :=
    div_lt_div_of_pos_left one_pos (by positivity) (by nlinarith)
  have : 0 < κ * θb ^ η * η / χ := by positivity
  nlinarith

/-- AKMM, p. 608: a larger discount factor `β` makes the response larger. -/
theorem ll_cs_beta {κ γ η χ ρ β₁ β₂ σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β₁) (h : β₁ < β₂) (hρβ : ρ * β₂ < 1)
    (hσ : 0 ≤ σ) (hθ : 0 < θb) :
    llCoeff κ γ η χ ρ β₁ σ θb < llCoeff κ γ η χ ρ β₂ σ θb := by
  have hg := ll_gap_pos hρ (hβ.trans h) hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  unfold llCoeff
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : 1 / (ρ * β₂) < 1 / (ρ * β₁) :=
    div_lt_div_of_pos_left one_pos (by positivity) (by nlinarith)
  have : 0 < κ * θb ^ η * η / χ := by positivity
  nlinarith

/-- AKMM, p. 608: a smaller separation probability `σ` makes the response larger. -/
theorem ll_cs_sigma {κ γ η χ ρ β σ₁ σ₂ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1) (hσ : 0 ≤ σ₁)
    (h : σ₁ < σ₂) (hθ : 0 < θb) :
    llCoeff κ γ η χ ρ β σ₂ θb < llCoeff κ γ η χ ρ β σ₁ θb := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  unfold llCoeff
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : 0 < κ * θb ^ η * η / χ := by positivity
  nlinarith

/-- AKMM, §20.6.4, p. 611: with a rigid wage `w̄` the job-creation condition is
`κ/λ_f(θ_t) = βE[z_{t+1} − w̄ + (1 − σ)κ/λ_f(θ_{t+1})]`; with Cobb–Douglas matching, in logs,
the derivatives at the steady state are `A_r = κθ̄^ηη/(βχ)` (left side divided by `β`) and
`B_r = (1 − σ)κθ̄^ηη/χ`. -/
theorem eq_20_27_deriv {κ β χ η θb zb wb σ : ℝ} (hθ : 0 < θb) :
    HasDerivAt (fun x ↦ κ * (θb * exp x) ^ η / (β * χ)) (κ * θb ^ η * η / (β * χ)) 0 ∧
    HasDerivAt (fun x ↦ zb - wb + (1 - σ) * κ * (θb * exp x) ^ η / χ)
      ((1 - σ) * (κ * θb ^ η * η / χ)) 0 := by
  have hpow : ∀ x, (θb * exp x) ^ η = θb ^ η * exp (η * x) := ll_rpow_exp hθ
  have hE : HasDerivAt (fun x ↦ θb ^ η * exp (η * x)) (θb ^ η * η) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul η).exp.const_mul (θb ^ η)
    simpa using this
  simp only [hpow]
  refine ⟨?_, ?_⟩
  · refine ((hE.const_mul κ).div_const (β * χ)).congr_deriv ?_; ring
  · refine (((hE.const_mul ((1 - σ) * κ)).div_const χ).const_add (zb - wb)).congr_deriv ?_
    ring

/-- AKMM, (20.27), p. 611: with rigid wages, `ρ/(A_r − ρB_r) =
[κθ̄^ηη/χ · (1/(ρβ) − (1 − σ))]^{−1}`. -/
theorem eq_20_27 {κ β χ η θb ρ σ : ℝ} (hβ : 0 < β) (hχ : 0 < χ) (hρ : 0 < ρ) :
    ρ * 1 / (κ * θb ^ η * η / (β * χ) - ρ * ((1 - σ) * (κ * θb ^ η * η / χ))) =
      1 / (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ))) := by
  by_cases hD : κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) = 0
  · have e : κ * θb ^ η * η / (β * χ) - ρ * ((1 - σ) * (κ * θb ^ η * η / χ)) =
        ρ * (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ))) := by field_simp
    rw [e, hD]; simp
  · field_simp

/-- AKMM, p. 611: comparing (20.26) and (20.27), the rigid-wage response is larger: it is not
multiplied by `1 − γ` and lacks the term `κγθ̄`. -/
theorem ll_rigid_gt {κ γ η χ ρ β σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 < γ)
    (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1) (hσ : 0 ≤ σ)
    (hθ : 0 < θb) :
    llCoeff κ γ η χ ρ β σ θb < 1 / (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ))) := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  have hE : 0 < κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) := by positivity
  unfold llCoeff
  rw [div_lt_div_iff₀ (by positivity) hE]
  nlinarith [mul_pos (mul_pos hκ hγ0) hθ]

/-- AKMM, 20.A.4, p. 882 (the worked example): log-linearising
`K_{t+1} = K_t^αN_t^{1−α} + (1 − δ)K_t − C_t` at the steady state gives
`K̄k_{t+1} = K̄^αN̄^{1−α}(αk_t + (1 − α)n_t) + (1 − δ)K̄k_t − C̄c_t`: the coefficients are the
derivatives of the right side in the log deviations `k`, `n`, `c` at `0`. -/
theorem eq_20_A_4_example {Kb Nb Cb α δ : ℝ} (hK : 0 < Kb) (hN : 0 < Nb) :
    HasDerivAt (fun k ↦ (Kb * exp k) ^ α * Nb ^ (1 - α) + (1 - δ) * (Kb * exp k) - Cb)
      (Kb ^ α * Nb ^ (1 - α) * α + (1 - δ) * Kb) 0 ∧
    HasDerivAt (fun n ↦ Kb ^ α * (Nb * exp n) ^ (1 - α) + (1 - δ) * Kb - Cb)
      (Kb ^ α * Nb ^ (1 - α) * (1 - α)) 0 ∧
    HasDerivAt (fun c ↦ Kb ^ α * Nb ^ (1 - α) + (1 - δ) * Kb - Cb * exp c) (-Cb) 0 := by
  have hE : ∀ a : ℝ, HasDerivAt (fun x ↦ exp (a * x)) a 0 := fun a ↦ by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).exp
  refine ⟨?_, ?_, ?_⟩
  · have h := ((((hE α).const_mul (Kb ^ α)).mul_const (Nb ^ (1 - α))).add
      (((hasDerivAt_exp (0 : ℝ)).const_mul Kb).const_mul (1 - δ))).sub_const Cb
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun k ↦ ?_)).congr_deriv ?_
    · simp only [ll_rpow_exp hK, Pi.add_apply]
    · simp only [exp_zero]; ring
  · have h := ((((hE (1 - α)).const_mul (Nb ^ (1 - α))).const_mul (Kb ^ α)).add_const
      ((1 - δ) * Kb)).sub_const Cb
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun n ↦ ?_)).congr_deriv ?_
    · simp only [ll_rpow_exp hN]
    · ring
  · have h := ((hasDerivAt_exp (0 : ℝ)).const_mul Cb).const_sub
      (Kb ^ α * Nb ^ (1 - α) + (1 - δ) * Kb)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun c ↦ ?_)).congr_deriv ?_
    · ring
    · simp

end AKMM.FrictionalLaborMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Endogenous separations

AKMM, §20.7, pp. 611–614, and 20.A.5, pp. 882–883. The matched firm chooses the separation
probability `σ` at maintenance cost `c(σ)`, `c′ < 0`.

* `eq_20_28`: the first-order condition of `σ ↦ −c(σ) + β(1 − σ)E[J′]` is `−c′(σ) = βE[J′]`, and
  with (20.10) it is `−c′(σ) = κ/λ_f(θ)`.
* `es_J_div`, `eq_20_29`: with `σ(z)` and `c(σ(z))`, the equilibrium equations give the job-creation
  equation (20.29).
* With `c(σ) = φσ^{−ξ}` and Cobb–Douglas matching: `es_foc_cd`: (20.28) reads
  `ξφσ^{−ξ−1} = κθ^η/χ`; `eq_20_31`, `eq_20_32`: its solution is exactly log-linear,
  `σ(θ̄e^x) = σ̄e^{−ηx/(ξ+1)}` and `c = c̄e^{ξηx/(ξ+1)}`; `es_ss_foc`: at the steady state
  `κσ̄θ̄^η/χ = ξc̄`.
* `eq_20_A_5_deriv`: the derivatives at the steady state of the bracket of (20.29) in the log
  deviations of `z`, `c`, `σ`, `θ`; `eq_20_A_5_misprint`: the printed first display of 20.A.5,
  with `β` on both sides, is inconsistent with the steady state for `β < 1`.
* `eq_20_A_6`: the undetermined-coefficient equation for `G`; `es_G`: substituting (20.31),
  (20.32) and the steady-state condition, `GΓ = Θ`, so `G = Θ/Γ` when `Γ ≠ 0`.
* `es_std_ratio`: `std(λ̂_w)/std(σ̂) = (1 − η)(1 + ξ)/η` (p. 613).
* `es_rigid_cancel`, `es_rigid_G`: with rigid wages the terms in `ĉ` and `σ̂` cancel exactly and
  `G` is the coefficient of (20.27) (p. 614); `es_nash_no_cancel`: with Nash bargaining they do
  not cancel (for `γ ∈ (0, 1)`, `G ≠ 0`).

Departures: `Γ ≠ 0` is an added hypothesis for `G = Θ/Γ`; the steady-state condition
`κσ̄θ̄^η/χ = ξc̄` used in 20.A.5–20.A.6 is made explicit.
-/

namespace AKMM.FrictionalLaborMarkets

open Real

variable {Z : Type*} [Fintype Z]

/-- AKMM, (20.28), p. 612: the terms of the matched firm's problem that depend on `σ` are
`−c(σ) + β(1 − σ)E[J′]` (using `V = 0`); if `c` has derivative `c′` at `σ`, the first-order
condition is `−c′(σ) = βE[J′]`, which by (20.10) is `−c′(σ) = κ/λ_f(θ)`. -/
theorem eq_20_28 {c : ℝ → ℝ} {c' σ β EJ κ lf : ℝ} (hc : HasDerivAt c c' σ)
    (h10 : κ / lf = β * EJ) :
    HasDerivAt (fun s ↦ -c s + β * ((1 - s) * EJ)) (-c' - β * EJ) σ ∧
      (-c' - β * EJ = 0 ↔ -c' = κ / lf) := by
  refine ⟨?_, ?_⟩
  · have h := hc.neg.add ((((hasDerivAt_const σ (1 : ℝ)).sub (hasDerivAt_id' σ)).mul_const
      EJ).const_mul β)
    refine h.congr_deriv ?_; ring
  · rw [h10]; constructor <;> intro h <;> linarith

/-- AKMM, (20.29), p. 612: with endogenous `σ(z)` and maintenance cost `c(σ(z))`, the equilibrium
equations give `J(z)/(1 − γ) = z − b − c(σ(z)) + (1 − σ(z) − γλ_w(θ(z)))/(1 − γ) · κ/λ_f(θ(z))`. -/
theorem es_J_div (MF : MatchFn) (P : Z → Z → ℝ) {κ β γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w σ cσ J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z - cσ z + β * dmpEx P (fun z' ↦ (1 - σ z) * J z' +
      σ z * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ z) * W z' + σ z * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    J z / (1 - γ) = zv z - b - cσ z +
      (1 - σ z - γ * lamW MF (θ z)) / (1 - γ) * (κ / lamF MF (θ z)) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have hJ := h7 z
  rw [dmp_ex_congr P (g := fun z' ↦ (1 - σ z) * J z') (fun z' ↦ by rw [h9 z']; ring),
    dmp_ex_mul] at hJ
  have hw' : ∀ z', W z' - U z' = γ * J z' / (1 - γ) := by
    intro z'
    have := h15 z'
    rw [h9 z'] at this
    rw [eq_div_iff hγ]; linarith
  have e : ∀ z', (1 - σ z) * W z' + σ z * U z' - (lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') = ((1 - σ z - lamW MF (θ z)) * γ / (1 - γ)) * J z' := by
    intro z'
    calc _ = (1 - σ z - lamW MF (θ z)) * (W z' - U z') := by ring
      _ = _ := by rw [hw' z']; ring
  have hsub : dmpEx P (fun z' ↦ (1 - σ z) * W z' + σ z * U z') z -
      dmpEx P (fun z' ↦ lamW MF (θ z) * W z' + (1 - lamW MF (θ z)) * U z') z =
      ((1 - σ z - lamW MF (θ z)) * γ / (1 - γ)) * dmpEx P J z := by
    rw [← dmp_ex_mul, ← dmp_ex_congr P e]
    simp only [dmpEx, ← Finset.sum_sub_distrib, mul_sub]
  have hWU : W z - U z = w z - b + β * (((1 - σ z - lamW MF (θ z)) * γ / (1 - γ)) *
      dmpEx P J z) := by
    rw [← hsub, h11 z, h12 z]; ring
  have hsum : J z / (1 - γ) = J z + (W z - U z) := by
    rw [hw' z]; field_simp; ring
  rw [hsum, hJ, hWU, show κ / lamF MF (θ z) = β * dmpEx P J z from h10]
  field_simp
  ring

/-- AKMM, (20.29), p. 612: the job-creation equation with endogenous separations,
`κ/((1 − γ)λ_f(θ_t)) = βE[z_{t+1} − b − c(σ(z_{t+1})) +
(1 − σ(z_{t+1}) − γλ_w(θ_{t+1}))/(1 − γ) · κ/λ_f(θ_{t+1})]`. -/
theorem eq_20_29 (MF : MatchFn) (P : Z → Z → ℝ) {κ β γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w σ cσ J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z - cσ z + β * dmpEx P (fun z' ↦ (1 - σ z) * J z' +
      σ z * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ z) * W z' + σ z * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    κ / ((1 - γ) * lamF MF (θ z)) = β * dmpEx P (fun z' ↦ zv z' - b - cσ z' +
      (1 - σ z' - γ * lamW MF (θ z')) / (1 - γ) * (κ / lamF MF (θ z'))) z := by
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have e := dmp_ex_congr P (fun z' ↦ (es_J_div MF P hγ1 hθ h7 h8 h9 h11 h12 h15 z').symm) z
  rw [e, show (fun z' ↦ J z' / (1 - γ)) = fun z' ↦ (1 - γ)⁻¹ * J z' by
    funext z'; ring, dmp_ex_mul, mul_left_comm, ← h10]
  field_simp

/-- AKMM, p. 612: with `c(σ) = φσ^{−ξ}` (so `c′(σ) = −ξφσ^{−ξ−1}`) and Cobb–Douglas matching
(`κ/λ_f(θ) = κθ^η/χ`), (20.28) reads `ξφσ^{−ξ−1} = κθ^η/χ`. -/
theorem es_foc_cd {φ ξ σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun s ↦ φ * s ^ (-ξ)) (-(ξ * φ * σ ^ (-ξ - 1))) σ := by
  have := (Real.hasDerivAt_rpow_const (p := -ξ) (Or.inl hσ.ne')).const_mul φ
  refine this.congr_deriv ?_; ring

/-- AKMM, (20.31), p. 612: if `σ̄` solves `ξφσ̄^{−ξ−1} = κθ̄^η/χ`, then for every `x`,
`σ = σ̄e^{−ηx/(ξ+1)}` solves the condition at `θ = θ̄e^x`: the log-linear relation
`σ̂ = −(η/(ξ + 1))θ̂` holds exactly. It is the only positive solution. -/
theorem eq_20_31 {φ ξ κ χ η θb σb : ℝ} (hφ : 0 < φ) (hξ : 0 < ξ) (hθ : 0 < θb) (hσ : 0 < σb)
    (hss : ξ * φ * σb ^ (-ξ - 1) = κ * θb ^ η / χ) (x : ℝ) :
    ξ * φ * (σb * exp (-(η / (ξ + 1)) * x)) ^ (-ξ - 1) = κ * (θb * exp x) ^ η / χ ∧
      ∀ s, 0 < s → ξ * φ * s ^ (-ξ - 1) = κ * (θb * exp x) ^ η / χ →
        s = σb * exp (-(η / (ξ + 1)) * x) := by
  have hξ1 : (ξ + 1) ≠ 0 := by linarith
  have e1 : (σb * exp (-(η / (ξ + 1)) * x)) ^ (-ξ - 1) = σb ^ (-ξ - 1) * exp (η * x) := by
    rw [Real.mul_rpow hσ.le (exp_pos _).le, ← Real.exp_mul]
    congr 2; field_simp; ring
  have e2 : (θb * exp x) ^ η = θb ^ η * exp (η * x) := ll_rpow_exp hθ x
  have hmain : ξ * φ * (σb * exp (-(η / (ξ + 1)) * x)) ^ (-ξ - 1) = κ * (θb * exp x) ^ η / χ := by
    rw [e1, e2, ← mul_assoc, hss]; ring
  refine ⟨hmain, fun s hs h ↦ ?_⟩
  have hp : 0 < σb * exp (-(η / (ξ + 1)) * x) := by positivity
  rw [← hmain] at h
  have hξφ : ξ * φ ≠ 0 := by positivity
  have h' := mul_left_cancel₀ hξφ h
  have hne : (-ξ - 1) ≠ 0 := by linarith
  rw [← Real.rpow_rpow_inv hs.le hne, h', Real.rpow_rpow_inv hp.le hne]

/-- AKMM, (20.32), p. 613: along the solution of `eq_20_31` the maintenance cost is
`c = φσ^{−ξ} = c̄e^{ξηx/(ξ+1)}`, `c̄ = φσ̄^{−ξ}`: `ĉ = (ξη/(ξ + 1))θ̂` exactly. -/
theorem eq_20_32 {φ ξ η σb : ℝ} (hξ : 0 < ξ) (hσ : 0 < σb) (x : ℝ) :
    φ * (σb * exp (-(η / (ξ + 1)) * x)) ^ (-ξ) = φ * σb ^ (-ξ) * exp (ξ * η / (ξ + 1) * x) := by
  have hξ1 : (ξ + 1) ≠ 0 := by linarith
  rw [Real.mul_rpow hσ.le (exp_pos _).le, ← Real.exp_mul,
    show -(η / (ξ + 1)) * x * -ξ = ξ * η / (ξ + 1) * x by ring]
  ring

/-- AKMM, 20.A.5, p. 883 (used implicitly): at the steady state, (20.28) with `c = φσ^{−ξ}`,
`ξφσ̄^{−ξ−1} = κθ̄^η/χ`, gives `κσ̄θ̄^η/χ = ξc̄`, `c̄ = φσ̄^{−ξ}`. -/
theorem es_ss_foc {φ ξ κ χ η θb σb : ℝ} (hσ : 0 < σb)
    (hss : ξ * φ * σb ^ (-ξ - 1) = κ * θb ^ η / χ) :
    κ * σb * θb ^ η / χ = ξ * (φ * σb ^ (-ξ)) := by
  have e : σb ^ (-ξ - 1) = σb ^ (-ξ) / σb := Real.rpow_sub_one hσ.ne' _
  rw [e] at hss
  have : κ * σb * θb ^ η / χ = σb * (κ * θb ^ η / χ) := by ring
  rw [this, ← hss]
  field_simp

/-- AKMM, 20.A.5, p. 882: with Cobb–Douglas matching, the bracket of (20.29) is
`z − c − b + κθ^η/((1 − γ)χ) − κσθ^η/((1 − γ)χ) − γκθ/(1 − γ)` (the first display of 20.A.5,
without the misprinted `β` on the left). -/
theorem es_bracket_cd {χ η : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) {z b c σ γ κ θ : ℝ}
    (hγ1 : γ < 1) (hθ : 0 < θ) :
    z - b - c + (1 - σ - γ * lamW (cdMatch χ η hχ hη0 hη1) θ) / (1 - γ) *
      (κ / lamF (cdMatch χ η hχ hη0 hη1) θ) =
    z - c - b + κ * θ ^ η / ((1 - γ) * χ) - κ * σ * θ ^ η / ((1 - γ) * χ) -
      γ * κ * θ / (1 - γ) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  rw [match_lamW_eq _ hθ, (eq_20_23 hχ hη0 hη1 hθ).2, Real.rpow_neg hθ.le]
  have : 0 < θ ^ η := by positivity
  field_simp
  ring

/-- AKMM, 20.A.5, p. 882: the bracket of (20.29) in log deviations,
`z̄e^{ẑ} − c̄e^{ĉ} − b + κ(θ̄e^{θ̂})^η/((1 − γ)χ) − κσ̄e^{σ̂}(θ̄e^{θ̂})^η/((1 − γ)χ) −
γκθ̄e^{θ̂}/(1 − γ)`. -/
noncomputable def esR (zb cb b σb γ κ χ η θb zh ch sh x : ℝ) : ℝ :=
  zb * exp zh - cb * exp ch - b + κ * (θb * exp x) ^ η / ((1 - γ) * χ) -
    κ * (σb * exp sh) * (θb * exp x) ^ η / ((1 - γ) * χ) - γ * κ * (θb * exp x) / (1 - γ)

/-- AKMM, 20.A.5, p. 882: the derivatives of the bracket at the steady state: `z̄` in `ẑ`, `−c̄` in
`ĉ`, `−κσ̄θ̄^η/((1 − γ)χ)` in `σ̂`, and
`(1 − σ̄)κθ̄^ηη/((1 − γ)χ) − γκθ̄/(1 − γ)` in `θ̂`. -/
theorem eq_20_A_5_deriv {zb cb b σb γ κ χ η θb : ℝ} (hθ : 0 < θb) :
    HasDerivAt (fun zh ↦ esR zb cb b σb γ κ χ η θb zh 0 0 0) zb 0 ∧
    HasDerivAt (fun ch ↦ esR zb cb b σb γ κ χ η θb 0 ch 0 0) (-cb) 0 ∧
    HasDerivAt (fun sh ↦ esR zb cb b σb γ κ χ η θb 0 0 sh 0)
      (-(κ * σb * θb ^ η / ((1 - γ) * χ))) 0 ∧
    HasDerivAt (fun x ↦ esR zb cb b σb γ κ χ η θb 0 0 0 x)
      ((1 - σb) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) 0 := by
  have hpow : ∀ x, (θb * exp x) ^ η = θb ^ η * exp (η * x) := ll_rpow_exp hθ
  have hE : HasDerivAt (fun x ↦ exp (η * x)) η 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul η).exp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ((hasDerivAt_exp (0 : ℝ)).const_mul zb).add_const
      (-(cb * exp 0) - b + κ * (θb * exp 0) ^ η / ((1 - γ) * χ) -
        κ * (σb * exp 0) * (θb * exp 0) ^ η / ((1 - γ) * χ) - γ * κ * (θb * exp 0) / (1 - γ))
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun zh ↦ ?_)).congr_deriv ?_
    · simp only [esR]; ring
    · simp
  · have h := ((hasDerivAt_exp (0 : ℝ)).const_mul cb).neg.add_const
      (zb * exp 0 - b + κ * (θb * exp 0) ^ η / ((1 - γ) * χ) -
        κ * (σb * exp 0) * (θb * exp 0) ^ η / ((1 - γ) * χ) - γ * κ * (θb * exp 0) / (1 - γ))
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ch ↦ ?_)).congr_deriv ?_
    · simp only [esR, Pi.neg_apply]; ring
    · simp
  · have h := (((hasDerivAt_exp (0 : ℝ)).const_mul σb).const_mul
      (-(κ * (θb * exp 0) ^ η / ((1 - γ) * χ)))).add_const
      (zb * exp 0 - cb * exp 0 - b + κ * (θb * exp 0) ^ η / ((1 - γ) * χ) -
        γ * κ * (θb * exp 0) / (1 - γ))
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun sh ↦ ?_)).congr_deriv ?_
    · simp only [esR]; ring
    · simp only [exp_zero, mul_one]; ring
  · have h1 := (hE.const_mul (θb ^ η)).const_mul (κ * (1 - σb * exp 0) / ((1 - γ) * χ))
    have h2 := ((hasDerivAt_exp (0 : ℝ)).const_mul θb).const_mul (γ * κ / (1 - γ))
    have h := (h1.sub h2).add_const (zb * exp 0 - cb * exp 0 - b)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
    · simp only [esR, hpow, Pi.sub_apply]; ring
    · simp only [exp_zero, mul_one]; ring

/-- AKMM, 20.A.5, p. 882, as printed: the first display `κθ_t^η/((1 − γ)βχ) = βE[⋯]` has `β` on
both sides. At a steady state of (20.29), where `κθ̄^η/((1 − γ)βχ)` equals the bracket `R̄`, the
printed form would force `R̄ = βR̄`, impossible for `β < 1` since `R̄ > 0`. -/
theorem eq_20_A_5_misprint {κ θη γ β χ R : ℝ} (hκ : 0 < κ) (hθη : 0 < θη) (hγ1 : γ < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hχ : 0 < χ) (hcorrect : κ * θη / ((1 - γ) * β * χ) = R)
    (hprinted : κ * θη / ((1 - γ) * β * χ) = β * R) : False := by
  have h1γ : 0 < 1 - γ := by linarith
  have hR : 0 < R := by rw [← hcorrect]; positivity
  have : (1 - β) * R = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h <;> linarith

/-- AKMM, (20.A.6), p. 883: with `θ̂ = Gẑ`, `σ̂ = Eẑ`, `ĉ = Fẑ` and `E[ẑ_{t+1}] = ρẑ_t`, the
log-linearised (20.29), `Aθ̂_t = E[z̄ẑ′ − c̄ĉ′ − κσ̄θ̄^ησ̂′/((1 − γ)χ) + Bθ̂′]` (coefficients from
`eq_20_A_5_deriv`), holds for all `ẑ_t` iff
`G = llCoeff · (z̄ − c̄F − κσ̄θ̄^ηE/((1 − γ)χ))`. -/
theorem eq_20_A_6 {κ γ β χ η θb ρ σb zb cb E F G : ℝ} (hγ1 : γ < 1) (hβ : 0 < β) (hχ : 0 < χ)
    (hρ : 0 < ρ)
    (hD : κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σb)) + κ * γ * θb ≠ 0) :
    (∀ zh : ℝ, κ * θb ^ η * η / ((1 - γ) * β * χ) * (G * zh) =
      (zb - cb * F - κ * σb * θb ^ η * E / ((1 - γ) * χ)) * (ρ * zh) +
        ((1 - σb) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) * (G * (ρ * zh))) ↔
    G = llCoeff κ γ η χ ρ β σb θb * (zb - cb * F - κ * σb * θb ^ η * E / ((1 - γ) * χ)) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  set X := zb - cb * F - κ * σb * θb ^ η * E / ((1 - γ) * χ)
  have hAB : κ * θb ^ η * η / ((1 - γ) * β * χ) -
      ρ * ((1 - σb) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) ≠ 0 := by
    have e : κ * θb ^ η * η / ((1 - γ) * β * χ) -
        ρ * ((1 - σb) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) =
        ρ / (1 - γ) * (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σb)) + κ * γ * θb) := by
      field_simp; ring
    rw [e]; exact mul_ne_zero (div_ne_zero hρ.ne' hγ) hD
  have hK := eq_20_26 (κ := κ) (γ := γ) (β := β) (χ := χ) (η := η) (θb := θb) (ρ := ρ)
    (σ := σb) hγ1 hβ hχ hρ
  rw [← hK, ll_undetermined hAB, mul_one, div_mul_eq_mul_div]

/-- AKMM, (20.A.6) and p. 613: substituting `E = −ηG/(ξ + 1)` (20.31), `F = ξηG/(ξ + 1)` (20.32)
and the steady-state condition `κσ̄θ̄^η/χ = ξc̄` into `G = K(z̄ − c̄F − κσ̄θ̄^ηE/((1 − γ)χ))`
gives `GΓ = Θ` with `Θ = Kz̄`, `Γ = 1 + Kc̄(ξη/(ξ + 1))(1 − 1/(1 − γ))`; hence `G = Θ/Γ` when
`Γ ≠ 0`. -/
theorem es_G {K zb cb κ σb θη χ γ ξ η G : ℝ} (hγ1 : γ < 1) (hξ : 0 < ξ)
    (hfoc : κ * σb * θη / χ = ξ * cb)
    (hG : G = K * (zb - cb * (ξ * η / (ξ + 1) * G) -
      κ * σb * θη * (-(η / (ξ + 1)) * G) / ((1 - γ) * χ))) :
    G * (1 + K * cb * (ξ * η / (ξ + 1)) * (1 - 1 / (1 - γ))) = K * zb ∧
      (1 + K * cb * (ξ * η / (ξ + 1)) * (1 - 1 / (1 - γ)) ≠ 0 →
        G = K * zb / (1 + K * cb * (ξ * η / (ξ + 1)) * (1 - 1 / (1 - γ)))) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have hξ1 : (ξ + 1) ≠ 0 := by linarith
  have key : κ * σb * θη * (-(η / (ξ + 1)) * G) / ((1 - γ) * χ) =
      -(ξ * cb * (η / (ξ + 1)) * G / (1 - γ)) := by
    rw [← hfoc]
    by_cases hχ : χ = 0
    · simp [hχ]
    · field_simp
  rw [key] at hG
  have h1 : G * (1 + K * cb * (ξ * η / (ξ + 1)) * (1 - 1 / (1 - γ))) = K * zb := by
    have e : G * (1 + K * cb * (ξ * η / (ξ + 1)) * (1 - 1 / (1 - γ))) =
        G + K * (cb * (ξ * η / (ξ + 1) * G) - ξ * cb * (η / (ξ + 1)) * G / (1 - γ)) := by
      field_simp
    rw [e]
    nth_rewrite 1 [hG]
    ring
  exact ⟨h1, fun hΓ ↦ by rw [eq_div_iff hΓ]; exact h1⟩

/-- AKMM, p. 613: with `λ̂_w = (1 − η)θ̂ = (1 − η)Gẑ` (from `λ_w = χθ^{1−η}`) and
`σ̂ = −(η/(ξ + 1))Gẑ` (20.31), the ratio of standard deviations is
`std(λ̂_w)/std(σ̂) = |(1 − η)G|/|−(η/(ξ + 1))G| = (1 − η)(1 + ξ)/η`. -/
theorem es_std_ratio {η ξ G : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hξ : 0 < ξ) (hG : G ≠ 0) :
    |(1 - η) * G| / |-(η / (ξ + 1)) * G| = (1 - η) * (1 + ξ) / η := by
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 1 - η),
    abs_of_pos (by positivity : (0 : ℝ) < η / (ξ + 1))]
  have : 0 < |G| := abs_pos.mpr hG
  field_simp
  ring

/-- AKMM, p. 613: with Cobb–Douglas matching `λ_w(θ̄e^x) = λ_w(θ̄)e^{(1−η)x}`: the log deviation
of the job-finding probability is exactly `(1 − η)θ̂`. -/
theorem es_lamW_loglinear {χ η θb : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) (hθ : 0 < θb)
    (x : ℝ) :
    lamW (cdMatch χ η hχ hη0 hη1) (θb * exp x) =
      lamW (cdMatch χ η hχ hη0 hη1) θb * exp ((1 - η) * x) := by
  rw [(eq_20_23 hχ hη0 hη1 (mul_pos hθ (exp_pos x))).1, (eq_20_23 hχ hη0 hη1 hθ).1,
    ll_rpow_exp hθ]
  ring

/-- AKMM, §20.7.4, p. 614: with rigid wages the bracket is `z − w̄ − c + (1 − σ)κθ^η/χ`, whose
`ĉ` and `σ̂` terms in the log-linearisation are `−c̄F − κσ̄θ̄^ηE/χ`; with (20.31), (20.32) and the
steady-state condition they cancel exactly. -/
theorem es_rigid_cancel {cb κ σb θη χ ξ η G : ℝ} (hξ : 0 < ξ) (hχ : χ ≠ 0)
    (hfoc : κ * σb * θη / χ = ξ * cb) :
    -(cb * (ξ * η / (ξ + 1) * G)) - κ * σb * θη * (-(η / (ξ + 1)) * G) / χ = 0 := by
  have hξ1 : (ξ + 1) ≠ 0 := by linarith
  have : κ * σb * θη = ξ * cb * χ := by field_simp at hfoc; linarith
  rw [this]
  field_simp
  ring

/-- AKMM, §20.7.4, p. 614: hence with rigid wages and endogenous separations the coefficient is
the one of (20.27): if `A_rG = ρ(z̄ − c̄F − κσ̄θ̄^ηE/χ + B_rG)` then
`G = z̄[κθ̄^ηη/χ(1/(ρβ) − (1 − σ̄))]^{−1}`. -/
theorem es_rigid_G {κ β χ η θb ρ σb zb cb ξ G : ℝ} (hβ : 0 < β) (hχ : 0 < χ) (hρ : 0 < ρ)
    (hξ : 0 < ξ) (hfoc : κ * σb * θb ^ η / χ = ξ * cb)
    (hD : κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σb)) ≠ 0)
    (heq : κ * θb ^ η * η / (β * χ) * G = ρ * (zb - cb * (ξ * η / (ξ + 1) * G) -
      κ * σb * θb ^ η * (-(η / (ξ + 1)) * G) / χ + (1 - σb) * (κ * θb ^ η * η / χ) * G)) :
    G = zb * (1 / (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σb)))) := by
  have hc := es_rigid_cancel (G := G) (η := η) hξ hχ.ne' hfoc
  have e2 : κ * θb ^ η * η / (β * χ) * G =
      ρ * (zb + (1 - σb) * (κ * θb ^ η * η / χ) * G) := by
    rw [heq]; linear_combination ρ * hc
  rw [mul_one_div, eq_div_iff hD]
  field_simp at e2 ⊢
  linarith

/-- AKMM, §20.7.2, p. 613: with Nash bargaining the `ĉ` and `σ̂` terms do not cancel:
`−c̄F − κσ̄θ̄^ηE/((1 − γ)χ) = (γ/(1 − γ))c̄ξηG/(ξ + 1)`, nonzero for `γ ∈ (0, 1)` and
`c̄, η, G ≠ 0`. -/
theorem es_nash_no_cancel {cb κ σb θη χ ξ η G γ : ℝ} (hξ : 0 < ξ) (hχ : χ ≠ 0) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hcb : cb ≠ 0) (hη : η ≠ 0) (hG : G ≠ 0)
    (hfoc : κ * σb * θη / χ = ξ * cb) :
    -(cb * (ξ * η / (ξ + 1) * G)) - κ * σb * θη * (-(η / (ξ + 1)) * G) / ((1 - γ) * χ) =
      γ / (1 - γ) * (cb * ξ * η * G / (ξ + 1)) ∧
    γ / (1 - γ) * (cb * ξ * η * G / (ξ + 1)) ≠ 0 := by
  have hξ1 : (ξ + 1) ≠ 0 := by linarith
  have hγ : (1 - γ) ≠ 0 := by linarith
  have : κ * σb * θη = ξ * cb * χ := by field_simp at hfoc; linarith
  refine ⟨?_, ?_⟩
  · rw [this]; field_simp; ring
  · have : (1 - γ) ≠ 0 := hγ
    have : γ ≠ 0 := hγ0.ne'
    have : ξ ≠ 0 := hξ.ne'
    positivity

end AKMM.FrictionalLaborMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Labour-market frictions in the neoclassical growth model

AKMM, §20.8, pp. 614–620, and Appendices 20.A.6–20.A.8, pp. 883–887. The aggregate state is
`X = (z, K, u)`. The functional fixed point `(Q, Ω, w, d, θ)` is computed in the book, not shown
to exist, and is not formalised; the results below are the equations the book derives.

* `ngm_rental`, `ngm_y`: the firm's capital demand gives `r = αz(K/(1 − u))^{α−1}`, and the
  surplus per match is `y = (1 − α)z(K/(1 − u))^α`; `ngm_resource`: income `rK + (1 − u)w + ub
  + d` equals output plus home production minus vacancy costs.
* `eq_20_36`: the Arrow-security price `Q(z′) = βf(z′)U′(c′(z′))/U′(c)` from (20.A.7), (20.A.9),
  (20.A.11); `ngm_arrow_foc`: in a two-period economy with finitely many states, at any optimum of
  the household's problem with Arrow securities, `Q(z′) = βf(z′)U′(c′(z′))/U′(c)` (by the
  first-order condition along a trade of one security against consumption).
* `ngm_asset_value`: the derivation of 20.A.7 for each claim, giving (20.37) and the values of
  vacancies, employed and unemployed workers.
* With aggregate states in a finite set and state prices `Q(X, X′)` (`dmpEx`), the labour block
  is the model of §20.4 with `β = 1` and `P = Q`: `eq_20_42`, `eq_20_43` (job creation),
  `eq_20_44` (wage) and `eq_20_45` (dividend); with a rigid wage, `eq_20_48`.
* 20.A.8: `ngm_calib_u`, `ngm_calib_r`, `ngm_calib_K` (with the exponent `1/(α − 1)`; the printed
  `1/(1 − α)` is wrong, `ngm_calib_K_misprint`), `ngm_calib_kappa` (the printed formula for `κ`
  does not solve the steady state of (20.43), `ngm_calib_kappa_misprint`), `ngm_calib_w`.
* §20.8.2: `ngm_rigid_max_profit`, `ngm_rigid_min_profit`: with `w̃ = max{w̄, y}` the flow
  profit `y − w̃` is never positive; `min{w̄, y}` keeps it nonnegative.

Departure: the aggregate state space is finite (the book's `X` has a continuum of values and
`Q(z′, X)` is a density); the derivations use only linearity of the integral.
-/

namespace AKMM.FrictionalLaborMarkets

/-- AKMM, p. 615: the firm's problem `max_k zk^α − rk` has first-order condition
`αzk^{α−1} = r`. -/
theorem ngm_rental {z α r k : ℝ} (hk : 0 < k) :
    HasDerivAt (fun x ↦ z * x ^ α - r * x) (α * z * k ^ (α - 1) - r) k ∧
      (α * z * k ^ (α - 1) - r = 0 ↔ r = α * z * k ^ (α - 1)) := by
  refine ⟨?_, ?_⟩
  · have := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hk.ne')).const_mul z).sub
      ((hasDerivAt_id k).const_mul r)
    refine this.congr_deriv ?_; simp; ring
  · constructor <;> intro h <;> linarith

/-- AKMM, p. 616: with `r = αz(K/(1 − u))^{α−1}`, the surplus per match is
`y = z(K/(1 − u))^α − r·K/(1 − u) = (1 − α)z(K/(1 − u))^α`. -/
theorem ngm_y {z α k : ℝ} (hk : 0 < k) :
    z * k ^ α - α * z * k ^ (α - 1) * k = (1 - α) * z * k ^ α := by
  rw [Real.rpow_sub_one hk.ne']
  field_simp

/-- AKMM, (20.45), p. 618: the dividend `d = (1 − u)(y − w) − κθu`. -/
def ngmDividend (u y w κ θ : ℝ) : ℝ := (1 - u) * (y - w) - κ * θ * u

/-- AKMM, (20.45) and p. 615: family income `rK + (1 − u)w + ub + d` equals output
`(1 − u)z(K/(1 − u))^α` plus home production `ub` minus vacancy costs `κθu`. -/
theorem ngm_resource {z α K u w b κ θ : ℝ} (hK : 0 < K) (hu : u < 1) :
    α * z * (K / (1 - u)) ^ (α - 1) * K + (1 - u) * w + u * b +
      ngmDividend u ((1 - α) * z * (K / (1 - u)) ^ α) w κ θ =
      (1 - u) * (z * (K / (1 - u)) ^ α) + u * b - κ * θ * u := by
  have h1u : 0 < 1 - u := by linarith
  have hk : 0 < K / (1 - u) := div_pos hK h1u
  rw [ngmDividend, Real.rpow_sub_one hk.ne']
  field_simp
  ring

/-- AKMM, (20.36) and 20.A.6, p. 884: combining the first-order conditions `U′(c) = μ(z)`
(20.A.7), `βV₂′f(z′|z) = μ(z)Q(z′)` (20.A.9) and the envelope condition `V₂′ = μ(z′) = U′(c′)`
(20.A.11), `Q(z′) = βf(z′|z)U′(c′)/U′(c)` (20.A.12). -/
theorem eq_20_36 {β f Uc Uc' μ μ' V2 Q : ℝ} (hμ : μ ≠ 0) (hA7 : Uc = μ) (hA9 : β * V2 * f = μ * Q)
    (hA11 : V2 = μ') (hA7' : Uc' = μ') : Q = β * f * Uc' / Uc := by
  rw [hA7, hA7', ← hA11, eq_div_iff hμ]
  linarith

/-- AKMM, (20.36), 20.A.6, p. 883: in a two-period economy with finitely many next-period states
`z′`, endowments `e` today and `e′(z′)` tomorrow, Arrow-security prices `Q(z′)` and probabilities
`f(z′)`, if `a` maximises `U(e − Σ Q(z′)a(z′)) + βΣ f(z′)U(e′(z′) + a(z′))` and `U` is
differentiable, then `Q(z′)U′(c) = βf(z′)U′(c′(z′))`, i.e. `Q(z′) = βf(z′)U′(c′(z′))/U′(c)`. -/
theorem ngm_arrow_foc {ι : Type*} [Fintype ι] {U U' : ℝ → ℝ} {β e : ℝ}
    {e' f Q a : ι → ℝ} (hU : ∀ x, HasDerivAt U (U' x) x)
    (hmax : ∀ b : ι → ℝ, U (e - ∑ i, Q i * b i) + β * ∑ i, f i * U (e' i + b i) ≤
      U (e - ∑ i, Q i * a i) + β * ∑ i, f i * U (e' i + a i)) (j : ι) :
    Q j * U' (e - ∑ i, Q i * a i) = β * f j * U' (e' j + a j) := by
  classical
  set g : ℝ → ℝ := fun t ↦ U (e - ∑ i, Q i * (a i + if i = j then t else 0)) +
    β * ∑ i, f i * U (e' i + (a i + if i = j then t else 0)) with hg
  have hsum : ∀ t, ∑ i, Q i * (a i + if i = j then t else 0) = ∑ i, Q i * a i + Q j * t := by
    intro t
    simp [mul_add, Finset.sum_add_distrib]
  have hsum2 : ∀ t, ∑ i, f i * U (e' i + (a i + if i = j then t else 0)) =
      ∑ i, f i * U (e' i + a i) - f j * U (e' j + a j) + f j * U (e' j + (a j + t)) := by
    intro t
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have : ∑ i ∈ Finset.univ.erase j, f i * U (e' i + (a i + if i = j then t else 0)) =
        ∑ i ∈ Finset.univ.erase j, f i * U (e' i + a i) := by
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp [Finset.ne_of_mem_erase hi]
    rw [this]; simp; ring
  have hgeq : g = fun t ↦ U (e - ∑ i, Q i * a i - Q j * t) + β * (∑ i, f i * U (e' i + a i) -
      f j * U (e' j + a j) + f j * U (e' j + (a j + t))) := by
    funext t; rw [hg]; simp only; rw [hsum, hsum2]; ring_nf
  have hmax0 : IsLocalMax g 0 := by
    refine Filter.Eventually.of_forall fun t ↦ ?_
    have h0 : g 0 = U (e - ∑ i, Q i * a i) + β * ∑ i, f i * U (e' i + a i) := by
      rw [hg]; simp
    rw [h0]
    exact hmax _
  have hd : HasDerivAt g (U' (e - ∑ i, Q i * a i) * (-Q j) +
      β * (f j * U' (e' j + a j))) 0 := by
    rw [hgeq]
    have h1 : HasDerivAt (fun t ↦ U (e - ∑ i, Q i * a i - Q j * t))
        (U' (e - ∑ i, Q i * a i) * (-Q j)) 0 := by
      have hin : HasDerivAt (fun t : ℝ ↦ e - ∑ i, Q i * a i - Q j * t) (-Q j) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (Q j)).const_sub (e - ∑ i, Q i * a i)
      exact (hU _).comp_of_eq (0 : ℝ) hin (by simp)
    have h2 : HasDerivAt (fun t ↦ U (e' j + (a j + t))) (U' (e' j + a j)) 0 := by
      have hin : HasDerivAt (fun t : ℝ ↦ e' j + (a j + t)) 1 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_add (a j)).const_add (e' j)
      have := (hU (e' j + a j)).comp_of_eq (0 : ℝ) hin (by simp)
      rw [mul_one] at this
      exact this
    exact h1.add (((h2.const_mul (f j)).const_add _).const_mul β)
  have := hmax0.hasDerivAt_eq_zero hd
  linarith

/-- AKMM, 20.A.7, pp. 885–886: the asset-value derivation. If the first-order condition for a
claim with price `P` paying `π` is `μP = μπ + ν₁p + ν₂(1 − p)` (as (20.A.13)–(20.A.16)), the
multipliers of the transitions are `νᵢ = βΣ f(z′)μ(z′)Pᵢ(z′)` ((20.A.17)–(20.A.24)) and
`Q(z′) = βf(z′)μ(z′)/μ` ((20.A.7), (20.A.12)), then `P = π + Σ Q(z′)(pP₁(z′) + (1 − p)P₂(z′))`;
this gives (20.37) and the equations for `V`, `W`, `U`. -/
theorem ngm_asset_value {ι : Type*} [Fintype ι] {β μ P π p ν₁ ν₂ : ℝ} {f μ' P₁ P₂ Q : ι → ℝ}
    (hμ : μ ≠ 0) (hfoc : μ * P = μ * π + ν₁ * p + ν₂ * (1 - p))
    (hν₁ : ν₁ = β * ∑ i, f i * (μ' i * P₁ i)) (hν₂ : ν₂ = β * ∑ i, f i * (μ' i * P₂ i))
    (hQ : ∀ i, Q i = β * f i * μ' i / μ) :
    P = π + ∑ i, Q i * (p * P₁ i + (1 - p) * P₂ i) := by
  have e : ∑ i, Q i * (p * P₁ i + (1 - p) * P₂ i) =
      (p * (β * ∑ i, f i * (μ' i * P₁ i)) + (1 - p) * (β * ∑ i, f i * (μ' i * P₂ i))) / μ := by
    simp only [hQ, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    field_simp
  rw [e, ← hν₁, ← hν₂]
  field_simp
  linarith

variable {S : Type*} [Fintype S]

/-- AKMM, (20.42), p. 617: with state prices `Q` in place of `βE`, (20.37)–(20.41) and
`V = 0` give `J(X)/(1 − γ) = y(X) − b + (1 − σ − γλ_w(θ(X)))/(1 − γ) · ∫Q J(X′)`; by (20.38)
the integral is `κ/λ_f(θ(X))`. This is `dmp_J_div` with `β = 1`. -/
theorem eq_20_42 (MF : MatchFn) (Q : S → S → ℝ) {κ σ γ b : ℝ} (hγ1 : γ < 1)
    {y θ w J V W U : S → ℝ} (hθ : ∀ X, 0 < θ X)
    (h37 : ∀ X, J X = y X - w X + 1 * dmpEx Q (fun X' ↦ (1 - σ) * J X' + σ * V X') X)
    (hV : ∀ X, V X = -κ + 1 * dmpEx Q (fun X' ↦ lamF MF (θ X) * J X' +
      (1 - lamF MF (θ X)) * V X') X)
    (hV0 : ∀ X, V X = 0)
    (h39 : ∀ X, W X = w X + 1 * dmpEx Q (fun X' ↦ (1 - σ) * W X' + σ * U X') X)
    (h40 : ∀ X, U X = b + 1 * dmpEx Q (fun X' ↦ lamW MF (θ X) * W X' +
      (1 - lamW MF (θ X)) * U X') X)
    (h41 : ∀ X, (1 - γ) * (W X - U X) = γ * (J X - V X)) (X : S) :
    J X / (1 - γ) = y X - b + (1 - σ - γ * lamW MF (θ X)) / (1 - γ) * dmpEx Q J X := by
  rw [dmp_J_div MF Q hγ1 hθ h37 hV hV0 h39 h40 h41 X, eq_20_10 MF Q hθ hV hV0 X, one_mul]

/-- AKMM, (20.43), p. 617: the job-creation condition of the growth model,
`κ/((1 − γ)λ_f(θ(X))) = ∫Q(X, X′)[y(X′) − b + (1 − σ − γλ_w(θ(X′)))/(1 − γ) · κ/λ_f(θ(X′))]`. -/
theorem eq_20_43 (MF : MatchFn) (Q : S → S → ℝ) {κ σ γ b : ℝ} (hγ1 : γ < 1)
    {y θ w J V W U : S → ℝ} (hθ : ∀ X, 0 < θ X)
    (h37 : ∀ X, J X = y X - w X + 1 * dmpEx Q (fun X' ↦ (1 - σ) * J X' + σ * V X') X)
    (hV : ∀ X, V X = -κ + 1 * dmpEx Q (fun X' ↦ lamF MF (θ X) * J X' +
      (1 - lamF MF (θ X)) * V X') X)
    (hV0 : ∀ X, V X = 0)
    (h39 : ∀ X, W X = w X + 1 * dmpEx Q (fun X' ↦ (1 - σ) * W X' + σ * U X') X)
    (h40 : ∀ X, U X = b + 1 * dmpEx Q (fun X' ↦ lamW MF (θ X) * W X' +
      (1 - lamW MF (θ X)) * U X') X)
    (h41 : ∀ X, (1 - γ) * (W X - U X) = γ * (J X - V X)) (X : S) :
    κ / ((1 - γ) * lamF MF (θ X)) = dmpEx Q (fun X' ↦ y X' - b +
      (1 - σ - γ * lamW MF (θ X')) / (1 - γ) * (κ / lamF MF (θ X'))) X := by
  rw [eq_20_16 MF Q hγ1 hθ h37 hV hV0 h39 h40 h41 X, one_mul]

/-- AKMM, (20.44), p. 618: the wage of the growth model, `w(X) = γ(y(X) − b) + b + γθ(X)κ`. -/
theorem eq_20_44 (MF : MatchFn) (Q : S → S → ℝ) {κ σ γ b : ℝ} (hγ1 : γ < 1)
    {y θ w J V W U : S → ℝ} (hθ : ∀ X, 0 < θ X)
    (h37 : ∀ X, J X = y X - w X + 1 * dmpEx Q (fun X' ↦ (1 - σ) * J X' + σ * V X') X)
    (hV : ∀ X, V X = -κ + 1 * dmpEx Q (fun X' ↦ lamF MF (θ X) * J X' +
      (1 - lamF MF (θ X)) * V X') X)
    (hV0 : ∀ X, V X = 0)
    (h39 : ∀ X, W X = w X + 1 * dmpEx Q (fun X' ↦ (1 - σ) * W X' + σ * U X') X)
    (h40 : ∀ X, U X = b + 1 * dmpEx Q (fun X' ↦ lamW MF (θ X) * W X' +
      (1 - lamW MF (θ X)) * U X') X)
    (h41 : ∀ X, (1 - γ) * (W X - U X) = γ * (J X - V X)) (X : S) :
    w X = γ * (y X - b) + b + γ * θ X * κ := by
  rw [(eq_20_A_2 MF Q hγ1 hθ h37 hV hV0 h39 h40 h41 X).2]; ring

/-- AKMM, (20.45), p. 618: with the wage (20.44) the dividend is
`d(X) = (1 − u)((1 − γ)(y − b) − γθκ) − κθu`, a function of `X`. -/
theorem eq_20_45 {u y b γ θ κ : ℝ} :
    ngmDividend u y (γ * (y - b) + b + γ * θ * κ) κ θ =
      (1 - u) * ((1 - γ) * (y - b) - γ * θ * κ) - κ * θ * u := by
  rw [ngmDividend]; ring

/-- AKMM, (20.47)–(20.48), p. 619, and the rigid-wage job-creation condition of §20.6.4, p. 611:
if `J(X) = y(X) − w̃(X) + βE[(1 − σ)J(X′) + σV(X′)]`, `V = 0` and `κ/λ_f(θ(X)) = βE[J(X′)]`,
then `κ/λ_f(θ(X)) = βE[y(X′) − w̃(X′) + (1 − σ)κ/λ_f(θ(X′))]` (in §20.8, `β = 1` and `E` is the
state-price integral). -/
theorem eq_20_48 (MF : MatchFn) (Q : S → S → ℝ) {κ σ β : ℝ} {y θ w J V : S → ℝ}
    (h47 : ∀ X, J X = y X - w X + β * dmpEx Q (fun X' ↦ (1 - σ) * J X' + σ * V X') X)
    (hV0 : ∀ X, V X = 0) (h38 : ∀ X, κ / lamF MF (θ X) = β * dmpEx Q J X) (X : S) :
    κ / lamF MF (θ X) = β * dmpEx Q (fun X' ↦ y X' - w X' + (1 - σ) * κ / lamF MF (θ X')) X := by
  rw [h38 X]
  congr 1
  refine dmp_ex_congr Q (fun X' ↦ ?_) X
  rw [h47 X', dmp_ex_congr Q (g := fun X'' ↦ (1 - σ) * J X'') (fun X'' ↦ by rw [hV0 X'']; ring),
    dmp_ex_mul, mul_div_assoc, h38 X']
  ring

/-- AKMM, 20.A.8, p. 887: with `θ̄ = 1` and Cobb–Douglas matching, `λ_w(1) = χ` and
`ū = σ/(χ + σ)`. -/
theorem ngm_calib_u {χ η σ u : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) :
    u = σ / (lamW (cdMatch χ η hχ hη0 hη1) 1 + σ) ↔ u = σ / (χ + σ) := by
  rw [(eq_20_23 hχ hη0 hη1 one_pos).1, Real.one_rpow, mul_one]

/-- AKMM, 20.A.8, p. 887: the steady-state Euler equation `1 = β(1 + r̄ − δ)` gives
`r̄ = 1/β − 1 + δ`. -/
theorem ngm_calib_r {β r δ : ℝ} (hβ : 0 < β) : 1 = β * (1 + r - δ) ↔ r = 1 / β - 1 + δ := by
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp; ring

/-- AKMM, 20.A.8, p. 887: `r̄ = α(K̄/(1 − ū))^{α−1}` solves for
`K̄ = (r̄/α)^{1/(α−1)}(1 − ū)` (`r̄, α > 0`, `α ≠ 1`, `ū < 1`, `K̄ > 0`). -/
theorem ngm_calib_K {α r K u : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) (hr : 0 < r) (hu : u < 1)
    (hK : 0 < K) : r = α * (K / (1 - u)) ^ (α - 1) ↔ K = (r / α) ^ (1 / (α - 1)) * (1 - u) := by
  have h1u : 0 < 1 - u := by linarith
  have hk : 0 < K / (1 - u) := div_pos hK h1u
  have hne : (α - 1) ≠ 0 := sub_ne_zero.mpr hα1
  constructor
  · intro h
    have : r / α = (K / (1 - u)) ^ (α - 1) := by rw [h]; field_simp
    rw [this, ← Real.rpow_mul hk.le, mul_one_div_cancel hne, Real.rpow_one]
    field_simp
  · intro h
    have : K / (1 - u) = (r / α) ^ (1 / (α - 1)) := by rw [h]; field_simp
    rw [this, ← Real.rpow_mul (div_pos hr hα).le, one_div_mul_cancel hne, Real.rpow_one]
    field_simp

/-- AKMM, 20.A.8, p. 887, as printed: `K̄ = (r/α)^{1/(1−α)}(1 − ū)` does not solve
`r = α(K̄/(1 − ū))^{α−1}`. With `α = 1/2`, `r = 2`, `ū = 0`, it gives `K̄ = 16`, and
`α·16^{−1/2} = 1/8 ≠ 2`. -/
theorem ngm_calib_K_misprint :
    (2 / (1 / 2) : ℝ) ^ (1 / (1 - 1 / 2) : ℝ) * (1 - 0) = 16 ∧
      (1 / 2 : ℝ) * ((16 : ℝ) / (1 - 0)) ^ ((1 / 2 : ℝ) - 1) ≠ 2 := by
  have h16 : (16 : ℝ) = 4 ^ (2 : ℝ) := by norm_num
  refine ⟨?_, ?_⟩
  · norm_num
  · rw [show (16 : ℝ) / (1 - 0) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num

/-- AKMM, 20.A.8, p. 887: at the steady state with `θ̄ = 1` (so `λ_f = λ_w = χ`) and `Q = β`,
(20.43) reads `κ/((1 − γ)χ) = β[ȳ − b + (1 − σ − γχ)/(1 − γ) · κ/χ]`; its solution is
`κ = β(1 − γ)χ(ȳ − b)/(1 − β(1 − σ − γχ))`. -/
theorem ngm_calib_kappa {β γ χ σ yb b κ : ℝ} (hγ1 : γ < 1) (hχ : 0 < χ)
    (hD : 1 - β * (1 - σ - γ * χ) ≠ 0) :
    κ / ((1 - γ) * χ) = β * (yb - b + (1 - σ - γ * χ) / (1 - γ) * (κ / χ)) ↔
      κ = β * (1 - γ) * χ * (yb - b) / (1 - β * (1 - σ - γ * χ)) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  rw [eq_div_iff hD]
  constructor
  · intro h; field_simp at h; linarith
  · intro h; field_simp; linarith

/-- AKMM, 20.A.8, p. 887, as printed: `κ = βχ(ȳ − b)(1 − β(1 − σ − γχ)/(1 − γ))^{−1}` does not
solve the steady state of (20.43): with `β = γ = σ = 1/2`, `χ = 1`, `ȳ − b = 1` it gives `1/2`,
while the solution is `1/4`. -/
theorem ngm_calib_kappa_misprint :
    (1 / 2 : ℝ) * 1 * 1 * (1 - 1 / 2 * (1 - 1 / 2 - 1 / 2 * 1) / (1 - 1 / 2))⁻¹ = 1 / 2 ∧
      (1 / 2 : ℝ) * (1 - 1 / 2) * 1 * 1 / (1 - 1 / 2 * (1 - 1 / 2 - 1 / 2 * 1)) = 1 / 4 ∧
      ¬ ((1 / 2 : ℝ) / ((1 - 1 / 2) * 1) =
        1 / 2 * (1 + (1 - 1 / 2 - 1 / 2 * 1) / (1 - 1 / 2) * ((1 / 2) / 1))) := by
  norm_num

/-- AKMM, 20.A.8, p. 887: with `θ̄ = 1` the steady-state wage (20.44) is
`w̄ = γ(ȳ − b) + b + γκ` and the dividend is `d̄ = (1 − ū)(ȳ − w̄) − κū`. -/
theorem ngm_calib_w {γ yb b κ u : ℝ} :
    γ * (yb - b) + b + γ * 1 * κ = γ * (yb - b) + b + γ * κ ∧
      ngmDividend u yb (γ * (yb - b) + b + γ * κ) κ 1 =
        (1 - u) * (yb - (γ * (yb - b) + b + γ * κ)) - κ * u := by
  refine ⟨by ring, by rw [ngmDividend]; ring⟩

/-- AKMM, §20.8.2, p. 619, as printed: with `w̃ = max{w̄, y}` the flow profit `y − w̃` is never
positive, contrary to "to maintain a positive profit". -/
theorem ngm_rigid_max_profit (wb y : ℝ) : y - max wb y ≤ 0 := by
  have := le_max_right wb y; linarith

/-- AKMM, §20.8.2, p. 619, corrected: with `w̃ = min{w̄, y}` the flow profit is nonnegative, and
positive exactly when `y > w̄` (then the wage is `w̄`). -/
theorem ngm_rigid_min_profit (wb y : ℝ) :
    0 ≤ y - min wb y ∧ (0 < y - min wb y ↔ wb < y) := by
  refine ⟨by have := min_le_right wb y; linarith, ?_⟩
  constructor
  · intro h
    by_contra hc
    rw [min_eq_right (not_lt.mp hc)] at h; linarith
  · intro h; rw [min_eq_left h.le]; linarith

end AKMM.FrictionalLaborMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The McCall search model

AKMM, §20.9, pp. 620–623. An unemployed worker receives `b` and one wage offer per period, drawn
from `F` on `[0, w_u]`; an employed worker loses the job with probability `σ`; the discount
factor is `β ∈ (0, 1)`. The Bellman equations (20.50), (20.52) are Miao's Exercise 8.2
(`Miao.Applications.od_FiringBellman` with firing probability `α = σ`; the timing is the same:
a worker who loses the job next period is unemployed then and searches the period after), which
is reused for existence, uniqueness, the reservation property and (20.55).

* `eq_20_51`: `(1 − β)U = b + β∫max{W(w) − U, 0}dF`; `eq_20_53`:
  `W(w) = (w + βσU)/(1 − β(1 − σ))`; `mc_W_strictMono`, `mc_U_pos`, `mc_W0_lt`: `W` is increasing
  and `W(0) < U`.
* `mc_exists_unique` (Miao's `ex_8_2`), `mc_reservation`: the reservation wage `w* = (1 − β)U`,
  with `W(w*) = U`; `eq_20_55`: `w* = b + β/(1 − β(1 − σ))∫_{w > w*}(w − w*)dF`, and `w*` is its
  only root (`mc_root_unique`).
* `mc_lambda_antitone`: `λ = 1 − F(w*)` is decreasing in `w*`.
* Comparative statics (p. 622): `mc_cs_b`, `mc_cs_beta`, `mc_cs_sigma`: `w*` increases in `b` and
  `β` and decreases in `σ` (the last is Miao's `ex_8_2_alpha`); `mc_G_partials`:
  `∂G/∂β < 0`, `∂G/∂σ > 0`, `∂G/∂b < 0` (when some offer exceeds `w*`).
* `mc_I_hasDerivAt` (Leibniz's rule): if `F` has no atom at `x`,
  `d/dx∫max{w − x, 0}dF = −(1 − F(x))`; `mc_G_w`: `∂G/∂w* = 1 + β(1 − F(w*))/(1 − β(1 − σ)) > 0`.
* A shift of all offers by `ε` (p. 623): `mc_shift_eq` (the reservation condition of the shifted
  distribution), `mc_shift_bounds`: the reservation wage `R(ε) = w*(ε) + ε` satisfies
  `0 < R(ε₂) − R(ε₁) < ε₂ − ε₁`; `mc_shift_deriv`: `dR/dε = β(1 − F(w*))/(1 − β(1 − σ) +
  β(1 − F(w*))) ∈ (0, 1)`.

Departures: the strict signs need `F(w > w*) > 0` (some offer is accepted), and Leibniz's rule
needs `F` to have no atom at `w*`; the derivative of `R` assumes `R` differentiable, as the book's
use of the implicit function theorem does (the difference bounds need no differentiability).
-/

namespace AKMM.FrictionalLaborMarkets

open MeasureTheory Filter Topology

variable {F : Measure ℝ} [IsProbabilityMeasure F] {B b σ β : ℝ}

/-- The option-value integral `I(x) = ∫max{w − x, 0}dF`. -/
noncomputable def mcI (F : Measure ℝ) (x : ℝ) : ℝ := ∫ w, max (w - x) 0 ∂F

omit [IsProbabilityMeasure F] in
/-- AKMM, (20.53), p. 622: `W(w) = (w + βσU)/(1 − β(1 − σ))` (Miao's `ex_8_2_E`). -/
theorem eq_20_53 (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) {V W : ℝ → ℝ} {U : ℝ}
    (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) :
    ∀ w ∈ Set.Icc 0 B, W w = (w + β * σ * U) / (1 - β * (1 - σ)) := by
  intro w hw
  rw [Miao.Applications.ex_8_2_E hβ0 hβ1 hσ hB w hw]
  congr 1 <;> ring

/-- `1 − β(1 − σ) > 0`. -/
theorem mc_D_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) : 0 < 1 - β * (1 - σ) := by
  nlinarith

/-- AKMM, (20.50)–(20.51), p. 621: `(1 − β)U = b + β∫max{W(w) − U, 0}dF`. -/
theorem eq_20_51 (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    {V W : ℝ → ℝ} {U : ℝ} (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) :
    (1 - β) * U = b + β * ∫ w, max (W w - U) 0 ∂F := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  have hW := eq_20_53 hβ0 hβ1 hσ hB
  have hcongr : (fun w ↦ max (W w - U) 0) =ᵐ[F]
      fun w ↦ max ((w + β * σ * U) / (1 - β * (1 - σ)) - U) 0 :=
    hF.mono fun w hw ↦ by simp only [hW w hw]
  have hcongr2 : V =ᵐ[F] fun w ↦ U + max ((w + β * σ * U) / (1 - β * (1 - σ)) - U) 0 :=
    hF.mono fun w hw ↦ by
      simp only [(hB.2 w hw).2, hW w hw]
      rcases le_total ((w + β * σ * U) / (1 - β * (1 - σ))) U with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]; ring
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  have hi : Integrable (fun w ↦ max ((w + β * σ * U) / (1 - β * (1 - σ)) - U) 0) F :=
    Miao.Applications.od_integrable_of_continuous hF (by fun_prop)
  have h1 := hB.1
  rw [integral_congr_ae hcongr2, integral_add (integrable_const U) hi, integral_const,
    probReal_univ, one_smul] at h1
  rw [integral_congr_ae hcongr]
  linarith

omit [IsProbabilityMeasure F] in
/-- AKMM, p. 622: `W(w)` is strictly increasing in `w`. -/
theorem mc_W_strictMono (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) {V W : ℝ → ℝ} {U : ℝ}
    (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) :
    StrictMonoOn W (Set.Icc 0 B) := by
  intro x hx y hy hxy
  rw [eq_20_53 hβ0 hβ1 hσ hB x hx, eq_20_53 hβ0 hβ1 hσ hB y hy]
  exact div_lt_div_of_pos_right (by linarith) (mc_D_pos hβ0 hβ1 hσ)

/-- AKMM, p. 622: with `b > 0`, `U ≥ b/(1 − β) > 0` (the worker can always reject). -/
theorem mc_U_pos (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    (hb : 0 < b) {V W : ℝ → ℝ} {U : ℝ}
    (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) : b / (1 - β) ≤ U ∧ 0 < U := by
  have h := eq_20_51 hF hβ0 hβ1 hσ hB
  have hI : 0 ≤ ∫ w, max (W w - U) 0 ∂F := integral_nonneg fun w ↦ le_max_right _ _
  have h1 : b ≤ (1 - β) * U := by nlinarith
  have h1β : 0 < 1 - β := by linarith
  refine ⟨by rw [div_le_iff₀ h1β]; linarith, ?_⟩
  have : 0 < (1 - β) * U := by linarith
  exact pos_of_mul_pos_right this h1β.le

omit [IsProbabilityMeasure F] in
/-- AKMM, p. 622: `W(0) = βσU/(1 − β(1 − σ)) < U` (when `U > 0`). -/
theorem mc_W0_lt (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) (hB0 : 0 ≤ B) {V W : ℝ → ℝ} {U : ℝ}
    (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) (hU : 0 < U) :
    W 0 = β * σ * U / (1 - β * (1 - σ)) ∧ W 0 < U := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  have h := eq_20_53 hβ0 hβ1 hσ hB 0 ⟨le_rfl, hB0⟩
  rw [zero_add] at h
  refine ⟨h, ?_⟩
  rw [h, div_lt_iff₀ hD]
  nlinarith

/-- AKMM, pp. 621–622: the Bellman equations (20.50), (20.52) have a solution, unique on
`[0, w_u]` (Miao's `ex_8_2`). -/
theorem mc_exists_unique (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 ≤ σ) : ∃ V W U, Miao.Applications.od_FiringBellman F B b σ β V W U ∧
      ∀ V' W' U', Miao.Applications.od_FiringBellman F B b σ β V' W' U' → U' = U ∧
        ∀ w ∈ Set.Icc 0 B, W' w = W w ∧ V' w = V w := by
  obtain ⟨U, -, hB, huniq⟩ := Miao.Applications.ex_8_2 (c := b) hF hβ0 hβ1 hσ
  refine ⟨_, _, U, hB, fun V' W' U' hB' ↦ ?_⟩
  obtain ⟨hU, h⟩ := huniq V' W' U' hB'
  exact ⟨hU, fun w hw ↦ h w hw⟩

omit [IsProbabilityMeasure F] in
/-- AKMM, p. 622: the reservation wage `w* = (1 − β)U`: the worker accepts `w` (`W(w) ≥ U`) iff
`w ≥ w*`, and `W(w*) = U` (Miao's `ex_8_2_reservation`). -/
theorem mc_reservation (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) {V W : ℝ → ℝ} {U : ℝ}
    (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) :
    (∀ w ∈ Set.Icc 0 B, U ≤ W w ↔ (1 - β) * U ≤ w) ∧
      ((1 - β) * U ∈ Set.Icc 0 B → W ((1 - β) * U) = U) := by
  refine ⟨fun w hw ↦ (Miao.Applications.ex_8_2_reservation hβ0 hβ1 hσ hB w hw).1, fun hw ↦ ?_⟩
  have hD := mc_D_pos hβ0 hβ1 hσ
  rw [eq_20_53 hβ0 hβ1 hσ hB _ hw]
  field_simp; ring

/-- AKMM, (20.54)–(20.55), p. 622: `w* = b + β/(1 − β(1 − σ))∫_{w > w*}(w − w*)dF(w)` (Miao's
`ex_8_2_reservation_eq`). -/
theorem eq_20_55 (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    {V W : ℝ → ℝ} {U : ℝ} (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) :
    (1 - β) * U = b + β / (1 - β * (1 - σ)) *
      ∫ w in Set.Ioi ((1 - β) * U), (w - (1 - β) * U) ∂F := by
  have h := Miao.Applications.ex_8_2_reservation_eq hF hβ0 hβ1 hσ hB
  rw [show 1 - β * (1 - σ) = 1 - β + σ * β by ring]
  linarith

/-- AKMM, p. 622: (20.55) has the reservation wage as its only root (Miao's
`ex_8_2_root_unique`). -/
theorem mc_root_unique (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    {V W : ℝ → ℝ} {U : ℝ} (hB : Miao.Applications.od_FiringBellman F B b σ β V W U) (x : ℝ) :
    x - b - β / (1 - β * (1 - σ)) * ∫ w in Set.Ioi x, (w - x) ∂F = 0 ↔ x = (1 - β) * U := by
  have h := Miao.Applications.ex_8_2_root_unique hF hβ0 hβ1 hσ hB x
  rw [Miao.Applications.od_firingψ, show 1 - β + σ * β = 1 - β * (1 - σ) by ring] at h
  exact h

omit [IsProbabilityMeasure F] in
/-- AKMM, p. 622: the job-finding probability `λ = 1 − F(w*) = F(w > w*)` is decreasing in
`w*`. -/
theorem mc_lambda_antitone [IsFiniteMeasure F] : Antitone fun x ↦ F.real (Set.Ioi x) :=
  fun _ _ h ↦ measureReal_mono (Set.Ioi_subset_Ioi h)

/-- The reservation-wage function `G(x) = x − b − β/(1 − β(1 − σ))∫_{w > x}(w − x)dF`. -/
noncomputable def mcG (F : Measure ℝ) (b σ β x : ℝ) : ℝ :=
  x - b - β / (1 - β * (1 - σ)) * ∫ w in Set.Ioi x, (w - x) ∂F

omit [IsProbabilityMeasure F] in
/-- `G` is Miao's `od_firingψ` with `α = σ`. -/
theorem mc_G_eq (x : ℝ) : mcG F b σ β x = Miao.Applications.od_firingψ F b σ β x := by
  rw [mcG, Miao.Applications.od_firingψ, show 1 - β + σ * β = 1 - β * (1 - σ) by ring]

/-- AKMM, p. 622: the reservation wage increases with `b`. -/
theorem mc_cs_b (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    {b₁ b₂ : ℝ} (h : b₁ < b₂) {V₁ W₁ V₂ W₂ : ℝ → ℝ} {U₁ U₂ : ℝ}
    (hB₁ : Miao.Applications.od_FiringBellman F B b₁ σ β V₁ W₁ U₁)
    (hB₂ : Miao.Applications.od_FiringBellman F B b₂ σ β V₂ W₂ U₂) :
    (1 - β) * U₁ < (1 - β) * U₂ := by
  have h1 := (mc_root_unique hF hβ0 hβ1 hσ hB₁ ((1 - β) * U₁)).mpr rfl
  have h2 := (mc_root_unique hF hβ0 hβ1 hσ hB₂ ((1 - β) * U₂)).mpr rfl
  have hmono := Miao.Applications.od_firingψ_strictMono (c := b₂) hF hβ0 hβ1 hσ
  have hlt : Miao.Applications.od_firingψ F b₂ σ β ((1 - β) * U₁) <
      Miao.Applications.od_firingψ F b₂ σ β ((1 - β) * U₂) := by
    rw [← mc_G_eq, ← mc_G_eq]; unfold mcG; linarith
  exact hmono.lt_iff_lt.mp hlt

/-- AKMM, p. 622: `β/(1 − β(1 − σ))` is strictly increasing in `β ∈ (0, 1)` (for `σ ≥ 0`). -/
theorem mc_coef_strictMono {β₁ β₂ : ℝ} (hσ : 0 ≤ σ) (hβ0 : 0 < β₁) (h : β₁ < β₂)
    (hβ1 : β₂ < 1) : β₁ / (1 - β₁ * (1 - σ)) < β₂ / (1 - β₂ * (1 - σ)) := by
  have hD1 := mc_D_pos hβ0 (h.trans hβ1) hσ
  have hD2 := mc_D_pos (hβ0.trans h) hβ1 hσ
  rw [div_lt_div_iff₀ hD1 hD2]
  nlinarith

/-- AKMM, p. 622: the reservation wage increases with `β`, strictly if some offer above the
lower reservation wage has positive probability. -/
theorem mc_cs_beta (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hσ : 0 ≤ σ) {β₁ β₂ : ℝ} (hβ0 : 0 < β₁)
    (h : β₁ < β₂) (hβ1 : β₂ < 1) {V₁ W₁ V₂ W₂ : ℝ → ℝ} {U₁ U₂ : ℝ}
    (hB₁ : Miao.Applications.od_FiringBellman F B b σ β₁ V₁ W₁ U₁)
    (hB₂ : Miao.Applications.od_FiringBellman F B b σ β₂ V₂ W₂ U₂) :
    (1 - β₁) * U₁ ≤ (1 - β₂) * U₂ ∧
      (0 < ∫ w in Set.Ioi ((1 - β₁) * U₁), (w - (1 - β₁) * U₁) ∂F →
        (1 - β₁) * U₁ < (1 - β₂) * U₂) := by
  have hb2 : 0 < β₂ := hβ0.trans h
  have h1 := (mc_root_unique hF hβ0 (h.trans hβ1) hσ hB₁ ((1 - β₁) * U₁)).mpr rfl
  have h2 := (mc_root_unique hF hb2 hβ1 hσ hB₂ ((1 - β₂) * U₂)).mpr rfl
  have hmono := Miao.Applications.od_firingψ_strictMono (c := b) hF hb2 hβ1 hσ
  have hk := mc_coef_strictMono hσ hβ0 h hβ1
  set x₁ := (1 - β₁) * U₁
  set I := ∫ w in Set.Ioi x₁, (w - x₁) ∂F
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun w hw ↦ by
    simp only [Set.mem_Ioi] at hw; linarith
  have hle : Miao.Applications.od_firingψ F b σ β₂ x₁ ≤
      Miao.Applications.od_firingψ F b σ β₂ ((1 - β₂) * U₂) := by
    rw [← mc_G_eq, ← mc_G_eq]; unfold mcG
    nlinarith [mul_le_mul_of_nonneg_right hk.le hI]
  refine ⟨hmono.le_iff_le.mp hle, fun hIpos ↦ ?_⟩
  have hlt : Miao.Applications.od_firingψ F b σ β₂ x₁ <
      Miao.Applications.od_firingψ F b σ β₂ ((1 - β₂) * U₂) := by
    rw [← mc_G_eq, ← mc_G_eq]; unfold mcG
    nlinarith [mul_lt_mul_of_pos_right hk hIpos]
  exact hmono.lt_iff_lt.mp hlt

/-- AKMM, p. 622: the reservation wage decreases with `σ` (Miao's `ex_8_2_alpha`). -/
theorem mc_cs_sigma (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) {σ₁ σ₂ : ℝ}
    (hσ : 0 ≤ σ₁) (h : σ₁ ≤ σ₂) {V₁ W₁ V₂ W₂ : ℝ → ℝ} {U₁ U₂ : ℝ}
    (hB₁ : Miao.Applications.od_FiringBellman F B b σ₁ β V₁ W₁ U₁)
    (hB₂ : Miao.Applications.od_FiringBellman F B b σ₂ β V₂ W₂ U₂) :
    (1 - β) * U₂ ≤ (1 - β) * U₁ :=
  Miao.Applications.ex_8_2_alpha hF hβ0 hβ1 hσ h hB₁ hB₂

/-- AKMM, p. 622: with `I = ∫_{w > w*}(w − w*)dF > 0` fixed, `G(w*, β, σ, b) = w* − b −
βI/(1 − β(1 − σ))` has `∂G/∂β = −I/(1 − β(1 − σ))² < 0`, `∂G/∂σ = β²I/(1 − β(1 − σ))² > 0`
and `∂G/∂b = −1 < 0`. -/
theorem mc_G_partials {x I : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) (hI : 0 < I) :
    HasDerivAt (fun β' ↦ x - b - β' / (1 - β' * (1 - σ)) * I)
      (-(I / (1 - β * (1 - σ)) ^ 2)) β ∧ -(I / (1 - β * (1 - σ)) ^ 2) < 0 ∧
    HasDerivAt (fun σ' ↦ x - b - β / (1 - β * (1 - σ')) * I)
      (β ^ 2 * I / (1 - β * (1 - σ)) ^ 2) σ ∧ 0 < β ^ 2 * I / (1 - β * (1 - σ)) ^ 2 ∧
    HasDerivAt (fun b' ↦ x - b' - β / (1 - β * (1 - σ)) * I) (-1) b := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  refine ⟨?_, by have : 0 < I / (1 - β * (1 - σ)) ^ 2 := by positivity
                 linarith, ?_, by positivity, ?_⟩
  · have hden : HasDerivAt (fun β' : ℝ ↦ 1 - β' * (1 - σ)) (-(1 - σ)) β := by
      simpa using ((hasDerivAt_id β).mul_const (1 - σ)).const_sub 1
    have := (((hasDerivAt_id β).div hden hD.ne').mul_const I).const_sub (x - b)
    refine this.congr_deriv ?_
    simp only [id]; field_simp; ring
  · have hden : HasDerivAt (fun σ' : ℝ ↦ 1 - β * (1 - σ')) β σ := by
      simpa using (((hasDerivAt_id σ).const_sub 1).const_mul β).const_sub 1
    have := (((hasDerivAt_const σ β).div hden hD.ne').mul_const I).const_sub (x - b)
    refine this.congr_deriv ?_
    field_simp; ring
  · have := ((hasDerivAt_id b).const_sub x).sub_const (β / (1 - β * (1 - σ)) * I)
    simpa using this

/-- The pointwise estimate behind Leibniz's rule: for all `w`,
`|max{w − y, 0} − max{w − x, 0} + (y − x)1{w > x}| ≤ |y − x|·1{|w − x| ≤ |y − x|}`. -/
theorem mc_pointwise (x y w : ℝ) :
    |max (w - y) 0 - max (w - x) 0 + (y - x) * (Set.Ioi x).indicator 1 w| ≤
      |y - x| * (Set.Icc (x - |y - x|) (x + |y - x|)).indicator 1 w := by
  have h1 := le_abs_self (y - x)
  have h2 := neg_abs_le (y - x)
  by_cases hw : w ∈ Set.Icc (x - |y - x|) (x + |y - x|)
  · rw [Set.indicator_of_mem hw, Pi.one_apply, mul_one, abs_le]
    by_cases hx : w ∈ Set.Ioi x
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      simp only [Set.mem_Ioi] at hx
      constructor <;> simp only [max_def] <;> split_ifs <;> linarith
    · rw [Set.indicator_of_notMem hx, mul_zero, add_zero]
      simp only [Set.mem_Ioi, not_lt] at hx
      obtain ⟨hw1, -⟩ := hw
      constructor <;> simp only [max_def] <;> split_ifs <;> linarith
  · rw [Set.indicator_of_notMem hw, mul_zero]
    simp only [Set.mem_Icc, not_and_or, not_le] at hw
    rcases hw with hw | hw
    · have hx : w ∉ Set.Ioi x := by simp only [Set.mem_Ioi, not_lt]; linarith
      rw [Set.indicator_of_notMem hx, mul_zero, add_zero, max_eq_right (by linarith),
        max_eq_right (by linarith)]
      simp
    · have hx : w ∈ Set.Ioi x := by simp only [Set.mem_Ioi]; linarith
      rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, max_eq_left (by linarith),
        max_eq_left (by linarith)]
      simp

/-- AKMM, p. 622 (**Leibniz's rule**): if the offer distribution has no atom at `x`, then
`d/dx ∫max{w − x, 0}dF(w) = −(1 − F(x)) = −F(w > x)`. -/
theorem mc_I_hasDerivAt (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) {x : ℝ} (hx : F {x} = 0) :
    HasDerivAt (mcI F) (-F.real (Set.Ioi x)) x := by
  have hint : ∀ y, Integrable (fun w ↦ max (w - y) 0) F := fun y ↦
    Miao.Applications.od_integrable_of_continuous hF (by fun_prop)
  have hind : ∀ s : Set ℝ, MeasurableSet s → Integrable (s.indicator (1 : ℝ → ℝ)) F :=
    fun s hs ↦ (integrable_const (1 : ℝ)).indicator hs
  -- the global estimate
  have hbound : ∀ y, |mcI F y - mcI F x - (y - x) * -F.real (Set.Ioi x)| ≤
      |y - x| * F.real (Set.Icc (x - |y - x|) (x + |y - x|)) := by
    intro y
    have e : mcI F y - mcI F x - (y - x) * -F.real (Set.Ioi x) = ∫ w,
        (max (w - y) 0 - max (w - x) 0 + (y - x) * (Set.Ioi x).indicator 1 w) ∂F := by
      have ha : Integrable (fun w ↦ max (w - y) 0 - max (w - x) 0) F := (hint y).sub (hint x)
      have hb : Integrable (fun w ↦ (y - x) * (Set.Ioi x).indicator (1 : ℝ → ℝ) w) F :=
        (hind _ measurableSet_Ioi).const_mul _
      rw [integral_add ha hb, integral_sub (hint y) (hint x), integral_const_mul,
        integral_indicator_one measurableSet_Ioi, mcI, mcI]
      ring
    rw [e]
    calc _ ≤ ∫ w, |max (w - y) 0 - max (w - x) 0 + (y - x) * (Set.Ioi x).indicator 1 w| ∂F :=
          abs_integral_le_integral_abs
      _ ≤ ∫ w, |y - x| * (Set.Icc (x - |y - x|) (x + |y - x|)).indicator 1 w ∂F :=
          integral_mono (((hint y).sub (hint x)).add
            ((hind _ measurableSet_Ioi).const_mul _)).abs
            ((hind _ measurableSet_Icc).const_mul _) fun w ↦ mc_pointwise x y w
      _ = _ := by rw [integral_const_mul, integral_indicator_one measurableSet_Icc]
  -- the measure of small intervals around `x` tends to `F {x} = 0`
  have hlim : Tendsto (fun r ↦ F (Metric.cthickening r {x})) (𝓝 0) (𝓝 0) := by
    have := tendsto_measure_cthickening_of_isClosed (μ := F) (s := {x})
      ⟨1, one_pos, measure_ne_top _ _⟩ isClosed_singleton
    rwa [hx] at this
  have hlim' : Tendsto (fun y ↦ F (Metric.cthickening |y - x| {x})) (𝓝 x) (𝓝 0) := by
    refine hlim.comp ?_
    have : Tendsto (fun y : ℝ ↦ |y - x|) (𝓝 x) (𝓝 |x - x|) :=
      ((continuous_id.sub continuous_const).abs).tendsto x
    simpa using this
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [hlim'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hc))] with y hy
  rw [Metric.cthickening_singleton _ (abs_nonneg _), Real.closedBall_eq_Icc] at hy
  have hreal : F.real (Set.Icc (x - |y - x|) (x + |y - x|)) ≤ c := by
    rw [measureReal_def]
    exact (ENNReal.toReal_le_of_le_ofReal hc.le hy.le)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
  calc _ ≤ |y - x| * F.real (Set.Icc (x - |y - x|) (x + |y - x|)) := hbound y
    _ ≤ |y - x| * c := mul_le_mul_of_nonneg_left hreal (abs_nonneg _)
    _ = c * |y - x| := mul_comm _ _

/-- AKMM, p. 622: if `F` has no atom at `x`, `∂G/∂w* = 1 + β(1 − F(w*))/(1 − β(1 − σ)) > 0`. -/
theorem mc_G_w (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    {x : ℝ} (hx : F {x} = 0) :
    HasDerivAt (mcG F b σ β) (1 + β / (1 - β * (1 - σ)) * F.real (Set.Ioi x)) x ∧
      0 < 1 + β / (1 - β * (1 - σ)) * F.real (Set.Ioi x) := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  have heq : mcG F b σ β = fun y ↦ y - b - β / (1 - β * (1 - σ)) * mcI F y := by
    funext y; rw [mcG, mcI, Miao.Applications.od_setIntegral_Ioi_eq]
  refine ⟨?_, by have : 0 ≤ F.real (Set.Ioi x) := measureReal_nonneg
                 positivity⟩
  rw [heq]
  have := (((hasDerivAt_id x).sub_const b).sub
    ((mc_I_hasDerivAt hF hx).const_mul (β / (1 - β * (1 - σ)))))
  refine this.congr_deriv ?_
  ring

omit [IsProbabilityMeasure F] in
/-- AKMM, p. 623: if every offer is shifted to `w + ε`, the reservation condition (20.55) for the
shifted distribution at `R` reads `G(R − ε, ε) = (R − ε) + ε − b − β/(1 − β(1 − σ))I(R − ε)`,
`I(x) = ∫max{w − x, 0}dF`: it is the book's `G(w*, ε)` with `w* = R − ε`. -/
theorem mc_shift_eq (ε R : ℝ) :
    ∫ w', max (w' - R) 0 ∂(F.map fun w ↦ w + ε) = mcI F (R - ε) := by
  rw [integral_map (measurable_add_const ε).aemeasurable (by fun_prop), mcI]
  congr 1; funext w; congr 1; ring

/-- AKMM, p. 623: with offers `w + ε`, write the reservation wage as `R(ε) = w*(ε) + ε` where
`w*(ε) + ε − b − kI(w*(ε)) = 0`, `k = β/(1 − β(1 − σ))`. If `ε₁ < ε₂` and some offer is at least
`w*(ε₁)` with positive probability, then `0 < R(ε₂) − R(ε₁) < ε₂ − ε₁`: the reservation wage
rises, but by less than the offers. -/
theorem mc_shift_bounds (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) {k ε₁ ε₂ x₁ x₂ : ℝ} (hk : 0 < k)
    (h : ε₁ < ε₂) (h₁ : x₁ + ε₁ - b - k * mcI F x₁ = 0) (h₂ : x₂ + ε₂ - b - k * mcI F x₂ = 0)
    (hpos : 0 < F.real (Set.Ici x₁)) :
    0 < (x₂ + ε₂) - (x₁ + ε₁) ∧ (x₂ + ε₂) - (x₁ + ε₁) < ε₂ - ε₁ := by
  have hint : ∀ y, Integrable (fun w ↦ max (w - y) 0) F := fun y ↦
    Miao.Applications.od_integrable_of_continuous hF (by fun_prop)
  -- `I` is antitone with slope at least `F(w ≥ x)`: `I(y) − I(x) ≥ (x − y)F(w ≥ x)` for `y ≤ x`
  have hslope : ∀ y x : ℝ, y ≤ x → (x - y) * F.real (Set.Ici x) ≤ mcI F y - mcI F x := by
    intro y x hyx
    rw [mcI, mcI, ← integral_sub (hint y) (hint x), ← integral_indicator_one measurableSet_Ici,
      ← integral_const_mul]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Ici |>.const_mul _)
      ((hint y).sub (hint x)) fun w ↦ ?_
    by_cases hw : w ∈ Set.Ici x
    · rw [Set.indicator_of_mem hw, Pi.one_apply, mul_one]
      simp only [Set.mem_Ici] at hw
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [Set.indicator_of_notMem hw, mul_zero]
      have : max (w - x) 0 ≤ max (w - y) 0 := max_le_max (by linarith) le_rfl
      linarith
  have hanti : ∀ y x : ℝ, y ≤ x → mcI F x ≤ mcI F y := fun y x hyx ↦ by
    have := hslope y x hyx
    have : 0 ≤ (x - y) * F.real (Set.Ici x) := mul_nonneg (by linarith) measureReal_nonneg
    linarith
  -- `x₂ < x₁`
  have hx : x₂ < x₁ := by
    by_contra hc
    have hle := not_lt.mp hc
    have := hanti x₁ x₂ hle
    nlinarith
  have hs := hslope x₂ x₁ hx.le
  constructor
  · -- `ε₂ − ε₁ = (x₁ − x₂) + k(I(x₂) − I(x₁)) ≥ (x₁ − x₂)(1 + kF(w ≥ x₁))`
    have : (x₁ - x₂) * (k * F.real (Set.Ici x₁)) ≤ k * (mcI F x₂ - mcI F x₁) := by
      nlinarith
    have : 0 < (x₁ - x₂) * (k * F.real (Set.Ici x₁)) := by
      have := sub_pos.mpr hx; positivity
    nlinarith
  · linarith

/-- AKMM, p. 623: if the shifted reservation condition `w*(ε) + ε − b − kI(w*(ε)) = 0` holds for
`ε` near `0`, `w*` is differentiable at `0` and `F` has no atom at `w*(0)`, then
`d(w* + ε)/dε = kλ/(1 + kλ) ∈ (0, 1)` with `λ = 1 − F(w*)`; with `k = β/(1 − β(1 − σ))` this is
`β(1 − F(w*))/(1 − β(1 − σ) + β(1 − F(w*)))`. -/
theorem mc_shift_deriv (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 ≤ σ) {xs : ℝ → ℝ} {d : ℝ} (hxs : HasDerivAt xs d 0)
    (hroot : ∀ᶠ ε in 𝓝 0, xs ε + ε - b - β / (1 - β * (1 - σ)) * mcI F (xs ε) = 0)
    (hatom : F {xs 0} = 0) :
    HasDerivAt (fun ε ↦ xs ε + ε)
      (β * F.real (Set.Ioi (xs 0)) / (1 - β * (1 - σ) + β * F.real (Set.Ioi (xs 0)))) 0 ∧
    0 ≤ β * F.real (Set.Ioi (xs 0)) / (1 - β * (1 - σ) + β * F.real (Set.Ioi (xs 0))) ∧
    β * F.real (Set.Ioi (xs 0)) / (1 - β * (1 - σ) + β * F.real (Set.Ioi (xs 0))) < 1 := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  set k := β / (1 - β * (1 - σ)) with hk
  set L := F.real (Set.Ioi (xs 0)) with hL
  have hL0 : 0 ≤ L := measureReal_nonneg
  have hI := mc_I_hasDerivAt hF hatom
  -- differentiate the identity at `0`
  have hcomp : HasDerivAt (fun ε ↦ xs ε + ε - b - k * mcI F (xs ε))
      (d + 1 - k * (-L * d)) 0 := by
    have h1 := (hxs.add (hasDerivAt_id 0)).sub_const b
    have h2 := (hI.comp 0 hxs).const_mul k
    refine (h1.sub h2).congr_deriv ?_
    ring
  have hzero : HasDerivAt (fun ε ↦ xs ε + ε - b - k * mcI F (xs ε)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hroot
  have hd : d + 1 - k * (-L * d) = 0 := hcomp.unique hzero
  have hkL : 0 ≤ k * L := by positivity
  have hd' : d = -1 / (1 + k * L) := by
    rw [eq_div_iff (by linarith)]; linarith
  have hval : d + 1 = β * L / (1 - β * (1 - σ) + β * L) := by
    rw [hd', hk]; field_simp; ring
  refine ⟨(hxs.add (hasDerivAt_id 0)).congr_deriv (by rw [← hval]), ?_, ?_⟩
  · positivity
  · rw [div_lt_one (by positivity)]; linarith

end AKMM.FrictionalLaborMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Mean-preserving spreads, frictional wage dispersion

AKMM, §20.9, pp. 623–625. A mean-preserving spread is Sargent–Stachurski's
`SargentStachurski.AdditionalApplications.IsMPS` (`x̃ = x + z` with `E[z | x] = 0`), exactly the
book's definition.

* `mps_mean`: a mean-preserving spread has the same mean.
* `mps_ibp`: integration by parts, `∫_0^x F(t)dt = ∫max{x − w, 0}dF(w)` for offers in `[0, ∞)`
  (by Fubini); with it, (20.56) reads `∫max{x − w, 0}dG ≥ ∫max{x − w, 0}dF`.
* `eq_20_56_of_mps`: a mean-preserving spread satisfies (20.56) (Jensen, via Sargent–Stachurski's
  `integral_max_le_of_isMPS`); `eq_20_56_not_sufficient`: (20.56) alone does not give a
  mean-preserving spread (point masses at `0` and `1`): the equivalence cited from
  Mas-Colell–Whinston–Green needs equal means.
* `eq_20_57`, `eq_20_58`: `∫_{w > x}(w − x)dF = μ_w − x + ∫max{x − w, 0}dF`, and (20.55) is
  `w* − b − β/(1 − β(1 − σ))(μ_w − w* + ∫_0^{w*}F) = 0`, whose left side is strictly increasing
  (`eq_20_58_strictMono`).
* `mc_mps_reservation`: under a mean-preserving spread of the offer distribution the reservation
  wage rises (p. 624).
* Frictional wage dispersion (pp. 624–625): `mm_formula`: with `λ = 1 − F(w*)`,
  `w^M = ∫_{w > w*} w dF/λ`, `ρ = b/w^M`, the mean–min ratio is
  `Mm = w^M/w* = (1 + βλ/(1 − β(1 − σ)))/(ρ + βλ/(1 − β(1 − σ)))` (`mm_formula_of_bellman` from
  the Bellman equations); `mm_back_of_envelope`: at `β = 0.996`, `σ = 0.034`, `λ = 0.45`,
  `ρ = 0.4` the formula gives `Mm > 1.04`, not the printed `1.031`.

The converse of `eq_20_56_of_mps` (Rothschild–Stiglitz) is cited by the book and not formalised.
-/

namespace AKMM.FrictionalLaborMarkets

open MeasureTheory Filter Topology ProbabilityTheory

/-- AKMM, p. 623: a mean-preserving spread `G` of `F` has the same mean as `F`. -/
theorem mps_mean {ψ φ : Measure ℝ} (h : SargentStachurski.AdditionalApplications.IsMPS ψ φ) :
    ∫ x, x ∂ψ = ∫ x, x ∂φ := by
  obtain ⟨Ω, mΩ, P, _, W, Z, hWm, hZm, hWi, hZi, hW, hWZ, hZ⟩ := h
  have hm : MeasurableSpace.comap W (inferInstance : MeasurableSpace ℝ) ≤ mΩ := hWm.comap_le
  change ∫ x, id x ∂ψ = ∫ x, id x ∂φ
  rw [← hW, ← hWZ, integral_map (hWm.add hZm).aemeasurable aestronglyMeasurable_id,
    integral_map hWm.aemeasurable aestronglyMeasurable_id]
  have hZ0 : ∫ ω, Z ω ∂P = 0 := by
    rw [← integral_condExp hm (μ := P) (f := Z), integral_congr_ae hZ]
    simp
  simp only [id, Pi.add_apply]
  rw [integral_add hWi hZi, hZ0, add_zero]

/-- AKMM, (20.58), p. 624 (**integration by parts**): for offers in `[0, ∞)`,
`∫_0^x F(t)dt = ∫max{x − w, 0}dF(w)` (equivalently `∫_0^x(w − x)dF = −∫_0^x F(w)dw`). -/
theorem mps_ibp {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : ∀ᵐ w ∂μ, 0 ≤ w) (x : ℝ) :
    ∫ t in Set.Icc 0 x, μ.real (Set.Iic t) = ∫ w, max (x - w) 0 ∂μ := by
  set ν : Measure ℝ := volume.restrict (Set.Icc 0 x) with hν
  have : IsFiniteMeasure ν := by
    rw [hν]; exact isFiniteMeasure_restrict.mpr (by simp)
  set f : ℝ → ℝ → ℝ := fun w t ↦ (Set.Ici w).indicator (1 : ℝ → ℝ) t with hf
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    have : Function.uncurry f = {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (1 : ℝ × ℝ → ℝ) := by
      funext p
      simp only [Function.uncurry, hf, Set.indicator_apply, Set.mem_Ici, Pi.one_apply]
      rfl
    rw [this]
    exact (integrable_const (1 : ℝ)).indicator hS
  have inner_t : ∀ t, ∫ w, f w t ∂μ = μ.real (Set.Iic t) := by
    intro t
    have : (fun w ↦ f w t) = (Set.Iic t).indicator (1 : ℝ → ℝ) := by
      funext w
      simp only [hf, Set.indicator_apply, Set.mem_Ici, Set.mem_Iic, Pi.one_apply]
    rw [this, integral_indicator_one measurableSet_Iic]
  have inner_w : ∀ᵐ w ∂μ, ∫ t, f w t ∂ν = max (x - w) 0 := by
    filter_upwards [hμ] with w hw
    simp only [hf]
    have hset : Set.Ici w ∩ Set.Icc 0 x = Set.Icc w x := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hw.trans h1, h3⟩
    rw [integral_indicator_one measurableSet_Ici, hν, measureReal_restrict_apply measurableSet_Ici,
      hset, Real.volume_real_Icc]
  rw [← integral_congr_ae inner_w, integral_integral_swap hint]
  simp only [inner_t]

/-- AKMM, (20.56), p. 623: a mean-preserving spread `G` of `F` satisfies (20.56), in the form
`∫max{x − w, 0}dG ≥ ∫max{x − w, 0}dF` (which is `∫_0^x G ≥ ∫_0^x F` by `mps_ibp`). -/
theorem eq_20_56_of_mps {ψ φ : Measure ℝ} [IsProbabilityMeasure ψ] [IsProbabilityMeasure φ]
    (hiφ : Integrable id φ) (hiψ : Integrable id ψ)
    (h : SargentStachurski.AdditionalApplications.IsMPS ψ φ) (x : ℝ) :
    ∫ w, max (x - w) 0 ∂φ ≤ ∫ w, max (x - w) 0 ∂ψ := by
  have hmax := SargentStachurski.AdditionalApplications.integral_max_le_of_isMPS h x
  have hmean := mps_mean h
  have e : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → Integrable id μ →
      ∫ w, max (x - w) 0 ∂μ = ∫ w, max w x ∂μ - ∫ w, w ∂μ := by
    intro μ _ hi
    have h1 : Integrable (fun w ↦ max w x) μ := hi.sup (integrable_const x)
    have h2 : Integrable (fun w : ℝ ↦ w) μ := hi
    rw [← integral_sub h1 h2]
    congr 1; funext w
    rcases le_total w x with hw | hw
    · rw [max_eq_left (by linarith), max_eq_right hw]
    · rw [max_eq_right (by linarith), max_eq_left hw]; ring
  rw [e φ inferInstance hiφ, e ψ inferInstance hiψ, hmean]
  linarith

/-- AKMM, p. 623 (correction): (20.56) alone does not make `G` a mean-preserving spread of `F`.
With `F` the point mass at `1` and `G` the point mass at `0`, `∫max{x − w, 0}dG = max{x, 0} ≥
max{x − 1, 0} = ∫max{x − w, 0}dF` for all `x`, but the means differ. -/
theorem eq_20_56_not_sufficient :
    (∀ x : ℝ, ∫ w, max (x - w) 0 ∂(Measure.dirac (1 : ℝ)) ≤
      ∫ w, max (x - w) 0 ∂(Measure.dirac (0 : ℝ))) ∧
    ¬ SargentStachurski.AdditionalApplications.IsMPS (Measure.dirac (0 : ℝ))
      (Measure.dirac (1 : ℝ)) := by
  refine ⟨fun x ↦ ?_, fun h ↦ ?_⟩
  · rw [integral_dirac, integral_dirac]
    exact max_le_max (by linarith) le_rfl
  · have := mps_mean h
    rw [integral_dirac, integral_dirac] at this
    norm_num at this

/-- AKMM, (20.57), p. 624: `∫_{w > x}(w − x)dF = μ_w − x + ∫max{x − w, 0}dF`, `μ_w` the mean. -/
theorem eq_20_57 {μ : Measure ℝ} [IsProbabilityMeasure μ] (hi : Integrable id μ) (x : ℝ) :
    ∫ w in Set.Ioi x, (w - x) ∂μ = ∫ w, w ∂μ - x + ∫ w, max (x - w) 0 ∂μ := by
  rw [Miao.Applications.od_setIntegral_Ioi_eq]
  have e : (fun w ↦ max (w - x) 0) = fun w ↦ (w - x) + max (x - w) 0 := by
    funext w
    rcases le_total w x with hw | hw
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have h1 : Integrable (fun w : ℝ ↦ w) μ := hi
  have h2 : Integrable (fun w : ℝ ↦ w - x) μ := h1.sub (integrable_const x)
  have h3 : Integrable (fun w : ℝ ↦ max (x - w) 0) μ :=
    ((integrable_const x).sub h1).sup (integrable_const 0)
  rw [e, integral_add h2 h3, integral_sub h1 (integrable_const x), integral_const, probReal_univ,
    one_smul]

/-- AKMM, (20.58), p. 624: the reservation-wage equation (20.55) in the form
`w* − b − β/(1 − β(1 − σ))(μ_w − w* + ∫max{w* − w, 0}dF) = 0`. -/
theorem eq_20_58 {μ : Measure ℝ} [IsProbabilityMeasure μ] (hi : Integrable id μ) {b σ β x : ℝ} :
    mcG μ b σ β x =
      x - b - β / (1 - β * (1 - σ)) * (∫ w, w ∂μ - x + ∫ w, max (x - w) 0 ∂μ) := by
  rw [mcG, eq_20_57 hi]

/-- AKMM, p. 624: the left side of (20.58) is strictly increasing in `w*`. -/
theorem eq_20_58_strictMono {μ : Measure ℝ} [IsProbabilityMeasure μ] {B b σ β : ℝ}
    (hμ : ∀ᵐ z ∂μ, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) :
    StrictMono (mcG μ b σ β) := by
  have h := Miao.Applications.od_firingψ_strictMono (c := b) hμ hβ0 hβ1 hσ
  intro x y hxy
  rw [mc_G_eq, mc_G_eq]
  exact h hxy

/-- AKMM, p. 624: if the offer distribution `ψ` is a mean-preserving spread of `φ` (both on
`[0, w_u]`), the reservation wage under `ψ` is at least that under `φ`. -/
theorem mc_mps_reservation {φ ψ : Measure ℝ} [IsProbabilityMeasure φ] [IsProbabilityMeasure ψ]
    {B b σ β : ℝ} (hφ : ∀ᵐ z ∂φ, z ∈ Set.Icc 0 B) (hψ : ∀ᵐ z ∂ψ, z ∈ Set.Icc 0 B)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ)
    (h : SargentStachurski.AdditionalApplications.IsMPS ψ φ) {V₁ W₁ V₂ W₂ : ℝ → ℝ} {U₁ U₂ : ℝ}
    (hB₁ : Miao.Applications.od_FiringBellman φ B b σ β V₁ W₁ U₁)
    (hB₂ : Miao.Applications.od_FiringBellman ψ B b σ β V₂ W₂ U₂) :
    (1 - β) * U₁ ≤ (1 - β) * U₂ := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  set x₁ := (1 - β) * U₁
  have h1 : mcG φ b σ β x₁ = 0 := by
    rw [mcG]; exact (mc_root_unique hφ hβ0 hβ1 hσ hB₁ x₁).mpr rfl
  have h2 : mcG ψ b σ β ((1 - β) * U₂) = 0 := by
    rw [mcG]; exact (mc_root_unique hψ hβ0 hβ1 hσ hB₂ _).mpr rfl
  -- `I_ψ(x₁) ≥ I_φ(x₁)` by Sargent–Stachurski's (8.18)
  have hI : ∫ w in Set.Ioi x₁, (w - x₁) ∂φ ≤ ∫ w in Set.Ioi x₁, (w - x₁) ∂ψ := by
    rw [Miao.Applications.od_setIntegral_Ioi_eq, Miao.Applications.od_setIntegral_Ioi_eq]
    have hmax := SargentStachurski.AdditionalApplications.integral_max_le_of_isMPS h x₁
    have e : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → (∀ᵐ z ∂μ, z ∈ Set.Icc 0 B) →
        ∫ w, max (w - x₁) 0 ∂μ = ∫ w, max w x₁ ∂μ - x₁ := by
      intro μ _ hμ
      have hint : Integrable (fun w ↦ max w x₁) μ :=
        Miao.Applications.od_integrable_of_continuous hμ (by fun_prop)
      have ef : (fun w ↦ max (w - x₁) 0) = fun w ↦ max w x₁ - x₁ := by
        funext w
        rcases le_total w x₁ with hw | hw
        · rw [max_eq_right (by linarith), max_eq_right hw]; ring
        · rw [max_eq_left (by linarith), max_eq_left hw]
      rw [ef, integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [e φ inferInstance hφ, e ψ inferInstance hψ]
    linarith
  have hle : mcG ψ b σ β x₁ ≤ mcG ψ b σ β ((1 - β) * U₂) := by
    rw [h2]; unfold mcG at h1 ⊢
    have : 0 ≤ β / (1 - β * (1 - σ)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hI this]
  exact (eq_20_58_strictMono hψ hβ0 hβ1 hσ).le_iff_le.mp hle

/-- AKMM, p. 625: the mean–min ratio. If `w* = b + k(λw^M − λw*)` (which is (20.55) with
`∫_{w > w*}(w − w*)dF = λ(w^M − w*)`, `k = β/(1 − β(1 − σ))`), `w*, w^M > 0` and `kλ ≥ 0`, then
`Mm = w^M/w* = (1 + kλ)/(ρ + kλ)` with `ρ = b/w^M`. -/
theorem mm_formula {b k lam wM ws : ℝ} (hwM : 0 < wM) (hws : 0 < ws) (hkl : 0 ≤ k * lam)
    (h : ws = b + k * (lam * wM - lam * ws)) :
    wM / ws = (1 + k * lam) / (b / wM + k * lam) := by
  have hden : b / wM + k * lam = ws * (1 + k * lam) / wM := by
    rw [eq_div_iff hwM.ne']; field_simp; linarith
  rw [hden]
  have : 0 < 1 + k * lam := by linarith
  field_simp

/-- AKMM, pp. 624–625: from the Bellman equations, with `λ = 1 − F(w*) > 0`,
`w^M = ∫_{w > w*} w dF/λ > 0` and `ρ = b/w^M`, the mean–min ratio is
`w^M/w* = (1 + βλ/(1 − β(1 − σ)))/(ρ + βλ/(1 − β(1 − σ)))`. -/
theorem mm_formula_of_bellman {F : Measure ℝ} [IsProbabilityMeasure F] {B b σ β : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 ≤ σ) (hb : 0 < b)
    {V W : ℝ → ℝ} {U : ℝ} (hB : Miao.Applications.od_FiringBellman F B b σ β V W U)
    (hlam : 0 < F.real (Set.Ioi ((1 - β) * U)))
    (hwM : 0 < (∫ w in Set.Ioi ((1 - β) * U), w ∂F) / F.real (Set.Ioi ((1 - β) * U))) :
    (∫ w in Set.Ioi ((1 - β) * U), w ∂F) / F.real (Set.Ioi ((1 - β) * U)) / ((1 - β) * U) =
      (1 + β / (1 - β * (1 - σ)) * F.real (Set.Ioi ((1 - β) * U))) /
        (b / ((∫ w in Set.Ioi ((1 - β) * U), w ∂F) / F.real (Set.Ioi ((1 - β) * U))) +
          β / (1 - β * (1 - σ)) * F.real (Set.Ioi ((1 - β) * U))) := by
  have hD := mc_D_pos hβ0 hβ1 hσ
  set ws := (1 - β) * U with hws
  set lam := F.real (Set.Ioi ws)
  set wM := (∫ w in Set.Ioi ws, w ∂F) / lam with hwMdef
  have hU := mc_U_pos hF hβ0 hβ1 hσ hb hB
  have hwsp : 0 < ws := mul_pos (by linarith) hU.2
  have h55 := eq_20_55 hF hβ0 hβ1 hσ hB
  have hi : Integrable (fun w : ℝ ↦ w) F :=
    Miao.Applications.od_integrable_of_continuous hF continuous_id
  have hsplit : ∫ w in Set.Ioi ws, (w - ws) ∂F = lam * wM - lam * ws := by
    rw [integral_sub hi.integrableOn (integrable_const ws), setIntegral_const, smul_eq_mul,
      hwMdef]
    field_simp
    ring
  rw [hsplit] at h55
  exact mm_formula hwM hwsp (by positivity) h55

/-- AKMM, p. 625: the back-of-the-envelope calculation. With `β = 0.996`, `σ = 0.034`,
`λ = 0.45` and `ρ = 0.4`, the formula gives `Mm > 1.04` (about `1.049`), not the printed
`1.031`. -/
theorem mm_back_of_envelope :
    let k : ℝ := 0.996 / (1 - 0.996 * (1 - 0.034))
    1.04 < (1 + k * 0.45) / (0.4 + k * 0.45) ∧ (1 + k * 0.45) / (0.4 + k * 0.45) ≠ 1.031 := by
  norm_num

end AKMM.FrictionalLaborMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Diamond paradox

AKMM, §20.9, p. 621 (stated verbally, after Diamond 1971). `n ≥ 1` identical firms post wages
`w : Fin n → ℝ`; a worker produces `p` and has reservation value `b < p`; searching again costs
`s > 0`. A firm meets the worker with probability `1/n` and earns `p − w_i` if the worker accepts.

The worker side is described by the two properties of optimal sequential search with cost `s`
used in the book's argument (`DiamondWorker`): offers below `b` are rejected, and an offer
`w_i ≥ b` within `s` of the best offer `max_j w_j` is accepted (one more search costs `s` and can
raise the wage by less than `s`). `diamondAccept` is a concrete such rule.

* `diamond_ne`: everyone offering the reservation wage `b` is a Nash equilibrium ("no firm would
  want to deviate as offering a higher wage does not make it more likely that the firm will hire
  a worker").
* `diamond_unique`: it is the only Nash equilibrium: in any other profile the highest-wage firm
  gains by cutting its wage slightly without losing the worker, or a firm whose offer is rejected
  gains by offering `b`.
* `diamond_paradox`: hence for every search cost `s > 0`, however small, the unique equilibrium
  wage is `b`.

Departure: the book's argument is verbal; the formalisation makes the game explicit, with the
worker's behaviour summarised by the two properties above.
-/

namespace AKMM.FrictionalLaborMarkets

/-- AKMM, p. 621: a worker's acceptance rule with reservation value `b` and search cost `s`:
offers below `b` are rejected, and an offer `w_i ≥ b` with `w_j − s < w_i` for every `j` is
accepted. -/
structure DiamondWorker (n : ℕ) (b s : ℝ) where
  /-- whether the worker accepts firm `i`'s offer under the wage profile `w` -/
  acc : (Fin n → ℝ) → Fin n → Prop
  /-- offers below the reservation value are rejected -/
  reject_low : ∀ w i, w i < b → ¬ acc w i
  /-- offers that searching again (at cost `s`) cannot beat are accepted -/
  accept_high : ∀ w i, b ≤ w i → (∀ j, w j - s < w i) → acc w i

/-- A concrete acceptance rule: accept `w_i` iff `w_i ≥ b` and `w_i > w_j − s` for all `j`. -/
def diamondAccept (n : ℕ) (b s : ℝ) : DiamondWorker n b s where
  acc w i := b ≤ w i ∧ ∀ j, w j - s < w i
  reject_low _ _ h h' := absurd h'.1 (not_le.mpr h)
  accept_high _ _ h h' := ⟨h, h'⟩

/-- Firm `i`'s expected profit `(p − w_i)/n` if the worker accepts its offer, `0` otherwise. -/
noncomputable def diamondProfit {n : ℕ} {b s : ℝ} (A : DiamondWorker n b s) (p : ℝ)
    (w : Fin n → ℝ) (i : Fin n) : ℝ := by
  classical exact if A.acc w i then (p - w i) / n else 0

/-- A wage profile is a Nash equilibrium if no firm gains by changing its own wage. -/
def DiamondNE {n : ℕ} {b s : ℝ} (A : DiamondWorker n b s) (p : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ i (w' : ℝ), diamondProfit A p (Function.update w i w') i ≤ diamondProfit A p w i

/-- When the worker accepts firm `i`'s offer, its profit is `(p − w_i)/n`. -/
theorem diamond_profit_acc {n : ℕ} {b s : ℝ} (A : DiamondWorker n b s) (p : ℝ) {w : Fin n → ℝ}
    {i : Fin n} (h : A.acc w i) : diamondProfit A p w i = (p - w i) / n := by
  classical
  unfold diamondProfit
  simp [h]

/-- Profit is zero when the offer is rejected. -/
theorem diamond_profit_rej {n : ℕ} {b s : ℝ} (A : DiamondWorker n b s) (p : ℝ) {w : Fin n → ℝ}
    {i : Fin n} (h : ¬ A.acc w i) : diamondProfit A p w i = 0 := by
  classical
  unfold diamondProfit
  simp [h]

/-- AKMM, p. 621: when all firms offer the reservation wage `b`, no firm gains by deviating. -/
theorem diamond_ne {n : ℕ} {b s p : ℝ} (A : DiamondWorker n b s) (hs : 0 < s) (hbp : b < p) :
    DiamondNE A p (fun _ ↦ b) := by
  intro i w'
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hacc : A.acc (fun _ ↦ b) i := A.accept_high _ _ le_rfl fun _ ↦ by linarith
  rw [diamond_profit_acc A p hacc]
  by_cases h : A.acc (Function.update (fun _ ↦ b) i w') i
  · rw [diamond_profit_acc A p h, Function.update_self]
    have hw' : b ≤ w' := by
      by_contra hc
      exact A.reject_low _ i (by rw [Function.update_self]; exact not_le.mp hc) h
    exact div_le_div_of_nonneg_right (by linarith) hn
  · rw [diamond_profit_rej A p h]
    exact div_nonneg (by linarith) hn

/-- AKMM, p. 621: the equilibrium is unique: in every Nash equilibrium every firm offers the
reservation wage `b`. -/
theorem diamond_unique {n : ℕ} {b s p : ℝ} (A : DiamondWorker n b s) (hs : 0 < s) (hbp : b < p)
    {w : Fin n → ℝ} (hNE : DiamondNE A p w) (i : Fin n) : w i = b := by
  classical
  have hn0 : 0 < n := Fin.pos i
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ w ⟨i, Finset.mem_univ i⟩
  have hk' : ∀ j, w j ≤ w k := fun j ↦ hk j (Finset.mem_univ j)
  -- step 1: the highest wage is at most `b`
  have hmax : w k ≤ b := by
    by_contra hc
    have hc : b < w k := not_le.mp hc
    set ε := min s (w k - b) / 2 with hε
    have hε0 : 0 < ε := by
      have : 0 < min s (w k - b) := lt_min hs (by linarith)
      positivity
    have hεs : ε < s := by
      have := min_le_left s (w k - b); linarith
    have hεb : ε ≤ w k - b := by
      have := min_le_right s (w k - b)
      have : 0 ≤ min s (w k - b) := by positivity
      linarith
    have hacc : A.acc w k := A.accept_high w k hc.le fun j ↦ by have := hk' j; linarith
    have hacc' : A.acc (Function.update w k (w k - ε)) k := by
      refine A.accept_high _ k (by rw [Function.update_self]; linarith) fun j ↦ ?_
      rw [Function.update_self]
      by_cases hj : j = k
      · subst hj; rw [Function.update_self]; linarith
      · rw [Function.update_of_ne hj]; have := hk' j; linarith
    have := hNE k (w k - ε)
    rw [diamond_profit_acc A p hacc', diamond_profit_acc A p hacc, Function.update_self] at this
    have := (div_le_div_iff_of_pos_right hn).mp this
    linarith
  -- step 2: every wage is at least `b`
  have hge : b ≤ w i := by
    by_contra hc
    have hc : w i < b := not_le.mp hc
    have hrej : ¬ A.acc w i := A.reject_low w i hc
    have hacc' : A.acc (Function.update w i b) i := by
      refine A.accept_high _ i (by rw [Function.update_self]) fun j ↦ ?_
      rw [Function.update_self]
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; linarith
      · rw [Function.update_of_ne hj]; have := hk' j; linarith
    have := hNE i b
    rw [diamond_profit_acc A p hacc', diamond_profit_rej A p hrej, Function.update_self] at this
    have : 0 < (p - b) / n := div_pos (by linarith) hn
    linarith
  have := hk' i
  linarith

/-- AKMM, p. 621 (**the Diamond paradox**): for every search cost `s > 0`, however small, the
wage profiles that are Nash equilibria are exactly the one where every firm offers the
reservation wage `b`. -/
theorem diamond_paradox {n : ℕ} {b p : ℝ} (hbp : b < p) (s : ℝ) (hs : 0 < s)
    (A : DiamondWorker n b s) (w : Fin n → ℝ) : DiamondNE A p w ↔ w = fun _ ↦ b := by
  constructor
  · intro h; funext i; exact diamond_unique A hs hbp h i
  · rintro rfl; exact diamond_ne A hs hbp

/-- The concrete acceptance rule `diamondAccept` instantiates `diamond_paradox`. -/
theorem diamond_paradox_example {n : ℕ} {b p s : ℝ} (hbp : b < p) (hs : 0 < s)
    (w : Fin n → ℝ) : DiamondNE (diamondAccept n b s) p w ↔ w = fun _ ↦ b :=
  diamond_paradox hbp s hs _ w

end AKMM.FrictionalLaborMarkets

set_option linter.style.longLine false
#print axioms AKMM.FrictionalLaborMarkets.lakeNext
#print axioms AKMM.FrictionalLaborMarkets.eq_20_1
#print axioms AKMM.FrictionalLaborMarkets.eq_20_2
#print axioms AKMM.FrictionalLaborMarkets.lake_ubar_anti_lam
#print axioms AKMM.FrictionalLaborMarkets.lake_ubar_mono_sigma
#print axioms AKMM.FrictionalLaborMarkets.lake_diff
#print axioms AKMM.FrictionalLaborMarkets.lake_gap
#print axioms AKMM.FrictionalLaborMarkets.lake_abs_lt_one
#print axioms AKMM.FrictionalLaborMarkets.lake_abs_eq_zero_example
#print axioms AKMM.FrictionalLaborMarkets.lake_isContraction
#print axioms AKMM.FrictionalLaborMarkets.lake_globallyStable
#print axioms AKMM.FrictionalLaborMarkets.lake_closed_form
#print axioms AKMM.FrictionalLaborMarkets.lake_tendsto
#print axioms AKMM.FrictionalLaborMarkets.lake_cauchy
#print axioms AKMM.FrictionalLaborMarkets.lake_duration_series
#print axioms AKMM.FrictionalLaborMarkets.lake_duration_recursion
#print axioms AKMM.FrictionalLaborMarkets.MatchFn
#print axioms AKMM.FrictionalLaborMarkets.MatchFn.mk
#print axioms AKMM.FrictionalLaborMarkets.MatchFn.M
#print axioms AKMM.FrictionalLaborMarkets.MatchFn.pos
#print axioms AKMM.FrictionalLaborMarkets.MatchFn.homog
#print axioms AKMM.FrictionalLaborMarkets.MatchFn.mono_u
#print axioms AKMM.FrictionalLaborMarkets.MatchFn.mono_v
#print axioms AKMM.FrictionalLaborMarkets.MatchFn.Bounded
#print axioms AKMM.FrictionalLaborMarkets.MatchFn.ofMiao
#print axioms AKMM.FrictionalLaborMarkets.lamW
#print axioms AKMM.FrictionalLaborMarkets.lamF
#print axioms AKMM.FrictionalLaborMarkets.match_rate_worker
#print axioms AKMM.FrictionalLaborMarkets.match_rate_firm
#print axioms AKMM.FrictionalLaborMarkets.eq_20_3
#print axioms AKMM.FrictionalLaborMarkets.match_lamW_eq
#print axioms AKMM.FrictionalLaborMarkets.match_lamW_pos
#print axioms AKMM.FrictionalLaborMarkets.match_lamF_pos
#print axioms AKMM.FrictionalLaborMarkets.match_lamW_strictMonoOn
#print axioms AKMM.FrictionalLaborMarkets.match_lamF_strictAntiOn
#print axioms AKMM.FrictionalLaborMarkets.match_lamW_le_one
#print axioms AKMM.FrictionalLaborMarkets.match_lamF_le_one
#print axioms AKMM.FrictionalLaborMarkets.eq_20_4
#print axioms AKMM.FrictionalLaborMarkets.eq_20_5
#print axioms AKMM.FrictionalLaborMarkets.eq_20_6
#print axioms AKMM.FrictionalLaborMarkets.skewMatch
#print axioms AKMM.FrictionalLaborMarkets.skewMatch_bounded
#print axioms AKMM.FrictionalLaborMarkets.eq_20_6_misprint
#print axioms AKMM.FrictionalLaborMarkets.match_bc_strictMonoOn
#print axioms AKMM.FrictionalLaborMarkets.match_ubar_unique
#print axioms AKMM.FrictionalLaborMarkets.match_ubar_exists
#print axioms AKMM.FrictionalLaborMarkets.match_beveridge_anti
#print axioms AKMM.FrictionalLaborMarkets.match_euler
#print axioms AKMM.FrictionalLaborMarkets.matchElast
#print axioms AKMM.FrictionalLaborMarkets.match_M2
#print axioms AKMM.FrictionalLaborMarkets.match_elast_eq
#print axioms AKMM.FrictionalLaborMarkets.cdMatch
#print axioms AKMM.FrictionalLaborMarkets.eq_20_23
#print axioms AKMM.FrictionalLaborMarkets.cd_lamF_hasDerivAt
#print axioms AKMM.FrictionalLaborMarkets.cd_not_bounded
#print axioms AKMM.FrictionalLaborMarkets.dmpEx
#print axioms AKMM.FrictionalLaborMarkets.dmp_ex_add
#print axioms AKMM.FrictionalLaborMarkets.dmp_ex_mul
#print axioms AKMM.FrictionalLaborMarkets.dmp_ex_congr
#print axioms AKMM.FrictionalLaborMarkets.eq_20_10
#print axioms AKMM.FrictionalLaborMarkets.eq_20_15
#print axioms AKMM.FrictionalLaborMarkets.eq_20_A_1
#print axioms AKMM.FrictionalLaborMarkets.dmp_J_div
#print axioms AKMM.FrictionalLaborMarkets.eq_20_16
#print axioms AKMM.FrictionalLaborMarkets.eq_20_A_2
#print axioms AKMM.FrictionalLaborMarkets.dmpSurplus
#print axioms AKMM.FrictionalLaborMarkets.eq_20_18
#print axioms AKMM.FrictionalLaborMarkets.eq_20_19
#print axioms AKMM.FrictionalLaborMarkets.jcLHS
#print axioms AKMM.FrictionalLaborMarkets.jcRHS
#print axioms AKMM.FrictionalLaborMarkets.jcPhi
#print axioms AKMM.FrictionalLaborMarkets.ss_phi_eq
#print axioms AKMM.FrictionalLaborMarkets.eq_20_17
#print axioms AKMM.FrictionalLaborMarkets.ss_phi_strictAntiOn
#print axioms AKMM.FrictionalLaborMarkets.ss_unique
#print axioms AKMM.FrictionalLaborMarkets.ss_exists
#print axioms AKMM.FrictionalLaborMarkets.ss_exists_of_tendsto
#print axioms AKMM.FrictionalLaborMarkets.ss_cd_lamF_limits
#print axioms AKMM.FrictionalLaborMarkets.ss_cd_existsUnique
#print axioms AKMM.FrictionalLaborMarkets.ss_theta_mono_z
#print axioms AKMM.FrictionalLaborMarkets.ss_ubar_strictAntiOn
#print axioms AKMM.FrictionalLaborMarkets.ss_vbar_strictMonoOn
#print axioms AKMM.FrictionalLaborMarkets.fn6_lhs_hasDerivAt
#print axioms AKMM.FrictionalLaborMarkets.fn6_rhs_hasDerivAt
#print axioms AKMM.FrictionalLaborMarkets.fn6_rhs_strictMonoOn
#print axioms AKMM.FrictionalLaborMarkets.ss_lhs_strictMonoOn
#print axioms AKMM.FrictionalLaborMarkets.fn6_next_strictMono
#print axioms AKMM.FrictionalLaborMarkets.fn7_slope
#print axioms AKMM.FrictionalLaborMarkets.fn7_slope_gt_one
#print axioms AKMM.FrictionalLaborMarkets.fn7_slope_eq
#print axioms AKMM.FrictionalLaborMarkets.fn7_step_above
#print axioms AKMM.FrictionalLaborMarkets.fn7_step_below
#print axioms AKMM.FrictionalLaborMarkets.fn7_diverge_above
#print axioms AKMM.FrictionalLaborMarkets.fn7_diverge_below
#print axioms AKMM.FrictionalLaborMarkets.fn7_jump
#print axioms AKMM.FrictionalLaborMarkets.planner_foc_theta
#print axioms AKMM.FrictionalLaborMarkets.planner_foc_u
#print axioms AKMM.FrictionalLaborMarkets.eq_20_A_3
#print axioms AKMM.FrictionalLaborMarkets.eq_20_A_2_misprint
#print axioms AKMM.FrictionalLaborMarkets.eq_20_20
#print axioms AKMM.FrictionalLaborMarkets.eq_20_22
#print axioms AKMM.FrictionalLaborMarkets.hosios_node
#print axioms AKMM.FrictionalLaborMarkets.hosios
#print axioms AKMM.FrictionalLaborMarkets.hosios_necessary
#print axioms AKMM.FrictionalLaborMarkets.hosios_cd_partials
#print axioms AKMM.FrictionalLaborMarkets.hosios_cd
#print axioms AKMM.FrictionalLaborMarkets.hosios_nonCRS
#print axioms AKMM.FrictionalLaborMarkets.hosios_nonCRS_example
#print axioms AKMM.FrictionalLaborMarkets.ll_rpow_exp
#print axioms AKMM.FrictionalLaborMarkets.llL
#print axioms AKMM.FrictionalLaborMarkets.llR
#print axioms AKMM.FrictionalLaborMarkets.ll_lhs_eq
#print axioms AKMM.FrictionalLaborMarkets.ll_rhs_eq
#print axioms AKMM.FrictionalLaborMarkets.eq_20_25
#print axioms AKMM.FrictionalLaborMarkets.eq_20_25_misprint
#print axioms AKMM.FrictionalLaborMarkets.ll_undetermined
#print axioms AKMM.FrictionalLaborMarkets.llCoeff
#print axioms AKMM.FrictionalLaborMarkets.eq_20_26
#print axioms AKMM.FrictionalLaborMarkets.eq_20_26_printed_B
#print axioms AKMM.FrictionalLaborMarkets.ll_gap_pos
#print axioms AKMM.FrictionalLaborMarkets.ll_cs_kappa
#print axioms AKMM.FrictionalLaborMarkets.ll_cs_gamma
#print axioms AKMM.FrictionalLaborMarkets.ll_rpow_mul_strictMono
#print axioms AKMM.FrictionalLaborMarkets.ll_cs_eta
#print axioms AKMM.FrictionalLaborMarkets.ll_cs_eta_counterexample
#print axioms AKMM.FrictionalLaborMarkets.ll_cs_chi
#print axioms AKMM.FrictionalLaborMarkets.ll_cs_rho
#print axioms AKMM.FrictionalLaborMarkets.ll_cs_beta
#print axioms AKMM.FrictionalLaborMarkets.ll_cs_sigma
#print axioms AKMM.FrictionalLaborMarkets.eq_20_27_deriv
#print axioms AKMM.FrictionalLaborMarkets.eq_20_27
#print axioms AKMM.FrictionalLaborMarkets.ll_rigid_gt
#print axioms AKMM.FrictionalLaborMarkets.eq_20_A_4_example
#print axioms AKMM.FrictionalLaborMarkets.eq_20_28
#print axioms AKMM.FrictionalLaborMarkets.es_J_div
#print axioms AKMM.FrictionalLaborMarkets.eq_20_29
#print axioms AKMM.FrictionalLaborMarkets.es_foc_cd
#print axioms AKMM.FrictionalLaborMarkets.eq_20_31
#print axioms AKMM.FrictionalLaborMarkets.eq_20_32
#print axioms AKMM.FrictionalLaborMarkets.es_ss_foc
#print axioms AKMM.FrictionalLaborMarkets.es_bracket_cd
#print axioms AKMM.FrictionalLaborMarkets.esR
#print axioms AKMM.FrictionalLaborMarkets.eq_20_A_5_deriv
#print axioms AKMM.FrictionalLaborMarkets.eq_20_A_5_misprint
#print axioms AKMM.FrictionalLaborMarkets.eq_20_A_6
#print axioms AKMM.FrictionalLaborMarkets.es_G
#print axioms AKMM.FrictionalLaborMarkets.es_std_ratio
#print axioms AKMM.FrictionalLaborMarkets.es_lamW_loglinear
#print axioms AKMM.FrictionalLaborMarkets.es_rigid_cancel
#print axioms AKMM.FrictionalLaborMarkets.es_rigid_G
#print axioms AKMM.FrictionalLaborMarkets.es_nash_no_cancel
#print axioms AKMM.FrictionalLaborMarkets.ngm_rental
#print axioms AKMM.FrictionalLaborMarkets.ngm_y
#print axioms AKMM.FrictionalLaborMarkets.ngmDividend
#print axioms AKMM.FrictionalLaborMarkets.ngm_resource
#print axioms AKMM.FrictionalLaborMarkets.eq_20_36
#print axioms AKMM.FrictionalLaborMarkets.ngm_arrow_foc
#print axioms AKMM.FrictionalLaborMarkets.ngm_asset_value
#print axioms AKMM.FrictionalLaborMarkets.eq_20_42
#print axioms AKMM.FrictionalLaborMarkets.eq_20_43
#print axioms AKMM.FrictionalLaborMarkets.eq_20_44
#print axioms AKMM.FrictionalLaborMarkets.eq_20_45
#print axioms AKMM.FrictionalLaborMarkets.eq_20_48
#print axioms AKMM.FrictionalLaborMarkets.ngm_calib_u
#print axioms AKMM.FrictionalLaborMarkets.ngm_calib_r
#print axioms AKMM.FrictionalLaborMarkets.ngm_calib_K
#print axioms AKMM.FrictionalLaborMarkets.ngm_calib_K_misprint
#print axioms AKMM.FrictionalLaborMarkets.ngm_calib_kappa
#print axioms AKMM.FrictionalLaborMarkets.ngm_calib_kappa_misprint
#print axioms AKMM.FrictionalLaborMarkets.ngm_calib_w
#print axioms AKMM.FrictionalLaborMarkets.ngm_rigid_max_profit
#print axioms AKMM.FrictionalLaborMarkets.ngm_rigid_min_profit
#print axioms AKMM.FrictionalLaborMarkets.mcI
#print axioms AKMM.FrictionalLaborMarkets.eq_20_53
#print axioms AKMM.FrictionalLaborMarkets.mc_D_pos
#print axioms AKMM.FrictionalLaborMarkets.eq_20_51
#print axioms AKMM.FrictionalLaborMarkets.mc_W_strictMono
#print axioms AKMM.FrictionalLaborMarkets.mc_U_pos
#print axioms AKMM.FrictionalLaborMarkets.mc_W0_lt
#print axioms AKMM.FrictionalLaborMarkets.mc_exists_unique
#print axioms AKMM.FrictionalLaborMarkets.mc_reservation
#print axioms AKMM.FrictionalLaborMarkets.eq_20_55
#print axioms AKMM.FrictionalLaborMarkets.mc_root_unique
#print axioms AKMM.FrictionalLaborMarkets.mc_lambda_antitone
#print axioms AKMM.FrictionalLaborMarkets.mcG
#print axioms AKMM.FrictionalLaborMarkets.mc_G_eq
#print axioms AKMM.FrictionalLaborMarkets.mc_cs_b
#print axioms AKMM.FrictionalLaborMarkets.mc_coef_strictMono
#print axioms AKMM.FrictionalLaborMarkets.mc_cs_beta
#print axioms AKMM.FrictionalLaborMarkets.mc_cs_sigma
#print axioms AKMM.FrictionalLaborMarkets.mc_G_partials
#print axioms AKMM.FrictionalLaborMarkets.mc_pointwise
#print axioms AKMM.FrictionalLaborMarkets.mc_I_hasDerivAt
#print axioms AKMM.FrictionalLaborMarkets.mc_G_w
#print axioms AKMM.FrictionalLaborMarkets.mc_shift_eq
#print axioms AKMM.FrictionalLaborMarkets.mc_shift_bounds
#print axioms AKMM.FrictionalLaborMarkets.mc_shift_deriv
#print axioms AKMM.FrictionalLaborMarkets.mps_mean
#print axioms AKMM.FrictionalLaborMarkets.mps_ibp
#print axioms AKMM.FrictionalLaborMarkets.eq_20_56_of_mps
#print axioms AKMM.FrictionalLaborMarkets.eq_20_56_not_sufficient
#print axioms AKMM.FrictionalLaborMarkets.eq_20_57
#print axioms AKMM.FrictionalLaborMarkets.eq_20_58
#print axioms AKMM.FrictionalLaborMarkets.eq_20_58_strictMono
#print axioms AKMM.FrictionalLaborMarkets.mc_mps_reservation
#print axioms AKMM.FrictionalLaborMarkets.mm_formula
#print axioms AKMM.FrictionalLaborMarkets.mm_formula_of_bellman
#print axioms AKMM.FrictionalLaborMarkets.mm_back_of_envelope
#print axioms AKMM.FrictionalLaborMarkets.DiamondWorker
#print axioms AKMM.FrictionalLaborMarkets.DiamondWorker.mk
#print axioms AKMM.FrictionalLaborMarkets.DiamondWorker.acc
#print axioms AKMM.FrictionalLaborMarkets.DiamondWorker.reject_low
#print axioms AKMM.FrictionalLaborMarkets.DiamondWorker.accept_high
#print axioms AKMM.FrictionalLaborMarkets.diamondAccept
#print axioms AKMM.FrictionalLaborMarkets.diamondProfit
#print axioms AKMM.FrictionalLaborMarkets.DiamondNE
#print axioms AKMM.FrictionalLaborMarkets.diamond_profit_acc
#print axioms AKMM.FrictionalLaborMarkets.diamond_profit_rej
#print axioms AKMM.FrictionalLaborMarkets.diamond_ne
#print axioms AKMM.FrictionalLaborMarkets.diamond_unique
#print axioms AKMM.FrictionalLaborMarkets.diamond_paradox
#print axioms AKMM.FrictionalLaborMarkets.diamond_paradox_example

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.DMMatching
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Order.IntermediateValue

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

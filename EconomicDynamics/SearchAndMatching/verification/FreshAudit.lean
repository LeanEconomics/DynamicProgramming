import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Probability.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §18.1: the matching function, job-filling and job-finding rates, the Beveridge curve

Miao, §18.1, pp. 588–589 and p. 593. The matching function `M(u, v)` is increasing in both
arguments, concave and linearly homogeneous (`DMMatchingFn`; positivity of `M` on the open
orthant is also assumed). Departures: the properties are imposed on the open orthant
`u, v > 0`, where the rates are defined; "increasing" is read as strictly increasing.

* `dm_q`, `eq_18_1`: the job-filling rate `q^v = M(u, v)/v = q(θ)` and the job-finding rate
  `q^u = M(u, v)/u = q(θ)θ`, `θ = v/u` (18.1); `dm_jobFinding`: `θq(θ) = M(1, θ)`.
* `dm_q_strictAntiOn`, `dm_jobFinding_strictMonoOn`: a tighter market makes it harder for a firm
  to meet a worker and easier for a worker to find a job.
* `dm_q_hasDerivAt`, `dm_q_elasticity`, `dm_xi_mem`: if `M` is differentiable in `u`,
  `q′(θ) < 0` and the elasticity `d ln q/d ln θ = θq′/q ∈ (−1, 0)`; equivalently
  `ξ(θ) = −θq′(θ)/q(θ) ∈ (0, 1)` (p. 595). These follow from concavity and strict monotonicity
  alone (no differentiability in `v` is needed).
* `dm_jobFinding_hasDerivAt`: `(θq(θ))′ = q(θ)(1 − ξ(θ))`.
* `dm_beveridge_anti`, `dm_beveridge_convex`: the Beveridge curve `ρ(1 − u) = M(u, v)` (18.19)
  is downward sloping and convex (p. 593).
* Cobb–Douglas `M(u, v) = μu^αv^{1−α}` is a matching function (`dm_cdMatching`), with
  `q(θ) = μθ^{−α}` (`dm_cd_q`) and `ξ(θ) = α` (`dm_cd_xi`).
-/

namespace Miao.SearchAndMatching

open Filter Topology

/-- Miao, §18.1, p. 589: a **matching function** `M(u, v)` (matches from `u` unemployed workers
and `v` vacancies), positive, linearly homogeneous, strictly increasing in both arguments and
jointly concave on the open orthant. -/
structure DMMatchingFn where
  /-- the matching function `M(u, v)` -/
  M : ℝ → ℝ → ℝ
  /-- `M > 0` on the open orthant -/
  pos : ∀ u v : ℝ, 0 < u → 0 < v → 0 < M u v
  /-- linear homogeneity -/
  homog : ∀ t u v : ℝ, 0 < t → 0 < u → 0 < v → M (t * u) (t * v) = t * M u v
  /-- strictly increasing in `u` -/
  mono_u : ∀ u u' v : ℝ, 0 < u → u < u' → 0 < v → M u v < M u' v
  /-- strictly increasing in `v` -/
  mono_v : ∀ u v v' : ℝ, 0 < u → 0 < v → v < v' → M u v < M u v'
  /-- joint concavity -/
  concave : ConcaveOn ℝ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) (fun p : ℝ × ℝ ↦ M p.1 p.2)

/-- Miao, (18.1), p. 589: the **job-filling rate** as a function of market tightness,
`q(θ) = M(1/θ, 1)`. -/
noncomputable def dm_q (MF : DMMatchingFn) (θ : ℝ) : ℝ := MF.M θ⁻¹ 1

/-- Miao, p. 595: the elasticity `ξ(θ) = −θq′(θ)/q(θ)`. -/
noncomputable def dm_xi (MF : DMMatchingFn) (θ : ℝ) : ℝ :=
  -θ * deriv (dm_q MF) θ / dm_q MF θ

/-- Miao, p. 589: `M(u, v) = v q(v/u)` (linear homogeneity). -/
theorem dm_M_eq_mul_q (MF : DMMatchingFn) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    MF.M u v = v * dm_q MF (v / u) := by
  have h := MF.homog v (u / v) 1 hv (div_pos hu hv) one_pos
  have e : v * (u / v) = u := by field_simp
  rw [e, mul_one] at h
  rw [dm_q, inv_div]
  exact h

/-- Miao, (18.1), p. 589: the job-filling rate is `q^v = M(u, v)/v = q(θ)` and the job-finding
rate is `q^u = M(u, v)/u = q(θ)θ`, where `θ = v/u`. -/
theorem eq_18_1 (MF : DMMatchingFn) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    MF.M u v / v = dm_q MF (v / u) ∧ MF.M u v / u = dm_q MF (v / u) * (v / u) := by
  rw [dm_M_eq_mul_q MF hu hv]
  constructor
  · field_simp
  · field_simp

/-- Miao, p. 589: `θq(θ) = M(1, θ)`. -/
theorem dm_jobFinding (MF : DMMatchingFn) {θ : ℝ} (hθ : 0 < θ) :
    θ * dm_q MF θ = MF.M 1 θ := by
  have h := MF.homog θ θ⁻¹ 1 hθ (inv_pos.mpr hθ) one_pos
  rw [mul_inv_cancel₀ hθ.ne', mul_one] at h
  rw [dm_q, h]

/-- Miao, p. 589: `q(θ) > 0`. -/
theorem dm_q_pos (MF : DMMatchingFn) {θ : ℝ} (hθ : 0 < θ) : 0 < dm_q MF θ :=
  MF.pos _ _ (inv_pos.mpr hθ) one_pos

/-- Miao, p. 589: `q` is strictly decreasing: when the labour market is tighter it is harder for a
firm to meet a worker. -/
theorem dm_q_strictAntiOn (MF : DMMatchingFn) : StrictAntiOn (dm_q MF) (Set.Ioi 0) := by
  intro x hx y hy hxy
  exact MF.mono_u _ _ _ (inv_pos.mpr (Set.mem_Ioi.mp hy)) (inv_strictAnti₀ hx hxy) one_pos

/-- Miao, p. 589: the job-finding rate `θq(θ)` is strictly increasing: when the labour market is
tighter it is easier for a worker to find a job. -/
theorem dm_jobFinding_strictMonoOn (MF : DMMatchingFn) :
    StrictMonoOn (fun θ ↦ θ * dm_q MF θ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only
  rw [dm_jobFinding MF hx, dm_jobFinding MF hy]
  exact MF.mono_v _ _ _ one_pos hx hxy

/-- Miao, p. 589: the slice `x ↦ M(x, v)` is concave on `x > 0`. -/
theorem dm_concave_u (MF : DMMatchingFn) {v : ℝ} (hv : 0 < v) :
    ConcaveOn ℝ (Set.Ioi 0) (fun x ↦ MF.M x v) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have h := MF.concave.2 (x := (x, v)) (y := (y, v)) ⟨hx, hv⟩ ⟨hy, hv⟩ ha hb hab
  have h2 : a * v + b * v = v := by rw [← add_mul, hab, one_mul]
  simpa [smul_eq_mul, h2] using h

/-- Miao, p. 589: `q` is continuous on `θ > 0` (a concave function is continuous on an open
interval). -/
theorem dm_q_continuousOn (MF : DMMatchingFn) : ContinuousOn (dm_q MF) (Set.Ioi 0) := by
  have hc : ContinuousOn (fun x ↦ MF.M x 1) (Set.Ioi 0) :=
    (dm_concave_u MF one_pos).continuousOn isOpen_Ioi
  refine hc.comp (continuousOn_inv₀.mono fun x hx ↦ ne_of_gt (Set.mem_Ioi.mp hx)) ?_
  intro x hx
  exact inv_pos.mpr (Set.mem_Ioi.mp hx)

/-- Miao, p. 589: if `x ↦ M(x, 1)` has derivative `d` at `1/θ`, then `q′(θ) = −d/θ²`. -/
theorem dm_q_hasDerivAt (MF : DMMatchingFn) {θ d : ℝ} (hθ : θ ≠ 0)
    (hd : HasDerivAt (fun x ↦ MF.M x 1) d θ⁻¹) :
    HasDerivAt (dm_q MF) (d * -(θ ^ 2)⁻¹) θ :=
  hd.comp θ (hasDerivAt_inv hθ)

/-- Miao, p. 589: the partial derivative `M_u(x, 1)` is positive (strict monotonicity and
concavity). -/
theorem dm_Mu_pos (MF : DMMatchingFn) {x d : ℝ} (hx : 0 < x)
    (hd : HasDerivAt (fun y ↦ MF.M y 1) d x) : 0 < d := by
  have h := (dm_concave_u MF one_pos).slope_le_of_hasDerivAt (Set.mem_Ioi.mpr hx)
    (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < x + 1)) (by linarith) hd
  rw [slope_def_field] at h
  have hm := MF.mono_u x (x + 1) 1 hx (by linarith) one_pos
  have : 0 < (MF.M (x + 1) 1 - MF.M x 1) / (x + 1 - x) := by
    apply div_pos <;> linarith
  linarith

/-- Miao, p. 589: `x M_u(x, 1) < M(x, 1)` (by Euler's theorem this is `M_v(x, 1) > 0`). -/
theorem dm_Mu_mul_lt (MF : DMMatchingFn) {x d : ℝ} (hx : 0 < x)
    (hd : HasDerivAt (fun y ↦ MF.M y 1) d x) : d * x < MF.M x 1 := by
  have h := (dm_concave_u MF one_pos).le_slope_of_hasDerivAt
    (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < x / 2)) (Set.mem_Ioi.mpr hx)
    (by linarith) hd
  rw [slope_def_field] at h
  have hh := MF.homog (1 / 2) x 1 (by norm_num) hx one_pos
  have hm := MF.mono_v (1 / 2 * x) (1 / 2 * 1) 1 (by linarith) (by norm_num) (by norm_num)
  have e : x - x / 2 = x / 2 := by ring
  rw [e, le_div_iff₀ (by linarith)] at h
  have e2 : 1 / 2 * x = x / 2 := by ring
  rw [e2] at hh hm
  rw [hh] at hm
  nlinarith

/-- Miao, p. 589: `q′(θ) < 0` and the elasticity `d ln q(θ)/d ln θ = θq′(θ)/q(θ)` lies in
`(−1, 0)` (when `M` is differentiable in `u` at `(1/θ, 1)`). -/
theorem dm_q_elasticity (MF : DMMatchingFn) {θ d : ℝ} (hθ : 0 < θ)
    (hd : HasDerivAt (fun x ↦ MF.M x 1) d θ⁻¹) :
    deriv (dm_q MF) θ < 0 ∧ -1 < θ * deriv (dm_q MF) θ / dm_q MF θ ∧
      θ * deriv (dm_q MF) θ / dm_q MF θ < 0 := by
  have hx : 0 < θ⁻¹ := inv_pos.mpr hθ
  rw [(dm_q_hasDerivAt MF hθ.ne' hd).deriv]
  have hd0 := dm_Mu_pos MF hx hd
  have hd1 := dm_Mu_mul_lt MF hx hd
  have hq : 0 < dm_q MF θ := dm_q_pos MF hθ
  have hqe : dm_q MF θ = MF.M θ⁻¹ 1 := rfl
  have key : θ * (d * -(θ ^ 2)⁻¹) / dm_q MF θ = -(d * θ⁻¹ / MF.M θ⁻¹ 1) := by
    rw [hqe]; field_simp
  rw [key]
  have hM : 0 < MF.M θ⁻¹ 1 := MF.pos _ _ hx one_pos
  refine ⟨?_, ?_, ?_⟩
  · have : 0 < d * (θ ^ 2)⁻¹ := by positivity
    linarith
  · have : d * θ⁻¹ / MF.M θ⁻¹ 1 < 1 := (div_lt_one hM).mpr hd1
    linarith
  · have : 0 < d * θ⁻¹ / MF.M θ⁻¹ 1 := by positivity
    linarith

/-- Miao, p. 595: "we can check that `ξ(θ) ∈ (0, 1)`". -/
theorem dm_xi_mem (MF : DMMatchingFn) {θ d : ℝ} (hθ : 0 < θ)
    (hd : HasDerivAt (fun x ↦ MF.M x 1) d θ⁻¹) : 0 < dm_xi MF θ ∧ dm_xi MF θ < 1 := by
  obtain ⟨-, h1, h2⟩ := dm_q_elasticity MF hθ hd
  have e : dm_xi MF θ = -(θ * deriv (dm_q MF) θ / dm_q MF θ) := by
    rw [dm_xi]; ring
  rw [e]
  constructor <;> linarith

/-- Miao, p. 595 (used in `a₂₁` and in the planner's problem, p. 599): the derivative of the
job-finding rate is `(θq(θ))′ = q(θ)(1 − ξ(θ))`. -/
theorem dm_jobFinding_hasDerivAt (MF : DMMatchingFn) {θ q' : ℝ} (hθ : 0 < θ)
    (hq : HasDerivAt (dm_q MF) q' θ) :
    HasDerivAt (fun x ↦ x * dm_q MF x) (dm_q MF θ * (1 - dm_xi MF θ)) θ := by
  have h := (hasDerivAt_id θ).mul hq
  have hq0 : dm_q MF θ ≠ 0 := (dm_q_pos MF hθ).ne'
  have e : 1 * dm_q MF θ + id θ * q' = dm_q MF θ * (1 - dm_xi MF θ) := by
    rw [dm_xi, hq.deriv]
    simp only [id]
    field_simp
    ring
  exact h.congr_deriv e

/-- Miao, (18.19), p. 593: the **Beveridge curve** `ρ(1 − u) = M(u, v)` is downward sloping. -/
theorem dm_beveridge_anti (MF : DMMatchingFn) {ρ u₁ u₂ v₁ v₂ : ℝ} (hρ : 0 < ρ)
    (hu₁ : 0 < u₁) (hu : u₁ < u₂) (hv₁ : 0 < v₁)
    (h₁ : ρ * (1 - u₁) = MF.M u₁ v₁) (h₂ : ρ * (1 - u₂) = MF.M u₂ v₂) : v₂ < v₁ := by
  by_contra hc
  rcases (not_lt.mp hc).lt_or_eq with hlt | heq
  · have a := MF.mono_v u₂ v₁ v₂ (by linarith) hv₁ hlt
    have c := MF.mono_u u₁ u₂ v₁ hu₁ hu hv₁
    nlinarith
  · have c := MF.mono_u u₁ u₂ v₁ hu₁ hu hv₁
    rw [← heq] at h₂
    nlinarith

/-- Miao, (18.19), p. 593: the **Beveridge curve** is convex: if `B(u) > 0` solves
`ρ(1 − u) = M(u, B(u))` for `u ∈ (0, 1)`, then `B` is convex. -/
theorem dm_beveridge_convex (MF : DMMatchingFn) {ρ : ℝ} {B : ℝ → ℝ}
    (hB : ∀ u ∈ Set.Ioo (0 : ℝ) 1, 0 < B u ∧ ρ * (1 - u) = MF.M u (B u)) :
    ConvexOn ℝ (Set.Ioo 0 1) B := by
  refine ⟨convex_Ioo 0 1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have hz : a • x + b • y ∈ Set.Ioo (0 : ℝ) 1 := (convex_Ioo 0 1) hx hy ha hb hab
  obtain ⟨hBx, ex⟩ := hB x hx
  obtain ⟨hBy, ey⟩ := hB y hy
  obtain ⟨hBz, ez⟩ := hB _ hz
  have hc := MF.concave.2 (x := (x, B x)) (y := (y, B y)) ⟨hx.1, hBx⟩ ⟨hy.1, hBy⟩ ha hb hab
  simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at hc hz ez ⊢
  have hpos : 0 < a * B x + b * B y := by
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_pos ha' hBx
      have := mul_nonneg hb hBy.le
      linarith
    · have hb1 : b = 1 := by rw [← ha'] at hab; linarith
      rw [← ha', hb1]
      simpa using hBy
  by_contra hcon
  have hlt := MF.mono_v _ _ _ hz.1 hpos (not_le.mp hcon)
  have e : a * MF.M x (B x) + b * MF.M y (B y) = ρ * (1 - (a * x + b * y)) := by
    rw [← ex, ← ey]
    have : a * (ρ * (1 - x)) + b * (ρ * (1 - y)) = ρ * ((a + b) - (a * x + b * y)) := by ring
    rw [this, hab]
  linarith

/-- Miao, p. 589: Cobb–Douglas `M(u, v) = μu^αv^{1−α}` is linearly homogeneous. -/
theorem dm_cd_homog {μ α : ℝ} (t u v : ℝ) (ht : 0 < t) (hu : 0 < u) (hv : 0 < v) :
    μ * (t * u) ^ α * (t * v) ^ (1 - α) = t * (μ * u ^ α * v ^ (1 - α)) := by
  rw [Real.mul_rpow ht.le hu.le, Real.mul_rpow ht.le hv.le]
  have : t ^ α * t ^ (1 - α) = t := by
    rw [← Real.rpow_add ht]; simp
  calc μ * (t ^ α * u ^ α) * (t ^ (1 - α) * v ^ (1 - α))
      = μ * (t ^ α * t ^ (1 - α)) * u ^ α * v ^ (1 - α) := by ring
    _ = t * (μ * u ^ α * v ^ (1 - α)) := by rw [this]; ring

/-- Miao, p. 589: Cobb–Douglas matching is jointly concave on the open orthant (weighted
AM–GM). -/
theorem dm_cd_concave {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1) :
    ConcaveOn ℝ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
      (fun p : ℝ × ℝ ↦ μ * p.1 ^ α * p.2 ^ (1 - α)) := by
  refine ⟨(convex_Ioi 0).prod (convex_Ioi 0), fun x hx y hy a b ha hb hab ↦ ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  simp only [Set.mem_Ioi] at hx1 hx2 hy1 hy2
  simp only [smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
  set U := a * x.1 + b * y.1 with hUdef
  set V := a * x.2 + b * y.2 with hVdef
  have hpos : ∀ p q : ℝ, 0 < p → 0 < q → 0 < a * p + b * q := by
    intro p q hp hq
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_pos ha' hp
      have := mul_nonneg hb hq.le
      linarith
    · have hb1 : b = 1 := by rw [← ha'] at hab; linarith
      rw [← ha', hb1]; simpa using hq
  have hU : 0 < U := hpos _ _ hx1 hy1
  have hV : 0 < V := hpos _ _ hx2 hy2
  have hα1' : 0 ≤ 1 - α := by linarith
  -- each term is bounded by the tangent plane at `(U, V)`
  have bound : ∀ p q : ℝ, 0 < p → 0 < q →
      p ^ α * q ^ (1 - α) ≤ U ^ α * V ^ (1 - α) * (α * (p / U) + (1 - α) * (q / V)) := by
    intro p q hp hq
    have amgm := Real.geom_mean_le_arith_mean2_weighted hα0.le hα1' (div_pos hp hU).le
      (div_pos hq hV).le (by ring)
    have ep : p = U * (p / U) := by field_simp
    have eq' : q = V * (q / V) := by field_simp
    calc p ^ α * q ^ (1 - α) = (U * (p / U)) ^ α * (V * (q / V)) ^ (1 - α) := by
          rw [← ep, ← eq']
      _ = U ^ α * V ^ (1 - α) * ((p / U) ^ α * (q / V) ^ (1 - α)) := by
          rw [Real.mul_rpow hU.le (div_pos hp hU).le, Real.mul_rpow hV.le (div_pos hq hV).le]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left amgm (by positivity)
  have b1 := bound _ _ hx1 hx2
  have b2 := bound _ _ hy1 hy2
  have hsum : a * (α * (x.1 / U) + (1 - α) * (x.2 / V)) +
      b * (α * (y.1 / U) + (1 - α) * (y.2 / V)) = 1 := by
    have e1 : a * (x.1 / U) + b * (y.1 / U) = 1 := by
      field_simp; linarith
    have e2 : a * (x.2 / V) + b * (y.2 / V) = 1 := by
      field_simp; linarith
    calc _ = α * (a * (x.1 / U) + b * (y.1 / U)) + (1 - α) * (a * (x.2 / V) + b * (y.2 / V)) := by
          ring
      _ = 1 := by rw [e1, e2]; ring
  have hW : 0 ≤ U ^ α * V ^ (1 - α) := by positivity
  calc a * (μ * x.1 ^ α * x.2 ^ (1 - α)) + b * (μ * y.1 ^ α * y.2 ^ (1 - α))
      = μ * (a * (x.1 ^ α * x.2 ^ (1 - α)) + b * (y.1 ^ α * y.2 ^ (1 - α))) := by ring
    _ ≤ μ * (a * (U ^ α * V ^ (1 - α) * (α * (x.1 / U) + (1 - α) * (x.2 / V))) +
          b * (U ^ α * V ^ (1 - α) * (α * (y.1 / U) + (1 - α) * (y.2 / V)))) := by
        gcongr
    _ = μ * (U ^ α * V ^ (1 - α) * (a * (α * (x.1 / U) + (1 - α) * (x.2 / V)) +
          b * (α * (y.1 / U) + (1 - α) * (y.2 / V)))) := by ring
    _ = μ * U ^ α * V ^ (1 - α) := by rw [hsum]; ring

/-- Miao, p. 589: the Cobb–Douglas matching function `M(u, v) = μu^αv^{1−α}`, `μ > 0`,
`α ∈ (0, 1)`, is a matching function in the sense of `DMMatchingFn`. -/
noncomputable def dm_cdMatching (μ α : ℝ) (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1) :
    DMMatchingFn where
  M u v := μ * u ^ α * v ^ (1 - α)
  pos u v hu hv := by positivity
  homog t u v ht hu hv := dm_cd_homog t u v ht hu hv
  mono_u u u' v hu huu hv := by
    have := Real.rpow_lt_rpow hu.le huu hα0
    have : 0 < v ^ (1 - α) := by positivity
    gcongr
  mono_v u v v' hu hv hvv := by
    have := Real.rpow_lt_rpow hv.le hvv (by linarith : 0 < 1 - α)
    have : 0 < μ * u ^ α := by positivity
    gcongr
  concave := dm_cd_concave hμ hα0 hα1

/-- Miao, p. 589: for Cobb–Douglas matching, `q(θ) = μθ^{−α}`. -/
theorem dm_cd_q {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1) {θ : ℝ} (hθ : 0 < θ) :
    dm_q (dm_cdMatching μ α hμ hα0 hα1) θ = μ * θ ^ (-α) := by
  simp only [dm_q, dm_cdMatching, Real.one_rpow, mul_one]
  rw [Real.inv_rpow hθ.le, Real.rpow_neg hθ.le]

/-- Miao, p. 595: for Cobb–Douglas matching, `ξ(θ) = α` (with the derivative of `q`). -/
theorem dm_cd_hasDerivAt {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1) {θ : ℝ}
    (hθ : 0 < θ) :
    HasDerivAt (fun x ↦ (dm_cdMatching μ α hμ hα0 hα1).M x 1)
      (μ * (α * θ⁻¹ ^ (α - 1))) θ⁻¹ := by
  simp only [dm_cdMatching, Real.one_rpow, mul_one]
  exact (Real.hasDerivAt_rpow_const (Or.inl (inv_pos.mpr hθ).ne')).const_mul μ

/-- Miao, p. 595: for Cobb–Douglas matching the elasticity is constant, `ξ(θ) = α`. -/
theorem dm_cd_xi {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1) {θ : ℝ} (hθ : 0 < θ) :
    dm_xi (dm_cdMatching μ α hμ hα0 hα1) θ = α := by
  have hd := dm_q_hasDerivAt _ hθ.ne' (dm_cd_hasDerivAt hμ hα0 hα1 hθ)
  rw [dm_xi, hd.deriv]
  have hq : dm_q (dm_cdMatching μ α hμ hα0 hα1) θ = μ * θ⁻¹ ^ α := by
    simp [dm_q, dm_cdMatching]
  rw [hq]
  have hx : 0 < θ⁻¹ := inv_pos.mpr hθ
  have e : θ⁻¹ ^ (α - 1) = θ⁻¹ ^ α / θ⁻¹ := Real.rpow_sub_one hx.ne' α
  rw [e]
  have : 0 < θ⁻¹ ^ α := by positivity
  field_simp

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §18.1: values of jobs and workers, free entry, Nash bargaining and the wage equation

Miao, §18.1, pp. 589–592, equations (18.4)–(18.15) and the definition of a search equilibrium.
All value functions are real sequences indexed by `t : ℕ`.

* `eq_18_6`, `eq_18_7`, `eq_18_8`: free entry `V_t = 0` in the vacancy equation (18.5) gives
  `J^F_{t+1} = κ/(βq^v_t)` (18.6); with the filled-job equation (18.4) it gives (18.7) and the
  job creation (Euler) equation (18.8).
* `dm_amgm2_strict`, `dm_nash_bound`, `dm_nash_solution`: the Nash product
  `(x₀ + w)^η (y₀ − w)^{1−η}` (surpluses affine in the wage, with constant total surplus) is
  maximised exactly where `η(y₀ − w) = (1 − η)(x₀ + w)` (weighted AM–GM, with its strict form for
  uniqueness).
* `eq_18_11`: the bargaining problem (18.11) — with the continuation values taken as given, the
  wage `w_t` solves (18.11) iff the first-order condition `ηJ^F_t = (1 − η)(J^W_t − J^U_t)`
  holds. The book only states the first-order condition; here it is shown to be necessary and
  sufficient for the constrained maximum.
* `eq_18_12`, `eq_18_13`: surplus sharing `ηS_t = J^W_t − J^U_t`, `(1 − η)S_t = J^F_t`,
  and `(1 − η)S_{t+1} = κ/(βq^v_t)`.
* `eq_18_14`: the surplus equation (all three lines); `dm_worker_surplus`: the worker-surplus
  equation on p. 591; `eq_18_15`: the wage equation `w_t = η(A + κθ_t) + (1 − η)b`.
* `dm_IsSearchEqm`: a search equilibrium (p. 592); `dm_bellman_implies_eqm`: the Bellman
  equations, free entry and Nash bargaining imply the equilibrium conditions (18.8), (18.15).
-/

namespace Miao.SearchAndMatching

/-- Miao, (18.6), p. 590: free entry `V_t = 0` in the vacancy equation (18.5)
`V_t = −κ + β(q^v_t J^F_{t+1} + (1 − q^v_t)V_{t+1})` gives `J^F_{t+1} = κ/(βq^v_t)`. -/
theorem eq_18_6 {κ β : ℝ} {JF V qv : ℕ → ℝ} (hV : ∀ t, V t = 0)
    (h5 : ∀ t, V t = -κ + β * (qv t * JF (t + 1) + (1 - qv t) * V (t + 1)))
    (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0) (t : ℕ) : JF (t + 1) = κ / (β * qv t) := by
  have h := h5 t
  rw [hV t, hV (t + 1)] at h
  have hq' := hq t
  field_simp
  linarith

/-- Miao, (18.7), p. 590: substituting (18.6) into the filled-job equation (18.4)
`J^F_t = A − w_t + β(ρV_{t+1} + (1 − ρ)J^F_{t+1})` gives `J^F_t = A − w_t + (1 − ρ)κ/q^v_t`. -/
theorem eq_18_7 {A κ β ρ : ℝ} {JF V qv w : ℕ → ℝ} (hV : ∀ t, V t = 0)
    (h4 : ∀ t, JF t = A - w t + β * (ρ * V (t + 1) + (1 - ρ) * JF (t + 1)))
    (h5 : ∀ t, V t = -κ + β * (qv t * JF (t + 1) + (1 - qv t) * V (t + 1)))
    (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0) (t : ℕ) : JF t = A - w t + (1 - ρ) * κ / qv t := by
  rw [h4 t, hV (t + 1), eq_18_6 hV h5 hβ hq t]
  have hq' := hq t
  field_simp
  ring

/-- Miao, (18.8), p. 590: the **job creation equation**
`κ/q^v_t = β(A − w_{t+1} + (1 − ρ)κ/q^v_{t+1})`. -/
theorem eq_18_8 {A κ β ρ : ℝ} {JF V qv w : ℕ → ℝ} (hV : ∀ t, V t = 0)
    (h4 : ∀ t, JF t = A - w t + β * (ρ * V (t + 1) + (1 - ρ) * JF (t + 1)))
    (h5 : ∀ t, V t = -κ + β * (qv t * JF (t + 1) + (1 - qv t) * V (t + 1)))
    (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0) (t : ℕ) :
    κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) := by
  rw [← eq_18_7 hV h4 h5 hβ hq (t + 1), eq_18_6 hV h5 hβ hq t]
  have hq' := hq t
  field_simp

/-- Strict weighted AM–GM for two terms: `p₁^w p₂^{1−w} < wp₁ + (1 − w)p₂` when `p₁ ≠ p₂`. -/
theorem dm_amgm2_strict {w p₁ p₂ : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hp₁ : 0 ≤ p₁)
    (hp₂ : 0 ≤ p₂) (hne : p₁ ≠ p₂) : p₁ ^ w * p₂ ^ (1 - w) < w * p₁ + (1 - w) * p₂ := by
  have h := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos (Finset.univ : Finset (Fin 2))
    ![w, 1 - w] ![p₁, p₂] ?_ ?_ ?_).mpr
    ⟨0, Finset.mem_univ _, 1, Finset.mem_univ _, by simpa using hne⟩
  · simpa [Fin.prod_univ_two, Fin.sum_univ_two] using h
  · intro i _
    fin_cases i
    · simpa using hw0
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith
  · simp [Fin.sum_univ_two]
  · intro i _
    fin_cases i
    · simpa using hp₁
    · simpa using hp₂

/-- Miao, (18.11), p. 590: the Nash product with nonnegative surpluses `x, y` is at most
`η^η(1 − η)^{1−η}(x + y)`, with equality only at the split `x = η(x + y)`. -/
theorem dm_nash_bound {η x y : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ η * y ^ (1 - η) ≤ η ^ η * (1 - η) ^ (1 - η) * (x + y) ∧
      (x ^ η * y ^ (1 - η) = η ^ η * (1 - η) ^ (1 - η) * (x + y) → x = η * (x + y)) := by
  have hη1' : 0 < 1 - η := by linarith
  have hp₁ : 0 ≤ x / η := div_nonneg hx hη0.le
  have hp₂ : 0 ≤ y / (1 - η) := div_nonneg hy hη1'.le
  have ex : x ^ η = η ^ η * (x / η) ^ η := by
    rw [← Real.mul_rpow hη0.le hp₁]; congr 1; field_simp
  have ey : y ^ (1 - η) = (1 - η) ^ (1 - η) * (y / (1 - η)) ^ (1 - η) := by
    rw [← Real.mul_rpow hη1'.le hp₂]; congr 1; field_simp
  have hsum : η * (x / η) + (1 - η) * (y / (1 - η)) = x + y := by field_simp
  have hprod : x ^ η * y ^ (1 - η) =
      η ^ η * (1 - η) ^ (1 - η) * ((x / η) ^ η * (y / (1 - η)) ^ (1 - η)) := by
    rw [ex, ey]; ring
  have hc : 0 < η ^ η * (1 - η) ^ (1 - η) := by positivity
  have amgm := Real.geom_mean_le_arith_mean2_weighted hη0.le hη1'.le hp₁ hp₂ (by ring)
  refine ⟨?_, fun heq ↦ ?_⟩
  · rw [hprod, ← hsum]
    exact mul_le_mul_of_nonneg_left amgm hc.le
  · by_contra hne
    have hne' : x / η ≠ y / (1 - η) := by
      intro h
      apply hne
      field_simp at h
      linarith
    have hlt := dm_amgm2_strict hη0 hη1 hp₁ hp₂ hne'
    rw [hprod, ← hsum] at heq
    have := mul_lt_mul_of_pos_left hlt hc
    linarith

/-- Miao, (18.11), p. 590: if the worker's surplus is `x₀ + w` and the firm's is `y₀ − w`, with
positive total surplus `x₀ + y₀`, then `w` maximises the Nash product
`(x₀ + w)^η(y₀ − w)^{1−η}` subject to both surpluses being nonnegative iff
`η(y₀ − w) = (1 − η)(x₀ + w)`. -/
theorem dm_nash_solution {η x₀ y₀ w : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hs : 0 < x₀ + y₀) :
    (0 ≤ x₀ + w ∧ 0 ≤ y₀ - w ∧
      IsMaxOn (fun w' ↦ (x₀ + w') ^ η * (y₀ - w') ^ (1 - η))
        {w' | 0 ≤ x₀ + w' ∧ 0 ≤ y₀ - w'} w) ↔ η * (y₀ - w) = (1 - η) * (x₀ + w) := by
  set c := η ^ η * (1 - η) ^ (1 - η) with hcdef
  have hη1' : 0 < 1 - η := by linarith
  -- the value at the split `x = ηs`
  have hval : ∀ w', x₀ + w' = η * (x₀ + y₀) →
      (x₀ + w') ^ η * (y₀ - w') ^ (1 - η) = c * (x₀ + y₀) := by
    intro w' hw'
    have hy : y₀ - w' = (1 - η) * (x₀ + y₀) := by linarith
    rw [hw', hy, Real.mul_rpow hη0.le hs.le, Real.mul_rpow hη1'.le hs.le]
    have : (x₀ + y₀) ^ η * (x₀ + y₀) ^ (1 - η) = x₀ + y₀ := by
      rw [← Real.rpow_add hs]; simp
    rw [hcdef]
    calc η ^ η * (x₀ + y₀) ^ η * ((1 - η) ^ (1 - η) * (x₀ + y₀) ^ (1 - η))
        = η ^ η * (1 - η) ^ (1 - η) * ((x₀ + y₀) ^ η * (x₀ + y₀) ^ (1 - η)) := by ring
      _ = _ := by rw [this]
  have hsum : ∀ w', (x₀ + w') + (y₀ - w') = x₀ + y₀ := fun w' ↦ by ring
  constructor
  · rintro ⟨h1, h2, hmax⟩
    set w₀ := η * (x₀ + y₀) - x₀ with hw₀
    have hw₀' : x₀ + w₀ = η * (x₀ + y₀) := by rw [hw₀]; ring
    have hmem : w₀ ∈ {w' | 0 ≤ x₀ + w' ∧ 0 ≤ y₀ - w'} := by
      refine ⟨?_, ?_⟩
      · rw [hw₀']; positivity
      · have : y₀ - w₀ = (1 - η) * (x₀ + y₀) := by rw [hw₀]; ring
        rw [this]; positivity
    have hge : (x₀ + w₀) ^ η * (y₀ - w₀) ^ (1 - η) ≤ (x₀ + w) ^ η * (y₀ - w) ^ (1 - η) :=
      hmax hmem
    rw [hval w₀ hw₀'] at hge
    obtain ⟨hle, heq⟩ := dm_nash_bound hη0 hη1 h1 h2
    rw [hsum] at hle heq
    have hx := heq (le_antisymm hle hge)
    linarith
  · intro hfoc
    have hx : x₀ + w = η * (x₀ + y₀) := by linarith
    have hy : y₀ - w = (1 - η) * (x₀ + y₀) := by linarith
    refine ⟨by rw [hx]; positivity, by rw [hy]; positivity, ?_⟩
    intro w' hw'
    dsimp only
    rw [hval w hx]
    have := (dm_nash_bound hη0 hη1 hw'.1 hw'.2).1
    rwa [hsum] at this

/-- Miao, (18.11) and the first-order condition, pp. 590–591: given the continuation values
`J^W_{t+1}, J^U_{t+1}, J^F_{t+1}, V_{t+1}` and `J^U_t` (which do not depend on `w_t`), the
worker's value `J^W_t(w) = w + β(ρJ^U_{t+1} + (1 − ρ)J^W_{t+1})` (18.9) and the firm's value
`J^F_t(w) = A − w + β(ρV_{t+1} + (1 − ρ)J^F_{t+1})` (18.4), the wage `w` solves the Nash
bargaining problem `max (J^W_t − J^U_t)^η (J^F_t − V_t)^{1−η}` subject to `J^W_t ≥ J^U_t` and
`J^F_t ≥ V_t` iff `η(J^F_t − V_t) = (1 − η)(J^W_t − J^U_t)` (when the total surplus is
positive). -/
theorem eq_18_11 {A β ρ η JWn JUn JFn Vn JU V w : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hS : 0 < A + β * (ρ * Vn + (1 - ρ) * JFn) - V + (β * (ρ * JUn + (1 - ρ) * JWn) - JU)) :
    (JU ≤ w + β * (ρ * JUn + (1 - ρ) * JWn) ∧ V ≤ A - w + β * (ρ * Vn + (1 - ρ) * JFn) ∧
      IsMaxOn (fun w' ↦ (w' + β * (ρ * JUn + (1 - ρ) * JWn) - JU) ^ η *
          (A - w' + β * (ρ * Vn + (1 - ρ) * JFn) - V) ^ (1 - η))
        {w' | JU ≤ w' + β * (ρ * JUn + (1 - ρ) * JWn) ∧
          V ≤ A - w' + β * (ρ * Vn + (1 - ρ) * JFn)} w) ↔
      η * (A - w + β * (ρ * Vn + (1 - ρ) * JFn) - V) =
        (1 - η) * (w + β * (ρ * JUn + (1 - ρ) * JWn) - JU) := by
  set X := β * (ρ * JUn + (1 - ρ) * JWn) with hX
  set Y := A + β * (ρ * Vn + (1 - ρ) * JFn) - V with hY
  have e1 : ∀ w', w' + X - JU = (X - JU) + w' := fun w' ↦ by ring
  have e2 : ∀ w', A - w' + β * (ρ * Vn + (1 - ρ) * JFn) - V = Y - w' := fun w' ↦ by
    rw [hY]; ring
  have i1 : ∀ w', (JU ≤ w' + X) ↔ 0 ≤ (X - JU) + w' := fun w' ↦ by
    constructor <;> intro h <;> linarith
  have i2 : ∀ w', (V ≤ A - w' + β * (ρ * Vn + (1 - ρ) * JFn)) ↔ 0 ≤ Y - w' := fun w' ↦ by
    rw [hY]; constructor <;> intro h <;> linarith
  simp only [e1, e2, i1, i2]
  have hS' : 0 < (X - JU) + Y := by rw [hY]; linarith
  exact dm_nash_solution hη0 hη1 hS'

/-- Miao, p. 591: the **total surplus** `S_t = J^F_t + J^W_t − J^U_t`. -/
def dm_surplus (JF JW JU : ℕ → ℝ) (t : ℕ) : ℝ := JF t + JW t - JU t

/-- Miao, (18.12)–(18.13), p. 591: the bargaining first-order condition
`ηJ^F_t = (1 − η)(J^W_t − J^U_t)` is equivalent to the surplus split `ηS_t = J^W_t − J^U_t`,
`(1 − η)S_t = J^F_t`. -/
theorem eq_18_12 {η : ℝ} {JF JW JU : ℕ → ℝ} (t : ℕ) :
    η * JF t = (1 - η) * (JW t - JU t) ↔
      η * dm_surplus JF JW JU t = JW t - JU t ∧ (1 - η) * dm_surplus JF JW JU t = JF t := by
  unfold dm_surplus
  constructor
  · intro h
    exact ⟨by linear_combination h, by linear_combination (-1 : ℝ) * h⟩
  · rintro ⟨h, -⟩
    linear_combination h

/-- Miao, (18.13), p. 591: `(1 − η)S_{t+1} = J^F_{t+1} = κ/(βq^v_t)`, by the free entry condition
(18.6). -/
theorem eq_18_13 {κ β η : ℝ} {JF JW JU V qv : ℕ → ℝ} (hV : ∀ t, V t = 0)
    (h5 : ∀ t, V t = -κ + β * (qv t * JF (t + 1) + (1 - qv t) * V (t + 1)))
    (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0)
    (hfoc : ∀ t, η * JF t = (1 - η) * (JW t - JU t)) (t : ℕ) :
    (1 - η) * dm_surplus JF JW JU (t + 1) = JF (t + 1) ∧ JF (t + 1) = κ / (β * qv t) :=
  ⟨((eq_18_12 (t + 1)).mp (hfoc (t + 1))).2, eq_18_6 hV h5 hβ hq t⟩

/-- Miao, (18.14), p. 591: by (18.4) (with `V = 0`), (18.9) and (18.10),
`S_t = A − b + β(1 − ρ)S_{t+1} − βq^u_t(J^W_{t+1} − J^U_{t+1})`; by (18.12) this is
`A − b + β(1 − ρ − ηq^u_t)S_{t+1}`, and by (18.13) it is
`A − b + κ(1 − ρ − ηq^u_t)/((1 − η)q^v_t)`. -/
theorem eq_18_14 {A b κ β ρ η : ℝ} {JF JW JU w qv qu : ℕ → ℝ} (t : ℕ)
    (h4 : JF t = A - w t + β * (ρ * 0 + (1 - ρ) * JF (t + 1)))
    (h9 : JW t = w t + β * (ρ * JU (t + 1) + (1 - ρ) * JW (t + 1)))
    (h10 : JU t = b + β * (qu t * JW (t + 1) + (1 - qu t) * JU (t + 1)))
    (h12 : η * dm_surplus JF JW JU (t + 1) = JW (t + 1) - JU (t + 1))
    (h13 : (1 - η) * dm_surplus JF JW JU (t + 1) = κ / (β * qv t))
    (hβ : β ≠ 0) (hq : qv t ≠ 0) (hη1 : η ≠ 1) :
    dm_surplus JF JW JU t = A - b + β * (1 - ρ) * dm_surplus JF JW JU (t + 1) -
        β * qu t * (JW (t + 1) - JU (t + 1)) ∧
      dm_surplus JF JW JU t = A - b + β * (1 - ρ - η * qu t) * dm_surplus JF JW JU (t + 1) ∧
      dm_surplus JF JW JU t = A - b + κ * (1 - ρ - η * qu t) / ((1 - η) * qv t) := by
  have first : dm_surplus JF JW JU t = A - b + β * (1 - ρ) * dm_surplus JF JW JU (t + 1) -
      β * qu t * (JW (t + 1) - JU (t + 1)) := by
    unfold dm_surplus
    rw [h4, h9, h10]
    ring
  have second : dm_surplus JF JW JU t =
      A - b + β * (1 - ρ - η * qu t) * dm_surplus JF JW JU (t + 1) := by
    rw [first, ← h12]; ring
  refine ⟨first, second, ?_⟩
  have hη' : 1 - η ≠ 0 := sub_ne_zero.mpr (Ne.symm hη1)
  have hS : dm_surplus JF JW JU (t + 1) = κ / ((1 - η) * β * qv t) := by
    field_simp
    field_simp at h13
    linear_combination h13
  rw [second, hS]
  field_simp

/-- Miao, p. 591: by (18.9), (18.10) and (18.12),
`ηS_t = J^W_t − J^U_t = w_t − b + β(1 − ρ − q^u_t)(J^W_{t+1} − J^U_{t+1})
  = w_t − b + β(1 − ρ − q^u_t)ηS_{t+1}`. -/
theorem dm_worker_surplus {b β ρ η : ℝ} {JF JW JU w qu : ℕ → ℝ} (t : ℕ)
    (h9 : JW t = w t + β * (ρ * JU (t + 1) + (1 - ρ) * JW (t + 1)))
    (h10 : JU t = b + β * (qu t * JW (t + 1) + (1 - qu t) * JU (t + 1)))
    (h12t : η * dm_surplus JF JW JU t = JW t - JU t)
    (h12 : η * dm_surplus JF JW JU (t + 1) = JW (t + 1) - JU (t + 1)) :
    η * dm_surplus JF JW JU t = w t - b + β * (1 - ρ - qu t) * (JW (t + 1) - JU (t + 1)) ∧
      η * dm_surplus JF JW JU t =
        w t - b + β * (1 - ρ - qu t) * (η * dm_surplus JF JW JU (t + 1)) := by
  have first : η * dm_surplus JF JW JU t =
      w t - b + β * (1 - ρ - qu t) * (JW (t + 1) - JU (t + 1)) := by
    rw [h12t, h9, h10]; ring
  exact ⟨first, by rw [first, h12]⟩

/-- Miao, (18.15), p. 591: substituting (18.14) for `S_t` and (18.13) for `S_{t+1}` into the
worker-surplus equation and using `q^u_t = θ_tq^v_t` (18.1) gives the **wage equation**
`w_t = η(A + κθ_t) + (1 − η)b`. -/
theorem eq_18_15 {A b κ β ρ η : ℝ} {JF JW JU w qv qu θ : ℕ → ℝ} (t : ℕ)
    (h4 : JF t = A - w t + β * (ρ * 0 + (1 - ρ) * JF (t + 1)))
    (h9 : JW t = w t + β * (ρ * JU (t + 1) + (1 - ρ) * JW (t + 1)))
    (h10 : JU t = b + β * (qu t * JW (t + 1) + (1 - qu t) * JU (t + 1)))
    (h12t : η * dm_surplus JF JW JU t = JW t - JU t)
    (h12 : η * dm_surplus JF JW JU (t + 1) = JW (t + 1) - JU (t + 1))
    (h13 : (1 - η) * dm_surplus JF JW JU (t + 1) = κ / (β * qv t))
    (hqu : qu t = θ t * qv t) (hβ : β ≠ 0) (hq : qv t ≠ 0) (hη1 : η ≠ 1) :
    w t = η * (A + κ * θ t) + (1 - η) * b := by
  have hη' : 1 - η ≠ 0 := sub_ne_zero.mpr (Ne.symm hη1)
  have hSt := (eq_18_14 (A := A) t h4 h9 h10 h12 h13 hβ hq hη1).2.2
  have hW := (dm_worker_surplus (w := w) t h9 h10 h12t h12).2
  have hS : dm_surplus JF JW JU (t + 1) = κ / ((1 - η) * β * qv t) := by
    field_simp
    field_simp at h13
    linear_combination h13
  rw [hSt, hS, hqu] at hW
  field_simp at hW
  have key : ((1 - η) * qv t) * (w t - (η * (A + κ * θ t) + (1 - η) * b)) = 0 := by
    linear_combination (-1 : ℝ) * hW
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero hη' hq)
  · linarith

/-- Miao, p. 592: a **search equilibrium**: sequences `N, u, v, θ, w, q^v` with `u, v > 0`
satisfying (18.1) (`θ_t = v_t/u_t`, `q^v_t = q(θ_t)`), (18.2), (18.3), (18.8) and (18.15). -/
def dm_IsSearchEqm (MF : DMMatchingFn) (A b κ β ρ η : ℝ) (N u v θ w qv : ℕ → ℝ) : Prop :=
  ∀ t, 0 < u t ∧ 0 < v t ∧ θ t = v t / u t ∧ qv t = dm_q MF (θ t) ∧
    N (t + 1) = (1 - ρ) * N t + MF.M (u t) (v t) ∧ u t = 1 - N t ∧
    κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) ∧
    w t = η * (A + κ * θ t) + (1 - η) * b

/-- Miao, pp. 590–592: the Bellman equations (18.4), (18.5), (18.9), (18.10), free entry and the
Nash bargaining first-order condition imply the equilibrium conditions (18.8) and (18.15) at
every date. -/
theorem dm_bellman_implies_eqm {A b κ β ρ η : ℝ} {JF JW JU V w qv qu θ : ℕ → ℝ}
    (hV : ∀ t, V t = 0)
    (h4 : ∀ t, JF t = A - w t + β * (ρ * V (t + 1) + (1 - ρ) * JF (t + 1)))
    (h5 : ∀ t, V t = -κ + β * (qv t * JF (t + 1) + (1 - qv t) * V (t + 1)))
    (h9 : ∀ t, JW t = w t + β * (ρ * JU (t + 1) + (1 - ρ) * JW (t + 1)))
    (h10 : ∀ t, JU t = b + β * (qu t * JW (t + 1) + (1 - qu t) * JU (t + 1)))
    (hfoc : ∀ t, η * JF t = (1 - η) * (JW t - JU t))
    (hqu : ∀ t, qu t = θ t * qv t) (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0) (hη1 : η ≠ 1) (t : ℕ) :
    κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) ∧
      w t = η * (A + κ * θ t) + (1 - η) * b := by
  refine ⟨eq_18_8 hV h4 h5 hβ hq t, ?_⟩
  have h4' : JF t = A - w t + β * (ρ * 0 + (1 - ρ) * JF (t + 1)) := by
    rw [h4 t, hV (t + 1)]
  obtain ⟨h13a, h13b⟩ := eq_18_13 hV h5 hβ hq hfoc t
  exact eq_18_15 t h4' (h9 t) (h10 t) ((eq_18_12 t).mp (hfoc t)).1
    ((eq_18_12 (t + 1)).mp (hfoc (t + 1))).1 (h13a.trans h13b) (hqu t) hβ (hq t) hη1

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §18.1: the steady state — job creation and wage curves, Beveridge curve, comparative statics

Miao, §18.1, "Steady State", pp. 592–594, equations (18.16)–(18.19) and Figures 18.1–18.2.

* `eq_18_16`, `dm_jc_iff`, `dm_jc_strictAntiOn`: the steady-state job creation condition and the
  downward-sloping job creation curve `w = A − κ(1 − β(1 − ρ))/(βq(θ))`.
* `eq_18_17`, `dm_wc_strictMono`: the upward-sloping wage curve `w = η(A + κθ) + (1 − η)b`.
* `eq_18_18`, `dm_ssLHS_strictMonoOn`, `dm_ss_unique`, `dm_ss_exists`, `dm_cd_ss_existsUnique`:
  eliminating `w`, `θ*` solves (18.18); the solution is unique, and exists under a condition at
  small `θ`. For Cobb–Douglas matching it exists iff `A > b`. Correction: the book's "unique
  solution" needs `A > b`; for `A ≤ b` there is no solution (`dm_ss_not_exists`).
* `eq_18_19`, `dm_uStar`: on the job creation line `v = θu`, the steady-state Beveridge relation
  `ρ(1 − u) = M(u, v)` gives `u* = ρ/(ρ + θq(θ))`; `dm_uStar_strictAntiOn`,
  `dm_vStar_strictMonoOn`: unemployment falls and vacancies rise with `θ`.
* Comparative statics (p. 593): `dm_cs_shifts` (the job creation curve shifts up one-for-one in
  `A`, the wage curve by `η < 1`), `dm_cs_A` (higher `A`: higher `θ`, `w`, `v`, lower `u`),
  `dm_cs_b` (higher `b`: higher `w`, `u`, lower `θ`, `v`), `dm_cs_eta` (higher `η`: the same
  signs as `b`, when `A > b`).
* `dm_steady_isSearchEqm`, `dm_searchEqm_exists`: the steady state is a search equilibrium; a
  concrete Cobb–Douglas economy has one.
-/

namespace Miao.SearchAndMatching

/-- Miao, (18.16), p. 592: the **job creation curve** `w = A − κ(1 − β(1 − ρ))/(βq(θ))`. -/
noncomputable def dm_jcCurve (MF : DMMatchingFn) (A κ β ρ θ : ℝ) : ℝ :=
  A - κ * (1 - β * (1 - ρ)) / (β * dm_q MF θ)

/-- Miao, (18.17), p. 592: the **wage curve** `w = η(A + κθ) + (1 − η)b`. -/
def dm_wageCurve (A b κ η θ : ℝ) : ℝ := η * (A + κ * θ) + (1 - η) * b

/-- Miao, (18.18), p. 593: the left side `κ(1 − β(1 − ρ))/q(θ) + βηκθ` of (18.18). -/
noncomputable def dm_ssLHS (MF : DMMatchingFn) (κ β ρ η θ : ℝ) : ℝ :=
  κ / dm_q MF θ * (1 - β * (1 - ρ)) + β * η * κ * θ

/-- Miao, (18.19), p. 593: steady-state unemployment `u* = ρ/(ρ + θq(θ))`. -/
noncomputable def dm_uStar (MF : DMMatchingFn) (ρ θ : ℝ) : ℝ := ρ / (ρ + θ * dm_q MF θ)

/-- Miao, (18.16), p. 592: in a steady state, the job creation equation (18.8) reads
`κ(1 − β(1 − ρ))/q(θ) = β(A − w)`. -/
theorem eq_18_16 (MF : DMMatchingFn) (A κ β ρ w θ : ℝ) :
    κ / dm_q MF θ = β * (A - w + (1 - ρ) * κ / dm_q MF θ) ↔
      κ / dm_q MF θ * (1 - β * (1 - ρ)) = β * (A - w) := by
  have e : (1 - ρ) * κ / dm_q MF θ = (1 - ρ) * (κ / dm_q MF θ) := by ring
  rw [e]
  constructor <;> intro h <;> linear_combination h

/-- Miao, (18.16), p. 592: (18.16) holds iff `w` lies on the job creation curve. -/
theorem dm_jc_iff (MF : DMMatchingFn) {A κ β ρ w θ : ℝ} (hβ : 0 < β) (hθ : 0 < θ) :
    κ / dm_q MF θ * (1 - β * (1 - ρ)) = β * (A - w) ↔ w = dm_jcCurve MF A κ β ρ θ := by
  have hq := (dm_q_pos MF hθ).ne'
  rw [dm_jcCurve]
  constructor
  · intro h
    have e : κ * (1 - β * (1 - ρ)) / (β * dm_q MF θ) = κ / dm_q MF θ * (1 - β * (1 - ρ)) / β := by
      field_simp
    rw [e, h, mul_div_cancel_left₀ _ hβ.ne']
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-- Miao, p. 592: the job creation curve slopes down in the `(θ, w)` plane. -/
theorem dm_jc_strictAntiOn (MF : DMMatchingFn) {A κ β ρ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hc : 0 < 1 - β * (1 - ρ)) :
    StrictAntiOn (fun θ ↦ dm_jcCurve MF A κ β ρ θ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hqx := dm_q_pos MF hx
  have hqy := dm_q_pos MF hy
  have hlt := dm_q_strictAntiOn MF hx hy hxy
  simp only [dm_jcCurve]
  have : κ * (1 - β * (1 - ρ)) / (β * dm_q MF x) < κ * (1 - β * (1 - ρ)) / (β * dm_q MF y) := by
    apply div_lt_div_of_pos_left (by positivity) (by positivity)
    exact mul_lt_mul_of_pos_left hlt hβ
  linarith

/-- Miao, (18.17), p. 592: the steady-state version of the wage equation (18.15). -/
theorem eq_18_17 (A b κ η w θ : ℝ) :
    w = η * (A + κ * θ) + (1 - η) * b ↔ w = dm_wageCurve A b κ η θ := Iff.rfl

/-- Miao, p. 593: the wage curve slopes up. -/
theorem dm_wc_strictMono {A b κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    StrictMono (fun θ ↦ dm_wageCurve A b κ η θ) := by
  intro x y hxy
  simp only [dm_wageCurve]
  have := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hxy hκ) hη
  nlinarith

/-- Miao, (18.18), p. 593: the steady state `(θ, w)` lies on both curves iff `θ` solves
`κ(1 − β(1 − ρ))/q(θ) + βηκθ = β(1 − η)(A − b)` and `w` is on the wage curve. -/
theorem eq_18_18 (MF : DMMatchingFn) (A b κ β ρ η w θ : ℝ) :
    (κ / dm_q MF θ * (1 - β * (1 - ρ)) = β * (A - w) ∧ w = dm_wageCurve A b κ η θ) ↔
      (dm_ssLHS MF κ β ρ η θ = β * (1 - η) * (A - b) ∧ w = dm_wageCurve A b κ η θ) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h2, dm_wageCurve] at h1
    rw [dm_ssLHS]
    linear_combination h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h2, dm_wageCurve]
    rw [dm_ssLHS] at h1
    linear_combination h1

/-- Miao, p. 593: at a solution of (18.18) the wage curve and the job creation curve meet. -/
theorem dm_wc_eq_jc (MF : DMMatchingFn) {A b κ β ρ η θ : ℝ} (hβ : 0 < β) (hθ : 0 < θ)
    (h : dm_ssLHS MF κ β ρ η θ = β * (1 - η) * (A - b)) :
    dm_wageCurve A b κ η θ = dm_jcCurve MF A κ β ρ θ := by
  have := ((eq_18_18 MF A b κ β ρ η (dm_wageCurve A b κ η θ) θ).mpr ⟨h, rfl⟩).1
  exact (dm_jc_iff MF hβ hθ).mp this

/-- Miao, p. 593: the left side of (18.18) is strictly increasing in `θ`. -/
theorem dm_ssLHS_strictMonoOn (MF : DMMatchingFn) {κ β ρ η : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hc : 0 < 1 - β * (1 - ρ)) :
    StrictMonoOn (fun θ ↦ dm_ssLHS MF κ β ρ η θ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hqx := dm_q_pos MF hx
  have hqy := dm_q_pos MF hy
  have hlt := dm_q_strictAntiOn MF hx hy hxy
  simp only [dm_ssLHS]
  have h1 : κ / dm_q MF x < κ / dm_q MF y := div_lt_div_of_pos_left hκ hqy hlt
  have h2 := mul_lt_mul_of_pos_right h1 hc
  have h3 : β * η * κ * x < β * η * κ * y := mul_lt_mul_of_pos_left hxy (by positivity)
  linarith

/-- Miao, p. 593: `θ*` is the **unique** solution of (18.18). -/
theorem dm_ss_unique (MF : DMMatchingFn) {A b κ β ρ η θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hc : 0 < 1 - β * (1 - ρ)) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (h₁ : dm_ssLHS MF κ β ρ η θ₁ = β * (1 - η) * (A - b))
    (h₂ : dm_ssLHS MF κ β ρ η θ₂ = β * (1 - η) * (A - b)) : θ₁ = θ₂ :=
  (dm_ssLHS_strictMonoOn MF hκ hβ hη hc).injOn hθ₁ hθ₂ (h₁.trans h₂.symm)

/-- Miao, p. 593: **existence** of a solution of (18.18), when the left side is below the right
side at some `θ₀ > 0` (by continuity of `q` and the intermediate value theorem). -/
theorem dm_ss_exists (MF : DMMatchingFn) {A b κ β ρ η θ₀ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hθ₀ : 0 < θ₀) (h₀ : dm_ssLHS MF κ β ρ η θ₀ < β * (1 - η) * (A - b))
    (hc : 0 < 1 - β * (1 - ρ)) :
    ∃ θ, 0 < θ ∧ dm_ssLHS MF κ β ρ η θ = β * (1 - η) * (A - b) := by
  set R := β * (1 - η) * (A - b)
  set T := max θ₀ (R / (β * η * κ))
  have hT : θ₀ ≤ T := le_max_left _ _
  have hk : 0 < β * η * κ := by positivity
  have hcont : ContinuousOn (fun θ ↦ dm_ssLHS MF κ β ρ η θ) (Set.Icc θ₀ T) := by
    have hq : ContinuousOn (dm_q MF) (Set.Icc θ₀ T) :=
      (dm_q_continuousOn MF).mono fun x hx ↦ lt_of_lt_of_le hθ₀ hx.1
    simp only [dm_ssLHS]
    refine ((continuousOn_const.div hq ?_).mul continuousOn_const).add
      (continuousOn_const.mul continuousOn_id)
    intro x hx
    exact (dm_q_pos MF (lt_of_lt_of_le hθ₀ hx.1)).ne'
  have hfT : R ≤ dm_ssLHS MF κ β ρ η T := by
    have hTpos : 0 < T := lt_of_lt_of_le hθ₀ hT
    have hq := dm_q_pos MF hTpos
    simp only [dm_ssLHS]
    have h1 : 0 ≤ κ / dm_q MF T * (1 - β * (1 - ρ)) := by positivity
    have h2 : R / (β * η * κ) ≤ T := le_max_right _ _
    have h3 : R ≤ β * η * κ * T := by
      rw [div_le_iff₀ hk] at h2; linarith
    linarith
  obtain ⟨θ, hθI, hθeq⟩ := intermediate_value_Icc hT hcont ⟨h₀.le, hfT⟩
  exact ⟨θ, lt_of_lt_of_le hθ₀ hθI.1, hθeq⟩

/-- Miao, p. 593 (correction): if `A ≤ b`, (18.18) has **no** solution `θ > 0`. -/
theorem dm_ss_not_exists (MF : DMMatchingFn) {A b κ β ρ η θ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hη1 : η < 1) (hc : 0 < 1 - β * (1 - ρ)) (hAb : A ≤ b) (hθ : 0 < θ) :
    dm_ssLHS MF κ β ρ η θ ≠ β * (1 - η) * (A - b) := by
  have hq := dm_q_pos MF hθ
  have h1 : 0 < dm_ssLHS MF κ β ρ η θ := by
    simp only [dm_ssLHS]; positivity
  have h2 : β * (1 - η) * (A - b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by linarith)
  intro h
  linarith

/-- Miao, p. 593: for Cobb–Douglas matching the left side of (18.18) is
`κ(1 − β(1 − ρ))θ^α/μ + βηκθ`. -/
theorem dm_cd_ssLHS {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1) {κ β ρ η θ : ℝ}
    (hθ : 0 < θ) :
    dm_ssLHS (dm_cdMatching μ α hμ hα0 hα1) κ β ρ η θ =
      κ * (1 - β * (1 - ρ)) * θ ^ α / μ + β * η * κ * θ := by
  rw [dm_ssLHS, dm_cd_q hμ hα0 hα1 hθ, Real.rpow_neg hθ.le]
  have : 0 < θ ^ α := by positivity
  field_simp

/-- Miao, p. 593: for Cobb–Douglas matching, (18.18) has a unique solution `θ* > 0` iff
`A > b` (the "if" part; the "only if" part is `dm_ss_not_exists`). -/
theorem dm_cd_ss_existsUnique {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1)
    {A b κ β ρ η : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hη : 0 < η) (hη1 : η < 1)
    (hc : 0 < 1 - β * (1 - ρ)) (hAb : b < A) :
    ∃! θ, 0 < θ ∧ dm_ssLHS (dm_cdMatching μ α hμ hα0 hα1) κ β ρ η θ =
      β * (1 - η) * (A - b) := by
  set MF := dm_cdMatching μ α hμ hα0 hα1
  set R := β * (1 - η) * (A - b) with hR
  have hRpos : 0 < R := by
    have : 0 < 1 - η := by linarith
    have : 0 < A - b := by linarith
    positivity
  set g : ℝ → ℝ := fun θ ↦ κ * (1 - β * (1 - ρ)) * θ ^ α / μ + β * η * κ * θ with hg
  have hk : 0 < β * η * κ := by positivity
  set T := R / (β * η * κ)
  have hTpos : 0 < T := div_pos hRpos hk
  have hcont : ContinuousOn g (Set.Icc 0 T) := by
    refine Continuous.continuousOn ?_
    exact ((continuous_const.mul (Real.continuous_rpow_const hα0.le)).div_const _).add
      (continuous_const.mul continuous_id)
  have hg0 : g 0 = 0 := by simp [hg, Real.zero_rpow hα0.ne']
  have hgT : R ≤ g T := by
    simp only [hg]
    have h1 : 0 ≤ κ * (1 - β * (1 - ρ)) * T ^ α / μ := by positivity
    have h3 : β * η * κ * T = R := by simp only [T]; field_simp
    linarith
  obtain ⟨θ, hθI, hθeq⟩ := intermediate_value_Icc hTpos.le hcont ⟨by rw [hg0]; exact hRpos.le, hgT⟩
  have hθpos : 0 < θ := by
    rcases hθI.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hg0] at hθeq; linarith
  refine ⟨θ, ⟨hθpos, ?_⟩, ?_⟩
  · rw [dm_cd_ssLHS hμ hα0 hα1 hθpos]; exact hθeq
  · rintro θ' ⟨hθ', h'⟩
    refine dm_ss_unique MF hκ hβ hη hc hθ' hθpos h' ?_
    rw [dm_cd_ssLHS hμ hα0 hα1 hθpos]; exact hθeq

/-- Miao, (18.19), p. 593: on the job creation line `v = θu`, the Beveridge relation
`ρ(1 − u) = M(u, v)` holds iff `u = ρ/(ρ + θq(θ))`. -/
theorem eq_18_19 (MF : DMMatchingFn) {ρ θ u : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) (hu : 0 < u) :
    ρ * (1 - u) = MF.M u (θ * u) ↔ u = dm_uStar MF ρ θ := by
  have hM : MF.M u (θ * u) = u * (θ * dm_q MF θ) := by
    rw [dm_M_eq_mul_q MF hu (mul_pos hθ hu)]
    have : θ * u / u = θ := by field_simp
    rw [this]; ring
  have hq := dm_q_pos MF hθ
  have hd : 0 < ρ + θ * dm_q MF θ := by positivity
  rw [hM, dm_uStar, eq_div_iff hd.ne']
  constructor <;> intro h <;> linarith

/-- Miao, p. 593: `0 < u* < 1`. -/
theorem dm_uStar_mem (MF : DMMatchingFn) {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) :
    0 < dm_uStar MF ρ θ ∧ dm_uStar MF ρ θ < 1 := by
  have hq := dm_q_pos MF hθ
  have hd : 0 < ρ + θ * dm_q MF θ := by positivity
  refine ⟨div_pos hρ hd, (div_lt_one hd).mpr ?_⟩
  have : 0 < θ * dm_q MF θ := by positivity
  linarith

/-- Miao, p. 593 (Figure 18.2): steady-state unemployment falls as `θ` rises (the job creation
line rotates anticlockwise along the Beveridge curve). -/
theorem dm_uStar_strictAntiOn (MF : DMMatchingFn) {ρ : ℝ} (hρ : 0 < ρ) :
    StrictAntiOn (fun θ ↦ dm_uStar MF ρ θ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have h := dm_jobFinding_strictMonoOn MF hx hy hxy
  have hqx := dm_q_pos MF hx
  simp only [dm_uStar] at h ⊢
  have hx' : 0 < ρ + x * dm_q MF x := by
    have : 0 < x * dm_q MF x := mul_pos hx hqx
    linarith
  exact div_lt_div_of_pos_left hρ hx' (by linarith)

/-- Miao, p. 593 (Figure 18.2): steady-state vacancies `v* = θu*` rise with `θ`. -/
theorem dm_vStar_strictMonoOn (MF : DMMatchingFn) {ρ : ℝ} (hρ : 0 < ρ) :
    StrictMonoOn (fun θ ↦ θ * dm_uStar MF ρ θ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have hqx := dm_q_pos MF hx0
  have hqy := dm_q_pos MF hy0
  have e : ∀ θ, 0 < θ → θ * dm_uStar MF ρ θ = ρ / (ρ / θ + dm_q MF θ) := by
    intro θ hθ
    have := dm_q_pos MF hθ
    rw [dm_uStar]
    field_simp
  simp only
  rw [e x hx0, e y hy0]
  have h1 : ρ / y < ρ / x := div_lt_div_of_pos_left hρ hx0 hxy
  have h2 := dm_q_strictAntiOn MF hx hy hxy
  apply div_lt_div_of_pos_left hρ (by positivity)
  linarith

/-- Miao, p. 593: an increase in `A` shifts the job creation curve up one-for-one and the wage
curve up by `η < 1`. -/
theorem dm_cs_shifts (MF : DMMatchingFn) (A b κ β ρ η θ Δ : ℝ) :
    dm_jcCurve MF (A + Δ) κ β ρ θ - dm_jcCurve MF A κ β ρ θ = Δ ∧
      dm_wageCurve (A + Δ) b κ η θ - dm_wageCurve A b κ η θ = η * Δ := by
  constructor
  · simp only [dm_jcCurve]; ring
  · simp only [dm_wageCurve]; ring

/-- Miao, p. 593: an increase in productivity `A` raises market tightness, the wage and
vacancies, and lowers unemployment. -/
theorem dm_cs_A (MF : DMMatchingFn) {A₁ A₂ b κ β ρ η θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hη1 : η < 1) (hρ : 0 < ρ) (hc : 0 < 1 - β * (1 - ρ)) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (h₁ : dm_ssLHS MF κ β ρ η θ₁ = β * (1 - η) * (A₁ - b))
    (h₂ : dm_ssLHS MF κ β ρ η θ₂ = β * (1 - η) * (A₂ - b)) (hA : A₁ < A₂) :
    θ₁ < θ₂ ∧ dm_wageCurve A₁ b κ η θ₁ < dm_wageCurve A₂ b κ η θ₂ ∧
      dm_uStar MF ρ θ₂ < dm_uStar MF ρ θ₁ ∧ θ₁ * dm_uStar MF ρ θ₁ < θ₂ * dm_uStar MF ρ θ₂ := by
  have hθ : θ₁ < θ₂ := by
    by_contra hcon
    have hle := (dm_ssLHS_strictMonoOn MF hκ hβ hη hc).monotoneOn hθ₂ hθ₁ (not_lt.mp hcon)
    have : β * (1 - η) * (A₁ - b) < β * (1 - η) * (A₂ - b) := by
      have : 0 < β * (1 - η) := mul_pos hβ (by linarith)
      nlinarith
    linarith
  refine ⟨hθ, ?_, dm_uStar_strictAntiOn MF hρ hθ₁ hθ₂ hθ,
    dm_vStar_strictMonoOn MF hρ hθ₁ hθ₂ hθ⟩
  simp only [dm_wageCurve]
  have := mul_lt_mul_of_pos_left hθ hκ
  nlinarith

/-- Miao, p. 593: an increase in the unemployment benefit `b` lowers market tightness and
vacancies and raises the wage and unemployment. -/
theorem dm_cs_b (MF : DMMatchingFn) {A b₁ b₂ κ β ρ η θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hη1 : η < 1) (hρ : 0 < ρ) (hc : 0 < 1 - β * (1 - ρ)) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (h₁ : dm_ssLHS MF κ β ρ η θ₁ = β * (1 - η) * (A - b₁))
    (h₂ : dm_ssLHS MF κ β ρ η θ₂ = β * (1 - η) * (A - b₂)) (hb : b₁ < b₂) :
    θ₂ < θ₁ ∧ dm_wageCurve A b₁ κ η θ₁ < dm_wageCurve A b₂ κ η θ₂ ∧
      dm_uStar MF ρ θ₁ < dm_uStar MF ρ θ₂ ∧ θ₂ * dm_uStar MF ρ θ₂ < θ₁ * dm_uStar MF ρ θ₁ := by
  have hθ : θ₂ < θ₁ := by
    by_contra hcon
    have hle := (dm_ssLHS_strictMonoOn MF hκ hβ hη hc).monotoneOn hθ₁ hθ₂ (not_lt.mp hcon)
    have : β * (1 - η) * (A - b₂) < β * (1 - η) * (A - b₁) := by
      have : 0 < β * (1 - η) := mul_pos hβ (by linarith)
      nlinarith
    linarith
  refine ⟨hθ, ?_, dm_uStar_strictAntiOn MF hρ hθ₂ hθ₁ hθ,
    dm_vStar_strictMonoOn MF hρ hθ₂ hθ₁ hθ⟩
  rw [dm_wc_eq_jc MF hβ hθ₁ h₁, dm_wc_eq_jc MF hβ hθ₂ h₂]
  exact dm_jc_strictAntiOn MF hκ hβ hc hθ₂ hθ₁ hθ

/-- Miao, p. 594: an increase in the worker's bargaining power `η` has the same effects as an
increase in `b` (when `A > b`): lower tightness and vacancies, higher wage and unemployment. -/
theorem dm_cs_eta (MF : DMMatchingFn) {A b κ β ρ η₁ η₂ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η₁) (hρ : 0 < ρ) (hc : 0 < 1 - β * (1 - ρ)) (hAb : b < A) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (h₁ : dm_ssLHS MF κ β ρ η₁ θ₁ = β * (1 - η₁) * (A - b))
    (h₂ : dm_ssLHS MF κ β ρ η₂ θ₂ = β * (1 - η₂) * (A - b)) (hη12 : η₁ < η₂) :
    θ₂ < θ₁ ∧ dm_wageCurve A b κ η₁ θ₁ < dm_wageCurve A b κ η₂ θ₂ ∧
      dm_uStar MF ρ θ₁ < dm_uStar MF ρ θ₂ ∧ θ₂ * dm_uStar MF ρ θ₂ < θ₁ * dm_uStar MF ρ θ₁ := by
  have hθ : θ₂ < θ₁ := by
    by_contra hcon
    have hle := (dm_ssLHS_strictMonoOn MF hκ hβ hη hc).monotoneOn hθ₁ hθ₂ (not_lt.mp hcon)
    simp only [dm_ssLHS] at hle h₁ h₂
    have hd : 0 < β * κ * θ₂ + β * (A - b) := by
      have : 0 < β * κ * θ₂ := by positivity
      have : 0 < β * (A - b) := mul_pos hβ (by linarith)
      linarith
    nlinarith
  refine ⟨hθ, ?_, dm_uStar_strictAntiOn MF hρ hθ₂ hθ₁ hθ,
    dm_vStar_strictMonoOn MF hρ hθ₂ hθ₁ hθ⟩
  rw [dm_wc_eq_jc MF hβ hθ₁ h₁, dm_wc_eq_jc MF hβ hθ₂ h₂]
  exact dm_jc_strictAntiOn MF hκ hβ hc hθ₂ hθ₁ hθ

/-- Miao, p. 592: the steady state `(θ*, w*, u*, v* = θ*u*)` (constant sequences, with
`N = 1 − u*` and `q^v = q(θ*)`) is a search equilibrium. -/
theorem dm_steady_isSearchEqm (MF : DMMatchingFn) {A b κ β ρ η θ : ℝ} (hρ : 0 < ρ)
    (hθ : 0 < θ) (h : dm_ssLHS MF κ β ρ η θ = β * (1 - η) * (A - b)) :
    dm_IsSearchEqm MF A b κ β ρ η (fun _ ↦ 1 - dm_uStar MF ρ θ) (fun _ ↦ dm_uStar MF ρ θ)
      (fun _ ↦ θ * dm_uStar MF ρ θ) (fun _ ↦ θ) (fun _ ↦ dm_wageCurve A b κ η θ)
      (fun _ ↦ dm_q MF θ) := by
  intro t
  obtain ⟨hu0, -⟩ := dm_uStar_mem MF hρ hθ
  have hB := (eq_18_19 MF hρ hθ hu0).mpr rfl
  have h16 := ((eq_18_18 MF A b κ β ρ η _ θ).mpr ⟨h, rfl⟩).1
  refine ⟨hu0, mul_pos hθ hu0, by field_simp, rfl, ?_, by ring, ?_, rfl⟩
  · simp only
    rw [← hB]; ring
  · exact (eq_18_16 MF A κ β ρ _ θ).mpr h16

/-- Miao, p. 592: a search equilibrium exists in a concrete economy (Cobb–Douglas matching with
`μ = 1`, `α = 1/2`; `A = 1`, `b = 0`, `κ = 1`, `β = ρ = η = 1/2`). -/
theorem dm_searchEqm_exists :
    ∃ N u v θ w qv : ℕ → ℝ, dm_IsSearchEqm (dm_cdMatching 1 (1 / 2) one_pos (by norm_num)
      (by norm_num)) 1 0 1 (1 / 2) (1 / 2) (1 / 2) N u v θ w qv := by
  obtain ⟨θ, ⟨hθ, h⟩, -⟩ := dm_cd_ss_existsUnique (μ := 1) (α := 1 / 2) one_pos (by norm_num)
    (by norm_num) (A := 1) (b := 0) (κ := 1) (β := 1 / 2) (ρ := 1 / 2) (η := 1 / 2) one_pos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, _, _, _, _, _, dm_steady_isSearchEqm _ (by norm_num) hθ h⟩

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §18.1: transitional dynamics — linearisation, saddle path and the phase diagram

Miao, §18.1, "Transitional Dynamics", pp. 594–596, equations (18.20)–(18.21) and Figures
18.3–18.4.

* `eq_18_20`: substituting the wage equation into (18.8) gives the dynamic job creation
  equation; `eq_18_21`: employment dynamics in terms of unemployment.
* `dm_lin_a11`: implicit differentiation of (18.20) at the steady state gives
  `dθ_{t+1}/dθ_t = a₁₁ = (q′/q²)/(β(1 − ρ)q′/q² + βη)`; `dm_a11_xi`:
  `a₁₁ = 1/(β(1 − ρ − ηθq/ξ))`; `dm_a11_gt_one`: `a₁₁ > 1` when `1 − ρ − ηθq/ξ > 0`.
* `dm_a21`, `dm_a21_sign`: `∂u_{t+1}/∂θ_t = −u q(θ)(1 − ξ(θ)) < 0`. **Correction**: the book
  prints `a₂₁ = uq(θ*)[1 − ξ(θ*)]` and says `a₂₁ > 0`; the sign is wrong (it does not affect the
  saddle-point conclusion, since the system is triangular).
* `dm_a22`, `dm_a22_mem`: `a₂₂ = 1 − ρ − q(θ*)θ* ∈ (−1, 1)` (for `ρ ∈ (0, 1)` and a job-finding
  probability `θq(θ) ∈ (0, 1]`).
* `dm_saddle_path`: the linearised system is a saddle: a solution with bounded `dθ` has
  `dθ_0 = 0`, hence `dθ_t = 0` for all `t` and `du_t → 0`.
* `dm_dtheta_locus`, `dm_du_locus`: the loci `Δθ = 0` (the horizontal line `θ = θ*`) and
  `Δu = 0` (`u = ρ/(ρ + θq(θ))`, downward sloping).
* `dm_uPath` and `dm_transition_isSearchEqm`: for any initial unemployment `u₀ ∈ (0, 1)`, the
  path with `θ_t = θ*` and `u_t` from (18.21) is a search equilibrium; `dm_uPath_sub`,
  `dm_uPath_tendsto`: `u_t − u* = a₂₂^t(u₀ − u*) → 0`; `dm_uPath_strictAnti`,
  `dm_vPath_strictAnti`, `dm_v0_gt`: when `a₂₂ > 0` and `u₀ > u*`, unemployment falls
  monotonically, vacancies jump above `v*` and fall.
* `dm_transition_not_monotone` (**correction**): when `a₂₂ < 0` the convergence oscillates; a
  concrete Cobb–Douglas economy satisfying the book's condition `1 − ρ − ηθq/ξ > 0` has
  `u₁ < u₂`, so "`u_t` falls until reaching the steady state" needs `1 − ρ − θ*q(θ*) ≥ 0`.
-/

namespace Miao.SearchAndMatching

open Filter Topology

/-- Miao, (18.20), p. 594: substituting the wage equation (18.15) into (18.8) gives the dynamic
job creation equation `κ/q(θ_t) = β((1 − η)(A − b) − ηκθ_{t+1} + (1 − ρ)κ/q(θ_{t+1}))`. -/
theorem eq_18_20 (MF : DMMatchingFn) {A b κ β ρ η : ℝ} {θ w : ℕ → ℝ} (t : ℕ)
    (h8 : κ / dm_q MF (θ t) = β * (A - w (t + 1) + (1 - ρ) * κ / dm_q MF (θ (t + 1))))
    (h15 : w (t + 1) = η * (A + κ * θ (t + 1)) + (1 - η) * b) :
    κ / dm_q MF (θ t) =
      β * ((1 - η) * (A - b) - η * κ * θ (t + 1) + (1 - ρ) * κ / dm_q MF (θ (t + 1))) := by
  rw [h8, h15]; ring

/-- Miao, (18.21), p. 594: by (18.1)–(18.3), `u_{t+1} = (1 − ρ − q(θ_t)θ_t)u_t + ρ`. -/
theorem eq_18_21 (MF : DMMatchingFn) {ρ : ℝ} {N u v θ : ℕ → ℝ} (t : ℕ) (hu : 0 < u t)
    (hv : 0 < v t) (hθ : θ t = v t / u t)
    (h2 : N (t + 1) = (1 - ρ) * N t + MF.M (u t) (v t)) (h3 : ∀ t, u t = 1 - N t) :
    u (t + 1) = (1 - ρ - dm_q MF (θ t) * θ t) * u t + ρ := by
  have hM : MF.M (u t) (v t) = dm_q MF (θ t) * θ t * u t := by
    rw [dm_M_eq_mul_q MF hu hv, hθ]
    field_simp
  rw [h3 (t + 1), h2, hM, h3 t]
  ring

/-- Miao, p. 595: the coefficient `a₁₁ = (q′/q²)/(β(1 − ρ)q′/q² + βη)`, written in terms of
`qd = q′(θ*)/q(θ*)²`. -/
noncomputable def dm_a11 (β ρ η qd : ℝ) : ℝ := qd / (β * (1 - ρ) * qd + β * η)

/-- Miao, p. 595: **linearisation of (18.20)**. If the dynamic job creation equation defines
`θ_{t+1} = g(θ_t)` near the steady state `θ* = g(θ*)`, with `g` and `q` differentiable at `θ*`,
then `g′(θ*) = a₁₁`. -/
theorem dm_lin_a11 (MF : DMMatchingFn) {A b κ β ρ η θs q' g' : ℝ} {g : ℝ → ℝ} (hθ : 0 < θs)
    (hκ : κ ≠ 0) (hg0 : g θs = θs) (hg : HasDerivAt g g' θs)
    (hq : HasDerivAt (dm_q MF) q' θs)
    (hD : β * (1 - ρ) * (q' / dm_q MF θs ^ 2) + β * η ≠ 0)
    (hid : ∀ᶠ θ in 𝓝 θs, κ / dm_q MF θ =
      β * ((1 - η) * (A - b) - η * κ * g θ + (1 - ρ) * κ / dm_q MF (g θ))) :
    g' = dm_a11 β ρ η (q' / dm_q MF θs ^ 2) := by
  have hq0 : dm_q MF θs ≠ 0 := (dm_q_pos MF hθ).ne'
  have hL := (hasDerivAt_const θs κ).div hq hq0
  have hq'' : HasDerivAt (dm_q MF) q' (g θs) := by rw [hg0]; exact hq
  have hqg := hq''.comp θs hg
  have hqg0 : (dm_q MF ∘ g) θs ≠ 0 := by simp only [Function.comp_apply, hg0]; exact hq0
  have hR1 := (hasDerivAt_const θs ((1 - ρ) * κ)).div hqg hqg0
  have hR := (((hasDerivAt_const θs ((1 - η) * (A - b))).sub
    (hg.const_mul (η * κ))).add hR1).const_mul β
  have hR' := hR.congr_of_eventuallyEq hid
  have heq := hL.unique hR'
  simp only [Function.comp_apply, hg0, zero_mul, zero_sub] at heq
  rw [dm_a11, eq_div_iff hD]
  field_simp at heq ⊢
  linear_combination heq

/-- Miao, p. 595: with `ξ = −θq′/q`, `a₁₁ = 1/(β(1 − ρ − ηθq(θ)/ξ))`. -/
theorem dm_a11_xi {β ρ η θ q q' : ℝ} (hθ : 0 < θ) (hq : 0 < q) (hξ : 0 < -θ * q' / q)
    (hc : 1 - ρ - η * θ * q / (-θ * q' / q) ≠ 0) (hβ : β ≠ 0) :
    dm_a11 β ρ η (q' / q ^ 2) = 1 / (β * (1 - ρ - η * θ * q / (-θ * q' / q))) := by
  have hq' : q' ≠ 0 := by
    intro h; rw [h] at hξ; simp at hξ
  rw [dm_a11]
  have hc' : (1 - ρ) * q' + η * q ^ 2 ≠ 0 := by
    intro h
    apply hc
    field_simp
    linear_combination h
  field_simp
  ring

/-- Miao, p. 595: if `1 − ρ − ηq(θ*)θ*/ξ(θ*) > 0` then `a₁₁ > 1`. -/
theorem dm_a11_gt_one {β ρ c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : 0 ≤ ρ) (hc : 0 < c)
    (hc1 : c ≤ 1 - ρ) : 1 < 1 / (β * c) := by
  have h1 : β * c < 1 := by nlinarith
  rw [lt_div_iff₀ (mul_pos hβ0 hc)]
  linarith

/-- Miao, p. 595: `∂u_{t+1}/∂θ_t = −u q(θ*)(1 − ξ(θ*))` for (18.21). -/
theorem dm_a21 (MF : DMMatchingFn) {ρ θs u q' : ℝ} (hθ : 0 < θs)
    (hq : HasDerivAt (dm_q MF) q' θs) :
    HasDerivAt (fun θ ↦ (1 - ρ - dm_q MF θ * θ) * u + ρ)
      (-u * dm_q MF θs * (1 - dm_xi MF θs)) θs := by
  have h := dm_jobFinding_hasDerivAt MF hθ hq
  have h2 := ((h.const_sub (1 - ρ)).mul_const u).add_const ρ
  have e : (fun θ ↦ (1 - ρ - dm_q MF θ * θ) * u + ρ) =
      (fun θ ↦ (1 - ρ - θ * dm_q MF θ) * u + ρ) := by
    funext θ; ring
  rw [e]
  convert h2 using 1
  ring

/-- Miao, p. 595 (**correction**): `a₂₁ = −uq(θ*)(1 − ξ(θ*)) < 0`, whereas the book's printed
`uq(θ*)(1 − ξ(θ*))` is positive. -/
theorem dm_a21_sign (MF : DMMatchingFn) {θs u d : ℝ} (hθ : 0 < θs) (hu : 0 < u)
    (hd : HasDerivAt (fun x ↦ MF.M x 1) d θs⁻¹) :
    -u * dm_q MF θs * (1 - dm_xi MF θs) < 0 ∧ 0 < u * dm_q MF θs * (1 - dm_xi MF θs) := by
  have hq := dm_q_pos MF hθ
  have hξ := (dm_xi_mem MF hθ hd).2
  have : 0 < u * dm_q MF θs * (1 - dm_xi MF θs) := by
    have : 0 < 1 - dm_xi MF θs := by linarith
    positivity
  constructor <;> linarith

/-- Miao, p. 595: `∂u_{t+1}/∂u_t = a₂₂ = 1 − ρ − q(θ*)θ*`. -/
theorem dm_a22 {ρ q θ u : ℝ} :
    HasDerivAt (fun x ↦ (1 - ρ - q * θ) * x + ρ) (1 - ρ - q * θ) u := by
  simpa using ((hasDerivAt_id u).const_mul (1 - ρ - q * θ)).add_const ρ

/-- Miao, p. 595: `a₂₂ ∈ (−1, 1)` when `ρ ∈ (0, 1)` and the job-finding probability
`θ*q(θ*) ∈ (0, 1]`. -/
theorem dm_a22_mem {ρ jf : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hjf0 : 0 < jf) (hjf1 : jf ≤ 1) :
    -1 < 1 - ρ - jf ∧ 1 - ρ - jf < 1 := by
  constructor <;> linarith

/-- Miao, p. 595: the linearised system `dθ_{t+1} = a₁₁dθ_t`,
`du_{t+1} = a₂₁dθ_t + a₂₂du_t` with `|a₁₁| > 1 > |a₂₂|` is a **saddle**: (i) a solution with
bounded `dθ` has `dθ_0 = 0`; (ii) then `dθ_t = 0` for all `t` (`θ_t` constant) and
`du_t → 0`. -/
theorem dm_saddle_path {a₁₁ a₂₁ a₂₂ : ℝ} {x y : ℕ → ℝ} (h1 : 1 < |a₁₁|) (h2 : |a₂₂| < 1)
    (hx : ∀ t, x (t + 1) = a₁₁ * x t) (hy : ∀ t, y (t + 1) = a₂₁ * x t + a₂₂ * y t) :
    ((∃ C, ∀ t, |x t| ≤ C) → x 0 = 0) ∧
      (x 0 = 0 → (∀ t, x t = 0) ∧ Tendsto y atTop (𝓝 0)) := by
  have hxt : ∀ t, x t = a₁₁ ^ t * x 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hx n, ih, pow_succ]; ring
  refine ⟨?_, ?_⟩
  · rintro ⟨C, hC⟩
    by_contra h0
    have hpos : 0 < |x 0| := abs_pos.mpr h0
    have ht := tendsto_pow_atTop_atTop_of_one_lt h1
    obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop (C / |x 0|)).exists
    have := hC n
    rw [hxt n, abs_mul, abs_pow] at this
    rw [div_lt_iff₀ hpos] at hn
    linarith
  · intro h0
    have hx0 : ∀ t, x t = 0 := fun t ↦ by rw [hxt t, h0, mul_zero]
    refine ⟨hx0, ?_⟩
    have hyt : ∀ t, y t = a₂₂ ^ t * y 0 := by
      intro t
      induction t with
      | zero => simp
      | succ n ih => rw [hy n, hx0 n, ih, pow_succ]; ring
    have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h2).mul_const (y 0)
    rw [zero_mul] at this
    exact this.congr fun t ↦ (hyt t).symm

/-- Miao, p. 595 (Figure 18.3): the locus `Δθ_t = 0`: a constant `θ_{t+1} = θ_t = θ` satisfies
(18.20) iff `θ` solves (18.18); so the locus is the horizontal line `θ = θ*`. -/
theorem dm_dtheta_locus (MF : DMMatchingFn) {A b κ β ρ η θ θs : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hη : 0 < η) (hc : 0 < 1 - β * (1 - ρ)) (hθ : 0 < θ) (hθs : 0 < θs)
    (hs : dm_ssLHS MF κ β ρ η θs = β * (1 - η) * (A - b)) :
    κ / dm_q MF θ = β * ((1 - η) * (A - b) - η * κ * θ + (1 - ρ) * κ / dm_q MF θ) ↔
      θ = θs := by
  constructor
  · intro h
    refine dm_ss_unique MF hκ hβ hη hc hθ hθs ?_ hs
    rw [dm_ssLHS]
    have e : (1 - ρ) * κ / dm_q MF θ = (1 - ρ) * (κ / dm_q MF θ) := by ring
    rw [e] at h
    linear_combination h
  · rintro rfl
    rw [dm_ssLHS] at hs
    have e : (1 - ρ) * κ / dm_q MF θ = (1 - ρ) * (κ / dm_q MF θ) := by ring
    rw [e]
    linear_combination hs

/-- Miao, p. 595 (Figure 18.3): the locus `Δu_t = 0` of (18.21) is `u = ρ/(ρ + θq(θ))`, which
is downward sloping in `θ` (`dm_uStar_strictAntiOn`). -/
theorem dm_du_locus (MF : DMMatchingFn) {ρ θ u : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) :
    (1 - ρ - dm_q MF θ * θ) * u + ρ = u ↔ u = dm_uStar MF ρ θ := by
  have hq := dm_q_pos MF hθ
  have hd : 0 < ρ + θ * dm_q MF θ := by positivity
  rw [dm_uStar, eq_div_iff hd.ne']
  constructor <;> intro h <;> linarith

/-- Miao, p. 595: the unemployment path of (18.21) at a constant job-finding rate `jf`:
`u_t = u* + (1 − ρ − jf)^t(u₀ − u*)`, `u* = ρ/(ρ + jf)`. -/
noncomputable def dm_uPath (ρ jf u₀ : ℝ) (t : ℕ) : ℝ :=
  ρ / (ρ + jf) + (1 - ρ - jf) ^ t * (u₀ - ρ / (ρ + jf))

/-- Miao, (18.21), p. 594: `dm_uPath` solves `u_{t+1} = (1 − ρ − jf)u_t + ρ` with `u_0 = u₀`. -/
theorem dm_uPath_rec {ρ jf u₀ : ℝ} (hd : ρ + jf ≠ 0) (t : ℕ) :
    dm_uPath ρ jf u₀ 0 = u₀ ∧
      dm_uPath ρ jf u₀ (t + 1) = (1 - ρ - jf) * dm_uPath ρ jf u₀ t + ρ := by
  refine ⟨by simp [dm_uPath], ?_⟩
  simp only [dm_uPath, pow_succ]
  field_simp
  ring

/-- Miao, p. 595: `u_t − u* = a₂₂^t(u₀ − u*)`. -/
theorem dm_uPath_sub (ρ jf u₀ : ℝ) (t : ℕ) :
    dm_uPath ρ jf u₀ t - ρ / (ρ + jf) = (1 - ρ - jf) ^ t * (u₀ - ρ / (ρ + jf)) := by
  simp [dm_uPath]

/-- Miao, p. 595: along the saddle path unemployment converges to `u*`. -/
theorem dm_uPath_tendsto {ρ jf u₀ : ℝ} (h : |1 - ρ - jf| < 1) :
    Tendsto (dm_uPath ρ jf u₀) atTop (𝓝 (ρ / (ρ + jf))) := by
  have := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).mul_const
    (u₀ - ρ / (ρ + jf))).const_add (ρ / (ρ + jf))
  rw [zero_mul, add_zero] at this
  exact this

/-- Miao, p. 595: the unemployment path stays in `(0, 1)` when `ρ ∈ (0, 1)`,
`jf ∈ (0, 1]` and `u₀ ∈ (0, 1)`. -/
theorem dm_uPath_mem {ρ jf u₀ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hjf0 : 0 < jf)
    (hjf1 : jf ≤ 1) (hu0 : 0 < u₀) (hu1 : u₀ < 1) (t : ℕ) :
    0 < dm_uPath ρ jf u₀ t ∧ dm_uPath ρ jf u₀ t < 1 := by
  have hd : ρ + jf ≠ 0 := by linarith
  induction t with
  | zero => rw [(dm_uPath_rec hd 0).1]; exact ⟨hu0, hu1⟩
  | succ n ih =>
    rw [(dm_uPath_rec hd n).2]
    obtain ⟨h0, h1⟩ := ih
    rcases le_or_gt 0 (1 - ρ - jf) with ha | ha
    · constructor <;> nlinarith
    · constructor <;> nlinarith

/-- Miao, p. 595 (Figure 18.3): if `a₂₂ = 1 − ρ − jf ∈ (0, 1)` and `u₀ > u*`, unemployment falls
monotonically towards the steady state. -/
theorem dm_uPath_strictAnti {ρ jf u₀ : ℝ} (ha0 : 0 < 1 - ρ - jf) (ha1 : 1 - ρ - jf < 1)
    (hu : ρ / (ρ + jf) < u₀) : StrictAnti (dm_uPath ρ jf u₀) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  simp only [dm_uPath, pow_succ]
  have hp : 0 < (1 - ρ - jf) ^ n := pow_pos ha0 n
  have hd : 0 < u₀ - ρ / (ρ + jf) := by linarith
  have : 0 < (1 - ρ - jf) ^ n * (u₀ - ρ / (ρ + jf)) := mul_pos hp hd
  nlinarith

/-- Miao, p. 595 (Figure 18.4): vacancies `v_t = θ*u_t` fall monotonically along the path. -/
theorem dm_vPath_strictAnti {ρ jf u₀ θs : ℝ} (hθ : 0 < θs) (ha0 : 0 < 1 - ρ - jf)
    (ha1 : 1 - ρ - jf < 1) (hu : ρ / (ρ + jf) < u₀) :
    StrictAnti (fun t ↦ θs * dm_uPath ρ jf u₀ t) := fun _ _ hmn ↦
  mul_lt_mul_of_pos_left (dm_uPath_strictAnti ha0 ha1 hu hmn) hθ

/-- Miao, p. 595 (Figure 18.4): "vacancy initially jumps higher than its steady state value":
`v₀ = θ*u₀ > θ*u* = v*` when `u₀ > u*`. -/
theorem dm_v0_gt {ρ jf u₀ θs : ℝ} (hθ : 0 < θs) (hu : ρ / (ρ + jf) < u₀) :
    θs * (ρ / (ρ + jf)) < θs * dm_uPath ρ jf u₀ 0 := by
  simp only [dm_uPath, pow_zero, one_mul]
  nlinarith

/-- Miao, p. 595: **the transition path is a search equilibrium**. Given `θ*` solving (18.18),
`ρ ∈ (0, 1)`, `θ*q(θ*) ≤ 1` and any initial unemployment `u₀ ∈ (0, 1)`, market tightness jumps
to `θ*` and stays there, `u_t` follows (18.21), `v_t = θ*u_t`, `N_t = 1 − u_t` and the wage is
constant; this is a search equilibrium. -/
theorem dm_transition_isSearchEqm (MF : DMMatchingFn) {A b κ β ρ η θs u₀ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hθ : 0 < θs) (hjf : θs * dm_q MF θs ≤ 1) (hu0 : 0 < u₀) (hu1 : u₀ < 1)
    (h : dm_ssLHS MF κ β ρ η θs = β * (1 - η) * (A - b)) :
    dm_IsSearchEqm MF A b κ β ρ η (fun t ↦ 1 - dm_uPath ρ (θs * dm_q MF θs) u₀ t)
      (dm_uPath ρ (θs * dm_q MF θs) u₀) (fun t ↦ θs * dm_uPath ρ (θs * dm_q MF θs) u₀ t)
      (fun _ ↦ θs) (fun _ ↦ dm_wageCurve A b κ η θs) (fun _ ↦ dm_q MF θs) := by
  intro t
  have hq := dm_q_pos MF hθ
  have hjf0 : 0 < θs * dm_q MF θs := mul_pos hθ hq
  have hd : ρ + θs * dm_q MF θs ≠ 0 := by linarith
  obtain ⟨hut, -⟩ := dm_uPath_mem hρ0 hρ1 hjf0 hjf hu0 hu1 t
  have h16 := ((eq_18_18 MF A b κ β ρ η _ θs).mpr ⟨h, rfl⟩).1
  refine ⟨hut, mul_pos hθ hut, by field_simp, rfl, ?_, by ring, ?_, rfl⟩
  · simp only
    rw [dm_M_eq_mul_q MF hut (mul_pos hθ hut), (dm_uPath_rec hd t).2]
    have : θs * dm_uPath ρ (θs * dm_q MF θs) u₀ t / dm_uPath ρ (θs * dm_q MF θs) u₀ t = θs := by
      field_simp
    rw [this]
    ring
  · exact (eq_18_16 MF A κ β ρ _ θs).mpr h16

/-- Miao, p. 595 (**correction**): a concrete economy (Cobb–Douglas matching `μ = α = 3/4`;
`A = 3`, `b = 0`, `κ = 1`, `β = ρ = 1/2`, `η = 1/4`) has steady state `θ* = 1`, satisfies the
book's condition `1 − ρ − ηθ*q(θ*)/ξ(θ*) = 1/4 > 0` (so `a₁₁ > 1`) and has job-finding
probability `θ*q(θ*) = 3/4 ≤ 1`, but `a₂₂ = −1/4 < 0`: starting from `u₀ = 1/2 > u* = 2/5`,
unemployment overshoots, `u₁ < u*` and `u₁ < u₂`, so it does not fall monotonically. -/
theorem dm_transition_not_monotone :
    let MF := dm_cdMatching (3 / 4) (3 / 4) (by norm_num) (by norm_num) (by norm_num)
    dm_ssLHS MF 1 (1 / 2) (1 / 2) (1 / 4) 1 = 1 / 2 * (1 - 1 / 4) * (3 - 0) ∧
      0 < 1 - 1 / 2 - 1 / 4 * 1 * dm_q MF 1 / dm_xi MF 1 ∧ 1 * dm_q MF 1 ≤ 1 ∧
      1 - 1 / 2 - 1 * dm_q MF 1 = -1 / 4 ∧
      dm_uPath (1 / 2) (1 * dm_q MF 1) (1 / 2) 1 < 1 / 2 / (1 / 2 + 1 * dm_q MF 1) ∧
      dm_uPath (1 / 2) (1 * dm_q MF 1) (1 / 2) 1 < dm_uPath (1 / 2) (1 * dm_q MF 1) (1 / 2) 2 := by
  intro MF
  have hq : dm_q MF 1 = 3 / 4 := by
    rw [dm_cd_q (by norm_num) (by norm_num) (by norm_num) one_pos]; simp
  have hξ : dm_xi MF 1 = 3 / 4 := dm_cd_xi (by norm_num) (by norm_num) (by norm_num) one_pos
  have hs : dm_ssLHS MF 1 (1 / 2) (1 / 2) (1 / 4) 1 = 9 / 8 := by
    rw [dm_ssLHS, hq]; norm_num
  rw [hs, hq, hξ]
  simp only [dm_uPath]
  norm_num

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §18.1: large firms

Miao, §18.1, "Large Firms", pp. 596–598, equations (18.22)–(18.27).

* `dm_firmProfit`, `dm_FirmFeasible`, `dm_FirmOptimal`: the firm's problem
  `max Σ βᵗ(F_t(N_t) − w_tN_t − κv_t)` subject to (18.22) `N_{t+1} = (1 − ρ)N_t + q^v_tv_t`,
  `v_t ≥ 0`. Departure: optimality is against plans that differ in finitely many periods (the
  comparison of the infinite sums reduces to a finite sum). `F_t(N) = AN` in the book; a general
  differentiable `F_t` is allowed (it is used in Exercise 18.1).
* `dm_firm_euler`: an optimal plan with positive vacancies at `t, t + 1` satisfies
  `κ/q^v_t = β(F′_{t+1}(N_{t+1}) − w_{t+1} + (1 − ρ)κ/q^v_{t+1})`; with `F_t(N) = AN` this is
  (18.8) (`dm_largeFirm_eq_18_8`). Proof: a one-period perturbation of `N_{t+1}` financed by
  `v_t`, `v_{t+1}`, and Fermat's theorem.
* `dm_firmOptimal_of_euler`: conversely, when (18.8) holds every feasible plan is optimal (the
  firm is indifferent over vacancies: (18.23) plays the role of free entry); with
  `dm_firmOptimal_exists` this shows `dm_FirmOptimal` is satisfiable.
* `eq_18_23`: combining the first-order conditions (18.23) gives (18.8).
* `dm_aggregate_18_2`: aggregating (18.22) over a unit measure of firms gives (18.2).
* `eq_18_24`: with an affine continuation value and the vacancy first-order condition, the
  Bellman right side is independent of `v` and `∂J_t/∂N = A − w_t + (1 − ρ)κ/q^v_t = J^F_t`.
* `dm_Jn`: the marginal value of `ε` extra workers paid `w`, `J_n(w, t) = (w_t − w) + ∂J_t/∂N`
  (18.25).
* `eq_18_26`, `eq_18_27`: the large-firm bargaining problems are equivalent to (18.11).
-/

namespace Miao.SearchAndMatching

open Filter Topology MeasureTheory

/-- Miao, p. 597: the large firm's period profit `F_t(N_t) − w_tN_t − κv_t`. -/
def dm_firmProfit (F : ℕ → ℝ → ℝ) (w : ℕ → ℝ) (κ : ℝ) (N v : ℕ → ℝ) (t : ℕ) : ℝ :=
  F t (N t) - w t * N t - κ * v t

/-- Miao, (18.22), p. 596: a feasible employment–vacancy plan. -/
def dm_FirmFeasible (ρ : ℝ) (qv N v : ℕ → ℝ) : Prop :=
  ∀ t, N (t + 1) = (1 - ρ) * N t + qv t * v t ∧ 0 ≤ v t

/-- Miao, p. 597: an optimal plan of the large firm: feasible, and no feasible plan with the same
`N₀` that coincides with it from some date `T` on yields a higher discounted profit. -/
def dm_FirmOptimal (F : ℕ → ℝ → ℝ) (w : ℕ → ℝ) (κ β ρ : ℝ) (qv N v : ℕ → ℝ) : Prop :=
  dm_FirmFeasible ρ qv N v ∧ ∀ (T : ℕ) (N' v' : ℕ → ℝ), dm_FirmFeasible ρ qv N' v' →
    N' 0 = N 0 → (∀ t, T ≤ t → N' t = N t ∧ v' t = v t) →
      ∑ t ∈ Finset.range T, β ^ t * dm_firmProfit F w κ N' v' t ≤
        ∑ t ∈ Finset.range T, β ^ t * dm_firmProfit F w κ N v t

/-- Miao, (18.23), p. 597: an optimal plan of the large firm with `v_t, v_{t+1} > 0` satisfies
the job creation (Euler) equation `κ/q^v_t = β(F′_{t+1}(N_{t+1}) − w_{t+1} + (1 − ρ)κ/q^v_{t+1})`.
-/
theorem dm_firm_euler {F : ℕ → ℝ → ℝ} {w qv N v : ℕ → ℝ} {κ β ρ Fn : ℝ}
    (hopt : dm_FirmOptimal F w κ β ρ qv N v) (t : ℕ) (hβ : 0 < β) (hq : 0 < qv t)
    (hq1 : 0 < qv (t + 1)) (hv : 0 < v t) (hv1 : 0 < v (t + 1))
    (hF : HasDerivAt (F (t + 1)) Fn (N (t + 1))) :
    κ / qv t = β * (Fn - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) := by
  obtain ⟨hfeas, hbest⟩ := hopt
  set N' : ℝ → ℕ → ℝ := fun ε s ↦ N s + if s = t + 1 then ε else 0 with hN'
  set v' : ℝ → ℕ → ℝ := fun ε s ↦ v s + (if s = t then ε / qv t else 0) -
    (if s = t + 1 then (1 - ρ) * ε / qv (t + 1) else 0) with hv'
  set φ : ℝ → ℝ := fun ε ↦ β ^ t * -(κ * ε / qv t) + β ^ (t + 1) *
    (F (t + 1) (N (t + 1) + ε) - F (t + 1) (N (t + 1)) - w (t + 1) * ε +
      κ * ((1 - ρ) * ε / qv (t + 1))) with hφ
  have ht1 : t ≠ t + 1 := by omega
  have ht2 : t + 1 ≠ t := by omega
  have ht3 : t + 1 + 1 ≠ t + 1 := by omega
  -- the deviation changes the finite sum by `φ ε`
  have hsum : ∀ ε, ∑ s ∈ Finset.range (t + 1 + 1), β ^ s * dm_firmProfit F w κ (N' ε) (v' ε) s =
      ∑ s ∈ Finset.range (t + 1 + 1), β ^ s * dm_firmProfit F w κ N v s + φ ε := by
    intro ε
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := t + 1),
      Finset.sum_range_succ]
    have hlow : ∑ s ∈ Finset.range t, β ^ s * dm_firmProfit F w κ (N' ε) (v' ε) s =
        ∑ s ∈ Finset.range t, β ^ s * dm_firmProfit F w κ N v s := by
      refine Finset.sum_congr rfl fun s hs ↦ ?_
      have hs' := Finset.mem_range.mp hs
      have h1 : s ≠ t + 1 := by omega
      have h2 : s ≠ t := by omega
      simp [dm_firmProfit, hN', hv', h1, h2]
    rw [hlow]
    generalize ∑ s ∈ Finset.range t, β ^ s * dm_firmProfit F w κ N v s = S
    simp only [dm_firmProfit, hN', hv', hφ, ht1, ht2, ↓reduceIte, add_zero, sub_zero]
    ring
  -- the deviation is feasible for small `ε`
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < v t + ε / qv t ∧
      0 < v (t + 1) - (1 - ρ) * ε / qv (t + 1) := by
    have c1 : ContinuousAt (fun ε : ℝ ↦ v t + ε / qv t) 0 := by fun_prop
    have c2 : ContinuousAt (fun ε : ℝ ↦ v (t + 1) - (1 - ρ) * ε / qv (t + 1)) 0 := by fun_prop
    have e1 := c1.eventually (lt_mem_nhds (show (0 : ℝ) < v t + 0 / qv t by simpa using hv))
    have e2 := c2.eventually
      (lt_mem_nhds (show (0 : ℝ) < v (t + 1) - (1 - ρ) * 0 / qv (t + 1) by simpa using hv1))
    filter_upwards [e1, e2] with ε h1 h2 using ⟨h1, h2⟩
  have hmax : IsLocalMax φ 0 := by
    filter_upwards [hev] with ε hε
    have hφ0 : φ 0 = 0 := by simp [hφ]
    rw [hφ0]
    have hfe : dm_FirmFeasible ρ qv (N' ε) (v' ε) := by
      intro s
      rcases eq_or_ne s t with rfl | hst
      · refine ⟨?_, ?_⟩
        · simp only [hN', hv', ht1, ↓reduceIte, add_zero, sub_zero]
          rw [(hfeas s).1]
          field_simp
          ring
        · simp only [hv', ht1, ↓reduceIte, sub_zero]; exact hε.1.le
      rcases eq_or_ne s (t + 1) with rfl | hst1
      · refine ⟨?_, ?_⟩
        · simp only [hN', hv', ht2, ht3, ↓reduceIte, add_zero]
          rw [(hfeas (t + 1)).1]
          field_simp
          ring
        · simp only [hv', ht2, ↓reduceIte, add_zero]; exact hε.2.le
      · have h1 : s + 1 ≠ t + 1 := by omega
        simp only [hN', hv', hst, hst1, h1, ↓reduceIte, add_zero, sub_zero]
        exact hfeas s
    have h0 : N' ε 0 = N 0 := by simp [hN']
    have hag : ∀ s, t + 1 + 1 ≤ s → N' ε s = N s ∧ v' ε s = v s := by
      intro s hs
      have h1 : s ≠ t + 1 := by omega
      have h2 : s ≠ t := by omega
      simp [hN', hv', h1, h2]
    have := hbest (t + 1 + 1) (N' ε) (v' ε) hfe h0 hag
    rw [hsum ε] at this
    linarith
  -- Fermat's theorem
  have h2 : HasDerivAt (fun ε : ℝ ↦ N (t + 1) + ε) 1 0 := (hasDerivAt_id' 0).const_add _
  have hF' : HasDerivAt (F (t + 1)) Fn (N (t + 1) + 0) := by rwa [add_zero]
  have hFc : HasDerivAt (fun ε ↦ F (t + 1) (N (t + 1) + ε)) (Fn * 1) 0 := hF'.comp 0 h2
  have hid := hasDerivAt_id' (0 : ℝ)
  have hd : HasDerivAt φ (β ^ t * -(κ * 1 / qv t) + β ^ (t + 1) *
      (Fn * 1 - w (t + 1) * 1 + κ * ((1 - ρ) * 1 / qv (t + 1)))) 0 :=
    (((hid.const_mul κ).div_const (qv t)).neg.const_mul (β ^ t)).add
      ((((hFc.sub_const (F (t + 1) (N (t + 1)))).sub (hid.const_mul (w (t + 1)))).add
        (((hid.const_mul (1 - ρ)).div_const (qv (t + 1))).const_mul κ)).const_mul (β ^ (t + 1)))
  have hz := hmax.hasDerivAt_eq_zero hd
  have hbt : 0 < β ^ t := pow_pos hβ t
  have key : β ^ t * (β * (Fn - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) - κ / qv t) = 0 := by
    rw [pow_succ] at hz
    linear_combination hz
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hbt.ne'
  · linarith

/-- Miao, p. 597: for the large firm with `F_t(N) = AN`, an optimal plan with positive vacancies
satisfies (18.8), "identical to" the small-firm job creation equation. -/
theorem dm_largeFirm_eq_18_8 {w qv N v : ℕ → ℝ} {A κ β ρ : ℝ}
    (hopt : dm_FirmOptimal (fun _ n ↦ A * n) w κ β ρ qv N v) (t : ℕ) (hβ : 0 < β)
    (hq : 0 < qv t) (hq1 : 0 < qv (t + 1)) (hv : 0 < v t) (hv1 : 0 < v (t + 1)) :
    κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) :=
  dm_firm_euler hopt t hβ hq hq1 hv hv1 (by simpa using (hasDerivAt_id' (N (t + 1))).const_mul A)

/-- Miao, p. 597: conversely, if (18.8) holds at every date, every feasible plan of the large
firm (with `F_t(N) = AN`) is optimal: the firm is indifferent over its vacancies, and (18.23)
determines aggregate vacancies as the free entry condition (18.6) does. -/
theorem dm_firmOptimal_of_euler {w qv N v : ℕ → ℝ} {A κ β ρ : ℝ} (hq : ∀ t, qv t ≠ 0)
    (h8 : ∀ t, κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)))
    (hfeas : dm_FirmFeasible ρ qv N v) :
    dm_FirmOptimal (fun _ n ↦ A * n) w κ β ρ qv N v := by
  refine ⟨hfeas, fun T N' v' hfeas' h0 hag ↦ le_of_eq ?_⟩
  set D : ℕ → ℝ := fun s ↦ β ^ s * (A - w s + (1 - ρ) * κ / qv s) * (N' s - N s) with hD
  have hterm : ∀ s, β ^ s * dm_firmProfit (fun _ n ↦ A * n) w κ N' v' s =
      β ^ s * dm_firmProfit (fun _ n ↦ A * n) w κ N v s + (D s - D (s + 1)) := by
    intro s
    have hk' : κ * v' s = κ / qv s * (N' (s + 1) - (1 - ρ) * N' s) := by
      rw [(hfeas' s).1]; field_simp [hq s]; ring
    have hk : κ * v s = κ / qv s * (N (s + 1) - (1 - ρ) * N s) := by
      rw [(hfeas s).1]; field_simp [hq s]; ring
    simp only [dm_firmProfit, hD]
    rw [pow_succ]
    linear_combination (-β ^ s) * hk' + β ^ s * hk + (-β ^ s * (N' (s + 1) - N (s + 1))) * h8 s
  rw [Finset.sum_congr rfl fun s _ ↦ hterm s, Finset.sum_add_distrib, Finset.sum_range_sub']
  have hD0 : D 0 = 0 := by simp [hD, h0]
  have hDT : D T = 0 := by simp [hD, (hag T le_rfl).1]
  rw [hD0, hDT, sub_zero, add_zero]

/-- Miao, p. 597: an optimal large-firm plan exists: in the steady state of a search equilibrium
(constant `w`, `q^v` satisfying (18.8)), the constant plan `N_t = N`, `v_t = ρN/q^v` is
optimal. -/
theorem dm_firmOptimal_exists {A κ β ρ w qv N : ℝ} (hq : 0 < qv) (hρ : 0 ≤ ρ) (hN : 0 ≤ N)
    (h8 : κ / qv = β * (A - w + (1 - ρ) * κ / qv)) :
    dm_FirmOptimal (fun _ n ↦ A * n) (fun _ ↦ w) κ β ρ (fun _ ↦ qv) (fun _ ↦ N)
      (fun _ ↦ ρ * N / qv) := by
  refine dm_firmOptimal_of_euler (fun _ ↦ hq.ne') (fun _ ↦ h8) fun t ↦ ⟨?_, by positivity⟩
  field_simp
  ring

/-- Miao, (18.23), p. 597: the first-order conditions `−κ + μ_tq^v_t = 0` (for `v_t`) and
`(A − w_{t+1}) + μ_{t+1}(1 − ρ) − β^{−1}μ_t = 0` (for `N_{t+1}`) combine to (18.8). -/
theorem eq_18_23 {A κ β ρ : ℝ} {w qv μ : ℕ → ℝ} (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0)
    (hv : ∀ t, -κ + μ t * qv t = 0)
    (hN : ∀ t, (A - w (t + 1)) + μ (t + 1) * (1 - ρ) - β⁻¹ * μ t = 0) (t : ℕ) :
    κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) := by
  have hμ : ∀ s, μ s = κ / qv s := fun s ↦ by
    have := hv s; field_simp [hq s]; linarith
  have h := hN t
  rw [hμ t, hμ (t + 1)] at h
  field_simp at h ⊢
  linear_combination (-1 : ℝ) * h

/-- Miao, p. 597: aggregating the firm-level law of motion (18.22) over a unit measure of firms,
with `q^v_t = q(θ_t)`, `θ_t = v_t/u_t` (aggregate vacancies `v_t = ∫ v^j_t`), gives the aggregate
law of motion (18.2) `N_{t+1} = (1 − ρ)N_t + M(u_t, v_t)`. -/
theorem dm_aggregate_18_2 (MF : DMMatchingFn) {J : Type*} [MeasurableSpace J] (μJ : Measure J)
    {ρ qv u : ℝ} {Nt Nt1 vt : J → ℝ} (hNi : Integrable Nt μJ) (hvi : Integrable vt μJ)
    (hj : ∀ j, Nt1 j = (1 - ρ) * Nt j + qv * vt j) (hu : 0 < u) (hv : 0 < ∫ j, vt j ∂μJ)
    (hqv : qv = dm_q MF ((∫ j, vt j ∂μJ) / u)) :
    ∫ j, Nt1 j ∂μJ = (1 - ρ) * ∫ j, Nt j ∂μJ + MF.M u (∫ j, vt j ∂μJ) := by
  have e : Nt1 = fun j ↦ (1 - ρ) * Nt j + qv * vt j := funext hj
  rw [e, integral_add (hNi.const_mul _) (hvi.const_mul _), integral_const_mul,
    integral_const_mul, dm_M_eq_mul_q MF hu hv, hqv]
  ring

/-- Miao, (18.24), p. 597: if the continuation value is affine, `J_{t+1}(N) = j_{t+1}N + c_{t+1}`,
and the vacancy first-order condition `κ = βj_{t+1}q^v_t` holds, then the Bellman right side
`AN − w_tN − vκ + βJ_{t+1}((1 − ρ)N + q^v_tv)` does not depend on `v` and equals
`(A − w_t + (1 − ρ)κ/q^v_t)N + βc_{t+1}`; so `J_t` is affine with
`∂J_t/∂N = A − w_t + (1 − ρ)μ_t = A − w_t + (1 − ρ)κ/q^v_t`, `μ_t = βj_{t+1}`, which is `J^F_t` by
(18.7). -/
theorem eq_18_24 {A κ β ρ w qv jn cn : ℝ} (hfoc : κ = β * jn * qv) (hq : qv ≠ 0) (N v : ℝ) :
    A * N - w * N - v * κ + β * (jn * ((1 - ρ) * N + qv * v) + cn) =
        (A - w + (1 - ρ) * κ / qv) * N + β * cn ∧
      A - w + (1 - ρ) * (β * jn) = A - w + (1 - ρ) * κ / qv ∧
      HasDerivAt (fun n ↦ (A - w + (1 - ρ) * κ / qv) * n + β * cn)
        (A - w + (1 - ρ) * κ / qv) N := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hfoc]; field_simp; ring
  · rw [hfoc]; field_simp
  · simpa using ((hasDerivAt_id' N).const_mul (A - w + (1 - ρ) * κ / qv)).add_const (β * cn)

/-- Miao, (18.25) and p. 598: with `ε` additional workers paid `w`, the Bellman right side is
`A(N + ε) − w_tN − wε − vκ + βJ_{t+1}((1 − ρ)(N + ε) + q^v_tv)`, and its derivative at `ε = 0`
is `A − w + (1 − ρ)βj_{t+1} = (w_t − w) + ∂J_t/∂N ≡ J_n(w, t)`. -/
theorem dm_Jn {A κ β ρ wt w qv jn cn N v : ℝ} (hfoc : κ = β * jn * qv) (hq : qv ≠ 0) :
    HasDerivAt (fun ε ↦ A * (N + ε) - wt * N - w * ε - v * κ +
        β * (jn * ((1 - ρ) * (N + ε) + qv * v) + cn))
      ((wt - w) + (A - wt + (1 - ρ) * κ / qv)) 0 := by
  have hid := hasDerivAt_id' (0 : ℝ)
  have h := ((((hid.const_add N).const_mul A).sub_const (wt * N)).sub
    (hid.const_mul w)).sub_const (v * κ) |>.add
    ((((hid.const_add N).const_mul (1 - ρ)).add_const (qv * v)).const_mul jn |>.add_const cn
      |>.const_mul β)
  convert h using 1
  rw [hfoc]; field_simp; ring

/-- Miao, (18.26), p. 598: in the large firm the worker's surplus at wage `w` is
`J^W_t(w) − J^U_t(w) = (J^W_t − J^U_t) + (w − w_t)` and the firm's is
`J_n(w, t) = J^F_t + (w_t − w)`; the equilibrium wage `w_t` solves the bargaining problem (18.26)
iff `ηJ^F_t = (1 − η)(J^W_t − J^U_t)`, the first-order condition of (18.11). -/
theorem eq_18_26 {η D JF wt : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hS : 0 < D + JF) :
    (0 ≤ D ∧ 0 ≤ JF ∧ IsMaxOn (fun w ↦ (D + (w - wt)) ^ η * (JF + (wt - w)) ^ (1 - η))
        {w | 0 ≤ D + (w - wt) ∧ 0 ≤ JF + (wt - w)} wt) ↔ η * JF = (1 - η) * D := by
  have e1 : ∀ w, D + (w - wt) = (D - wt) + w := fun w ↦ by ring
  have e2 : ∀ w, JF + (wt - w) = (JF + wt) - w := fun w ↦ by ring
  simp only [e1, e2]
  have h := dm_nash_solution (w := wt) hη0 hη1 (show 0 < (D - wt) + (JF + wt) by linarith)
  simp only [sub_add_cancel, add_sub_cancel_right] at h
  exact h

/-- Miao, (18.27), p. 598: since `∂J_t/∂N` at wage `w` is `A − w + (1 − ρ)κ/q^v_t`, which is the
filled-job value `J^F_t(w) = A − w + β(ρ·0 + (1 − ρ)J^F_{t+1})` of (18.4) under free entry
`J^F_{t+1} = κ/(βq^v_t)`, the objective of (18.27) coincides with that of (18.11). -/
theorem eq_18_27 {A κ β ρ η qv X JU : ℝ} (hβ : β ≠ 0) (hq : qv ≠ 0) :
    (fun w ↦ (w + X - JU) ^ η * (A - w + (1 - ρ) * κ / qv) ^ (1 - η)) =
      fun w ↦ (w + X - JU) ^ η * (A - w + β * (ρ * 0 + (1 - ρ) * (κ / (β * qv)))) ^ (1 - η) := by
  funext w
  congr 2
  field_simp
  ring

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §18.1: efficiency — the planner's problem and the Hosios condition

Miao, §18.1, "Efficiency", pp. 598–599, equation (18.28).

The planner maximises `Σ βᵗ(AN_t + bu_t − κv_t)` subject to
`N_{t+1} = (1 − ρ)N_t + u_t f(θ_t)`, `u_t = 1 − N_t`, `θ_t = v_t/u_t`, where
`f(θ) = θq(θ) = M(1, θ)` is the job-finding rate, with Lagrangian
`Σ βᵗ[AN_t + b(1 − N_t) − κv_t + μ_t((1 − ρ)N_t + (1 − N_t)f(v_t/(1 − N_t)) − N_{t+1})]`.

* `dm_planner_foc_v`, `dm_planner_foc_N`: the first-order conditions are the partial derivatives
  of the Lagrangian: `−κ + μ_tf′(θ_t) = 0` and
  `0 = (A − b) − β^{−1}μ_{t−1} + μ_t(1 − ρ − f(θ_t) + θ_tf′(θ_t))`.
  **Correction**: the book prints the last term as `μ_t(1 − ρ)[1 − q(θ_t)θ_t + (q(θ_t)θ_t)′θ_t]`;
  `dm_planner_foc_N_misprint` shows the two differ by `μ_tρθ_tq(θ_t)ξ(θ_t) ≠ 0`, and only the
  corrected condition yields (18.28).
* `eq_18_28`: in a steady state, the first-order conditions give
  `κ(1 − β(1 − ρ))/q(θ) + βξ(θ)κθ = β(1 − ξ(θ))(A − b)`.
* `dm_xi_duration`: `ξ(θ)` and `1 − ξ(θ)` are the elasticities of the expected durations of a
  vacancy and of unemployment (p. 599).
* `dm_hosios`: when `ξ(θ*) = η`, the equilibrium `θ*` (18.18) satisfies the planner's condition
  (18.28): the **Hosios condition**.
* `dm_cd_planner_existsUnique`, `dm_cd_hosios_iff`, `dm_cd_hosios_compare`: with Cobb–Douglas
  matching (`ξ = α`), the planner's steady state exists and is unique, the equilibrium is
  efficient iff `η = α`, and `η > α` (`η < α`) gives too low (too high) market tightness.
* `dm_hosios_misprint` (**correction**): the book's "if and only if `ξ(θ) = β`" (p. 599) should
  read `ξ(θ) = η`; a Cobb–Douglas economy with `ξ = α = β ≠ η` is inefficient.

Departure: "efficient" is formalised as "satisfies the planner's steady-state first-order
conditions"; second-order conditions are not discussed by the book and are not formalised.
-/

namespace Miao.SearchAndMatching

/-- Miao, p. 599: the planner's first-order condition for `v_t`: the derivative of the date-`t`
Lagrangian term `βᵗ(AN + b(1 − N) − κv + μ((1 − ρ)N + (1 − N)f(v/(1 − N))))` in `v` is
`βᵗ(−κ + μf′(θ))`, `θ = v/(1 − N)`. -/
theorem dm_planner_foc_v {f : ℝ → ℝ} {A b κ β ρ μ N v f' : ℝ} (t : ℕ) (hN : N < 1)
    (hf : HasDerivAt f f' (v / (1 - N))) :
    HasDerivAt (fun x ↦ β ^ t * (A * N + b * (1 - N) - κ * x +
        μ * ((1 - ρ) * N + (1 - N) * f (x / (1 - N)))))
      (β ^ t * (-κ + μ * f')) v := by
  have hu : 1 - N ≠ 0 := by linarith
  have hd : HasDerivAt (fun x ↦ x / (1 - N)) (1 / (1 - N)) v := (hasDerivAt_id' v).div_const _
  have hfc := hf.comp v hd
  have h := ((((hasDerivAt_id' v).const_mul κ).const_sub (A * N + b * (1 - N))).add
    (((hfc.const_mul (1 - N)).const_add ((1 - ρ) * N)).const_mul μ)).const_mul (β ^ t)
  refine h.congr_deriv ?_
  field_simp

/-- Miao, p. 599: the planner's first-order condition for `N_{s+1}`: the derivative in `N` of the
terms of the Lagrangian containing `N_{s+1}`,
`β^{s+1}(AN + b(1 − N) − κv + μ₁((1 − ρ)N + (1 − N)f(v/(1 − N)))) − β^sμ₀N`, is
`β^{s+1}((A − b) + μ₁(1 − ρ − f(θ) + θf′(θ))) − β^sμ₀`. Dividing by `β^{s+1}` gives
`0 = (A − b) − β^{−1}μ₀ + μ₁(1 − ρ − f(θ) + θf′(θ))`. -/
theorem dm_planner_foc_N {f : ℝ → ℝ} {A b κ β ρ μ₀ μ₁ N v f' : ℝ} (s : ℕ) (hN : N < 1)
    (hf : HasDerivAt f f' (v / (1 - N))) :
    HasDerivAt (fun n ↦ β ^ (s + 1) * (A * n + b * (1 - n) - κ * v +
        μ₁ * ((1 - ρ) * n + (1 - n) * f (v / (1 - n)))) - β ^ s * μ₀ * n)
      (β ^ (s + 1) * ((A - b) + μ₁ * (1 - ρ - f (v / (1 - N)) + v / (1 - N) * f')) -
        β ^ s * μ₀) N := by
  have hu : 1 - N ≠ 0 := by linarith
  have h1 : HasDerivAt (fun n : ℝ ↦ 1 - n) (-1) N := by
    simpa using (hasDerivAt_id' N).const_sub 1
  have h2 : HasDerivAt (fun n : ℝ ↦ v / (1 - n)) (-(v * -1) / (1 - N) ^ 2) N := by
    have := (h1.inv hu).const_mul v
    convert this using 1
    · funext n; simp [div_eq_mul_inv]
    · field_simp
  have hfc := hf.comp N h2
  have hg := h1.mul hfc
  have h := ((((((hasDerivAt_id' N).const_mul A).add (h1.const_mul b)).sub_const (κ * v)).add
    ((((hasDerivAt_id' N).const_mul (1 - ρ)).add hg).const_mul μ₁)).const_mul (β ^ (s + 1))).sub
    ((hasDerivAt_id' N).const_mul (β ^ s * μ₀))
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  field_simp
  ring

/-- Miao, p. 599 (**correction**): the printed first-order condition for `N_t` has
`μ_t(1 − ρ)[1 − f + θf′]` instead of `μ_t(1 − ρ − f + θf′)`; with `f = θq`, `f′ = q(1 − ξ)`
the two differ by `μ_tρθq(θ)ξ(θ)`, which is positive when `μ, ρ, θ, q, ξ > 0`. -/
theorem dm_planner_foc_N_misprint {μ ρ θ q ξ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) (hθ : 0 < θ)
    (hq : 0 < q) (hξ : 0 < ξ) :
    μ * ((1 - ρ) * (1 - θ * q + θ * (q * (1 - ξ)))) -
        μ * (1 - ρ - θ * q + θ * (q * (1 - ξ))) = μ * ρ * θ * q * ξ ∧
      μ * ((1 - ρ) * (1 - θ * q + θ * (q * (1 - ξ)))) ≠
        μ * (1 - ρ - θ * q + θ * (q * (1 - ξ))) := by
  have e : μ * ((1 - ρ) * (1 - θ * q + θ * (q * (1 - ξ)))) -
      μ * (1 - ρ - θ * q + θ * (q * (1 - ξ))) = μ * ρ * θ * q * ξ := by ring
  refine ⟨e, fun h ↦ ?_⟩
  have : 0 < μ * ρ * θ * q * ξ := by positivity
  linarith

/-- Miao, (18.28), p. 599: the left side `κ(1 − β(1 − ρ))/q(θ) + βξ(θ)κθ` of the planner's
steady-state condition. -/
noncomputable def dm_plannerLHS (MF : DMMatchingFn) (κ β ρ θ : ℝ) : ℝ :=
  κ / dm_q MF θ * (1 - β * (1 - ρ)) + β * dm_xi MF θ * κ * θ

/-- Miao, (18.28), p. 599: combining the planner's first-order conditions in a steady state
(`μ_t = μ`, `θ_t = θ`, with `f(θ) = θq(θ)` and `f′(θ) = q(θ)(1 − ξ(θ))`) gives
`κ(1 − β(1 − ρ))/q(θ) + βξ(θ)κθ = β(1 − ξ(θ))(A − b)`. -/
theorem eq_18_28 (MF : DMMatchingFn) {A b κ β ρ θ μ q' : ℝ} (hθ : 0 < θ) (hβ : 0 < β)
    (hq' : HasDerivAt (dm_q MF) q' θ) (hξ1 : dm_xi MF θ < 1)
    (hv : -κ + μ * deriv (fun x ↦ x * dm_q MF x) θ = 0)
    (hN : (A - b) - β⁻¹ * μ +
      μ * (1 - ρ - θ * dm_q MF θ + θ * deriv (fun x ↦ x * dm_q MF x) θ) = 0) :
    dm_plannerLHS MF κ β ρ θ = β * (1 - dm_xi MF θ) * (A - b) := by
  rw [(dm_jobFinding_hasDerivAt MF hθ hq').deriv] at hv hN
  rw [dm_plannerLHS]
  have hq := dm_q_pos MF hθ
  set q := dm_q MF θ
  set ξ := dm_xi MF θ
  have h1 : 0 < 1 - ξ := by linarith
  have hμ : μ = κ / (q * (1 - ξ)) := by
    field_simp; linarith
  rw [hμ] at hN
  field_simp at hN ⊢
  linear_combination (-1 : ℝ) * hN

/-- Miao, p. 599: the **Hosios condition**: if `ξ(θ*) = η`, the steady-state equilibrium market
tightness `θ*` (solving (18.18)) satisfies the planner's condition (18.28), so the steady-state
search equilibrium is socially efficient. -/
theorem dm_hosios (MF : DMMatchingFn) {A b κ β ρ η θ : ℝ} (hξ : dm_xi MF θ = η)
    (h : dm_ssLHS MF κ β ρ η θ = β * (1 - η) * (A - b)) :
    dm_plannerLHS MF κ β ρ θ = β * (1 - dm_xi MF θ) * (A - b) := by
  rw [dm_plannerLHS, hξ]
  rw [dm_ssLHS] at h
  exact h

/-- Miao, p. 599: `ξ(θ)` is the elasticity of the expected duration of a vacancy `1/q(v/u)` with
respect to vacancies, and `1 − ξ(θ)` is the elasticity of the expected duration of unemployment
`1/(θq(θ))`, `θ = v/u`, with respect to unemployment. -/
theorem dm_xi_duration (MF : DMMatchingFn) {u v q' : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hq : HasDerivAt (dm_q MF) q' (v / u)) :
    HasDerivAt (fun x ↦ (dm_q MF (x / u))⁻¹) (-(q' * (1 / u)) / dm_q MF (v / u) ^ 2) v ∧
      v * (-(q' * (1 / u)) / dm_q MF (v / u) ^ 2) / (dm_q MF (v / u))⁻¹ = dm_xi MF (v / u) ∧
      HasDerivAt (fun y ↦ ((v / y) * dm_q MF (v / y))⁻¹)
        (-((dm_q MF (v / u) + v / u * q') * (-v / u ^ 2)) / (v / u * dm_q MF (v / u)) ^ 2) u ∧
      u * (-((dm_q MF (v / u) + v / u * q') * (-v / u ^ 2)) / (v / u * dm_q MF (v / u)) ^ 2) /
        ((v / u) * dm_q MF (v / u))⁻¹ = 1 - dm_xi MF (v / u) := by
  have hθ : 0 < v / u := div_pos hv hu
  have hq0 : dm_q MF (v / u) ≠ 0 := (dm_q_pos MF hθ).ne'
  have hd1 : HasDerivAt (fun x ↦ x / u) (1 / u) v := (hasDerivAt_id' v).div_const u
  have hd2 : HasDerivAt (fun y ↦ v / y) (-v / u ^ 2) u := by
    have := (hasDerivAt_inv hu.ne').const_mul v
    refine (this.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun y ↦ by simp [div_eq_mul_inv]
  have hf := (hasDerivAt_id' (v / u)).mul hq
  have hf0 : v / u * dm_q MF (v / u) ≠ 0 := mul_ne_zero hθ.ne' hq0
  have hc := hq.comp v hd1
  refine ⟨hc.inv hq0, ?_, ?_, ?_⟩
  · rw [dm_xi, hq.deriv]; field_simp
  · have h := (hf.comp u hd2).inv (by simpa using hf0)
    refine h.congr_deriv ?_
    simp only [Function.comp_apply, Pi.mul_apply]
    ring
  · rw [dm_xi, hq.deriv]; field_simp; ring

/-- Miao, p. 599: with Cobb–Douglas matching the planner's condition (18.28) is (18.18) with `η`
replaced by `α`. -/
theorem dm_cd_plannerLHS {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1) {κ β ρ θ : ℝ}
    (hθ : 0 < θ) :
    dm_plannerLHS (dm_cdMatching μ α hμ hα0 hα1) κ β ρ θ =
      dm_ssLHS (dm_cdMatching μ α hμ hα0 hα1) κ β ρ α θ := by
  rw [dm_plannerLHS, dm_ssLHS, dm_cd_xi hμ hα0 hα1 hθ]

/-- Miao, p. 599: with Cobb–Douglas matching and `A > b`, the planner's steady-state condition
(18.28) has a unique solution `θ^p > 0`. -/
theorem dm_cd_planner_existsUnique {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1)
    {A b κ β ρ : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hc : 0 < 1 - β * (1 - ρ)) (hAb : b < A) :
    ∃! θ, 0 < θ ∧ dm_plannerLHS (dm_cdMatching μ α hμ hα0 hα1) κ β ρ θ =
      β * (1 - dm_xi (dm_cdMatching μ α hμ hα0 hα1) θ) * (A - b) := by
  obtain ⟨θ, ⟨hθ, h⟩, huniq⟩ := dm_cd_ss_existsUnique hμ hα0 hα1 hκ hβ hα0 hα1 hc hAb
  refine ⟨θ, ⟨hθ, ?_⟩, ?_⟩
  · rw [dm_cd_plannerLHS hμ hα0 hα1 hθ, dm_cd_xi hμ hα0 hα1 hθ]; exact h
  · rintro θ' ⟨hθ', h'⟩
    rw [dm_cd_plannerLHS hμ hα0 hα1 hθ', dm_cd_xi hμ hα0 hα1 hθ'] at h'
    exact huniq θ' ⟨hθ', h'⟩

/-- Miao, p. 599: with Cobb–Douglas matching (`ξ ≡ α`) and `A > b`, the steady-state equilibrium
tightness `θ^e` (18.18) equals the efficient tightness `θ^p` (18.28) **iff** `η = α`. -/
theorem dm_cd_hosios_iff {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1)
    {A b κ β ρ η θe θp : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hc : 0 < 1 - β * (1 - ρ)) (hAb : b < A)
    (hθe : 0 < θe) (hθp : 0 < θp)
    (he : dm_ssLHS (dm_cdMatching μ α hμ hα0 hα1) κ β ρ η θe = β * (1 - η) * (A - b))
    (hp : dm_plannerLHS (dm_cdMatching μ α hμ hα0 hα1) κ β ρ θp =
      β * (1 - dm_xi (dm_cdMatching μ α hμ hα0 hα1) θp) * (A - b)) :
    θe = θp ↔ η = α := by
  rw [dm_cd_plannerLHS hμ hα0 hα1 hθp, dm_cd_xi hμ hα0 hα1 hθp] at hp
  constructor
  · rintro rfl
    rw [dm_ssLHS] at he hp
    have hd : 0 < β * κ * θe + β * (A - b) := by
      have : 0 < β * κ * θe := by positivity
      have : 0 < β * (A - b) := mul_pos hβ (by linarith)
      linarith
    have key : (η - α) * (β * κ * θe + β * (A - b)) = 0 := by linear_combination he - hp
    rcases mul_eq_zero.mp key with h | h
    · linarith
    · linarith
  · rintro rfl
    exact dm_ss_unique _ hκ hβ hα0 hc hθe hθp he hp

/-- Miao, p. 599: with Cobb–Douglas matching and `A > b`, a worker bargaining power above the
Hosios value (`η > α`) gives too little job creation (`θ^e < θ^p`), and below it too much. -/
theorem dm_cd_hosios_compare {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1)
    {A b κ β ρ η θe θp : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hρ : 0 < ρ) (hη : 0 < η)
    (hc : 0 < 1 - β * (1 - ρ)) (hAb : b < A) (hθe : 0 < θe) (hθp : 0 < θp)
    (he : dm_ssLHS (dm_cdMatching μ α hμ hα0 hα1) κ β ρ η θe = β * (1 - η) * (A - b))
    (hp : dm_plannerLHS (dm_cdMatching μ α hμ hα0 hα1) κ β ρ θp =
      β * (1 - dm_xi (dm_cdMatching μ α hμ hα0 hα1) θp) * (A - b)) :
    (α < η → θe < θp) ∧ (η < α → θp < θe) := by
  rw [dm_cd_plannerLHS hμ hα0 hα1 hθp, dm_cd_xi hμ hα0 hα1 hθp] at hp
  exact ⟨fun h ↦ (dm_cs_eta _ hκ hβ hα0 hρ hc hAb hθp hθe hp he h).1,
    fun h ↦ (dm_cs_eta _ hκ hβ hη hρ hc hAb hθe hθp he hp h).1⟩

/-- Miao, p. 599 (**correction**): "if and only if `ξ(θ) = β`, the two congestion effects offset
each other" should read `ξ(θ) = η`: in the Cobb–Douglas economy `μ = 1`, `α = β = ρ = 1/2`,
`η = 1/4`, `κ = A = 1`, `b = 0`, `ξ(θ) = α = β` but the equilibrium and efficient market
tightness differ. -/
theorem dm_hosios_misprint :
    let MF := dm_cdMatching 1 (1 / 2) one_pos (by norm_num) (by norm_num)
    ∃ θe θp : ℝ, 0 < θe ∧ 0 < θp ∧
      dm_ssLHS MF 1 (1 / 2) (1 / 2) (1 / 4) θe = 1 / 2 * (1 - 1 / 4) * (1 - 0) ∧
      dm_plannerLHS MF 1 (1 / 2) (1 / 2) θp = 1 / 2 * (1 - dm_xi MF θp) * (1 - 0) ∧
      dm_xi MF θp = 1 / 2 ∧ θe ≠ θp := by
  intro MF
  obtain ⟨θe, ⟨hθe, he⟩, -⟩ := dm_cd_ss_existsUnique (μ := 1) (α := 1 / 2) one_pos
    (by norm_num) (by norm_num) (A := 1) (b := 0) (κ := 1) (β := 1 / 2) (ρ := 1 / 2)
    (η := 1 / 4) one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨θp, ⟨hθp, hp⟩, -⟩ := dm_cd_planner_existsUnique (μ := 1) (α := 1 / 2) one_pos
    (by norm_num) (by norm_num) (A := 1) (b := 0) (κ := 1) (β := 1 / 2) (ρ := 1 / 2) one_pos
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨θe, θp, hθe, hθp, he, hp, dm_cd_xi _ _ _ hθp, fun h ↦ ?_⟩
  have := (dm_cd_hosios_iff one_pos (by norm_num) (by norm_num) one_pos (by norm_num)
    (by norm_num) (by norm_num) hθe hθp he hp).mp h
  norm_num at this

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 18.1: firms own capital, households trade firm shares

Miao, §18.4, Exercise 18.1, p. 614: "For the model in Section 18.1, suppose that firms own
capital and make investment decisions. Households trade firm shares. Formulate this market
arrangement and define a search equilibrium. Analyze this equilibrium."

**Formulation.** Households have linear utility `Σ βᵗC_t` and budget
`C_t + p_ts_{t+1} = (p_t + d_t)s_t + y_t` (`y_t`: wages, benefits and lump-sum taxes, taken as
given by the portfolio choice). A unit measure of large firms (§18.1, "Large Firms") with
production function `F(K, N)` pays dividends `d_t = F(K_t, N_t) − w_tN_t − κv_t − I_t`, with
`K_{t+1} = (1 − δ)K_t + I_t` and `N_{t+1} = (1 − ρ)N_t + q^v_tv_t`, `v_t ≥ 0`. Wages are Nash
bargained as in (18.26). Optimality is against plans that differ in finitely many periods.

* `dm_ex1_share_euler`: optimal share holdings imply `p_t = β(p_{t+1} + d_{t+1})`;
  `dm_ex1_hhOptimal_of_euler`: conversely (so `dm_Ex1HHOptimal` is satisfiable);
  `dm_ex1_price`: with `βᵀp_T → 0`, `p₀ = Σ βᵗ⁺¹d_{t+1}`, so maximising firm value means
  maximising dividends discounted at `β`.
* `dm_ex1_capital_euler`: the firm's investment Euler equation
  `1 = β(F_K(K_{t+1}, N_{t+1}) + 1 − δ)`; `dm_ex1_job_creation`: the job creation equation
  `κ/q^v_t = β(F_N(K_{t+1}, N_{t+1}) − w_{t+1} + (1 − ρ)κ/q^v_{t+1})`; `dm_ex1_wage`: the wage
  equation `w_t = η(F_N(K_t, N_t) + κθ_t) + (1 − η)b` (the derivation of (18.15) with `A`
  replaced by the marginal product of labour).
* `dm_Ex1IsSearchEqm`: a search equilibrium.
* Analysis of the steady state with `F(K, N) = AK^aN^{1−a}`: `dm_ex1_FK`, `dm_ex1_FN` (marginal
  products in terms of `k = K/N`), `dm_ex1_kstar_unique` (the capital Euler equation pins down
  `k* = (aA/(1/β − 1 + δ))^{1/(1−a)}`), `dm_ex1_steady` (in a steady state, `θ` solves the basic
  DMP equation (18.18) with `A` replaced by `A_eff = (1 − a)Ak*^a`, and unemployment is
  `u* = ρ/(ρ + θq(θ))`), `dm_ex1_steady_isSearchEqm` and `dm_ex1_searchEqm_exists`: such a steady
  state is a search equilibrium, and one exists in a concrete economy.
-/

namespace Miao.SearchAndMatching

open Filter Topology

/-- Exercise 18.1: the household's consumption `C_t = (p_t + d_t)s_t − p_ts_{t+1} + y_t`. -/
def dm_hhCons (p d y s : ℕ → ℝ) (t : ℕ) : ℝ := (p t + d t) * s t - p t * s (t + 1) + y t

/-- Exercise 18.1: optimal share holdings: no share plan with the same `s₀` that coincides with
`s` from some date `T` on gives higher discounted consumption. -/
def dm_Ex1HHOptimal (β : ℝ) (p d y s : ℕ → ℝ) : Prop :=
  ∀ (T : ℕ) (s' : ℕ → ℝ), s' 0 = s 0 → (∀ t, T ≤ t → s' t = s t) →
    ∑ t ∈ Finset.range T, β ^ t * dm_hhCons p d y s' t ≤
      ∑ t ∈ Finset.range T, β ^ t * dm_hhCons p d y s t

/-- **Exercise 18.1** (Miao, p. 614): optimal share holdings imply the asset-pricing equation
`p_t = β(p_{t+1} + d_{t+1})`. -/
theorem dm_ex1_share_euler {β : ℝ} {p d y s : ℕ → ℝ} (hβ : 0 < β)
    (hopt : dm_Ex1HHOptimal β p d y s) (t : ℕ) : p t = β * (p (t + 1) + d (t + 1)) := by
  have gain : ∀ ε : ℝ, β ^ t * ε * (β * (p (t + 1) + d (t + 1)) - p t) ≤ 0 := by
    intro ε
    set s' : ℕ → ℝ := fun r ↦ s r + if r = t + 1 then ε else 0 with hs'
    have h0 : s' 0 = s 0 := by simp [hs']
    have hag : ∀ r, t + 1 + 1 ≤ r → s' r = s r := by
      intro r hr
      have : r ≠ t + 1 := by omega
      simp [hs', this]
    have h := hopt (t + 1 + 1) s' h0 hag
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := t + 1),
      Finset.sum_range_succ] at h
    have hlow : ∑ r ∈ Finset.range t, β ^ r * dm_hhCons p d y s' r =
        ∑ r ∈ Finset.range t, β ^ r * dm_hhCons p d y s r := by
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      have hr' := Finset.mem_range.mp hr
      have h1 : r ≠ t + 1 := by omega
      have h2 : r ≠ t := by omega
      simp [dm_hhCons, hs', h1, h2]
    rw [hlow] at h
    have ht1 : t ≠ t + 1 := by omega
    have ht3 : t + 1 + 1 ≠ t + 1 := by omega
    simp only [dm_hhCons, hs', ht1, ht3, ↓reduceIte, add_zero] at h
    rw [pow_succ] at h
    nlinarith
  have hbt : 0 < β ^ t := pow_pos hβ t
  have h1 := gain 1
  have h2 := gain (-1)
  have a : β * (p (t + 1) + d (t + 1)) - p t ≤ 0 := by nlinarith
  have b : 0 ≤ β * (p (t + 1) + d (t + 1)) - p t := by nlinarith
  linarith

/-- **Exercise 18.1** (Miao, p. 614): conversely, if `p_t = β(p_{t+1} + d_{t+1})` for all `t`,
every share plan is optimal (households are indifferent at the margin). -/
theorem dm_ex1_hhOptimal_of_euler {β : ℝ} {p d y s : ℕ → ℝ}
    (he : ∀ t, p t = β * (p (t + 1) + d (t + 1))) : dm_Ex1HHOptimal β p d y s := by
  intro T s' h0 hag
  refine le_of_eq ?_
  set D : ℕ → ℝ := fun r ↦ β ^ r * (p r + d r) * (s' r - s r) with hD
  have hterm : ∀ r, β ^ r * dm_hhCons p d y s' r =
      β ^ r * dm_hhCons p d y s r + (D r - D (r + 1)) := by
    intro r
    simp only [dm_hhCons, hD]
    rw [pow_succ]
    linear_combination (-β ^ r * (s' (r + 1) - s (r + 1))) * he r
  rw [Finset.sum_congr rfl fun r _ ↦ hterm r, Finset.sum_add_distrib, Finset.sum_range_sub']
  have hD0 : D 0 = 0 := by simp [hD, h0]
  have hDT : D T = 0 := by simp [hD, hag T le_rfl]
  rw [hD0, hDT, sub_zero, add_zero]

/-- **Exercise 18.1** (Miao, p. 614): iterating `p_t = β(p_{t+1} + d_{t+1})` with `βᵀp_T → 0`
gives the share price as the present value of dividends, `p₀ = Σ_{t ≥ 0} β^{t+1}d_{t+1}`. -/
theorem dm_ex1_price {β : ℝ} {p d : ℕ → ℝ} (he : ∀ t, p t = β * (p (t + 1) + d (t + 1)))
    (htv : Tendsto (fun T ↦ β ^ T * p T) atTop (𝓝 0)) :
    Tendsto (fun T ↦ ∑ t ∈ Finset.range T, β ^ (t + 1) * d (t + 1)) atTop (𝓝 (p 0)) := by
  have hpart : ∀ T, p 0 = ∑ t ∈ Finset.range T, β ^ (t + 1) * d (t + 1) + β ^ T * p T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, he n, pow_succ]
      ring
  have : (fun T ↦ ∑ t ∈ Finset.range T, β ^ (t + 1) * d (t + 1)) =
      fun T ↦ p 0 - β ^ T * p T := by
    funext T; rw [hpart T]; ring
  rw [this]
  simpa using htv.const_sub (p 0)

/-- Exercise 18.1: the firm's dividend `d_t = F(K_t, N_t) − w_tN_t − κv_t − I_t`. -/
def dm_ex1Div (F : ℝ → ℝ → ℝ) (w : ℕ → ℝ) (κ : ℝ) (K I N v : ℕ → ℝ) (t : ℕ) : ℝ :=
  F (K t) (N t) - w t * N t - κ * v t - I t

/-- Exercise 18.1: a feasible plan of the firm: capital accumulation, (18.22) and `v ≥ 0`. -/
def dm_Ex1Feasible (δ ρ : ℝ) (qv K I N v : ℕ → ℝ) : Prop :=
  ∀ t, K (t + 1) = (1 - δ) * K t + I t ∧ N (t + 1) = (1 - ρ) * N t + qv t * v t ∧ 0 ≤ v t

/-- Exercise 18.1: an optimal plan of the firm (value maximisation, i.e. dividends discounted at
`β` by `dm_ex1_price`), against plans with the same `K₀, N₀` coinciding from some date on. -/
def dm_Ex1FirmOptimal (F : ℝ → ℝ → ℝ) (w : ℕ → ℝ) (κ β δ ρ : ℝ) (qv K I N v : ℕ → ℝ) : Prop :=
  dm_Ex1Feasible δ ρ qv K I N v ∧ ∀ (T : ℕ) (K' I' N' v' : ℕ → ℝ),
    dm_Ex1Feasible δ ρ qv K' I' N' v' → K' 0 = K 0 → N' 0 = N 0 →
    (∀ t, T ≤ t → K' t = K t ∧ I' t = I t ∧ N' t = N t ∧ v' t = v t) →
      ∑ t ∈ Finset.range T, β ^ t * dm_ex1Div F w κ K' I' N' v' t ≤
        ∑ t ∈ Finset.range T, β ^ t * dm_ex1Div F w κ K I N v t

/-- **Exercise 18.1** (Miao, p. 614): the firm's investment Euler equation
`1 = β(F_K(K_{t+1}, N_{t+1}) + 1 − δ)`. -/
theorem dm_ex1_capital_euler {F : ℝ → ℝ → ℝ} {w qv K I N v : ℕ → ℝ} {κ β δ ρ FK : ℝ}
    (hopt : dm_Ex1FirmOptimal F w κ β δ ρ qv K I N v) (t : ℕ) (hβ : 0 < β)
    (hF : HasDerivAt (fun k ↦ F k (N (t + 1))) FK (K (t + 1))) :
    1 = β * (FK + 1 - δ) := by
  obtain ⟨hfeas, hbest⟩ := hopt
  set K' : ℝ → ℕ → ℝ := fun ε s ↦ K s + if s = t + 1 then ε else 0 with hK'
  set I' : ℝ → ℕ → ℝ := fun ε s ↦ I s + (if s = t then ε else 0) -
    (if s = t + 1 then (1 - δ) * ε else 0) with hI'
  set φ : ℝ → ℝ := fun ε ↦ β ^ t * -ε + β ^ (t + 1) *
    (F (K (t + 1) + ε) (N (t + 1)) - F (K (t + 1)) (N (t + 1)) + (1 - δ) * ε) with hφ
  have ht1 : t ≠ t + 1 := by omega
  have ht2 : t + 1 ≠ t := by omega
  have ht3 : t + 1 + 1 ≠ t + 1 := by omega
  have hmax : IsLocalMax φ 0 := by
    refine Filter.Eventually.of_forall fun ε ↦ ?_
    have hφ0 : φ 0 = 0 := by simp [hφ]
    rw [hφ0]
    have hfe : dm_Ex1Feasible δ ρ qv (K' ε) (I' ε) N v := by
      intro s
      refine ⟨?_, (hfeas s).2.1, (hfeas s).2.2⟩
      rcases eq_or_ne s t with rfl | hst
      · simp only [hK', hI', ht1, ↓reduceIte, add_zero, sub_zero]
        rw [(hfeas s).1]; ring
      rcases eq_or_ne s (t + 1) with rfl | hst1
      · simp only [hK', hI', ht2, ht3, ↓reduceIte, add_zero]
        rw [(hfeas (t + 1)).1]; ring
      · have h1 : s + 1 ≠ t + 1 := by omega
        simp only [hK', hI', hst, hst1, h1, ↓reduceIte, add_zero, sub_zero]
        exact (hfeas s).1
    have h0 : K' ε 0 = K 0 := by simp [hK']
    have hag : ∀ s, t + 1 + 1 ≤ s → K' ε s = K s ∧ I' ε s = I s ∧ N s = N s ∧ v s = v s := by
      intro s hs
      have h1 : s ≠ t + 1 := by omega
      have h2 : s ≠ t := by omega
      simp [hK', hI', h1, h2]
    have h := hbest (t + 1 + 1) (K' ε) (I' ε) N v hfe h0 rfl hag
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := t + 1),
      Finset.sum_range_succ] at h
    have hlow : ∑ s ∈ Finset.range t, β ^ s * dm_ex1Div F w κ (K' ε) (I' ε) N v s =
        ∑ s ∈ Finset.range t, β ^ s * dm_ex1Div F w κ K I N v s := by
      refine Finset.sum_congr rfl fun s hs ↦ ?_
      have hs' := Finset.mem_range.mp hs
      have h1 : s ≠ t + 1 := by omega
      have h2 : s ≠ t := by omega
      simp [dm_ex1Div, hK', hI', h1, h2]
    rw [hlow] at h
    generalize ∑ s ∈ Finset.range t, β ^ s * dm_ex1Div F w κ K I N v s = S at h
    simp only [dm_ex1Div, hK', hI', hφ, ht1, ht2, ↓reduceIte, add_zero, sub_zero] at h ⊢
    linarith
  have h2 : HasDerivAt (fun ε : ℝ ↦ K (t + 1) + ε) 1 0 := (hasDerivAt_id' 0).const_add _
  have hF' : HasDerivAt (fun k ↦ F k (N (t + 1))) FK (K (t + 1) + 0) := by rwa [add_zero]
  have hFc : HasDerivAt (fun ε ↦ F (K (t + 1) + ε) (N (t + 1))) (FK * 1) 0 := hF'.comp 0 h2
  have hid := hasDerivAt_id' (0 : ℝ)
  have hd : HasDerivAt φ (β ^ t * -1 + β ^ (t + 1) * (FK * 1 + (1 - δ) * 1)) 0 :=
    (hid.neg.const_mul (β ^ t)).add (((hFc.sub_const (F (K (t + 1)) (N (t + 1)))).add
      (hid.const_mul (1 - δ))).const_mul (β ^ (t + 1)))
  have hz := hmax.hasDerivAt_eq_zero hd
  have hbt : 0 < β ^ t := pow_pos hβ t
  have key : β ^ t * (β * (FK + 1 - δ) - 1) = 0 := by
    rw [pow_succ] at hz
    linear_combination hz
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hbt.ne'
  · linarith

/-- **Exercise 18.1** (Miao, p. 614): an optimal plan of the capital-owning firm with positive
vacancies at `t, t + 1` satisfies the job creation equation
`κ/q^v_t = β(F_N(K_{t+1}, N_{t+1}) − w_{t+1} + (1 − ρ)κ/q^v_{t+1})` (by `dm_firm_euler` applied
to `F_t(N) = F(K_t, N) − I_t`). -/
theorem dm_ex1_job_creation {F : ℝ → ℝ → ℝ} {w qv K I N v : ℕ → ℝ} {κ β δ ρ FN : ℝ}
    (hopt : dm_Ex1FirmOptimal F w κ β δ ρ qv K I N v) (t : ℕ) (hβ : 0 < β) (hq : 0 < qv t)
    (hq1 : 0 < qv (t + 1)) (hv : 0 < v t) (hv1 : 0 < v (t + 1))
    (hF : HasDerivAt (fun n ↦ F (K (t + 1)) n) FN (N (t + 1))) :
    κ / qv t = β * (FN - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) := by
  obtain ⟨hfeas, hbest⟩ := hopt
  have hopt' : dm_FirmOptimal (fun s n ↦ F (K s) n - I s) w κ β ρ qv N v := by
    refine ⟨fun s ↦ (hfeas s).2, fun T N' v' hfe' h0 hag ↦ ?_⟩
    have hfe : dm_Ex1Feasible δ ρ qv K I N' v' := fun s ↦ ⟨(hfeas s).1, hfe' s⟩
    have hag' : ∀ s, T ≤ s → K s = K s ∧ I s = I s ∧ N' s = N s ∧ v' s = v s :=
      fun s hs ↦ ⟨rfl, rfl, hag s hs⟩
    have h := hbest T K I N' v' hfe rfl h0 hag'
    have e : ∀ N₁ v₁ : ℕ → ℝ, ∀ s, dm_ex1Div F w κ K I N₁ v₁ s =
        dm_firmProfit (fun s n ↦ F (K s) n - I s) w κ N₁ v₁ s := by
      intro N₁ v₁ s; simp only [dm_ex1Div, dm_firmProfit]; ring
    simp only [e] at h
    exact h
  exact dm_firm_euler (F := fun s n ↦ F (K s) n - I s) hopt' t hβ hq hq1 hv hv1
    (by simpa using hF.sub_const (I (t + 1)))

/-- **Exercise 18.1** (Miao, p. 614): the Nash-bargained wage in the capital-owning large firm
is `w_t = η(F_N(K_t, N_t) + κθ_t) + (1 − η)b`: the firm's marginal value of a worker
`∂J_t/∂N = F_N(K_t, N_t) − w_t + (1 − ρ)κ/q^v_t` takes the place of `J^F_t`, and the derivation
of (18.15) goes through with `A` replaced by `F_N(K_t, N_t)`. -/
theorem dm_ex1_wage {b κ β ρ η : ℝ} {JF JW JU w qv qu θ FN : ℕ → ℝ} (t : ℕ)
    (h4 : JF t = FN t - w t + β * (ρ * 0 + (1 - ρ) * JF (t + 1)))
    (h9 : JW t = w t + β * (ρ * JU (t + 1) + (1 - ρ) * JW (t + 1)))
    (h10 : JU t = b + β * (qu t * JW (t + 1) + (1 - qu t) * JU (t + 1)))
    (h12t : η * dm_surplus JF JW JU t = JW t - JU t)
    (h12 : η * dm_surplus JF JW JU (t + 1) = JW (t + 1) - JU (t + 1))
    (h13 : (1 - η) * dm_surplus JF JW JU (t + 1) = κ / (β * qv t))
    (hqu : qu t = θ t * qv t) (hβ : β ≠ 0) (hq : qv t ≠ 0) (hη1 : η ≠ 1) :
    w t = η * (FN t + κ * θ t) + (1 - η) * b :=
  eq_18_15 t h4 h9 h10 h12t h12 h13 hqu hβ hq hη1

/-- **Exercise 18.1** (Miao, p. 614): a **search equilibrium** of the economy with capital:
sequences `C, K, I, N, u, v, θ, w, q^v, p, d` (with `u, v > 0`) such that (18.1)–(18.3) hold,
`d` is the dividend, shares satisfy `p_t = β(p_{t+1} + d_{t+1})` (one share outstanding), the
firm's capital Euler and job creation equations hold (`F_K`, `F_N` the marginal products), the
wage satisfies `w_t = η(F_N + κθ_t) + (1 − η)b`, and the resource constraint
`C_t + I_t + κv_t = F(K_t, N_t)` holds (benefits are financed by lump-sum taxes). -/
def dm_Ex1IsSearchEqm (MF : DMMatchingFn) (F FK FN : ℝ → ℝ → ℝ) (b κ β δ ρ η : ℝ)
    (C K I N u v θ w qv p d : ℕ → ℝ) : Prop :=
  ∀ t, 0 < u t ∧ 0 < v t ∧ θ t = v t / u t ∧ qv t = dm_q MF (θ t) ∧
    N (t + 1) = (1 - ρ) * N t + MF.M (u t) (v t) ∧ u t = 1 - N t ∧
    K (t + 1) = (1 - δ) * K t + I t ∧
    d t = F (K t) (N t) - w t * N t - κ * v t - I t ∧
    p t = β * (p (t + 1) + d (t + 1)) ∧
    1 = β * (FK (K (t + 1)) (N (t + 1)) + 1 - δ) ∧
    κ / qv t = β * (FN (K (t + 1)) (N (t + 1)) - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) ∧
    w t = η * (FN (K t) (N t) + κ * θ t) + (1 - η) * b ∧
    C t + I t + κ * v t = F (K t) (N t)

/-- Exercise 18.1: for `F(K, N) = AK^aN^{1−a}`, `F_K = aA(K/N)^{a−1}`. -/
theorem dm_ex1_FK {A a K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    HasDerivAt (fun k ↦ A * k ^ a * N ^ (1 - a)) (a * A * (K / N) ^ (a - 1)) K := by
  have h := ((Real.hasDerivAt_rpow_const (p := a) (Or.inl hK.ne')).const_mul A).mul_const
    (N ^ (1 - a))
  refine h.congr_deriv ?_
  rw [Real.div_rpow hK.le hN.le]
  have e : N ^ (1 - a) = (N ^ (a - 1))⁻¹ := by
    rw [← Real.rpow_neg hN.le]; ring_nf
  rw [e]
  have : 0 < N ^ (a - 1) := by positivity
  field_simp

/-- Exercise 18.1: for `F(K, N) = AK^aN^{1−a}`, `F_N = (1 − a)A(K/N)^a`. -/
theorem dm_ex1_FN {A a K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    HasDerivAt (fun n ↦ A * K ^ a * n ^ (1 - a)) ((1 - a) * A * (K / N) ^ a) N := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - a) (Or.inl hN.ne')).const_mul (A * K ^ a)
  refine h.congr_deriv ?_
  rw [Real.div_rpow hK.le hN.le]
  have e : N ^ (1 - a - 1) = (N ^ a)⁻¹ := by
    rw [← Real.rpow_neg hN.le]; ring_nf
  rw [e]
  have : 0 < N ^ a := by positivity
  field_simp

/-- Exercise 18.1: the steady-state capital–labour ratio `k* = (aA/(1/β − 1 + δ))^{1/(1−a)}`. -/
noncomputable def dm_ex1_kstar (A a β δ : ℝ) : ℝ := (a * A / (1 / β - 1 + δ)) ^ (1 / (1 - a))

/-- Exercise 18.1: the capital Euler equation `1 = β(aAk^{a−1} + 1 − δ)` pins down the
capital–labour ratio uniquely: `k = k*`. -/
theorem dm_ex1_kstar_unique {A a β δ k : ℝ} (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hβ : 0 < β) (hr : 0 < 1 / β - 1 + δ) (hk : 0 < k) :
    1 = β * (a * A * k ^ (a - 1) + 1 - δ) ↔ k = dm_ex1_kstar A a β δ := by
  set r := 1 / β - 1 + δ with hrdef
  have hc : 0 < a * A / r := by positivity
  have hks : 0 < dm_ex1_kstar A a β δ := Real.rpow_pos_of_pos hc _
  have h1a : (1 - a) ≠ 0 := by linarith
  -- `k*^{a−1} = r/(aA)`
  have hkey : dm_ex1_kstar A a β δ ^ (a - 1) = r / (a * A) := by
    rw [dm_ex1_kstar, ← Real.rpow_mul hc.le]
    have : 1 / (1 - a) * (a - 1) = -1 := by field_simp; ring
    rw [this, Real.rpow_neg_one, inv_div]
  have hEuler : ∀ x, (1 = β * (a * A * x + 1 - δ) ↔ x = r / (a * A)) := by
    intro x
    rw [hrdef]
    constructor
    · intro h; field_simp; field_simp at h; linarith
    · intro h; rw [h]; field_simp; ring
  rw [hEuler, ← hkey]
  constructor
  · intro h
    have hinj : Set.InjOn (fun x : ℝ ↦ x ^ (a - 1)) (Set.Ioi 0) := by
      intro x hx y hy hxy
      have := congrArg (fun z : ℝ ↦ z ^ (1 / (a - 1))) hxy
      simp only at this
      rwa [← Real.rpow_mul (Set.mem_Ioi.mp hx).le, ← Real.rpow_mul (Set.mem_Ioi.mp hy).le,
        mul_one_div_cancel (by linarith : a - 1 ≠ 0), Real.rpow_one, Real.rpow_one] at this
    exact hinj hk hks h
  · intro h; rw [h]

/-- **Exercise 18.1** (Miao, p. 614): **analysis of the steady state**. With `F = AK^aN^{1−a}`
and a constant job-filling rate, in a steady state with `K, N > 0` the capital Euler equation
gives `K/N = k*`; the job creation and wage equations then reduce to the basic DMP equations with
`A` replaced by the marginal product of labour `A_eff = (1 − a)Ak*^a`: `θ` solves (18.18) with
`A_eff`, the wage is on the wage curve with `A_eff`, and on `v = θu` the employment dynamics give
`u = ρ/(ρ + θq(θ))`. -/
theorem dm_ex1_steady (MF : DMMatchingFn) {A a b κ β δ ρ η K N u θ w : ℝ} (hA : 0 < A)
    (ha0 : 0 < a) (ha1 : a < 1) (hβ : 0 < β) (hr : 0 < 1 / β - 1 + δ) (hρ : 0 < ρ)
    (hK : 0 < K) (hN : 0 < N) (hθ : 0 < θ) (hu : 0 < u)
    (hEuler : 1 = β * (a * A * (K / N) ^ (a - 1) + 1 - δ))
    (hJC : κ / dm_q MF θ = β * ((1 - a) * A * (K / N) ^ a - w + (1 - ρ) * κ / dm_q MF θ))
    (hW : w = η * ((1 - a) * A * (K / N) ^ a + κ * θ) + (1 - η) * b)
    (hB : N = (1 - ρ) * N + MF.M u (θ * u)) (hNu : u = 1 - N) :
    K / N = dm_ex1_kstar A a β δ ∧
      dm_ssLHS MF κ β ρ η θ = β * (1 - η) * ((1 - a) * A * dm_ex1_kstar A a β δ ^ a - b) ∧
      w = dm_wageCurve ((1 - a) * A * dm_ex1_kstar A a β δ ^ a) b κ η θ ∧
      u = dm_uStar MF ρ θ := by
  have hk := (dm_ex1_kstar_unique hA ha0 ha1 hβ hr (div_pos hK hN)).mp hEuler
  rw [hk] at hJC hW
  have h16 := (eq_18_16 MF _ κ β ρ w θ).mp hJC
  have h18 := (eq_18_18 MF _ b κ β ρ η w θ).mp ⟨h16, hW⟩
  refine ⟨hk, h18.1, h18.2, (eq_18_19 MF hρ hθ hu).mp ?_⟩
  have hN' : N = 1 - u := by linarith
  rw [hN'] at hB
  linarith

/-- **Exercise 18.1** (Miao, p. 614): the steady state of the economy with capital is a search
equilibrium: with `k = k*`, `θ` solving (18.18) at `A_eff = (1 − a)Ak*^a`, `u = u*`, `N = 1 − u`,
`K = k*N`, `I = δK`, `v = θu`, the wage on the wage curve, dividends
`d = F − wN − κv − δK`, price `p = βd/(1 − β)` and consumption `C = F − δK − κv`. -/
theorem dm_ex1_steady_isSearchEqm (MF : DMMatchingFn) {A a b κ β δ ρ η θ : ℝ} (hA : 0 < A)
    (ha0 : 0 < a) (ha1 : a < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hr : 0 < 1 / β - 1 + δ)
    (hρ : 0 < ρ) (hθ : 0 < θ)
    (h : dm_ssLHS MF κ β ρ η θ = β * (1 - η) * ((1 - a) * A * dm_ex1_kstar A a β δ ^ a - b)) :
    let u := dm_uStar MF ρ θ
    let N := 1 - u
    let K := dm_ex1_kstar A a β δ * N
    let w := dm_wageCurve ((1 - a) * A * dm_ex1_kstar A a β δ ^ a) b κ η θ
    let d := A * K ^ a * N ^ (1 - a) - w * N - κ * (θ * u) - δ * K
    dm_Ex1IsSearchEqm MF (fun k n ↦ A * k ^ a * n ^ (1 - a))
      (fun k n ↦ a * A * (k / n) ^ (a - 1)) (fun k n ↦ (1 - a) * A * (k / n) ^ a)
      b κ β δ ρ η (fun _ ↦ A * K ^ a * N ^ (1 - a) - δ * K - κ * (θ * u)) (fun _ ↦ K)
      (fun _ ↦ δ * K) (fun _ ↦ N) (fun _ ↦ u) (fun _ ↦ θ * u) (fun _ ↦ θ) (fun _ ↦ w)
      (fun _ ↦ dm_q MF θ) (fun _ ↦ β * d / (1 - β)) (fun _ ↦ d) := by
  intro u N K w d t
  obtain ⟨hu0, hu1⟩ := dm_uStar_mem MF hρ hθ
  have hune : u ≠ 0 := hu0.ne'
  have hN : 0 < N := by simp only [N]; linarith
  have hks : 0 < dm_ex1_kstar A a β δ := Real.rpow_pos_of_pos (by positivity) _
  have hkN : K / N = dm_ex1_kstar A a β δ := by simp only [K]; field_simp
  have hB := (eq_18_19 MF hρ hθ hu0).mpr rfl
  have h16 := ((eq_18_18 MF _ b κ β ρ η w θ).mpr ⟨h, rfl⟩).1
  have hβ1' : 1 - β ≠ 0 := by linarith
  refine ⟨hu0, mul_pos hθ hu0, by field_simp, rfl, ?_, by simp only [N]; ring, by ring, rfl,
    ?_, ?_, ?_, ?_, by ring⟩
  · simp only [N]; rw [← hB]; ring
  · field_simp; ring
  · simp only [hkN]
    exact (dm_ex1_kstar_unique hA ha0 ha1 hβ0 hr hks).mpr rfl
  · simp only [hkN]
    exact (eq_18_16 MF _ κ β ρ w θ).mpr h16
  · simp only [hkN, w, dm_wageCurve]

/-- **Exercise 18.1** (Miao, p. 614): a search equilibrium of the economy with capital exists in
a concrete economy (Cobb–Douglas matching `μ = 1`, `α = 1/2`; `A = 1`, `a = 1/3`, `b = 0`,
`κ = 1`, `β = ρ = η = 1/2`, `δ = 1/10`). -/
theorem dm_ex1_searchEqm_exists :
    ∃ C K I N u v θ w qv p d : ℕ → ℝ,
      dm_Ex1IsSearchEqm (dm_cdMatching 1 (1 / 2) one_pos (by norm_num) (by norm_num))
        (fun k n ↦ 1 * k ^ (1 / 3 : ℝ) * n ^ (1 - 1 / 3 : ℝ))
        (fun k n ↦ 1 / 3 * 1 * (k / n) ^ (1 / 3 - 1 : ℝ))
        (fun k n ↦ (1 - 1 / 3) * 1 * (k / n) ^ (1 / 3 : ℝ))
        0 1 (1 / 2) (1 / 10) (1 / 2) (1 / 2) C K I N u v θ w qv p d := by
  have hAe : 0 < (1 - 1 / 3) * 1 * dm_ex1_kstar 1 (1 / 3) (1 / 2) (1 / 10) ^ (1 / 3 : ℝ) := by
    have : 0 < dm_ex1_kstar 1 (1 / 3) (1 / 2) (1 / 10) :=
      Real.rpow_pos_of_pos (by norm_num) _
    positivity
  obtain ⟨θ, ⟨hθ, h⟩, -⟩ := dm_cd_ss_existsUnique (μ := 1) (α := 1 / 2) one_pos (by norm_num)
    (by norm_num) (A := (1 - 1 / 3) * 1 * dm_ex1_kstar 1 (1 / 3) (1 / 2) (1 / 10) ^ (1 / 3 : ℝ))
    (b := 0) (κ := 1) (β := 1 / 2) (ρ := 1 / 2) (η := 1 / 2) one_pos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAe
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, dm_ex1_steady_isSearchEqm _ one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hθ h⟩

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 18.2: the planner's problem with endogenous job destruction

Miao, §18.4, Exercise 18.2, p. 614: "Following a similar analysis in Section 18.1, derive the
social planner's problem for the model in Section 18.2. Study efficiency properties of the
decentralized search equilibrium."

**Formulation.** In the model of §18.2 (Mortensen–Pissarides), let `E_t` be the measure of
matches at the start of period `t` (before the idiosyncratic draw `z ~ G`). The planner chooses
the reservation productivity `z_t` and vacancies `v_t`; matches with `z ≤ z_t` separate, so
employment is `N_t = P(z_t)E_t`, `P = 1 − G`, and `u_t = 1 − N_t`. Output is `AE_tH(z_t)`,
`H(z) = ∫_z^∞ x dG(x)`. With the job-finding rate `f(θ) = θq(θ)`, the planner solves
`max Σ βᵗ(AE_tH(z_t) + bu_t − κv_t)` subject to
`E_{t+1} = (1 − ρ^x)P(z_t)E_t + u_tf(v_t/u_t)`. The Lagrangian, with multiplier `β^{t+1}λ_{t+1}`
on the date-`t` constraint, has date-`t` terms `βᵗ · dm_mpLag(…)`.

* `dm_mp_foc_v`, `dm_mp_foc_z`, `dm_mp_foc_E`: the first-order conditions are the partial
  derivatives of `dm_mpLag` in `v`, `z` and `E`.
* `ex_18_2`: in a steady state, with `H′(z) = zP′(z)` (`G` has a density), the planner's
  conditions give the shadow value of a match `λ = A∫_{z*}^∞(z − z*)dG`, the planner's job
  creation condition `κ/q(θ) = β(1 − ξ(θ))A∫_{z*}^∞(z − z*)dG` and job destruction condition
  `ξθκ = (1 − ξ)(Az* − b) + β(1 − ρ^x)(1 − ξ)A∫_{z*}^∞(z − z*)dG`: the decentralised (18.44),
  (18.45) with `η` replaced by `ξ(θ)`.
* `ex_18_2_efficiency`: a decentralised steady state `(θ, z*)` satisfying (18.44)–(18.45)
  satisfies the planner's steady-state first-order conditions iff `ξ(θ) = η`: the Hosios
  condition again characterises efficiency.
* `dm_mp_exp_dist`: the exponential distribution `G(z) = 1 − e^{−z}` (mean 1, as in §18.2)
  satisfies the density hypothesis, with `P(z) = e^{−z}`, `H(z) = (z + 1)e^{−z}`.

Departure: `G` enters only through `P` and `H` and the density relation `H′ = zP′`; "efficient"
means "satisfies the planner's steady-state first-order conditions".
-/

namespace Miao.SearchAndMatching

/-- Exercise 18.2: the date-`t` terms of the planner's Lagrangian (divided by `βᵗ`):
`AEH(z) + b(1 − P(z)E) − κv + βλ′((1 − ρ^x)P(z)E + (1 − P(z)E)f(v/(1 − P(z)E))) − λE`. -/
noncomputable def dm_mpLag (f P H : ℝ → ℝ) (A b κ β ρx lam lam' E z v : ℝ) : ℝ :=
  A * E * H z + b * (1 - P z * E) - κ * v +
    β * lam' * ((1 - ρx) * P z * E + (1 - P z * E) * f (v / (1 - P z * E))) - lam * E

/-- Exercise 18.2: the derivative of `y ↦ U(y)f(v/U(y))` is `U′(f(θ) − θf′(θ))`, `θ = v/U`. -/
theorem dm_uf_hasDerivAt {f U : ℝ → ℝ} {v x U' f' : ℝ} (hU : HasDerivAt U U' x)
    (hU0 : U x ≠ 0) (hf : HasDerivAt f f' (v / U x)) :
    HasDerivAt (fun y ↦ U y * f (v / U y)) (U' * (f (v / U x) - v / U x * f')) x := by
  have h2 : HasDerivAt (fun y ↦ v / U y) (-(v * U') / U x ^ 2) x := by
    have := (hU.inv hU0).const_mul v
    refine (this.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun y ↦ by simp [div_eq_mul_inv]
  have h := hU.mul (hf.comp x h2)
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  field_simp
  ring

/-- **Exercise 18.2** (Miao, p. 614): the planner's first-order condition for `v`:
`∂/∂v = −κ + βλ′f′(θ)`. -/
theorem dm_mp_foc_v {f P H : ℝ → ℝ} {A b κ β ρx lam lam' E z v f' : ℝ}
    (hu : 1 - P z * E ≠ 0) (hf : HasDerivAt f f' (v / (1 - P z * E))) :
    HasDerivAt (fun x ↦ dm_mpLag f P H A b κ β ρx lam lam' E z x)
      (-κ + β * lam' * f') v := by
  have hd : HasDerivAt (fun x ↦ x / (1 - P z * E)) (1 / (1 - P z * E)) v :=
    (hasDerivAt_id' v).div_const _
  have h := (((hasDerivAt_id' v).const_mul κ).const_sub (A * E * H z + b * (1 - P z * E))).add
    ((((hf.comp v hd).const_mul (1 - P z * E)).const_add ((1 - ρx) * P z * E)).const_mul
      (β * lam')) |>.sub_const (lam * E)
  refine h.congr_deriv ?_
  field_simp

/-- **Exercise 18.2** (Miao, p. 614): the planner's first-order condition for the reservation
productivity `z`: `∂/∂z = AEH′(z) − bP′(z)E + βλ′((1 − ρ^x)P′(z)E − P′(z)E(f(θ) − θf′(θ)))`. -/
theorem dm_mp_foc_z {f P H : ℝ → ℝ} {A b κ β ρx lam lam' E z v f' P' H' : ℝ}
    (hP : HasDerivAt P P' z) (hH : HasDerivAt H H' z) (hu : 1 - P z * E ≠ 0)
    (hf : HasDerivAt f f' (v / (1 - P z * E))) :
    HasDerivAt (fun y ↦ dm_mpLag f P H A b κ β ρx lam lam' E y v)
      (A * E * H' - b * (P' * E) + β * lam' * ((1 - ρx) * P' * E -
        P' * E * (f (v / (1 - P z * E)) - v / (1 - P z * E) * f'))) z := by
  have hU : HasDerivAt (fun y ↦ 1 - P y * E) (-(P' * E)) z := by
    simpa using (hP.mul_const E).const_sub 1
  have hg := dm_uf_hasDerivAt hU hu hf
  have h := ((((hH.const_mul (A * E)).add (hU.const_mul b)).sub_const (κ * v)).add
    ((((hP.const_mul (1 - ρx)).mul_const E).add hg).const_mul (β * lam'))).sub_const (lam * E)
  refine h.congr_deriv ?_
  ring

/-- **Exercise 18.2** (Miao, p. 614): the planner's first-order condition for the stock of matches
`E`: `∂/∂E = AH(z) − bP(z) + βλ′((1 − ρ^x)P(z) − P(z)(f(θ) − θf′(θ))) − λ`. -/
theorem dm_mp_foc_E {f P H : ℝ → ℝ} {A b κ β ρx lam lam' E z v f' : ℝ}
    (hu : 1 - P z * E ≠ 0) (hf : HasDerivAt f f' (v / (1 - P z * E))) :
    HasDerivAt (fun e ↦ dm_mpLag f P H A b κ β ρx lam lam' e z v)
      (A * H z - b * P z + β * lam' * ((1 - ρx) * P z -
        P z * (f (v / (1 - P z * E)) - v / (1 - P z * E) * f')) - lam) E := by
  have hU : HasDerivAt (fun e ↦ 1 - P z * e) (-P z) E := by
    simpa using ((hasDerivAt_id' E).const_mul (P z)).const_sub 1
  have hg := dm_uf_hasDerivAt hU hu hf
  have hid := hasDerivAt_id' E
  have h := (((((hid.const_mul A).mul_const (H z)).add (hU.const_mul b)).sub_const (κ * v)).add
    (((hid.const_mul ((1 - ρx) * P z)).add hg).const_mul (β * lam'))).sub
      (hid.const_mul lam)
  refine h.congr_deriv ?_
  ring

/-- **Exercise 18.2** (Miao, p. 614): **the planner's steady state**. Let `θ = v/u`, with
`f(θ) = θq` and `f′(θ) = q(1 − ξ)` (`q = q(θ) > 0`, `ξ = ξ(θ) < 1`), `H′(z) = zP′(z)` with
`P′(z) ≠ 0`, `E ≠ 0`, and let the three first-order conditions hold with `λ′ = λ`. Then
`λ = A(H(z) − zP(z)) = A∫_z^∞(x − z)dG`, `κ/q = β(1 − ξ)A(H − zP)` (planner's job creation) and
`ξθκ = (1 − ξ)(Az − b) + β(1 − ρ^x)(1 − ξ)A(H − zP)` (planner's job destruction). -/
theorem ex_18_2 {A b κ β ρx lam E z θ q ξ Pz Hz P' : ℝ} (hq : 0 < q)
    (hξ : ξ < 1) (hP' : P' ≠ 0) (hE : E ≠ 0)
    (hv : -κ + β * lam * (q * (1 - ξ)) = 0)
    (hz : A * E * (z * P') - b * (P' * E) + β * lam * ((1 - ρx) * P' * E -
      P' * E * (θ * q - θ * (q * (1 - ξ)))) = 0)
    (hE' : A * Hz - b * Pz + β * lam * ((1 - ρx) * Pz -
      Pz * (θ * q - θ * (q * (1 - ξ)))) - lam = 0) :
    lam = A * (Hz - z * Pz) ∧ κ / q = β * (1 - ξ) * (A * (Hz - z * Pz)) ∧
      ξ * θ * κ = (1 - ξ) * (A * z - b) + β * (1 - ρx) * (1 - ξ) * (A * (Hz - z * Pz)) := by
  have hz' : A * z - b + β * lam * ((1 - ρx) - θ * q * ξ) = 0 := by
    have key : (P' * E) * (A * z - b + β * lam * ((1 - ρx) - θ * q * ξ)) = 0 := by
      linear_combination hz
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (mul_ne_zero hP' hE)
    · exact h
  have hlam : lam = A * (Hz - z * Pz) := by linear_combination (-1 : ℝ) * hE' + Pz * hz'
  have h1 : 0 < 1 - ξ := by linarith
  refine ⟨hlam, ?_, ?_⟩
  · rw [← hlam, div_eq_iff hq.ne']
    linear_combination (-1 : ℝ) * hv
  · rw [← hlam]
    linear_combination (-(1 - ξ)) * hz' + (-(ξ * θ)) * hv

/-- **Exercise 18.2** (Miao, p. 614): **efficiency**. Let the decentralised steady state
`(θ, z*)` satisfy the job creation condition (18.44) `κ/q(θ) = β(1 − η)A∫_{z*}^∞(z − z*)dG` and
the job destruction condition (18.45)
`ηθκ = (1 − η)(Az* − b) + β(1 − ρ^x)(1 − η)A∫_{z*}^∞(z − z*)dG`, with `A∫(z − z*)dG > 0`.
Then it satisfies the planner's steady-state first-order conditions (for some multiplier `λ`)
iff `ξ(θ) = η` (the Hosios condition). -/
theorem ex_18_2_efficiency {A b κ β ρx η E z θ q ξ Pz Hz P' : ℝ} (hβ : 0 < β) (hq : 0 < q)
    (hη1 : η < 1) (hP' : P' ≠ 0) (hE : E ≠ 0) (hI : 0 < A * (Hz - z * Pz))
    (h44 : κ / q = β * (1 - η) * (A * (Hz - z * Pz)))
    (h45 : η * θ * κ = (1 - η) * (A * z - b) + β * (1 - ρx) * (1 - η) * (A * (Hz - z * Pz))) :
    (∃ lam : ℝ, -κ + β * lam * (q * (1 - ξ)) = 0 ∧
      A * E * (z * P') - b * (P' * E) + β * lam * ((1 - ρx) * P' * E -
        P' * E * (θ * q - θ * (q * (1 - ξ)))) = 0 ∧
      A * Hz - b * Pz + β * lam * ((1 - ρx) * Pz -
        Pz * (θ * q - θ * (q * (1 - ξ)))) - lam = 0) ↔ ξ = η := by
  set I := A * (Hz - z * Pz) with hIdef
  have hκ : κ = β * (1 - η) * I * q := by
    rw [div_eq_iff hq.ne'] at h44; exact h44
  constructor
  · rintro ⟨lam, hv, hz, hE'⟩
    have key : (P' * E) * (A * z - b + β * lam * ((1 - ρx) - θ * q * ξ)) = 0 := by
      linear_combination hz
    have hz' := (mul_eq_zero.mp key).resolve_left (mul_ne_zero hP' hE)
    have hlam : lam = I := by
      rw [hIdef]
      linear_combination (-1 : ℝ) * hE' + Pz * hz'
    rw [hlam, hκ] at hv
    have key2 : β * I * q * (ξ - η) = 0 := by linear_combination (-1 : ℝ) * hv
    have hne : β * I * q ≠ 0 := by positivity
    have := (mul_eq_zero.mp key2).resolve_left hne
    linarith
  · rintro rfl
    have hX : (1 - ξ) * (A * z - b + β * (1 - ρx) * I - β * I * θ * q * ξ) = 0 := by
      linear_combination (-1 : ℝ) * h45 + ξ * θ * hκ
    have hX' := (mul_eq_zero.mp hX).resolve_left (by linarith)
    refine ⟨I, ?_, ?_, ?_⟩
    · rw [hκ]; ring
    · linear_combination (P' * E) * hX'
    · rw [hIdef]
      rw [hIdef] at hX'
      linear_combination Pz * hX'

/-- Exercise 18.2: the exponential distribution `G(z) = 1 − e^{−z}` (mean 1) satisfies the
density hypothesis `H′(z) = zP′(z)` with `P(z) = e^{−z}` and `H(z) = ∫_z^∞ x dG = (z + 1)e^{−z}`;
`P(0) = 1` and the mean is `H(0) = 1`. -/
theorem dm_mp_exp_dist (z : ℝ) :
    HasDerivAt (fun x ↦ Real.exp (-x)) (-Real.exp (-z)) z ∧
      HasDerivAt (fun x ↦ (x + 1) * Real.exp (-x)) (z * -Real.exp (-z)) z ∧
      Real.exp (-0) = 1 ∧ (0 + 1) * Real.exp (-0) = 1 := by
  have hP : HasDerivAt (fun x ↦ Real.exp (-x)) (-Real.exp (-z)) z := by
    exact ((hasDerivAt_id' z).neg.exp).congr_deriv (by simp)
  refine ⟨hP, ?_, by simp, by simp⟩
  have h := ((hasDerivAt_id' z).add_const 1).mul hP
  refine h.congr_deriv ?_
  ring

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Tools for Miao §§18.2–18.3: Nash bargaining, first-order and envelope conditions

Generic facts used by the derivations of Miao, *Economic Dynamics in Discrete Time*, §§18.2–18.3
(pp. 600–614):

* **Nash bargaining with affine surpluses.** If the worker's surplus is `a + λ w` and the firm's is
  `c − w`, then `w` maximises the Nash product `(a + λ w)^η (c − w)^(1−η)` over the feasible wages
  iff `(1 − η)(a + λ w) = η λ (c − w)` (`jd_nash_iff`). This is the first-order condition used for
  (18.37)–(18.38) (`λ = 1`) and in §18.3 (`λ = Λ_t`, the marginal utility). The proof is the
  weighted AM–GM inequality with its equality case (`jd_nash_le`, `jd_nash_eq_iff`), so it is a
  global statement, not only a first-order condition.
* **First-order and envelope conditions** (`jd_foc`, `jd_envelope`): at a maximiser the derivative
  of the objective vanishes; if `g ≤ W` with equality at `x₀` and both are differentiable there,
  then `W′(x₀) = g′(x₀)` (the envelope condition, with `g` the objective at the optimal control).
* **Constant returns to scale**: the partial derivatives of a linearly homogeneous function are
  homogeneous of degree zero (`jd_partial_homog_one`, `jd_partial_homog_two`).
* **Affine recursions** `u_{t+1} = a u_t + r` (`jd_affine_sol`, `jd_affine_antitone`,
  `jd_affine_tendsto`): used for unemployment dynamics (18.43).
-/

namespace Miao.SearchAndMatching

open Filter Topology

/-- Weighted AM–GM in the form used for Nash bargaining (Miao, (18.11), p. 590, used on
pp. 601 and 612): `x^η y^(1−η) ≤ η^η (1−η)^(1−η) (x + y)`. -/
theorem jd_nash_le {η x y : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ η * y ^ (1 - η) ≤ η ^ η * (1 - η) ^ (1 - η) * (x + y) := by
  have h1η : 0 < 1 - η := by linarith
  have hp1 : 0 ≤ x / η := div_nonneg hx hη0.le
  have hp2 : 0 ≤ y / (1 - η) := div_nonneg hy h1η.le
  have key := Real.geom_mean_le_arith_mean2_weighted hη0.le h1η.le hp1 hp2 (by ring)
  have ex : x = η * (x / η) := by field_simp
  have ey : y = (1 - η) * (y / (1 - η)) := by field_simp
  have hxe : x ^ η = η ^ η * (x / η) ^ η := by
    conv_lhs => rw [ex]
    exact Real.mul_rpow hη0.le hp1
  have hye : y ^ (1 - η) = (1 - η) ^ (1 - η) * (y / (1 - η)) ^ (1 - η) := by
    conv_lhs => rw [ey]
    exact Real.mul_rpow h1η.le hp2
  have hs : η * (x / η) + (1 - η) * (y / (1 - η)) = x + y := by field_simp
  rw [hxe, hye, ← hs]
  have hc : 0 ≤ η ^ η * (1 - η) ^ (1 - η) :=
    mul_nonneg (Real.rpow_nonneg hη0.le _) (Real.rpow_nonneg h1η.le _)
  calc η ^ η * (x / η) ^ η * ((1 - η) ^ (1 - η) * (y / (1 - η)) ^ (1 - η))
      = η ^ η * (1 - η) ^ (1 - η) * ((x / η) ^ η * (y / (1 - η)) ^ (1 - η)) := by ring
    _ ≤ η ^ η * (1 - η) ^ (1 - η) * (η * (x / η) + (1 - η) * (y / (1 - η))) :=
        mul_le_mul_of_nonneg_left key hc

/-- The equality case of `jd_nash_le` (Miao, p. 591): equality iff `(1 − η) x = η y`, i.e. the
worker receives the share `η` of the total surplus. -/
theorem jd_nash_eq_iff {η x y : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ η * y ^ (1 - η) = η ^ η * (1 - η) ^ (1 - η) * (x + y) ↔ (1 - η) * x = η * y := by
  have h1η : 0 < 1 - η := by linarith
  have hp1 : 0 ≤ x / η := div_nonneg hx hη0.le
  have hp2 : 0 ≤ y / (1 - η) := div_nonneg hy h1η.le
  have key := Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos hη0 h1η hp1 hp2 (by ring)
  have ex : x = η * (x / η) := by field_simp
  have ey : y = (1 - η) * (y / (1 - η)) := by field_simp
  have hxe : x ^ η = η ^ η * (x / η) ^ η := by
    conv_lhs => rw [ex]
    exact Real.mul_rpow hη0.le hp1
  have hye : y ^ (1 - η) = (1 - η) ^ (1 - η) * (y / (1 - η)) ^ (1 - η) := by
    conv_lhs => rw [ey]
    exact Real.mul_rpow h1η.le hp2
  have hs : η * (x / η) + (1 - η) * (y / (1 - η)) = x + y := by field_simp
  have hc : 0 < η ^ η * (1 - η) ^ (1 - η) :=
    mul_pos (Real.rpow_pos_of_pos hη0 _) (Real.rpow_pos_of_pos h1η _)
  rw [hxe, hye, ← hs]
  have e1 : η ^ η * (x / η) ^ η * ((1 - η) ^ (1 - η) * (y / (1 - η)) ^ (1 - η))
      = η ^ η * (1 - η) ^ (1 - η) * ((x / η) ^ η * (y / (1 - η)) ^ (1 - η)) := by ring
  rw [e1, mul_right_inj' hc.ne', key]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- **Nash bargaining with affine surpluses** (Miao, (18.11), p. 590; (18.37)–(18.38), p. 602;
p. 613). With worker surplus `a + λ w` (`λ > 0`) and firm surplus `c − w`, a feasible wage `w`
maximises the Nash product over all feasible wages iff `(1 − η)(a + λ w) = η λ (c − w)`. -/
theorem jd_nash_iff {η a c lam w : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hlam : 0 < lam)
    (hW : 0 ≤ a + lam * w) (hF : 0 ≤ c - w) :
    (∀ w', 0 ≤ a + lam * w' → 0 ≤ c - w' →
      (a + lam * w') ^ η * (c - w') ^ (1 - η) ≤ (a + lam * w) ^ η * (c - w) ^ (1 - η)) ↔
      (1 - η) * (a + lam * w) = η * lam * (c - w) := by
  have h1η : 0 < 1 - η := by linarith
  set K : ℝ := η ^ η * (1 - η) ^ (1 - η) with hK
  -- the Nash product equals `lam^η (x^η y^(1-η))` with `x = (a + lam w)/lam`, `y = c - w`
  have rew : ∀ w', 0 ≤ a + lam * w' → (a + lam * w') ^ η * (c - w') ^ (1 - η)
      = lam ^ η * (((a + lam * w') / lam) ^ η * (c - w') ^ (1 - η)) := by
    intro w' h
    have : a + lam * w' = lam * ((a + lam * w') / lam) := by field_simp
    conv_lhs => rw [this, Real.mul_rpow hlam.le (div_nonneg h hlam.le)]
    ring
  have hS : (a + lam * w) / lam + (c - w) = a / lam + c := by field_simp; ring
  have hsum : ∀ w', (a + lam * w') / lam + (c - w') = a / lam + c := by
    intro w'; field_simp; ring
  have hS0 : 0 ≤ a / lam + c := by rw [← hS]; exact add_nonneg (div_nonneg hW hlam.le) hF
  have hpos : 0 < lam ^ η := Real.rpow_pos_of_pos hlam _
  -- the candidate maximiser
  set w0 : ℝ := c - (1 - η) * (a / lam + c) with hw0
  have hx0 : (a + lam * w0) / lam = η * (a / lam + c) := by
    rw [hw0]; field_simp; ring
  have hW0 : 0 ≤ a + lam * w0 := by
    have : a + lam * w0 = lam * (η * (a / lam + c)) := by rw [← hx0]; field_simp
    rw [this]; exact mul_nonneg hlam.le (mul_nonneg hη0.le hS0)
  have hF0 : 0 ≤ c - w0 := by rw [hw0]; nlinarith
  have hval0 : (a + lam * w0) ^ η * (c - w0) ^ (1 - η) = lam ^ η * (K * (a / lam + c)) := by
    rw [rew w0 hW0]
    congr 1
    rw [← hsum w0]
    refine (jd_nash_eq_iff hη0 hη1 (div_nonneg hW0 hlam.le) hF0).2 ?_
    rw [hx0, hw0]; ring
  have hle : ∀ w', 0 ≤ a + lam * w' → 0 ≤ c - w' →
      (a + lam * w') ^ η * (c - w') ^ (1 - η) ≤ lam ^ η * (K * (a / lam + c)) := by
    intro w' h1 h2
    rw [rew w' h1, ← hsum w']
    exact mul_le_mul_of_nonneg_left (jd_nash_le hη0 hη1 (div_nonneg h1 hlam.le) h2) hpos.le
  have hfoc : (1 - η) * (a + lam * w) = η * lam * (c - w) ↔
      (1 - η) * ((a + lam * w) / lam) = η * (c - w) := by
    constructor
    · intro h; field_simp; linarith
    · intro h; field_simp at h; linarith
  rw [hfoc, ← jd_nash_eq_iff hη0 hη1 (div_nonneg hW hlam.le) hF, hS]
  constructor
  · intro h
    have h1 := h w0 hW0 hF0
    rw [hval0, rew w hW] at h1
    have h2 := hle w hW hF
    rw [rew w hW] at h2
    have h1' := le_of_mul_le_mul_left h1 hpos
    have h2' := le_of_mul_le_mul_left h2 hpos
    rw [← hK]; linarith
  · intro h w' h1 h2
    rw [rew w hW, h, ← hK]
    exact hle w' h1 h2

/-- First-order condition (Miao, pp. 601, 609–611): if `y₀` maximises a function differentiable
at `y₀`, its derivative there is zero. -/
theorem jd_foc {h : ℝ → ℝ} {y₀ d : ℝ} (hmax : ∀ y, h y ≤ h y₀) (hd : HasDerivAt h d y₀) :
    d = 0 :=
  IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall hmax) hd

/-- Envelope condition (Miao, pp. 609–612): if `g ≤ W` with equality at `x₀` (`g` is the objective
evaluated at the control that is optimal at `x₀`), and both are differentiable at `x₀`, then
`W′(x₀) = g′(x₀)`. -/
theorem jd_envelope {W g : ℝ → ℝ} {x₀ dW dg : ℝ} (hle : ∀ x, g x ≤ W x) (heq : g x₀ = W x₀)
    (hW : HasDerivAt W dW x₀) (hg : HasDerivAt g dg x₀) : dW = dg := by
  have hmin : IsLocalMin (fun x => W x - g x) x₀ :=
    Filter.Eventually.of_forall fun x => by simp only; linarith [hle x]
  have := hmin.hasDerivAt_eq_zero (hW.sub hg)
  linarith

/-- Constant returns to scale (Miao, p. 610, used for (18.51)): if `F` is linearly homogeneous on
the positive quadrant and differentiable in its first argument with partial derivative `F₁`,
then `F₁` is homogeneous of degree zero. -/
theorem jd_partial_homog_one {F F₁ : ℝ → ℝ → ℝ}
    (hhom : ∀ t k l, 0 < t → 0 < k → 0 < l → F (t * k) (t * l) = t * F k l)
    (hd : ∀ k l, 0 < k → 0 < l → HasDerivAt (fun x => F x l) (F₁ k l) k)
    {t k l : ℝ} (ht : 0 < t) (hk : 0 < k) (hl : 0 < l) : F₁ (t * k) (t * l) = F₁ k l := by
  have h1 : HasDerivAt (fun x => F (t * x) (t * l)) (F₁ (t * k) (t * l) * t) k := by
    have := (hd (t * k) (t * l) (mul_pos ht hk) (mul_pos ht hl)).comp k
      ((hasDerivAt_id k).const_mul t)
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun x => F (t * x) (t * l)) (t * F₁ k l) k := by
    have h3 := (hd k l hk hl).const_mul t
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hk] with x hx
    exact hhom t x l ht hx hl
  have := h1.unique h2
  have ht' : t ≠ 0 := ht.ne'
  have : t * F₁ (t * k) (t * l) = t * F₁ k l := by linarith
  exact mul_left_cancel₀ ht' this

/-- Constant returns to scale, second argument (Miao, p. 613, used for (18.56)): the partial
derivative `F₂` of a linearly homogeneous `F` is homogeneous of degree zero. -/
theorem jd_partial_homog_two {F F₂ : ℝ → ℝ → ℝ}
    (hhom : ∀ t k l, 0 < t → 0 < k → 0 < l → F (t * k) (t * l) = t * F k l)
    (hd : ∀ k l, 0 < k → 0 < l → HasDerivAt (fun y => F k y) (F₂ k l) l)
    {t k l : ℝ} (ht : 0 < t) (hk : 0 < k) (hl : 0 < l) : F₂ (t * k) (t * l) = F₂ k l := by
  have h1 : HasDerivAt (fun y => F (t * k) (t * y)) (F₂ (t * k) (t * l) * t) l := by
    have := (hd (t * k) (t * l) (mul_pos ht hk) (mul_pos ht hl)).comp l
      ((hasDerivAt_id l).const_mul t)
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun y => F (t * k) (t * y)) (t * F₂ k l) l := by
    have h3 := (hd k l hk hl).const_mul t
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hl] with y hy
    exact hhom t k y ht hk hy
  have := h1.unique h2
  have : t * F₂ (t * k) (t * l) = t * F₂ k l := by linarith
  exact mul_left_cancel₀ ht.ne' this

/-- Solution of the affine recursion `u_{t+1} = a u_t + r` (Miao, (18.43), p. 603): with
`ū = r/(1 − a)`, `u_t − ū = aᵗ (u₀ − ū)`. -/
theorem jd_affine_sol {a r : ℝ} {u : ℕ → ℝ} (ha : a ≠ 1) (hu : ∀ t, u (t + 1) = a * u t + r)
    (t : ℕ) : u t - r / (1 - a) = a ^ t * (u 0 - r / (1 - a)) := by
  have h1a : (1 - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hu n, pow_succ]
    have : a * u n + r - r / (1 - a) = a * (u n - r / (1 - a)) := by field_simp; ring
    rw [this, ih]; ring

/-- Monotone adjustment (Miao, p. 607): if `0 ≤ a < 1` and `u₀ ≥ ū`, the solution of
`u_{t+1} = a u_t + r` is nonincreasing and stays above `ū = r/(1 − a)`. -/
theorem jd_affine_antitone {a r : ℝ} {u : ℕ → ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hu : ∀ t, u (t + 1) = a * u t + r) (h0 : r / (1 - a) ≤ u 0) :
    Antitone u ∧ ∀ t, r / (1 - a) ≤ u t := by
  have hsol := jd_affine_sol ha1.ne hu
  have hge : ∀ t, r / (1 - a) ≤ u t := fun t => by
    have := hsol t
    have : 0 ≤ a ^ t * (u 0 - r / (1 - a)) := mul_nonneg (pow_nonneg ha0 t) (by linarith)
    linarith
  refine ⟨antitone_nat_of_succ_le fun t => ?_, hge⟩
  have e1 := hsol t
  have e2 := hsol (t + 1)
  have : a ^ (t + 1) * (u 0 - r / (1 - a)) ≤ a ^ t * (u 0 - r / (1 - a)) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact pow_le_pow_of_le_one ha0 ha1.le (Nat.le_succ t)
  linarith

/-- Convergence (Miao, pp. 595, 607): if `|a| < 1`, the solution of `u_{t+1} = a u_t + r`
converges to `ū = r/(1 − a)`. -/
theorem jd_affine_tendsto {a r : ℝ} {u : ℕ → ℝ} (ha : |a| < 1)
    (hu : ∀ t, u (t + 1) = a * u t + r) : Tendsto u atTop (𝓝 (r / (1 - a))) := by
  have ha1 : a ≠ 1 := by intro h; rw [h] at ha; simp at ha
  have hsol := jd_affine_sol ha1 hu
  have hp : Tendsto (fun t : ℕ => a ^ t * (u 0 - r / (1 - a))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one ha).mul_const (u 0 - r / (1 - a))
  have : u = fun t => a ^ t * (u 0 - r / (1 - a)) + r / (1 - a) := by
    funext t; linarith [hsol t]
  rw [this]
  simpa using hp.add_const (r / (1 - a))

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The productivity distribution of Miao §18.2: the option-value integral

Miao, *Economic Dynamics in Discrete Time*, §18.2, pp. 600–604. Idiosyncratic productivity `z`
is drawn from a distribution `G` on `(0, ∞)` with mean `1`. Everything in §18.2 depends on `G`
only through the integral

  `Φ(c) = ∫_c^∞ (z − c) dG(z) = ∫ max(z − c, 0) dG(z)`  (`jd_Phi`, `jd_Phi_eq_setIntegral`),

the expected surplus above a reservation productivity `c`, which appears in (18.41)–(18.45).
`G` is a probability measure `μ` on `ℝ` with `∫ |z| dμ < ∞`; the book's support and mean
assumptions (`μ(−∞, 0] = 0`, `∫ z dμ = 1`) are only needed for `jd_Phi_of_nonpos`.

Proved: `Φ ≥ 0` and is antitone, `1`-Lipschitz and continuous; `Φ(c′) − Φ(c) ≥ (c − c′)(1 − G(c))`
for `c′ ≤ c` (`jd_Phi_gap`), so `Φ` is strictly decreasing where `1 − G > 0`; `Φ(c) > 0` iff
`G(c) < 1` (`jd_Phi_pos_iff`); `Φ(c) = 1 − c` for `c ≤ 0` (`jd_Phi_of_nonpos`); `Φ(c) → 0` as
`c → ∞` (`jd_Phi_tendsto_atTop`); and `Φ′(c) = −(1 − G(c))` at every `c` that is not an atom of
`G` (`jd_Phi_hasDerivAt`), the slope used in the linearisation of the job creation condition.
-/

namespace Miao.SearchAndMatching

open MeasureTheory Filter Topology

/-- Miao, (18.41), p. 603: the option-value integral `Φ(c) = ∫ max(z − c, 0) dG(z)`. -/
noncomputable def jd_Phi (μ : Measure ℝ) (c : ℝ) : ℝ := ∫ z, max (z - c) 0 ∂μ

/-- Miao, p. 600: the distribution function `G(c) = μ(−∞, c]` of idiosyncratic productivity. -/
noncomputable def jd_G (μ : Measure ℝ) (c : ℝ) : ℝ := μ.real (Set.Iic c)

/-- Miao, p. 600: `1 − G(c) = μ(c, ∞)` for a probability measure. -/
theorem jd_one_sub_G (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    1 - jd_G μ c = μ.real (Set.Ioi c) := by
  unfold jd_G
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- Miao, p. 600: `G` is nondecreasing. -/
theorem jd_G_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] : Monotone (jd_G μ) := by
  intro c c' h
  exact measureReal_mono (Set.Iic_subset_Iic.mpr h)

/-- Miao, p. 600: `0 ≤ G ≤ 1`. -/
theorem jd_G_mem (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    0 ≤ jd_G μ c ∧ jd_G μ c ≤ 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

/-- The integrand of `Φ` is integrable. -/
theorem jd_Phi_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (c : ℝ) : Integrable (fun z => max (z - c) 0) μ :=
  (hint.sub (integrable_const c)).pos_part

/-- Miao, p. 603: `Φ(c) ≥ 0`. -/
theorem jd_Phi_nonneg (μ : Measure ℝ) (c : ℝ) : 0 ≤ jd_Phi μ c :=
  integral_nonneg fun _ => le_max_right _ _

/-- Miao, (18.41), p. 603: `Φ(c) = ∫_c^∞ (z − c) dG(z)`. -/
theorem jd_Phi_eq_setIntegral (μ : Measure ℝ) (c : ℝ) :
    jd_Phi μ c = ∫ z in Set.Ioi c, (z - c) ∂μ := by
  unfold jd_Phi
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext z
  by_cases hz : c < z
  · simp [Set.indicator, hz, max_eq_left (sub_nonneg.mpr hz.le)]
  · simp [Set.indicator, hz, max_eq_right (sub_nonpos.mpr (not_lt.mp hz))]

/-- Miao, p. 604 (the job creation curve slopes down): `Φ` is antitone. -/
theorem jd_Phi_antitone {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) : Antitone (jd_Phi μ) := by
  intro c c' h
  exact integral_mono (jd_Phi_integrable hint c') (jd_Phi_integrable hint c)
    fun z => max_le_max (by linarith) le_rfl

/-- `Φ` is `1`-Lipschitz: `Φ(c) − Φ(c′) ≤ c′ − c` for `c ≤ c′`. -/
theorem jd_Phi_sub_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {c c' : ℝ} (h : c ≤ c') :
    jd_Phi μ c - jd_Phi μ c' ≤ c' - c := by
  unfold jd_Phi
  rw [← integral_sub (jd_Phi_integrable hint c) (jd_Phi_integrable hint c')]
  have : ∫ _z, (c' - c) ∂μ = c' - c := by simp
  rw [← this]
  refine integral_mono ((jd_Phi_integrable hint c).sub (jd_Phi_integrable hint c'))
    (integrable_const _) fun z => ?_
  simp only
  rcases le_total (z - c') 0 with h1 | h1 <;> rcases le_total (z - c) 0 with h2 | h2 <;>
    simp only [max_eq_left, max_eq_right, h1, h2] <;> linarith

/-- `|Φ(c) − Φ(c′)| ≤ |c − c′|`. -/
theorem jd_Phi_abs_sub_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (c c' : ℝ) :
    |jd_Phi μ c - jd_Phi μ c'| ≤ |c - c'| := by
  rcases le_total c c' with h | h
  · have h1 := jd_Phi_sub_le hint h
    have h2 := jd_Phi_antitone hint h
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h1 := jd_Phi_sub_le hint h
    have h2 := jd_Phi_antitone hint h
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- `Φ` is continuous. -/
theorem jd_Phi_continuous {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) : Continuous (jd_Phi μ) := by
  refine (LipschitzWith.of_dist_le_mul fun c c' => ?_).continuous (K := 1)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  exact jd_Phi_abs_sub_le hint c c'

/-- Miao, p. 604: for `c′ ≤ c`, `Φ(c′) − Φ(c) ≥ (c − c′)(1 − G(c))`; `Φ` strictly decreases
wherever matches above the cutoff have positive probability. -/
theorem jd_Phi_gap {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {c c' : ℝ} (h : c' ≤ c) :
    (c - c') * μ.real (Set.Ioi c) ≤ jd_Phi μ c' - jd_Phi μ c := by
  unfold jd_Phi
  rw [← integral_sub (jd_Phi_integrable hint c') (jd_Phi_integrable hint c)]
  have : ∫ z, (Set.Ioi c).indicator (fun _ => c - c') z ∂μ = (c - c') * μ.real (Set.Ioi c) := by
    rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_comm]
  rw [← this]
  refine integral_mono ((integrable_const (c - c')).indicator measurableSet_Ioi)
    ((jd_Phi_integrable hint c').sub (jd_Phi_integrable hint c)) fun z => ?_
  simp only [Set.indicator, Set.mem_Ioi]
  split_ifs with hz
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
  · rcases le_total (z - c') 0 with h1 | h1
    · rw [max_eq_right h1, max_eq_right (by linarith)]; simp
    · rw [max_eq_left h1, max_eq_right (by linarith)]; linarith

/-- Miao, p. 604: `Φ(c) > 0` iff `G(c) < 1`, i.e. iff `μ(c, ∞) > 0`. -/
theorem jd_Phi_pos_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (c : ℝ) : 0 < jd_Phi μ c ↔ 0 < μ (Set.Ioi c) := by
  unfold jd_Phi
  rw [integral_pos_iff_support_of_nonneg (f := fun z => max (z - c) 0)
    (fun _ => le_max_right _ _) (jd_Phi_integrable hint c)]
  have : Function.support (fun z => max (z - c) 0) = Set.Ioi c := by
    ext z
    simp only [Function.mem_support, Set.mem_Ioi, ne_eq]
    constructor
    · intro hz
      by_contra h
      exact hz (max_eq_right (by linarith [not_lt.mp h]))
    · intro hz
      rw [max_eq_left (by linarith)]
      linarith
  rw [this]

/-- Miao, p. 604: `Φ(c) > 0` iff `1 − G(c) > 0` (real-valued form). -/
theorem jd_Phi_pos_iff_real {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (c : ℝ) : 0 < jd_Phi μ c ↔ 0 < μ.real (Set.Ioi c) := by
  rw [jd_Phi_pos_iff hint, measureReal_def, ENNReal.toReal_pos_iff]
  simp [measure_lt_top]

/-- Miao, p. 604: `Φ` is strictly decreasing to the right of a point where it is positive:
`c₁ < c₂` and `Φ(c₁) > 0` imply `Φ(c₂) < Φ(c₁)`. -/
theorem jd_Phi_strictAnti_of_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {c₁ c₂ : ℝ} (hc : c₁ < c₂) (hP : 0 < jd_Phi μ c₁) :
    jd_Phi μ c₂ < jd_Phi μ c₁ := by
  rcases (jd_Phi_nonneg μ c₂).lt_or_eq with h | h
  · have hm := (jd_Phi_pos_iff_real hint c₂).mp h
    have hgap := jd_Phi_gap hint hc.le
    have : 0 < (c₂ - c₁) * μ.real (Set.Ioi c₂) := mul_pos (by linarith) hm
    linarith
  · rw [← h]; exact hP

/-- Miao, p. 600 (support `(0, ∞)`, mean `1`): `Φ(c) = 1 − c` for `c ≤ 0`. -/
theorem jd_Phi_of_nonpos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (hsupp : μ (Set.Iic 0) = 0) (hmean : ∫ z, z ∂μ = 1)
    {c : ℝ} (hc : c ≤ 0) : jd_Phi μ c = 1 - c := by
  unfold jd_Phi
  have hae : (fun z => max (z - c) 0) =ᵐ[μ] fun z => z - c := by
    have : ∀ᵐ z ∂μ, z ∉ Set.Iic (0 : ℝ) := measure_eq_zero_iff_ae_notMem.mp hsupp
    filter_upwards [this] with z hz
    simp only [Set.mem_Iic, not_le] at hz
    exact max_eq_left (by linarith)
  rw [integral_congr_ae hae, integral_sub hint (integrable_const c), hmean]
  simp

/-- Miao, p. 604: `Φ(c) → 0` as `c → ∞`. -/
theorem jd_Phi_tendsto_atTop {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) : Tendsto (jd_Phi μ) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun c z => max (z - c) 0) (f := fun _ => (0 : ℝ)) (fun z => |z|)
    (Eventually.of_forall fun c => (jd_Phi_integrable hint c).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop 0] with c hc
      refine Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self z]) (abs_nonneg z))
    hint.abs
    (Eventually.of_forall fun z => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop z] with c hc
      exact (max_eq_right (by linarith)).symm)
  have e : jd_Phi μ = fun n => ∫ a, max (a - n) 0 ∂μ := rfl
  rw [e]
  simpa using h

/-- Miao, p. 603 (linearisation of (18.41)): at a non-atom `c` of `G`, `Φ′(c) = −(1 − G(c))`. -/
theorem jd_Phi_hasDerivAt {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {c : ℝ} (hc : μ {c} = 0) :
    HasDerivAt (jd_Phi μ) (-μ.real (Set.Ioi c)) c := by
  set g : ℝ → ℝ := fun r => μ.real (Set.Icc (c - r) (c + r)) with hg
  have gmono : MonotoneOn g (Set.Ici 0) := by
    intro r _ r' _ h
    exact measureReal_mono (Set.Icc_subset_Icc (by linarith) (by linarith))
  -- `g r → μ {c} = 0` as `r ↓ 0`
  have hlim : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_measure_biInter_gt (μ := μ) (s := fun r => Set.Icc (c - r) (c + r))
      (a := (0 : ℝ)) (fun r _ => measurableSet_Icc.nullMeasurableSet)
      (fun i j _ hij => Set.Icc_subset_Icc (by linarith) (by linarith))
      ⟨1, one_pos, measure_ne_top _ _⟩
    have hint' : (⋂ r > (0 : ℝ), Set.Icc (c - r) (c + r)) = {c} := by
      ext z
      simp only [Set.mem_iInter, Set.mem_Icc, Set.mem_singleton_iff]
      constructor
      · intro hz
        by_contra hne
        have hpos : 0 < |z - c| := abs_pos.mpr (sub_ne_zero.mpr hne)
        have := hz (|z - c| / 2) (by linarith)
        rcases le_total 0 (z - c) with h1 | h1
        · rw [abs_of_nonneg h1] at hpos this; linarith [this.2]
        · rw [abs_of_nonpos h1] at hpos this; linarith [this.1]
      · rintro rfl r hr
        constructor <;> linarith
    rw [hint', hc] at h
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [g, Function.comp_def, measureReal_def] using h2
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
  obtain ⟨r₀, hr₀, hr₀pos⟩ := (hev.and self_mem_nhdsWithin).exists
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr₀pos] with h hh
  have hh' : |h| < r₀ := by simpa [Real.dist_eq] using hh
  -- the integrand bound
  have hbound : ∀ z, ‖max (z - (c + h)) 0 - max (z - c) 0 + (Set.Ioi c).indicator (fun _ => h) z‖
      ≤ (Set.Icc (c - |h|) (c + |h|)).indicator (fun _ => 2 * |h|) z := by
    intro z
    rw [Real.norm_eq_abs]
    have hmm : |max (z - (c + h)) 0 - max (z - c) 0| ≤ |h| := by
      have := abs_max_sub_max_le_abs (z - (c + h)) (z - c) 0
      have e : z - (c + h) - (z - c) = -h := by ring
      rwa [e, abs_neg] at this
    by_cases hin : z ∈ Set.Icc (c - |h|) (c + |h|)
    · rw [Set.indicator_of_mem hin]
      have hi : |(Set.Ioi c).indicator (fun _ => h) z| ≤ |h| := by
        by_cases hz : z ∈ Set.Ioi c
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]; simp
      calc _ ≤ |max (z - (c + h)) 0 - max (z - c) 0| + |(Set.Ioi c).indicator (fun _ => h) z| :=
            abs_add_le _ _
        _ ≤ 2 * |h| := by linarith
    · rw [Set.indicator_of_notMem hin]
      simp only [Set.mem_Icc, not_and_or, not_le] at hin
      have hab := le_abs_self h
      have hab' := neg_abs_le h
      rcases hin with hz | hz
      · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; linarith),
          max_eq_right (by linarith), max_eq_right (by linarith)]
        simp
      · rw [Set.indicator_of_mem (by simp only [Set.mem_Ioi]; linarith),
          max_eq_left (by linarith), max_eq_left (by linarith)]
        simp only [abs_nonpos_iff]
        ring
  have hint1 := jd_Phi_integrable hint (c + h)
  have hint2 := jd_Phi_integrable hint c
  have hint3 : Integrable ((Set.Ioi c).indicator (fun _ => h)) μ :=
    (integrable_const h).indicator measurableSet_Ioi
  have hexpr : jd_Phi μ (c + h) - jd_Phi μ c - h • (-μ.real (Set.Ioi c)) =
      ∫ z, (max (z - (c + h)) 0 - max (z - c) 0 + (Set.Ioi c).indicator (fun _ => h) z) ∂μ := by
    have hsub : Integrable (fun z => max (z - (c + h)) 0 - max (z - c) 0) μ := hint1.sub hint2
    rw [integral_add hsub hint3, integral_sub hint1 hint2,
      integral_indicator_const _ measurableSet_Ioi]
    simp only [jd_Phi, smul_eq_mul]
    ring
  rw [hexpr]
  have hgle : g |h| ≤ g r₀ := gmono (abs_nonneg h) hr₀pos.le hh'.le
  have hgr : g r₀ < ε / 2 := hr₀
  calc ‖∫ z, (max (z - (c + h)) 0 - max (z - c) 0 + (Set.Ioi c).indicator (fun _ => h) z) ∂μ‖
      ≤ ∫ z, (Set.Icc (c - |h|) (c + |h|)).indicator (fun _ => 2 * |h|) z ∂μ :=
        norm_integral_le_of_norm_le ((integrable_const _).indicator measurableSet_Icc)
          (Eventually.of_forall hbound)
    _ = g |h| * (2 * |h|) := by
        rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
    _ ≤ ε / 2 * (2 * |h|) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ε * ‖h‖ := by rw [Real.norm_eq_abs]; ring

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Endogenous job destruction: the equilibrium conditions (Miao §18.2, pp. 600–603)

Miao, *Economic Dynamics in Discrete Time*, §18.2 (Mortensen–Pissarides 1994), pp. 600–603.
Matches draw an i.i.d. idiosyncratic productivity `z ∼ G` (a probability measure `μ`) each period;
exogenous separation has probability `ρˣ`; a filled job produces `A z`. All integrals over `z`
are set integrals over `(z*, ∞)` with respect to `μ`. Proved, as the text derives them:

* employment and unemployment dynamics (18.29) ⇒ (18.43) (`eq_18_43`); the total separation
  rate `ρ_t = ρˣ + (1 − ρˣ) G(z*_t)` (`jd_sepRate`, `jd_sepRate_mem`, `jd_sepRate_mono`);
* the Bellman equation for a filled job rewritten with the cutoff (`jd_filled_job_cutoff_form`);
* free entry in (18.30) ⇒ (18.31) (`eq_18_31`), (18.32) (`eq_18_32`), (18.33) (`eq_18_33`);
  the reservation productivity condition (18.34) (`eq_18_34`);
* Nash bargaining (18.37)–(18.38) (`eq_18_37_38`, via `jd_nash_iff`), the worker-surplus
  identity on p. 602 (`jd_worker_surplus`), the intermediate wage expression
  (`jd_wage_intermediate`) and the wage equation (18.39) (`eq_18_39`);
* the firm's value under the wage, (18.40) (`eq_18_40`), its linear form
  `J^F_t(z) = (1 − η) A (z − z*_t)` (`jd_JF_linear`) and the cutoff property (`jd_cutoff`);
* the job creation condition (18.41) (`eq_18_41`) and the job destruction condition (18.42)
  (`eq_18_42`);
* the job creation and destruction rates and their equality in a steady state
  (`jd_jcRate`, `jd_jdRate`, `jd_jc_eq_jd_of_steady`).

**Correction (timing in (18.41)–(18.42)).** The book writes `∫_{z*_t}^∞ (z_{t+1} − z*_t) dG` in
(18.41) and `∫_{z*_t}^∞ (z − z*_t) dG` in (18.42). Substituting `J^F_{t+1}(z) =
(1 − η) A (z − z*_{t+1})` into (18.31) gives the reservation productivity of period `t + 1`:
`κ / q(θ_t) = β (1 − η) A Φ(z*_{t+1})` and `η θ_t κ = (1 − η)(A z*_t − b) +
β (1 − ρˣ)(1 − η) A Φ(z*_{t+1})`, which is what `eq_18_41` and `eq_18_42` prove. The two
versions agree along constant paths, so the steady-state conditions (18.44)–(18.45) are
unaffected; the dynamics are in `JDSteadyState`.
-/

namespace Miao.SearchAndMatching

open MeasureTheory

/-- Miao, p. 600: the total separation rate `ρ_t = ρˣ + (1 − ρˣ) G(z*_t)`. -/
noncomputable def jd_sepRate (μ : Measure ℝ) (ρx zs : ℝ) : ℝ := ρx + (1 - ρx) * jd_G μ zs

/-- Miao, p. 600: `ρˣ ≤ ρ_t ≤ 1`. -/
theorem jd_sepRate_mem (μ : Measure ℝ) [IsProbabilityMeasure μ] {ρx : ℝ} (h1 : ρx ≤ 1)
    (zs : ℝ) : ρx ≤ jd_sepRate μ ρx zs ∧ jd_sepRate μ ρx zs ≤ 1 := by
  obtain ⟨g0, g1⟩ := jd_G_mem μ zs
  unfold jd_sepRate
  constructor <;> nlinarith

/-- Miao, p. 600: the separation rate is nondecreasing in the reservation productivity. -/
theorem jd_sepRate_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] {ρx : ℝ} (h1 : ρx ≤ 1) :
    Monotone (jd_sepRate μ ρx) := by
  intro c c' h
  unfold jd_sepRate
  have := jd_G_mono μ h
  nlinarith

/-- Miao, (18.29) and (18.43), p. 603: with `u_t = 1 − N_t` and `v_t = θ_t u_t`, the employment
dynamics `N_{t+1} = (1 − ρ_t) N_t + q(θ_t) v_t` are `u_{t+1} = (1 − ρ_t − q(θ_t) θ_t) u_t + ρ_t`. -/
theorem eq_18_43 {q : ℝ → ℝ} {θ ρ N u v : ℕ → ℝ}
    (h29 : ∀ t, N (t + 1) = (1 - ρ t) * N t + q (θ t) * v t) (hu : ∀ t, u t = 1 - N t)
    (hv : ∀ t, v t = θ t * u t) (t : ℕ) :
    u (t + 1) = (1 - ρ t - q (θ t) * θ t) * u t + ρ t := by
  rw [hu (t + 1), h29 t, hv t, hu t]
  ring

/-- Miao, p. 601: when `J ≤ V` below the cutoff `c` and `J ≥ V` above it, the continuation value
`∫ max(J(z), V) dG` equals `∫_c^∞ (J(z) − V) dG + V`. This rewrites the Bellman equation for a
filled job with the reservation productivity. -/
theorem jd_filled_job_cutoff_form {μ : Measure ℝ} [IsProbabilityMeasure μ] {J : ℝ → ℝ}
    {V c : ℝ} (hJ : Integrable J μ) (hlo : ∀ z, z ≤ c → J z ≤ V) (hhi : ∀ z, c < z → V ≤ J z) :
    ∫ z, max (J z) V ∂μ = (∫ z in Set.Ioi c, (J z - V) ∂μ) + V := by
  have hpt : (fun z => max (J z) V) = fun z => (Set.Ioi c).indicator (fun z => J z - V) z + V := by
    funext z
    by_cases hz : c < z
    · rw [Set.indicator_of_mem (by exact hz), max_eq_left (hhi z hz)]; ring
    · rw [Set.indicator_of_notMem (by exact hz), max_eq_right (hlo z (not_lt.mp hz))]; ring
  have hi : Integrable (fun z => (Set.Ioi c).indicator (fun z => J z - V) z) μ :=
    (hJ.sub (integrable_const V)).indicator measurableSet_Ioi
  rw [hpt, integral_add hi (integrable_const V), integral_indicator measurableSet_Ioi]
  simp

/-- Miao, (18.30)–(18.31), p. 601: free entry (`V_t = 0` for all `t`) in the vacancy value
equation gives `β ∫_{z*_{t+1}}^∞ J^F_{t+1}(z) dG = κ / q(θ_t)`. -/
theorem eq_18_31 {μ : Measure ℝ} {β κ : ℝ} {q : ℝ → ℝ} {θ zs V : ℕ → ℝ} {JF : ℕ → ℝ → ℝ}
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t)) (t : ℕ) :
    β * ∫ z in Set.Ioi (zs (t + 1)), JF (t + 1) z ∂μ = κ / q (θ t) := by
  have h := h30 t
  simp only [hfree, sub_zero, add_zero] at h
  have hq0 := (hq t).ne'
  field_simp
  linarith

/-- Miao, (18.32), p. 601: with free entry, the value of a filled job is
`J^F_t(z) = A z − w_t(z) + (1 − ρˣ) κ / q(θ_t)`. -/
theorem eq_18_32 {μ : Measure ℝ} {A β ρx κ : ℝ} {q : ℝ → ℝ} {θ zs V : ℕ → ℝ}
    {JF w : ℕ → ℝ → ℝ}
    (hJF : ∀ t z, JF t z = A * z - w t z + β * (1 - ρx) *
      ((∫ x in Set.Ioi (zs (t + 1)), (JF (t + 1) x - V (t + 1)) ∂μ) + V (t + 1)))
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t)) (t : ℕ) (z : ℝ) :
    JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t) := by
  have h31 := eq_18_31 h30 hfree hq t
  have h := hJF t z
  simp only [hfree, sub_zero, add_zero] at h
  have e : (1 - ρx) * κ / q (θ t) = (1 - ρx) * (κ / q (θ t)) := by ring
  rw [h, e, ← h31]
  ring

/-- Miao, (18.33), p. 601: `κ / q(θ_t) = β ∫_{z*_{t+1}}^∞ (A z − w_{t+1}(z) + (1 − ρˣ) κ /
q(θ_{t+1})) dG(z)`. -/
theorem eq_18_33 {μ : Measure ℝ} {A β ρx κ : ℝ} {q : ℝ → ℝ} {θ zs V : ℕ → ℝ}
    {JF w : ℕ → ℝ → ℝ}
    (hJF : ∀ t z, JF t z = A * z - w t z + β * (1 - ρx) *
      ((∫ x in Set.Ioi (zs (t + 1)), (JF (t + 1) x - V (t + 1)) ∂μ) + V (t + 1)))
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t)) (t : ℕ) :
    κ / q (θ t) = β * ∫ z in Set.Ioi (zs (t + 1)),
      (A * z - w (t + 1) z + (1 - ρx) * κ / q (θ (t + 1))) ∂μ := by
  rw [← eq_18_31 h30 hfree hq t]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun z _ => eq_18_32 hJF h30 hfree hq (t + 1) z

/-- Miao, (18.34), p. 601: the reservation productivity solves `J^F_t(z*_t) = 0`, i.e.
`A z*_t − w_t(z*_t) + (1 − ρˣ) κ / q(θ_t) = 0`. -/
theorem eq_18_34 {μ : Measure ℝ} {A β ρx κ : ℝ} {q : ℝ → ℝ} {θ zs V : ℕ → ℝ}
    {JF w : ℕ → ℝ → ℝ}
    (hJF : ∀ t z, JF t z = A * z - w t z + β * (1 - ρx) *
      ((∫ x in Set.Ioi (zs (t + 1)), (JF (t + 1) x - V (t + 1)) ∂μ) + V (t + 1)))
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t)) (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) :
    A * zs t - w t (zs t) + (1 - ρx) * κ / q (θ t) = 0 := by
  rw [← eq_18_32 hJF h30 hfree hq t (zs t)]
  exact hres t

/-- Miao, (18.37)–(18.38), p. 602: Nash bargaining over `w_t(z)`. The worker's surplus is
`J^W_t(z) − J^U_t = w + a` and the firm's `J^F_t(z) = c − w`, where `a` and `c` collect terms
that do not depend on the current wage. A feasible wage maximises
`(J^W − J^U)^η (J^F)^(1−η)` iff `η S = J^W − J^U` and `(1 − η) S = J^F`, `S = J^F + J^W − J^U`. -/
theorem eq_18_37_38 {η a c w : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hW : 0 ≤ a + w)
    (hF : 0 ≤ c - w) :
    (∀ w', 0 ≤ a + w' → 0 ≤ c - w' →
      (a + w') ^ η * (c - w') ^ (1 - η) ≤ (a + w) ^ η * (c - w) ^ (1 - η)) ↔
      (η * ((c - w) + (a + w)) = a + w ∧ (1 - η) * ((c - w) + (a + w)) = c - w) := by
  have h := jd_nash_iff (lam := 1) hη0 hη1 one_pos (by simpa using hW) hF
  simp only [one_mul] at h
  rw [h]
  constructor
  · intro h1; constructor <;> linarith
  · intro h1; linarith [h1.1]

/-- Miao, p. 602: subtracting (18.36) from (18.35), the worker's surplus satisfies
`J^W_t(z) − J^U_t = w_t(z) − b + β (1 − ρˣ − q^u_t) ∫_{z*_{t+1}}^∞ (J^W_{t+1} − J^U_{t+1}) dG`. -/
theorem jd_worker_surplus {μ : Measure ℝ} {β ρx b : ℝ} {qu zs JU : ℕ → ℝ}
    {JW w : ℕ → ℝ → ℝ}
    (h35 : ∀ t z, JW t z = w t z + β * ((1 - ρx) *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (h36 : ∀ t, JU t = b + β * (qu t *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (t : ℕ) (z : ℝ) :
    JW t z - JU t = w t z - b + β * (1 - ρx - qu t) *
      ∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ := by
  rw [h35 t z, h36 t]
  ring

/-- Miao, (18.39), p. 602: the Nash-bargained wage `w_t(z) = η (A z + θ_t κ) + (1 − η) b`,
derived from the Bellman equations (18.35)–(18.36) with `q^u_t = q(θ_t) θ_t`, the sharing rule
(18.37)–(18.38) (in the form `(1 − η)(J^W − J^U) = η J^F`), (18.31) and (18.32). -/
theorem eq_18_39 {μ : Measure ℝ} {A β ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs V JU : ℕ → ℝ}
    {JF JW w : ℕ → ℝ → ℝ} (hβ : 0 < β) (hη1 : η < 1)
    (hJF : ∀ t z, JF t z = A * z - w t z + β * (1 - ρx) *
      ((∫ x in Set.Ioi (zs (t + 1)), (JF (t + 1) x - V (t + 1)) ∂μ) + V (t + 1)))
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t))
    (h35 : ∀ t z, JW t z = w t z + β * ((1 - ρx) *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (h36 : ∀ t, JU t = b + β * (q (θ t) * θ t *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (hnash : ∀ t z, (1 - η) * (JW t z - JU t) = η * JF t z) (t : ℕ) (z : ℝ) :
    w t z = η * (A * z + θ t * κ) + (1 - η) * b := by
  have h1η : (1 - η) ≠ 0 := by linarith
  have hq0 := (hq t).ne'
  have hβ0 := hβ.ne'
  set X := ∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ with hXdef
  have hX : X = η / (1 - η) * ∫ x in Set.Ioi (zs (t + 1)), JF (t + 1) x ∂μ := by
    rw [hXdef, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have := hnash (t + 1) x
    field_simp
    linarith
  have h31 := eq_18_31 h30 hfree hq t
  have hβX : β * X = η * κ / ((1 - η) * q (θ t)) := by
    rw [hX]
    have : β * (η / (1 - η) * ∫ x in Set.Ioi (zs (t + 1)), JF (t + 1) x ∂μ) =
        η / (1 - η) * (β * ∫ x in Set.Ioi (zs (t + 1)), JF (t + 1) x ∂μ) := by ring
    rw [this, h31]
    field_simp
  have hs := jd_worker_surplus (qu := fun t => q (θ t) * θ t) h35 h36 t z
  rw [← hXdef] at hs
  have h32 := eq_18_32 hJF h30 hfree hq t z
  have hn := hnash t z
  rw [hs, h32] at hn
  linear_combination (norm := (field_simp; ring)) hn - (1 - η) * (1 - ρx - q (θ t) * θ t) * hβX

/-- Miao, p. 602 (the intermediate wage expression): substituting (18.38) into the worker-surplus
identity, `w_t(z) = (1 − η) b + η (A z + (1 − ρˣ) κ / q(θ_t)) − η β (1 − ρˣ − q^u_t)
∫_{z*_{t+1}}^∞ (A z′ − w_{t+1}(z′) + (1 − ρˣ) κ / q(θ_{t+1})) dG(z′)`; with (18.33) this is the
wage equation (18.39). -/
theorem jd_wage_intermediate {μ : Measure ℝ} {A β ρx κ η b : ℝ} {q : ℝ → ℝ}
    {θ zs V JU : ℕ → ℝ} {JF JW w : ℕ → ℝ → ℝ} (hβ : 0 < β) (hη1 : η < 1)
    (hJF : ∀ t z, JF t z = A * z - w t z + β * (1 - ρx) *
      ((∫ x in Set.Ioi (zs (t + 1)), (JF (t + 1) x - V (t + 1)) ∂μ) + V (t + 1)))
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t))
    (h35 : ∀ t z, JW t z = w t z + β * ((1 - ρx) *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (h36 : ∀ t, JU t = b + β * (q (θ t) * θ t *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (hnash : ∀ t z, (1 - η) * (JW t z - JU t) = η * JF t z) (t : ℕ) (z : ℝ) :
    w t z = (1 - η) * b + η * (A * z + (1 - ρx) * κ / q (θ t)) -
      η * β * (1 - ρx - q (θ t) * θ t) * ∫ x in Set.Ioi (zs (t + 1)),
        (A * x - w (t + 1) x + (1 - ρx) * κ / q (θ (t + 1))) ∂μ := by
  have h39 := eq_18_39 hβ hη1 hJF h30 hfree hq h35 h36 hnash t z
  have h33 := eq_18_33 hJF h30 hfree hq t
  have hq0 := (hq t).ne'
  have hβ0 := hβ.ne'
  set I := ∫ x in Set.Ioi (zs (t + 1)), (A * x - w (t + 1) x + (1 - ρx) * κ / q (θ (t + 1))) ∂μ
  have hI : I = κ / (β * q (θ t)) := by
    field_simp; field_simp at h33; linarith
  rw [hI, h39]
  field_simp
  ring

/-- Miao, (18.40), p. 602: under the wage (18.39),
`J^F_t(z) = (1 − η)(A z − b) − η θ_t κ + (1 − ρˣ) κ / q(θ_t)`, and this vanishes at `z*_t`. -/
theorem eq_18_40 {A ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs : ℕ → ℝ} {JF w : ℕ → ℝ → ℝ}
    (h32 : ∀ t z, JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t))
    (h39 : ∀ t z, w t z = η * (A * z + θ t * κ) + (1 - η) * b)
    (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) :
    (∀ z, JF t z = (1 - η) * (A * z - b) - η * θ t * κ + (1 - ρx) * κ / q (θ t)) ∧
      0 = (1 - η) * (A * zs t - b) - η * θ t * κ + (1 - ρx) * κ / q (θ t) := by
  have hz : ∀ z, JF t z = (1 - η) * (A * z - b) - η * θ t * κ + (1 - ρx) * κ / q (θ t) := by
    intro z; rw [h32, h39]; ring
  exact ⟨hz, by rw [← hz, hres]⟩

/-- Miao, p. 603: taking the difference of the two equations in (18.40),
`J^F_t(z) = (1 − η) A (z − z*_t)`. -/
theorem jd_JF_linear {A ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs : ℕ → ℝ} {JF w : ℕ → ℝ → ℝ}
    (h32 : ∀ t z, JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t))
    (h39 : ∀ t z, w t z = η * (A * z + θ t * κ) + (1 - η) * b)
    (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) (z : ℝ) :
    JF t z = (1 - η) * A * (z - zs t) := by
  obtain ⟨h1, h2⟩ := eq_18_40 h32 h39 hres t
  rw [h1 z]
  linarith

/-- Miao, p. 600 ("clearly, there is a cutoff value"): with `A > 0` and `η < 1`, the firm keeps
the match iff `z > z*_t`: `J^F_t(z) ≤ 0 ↔ z ≤ z*_t`. -/
theorem jd_cutoff {A ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs : ℕ → ℝ} {JF w : ℕ → ℝ → ℝ}
    (hA : 0 < A) (hη1 : η < 1)
    (h32 : ∀ t z, JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t))
    (h39 : ∀ t z, w t z = η * (A * z + θ t * κ) + (1 - η) * b)
    (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) (z : ℝ) : JF t z ≤ 0 ↔ z ≤ zs t := by
  rw [jd_JF_linear h32 h39 hres t z]
  have hc : 0 < (1 - η) * A := mul_pos (by linarith) hA
  constructor
  · intro h
    by_contra hne
    have : 0 < (1 - η) * A * (z - zs t) := mul_pos hc (by linarith [not_le.mp hne])
    linarith
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith)

/-- Miao, (18.41), p. 603, with the timing corrected: the job creation condition
`κ / q(θ_t) = β (1 − η) A ∫_{z*_{t+1}}^∞ (z − z*_{t+1}) dG(z) = β (1 − η) A Φ(z*_{t+1})`. -/
theorem eq_18_41 {μ : Measure ℝ} {A β ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs : ℕ → ℝ}
    {JF w : ℕ → ℝ → ℝ}
    (h31 : ∀ t, β * ∫ z in Set.Ioi (zs (t + 1)), JF (t + 1) z ∂μ = κ / q (θ t))
    (h32 : ∀ t z, JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t))
    (h39 : ∀ t z, w t z = η * (A * z + θ t * κ) + (1 - η) * b)
    (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) :
    κ / q (θ t) = β * (1 - η) * A * ∫ z in Set.Ioi (zs (t + 1)), (z - zs (t + 1)) ∂μ ∧
      κ / q (θ t) = β * (1 - η) * A * jd_Phi μ (zs (t + 1)) := by
  have h : κ / q (θ t) = β * (1 - η) * A * ∫ z in Set.Ioi (zs (t + 1)), (z - zs (t + 1)) ∂μ := by
    have e : ∫ z in Set.Ioi (zs (t + 1)), JF (t + 1) z ∂μ =
        ∫ z in Set.Ioi (zs (t + 1)), (1 - η) * A * (z - zs (t + 1)) ∂μ :=
      setIntegral_congr_fun measurableSet_Ioi fun z _ => jd_JF_linear h32 h39 hres (t + 1) z
    rw [← h31 t, e, integral_const_mul]
    ring
  exact ⟨h, by rw [h, jd_Phi_eq_setIntegral]⟩

/-- Miao, (18.42), p. 603, with the timing corrected: the job destruction condition
`η θ_t κ = (1 − η)(A z*_t − b) + β (1 − ρˣ)(1 − η) A Φ(z*_{t+1})`. -/
theorem eq_18_42 {μ : Measure ℝ} {A β ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs : ℕ → ℝ}
    {JF w : ℕ → ℝ → ℝ}
    (h31 : ∀ t, β * ∫ z in Set.Ioi (zs (t + 1)), JF (t + 1) z ∂μ = κ / q (θ t))
    (h32 : ∀ t z, JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t))
    (h39 : ∀ t z, w t z = η * (A * z + θ t * κ) + (1 - η) * b)
    (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) :
    η * θ t * κ = (1 - η) * (A * zs t - b) +
      β * (1 - ρx) * (1 - η) * A * jd_Phi μ (zs (t + 1)) := by
  have h40 := (eq_18_40 h32 h39 hres t).2
  have h41 := (eq_18_41 h31 h32 h39 hres t).2
  have : (1 - ρx) * κ / q (θ t) = (1 - ρx) * (κ / q (θ t)) := by ring
  rw [this, h41] at h40
  linarith

/-- Miao, p. 603: the job destruction rate `jd_t = ρˣ + (1 − ρˣ) G(z*_t)`. -/
noncomputable def jd_jdRate (μ : Measure ℝ) (ρx zs : ℝ) : ℝ := jd_sepRate μ ρx zs

/-- Miao, p. 603: the job creation rate
`jc_t = M(u_t, v_t)/(1 − u_t) = q(θ_t) θ_t u_t/(1 − u_t)`. -/
noncomputable def jd_jcRate (q : ℝ → ℝ) (θ u : ℝ) : ℝ := q θ * θ * u / (1 - u)

/-- Miao, (18.43), pp. 603–607: in a steady state of (18.43) with `u < 1`, the job creation rate
equals the job destruction rate, and `u = ρ / (ρ + q(θ) θ)`. -/
theorem jd_jc_eq_jd_of_steady {μ : Measure ℝ} {ρx zs θ u : ℝ} {q : ℝ → ℝ} (hu1 : u < 1)
    (hpos : 0 < jd_sepRate μ ρx zs + q θ * θ)
    (hss : u = (1 - jd_sepRate μ ρx zs - q θ * θ) * u + jd_sepRate μ ρx zs) :
    jd_jcRate q θ u = jd_jdRate μ ρx zs ∧
      u = jd_sepRate μ ρx zs / (jd_sepRate μ ρx zs + q θ * θ) := by
  have h1u : (1 - u) ≠ 0 := by linarith
  unfold jd_jcRate jd_jdRate
  constructor
  · field_simp
    linarith
  · field_simp
    linarith

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Endogenous job destruction: steady state, comparative statics, dynamics (Miao §18.2)

Miao, *Economic Dynamics in Discrete Time*, §18.2, pp. 604–607. With
`Φ(c) = ∫_c^∞ (z − c) dG` (`jd_Phi`), the steady-state job creation (JC) and job destruction (JD)
conditions are

  (18.44) `κ / q(θ) = β (1 − η) A Φ(z*)`  (`jd_JC`),
  (18.45) `η θ κ = (1 − η)(A z* − b) + β (1 − ρˣ)(1 − η) A Φ(z*)`  (`jd_JD`).

Proved:

* JC slopes down (`eq_18_44`), JD slopes up (`eq_18_45`) in the `(θ, z*)` plane;
* **existence and uniqueness** of the steady state `(θ*, z̄*)` with `θ* > 0`
  (`jd_steady_state_unique`, `jd_steady_state_exists`, `jd_steady_state_existsUnique`) when `q`
  is positive, continuous and strictly decreasing on `(0, ∞)` with `q(θ) → ∞` as `θ ↓ 0`, and
  `G(b/A) < 1` (some matches are worth more than unemployment benefits); a concrete instance
  (Cobb–Douglas `q`, degenerate `G`) is `jd_example_steady_state`;
* the Beveridge curve with `ρ = ρˣ + (1 − ρˣ) G(z̄*)`: steady-state unemployment
  `u = ρ / (ρ + q(θ) θ)` (`jd_jc_eq_jd_of_steady`), the curve slopes down
  (`jd_beveridge_downward`) and shifts down when `ρ` falls (`jd_beveridge_shift`);
* comparative statics in `A`: with fixed `κ`, tightness rises (`jd_compstat_A_theta`; the book
  says the effect on `z*` is ambiguous, not formalised); with posting cost `κ A`, `A` cancels from
  JC (`jd_JC_kappaA_iff`), the reservation productivity falls and tightness rises
  (`jd_compstat_kappaA`), the job destruction rate does not rise (`jd_compstat_kappaA_jd`), and
  unemployment and the steady-state job creation rate fall (`jd_compstat_kappaA_u`);
* transitional dynamics: the linearised JC/JD system reduces to `dz_t = ψ dz_{t+1}` with
  `ψ = β (1 − G(z̄*)) ((1 − ρˣ) − η q(θ*) θ* / ξ(θ*))` (`jd_linear_psi`); when `|ψ| < 1` (in
  particular under the analogue of the §18.1 condition `1 − ρˣ − η q θ / ξ ≥ 0`,
  `jd_psi_abs_lt_one`) the only bounded solution has `dz ≡ dθ ≡ 0` and unemployment converges
  (`jd_saddle`), the saddle-point property; after a permanent rise in `A` unemployment falls
  monotonically and the job creation rate falls to the constant job destruction rate
  (`jd_transition_unemployment`). The slopes used are `Φ′ = −(1 − G)` (`jd_Phi_hasDerivAt`) and
  `(κ/q)′ = −κ q′/q²` (`jd_kappa_div_q_hasDerivAt`).

**Departure.** The book's claim that `z*` and `θ` are "constant over time" reads off its printed
(18.41)–(18.42), whose integrals start at `z*_t`; with the correct timing (`eq_18_41`,
`eq_18_42`) constancy is the saddle-path selection proved in `jd_saddle` (linearised).
-/

namespace Miao.SearchAndMatching

open MeasureTheory Filter Topology

/-- Miao, (18.44), p. 604: the steady-state job creation condition
`κ / q(θ) = β (1 − η) A Φ(z*)`. -/
def jd_JC (μ : Measure ℝ) (q : ℝ → ℝ) (β η κ A θ c : ℝ) : Prop :=
  κ / q θ = β * (1 - η) * A * jd_Phi μ c

/-- Miao, (18.45), p. 604: the steady-state job destruction condition
`η θ κ = (1 − η)(A z* − b) + β (1 − ρˣ)(1 − η) A Φ(z*)`. -/
def jd_JD (μ : Measure ℝ) (β ρx η κ A b θ c : ℝ) : Prop :=
  η * θ * κ = (1 - η) * (A * c - b) + β * (1 - ρx) * (1 - η) * A * jd_Phi μ c

/-- The JD curve as a function of `z*`: `θ_JD(c) = [(1 − η)(A c − b) + β(1 − ρˣ)(1 − η) A Φ(c)]
/ (η κ)`. -/
noncomputable def jd_thetaJD (μ : Measure ℝ) (β ρx η κ A b c : ℝ) : ℝ :=
  ((1 - η) * (A * c - b) + β * (1 - ρx) * (1 - η) * A * jd_Phi μ c) / (η * κ)

/-- `c ↦ c + β(1 − ρˣ) Φ(c)` is strictly increasing when `0 ≤ β(1 − ρˣ) < 1`. -/
theorem jd_h_strictMono {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    StrictMono fun c => c + k * jd_Phi μ c := by
  intro c c' h
  have h1 := jd_Phi_sub_le hint h.le
  simp only
  nlinarith

/-- Miao, (18.45), p. 604: `JD(θ, c) ↔ θ = θ_JD(c)`. -/
theorem jd_JD_iff {μ : Measure ℝ} {β ρx η κ A b θ c : ℝ} (hη : 0 < η) (hκ : 0 < κ) :
    jd_JD μ β ρx η κ A b θ c ↔ θ = jd_thetaJD μ β ρx η κ A b c := by
  unfold jd_JD jd_thetaJD
  rw [eq_div_iff (mul_pos hη hκ).ne']
  constructor <;> intro h <;> linarith

/-- Miao, p. 604: `θ_JD` is strictly increasing in `z*` (the JD curve slopes up). -/
theorem jd_thetaJD_strictMono {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {β ρx η κ A b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hA : 0 < A) :
    StrictMono (jd_thetaJD μ β ρx η κ A b) := by
  intro c c' h
  have hk0 : 0 ≤ β * (1 - ρx) := mul_nonneg hβ0.le (by linarith)
  have hk1 : β * (1 - ρx) < 1 := by nlinarith
  have hh := jd_h_strictMono hint hk0 hk1 h
  simp only at hh
  unfold jd_thetaJD
  apply div_lt_div_of_pos_right _ (mul_pos hη0 hκ)
  have hc : 0 < (1 - η) * A := mul_pos (by linarith) hA
  have : (1 - η) * (A * c - b) + β * (1 - ρx) * (1 - η) * A * jd_Phi μ c
      = (1 - η) * A * (c + β * (1 - ρx) * jd_Phi μ c) - (1 - η) * b := by ring
  have h' : (1 - η) * (A * c' - b) + β * (1 - ρx) * (1 - η) * A * jd_Phi μ c'
      = (1 - η) * A * (c' + β * (1 - ρx) * jd_Phi μ c') - (1 - η) * b := by ring
  rw [this, h']
  nlinarith

/-- `θ_JD` is continuous. -/
theorem jd_thetaJD_continuous {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) (β ρx η κ A b : ℝ) :
    Continuous (jd_thetaJD μ β ρx η κ A b) := by
  unfold jd_thetaJD
  have := jd_Phi_continuous hint
  fun_prop

/-- **The job creation curve slopes down** (Miao, (18.44), p. 604). If `(θ₁, c₁)` and
`(θ₂, c₂)` satisfy (18.44) with `θᵢ > 0` and `c₁ < c₂`, then `θ₂ < θ₁`. -/
theorem eq_18_44 {μ : Measure ℝ} [IsProbabilityMeasure μ] (hint : Integrable (fun z => z) μ)
    {q : ℝ → ℝ} {β η κ A θ₁ θ₂ c₁ c₂ : ℝ} (hβ : 0 < β) (hη1 : η < 1) (hκ : 0 < κ) (hA : 0 < A)
    (hqpos : ∀ θ, 0 < θ → 0 < q θ) (hqanti : StrictAntiOn q (Set.Ioi 0))
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (h₁ : jd_JC μ q β η κ A θ₁ c₁) (h₂ : jd_JC μ q β η κ A θ₂ c₂)
    (hc : c₁ < c₂) : θ₂ < θ₁ := by
  unfold jd_JC at h₁ h₂
  have hK : 0 < β * (1 - η) * A := mul_pos (mul_pos hβ (by linarith)) hA
  have hq₁ := hqpos θ₁ hθ₁
  have hq₂ := hqpos θ₂ hθ₂
  have hPhi₁ : 0 < jd_Phi μ c₁ := by
    have : 0 < κ / q θ₁ := div_pos hκ hq₁
    rw [h₁] at this
    exact pos_of_mul_pos_right this hK.le
  have hlt : jd_Phi μ c₂ < jd_Phi μ c₁ := jd_Phi_strictAnti_of_pos hint hc hPhi₁
  have : κ / q θ₂ < κ / q θ₁ := by rw [h₁, h₂]; exact mul_lt_mul_of_pos_left hlt hK
  rw [div_lt_div_iff_of_pos_left hκ hq₂ hq₁] at this
  by_contra hne
  rcases (not_lt.mp hne).lt_or_eq with h | h
  · have := hqanti (Set.mem_Ioi.mpr hθ₁) (Set.mem_Ioi.mpr hθ₂) h; linarith
  · rw [h] at this; linarith

/-- **The job destruction curve slopes up** (Miao, (18.45), p. 604). If `(θ₁, c₁)` and
`(θ₂, c₂)` satisfy (18.45) and `c₁ < c₂`, then `θ₁ < θ₂`. -/
theorem eq_18_45 {μ : Measure ℝ} [IsProbabilityMeasure μ] (hint : Integrable (fun z => z) μ)
    {β ρx η κ A b θ₁ θ₂ c₁ c₂ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1)
    (hη0 : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hA : 0 < A)
    (h₁ : jd_JD μ β ρx η κ A b θ₁ c₁) (h₂ : jd_JD μ β ρx η κ A b θ₂ c₂) (hc : c₁ < c₂) :
    θ₁ < θ₂ := by
  rw [jd_JD_iff hη0 hκ] at h₁ h₂
  rw [h₁, h₂]
  exact jd_thetaJD_strictMono hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hc

/-- **Uniqueness of the steady state** (Miao, p. 604, Figure 18.5): the JC and JD curves cross at
most once in `θ > 0`. -/
theorem jd_steady_state_unique {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ} {β ρx η κ A b θ₁ θ₂ c₁ c₂ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hC₁ : jd_JC μ q β η κ A θ₁ c₁) (hD₁ : jd_JD μ β ρx η κ A b θ₁ c₁)
    (hC₂ : jd_JC μ q β η κ A θ₂ c₂) (hD₂ : jd_JD μ β ρx η κ A b θ₂ c₂) :
    θ₁ = θ₂ ∧ c₁ = c₂ := by
  have hc : c₁ = c₂ := by
    rcases lt_trichotomy c₁ c₂ with h | h | h
    · have := eq_18_44 hint hβ0 hη1 hκ hA hqpos hqanti hθ₁ hθ₂ hC₁ hC₂ h
      have := eq_18_45 hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hD₁ hD₂ h
      linarith
    · exact h
    · have := eq_18_44 hint hβ0 hη1 hκ hA hqpos hqanti hθ₂ hθ₁ hC₂ hC₁ h
      have := eq_18_45 hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hD₂ hD₁ h
      linarith
  refine ⟨?_, hc⟩
  rw [jd_JD_iff hη0 hκ] at hD₁ hD₂
  rw [hD₁, hD₂, hc]

/-- **Existence of the steady state** (Miao, p. 604, Figure 18.5). If `q` is positive, continuous
and strictly decreasing on `(0, ∞)` with `q(θ) → ∞` as `θ ↓ 0`, and `G(b/A) < 1`, then the JC
and JD curves cross at some `(θ*, z̄*)` with `θ* > 0`. -/
theorem jd_steady_state_exists {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ} {β ρx η κ A b : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hqcont : ContinuousOn q (Set.Ioi 0))
    (hq0 : Tendsto q (𝓝[>] 0) atTop) (hG : 0 < μ (Set.Ioi (b / A))) :
    ∃ θ c, 0 < θ ∧ jd_JC μ q β η κ A θ c ∧ jd_JD μ β ρx η κ A b θ c := by
  set T := jd_thetaJD μ β ρx η κ A b with hT
  have hTmono : StrictMono T := jd_thetaJD_strictMono hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA
  have hTcont : Continuous T := jd_thetaJD_continuous hint β ρx η κ A b
  have hPcont := jd_Phi_continuous hint (μ := μ)
  have hK : 0 < β * (1 - η) * A := mul_pos (mul_pos hβ0 (by linarith)) hA
  have hηκ : 0 < η * κ := mul_pos hη0 hκ
  set F : ℝ → ℝ := fun c => κ / q (T c) - β * (1 - η) * A * jd_Phi μ c with hF
  -- Step 1: at `c₁ = b / A` the JD curve is above zero
  set c₁ := b / A with hc₁
  have hP₁ : 0 < jd_Phi μ c₁ := (jd_Phi_pos_iff hint c₁).mpr hG
  have hT₁ : 0 < T c₁ := by
    rw [hT]; unfold jd_thetaJD
    have : A * c₁ - b = 0 := by rw [hc₁]; field_simp; ring
    rw [this]
    apply div_pos _ hηκ
    have : 0 < β * (1 - ρx) * (1 - η) * A :=
      mul_pos (mul_pos (mul_pos hβ0 (by linarith)) (by linarith)) hA
    nlinarith
  -- Step 2: a `c₂ ≥ c₁` with `F c₂ > 0`
  have hm : 0 < κ / q (T c₁) := div_pos hκ (hqpos _ hT₁)
  have hlow : ∀ c, c₁ ≤ c → κ / q (T c₁) ≤ κ / q (T c) := by
    intro c hc
    have hTc : T c₁ ≤ T c := hTmono.monotone hc
    have hTc0 : 0 < T c := lt_of_lt_of_le hT₁ hTc
    have hqle : q (T c) ≤ q (T c₁) := hqanti.antitoneOn (Set.mem_Ioi.mpr hT₁)
      (Set.mem_Ioi.mpr hTc0) hTc
    exact div_le_div_of_nonneg_left hκ.le (hqpos _ hTc0) hqle
  have hev : ∀ᶠ c in atTop, β * (1 - η) * A * jd_Phi μ c < κ / q (T c₁) := by
    have := ((jd_Phi_tendsto_atTop hint).const_mul (β * (1 - η) * A))
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hm)
  obtain ⟨c₂, hc₂F, hc₂⟩ := (hev.and (eventually_ge_atTop c₁)).exists
  have hF₂ : 0 < F c₂ := by
    simp only [hF]; linarith [hlow c₂ hc₂]
  -- Step 3: the zero `c₀` of the JD curve
  set k := β * (1 - ρx) with hk
  have hk0 : 0 ≤ k := mul_nonneg hβ0.le (by linarith)
  have hk1 : k < 1 := by rw [hk]; nlinarith
  set cn := min 0 ((b - k * A * jd_Phi μ 0 - 1) / (A * (1 - k))) with hcn
  have hAk : 0 < A * (1 - k) := mul_pos hA (by linarith)
  have hTn : T cn < 0 := by
    rw [hT]; unfold jd_thetaJD
    apply div_neg_of_neg_of_pos _ hηκ
    have hcn0 : cn ≤ 0 := min_le_left _ _
    have hcn1 : A * (1 - k) * cn ≤ b - k * A * jd_Phi μ 0 - 1 := by
      have := min_le_right 0 ((b - k * A * jd_Phi μ 0 - 1) / (A * (1 - k)))
      rw [← hcn] at this
      calc A * (1 - k) * cn ≤ A * (1 - k) * ((b - k * A * jd_Phi μ 0 - 1) / (A * (1 - k))) :=
            mul_le_mul_of_nonneg_left this hAk.le
        _ = b - k * A * jd_Phi μ 0 - 1 := mul_div_cancel₀ _ hAk.ne'
    have hP := jd_Phi_sub_le hint hcn0
    have : β * (1 - ρx) * (1 - η) * A * jd_Phi μ cn = (1 - η) * (k * A * jd_Phi μ cn) := by
      rw [hk]; ring
    rw [this]
    have hkA : 0 ≤ k * A := mul_nonneg hk0 hA.le
    have : k * A * jd_Phi μ cn ≤ k * A * (jd_Phi μ 0 - cn) :=
      mul_le_mul_of_nonneg_left (by linarith) hkA
    have h1η : 0 < 1 - η := by linarith
    nlinarith
  have hcn₁ : cn ≤ c₁ := by
    by_contra h
    have := hTmono.monotone (not_le.mp h).le
    linarith
  obtain ⟨c₀, ⟨hc₀l, hc₀r⟩, hT₀⟩ : ∃ c₀ ∈ Set.Icc cn c₁, T c₀ = 0 :=
    intermediate_value_Icc hcn₁ hTcont.continuousOn ⟨hTn.le, hT₁.le⟩
  have hc₀₁ : c₀ < c₁ := by
    rcases hc₀r.lt_or_eq with h | h
    · exact h
    · rw [h] at hT₀; linarith
  have hP₀ : 0 < jd_Phi μ c₀ := lt_of_lt_of_le hP₁ (jd_Phi_antitone hint hc₀₁.le)
  -- Step 4: just above `c₀`, `F < 0`
  have hTlim : Tendsto T (𝓝[>] c₀) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := (hTcont.tendsto c₀).mono_left (nhdsWithin_le_nhds (s := Set.Ioi c₀))
      rwa [hT₀] at this
    · filter_upwards [self_mem_nhdsWithin] with c hc
      rw [Set.mem_Ioi, ← hT₀]
      exact hTmono hc
  have hFlim : Tendsto F (𝓝[>] c₀) (𝓝 (0 - β * (1 - η) * A * jd_Phi μ c₀)) := by
    refine Tendsto.sub ?_ ?_
    · exact tendsto_const_nhds.div_atTop (hq0.comp hTlim)
    · exact ((hPcont.tendsto c₀).mono_left nhdsWithin_le_nhds).const_mul _
  have hneg : 0 - β * (1 - η) * A * jd_Phi μ c₀ < 0 := by
    have := mul_pos hK hP₀; linarith
  have hev2 := hFlim.eventually (gt_mem_nhds hneg)
  have hc₀₂ : c₀ < c₂ := lt_of_lt_of_le hc₀₁ hc₂
  obtain ⟨cl, hclF, hcl⟩ := (hev2.and (Ioo_mem_nhdsGT hc₀₂)).exists
  -- Step 5: intermediate value theorem on `[cl, c₂]`
  have hpos : ∀ c ∈ Set.Icc cl c₂, 0 < T c := by
    intro c hc
    rw [← hT₀]
    exact hTmono (lt_of_lt_of_le hcl.1 hc.1)
  have hFcont : ContinuousOn F (Set.Icc cl c₂) := by
    simp only [hF]
    refine ContinuousOn.sub ?_ (continuous_const.mul hPcont).continuousOn
    refine continuousOn_const.div (hqcont.comp hTcont.continuousOn fun c hc => hpos c hc) ?_
    intro c hc
    exact (hqpos _ (hpos c hc)).ne'
  obtain ⟨cs, hcs, hFcs⟩ : ∃ cs ∈ Set.Icc cl c₂, F cs = 0 :=
    intermediate_value_Icc hcl.2.le hFcont ⟨hclF.le, hF₂.le⟩
  refine ⟨T cs, cs, hpos cs hcs, ?_, ?_⟩
  · unfold jd_JC
    simp only [hF] at hFcs
    linarith
  · rw [jd_JD_iff hη0 hκ]

/-- **Existence and uniqueness of the steady state** (Miao, p. 604, Figure 18.5): under the
hypotheses of `jd_steady_state_exists` there is exactly one `(θ*, z̄*)` with `θ* > 0` solving
(18.44)–(18.45). -/
theorem jd_steady_state_existsUnique {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ} {β ρx η κ A b : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hqcont : ContinuousOn q (Set.Ioi 0))
    (hq0 : Tendsto q (𝓝[>] 0) atTop) (hG : 0 < μ (Set.Ioi (b / A))) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ jd_JC μ q β η κ A p.1 p.2 ∧ jd_JD μ β ρx η κ A b p.1 p.2 := by
  obtain ⟨θ, c, h0, h1, h2⟩ :=
    jd_steady_state_exists hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hqpos hqanti hqcont hq0 hG
  refine ⟨(θ, c), ⟨h0, h1, h2⟩, ?_⟩
  rintro ⟨θ', c'⟩ ⟨h0', h1', h2'⟩
  obtain ⟨e1, e2⟩ := jd_steady_state_unique hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hqpos hqanti
    h0' h0 h1' h2' h1 h2
  exact Prod.ext e1 e2

/-- A concrete instance of `jd_steady_state_existsUnique` (non-vacuity): Cobb–Douglas
`q(θ) = θ^(−1/2)`, degenerate `G` at the mean `1`, `b < A`. -/
theorem jd_example_steady_state {β ρx η κ A b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hA : 0 < A)
    (hb : b < A) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ jd_JC (Measure.dirac 1) (fun θ => θ ^ (-(1 / 2 : ℝ))) β η κ A p.1 p.2
      ∧ jd_JD (Measure.dirac 1) β ρx η κ A b p.1 p.2 := by
  refine jd_steady_state_existsUnique (integrable_dirac (by simp)) hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA
    (fun θ hθ => Real.rpow_pos_of_pos hθ _) ?_ ?_ (tendsto_rpow_neg_nhdsGT_zero (by norm_num)) ?_
  · intro x hx y hy hxy
    exact Real.rpow_lt_rpow_of_neg hx hxy (by norm_num)
  · exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx))).continuousWithinAt
  · have : (1 : ℝ) ∈ Set.Ioi (b / A) := by
      rw [Set.mem_Ioi, div_lt_one hA]; exact hb
    simp [Measure.dirac_apply' _ measurableSet_Ioi, this]

/-- Miao, p. 605: with the posting cost `κ A`, `A` cancels from the job creation condition:
`κ A / q(θ) = β (1 − η) A Φ(z*) ↔ κ / q(θ) = β (1 − η) Φ(z*)`. -/
theorem jd_JC_kappaA_iff {μ : Measure ℝ} {q : ℝ → ℝ} {β η κ A θ c : ℝ} (hA : 0 < A) :
    jd_JC μ q β η (κ * A) A θ c ↔ κ / q θ = β * (1 - η) * jd_Phi μ c := by
  unfold jd_JC
  have hA0 := hA.ne'
  constructor
  · intro h
    have : κ * A / q θ = κ / q θ * A := by ring
    rw [this] at h
    have h2 : κ / q θ * A = (β * (1 - η) * jd_Phi μ c) * A := by rw [h]; ring
    exact mul_right_cancel₀ hA0 h2
  · intro h
    have : κ * A / q θ = κ / q θ * A := by ring
    rw [this, h]; ring

/-- **Comparative statics in `A`, fixed `κ`** (Miao, pp. 604–605): a permanent rise in
productivity `A < A′` raises steady-state market tightness (for `b ≥ 0`). -/
theorem jd_compstat_A_theta {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ} {β ρx η κ A A' b θ θ' c c' : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hAA : A < A') (hb : 0 ≤ b) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hθ : 0 < θ) (hθ' : 0 < θ')
    (hC : jd_JC μ q β η κ A θ c) (hD : jd_JD μ β ρx η κ A b θ c)
    (hC' : jd_JC μ q β η κ A' θ' c') (hD' : jd_JD μ β ρx η κ A' b θ' c') : θ < θ' := by
  unfold jd_JC at hC hC'
  unfold jd_JD at hD hD'
  by_contra hne
  have hle : θ' ≤ θ := not_lt.mp hne
  have hq := hqpos θ hθ
  have hq' := hqpos θ' hθ'
  have hqq : q θ ≤ q θ' := hqanti.antitoneOn (Set.mem_Ioi.mpr hθ') (Set.mem_Ioi.mpr hθ) hle
  have h1 : κ / q θ' ≤ κ / q θ := div_le_div_of_nonneg_left hκ.le hq hqq
  have hb1 : 0 < β * (1 - η) := mul_pos hβ0 (by linarith)
  have hP : 0 < jd_Phi μ c := by
    have : 0 < κ / q θ := div_pos hκ hq
    rw [hC] at this
    exact pos_of_mul_pos_right this (mul_pos hb1 hA).le
  have h2 : A' * jd_Phi μ c' ≤ A * jd_Phi μ c := by
    rw [hC, hC'] at h1
    have : β * (1 - η) * (A' * jd_Phi μ c') ≤ β * (1 - η) * (A * jd_Phi μ c) := by linarith
    exact le_of_mul_le_mul_left this hb1
  have h3 : jd_Phi μ c' < jd_Phi μ c := by
    have : A * jd_Phi μ c < A' * jd_Phi μ c := mul_lt_mul_of_pos_right hAA hP
    have hA' : 0 < A' := by linarith
    by_contra h4
    have : A' * jd_Phi μ c ≤ A' * jd_Phi μ c' := mul_le_mul_of_nonneg_left (not_lt.mp h4) hA'.le
    linarith
  have hcc : c < c' := by
    by_contra h4
    have := jd_Phi_antitone hint (not_lt.mp h4)
    linarith
  have hk0 : 0 ≤ β * (1 - ρx) := mul_nonneg hβ0.le (by linarith)
  have hk1 : β * (1 - ρx) < 1 := by nlinarith
  have hh := jd_h_strictMono hint hk0 hk1 hcc
  simp only at hh
  set h₀ := c + β * (1 - ρx) * jd_Phi μ c
  set h₁ := c' + β * (1 - ρx) * jd_Phi μ c'
  have h1η : 0 < 1 - η := by linarith
  have eD : η * θ * κ = (1 - η) * (A * h₀ - b) := by rw [hD]; ring
  have eD' : η * θ' * κ = (1 - η) * (A' * h₁ - b) := by rw [hD']; ring
  have hpos : 0 < η * θ * κ := mul_pos (mul_pos hη0 hθ) hκ
  have hh0 : 0 < h₀ := by
    have : 0 < A * h₀ - b := by
      rw [eD] at hpos; exact pos_of_mul_pos_right hpos h1η.le
    by_contra h5
    have : A * h₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA.le (not_lt.mp h5)
    linarith
  have : A * h₀ < A' * h₁ := by nlinarith
  have : η * θ * κ < η * θ' * κ := by rw [eD, eD']; nlinarith
  have : θ < θ' := by
    have hηκ : 0 < η * κ := mul_pos hη0 hκ
    nlinarith
  linarith

/-- **Comparative statics in `A`, posting cost `κ A`** (Miao, pp. 605–607): for `b > 0` and
`A < A′`, the reservation productivity falls and market tightness rises. -/
theorem jd_compstat_kappaA {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ} {β ρx η κ A A' b θ θ' c c' : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hAA : A < A') (hb : 0 < b) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hθ : 0 < θ) (hθ' : 0 < θ')
    (hC : jd_JC μ q β η (κ * A) A θ c) (hD : jd_JD μ β ρx η (κ * A) A b θ c)
    (hC' : jd_JC μ q β η (κ * A') A' θ' c') (hD' : jd_JD μ β ρx η (κ * A') A' b θ' c') :
    c' < c ∧ θ < θ' := by
  have hA' : 0 < A' := by linarith
  rw [jd_JC_kappaA_iff hA] at hC
  rw [jd_JC_kappaA_iff hA'] at hC'
  unfold jd_JD at hD hD'
  have hq := hqpos θ hθ
  have hq' := hqpos θ' hθ'
  have hb1 : 0 < β * (1 - η) := mul_pos hβ0 (by linarith)
  have h1η : 0 < 1 - η := by linarith
  have hk0 : 0 ≤ β * (1 - ρx) := mul_nonneg hβ0.le (by linarith)
  have hk1 : β * (1 - ρx) < 1 := by nlinarith
  -- JD divided by `A`
  have eD : η * θ * κ = (1 - η) * ((c + β * (1 - ρx) * jd_Phi μ c) - b / A) := by
    field_simp; linarith
  have eD' : η * θ' * κ = (1 - η) * ((c' + β * (1 - ρx) * jd_Phi μ c') - b / A') := by
    field_simp; linarith
  have hbA : b / A' < b / A := div_lt_div_of_pos_left hb hA hAA
  have hcc : c' < c := by
    by_contra h
    have hle : c ≤ c' := not_lt.mp h
    have hP := jd_Phi_antitone hint hle
    have h1 : κ / q θ' ≤ κ / q θ := by rw [hC, hC']; exact mul_le_mul_of_nonneg_left hP hb1.le
    have hqq : q θ ≤ q θ' := by
      rw [div_le_div_iff_of_pos_left hκ hq' hq] at h1; exact h1
    have hθθ : θ' ≤ θ := by
      by_contra h2
      have := hqanti (Set.mem_Ioi.mpr hθ) (Set.mem_Ioi.mpr hθ') (not_le.mp h2)
      linarith
    have hh := (jd_h_strictMono hint hk0 hk1).monotone hle
    beta_reduce at hh
    have : η * θ' * κ ≤ η * θ * κ := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθθ hη0.le) hκ.le
      linarith
    rw [eD, eD'] at this
    have := le_of_mul_le_mul_left this h1η
    linarith
  refine ⟨hcc, ?_⟩
  have hP : 0 < jd_Phi μ c := by
    have : 0 < κ / q θ := div_pos hκ hq
    rw [hC] at this
    exact pos_of_mul_pos_right this hb1.le
  have hm := (jd_Phi_pos_iff_real hint c).mp hP
  have hgap := jd_Phi_gap hint hcc.le
  have hlt : jd_Phi μ c < jd_Phi μ c' := by nlinarith
  have h1 : κ / q θ < κ / q θ' := by rw [hC, hC']; exact mul_lt_mul_of_pos_left hlt hb1
  rw [div_lt_div_iff_of_pos_left hκ hq hq'] at h1
  by_contra h2
  rcases (not_lt.mp h2).lt_or_eq with h3 | h3
  · have := hqanti (Set.mem_Ioi.mpr hθ') (Set.mem_Ioi.mpr hθ) h3; linarith
  · rw [h3] at h1; linarith

/-- Miao, p. 606: with posting cost `κ A`, a rise in `A` does not raise the job destruction rate
`ρˣ + (1 − ρˣ) G(z̄*)` (it falls weakly, strictly if `G` puts mass on `(z̄*′, z̄*]`). -/
theorem jd_compstat_kappaA_jd {μ : Measure ℝ} [IsProbabilityMeasure μ] {ρx c c' : ℝ}
    (hρ1 : ρx ≤ 1) (hcc : c' < c) : jd_jdRate μ ρx c' ≤ jd_jdRate μ ρx c :=
  jd_sepRate_mono μ hρ1 hcc.le

/-- Miao, p. 607: steady-state unemployment `u = ρ / (ρ + f)` falls when the separation rate
does not rise and the job-finding rate `f = q(θ) θ` rises: `ρ′ ≤ ρ`, `f < f′` ⇒ `u′ < u`. -/
theorem jd_compstat_kappaA_u {ρ ρ' f f' : ℝ} (hρ : 0 < ρ) (hρ' : 0 ≤ ρ') (hρρ : ρ' ≤ ρ)
    (hf : 0 ≤ f) (hff : f < f') : ρ' / (ρ' + f') < ρ / (ρ + f) := by
  have hf' : 0 < f' := lt_of_le_of_lt hf hff
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Miao, p. 604 ("it is downward sloping"): if the matching function `M` is nondecreasing in
`u` and in `v`, two points `(u₁, v₁)`, `(u₂, v₂)` of the Beveridge curve `ρ (1 − u) = M(u, v)`
with `ρ > 0` and `u₁ < u₂` have `v₂ < v₁`. (Convexity is the §18.1 claim and is not repeated.) -/
theorem jd_beveridge_downward {M : ℝ → ℝ → ℝ} {ρ u₁ u₂ v₁ v₂ : ℝ}
    (hMu : ∀ v, Monotone fun u => M u v) (hMv : ∀ u, Monotone (M u)) (hρ : 0 < ρ)
    (h₁ : ρ * (1 - u₁) = M u₁ v₁) (h₂ : ρ * (1 - u₂) = M u₂ v₂) (hu : u₁ < u₂) : v₂ < v₁ := by
  by_contra h
  have hv : v₁ ≤ v₂ := not_lt.mp h
  have e1 : M u₁ v₁ ≤ M u₁ v₂ := hMv u₁ hv
  have e2 : M u₁ v₂ ≤ M u₂ v₂ := hMu v₂ hu.le
  nlinarith

/-- Miao, p. 604 and Figure 18.6: the Beveridge curve `ρ (1 − u) = M(u, v) = v q(v/u)` shifts
down when the separation rate falls: at given `u ∈ (0, 1)`, if `θ ↦ θ q(θ)` is strictly
increasing on `(0, ∞)` and `ρ′ < ρ`, the vacancies on the new curve are lower. -/
theorem jd_beveridge_shift {q : ℝ → ℝ} {ρ ρ' u v v' : ℝ}
    (hf : StrictMonoOn (fun θ => θ * q θ) (Set.Ioi 0)) (hu0 : 0 < u) (hu1 : u < 1)
    (hv : 0 < v) (hv' : 0 < v') (hρρ : ρ' < ρ)
    (hBC : ρ * (1 - u) = v * q (v / u)) (hBC' : ρ' * (1 - u) = v' * q (v' / u)) : v' < v := by
  have e : ∀ x, x * q (x / u) = u * ((x / u) * q (x / u)) := by
    intro x; field_simp
  rw [e] at hBC hBC'
  have hlt : u * ((v' / u) * q (v' / u)) < u * ((v / u) * q (v / u)) := by
    rw [← hBC, ← hBC']; nlinarith
  have hlt' := lt_of_mul_lt_mul_left hlt hu0.le
  have : v' / u < v / u := by
    by_contra h
    have := hf.monotoneOn (Set.mem_Ioi.mpr (div_pos hv hu0)) (Set.mem_Ioi.mpr (div_pos hv' hu0))
      (not_lt.mp h)
    beta_reduce at this
    linarith
  exact (div_lt_div_iff_of_pos_right hu0).mp this

/-- **Transitional dynamics after a permanent rise in `A`** (Miao, p. 607). Tightness and the
reservation productivity jump to their new steady state; then `u_{t+1} = (1 − ρ − f) u_t + ρ`
with constant `ρ` and `f = q(θ) θ`. If `0 ≤ 1 − ρ − f`, `f > 0` and `u₀ ≥ ū = ρ/(ρ + f)`,
unemployment falls monotonically to `ū`, and the job creation rate `f u_t /(1 − u_t)` falls
monotonically to the constant job destruction rate `ρ`. -/
theorem jd_transition_unemployment {ρ f : ℝ} {u : ℕ → ℝ} (hρ : 0 ≤ ρ) (hf : 0 < f)
    (ha : 0 ≤ 1 - ρ - f) (hu : ∀ t, u (t + 1) = (1 - ρ - f) * u t + ρ)
    (h0 : ρ / (ρ + f) ≤ u 0) (h01 : u 0 < 1) :
    Antitone u ∧ Tendsto u atTop (𝓝 (ρ / (ρ + f))) ∧
      Antitone (fun t => f * u t / (1 - u t)) ∧ (∀ t, ρ ≤ f * u t / (1 - u t)) ∧
      Tendsto (fun t => f * u t / (1 - u t)) atTop (𝓝 ρ) := by
  have hpos : 0 < ρ + f := by linarith
  have e : ρ / (1 - (1 - ρ - f)) = ρ / (ρ + f) := by congr 1; ring
  have ha1 : 1 - ρ - f < 1 := by linarith
  have hu' : ∀ t, u (t + 1) = (1 - ρ - f) * u t + ρ := hu
  obtain ⟨hanti, hge⟩ := jd_affine_antitone ha ha1 hu' (by rw [e]; exact h0)
  rw [e] at hge
  have hlim : Tendsto u atTop (𝓝 (ρ / (ρ + f))) := by
    have := jd_affine_tendsto (abs_lt.mpr ⟨by linarith, ha1⟩) hu'
    rwa [e] at this
  have hlt1 : ∀ t, u t < 1 := fun t => lt_of_le_of_lt (hanti (Nat.zero_le t)) h01
  have hus1 : ρ / (ρ + f) < 1 := by rw [div_lt_one hpos]; linarith
  have hjc : ∀ t, ρ ≤ f * u t / (1 - u t) := by
    intro t
    have h1 : 0 < 1 - u t := by linarith [hlt1 t]
    rw [le_div_iff₀ h1]
    have := hge t
    rw [div_le_iff₀ hpos] at this
    nlinarith
  refine ⟨hanti, hlim, ?_, hjc, ?_⟩
  · intro s t hst
    have h1 : 0 < 1 - u t := by linarith [hlt1 t]
    have h2 : 0 < 1 - u s := by linarith [hlt1 s]
    have hus := hanti hst
    simp only
    rw [div_le_div_iff₀ h1 h2]
    nlinarith
  · have hcont : Tendsto (fun x => f * x / (1 - x)) (𝓝 (ρ / (ρ + f)))
        (𝓝 (f * (ρ / (ρ + f)) / (1 - ρ / (ρ + f)))) := by
      refine Tendsto.div (tendsto_const_nhds.mul tendsto_id) (tendsto_const_nhds.sub tendsto_id) ?_
      linarith
    have := hcont.comp hlim
    have e2 : f * (ρ / (ρ + f)) / (1 - ρ / (ρ + f)) = ρ := by
      field_simp
      ring_nf
      field_simp
    rw [e2] at this
    exact this

/-- Miao, p. 607 (linearising (18.41)): `θ ↦ κ / q(θ)` has derivative `−κ q′(θ)/q(θ)²`. -/
theorem jd_kappa_div_q_hasDerivAt {q : ℝ → ℝ} {κ θ q' : ℝ} (hq : HasDerivAt q q' θ)
    (hq0 : q θ ≠ 0) : HasDerivAt (fun x => κ / q x) (-(κ * q') / q θ ^ 2) θ := by
  have h := (hasDerivAt_const θ κ).div hq hq0
  have e : (fun x => κ / q x) = (fun _ => κ) / q := rfl
  rw [e]
  convert h using 1
  ring

/-- Miao, p. 607 (the linearised system): if `D = (κ/q)′(θ*) > 0` and `g = 1 − G(z̄*)`, the
linearised (18.41) `D dθ_t = −β (1 − η) A g dz_{t+1}` and (18.42)
`η κ dθ_t = (1 − η) A dz_t − β (1 − ρˣ)(1 − η) A g dz_{t+1}` give
`dz_t = ψ dz_{t+1}` with `ψ = β g ((1 − ρˣ) − η κ / D)`. With `D = κ ξ/(θ q)`, `ξ = −θ q′/q`,
this is `ψ = β g ((1 − ρˣ) − η q θ / ξ)`. -/
theorem jd_linear_psi {β ρx η κ A g D : ℝ} {dz dθ : ℕ → ℝ} (hη1 : η < 1) (hA : 0 < A)
    (hD : 0 < D)
    (hJC : ∀ t, D * dθ t = -(β * (1 - η) * A * g) * dz (t + 1))
    (hJD : ∀ t, η * κ * dθ t = (1 - η) * A * dz t - β * (1 - ρx) * (1 - η) * A * g * dz (t + 1))
    (t : ℕ) : dz t = β * g * ((1 - ρx) - η * κ / D) * dz (t + 1) := by
  have h1 := hJC t
  have h2 := hJD t
  have hD0 := hD.ne'
  have hc : (1 - η) * A ≠ 0 := (mul_pos (by linarith) hA).ne'
  have hθ : dθ t = -(β * (1 - η) * A * g) * dz (t + 1) / D := by
    field_simp; linarith
  rw [hθ] at h2
  apply mul_left_cancel₀ hc
  field_simp at h2 ⊢
  linarith

/-- Miao, p. 607: under the analogue of the §18.1 condition, `(1 − ρˣ) − η κ / D ≥ 0`, and
`0 ≤ g ≤ 1`, `0 < β < 1`, the coefficient satisfies `0 ≤ ψ < 1`. -/
theorem jd_psi_abs_lt_one {β ρx η κ g D : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx)
    (hη0 : 0 < η) (hκ : 0 < κ) (hD : 0 < D) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hcond : 0 ≤ (1 - ρx) - η * κ / D) : |β * g * ((1 - ρx) - η * κ / D)| < 1 := by
  have hpos : 0 < η * κ / D := div_pos (mul_pos hη0 hκ) hD
  have h1 : (1 - ρx) - η * κ / D < 1 := by linarith
  have h0 : 0 ≤ β * g * ((1 - ρx) - η * κ / D) := mul_nonneg (mul_nonneg hβ0.le hg0) hcond
  rw [abs_of_nonneg h0]
  have : β * g ≤ β := by nlinarith
  calc β * g * ((1 - ρx) - η * κ / D) ≤ β * ((1 - ρx) - η * κ / D) :=
        mul_le_mul_of_nonneg_right this hcond
    _ < 1 := by nlinarith

/-- **The steady state is a saddle point** (Miao, p. 607). In the linearised system
`dz_t = ψ dz_{t+1}` (`jd_linear_psi`), `D dθ_t = −β (1 − η) A g dz_{t+1}` and
`du_{t+1} = a dz_t + a' dθ_t + (1 − ρ − f) du_t` (from (18.43)), with `|ψ| < 1` and
`|1 − ρ − f| < 1`, every bounded solution has `dz_t = dθ_t = 0` for all `t` (the jump variables
sit at their steady state), and `du_t = (1 − ρ − f)ᵗ du₀ → 0`. -/
theorem jd_saddle {β η A g D ψ a a' ρ f : ℝ} {dz dθ du : ℕ → ℝ} (hD : 0 < D) (hψ : |ψ| < 1)
    (hr : |1 - ρ - f| < 1) (hz : ∀ t, dz t = ψ * dz (t + 1))
    (hJC : ∀ t, D * dθ t = -(β * (1 - η) * A * g) * dz (t + 1))
    (hu : ∀ t, du (t + 1) = a * dz t + a' * dθ t + (1 - ρ - f) * du t)
    (hbdd : ∃ M, ∀ t, |dz t| ≤ M) :
    (∀ t, dz t = 0) ∧ (∀ t, dθ t = 0) ∧ (∀ t, du t = (1 - ρ - f) ^ t * du 0) ∧
      Tendsto du atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hbdd
  have hz0 : ∀ t, dz t = 0 := by
    intro t
    have hpow : ∀ n, |dz t| ≤ |ψ| ^ n * M := by
      intro n
      induction n generalizing t with
      | zero => simpa using hM t
      | succ n ih =>
        have := ih (t + 1)
        rw [hz t, abs_mul, pow_succ]
        have h0 : 0 ≤ |ψ| := abs_nonneg ψ
        calc |ψ| * |dz (t + 1)| ≤ |ψ| * (|ψ| ^ n * M) := mul_le_mul_of_nonneg_left this h0
          _ = |ψ| ^ n * |ψ| * M := by ring
    have hlim : Tendsto (fun n : ℕ => |ψ| ^ n * M) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ψ) hψ).mul_const M
    have : |dz t| ≤ 0 := ge_of_tendsto' hlim hpow
    exact abs_nonpos_iff.mp this
  have hθ0 : ∀ t, dθ t = 0 := by
    intro t
    have := hJC t
    rw [hz0 (t + 1), mul_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hD.ne'
    · exact h
  have hu' : ∀ t, du (t + 1) = (1 - ρ - f) * du t + 0 := by
    intro t; rw [hu t, hz0 t, hθ0 t]; ring
  have hsol : ∀ t, du t = (1 - ρ - f) ^ t * du 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hu' n, ih, pow_succ]; ring
  refine ⟨hz0, hθ0, hsol, ?_⟩
  have := jd_affine_tendsto hr hu'
  simpa using this

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Unemployment and business cycles (Miao §18.3, pp. 607–614)

Miao, *Economic Dynamics in Discrete Time*, §18.3: the DMP model embedded in an RBC economy
(Merz 1995, Andolfatto 1996). The aggregate state follows a Markov chain; at a node the next
period's states `s` range over a finite type `S` with probabilities `p s`, so `E_t X_{t+1} =
∑ s, p s * X s`. Value functions are given functions whose maximising property is a hypothesis
("`V = max obj`": `obj ≤ V` everywhere with equality at the optimum); first-order and envelope
conditions are then proved from differentiability by `jd_foc` and `jd_envelope`.

**Households** (pp. 608–610; objective `jd_hhObj`, budget (18.46), capital (18.47), employment
(18.48) with `q^u = f` taken as given):
* the first-order condition for investment and the envelope condition for capital
  (`jd_hh_foc_I`, `jd_hh_envelope_K`) and the Euler equation (18.49) (`eq_18_49`);
* the envelope condition for employment (p. 609) (`jd_hh_envelope_N`) and the household surplus
  recursion (18.50) (`eq_18_50`);
* the marginal value `V_n(w, t) = Λ_t (w − w_t) + ∂V_t/∂N_t` of hiring one more member at wage
  `w` (`jd_hh_Vn`). **Correction**: this requires the new member to give up the benefit `b`; with
  the budget printed on p. 610 (`b (1 − N_t)`, benefit kept) the derivative is
  `Λ_t (w − w_t) + ∂V_t/∂N_t + Λ_t b` (`jd_hh_Vn_book_budget`), so the book's second equality
  fails when `b ≠ 0`. The first line of the book's display omits `−Λ_t b` correspondingly;
* the disutility microfoundation `∫₀^N χ j^φ dj = χ N^{1+φ}/(1+φ)` (`jd_disutility_integral`)
  and the derivatives of the CRRA utility and of the disutility (`jd_crra_hasDerivAt`,
  `jd_disutility_hasDerivAt`).

**Firms** (pp. 610–612; objective `jd_firmObj`, employment law (18.22)): (18.51) (`eq_18_51`),
(18.52) (`eq_18_52`), the envelope condition (18.53) (`eq_18_53`), the firm surplus (18.54)
(`eq_18_54`), the job creation condition (18.55) (`eq_18_55`), the marginal value
`J_n(w, t) = w_t − w + ∂J_t/∂N_t` (`jd_firm_Jn`); `K^j/N^j` is the same for all firms
(`jd_capital_ratio_indep`, from constant returns, `jd_partial_homog_one`).

**Nash bargaining** (pp. 612–613): `w_t` maximises `V_n^η J_n^(1−η)` at `w = w_t` iff
`(1 − η) S^H_t = η S^F_t` (`jd_nash_18_3`); the wage (18.56) (`eq_18_56`), the same for all
firms (`jd_wage_indep`).

**Equilibrium** (p. 614): aggregation `∫ F(K^j, A N^j) dj = F(K, A N)` (`jd_aggregate_output`,
finitely many firm types with masses `ω_j`), consistency of the firms' and households' employment
laws (`jd_employment_consistency`), and the resource constraint
`C_t + K_{t+1} − (1 − δ) K_t = F(K_t, A_t N_t) − κ v_t` (`jd_resource_constraint`).

The text derives no steady state, log-linearisation or simulation for this model; the steady
state used for calibration (Exercise 18.5) is in `JDExercises`.
-/

namespace Miao.SearchAndMatching

open Filter Topology

/-- Miao, (18.46)–(18.48), p. 609: the household's objective at a node, with consumption from
the budget `C = D + R K + w N + b (1 − N) − T − I` (written `R K + (w − b) N + (b + D − T) − I`),
next capital `(1 − δ) K + I` and next employment `(1 − ρ) N + f (1 − N) = (1 − ρ − f) N + f`. -/
noncomputable def jd_hhObj {S : Type*} [Fintype S] (u : ℝ → ℝ) (p : S → ℝ)
    (Vn : S → ℝ → ℝ → ℝ) (β δ χ φ ρ f R w b D T K N I : ℝ) : ℝ :=
  u (R * K + (w - b) * N + (b + D - T) - I) - χ * N ^ (1 + φ) / (1 + φ) +
    β * ∑ s, p s * Vn s ((1 - δ) * K + I) ((1 - ρ - f) * N + f)

/-- Miao, (18.46) and (18.48), p. 609: the two forms of the budget and employment law agree. -/
theorem jd_hh_budget_forms (R w b D T K N I ρ f : ℝ) :
    D + R * K + w * N + b * (1 - N) - T - I = R * K + (w - b) * N + (b + D - T) - I ∧
      (1 - ρ) * N + f * (1 - N) = (1 - ρ - f) * N + f := by
  constructor <;> ring

/-- Miao, p. 608: the CRRA utility `(C^{1−γ} − 1)/(1 − γ)` has marginal utility `Λ = C^{−γ}`. -/
theorem jd_crra_hasDerivAt {γ C : ℝ} (hγ : γ ≠ 1) (hC : 0 < C) :
    HasDerivAt (fun x => (x ^ (1 - γ) - 1) / (1 - γ)) (C ^ (-γ)) C := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hC.ne')).sub_const 1).div_const
    (1 - γ)
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  convert h using 1
  field_simp
  ring_nf

/-- Miao, p. 608: the disutility `χ N^{1+φ}/(1 + φ)` has derivative `χ N^φ` at `N > 0`. -/
theorem jd_disutility_hasDerivAt {χ φ N : ℝ} (hφ : 0 < φ) (hN : 0 < N) :
    HasDerivAt (fun x => χ * x ^ (1 + φ) / (1 + φ)) (χ * N ^ φ) N := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1 + φ) (Or.inl hN.ne')).const_mul χ).div_const
    (1 + φ)
  have h1 : (1 + φ) ≠ 0 := by linarith
  convert h using 1
  field_simp
  ring_nf

/-- Miao, p. 608 (microfoundation of the disutility of work): if member `j ∈ [0, N]` has
disutility `χ j^φ`, total disutility is `∫₀^N χ j^φ dj = χ N^{1+φ}/(1 + φ)`. -/
theorem jd_disutility_integral {χ φ N : ℝ} (hφ : 0 < φ) :
    ∫ j in (0 : ℝ)..N, χ * j ^ φ = χ * N ^ (1 + φ) / (1 + φ) := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  have h0 : (0 : ℝ) ^ (φ + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0, add_comm φ 1]
  ring

/-- Miao, p. 609: the first-order condition for investment, `Λ_t = β E_t ∂V_{t+1}/∂K_{t+1}`. -/
theorem jd_hh_foc_I {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {Vn : S → ℝ → ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} {β δ χ φ ρ f R w b D T K₀ N₀ I₀ Λ : ℝ} {VK : S → ℝ}
    (hmax : ∀ K N I, jd_hhObj u p Vn β δ χ φ ρ f R w b D T K N I ≤ V K N)
    (hopt : jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N₀ I₀ = V K₀ N₀)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVK : ∀ s, HasDerivAt (fun k => Vn s k ((1 - ρ - f) * N₀ + f)) (VK s) ((1 - δ) * K₀ + I₀)) :
    Λ = β * ∑ s, p s * VK s := by
  have hin : HasDerivAt (fun I => R * K₀ + (w - b) * N₀ + (b + D - T) - I) (-1) I₀ := by
    simpa using (hasDerivAt_id I₀).const_sub (R * K₀ + (w - b) * N₀ + (b + D - T))
  have hin2 : HasDerivAt (fun I => (1 - δ) * K₀ + I) 1 I₀ := by
    simpa using (hasDerivAt_id I₀).const_add ((1 - δ) * K₀)
  have hsum : HasDerivAt (fun I => ∑ s, p s * Vn s ((1 - δ) * K₀ + I) ((1 - ρ - f) * N₀ + f))
      (∑ s, p s * (VK s * 1)) I₀ :=
    HasDerivAt.fun_sum fun s _ => ((hVK s).comp_of_eq I₀ hin2 (by ring)).const_mul (p s)
  have hd := (((hu.comp I₀ hin).sub_const (χ * N₀ ^ (1 + φ) / (1 + φ))).add
    (hsum.const_mul β))
  have := jd_foc (h := fun I => jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N₀ I)
    (fun I => (hmax K₀ N₀ I).trans hopt.ge) hd
  simp only [mul_one, mul_neg] at this
  linarith

/-- Miao, p. 609: the envelope condition for capital,
`∂V_t/∂K_t = Λ_t (R_{kt} + 1 − δ)` (using the first-order condition for investment). -/
theorem jd_hh_envelope_K {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ}
    {Vn : S → ℝ → ℝ → ℝ} {V : ℝ → ℝ → ℝ} {β δ χ φ ρ f R w b D T K₀ N₀ I₀ Λ VK₀ : ℝ}
    {VK : S → ℝ}
    (hmax : ∀ K N I, jd_hhObj u p Vn β δ χ φ ρ f R w b D T K N I ≤ V K N)
    (hopt : jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N₀ I₀ = V K₀ N₀)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVK : ∀ s, HasDerivAt (fun k => Vn s k ((1 - ρ - f) * N₀ + f)) (VK s) ((1 - δ) * K₀ + I₀))
    (hV : HasDerivAt (fun k => V k N₀) VK₀ K₀) : VK₀ = Λ * (R + 1 - δ) := by
  have hfoc := jd_hh_foc_I hmax hopt hu hVK
  have hin : HasDerivAt (fun K => R * K + (w - b) * N₀ + (b + D - T) - I₀) R K₀ := by
    simpa using ((((hasDerivAt_id K₀).const_mul R).add_const ((w - b) * N₀)).add_const
      (b + D - T)).sub_const I₀
  have hin2 : HasDerivAt (fun K => (1 - δ) * K + I₀) (1 - δ) K₀ := by
    simpa using ((hasDerivAt_id K₀).const_mul (1 - δ)).add_const I₀
  have hsum : HasDerivAt (fun K => ∑ s, p s * Vn s ((1 - δ) * K + I₀) ((1 - ρ - f) * N₀ + f))
      (∑ s, p s * (VK s * (1 - δ))) K₀ :=
    HasDerivAt.fun_sum fun s _ => ((hVK s).comp_of_eq K₀ hin2 (by ring)).const_mul (p s)
  have hd := (((hu.comp K₀ hin).sub_const (χ * N₀ ^ (1 + φ) / (1 + φ))).add
    (hsum.const_mul β))
  have := jd_envelope (g := fun K => jd_hhObj u p Vn β δ χ φ ρ f R w b D T K N₀ I₀)
    (fun K => hmax K N₀ I₀) hopt hV hd
  rw [this]
  have e : ∑ s, p s * (VK s * (1 - δ)) = (1 - δ) * ∑ s, p s * VK s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  have : β * ((1 - δ) * ∑ s, p s * VK s) = (1 - δ) * Λ := by rw [hfoc]; ring
  linarith

/-- **The Euler equation** (Miao, (18.49), p. 609):
`Λ_t = β E_t [Λ_{t+1} (R_{k,t+1} + 1 − δ)]`, from the first-order condition for investment and
the envelope condition for capital at `t + 1` (`jd_hh_envelope_K` applied in each state). -/
theorem eq_18_49 {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {Vn : S → ℝ → ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} {β δ χ φ ρ f R w b D T K₀ N₀ I₀ Λ : ℝ} {VK Λn Rn : S → ℝ}
    (hmax : ∀ K N I, jd_hhObj u p Vn β δ χ φ ρ f R w b D T K N I ≤ V K N)
    (hopt : jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N₀ I₀ = V K₀ N₀)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVK : ∀ s, HasDerivAt (fun k => Vn s k ((1 - ρ - f) * N₀ + f)) (VK s) ((1 - δ) * K₀ + I₀))
    (henv : ∀ s, VK s = Λn s * (Rn s + 1 - δ)) :
    Λ = β * ∑ s, p s * (Λn s * (Rn s + 1 - δ)) := by
  rw [jd_hh_foc_I hmax hopt hu hVK]
  simp only [henv]

/-- Miao, p. 609: the envelope condition for employment,
`∂V_t/∂N_t = Λ_t (w_t − b) − χ N_t^φ + (1 − ρ − q(θ_t) θ_t) β E_t ∂V_{t+1}/∂N_{t+1}`. -/
theorem jd_hh_envelope_N {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ}
    {Vn : S → ℝ → ℝ → ℝ} {V : ℝ → ℝ → ℝ} {β δ χ φ ρ f R w b D T K₀ N₀ I₀ Λ VN₀ : ℝ}
    {VN : S → ℝ} (hφ : 0 < φ) (hN : 0 < N₀)
    (hmax : ∀ K N I, jd_hhObj u p Vn β δ χ φ ρ f R w b D T K N I ≤ V K N)
    (hopt : jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N₀ I₀ = V K₀ N₀)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVN : ∀ s, HasDerivAt (fun n => Vn s ((1 - δ) * K₀ + I₀) n) (VN s) ((1 - ρ - f) * N₀ + f))
    (hV : HasDerivAt (fun n => V K₀ n) VN₀ N₀) :
    VN₀ = Λ * (w - b) - χ * N₀ ^ φ + (1 - ρ - f) * (β * ∑ s, p s * VN s) := by
  have hin : HasDerivAt (fun N => R * K₀ + (w - b) * N + (b + D - T) - I₀) (w - b) N₀ := by
    simpa using ((((hasDerivAt_id N₀).const_mul (w - b)).const_add (R * K₀)).add_const
      (b + D - T)).sub_const I₀
  have hin2 : HasDerivAt (fun N => (1 - ρ - f) * N + f) (1 - ρ - f) N₀ := by
    simpa using ((hasDerivAt_id N₀).const_mul (1 - ρ - f)).add_const f
  have hsum : HasDerivAt (fun N => ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * N + f))
      (∑ s, p s * (VN s * (1 - ρ - f))) N₀ :=
    HasDerivAt.fun_sum fun s _ => ((hVN s).comp_of_eq N₀ hin2 (by ring)).const_mul (p s)
  have hd := (((hu.comp N₀ hin).sub (jd_disutility_hasDerivAt (χ := χ) hφ hN)).add
    (hsum.const_mul β))
  have := jd_envelope (g := fun N => jd_hhObj u p Vn β δ χ φ ρ f R w b D T K₀ N I₀)
    (fun N => hmax K₀ N I₀) hopt hV hd
  rw [this]
  have e : ∑ s, p s * (VN s * (1 - ρ - f)) = (1 - ρ - f) * ∑ s, p s * VN s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  ring

/-- Miao, (18.50), p. 609: with `S^H_t = (∂V_t/∂N_t)/Λ_t` and `∂V_{t+1}/∂N_{t+1} = Λ_{t+1}
S^H_{t+1}`, `S^H_t = w_t − b − χ N_t^φ/Λ_t + (1 − ρ − q(θ_t)θ_t) E_t[(β Λ_{t+1}/Λ_t) S^H_{t+1}]`. -/
theorem eq_18_50 {S : Type*} [Fintype S] {p : S → ℝ} {β χ φ ρ f w b N₀ Λ VN₀ : ℝ}
    {VN Λn SHn : S → ℝ} (hΛ : Λ ≠ 0)
    (henv : VN₀ = Λ * (w - b) - χ * N₀ ^ φ + (1 - ρ - f) * (β * ∑ s, p s * VN s))
    (hnext : ∀ s, VN s = Λn s * SHn s) :
    VN₀ / Λ = w - b - χ * N₀ ^ φ / Λ + (1 - ρ - f) * ∑ s, p s * (β * Λn s / Λ * SHn s) := by
  rw [henv]
  simp only [hnext]
  have e : ∑ s, p s * (β * Λn s / Λ * SHn s) = (β * ∑ s, p s * (Λn s * SHn s)) / Λ := by
    rw [Finset.mul_sum, Finset.sum_div]; congr 1; funext s; field_simp
  rw [e]
  field_simp

/-- Miao, p. 610 (corrected budget): if an additional member `ε` is hired at wage `w̃` and gives
up the benefit `b`, the marginal value is `V_n(w̃, t) = Λ_t (w̃ − w_t) + ∂V_t/∂N_t`. Here `Ṽ(ε)`
is the value with `N_t + ε` members (`Ṽ ≥` the objective at the optimal investment `I₀`, equality
at `ε = 0`) and `∂V_t/∂N_t` is given by `jd_hh_envelope_N`. -/
theorem jd_hh_Vn {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {Vn : S → ℝ → ℝ → ℝ}
    {Vt : ℝ → ℝ} {β δ χ φ ρ f R w w' b D T K₀ N₀ I₀ Λ VN₀ dV : ℝ} {VN : S → ℝ}
    (hφ : 0 < φ) (hN : 0 < N₀)
    (hle : ∀ ε, u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + (w' - b) * ε) -
      χ * (N₀ + ε) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f) ≤ Vt ε)
    (heq : u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + (w' - b) * 0) -
      χ * (N₀ + 0) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + 0) + f) = Vt 0)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVN : ∀ s, HasDerivAt (fun n => Vn s ((1 - δ) * K₀ + I₀) n) (VN s) ((1 - ρ - f) * N₀ + f))
    (hVt : HasDerivAt Vt dV 0)
    (henv : VN₀ = Λ * (w - b) - χ * N₀ ^ φ + (1 - ρ - f) * (β * ∑ s, p s * VN s)) :
    dV = Λ * (w' - w) + VN₀ := by
  have hin : HasDerivAt (fun ε => R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + (w' - b) * ε)
      (w' - b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (w' - b)).const_add
      (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀)
  have hin2 : HasDerivAt (fun ε => (1 - ρ - f) * (N₀ + ε) + f) (1 - ρ - f) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add N₀).const_mul (1 - ρ - f)).add_const f
  have hin3 : HasDerivAt (fun ε : ℝ => N₀ + ε) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add N₀
  have hsum : HasDerivAt
      (fun ε => ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f))
      (∑ s, p s * (VN s * (1 - ρ - f))) 0 :=
    HasDerivAt.fun_sum fun s _ =>
      ((hVN s).comp_of_eq 0 hin2 (by ring)).const_mul (p s)
  have hdis := (jd_disutility_hasDerivAt (χ := χ) hφ hN).comp_of_eq 0 hin3 (by ring)
  have hd := (((hu.comp_of_eq 0 hin (by ring)).sub hdis).add (hsum.const_mul β))
  have := jd_envelope (g := fun ε => u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ +
      (w' - b) * ε) - χ * (N₀ + ε) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f))
    hle heq hVt hd
  rw [this, henv]
  have e : ∑ s, p s * (VN s * (1 - ρ - f)) = (1 - ρ - f) * ∑ s, p s * VN s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  ring

/-- **Correction** (Miao, p. 610, budget as printed): if the new member keeps the benefit
(`… + w̃ ε + b (1 − N_t)`), the marginal value is `Λ_t (w̃ − w_t) + ∂V_t/∂N_t + Λ_t b`, not
`Λ_t (w̃ − w_t) + ∂V_t/∂N_t` as printed; the two differ whenever `Λ_t b ≠ 0`. -/
theorem jd_hh_Vn_book_budget {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ}
    {Vn : S → ℝ → ℝ → ℝ} {Vt : ℝ → ℝ} {β δ χ φ ρ f R w w' b D T K₀ N₀ I₀ Λ VN₀ dV : ℝ}
    {VN : S → ℝ} (hφ : 0 < φ) (hN : 0 < N₀)
    (hle : ∀ ε, u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + w' * ε) -
      χ * (N₀ + ε) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f) ≤ Vt ε)
    (heq : u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + w' * 0) -
      χ * (N₀ + 0) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + 0) + f) = Vt 0)
    (hu : HasDerivAt u Λ (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀))
    (hVN : ∀ s, HasDerivAt (fun n => Vn s ((1 - δ) * K₀ + I₀) n) (VN s) ((1 - ρ - f) * N₀ + f))
    (hVt : HasDerivAt Vt dV 0)
    (henv : VN₀ = Λ * (w - b) - χ * N₀ ^ φ + (1 - ρ - f) * (β * ∑ s, p s * VN s)) :
    dV = Λ * (w' - w) + VN₀ + Λ * b ∧ (Λ * b ≠ 0 → dV ≠ Λ * (w' - w) + VN₀) := by
  have hin : HasDerivAt (fun ε => R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ + w' * ε) w' 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul w').const_add
      (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀)
  have hin2 : HasDerivAt (fun ε => (1 - ρ - f) * (N₀ + ε) + f) (1 - ρ - f) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add N₀).const_mul (1 - ρ - f)).add_const f
  have hin3 : HasDerivAt (fun ε : ℝ => N₀ + ε) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add N₀
  have hsum : HasDerivAt
      (fun ε => ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f))
      (∑ s, p s * (VN s * (1 - ρ - f))) 0 :=
    HasDerivAt.fun_sum fun s _ =>
      ((hVN s).comp_of_eq 0 hin2 (by ring)).const_mul (p s)
  have hdis := (jd_disutility_hasDerivAt (χ := χ) hφ hN).comp_of_eq 0 hin3 (by ring)
  have hd := (((hu.comp_of_eq 0 hin (by ring)).sub hdis).add (hsum.const_mul β))
  have := jd_envelope (g := fun ε => u (R * K₀ + (w - b) * N₀ + (b + D - T) - I₀ +
      w' * ε) - χ * (N₀ + ε) ^ (1 + φ) / (1 + φ) +
      β * ∑ s, p s * Vn s ((1 - δ) * K₀ + I₀) ((1 - ρ - f) * (N₀ + ε) + f))
    hle heq hVt hd
  have e : ∑ s, p s * (VN s * (1 - ρ - f)) = (1 - ρ - f) * ∑ s, p s * VN s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  have key : dV = Λ * (w' - w) + VN₀ + Λ * b := by
    rw [this, henv, e]; ring
  refine ⟨key, fun hb h => hb ?_⟩
  linarith

/-- Miao, p. 611: firm `j`'s objective at a node, with `N′ = (1 − ρ) N + q^v v` (18.22) and
stochastic discount factor `m s = β Λ_{t+1}(s)/Λ_t`. -/
noncomputable def jd_firmObj {S : Type*} [Fintype S] (F : ℝ → ℝ → ℝ) (p m : S → ℝ)
    (Jn : S → ℝ → ℝ) (A w R κ ρ qv N K v : ℝ) : ℝ :=
  F K (A * N) - w * N - R * K - v * κ + ∑ s, p s * (m s * Jn s ((1 - ρ) * N + qv * v))

/-- Miao, (18.51), p. 611: the first-order condition for capital, `F₁(K^j_t, A_t N^j_t) = R_kt`. -/
theorem eq_18_51 {S : Type*} [Fintype S] {F : ℝ → ℝ → ℝ} {p m : S → ℝ} {Jn : S → ℝ → ℝ}
    {J : ℝ → ℝ} {A w R κ ρ qv N₀ K₀ v₀ F₁ : ℝ}
    (hmax : ∀ N K v, jd_firmObj F p m Jn A w R κ ρ qv N K v ≤ J N)
    (hopt : jd_firmObj F p m Jn A w R κ ρ qv N₀ K₀ v₀ = J N₀)
    (hF₁ : HasDerivAt (fun k => F k (A * N₀)) F₁ K₀) : F₁ = R := by
  have hd := (((hF₁.sub_const (w * N₀)).sub ((hasDerivAt_id K₀).const_mul R)).sub_const
    (v₀ * κ)).add_const (∑ s, p s * (m s * Jn s ((1 - ρ) * N₀ + qv * v₀)))
  have := jd_foc (h := fun K => jd_firmObj F p m Jn A w R κ ρ qv N₀ K v₀)
    (fun K => (hmax N₀ K v₀).trans hopt.ge) hd
  simp only [mul_one] at this
  linarith

/-- Miao, (18.52), p. 611: the first-order condition for vacancies,
`κ = E_t[(β Λ_{t+1}/Λ_t) ∂J_{t+1}/∂N^j_{t+1}] q^v_t`. -/
theorem eq_18_52 {S : Type*} [Fintype S] {F : ℝ → ℝ → ℝ} {p m : S → ℝ} {Jn : S → ℝ → ℝ}
    {J : ℝ → ℝ} {A w R κ ρ qv N₀ K₀ v₀ : ℝ} {JN : S → ℝ}
    (hmax : ∀ N K v, jd_firmObj F p m Jn A w R κ ρ qv N K v ≤ J N)
    (hopt : jd_firmObj F p m Jn A w R κ ρ qv N₀ K₀ v₀ = J N₀)
    (hJN : ∀ s, HasDerivAt (Jn s) (JN s) ((1 - ρ) * N₀ + qv * v₀)) :
    κ = (∑ s, p s * (m s * JN s)) * qv := by
  have hin : HasDerivAt (fun v => (1 - ρ) * N₀ + qv * v) qv v₀ := by
    simpa using ((hasDerivAt_id v₀).const_mul qv).const_add ((1 - ρ) * N₀)
  have hsum : HasDerivAt (fun v => ∑ s, p s * (m s * Jn s ((1 - ρ) * N₀ + qv * v)))
      (∑ s, p s * (m s * (JN s * qv))) v₀ :=
    HasDerivAt.fun_sum fun s _ =>
      (((hJN s).comp_of_eq v₀ hin (by ring)).const_mul (m s)).const_mul (p s)
  have h1 : HasDerivAt (fun v => F K₀ (A * N₀) - w * N₀ - R * K₀ - v * κ) (-κ) v₀ := by
    simpa using ((hasDerivAt_id v₀).mul_const κ).const_sub (F K₀ (A * N₀) - w * N₀ - R * K₀)
  have hd := h1.add hsum
  have := jd_foc (h := fun v => jd_firmObj F p m Jn A w R κ ρ qv N₀ K₀ v)
    (fun v => (hmax N₀ K₀ v).trans hopt.ge) hd
  have e : ∑ s, p s * (m s * (JN s * qv)) = (∑ s, p s * (m s * JN s)) * qv := by
    rw [Finset.sum_mul]; congr 1; funext s; ring
  rw [e] at this
  linarith

/-- Miao, (18.53), p. 611: the envelope condition, `∂J_t/∂N^j_t = A_t F₂(K^j_t, A_t N^j_t) −
w_t + (1 − ρ) E_t[(β Λ_{t+1}/Λ_t) ∂J_{t+1}/∂N^j_{t+1}]`. -/
theorem eq_18_53 {S : Type*} [Fintype S] {F : ℝ → ℝ → ℝ} {p m : S → ℝ} {Jn : S → ℝ → ℝ}
    {J : ℝ → ℝ} {A w R κ ρ qv N₀ K₀ v₀ F₂ JN₀ : ℝ} {JN : S → ℝ}
    (hmax : ∀ N K v, jd_firmObj F p m Jn A w R κ ρ qv N K v ≤ J N)
    (hopt : jd_firmObj F p m Jn A w R κ ρ qv N₀ K₀ v₀ = J N₀)
    (hF₂ : HasDerivAt (F K₀) F₂ (A * N₀))
    (hJN : ∀ s, HasDerivAt (Jn s) (JN s) ((1 - ρ) * N₀ + qv * v₀)) (hJ : HasDerivAt J JN₀ N₀) :
    JN₀ = A * F₂ - w + (1 - ρ) * ∑ s, p s * (m s * JN s) := by
  have hin : HasDerivAt (fun N => (1 - ρ) * N + qv * v₀) (1 - ρ) N₀ := by
    simpa using ((hasDerivAt_id N₀).const_mul (1 - ρ)).add_const (qv * v₀)
  have hin2 : HasDerivAt (fun N => A * N) A N₀ := by
    simpa using (hasDerivAt_id N₀).const_mul A
  have hsum : HasDerivAt (fun N => ∑ s, p s * (m s * Jn s ((1 - ρ) * N + qv * v₀)))
      (∑ s, p s * (m s * (JN s * (1 - ρ)))) N₀ :=
    HasDerivAt.fun_sum fun s _ =>
      (((hJN s).comp_of_eq N₀ hin (by ring)).const_mul (m s)).const_mul (p s)
  have hd := ((((hF₂.comp N₀ hin2).sub ((hasDerivAt_id N₀).const_mul w)).sub_const
    (R * K₀)).sub_const (v₀ * κ)).add hsum
  have := jd_envelope (g := fun N => jd_firmObj F p m Jn A w R κ ρ qv N K₀ v₀)
    (fun N => hmax N K₀ v₀) hopt hJ hd
  rw [this]
  have e : ∑ s, p s * (m s * (JN s * (1 - ρ))) = (1 - ρ) * ∑ s, p s * (m s * JN s) := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  simp only [mul_one]
  ring

/-- Miao, (18.54), p. 611: with `S^F_t = ∂J_t/∂N^j_t`, (18.52) and (18.53) give
`S^F_t = A_t F₂(K^j_t, A_t N^j_t) − w_t + (1 − ρ) κ / q^v_t`. -/
theorem eq_18_54 {S : Type*} [Fintype S] {p m JN : S → ℝ} {A w κ ρ qv F₂ JN₀ : ℝ}
    (hqv : qv ≠ 0) (h52 : κ = (∑ s, p s * (m s * JN s)) * qv)
    (h53 : JN₀ = A * F₂ - w + (1 - ρ) * ∑ s, p s * (m s * JN s)) :
    JN₀ = A * F₂ - w + (1 - ρ) * κ / qv := by
  rw [h53, h52]
  field_simp

/-- Miao, (18.55), p. 612: substituting (18.54) at `t + 1` into (18.52),
`κ / q(θ_t) = E_t[(β Λ_{t+1}/Λ_t)(A_{t+1} F₂(K^j_{t+1}, A_{t+1} N^j_{t+1}) − w_{t+1} +
(1 − ρ) κ / q(θ_{t+1}))]`. -/
theorem eq_18_55 {S : Type*} [Fintype S] {p m JN An F₂n wn qn : S → ℝ} {κ ρ qv : ℝ}
    (hqv : qv ≠ 0) (h52 : κ = (∑ s, p s * (m s * JN s)) * qv)
    (h54 : ∀ s, JN s = An s * F₂n s - wn s + (1 - ρ) * κ / qn s) :
    κ / qv = ∑ s, p s * (m s * (An s * F₂n s - wn s + (1 - ρ) * κ / qn s)) := by
  have e : κ / qv = ∑ s, p s * (m s * JN s) := by rw [div_eq_iff hqv]; exact h52
  rw [e]
  simp only [h54]

/-- Miao, p. 612: hiring `ε` more workers at wage `w̃`, the firm's marginal value is
`J_n(w̃, t) = w_t − w̃ + ∂J_t/∂N^j_t`. `J̃(ε)` is the value with `N^j_t + ε` workers (`J̃ ≥` the
objective at the optimal `(K, v)`, equality at `ε = 0`). -/
theorem jd_firm_Jn {S : Type*} [Fintype S] {F : ℝ → ℝ → ℝ} {p m : S → ℝ} {Jn : S → ℝ → ℝ}
    {Jt : ℝ → ℝ} {A w w' R κ ρ qv N₀ K₀ v₀ F₂ JN₀ dJ : ℝ} {JN : S → ℝ}
    (hle : ∀ ε, F K₀ (A * (N₀ + ε)) - w * N₀ - w' * ε - R * K₀ - v₀ * κ +
      ∑ s, p s * (m s * Jn s ((1 - ρ) * (N₀ + ε) + qv * v₀)) ≤ Jt ε)
    (heq : F K₀ (A * (N₀ + 0)) - w * N₀ - w' * 0 - R * K₀ - v₀ * κ +
      ∑ s, p s * (m s * Jn s ((1 - ρ) * (N₀ + 0) + qv * v₀)) = Jt 0)
    (hF₂ : HasDerivAt (F K₀) F₂ (A * N₀))
    (hJN : ∀ s, HasDerivAt (Jn s) (JN s) ((1 - ρ) * N₀ + qv * v₀)) (hJt : HasDerivAt Jt dJ 0)
    (h53 : JN₀ = A * F₂ - w + (1 - ρ) * ∑ s, p s * (m s * JN s)) :
    dJ = w - w' + JN₀ := by
  have hin : HasDerivAt (fun ε => (1 - ρ) * (N₀ + ε) + qv * v₀) (1 - ρ) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add N₀).const_mul (1 - ρ)).add_const (qv * v₀)
  have hin2 : HasDerivAt (fun ε => A * (N₀ + ε)) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add N₀).const_mul A
  have hsum : HasDerivAt (fun ε => ∑ s, p s * (m s * Jn s ((1 - ρ) * (N₀ + ε) + qv * v₀)))
      (∑ s, p s * (m s * (JN s * (1 - ρ)))) 0 :=
    HasDerivAt.fun_sum fun s _ =>
      ((((hJN s).comp_of_eq 0 hin (by ring))).const_mul (m s)).const_mul (p s)
  have hd := (((((hF₂.comp_of_eq 0 hin2 (by ring)).sub_const (w * N₀)).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul w')).sub_const (R * K₀)).sub_const (v₀ * κ)).add hsum
  have := jd_envelope (g := fun ε => F K₀ (A * (N₀ + ε)) - w * N₀ - w' * ε - R * K₀ - v₀ * κ +
      ∑ s, p s * (m s * Jn s ((1 - ρ) * (N₀ + ε) + qv * v₀))) hle heq hJt hd
  rw [this, h53]
  have e : ∑ s, p s * (m s * (JN s * (1 - ρ))) = (1 - ρ) * ∑ s, p s * (m s * JN s) := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  simp only [mul_one]
  ring

/-- **Nash bargaining in §18.3** (Miao, pp. 612–613). With `V_n(w) = Λ_t (w − w_t) + V_N` and
`J_n(w) = w_t − w + J_N` (`jd_hh_Vn`, `jd_firm_Jn`), the wage `w_t` maximises
`V_n(w)^η J_n(w)^(1−η)` over the feasible wages iff `(1 − η) V_N = η Λ_t J_N`, i.e.
`(1 − η) S^H_t = η S^F_t` with `S^H_t = V_N/Λ_t`, `S^F_t = J_N`. -/
theorem jd_nash_18_3 {η Λ wt VN JN : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hΛ : 0 < Λ)
    (hVN : 0 ≤ VN) (hJN : 0 ≤ JN) :
    (∀ w, 0 ≤ Λ * (w - wt) + VN → 0 ≤ wt - w + JN →
      (Λ * (w - wt) + VN) ^ η * (wt - w + JN) ^ (1 - η) ≤ VN ^ η * JN ^ (1 - η)) ↔
      (1 - η) * (VN / Λ) = η * JN := by
  have h := jd_nash_iff (a := VN - Λ * wt) (c := wt + JN) (lam := Λ) (w := wt) hη0 hη1 hΛ
    (by linarith) (by linarith)
  have e1 : ∀ w, Λ * (w - wt) + VN = VN - Λ * wt + Λ * w := fun w => by ring
  have e2 : ∀ w, wt - w + JN = wt + JN - w := fun w => by ring
  simp only [e1, e2]
  have e3 : VN - Λ * wt + Λ * wt = VN := by ring
  have e4 : wt + JN - wt = JN := by ring
  rw [e3, e4] at h
  rw [h]
  constructor
  · intro h1; field_simp; linarith
  · intro h1; field_simp at h1; linarith

/-- **The wage equation** (Miao, (18.56), p. 613):
`w_t = (1 − η)(b + χ N_t^φ/Λ_t) + η (A_t F₂(K^j_t, A_t N^j_t) + κ θ_t)`, from (18.50), the
sharing rule `(1 − η) S^H = η S^F` at `t` and `t + 1`, (18.52) in the form
`κ / q(θ_t) = E_t[m S^F_{t+1}]`, and (18.54); the job-finding rate is `q(θ_t) θ_t`. -/
theorem eq_18_56 {S : Type*} [Fintype S] {p m SHn SFn : S → ℝ}
    {η χ φ ρ κ θ q w b N₀ Λ A F₂ SH SF : ℝ} (hη1 : η < 1) (hq : q ≠ 0) (hΛ : Λ ≠ 0)
    (h50 : SH = w - b - χ * N₀ ^ φ / Λ + (1 - ρ - q * θ) * ∑ s, p s * (m s * SHn s))
    (hshare : (1 - η) * SH = η * SF) (hsharen : ∀ s, (1 - η) * SHn s = η * SFn s)
    (h52 : κ / q = ∑ s, p s * (m s * SFn s)) (h54 : SF = A * F₂ - w + (1 - ρ) * κ / q) :
    w = (1 - η) * (b + χ * N₀ ^ φ / Λ) + η * (A * F₂ + κ * θ) := by
  have h1η : (1 - η) ≠ 0 := by linarith
  have hSHn : ∀ s, SHn s = η / (1 - η) * SFn s := fun s => by
    field_simp; linarith [hsharen s]
  have hsum : ∑ s, p s * (m s * SHn s) = η / (1 - η) * (κ / q) := by
    rw [h52, Finset.mul_sum]; congr 1; funext s; rw [hSHn]; ring
  rw [hsum] at h50
  rw [h50, h54] at hshare
  linear_combination (norm := (field_simp; ring)) hshare

/-- Miao, p. 611 ("(18.51) implies that `K^j_t/N^j_t` does not depend on firm identity"): with
constant returns and `k ↦ F₁(k, 1)` injective on `(0, ∞)`, two firms facing the same rental rate
choose the same capital per effective worker. -/
theorem jd_capital_ratio_indep {F F₁ : ℝ → ℝ → ℝ}
    (hhom : ∀ t k l, 0 < t → 0 < k → 0 < l → F (t * k) (t * l) = t * F k l)
    (hd : ∀ k l, 0 < k → 0 < l → HasDerivAt (fun x => F x l) (F₁ k l) k)
    (hinj : Set.InjOn (fun k => F₁ k 1) (Set.Ioi 0)) {A K K' N N' R : ℝ} (hA : 0 < A)
    (hK : 0 < K) (hK' : 0 < K') (hN : 0 < N) (hN' : 0 < N')
    (h51 : F₁ K (A * N) = R) (h51' : F₁ K' (A * N') = R) : K / (A * N) = K' / (A * N') := by
  have hscale : ∀ k n, 0 < k → 0 < n → F₁ k (A * n) = F₁ (k / (A * n)) 1 := by
    intro k n hk hn
    have hAn : 0 < A * n := mul_pos hA hn
    have := jd_partial_homog_one hhom hd (t := A * n) (k := k / (A * n)) (l := 1) hAn
      (div_pos hk hAn) one_pos
    rw [← this]
    congr 1
    · field_simp
    · ring
  rw [hscale K N hK hN] at h51
  rw [hscale K' N' hK' hN'] at h51'
  exact hinj (Set.mem_Ioi.mpr (div_pos hK (mul_pos hA hN)))
    (Set.mem_Ioi.mpr (div_pos hK' (mul_pos hA hN'))) (by simp only; rw [h51, h51'])

/-- Miao, p. 613 ("the wage rate `w_t` does not depend on `j`"): with constant returns, firms with
the same capital per effective worker have the same `F₂`, hence the same wage (18.56). -/
theorem jd_wage_indep {F F₂ : ℝ → ℝ → ℝ}
    (hhom : ∀ t k l, 0 < t → 0 < k → 0 < l → F (t * k) (t * l) = t * F k l)
    (hd : ∀ k l, 0 < k → 0 < l → HasDerivAt (fun y => F k y) (F₂ k l) l)
    {A K K' N N' η b χ φ Λ κ θ Nagg : ℝ} (hA : 0 < A) (hK : 0 < K) (hK' : 0 < K') (hN : 0 < N)
    (hN' : 0 < N') (hratio : K / (A * N) = K' / (A * N')) :
    (1 - η) * (b + χ * Nagg ^ φ / Λ) + η * (A * F₂ K (A * N) + κ * θ) =
      (1 - η) * (b + χ * Nagg ^ φ / Λ) + η * (A * F₂ K' (A * N') + κ * θ) := by
  have hscale : ∀ k n, 0 < k → 0 < n → F₂ k (A * n) = F₂ (k / (A * n)) 1 := by
    intro k n hk hn
    have hAn : 0 < A * n := mul_pos hA hn
    have := jd_partial_homog_two hhom hd (t := A * n) (k := k / (A * n)) (l := 1) hAn
      (div_pos hk hAn) one_pos
    rw [← this]
    congr 1
    · field_simp
    · ring
  rw [hscale K N hK hN, hscale K' N' hK' hN', hratio]

/-- Miao, p. 614: aggregation. If firm types `j` (masses `ω j`, employment `N j > 0`) all
use capital `K j = k A N j`, then `∑ ω_j F(K_j, A N_j) = F(∑ ω_j K_j, A ∑ ω_j N_j)`. -/
theorem jd_aggregate_output {ι : Type*} [Fintype ι] {F : ℝ → ℝ → ℝ}
    (hhom : ∀ t k l, 0 < t → 0 < k → 0 < l → F (t * k) (t * l) = t * F k l)
    {ω N K : ι → ℝ} {A k : ℝ} (hA : 0 < A) (hk : 0 < k)
    (hN : ∀ j, 0 < N j) (hpos : 0 < ∑ j, ω j * N j) (hK : ∀ j, K j = k * (A * N j)) :
    ∑ j, ω j * F (K j) (A * N j) = F (∑ j, ω j * K j) (A * ∑ j, ω j * N j) := by
  have hj : ∀ j, F (K j) (A * N j) = A * N j * F k 1 := by
    intro j
    have := hhom (A * N j) k 1 (mul_pos hA (hN j)) hk one_pos
    rw [mul_one] at this
    rw [hK j, mul_comm k, this]
  have hsumK : ∑ j, ω j * K j = (A * ∑ j, ω j * N j) * k := by
    rw [Finset.mul_sum, Finset.sum_mul]; congr 1; funext j; rw [hK j]; ring
  have hagg := hhom (A * ∑ j, ω j * N j) k 1 (mul_pos hA hpos) hk one_pos
  rw [mul_one] at hagg
  rw [hsumK, hagg]
  simp only [hj]
  rw [Finset.mul_sum, Finset.sum_mul]
  congr 1; funext j; ring

/-- Miao, (18.22), (18.48), p. 609: summing the firms' employment laws
`N^j_{t+1} = (1 − ρ) N^j_t + q(θ_t) v^j_t` gives the household's law
`N_{t+1} = (1 − ρ) N_t + q(θ_t) θ_t u_t` when `v_t = θ_t u_t`. -/
theorem jd_employment_consistency {ι : Type*} [Fintype ι] {ω Nj Nj' vj : ι → ℝ}
    {ρ q θ u : ℝ} (hlaw : ∀ j, Nj' j = (1 - ρ) * Nj j + q * vj j)
    (hv : ∑ j, ω j * vj j = θ * u) :
    ∑ j, ω j * Nj' j = (1 - ρ) * ∑ j, ω j * Nj j + q * θ * u := by
  simp only [hlaw]
  rw [mul_assoc, ← hv, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1; funext j; ring

/-- **The resource constraint** (Miao, p. 614): the household budget (18.46), capital (18.47),
dividends `D_t = Y_t − w_t N_t − R_kt K_t − κ v_t` and the balanced benefit budget
`T_t = b (1 − N_t)` give `C_t + K_{t+1} − (1 − δ) K_t = Y_t − κ v_t`. -/
theorem jd_resource_constraint {C I D R K w N b T K' δ Y κ v : ℝ}
    (h46 : C + I = D + R * K + w * N + b * (1 - N) - T) (h47 : K' = (1 - δ) * K + I)
    (hD : D = Y - w * N - R * K - κ * v) (hT : T = b * (1 - N)) :
    C + K' - (1 - δ) * K = Y - κ * v := by
  rw [h47]
  rw [hD, hT] at h46
  linarith

end Miao.SearchAndMatching

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 18.3–18.5 (Miao, p. 614)

Miao, *Economic Dynamics in Discrete Time*, §18.4, Exercises 3–5, p. 614.

**Exercise 18.3** (a mean-preserving spread in `G`, model of §18.2). A mean-preserving spread
(increase in risk, Rothschild–Stiglitz) raises the option-value integral pointwise,
`Φ_{G′} ≥ Φ_G`, with the mean unchanged; this integral condition is the hypothesis used, and a
concrete spread (`δ₁` versus `½ δ_{1/2} + ½ δ_{3/2}`) satisfies it (`jd_mps_example`). Proved:
steady-state tightness does not fall, and rises strictly if `Φ_{G′}(z̄*) > Φ_G(z̄*)`
(`ex_18_3_theta`); the reservation productivity moves with
`H(θ) = η θ κ − (1 − ρˣ) κ / q(θ)`, a function that does not involve `G`:
`(1 − η) A (z̄*′ − z̄*) = H(θ′) − H(θ)` (`ex_18_3_reservation`), so `z̄*` rises when `H` is
nondecreasing (`ex_18_3_reservation_mono`); steady-state unemployment falls if the separation
rate does not rise and tightness rises strictly (`ex_18_3_unemployment`). In general the
effects on `z̄*` and `u` are ambiguous (`H` need not be monotone; `G` itself changes `ρ`).

**Exercise 18.4** (the planner's problem for the model of §18.3). The planner chooses next-period
capital and vacancies subject to the resource constraint and `N′ = (1 − ρ) N + M(1 − N, v)`
(`jd_plannerObj`). Proved: the first-order conditions for capital and vacancies
(`ex_18_4_foc_K`, `ex_18_4_foc_v`), the envelope conditions (`ex_18_4_envelope_K`,
`ex_18_4_envelope_N`), the planner's Euler equation (`ex_18_4_euler`) and surplus recursion with
job creation condition (`ex_18_4_surplus`); the partial derivatives of `M(u, v) = v q(v/u)`:
`M_v = q (1 − ξ)`, `M_u = ξ θ q` with `ξ = −θ q′/q` (`jd_matching_partial_v`,
`jd_matching_partial_u`). Efficiency: node by node,
`S^F − (1 − η) S^P = −(1 − η) b + (η − ξ) κ ((1 − ρ)/q − θ)/(1 − ξ)` (`ex_18_4_gap`), so with
`b = 0` and the Hosios condition `η = ξ` the decentralised firm surplus is `(1 − η)` times the
planner's surplus and the two job creation conditions coincide (`ex_18_4_hosios`). The steady-state
tightness equations are the analogues of (18.18) and (18.28) (`ex_18_4_ss_decentralised`,
`ex_18_4_ss_planner`), and coincide when `η = ξ`, `b = 0` (`ex_18_4_ss_hosios`).

**Exercise 18.5** (calibration of §18.3; the numerical solution is not formalised). Its
mathematical content: the steady-state rental rate `R = 1/β − 1 + δ` (`ex_18_5_rental`),
employment and unemployment `N = f/(ρ + f)`, `u = ρ/(ρ + f)` (`ex_18_5_employment`), the
separation rate implied by targets for `u` and `f` (`ex_18_5_rho`), the posting cost implied by a
target `θ` (`ex_18_5_kappa`, the unique `κ` solving the steady-state tightness equation), and
steady-state consumption from the resource constraint (`ex_18_5_consumption`).
-/

namespace Miao.SearchAndMatching

open MeasureTheory Filter Topology

/-- **Exercise 18.3** (Miao, p. 614): a mean-preserving spread does not lower steady-state
tightness. `(θ, c)` is the steady state for `G = μ`, `(θ′, c′)` for `G′ = μ′`, and
`Φ_μ ≤ Φ_{μ′}` pointwise. If moreover `Φ_μ(c) < Φ_{μ′}(c)`, tightness rises strictly. -/
theorem ex_18_3_theta {μ μ' : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ}
    {β ρx η κ A b θ θ' c c' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1)
    (hη0 : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hA : 0 < A) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hθ : 0 < θ) (hθ' : 0 < θ')
    (hmps : ∀ x, jd_Phi μ x ≤ jd_Phi μ' x)
    (hC : jd_JC μ q β η κ A θ c) (hD : jd_JD μ β ρx η κ A b θ c)
    (hC' : jd_JC μ' q β η κ A θ' c') (hD' : jd_JD μ' β ρx η κ A b θ' c') :
    θ ≤ θ' ∧ (jd_Phi μ c < jd_Phi μ' c → θ < θ') := by
  unfold jd_JC at hC hC'
  unfold jd_JD at hD hD'
  have hK : 0 < β * (1 - η) * A := mul_pos (mul_pos hβ0 (by linarith)) hA
  have hk0 : 0 ≤ β * (1 - ρx) := mul_nonneg hβ0.le (by linarith)
  have hk1 : β * (1 - ρx) < 1 := by nlinarith
  have hc1 : 0 < (1 - η) * A := mul_pos (by linarith) hA
  have hq := hqpos θ hθ
  have hq' := hqpos θ' hθ'
  -- JD in the form `η θ κ + (1 − η) b = (1 − η) A h(c)`
  have eD : η * θ * κ + (1 - η) * b = (1 - η) * A * (c + β * (1 - ρx) * jd_Phi μ c) := by
    rw [hD]; ring
  have eD' : η * θ' * κ + (1 - η) * b = (1 - η) * A * (c' + β * (1 - ρx) * jd_Phi μ' c') := by
    rw [hD']; ring
  have hh := jd_h_strictMono hint hk0 hk1
  have hηκ : 0 < η * κ := mul_pos hη0 hκ
  have hweak : θ ≤ θ' := by
    by_contra hne
    have hlt : θ' < θ := not_le.mp hne
    have hqq : q θ < q θ' := hqanti (Set.mem_Ioi.mpr hθ') (Set.mem_Ioi.mpr hθ) hlt
    have h1 : κ / q θ' < κ / q θ := div_lt_div_of_pos_left hκ hq hqq
    rw [hC, hC'] at h1
    have h2 : jd_Phi μ' c' < jd_Phi μ c := lt_of_mul_lt_mul_left h1 hK.le
    have hcc : c < c' := by
      by_contra h3
      have := jd_Phi_antitone hint (not_lt.mp h3)
      linarith [hmps c']
    have h4 := hh hcc
    beta_reduce at h4
    have h5 : c' + β * (1 - ρx) * jd_Phi μ c' ≤ c' + β * (1 - ρx) * jd_Phi μ' c' := by
      have := mul_le_mul_of_nonneg_left (hmps c') hk0; linarith
    have : η * θ * κ < η * θ' * κ := by nlinarith
    nlinarith
  refine ⟨hweak, fun hstr => ?_⟩
  rcases hweak.lt_or_eq with h | h
  · exact h
  · exfalso
    subst h
    have hPP : jd_Phi μ' c' = jd_Phi μ c := by
      have : β * (1 - η) * A * jd_Phi μ' c' = β * (1 - η) * A * jd_Phi μ c := by
        rw [← hC, ← hC']
      exact mul_left_cancel₀ hK.ne' this
    have hhh : c' + β * (1 - ρx) * jd_Phi μ' c' = c + β * (1 - ρx) * jd_Phi μ c := by
      have : (1 - η) * A * (c' + β * (1 - ρx) * jd_Phi μ' c') =
          (1 - η) * A * (c + β * (1 - ρx) * jd_Phi μ c) := by rw [← eD, ← eD']
      exact mul_left_cancel₀ hc1.ne' this
    rw [hPP] at hhh
    have hcc : c' = c := by linarith
    rw [hcc] at hPP
    linarith

/-- **Exercise 18.3** (Miao, p. 614): combining (18.44) and (18.45),
`(1 − η)(A z̄* − b) = H(θ) := η θ κ − (1 − ρˣ) κ / q(θ)` for every `G`, so across two steady
states `(1 − η) A (z̄*′ − z̄*) = H(θ′) − H(θ)`. -/
theorem ex_18_3_reservation {μ μ' : Measure ℝ} {q : ℝ → ℝ} {β ρx η κ A b θ θ' c c' : ℝ}
    (hC : jd_JC μ q β η κ A θ c) (hD : jd_JD μ β ρx η κ A b θ c)
    (hC' : jd_JC μ' q β η κ A θ' c') (hD' : jd_JD μ' β ρx η κ A b θ' c') :
    (1 - η) * A * (c' - c) =
      (η * θ' * κ - (1 - ρx) * κ / q θ') - (η * θ * κ - (1 - ρx) * κ / q θ) := by
  unfold jd_JC at hC hC'
  unfold jd_JD at hD hD'
  have e : ∀ x, (1 - ρx) * κ / q x = (1 - ρx) * (κ / q x) := fun x => by ring
  rw [e, e, hC, hC']
  linarith

/-- **Exercise 18.3** (Miao, p. 614): if `H(θ) = η θ κ − (1 − ρˣ) κ / q(θ)` is nondecreasing on
`(0, ∞)`, a mean-preserving spread raises the reservation productivity (more job destruction). -/
theorem ex_18_3_reservation_mono {μ μ' : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (hint : Integrable (fun z => z) μ) {q : ℝ → ℝ}
    {β ρx η κ A b θ θ' c c' : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρx) (hρ1 : ρx < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hA : 0 < A) (hqpos : ∀ θ, 0 < θ → 0 < q θ)
    (hqanti : StrictAntiOn q (Set.Ioi 0)) (hθ : 0 < θ) (hθ' : 0 < θ')
    (hmps : ∀ x, jd_Phi μ x ≤ jd_Phi μ' x)
    (hH : MonotoneOn (fun x => η * x * κ - (1 - ρx) * κ / q x) (Set.Ioi 0))
    (hC : jd_JC μ q β η κ A θ c) (hD : jd_JD μ β ρx η κ A b θ c)
    (hC' : jd_JC μ' q β η κ A θ' c') (hD' : jd_JD μ' β ρx η κ A b θ' c') : c ≤ c' := by
  have hθθ := (ex_18_3_theta (μ' := μ') hint hβ0 hβ1 hρ0 hρ1 hη0 hη1 hκ hA hqpos hqanti hθ hθ' hmps
    hC hD hC' hD').1
  have e := ex_18_3_reservation hC hD hC' hD'
  have hm := hH (Set.mem_Ioi.mpr hθ) (Set.mem_Ioi.mpr hθ') hθθ
  beta_reduce at hm
  have hc1 : 0 < (1 - η) * A := mul_pos (by linarith) hA
  have : 0 ≤ (1 - η) * A * (c' - c) := by rw [e]; linarith
  by_contra hne
  have := mul_neg_of_pos_of_neg hc1 (by linarith [not_le.mp hne] : c' - c < 0)
  linarith

/-- **Exercise 18.3** (Miao, p. 614): steady-state unemployment `u = ρ/(ρ + q(θ)θ)` falls after the
spread if the separation rate does not rise and tightness rises strictly (`θ q(θ)` strictly
increasing). -/
theorem ex_18_3_unemployment {q : ℝ → ℝ} {ρ ρ' θ θ' : ℝ}
    (hf : StrictMonoOn (fun x => x * q x) (Set.Ioi 0)) (hθ : 0 < θ) (hθθ : θ < θ')
    (hqθ : 0 ≤ θ * q θ) (hρ : 0 < ρ) (hρ' : 0 ≤ ρ') (hρρ : ρ' ≤ ρ) :
    ρ' / (ρ' + θ' * q θ') < ρ / (ρ + θ * q θ) := by
  have := hf (Set.mem_Ioi.mpr hθ) (Set.mem_Ioi.mpr (lt_trans hθ hθθ)) hθθ
  beta_reduce at this
  exact jd_compstat_kappaA_u hρ hρ' hρρ hqθ this

/-- **Exercise 18.3** (a concrete mean-preserving spread): `G′ = ½ δ_{1/2} + ½ δ_{3/2}` spreads
`G = δ₁`: same total mass and mean, and `Φ_G ≤ Φ_{G′}` pointwise. -/
theorem jd_mps_example :
    let μ' : Measure ℝ := (1 / 2 : ENNReal) • Measure.dirac (1 / 2 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac (3 / 2 : ℝ)
    μ' Set.univ = 1 ∧ ∫ z, z ∂μ' = 1 ∧ ∀ c, jd_Phi (Measure.dirac 1) c ≤ jd_Phi μ' c := by
  intro μ'
  have hint : ∀ f : ℝ → ℝ, Integrable f μ' := by
    intro f
    refine Integrable.add_measure ?_ ?_
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
  have hI : ∀ f : ℝ → ℝ, ∫ z, f z ∂μ' = 1 / 2 * f (1 / 2) + 1 / 2 * f (3 / 2) := by
    intro f
    rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
      integral_dirac]
    · simp
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
  have _ := hint
  refine ⟨?_, ?_, fun c => ?_⟩
  · simp only [μ', Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [ENNReal.add_halves]
  · rw [hI]; norm_num
  · unfold jd_Phi
    rw [hI, integral_dirac]
    apply max_le
    · have h1 := le_max_left (1 / 2 - c) 0
      have h2 := le_max_left (3 / 2 - c) 0
      linarith
    · have h1 := le_max_right (1 / 2 - c) 0
      have h2 := le_max_right (3 / 2 - c) 0
      linarith

/-- **Exercise 18.4** (Miao, p. 614): the planner's objective at a node of the §18.3 model.
Controls are next-period capital `K′` and vacancies `v`; consumption comes from the resource
constraint `C = F(K, A N) + (1 − δ) K − κ v − K′` and employment evolves by
`N′ = (1 − ρ) N + M(1 − N, v)`. -/
noncomputable def jd_plannerObj {S : Type*} [Fintype S] (u : ℝ → ℝ) (p : S → ℝ)
    (W : S → ℝ → ℝ → ℝ) (F M : ℝ → ℝ → ℝ) (β δ χ φ ρ κ A K N K' v : ℝ) : ℝ :=
  u (F K (A * N) + (1 - δ) * K - κ * v - K') - χ * N ^ (1 + φ) / (1 + φ) +
    β * ∑ s, p s * W s K' ((1 - ρ) * N + M (1 - N) v)

/-- **Exercise 18.4** (Miao, p. 614): the planner's first-order condition for capital,
`Λ_t = β E_t ∂W_{t+1}/∂K_{t+1}`. -/
theorem ex_18_4_foc_K {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {W : S → ℝ → ℝ → ℝ}
    {F M : ℝ → ℝ → ℝ} {Wv : ℝ → ℝ → ℝ} {β δ χ φ ρ κ A K₀ N₀ K₁ v₀ Λ : ℝ} {WK : S → ℝ}
    (hmax : ∀ K N K' v, jd_plannerObj u p W F M β δ χ φ ρ κ A K N K' v ≤ Wv K N)
    (hopt : jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v₀ = Wv K₀ N₀)
    (hu : HasDerivAt u Λ (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - K₁))
    (hWK : ∀ s, HasDerivAt (fun k => W s k ((1 - ρ) * N₀ + M (1 - N₀) v₀)) (WK s) K₁) :
    Λ = β * ∑ s, p s * WK s := by
  have hin : HasDerivAt (fun k => F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - k) (-1) K₁ := by
    simpa using (hasDerivAt_id K₁).const_sub (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀)
  have hsum : HasDerivAt (fun k => ∑ s, p s * W s k ((1 - ρ) * N₀ + M (1 - N₀) v₀))
      (∑ s, p s * WK s) K₁ := HasDerivAt.fun_sum fun s _ => (hWK s).const_mul (p s)
  have hd := ((hu.comp K₁ hin).sub_const (χ * N₀ ^ (1 + φ) / (1 + φ))).add (hsum.const_mul β)
  have := jd_foc (h := fun k => jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ k v₀)
    (fun k => (hmax K₀ N₀ k v₀).trans hopt.ge) hd
  linarith

/-- **Exercise 18.4** (Miao, p. 614): the planner's first-order condition for vacancies,
`κ Λ_t = M_v(u_t, v_t) β E_t ∂W_{t+1}/∂N_{t+1}`. -/
theorem ex_18_4_foc_v {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {W : S → ℝ → ℝ → ℝ}
    {F M : ℝ → ℝ → ℝ} {Wv : ℝ → ℝ → ℝ} {β δ χ φ ρ κ A K₀ N₀ K₁ v₀ Λ Mv : ℝ} {WN : S → ℝ}
    (hmax : ∀ K N K' v, jd_plannerObj u p W F M β δ χ φ ρ κ A K N K' v ≤ Wv K N)
    (hopt : jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v₀ = Wv K₀ N₀)
    (hu : HasDerivAt u Λ (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - K₁))
    (hMv : HasDerivAt (fun y => M (1 - N₀) y) Mv v₀)
    (hWN : ∀ s, HasDerivAt (fun n => W s K₁ n) (WN s) ((1 - ρ) * N₀ + M (1 - N₀) v₀)) :
    κ * Λ = Mv * (β * ∑ s, p s * WN s) := by
  have hin : HasDerivAt (fun v => F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v - K₁) (-κ) v₀ := by
    simpa using (((hasDerivAt_id v₀).const_mul κ).const_sub
      (F K₀ (A * N₀) + (1 - δ) * K₀)).sub_const K₁
  have hin2 : HasDerivAt (fun v => (1 - ρ) * N₀ + M (1 - N₀) v) Mv v₀ :=
    hMv.const_add ((1 - ρ) * N₀)
  have hsum : HasDerivAt (fun v => ∑ s, p s * W s K₁ ((1 - ρ) * N₀ + M (1 - N₀) v))
      (∑ s, p s * (WN s * Mv)) v₀ :=
    HasDerivAt.fun_sum fun s _ => ((hWN s).comp_of_eq v₀ hin2 (by ring)).const_mul (p s)
  have hd := ((hu.comp v₀ hin).sub_const (χ * N₀ ^ (1 + φ) / (1 + φ))).add (hsum.const_mul β)
  have := jd_foc (h := fun v => jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v)
    (fun v => (hmax K₀ N₀ K₁ v).trans hopt.ge) hd
  have e : ∑ s, p s * (WN s * Mv) = Mv * ∑ s, p s * WN s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e] at this
  linarith

/-- **Exercise 18.4** (Miao, p. 614): the planner's envelope condition for capital,
`∂W_t/∂K_t = Λ_t (F₁(K_t, A_t N_t) + 1 − δ)`. -/
theorem ex_18_4_envelope_K {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ}
    {W : S → ℝ → ℝ → ℝ} {F M : ℝ → ℝ → ℝ} {Wv : ℝ → ℝ → ℝ}
    {β δ χ φ ρ κ A K₀ N₀ K₁ v₀ Λ F₁ WK₀ : ℝ}
    (hmax : ∀ K N K' v, jd_plannerObj u p W F M β δ χ φ ρ κ A K N K' v ≤ Wv K N)
    (hopt : jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v₀ = Wv K₀ N₀)
    (hu : HasDerivAt u Λ (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - K₁))
    (hF₁ : HasDerivAt (fun k => F k (A * N₀)) F₁ K₀) (hW : HasDerivAt (fun k => Wv k N₀) WK₀ K₀) :
    WK₀ = Λ * (F₁ + 1 - δ) := by
  have hin : HasDerivAt (fun k => F k (A * N₀) + (1 - δ) * k - κ * v₀ - K₁) (F₁ + (1 - δ)) K₀ := by
    simpa using ((hF₁.add ((hasDerivAt_id K₀).const_mul (1 - δ))).sub_const (κ * v₀)).sub_const K₁
  have hd := ((hu.comp K₀ hin).sub_const (χ * N₀ ^ (1 + φ) / (1 + φ))).add_const
    (β * ∑ s, p s * W s K₁ ((1 - ρ) * N₀ + M (1 - N₀) v₀))
  have := jd_envelope (g := fun k => jd_plannerObj u p W F M β δ χ φ ρ κ A k N₀ K₁ v₀)
    (fun k => hmax k N₀ K₁ v₀) hopt hW hd
  rw [this]
  ring

/-- **Exercise 18.4** (Miao, p. 614): the planner's Euler equation
`Λ_t = β E_t[Λ_{t+1}(F₁(K_{t+1}, A_{t+1} N_{t+1}) + 1 − δ)]`, identical to (18.49) with
`R_k = F₁` (18.51). -/
theorem ex_18_4_euler {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ} {W : S → ℝ → ℝ → ℝ}
    {F M : ℝ → ℝ → ℝ} {Wv : ℝ → ℝ → ℝ} {β δ χ φ ρ κ A K₀ N₀ K₁ v₀ Λ : ℝ}
    {WK Λn F₁n : S → ℝ}
    (hmax : ∀ K N K' v, jd_plannerObj u p W F M β δ χ φ ρ κ A K N K' v ≤ Wv K N)
    (hopt : jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v₀ = Wv K₀ N₀)
    (hu : HasDerivAt u Λ (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - K₁))
    (hWK : ∀ s, HasDerivAt (fun k => W s k ((1 - ρ) * N₀ + M (1 - N₀) v₀)) (WK s) K₁)
    (henv : ∀ s, WK s = Λn s * (F₁n s + 1 - δ)) :
    Λ = β * ∑ s, p s * (Λn s * (F₁n s + 1 - δ)) := by
  rw [ex_18_4_foc_K hmax hopt hu hWK]
  simp only [henv]

/-- **Exercise 18.4** (Miao, p. 614): the planner's envelope condition for employment,
`∂W_t/∂N_t = Λ_t A_t F₂ − χ N_t^φ + (1 − ρ − M_u) β E_t ∂W_{t+1}/∂N_{t+1}`. -/
theorem ex_18_4_envelope_N {S : Type*} [Fintype S] {u : ℝ → ℝ} {p : S → ℝ}
    {W : S → ℝ → ℝ → ℝ} {F M : ℝ → ℝ → ℝ} {Wv : ℝ → ℝ → ℝ}
    {β δ χ φ ρ κ A K₀ N₀ K₁ v₀ Λ F₂ Mu WN₀ : ℝ} {WN : S → ℝ} (hφ : 0 < φ) (hN : 0 < N₀)
    (hmax : ∀ K N K' v, jd_plannerObj u p W F M β δ χ φ ρ κ A K N K' v ≤ Wv K N)
    (hopt : jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ N₀ K₁ v₀ = Wv K₀ N₀)
    (hu : HasDerivAt u Λ (F K₀ (A * N₀) + (1 - δ) * K₀ - κ * v₀ - K₁))
    (hF₂ : HasDerivAt (F K₀) F₂ (A * N₀)) (hMu : HasDerivAt (fun x => M x v₀) Mu (1 - N₀))
    (hWN : ∀ s, HasDerivAt (fun n => W s K₁ n) (WN s) ((1 - ρ) * N₀ + M (1 - N₀) v₀))
    (hW : HasDerivAt (fun n => Wv K₀ n) WN₀ N₀) :
    WN₀ = Λ * (A * F₂) - χ * N₀ ^ φ + (1 - ρ - Mu) * (β * ∑ s, p s * WN s) := by
  have hAN : HasDerivAt (fun n => A * n) A N₀ := by simpa using (hasDerivAt_id N₀).const_mul A
  have hin : HasDerivAt (fun n => F K₀ (A * n) + (1 - δ) * K₀ - κ * v₀ - K₁) (F₂ * A) N₀ :=
    (((hF₂.comp N₀ hAN).add_const ((1 - δ) * K₀)).sub_const (κ * v₀)).sub_const K₁
  have h1N : HasDerivAt (fun n : ℝ => 1 - n) (-1) N₀ := by
    simpa using (hasDerivAt_id N₀).const_sub 1
  have hMN : HasDerivAt (fun n => M (1 - n) v₀) (Mu * (-1)) N₀ := hMu.comp N₀ h1N
  have hin2 : HasDerivAt (fun n => (1 - ρ) * n + M (1 - n) v₀) ((1 - ρ) + Mu * (-1)) N₀ := by
    have := ((hasDerivAt_id N₀).const_mul (1 - ρ)).add hMN
    exact this.congr_deriv (by ring)
  have hsum : HasDerivAt (fun n => ∑ s, p s * W s K₁ ((1 - ρ) * n + M (1 - n) v₀))
      (∑ s, p s * (WN s * ((1 - ρ) + Mu * (-1)))) N₀ :=
    HasDerivAt.fun_sum fun s _ => ((hWN s).comp_of_eq N₀ hin2 (by ring)).const_mul (p s)
  have hd := ((hu.comp_of_eq N₀ hin (by ring)).sub
    (jd_disutility_hasDerivAt (χ := χ) hφ hN)).add (hsum.const_mul β)
  have := jd_envelope (g := fun n => jd_plannerObj u p W F M β δ χ φ ρ κ A K₀ n K₁ v₀)
    (fun n => hmax K₀ n K₁ v₀) hopt hW hd
  rw [this]
  have e : ∑ s, p s * (WN s * ((1 - ρ) + Mu * (-1))) = (1 - ρ - Mu) * ∑ s, p s * WN s := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  rw [e]
  ring

/-- **Exercise 18.4** (Miao, p. 614): with the planner's surplus `S^P_t = (∂W_t/∂N_t)/Λ_t`,
`m = β Λ_{t+1}/Λ_t` and `∂W_{t+1}/∂N_{t+1} = Λ_{t+1} S^P_{t+1}`, the planner's job creation
condition is `κ / M_v = E_t[m S^P_{t+1}]` and
`S^P_t = A_t F₂ − χ N_t^φ/Λ_t + (1 − ρ − M_u) κ / M_v`. -/
theorem ex_18_4_surplus {S : Type*} [Fintype S] {p Λn SPn WN : S → ℝ}
    {β χ φ ρ κ A F₂ N₀ Λ Mu Mv WN₀ : ℝ} (hΛ : Λ ≠ 0) (hMv : Mv ≠ 0)
    (hfoc : κ * Λ = Mv * (β * ∑ s, p s * WN s))
    (henv : WN₀ = Λ * (A * F₂) - χ * N₀ ^ φ + (1 - ρ - Mu) * (β * ∑ s, p s * WN s))
    (hnext : ∀ s, WN s = Λn s * SPn s) :
    κ / Mv = ∑ s, p s * (β * Λn s / Λ * SPn s) ∧
      WN₀ / Λ = A * F₂ - χ * N₀ ^ φ / Λ + (1 - ρ - Mu) * (κ / Mv) := by
  have e : ∑ s, p s * (β * Λn s / Λ * SPn s) = (β * ∑ s, p s * WN s) / Λ := by
    rw [Finset.mul_sum, Finset.sum_div]; congr 1; funext s; rw [hnext]; field_simp
  have h1 : κ / Mv = (β * ∑ s, p s * WN s) / Λ := by
    field_simp; linarith
  refine ⟨by rw [e, h1], ?_⟩
  rw [h1, henv]
  field_simp

/-- **Exercise 18.4** (Miao, p. 614): for `M(u, v) = v q(v/u)` and `θ = v/u`,
`∂M/∂v = q(θ) + θ q′(θ) = q(θ)(1 − ξ(θ))`, `ξ = −θ q′/q`. -/
theorem jd_matching_partial_v {q : ℝ → ℝ} {u v q' : ℝ} (hu : 0 < u)
    (hq : HasDerivAt q q' (v / u)) :
    HasDerivAt (fun y => y * q (y / u)) (q (v / u) + v / u * q') v := by
  have hin : HasDerivAt (fun y => y / u) (1 / u) v := by
    simpa using (hasDerivAt_id v).div_const u
  have := (hasDerivAt_id v).mul (hq.comp v hin)
  exact this.congr_deriv (by simp only [Function.comp_apply, id_eq]; field_simp)

/-- **Exercise 18.4** (Miao, p. 614): for `M(u, v) = v q(v/u)`,
`∂M/∂u = −θ² q′(θ) = ξ(θ) θ q(θ)`. -/
theorem jd_matching_partial_u {q : ℝ → ℝ} {u v q' : ℝ} (hu : 0 < u)
    (hq : HasDerivAt q q' (v / u)) :
    HasDerivAt (fun x => v * q (v / x)) (-(v / u) ^ 2 * q') u := by
  have hin : HasDerivAt (fun x => v / x) (-(v / u ^ 2)) u := by
    have := (hasDerivAt_inv hu.ne').const_mul v
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp
  have := (hq.comp u hin).const_mul v
  exact this.congr_deriv (by field_simp)

/-- **Exercise 18.4** (efficiency gap, Miao, pp. 599, 614). At a node, with `M_v = q (1 − ξ)`,
`M_u = ξ θ q`, the decentralised firm surplus (18.54) under the wage (18.56),
`S^F = (1 − η)(A F₂ − b − χ N^φ/Λ) − η κ θ + (1 − ρ) κ / q`, and the planner's surplus
`S^P = A F₂ − χ N^φ/Λ + (1 − ρ − M_u) κ / M_v` satisfy
`S^F − (1 − η) S^P = −(1 − η) b + (η − ξ) κ ((1 − ρ)/q − θ)/(1 − ξ)`. -/
theorem ex_18_4_gap {η ξ ρ κ θ q b y : ℝ} (hq : q ≠ 0) (hξ : ξ ≠ 1) :
    ((1 - η) * (y - b) - η * κ * θ + (1 - ρ) * κ / q) -
      (1 - η) * (y + (1 - ρ - ξ * θ * q) * κ / (q * (1 - ξ))) =
      -(1 - η) * b + (η - ξ) * κ * ((1 - ρ) / q - θ) / (1 - ξ) := by
  have h1 : (1 - ξ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hξ)
  field_simp
  ring

/-- **Exercise 18.4: the Hosios condition** (Miao, pp. 599, 614). With `b = 0` and `η = ξ`
(constant elasticity, e.g. Cobb–Douglas matching), the decentralised firm surplus is `(1 − η)`
times the planner's surplus at every node, so the decentralised job creation condition (18.55),
`κ / q = E_t[m S^F_{t+1}]`, holds iff the planner's, `κ / M_v = E_t[m S^P_{t+1}]` with
`M_v = q (1 − η)`. -/
theorem ex_18_4_hosios {S : Type*} [Fintype S] {p m SFn SPn : S → ℝ} {η q κ : ℝ}
    (hη1 : η < 1) (hq : q ≠ 0) (hrel : ∀ s, SFn s = (1 - η) * SPn s) :
    κ / q = ∑ s, p s * (m s * SFn s) ↔ κ / (q * (1 - η)) = ∑ s, p s * (m s * SPn s) := by
  have h1 : (1 - η) ≠ 0 := by linarith
  have e : ∑ s, p s * (m s * SFn s) = (1 - η) * ∑ s, p s * (m s * SPn s) := by
    rw [Finset.mul_sum]; congr 1; funext s; rw [hrel]; ring
  rw [e]
  constructor
  · intro h
    rw [div_mul_eq_div_div, h]
    field_simp
  · intro h
    rw [div_mul_eq_div_div] at h
    rw [← h]
    field_simp

/-- **Exercise 18.4** (Miao, p. 614): the node identity behind `ex_18_4_hosios`: with `b = 0` and
`ξ = η`, `S^F = (1 − η) S^P`. -/
theorem ex_18_4_surplus_hosios {η ρ κ θ q y : ℝ} (hq : q ≠ 0) (hη : η ≠ 1) :
    (1 - η) * (y - 0) - η * κ * θ + (1 - ρ) * κ / q =
      (1 - η) * (y + (1 - ρ - η * θ * q) * κ / (q * (1 - η))) := by
  have := ex_18_4_gap (η := η) (ξ := η) (ρ := ρ) (κ := κ) (θ := θ) (b := 0) (y := y) hq hη
  simp only [sub_self, zero_mul, zero_div, mul_zero, add_zero] at this
  linarith

/-- **Exercise 18.4** (Miao, p. 614; analogue of (18.18)): in a steady state of the decentralised
§18.3 economy (`m = β` in (18.55), wage (18.56)), with `a = A F₂` and `h = χ N^φ/Λ`:
`κ / q(θ) (1 − β(1 − ρ)) + β η κ θ = β (1 − η)(a − h − b)`. -/
theorem ex_18_4_ss_decentralised {β ρ κ η θ q w b a h SF : ℝ}
    (h55 : κ / q = β * SF) (h54 : SF = a - w + (1 - ρ) * κ / q)
    (h56 : w = (1 - η) * (b + h) + η * (a + κ * θ)) :
    κ / q * (1 - β * (1 - ρ)) + β * η * κ * θ = β * (1 - η) * (a - h - b) := by
  rw [h54, h56] at h55
  have e : (1 - ρ) * κ / q = (1 - ρ) * (κ / q) := by ring
  rw [e] at h55
  linear_combination h55

/-- **Exercise 18.4** (Miao, p. 614; analogue of (18.28)): in a steady state of the planner's
problem (`m = β`), with `M_v = q (1 − ξ)`, `M_u = ξ θ q`, `a = A F₂`, `h = χ N^φ/Λ`:
`κ / q(θ) (1 − β(1 − ρ)) + β ξ κ θ = β (1 − ξ)(a − h)`. -/
theorem ex_18_4_ss_planner {β ρ κ ξ θ q a h SP : ℝ} (hq : q ≠ 0) (hξ : ξ ≠ 1)
    (hjc : κ / (q * (1 - ξ)) = β * SP)
    (hsp : SP = a - h + (1 - ρ - ξ * θ * q) * (κ / (q * (1 - ξ)))) :
    κ / q * (1 - β * (1 - ρ)) + β * ξ * κ * θ = β * (1 - ξ) * (a - h) := by
  have h1 : (1 - ξ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hξ)
  rw [hsp] at hjc
  have e : κ / (q * (1 - ξ)) = κ / q / (1 - ξ) := by rw [div_mul_eq_div_div]
  rw [e] at hjc
  linear_combination (norm := (field_simp; ring)) (1 - ξ) * hjc

/-- **Exercise 18.4** (Miao, pp. 599, 614): with `b = 0`, the decentralised and planner's
steady-state tightness equations (`ex_18_4_ss_decentralised`, `ex_18_4_ss_planner`) differ by
`β (η − ξ)(κ θ + y)`, `y = a − h`: they coincide when `η = ξ` (Hosios), and if both hold with
`κ θ + y ≠ 0`, `β > 0`, then `η = ξ`. -/
theorem ex_18_4_ss_hosios {β ρ κ η ξ θ q y : ℝ} :
    (η = ξ → (κ / q * (1 - β * (1 - ρ)) + β * η * κ * θ = β * (1 - η) * (y - 0) ↔
      κ / q * (1 - β * (1 - ρ)) + β * ξ * κ * θ = β * (1 - ξ) * y)) ∧
    (0 < β → κ * θ + y ≠ 0 →
      κ / q * (1 - β * (1 - ρ)) + β * η * κ * θ = β * (1 - η) * (y - 0) →
      κ / q * (1 - β * (1 - ρ)) + β * ξ * κ * θ = β * (1 - ξ) * y → η = ξ) := by
  refine ⟨fun h => by rw [h, sub_zero], fun hβ hne h1 h2 => ?_⟩
  have : β * ((η - ξ) * (κ * θ + y)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h3 | h3
  · linarith
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exact absurd h4 hne

/-- **Exercise 18.5** (Miao, p. 614): in a deterministic steady state the Euler equation (18.49),
`1 = β (R + 1 − δ)`, gives the rental rate `R = 1/β − 1 + δ`. -/
theorem ex_18_5_rental {β δ R : ℝ} (hβ : 0 < β) (h49 : 1 = β * (R + 1 - δ)) :
    R = 1 / β - 1 + δ := by
  field_simp
  linarith

/-- **Exercise 18.5** (Miao, p. 614): steady-state employment (18.48) with job-finding rate
`f = q(θ) θ`: `N = (1 − ρ) N + f (1 − N)` iff `N = f/(ρ + f)`, and then `u = ρ/(ρ + f)`. -/
theorem ex_18_5_employment {ρ f N : ℝ} (hpos : 0 < ρ + f) :
    N = (1 - ρ) * N + f * (1 - N) ↔ N = f / (ρ + f) ∧ 1 - N = ρ / (ρ + f) := by
  constructor
  · intro h
    constructor
    · field_simp; linarith
    · field_simp; linarith
  · intro ⟨h, _⟩
    rw [h]
    field_simp
    ring

/-- **Exercise 18.5** (Miao, p. 614): targets for unemployment `u ∈ (0, 1)` and the job-finding
rate `f` pin down the separation rate `ρ = f u /(1 − u)` (steady state of (18.48)). -/
theorem ex_18_5_rho {ρ f u : ℝ} (hu1 : u < 1) :
    1 - u = (1 - ρ) * (1 - u) + f * u ↔ ρ = f * u / (1 - u) := by
  have : (1 - u) ≠ 0 := by linarith
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp; ring

/-- **Exercise 18.5** (Miao, p. 614): given a target `θ` and `y = A F₂ − χ N^φ/Λ`, the
steady-state tightness equation of `ex_18_4_ss_decentralised` determines the posting cost
uniquely: `κ = β (1 − η)(y − b) / ((1 − β(1 − ρ))/q(θ) + β η θ)`. -/
theorem ex_18_5_kappa {β ρ η θ q y b κ : ℝ}
    (hden : (1 - β * (1 - ρ)) / q + β * η * θ ≠ 0) :
    κ / q * (1 - β * (1 - ρ)) + β * η * κ * θ = β * (1 - η) * (y - b) ↔
      κ = β * (1 - η) * (y - b) / ((1 - β * (1 - ρ)) / q + β * η * θ) := by
  rw [eq_div_iff hden]
  have e : κ / q * (1 - β * (1 - ρ)) + β * η * κ * θ =
      κ * ((1 - β * (1 - ρ)) / q + β * η * θ) := by ring
  rw [e]

/-- **Exercise 18.5** (Miao, p. 614): steady-state consumption from the resource constraint,
`C = F(K, A N) − δ K − κ v` with `v = θ u`. -/
theorem ex_18_5_consumption {C K Y δ κ v θ u : ℝ} (hv : v = θ * u)
    (hrc : C + K - (1 - δ) * K = Y - κ * v) : C = Y - δ * K - κ * θ * u := by
  rw [hv] at hrc
  linarith

end Miao.SearchAndMatching

set_option linter.style.longLine false
#print axioms Miao.SearchAndMatching.DMMatchingFn
#print axioms Miao.SearchAndMatching.DMMatchingFn.mk
#print axioms Miao.SearchAndMatching.DMMatchingFn.M
#print axioms Miao.SearchAndMatching.DMMatchingFn.pos
#print axioms Miao.SearchAndMatching.DMMatchingFn.homog
#print axioms Miao.SearchAndMatching.DMMatchingFn.mono_u
#print axioms Miao.SearchAndMatching.DMMatchingFn.mono_v
#print axioms Miao.SearchAndMatching.DMMatchingFn.concave
#print axioms Miao.SearchAndMatching.dm_q
#print axioms Miao.SearchAndMatching.dm_xi
#print axioms Miao.SearchAndMatching.dm_M_eq_mul_q
#print axioms Miao.SearchAndMatching.eq_18_1
#print axioms Miao.SearchAndMatching.dm_jobFinding
#print axioms Miao.SearchAndMatching.dm_q_pos
#print axioms Miao.SearchAndMatching.dm_q_strictAntiOn
#print axioms Miao.SearchAndMatching.dm_jobFinding_strictMonoOn
#print axioms Miao.SearchAndMatching.dm_concave_u
#print axioms Miao.SearchAndMatching.dm_q_continuousOn
#print axioms Miao.SearchAndMatching.dm_q_hasDerivAt
#print axioms Miao.SearchAndMatching.dm_Mu_pos
#print axioms Miao.SearchAndMatching.dm_Mu_mul_lt
#print axioms Miao.SearchAndMatching.dm_q_elasticity
#print axioms Miao.SearchAndMatching.dm_xi_mem
#print axioms Miao.SearchAndMatching.dm_jobFinding_hasDerivAt
#print axioms Miao.SearchAndMatching.dm_beveridge_anti
#print axioms Miao.SearchAndMatching.dm_beveridge_convex
#print axioms Miao.SearchAndMatching.dm_cd_homog
#print axioms Miao.SearchAndMatching.dm_cd_concave
#print axioms Miao.SearchAndMatching.dm_cdMatching
#print axioms Miao.SearchAndMatching.dm_cd_q
#print axioms Miao.SearchAndMatching.dm_cd_hasDerivAt
#print axioms Miao.SearchAndMatching.dm_cd_xi
#print axioms Miao.SearchAndMatching.eq_18_6
#print axioms Miao.SearchAndMatching.eq_18_7
#print axioms Miao.SearchAndMatching.eq_18_8
#print axioms Miao.SearchAndMatching.dm_amgm2_strict
#print axioms Miao.SearchAndMatching.dm_nash_bound
#print axioms Miao.SearchAndMatching.dm_nash_solution
#print axioms Miao.SearchAndMatching.eq_18_11
#print axioms Miao.SearchAndMatching.dm_surplus
#print axioms Miao.SearchAndMatching.eq_18_12
#print axioms Miao.SearchAndMatching.eq_18_13
#print axioms Miao.SearchAndMatching.eq_18_14
#print axioms Miao.SearchAndMatching.dm_worker_surplus
#print axioms Miao.SearchAndMatching.eq_18_15
#print axioms Miao.SearchAndMatching.dm_IsSearchEqm
#print axioms Miao.SearchAndMatching.dm_bellman_implies_eqm
#print axioms Miao.SearchAndMatching.dm_jcCurve
#print axioms Miao.SearchAndMatching.dm_wageCurve
#print axioms Miao.SearchAndMatching.dm_ssLHS
#print axioms Miao.SearchAndMatching.dm_uStar
#print axioms Miao.SearchAndMatching.eq_18_16
#print axioms Miao.SearchAndMatching.dm_jc_iff
#print axioms Miao.SearchAndMatching.dm_jc_strictAntiOn
#print axioms Miao.SearchAndMatching.eq_18_17
#print axioms Miao.SearchAndMatching.dm_wc_strictMono
#print axioms Miao.SearchAndMatching.eq_18_18
#print axioms Miao.SearchAndMatching.dm_wc_eq_jc
#print axioms Miao.SearchAndMatching.dm_ssLHS_strictMonoOn
#print axioms Miao.SearchAndMatching.dm_ss_unique
#print axioms Miao.SearchAndMatching.dm_ss_exists
#print axioms Miao.SearchAndMatching.dm_ss_not_exists
#print axioms Miao.SearchAndMatching.dm_cd_ssLHS
#print axioms Miao.SearchAndMatching.dm_cd_ss_existsUnique
#print axioms Miao.SearchAndMatching.eq_18_19
#print axioms Miao.SearchAndMatching.dm_uStar_mem
#print axioms Miao.SearchAndMatching.dm_uStar_strictAntiOn
#print axioms Miao.SearchAndMatching.dm_vStar_strictMonoOn
#print axioms Miao.SearchAndMatching.dm_cs_shifts
#print axioms Miao.SearchAndMatching.dm_cs_A
#print axioms Miao.SearchAndMatching.dm_cs_b
#print axioms Miao.SearchAndMatching.dm_cs_eta
#print axioms Miao.SearchAndMatching.dm_steady_isSearchEqm
#print axioms Miao.SearchAndMatching.dm_searchEqm_exists
#print axioms Miao.SearchAndMatching.eq_18_20
#print axioms Miao.SearchAndMatching.eq_18_21
#print axioms Miao.SearchAndMatching.dm_a11
#print axioms Miao.SearchAndMatching.dm_lin_a11
#print axioms Miao.SearchAndMatching.dm_a11_xi
#print axioms Miao.SearchAndMatching.dm_a11_gt_one
#print axioms Miao.SearchAndMatching.dm_a21
#print axioms Miao.SearchAndMatching.dm_a21_sign
#print axioms Miao.SearchAndMatching.dm_a22
#print axioms Miao.SearchAndMatching.dm_a22_mem
#print axioms Miao.SearchAndMatching.dm_saddle_path
#print axioms Miao.SearchAndMatching.dm_dtheta_locus
#print axioms Miao.SearchAndMatching.dm_du_locus
#print axioms Miao.SearchAndMatching.dm_uPath
#print axioms Miao.SearchAndMatching.dm_uPath_rec
#print axioms Miao.SearchAndMatching.dm_uPath_sub
#print axioms Miao.SearchAndMatching.dm_uPath_tendsto
#print axioms Miao.SearchAndMatching.dm_uPath_mem
#print axioms Miao.SearchAndMatching.dm_uPath_strictAnti
#print axioms Miao.SearchAndMatching.dm_vPath_strictAnti
#print axioms Miao.SearchAndMatching.dm_v0_gt
#print axioms Miao.SearchAndMatching.dm_transition_isSearchEqm
#print axioms Miao.SearchAndMatching.dm_transition_not_monotone
#print axioms Miao.SearchAndMatching.dm_firmProfit
#print axioms Miao.SearchAndMatching.dm_FirmFeasible
#print axioms Miao.SearchAndMatching.dm_FirmOptimal
#print axioms Miao.SearchAndMatching.dm_firm_euler
#print axioms Miao.SearchAndMatching.dm_largeFirm_eq_18_8
#print axioms Miao.SearchAndMatching.dm_firmOptimal_of_euler
#print axioms Miao.SearchAndMatching.dm_firmOptimal_exists
#print axioms Miao.SearchAndMatching.eq_18_23
#print axioms Miao.SearchAndMatching.dm_aggregate_18_2
#print axioms Miao.SearchAndMatching.eq_18_24
#print axioms Miao.SearchAndMatching.dm_Jn
#print axioms Miao.SearchAndMatching.eq_18_26
#print axioms Miao.SearchAndMatching.eq_18_27
#print axioms Miao.SearchAndMatching.dm_planner_foc_v
#print axioms Miao.SearchAndMatching.dm_planner_foc_N
#print axioms Miao.SearchAndMatching.dm_planner_foc_N_misprint
#print axioms Miao.SearchAndMatching.dm_plannerLHS
#print axioms Miao.SearchAndMatching.eq_18_28
#print axioms Miao.SearchAndMatching.dm_hosios
#print axioms Miao.SearchAndMatching.dm_xi_duration
#print axioms Miao.SearchAndMatching.dm_cd_plannerLHS
#print axioms Miao.SearchAndMatching.dm_cd_planner_existsUnique
#print axioms Miao.SearchAndMatching.dm_cd_hosios_iff
#print axioms Miao.SearchAndMatching.dm_cd_hosios_compare
#print axioms Miao.SearchAndMatching.dm_hosios_misprint
#print axioms Miao.SearchAndMatching.dm_hhCons
#print axioms Miao.SearchAndMatching.dm_Ex1HHOptimal
#print axioms Miao.SearchAndMatching.dm_ex1_share_euler
#print axioms Miao.SearchAndMatching.dm_ex1_hhOptimal_of_euler
#print axioms Miao.SearchAndMatching.dm_ex1_price
#print axioms Miao.SearchAndMatching.dm_ex1Div
#print axioms Miao.SearchAndMatching.dm_Ex1Feasible
#print axioms Miao.SearchAndMatching.dm_Ex1FirmOptimal
#print axioms Miao.SearchAndMatching.dm_ex1_capital_euler
#print axioms Miao.SearchAndMatching.dm_ex1_job_creation
#print axioms Miao.SearchAndMatching.dm_ex1_wage
#print axioms Miao.SearchAndMatching.dm_Ex1IsSearchEqm
#print axioms Miao.SearchAndMatching.dm_ex1_FK
#print axioms Miao.SearchAndMatching.dm_ex1_FN
#print axioms Miao.SearchAndMatching.dm_ex1_kstar
#print axioms Miao.SearchAndMatching.dm_ex1_kstar_unique
#print axioms Miao.SearchAndMatching.dm_ex1_steady
#print axioms Miao.SearchAndMatching.dm_ex1_steady_isSearchEqm
#print axioms Miao.SearchAndMatching.dm_ex1_searchEqm_exists
#print axioms Miao.SearchAndMatching.dm_mpLag
#print axioms Miao.SearchAndMatching.dm_uf_hasDerivAt
#print axioms Miao.SearchAndMatching.dm_mp_foc_v
#print axioms Miao.SearchAndMatching.dm_mp_foc_z
#print axioms Miao.SearchAndMatching.dm_mp_foc_E
#print axioms Miao.SearchAndMatching.ex_18_2
#print axioms Miao.SearchAndMatching.ex_18_2_efficiency
#print axioms Miao.SearchAndMatching.dm_mp_exp_dist
#print axioms Miao.SearchAndMatching.jd_nash_le
#print axioms Miao.SearchAndMatching.jd_nash_eq_iff
#print axioms Miao.SearchAndMatching.jd_nash_iff
#print axioms Miao.SearchAndMatching.jd_foc
#print axioms Miao.SearchAndMatching.jd_envelope
#print axioms Miao.SearchAndMatching.jd_partial_homog_one
#print axioms Miao.SearchAndMatching.jd_partial_homog_two
#print axioms Miao.SearchAndMatching.jd_affine_sol
#print axioms Miao.SearchAndMatching.jd_affine_antitone
#print axioms Miao.SearchAndMatching.jd_affine_tendsto
#print axioms Miao.SearchAndMatching.jd_Phi
#print axioms Miao.SearchAndMatching.jd_G
#print axioms Miao.SearchAndMatching.jd_one_sub_G
#print axioms Miao.SearchAndMatching.jd_G_mono
#print axioms Miao.SearchAndMatching.jd_G_mem
#print axioms Miao.SearchAndMatching.jd_Phi_integrable
#print axioms Miao.SearchAndMatching.jd_Phi_nonneg
#print axioms Miao.SearchAndMatching.jd_Phi_eq_setIntegral
#print axioms Miao.SearchAndMatching.jd_Phi_antitone
#print axioms Miao.SearchAndMatching.jd_Phi_sub_le
#print axioms Miao.SearchAndMatching.jd_Phi_abs_sub_le
#print axioms Miao.SearchAndMatching.jd_Phi_continuous
#print axioms Miao.SearchAndMatching.jd_Phi_gap
#print axioms Miao.SearchAndMatching.jd_Phi_pos_iff
#print axioms Miao.SearchAndMatching.jd_Phi_pos_iff_real
#print axioms Miao.SearchAndMatching.jd_Phi_strictAnti_of_pos
#print axioms Miao.SearchAndMatching.jd_Phi_of_nonpos
#print axioms Miao.SearchAndMatching.jd_Phi_tendsto_atTop
#print axioms Miao.SearchAndMatching.jd_Phi_hasDerivAt
#print axioms Miao.SearchAndMatching.jd_sepRate
#print axioms Miao.SearchAndMatching.jd_sepRate_mem
#print axioms Miao.SearchAndMatching.jd_sepRate_mono
#print axioms Miao.SearchAndMatching.eq_18_43
#print axioms Miao.SearchAndMatching.jd_filled_job_cutoff_form
#print axioms Miao.SearchAndMatching.eq_18_31
#print axioms Miao.SearchAndMatching.eq_18_32
#print axioms Miao.SearchAndMatching.eq_18_33
#print axioms Miao.SearchAndMatching.eq_18_34
#print axioms Miao.SearchAndMatching.eq_18_37_38
#print axioms Miao.SearchAndMatching.jd_worker_surplus
#print axioms Miao.SearchAndMatching.eq_18_39
#print axioms Miao.SearchAndMatching.jd_wage_intermediate
#print axioms Miao.SearchAndMatching.eq_18_40
#print axioms Miao.SearchAndMatching.jd_JF_linear
#print axioms Miao.SearchAndMatching.jd_cutoff
#print axioms Miao.SearchAndMatching.eq_18_41
#print axioms Miao.SearchAndMatching.eq_18_42
#print axioms Miao.SearchAndMatching.jd_jdRate
#print axioms Miao.SearchAndMatching.jd_jcRate
#print axioms Miao.SearchAndMatching.jd_jc_eq_jd_of_steady
#print axioms Miao.SearchAndMatching.jd_JC
#print axioms Miao.SearchAndMatching.jd_JD
#print axioms Miao.SearchAndMatching.jd_thetaJD
#print axioms Miao.SearchAndMatching.jd_h_strictMono
#print axioms Miao.SearchAndMatching.jd_JD_iff
#print axioms Miao.SearchAndMatching.jd_thetaJD_strictMono
#print axioms Miao.SearchAndMatching.jd_thetaJD_continuous
#print axioms Miao.SearchAndMatching.eq_18_44
#print axioms Miao.SearchAndMatching.eq_18_45
#print axioms Miao.SearchAndMatching.jd_steady_state_unique
#print axioms Miao.SearchAndMatching.jd_steady_state_exists
#print axioms Miao.SearchAndMatching.jd_steady_state_existsUnique
#print axioms Miao.SearchAndMatching.jd_example_steady_state
#print axioms Miao.SearchAndMatching.jd_JC_kappaA_iff
#print axioms Miao.SearchAndMatching.jd_compstat_A_theta
#print axioms Miao.SearchAndMatching.jd_compstat_kappaA
#print axioms Miao.SearchAndMatching.jd_compstat_kappaA_jd
#print axioms Miao.SearchAndMatching.jd_compstat_kappaA_u
#print axioms Miao.SearchAndMatching.jd_beveridge_downward
#print axioms Miao.SearchAndMatching.jd_beveridge_shift
#print axioms Miao.SearchAndMatching.jd_transition_unemployment
#print axioms Miao.SearchAndMatching.jd_kappa_div_q_hasDerivAt
#print axioms Miao.SearchAndMatching.jd_linear_psi
#print axioms Miao.SearchAndMatching.jd_psi_abs_lt_one
#print axioms Miao.SearchAndMatching.jd_saddle
#print axioms Miao.SearchAndMatching.jd_hhObj
#print axioms Miao.SearchAndMatching.jd_hh_budget_forms
#print axioms Miao.SearchAndMatching.jd_crra_hasDerivAt
#print axioms Miao.SearchAndMatching.jd_disutility_hasDerivAt
#print axioms Miao.SearchAndMatching.jd_disutility_integral
#print axioms Miao.SearchAndMatching.jd_hh_foc_I
#print axioms Miao.SearchAndMatching.jd_hh_envelope_K
#print axioms Miao.SearchAndMatching.eq_18_49
#print axioms Miao.SearchAndMatching.jd_hh_envelope_N
#print axioms Miao.SearchAndMatching.eq_18_50
#print axioms Miao.SearchAndMatching.jd_hh_Vn
#print axioms Miao.SearchAndMatching.jd_hh_Vn_book_budget
#print axioms Miao.SearchAndMatching.jd_firmObj
#print axioms Miao.SearchAndMatching.eq_18_51
#print axioms Miao.SearchAndMatching.eq_18_52
#print axioms Miao.SearchAndMatching.eq_18_53
#print axioms Miao.SearchAndMatching.eq_18_54
#print axioms Miao.SearchAndMatching.eq_18_55
#print axioms Miao.SearchAndMatching.jd_firm_Jn
#print axioms Miao.SearchAndMatching.jd_nash_18_3
#print axioms Miao.SearchAndMatching.eq_18_56
#print axioms Miao.SearchAndMatching.jd_capital_ratio_indep
#print axioms Miao.SearchAndMatching.jd_wage_indep
#print axioms Miao.SearchAndMatching.jd_aggregate_output
#print axioms Miao.SearchAndMatching.jd_employment_consistency
#print axioms Miao.SearchAndMatching.jd_resource_constraint
#print axioms Miao.SearchAndMatching.ex_18_3_theta
#print axioms Miao.SearchAndMatching.ex_18_3_reservation
#print axioms Miao.SearchAndMatching.ex_18_3_reservation_mono
#print axioms Miao.SearchAndMatching.ex_18_3_unemployment
#print axioms Miao.SearchAndMatching.jd_mps_example
#print axioms Miao.SearchAndMatching.jd_plannerObj
#print axioms Miao.SearchAndMatching.ex_18_4_foc_K
#print axioms Miao.SearchAndMatching.ex_18_4_foc_v
#print axioms Miao.SearchAndMatching.ex_18_4_envelope_K
#print axioms Miao.SearchAndMatching.ex_18_4_euler
#print axioms Miao.SearchAndMatching.ex_18_4_envelope_N
#print axioms Miao.SearchAndMatching.ex_18_4_surplus
#print axioms Miao.SearchAndMatching.jd_matching_partial_v
#print axioms Miao.SearchAndMatching.jd_matching_partial_u
#print axioms Miao.SearchAndMatching.ex_18_4_gap
#print axioms Miao.SearchAndMatching.ex_18_4_hosios
#print axioms Miao.SearchAndMatching.ex_18_4_surplus_hosios
#print axioms Miao.SearchAndMatching.ex_18_4_ss_decentralised
#print axioms Miao.SearchAndMatching.ex_18_4_ss_planner
#print axioms Miao.SearchAndMatching.ex_18_4_ss_hosios
#print axioms Miao.SearchAndMatching.ex_18_5_rental
#print axioms Miao.SearchAndMatching.ex_18_5_employment
#print axioms Miao.SearchAndMatching.ex_18_5_rho
#print axioms Miao.SearchAndMatching.ex_18_5_kappa
#print axioms Miao.SearchAndMatching.ex_18_5_consumption

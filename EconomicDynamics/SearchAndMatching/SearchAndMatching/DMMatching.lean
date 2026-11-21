/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MeanInequalities

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

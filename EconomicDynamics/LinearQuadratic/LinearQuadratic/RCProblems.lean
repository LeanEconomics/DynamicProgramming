/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Bounds.Basic

/-!
# The constraint and multiplier problems

Miao, §9.6, pp. 318–320 ("Two Robust Control Problems" and the start of "Recursive
Formulation"). The problems are stated abstractly: a control `u` (a plan `{u_t}`) and a belief
distortion `m` (a sequence `{m_{t+1}}`) give the expected discounted reward `J u m` under the
distorted belief, and the distortion has discounted entropy `ent m ≥ 0` (the left side of
(9.45)), with `ent m₀ = 0` for the reference model `m₀ = 1`.

* The constraint problem: `max_u min_{ent m ≤ η} J u m`; the multiplier problem:
  `max_u min_m (J u m + θ ent m)` (`rcMultObj`).
* `rc_lagrange` (p. 319, "θ as the Lagrange multiplier associated with (9.45)"): a minimiser of the
  multiplier objective satisfying complementary slackness `θ(ent m* − η) = 0` solves the
  constraint problem, with value `min(J + θ ent) − θη`; `rc_weak_duality`: for every `θ ≥ 0`,
  `min_m(J + θ ent) − θη` is a lower bound for the constrained value.
* `rc_mult_mono`, `rc_mult_le_ref` (p. 319): the multiplier value increases with `θ` (a smaller
  `θ` means more concern about misspecification), and never exceeds the reference value.
* `rc_mult_tendsto` (p. 319, "when `θ → ∞` the multiplier problem converges to the standard control
  problem under `P`"): under a Pinsker-type bound `|J u m − J u m₀| ≤ c√(ent m)` the inner value is
  within `c²/(4θ)` of `J u m₀`, and the robust value converges to the standard one.
* `rc_bellman_scale`, `rc_bellman_divide` (p. 320): the conjecture `W(M, x) = MV(x)`: for `M > 0`,
  `MV(x) = max_u min_m M·g(u, m)` iff `V(x) = max_u min_m g(u, m)`; `rc_min_add` pulls the reward
  `r(x, u)`, which does not depend on `m`, out of the minimisation.

Departure: the convergence as `θ → ∞` needs some continuity of `J` in the distortion; we take the
bound `|J u m − J u m₀| ≤ c√(ent m)` (Pinsker's inequality for bounded rewards) as a hypothesis.
-/

open Filter Topology

namespace Miao.LinearQuadratic

variable {Ctrl Dist : Type*}

/-- The multiplier objective `J(u, m) + θ ent(m)` (Miao, p. 318). -/
def rcMultObj (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) (θ : ℝ) (u : Ctrl) (m : Dist) : ℝ :=
  J u m + θ * ent m

/-- Miao, p. 319: `θ` as the Lagrange multiplier of (9.45). If `m*` minimises
`J(u, ·) + θ ent` with `θ ≥ 0`, `ent m* ≤ η` and `θ(ent m* − η) = 0`, then `m*` minimises
`J(u, ·)` subject to the entropy constraint `ent m ≤ η`, and the constrained value is the
multiplier value minus `θη`. -/
theorem rc_lagrange (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) {θ η : ℝ} (hθ : 0 ≤ θ) (u : Ctrl)
    {mstar : Dist} (hmin : ∀ m, rcMultObj J ent θ u mstar ≤ rcMultObj J ent θ u m)
    (hfeas : ent mstar ≤ η) (hcs : θ * (ent mstar - η) = 0) :
    IsLeast ((J u) '' {m | ent m ≤ η}) (J u mstar) ∧
      J u mstar = rcMultObj J ent θ u mstar - θ * η := by
  have hval : J u mstar = rcMultObj J ent θ u mstar - θ * η := by
    simp only [rcMultObj]; linarith
  refine ⟨⟨⟨mstar, hfeas, rfl⟩, ?_⟩, hval⟩
  rintro _ ⟨m, hm, rfl⟩
  have h1 := hmin m
  simp only [rcMultObj] at h1
  have h2 : θ * ent m ≤ θ * η := mul_le_mul_of_nonneg_left hm hθ
  nlinarith

/-- Weak duality (Miao, p. 319): for `θ ≥ 0`, a lower bound `v` of the multiplier objective gives
the lower bound `v − θη` on `J(u, m)` over the constraint set `ent m ≤ η`. -/
theorem rc_weak_duality (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) {θ η v : ℝ} (hθ : 0 ≤ θ)
    (u : Ctrl) (hv : ∀ m, v ≤ rcMultObj J ent θ u m) {m : Dist} (hm : ent m ≤ η) :
    v - θ * η ≤ J u m := by
  have h1 := hv m
  simp only [rcMultObj] at h1
  have h2 : θ * ent m ≤ θ * η := mul_le_mul_of_nonneg_left hm hθ
  linarith

/-- Miao, p. 319: with nonnegative entropy the multiplier value is increasing in `θ`. -/
theorem rc_mult_mono (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) (hent : ∀ m, 0 ≤ ent m) (u : Ctrl)
    {θ θ' v v' : ℝ} (hθ : θ ≤ θ') (hv : IsLeast (Set.range (rcMultObj J ent θ u)) v)
    (hv' : IsLeast (Set.range (rcMultObj J ent θ' u)) v') : v ≤ v' := by
  obtain ⟨m, hm⟩ := hv'.1
  rw [← hm]
  refine (hv.2 ⟨m, rfl⟩).trans ?_
  simp only [rcMultObj]
  nlinarith [hent m]

/-- Miao, p. 319: the multiplier value never exceeds the value under the reference model `m₀`
(which has zero entropy). -/
theorem rc_mult_le_ref (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) {m₀ : Dist} (h0 : ent m₀ = 0)
    (u : Ctrl) {θ v : ℝ} (hv : IsLeast (Set.range (rcMultObj J ent θ u)) v) : v ≤ J u m₀ := by
  have := hv.2 ⟨m₀, rfl⟩
  simpa [rcMultObj, h0] using this

/-- The key inequality for `θ → ∞`: `θe − c√e ≥ −c²/(4θ)`. -/
theorem rc_sqrt_penalty {θ c e : ℝ} (hθ : 0 < θ) (he : 0 ≤ e) :
    -(c ^ 2 / (4 * θ)) ≤ θ * e - c * Real.sqrt e := by
  have hs := Real.sq_sqrt he
  have h : 0 ≤ θ * (Real.sqrt e - c / (2 * θ)) ^ 2 := by positivity
  have e1 : θ * (Real.sqrt e - c / (2 * θ)) ^ 2 =
      θ * (Real.sqrt e) ^ 2 - c * Real.sqrt e + c ^ 2 / (4 * θ) := by
    field_simp
    ring
  rw [e1, hs] at h
  linarith

/-- Miao, p. 319: under the Pinsker-type bound `|J u m − J u m₀| ≤ c√(ent m)`, every multiplier
objective value is at least `J u m₀ − c²/(4θ)`. -/
theorem rc_mult_lower (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) (hent : ∀ m, 0 ≤ ent m)
    {m₀ : Dist} {c θ : ℝ} (hθ : 0 < θ)
    (hpin : ∀ u m, |J u m - J u m₀| ≤ c * Real.sqrt (ent m)) (u : Ctrl) (m : Dist) :
    J u m₀ - c ^ 2 / (4 * θ) ≤ rcMultObj J ent θ u m := by
  have h1 := (abs_le.1 (hpin u m)).1
  have h2 := rc_sqrt_penalty (c := c) hθ (hent m)
  simp only [rcMultObj]
  linarith

/-- Miao, p. 319: as `θ → ∞` the multiplier problem converges to the standard control problem.
Under the Pinsker-type bound, if `W θ` is the robust value `max_u min_m (J + θ ent)` and `W₀` the
standard value `max_u J(u, m₀)`, then `W₀ − c²/(4θ) ≤ W θ ≤ W₀` and `W θ → W₀`. -/
theorem rc_mult_tendsto (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) (hent : ∀ m, 0 ≤ ent m)
    {m₀ : Dist} (h0 : ent m₀ = 0) {c : ℝ}
    (hpin : ∀ u m, |J u m - J u m₀| ≤ c * Real.sqrt (ent m))
    (v : ℝ → Ctrl → ℝ) (hv : ∀ θ, 0 < θ → ∀ u, IsLeast (Set.range (rcMultObj J ent θ u)) (v θ u))
    (W : ℝ → ℝ) (hW : ∀ θ, 0 < θ → IsGreatest (Set.range (v θ)) (W θ)) {W₀ : ℝ}
    (hW₀ : IsGreatest (Set.range fun u => J u m₀) W₀) :
    (∀ θ, 0 < θ → W₀ - c ^ 2 / (4 * θ) ≤ W θ ∧ W θ ≤ W₀) ∧ Tendsto W atTop (𝓝 W₀) := by
  have hb : ∀ θ, 0 < θ → W₀ - c ^ 2 / (4 * θ) ≤ W θ ∧ W θ ≤ W₀ := by
    intro θ hθ
    obtain ⟨u₀, hu₀⟩ := hW₀.1
    refine ⟨?_, ?_⟩
    · have hlow : J u₀ m₀ - c ^ 2 / (4 * θ) ≤ v θ u₀ := by
        obtain ⟨m, hm⟩ := (hv θ hθ u₀).1
        rw [← hm]
        exact rc_mult_lower J ent hent hθ hpin u₀ m
      have := (hW θ hθ).2 ⟨u₀, rfl⟩
      simp only at hu₀
      linarith
    · obtain ⟨u, hu⟩ := (hW θ hθ).1
      rw [← hu]
      exact (rc_mult_le_ref J ent h0 u (hv θ hθ u)).trans (hW₀.2 ⟨u, rfl⟩)
  refine ⟨hb, ?_⟩
  have hlim : Tendsto (fun θ : ℝ => W₀ - c ^ 2 / (4 * θ)) atTop (𝓝 W₀) := by
    have h : Tendsto (fun θ : ℝ => c ^ 2 / (4 * θ)) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (c ^ 2 / 4)
      rw [mul_zero] at this
      refine this.congr fun θ => ?_
      rw [div_mul_eq_div_div, div_eq_mul_inv (c ^ 2 / 4)]
    simpa using (tendsto_const_nhds (x := W₀)).sub h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with θ hθ using (hb θ hθ).1
  · filter_upwards [eventually_gt_atTop 0] with θ hθ using (hb θ hθ).2

/-- Miao, p. 320: the conjecture `W(M, x) = MV(x)`. If `w u = min_m g(u, m)` and
`V = max_u w u`, then for `M > 0`, `M·w u = min_m M·g(u, m)` and `MV = max_u M·w u`. -/
theorem rc_bellman_scale {g : Ctrl → Dist → ℝ} {w : Ctrl → ℝ} {V M : ℝ} (hM : 0 < M)
    (hw : ∀ u, IsLeast (Set.range (g u)) (w u)) (hV : IsGreatest (Set.range w) V) :
    (∀ u, IsLeast (Set.range fun m => M * g u m) (M * w u)) ∧
      IsGreatest (Set.range fun u => M * w u) (M * V) := by
  refine ⟨fun u => ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := (hw u).1
    exact ⟨m, by simp only; rw [hm]⟩
  · rintro _ ⟨m, rfl⟩
    exact mul_le_mul_of_nonneg_left ((hw u).2 ⟨m, rfl⟩) hM.le
  · obtain ⟨u, hu⟩ := hV.1
    exact ⟨u, by simp only; rw [hu]⟩
  · rintro _ ⟨u, rfl⟩
    exact mul_le_mul_of_nonneg_left (hV.2 ⟨u, rfl⟩) hM.le

/-- Miao, p. 320: dividing the Bellman equation for `W(M, x) = MV(x)` by `M > 0`. -/
theorem rc_bellman_divide {g : Ctrl → Dist → ℝ} {w : Ctrl → ℝ} {V M : ℝ} (hM : 0 < M)
    (hw : ∀ u, IsLeast (Set.range fun m => M * g u m) (M * w u))
    (hV : IsGreatest (Set.range fun u => M * w u) (M * V)) :
    (∀ u, IsLeast (Set.range (g u)) (w u)) ∧ IsGreatest (Set.range w) V := by
  have h := rc_bellman_scale (inv_pos.2 hM) hw hV
  simp only [← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul] at h
  exact h

/-- Miao, p. 320: the reward `r(x, u)` does not depend on the distortion, so
`min_m (r + βh(m)) = r + β min_m h(m)` for `β > 0`. -/
theorem rc_min_add {h : Dist → ℝ} {a r β : ℝ} (hβ : 0 < β) :
    IsLeast (Set.range h) a ↔ IsLeast (Set.range fun m => r + β * h m) (r + β * a) := by
  constructor
  · rintro ⟨⟨m, hm⟩, hle⟩
    refine ⟨⟨m, by simp only; rw [hm]⟩, ?_⟩
    rintro _ ⟨m', rfl⟩
    have := hle ⟨m', rfl⟩
    simp only
    nlinarith
  · rintro ⟨⟨m, hm⟩, hle⟩
    refine ⟨⟨m, ?_⟩, ?_⟩
    · simp only at hm
      have : β * h m = β * a := by linarith
      exact mul_left_cancel₀ hβ.ne' this
    · rintro _ ⟨m', rfl⟩
      have := hle ⟨m', rfl⟩
      simp only at this
      nlinarith

end Miao.LinearQuadratic

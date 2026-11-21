/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.DMSteadyState
import Mathlib.Analysis.SpecificLimits.Basic

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

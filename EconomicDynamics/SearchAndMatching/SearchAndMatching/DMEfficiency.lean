/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.DMSteadyState

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

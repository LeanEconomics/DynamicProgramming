/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFrictionalLaborMarkets.DMP
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

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

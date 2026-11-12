/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFrictionalLaborMarkets.DMP
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

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

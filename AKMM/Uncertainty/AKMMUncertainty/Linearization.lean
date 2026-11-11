/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.PolicySlope
import RationalExpectations.VARMoments
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Solving the stochastic growth model by linearisation

AKMM, §7.3.4, (7.17)–(7.19), pp. 201–203. Steady-state values: `f_K, f_A, f_KK, f_KA` are the
derivatives of `f(A, K)` at `(Ā, K̄)`, `q = u′/u″` at `C̄`, `g_K, g_A` the derivatives of the
policy; TFP follows `Â′ = ρÂ + ε′`.

* Certainty equivalence (p. 202): the expectation of the linearised right-hand side over any
  mean-zero shock is its value at `ε′ = 0`, whatever the shock's variance
  (`lin_certainty_equivalence`).
* Matching coefficients (p. 202): the linearised Euler equation holds for all `(K̂, Â)` iff the
  `K̂`- and `Â`-coefficient equations hold (`lin_match`).
* The `K̂` equation is what differentiating the functional Euler equation at the steady state
  gives in the deterministic model (`lin_K_eq_of_policy`, from Chapter 4's (4.29)).
* **(7.17)**: with `βf_K = 1` the `K̂` equation is the quadratic
  `g_K² − (1 + β⁻¹ + qf_KK/f_K)g_K + β⁻¹ = 0` (`eq_7_17`); it is `β⁻¹ > 0` at `0` and
  `−qf_KK/f_K < 0` at `1` (`eq_7_17_values`); its roots are Chapter 4's `slopeRoot β Θ ∈ (0, 1)`
  and `slopeRootOther β Θ > 1` with `Θ = β²u′f_KK/u″`, so the stable root agrees with Chapter 4's
  `a₁` (`eq_7_17_roots`).
* The `Â` equation gives the printed formula for `g_A` (`lin_gA`), whose denominator is positive at
  the stable root for `ρ ≤ 1` (`lin_gA_denominator_pos`).
* (7.18)–(7.19) as the system `x_{t+1} = Mx_t + bε_{t+1}` with `M = [g_K g_A; 0 ρ]`
  (`eq_7_18_7_19`), stable when `|g_K|, |ρ| < 1` (`lin_system_stable`), so `LinearSDE` applies.

Departure: the first display of the linearised (7.16) (p. 202) omits the factor `β` of the second;
the equations are stated with `β`.
-/

namespace AKMM.Uncertainty

open Filter Topology Matrix Polynomial Miao.RationalExpectations AKMM.DynamicOptimization

/-- **AKMM, p. 202: certainty equivalence.** If the shock `e` has probabilities `p` with mean
zero, the expectation of a linear function `c + d(ρÂ + e)` of `Â′ = ρÂ + e` is its value at
`Â′ = ρÂ`: only expected values matter, and the shock's variance does not. -/
theorem lin_certainty_equivalence {ι : Type*} (s : Finset ι) {p e : ι → ℝ}
    (hp : ∑ i ∈ s, p i = 1) (he : ∑ i ∈ s, p i * e i = 0) (c d ρ Ahat : ℝ) :
    ∑ i ∈ s, p i * (c + d * (ρ * Ahat + e i)) = c + d * (ρ * Ahat) := by
  have : ∀ i, p i * (c + d * (ρ * Ahat + e i)) = (c + d * (ρ * Ahat)) * p i + d * (p i * e i) :=
    fun i => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, he, hp]
  ring

/-- AKMM, p. 202: the `K̂`-coefficient equation
`f_K − g_K = β[f_K(f_K − g_K)g_K + qf_KKg_K]`. -/
def lin_Keq (β fK fKK q gK : ℝ) : Prop := fK - gK = β * (fK * (fK - gK) * gK + q * fKK * gK)

/-- AKMM, p. 203: the `Â`-coefficient equation
`f_A − g_A = β[f_K((f_K − g_K)g_A + (f_A − g_A)ρ) + q(f_KKg_A + f_KAρ)]`. -/
def lin_Aeq (β ρ fK fA fKK fKA q gK gA : ℝ) : Prop :=
  fA - gA = β * (fK * ((fK - gK) * gA + (fA - gA) * ρ) + q * (fKK * gA + fKA * ρ))

/-- **AKMM, p. 202: matching coefficients.** The linearised Euler equation (after certainty
equivalence)
`(f_K − g_K)K̂ + (f_A − g_A)Â = β[f_K((f_K − g_K)(g_KK̂ + g_AÂ) + (f_A − g_A)ρÂ)
+ q(f_KK(g_KK̂ + g_AÂ) + f_KAρÂ)]` holds for all `K̂, Â` iff the `K̂` and `Â` equations hold. -/
theorem lin_match (β ρ fK fA fKK fKA q gK gA : ℝ) :
    (∀ Khat Ahat : ℝ, (fK - gK) * Khat + (fA - gA) * Ahat =
      β * (fK * ((fK - gK) * (gK * Khat + gA * Ahat) + (fA - gA) * (ρ * Ahat)) +
        q * (fKK * (gK * Khat + gA * Ahat) + fKA * (ρ * Ahat)))) ↔
      lin_Keq β fK fKK q gK ∧ lin_Aeq β ρ fK fA fKK fKA q gK gA := by
  constructor
  · intro h
    have h1 := h 1 0
    have h2 := h 0 1
    refine ⟨?_, ?_⟩ <;> simp only [lin_Keq, lin_Aeq] <;> linarith
  · rintro ⟨h1, h2⟩ Khat Ahat
    simp only [lin_Keq, lin_Aeq] at h1 h2
    linear_combination Khat * h1 + Ahat * h2

/-- AKMM, p. 202: the `K̂` equation is the derivative of the functional Euler equation at the
steady state. In the deterministic model (`A = Ā`), if `g = g(Ā, ·)` is differentiable at `K̄`
with slope `g_K`, `h = f(Ā, ·)` has `h′(K̄) = f_K`, `h″(K̄) = f_KK`, `βf_K = 1`, `u″(C̄) ≠ 0`,
and (7.16) holds near `K̄`, then `g_K` satisfies the `K̂` equation with `q = u′(C̄)/u″(C̄)`
(Chapter 4's (4.29)). -/
theorem lin_K_eq_of_policy {u' h h' g : ℝ → ℝ} {β Kbar gK u2 fKK : ℝ} (hβ : 0 < β)
    (hss : g Kbar = Kbar) (hg : HasDerivAt g gK Kbar) (hu' : HasDerivAt u' u2 (h Kbar - Kbar))
    (hh : HasDerivAt h (h' Kbar) Kbar) (hh' : HasDerivAt h' fKK Kbar)
    (hfK : β * h' Kbar = 1) (hu2 : u2 ≠ 0)
    (h716 : ∀ᶠ k in 𝓝 Kbar, u' (h k - g k) = β * u' (h (g k) - g (g k)) * h' (g k)) :
    lin_Keq β (h' Kbar) fKK (u' (h Kbar - Kbar) / u2) gK := by
  have e := eq_4_29 hβ hss hg hu' hh hh' hfK h716
  simp only [lin_Keq]
  have hfK' : h' Kbar = 1 / β := by rw [eq_inv_of_mul_eq_one_right hfK, one_div]
  have e' : 1 - β * gK = gK - β * gK ^ 2 + β ^ 2 * (u' (h Kbar - Kbar) / u2) * fKK * gK := by
    field_simp
    linear_combination e
  rw [hfK']
  calc 1 / β - gK = (1 - β * gK) / β := by field_simp
    _ = (gK - β * gK ^ 2 + β ^ 2 * (u' (h Kbar - Kbar) / u2) * fKK * gK) / β := by rw [e']
    _ = _ := by field_simp

/-- **AKMM, (7.17), p. 203.** With `βf_K = 1` (the steady-state Euler equation) the `K̂` equation
is `g_K² − (1 + β⁻¹ + qf_KK/f_K)g_K + β⁻¹ = 0`. -/
theorem eq_7_17 {β fK fKK q gK : ℝ} (hβ : β ≠ 0) (hfK : β * fK = 1) :
    lin_Keq β fK fKK q gK ↔ gK ^ 2 - (1 + β⁻¹ + q * fKK / fK) * gK + β⁻¹ = 0 := by
  have hf : fK = β⁻¹ := eq_inv_of_mul_eq_one_right hfK
  simp only [lin_Keq]
  subst hf
  constructor <;> intro h
  · field_simp at h ⊢; linarith
  · field_simp at h ⊢; linarith

/-- AKMM, p. 203: the quadratic of (7.17) is `β⁻¹ > 0` at `g_K = 0` and `−qf_KK/f_K` at
`g_K = 1`, which is negative when `u′ > 0`, `u″ < 0`, `f_K > 0`, `f_KK < 0`. -/
theorem eq_7_17_values {β fK fKK u1 u2 : ℝ} (hβ : 0 < β) (hu1 : 0 < u1) (hu2 : u2 < 0)
    (hfK : 0 < fK) (hfKK : fKK < 0) :
    (0 : ℝ) ^ 2 - (1 + β⁻¹ + u1 / u2 * fKK / fK) * 0 + β⁻¹ = β⁻¹ ∧ 0 < β⁻¹ ∧
      (1 : ℝ) ^ 2 - (1 + β⁻¹ + u1 / u2 * fKK / fK) * 1 + β⁻¹ = -(u1 / u2 * fKK / fK) ∧
      -(u1 / u2 * fKK / fK) < 0 := by
  refine ⟨by ring, inv_pos.2 hβ, by ring, ?_⟩
  have : 0 < u1 / u2 * fKK / fK :=
    div_pos (mul_pos_of_neg_of_neg (div_neg_of_pos_of_neg hu1 hu2) hfKK) hfK
  linarith

/-- **AKMM, p. 203: (7.17) has one root in `(0, 1)` and one above `1`.** With `0 < β < 1`,
`βf_K = 1`, `u′ > 0`, `u″ < 0` and `f_KK < 0`, the `K̂` equation holds iff `g_K` is
Chapter 4's stable root `slopeRoot β Θ` or `slopeRootOther β Θ`, `Θ = β²u′f_KK/u″`, and
`0 < slopeRoot β Θ < 1 < slopeRootOther β Θ`. The relevant root is the stable one, the slope `a₁`
of Chapter 4. -/
theorem eq_7_17_roots {β fK fKK u1 u2 gK : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hfK : β * fK = 1)
    (hu1 : 0 < u1) (hu2 : u2 < 0) (hfKK : fKK < 0) :
    (lin_Keq β fK fKK (u1 / u2) gK ↔
      gK = slopeRoot β (β ^ 2 * u1 * fKK / u2) ∨ gK = slopeRootOther β (β ^ 2 * u1 * fKK / u2)) ∧
      0 < slopeRoot β (β ^ 2 * u1 * fKK / u2) ∧ slopeRoot β (β ^ 2 * u1 * fKK / u2) < 1 ∧
      1 < slopeRootOther β (β ^ 2 * u1 * fKK / u2) := by
  set Θ := β ^ 2 * u1 * fKK / u2 with hΘ
  have hΘpos : 0 < Θ :=
    div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (mul_pos (pow_pos hβ 2) hu1) hfKK) hu2
  obtain ⟨r1, r2, -⟩ := slopeRoot_isRoot hβ hΘpos.le
  obtain ⟨m0, m1, m2⟩ := slopeRoot_mem hβ hβ1 hΘpos
  refine ⟨?_, m0, m1, m2⟩
  have hfK0 : fK = β⁻¹ := eq_inv_of_mul_eq_one_right hfK
  -- the K̂ equation is the quadratic `βg² − (1 + β + Θ)g + 1 = 0`
  have hq : lin_Keq β fK fKK (u1 / u2) gK ↔ β * gK ^ 2 - (1 + β + Θ) * gK + 1 = 0 := by
    simp only [lin_Keq, hΘ, hfK0]
    have hu2' := hu2.ne
    constructor <;> intro h
    · field_simp at h ⊢; linarith
    · field_simp at h ⊢; linarith
  rw [hq]
  -- factor through the two roots
  have hsum : slopeRoot β Θ + slopeRootOther β Θ = (1 + β + Θ) / β := by
    simp only [slopeRoot, slopeRootOther]; field_simp; ring
  have hprod : slopeRoot β Θ * slopeRootOther β Θ = 1 / β := (slopeRoot_isRoot hβ hΘpos.le).2.2
  have hfac : β * gK ^ 2 - (1 + β + Θ) * gK + 1 =
      β * ((gK - slopeRoot β Θ) * (gK - slopeRootOther β Θ)) := by
    have e1 : 1 + β + Θ = β * (slopeRoot β Θ + slopeRootOther β Θ) := by
      rw [hsum]; field_simp
    have e2 : (1 : ℝ) = β * (slopeRoot β Θ * slopeRootOther β Θ) := by
      rw [hprod]; field_simp
    rw [e1]
    linear_combination e2
  rw [hfac, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hβ.ne'
    · exact h
  · intro h; exact Or.inr h

/-- **AKMM, p. 203: the formula for `g_A`.** With `βf_K = 1` and
`D = f_K − g_K + 1 − ρ + qf_KK/f_K ≠ 0`, the `Â` equation holds iff
`g_A = D⁻¹((1 − ρ)f_A − ρqf_KA/f_K)`. -/
theorem lin_gA {β ρ fK fA fKK fKA q gK gA : ℝ} (hβ : β ≠ 0) (hfK : β * fK = 1)
    (hD : fK - gK + 1 - ρ + q * fKK / fK ≠ 0) :
    lin_Aeq β ρ fK fA fKK fKA q gK gA ↔
      gA = (fK - gK + 1 - ρ + q * fKK / fK)⁻¹ * ((1 - ρ) * fA - ρ * q * fKA / fK) := by
  have hfK0 : fK ≠ 0 := by rintro rfl; simp at hfK
  have hb : β = fK⁻¹ := eq_inv_of_mul_eq_one_left hfK
  simp only [lin_Aeq]
  subst hb
  rw [eq_inv_mul_iff_mul_eq₀ hD]
  constructor <;> intro h
  · field_simp at h ⊢; linarith
  · field_simp at h ⊢; linarith

/-- AKMM, p. 203: at the stable root (`g_K < 1 < f_K = β⁻¹`), with `ρ ≤ 1`, `u′ > 0`,
`u″ < 0`, `f_KK < 0`, the denominator of `g_A` is positive. -/
theorem lin_gA_denominator_pos {ρ fK fKK u1 u2 gK : ℝ} (hρ : ρ ≤ 1) (hgK : gK < 1)
    (hfK : 1 < fK) (hu1 : 0 < u1) (hu2 : u2 < 0) (hfKK : fKK < 0) :
    0 < fK - gK + 1 - ρ + u1 / u2 * fKK / fK := by
  have : 0 < u1 / u2 * fKK / fK :=
    div_pos (mul_pos_of_neg_of_neg (div_neg_of_pos_of_neg hu1 hu2) hfKK) (by linarith)
  linarith

/-- The coefficient matrix of (7.18)–(7.19) in the state `(K̂, Â)`. -/
def lin_M (gK gA ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![gK, gA; 0, ρ]

/-- **AKMM, (7.18)–(7.19), p. 203.** `K′ = K̄ + g_K(K − K̄) + g_A(A − Ā)` and
`A′ = Ā + ρ(A − Ā) + ε′` are the linear stochastic difference equation
`x′ = Mx + bε′` for `x = (K − K̄, A − Ā)`, `M = [g_K g_A; 0 ρ]`, `b = (0, 1)`. -/
theorem eq_7_18_7_19 (gK gA ρ Kbar Abar K A K' A' e : ℝ) :
    (K' = Kbar + gK * (K - Kbar) + gA * (A - Abar) ∧ A' = Abar + ρ * (A - Abar) + e) ↔
      ![K' - Kbar, A' - Abar] = lin_M gK gA ρ *ᵥ ![K - Kbar, A - Abar] + e • ![0, 1] := by
  constructor
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i <;> simp [lin_M, h1, h2] <;> ring
  · intro h
    have h1 := congrFun h 0
    have h2 := congrFun h 1
    simp [lin_M] at h1 h2
    constructor <;> linarith

/-- AKMM, p. 203: if `|g_K| < 1` and `|ρ| < 1`, the system (7.18)–(7.19) is stable (both
eigenvalues `g_K, ρ` inside the unit circle), so the moments and impulse responses of
§7.1.4 (`eq_7_6`, `sde_impulse_response`) apply. -/
theorem lin_system_stable {gK gA ρ : ℝ} (hg : |gK| < 1) (hρ : |ρ| < 1) :
    IsStableMatrix ((lin_M gK gA ρ).map Complex.ofRealHom) := by
  rw [isStableMatrix_iff_roots]
  intro μ hμ
  rw [charpoly_fin_two] at hμ
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_C, IsRoot.def, eval_add, eval_sub, eval_pow, eval_X,
    eval_mul, eval_C, trace_fin_two, det_fin_two, lin_M] at hμ
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    mul_zero, sub_zero, map_add, map_mul] at hμ
  have hf : (μ - gK) * (μ - ρ) = 0 := by
    simp only [Complex.ofRealHom_eq_coe] at hμ
    linear_combination hμ
  rcases mul_eq_zero.1 hf with h | h
  · rw [sub_eq_zero.1 h, Complex.norm_real, Real.norm_eq_abs]; exact hg
  · rw [sub_eq_zero.1 h, Complex.norm_real, Real.norm_eq_abs]; exact hρ

end AKMM.Uncertainty

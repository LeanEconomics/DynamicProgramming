/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.LSInfiniteHorizon
import PartialInformation.VARMoments

/-!
# Limits, the side condition and the numerical methods of §9.3

Copied from `EconomicDynamics/LinearQuadratic` (module `LSInfiniteLimits`), namespace renamed.

Miao, §9.3, pp. 298–304.

* `ls_F_tendsto` (p. 299): `P(s) → P` gives `F(s) = F(P(s − 1)) → F(P)`.
* `ls_dIter_tendsto` (pp. 299, 302): for `β < 1`, `d(s) → d = (1 − β)⁻¹β tr(PCC')`.
* (9.10) (p. 298): `E∑βᵗ(u_t·u_t + x_t·x_t) < ∞` forces `βᵗ|x_t|² → 0` and `βᵗ|u_t|² → 0`
  (`eq_9_10_growth`); if every closed-loop path `x_{t+1} = Γx_t` satisfies the side condition
  then `√βΓ` is stable (`ls_stable_of_side_condition`), which is how (9.10) replaces
  observability or detectability in Proposition 9.3.2 (p. 301).
* Policy improvement (p. 302): the Riccati equation rewritten with `F = F(P)`
  (`ls_policy_riccati`), and the Lyapunov step
  `P_j = Q + F_j'RF_j − SF_j − F_j'S' + β(A − BF_j)'P_j(A − BF_j)` has a unique solution when the
  eigenvalues of `A − BF_j` are below `1/√β` in modulus, i.e. `√β(A − BF_j)` is stable
  (`ls_policy_lyapunov`).
* The Lagrange method (pp. 303–304): with `u_t = −Fx_t` and `λ_t = Px_t`, the first-order
  conditions `Ru_t + S'x_t + βB'E_tλ_{t+1} = 0`, `λ_t = Qx_t + Su_t + βA'E_tλ_{t+1}` hold
  (`ls_lagrange`), where `E_tλ_{t+1} = PE_tx_{t+1} = P(Ax_t + Bu_t)`; and for `V(x) = −x'Px − d`,
  `V(x + h) = V(x) − 2λ·h − h'Ph` (`ls_envelope`): the gradient of `V` is `−2λ`, not `λ` as printed.
-/

open Filter Topology Matrix

namespace Miao.PartialInformation

variable {X U E : Type*} [Fintype X] [Fintype U]

omit [Fintype U] in
/-- (9.10) (Miao, p. 298): if `∑βᵗ(u_t·u_t + x_t·x_t) < ∞` then `βᵗ x_t·x_t → 0` and
`βᵗ u_t·u_t → 0`: `x_t`, `u_t` cannot grow at a rate exceeding `1/√β`. -/
theorem eq_9_10_growth [Fintype U] {β : ℝ} (hβ : 0 ≤ β) {x : ℕ → X → ℝ} {u : ℕ → U → ℝ}
    (h : Summable fun t => β ^ t * (u t ⬝ᵥ u t + x t ⬝ᵥ x t)) :
    Tendsto (fun t => β ^ t * (x t ⬝ᵥ x t)) atTop (𝓝 0) ∧
      Tendsto (fun t => β ^ t * (u t ⬝ᵥ u t)) atTop (𝓝 0) := by
  classical
  have h0 := h.tendsto_atTop_zero
  have hx : ∀ t, 0 ≤ x t ⬝ᵥ x t := fun t => ls_dot_self_nonneg _
  have hu : ∀ t, 0 ≤ u t ⬝ᵥ u t := fun t => ls_dot_self_nonneg _
  refine ⟨squeeze_zero (fun t => mul_nonneg (pow_nonneg hβ t) (hx t)) (fun t => ?_) h0,
    squeeze_zero (fun t => mul_nonneg (pow_nonneg hβ t) (hu t)) (fun t => ?_) h0⟩
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hu t)) (pow_nonneg hβ t)
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hx t)) (pow_nonneg hβ t)

/-- Miao, p. 301: if every path of `x_{t+1} = Γx_t` satisfies the side condition
`∑βᵗx_t·x_t < ∞`, then `√βΓ` is stable. -/
theorem ls_stable_of_side_condition [DecidableEq X] {β : ℝ} (hβ : 0 ≤ β) (Γ : Matrix X X ℝ)
    (h : ∀ x : ℕ → X → ℝ, (∀ t, x (t + 1) = Γ *ᵥ x t) → Summable fun t => β ^ t * (x t ⬝ᵥ x t)) :
    ls_Stable (Real.sqrt β • Γ) := by
  rw [ls_stable_iff_tendsto]
  intro v
  have hs := h (fun t => (Γ ^ t) *ᵥ v) fun t => by rw [pow_succ', mulVec_mulVec]
  have h0 := hs.tendsto_atTop_zero
  refine ls_tendsto_zero_of_quad_posDef PosDef.one (h0.congr fun t => ?_)
  rw [one_mulVec, smul_pow, smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, ← mul_pow, Real.mul_self_sqrt hβ]

namespace LSProblem

variable [DecidableEq U] (L : LSProblem X U E)

omit [Fintype U] [DecidableEq U] in
theorem ls_G_tendsto {Pn : ℕ → Matrix X X ℝ} {P : Matrix X X ℝ} (h : Tendsto Pn atTop (𝓝 P)) :
    Tendsto (fun n => L.G (Pn n)) atTop (𝓝 (L.G P)) :=
  tendsto_const_nhds.add
    ((ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds).const_smul L.β)

omit [Fintype U] [DecidableEq U] in
theorem ls_N_tendsto {Pn : ℕ → Matrix X X ℝ} {P : Matrix X X ℝ} (h : Tendsto Pn atTop (𝓝 P)) :
    Tendsto (fun n => L.N (Pn n)) atTop (𝓝 (L.N P)) :=
  tendsto_const_nhds.add
    ((ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds).const_smul L.β)

/-- Miao, p. 299: if `P(s) → P ≥ 0` then `F(s) = F(P(s − 1)) → F = F(P)`. -/
theorem ls_F_tendsto (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {Pn : ℕ → Matrix X X ℝ}
    {P : Matrix X X ℝ} (hP : P.PosSemidef) (h : Tendsto Pn atTop (𝓝 P)) :
    Tendsto (fun n => L.F (Pn n)) atTop (𝓝 (L.F P)) :=
  ls_tendsto_mul (ls_tendsto_inv ((isUnit_iff_isUnit_det _).1 (L.G_posDef hR hP hβ).isUnit)
    (L.ls_G_tendsto h)) (L.ls_N_tendsto h)

/-- Miao, pp. 299 and 302: for `0 ≤ β < 1`, if `P(s) = Tˢ(P(0)) → P` then the constants
`d(s + 1) = β tr(P(s)CC') + βd(s)` converge to `d = (1 − β)⁻¹β tr(PCC')`. -/
theorem ls_dIter_tendsto [Fintype E] (hβ0 : 0 ≤ L.β) (hβ1 : L.β < 1) {P₀ P : Matrix X X ℝ}
    (h : Tendsto (fun s => L.T^[s] P₀) atTop (𝓝 P)) :
    Tendsto (L.dIter P₀) atTop (𝓝 ((1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ)))) := by
  set c := trace (P * L.C * L.Cᵀ)
  set dstar := (1 - L.β)⁻¹ * (L.β * c)
  set tr : ℕ → ℝ := fun s => trace (L.T^[s] P₀ * L.C * L.Cᵀ)
  have hc : Tendsto tr atTop (𝓝 c) :=
    ((Continuous.matrix_trace continuous_id).tendsto _).comp
      (ls_tendsto_mul (ls_tendsto_mul h tendsto_const_nhds) tendsto_const_nhds)
  have hfix : dstar = L.β * c + L.β * dstar := by
    have : (1 - L.β) ≠ 0 := by linarith
    simp only [dstar]
    field_simp
    ring
  have hrec : ∀ s, |L.dIter P₀ (s + 1) - dstar| ≤
      L.β * |L.dIter P₀ s - dstar| + L.β * |tr s - c| := by
    intro s
    have e : L.dIter P₀ (s + 1) - dstar = L.β * (tr s - c) + L.β * (L.dIter P₀ s - dstar) := by
      simp only [dIter, tr]
      linear_combination (-1 : ℝ) * hfix
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hβ0]
    linarith
  have hδ : Tendsto (fun s => L.β * |tr s - c|) atTop (𝓝 0) := by
    have := ((hc.sub (tendsto_const_nhds (x := c))).abs.const_mul L.β)
    simpa using this
  have he := ls_tendsto_zero_of_le_rec hβ0 hβ1 (fun s => abs_nonneg (L.dIter P₀ s - dstar))
    hrec hδ
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using he

/-- Policy improvement (Miao, p. 302): by (9.9) the Riccati equation reads
`P = Q + F'RF − SF − F'S' + β(A − BF)'P(A − BF)` with `F = F(P)`. -/
theorem ls_policy_riccati {P : Matrix X X ℝ} (hG : IsUnit (L.G P).det) :
    L.T P = L.Q + (L.F P)ᵀ * L.R * L.F P - L.S * L.F P - (L.F P)ᵀ * L.Sᵀ +
      L.β • ((L.A - L.B * L.F P)ᵀ * P * (L.A - L.B * L.F P)) := by
  rw [← L.TF_F hG, TF]
  abel

omit [DecidableEq U] in
/-- Policy improvement (Miao, pp. 302–303): if the eigenvalues of `A − BF_j` are less than
`1/√β` in modulus (`√β(A − BF_j)` stable), the Lyapunov (Sylvester) equation
`P_j = Q + F_j'RF_j − SF_j − F_j'S' + β(A − BF_j)'P_j(A − BF_j)` has a unique solution. -/
theorem ls_policy_lyapunov [DecidableEq X] [Nonempty X] (hβ : 0 ≤ L.β) (Fj : Matrix U X ℝ)
    (hst : ls_Stable (Real.sqrt L.β • (L.A - L.B * Fj))) :
    ∃ P : Matrix X X ℝ, P = L.Q + Fjᵀ * L.R * Fj - L.S * Fj - Fjᵀ * L.Sᵀ +
        L.β • ((L.A - L.B * Fj)ᵀ * P * (L.A - L.B * Fj)) ∧
      ∀ P' : Matrix X X ℝ, P' = L.Q + Fjᵀ * L.R * Fj - L.S * Fj - Fjᵀ * L.Sᵀ +
        L.β • ((L.A - L.B * Fj)ᵀ * P' * (L.A - L.B * Fj)) → P' = P := by
  set M := L.A - L.B * Fj
  set W := L.Q + Fjᵀ * L.R * Fj - L.S * Fj - Fjᵀ * L.Sᵀ
  set Φ := (Real.sqrt L.β • M)ᵀ
  have hΦ : ls_Stable Φ := (ls_stable_transpose _).2 hst
  have hmap : ∀ Y, var_lyapMap Φ W Y = W + L.β • (Mᵀ * Y * M) := by
    intro Y
    simp only [var_lyapMap, Φ, transpose_transpose, transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hβ]
    abel
  refine ⟨var_lyapSol Φ W, ?_, fun P' hP' => lyap_unique Φ hΦ W P' (by rw [hmap]; exact hP'.symm)⟩
  rw [← hmap]
  exact (lyap_fixed Φ hΦ W).symm

/-- The Lagrange method (Miao, pp. 303–304): at a fixed point `P = T(P)`, with `u = −Fx`,
`x₊ = Ax + Bu` (`= E_tx_{t+1}`) and multipliers `λ = Px`, `λ₊ = Px₊` (`= E_tλ_{t+1}`), the
first-order conditions hold: `Ru + S'x + βB'λ₊ = 0` and `λ = Qx + Su + βA'λ₊`. -/
theorem ls_lagrange {P : Matrix X X ℝ} (hG : IsUnit (L.G P).det) (hfix : L.T P = P)
    (x : X → ℝ) :
    L.R *ᵥ (-(L.F P *ᵥ x)) + L.Sᵀ *ᵥ x +
        L.β • (L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ (-(L.F P *ᵥ x))))) = 0 ∧
      P *ᵥ x = L.Q *ᵥ x + L.S *ᵥ (-(L.F P *ᵥ x)) +
        L.β • (L.Aᵀ *ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ (-(L.F P *ᵥ x))))) := by
  set y := L.F P *ᵥ x
  have hGy : L.G P *ᵥ y = L.N P *ᵥ x := by rw [mulVec_mulVec, G_mul_F _ hG]
  refine ⟨?_, ?_⟩
  · have e : L.R *ᵥ (-y) + L.Sᵀ *ᵥ x + L.β • (L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ (-y)))) =
        L.N P *ᵥ x - L.G P *ᵥ y := by
      simp only [G, N, add_mulVec, smul_mulVec, mulVec_add, mulVec_neg, smul_add, smul_neg,
        ← mulVec_mulVec]
      abel
    rw [e, hGy, sub_self]
  · conv_lhs => rw [← hfix, T_eq_sub]
    simp only [sub_mulVec, add_mulVec, smul_mulVec, mulVec_add, mulVec_neg, smul_add, smul_neg,
      ← mulVec_mulVec]
    abel

omit [Fintype U] [DecidableEq U] in
/-- The envelope condition (Miao, p. 303), corrected: for `V(x) = −x'Px − d` with symmetric `P`
and `λ = Px`, `V(x + h) = V(x) − 2λ·h − h'Ph`, so `∂V/∂x = −2λ` (the book prints
`∂V/∂x = Qλ_t + Su_t + βA'E_tλ_{t+1} = λ_t`). -/
theorem ls_envelope {P : Matrix X X ℝ} (hP : Pᵀ = P) (d : ℝ) (x h : X → ℝ) :
    -((x + h) ⬝ᵥ (P *ᵥ (x + h))) - d =
      (-(x ⬝ᵥ (P *ᵥ x)) - d) - 2 * ((P *ᵥ x) ⬝ᵥ h) - h ⬝ᵥ (P *ᵥ h) := by
  rw [SS.LQProblem.quad_add hP, dotProduct_comm (P *ᵥ x) h]
  ring

/-- Verification with the side condition (Miao, p. 298, Hansen and Sargent): if `P` is a
symmetric solution of (9.12) with `G(P) > 0` and `β ≥ 0`, then along every deterministic path
`x_{t+1} = Ax_t + Bu_t`,
`∑_{t<s}βᵗr(x_t, u_t) = x₀'Px₀ − βˢx_s'Px_s + ∑_{t<s}βᵗ(u_t + Fx_t)'G(u_t + Fx_t)`; hence every
path with `βˢx_s'Px_s → 0` and summable losses costs at least `x₀'Px₀`, and (for a positive
semidefinite joint cost matrix) the rule `u_t = −Fx_t` costs exactly `x₀'Px₀` when its path
satisfies `βˢx_s'Px_s → 0`. -/
theorem ls_verification (hJ : L.JointPSD) (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ}
    (hP : Pᵀ = P) (hG : (L.G P).PosDef) (hβ : 0 ≤ L.β) (hfix : L.T P = P) {x : ℕ → X → ℝ}
    {u : ℕ → U → ℝ} (hx : ∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ u t) :
    (∀ s, ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t) =
      x 0 ⬝ᵥ (P *ᵥ x 0) - L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s)) + ∑ t ∈ Finset.range s, L.β ^ t *
        ((u t + L.F P *ᵥ x t) ⬝ᵥ (L.G P *ᵥ (u t + L.F P *ᵥ x t)))) ∧
    (Tendsto (fun s => L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s))) atTop (𝓝 0) →
      Summable (fun t => L.β ^ t * L.loss (x t) (u t)) →
      x 0 ⬝ᵥ (P *ᵥ x 0) ≤ ∑' t, L.β ^ t * L.loss (x t) (u t)) ∧
    ((∀ t, u t = -(L.F P *ᵥ x t)) →
      Tendsto (fun s => L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s))) atTop (𝓝 0) →
      HasSum (fun t => L.β ^ t * L.loss (x t) (u t)) (x 0 ⬝ᵥ (P *ᵥ x 0))) := by
  have hu := (isUnit_iff_isUnit_det _).1 hG.isUnit
  have hid : ∀ s, ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t) =
      x 0 ⬝ᵥ (P *ᵥ x 0) - L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s)) + ∑ t ∈ Finset.range s, L.β ^ t *
        ((u t + L.F P *ᵥ x t) ⬝ᵥ (L.G P *ᵥ (u t + L.F P *ᵥ x t))) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      have hsq := L.loss_add_cont hR hP hu (x s) (u s)
      rw [hfix, ← hx s] at hsq
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ]
      linear_combination L.β ^ s * hsq
  have hnn : ∀ t, 0 ≤ L.β ^ t * ((u t + L.F P *ᵥ x t) ⬝ᵥ (L.G P *ᵥ (u t + L.F P *ᵥ x t))) :=
    fun t => mul_nonneg (pow_nonneg hβ t)
      ((SS.LQProblem.posSemidef_iff_real.1 hG.posSemidef).2 _)
  refine ⟨hid, fun hlim hs => ?_, fun hpol hlim => ?_⟩
  · have hle : ∀ s, x 0 ⬝ᵥ (P *ᵥ x 0) - L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s)) ≤
        ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t) := fun s => by
      rw [hid s]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun t _ => hnn t)
    have h1 : Tendsto (fun s => x 0 ⬝ᵥ (P *ᵥ x 0) - L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s))) atTop
        (𝓝 (x 0 ⬝ᵥ (P *ᵥ x 0))) := by simpa using tendsto_const_nhds.sub hlim
    exact le_of_tendsto_of_tendsto' h1 hs.hasSum.tendsto_sum_nat hle
  · have hz : ∀ t, L.β ^ t * ((u t + L.F P *ᵥ x t) ⬝ᵥ (L.G P *ᵥ (u t + L.F P *ᵥ x t))) = 0 :=
      fun t => by rw [hpol t, neg_add_cancel, mulVec_zero, dotProduct_zero, mul_zero]
    have h2 : ∀ s, ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t) =
        x 0 ⬝ᵥ (P *ᵥ x 0) - L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s)) := fun s => by
      rw [hid s, Finset.sum_eq_zero fun t _ => hz t, add_zero]
    have hlos : ∀ t, 0 ≤ L.β ^ t * L.loss (x t) (u t) := fun t =>
      mul_nonneg (pow_nonneg hβ t) (L.loss_nonneg hJ _ _)
    refine (hasSum_iff_tendsto_nat_of_nonneg hlos _).2 ?_
    simp only [h2]
    simpa using tendsto_const_nhds.sub hlim

end LSProblem

end Miao.PartialInformation

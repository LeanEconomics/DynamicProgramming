/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.StochasticBK
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# The New Keynesian model: Example 2.3.1 and Exercise 2.2

Copied from `EconomicDynamics/RationalExpectations` (module `NewKeynesian`), namespace renamed.

Miao, Example 2.3.1, pp. 54–55, and Exercise 2 of §2.6, pp. 82–83. The model is the Phillips
curve (2.13) `π_t = κx_t + βE_tπ_{t+1}` and the IS curve (2.14)
`x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1}) + ε^x_t`, with `κ, β, γ > 0`.

**Example 2.3.1** (exogenous rule (2.15) `i_t = ρ_ri_{t−1} + ε_t`, state `(i_{t−1}, x_t, π_t)`):
* (2.16) is derived from (2.13)–(2.15) (`eq_2_16`, an equivalence, given that `i_t` is
  `F_t`-measurable). `A⁻¹`, `W = A⁻¹B` and `A⁻¹C` are computed (`eq_2_16_W`): the printed `W`
  (whose typesetting is garbled) has the right entries
  `[[ρ_r, 0, 0], [ρ_r/γ, 1 + κ/(βγ), −1/(βγ)], [0, −κ/β, 1/β]]`.
* The eigenvalues of `W` are `ρ_r` and the roots `λ₂ ∈ (0, 1)`, `λ₁ > 1` of
  `λ² − (1 + 1/β + κ/(βγ))λ + 1/β` (`nk_lam`, `example_2_3_1_eigen`); exactly one lies outside
  the unit circle. Only `κ, β, γ > 0` and `|ρ_r| < 1` are used (`β < 1` is not needed).
* An explicit real block split with `n_s = 2`, `n_u = 1` (`example_2_3_1_split`, from the general
  saddle lemma `nk_saddle_split`); with two jump variables the Blanchard–Kahn order condition
  fails, and the stochastic Theorem 1.4.3 (`theorem_1_4_3_lt_exists_stoch`) gives
  indeterminacy: for every `F_0`-measurable `i_{−1}` and stable adapted shocks there are
  infinitely many stable solutions (`example_2_3_1_indeterminate`; in general this needs one
  nonzero `F_0`-measurable random variable `w`, e.g. a constant), in particular in the
  deterministic case (`example_2_3_1_indeterminate_det`).

**Exercise 2.2** (`i_t = δ_ππ_t + δ_xx_t + ε_t`, state `(x_t, π_t)`, both jump variables): the model
is the jump-only system `E_tX_{t+1} = WX_t + c_t` (`nk_taylor_iff`), and it has a unique stable
equilibrium for all stable adapted shocks (`nkDeterminate`) iff both eigenvalues of `W` lie
outside the unit circle (`nk_jump2_unique` via `bkS_jump_unique`; `nk_jump2_nonunique` for the
converse). With `κ, γ > 0`, `0 < β < 1`:
* **(b), exact** (`ex_2_2_b_exact`, `δ_x ≥ 0`): determinacy iff `κ(δ_π − 1) + (1 − β)δ_x > 0` or
  `κ(1 + δ_π) + (1 + β)(2γ + δ_x) < 0`; for `δ_π, δ_x ≥ 0` the second branch is impossible and
  the condition is Bullard–Mitra's `κ(δ_π − 1) + (1 − β)δ_x > 0` (`ex_2_2_b`).
* **(a), corrected** (`ex_2_2_a`, `δ_x = 0`): determinacy iff `δ > 1` or
  `δ < −1 − 2(1 + β)γ/κ`. The printed claim "`δ > 1` is necessary and sufficient" is false:
  `κ = γ = 1`, `β = 1/2`, `δ = −5` is determinate (`ex_2_2_a_printed_false`); both roots leave
  the unit circle through `−1`. The Taylor principle holds for `δ ≥ 0`
  (`ex_2_2_a_taylor_principle`).

General tools: `nk_eig2` (eigenvalues of `2 × 2` matrices), `nkBothOut` and
`nk_out_of_bothOut`/`nk_root_of_not_bothOut` (both roots of `λ² − Tλ + D` outside the unit
circle iff `D > 1, 1 ∓ T + D > 0` or `D < −1, 1 ∓ T + D < 0`, given `T² ≥ 4`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Example 2.3.1: the system (2.16) -/

/-- The matrix `A` of (2.16), Miao, p. 55; the state is `(i_{t−1}, x_t, π_t)`. -/
noncomputable def nkA (β γ : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![1] 0 !![-1 / γ; 0] !![1, 1 / γ; 0, β]

/-- The matrix `B` of (2.16), Miao, p. 55. -/
noncomputable def nkB (κ ρ : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![ρ] 0 0 !![1, 0; -κ, 1]

/-- The forcing matrix of (2.16): `(ε_t, −ε^x_t, 0)' = C(ε_t, ε^x_t)'`. -/
noncomputable def nkC : Matrix (Fin 1 ⊕ Fin 2) (Fin 2) ℝ :=
  Matrix.fromRows !![1, 0] !![0, -1; 0, 0]

/-- `A⁻¹` for (2.16). -/
noncomputable def nkAinv (β γ : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![1] 0 !![1 / γ; 0] !![1, -1 / (β * γ); 0, 1 / β]

/-- A `3 × 3` matrix with a predetermined first coordinate:
`[[ρ, 0, 0], [q, m₁₁, m₁₂], [0, m₂₁, m₂₂]]`. -/
noncomputable def nkSaddleW (ρ q m11 m12 m21 m22 : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![ρ] 0 !![q; 0] !![m11, m12; m21, m22]

/-- The matrix `W = A⁻¹B` of Example 2.3.1 (Miao, p. 55):
`[[ρ_r, 0, 0], [ρ_r/γ, 1 + κ/(βγ), −1/(βγ)], [0, −κ/β, 1/β]]`. -/
noncomputable def nkW (κ β γ ρ : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  nkSaddleW ρ (ρ / γ) (1 + κ / (β * γ)) (-1 / (β * γ)) (-κ / β) (1 / β)

/-- The forcing matrix `A⁻¹C` of the reduced form of (2.16). -/
noncomputable def nkG (γ : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 2) ℝ :=
  Matrix.fromRows !![1, 0] !![1 / γ, -1; 0, 0]

/-- The state `(i_{t−1}, x_t, π_t)` of (2.16), with `ii t = i_{t−1}`. -/
def nkState (ii x π : ℕ → V) : ℕ → Fin 1 ⊕ Fin 2 → V :=
  fun t => Sum.elim (fun _ => ii t) ![x t, π t]

/-- The shocks `(ε_t, ε^x_t)`. -/
def nkShock (ε εx : ℕ → V) : ℕ → Fin 2 → V :=
  fun t => ![ε t, εx t]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem nk_sumElim_eq_iff {a a' b b' c c' : V} :
    Sum.elim (fun _ : Fin 1 => a) ![b, c] = Sum.elim (fun _ : Fin 1 => a') ![b', c'] ↔
      a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    exact ⟨congrFun h (Sum.inl 0), congrFun h (Sum.inr 0), congrFun h (Sum.inr 1)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem nk_matAct_A (β γ : ℝ) (a b c : V) :
    matAct (nkA β γ) (Sum.elim (fun _ : Fin 1 => a) ![b, c]) =
      Sum.elim (fun _ : Fin 1 => a) ![-(γ⁻¹ • a) + (b + γ⁻¹ • c), β • c] := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [matAct, nkA, Fintype.sum_sum_type, Fin.sum_univ_two, neg_div, neg_smul]

theorem nk_matAct_B (κ ρ : ℝ) (a b c : V) :
    matAct (nkB κ ρ) (Sum.elim (fun _ : Fin 1 => a) ![b, c]) =
      Sum.elim (fun _ : Fin 1 => ρ • a) ![b, -(κ • b) + c] := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [matAct, nkB, Fintype.sum_sum_type, Fin.sum_univ_two, neg_smul]

theorem nk_matAct_C (e ex : V) :
    matAct nkC ![e, ex] = Sum.elim (fun _ : Fin 1 => e) ![-ex, 0] := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [matAct, nkC, Fin.sum_univ_two]

/-- Miao, (2.16), p. 55: given that `i_t` is `F_t`-measurable, the Phillips curve (2.13)
`π_t = κx_t + βE_tπ_{t+1}`, the IS curve (2.14) `x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1}) + ε^x_t`
and the rule (2.15) `i_t = ρ_ri_{t−1} + ε_t` hold iff `(i_{t−1}, x_t, π_t)` solves (2.16),
`AE_t(i_t, x_{t+1}, π_{t+1})' = B(i_{t−1}, x_t, π_t)' + (ε_t, −ε^x_t, 0)'`. -/
theorem eq_2_16 (E : CondExpSystem ℝ V) (κ β γ ρ : ℝ) (ii x π ε εx : ℕ → V)
    (hia : ∀ t, E.E t (ii (t + 1)) = ii (t + 1)) :
    ((∀ t, π t = κ • x t + β • E.E t (π (t + 1))) ∧
        (∀ t, x t = E.E t (x (t + 1)) - γ⁻¹ • (ii (t + 1) - E.E t (π (t + 1))) + εx t) ∧
        (∀ t, ii (t + 1) = ρ • ii t + ε t)) ↔
      IsRESolution E (nkA β γ) (nkB κ ρ) nkC (nkShock ε εx) (nkState ii x π) := by
  have hE : ∀ t, Evec E t (nkState ii x π (t + 1)) =
      Sum.elim (fun _ : Fin 1 => ii (t + 1)) ![E.E t (x (t + 1)), E.E t (π (t + 1))] := fun t => by
    funext i
    rcases i with i | i <;> fin_cases i
    · exact hia t
    · rfl
    · rfl
  have hS : ∀ (a b c : V) (a' b' c' : V), Sum.elim (fun _ : Fin 1 => a) ![b, c] +
      Sum.elim (fun _ : Fin 1 => a') ![b', c'] = Sum.elim (fun _ : Fin 1 => a + a') ![b + b',
        c + c'] := fun a b c a' b' c' => by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  have key : ∀ t, (π t = κ • x t + β • E.E t (π (t + 1)) ∧
      x t = E.E t (x (t + 1)) - γ⁻¹ • (ii (t + 1) - E.E t (π (t + 1))) + εx t ∧
      ii (t + 1) = ρ • ii t + ε t) ↔
      matAct (nkA β γ) (Evec E t (nkState ii x π (t + 1))) =
        matAct (nkB κ ρ) (nkState ii x π t) + matAct nkC (nkShock ε εx t) := fun t => by
    rw [hE t]
    simp only [nkState, nkShock]
    rw [nk_matAct_A, nk_matAct_B, nk_matAct_C, hS, nk_sumElim_eq_iff]
    constructor
    · rintro ⟨h13, h14, h15⟩
      refine ⟨h15, ?_, ?_⟩
      · linear_combination (norm := module) -h14
      · linear_combination (norm := module) -h13
    · rintro ⟨h15, h14, h13⟩
      refine ⟨?_, ?_, h15⟩
      · linear_combination (norm := module) -h13
      · linear_combination (norm := module) -h14
  unfold IsRESolution
  simp only [← key, forall_and]

/-- Miao, p. 55: the inverse of `A` in (2.16). -/
theorem nkA_mul_inv {β γ : ℝ} (hβ : β ≠ 0) (hγ : γ ≠ 0) : nkA β γ * nkAinv β γ = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [nkA, nkAinv, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    field_simp <;> ring1

/-- Miao, p. 55, checked: `A⁻¹ = [[1, 0, 0], [1/γ, 1, −1/(βγ)], [0, 0, 1/β]]`,
`W = A⁻¹B = [[ρ_r, 0, 0], [ρ_r/γ, 1 + κ/(βγ), −1/(βγ)], [0, −κ/β, 1/β]]` (the printed `W`,
whose typesetting is garbled, has exactly these entries) and the reduced-form forcing is
`A⁻¹(ε_t, −ε^x_t, 0)' = (ε_t, ε_t/γ − ε^x_t, 0)'`. -/
theorem eq_2_16_W {κ β γ ρ : ℝ} (hβ : β ≠ 0) (hγ : γ ≠ 0) :
    IsUnit (nkA β γ).det ∧ (nkA β γ)⁻¹ = nkAinv β γ ∧ (nkA β γ)⁻¹ * nkB κ ρ = nkW κ β γ ρ ∧
      (nkA β γ)⁻¹ * nkC = nkG γ := by
  have h1 := nkA_mul_inv hβ hγ
  have hinv : (nkA β γ)⁻¹ = nkAinv β γ := Matrix.inv_eq_right_inv h1
  refine ⟨Matrix.isUnit_det_of_right_inverse h1, hinv, ?_, ?_⟩ <;> rw [hinv]
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [nkAinv, nkB, nkW, nkSaddleW, Matrix.mul_apply, Fintype.sum_sum_type,
        Fin.sum_univ_two] <;>
      field_simp
  · ext (i | i) j <;> fin_cases i <;> fin_cases j <;>
      simp [nkAinv, nkC, nkG, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

/-! ### Example 2.3.1: eigenvalues and a real block split of `W` -/

/-- The `s`-rows `(1, 0, 0)`, `(0, m₂₁, λ₂ − m₁₁)` and the `u`-row `(ℓ₀, m₂₁, λ₁ − m₁₁)`,
`ℓ₀ = m₂₁q/(λ₁ − ρ)` (left eigenvector for `λ₁`), of a real block split of `nkSaddleW`. -/
noncomputable def nkSaddleP (ρ q m11 m21 l1 l2 : ℝ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![1; 0] !![0, 0; m21, l2 - m11] !![m21 * q / (l1 - ρ)] !![m21, l1 - m11]

/-- The inverse of `nkSaddleP`. -/
noncomputable def nkSaddleR (ρ q m11 m21 l1 l2 : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 2 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks !![1, 0] !![0]
    !![(l2 - m11) * (m21 * q / (l1 - ρ)) / (m21 * (l1 - l2)), (l1 - m11) / (m21 * (l1 - l2));
      -(m21 * q / (l1 - ρ)) / (l1 - l2), -1 / (l1 - l2)]
    !![-(l2 - m11) / (m21 * (l1 - l2)); 1 / (l1 - l2)]

/-- A lower triangular real `2 × 2` matrix with diagonal entries inside the unit circle is
stable. -/
theorem nk_tri_stable {a b c : ℝ} (ha : |a| < 1) (hc : |c| < 1) :
    IsStableMatrix ((!![a, 0; b, c] : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofRealHom) := by
  intro μ hμ
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have h1 := Module.End.mem_eigenspace_iff.1 hw.1
  have e0 : (a : ℂ) * w 0 = μ * w 0 := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 0
  have e1 : (b : ℂ) * w 0 + c * w 1 = μ * w 1 := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 1
  by_cases h0 : w 0 = 0
  · have h1' : w 1 ≠ 0 := fun h => hw.2 (funext fun i => by fin_cases i <;> simp [h0, h])
    rw [h0, mul_zero, zero_add] at e1
    rw [← mul_right_cancel₀ h1' e1, Complex.norm_real, Real.norm_eq_abs]
    exact hc
  · rw [← mul_right_cancel₀ h0 e0, Complex.norm_real, Real.norm_eq_abs]
    exact ha

/-- The eigenvalue of a `1 × 1` matrix `(l)` is `l`. -/
theorem nk_scalar_eig {l : ℝ} {μ : ℂ}
    (hμ : Module.End.HasEigenvalue
      (Matrix.toLin' ((!![l] : Matrix (Fin 1) (Fin 1) ℝ).map Complex.ofRealHom)) μ) :
    μ = l := by
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have h1 := Module.End.mem_eigenspace_iff.1 hw.1
  have e0 : (l : ℂ) * w 0 = μ * w 0 := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using congrFun h1 0
  have h0 : w 0 ≠ 0 := fun h => hw.2 (funext fun i => by fin_cases i; exact h)
  exact (mul_right_cancel₀ h0 e0).symm

/-- A real block split of the saddle matrix `nkSaddleW` (Miao, pp. 54–55): if `|ρ| < 1` and the
lower block has eigenvalues `λ₁ > 1` and `|λ₂| < 1` (`λ₁ + λ₂ = m₁₁ + m₂₂`,
`λ₁λ₂ = m₁₁m₂₂ − m₁₂m₂₁`) with `m₂₁ ≠ 0`, then `PWP⁻¹ = diag(J_s, J_u)` with
`J_s = [[ρ, 0], [m₂₁q, λ₂]]` (stable) and `J_u = (λ₁)`: `n_s = 2`, `n_u = 1`. -/
theorem nk_saddle_split {ρ q m11 m12 m21 m22 l1 l2 : ℝ} (hρ : |ρ| < 1) (hl1 : 1 < l1)
    (hl2 : |l2| < 1) (ha : m21 ≠ 0) (hsum : l1 + l2 = m11 + m22)
    (hprod : l1 * l2 = m11 * m22 - m12 * m21) :
    IsRealBlockSplit (nkSaddleW ρ q m11 m12 m21 m22) (nkSaddleP ρ q m11 m21 l1 l2)
      (nkSaddleR ρ q m11 m21 l1 l2) !![ρ, 0; m21 * q, l2] !![l1] := by
  have hd : l1 - l2 ≠ 0 := by
    have := (abs_lt.1 hl2).2
    linarith
  have hr : l1 - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  obtain rfl : m22 = l1 + l2 - m11 := by linarith
  obtain rfl : m12 = (m11 * (l1 + l2 - m11) - l1 * l2) / m21 := by
    field_simp
    linarith
  refine ⟨?_, ?_, ?_, nk_tri_stable hρ hl2, fun μ hμ => ?_⟩
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [nkSaddleP, nkSaddleR, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
      field_simp <;> ring1
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [nkSaddleP, nkSaddleR, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
      field_simp <;> ring1
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [nkSaddleP, nkSaddleW, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
      field_simp <;> ring1
  · rw [nk_scalar_eig hμ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hl1

/-- The eigenvalues of the saddle matrix `nkSaddleW` are `ρ`, `λ₁` and `λ₂` (Miao, p. 55). -/
theorem nk_saddle_eig {ρ q m11 m12 m21 m22 l1 l2 : ℝ} (hsum : l1 + l2 = m11 + m22)
    (hprod : l1 * l2 = m11 * m22 - m12 * m21) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue
      (Matrix.toLin' ((nkSaddleW ρ q m11 m12 m21 m22).map Complex.ofRealHom)) μ) :
    μ = ρ ∨ μ = l1 ∨ μ = l2 := by
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have h1 := Module.End.mem_eigenspace_iff.1 hw.1
  have e0 : (ρ : ℂ) * w (Sum.inl 0) = μ * w (Sum.inl 0) := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, nkSaddleW] using congrFun h1 (Sum.inl 0)
  have e1 : (q : ℂ) * w (Sum.inl 0) + (m11 * w (Sum.inr 0) + m12 * w (Sum.inr 1)) =
      μ * w (Sum.inr 0) := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, nkSaddleW] using congrFun h1 (Sum.inr 0)
  have e2 : (m21 : ℂ) * w (Sum.inr 0) + m22 * w (Sum.inr 1) = μ * w (Sum.inr 1) := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, nkSaddleW] using congrFun h1 (Sum.inr 1)
  by_cases h0 : w (Sum.inl 0) = 0
  · right
    rw [h0, mul_zero, zero_add] at e1
    have hc : (μ - l1) * (μ - l2) = μ ^ 2 - (m11 + m22) * μ + (m11 * m22 - m12 * m21) := by
      have hs : ((l1 : ℂ) + l2) = (m11 : ℂ) + m22 := by exact_mod_cast hsum
      have hp : ((l1 : ℂ) * l2) = (m11 : ℂ) * m22 - m12 * m21 := by exact_mod_cast hprod
      linear_combination (-μ) * hs + hp
    have hx : (μ ^ 2 - (m11 + m22) * μ + (m11 * m22 - m12 * m21)) * w (Sum.inr 0) = 0 := by
      linear_combination (m22 - μ) * e1 - m12 * e2
    have hy : (μ ^ 2 - (m11 + m22) * μ + (m11 * m22 - m12 * m21)) * w (Sum.inr 1) = 0 := by
      linear_combination (m11 - μ) * e2 - m21 * e1
    have hne : w (Sum.inr 0) ≠ 0 ∨ w (Sum.inr 1) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hw.2
      funext i
      rcases i with i | i <;> fin_cases i
      · exact h0
      · exact hcon.1
      · exact hcon.2
    have hchar : (μ - l1) * (μ - l2) = 0 := by
      rw [hc]
      rcases hne with h | h
      · exact (mul_eq_zero.1 hx).resolve_right h
      · exact (mul_eq_zero.1 hy).resolve_right h
    rcases mul_eq_zero.1 hchar with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  · exact Or.inl (mul_right_cancel₀ h0 e0).symm

/-- `λ₁` is an eigenvalue of the saddle matrix, with eigenvector `(0, λ₁ − m₂₂, m₂₁)`. -/
theorem nk_saddle_eig_l1 {ρ q m11 m12 m21 m22 l1 l2 : ℝ} (ha : m21 ≠ 0)
    (hsum : l1 + l2 = m11 + m22) (hprod : l1 * l2 = m11 * m22 - m12 * m21) :
    Module.End.HasEigenvalue
      (Matrix.toLin' ((nkSaddleW ρ q m11 m12 m21 m22).map Complex.ofRealHom)) l1 := by
  have h1 : l1 ^ 2 - (m11 + m22) * l1 + (m11 * m22 - m12 * m21) = 0 := by
    rw [← hsum, ← hprod]; ring
  have h1c : (l1 : ℂ) ^ 2 - (m11 + m22) * l1 + (m11 * m22 - m12 * m21) = 0 := by
    exact_mod_cast h1
  set v : Fin 1 ⊕ Fin 2 → ℂ := Sum.elim 0 ![(l1 : ℂ) - m22, m21]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    ⟨Module.End.mem_eigenspace_iff.2 ?_, fun h => ha ?_⟩
  · funext i
    rcases i with i | i <;> fin_cases i
    · simp [v, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, nkSaddleW]
    · have e : (m11 : ℂ) * (l1 - m22) + m12 * m21 = l1 * (l1 - m22) := by
        linear_combination -h1c
      simpa [v, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fin.sum_univ_two, nkSaddleW] using e
    · have e : (m21 : ℂ) * (l1 - m22) + m22 * m21 = l1 * m21 := by ring
      simpa [v, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fin.sum_univ_two, nkSaddleW] using e
  · have := congrFun h (Sum.inr 1)
    simpa [v] using this

/-- Miao, p. 55: exactly one eigenvalue of the saddle matrix lies outside the unit circle. -/
theorem nk_saddle_unstable {ρ q m11 m12 m21 m22 l1 l2 : ℝ} (hρ : |ρ| < 1) (hl1 : 1 < l1)
    (hl2 : |l2| < 1) (ha : m21 ≠ 0) (hsum : l1 + l2 = m11 + m22)
    (hprod : l1 * l2 = m11 * m22 - m12 * m21) :
    {μ : ℂ | Module.End.HasEigenvalue
      (Matrix.toLin' ((nkSaddleW ρ q m11 m12 m21 m22).map Complex.ofRealHom)) μ ∧ 1 < ‖μ‖} =
      {(l1 : ℂ)} := by
  ext μ
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hμ, h1⟩
    rcases nk_saddle_eig hsum hprod hμ with h | h | h
    · rw [h, Complex.norm_real, Real.norm_eq_abs] at h1
      linarith
    · exact h
    · rw [h, Complex.norm_real, Real.norm_eq_abs] at h1
      linarith
  · rintro rfl
    refine ⟨nk_saddle_eig_l1 ha hsum hprod, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hl1

/-! ### Example 2.3.1: the New Keynesian model is indeterminate -/

/-- The trace `1 + 1/β + κ/(βγ)` of the jump block of `W` in Example 2.3.1. -/
noncomputable def nkTr (κ β γ : ℝ) : ℝ := 1 + κ / (β * γ) + 1 / β

/-- The unstable root `λ₁ = (T + √(T² − 4/β))/2` of `λ² − Tλ + 1/β` (Example 2.3.1). -/
noncomputable def nkLam1 (κ β γ : ℝ) : ℝ := (nkTr κ β γ + √(nkTr κ β γ ^ 2 - 4 / β)) / 2

/-- The stable root `λ₂ = (T − √(T² − 4/β))/2` of `λ² − Tλ + 1/β` (Example 2.3.1). -/
noncomputable def nkLam2 (κ β γ : ℝ) : ℝ := (nkTr κ β γ - √(nkTr κ β γ ^ 2 - 4 / β)) / 2

/-- Miao, p. 55: for `κ, β, γ > 0` the jump block of `W` has eigenvalues `λ₁ > 1` and
`0 < λ₂ < 1` (`β < 1` is not needed): its characteristic polynomial `λ² − Tλ + 1/β` is
negative at `λ = 1`. -/
theorem nk_lam {κ β γ : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hγ : 0 < γ) :
    nkLam1 κ β γ + nkLam2 κ β γ = (1 + κ / (β * γ)) + 1 / β ∧
      nkLam1 κ β γ * nkLam2 κ β γ = (1 + κ / (β * γ)) * (1 / β) - (-1 / (β * γ)) * (-κ / β) ∧
      0 < nkLam2 κ β γ ∧ nkLam2 κ β γ < 1 ∧ 1 < nkLam1 κ β γ := by
  have hk : 0 < κ / (β * γ) := by positivity
  have hib : 0 < 1 / β := by positivity
  have hD : 0 < nkTr κ β γ ^ 2 - 4 / β := by
    have e : nkTr κ β γ ^ 2 - 4 / β = (1 - 1 / β) ^ 2 + 2 * (1 + 1 / β) * (κ / (β * γ)) +
        (κ / (β * γ)) ^ 2 := by
      simp only [nkTr]; ring
    rw [e]
    positivity
  set s := √(nkTr κ β γ ^ 2 - 4 / β) with hs_def
  have hs : s ^ 2 = nkTr κ β γ ^ 2 - 4 / β := Real.sq_sqrt hD.le
  have hs0 : 0 < s := Real.sqrt_pos.2 hD
  have hsum : nkLam1 κ β γ + nkLam2 κ β γ = nkTr κ β γ := by
    simp only [nkLam1, nkLam2, ← hs_def]; ring
  have hprod : nkLam1 κ β γ * nkLam2 κ β γ = 1 / β := by
    simp only [nkLam1, nkLam2, ← hs_def]
    linear_combination (-1 / 4 : ℝ) * hs
  have hlt : nkLam2 κ β γ < nkLam1 κ β γ := by
    simp only [nkLam1, nkLam2, ← hs_def]; linarith
  have hT : nkTr κ β γ = 1 + κ / (β * γ) + 1 / β := rfl
  have hp1 : (1 - nkLam1 κ β γ) * (1 - nkLam2 κ β γ) = -(κ / (β * γ)) := by
    linear_combination -hsum + hprod - hT
  have h1 : 1 < nkLam1 κ β γ := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 (hlt.trans_le h).le)]
  have h2 : nkLam2 κ β γ < 1 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (sub_nonneg.2 h1.le) (sub_nonneg.2 h)]
  have h3 : 0 < nkLam2 κ β γ := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (zero_le_one.trans h1.le) h]
  refine ⟨hsum, ?_, h3, h2, h1⟩
  rw [hprod]
  field_simp
  ring

/-- **Example 2.3.1** (Miao, p. 55): a real block split of `W` with `n_s = 2` and `n_u = 1`
(stable block `[[ρ_r, 0], [−κρ_r/(βγ), λ₂]]`, unstable block `(λ₁)`). There are two jump
variables (`x_t`, `π_t`), so the order condition `n_u = n_y` of Blanchard and Kahn fails. -/
theorem example_2_3_1_split {κ β γ ρ : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hγ : 0 < γ)
    (hρ : |ρ| < 1) :
    IsRealBlockSplit (nkW κ β γ ρ)
      (nkSaddleP ρ (ρ / γ) (1 + κ / (β * γ)) (-κ / β) (nkLam1 κ β γ) (nkLam2 κ β γ))
      (nkSaddleR ρ (ρ / γ) (1 + κ / (β * γ)) (-κ / β) (nkLam1 κ β γ) (nkLam2 κ β γ))
      !![ρ, 0; -κ / β * (ρ / γ), nkLam2 κ β γ] !![nkLam1 κ β γ] ∧
      Fintype.card (Fin 1) < Fintype.card (Fin 2) := by
  obtain ⟨hsum, hprod, h3, h2, h1⟩ := nk_lam hκ hβ hγ
  refine ⟨nk_saddle_split hρ h1 (abs_lt.2 ⟨by linarith, h2⟩)
    (div_ne_zero (neg_ne_zero.2 hκ.ne') hβ.ne') hsum hprod,
    by simp⟩

/-- **Example 2.3.1** (Miao, p. 55): for `κ, β, γ > 0` and `|ρ_r| < 1`, exactly one eigenvalue of
`W` lies outside the unit circle, namely `λ₁`; the others are `ρ_r` and `λ₂ ∈ (0, 1)`. -/
theorem example_2_3_1_eigen {κ β γ ρ : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hγ : 0 < γ)
    (hρ : |ρ| < 1) :
    {μ : ℂ | Module.End.HasEigenvalue
      (Matrix.toLin' ((nkW κ β γ ρ).map Complex.ofRealHom)) μ ∧ 1 < ‖μ‖} =
      {(nkLam1 κ β γ : ℂ)} ∧
    (∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toLin' ((nkW κ β γ ρ).map Complex.ofRealHom)) μ →
        μ = ρ ∨ μ = nkLam1 κ β γ ∨ μ = nkLam2 κ β γ) ∧
    1 < nkLam1 κ β γ ∧ 0 < nkLam2 κ β γ ∧ nkLam2 κ β γ < 1 := by
  obtain ⟨hsum, hprod, h3, h2, h1⟩ := nk_lam hκ hβ hγ
  exact ⟨nk_saddle_unstable hρ h1 (abs_lt.2 ⟨by linarith, h2⟩)
    (div_ne_zero (neg_ne_zero.2 hκ.ne') hβ.ne') hsum hprod,
    fun μ hμ => nk_saddle_eig hsum hprod hμ, h1, h3, h2⟩

/-- **Example 2.3.1** (Miao, pp. 54–55): the exogenous rule `i_t = ρ_ri_{t−1} + ε_t` makes the
equilibrium indeterminate. For `κ, β, γ > 0`, `|ρ_r| < 1`, every `F_0`-measurable `i_{−1}` and
every stable adapted shock process `(ε_t, ε^x_t)`, the system (2.16) has infinitely many stable
adapted solutions with `i` predetermined and initial value `i_{−1}` (provided `V` contains a
nonzero `F_0`-measurable `w`; the extra solutions add `cλ₂ᵗw` along the stable eigenvector). -/
theorem example_2_3_1_indeterminate [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ ρ : ℝ}
    (hκ : 0 < κ) (hβ : 0 < β) (hγ : 0 < γ) (hρ : |ρ| < 1) (i₀ : V) (hi₀ : E.E 0 i₀ = i₀)
    {z : ℕ → Fin 2 → V} (hz : IsStableProc z) (hza : IsAdaptedV E z) {w : V} (hw : w ≠ 0)
    (hw0 : E.E 0 w = w) :
    {X : ℕ → Fin 1 ⊕ Fin 2 → V | IsRESolution E (nkA β γ) (nkB κ ρ) nkC z X ∧
      IsAdaptedV E X ∧ IsPredeterminedBK E (fun t => X t ∘ Sum.inl) ∧ IsStableProc X ∧
      X 0 (Sum.inl 0) = i₀}.Infinite := by
  obtain ⟨hdetA, -, hW, hG⟩ := eq_2_16_W (κ := κ) (ρ := ρ) hβ.ne' hγ.ne'
  obtain ⟨hS, hcard⟩ := example_2_3_1_split hκ hβ hγ hρ
  have hQ : (nkSaddleP ρ (ρ / γ) (1 + κ / (β * γ)) (-κ / β) (nkLam1 κ β γ)
      (nkLam2 κ β γ)).toBlocks₂₂ * !![1 / (-κ / β); 0] = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [nkSaddleP, Matrix.toBlocks_fromBlocks₂₂]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  have hinf := theorem_1_4_3_lt_exists_stoch E hS hcard _ hQ (nkG γ) hz hza (fun _ => i₀)
    (fun _ => hi₀) hw hw0
  refine hinf.mono ?_
  rintro X ⟨⟨he, ha, hp, hs⟩, hX0⟩
  refine ⟨?_, ha, hp, hs, congrFun hX0 0⟩
  rw [eq_2_11_iff E _ _ _ hdetA z X, hW, hG]
  exact he

/-- **Example 2.3.1**, deterministic case (Miao, p. 55): with `E_t = id` on `ℝ` (no
uncertainty), for every `i_{−1}` and every bounded shock sequence there are infinitely many
bounded solutions of (2.16) with initial value `i_{−1}`. -/
theorem example_2_3_1_indeterminate_det {κ β γ ρ : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hγ : 0 < γ)
    (hρ : |ρ| < 1) (i₀ : ℝ) {z : ℕ → Fin 2 → ℝ} (hz : IsStableSeq z) :
    {X : ℕ → Fin 1 ⊕ Fin 2 → ℝ | IsSolution (nkA β γ) (nkB κ ρ) nkC z X ∧ IsStableSeq X ∧
      X 0 (Sum.inl 0) = i₀}.Infinite := by
  have hz' : IsStableProc z := by
    rw [bkS_isStableProc_iff, ← isStableSeq_iff_exists_le]
    exact hz
  refine (example_2_3_1_indeterminate (bkS_trivial ℝ) hκ hβ hγ hρ i₀ rfl hz' (fun _ _ => rfl)
    one_ne_zero rfl).mono ?_
  rintro X ⟨he, ha, hp, hs, h0⟩
  have := (certainty_equivalence _ _ _ z X).1 ⟨he, ha, hp, hs⟩
  exact ⟨this.1, this.2, h0⟩

/-! ### Exercise 2.2: interest rate rules and determinacy -/

/-- Both roots of `λ² − Tλ + D` lie outside the unit circle (the Schur–Cohn conditions for the
reciprocal polynomial): `D > 1, 1 − T + D > 0, 1 + T + D > 0`, or
`D < −1, 1 − T + D < 0, 1 + T + D < 0`. -/
def nkBothOut (T D : ℝ) : Prop :=
  (1 < D ∧ 0 < 1 - T + D ∧ 0 < 1 + T + D) ∨ (D < -1 ∧ 1 - T + D < 0 ∧ 1 + T + D < 0)

/-- The eigenvalues of a real `2 × 2` matrix are roots of `μ² − (tr M)μ + det M`. -/
theorem nk_eig2 (M : Matrix (Fin 2) (Fin 2) ℝ) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (M.map Complex.ofRealHom)) μ) :
    μ ^ 2 - ((M 0 0 + M 1 1 : ℝ) : ℂ) * μ + ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ) = 0 := by
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have h1 := Module.End.mem_eigenspace_iff.1 hw.1
  have e0 : (M 0 0 : ℂ) * w 0 + M 0 1 * w 1 = μ * w 0 := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 0
  have e1 : (M 1 0 : ℂ) * w 0 + M 1 1 * w 1 = μ * w 1 := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 1
  have hx : (μ ^ 2 - ((M 0 0 + M 1 1 : ℝ) : ℂ) * μ + ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ))
      * w 0 = 0 := by
    push_cast
    linear_combination (M 1 1 - μ) * e0 - M 0 1 * e1
  have hy : (μ ^ 2 - ((M 0 0 + M 1 1 : ℝ) : ℂ) * μ + ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ))
      * w 1 = 0 := by
    push_cast
    linear_combination (M 0 0 - μ) * e1 - M 1 0 * e0
  by_cases h0 : w 0 = 0
  · have h1' : w 1 ≠ 0 := fun h => hw.2 (funext fun i => by fin_cases i <;> simp [h0, h])
    exact (mul_eq_zero.1 hy).resolve_right h1'
  · exact (mul_eq_zero.1 hx).resolve_right h0

/-- Under `nkBothOut T D`, every complex root of `μ² − Tμ + D` has modulus greater than one. -/
theorem nk_out_of_bothOut {T D : ℝ} (h : nkBothOut T D) {μ : ℂ}
    (hμ : μ ^ 2 - (T : ℂ) * μ + (D : ℂ) = 0) : 1 < ‖μ‖ := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, μ = a + b * Complex.I := ⟨μ.re, μ.im, (Complex.re_add_im μ).symm⟩
  have hc : (((a ^ 2 - b ^ 2 - T * a + D : ℝ) : ℂ) + ((2 * a * b - T * b : ℝ) : ℂ) * Complex.I)
      = 0 := by
    push_cast
    linear_combination hμ - b ^ 2 * Complex.I_sq
  have hr : a ^ 2 - b ^ 2 - T * a + D = 0 := by
    have := congrArg Complex.re hc
    rwa [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at this
  have hi : 2 * a * b - T * b = 0 := by
    have := congrArg Complex.im hc
    rwa [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero, zero_add, Complex.zero_im] at this
  have hn : ‖(a : ℂ) + b * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  suffices hs : 1 < a ^ 2 + b ^ 2 by
    by_contra hle
    push Not at hle
    have : ‖(a : ℂ) + b * Complex.I‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hle
    linarith
  by_cases hb : b = 0
  · subst hb
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, add_zero]
      at hr ⊢
    by_contra hle
    push Not at hle
    have ha1 : a ≤ 1 := by nlinarith
    have ha2 : -1 ≤ a := by nlinarith
    rcases h with ⟨hD, h1, h2⟩ | ⟨hD, h1, h2⟩
    · -- the other root `b' = T − a` satisfies `ab' = D`, `(1 − a)(1 − b') = 1 − T + D`
      have hp1 : (1 - a) * (1 - (T - a)) = 1 - T + D := by linear_combination -hr
      have hp2 : (1 + a) * (1 + (T - a)) = 1 + T + D := by linear_combination -hr
      have hab : a * (T - a) = D := by linear_combination -hr
      have hb1 : T - a < 1 := by
        by_contra hc
        push Not at hc
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 ha1) (sub_nonpos.2 hc)]
      have hb2 : -1 < T - a := by
        by_contra hc
        push Not at hc
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (neg_le_iff_add_nonneg.1 ha2)
          (by linarith : 1 + (T - a) ≤ 0)]
      nlinarith [mul_le_mul_of_nonneg_left (abs_le.2 ⟨ha2, ha1⟩) (abs_nonneg (T - a)),
        abs_mul a (T - a), le_abs_self (a * (T - a)), abs_lt.2 ⟨hb2, hb1⟩, abs_nonneg a]
    · have hp1 : (1 - a) * (1 - (T - a)) = 1 - T + D := by linear_combination -hr
      have hp2 : (1 + a) * (1 + (T - a)) = 1 + T + D := by linear_combination -hr
      have ha1' : a < 1 := by
        rcases ha1.lt_or_eq with h | h
        · exact h
        · subst h; linarith
      have hb1 : 1 < T - a := by
        by_contra hc
        push Not at hc
        nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hc)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a) (by linarith : (0 : ℝ) ≤ 1 + (T - a))]
  · have ha : a = T / 2 := by
      have : b * (2 * a - T) = 0 := by linear_combination hi
      have := (mul_eq_zero.1 this).resolve_left hb
      linarith
    have hbb : b ^ 2 = D - T ^ 2 / 4 := by rw [ha] at hr; linear_combination -hr
    have hb2 : 0 < b ^ 2 := by positivity
    rcases h with ⟨hD, -, -⟩ | ⟨hD, -, -⟩
    · nlinarith
    · nlinarith

/-- If `T² ≥ 4` and the roots of `λ² − Tλ + D` are not both outside the unit circle, one of them
is real and lies in `[−1, 1]`. -/
theorem nk_root_of_not_bothOut {T D : ℝ} (hT : 4 ≤ T ^ 2) (h : ¬ nkBothOut T D) :
    ∃ r : ℝ, |r| ≤ 1 ∧ r ^ 2 - T * r + D = 0 := by
  by_cases hd : T ^ 2 - 4 * D < 0
  · exact absurd (Or.inl ⟨by nlinarith, by nlinarith [sq_nonneg (2 - T)],
      by nlinarith [sq_nonneg (2 + T)]⟩) h
  push Not at hd
  set s := √(T ^ 2 - 4 * D)
  have hs : s ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt hd
  have hr1 : ((T - s) / 2) ^ 2 - T * ((T - s) / 2) + D = 0 := by linear_combination hs / 4
  have hr2 : ((T + s) / 2) ^ 2 - T * ((T + s) / 2) + D = 0 := by linear_combination hs / 4
  by_contra hall
  push Not at hall
  have h1 : 1 < |(T - s) / 2| := by
    by_contra hc; push Not at hc; exact hall _ hc hr1
  have h2 : 1 < |(T + s) / 2| := by
    by_contra hc; push Not at hc; exact hall _ hc hr2
  have hD : D = ((T - s) / 2) * ((T + s) / 2) := by linear_combination hs / 4
  have hp1 : 1 - T + D = (1 - (T - s) / 2) * (1 - (T + s) / 2) := by rw [hD]; ring
  have hp2 : 1 + T + D = (1 + (T - s) / 2) * (1 + (T + s) / 2) := by rw [hD]; ring
  apply h
  rcases lt_abs.1 h1 with h1 | h1 <;> rcases lt_abs.1 h2 with h2 | h2
  · exact Or.inl ⟨by rw [hD]; nlinarith, by rw [hp1]; nlinarith, by rw [hp2]; nlinarith⟩
  · exact Or.inr ⟨by rw [hD]; nlinarith, by rw [hp1]; nlinarith, by rw [hp2]; nlinarith⟩
  · exact Or.inr ⟨by rw [hD]; nlinarith, by rw [hp1]; nlinarith, by rw [hp2]; nlinarith⟩
  · exact Or.inl ⟨by rw [hD]; nlinarith, by rw [hp1]; nlinarith, by rw [hp2]; nlinarith⟩

/-- An eigenvector of a real `2 × 2` matrix for a real root `r` of its characteristic
polynomial: `(r − M₁₁, M₁₀)`. -/
theorem nk_eigvec2 (M : Matrix (Fin 2) (Fin 2) ℝ) {r : ℝ}
    (hr : r ^ 2 - (M 0 0 + M 1 1) * r + (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 0) :
    M *ᵥ ![r - M 1 1, M 1 0] = r • ![r - M 1 1, M 1 0] := by
  funext i
  fin_cases i
  · have e : M 0 0 * (r - M 1 1) + M 0 1 * M 1 0 = r * (r - M 1 1) := by
      linear_combination -hr
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using e
  · have e : M 1 0 * (r - M 1 1) + M 1 1 * M 1 0 = r * M 1 0 := by ring
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using e

/-- **Jump-only `2 × 2` systems, determinacy** (Miao, pp. 53–54 with `n_k = 0`): if both roots
of the characteristic polynomial of `M` lie outside the unit circle, then for every stable
adapted `c`, `E_tX_{t+1} = MX_t + c_t` has exactly one stable adapted solution. -/
theorem nk_jump2_unique [CompleteSpace V] (E : CondExpSystem ℝ V) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (h : nkBothOut (M 0 0 + M 1 1) (M 0 0 * M 1 1 - M 0 1 * M 1 0)) {c : ℕ → Fin 2 → V}
    (hc : IsStableProc c) (hca : IsAdaptedV E c) :
    ∃! X : ℕ → Fin 2 → V, (∀ t, Evec E t (X (t + 1)) = matAct M (X t) + c t) ∧
      IsAdaptedV E X ∧ IsStableProc X := by
  have hev : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toLin' (M.map Complex.ofRealHom)) μ → 1 < ‖μ‖ :=
    fun μ hμ => nk_out_of_bothOut h (nk_eig2 M hμ)
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv M hev
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  exact bkS_jump_unique E hdet hKa hc hca

/-- **Jump-only `2 × 2` systems, indeterminacy**: if `M₁₀ ≠ 0`, `(tr M)² ≥ 4` and the roots are
not both outside the unit circle, the homogeneous system `E_tX_{t+1} = MX_t` has a nonzero
stable adapted solution `rᵗvw` (`|r| ≤ 1` a real root, `v` its eigenvector, `w ≠ 0`
`F_0`-measurable). -/
theorem nk_jump2_nonunique (E : CondExpSystem ℝ V) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM10 : M 1 0 ≠ 0) (hT : 4 ≤ (M 0 0 + M 1 1) ^ 2)
    (h : ¬ nkBothOut (M 0 0 + M 1 1) (M 0 0 * M 1 1 - M 0 1 * M 1 0)) {w : V} (hw : w ≠ 0)
    (hw0 : E.E 0 w = w) :
    ∃ X : ℕ → Fin 2 → V, X ≠ 0 ∧ (∀ t, Evec E t (X (t + 1)) = matAct M (X t)) ∧
      IsAdaptedV E X ∧ IsStableProc X := by
  obtain ⟨r, hr1, hr⟩ := nk_root_of_not_bothOut hT h
  set v : Fin 2 → ℝ := ![r - M 1 1, M 1 0]
  have hv := nk_eigvec2 M (r := r) (by linear_combination hr)
  have hwt : ∀ t, E.E t w = w := fun t => by rw [← hw0, E.tower_ge_apply (Nat.zero_le t)]
  set X : ℕ → Fin 2 → V := fun t i => (r ^ t * v i) • w
  have hXa : ∀ s t, Evec E s (X t) = X t := fun s t => funext fun i => by
    simp only [X, Evec, map_smul, hwt]
  have hrec : ∀ t, matAct M (X t) = X (t + 1) := fun t => by
    funext i
    have hvi := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hvi
    simp only [matAct, X, smul_smul, ← Finset.sum_smul]
    congr 1
    calc ∑ j, M i j * (r ^ t * v j) = r ^ t * ∑ j, M i j * v j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = r ^ (t + 1) * v i := by rw [hvi, pow_succ]; ring
  refine ⟨X, fun h0 => ?_, fun t => by rw [hXa, hrec], (bkS_isAdaptedV_iff E X).2 fun t =>
    hXa t t, ⟨‖v‖ * ‖w‖ + 1, by positivity, fun t i => ?_⟩⟩
  · have := congrFun (congrFun h0 0) 1
    simp only [X, v, pow_zero, one_mul, Pi.zero_apply] at this
    exact smul_ne_zero hM10 hw this
  · simp only [X]
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow]
    have h1 : |r| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg r) hr1
    have h2 : |v i| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
    nlinarith [abs_nonneg (v i), norm_nonneg w, pow_nonneg (abs_nonneg r) t,
      mul_le_mul h1 h2 (abs_nonneg _) zero_le_one]

/-- The jump matrix `W` of the Taylor-rule model of Exercise 2.2 with state `(x_t, π_t)`:
`W = [[1 + δ_x/γ + κ/(βγ), δ_π/γ − 1/(βγ)], [−κ/β, 1/β]]`. -/
noncomputable def nkWT (κ β γ δπ δx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + δx / γ + κ / (β * γ), δπ / γ - 1 / (β * γ); -κ / β, 1 / β]

/-- Exercise 2.2: the model (2.13)–(2.14) with the Taylor rule `i_t = δ_ππ_t + δ_xx_t + ε_t`,
for the state `X_t = (x_t, π_t)`. -/
def nkTaylorEqm (E : CondExpSystem ℝ V) (κ β γ δπ δx : ℝ) (ε εx : ℕ → V)
    (X : ℕ → Fin 2 → V) : Prop :=
  ∀ t, X t 1 = κ • X t 0 + β • E.E t (X (t + 1) 1) ∧
    X t 0 = E.E t (X (t + 1) 0) - γ⁻¹ • ((δπ • X t 1 + δx • X t 0 + ε t) - E.E t (X (t + 1) 1))
      + εx t

/-- Exercise 2.2: the Taylor-rule model has a unique stable equilibrium for every stable adapted
pair of shocks `(ε_t, ε^x_t)`. -/
def nkDeterminate (E : CondExpSystem ℝ V) (κ β γ δπ δx : ℝ) : Prop :=
  ∀ ε εx : ℕ → V, (∃ C, ∀ t, ‖ε t‖ ≤ C) → (∃ C, ∀ t, ‖εx t‖ ≤ C) →
    (∀ t, E.E t (ε t) = ε t) → (∀ t, E.E t (εx t) = εx t) →
    ∃! X, nkTaylorEqm E κ β γ δπ δx ε εx X ∧ IsAdaptedV E X ∧ IsStableProc X

/-- Exercise 2.2 (Miao, pp. 82–83): substituting the Taylor rule, (2.13)–(2.14) are the
jump-only system `E_tX_{t+1} = WX_t + (γ⁻¹ε_t − ε^x_t, 0)'`, `W = nkWT`. -/
theorem nk_taylor_iff (E : CondExpSystem ℝ V) {κ β γ : ℝ} (δπ δx : ℝ) (hβ : β ≠ 0)
    (ε εx : ℕ → V) (X : ℕ → Fin 2 → V) :
    nkTaylorEqm E κ β γ δπ δx ε εx X ↔
      ∀ t, Evec E t (X (t + 1)) = matAct (nkWT κ β γ δπ δx) (X t) + ![γ⁻¹ • ε t - εx t, 0] := by
  refine forall_congr' fun t => ?_
  set a := E.E t (X (t + 1) 0)
  set b := E.E t (X (t + 1) 1)
  set x := X t 0
  set p := X t 1
  have hv : Evec E t (X (t + 1)) = ![a, b] := funext fun i => by fin_cases i <;> rfl
  have hm : matAct (nkWT κ β γ δπ δx) (X t) = ![(1 + δx / γ + κ / (β * γ)) • x +
      (δπ / γ - 1 / (β * γ)) • p, (-κ / β) • x + (1 / β) • p] := funext fun i => by
    fin_cases i <;> simp [matAct, nkWT, Fin.sum_univ_two, x, p]
  have hvec : ∀ u u' v' v'' : V, ![u, u'] = ![v', v''] ↔ u = v' ∧ u' = v'' := fun u u' v' v'' =>
    ⟨fun h => ⟨congrFun h 0, congrFun h 1⟩, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩
  have hadd : ∀ u u' v' v'' : V, ![u, u'] + ![v', v''] = ![u + v', u' + v''] :=
    fun u u' v' v'' => funext fun i => by fin_cases i <;> rfl
  rw [hv, hm, hadd, hvec]
  have e1 : β * (-κ / β) = -κ := by field_simp
  have e2 : β * (1 / β) = 1 := by field_simp
  constructor
  · rintro ⟨h1, h2⟩
    have hb : b = β⁻¹ • (p - κ • x) := by
      rw [h1, add_sub_cancel_left, inv_smul_smul₀ hβ]
    have ha : a = x + γ⁻¹ • ((δπ • p + δx • x + ε t) - b) - εx t := by
      linear_combination (norm := module) -h2
    refine ⟨?_, ?_⟩
    · rw [ha, hb]
      module
    · rw [hb, add_zero]
      module
  · rintro ⟨h1, h2⟩
    rw [add_zero] at h2
    refine ⟨?_, ?_⟩
    · rw [h2, smul_add, smul_smul, smul_smul, e1, e2]
      module
    · rw [h1, h2]
      module

/-- Exercise 2.2: the determinacy conditions for `nkWT`. With `κ, γ > 0`, `0 < β < 1` and
`δ_x ≥ 0`, both eigenvalues of `W` lie outside the unit circle iff
`κ(δ_π − 1) + (1 − β)δ_x > 0` or `κ(1 + δ_π) + (1 + β)(2γ + δ_x) < 0`. -/
theorem nk_bothOut_WT {κ β γ δπ δx : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hδx : 0 ≤ δx) :
    nkBothOut (nkWT κ β γ δπ δx 0 0 + nkWT κ β γ δπ δx 1 1)
        (nkWT κ β γ δπ δx 0 0 * nkWT κ β γ δπ δx 1 1 -
          nkWT κ β γ δπ δx 0 1 * nkWT κ β γ δπ δx 1 0) ↔
      (0 < κ * (δπ - 1) + (1 - β) * δx ∨ κ * (1 + δπ) + (1 + β) * (2 * γ + δx) < 0) := by
  have hP : 0 < β * γ := mul_pos hβ0 hγ
  have eT : nkWT κ β γ δπ δx 0 0 + nkWT κ β γ δπ δx 1 1 =
      1 + δx / γ + κ / (β * γ) + 1 / β := by simp [nkWT]
  have eD : nkWT κ β γ δπ δx 0 0 * nkWT κ β γ δπ δx 1 1 -
      nkWT κ β γ δπ δx 0 1 * nkWT κ β γ δπ δx 1 0 = (γ + δx + κ * δπ) / (β * γ) := by
    simp only [nkWT, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring
  have k1 : 1 - (1 + δx / γ + κ / (β * γ) + 1 / β) + (γ + δx + κ * δπ) / (β * γ) =
      (κ * (δπ - 1) + (1 - β) * δx) / (β * γ) := by
    field_simp
    ring
  have k2 : 1 + (1 + δx / γ + κ / (β * γ) + 1 / β) + (γ + δx + κ * δπ) / (β * γ) =
      (κ * (1 + δπ) + (1 + β) * (2 * γ + δx)) / (β * γ) := by
    field_simp
    ring
  rw [eT, eD, nkBothOut, k1, k2]
  simp only [lt_div_iff₀ hP, div_lt_iff₀ hP, one_mul, zero_mul, neg_one_mul]
  have hbd : 0 ≤ β * δx := mul_nonneg hβ0.le hδx
  constructor
  · rintro (⟨-, h, -⟩ | ⟨-, -, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨by nlinarith, h, by nlinarith⟩
    · exact Or.inr ⟨by nlinarith, by nlinarith, h⟩

/-- The trace of `nkWT` exceeds `2` (so `T² ≥ 4`) when `0 < β < 1`, `κ, γ > 0`, `δ_x ≥ 0`. -/
theorem nk_WT_trace {κ β γ δπ δx : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hδx : 0 ≤ δx) : 4 ≤ (nkWT κ β γ δπ δx 0 0 + nkWT κ β γ δπ δx 1 1) ^ 2 := by
  have eT : nkWT κ β γ δπ δx 0 0 + nkWT κ β γ δπ δx 1 1 =
      1 + δx / γ + κ / (β * γ) + 1 / β := by simp [nkWT]
  have h1 : 1 < 1 / β := one_lt_one_div hβ0 hβ1
  have h2 : 0 ≤ δx / γ := div_nonneg hδx hγ.le
  have h3 : 0 < κ / (β * γ) := by positivity
  rw [eT]
  nlinarith

/-- **Exercise 2.2, sufficiency** (Miao, pp. 82–83): with `κ, γ > 0`, `0 < β < 1`, `δ_x ≥ 0`, if
`κ(δ_π − 1) + (1 − β)δ_x > 0` or `κ(1 + δ_π) + (1 + β)(2γ + δ_x) < 0`, the Taylor-rule model has a
unique stable equilibrium for every stable adapted pair of shocks. -/
theorem ex_2_2_suff [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ δπ δx : ℝ} (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hδx : 0 ≤ δx)
    (hc : 0 < κ * (δπ - 1) + (1 - β) * δx ∨ κ * (1 + δπ) + (1 + β) * (2 * γ + δx) < 0) :
    nkDeterminate E κ β γ δπ δx := by
  rintro ε εx ⟨C1, h1⟩ ⟨C2, h2⟩ ha1 ha2
  set c : ℕ → Fin 2 → V := fun t => ![γ⁻¹ • ε t - εx t, 0]
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  have hC2 : 0 ≤ C2 := (norm_nonneg _).trans (h2 0)
  have hcs : IsStableProc c := by
    refine ⟨|γ⁻¹| * C1 + C2 + 1, by positivity, fun t i => ?_⟩
    fin_cases i
    · simp only [c]
      calc ‖γ⁻¹ • ε t - εx t‖ ≤ ‖γ⁻¹ • ε t‖ + ‖εx t‖ := norm_sub_le _ _
        _ = |γ⁻¹| * ‖ε t‖ + ‖εx t‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |γ⁻¹| * C1 + C2 := add_le_add (mul_le_mul_of_nonneg_left (h1 t) (abs_nonneg _)) (h2 t)
        _ < |γ⁻¹| * C1 + C2 + 1 := lt_add_one _
    · simp only [c]
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_zero]
      positivity
  have hca : IsAdaptedV E c := fun t i => by
    fin_cases i
    · simp only [c]
      simp only [Fin.zero_eta, Matrix.cons_val_zero, map_sub, map_smul, ha1, ha2]
    · simp only [c]
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_zero]
  obtain h := nk_jump2_unique E (nkWT κ β γ δπ δx) ((nk_bothOut_WT hκ hβ0 hβ1 hγ hδx).2 hc)
    hcs hca
  refine (existsUnique_congr fun X => ?_).2 h
  rw [nk_taylor_iff E δπ δx hβ0.ne' ε εx X]

/-- **Exercise 2.2, necessity** (Miao, pp. 82–83): with `κ, γ > 0`, `0 < β < 1`, `δ_x ≥ 0`, if the
Taylor-rule model has a unique stable equilibrium for all stable adapted shocks, then
`κ(δ_π − 1) + (1 − β)δ_x > 0` or `κ(1 + δ_π) + (1 + β)(2γ + δ_x) < 0`. Otherwise a root `r` of
the jump matrix with `|r| ≤ 1` gives, for zero shocks, the second stable equilibrium `rᵗvw`
(`w ≠ 0` `F_0`-measurable). -/
theorem ex_2_2_nec (E : CondExpSystem ℝ V) {κ β γ δπ δx : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hγ : 0 < γ) (hδx : 0 ≤ δx) {w : V} (hw : w ≠ 0) (hw0 : E.E 0 w = w)
    (hdet : nkDeterminate E κ β γ δπ δx) :
    0 < κ * (δπ - 1) + (1 - β) * δx ∨ κ * (1 + δπ) + (1 + β) * (2 * γ + δx) < 0 := by
  by_contra hc
  have hnb := fun hb => hc ((nk_bothOut_WT (δπ := δπ) hκ hβ0 hβ1 hγ hδx).1 hb)
  have hM10 : nkWT κ β γ δπ δx 1 0 ≠ 0 := by
    have e : nkWT κ β γ δπ δx 1 0 = -κ / β := by simp [nkWT]
    rw [e]
    exact div_ne_zero (neg_ne_zero.2 hκ.ne') hβ0.ne'
  obtain ⟨X, hX0, hXe, hXa, hXs⟩ := nk_jump2_nonunique E (nkWT κ β γ δπ δx) hM10
    (nk_WT_trace hκ hβ0 hβ1 hγ hδx) hnb hw hw0
  obtain ⟨Y, -, hYu⟩ := hdet (fun _ => 0) (fun _ => 0) ⟨0, fun _ => by simp⟩
    ⟨0, fun _ => by simp⟩ (fun _ => map_zero _) (fun _ => map_zero _)
  have hz : (![γ⁻¹ • (0 : V) - 0, 0] : Fin 2 → V) = 0 := by
    funext i
    fin_cases i <;> simp
  have h1 := hYu X ⟨(nk_taylor_iff E δπ δx hβ0.ne' _ _ X).2 fun t => by
    rw [hXe t, hz, add_zero], hXa, hXs⟩
  have h2 := hYu 0 ⟨(nk_taylor_iff E δπ δx hβ0.ne' _ _ 0).2 fun t => by
    rw [Pi.zero_apply, Pi.zero_apply, bkS_Evec_zero, bkS_matAct_zero, hz, add_zero],
    fun _ _ => map_zero _, ⟨1, one_pos, fun _ _ => by simp⟩⟩
  exact hX0 (h1.trans h2.symm)

/-- **Exercise 2.2(b)**, exact conditions (Miao, p. 83): for the Taylor rule
`i_t = δ_ππ_t + δ_xx_t + ε_t` with `κ, γ > 0`, `0 < β < 1` and `δ_x ≥ 0` (and `V` containing a
nonzero `F_0`-measurable `w`), there is a unique stable equilibrium for all stable adapted shocks
iff `κ(δ_π − 1) + (1 − β)δ_x > 0` or `κ(1 + δ_π) + (1 + β)(2γ + δ_x) < 0`. The second branch (both
roots below `−1`, for a strongly negative `δ_π`) is missing from the usual statement. -/
theorem ex_2_2_b_exact [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ δπ δx : ℝ}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hδx : 0 ≤ δx) {w : V} (hw : w ≠ 0)
    (hw0 : E.E 0 w = w) :
    nkDeterminate E κ β γ δπ δx ↔
      (0 < κ * (δπ - 1) + (1 - β) * δx ∨ κ * (1 + δπ) + (1 + β) * (2 * γ + δx) < 0) :=
  ⟨ex_2_2_nec E hκ hβ0 hβ1 hγ hδx hw hw0, ex_2_2_suff E hκ hβ0 hβ1 hγ hδx⟩

/-- **Exercise 2.2(b)** (Miao, p. 83), the Bullard–Mitra condition: for `δ_π, δ_x ≥ 0` (with
`κ, γ > 0`, `0 < β < 1`), there is a unique stable equilibrium iff
`κ(δ_π − 1) + (1 − β)δ_x > 0`. -/
theorem ex_2_2_b [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ δπ δx : ℝ} (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hδπ : 0 ≤ δπ) (hδx : 0 ≤ δx) {w : V}
    (hw : w ≠ 0) (hw0 : E.E 0 w = w) :
    nkDeterminate E κ β γ δπ δx ↔ 0 < κ * (δπ - 1) + (1 - β) * δx := by
  rw [ex_2_2_b_exact E hκ hβ0 hβ1 hγ hδx hw hw0]
  refine ⟨fun h => h.resolve_right fun h' => ?_, Or.inl⟩
  nlinarith [mul_nonneg hκ.le hδπ, mul_nonneg hβ0.le hδx]

/-- **Exercise 2.2(a)**, corrected (Miao, p. 82): for the rule `i_t = δπ_t + ε_t` (with
`κ, γ > 0`, `0 < β < 1`), there is a unique stable equilibrium iff `δ > 1` or
`δ < −1 − 2(1 + β)γ/κ`. The book's claim that `δ > 1` is necessary is false
(`ex_2_2_a_printed_false`): for very negative `δ` both roots leave the unit circle through `−1`. -/
theorem ex_2_2_a [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ : ℝ} (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (δ : ℝ) {w : V} (hw : w ≠ 0)
    (hw0 : E.E 0 w = w) :
    nkDeterminate E κ β γ δ 0 ↔ (1 < δ ∨ δ < -1 - 2 * (1 + β) * γ / κ) := by
  rw [ex_2_2_b_exact E hκ hβ0 hβ1 hγ le_rfl hw hw0]
  have e : -1 - 2 * (1 + β) * γ / κ = (-κ - 2 * (1 + β) * γ) / κ := by
    rw [eq_div_iff hκ.ne']
    field_simp
  rw [e, lt_div_iff₀ hκ]
  constructor
  · rintro (h | h)
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)
  · rintro (h | h)
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)

/-- **Exercise 2.2(a)**, the Taylor principle (Miao, p. 82), proved for `δ ≥ 0`: with `κ, γ > 0`
and `0 < β < 1`, there is a unique stable equilibrium iff `δ > 1`. -/
theorem ex_2_2_a_taylor_principle [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ δ : ℝ}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hδ : 0 ≤ δ) {w : V} (hw : w ≠ 0)
    (hw0 : E.E 0 w = w) : nkDeterminate E κ β γ δ 0 ↔ 1 < δ := by
  rw [ex_2_2_a E hκ hβ0 hβ1 hγ δ hw hw0]
  refine ⟨fun h => h.resolve_right fun h' => ?_, Or.inl⟩
  have : 0 < 2 * (1 + β) * γ / κ := by positivity
  linarith

/-- **Exercise 2.2(a)** as printed is false (Miao, p. 82): "`δ > 1` is necessary". For
`κ = γ = 1`, `β = 1/2` and `δ = −5` the equilibrium is unique (the roots of `λ² − 5λ − 8` are
`(5 ± √57)/2`, both outside the unit circle). -/
theorem ex_2_2_a_printed_false [CompleteSpace V] (E : CondExpSystem ℝ V) :
    nkDeterminate E 1 (1 / 2) 1 (-5) 0 ∧ ¬ (1 < (-5 : ℝ)) :=
  ⟨ex_2_2_suff E one_pos (by norm_num) (by norm_num) one_pos le_rfl (Or.inr (by norm_num)),
    by norm_num⟩

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RBSaddle
import NeoclassicalGrowth.NewKeynesian

/-!
# The stochastic saddle path of the log-linearised RBC model (Blanchard–Kahn)

Miao, §14.2, pp. 476–478: "Equations (14.32) and (14.33) combined with the shock process in
(14.25) constitute a linear system of difference equations for `{Ĉ_t, K̂_{t+1}}` ... Given any
initial state for `K̂₀` and `ẑ₀`, there is a unique solution `Ĉ₀`, which must lie on the saddle."
Here this is the stochastic Theorem 1.4.2 of Chapter 2 (`bkS_exists`, `bkS_unique`) applied to
the RBC system, with `E_t` a conditional expectation system (`CondExpSystem`) on a real Banach
space `V` (e.g. `L¹`).

* `rb_split2`: an explicit real block split of a `2 × 2` saddle matrix `[[m₁₁, m₁₂], [m₂₁, m₂₂]]`
  with eigenvalues `|λ₁| < 1 < λ₂` (left eigenvectors `(λᵢ − m₂₂, m₁₂)`).
* `rb_bk_iff`: with `K̂` predetermined and `E_tẑ_{t+1} = ρẑ_t` (from (14.25)), (14.32)–(14.33)
  are equivalent to `E_tx_{t+1} = Wx_t + Gẑ_t` for `x = (K̂, Ĉ)`, `W` the matrix of
  `RBSaddle` and `G = (g, (bρ − cg)/(1 + a))`.
* **`rb_saddle_stoch`**: for every `F₀`-measurable `K̂₀` and every stable adapted `ẑ` with
  `E_tẑ_{t+1} = ρẑ_t`, there is exactly one stable adapted solution `(K̂, Ĉ)` of (14.32)–(14.33)
  with `K̂` predetermined and the given `K̂₀`.
-/

namespace Miao.NeoclassicalGrowth

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A `2 × 2` matrix in the block form of Chapter 2 (`k = Fin 1`, `y = Fin 1`). -/
noncomputable def rb_W2 (m11 m12 m21 m22 : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks !![m11] !![m12] !![m21] !![m22]

/-- The rows `(λ₁ − m₂₂, m₁₂)` (stable) and `(λ₂ − m₂₂, m₁₂)` (unstable): left eigenvectors. -/
noncomputable def rb_P2 (m12 m22 l1 l2 : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks !![l1 - m22] !![m12] !![l2 - m22] !![m12]

/-- The inverse of `rb_P2`. -/
noncomputable def rb_R2 (m12 m22 l1 l2 : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks !![m12 / (m12 * (l1 - l2))] !![-m12 / (m12 * (l1 - l2))]
    !![-(l2 - m22) / (m12 * (l1 - l2))] !![(l1 - m22) / (m12 * (l1 - l2))]

/-- A real block split of a `2 × 2` saddle matrix (Miao, pp. 53–54 applied on p. 478): if
`λ₁ + λ₂ = m₁₁ + m₂₂`, `λ₁λ₂ = m₁₁m₂₂ − m₁₂m₂₁`, `m₁₂ ≠ 0`, `|λ₁| < 1 < λ₂`, then
`PWP⁻¹ = diag(λ₁, λ₂)` with `n_s = n_u = 1`. -/
theorem rb_split2 {m11 m12 m21 m22 l1 l2 : ℝ} (hsum : l1 + l2 = m11 + m22)
    (hprod : l1 * l2 = m11 * m22 - m12 * m21) (hm12 : m12 ≠ 0) (hl1 : |l1| < 1)
    (hl2 : 1 < l2) :
    IsRealBlockSplit (rb_W2 m11 m12 m21 m22) (rb_P2 m12 m22 l1 l2) (rb_R2 m12 m22 l1 l2)
      !![l1] !![l2] := by
  have hd : l1 - l2 ≠ 0 := by
    have := (abs_lt.1 hl1).2
    linarith
  obtain rfl : m22 = l1 + l2 - m11 := by linarith
  obtain rfl : m21 = (m11 * (l1 + l2 - m11) - l1 * l2) / m12 := by
    field_simp
    linarith
  refine ⟨?_, ?_, ?_, fun μ hμ => ?_, fun μ hμ => ?_⟩
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [rb_P2, rb_R2, Matrix.mul_apply, Fintype.sum_sum_type] <;>
      field_simp <;> ring
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [rb_P2, rb_R2, Matrix.mul_apply, Fintype.sum_sum_type] <;>
      field_simp <;> ring
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [rb_P2, rb_W2, Matrix.mul_apply, Fintype.sum_sum_type] <;>
      field_simp <;> ring
  · rw [nk_scalar_eig hμ, Complex.norm_real, Real.norm_eq_abs]
    exact hl1
  · rw [nk_scalar_eig hμ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hl2

/-- The forcing matrix `G = (g, h)` of the shock `ẑ_t`. -/
noncomputable def rb_G2 (g h : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ :=
  Matrix.of fun i _ => Sum.elim (fun _ => g) (fun _ => h) i

/-- The log-linearised RBC system (14.32)–(14.33) at date `t` for `V`-valued `x = (K̂, Ĉ)` and
shock `ẑ`. -/
def rb_IsLinRBC (E : CondExpSystem ℝ V) (α β ζ yk ck : ℝ) (z : ℕ → Fin 1 → V)
    (x : ℕ → Fin 1 ⊕ Fin 1 → V) (t : ℕ) : Prop :=
  x (t + 1) (Sum.inl 0) = rb_p α β ζ yk • x t (Sum.inl 0) + rb_g α ζ yk • z t 0 -
      rb_q α ζ yk ck • x t (Sum.inr 0) ∧
    -x t (Sum.inr 0) = -(1 + rb_a α β ζ yk) • E.E t (x (t + 1) (Sum.inr 0)) +
      rb_b α β ζ yk • E.E t (z (t + 1) 0) - rb_c α β ζ yk • E.E t (x (t + 1) (Sum.inl 0))

/-- The matrices `W`, `G` of the RBC system in the form `E_tx_{t+1} = Wx_t + Gẑ_t`. -/
noncomputable def rb_Wrbc (α β ζ yk ck : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  rb_W2 (rb_p α β ζ yk) (-rb_q α ζ yk ck) (rb_m21 α β ζ yk) (rb_m22 α β ζ yk ck)

/-- `G = (g, (bρ − cg)/(1 + a))`. -/
noncomputable def rb_Grbc (α β ζ yk ρ : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ :=
  rb_G2 (rb_g α ζ yk)
    ((rb_b α β ζ yk * ρ - rb_c α β ζ yk * rb_g α ζ yk) / (1 + rb_a α β ζ yk))

theorem rb_matAct_W2 (m11 m12 m21 m22 : ℝ) (x : Fin 1 ⊕ Fin 1 → V) :
    matAct (rb_W2 m11 m12 m21 m22) x (Sum.inl 0) = m11 • x (Sum.inl 0) + m12 • x (Sum.inr 0) ∧
      matAct (rb_W2 m11 m12 m21 m22) x (Sum.inr 0) =
        m21 • x (Sum.inl 0) + m22 • x (Sum.inr 0) := by
  simp [matAct, rb_W2, Fintype.sum_sum_type]

theorem rb_matAct_G2 (g h : ℝ) (z : Fin 1 → V) :
    matAct (rb_G2 g h) z (Sum.inl 0) = g • z 0 ∧ matAct (rb_G2 g h) z (Sum.inr 0) = h • z 0 := by
  simp [matAct, rb_G2]

/-- Miao, pp. 476–477: with `K̂_{t+1}` known at `t` and `E_tẑ_{t+1} = ρẑ_t`, (14.32)–(14.33)
at date `t` are equivalent to `E_tx_{t+1} = Wx_t + Gẑ_t`. -/
theorem rb_bk_iff (E : CondExpSystem ℝ V) {α β ζ yk ck ρ : ℝ} (ha : 1 + rb_a α β ζ yk ≠ 0)
    {z : ℕ → Fin 1 → V} {x : ℕ → Fin 1 ⊕ Fin 1 → V} (t : ℕ)
    (hz : E.E t (z (t + 1) 0) = ρ • z t 0)
    (hk : E.E t (x (t + 1) (Sum.inl 0)) = x (t + 1) (Sum.inl 0)) :
    Evec E t (x (t + 1)) = matAct (rb_Wrbc α β ζ yk ck) (x t) +
        matAct (rb_Grbc α β ζ yk ρ) (z t) ↔ rb_IsLinRBC E α β ζ yk ck z x t := by
  obtain ⟨hW1, hW2⟩ := rb_matAct_W2 (rb_p α β ζ yk) (-rb_q α ζ yk ck) (rb_m21 α β ζ yk)
    (rb_m22 α β ζ yk ck) (x t)
  obtain ⟨hG1, hG2⟩ := rb_matAct_G2 (V := V) (rb_g α ζ yk)
    ((rb_b α β ζ yk * ρ - rb_c α β ζ yk * rb_g α ζ yk) / (1 + rb_a α β ζ yk)) (z t)
  have hfun : ∀ u v : Fin 1 ⊕ Fin 1 → V, u = v ↔ u (Sum.inl 0) = v (Sum.inl 0) ∧
      u (Sum.inr 0) = v (Sum.inr 0) := fun u v => by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      funext i
      rcases i with i | i <;> fin_cases i
      · exact h1
      · exact h2
  rw [hfun]
  simp only [Evec, Pi.add_apply, rb_Wrbc, rb_Grbc, hW1, hW2, hG1, hG2, hk, rb_IsLinRBC, hz]
  set K := x t (Sum.inl 0)
  set C := x t (Sum.inr 0)
  set K' := x (t + 1) (Sum.inl 0)
  set EC := E.E t (x (t + 1) (Sum.inr 0))
  set Z := z t 0
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : K' = rb_p α β ζ yk • K + rb_g α ζ yk • Z - rb_q α ζ yk ck • C := by
      rw [h1]; module
    refine ⟨h1', ?_⟩
    rw [h2, h1', rb_m21, rb_m22]
    match_scalars <;> field_simp <;> ring
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h1]; module, ?_⟩
    rw [h1] at h2
    have h3 : EC = (1 + rb_a α β ζ yk)⁻¹ • ((1 + rb_a α β ζ yk) • EC) := by
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    have h4 : (1 + rb_a α β ζ yk) • EC = C + rb_b α β ζ yk • ρ • Z -
        rb_c α β ζ yk • (rb_p α β ζ yk • K + rb_g α ζ yk • Z - rb_q α ζ yk ck • C) := by
      have : (1 + rb_a α β ζ yk) • EC = -(-(1 + rb_a α β ζ yk) • EC) := by module
      rw [this]
      have h5 : -(1 + rb_a α β ζ yk) • EC = -C - rb_b α β ζ yk • ρ • Z +
          rb_c α β ζ yk • (rb_p α β ζ yk • K + rb_g α ζ yk • Z - rb_q α ζ yk ck • C) := by
        rw [h2]; module
      rw [h5]
      module
    rw [h3, h4, rb_m21, rb_m22]
    match_scalars <;> field_simp
    ring

/-- **The stochastic saddle path** (Miao, pp. 476–478, via the stochastic Blanchard–Kahn
Theorem 1.4.2 of Chapter 2). Let `0 < α < 1`, `0 < β < 1`, `ζ, Y/K, C/K > 0`. For every
`F₀`-measurable `K̂₀` and every stable adapted shock `ẑ` with `E_tẑ_{t+1} = ρẑ_t`, there is exactly
one stable adapted process `x = (K̂, Ĉ)` with `K̂` predetermined and `K̂_0 = K̂₀` satisfying
(14.32)–(14.33) at every date. -/
theorem rb_saddle_stoch [CompleteSpace V] (E : CondExpSystem ℝ V) {α β ζ yk ck ρ : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk)
    (hck : 0 < ck) {z : ℕ → Fin 1 → V} (hzs : IsStableProc z) (hza : IsAdaptedV E z)
    (hz : ∀ t, E.E t (z (t + 1) 0) = ρ • z t 0) (k₀ : V) (hk₀ : E.E 0 k₀ = k₀) :
    ∃! x : ℕ → Fin 1 ⊕ Fin 1 → V, (∀ t, rb_IsLinRBC E α β ζ yk ck z x t) ∧
      IsAdaptedV E x ∧ IsPredeterminedBK E (fun t => x t ∘ Sum.inl) ∧ IsStableProc x ∧
      x 0 (Sum.inl 0) = k₀ := by
  obtain ⟨-, -, ha, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have ha' : 1 + rb_a α β ζ yk ≠ 0 := by linarith
  obtain ⟨hs, hpr, hl0, hl1, hl2, -, -⟩ := rb_saddle_eigen hα0 hα1 hβ0 hβ1 hζ hyk hck
  obtain ⟨-, hq, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have hm12 : -rb_q α ζ yk ck ≠ 0 := neg_ne_zero.2 hq.ne'
  have hS := rb_split2 hs hpr hm12 (by rw [abs_of_pos hl0]; exact hl1) hl2
  set P := rb_P2 (-rb_q α ζ yk ck) (rb_m22 α β ζ yk ck) _ _
  have hP22 : P.toBlocks₂₂ = !![-rb_q α ζ yk ck] := by
    simp [P, rb_P2]
  set Q : Matrix (Fin 1) (Fin 1) ℝ := !![(-rb_q α ζ yk ck)⁻¹]
  have hQ1 : P.toBlocks₂₂ * Q = 1 := by
    rw [hP22]
    ext i j
    fin_cases i; fin_cases j
    simp [Q, hq.ne']
  have hQ2 : Q * P.toBlocks₂₂ = 1 := by
    rw [hP22]
    ext i j
    fin_cases i; fin_cases j
    simp [Q, hq.ne']
  -- the set of solutions coincides with the stable solutions of the Blanchard–Kahn system
  have hiff : ∀ x : ℕ → Fin 1 ⊕ Fin 1 → V,
      ((∀ t, rb_IsLinRBC E α β ζ yk ck z x t) ∧ IsAdaptedV E x ∧
        IsPredeterminedBK E (fun t => x t ∘ Sum.inl) ∧ IsStableProc x ∧
        x 0 (Sum.inl 0) = k₀) ↔
      (bkS_IsStableSol E (rb_Wrbc α β ζ yk ck) (rb_Grbc α β ζ yk ρ) z x ∧
        x 0 ∘ Sum.inl = fun _ => k₀) := fun x => by
    have h0 : x 0 ∘ Sum.inl = (fun _ : Fin 1 => k₀) ↔ x 0 (Sum.inl 0) = k₀ := by
      constructor
      · intro h; exact congrFun h 0
      · intro h; funext i; fin_cases i; exact h
    rw [h0, bkS_IsStableSol]
    constructor
    · rintro ⟨hsys, hxa, hxp, hxs, hx0⟩
      exact ⟨⟨fun t => (rb_bk_iff E ha' t (hz t) (hxp t 0)).2 (hsys t), hxa, hxp, hxs⟩, hx0⟩
    · rintro ⟨⟨hsys, hxa, hxp, hxs⟩, hx0⟩
      exact ⟨fun t => (rb_bk_iff E ha' t (hz t) (hxp t 0)).1 (hsys t), hxa, hxp, hxs, hx0⟩
  obtain ⟨x, hx, hx0⟩ := bkS_exists E hS Q hQ1 (rb_Grbc α β ζ yk ρ) hzs hza
    (fun _ : Fin 1 => k₀) (fun _ => hk₀)
  refine ⟨x, (hiff x).2 ⟨hx, hx0⟩, fun y hy => ?_⟩
  obtain ⟨hy, hy0⟩ := (hiff y).1 hy
  exact bkS_unique E hS Q hQ2 (rb_Grbc α β ζ yk ρ) hzs hza hy hx (hy0.trans hx0.symm)

end Miao.NeoclassicalGrowth

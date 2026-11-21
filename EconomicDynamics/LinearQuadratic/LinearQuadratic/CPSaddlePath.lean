/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.CPRamsey
import LinearQuadratic.KleinSimplified

/-!
# Optimal policy under commitment: the saddle path and time inconsistency

Miao, §9.4, pp. 307–308. The stacked system (9.22) (`eq_9_22`) is reordered with the
predetermined block `k_t = (z_t, μ_{yt})` first and the non-predetermined block
`λ_t = (y_t, u_t, μ_{zt})` second, `J E_t[k_{t+1}; λ_{t+1}] = H[k_t; λ_t]`, and solved by
Klein's method (Chapter 2's `Singular` and `KleinSimplified`).

**Representation.** `z`, `y`, `u` are indexed by `Fin nz`, `Fin ny`, `Fin nu`; the reordered
vector `(k, λ)` lives on `Fin ((nz + ny) + ((ny + nu) + nz))`, with `k_t` the first `nz + ny`
coordinates (`z_t`, then `μ_{yt}`) and `λ_t` the rest (`y_t`, `u_t`, then `μ_{zt}`).
`cpColEquiv` maps these coordinates to the `(x, μ)` coordinates of (9.22) and `cpRowEquiv`
orders the equations. `J = cpJ`, `H = cpH`.

* `cp_reordered_iff` (p. 307, "we reorder equations in (9.22)"): a path solves
  `J[k; λ]_{t+1} = H[k; λ]_t + C'ε_{t+1}` iff the corresponding path solves (9.22).
* `cp_saddle_path` (p. 307, "the above system has a unique saddle path solution as long as a
  stability condition and a rank condition is satisfied"): under the hypotheses of Klein's
  Theorem 1.4.5 for `(J, H)` (regularity, an ordered QZ form with as many stable generalised
  eigenvalues as predetermined variables, invertible `Z₁₁`, no eigenvalue on the unit circle),
  for every `z̄₀` and every bounded shock path, (9.22) has a unique bounded solution with
  `z₀ = z̄₀` and `μ_{y0} = 0`.
* `cp_recursive_form` (pp. 307–308): with uncertainty (the system in expectations, `ε`
  entering through the prediction error of `z`), there are matrices with
  `z_{t+1} = A_zz z_t + A_zμ μ_{yt} + Cε_{t+1}`, `μ_{y,t+1} = A_μz z_t + A_μμ μ_{yt}`,
  `y_t = A_yz z_t + A_yμ μ_{yt}`, `u_t = A_uz z_t + A_uμ μ_{yt}`,
  `μ_{zt} = A_{μz z} z_t + A_{μz μ} μ_{yt}` for every stable adapted solution: the multiplier
  `μ_y` on the forward-looking variables is a state variable.
* `cp_time_inconsistency` (p. 308): reoptimising at date `t₀` restarts the system from
  `(z_{t₀}, 0)`; the reoptimised plan coincides with the continuation of the date-`0` plan iff
  `μ_{y,t₀} = 0`.

**Departures.** The deterministic saddle-path statement is the perfect-foresight form (the shock
path given); the recursive form uses the stochastic Klein theorem of Chapter 2, whose
coefficient matrices are complex (the QZ form is complex); that they are real is not proved.
-/

namespace Miao.LinearQuadratic

open scoped Matrix

/-! ### Reordering -/

/-- The reordering `(k, λ) = ((z, μ_y), ((y, u), μ_z)) ↦ ((z, y, u), (μ_z, μ_y))`. -/
def cpReorder (Z Y U : Type*) :
    (Z ⊕ Y) ⊕ ((Y ⊕ U) ⊕ Z) ≃ ((Z ⊕ Y) ⊕ U) ⊕ (Z ⊕ Y) where
  toFun
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl (Sum.inl i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr (Sum.inl (Sum.inl i)) => Sum.inl (Sum.inl (Sum.inr i))
    | Sum.inr (Sum.inl (Sum.inr i)) => Sum.inl (Sum.inr i)
    | Sum.inr (Sum.inr i) => Sum.inr (Sum.inl i)
  invFun
    | Sum.inl (Sum.inl (Sum.inl i)) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inl (Sum.inr i)) => Sum.inr (Sum.inl (Sum.inl i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inl (Sum.inr i))
    | Sum.inr (Sum.inl i) => Sum.inr (Sum.inr i)
    | Sum.inr (Sum.inr i) => Sum.inl (Sum.inr i)
  left_inv := by rintro ((i | i) | ((i | i) | i)) <;> rfl
  right_inv := by rintro (((i | i) | i) | (i | i)) <;> rfl

/-- The coordinates of `(k, λ)`: `Fin ((nz + ny) + ((ny + nu) + nz)) ≃ (x, μ)`-coordinates. -/
def cpColEquiv (nz ny nu : ℕ) :
    Fin ((nz + ny) + ((ny + nu) + nz)) ≃
      ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ⊕ (Fin nz ⊕ Fin ny) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _))))).trans
    (cpReorder (Fin nz) (Fin ny) (Fin nu))

/-- An ordering of the equations of (9.22). -/
def cpRowEquiv (nz ny nu : ℕ) :
    Fin ((nz + ny) + ((ny + nu) + nz)) ≃
      (Fin nz ⊕ Fin ny) ⊕ ((Fin nz ⊕ Fin ny) ⊕ Fin nu) :=
  (finCongr (by omega : (nz + ny) + ((ny + nu) + nz) = (nz + ny) + ((nz + ny) + nu))).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm
      (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)))))

/-- `J` of Miao, p. 307: the reordered left matrix of (9.22). -/
def cpJ {nz ny nu : ℕ} (β : ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ) :
    Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ((nz + ny) + ((ny + nu) + nz))) ℝ :=
  (cpLeft β Dbar Abar).submatrix (cpRowEquiv nz ny nu) (cpColEquiv nz ny nu)

/-- `H` of Miao, p. 307: the reordered right matrix of (9.22). -/
def cpH {nz ny nu : ℕ}
    (W : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ) :
    Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ((nz + ny) + ((ny + nu) + nz))) ℝ :=
  (cpRight W Dbar Abar).submatrix (cpRowEquiv nz ny nu) (cpColEquiv nz ny nu)

/-- The shock loading `[C; 0; 0]` in the reordered equations. -/
def cpCfin {nz ny nu ne : ℕ} (C : Matrix (Fin nz) (Fin ne) ℝ) :
    Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ne) ℝ :=
  (Matrix.fromRows (Matrix.fromRows C (0 : Matrix (Fin ny) (Fin ne) ℝ))
    (0 : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) (Fin ne) ℝ)).submatrix (cpRowEquiv nz ny nu)
      (Equiv.refl _)

theorem cp_submatrix_id_mulVec {α β γ : Type*} [Fintype γ] (M : Matrix β γ ℝ) (e : α → β)
    (v : γ → ℝ) : M.submatrix e id *ᵥ v = (M *ᵥ v) ∘ e :=
  rfl

theorem cp_comp_equiv_iff {α β : Type*} (e : α ≃ β) (f g k : β → ℝ) :
    f ∘ e = g ∘ e + k ∘ e ↔ f = g + k := by
  constructor
  · intro H
    funext i
    have := congrFun H (e.symm i)
    simpa using this
  · intro H
    rw [H]
    rfl

/-- Miao, p. 307 ("we reorder equations in (9.22) and rewrite it as `J[k; λ]_{t+1} =
H[k; λ]_t`"): a path `v` of `(k, λ)` solves the reordered system iff `v ∘ cpColEquiv⁻¹` solves
(9.22) with `c_{t+1} = [Cε_{t+1}; 0]`. -/
theorem cp_reordered_iff {nz ny nu ne : ℕ} (β : ℝ)
    (W : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (C : Matrix (Fin nz) (Fin ne) ℝ) (ε : ℕ → Fin ne → ℝ)
    (v : ℕ → Fin ((nz + ny) + ((ny + nu) + nz)) → ℝ) :
    IsSolution (cpJ β Dbar Abar) (cpH W Dbar Abar) (cpCfin (ny := ny) (nu := nu) C)
        (fun t => ε (t + 1)) v ↔
      ∀ t, cpLeft β Dbar Abar *ᵥ (v (t + 1) ∘ (cpColEquiv nz ny nu).symm) =
        cpRight W Dbar Abar *ᵥ (v t ∘ (cpColEquiv nz ny nu).symm) +
          Sum.elim (Sum.elim (C *ᵥ ε (t + 1)) 0) 0 := by
  simp only [IsSolution, cpJ, cpH, cpCfin, Matrix.submatrix_mulVec_equiv, Equiv.coe_refl,
    cp_submatrix_id_mulVec, cp_comp_equiv_iff, Matrix.fromRows_mulVec, Matrix.zero_mulVec]

/-- The sup norm is invariant under relabelling coordinates. -/
theorem cp_norm_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (v : β → ℝ) :
    ‖v ∘ e‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · exact norm_le_pi_norm v (e i)
  · have := norm_le_pi_norm (v ∘ e) (e.symm i)
    simpa using this

/-! ### The saddle path -/

/-- **The saddle-path solution** (Miao, p. 307). Suppose `(J, H)` satisfies the hypotheses of
Klein's Theorem 1.4.5 (`theorem_1_4_5_real`) with `n_k = n_z + n_y` predetermined variables
`k = (z, μ_y)`. Then for every initial state `z̄₀` and every bounded shock path, (9.22) has a
unique bounded solution with `z₀ = z̄₀` and `μ_{y0} = 0`. -/
theorem cp_saddle_path {nz ny nu ne : ℕ} (β : ℝ)
    (W : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (C : Matrix (Fin nz) (Fin ne) ℝ)
    (hreg : IsRegular ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom))
    {Q Zq : Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ((nz + ny) + ((ny + nu) + nz))) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup _ ℂ) (hZ : Zq ∈ Matrix.unitaryGroup _ ℂ)
    (hS : (Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hT : (Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hord : ∀ i : Fin ((nz + ny) + ((ny + nu) + nz)), i.val < nz + ny ↔
      ‖(Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq) i i‖ <
        ‖(Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq) i i‖)
    (hZ11 : (Zq.submatrix (Fin.castAdd ((ny + nu) + nz))
      (Fin.castAdd ((ny + nu) + nz))).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom), ‖lam‖ ≠ 1)
    (zbar : Fin nz → ℝ) {ε : ℕ → Fin ne → ℝ} (hε : IsStableSeq ε) :
    ∃! w : ℕ → ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ⊕ (Fin nz ⊕ Fin ny) → ℝ,
      (∀ t, cpLeft β Dbar Abar *ᵥ w (t + 1) =
        cpRight W Dbar Abar *ᵥ w t + Sum.elim (Sum.elim (C *ᵥ ε (t + 1)) 0) 0) ∧
      IsStableSeq w ∧ (∀ i, w 0 (Sum.inl (Sum.inl (Sum.inl i))) = zbar i) ∧
      ∀ i, w 0 (Sum.inr (Sum.inr i)) = 0 := by
  set e := cpColEquiv nz ny nu
  obtain ⟨v, ⟨h1, h2, h3⟩, hu⟩ := theorem_1_4_5_real (C := cpCfin (ny := ny) (nu := nu) C)
    hreg hQ hZ hS hT hord hZ11 hcirc (Fin.append zbar 0) (hε.shift 1)
  have he1 : ∀ i, e (Fin.castAdd _ (Fin.castAdd ny i)) = Sum.inl (Sum.inl (Sum.inl i)) :=
    fun i => by simp [e, cpColEquiv, cpReorder]
  have he2 : ∀ i, e (Fin.castAdd _ (Fin.natAdd nz i)) = Sum.inr (Sum.inr i) :=
    fun i => by simp [e, cpColEquiv, cpReorder]
  refine ⟨fun t => v t ∘ e.symm, ⟨(cp_reordered_iff β W Dbar Abar C ε v).1 h1, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨M, hM, h⟩ := h2
    exact ⟨M, hM, fun t => by rw [cp_norm_comp_equiv]; exact h t⟩
  · intro i
    have := h3 (Fin.castAdd ny i)
    rw [Fin.append_left] at this
    simp only [Function.comp_apply, ← he1, Equiv.symm_apply_apply]
    exact this
  · intro i
    have := h3 (Fin.natAdd nz i)
    rw [Fin.append_right] at this
    simp only [Function.comp_apply, ← he2, Equiv.symm_apply_apply]
    exact this
  · rintro w ⟨hw1, hw2, hw3, hw4⟩
    have hwv : ∀ t, (w t ∘ e) ∘ e.symm = w t := fun t => by
      funext i
      simp
    have := hu (fun t => w t ∘ e) ⟨(cp_reordered_iff β W Dbar Abar C ε _).2 (fun t => by
      rw [hwv, hwv]
      exact hw1 t), ?_, ?_⟩
    · funext t
      rw [← this]
      funext i
      simp
    · obtain ⟨M, hM, h⟩ := hw2
      exact ⟨M, hM, fun t => by rw [cp_norm_comp_equiv]; exact h t⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Function.comp_apply, he1, Fin.append_left]
        exact hw3 i
      · simp only [Function.comp_apply, he2, Fin.append_right, Pi.zero_apply]
        exact hw4 i

/-- **Time inconsistency** (Miao, p. 308). Let `w` be the commitment plan chosen at date `0`
(the bounded solution of (9.22) from `(z̄₀, μ_{y0} = 0)`), and let `ŵ` be the plan chosen by
reoptimising at date `t₀`: the bounded solution of (9.22) for the remaining shocks from
`(z_{t₀}, μ_{y t₀} = 0)` ("we must have `μ_{yt} = 0` because `y_t` is freely chosen"). Under
the hypotheses of `cp_saddle_path`, the reoptimised plan is the continuation of the date-`0`
plan iff `μ_{y t₀} = 0`. -/
theorem cp_time_inconsistency {nz ny nu ne : ℕ} (β : ℝ)
    (W : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (C : Matrix (Fin nz) (Fin ne) ℝ)
    (hreg : IsRegular ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom))
    {Q Zq : Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ((nz + ny) + ((ny + nu) + nz))) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup _ ℂ) (hZ : Zq ∈ Matrix.unitaryGroup _ ℂ)
    (hS : (Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hT : (Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hord : ∀ i : Fin ((nz + ny) + ((ny + nu) + nz)), i.val < nz + ny ↔
      ‖(Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq) i i‖ <
        ‖(Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq) i i‖)
    (hZ11 : (Zq.submatrix (Fin.castAdd ((ny + nu) + nz))
      (Fin.castAdd ((ny + nu) + nz))).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom), ‖lam‖ ≠ 1)
    {ε : ℕ → Fin ne → ℝ} (hε : IsStableSeq ε)
    {w : ℕ → ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ⊕ (Fin nz ⊕ Fin ny) → ℝ}
    (hw : ∀ t, cpLeft β Dbar Abar *ᵥ w (t + 1) =
      cpRight W Dbar Abar *ᵥ w t + Sum.elim (Sum.elim (C *ᵥ ε (t + 1)) 0) 0)
    (hws : IsStableSeq w) (t₀ : ℕ)
    {ŵ : ℕ → ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ⊕ (Fin nz ⊕ Fin ny) → ℝ}
    (hŵ : ∀ t, cpLeft β Dbar Abar *ᵥ ŵ (t + 1) =
      cpRight W Dbar Abar *ᵥ ŵ t + Sum.elim (Sum.elim (C *ᵥ ε (t + t₀ + 1)) 0) 0)
    (hŵs : IsStableSeq ŵ)
    (hŵz : ∀ i, ŵ 0 (Sum.inl (Sum.inl (Sum.inl i))) = w t₀ (Sum.inl (Sum.inl (Sum.inl i))))
    (hŵμ : ∀ i, ŵ 0 (Sum.inr (Sum.inr i)) = 0) :
    (∀ s, ŵ s = w (s + t₀)) ↔ ∀ i, w t₀ (Sum.inr (Sum.inr i)) = 0 := by
  constructor
  · intro h i
    rw [← hŵμ i, h 0, zero_add]
  · intro hμ
    have hu := cp_saddle_path β W Dbar Abar C hreg hQ hZ hS hT hord hZ11 hcirc
      (fun i => w t₀ (Sum.inl (Sum.inl (Sum.inl i)))) (hε.shift t₀)
    have := hu.unique (y₁ := ŵ) (y₂ := fun s => w (s + t₀))
      ⟨fun t => by simpa only [add_right_comm] using hŵ t, hŵs, hŵz, hŵμ⟩
      ⟨fun t => by simpa only [add_right_comm] using hw (t + t₀), hws.shift t₀,
        fun i => by simp, fun i => by simpa using hμ i⟩
    exact fun s => congrFun this s

/-! ### The recursive form of the solution -/

/-- **The recursive solution** (Miao, pp. 307–308). Under the hypotheses of Klein's theorem for
the complexified `(J, H)` (`klein_simplified_form`), there are matrices such that every stable
adapted solution `(k, λ) = ((z, μ_y), ((y, u), μ_z))` of the system in expectations
`J E_t[k; λ]_{t+1} = H[k; λ]_t`, in which `z` has prediction error `Cε_{t+1}` and `μ_y` is
predetermined, satisfies
`z_{t+1} = A_zz z_t + A_zμ μ_{yt} + Cε_{t+1}`, `μ_{y,t+1} = A_μz z_t + A_μμ μ_{yt}`,
`y_t = A_yz z_t + A_yμ μ_{yt}`, `u_t = A_uz z_t + A_uμ μ_{yt}` and
`μ_{zt} = A_{μz,z} z_t + A_{μz,μ} μ_{yt}`. -/
theorem cp_recursive_form {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (E : CondExpSystem ℂ V) {nz ny nu ne : ℕ} (β : ℝ)
    (W : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (C : Matrix (Fin nz) (Fin ne) ℂ)
    (hreg : IsRegular ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom))
    {Q Zq : Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ((nz + ny) + ((ny + nu) + nz))) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup _ ℂ) (hZ : Zq ∈ Matrix.unitaryGroup _ ℂ)
    (hS : (Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hT : (Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hord : ∀ i : Fin ((nz + ny) + ((ny + nu) + nz)), i.val < nz + ny ↔
      ‖(Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq) i i‖ <
        ‖(Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq) i i‖)
    (hZ11 : (Zq.submatrix (Fin.castAdd ((ny + nu) + nz))
      (Fin.castAdd ((ny + nu) + nz))).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom), ‖lam‖ ≠ 1) :
    ∃ (Azz : Matrix (Fin nz) (Fin nz) ℂ) (Azμ : Matrix (Fin nz) (Fin ny) ℂ)
      (Aμz : Matrix (Fin ny) (Fin nz) ℂ) (Aμμ : Matrix (Fin ny) (Fin ny) ℂ)
      (Ayz : Matrix (Fin ny) (Fin nz) ℂ) (Ayμ : Matrix (Fin ny) (Fin ny) ℂ)
      (Auz : Matrix (Fin nu) (Fin nz) ℂ) (Auμ : Matrix (Fin nu) (Fin ny) ℂ)
      (Amz : Matrix (Fin nz) (Fin nz) ℂ) (Amμ : Matrix (Fin nz) (Fin ny) ℂ),
      ∀ (ε : ℕ → Fin ne → V) (x : ℕ → Fin ((nz + ny) + ((ny + nu) + nz)) → V),
        IsRESolution E ((cpJ β Dbar Abar).map Complex.ofRealHom)
          ((cpH W Dbar Abar).map Complex.ofRealHom) (0 : Matrix _ (Fin 0) ℂ) (fun _ => 0) x →
        IsStableProc x → IsAdaptedV E x →
        (∀ t i, x (t + 1) (Fin.castAdd _ (Fin.castAdd ny i)) -
          E.E t (x (t + 1) (Fin.castAdd _ (Fin.castAdd ny i))) = matAct C (ε (t + 1)) i) →
        (∀ t i, E.E t (x (t + 1) (Fin.castAdd _ (Fin.natAdd nz i))) =
          x (t + 1) (Fin.castAdd _ (Fin.natAdd nz i))) →
        ∀ t,
          (x (t + 1) ∘ Fin.castAdd _) ∘ Fin.castAdd ny =
            matAct Azz ((x t ∘ Fin.castAdd _) ∘ Fin.castAdd ny) +
              matAct Azμ ((x t ∘ Fin.castAdd _) ∘ Fin.natAdd nz) + matAct C (ε (t + 1)) ∧
          (x (t + 1) ∘ Fin.castAdd _) ∘ Fin.natAdd nz =
            matAct Aμz ((x t ∘ Fin.castAdd _) ∘ Fin.castAdd ny) +
              matAct Aμμ ((x t ∘ Fin.castAdd _) ∘ Fin.natAdd nz) ∧
          (x t ∘ Fin.natAdd (nz + ny)) ∘ (Fin.castAdd nz ∘ Fin.castAdd nu) =
            matAct Ayz ((x t ∘ Fin.castAdd _) ∘ Fin.castAdd ny) +
              matAct Ayμ ((x t ∘ Fin.castAdd _) ∘ Fin.natAdd nz) ∧
          (x t ∘ Fin.natAdd (nz + ny)) ∘ (Fin.castAdd nz ∘ Fin.natAdd ny) =
            matAct Auz ((x t ∘ Fin.castAdd _) ∘ Fin.castAdd ny) +
              matAct Auμ ((x t ∘ Fin.castAdd _) ∘ Fin.natAdd nz) ∧
          (x t ∘ Fin.natAdd (nz + ny)) ∘ Fin.natAdd (ny + nu) =
            matAct Amz ((x t ∘ Fin.castAdd _) ∘ Fin.castAdd ny) +
              matAct Amμ ((x t ∘ Fin.castAdd _) ∘ Fin.natAdd nz) := by
  have hΦ : ∀ (j : ℕ) (a b : Fin 0), ‖((0 : Matrix (Fin 0) (Fin 0) ℂ) ^ j) a b‖ ≤ 0 :=
    fun _ a => a.elim0
  obtain ⟨Ayk, Ayz', Akk, Akz, hK⟩ := klein_simplified_form E hreg hQ hZ hS hT hord hZ11 hcirc
    (C := (0 : Matrix _ (Fin 0) ℂ)) 0 hΦ
  refine ⟨Akk.submatrix (Fin.castAdd ny) (Fin.castAdd ny),
    Akk.submatrix (Fin.castAdd ny) (Fin.natAdd nz),
    Akk.submatrix (Fin.natAdd nz) (Fin.castAdd ny), Akk.submatrix (Fin.natAdd nz) (Fin.natAdd nz),
    Ayk.submatrix (Fin.castAdd nz ∘ Fin.castAdd nu) (Fin.castAdd ny),
    Ayk.submatrix (Fin.castAdd nz ∘ Fin.castAdd nu) (Fin.natAdd nz),
    Ayk.submatrix (Fin.castAdd nz ∘ Fin.natAdd ny) (Fin.castAdd ny),
    Ayk.submatrix (Fin.castAdd nz ∘ Fin.natAdd ny) (Fin.natAdd nz),
    Ayk.submatrix (Fin.natAdd (ny + nu)) (Fin.castAdd ny),
    Ayk.submatrix (Fin.natAdd (ny + nu)) (Fin.natAdd nz), ?_⟩
  intro ε x hx hxs hxa hz hμ t
  have h0 : ∀ (M : Matrix (Fin (nz + ny)) (Fin 0) ℂ) (v : Fin 0 → V), matAct M v = 0 :=
    fun M v => funext fun i => by simp [matAct]
  have h0' : ∀ (M : Matrix (Fin ((ny + nu) + nz)) (Fin 0) ℂ) (v : Fin 0 → V), matAct M v = 0 :=
    fun M v => funext fun i => by simp [matAct]
  obtain ⟨hy, hk⟩ := hK (fun _ => 0) (fun t => Fin.append (matAct C (ε t)) 0) x
    ⟨1, one_pos, fun _ a => a.elim0⟩ (fun _ a => a.elim0) (fun _ => funext fun a => a.elim0)
    hx hxs hxa (fun t i => by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]
        exact hz t i
      · rw [Fin.append_right, hμ t i, sub_self]
        rfl) t
  rw [h0', add_zero] at hy
  rw [h0, add_zero] at hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hk, Pi.add_comp, klS_append_castAdd, klS_matAct_blocks]
  · rw [hk, Pi.add_comp, klS_append_natAdd, klS_matAct_blocks, add_zero]
  · rw [hy, klS_matAct_blocks]
  · rw [hy, klS_matAct_blocks]
  · rw [hy, klS_matAct_blocks]

end Miao.LinearQuadratic

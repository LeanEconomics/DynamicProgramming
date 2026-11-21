/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.StochasticKlein
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# The Klein solution in state-space form

Copied from `EconomicDynamics/RationalExpectations` (module `KleinSimplified`), namespace renamed.

Miao, §2.3.2, p. 57: "We can simplify the solution if we assume that `{z_t}` satisfies (2.1). In
this case, the solution will be of the following form: `y_t = A_yk k_t + A_yz z_t`,
`k_{t+1} = A_kk k_t + A_kz z_t + ξ_{t+1}`" (the book refers to Klein (2000) for details).

* `klS_Ez_of_2_1`: under (2.1)–(2.2), `E_t z_{t+1} = Φz_t`; this is all that is used.
* `klS_sylvester_exists`: if the powers of `N = T₂₂⁻¹S₂₂` tend to zero and the powers of `Φ` are
  bounded, the Sylvester equation `F = NFΦ + W` has a solution (the map `F ↦ F − NFΦ` is
  injective on a finite-dimensional space).
* `klein_simplified_form`: under the hypotheses of `klein_stochastic`, with `E_t z_{t+1} = Φz_t`
  and `Φ` power bounded (e.g. stable, as in Klein (2000)), there are matrices `A_yk`, `A_yz`,
  `A_kk`, `A_kz`, depending only on `A, B, C, Φ` and the QZ form, such that every stable adapted
  solution whose `k` has prediction error `ξ` satisfies the book's two equations for all `t`.
  Explicitly, with `F` the Sylvester solution for `W = −T₂₂⁻¹Q₂C` (so `u_t = Fz_t`):
  `A_yk = Z₂₁Z₁₁⁻¹`, `A_yz = (Z₂₂ − Z₂₁Z₁₁⁻¹Z₁₂)F`, `A_kk = Z₁₁S₁₁⁻¹T₁₁Z₁₁⁻¹` and
  `A_kz = Z₁₁S₁₁⁻¹(T₁₂F − S₁₂FΦ + Q₁C) + Z₁₂FΦ − A_kk Z₁₂F`.

**Departure.** The book takes `{z_t}` to satisfy (2.1); the proof uses only `E_t z_{t+1} = Φz_t`
and needs `Φ` power bounded (the book is silent on `Φ`; Klein (2000) takes it stable).
-/

open Filter Topology

namespace Miao.LinearQuadratic

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Miao, (2.1)–(2.2), p. 45: if `z_{t+1} = Φz_t + Σε_{t+1}` with `E_t ε_{t+1} = 0` and `z`
adapted, then `E_t z_{t+1} = Φz_t`. -/
theorem klS_Ez_of_2_1 (E : CondExpSystem ℂ V) {nz ne : ℕ} (Φ : Matrix (Fin nz) (Fin nz) ℂ)
    (Sig : Matrix (Fin nz) (Fin ne) ℂ) {z : ℕ → Fin nz → V} {ε : ℕ → Fin ne → V}
    (hza : ∀ t, Evec E t (z t) = z t)
    (hrec : ∀ t, z (t + 1) = matAct Φ (z t) + matAct Sig (ε (t + 1)))
    (hε : ∀ t, Evec E t (ε (t + 1)) = 0) (t : ℕ) :
    Evec E t (z (t + 1)) = matAct Φ (z t) := by
  rw [hrec, klS_Evec_add, Evec_matAct, Evec_matAct, hza, hε, klS_matAct_zero, add_zero]

/-! ### The Sylvester equation `F = NFΦ + W` -/

theorem klS_entry_le_ent {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) (a : ι)
    (b : κ) : ‖M a b‖ ≤ klS_ent M :=
  (Finset.single_le_sum (f := fun j => ‖M a j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))

theorem klS_entry_mul_le {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (P : Matrix ι κ ℂ) (G : Matrix κ ρ ℂ) (a : ι) (b : ρ) :
    ‖(P * G) a b‖ ≤ klS_ent P * klS_ent G := by
  calc ‖(P * G) a b‖ = ‖∑ c, P a c * G c b‖ := rfl
    _ ≤ ∑ c, ‖P a c‖ * ‖G c b‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => (norm_mul _ _).le)
    _ ≤ ∑ c, ‖P a c‖ * klS_ent G := Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_left (klS_entry_le_ent G c b) (norm_nonneg _)
    _ = (∑ c, ‖P a c‖) * klS_ent G := by rw [Finset.sum_mul]
    _ ≤ klS_ent P * klS_ent G := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, ‖P i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))
        (klS_ent_nonneg G)

/-- If `Nʲ → 0` and the powers of `Φ` are bounded, `F = NFΦ` forces `F = 0`. -/
theorem klS_sylvester_unique {p q : ℕ} {N : Matrix (Fin p) (Fin p) ℂ}
    {Φ : Matrix (Fin q) (Fin q) ℂ} (hN : Tendsto (fun j => klS_ent (N ^ j)) atTop (𝓝 0))
    {Kb : ℝ} (hΦ : ∀ j a b, ‖(Φ ^ j) a b‖ ≤ Kb) {F : Matrix (Fin p) (Fin q) ℂ}
    (h : F = N * F * Φ) : F = 0 := by
  have hj : ∀ j, F = N ^ j * F * Φ ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc F = N * F * Φ := h
        _ = N * (N ^ j * F * Φ ^ j) * Φ := by rw [← ih]
        _ = N ^ (j + 1) * F * Φ ^ (j + 1) := by
          rw [pow_succ', pow_succ]
          simp only [Matrix.mul_assoc]
  ext a b
  have hb : ∀ j, ‖F a b‖ ≤ q * Kb * klS_ent F * klS_ent (N ^ j) := fun j => by
    calc ‖F a b‖ = ‖(N ^ j * F * Φ ^ j) a b‖ := by rw [← hj j]
      _ = ‖∑ d, (N ^ j * F) a d * (Φ ^ j) d b‖ := rfl
      _ ≤ ∑ d, ‖(N ^ j * F) a d‖ * ‖(Φ ^ j) d b‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => (norm_mul _ _).le)
      _ ≤ ∑ _d : Fin q, klS_ent (N ^ j) * klS_ent F * Kb := Finset.sum_le_sum fun d _ =>
          mul_le_mul (klS_entry_mul_le _ _ a d) (hΦ j d b) (norm_nonneg _)
            (mul_nonneg (klS_ent_nonneg _) (klS_ent_nonneg _))
      _ = q * Kb * klS_ent F * klS_ent (N ^ j) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hlim : Tendsto (fun j => q * Kb * klS_ent F * klS_ent (N ^ j)) atTop (𝓝 0) := by
    simpa using hN.const_mul (q * Kb * klS_ent F)
  have h0 := ge_of_tendsto' hlim hb
  simpa using norm_le_zero_iff.1 h0

/-- The Sylvester equation `F = NFΦ + W` is solvable when `Nʲ → 0` and the powers of `Φ` are
bounded. -/
theorem klS_sylvester_exists {p q : ℕ} {N : Matrix (Fin p) (Fin p) ℂ}
    {Φ : Matrix (Fin q) (Fin q) ℂ} (hN : Tendsto (fun j => klS_ent (N ^ j)) atTop (𝓝 0))
    {Kb : ℝ} (hΦ : ∀ j a b, ‖(Φ ^ j) a b‖ ≤ Kb) (W : Matrix (Fin p) (Fin q) ℂ) :
    ∃ F : Matrix (Fin p) (Fin q) ℂ, F = N * F * Φ + W := by
  let L : Matrix (Fin p) (Fin q) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ :=
    { toFun := fun F => F - N * F * Φ
      map_add' := fun F G => by
        simp only [Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c F => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, RingHom.id_apply] }
  have hinj : Function.Injective L := (injective_iff_map_eq_zero L).2 fun F hF => by
    have h1 : F - N * F * Φ = 0 := hF
    exact klS_sylvester_unique hN hΦ (sub_eq_zero.1 h1)
  obtain ⟨F, hF⟩ := LinearMap.injective_iff_surjective.1 hinj W
  have h1 : F - N * F * Φ = W := hF
  exact ⟨F, by rw [← h1]; abel⟩

/-! ### The algebra of the simplified form -/

/-- Miao, p. 57, the `y` equation: from `k = Z₁₁s + Z₁₂u`, `y = Z₂₁s + Z₂₂u` and `u = Fz`,
`y = Z₂₁Z₁₁⁻¹k + (Z₂₂ − Z₂₁Z₁₁⁻¹Z₁₂)Fz`. -/
theorem klS_simpl_y {m p r q : ℕ} {Z11 : Matrix (Fin m) (Fin m) ℂ}
    {Z12 : Matrix (Fin m) (Fin p) ℂ} {Z21 : Matrix (Fin r) (Fin m) ℂ}
    {Z22 : Matrix (Fin r) (Fin p) ℂ} {F : Matrix (Fin p) (Fin q) ℂ} (hZ11 : Z11.det ≠ 0)
    {k s : Fin m → V} {u : Fin p → V} {yv : Fin r → V} {zt : Fin q → V}
    (hk : k = matAct Z11 s + matAct Z12 u) (hy : yv = matAct Z21 s + matAct Z22 u)
    (hu : u = matAct F zt) :
    yv = matAct (Z21 * Z11⁻¹) k + matAct ((Z22 - Z21 * Z11⁻¹ * Z12) * F) zt := by
  have hs : s = matAct Z11⁻¹ (k - matAct Z12 u) := by
    rw [hk, add_sub_cancel_right, klS_matAct_inv_mul hZ11]
  rw [hy, hs, hu]
  simp only [klS_matAct_sub, klS_sub_matAct, matAct_mul, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- Miao, p. 57, the `k` equation: from `k_t = Z₁₁s_t + Z₁₂u_t`,
`E_t k_{t+1} = Z₁₁E_t s_{t+1} + Z₁₂E_t u_{t+1}`, the `s`-block, `u_t = Fz_t`,
`E_t u_{t+1} = FΦz_t`, `c¹_t = Q₁Cz_t` and `k_{t+1} = E_t k_{t+1} + ξ_{t+1}`,
`k_{t+1} = A_kk k_t + A_kz z_t + ξ_{t+1}`. -/
theorem klS_simpl_k {m p q : ℕ} {S11 T11 Z11 : Matrix (Fin m) (Fin m) ℂ}
    {S12 T12 Z12 : Matrix (Fin m) (Fin p) ℂ} {F : Matrix (Fin p) (Fin q) ℂ}
    {Φ : Matrix (Fin q) (Fin q) ℂ} {QCK : Matrix (Fin m) (Fin q) ℂ} (hS11 : S11.det ≠ 0)
    (hZ11 : Z11.det ≠ 0) {k k' Ek' s Es' c1 ξ' : Fin m → V} {u Eu' : Fin p → V}
    {zt : Fin q → V} (hk : k = matAct Z11 s + matAct Z12 u)
    (hEk' : Ek' = matAct Z11 Es' + matAct Z12 Eu')
    (h1 : matAct S11 Es' + matAct S12 Eu' = matAct T11 s + matAct T12 u + c1)
    (hu : u = matAct F zt) (hEu : Eu' = matAct F (matAct Φ zt)) (hc : c1 = matAct QCK zt)
    (hk' : k' = Ek' + ξ') :
    k' = matAct (Z11 * (S11⁻¹ * T11) * Z11⁻¹) k +
      matAct (Z11 * (S11⁻¹ * (T12 * F - S12 * (F * Φ) + QCK)) + Z12 * (F * Φ) -
        Z11 * (S11⁻¹ * T11) * Z11⁻¹ * (Z12 * F)) zt + ξ' := by
  have hs : s = matAct Z11⁻¹ (k - matAct Z12 u) := by
    rw [hk, add_sub_cancel_right, klS_matAct_inv_mul hZ11]
  rw [hk', hEk', (eq_klein_Es hS11 _ _ _ _ _).1 h1, hs, hEu, hc, hu]
  simp only [matAct_add, klS_matAct_sub, klS_add_matAct, klS_sub_matAct, matAct_mul,
    Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **The simplified Klein solution** (Miao, p. 57; Klein (2000)). Under the hypotheses of
`klein_stochastic` on `A, B, C` and the QZ form, let `Φ` have bounded powers. There are matrices
`A_yk, A_yz, A_kk, A_kz` (depending only on `A, B, C, Φ, Q, Z`) such that for every stable
adapted `{z_t}` with `E_t z_{t+1} = Φz_t` (e.g. (2.1), `klS_Ez_of_2_1`) and every stable adapted
solution `x = (k, y)` of (2.11) whose `k` has prediction error `ξ`,
`y_t = A_yk k_t + A_yz z_t` and `k_{t+1} = A_kk k_t + A_kz z_t + ξ_{t+1}`. -/
theorem klein_simplified_form [CompleteSpace V] (E : CondExpSystem ℂ V) {nk ny nz : ℕ}
    {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ} {C : Matrix (Fin (nk + ny)) (Fin nz) ℂ}
    (hreg : IsRegular A B) {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) (Φ : Matrix (Fin nz) (Fin nz) ℂ) {Kb : ℝ}
    (hΦ : ∀ j a b, ‖(Φ ^ j) a b‖ ≤ Kb) :
    ∃ (Ayk : Matrix (Fin ny) (Fin nk) ℂ) (Ayz : Matrix (Fin ny) (Fin nz) ℂ)
      (Akk : Matrix (Fin nk) (Fin nk) ℂ) (Akz : Matrix (Fin nk) (Fin nz) ℂ),
      ∀ (z : ℕ → Fin nz → V) (ξ : ℕ → Fin nk → V) (x : ℕ → Fin (nk + ny) → V),
        IsStableProc z → IsAdaptedV E z → (∀ t, Evec E t (z (t + 1)) = matAct Φ (z t)) →
        IsRESolution E A B C z x → IsStableProc x → IsAdaptedV E x →
        (∀ t i, x (t + 1) (Fin.castAdd ny i) - E.E t (x (t + 1) (Fin.castAdd ny i)) =
          ξ (t + 1) i) →
        ∀ t, x t ∘ Fin.natAdd nk = matAct Ayk (x t ∘ Fin.castAdd ny) + matAct Ayz (z t) ∧
          x (t + 1) ∘ Fin.castAdd ny =
            matAct Akk (x t ∘ Fin.castAdd ny) + matAct Akz (z t) + ξ (t + 1) := by
  have hdiag := diag_off_circle hreg hQ hZ hS hT hcirc
  have hS11 := det_S11_ne_zero hS hord
  have hT22 := det_T22_ne_zero hT hord hdiag
  have hN := klS_summable_ent (summable_Mu hS hT hord hdiag)
  obtain ⟨F, hF⟩ := klS_sylvester_exists hN.tendsto_atTop_zero hΦ
    (-(((Q * B * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *
      (Q * C).submatrix (Fin.natAdd nk) id))
  refine ⟨Z.submatrix (Fin.natAdd nk) (Fin.castAdd ny) *
      (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹,
    (Z.submatrix (Fin.natAdd nk) (Fin.natAdd nk) - Z.submatrix (Fin.natAdd nk) (Fin.castAdd ny) *
      (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
        Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk)) * F,
    Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny) *
      (((Q * A * Z).submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
        (Q * B * Z).submatrix (Fin.castAdd ny) (Fin.castAdd ny)) *
      (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹,
    Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny) *
        (((Q * A * Z).submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
          ((Q * B * Z).submatrix (Fin.castAdd ny) (Fin.natAdd nk) * F -
            (Q * A * Z).submatrix (Fin.castAdd ny) (Fin.natAdd nk) * (F * Φ) +
              (Q * C).submatrix (Fin.castAdd ny) id)) +
      Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk) * (F * Φ) -
      Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny) *
        (((Q * A * Z).submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
          (Q * B * Z).submatrix (Fin.castAdd ny) (Fin.castAdd ny)) *
        (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
        (Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk) * F), ?_⟩
  intro z ξ x hz hza hzΦ hx hxs hxa hp
  have hza' : ∀ t, Evec E t (z t) = z t := fun t => funext (hza t)
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hback : ∀ v : Fin (nk + ny) → V, matAct Z (matAct (star Z) v) = v := fun v => by
    rw [matAct_mul, hZZ, matAct_one]
  have h := (klS_isRESolution_iff E hQ hZ z x).1 hx
  have hb := fun t => (klS_blocks_iff hS hT _ _ _).1 (h t)
  -- the `u`-block: `u_t = Fz_t`
  have hwS : IsStableProc fun t =>
      -matAct ((Q * B * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹
        (matAct Q (matAct C (z t)) ∘ Fin.natAdd nk) := by
    obtain ⟨M, hM, hM'⟩ := klS_stable_matAct (klS_stable_comp (klS_stable_matAct
      (klS_stable_matAct hz C) Q) (Fin.natAdd nk))
      ((Q * B * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹
    exact ⟨M, hM, fun t i => by simp only [Pi.neg_apply, norm_neg]; exact hM' t i⟩
  obtain ⟨Wb, -, hW⟩ := klS_stable_bound hwS
  have hu : ∀ t, matAct (star Z) (x t) ∘ Fin.natAdd nk = matAct F (z t) := fun t =>
    (klS_eq_fwd E hN hW (u := fun t => matAct (star Z) (x t) ∘ Fin.natAdd nk)
      (klS_stable_comp (klS_stable_matAct hxs _) _)
      (fun t => by
        rw [klS_Evec_comp, Evec_matAct, show Evec E t (x t) = x t from funext (hxa t)])
      (fun t => (klS_solve_fwd hT22 _ _ _).1 (hb t).2) t).trans
    (klS_eq_fwd E hN hW (u := fun t => matAct F (z t)) (klS_stable_matAct hz F)
      (fun t => by
        rw [Evec_matAct, hza'])
      (fun t => by
        rw [Evec_matAct, hzΦ]
        conv_lhs => rw [hF]
        simp only [klS_add_matAct, klS_neg_matAct, matAct_mul, klS_matAct_comp,
          Matrix.mul_assoc]) t).symm
  have hxK : ∀ t, x t ∘ Fin.castAdd ny =
      matAct (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))
          (matAct (star Z) (x t) ∘ Fin.castAdd ny) +
        matAct (Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk))
          (matAct (star Z) (x t) ∘ Fin.natAdd nk) := fun t => by
    have := klS_matAct_blocks Z (Fin.castAdd ny) (matAct (star Z) (x t))
    rwa [hback] at this
  have hxU : ∀ t, x t ∘ Fin.natAdd nk =
      matAct (Z.submatrix (Fin.natAdd nk) (Fin.castAdd ny))
          (matAct (star Z) (x t) ∘ Fin.castAdd ny) +
        matAct (Z.submatrix (Fin.natAdd nk) (Fin.natAdd nk))
          (matAct (star Z) (x t) ∘ Fin.natAdd nk) := fun t => by
    have := klS_matAct_blocks Z (Fin.natAdd nk) (matAct (star Z) (x t))
    rwa [hback] at this
  intro t
  refine ⟨klS_simpl_y hZ11 (hxK t) (hxU t) (hu t), klS_simpl_k hS11 hZ11
    (Ek' := Evec E t (x (t + 1) ∘ Fin.castAdd ny)) (hxK t) ?_ (hb t).1 (hu t) ?_ ?_ ?_⟩
  · rw [hxK (t + 1), klS_Evec_add, Evec_matAct, Evec_matAct, klS_Evec_comp, klS_Evec_comp]
  · rw [← klS_Evec_comp, hu (t + 1), Evec_matAct, hzΦ]
  · rw [matAct_mul]
    rfl
  · funext i
    change x (t + 1) (Fin.castAdd ny i) = E.E t (x (t + 1) (Fin.castAdd ny i)) + ξ (t + 1) i
    rw [← hp t i]
    abel

end Miao.LinearQuadratic

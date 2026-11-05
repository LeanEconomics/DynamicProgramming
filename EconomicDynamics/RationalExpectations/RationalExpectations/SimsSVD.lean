/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.Sims
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The Sims method: SVD, uniqueness of prediction errors, sunspots

Miao, §2.3.3, pp. 62–64, continuing `Sims`. The SVD (2.25) is taken as a hypothesis
(`IsThinSVD B U.1 D₁₁ V.1`: `B = U.1D₁₁V.1ᴴ`, orthonormal columns, `D₁₁` invertible; for the
sunspot part also `V.2` with `V.1ᴴV.2 = 0`, `V.2ᴴV.2 = I`, `V.1V.1ᴴ + V.2V.2ᴴ = I`); the
existence of an SVD is not formalised (it is not needed: Assumption 2.3.2 is characterised by
kernels in `simsAssumption2_iff_ker`).

* The column-space test: `colspace_iff`, `colspace_iff_thin`, `colspace_printed_false`.
* `Λ` and `Ξ` (p. 62): `lambda_formula` (any `r`), `xi_formula` (`m = r`), `xi_residual`
  (p. 63, `Q₁.Π − ΞQ₂.Π = Q₁.Π(I − V.1V.1ᴴ)`), `svd_injective_iff` (`m = r` iff `Q₂.Π`
  has full column rank).
* Uniqueness: `SimsYUnique`, `SimsPairUnique`; `simsY_unique_iff` (with a rich filtration,
  `y` is unique iff Assumption 2.3.2); `corollary_2_3_1` (the pair `(y, η)` is unique iff
  `m = r`); `corollary_2_3_1_printed_false`; `lubik_schorfheide`.
* Sunspots (pp. 63–64): `eq_2_26`, `eq_sunspot_identity`, `sunspot_term_simplified`,
  `simsTheta3`, `sunspot_solution` (every stable solution is
  `y_t = Θ₁y_{t−1} + Θ₂ε_t + Θ₃e_t`, `e_t = V.2ᴴη_t`), `sunspot_existence`.

**Corrections.**
* The column-space test "If `B`'s SVD is `TCW`, `A`'s column space includes `B`'s iff
  `(I − UUᴴ)T = 0`" is vacuous with the full unitary `U` (`colspace_printed_false`); the correct
  test uses the first `r` columns: `(I − U.1U.1ᴴ)B = 0`, equivalently `(I − U.1U.1ᴴ)T.1 = 0`.
* Corollary 2.3.1 ("given Assumption 2.3.1, uniqueness iff `m = r`") is true for the pair
  `(y, η)` (and needs no Assumption 2.3.1) but false for `y`, which is what Theorem 2.3.1 calls
  the solution: with a prediction error that enters nowhere (a zero column of `Π`), `m > r`
  and `y` is unique (`corollary_2_3_1_printed_false`). The correct condition for `y` is
  Assumption 2.3.2 (`simsY_unique_iff`); `m = r` implies it (`xi_formula`), and the two agree
  when `Π` has full column rank.
* Likewise "if `m > r` there are infinitely many stable solutions" (Lubik–Schorfheide) holds
  for `(y, η)` (`lubik_schorfheide`, with a rich filtration) but not for `y`.
* The sunspot formulas (2.26), the identity on p. 63 and `Θ₃` are correct as printed (with
  `V.1′ = V.1ᴴ`); the factor `I − V.1V.1ᴴ` in front of `V.2` is redundant
  (`sunspot_term_simplified`). The representation `sunspot_solution` needs neither
  Assumption 2.3.1 nor 2.3.2.
-/

namespace Miao.RationalExpectations

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### Thin singular value decompositions -/

variable {p m r : ℕ} (B : Matrix (Fin p) (Fin m) ℂ) (U1 : Matrix (Fin p) (Fin r) ℂ)
  (D : Matrix (Fin r) (Fin r) ℂ) (V1 : Matrix (Fin m) (Fin r) ℂ) in
/-- A thin singular value decomposition `B = U.1 D₁₁ V.1ᴴ` (Miao, (2.25), p. 62): `U.1` and `V.1`
have orthonormal columns and `D₁₁` is invertible; `r` is the rank. (That `D₁₁` is diagonal
with positive entries is not used anywhere.) Here `ᴴ` is `star`. -/
structure IsThinSVD : Prop where
  eq : B = U1 * D * V1ᴴ
  U1_orth : U1ᴴ * U1 = 1
  V1_orth : V1ᴴ * V1 = 1
  det_D : D.det ≠ 0

/-- `(I − U.1U.1ᴴ)U.1 = 0`. -/
theorem simsH_proj_mul {p r : ℕ} {U1 : Matrix (Fin p) (Fin r) ℂ} (h : U1ᴴ * U1 = 1) :
    (1 - U1 * U1ᴴ) * U1 = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_one, sub_self]

/-- `D₁₁⁻¹U.1ᴴB = V.1ᴴ`. -/
theorem simsH_svd_left {p m r : ℕ} {B : Matrix (Fin p) (Fin m) ℂ} {U1 : Matrix (Fin p) (Fin r) ℂ}
    {D : Matrix (Fin r) (Fin r) ℂ} {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD B U1 D V1) :
    D⁻¹ * U1ᴴ * B = V1ᴴ := by
  rw [h.eq, show D⁻¹ * U1ᴴ * (U1 * D * V1ᴴ) = D⁻¹ * (U1ᴴ * U1) * D * V1ᴴ by
    simp only [Matrix.mul_assoc], h.U1_orth, Matrix.mul_one,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h.det_D), Matrix.one_mul]

/-- The explicit `Λ` (Miao, p. 62): if `(I − U.1U.1ᴴ)C = 0` then `C = B(V.1D₁₁⁻¹U.1ᴴC)`. -/
theorem simsH_colspace_explicit {p m r k : ℕ} {B : Matrix (Fin p) (Fin m) ℂ}
    {U1 : Matrix (Fin p) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD B U1 D V1) {C : Matrix (Fin p) (Fin k) ℂ}
    (hC : (1 - U1 * U1ᴴ) * C = 0) : C = B * (V1 * D⁻¹ * U1ᴴ * C) := by
  have e : B * (V1 * D⁻¹ * U1ᴴ * C) = U1 * D * (V1ᴴ * V1) * D⁻¹ * U1ᴴ * C := by
    rw [h.eq]
    simp only [Matrix.mul_assoc]
  rw [e, h.V1_orth, Matrix.mul_one, Matrix.mul_assoc U1 D D⁻¹,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h.det_D), Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hC
  exact hC

/-- Miao, p. 62, the column-space test, corrected. The book states "If `B`'s SVD is `TCW`,
`A`'s column space includes `B`'s iff `(I − UUᴴ)T = 0`", which with the full unitary `U` of
`A`'s SVD is vacuous (`colspace_printed_false`). The correct test uses the first `r` columns
`U.1`: with `A = U.1D₁₁V.1ᴴ`, `col(C) ⊆ col(A)` iff `(I − U.1U.1ᴴ)C = 0`. -/
theorem colspace_iff {p m r k : ℕ} {A : Matrix (Fin p) (Fin m) ℂ}
    {U1 : Matrix (Fin p) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD A U1 D V1) (C : Matrix (Fin p) (Fin k) ℂ) :
    (∃ Λ, C = A * Λ) ↔ (1 - U1 * U1ᴴ) * C = 0 := by
  constructor
  · rintro ⟨Λ, rfl⟩
    rw [h.eq, show (1 - U1 * U1ᴴ) * (U1 * D * V1ᴴ * Λ) =
      (1 - U1 * U1ᴴ) * U1 * D * V1ᴴ * Λ by simp only [Matrix.mul_assoc],
      simsH_proj_mul h.U1_orth]
    simp only [Matrix.zero_mul]
  · intro hC
    exact ⟨_, simsH_colspace_explicit h hC⟩

/-- Miao, p. 62, the column-space test in terms of `C`'s own SVD `C = T.1C₁₁W.1ᴴ`: `col(C) ⊆
col(A)` iff `(I − U.1U.1ᴴ)T.1 = 0`, with the thin factors `U.1`, `T.1` (the reconstruction of
the garbled printed test). -/
theorem colspace_iff_thin {p m r k q : ℕ} {A : Matrix (Fin p) (Fin m) ℂ}
    {U1 : Matrix (Fin p) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD A U1 D V1) {C : Matrix (Fin p) (Fin k) ℂ}
    {T1 : Matrix (Fin p) (Fin q) ℂ} {C1 : Matrix (Fin q) (Fin q) ℂ}
    {W1 : Matrix (Fin k) (Fin q) ℂ} (hC : IsThinSVD C T1 C1 W1) :
    (∃ Λ, C = A * Λ) ↔ (1 - U1 * U1ᴴ) * T1 = 0 := by
  rw [colspace_iff h]
  constructor
  · intro h0
    have e : T1 = C * (W1 * C1⁻¹) := by
      rw [hC.eq, show T1 * C1 * W1ᴴ * (W1 * C1⁻¹) = T1 * (C1 * (W1ᴴ * W1) * C1⁻¹) by
        simp only [Matrix.mul_assoc], hC.V1_orth, Matrix.mul_one,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hC.det_D), Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, h0, Matrix.zero_mul]
  · intro h0
    rw [hC.eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.zero_mul]

/-- **Counterexample to the printed column-space test** (Miao, p. 62). With the full unitary `U`
of `A`'s SVD, `(I − UUᴴ)T = 0` always holds, yet for `A = 0`, `C = 1` (`1 × 1`,
`U = V = T = W = C₁₁ = 1`, `D = 0`) the column space of `A` does not include that of `C`. -/
theorem colspace_printed_false :
    ∃ (A C U D Vm T C1 W : Matrix (Fin 1) (Fin 1) ℂ),
      U ∈ Matrix.unitaryGroup (Fin 1) ℂ ∧ Vm ∈ Matrix.unitaryGroup (Fin 1) ℂ ∧
      T ∈ Matrix.unitaryGroup (Fin 1) ℂ ∧ W ∈ Matrix.unitaryGroup (Fin 1) ℂ ∧
      A = U * D * star Vm ∧ C = T * C1 * star W ∧ (1 - U * star U) * T = 0 ∧
      ¬ ∃ Λ, C = A * Λ := by
  refine ⟨0, 1, 1, 0, 1, 1, 1, 1, one_mem _, one_mem _, one_mem _, one_mem _, by simp, by simp,
    by simp, ?_⟩
  rintro ⟨Λ, hΛ⟩
  have := congrFun (congrFun hΛ 0) 0
  simp at this

/-- Miao, p. 62: "`Λ = V.1D₁₁⁻¹U.1ᴴ(Q₂.Ψ)`". Under Assumption 2.3.1 this `Λ` works, whether or
not `m = r`. -/
theorem lambda_formula {ns nu nε m r : ℕ} {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {U1 : Matrix (Fin nu) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD (simsBot Q * Pm) U1 D V1)
    (hA1 : SimsAssumption1 Q Ψ Pm) :
    simsBot Q * Ψ = simsBot Q * Pm * (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) := by
  obtain ⟨Λ, hΛ⟩ := hA1
  exact simsH_colspace_explicit h ((colspace_iff h _).1 ⟨Λ, hΛ⟩)

/-- Miao, p. 63: with `Ξ = Q₁.ΠV.1D₁₁⁻¹U.1ᴴ`, `Q₁.Π − ΞQ₂.Π = Q₁.Π(I − V.1V.1ᴴ)` (as printed;
"not equal to zero in general"). -/
theorem xi_residual {p q m r : ℕ} {B : Matrix (Fin p) (Fin m) ℂ}
    {U1 : Matrix (Fin p) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD B U1 D V1) (C : Matrix (Fin q) (Fin m) ℂ) :
    C - C * V1 * D⁻¹ * U1ᴴ * B = C * (1 - V1 * V1ᴴ) := by
  rw [show C * V1 * D⁻¹ * U1ᴴ * B = C * V1 * (D⁻¹ * U1ᴴ * B) by
    simp only [Matrix.mul_assoc], simsH_svd_left h, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_assoc]

/-- Miao, p. 62: "If `m = r` … `Ξ = (Q₁.Π)V.1D₁₁⁻¹U.1ᴴ`" satisfies Assumption 2.3.2. With
`m = r`, `V.1` is square with `V.1ᴴV.1 = I`, hence `V.1V.1ᴴ = I`. -/
theorem xi_formula {p q m : ℕ} {B : Matrix (Fin p) (Fin m) ℂ} {U1 : Matrix (Fin p) (Fin m) ℂ}
    {D : Matrix (Fin m) (Fin m) ℂ} {V1 : Matrix (Fin m) (Fin m) ℂ} (h : IsThinSVD B U1 D V1)
    (C : Matrix (Fin q) (Fin m) ℂ) : C = C * V1 * D⁻¹ * U1ᴴ * B := by
  have hV : V1 * V1ᴴ = 1 := mul_eq_one_comm.1 h.V1_orth
  have := xi_residual h C
  rw [hV, sub_self, Matrix.mul_zero, sub_eq_zero] at this
  exact this

/-- `m = r` means that `Q₂.Π` has full column rank: for a thin SVD `B = U.1D₁₁V.1ᴴ` of an
`n_u × m` matrix of rank `r`, `Bv = 0 → v = 0` iff `r = m`. -/
theorem svd_injective_iff {p m r : ℕ} {B : Matrix (Fin p) (Fin m) ℂ}
    {U1 : Matrix (Fin p) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD B U1 D V1) :
    (∀ v, B *ᵥ v = 0 → v = 0) ↔ r = m := by
  have hker : ∀ v, B *ᵥ v = 0 ↔ V1ᴴ *ᵥ v = 0 := fun v => by
    constructor
    · intro hv
      rw [← simsH_svd_left h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    · intro hv
      rw [h.eq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hrm : r ≤ m := by
    have hinj : Function.Injective (Matrix.mulVecLin V1) := by
      intro a b hab
      have := congrArg (V1ᴴ *ᵥ ·) hab
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h.V1_orth,
        Matrix.one_mulVec] using this
    simpa only [Module.finrank_fin_fun] using LinearMap.finrank_le_finrank_of_injective hinj
  constructor
  · intro hinj
    by_contra hne
    have hlt : Module.finrank ℂ (Fin r → ℂ) < Module.finrank ℂ (Fin m → ℂ) := by
      simp only [Module.finrank_fin_fun]
      omega
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1
      (LinearMap.ker_ne_bot_of_finrank_lt (f := Matrix.mulVecLin (V1ᴴ)) hlt)
    exact hv0 (hinj v ((hker v).2 hv))
  · rintro rfl v hv
    have hV : V1 * V1ᴴ = 1 := mul_eq_one_comm.1 h.V1_orth
    rw [← Matrix.one_mulVec v, ← hV, ← Matrix.mulVec_mulVec, (hker v).1 hv, Matrix.mulVec_zero]

/-! ### Uniqueness of `y` and of `(y, η)` -/

/-- Uniqueness of the stable solution `y` of (2.20): for every exogenous shock, two stable
solutions with the same initial value coincide (their prediction errors may differ). -/
def SimsYUnique {n nε m : ℕ} (E : CondExpSystem ℂ V) (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ)
    (Ψ : Matrix (Fin n) (Fin nε) ℂ) (Pm : Matrix (Fin n) (Fin m) ℂ) : Prop :=
  ∀ ε : ℕ → Fin nε → V, IsSimsShock E ε → ∀ (y y' : ℕ → Fin n → V) (η η' : ℕ → Fin m → V),
    IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η → IsStableProc y → IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y' η' →
      IsStableProc y' → y 0 = y' 0 → y = y'

/-- Uniqueness of the pair `(y, η)` (with `η_t` for `t ≥ 1`; `η₀` does not enter (2.20)). -/
def SimsPairUnique {n nε m : ℕ} (E : CondExpSystem ℂ V) (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ)
    (Ψ : Matrix (Fin n) (Fin nε) ℂ) (Pm : Matrix (Fin n) (Fin m) ℂ) : Prop :=
  ∀ ε : ℕ → Fin nε → V, IsSimsShock E ε → ∀ (y y' : ℕ → Fin n → V) (η η' : ℕ → Fin m → V),
    IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η → IsStableProc y → IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y' η' →
      IsStableProc y' → y 0 = y' 0 → y = y' ∧ ∀ t, η (t + 1) = η' (t + 1)

/-- Solutions of (2.20) add: a solution for `ε` plus a solution of the homogeneous system
(`ε = 0`) is a solution for `ε`. -/
theorem simsH_sol_add {n nε m : ℕ} {E : CondExpSystem ℂ V} {Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ}
    {Ψ : Matrix (Fin n) (Fin nε) ℂ} {Pm : Matrix (Fin n) (Fin m) ℂ} {ε : ℕ → Fin nε → V}
    {y d : ℕ → Fin n → V} {η h : ℕ → Fin m → V} (h1 : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η)
    (h2 : IsSimsSolution E Γ₀ Γ₁ Ψ Pm 0 d h) : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε (y + d) (η + h) := by
  obtain ⟨a1, b1, c1, e1⟩ := h1
  obtain ⟨a2, b2, c2, e2⟩ := h2
  refine ⟨fun t i => ?_, fun t i => ?_, fun t i => ?_, fun t => ?_⟩
  · simp only [Pi.add_apply, map_add, a1 t i, a2 t i]
  · simp only [Pi.add_apply, map_add, b1 t i, b2 t i]
  · simp only [Pi.add_apply, map_add, c1 t i, c2 t i, add_zero]
  · have := e2 t
    rw [Pi.zero_apply, klS_matAct_zero, add_zero] at this
    simp only [Pi.add_apply, matAct_add, e1 t, this]
    abel

/-- A prediction error `η_t = vζ_t` in the kernel of `Q₂.Π` (`ζ` a stable adapted scalar
martingale difference) drives a stable solution of the homogeneous system with `y₀ = 0`. -/
theorem simsH_perturb [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ζ : ℕ → V} (hζa : ∀ t, E.E t (ζ t) = ζ t) (hζm : ∀ t, E.E t (ζ (t + 1)) = 0) {M : ℝ}
    (hζb : ∀ t, ‖ζ t‖ ≤ M) {v : Fin m → ℂ} (hv : (simsBot Q * Pm) *ᵥ v = 0) :
    ∃ d, IsSimsSolution E Γ₀ Γ₁ Ψ Pm (0 : ℕ → Fin nε → V) d (fun t k => v k • ζ t) ∧
      IsStableProc d ∧ d 0 = 0 := by
  obtain ⟨hηa, hηm, hηs⟩ := simsH_rich_shock E hζa hζm hζb v
  exact simsH_core_exists E hqz (simsH_zero_shock E).1 (simsH_zero_shock E).2.2 hηa hηm hηs
    (fun t => by
      rw [Pi.zero_apply, klS_matAct_zero, zero_add, simsH_matAct_smul, simsH_matAct_smul,
        Matrix.mulVec_mulVec, hv]
      funext i
      simp) 0 (klS_Evec_zero E 0) (klS_matAct_zero _)

/-- Miao, pp. 61–62, uniqueness of `y` characterised: with a rich filtration, the stable
solution `y` is unique (given `y₀`, for every shock) iff Assumption 2.3.2 holds, i.e. iff
`ker(Q₂.Π) ⊆ ker(Q₁.Π)` (`simsAssumption2_iff_ker`). -/
theorem simsY_unique_iff [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} :
    SimsYUnique E Γ₀ Γ₁ Ψ Pm ↔ SimsAssumption2 Q Pm := by
  constructor
  · intro H
    exact theorem_2_3_1_necessity_2 E hrich hqz fun y η hsol hy hy0 => H 0 (simsH_zero_shock E)
      y 0 η 0 hsol hy (simsH_zero_solution E Γ₀ Γ₁ Ψ Pm) simsH_stable_zero hy0
  · intro hA2 ε hε y y' η η' h1 h2 h3 h4 h0
    exact theorem_2_3_1_uniqueness E hqz hA2 hε.2.1 h1 h2 h3 h4 h0

/-- **Corollary 2.3.1** (Miao, p. 62), correct form. Let `Q₂.Π = U.1D₁₁V.1ᴴ` be a thin SVD of
rank `r` and let the filtration be rich. Then the stable solution together with its prediction
error, `(y, η)`, is unique (for every shock, given `y₀`) iff `m = r`. ("Given Assumption 2.3.1"
is not needed.) If `m = r`, Assumption 2.3.2 holds automatically (`xi_formula`). For the
uniqueness of `y` alone, `m = r` is not necessary (`corollary_2_3_1_printed_false`); the
condition is Assumption 2.3.2 (`simsY_unique_iff`). -/
theorem corollary_2_3_1 [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m r : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} {U1 : Matrix (Fin nu) (Fin r) ℂ}
    {D : Matrix (Fin r) (Fin r) ℂ} {V1 : Matrix (Fin m) (Fin r) ℂ}
    (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1) :
    SimsPairUnique E Γ₀ Γ₁ Ψ Pm ↔ r = m := by
  constructor
  · intro H
    by_contra hne
    have hni := mt (svd_injective_iff hsvd).1 hne
    push Not at hni
    obtain ⟨v, hv, hv0⟩ := hni
    obtain ⟨ζ, hζa, hζm, ⟨M, hζb⟩, hζ1⟩ := hrich
    obtain ⟨d, hd, hds, hd0⟩ := simsH_perturb E hqz (Ψ := Ψ) hζa hζm hζb hv
    obtain ⟨-, hη⟩ := H 0 (simsH_zero_shock E) 0 d 0 _ (simsH_zero_solution E Γ₀ Γ₁ Ψ Pm)
      simsH_stable_zero hd hds hd0.symm
    refine hv0 (funext fun k => ?_)
    have := congrFun (hη 0) k
    simp only [Pi.zero_apply] at this
    exact (smul_eq_zero.1 this.symm).resolve_right hζ1
  · rintro rfl ε hε y y' η η' h1 h2 h3 h4 h0
    have hinj := (svd_injective_iff hsvd).2 rfl
    have hA2 : SimsAssumption2 Q Pm := (simsAssumption2_iff_ker Q Pm).2 fun v hv => by
      rw [hinj v hv, Matrix.mulVec_zero]
    refine ⟨theorem_2_3_1_uniqueness E hqz hA2 hε.2.1 h1 h2 h3 h4 h0, fun t => ?_⟩
    have e1 := eq_2_23 E hqz hε.2.1 h1 h2 t
    have e2 := eq_2_23 E hqz hε.2.1 h3 h4 t
    rw [matAct_add, matAct_mul, matAct_mul] at e1 e2
    have e3 : matAct (simsBot Q * Pm) (η (t + 1)) = matAct (simsBot Q * Pm) (η' (t + 1)) := by
      rw [← add_right_inj (matAct (simsBot Q * Ψ) (ε (t + 1))), e1, e2]
    have hL : V1 * (D⁻¹ * U1ᴴ * (simsBot Q * Pm)) = 1 := by
      rw [simsH_svd_left hsvd]
      exact mul_eq_one_comm.1 hsvd.V1_orth
    have := congrArg (matAct (V1 * (D⁻¹ * U1ᴴ))) e3
    rwa [matAct_mul, matAct_mul, Matrix.mul_assoc V1, hL, matAct_one, matAct_one] at this

/-- **Counterexample to Corollary 2.3.1 for the uniqueness of `y`, and to "if `m > r` there are
infinitely many stable solutions" (Lubik–Schorfheide, Miao, p. 62) for `y`.** Take `n = n_u = 1`,
`Γ₀ = 1`, `Γ₁ = 2`, `Q = Z = 1`, `Ψ = 0` and `Π = [1 0]`, whose second prediction error enters
nowhere (a zero column). Then `Q₂.Π = [1 0]` has the thin SVD `U.1 = D₁₁ = 1`,
`V.1 = (1, 0)ᵀ`, so `r = 1 < m = 2`; Assumptions 2.3.1–2.3.2 hold, and in every `CondExpSystem`
the stable solution `y` (here `y = 0`) is unique. Only the prediction error is indeterminate
(`lubik_schorfheide`). -/
theorem corollary_2_3_1_printed_false [CompleteSpace V] (E : CondExpSystem ℂ V) :
    ∃ (Γ₀ Γ₁ Q Z : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) (Ψ : Matrix (Fin (0 + 1)) (Fin 1) ℂ)
      (Pm : Matrix (Fin (0 + 1)) (Fin 2) ℂ) (U1 D : Matrix (Fin 1) (Fin 1) ℂ)
      (V1 : Matrix (Fin 2) (Fin 1) ℂ),
      IsSimsQZ Γ₀ Γ₁ Q Z ∧ SimsAssumption1 Q Ψ Pm ∧ SimsAssumption2 Q Pm ∧
      IsThinSVD (simsBot Q * Pm) U1 D V1 ∧ SimsYUnique E Γ₀ Γ₁ Ψ Pm := by
  have hS : (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) * 1 * 1 = 1 := by simp
  have hT : (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) * ((2 : ℂ) • 1) * 1 = (2 : ℂ) • 1 := by
    simp
  have hup : ∀ M : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ, M.IsUpperTriangular := fun M i j h => by
    have hi := i.isLt
    have hj := j.isLt
    rw [Fin.lt_def] at h
    omega
  have hqz : IsSimsQZ (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) ((2 : ℂ) • 1) 1 1 := by
    refine ⟨one_mem _, one_mem _, hup _, hup _, fun i => ?_, fun i => ?_⟩
    · rw [hS, hT]
      refine iff_of_false (by omega) ?_
      norm_num
    · rw [hS, hT]
      norm_num
  have hA2 : SimsAssumption2 (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) !![1, 0] :=
    ⟨0, by ext i; exact Fin.elim0 i⟩
  refine ⟨1, (2 : ℂ) • 1, 1, 1, 0, !![1, 0], 1, 1, !![1; 0], hqz, ⟨0, by simp⟩, hA2,
    ⟨?_, by simp, ?_, by simp⟩, ?_⟩
  · ext i j
    fin_cases i
    fin_cases j <;> simp [Matrix.mul_apply, Matrix.one_apply, Fin.ext_iff]
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro ε hε y y' η η' h1 h2 h3 h4 h0
    exact theorem_2_3_1_uniqueness E hqz hA2 hε.2.1 h1 h2 h3 h4 h0

/-- **Lubik–Schorfheide** (Miao, p. 62), correct form: if `m > r` (equivalently `Q₂.Π` has a
nonzero kernel vector) and the filtration is rich, then every stable solution `(y, η)` lies in a
one-parameter family of distinct stable solutions with the same initial value: infinitely many
stable solutions, in the sense of pairs `(y, η)`. (For `y` alone this is false,
`corollary_2_3_1_printed_false`.) -/
theorem lubik_schorfheide [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m r : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} {U1 : Matrix (Fin nu) (Fin r) ℂ}
    {D : Matrix (Fin r) (Fin r) ℂ} {V1 : Matrix (Fin m) (Fin r) ℂ}
    (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1) (hr : r < m) {ε : ℕ → Fin nε → V}
    {y : ℕ → Fin (ns + nu) → V} {η : ℕ → Fin m → V}
    (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y) :
    ∃ f : ℂ → (ℕ → Fin (ns + nu) → V) × (ℕ → Fin m → V), Function.Injective f ∧
      ∀ c, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε (f c).1 (f c).2 ∧ IsStableProc (f c).1 ∧
        (f c).1 0 = y 0 := by
  have hni := mt (svd_injective_iff hsvd).1 (Nat.ne_of_lt hr)
  push Not at hni
  obtain ⟨v, hv, hv0⟩ := hni
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  obtain ⟨ζ, hζa, hζm, ⟨M, hζb⟩, hζ1⟩ := hrich
  choose d hd hds hd0 using fun c : ℂ => simsH_perturb E hqz (Ψ := Ψ) (v := c • v) hζa hζm hζb
    (by rw [Matrix.mulVec_smul, hv, smul_zero])
  refine ⟨fun c => (y + d c, η + fun t k => (c • v) k • ζ t), fun c c' hcc => ?_,
    fun c => ⟨simsH_sol_add hsol (hd c), klS_stable_add hy (hds c), ?_⟩⟩
  · have := congrFun (congrFun (congrArg Prod.snd hcc) 1) k
    simp only [Pi.add_apply, add_right_inj, Pi.smul_apply, smul_eq_mul] at this
    have h2 := (smul_left_injective ℂ hζ1) this
    exact mul_right_cancel₀ hk h2
  · change y 0 + d c 0 = y 0
    rw [hd0, add_zero]

/-! ### Sunspots: (2.26) and `Θ₃` -/

/-- Miao, (2.26), p. 63: under Assumption 2.3.1, with the full SVD `V = [V.1 V.2]`
(`V.1ᴴV.2 = 0`, `V.1V.1ᴴ + V.2V.2ᴴ = I`), the solutions `η` of (2.23) for a given `ε` are
exactly `η = −V.1D₁₁⁻¹U.1ᴴQ₂.Ψε + V.2e` with `e` arbitrary ("`V.2e_t` is a solution to the
homogeneous equation"). -/
theorem eq_2_26 {ns nu nε m r k : ℕ} {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {U1 : Matrix (Fin nu) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1)
    {V2 : Matrix (Fin m) (Fin k) ℂ} (hV12 : V1ᴴ * V2 = 0) (hcompl : V1 * V1ᴴ + V2 * V2ᴴ = 1)
    (hA1 : SimsAssumption1 Q Ψ Pm) (e : Fin nε → V) (h : Fin m → V) :
    matAct (simsBot Q) (matAct Ψ e + matAct Pm h) = 0 ↔
      ∃ s : Fin k → V, h = -matAct (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) e + matAct V2 s := by
  have hΛ := lambda_formula hsvd hA1
  have hBV2 : simsBot Q * Pm * V2 = 0 := by
    rw [hsvd.eq, Matrix.mul_assoc, hV12, Matrix.mul_zero]
  rw [matAct_add, matAct_mul, matAct_mul]
  constructor
  · intro H
    have hBh : matAct (simsBot Q * Pm) h = -matAct (simsBot Q * Ψ) e := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
      exact H
    refine ⟨matAct V2ᴴ h, ?_⟩
    calc h = matAct (V1 * V1ᴴ + V2 * V2ᴴ) h := by rw [hcompl, matAct_one]
      _ = matAct V1 (matAct (D⁻¹ * U1ᴴ) (matAct (simsBot Q * Pm) h)) +
          matAct V2 (matAct V2ᴴ h) := by
        rw [matAct_mul (D⁻¹ * U1ᴴ), simsH_svd_left hsvd, klS_add_matAct, matAct_mul, matAct_mul]
      _ = _ := by
        rw [hBh, klS_matAct_neg, klS_matAct_neg, matAct_mul, matAct_mul, matAct_mul,
          Matrix.mul_assoc V1 D⁻¹, Matrix.mul_assoc V1]
  · rintro ⟨s, rfl⟩
    rw [matAct_add, klS_matAct_neg, matAct_mul, matAct_mul, ← hΛ, hBV2, klS_zero_matAct,
      add_zero, add_neg_cancel]

/-- The stable-block prediction-error term of the sunspot solution (Miao, p. 63): with
`Ξ = Q₁.ΠV.1D₁₁⁻¹U.1ᴴ` and `η = −V.1D₁₁⁻¹U.1ᴴQ₂.Ψε + V.2e`,
`(Q₁. − ΞQ₂.)Πη = Q₁.Π(I − V.1V.1ᴴ)V.2e`, as printed. -/
theorem eq_sunspot_identity {ns nu nε m r k : ℕ} {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {U1 : Matrix (Fin nu) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1)
    (V2 : Matrix (Fin m) (Fin k) ℂ) (e : Fin nε → V) (s : Fin k → V) :
    matAct ((simsTop Q - simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ * simsBot Q) * Pm)
        (-matAct (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) e + matAct V2 s) =
      matAct (simsTop Q * Pm * (1 - V1 * V1ᴴ) * V2) s := by
  have hR : (simsTop Q - simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ * simsBot Q) * Pm =
      simsTop Q * Pm * (1 - V1 * V1ᴴ) := by
    rw [Matrix.sub_mul, Matrix.mul_assoc (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ), xi_residual hsvd]
  have hRV1 : simsTop Q * Pm * (1 - V1 * V1ᴴ) * V1 = 0 := by
    rw [Matrix.mul_assoc (simsTop Q * Pm), Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc V1,
      hsvd.V1_orth, Matrix.mul_one, sub_self, Matrix.mul_zero]
  rw [hR, matAct_add, klS_matAct_neg, show V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ) =
    V1 * (D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) by simp only [Matrix.mul_assoc], ← matAct_mul V1,
    matAct_mul _ V1, hRV1, klS_zero_matAct, neg_zero, zero_add, matAct_mul]

/-- The term of `eq_sunspot_identity` simplifies: `(I − V.1V.1ᴴ)V.2 = V.2` when `V.1ᴴV.2 = 0`, so
`Q₁.Π(I − V.1V.1ᴴ)V.2 = Q₁.ΠV.2` (the book keeps the redundant factor). -/
theorem sunspot_term_simplified {m r k q : ℕ} {V1 : Matrix (Fin m) (Fin r) ℂ}
    {V2 : Matrix (Fin m) (Fin k) ℂ} (hV12 : V1ᴴ * V2 = 0) (C : Matrix (Fin q) (Fin m) ℂ) :
    C * (1 - V1 * V1ᴴ) * V2 = C * V2 := by
  rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV12, Matrix.mul_zero,
    sub_zero]

/-- `Θ₃ = ZG⁻¹[[Q₁.Π(I − V.1V.1ᴴ)], [0]]V.2` (Miao, p. 64, where `V.1′` means `V.1ᴴ`). -/
noncomputable def simsTheta3 {ns nu m r k : ℕ} (Γ₀ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) (Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ)
    (V1 : Matrix (Fin m) (Fin r) ℂ) (V2 : Matrix (Fin m) (Fin k) ℂ) :
    Matrix (Fin (ns + nu)) (Fin k) ℂ :=
  Z * (simsGmat (Q * Γ₀ * Z) Ξ)⁻¹ * simsRows (simsTop Q * Pm * (1 - V1 * V1ᴴ)) 0 * V2

theorem simsH_rows_zero {a b : ℕ} {κ : Type*} :
    simsRows (0 : Matrix (Fin a) κ ℂ) (0 : Matrix (Fin b) κ ℂ) = 0 := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [simsRows]

/-- **The sunspot solution** (Miao, pp. 63–64), first half: with `Ξ = Q₁.ΠV.1D₁₁⁻¹U.1ᴴ` and the
full SVD (`V.1V.1ᴴ + V.2V.2ᴴ = I`), every stable solution of (2.20) satisfies
`y_t = Θ₁y_{t−1} + Θ₂ε_t + Θ₃e_t` with `e_t = V.2ᴴη_t`. Neither Assumption 2.3.1 nor 2.3.2 is
needed for this representation. -/
theorem sunspot_solution [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m r k : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {U1 : Matrix (Fin nu) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1)
    {V2 : Matrix (Fin m) (Fin k) ℂ} (hcompl : V1 * V1ᴴ + V2 * V2ᴴ = 1)
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (t : ℕ) :
    y (t + 1) = matAct (simsTheta1 Γ₀ Γ₁ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ)) (y t) +
      matAct (simsTheta2 Γ₀ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ) Ψ) (ε (t + 1)) +
      matAct (simsTheta3 Γ₀ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ) Pm V1 V2)
        (matAct V2ᴴ (η (t + 1))) := by
  set Ξ := simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ with hΞ
  set R := simsTop Q * Pm * (1 - V1 * V1ᴴ) with hRdef
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hqz.unitary_Z
  have hback : ∀ v : Fin (ns + nu) → V, matAct Z (matAct (star Z) v) = v := fun v => by
    rw [matAct_mul, hZZ, matAct_one]
  have hR : (simsTop Q - Ξ * simsBot Q) * Pm = R := by
    rw [Matrix.sub_mul, Matrix.mul_assoc Ξ, hΞ, xi_residual hsvd]
  have hRV1 : R * V1 = 0 := by
    rw [hRdef, Matrix.mul_assoc (simsTop Q * Pm), Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc V1, hsvd.V1_orth, Matrix.mul_one, sub_self, Matrix.mul_zero]
  have hKP : simsKmat Q Ξ * Pm = simsRows R 0 := by
    rw [simsKmat, simsRows_mul, hR, Matrix.zero_mul]
  have hη : matAct (simsKmat Q Ξ) (matAct Pm (η (t + 1))) =
      matAct (simsRows R 0 * V2) (matAct V2ᴴ (η (t + 1))) := by
    have e1 : simsRows R (0 : Matrix (Fin nu) (Fin m) ℂ) =
        simsRows R (0 : Matrix (Fin nu) (Fin m) ℂ) * V2 * V2ᴴ := by
      calc simsRows R (0 : Matrix (Fin nu) (Fin m) ℂ) =
          simsRows R 0 * (V1 * V1ᴴ + V2 * V2ᴴ) := by rw [hcompl, Matrix.mul_one]
        _ = simsRows R 0 * V2 * V2ᴴ := by
          rw [Matrix.mul_add, ← Matrix.mul_assoc, simsRows_mul R, hRV1, Matrix.zero_mul,
            simsH_rows_zero, Matrix.zero_mul, zero_add, Matrix.mul_assoc]
    rw [matAct_mul, hKP, matAct_mul, ← e1]
  have h := eq_2_24 E hqz hεm hsol hy Ξ t
  rw [matAct_add, hη] at h
  have h' := (simsH_solve_G (simsGmat_det hqz.upper_S hqz.ord Ξ) hqz.unitary_Z _ _ _).1 h
  rw [hback, hback] at h'
  rw [h', add_assoc]
  congr 1
  simp only [simsTheta2, simsTheta3, matAct_add, matAct_mul, Matrix.mul_assoc, hRdef]

/-- **The sunspot solution** (Miao, pp. 63–64), second half: under Assumption 2.3.1, for every
exogenous shock `ε`, every sunspot shock `e` (adapted, stable, `E_{t−1}e_t = 0`) and every
admissible `y₀`, the prediction error (2.26) `η_t = −V.1D₁₁⁻¹U.1ᴴQ₂.Ψε_t + V.2e_t` gives a stable
solution of (2.20) with `y_0 = y₀`; if `V.2` has orthonormal columns it is
`y_t = Θ₁y_{t−1} + Θ₂ε_t + Θ₃e_t` (`Θ₃` as printed). "Sunspot shocks can influence the
equilibrium allocations". -/
theorem sunspot_existence [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m r k : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {U1 : Matrix (Fin nu) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1)
    {V2 : Matrix (Fin m) (Fin k) ℂ} (hV12 : V1ᴴ * V2 = 0) (hV2 : V2ᴴ * V2 = 1)
    (hcompl : V1 * V1ᴴ + V2 * V2ᴴ = 1) (hA1 : SimsAssumption1 Q Ψ Pm)
    {ε : ℕ → Fin nε → V} (hε : IsSimsShock E ε) {e : ℕ → Fin k → V} (he : IsSimsShock E e)
    (y₀ : Fin (ns + nu) → V) (hy₀a : Evec E 0 y₀ = y₀)
    (hy₀ : matAct (simsBot (star Z)) y₀ = 0) :
    ∃ y, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y
        (fun t => -matAct (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) (ε t) + matAct V2 (e t)) ∧
      IsStableProc y ∧ y 0 = y₀ ∧ ∀ t, y (t + 1) =
        matAct (simsTheta1 Γ₀ Γ₁ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ)) (y t) +
        matAct (simsTheta2 Γ₀ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ) Ψ) (ε (t + 1)) +
        matAct (simsTheta3 Γ₀ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ) Pm V1 V2) (e (t + 1)) := by
  obtain ⟨hεa, hεm, hεs⟩ := hε
  obtain ⟨hea, hem, hes⟩ := he
  set Λ₀ := V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)
  have hηs : IsStableProc fun t => -matAct Λ₀ (ε t) + matAct V2 (e t) :=
    klS_stable_add (by simpa only [klS_neg_matAct] using klS_stable_matAct hεs (-Λ₀))
      (klS_stable_matAct hes V2)
  have hηa : IsAdaptedV E fun t => -matAct Λ₀ (ε t) + matAct V2 (e t) := fun t i => by
    change Evec E t (-matAct Λ₀ (ε t) + matAct V2 (e t)) i = _
    rw [klS_Evec_add, klS_Evec_neg, Evec_matAct, Evec_matAct,
      show Evec E t (ε t) = ε t from funext (hεa t), show Evec E t (e t) = e t from funext (hea t)]
  have hηm : IsMartingaleDiffProc E fun t => -matAct Λ₀ (ε t) + matAct V2 (e t) := fun t i => by
    change Evec E t (-matAct Λ₀ (ε (t + 1)) + matAct V2 (e (t + 1))) i = (0 : Fin m → V) i
    rw [klS_Evec_add, klS_Evec_neg, Evec_matAct, Evec_matAct,
      show Evec E t (ε (t + 1)) = 0 from funext (hεm t),
      show Evec E t (e (t + 1)) = 0 from funext (hem t), klS_matAct_zero, klS_matAct_zero,
      neg_zero, add_zero]
  obtain ⟨y, hsol, hy, hy0⟩ := simsH_core_exists E hqz hεa hεs hηa hηm hηs
    (fun t => (eq_2_26 hsvd hV12 hcompl hA1 _ _).2 ⟨e (t + 1), rfl⟩) y₀ hy₀a hy₀
  refine ⟨y, hsol, hy, hy0, fun t => ?_⟩
  have hV21 : V2ᴴ * V1 = 0 := by
    have := congrArg Matrix.conjTranspose hV12
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using this
  have hev : matAct V2ᴴ (-matAct Λ₀ (ε (t + 1)) + matAct V2 (e (t + 1))) = e (t + 1) := by
    rw [matAct_add, klS_matAct_neg, matAct_mul, matAct_mul, hV2, matAct_one,
      show V2ᴴ * Λ₀ = V2ᴴ * V1 * (D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) by simp only [Λ₀,
        Matrix.mul_assoc], hV21, Matrix.zero_mul, klS_zero_matAct, neg_zero, zero_add]
  rw [sunspot_solution E hqz hsvd hcompl hεm hsol hy t, hev]

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.StochasticKlein
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# The Sims method

Miao, §2.3.3, pp. 58–62, in the abstract setting of `Basics` with `𝕜 = ℂ` (the QZ form is
complex): `V` is a complete complex normed space of scalar random variables with conditional
expectations `E : CondExpSystem ℂ V`, a vector random variable is `Fin k → V`.

**Representation.** (2.20) `Γ₀y_t = Γ₁y_{t−1} + Ψε_t + Πη_t` is `IsSimsSolution` (for `t ≥ 1`,
indexed as `t + 1`; `y`, `η` adapted, `E_tη_{t+1} = 0`; `Pm` stands for `Π`). The exogenous
shock `ε` is an `IsSimsShock` (adapted, stable, martingale difference). An ordered QZ form
(`IsSimsQZ`, from `theorem_1_4_4_stable` via `isSimsQZ_of_regular`) has `n = n_s + n_u`, the
stable pairs first and none on the unit circle; rows of `Q`, `Zᴴ` are split by `simsTop`,
`simsBot`, blocks by `sims11`, `sims12`, `sims22`; `y* = Zᴴy = (s, u)`.

* (2.21) `eq_2_21`; (2.22) `eq_2_22` (pathwise forward solution) and `eq_2_22_expect`: a
  stable adapted `u` whose forcing is a martingale difference vanishes; hence every stable
  solution has `u_t = Z₂ᴴy_t = 0` for all `t` (`sims_u_eq_zero`), `Z₂ᴴy₀ = 0`
  (`sims_Z2_y0`) and (2.23) `Q₂.(Ψε_t + Πη_t) = 0` (`eq_2_23`).
* Lemma 2.3.1 (`lemma_2_3_1`, matrix form; `lemma_2_3_1_sims`; `lemma_2_3_1_random`, random
  right-hand sides); Assumptions 2.3.1–2.3.2 (`SimsAssumption1`, `SimsAssumption2`);
  Assumption 2.3.2 iff `ker(Q₂.Π) ⊆ ker(Q₁.Π)` (`simsAssumption2_iff_ker`);
  `assumption_2_3_1_nu_gt_m` (existence with `n_u > m`).
* (2.24) `eq_2_24` (any `Ξ`), `simsKmat_mul_Pm`; the matrices `G`, `H`, `K`, `Θ₁`, `Θ₂`
  (`simsGmat`, `simsHmat`, `simsKmat`, `simsTheta1`, `simsTheta2`).
* Theorem 2.3.1: `theorem_2_3_1_theta` (every stable solution is `y_t = Θ₁y_{t−1} + Θ₂ε_t`,
  under 2.3.2), `theorem_2_3_1_uniqueness` (2.3.2 only), `theorem_2_3_1_existence`
  (2.3.1 only, `η = −Λε`), `theorem_2_3_1_sufficiency`, `theorem_2_3_1_necessity_1`,
  `theorem_2_3_1_necessity_2` and the characterisation `theorem_2_3_1` under a rich
  filtration (`SimsRich`; `simsRich_trunc` shows the hypothesis is satisfiable).

**Corrections.**
* (2.22) is printed `u_t = −T₂₂⁻¹∑_{j≥1}(T₂₂⁻¹S₂₂)ʲQ₂.(Ψε_{t+j} + Πη_{t+j})`; the forward
  solution of `S₂₂u_t = T₂₂u_{t−1} + Q₂.(…)` is `u_t = −∑_{j≥1}(T₂₂⁻¹S₂₂)^{j−1}T₂₂⁻¹Q₂.(…)`
  (`eq_2_22`; `eq_2_22_printed_false`). The conclusion `u_t = 0` needs both stability (for
  the forward sum) and the martingale-difference property of `ε`, `η` (for `E_t` to kill it).
* `Θ₁` is printed `Z G⁻¹ H`; it must be `Z G⁻¹ H Zᴴ` (`theta_1_printed_false`). `Θ₂` and (2.24)
  are correct as printed.
* Theorem 2.3.1 ("necessary and sufficient", called "Theorem 2.19" on p. 62): sufficiency holds
  in every `CondExpSystem`, with "unique" meaning unique `y` (given `y₀`; `y₀` is free subject
  to `Z₂ᴴy₀ = 0`), not unique `(y, η)`. Existence needs only 2.3.1, uniqueness only 2.3.2.
  Necessity is false in general: in the deterministic system `E_t = id` martingale differences
  vanish and a system violating both assumptions has a unique stable solution
  (`theorem_2_3_1_necessity_false`); it holds when the filtration carries a nonzero stable
  martingale difference (`theorem_2_3_1`).
* Lemma 2.3.1's proof takes the `j`-th column of `Λ` to be the `η` solving (2.23) for
  `ε = I_j`; that gives `Q₂.Ψ = −Q₂.ΠΛ`, so the column must be `−η`.
* The book's hypotheses leave implicit that the shocks are adapted and stable; both are
  assumed (`IsSimsShock`).
-/

namespace Miao.RationalExpectations

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### Blocks -/

/-- The first `a` rows `M_{1·}` of a matrix with `a + b` rows (e.g. `Q₁.`, `Z₁ᴴ`). -/
abbrev simsTop {a b : ℕ} {κ : Type*} (M : Matrix (Fin (a + b)) κ ℂ) : Matrix (Fin a) κ ℂ :=
  M.submatrix (Fin.castAdd b) id

/-- The last `b` rows `M_{2·}` of a matrix with `a + b` rows (e.g. `Q₂.`, `Z₂ᴴ`). -/
abbrev simsBot {a b : ℕ} {κ : Type*} (M : Matrix (Fin (a + b)) κ ℂ) : Matrix (Fin b) κ ℂ :=
  M.submatrix (Fin.natAdd a) id

/-- The block `M₁₁`. -/
abbrev sims11 {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) : Matrix (Fin a) (Fin a) ℂ :=
  M.submatrix (Fin.castAdd b) (Fin.castAdd b)

/-- The block `M₁₂`. -/
abbrev sims12 {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) : Matrix (Fin a) (Fin b) ℂ :=
  M.submatrix (Fin.castAdd b) (Fin.natAdd a)

/-- The block `M₂₂`. -/
abbrev sims22 {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) : Matrix (Fin b) (Fin b) ℂ :=
  M.submatrix (Fin.natAdd a) (Fin.natAdd a)

/-- The block matrix `[[A, B], [C, D]]` indexed by `Fin (a + b)`. -/
def simsBlk {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)

/-- The stacked matrix `[[A], [C]]` indexed by `Fin (a + b)` rows. -/
def simsRows {a b : ℕ} {κ : Type*} (A : Matrix (Fin a) κ ℂ) (C : Matrix (Fin b) κ ℂ) :
    Matrix (Fin (a + b)) κ ℂ :=
  Matrix.reindex finSumFinEquiv (Equiv.refl κ) (Matrix.fromRows A C)

theorem simsBlk_11 {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    sims11 (simsBlk A B C D) = A := by
  ext i j
  simp [simsBlk]

theorem simsBlk_12 {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    sims12 (simsBlk A B C D) = B := by
  ext i j
  simp [simsBlk]

theorem simsBlk_21 {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    (simsBlk A B C D).submatrix (Fin.natAdd a) (Fin.castAdd b) = C := by
  ext i j
  simp [simsBlk]

theorem simsBlk_22 {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    sims22 (simsBlk A B C D) = D := by
  ext i j
  simp [simsBlk]

theorem simsRows_top {a b : ℕ} {κ : Type*} (A : Matrix (Fin a) κ ℂ) (C : Matrix (Fin b) κ ℂ) :
    simsTop (simsRows A C) = A := by
  ext i j
  simp [simsRows]

theorem simsRows_bot {a b : ℕ} {κ : Type*} (A : Matrix (Fin a) κ ℂ) (C : Matrix (Fin b) κ ℂ) :
    simsBot (simsRows A C) = C := by
  ext i j
  simp [simsRows]

theorem simsBlk_det {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (D : Matrix (Fin b) (Fin b) ℂ) : (simsBlk A B 0 D).det = A.det * D.det := by
  rw [simsBlk, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem simsTop_mul {a b : ℕ} {κ ρ : Type*} [Fintype κ] (M : Matrix (Fin (a + b)) κ ℂ)
    (N : Matrix κ ρ ℂ) : simsTop M * N = simsTop (M * N) := by
  ext i j
  simp [Matrix.mul_apply]

theorem simsBot_mul {a b : ℕ} {κ ρ : Type*} [Fintype κ] (M : Matrix (Fin (a + b)) κ ℂ)
    (N : Matrix κ ρ ℂ) : simsBot M * N = simsBot (M * N) := by
  ext i j
  simp [Matrix.mul_apply]

theorem simsRows_mul {a b : ℕ} {κ ρ : Type*} [Fintype κ] (A : Matrix (Fin a) κ ℂ)
    (C : Matrix (Fin b) κ ℂ) (N : Matrix κ ρ ℂ) : simsRows A C * N = simsRows (A * N) (C * N) := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [simsRows, Matrix.mul_apply]

/-- The top rows of `Mv`: `(Mv)₁ = M₁.v`. -/
theorem simsH_top_matAct {a b : ℕ} {κ : Type*} [Fintype κ] (M : Matrix (Fin (a + b)) κ ℂ)
    (x : κ → V) : matAct M x ∘ Fin.castAdd b = matAct (simsTop M) x := rfl

/-- The bottom rows of `Mv`: `(Mv)₂ = M₂.v`. -/
theorem simsH_bot_matAct {a b : ℕ} {κ : Type*} [Fintype κ] (M : Matrix (Fin (a + b)) κ ℂ)
    (x : κ → V) : matAct M x ∘ Fin.natAdd a = matAct (simsBot M) x := rfl

/-- The top rows of a block matrix acting on a vector. -/
theorem simsH_blk_top {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) (x : Fin (a + b) → V) :
    matAct (simsBlk A B C D) x ∘ Fin.castAdd b =
      matAct A (x ∘ Fin.castAdd b) + matAct B (x ∘ Fin.natAdd a) := by
  rw [klS_matAct_blocks]
  rw [show (simsBlk A B C D).submatrix (Fin.castAdd b) (Fin.castAdd b) = A from simsBlk_11 A B C D,
    show (simsBlk A B C D).submatrix (Fin.castAdd b) (Fin.natAdd a) = B from simsBlk_12 A B C D]

/-- The bottom rows of a block matrix acting on a vector. -/
theorem simsH_blk_bot {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) (x : Fin (a + b) → V) :
    matAct (simsBlk A B C D) x ∘ Fin.natAdd a =
      matAct C (x ∘ Fin.castAdd b) + matAct D (x ∘ Fin.natAdd a) := by
  rw [klS_matAct_blocks]
  rw [simsBlk_21, show (simsBlk A B C D).submatrix (Fin.natAdd a) (Fin.natAdd a) = D from
    simsBlk_22 A B C D]

/-- A matrix acting on a scalar multiple of one random variable:
`M(v ζ) = (Mv) ζ`. -/
theorem simsH_matAct_smul {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (v : κ → ℂ) (X : V) :
    matAct M (fun k => v k • X) = fun i => (M *ᵥ v) i • X := by
  funext i
  simp only [matAct, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]

/-! ### The Sims form (2.20) -/

/-- Miao, (2.20), p. 58: `Γ₀y_t = Γ₁y_{t−1} + Ψε_t + Πη_t` for `t ≥ 1`, with `y` and the
prediction error `η` adapted ("all variables dated `t` are observable at `t`", p. 59) and `η` a
martingale difference, `E_t η_{t+1} = 0`. (`Pm` stands for `Π`, a reserved token.) The value
`η₀` does not enter the system. -/
def IsSimsSolution {n nε m : ℕ} (E : CondExpSystem ℂ V) (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ)
    (Ψ : Matrix (Fin n) (Fin nε) ℂ) (Pm : Matrix (Fin n) (Fin m) ℂ) (ε : ℕ → Fin nε → V)
    (y : ℕ → Fin n → V) (η : ℕ → Fin m → V) : Prop :=
  IsAdaptedV E y ∧ IsAdaptedV E η ∧ IsMartingaleDiffProc E η ∧
    ∀ t, matAct Γ₀ (y (t + 1)) = matAct Γ₁ (y t) + matAct Ψ (ε (t + 1)) + matAct Pm (η (t + 1))

/-- The exogenous shocks of (2.20) (Miao, p. 59): `ε` is adapted, stable and a martingale
difference, `E_t ε_{t+1} = 0`. -/
def IsSimsShock {nε : ℕ} (E : CondExpSystem ℂ V) (ε : ℕ → Fin nε → V) : Prop :=
  IsAdaptedV E ε ∧ IsMartingaleDiffProc E ε ∧ IsStableProc ε

/-- An ordered complex QZ form of the pencil `(Γ₀, Γ₁)` (Miao, p. 59, via Theorem 1.4.4):
unitary `Q`, `Z` with `S = QΓ₀Z`, `T = QΓ₁Z` upper triangular, the first `n_s` pairs
`(sᵢᵢ, tᵢᵢ)` stable (`|tᵢᵢ| < |sᵢᵢ|`) and the remaining `n_u` unstable, none on the unit
circle (`|tᵢᵢ| ≠ |sᵢᵢ|`). For a regular pencil without generalized eigenvalues of modulus one
such a form exists (`theorem_1_4_4_stable`, `isSimsQZ_of_regular`). -/
structure IsSimsQZ {ns nu : ℕ} (G₀ G₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ) : Prop where
  unitary_Q : Q ∈ Matrix.unitaryGroup (Fin (ns + nu)) ℂ
  unitary_Z : Z ∈ Matrix.unitaryGroup (Fin (ns + nu)) ℂ
  upper_S : (Q * G₀ * Z).IsUpperTriangular
  upper_T : (Q * G₁ * Z).IsUpperTriangular
  ord : ∀ i : Fin (ns + nu), i.val < ns ↔ ‖(Q * G₁ * Z) i i‖ < ‖(Q * G₀ * Z) i i‖
  off_circle : ∀ i, ‖(Q * G₁ * Z) i i‖ ≠ ‖(Q * G₀ * Z) i i‖

/-- Miao, p. 59: for a regular pencil `(Γ₀, Γ₁)` (Assumption 1.4.1) without generalized
eigenvalues on the unit circle, any QZ form with the stable pairs first is an `IsSimsQZ`; such a
form exists by `theorem_1_4_4_stable`. -/
theorem isSimsQZ_of_regular {ns nu : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hreg : IsRegular Γ₀ Γ₁) (hcirc : ∀ lam ∈ genEigenvalues Γ₀ Γ₁, ‖lam‖ ≠ 1)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (ns + nu)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (ns + nu)) ℂ)
    (hS : (Q * Γ₀ * Z).IsUpperTriangular) (hT : (Q * Γ₁ * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (ns + nu), i.val < ns ↔ ‖(Q * Γ₁ * Z) i i‖ < ‖(Q * Γ₀ * Z) i i‖) :
    IsSimsQZ Γ₀ Γ₁ Q Z :=
  ⟨hQ, hZ, hS, hT, hord, diag_off_circle hreg hQ hZ hS hT hcirc⟩

/-- **Assumption 2.3.1** (Miao, p. 60): the column space of `Q₂.Ψ` is contained in that of
`Q₂.Π`, i.e. `Q₂.Ψ = Q₂.ΠΛ` for some `m × n_ε` matrix `Λ`. -/
def SimsAssumption1 {ns nu nε m : ℕ} (Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ) (Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ) : Prop :=
  ∃ Λ : Matrix (Fin m) (Fin nε) ℂ, simsBot Q * Ψ = simsBot Q * Pm * Λ

/-- **Assumption 2.3.2** (Miao, p. 61): `Q₁.Π = ΞQ₂.Π` for some `n_s × n_u` matrix `Ξ`. -/
def SimsAssumption2 {ns nu m : ℕ} (Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ) : Prop :=
  ∃ Ξ : Matrix (Fin ns) (Fin nu) ℂ, simsTop Q * Pm = Ξ * (simsBot Q * Pm)

/-- The unitary change of variables `y* = Zᴴy` (Miao, p. 59): `Γ₀b = Γ₁a + w` iff
`S(Zᴴb) = T(Zᴴa) + Qw` with `S = QΓ₀Z`, `T = QΓ₁Z`. -/
theorem simsH_transform {n : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (a b w : Fin n → V) :
    matAct Γ₀ b = matAct Γ₁ a + w ↔
      matAct (Q * Γ₀ * Z) (matAct (star Z) b) = matAct (Q * Γ₁ * Z) (matAct (star Z) a) +
        matAct Q w := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hQQ : star Q * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  have key : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → V),
      matAct (Q * M * Z) (matAct (star Z) v) = matAct Q (matAct M v) := fun M v => by
    simp only [matAct_mul, Matrix.mul_assoc, hZZ, Matrix.mul_one]
  simp only [key, ← matAct_add]
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have := congrArg (matAct (star Q)) h
  simpa only [matAct_mul, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, matAct_one] using this

/-- Miao, (2.21), p. 59: in the coordinates `y* = Zᴴy = (s, u)`, the equation
`Γ₀b = Γ₁a + w` (`b = y_t`, `a = y_{t−1}`, `w = Ψε_t + Πη_t`) is the pair of block rows
`S₁₁s_t + S₁₂u_t = T₁₁s_{t−1} + T₁₂u_{t−1} + Q₁.w` and `S₂₂u_t = T₂₂u_{t−1} + Q₂.w`. -/
theorem eq_2_21 {ns nu : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) (a b w : Fin (ns + nu) → V) :
    matAct Γ₀ b = matAct Γ₁ a + w ↔
      (matAct (sims11 (Q * Γ₀ * Z)) (matAct (simsTop (star Z)) b) +
          matAct (sims12 (Q * Γ₀ * Z)) (matAct (simsBot (star Z)) b) =
        matAct (sims11 (Q * Γ₁ * Z)) (matAct (simsTop (star Z)) a) +
          matAct (sims12 (Q * Γ₁ * Z)) (matAct (simsBot (star Z)) a) + matAct (simsTop Q) w) ∧
      matAct (sims22 (Q * Γ₀ * Z)) (matAct (simsBot (star Z)) b) =
        matAct (sims22 (Q * Γ₁ * Z)) (matAct (simsBot (star Z)) a) + matAct (simsBot Q) w := by
  rw [simsH_transform hqz.unitary_Q hqz.unitary_Z, klS_blocks_iff hqz.upper_S hqz.upper_T]
  rfl

/-! ### The forward solution (2.22) and `u_t = 0` -/

/-- The pathwise system `E_t = id` on `V`, used for identities that hold realization by
realization (no expectations are taken). -/
noncomputable def simsH_idSystem : CondExpSystem ℂ V where
  E _ := ContinuousLinearMap.id ℂ V
  norm_le _ := ContinuousLinearMap.norm_id_le
  tower_le _ _ _ := ContinuousLinearMap.id_comp _
  tower_ge _ _ _ := ContinuousLinearMap.id_comp _

theorem simsH_Evec_id {ι : Type*} (t : ℕ) (x : ι → V) : Evec simsH_idSystem t x = x := rfl

/-- The unstable block solved forward pathwise: a stable `u` with
`S₂₂u_{t+1} = T₂₂u_t + c_{t+1}` is the forward sum `∑ⱼ (T₂₂⁻¹S₂₂)ʲ (−T₂₂⁻¹c_{t+1+j})`. -/
theorem simsH_fwd_data [CompleteSpace V] {p : ℕ} {S22 T22 : Matrix (Fin p) (Fin p) ℂ}
    (hT22 : T22.det ≠ 0) (hN : Summable fun j => ‖mclm ((T22⁻¹ * S22) ^ j)‖)
    {u c : ℕ → Fin p → V} (hu : IsStableProc u)
    (h : ∀ t, matAct S22 (u (t + 1)) = matAct T22 (u t) + c (t + 1)) :
    ∃ K, (∀ t, ‖-matAct T22⁻¹ (c (t + 1))‖ ≤ K) ∧ ∀ t, u t =
      klS_fwd simsH_idSystem (T22⁻¹ * S22) (fun t => -matAct T22⁻¹ (c (t + 1))) t := by
  have hc : ∀ t, c (t + 1) = matAct S22 (u (t + 1)) - matAct T22 (u t) := fun t => by
    rw [h t]
    abel
  have hcs : IsStableProc fun t => -matAct T22⁻¹ (c (t + 1)) := by
    have := klS_stable_matAct (klS_stable_sub (klS_stable_matAct (klS_stable_shift hu 1) S22)
      (klS_stable_matAct hu T22)) (-T22⁻¹)
    simpa only [klS_neg_matAct, hc] using this
  obtain ⟨K, -, hK⟩ := klS_stable_bound hcs
  exact ⟨K, hK, fun t => klS_eq_fwd simsH_idSystem (klS_summable_ent hN) hK hu (fun _ => rfl)
    (fun t => (klS_solve_fwd hT22 _ _ _).1 (h t)) t⟩

/-- Miao, (2.22) as corrected, p. 59. From `S₂₂u_t = T₂₂u_{t−1} + Q₂.(Ψε_t + Πη_t)`, written
`S₂₂u_{t+1} = T₂₂u_t + c_{t+1}`, a stable `u` satisfies (pathwise, without expectations)
`u_t = −∑_{j≥1} (T₂₂⁻¹S₂₂)^{j−1} T₂₂⁻¹ c_{t+j}`, here with the summation index shifted to
`j ≥ 0`. The book prints `u_t = −T₂₂⁻¹∑_{j≥1} (T₂₂⁻¹S₂₂)ʲ c_{t+j}`, which is false
(`eq_2_22_printed_false`). -/
theorem eq_2_22 [CompleteSpace V] {p : ℕ} {S22 T22 : Matrix (Fin p) (Fin p) ℂ}
    (hT22 : T22.det ≠ 0) (hN : Summable fun j => ‖mclm ((T22⁻¹ * S22) ^ j)‖)
    {u c : ℕ → Fin p → V} (hu : IsStableProc u)
    (h : ∀ t, matAct S22 (u (t + 1)) = matAct T22 (u t) + c (t + 1)) (t : ℕ) :
    u t = -∑' j, matAct ((T22⁻¹ * S22) ^ j * T22⁻¹) (c (t + 1 + j)) := by
  obtain ⟨K, -, hK⟩ := simsH_fwd_data hT22 hN hu h
  rw [hK t, klS_fwd, ← tsum_neg]
  congr 1
  funext j
  rw [simsH_Evec_id, klS_matAct_neg, matAct_mul, show t + j + 1 = t + 1 + j by ring]

/-- Miao, p. 60 ("Taking expectations `E_t` gives `E_t u_t = u_t = 0`"): if moreover `u` is
adapted and `c` is a martingale difference (`E_t c_{t+1} = 0`), then `u_t = 0`, because
`E_t c_{t+j} = 0` for all `j ≥ 1` and `E_t` passes through the convergent forward sum. -/
theorem eq_2_22_expect [CompleteSpace V] (E : CondExpSystem ℂ V) {p : ℕ}
    {S22 T22 : Matrix (Fin p) (Fin p) ℂ} (hT22 : T22.det ≠ 0)
    (hN : Summable fun j => ‖mclm ((T22⁻¹ * S22) ^ j)‖) {u c : ℕ → Fin p → V}
    (hu : IsStableProc u) (hua : ∀ t, Evec E t (u t) = u t)
    (hcm : ∀ t, Evec E t (c (t + 1)) = 0)
    (h : ∀ t, matAct S22 (u (t + 1)) = matAct T22 (u t) + c (t + 1)) (t : ℕ) : u t = 0 := by
  obtain ⟨K, hKb, hK⟩ := simsH_fwd_data hT22 hN hu h
  have hE : ∀ j, Evec E t (c (t + j + 1)) = 0 := fun j => by
    rw [← klS_Evec_tower_le E (Nat.le_add_right t j), hcm, klS_Evec_zero]
  rw [← hua t, hK t, klS_fwd, ← klS_EvecCLM_apply, (klS_EvecCLM E t (Fin p)).map_tsum
    (klS_fwd_summable simsH_idSystem (klS_summable_ent hN) hKb t)]
  simp only [klS_EvecCLM_apply, simsH_Evec_id, Evec_matAct, klS_Evec_neg, hE, klS_matAct_zero,
    neg_zero, tsum_zero]

/-- Miao, p. 60: every stable solution of (2.20) has `u_t = Z₂ᴴy_t = 0` for all `t`
(including `t = 0`). This uses only that `u` is adapted and stable and that `ε`, `η` are
martingale differences; no condition on `Ψ`, `Π` is needed. -/
theorem sims_u_eq_zero [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (t : ℕ) : matAct (simsBot (star Z)) (y t) = 0 := by
  obtain ⟨hya, -, hηm, heq⟩ := hsol
  refine eq_2_22_expect E (det_T22_ne_zero hqz.upper_T hqz.ord hqz.off_circle)
    (summable_Mu hqz.upper_S hqz.upper_T hqz.ord hqz.off_circle)
    (c := fun t => matAct (simsBot Q) (matAct Ψ (ε t) + matAct Pm (η t)))
    (klS_stable_matAct hy _) (fun t => by rw [Evec_matAct, show Evec E t (y t) = y t from
      funext (hya t)]) (fun t => ?_) (fun t => ?_) t
  · rw [Evec_matAct, klS_Evec_add, Evec_matAct, Evec_matAct,
      show Evec E t (ε (t + 1)) = 0 from funext (hεm t),
      show Evec E t (η (t + 1)) = 0 from funext (hηm t)]
    simp only [klS_matAct_zero, add_zero]
  · have := ((eq_2_21 hqz (y t) (y (t + 1)) _).1 (by rw [heq t, add_assoc])).2
    exact this

/-- Miao, p. 60: "It follows that `Z₂ᴴy₀ = 0`", the restriction on the initial value. -/
theorem sims_Z2_y0 [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y) :
    matAct (simsBot (star Z)) (y 0) = 0 :=
  sims_u_eq_zero E hqz hεm hsol hy 0

/-- Miao, (2.23), p. 60: in every stable solution, `Q₂.(Ψε_t + Πη_t) = 0` for `t ≥ 1`. -/
theorem eq_2_23 [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (t : ℕ) : matAct (simsBot Q) (matAct Ψ (ε (t + 1)) + matAct Pm (η (t + 1))) = 0 := by
  have h := ((eq_2_21 hqz (y t) (y (t + 1)) _).1 (by rw [hsol.2.2.2 t, add_assoc])).2
  rw [sims_u_eq_zero E hqz hεm hsol hy, sims_u_eq_zero E hqz hεm hsol hy, klS_matAct_zero,
    klS_matAct_zero, zero_add] at h
  exact h.symm

/-! ### Lemma 2.3.1 and the two assumptions -/

/-- **Lemma 2.3.1** (Miao, p. 60), with `A = Q₂.Ψ` and `B = Q₂.Π`: for every `ε ∈ ℂ^{n_ε}`
there is `η ∈ ℂ^m` with `Aε + Bη = 0` iff `A = BΛ` for some `m × n_ε` matrix `Λ`. ("For
every `ε_t`" is read as "for every vector value".) The book's proof takes the `j`-th column of
`Λ` to be a solution `η` for `ε = I_j`; that gives `A = −BΛ`, so the column is `−η`. -/
theorem lemma_2_3_1 {p nε m : ℕ} (A : Matrix (Fin p) (Fin nε) ℂ) (B : Matrix (Fin p) (Fin m) ℂ) :
    (∀ e : Fin nε → ℂ, ∃ h : Fin m → ℂ, A *ᵥ e + B *ᵥ h = 0) ↔
      ∃ Λ : Matrix (Fin m) (Fin nε) ℂ, A = B * Λ := by
  constructor
  · intro H
    choose h hh using fun j : Fin nε => H (Pi.single j 1)
    refine ⟨Matrix.of fun k j => -h j k, ?_⟩
    ext i j
    have := congrFun (hh j) i
    simp only [Matrix.mulVec_single_one, Pi.add_apply, Matrix.col_apply, Pi.zero_apply,
      Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_neg, Finset.sum_neg_distrib]
    linear_combination this
  · rintro ⟨Λ, rfl⟩ e
    exact ⟨-(Λ *ᵥ e), by rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, add_neg_cancel]⟩

/-- Lemma 2.3.1 in the notation of (2.23): (2.23) is solvable in `η` for every value of `ε` iff
Assumption 2.3.1 holds. -/
theorem lemma_2_3_1_sims {ns nu nε m : ℕ} (Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ) (Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ) :
    (∀ e : Fin nε → ℂ, ∃ h : Fin m → ℂ, simsBot Q *ᵥ (Ψ *ᵥ e + Pm *ᵥ h) = 0) ↔
      SimsAssumption1 Q Ψ Pm := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  exact lemma_2_3_1 _ _

/-- A vector equation with random right-hand sides proportional to one random variable
`X ≠ 0` has a scalar solution (apply a continuous functional `g` with `g X = ‖X‖`, by
Hahn–Banach). -/
theorem simsH_scalar_of_vec {p nε m : ℕ} (A : Matrix (Fin p) (Fin nε) ℂ)
    (B : Matrix (Fin p) (Fin m) ℂ) {X : V} (hX : X ≠ 0) (e : Fin nε → ℂ) (h : Fin m → V)
    (H : matAct A (fun i => e i • X) + matAct B h = 0) :
    ∃ h' : Fin m → ℂ, A *ᵥ e + B *ᵥ h' = 0 := by
  obtain ⟨g, -, hg⟩ := exists_dual_vector ℂ X (norm_ne_zero_iff.2 hX)
  have hXn : ((‖X‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hX
  have key : A *ᵥ (((‖X‖ : ℝ) : ℂ) • e) + B *ᵥ (fun k => g (h k)) = 0 := by
    funext i
    have := congrArg g (congrFun H i)
    simp only [Pi.add_apply, matAct, map_add, map_sum, map_smul, hg, smul_eq_mul,
      Pi.zero_apply, map_zero] at this
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    rw [← this]
    congr 1
    exact Finset.sum_congr rfl fun j _ => congrArg (A i j * ·) (mul_comm _ _)
  refine ⟨(((‖X‖ : ℝ) : ℂ))⁻¹ • fun k => g (h k), ?_⟩
  have := congrArg ((((‖X‖ : ℝ) : ℂ))⁻¹ • ·) key
  simpa only [Matrix.mulVec_smul, smul_add, smul_smul, inv_mul_cancel₀ hXn, one_smul,
    smul_zero] using this

/-- Lemma 2.3.1 with random right-hand sides (Miao, p. 60, "for every `ε_t`" read as "for
every random vector"): if `V ≠ 0`, (2.23) `Aε + Bη = 0` is solvable in `η ∈ V^m` for every
`ε ∈ V^{n_ε}` iff `A = BΛ` for some matrix `Λ`. -/
theorem lemma_2_3_1_random [Nontrivial V] {p nε m : ℕ} (A : Matrix (Fin p) (Fin nε) ℂ)
    (B : Matrix (Fin p) (Fin m) ℂ) :
    (∀ e : Fin nε → V, ∃ h : Fin m → V, matAct A e + matAct B h = 0) ↔
      ∃ Λ : Matrix (Fin m) (Fin nε) ℂ, A = B * Λ := by
  constructor
  · intro H
    obtain ⟨X, hX⟩ := exists_ne (0 : V)
    refine (lemma_2_3_1 A B).1 fun e => ?_
    obtain ⟨h, hh⟩ := H fun i => e i • X
    exact simsH_scalar_of_vec A B hX e h hh
  · rintro ⟨Λ, rfl⟩ e
    exact ⟨-matAct Λ e, by rw [klS_matAct_neg, matAct_mul, add_neg_cancel]⟩

/-- Miao, p. 60: Assumption 2.3.1 "generalizes the usual existence condition `n_u ≤ m`… we may
have existence even if `n_u > m`": with `n_u = 2`, `m = 1`, `Q = I` and `Ψ = Π = (1, 1)ᵀ`,
Assumption 2.3.1 holds (`Λ = 1`) and `Q₂.Ψ ≠ 0`. -/
theorem assumption_2_3_1_nu_gt_m :
    ∃ (Q : Matrix (Fin (0 + 2)) (Fin (0 + 2)) ℂ) (Ψ Pm : Matrix (Fin (0 + 2)) (Fin 1) ℂ),
      SimsAssumption1 Q Ψ Pm ∧ simsBot Q * Ψ ≠ 0 := by
  refine ⟨1, !![1; 1], !![1; 1], ⟨1, by rw [Matrix.mul_one]⟩, fun h => ?_⟩
  have := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Matrix.one_apply] at this

/-- Assumption 2.3.2 as a kernel condition: `C = ΞB` for some `Ξ` iff `ker B ⊆ ker C`. For
`B = Q₂.Π`, `C = Q₁.Π`: a combination of prediction errors that does not move the unstable
block does not move the stable block either. -/
theorem simsH_factor_iff {p q m : ℕ} (B : Matrix (Fin p) (Fin m) ℂ)
    (C : Matrix (Fin q) (Fin m) ℂ) :
    (∀ v, B *ᵥ v = 0 → C *ᵥ v = 0) ↔ ∃ Ξ : Matrix (Fin q) (Fin p) ℂ, C = Ξ * B := by
  constructor
  · intro H
    have hk : LinearMap.ker (Matrix.mulVecLin B) ≤ LinearMap.ker (Matrix.mulVecLin C) :=
      fun v hv => H v hv
    obtain ⟨h, hh⟩ := LinearMap.exists_extend
      (((LinearMap.ker (Matrix.mulVecLin B)).liftQ (Matrix.mulVecLin C) hk).comp
        (Matrix.mulVecLin B).quotKerEquivRange.symm.toLinearMap)
    refine ⟨LinearMap.toMatrix' h, ?_⟩
    have hv : ∀ v, C *ᵥ v = (LinearMap.toMatrix' h * B) *ᵥ v := fun v => by
      rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
      have := LinearMap.congr_fun hh ⟨B *ᵥ v, LinearMap.mem_range_self _ v⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        LinearEquiv.coe_coe] at this
      rw [this]
      change _ = (LinearMap.ker (Matrix.mulVecLin B)).liftQ (Matrix.mulVecLin C) hk
        ((Matrix.mulVecLin B).quotKerEquivRange.symm ⟨(Matrix.mulVecLin B) v, _⟩)
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      rfl
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using this
  · rintro ⟨Ξ, rfl⟩ v hv
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- Assumption 2.3.2 iff `ker(Q₂.Π) ⊆ ker(Q₁.Π)`. -/
theorem simsAssumption2_iff_ker {ns nu m : ℕ} (Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ) :
    SimsAssumption2 Q Pm ↔
      ∀ v, (simsBot Q * Pm) *ᵥ v = 0 → (simsTop Q * Pm) *ᵥ v = 0 :=
  (simsH_factor_iff _ _).symm

/-! ### The matrices of (2.24) and the solution matrices `Θ₁`, `Θ₂` -/

/-- The left matrix `[[S₁₁, S₁₂ − ΞS₂₂], [0, I]]` of (2.24) (Miao, p. 61). -/
def simsGmat {ns nu : ℕ} (S : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ :=
  simsBlk (sims11 S) (sims12 S - Ξ * sims22 S) 0 1

/-- The matrix `[[T₁₁, T₁₂ − ΞT₂₂], [0, 0]]` of (2.24) (Miao, p. 61). -/
def simsHmat {ns nu : ℕ} (T : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ :=
  simsBlk (sims11 T) (sims12 T - Ξ * sims22 T) 0 0

/-- The matrix `[[Q₁. − ΞQ₂.], [0]]` of (2.24) (Miao, p. 61). -/
def simsKmat {ns nu : ℕ} (Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ :=
  simsRows (simsTop Q - Ξ * simsBot Q) 0

/-- `Θ₁ = Z G⁻¹ H Zᴴ` (Miao, p. 61, corrected: the book omits the final `Zᴴ`, see
`theta_1_printed_false`), with `G = simsGmat S Ξ`, `H = simsHmat T Ξ`. -/
noncomputable def simsTheta1 {ns nu : ℕ} (Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ :=
  Z * (simsGmat (Q * Γ₀ * Z) Ξ)⁻¹ * simsHmat (Q * Γ₁ * Z) Ξ * star Z

/-- `Θ₂ = Z G⁻¹ [[Q₁. − ΞQ₂.], [0]] Ψ` (Miao, p. 61, as printed). -/
noncomputable def simsTheta2 {ns nu nε : ℕ} (Γ₀ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) (Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ) :
    Matrix (Fin (ns + nu)) (Fin nε) ℂ :=
  Z * (simsGmat (Q * Γ₀ * Z) Ξ)⁻¹ * simsKmat Q Ξ * Ψ

/-- `G` is invertible: `det G = det S₁₁ ≠ 0`. -/
theorem simsGmat_det {ns nu : ℕ} {S T : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hS : S.IsUpperTriangular) (hord : ∀ i : Fin (ns + nu), i.val < ns ↔ ‖T i i‖ < ‖S i i‖)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) : (simsGmat S Ξ).det ≠ 0 := by
  rw [simsGmat, simsBlk_det, Matrix.det_one, mul_one]
  exact det_S11_ne_zero hS hord

omit [NormedSpace ℂ V] in
theorem simsH_add_comp {ι κ : Type*} (x z : ι → V) (f : κ → ι) : (x + z) ∘ f = x ∘ f + z ∘ f :=
  rfl

/-- Solving `Gx' = Hx + k` for `y' = Zx'` in terms of `y = Zx` (Miao, p. 61, "Using
`y_t = Zy*_t` and the above equation"): `Zx' = (ZG⁻¹HZᴴ)(Zx) + ZG⁻¹k`. -/
theorem simsH_solve_G {n : ℕ} {G H Z : Matrix (Fin n) (Fin n) ℂ} (hG : G.det ≠ 0)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ) (x x' k : Fin n → V) :
    matAct G x' = matAct H x + k ↔
      matAct Z x' = matAct (Z * G⁻¹ * H * star Z) (matAct Z x) + matAct (Z * G⁻¹) k := by
  have hZZ' : star Z * Z = 1 := Matrix.mem_unitaryGroup_iff'.1 hZ
  have hback : ∀ v : Fin n → V, matAct (star Z) (matAct Z v) = v := fun v => by
    rw [matAct_mul, hZZ', matAct_one]
  have e1 : matAct (Z * G⁻¹ * H * star Z) (matAct Z x) =
      matAct Z (matAct G⁻¹ (matAct H x)) := by
    simp only [matAct_mul, Matrix.mul_assoc, hZZ', Matrix.mul_one]
  rw [e1, ← matAct_mul Z G⁻¹ k, ← matAct_add, ← matAct_add]
  constructor
  · intro h
    rw [← h, klS_matAct_inv_mul hG]
  · intro h
    have h1 := congrArg (matAct (star Z)) h
    rw [hback, hback] at h1
    rw [h1, klS_matAct_mul_inv hG]

/-- Miao, (2.24), p. 61: premultiplying (2.21) by `[I  −Ξ]` and appending `u_t = 0`, every
stable solution satisfies `G y*_t = H y*_{t−1} + [[Q₁. − ΞQ₂.], [0]](Ψε_t + Πη_t)`, for any
`n_s × n_u` matrix `Ξ` (Assumption 2.3.2 is not needed for this step). -/
theorem eq_2_24 [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) (t : ℕ) :
    matAct (simsGmat (Q * Γ₀ * Z) Ξ) (matAct (star Z) (y (t + 1))) =
      matAct (simsHmat (Q * Γ₁ * Z) Ξ) (matAct (star Z) (y t)) +
        matAct (simsKmat Q Ξ) (matAct Ψ (ε (t + 1)) + matAct Pm (η (t + 1))) := by
  have hu := sims_u_eq_zero E hqz hεm hsol hy
  have h23 := eq_2_23 E hqz hεm hsol hy t
  have htop := ((eq_2_21 hqz (y t) (y (t + 1)) _).1 (by rw [hsol.2.2.2 t, add_assoc])).1
  rw [hu, hu, klS_matAct_zero, klS_matAct_zero, add_zero, add_zero] at htop
  refine klS_ext_blocks ?_ ?_
  · rw [simsGmat, simsH_blk_top, simsH_add_comp, simsHmat, simsH_blk_top, simsKmat,
      simsH_top_matAct (simsRows _ _), simsRows_top]
    simp only [simsH_top_matAct, simsH_bot_matAct, hu, klS_matAct_zero, add_zero,
      klS_sub_matAct, ← matAct_mul, h23, sub_zero]
    exact htop
  · rw [simsGmat, simsH_blk_bot, simsH_add_comp, simsHmat, simsH_blk_bot, simsKmat,
      simsH_bot_matAct (simsRows _ _), simsRows_bot]
    simp only [simsH_bot_matAct, hu, klS_zero_matAct, matAct_one, add_zero]

/-- Miao, p. 61: under Assumption 2.3.2 (`Q₁.Π = ΞQ₂.Π`) the prediction errors drop out of
(2.24): `[[Q₁. − ΞQ₂.], [0]]Π = 0`. -/
theorem simsKmat_mul_Pm {ns nu m : ℕ} {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} {Ξ : Matrix (Fin ns) (Fin nu) ℂ}
    (hΞ : simsTop Q * Pm = Ξ * (simsBot Q * Pm)) : simsKmat Q Ξ * Pm = 0 := by
  rw [simsKmat, simsRows_mul, Matrix.sub_mul, Matrix.mul_assoc, ← hΞ, sub_self,
    Matrix.zero_mul]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [simsRows]

/-- **Theorem 2.3.1, the solution formula** (Miao, p. 61). Under Assumption 2.3.2
(`Q₁.Π = ΞQ₂.Π`), every stable solution of (2.20) satisfies `y_t = Θ₁y_{t−1} + Θ₂ε_t` with
`Θ₁ = ZG⁻¹HZᴴ` and `Θ₂ = ZG⁻¹[[Q₁. − ΞQ₂.], [0]]Ψ`. -/
theorem theorem_2_3_1_theta [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {Ξ : Matrix (Fin ns) (Fin nu) ℂ} (hΞ : simsTop Q * Pm = Ξ * (simsBot Q * Pm))
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (t : ℕ) :
    y (t + 1) = matAct (simsTheta1 Γ₀ Γ₁ Q Z Ξ) (y t) +
      matAct (simsTheta2 Γ₀ Q Z Ξ Ψ) (ε (t + 1)) := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hqz.unitary_Z
  have hback : ∀ v : Fin (ns + nu) → V, matAct Z (matAct (star Z) v) = v := fun v => by
    rw [matAct_mul, hZZ, matAct_one]
  have h := eq_2_24 E hqz hεm hsol hy Ξ t
  rw [matAct_add, matAct_mul (simsKmat Q Ξ) Pm, simsKmat_mul_Pm hΞ, klS_zero_matAct,
    add_zero] at h
  have h' := (simsH_solve_G (simsGmat_det hqz.upper_S hqz.ord Ξ) hqz.unitary_Z _ _ _).1 h
  rw [hback, hback] at h'
  rw [h']
  congr 1
  simp only [simsTheta2, matAct_mul, Matrix.mul_assoc]

/-- **Theorem 2.3.1, uniqueness** (Miao, p. 61). Under Assumption 2.3.2, two stable solutions
of (2.20) for the same `ε` with the same initial value `y₀` coincide (whatever their
prediction errors). Assumption 2.3.1 is not needed. -/
theorem theorem_2_3_1_uniqueness [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (hA2 : SimsAssumption2 Q Pm) {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε)
    {y y' : ℕ → Fin (ns + nu) → V} {η η' : ℕ → Fin m → V}
    (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (hsol' : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y' η') (hy' : IsStableProc y') (h0 : y 0 = y' 0) :
    y = y' := by
  obtain ⟨Ξ, hΞ⟩ := hA2
  funext t
  induction t with
  | zero => exact h0
  | succ t ih =>
    rw [theorem_2_3_1_theta E hqz hΞ hεm hsol hy t, theorem_2_3_1_theta E hqz hΞ hεm hsol' hy' t,
      ih]

/-! ### Existence -/

omit [NormedSpace ℂ V] in
theorem simsH_stable_zero {ι : Type*} : IsStableProc (fun _ : ℕ => (0 : ι → V)) :=
  ⟨1, one_pos, fun _ _ => by simp⟩

/-- The construction behind the existence half of Theorem 2.3.1 (Miao, pp. 60–61). Given a
stable adapted `ε` and a stable adapted martingale-difference `η` satisfying (2.23)
(`Q₂.(Ψε_t + Πη_t) = 0`), and an `F₀`-measurable `y₀` with `Z₂ᴴy₀ = 0`, the recursion
`u_t = 0`, `s_t = S₁₁⁻¹T₁₁s_{t−1} + S₁₁⁻¹Q₁.(Ψε_t + Πη_t)`, `s₀ = Z₁ᴴy₀` defines a stable
solution `y_t = Z(s_t, 0)` of (2.20) with prediction error `η`. -/
theorem simsH_core_exists [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ε : ℕ → Fin nε → V} (hεa : IsAdaptedV E ε) (hεs : IsStableProc ε)
    {η : ℕ → Fin m → V} (hηa : IsAdaptedV E η) (hηm : IsMartingaleDiffProc E η)
    (hηs : IsStableProc η)
    (h23 : ∀ t, matAct (simsBot Q) (matAct Ψ (ε (t + 1)) + matAct Pm (η (t + 1))) = 0)
    (y₀ : Fin (ns + nu) → V) (hy₀a : Evec E 0 y₀ = y₀)
    (hy₀ : matAct (simsBot (star Z)) y₀ = 0) :
    ∃ y, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η ∧ IsStableProc y ∧ y 0 = y₀ := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hqz.unitary_Z
  have hZZ' : star Z * Z = 1 := Matrix.mem_unitaryGroup_iff'.1 hqz.unitary_Z
  have hS11 := det_S11_ne_zero hqz.upper_S hqz.ord
  set w : ℕ → Fin (ns + nu) → V := fun t => matAct Ψ (ε t) + matAct Pm (η t) with hw
  have hwa : ∀ t, Evec E t (w t) = w t := fun t => by
    rw [hw]
    simp only [klS_Evec_add, Evec_matAct, show Evec E t (ε t) = ε t from funext (hεa t),
      show Evec E t (η t) = η t from funext (hηa t)]
  have hws : IsStableProc w := klS_stable_add (klS_stable_matAct hεs Ψ) (klS_stable_matAct hηs Pm)
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℕ → Fin ns → V, s 0 = matAct (simsTop (star Z)) y₀ ∧
      ∀ t, s (t + 1) = matAct ((sims11 (Q * Γ₀ * Z))⁻¹ * sims11 (Q * Γ₁ * Z)) (s t) +
        matAct ((sims11 (Q * Γ₀ * Z))⁻¹ * simsTop Q) (w (t + 1)) :=
    ⟨fun t => Nat.rec (matAct (simsTop (star Z)) y₀)
      (fun t st => matAct ((sims11 (Q * Γ₀ * Z))⁻¹ * sims11 (Q * Γ₁ * Z)) st +
        matAct ((sims11 (Q * Γ₀ * Z))⁻¹ * simsTop Q) (w (t + 1))) t,
      rfl, fun _ => rfl⟩
  have hss : IsStableProc s := klS_stable_of_rec
    (klS_summable_ent (summable_Ms hqz.upper_S hqz.upper_T hqz.ord))
    (klS_stable_matAct (klS_stable_shift hws 1) _) hs
  have hsa : ∀ t, Evec E t (s t) = s t := by
    intro t
    induction t with
    | zero => rw [hs0, Evec_matAct, hy₀a]
    | succ t ih => rw [hs, klS_Evec_add, Evec_matAct, Evec_matAct, klS_adapted_succ E ih, hwa]
  set x : ℕ → Fin (ns + nu) → V := fun t => Fin.append (s t) 0 with hx
  have hxs : ∀ t, matAct (star Z) (matAct Z (x t)) = x t := fun t => by
    rw [matAct_mul, hZZ', matAct_one]
  have hxt : ∀ t, matAct (simsTop (star Z)) (matAct Z (x t)) = s t := fun t => by
    rw [← simsH_top_matAct, hxs, hx, klS_append_castAdd]
  have hxb : ∀ t, matAct (simsBot (star Z)) (matAct Z (x t)) = 0 := fun t => by
    rw [← simsH_bot_matAct, hxs, hx, klS_append_natAdd]
  refine ⟨fun t => matAct Z (x t), ⟨fun t i => ?_, hηa, hηm, fun t => ?_⟩, ?_, ?_⟩
  · change Evec E t (matAct Z (x t)) i = matAct Z (x t) i
    rw [Evec_matAct, hx, klS_Evec_append, hsa, klS_Evec_zero]
  · rw [add_assoc]
    refine (eq_2_21 hqz _ _ (w (t + 1))).2 ⟨?_, ?_⟩
    · rw [hxt, hxt, hxb, hxb, klS_matAct_zero, klS_matAct_zero, add_zero, add_zero, hs,
        matAct_add, ← matAct_mul, ← matAct_mul, klS_matAct_mul_inv hS11,
        klS_matAct_mul_inv hS11]
    · rw [hxb, hxb, klS_matAct_zero, klS_matAct_zero, zero_add]
      exact (h23 t).symm
  · exact klS_stable_matAct (klS_stable_append hss simsH_stable_zero) Z
  · change matAct Z (Fin.append (s 0) 0) = y₀
    have : Fin.append (s 0) 0 = matAct (star Z) y₀ := by
      refine klS_ext_blocks ?_ ?_
      · rw [klS_append_castAdd, hs0]
        rfl
      · rw [klS_append_natAdd, simsH_bot_matAct, hy₀]
    rw [this, matAct_mul, hZZ, matAct_one]

/-- **Theorem 2.3.1, existence** (Miao, pp. 60–61). Under Assumption 2.3.1 (`Q₂.Ψ = Q₂.ΠΛ`),
for every exogenous shock `ε` (adapted, stable, martingale difference) and every
`F₀`-measurable `y₀` with `Z₂ᴴy₀ = 0` there is a stable solution of (2.20) with `y_0 = y₀`,
whose prediction error is `η_t = −Λε_t` (stable). Assumption 2.3.2 is not needed. -/
theorem theorem_2_3_1_existence [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {Λ : Matrix (Fin m) (Fin nε) ℂ} (hΛ : simsBot Q * Ψ = simsBot Q * Pm * Λ)
    {ε : ℕ → Fin nε → V} (hε : IsSimsShock E ε)
    (y₀ : Fin (ns + nu) → V) (hy₀a : Evec E 0 y₀ = y₀)
    (hy₀ : matAct (simsBot (star Z)) y₀ = 0) :
    ∃ y, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y (fun t => -matAct Λ (ε t)) ∧ IsStableProc y ∧
      y 0 = y₀ := by
  obtain ⟨hεa, hεm, hεs⟩ := hε
  refine simsH_core_exists E hqz hεa hεs (fun t i => ?_) (fun t i => ?_)
    (by simpa only [klS_neg_matAct] using klS_stable_matAct hεs (-Λ)) (fun t => ?_) y₀ hy₀a hy₀
  · change Evec E t (-matAct Λ (ε t)) i = -matAct Λ (ε t) i
    rw [klS_Evec_neg, Evec_matAct, show Evec E t (ε t) = ε t from funext (hεa t)]
    rfl
  · change Evec E t (-matAct Λ (ε (t + 1))) i = (0 : Fin m → V) i
    rw [klS_Evec_neg, Evec_matAct, show Evec E t (ε (t + 1)) = 0 from funext (hεm t),
      klS_matAct_zero, neg_zero]
  · rw [matAct_add, klS_matAct_neg, klS_matAct_neg, matAct_mul, matAct_mul, matAct_mul, ← hΛ,
      add_neg_cancel]

/-- **Theorem 2.3.1, sufficiency** (Miao, p. 61). Under Assumptions 2.3.1 and 2.3.2, for every
exogenous shock `ε` and every `F₀`-measurable `y₀` with `Z₂ᴴy₀ = 0` there is exactly one
stable `y` with `y_0 = y₀` solving (2.20) for some prediction error `η`; it is
`y_t = Θ₁y_{t−1} + Θ₂ε_t` (`theorem_2_3_1_theta`). Uniqueness is of `y`, not of `η`
(see `SimsSVD`). The initial value is free subject to `Z₂ᴴy₀ = 0` (`sims_Z2_y0`). -/
theorem theorem_2_3_1_sufficiency [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (hA1 : SimsAssumption1 Q Ψ Pm) (hA2 : SimsAssumption2 Q Pm) {ε : ℕ → Fin nε → V}
    (hε : IsSimsShock E ε) (y₀ : Fin (ns + nu) → V) (hy₀a : Evec E 0 y₀ = y₀)
    (hy₀ : matAct (simsBot (star Z)) y₀ = 0) :
    ∃! y, (∃ η, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) ∧ IsStableProc y ∧ y 0 = y₀ := by
  obtain ⟨Λ, hΛ⟩ := hA1
  obtain ⟨y, hy1, hy2, hy3⟩ := theorem_2_3_1_existence E hqz hΛ hε y₀ hy₀a hy₀
  refine ⟨y, ⟨⟨_, hy1⟩, hy2, hy3⟩, ?_⟩
  rintro y' ⟨⟨η', h'⟩, hs', h0'⟩
  exact (theorem_2_3_1_uniqueness E hqz hA2 hε.2.1 hy1 hy2 h' hs' (hy3.trans h0'.symm)).symm

/-! ### Necessity -/

/-- A filtration rich enough for the necessity half of Theorem 2.3.1: there is a stable adapted
scalar martingale difference `ζ` with `ζ₁ ≠ 0` (true for `L¹` of any probability space carrying
a nondegenerate shock at date 1, e.g. `simsRich_trunc`). Without such a `ζ` the stochastic
content of (2.20) is void (`theorem_2_3_1_necessity_false`). -/
def SimsRich (E : CondExpSystem ℂ V) : Prop :=
  ∃ ζ : ℕ → V, (∀ t, E.E t (ζ t) = ζ t) ∧ (∀ t, E.E t (ζ (t + 1)) = 0) ∧
    (∃ M, ∀ t, ‖ζ t‖ ≤ M) ∧ ζ 1 ≠ 0

/-- A vector `c` times a stable adapted scalar martingale difference `ζ` is an exogenous
shock. -/
theorem simsH_rich_shock {k : ℕ} (E : CondExpSystem ℂ V) {ζ : ℕ → V}
    (hζa : ∀ t, E.E t (ζ t) = ζ t) (hζm : ∀ t, E.E t (ζ (t + 1)) = 0) {M : ℝ}
    (hζb : ∀ t, ‖ζ t‖ ≤ M) (c : Fin k → ℂ) : IsSimsShock E (fun t i => c i • ζ t) := by
  refine ⟨fun t i => by simp only [map_smul, hζa], fun t i => by simp only [map_smul, hζm,
    smul_zero], isStableProc_of_uniformly_bounded (M := ‖c‖ * M) fun t i => ?_⟩
  rw [norm_smul]
  exact mul_le_mul (norm_le_pi_norm c i) (hζb t) (norm_nonneg _) (norm_nonneg _)

theorem simsH_zero_shock {k : ℕ} (E : CondExpSystem ℂ V) :
    IsSimsShock E (0 : ℕ → Fin k → V) :=
  ⟨fun _ _ => map_zero _, fun _ _ => map_zero _, simsH_stable_zero⟩

theorem simsH_zero_solution {n nε m : ℕ} (E : CondExpSystem ℂ V)
    (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ) (Ψ : Matrix (Fin n) (Fin nε) ℂ)
    (Pm : Matrix (Fin n) (Fin m) ℂ) : IsSimsSolution E Γ₀ Γ₁ Ψ Pm 0 0 0 :=
  ⟨fun _ _ => map_zero _, fun _ _ => map_zero _, fun _ _ => map_zero _, fun _ => by
    simp only [Pi.zero_apply, klS_matAct_zero, add_zero]⟩

/-- **Theorem 2.3.1, necessity of Assumption 2.3.1** (Miao, p. 60, "for a solution to (2.20)
to exist, we must make the following"). If the filtration is rich (`SimsRich`) and (2.20) has a
stable solution for every exogenous shock `ε`, then Assumption 2.3.1 holds: take
`ε_t = eζ_t`; (2.23) at `t = 1` and a functional separating `ζ₁` give a scalar solution of
Lemma 2.3.1's equation for every `e`. -/
theorem theorem_2_3_1_necessity_1 [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (hex : ∀ ε : ℕ → Fin nε → V, IsSimsShock E ε →
      ∃ y η, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η ∧ IsStableProc y) :
    SimsAssumption1 Q Ψ Pm := by
  obtain ⟨ζ, hζa, hζm, ⟨M, hζb⟩, hζ1⟩ := hrich
  refine (lemma_2_3_1 _ _).1 fun e => ?_
  have hsh := simsH_rich_shock E hζa hζm hζb e
  obtain ⟨y, η, hsol, hy⟩ := hex _ hsh
  have h := eq_2_23 E hqz hsh.2.1 hsol hy 0
  rw [matAct_add, matAct_mul, matAct_mul] at h
  exact simsH_scalar_of_vec _ _ hζ1 e _ h

/-- **Theorem 2.3.1, necessity of Assumption 2.3.2** (Miao, pp. 60–61). If the filtration is
rich and the homogeneous system (`ε = 0`) has only the zero stable solution from `y₀ = 0`, then
Assumption 2.3.2 holds. Otherwise there is `v` with `Q₂.Πv = 0`, `Q₁.Πv ≠ 0`, and the
sunspot-like prediction error `η_t = vζ_t` drives a nonzero stable solution. -/
theorem theorem_2_3_1_necessity_2 [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (huniq : ∀ y η, IsSimsSolution E Γ₀ Γ₁ Ψ Pm (0 : ℕ → Fin nε → V) y η → IsStableProc y →
      y 0 = 0 → y = 0) :
    SimsAssumption2 Q Pm := by
  obtain ⟨ζ, hζa, hζm, ⟨M, hζb⟩, hζ1⟩ := hrich
  rw [simsAssumption2_iff_ker]
  intro v hv
  by_contra hne
  obtain ⟨hηa, hηm, hηs⟩ := simsH_rich_shock E hζa hζm hζb v
  obtain ⟨y, hsol, hy, hy0⟩ := simsH_core_exists E hqz (simsH_zero_shock E).1
    (simsH_zero_shock E).2.2 hηa hηm hηs (fun t => by
      rw [Pi.zero_apply, klS_matAct_zero, zero_add, simsH_matAct_smul, simsH_matAct_smul,
        Matrix.mulVec_mulVec, hv]
      funext i
      simp) 0 (klS_Evec_zero E 0) (klS_matAct_zero _)
  have he := hsol.2.2.2 0
  rw [huniq y _ hsol hy hy0] at he
  simp only [Pi.zero_apply, klS_matAct_zero, zero_add, simsH_matAct_smul] at he
  have hPv : Pm *ᵥ v = 0 := funext fun i => by
    have := congrFun he i
    simp only [Pi.zero_apply] at this
    exact (smul_eq_zero.1 this.symm).resolve_right hζ1
  exact hne (by rw [← Matrix.mulVec_mulVec, hPv, Matrix.mulVec_zero])

/-- **Theorem 2.3.1** (Sims, Miao, p. 61), the correct form of "Assumptions 2.3.1–2.3.2 are
necessary and sufficient for the existence of a unique stable solution to (2.20)" (the text on
p. 62 calls it "Theorem 2.19"). For a regular pencil with an ordered QZ form and no generalized
eigenvalue on the unit circle, and a rich filtration (`SimsRich`): for every exogenous shock `ε`
and every admissible initial value `y₀` (`F₀`-measurable, `Z₂ᴴy₀ = 0`) there is exactly one
stable `y` with `y_0 = y₀` that solves (2.20) with some prediction error `η` iff Assumptions
2.3.1 and 2.3.2 hold. "Unique" refers to `y`; `η` is unique only when moreover `m = r`
(`corollary_2_3_1`). Sufficiency needs no richness (`theorem_2_3_1_sufficiency`); necessity
fails without it (`theorem_2_3_1_necessity_false`). -/
theorem theorem_2_3_1 [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} :
    (∀ ε : ℕ → Fin nε → V, IsSimsShock E ε → ∀ y₀ : Fin (ns + nu) → V, Evec E 0 y₀ = y₀ →
      matAct (simsBot (star Z)) y₀ = 0 →
        ∃! y, (∃ η, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) ∧ IsStableProc y ∧ y 0 = y₀) ↔
      SimsAssumption1 Q Ψ Pm ∧ SimsAssumption2 Q Pm := by
  constructor
  · intro H
    refine ⟨theorem_2_3_1_necessity_1 E hrich hqz fun ε hε => ?_,
      theorem_2_3_1_necessity_2 E hrich hqz (Ψ := Ψ) fun y η hsol hy hy0 => ?_⟩
    · obtain ⟨y, ⟨⟨η, hsol⟩, hy, -⟩, -⟩ := H ε hε 0 (klS_Evec_zero E 0) (klS_matAct_zero _)
      exact ⟨y, η, hsol, hy⟩
    · obtain ⟨y', -, hu⟩ := H 0 (simsH_zero_shock E) 0 (klS_Evec_zero E 0) (klS_matAct_zero _)
      exact (hu y ⟨⟨η, hsol⟩, hy, hy0⟩).trans
        (hu 0 ⟨⟨0, simsH_zero_solution E Γ₀ Γ₁ Ψ Pm⟩, simsH_stable_zero, rfl⟩).symm
  · rintro ⟨hA1, hA2⟩ ε hε y₀ hy₀a hy₀
    exact theorem_2_3_1_sufficiency E hqz hA1 hA2 hε y₀ hy₀a hy₀

/-! ### Counterexamples and a rich filtration -/

/-- The truncation system on `ℓ^∞(ℕ)` (`klM_truncSystem`) is rich: `ζ_t = e_t` is adapted, a
martingale difference, bounded by `1`, and `ζ₁ ≠ 0`. -/
theorem simsRich_trunc : SimsRich klM_truncSystem := by
  refine ⟨fun t => lp.single ⊤ t 1, fun t => ?_, fun t => ?_, ⟨1, fun t => ?_⟩, ?_⟩
  · refine lp.ext (funext fun n => ?_)
    change klM_trunc t _ n = _
    rw [klM_trunc_apply]
    split_ifs with h
    · rfl
    · rw [lp.single_apply_ne ⊤ t _ (by omega)]
  · refine lp.ext (funext fun n => ?_)
    change klM_trunc t _ n = _
    rw [klM_trunc_apply]
    split_ifs with h
    · rw [lp.single_apply_ne ⊤ (t + 1) _ (by omega)]
      rfl
    · rfl
  · rw [lp.norm_single ENNReal.zero_lt_top, norm_one]
  · intro h
    have := congrArg (fun f : lp (fun _ : ℕ => ℂ) ⊤ => f 1) h
    simp only [lp.single_apply_self] at this
    exact one_ne_zero this

/-- With `E_t = id` a martingale difference vanishes from date 1 on. -/
theorem simsH_det_mdiff {k : ℕ} {x : ℕ → Fin k → ℂ} (h : IsMartingaleDiffProc klS_detSystem x)
    (t : ℕ) : x (t + 1) = 0 :=
  funext (h t)

/-- With `E_t = id`, the shocks and prediction errors of (2.20) vanish, so `Ψ` and `Π` play no
role. -/
theorem simsH_det_sol_iff {n nε m : ℕ} {Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ}
    {Ψ : Matrix (Fin n) (Fin nε) ℂ} {Pm : Matrix (Fin n) (Fin m) ℂ} {ε : ℕ → Fin nε → ℂ}
    (hεm : IsMartingaleDiffProc klS_detSystem ε) (y : ℕ → Fin n → ℂ) (η : ℕ → Fin m → ℂ) :
    IsSimsSolution klS_detSystem Γ₀ Γ₁ Ψ Pm ε y η ↔
      IsSimsSolution klS_detSystem Γ₀ Γ₁ 0 0 ε y η := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun t => ?_⟩
    have := h4 t
    rw [simsH_det_mdiff hεm t, simsH_det_mdiff h3 t] at this ⊢
    simpa only [klS_matAct_zero, klS_zero_matAct, add_zero] using this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun t => ?_⟩
    have := h4 t
    rw [simsH_det_mdiff hεm t, simsH_det_mdiff h3 t] at this ⊢
    simpa only [klS_matAct_zero, klS_zero_matAct, add_zero] using this

/-- **Counterexample to the necessity half of Theorem 2.3.1 as printed** (Miao, p. 61). In the
deterministic system `E_t = id` (`klS_detSystem`), take `Γ₀ = I`, `Γ₁ = diag(1/2, 2)`,
`Q = Z = I`, `Ψ = e₂`, `Π = e₁`. Then `Q₂.Ψ = 1`, `Q₂.Π = 0`, `Q₁.Π = 1`, so both Assumption
2.3.1 and Assumption 2.3.2 fail; yet for every shock and every admissible `y₀` there is
exactly one stable solution (martingale differences are zero, so `Ψ` and `Π` play no role).
Necessity needs a rich filtration (`theorem_2_3_1`). -/
theorem theorem_2_3_1_necessity_false :
    ∃ (Γ₀ Γ₁ Q Z : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) (Ψ : Matrix (Fin (1 + 1)) (Fin 1) ℂ)
      (Pm : Matrix (Fin (1 + 1)) (Fin 1) ℂ),
      IsSimsQZ Γ₀ Γ₁ Q Z ∧ ¬ SimsAssumption1 Q Ψ Pm ∧ ¬ SimsAssumption2 Q Pm ∧
      ∀ ε : ℕ → Fin 1 → ℂ, IsSimsShock klS_detSystem ε → ∀ y₀ : Fin (1 + 1) → ℂ,
        Evec klS_detSystem 0 y₀ = y₀ → matAct (simsBot (star Z)) y₀ = 0 →
          ∃! y, (∃ η, IsSimsSolution klS_detSystem Γ₀ Γ₁ Ψ Pm ε y η) ∧ IsStableProc y ∧
            y 0 = y₀ := by
  have hqz : IsSimsQZ (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) !![1 / 2, 0; 0, 2] 1 1 := by
    refine ⟨one_mem _, one_mem _, ?_, ?_, fun i => ?_, fun i => ?_⟩
    · rw [Matrix.mul_one, Matrix.mul_one]
      exact fun i j h => Matrix.one_apply_ne (ne_of_lt h).symm
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> norm_num
    · fin_cases i <;> norm_num
  refine ⟨1, !![1 / 2, 0; 0, 2], 1, 1, !![0; 1], !![1; 0], hqz, ?_, ?_, ?_⟩
  · rintro ⟨Λ, hΛ⟩
    have := congrFun (congrFun hΛ 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Fin.ext_iff] at this
  · rintro ⟨Ξ, hΞ⟩
    have := congrFun (congrFun hΞ 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Fin.ext_iff] at this
  · intro ε hε y₀ h1 h2
    refine (existsUnique_congr fun y => and_congr_left' (exists_congr fun η =>
      (simsH_det_sol_iff hε.2.1 y η).symm)).1 ?_
    exact theorem_2_3_1_sufficiency klS_detSystem hqz ⟨0, by simp⟩ ⟨0, by simp⟩ hε y₀ h1 h2

/-- `matAct (c • M) x = c • matAct M x`. -/
theorem simsH_smul_matAct {ι κ : Type*} [Fintype κ] (c : ℂ) (M : Matrix ι κ ℂ) (x : κ → V) :
    matAct (c • M) x = c • matAct M x := by
  funext i
  simp only [matAct, Matrix.smul_apply, smul_eq_mul, mul_smul, Pi.smul_apply, Finset.smul_sum]

theorem simsH_upper_one (M : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) : M.IsUpperTriangular := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  rw [Fin.lt_def] at h
  omega

/-- **Counterexample to the printed `Θ₁`** (Miao, p. 61). The book writes
`Θ₁ = Z G⁻¹ H`; the correct matrix is `Θ₁ = Z G⁻¹ H Zᴴ` (`theorem_2_3_1_theta`). With
`n = n_s = 1`, `Γ₀ = 1`, `Γ₁ = 1/2`, the QZ form `Q = Z = −1` (so `S = 1`, `T = 1/2`), `E_t = id`
and `ε = 0`, the stable solution from `y₀ = 1` has `y₁ = 1/2 = Θ₁y₀`, while the printed matrix
gives `Z G⁻¹ H y₀ = −1/2`. -/
theorem theta_1_printed_false :
    ∃ (Γ₀ Γ₁ Q Z : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) (Ξ : Matrix (Fin 1) (Fin 0) ℂ)
      (y : ℕ → Fin (1 + 0) → ℂ),
      IsSimsQZ Γ₀ Γ₁ Q Z ∧
      (∃ η, IsSimsSolution klS_detSystem Γ₀ Γ₁ (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ)
        (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ) 0 y η) ∧ IsStableProc y ∧
      y 1 = matAct (simsTheta1 Γ₀ Γ₁ Q Z Ξ) (y 0) ∧
      y 1 ≠ matAct (Z * (simsGmat (Q * Γ₀ * Z) Ξ)⁻¹ * simsHmat (Q * Γ₁ * Z) Ξ) (y 0) := by
  set Γ₁ : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ := (1 / 2 : ℂ) • 1
  have hu : (-1 : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) ∈ Matrix.unitaryGroup (Fin (1 + 0)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_neg, star_one, neg_mul_neg, Matrix.one_mul]
  have hS : (-1) * 1 * (-1) = (1 : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) := by
    rw [Matrix.mul_one, neg_mul_neg, Matrix.one_mul]
  have hT : (-1) * Γ₁ * (-1) = Γ₁ := by
    rw [neg_mul, Matrix.one_mul, neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]
  have hqz : IsSimsQZ 1 Γ₁ (-1) (-1) := by
    refine ⟨hu, hu, simsH_upper_one _, simsH_upper_one _, fun i => ?_, fun i => ?_⟩
    · rw [hS, hT]
      refine iff_of_true (by omega) ?_
      norm_num [Γ₁]
    · rw [hS, hT]
      norm_num [Γ₁]
  have hΞ : simsTop (-1 : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) *
      (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ) = (0 : Matrix (Fin 1) (Fin 0) ℂ) *
        (simsBot (-1 : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) *
          (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ)) := by
    rw [Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_zero]
  obtain ⟨y, hsol, hy, hy0⟩ := theorem_2_3_1_existence klS_detSystem hqz
    (Ψ := (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ)) (Pm := (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ))
    (Λ := 0) (by simp)
    (simsH_zero_shock _) (fun _ => 1) rfl (funext fun i => Fin.elim0 i)
  have h1 := theorem_2_3_1_theta klS_detSystem hqz hΞ (simsH_zero_shock _).2.1 hsol hy 0
  rw [Pi.zero_apply, klS_matAct_zero] at h1
  replace h1 := h1.trans (add_zero _)
  refine ⟨1, Γ₁, -1, -1, 0, y, hqz, ⟨_, hsol⟩, hy, h1, fun h => ?_⟩
  have he := hsol.2.2.2 0
  rw [matAct_one, klS_zero_matAct, klS_zero_matAct, hy0, simsH_smul_matAct, matAct_one] at he
  replace he := he.trans ((add_zero _).trans (add_zero _))
  have h10 : y 1 0 = 1 / 2 := by
    have := congrFun he 0
    simpa using this
  have hpr : (-1) * (simsGmat ((-1) * 1 * (-1)) 0)⁻¹ * simsHmat ((-1) * Γ₁ * (-1)) 0 =
      simsTheta1 1 Γ₁ (-1) (-1) (0 : Matrix (Fin 1) (Fin 0) ℂ) * (-1) := by
    simp only [simsTheta1, star_neg, star_one, Matrix.mul_assoc, neg_mul_neg,
      Matrix.mul_one]
  rw [hpr, ← matAct_mul, klS_neg_matAct, matAct_one, klS_matAct_neg, ← h1] at h
  have := congrFun h 0
  rw [Pi.neg_apply, h10] at this
  norm_num at this

/-- **Counterexample to (2.22) as printed** (Miao, p. 59). The book's forward solution
`u_t = −T₂₂⁻¹∑_{j≥1} (T₂₂⁻¹S₂₂)ʲ c_{t+j}` (with `c_t = Q₂.(Ψε_t + Πη_t)`) fails for the
scalar recursion `S₂₂u_{t+1} = T₂₂u_t + c_{t+1}` with `S₂₂ = 0`, `T₂₂ = 1` (an infinite
generalized eigenvalue), `c ≡ 1`, `u ≡ −1`: the printed sum vanishes. The correct formula is
`eq_2_22`. (In a stable solution of (2.20) both sides vanish after `E_t`, `eq_2_22_expect`.) -/
theorem eq_2_22_printed_false :
    ∃ (S22 T22 : Matrix (Fin 1) (Fin 1) ℂ) (u c : ℕ → Fin 1 → ℂ),
      T22.det ≠ 0 ∧ (∀ i, ‖S22 i i‖ < ‖T22 i i‖) ∧ IsStableProc u ∧ IsStableProc c ∧
      (∀ t, matAct S22 (u (t + 1)) = matAct T22 (u t) + c (t + 1)) ∧
      u 0 ≠ -matAct T22⁻¹ (∑' j, matAct ((T22⁻¹ * S22) ^ (j + 1)) (c (0 + 1 + j))) := by
  refine ⟨0, 1, fun _ _ => -1, fun _ _ => 1, by simp, fun i => by simp,
    isStableProc_of_uniformly_bounded (M := 1) fun t i => by simp,
    isStableProc_of_uniformly_bounded (M := 1) fun t i => by simp, fun t => ?_, ?_⟩
  · rw [klS_zero_matAct, matAct_one]
    funext i
    simp
  · simp only [Matrix.mul_zero, pow_succ, klS_zero_matAct, tsum_zero, klS_matAct_zero, neg_zero]
    intro h
    have := congrFun h 0
    simp at this

end Miao.RationalExpectations

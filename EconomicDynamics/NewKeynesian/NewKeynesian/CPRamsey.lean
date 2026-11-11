/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.Singular
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Optimal policy under commitment: the Ramsey problem and its first-order conditions

Copied from `EconomicDynamics/LinearQuadratic` (module `CPRamsey`), namespace renamed.

Miao, §9.4, pp. 304–307. The equilibrium system (9.18) is
`D[z_{t+1}; E_t y_{t+1}] = A[z_t; y_t] + Bu_t + [Cε_{t+1}; 0]` with `D = [I 0; D₂₁ D₂₂]`, the
period loss is (9.19), and the policymaker minimises `E∑ βᵗL_t` once and for all at date `0`.

**Representation.** The predetermined variables `z_t`, the forward-looking variables `y_t` and
the instruments `u_t` are indexed by arbitrary finite types `Z`, `Y`, `U`; the state
`(z_t, y_t)` is a vector on `Z ⊕ Y` and the augmented vector `x_t = (z_t, y_t, u_t)` a vector on
`(Z ⊕ Y) ⊕ U`. The augmented matrices are `D̄ = [D 0]` (`cpDbar`), `Ā = [A B]` (`cpAbar`) and
`W = [Q S; S' R]` (`cpW`).

* `eq_9_19_W` (p. 306): `L_t = ½x_t'Wx_t`; `cp_augmented` (p. 306): the augmented system is
  `D̄x_{t+1} = Āx_t + [Cε_{t+1}; 0]`.
* The Lagrangian (p. 306), truncated at a horizon `T` and with the shocks and expectations
  replaced by a given (perfect-foresight) path: `cpLagrangian`, with the multiplier term
  `β^{t+1}μ_{t+1}'(D̄x_{t+1} − Āx_t − c_{t+1})` and the initial term `μ_{z0}'(z₀ − z̄₀)`.
  `cp_lagrangian_perturb` computes it exactly along a perturbation `x_s ↦ x_s + εh` of one
  date `s < T`: it changes by `εβˢ g_s·h + ε²βˢ½h'Wh`, where `g_s` (`cpGrad`) is
  `Wx_s + D̄'μ_s − βĀ'μ_{s+1}` (for `s = 0`, `D̄'μ_0` is replaced by `(μ_{z0}, 0, 0)`).
  `cp_hasDerivAt` is the derivative, and `eq_foc_9_4` the first-order conditions: the
  Lagrangian is stationary in `x_s` iff `g_s = 0`. `cp_init_eq_Dbar` shows that with
  `μ_{y0} = 0` and `D = [I 0; D₂₁ D₂₂]` the date-`0` condition has the same form
  `Wx₀ + D̄'μ₀ − βĀ'μ₁ = 0` (`cp_grad_eq`), as the book writes it.
* `eq_9_22` (p. 307): the first-order conditions together with (9.18) are the stacked system
  `[D̄ 0; 0 βĀ'][x_{t+1}; μ_{t+1}] = [Ā 0; W D̄'][x_t; μ_t] + [c_{t+1}; 0]`.

**Departures.** The book's first-order conditions contain `E_t μ_{t+1}`; the conditioning step
(the multiplier enters linearly) is not formalised, so the Lagrangian is written along one
realised path (perfect foresight), as in `LQKlein`. The book writes the initial term as
`μ_{z0}'D̄(z₀ − z̄₀)`, which is not dimensionally consistent; we use `μ_{z0}'(z₀ − z̄₀)`, which
is what the book's date-`0` first-order condition uses (`cp_init_eq_Dbar`). The garbled printed
`D̄` is read as `[D 0]`, the only reading consistent with (9.22).
-/

namespace Miao.NewKeynesian

open scoped Matrix

/-! ### Dot products -/

/-- The dot product of two vectors on a sum type. -/
theorem cp_sumElim_dotProduct {α β : Type*} [Fintype α] [Fintype β] (a c : α → ℝ)
    (b d : β → ℝ) : Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- `v'Mw = w'M'v`. -/
theorem cp_dotProduct_mulVec_comm {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℝ)
    (v : α → ℝ) (w : β → ℝ) : v ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (Mᵀ *ᵥ v) := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

/-- For symmetric `M`, `v'Mw = (Mv)·w`. -/
theorem cp_dotProduct_mulVec_symm {α : Type*} [Fintype α] {M : Matrix α α ℝ} (hM : Mᵀ = M)
    (v w : α → ℝ) : v ⬝ᵥ (M *ᵥ w) = (M *ᵥ v) ⬝ᵥ w := by
  rw [cp_dotProduct_mulVec_comm, hM, dotProduct_comm]

variable {Z Y U : Type*} [Fintype Z] [Fintype Y] [Fintype U]

/-! ### The loss function and the augmented system -/

/-- The period loss (9.19) (Miao, p. 304):
`L = ½[z; y]'Q[z; y] + ½u'Ru + [z; y]'Su`. -/
noncomputable def cpLoss (Q : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) (S : Matrix (Z ⊕ Y) U ℝ) (R : Matrix U U ℝ)
    (s : Z ⊕ Y → ℝ) (u : U → ℝ) : ℝ :=
  (1 / 2) * (s ⬝ᵥ (Q *ᵥ s)) + (1 / 2) * (u ⬝ᵥ (R *ᵥ u)) + s ⬝ᵥ (S *ᵥ u)

/-- The weighting matrix `W = [Q S; S' R]` (Miao, p. 306). -/
def cpW (Q : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) (S : Matrix (Z ⊕ Y) U ℝ) (R : Matrix U U ℝ) :
    Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ :=
  Matrix.fromBlocks Q S Sᵀ R

/-- `D̄ = [D 0]` (Miao, p. 306). -/
def cpDbar (U : Type*) (D : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ :=
  Matrix.fromCols D 0

/-- `Ā = [A B]` (Miao, p. 306). -/
def cpAbar (A : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) (B : Matrix (Z ⊕ Y) U ℝ) :
    Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ :=
  Matrix.fromCols A B

/-- Miao, p. 306: the period loss (9.19) is `L_t = ½[z_t; y_t; u_t]'W[z_t; y_t; u_t]`. -/
theorem eq_9_19_W (Q : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) (S : Matrix (Z ⊕ Y) U ℝ)
    (R : Matrix U U ℝ) (s : Z ⊕ Y → ℝ) (u : U → ℝ) :
    cpLoss Q S R s u = (1 / 2) * (Sum.elim s u ⬝ᵥ (cpW Q S R *ᵥ Sum.elim s u)) := by
  simp only [cpLoss, cpW, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    cp_sumElim_dotProduct, dotProduct_add]
  rw [cp_dotProduct_mulVec_comm Sᵀ u s, Matrix.transpose_transpose]
  ring

/-- Miao, p. 306: appending the instruments, (9.18) reads `D̄x_{t+1} = Āx_t + [Cε_{t+1}; 0]`
with `x_t = (z_t, y_t, u_t)`: `D̄x = D[z; y]` and `Āx = A[z; y] + Bu`. -/
theorem cp_augmented (D A : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) (B : Matrix (Z ⊕ Y) U ℝ)
    (s : Z ⊕ Y → ℝ) (u : U → ℝ) :
    cpDbar U D *ᵥ Sum.elim s u = D *ᵥ s ∧ cpAbar A B *ᵥ Sum.elim s u = A *ᵥ s + B *ᵥ u := by
  refine ⟨?_, ?_⟩
  · rw [cpDbar, Matrix.fromCols_mulVec_sumElim, Matrix.zero_mulVec, add_zero]
  · rw [cpAbar, Matrix.fromCols_mulVec_sumElim]

/-! ### The Lagrangian and the first-order conditions -/

/-- The Lagrangian of the Ramsey problem (Miao, p. 306), truncated at horizon `T`, along a
given path: `∑_{t<T} βᵗ[½x_t'Wx_t + βμ_{t+1}'(D̄x_{t+1} − Āx_t − c_{t+1})] + μ_{z0}'(z₀ − z̄₀)`,
where `c_{t+1} = [Cε_{t+1}; 0]` and `β^{t+1}μ_{t+1}` is the multiplier on (9.18) at date `t`. -/
noncomputable def cpLagrangian (W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (c μ : ℕ → Z ⊕ Y → ℝ)
    (zbar : Z → ℝ) (T : ℕ) (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, β ^ t * ((1 / 2) * (x t ⬝ᵥ (W *ᵥ x t)) +
      β * (μ (t + 1) ⬝ᵥ (Dbar *ᵥ x (t + 1) - Abar *ᵥ x t - c (t + 1)))) +
    (fun i => μ 0 (Sum.inl i)) ⬝ᵥ (fun i => x 0 (Sum.inl (Sum.inl i)) - zbar i)

/-- The path `x` with `x_s` perturbed to `x_s + εh`. -/
def cpPerturb (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) (s : ℕ) (h : (Z ⊕ Y) ⊕ U → ℝ) (ε : ℝ) :
    ℕ → (Z ⊕ Y) ⊕ U → ℝ :=
  fun t => x t + (if t = s then ε else 0) • h

/-- The vector `(μ_{z0}, 0, 0)`: the derivative of the initial term `μ_{z0}'(z₀ − z̄₀)`. -/
def cpInit (μ0 : Z ⊕ Y → ℝ) : (Z ⊕ Y) ⊕ U → ℝ :=
  Sum.elim (Sum.elim (fun i => μ0 (Sum.inl i)) 0) 0

/-- The gradient of the Lagrangian in `x_s` (divided by `βˢ`):
`g_s = Wx_s + D̄'μ_s − βĀ'μ_{s+1}`, with `D̄'μ_0` replaced by `(μ_{z0}, 0, 0)` at `s = 0`. -/
def cpGrad (W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (μ : ℕ → Z ⊕ Y → ℝ)
    (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) (s : ℕ) : (Z ⊕ Y) ⊕ U → ℝ :=
  W *ᵥ x s + (if s = 0 then cpInit (μ 0) else Dbarᵀ *ᵥ μ s) - β • (Abarᵀ *ᵥ μ (s + 1))

/-- One date-`t` term of the Lagrangian when `x_t` moves by `a h` and `x_{t+1}` by `b h`. -/
theorem cp_lagr_term {W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ} (hW : Wᵀ = W)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (c' m : Z ⊕ Y → ℝ)
    (x x' h : (Z ⊕ Y) ⊕ U → ℝ) (a b : ℝ) (t : ℕ) :
    β ^ t * ((1 / 2) * ((x + a • h) ⬝ᵥ (W *ᵥ (x + a • h))) +
      β * (m ⬝ᵥ (Dbar *ᵥ (x' + b • h) - Abar *ᵥ (x + a • h) - c'))) =
    β ^ t * ((1 / 2) * (x ⬝ᵥ (W *ᵥ x)) + β * (m ⬝ᵥ (Dbar *ᵥ x' - Abar *ᵥ x - c'))) +
      a * (β ^ t * ((W *ᵥ x) ⬝ᵥ h - β * (m ⬝ᵥ (Abar *ᵥ h)))) +
      a ^ 2 * (β ^ t * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))) +
      b * (β ^ (t + 1) * (m ⬝ᵥ (Dbar *ᵥ h))) := by
  have h1 := cp_dotProduct_mulVec_symm hW x h
  have h2 : h ⬝ᵥ (W *ᵥ x) = (W *ᵥ x) ⬝ᵥ h := dotProduct_comm _ _
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, dotProduct_sub, h1, h2]
  ring

/-- Miao, p. 306: the Lagrangian along the perturbation `x_s ↦ x_s + εh` (`s < T`, `W`
symmetric) is exactly `ℒ + εβˢ g_s·h + ε²βˢ½h'Wh`. -/
theorem cp_lagrangian_perturb {W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ} (hW : Wᵀ = W)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (c μ : ℕ → Z ⊕ Y → ℝ)
    (zbar : Z → ℝ) {T s : ℕ} (hs : s < T) (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ)
    (h : (Z ⊕ Y) ⊕ U → ℝ) (ε : ℝ) :
    cpLagrangian W Dbar Abar β c μ zbar T (cpPerturb x s h ε) =
      cpLagrangian W Dbar Abar β c μ zbar T x +
        ε * (β ^ s * (cpGrad W Dbar Abar β μ x s ⬝ᵥ h)) +
        ε ^ 2 * (β ^ s * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))) := by
  set δ : ℕ → ℝ := fun t => if t = s then ε else 0 with hδ
  have hterm := fun t => cp_lagr_term hW Dbar Abar β (c (t + 1)) (μ (t + 1)) (x t) (x (t + 1))
    h (δ t) (δ (t + 1)) t
  have hinit : (fun i => μ 0 (Sum.inl i)) ⬝ᵥ
      (fun i => cpPerturb x s h ε 0 (Sum.inl (Sum.inl i)) - zbar i) =
      (fun i => μ 0 (Sum.inl i)) ⬝ᵥ (fun i => x 0 (Sum.inl (Sum.inl i)) - zbar i) +
        δ 0 * (cpInit (μ 0) ⬝ᵥ h) := by
    simp only [cpPerturb, cpInit, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero, Finset.mul_sum, ← Finset.sum_add_distrib, δ]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hsum1 : ∑ t ∈ Finset.range T, δ t * (β ^ t * ((W *ᵥ x t) ⬝ᵥ h -
      β * (μ (t + 1) ⬝ᵥ (Abar *ᵥ h)))) =
      ε * (β ^ s * ((W *ᵥ x s) ⬝ᵥ h - β * (μ (s + 1) ⬝ᵥ (Abar *ᵥ h)))) := by
    simp only [δ, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_range, hs, ↓reduceIte]
  have hsum2 : ∑ t ∈ Finset.range T, δ t ^ 2 * (β ^ t * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))) =
      ε ^ 2 * (β ^ s * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))) := by
    simp only [δ, ite_pow, ite_mul, zero_pow two_ne_zero, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_range, hs, ↓reduceIte]
  have hsum3 : ∑ t ∈ Finset.range T, δ (t + 1) * (β ^ (t + 1) * (μ (t + 1) ⬝ᵥ (Dbar *ᵥ h))) =
      if s = 0 then 0 else ε * (β ^ s * (μ s ⬝ᵥ (Dbar *ᵥ h))) := by
    rcases Nat.eq_zero_or_eq_succ_pred s with h0 | h0
    · simp only [δ, h0, Nat.add_one_ne_zero, ↓reduceIte, zero_mul, Finset.sum_const_zero]
    · have hne : s ≠ 0 := by omega
      have hr : s - 1 < T := by omega
      have hiff : ∀ t, (t + 1 = s) ↔ (t = s - 1) := fun t => by omega
      simp only [δ, hiff, ite_mul, zero_mul, hne, ↓reduceIte]
      simp only [Finset.sum_ite_eq', Finset.mem_range, hr, ↓reduceIte,
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hne)]
  have hP : cpLagrangian W Dbar Abar β c μ zbar T (cpPerturb x s h ε) =
      ∑ t ∈ Finset.range T, β ^ t * ((1 / 2) * ((x t + δ t • h) ⬝ᵥ (W *ᵥ (x t + δ t • h))) +
        β * (μ (t + 1) ⬝ᵥ (Dbar *ᵥ (x (t + 1) + δ (t + 1) • h) - Abar *ᵥ (x t + δ t • h) -
          c (t + 1)))) +
      (fun i => μ 0 (Sum.inl i)) ⬝ᵥ
        (fun i => cpPerturb x s h ε 0 (Sum.inl (Sum.inl i)) - zbar i) := rfl
  rw [hP, hinit, Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, hsum1, hsum2, hsum3]
  simp only [cpLagrangian, cpGrad]
  have e1 : (Dbarᵀ *ᵥ μ s) ⬝ᵥ h = μ s ⬝ᵥ (Dbar *ᵥ h) := by
    rw [cp_dotProduct_mulVec_comm, dotProduct_comm]
  have e2 : (Abarᵀ *ᵥ μ (s + 1)) ⬝ᵥ h = μ (s + 1) ⬝ᵥ (Abar *ᵥ h) := by
    rw [cp_dotProduct_mulVec_comm, dotProduct_comm]
  by_cases h0 : s = 0
  · subst h0
    simp only [δ, ↓reduceIte, add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul, e2,
      pow_zero]
    ring
  · have h0' : ¬ (0 = s) := fun h => h0 h.symm
    simp only [δ, h0, h0', ↓reduceIte, add_dotProduct, sub_dotProduct, smul_dotProduct,
      smul_eq_mul, e1, e2, zero_mul, add_zero]
    ring

/-- Miao, p. 306: the derivative of the Lagrangian in the direction `h` of `x_s` (`s < T`) is
`βˢ g_s·h`. -/
theorem cp_hasDerivAt {W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ} (hW : Wᵀ = W)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (c μ : ℕ → Z ⊕ Y → ℝ)
    (zbar : Z → ℝ) {T s : ℕ} (hs : s < T) (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ)
    (h : (Z ⊕ Y) ⊕ U → ℝ) :
    HasDerivAt (fun ε => cpLagrangian W Dbar Abar β c μ zbar T (cpPerturb x s h ε))
      (β ^ s * (cpGrad W Dbar Abar β μ x s ⬝ᵥ h)) 0 := by
  have := (((hasDerivAt_id (0 : ℝ)).mul_const (β ^ s * (cpGrad W Dbar Abar β μ x s ⬝ᵥ h))).const_add
    (cpLagrangian W Dbar Abar β c μ zbar T x)).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (β ^ s * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))))
  have hf : (fun ε => cpLagrangian W Dbar Abar β c μ zbar T (cpPerturb x s h ε)) =
      (fun ε => cpLagrangian W Dbar Abar β c μ zbar T x +
        id ε * (β ^ s * (cpGrad W Dbar Abar β μ x s ⬝ᵥ h))) +
      fun ε => ε ^ 2 * (β ^ s * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))) := by
    funext ε
    rw [cp_lagrangian_perturb hW Dbar Abar β c μ zbar hs x h, Pi.add_apply, id]
  rw [hf]
  convert this using 1
  simp

/-- **First-order conditions** (Miao, p. 306). For `β ≠ 0`, symmetric `W` and `s < T`, the
Lagrangian is stationary in `x_s` (zero derivative in every direction) iff
`Wx_s + D̄'μ_s − βĀ'μ_{s+1} = 0` (with `(μ_{z0}, 0, 0)` for `D̄'μ_0` at `s = 0`). -/
theorem eq_foc_9_4 {W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ} (hW : Wᵀ = W)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) {β : ℝ} (hβ : β ≠ 0) (c μ : ℕ → Z ⊕ Y → ℝ)
    (zbar : Z → ℝ) {T s : ℕ} (hs : s < T) (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) :
    (∀ h, HasDerivAt (fun ε => cpLagrangian W Dbar Abar β c μ zbar T (cpPerturb x s h ε)) 0 0) ↔
      cpGrad W Dbar Abar β μ x s = 0 := by
  constructor
  · intro H
    have h1 := (cp_hasDerivAt hW Dbar Abar β c μ zbar hs x (cpGrad W Dbar Abar β μ x s)).unique
      (H _)
    have h2 : cpGrad W Dbar Abar β μ x s ⬝ᵥ cpGrad W Dbar Abar β μ x s = 0 := by
      rcases mul_eq_zero.1 h1 with h3 | h3
      · exact absurd h3 (pow_ne_zero _ hβ)
      · exact h3
    exact dotProduct_self_eq_zero.1 h2
  · intro H h
    have := cp_hasDerivAt hW Dbar Abar β c μ zbar hs x h
    rwa [H, zero_dotProduct, mul_zero] at this

omit [Fintype U] in
/-- Miao, p. 307: if `D = [I 0; D₂₁ D₂₂]` and `μ_{y0} = 0` ("no past promises"), then
`(μ_{z0}, 0, 0) = D̄'μ₀`. -/
theorem cp_init_eq_Dbar [DecidableEq Z] (D21 : Matrix Y Z ℝ) (D22 : Matrix Y Y ℝ)
    (μ0 : Z ⊕ Y → ℝ) (hμ : ∀ i, μ0 (Sum.inr i) = 0) :
    cpInit (U := U) μ0 = (cpDbar U (Matrix.fromBlocks 1 0 D21 D22))ᵀ *ᵥ μ0 := by
  have hμ' : μ0 = Sum.elim (fun i => μ0 (Sum.inl i)) 0 := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact hμ i
  rw [cpDbar, Matrix.transpose_fromCols, Matrix.fromRows_mulVec, Matrix.fromBlocks_transpose]
  conv_rhs => rw [hμ']
  rw [Matrix.fromBlocks_mulVec]
  simp only [cpInit, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.transpose_one,
    Matrix.one_mulVec, Matrix.mulVec_zero, add_zero, Matrix.transpose_zero, Matrix.zero_mulVec]

/-- **First-order conditions with respect to `z_t, y_t, u_t`** (Miao, p. 306). With
`D = [I 0; D₂₁ D₂₂]` and `μ_{y0} = 0`, the gradient is `Wx_s + D̄'μ_s − βĀ'μ_{s+1}` at every
date `s ≥ 0`, including `s = 0`. -/
theorem cp_grad_eq [DecidableEq Z] (W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ)
    (D21 : Matrix Y Z ℝ) (D22 : Matrix Y Y ℝ) (Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ)
    (μ : ℕ → Z ⊕ Y → ℝ) (hμ : ∀ i, μ 0 (Sum.inr i) = 0) (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) (s : ℕ) :
    cpGrad W (cpDbar U (Matrix.fromBlocks 1 0 D21 D22)) Abar β μ x s =
      W *ᵥ x s + (cpDbar U (Matrix.fromBlocks 1 0 D21 D22))ᵀ *ᵥ μ s - β • (Abarᵀ *ᵥ μ (s + 1)) := by
  rw [cpGrad]
  by_cases h0 : s = 0
  · subst h0
    simp only [↓reduceIte, cp_init_eq_Dbar D21 D22 (μ 0) hμ]
  · simp only [h0, ↓reduceIte]

/-! ### The stacked system (9.22) -/

/-- The left matrix of (9.22): `[D̄ 0; 0 βĀ']`. -/
def cpLeft (β : ℝ) (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) :
    Matrix ((Z ⊕ Y) ⊕ ((Z ⊕ Y) ⊕ U)) (((Z ⊕ Y) ⊕ U) ⊕ (Z ⊕ Y)) ℝ :=
  Matrix.fromBlocks Dbar 0 0 (β • Abarᵀ)

/-- The right matrix of (9.22): `[Ā 0; W D̄']`. -/
def cpRight (W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) :
    Matrix ((Z ⊕ Y) ⊕ ((Z ⊕ Y) ⊕ U)) (((Z ⊕ Y) ⊕ U) ⊕ (Z ⊕ Y)) ℝ :=
  Matrix.fromBlocks Abar 0 W Dbarᵀ

/-- Miao, (9.22), p. 307: the constraints `D̄x_{t+1} = Āx_t + c_{t+1}` together with the
first-order conditions `Wx_t + D̄'μ_t − βĀ'μ_{t+1} = 0` are the stacked system
`[D̄ 0; 0 βĀ'][x_{t+1}; μ_{t+1}] = [Ā 0; W D̄'][x_t; μ_t] + [c_{t+1}; 0]`. -/
theorem eq_9_22 (W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (c μ : ℕ → Z ⊕ Y → ℝ)
    (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) :
    ((∀ t, Dbar *ᵥ x (t + 1) = Abar *ᵥ x t + c (t + 1)) ∧
      ∀ t, W *ᵥ x t + Dbarᵀ *ᵥ μ t - β • (Abarᵀ *ᵥ μ (t + 1)) = 0) ↔
    ∀ t, cpLeft β Dbar Abar *ᵥ Sum.elim (x (t + 1)) (μ (t + 1)) =
      cpRight W Dbar Abar *ᵥ Sum.elim (x t) (μ t) + Sum.elim (c (t + 1)) 0 := by
  simp only [cpLeft, cpRight, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, add_zero, zero_add, Matrix.smul_mulVec, ← Sum.elim_add_add,
    Sum.elim_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩ t
    exact ⟨h1 t, (sub_eq_zero.1 (h2 t)).symm⟩
  · intro h
    exact ⟨fun t => (h t).1, fun t => sub_eq_zero.2 (h t).2.symm⟩

end Miao.NewKeynesian

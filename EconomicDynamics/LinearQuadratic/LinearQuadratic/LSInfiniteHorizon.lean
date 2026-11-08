/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.LSRiccatiConvergence

/-!
# Infinite-horizon limits: Propositions 9.3.1 and 9.3.2

Miao, §9.3, pp. 298–304. For an `LSProblem` with `S = 0` the Riccati operator (9.11) of the
discounted problem is the undiscounted Riccati map of `(√βA, √βB)` (`toSS`, `toSS_riccati`,
`toSS_gain`): discounting is removed by the transformation `x̂_t = β^{t/2}x_t`,
`û_t = β^{t/2}u_t` (`ls_discount_rescale`). The results of `LSRiccatiConvergence` then give:

* (9.11) for the stationary finite-horizon problem: `P(s) = T(P(s − 1)) = Tˢ(P(0))`,
  `F(s) = F(P(s − 1))`, and the constants `d(s)` (`eq_9_11`, `toFin_dbk`).
* The proof of Proposition 9.3.1: `P(1) = Q` (`ls_P_one`), `P(s) ≤ P(s + 1)` (`ls_P_mono`; the
  book's strict `P(s + 1) > P(s)` is false, `ls_P_mono_not_strict`).
* **Proposition 9.3.1** (`proposition_9_3_1`): `Q > 0`, `R > 0`, `(√βA, √βB)` controllable or
  stabilizable ⇒ `P = T(P)` (9.12) has a unique positive semidefinite solution, and
  `P(s) → P` from every positive semidefinite `P(0)`.
* **Proposition 9.3.2** (`proposition_9_3_2`): the same with `Q = L'L`, `(√βA, L)` observable or
  detectable.
* `ls_discounted_main`: the full conclusion, also giving that `√β(A − BF)` is stable,
  (9.13) `P = Q + F'RF + βΓ'PΓ` and the series `P = ∑ (√βΓ')ʲ(Q + F'RF)(√βΓ)ʲ`
  (`eq_9_13`, `eq_9_13_series`); (9.14) (`eq_9_14`); the upper bound
  `P(s) ≤ ∑_{j<s} βʲΓ'ʲ(Q + F'RF)Γʲ + βˢΓ'ˢP(0)Γˢ` (`ls_P_le_policy`; the book omits `βˢ`).
* The value function and the optimal policy of the infinite-horizon deterministic problem
  (`ls_infinite_value`), and, in the general case with `S ≠ 0` and noise,
  `V(x) = −x'Px − d`, `d = (1 − β)⁻¹β tr(PCC')`, `u = −Fx` (9.16)–(9.17) (`eq_9_16_9_17`).
* The limits `F(s) → F` and `d(s) → d` (`ls_F_tendsto`, `ls_dIter_tendsto`).
* The side condition (9.10) (`eq_9_10_growth`, `ls_stable_of_side_condition`).
* Policy improvement: the rewritten Riccati equation and solvability of its Lyapunov step
  (`ls_policy_riccati`, `ls_policy_lyapunov`).
* The Lagrange method: the multiplier `λ_t = Px_t` satisfies the first-order conditions and the
  constraint (`ls_lagrange`), and `V(x + h) = V(x) − 2λ·h − h'Ph` (`ls_envelope`).
* Controllability implies stabilizability (`controllable_stabilizable`, Miao p. 293).
-/

open Filter Topology Matrix MeasureTheory

open scoped MatrixOrder

namespace Miao.LinearQuadratic

namespace LSProblem

variable {X U E : Type*} [Fintype X] [Fintype U] [DecidableEq U] (L : LSProblem X U E)

/-- The undiscounted Sargent–Stachurski problem `(Q, R, √βA, √βB)` of an `LSProblem`. -/
noncomputable def toSS (hQ : L.Q.PosSemidef) (hR : L.R.PosDef) : SS.LQProblem X U :=
  ⟨Real.sqrt L.β • L.A, Real.sqrt L.β • L.B, L.Q, L.R, hQ, hR⟩

omit [DecidableEq U] in
theorem toSS_gainDen (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    (P : Matrix X X ℝ) : (L.toSS hQ hR).gainDen P = L.G P := by
  simp only [SS.LQProblem.gainDen, toSS, G, transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Real.mul_self_sqrt hβ]
  abel

/-- With `S = 0`, the Riccati operator (9.11) is the Riccati map of `(Q, R, √βA, √βB)`. -/
theorem toSS_riccati (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    (P : Matrix X X ℝ) : (L.toSS hQ hR).riccati P = L.T P := by
  have hb := Real.mul_self_sqrt hβ
  rw [SS.LQProblem.riccati, toSS_gainDen L hβ]
  simp only [toSS, T, N, hS, transpose_zero, zero_add, transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [show Real.sqrt L.β * (Real.sqrt L.β * (Real.sqrt L.β * Real.sqrt L.β)) = L.β * L.β by
    rw [hb, ← mul_assoc, hb], hb]
  abel

/-- With `S = 0`, the gain (9.17) is minus the Sargent–Stachurski gain of `(√βA, √βB)`. -/
theorem toSS_gain (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    (P : Matrix X X ℝ) : (L.toSS hQ hR).gain P = -L.F P := by
  have hb := Real.mul_self_sqrt hβ
  rw [SS.LQProblem.gain, toSS_gainDen L hβ]
  simp only [toSS, F, N, hS, transpose_zero, zero_add, transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hb]

omit [DecidableEq U] in
theorem toSS_closedLoop (hQ : L.Q.PosSemidef) (hR : L.R.PosDef) (F : Matrix U X ℝ) :
    (L.toSS hQ hR).closedLoop (-F) = Real.sqrt L.β • (L.A - L.B * F) := by
  simp only [SS.LQProblem.closedLoop, toSS, Matrix.smul_mul, Matrix.mul_neg, smul_sub]
  abel

omit [DecidableEq U] in
theorem toSS_costMat (hQ : L.Q.PosSemidef) (hR : L.R.PosDef) (F : Matrix U X ℝ) :
    (L.toSS hQ hR).costMat (-F) = L.Q + Fᵀ * L.R * F := by
  simp only [SS.LQProblem.costMat, toSS, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  abel

theorem toSS_riccati_iter (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef)
    (hR : L.R.PosDef) (s : ℕ) : (L.toSS hQ hR).riccati^[s] = L.T^[s] := by
  have : (L.toSS hQ hR).riccati = L.T := funext (L.toSS_riccati hS hβ hQ hR)
  rw [this]

omit [DecidableEq U] in
/-- The loss with `S = 0`. -/
theorem loss_S_zero (hS : L.S = 0) (x : X → ℝ) (u : U → ℝ) :
    L.loss x u = x ⬝ᵥ (L.Q *ᵥ x) + u ⬝ᵥ (L.R *ᵥ u) := by
  simp [loss, hS]

omit [DecidableEq U] in
/-- Removing the discount (Miao, pp. 299–301): with `x̂_t = β^{t/2}x_t`, `û_t = β^{t/2}u_t`,
the transition `x_{t+1} = Ax_t + Bu_t` becomes `x̂_{t+1} = √βAx̂_t + √βBû_t` and
`βᵗr(x_t, u_t) = r(x̂_t, û_t)`. -/
theorem ls_discount_rescale (hβ : 0 ≤ L.β) {x : ℕ → X → ℝ} {u : ℕ → U → ℝ}
    (hx : ∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ u t) (t : ℕ) :
    Real.sqrt L.β ^ (t + 1) • x (t + 1) =
        (Real.sqrt L.β • L.A) *ᵥ (Real.sqrt L.β ^ t • x t) +
          (Real.sqrt L.β • L.B) *ᵥ (Real.sqrt L.β ^ t • u t) ∧
      L.β ^ t * L.loss (x t) (u t) =
        L.loss (Real.sqrt L.β ^ t • x t) (Real.sqrt L.β ^ t • u t) := by
  have hb : Real.sqrt L.β ^ t * Real.sqrt L.β ^ t = L.β ^ t := by
    rw [← mul_pow, Real.mul_self_sqrt hβ]
  refine ⟨?_, ?_⟩
  · rw [hx, smul_add, smul_mulVec, smul_mulVec, mulVec_smul, mulVec_smul, smul_smul, smul_smul,
      pow_succ']
  · simp only [loss, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [← hb]
    ring

/-! ### The stationary finite-horizon problem and (9.11) -/

/-- The stationary finite-horizon problem with horizon `T` and terminal matrix `P(0)`. -/
def toFin (hor : ℕ) (PT : Matrix X X ℝ) : LSFinProblem X U E :=
  ⟨fun _ => L.A, fun _ => L.B, fun _ => L.C, fun _ => L.Q, fun _ => L.R, fun _ => L.S, L.β,
    hor, PT⟩

omit [Fintype X] [Fintype U] [DecidableEq U] in
theorem toFin_stage (hor : ℕ) (PT : Matrix X X ℝ) (t : ℕ) : (L.toFin hor PT).stage t = L := rfl

theorem toFin_Pbk (hor : ℕ) (PT : Matrix X X ℝ) (s : ℕ) :
    (L.toFin hor PT).Pbk s = L.T^[s] PT := by
  induction s with
  | zero => rfl
  | succ s ih => rw [LSFinProblem.Pbk, ih, toFin_stage, Function.iterate_succ_apply']

/-- The constants `d(s)` of the stationary finite-horizon problem:
`d(s + 1) = β tr(P(s)CC') + βd(s)`, `d(0) = 0`. -/
noncomputable def dIter [Fintype E] (P₀ : Matrix X X ℝ) : ℕ → ℝ
  | 0 => 0
  | s + 1 => L.β * trace (L.T^[s] P₀ * L.C * L.Cᵀ) + L.β * dIter P₀ s

theorem toFin_dbk [Fintype E] (hor : ℕ) (PT : Matrix X X ℝ) (s : ℕ) :
    (L.toFin hor PT).dbk s = L.dIter PT s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [LSFinProblem.dbk, ih, toFin_Pbk, dIter]
    rfl

/-- (9.11) (Miao, p. 298): for the stationary problem, with `s = T − t` periods remaining,
`P(s) = T(P(s − 1)) = Tˢ(P(0))` and `F(s) = (R + βB'P(s − 1)B)⁻¹(S' + βB'P(s − 1)A)`. -/
theorem eq_9_11 (hor : ℕ) (PT : Matrix X X ℝ) {s : ℕ} (hs : s ≤ hor) :
    (L.toFin hor PT).P (hor - s) = L.T^[s] PT ∧
      (0 < s → (L.toFin hor PT).Fg (hor - s) = L.F (L.T^[s - 1] PT)) := by
  refine ⟨?_, fun hs0 => ?_⟩
  · rw [LSFinProblem.P, show (L.toFin hor PT).hor - (hor - s) = s from by
      change hor - (hor - s) = s; omega, toFin_Pbk]
  · rw [LSFinProblem.Fg, toFin_stage, LSFinProblem.P,
      show (L.toFin hor PT).hor - (hor - s + 1) = s - 1 from by
        change hor - (hor - s + 1) = s - 1; omega, toFin_Pbk]

theorem T_zero_S (hS : L.S = 0) : L.T 0 = L.Q := by
  simp [T, hS, N]

/-- Miao, p. 299: `P(0) = 0` gives `P(1) = Q`, so `V₁(x) = −x'Qx < 0 = V₀(x)` for `x ≠ 0` when
`Q > 0`. -/
theorem ls_P_one (hS : L.S = 0) (hQ : L.Q.PosDef) :
    L.T^[1] 0 = L.Q ∧ ∀ x : X → ℝ, x ≠ 0 → -(x ⬝ᵥ (L.T^[1] 0 *ᵥ x)) < -(x ⬝ᵥ (0 *ᵥ x)) := by
  have h1 : L.T^[1] 0 = L.Q := by simp [T_zero_S L hS]
  refine ⟨h1, fun x hx => ?_⟩
  rw [h1, zero_mulVec, dotProduct_zero, neg_zero, neg_lt_zero]
  exact (SS.LQProblem.posDef_iff_real.1 hQ).2 hx

/-- Miao, p. 299 (corrected): `P(s) ≤ P(s + 1)` for `P(0) = 0`. -/
theorem ls_P_mono (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    (s : ℕ) : L.T^[s] 0 ≤ L.T^[s + 1] 0 := by
  rw [← toSS_riccati_iter L hS hβ hQ hR, ← toSS_riccati_iter L hS hβ hQ hR]
  exact ls_iter_zero_mono _ s

/-- Miao, p. 299, "`P(s + 1) > P(s)` for any `s`" is false: with `A = 0` (scalar, `Q = R = 1`,
`B = 1`, `β = 1`), `T(P) = Q` for every `P`, so `P(2) = P(1)`. -/
theorem ls_P_mono_not_strict :
    let L0 : LSProblem (Fin 1) (Fin 1) (Fin 1) := ⟨0, 1, 0, 1, 1, 0, 1⟩
    L0.T^[2] 0 = L0.T^[1] 0 := by
  intro L0
  have hT : ∀ P, L0.T P = 1 := fun P => by simp [L0, T, N]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, hT]

/-! ### Propositions 9.3.1 and 9.3.2 -/

/-- The common conclusion of Propositions 9.3.1–9.3.2 (Miao, pp. 299–301), for `S = 0` and
`β ≥ 0`: if `(√βA, √βB)` is controllable or stabilizable and the detection condition holds,
the Riccati equation (9.12) has a positive semidefinite solution `P`, unique among positive
semidefinite matrices, `P(s) = Tˢ(P(0)) → P` for every positive semidefinite `P(0)`,
`√β(A − BF)` is stable for `F = F(P)`, and `P = ∑ (√βΓ')ʲ(Q + F'RF)(√βΓ)ʲ`. -/
theorem ls_discounted_main [Nonempty X] [DecidableEq X] (hS : L.S = 0) (hβ : 0 ≤ L.β)
    (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    (hstab : ls_Controllable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) ∨
      ls_Stabilizable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B))
    (hD : ∀ F, ls_Detects (L.toSS hQ hR) F) :
    ∃ P : Matrix X X ℝ, P.PosSemidef ∧ L.T P = P ∧
      (∀ P' : Matrix X X ℝ, P'.PosSemidef → L.T P' = P' → P' = P) ∧
      (∀ P₀ : Matrix X X ℝ, P₀.PosSemidef → Tendsto (fun s => L.T^[s] P₀) atTop (𝓝 P)) ∧
      ls_Stable (Real.sqrt L.β • (L.A - L.B * L.F P)) ∧
      P = (L.toSS hQ hR).PF (-L.F P) := by
  have hstab' : (∃ F, (L.toSS hQ hR).IsStable F) ∨
      ls_Controllable (L.toSS hQ hR).A (L.toSS hQ hR).B := by
    rcases hstab with hc | ⟨H, hH⟩
    · exact Or.inr hc
    · exact Or.inl ⟨H, ls_specRad_lt_of_stable hH⟩
  obtain ⟨P, hP, hfix, hst, hPF, hconv, huniq⟩ := ls_riccati_main (L.toSS hQ hR) hstab' hD
  rw [L.toSS_riccati hS hβ] at hfix
  rw [L.toSS_gain hS hβ] at hst hPF
  refine ⟨P, hP, hfix, fun P' hP' h' => huniq P' hP' (by rw [L.toSS_riccati hS hβ]; exact h'),
    fun P₀ hP₀ => ?_, ?_, hPF⟩
  · simpa only [L.toSS_riccati_iter hS hβ hQ hR] using hconv P₀ hP₀
  · have := ls_stable_of_specRad hst
    rwa [toSS_closedLoop] at this

/-- **Proposition 9.3.1** (Miao, p. 299). Suppose `S = 0`, (i) `Q > 0`, (ii) `R > 0`, (iii)
`(√βA, √βB)` is controllable or stabilizable (and `β ≥ 0`; the book has `β ∈ (0, 1]`). Then
(i) the Riccati equation `P = T(P)` (9.12) has a unique positive semidefinite solution `P`;
(ii) `P(s) = Tˢ(P(0)) → P` for every positive semidefinite `P(0)`. -/
theorem proposition_9_3_1 [Nonempty X] [DecidableEq X] (hS : L.S = 0) (hQ : L.Q.PosDef)
    (hR : L.R.PosDef) (hβ : 0 ≤ L.β)
    (hstab : ls_Controllable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) ∨
      ls_Stabilizable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B)) :
    ∃ P : Matrix X X ℝ, (P.PosSemidef ∧ L.T P = P) ∧
      (∀ P' : Matrix X X ℝ, P'.PosSemidef → L.T P' = P' → P' = P) ∧
      ∀ P₀ : Matrix X X ℝ, P₀.PosSemidef → Tendsto (fun s => L.T^[s] P₀) atTop (𝓝 P) := by
  obtain ⟨P, hP, hfix, huniq, hconv, -⟩ := L.ls_discounted_main hS hβ hQ.posSemidef hR hstab
    fun F => ls_detects_of_posDef (L.toSS hQ.posSemidef hR) hQ F
  exact ⟨P, ⟨hP, hfix⟩, huniq, hconv⟩

/-- **Proposition 9.3.2** (Miao, p. 301): Proposition 9.3.1 holds with (i) weakened to
`Q = L'L` with `(√βA, L)` observable or detectable. -/
theorem proposition_9_3_2 [Nonempty X] [DecidableEq X] {Y : Type*} [Fintype Y] (hS : L.S = 0)
    {Lm : Matrix Y X ℝ} (hQL : L.Q = Lmᵀ * Lm)
    (hobs : ls_Observable (Real.sqrt L.β • L.A) Lm ∨ ls_Detectable (Real.sqrt L.β • L.A) Lm)
    (hR : L.R.PosDef) (hβ : 0 ≤ L.β)
    (hstab : ls_Controllable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) ∨
      ls_Stabilizable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B)) :
    ∃ P : Matrix X X ℝ, (P.PosSemidef ∧ L.T P = P) ∧
      (∀ P' : Matrix X X ℝ, P'.PosSemidef → L.T P' = P' → P' = P) ∧
      ∀ P₀ : Matrix X X ℝ, P₀.PosSemidef → Tendsto (fun s => L.T^[s] P₀) atTop (𝓝 P) := by
  have hQ : L.Q.PosSemidef := by
    rw [hQL]
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self Lm
  have hD : ∀ F, ls_Detects (L.toSS hQ hR) F := by
    rcases hobs with ho | hd
    · exact fun F => ls_detects_of_observable (L.toSS hQ hR) hQL ho F
    · exact fun F => ls_detects_of_detectable (L.toSS hQ hR) hQL hd F
  obtain ⟨P, hP, hfix, huniq, hconv, -⟩ := L.ls_discounted_main hS hβ hQ hR hstab hD
  exact ⟨P, ⟨hP, hfix⟩, huniq, hconv⟩

/-- (9.13) (Miao, p. 300): with `S = 0`, a fixed point `P = T(P)` satisfies
`P = Q + F'RF + βΓ'PΓ`, `F = (R + βB'PB)⁻¹βB'PA`, `Γ = A − BF`. -/
theorem eq_9_13 (hS : L.S = 0) {P : Matrix X X ℝ} (hG : IsUnit (L.G P).det) (hfix : L.T P = P) :
    P = L.Q + (L.F P)ᵀ * L.R * L.F P +
      L.β • ((L.A - L.B * L.F P)ᵀ * P * (L.A - L.B * L.F P)) := by
  conv_lhs => rw [← hfix, ← L.TF_F hG]
  simp [TF, hS]

omit [Fintype U] [DecidableEq U] in
/-- `((√βM)ʲ)'W(√βM)ʲ = βʲ(Mʲ)'WMʲ`. -/
theorem ls_sqrt_sandwich [DecidableEq X] {β : ℝ} (hβ : 0 ≤ β) (M W : Matrix X X ℝ) (j : ℕ) :
    ((Real.sqrt β • M) ^ j)ᵀ * W * (Real.sqrt β • M) ^ j = β ^ j • ((M ^ j)ᵀ * W * M ^ j) := by
  simp only [smul_pow, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← mul_pow, Real.mul_self_sqrt hβ]

/-- The series form of (9.13) (Miao, p. 300): if `√βΓ` is stable,
`P = ∑ⱼ (√βΓ')ʲ(Q + F'RF)(√βΓ)ʲ = ∑ⱼ βʲΓ'ʲ(Q + F'RF)Γʲ` (entrywise). -/
theorem eq_9_13_series [Nonempty X] [DecidableEq X] (hS : L.S = 0) (hβ : 0 ≤ L.β)
    (hQ : L.Q.PosSemidef) (hR : L.R.PosDef) {P : Matrix X X ℝ} (hP : P.PosSemidef)
    (hfix : L.T P = P) (hst : ls_Stable (Real.sqrt L.β • (L.A - L.B * L.F P))) (a b : X) :
    HasSum (fun j => ((L.β ^ j • (((L.A - L.B * L.F P) ^ j)ᵀ *
      (L.Q + (L.F P)ᵀ * L.R * L.F P) * (L.A - L.B * L.F P) ^ j) : Matrix X X ℝ) a b))
      (P a b) := by
  have hst' : (L.toSS hQ hR).IsStable (-L.F P) := by
    rw [SS.LQProblem.IsStable, toSS_closedLoop]
    exact ls_specRad_lt_of_stable hst
  have hTF : (L.toSS hQ hR).TF (-L.F P) P = P := by
    rw [← L.toSS_gain hS hβ hQ hR, ← SS.LQProblem.riccati_eq_TF _ hP, L.toSS_riccati hS hβ, hfix]
  have hPF := hst'.eq_PF hTF
  have h := hst'.hasSum_PF a b
  rw [← hPF] at h
  refine h.congr_fun fun j => ?_
  simp only [SS.LQProblem.discCost, toSS_closedLoop, toSS_costMat, ls_sqrt_sandwich hβ]

/-- (9.14) (Miao, p. 300): at a fixed point, along `x_{t+1} = √βΓx_t`, `V(x) = −x'Px` increases,
`V(x_{t+1}) − V(x_t) = x_t'(Q + F'RF)x_t ≥ 0`, and `x_t'(Q + F'RF)x_t → 0`. -/
theorem eq_9_14 (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    {P : Matrix X X ℝ} (hP : P.PosSemidef) (hfix : L.T P = P) {x : ℕ → X → ℝ}
    (hx : ∀ t, x (t + 1) = (Real.sqrt L.β • (L.A - L.B * L.F P)) *ᵥ x t) :
    (∀ t, -(x (t + 1) ⬝ᵥ (P *ᵥ x (t + 1))) - -(x t ⬝ᵥ (P *ᵥ x t)) =
      x t ⬝ᵥ ((L.Q + (L.F P)ᵀ * L.R * L.F P) *ᵥ x t)) ∧
    Tendsto (fun t => x t ⬝ᵥ ((L.Q + (L.F P)ᵀ * L.R * L.F P) *ᵥ x t)) atTop (𝓝 0) := by
  have hfix' : (L.toSS hQ hR).riccati P = P := by rw [L.toSS_riccati hS hβ, hfix]
  have hx' : ∀ t, x (t + 1) = (L.toSS hQ hR).closedLoop ((L.toSS hQ hR).gain P) *ᵥ x t := by
    intro t
    rw [L.toSS_gain hS hβ, toSS_closedLoop, hx]
  obtain ⟨hsum, hQt, hFt⟩ := ls_cost_tendsto_zero (L.toSS hQ hR) hP hfix' hx'
  have hcm : (L.toSS hQ hR).costMat ((L.toSS hQ hR).gain P) = L.Q + (L.F P)ᵀ * L.R * L.F P := by
    rw [L.toSS_gain hS hβ, toSS_costMat]
  refine ⟨fun t => ?_, ?_⟩
  · have h1 := hsum (t + 1)
    have h2 := hsum t
    rw [Finset.sum_range_succ, hcm] at h1
    rw [hcm] at h2
    linarith
  · have hFt' : Tendsto (fun t => (L.F P *ᵥ x t) ⬝ᵥ (L.R *ᵥ (L.F P *ᵥ x t))) atTop (𝓝 0) := by
      rw [L.toSS_gain hS hβ] at hFt
      have h := hFt.neg
      simp only [neg_zero] at h
      have hc : Continuous fun v : U → ℝ => v ⬝ᵥ (L.R *ᵥ v) :=
        Continuous.dotProduct continuous_id
          (Continuous.matrix_mulVec continuous_const continuous_id)
      have := (hc.tendsto 0).comp h
      simpa [Function.comp_def, neg_mulVec] using this
    have := hQt.add hFt'
    rw [add_zero] at this
    refine this.congr fun t => ?_
    rw [add_mulVec, dotProduct_add, SS.LQProblem.dotProduct_transpose_mul_mul]
    rfl

/-- The upper bound of p. 300, corrected: for any `F`, with `Γ = A − BF`,
`P(s) = Tˢ(P(0)) ≤ ∑_{j<s} βʲΓ'ʲ(Q + F'RF)Γʲ + βˢΓ'ˢP(0)Γˢ` (the book omits `βˢ`). -/
theorem ls_P_le_policy [DecidableEq X] (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef)
    (hR : L.R.PosDef) {P₀ : Matrix X X ℝ} (hP₀ : P₀.PosSemidef) (F : Matrix U X ℝ) (s : ℕ) :
    L.T^[s] P₀ ≤ ∑ j ∈ Finset.range s, L.β ^ j • (((L.A - L.B * F) ^ j)ᵀ *
      (L.Q + Fᵀ * L.R * F) * (L.A - L.B * F) ^ j) +
      L.β ^ s • (((L.A - L.B * F) ^ s)ᵀ * P₀ * (L.A - L.B * F) ^ s) := by
  set L' := L.toSS hQ hR
  have hup : ∀ s, L'.riccati^[s] P₀ ≤ (L'.TF (-F))^[s] P₀ := by
    intro s
    induction s with
    | zero => exact le_rfl
    | succ s ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (ls_riccati_le_TF L' (ls_iter_psd L' hP₀ s) (-F)).trans (L'.TF_mono (-F) ih)
  have h := hup s
  rw [L.toSS_riccati_iter hS hβ hQ hR, SS.LQProblem.TF_iterate] at h
  simpa only [SS.LQProblem.discCost, L', toSS_closedLoop, toSS_costMat, ls_sqrt_sandwich hβ]
    using h

/-- The printed bound of p. 300 does not tend to `P`: with `A = 1`, `B = 0`, `Q = R = 1`,
`β = 1/4` (so `(√βA, √βB)` is stabilizable and Proposition 9.3.1 applies), `Γ = A − BF = 1` for
every `F`, so the printed remainder `Γ'ˢP(0)Γˢ = P(0)` does not vanish. -/
theorem ls_P_le_policy_misprint (F : Matrix (Fin 1) (Fin 1) ℝ) (P₀ : Matrix (Fin 1) (Fin 1) ℝ)
    (s : ℕ) :
    let L0 : LSProblem (Fin 1) (Fin 1) (Fin 1) := ⟨1, 0, 0, 1, 1, 0, 1 / 4⟩
    ((L0.A - L0.B * F) ^ s)ᵀ * P₀ * (L0.A - L0.B * F) ^ s = P₀ := by
  intro L0
  simp [L0]

/-! ### The value function and the optimal policy -/

/-- The infinite-horizon value function and optimal policy (Miao, pp. 299–301), deterministic
case with `S = 0`, `β > 0`: if `P = T(P)` is the limit of `Tˢ(0)` and `√β(A − BF)` is stable
(`F = F(P)`), then (a) every control sequence costs at least `x₀'Tˢ(0)x₀` over `s` periods, and
at least `x₀'Px₀` in total; (b) the stationary rule `u_t = −Fx_t` costs exactly `x₀'Px₀`. So
`V(x) = −x'Px` and `u = −Fx` is optimal. -/
theorem ls_infinite_value [Nonempty X] [DecidableEq X] (hS : L.S = 0) (hβ : 0 < L.β)
    (hQ : L.Q.PosSemidef) (hR : L.R.PosDef) {P : Matrix X X ℝ} (hP : P.PosSemidef)
    (hfix : L.T P = P) (hlim : Tendsto (fun s => L.T^[s] 0) atTop (𝓝 P))
    (hst : ls_Stable (Real.sqrt L.β • (L.A - L.B * L.F P))) (x₀ : X → ℝ) :
    (∀ (x : ℕ → X → ℝ) (u : ℕ → U → ℝ), x 0 = x₀ →
      (∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ u t) →
      (∀ s, x₀ ⬝ᵥ (L.T^[s] 0 *ᵥ x₀) ≤
        ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t)) ∧
      (Summable (fun t => L.β ^ t * L.loss (x t) (u t)) →
        x₀ ⬝ᵥ (P *ᵥ x₀) ≤ ∑' t, L.β ^ t * L.loss (x t) (u t))) ∧
    ∀ x : ℕ → X → ℝ, x 0 = x₀ → (∀ t, x (t + 1) = (L.A - L.B * L.F P) *ᵥ x t) →
      HasSum (fun t => L.β ^ t * L.loss (x t) (-(L.F P *ᵥ x t))) (x₀ ⬝ᵥ (P *ᵥ x₀)) := by
  set sb := Real.sqrt L.β
  refine ⟨fun x u hx0 hx => ?_, fun x hx0 hx => ?_⟩
  · have hfin : ∀ s, x₀ ⬝ᵥ (L.T^[s] 0 *ᵥ x₀) ≤
        ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t) := by
      intro s
      have h := ls_finite_lower (L.toSS hQ hR) PosSemidef.zero s (fun t => sb ^ t • x t)
        (fun t => sb ^ t • u t) fun t => (L.ls_discount_rescale hβ.le hx t).1
      rw [L.toSS_riccati_iter hS hβ.le hQ hR] at h
      simp only [pow_zero, one_smul, hx0, zero_mulVec, dotProduct_zero, add_zero] at h
      refine h.trans (le_of_eq (Finset.sum_congr rfl fun t _ => ?_))
      rw [(L.ls_discount_rescale hβ.le hx t).2, L.loss_S_zero hS]
      rfl
    refine ⟨hfin, fun hs => ?_⟩
    exact le_of_tendsto_of_tendsto' (ls_tendsto_quad hlim x₀) hs.hasSum.tendsto_sum_nat hfin
  · have hst' : (L.toSS hQ hR).IsStable (-L.F P) := by
      rw [SS.LQProblem.IsStable, toSS_closedLoop]
      exact ls_specRad_lt_of_stable hst
    have hTF : (L.toSS hQ hR).TF (-L.F P) P = P := by
      rw [← L.toSS_gain hS hβ.le hQ hR, ← SS.LQProblem.riccati_eq_TF _ hP,
        L.toSS_riccati hS hβ.le, hfix]
    have hPF := hst'.eq_PF hTF
    have h := hst'.hasSum_cost x₀
    rw [← hPF] at h
    have hxt : ∀ t, x t = ((L.A - L.B * L.F P) ^ t) *ᵥ x₀ := by
      intro t
      induction t with
      | zero => simp [hx0]
      | succ t ih => rw [hx, ih, mulVec_mulVec, pow_succ']
    have hu : ∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ (-(L.F P *ᵥ x t)) := fun t => by
      rw [hx, sub_mulVec, mulVec_neg, ← mulVec_mulVec, sub_eq_add_neg]
    refine h.congr_fun fun t => ?_
    rw [(L.ls_discount_rescale hβ.le hu t).2, L.loss_S_zero hS, toSS_closedLoop, toSS_costMat,
      smul_pow, smul_mulVec, ← hxt t, add_mulVec, dotProduct_add,
      SS.LQProblem.dotProduct_transpose_mul_mul]
    simp only [mulVec_smul, smul_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

variable [Fintype E] [DecidableEq E]

/-- (9.16)–(9.17) (Miao, pp. 301–302), the general case with `S ≠ 0` and uncertainty: if
`P ≥ 0` solves (9.12) and `0 ≤ β < 1`, then `V(x) = −x'Px − d` with
`d = (1 − β)⁻¹β tr(PCC')` satisfies the Bellman equation
`V(x) = max_u {−r(x, u) + βE V(Ax + Bu + Cε)}`, and the maximum is attained exactly at
`u = −Fx` with `F = (R + βB'PB)⁻¹(S' + βB'PA)`. -/
theorem eq_9_16_9_17 {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (hR : L.R.PosDef)
    (hβ0 : 0 ≤ L.β) (hβ1 : L.β < 1) {P : Matrix X X ℝ} (hP : P.PosSemidef) (hfix : L.T P = P)
    (x : X → ℝ) :
    IsGreatest (Set.range (L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) -
        (1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ))) x))
        (-(x ⬝ᵥ (P *ᵥ x)) - (1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ))) ∧
      ∀ u, L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) -
          (1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ))) x u =
          -(x ⬝ᵥ (P *ᵥ x)) - (1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ)) ↔
        u = -(L.F P *ᵥ x) := by
  have hd : L.β * trace (P * L.C * L.Cᵀ) + L.β * ((1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ))) =
      (1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ)) := by
    have : (1 - L.β) ≠ 0 := by linarith
    field_simp
    ring
  have h := L.bellObj_isGreatest hν hR hP hβ0 ((1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ))) x
  rw [hd, hfix] at h
  exact h

end LSProblem

/-- Miao, p. 293: controllability implies stabilizability. (With `Q = R = I`, the controllable
case of Proposition 9.3.1 gives a fixed point whose gain `H` makes `A + BH` stable.) -/
theorem controllable_stabilizable {X U : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype U] {A : Matrix X X ℝ} {B : Matrix X U ℝ}
    (hc : ls_Controllable A B) : ls_Stabilizable A B := by
  classical
  set L0 : SS.LQProblem X U := ⟨A, B, 1, 1, PosSemidef.one, PosDef.one⟩
  obtain ⟨P, -, -, hst, -⟩ := ls_riccati_main L0 (Or.inr hc)
    fun F => ls_detects_of_posDef L0 PosDef.one F
  exact ⟨L0.gain P, ls_stable_of_specRad hst⟩


end Miao.LinearQuadratic

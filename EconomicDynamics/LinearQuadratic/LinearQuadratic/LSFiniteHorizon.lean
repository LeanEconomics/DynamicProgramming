/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.LSRiccati
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite-horizon LQ problems: Proposition 9.2.1

Miao, §9.2, pp. 294–297. The non-stationary problem
`max −E[∑_{t<T} βᵗ(x_t'Q_tx_t + u_t'R_tu_t + 2x_t'S_tu_t) + βᵀx_T'P_Tx_T]` subject to
`x_{t+1} = A_tx_t + B_tu_t + C_tε_{t+1}` (`LSFinProblem`; its date-`t` data form the
one-period problem `stage t`).

The shocks enter the Bellman equation only through the conditional law of `ε_{t+1}` given
`F_t`; under Assumption 9.1.1 this law has mean zero and identity second moments. We model it by
a probability measure `ν` on `ℝ^{nε}` with these moments (`LSShockLaw`); see `LSStateSpace` for
Assumption 9.1.1 itself and the conditional-expectation computation of p. 296.

* `ls_integral_quad` (p. 296): `E(y + Cε)'P(y + Cε) = y'Py + tr(PCC')`.
* `LSProblem.bellObj_quad`, `LSProblem.bellObj_isGreatest` (pp. 295–296): with a quadratic
  continuation value `−z'Pz − d`, the Bellman objective is
  `−x'T(P)x − β tr(PCC') − βd − (u + F(P)x)'G(P)(u + F(P)x)`, maximised exactly at
  `u = −F(P)x`; the first-order condition `(R + βB'PB)u = −(S' + βB'PA)x` (`ls_foc`) and the
  first variation (`ls_first_variation`).
* `LSFinProblem.V` is the value function defined by the Bellman recursion (with `sSup`), and
  `P`, `d`, `Fg` are the backward recursions (9.5), (9.6), (9.8).
* **Proposition 9.2.1** (`proposition_9_2_1`): `V_t(x) = −x'P_tx − d_t` (9.4), `P_t ≥ 0`,
  (9.5), (9.6), and the optimal control is `u_t = −F_tx_t` (9.7)–(9.8), uniquely.
* `eq_9_9`: (9.9), `P_t` is the Loewner minimum of `T_F` over `F`, attained at `F_t`.
* `ls_finite_seq_identity`, `ls_finite_seq_optimal`: for the deterministic problem, every control
  sequence satisfies `∑βᵗr_t + βᵀx_T'P_Tx_T = x_0'P_0x_0 + ∑βᵗ(u_t + F_tx_t)'G_t(u_t + F_tx_t)`,
  so the feedback rule is optimal among all (open-loop) sequences, uniquely.
* `certainty_equivalence` (p. 297): `C_t` affects neither `P_t` nor `F_t`, only `d_t`; the value
  of the stochastic problem is that of the deterministic one minus `d_t`, and the decision rules
  coincide.

Departure: Proposition 9.2.1 is stated for `β ∈ (0, 1]`; only `β ≥ 0` is used.
-/

open Matrix MeasureTheory

open scoped MatrixOrder

namespace Miao.LinearQuadratic

variable {X U E : Type*} [Fintype X] [Fintype U] [Fintype E]

/-- The conditional law of `ε_{t+1}` under Assumption 9.1.1: a probability measure on `ℝ^{nε}`
with integrable first and second moments, mean zero and second moments `I`. -/
structure LSShockLaw [DecidableEq E] (ν : Measure (E → ℝ)) : Prop where
  prob : IsProbabilityMeasure ν
  int1 : ∀ k, Integrable (fun e : E → ℝ => e k) ν
  int2 : ∀ k l, Integrable (fun e : E → ℝ => e k * e l) ν
  mean : ∀ k, ∫ e, e k ∂ν = 0
  cov : ∀ k l, ∫ e, e k * e l ∂ν = if k = l then 1 else 0

omit [Fintype X] in
/-- Expanding `(y + Ce)'P(y + Ce)` into constant, linear and quadratic terms in `e`. -/
theorem ls_quad_shock_expand [Fintype X] (y : X → ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ)
    (e : E → ℝ) :
    (y + C *ᵥ e) ⬝ᵥ (P *ᵥ (y + C *ᵥ e)) = y ⬝ᵥ (P *ᵥ y) +
      ∑ k, (y ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ y)) k * e k +
      ∑ k, ∑ l, (Cᵀ * P * C) k l * (e k * e l) := by
  have h1 : y ⬝ᵥ (P *ᵥ (C *ᵥ e)) = ∑ k, (y ᵥ* (P * C)) k * e k := by
    rw [mulVec_mulVec, dotProduct_mulVec]
    rfl
  have h2 : (C *ᵥ e) ⬝ᵥ (P *ᵥ y) = ∑ k, (Cᵀ *ᵥ (P *ᵥ y)) k * e k := by
    rw [SS.LQProblem.mulVec_dotProduct, dotProduct_comm]
    rfl
  have h3 : (C *ᵥ e) ⬝ᵥ (P *ᵥ (C *ᵥ e)) = ∑ k, ∑ l, (Cᵀ * P * C) k l * (e k * e l) := by
    rw [← SS.LQProblem.dotProduct_transpose_mul_mul]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, h1, h2, h3]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- Miao, p. 296: `E[(y + Cε)'P(y + Cε)] = y'Py + tr(PCC')` when `ε` has mean zero and second
moments `I` (and the integrand is integrable). -/
theorem ls_integral_quad [DecidableEq E] {ν : Measure (E → ℝ)} (hν : LSShockLaw ν)
    (y : X → ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    Integrable (fun e : E → ℝ => (y + C *ᵥ e) ⬝ᵥ (P *ᵥ (y + C *ᵥ e))) ν ∧
      ∫ e, (y + C *ᵥ e) ⬝ᵥ (P *ᵥ (y + C *ᵥ e)) ∂ν = y ⬝ᵥ (P *ᵥ y) + trace (P * C * Cᵀ) := by
  have := hν.prob
  simp only [ls_quad_shock_expand]
  have hlin : Integrable (fun e : E → ℝ => ∑ k, (y ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ y)) k * e k) ν :=
    integrable_finsetSum _ fun k _ => (hν.int1 k).const_mul _
  have hq : Integrable (fun e : E → ℝ => ∑ k, ∑ l, (Cᵀ * P * C) k l * (e k * e l)) ν :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hν.int2 k l).const_mul _
  have hcl : Integrable (fun e : E → ℝ => y ⬝ᵥ (P *ᵥ y) +
      ∑ k, (y ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ y)) k * e k) ν := (integrable_const _).add hlin
  refine ⟨hcl.add hq, ?_⟩
  have hlin0 : ∫ e, ∑ k, (y ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ y)) k * e k ∂ν = 0 := by
    rw [integral_finsetSum (f := fun k (e : E → ℝ) => (y ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ y)) k * e k)
      _ fun k _ => (hν.int1 k).const_mul _]
    simp [integral_const_mul, hν.mean]
  have hrow : ∀ k, ∫ e, ∑ l, (Cᵀ * P * C) k l * (e k * e l) ∂ν = (Cᵀ * P * C) k k := by
    intro k
    rw [integral_finsetSum (f := fun l (e : E → ℝ) => (Cᵀ * P * C) k l * (e k * e l)) _
      fun l _ => (hν.int2 k l).const_mul _]
    simp [integral_const_mul, hν.cov]
  have hq0 : ∫ e, ∑ k, ∑ l, (Cᵀ * P * C) k l * (e k * e l) ∂ν = trace (Cᵀ * P * C) := by
    rw [integral_finsetSum (f := fun k (e : E → ℝ) => ∑ l, (Cᵀ * P * C) k l * (e k * e l)) _
      fun k _ => integrable_finsetSum _ fun l _ => (hν.int2 k l).const_mul _]
    simp only [hrow]
    rfl
  have htr : trace (Cᵀ * P * C) = trace (P * C * Cᵀ) := by rw [Matrix.mul_assoc, trace_mul_comm]
  rw [integral_add hcl hq, integral_add (integrable_const _) hlin, integral_const, hlin0, hq0,
    probReal_univ, one_smul, add_zero, htr]

namespace LSProblem

variable (L : LSProblem X U E)

/-- The Bellman objective with continuation value `W`:
`−r(x, u) + βE W(Ax + Bu + Cε)`. -/
noncomputable def bellObj (ν : Measure (E → ℝ)) (W : (X → ℝ) → ℝ) (x : X → ℝ) (u : U → ℝ) :
    ℝ :=
  -L.loss x u + L.β * ∫ e, W (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ∂ν

variable [DecidableEq U] [DecidableEq E]

/-- Miao, pp. 295–296: with the quadratic continuation value `−z'Pz − d`,
`−r(x, u) + βE V(x') = −x'T(P)x − (β tr(PCC') + βd) − (u + F(P)x)'G(P)(u + F(P)x)`. -/
theorem bellObj_quad {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (hR : L.Rᵀ = L.R)
    {P : Matrix X X ℝ} (hP : Pᵀ = P) (hu : IsUnit (L.G P).det) (d : ℝ) (x : X → ℝ)
    (u : U → ℝ) :
    L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) x u =
      -(x ⬝ᵥ (L.T P *ᵥ x)) - (L.β * trace (P * L.C * L.Cᵀ) + L.β * d) -
        (u + L.F P *ᵥ x) ⬝ᵥ (L.G P *ᵥ (u + L.F P *ᵥ x)) := by
  have := hν.prob
  obtain ⟨hint, heq⟩ := ls_integral_quad hν (L.A *ᵥ x + L.B *ᵥ u) L.C P
  have hI : ∫ e, (-((L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ⬝ᵥ
      (P *ᵥ (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e))) - d) ∂ν =
      -((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ u)) + trace (P * L.C * L.Cᵀ)) - d := by
    have hn : Integrable (fun e : E → ℝ => -((L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ⬝ᵥ
        (P *ᵥ (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)))) ν := hint.neg
    rw [integral_sub hn (integrable_const d), integral_neg, heq, integral_const,
      probReal_univ, one_smul]
  have hsq := L.loss_add_cont hR hP hu x u
  rw [bellObj, hI]
  linear_combination -hsq

/-- Miao, pp. 295–296: the Bellman maximum with continuation `−z'Pz − d` is
`−x'T(P)x − β tr(PCC') − βd`, attained exactly at `u = −F(P)x`. -/
theorem bellObj_isGreatest {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (hR : L.R.PosDef)
    {P : Matrix X X ℝ} (hP : P.PosSemidef) (hβ : 0 ≤ L.β) (d : ℝ) (x : X → ℝ) :
    IsGreatest (Set.range (L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) x))
        (-(x ⬝ᵥ (L.T P *ᵥ x)) - (L.β * trace (P * L.C * L.Cᵀ) + L.β * d)) ∧
      ∀ u, L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) x u =
          -(x ⬝ᵥ (L.T P *ᵥ x)) - (L.β * trace (P * L.C * L.Cᵀ) + L.β * d) ↔
        u = -(L.F P *ᵥ x) := by
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have hG := L.G_posDef hR hP hβ
  have hu := (isUnit_iff_isUnit_det _).1 hG.isUnit
  have hG' := SS.LQProblem.posDef_iff_real.1 hG
  have hq : ∀ v, 0 ≤ v ⬝ᵥ (L.G P *ᵥ v) := (SS.LQProblem.posSemidef_iff_real.1 hG.posSemidef).2
  refine ⟨⟨⟨-(L.F P *ᵥ x), ?_⟩, ?_⟩, fun u => ?_⟩
  · rw [L.bellObj_quad hν hRs hPs hu, neg_add_cancel, mulVec_zero, dotProduct_zero, sub_zero]
  · rintro _ ⟨u, rfl⟩
    rw [L.bellObj_quad hν hRs hPs hu]
    linarith [hq (u + L.F P *ᵥ x)]
  · rw [L.bellObj_quad hν hRs hPs hu, sub_eq_self]
    constructor
    · intro h
      by_contra hne
      have : u + L.F P *ᵥ x ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
      linarith [hG'.2 this]
    · rintro rfl
      rw [neg_add_cancel, mulVec_zero, dotProduct_zero]

omit [DecidableEq E] [Fintype E] in
/-- The first-order condition (Miao, p. 296): `(R + βB'PB)u = −(S' + βB'PA)x` iff
`u = −F(P)x`. -/
theorem ls_foc {P : Matrix X X ℝ} (hu : IsUnit (L.G P).det) (x : X → ℝ) (u : U → ℝ) :
    L.G P *ᵥ u = -(L.N P *ᵥ x) ↔ u = -(L.F P *ᵥ x) := by
  constructor
  · intro h
    have := congrArg (fun v => (L.G P)⁻¹ *ᵥ v) h
    simp only [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec, mulVec_neg] at this
    rw [this, F, ← mulVec_mulVec]
  · rintro rfl
    rw [mulVec_neg, mulVec_mulVec, G_mul_F _ hu]

/-- The first variation of the Bellman objective in the control (Miao, p. 296, footnote 1):
`obj(u + h) − obj(u) = −2h'(G(P)u + N(P)x) − h'G(P)h`; it vanishes to first order iff the
first-order condition `G(P)u + N(P)x = 0` holds. -/
theorem ls_first_variation {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (hR : L.Rᵀ = L.R)
    {P : Matrix X X ℝ} (hP : Pᵀ = P) (hu : IsUnit (L.G P).det) (d : ℝ) (x : X → ℝ)
    (u h : U → ℝ) :
    L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) x (u + h) -
        L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) x u =
      -2 * (h ⬝ᵥ (L.G P *ᵥ u + L.N P *ᵥ x)) - h ⬝ᵥ (L.G P *ᵥ h) := by
  have hGs := L.G_transpose hR hP
  rw [L.bellObj_quad hν hR hP hu, L.bellObj_quad hν hR hP hu]
  have hNF : L.N P *ᵥ x = L.G P *ᵥ (L.F P *ᵥ x) := by rw [mulVec_mulVec, G_mul_F _ hu]
  have e := SS.LQProblem.quad_add hGs (u + L.F P *ᵥ x) h
  rw [show u + h + L.F P *ᵥ x = u + L.F P *ᵥ x + h by abel, e, hNF,
    SS.LQProblem.dotProduct_mulVec_comm_of_symm hGs h, ← mulVec_add,
    SS.LQProblem.dotProduct_mulVec_comm_of_symm hGs h (u + L.F P *ᵥ x)]
  ring

end LSProblem

/-- The non-stationary finite-horizon problem of §9.2 (Miao, p. 294): date-`t` matrices
`A_t, B_t, C_t, Q_t, R_t, S_t`, discount factor `β`, horizon `T` (`hor`) and terminal `P_T`. -/
structure LSFinProblem (X U E : Type*) where
  /-- `A_t` -/
  A : ℕ → Matrix X X ℝ
  /-- `B_t` -/
  B : ℕ → Matrix X U ℝ
  /-- `C_t` -/
  C : ℕ → Matrix X E ℝ
  /-- `Q_t` -/
  Q : ℕ → Matrix X X ℝ
  /-- `R_t` -/
  R : ℕ → Matrix U U ℝ
  /-- `S_t` -/
  S : ℕ → Matrix X U ℝ
  /-- the discount factor -/
  β : ℝ
  /-- the horizon `T` -/
  hor : ℕ
  /-- the terminal matrix `P_T` -/
  PT : Matrix X X ℝ

namespace LSFinProblem

variable (L : LSFinProblem X U E)

/-- The date-`t` one-period problem. -/
def stage (t : ℕ) : LSProblem X U E := ⟨L.A t, L.B t, L.C t, L.Q t, L.R t, L.S t, L.β⟩

variable [DecidableEq U]

/-- The Riccati recursion (9.5), indexed by the number `s` of remaining periods. -/
noncomputable def Pbk : ℕ → Matrix X X ℝ
  | 0 => L.PT
  | s + 1 => (L.stage (L.hor - s - 1)).T (Pbk s)

/-- The constants (9.6), indexed by the number of remaining periods. -/
noncomputable def dbk : ℕ → ℝ
  | 0 => 0
  | s + 1 => L.β * trace (L.Pbk s * L.C (L.hor - s - 1) * (L.C (L.hor - s - 1))ᵀ) + L.β * dbk s

/-- `P_t` (9.5). -/
noncomputable def P (t : ℕ) : Matrix X X ℝ := L.Pbk (L.hor - t)

/-- `d_t` (9.6). -/
noncomputable def d (t : ℕ) : ℝ := L.dbk (L.hor - t)

/-- The gain `F_t = (R_t + βB_t'P_{t+1}B_t)⁻¹(S_t' + βB_t'P_{t+1}A_t)` (9.8). -/
noncomputable def Fg (t : ℕ) : Matrix U X ℝ := (L.stage t).F (L.P (t + 1))

/-- The value function, defined by the Bellman recursion
`V_t(x) = sup_u {−r_t(x, u) + βE V_{t+1}(A_tx + B_tu + C_tε)}`, `V_T(x) = −x'P_Tx`, indexed by
the number of remaining periods. -/
noncomputable def Vbk (ν : Measure (E → ℝ)) : ℕ → (X → ℝ) → ℝ
  | 0 => fun x => -(x ⬝ᵥ (L.PT *ᵥ x))
  | s + 1 => fun x => sSup (Set.range ((L.stage (L.hor - s - 1)).bellObj ν (Vbk ν s) x))

/-- The value function `V_t`. -/
noncomputable def V (ν : Measure (E → ℝ)) (t : ℕ) (x : X → ℝ) : ℝ := L.Vbk ν (L.hor - t) x

omit [Fintype E] in
theorem P_hor : L.P L.hor = L.PT := by simp [P, Pbk]

theorem d_hor : L.d L.hor = 0 := by simp [d, dbk]

omit [DecidableEq U] in
theorem V_hor (ν : Measure (E → ℝ)) (x : X → ℝ) : L.V ν L.hor x = -(x ⬝ᵥ (L.PT *ᵥ x)) := by
  simp [V, Vbk]

omit [Fintype E] in
/-- (9.5): `P_t = T_t(P_{t+1})` for `t < T`. -/
theorem P_succ {t : ℕ} (ht : t < L.hor) : L.P t = (L.stage t).T (L.P (t + 1)) := by
  have h1 : L.hor - t = L.hor - (t + 1) + 1 := by omega
  have h2 : L.hor - (L.hor - (t + 1)) - 1 = t := by omega
  rw [P, h1, Pbk, h2]
  rfl

/-- (9.6): `d_t = β tr(P_{t+1}C_tC_t') + βd_{t+1}` for `t < T`. -/
theorem d_succ {t : ℕ} (ht : t < L.hor) :
    L.d t = L.β * trace (L.P (t + 1) * L.C t * (L.C t)ᵀ) + L.β * L.d (t + 1) := by
  have h1 : L.hor - t = L.hor - (t + 1) + 1 := by omega
  have h2 : L.hor - (L.hor - (t + 1)) - 1 = t := by omega
  rw [d, h1, dbk, h2]
  rfl

omit [DecidableEq U] in
/-- The Bellman equation defining `V_t`, `t < T`. -/
theorem V_succ (ν : Measure (E → ℝ)) {t : ℕ} (ht : t < L.hor) (x : X → ℝ) :
    L.V ν t x = sSup (Set.range ((L.stage t).bellObj ν (L.V ν (t + 1)) x)) := by
  have h1 : L.hor - t = L.hor - (t + 1) + 1 := by omega
  have h2 : L.hor - (L.hor - (t + 1)) - 1 = t := by omega
  rw [V, h1, Vbk, h2]
  rfl

variable [DecidableEq E]

/-- **Proposition 9.2.1** (Miao, p. 295). Suppose `[[Q_t, S_t], [S_t', R_t]] ≥ 0`, `R_t > 0`
(`t < T`) and `P_T ≥ 0` (and `β ≥ 0`). Then for `t ≤ T`:
(i) the value function is `V_t(x) = −x'P_tx − d_t` (9.4), with `P_t ≥ 0`; `P_t` satisfies
(9.5) and `d_t` satisfies (9.6), `d_T = 0`;
(ii) for `t < T` the optimal control is `u_t = −F_tx_t` (9.7)–(9.8): it attains the Bellman
maximum, and it is the only control that does. -/
theorem proposition_9_2_1 {ν : Measure (E → ℝ)} (hν : LSShockLaw ν)
    (hJ : ∀ t < L.hor, (L.stage t).JointPSD) (hR : ∀ t < L.hor, (L.R t).PosDef)
    (hPT : L.PT.PosSemidef) (hβ : 0 ≤ L.β) :
    (∀ t ≤ L.hor, ∀ x, L.V ν t x = -(x ⬝ᵥ (L.P t *ᵥ x)) - L.d t) ∧
    (∀ t ≤ L.hor, (L.P t).PosSemidef) ∧
    (∀ t < L.hor, L.P t = L.Q t + L.β • ((L.A t)ᵀ * L.P (t + 1) * L.A t) -
      (L.S t + L.β • ((L.A t)ᵀ * L.P (t + 1) * L.B t)) *
        (L.R t + L.β • ((L.B t)ᵀ * L.P (t + 1) * L.B t))⁻¹ *
        (L.β • ((L.B t)ᵀ * L.P (t + 1) * L.A t) + (L.S t)ᵀ)) ∧
    (∀ t < L.hor, L.d t = L.β * trace (L.P (t + 1) * L.C t * (L.C t)ᵀ) + L.β * L.d (t + 1)) ∧
    L.d L.hor = 0 ∧
    (∀ t < L.hor, ∀ x, IsGreatest (Set.range ((L.stage t).bellObj ν (L.V ν (t + 1)) x))
        (L.V ν t x) ∧
      ∀ u, (L.stage t).bellObj ν (L.V ν (t + 1)) x u = L.V ν t x ↔ u = -(L.Fg t *ᵥ x)) := by
  -- the induction on the number of remaining periods
  have key : ∀ s ≤ L.hor, (L.Pbk s).PosSemidef ∧
      ∀ x, L.Vbk ν s x = -(x ⬝ᵥ (L.Pbk s *ᵥ x)) - L.dbk s := by
    intro s
    induction s with
    | zero => exact fun _ => ⟨hPT, fun x => by simp [Pbk, Vbk, dbk]⟩
    | succ s ih =>
      intro hs
      obtain ⟨hP, hV⟩ := ih (by omega)
      have ht : L.hor - s - 1 < L.hor := by omega
      have hW : L.Vbk ν s = fun z => -(z ⬝ᵥ (L.Pbk s *ᵥ z)) - L.dbk s := funext hV
      refine ⟨(L.stage _).T_posSemidef (hJ _ ht) (hR _ ht) hβ hP, fun x => ?_⟩
      have hg := ((L.stage (L.hor - s - 1)).bellObj_isGreatest hν (hR _ ht) hP hβ
        (L.dbk s) x).1
      simp only [Vbk, Pbk, dbk]
      rw [hW, hg.csSup_eq]
      rfl
  have hV : ∀ t ≤ L.hor, ∀ x, L.V ν t x = -(x ⬝ᵥ (L.P t *ᵥ x)) - L.d t :=
    fun t _ x => (key (L.hor - t) (by omega)).2 x
  have hP : ∀ t ≤ L.hor, (L.P t).PosSemidef := fun t _ => (key (L.hor - t) (by omega)).1
  refine ⟨hV, hP, fun t ht => ?_, fun t ht => L.d_succ ht, L.d_hor, fun t ht x => ?_⟩
  · rw [L.P_succ ht, LSProblem.T, LSProblem.N, add_comm (L.stage t).Sᵀ]
    rfl
  · have hW : L.V ν (t + 1) = fun z => -(z ⬝ᵥ (L.P (t + 1) *ᵥ z)) - L.d (t + 1) :=
      funext (hV (t + 1) ht)
    obtain ⟨hg, hu⟩ := (L.stage t).bellObj_isGreatest hν (hR t ht) (hP (t + 1) ht) hβ
      (L.d (t + 1)) x
    have hVt : L.V ν t x = -(x ⬝ᵥ ((L.stage t).T (L.P (t + 1)) *ᵥ x)) -
        (L.β * trace (L.P (t + 1) * L.C t * (L.C t)ᵀ) + L.β * L.d (t + 1)) := by
      rw [hV t ht.le, L.P_succ ht, L.d_succ ht]
    rw [hW, hVt]
    exact ⟨hg, hu⟩

omit [DecidableEq E] [Fintype E] in
/-- (9.9) (Miao, p. 297): `P_t = min_F [Q_t − F'S_t' − S_tF + F'R_tF + β(A_t − B_tF)'P_{t+1}
(A_t − B_tF)]` in the Loewner order, the minimum being attained exactly at `F = F_t`. -/
theorem eq_9_9 (hJ : ∀ t < L.hor, (L.stage t).JointPSD) (hR : ∀ t < L.hor, (L.R t).PosDef)
    (hPT : L.PT.PosSemidef) (hβ : 0 ≤ L.β) {t : ℕ} (ht : t < L.hor) :
    (∀ F' : Matrix U X ℝ, L.P t ≤ (L.stage t).TF (L.P (t + 1)) F') ∧
      ∀ F' : Matrix U X ℝ, (L.stage t).TF (L.P (t + 1)) F' = L.P t ↔ F' = L.Fg t := by
  have hPpsd : ∀ s ≤ L.hor, (L.Pbk s).PosSemidef := by
    intro s
    induction s with
    | zero => exact fun _ => hPT
    | succ s ih =>
      intro hs
      exact (L.stage _).T_posSemidef (hJ _ (by omega)) (hR _ (by omega)) hβ (ih (by omega))
  have hP1 : (L.P (t + 1)).PosSemidef := hPpsd _ (by omega)
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP1).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 (hR t ht)).1
  have hG := (L.stage t).G_posDef (hR t ht) hP1 hβ
  rw [L.P_succ ht]
  exact ⟨(L.stage t).TF_ge_T hRs hPs hG, (L.stage t).TF_eq_T_iff hRs hPs hG⟩

omit [DecidableEq E] [Fintype E] in
/-- Completing the square along a deterministic path (Miao, pp. 295–297): if
`x_{t+1} = A_tx_t + B_tu_t` for `t < T`, then
`∑_{t<T} βᵗr_t(x_t, u_t) + βᵀx_T'P_Tx_T = x_0'P_0x_0 + ∑_{t<T} βᵗ(u_t + F_tx_t)'G_t(u_t + F_tx_t)`,
where `G_t = R_t + βB_t'P_{t+1}B_t`. -/
theorem ls_finite_seq_identity (hRs : ∀ t < L.hor, (L.R t)ᵀ = L.R t)
    (hPs : ∀ t ≤ L.hor, (L.P t)ᵀ = L.P t)
    (hu : ∀ t < L.hor, IsUnit ((L.stage t).G (L.P (t + 1))).det)
    (x : ℕ → X → ℝ) (u : ℕ → U → ℝ) (hx : ∀ t < L.hor, x (t + 1) = L.A t *ᵥ x t + L.B t *ᵥ u t) :
    ∑ t ∈ Finset.range L.hor, L.β ^ t * (L.stage t).loss (x t) (u t) +
        L.β ^ L.hor * (x L.hor ⬝ᵥ (L.PT *ᵥ x L.hor)) =
      x 0 ⬝ᵥ (L.P 0 *ᵥ x 0) + ∑ t ∈ Finset.range L.hor, L.β ^ t *
        ((u t + L.Fg t *ᵥ x t) ⬝ᵥ ((L.stage t).G (L.P (t + 1)) *ᵥ (u t + L.Fg t *ᵥ x t))) := by
  have step : ∀ n ≤ L.hor, ∑ t ∈ Finset.range n, L.β ^ t * (L.stage t).loss (x t) (u t) +
      L.β ^ n * (x n ⬝ᵥ (L.P n *ᵥ x n)) = x 0 ⬝ᵥ (L.P 0 *ᵥ x 0) +
      ∑ t ∈ Finset.range n, L.β ^ t *
        ((u t + L.Fg t *ᵥ x t) ⬝ᵥ ((L.stage t).G (L.P (t + 1)) *ᵥ (u t + L.Fg t *ᵥ x t))) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have ht : n < L.hor := by omega
      have hsq := (L.stage n).loss_add_cont (hRs n ht) (hPs (n + 1) hn) (hu n ht) (x n) (u n)
      rw [← L.P_succ ht] at hsq
      have hx' : (L.stage n).A *ᵥ x n + (L.stage n).B *ᵥ u n = x (n + 1) := (hx n ht).symm
      rw [hx'] at hsq
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hb : (L.stage n).β = L.β := rfl
      rw [hb] at hsq
      simp only [Fg] at ih ⊢
      linear_combination ih (by omega) + L.β ^ n * hsq
  have := step L.hor le_rfl
  rwa [L.P_hor] at this

omit [DecidableEq E] [Fintype E] in
/-- Optimality of the feedback rule among all control sequences for the deterministic problem
(Miao, pp. 296–297): under the hypotheses of Proposition 9.2.1 and `β > 0`, every sequence
satisfies `∑_{t<T} βᵗr_t + βᵀx_T'P_Tx_T ≥ x_0'P_0x_0`, with equality iff `u_t = −F_tx_t` for all
`t < T`. -/
theorem ls_finite_seq_optimal (hJ : ∀ t < L.hor, (L.stage t).JointPSD)
    (hR : ∀ t < L.hor, (L.R t).PosDef) (hPT : L.PT.PosSemidef) (hβ : 0 < L.β)
    (x : ℕ → X → ℝ) (u : ℕ → U → ℝ) (hx : ∀ t < L.hor, x (t + 1) = L.A t *ᵥ x t + L.B t *ᵥ u t) :
    x 0 ⬝ᵥ (L.P 0 *ᵥ x 0) ≤ ∑ t ∈ Finset.range L.hor, L.β ^ t * (L.stage t).loss (x t) (u t) +
        L.β ^ L.hor * (x L.hor ⬝ᵥ (L.PT *ᵥ x L.hor)) ∧
      (x 0 ⬝ᵥ (L.P 0 *ᵥ x 0) = ∑ t ∈ Finset.range L.hor, L.β ^ t * (L.stage t).loss (x t) (u t) +
        L.β ^ L.hor * (x L.hor ⬝ᵥ (L.PT *ᵥ x L.hor)) ↔ ∀ t < L.hor, u t = -(L.Fg t *ᵥ x t)) := by
  have hPpsd : ∀ s ≤ L.hor, (L.Pbk s).PosSemidef := by
    intro s
    induction s with
    | zero => exact fun _ => hPT
    | succ s ih =>
      intro hs
      exact (L.stage _).T_posSemidef (hJ _ (by omega)) (hR _ (by omega)) hβ.le (ih (by omega))
  have hP : ∀ t ≤ L.hor, (L.P t).PosSemidef := fun t _ => hPpsd _ (by omega)
  have hG : ∀ t < L.hor, ((L.stage t).G (L.P (t + 1))).PosDef := fun t ht =>
    (L.stage t).G_posDef (hR t ht) (hP (t + 1) ht) hβ.le
  have hid := L.ls_finite_seq_identity (fun t ht => (SS.LQProblem.posDef_iff_real.1 (hR t ht)).1)
    (fun t ht => (SS.LQProblem.posSemidef_iff_real.1 (hP t ht)).1)
    (fun t ht => (isUnit_iff_isUnit_det _).1 (hG t ht).isUnit) x u hx
  have hnn : ∀ t ∈ Finset.range L.hor, 0 ≤ L.β ^ t *
      ((u t + L.Fg t *ᵥ x t) ⬝ᵥ ((L.stage t).G (L.P (t + 1)) *ᵥ (u t + L.Fg t *ᵥ x t))) :=
    fun t ht => mul_nonneg (pow_nonneg hβ.le t)
      ((SS.LQProblem.posSemidef_iff_real.1 (hG t (Finset.mem_range.1 ht)).posSemidef).2 _)
  rw [hid]
  refine ⟨le_add_of_nonneg_right (Finset.sum_nonneg hnn), ?_⟩
  rw [left_eq_add, Finset.sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h t ht
    have h1 := h t (Finset.mem_range.2 ht)
    rw [mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (pow_ne_zero _ hβ.ne')
    · by_contra hne
      have : u t + L.Fg t *ᵥ x t ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
      have := (SS.LQProblem.posDef_iff_real.1 (hG t ht)).2 this
      linarith
  · intro h t ht
    rw [h t (Finset.mem_range.1 ht), neg_add_cancel, mulVec_zero, dotProduct_zero, mul_zero]

/-- The same problem with the shock loadings `C_t` set to zero: the corresponding deterministic
problem. -/
def zeroC : LSFinProblem X U E := { L with C := fun _ => 0 }

omit [DecidableEq E] [Fintype E] in
theorem zeroC_Pbk (s : ℕ) : L.zeroC.Pbk s = L.Pbk s := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [Pbk, ih]; rfl

omit [DecidableEq E] in
theorem zeroC_dbk (s : ℕ) : L.zeroC.dbk s = 0 := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [dbk, ih]
    simp [zeroC]

/-- **Certainty equivalence principle** (Miao, p. 297): the shock loadings affect neither the
Riccati matrices `P_t` nor the decision rules `F_t`; they only shift the constants `d_t` (which
vanish in the deterministic problem). Hence the value of the stochastic problem is that of the
deterministic problem minus `d_t`, and the two problems have the same optimal decision rule
`u_t = −F_tx_t`. -/
theorem certainty_equivalence {ν : Measure (E → ℝ)} (hν : LSShockLaw ν)
    (hJ : ∀ t < L.hor, (L.stage t).JointPSD) (hR : ∀ t < L.hor, (L.R t).PosDef)
    (hPT : L.PT.PosSemidef) (hβ : 0 ≤ L.β) :
    (∀ t, L.zeroC.P t = L.P t) ∧ (∀ t, L.zeroC.Fg t = L.Fg t) ∧ (∀ t, L.zeroC.d t = 0) ∧
    (∀ t ≤ L.hor, ∀ x, L.V ν t x = L.zeroC.V ν t x - L.d t) ∧
    (∀ t < L.hor, ∀ x u, (L.stage t).bellObj ν (L.V ν (t + 1)) x u = L.V ν t x ↔
      (L.zeroC.stage t).bellObj ν (L.zeroC.V ν (t + 1)) x u = L.zeroC.V ν t x) := by
  have hPe : ∀ t, L.zeroC.P t = L.P t := fun t => L.zeroC_Pbk _
  have hFe : ∀ t, L.zeroC.Fg t = L.Fg t := fun t => by
    simp only [Fg, hPe]
    rfl
  have hde : ∀ t, L.zeroC.d t = 0 := fun t => L.zeroC_dbk _
  have h1 := L.proposition_9_2_1 hν hJ hR hPT hβ
  have h0 := L.zeroC.proposition_9_2_1 hν hJ hR hPT hβ
  refine ⟨hPe, hFe, hde, fun t ht x => ?_, fun t ht x u => ?_⟩
  · rw [h1.1 t ht, h0.1 t ht, hPe, hde]
    ring
  · rw [(h1.2.2.2.2.2 t ht x).2 u, (h0.2.2.2.2.2 t ht x).2 u, hFe]

end LSFinProblem

end Miao.LinearQuadratic

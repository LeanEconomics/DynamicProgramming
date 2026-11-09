/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.KFSteady

/-!
# Linear-quadratic control under partial information

Miao, §10.3, pp. 342–345. The LQ problem `max −E∑βᵗr(x_t, u_t)`, `x_{t+1} = Ax_t + Bu_t + η_{t+1}`,
`y_t = Gx_t + v_t`, when the decision maker observes only `y^t`. The book sketches the separation
principle (certainty equivalence): with the (stationary) Kalman filter, the value function is
`V(x̂_{t|t}) = −½x̂'_{t|t}Px̂_{t|t} + constant` with the same `P` as under full information (9.12),
and the policy is `u_t = −Fx̂_{t|t}` with the same `F` (9.17).

The project's LQ conventions (Chapter 9) are used: the loss is `r(x, u) = x'Qx + u'Ru + 2x'Su`
(the book's `r` without the factor `½`) and `V(x) = −x'Px − d`.

* `kf_Delta_succ`: `Δ_t = x_t − x̂_{t|t}` satisfies `Δ_{t+1} = AΔ_t + Cε_{t+1} − K_{t+1}a_{t+1}`
  (the book's `Δ_t = Ax_{t−1} + η_t − Ax̂_{t−1|t−1} − Ka_t`; the control terms cancel), and it
  does not depend on the controls (`KFSystem.kf_err_control_free`).
* `kf_expected_loss`: `E_t r(x̂ + Δ, u) = r(x̂, u) + E_tΔ'QΔ` when `Δ` has conditional mean zero —
  the decomposition `E_t[x'Qx + u'Ru + 2x'Su] = x̂'Qx̂ + u'Ru + 2x̂'Su + …` of p. 344.
* `kf_expected_cont`: with the filter law of motion `x̂_{t+1|t+1} = Ax̂_{t|t} + Bu_t + K a_{t+1}`
  (`KFSystem.kf_filt_recursive`) and `Ka_{t+1} = (KW)ξ_{t+1}`, `WW' = Ω`, `ξ` with mean zero and
  second moments `I`: `E_t x̂'_{t+1|t+1}Px̂_{t+1|t+1} = (Ax̂ + Bu)'P(Ax̂ + Bu) + tr(PKWW'K')`.
* `kf_certainty_equivalence` (**the separation principle**, pp. 343–345): the partial-information
  Bellman equation `V(x̂) = max_u {−E_t r(x̂ + Δ, u) + βE_tV(Ax̂ + Bu + KWξ)}` is solved by
  `V(x̂) = −x̂'Px̂ − d̂` with `P` the full-information Riccati fixed point (9.12), maximised exactly
  at `u = −F(P)x̂` with the full-information gain (9.17); only the constant changes:
  `d̂ = (1 − β)⁻¹(E Δ'QΔ + β tr(PKWW'K'))` instead of `(1 − β)⁻¹β tr(PCC')`
  (`LSProblem.eq_9_16_9_17`). The Riccati operator and gain do not depend on the shock loading
  (`kf_filt_T`).

Reading: the conditional laws given `y^t` are represented by a probability law `κ` of the
filtered error `Δ_t` (mean zero) and a law `ν` of the standardised innovation (mean zero, second
moments `I`); that `Δ_t` and `a_{t+1}` are conditionally mean zero given `y^t` and independent of
the control is the Gaussian reading of §10.1.1, whose second-moment content is `KFFilter`.
-/

open MeasureTheory Matrix

namespace Miao.PartialInformation

variable {X U E : Type*} [Fintype X] [Fintype U] [Fintype E]

namespace KFSystem

variable {Y : Type*} [Fintype Y] [DecidableEq X] [DecidableEq Y] (S : KFSystem X U Y E)
  {Ω : Type*} {x : ℕ → Ω → X → ℝ} {y h : ℕ → Ω → Y → ℝ} {u : ℕ → Ω → U → ℝ}
  {ε : ℕ → Ω → E → ℝ}

/-- Miao, p. 344: the filtered error `Δ_t = x_t − x̂_{t|t}` satisfies
`Δ_{t+1} = A_tΔ_t + C_tε_{t+1} − K_{t+1}a_{t+1}` (the control terms cancel). -/
theorem kf_Delta_succ
    (hx : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
      kf_app (S.C t) (ε (t + 1))) (t : ℕ) :
    x (t + 1) - S.xfilt y h u (t + 1) = kf_app (S.A t) (x t - S.xfilt y h u t) +
      kf_app (S.C t) (ε (t + 1)) - kf_app (S.K (t + 1)) (S.innov y h u (t + 1)) := by
  rw [S.kf_filt_err, S.kf_err_succ hx, ← S.kf_filt_err]

end KFSystem

variable [DecidableEq U] [DecidableEq E]

/-- The filtered-state problem: the LQ problem `L` with the shock loading replaced by `KW`
(the law of motion `x̂_{t+1|t+1} = Ax̂_{t|t} + Bu_t + KWξ_{t+1}`). -/
def kf_filtProblem {E' : Type*} (L : LSProblem X U E') (KW : Matrix X E ℝ) : LSProblem X U E :=
  ⟨L.A, L.B, KW, L.Q, L.R, L.S, L.β⟩

omit [Fintype E] [DecidableEq E] in
/-- Miao, p. 343: the Riccati operator (9.12) and the gain (9.17) of the filtered-state problem
are those of the full-information problem: they do not involve the shock loading. -/
theorem kf_filt_T {E' : Type*} (L : LSProblem X U E') (KW : Matrix X E ℝ) :
    (kf_filtProblem L KW).T = L.T ∧ (kf_filtProblem L KW).F = L.F := ⟨rfl, rfl⟩

omit [Fintype U] [Fintype E] [DecidableEq U] [DecidableEq E] in
/-- The expansion `r(x̂ + Δ, u) = r(x̂, u) + ℓ'Δ + Δ'QΔ` with `ℓ = Q'x̂ + Qx̂ + 2Su`. -/
theorem kf_loss_expand [Fintype U] (L : LSProblem X U E) (xh δ : X → ℝ) (v : U → ℝ) :
    L.loss (xh + δ) v = L.loss xh v +
      (xh ᵥ* L.Q + L.Q *ᵥ xh + (2 : ℝ) • (L.S *ᵥ v)) ⬝ᵥ δ + δ ⬝ᵥ (L.Q *ᵥ δ) := by
  simp only [LSProblem.loss, mulVec_add, dotProduct_add, add_dotProduct, smul_dotProduct,
    smul_eq_mul, dotProduct_mulVec xh L.Q δ, dotProduct_comm δ (L.Q *ᵥ xh),
    dotProduct_comm δ (L.S *ᵥ v)]
  ring

omit [Fintype U] [Fintype E] [DecidableEq U] [DecidableEq E] in
/-- Miao, p. 344: if the estimation error `Δ` has (conditional) law `κ` with mean zero and
integrable second moments, then `E_t r(x̂ + Δ, u) = r(x̂, u) + E_tΔ'QΔ`; the second term does not
depend on the control. -/
theorem kf_expected_loss [Fintype U] (L : LSProblem X U E) {κ : Measure (X → ℝ)}
    [IsProbabilityMeasure κ] (h1 : ∀ k, Integrable (fun δ : X → ℝ => δ k) κ)
    (h2 : ∀ k l, Integrable (fun δ : X → ℝ => δ k * δ l) κ) (hm : ∀ k, ∫ δ, δ k ∂κ = 0)
    (xh : X → ℝ) (v : U → ℝ) :
    Integrable (fun δ => L.loss (xh + δ) v) κ ∧
      ∫ δ, L.loss (xh + δ) v ∂κ = L.loss xh v + ∫ δ, δ ⬝ᵥ (L.Q *ᵥ δ) ∂κ := by
  set ℓ := xh ᵥ* L.Q + L.Q *ᵥ xh + (2 : ℝ) • (L.S *ᵥ v)
  have hq : ∀ δ : X → ℝ, δ ⬝ᵥ (L.Q *ᵥ δ) = ∑ k, ∑ l, L.Q k l * (δ k * δ l) := by
    intro δ
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hqi : Integrable (fun δ : X → ℝ => δ ⬝ᵥ (L.Q *ᵥ δ)) κ := by
    simp only [hq]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (h2 k l).const_mul _
  have hli : Integrable (fun δ : X → ℝ => ℓ ⬝ᵥ δ) κ := by
    simp only [dotProduct]
    exact integrable_finsetSum _ fun k _ => (h1 k).const_mul _
  have hl0 : ∫ δ, ℓ ⬝ᵥ δ ∂κ = 0 := by
    simp only [dotProduct]
    rw [integral_finsetSum _ fun k _ => (h1 k).const_mul _]
    simp [integral_const_mul, hm]
  have hI : Integrable (fun δ : X → ℝ => (L.loss xh v + ℓ ⬝ᵥ δ) + δ ⬝ᵥ (L.Q *ᵥ δ)) κ :=
    ((integrable_const _).add hli).add hqi
  have e : (fun δ => L.loss (xh + δ) v) =
      fun δ : X → ℝ => (L.loss xh v + ℓ ⬝ᵥ δ) + δ ⬝ᵥ (L.Q *ᵥ δ) :=
    funext fun δ => kf_loss_expand L xh δ v
  rw [e]
  refine ⟨hI, ?_⟩
  have hA : Integrable (fun δ : X → ℝ => L.loss xh v + ℓ ⬝ᵥ δ) κ := (integrable_const _).add hli
  rw [integral_add hA hqi, integral_add (integrable_const _) hli, hl0, integral_const,
    probReal_univ, one_smul, add_zero]

omit [Fintype U] [DecidableEq U] in
/-- Miao, p. 344: with the filter law of motion `x̂_{t+1|t+1} = Ax̂_{t|t} + Bu_t + KWξ_{t+1}`,
`E_t x̂'_{t+1|t+1}Px̂_{t+1|t+1} = (Ax̂_{t|t} + Bu_t)'P(Ax̂_{t|t} + Bu_t) + tr(P(KW)(KW)')`; the
second term does not depend on the control. -/
theorem kf_expected_cont {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (z : X → ℝ)
    (KW : Matrix X E ℝ) (P : Matrix X X ℝ) :
    ∫ e, (z + KW *ᵥ e) ⬝ᵥ (P *ᵥ (z + KW *ᵥ e)) ∂ν = z ⬝ᵥ (P *ᵥ z) + trace (P * KW * KWᵀ) :=
  (ls_integral_quad hν z KW P).2

/-- The partial-information Bellman objective (Miao, pp. 344–345):
`−E_t r(x̂ + Δ, u) + βE_t W(Ax̂ + Bu + KWξ)`, with `Δ ∼ κ` and `ξ ∼ ν`. -/
noncomputable def kf_piObj (L : LSProblem X U E) (κ : Measure (X → ℝ)) (ν : Measure (E → ℝ))
    (W : (X → ℝ) → ℝ) (xh : X → ℝ) (v : U → ℝ) : ℝ :=
  -∫ δ, L.loss (xh + δ) v ∂κ + L.β * ∫ e, W (L.A *ᵥ xh + L.B *ᵥ v + L.C *ᵥ e) ∂ν

/-- **The separation principle / certainty equivalence** (Miao, §10.3, pp. 343–345). Let `L` be
the filtered-state LQ problem (its shock loading `C = KW` is the filter's innovation loading),
`R > 0`, `0 ≤ β < 1`, `P ≥ 0` a fixed point `P = T(P)` of the full-information Riccati equation
(9.12), `κ` the law of the estimation error (mean zero, integrable second moments), `ν` the law
of the standardised innovation. Then with `d̂ = (1 − β)⁻¹(EΔ'QΔ + β tr(PCC'))` the function
`V(x̂) = −x̂'Px̂ − d̂` solves the partial-information Bellman equation: `V(x̂)` is the maximum over
`u` of `−E_t r(x̂ + Δ, u) + βE_tV(Ax̂ + Bu + Cξ)`, attained exactly at `u = −F(P)x̂`, the
full-information policy (9.17) applied to the filtered state. -/
theorem kf_certainty_equivalence (L : LSProblem X U E) {κ : Measure (X → ℝ)}
    [IsProbabilityMeasure κ] (h1 : ∀ k, Integrable (fun δ : X → ℝ => δ k) κ)
    (h2 : ∀ k l, Integrable (fun δ : X → ℝ => δ k * δ l) κ) (hm : ∀ k, ∫ δ, δ k ∂κ = 0)
    {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (hR : L.R.PosDef) (hβ0 : 0 ≤ L.β)
    (hβ1 : L.β < 1) {P : Matrix X X ℝ} (hP : P.PosSemidef) (hfix : L.T P = P) (xh : X → ℝ) :
    let dh := (1 - L.β)⁻¹ * (∫ δ, δ ⬝ᵥ (L.Q *ᵥ δ) ∂κ + L.β * trace (P * L.C * L.Cᵀ))
    IsGreatest (Set.range (kf_piObj L κ ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - dh) xh))
        (-(xh ⬝ᵥ (P *ᵥ xh)) - dh) ∧
      ∀ v, kf_piObj L κ ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - dh) xh v = -(xh ⬝ᵥ (P *ᵥ xh)) - dh ↔
        v = -(L.F P *ᵥ xh) := by
  intro dh
  set c := ∫ δ, δ ⬝ᵥ (L.Q *ᵥ δ) ∂κ
  have hobj : ∀ v, kf_piObj L κ ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - dh) xh v =
      L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - dh) xh v - c := by
    intro v
    rw [kf_piObj, LSProblem.bellObj, (kf_expected_loss L h1 h2 hm xh v).2]
    ring
  have hd : -(xh ⬝ᵥ (P *ᵥ xh)) - (L.β * trace (P * L.C * L.Cᵀ) + L.β * dh) - c =
      -(xh ⬝ᵥ (P *ᵥ xh)) - dh := by
    have : (1 - L.β) ≠ 0 := by linarith
    simp only [dh, c]
    field_simp
    ring
  obtain ⟨hg, hiff⟩ := L.bellObj_isGreatest hν hR hP hβ0 dh xh
  rw [hfix] at hg hiff
  refine ⟨⟨⟨-(L.F P *ᵥ xh), ?_⟩, ?_⟩, fun v => ?_⟩
  · rw [hobj, (hiff _).2 rfl, hd]
  · rintro _ ⟨v, rfl⟩
    rw [hobj, ← hd]
    exact sub_le_sub_right (hg.2 ⟨v, rfl⟩) c
  · rw [hobj, ← hd, sub_left_inj]
    exact hiff v

end Miao.PartialInformation

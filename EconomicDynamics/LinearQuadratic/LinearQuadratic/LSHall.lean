/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.LSExercises

/-!
# Exercise 9.4: Hall's consumption problem

Miao, §9.7, Exercise 9.4, pp. 325–326: `max −E∑βᵗ(c_t − b)²` subject to
`c_t + a_{t+1} = Ra_t + y_t`, `y_{t+1} = μ(1 − ρ) + ρy_t + σε_{t+1}`, with state
`x_t = [1, a_t, y_t]'` and control `c_t` (`hallProblem`; `ex_9_4_loss`, `ex_9_4_transition`).
Here `S ≠ 0` and `Q − SR⁻¹S' = 0`, so Propositions 9.3.1–9.3.2 do not apply; we solve the
Riccati equation explicitly.

With `κ = βR² > 1` (true in Hall's case `βR = 1`, as `R > 1`), `q = 1 − 1/κ` and
`w = [μR/(R − 1) − μR/(R − ρ) − bR/(R − 1), R, R/(R − ρ)]`:

* `ex_9_4_riccati`: `P = q ww'` solves the Riccati equation (9.12), with gain
  `F = −(b e₁' + q w')`, i.e. the consumption rule (`ex_9_4_rule`)
  `c_t = b + q(Ra_t + Ry_t/(R − ρ) + μR/(R − 1) − μR/(R − ρ) − bR/(R − 1))`;
  for `βR = 1` this is Hall's `c_t = (R − 1)a_t + μ + (R − 1)(y_t − μ)/(R − ρ)`
  (`ex_9_4_martingale`).
* `ex_9_4_optimal`: in the deterministic (certainty-equivalent) problem, every plan with
  `βᵗx_t'Px_t → 0` (for instance under the side condition (9.10)) has loss at least `x₀'Px₀`, and
  the rule attains `x₀'Px₀` (along it, `c_{t+1} − b = (βR)⁻¹(c_t − b)`).
* `ex_9_4_bellman`: with shocks, `V(x) = −x'Px − d` solves the Bellman equation and the rule is
  the unique maximiser (certainty equivalence).
* `ex_9_4_impatient`: for `βR² < 1`, `P = 0` solves (9.12) with rule `c_t = b`, which attains the
  infimum `0` of the loss (with debt growing at rate `R < 1/√β`, permitted by (9.10)).
-/

open Filter Topology Matrix MeasureTheory

namespace Miao.LinearQuadratic

/-- A positive semidefinite joint cost matrix from a nonnegative loss. -/
theorem ls_jointPSD_of_loss {X U E : Type*} [Fintype X] [Fintype U] (L : LSProblem X U E)
    (hQ : L.Qᵀ = L.Q) (hR : L.Rᵀ = L.R) (h : ∀ x u, 0 ≤ L.loss x u) : L.JointPSD := by
  refine SS.LQProblem.posSemidef_iff_real.2 ⟨?_, fun v => ?_⟩
  · rw [fromBlocks_transpose, hQ, hR, transpose_transpose]
  · have hv : v = Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) := by
      funext i; rcases i with i | i <;> rfl
    rw [hv, L.quad_joint]
    exact h _ _

/-- Hall's problem (Exercise 9.4) with state `x = [1, a, y]'`, control `c`, shock `ε`. -/
noncomputable def hallProblem (b μ Rr ρ σ β : ℝ) : LSProblem (Fin 3) (Fin 1) (Fin 1) where
  A := !![1, 0, 0; 0, Rr, 1; μ * (1 - ρ), 0, ρ]
  B := !![0; -1; 0]
  C := !![0; 0; σ]
  Q := !![b ^ 2, 0, 0; 0, 0, 0; 0, 0, 0]
  R := 1
  S := !![-b; 0; 0]
  β := β

variable (b μ Rr ρ σ β : ℝ)

/-- Exercise 9.4: the loss of `x = [1, a, y]'`, `c` is `(c − b)²`. -/
theorem ex_9_4_loss (a y c : ℝ) :
    (hallProblem b μ Rr ρ σ β).loss ![1, a, y] ![c] = (c - b) ^ 2 := by
  simp [LSProblem.loss, hallProblem, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Exercise 9.4: the transition `[1, a, y] ↦ [1, Ra + y − c, μ(1 − ρ) + ρy + σε]`. -/
theorem ex_9_4_transition (a y c e : ℝ) :
    (hallProblem b μ Rr ρ σ β).A *ᵥ ![1, a, y] + (hallProblem b μ Rr ρ σ β).B *ᵥ ![c] +
        (hallProblem b μ Rr ρ σ β).C *ᵥ ![e] =
      ![1, Rr * a + y - c, μ * (1 - ρ) + ρ * y + σ * e] := by
  funext i
  fin_cases i <;> simp [hallProblem] <;> ring

theorem ex_9_4_jointPSD : (hallProblem b μ Rr ρ σ β).JointPSD := by
  refine ls_jointPSD_of_loss _ ?_ ?_ fun x u => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hallProblem]
  · simp [hallProblem]
  · have : (hallProblem b μ Rr ρ σ β).loss x u = (u 0 - b * x 0) ^ 2 := by
      simp [LSProblem.loss, hallProblem, mulVec, dotProduct, Fin.sum_univ_three]
      ring
    rw [this]
    positivity

/-- `q = 1 − 1/(βR²)`. -/
noncomputable def hallq : ℝ := 1 - 1 / (β * Rr ^ 2)

/-- `w = [μR/(R − 1) − μR/(R − ρ) − bR/(R − 1), R, R/(R − ρ)]`. -/
noncomputable def hallW : Fin 3 → ℝ :=
  ![μ * Rr / (Rr - 1) - μ * Rr / (Rr - ρ) - b * Rr / (Rr - 1), Rr, Rr / (Rr - ρ)]

/-- The Riccati solution `P = q ww'`. -/
noncomputable def hallP : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => hallq Rr β * hallW b μ Rr ρ i * hallW b μ Rr ρ j

/-- The gain `F = −(b e₁' + q w')`. -/
noncomputable def hallF : Matrix (Fin 1) (Fin 3) ℝ :=
  Matrix.of fun _ j => -(![b, 0, 0] j + hallq Rr β * hallW b μ Rr ρ j)

variable {b μ Rr ρ σ β}

theorem hallP_quad (x : Fin 3 → ℝ) :
    x ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x) = hallq Rr β * (hallW b μ Rr ρ ⬝ᵥ x) ^ 2 := by
  simp only [hallP, dotProduct, mulVec, of_apply, Fin.sum_univ_three]
  ring

/-- **Exercise 9.4** (Miao, p. 325): for `β > 0`, `R > 1` and `|ρ| < 1`, `P = q ww'` solves
the Riccati equation (9.12) and the gain (9.17) is `F = −(b e₁' + q w')`. -/
theorem ex_9_4_riccati (hβ : 0 < β) (hR1 : 1 < Rr) (hρ : |ρ| < 1) :
    (hallProblem b μ Rr ρ σ β).T (hallP b μ Rr ρ β) = hallP b μ Rr ρ β ∧
      (hallProblem b μ Rr ρ σ β).F (hallP b μ Rr ρ β) = hallF b μ Rr ρ β ∧
      ((hallProblem b μ Rr ρ σ β).G (hallP b μ Rr ρ β)).PosDef := by
  set L := hallProblem b μ Rr ρ σ β
  have hR1' : Rr - 1 ≠ 0 := by linarith
  have hRρ : Rr - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  have hκ0 : β * Rr ^ 2 ≠ 0 := by positivity
  have hRr : Rr ≠ 0 := by linarith
  have hGe : L.G (hallP b μ Rr ρ β) = !![β * Rr ^ 2] := by
    ext i j
    fin_cases i; fin_cases j
    simp [L, LSProblem.G, hallProblem, hallP, hallq, hallW, Matrix.mul_apply, Fin.sum_univ_three]
    field_simp
    ring
  have hGpd : (L.G (hallP b μ Rr ρ β)).PosDef := by
    rw [hGe]
    refine SS.LQProblem.posDef_iff_real.2 ⟨by ext i j; fin_cases i; fin_cases j; rfl,
      fun v hv => ?_⟩
    have hv0 : v 0 ≠ 0 := fun h0 => hv (funext fun i => by fin_cases i; exact h0)
    simp only [dotProduct, mulVec, Fin.sum_univ_one, of_apply, cons_val', cons_val_fin_one,
      empty_val']
    have : 0 < v 0 * v 0 := mul_self_pos.2 hv0
    nlinarith [mul_pos (by positivity : 0 < β * Rr ^ 2) this]
  have hu := (isUnit_iff_isUnit_det _).1 hGpd.isUnit
  have hGF : L.G (hallP b μ Rr ρ β) * hallF b μ Rr ρ β = L.N (hallP b μ Rr ρ β) := by
    rw [hGe]
    ext i j
    fin_cases i; fin_cases j <;>
      simp [L, LSProblem.N, hallProblem, hallP, hallF, hallq, hallW, Matrix.mul_apply,
        Fin.sum_univ_three] <;> field_simp <;> ring
  have hF : L.F (hallP b μ Rr ρ β) = hallF b μ Rr ρ β := by
    rw [LSProblem.F, ← hGF, nonsing_inv_mul_cancel_left _ _ hu]
  refine ⟨?_, hF, hGpd⟩
  rw [LSProblem.T_eq_sub, hF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L, hallProblem, hallP, hallF, hallq, hallW, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

/-- **Exercise 9.4**, the consumption rule `c = −Fx` at `x = [1, a, y]'`:
`c = b + q(Ra + Ry/(R − ρ) + μR/(R − 1) − μR/(R − ρ) − bR/(R − 1))`. -/
theorem ex_9_4_rule (a y : ℝ) :
    (-(hallF b μ Rr ρ β *ᵥ ![1, a, y])) 0 = b + hallq Rr β *
      (Rr * a + Rr * y / (Rr - ρ) + μ * Rr / (Rr - 1) - μ * Rr / (Rr - ρ) -
        b * Rr / (Rr - 1)) := by
  simp [hallF, hallW, vecHead, vecTail]
  ring

/-- **Exercise 9.4**, Hall's case `βR = 1`: `c_t = (R − 1)a_t + μ + (R − 1)(y_t − μ)/(R − ρ)`;
consumption is a martingale (`ex_9_4_closed_loop`). -/
theorem ex_9_4_martingale (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hβR : β * Rr = 1) (a y : ℝ) :
    (-(hallF b μ Rr ρ β *ᵥ ![1, a, y])) 0 = (Rr - 1) * a + μ + (Rr - 1) * (y - μ) / (Rr - ρ) := by
  have hR1' : Rr - 1 ≠ 0 := by linarith
  have hRρ : Rr - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  have hRr : Rr ≠ 0 := by linarith
  have hβ : β = 1 / Rr := by field_simp; linarith
  rw [ex_9_4_rule, hallq, hβ]
  field_simp
  ring

/-- **Exercise 9.4**: along the rule, `w'x_{t+1} = (βR)⁻¹w'x_t`, i.e.
`c_{t+1} − b = (βR)⁻¹(c_t − b)` (the Euler equation). -/
theorem ex_9_4_closed_loop (hβ : 0 < β) (hR1 : 1 < Rr) (hρ : |ρ| < 1) (x : Fin 3 → ℝ) :
    hallW b μ Rr ρ ⬝ᵥ (((hallProblem b μ Rr ρ σ β).A - (hallProblem b μ Rr ρ σ β).B *
      hallF b μ Rr ρ β) *ᵥ x) = (β * Rr)⁻¹ * (hallW b μ Rr ρ ⬝ᵥ x) := by
  have hR1' : Rr - 1 ≠ 0 := by linarith
  have hRρ : Rr - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  have hRr : Rr ≠ 0 := by linarith
  have hβ0 : β ≠ 0 := hβ.ne'
  simp [hallProblem, hallF, hallW, hallq, mulVec, dotProduct, Fin.sum_univ_three]
  field_simp
  ring

/-- **Exercise 9.4**, optimality in the deterministic problem (`ε = 0`): for `βR² > 1`, every plan
`x_{t+1} = Ax_t + Bc_t` with `βᵗx_t'Px_t → 0` and summable losses has
`∑βᵗ(c_t − b)² ≥ x₀'Px₀`, and the rule `c_t = −Fx_t` attains `x₀'Px₀`. -/
theorem ex_9_4_optimal (hβ : 0 < β) (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) :
    (∀ (x : ℕ → Fin 3 → ℝ) (c : ℕ → Fin 1 → ℝ),
      (∀ t, x (t + 1) = (hallProblem b μ Rr ρ σ β).A *ᵥ x t +
        (hallProblem b μ Rr ρ σ β).B *ᵥ c t) →
      Tendsto (fun s => β ^ s * (x s ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x s))) atTop (𝓝 0) →
      Summable (fun t => β ^ t * (hallProblem b μ Rr ρ σ β).loss (x t) (c t)) →
      x 0 ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x 0) ≤
        ∑' t, β ^ t * (hallProblem b μ Rr ρ σ β).loss (x t) (c t)) ∧
    ∀ x : ℕ → Fin 3 → ℝ, (∀ t, x (t + 1) = ((hallProblem b μ Rr ρ σ β).A -
        (hallProblem b μ Rr ρ σ β).B * hallF b μ Rr ρ β) *ᵥ x t) →
      HasSum (fun t => β ^ t * (hallProblem b μ Rr ρ σ β).loss (x t)
        (-(hallF b μ Rr ρ β *ᵥ x t))) (x 0 ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x 0)) := by
  set L := hallProblem b μ Rr ρ σ β
  obtain ⟨hfix, hF, hG⟩ := ex_9_4_riccati (σ := σ) hβ hR1 hρ
  have hPs : (hallP b μ Rr ρ β)ᵀ = hallP b μ Rr ρ β := by
    ext i j
    simp only [hallP, transpose_apply, of_apply]
    ring
  have hRs : L.Rᵀ = L.R := by simp [L, hallProblem]
  have hJ := ex_9_4_jointPSD b μ Rr ρ σ β
  refine ⟨fun x c hx hlim hs => ?_, fun x hx => ?_⟩
  · exact (L.ls_verification hJ hRs hPs hG hβ.le hfix hx).2.1 hlim hs
  · have hx' : ∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ (-(hallF b μ Rr ρ β *ᵥ x t)) := fun t => by
      rw [hx, sub_mulVec, mulVec_neg, ← mulVec_mulVec, sub_eq_add_neg]
    have hw : ∀ t, hallW b μ Rr ρ ⬝ᵥ x t = (β * Rr)⁻¹ ^ t * (hallW b μ Rr ρ ⬝ᵥ x 0) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [hx, ex_9_4_closed_loop hβ hR1 hρ, ih, pow_succ]; ring
    have hlim : Tendsto (fun s => β ^ s * (x s ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x s))) atTop (𝓝 0) := by
      have hr0 : 0 ≤ (β * Rr ^ 2)⁻¹ := by positivity
      have hr1 : (β * Rr ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hκ
      have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const
        (hallq Rr β * (hallW b μ Rr ρ ⬝ᵥ x 0) ^ 2)
      rw [zero_mul] at h0
      refine h0.congr fun s => ?_
      rw [hallP_quad, hw s]
      have hRr : Rr ≠ 0 := by linarith
      have hβ0 : β ≠ 0 := hβ.ne'
      have hb : (β * Rr ^ 2)⁻¹ = β * ((β * Rr)⁻¹) ^ 2 := by field_simp
      rw [hb, mul_pow, ← pow_mul, pow_mul']
      ring
    exact (L.ls_verification hJ hRs hPs hG hβ.le hfix hx').2.2 (fun t => by rw [hF]) hlim

/-- **Exercise 9.4** with shocks (certainty equivalence): for `0 < β < 1` and `βR² > 1`,
`V(x) = −x'Px − d`, `d = (1 − β)⁻¹β tr(PCC')`, solves the Bellman equation, and the rule
`c = −Fx` is the unique maximiser. -/
theorem ex_9_4_bellman {ν : Measure (Fin 1 → ℝ)} (hν : LSShockLaw ν) (hβ : 0 < β)
    (hβ1 : β < 1) (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) (x : Fin 3 → ℝ) :
    IsGreatest (Set.range ((hallProblem b μ Rr ρ σ β).bellObj ν
        (fun z => -(z ⬝ᵥ (hallP b μ Rr ρ β *ᵥ z)) - (1 - β)⁻¹ *
          (β * trace (hallP b μ Rr ρ β * (hallProblem b μ Rr ρ σ β).C *
            (hallProblem b μ Rr ρ σ β).Cᵀ))) x))
        (-(x ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x)) - (1 - β)⁻¹ *
          (β * trace (hallP b μ Rr ρ β * (hallProblem b μ Rr ρ σ β).C *
            (hallProblem b μ Rr ρ σ β).Cᵀ))) ∧
      ∀ u, (hallProblem b μ Rr ρ σ β).bellObj ν
          (fun z => -(z ⬝ᵥ (hallP b μ Rr ρ β *ᵥ z)) - (1 - β)⁻¹ *
            (β * trace (hallP b μ Rr ρ β * (hallProblem b μ Rr ρ σ β).C *
              (hallProblem b μ Rr ρ σ β).Cᵀ))) x u =
          -(x ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x)) - (1 - β)⁻¹ *
            (β * trace (hallP b μ Rr ρ β * (hallProblem b μ Rr ρ σ β).C *
              (hallProblem b μ Rr ρ σ β).Cᵀ)) ↔ u = -(hallF b μ Rr ρ β *ᵥ x) := by
  obtain ⟨hfix, hF, -⟩ := ex_9_4_riccati (σ := σ) hβ hR1 hρ
  have hq : 0 < hallq Rr β := by
    rw [hallq, sub_pos, div_lt_one (by positivity)]
    exact hκ
  have hP : (hallP b μ Rr ρ β).PosSemidef := by
    refine SS.LQProblem.posSemidef_iff_real.2 ⟨?_, fun v => ?_⟩
    · ext i j
      simp only [hallP, transpose_apply, of_apply]
      ring
    · rw [hallP_quad]
      positivity
  have hR : (hallProblem b μ Rr ρ σ β).R.PosDef := by
    simpa [hallProblem] using (PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef)
  have h := (hallProblem b μ Rr ρ σ β).eq_9_16_9_17 hν hR hβ.le hβ1 hP hfix x
  rw [hF] at h
  exact h

/-- **Exercise 9.4**, a second solution: `P = 0` always solves (9.12) for Hall's problem, with
rule `c = b` (the loss `0` is then attained, financed by debt growing at rate `R`, which the
side condition (9.10) permits iff `βR² < 1`). So for `βR² > 1` the Riccati equation has two
positive semidefinite solutions (`Q − SR⁻¹S' = 0`, so the detectability of Proposition 9.3.2
fails), and the side condition selects `P = q ww'`. -/
theorem ex_9_4_zero_solution (a y : ℝ) :
    (hallProblem b μ Rr ρ σ β).T 0 = 0 ∧
      (-((hallProblem b μ Rr ρ σ β).F 0 *ᵥ ![1, a, y])) 0 = b := by
  have hG : (hallProblem b μ Rr ρ σ β).G 0 = 1 := by simp [LSProblem.G, hallProblem]
  refine ⟨?_, ?_⟩
  · rw [LSProblem.T, hG, inv_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hallProblem, LSProblem.N, vecMul, dotProduct]
    all_goals ring
  · rw [LSProblem.F, hG, inv_one, Matrix.one_mul]
    simp [hallProblem, LSProblem.N, mulVec, dotProduct, Fin.sum_univ_three]

/-- For `βR² > 1` the two solutions differ: `P = q ww' ≠ 0`. -/
theorem ex_9_4_two_solutions (hβ : 0 < β) (hR1 : 1 < Rr) (hκ : 1 < β * Rr ^ 2) :
    hallP b μ Rr ρ β ≠ 0 := by
  intro h
  have h11 := congrFun (congrFun h 1) 1
  have hq : 0 < hallq Rr β := by
    rw [hallq, sub_pos, div_lt_one (by positivity)]
    exact hκ
  have hRr : Rr ≠ 0 := by linarith
  have h11' : hallP b μ Rr ρ β 1 1 = hallq Rr β * Rr * Rr := by simp [hallP, hallW]
  rw [h11'] at h11
  exact mul_ne_zero (mul_ne_zero hq.ne' hRr) hRr h11

end Miao.LinearQuadratic

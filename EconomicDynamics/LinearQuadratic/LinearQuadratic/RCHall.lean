/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.RCExercise3
import LinearQuadratic.LSHall

/-!
# Exercise 9.5: the robust consumption rule

Miao, §9.7, Exercise 9.5, p. 326: the multiplier problem for Hall's consumption-saving problem
(Exercise 9.4), `max −E∑βᵗ(c_t − b)²`, `c_t + a_{t+1} = Ra_t + y_t`,
`y_{t+1} = μ(1 − ρ) + ρy_t + σε_{t+1}`, state `x = [1, a, y]'`. In the normalisation of §9.6,
`r = −½(x'Qx + u'Ru + 2x'Su) = −(c − b)²` (`rcHallRobust`: Hall's `Q, R, S` doubled;
`ex_9_5_loss`; the transition is that of Exercise 9.4, `ex_9_5_data`).

With `κ = βR² > 1`, `w = [μR/(R − 1) − μR/(R − ρ) − bR/(R − 1), R, R/(R − ρ)]` (`hallW`, the vector
of Exercise 9.4), `k = σ²R²/(R − ρ)² = (w'C)²` (`rcHallK`) and `θ > 2k`:

* `ex_9_5`: `P = 2q_θ ww'` with `q_θ = θ(κ − 1)/(θκ − 2k)` (`rcHallQθ`, `rcHallPθ`) solves the
  robust Riccati equation `P = T(D(P))` (9.53), with `θ − C'PC > 0` and `D(P) = θP/(θ − 2q_θk)`
  (rank one in the same direction); the robust gain (9.52) is `F = −(be₁' + q_θw')`.
* `ex_9_5_rule`: the robust consumption rule
  `c_t = b + q_θ(Ra_t + Ry_t/(R − ρ) + μR/(R − 1) − μR/(R − ρ) − bR/(R − 1))`; in Hall's case
  `βR = 1`, `q_θ = θ(R − 1)/(θR − 2k)` (`ex_9_5_hall_case`).
* `ex_9_5_bellman`: with Gaussian shocks and `β < 1`, `V(x) = −½x'Px − d/2` with (9.55) solves the
  robust Bellman equation, and the rule is the unique maximiser.
* `ex_9_5_limit`: `q_θ → q = 1 − 1/(βR²)` as `θ → ∞` (the rule of Exercise 9.4, cf. Exercise 9.3);
  `ex_9_5_more_responsive`: for `σ ≠ 0`, `q_θ > q`: the robust consumer's consumption responds more
  to wealth.
* `ex_9_5_breakdown`: the breakdown point is `θ = 2k`: on the robust solution
  `θ − C'PC = θκ(θ − 2k)/(θκ − 2k)`.
-/

open Matrix Filter Topology

namespace Miao.LinearQuadratic

/-- Hall's problem in the normalisation of §9.6: `−½(x'Qx + u'Ru + 2x'Su) = −(c − b)²`. -/
noncomputable def rcHallRobust (b μ Rr ρ σ β : ℝ) : LSProblem (Fin 3) (Fin 1) (Fin 1) where
  A := !![1, 0, 0; 0, Rr, 1; μ * (1 - ρ), 0, ρ]
  B := !![0; -1; 0]
  C := !![0; 0; σ]
  Q := !![2 * b ^ 2, 0, 0; 0, 0, 0; 0, 0, 0]
  R := !![2]
  S := !![-2 * b; 0; 0]
  β := β

/-- `k = σ²R²/(R − ρ)²`. -/
noncomputable def rcHallK (Rr ρ σ : ℝ) : ℝ := σ ^ 2 * (Rr / (Rr - ρ)) ^ 2

/-- `q_θ = θ(βR² − 1)/(θβR² − 2k)`. -/
noncomputable def rcHallQθ (Rr ρ σ β θ : ℝ) : ℝ :=
  θ * (β * Rr ^ 2 - 1) / (θ * (β * Rr ^ 2) - 2 * rcHallK Rr ρ σ)

/-- A rank-one matrix `p ww'`. -/
noncomputable def rcHallRank1 (b μ Rr ρ p : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => p * hallW b μ Rr ρ i * hallW b μ Rr ρ j

/-- The robust Riccati solution `P = 2q_θ ww'`. -/
noncomputable def rcHallPθ (b μ Rr ρ σ β θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rcHallRank1 b μ Rr ρ (2 * rcHallQθ Rr ρ σ β θ)

/-- The gain `−(be₁' + q w')`. -/
noncomputable def rcHallGain (b μ Rr ρ q : ℝ) : Matrix (Fin 1) (Fin 3) ℝ :=
  Matrix.of fun _ j => -(![b, 0, 0] j + q * hallW b μ Rr ρ j)

variable (b μ Rr ρ σ β : ℝ)

/-- Exercise 9.5: `−½ loss = −(c − b)²` at `x = [1, a, y]'`, `u = c`. -/
theorem ex_9_5_loss (a y c : ℝ) :
    -(1 / 2) * (rcHallRobust b μ Rr ρ σ β).loss ![1, a, y] ![c] = -(c - b) ^ 2 := by
  simp [LSProblem.loss, rcHallRobust, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Exercise 9.5: the transition is that of Exercise 9.4. -/
theorem ex_9_5_data :
    (rcHallRobust b μ Rr ρ σ β).A = (hallProblem b μ Rr ρ σ β).A ∧
      (rcHallRobust b μ Rr ρ σ β).B = (hallProblem b μ Rr ρ σ β).B ∧
      (rcHallRobust b μ Rr ρ σ β).C = (hallProblem b μ Rr ρ σ β).C ∧
      (rcHallRobust b μ Rr ρ σ β).β = β :=
  ⟨rfl, rfl, rfl, rfl⟩

variable {b μ Rr ρ σ β}

/-- The Riccati operator and gain on rank-one matrices `pww'`, parametrised by
`g = s/(2 + s)`, `s = βR²p` (so `p = 2g/(βR²(1 − g))`): `G = 2/(1 − g)`,
`F(pww') = −(be₁' + gw')` and `T(pww') = 2g ww'`. -/
theorem rc_hall_rank1_T (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : β * Rr ^ 2 ≠ 0) {g : ℝ} (hg : g ≠ 1) :
    (rcHallRobust b μ Rr ρ σ β).G (rcHallRank1 b μ Rr ρ (2 * g / (β * Rr ^ 2 * (1 - g)))) =
        !![2 / (1 - g)] ∧
      (rcHallRobust b μ Rr ρ σ β).F (rcHallRank1 b μ Rr ρ (2 * g / (β * Rr ^ 2 * (1 - g)))) =
        rcHallGain b μ Rr ρ g ∧
      (rcHallRobust b μ Rr ρ σ β).T (rcHallRank1 b μ Rr ρ (2 * g / (β * Rr ^ 2 * (1 - g)))) =
        rcHallRank1 b μ Rr ρ (2 * g) := by
  set L := rcHallRobust b μ Rr ρ σ β
  have hg' : 1 - g ≠ 0 := sub_ne_zero.2 (Ne.symm hg)
  have hβ0 : β ≠ 0 := fun h => hκ (by rw [h, zero_mul])
  have hR1' : Rr - 1 ≠ 0 := by linarith
  have hRr : Rr ≠ 0 := by linarith
  have hRρ : Rr - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  set P := rcHallRank1 b μ Rr ρ (2 * g / (β * Rr ^ 2 * (1 - g)))
  have hGe : L.G P = !![2 / (1 - g)] := by
    ext i j
    fin_cases i; fin_cases j
    simp [L, P, LSProblem.G, rcHallRobust, rcHallRank1, hallW, Matrix.mul_apply, Fin.sum_univ_three]
    field_simp
    ring
  have hu : IsUnit (L.G P).det := by
    rw [hGe, det_fin_one_of]
    exact (div_ne_zero two_ne_zero hg').isUnit
  have hGF : L.G P * rcHallGain b μ Rr ρ g = L.N P := by
    rw [hGe]
    ext i j
    fin_cases i; fin_cases j <;>
      simp [L, P, LSProblem.N, rcHallRobust, rcHallRank1, rcHallGain, hallW, Matrix.mul_apply,
        Fin.sum_univ_three] <;> field_simp <;> ring
  have hF : L.F P = rcHallGain b μ Rr ρ g := by
    rw [LSProblem.F, ← hGF, nonsing_inv_mul_cancel_left _ _ hu]
  refine ⟨hGe, hF, ?_⟩
  rw [LSProblem.T_eq_sub, hF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L, P, rcHallRobust, rcHallRank1, rcHallGain, hallW, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    field_simp <;> ring

/-- `θ − C'(pww')C = θ − pk` and `D(pww') = (θp/(θ − pk))ww'`. -/
theorem rc_hall_rank1_D {θ p : ℝ} (hθp : θ - p * rcHallK Rr ρ σ ≠ 0) :
    rcH θ (rcHallRobust b μ Rr ρ σ β).C (rcHallRank1 b μ Rr ρ p) = !![θ - p * rcHallK Rr ρ σ] ∧
      rcD θ (rcHallRobust b μ Rr ρ σ β).C (rcHallRank1 b μ Rr ρ p) =
        rcHallRank1 b μ Rr ρ (θ * p / (θ - p * rcHallK Rr ρ σ)) := by
  have hk : rcHallK Rr ρ σ = σ ^ 2 * hallW b μ Rr ρ 2 ^ 2 := by simp [rcHallK, hallW]
  rw [hk] at hθp ⊢
  have hθp' : -(p * hallW b μ Rr ρ 2 ^ 2 * σ ^ 2) + θ ≠ 0 := by
    intro h; apply hθp; linarith
  have hH : rcH θ (rcHallRobust b μ Rr ρ σ β).C (rcHallRank1 b μ Rr ρ p) =
      !![θ - p * (σ ^ 2 * hallW b μ Rr ρ 2 ^ 2)] := by
    ext i j
    fin_cases i; fin_cases j
    simp [rcH, rcHallRobust, rcHallRank1, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  refine ⟨hH, ?_⟩
  set t := (θ - p * (σ ^ 2 * hallW b μ Rr ρ 2 ^ 2))⁻¹ with htdef
  have ht : t * (θ - p * (σ ^ 2 * hallW b μ Rr ρ 2 ^ 2)) = 1 := inv_mul_cancel₀ hθp
  rw [rcD, hH, rc_inv_fin_one, ← htdef, div_eq_mul_inv, ← htdef]
  ext i j
  simp [rcHallRobust, rcHallRank1, Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination (-(p * hallW b μ Rr ρ i * hallW b μ Rr ρ j)) * ht

/-- The breakdown point of Exercise 9.5: on `P = 2q_θww'`,
`θ − C'PC = θκ(θ − 2k)/(θκ − 2k)`, `κ = βR²`; positive iff `θ > 2k` (given `κ > 1`). -/
theorem ex_9_5_breakdown {θ : ℝ} (hden : θ * (β * Rr ^ 2) - 2 * rcHallK Rr ρ σ ≠ 0) :
    θ - 2 * rcHallQθ Rr ρ σ β θ * rcHallK Rr ρ σ =
      θ * (β * Rr ^ 2) * (θ - 2 * rcHallK Rr ρ σ) / (θ * (β * Rr ^ 2) - 2 * rcHallK Rr ρ σ) := by
  rw [rcHallQθ]
  generalize hD : θ * (β * Rr ^ 2) - 2 * rcHallK Rr ρ σ = D at hden ⊢
  field_simp
  subst hD
  ring

/-- **Exercise 9.5** (Miao, p. 326): for `R > 1`, `|ρ| < 1`, `κ = βR² > 1` and
`θ > 2k`, `P = 2q_θww'` is positive semidefinite with `θ − C'PC > 0` and solves the robust
Riccati equation `P = T(D(P))` (9.53), and the robust gain (9.52) is `F = −(be₁' + q_θw')`. -/
theorem ex_9_5 (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) {θ : ℝ}
    (hθ : 2 * rcHallK Rr ρ σ < θ) :
    (rcHallPθ b μ Rr ρ σ β θ).PosSemidef ∧
      (rcH θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)).PosDef ∧
      (rcHallRobust b μ Rr ρ σ β).T
          (rcD θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) =
        rcHallPθ b μ Rr ρ σ β θ ∧
      (rcHallRobust b μ Rr ρ σ β).F
          (rcD θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) =
        rcHallGain b μ Rr ρ (rcHallQθ Rr ρ σ β θ) := by
  set k := rcHallK Rr ρ σ with hk
  set κ := β * Rr ^ 2 with hκdef
  have hk0 : 0 ≤ k := by simp only [k, rcHallK]; positivity
  have hθ0 : 0 < θ := by linarith
  have hden : 0 < θ * κ - 2 * k := by nlinarith
  set q := rcHallQθ Rr ρ σ β θ with hq
  have hqpos : 0 < q := by
    simp only [q, rcHallQθ, ← hκdef, ← hk]
    exact div_pos (mul_pos hθ0 (by linarith)) hden
  have hH0 : 0 < θ - 2 * q * k := by
    have h := ex_9_5_breakdown (σ := σ) (θ := θ) (β := β) (Rr := Rr) (ρ := ρ) hden.ne'
    rw [← hκdef, ← hk] at h
    rw [h]
    exact div_pos (mul_pos (mul_pos hθ0 (by linarith)) (by linarith)) hden
  obtain ⟨hH, hD⟩ := rc_hall_rank1_D (b := b) (μ := μ) (β := β) (θ := θ) (p := 2 * q) hH0.ne'
  have hq1 : 0 < 1 - q := by
    have : 1 - q = (θ - 2 * k) / (θ * κ - 2 * k) := by
      simp only [q, rcHallQθ, ← hκdef, ← hk]
      field_simp
      ring
    rw [this]
    exact div_pos (by linarith) hden
  have hκ0 : κ ≠ 0 := by linarith
  have hpt : θ * (2 * q) / (θ - 2 * q * k) = 2 * q / (κ * (1 - q)) := by
    have h := ex_9_5_breakdown (σ := σ) (θ := θ) (β := β) (Rr := Rr) (ρ := ρ) hden.ne'
    rw [← hκdef, ← hk] at h
    rw [h]
    have h1 : 1 - q = (θ - 2 * k) / (θ * κ - 2 * k) := by
      simp only [q, rcHallQθ, ← hκdef, ← hk]
      field_simp
      ring
    rw [h1]
    have h2 : θ - 2 * k ≠ 0 := by linarith
    field_simp
  obtain ⟨-, hF, hT⟩ := rc_hall_rank1_T (b := b) (μ := μ) (σ := σ) (β := β) hR1 hρ hκ0
    (g := q) (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine SS.LQProblem.posSemidef_iff_real.2 ⟨?_, fun x => ?_⟩
    · ext i j
      simp only [rcHallPθ, rcHallRank1, transpose_apply, of_apply]
      ring
    · have : x ⬝ᵥ (rcHallPθ b μ Rr ρ σ β θ *ᵥ x) = 2 * q * (hallW b μ Rr ρ ⬝ᵥ x) ^ 2 := by
        simp only [rcHallPθ, rcHallRank1, dotProduct, mulVec, of_apply, Fin.sum_univ_three]
        ring
      rw [this]
      positivity
  · rw [rcHallPθ, hH]
    refine SS.LQProblem.posDef_iff_real.2 ⟨by ext i j; fin_cases i; fin_cases j; rfl,
      fun v hv => ?_⟩
    have hv0 : v 0 ≠ 0 := fun h0 => hv (funext fun i => by fin_cases i; exact h0)
    simp only [dotProduct, mulVec, Fin.sum_univ_one, of_apply, cons_val', cons_val_fin_one,
      empty_val']
    have : 0 < v 0 * v 0 := mul_self_pos.2 hv0
    nlinarith
  · rw [rcHallPθ, hD, hpt, hT]
  · rw [rcHallPθ, hD, hpt, hF]

/-- **Exercise 9.5**, the robust consumption rule `c = −Fx` at `x = [1, a, y]'`:
`c = b + q_θ(Ra + Ry/(R − ρ) + μR/(R − 1) − μR/(R − ρ) − bR/(R − 1))`. -/
theorem ex_9_5_rule (θ a y : ℝ) :
    (-(rcHallGain b μ Rr ρ (rcHallQθ Rr ρ σ β θ) *ᵥ ![1, a, y])) 0 = b + rcHallQθ Rr ρ σ β θ *
      (Rr * a + Rr * y / (Rr - ρ) + μ * Rr / (Rr - 1) - μ * Rr / (Rr - ρ) -
        b * Rr / (Rr - 1)) := by
  simp [rcHallGain, hallW, vecHead, vecTail]
  ring

/-- **Exercise 9.5**, Hall's case `βR = 1`: `q_θ = θ(R − 1)/(θR − 2k)`. -/
theorem ex_9_5_hall_case (hβR : β * Rr = 1) (θ : ℝ) :
    rcHallQθ Rr ρ σ β θ = θ * (Rr - 1) / (θ * Rr - 2 * rcHallK Rr ρ σ) := by
  have h : β * Rr ^ 2 = Rr := by rw [pow_two, ← mul_assoc, hβR, one_mul]
  rw [rcHallQθ, h]

/-- **Exercise 9.5**, the robust Bellman equation: with Gaussian shocks and `0 < β < 1`,
`V(x) = −½x'Px − d/2` (`P = 2q_θww'`, `d` from (9.55)) solves the robust Bellman equation (9.49),
and the robust consumption rule is its unique maximiser. -/
theorem ex_9_5_bellman {ν : MeasureTheory.Measure (Fin 1 → ℝ)} (hν : RCGaussian ν) (hβ : 0 < β)
    (hβ1 : β < 1) (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) {θ : ℝ}
    (hθ : 2 * rcHallK Rr ρ σ < θ) (x : Fin 3 → ℝ) :
    IsGreatest (Set.range (rcRobObj (rcHallRobust b μ Rr ρ σ β) ν θ (rcHallPθ b μ Rr ρ σ β θ)
        (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x))
        (rcV (rcHallPθ b μ Rr ρ σ β θ)
          (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x) ∧
      ∀ u, rcRobObj (rcHallRobust b μ Rr ρ σ β) ν θ (rcHallPθ b μ Rr ρ σ β θ)
          (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x u =
          rcV (rcHallPθ b μ Rr ρ σ β θ)
            (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x ↔
        u = -(rcHallGain b μ Rr ρ (rcHallQθ Rr ρ σ β θ) *ᵥ x) := by
  obtain ⟨hP, hH, hfix, hF⟩ := ex_9_5 (b := b) (μ := μ) hR1 hρ hκ hθ
  have hR : (rcHallRobust b μ Rr ρ σ β).R.PosDef := by
    refine SS.LQProblem.posDef_iff_real.2 ⟨by ext i j; fin_cases i; fin_cases j; rfl,
      fun v hv => ?_⟩
    have hv0 : v 0 ≠ 0 := fun h0 => hv (funext fun i => by fin_cases i; exact h0)
    simp only [rcHallRobust, dotProduct, mulVec, Fin.sum_univ_one, of_apply, cons_val',
      cons_val_fin_one, empty_val']
    have : 0 < v 0 * v 0 := mul_self_pos.2 hv0
    nlinarith
  have hk0 : 0 ≤ rcHallK Rr ρ σ := by simp only [rcHallK]; positivity
  have hθ0 : 0 < θ := by linarith
  have h := eq_9_51_9_55 (rcHallRobust b μ Rr ρ σ β) hν hR hβ.le hβ1 hθ0 hP hH hfix x
  rw [hF] at h
  exact h

/-- **Exercise 9.5** and Exercise 9.3: `q_θ → q = 1 − 1/(βR²)` as `θ → ∞`, the rule of
Exercise 9.4. -/
theorem ex_9_5_limit (hκ : 1 < β * Rr ^ 2) :
    Tendsto (fun θ => rcHallQθ Rr ρ σ β θ) atTop (𝓝 (hallq Rr β)) := by
  have hκ0 : β * Rr ^ 2 ≠ 0 := by linarith
  have h : Tendsto (fun θ : ℝ => (β * Rr ^ 2 - 1) / (β * Rr ^ 2 - 2 * rcHallK Rr ρ σ * θ⁻¹))
      atTop (𝓝 ((β * Rr ^ 2 - 1) / (β * Rr ^ 2 - 2 * rcHallK Rr ρ σ * 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero (𝕜 := ℝ)))) (by simpa using hκ0)
  have hq : hallq Rr β = (β * Rr ^ 2 - 1) / (β * Rr ^ 2 - 2 * rcHallK Rr ρ σ * 0) := by
    rw [hallq, mul_zero, sub_zero, sub_div, div_self hκ0]
  rw [hq]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with θ hθ
  rw [rcHallQθ]
  field_simp

/-- **Exercise 9.5**: for `σ ≠ 0` the robust consumer's marginal propensity to consume out of
`w'x` exceeds the standard one, `q_θ > q = 1 − 1/(βR²)`. -/
theorem ex_9_5_more_responsive (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) (hσ : σ ≠ 0)
    {θ : ℝ} (hθ : 2 * rcHallK Rr ρ σ < θ) : hallq Rr β < rcHallQθ Rr ρ σ β θ := by
  have hRρ : Rr - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  have hk : 0 < rcHallK Rr ρ σ := by
    simp only [rcHallK]
    have : Rr / (Rr - ρ) ≠ 0 := div_ne_zero (by linarith) hRρ
    positivity
  have hθ0 : 0 < θ := by linarith
  have hden : 0 < θ * (β * Rr ^ 2) - 2 * rcHallK Rr ρ σ := by nlinarith
  rw [hallq, rcHallQθ, lt_div_iff₀ hden]
  have hκ0 : 0 < β * Rr ^ 2 := by linarith
  rw [one_sub_div hκ0.ne']
  rw [div_mul_eq_mul_div, div_lt_iff₀ hκ0]
  nlinarith

end Miao.LinearQuadratic

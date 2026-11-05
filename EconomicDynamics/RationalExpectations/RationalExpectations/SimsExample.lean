/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.Sims
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The Sims form (2.19) and Example 2.3.2

Miao, §2.3.3, pp. 58 and 64, continuing `Sims`.

* `IsSims19Solution`: the general form (2.19) `Γ₀y_t = Γ₁y_{t−1} + C + Ψz_t + Πη_t`;
  `isSims19_zero_iff` (`C = 0`, `z = ε` is (2.20)).
* The reductions of p. 58, as equivalences of solution sets: `eq_2_19_const` (`C = 0` by
  `y ↦ y − (Γ₀ − Γ₁)⁻¹C`, when `Γ₀ − Γ₁` is invertible; stability is preserved) and
  `eq_2_19_append` (appending `z_t = Φz_{t−1} + Σε_t` to `y_t`, so that `ε` replaces `z`).
* Example 2.3.2: the New Keynesian model (2.13)–(2.15) (`IsNKSolution`), the printed matrices
  (`ex232Γ₀`, `ex232Γ₁`, `ex232Ψ`, `ex232Pm`), `example_2_3_2_rows` and the equivalence of
  solution sets `example_2_3_2`.

**Corrections.**
* The change of variables "as in Example 2.1.1" needs `Γ₀ − Γ₁` invertible (the analogue of
  `1 − b ≠ 0`); otherwise the reduction to `C = 0` can fail (`eq_2_19_const_singular`).
* The matrices of Example 2.3.2 are correct as printed (every entry checked), with
  `y_t = (i_t, ξ^x_t, ξ^π_t, x_t, π_t)`, `ε_t = (ε_t, ε^x_t)`, `η_t = (η^x_t, η^π_t)`; the
  equivalence holds for `t ≥ 1` (the equations at `t` involve `y_{t−1}`).
-/

namespace Miao.RationalExpectations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### The general form (2.19) and its reduction to (2.20) -/

/-- Miao, (2.19), p. 58: `Γ₀y_t = Γ₁y_{t−1} + C + Ψz_t + Πη_t` (`t ≥ 1`) with `y`, `η`
adapted and `η` a martingale difference. The constant `C` is a vector of deterministic random
variables (`E₀C = C`). -/
def IsSims19Solution {n nz m : ℕ} (E : CondExpSystem ℂ V) (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ)
    (C : Fin n → V) (Ψ : Matrix (Fin n) (Fin nz) ℂ) (Pm : Matrix (Fin n) (Fin m) ℂ)
    (z : ℕ → Fin nz → V) (y : ℕ → Fin n → V) (η : ℕ → Fin m → V) : Prop :=
  IsAdaptedV E y ∧ IsAdaptedV E η ∧ IsMartingaleDiffProc E η ∧
    ∀ t, matAct Γ₀ (y (t + 1)) = matAct Γ₁ (y t) + C + matAct Ψ (z (t + 1)) +
      matAct Pm (η (t + 1))

/-- (2.19) with `C = 0` and `z = ε` is (2.20). -/
theorem isSims19_zero_iff {n nz m : ℕ} (E : CondExpSystem ℂ V)
    (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ) (Ψ : Matrix (Fin n) (Fin nz) ℂ)
    (Pm : Matrix (Fin n) (Fin m) ℂ) (z : ℕ → Fin nz → V) (y : ℕ → Fin n → V)
    (η : ℕ → Fin m → V) :
    IsSims19Solution E Γ₀ Γ₁ 0 Ψ Pm z y η ↔ IsSimsSolution E Γ₀ Γ₁ Ψ Pm z y η := by
  simp only [IsSims19Solution, IsSimsSolution, add_zero]

/-- Miao, p. 58 ("we may assume `C = 0` by appropriate change of variables as in Example
2.1.1"). If `Γ₀ − Γ₁` is invertible (`1` is not a generalized eigenvalue, the analogue of
`1 − b ≠ 0` in Example 2.1.1), put `ȳ = (Γ₀ − Γ₁)⁻¹C`. Then `(y, η)` solves (2.19) iff
`(y − ȳ, η)` solves (2.19) with `C = 0`, i.e. (2.20) with `z` in place of `ε`, and `y` is
stable iff `y − ȳ` is. Without the invertibility the reduction can fail
(`eq_2_19_const_singular`). -/
theorem eq_2_19_const {n nz m : ℕ} (E : CondExpSystem ℂ V) {Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ}
    (hdet : (Γ₀ - Γ₁).det ≠ 0) {C : Fin n → V} (hC : Evec E 0 C = C)
    (Ψ : Matrix (Fin n) (Fin nz) ℂ) (Pm : Matrix (Fin n) (Fin m) ℂ) (z : ℕ → Fin nz → V)
    (y : ℕ → Fin n → V) (η : ℕ → Fin m → V) :
    (IsSims19Solution E Γ₀ Γ₁ C Ψ Pm z y η ↔
      IsSimsSolution E Γ₀ Γ₁ Ψ Pm z (fun t => y t - matAct (Γ₀ - Γ₁)⁻¹ C) η) ∧
    (IsStableProc y ↔ IsStableProc fun t => y t - matAct (Γ₀ - Γ₁)⁻¹ C) := by
  set yb := matAct (Γ₀ - Γ₁)⁻¹ C with hyb
  have hyba : ∀ t, Evec E t yb = yb := fun t => by
    rw [hyb, Evec_matAct, ← hC, klS_Evec_tower_ge E (Nat.zero_le t)]
  have hCyb : matAct Γ₀ yb - matAct Γ₁ yb = C := by
    rw [← klS_sub_matAct, hyb, klS_matAct_mul_inv hdet]
  have hcst : IsStableProc fun _ : ℕ => yb := isStableProc_of_uniformly_bounded
    (M := ‖yb‖) fun _ i => norm_le_pi_norm yb i
  refine ⟨?_, ⟨fun h => klS_stable_sub h hcst, fun h => ?_⟩⟩
  · have hadapt : IsAdaptedV E y ↔ IsAdaptedV E fun t => y t - yb := by
      refine forall_congr' fun t => forall_congr' fun i => ?_
      have := congrFun (hyba t) i
      simp only [Evec] at this
      simp only [Pi.sub_apply, map_sub, this, sub_left_inj]
    refine and_congr hadapt (and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun t => ?_)))
    rw [klS_matAct_sub, klS_matAct_sub, ← hCyb]
    constructor
    · intro h
      rw [h]
      abel
    · intro h
      linear_combination (norm := module) h
  · simpa only [sub_add_cancel] using klS_stable_add h hcst

/-- **The reduction `C = 0` needs `Γ₀ − Γ₁` invertible** (Miao, p. 58). With `Γ₀ = Γ₁ = 1`,
`C = 1`, `Ψ = Π = 0` and `E_t = id`, (2.19) is `y_t = y_{t−1} + 1`, which has no stable
solution, while the system with `C = 0` has the stable solution `y = 0`
(`simsH_zero_solution`). -/
theorem eq_2_19_const_singular :
    ¬ ∃ (y : ℕ → Fin 1 → ℂ) (η : ℕ → Fin 1 → ℂ),
      IsSims19Solution klS_detSystem 1 1 (fun _ => 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 y η ∧
        IsStableProc y := by
  rintro ⟨y, η, ⟨-, -, -, h⟩, ⟨M, -, hM⟩⟩
  have hy : ∀ t, y t 0 = y 0 0 + t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := congrFun (h t) 0
      simp only [matAct_one, klS_zero_matAct, Pi.add_apply, Pi.zero_apply, add_zero] at this
      rw [this, ih]
      push_cast
      ring
  obtain ⟨t, ht⟩ := exists_nat_gt (M + ‖y 0 0‖)
  have h1 := hM t 0
  rw [hy t] at h1
  have h2 : (t : ℝ) ≤ ‖y 0 0 + t‖ + ‖y 0 0‖ := by
    have := norm_sub_le (y 0 0 + t) (y 0 0)
    rw [add_sub_cancel_left, Complex.norm_natCast] at this
    exact this
  linarith

/-- Miao, p. 58 ("we may append `z_t` to `y_t` and replace `z_t` in (2.19) with `ε_t`"). If
`z_t = Φz_{t−1} + Σε_t` as in (2.1), then `(y, z)` stacked solves (2.20) with
`Γ̃₀ = [[Γ₀, −Ψ], [0, I]]`, `Γ̃₁ = [[Γ₁, 0], [0, Φ]]`, `Ψ̃ = [[0], [Σ]]`, `Π̃ = [[Π], [0]]` and
shock `ε` iff `y` solves (2.19) (with `C = 0`) driven by `z`, `z` is adapted and `z` follows
(2.1). (`Sg` stands for `Σ`, a reserved token.) -/
theorem eq_2_19_append {n nz nε m : ℕ} (E : CondExpSystem ℂ V)
    (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ) (Ψ : Matrix (Fin n) (Fin nz) ℂ)
    (Pm : Matrix (Fin n) (Fin m) ℂ) (Φ : Matrix (Fin nz) (Fin nz) ℂ)
    (Sg : Matrix (Fin nz) (Fin nε) ℂ) (ε : ℕ → Fin nε → V) (y : ℕ → Fin n → V)
    (z : ℕ → Fin nz → V) (η : ℕ → Fin m → V) :
    IsSimsSolution E (simsBlk Γ₀ (-Ψ) 0 1) (simsBlk Γ₁ 0 0 Φ) (simsRows 0 Sg) (simsRows Pm 0)
        ε (fun t => Fin.append (y t) (z t)) η ↔
      IsSims19Solution E Γ₀ Γ₁ 0 Ψ Pm z y η ∧ IsAdaptedV E z ∧
        ∀ t, z (t + 1) = matAct Φ (z t) + matAct Sg (ε (t + 1)) := by
  have hadapt : IsAdaptedV E (fun t => Fin.append (y t) (z t)) ↔
      IsAdaptedV E y ∧ IsAdaptedV E z := by
    constructor
    · intro h
      exact ⟨fun t i => by simpa using h t (Fin.castAdd nz i),
        fun t i => by simpa using h t (Fin.natAdd n i)⟩
    · rintro ⟨h1, h2⟩ t i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using h1 t i
      · simpa using h2 t i
  have heq : ∀ t, (matAct (simsBlk Γ₀ (-Ψ) 0 1) (Fin.append (y (t + 1)) (z (t + 1))) =
      matAct (simsBlk Γ₁ 0 0 Φ) (Fin.append (y t) (z t)) + matAct (simsRows 0 Sg) (ε (t + 1)) +
        matAct (simsRows Pm 0) (η (t + 1))) ↔
      (matAct Γ₀ (y (t + 1)) = matAct Γ₁ (y t) + 0 + matAct Ψ (z (t + 1)) +
        matAct Pm (η (t + 1))) ∧ z (t + 1) = matAct Φ (z t) + matAct Sg (ε (t + 1)) := by
    intro t
    constructor
    · intro h
      have h1 := congrArg (· ∘ Fin.castAdd nz) h
      have h2 := congrArg (· ∘ Fin.natAdd n) h
      simp only [simsH_add_comp, simsH_blk_top, simsH_blk_bot] at h1 h2
      simp only [simsH_top_matAct, simsH_bot_matAct, simsRows_top, simsRows_bot,
        klS_append_castAdd, klS_append_natAdd, klS_zero_matAct, klS_neg_matAct, matAct_one,
        add_zero, zero_add] at h1 h2
      refine ⟨?_, h2⟩
      rw [add_zero]
      linear_combination (norm := module) h1
    · rintro ⟨h1, h2⟩
      refine klS_ext_blocks ?_ ?_
      · simp only [simsH_add_comp, simsH_blk_top]
        simp only [simsH_top_matAct, simsRows_top,
          klS_append_castAdd, klS_append_natAdd, klS_zero_matAct, klS_neg_matAct, add_zero]
        rw [h1]
        abel
      · simp only [simsH_add_comp, simsH_blk_bot]
        simp only [simsH_bot_matAct, simsRows_bot,
          klS_append_castAdd, klS_append_natAdd, klS_zero_matAct, matAct_one, add_zero,
          zero_add]
        exact h2
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨hy, hz⟩ := hadapt.1 h1
    exact ⟨⟨hy, h2, h3, fun t => ((heq t).1 (h4 t)).1⟩, hz, fun t => ((heq t).1 (h4 t)).2⟩
  · rintro ⟨⟨hy, h2, h3, h4⟩, hz, h5⟩
    exact ⟨hadapt.2 ⟨hy, hz⟩, h2, h3, fun t => (heq t).2 ⟨h4 t, h5 t⟩⟩

/-! ### Example 2.3.2 -/

/-- The New Keynesian model of Example 2.3.1 (Miao, (2.13)–(2.15), p. 54) for `t ≥ 1`:
`π_t = κx_t + βE_tπ_{t+1}`, `x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1}) + ε^x_t`,
`i_t = ρ_r i_{t−1} + ε_t` (`p` is inflation `π`; `eI`, `eX` are the shocks `ε`, `ε^x`).
These are the three rows of (2.16). -/
def IsNKSolution (E : CondExpSystem ℂ V) (ρ κ β γ : ℂ) (eI eX : ℕ → V) (i x p : ℕ → V) :
    Prop :=
  ∀ t, p (t + 1) = κ • x (t + 1) + β • E.E (t + 1) (p (t + 2)) ∧
    x (t + 1) = E.E (t + 1) (x (t + 2)) - γ⁻¹ • (i (t + 1) - E.E (t + 1) (p (t + 2))) +
      eX (t + 1) ∧
    i (t + 1) = ρ • i t + eI (t + 1)

/-- `Γ₀` of Example 2.3.2 (Miao, p. 64), for `y_t = (i_t, ξ^x_t, ξ^π_t, x_t, π_t)`. -/
noncomputable def ex232Γ₀ (β γ : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![1, 0, 0, 0, 0; -γ⁻¹, 1, γ⁻¹, 0, 0; 0, 0, β, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

/-- `Γ₁` of Example 2.3.2 (Miao, p. 64). -/
def ex232Γ₁ (ρ κ : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![ρ, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, -κ, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0]

/-- `Ψ` of Example 2.3.2 (Miao, p. 64), for `ε_t = (ε_t, ε^x_t)`. -/
def ex232Ψ : Matrix (Fin 5) (Fin 2) ℂ :=
  !![1, 0; 0, -1; 0, 0; 0, 0; 0, 0]

/-- `Π` of Example 2.3.2 (Miao, p. 64), for `η_t = (η^x_t, η^π_t)`. -/
def ex232Pm (κ : ℂ) : Matrix (Fin 5) (Fin 2) ℂ :=
  !![0, 0; 1, 0; -κ, 1; 1, 0; 0, 1]

/-- The five rows of the Sims form of Example 2.3.2. -/
theorem example_2_3_2_rows (ρ κ β γ : ℂ) (a b : Fin 5 → V) (e h : Fin 2 → V) :
    matAct (ex232Γ₀ β γ) b = matAct (ex232Γ₁ ρ κ) a + matAct ex232Ψ e + matAct (ex232Pm κ) h ↔
      b 0 = ρ • a 0 + e 0 ∧ -γ⁻¹ • b 0 + b 1 + γ⁻¹ • b 2 = a 1 - e 1 + h 0 ∧
        β • b 2 = -κ • a 1 + a 2 + (-κ • h 0 + h 1) ∧ b 3 = a 1 + h 0 ∧ b 4 = a 2 + h 1 := by
  simp only [ex232Γ₀, ex232Γ₁, ex232Ψ, ex232Pm, funext_iff, Fin.forall_fin_succ, Pi.add_apply,
    matAct, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [sub_eq_add_neg, add_assoc]

/-- **Example 2.3.2** (Miao, p. 64). With `ξ^x_t = E_tx_{t+1}`, `ξ^π_t = E_tπ_{t+1}`,
`η^x_t = x_t − ξ^x_{t−1}`, `η^π_t = π_t − ξ^π_{t−1}`, system (2.16) is the Sims form (2.20) with
the printed `5 × 5` matrices `Γ₀`, `Γ₁` and `5 × 2` matrices `Ψ`, `Π` (every entry checked;
they are correct as printed): an adapted `y = (i, ξ^x, ξ^π, x, π)` with adapted `η` solves
(2.20) iff `(i, x, π)` solves (2.13)–(2.15) for `t ≥ 1`, `ξ^x`, `ξ^π` are the expectations
`E_tx_{t+1}`, `E_tπ_{t+1}`, and `η` is the stacked prediction error. -/
theorem example_2_3_2 (E : CondExpSystem ℂ V) (ρ κ β γ : ℂ) (eI eX : ℕ → V)
    (y : ℕ → Fin 5 → V) (η : ℕ → Fin 2 → V) :
    IsSimsSolution E (ex232Γ₀ β γ) (ex232Γ₁ ρ κ) ex232Ψ (ex232Pm κ) (fun t => ![eI t, eX t])
        y η ↔
      IsAdaptedV E y ∧ IsAdaptedV E η ∧
        IsNKSolution E ρ κ β γ eI eX (fun t => y t 0) (fun t => y t 3) (fun t => y t 4) ∧
        (∀ t, y t 1 = E.E t (y (t + 1) 3)) ∧ (∀ t, y t 2 = E.E t (y (t + 1) 4)) ∧
        ∀ t, η (t + 1) 0 = y (t + 1) 3 - y t 1 ∧ η (t + 1) 1 = y (t + 1) 4 - y t 2 := by
  constructor
  · rintro ⟨hya, hηa, hηm, heq⟩
    have hr := fun t => (example_2_3_2_rows ρ κ β γ (y t) (y (t + 1)) _ _).1 (heq t)
    have hξx : ∀ t, y t 1 = E.E t (y (t + 1) 3) := fun t => by
      rw [(hr t).2.2.2.1, map_add, hya t 1, hηm t 0, add_zero]
    have hξp : ∀ t, y t 2 = E.E t (y (t + 1) 4) := fun t => by
      rw [(hr t).2.2.2.2, map_add, hya t 2, hηm t 1, add_zero]
    refine ⟨hya, hηa, fun t => ⟨?_, ?_, ?_⟩, hξx, hξp, fun t => ⟨?_, ?_⟩⟩
    · obtain ⟨-, -, h2, h3, h4⟩ := hr t
      rw [← hξp (t + 1)]
      linear_combination (norm := module) h4 - κ • h3 - h2
    · obtain ⟨-, h1, -, h3, -⟩ := hr t
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      rw [← hξx (t + 1), ← hξp (t + 1)]
      linear_combination (norm := module) h3 - h1
    · have := (hr t).1
      simpa using this
    · rw [(hr t).2.2.2.1]
      abel
    · rw [(hr t).2.2.2.2]
      abel
  · rintro ⟨hya, hηa, hnk, hξx, hξp, hη⟩
    refine ⟨hya, hηa, fun t i => ?_, fun t => ?_⟩
    · fin_cases i
      · change E.E t (η (t + 1) 0) = 0
        rw [(hη t).1, map_sub, ← hξx t, hya t 1, sub_self]
      · change E.E t (η (t + 1) 1) = 0
        rw [(hη t).2, map_sub, ← hξp t, hya t 2, sub_self]
    · refine (example_2_3_2_rows ρ κ β γ (y t) (y (t + 1)) _ _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa using (hnk t).2.2
      · obtain ⟨-, h1, -⟩ := hnk t
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hξx (t + 1), hξp (t + 1), (hη t).1]
        linear_combination (norm := module) -h1
      · obtain ⟨h1, -, -⟩ := hnk t
        rw [hξp (t + 1), (hη t).1, (hη t).2]
        linear_combination (norm := module) -h1
      · rw [(hη t).1]
        abel
      · rw [(hη t).2]
        abel

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.PerturbationSystem
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The perturbation method: misprints and counterexamples

Miao, §2.4, pp. 68–69: the misprints in the second-order displays, and the counterexamples
showing that certainty equivalence needs the determinant conditions.

* `pertFxxPrinted`, `eq_F_xx_printed` (true `F_xx` = printed + `(f_{y'y'} − f_{y'y})(g_xh_x)²`),
  `eq_F_xx_printed_false` (`f = y'²`, `g = h = x`: true `2`, printed `0`).
* `pertFssPrinted`, `eq_F_sigma_sigma_printed` (true `F_σσ` = printed + `(E[ε'²] − 1)η²c`),
  `eq_F_sigma_sigma_printed_false` (`f = x'²`, `ε' = ±2`: true `8`, printed `2`).
* `g_sigma_not_forced` (`f = (y − y', x' − x)`, `g = σ`, `h = x`: a genuine solution with zero
  determinant and `g_σ = 1`), `g_sigma_x_not_forced` (`g = σx`: `g_σx = 1`).
* `pert_P_eq`: a partial derivative computed along a coordinate line.
-/

namespace Miao.RationalExpectations

/-- A partial derivative `pertP K j v` computed along the line `v + t·e_j`. -/
theorem pert_P_eq {K : ℝ × ℝ × ℝ × ℝ → ℝ} (hK : Differentiable ℝ K) {v : ℝ × ℝ × ℝ × ℝ}
    {j : Fin 4} {φ : ℝ → ℝ} {d : ℝ} (hφ : ∀ t, K (v + t • pertE4 j) = φ t)
    (h : HasDerivAt φ d 0) : pertP K j v = d := by
  have hl : HasDerivAt (fun t : ℝ => v + t • pertE4 j) (pertE4 j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (pertE4 j)).const_add v
  have := (hK (v + (0 : ℝ) • pertE4 j)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  rw [zero_smul, add_zero] at this
  exact this.unique (h.congr_of_eventuallyEq (Filter.Eventually.of_forall hφ))

/-! ### `F_xx`: the misprinted first term -/

/-- The display for `F_xx(x̄, 0)` as printed (Miao, p. 68), whose first term is
`f_{y'y}g_xh_x`. -/
noncomputable def pertFxxPrinted (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ)
    (gx hx gxx hxx : ℝ) : ℝ :=
  (pertP (pertP fk 0) 1 v * (gx * hx) + pertP (pertP fk 0) 1 v * gx +
      pertP (pertP fk 0) 2 v * hx + pertP (pertP fk 0) 3 v) * (gx * hx) +
    pertP fk 0 v * gxx * hx * hx + pertP fk 0 v * gx * hxx +
    pertRow fk v 1 (gx * hx) gx hx 1 * gx + pertP fk 1 v * gxx +
    pertRow fk v 2 (gx * hx) gx hx 1 * hx + pertP fk 2 v * hxx + pertRow fk v 3 (gx * hx) gx hx 1

/-- Miao, p. 68: the true `F_xx(x̄, 0)` differs from the printed display by
`(f_{y'y'} − f_{y'y})(g_xh_x)²`. -/
theorem eq_F_xx_printed {fk : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 fk)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDx (pertDx (pertF fk g h η p ε)) (xb, 0) =
      pertFxxPrinted fk (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx h (xb, 0))
          (pertDx (pertDx g) (xb, 0)) (pertDx (pertDx h) (xb, 0)) +
        (pertP (pertP fk 0) 0 (yb, yb, xb, xb) - pertP (pertP fk 0) 1 (yb, yb, xb, xb)) *
          (pertDx g (xb, 0) * pertDx h (xb, 0)) ^ 2 := by
  rw [eq_F_xx hf hg hh η hp hx hy, pertFxxPrinted]
  simp only [pertRow]
  ring

/-- **Counterexample to the printed `F_xx` display** (Miao, p. 68). With `f = y'²`,
`g(x, σ) = h(x, σ) = x` and the degenerate shock `ε' = 0`, at `(x̄, ȳ) = (0, 0)`:
`F_xx(x̄, 0) = 2` (`f_{y'y'}g_x²h_x² = 2`), while the printed display (with `f_{y'y} = 0` in
place of `f_{y'y'}`) gives `0`. -/
theorem eq_F_xx_printed_false :
    ∃ (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (p ε : Fin 1 → ℝ),
      ContDiff ℝ 2 fk ∧ ContDiff ℝ 2 g ∧ ContDiff ℝ 2 h ∧ IsFiniteShock p ε ∧
      h (0, 0) = 0 ∧ g (0, 0) = 0 ∧
      pertDx (pertDx (pertF fk g h 0 p ε)) (0, 0) ≠
        pertFxxPrinted fk (0, 0, 0, 0) (pertDx g (0, 0)) (pertDx h (0, 0))
          (pertDx (pertDx g) (0, 0)) (pertDx (pertDx h) (0, 0)) := by
  set fk : ℝ × ℝ × ℝ × ℝ → ℝ := fun v => v.1 ^ 2 with hfk
  set g : ℝ × ℝ → ℝ := fun q => q.1 with hg
  have hfk2 : ContDiff ℝ 2 fk := by fun_prop
  have hg2 : ContDiff ℝ 2 g := by fun_prop
  have hp : IsFiniteShock ![(1 : ℝ)] ![0] := ⟨fun i => by simp, by simp, by simp⟩
  have hgx : pertDx g (0, 0) = 1 :=
    pert_Dx_eq (hg2.differentiable (by norm_num)) (hasDerivAt_id (0 : ℝ))
  have hP0 : pertP fk 0 = fun v => 2 * v.1 := funext fun v =>
    pert_P_eq (hfk2.differentiable (by norm_num)) (φ := fun t => (v.1 + t) ^ 2)
      (fun t => by simp [hfk, pertE4])
      (by simpa using ((hasDerivAt_id' (0 : ℝ)).const_add v.1).fun_pow 2)
  have h00 : pertP (pertP fk 0) 0 (0, 0, 0, 0) = 2 := by
    rw [hP0]
    exact pert_P_eq (by fun_prop) (φ := fun t => 2 * t) (fun t => by simp [pertE4])
      (by simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2)
  have h01 : pertP (pertP fk 0) 1 (0, 0, 0, 0) = 0 := by
    rw [hP0]
    exact pert_P_eq (by fun_prop) (φ := fun _ => 0) (fun t => by simp [pertE4])
      (hasDerivAt_const 0 0)
  refine ⟨fk, g, g, ![1], ![0], hfk2, hg2, hg2, hp, rfl, rfl, fun H => ?_⟩
  rw [eq_F_xx_printed (xb := 0) (yb := 0) hfk2 hg2 hg2 0 hp rfl rfl, h00, h01, hgx] at H
  norm_num at H

/-! ### `F_σσ`: the missing `E[ε'²]` -/

/-- The display for `F_σσ(x̄, 0)` as printed (Miao, p. 69), with `I = 1`. -/
noncomputable def pertFssPrinted (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ)
    (η gx gxx gss hss : ℝ) : ℝ :=
  pertP fk 0 v * gx * hss + pertP (pertP fk 0) 0 v * gx * η * gx * η +
    pertP (pertP fk 0) 2 v * η * gx * η + pertP fk 0 v * gxx * η * η + pertP fk 0 v * gss +
    pertP fk 1 v * gss + pertP fk 2 v * hss + pertP (pertP fk 2) 0 v * gx * η * η +
    pertP (pertP fk 2) 2 v * η * η

/-- Miao, p. 69: the true `F_σσ(x̄, 0)` (given `g_σ = h_σ = 0`) is the printed display plus
`(E[ε'²] − 1)η²c`, `c = pertCoefSS`; so the display is right iff `E[ε'²] = 1` or `ηc = 0`. -/
theorem eq_F_sigma_sigma_printed {fk : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ 2 fk) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ}
    {p ε : Fin N → ℝ} (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb)
    (hy : g (xb, 0) = yb) (hgs : pertDs g (xb, 0) = 0) (hhs : pertDs h (xb, 0) = 0) :
    pertDs (pertDs (pertF fk g h η p ε)) (xb, 0) =
      pertFssPrinted fk (yb, yb, xb, xb) η (pertDx g (xb, 0)) (pertDx (pertDx g) (xb, 0))
          (pertDs (pertDs g) (xb, 0)) (pertDs (pertDs h) (xb, 0)) +
        (∑ i, p i * ε i ^ 2 - 1) * η ^ 2 *
          pertCoefSS fk (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx (pertDx g) (xb, 0)) := by
  rw [eq_F_sigma_sigma hf hg hh η hp hx hy hgs hhs, pertFssPrinted, pertCoefSS]
  ring

/-- **Counterexample to the printed `F_σσ` display** (Miao, p. 69). With `f = x'²`, `g = h = 0`,
`η = 1` and `ε' = ±2` with probability `½` each (so `E[ε'²] = 4`), at `(x̄, ȳ) = (0, 0)`:
`F_σσ(x̄, 0) = f_{x'x'}η²E[ε'²] = 8`, while the printed display gives `f_{x'x'}η² = 2`. -/
theorem eq_F_sigma_sigma_printed_false :
    ∃ (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (p ε : Fin 2 → ℝ),
      ContDiff ℝ 2 fk ∧ ContDiff ℝ 2 g ∧ ContDiff ℝ 2 h ∧ IsFiniteShock p ε ∧
      h (0, 0) = 0 ∧ g (0, 0) = 0 ∧ pertDs g (0, 0) = 0 ∧ pertDs h (0, 0) = 0 ∧
      pertDs (pertDs (pertF fk g h 1 p ε)) (0, 0) ≠
        pertFssPrinted fk (0, 0, 0, 0) 1 (pertDx g (0, 0)) (pertDx (pertDx g) (0, 0))
          (pertDs (pertDs g) (0, 0)) (pertDs (pertDs h) (0, 0)) := by
  set fk : ℝ × ℝ × ℝ × ℝ → ℝ := fun v => v.2.2.1 ^ 2 with hfk
  set g : ℝ × ℝ → ℝ := fun _ => 0 with hg
  have hfk2 : ContDiff ℝ 2 fk := by fun_prop
  have hg2 : ContDiff ℝ 2 g := contDiff_const
  have hp : IsFiniteShock ![(1 / 2 : ℝ), 1 / 2] ![2, -2] :=
    ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]; norm_num,
      by simp [Fin.sum_univ_two]⟩
  obtain ⟨hgx, hgs⟩ := pert_partials_vanish (G := g) fun _ => rfl
  have hgx' : pertDx g = fun _ => 0 := funext hgx
  have hgxx : pertDx (pertDx g) (0, 0) = 0 := by
    rw [hgx']
    exact (pert_partials_vanish (G := fun _ : ℝ × ℝ => (0 : ℝ)) fun _ => rfl).1 _
  have hP2 : pertP fk 2 = fun v => 2 * v.2.2.1 := funext fun v =>
    pert_P_eq (hfk2.differentiable (by norm_num)) (φ := fun t => (v.2.2.1 + t) ^ 2)
      (fun t => by simp [hfk, pertE4])
      (by simpa using ((hasDerivAt_id' (0 : ℝ)).const_add v.2.2.1).fun_pow 2)
  have h22 : pertP (pertP fk 2) 2 (0, 0, 0, 0) = 2 := by
    rw [hP2]
    exact pert_P_eq (by fun_prop) (φ := fun t => 2 * t) (fun t => by simp [pertE4])
      (by simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2)
  refine ⟨fk, g, g, ![1 / 2, 1 / 2], ![2, -2], hfk2, hg2, hg2, hp, rfl, rfl, hgs _, hgs _,
    fun H => ?_⟩
  rw [eq_F_sigma_sigma_printed (xb := 0) (yb := 0) hfk2 hg2 hg2 1 hp rfl rfl (hgs _)
    (hgs _), pertCoefSS, hgx, hgxx, h22] at H
  simp [Fin.sum_univ_two] at H
  norm_num at H

/-! ### `g_σ = h_σ = 0` and `g_σx = h_σx = 0` are not forced when the determinant vanishes -/

/-- **`g_σ = h_σ = 0` is not forced** (Miao, p. 67). With `f₀ = y − y'` (`y_t = E_ty_{t+1}`),
`f₁ = x' − x` (`x_{t+1} = x_t + σε_{t+1}`), `η = 1`, `ε' = ±1` with probability `½`, the policy
`g(x, σ) = σ`, `h(x, σ) = x` solves (2.30), passes through the steady state `(0, 0)`, the
determinant of the `F_σ` system is `0`, and `g_σ(0, 0) = 1 ≠ 0`. -/
theorem g_sigma_not_forced :
    ∃ (f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (p ε : Fin 2 → ℝ),
      IsPertSolution f g h 1 p ε ∧ h (0, 0) = 0 ∧ g (0, 0) = 0 ∧
      pertCoefA (f 0) (0, 0, 0, 0) * pertCoefB (f 1) (0, 0, 0, 0) (pertDx g (0, 0)) -
        pertCoefB (f 0) (0, 0, 0, 0) (pertDx g (0, 0)) * pertCoefA (f 1) (0, 0, 0, 0) = 0 ∧
      pertDs g (0, 0) ≠ 0 := by
  set f0 : ℝ × ℝ × ℝ × ℝ → ℝ := fun v => v.2.1 - v.1 with hf0
  have hf0d : Differentiable ℝ f0 := by fun_prop
  have h00 : pertP f0 0 (0, 0, 0, 0) = -1 :=
    pert_P_eq hf0d (φ := fun t => -t) (fun t => by simp [hf0, pertE4])
      (hasDerivAt_id' (0 : ℝ)).neg
  have h01 : pertP f0 1 (0, 0, 0, 0) = 1 :=
    pert_P_eq hf0d (φ := fun t => t) (fun t => by simp [hf0, pertE4]) (hasDerivAt_id 0)
  have h02 : pertP f0 2 (0, 0, 0, 0) = 0 :=
    pert_P_eq hf0d (φ := fun _ => 0) (fun t => by simp [hf0, pertE4]) (hasDerivAt_const 0 0)
  have hgd : Differentiable ℝ fun q : ℝ × ℝ => q.2 := by fun_prop
  have hgx : pertDx (fun q : ℝ × ℝ => q.2) (0, 0) = 0 := pert_Dx_eq hgd (hasDerivAt_const 0 0)
  have hgs : pertDs (fun q : ℝ × ℝ => q.2) (0, 0) = 1 := pert_Ds_eq hgd (hasDerivAt_id 0)
  refine ⟨![f0, fun v => v.2.2.1 - v.2.2.2], fun q => q.2, fun q => q.1, ![1 / 2, 1 / 2],
    ![1, -1], ⟨fun k => ?_, by fun_prop, by fun_prop, ⟨fun i => by fin_cases i <;> norm_num,
      by simp [Fin.sum_univ_two]; norm_num, by simp [Fin.sum_univ_two]⟩, fun k q => ?_⟩, rfl,
      rfl, ?_, by rw [hgs]; norm_num⟩
  · fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hf0] <;> fun_prop
  · fin_cases k <;> simp [pertF, pertPhi, pertPsi, Fin.sum_univ_two, hf0]
  · simp only [Matrix.cons_val_zero, pertCoefA, pertCoefB, h00, h01, h02, hgx]
    ring

/-- **`g_σx = h_σx = 0` is not forced** (Miao, p. 69). Same `f`, `η`, shock as
`g_sigma_not_forced`, with the policy `g(x, σ) = σx`, `h(x, σ) = x`: it solves (2.30), passes
through `(0, 0)`, `g_σ = h_σ = 0` there, the determinant of the `F_σx` system is `0`, and
`g_σx(0, 0) = 1 ≠ 0`. -/
theorem g_sigma_x_not_forced :
    ∃ (f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (p ε : Fin 2 → ℝ),
      IsPertSolution f g h 1 p ε ∧ h (0, 0) = 0 ∧ g (0, 0) = 0 ∧ pertDs g (0, 0) = 0 ∧
      pertDs h (0, 0) = 0 ∧
      pertCoefAx (f 0) (0, 0, 0, 0) (pertDx h (0, 0)) *
          pertCoefB (f 1) (0, 0, 0, 0) (pertDx g (0, 0)) -
        pertCoefB (f 0) (0, 0, 0, 0) (pertDx g (0, 0)) *
          pertCoefAx (f 1) (0, 0, 0, 0) (pertDx h (0, 0)) = 0 ∧
      pertDs (pertDx g) (0, 0) ≠ 0 := by
  set f0 : ℝ × ℝ × ℝ × ℝ → ℝ := fun v => v.2.1 - v.1 with hf0
  have hf0d : Differentiable ℝ f0 := by fun_prop
  have h00 : pertP f0 0 (0, 0, 0, 0) = -1 :=
    pert_P_eq hf0d (φ := fun t => -t) (fun t => by simp [hf0, pertE4])
      (hasDerivAt_id' (0 : ℝ)).neg
  have h01 : pertP f0 1 (0, 0, 0, 0) = 1 :=
    pert_P_eq hf0d (φ := fun t => t) (fun t => by simp [hf0, pertE4]) (hasDerivAt_id 0)
  have h02 : pertP f0 2 (0, 0, 0, 0) = 0 :=
    pert_P_eq hf0d (φ := fun _ => 0) (fun t => by simp [hf0, pertE4]) (hasDerivAt_const 0 0)
  set g : ℝ × ℝ → ℝ := fun q => q.2 * q.1 with hg
  have hgd : Differentiable ℝ g := by fun_prop
  have hhd : Differentiable ℝ fun q : ℝ × ℝ => q.1 := by fun_prop
  have hgx : pertDx g = fun q => q.2 := funext fun q =>
    pert_Dx_eq hgd (by simpa using (hasDerivAt_id q.1).const_mul q.2)
  have hgs : pertDs g (0, 0) = 0 :=
    pert_Ds_eq hgd (by simpa [hg] using (hasDerivAt_id (0 : ℝ)).mul_const (0 : ℝ))
  have hhx : pertDx (fun q : ℝ × ℝ => q.1) (0, 0) = 1 := pert_Dx_eq hhd (hasDerivAt_id 0)
  have hhs : pertDs (fun q : ℝ × ℝ => q.1) (0, 0) = 0 := pert_Ds_eq hhd (hasDerivAt_const 0 0)
  have hgsx : pertDs (pertDx g) (0, 0) = 1 := by
    rw [hgx]
    exact pert_Ds_eq (by fun_prop) (hasDerivAt_id 0)
  refine ⟨![f0, fun v => v.2.2.1 - v.2.2.2], g, fun q => q.1, ![1 / 2, 1 / 2],
    ![1, -1], ⟨fun k => ?_, by fun_prop, by fun_prop, ⟨fun i => by fin_cases i <;> norm_num,
      by simp [Fin.sum_univ_two]; norm_num, by simp [Fin.sum_univ_two]⟩, fun k q => ?_⟩, rfl,
      by simp [hg], hgs, hhs, ?_, by rw [hgsx]; norm_num⟩
  · fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hf0] <;> fun_prop
  · fin_cases k
    · simp [pertF, pertPhi, pertPsi, Fin.sum_univ_two, hf0, hg]
      ring
    · simp [pertF, pertPhi, pertPsi, Fin.sum_univ_two, hf0, hg]
  · simp only [Matrix.cons_val_zero, pertCoefAx, pertCoefB, h00, h01, h02, hgx, hhx]
    ring

end Miao.RationalExpectations

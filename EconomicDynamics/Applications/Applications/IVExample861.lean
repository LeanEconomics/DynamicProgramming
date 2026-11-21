/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.IVAugmented
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Example 8.6.1 (static investment with fixed and transactions costs)

Miao, Example 8.6.1, pp. 285–286: `ψ(Q) = max_I QI − p_bI1_{I>0} − p_sI1_{I<0} − I²/2 − φ1_{I≠0}`
(`iv_g` and `iv_gφ` with `Ψ(I) = I²/2`), `p_s ≤ p_b`.

* No fixed cost: `I* = Q − p_b > 0` if `Q > p_b`, `0` if `p_s ≤ Q ≤ p_b`, `Q − p_s < 0` if
  `Q < p_s`, with profits `(Q − p_b)²/2`, `0`, `(Q − p_s)²/2` (`example_8_6_1_buy`,
  `example_8_6_1_inaction`, `example_8_6_1_sell`).
* Fixed cost `φ > 0`: **correction** — the thresholds are `p_b + √(2φ)` and `p_s − √(2φ)`, not
  `p_b + 2√φ` and `p_s − 2√φ` as printed (`example_8_6_1_fixed_buy`,
  `example_8_6_1_fixed_inaction`, `example_8_6_1_fixed_sell`; counterexample
  `example_8_6_1_misprint`). `Q₂ = p_b + √(2φ)` is the zero of `ψ − φ` used in (8.43)
  (`example_8_6_1_Q2`).
* (8.38)–(8.40) are not sufficient with fixed costs (`iv_fixed_foc_not_sufficient`), and (8.36)
  as printed (fixed cost charged also at `I = 0`) selects a non-optimal investment
  (`iv_eq_8_36_misprint`).
-/

namespace Miao.Applications

/-- The quadratic adjustment cost `Ψ(I) = I²/2` of Example 8.6.1. -/
noncomputable def iv_psi861 (I : ℝ) : ℝ := I ^ 2 / 2

/-- **Example 8.6.1** (Miao, p. 285), `φ = 0`, `Q > p_b`: `I* = Q − p_b > 0` is optimal with
profit `(Q − p_b)²/2`. -/
theorem example_8_6_1_buy {pb ps Q : ℝ} (hp : ps ≤ pb) (hQ : pb < Q) :
    0 < Q - pb ∧ (∀ I, iv_g pb ps iv_psi861 Q I ≤ iv_g pb ps iv_psi861 Q (Q - pb)) ∧
      iv_g pb ps iv_psi861 Q (Q - pb) = (Q - pb) ^ 2 / 2 := by
  have hI : 0 < Q - pb := by linarith
  have hv : iv_g pb ps iv_psi861 Q (Q - pb) = (Q - pb) ^ 2 / 2 := by
    simp only [iv_g, iv_psi861, hI, ↓reduceIte]; ring
  refine ⟨hI, fun I => ?_, hv⟩
  rw [hv]
  have := (iv_g_le_buy (Q := Q) (Ψ := iv_psi861) hp (by simp [iv_psi861]) I).1
  simp only [iv_psi861] at this
  nlinarith [sq_nonneg (I - (Q - pb))]

/-- **Example 8.6.1** (Miao, p. 285), `φ = 0`, `p_s ≤ Q ≤ p_b`: `I* = 0` with profit `0`. -/
theorem example_8_6_1_inaction {pb ps Q : ℝ} (h1 : ps ≤ Q) (h2 : Q ≤ pb) :
    (∀ I, iv_g pb ps iv_psi861 Q I ≤ iv_g pb ps iv_psi861 Q 0) ∧ iv_g pb ps iv_psi861 Q 0 = 0 :=
  ⟨eq_8_39 (by simp [iv_psi861]) (fun I => by unfold iv_psi861; positivity) h1 h2,
    by simp [iv_g, iv_psi861]⟩

/-- **Example 8.6.1** (Miao, p. 285), `φ = 0`, `Q < p_s`: `I* = Q − p_s < 0` is optimal with
profit `(Q − p_s)²/2`. -/
theorem example_8_6_1_sell {pb ps Q : ℝ} (hp : ps ≤ pb) (hQ : Q < ps) :
    Q - ps < 0 ∧ (∀ I, iv_g pb ps iv_psi861 Q I ≤ iv_g pb ps iv_psi861 Q (Q - ps)) ∧
      iv_g pb ps iv_psi861 Q (Q - ps) = (Q - ps) ^ 2 / 2 := by
  have hI : Q - ps < 0 := by linarith
  have hv : iv_g pb ps iv_psi861 Q (Q - ps) = (Q - ps) ^ 2 / 2 := by
    simp only [iv_g, iv_psi861, not_lt.2 hI.le, hI, ↓reduceIte]; ring
  refine ⟨hI, fun I => ?_, hv⟩
  rw [hv]
  have := (iv_g_le_sell (Q := Q) (Ψ := iv_psi861) hp (by simp [iv_psi861]) I).1
  simp only [iv_psi861] at this
  nlinarith [sq_nonneg (I - (Q - ps))]

/-- **Example 8.6.1** (Miao, p. 286), corrected: with fixed cost `φ > 0` and `Q > p_b + √(2φ)`,
`I* = Q − p_b > 0` is optimal and strictly better than inaction. -/
theorem example_8_6_1_fixed_buy {pb ps Q φ : ℝ} (hp : ps ≤ pb) (hφ : 0 < φ)
    (hQ : pb + Real.sqrt (2 * φ) < Q) :
    (∀ I, iv_gφ pb ps φ iv_psi861 Q I ≤ iv_gφ pb ps φ iv_psi861 Q (Q - pb)) ∧
      iv_gφ pb ps φ iv_psi861 Q 0 < iv_gφ pb ps φ iv_psi861 Q (Q - pb) := by
  have hs0 : 0 ≤ Real.sqrt (2 * φ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2 * φ) ^ 2 = 2 * φ := Real.sq_sqrt (by linarith)
  obtain ⟨hI, hopt, hv⟩ := example_8_6_1_buy (Q := Q) hp (by linarith)
  have h0 : iv_gφ pb ps φ iv_psi861 Q 0 = 0 := by simp [iv_gφ, iv_g, iv_psi861]
  have hs : iv_gφ pb ps φ iv_psi861 Q (Q - pb) = (Q - pb) ^ 2 / 2 - φ := by
    simp [iv_gφ, hI.ne', hv]
  have hlt : φ < (Q - pb) ^ 2 / 2 := by nlinarith
  refine ⟨fun I => ?_, by rw [h0, hs]; linarith⟩
  rw [hs]
  rcases eq_or_ne I 0 with h | h
  · subst h; rw [h0]; linarith
  · simp only [iv_gφ, h, ↓reduceIte]
    linarith [hopt I, hv]

/-- **Example 8.6.1** (Miao, p. 286), corrected: with `φ > 0` and
`p_s − √(2φ) ≤ Q ≤ p_b + √(2φ)`, inaction is optimal. -/
theorem example_8_6_1_fixed_inaction {pb ps Q φ : ℝ} (hp : ps ≤ pb) (hφ : 0 < φ)
    (h1 : ps - Real.sqrt (2 * φ) ≤ Q) (h2 : Q ≤ pb + Real.sqrt (2 * φ)) (I : ℝ) :
    iv_gφ pb ps φ iv_psi861 Q I ≤ iv_gφ pb ps φ iv_psi861 Q 0 := by
  have hs0 : 0 ≤ Real.sqrt (2 * φ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2 * φ) ^ 2 = 2 * φ := Real.sq_sqrt (by linarith)
  have h0 : iv_gφ pb ps φ iv_psi861 Q 0 = 0 := by simp [iv_gφ, iv_g, iv_psi861]
  rw [h0]
  rcases lt_trichotomy I 0 with h | h | h
  · simp only [iv_gφ, h.ne, ↓reduceIte]
    rw [(iv_g_le_sell (Q := Q) (Ψ := iv_psi861) hp (by simp [iv_psi861]) I).2 h.le]
    simp only [iv_psi861]
    nlinarith [sq_nonneg (I + Real.sqrt (2 * φ))]
  · subst h; rw [h0]
  · simp only [iv_gφ, h.ne', ↓reduceIte]
    rw [(iv_g_le_buy (Q := Q) (Ψ := iv_psi861) hp (by simp [iv_psi861]) I).2 h.le]
    simp only [iv_psi861]
    nlinarith [sq_nonneg (I - Real.sqrt (2 * φ))]

/-- **Example 8.6.1** (Miao, p. 286), corrected: with `φ > 0` and `Q < p_s − √(2φ)`,
`I* = Q − p_s < 0` is optimal and strictly better than inaction. -/
theorem example_8_6_1_fixed_sell {pb ps Q φ : ℝ} (hp : ps ≤ pb) (hφ : 0 < φ)
    (hQ : Q < ps - Real.sqrt (2 * φ)) :
    (∀ I, iv_gφ pb ps φ iv_psi861 Q I ≤ iv_gφ pb ps φ iv_psi861 Q (Q - ps)) ∧
      iv_gφ pb ps φ iv_psi861 Q 0 < iv_gφ pb ps φ iv_psi861 Q (Q - ps) := by
  have hs0 : 0 ≤ Real.sqrt (2 * φ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2 * φ) ^ 2 = 2 * φ := Real.sq_sqrt (by linarith)
  obtain ⟨hI, hopt, hv⟩ := example_8_6_1_sell (Q := Q) hp (by linarith)
  have h0 : iv_gφ pb ps φ iv_psi861 Q 0 = 0 := by simp [iv_gφ, iv_g, iv_psi861]
  have hs : iv_gφ pb ps φ iv_psi861 Q (Q - ps) = (Q - ps) ^ 2 / 2 - φ := by
    simp [iv_gφ, hI.ne, hv]
  have hlt : φ < (Q - ps) ^ 2 / 2 := by nlinarith
  refine ⟨fun I => ?_, by rw [h0, hs]; linarith⟩
  rw [hs]
  rcases eq_or_ne I 0 with h | h
  · subst h; rw [h0]; linarith
  · simp only [iv_gφ, h, ↓reduceIte]
    linarith [hopt I, hv]

/-- Miao, p. 286: `Q₂ = p_b + √(2φ)` is where the shifted reward `ψ − φ` crosses zero: the
buy-FOC solution `I₂ = Q₂ − p_b = √(2φ) > 0` has `g_{Q₂}(I₂) = φ` (the hypothesis of
`eq_8_43`). -/
theorem example_8_6_1_Q2 {pb ps φ : ℝ} (hφ : 0 < φ) :
    0 < Real.sqrt (2 * φ) ∧
      iv_g pb ps iv_psi861 (pb + Real.sqrt (2 * φ)) (Real.sqrt (2 * φ)) = φ := by
  have hs : 0 < Real.sqrt (2 * φ) := Real.sqrt_pos.2 (by linarith)
  have hs2 : Real.sqrt (2 * φ) ^ 2 = 2 * φ := Real.sq_sqrt (by linarith)
  refine ⟨hs, ?_⟩
  simp only [iv_g, iv_psi861, hs, ↓reduceIte]
  nlinarith

/-- **Correction** to Example 8.6.1 (Miao, p. 286): the printed thresholds `p_b + 2√φ`,
`p_s − 2√φ` are wrong. With `φ = 1/2` and `Q = p_b + 6/5 ≤ p_b + 2√φ = p_b + √2`, the printed
rule prescribes `I* = 0`, but investing `I = 6/5` gives `(6/5)²/2 − 1/2 = 0.22 > 0`. -/
theorem example_8_6_1_misprint {pb ps : ℝ} :
    pb + 6 / 5 ≤ pb + 2 * Real.sqrt (1 / 2) ∧
      iv_gφ pb ps (1 / 2) iv_psi861 (pb + 6 / 5) 0 <
        iv_gφ pb ps (1 / 2) iv_psi861 (pb + 6 / 5) (6 / 5) := by
  have hs : (6 / 5 : ℝ) ≤ 2 * Real.sqrt (1 / 2) := by
    have h2 : (3 / 5 : ℝ) ≤ Real.sqrt (1 / 2) := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  refine ⟨by linarith, ?_⟩
  have hpos : (0 : ℝ) < 6 / 5 := by norm_num
  simp only [iv_gφ, iv_g, iv_psi861, hpos, ↓reduceIte, lt_irrefl]
  norm_num
  linarith

/-- Miao, p. 286: "(8.38)–(8.40) … are not sufficient for optimality" with fixed costs. With
`p_b = 1`, `p_s = 0`, `φ = 1/2`, `Q = 3/2`, `I* = 1/2 > 0` satisfies `p_b + Ψ₁(I*) = Q`
(`Ψ₁(I) = I`), yet inaction is strictly better. -/
theorem iv_fixed_foc_not_sufficient :
    (0 : ℝ) < 1 / 2 ∧ (1 : ℝ) + 1 / 2 = 3 / 2 ∧
      iv_gφ 1 0 (1 / 2) iv_psi861 (3 / 2) (1 / 2) < iv_gφ 1 0 (1 / 2) iv_psi861 (3 / 2) 0 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  simp only [iv_gφ, iv_g, iv_psi861, hpos, ↓reduceIte, lt_irrefl]
  norm_num

/-- **Correction** to (8.36) (Miao, p. 282): as printed, (8.36) subtracts `φ(K)` for every `I`,
including `I = 0`. Take a linear continuation value `W(x) = Qx` (so `R(I) − R(0)` is exactly the
static objective, `eq_8_36`), `p_b = 1`, `p_s = 0`, `Ψ(I) = I²/2`, `φ = 1/2`, `Q = 3/2`. The
printed objective `g(I) − φ` is maximised at `I = 1/2`, but the true objective
(fixed cost only if `I ≠ 0`) is strictly larger at `I = 0` than at `I = 1/2`. -/
theorem iv_eq_8_36_misprint :
    (∀ I, iv_g 1 0 iv_psi861 (3 / 2) I - 1 / 2 ≤ iv_g 1 0 iv_psi861 (3 / 2) (1 / 2) - 1 / 2) ∧
      iv_gφ 1 0 (1 / 2) iv_psi861 (3 / 2) (1 / 2) < iv_gφ 1 0 (1 / 2) iv_psi861 (3 / 2) 0 := by
  refine ⟨fun I => ?_, iv_fixed_foc_not_sufficient.2.2⟩
  obtain ⟨_, hopt, _⟩ := example_8_6_1_buy (pb := 1) (ps := 0) (Q := 3 / 2) (by norm_num)
    (by norm_num)
  have := hopt I
  norm_num at this ⊢
  linarith

end Miao.Applications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Portfolio choice

AKMM, §7.2.3, pp. 195–196. Wealth `W > 0` is split between a risk-free asset with gross return
`R_f` and an amount `A` in a risky asset with return `Z`, which takes finitely many values
`Z(s)` with probabilities `p(s)`; date-1 consumption is `R_f(W − A) + Z(s)A`
(`pf_cons`), and the investor maximises `E₀u(R_f(W − A) + ZA)` (`pf_value`).

* The first-order condition `E₀[u′(R_f(W − A) + ZA)(Z − R_f)] = 0` at an interior optimum
  (`portfolio_foc`).
* CRRA `u(c) = c^{1−σ}/(1 − σ)`: the condition is `W^{−σ}` times a condition in `A/W` alone
  (`portfolio_crra_foc`), and if `A` is optimal at `W` then `λA` is optimal at `λW`
  (`portfolio_crra_scale`): the optimal risky share `A/W` does not depend on wealth
  (`portfolio_crra_share`).
* CARA `u(c) = −exp(−αc)`: the condition is `α exp(−αR_fW)` times a condition in `A` alone
  (`portfolio_cara_foc`), the objective at `W′` is `exp(−αR_f(W′ − W))` times the objective at
  `W`, so the optimal amount `A` does not depend on wealth (`portfolio_cara_invariant`), and the
  risky share `A/W` falls with wealth (`portfolio_cara_share_falls`).

Departure: the book derives these from the first-order condition, which determines the optimum
only when it has a unique solution; the homogeneity statements are proved for the optimum itself
(any maximiser), by scaling the objective, and need no uniqueness or interiority.
-/

namespace AKMM.Uncertainty

open Real

variable {S : Type*} [Fintype S]

/-- AKMM, p. 195: date-1 consumption `R_f(W − A) + Z(s)A` in state `s`. -/
def pf_cons (Rf : ℝ) (Z : S → ℝ) (W A : ℝ) (s : S) : ℝ := Rf * (W - A) + Z s * A

/-- AKMM, p. 195: the investor's objective `E₀u(R_f(W − A) + ZA)`. -/
noncomputable def pf_value (u : ℝ → ℝ) (p : S → ℝ) (Rf : ℝ) (Z : S → ℝ) (W A : ℝ) : ℝ :=
  ∑ s, p s * u (pf_cons Rf Z W A s)

/-- **AKMM, p. 195: the first-order condition of the portfolio problem.** At a local maximum
`A`, with `u` differentiable at each date-1 consumption,
`E₀[u′(R_f(W − A) + ZA)(Z − R_f)] = 0`. -/
theorem portfolio_foc {u : ℝ → ℝ} {du : S → ℝ} {p : S → ℝ} {Rf : ℝ} {Z : S → ℝ} {W A : ℝ}
    (hmax : IsLocalMax (fun A => pf_value u p Rf Z W A) A)
    (hd : ∀ s, HasDerivAt u (du s) (pf_cons Rf Z W A s)) :
    ∑ s, p s * (du s * (Z s - Rf)) = 0 := by
  have hc : ∀ s, HasDerivAt (fun A => pf_cons Rf Z W A s) (Z s - Rf) A := fun s => by
    have h1 : HasDerivAt (fun A => Rf * (W - A) + Z s * A) (Rf * (-1) + Z s * 1) A :=
      (((hasDerivAt_id' A).const_sub W).const_mul Rf).add ((hasDerivAt_id' A).const_mul (Z s))
    exact h1.congr_deriv (by ring)
  have hV : HasDerivAt (fun A => pf_value u p Rf Z W A)
      (∑ s, p s * (du s * (Z s - Rf))) A := by
    unfold pf_value
    exact HasDerivAt.fun_sum fun s _ => ((hd s).comp A (hc s)).const_mul (p s)
  exact hmax.hasDerivAt_eq_zero hV

/-- AKMM, p. 195: with CRRA marginal utility `c^{−σ}` and `W > 0`, the first-order condition is
`W^{−σ}E₀[(R_f(1 − A/W) + ZA/W)^{−σ}(Z − R_f)] = 0`, which involves `A/W` only. -/
theorem portfolio_crra_foc {p : S → ℝ} {Rf σ W A : ℝ} {Z : S → ℝ} (hW : 0 < W)
    (hc : ∀ s, 0 < pf_cons Rf Z W A s) :
    ∑ s, p s * (pf_cons Rf Z W A s ^ (-σ) * (Z s - Rf)) =
      W ^ (-σ) * ∑ s, p s * ((Rf * (1 - A / W) + Z s * (A / W)) ^ (-σ) * (Z s - Rf)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have he : pf_cons Rf Z W A s = W * (Rf * (1 - A / W) + Z s * (A / W)) := by
    simp only [pf_cons]; field_simp
  have hpos : 0 ≤ Rf * (1 - A / W) + Z s * (A / W) := by
    have := hc s
    rw [he] at this
    exact (pos_of_mul_pos_right this hW.le).le
  rw [he, mul_rpow hW.le hpos]
  ring

/-- The investor with CRRA utility `c^{1−σ}/(1 − σ)` chooses `A` among the portfolios with
positive consumption in every state. -/
def pf_CRRAOptimal (p : S → ℝ) (Rf σ : ℝ) (Z : S → ℝ) (W A : ℝ) : Prop :=
  (∀ s, 0 < pf_cons Rf Z W A s) ∧ ∀ A', (∀ s, 0 < pf_cons Rf Z W A' s) →
    pf_value (fun c => c ^ (1 - σ) / (1 - σ)) p Rf Z W A' ≤
      pf_value (fun c => c ^ (1 - σ) / (1 - σ)) p Rf Z W A

omit [Fintype S] in
theorem pf_cons_smul (Rf : ℝ) (Z : S → ℝ) (W A l : ℝ) (s : S) :
    pf_cons Rf Z (l * W) (l * A) s = l * pf_cons Rf Z W A s := by
  simp only [pf_cons]; ring

theorem pf_value_crra_smul {p : S → ℝ} {Rf σ W A l : ℝ} {Z : S → ℝ} (hl : 0 < l)
    (hc : ∀ s, 0 < pf_cons Rf Z W A s) :
    pf_value (fun c => c ^ (1 - σ) / (1 - σ)) p Rf Z (l * W) (l * A) =
      l ^ (1 - σ) * pf_value (fun c => c ^ (1 - σ) / (1 - σ)) p Rf Z W A := by
  simp only [pf_value, pf_cons_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_rpow hl.le (hc s).le]
  ring

/-- **AKMM, pp. 195–196: CRRA portfolios scale with wealth.** If `A` is optimal at wealth `W`
then `λA` is optimal at wealth `λW` for every `λ > 0`. -/
theorem portfolio_crra_scale {p : S → ℝ} {Rf σ W A : ℝ} {Z : S → ℝ}
    (hopt : pf_CRRAOptimal p Rf σ Z W A) {l : ℝ} (hl : 0 < l) :
    pf_CRRAOptimal p Rf σ Z (l * W) (l * A) := by
  obtain ⟨hc, hmax⟩ := hopt
  refine ⟨fun s => by rw [pf_cons_smul]; exact mul_pos hl (hc s), fun A' hA' => ?_⟩
  have hA'' : ∀ s, 0 < pf_cons Rf Z W (A' / l) s := fun s => by
    have h := hA' s
    rw [show A' = l * (A' / l) by field_simp, pf_cons_smul] at h
    exact pos_of_mul_pos_right h hl.le
  have hle := hmax _ hA''
  have e : A' = l * (A' / l) := by field_simp
  rw [e, pf_value_crra_smul hl hA'', pf_value_crra_smul hl hc]
  have : 0 < l ^ (1 - σ) := rpow_pos_of_pos hl _
  exact mul_le_mul_of_nonneg_left hle this.le

/-- **AKMM, p. 196: "the rich and the poor choose the same risk exposure".** Under CRRA, if `A`
is optimal at `W > 0` then at every wealth `W′ > 0` the portfolio with the same risky share
`A/W` is optimal. -/
theorem portfolio_crra_share {p : S → ℝ} {Rf σ W A : ℝ} {Z : S → ℝ} (hW : 0 < W)
    (hopt : pf_CRRAOptimal p Rf σ Z W A) {W' : ℝ} (hW' : 0 < W') :
    pf_CRRAOptimal p Rf σ Z W' (A / W * W') := by
  have h := portfolio_crra_scale hopt (div_pos hW' hW)
  rwa [show W' / W * W = W' by field_simp, show W' / W * A = A / W * W' by ring] at h

/-- AKMM, p. 196: with CARA marginal utility `α exp(−αc)`, the first-order condition is
`α exp(−αR_fW) E₀[exp(−α(Z − R_f)A)(Z − R_f)] = 0`, which does not involve `W`. -/
theorem portfolio_cara_foc (p : S → ℝ) (Rf α W A : ℝ) (Z : S → ℝ) :
    ∑ s, p s * (α * exp (-α * pf_cons Rf Z W A s) * (Z s - Rf)) =
      α * exp (-α * Rf * W) * ∑ s, p s * (exp (-α * (Z s - Rf) * A) * (Z s - Rf)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have : -α * pf_cons Rf Z W A s = -α * Rf * W + -α * (Z s - Rf) * A := by
    simp only [pf_cons]; ring
  rw [this, exp_add]
  ring

/-- **AKMM, p. 196: CARA portfolios do not depend on wealth.** With `u(c) = −exp(−αc)` the
objective at `W′` is `exp(−αR_f(W′ − W))` times the objective at `W`, so `A` is optimal at `W`
iff it is optimal at `W′`. -/
theorem portfolio_cara_invariant (p : S → ℝ) (Rf α : ℝ) (Z : S → ℝ) (W W' A : ℝ) :
    (∀ A', pf_value (fun c => -exp (-α * c)) p Rf Z W' A' =
      exp (-α * Rf * (W' - W)) * pf_value (fun c => -exp (-α * c)) p Rf Z W A') ∧
    ((∀ A', pf_value (fun c => -exp (-α * c)) p Rf Z W A' ≤
        pf_value (fun c => -exp (-α * c)) p Rf Z W A) ↔
      ∀ A', pf_value (fun c => -exp (-α * c)) p Rf Z W' A' ≤
        pf_value (fun c => -exp (-α * c)) p Rf Z W' A) := by
  have key : ∀ A', pf_value (fun c => -exp (-α * c)) p Rf Z W' A' =
      exp (-α * Rf * (W' - W)) * pf_value (fun c => -exp (-α * c)) p Rf Z W A' := fun A' => by
    simp only [pf_value, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : -α * pf_cons Rf Z W' A' s = -α * Rf * (W' - W) + -α * pf_cons Rf Z W A' s := by
      simp only [pf_cons]; ring
    rw [this, exp_add]
    ring
  have hpos : 0 < exp (-α * Rf * (W' - W)) := exp_pos _
  refine ⟨key, ⟨fun h A' => ?_, fun h A' => ?_⟩⟩
  · rw [key, key]; exact mul_le_mul_of_nonneg_left (h A') hpos.le
  · have h' := h A'
    rw [key, key] at h'
    exact le_of_mul_le_mul_left h' hpos

/-- AKMM, p. 196: "the rich have a lower risky share than poorer households": with the same
positive risky amount `A`, the share `A/W` falls as wealth rises. -/
theorem portfolio_cara_share_falls {A W W' : ℝ} (hA : 0 < A) (hW : 0 < W) (hWW' : W < W') :
    A / W' < A / W :=
  div_lt_div_of_pos_left hA hW hWW'

end AKMM.Uncertainty

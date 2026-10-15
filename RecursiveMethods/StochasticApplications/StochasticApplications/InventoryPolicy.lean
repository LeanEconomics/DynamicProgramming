/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.InventoryResults

/-!
# Production and inventory accumulation: monotone policies

SLP §10.5, Exercises 10.5e–g, pp. 299–300. The book derives from the first-order conditions
(3)–(4) that a larger stock means more storage and less production: if `x₂ > x₁` then
`Y(x₂) > Y(x₁)` or `Y(x₂) = Y(x₁) = 0` (10.5e–f), and `N(x₂) < N(x₁)` (10.5g).

* `ex_10_5e`: the weak form, `x ≤ x′ ⇒ Y(x) ≤ Y(x′)` and `N(x′) ≤ N(x)`, without first-order
  conditions or differentiability. The proof is Topkis's: order choices by `(y, −n)`. The
  constraint `[0, x] × [0, N̄]` is ascending in `x`; `U(x − y)` has increasing differences in
  `(x, y)` (`U_sub_submod`); the costs are separable; and `v(y + nω)` has decreasing differences
  in `(y, n)` because `v` is concave (`concave_sum_submod`). Uniqueness of the maximizer
  (`inv_policy`) then forces the order.

The strict statements of 10.5e and 10.5g, and 10.5d (consumption `x − Y(x)` strictly
increasing), rest on the first-order conditions and are not formalised; 10.5f's sign argument
is `ex_10_5f`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

variable {U H c : ℝ → ℝ} {β Ubar Nbar ω₁ ω₂ : ℝ} {μ : Measure (Icc ω₁ ω₂)}
  [IsProbabilityMeasure μ]

/-- For concave `g` and `p ≤ m₁, m₂ ≤ q` with `m₁ + m₂ = p + q`,
`g(p) + g(q) ≤ g(m₁) + g(m₂)`. -/
theorem concave_four {S : Set ℝ} {g : ℝ → ℝ} (hg : ConcaveOn ℝ S g) {p q m₁ m₂ : ℝ} (hp : p ∈ S)
    (hq : q ∈ S) (hpm : p ≤ m₁) (hmq : m₁ ≤ q) (hsum : m₁ + m₂ = p + q) :
    g p + g q ≤ g m₁ + g m₂ := by
  rcases eq_or_lt_of_le (hpm.trans hmq) with hpq | hpq
  · have h1 : m₁ = p := le_antisymm (hpq ▸ hmq) hpm
    have h2 : m₂ = q := by linarith
    rw [h1, h2]
  · have hd : 0 < q - p := sub_pos.2 hpq
    set l := (q - m₁) / (q - p)
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hd.le
    have hl1 : 0 ≤ 1 - l := by
      rw [sub_nonneg, div_le_one hd]; linarith
    have e1 : l • p + (1 - l) • q = m₁ := by
      simp only [smul_eq_mul, l]; field_simp; ring
    have e2 : (1 - l) • p + l • q = m₂ := by
      rw [show m₂ = p + q - m₁ by linarith]
      simp only [smul_eq_mul, l]; field_simp; ring
    have c1 := hg.2 hp hq hl0 hl1 (by ring)
    have c2 := hg.2 hp hq hl1 hl0 (by ring)
    rw [e1] at c1
    rw [e2] at c2
    simp only [smul_eq_mul] at c1 c2
    linarith

/-- A concave function of a sum has decreasing differences:
`g(a + b) + g(a′ + b′) ≤ g(min{a, a′} + max{b, b′}) + g(max{a, a′} + min{b, b′})`. -/
theorem concave_sum_submod {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Ici 0) g) {a a' b b' : ℝ} (ha : 0 ≤ a)
    (ha' : 0 ≤ a') (hb : 0 ≤ b) (hb' : 0 ≤ b') :
    g (a + b) + g (a' + b') ≤ g (min a a' + max b b') + g (max a a' + min b b') := by
  rcases le_total a a' with h1 | h1 <;> rcases le_total b b' with h2 | h2
  · rw [min_eq_left h1, max_eq_right h2, max_eq_right h1, min_eq_left h2]
    exact concave_four hg (mem_Ici.2 (by positivity)) (mem_Ici.2 (by positivity)) (by linarith)
      (by linarith) (by ring)
  · rw [min_eq_left h1, max_eq_left h2, max_eq_right h1, min_eq_right h2]
  · rw [min_eq_right h1, max_eq_right h2, max_eq_left h1, min_eq_left h2, add_comm]
  · rw [min_eq_right h1, max_eq_left h2, max_eq_left h1, min_eq_right h2]
    have := concave_four hg (mem_Ici.2 (by positivity : 0 ≤ a' + b'))
      (mem_Ici.2 (by positivity : 0 ≤ a + b)) (by linarith : a' + b' ≤ a' + b) (by linarith)
      (by ring : a' + b + (a + b') = a' + b' + (a + b))
    linarith

/-- `U(x − y)` has increasing differences in `(x, y)`: for `x ≤ x′`,
`U(x − y) + U(x′ − y′) ≤ U(x − min{y, y′}) + U(x′ − max{y, y′})`. -/
theorem U_sub_submod (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {x x' y y' : ℝ} (hxx : x ≤ x')
    (hy : y ≤ x) (hy' : y' ≤ x') :
    U (x - y) + U (x' - y') ≤ U (x - min y y') + U (x' - max y y') := by
  rcases le_total y y' with h1 | h1
  · rw [min_eq_left h1, max_eq_right h1]
  · rw [min_eq_right h1, max_eq_left h1]
    exact concave_four h.U_conc.concaveOn (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith))
      (by linarith) (by linarith) (by ring)

theorem min_add_max_apply (f : ℝ → ℝ) (a b : ℝ) : f (min a b) + f (max a b) = f a + f b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, add_comm]

omit [IsProbabilityMeasure μ] in
/-- The continuation integrand in terms of `v(·, ω′)` extended to `ℝ`. -/
theorem v_invφ (hω : 0 ≤ ω₁) (v : Ici (0 : ℝ) × Icc ω₁ ω₂ → ℝ) (x : Ici (0 : ℝ)) {p : ℝ × ℝ}
    (hy : 0 ≤ p.1) (hn : 0 ≤ p.2) (ω' : Icc ω₁ ω₂) :
    v (invφ (x, p, ω'), ω') = liftS (fun x => v (x, ω')) (p.1 + p.2 * ω'.1) := by
  have hm : p.1 + p.2 * ω'.1 ∈ Ici (0 : ℝ) :=
    mem_Ici.2 (add_nonneg hy (mul_nonneg hn (hω.trans ω'.2.1)))
  rw [liftS_of_mem _ hm, show invφ (x, p, ω') = ⟨_, hm⟩ from Subtype.ext (invφ_val _ _ _ hω hy hn)]

/-- **Exercise 10.5e** (weak form). A larger stock means (weakly) more storage and less
production: `x ≤ x′` implies `Y(x) ≤ Y(x′)` and `N(x′) ≤ N(x)`. -/
theorem ex_10_5e (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) {x x' : Ici (0 : ℝ)} (hxx : x.1 ≤ x'.1) (ω : Icc ω₁ ω₂)
    {P P' : ℝ × ℝ} (hP : P ∈ policy (invModel μ U H c β Nbar) v (x, ω))
    (hP' : P' ∈ policy (invModel μ U H c β Nbar) v (x', ω)) : P.1 ≤ P'.1 ∧ P'.2 ≤ P.2 := by
  have hω := h.ω_nonneg
  have a1 := hP.1; have a2 := hP'.1
  have hy : 0 ≤ P.1 := a1.1.1; have hy' : 0 ≤ P'.1 := a2.1.1
  have hn : 0 ≤ P.2 := a1.2.1; have hn' : 0 ≤ P'.2 := a2.2.1
  have hyx : P.1 ≤ x.1 := a1.1.2; have hyx' : P'.1 ≤ x'.1 := a2.1.2
  set Pm : ℝ × ℝ := (min P.1 P'.1, max P.2 P'.2)
  set Pj : ℝ × ℝ := (max P.1 P'.1, min P.2 P'.2)
  have hPm : Pm ∈ invΓ Nbar (x, ω) :=
    ⟨⟨le_min hy hy', (min_le_left _ _).trans hyx⟩, hn.trans (le_max_left _ _),
      max_le a1.2.2 a2.2.2⟩
  have hPj : Pj ∈ invΓ Nbar (x', ω) :=
    ⟨⟨hy.trans (le_max_left _ _), max_le (hyx.trans hxx) hyx'⟩, le_min hn hn',
      (min_le_left _ _).trans a1.2.2⟩
  -- the continuation values have decreasing differences
  have hE : ∫ ω', v (invφ (x, P, ω'), ω') ∂μ + ∫ ω', v (invφ (x', P', ω'), ω') ∂μ ≤
      ∫ ω', v (invφ (x, Pm, ω'), ω') ∂μ + ∫ ω', v (invφ (x', Pj, ω'), ω') ∂μ := by
    rw [← integral_add (integrable_inv v x P) (integrable_inv v x' P'),
      ← integral_add (integrable_inv v x Pm) (integrable_inv v x' Pj)]
    refine integral_mono ((integrable_inv v x P).add (integrable_inv v x' P'))
      ((integrable_inv v x Pm).add (integrable_inv v x' Pj)) fun ω' => ?_
    have hw : 0 ≤ ω'.1 := hω.trans ω'.2.1
    have hg := concaveOn_liftS (inv_strictConcave h hv ω').isConcaveS
    dsimp only
    rw [v_invφ hω v x hy hn, v_invφ hω v x' hy' hn',
      v_invφ hω v x (le_min hy hy') (hn.trans (le_max_left _ _)),
      v_invφ hω v x' (hy.trans (le_max_left _ _)) (le_min hn hn')]
    dsimp only [Pm, Pj]
    rw [max_mul_of_nonneg _ _ hw, min_mul_of_nonneg _ _ hw]
    exact concave_sum_submod hg hy hy' (mul_nonneg hn hw) (mul_nonneg hn' hw)
  have hU := U_sub_submod h hxx hyx hyx'
  have hH := min_add_max_apply H P.1 P'.1
  have hc := min_add_max_apply c P.2 P'.2
  -- so `Pm` does at least as well as `P` at `x`
  have hjle := (inv_max h hv (x', ω)).2 Pj hPj
  have hmle := (inv_max h hv (x, ω)).2 Pm hPm
  have e1 := hP.2
  have e2 := hP'.2
  rw [inv_rhs] at hjle hmle e1 e2
  dsimp only [Pm, Pj] at hjle hmle hE
  have hopt : Pm ∈ policy (invModel μ U H c β Nbar) v (x, ω) := by
    refine ⟨hPm, le_antisymm ?_ hmle⟩
    rw [inv_rhs]
    dsimp only [Pm]
    nlinarith [mul_le_mul_of_nonneg_left hE h.β_pos.le, max_comm P.2 P'.2]
  have hpol := (inv_policy h hv).2
  have heq := (inv_policy h hv).1.unique (x, ω) Pm (hpol (x, ω) ▸ hopt) P (hpol (x, ω) ▸ hP)
  have h1 : min P.1 P'.1 = P.1 := congrArg Prod.fst heq
  have h2 : max P.2 P'.2 = P.2 := congrArg Prod.snd heq
  exact ⟨min_eq_left_iff.1 h1, max_eq_left_iff.1 h2⟩

end StokeyLucasPrescott.StochasticApplications

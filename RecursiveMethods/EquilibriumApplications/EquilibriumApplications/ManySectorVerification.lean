/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManySectorEnvelope
import EquilibriumApplications.GrowthCertaintySequential

/-!
# Pricing securities: the equilibrium price makes no trade optimal (Ex 16.2(d), converse)

SLP §16.2, p. 483. `ex_16_2_eq2` showed that no trade at `A = 0` in every state forces the pricing
equation (2). This module proves the converse by a verification argument: if `q` satisfies (2)
in every state, then every solution `w` of (1) bounded on `D` has the supergradient `U′(c(s))` at
`A = 0`,

  `w(A, s) ≤ w(0, s) + U′(c(s)) A` for all `(A, s) ∈ D`,

and `b = 0` is optimal at `A = 0` in every state; with concavity of `w` (`ms_sec_fixed_concave`),
`w₁(0, s) = U′(c(s))`, the book's (d).

Proof: `e(A, s) = w(A, s) − w(0, s) − U′(c(s))A` is bounded on `D` (`U′(c)(c − qB)` bounded) and,
by the tangent inequality for `U`, the Bellman equation and (2), `e ≤ β sup e`; so `e ≤ βⁿ M → 0`.

* `ms_sec_supergradient`: the supergradient inequality.
* **Exercise 16.2(d), converse** (`ex_16_2d_converse`): (2) in every state implies that `b = 0` is
  optimal at `A = 0` in every state.
* `ex_16_2d_equilibrium`: in equilibrium, `w(·, s)` is differentiable at `0` with
  `w₁(0, s) = U′(c(s))`.

**Hypotheses.** `c > 0`, `U` concave and differentiable on `(0, ∞)` with `U′ > 0`, and
`U′(c(s))(c(s) − q(s)B)` bounded above (automatic if the state space is compact).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

variable {Sx : Type*} [TopologicalSpace Sx] {Zf : Type*} [Fintype Zf]
  {U : ℝ → ℝ} {c q : Sx → ℝ} {R π : Sx → Zf → ℝ} {nxt : Sx → Zf → Sx} {B β : ℝ}

/-- The key step: if `w(A′, s′) ≤ w(0, s′) + U′(c(s′))A′ + E` on `D`, then
`w(A, s) ≤ w(0, s) + U′(c(s))A + βE` on `D` (tangent inequality, Bellman equation and (2)). -/
theorem ms_sec_super_step (D : MsSecData U c q R π nxt B β) (hU : ConcaveOn ℝ (Ici 0) U)
    {dU : ℝ → ℝ} (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) (hc : ∀ s, 0 < c s)
    (h2 : ∀ s, q s * dU (c s) = β * ∑ z', π s z' * (dU (c (nxt s z')) * R s z'))
    {w : ℝ × Sx → ℝ} (hw : MsSecBellman U c q R π nxt B β w) {E : ℝ}
    (hE : ∀ A s, q s * B - c s ≤ A → w (A, s) ≤ w (0, s) + dU (c s) * A + E)
    {A : ℝ} {s : Sx} {b : ℝ} (hb : B ≤ b) (hbf : q s * b ≤ c s + A) :
    msSecObj U c q R π nxt β w A s b ≤ w (0, s) + dU (c s) * A + β * E := by
  have hq := D.q_pos s
  have h0dom : q s * B - c s ≤ 0 := by nlinarith [D.B_neg, hc s]
  have hge0 := (hw 0 s h0dom).1 0 D.B_neg.le (by rw [mul_zero, add_zero]; exact (hc s).le)
  simp only [msSecObj, add_zero, mul_zero, sub_zero, zero_mul] at hge0
  have ht := gc_concave_le_tangent hU (hc s) (by linarith : (0 : ℝ) ≤ c s + A - q s * b)
    (hdU _ (hc s))
  have hsum : ∑ z', π s z' * w (b * R s z', nxt s z') ≤
      ∑ z', π s z' * w (0, nxt s z') + b * ∑ z', π s z' * (dU (c (nxt s z')) * R s z') + E := by
    calc ∑ z', π s z' * w (b * R s z', nxt s z')
        ≤ ∑ z', (π s z' * w (0, nxt s z') + b * (π s z' * (dU (c (nxt s z')) * R s z')) +
            π s z' * E) := Finset.sum_le_sum fun z' _ => by
          have h := hE _ _ (ms_sec_next_mem D s hb z')
          have hπ := D.π_nonneg s z'
          nlinarith [mul_le_mul_of_nonneg_left h hπ]
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
            D.π_sum, one_mul]
  have e2 := h2 s
  have hβ := D.beta_pos
  simp only [msSecObj]
  have key : β * (b * ∑ z', π s z' * (dU (c (nxt s z')) * R s z')) = b * (q s * dU (c s)) := by
    rw [e2]; ring
  nlinarith [mul_le_mul_of_nonneg_left hsum hβ.le]

/-- **The supergradient inequality**: if `q` satisfies (2) in every state, every solution `w` of
(1) bounded on `D` satisfies `w(A, s) ≤ w(0, s) + U′(c(s))A` on `D`. -/
theorem ms_sec_supergradient (D : MsSecData U c q R π nxt B β) (hU : ConcaveOn ℝ (Ici 0) U)
    {dU : ℝ → ℝ} (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) (hdUpos : ∀ x, 0 < x → 0 < dU x)
    (hc : ∀ s, 0 < c s)
    (h2 : ∀ s, q s * dU (c s) = β * ∑ z', π s z' * (dU (c (nxt s z')) * R s z'))
    (hK : ∃ K, ∀ s, dU (c s) * (c s - q s * B) ≤ K) {w : ℝ × Sx → ℝ}
    (hw : MsSecBellman U c q R π nxt B β w) (hwb : ∃ C, ∀ p ∈ msSecDom c q B, |w p| ≤ C) :
    ∀ A s, q s * B - c s ≤ A → w (A, s) ≤ w (0, s) + dU (c s) * A := by
  obtain ⟨K, hK⟩ := hK
  obtain ⟨C, hC⟩ := hwb
  set M := 2 * C + max K 0 with hM
  have key : ∀ n : ℕ, ∀ A s, q s * B - c s ≤ A →
      w (A, s) ≤ w (0, s) + dU (c s) * A + β ^ n * M := by
    intro n
    induction n with
    | zero =>
      intro A s hA
      have hq := D.q_pos s
      have h0dom : q s * B - c s ≤ 0 := by nlinarith [D.B_neg, hc s]
      have h1 := (abs_le.1 (hC (A, s) hA)).2
      have h2' := (abs_le.1 (hC (0, s) h0dom)).1
      have hd := hdUpos _ (hc s)
      have hKs := hK s
      have : -(dU (c s) * A) ≤ max K 0 := by
        rcases le_total A 0 with hneg | hpos
        · have : -(dU (c s) * A) ≤ dU (c s) * (c s - q s * B) := by nlinarith
          exact this.trans (hKs.trans (le_max_left _ _))
        · have : -(dU (c s) * A) ≤ 0 := by nlinarith
          exact this.trans (le_max_right _ _)
      rw [pow_zero, one_mul, hM]
      linarith
    | succ n ih =>
      intro A s hA
      obtain ⟨b, hb, hbf, e⟩ := (hw A s hA).2
      have := ms_sec_super_step D hU hdU hc h2 hw ih hb hbf
      rw [e, pow_succ, mul_comm (β ^ n) β, mul_assoc]
      exact this
  intro A s hA
  have hlim : Tendsto (fun n : ℕ => w (0, s) + dU (c s) * A + β ^ n * M) atTop
      (𝓝 (w (0, s) + dU (c s) * A)) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one D.beta_pos.le D.beta_lt_one).mul_const M)
  exact ge_of_tendsto' hlim fun n => key n A s hA

/-- **Exercise 16.2(d), converse**: if the price `q` satisfies the pricing equation (2) in every
state, then for every solution `w` of (1) bounded on `D`, `b = 0` (no trade, `δ = 0`) is optimal at
`A = 0` in every state. -/
theorem ex_16_2d_converse (D : MsSecData U c q R π nxt B β) (hU : ConcaveOn ℝ (Ici 0) U)
    {dU : ℝ → ℝ} (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) (hdUpos : ∀ x, 0 < x → 0 < dU x)
    (hc : ∀ s, 0 < c s)
    (h2 : ∀ s, q s * dU (c s) = β * ∑ z', π s z' * (dU (c (nxt s z')) * R s z'))
    (hK : ∃ K, ∀ s, dU (c s) * (c s - q s * B) ≤ K) {w : ℝ × Sx → ℝ}
    (hw : MsSecBellman U c q R π nxt B β w) (hwb : ∃ C, ∀ p ∈ msSecDom c q B, |w p| ≤ C)
    (s : Sx) : w (0, s) = msSecObj U c q R π nxt β w 0 s 0 := by
  have hsup := ms_sec_supergradient D hU hdU hdUpos hc h2 hK hw hwb
  have hq := D.q_pos s
  have h0dom : q s * B - c s ≤ 0 := by nlinarith [D.B_neg, hc s]
  obtain ⟨b, hb, hbf, e⟩ := (hw 0 s h0dom).2
  have hge := (hw 0 s h0dom).1 0 D.B_neg.le (by rw [mul_zero, add_zero]; exact (hc s).le)
  have hge0 : msSecObj U c q R π nxt β w 0 s 0 = U (c s) + β * ∑ z', π s z' * w (0, nxt s z') := by
    simp only [msSecObj, add_zero, mul_zero, sub_zero, zero_mul]
  apply le_antisymm _ hge
  rw [e]
  have hstep : msSecObj U c q R π nxt β w 0 s b ≤ msSecObj U c q R π nxt β w 0 s 0 := by
    have ht := gc_concave_le_tangent hU (hc s) (by linarith : (0 : ℝ) ≤ c s + 0 - q s * b)
      (hdU _ (hc s))
    have hsum : ∑ z', π s z' * w (b * R s z', nxt s z') ≤
        ∑ z', π s z' * w (0, nxt s z') + b * ∑ z', π s z' * (dU (c (nxt s z')) * R s z') := by
      calc ∑ z', π s z' * w (b * R s z', nxt s z')
          ≤ ∑ z', (π s z' * w (0, nxt s z') + b * (π s z' * (dU (c (nxt s z')) * R s z'))) :=
            Finset.sum_le_sum fun z' _ => by
              have h := hsup _ _ (ms_sec_next_mem D s hb z')
              have hπ := D.π_nonneg s z'
              nlinarith [mul_le_mul_of_nonneg_left h hπ]
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have key : β * (b * ∑ z', π s z' * (dU (c (nxt s z')) * R s z')) = b * (q s * dU (c s)) := by
      rw [h2 s]; ring
    rw [hge0]
    simp only [msSecObj]
    nlinarith [mul_le_mul_of_nonneg_left hsum D.beta_pos.le]
  exact hstep

/-- **In equilibrium the book's (d) holds**: if `q` satisfies (2) in every state and `w` (bounded on
`D`, concave in `A`) solves (1), then `w(·, s)` is differentiable at `0` with
`w₁(0, s) = U′(c(s))`. -/
theorem ex_16_2d_equilibrium (D : MsSecData U c q R π nxt B β)
    (hUs : StrictConcaveOn ℝ (Ici 0) U) {dU : ℝ → ℝ} (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x)
    (hdUpos : ∀ x, 0 < x → 0 < dU x) (hc : ∀ s, 0 < c s)
    (h2 : ∀ s, q s * dU (c s) = β * ∑ z', π s z' * (dU (c (nxt s z')) * R s z'))
    (hK : ∃ K, ∀ s, dU (c s) * (c s - q s * B) ≤ K) {w : ℝ × Sx → ℝ}
    (hw : MsSecBellman U c q R π nxt B β w) (hwb : ∃ C, ∀ p ∈ msSecDom c q B, |w p| ≤ C)
    (hcv : MsSecConcave c q B w) (s : Sx) :
    HasDerivAt (fun A => w (A, s)) (dU (c s)) 0 := by
  have hopt := ex_16_2d_converse D hUs.concaveOn hdU hdUpos hc h2 hK hw hwb s
  have := ex_16_2d D hdU hw hcv (s := s) D.B_neg.le hopt (by rw [mul_zero, sub_zero]; exact hc s)
  rwa [mul_zero, sub_zero] at this

end StokeyLucasPrescott.EquilibriumApplications

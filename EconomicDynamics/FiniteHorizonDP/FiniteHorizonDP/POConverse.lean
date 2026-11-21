/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.POVerification
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Optimal plans follow the Bellman policy: Theorem 6.3.3, corrected

Miao, §6.3, pp. 169–172. **Theorem 6.3.3** claims that every optimal plan `π*` of (5.5)
satisfies `π*_0 ∈ G_0(s_0)` and `π*_t(sᵗ) ∈ G_t(s_t)` for **all** `t` and `sᵗ`.

**Correction.** This holds only for almost every history: changing an optimal plan on a set of
histories of probability zero leaves its value unchanged and keeps it optimal.
* `theorem_6_3_3` proves `π*_0 ∈ G_0(s_0)` and, for `t < T`, `π*_t(sᵗ) ∈ G_t(s_t)` for
  `μᵗ(s₀, ·; π*)`-almost every history `sᵗ` (the histories that `π*` reaches), when `β > 0`.
  The core induction is `po_converse_core`.
* `theorem_6_3_3_counterexample`: a process on `S = A = Bool` with `T = 2` (the next state is
  always `true`; the reward is `1` for the action `true`) and an optimal plan with
  `π*_1(false) = false ∉ G_1(false) = {true}`; the history `s₁ = false` has probability zero.

The book's hypotheses that `G_t` be nonempty with a measurable selection are not needed: the
proof below only uses that `V_t = w_t` solves the Bellman equation. The book's argument via
Theorem 6.3.2 is replaced by the definition of `V_1` as a supremum. Also needed, and assumed:
`β > 0` (with `β = 0` the decisions after date `0` are unrestricted), and the integrability of
`V_{t+1}` against `P_{t+1}(s, a; ·)` for `a ∈ Γ(s)`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

theorem po_measurableSet_G {M : MDP S A} {w : ℕ → S → ℝ} {j : ℕ} (hu : Measurable (M.u j))
    (hw : Measurable (w (j + 1))) (hw' : Measurable (w j)) (hP : M.IsMarkov) {s : S}
    {π : Plan S A} (hπm : Measurable (π j)) (hπΓ : ∀ h, π j h ∈ M.Γ (lastState s h)) :
    MeasurableSet {h : Fin j → S | π j h ∈ po_G M w j (lastState s h)} := by
  have hk := isSFiniteKernel_stepKernel M hP s π j
  have hI : Measurable fun h : Fin j → S =>
      ∫ s', w (j + 1) s' ∂M.P j (lastState s h, π j h) := by
    have := (hw.stronglyMeasurable.integral_kernel (κ := stepKernel M s π j)).measurable
    have heq : (fun h : Fin j → S => ∫ s', w (j + 1) s' ∂M.P j (lastState s h, π j h)) =
        fun h => ∫ s', w (j + 1) s' ∂stepKernel M s π j h := by
      funext h
      rw [stepKernel_apply M s hπm]
    rw [heq]
    exact this
  have hF : Measurable fun h : Fin j → S => po_bellmanVal M w j (lastState s h) (π j h) :=
    (hu.comp ((measurable_lastState s j).prodMk hπm)).add (measurable_const.mul hI)
  have : {h : Fin j → S | π j h ∈ po_G M w j (lastState s h)} =
      {h | po_bellmanVal M w j (lastState s h) (π j h) = w j (lastState s h)} := by
    ext h
    exact ⟨fun hh => hh.2, fun hh => ⟨hπΓ h, hh⟩⟩
  rw [this]
  exact measurableSet_eq_fun hF (hw'.comp (measurable_lastState s j))

/-- **The induction behind Theorem 6.3.3**, at date `0` of a process `M` with horizon `n`: if
`w_j` is the value from date `j` (`j ≤ n`), measurable, and satisfies the Bellman inequalities
(`w` solves the Bellman equation), `β > 0`, and `π` is a feasible plan from `s` with integrable
rewards and `J₀ⁿ(s, π) = w₀(s)`, then `π_j(sʲ) ∈ G_j(s_j)` for `μʲ(s, ·; π)`-a.e. `sʲ`. -/
theorem po_converse_core :
    ∀ (n : ℕ) (M : MDP S A) (w : ℕ → S → ℝ), M.IsMarkov → 0 < M.β →
      (∀ j < n, Measurable (M.u j)) → (∀ j ≤ n, Measurable (w j)) →
      (∀ j ≤ n, ∀ s, V0 (po_shift M j) (n - j) s = w j s) →
      (∀ j < n, ∀ s, ∀ a ∈ M.Γ s, Integrable (w (j + 1)) (M.P j (s, a)) ∧
        po_bellmanVal M w j s a ≤ w j s) →
      ∀ (s : S) (π : Plan S A), π ∈ feasiblePlans M (n : ℕ∞) s → po_IntPlan M n s π →
      J0T M n s π = w 0 s →
      ∀ j < n, ∀ᵐ h ∂mu M s π j, π j h ∈ po_G M w j (lastState s h) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro M w hP hβ hu hwm hV hB s π hπ hIπ hopt
    have hπm := po_plan_meas hπ
    have ha : π 0 Fin.elim0 ∈ M.Γ s := hπ.2 0 (po_cast_lt.2 (Nat.succ_pos n)) Fin.elim0
    obtain ⟨hint, hle⟩ := hB 0 (Nat.succ_pos n) s _ ha
    have hJi := po_integrable_J0T_cont hP hπm hIπ
    have hJle : ∀ s', J0T (po_shift M 1) n s' (po_cont π s') ≤ w 1 s' := fun s' => by
      have h1 := po_J_le_V0 (po_cont_feasible hπ s')
      have h2 := hV 1 (by omega) s'
      simp only [Nat.add_sub_cancel] at h2
      rw [h2] at h1
      exact EReal.coe_le_coe_iff.1 h1
    have hrec := po_J0T_succ hP hπm hIπ
    rw [hopt] at hrec
    have hmono : ∫ s', J0T (po_shift M 1) n s' (po_cont π s') ∂M.P 0 (s, π 0 Fin.elim0) ≤
        ∫ s', w 1 s' ∂M.P 0 (s, π 0 Fin.elim0) := integral_mono hJi hint hJle
    simp only [po_bellmanVal] at hle
    have hEq : ∫ s', J0T (po_shift M 1) n s' (po_cont π s') ∂M.P 0 (s, π 0 Fin.elim0) =
        ∫ s', w 1 s' ∂M.P 0 (s, π 0 Fin.elim0) := by
      refine le_antisymm hmono ?_
      have := mul_le_mul_of_nonneg_left hmono hβ.le
      by_contra hne
      have hlt : ∫ s', J0T (po_shift M 1) n s' (po_cont π s') ∂M.P 0 (s, π 0 Fin.elim0) <
          ∫ s', w 1 s' ∂M.P 0 (s, π 0 Fin.elim0) := lt_of_not_ge hne
      have := mul_lt_mul_of_pos_left hlt hβ
      linarith
    have hG0 : po_bellmanVal M w 0 s (π 0 Fin.elim0) = w 0 s := by
      simp only [po_bellmanVal]
      rw [← hEq]
      linarith
    have hae : ∀ᵐ s' ∂M.P 0 (s, π 0 Fin.elim0),
        J0T (po_shift M 1) n s' (po_cont π s') = w 1 s' := by
      have hnn : 0 ≤ᵐ[M.P 0 (s, π 0 Fin.elim0)]
          fun s' => w 1 s' - J0T (po_shift M 1) n s' (po_cont π s') :=
        Filter.Eventually.of_forall fun s' => sub_nonneg.2 (hJle s')
      have h0 : ∫ s', (w 1 s' - J0T (po_shift M 1) n s' (po_cont π s'))
          ∂M.P 0 (s, π 0 Fin.elim0) = 0 := by
        rw [integral_sub hint hJi, hEq, sub_self]
      have := (integral_eq_zero_iff_of_nonneg_ae hnn (hint.sub hJi)).1 h0
      filter_upwards [this] with s' hs'
      have : w 1 s' - J0T (po_shift M 1) n s' (po_cont π s') = 0 := hs'
      linarith
    intro j hj
    cases j with
    | zero =>
      refine Filter.Eventually.of_forall fun h => ?_
      have : h = Fin.elim0 := Subsingleton.elim _ _
      subst this
      exact ⟨ha, hG0⟩
    | succ j =>
      have hIH := ih (po_shift M 1) (fun j => w (j + 1)) (po_shift_isMarkov hP 1) hβ
        (fun k hk => hu (k + 1) (by omega)) (fun k hk => hwm (k + 1) (by omega))
        (fun k hk s => by
          rw [po_shift_shift, Nat.add_comm 1 k]
          have := hV (k + 1) (by omega) s
          rwa [show n + 1 - (k + 1) = n - k by omega] at this)
        (fun k hk s a ha => hB (k + 1) (by omega) s a ha)
      refine po_ae_mu_succ hP s (fun k hk => hπm k (by omega))
        (po_measurableSet_G (hu (j + 1) (by omega)) (hwm (j + 2) (by omega))
          (hwm (j + 1) (by omega)) hP (hπm (j + 1) (by omega))
          fun h => hπ.2 (j + 1) (po_cast_lt.2 hj) h) ?_
      filter_upwards [hae, po_ae_IntPlan_cont hP hπm hIπ] with s' h1 h2
      have := hIH s' (po_cont π s') (po_cont_feasible hπ s') h2 h1 j (by omega)
      filter_upwards [this] with h hh
      rw [lastState_cons]
      exact hh

/-- **Theorem 6.3.3** (Miao, p. 170), corrected. Let the value functions `V_t = w_t` (`t ≤ T`)
be measurable, real-valued and solve the Bellman equation (6.17)/(6.19), with the integrals of
`w_{t+1}` against `P_{t+1}(s, a; ·)`, `a ∈ Γ(s)`, existing; let Assumption 5.1.3 hold and
`β > 0`. Then any optimal plan `π*` for (5.5) from `s₀` satisfies `π*_0 ∈ G_0(s₀)` and, for every
`t < T`, `π*_t(sᵗ) ∈ G_t(s_t)` for `μᵗ(s₀, ·; π*)`-almost every history `sᵗ`. (The book's "for
all `sᵗ`" is false: `theorem_6_3_3_counterexample`.) -/
theorem theorem_6_3_3 {M : MDP S A} (hP : M.IsMarkov) (hβ : 0 < M.β) {T : ℕ}
    (hI : Assumption513 M T) {w : ℕ → S → ℝ} (hwm : ∀ t ≤ T, Measurable (w t))
    (hV : ∀ t ≤ T, ∀ s, V0 (po_shift M t) (T - t) s = w t s)
    (hint : ∀ t < T, ∀ s, ∀ a ∈ M.Γ s, Integrable (w (t + 1)) (M.P t (s, a)))
    (hsol : ∀ t < T, ∀ s, po_SolvesAt M w t s) {s₀ : S} {π : Plan S A}
    (hopt : IsOptimalPlan0 M T s₀ π) :
    (0 < T → π 0 Fin.elim0 ∈ po_G M w 0 s₀) ∧
      ∀ t < T, ∀ᵐ h ∂mu M s₀ π t, π t h ∈ po_G M w t (lastState s₀ h) := by
  have hJ : J0T M T s₀ π = w 0 s₀ := by
    have h1 := hopt.2
    have h2 := hV 0 (Nat.zero_le T) s₀
    rw [po_shift_zero, Nat.sub_zero] at h2
    rw [h2] at h1
    exact (EReal.coe_eq_coe_iff.1 h1).symm
  have hc := po_converse_core T M w hP hβ (fun j hj => hI.1 j hj) hwm hV
    (fun j hj s a ha => ⟨hint j hj s a ha, po_bellmanVal_le (hsol j hj s) ha⟩) s₀ π hopt.1
    (po_intPlan_of_assumption513 hI hopt.1) hJ
  refine ⟨fun hT => ?_, hc⟩
  have := hc 0 hT
  rw [mu_zero, ae_dirac_iff (Subsingleton.measurableSet)] at this
  exact this

end Miao.FiniteHorizonDP

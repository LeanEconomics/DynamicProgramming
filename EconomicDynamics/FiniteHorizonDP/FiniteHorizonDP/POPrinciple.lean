/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.POHistory

/-!
# The principle of optimality: the sequence problem from a history and the Bellman equation

Miao, §6.3, pp. 163–167, in the Markov decision process model (5.1) of Chapter 5 with horizon
`T < ∞`. A history `sᵗ = (s₀, …, s_t)` is a function `Fin (t + 1) → S`.

* Plans from a history (p. 163): a plan from `sᵗ` is a feasible plan of the process from date
  `t` started at `s_t` (`po_plansFrom`): `π_t ∈ Γ(s_t)` and measurable `π_{t+j} : Sʲ → A` with
  `π_{t+j}(s_{t+1}, …, s_{t+j}) ∈ Γ(s_{t+j})`. Continuation plans `C(π, s_{t+1})` are
  `po_cont`, and they are plans from `s^{t+1}` (`po_cont_mem_plansFrom`).
* The measures (6.12) (`po_muFrom`, `eq_6_12`), the objective (6.13) (`po_JFrom`, `eq_6_13`,
  `eq_6_13_terminal`) and the sequence problem (6.14) (`po_VFrom`, `eq_6_14`,
  `po_VFrom_terminal`, `po_VFrom_zero`: the original problem (5.5) is the case `t = 0`).
* **Lemma 6.3.1** (`lemma_6_3_1`): `J_t(sᵗ, π) = u_t(s_t, π_t) + β ∫ J_{t+1}(s^{t+1}, C(π,
  s_{t+1})) P_{t+1}(s_t, π_t; ds_{t+1})`.
* **Assumption 6.3.1** (`Assumption631`) and **Theorem 6.3.1** (`theorem_6_3_1`): the value
  functions satisfy the Bellman equation (6.17), `V_T = u_T`, and `V_t(sᵗ)` depends on `sᵗ`
  only through `s_t`. The Bellman step at one date is `po_bellman_step`.

**Departures from the book.**
1. *Integrability.* The book's Assumption 5.1.3 is stated for the problem from date `0`, but the
   proofs of §6.3 use it for the problems from every date `t` (the plans from `sᵗ` are not plans
   from `s₀`). `po_Assumption513` asks for it at every date. With bounded measurable rewards it
   holds (`po_assumption513_of_bounded`).
2. *Assumption 6.3.1(b).* The book asks the ε-optimal plans `π^{sᵗ}` to be measurable in `sᵗ`
   for each fixed future history `s^{t+j}_{t+1}`, i.e. *separately* measurable. The proof
   glues them into one plan from `s^{t−1}` whose date-`t + j` decision is
   `(s_t, s^{t+j}_{t+1}) ↦ π^{sᵗ}_{t+j}(s^{t+j}_{t+1})`, and Definition 5.1.1 requires that map to
   be measurable on `S^{j+1}`, which separate measurability does not give. `Assumption631` asks
   for *joint* measurability (`po_JointMeas`). The ε-plans are indexed by the current state
   `s_t` rather than the history (by Lemma 6.3.1 and the Markov structure only `s_t` matters).
3. *The integrals in (6.17).* The book takes `∫ V_{t+1} dP_{t+1}(s_t, a_t; ·)` for granted; under
   Assumption 6.3.1 it exists for every `a_t ∈ Γ(s_t)` (part of `theorem_6_3_1`), because
   `J_{t+1}(·, π^{s^{t+1}}) ≤ V_{t+1} ≤ J_{t+1}(·, π^{s^{t+1}}) + ε` with an integrable lower
   bound.
4. *Discounting.* Only `β ≥ 0` is used (Assumption 5.1.2's `β < 1` is not needed for `T < ∞`).
5. *The Markov property* holds by construction: (6.12)–(6.13) involve `sᵗ` only through `s_t`,
   so the book's induction is not needed.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- `Π(sᵗ)`, the feasible plans from the history `sᵗ = (s₀, …, s_t)` (Miao, p. 163): feasible
plans of the process from date `t`, started at `s_t`, over the remaining horizon `T − t`. -/
def po_plansFrom (M : MDP S A) (T t : ℕ) (h : Fin (t + 1) → S) : Set (Plan S A) :=
  feasiblePlans (po_shift M t) ((T - t : ℕ) : ℕ∞) (h (Fin.last t))

/-- `μ_t^{t+j}(sᵗ, ·; π)`, the measure on `Sʲ` of the history `(s_{t+1}, …, s_{t+j})` given the
history `sᵗ` and a plan `π` from `sᵗ` (Miao (6.12), p. 163). -/
noncomputable def po_muFrom (M : MDP S A) (t : ℕ) (h : Fin (t + 1) → S) (π : Plan S A)
    (j : ℕ) : Measure (Fin j → S) :=
  mu (po_shift M t) (h (Fin.last t)) π j

/-- **Miao (6.12)**, p. 163, in recursive form on measurable rectangles:
`μ_t^{t+j+1}(sᵗ, B₁ × ⋯ × B_{j+1}; π) =
∫_{B₁×⋯×B_j} P_{t+j+1}(s_{t+j}, π_{t+j}; B_{j+1}) dμ_t^{t+j}`.
Iterating gives the nested integral printed in (6.12). -/
theorem eq_6_12 {M : MDP S A} (hP : M.IsMarkov) (t : ℕ) (h : Fin (t + 1) → S) {π : Plan S A}
    {j : ℕ} (hπ : Measurable (π j)) {B : Fin (j + 1) → Set S} (hB : ∀ i, MeasurableSet (B i)) :
    po_muFrom M t h π (j + 1) (Set.pi Set.univ B) =
      ∫⁻ h' in Set.pi Set.univ (Fin.init B),
        M.P (j + t) (lastState (h (Fin.last t)) h', π j h') (B (Fin.last j))
        ∂po_muFrom M t h π j :=
  eq_5_2 (po_shift M t) (po_shift_isMarkov hP t) _ hπ hB

/-- `J_t^T(sᵗ, π)`, the discounted expected rewards of a plan `π` from the history `sᵗ`
(Miao (6.13), p. 164). -/
noncomputable def po_JFrom (M : MDP S A) (T t : ℕ) (h : Fin (t + 1) → S) (π : Plan S A) : ℝ :=
  J0T (po_shift M t) (T - t) (h (Fin.last t)) π

/-- **Miao (6.13)**, p. 164: for `t < T`, `J_t^T(sᵗ, π) = u_t(s_t, π_t) +
∑_{j=1}^{T−t−1} βʲ ∫ u_{t+j}(s_{t+j}, π_{t+j}) dμ_t^{t+j} + β^{T−t} ∫ u_T(s_T) dμ_t^T`. -/
theorem eq_6_13 (M : MDP S A) {T t : ℕ} (ht : t < T) (h : Fin (t + 1) → S) (π : Plan S A) :
    po_JFrom M T t h π = M.u t (h (Fin.last t), π 0 Fin.elim0) +
      ∑ j ∈ Finset.Ico 1 (T - t), M.β ^ j *
        ∫ h', M.u (j + t) (lastState (h (Fin.last t)) h', π j h') ∂po_muFrom M t h π j +
      M.β ^ (T - t) * ∫ h', M.uT (lastState (h (Fin.last t)) h') ∂po_muFrom M t h π (T - t) := by
  rw [po_JFrom, eq_5_3 (po_shift M t) (by omega)]
  have e : (po_shift M t).u 0 = M.u t := by simp only [po_shift, zero_add]
  rw [e]
  rfl

theorem po_J0T_zero (M : MDP S A) (s : S) (π : Plan S A) : J0T M 0 s π = M.uT s := by
  rw [J0T, Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, integral_mu_zero, zero_add]
  rfl

/-- Miao, p. 164: at the terminal date `J_T^T(s^T) = u_T(s_T)`. -/
theorem eq_6_13_terminal (M : MDP S A) (T : ℕ) (h : Fin (T + 1) → S) (π : Plan S A) :
    po_JFrom M T T h π = M.uT (h (Fin.last T)) := by
  rw [po_JFrom, Nat.sub_self, po_J0T_zero]
  rfl

/-- `V_t(sᵗ) = sup_{π ∈ Π(sᵗ)} J_t^T(sᵗ, π)`, the value of the sequence problem from `sᵗ`
(Miao (6.14), p. 164), in `[−∞, +∞]`. -/
noncomputable def po_VFrom (M : MDP S A) (T t : ℕ) (h : Fin (t + 1) → S) : EReal :=
  ⨆ π ∈ po_plansFrom M T t h, (po_JFrom M T t h π : EReal)

/-- **Miao (6.14)**, p. 164: the value from `sᵗ` is the value (5.5) of the process from date `t`
started at `s_t`. -/
theorem eq_6_14 (M : MDP S A) (T t : ℕ) (h : Fin (t + 1) → S) :
    po_VFrom M T t h = V0 (po_shift M t) (T - t) (h (Fin.last t)) := rfl

/-- Miao, p. 164: the original problem (5.5) is the case `t = 0` of (6.14). -/
theorem po_VFrom_zero (M : MDP S A) (T : ℕ) (s₀ : S) :
    po_VFrom M T 0 (fun _ => s₀) = V0 M T s₀ := by
  rw [eq_6_14, Nat.sub_zero]
  rfl

theorem po_feasible_zero (M : MDP S A) (s : S) (π : Plan S A) :
    π ∈ feasiblePlans M ((0 : ℕ) : ℕ∞) s :=
  ⟨fun _ ht => absurd (po_cast_lt.1 ht) (Nat.not_lt_zero _),
    fun _ ht => absurd (po_cast_lt.1 ht) (Nat.not_lt_zero _)⟩

theorem po_V0_zero [Nonempty A] (M : MDP S A) (s : S) : V0 M 0 s = M.uT s := by
  refine le_antisymm (iSup₂_le fun π _ => by rw [po_J0T_zero]) ?_
  refine le_iSup₂_of_le (f := fun π (_ : π ∈ feasiblePlans M ((0 : ℕ) : ℕ∞) s) =>
    (J0T M 0 s π : EReal)) (fun _ _ => Classical.arbitrary A) (po_feasible_zero M s _) ?_
  rw [po_J0T_zero]

/-- Miao, p. 164: `V_T(s^T) = u_T(s_T)` (there is no decision at the terminal date). -/
theorem po_VFrom_terminal [Nonempty A] (M : MDP S A) (T : ℕ) (h : Fin (T + 1) → S) :
    po_VFrom M T T h = M.uT (h (Fin.last T)) := by
  rw [eq_6_14, Nat.sub_self, po_V0_zero]
  rfl

/-- Miao, p. 163: the continuation `C(π, s_{t+1})` of a plan from `sᵗ` is a plan from
`s^{t+1} = (sᵗ, s_{t+1})`. -/
theorem po_cont_mem_plansFrom {M : MDP S A} {T t : ℕ} (ht : t < T) {h : Fin (t + 1) → S}
    {π : Plan S A} (hπ : π ∈ po_plansFrom M T t h) (s' : S) :
    po_cont π s' ∈ po_plansFrom M T (t + 1) (Fin.snoc h s') := by
  have hn : T - t = (T - (t + 1)) + 1 := by omega
  unfold po_plansFrom at hπ ⊢
  rw [hn] at hπ
  rw [Fin.snoc_last, ← po_shift_shift]
  exact po_cont_feasible hπ s'

theorem po_J_le_V0 {M : MDP S A} {T : ℕ} {s : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M (T : ℕ∞) s) : (J0T M T s π : EReal) ≤ V0 M T s :=
  le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans M (T : ℕ∞) s) => (J0T M T s π : EReal)) π hπ

theorem po_coe_le_of_forall_sub {x : ℝ} {y : EReal}
    (h : ∀ δ : ℝ, 0 < δ → ((x - δ : ℝ) : EReal) ≤ y) : (x : EReal) ≤ y := by
  induction y using EReal.rec with
  | bot => exact absurd (le_bot_iff.1 (h 1 one_pos)) (EReal.coe_ne_bot _)
  | top => exact le_top
  | coe r =>
    refine EReal.coe_le_coe_iff.2 (le_of_forall_pos_le_add fun δ hδ => ?_)
    have := EReal.coe_le_coe_iff.1 (h δ hδ)
    linarith

/-- **Assumption 5.1.3 at every date** (used throughout §6.3): the problem from each date
`t ≤ T` satisfies Assumption 5.1.3 over the remaining horizon. -/
def po_Assumption513 (M : MDP S A) (T : ℕ) : Prop :=
  ∀ t ≤ T, Assumption513 (po_shift M t) (T - t)

/-- With stochastic kernels, bounded measurable rewards satisfy Assumption 5.1.3 at every
date. -/
theorem po_assumption513_of_bounded {M : MDP S A} (hP : M.IsMarkov) {B : ℝ}
    (hB : BoundedRewards M B) (hu : ∀ t, Measurable (M.u t)) (huT : Measurable M.uT) (T : ℕ) :
    po_Assumption513 M T := fun t _ =>
  assumption_5_1_3_of_bounded (po_shift_isMarkov hP t) ⟨fun j x => hB.1 (j + t) x, hB.2⟩
    (fun j => hu (j + t)) huT (T - t)

theorem po_shift_u0 (M : MDP S A) (t : ℕ) : (po_shift M t).u 0 = M.u t := by
  simp only [po_shift, zero_add]

theorem po_shift_P0 (M : MDP S A) (t : ℕ) : (po_shift M t).P 0 = M.P t := by
  simp only [po_shift, zero_add]

/-- **Lemma 6.3.1** (Miao, p. 165). For a feasible plan `π` from `sᵗ`, `t < T`, under
Assumption 5.1.3 for the problem from date `t`:
`J_t^T(sᵗ, π) = u_t(s_t, π_t) +
β ∫ J_{t+1}^T(s^{t+1}, C(π, s_{t+1})) P_{t+1}(s_t, π_t; ds_{t+1})`. -/
theorem lemma_6_3_1 {M : MDP S A} (hP : M.IsMarkov) {T t : ℕ} (ht : t < T)
    (hI : Assumption513 (po_shift M t) (T - t)) {h : Fin (t + 1) → S} {π : Plan S A}
    (hπ : π ∈ po_plansFrom M T t h) :
    po_JFrom M T t h π = M.u t (h (Fin.last t), π 0 Fin.elim0) +
      M.β * ∫ s', po_JFrom M T (t + 1) (Fin.snoc h s') (po_cont π s')
        ∂M.P t (h (Fin.last t), π 0 Fin.elim0) := by
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  unfold po_JFrom
  simp only [Fin.snoc_last, hn']
  unfold po_plansFrom at hπ
  rw [hn] at hπ hI
  rw [← po_shift_shift, hn, po_J0T_succ (po_shift_isMarkov hP t) (po_plan_meas hπ)
    (po_intPlan_of_assumption513 hI hπ), po_shift_u0, po_shift_P0]
  rfl

/-- **Assumption 6.3.1** (Miao, p. 164), with `w t` the value function at date `t` as a function
of the current state. For `t = 1, …, T − 1`: (a) `V_t` is real-valued, `V_t(sᵗ) = w_t(s_t)`, and
`w_t` is measurable; (b) for every `ε > 0` there is a family of plans `π^{s_t}` from the states
`s_t`, ε-optimal (6.15) and jointly measurable in the state and the history (see the module
docstring for this correction of the book's measurability requirement). -/
def Assumption631 (M : MDP S A) (T : ℕ) (w : ℕ → S → ℝ) : Prop :=
  ∀ t, 1 ≤ t → t < T → Measurable (w t) ∧
    (∀ h : Fin (t + 1) → S, po_VFrom M T t h = w t (h (Fin.last t))) ∧
    ∀ ε : ℝ, 0 < ε → ∃ ρ : S → Plan S A,
      (∀ s, ρ s ∈ feasiblePlans (po_shift M t) ((T - t : ℕ) : ℕ∞) s) ∧
      (∀ s, w t s ≤ J0T (po_shift M t) (T - t) s (ρ s) + ε) ∧ po_JointMeas ρ (T - t)

/-- **The Bellman step** behind Theorem 6.3.1, at date `0` of a process `M` with horizon `n + 1`:
if the value of the problem from date `1` is a measurable real function `w'` with jointly
measurable ε-optimal plans, then `w'` is integrable against `P₁(s, a; ·)` for `a ∈ Γ(s)` and
`V₀(s) = sup_{a ∈ Γ(s)} u₀(s, a) + β ∫ w' dP₁(s, a; ·)`. -/
theorem po_bellman_step {M : MDP S A} (hP : M.IsMarkov) (hβ : 0 ≤ M.β) {n : ℕ}
    (hI : Assumption513 M (n + 1)) {w' : S → ℝ} (hwm : Measurable w')
    (hwV : ∀ s, V0 (po_shift M 1) n s = w' s)
    (hρ : ∀ ε : ℝ, 0 < ε → ∃ ρ : S → Plan S A,
      (∀ s, ρ s ∈ feasiblePlans (po_shift M 1) (n : ℕ∞) s) ∧
      (∀ s, w' s ≤ J0T (po_shift M 1) n s (ρ s) + ε) ∧ po_JointMeas ρ n) (s : S) :
    (∀ a ∈ M.Γ s, Integrable w' (M.P 0 (s, a))) ∧
      V0 M (n + 1) s =
        ⨆ a ∈ M.Γ s, ((M.u 0 (s, a) + M.β * ∫ s', w' s' ∂M.P 0 (s, a) : ℝ) : EReal) := by
  have hJle : ∀ s' σ, σ ∈ feasiblePlans (po_shift M 1) (n : ℕ∞) s' →
      J0T (po_shift M 1) n s' σ ≤ w' s' := by
    intro s' σ hσ
    have := po_J_le_V0 hσ
    rw [hwV] at this
    exact EReal.coe_le_coe_iff.1 this
  have hglue : ∀ a ∈ M.Γ s, ∀ ρ : S → Plan S A,
      (∀ s, ρ s ∈ feasiblePlans (po_shift M 1) (n : ℕ∞) s) → po_JointMeas ρ n →
      po_glue a ρ ∈ feasiblePlans M ((n + 1 : ℕ) : ℕ∞) s ∧
      Integrable (fun s' => J0T (po_shift M 1) n s' (ρ s')) (M.P 0 (s, a)) ∧
      J0T M (n + 1) s (po_glue a ρ) = M.u 0 (s, a) +
        M.β * ∫ s', J0T (po_shift M 1) n s' (ρ s') ∂M.P 0 (s, a) := by
    intro a ha ρ hρF hρm
    have hπ := po_glue_feasible ha hρF hρm
    have hJi := po_integrable_J0T_cont hP (po_plan_meas hπ) (po_intPlan_of_assumption513 hI hπ)
    have hJ := po_J0T_succ hP (po_plan_meas hπ) (po_intPlan_of_assumption513 hI hπ)
    simp only [po_cont_glue] at hJi hJ
    exact ⟨hπ, hJi, hJ⟩
  have hint : ∀ a ∈ M.Γ s, Integrable w' (M.P 0 (s, a)) := by
    intro a ha
    obtain ⟨ρ, hρF, hρε, hρm⟩ := hρ 1 one_pos
    obtain ⟨-, hJi, -⟩ := hglue a ha ρ hρF hρm
    have : IsMarkovKernel (M.P 0) := hP 0
    refine Integrable.mono' (hJi.abs.add (integrable_const 1)) hwm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s' => ?_)
    have h1 := hJle s' (ρ s') (hρF s')
    have h2 := hρε s'
    change ‖w' s'‖ ≤ |J0T (po_shift M 1) n s' (ρ s')| + 1
    rw [Real.norm_eq_abs]
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith [neg_abs_le (J0T (po_shift M 1) n s' (ρ s'))]
    · linarith [le_abs_self (J0T (po_shift M 1) n s' (ρ s'))]
  refine ⟨hint, le_antisymm ?_ ?_⟩
  · refine iSup₂_le fun π hπ => ?_
    have hπm := po_plan_meas hπ
    have hIπ := po_intPlan_of_assumption513 hI hπ
    have ha : π 0 Fin.elim0 ∈ M.Γ s := hπ.2 0 (po_cast_lt.2 (Nat.succ_pos n)) Fin.elim0
    rw [po_J0T_succ hP hπm hIπ]
    refine le_trans ?_ (le_iSup₂_of_le (π 0 Fin.elim0) ha le_rfl)
    refine EReal.coe_le_coe_iff.2 (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (integral_mono (po_integrable_J0T_cont hP hπm hIπ) (hint _ ha)
        fun s' => hJle s' _ (po_cont_feasible hπ s')) hβ))
  · refine iSup₂_le fun a ha => po_coe_le_of_forall_sub fun δ hδ => ?_
    have hβ1 : 0 < M.β + 1 := by linarith
    have hε : 0 < δ / (M.β + 1) := div_pos hδ hβ1
    obtain ⟨ρ, hρF, hρε, hρm⟩ := hρ _ hε
    obtain ⟨hπ, hJi, hJ⟩ := hglue a ha ρ hρF hρm
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) (po_J_le_V0 hπ)
    rw [hJ]
    have : IsMarkovKernel (M.P 0) := hP 0
    have h1 : ∫ s', (w' s' - δ / (M.β + 1)) ∂M.P 0 (s, a) ≤
        ∫ s', J0T (po_shift M 1) n s' (ρ s') ∂M.P 0 (s, a) :=
      integral_mono ((hint a ha).sub (integrable_const _)) hJi fun s' => by
        linarith [hρε s']
    rw [integral_sub (hint a ha) (integrable_const _)] at h1
    have hc : ∫ _, δ / (M.β + 1) ∂M.P 0 (s, a) = δ / (M.β + 1) := by simp
    rw [hc] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hβ
    have h3 : M.β * (δ / (M.β + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ hβ1]
      nlinarith
    nlinarith

/-- **Theorem 6.3.1** (Miao, p. 166), the dynamic programming principle. Under Assumption 5.1.3
at every date, `β ≥ 0` and Assumption 6.3.1 (with `w_t` the value at date `t`, `w_T = u_T`),
for `t < T` and every history `sᵗ`: `V_{t+1}` is integrable against `P_{t+1}(s_t, a; ·)` for
`a ∈ Γ(s_t)`, and the Bellman equation (6.17) holds,
`V_t(sᵗ) = sup_{a ∈ Γ(s_t)} u_t(s_t, a) + β ∫ V_{t+1}(s^{t+1}) P_{t+1}(s_t, a; ds_{t+1})`;
moreover `V_T(s^T) = u_T(s_T)` and `V_t` is Markovian: `V_t(sᵗ)` depends on `sᵗ` only through
`s_t`. -/
theorem theorem_6_3_1 [Nonempty A] {M : MDP S A} (hP : M.IsMarkov) (hβ : 0 ≤ M.β) {T : ℕ}
    (hI : po_Assumption513 M T) {w : ℕ → S → ℝ} (hA : Assumption631 M T w)
    (hwT : w T = M.uT) :
    (∀ t < T, ∀ h : Fin (t + 1) → S,
      (∀ a ∈ M.Γ (h (Fin.last t)), Integrable (w (t + 1)) (M.P t (h (Fin.last t), a))) ∧
      po_VFrom M T t h = ⨆ a ∈ M.Γ (h (Fin.last t)),
        ((M.u t (h (Fin.last t), a) +
          M.β * ∫ s', w (t + 1) s' ∂M.P t (h (Fin.last t), a) : ℝ) : EReal)) ∧
    (∀ h : Fin (T + 1) → S, po_VFrom M T T h = M.uT (h (Fin.last T))) ∧
    (∀ t, ∀ h h' : Fin (t + 1) → S, h (Fin.last t) = h' (Fin.last t) →
      po_VFrom M T t h = po_VFrom M T t h') := by
  refine ⟨fun t ht h => ?_, fun h => po_VFrom_terminal M T h, fun t h h' hh => by
    rw [eq_6_14, eq_6_14, hh]⟩
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  have hIt := hI t ht.le
  rw [hn] at hIt
  have hdata : Measurable (w (t + 1)) ∧
      (∀ s, V0 (po_shift (po_shift M t) 1) n s = w (t + 1) s) ∧
      ∀ ε : ℝ, 0 < ε → ∃ ρ : S → Plan S A,
        (∀ s, ρ s ∈ feasiblePlans (po_shift (po_shift M t) 1) (n : ℕ∞) s) ∧
        (∀ s, w (t + 1) s ≤ J0T (po_shift (po_shift M t) 1) n s (ρ s) + ε) ∧
        po_JointMeas ρ n := by
    rw [po_shift_shift]
    rcases Nat.lt_or_ge (t + 1) T with h1 | h1
    · obtain ⟨hm, hV, hρ⟩ := hA (t + 1) (by omega) h1
      rw [hn'] at hρ
      refine ⟨hm, fun s => ?_, hρ⟩
      have := hV fun _ => s
      rw [eq_6_14, hn'] at this
      exact this
    · have hT : t + 1 = T := by omega
      have hn0 : n = 0 := by omega
      subst hn0
      rw [hT, hwT]
      refine ⟨(hI T le_rfl).2.1, fun s => po_V0_zero _ s, fun ε hε => ?_⟩
      refine ⟨fun _ _ _ => Classical.arbitrary A, fun s => po_feasible_zero _ s _,
        fun s => ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      rw [po_J0T_zero]
      exact le_add_of_nonneg_right hε.le
  obtain ⟨hm, hV, hρ⟩ := hdata
  have := po_bellman_step (po_shift_isMarkov hP t) hβ hIt hm hV hρ (h (Fin.last t))
  rw [po_shift_u0, po_shift_P0] at this
  refine ⟨this.1, ?_⟩
  rw [eq_6_14, hn]
  exact this.2

end Miao.FiniteHorizonDP

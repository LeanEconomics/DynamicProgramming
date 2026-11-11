/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.POHistory
import Applications.IHEInt

/-!
# The recursive structure of the objective: Assumption 7.1.1 and Lemma 7.1.1

Copied from `EconomicDynamics/InfiniteHorizonDP` (module `IHLemma711`), namespace renamed.

Miao, §7.1, pp. 193–195, in the infinite-horizon Markov decision process model of Chapter 5
(`MDP`, plans, the measures `μᵗ` of (5.2), the objective `J` of (5.4) with values in `[−∞, +∞]`,
Assumptions 5.1.2 and 5.1.4).

* Under Assumption 5.1.4 the process is stationary, so the process from date `1` is the process
  itself (`ih_shift_eq`), and the continuation plan `C(π, s₁)` of a feasible plan is feasible from
  `s₁` (`ih_cont_feasible'`). Glued plans are feasible when the family of plans is jointly
  measurable (`ih_glue_feasible`).
* `ih_partialSum_succ`: the partial sums of (5.4) satisfy
  `J₀ⁿ⁺¹(s₀, π) = u(s₀, π₀) + β ∫ J₀ⁿ(s₁, C(π, s₁)) P(s₀, π₀; ds₁)` (the first equality of the
  book's proof), with the inner function integrable.
* **Assumption 7.1.1** (`Assumption711`) and the three cases of the proof (`ih_SignCases`:
  `u ≥ 0`, `u ≤ 0`, or Assumption 7.1.1).
* **Lemma 7.1.1** (`lemma_7_1_1`): `J(s₀, π) = u(s₀, π₀) + β ∫ J(s₁, C(π, s₁)) P(s₀, π₀; ds₁)`,
  the integral being the extended integral `ih_eint`. In the three cases separately:
  `lemma_7_1_1_nonneg` (monotone convergence, the integral is a lower integral in `[0, ∞]`),
  `lemma_7_1_1_nonpos` (monotone convergence, the integral lies in `[−∞, 0]`) and
  `lemma_7_1_1_bounded` (dominated convergence; `J(s₁, C(π, s₁))` is then real, bounded and
  integrable, and the integral is a Bochner integral).

**Departures from the book.** Assumption 5.1.1 is not used, and only `β > 0` from Assumption
5.1.2. The bound of Assumption 7.1.1 is read as holding for every history `sᵗ`, which is what
the dominated convergence step needs; the measurability of `L_t` is part of the definition but
is not used.
-/

namespace Miao.Applications

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- Under stationarity the process from date `t` is the process itself. -/
theorem ih_shift_eq {M : MDP S A} (h : M.IsStationary) (t : ℕ) : po_shift M t = M := by
  cases M with
  | mk Γ P u uT β =>
    simp only [po_shift, MDP.mk.injEq, true_and, and_true]
    exact ⟨funext fun j => (h (j + t)).1.trans (h j).1.symm,
      funext fun j => (h (j + t)).2.trans (h j).2.symm⟩

/-- The continuation `C(π, s₁)` of a feasible infinite-horizon plan is feasible for the process
from date `1`. -/
theorem ih_cont_feasible {M : MDP S A} {s : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ⊤ s) (s' : S) : po_cont π s' ∈ feasiblePlans (po_shift M 1) ⊤ s' :=
  ⟨fun j _ => (hπ.1 (j + 1) (WithTop.coe_lt_top _)).comp
    ((measurable_cons j).comp (measurable_const.prodMk measurable_id)),
   fun j _ h => by
    have := hπ.2 (j + 1) (WithTop.coe_lt_top _) (Fin.cons s' h)
    rwa [lastState_cons] at this⟩

/-- Miao, p. 194: for a stationary process, the continuation `C(π, s₁)` of a plan feasible from
`s₀` is feasible from `s₁`. -/
theorem ih_cont_feasible' {M : MDP S A} (hst : M.IsStationary) {s : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ⊤ s) (s' : S) : po_cont π s' ∈ feasiblePlans M ⊤ s' := by
  have := ih_cont_feasible hπ s'
  rwa [ih_shift_eq hst 1] at this

/-- The plan that takes the action `a ∈ Γ(s)` and then follows `ρ(s₁)` is feasible from `s` when
the plans `ρ(s₁)` are feasible from `s₁` and jointly measurable in `s₁` and the history. -/
theorem ih_glue_feasible {M : MDP S A} {s : S} {a : A} {ρ : S → Plan S A} (ha : a ∈ M.Γ s)
    (hρ : ∀ s', ρ s' ∈ feasiblePlans (po_shift M 1) ⊤ s') (hm : ∀ n, po_JointMeas ρ n) :
    po_glue a ρ ∈ feasiblePlans M ⊤ s := by
  refine ⟨fun j _ => ?_, fun j _ h => ?_⟩
  · cases j with
    | zero => exact measurable_const
    | succ j =>
      exact (hm (j + 1) j (Nat.lt_succ_self j)).comp
        ((measurable_pi_apply 0).prodMk (po_measurable_tail j))
  · cases j with
    | zero => exact ha
    | succ j =>
      have := (hρ (h 0)).2 j (WithTop.coe_lt_top _) (Fin.tail h)
      have hl : lastState s h = lastState (h 0) (Fin.tail h) := by
        conv_lhs => rw [← Fin.cons_self_tail h]
        exact lastState_cons s (h 0) (Fin.tail h)
      rw [hl]
      exact this

theorem ih_J_le_V {M : MDP S A} {s : S} {π : Plan S A} (hπ : π ∈ feasiblePlans M ⊤ s) :
    J M s π ≤ V M s :=
  le_iSup₂ (f := fun π (_ : π ∈ feasiblePlans M ⊤ s) => J M s π) π hπ

/-- The process with terminal reward `0`: its finite-horizon objectives are the partial sums
of (5.4). -/
def ih_noT (M : MDP S A) : MDP S A := { M with uT := fun _ => 0 }

theorem ih_expRew_noT (M : MDP S A) (s : S) (π : Plan S A) (t : ℕ) :
    expRew (ih_noT M) s π t = expRew M s π t := by
  simp only [expRew, mu_congr (M := ih_noT M) (M' := M) rfl s (π := π) (t := t) fun _ _ => rfl]
  rfl

theorem ih_partialSum_eq_J0T (M : MDP S A) (s : S) (π : Plan S A) (n : ℕ) :
    partialSum M s π n = J0T (ih_noT M) (n + 1) s π := by
  have : (ih_noT M).uT = fun _ => 0 := rfl
  simp only [partialSum, J0T, ih_expRew_noT, this, integral_zero, mul_zero, add_zero]
  rfl

/-- The first equality of the proof of Lemma 7.1.1 (Miao, p. 195), for the partial sums:
`J₀ⁿ⁺¹(s₀, π) = u(s₀, π₀) + β ∫ J₀ⁿ(s₁, C(π, s₁)) P(s₀, π₀; ds₁)`, where `J₀ⁿ` is the `n`-th
partial sum of (5.4); the inner function is integrable. -/
theorem ih_partialSum_succ {M : MDP S A} (hP : M.IsMarkov) (hst : M.IsStationary) {s : S}
    {π : Plan S A} (hπ : π ∈ feasiblePlans M ⊤ s)
    (hI : ∀ t, Integrable (rew M s π t) (mu M s π t)) (n : ℕ) :
    Integrable (fun s' => partialSum M s' (po_cont π s') n) (M.P 0 (s, π 0 Fin.elim0)) ∧
      partialSum M s π (n + 1) = M.u 0 (s, π 0 Fin.elim0) +
        M.β * ∫ s', partialSum M s' (po_cont π s') n ∂M.P 0 (s, π 0 Fin.elim0) := by
  have hP' : (ih_noT M).IsMarkov := hP
  have hst' : (ih_noT M).IsStationary := hst
  have hm : ∀ j ≤ n + 1, Measurable (π j) := fun j _ => hπ.1 j (WithTop.coe_lt_top j)
  have hIπ : po_IntPlan (ih_noT M) (n + 1 + 1) s π := by
    refine ⟨fun j _ => ?_, ?_⟩
    · rw [mu_congr (M := ih_noT M) (M' := M) rfl s (π := π) (t := j) fun _ _ => rfl]
      exact hI j
    · exact integrable_zero _ _ _
  have h1 := po_integrable_J0T_cont hP' hm hIπ
  have h2 := po_J0T_succ hP' hm hIπ
  have key : ∀ s' σ, J0T (po_shift (ih_noT M) 1) (n + 1) s' σ = partialSum M s' σ n := by
    intro s' σ
    rw [ih_shift_eq hst' 1, ← ih_partialSum_eq_J0T]
  simp only [key] at h1 h2
  rw [← ih_partialSum_eq_J0T] at h2
  exact ⟨h1, h2⟩

/-- **Assumption 7.1.1** (Miao, p. 194). There are nonnegative measurable `L_t : S → ℝ₊` with
`|u(s_t, π_t(sᵗ))| ≤ L_t(s₀)` for every feasible plan `π ∈ Π(s₀)`, date `t` and history `sᵗ`
(for `t = 0`: `|u(s₀, π₀)| ≤ L₀(s₀)`), and `∑ βᵗ L_t(s₀) < ∞`. -/
def Assumption711 (M : MDP S A) : Prop :=
  ∃ L : ℕ → S → ℝ, (∀ t, Measurable (L t)) ∧ (∀ t s, 0 ≤ L t s) ∧
    (∀ s₀, ∀ π ∈ feasiblePlans M ⊤ s₀, ∀ t (h : Fin t → S), |rew M s₀ π t h| ≤ L t s₀) ∧
    ∀ s₀, Summable fun t => M.β ^ t * L t s₀

/-- The three cases of the proof of Lemma 7.1.1 (Miao, p. 195): `u ≥ 0`, `u ≤ 0`, or `u` takes
both signs and Assumption 7.1.1 holds. -/
def ih_SignCases (M : MDP S A) : Prop :=
  (∀ x, 0 ≤ M.u 0 x) ∨ (∀ x, M.u 0 x ≤ 0) ∨ Assumption711 M

theorem ih_partialSum_mono {M : MDP S A} (hβ : 0 ≤ M.β) (hu : ∀ t x, 0 ≤ M.u t x) (s : S)
    (σ : Plan S A) : Monotone (partialSum M s σ) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [partialSum, partialSum, Finset.sum_range_succ _ (n + 1)]
  have : 0 ≤ M.β ^ (n + 1) * expRew M s σ (n + 1) :=
    mul_nonneg (pow_nonneg hβ _) (integral_nonneg fun h => hu _ _)
  linarith

theorem ih_partialSum_nonneg {M : MDP S A} (hβ : 0 ≤ M.β) (hu : ∀ t x, 0 ≤ M.u t x) (s : S)
    (σ : Plan S A) (n : ℕ) : 0 ≤ partialSum M s σ n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hβ _) (integral_nonneg fun _ => hu _ _)

theorem ih_partialSum_anti {M : MDP S A} (hβ : 0 ≤ M.β) (hu : ∀ t x, M.u t x ≤ 0) (s : S)
    (σ : Plan S A) : Antitone (partialSum M s σ) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [partialSum, partialSum, Finset.sum_range_succ _ (n + 1)]
  have : M.β ^ (n + 1) * expRew M s σ (n + 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ _) (integral_nonpos fun h => hu _ _)
  linarith

theorem ih_partialSum_nonpos {M : MDP S A} (hβ : 0 ≤ M.β) (hu : ∀ t x, M.u t x ≤ 0) (s : S)
    (σ : Plan S A) (n : ℕ) : partialSum M s σ n ≤ 0 :=
  Finset.sum_nonpos fun _ _ =>
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ _) (integral_nonpos fun _ => hu _ _)

/-- Under Assumption 7.1.1, the partial sums along the continuation plans are bounded,
uniformly in `s₁` and `n`, by `∑ βᵗ L_{t+1}(s₀)`. -/
theorem ih_partialSum_cont_bound {M : MDP S A} (hP : M.IsMarkov) (hβ : 0 < M.β)
    (hst : M.IsStationary) {L : ℕ → S → ℝ} (hL0 : ∀ t s, 0 ≤ L t s)
    (hLb : ∀ s₀, ∀ π ∈ feasiblePlans M ⊤ s₀, ∀ t (h : Fin t → S), |rew M s₀ π t h| ≤ L t s₀)
    (hLs : ∀ s₀, Summable fun t => M.β ^ t * L t s₀) {s₀ : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ⊤ s₀) (n : ℕ) (s' : S) :
    |partialSum M s' (po_cont π s') n| ≤ ∑' t, M.β ^ t * L (t + 1) s₀ := by
  have hsum : Summable fun t => M.β ^ t * L (t + 1) s₀ := by
    have h1 := ((summable_nat_add_iff 1).2 (hLs s₀)).mul_left M.β⁻¹
    refine h1.congr fun t => ?_
    rw [pow_succ]
    field_simp
  have hc := ih_cont_feasible' hst hπ s'
  have hrew : ∀ t (h : Fin t → S), |rew M s' (po_cont π s') t h| ≤ L (t + 1) s₀ := by
    intro t h
    have := hLb s₀ π hπ (t + 1) (Fin.cons s' h)
    rwa [po_rew_cons, ih_shift_eq hst 1] at this
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (hsum.sum_le_tsum (Finset.range (n + 1))
    fun t _ => mul_nonneg (pow_nonneg hβ.le _) (hL0 _ _))
  refine Finset.sum_le_sum fun t _ => ?_
  rw [abs_mul, abs_of_nonneg (pow_nonneg hβ.le _)]
  exact mul_le_mul_of_nonneg_left (abs_expRew_le hP s' (hrew t)
    fun j _ => hc.1 j (WithTop.coe_lt_top j)) (pow_nonneg hβ.le _)

/-- The convergence step of the proof of Lemma 7.1.1 (Miao, p. 195): in each of the three
cases, `∫ J₀ⁿ(s₁, C(π, s₁)) P(s₀, π₀; ds₁) → ∫ J(s₁, C(π, s₁)) P(s₀, π₀; ds₁)`. -/
theorem ih_tendsto_integral_cont {M : MDP S A} (hP : M.IsMarkov) (h512 : Assumption512 M)
    (h514 : Assumption514 M) (hcase : ih_SignCases M) {s₀ : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ⊤ s₀) :
    Tendsto (fun n => ((∫ s', partialSum M s' (po_cont π s') n ∂M.P 0 (s₀, π 0 Fin.elim0) : ℝ) :
      EReal)) atTop
      (𝓝 (ih_eint (M.P 0 (s₀, π 0 Fin.elim0)) fun s₁ => J M s₁ (po_cont π s₁))) := by
  have hst := h514.1
  have hint := fun n => (ih_partialSum_succ hP hst hπ (h514.2 s₀ π hπ).1 n).1
  have hlim : ∀ s', Tendsto (fun n => (partialSum M s' (po_cont π s') n : EReal)) atTop
      (𝓝 (J M s' (po_cont π s'))) := fun s' => J_spec h514 (ih_cont_feasible' hst hπ s')
  rcases hcase with hu | hu | ⟨L, -, hL0, hLb, hLs⟩
  · have hu' : ∀ t x, 0 ≤ M.u t x := fun t x => by rw [(hst t).2]; exact hu x
    exact ih_tendsto_eint_nonneg hint
      (fun n s' => ih_partialSum_nonneg h512.1.le hu' s' _ n)
      (fun s' => ih_partialSum_mono h512.1.le hu' s' _) hlim
  · have hu' : ∀ t x, M.u t x ≤ 0 := fun t x => by rw [(hst t).2]; exact hu x
    exact ih_tendsto_eint_nonpos hint
      (fun n s' => ih_partialSum_nonpos h512.1.le hu' s' _ n)
      (fun s' => ih_partialSum_anti h512.1.le hu' s' _) hlim
  · have := hP 0
    exact (ih_tendsto_eint_bounded hint
      (ih_partialSum_cont_bound hP h512.1 hst hL0 hLb hLs hπ) hlim).2.2.2.2

/-- **Lemma 7.1.1** (Miao, p. 194). Under Assumptions 5.1.2 and 5.1.4, in each of the three
cases `u ≥ 0`, `u ≤ 0`, or Assumption 7.1.1, for every `s₀` and `π ∈ Π(s₀)`,
`J(s₀, π) = u(s₀, π₀) + β ∫ J(s₁, C(π, s₁)) P(s₀, π₀; ds₁)`, where `C(π, s₁)` is the
continuation plan and the integral is the extended integral `ih_eint` in `[−∞, +∞]`. -/
theorem lemma_7_1_1 {M : MDP S A} (hP : M.IsMarkov) (h512 : Assumption512 M)
    (h514 : Assumption514 M) (hcase : ih_SignCases M) {s₀ : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ⊤ s₀) :
    J M s₀ π = (M.u 0 (s₀, π 0 Fin.elim0) : EReal) +
      (M.β : EReal) * ih_eint (M.P 0 (s₀, π 0 Fin.elim0)) fun s₁ => J M s₁ (po_cont π s₁) := by
  have hrec := ih_partialSum_succ hP h514.1 hπ (h514.2 s₀ π hπ).1
  have h1 := (J_spec h514 hπ).comp (tendsto_add_atTop_nat 1)
  have h2 := ((IHDet.continuous_add_mul (M.u 0 (s₀, π 0 Fin.elim0)) M.β h512.1.le).tendsto _).comp
    (ih_tendsto_integral_cont hP h512 h514 hcase hπ)
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  simp only [Function.comp_apply, (hrec n).2, EReal.coe_add, EReal.coe_mul]

/-- The function `s₁ ↦ J(s₁, C(π, s₁))` has a.e.-measurable positive and negative parts (as a
pointwise limit of integrable functions). -/
theorem ih_J_cont_aemeasurable {M : MDP S A} (hP : M.IsMarkov) (h514 : Assumption514 M)
    {s₀ : S} {π : Plan S A} (hπ : π ∈ feasiblePlans M ⊤ s₀) :
    AEMeasurable (fun s₁ => (J M s₁ (po_cont π s₁)).toENNReal) (M.P 0 (s₀, π 0 Fin.elim0)) ∧
      AEMeasurable (fun s₁ => (-J M s₁ (po_cont π s₁)).toENNReal)
        (M.P 0 (s₀, π 0 Fin.elim0)) :=
  ih_aemeasurable_parts
    (fun n => (ih_partialSum_succ hP h514.1 hπ (h514.2 s₀ π hπ).1 n).1.1.aemeasurable)
    fun s' => J_spec h514 (ih_cont_feasible' h514.1 hπ s')

/-- **Lemma 7.1.1, case `u ≥ 0`** (Miao, p. 195, by the Monotone Convergence Theorem):
`J(s₀, π) = u(s₀, π₀) + β ∫⁻ J(s₁, C(π, s₁)) P(s₀, π₀; ds₁)`, a lower integral in `[0, ∞]`. -/
theorem lemma_7_1_1_nonneg {M : MDP S A} (hP : M.IsMarkov) (h512 : Assumption512 M)
    (h514 : Assumption514 M) (hu : ∀ x, 0 ≤ M.u 0 x) {s₀ : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ⊤ s₀) :
    J M s₀ π = (M.u 0 (s₀, π 0 Fin.elim0) : EReal) + (M.β : EReal) *
      ((∫⁻ s₁, (J M s₁ (po_cont π s₁)).toENNReal ∂M.P 0 (s₀, π 0 Fin.elim0) : ℝ≥0∞) :
        EReal) := by
  have hu' : ∀ t x, 0 ≤ M.u t x := fun t x => by rw [(h514.1 t).2]; exact hu x
  rw [lemma_7_1_1 hP h512 h514 (Or.inl hu) hπ, ih_eint_of_nonneg]
  intro s₁
  exact ge_of_tendsto' (J_spec h514 (ih_cont_feasible' h514.1 hπ s₁)) fun n =>
    EReal.coe_nonneg.2 (ih_partialSum_nonneg h512.1.le hu' _ _ n)

/-- **Lemma 7.1.1, case `u ≤ 0`** (Miao, p. 195, by the Monotone Convergence Theorem):
`J(s₀, π) = u(s₀, π₀) − β ∫⁻ (−J(s₁, C(π, s₁))) P(s₀, π₀; ds₁)`, the integral in `[−∞, 0]`. -/
theorem lemma_7_1_1_nonpos {M : MDP S A} (hP : M.IsMarkov) (h512 : Assumption512 M)
    (h514 : Assumption514 M) (hu : ∀ x, M.u 0 x ≤ 0) {s₀ : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ⊤ s₀) :
    J M s₀ π = (M.u 0 (s₀, π 0 Fin.elim0) : EReal) + (M.β : EReal) *
      -((∫⁻ s₁, (-J M s₁ (po_cont π s₁)).toENNReal ∂M.P 0 (s₀, π 0 Fin.elim0) : ℝ≥0∞) :
        EReal) := by
  have hu' : ∀ t x, M.u t x ≤ 0 := fun t x => by rw [(h514.1 t).2]; exact hu x
  rw [lemma_7_1_1 hP h512 h514 (Or.inr (Or.inl hu)) hπ, ih_eint_of_nonpos]
  intro s₁
  exact le_of_tendsto' (J_spec h514 (ih_cont_feasible' h514.1 hπ s₁)) fun n =>
    EReal.coe_nonpos.2 (ih_partialSum_nonpos h512.1.le hu' _ _ n)

/-- **Lemma 7.1.1, case of rewards of both signs** (Miao, p. 195, by the Dominated Convergence
Theorem under Assumption 7.1.1): `J(s₁, C(π, s₁))` is real, bounded in `s₁` and integrable, and
`J(s₀, π) = u(s₀, π₀) + β ∫ J(s₁, C(π, s₁)) P(s₀, π₀; ds₁)` with a Bochner integral. -/
theorem lemma_7_1_1_bounded {M : MDP S A} (hP : M.IsMarkov) (h512 : Assumption512 M)
    (h514 : Assumption514 M) (h711 : Assumption711 M) {s₀ : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ⊤ s₀) :
    (∀ s₁, J M s₁ (po_cont π s₁) = ((J M s₁ (po_cont π s₁)).toReal : EReal)) ∧
      Integrable (fun s₁ => (J M s₁ (po_cont π s₁)).toReal) (M.P 0 (s₀, π 0 Fin.elim0)) ∧
      J M s₀ π = ((M.u 0 (s₀, π 0 Fin.elim0) + M.β *
        ∫ s₁, (J M s₁ (po_cont π s₁)).toReal ∂M.P 0 (s₀, π 0 Fin.elim0) : ℝ) : EReal) := by
  obtain ⟨L, hLm, hL0, hLb, hLs⟩ := h711
  have := hP 0
  have hb := ih_tendsto_eint_bounded
    (fun n => (ih_partialSum_succ hP h514.1 hπ (h514.2 s₀ π hπ).1 n).1)
    (ih_partialSum_cont_bound hP h512.1 h514.1 hL0 hLb hLs hπ)
    fun s' => J_spec h514 (ih_cont_feasible' h514.1 hπ s')
  refine ⟨hb.1, hb.2.2.1, ?_⟩
  rw [lemma_7_1_1 hP h512 h514 (Or.inr (Or.inr ⟨L, hLm, hL0, hLb, hLs⟩)) hπ, hb.2.2.2.1,
    EReal.coe_add, EReal.coe_mul]

end Miao.Applications

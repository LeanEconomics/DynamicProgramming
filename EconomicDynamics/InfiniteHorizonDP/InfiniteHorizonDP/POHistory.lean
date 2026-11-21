/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.MDPObjective

/-!
# Problems from a later date, continuation plans and the first-date split

Copied from `EconomicDynamics/FiniteHorizonDP` (module `POHistory`), namespace renamed.

Tools for Miao, §6.3, pp. 163–165. Everything is stated for date `0` of a Markov decision
process `M`; the problem from date `t` is date `0` of the shifted process `po_shift M t`.

* `po_shift M t`: the process from date `t` on (`P j`, `u j` are `M`'s `P (j + t)`, `u (j + t)`);
  `po_shift_shift` composes shifts.
* `po_cont π s`: the continuation plan `C(π, s₁)` of a plan after the first state `s₁ = s`
  (Miao, p. 163); `po_cont_feasible`: it is feasible from `s₁` for the remaining horizon.
* `po_glue a ρ`: the plan that takes the action `a` now and follows the plan `ρ(s₁)` after `s₁`;
  `po_cont_glue`, `po_glue_feasible` (with `po_JointMeas`, joint measurability of the family
  `ρ` in the state and the history, which is what makes the glued plan a plan).
* The first-date split of the history measures: `po_mu_succ_lintegral`, the kernel
  `po_contKernel` (`s₁ ↦ μᵗ(s₁, ·; C(π, s₁))`), `po_mu_succ_eq`, `po_integral_mu_succ`,
  `po_integrable_cont`, `po_ae_mu_succ`.
* `po_IntPlan`: the rewards along a plan are integrable (what Assumption 5.1.3 gives).
  `po_J0T_succ`: the recursive form of the objective, which is Lemma 6.3.1 at date `0`, and
  `po_integrable_J0T_cont`, `po_ae_IntPlan_cont`.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The Markov decision process from date `t` on: its date `j` is date `j + t` of `M`. -/
def po_shift (M : MDP S A) (t : ℕ) : MDP S A where
  Γ := M.Γ
  P := fun j => M.P (j + t)
  u := fun j => M.u (j + t)
  uT := M.uT
  β := M.β

theorem po_shift_zero (M : MDP S A) : po_shift M 0 = M := rfl

theorem po_shift_shift (M : MDP S A) (a b : ℕ) :
    po_shift (po_shift M a) b = po_shift M (a + b) := by
  have h : ∀ j, j + b + a = j + (a + b) := fun j => by omega
  simp only [po_shift, h]

theorem po_shift_isMarkov {M : MDP S A} (hP : M.IsMarkov) (t : ℕ) : (po_shift M t).IsMarkov :=
  fun j => hP (j + t)

/-- The continuation plan `C(π, s₁)` (Miao, p. 163): `C_{j}(sʲ; π, s₁) = π_{j+1}(s₁, sʲ)`. -/
def po_cont (π : Plan S A) (s : S) : Plan S A := fun j h => π (j + 1) (Fin.cons s h)

/-- Take the action `a` now, and follow the plan `ρ(s₁)` from the next state `s₁` on. -/
def po_glue (a : A) (ρ : S → Plan S A) : Plan S A
  | 0, _ => a
  | j + 1, h => ρ (h 0) j (Fin.tail h)

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem po_cont_glue (a : A) (ρ : S → Plan S A) (s : S) : po_cont (po_glue a ρ) s = ρ s := by
  funext j h
  simp [po_cont, po_glue]

/-- A family of plans `s ↦ ρ(s)` is jointly measurable in the state and the history, at the
dates `j < n`. -/
def po_JointMeas (ρ : S → Plan S A) (n : ℕ) : Prop :=
  ∀ j < n, Measurable fun p : S × (Fin j → S) => ρ p.1 j p.2

theorem po_measurable_tail (j : ℕ) :
    Measurable (Fin.tail : (Fin (j + 1) → S) → Fin j → S) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem po_measurable_lastState_prod (t : ℕ) :
    Measurable fun p : S × (Fin t → S) => lastState p.1 p.2 := by
  cases t with
  | zero => exact measurable_fst
  | succ t => exact (measurable_pi_apply _).comp measurable_snd

theorem po_cast_lt {j n : ℕ} : ((j : ℕ) : ℕ∞) < ((n : ℕ) : ℕ∞) ↔ j < n := Nat.cast_lt

/-- The continuation of a feasible plan is feasible for the remaining horizon (Miao, p. 163). -/
theorem po_cont_feasible {M : MDP S A} {n : ℕ} {s : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ((n + 1 : ℕ) : ℕ∞) s) (s' : S) :
    po_cont π s' ∈ feasiblePlans (po_shift M 1) (n : ℕ∞) s' := by
  refine ⟨fun j hj => ?_, fun j hj h => ?_⟩
  · have hj' : ((j + 1 : ℕ) : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := po_cast_lt.2 (by
      have := po_cast_lt.1 hj; omega)
    exact (hπ.1 (j + 1) hj').comp ((measurable_cons j).comp
      (measurable_const.prodMk measurable_id))
  · have hj' : ((j + 1 : ℕ) : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := po_cast_lt.2 (by
      have := po_cast_lt.1 hj; omega)
    have := hπ.2 (j + 1) hj' (Fin.cons s' h)
    rwa [lastState_cons] at this

/-- The glued plan `(a, ρ)` is feasible when `a ∈ Γ(s)`, each `ρ(s₁)` is feasible from `s₁` and
the family is jointly measurable. -/
theorem po_glue_feasible {M : MDP S A} {n : ℕ} {s : S} {a : A} {ρ : S → Plan S A}
    (ha : a ∈ M.Γ s) (hρ : ∀ s', ρ s' ∈ feasiblePlans (po_shift M 1) (n : ℕ∞) s')
    (hm : po_JointMeas ρ n) : po_glue a ρ ∈ feasiblePlans M ((n + 1 : ℕ) : ℕ∞) s := by
  refine ⟨fun j hj => ?_, fun j hj h => ?_⟩
  · cases j with
    | zero => exact measurable_const
    | succ j =>
      have hj' : j < n := by have := po_cast_lt.1 hj; omega
      exact (hm j hj').comp ((measurable_pi_apply 0).prodMk (po_measurable_tail j))
  · cases j with
    | zero => exact ha
    | succ j =>
      have hj' : ((j : ℕ) : ℕ∞) < ((n : ℕ) : ℕ∞) := po_cast_lt.2 (by
        have := po_cast_lt.1 hj; omega)
      have := (hρ (h 0)).2 j hj' (Fin.tail h)
      have hl : lastState s h = lastState (h 0) (Fin.tail h) := by
        conv_lhs => rw [← Fin.cons_self_tail h]
        exact lastState_cons s (h 0) (Fin.tail h)
      rw [hl]
      exact this

/-- The lower integral of a function of `(s₁, sᵗ)` along `μᵗ(s₁, ·; ρ(s₁))` is measurable in
`s₁` for a jointly measurable family of plans. -/
theorem po_measurable_lintegral_family {M : MDP S A} (hP : M.IsMarkov) {ρ : S → Plan S A}
    {n : ℕ} (hm : po_JointMeas ρ n) :
    ∀ t ≤ n, ∀ {F : S × (Fin t → S) → ℝ≥0∞}, Measurable F →
      Measurable fun s => ∫⁻ h, F (s, h) ∂mu M s (ρ s) t := by
  intro t
  induction t with
  | zero =>
    intro _ F hF
    have : (fun s => ∫⁻ h, F (s, h) ∂mu M s (ρ s) 0) = fun s => F (s, Fin.elim0) := by
      funext s
      rw [mu_zero, lintegral_dirac' _ Subsingleton.measurable]
    rw [this]
    exact hF.comp (measurable_id.prodMk measurable_const)
  | succ t ih =>
    intro ht F hF
    have hmt : Measurable fun p : S × (Fin t → S) => ρ p.1 t p.2 := hm t (by omega)
    set κ : Kernel (S × (Fin t → S)) S := (M.P t).comap
      (fun p : S × (Fin t → S) => (lastState p.1 p.2, ρ p.1 t p.2))
      ((po_measurable_lastState_prod t).prodMk hmt) with hκ
    have : IsMarkovKernel (M.P t) := hP t
    have hκM : IsMarkovKernel κ := by rw [hκ]; infer_instance
    have hG : Measurable fun p : S × (Fin t → S) =>
        ∫⁻ s'', F (p.1, Fin.snoc p.2 s'') ∂κ p := by
      refine Measurable.lintegral_kernel_prod_right' (κ := κ)
        (f := fun q : (S × (Fin t → S)) × S => F (q.1.1, Fin.snoc q.1.2 q.2)) ?_
      exact hF.comp (measurable_fst.fst.prodMk ((measurable_snoc t).comp
        (measurable_fst.snd.prodMk measurable_snd)))
    have heq : (fun s => ∫⁻ h, F (s, h) ∂mu M s (ρ s) (t + 1)) =
        fun s => ∫⁻ h, ∫⁻ s'', F (s, Fin.snoc h s'') ∂κ (s, h) ∂mu M s (ρ s) t := by
      funext s
      have hρt : Measurable (ρ s t) := hmt.comp (measurable_const.prodMk measurable_id)
      rw [mu_succ_lintegral M hP s hρt (f := fun h => F (s, h))
        (hF.comp (measurable_const.prodMk measurable_id))]
      rfl
    rw [heq]
    exact ih (by omega) hG

/-- The first-date split of the history measures, for lower integrals:
`∫ f dμᵗ⁺¹(s, ·; π) = ∫ [∫ f(s₁, sᵗ) μᵗ(s₁, dsᵗ; C(π, s₁))] P₁(s, π₀; ds₁)`, where `μᵗ(s₁, ·; ·)`
is the measure of the process from date `1`. -/
theorem po_mu_succ_lintegral {M : MDP S A} (hP : M.IsMarkov) (s : S) {π : Plan S A} :
    ∀ (t : ℕ), (∀ j ≤ t, Measurable (π j)) → ∀ {f : (Fin (t + 1) → S) → ℝ≥0∞}, Measurable f →
      ∫⁻ h, f h ∂mu M s π (t + 1) =
        ∫⁻ s', ∫⁻ h, f (Fin.cons s' h) ∂mu (po_shift M 1) s' (po_cont π s') t
          ∂M.P 0 (s, π 0 Fin.elim0) := by
  intro t
  induction t with
  | zero =>
    intro hπ f hf
    rw [mu_succ_lintegral M hP s (hπ 0 le_rfl) hf, mu_zero,
      lintegral_dirac' _ Subsingleton.measurable]
    refine lintegral_congr fun s' => ?_
    rw [mu_zero, lintegral_dirac' _ Subsingleton.measurable]
    have : (Fin.snoc (Fin.elim0 : Fin 0 → S) s' : Fin 1 → S) = Fin.cons s' Fin.elim0 := by
      funext i
      fin_cases i
      rfl
    rw [this]
  | succ t ih =>
    intro hπ f hf
    have hπt : Measurable (π (t + 1)) := hπ (t + 1) le_rfl
    have := isSFiniteKernel_stepKernel M hP s π (t + 1)
    have hg : Measurable fun h : Fin (t + 1) → S =>
        ∫⁻ s'', f (Fin.snoc h s'') ∂M.P (t + 1) (lastState s h, π (t + 1) h) := by
      have h1 := (hf.comp (measurable_snoc (t + 1))).lintegral_kernel_prod_right'
        (κ := stepKernel M s π (t + 1))
      have h2 : (fun h : Fin (t + 1) → S =>
          ∫⁻ s'', f (Fin.snoc h s'') ∂M.P (t + 1) (lastState s h, π (t + 1) h)) =
          fun h => ∫⁻ s'', (f ∘ fun p : (Fin (t + 1) → S) × S => Fin.snoc p.1 p.2) (h, s'')
            ∂stepKernel M s π (t + 1) h := by
        funext h
        rw [stepKernel_apply M s hπt]
        rfl
      rw [h2]
      exact h1
    rw [mu_succ_lintegral M hP s hπt hf, ih (fun j hj => hπ j (by omega)) hg]
    refine lintegral_congr fun s' => ?_
    have hc : Measurable (po_cont π s' t) :=
      hπt.comp ((measurable_cons t).comp (measurable_const.prodMk measurable_id))
    rw [mu_succ_lintegral (po_shift M 1) (po_shift_isMarkov hP 1) s' hc
      (f := fun h => f (Fin.cons s' h))
      (hf.comp ((measurable_cons (t + 1)).comp (measurable_const.prodMk measurable_id)))]
    refine lintegral_congr fun h' => ?_
    rw [lastState_cons]
    refine lintegral_congr fun s'' => ?_
    rw [Fin.cons_snoc_eq_snoc_cons]

open Classical in
/-- The kernel `s₁ ↦ μᵗ(s₁, ·; C(π, s₁))` of the history after the first state (the zero kernel
if the hypotheses fail, a case that never arises for plans of Markov processes). -/
noncomputable def po_contKernel (M : MDP S A) (π : Plan S A) (t : ℕ) :
    Kernel S (Fin t → S) :=
  if h : M.IsMarkov ∧ ∀ j ≤ t, Measurable (π j) then
    { toFun := fun s' => mu (po_shift M 1) s' (po_cont π s') t
      measurable' := by
        refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
        have hm : po_JointMeas (po_cont π) t := fun j hj =>
          (h.2 (j + 1) (by omega)).comp (measurable_cons j)
        have := po_measurable_lintegral_family (po_shift_isMarkov h.1 1) hm t le_rfl
          (F := fun p : S × (Fin t → S) => B.indicator 1 p.2)
          ((measurable_one.indicator hB).comp measurable_snd)
        have hfun : (fun s' => (mu (po_shift M 1) s' (po_cont π s') t) B) = fun s' =>
            ∫⁻ h, (fun p : S × (Fin t → S) => B.indicator 1 p.2) (s', h)
              ∂mu (po_shift M 1) s' (po_cont π s') t := by
          funext s'
          exact (lintegral_indicator_one hB).symm
        rw [hfun]
        exact this }
  else 0

theorem po_contKernel_apply {M : MDP S A} (hP : M.IsMarkov) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j ≤ t, Measurable (π j)) (s' : S) :
    po_contKernel M π t s' = mu (po_shift M 1) s' (po_cont π s') t := by
  unfold po_contKernel
  split_ifs with h
  · rfl
  · exact absurd ⟨hP, hπ⟩ h

theorem po_isMarkovKernel_contKernel {M : MDP S A} (hP : M.IsMarkov) {π : Plan S A}
    {t : ℕ} (hπ : ∀ j ≤ t, Measurable (π j)) : IsMarkovKernel (po_contKernel M π t) := by
  refine ⟨fun s' => ?_⟩
  rw [po_contKernel_apply hP hπ]
  exact isProbabilityMeasure_mu (po_shift M 1) (po_shift_isMarkov hP 1) s'
    fun j hj => (hπ (j + 1) (by omega)).comp
      ((measurable_cons j).comp (measurable_const.prodMk measurable_id))

/-- The first-date split as an identity of measures: `μᵗ⁺¹(s, ·; π)` is the image under
`(s₁, sᵗ) ↦ (s₁, sᵗ)` of `P₁(s, π₀; ·) ⊗ μᵗ(s₁, ·; C(π, s₁))`. -/
theorem po_mu_succ_eq {M : MDP S A} (hP : M.IsMarkov) (s : S) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j ≤ t, Measurable (π j)) :
    mu M s π (t + 1) = ((M.P 0 (s, π 0 Fin.elim0)) ⊗ₘ po_contKernel M π t).map
      fun p => (Fin.cons p.1 p.2 : Fin (t + 1) → S) := by
  have := po_isMarkovKernel_contKernel hP hπ
  have : IsMarkovKernel (M.P 0) := hP 0
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [po_mu_succ_lintegral hP s t hπ hf, lintegral_map hf (measurable_cons t),
    Measure.lintegral_compProd (f := fun p : S × (Fin t → S) => f (Fin.cons p.1 p.2))
      (hf.comp (measurable_cons t))]
  refine lintegral_congr fun s' => ?_
  rw [po_contKernel_apply hP hπ]

/-- The first-date split for integrable functions:
`∫ f dμᵗ⁺¹(s, ·; π) = ∫ [∫ f(s₁, sᵗ) μᵗ(s₁, dsᵗ; C(π, s₁))] P₁(s, π₀; ds₁)`. -/
theorem po_integral_mu_succ {M : MDP S A} (hP : M.IsMarkov) (s : S) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j ≤ t, Measurable (π j)) {f : (Fin (t + 1) → S) → ℝ}
    (hf : Integrable f (mu M s π (t + 1))) :
    ∫ h, f h ∂mu M s π (t + 1) =
      ∫ s', ∫ h, f (Fin.cons s' h) ∂mu (po_shift M 1) s' (po_cont π s') t
        ∂M.P 0 (s, π 0 Fin.elim0) := by
  have := po_isMarkovKernel_contKernel hP hπ
  have : IsMarkovKernel (M.P 0) := hP 0
  rw [po_mu_succ_eq hP s hπ] at hf ⊢
  have hf' := (integrable_map_measure hf.1 (measurable_cons t).aemeasurable).1 hf
  rw [integral_map (measurable_cons t).aemeasurable hf.1,
    Measure.integral_compProd (f := fun p : S × (Fin t → S) => f (Fin.cons p.1 p.2)) hf']
  refine integral_congr_ae (Filter.Eventually.of_forall fun s' => ?_)
  simp only [po_contKernel_apply hP hπ]

/-- For an integrable `f`, the inner integral of the first-date split is integrable in `s₁`,
and `f(s₁, ·)` is integrable for almost every `s₁`. -/
theorem po_integrable_cont {M : MDP S A} (hP : M.IsMarkov) (s : S) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j ≤ t, Measurable (π j)) {f : (Fin (t + 1) → S) → ℝ}
    (hf : Integrable f (mu M s π (t + 1))) :
    Integrable (fun s' => ∫ h, f (Fin.cons s' h) ∂mu (po_shift M 1) s' (po_cont π s') t)
      (M.P 0 (s, π 0 Fin.elim0)) ∧
    ∀ᵐ s' ∂M.P 0 (s, π 0 Fin.elim0),
      Integrable (fun h => f (Fin.cons s' h)) (mu (po_shift M 1) s' (po_cont π s') t) := by
  have := po_isMarkovKernel_contKernel hP hπ
  have : IsMarkovKernel (M.P 0) := hP 0
  rw [po_mu_succ_eq hP s hπ] at hf
  have hf' := (integrable_map_measure hf.1 (measurable_cons t).aemeasurable).1 hf
  have h1 := MeasureTheory.Integrable.integral_compProd
    (κ := Kernel.const Unit (M.P 0 (s, π 0 Fin.elim0)))
    (η := Kernel.prodMkLeft Unit (po_contKernel M π t)) (a := ()) hf'
  have h2 := ((Measure.integrable_compProd_iff hf'.1).1 hf').1
  refine ⟨?_, ?_⟩
  · refine h1.congr (Filter.Eventually.of_forall fun s' => ?_)
    simp only [Kernel.prodMkLeft_apply, po_contKernel_apply hP hπ, Function.comp_apply]
  · filter_upwards [h2] with s' hs'
    rw [po_contKernel_apply hP hπ] at hs'
    exact hs'

/-- The first-date split for almost-everywhere statements: if `p` holds for almost every
continuation history after almost every first state, it holds `μᵗ⁺¹`-almost everywhere. -/
theorem po_ae_mu_succ {M : MDP S A} (hP : M.IsMarkov) (s : S) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j ≤ t, Measurable (π j)) {p : (Fin (t + 1) → S) → Prop}
    (hp : MeasurableSet {h | p h})
    (h : ∀ᵐ s' ∂M.P 0 (s, π 0 Fin.elim0),
      ∀ᵐ h ∂mu (po_shift M 1) s' (po_cont π s') t, p (Fin.cons s' h)) :
    ∀ᵐ h ∂mu M s π (t + 1), p h := by
  have := po_isMarkovKernel_contKernel hP hπ
  have : IsMarkovKernel (M.P 0) := hP 0
  rw [po_mu_succ_eq hP s hπ, ae_map_iff (measurable_cons t).aemeasurable hp]
  refine Measure.ae_compProd_of_ae_ae ((measurable_cons t) hp) ?_
  filter_upwards [h] with s' hs'
  rw [po_contKernel_apply hP hπ]
  exact hs'

/-- The rewards along `π` from `s` are integrable over the horizon `n` (the integrability that
Assumption 5.1.3 grants to every feasible plan). -/
def po_IntPlan (M : MDP S A) (n : ℕ) (s : S) (π : Plan S A) : Prop :=
  (∀ j < n, Integrable (rew M s π j) (mu M s π j)) ∧
    Integrable (fun h => M.uT (lastState s h)) (mu M s π n)

theorem po_intPlan_of_assumption513 {M : MDP S A} {n : ℕ} (h : Assumption513 M n) {s : S}
    {π : Plan S A} (hπ : π ∈ feasiblePlans M (n : ℕ∞) s) : po_IntPlan M n s π :=
  h.2.2 s π hπ

theorem po_rew_cons (M : MDP S A) (s s' : S) (π : Plan S A) (j : ℕ) (h : Fin j → S) :
    rew M s π (j + 1) (Fin.cons s' h) = rew (po_shift M 1) s' (po_cont π s') j h := by
  simp only [rew, lastState_cons]
  rfl

theorem po_plan_meas {M : MDP S A} {n : ℕ} {s : S} {π : Plan S A}
    (hπ : π ∈ feasiblePlans M ((n + 1 : ℕ) : ℕ∞) s) : ∀ j ≤ n, Measurable (π j) :=
  fun j hj => hπ.1 j (po_cast_lt.2 (by omega))

/-- The objective of the continuation plans, `s₁ ↦ J(s₁, C(π, s₁))`, is integrable against
`P₁(s, π₀; ·)`. -/
theorem po_integrable_J0T_cont {M : MDP S A} (hP : M.IsMarkov) {n : ℕ} {s : S}
    {π : Plan S A} (hπ : ∀ j ≤ n, Measurable (π j)) (hI : po_IntPlan M (n + 1) s π) :
    Integrable (fun s' => J0T (po_shift M 1) n s' (po_cont π s')) (M.P 0 (s, π 0 Fin.elim0)) := by
  unfold J0T
  refine Integrable.add (integrable_finsetSum _ fun j hj => ?_) ?_
  · refine Integrable.const_mul ?_ _
    have hj : j < n := Finset.mem_range.1 hj
    have := (po_integrable_cont hP s (fun k hk => hπ k (by omega)) (hI.1 (j + 1) (by omega))).1
    refine this.congr (Filter.Eventually.of_forall fun s' => ?_)
    simp only [expRew, po_rew_cons]
  · refine Integrable.const_mul ?_ _
    have := (po_integrable_cont hP s hπ hI.2).1
    refine this.congr (Filter.Eventually.of_forall fun s' => ?_)
    simp only [lastState_cons]
    rfl

/-- For almost every first state `s₁`, the rewards along the continuation plan `C(π, s₁)` are
integrable. -/
theorem po_ae_IntPlan_cont {M : MDP S A} (hP : M.IsMarkov) {n : ℕ} {s : S}
    {π : Plan S A} (hπ : ∀ j ≤ n, Measurable (π j)) (hI : po_IntPlan M (n + 1) s π) :
    ∀ᵐ s' ∂M.P 0 (s, π 0 Fin.elim0), po_IntPlan (po_shift M 1) n s' (po_cont π s') := by
  have h1 : ∀ j, ∀ᵐ s' ∂M.P 0 (s, π 0 Fin.elim0), j < n →
      Integrable (rew (po_shift M 1) s' (po_cont π s') j)
        (mu (po_shift M 1) s' (po_cont π s') j) := by
    intro j
    by_cases hj : j < n
    · have := (po_integrable_cont hP s (fun k hk => hπ k (by omega)) (hI.1 (j + 1) (by omega))).2
      filter_upwards [this] with s' hs' _
      refine hs'.congr (Filter.Eventually.of_forall fun h => ?_)
      exact po_rew_cons M s s' π j h
    · exact Filter.Eventually.of_forall fun _ h => absurd h hj
  have h2 := (po_integrable_cont hP s hπ hI.2).2
  filter_upwards [ae_all_iff.2 h1, h2] with s' hs1 hs2
  refine ⟨fun j hj => hs1 j hj, ?_⟩
  refine hs2.congr (Filter.Eventually.of_forall fun h => ?_)
  simp only [lastState_cons]
  rfl

/-- **The recursive form of the objective** (Miao, Lemma 6.3.1 at date `0`, p. 165):
`J₀ⁿ⁺¹(s, π) = u₀(s, π₀) + β ∫ J₁ⁿ⁺¹(s₁, C(π, s₁)) P₁(s, π₀; ds₁)`, where the objective of the
continuation is that of the process from date `1` over the remaining horizon `n`. -/
theorem po_J0T_succ {M : MDP S A} (hP : M.IsMarkov) {n : ℕ} {s : S} {π : Plan S A}
    (hπ : ∀ j ≤ n, Measurable (π j)) (hI : po_IntPlan M (n + 1) s π) :
    J0T M (n + 1) s π = M.u 0 (s, π 0 Fin.elim0) +
      M.β * ∫ s', J0T (po_shift M 1) n s' (po_cont π s') ∂M.P 0 (s, π 0 Fin.elim0) := by
  have hR : ∀ j < n, Integrable (fun s' => expRew (po_shift M 1) s' (po_cont π s') j)
      (M.P 0 (s, π 0 Fin.elim0)) := fun j hj => by
    have := (po_integrable_cont hP s (fun k hk => hπ k (by omega)) (hI.1 (j + 1) (by omega))).1
    refine this.congr (Filter.Eventually.of_forall fun s' => ?_)
    simp only [expRew, po_rew_cons]
  have hR' : ∀ j < n, expRew M s π (j + 1) =
      ∫ s', expRew (po_shift M 1) s' (po_cont π s') j ∂M.P 0 (s, π 0 Fin.elim0) := fun j hj => by
    rw [expRew, po_integral_mu_succ hP s (fun k hk => hπ k (by omega)) (hI.1 (j + 1) (by omega))]
    simp only [expRew, po_rew_cons]
  have hTi := (po_integrable_cont hP s hπ hI.2).1
  have hT : ∫ h, M.uT (lastState s h) ∂mu M s π (n + 1) =
      ∫ s', ∫ h, (po_shift M 1).uT (lastState s' h) ∂mu (po_shift M 1) s' (po_cont π s') n
        ∂M.P 0 (s, π 0 Fin.elim0) := by
    rw [po_integral_mu_succ hP s hπ hI.2]
    simp only [lastState_cons]
    rfl
  have hTi' : Integrable (fun s' => ∫ h, (po_shift M 1).uT (lastState s' h)
      ∂mu (po_shift M 1) s' (po_cont π s') n) (M.P 0 (s, π 0 Fin.elim0)) := by
    refine hTi.congr (Filter.Eventually.of_forall fun s' => ?_)
    simp only [lastState_cons]
    rfl
  unfold J0T
  rw [integral_add (integrable_finsetSum _ fun j hj => (hR j (Finset.mem_range.1 hj)).const_mul _)
    (hTi'.const_mul _), integral_finsetSum _ fun j hj => (hR j (Finset.mem_range.1 hj)).const_mul _,
    integral_const_mul, Finset.sum_range_succ', hT, expRew_zero]
  simp only [integral_const_mul, mul_add, Finset.mul_sum]
  have hs : ∀ j ∈ Finset.range n, M.β ^ (j + 1) * expRew M s π (j + 1) =
      M.β * (M.β ^ j * ∫ s', expRew (po_shift M 1) s' (po_cont π s') j
        ∂M.P 0 (s, π 0 Fin.elim0)) := fun j hj => by
    rw [hR' j (Finset.mem_range.1 hj), pow_succ]
    ring
  rw [Finset.sum_congr rfl hs]
  have : (po_shift M 1).β = M.β := rfl
  simp only [this, pow_zero, one_mul, pow_succ]
  ring

end Miao.InfiniteHorizonDP

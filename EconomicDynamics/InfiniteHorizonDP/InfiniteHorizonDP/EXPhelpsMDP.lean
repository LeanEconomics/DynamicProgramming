/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.EXPhelps
import InfiniteHorizonDP.IHVerification
import InfiniteHorizonDP.MDPKernelTools

/-!
# Exercises 7.6 and 7.10: verification of the value function of Example 7.5.1 by §7.1

Miao, §7.6, Exercises 6 and 10, pp. 229–230. Example 7.5.1 as a Markov decision process of
Chapter 5 (`ex7_phMDP`): the state is cash on hand `x > 0`, the action is the saving
`s ∈ Γ(x) = (0, x)` (both in `po61_Pos`), the next state is `R′s` with `R′ ~ ν` iid
(`ex7_phKernel`), the reward is `u(x − s)`, CRRA with `γ ≠ 1`. The value function of
Exercise 7.6 is `V(x) = A^{−γ} u(x)` (`ex7_phW`) with `A = 1 − (βm)^{1/γ}`, `m = E[R^{1−γ}]`
(`ex7_phm`), and the policy saves the fraction `1 − A` (`ex7_phg`).

* `ex7_ph_bellman`: `V` solves the Bellman equation (7.2) of the MDP and the policy is a
  measurable selection of `G` (with the integrability needed in Theorem 7.1.2).
* `ex7_ph_moment`: along the stationary plan saving the fraction `δ`,
  `E[x_n^p] = (δ^p E[R^p])ⁿ x₀^p`; `ex7_ph_moment_le`: along every feasible plan,
  `E[x_n^p] ≤ E[R^p]ⁿ x₀^p` for `p > 0`.
* **Exercise 7.6, `γ < 1`** (`ex_7_6`): Assumption 5.1.4 holds (`ex7_ph_assumption514`), and the
  transversality condition (7.4) holds along **every** feasible plan (`ex7_ph_tvc_all`), so
  Theorem 7.1.2 (`theorem_7_1_2`) applies verbatim: `V` is the value function and `c = Ax` is
  optimal.
* **Exercise 7.6, `γ > 1`** (`ex_7_6_gt`): (7.4) fails along some feasible plans
  (`ex_7_10_tvc_fails`, a plan saving a small fraction `δ`, with `βmδ^{1−γ} > 1`), so Theorem 7.1.2
  does not apply; Corollary 7.1.1 (`corollary_7_1_1`) does: the policy plan is in `Π̂` and every
  feasible plan outside `Π̂` has `J = −∞` (`ex7_ph_J_bot`), since `u(c) ≤ V(x)/A^{−γ} ≤ 0` and
  `βⁿE V(x_n) ↛ 0`. This uses Assumption 5.1.4 as a hypothesis (it is the standing assumption of
  §7.1; for `γ > 1` it restricts `ν`, see the corrections).
* **Exercise 7.10** (`ex_7_10_all_plans`): (7.4) for all plans holds for `γ < 1` and fails for
  `γ > 1`; the relation of (7.4) to (7.35) along the optimal plan is in `EXPhelpsTVC`.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-! ### The model -/

/-- The next state `x′ = R′ s` from `((x, s), R′)`. -/
def ex7_phNext (q : (po61_Pos × po61_Pos) × po61_Pos) : po61_Pos :=
  ⟨q.2.1 * q.1.2.1, mul_pos q.2.2 q.1.2.2⟩

theorem ex7_phNext_measurable : Measurable ex7_phNext :=
  ((measurable_subtype_coe.comp measurable_snd).mul
    (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))).subtype_mk

/-- The transition of Example 7.5.1: from `(x, s)` to `R′s`, `R′ ~ ν`. -/
noncomputable def ex7_phKernel (ν : Measure po61_Pos) : Kernel (po61_Pos × po61_Pos) po61_Pos :=
  pushKernel (Kernel.const _ ν) ex7_phNext

variable {ν : Measure po61_Pos}

theorem ex7_phKernel_apply [IsProbabilityMeasure ν] (p : po61_Pos × po61_Pos) :
    ex7_phKernel ν p = ν.map fun r => ex7_phNext (p, r) := by
  rw [ex7_phKernel, pushKernel_apply _ ex7_phNext_measurable, Kernel.const_apply]

theorem ex7_phKernel_markov [IsProbabilityMeasure ν] : IsMarkovKernel (ex7_phKernel ν) :=
  isMarkovKernel_pushKernel _ ex7_phNext_measurable

/-- **Example 7.5.1 as a Markov decision process** (Miao, pp. 227, 229): state `x > 0`, saving
`s ∈ (0, x)`, next state `R′s`, reward `u(x − s)`. -/
noncomputable def ex7_phMDP (γ β : ℝ) (ν : Measure po61_Pos) : MDP po61_Pos po61_Pos where
  Γ := fun x => {s | s.1 < x.1}
  P := fun _ => ex7_phKernel ν
  u := fun _ p => cs_crra γ (p.1.1 - p.2.1)
  uT := fun _ => 0
  β := β

/-- `m = E[R^{1−γ}]`. -/
noncomputable def ex7_phm (ν : Measure po61_Pos) (γ : ℝ) : ℝ := ∫ r, r.1 ^ (1 - γ) ∂ν

/-- The value function of Exercise 7.6, `V(x) = A^{−γ} u(x)`. -/
noncomputable def ex7_phW (γ β : ℝ) (ν : Measure po61_Pos) (x : po61_Pos) : ℝ :=
  ex7_phA β (ex7_phm ν γ) γ ^ (-γ) * cs_crra γ x.1

/-- The stationary policy saving the fraction `δ` of cash on hand. -/
def ex7_phg (δ : po61_Pos) (x : po61_Pos) : po61_Pos := ⟨δ.1 * x.1, mul_pos δ.2 x.2⟩

theorem ex7_crra_measurable (γ : ℝ) : Measurable (cs_crra γ) := by
  by_cases h : γ = 1
  · have e : cs_crra γ = Real.log := funext fun c => by simp [cs_crra, h]
    rw [e]; exact Real.measurable_log
  · have e : cs_crra γ = fun c => c ^ (1 - γ) / (1 - γ) := funext fun c => by simp [cs_crra, h]
    rw [e]; exact (measurable_id.pow_const _).div_const _

theorem ex7_phW_measurable (γ β : ℝ) (ν : Measure po61_Pos) : Measurable (ex7_phW γ β ν) :=
  measurable_const.mul ((ex7_crra_measurable γ).comp measurable_subtype_coe)

theorem ex7_phg_measurable (δ : po61_Pos) : Measurable (ex7_phg δ) :=
  (measurable_const.mul measurable_subtype_coe).subtype_mk

theorem ex7_ph_markov [IsProbabilityMeasure ν] (γ β : ℝ) : (ex7_phMDP γ β ν).IsMarkov :=
  fun _ => ex7_phKernel_markov

theorem ex7_ph_stationary (γ β : ℝ) : (ex7_phMDP γ β ν).IsStationary := fun _ => ⟨rfl, rfl⟩

theorem ex7_ph_u_measurable (γ β : ℝ) (t : ℕ) : Measurable ((ex7_phMDP γ β ν).u t) :=
  (ex7_crra_measurable γ).comp ((measurable_subtype_coe.comp measurable_fst).sub
    (measurable_subtype_coe.comp measurable_snd))

/-- Integrals against the transition: `∫ f dP(x, s; ·) = ∫ f(R s) ν(dR)`. -/
theorem ex7_ph_integral [IsProbabilityMeasure ν] {f : po61_Pos → ℝ} (hf : Measurable f)
    (p : po61_Pos × po61_Pos) :
    (Integrable f (ex7_phKernel ν p) ↔
      Integrable (fun r : po61_Pos => f ⟨r.1 * p.2.1, mul_pos r.2 p.2.2⟩) ν) ∧
      ∫ x, f x ∂ex7_phKernel ν p = ∫ r, f ⟨r.1 * p.2.1, mul_pos r.2 p.2.2⟩ ∂ν := by
  have hm : Measurable fun r => ex7_phNext (p, r) :=
    ex7_phNext_measurable.comp measurable_prodMk_left
  rw [ex7_phKernel_apply]
  exact ⟨integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable,
    integral_map hm.aemeasurable hf.aestronglyMeasurable⟩

/-! ### The Bellman equation -/

/-- **Exercise 7.6, the Bellman equation of the MDP** (Miao, p. 229), `γ ≠ 1`: with
`0 < βm < 1`, `V = A^{−γ}u` solves (7.2), `V` is integrable against every `P(x, s; ·)`, and the
policy saving the fraction `1 − A` is a measurable selection of `G` at every date. -/
theorem ex7_ph_bellman [IsProbabilityMeasure ν] {γ β : ℝ} (hγ : 0 < γ) (hγ1 : γ ≠ 1)
    (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν) (hbm : 0 < β * ex7_phm ν γ)
    (hbm1 : β * ex7_phm ν γ < 1) :
    let A := ex7_phA β (ex7_phm ν γ) γ
    ∃ hA : 0 < 1 - A,
    ih_Bellman (ex7_phMDP γ β ν) (fun x => (ex7_phW γ β ν x : EReal)) ∧
      (∀ x, ∀ s ∈ (ex7_phMDP γ β ν).Γ x,
        Integrable (ex7_phW γ β ν) ((ex7_phMDP γ β ν).P 0 (x, s))) ∧
      ih_GeneratedBy (ex7_phMDP γ β ν) (fun x => (ex7_phW γ β ν x : EReal))
        (fun _ => ex7_phg ⟨1 - A, hA⟩) := by
  intro A
  obtain ⟨hA0, hA1, -⟩ := ex_7_6_constants hγ hbm hbm1
  have hA : 0 < 1 - A := by linarith
  refine ⟨hA, ?_⟩
  have hI : ∀ x s : po61_Pos, Integrable (ex7_phW γ β ν) ((ex7_phMDP γ β ν).P 0 (x, s)) ∧
      ∫ y, ex7_phW γ β ν y ∂(ex7_phMDP γ β ν).P 0 (x, s) =
        ∫ r, A ^ (-γ) * cs_crra γ (r.1 * s.1) ∂ν := fun x s => by
    obtain ⟨h1, h2⟩ := ex7_ph_integral (ν := ν) (ex7_phW_measurable γ β ν) (x, s)
    refine ⟨h1.2 ?_, h2⟩
    exact ((ex7_integral_crra hγ1 s.2 hm).1.const_mul _)
  have hval : ∀ x s : po61_Pos, ih_bellmanVal (ex7_phMDP γ β ν)
      (fun x => (ex7_phW γ β ν x : EReal)) x s =
      ((cs_crra γ (x.1 - s.1) + β * ∫ r, A ^ (-γ) * cs_crra γ (r.1 * s.1) ∂ν : ℝ) : EReal) :=
    fun x s => by rw [ih_bellmanVal_coe (hI x s).1, (hI x s).2]; rfl
  have hB := fun x : po61_Pos => ex_7_6_bellman hγ hγ1 hm hbm hbm1 x.2
  have hW : ∀ x : po61_Pos, ex7_phW γ β ν x = A ^ (-γ) * cs_crra γ x.1 := fun _ => rfl
  have hG : ∀ x, ex7_phg ⟨1 - A, hA⟩ x ∈ ih_G (ex7_phMDP γ β ν)
      (fun x => (ex7_phW γ β ν x : EReal)) x := fun x => by
    obtain ⟨-, -, hlt, heq⟩ := hB x
    refine ⟨hlt, ?_⟩
    rw [hval]
    change _ = ((ex7_phW γ β ν x : ℝ) : EReal)
    rw [hW]
    exact congrArg _ heq
  refine ⟨fun x => le_antisymm ?_ (iSup₂_le fun s hs => ?_), fun x s _ => (hI x s).1,
    fun _ => ⟨ex7_phg_measurable _, hG⟩⟩
  · exact le_iSup₂_of_le (f := fun s (_ : s ∈ (ex7_phMDP γ β ν).Γ x) => ih_bellmanVal
      (ex7_phMDP γ β ν) (fun x => (ex7_phW γ β ν x : EReal)) x s) _ (hG x).1 (hG x).2.ge
  · rw [hval]
    change _ ≤ ((ex7_phW γ β ν x : ℝ) : EReal)
    rw [hW]
    exact EReal.coe_le_coe_iff.2 ((hB x).1 s.1 s.2 hs)

/-! ### Moments along plans -/

/-- The last-date decomposition for the MDP: `∫ f(x_{t+1}) dμᵗ⁺¹ = ∫ ∫ f(R s_t) ν(dR) dμᵗ`. -/
theorem ex7_ph_lintegral_succ [IsProbabilityMeasure ν] (γ β : ℝ) (x₀ : po61_Pos)
    {σ : Plan po61_Pos po61_Pos} {t : ℕ} (hσ : Measurable (σ t)) {f : po61_Pos → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ h, f (lastState x₀ h) ∂mu (ex7_phMDP γ β ν) x₀ σ (t + 1) =
      ∫⁻ h, ∫⁻ r, f ⟨r.1 * (σ t h).1, mul_pos r.2 (σ t h).2⟩ ∂ν
        ∂mu (ex7_phMDP γ β ν) x₀ σ t := by
  rw [mu_succ_lintegral _ (ex7_ph_markov γ β) x₀ hσ (f := fun h => f (lastState x₀ h))
    (hf.comp (measurable_lastState x₀ (t + 1)))]
  refine lintegral_congr fun h => ?_
  simp only [lastState_snoc]
  change ∫⁻ s, f s ∂ex7_phKernel ν (lastState x₀ h, σ t h) = _
  rw [ex7_phKernel_apply]
  change ∫⁻ s, f s ∂Measure.map (ex7_phNext ∘ Prod.mk (lastState x₀ h, σ t h)) ν = _
  rw [lintegral_map hf (ex7_phNext_measurable.comp measurable_prodMk_left)]
  rfl

/-- `∫⁻ (R s)^p ν(dR) = s^p E[R^p]`. -/
theorem ex7_ph_lintegral_rpow {p : ℝ} (hmp : Integrable (fun r : po61_Pos => r.1 ^ p) ν)
    (s : po61_Pos) :
    ∫⁻ r, ENNReal.ofReal ((r.1 * s.1) ^ p) ∂ν =
      ENNReal.ofReal (∫ r, r.1 ^ p ∂ν) * ENNReal.ofReal (s.1 ^ p) := by
  have e : ∀ r : po61_Pos, ENNReal.ofReal ((r.1 * s.1) ^ p) =
      ENNReal.ofReal (r.1 ^ p) * ENNReal.ofReal (s.1 ^ p) := fun r => by
    rw [Real.mul_rpow r.2.le s.2.le, ENNReal.ofReal_mul (Real.rpow_pos_of_pos r.2 _).le]
  simp only [e]
  rw [lintegral_mul_const _ ((measurable_subtype_coe.pow_const p).ennreal_ofReal),
    ofReal_integral_eq_lintegral_ofReal hmp
      (Eventually.of_forall fun r => (Real.rpow_pos_of_pos r.2 _).le)]

/-- Moments of cash on hand at date `0`. -/
theorem ex7_ph_lintegral_zero (γ β : ℝ) (x₀ : po61_Pos) (σ : Plan po61_Pos po61_Pos) (p : ℝ) :
    ∫⁻ h, ENNReal.ofReal ((lastState x₀ h).1 ^ p) ∂mu (ex7_phMDP γ β ν) x₀ σ 0 =
      ENNReal.ofReal (x₀.1 ^ p) := by
  rw [mu_zero, lintegral_dirac' _ (f := fun h => ENNReal.ofReal ((lastState x₀ h).1 ^ p))
    (((measurable_subtype_coe.pow_const p).ennreal_ofReal).comp (measurable_lastState x₀ 0))]
  rfl

/-- **Moments along the stationary plan saving the fraction `δ`**:
`∫⁻ x_n^p dμⁿ = (δ^p E[R^p])ⁿ x₀^p`. -/
theorem ex7_ph_moment [IsProbabilityMeasure ν] (γ β : ℝ) (δ x₀ : po61_Pos) {p : ℝ}
    (hmp : Integrable (fun r : po61_Pos => r.1 ^ p) ν) (n : ℕ) :
    ∫⁻ h, ENNReal.ofReal ((lastState x₀ h).1 ^ p)
        ∂mu (ex7_phMDP γ β ν) x₀ (po_genPlan (fun _ => ex7_phg δ) x₀) n =
      ENNReal.ofReal ((δ.1 ^ p * ∫ r, r.1 ^ p ∂ν) ^ n * x₀.1 ^ p) := by
  have hmp0 : 0 ≤ ∫ r, r.1 ^ p ∂ν := integral_nonneg fun r => (Real.rpow_pos_of_pos r.2 _).le
  have hδp : 0 < δ.1 ^ p := Real.rpow_pos_of_pos δ.2 _
  induction n with
  | zero => rw [ex7_ph_lintegral_zero]; simp
  | succ n ih =>
    rw [ex7_ph_lintegral_succ γ β x₀ ((ex7_phg_measurable δ).comp (measurable_lastState x₀ n))
      ((measurable_subtype_coe.pow_const p).ennreal_ofReal)]
    have e : ∀ h : Fin n → po61_Pos, ∫⁻ r, ENNReal.ofReal ((r.1 * ((po_genPlan
        (fun _ => ex7_phg δ) x₀) n h).1) ^ p) ∂ν =
        ENNReal.ofReal (δ.1 ^ p * ∫ r, r.1 ^ p ∂ν) * ENNReal.ofReal ((lastState x₀ h).1 ^ p) :=
      fun h => by
      rw [ex7_ph_lintegral_rpow hmp]
      simp only [po_genPlan, ex7_phg]
      rw [Real.mul_rpow δ.2.le (lastState x₀ h).2.le, ENNReal.ofReal_mul hδp.le,
        ENNReal.ofReal_mul hδp.le]
      ring
    simp only [e]
    rw [lintegral_const_mul _ (f := fun h => ENNReal.ofReal ((lastState x₀ h).1 ^ p))
      (((measurable_subtype_coe.pow_const p).ennreal_ofReal).comp (measurable_lastState x₀ n)),
      ih, ← ENNReal.ofReal_mul (mul_nonneg hδp.le hmp0), pow_succ]
    ring_nf

/-- **Moments along every feasible plan**, `p > 0`: `∫⁻ x_n^p dμⁿ ≤ E[R^p]ⁿ x₀^p`, since the
saving is below cash on hand. -/
theorem ex7_ph_moment_le [IsProbabilityMeasure ν] (γ β : ℝ) {x₀ : po61_Pos}
    {σ : Plan po61_Pos po61_Pos} (hσ : σ ∈ feasiblePlans (ex7_phMDP γ β ν) ⊤ x₀) {p : ℝ}
    (hp : 0 < p) (hmp : Integrable (fun r : po61_Pos => r.1 ^ p) ν) (n : ℕ) :
    ∫⁻ h, ENNReal.ofReal ((lastState x₀ h).1 ^ p) ∂mu (ex7_phMDP γ β ν) x₀ σ n ≤
      ENNReal.ofReal ((∫ r, r.1 ^ p ∂ν) ^ n * x₀.1 ^ p) := by
  have hmp0 : 0 ≤ ∫ r, r.1 ^ p ∂ν := integral_nonneg fun r => (Real.rpow_pos_of_pos r.2 _).le
  induction n with
  | zero => rw [ex7_ph_lintegral_zero]; simp
  | succ n ih =>
    rw [ex7_ph_lintegral_succ γ β x₀ (hσ.1 n (WithTop.coe_lt_top n))
      ((measurable_subtype_coe.pow_const p).ennreal_ofReal)]
    have e : ∀ h : Fin n → po61_Pos, ∫⁻ r, ENNReal.ofReal ((r.1 * (σ n h).1) ^ p) ∂ν ≤
        ENNReal.ofReal (∫ r, r.1 ^ p ∂ν) * ENNReal.ofReal ((lastState x₀ h).1 ^ p) :=
      fun h => by
      rw [ex7_ph_lintegral_rpow hmp]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (σ n h).2.le (hσ.2 n (WithTop.coe_lt_top n) h).le hp.le))
    refine (lintegral_mono e).trans ?_
    rw [lintegral_const_mul _ (f := fun h => ENNReal.ofReal ((lastState x₀ h).1 ^ p))
      (((measurable_subtype_coe.pow_const p).ennreal_ofReal).comp (measurable_lastState x₀ n))]
    refine (mul_le_mul' le_rfl ih).trans_eq ?_
    rw [← ENNReal.ofReal_mul hmp0, pow_succ]
    ring_nf

/-- A nonnegative measurable function with `∫⁻ ofReal f ≤ ofReal c` is integrable with
`∫ f ≤ c`; with equality, `∫ f = c`. -/
theorem ex7_integrable_of_lintegral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) {c : ℝ} (hc : 0 ≤ c)
    (hle : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal c) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ c ∧
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ = ENNReal.ofReal c → ∫ x, f x ∂μ = c) := by
  have hnn : 0 ≤ᵐ[μ] f := Eventually.of_forall h0
  have hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ∞ := hle.trans_lt ENNReal.ofReal_lt_top
  refine ⟨⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hfin⟩, ?_, fun he => ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hc hle
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable, he,
      ENNReal.toReal_ofReal hc]

/-- Along the stationary plan saving `δ`: `x_n^p` is integrable and `E[x_n^p] = (δ^p E[R^p])ⁿ
x₀^p`. -/
theorem ex7_ph_moment_int [IsProbabilityMeasure ν] (γ β : ℝ) (δ x₀ : po61_Pos) {p : ℝ}
    (hmp : Integrable (fun r : po61_Pos => r.1 ^ p) ν) (n : ℕ) :
    Integrable (fun h => (lastState x₀ h).1 ^ p)
        (mu (ex7_phMDP γ β ν) x₀ (po_genPlan (fun _ => ex7_phg δ) x₀) n) ∧
      ∫ h, (lastState x₀ h).1 ^ p
        ∂mu (ex7_phMDP γ β ν) x₀ (po_genPlan (fun _ => ex7_phg δ) x₀) n =
        (δ.1 ^ p * ∫ r, r.1 ^ p ∂ν) ^ n * x₀.1 ^ p := by
  have hmp0 : 0 ≤ ∫ r, r.1 ^ p ∂ν := integral_nonneg fun r => (Real.rpow_pos_of_pos r.2 _).le
  have hc : 0 ≤ (δ.1 ^ p * ∫ r, r.1 ^ p ∂ν) ^ n * x₀.1 ^ p :=
    mul_nonneg (pow_nonneg (mul_nonneg (Real.rpow_pos_of_pos δ.2 _).le hmp0) _)
      (Real.rpow_pos_of_pos x₀.2 _).le
  have h := ex7_integrable_of_lintegral (μ := mu (ex7_phMDP γ β ν) x₀
    (po_genPlan (fun _ => ex7_phg δ) x₀) n)
    ((measurable_subtype_coe.pow_const p).comp (measurable_lastState x₀ n))
    (fun h => (Real.rpow_pos_of_pos (lastState x₀ h).2 _).le) hc
    (ex7_ph_moment γ β δ x₀ hmp n).le
  exact ⟨h.1, h.2.2 (ex7_ph_moment γ β δ x₀ hmp n)⟩

/-! ### The transversality condition (7.4) -/

/-- `V(x_n) = A^{−γ} x_n^{1−γ}/(1 − γ)` as a function of the history. -/
theorem ex7_phW_eq {γ β : ℝ} (hγ1 : γ ≠ 1) (x : po61_Pos) :
    ex7_phW γ β ν x =
      ex7_phA β (ex7_phm ν γ) γ ^ (-γ) / (1 - γ) * x.1 ^ (1 - γ) := by
  simp only [ex7_phW, cs_crra, hγ1, ↓reduceIte]
  ring

/-- **(7.4) along the stationary plan saving `δ`**:
`βⁿ E V(x_n) = (A^{−γ}/(1 − γ)) x₀^{1−γ} (βmδ^{1−γ})ⁿ`, with `V(x_n)` integrable. -/
theorem ex7_ph_tvc_formula [IsProbabilityMeasure ν] {γ β : ℝ} (hγ1 : γ ≠ 1)
    (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν) (δ x₀ : po61_Pos) (n : ℕ) :
    Integrable (fun h => ex7_phW γ β ν (lastState x₀ h))
        (mu (ex7_phMDP γ β ν) x₀ (po_genPlan (fun _ => ex7_phg δ) x₀) n) ∧
      β ^ n * ∫ h, ex7_phW γ β ν (lastState x₀ h)
        ∂mu (ex7_phMDP γ β ν) x₀ (po_genPlan (fun _ => ex7_phg δ) x₀) n =
        ex7_phA β (ex7_phm ν γ) γ ^ (-γ) / (1 - γ) * x₀.1 ^ (1 - γ) *
          (β * ex7_phm ν γ * δ.1 ^ (1 - γ)) ^ n := by
  obtain ⟨hI, hE⟩ := ex7_ph_moment_int γ β δ x₀ hm n
  simp only [ex7_phW_eq hγ1]
  refine ⟨hI.const_mul _, ?_⟩
  rw [integral_const_mul, hE, ex7_phm]
  ring

/-- **(7.4) along the optimal plan** (Miao, p. 229): with `δ = 1 − A = (βm)^{1/γ}`,
`βmδ^{1−γ} = δ < 1`, so `βⁿ E V(x_n) → 0`. -/
theorem ex7_ph_tvc_opt [IsProbabilityMeasure ν] {γ β : ℝ} (hγ : 0 < γ) (hγ1 : γ ≠ 1)
    (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν) (hbm : 0 < β * ex7_phm ν γ)
    (hbm1 : β * ex7_phm ν γ < 1) (hA : 0 < 1 - ex7_phA β (ex7_phm ν γ) γ) (x₀ : po61_Pos) :
    po_genPlan (fun _ => ex7_phg ⟨1 - ex7_phA β (ex7_phm ν γ) γ, hA⟩) x₀ ∈
      ih_PiHat (ex7_phMDP γ β ν) (ex7_phW γ β ν) x₀ := by
  set δ : po61_Pos := ⟨1 - ex7_phA β (ex7_phm ν γ) γ, hA⟩
  have hδ : δ.1 = (β * ex7_phm ν γ) ^ (1 / γ) := by simp [δ, ex7_phA]
  have hq : β * ex7_phm ν γ * δ.1 ^ (1 - γ) = δ.1 := by
    rw [hδ, ← Real.rpow_mul hbm.le]
    nth_rewrite 1 [← Real.rpow_one (β * ex7_phm ν γ)]
    rw [← Real.rpow_add hbm]
    congr 1; field_simp; ring
  have hδ1 : δ.1 < 1 := by
    rw [hδ]; exact Real.rpow_lt_one hbm.le hbm1 (by positivity)
  obtain ⟨hA', -, -, hg⟩ := ex7_ph_bellman hγ hγ1 hm hbm hbm1
  refine ⟨ih_genPlan_feasible hg x₀, fun n => (ex7_ph_tvc_formula hγ1 hm δ x₀ n).1, ?_⟩
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one δ.2.le hδ1).const_mul
    (ex7_phA β (ex7_phm ν γ) γ ^ (-γ) / (1 - γ) * x₀.1 ^ (1 - γ))
  rw [mul_zero] at hlim
  refine hlim.congr fun n => ?_
  change _ = β ^ n * _
  rw [(ex7_ph_tvc_formula hγ1 hm δ x₀ n).2, hq]

/-- Along every feasible plan, `γ < 1`: `V(x_n)` is integrable and
`0 ≤ E V(x_n) ≤ (A^{−γ}/(1 − γ)) mⁿ x₀^{1−γ}`. -/
theorem ex7_ph_W_bound [IsProbabilityMeasure ν] {γ β : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν) (hbm : 0 < β * ex7_phm ν γ)
    (hbm1 : β * ex7_phm ν γ < 1) {x₀ : po61_Pos}
    {σ : Plan po61_Pos po61_Pos} (hσ : σ ∈ feasiblePlans (ex7_phMDP γ β ν) ⊤ x₀) (n : ℕ) :
    Integrable (fun h => (lastState x₀ h).1 ^ (1 - γ)) (mu (ex7_phMDP γ β ν) x₀ σ n) ∧
    Integrable (fun h => ex7_phW γ β ν (lastState x₀ h)) (mu (ex7_phMDP γ β ν) x₀ σ n) ∧
      0 ≤ ∫ h, ex7_phW γ β ν (lastState x₀ h) ∂mu (ex7_phMDP γ β ν) x₀ σ n ∧
      ∫ h, ex7_phW γ β ν (lastState x₀ h) ∂mu (ex7_phMDP γ β ν) x₀ σ n ≤
        ex7_phA β (ex7_phm ν γ) γ ^ (-γ) / (1 - γ) * (ex7_phm ν γ ^ n * x₀.1 ^ (1 - γ)) := by
  have hp : 0 < 1 - γ := by linarith
  have hmp0 : 0 ≤ ex7_phm ν γ := integral_nonneg fun r => (Real.rpow_pos_of_pos r.2 _).le
  have h := ex7_integrable_of_lintegral (μ := mu (ex7_phMDP γ β ν) x₀ σ n)
    ((measurable_subtype_coe.pow_const (1 - γ)).comp (measurable_lastState x₀ n))
    (fun h => (Real.rpow_pos_of_pos (lastState x₀ h).2 _).le)
    (mul_nonneg (pow_nonneg hmp0 _) (Real.rpow_pos_of_pos x₀.2 _).le)
    (ex7_ph_moment_le γ β hσ hp hm n)
  have hK : 0 ≤ ex7_phA β (ex7_phm ν γ) γ ^ (-γ) / (1 - γ) :=
    div_nonneg (Real.rpow_pos_of_pos (ex_7_6_constants hγ hbm hbm1).1 _).le hp.le
  simp only [ex7_phW_eq hγ1.ne]
  refine ⟨h.1, h.1.const_mul _, ?_, ?_⟩
  · rw [integral_const_mul]
    exact mul_nonneg hK (integral_nonneg fun h => (Real.rpow_pos_of_pos (lastState x₀ h).2 _).le)
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left h.2.1 hK

/-! ### `γ < 1`: Theorem 7.1.2 applies -/

/-- For `γ < 1`, along every feasible plan, `0 ≤ u(c_t) ≤ x_t^{1−γ}/(1 − γ)`. -/
theorem ex7_ph_rew_bound {γ β : ℝ} (hγ1 : γ < 1) {x₀ : po61_Pos} {σ : Plan po61_Pos po61_Pos}
    (hσ : σ ∈ feasiblePlans (ex7_phMDP γ β ν) ⊤ x₀) (t : ℕ) (h : Fin t → po61_Pos) :
    0 ≤ rew (ex7_phMDP γ β ν) x₀ σ t h ∧
      rew (ex7_phMDP γ β ν) x₀ σ t h ≤ (lastState x₀ h).1 ^ (1 - γ) / (1 - γ) := by
  have hp : 0 < 1 - γ := by linarith
  have hs : (σ t h).1 < (lastState x₀ h).1 := hσ.2 t (WithTop.coe_lt_top t) h
  have hc : 0 < (lastState x₀ h).1 - (σ t h).1 := by linarith
  change 0 ≤ cs_crra γ ((lastState x₀ h).1 - (σ t h).1) ∧
    cs_crra γ ((lastState x₀ h).1 - (σ t h).1) ≤ _
  simp only [cs_crra, hγ1.ne, ↓reduceIte]
  refine ⟨div_nonneg (Real.rpow_pos_of_pos hc _).le hp.le, ?_⟩
  gcongr
  linarith [(σ t h).2]

/-- **Assumption 5.1.4 for Example 7.5.1, `γ < 1`**: the model is stationary, the rewards along
every feasible plan are integrable, and the partial sums converge in `[−∞, +∞]` (they increase). -/
theorem ex7_ph_assumption514 [IsProbabilityMeasure ν] {γ β : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (hβ : 0 < β) (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν)
    (hbm : 0 < β * ex7_phm ν γ) (hbm1 : β * ex7_phm ν γ < 1) :
    Assumption514 (ex7_phMDP γ β ν) := by
  refine ⟨ex7_ph_stationary γ β, fun x₀ σ hσ => ⟨fun t => ?_, ?_⟩⟩
  · have hb := (ex7_ph_W_bound hγ hγ1 hm hbm hbm1 hσ t).1
    refine (hb.div_const (1 - γ)).mono' ((measurable_rew _ x₀ (ex7_ph_u_measurable γ β t)
      (hσ.1 t (WithTop.coe_lt_top t))).aestronglyMeasurable) (Eventually.of_forall fun h => ?_)
    obtain ⟨h0, h1⟩ := ex7_ph_rew_bound hγ1 hσ t h
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  · have hmono : Monotone fun n => (partialSum (ex7_phMDP γ β ν) x₀ σ n : EReal) := by
      refine monotone_nat_of_le_succ fun n => EReal.coe_le_coe_iff.2 ?_
      simp only [partialSum]
      rw [Finset.sum_range_succ _ (n + 1)]
      have : 0 ≤ (ex7_phMDP γ β ν).β ^ (n + 1) * expRew (ex7_phMDP γ β ν) x₀ σ (n + 1) :=
        mul_nonneg (pow_nonneg hβ.le _)
          (integral_nonneg fun h => (ex7_ph_rew_bound hγ1 hσ (n + 1) h).1)
      linarith
    exact ⟨_, tendsto_atTop_iSup hmono⟩

/-- **The transversality condition (7.4) along every feasible plan, `γ < 1`** (Miao, p. 197):
`0 ≤ βⁿ E V(x_n) ≤ (A^{−γ}/(1 − γ)) x₀^{1−γ} (βm)ⁿ → 0`. -/
theorem ex7_ph_tvc_all [IsProbabilityMeasure ν] {γ β : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (hβ : 0 < β) (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν)
    (hbm : 0 < β * ex7_phm ν γ) (hbm1 : β * ex7_phm ν γ < 1) {x₀ : po61_Pos}
    {σ : Plan po61_Pos po61_Pos} (hσ : σ ∈ feasiblePlans (ex7_phMDP γ β ν) ⊤ x₀) :
    Tendsto (fun n => (ex7_phMDP γ β ν).β ^ n *
      ∫ h, ex7_phW γ β ν (lastState x₀ h) ∂mu (ex7_phMDP γ β ν) x₀ σ n) atTop (𝓝 0) := by
  set C := ex7_phA β (ex7_phm ν γ) γ ^ (-γ) / (1 - γ) * x₀.1 ^ (1 - γ)
  have hlim : Tendsto (fun n : ℕ => C * (β * ex7_phm ν γ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hbm.le hbm1).const_mul C
  refine squeeze_zero (fun n => mul_nonneg (pow_nonneg hβ.le _)
    (ex7_ph_W_bound hγ hγ1 hm hbm hbm1 hσ n).2.2.1) (fun n => ?_) hlim
  have := mul_le_mul_of_nonneg_left (ex7_ph_W_bound hγ hγ1 hm hbm hbm1 hσ n).2.2.2
    (pow_nonneg hβ.le n)
  change β ^ n * _ ≤ _
  refine this.trans_eq ?_
  simp only [C, mul_pow]
  ring

/-- **Exercise 7.6, `0 < γ < 1`** (Miao, p. 229): by Theorem 7.1.2, `V(x) = A^{−γ}u(x)` is the
value function of Example 7.5.1 and the plan generated by `c = Ax` (saving `(1 − A)x`) is
optimal from every `x₀`. All hypotheses of `theorem_7_1_2` are verified: the Bellman equation
(`ex7_ph_bellman`), Assumption 5.1.4 (`ex7_ph_assumption514`), the integrability of `V(x_n)` and
(7.4) along every feasible plan (`ex7_ph_W_bound`, `ex7_ph_tvc_all`). -/
theorem ex_7_6 [IsProbabilityMeasure ν] {γ β : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) (hβ : 0 < β)
    (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν)
    (hbm : 0 < β * ex7_phm ν γ) (hbm1 : β * ex7_phm ν γ < 1) :
    ∃ hA : 0 < 1 - ex7_phA β (ex7_phm ν γ) γ,
      (∀ x, V (ex7_phMDP γ β ν) x = ex7_phW γ β ν x) ∧
      ∀ x, IsOptimalPlan (ex7_phMDP γ β ν) x
        (po_genPlan (fun _ => ex7_phg ⟨1 - ex7_phA β (ex7_phm ν γ) γ, hA⟩) x) := by
  obtain ⟨hA, hB, hint, hg⟩ := ex7_ph_bellman hγ hγ1.ne hm hbm hbm1
  exact ⟨hA, theorem_7_1_2 (ex7_ph_markov γ β) hβ.le
    (ex7_ph_assumption514 hγ hγ1 hβ hm hbm hbm1) hB hint
    (fun _ _ hσ n => (ex7_ph_W_bound hγ hγ1 hm hbm hbm1 hσ n).2.1)
    (fun _ _ hσ => ex7_ph_tvc_all hγ hγ1 hβ hm hbm hbm1 hσ) hg⟩

/-! ### `γ > 1`: Corollary 7.1.1 -/

/-- For `γ > 1`, along every feasible plan, `A^{−γ}u(c_t) ≤ V(x_t) ≤ 0`. -/
theorem ex7_ph_rew_bound_gt {γ β : ℝ} (hγ1 : 1 < γ) {x₀ : po61_Pos}
    {σ : Plan po61_Pos po61_Pos} (hσ : σ ∈ feasiblePlans (ex7_phMDP γ β ν) ⊤ x₀) {B : ℝ}
    (hB : 0 < B) (hBdef : B = ex7_phA β (ex7_phm ν γ) γ ^ (-γ)) (t : ℕ) (h : Fin t → po61_Pos) :
    B * rew (ex7_phMDP γ β ν) x₀ σ t h ≤ ex7_phW γ β ν (lastState x₀ h) ∧
      ex7_phW γ β ν (lastState x₀ h) ≤ 0 := by
  have hp : 1 - γ < 0 := by linarith
  have hs : (σ t h).1 < (lastState x₀ h).1 := hσ.2 t (WithTop.coe_lt_top t) h
  have hc : 0 < (lastState x₀ h).1 - (σ t h).1 := by linarith
  have hx := (lastState x₀ h).2
  change B * cs_crra γ ((lastState x₀ h).1 - (σ t h).1) ≤ _ ∧ _
  rw [ex7_phW_eq hγ1.ne', ← hBdef]
  simp only [cs_crra, hγ1.ne', ↓reduceIte]
  have hlt : (lastState x₀ h).1 ^ (1 - γ) ≤ ((lastState x₀ h).1 - (σ t h).1) ^ (1 - γ) :=
    Real.rpow_le_rpow_of_nonpos hc (by linarith [(σ t h).2]) hp.le
  have hBp : B / (1 - γ) < 0 := div_neg_of_pos_of_neg hB hp
  constructor
  · rw [show B * (((lastState x₀ h).1 - (σ t h).1) ^ (1 - γ) / (1 - γ)) =
      B / (1 - γ) * ((lastState x₀ h).1 - (σ t h).1) ^ (1 - γ) by ring]
    exact mul_le_mul_of_nonpos_left hlt hBp.le
  · exact mul_nonpos_of_nonpos_of_nonneg hBp.le (Real.rpow_pos_of_pos hx _).le

/-- **Condition (b) of Corollary 7.1.1, `γ > 1`** (Miao, p. 199): under Assumption 5.1.4, a
feasible plan outside `Π̂` has `J = −∞`. Indeed `V(x_t)` is integrable
(`|V(x_t)| ≤ A^{−γ}|u(c_t)|`),
so outside `Π̂` the terms `βᵗ E V(x_t) ≤ 0` do not tend to `0`; since
`A^{−γ} βᵗ E u(c_t) ≤ βᵗ E V(x_t) ≤ 0`, the partial sums decrease and are unbounded below. -/
theorem ex7_ph_J_bot [IsProbabilityMeasure ν] {γ β : ℝ} (hγ : 0 < γ) (hγ1 : 1 < γ)
    (hβ : 0 < β) (hbm : 0 < β * ex7_phm ν γ) (hbm1 : β * ex7_phm ν γ < 1)
    (h514 : Assumption514 (ex7_phMDP γ β ν)) {x₀ : po61_Pos} {σ : Plan po61_Pos po61_Pos}
    (hσ : σ ∈ feasiblePlans (ex7_phMDP γ β ν) ⊤ x₀)
    (hout : σ ∉ ih_PiHat (ex7_phMDP γ β ν) (ex7_phW γ β ν) x₀) :
    J (ex7_phMDP γ β ν) x₀ σ = ⊥ := by
  set M := ex7_phMDP γ β ν
  set B := ex7_phA β (ex7_phm ν γ) γ ^ (-γ) with hBdef
  have hB : 0 < B := Real.rpow_pos_of_pos (ex_7_6_constants hγ hbm hbm1).1 _
  have hI := (h514.2 x₀ σ hσ).1
  have hbd := fun t h => ex7_ph_rew_bound_gt hγ1 hσ hB hBdef t h
  -- `V(x_t)` is integrable
  have hwI : ∀ n, Integrable (fun h => ex7_phW γ β ν (lastState x₀ h)) (mu M x₀ σ n) := by
    intro n
    refine ((hI n).norm.const_mul B).mono'
      ((ex7_phW_measurable γ β ν).comp (measurable_lastState x₀ n)).aestronglyMeasurable
      (Eventually.of_forall fun h => ?_)
    obtain ⟨h1, h2⟩ := hbd n h
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos h2,
      abs_of_nonpos (by nlinarith : rew M x₀ σ n h ≤ 0)]
    linarith
  -- hence (7.4) fails
  have hnot : ¬ Tendsto (fun n => M.β ^ n *
      ∫ h, ex7_phW γ β ν (lastState x₀ h) ∂mu M x₀ σ n) atTop (𝓝 0) :=
    fun hT => hout ⟨hσ, hwI, hT⟩
  set a : ℕ → ℝ := fun n => β ^ n * expRew M x₀ σ n
  set E : ℕ → ℝ := fun n => β ^ n * ∫ h, ex7_phW γ β ν (lastState x₀ h) ∂mu M x₀ σ n
  have haE : ∀ n, B * a n ≤ E n ∧ E n ≤ 0 := fun n => by
    have h1 : B * expRew M x₀ σ n ≤ ∫ h, ex7_phW γ β ν (lastState x₀ h) ∂mu M x₀ σ n := by
      rw [expRew, ← integral_const_mul]
      exact integral_mono ((hI n).const_mul B) (hwI n) fun h => (hbd n h).1
    have h2 : ∫ h, ex7_phW γ β ν (lastState x₀ h) ∂mu M x₀ σ n ≤ 0 :=
      integral_nonpos fun h => (hbd n h).2
    have hb := pow_nonneg hβ.le n
    exact ⟨by simpa [a, E, mul_left_comm] using mul_le_mul_of_nonneg_left h1 hb,
      mul_nonpos_of_nonneg_of_nonpos hb h2⟩
  have ha0 : ∀ n, a n ≤ 0 := fun n => by
    have := (haE n).1.trans (haE n).2
    by_contra hc; push Not at hc; nlinarith
  have hS : ∀ n, partialSum M x₀ σ (n + 1) = partialSum M x₀ σ n + a (n + 1) := fun n => by
    simp only [partialSum]; rw [Finset.sum_range_succ _ (n + 1)]; rfl
  have hanti : Antitone (partialSum M x₀ σ) :=
    antitone_nat_of_succ_le fun n => by rw [hS]; linarith [ha0 (n + 1)]
  by_cases hbdd : BddBelow (Set.range (partialSum M x₀ σ))
  · exfalso
    apply hnot
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have ha : Tendsto (fun n => a (n + 1)) atTop (𝓝 0) := by
      have := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
      rw [sub_self] at this
      exact this.congr fun n => by simp only [Function.comp_apply, hS]; ring
    have hE : Tendsto (fun n => E (n + 1)) atTop (𝓝 0) := by
      have hl : Tendsto (fun n => B * a (n + 1)) atTop (𝓝 0) := by
        simpa using ha.const_mul B
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
        (fun n => (haE (n + 1)).1) fun n => (haE (n + 1)).2
    exact (tendsto_add_atTop_iff_nat 1).1 hE
  · have hbot : Tendsto (partialSum M x₀ σ) atTop atBot := by
      refine tendsto_atTop_atBot_of_antitone hanti fun b => ?_
      by_contra hc
      push Not at hc
      exact hbdd ⟨b, by rintro _ ⟨n, rfl⟩; exact (hc n).le⟩
    have hE : Tendsto (fun n => (partialSum M x₀ σ n : EReal)) atTop (𝓝 ⊥) :=
      EReal.tendsto_nhds_bot_iff_real.2 fun x =>
        (hbot.eventually (eventually_lt_atBot x)).mono fun n hn => EReal.coe_lt_coe_iff.2 hn
    exact tendsto_nhds_unique (J_spec h514 hσ) hE

/-- **Exercise 7.6, `γ > 1`** (Miao, p. 229): under Assumption 5.1.4, by Corollary 7.1.1,
`V(x) = A^{−γ}u(x) = V̂(x)` is the value function of Example 7.5.1 and the plan generated by
`c = Ax` attains it. Condition (a) is `ex7_ph_tvc_opt`; condition (b) holds because the plans
outside `Π̂` have `J = −∞` (`ex7_ph_J_bot`). (7.4) does not hold for all plans
(`ex_7_10_tvc_fails`), so Theorem 7.1.2 itself does not apply. -/
theorem ex_7_6_gt [IsProbabilityMeasure ν] {γ β : ℝ} (hγ1 : 1 < γ) (hβ : 0 < β)
    (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν)
    (hbm : 0 < β * ex7_phm ν γ) (hbm1 : β * ex7_phm ν γ < 1)
    (h514 : Assumption514 (ex7_phMDP γ β ν)) :
    ∃ hA : 0 < 1 - ex7_phA β (ex7_phm ν γ) γ, ∀ x,
      V (ex7_phMDP γ β ν) x = ex7_phW γ β ν x ∧
      (ex7_phW γ β ν x : EReal) = ih_VHat (ex7_phMDP γ β ν) (ex7_phW γ β ν) x ∧
      ih_VHat (ex7_phMDP γ β ν) (ex7_phW γ β ν) x = J (ex7_phMDP γ β ν) x
        (po_genPlan (fun _ => ex7_phg ⟨1 - ex7_phA β (ex7_phm ν γ) γ, hA⟩) x) := by
  have hγ : 0 < γ := by linarith
  obtain ⟨hA, hB, hint, hg⟩ := ex7_ph_bellman hγ hγ1.ne' hm hbm hbm1
  have ha := fun x => ex7_ph_tvc_opt hγ hγ1.ne' hm hbm hbm1 hA x
  refine ⟨hA, corollary_7_1_1 (ex7_ph_markov γ β) hβ.le h514 hB hint hg ha
    (fun x σ hσ => ?_)⟩
  by_cases hin : σ ∈ ih_PiHat (ex7_phMDP γ β ν) (ex7_phW γ β ν) x
  · exact ⟨σ, hin, le_rfl⟩
  · exact ⟨_, ha x, by rw [ex7_ph_J_bot hγ hγ1 hβ hbm hbm1 h514 hσ hin]; exact bot_le⟩

/-! ### Exercise 7.10: (7.4) for all plans -/

/-- **(7.4) fails along some feasible plans when `γ > 1`** (Exercise 7.10): the stationary plan
saving the fraction `δ ∈ (0, 1)` with `βmδ^{1−γ} > 1` is feasible and
`βⁿ E V(x_n) = (A^{−γ}/(1 − γ)) x₀^{1−γ}(βmδ^{1−γ})ⁿ → −∞`. -/
theorem ex_7_10_tvc_fails [IsProbabilityMeasure ν] {γ β : ℝ} (hγ1 : 1 < γ)
    (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν)
    (hbm : 0 < β * ex7_phm ν γ) (hbm1 : β * ex7_phm ν γ < 1) (δ x₀ : po61_Pos) (hδ : δ.1 < 1)
    (hq : 1 < β * ex7_phm ν γ * δ.1 ^ (1 - γ)) :
    po_genPlan (fun _ => ex7_phg δ) x₀ ∈ feasiblePlans (ex7_phMDP γ β ν) ⊤ x₀ ∧
      ¬ Tendsto (fun n => (ex7_phMDP γ β ν).β ^ n * ∫ h, ex7_phW γ β ν (lastState x₀ h)
        ∂mu (ex7_phMDP γ β ν) x₀ (po_genPlan (fun _ => ex7_phg δ) x₀) n) atTop (𝓝 0) := by
  have hγ : 0 < γ := by linarith
  refine ⟨⟨fun j _ => (ex7_phg_measurable δ).comp (measurable_lastState x₀ j), fun j _ h => ?_⟩,
    fun hT => ?_⟩
  · change δ.1 * (lastState x₀ h).1 < (lastState x₀ h).1
    nlinarith [(lastState x₀ h).2]
  · set C := ex7_phA β (ex7_phm ν γ) γ ^ (-γ) / (1 - γ) * x₀.1 ^ (1 - γ)
    have hC : C ≠ 0 := by
      have hA0 := (ex_7_6_constants hγ hbm hbm1).1
      have : 1 - γ ≠ 0 := by linarith
      exact mul_ne_zero (div_ne_zero (Real.rpow_pos_of_pos hA0 _).ne' this)
        (Real.rpow_pos_of_pos x₀.2 _).ne'
    have h1 : Tendsto (fun n : ℕ => C * (β * ex7_phm ν γ * δ.1 ^ (1 - γ)) ^ n) atTop (𝓝 0) :=
      hT.congr fun n => by
        change β ^ n * _ = _
        rw [(ex7_ph_tvc_formula hγ1.ne' hm δ x₀ n).2]
    have h2 := h1.const_mul C⁻¹
    rw [mul_zero] at h2
    have h3 : Tendsto (fun n : ℕ => (β * ex7_phm ν γ * δ.1 ^ (1 - γ)) ^ n) atTop (𝓝 0) :=
      h2.congr fun n => by field_simp
    exact not_tendsto_nhds_of_tendsto_atTop (tendsto_pow_atTop_atTop_of_one_lt hq) 0 h3

/-- A saving fraction violating (7.4) exists when `γ > 1`: `δ = (βm/2)^{1/(γ−1)} ∈ (0, 1)` has
`βmδ^{1−γ} = 2`. -/
theorem ex7_exists_bad_delta {β m γ : ℝ} (hγ1 : 1 < γ) (hbm : 0 < β * m) (hbm1 : β * m < 1) :
    ∃ δ : po61_Pos, δ.1 < 1 ∧ 1 < β * m * δ.1 ^ (1 - γ) := by
  have hb2 : 0 < β * m / 2 := by positivity
  have hg : 0 < 1 / (γ - 1) := by have : 0 < γ - 1 := by linarith
                                  positivity
  refine ⟨⟨(β * m / 2) ^ (1 / (γ - 1)), Real.rpow_pos_of_pos hb2 _⟩,
    Real.rpow_lt_one hb2.le (by linarith) hg, ?_⟩
  change 1 < β * m * ((β * m / 2) ^ (1 / (γ - 1))) ^ (1 - γ)
  rw [← Real.rpow_mul hb2.le, show 1 / (γ - 1) * (1 - γ) = -1 by
    have : γ - 1 ≠ 0 := by linarith
    field_simp; ring, Real.rpow_neg_one]
  rw [show β * m * (β * m / 2)⁻¹ = 2 by field_simp; exact div_self hbm.ne']
  norm_num

/-- **Exercise 7.10, (7.4) for all plans** (Miao, p. 230): for `0 < γ < 1` the transversality
condition (7.4) of Theorem 7.1.2 holds along every feasible plan; for `γ > 1` it fails along some
feasible plan, so only Corollary 7.1.1 (with its dominance condition (b)) applies. -/
theorem ex_7_10_all_plans [IsProbabilityMeasure ν] {γ β : ℝ} (hβ : 0 < β)
    (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν)
    (hbm : 0 < β * ex7_phm ν γ) (hbm1 : β * ex7_phm ν γ < 1) (x₀ : po61_Pos) :
    ((0 < γ ∧ γ < 1) → ∀ σ ∈ feasiblePlans (ex7_phMDP γ β ν) ⊤ x₀,
      Tendsto (fun n => (ex7_phMDP γ β ν).β ^ n *
        ∫ h, ex7_phW γ β ν (lastState x₀ h) ∂mu (ex7_phMDP γ β ν) x₀ σ n) atTop (𝓝 0)) ∧
    (1 < γ → ∃ σ ∈ feasiblePlans (ex7_phMDP γ β ν) ⊤ x₀,
      ¬ Tendsto (fun n => (ex7_phMDP γ β ν).β ^ n *
        ∫ h, ex7_phW γ β ν (lastState x₀ h) ∂mu (ex7_phMDP γ β ν) x₀ σ n) atTop (𝓝 0)) := by
  refine ⟨fun hγ σ hσ => ex7_ph_tvc_all hγ.1 hγ.2 hβ hm hbm hbm1 hσ, fun hγ1 => ?_⟩
  obtain ⟨δ, hδ, hq⟩ := ex7_exists_bad_delta hγ1 hbm hbm1
  exact ⟨_, ex_7_10_tvc_fails hγ1 hm hbm hbm1 δ x₀ hδ hq⟩

end Miao.InfiniteHorizonDP

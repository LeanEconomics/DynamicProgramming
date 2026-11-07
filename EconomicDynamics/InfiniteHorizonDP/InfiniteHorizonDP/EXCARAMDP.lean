/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.EXCARA
import InfiniteHorizonDP.EXPhelpsMDP
import InfiniteHorizonDP.IHVerification
import InfiniteHorizonDP.MDPKernelTools

/-!
# Exercise 7.7: optimality of the limit policy, and its failure without a no-Ponzi condition

Miao, §7.6, Exercise 7, p. 229: "Prove that limit policies are optimal for the infinite horizon
case and derive the value function." The model of `EXCARA` as a Markov decision process
(`ex7_caMDP`): the state is cash on hand `x ∈ ℝ`, the action is the saving `s ∈ ℝ` (no
borrowing constraint), the next state is `Rs + y′`, `y′ ~ μ` iid, the reward is `−e^{−γ(x−s)}`.

* `ex7_verif_le_plan`, `ex7_verif_eq_plan`: the proof of Theorem 7.1.2 (`ih_verif_le`,
  `ih_verif_eq`), plan by plan, without Assumption 5.1.4 (which need not hold here: a measurable
  plan can make `e^{−γc_t}` non-integrable); `ex7_J_spec_nonpos`: with `u ≤ 0` the partial sums
  of every plan converge in `[−∞, 0]`.
* `ex7_ca_bellman`: `V̄(x) = −Āe^{−ᾱx}` solves the Bellman equation (7.2) of the MDP and the
  limit saving policy `s̄` is a measurable selection of `G`.
* `ex7_ca_moment`: along the limit policy, `E[Āe^{−ᾱx_n}] = Āe^{−ᾱx₀}(βR)^{−n}`.
* **Exercise 7.7, corrected** (`ex_7_7`): the limit policy plan lies in `Π̂` (the plans along
  which (7.4) `βⁿ E V̄(x_n) → 0` holds; here `βⁿ E V̄(x_n) = V̄(x₀)R^{−n}`), attains `V̄(x₀)`, and
  every feasible plan in `Π̂` with integrable rewards has `J ≤ V̄(x₀)`: the limit policy is
  optimal among the plans satisfying the transversality (no-Ponzi) condition (7.4).
* **The book's claim is false** (`ex_7_7_ponzi`): over all feasible plans the value is
  `V ≡ 0` (consume `c` forever, rolling over the debt: `J = −e^{−γc}/(1 − β) → 0`), which exceeds
  `V̄(x) < 0`; the limit policy is not optimal and the supremum is not attained. Condition (b) of
  Corollary 7.1.1 fails.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-! ### The proof of Theorem 7.1.2 plan by plan -/

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- **The inequality of Theorem 7.1.2 for one plan** (Miao, p. 198): if `w` satisfies (7.5) at
every feasible action, `σ` is feasible with integrable rewards, its partial sums converge to
`J(s₀, σ)`, `w(s_n)` is integrable and (7.4) holds along `σ`, then `J(s₀, σ) ≤ w(s₀)`. The proof
is that of `ih_verif_le`, with Assumption 5.1.4 replaced by its consequences for `σ`. -/
theorem ex7_verif_le_plan {M : MDP S A} (hP : M.IsMarkov) (hst : M.IsStationary) (hβ : 0 ≤ M.β)
    {w : S → ℝ} (hle : ∀ s, ∀ a ∈ M.Γ s, Integrable w (M.P 0 (s, a)) ∧
      M.u 0 (s, a) + M.β * ∫ s', w s' ∂M.P 0 (s, a) ≤ w s)
    {s₀ : S} {σ : Plan S A} (hσ : σ ∈ feasiblePlans M ⊤ s₀)
    (hI : ∀ t, Integrable (rew M s₀ σ t) (mu M s₀ σ t))
    (hJ : Tendsto (fun n => (partialSum M s₀ σ n : EReal)) atTop (𝓝 (J M s₀ σ)))
    (hwI : ∀ n, Integrable (fun h => w (lastState s₀ h)) (mu M s₀ σ n))
    (h74 : Tendsto (fun n => M.β ^ n * ∫ h, w (lastState s₀ h) ∂mu M s₀ σ n) atTop (𝓝 0)) :
    J M s₀ σ ≤ w s₀ := by
  have hD : ∀ t h, 0 ≤ ih_slack M w s₀ σ t h := fun t h => by
    have := (hle _ _ (hσ.2 t (WithTop.coe_lt_top t) h)).2
    simp only [ih_slack, rew]
    rw [(hst t).2]
    linarith
  have hbound : ∀ n, partialSum M s₀ σ n ≤
      w s₀ - M.β ^ (n + 1) * ∫ h, w (lastState s₀ h) ∂mu M s₀ σ (n + 1) := fun n => by
    rw [ih_partialSum_telescope hP hst hσ hI hwI n]
    have : 0 ≤ ∑ t ∈ Finset.range (n + 1), M.β ^ t * ∫ h, ih_slack M w s₀ σ t h ∂mu M s₀ σ t :=
      Finset.sum_nonneg fun t _ => mul_nonneg (pow_nonneg hβ _) (integral_nonneg (hD t))
    linarith
  have hlim : Tendsto (fun n => w s₀ - M.β ^ (n + 1) *
      ∫ h, w (lastState s₀ h) ∂mu M s₀ σ (n + 1)) atTop (𝓝 (w s₀)) := by
    have := (h74.comp (tendsto_add_atTop_nat 1)).const_sub (w s₀)
    simpa using this
  exact le_of_tendsto_of_tendsto hJ (EReal.tendsto_coe.2 hlim)
    (Eventually.of_forall fun n => EReal.coe_le_coe_iff.2 (hbound n))

/-- **The equality of Theorem 7.1.2 for one plan** (Miao, p. 198): along a feasible plan with
integrable rewards, no slack in (7.5) and (7.4), `J(s₀, σ) = w(s₀)` (and the partial sums
converge to it). -/
theorem ex7_verif_eq_plan {M : MDP S A} (hP : M.IsMarkov) (hst : M.IsStationary) {w : S → ℝ}
    {s₀ : S} {σ : Plan S A} (hσ : σ ∈ feasiblePlans M ⊤ s₀)
    (hI : ∀ t, Integrable (rew M s₀ σ t) (mu M s₀ σ t))
    (hD : ∀ t h, ih_slack M w s₀ σ t h = 0)
    (hwI : ∀ n, Integrable (fun h => w (lastState s₀ h)) (mu M s₀ σ n))
    (h74 : Tendsto (fun n => M.β ^ n * ∫ h, w (lastState s₀ h) ∂mu M s₀ σ n) atTop (𝓝 0)) :
    Tendsto (fun n => (partialSum M s₀ σ n : EReal)) atTop (𝓝 (w s₀ : EReal)) ∧
      J M s₀ σ = w s₀ := by
  have heq : ∀ n, partialSum M s₀ σ n =
      w s₀ - M.β ^ (n + 1) * ∫ h, w (lastState s₀ h) ∂mu M s₀ σ (n + 1) := fun n => by
    rw [ih_partialSum_telescope hP hst hσ hI hwI n]
    simp [hD]
  have hlim : Tendsto (fun n => w s₀ - M.β ^ (n + 1) *
      ∫ h, w (lastState s₀ h) ∂mu M s₀ σ (n + 1)) atTop (𝓝 (w s₀)) := by
    have := (h74.comp (tendsto_add_atTop_nat 1)).const_sub (w s₀)
    simpa using this
  have hT : Tendsto (fun n => (partialSum M s₀ σ n : EReal)) atTop (𝓝 (w s₀ : EReal)) := by
    simp only [heq]
    exact EReal.tendsto_coe.2 hlim
  exact ⟨hT, by rw [J, hT.limUnder_eq]⟩

/-- With nonpositive rewards the partial sums of every plan decrease, so they converge in
`[−∞, +∞]` to `J(s₀, σ)`, and `J(s₀, σ) ≤ 0`. -/
theorem ex7_J_spec_nonpos {M : MDP S A} (hβ : 0 ≤ M.β) (hu : ∀ t p, M.u t p ≤ 0) (s₀ : S)
    (σ : Plan S A) :
    Tendsto (fun n => (partialSum M s₀ σ n : EReal)) atTop (𝓝 (J M s₀ σ)) ∧ J M s₀ σ ≤ 0 := by
  have hanti : Antitone fun n => (partialSum M s₀ σ n : EReal) := by
    refine antitone_nat_of_succ_le fun n => EReal.coe_le_coe_iff.2 ?_
    simp only [partialSum]
    rw [Finset.sum_range_succ _ (n + 1)]
    have : M.β ^ (n + 1) * expRew M s₀ σ (n + 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ _) (integral_nonpos fun h => hu _ _)
    linarith
  have hT := tendsto_atTop_iInf hanti
  have hJ : J M s₀ σ = ⨅ n, (partialSum M s₀ σ n : EReal) := by rw [J, hT.limUnder_eq]
  refine ⟨hJ ▸ hT, ?_⟩
  rw [hJ]
  refine (iInf_le _ 0).trans (EReal.coe_le_coe_iff.2 ?_)
  simp only [partialSum, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul]
  exact integral_nonpos fun h => hu _ _

/-! ### The model -/

/-- The transition of Exercise 7.7: from `(x, s)` to `Rs + y′`, `y′ ~ μ`. -/
noncomputable def ex7_caKernel (R : ℝ) (μ : Measure ℝ) : Kernel (ℝ × ℝ) ℝ :=
  pushKernel (Kernel.const _ μ) fun q : (ℝ × ℝ) × ℝ => R * q.1.2 + q.2

theorem ex7_caNext_measurable (R : ℝ) :
    Measurable fun q : (ℝ × ℝ) × ℝ => R * q.1.2 + q.2 := by fun_prop

/-- **Exercise 7.7 as a Markov decision process** (Miao, p. 229): cash on hand `x`, saving
`s ∈ ℝ`, next state `Rs + y′`, reward `−e^{−γ(x − s)}`. -/
noncomputable def ex7_caMDP (γ β R : ℝ) (μ : Measure ℝ) : MDP ℝ ℝ where
  Γ := fun _ => Set.univ
  P := fun _ => ex7_caKernel R μ
  u := fun _ p => -Real.exp (-(γ * (p.1 - p.2)))
  uT := fun _ => 0
  β := β

/-- The value function of Exercise 7.7, `V̄(x) = −Āe^{−ᾱx}`. -/
noncomputable def ex7_caW (γ β R : ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ :=
  -(ex7_caraAlim γ β R μ * Real.exp (-(ex7_caraAbar γ R * x)))

variable {μ : Measure ℝ}

theorem ex7_caKernel_apply [IsProbabilityMeasure μ] (R : ℝ) (p : ℝ × ℝ) :
    ex7_caKernel R μ p = μ.map fun y => R * p.2 + y := by
  rw [ex7_caKernel, pushKernel_apply _ (ex7_caNext_measurable R), Kernel.const_apply]

theorem ex7_ca_markov [IsProbabilityMeasure μ] (γ β R : ℝ) : (ex7_caMDP γ β R μ).IsMarkov :=
  fun _ => isMarkovKernel_pushKernel _ (ex7_caNext_measurable R)

theorem ex7_ca_stationary (γ β R : ℝ) : (ex7_caMDP γ β R μ).IsStationary :=
  fun _ => ⟨rfl, rfl⟩

theorem ex7_ca_u_nonpos (γ β R : ℝ) (t : ℕ) (p : ℝ × ℝ) : (ex7_caMDP γ β R μ).u t p ≤ 0 :=
  neg_nonpos.2 (Real.exp_pos _).le

theorem ex7_caW_measurable (γ β R : ℝ) : Measurable (ex7_caW γ β R μ) := by
  unfold ex7_caW; fun_prop

theorem ex7_caraSbar_measurable (γ β R : ℝ) : Measurable (ex7_caraSbar γ β R μ) := by
  unfold ex7_caraSbar; fun_prop

/-- Integrals against the transition: `∫ f dP(x, s; ·) = ∫ f(Rs + y) μ(dy)`. -/
theorem ex7_ca_integral [IsProbabilityMeasure μ] {R : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (p : ℝ × ℝ) :
    (Integrable f (ex7_caKernel R μ p) ↔ Integrable (fun y => f (R * p.2 + y)) μ) ∧
      ∫ x, f x ∂ex7_caKernel R μ p = ∫ y, f (R * p.2 + y) ∂μ := by
  have hm : Measurable fun y => R * p.2 + y := by fun_prop
  rw [ex7_caKernel_apply]
  exact ⟨integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable,
    integral_map hm.aemeasurable hf.aestronglyMeasurable⟩

/-- `V̄(Rs + y)` is integrable in `y`. -/
theorem ex7_caW_integrable [IsProbabilityMeasure μ] {γ β R ymin ymax : ℝ}
    (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) (s : ℝ) :
    Integrable (fun y => ex7_caW γ β R μ (R * s + y)) μ := by
  have e : (fun y => ex7_caW γ β R μ (R * s + y)) = fun y =>
      -(ex7_caraAlim γ β R μ * Real.exp (-(ex7_caraAbar γ R * R * s))) *
        Real.exp (-(ex7_caraAbar γ R * y)) := by
    funext y
    simp only [ex7_caW]
    rw [show -(ex7_caraAbar γ R * (R * s + y)) = -(ex7_caraAbar γ R * R * s) +
      -(ex7_caraAbar γ R * y) by ring, Real.exp_add]
    ring
  rw [e]
  exact (ex7_exp_integrable hμ _).const_mul _

/-! ### The Bellman equation -/

/-- **Exercise 7.7, the Bellman equation of the MDP** (Miao, p. 229), `R > 1`: `V̄` solves (7.2),
is integrable against every `P(x, s; ·)`, and the limit saving policy `s̄` is a measurable
selection of `G` at every date. -/
theorem ex7_ca_bellman [IsProbabilityMeasure μ] {γ β R ymin ymax : ℝ} (hγ : 0 < γ)
    (hβ : 0 < β) (hR : 1 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) :
    ih_Bellman (ex7_caMDP γ β R μ) (fun x => (ex7_caW γ β R μ x : EReal)) ∧
      (∀ x, ∀ s ∈ (ex7_caMDP γ β R μ).Γ x,
        Integrable (ex7_caW γ β R μ) ((ex7_caMDP γ β R μ).P 0 (x, s))) ∧
      ih_GeneratedBy (ex7_caMDP γ β R μ) (fun x => (ex7_caW γ β R μ x : EReal))
        (fun _ => ex7_caraSbar γ β R μ) := by
  have hI : ∀ x s : ℝ, Integrable (ex7_caW γ β R μ) ((ex7_caMDP γ β R μ).P 0 (x, s)) ∧
      ∫ y, ex7_caW γ β R μ y ∂(ex7_caMDP γ β R μ).P 0 (x, s) =
        ∫ y, ex7_caW γ β R μ (R * s + y) ∂μ := fun x s => by
    obtain ⟨h1, h2⟩ := ex7_ca_integral (μ := μ) (R := R) (ex7_caW_measurable γ β R) (x, s)
    exact ⟨h1.2 (ex7_caW_integrable hμ s), h2⟩
  have hval : ∀ x s : ℝ, ih_bellmanVal (ex7_caMDP γ β R μ)
      (fun x => (ex7_caW γ β R μ x : EReal)) x s =
      ((-Real.exp (-(γ * (x - s))) + β * ∫ y, ex7_caW γ β R μ (R * s + y) ∂μ : ℝ) : EReal) :=
    fun x s => by rw [ih_bellmanVal_coe (hI x s).1, (hI x s).2]; rfl
  have hB := fun x => ex_7_7_bellman hγ hβ hR hμ x
  have hG : ∀ x, ex7_caraSbar γ β R μ x ∈ ih_G (ex7_caMDP γ β R μ)
      (fun x => (ex7_caW γ β R μ x : EReal)) x := fun x => by
    refine ⟨Set.mem_univ _, ?_⟩
    rw [hval]
    exact congrArg _ (hB x).2.1.symm
  refine ⟨fun x => le_antisymm ?_ (iSup₂_le fun s _ => ?_), fun x s _ => (hI x s).1,
    fun _ => ⟨ex7_caraSbar_measurable γ β R, hG⟩⟩
  · exact le_iSup₂_of_le (f := fun s (_ : s ∈ (ex7_caMDP γ β R μ).Γ x) => ih_bellmanVal
      (ex7_caMDP γ β R μ) (fun x => (ex7_caW γ β R μ x : EReal)) x s) _ (hG x).1 (hG x).2.ge
  · rw [hval]
    refine EReal.coe_le_coe_iff.2 ?_
    rcases eq_or_ne s (ex7_caraSbar γ β R μ x) with h | h
    · rw [h]; exact (hB x).2.1.ge
    · exact ((hB x).1 s h).le.trans (hB x).2.1.ge

/-! ### Moments along the limit policy -/

/-- The last-date decomposition for the MDP: `∫⁻ f(x_{t+1}) dμᵗ⁺¹ = ∫⁻ ∫⁻ f(Rs_t + y) μ(dy)
dμᵗ`. -/
theorem ex7_ca_lintegral_succ [IsProbabilityMeasure μ] (γ β R : ℝ) (x₀ : ℝ)
    {σ : Plan ℝ ℝ} {t : ℕ} (hσ : Measurable (σ t)) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ h, f (lastState x₀ h) ∂mu (ex7_caMDP γ β R μ) x₀ σ (t + 1) =
      ∫⁻ h, ∫⁻ y, f (R * σ t h + y) ∂μ ∂mu (ex7_caMDP γ β R μ) x₀ σ t := by
  rw [mu_succ_lintegral _ (ex7_ca_markov γ β R) x₀ hσ (f := fun h => f (lastState x₀ h))
    (hf.comp (measurable_lastState x₀ (t + 1)))]
  refine lintegral_congr fun h => ?_
  simp only [lastState_snoc]
  change ∫⁻ s, f s ∂ex7_caKernel R μ (lastState x₀ h, σ t h) = _
  rw [ex7_caKernel_apply, lintegral_map hf (by fun_prop)]

/-- **Moments along the limit policy**: `∫⁻ Āe^{−ᾱx_n} dμⁿ = Āe^{−ᾱx₀}(βR)^{−n}`. -/
theorem ex7_ca_moment [IsProbabilityMeasure μ] {γ β R ymin ymax : ℝ} (hγ : 0 < γ) (hβ : 0 < β)
    (hR : 1 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) (x₀ : ℝ) (n : ℕ) :
    ∫⁻ h, ENNReal.ofReal (-ex7_caW γ β R μ (lastState x₀ h))
        ∂mu (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ => ex7_caraSbar γ β R μ) x₀) n =
      ENNReal.ofReal (-ex7_caW γ β R μ x₀ * ((β * R)⁻¹) ^ n) := by
  have hR0 : 0 < R := by linarith
  have hW : Measurable fun x => ENNReal.ofReal (-ex7_caW γ β R μ x) :=
    (ex7_caW_measurable γ β R).neg.ennreal_ofReal
  have hWn : ∀ x, 0 ≤ -ex7_caW γ β R μ x := fun x => by
    simp only [ex7_caW, neg_neg]; exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  -- one step: `∫⁻ −V̄(R s̄(x) + y) μ(dy) = −V̄(x)/(βR)`
  have hstep : ∀ x, ∫⁻ y, ENNReal.ofReal (-ex7_caW γ β R μ (R * ex7_caraSbar γ β R μ x + y)) ∂μ =
      ENNReal.ofReal ((β * R)⁻¹) * ENNReal.ofReal (-ex7_caW γ β R μ x) := fun x => by
    have hi := (ex7_caW_integrable (γ := γ) (β := β) (R := R) hμ (ex7_caraSbar γ β R μ x)).neg
    rw [← ofReal_integral_eq_lintegral_ofReal
        (f := fun y => -ex7_caW γ β R μ (R * ex7_caraSbar γ β R μ x + y)) hi
        (Eventually.of_forall fun y => hWn _),
      ← ENNReal.ofReal_mul (inv_nonneg.2 (mul_pos hβ hR0).le)]
    congr 1
    have h3 : β * ∫ y, ex7_caW γ β R μ (R * ex7_caraSbar γ β R μ x + y) ∂μ =
        ex7_caW γ β R μ x / R := (ex_7_7_bellman hγ hβ hR hμ x).2.2.1
    rw [integral_neg]
    change -∫ y, ex7_caW γ β R μ (R * ex7_caraSbar γ β R μ x + y) ∂μ = _
    have hβ0 : β ≠ 0 := hβ.ne'
    have hR0' : R ≠ 0 := hR0.ne'
    have : ∫ y, ex7_caW γ β R μ (R * ex7_caraSbar γ β R μ x + y) ∂μ =
        ex7_caW γ β R μ x / R / β := by
      calc ∫ y, ex7_caW γ β R μ (R * ex7_caraSbar γ β R μ x + y) ∂μ =
          (β * ∫ y, ex7_caW γ β R μ (R * ex7_caraSbar γ β R μ x + y) ∂μ) / β := by field_simp
        _ = _ := by rw [h3]
    rw [this]
    field_simp
  induction n with
  | zero =>
    rw [mu_zero, lintegral_dirac' _ (f := fun h => ENNReal.ofReal (-ex7_caW γ β R μ
      (lastState x₀ h))) (hW.comp (measurable_lastState x₀ 0))]
    simp [lastState]
  | succ n ih =>
    rw [ex7_ca_lintegral_succ γ β R x₀ ((ex7_caraSbar_measurable γ β R).comp
      (measurable_lastState x₀ n)) hW]
    simp only [po_genPlan, hstep]
    rw [lintegral_const_mul _ (f := fun h => ENNReal.ofReal (-ex7_caW γ β R μ (lastState x₀ h)))
      (hW.comp (measurable_lastState x₀ n)), ih,
      ← ENNReal.ofReal_mul (inv_nonneg.2 (mul_pos hβ hR0).le), pow_succ]
    ring_nf

/-- Along the limit policy: `V̄(x_n)` is integrable, `E V̄(x_n) = V̄(x₀)(βR)^{−n}`, and the
rewards `−e^{−γ(x_t − s̄(x_t))} = (1 − 1/R)V̄(x_t)` are integrable. -/
theorem ex7_ca_plan_int [IsProbabilityMeasure μ] {γ β R ymin ymax : ℝ} (hγ : 0 < γ)
    (hβ : 0 < β) (hR : 1 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) (x₀ : ℝ) (n : ℕ) :
    Integrable (fun h => ex7_caW γ β R μ (lastState x₀ h))
        (mu (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ => ex7_caraSbar γ β R μ) x₀) n) ∧
      ∫ h, ex7_caW γ β R μ (lastState x₀ h)
        ∂mu (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ => ex7_caraSbar γ β R μ) x₀) n =
        ex7_caW γ β R μ x₀ * ((β * R)⁻¹) ^ n ∧
      Integrable (rew (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ => ex7_caraSbar γ β R μ) x₀) n)
        (mu (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ => ex7_caraSbar γ β R μ) x₀) n) := by
  have hR0 : 0 < R := by linarith
  have hWn : ∀ x, 0 ≤ -ex7_caW γ β R μ x := fun x => by
    simp only [ex7_caW, neg_neg]; exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hc : 0 ≤ -ex7_caW γ β R μ x₀ * ((β * R)⁻¹) ^ n :=
    mul_nonneg (hWn x₀) (pow_nonneg (inv_nonneg.2 (mul_pos hβ hR0).le) _)
  have h := ex7_integrable_of_lintegral (μ := mu (ex7_caMDP γ β R μ) x₀
    (po_genPlan (fun _ => ex7_caraSbar γ β R μ) x₀) n)
    (f := fun h => -ex7_caW γ β R μ (lastState x₀ h))
    ((ex7_caW_measurable γ β R).neg.comp (measurable_lastState x₀ n))
    (fun h => hWn _) hc (ex7_ca_moment hγ hβ hR hμ x₀ n).le
  have hI : Integrable (fun h => ex7_caW γ β R μ (lastState x₀ h))
      (mu (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ => ex7_caraSbar γ β R μ) x₀) n) := by
    refine h.1.neg.congr (Eventually.of_forall fun _ => ?_)
    simp
  refine ⟨hI, ?_, ?_⟩
  · have := h.2.2 (ex7_ca_moment hγ hβ hR hμ x₀ n)
    rw [integral_neg] at this
    linarith
  · refine (hI.const_mul (1 - R⁻¹)).congr (Eventually.of_forall fun h => ?_)
    have : -Real.exp (-(γ * (lastState x₀ h - ex7_caraSbar γ β R μ (lastState x₀ h)))) =
        (1 - R⁻¹) * ex7_caW γ β R μ (lastState x₀ h) :=
      (ex_7_7_bellman hγ hβ hR hμ (lastState x₀ h)).2.2.2
    change _ = -Real.exp (-(γ * (lastState x₀ h - ex7_caraSbar γ β R μ (lastState x₀ h))))
    rw [this]

/-! ### Exercise 7.7 -/

/-- **Exercise 7.7, corrected** (Miao, p. 229), `R > 1`: the limit policy `s̄` (consumption
`c̄(x) = (1 − 1/R)x − L̄/(γR)`) generates a plan in `Π̂`, with integrable rewards, attaining
`V̄(x₀) = −Āe^{−ᾱx₀}`; every feasible plan in `Π̂` (i.e. satisfying the transversality condition
(7.4)) with integrable rewards has `J ≤ V̄(x₀)`. -/
theorem ex_7_7 [IsProbabilityMeasure μ] {γ β R ymin ymax : ℝ} (hγ : 0 < γ) (hβ : 0 < β)
    (hR : 1 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) (x₀ : ℝ) :
    po_genPlan (fun _ => ex7_caraSbar γ β R μ) x₀ ∈
        ih_PiHat (ex7_caMDP γ β R μ) (ex7_caW γ β R μ) x₀ ∧
      J (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ => ex7_caraSbar γ β R μ) x₀) =
        ex7_caW γ β R μ x₀ ∧
      (∀ σ ∈ ih_PiHat (ex7_caMDP γ β R μ) (ex7_caW γ β R μ) x₀,
        (∀ t, Integrable (rew (ex7_caMDP γ β R μ) x₀ σ t) (mu (ex7_caMDP γ β R μ) x₀ σ t)) →
        J (ex7_caMDP γ β R μ) x₀ σ ≤ ex7_caW γ β R μ x₀) := by
  have hR0 : 0 < R := by linarith
  obtain ⟨hB, hint, hg⟩ := ex7_ca_bellman hγ hβ hR hμ
  have hP := ex7_ca_markov (μ := μ) γ β R
  have hst := ex7_ca_stationary (μ := μ) γ β R
  set σ' := po_genPlan (fun _ => ex7_caraSbar γ β R μ) x₀
  have hσ' := ih_genPlan_feasible hg x₀
  have hints := ex7_ca_plan_int hγ hβ hR hμ x₀
  have h74 : Tendsto (fun n => (ex7_caMDP γ β R μ).β ^ n *
      ∫ h, ex7_caW γ β R μ (lastState x₀ h) ∂mu (ex7_caMDP γ β R μ) x₀ σ' n) atTop (𝓝 0) := by
    have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hR0.le)
      (inv_lt_one_of_one_lt₀ hR)).const_mul (ex7_caW γ β R μ x₀)
    rw [mul_zero] at hlim
    refine hlim.congr fun n => ?_
    change _ = β ^ n * _
    have : β ^ n ≠ 0 := pow_ne_zero _ hβ.ne'
    rw [(hints n).2.1, mul_inv, mul_pow, inv_pow β n]
    field_simp
  have hmem : σ' ∈ ih_PiHat (ex7_caMDP γ β R μ) (ex7_caW γ β R μ) x₀ :=
    ⟨hσ', fun n => (hints n).1, h74⟩
  have hJ := (ex7_verif_eq_plan hP hst hσ' (fun t => (hints t).2.2)
    (ih_slack_genPlan hst hg hint x₀) (fun n => (hints n).1) h74).2
  have hle : ∀ s, ∀ a ∈ (ex7_caMDP γ β R μ).Γ s,
      Integrable (ex7_caW γ β R μ) ((ex7_caMDP γ β R μ).P 0 (s, a)) ∧
      (ex7_caMDP γ β R μ).u 0 (s, a) + (ex7_caMDP γ β R μ).β *
        ∫ s', ex7_caW γ β R μ s' ∂(ex7_caMDP γ β R μ).P 0 (s, a) ≤ ex7_caW γ β R μ s :=
    fun s a ha => ⟨hint s a ha, ih_bellman_le hB ha (hint s a ha)⟩
  have hhat : ∀ σ ∈ ih_PiHat (ex7_caMDP γ β R μ) (ex7_caW γ β R μ) x₀,
      (∀ t, Integrable (rew (ex7_caMDP γ β R μ) x₀ σ t) (mu (ex7_caMDP γ β R μ) x₀ σ t)) →
      J (ex7_caMDP γ β R μ) x₀ σ ≤ ex7_caW γ β R μ x₀ := fun σ hσ hI =>
    ex7_verif_le_plan hP hst hβ.le hle hσ.1 hI
      (ex7_J_spec_nonpos hβ.le (ex7_ca_u_nonpos γ β R) x₀ σ).1 hσ.2.1 hσ.2.2
  exact ⟨hmem, hJ, hhat⟩

/-! ### The book's claim fails: Ponzi schemes -/

/-- **The Ponzi plan** (consume `c` every period, saving `s_t = x_t − c`, rolling the debt over):
it is feasible (there is no borrowing constraint), and
`J = Σ βᵗ(−e^{−γc}) = −e^{−γc}/(1 − β)`. -/
theorem ex7_ca_ponzi_J [IsProbabilityMeasure μ] {γ β R : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (c x₀ : ℝ) :
    po_genPlan (fun _ x => x - c) x₀ ∈ feasiblePlans (ex7_caMDP γ β R μ) ⊤ x₀ ∧
      J (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ x => x - c) x₀) =
        ((-Real.exp (-(γ * c)) / (1 - β) : ℝ) : EReal) := by
  have hmeas : ∀ j, Measurable (po_genPlan (fun _ x => x - c) x₀ j : (Fin j → ℝ) → ℝ) :=
    fun j => (measurable_id.sub_const c).comp (measurable_lastState x₀ j)
  refine ⟨⟨fun j _ => hmeas j, fun _ _ _ => Set.mem_univ _⟩, ?_⟩
  have hexp : ∀ t, expRew (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ x => x - c) x₀) t =
      -Real.exp (-(γ * c)) := fun t => by
    have : IsProbabilityMeasure (mu (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ x => x - c) x₀) t) :=
      isProbabilityMeasure_mu (ex7_caMDP γ β R μ) (ex7_ca_markov γ β R) x₀ fun j _ => hmeas j
    have e : rew (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ x => x - c) x₀) t =
        fun _ => -Real.exp (-(γ * c)) := funext fun h => by
      change -Real.exp (-(γ * (lastState x₀ h - (lastState x₀ h - c)))) = _
      ring_nf
    rw [expRew, e, integral_const, probReal_univ, one_smul]
  have hS : ∀ n, partialSum (ex7_caMDP γ β R μ) x₀ (po_genPlan (fun _ x => x - c) x₀) n =
      -Real.exp (-(γ * c)) * ∑ t ∈ Finset.range (n + 1), β ^ t := fun n => by
    simp only [partialSum, hexp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by change β ^ t * _ = _; ring
  have hgeo := ((hasSum_geometric_of_lt_one hβ0 hβ1).tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  have hT : Tendsto (fun n => (partialSum (ex7_caMDP γ β R μ) x₀
      (po_genPlan (fun _ x => x - c) x₀) n : EReal)) atTop
      (𝓝 ((-Real.exp (-(γ * c)) / (1 - β) : ℝ) : EReal)) := by
    have := hgeo.const_mul (-Real.exp (-(γ * c)))
    rw [← div_eq_mul_inv] at this
    exact EReal.tendsto_coe.2 (this.congr fun n => (hS n).symm)
  rw [J, hT.limUnder_eq]

/-- **Exercise 7.7: the limit policy is not optimal over all feasible plans** (counterexample;
Miao, p. 229). For `R > 1`, the value of the MDP is `V ≡ 0` (`J ≤ 0` for every plan since
`u < 0`, and the Ponzi plans of `ex7_ca_ponzi_J` have `J → 0` as `c → ∞`), which is strictly
above `V̄(x) = −Āe^{−ᾱx} = J(limit plan)`; so the limit policy is not an optimal plan, the
supremum is not attained, and condition (b) of Corollary 7.1.1 fails. -/
theorem ex_7_7_ponzi [IsProbabilityMeasure μ] {γ β R ymin ymax : ℝ} (hγ : 0 < γ) (hβ : 0 < β)
    (hβ1 : β < 1) (hR : 1 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) (x : ℝ) :
    V (ex7_caMDP γ β R μ) x = 0 ∧ (ex7_caW γ β R μ x : EReal) < V (ex7_caMDP γ β R μ) x ∧
      ¬ IsOptimalPlan (ex7_caMDP γ β R μ) x (po_genPlan (fun _ => ex7_caraSbar γ β R μ) x) := by
  have hV0 : V (ex7_caMDP γ β R μ) x = 0 := by
    refine le_antisymm (iSup₂_le fun σ _ =>
      (ex7_J_spec_nonpos hβ.le (ex7_ca_u_nonpos γ β R) x σ).2) ?_
    have hlim : Tendsto (fun n : ℕ => ((-Real.exp (-(γ * n)) / (1 - β) : ℝ) : EReal)) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => -(γ * n)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hγ tendsto_natCast_atTop_atTop)
      have h2 := ((Real.tendsto_exp_atBot.comp h1).neg).div_const (1 - β)
      simp only [neg_zero, zero_div] at h2
      rw [← EReal.coe_zero]
      exact EReal.tendsto_coe.2 h2
    refine le_of_tendsto' hlim fun n => ?_
    obtain ⟨hf, hJ⟩ := ex7_ca_ponzi_J (μ := μ) (γ := γ) (R := R) hβ.le hβ1 (n : ℝ) x
    rw [← hJ]
    exact le_iSup₂ (f := fun σ (_ : σ ∈ feasiblePlans (ex7_caMDP γ β R μ) ⊤ x) =>
      J (ex7_caMDP γ β R μ) x σ) _ hf
  have hW : ex7_caW γ β R μ x < 0 := by
    simp only [ex7_caW, neg_neg_iff_pos]
    exact mul_pos (Real.exp_pos _) (Real.exp_pos _)
  refine ⟨hV0, by rw [hV0]; exact EReal.coe_lt_coe_iff.2 hW, fun hopt => ?_⟩
  have hJ := (ex_7_7 hγ hβ hR hμ x).2.1
  have := hopt.2
  rw [hV0, hJ] at this
  exact absurd (EReal.coe_eq_coe_iff.1 this.symm ▸ hW) (lt_irrefl _)

end Miao.InfiniteHorizonDP

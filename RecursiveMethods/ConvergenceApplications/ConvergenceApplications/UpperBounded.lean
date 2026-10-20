/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.GrowthPolicy

/-!
# Returns bounded above

The industry-investment and inventory problems of SLP §§10.4–10.5 have returns that are bounded
above but not below (adjustment and holding costs grow without bound), so Assumption 9.7 fails.
What they do have is a choice with nonnegative return in every state. Under these hypotheses
(`UpperDP`), truncating `F` below at `−K` (`truncModel`) gives a model satisfying the hypotheses
of §9.2, and for `K > βA/(1 − β)` the truncation never binds at an optimum. Hence
(`upper_fixed`):

* the fixed point `v` of the truncated operator satisfies `0 ≤ v ≤ A/(1 − β)` and solves the
  functional equation of the original problem, the maximum being attained;
* it is the only bounded continuous solution, because the original operator is itself a
  `β`-contraction wherever the maxima exist.

`trunc_bellman_argmax` is the analogue of `exists_bellman_argmax` for the original returns, on
functions with values in `[0, A/(1 − β)]`; it lets monotonicity and concavity be proved through
the truncated contraction.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- §9.2's hypotheses with Assumption 9.7 weakened: returns are bounded above by `A ≥ 0`, and a
nonnegative return is available in every state. -/
structure UpperDP (M : Model X Y Z) (A : ℝ) : Prop where
  nonempty : ∀ s, (M.Γ s).Nonempty
  compact : ∀ s, IsCompact (M.Γ s)
  lhc : ∀ s, IsLHC M.Γ s
  uhc : ∀ s, IsUHC M.Γ s
  contF : ContinuousOn M.F (graphA M)
  A_nonneg : 0 ≤ A
  bddAbove : ∀ p ∈ graphA M, M.F p ≤ A
  safe : ∀ s, ∃ y ∈ M.Γ s, 0 ≤ M.F (s.1, y, s.2)
  β_pos : 0 < M.β
  β_lt : M.β < 1
  contφ : ContinuousOn (fun q : (X × Y) × Z => M.φ (q.1.1, q.1.2, q.2)) (domD M ×ˢ univ)
  contExp : ContExp M

/-- The model with returns truncated below at `−K`. -/
abbrev truncModel (M : Model X Y Z) (K : ℝ) : Model X Y Z :=
  ⟨M.Q, M.Γ, M.φ, fun p => max (M.F p) (-K), M.β⟩

variable {M : Model X Y Z} {A : ℝ}

/-- The truncated model satisfies the hypotheses of §9.2. -/
theorem truncModel_boundedDP (h : UpperDP M A) {K : ℝ} (hK : 0 ≤ K) :
    BoundedDP (truncModel M K) :=
  ⟨h.nonempty, h.compact, h.lhc, h.uhc,
    continuous_max.comp_continuousOn (h.contF.prodMk continuousOn_const),
    ⟨max A K, fun p hp => abs_le.2 ⟨by
      have := le_max_right (M.F p) (-K)
      have := le_max_right A K
      change -max A K ≤ max (M.F p) (-K)
      linarith, max_le ((h.bddAbove p hp).trans (le_max_left _ _))
        (by linarith [le_max_right A K])⟩⟩,
    h.β_pos, h.β_lt, h.contφ, h.contExp⟩

/-- The truncation level used: `K = A/(1 − β) + 1`. -/
noncomputable def truncK (A β : ℝ) : ℝ := A / (1 - β) + 1

theorem truncK_pos (h : UpperDP M A) : 0 < truncK A M.β := by
  have : 0 < 1 - M.β := by linarith [h.β_lt]
  have := div_nonneg h.A_nonneg this.le
  unfold truncK; linarith

/-- The truncated operator `T̃`. -/
noncomputable abbrev truncT [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] (h : UpperDP M A) :
    (X × Z →ᵇ ℝ) → (X × Z →ᵇ ℝ) :=
  bellman (truncModel M (truncK A M.β)) (truncModel_boundedDP h (truncK_pos h).le)

/-- On functions with values in `[0, A/(1 − β)]`, the truncated operator equals the original one:
it attains its maximum at a `y` where the truncation does not bind, and dominates `rhs` for the
original returns. -/
theorem trunc_bellman_argmax [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] (h : UpperDP M A)
    {f : X × Z →ᵇ ℝ} (hf : ∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - M.β)) (s : X × Z) :
    ∃ y ∈ M.Γ s, truncT h f s = rhs M f s y ∧ ∀ y' ∈ M.Γ s, rhs M f s y' ≤ truncT h f s := by
  set K := truncK A M.β
  set M' := truncModel M K
  have hb := truncModel_boundedDP h (truncK_pos h).le
  obtain ⟨y, hy, hval, hmax⟩ := exists_bellman_argmax M' hb f s
  have hEf : ∀ y', y' ∈ M.Γ s → 0 ≤ expV M f s y' ∧ expV M f s y' ≤ A / (1 - M.β) := by
    intro y' hy'
    have hint := integrable_integrand M' hb f hy' s.2
    refine ⟨integral_nonneg fun z' => (hf _).1, ?_⟩
    have := integral_mono hint (integrable_const (A / (1 - M.β))) fun z' => (hf _).2
    simpa [expV] using this
  have hexpV : ∀ y', expV M' f s y' = expV M f s y' := fun _ => rfl
  -- the value is nonnegative, using the safe choice
  obtain ⟨y₀, hy₀, hF₀⟩ := h.safe s
  have h0 : 0 ≤ bellman M' hb f s := by
    refine le_trans ?_ (hmax y₀ hy₀)
    simp only [rhs, hexpV]
    have := (hEf y₀ hy₀).1
    have := mul_nonneg h.β_pos.le this
    have := le_max_left (M.F (s.1, y₀, s.2)) (-K)
    change 0 ≤ max (M.F (s.1, y₀, s.2)) (-K) + M.β * expV M f s y₀
    linarith
  -- so the truncation does not bind at `y`
  have hβR : M.β * (A / (1 - M.β)) < K := by
    have h1 : 0 < 1 - M.β := by linarith [h.β_lt]
    have : M.β * (A / (1 - M.β)) ≤ A / (1 - M.β) :=
      mul_le_of_le_one_left (div_nonneg h.A_nonneg h1.le) h.β_lt.le
    unfold K truncK; linarith
  have hbind : -K < M.F (s.1, y, s.2) := by
    simp only [rhs, hexpV] at hval
    have hE := (hEf y hy).2
    have := mul_le_mul_of_nonneg_left hE h.β_pos.le
    by_contra hle
    have hmx : max (M.F (s.1, y, s.2)) (-K) = -K := max_eq_right (not_lt.1 hle)
    change bellman M' hb f s = max (M.F (s.1, y, s.2)) (-K) + M.β * expV M f s y at hval
    rw [hmx] at hval
    linarith
  refine ⟨y, hy, ?_, fun y' hy' => ?_⟩
  · rw [hval]
    simp only [rhs, hexpV]
    change max (M.F (s.1, y, s.2)) (-K) + _ = _
    rw [max_eq_left hbind.le]
  · refine le_trans ?_ (hmax y' hy')
    simp only [rhs, hexpV]
    change _ ≤ max (M.F (s.1, y', s.2)) (-K) + _
    linarith [le_max_left (M.F (s.1, y', s.2)) (-K)]

/-- `T̃` maps functions with values in `[0, A/(1 − β)]` into themselves. -/
theorem truncT_mapsTo [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] (h : UpperDP M A) :
    MapsTo (truncT h) {f | ∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - M.β)}
      {f | ∀ s, 0 ≤ f s ∧ f s ≤ A / (1 - M.β)} := by
  intro f hf s
  obtain ⟨y, hy, hval, hmax⟩ := trunc_bellman_argmax h hf s
  obtain ⟨y₀, hy₀, hF₀⟩ := h.safe s
  have hb := truncModel_boundedDP h (truncK_pos h).le
  have hint : ∀ y', y' ∈ M.Γ s → Integrable (fun z' => f (M.φ (s.1, y', z'), z')) (M.Q s.2) :=
    fun y' hy' => integrable_integrand (truncModel M _) hb f hy' s.2
  have hE0 : ∀ y', y' ∈ M.Γ s → 0 ≤ expV M f s y' := fun y' _ =>
    integral_nonneg fun z' => (hf _).1
  have hER : ∀ y', y' ∈ M.Γ s → expV M f s y' ≤ A / (1 - M.β) := fun y' hy' => by
    have := integral_mono (hint y' hy') (integrable_const (A / (1 - M.β))) fun z' => (hf _).2
    simpa [expV] using this
  have h1 : 0 < 1 - M.β := by linarith [h.β_lt]
  refine ⟨le_trans ?_ (hmax y₀ hy₀), ?_⟩
  · simp only [rhs]
    have := mul_nonneg h.β_pos.le (hE0 y₀ hy₀)
    linarith
  · rw [hval]
    simp only [rhs]
    have hA := h.bddAbove (s.1, y, s.2) hy
    have := mul_le_mul_of_nonneg_left (hER y hy) h.β_pos.le
    have e : A / (1 - M.β) = A + M.β * (A / (1 - M.β)) := by field_simp; ring
    linarith

omit [MeasurableSpace X] [MeasurableSpace Z] in
theorem isClosed_bounds (R : ℝ) :
    IsClosed {f : X × Z →ᵇ ℝ | ∀ s, 0 ≤ f s ∧ f s ≤ R} := by
  have : {f : X × Z →ᵇ ℝ | ∀ s, 0 ≤ f s ∧ f s ≤ R} =
      ⋂ s, ({f : X × Z →ᵇ ℝ | 0 ≤ f s} ∩ {f | f s ≤ R}) := by ext; simp
  rw [this]
  exact isClosed_iInter fun s => (isClosed_le continuous_const (continuous_eval_const s)).inter
    (isClosed_le (continuous_eval_const s) continuous_const)

/-- **Returns bounded above.** The fixed point `v` of the truncated operator has values in
`[0, A/(1 − β)]`, attains the maximum in the original functional equation at every state, and is
the only bounded continuous solution of that equation. -/
theorem upper_fixed [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] (h : UpperDP M A) :
    ∃ v : X × Z →ᵇ ℝ, truncT h v = v ∧ (∀ s, 0 ≤ v s ∧ v s ≤ A / (1 - M.β)) ∧
      (∀ s, ∃ y ∈ M.Γ s, v s = rhs M v s y) ∧ (∀ s, ∀ y ∈ M.Γ s, rhs M v s y ≤ v s) ∧
      SolvesFE M v ∧ ∀ w : X × Z →ᵇ ℝ, SolvesFE M w → w = v := by
  set M' := truncModel M (truncK A M.β)
  have hb := truncModel_boundedDP h (truncK_pos h).le
  obtain ⟨v, hv, -, -, -⟩ := ex_9_7b M' hb
  have hvR := (corollary_1 (bellman_contraction M' hb) hv
    ⟨0, fun _ => ⟨le_rfl, div_nonneg h.A_nonneg (by linarith [h.β_lt])⟩⟩ (isClosed_bounds _)
    (truncT_mapsTo h) (truncT_mapsTo h)).1
  have hatt : ∀ s, ∃ y ∈ M.Γ s, v s = rhs M v s y := fun s => by
    obtain ⟨y, hy, hval, -⟩ := trunc_bellman_argmax h hvR s
    exact ⟨y, hy, (congrFun (congrArg DFunLike.coe hv) s).symm.trans hval⟩
  have hle : ∀ s, ∀ y ∈ M.Γ s, rhs M v s y ≤ v s := fun s y hy => by
    obtain ⟨-, -, -, hmax⟩ := trunc_bellman_argmax h hvR s
    exact (hmax y hy).trans_eq (congrFun (congrArg DFunLike.coe hv) s)
  have hFE : SolvesFE M v := fun s => by
    obtain ⟨y, hy, hval⟩ := hatt s
    refine IsGreatest.isLUB ⟨⟨y, hy, hval.symm⟩, ?_⟩
    rintro _ ⟨y', hy', rfl⟩
    exact hle s y' hy'
  refine ⟨v, hv, hvR, hatt, hle, hFE, fun w hw => ?_⟩
  -- the original operator is a `β`-contraction wherever the maxima exist
  have hdiff : ∀ s, ∀ y ∈ M.Γ s, |expV M w s y - expV M v s y| ≤ ‖w - v‖ := fun s y hy => by
    have hiw := integrable_integrand M' hb w hy s.2
    have hiv := integrable_integrand M' hb v hy s.2
    rw [expV, expV, ← integral_sub hiw hiv]
    have := norm_integral_le_of_norm_le_const (μ := M.Q s.2) (C := ‖w - v‖)
      (f := fun z' => w (M.φ (s.1, y, z'), z') - v (M.φ (s.1, y, z'), z'))
      (Eventually.of_forall fun z' => by
        rw [← BoundedContinuousFunction.sub_apply]; exact (w - v).norm_coe_le_norm _)
    simpa [measureReal_def, Real.norm_eq_abs] using this
  have hβ0 := h.β_pos
  have hpt : ∀ s, |w s - v s| ≤ M.β * ‖w - v‖ := fun s => by
    rw [abs_le]
    obtain ⟨y, hy, hval⟩ := hatt s
    constructor
    · -- `v(s) = rhs_v(y) ≤ rhs_w(y) + β‖w − v‖ ≤ w(s) + β‖w − v‖`
      have h1 : rhs M w s y ≤ w s := (hw s).1 ⟨y, hy, rfl⟩
      have h2 := (abs_le.1 (hdiff s y hy)).1
      simp only [rhs] at hval h1
      nlinarith [mul_le_mul_of_nonneg_left (show -‖w - v‖ ≤ expV M w s y - expV M v s y from h2)
        hβ0.le]
    · -- `w(s) = sup rhs_w ≤ sup rhs_v + β‖w − v‖ ≤ v(s) + β‖w − v‖`
      refine sub_le_iff_le_add'.2 ((hw s).2 ?_)
      rintro _ ⟨y', hy', rfl⟩
      have h2 := (abs_le.1 (hdiff s y' hy')).2
      have h3 := hle s y' hy'
      simp only [rhs] at h3 ⊢
      nlinarith [mul_le_mul_of_nonneg_left h2 hβ0.le]
  have hnorm : ‖w - v‖ ≤ M.β * ‖w - v‖ :=
    (norm_le (mul_nonneg hβ0.le (norm_nonneg _))).2 fun s => by
      rw [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs]; exact hpt s
  have : ‖w - v‖ = 0 := by
    have := norm_nonneg (w - v)
    nlinarith [h.β_lt]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end StokeyLucasPrescott.ConvergenceApplications

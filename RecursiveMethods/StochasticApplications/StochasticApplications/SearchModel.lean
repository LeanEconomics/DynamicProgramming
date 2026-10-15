/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.ManyGoods

/-!
# A model of search unemployment

SLP §10.7, pp. 304–307, Exercise 10.7a–c. A worker with wage offer `w ∈ W = [0, w̄]` either works
(`y = 1`), earning `U(w)` and keeping the job next period with probability `1 − θ`, or searches
(`y = 0`), earning nothing and drawing a new offer from `μ`. The exogenous shocks are
`(d, z) ∈ {0, 1} × W`, i.i.d. with law `(θ δ₀ + (1 − θ) δ₁) ⊗ μ`: `d = 0` means the job is lost.
The book takes `μ` with a density `f`; any probability measure on `W` will do here.

* **Exercise 10.7a** (`searchφ`, `ex_10_7a`): the law of motion is
  `w_{t+1} = w_t` if `y_t = 1` and `d_{t+1} = 1`, `0` if `y_t = 1` and `d_{t+1} = 0`, and
  `z_{t+1}` if `y_t = 0`.
* `search_boundedDP`: the hypotheses of §9.2 hold, so Chapter 9 applies.
* **Exercise 10.7b–c** (`ex_10_7c`): the fixed point `v(w, d, z)` does not depend on `(d, z)`.
  Its section `v(w)` is the unique continuous solution of
  `v(w) = max {U(w) + β[(1 − θ)v(w) + θv(0)], β ∫ v dμ}` (1), it is nondecreasing, and it is the
  supremum function of the sequence problem, which therefore depends only on `w₀`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- The two-point set `{0, 1}` (as a subset of `ℕ`, which carries a metric). -/
abbrev Two : Type := Set.Iic (1 : ℕ)

/-- `0 ∈ {0, 1}`. -/
def two0 : Two := ⟨0, Set.mem_Iic.2 zero_le_one⟩

/-- `1 ∈ {0, 1}`. -/
def two1 : Two := ⟨1, Set.mem_Iic.2 le_rfl⟩

theorem two_cases (y : Two) : y = two0 ∨ y = two1 := by
  obtain ⟨n, hn⟩ := y
  have : n ≤ 1 := hn
  interval_cases n
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr (Subtype.ext rfl)

theorem two0_ne_two1 : two0 ≠ two1 := by
  intro h
  have := congrArg Subtype.val h
  simp [two0, two1] at this

/-- The law of the job-loss shock: `d = 0` (job lost) with probability `θ`. -/
noncomputable def lossMeasure (θ : ℝ) : Measure Two :=
  ENNReal.ofReal θ • Measure.dirac two0 + ENNReal.ofReal (1 - θ) • Measure.dirac two1

theorem isProbabilityMeasure_lossMeasure {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    IsProbabilityMeasure (lossMeasure θ) :=
  ⟨by simp [lossMeasure, ← ENNReal.ofReal_add h0 (by linarith : (0 : ℝ) ≤ 1 - θ)]⟩

theorem integral_lossMeasure {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (g : Two → ℝ) :
    ∫ d, g d ∂lossMeasure θ = θ * g two0 + (1 - θ) * g two1 := by
  have : IsFiniteMeasure (ENNReal.ofReal θ • Measure.dirac two0) := ⟨by simp⟩
  have : IsFiniteMeasure (ENNReal.ofReal (1 - θ) • Measure.dirac two1) := ⟨by simp⟩
  rw [lossMeasure, integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- Integration against `(θ δ₀ + (1 − θ) δ₁) ⊗ μ`. -/
theorem integral_loss_prod {W : Type*} [MeasurableSpace W] {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (μ : Measure W) [IsProbabilityMeasure μ] {g : Two × W → ℝ}
    (hg : Integrable g ((lossMeasure θ).prod μ)) :
    ∫ p, g p ∂(lossMeasure θ).prod μ =
      θ * ∫ z, g (two0, z) ∂μ + (1 - θ) * ∫ z, g (two1, z) ∂μ := by
  have : IsProbabilityMeasure (lossMeasure θ) := isProbabilityMeasure_lossMeasure h0 h1
  rw [integral_prod g hg, integral_lossMeasure h0 h1]

/-- The hypotheses of SLP §10.7 used here: `0 < β < 1`, `0 ≤ θ ≤ 1`, and `U` continuous and
strictly increasing on `W = [0, w̄]` with `U(0) = 0`. (Concavity and differentiability of `U`
are not needed.) -/
structure SearchHyp (U : ℝ → ℝ) (θ β wbar : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  θ_nonneg : 0 ≤ θ
  θ_le : θ ≤ 1
  wbar_pos : 0 < wbar
  U_cont : ContinuousOn U (Icc 0 wbar)
  U_mono : StrictMonoOn U (Icc 0 wbar)
  U_zero : U 0 = 0

variable {U : ℝ → ℝ} {θ β wbar : ℝ}

/-- The zero wage. -/
def w0 (hw : 0 ≤ wbar) : Icc (0 : ℝ) wbar := ⟨0, le_rfl, hw⟩

/-- **Exercise 10.7a.** The law of motion `w_{t+1} = φ(w_t, y_t, d_{t+1}, z_{t+1})`. -/
def searchφ (hw : 0 ≤ wbar)
    (p : Icc (0 : ℝ) wbar × Two × (Two × Icc (0 : ℝ) wbar)) : Icc (0 : ℝ) wbar :=
  if p.2.1 = two1 then (if p.2.2.1 = two1 then p.1 else w0 hw) else p.2.2.2

/-- The return: `U(w)` when working, `0` when searching. -/
def searchF (U : ℝ → ℝ) (p : Icc (0 : ℝ) wbar × Two × (Two × Icc (0 : ℝ) wbar)) : ℝ :=
  if p.2.1 = two1 then U p.1.1 else 0

/-- The search model in the second formulation of Chapter 9: `x = w`, `y ∈ {0, 1}`, shocks
`(d, z)` i.i.d. -/
noncomputable abbrev searchModel (hw : 0 ≤ wbar) (U : ℝ → ℝ) (θ β : ℝ)
    (μ : Measure (Icc (0 : ℝ) wbar)) :
    Model (Icc (0 : ℝ) wbar) Two (Two × Icc (0 : ℝ) wbar) :=
  ⟨Kernel.const _ ((lossMeasure θ).prod μ), fun _ => univ, searchφ hw, searchF U, β⟩

/-- **Exercise 10.7a.** -/
theorem ex_10_7a (hw : 0 ≤ wbar) (w z : Icc (0 : ℝ) wbar) :
    searchφ hw (w, two1, (two1, z)) = w ∧ searchφ hw (w, two1, (two0, z)) = w0 hw ∧
      ∀ d, searchφ hw (w, two0, (d, z)) = z := by
  refine ⟨by simp [searchφ], by simp [searchφ, two0_ne_two1], fun d => by
    simp [searchφ, two0_ne_two1]⟩

theorem continuous_searchF (h : SearchHyp U θ β wbar) :
    Continuous (searchF U : Icc (0 : ℝ) wbar × Two × (Two × Icc (0 : ℝ) wbar) → ℝ) := by
  have hU : Continuous fun w : Icc (0 : ℝ) wbar => U w.1 :=
    h.U_cont.comp_continuous continuous_subtype_val fun w => w.2
  have hG : Continuous fun q : Two × (Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar)) =>
      if q.1 = two1 then U q.2.1.1 else 0 := by
    refine continuous_prod_of_discrete_left.2 fun y => ?_
    dsimp only
    split_ifs
    · exact hU.comp continuous_fst
    · exact continuous_const
  exact hG.comp (continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))

theorem continuous_searchφ (hw : 0 ≤ wbar) :
    Continuous fun q : (Icc (0 : ℝ) wbar × Two) × (Two × Icc (0 : ℝ) wbar) =>
      searchφ hw (q.1.1, q.1.2, q.2) := by
  have hH : Continuous fun q : (Two × Two) × (Icc (0 : ℝ) wbar × Icc (0 : ℝ) wbar) =>
      if q.1.1 = two1 then (if q.1.2 = two1 then q.2.1 else w0 hw) else q.2.2 := by
    refine continuous_prod_of_discrete_left.2 fun yd => ?_
    dsimp only
    split_ifs
    · exact continuous_fst
    · exact continuous_const
    · exact continuous_snd
  exact hH.comp ((continuous_fst.snd.prodMk continuous_snd.fst).prodMk
    (continuous_fst.fst.prodMk continuous_snd.snd))

theorem continuous_searchφ' (hw : 0 ≤ wbar) : Continuous (searchφ hw) :=
  (continuous_searchφ hw).comp ((continuous_fst.prodMk continuous_snd.fst).prodMk
    continuous_snd.snd)

/-- The hypotheses of §9.2 hold for the search model. -/
theorem search_boundedDP (h : SearchHyp U θ β wbar) (μ : Measure (Icc (0 : ℝ) wbar))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure (lossMeasure θ)] :
    BoundedDP (searchModel h.wbar_pos.le U θ β μ) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_searchF h (wbar := wbar)).continuousOn
  have hφ := continuous_searchφ h.wbar_pos.le
  refine ⟨fun _ => univ_nonempty, fun _ => isCompact_univ,
    fun _ => ⟨univ_nonempty, fun y _ _ _ => ⟨0, fun _ => y, fun _ _ => mem_univ _,
      tendsto_const_nhds⟩⟩, fun _ => ⟨univ_nonempty, fun xs _ ys _ => ?_⟩,
    (continuous_searchF h).continuousOn, ⟨B, fun p _ => by
      simpa [Real.norm_eq_abs] using hB p (mem_univ _)⟩, h.β_pos, h.β_lt, hφ.continuousOn,
    contExp_of_preservesBC _ hφ.continuousOn
      (lemma_9_5_compact _ (isFeller_const _))⟩
  obtain ⟨y, -, φ, hφ', hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
  exact ⟨y, mem_univ _, φ, hφ', hlim⟩

variable (h : SearchHyp U θ β wbar) (μ : Measure (Icc (0 : ℝ) wbar)) [IsProbabilityMeasure μ]
  [IsProbabilityMeasure (lossMeasure θ)]

/-- `T` does not see the current shock: `(Tf)(w, s) = (Tf)(w, s′)`. -/
theorem search_bellman_indep (f : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ)
    (w : Icc (0 : ℝ) wbar) (s s' : Two × Icc (0 : ℝ) wbar) :
    bellman (searchModel h.wbar_pos.le U θ β μ) (search_boundedDP h μ) f (w, s) =
      bellman (searchModel h.wbar_pos.le U θ β μ) (search_boundedDP h μ) f (w, s') := by
  simp only [bellman_apply, maxValue, objG, rhs, expV, searchF, Kernel.const_apply]

/-- The expected continuation values: working gives `θ f(0) + (1 − θ) f(w)`, searching
`∫ f dμ`, when `f` does not depend on the shock. -/
theorem search_expV {f : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ}
    (hf : ∀ w s s', f (w, s) = f (w, s')) (s₀ : Two × Icc (0 : ℝ) wbar)
    (w : Icc (0 : ℝ) wbar) (s : Two × Icc (0 : ℝ) wbar) :
    expV (searchModel h.wbar_pos.le U θ β μ) f (w, s) two1 =
        θ * f (w0 h.wbar_pos.le, s₀) + (1 - θ) * f (w, s₀) ∧
      expV (searchModel h.wbar_pos.le U θ β μ) f (w, s) two0 = ∫ z, f (z, s₀) ∂μ := by
  have hint : ∀ y, Integrable (fun p => f (searchφ h.wbar_pos.le (w, y, p), p))
      ((lossMeasure θ).prod μ) := fun y => by
    have hc : Continuous fun p : Two × Icc (0 : ℝ) wbar => f (searchφ h.wbar_pos.le (w, y, p), p) :=
      f.continuous.comp (((continuous_searchφ' h.wbar_pos.le).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))).prodMk continuous_id)
    exact integrable_of_abs_le hc.measurable fun p => by
      rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
  simp only [expV, Kernel.const_apply]
  constructor
  · rw [integral_loss_prod h.θ_nonneg h.θ_le μ (hint two1)]
    have e1 : ∀ z, searchφ h.wbar_pos.le (w, two1, (two1, z)) = w := fun z => by
      simp [searchφ]
    have e0 : ∀ z, searchφ h.wbar_pos.le (w, two1, (two0, z)) = w0 h.wbar_pos.le := fun z => by
      simp [searchφ, two0_ne_two1]
    simp only [e0, e1]
    rw [show (fun z => f (w0 h.wbar_pos.le, (two0, z))) = fun _ => f (w0 h.wbar_pos.le, s₀) from
      funext fun z => hf _ _ _, show (fun z => f (w, (two1, z))) = fun _ => f (w, s₀) from
      funext fun z => hf _ _ _]
    simp
  · rw [integral_loss_prod h.θ_nonneg h.θ_le μ (hint two0)]
    have e : ∀ d z, searchφ h.wbar_pos.le (w, two0, (d, z)) = z := fun d z => by
      simp [searchφ, two0_ne_two1]
    simp only [e]
    rw [show (fun z => f (z, (two0, z))) = fun z => f (z, s₀) from funext fun z => hf _ _ _,
      show (fun z => f (z, (two1, z))) = fun z => f (z, s₀) from funext fun z => hf _ _ _]
    ring

/-- The value at a state is the larger of working and searching. -/
theorem search_bellman_eq_max {f : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ}
    (hf : ∀ w s s', f (w, s) = f (w, s')) (s₀ : Two × Icc (0 : ℝ) wbar)
    (w : Icc (0 : ℝ) wbar) (s : Two × Icc (0 : ℝ) wbar) :
    bellman (searchModel h.wbar_pos.le U θ β μ) (search_boundedDP h μ) f (w, s) =
      max (U w.1 + β * (θ * f (w0 h.wbar_pos.le, s₀) + (1 - θ) * f (w, s₀)))
        (β * ∫ z, f (z, s₀) ∂μ) := by
  set M := searchModel h.wbar_pos.le U θ β μ
  have hb := search_boundedDP h μ
  obtain ⟨e1, e0⟩ := search_expV h μ hf s₀ w s
  have r1 : rhs M f (w, s) two1 =
      U w.1 + β * (θ * f (w0 h.wbar_pos.le, s₀) + (1 - θ) * f (w, s₀)) := by
    simp only [rhs]; rw [e1]; simp [M, searchF]
  have r0 : rhs M f (w, s) two0 = β * ∫ z, f (z, s₀) ∂μ := by
    simp only [rhs]; rw [e0]; simp [M, searchF, two0_ne_two1]
  obtain ⟨y, -, hval, hmax⟩ := exists_bellman_argmax M hb f (w, s)
  rw [← r1, ← r0]
  refine le_antisymm ?_ (max_le (hmax two1 (mem_univ _)) (hmax two0 (mem_univ _)))
  rw [hval]
  rcases two_cases y with rfl | rfl
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- **Exercise 10.7b–c.** Let `v` be the fixed point of `T` (Theorem 9.6), and `v(w)` its section
at any shock `s₀`. Then `v(w, s)` does not depend on `s`; `v(w)` satisfies (1) and is the only
continuous solution of (1); `v(w)` is nondecreasing; and `v(w) = v*(w, s)` for every `s`, so the
supremum function depends only on `w₀`. -/
theorem ex_10_7c {v : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ}
    (hv : bellman (searchModel h.wbar_pos.le U θ β μ) (search_boundedDP h μ) v = v)
    (s₀ : Two × Icc (0 : ℝ) wbar) :
    (∀ w s, v (w, s) = v (w, s₀)) ∧
      (∀ w, v (w, s₀) = max (U w.1 + β * ((1 - θ) * v (w, s₀) + θ * v (w0 h.wbar_pos.le, s₀)))
        (β * ∫ z, v (z, s₀) ∂μ)) ∧
      (∀ u : C(Icc (0 : ℝ) wbar, ℝ), (∀ w, u w = max (U w.1 + β * ((1 - θ) * u w +
        θ * u (w0 h.wbar_pos.le))) (β * ∫ z, u z ∂μ)) → ∀ w, u w = v (w, s₀)) ∧
      Monotone (fun w => v (w, s₀)) ∧
      ∀ w s, vStar (searchModel h.wbar_pos.le U θ β μ) (w, s) = v (w, s₀) := by
  set M := searchModel h.wbar_pos.le U θ β μ
  have hb := search_boundedDP h μ
  obtain ⟨v', -, huniq, -, -⟩ := ex_9_7b M hb
  have hind : ∀ w s s', v (w, s) = v (w, s') := fun w s s' => by
    rw [← hv]; exact search_bellman_indep h μ v w s s'
  have hfe : ∀ w, v (w, s₀) = max (U w.1 + β * ((1 - θ) * v (w, s₀) +
      θ * v (w0 h.wbar_pos.le, s₀))) (β * ∫ z, v (z, s₀) ∂μ) := fun w => by
    conv_lhs => rw [← hv]
    rw [search_bellman_eq_max h μ hind s₀ w s₀]
    ring_nf
  refine ⟨fun w s => hind w s s₀, hfe, fun u hu w => ?_, ?_, fun w s => ?_⟩
  · -- uniqueness: lift `u` to a fixed point of `T`
    have : CompactSpace (Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar)) := inferInstance
    set ũ : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ :=
      mkOfCompact (u.comp ⟨Prod.fst, continuous_fst⟩)
    have hũ : ∀ w s s', ũ (w, s) = ũ (w, s') := fun _ _ _ => rfl
    have hfix : bellman M hb ũ = ũ := by
      ext ⟨w, s⟩
      rw [search_bellman_eq_max h μ hũ s₀ w s]
      change _ = u w
      rw [hu w]
      change max (U w.1 + β * (θ * u (w0 h.wbar_pos.le) + (1 - θ) * u w)) (β * ∫ z, u z ∂μ) = _
      ring_nf
    have := (huniq ũ hfix).trans (huniq v hv).symm
    change ũ (w, s₀) = v (w, s₀)
    rw [this]
  · -- monotonicity: `T` maps functions nondecreasing in `w` into themselves
    set C' : Set (Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) →ᵇ ℝ) :=
      {f | ∀ s, Monotone fun w => f (w, s)}
    have hclosed : IsClosed C' := by
      have := isClosed_pointwise_le (S := Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar))
        (ι := {q : Icc (0 : ℝ) wbar × Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) //
          q.1 ≤ q.2.1}) (fun q => (q.1.1, q.1.2.2)) (fun q => (q.1.2.1, q.1.2.2))
      convert this using 1
      ext f
      exact ⟨fun hf q => hf q.1.2.2 q.2, fun hf s w w' hww' => hf ⟨(w, w', s), hww'⟩⟩
    have hmaps : MapsTo (bellman M hb) C' C' := by
      intro f hf s w w' hww'
      obtain ⟨y, -, hval, -⟩ := exists_bellman_argmax M hb f (w, s)
      obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb f (w', s)
      dsimp only
      rw [hval]
      refine le_trans ?_ (hmax y (mem_univ _))
      simp only [rhs, expV]
      have hint : ∀ x, Integrable (fun p => f (searchφ h.wbar_pos.le (x, y, p), p))
          ((lossMeasure θ).prod μ) := fun x => by
        have hc : Continuous fun p : Two × Icc (0 : ℝ) wbar =>
            f (searchφ h.wbar_pos.le (x, y, p), p) :=
          f.continuous.comp (((continuous_searchφ' h.wbar_pos.le).comp
            (continuous_const.prodMk (continuous_const.prodMk continuous_id))).prodMk
              continuous_id)
        exact integrable_of_abs_le hc.measurable fun p => by
          rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
      have hE := integral_mono (hint w) (hint w') fun p => by
        refine hf p ?_
        change searchφ h.wbar_pos.le (w, y, p) ≤ searchφ h.wbar_pos.le (w', y, p)
        simp only [searchφ]
        split_ifs
        · exact hww'
        · exact le_rfl
        · exact le_rfl
      have hF : searchF U (w, y, s) ≤ searchF U (w', y, s) := by
        simp only [searchF]
        split_ifs
        · exact h.U_mono.monotoneOn w.2 w'.2 hww'
        · exact le_rfl
      change searchF U (w, y, s) + β * ∫ p, f (searchφ h.wbar_pos.le (w, y, p), p)
          ∂((lossMeasure θ).prod μ) ≤
        searchF U (w', y, s) + β * ∫ p, f (searchφ h.wbar_pos.le (w', y, p), p)
          ∂((lossMeasure θ).prod μ)
      have := mul_le_mul_of_nonneg_left hE h.β_pos.le
      linarith
    exact (corollary_1 (S' := C') (S'' := C') (bellman_contraction M hb) hv
      ⟨0, fun _ _ _ _ => le_rfl⟩ hclosed hmaps hmaps).1 s₀
  · -- `v = v*`, with the measurable policy "work iff working is at least as good"
    have hcont : Continuous fun p : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) =>
        (objG M v (p, two1), objG M v (p, two0)) := by
      have hc := continuousOn_univ.1 ((continuousOn_objG M hb v).mono fun _ _ => mem_univ _)
      exact (hc.comp (continuous_id.prodMk continuous_const)).prodMk
        (hc.comp (continuous_id.prodMk continuous_const))
    set g : Icc (0 : ℝ) wbar × (Two × Icc (0 : ℝ) wbar) → Two := fun p =>
      if objG M v (p, two0) ≤ objG M v (p, two1) then two1 else two0
    have hgm : Measurable g := by
      classical
      refine Measurable.ite ?_ measurable_const measurable_const
      exact (isClosed_le (continuous_snd.comp hcont) (continuous_fst.comp hcont)).measurableSet
    have hgG : ∀ p, g p ∈ policy M v p := fun p => by
      rw [policy_eq_argmax M hb hv]
      refine ⟨mem_univ _, le_antisymm ?_ ?_⟩
      · exact le_maxValue (continuousOn_objG M hb v) (hb.compact p) (mem_univ _)
      · obtain ⟨y, -, hval, hmax⟩ := exists_argmax (continuousOn_objG M hb v) (hb.compact p)
          (hb.nonempty p)
        rw [← hval]
        simp only [g]
        split_ifs with hle
        · rcases two_cases y with rfl | rfl
          · exact hle
          · exact le_rfl
        · rcases two_cases y with rfl | rfl
          · exact le_rfl
          · exact (not_le.1 hle).le
    have hopt := bounded_vStar M hb (continuous_searchφ' h.wbar_pos.le).measurable
      (continuous_searchF h).measurable hv (g := fun _ => g) (fun _ => hgm) (fun _ => hgG) (w, s)
    rw [hopt.2.2, hind w s s₀]

end StokeyLucasPrescott.StochasticApplications

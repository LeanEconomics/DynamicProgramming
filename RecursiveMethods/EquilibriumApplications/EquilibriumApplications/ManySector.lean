/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.LinftyTimeState

/-!
# A many-sector model of stochastic growth: the consumption side

SLP §16.2, pp. 481–482. `(Z^t, 𝒵^t, μ^t)` are probability spaces (`Ω t`, `μ t`) and the commodity
space is `S = LinftyTimeState μ`: sequences `c = (c_t)` with `c_t ∈ L∞(μ^t)` and
`‖c‖ = sup_t ‖c_t‖_∞`. One consumption good per period (`M = 1`; see the Correction).

* `msC`: the consumption set `C`, the positive orthant (`c_t ≥ 0` a.e.).
* `msU`: `u(c) = Σ_t βᵗ ∫ U[c_t(z^t)] dμ^t(z^t)` (§10.3 (1)); `ManySectorHyp`: `U` continuous,
  bounded, strictly increasing and strictly concave on `ℝ₊`, `0 < β < 1`.
* `msOne`: the constant plan `𝟙`.
* **Exercise 16.2(a), consumption side** (`ex_16_2a_consumer`): Assumptions 15.1, 15.2, 15.3,
  the consumer halves of 15.6 and 15.8′, 15.7 and 15.9′ hold for `(C, u)`;
  in detail `ms_convex_C`, `ms_U_concave`, `ms_U_continuous`, `ms_tendsto_U_timeTrunc`
  (`u(cᵀ) → u(c)`), `msU_periodTrunc` and `ms_tendsto_U_periodTrunc` (`u(c^{A_{tn}}) → u(c)`).
* `ms_U_lt_add_one`: nonsatiation `u(c + 𝟙) > u(c)`.
* `ms_supporting_nonneg`, `ms_abs_le_of_nonneg`, `ms_one_pos`, `ms_interior_ge`: a functional
  supporting a consumption plan is positive on `C`, bounded by its value at `𝟙`, and `φ(𝟙) > 0`
  unless `φ = 0`; points with a ball inside `C` are `≥ ε𝟙`.

**Correction.** `U` is taken continuous and bounded on all of `ℝ` (only its values on `ℝ₊`
matter, as consumption is a.e. nonnegative; e.g. replace `U` by `U ∘ max 0`). The book has `M`
consumption goods; the Chapter 15 Theorem 15.9 of this project, used in Exercise 16.2(b), is for
one good per period (the book's own statement of Theorem 15.9 is one-good, NOTE (iv) to Ex 16.2a),
so `M = 1` here.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set

variable {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] {μ : ∀ t, Measure (Ω t)}

/-- The restrictions of §16.2 / §10.3 on `U` and `β` (one consumption good). -/
structure ManySectorHyp (U : ℝ → ℝ) (β : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  U_cont : Continuous U
  U_bdd : ∃ B, ∀ x, |U x| ≤ B
  U_strictMono : StrictMonoOn U (Ici 0)
  U_strictConcave : StrictConcaveOn ℝ (Ici 0) U

/-- The consumption set `C` (p. 482): the positive orthant of `S`. -/
def msC (μ : ∀ t, Measure (Ω t)) : Set (LinftyTimeState μ) := {c | ∀ t, ∀ᵐ ω ∂μ t, 0 ≤ c t ω}

/-- Preferences `u(c) = Σ_t βᵗ ∫ U(c_t) dμ^t` (§10.3 (1)). -/
noncomputable def msU (μ : ∀ t, Measure (Ω t)) (β : ℝ) (U : ℝ → ℝ) (c : LinftyTimeState μ) : ℝ :=
  ∑' t, β ^ t * linftyExpectedUtility (μ t) U (c t)

/-- Coordinates of a sum. -/
theorem ms_coord_add (c d : LinftyTimeState μ) (t : ℕ) : (c + d) t = c t + d t := by
  rw [lp.coeFn_add]; rfl

/-- Coordinates of a difference. -/
theorem ms_coord_sub (c d : LinftyTimeState μ) (t : ℕ) : (c - d) t = c t - d t := by
  rw [lp.coeFn_sub]; rfl

/-- Coordinates of a scalar multiple. -/
theorem ms_coord_smul (a : ℝ) (c : LinftyTimeState μ) (t : ℕ) : (a • c) t = a • c t := by
  rw [lp.coeFn_smul]; rfl

variable [∀ t, IsProbabilityMeasure (μ t)]

/-- The constant plan `𝟙`. -/
noncomputable def msOne (μ : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (μ t)] :
    LinftyTimeState μ :=
  ⟨fun t => linftyOne (μ t), memℓp_infty ⟨1, by rintro _ ⟨t, rfl⟩; exact norm_linftyOne_le⟩⟩

/-- `𝟙_t = 1` a.e. -/
theorem msOne_ae (t : ℕ) : ∀ᵐ ω ∂μ t, msOne μ t ω = 1 := coeFn_linftyOne

/-- `‖𝟙‖ ≤ 1`. -/
theorem norm_msOne_le : ‖msOne μ‖ ≤ 1 :=
  lp.norm_le_of_forall_le zero_le_one fun _ => norm_linftyOne_le

variable {U : ℝ → ℝ} {β : ℝ}

/-- `|∫ U(x) dμ^t| ≤ B` for `|U| ≤ B`. -/
theorem ms_eu_abs_le {B : ℝ} (hB : ∀ x, |U x| ≤ B) (t : ℕ) (x : Lp ℝ ⊤ (μ t)) :
    |linftyExpectedUtility (μ t) U x| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ t) (f := fun ω => U (x ω)) (C := B)
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)
  simpa [linftyExpectedUtility, probReal_univ] using this

/-- The terms of `u` are bounded by `B βᵗ`. -/
theorem ms_term_le (H : ManySectorHyp U β) {B : ℝ} (hB : ∀ x, |U x| ≤ B) (c : LinftyTimeState μ)
    (t : ℕ) : ‖β ^ t * linftyExpectedUtility (μ t) U (c t)‖ ≤ B * β ^ t := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos H.beta_pos t), mul_comm]
  exact mul_le_mul_of_nonneg_right (ms_eu_abs_le hB t _) (pow_nonneg H.beta_pos.le t)

/-- The series defining `u` converges. -/
theorem ms_summable (H : ManySectorHyp U β) (c : LinftyTimeState μ) :
    Summable fun t => β ^ t * linftyExpectedUtility (μ t) U (c t) := by
  obtain ⟨B, hB⟩ := H.U_bdd
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one H.beta_pos.le
    H.beta_lt_one).mul_left B) (ms_term_le H hB c)

/-! ### Assumptions 15.1–15.3 -/

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- **Assumption 15.1**: `C` is convex. -/
theorem ms_convex_C : Convex ℝ (msC μ) := by
  intro c hc d hd a b ha hb _ t
  filter_upwards [hc t, hd t, Lp.coeFn_add (a • c t) (b • d t), Lp.coeFn_smul a (c t),
    Lp.coeFn_smul b (d t)] with ω h1 h2 h3 h4 h5
  rw [ms_coord_add, ms_coord_smul, ms_coord_smul, h3, Pi.add_apply, h4, h5, Pi.smul_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  positivity

/-- `U ∘ x` is integrable for `x ∈ L∞(μ^t)`. -/
theorem ms_integrable (H : ManySectorHyp U β) (t : ℕ) (x : Lp ℝ ⊤ (μ t)) :
    Integrable (fun ω => U (x ω)) (μ t) :=
  integrable_comp_linfty Measure.AbsolutelyContinuous.rfl H.U_cont x

/-- Per-period concavity on a.e. nonnegative plans. -/
theorem ms_eu_concave (H : ManySectorHyp U β) (t : ℕ) {x x' : Lp ℝ ⊤ (μ t)}
    (hx : ∀ᵐ ω ∂μ t, 0 ≤ x ω) (hx' : ∀ᵐ ω ∂μ t, 0 ≤ x' ω) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * linftyExpectedUtility (μ t) U x + (1 - θ) * linftyExpectedUtility (μ t) U x' ≤
      linftyExpectedUtility (μ t) U (θ • x + (1 - θ) • x') := by
  rw [linftyExpectedUtility, linftyExpectedUtility, linftyExpectedUtility,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((ms_integrable H t x).const_mul θ) ((ms_integrable H t x').const_mul (1 - θ))]
  refine integral_mono_ae (((ms_integrable H t x).const_mul θ).add
    ((ms_integrable H t x').const_mul (1 - θ))) (ms_integrable H t _) ?_
  filter_upwards [Lp.coeFn_add (θ • x) ((1 - θ) • x'), Lp.coeFn_smul θ x,
    Lp.coeFn_smul (1 - θ) x', hx, hx'] with ω e1 e2 e3 p1 p2
  rw [e1, Pi.add_apply, e2, e3, Pi.smul_apply, Pi.smul_apply]
  have := H.U_strictConcave.concaveOn.2 (mem_Ici.2 p1) (mem_Ici.2 p2) h0
    (show (0 : ℝ) ≤ 1 - θ by linarith) (show θ + (1 - θ) = 1 by ring)
  simpa only [smul_eq_mul] using this

/-- `u` is concave on `C`. -/
theorem ms_U_concave (H : ManySectorHyp U β) : ConcaveOn ℝ (msC μ) (msU μ β U) := by
  refine ⟨ms_convex_C, fun c hc d hd a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  simp only [smul_eq_mul, msU]
  rw [← tsum_mul_left, ← tsum_mul_left, ← (((ms_summable H c).mul_left a)).tsum_add
    ((ms_summable H d).mul_left (1 - a))]
  refine Summable.tsum_le_tsum (fun t => ?_) (((ms_summable H c).mul_left a).add
    ((ms_summable H d).mul_left (1 - a))) (ms_summable H _)
  rw [ms_coord_add, ms_coord_smul, ms_coord_smul]
  have := ms_eu_concave H t (hc t) (hd t) ha (by linarith)
  have hβ := pow_pos H.beta_pos t
  nlinarith [mul_le_mul_of_nonneg_left this hβ.le]

/-- **Assumption 15.2** (from concavity of `U`). -/
theorem ms_assumption15_2 (H : ManySectorHyp U β) :
    Assumption15_2 (fun _ : Unit => msC μ) (fun _ => msU μ β U) := by
  intro _ z hz z' hz' hlt θ h0 h1
  have := (ms_U_concave H).2 hz hz' h0.le (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at this
  nlinarith

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- Coordinates are `1`-Lipschitz. -/
theorem ms_continuous_coord (t : ℕ) : Continuous fun c : LinftyTimeState μ => c t :=
  LipschitzWith.continuous (K := 1) <| LipschitzWith.of_dist_le_mul fun c d => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← ms_coord_sub]
    exact norm_linftyTimeState_apply_le _ t

/-- **Assumption 15.3**: `u` is continuous on `S` (uniformly convergent series of continuous
terms; each term is continuous by uniform continuity of `U` on bounded sets, Ex 15.12). -/
theorem ms_U_continuous (H : ManySectorHyp U β) : Continuous (msU μ β U) := by
  obtain ⟨B, hB⟩ := H.U_bdd
  exact continuous_tsum (fun t => continuous_const.mul
    ((ex_15_12_continuous Measure.AbsolutelyContinuous.rfl H.U_cont).comp
      (ms_continuous_coord t)))
    ((summable_geometric_of_lt_one H.beta_pos.le H.beta_lt_one).mul_left B)
    (fun t c => ms_term_le H hB c t)

/-! ### Truncations -/

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- `C` is closed under time truncation. -/
theorem ms_C_timeTrunc {c : LinftyTimeState μ} (hc : c ∈ msC μ) (T : ℕ) :
    linftyTimeTrunc T c ∈ msC μ := fun t => by
  rw [linftyTimeTrunc_apply]
  split_ifs
  · exact hc t
  · filter_upwards [Lp.coeFn_zero ℝ ⊤ (μ t)] with ω h
    rw [h]; rfl

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- `C` is closed under truncation on an event in one period. -/
theorem ms_C_periodTrunc {c : LinftyTimeState μ} (hc : c ∈ msC μ) (s : ℕ) {A : Set (Ω s)}
    (hA : MeasurableSet A) : linftyPeriodTrunc s A c ∈ msC μ := fun t => by
  by_cases hts : t = s
  · subst hts
    rw [linftyPeriodTrunc_apply_self]
    filter_upwards [coeFn_linftyRestrict hA.compl (c t), hc t] with ω h1 h2
    rw [linftyTrunc, h1]
    by_cases hω : ω ∈ Aᶜ
    · rw [indicator_of_mem hω]; exact h2
    · rw [indicator_of_notMem hω]
  · rw [linftyPeriodTrunc_apply_of_ne hts]
    exact hc t

/-- `u(cᵀ) → u(c)` (dominated convergence; `U` bounded). -/
theorem ms_tendsto_U_timeTrunc (H : ManySectorHyp U β) (c : LinftyTimeState μ) :
    Tendsto (fun T => msU μ β U (linftyTimeTrunc T c)) atTop (𝓝 (msU μ β U c)) := by
  obtain ⟨B, hB⟩ := H.U_bdd
  refine tendsto_tsum_of_dominated_convergence ((summable_geometric_of_lt_one H.beta_pos.le
    H.beta_lt_one).mul_left B) (fun t => ?_) (Eventually.of_forall fun T t => ms_term_le H hB _ t)
  refine tendsto_const_nhds.congr' ((eventually_ge_atTop t).mono fun T hT => ?_)
  simp only [linftyTimeTrunc_apply, hT, ↓reduceIte]

/-- **Assumption 15.7** (time–state form). -/
theorem ms_assumption15_7 (H : ManySectorHyp U β) :
    Assumption15_7_timeState (fun _ : Unit => msC μ) (fun _ => msU μ β U) :=
  fun _ x _ _ _ hlt => (ms_tendsto_U_timeTrunc H x).eventually (lt_mem_nhds hlt)

/-- Truncating period `s` on `A` changes only the period-`s` term of `u`. -/
theorem msU_periodTrunc (H : ManySectorHyp U β) (c : LinftyTimeState μ) (s : ℕ) (A : Set (Ω s)) :
    msU μ β U (linftyPeriodTrunc s A c) = msU μ β U c + β ^ s *
      (linftyExpectedUtility (μ s) U (linftyTrunc (μ s) A (c s)) -
        linftyExpectedUtility (μ s) U (c s)) := by
  rw [msU, msU, ← sub_eq_iff_eq_add', ← (ms_summable H _).tsum_sub (ms_summable H c),
    tsum_eq_single s fun t ht => by rw [linftyPeriodTrunc_apply_of_ne ht, sub_self],
    linftyPeriodTrunc_apply_self]
  ring

/-- `u(c^{A_n}) → u(c)` when `A_n ↓ 0` in period `s` (Ex 15.12). -/
theorem ms_tendsto_U_periodTrunc (H : ManySectorHyp U β) (c : LinftyTimeState μ) (s : ℕ)
    {A : ℕ → Set (Ω s)} (hA : LinftyNullSeq (μ s) A) :
    Tendsto (fun n => msU μ β U (linftyPeriodTrunc s (A n) c)) atTop (𝓝 (msU μ β U c)) := by
  simp only [msU_periodTrunc H]
  have := ((ex_15_12_tendsto Measure.AbsolutelyContinuous.rfl H.U_cont hA (c s)).sub_const
    (linftyExpectedUtility (μ s) U (c s))).const_mul (β ^ s)
  simpa using (tendsto_const_nhds (x := msU μ β U c)).add this

/-- **Assumption 15.9′**. -/
theorem ms_assumption15_9' (H : ManySectorHyp U β) :
    Assumption15_9' μ (fun _ : Unit => msC μ) (fun _ => msU μ β U) :=
  fun _ s x _ _ _ hlt _ hA => (ms_tendsto_U_periodTrunc H x s hA).eventually (lt_mem_nhds hlt)

/-- **Exercise 16.2(a), consumption side**: `(C, u)` satisfy Assumptions 15.1, 15.2, 15.3, 15.7
and 15.9′, and `C` is closed under time truncations (15.6) and event truncations (15.8′). -/
theorem ex_16_2a_consumer (H : ManySectorHyp U β) :
    Assumption15_1 (fun _ : Unit => msC μ) ∧ Assumption15_2 (fun _ : Unit => msC μ)
      (fun _ => msU μ β U) ∧ Assumption15_3 (fun _ : Unit => msC μ) (fun _ => msU μ β U) ∧
      Assumption15_7_timeState (fun _ : Unit => msC μ) (fun _ => msU μ β U) ∧
      Assumption15_9' μ (fun _ : Unit => msC μ) (fun _ => msU μ β U) ∧
      (∀ c ∈ msC μ, ∀ T, linftyTimeTrunc T c ∈ msC μ) ∧
      ∀ c ∈ msC μ, ∀ s (A : Set (Ω s)), MeasurableSet A → linftyPeriodTrunc s A c ∈ msC μ :=
  ⟨fun _ => ms_convex_C, ms_assumption15_2 H, fun _ => (ms_U_continuous H).continuousOn,
    ms_assumption15_7 H, ms_assumption15_9' H, fun _ hc T => ms_C_timeTrunc hc T,
    fun _ hc s _ hA => ms_C_periodTrunc hc s hA⟩

/-! ### Monotonicity, nonsatiation and positive functionals -/

/-- `u` is monotone on `C`. -/
theorem ms_U_mono (H : ManySectorHyp U β) {c d : LinftyTimeState μ} (hc : c ∈ msC μ)
    (hcd : ∀ t, ∀ᵐ ω ∂μ t, c t ω ≤ d t ω) : msU μ β U c ≤ msU μ β U d := by
  refine Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left ?_
    (pow_nonneg H.beta_pos.le t)) (ms_summable H c) (ms_summable H d)
  refine integral_mono_ae (ms_integrable H t _) (ms_integrable H t _) ?_
  filter_upwards [hc t, hcd t] with ω h1 h2
  exact H.U_strictMono.monotoneOn (mem_Ici.2 h1) (mem_Ici.2 (h1.trans h2)) h2

/-- `c + 𝟙` coordinates. -/
theorem ms_add_one_ae (c : LinftyTimeState μ) (t : ℕ) :
    ∀ᵐ ω ∂μ t, (c + msOne μ) t ω = c t ω + 1 := by
  filter_upwards [Lp.coeFn_add (c t) (msOne μ t), msOne_ae (μ := μ) t] with ω h1 h2
  rw [ms_coord_add, h1, Pi.add_apply, h2]

/-- **Nonsatiation**: `u(c + 𝟙) > u(c)` for `c ∈ C`. -/
theorem ms_U_lt_add_one (H : ManySectorHyp U β) {c : LinftyTimeState μ} (hc : c ∈ msC μ) :
    msU μ β U c < msU μ β U (c + msOne μ) := by
  have hle : ∀ t, β ^ t * linftyExpectedUtility (μ t) U (c t) ≤
      β ^ t * linftyExpectedUtility (μ t) U ((c + msOne μ) t) := fun t =>
    mul_le_mul_of_nonneg_left (integral_mono_ae (ms_integrable H t _) (ms_integrable H t _) (by
      filter_upwards [hc t, ms_add_one_ae c t] with ω h1 h2
      rw [h2]
      exact H.U_strictMono.monotoneOn (mem_Ici.2 h1) (mem_Ici.2 (by linarith)) (by linarith)))
      (pow_nonneg H.beta_pos.le t)
  have hlt0 : linftyExpectedUtility (μ 0) U (c 0) <
      linftyExpectedUtility (μ 0) U ((c + msOne μ) 0) := by
    rw [linftyExpectedUtility, linftyExpectedUtility, ← sub_pos,
      ← integral_sub (ms_integrable H 0 _) (ms_integrable H 0 _)]
    have hpos : ∀ᵐ ω ∂μ 0, 0 < U ((c + msOne μ) 0 ω) - U (c 0 ω) := by
      filter_upwards [hc 0, ms_add_one_ae c 0] with ω h1 h2
      rw [h2, sub_pos]
      exact H.U_strictMono (mem_Ici.2 h1) (mem_Ici.2 (by linarith)) (by linarith)
    rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ h => h.le)
      ((ms_integrable H 0 _).sub (ms_integrable H 0 _))]
    by_contra hz
    have hz' : (μ 0) (Function.support fun ω => U ((c + msOne μ) 0 ω) - U (c 0 ω)) = 0 :=
      le_antisymm (not_lt.1 hz) zero_le
    have hnot := measure_eq_zero_iff_ae_notMem.1 hz'
    obtain ⟨ω, h1, h2⟩ := (hpos.and hnot).exists
    exact h2 (Function.mem_support.2 h1.ne')
  have := Summable.tsum_lt_tsum (i := 0) hle (mul_lt_mul_of_pos_left hlt0 (pow_pos H.beta_pos 0))
    (ms_summable H c) (ms_summable H _)
  exact this

/-- `c + 𝟙 ∈ C` for `c ∈ C`. -/
theorem ms_add_one_mem {c : LinftyTimeState μ} (hc : c ∈ msC μ) : c + msOne μ ∈ msC μ :=
  fun t => by
    filter_upwards [hc t, ms_add_one_ae c t] with ω h1 h2
    rw [h2]; linarith

/-- A functional supporting `c⁰ ∈ C` (condition (3) of Theorem 15.4) is **positive** on `C`. -/
theorem ms_supporting_nonneg (H : ManySectorHyp U β) {c₀ : LinftyTimeState μ} (hc₀ : c₀ ∈ msC μ)
    {φ : StrongDual ℝ (LinftyTimeState μ)}
    (hφ : ∀ z ∈ msC μ, msU μ β U c₀ ≤ msU μ β U z → φ c₀ ≤ φ z) {z : LinftyTimeState μ}
    (hz : z ∈ msC μ) : 0 ≤ φ z := by
  have hsum : c₀ + z ∈ msC μ := fun t => by
    filter_upwards [hc₀ t, hz t, Lp.coeFn_add (c₀ t) (z t)] with ω h1 h2 h3
    rw [ms_coord_add, h3, Pi.add_apply]; linarith
  have := hφ _ hsum (ms_U_mono H hc₀ fun t => by
    filter_upwards [hz t, Lp.coeFn_add (c₀ t) (z t)] with ω h2 h3
    rw [ms_coord_add, h3, Pi.add_apply]; linarith)
  rw [map_add] at this
  linarith

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- `|z_t| ≤ ‖z‖` a.e. -/
theorem ms_ae_abs_le (z : LinftyTimeState μ) (t : ℕ) : ∀ᵐ ω ∂μ t, |z t ω| ≤ ‖z‖ := by
  filter_upwards [ae_abs_le_norm_linfty (z t)] with ω h
  exact h.trans (norm_linftyTimeState_apply_le z t)

/-- `(a • 𝟙 + b • z)_t = a + b z_t` a.e. -/
theorem ms_combo_one_ae (a b : ℝ) (z : LinftyTimeState μ) (t : ℕ) :
    ∀ᵐ ω ∂μ t, (a • msOne μ + b • z) t ω = a + b * z t ω := by
  filter_upwards [Lp.coeFn_add (a • msOne μ t) (b • z t), Lp.coeFn_smul a (msOne μ t),
    Lp.coeFn_smul b (z t), msOne_ae (μ := μ) t] with ω h1 h2 h3 h4
  rw [ms_coord_add, ms_coord_smul, ms_coord_smul, h1, Pi.add_apply, h2, h3, Pi.smul_apply,
    Pi.smul_apply, h4, smul_eq_mul, smul_eq_mul, mul_one]

/-- A positive functional is bounded by its value at `𝟙`: `|φ(z)| ≤ ‖z‖ φ(𝟙)`. -/
theorem ms_abs_le_of_nonneg {φ : StrongDual ℝ (LinftyTimeState μ)}
    (hφ : ∀ z ∈ msC μ, 0 ≤ φ z) (z : LinftyTimeState μ) : |φ z| ≤ ‖z‖ * φ (msOne μ) := by
  have h1 : ‖z‖ • msOne μ + (-1 : ℝ) • z ∈ msC μ := fun t => by
    filter_upwards [ms_combo_one_ae ‖z‖ (-1) z t, ms_ae_abs_le z t] with ω e h
    rw [e]; linarith [(abs_le.1 h).2]
  have h2 : ‖z‖ • msOne μ + (1 : ℝ) • z ∈ msC μ := fun t => by
    filter_upwards [ms_combo_one_ae ‖z‖ 1 z t, ms_ae_abs_le z t] with ω e h
    rw [e]; linarith [(abs_le.1 h).1]
  have a1 := hφ _ h1
  have a2 := hφ _ h2
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at a1 a2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- A nonzero positive functional has `φ(𝟙) > 0`. -/
theorem ms_one_pos {φ : StrongDual ℝ (LinftyTimeState μ)} (hφ : ∀ z ∈ msC μ, 0 ≤ φ z)
    (hne : φ ≠ 0) : 0 < φ (msOne μ) := by
  have h1 : msOne μ ∈ msC μ := fun t => by
    filter_upwards [msOne_ae (μ := μ) t] with ω h
    rw [h]; exact zero_le_one
  rcases (hφ _ h1).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply hne
    ext z
    have := ms_abs_le_of_nonneg hφ z
    rw [← heq, mul_zero] at this
    simpa using abs_nonpos_iff.1 this

/-- A point with a ball of radius `r` inside `C` is `≥ (r/2)𝟙`: `y − (r/2)𝟙 ∈ C`. -/
theorem ms_interior_ge {Y : Set (LinftyTimeState μ)} (hYC : Y ⊆ msC μ) {y : LinftyTimeState μ}
    (hy : y ∈ interior Y) : ∃ ε : ℝ, 0 < ε ∧ y + (-ε) • msOne μ ∈ msC μ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy)
  refine ⟨r / 2, half_pos hr, hYC (hball ?_)⟩
  rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (half_pos hr)]
  calc r / 2 * ‖msOne μ‖ ≤ r / 2 * 1 := mul_le_mul_of_nonneg_left norm_msOne_le (half_pos hr).le
    _ < r := by linarith

end StokeyLucasPrescott.EquilibriumApplications

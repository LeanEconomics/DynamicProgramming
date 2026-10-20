/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.IndustryEquilibrium
import EquilibriumApplications.SustainedGrowthWelfare

/-!
# Industry investment as a general equilibrium model (Exercise 16.4(d)–(e))

SLP §16.4, p. 491. The commodity space `L` is made a normed space, `IndustrySpace ℱ`: bounded
`ℱ`-adapted pairs `(q_t, I_t)`, a closed subspace of `ℓ_∞(ℕ × Ω; ℝ²)` with the sup norm
`sup_{t, ω} max(|q_t(ω)|, |I_t(ω)|)` (equivalent to the book's `sup_t (‖q_t‖_∞ + ‖I_t‖_∞)`).
`indQ s`, `indI s` are the two components of `s`, and `indMk` builds `s` from a plan in `L`.
The **synthetic consumer** has `X = L₊` (`indX`) and `u(q, I) = E Σ (1 + r)⁻ᵗ [U(q_t, z_t) − I_t]`
(`indU`); the firm has production set `Y` (`indY`).

* **Exercise 16.4(d)** (`ex_16_4d`): `(X, u)` satisfies Assumptions 15.1–15.3 and `Y` satisfies
  15.4 and 15.5 (interior point: `q ≡ k₀/2`, `I ≡ k₀ c(1)`, `industry_interior`).
* `indPriceDual p`: the price functional `φ(q, I) = E Σ (1 + r)⁻ᵗ [p_t q_t − I_t]` for a bounded
  measurable `p`, a continuous linear functional on `L`.
* **Exercise 16.4(e), part (b)** (`ex_16_4e_b`, `ex_16_4e_competitiveEq`): an industry
  equilibrium `(q, I, p)` gives a competitive equilibrium `((q, I), (q, I), φ_p)` of the synthetic
  economy, hence (Theorem 15.3) a Pareto optimum, hence a surplus maximum.
* **Exercise 16.4(e), part (c)** (`ex_16_4e_c`): a surplus maximum is Pareto optimal
  (`indParetoOptimal_of_surplusMax`), so Theorem 15.4 gives a nonzero supporting `φ`, and the
  interior point of `Y` (which lies in `X`) is a cheaper point, so `φ` is a competitive
  equilibrium price (Remark to Theorem 15.4).

**Correction (Ex 16.4(e)).** "Theorems 15.3–15.6": there is no Theorem 15.5 (it is Lemma 15.5).
Theorem 15.3 gives (b) (proved here). Theorem 15.4 gives only *some* nonzero continuous linear
`φ` on `L` (proved here, together with the cheaper point); nothing in Theorems 15.4–15.6 shows
that `φ` is the functional `φ_p` with `p_t = D(q_t, z_t)` of (I2), nor even that it has the
inner-product form `Σ_t ∫ p_t x_t dμ` with `p_t ∈ L¹`: that would need Theorem 15.9, whose
Assumption 15.8′ fails for this `Y` (`IndustryLinfty.industry_not_assumption15_8'`). Part (c)
itself is proved directly in `IndustryEquilibrium.ex_16_4c` (the derivative argument).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The adapted bounded pairs, a submodule of `ℓ_∞(ℕ × Ω; ℝ × ℝ)`. -/
def industrySub (ℱ : Filtration ℕ mΩ) : Submodule ℝ (lp (fun _ : ℕ × Ω => ℝ × ℝ) ∞) where
  carrier := {x | ∀ t, StronglyMeasurable[ℱ t] (fun ω => (x (t, ω)).1) ∧
    StronglyMeasurable[ℱ t] (fun ω => (x (t, ω)).2)}
  add_mem' := fun hx hy t => ⟨(hx t).1.add (hy t).1, (hx t).2.add (hy t).2⟩
  zero_mem' := fun _ => ⟨stronglyMeasurable_const, stronglyMeasurable_const⟩
  smul_mem' := fun a _ hx t => ⟨(hx t).1.const_smul a, (hx t).2.const_smul a⟩

/-- The **commodity space** `L` of §16.4 as a normed space. -/
abbrev IndustrySpace (ℱ : Filtration ℕ mΩ) : Type _ := ↥(industrySub ℱ)

variable {ℱ : Filtration ℕ mΩ}

/-- Production `q_t(ω)` of `s ∈ L`. -/
def indQ (s : IndustrySpace ℱ) : ℕ → Ω → ℝ :=
  fun t ω => ((s : lp (fun _ : ℕ × Ω => ℝ × ℝ) ∞) (t, ω)).1

/-- Investment `I_t(ω)` of `s ∈ L`. -/
def indI (s : IndustrySpace ℱ) : ℕ → Ω → ℝ :=
  fun t ω => ((s : lp (fun _ : ℕ × Ω => ℝ × ℝ) ∞) (t, ω)).2

/-- Components of a linear combination. -/
theorem indQ_combo (a b : ℝ) (s s' : IndustrySpace ℱ) (t : ℕ) (ω : Ω) :
    indQ (a • s + b • s') t ω = a * indQ s t ω + b * indQ s' t ω := rfl

/-- Components of a linear combination. -/
theorem indI_combo (a b : ℝ) (s s' : IndustrySpace ℱ) (t : ℕ) (ω : Ω) :
    indI (a • s + b • s') t ω = a * indI s t ω + b * indI s' t ω := rfl

/-- Components of a sum. -/
theorem indQ_add (s s' : IndustrySpace ℱ) (t : ℕ) (ω : Ω) :
    indQ (s + s') t ω = indQ s t ω + indQ s' t ω := rfl

/-- Components of a sum. -/
theorem indI_add (s s' : IndustrySpace ℱ) (t : ℕ) (ω : Ω) :
    indI (s + s') t ω = indI s t ω + indI s' t ω := rfl

/-- Components of a difference. -/
theorem indQ_sub (s s' : IndustrySpace ℱ) (t : ℕ) (ω : Ω) :
    indQ (s - s') t ω = indQ s t ω - indQ s' t ω := rfl

/-- Components of a difference. -/
theorem indI_sub (s s' : IndustrySpace ℱ) (t : ℕ) (ω : Ω) :
    indI (s - s') t ω = indI s t ω - indI s' t ω := rfl

/-- Components of a multiple. -/
theorem indQ_smul (a : ℝ) (s : IndustrySpace ℱ) (t : ℕ) (ω : Ω) :
    indQ (a • s) t ω = a * indQ s t ω := rfl

/-- Components of a multiple. -/
theorem indI_smul (a : ℝ) (s : IndustrySpace ℱ) (t : ℕ) (ω : Ω) :
    indI (a • s) t ω = a * indI s t ω := rfl

/-- `|q_t(ω)|, |I_t(ω)| ≤ ‖s‖`. -/
theorem abs_ind_le (s : IndustrySpace ℱ) (t : ℕ) (ω : Ω) :
    |indQ s t ω| ≤ ‖s‖ ∧ |indI s t ω| ≤ ‖s‖ := by
  have h := lp.norm_apply_le_norm ENNReal.top_ne_zero (s : lp (fun _ : ℕ × Ω => ℝ × ℝ) ∞) (t, ω)
  have hs : ‖(s : lp (fun _ : ℕ × Ω => ℝ × ℝ) ∞)‖ = ‖s‖ := rfl
  rw [hs] at h
  exact ⟨by rw [← Real.norm_eq_abs]; exact (norm_fst_le _).trans h,
    by rw [← Real.norm_eq_abs]; exact (norm_snd_le _).trans h⟩

/-- Every `s ∈ L` is an adapted bounded plan. -/
theorem indAdapted (s : IndustrySpace ℱ) : IndustryAdapted ℱ (indQ s) (indI s) :=
  ⟨fun t => s.2 t, ‖s‖, abs_ind_le s⟩

/-- The element of `L` given by an adapted bounded plan `(q, I)`. -/
noncomputable def indMk {q I : ℕ → Ω → ℝ} (h : IndustryAdapted ℱ q I) : IndustrySpace ℱ :=
  ⟨⟨fun p => (q p.1 p.2, I p.1 p.2), memℓp_infty ⟨max h.2.choose 0, by
    rintro _ ⟨p, rfl⟩
    have hb := h.2.choose_spec p.1 p.2
    exact (max_le (by rw [Real.norm_eq_abs]; exact hb.1)
      (by rw [Real.norm_eq_abs]; exact hb.2)).trans (le_max_left _ _)⟩⟩, fun t => h.1 t⟩

/-- Components of `indMk`. -/
@[simp] theorem indQ_mk {q I : ℕ → Ω → ℝ} (h : IndustryAdapted ℱ q I) : indQ (indMk h) = q := rfl

/-- Components of `indMk`. -/
@[simp] theorem indI_mk {q I : ℕ → Ω → ℝ} (h : IndustryAdapted ℱ q I) : indI (indMk h) = I := rfl

/-- The consumption set `X = L₊` of the synthetic consumer (p. 491). -/
def indX (ℱ : Filtration ℕ mΩ) : Unit → Set (IndustrySpace ℱ) :=
  fun _ => {s | ∀ t ω, 0 ≤ indQ s t ω ∧ 0 ≤ indI s t ω}

/-- The synthetic consumer's utility `u(q, I) = E Σ (1 + r)⁻ᵗ [U(q_t, z_t) − I_t]` (p. 491). -/
noncomputable def indU (μ : Measure Ω) (r : ℝ) (D : ℝ → ℝ → ℝ) (z : ℕ → Ω → ℝ) :
    Unit → IndustrySpace ℱ → ℝ :=
  fun _ s => industrySurplus μ r D z (indQ s) (indI s)

/-- The production set `Y ⊆ L` of (1). -/
def indY (ℱ : Filtration ℕ mΩ) (c : ℝ → ℝ) (δ k0 : ℝ) : Unit → Set (IndustrySpace ℱ) :=
  fun _ => {s | (indQ s, indI s) ∈ IndustryTech ℱ c δ k0}

variable {μ : Measure Ω} {D : ℝ → ℝ → ℝ} {zlo zhi : ℝ} {z : ℕ → Ω → ℝ} {c : ℝ → ℝ}
  {δ k0 r : ℝ}

/-- `|E Σ (1 + r)⁻ᵗ g_t| ≤ B/(1 − (1 + r)⁻¹)` for `|g| ≤ B`. -/
theorem industryPV_abs_le [IsProbabilityMeasure μ] (hr : 0 < r) {g : ℕ → Ω → ℝ} {B : ℝ}
    (hm : ∀ t, AEStronglyMeasurable (g t) μ) (hB : ∀ t ω, |g t ω| ≤ B) :
    |industryPV μ r g| ≤ B * (1 - (1 + r)⁻¹)⁻¹ := by
  obtain ⟨h0, h1⟩ := industry_disc hr
  have hg : IndustryBdd μ g := ⟨hm, B, hB⟩
  have hc : IndustryBdd μ fun (_ : ℕ) (_ : Ω) => B :=
    ⟨fun _ => aestronglyMeasurable_const, |B|, fun _ _ => le_rfl⟩
  have hcn : IndustryBdd μ fun (_ : ℕ) (_ : Ω) => -B :=
    ⟨fun _ => aestronglyMeasurable_const, |-B|, fun _ _ => le_rfl⟩
  have hconst : ∀ a : ℝ, industryPV μ r (fun _ _ => a) = a * (1 - (1 + r)⁻¹)⁻¹ := fun a => by
    unfold industryPV
    simp only [integral_const, probReal_univ, one_smul]
    rw [tsum_mul_right, tsum_geometric_of_lt_one h0 h1, mul_comm]
  rw [abs_le]
  constructor
  · have := industryPV_mono hr hcn hg fun t ω => by linarith [neg_abs_le (g t ω), hB t ω]
    rw [hconst] at this
    linarith
  · have := industryPV_mono hr hg hc fun t ω => (le_abs_self _).trans (hB t ω)
    rwa [hconst] at this

/-- The surplus integrand of `s ∈ X` is bounded and measurable. -/
theorem ind_surplus_bdd (hD : IndustryDemand D zlo zhi) (hz : IndustryShocks ℱ z zlo zhi)
    {s : IndustrySpace ℱ} (hs : s ∈ indX ℱ ()) :
    IndustryBdd μ fun t ω => surplusFn D (indQ s t ω) (z t ω) - indI s t ω :=
  industry_surplus_bdd hD hz (indAdapted s) fun t ω => (hs t ω).1

/-- `u` is concave on `X`. -/
theorem ind_utility_concave [IsProbabilityMeasure μ] (hD : IndustryDemand D zlo zhi)
    (hz : IndustryShocks ℱ z zlo zhi) (hr : 0 < r) {s s' : IndustrySpace ℱ}
    (hs : s ∈ indX ℱ ()) (hs' : s' ∈ indX ℱ ()) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a * indU μ r D z () s + (1 - a) * indU μ r D z () s' ≤
      indU μ r D z () (a • s + (1 - a) • s') := by
  have hm : a • s + (1 - a) • s' ∈ indX ℱ () := fun t ω => by
    rw [indQ_combo, indI_combo]
    exact ⟨add_nonneg (mul_nonneg ha0 (hs t ω).1) (mul_nonneg (by linarith) (hs' t ω).1),
      add_nonneg (mul_nonneg ha0 (hs t ω).2) (mul_nonneg (by linarith) (hs' t ω).2)⟩
  have hb := ind_surplus_bdd (μ := μ) hD hz hs
  have hb' := ind_surplus_bdd (μ := μ) hD hz hs'
  have hbm := ind_surplus_bdd (μ := μ) hD hz hm
  unfold indU industrySurplus
  rw [← industryPV_const_mul, ← industryPV_const_mul,
    ← industryPV_add hr (hb.const_mul a) (hb'.const_mul (1 - a))]
  refine industryPV_mono hr ((hb.const_mul a).add (hb'.const_mul (1 - a))) hbm fun t ω => ?_
  rw [indQ_combo, indI_combo]
  set m := a * indQ s t ω + (1 - a) * indQ s' t ω
  have hm0 : 0 ≤ m := (hm t ω).1
  have h1 := surplusFn_le hD hm0 (hs t ω).1 (hz.mem t ω)
  have h2 := surplusFn_le hD hm0 (hs' t ω).1 (hz.mem t ω)
  have hcomb : a * (D m (z t ω) * (indQ s t ω - m)) +
      (1 - a) * (D m (z t ω) * (indQ s' t ω - m)) = 0 := by
    simp only [m]; ring
  nlinarith [mul_le_mul_of_nonneg_left h1 ha0,
    mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ 1 - a)]

/-- The interior point of `Y` (Assumption 15.5): `q ≡ k₀/2`, `I ≡ k₀ c(1)`, and every `s` within
`ε = min(k₀/8, k₀c(1)/4)` of it lies in `Y` (its capital stays above `3k₀/4`). -/
theorem industry_interior (hc : IndustryCost c δ) (hk0 : 0 < k0) :
    ∃ s0 : IndustrySpace ℱ, ∃ ε > 0, Metric.ball s0 ε ⊆ indY ℱ c δ k0 () := by
  have h1 := hc.one_pos
  have hA0 : IndustryAdapted ℱ (fun _ _ => k0 / 2) (fun _ _ => k0 * c 1) :=
    ⟨fun _ => ⟨stronglyMeasurable_const, stronglyMeasurable_const⟩, max (k0 / 2) (k0 * c 1),
      fun _ _ => ⟨by rw [abs_of_pos (by positivity)]; exact le_max_left _ _,
        by rw [abs_of_pos (by positivity)]; exact le_max_right _ _⟩⟩
  refine ⟨indMk hA0, min (k0 / 8) (k0 * c 1 / 4), lt_min (by positivity) (by positivity),
    fun s hs => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have hε1 := min_le_left (k0 / 8) (k0 * c 1 / 4)
  have hε2 := min_le_right (k0 / 8) (k0 * c 1 / 4)
  have hq : ∀ t ω, |indQ s t ω - k0 / 2| < min (k0 / 8) (k0 * c 1 / 4) := fun t ω =>
    lt_of_le_of_lt (abs_ind_le (s - indMk hA0) t ω).1 hs
  have hI : ∀ t ω, |indI s t ω - k0 * c 1| < min (k0 / 8) (k0 * c 1 / 4) := fun t ω =>
    lt_of_le_of_lt (abs_ind_le (s - indMk hA0) t ω).2 hs
  have hnn : ∀ t ω, 0 ≤ indQ s t ω ∧ 0 ≤ indI s t ω := fun t ω => by
    have := abs_lt.1 (hq t ω)
    have := abs_lt.1 (hI t ω)
    constructor <;> linarith
  -- the generated capital stays above `3k₀/4`
  have hcap : ∀ t ω, 3 * k0 / 4 ≤ industryCap c k0 (indI s) t ω := by
    intro t
    induction t with
    | zero => intro ω; change 3 * k0 / 4 ≤ k0; linarith
    | succ t ih =>
      intro ω
      have hK : 0 < 3 * k0 / 4 := by positivity
      have hge : c 1 ≤ indI s t ω / (3 * k0 / 4) := by
        rw [le_div_iff₀ hK]
        have := abs_lt.1 (hI t ω)
        linarith
      change 3 * k0 / 4 ≤ industryCap c k0 (indI s) t ω *
        industryH c (indI s t ω / industryCap c k0 (indI s) t ω)
      calc 3 * k0 / 4 ≤ 3 * k0 / 4 * industryH c (indI s t ω / (3 * k0 / 4)) :=
            le_mul_of_one_le_right hK.le (one_le_industryH hc hge)
        _ ≤ _ := industryH_persp_mono hc hK (ih ω) (hnn t ω).2
  refine industryTech_of_cap hc hk0 (indAdapted s) hnn fun t ω => ?_
  have := abs_lt.1 (hq t ω)
  linarith [hcap t ω]

/-- **Exercise 16.4(d)**: `(X, u)` satisfies Assumptions 15.1–15.3 and `Y` satisfies 15.4 and
15.5. -/
theorem ex_16_4d [IsProbabilityMeasure μ] (hD : IndustryDemand D zlo zhi) (hc : IndustryCost c δ)
    (hz : IndustryShocks ℱ z zlo zhi) (hr : 0 < r) (hk0 : 0 < k0) :
    Assumption15_1 (indX ℱ) ∧ Assumption15_2 (indX ℱ) (indU μ r D z) ∧
      Assumption15_3 (indX ℱ) (indU μ r D z) ∧ Assumption15_4 (indY ℱ c δ k0) ∧
        Assumption15_5 (IndustrySpace ℱ) (indY ℱ c δ k0) := by
  refine ⟨fun _ s hs s' hs' a b ha hb hab t ω => ?_, fun _ s hs s' hs' hlt a ha0 ha1 => ?_,
    fun _ => ?_, ?_, Or.inl ?_⟩
  · rw [indQ_combo, indI_combo]
    exact ⟨add_nonneg (mul_nonneg ha (hs t ω).1) (mul_nonneg hb (hs' t ω).1),
      add_nonneg (mul_nonneg ha (hs t ω).2) (mul_nonneg hb (hs' t ω).2)⟩
  · have := ind_utility_concave (μ := μ) hD hz hr hs hs' ha0.le ha1.le
    nlinarith
  · -- Lipschitz continuity: `|u(s) − u(s′)| ≤ (D̄ + 1) ‖s − s′‖ / (1 − (1 + r)⁻¹)`
    set K := (D 0 zhi + 1) * (1 - (1 + r)⁻¹)⁻¹
    have hD0 : 0 ≤ D 0 zhi := (hD.pos_zero zhi ⟨hD.zlo_le, le_rfl⟩).le
    have hK : 0 < K := mul_pos (by linarith) (inv_pos.2 (by linarith [(industry_disc hr).2]))
    rw [Metric.continuousOn_iff]
    intro s hs ε hε
    refine ⟨ε / K, div_pos hε hK, fun s' hs' hd => ?_⟩
    rw [dist_eq_norm] at hd
    rw [Real.dist_eq]
    have hb := ind_surplus_bdd (μ := μ) hD hz hs
    have hb' := ind_surplus_bdd (μ := μ) hD hz hs'
    unfold indU industrySurplus
    rw [← industryPV_sub hr hb' hb]
    calc |industryPV μ r _| ≤ (D 0 zhi + 1) * ‖s' - s‖ * (1 - (1 + r)⁻¹)⁻¹ := by
          refine industryPV_abs_le hr (hb'.sub hb).1 fun t ω => ?_
          have hl := surplusFn_lipschitz hD (hs t ω).1 (hs' t ω).1 (hz.mem t ω)
          have hq := (abs_ind_le (s' - s) t ω).1
          have hI := (abs_ind_le (s' - s) t ω).2
          rw [indQ_sub] at hq
          rw [indI_sub] at hI
          calc |surplusFn D (indQ s' t ω) (z t ω) - indI s' t ω -
                (surplusFn D (indQ s t ω) (z t ω) - indI s t ω)|
              ≤ |surplusFn D (indQ s' t ω) (z t ω) - surplusFn D (indQ s t ω) (z t ω)| +
                  |indI s' t ω - indI s t ω| := by
                rw [show surplusFn D (indQ s' t ω) (z t ω) - indI s' t ω -
                  (surplusFn D (indQ s t ω) (z t ω) - indI s t ω) =
                  (surplusFn D (indQ s' t ω) (z t ω) - surplusFn D (indQ s t ω) (z t ω)) -
                    (indI s' t ω - indI s t ω) by ring]
                exact abs_sub _ _
            _ ≤ D 0 zhi * ‖s' - s‖ + ‖s' - s‖ :=
                add_le_add (hl.trans (mul_le_mul_of_nonneg_left hq hD0)) hI
            _ = (D 0 zhi + 1) * ‖s' - s‖ := by ring
      _ = K * ‖s' - s‖ := by ring
      _ < K * (ε / K) := mul_lt_mul_of_pos_left hd hK
      _ = ε := by field_simp
  · unfold Assumption15_4 indY
    rw [sg_aggTech_unit]
    intro s hs s' hs' a b ha hb hab
    exact industryTech_combo hc hk0 hs hs' ha hb hab
  · unfold indY
    rw [sg_aggTech_unit]
    obtain ⟨s0, ε, hε, hball⟩ := industry_interior (ℱ := ℱ) hc hk0
    exact ⟨s0, mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨ε, hε, hball⟩)⟩

/-- The direction `(1, 0)`: one more unit of output in every period and state. -/
noncomputable def indE (ℱ : Filtration ℕ mΩ) : IndustrySpace ℱ :=
  indMk (q := fun _ _ => 1) (I := fun _ _ => 0)
    ⟨fun _ => ⟨stronglyMeasurable_const, stronglyMeasurable_const⟩, 1, fun _ _ => by simp⟩

/-- Components of `e`. -/
theorem indQ_indE (t : ℕ) (ω : Ω) : indQ (indE ℱ) t ω = 1 := rfl

/-- Components of `e`. -/
theorem indI_indE (t : ℕ) (ω : Ω) : indI (indE ℱ) t ω = 0 := rfl

/-- **Strict monotonicity in output**: `u(s + εe) > u(s)` for `s ∈ X`, `ε > 0`. -/
theorem ind_utility_lt_add [IsProbabilityMeasure μ] (hD : IndustryDemand D zlo zhi)
    (hz : IndustryShocks ℱ z zlo zhi) (hr : 0 < r) {s : IndustrySpace ℱ} (hs : s ∈ indX ℱ ())
    {ε : ℝ} (hε : 0 < ε) : indU μ r D z () s < indU μ r D z () (s + ε • indE ℱ) := by
  have hm : s + ε • indE ℱ ∈ indX ℱ () := fun t ω => by
    rw [indQ_add, indI_add, indQ_smul, indI_smul]
    rw [indQ_indE, indI_indE, mul_one, mul_zero, add_zero]
    exact ⟨add_nonneg (hs t ω).1 hε.le, (hs t ω).2⟩
  obtain ⟨h0, h1⟩ := industry_disc hr
  set B := ‖s‖
  set η := ε * D (B + ε) zlo
  have hη : 0 < η := mul_pos hε (D_pos hD (by positivity) ⟨le_rfl, hD.zlo_le⟩)
  have hb := ind_surplus_bdd (μ := μ) hD hz hs
  have hbm := ind_surplus_bdd (μ := μ) hD hz hm
  have hc : IndustryBdd μ fun (_ : ℕ) (_ : Ω) => η :=
    ⟨fun _ => aestronglyMeasurable_const, |η|, fun _ _ => le_rfl⟩
  have hle := industryPV_mono hr (hb.add hc) hbm fun t ω => by
    rw [indQ_add, indI_add, indQ_smul, indI_smul]
    rw [indQ_indE, indI_indE, mul_one, mul_zero, add_zero]
    have hq0 := (hs t ω).1
    have hqB : indQ s t ω ≤ B := (le_abs_self _).trans (abs_ind_le s t ω).1
    have hzt := hz.mem t ω
    have h := surplusFn_le hD (by linarith : 0 ≤ indQ s t ω + ε) hq0 hzt
    have hD1 : D (B + ε) zlo ≤ D (indQ s t ω + ε) (z t ω) :=
      ((hD.antiQ zlo ⟨le_rfl, hD.zlo_le⟩).antitoneOn (mem_Ici.2 (by linarith))
        (mem_Ici.2 (by positivity)) (by linarith)).trans
        ((hD.monoZ _ (by linarith)).monotoneOn ⟨le_rfl, hD.zlo_le⟩ hzt hzt.1)
    have : η ≤ ε * D (indQ s t ω + ε) (z t ω) := mul_le_mul_of_nonneg_left hD1 hε.le
    nlinarith
  rw [industryPV_add hr hb hc] at hle
  have hconst : 0 < industryPV μ r (fun (_ : ℕ) (_ : Ω) => η) := by
    unfold industryPV
    simp only [integral_const, probReal_univ, one_smul]
    rw [tsum_mul_right, tsum_geometric_of_lt_one h0 h1]
    exact mul_pos (inv_pos.2 (by linarith)) hη
  unfold indU industrySurplus
  linarith

/-- **Local nonsatiation** of the synthetic consumer. -/
theorem ind_localNonsatiation [IsProbabilityMeasure μ] (hD : IndustryDemand D zlo zhi)
    (hz : IndustryShocks ℱ z zlo zhi) (hr : 0 < r) :
    LocalNonsatiation (indX ℱ) (indU μ r D z) := by
  intro i s hs
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  refine ⟨fun n => s + (1 / ((n : ℝ) + 1)) • indE ℱ, fun n t ω => ?_, ?_,
    fun n => ind_utility_lt_add hD hz hr hs (hpos n)⟩
  · rw [indQ_add, indI_add, indQ_smul, indI_smul]
    rw [indQ_indE, indI_indE, mul_one, mul_zero, add_zero]
    exact ⟨add_nonneg (hs t ω).1 (hpos n).le, (hs t ω).2⟩
  · have : Tendsto (fun n : ℕ => s + (1 / ((n : ℝ) + 1)) • indE ℱ) atTop
        (𝓝 (s + (0 : ℝ) • indE ℱ)) :=
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.smul tendsto_const_nhds)
    simpa using this

/-- The price functional `φ_p(q, I) = E Σ (1 + r)⁻ᵗ [p_t q_t − I_t]` of a bounded measurable
price process, as a continuous linear functional on `L`. -/
noncomputable def indPriceDual [IsProbabilityMeasure μ] (hr : 0 < r) {p : ℕ → Ω → ℝ}
    (hp : IndustryBdd μ p) : StrongDual ℝ (IndustrySpace ℱ) :=
  LinearMap.mkContinuous
    { toFun := fun s => industryProfit μ r p (indQ s) (indI s)
      map_add' := fun s s' => by
        unfold industryProfit
        rw [← industryPV_add hr (industry_profit_bdd hp (indAdapted s))
          (industry_profit_bdd hp (indAdapted s'))]
        congr 1
        funext t ω
        rw [indQ_add, indI_add]
        ring
      map_smul' := fun a s => by
        unfold industryProfit
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← industryPV_const_mul]
        congr 1
        funext t ω
        rw [indQ_smul, indI_smul]
        ring }
    ((hp.2.choose + 1) * (1 - (1 + r)⁻¹)⁻¹) fun s => by
      rw [Real.norm_eq_abs]
      have hB := hp.2.choose_spec
      refine (industryPV_abs_le hr (B := (hp.2.choose + 1) * ‖s‖)
        (industry_profit_bdd hp (indAdapted s)).1 fun t ω => ?_).trans
        (le_of_eq (by ring))
      have h1 := (abs_ind_le s t ω).1
      have h2 := (abs_ind_le s t ω).2
      calc |p t ω * indQ s t ω - indI s t ω| ≤ |p t ω| * |indQ s t ω| + |indI s t ω| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ hp.2.choose * ‖s‖ + ‖s‖ :=
            add_le_add (mul_le_mul (hB t ω) h1 (abs_nonneg _) ((abs_nonneg _).trans (hB t ω)))
              h2
        _ = (hp.2.choose + 1) * ‖s‖ := by ring

/-- `φ_p` evaluates to expected discounted profit. -/
theorem indPriceDual_apply [IsProbabilityMeasure μ] (hr : 0 < r) {p : ℕ → Ω → ℝ}
    (hp : IndustryBdd μ p) (s : IndustrySpace ℱ) :
    indPriceDual hr hp s = industryProfit μ r p (indQ s) (indI s) := rfl

/-- Plans of `Y` are in `X = L₊`. -/
theorem indY_subset_indX {s : IndustrySpace ℱ} (hs : s ∈ indY ℱ c δ k0 ()) : s ∈ indX ℱ () :=
  fun t ω => hs.2.1 t ω

/-- **Exercise 16.4(e)** via the welfare framework: an industry equilibrium `(q, I, p)` gives the
competitive equilibrium `((q, I), (q, I), φ_p)` of the synthetic economy `(X, u, Y)`. -/
theorem ex_16_4e_competitiveEq [IsProbabilityMeasure μ] (hD : IndustryDemand D zlo zhi)
    (hz : IndustryShocks ℱ z zlo zhi) (hr : 0 < r) {q I p : ℕ → Ω → ℝ}
    (hE : IndustryEquilibrium μ ℱ D z c δ k0 r q I p) :
    ∃ hp : IndustryBdd μ p, CompetitiveEq (indX ℱ) (indU μ r D z) (indY ℱ c δ k0)
      (fun _ => indMk hE.1.1) (fun _ => indMk hE.1.1) (indPriceDual hr hp) := by
  obtain ⟨hY, -, hI2, hI3⟩ := hE
  have hA : IndustryAdapted ℱ q I := hY.1
  have hq := fun t ω => (hY.2.1 t ω).1
  have hpB : IndustryBdd μ p := by
    have := (industry_D_bdd (μ := μ) hD hz hA hq).1
    have he : p = fun t ω => D (q t ω) (z t ω) := funext fun t => funext fun ω => hI2 t ω
    rwa [he]
  set s := indMk hA
  have hsY : s ∈ indY ℱ c δ k0 () := hY
  refine ⟨hpB, sg_feasible_unit.2 ⟨indY_subset_indX hsY, hsY, rfl⟩, fun _ w hw hφ => ?_,
    fun _ w hw => ?_⟩
  · rw [indPriceDual_apply, indPriceDual_apply] at hφ
    have hb := ind_surplus_bdd (μ := μ) hD hz hw
    have hbs := ind_surplus_bdd (μ := μ) hD hz (indY_subset_indX hsY)
    have hP := industry_profit_bdd hpB (indAdapted w)
    have hPs := industry_profit_bdd hpB (indAdapted s)
    have hmono := industryPV_mono hr hb (hbs.add (hP.sub hPs)) fun t ω => by
      have := surplusFn_le hD (hq t ω) (hw t ω).1 (hz.mem t ω)
      simp only [s, indQ_mk, indI_mk]
      rw [← hI2 t ω] at this
      linarith
    rw [industryPV_add hr hbs (hP.sub hPs), industryPV_sub hr hP hPs] at hmono
    unfold industryProfit at hφ
    change industrySurplus μ r D z (indQ w) (indI w) ≤ industrySurplus μ r D z (indQ s) (indI s)
    unfold industrySurplus
    linarith
  · rw [indPriceDual_apply, indPriceDual_apply]
    exact hI3 _ _ hw

/-- **Exercise 16.4(e), part (b)** via Theorem 15.3: an industry equilibrium allocation is
surplus maximising. -/
theorem ex_16_4e_b [IsProbabilityMeasure μ] (hD : IndustryDemand D zlo zhi)
    (hz : IndustryShocks ℱ z zlo zhi) (hr : 0 < r) {q I p : ℕ → Ω → ℝ}
    (hE : IndustryEquilibrium μ ℱ D z c δ k0 r q I p) :
    IndustrySurplusMax μ ℱ D z c δ k0 r q I := by
  obtain ⟨hp, hCE⟩ := ex_16_4e_competitiveEq hD hz hr hE
  have hPO := theorem_15_3 (ind_localNonsatiation hD hz hr) hCE
  refine ⟨hE.1, fun q' I' hY' => ?_⟩
  have hA' : IndustryAdapted ℱ q' I' := hY'.1
  have hw : indMk hA' ∈ indY ℱ c δ k0 () := hY'
  by_contra hlt
  push Not at hlt
  exact hPO.2 ⟨fun _ => indMk hA', fun _ => indMk hA',
    sg_feasible_unit.2 ⟨indY_subset_indX hw, hw, rfl⟩, fun _ => hlt.le, (), hlt⟩

/-- A surplus maximum is **Pareto optimal** in the synthetic economy (p. 491: "clearly"). -/
theorem indParetoOptimal_of_surplusMax {q I : ℕ → Ω → ℝ}
    (hS : IndustrySurplusMax μ ℱ D z c δ k0 r q I) :
    ParetoOptimal (indX ℱ) (indU μ r D z) (indY ℱ c δ k0) (fun _ => indMk hS.1.1)
      (fun _ => indMk hS.1.1) := by
  have hsY : indMk hS.1.1 ∈ indY ℱ c δ k0 () := hS.1
  refine ⟨sg_feasible_unit.2 ⟨indY_subset_indX hsY, hsY, rfl⟩, ?_⟩
  rintro ⟨x', y', hF', -, i, hi⟩
  obtain ⟨-, hy', he⟩ := sg_feasible_unit.1 hF'
  have h := hS.2 _ _ (show (indQ (y' ()), indI (y' ())) ∈ IndustryTech ℱ c δ k0 from hy')
  change industrySurplus μ r D z q I < industrySurplus μ r D z (indQ (x' ())) (indI (x' ())) at hi
  rw [he] at hi
  linarith

/-- **Exercise 16.4(e), part (c)** via Theorem 15.4 and its Remark: for a surplus maximum there
is a nonzero continuous linear price `φ` on `L` supporting it, and with it the allocation is a
competitive equilibrium of the synthetic economy (the interior point of `Y` is a cheaper point).
Nothing here identifies `φ` with the (I2) price functional `φ_p`; see the module docstring. -/
theorem ex_16_4e_c [IsProbabilityMeasure μ] (hD : IndustryDemand D zlo zhi)
    (hc : IndustryCost c δ) (hz : IndustryShocks ℱ z zlo zhi) (hr : 0 < r) (hk0 : 0 < k0)
    {q I : ℕ → Ω → ℝ} (hS : IndustrySurplusMax μ ℱ D z c δ k0 r q I) :
    ∃ φ : StrongDual ℝ (IndustrySpace ℱ), φ ≠ 0 ∧
      SupportsAllocation (indX ℱ) (indU μ r D z) (indY ℱ c δ k0) (fun _ => indMk hS.1.1)
        (fun _ => indMk hS.1.1) φ ∧
      CompetitiveEq (indX ℱ) (indU μ r D z) (indY ℱ c δ k0) (fun _ => indMk hS.1.1)
        (fun _ => indMk hS.1.1) φ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ex_16_4d (μ := μ) hD hc hz hr hk0
  have hPO := indParetoOptimal_of_surplusMax hS
  set s := indMk hS.1.1
  have hsX : s ∈ indX ℱ () := indY_subset_indX hS.1
  obtain ⟨φ, hφ0, hsup⟩ := theorem_15_4 h1 h2 h3 h4 h5 hPO (h := ())
    (xhat := s + (1 : ℝ) • indE ℱ) (by
      intro t ω
      rw [indQ_add, indI_add, indQ_smul, indI_smul]
      rw [indQ_indE, indI_indE, mul_one, mul_zero, add_zero]
      exact ⟨add_nonneg (hsX t ω).1 zero_le_one, (hsX t ω).2⟩)
    (ind_utility_lt_add hD hz hr hsX one_pos)
  refine ⟨φ, hφ0, hsup, remark_cheaper_point h1 h3 hPO.1 hsup fun _ => ?_⟩
  -- the cheaper point: an interior point of `Y`
  obtain ⟨s0, ε, hε, hball⟩ := industry_interior (ℱ := ℱ) hc hk0
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ0 (ContinuousLinearMap.ext h)
  set v' := if 0 < φ v then v else -v
  have hv' : 0 < φ v' := by
    simp only [v']
    split_ifs with h
    · exact h
    · rw [φ.map_neg v]
      exact neg_pos.2 (lt_of_le_of_ne (not_lt.1 h) hv)
  have hv'n : 0 < ‖v'‖ := norm_pos_iff.2 fun h => by
    rw [h, φ.map_zero] at hv'; exact lt_irrefl _ hv'
  set w := (ε / (2 * ‖v'‖)) • v'
  have hw : s0 + w ∈ indY ℱ c δ k0 () := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    field_simp
    linarith)
  have hle := hsup.2 () _ hw
  rw [φ.map_add, φ.map_smul, smul_eq_mul] at hle
  have : 0 < ε / (2 * ‖v'‖) * φ v' := mul_pos (by positivity) hv'
  exact ⟨s0, indY_subset_indX (hball (Metric.mem_ball_self hε)), by linarith⟩

end StokeyLucasPrescott.EquilibriumApplications

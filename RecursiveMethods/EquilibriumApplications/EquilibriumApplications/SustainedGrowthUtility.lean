/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.SustainedGrowth
import EquilibriumApplications.SequenceAssumptions

/-!
# Sustained growth: continuity and boundedness of utility on `S_θ` (Exercise 16.3(c)–(d))

SLP §16.3, pp. 486–487. With `S_θ` identified with `ℓ_∞` by `sgOfBdd θ` (module
`SustainedGrowth`), the utility of a consumption path `x ∈ S_θ` is
`u(x) = Σ_t βᵗ U(x_t)` (`sgUtility`), and continuity is continuity in `‖·‖_θ`, i.e. of
`w ↦ u(sgOfBdd θ w)` on `ℓ_∞`.

* **Exercise 16.3(c)** (`ex_16_3c`): if `X = S_θ⁺` (`sgSθplus`) and `U : ℝ₊ → ℝ` is continuous
  and bounded, `u` is continuous in `‖·‖_θ`.
* `sgCRRA σ`: `U(c) = (c^{1−σ} − 1)/(1 − σ)` for `σ ≠ 1` and `U = log` for `σ = 1`; it is
  continuous, strictly increasing and concave on `(0, ∞)` for `σ > 0` (`sgCRRA_continuousOn`,
  `sgCRRA_strictMonoOn`, `sgCRRA_concaveOn`), unbounded above if `σ ≤ 1`
  (`sgCRRA_not_bddAbove`) and unbounded below if `σ ≥ 1` (`sgCRRA_not_bddBelow`) (p. 486).
* `sgCRRA_scale`: `U(λc) = λ^{1−σ} U(c) + U(λ)`; hence (`sgUtility_split`), with
  `ρ = βθ^{1−σ}`, `u(θᵗ w_t) = Σ_t ρᵗ U(w_t) + K` where `K = Σ_t βᵗ U(θᵗ)`.
* `sgXa θ a` (the corrected `X = {x ∈ S_θ⁺ : x_t ≥ a θᵗ}`) and `sgXPrinted θ a` (the printed
  `X = {x ∈ S_θ : inf_t |θ⁻ᵗ x_t| ≥ a}`).
* **Exercise 16.3(d), corrected**, for CRRA `U` with `σ > 0`, `0 ≤ β`, `βθ^{1−σ} < 1`, `a > 0`:
  `u` is finite on `X` (`ex_16_3d_summable`), bounded on norm-bounded subsets of `X`
  (`ex_16_3d_bounded_on_balls`), and continuous on `X` (`ex_16_3d_continuousOn`); for `σ > 1`
  it is bounded on `X` (`ex_16_3d_bounded_of_one_lt`).

**Corrections.**
* Ex 16.3(d): the printed `X` is not a subset of `S_θ⁺` (`ex_16_3d_printed_not_nonneg`: the
  constant path `−a` lies in it), and CRRA `U` is undefined there; `X ⊆ S_θ⁺` is needed (the
  manual uses it silently).
* Ex 16.3(d): "`u` is bounded on `X`" is **false** for `σ ≤ 1`: with `θ = 1` (so
  `βθ^{1−σ} = β < 1`), `u(b𝟙) = U(b)/(1 − β) → ∞` as `b → ∞`
  (`ex_16_3d_counterexample`; for `σ = ½`, `u(b𝟙) = (2√b − 2)/(1 − β)`,
  `ex_16_3d_counterexample_half`). The manual's "bound" depends on `b = ‖x‖_θ`, so it proves only
  finiteness and boundedness on bounded sets, both proved here; the claim holds for `σ > 1`.
* The manual's continuity argument for (d) (bounds taken globally) is replaced by the local
  bounds above; continuity holds for every `σ > 0`.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

/-- The utility `u(x) = Σ_t βᵗ U(x_t)` of a path `x` (p. 486). -/
noncomputable def sgUtility (β : ℝ) (U : ℝ → ℝ) (x : ℕ → ℝ) : ℝ := ∑' t, β ^ t * U (x t)

/-- The positive cone `S_θ⁺`, in `ℓ_∞` coordinates. -/
def sgSθplus (θ : ℝ) : Set (BddSeq ℝ) := {w | ∀ t, 0 ≤ sgOfBdd θ w t}

/-- **Exercise 16.3(c)**: if `U : ℝ₊ → ℝ` is continuous and bounded, `u` is continuous on
`X = S_θ⁺` in the norm `‖·‖_θ`. -/
theorem ex_16_3c {β θ D : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {U : ℝ → ℝ}
    (hUc : ContinuousOn U (Ici 0)) (hUb : ∀ c, 0 ≤ c → |U c| ≤ D) :
    ContinuousOn (fun w => sgUtility β U (sgOfBdd θ w)) (sgSθplus θ) := by
  refine continuousOn_tsum (u := fun t => D * β ^ t)
    (f := fun t w => β ^ t * U (sgOfBdd θ w t)) (fun t => ?_)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_left D) (fun t w hw => ?_)
  · refine continuousOn_const.mul (hUc.comp ?_ fun w hw => hw t)
    exact (continuous_const.mul (continuous_seq_coord t)).continuousOn
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
    exact mul_le_mul_of_nonneg_right (hUb _ (hw t)) (pow_nonneg hβ0 t)

/-- The CRRA utility `U(c) = (c^{1−σ} − 1)/(1 − σ)`, read as `log c` for `σ = 1` (p. 486). -/
noncomputable def sgCRRA (σ c : ℝ) : ℝ :=
  if σ = 1 then Real.log c else (c ^ (1 - σ) - 1) / (1 - σ)

/-- CRRA for `σ ≠ 1`. -/
theorem sgCRRA_of_ne {σ : ℝ} (hσ : σ ≠ 1) (c : ℝ) :
    sgCRRA σ c = (c ^ (1 - σ) - 1) / (1 - σ) := by
  simp [sgCRRA, hσ]

/-- CRRA for `σ = 1` is `log`. -/
theorem sgCRRA_one (c : ℝ) : sgCRRA 1 c = Real.log c := by simp [sgCRRA]

/-- **Scaling**: `U(λc) = λ^{1−σ} U(c) + U(λ)` for `λ, c > 0`. -/
theorem sgCRRA_scale {σ l c : ℝ} (hl : 0 < l) (hc : 0 < c) :
    sgCRRA σ (l * c) = l ^ (1 - σ) * sgCRRA σ c + sgCRRA σ l := by
  by_cases hσ : σ = 1
  · subst hσ
    simp only [sgCRRA_one, sub_self, Real.rpow_zero, one_mul]
    rw [Real.log_mul hl.ne' hc.ne', add_comm]
  · rw [sgCRRA_of_ne hσ, sgCRRA_of_ne hσ, sgCRRA_of_ne hσ, Real.mul_rpow hl.le hc.le]
    have : (1 - σ) ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    field_simp
    ring

/-- CRRA is continuous on `(0, ∞)`. -/
theorem sgCRRA_continuousOn (σ : ℝ) : ContinuousOn (sgCRRA σ) (Ioi 0) := by
  by_cases hσ : σ = 1
  · subst hσ
    have : sgCRRA 1 = Real.log := funext sgCRRA_one
    rw [this]
    exact Real.continuousOn_log.mono fun x hx => ne_of_gt hx
  · have : sgCRRA σ = fun c => (c ^ (1 - σ) - 1) / (1 - σ) := funext (sgCRRA_of_ne hσ)
    rw [this]
    exact ((continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)).sub
      continuousOn_const).div_const _

/-- CRRA is strictly increasing on `(0, ∞)` for `σ > 0`. -/
theorem sgCRRA_strictMonoOn {σ : ℝ} (hσ : 0 < σ) : StrictMonoOn (sgCRRA σ) (Ioi 0) := by
  intro x hx y hy hxy
  by_cases h1 : σ = 1
  · subst h1
    simp only [sgCRRA_one]
    exact Real.log_lt_log hx hxy
  · rw [sgCRRA_of_ne h1, sgCRRA_of_ne h1]
    rcases lt_or_gt_of_ne h1 with h | h
    · have hp : 0 < 1 - σ := by linarith
      have := Real.rpow_lt_rpow (le_of_lt hx) hxy hp
      exact div_lt_div_of_pos_right (by linarith) hp
    · have hp : 1 - σ < 0 := by linarith
      have := Real.rpow_lt_rpow_of_neg hx hxy hp
      exact (div_lt_div_right_of_neg hp).2 (by linarith)

/-- `x ↦ x^p` is convex on `(0, ∞)` for `p ≤ 0` (via `x^p = exp(p log x)`). -/
theorem sg_convexOn_rpow_nonpos {p : ℝ} (hp : p ≤ 0) : ConvexOn ℝ (Ioi 0) fun x : ℝ => x ^ p := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hxy : 0 < a * x + b * y := by
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have : b = 1 := by linarith
      subst this
      simpa using (show (0 : ℝ) < y from hy)
    · have : 0 ≤ b * y := mul_nonneg hb (le_of_lt hy)
      have : 0 < a * x := mul_pos h hx
      linarith
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hlog
  rw [Real.rpow_def_of_pos hxy, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy]
  calc Real.exp (Real.log (a * x + b * y) * p)
      ≤ Real.exp (a * (Real.log x * p) + b * (Real.log y * p)) := by
        apply Real.exp_le_exp.2
        nlinarith
    _ ≤ a * Real.exp (Real.log x * p) + b * Real.exp (Real.log y * p) := by
        have := convexOn_exp.2 (mem_univ (Real.log x * p)) (mem_univ (Real.log y * p)) ha hb hab
        simpa only [smul_eq_mul] using this

/-- CRRA is concave on `(0, ∞)` for `σ > 0`. -/
theorem sgCRRA_concaveOn {σ : ℝ} (hσ : 0 < σ) : ConcaveOn ℝ (Ioi 0) (sgCRRA σ) := by
  by_cases h1 : σ = 1
  · subst h1
    have : sgCRRA 1 = Real.log := funext sgCRRA_one
    rw [this]
    exact strictConcaveOn_log_Ioi.concaveOn
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, sgCRRA_of_ne h1]
  have hb' : b = 1 - a := by linarith
  subst hb'
  rcases lt_or_gt_of_ne h1 with h | h
  · have hp : 0 < 1 - σ := by linarith
    have hc := ((Real.concaveOn_rpow hp.le (by linarith)).subset Ioi_subset_Ici_self
      (convex_Ioi 0)).2 hx hy ha hb hab
    simp only [smul_eq_mul] at hc
    have hL : a * ((x ^ (1 - σ) - 1) / (1 - σ)) + (1 - a) * ((y ^ (1 - σ) - 1) / (1 - σ)) =
        (a * x ^ (1 - σ) + (1 - a) * y ^ (1 - σ) - 1) / (1 - σ) := by
      field_simp; ring
    rw [hL]
    apply div_le_div_of_nonneg_right _ hp.le
    linarith
  · have hp : 1 - σ < 0 := by linarith
    have hc := (sg_convexOn_rpow_nonpos hp.le).2 hx hy ha hb hab
    simp only [smul_eq_mul] at hc
    have hL : a * ((x ^ (1 - σ) - 1) / (1 - σ)) + (1 - a) * ((y ^ (1 - σ) - 1) / (1 - σ)) =
        (a * x ^ (1 - σ) + (1 - a) * y ^ (1 - σ) - 1) / (1 - σ) := by
      field_simp; ring
    rw [hL, div_le_div_right_of_neg hp]
    linarith

/-- CRRA tends to `+∞` at `+∞` for `σ ≤ 1`. -/
theorem sgCRRA_tendsto_atTop {σ : ℝ} (hσ : σ ≤ 1) : Tendsto (sgCRRA σ) atTop atTop := by
  rcases eq_or_lt_of_le hσ with h | h
  · subst h
    have : sgCRRA 1 = Real.log := funext sgCRRA_one
    rw [this]
    exact Real.tendsto_log_atTop
  · have : sgCRRA σ = fun c => (c ^ (1 - σ) - 1) / (1 - σ) := funext (sgCRRA_of_ne h.ne)
    rw [this]
    simp only [sub_eq_add_neg _ (1 : ℝ)]
    exact (tendsto_atTop_add_const_right _ _ (tendsto_rpow_atTop (by linarith))).atTop_div_const
      (by linarith)

/-- (p. 486) CRRA is unbounded above on `(0, ∞)` for `σ ≤ 1`. -/
theorem sgCRRA_not_bddAbove {σ : ℝ} (hσ : σ ≤ 1) : ¬ BddAbove (sgCRRA σ '' Ioi 0) := by
  rintro ⟨M, hM⟩
  obtain ⟨c, hc1, hc2⟩ :=
    (((sgCRRA_tendsto_atTop hσ).eventually_gt_atTop M).and (eventually_gt_atTop 0)).exists
  exact absurd (hM ⟨c, hc2, rfl⟩) (not_le.2 hc1)

/-- (p. 486) CRRA is unbounded below on `(0, ∞)` for `σ ≥ 1`. -/
theorem sgCRRA_not_bddBelow {σ : ℝ} (hσ : 1 ≤ σ) : ¬ BddBelow (sgCRRA σ '' Ioi 0) := by
  have ht : Tendsto (sgCRRA σ) (𝓝[>] 0) atBot := by
    rcases eq_or_lt_of_le hσ with h | h
    · subst h
      have : sgCRRA 1 = Real.log := funext sgCRRA_one
      rw [this]
      exact Real.tendsto_log_nhdsGT_zero
    · have : sgCRRA σ = fun c => (c ^ (1 - σ) - 1) / (1 - σ) := funext (sgCRRA_of_ne h.ne')
      rw [this]
      simp only [sub_eq_add_neg _ (1 : ℝ)]
      exact (tendsto_atTop_add_const_right _ _
        (tendsto_rpow_neg_nhdsGT_zero (by linarith))).atTop_div_const_of_neg (by linarith)
  rintro ⟨M, hM⟩
  obtain ⟨c, hc1, hc2⟩ := ((ht.eventually_lt_atBot M).and self_mem_nhdsWithin).exists
  exact absurd (hM ⟨c, hc2, rfl⟩) (not_le.2 hc1)

/-- The corrected consumption set `X = {x ∈ S_θ : x_t ≥ a θᵗ ∀t}` of Exercise 16.3(d), in
`ℓ_∞` coordinates. -/
def sgXa (θ a : ℝ) : Set (BddSeq ℝ) := {w | ∀ t, a * θ ^ t ≤ sgOfBdd θ w t}

/-- The consumption set **as printed** in Exercise 16.3(d), `{x ∈ S_θ : inf_t |θ⁻ᵗ x_t| ≥ a}`. -/
def sgXPrinted (θ a : ℝ) : Set (BddSeq ℝ) := {w | ∀ t, a ≤ |θ⁻¹ ^ t * sgOfBdd θ w t|}

/-- `w ∈ X` iff `w_t ≥ a` for all `t`. -/
theorem mem_sgXa_iff {θ a : ℝ} (hθ : 0 < θ) {w : BddSeq ℝ} : w ∈ sgXa θ a ↔ ∀ t, a ≤ w t := by
  refine forall_congr' fun t => ?_
  change a * θ ^ t ≤ θ ^ t * w t ↔ _
  rw [mul_comm (θ ^ t)]
  exact mul_le_mul_iff_left₀ (pow_pos hθ t)

/-- **Correction** to Ex 16.3(d): the printed `X` is not contained in `S_θ⁺` (it contains the
constant path `−a`). -/
theorem ex_16_3d_printed_not_nonneg {θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a) :
    ¬ sgXPrinted θ a ⊆ sgSθplus θ := by
  intro h
  have hmem : sgConst (-a) ∈ sgXPrinted θ a := fun t => by
    change a ≤ |θ⁻¹ ^ t * (θ ^ t * -a)|
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hθ.ne', one_pow, one_mul, abs_neg,
      abs_of_pos ha]
  have := h hmem 0
  change 0 ≤ θ ^ 0 * -a at this
  simp only [pow_zero, one_mul] at this
  linarith

/-- The term identity: `βᵗ U(θᵗ c) = (βθ^{1−σ})ᵗ U(c) + βᵗ U(θᵗ)`. -/
theorem sg_term_split {β θ σ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) (t : ℕ) :
    β ^ t * sgCRRA σ (θ ^ t * c) =
      (β * θ ^ (1 - σ)) ^ t * sgCRRA σ c + β ^ t * sgCRRA σ (θ ^ t) := by
  rw [sgCRRA_scale (pow_pos hθ t) hc, ← Real.rpow_pow_comm hθ.le, mul_pow]
  ring

/-- The constant `K = Σ_t βᵗ U(θᵗ)` is a convergent series. -/
theorem sg_summable_const {β θ σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : 0 < θ)
    (hρ1 : β * θ ^ (1 - σ) < 1) : Summable fun t : ℕ => β ^ t * sgCRRA σ (θ ^ t) := by
  by_cases h1 : σ = 1
  · subst h1
    have hs := (summable_pow_mul_geometric_of_norm_lt_one 1
      (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)).mul_left (Real.log θ)
    refine hs.congr fun t => ?_
    rw [sgCRRA_one, Real.log_pow]
    ring
  · have hρ0 : 0 ≤ β * θ ^ (1 - σ) := mul_nonneg hβ0 (Real.rpow_nonneg hθ.le _)
    have hs := ((summable_geometric_of_lt_one hρ0 hρ1).sub
      (summable_geometric_of_lt_one hβ0 hβ1)).div_const (1 - σ)
    refine hs.congr fun t => ?_
    rw [sgCRRA_of_ne h1, ← Real.rpow_pow_comm hθ.le, mul_pow]
    ring

/-- The constant `K = Σ_t βᵗ U(θᵗ)`. -/
noncomputable def sgConstK (β θ σ : ℝ) : ℝ := ∑' t : ℕ, β ^ t * sgCRRA σ (θ ^ t)

/-- **Splitting the utility**: for `w > 0` with `Σ ρᵗ U(w_t)` convergent (`ρ = βθ^{1−σ}`),
`Σ βᵗ U(θᵗ w_t)` converges and equals `Σ ρᵗ U(w_t) + K`. -/
theorem sgUtility_split {β θ σ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : 0 < θ)
    (hρ1 : β * θ ^ (1 - σ) < 1) {w : BddSeq ℝ} (hw : ∀ t, 0 < w t)
    (hs : Summable fun t => (β * θ ^ (1 - σ)) ^ t * sgCRRA σ (w t)) :
    Summable (fun t => β ^ t * sgCRRA σ (sgOfBdd θ w t)) ∧
      sgUtility β (sgCRRA σ) (sgOfBdd θ w) =
        discountedUtility (β * θ ^ (1 - σ)) (sgCRRA σ) w + sgConstK β θ σ := by
  have hK := sg_summable_const hβ0 hβ1 hθ hρ1
  have heq : (fun t => β ^ t * sgCRRA σ (sgOfBdd θ w t)) =
      fun t => (β * θ ^ (1 - σ)) ^ t * sgCRRA σ (w t) + β ^ t * sgCRRA σ (θ ^ t) :=
    funext fun t => sg_term_split hθ (hw t) t
  refine ⟨heq ▸ hs.add hK, ?_⟩
  unfold sgUtility discountedUtility sgConstK
  rw [heq, hs.tsum_add hK]

/-- CRRA is bounded on `[a, R]`, `a > 0`: `|U(c)| ≤ |U(a)| + |U(R)|`. -/
theorem sgCRRA_abs_le {σ a R c : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hc : c ∈ Icc a R) :
    |sgCRRA σ c| ≤ |sgCRRA σ a| + |sgCRRA σ R| := by
  have hm := (sgCRRA_strictMonoOn hσ).monotoneOn
  have h1 : sgCRRA σ a ≤ sgCRRA σ c := hm (show a ∈ Ioi 0 from ha)
    (show c ∈ Ioi 0 from lt_of_lt_of_le ha hc.1) hc.1
  have h2 : sgCRRA σ c ≤ sgCRRA σ R := hm (show c ∈ Ioi 0 from lt_of_lt_of_le ha hc.1)
    (show R ∈ Ioi 0 from lt_of_lt_of_le ha (hc.1.trans hc.2)) hc.2
  rw [abs_le]
  constructor <;> linarith [abs_nonneg (sgCRRA σ a), abs_nonneg (sgCRRA σ R),
    neg_abs_le (sgCRRA σ a), le_abs_self (sgCRRA σ R)]

/-- Points of `X` lie in `[a, ‖w‖]^ℕ`. -/
theorem sgXa_mem_seqSet {θ a : ℝ} (hθ : 0 < θ) {w : BddSeq ℝ} (hw : w ∈ sgXa θ a) {R : ℝ}
    (hR : ‖w‖ ≤ R) : w ∈ seqSet (Icc a R) := fun t =>
  ⟨(mem_sgXa_iff hθ).1 hw t, (le_abs_self _).trans ((norm_seq_coord_le w t).trans hR)⟩

/-- The normalised series `Σ ρᵗ U(w_t)` converges on `X`. -/
theorem sg_summable_normalised {β θ σ a : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hθ : 0 < θ)
    (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) {w : BddSeq ℝ} (hw : w ∈ sgXa θ a) :
    Summable fun t => (β * θ ^ (1 - σ)) ^ t * sgCRRA σ (w t) :=
  summable_discounted (mul_nonneg hβ0 (Real.rpow_nonneg hθ.le _)) hρ1
    (fun _ hc => sgCRRA_abs_le hσ ha hc) (sgXa_mem_seqSet hθ hw le_rfl)

/-- **Exercise 16.3(d), finiteness**: `u(x) = Σ βᵗ U(x_t)` converges at every `x ∈ X`. -/
theorem ex_16_3d_summable {β θ σ a : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : 0 < θ)
    (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) {w : BddSeq ℝ} (hw : w ∈ sgXa θ a) :
    Summable fun t => β ^ t * sgCRRA σ (sgOfBdd θ w t) :=
  (sgUtility_split hβ0 hβ1 hθ hρ1 (fun t => lt_of_lt_of_le ha ((mem_sgXa_iff hθ).1 hw t))
    (sg_summable_normalised hσ hβ0 hθ hρ1 ha hw)).1

/-- The utility on `X` is `Σ ρᵗ U(w_t) + K`. -/
theorem sgUtility_eq_on_sgXa {β θ σ a : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) {w : BddSeq ℝ} (hw : w ∈ sgXa θ a) :
    sgUtility β (sgCRRA σ) (sgOfBdd θ w) =
      discountedUtility (β * θ ^ (1 - σ)) (sgCRRA σ) w + sgConstK β θ σ :=
  (sgUtility_split hβ0 hβ1 hθ hρ1 (fun t => lt_of_lt_of_le ha ((mem_sgXa_iff hθ).1 hw t))
    (sg_summable_normalised hσ hβ0 hθ hρ1 ha hw)).2

/-- **Exercise 16.3(d), corrected boundedness**: `u` is bounded on every norm-bounded subset
of `X` (this is what the manual's argument proves). -/
theorem ex_16_3d_bounded_on_balls {β θ σ a : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) (R : ℝ) :
    ∃ M, ∀ w ∈ sgXa θ a, ‖w‖ ≤ R → |sgUtility β (sgCRRA σ) (sgOfBdd θ w)| ≤ M := by
  set ρ := β * θ ^ (1 - σ)
  have hρ0 : 0 ≤ ρ := mul_nonneg hβ0 (Real.rpow_nonneg hθ.le _)
  set MR := |sgCRRA σ a| + |sgCRRA σ R|
  refine ⟨MR * (1 - ρ)⁻¹ + |sgConstK β θ σ|, fun w hw hR => ?_⟩
  rw [sgUtility_eq_on_sgXa hσ hβ0 hβ1 hθ hρ1 ha hw]
  have hmem := sgXa_mem_seqSet hθ hw hR
  have hs := sg_summable_normalised hσ hβ0 hθ hρ1 ha hw
  have hg := summable_geometric_of_lt_one hρ0 hρ1
  have hV : |discountedUtility ρ (sgCRRA σ) w| ≤ MR * (1 - ρ)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hρ0 hρ1, ← tsum_mul_left, abs_le]
    unfold discountedUtility
    constructor
    · rw [← tsum_neg]
      refine (hg.mul_left MR).neg.tsum_le_tsum (fun t => ?_) hs
      have := norm_discounted_term_le hρ0 (fun _ hc => sgCRRA_abs_le hσ ha hc) hmem t
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (ρ ^ t * sgCRRA σ (w t))]
    · refine hs.tsum_le_tsum (fun t => ?_) (hg.mul_left MR)
      have := norm_discounted_term_le hρ0 (fun _ hc => sgCRRA_abs_le hσ ha hc) hmem t
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (ρ ^ t * sgCRRA σ (w t))]
  calc |discountedUtility ρ (sgCRRA σ) w + sgConstK β θ σ|
      ≤ |discountedUtility ρ (sgCRRA σ) w| + |sgConstK β θ σ| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- **Exercise 16.3(d), continuity**: for CRRA `U` with `σ > 0` and `βθ^{1−σ} < 1`, `u` is
continuous on `X` in `‖·‖_θ` (local bounds on `[a, ‖w₀‖ + 1]`). -/
theorem ex_16_3d_continuousOn {β θ σ a : ℝ} (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) :
    ContinuousOn (fun w => sgUtility β (sgCRRA σ) (sgOfBdd θ w)) (sgXa θ a) := by
  intro w0 hw0
  set ρ := β * θ ^ (1 - σ)
  have hρ0 : 0 ≤ ρ := mul_nonneg hβ0 (Real.rpow_nonneg hθ.le _)
  set R := ‖w0‖ + 1
  have hV : ContinuousOn (discountedUtility ρ (sgCRRA σ)) (seqSet (Icc a R)) :=
    ex_15_10b_continuousOn hρ0 hρ1 (fun _ hc => sgCRRA_abs_le hσ ha hc)
      ((sgCRRA_continuousOn σ).mono fun c hc => lt_of_lt_of_le ha hc.1)
  have hw0R : w0 ∈ seqSet (Icc a R) := sgXa_mem_seqSet hθ hw0 (by linarith)
  have hcw : ContinuousWithinAt (fun w => discountedUtility ρ (sgCRRA σ) w + sgConstK β θ σ)
      (seqSet (Icc a R)) w0 := (hV w0 hw0R).add continuousWithinAt_const
  have hnhds : seqSet (Icc a R) ∈ 𝓝[sgXa θ a] w0 := by
    refine mem_nhdsWithin.2 ⟨Metric.ball w0 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos,
      fun w ⟨hb, hw⟩ t => ⟨(mem_sgXa_iff hθ).1 hw t, ?_⟩⟩
    rw [Metric.mem_ball, dist_eq_norm] at hb
    have h1 := norm_seq_coord_le (w - w0) t
    rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] at h1
    have h2 := norm_seq_coord_le w0 t
    rw [Real.norm_eq_abs] at h2
    linarith [le_abs_self (w t - w0 t), le_abs_self (w0 t)]
  refine (hcw.mono_of_mem_nhdsWithin hnhds).congr (fun w hw => ?_) ?_
  · exact sgUtility_eq_on_sgXa hσ hβ0 hβ1 hθ hρ1 ha hw
  · exact sgUtility_eq_on_sgXa hσ hβ0 hβ1 hθ hρ1 ha hw0

/-- CRRA with `σ > 1` is bounded above by `1/(σ − 1)`. -/
theorem sgCRRA_le_of_one_lt {σ c : ℝ} (hσ : 1 < σ) (hc : 0 < c) :
    sgCRRA σ c ≤ 1 / (σ - 1) := by
  rw [sgCRRA_of_ne hσ.ne']
  have hp : 0 < c ^ (1 - σ) := Real.rpow_pos_of_pos hc _
  rw [show (c ^ (1 - σ) - 1) / (1 - σ) = (1 - c ^ (1 - σ)) / (σ - 1) by
    rw [← neg_sub, ← neg_sub σ, neg_div_neg_eq]]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- **Exercise 16.3(d) for `σ > 1`**: `u` is bounded on `X`. -/
theorem ex_16_3d_bounded_of_one_lt {β θ σ a : ℝ} (hσ : 1 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hρ1 : β * θ ^ (1 - σ) < 1) (ha : 0 < a) :
    BddAbove ((fun w => sgUtility β (sgCRRA σ) (sgOfBdd θ w)) '' sgXa θ a) ∧
      BddBelow ((fun w => sgUtility β (sgCRRA σ) (sgOfBdd θ w)) '' sgXa θ a) := by
  set ρ := β * θ ^ (1 - σ)
  have hσ0 : 0 < σ := by linarith
  have hρ0 : 0 ≤ ρ := mul_nonneg hβ0 (Real.rpow_nonneg hθ.le _)
  have hg := summable_geometric_of_lt_one hρ0 hρ1
  have hmono := (sgCRRA_strictMonoOn hσ0).monotoneOn
  constructor
  · refine ⟨1 / (σ - 1) * (1 - ρ)⁻¹ + sgConstK β θ σ, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simp only
    rw [sgUtility_eq_on_sgXa hσ0 hβ0 hβ1 hθ hρ1 ha hw]
    gcongr
    rw [← tsum_geometric_of_lt_one hρ0 hρ1, ← tsum_mul_left]
    refine (sg_summable_normalised hσ0 hβ0 hθ hρ1 ha hw).tsum_le_tsum (fun t => ?_)
      (hg.mul_left _)
    rw [mul_comm (1 / (σ - 1))]
    exact mul_le_mul_of_nonneg_left (sgCRRA_le_of_one_lt hσ
      (lt_of_lt_of_le ha ((mem_sgXa_iff hθ).1 hw t))) (pow_nonneg hρ0 t)
  · refine ⟨sgCRRA σ a * (1 - ρ)⁻¹ + sgConstK β θ σ, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simp only
    rw [sgUtility_eq_on_sgXa hσ0 hβ0 hβ1 hθ hρ1 ha hw]
    gcongr
    rw [← tsum_geometric_of_lt_one hρ0 hρ1, ← tsum_mul_left]
    refine (hg.mul_left _).tsum_le_tsum (fun t => ?_)
      (sg_summable_normalised hσ0 hβ0 hθ hρ1 ha hw)
    rw [mul_comm (sgCRRA σ a)]
    have hwt := (mem_sgXa_iff hθ).1 hw t
    exact mul_le_mul_of_nonneg_left (hmono (show a ∈ Ioi 0 from ha)
      (show w t ∈ Ioi 0 from lt_of_lt_of_le ha hwt) hwt) (pow_nonneg hρ0 t)

/-- The utility of a constant path at `θ = 1`: `u(b𝟙) = U(b)/(1 − β)`. -/
theorem sgUtility_const {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (U : ℝ → ℝ) (b : ℝ) :
    sgUtility β U (sgOfBdd 1 (sgConst b)) = U b / (1 - β) := by
  unfold sgUtility sgOfBdd
  simp only [one_pow, sgConst_apply, one_mul]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_inv_mul]

/-- **Counterexample** to Ex 16.3(d) ("u is bounded on X") for `σ ≤ 1`: with `θ = 1` (so
`βθ^{1−σ} = β < 1`), `u` is unbounded above on `X`, since `u(b𝟙) = U(b)/(1 − β)`. -/
theorem ex_16_3d_counterexample {β σ a : ℝ} (hσ : σ ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ¬ BddAbove ((fun w => sgUtility β (sgCRRA σ) (sgOfBdd 1 w)) '' sgXa 1 a) := by
  rintro ⟨M, hM⟩
  obtain ⟨b, hb1, hb2⟩ := (((sgCRRA_tendsto_atTop hσ).eventually_gt_atTop (M * (1 - β))).and
    (eventually_ge_atTop a)).exists
  have hmem : sgConst b ∈ sgXa 1 a := (mem_sgXa_iff one_pos).2 fun _ => hb2
  have := hM ⟨sgConst b, hmem, rfl⟩
  simp only [sgUtility_const hβ0 hβ1] at this
  rw [div_le_iff₀ (by linarith)] at this
  linarith

/-- The book's case `σ = ½`, `θ = 1`: `u(b𝟙) = (2√b − 2)/(1 − β)`, unbounded on `X`. -/
theorem ex_16_3d_counterexample_half {β a b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    sgUtility β (sgCRRA (1 / 2)) (sgOfBdd 1 (sgConst b)) = (2 * √b - 2) / (1 - β) ∧
      ¬ BddAbove ((fun w => sgUtility β (sgCRRA (1 / 2)) (sgOfBdd 1 w)) '' sgXa 1 a) := by
  refine ⟨?_, ex_16_3d_counterexample (by norm_num) hβ0 hβ1⟩
  rw [sgUtility_const hβ0 hβ1, sgCRRA_of_ne (by norm_num), Real.sqrt_eq_rpow]
  norm_num
  ring

end StokeyLucasPrescott.EquilibriumApplications

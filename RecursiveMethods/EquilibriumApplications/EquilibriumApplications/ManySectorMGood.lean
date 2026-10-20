/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManySectorPrices

/-!
# A many-sector model of stochastic growth with `M` consumption goods (Ex 16.2(a)–(b))

SLP §16.2, pp. 481–482, as the book states it: `M` consumption goods, `l` capital goods, and the
commodity space `S^M` of sequences of essentially bounded `c_t : Z^t → ℝ^M`. `ManySector`,
`ManySectorTech` and `ManySectorPrices` prove Exercise 16.2(a)–(b) for `M = 1`; this module
reuses that structure for any `M ≥ 1`.

**The commodity space.** A bundle `c_t(z^t) = (c_{t1}(z^t), …, c_{tM}(z^t)) ∈ ℝ^M` (goods as
`Fin M → ℝ`) is the function `(z^t, m) ↦ c_{tm}(z^t)` on `Z^t × {1, …, M}`, and
`S^M = LinftyTimeState (msMμ μ M)` with `msMμ μ M t = μ^t ⊗ ρ`, `ρ` the uniform probability on the
goods (`msMUnif`). A set is `μ^t ⊗ ρ`-null iff its `z^t`-projection is `μ^t`-null
(`msM_ae_iff`: a.e. on `Z^t × {1, …, M}` means `μ^t`-a.e. for every good), so elements of `S^M`
are the book's equivalence classes and `‖c‖ = sup_t ess sup_{z^t} max_m |c_{tm}(z^t)|` (the sup
norm on `ℝ^M`). The Chapter 15 machinery (Theorems 15.4 and 15.9, for one good on an arbitrary
probability space) then applies verbatim, and the price of Theorem 15.9 on `Z^t × {1, …, M}` is
read back as `M` prices per period (`msM_price_form`).

* Preferences: `msMEU`, `msMU` (`u(c) = Σ_t βᵗ ∫ U[c_t(z^t)] dμ^t`, `U : ℝ^M → ℝ`),
  `ManySectorMHyp` (`U` continuous, bounded, strictly increasing and strictly concave on `ℝ^M_+`).
* **Exercise 16.2(a), consumption side** (`ex_16_2a_consumer_M`): 15.1–15.3, 15.7, 15.9′ (an
  event of `Z^s × {1, …, M}` may truncate some goods and not others: `msM_eu_trunc_tendsto`) and
  the consumer halves of 15.6 and 15.8′; `msM_U_lt_add_one` (nonsatiation),
  `msM_supporting_nonneg`.
* Technology: `MsMTech` (properties (a)–(c) of §10.3 for `Φ(x, z) ⊆ ℝ^M_+ × X`), `msMY` (the
  production set), `MsMFreeDisposal` (goodwise free disposal of consumption),
  `MsMPositiveProduction` (a plan producing at least `ε > 0` of every good); `msM_Y_sub_C`,
  `msM_convex_Y` (15.4), `msM_Y_timeTrunc` (15.6), `msM_Y_periodTrunc` (15.8′), `msM_interior_Y`
  (15.5).
* **Exercise 16.2(a), `M` goods** (`ex_16_2a_M`): `(C, u, Y)` satisfy 15.1–15.7 and 15.8′–15.9′.
* **Exercise 16.2(b), `M` goods** (`ex_16_2b_M`): `(γ*, γ*, ν)` is a competitive equilibrium with
  `ν(γ*) > 0` and `ν(c) = Σ_t ∫ [Σ_m p_{tm}(z^t) c_{tm}(z^t)] dμ^t(z^t)`, `p_{tm} ∈ L¹(μ^t)`.

**Corrections.** As for `M = 1` (NOTE to Ex 16.2a): free disposal of consumption (here goodwise)
and a plan producing a uniformly positive amount of **every** good are added (the counterexamples
`ex_16_2a_trunc_counterexample` and `ex_16_2a_interior_counterexample` of `ManySectorTech` are the
case `M = 1`); "for all `z^t`" in `Y` reads "a.e."; `U` is defined on all of `ℝ^M` (only its values
on `ℝ^M_+` matter); `γ*` maximising `u` on `C ∩ Y` (Ex 10.3b) is a hypothesis. Theorem 15.9 is
used for one good on `Z^t × {1, …, M}`, which is the remark after Theorem 15.8 ("any finite number
of goods", NOTE (iv)) made precise.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] {μ : ∀ t, Measure (Ω t)} {M : ℕ}

/-- The uniform probability on the `M` goods, `ρ{m} = 1/M`. -/
noncomputable def msMUnif (M : ℕ) : Measure (Fin M) := (M : ℝ≥0∞)⁻¹ • Measure.count

/-- The measure `μ^t ⊗ ρ` on `Z^t × {1, …, M}`: a commodity bundle `c_t : Z^t → ℝ^M` is the
function `(z^t, m) ↦ c_{tm}(z^t)`. -/
noncomputable def msMμ (μ : ∀ t, Measure (Ω t)) (M : ℕ) (t : ℕ) : Measure (Ω t × Fin M) :=
  (μ t).prod (msMUnif M)

/-- `ρ` is a probability measure (`M ≥ 1`). -/
theorem msMUnif_prob [NeZero M] : IsProbabilityMeasure (msMUnif M) := by
  constructor
  simp only [msMUnif, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, ENat.toENNReal_coe]
  exact ENNReal.inv_mul_cancel (by simp [NeZero.ne]) (by simp)

/-- Every good has positive weight: `ρ{m} ≠ 0`. -/
theorem msMUnif_singleton_ne (m : Fin M) : msMUnif M {m} ≠ 0 := by
  simp [msMUnif]

/-- `μ^t ⊗ ρ` is a probability measure. -/
theorem msMμ_prob [∀ t, IsProbabilityMeasure (μ t)] [NeZero M] (t : ℕ) :
    IsProbabilityMeasure (msMμ μ M t) := by
  have := msMUnif_prob (M := M)
  rw [msMμ]
  infer_instance

/-- **A.e. on `Z^t × {1, …, M}` is a.e. in `z^t` for every good**. -/
theorem msM_ae_iff {t : ℕ} {P : Ω t × Fin M → Prop} :
    (∀ᵐ p ∂msMμ μ M t, P p) ↔ ∀ᵐ ω ∂μ t, ∀ m, P (ω, m) := by
  constructor
  · intro h
    filter_upwards [Measure.ae_ae_of_ae_prod h] with ω hω m
    exact (ae_iff_of_countable.1 hω) m (msMUnif_singleton_ne m)
  · intro h
    rw [ae_iff]
    refine measure_mono_null (t := {ω | ¬ ∀ m, P (ω, m)} ×ˢ univ) ?_ ?_
    · intro p hp
      exact ⟨fun hall => hp (hall p.2), mem_univ _⟩
    · rw [msMμ, Measure.prod_prod, ae_iff.1 h, zero_mul]

/-- The coordinate `z^t ↦ x_m(z^t)` of `x ∈ L∞(μ^t ⊗ ρ)` is measurable. -/
theorem msM_coord_measurable {t : ℕ} (x : Lp ℝ ⊤ (msMμ μ M t)) (m : Fin M) :
    Measurable fun ω => x (ω, m) :=
  (Lp.stronglyMeasurable x).measurable.comp measurable_prodMk_right

/-- The bundle `z^t ↦ (x_m(z^t))_m ∈ ℝ^M` is measurable. -/
theorem msM_bundle_measurable {t : ℕ} (x : Lp ℝ ⊤ (msMμ μ M t)) :
    Measurable fun ω => fun m => x (ω, m) :=
  measurable_pi_iff.2 fun m => msM_coord_measurable x m

/-- Coordinates of a linear combination in one period, a.e. for every good. -/
theorem msM_lp_combo_ae {t : ℕ} (a b : ℝ) (x y : Lp ℝ ⊤ (msMμ μ M t)) :
    ∀ᵐ ω ∂μ t, ∀ m, (a • x + b • y) (ω, m) = a * x (ω, m) + b * y (ω, m) :=
  (msM_ae_iff (P := fun p => (a • x + b • y) p = a * x p + b * y p)).1 (by
    filter_upwards [Lp.coeFn_add (a • x) (b • y), Lp.coeFn_smul a x, Lp.coeFn_smul b y]
      with p h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul])

/-- Coordinates of a sum, a.e. for every good. -/
theorem msM_add_ae (c d : LinftyTimeState (msMμ μ M)) (t : ℕ) :
    ∀ᵐ ω ∂μ t, ∀ m, (c + d) t (ω, m) = c t (ω, m) + d t (ω, m) :=
  (msM_ae_iff (P := fun p => (c + d) t p = c t p + d t p)).1 (by
    filter_upwards [Lp.coeFn_add (c t) (d t)] with p hp
    rw [ms_coord_add, hp, Pi.add_apply])

/-- Membership in `C`: every good is consumed in a nonnegative amount, a.e. -/
theorem msM_C_ae {c : LinftyTimeState (msMμ μ M)} (hc : c ∈ msC (msMμ μ M)) (t : ℕ) :
    ∀ᵐ ω ∂μ t, ∀ m, 0 ≤ c t (ω, m) :=
  (msM_ae_iff (P := fun p => 0 ≤ c t p)).1 (hc t)

/-- `C` from the bundle: a.e. nonnegative bundles in every period. -/
theorem msM_C_of_ae {c : LinftyTimeState (msMμ μ M)}
    (hc : ∀ t, ∀ᵐ ω ∂μ t, ∀ m, 0 ≤ c t (ω, m)) : c ∈ msC (msMμ μ M) :=
  fun t => (msM_ae_iff (P := fun p => 0 ≤ c t p)).2 (hc t)

/-- `|x_m(z^t)| ≤ ‖x‖` a.e. for every good. -/
theorem msM_ae_abs_le (c : LinftyTimeState (msMμ μ M)) (t : ℕ) :
    ∀ᵐ ω ∂μ t, ∀ m, |c t (ω, m)| ≤ ‖c‖ :=
  (msM_ae_iff (P := fun p => |c t p| ≤ ‖c‖)).1 (ms_ae_abs_le c t)

/-! ### Preferences over `M` goods -/

/-- Expected utility in period `t`: `∫ U(x_1(z^t), …, x_M(z^t)) dμ^t(z^t)`. -/
noncomputable def msMEU (μ : ∀ t, Measure (Ω t)) (M : ℕ) (U : (Fin M → ℝ) → ℝ) (t : ℕ)
    (x : Lp ℝ ⊤ (msMμ μ M t)) : ℝ :=
  ∫ ω, U (fun m => x (ω, m)) ∂(μ t)

/-- Preferences `u(c) = Σ_t βᵗ ∫ U[c_t(z^t)] dμ^t` with `c_t(z^t) ∈ ℝ^M` (§10.3 (1)). -/
noncomputable def msMU (μ : ∀ t, Measure (Ω t)) (M : ℕ) (β : ℝ) (U : (Fin M → ℝ) → ℝ)
    (c : LinftyTimeState (msMμ μ M)) : ℝ :=
  ∑' t, β ^ t * msMEU μ M U t (c t)

/-- The restrictions of §10.3 on `U : ℝ^M → ℝ` and `β`: `U` continuous, bounded, strictly
increasing and strictly concave on `ℝ^M_+`, `0 < β < 1`. -/
structure ManySectorMHyp (U : (Fin M → ℝ) → ℝ) (β : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  U_cont : Continuous U
  U_bdd : ∃ B, ∀ x, |U x| ≤ B
  U_strictMono : StrictMonoOn U (Ici 0)
  U_strictConcave : StrictConcaveOn ℝ (Ici 0) U

variable {U : (Fin M → ℝ) → ℝ} {β : ℝ} [∀ t, IsProbabilityMeasure (μ t)]

/-- `U ∘ x` is integrable. -/
theorem msM_integrable (H : ManySectorMHyp U β) (t : ℕ) (x : Lp ℝ ⊤ (msMμ μ M t)) :
    Integrable (fun ω => U (fun m => x (ω, m))) (μ t) := by
  obtain ⟨B, hB⟩ := H.U_bdd
  exact Integrable.of_bound
    (H.U_cont.measurable.comp (msM_bundle_measurable x)).aestronglyMeasurable
    B (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)

/-- `|∫ U(x) dμ^t| ≤ B` for `|U| ≤ B`. -/
theorem msM_eu_abs_le {B : ℝ} (hB : ∀ x, |U x| ≤ B) (t : ℕ) (x : Lp ℝ ⊤ (msMμ μ M t)) :
    |msMEU μ M U t x| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ t) (f := fun ω => U (fun m => x (ω, m)))
    (C := B) (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)
  simpa [msMEU, probReal_univ] using this

/-- The terms of `u` are bounded by `B βᵗ`. -/
theorem msM_term_le (H : ManySectorMHyp U β) {B : ℝ} (hB : ∀ x, |U x| ≤ B)
    (c : LinftyTimeState (msMμ μ M)) (t : ℕ) :
    ‖β ^ t * msMEU μ M U t (c t)‖ ≤ B * β ^ t := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos H.beta_pos t), mul_comm]
  exact mul_le_mul_of_nonneg_right (msM_eu_abs_le hB t _) (pow_nonneg H.beta_pos.le t)

/-- The series defining `u` converges. -/
theorem msM_summable (H : ManySectorMHyp U β) (c : LinftyTimeState (msMμ μ M)) :
    Summable fun t => β ^ t * msMEU μ M U t (c t) := by
  obtain ⟨B, hB⟩ := H.U_bdd
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one H.beta_pos.le
    H.beta_lt_one).mul_left B) (msM_term_le H hB c)

/-- Per-period concavity on a.e. nonnegative bundles. -/
theorem msM_eu_concave (H : ManySectorMHyp U β) (t : ℕ) {x x' : Lp ℝ ⊤ (msMμ μ M t)}
    (hx : ∀ᵐ ω ∂μ t, ∀ m, 0 ≤ x (ω, m)) (hx' : ∀ᵐ ω ∂μ t, ∀ m, 0 ≤ x' (ω, m)) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * msMEU μ M U t x + (1 - θ) * msMEU μ M U t x' ≤ msMEU μ M U t (θ • x + (1 - θ) • x') := by
  rw [msMEU, msMEU, msMEU, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((msM_integrable H t x).const_mul θ) ((msM_integrable H t x').const_mul (1 - θ))]
  refine integral_mono_ae (((msM_integrable H t x).const_mul θ).add
    ((msM_integrable H t x').const_mul (1 - θ))) (msM_integrable H t _) ?_
  filter_upwards [msM_lp_combo_ae θ (1 - θ) x x', hx, hx'] with ω e p1 p2
  have hb : (fun m => (θ • x + (1 - θ) • x') (ω, m)) =
      θ • (fun m => x (ω, m)) + (1 - θ) • (fun m => x' (ω, m)) := by
    funext m
    rw [e m, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  have := H.U_strictConcave.concaveOn.2 (mem_Ici.2 fun m => p1 m) (mem_Ici.2 fun m => p2 m) h0
    (show (0 : ℝ) ≤ 1 - θ by linarith) (show θ + (1 - θ) = 1 by ring)
  simp only [smul_eq_mul] at this
  change θ * U (fun m => x (ω, m)) + (1 - θ) * U (fun m => x' (ω, m)) ≤
    U (fun m => (θ • x + (1 - θ) • x') (ω, m))
  rw [hb]
  exact this

/-- `u` is concave on `C`. -/
theorem msM_U_concave (H : ManySectorMHyp U β) :
    ConcaveOn ℝ (msC (msMμ μ M)) (msMU μ M β U) := by
  refine ⟨ms_convex_C, fun c hc d hd a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  simp only [smul_eq_mul, msMU]
  rw [← tsum_mul_left, ← tsum_mul_left, ← (((msM_summable H c).mul_left a)).tsum_add
    ((msM_summable H d).mul_left (1 - a))]
  refine Summable.tsum_le_tsum (fun t => ?_) (((msM_summable H c).mul_left a).add
    ((msM_summable H d).mul_left (1 - a))) (msM_summable H _)
  rw [ms_coord_add, ms_coord_smul, ms_coord_smul]
  have := msM_eu_concave H t (msM_C_ae hc t) (msM_C_ae hd t) ha (by linarith)
  have hβ := pow_pos H.beta_pos t
  nlinarith [mul_le_mul_of_nonneg_left this hβ.le]

/-- **Assumption 15.2** (from concavity of `U`). -/
theorem msM_assumption15_2 (H : ManySectorMHyp U β) :
    Assumption15_2 (fun _ : Unit => msC (msMμ μ M)) (fun _ => msMU μ M β U) := by
  intro _ z hz z' hz' hlt θ h0 h1
  have := (msM_U_concave H).2 hz hz' h0.le (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at this
  nlinarith

/-- Per-period expected utility is continuous on `L∞(μ^t ⊗ ρ)` (dominated convergence along
sequences: `L∞` convergence gives a.e. convergence of the bundles). -/
theorem msM_eu_continuous (H : ManySectorMHyp U β) (t : ℕ) : Continuous (msMEU μ M U t) := by
  obtain ⟨B, hB⟩ := H.U_bdd
  rw [continuous_iff_seqContinuous]
  intro x x₀ hx
  have hae : ∀ᵐ ω ∂μ t, ∀ m, ∀ n, |x n (ω, m) - x₀ (ω, m)| ≤ ‖x n - x₀‖ := by
    refine (msM_ae_iff (P := fun p => ∀ n, |x n p - x₀ p| ≤ ‖x n - x₀‖)).1 ?_
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_sub (x n) x₀, ae_abs_le_norm_linfty (x n - x₀)] with p h1 h2
    rw [h1, Pi.sub_apply] at h2
    exact h2
  have hn := tendsto_iff_norm_sub_tendsto_zero.1 hx
  change Tendsto (fun n => ∫ ω, U (fun m => x n (ω, m)) ∂(μ t)) atTop
    (𝓝 (∫ ω, U (fun m => x₀ (ω, m)) ∂(μ t)))
  refine tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun n => (msM_integrable H t _).aestronglyMeasurable) (integrable_const B)
    (fun n => Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _) ?_
  filter_upwards [hae] with ω hω
  have hb : Tendsto (fun n => fun m => x n (ω, m)) atTop (𝓝 fun m => x₀ (ω, m)) :=
    tendsto_pi_nhds.2 fun m => tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun n => norm_nonneg _)
        (fun n => by rw [Real.norm_eq_abs]; exact hω m n) hn)
  exact (H.U_cont.tendsto _).comp hb

/-- **Assumption 15.3**: `u` is continuous on `S^M`. -/
theorem msM_U_continuous (H : ManySectorMHyp U β) : Continuous (msMU μ M β U) := by
  obtain ⟨B, hB⟩ := H.U_bdd
  exact continuous_tsum (fun t => continuous_const.mul
    ((msM_eu_continuous H t).comp (ms_continuous_coord t)))
    ((summable_geometric_of_lt_one H.beta_pos.le H.beta_lt_one).mul_left B)
    (fun t c => msM_term_le H hB c t)

/-- `u(cᵀ) → u(c)` (dominated convergence; `U` bounded). -/
theorem msM_tendsto_U_timeTrunc (H : ManySectorMHyp U β) (c : LinftyTimeState (msMμ μ M)) :
    Tendsto (fun T => msMU μ M β U (linftyTimeTrunc T c)) atTop (𝓝 (msMU μ M β U c)) := by
  obtain ⟨B, hB⟩ := H.U_bdd
  refine tendsto_tsum_of_dominated_convergence ((summable_geometric_of_lt_one H.beta_pos.le
    H.beta_lt_one).mul_left B) (fun t => ?_)
    (Eventually.of_forall fun T t => msM_term_le H hB _ t)
  refine tendsto_const_nhds.congr' ((eventually_ge_atTop t).mono fun T hT => ?_)
  simp only [linftyTimeTrunc_apply, hT, ↓reduceIte]

/-- Truncating period `s` on `A` changes only the period-`s` term of `u`. -/
theorem msMU_periodTrunc (H : ManySectorMHyp U β) (c : LinftyTimeState (msMμ μ M)) (s : ℕ)
    (A : Set (Ω s × Fin M)) :
    msMU μ M β U (linftyPeriodTrunc s A c) = msMU μ M β U c + β ^ s *
      (msMEU μ M U s (linftyTrunc (msMμ μ M s) A (c s)) - msMEU μ M U s (c s)) := by
  rw [msMU, msMU, ← sub_eq_iff_eq_add', ← (msM_summable H _).tsum_sub (msM_summable H c),
    tsum_eq_single s fun t ht => by rw [linftyPeriodTrunc_apply_of_ne ht, sub_self],
    linftyPeriodTrunc_apply_self]
  ring

/-- Per-period expected utility along event truncations: `u_s(x^{A_n}) → u_s(x)` when `A_n ↓ 0`
in `Z^s × {1, …, M}` (an event may truncate some goods and not others). -/
theorem msM_eu_trunc_tendsto (H : ManySectorMHyp U β) (s : ℕ) {A : ℕ → Set (Ω s × Fin M)}
    (hA : LinftyNullSeq (msMμ μ M s) A) (x : Lp ℝ ⊤ (msMμ μ M s)) :
    Tendsto (fun n => msMEU μ M U s (linftyTrunc (msMμ μ M s) (A n) x)) atTop
      (𝓝 (msMEU μ M U s x)) := by
  obtain ⟨B, hB⟩ := H.U_bdd
  refine tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun n => (msM_integrable H s _).aestronglyMeasurable) (integrable_const B)
    (fun n => Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _) ?_
  have hall : ∀ᵐ ω ∂μ s, ∀ m, ∀ n,
      linftyTrunc (msMμ μ M s) (A n) x (ω, m) = (A n)ᶜ.indicator x (ω, m) :=
    (msM_ae_iff (P := fun p => ∀ n,
      linftyTrunc (msMμ μ M s) (A n) x p = (A n)ᶜ.indicator x p)).1
      (ae_all_iff.2 fun n => coeFn_linftyRestrict (hA.measurableSet n).compl x)
  have hnull : msMμ μ M s (⋂ n, A n) = 0 :=
    le_antisymm (ge_of_tendsto' hA.tendsto_measure fun n => measure_mono (iInter_subset _ n))
      zero_le
  have hnot : ∀ᵐ ω ∂μ s, ∀ m, (ω, m) ∉ ⋂ n, A n :=
    (msM_ae_iff (P := fun p => p ∉ ⋂ n, A n)).1 (measure_eq_zero_iff_ae_notMem.1 hnull)
  filter_upwards [hall, hnot] with ω h1 h2
  choose N hN using fun m => (by simpa only [mem_iInter, not_forall] using h2 m :
    ∃ n, (ω, m) ∉ A n)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (Finset.univ.sup N)] with n hn
  congr 1
  funext m
  rw [h1 m n, indicator_of_mem (show (ω, m) ∈ (A n)ᶜ from fun h =>
    hN m (hA.antitone ((Finset.le_sup (Finset.mem_univ m)).trans hn) h))]

/-- `u(c^{A_n}) → u(c)` when `A_n ↓ 0` in period `s`. -/
theorem msM_tendsto_U_periodTrunc (H : ManySectorMHyp U β) (c : LinftyTimeState (msMμ μ M))
    (s : ℕ) {A : ℕ → Set (Ω s × Fin M)} (hA : LinftyNullSeq (msMμ μ M s) A) :
    Tendsto (fun n => msMU μ M β U (linftyPeriodTrunc s (A n) c)) atTop
      (𝓝 (msMU μ M β U c)) := by
  simp only [msMU_periodTrunc H]
  have := ((msM_eu_trunc_tendsto H s hA (c s)).sub_const
    (msMEU μ M U s (c s))).const_mul (β ^ s)
  simpa using (tendsto_const_nhds (x := msMU μ M β U c)).add this

/-- **Exercise 16.2(a), consumption side, `M` goods**: `(C, u)` satisfy Assumptions 15.1, 15.2,
15.3, 15.7 and 15.9′, and `C` is closed under time and event truncations (15.6, 15.8′). -/
theorem ex_16_2a_consumer_M (H : ManySectorMHyp U β) :
    Assumption15_1 (fun _ : Unit => msC (msMμ μ M)) ∧
      Assumption15_2 (fun _ : Unit => msC (msMμ μ M)) (fun _ => msMU μ M β U) ∧
      Assumption15_3 (fun _ : Unit => msC (msMμ μ M)) (fun _ => msMU μ M β U) ∧
      Assumption15_7_timeState (fun _ : Unit => msC (msMμ μ M)) (fun _ => msMU μ M β U) ∧
      Assumption15_9' (msMμ μ M) (fun _ : Unit => msC (msMμ μ M)) (fun _ => msMU μ M β U) ∧
      (∀ c ∈ msC (msMμ μ M), ∀ T, linftyTimeTrunc T c ∈ msC (msMμ μ M)) ∧
      ∀ c ∈ msC (msMμ μ M), ∀ s (A : Set (Ω s × Fin M)), MeasurableSet A →
        linftyPeriodTrunc s A c ∈ msC (msMμ μ M) :=
  ⟨fun _ => ms_convex_C, msM_assumption15_2 H, fun _ => (msM_U_continuous H).continuousOn,
    fun _ x _ _ _ hlt => (msM_tendsto_U_timeTrunc H x).eventually (lt_mem_nhds hlt),
    fun _ s x _ _ _ hlt _ hA => (msM_tendsto_U_periodTrunc H x s hA).eventually (lt_mem_nhds hlt),
    fun _ hc T => ms_C_timeTrunc hc T, fun _ hc s _ hA => ms_C_periodTrunc hc s hA⟩

/-! ### Monotonicity, nonsatiation and supporting functionals -/

/-- `u` is monotone on `C` (goodwise comparison of bundles). -/
theorem msM_U_mono (H : ManySectorMHyp U β) {c d : LinftyTimeState (msMμ μ M)}
    (hc : c ∈ msC (msMμ μ M)) (hcd : ∀ t, ∀ᵐ ω ∂μ t, ∀ m, c t (ω, m) ≤ d t (ω, m)) :
    msMU μ M β U c ≤ msMU μ M β U d := by
  refine Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left ?_
    (pow_nonneg H.beta_pos.le t)) (msM_summable H c) (msM_summable H d)
  refine integral_mono_ae (msM_integrable H t _) (msM_integrable H t _) ?_
  filter_upwards [msM_C_ae hc t, hcd t] with ω h1 h2
  exact H.U_strictMono.monotoneOn (mem_Ici.2 fun m => h1 m)
    (mem_Ici.2 fun m => (h1 m).trans (h2 m)) fun m => h2 m

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- `(c + 𝟙)_t = c_t + 1` for every good, a.e. -/
theorem msM_add_one_ae [∀ t, IsProbabilityMeasure (msMμ μ M t)]
    (c : LinftyTimeState (msMμ μ M)) (t : ℕ) :
    ∀ᵐ ω ∂μ t, ∀ m, (c + msOne (msMμ μ M)) t (ω, m) = c t (ω, m) + 1 :=
  (msM_ae_iff (P := fun p => (c + msOne (msMμ μ M)) t p = c t p + 1)).1 (ms_add_one_ae c t)

/-- **Nonsatiation**: `u(c + 𝟙) > u(c)` for `c ∈ C` (`U` strictly increasing). -/
theorem msM_U_lt_add_one [NeZero M] [∀ t, IsProbabilityMeasure (msMμ μ M t)]
    (H : ManySectorMHyp U β)
    {c : LinftyTimeState (msMμ μ M)} (hc : c ∈ msC (msMμ μ M)) :
    msMU μ M β U c < msMU μ M β U (c + msOne (msMμ μ M)) := by
  have hlt : ∀ t, ∀ᵐ ω ∂μ t, U (fun m => c t (ω, m)) <
      U (fun m => (c + msOne (msMμ μ M)) t (ω, m)) := fun t => by
    filter_upwards [msM_C_ae hc t, msM_add_one_ae c t] with ω h1 h2
    have e : (fun m => (c + msOne (msMμ μ M)) t (ω, m)) = fun m => c t (ω, m) + 1 := funext h2
    rw [e]
    refine H.U_strictMono (mem_Ici.2 fun m => h1 m)
      (mem_Ici.2 fun m => by change (0 : ℝ) ≤ c t (ω, m) + 1; linarith [h1 m])
      (Pi.lt_def.2 ⟨fun m => by linarith, ?_⟩)
    exact ⟨⟨0, NeZero.pos M⟩, by linarith⟩
  have hle : ∀ t, β ^ t * msMEU μ M U t (c t) ≤
      β ^ t * msMEU μ M U t ((c + msOne (msMμ μ M)) t) := fun t =>
    mul_le_mul_of_nonneg_left (integral_mono_ae (msM_integrable H t _) (msM_integrable H t _)
      ((hlt t).mono fun _ h => h.le)) (pow_nonneg H.beta_pos.le t)
  have hlt0 : msMEU μ M U 0 (c 0) < msMEU μ M U 0 ((c + msOne (msMμ μ M)) 0) := by
    rw [msMEU, msMEU, ← sub_pos, ← integral_sub (msM_integrable H 0 _) (msM_integrable H 0 _)]
    have hpos : ∀ᵐ ω ∂μ 0, 0 < U (fun m => (c + msOne (msMμ μ M)) 0 (ω, m)) -
        U (fun m => c 0 (ω, m)) := (hlt 0).mono fun _ h => sub_pos.2 h
    rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ h => h.le)
      ((msM_integrable H 0 _).sub (msM_integrable H 0 _))]
    by_contra hz
    have hz' : (μ 0) (Function.support fun ω => U (fun m => (c + msOne (msMμ μ M)) 0 (ω, m)) -
        U (fun m => c 0 (ω, m))) = 0 := le_antisymm (not_lt.1 hz) zero_le
    have hnot := measure_eq_zero_iff_ae_notMem.1 hz'
    obtain ⟨ω, h1, h2⟩ := (hpos.and hnot).exists
    exact h2 (Function.mem_support.2 h1.ne')
  exact Summable.tsum_lt_tsum (i := 0) hle (mul_lt_mul_of_pos_left hlt0 (pow_pos H.beta_pos 0))
    (msM_summable H c) (msM_summable H _)

/-- A functional supporting `c⁰ ∈ C` (condition (3) of Theorem 15.4) is **positive** on `C`. -/
theorem msM_supporting_nonneg (H : ManySectorMHyp U β) {c₀ : LinftyTimeState (msMμ μ M)}
    (hc₀ : c₀ ∈ msC (msMμ μ M)) {φ : StrongDual ℝ (LinftyTimeState (msMμ μ M))}
    (hφ : ∀ z ∈ msC (msMμ μ M), msMU μ M β U c₀ ≤ msMU μ M β U z → φ c₀ ≤ φ z)
    {z : LinftyTimeState (msMμ μ M)} (hz : z ∈ msC (msMμ μ M)) : 0 ≤ φ z := by
  have hsum : c₀ + z ∈ msC (msMμ μ M) := fun t => by
    filter_upwards [hc₀ t, hz t, Lp.coeFn_add (c₀ t) (z t)] with ω h1 h2 h3
    rw [ms_coord_add, h3, Pi.add_apply]; linarith
  have := hφ _ hsum (msM_U_mono H hc₀ fun t => by
    filter_upwards [msM_C_ae hz t, msM_add_ae c₀ z t] with ω h2 h3 m
    rw [h3 m]; linarith [h2 m])
  rw [map_add] at this
  linarith

/-! ### Technology with `M` consumption goods -/

variable {Z : Type*} [TopologicalSpace Z] {l : ℕ}

variable (Xc : Set (Fin l → ℝ)) (Φ : (Fin l → ℝ) → Z → Set ((Fin M → ℝ) × (Fin l → ℝ))) in
/-- **Properties (a)–(c) of §10.3** for `Φ(x, z) ⊆ ℝ^M_+ × X` (`M` consumption goods, `l` capital
goods), with `X` convex; continuity is upper plus lower hemicontinuity in sequential form. -/
structure MsMTech : Prop where
  convex_X : Convex ℝ Xc
  nonempty : ∀ x ∈ Xc, ∀ z, (Φ x z).Nonempty
  compact : ∀ x ∈ Xc, ∀ z, IsCompact (Φ x z)
  convex : ∀ x ∈ Xc, ∀ z, Convex ℝ (Φ x z)
  range : ∀ x z p, p ∈ Φ x z → 0 ≤ p.1 ∧ p.2 ∈ Xc
  uhc : ∀ (x : ℕ → Fin l → ℝ) (z : ℕ → Z) (x₀ : Fin l → ℝ) (z₀ : Z), (∀ n, x n ∈ Xc) →
    x₀ ∈ Xc → Tendsto x atTop (𝓝 x₀) → Tendsto z atTop (𝓝 z₀) →
    ∀ p : ℕ → (Fin M → ℝ) × (Fin l → ℝ), (∀ n, p n ∈ Φ (x n) (z n)) →
      ∃ q ∈ Φ x₀ z₀, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (p ∘ φ) atTop (𝓝 q)
  lhc : ∀ (x : ℕ → Fin l → ℝ) (z : ℕ → Z) (x₀ : Fin l → ℝ) (z₀ : Z), (∀ n, x n ∈ Xc) →
    x₀ ∈ Xc → Tendsto x atTop (𝓝 x₀) → Tendsto z atTop (𝓝 z₀) →
    ∀ q ∈ Φ x₀ z₀, ∃ p : ℕ → (Fin M → ℝ) × (Fin l → ℝ), (∀ n, p n ∈ Φ (x n) (z n)) ∧
      Tendsto p atTop (𝓝 q)
  mono : ∀ x x' z p, x ∈ Xc → x ≤ x' → p ∈ Φ x z → p ∈ Φ x' z
  jointConvex : ∀ x x' z p p' (θ : ℝ), 0 ≤ θ → θ ≤ 1 → p ∈ Φ x z → p' ∈ Φ x' z →
    θ • p + (1 - θ) • p' ∈ Φ (θ • x + (1 - θ) • x') z

/-- The production set `Y` with `M` goods (p. 482): plans `c` produced by a bounded measurable
capital plan `k` from `x̂`, `(c_t(z^t), k_t(z^t)) ∈ Φ(x_t, z_t)` `μ^t`-a.e., with
`c_t(z^t) = (c_{tm}(z^t))_m ∈ ℝ^M`. -/
def msMY (μ : ∀ t, Measure (Ω t)) (M : ℕ) (proj : ∀ t, Ω (t + 1) → Ω t) (ζ : ∀ t, Ω t → Z)
    (Φ : (Fin l → ℝ) → Z → Set ((Fin M → ℝ) × (Fin l → ℝ))) (xhat : Fin l → ℝ) :
    Set (LinftyTimeState (msMμ μ M)) :=
  {c | ∃ k : ∀ t, Ω t → Fin l → ℝ, (∀ t, Measurable (k t)) ∧ (∃ B, ∀ t ω, ‖k t ω‖ ≤ B) ∧
    ∀ t, ∀ᵐ ω ∂μ t, ((fun m => c t (ω, m)), k t ω) ∈ Φ (msBeg proj xhat k t ω) (ζ t ω)}

/-- **Free disposal of consumption** (goodwise): `(c, y) ∈ Φ(x, z)`, `0 ≤ c′ ≤ c` in `ℝ^M` imply
`(c′, y) ∈ Φ(x, z)`. -/
def MsMFreeDisposal (Φ : (Fin l → ℝ) → Z → Set ((Fin M → ℝ) × (Fin l → ℝ))) : Prop :=
  ∀ x z c y c', (c, y) ∈ Φ x z → 0 ≤ c' → c' ≤ c → (c', y) ∈ Φ x z

/-- **Uniformly positive production**: some bounded measurable capital plan from `x̂` produces at
least `ε > 0` of every good a.e. in every period. -/
def MsMPositiveProduction (μ : ∀ t, Measure (Ω t)) (proj : ∀ t, Ω (t + 1) → Ω t)
    (ζ : ∀ t, Ω t → Z) (Φ : (Fin l → ℝ) → Z → Set ((Fin M → ℝ) × (Fin l → ℝ)))
    (xhat : Fin l → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ k : ∀ t, Ω t → Fin l → ℝ, (∀ t, Measurable (k t)) ∧
    (∃ B, ∀ t ω, ‖k t ω‖ ≤ B) ∧
    ∀ t, ∀ᵐ ω ∂μ t, ((fun _ => ε), k t ω) ∈ Φ (msBeg proj xhat k t ω) (ζ t ω)

variable {Xc : Set (Fin l → ℝ)} {Φ : (Fin l → ℝ) → Z → Set ((Fin M → ℝ) × (Fin l → ℝ))}
  {proj : ∀ t, Ω (t + 1) → Ω t} {ζ : ∀ t, Ω t → Z} {xhat : Fin l → ℝ}

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- `Y ⊆ C`. -/
theorem msM_Y_sub_C (hT : MsMTech Xc Φ) : msMY μ M proj ζ Φ xhat ⊆ msC (msMμ μ M) := by
  rintro c ⟨k, -, -, hk⟩
  refine msM_C_of_ae fun t => ?_
  filter_upwards [hk t] with ω h m
  exact (hT.range _ _ _ h).1 m

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- **Assumption 15.4**: `Y` is convex (joint convexity (c) of `Φ`). -/
theorem msM_convex_Y (hT : MsMTech Xc Φ) : Convex ℝ (msMY μ M proj ζ Φ xhat) := by
  rintro c ⟨k, hkm, ⟨B, hB⟩, hk⟩ c' ⟨k', hkm', ⟨B', hB'⟩, hk'⟩ a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  refine ⟨fun t ω => a • k t ω + (1 - a) • k' t ω, fun t => ((hkm t).const_smul a).add
    ((hkm' t).const_smul (1 - a)), ⟨a * B + (1 - a) * B', fun t ω => ?_⟩, fun t => ?_⟩
  · calc ‖a • k t ω + (1 - a) • k' t ω‖ ≤ ‖a • k t ω‖ + ‖(1 - a) • k' t ω‖ := norm_add_le _ _
      _ = a * ‖k t ω‖ + (1 - a) * ‖k' t ω‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * B + (1 - a) * B' := add_le_add (mul_le_mul_of_nonneg_left (hB t ω) ha)
          (mul_le_mul_of_nonneg_left (hB' t ω) hb)
  · filter_upwards [hk t, hk' t, msM_lp_combo_ae a (1 - a) (c t) (c' t)] with ω h1 h2 e
    have := hT.jointConvex _ _ _ _ _ a ha (by linarith) h1 h2
    rw [msBeg_combo]
    have hb' : (fun m => (a • c + (1 - a) • c') t (ω, m)) =
        a • (fun m => c t (ω, m)) + (1 - a) • (fun m => c' t (ω, m)) := by
      funext m
      rw [ms_coord_add, ms_coord_smul, ms_coord_smul, e m, Pi.add_apply, Pi.smul_apply,
        Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [hb']
    simpa only [Prod.smul_mk, Prod.mk_add_mk] using this

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- **Assumption 15.6 for `Y`, with free disposal**. -/
theorem msM_Y_timeTrunc (hT : MsMTech Xc Φ) (hfd : MsMFreeDisposal Φ)
    {c : LinftyTimeState (msMμ μ M)} (hc : c ∈ msMY μ M proj ζ Φ xhat) (T : ℕ) :
    linftyTimeTrunc T c ∈ msMY μ M proj ζ Φ xhat := by
  obtain ⟨k, hkm, hkB, hk⟩ := hc
  refine ⟨k, hkm, hkB, fun t => ?_⟩
  rw [linftyTimeTrunc_apply]
  split_ifs
  · exact hk t
  · have h0 := (msM_ae_iff (P := fun p => (0 : Lp ℝ ⊤ (msMμ μ M t)) p = 0)).1
      (Lp.coeFn_zero ℝ ⊤ (msMμ μ M t))
    filter_upwards [hk t, h0] with ω h1 h2
    have e : (fun m => (0 : Lp ℝ ⊤ (msMμ μ M t)) (ω, m)) = 0 := funext h2
    rw [e]
    exact hfd _ _ _ _ _ h1 le_rfl (hT.range _ _ _ h1).1

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- **Assumption 15.8′ for `Y`, with free disposal**: truncation on an event of
`Z^s × {1, …, M}` (some goods in some states) keeps the capital plan. -/
theorem msM_Y_periodTrunc (hT : MsMTech Xc Φ) (hfd : MsMFreeDisposal Φ)
    {c : LinftyTimeState (msMμ μ M)} (hc : c ∈ msMY μ M proj ζ Φ xhat) (s : ℕ)
    {A : Set (Ω s × Fin M)} (hA : MeasurableSet A) :
    linftyPeriodTrunc s A c ∈ msMY μ M proj ζ Φ xhat := by
  obtain ⟨k, hkm, hkB, hk⟩ := hc
  refine ⟨k, hkm, hkB, fun t => ?_⟩
  by_cases hts : t = s
  · subst hts
    rw [linftyPeriodTrunc_apply_self]
    have h0 := (msM_ae_iff (P := fun p =>
      linftyRestrict (msMμ μ M t) Aᶜ (c t) p = Aᶜ.indicator (c t) p)).1
      (coeFn_linftyRestrict hA.compl (c t))
    filter_upwards [hk t, h0] with ω h1 h2
    have hnn := (hT.range _ _ _ h1).1
    refine hfd _ _ _ _ _ h1 (fun m => ?_) (fun m => ?_)
    · change 0 ≤ linftyRestrict (msMμ μ M t) Aᶜ (c t) (ω, m)
      rw [h2 m]
      by_cases hω : (ω, m) ∈ Aᶜ
      · rw [indicator_of_mem hω]; exact hnn m
      · rw [indicator_of_notMem hω]
    · change linftyRestrict (msMμ μ M t) Aᶜ (c t) (ω, m) ≤ c t (ω, m)
      rw [h2 m]
      by_cases hω : (ω, m) ∈ Aᶜ
      · rw [indicator_of_mem hω]
      · rw [indicator_of_notMem hω]; exact hnn m
  · rw [linftyPeriodTrunc_apply_of_ne hts]
    exact hk t

omit [TopologicalSpace Z] in
/-- **Assumption 15.5 under uniformly positive production and free disposal**: the ball of
radius `ε/2` about `(ε/2)𝟙` lies in `Y`. -/
theorem msM_interior_Y [NeZero M] (hfd : MsMFreeDisposal Φ)
    (hpos : MsMPositiveProduction μ proj ζ Φ xhat) :
    (interior (msMY μ M proj ζ Φ xhat)).Nonempty := by
  have : ∀ t, IsProbabilityMeasure (msMμ μ M t) := msMμ_prob
  obtain ⟨ε, hε, k, hkm, hkB, hk⟩ := hpos
  refine ⟨(ε / 2) • msOne (msMμ μ M), interior_maximal
    (t := Metric.ball ((ε / 2) • msOne (msMμ μ M)) (ε / 2)) ?_
    Metric.isOpen_ball (Metric.mem_ball_self (half_pos hε))⟩
  intro c hc
  rw [mem_ball_iff_norm] at hc
  refine ⟨k, hkm, hkB, fun t => ?_⟩
  have hb := (msM_ae_iff (P := fun p => |c t p - ε / 2| ≤ ‖c - (ε / 2) • msOne (msMμ μ M)‖)).1
    (by
      filter_upwards [ms_ae_abs_le (c - (ε / 2) • msOne (msMμ μ M)) t,
        Lp.coeFn_sub (c t) ((ε / 2) • msOne (msMμ μ M) t),
        Lp.coeFn_smul (ε / 2) (msOne (msMμ μ M) t), msOne_ae (μ := msMμ μ M) t]
        with p h2 e1 e2 e3
      rw [ms_coord_sub, ms_coord_smul, e1, Pi.sub_apply, e2, Pi.smul_apply, e3, smul_eq_mul,
        mul_one] at h2
      exact h2)
  filter_upwards [hk t, hb] with ω h1 h2
  refine hfd _ _ _ _ _ h1 (fun m => ?_) (fun m => ?_)
  · have h3 := abs_lt.1 ((h2 m).trans_lt hc)
    change 0 ≤ c t (ω, m); linarith [h3.1]
  · have h3 := abs_lt.1 ((h2 m).trans_lt hc)
    change c t (ω, m) ≤ ε; linarith [h3.2]

/-- **Exercise 16.2(a), `M` goods, corrected**: if `Φ` satisfies (a)–(c) of §10.3, has free
disposal of consumption and some plan produces a uniformly positive amount of every good, then
`(C, u, Y)` satisfy Assumptions 15.1–15.7 and 15.8′–15.9′. -/
theorem ex_16_2a_M [NeZero M] (H : ManySectorMHyp U β) (hT : MsMTech Xc Φ)
    (hfd : MsMFreeDisposal Φ) (hpos : MsMPositiveProduction μ proj ζ Φ xhat) :
    Assumption15_1 (fun _ : Unit => msC (msMμ μ M)) ∧
      Assumption15_2 (fun _ : Unit => msC (msMμ μ M)) (fun _ => msMU μ M β U) ∧
      Assumption15_3 (fun _ : Unit => msC (msMμ μ M)) (fun _ => msMU μ M β U) ∧
      Assumption15_4 (fun _ : Unit => msMY μ M proj ζ Φ xhat) ∧
      Assumption15_5 (LinftyTimeState (msMμ μ M)) (fun _ : Unit => msMY μ M proj ζ Φ xhat) ∧
      Assumption15_6_timeState (fun _ : Unit => msC (msMμ μ M))
        (fun _ : Unit => msMY μ M proj ζ Φ xhat) ∧
      Assumption15_7_timeState (fun _ : Unit => msC (msMμ μ M)) (fun _ => msMU μ M β U) ∧
      Assumption15_8' (msMμ μ M) (fun _ : Unit => msC (msMμ μ M))
        (fun _ : Unit => msMY μ M proj ζ Φ xhat) ∧
      Assumption15_9' (msMμ μ M) (fun _ : Unit => msC (msMμ μ M)) (fun _ => msMU μ M β U) := by
  obtain ⟨h1, h2, h3, h7, h9, hCT, hCP⟩ := ex_16_2a_consumer_M (μ := μ) H
  refine ⟨h1, h2, h3, ?_, Or.inl ?_, ⟨fun _ c hc => Eventually.of_forall fun T => hCT c hc T,
    fun _ c hc => Eventually.of_forall fun T => msM_Y_timeTrunc hT hfd hc T⟩, h7,
    ⟨fun _ s c hc A hA => Eventually.of_forall fun n => hCP c hc s (A n) (hA.measurableSet n),
      fun _ s c hc A hA => Eventually.of_forall fun n =>
        msM_Y_periodTrunc hT hfd hc s (hA.measurableSet n)⟩, h9⟩
  · rw [Assumption15_4, ms_aggTech_unit]
    exact msM_convex_Y hT
  · rw [ms_aggTech_unit]
    exact msM_interior_Y hfd hpos

/-! ### Exercise 16.2(b) with `M` goods -/

/-- **The price system in the book's form** `ν(c) = Σ_t ∫ Σ_m p_{tm} c_{tm} dμ^t`: an inner-product
representation on `Z^t × {1, …, M}` (Theorem 15.9 for the one-good space `L∞(μ^t ⊗ ρ)`) is one
with `M` prices `p_{tm}(z^t) = p_t(z^t, m)/M ∈ L¹(μ^t)` per period (Fubini over the goods). -/
theorem msM_price_form [NeZero M] {ν : StrongDual ℝ (LinftyTimeState (msMμ μ M))}
    {p : ∀ t, Ω t × Fin M → ℝ} (hp : ∀ t, Integrable (p t) (msMμ μ M t))
    (hν : ∀ c, HasSum (fun t => ∫ w, p t w * c t w ∂(msMμ μ M t)) (ν c)) :
    (∀ t m, Integrable (fun ω => (M : ℝ)⁻¹ * p t (ω, m)) (μ t)) ∧
      ∀ c : LinftyTimeState (msMμ μ M),
        HasSum (fun t => ∫ ω, ∑ m, (M : ℝ)⁻¹ * p t (ω, m) * c t (ω, m) ∂(μ t)) (ν c) := by
  have : IsProbabilityMeasure (msMUnif M) := msMUnif_prob
  have hreal : ∀ m : Fin M, (msMUnif M).real {m} = (M : ℝ)⁻¹ := fun m => by
    simp [msMUnif, measureReal_def, ENNReal.toReal_inv]
  refine ⟨fun t m => ?_, fun c => ?_⟩
  · have hpt : Integrable (p t) ((μ t).prod (msMUnif M)) := hp t
    have h := ((integrable_prod_iff' hpt.aestronglyMeasurable).1 hpt).1
    exact ((ae_iff_of_countable.1 h) m (msMUnif_singleton_ne m)).const_mul _
  · refine (hν c).congr_fun fun t => ?_
    have hi0 : Integrable (fun w => p t w * c t w) (msMμ μ M t) := by
      have := (hp t).bdd_mul (c := ‖c t‖) (Lp.aestronglyMeasurable (c t))
        ((ae_abs_le_norm_linfty (c t)).mono fun w h => by rwa [Real.norm_eq_abs])
      simpa only [mul_comm] using this
    have hi : Integrable (fun w => p t w * c t w) ((μ t).prod (msMUnif M)) := hi0
    change ∫ ω, ∑ m, (M : ℝ)⁻¹ * p t (ω, m) * c t (ω, m) ∂(μ t) =
      ∫ w, p t w * c t w ∂((μ t).prod (msMUnif M))
    rw [integral_prod _ hi]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    change ∑ m, (M : ℝ)⁻¹ * p t (ω, m) * c t (ω, m) =
      ∫ m, p t (ω, m) * c t (ω, m) ∂(msMUnif M)
    rw [integral_fintype Integrable.of_finite]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hreal, smul_eq_mul, mul_assoc]

/-- `(γ*, γ*)` is Pareto optimal in the one-consumer, one-firm economy with `M` goods. -/
theorem msM_paretoOptimal (H : ManySectorMHyp U β) (hT : MsMTech Xc Φ)
    {γ : LinftyTimeState (msMμ μ M)} (hγC : γ ∈ msC (msMμ μ M))
    (hγY : γ ∈ msMY μ M proj ζ Φ xhat)
    (hopt : ∀ c ∈ msC (msMμ μ M), c ∈ msMY μ M proj ζ Φ xhat → msMU μ M β U c ≤ msMU μ M β U γ) :
    ParetoOptimal (fun _ : Unit => msC (msMμ μ M)) (fun _ => msMU μ M β U)
      (fun _ : Unit => msMY μ M proj ζ Φ xhat) (fun _ => γ) (fun _ => γ) :=
  (gc_symmetric_paretoOptimal_iff ms_convex_C (msM_convex_Y hT) (msM_U_concave H) γ γ).2
    ⟨rfl, hγC, hγY, hopt⟩

/-- **Exercise 16.2(b) with `M` consumption goods** (corrected hypotheses as in `ex_16_2a_M`): if
`γ*` maximises `u` on `C ∩ Y` (Ex 10.3b), there is a continuous linear `ν` such that
`(γ*, γ*, ν)` is a competitive equilibrium, `ν(γ*) > 0`, and
`ν(c) = Σ_t ∫ [Σ_m p_{tm}(z^t) c_{tm}(z^t)] dμ^t(z^t)` for all `c ∈ S^M`, with every
`p_{tm} ∈ L¹(μ^t)`. -/
theorem ex_16_2b_M [NeZero M] (H : ManySectorMHyp U β) (hT : MsMTech Xc Φ)
    (hfd : MsMFreeDisposal Φ) (hpos : MsMPositiveProduction μ proj ζ Φ xhat)
    {γ : LinftyTimeState (msMμ μ M)} (hγC : γ ∈ msC (msMμ μ M))
    (hγY : γ ∈ msMY μ M proj ζ Φ xhat)
    (hopt : ∀ c ∈ msC (msMμ μ M), c ∈ msMY μ M proj ζ Φ xhat → msMU μ M β U c ≤ msMU μ M β U γ) :
    ∃ ν : StrongDual ℝ (LinftyTimeState (msMμ μ M)),
      CompetitiveEq (fun _ : Unit => msC (msMμ μ M)) (fun _ => msMU μ M β U)
        (fun _ : Unit => msMY μ M proj ζ Φ xhat) (fun _ => γ) (fun _ => γ) ν ∧ 0 < ν γ ∧
      ∃ p : ∀ t, Fin M → Ω t → ℝ, (∀ t m, Integrable (p t m) (μ t)) ∧
        ∀ c : LinftyTimeState (msMμ μ M),
          HasSum (fun t => ∫ ω, ∑ m, p t m ω * c t (ω, m) ∂(μ t)) (ν c) := by
  have : ∀ t, IsProbabilityMeasure (msMμ μ M t) := msMμ_prob
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ex_16_2a_M H hT hfd hpos
  have hPO := msM_paretoOptimal H hT hγC hγY hopt
  have hsatX := ms_add_one_mem hγC
  have hsat := msM_U_lt_add_one H hγC
  obtain ⟨φ, hne, hφ⟩ := theorem_15_4 h1 h2 h3 h4 h5 hPO (h := ()) hsatX hsat
  have hφpos : ∀ z ∈ msC (msMμ μ M), 0 ≤ φ z := fun z hz =>
    msM_supporting_nonneg H hγC (fun w hw hle => hφ.1 () w hw hle) hz
  obtain ⟨ystar, hystar⟩ := msM_interior_Y hfd hpos (μ := μ) (proj := proj) (ζ := ζ) (xhat := xhat)
  obtain ⟨ε, hε, hεy⟩ := ms_interior_ge (msM_Y_sub_C hT) hystar
  have hyφ := hφpos _ hεy
  rw [map_add, map_smul, smul_eq_mul] at hyφ
  have hφ1 := ms_one_pos hφpos hne
  have hφγ : 0 < φ γ := by
    have := hφ.2 () ystar (interior_subset hystar)
    nlinarith
  obtain ⟨ν, hνX, hνY, p, hp, hpν⟩ := ms_linfty_bounds h6 h7 h8 h9 hPO.1 hφ
  have hνsup := supportsAllocation_of_limit_bounds h1 h2 hPO.1 (fun _ => ⟨_, hsatX, hsat⟩) hνX hνY
  have hle1 : ν γ ≤ φ γ := hνY () γ hγY
  have hle2 : φ γ ≤ ν γ := by
    have hc : Continuous fun θ : ℝ => ν γ + θ * ν (msOne (msMμ μ M)) := by fun_prop
    have ht : Tendsto (fun θ : ℝ => ν γ + θ * ν (msOne (msMμ μ M))) (𝓝[>] 0) (𝓝 (ν γ)) := by
      have := hc.tendsto 0
      simp only [zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
    have hmem : θ • (γ + msOne (msMμ μ M)) + (1 - θ) • γ ∈ msC (msMμ μ M) :=
      ms_convex_C hsatX hγC hθ.1.le (by linarith [hθ.2]) (by ring)
    have hlt := h2 () _ hsatX γ hγC hsat θ hθ.1 hθ.2
    have := hνX () _ hmem hlt
    have e : θ • (γ + msOne (msMμ μ M)) + (1 - θ) • γ = γ + θ • msOne (msMμ μ M) := by
      rw [smul_add, add_comm (θ • γ), add_assoc, ← add_smul, add_sub_cancel, one_smul,
        add_comm]
    rw [e, map_add, map_smul, smul_eq_mul] at this
    exact this
  have hνγ : ν γ = φ γ := le_antisymm hle1 hle2
  obtain ⟨hpi, hpsum⟩ := msM_price_form hp hpν
  refine ⟨ν, remark_cheaper_point h1 h3 hPO.1 hνsup fun _ => ⟨0, ms_zero_mem_C, by
    rw [map_zero, hνγ]; exact hφγ⟩, hνγ ▸ hφγ, fun t m ω => (M : ℝ)⁻¹ * p t (ω, m), hpi,
    hpsum⟩

end StokeyLucasPrescott.EquilibriumApplications

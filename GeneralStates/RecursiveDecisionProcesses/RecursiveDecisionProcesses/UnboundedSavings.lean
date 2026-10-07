/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.SolutionProperties
import RecursiveDecisionProcesses.SavingsFeller
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Optimal savings with utility unbounded above

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.3.1 (pp. 232–233), with
Exercises 7.2.2–7.2.4 (pp. 224–225).

Wealth `w`, consumption `c ∈ Γ(w) = [0, max(w, 0)]`, utility `u` continuous, nonnegative and
increasing, gross return `R ≥ 0`, income `y ∼ ψ`, and
`B(w, c, v) = u(c) + β ∫ v(R(w − c) + y)ψ(dy)` on `V = bℓX₊`.

The weight function (7.25) is `ℓ(w) = 𝔼 ∑_t δᵗ u(Ŵ_t)` along the zero-consumption wealth path. The
proofs use only the properties that the solutions to Exercises 7.3.1–7.3.2 derive from it: `ℓ` is
measurable and increasing, `ℓ(s + ·)` is integrable for every shift, and the recursion
`u(w⁺) + δ ∫ ℓ(Rw + y)ψ(dy) ≤ ℓ(w)`. A weight function must be `≥ 1`; the expected discounted sum
with `u + 1` in place of `u` satisfies all of these, while (7.25) itself can be below `1`. The
path-space expectation is not constructed.

* **Exercise 7.3.1**: (U1) with `λ = β/δ < 1`, and (U2).
* **Exercise 7.3.2**: Assumption 7.2.7 when income has a continuous density `φ` and `ℓ` is
  continuous: `(w, c) ↦ B(w, c, v)` is continuous for every `v ∈ bℓX₊`. The proof writes
  `∫ v(s + y)φ(y) dy = ∫ v(x)φ(x − s) dx` and applies Scheffé's lemma to `ℓ(x)φ(x − s)`, whose
  integral `∫ ℓ(s + y)φ(y) dy` is continuous in `s` by dominated convergence (`ℓ` increasing).
* So Proposition 7.2.5 applies: `v* ∈ bℓcX₊` and VFI, OPI and HPI converge (`section_7_3_1`).
* **Exercise 7.2.2**: Assumption 7.2.8, so `v*` is increasing (Proposition 7.2.6).
* **Exercise 7.2.3**: with `u` concave on `ℝ₊` and income nonnegative, `v*` is increasing and
  concave on `ℝ₊`.
* **Exercise 7.2.4**: with `u` strictly concave, the optimal policy is unique and continuous.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- **Scheffé's lemma** (p. 365), general form: if nonnegative integrable `q_z → q₀` almost
everywhere and `∫ q_z → ∫ q₀`, then `∫ |q_z − q₀| → 0`. -/
theorem scheffe_general {Y X : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter Y}
    [l.IsCountablyGenerated] {q : Y → X → ℝ} {q₀ : X → ℝ} (hq0 : ∀ z x, 0 ≤ q z x)
    (hq₀0 : ∀ x, 0 ≤ q₀ x) (hint : ∀ z, Integrable (q z) μ) (hint₀ : Integrable q₀ μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun z => q z x) l (𝓝 (q₀ x)))
    (hI : Tendsto (fun z => ∫ x, q z x ∂μ) l (𝓝 (∫ x, q₀ x ∂μ))) :
    Tendsto (fun z => ∫ x, |q z x - q₀ x| ∂μ) l (𝓝 0) := by
  have hkey : ∀ z, ∫ x, |q z x - q₀ x| ∂μ =
      2 * ∫ x, max (q₀ x - q z x) 0 ∂μ + (∫ x, q z x ∂μ - ∫ x, q₀ x ∂μ) := by
    intro z
    have hi1 : Integrable (fun x => q₀ x - q z x) μ := hint₀.sub (hint z)
    have habs : ∀ x, |q z x - q₀ x| = 2 * max (q₀ x - q z x) 0 - (q₀ x - q z x) := by
      intro x
      rcases le_total (q₀ x) (q z x) with h | h
      · rw [max_eq_right (sub_nonpos.2 h), abs_of_nonneg (sub_nonneg.2 h)]
        ring
      · rw [max_eq_left (sub_nonneg.2 h), abs_of_nonpos (sub_nonpos.2 h)]
        ring
    simp_rw [habs]
    rw [integral_sub (hi1.pos_part.const_mul 2) hi1, integral_const_mul,
      integral_sub hint₀ (hint z)]
    ring
  have hpos : Tendsto (fun z => ∫ x, max (q₀ x - q z x) 0 ∂μ) l (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := l)
      (F := fun z x => max (q₀ x - q z x) 0) (f := fun _ => (0 : ℝ)) q₀
      (Eventually.of_forall fun z => (hint₀.sub (hint z)).pos_part.aestronglyMeasurable)
      (Eventually.of_forall fun z => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [hq0 z x]) (hq₀0 x))
      hint₀ (by
        filter_upwards [hlim] with x hx
        have h2 := (tendsto_const_nhds (x := q₀ x)).sub hx
        rw [sub_self] at h2
        have h3 := h2.max (tendsto_const_nhds (x := (0 : ℝ)))
        rwa [max_self] at h3)
    simpa using this
  have hsub : Tendsto (fun z => ∫ x, q z x ∂μ - ∫ x, q₀ x ∂μ) l (𝓝 0) := by
    have := hI.sub (tendsto_const_nhds (x := ∫ x, q₀ x ∂μ))
    rwa [sub_self] at this
  have := (hpos.const_mul 2).add hsub
  rw [mul_zero, add_zero] at this
  exact this.congr fun z => (hkey z).symm

/-- The optimal savings model of §7.3.1, with the weight function `ℓ` and its properties. -/
structure SavingsU where
  /-- utility -/
  u : ℝ → ℝ
  continuous_u : Continuous u
  u_nonneg : ∀ c, 0 ≤ u c
  monotone_u : Monotone u
  /-- gross return -/
  R : ℝ
  R_nonneg : 0 ≤ R
  /-- discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  /-- the discount factor in (7.25), `δ ∈ (β, 1)` -/
  δ : ℝ
  β_lt_δ : β < δ
  δ_lt_one : δ < 1
  /-- the income distribution -/
  ψ : Measure ℝ
  [isProb : IsProbabilityMeasure ψ]
  /-- the weight function -/
  ℓ : ℝ → ℝ
  measurable_ℓ : Measurable ℓ
  one_le_ℓ : ∀ w, 1 ≤ ℓ w
  monotone_ℓ : Monotone ℓ
  integrable_ℓ : ∀ s, Integrable (fun y => ℓ (s + y)) ψ
  /-- the recursion satisfied by (7.25) -/
  ℓ_rec : ∀ w, u (max w 0) + δ * ∫ y, ℓ (R * w + y) ∂ψ ≤ ℓ w

namespace SavingsU

attribute [local instance] SavingsU.isProb

variable (M : SavingsU)

/-- `B(w, c, v) = u(c) + β ∫ v(R(w − c) + y)ψ(dy)`. -/
noncomputable def B : ℝ → ℝ → (ℝ → ℝ) → ℝ :=
  fun w c v => M.u c + M.β * ∫ y, v (M.R * (w - c) + y) ∂M.ψ

theorem δ_pos : 0 < M.δ := M.β_nonneg.trans_lt M.β_lt_δ

theorem integrable_v {v : ℝ → ℝ} (hv : v ∈ blPlus M.ℓ) (s : ℝ) :
    Integrable (fun y => v (s + y)) M.ψ := by
  obtain ⟨hm, h0, C, hC⟩ := hv
  refine ((M.integrable_ℓ s).const_mul |C|).mono'
    (hm.comp (measurable_const_add s)).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
  exact (hC _).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
    (zero_le_one.trans (M.one_le_ℓ _)))

theorem integral_ℓ_le (w : ℝ) : ∫ y, M.ℓ (M.R * w + y) ∂M.ψ ≤ M.ℓ w / M.δ := by
  rw [le_div_iff₀ M.δ_pos]
  have h1 := M.ℓ_rec w
  have h2 := M.u_nonneg (max w 0)
  linarith

/-- For feasible `c ≥ 0`, `∫ ℓ(R(w − c) + y) ≤ ∫ ℓ(Rw + y) ≤ ℓ(w)/δ` (`ℓ` increasing). -/
theorem integral_ℓ_feasible_le {w c : ℝ} (hc : 0 ≤ c) :
    ∫ y, M.ℓ (M.R * (w - c) + y) ∂M.ψ ≤ M.ℓ w / M.δ :=
  (integral_mono (M.integrable_ℓ _) (M.integrable_ℓ _) fun y => M.monotone_ℓ (by
    have := mul_le_mul_of_nonneg_left hc M.R_nonneg
    linarith)).trans (M.integral_ℓ_le w)

/-- The savings model as a weighted RDP (§7.3.1); (U2) is the second half of Exercise 7.3.1. -/
noncomputable def wrdp : WRDP ℝ ℝ where
  ℓ := M.ℓ
  measurable_ℓ := M.measurable_ℓ
  one_le_ℓ := M.one_le_ℓ
  Γ w := Icc 0 (max w 0)
  B := M.B
  measurable v hv := by
    have hf : Measurable fun q : (ℝ × ℝ) × ℝ => v (M.R * (q.1.1 - q.1.2) + q.2) :=
      hv.1.comp ((measurable_const.mul ((measurable_fst.comp measurable_fst).sub
        (measurable_snd.comp measurable_fst))).add measurable_snd)
    exact (M.continuous_u.measurable.comp measurable_snd).add (measurable_const.mul
      (hf.stronglyMeasurable.integral_prod_right' (ν := M.ψ)).measurable)
  nonneg _ c _ v hv := add_nonneg (M.u_nonneg c)
    (mul_nonneg M.β_nonneg (integral_nonneg fun _ => hv.2.1 _))
  mono _ _ _ v hv v' hv' h := add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (integral_mono (M.integrable_v hv _) (M.integrable_v hv' _) fun _ => h _) M.β_nonneg)
  U2 v hv := by
    obtain ⟨hm, h0, C, hC⟩ := hv
    refine ⟨0, 1 + M.β * |C| / M.δ, le_rfl, add_nonneg zero_le_one
      (div_nonneg (mul_nonneg M.β_nonneg (abs_nonneg C)) M.δ_pos.le), fun w c hc => ?_⟩
    have hI : ∫ y, v (M.R * (w - c) + y) ∂M.ψ ≤ |C| * (M.ℓ w / M.δ) :=
      (integral_mono (M.integrable_v ⟨hm, h0, C, hC⟩ _) ((M.integrable_ℓ _).const_mul |C|)
        fun y => (hC _).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
          (zero_le_one.trans (M.one_le_ℓ _)))).trans (by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (M.integral_ℓ_feasible_le hc.1) (abs_nonneg C))
    have hu : M.u c ≤ M.ℓ w := by
      have h1 := M.monotone_u hc.2
      have h2 := M.ℓ_rec w
      have h3 : 0 ≤ ∫ y, M.ℓ (M.R * w + y) ∂M.ψ :=
        integral_nonneg fun _ => zero_le_one.trans (M.one_le_ℓ _)
      nlinarith [M.δ_pos]
    change M.u c + M.β * ∫ y, v (M.R * (w - c) + y) ∂M.ψ ≤ 0 + (1 + M.β * |C| / M.δ) * M.ℓ w
    have := mul_le_mul_of_nonneg_left hI M.β_nonneg
    have heq : M.β * (|C| * (M.ℓ w / M.δ)) = M.β * |C| / M.δ * M.ℓ w := by ring
    linarith
  exists_policy := ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩

/-- **Exercise 7.3.1** (p. 232): (U1) holds with `λ = β/δ < 1`, and (U2) holds. -/
theorem exercise_7_3_1 :
    M.wrdp.IsBlackwell (M.β / M.δ) ∧ 0 ≤ M.β / M.δ ∧ M.β / M.δ < 1 ∧
      ∀ v ∈ blPlus M.ℓ, ∃ K N : ℝ, 0 ≤ K ∧ 0 ≤ N ∧
        ∀ w, ∀ c ∈ Set.Icc 0 (max w 0), M.B w c v ≤ K + N * M.ℓ w := by
  refine ⟨fun w c hc v hv κ hκ => ?_, div_nonneg M.β_nonneg M.δ_pos.le,
    (div_lt_one M.δ_pos).2 M.β_lt_δ, M.wrdp.U2⟩
  change M.u c + M.β * ∫ y, (v (M.R * (w - c) + y) + κ * M.ℓ (M.R * (w - c) + y)) ∂M.ψ ≤
    M.u c + M.β * ∫ y, v (M.R * (w - c) + y) ∂M.ψ + M.β / M.δ * κ * M.ℓ w
  rw [integral_add (M.integrable_v hv _) ((M.integrable_ℓ _).const_mul κ), integral_const_mul]
  have h1 := mul_le_mul_of_nonneg_left (M.integral_ℓ_feasible_le (w := w) hc.1) hκ
  have h2 := mul_le_mul_of_nonneg_left h1 M.β_nonneg
  have heq : M.β * (κ * (M.ℓ w / M.δ)) = M.β / M.δ * κ * M.ℓ w := by ring
  nlinarith

/-! ### Continuity with a density -/

/-- Integrals against the density `φ`: `∫ g(s + y)ψ(dy) = ∫ g(x)φ(x − s) dx`. -/
theorem integral_shift_density {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hψ : M.ψ = Savings.densityMeasure φ) (g : ℝ → ℝ) (s : ℝ) :
    ∫ y, g (s + y) ∂M.ψ = ∫ x, g x * φ (x - s) := by
  rw [hψ, Savings.densityMeasure, integral_withDensity_eq_integral_smul
    (f := fun y => (φ y).toNNReal) hφc.measurable.real_toNNReal,
    ← integral_sub_right_eq_self (μ := volume) (fun y => (φ y).toNNReal • g (s + y)) s]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hφ0 _), smul_eq_mul, add_sub_cancel]
  ring

theorem integrable_shift_density {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hψ : M.ψ = Savings.densityMeasure φ) {g : ℝ → ℝ} {s : ℝ}
    (hg : Integrable (fun y => g (s + y)) M.ψ) : Integrable (fun x => g x * φ (x - s)) := by
  rw [hψ, Savings.densityMeasure, integrable_withDensity_iff_integrable_smul
    hφc.measurable.real_toNNReal] at hg
  refine (hg.comp_sub_right s).congr (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hφ0 _), smul_eq_mul, add_sub_cancel]
  ring

/-- `s ↦ ∫ ℓ(s + y)ψ(dy)` is continuous when `ℓ` is (dominated convergence, `ℓ` increasing). -/
theorem continuous_integral_ℓ (hℓc : Continuous M.ℓ) :
    Continuous fun s => ∫ y, M.ℓ (s + y) ∂M.ψ := by
  refine continuous_iff_continuousAt.2 fun s₀ => ?_
  refine continuousAt_of_dominated (bound := fun y => M.ℓ (s₀ + 1 + y))
    (Eventually.of_forall fun s =>
      (M.measurable_ℓ.comp (measurable_const_add s)).aestronglyMeasurable)
    ?_ (M.integrable_ℓ _) (Eventually.of_forall fun y =>
      (hℓc.comp (continuous_id.add continuous_const)).continuousAt)
  filter_upwards [Iio_mem_nhds (lt_add_one s₀)] with s hs
  refine Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (M.one_le_ℓ _))]
  exact M.monotone_ℓ (by linarith [mem_Iio.1 hs])

/-- **Exercise 7.3.2** (p. 232): if income has a continuous density `φ` and `ℓ` is continuous, then
`(w, c) ↦ B(w, c, v)` is continuous for every `v ∈ bℓX₊` (Assumption 7.2.7). -/
theorem exercise_7_3_2 (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) {v : ℝ → ℝ}
    (hv : v ∈ blPlus M.ℓ) : Continuous fun p : ℝ × ℝ => M.B p.1 p.2 v := by
  obtain ⟨hm, h0, C, hC⟩ := hv
  have hvbl : v ∈ blPlus M.ℓ := ⟨hm, h0, C, hC⟩
  -- `q_s(x) = ℓ(x)φ(x − s)`
  let q : ℝ → ℝ → ℝ := fun s x => M.ℓ x * φ (x - s)
  have hqint : ∀ s, Integrable (q s) := fun s =>
    M.integrable_shift_density hφc hφ0 hψ (M.integrable_ℓ s)
  have hvint : ∀ s, Integrable fun x => v x * φ (x - s) := fun s =>
    M.integrable_shift_density hφc hφ0 hψ (M.integrable_v hvbl s)
  have hI : Continuous fun s => ∫ y, v (s + y) ∂M.ψ := by
    refine continuous_iff_continuousAt.2 fun s₀ => ?_
    have hS := scheffe_general (μ := volume) (l := 𝓝 s₀) (q := q) (q₀ := q s₀)
      (fun s x => mul_nonneg (zero_le_one.trans (M.one_le_ℓ x)) (hφ0 _))
      (fun x => mul_nonneg (zero_le_one.trans (M.one_le_ℓ x)) (hφ0 _)) hqint (hqint s₀)
      (Eventually.of_forall fun x =>
        ((hφc.comp (continuous_const.sub continuous_id)).tendsto s₀).const_mul (M.ℓ x))
      (by
        have h := (M.continuous_integral_ℓ hℓc).tendsto s₀
        simp only [M.integral_shift_density hφc hφ0 hψ M.ℓ] at h
        exact h)
    refine tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' ?_ (by simpa using hS.const_mul |C|))
    refine Eventually.of_forall fun s => ?_
    dsimp only
    rw [M.integral_shift_density hφc hφ0 hψ v s, M.integral_shift_density hφc hφ0 hψ v s₀,
      ← integral_sub (hvint s) (hvint s₀), ← integral_const_mul]
    refine norm_integral_le_of_norm_le (((hqint s).sub (hqint s₀)).abs.const_mul _)
      (Eventually.of_forall fun x => ?_)
    have hl : 0 ≤ M.ℓ x := zero_le_one.trans (M.one_le_ℓ x)
    have hvx : |v x| ≤ |C| * M.ℓ x := by
      rw [abs_of_nonneg (h0 x)]
      exact (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hl)
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, show q s x - q s₀ x = M.ℓ x * (φ (x - s) - φ (x - s₀))
      from by ring, abs_mul, abs_of_nonneg hl, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hvx (abs_nonneg _)
  exact (M.continuous_u.comp continuous_snd).add (continuous_const.mul
    (hI.comp ((continuous_const.mul (continuous_fst.sub continuous_snd)))))

theorem hasMaxSelections : HasMaxSelections M.wrdp.Γ :=
  hasMaxSelections_Icc (g := fun _ => 0) (h := fun w => max w 0) continuous_const
    (continuous_id.max continuous_const) fun _ => le_max_right _ _

/-- The savings model with a continuous income density satisfies the conditions of
Proposition 7.2.5, with Assumption 7.2.7 (Exercises 7.3.1 and 7.3.2). -/
theorem continuousCase (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) : M.wrdp.ContinuousCase :=
  ⟨hℓc, M.hasMaxSelections, ⟨_, M.exercise_7_3_1.2.1, M.exercise_7_3_1.2.2.1,
    M.exercise_7_3_1.1⟩, fun _ hv _ => (M.exercise_7_3_2 hℓc hφc hφ0 hψ hv).continuousOn⟩

/-- §7.3.1 (p. 232): the conclusions of Proposition 7.2.5 hold: the fundamental optimality
properties, `v* ∈ bℓcℝ₊` satisfies the Bellman equation, VFI converges geometrically on `bℓcℝ₊`,
and OPI and HPI converge. -/
theorem section_7_3_1 (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) :
    ∃ hw : M.wrdp.toRDP.adp.WellPosed, M.wrdp.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ bcPlus ℝ, Continuous (wev M.ℓ vstar) ∧
        M.wrdp.toRDP.adp.VFIGeometric (bcPlus ℝ) vstar ∧
        ∀ g, M.wrdp.toRDP.adp.IsSelector g →
          M.wrdp.toRDP.adp.OPIConverges g vstar ∧ M.wrdp.toRDP.adp.HPIConverges hw g vstar := by
  obtain ⟨hw, hFO, vstar, hv, hvc, hgeo, hconv⟩ := M.wrdp.proposition_7_2_5 hℓc
    M.hasMaxSelections M.exercise_7_3_1.2.1 M.exercise_7_3_1.2.2.1 M.exercise_7_3_1.1
    fun _ hv _ => (M.exercise_7_3_2 hℓc hφc hφ0 hψ hv).continuousOn
  exact ⟨hw, hFO, vstar, hv, hvc, hgeo,
    hconv fun _ hv => (M.exercise_7_3_2 hℓc hφc hφ0 hψ hv).continuousOn⟩

/-! ### Shape of the value function and the optimal policy -/

/-- **Exercise 7.2.2** (p. 224): Assumption 7.2.8 holds: `Γ` is increasing and
`B(w, c, v) ≤ B(w', c, v)` for `w ≤ w'`, `c ∈ Γ(w)` and increasing `v`. -/
theorem exercise_7_2_2 :
    (∀ w w', w ≤ w' → M.wrdp.Γ w ⊆ M.wrdp.Γ w') ∧
      ∀ w w', w ≤ w' → ∀ v ∈ blPlus M.ℓ, Continuous v → Monotone v →
        ∀ c ∈ M.wrdp.Γ w, M.wrdp.B w c v ≤ M.wrdp.B w' c v := by
  refine ⟨fun w w' h => Icc_subset_Icc le_rfl (max_le_max h le_rfl),
    fun w w' h v hv _ hmono c _ => ?_⟩
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono (M.integrable_v hv _)
    (M.integrable_v hv _) fun y => hmono ?_) M.β_nonneg)
  have := mul_le_mul_of_nonneg_left h M.R_nonneg
  linarith

/-- Under Exercise 7.2.2, `v*` is increasing (Proposition 7.2.6). -/
theorem vstar_monotone (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) :
    ∃ vstar, M.wrdp.toRDP.adp.IsValueFunction vstar ∧ Monotone (wev M.ℓ vstar) := by
  obtain ⟨-, -, vstar, -, hv, hmono⟩ := WRDP.proposition_7_2_6 (M.continuousCase hℓc hφc hφ0 hψ)
    M.exercise_7_2_2.1 M.exercise_7_2_2.2
  exact ⟨vstar, hv, hmono⟩

/-- The feasible pairs with `w ≥ 0`, `{(w, c) : 0 ≤ c ≤ w}`, form a convex set. -/
theorem convex_feasibleOn : Convex ℝ (WRDP.feasibleOn M.wrdp.Γ (Ici 0)) := by
  rintro ⟨w₁, c₁⟩ ⟨hw₁, hc₁⟩ ⟨w₂, c₂⟩ ⟨hw₂, hc₂⟩ a b ha hb hab
  have h1 : (0 : ℝ) ≤ w₁ := hw₁
  have h2 : (0 : ℝ) ≤ w₂ := hw₂
  change c₁ ∈ Icc 0 (max w₁ 0) at hc₁
  change c₂ ∈ Icc 0 (max w₂ 0) at hc₂
  rw [max_eq_left h1] at hc₁
  rw [max_eq_left h2] at hc₂
  change (0 : ℝ) ≤ a * w₁ + b * w₂ ∧ a * c₁ + b * c₂ ∈ Icc 0 (max (a * w₁ + b * w₂) 0)
  refine ⟨by positivity, ⟨by nlinarith [hc₁.1, hc₂.1], le_max_of_le_left ?_⟩⟩
  nlinarith [hc₁.2, hc₂.2]

/-- The integral term is concave in `(w, c)` over feasible pairs, for `v` concave on `ℝ₊`, when
income is nonnegative. -/
theorem integral_concave (hψ0 : ∀ᵐ y ∂M.ψ, 0 ≤ y) {v : ℝ → ℝ} (hv : v ∈ blPlus M.ℓ)
    (hconc : ConcaveOn ℝ (Ici 0) v) {w₁ c₁ w₂ c₂ a b : ℝ} (hc₁ : c₁ ≤ w₁) (hc₂ : c₂ ≤ w₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * ∫ y, v (M.R * (w₁ - c₁) + y) ∂M.ψ + b * ∫ y, v (M.R * (w₂ - c₂) + y) ∂M.ψ ≤
      ∫ y, v (M.R * ((a * w₁ + b * w₂) - (a * c₁ + b * c₂)) + y) ∂M.ψ := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((M.integrable_v hv _).const_mul a) ((M.integrable_v hv _).const_mul b)]
  refine integral_mono_ae (((M.integrable_v hv _).const_mul a).add
    ((M.integrable_v hv _).const_mul b)) (M.integrable_v hv _) ?_
  filter_upwards [hψ0] with y hy
  have hx₁ : M.R * (w₁ - c₁) + y ∈ Ici (0 : ℝ) :=
    add_nonneg (mul_nonneg M.R_nonneg (sub_nonneg.2 hc₁)) hy
  have hx₂ : M.R * (w₂ - c₂) + y ∈ Ici (0 : ℝ) :=
    add_nonneg (mul_nonneg M.R_nonneg (sub_nonneg.2 hc₂)) hy
  have := hconc.2 hx₁ hx₂ ha hb hab
  simp only [smul_eq_mul] at this
  have heq : a * (M.R * (w₁ - c₁) + y) + b * (M.R * (w₂ - c₂) + y) =
      M.R * ((a * w₁ + b * w₂) - (a * c₁ + b * c₂)) + y := by
    linear_combination y * hab
  rw [heq] at this
  exact this

/-- **Exercise 7.2.3** (p. 224): if `u` is also concave on `ℝ₊` and income is nonnegative, then
`v*` is increasing and concave on `ℝ₊` (Propositions 7.2.6 and 7.2.7). -/
theorem exercise_7_2_3 (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) (hψ0 : ∀ᵐ y ∂M.ψ, 0 ≤ y)
    (hu : ConcaveOn ℝ (Ici 0) M.u) :
    ∃ vstar, M.wrdp.toRDP.adp.IsValueFunction vstar ∧ Monotone (wev M.ℓ vstar) ∧
      ConcaveOn ℝ (Ici 0) (wev M.ℓ vstar) := by
  have hBc : ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ (Ici 0) v →
      ConcaveOn ℝ (WRDP.feasibleOn M.wrdp.Γ (Ici 0)) fun p => M.wrdp.B p.1 p.2 v := by
    intro v hv _ hconc
    refine ⟨M.convex_feasibleOn, ?_⟩
    rintro ⟨w₁, c₁⟩ ⟨hw₁, hc₁⟩ ⟨w₂, c₂⟩ ⟨hw₂, hc₂⟩ a b ha hb hab
    have h1 : (0 : ℝ) ≤ w₁ := hw₁
    have h2 : (0 : ℝ) ≤ w₂ := hw₂
    change c₁ ∈ Icc 0 (max w₁ 0) at hc₁
    change c₂ ∈ Icc 0 (max w₂ 0) at hc₂
    rw [max_eq_left h1] at hc₁
    rw [max_eq_left h2] at hc₂
    have hU := hu.2 (mem_Ici.2 hc₁.1) (mem_Ici.2 hc₂.1) ha hb hab
    have hI := M.integral_concave hψ0 hv hconc hc₁.2 hc₂.2 ha hb hab
    simp only [smul_eq_mul] at hU
    change a * (M.u c₁ + M.β * ∫ y, v (M.R * (w₁ - c₁) + y) ∂M.ψ) +
        b * (M.u c₂ + M.β * ∫ y, v (M.R * (w₂ - c₂) + y) ∂M.ψ) ≤
      M.u (a * c₁ + b * c₂) +
        M.β * ∫ y, v (M.R * ((a * w₁ + b * w₂) - (a * c₁ + b * c₂)) + y) ∂M.ψ
    nlinarith [mul_le_mul_of_nonneg_left hI M.β_nonneg]
  obtain ⟨-, -, v₁, -, hv₁, hconc⟩ := WRDP.proposition_7_2_7 (M.continuousCase hℓc hφc hφ0 hψ)
    (convex_Ici 0) M.convex_feasibleOn hBc
  obtain ⟨v₂, hv₂, hmono⟩ := M.vstar_monotone hℓc hφc hφ0 hψ
  rw [hv₂.unique hv₁] at hmono
  exact ⟨v₁, hv₁, hmono, hconc⟩

/-- **Exercise 7.2.4** (p. 225): if `u` is strictly concave on `ℝ₊` and income is nonnegative,
the optimal policy is unique and continuous (Proposition 7.2.8). -/
theorem exercise_7_2_4 (hℓc : Continuous M.ℓ) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hψ : M.ψ = Savings.densityMeasure φ) (hψ0 : ∀ᵐ y ∂M.ψ, 0 ≤ y)
    (hu : StrictConcaveOn ℝ (Ici 0) M.u) :
    ∃ hw : M.wrdp.toRDP.adp.WellPosed, M.wrdp.toRDP.adp.FundamentalOptimality hw ∧
      ∃ σ, M.wrdp.toRDP.adp.IsOptimal hw σ ∧ (∀ τ, M.wrdp.toRDP.adp.IsOptimal hw τ → τ = σ) ∧
        Continuous σ.1 := by
  have hBc : ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ (Ici 0) v →
      ConcaveOn ℝ (WRDP.feasibleOn M.wrdp.Γ (Ici 0)) fun p => M.wrdp.B p.1 p.2 v := by
    intro v hv _ hconc
    refine ⟨M.convex_feasibleOn, ?_⟩
    rintro ⟨w₁, c₁⟩ ⟨hw₁, hc₁⟩ ⟨w₂, c₂⟩ ⟨hw₂, hc₂⟩ a b ha hb hab
    have h1 : (0 : ℝ) ≤ w₁ := hw₁
    have h2 : (0 : ℝ) ≤ w₂ := hw₂
    change c₁ ∈ Icc 0 (max w₁ 0) at hc₁
    change c₂ ∈ Icc 0 (max w₂ 0) at hc₂
    rw [max_eq_left h1] at hc₁
    rw [max_eq_left h2] at hc₂
    have hU := hu.concaveOn.2 (mem_Ici.2 hc₁.1) (mem_Ici.2 hc₂.1) ha hb hab
    have hI := M.integral_concave hψ0 hv hconc hc₁.2 hc₂.2 ha hb hab
    simp only [smul_eq_mul] at hU
    change a * (M.u c₁ + M.β * ∫ y, v (M.R * (w₁ - c₁) + y) ∂M.ψ) +
        b * (M.u c₂ + M.β * ∫ y, v (M.R * (w₂ - c₂) + y) ∂M.ψ) ≤
      M.u (a * c₁ + b * c₂) +
        M.β * ∫ y, v (M.R * ((a * w₁ + b * w₂) - (a * c₁ + b * c₂)) + y) ∂M.ψ
    nlinarith [mul_le_mul_of_nonneg_left hI M.β_nonneg]
  have hstrict : ∀ w, ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ (Ici 0) v →
      StrictConcaveOn ℝ (M.wrdp.Γ w) fun c => M.wrdp.B w c v := by
    intro w v hv _ hconc
    change StrictConcaveOn ℝ (Icc 0 (max w 0)) fun c =>
      M.u c + M.β * ∫ y, v (M.R * (w - c) + y) ∂M.ψ
    rcases le_or_gt 0 w with hw | hw
    · rw [max_eq_left hw]
      have hconcI : ConcaveOn ℝ (Icc 0 w) fun c => M.β * ∫ y, v (M.R * (w - c) + y) ∂M.ψ := by
        refine ⟨convex_Icc 0 w, fun c₁ hc₁ c₂ hc₂ a b ha hb hab => ?_⟩
        have hI := M.integral_concave (w₁ := w) (w₂ := w) hψ0 hv hconc hc₁.2 hc₂.2 ha hb hab
        have hw' : a * w + b * w = w := by rw [← add_mul, hab, one_mul]
        rw [hw'] at hI
        simp only [smul_eq_mul]
        nlinarith [mul_le_mul_of_nonneg_left hI M.β_nonneg]
      exact (hu.subset Icc_subset_Ici_self (convex_Icc 0 w)).add_concaveOn hconcI
    · rw [max_eq_right hw.le]
      refine ⟨convex_Icc 0 0, fun x hx y hy hxy => absurd ?_ hxy⟩
      rw [le_antisymm hx.2 hx.1, le_antisymm hy.2 hy.1]
  obtain ⟨hw, hFO, σ, hσ, huniq, hcont⟩ := WRDP.proposition_7_2_8 (M.continuousCase hℓc hφc hφ0 hψ)
    (convex_Ici 0) M.convex_feasibleOn hBc hstrict
  exact ⟨hw, hFO, σ, hσ, huniq, hcont (hasContinuousUniqueMax_Icc continuous_const
    (continuous_id.max continuous_const) fun _ => le_max_right _ _)⟩

end SavingsU

end SargentStachurski.RecursiveDecisionProcesses

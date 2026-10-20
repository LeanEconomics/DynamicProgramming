/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManySectorSecurities

/-!
# Pricing securities: Exercise 16.2(c) for a Feller transition on a compact shock space

SLP §16.2, p. 483. As in `ManySectorSecurities`, but the next shock `z′` has a general law
`Q(s, ·)` on a **compact** shock space `Z` (a probability measure on the Borel sets), the
transition `s ↦ Q(s, ·)` is **Feller** (continuous into the probability measures with the weak
topology), and the return `R(s, z′) ≥ 0` and next state `nxt(s, z′)` are jointly continuous:

  (1) `w(A, s) = max {U(c(s) + A − q(s) b) + β ∫ w(b R(s, z′), nxt(s, z′)) Q(s, dz′) :
        b ≥ B, q(s) b ≤ c(s) + A}`.

(For the book, `s = (x, z)`, `nxt(s, z′) = (g(x, z), z′)`, `R = f(z′)` with `f` continuous.)

* `msFE_continuous`: for bounded continuous `w`, `(s, b) ↦ ∫ w(b R(s, z′), nxt(s, z′)) Q(s, dz′)` is
  continuous: uniform convergence of the integrands (the tube lemma on the compact `Z`) plus weak
  convergence of `Q(s, ·)`. (No local compactness of the state space is needed: the tube lemma
  over the compact `Z` gives the uniform estimate.)
* `ms_fellerBellman_unique`: (1) has at most one bounded continuous solution on `D`.
* `msFellerTB`, `ms_fellerTB_contracting`: the operator of (1) on bounded continuous functions, a
  contraction of modulus `β`.
* **Exercise 16.2(c), Feller version** (`ex_16_2c_feller`): there is exactly one bounded continuous
  `w` satisfying (1) on `D`.

**Correction (NOTE (iii) to Ex 16.2c).** Continuity needs `f` (here `R`) continuous and `Q` Feller;
with `Z` compact these suffice. The domain condition of `ManySectorSecurities` is still needed.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set
open scoped BoundedContinuousFunction

variable {Sx : Type*} [TopologicalSpace Sx]
  {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]

variable (U : ℝ → ℝ) (c q : Sx → ℝ) (R : Sx → Z → ℝ) (Q : Sx → ProbabilityMeasure Z)
  (nxt : Sx → Z → Sx) in
/-- The data of (1) with a Feller transition `Q` on a compact shock space, with the domain
condition `q(s′)B − c(s′) ≤ B R(s, z′)`. -/
structure MsFellerData (B β : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  B_neg : B < 0
  U_cont : Continuous U
  U_bdd : ∃ M, ∀ x, |U x| ≤ M
  c_cont : Continuous c
  q_cont : Continuous q
  q_pos : ∀ s, 0 < q s
  R_cont : Continuous fun p : Sx × Z => R p.1 p.2
  R_nonneg : ∀ s z', 0 ≤ R s z'
  Q_cont : Continuous Q
  nxt_cont : Continuous fun p : Sx × Z => nxt p.1 p.2
  dom : ∀ s z', q (nxt s z') * B - c (nxt s z') ≤ B * R s z'

/-- The expected continuation value `∫ w(b R(s, z′), nxt(s, z′)) Q(s, dz′)`. -/
noncomputable def msFE (R : Sx → Z → ℝ) (Q : Sx → ProbabilityMeasure Z) (nxt : Sx → Z → Sx)
    (w : ℝ × Sx → ℝ) (s : Sx) (b : ℝ) : ℝ :=
  ∫ z', w (b * R s z', nxt s z') ∂(Q s : Measure Z)

/-- The objective of (1). -/
noncomputable def msFObj (U : ℝ → ℝ) (c q : Sx → ℝ) (R : Sx → Z → ℝ)
    (Q : Sx → ProbabilityMeasure Z) (nxt : Sx → Z → Sx) (β : ℝ) (w : ℝ × Sx → ℝ) (A : ℝ)
    (s : Sx) (b : ℝ) : ℝ :=
  U (c s + A - q s * b) + β * msFE R Q nxt w s b

/-- `w` **satisfies (1) on `D`** (with "max"). -/
def MsFellerBellman (U : ℝ → ℝ) (c q : Sx → ℝ) (R : Sx → Z → ℝ) (Q : Sx → ProbabilityMeasure Z)
    (nxt : Sx → Z → Sx) (B β : ℝ) (w : ℝ × Sx → ℝ) : Prop :=
  ∀ A s, q s * B - c s ≤ A →
    (∀ b, B ≤ b → q s * b ≤ c s + A → msFObj U c q R Q nxt β w A s b ≤ w (A, s)) ∧
    ∃ b, B ≤ b ∧ q s * b ≤ c s + A ∧ w (A, s) = msFObj U c q R Q nxt β w A s b

variable {U : ℝ → ℝ} {c q : Sx → ℝ} {R : Sx → Z → ℝ} {Q : Sx → ProbabilityMeasure Z}
  {nxt : Sx → Z → Sx} {B β : ℝ}

omit [CompactSpace Z] in
/-- Feasible purchases lead to states in `D`. -/
theorem ms_feller_next_mem (D : MsFellerData U c q R Q nxt B β) (s : Sx) {b : ℝ} (hb : B ≤ b)
    (z' : Z) : (b * R s z', nxt s z') ∈ msSecDom c q B := by
  have h1 := D.dom s z'
  have h2 := D.R_nonneg s z'
  change q (nxt s z') * B - c (nxt s z') ≤ b * R s z'
  nlinarith

omit [CompactSpace Z] in
/-- The integrand is continuous in `z′`, hence integrable (bounded, probability measure). -/
theorem ms_feller_integrable (D : MsFellerData U c q R Q nxt B β) (w : ℝ × Sx →ᵇ ℝ) (s : Sx)
    (b : ℝ) : Integrable (fun z' => w (b * R s z', nxt s z')) (Q s : Measure Z) := by
  have hc : Continuous fun z' : Z => w (b * R s z', nxt s z') :=
    w.continuous.comp ((continuous_const.mul (D.R_cont.comp (continuous_const.prodMk
      continuous_id))).prodMk (D.nxt_cont.comp (continuous_const.prodMk continuous_id)))
  exact Integrable.of_bound hc.aestronglyMeasurable ‖w‖ (Eventually.of_forall fun z' =>
    w.norm_coe_le_norm _)

omit [CompactSpace Z] in
/-- `|∫ u − ∫ v| ≤ C` when `|u − v| ≤ C` on the relevant points. -/
theorem ms_feller_sub_le (D : MsFellerData U c q R Q nxt B β) (w w' : ℝ × Sx →ᵇ ℝ) (s : Sx)
    (b : ℝ) {C : ℝ}
    (h : ∀ z', |w (b * R s z', nxt s z') - w' (b * R s z', nxt s z')| ≤ C) :
    |msFE R Q nxt w s b - msFE R Q nxt w' s b| ≤ C := by
  rw [msFE, msFE, ← integral_sub (ms_feller_integrable D w s b) (ms_feller_integrable D w' s b)]
  have := norm_integral_le_of_norm_le_const (μ := (Q s : Measure Z))
    (f := fun z' => w (b * R s z', nxt s z') - w' (b * R s z', nxt s z')) (C := C)
    (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact h z')
  simpa [probReal_univ] using this

/-- **Continuity of the expected continuation value** (the Feller property and the tube
lemma). -/
theorem msFE_continuous (D : MsFellerData U c q R Q nxt B β) (w : ℝ × Sx →ᵇ ℝ) :
    Continuous fun p : Sx × ℝ => msFE R Q nxt w p.1 p.2 := by
  set φ : Sx × ℝ → Z → ℝ := fun p z' => w (p.2 * R p.1 z', nxt p.1 z') with hφdef
  have hφ : Continuous fun r : (Sx × ℝ) × Z => φ r.1 r.2 :=
    w.continuous.comp (((continuous_snd.comp continuous_fst).mul (D.R_cont.comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd))).prodMk
      (D.nxt_cont.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)))
  rw [continuous_iff_continuousAt]
  intro p₀
  set g : Z →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨φ p₀, hφ.comp (continuous_const.prodMk continuous_id)⟩ with hg
  have h2 : Tendsto (fun p : Sx × ℝ => ∫ z', g z' ∂(Q p.1 : Measure Z)) (𝓝 p₀)
      (𝓝 (∫ z', g z' ∂(Q p₀.1 : Measure Z))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
      ((D.Q_cont.tendsto p₀.1).comp (continuous_fst.tendsto p₀))) g
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have e1 : ∀ᶠ p in 𝓝 p₀, ∀ z' ∈ (univ : Set Z), |φ p z' - φ p₀ z'| < ε / 2 :=
    isCompact_univ.eventually_forall_of_forall_eventually fun y _ => by
      have hcont : Continuous fun r : (Sx × ℝ) × Z => |φ r.1 r.2 - φ p₀ r.2| :=
        continuous_abs.comp (hφ.sub (hφ.comp (continuous_const.prodMk continuous_snd)))
      have := hcont.tendsto (p₀, y)
      simp only [sub_self, abs_zero] at this
      exact this.eventually_lt_const (half_pos hε)
  have e2 := (Metric.tendsto_nhds.1 h2) (ε / 2) (half_pos hε)
  filter_upwards [e1, e2] with p hp1 hp2
  have hint1 := ms_feller_integrable D w p.1 p.2
  have hint0 : Integrable (fun z' => g z') (Q p.1 : Measure Z) :=
    Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖
      (Eventually.of_forall fun z' => g.norm_coe_le_norm z')
  have hA : |msFE R Q nxt w p.1 p.2 - ∫ z', g z' ∂(Q p.1 : Measure Z)| ≤ ε / 2 := by
    rw [msFE, ← integral_sub hint1 hint0]
    have := norm_integral_le_of_norm_le_const (μ := (Q p.1 : Measure Z))
      (f := fun z' => w (p.2 * R p.1 z', nxt p.1 z') - g z') (C := ε / 2)
      (Eventually.of_forall fun z' => by
        rw [Real.norm_eq_abs]
        exact (hp1 z' (mem_univ _)).le)
    simpa [probReal_univ] using this
  have hg0 : ∫ z', g z' ∂(Q p₀.1 : Measure Z) = msFE R Q nxt w p₀.1 p₀.2 := rfl
  rw [Real.dist_eq] at hp2 ⊢
  rw [hg0] at hp2
  calc |msFE R Q nxt w p.1 p.2 - msFE R Q nxt w p₀.1 p₀.2|
      ≤ |msFE R Q nxt w p.1 p.2 - ∫ z', g z' ∂(Q p.1 : Measure Z)| +
          |∫ z', g z' ∂(Q p.1 : Measure Z) - msFE R Q nxt w p₀.1 p₀.2| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hA hp2
    _ = ε := by ring

omit [CompactSpace Z] in
/-- **At most one bounded continuous solution of (1) on `D`**. -/
theorem ms_fellerBellman_unique (D : MsFellerData U c q R Q nxt B β) {w w' : ℝ × Sx →ᵇ ℝ}
    (hw : MsFellerBellman U c q R Q nxt B β w) (hw' : MsFellerBellman U c q R Q nxt B β w') :
    ∀ p ∈ msSecDom c q B, w p = w' p := by
  have key : ∀ n, ∀ p ∈ msSecDom c q B, |w p - w' p| ≤ β ^ n * (‖w‖ + ‖w'‖) := by
    intro n
    induction n with
    | zero =>
      intro p _
      rw [pow_zero, one_mul]
      have h1 : |w p| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact w.norm_coe_le_norm p
      have h2 : |w' p| ≤ ‖w'‖ := by rw [← Real.norm_eq_abs]; exact w'.norm_coe_le_norm p
      exact (abs_sub _ _).trans (add_le_add h1 h2)
    | succ n ih =>
      rintro ⟨A, s⟩ hp
      obtain ⟨b₁, hb₁, hf₁, e₁⟩ := (hw A s hp).2
      obtain ⟨b₂, hb₂, hf₂, e₂⟩ := (hw' A s hp).2
      have a1 := (hw' A s hp).1 b₁ hb₁ hf₁
      have a2 := (hw A s hp).1 b₂ hb₂ hf₂
      have d1 := ms_feller_sub_le D w w' s b₁ fun z' => ih _ (ms_feller_next_mem D s hb₁ z')
      have d2 := ms_feller_sub_le D w w' s b₂ fun z' => ih _ (ms_feller_next_mem D s hb₂ z')
      simp only [msFObj] at e₁ e₂ a1 a2
      have hβ := D.beta_pos
      rw [pow_succ, mul_comm (β ^ n) β, mul_assoc]
      refine abs_le.2 ⟨?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d2).1 hβ.le]
      · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d1).2 hβ.le]
  intro p hp
  have hlim : Tendsto (fun n : ℕ => β ^ n * (‖w‖ + ‖w'‖)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one D.beta_pos.le D.beta_lt_one).mul_const _
  have : |w p - w' p| ≤ 0 := ge_of_tendsto' hlim fun n => key n p hp
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-! ### Existence -/

/-- **The operator of (1)** with purchases `b = msSecB A s r`, `r ∈ [0, 1]`. -/
noncomputable def msFellerT (U : ℝ → ℝ) (c q : Sx → ℝ) (R : Sx → Z → ℝ)
    (Q : Sx → ProbabilityMeasure Z) (nxt : Sx → Z → Sx) (B β : ℝ) (w : ℝ × Sx → ℝ)
    (p : ℝ × Sx) : ℝ :=
  sSup ((fun r => msFObj U c q R Q nxt β w p.1 p.2 (msSecB c q B p.1 p.2 r)) '' Icc 0 1)

/-- The objective along `b = msSecB A s r` is jointly continuous. -/
theorem msFObj_continuous (D : MsFellerData U c q R Q nxt B β) (w : ℝ × Sx →ᵇ ℝ) :
    Continuous fun r : (ℝ × Sx) × ℝ =>
      msFObj U c q R Q nxt β w r.1.1 r.1.2 (msSecB c q B r.1.1 r.1.2 r.2) := by
  have hc : Continuous fun r : (ℝ × Sx) × ℝ => c r.1.2 :=
    D.c_cont.comp (continuous_snd.comp continuous_fst)
  have hq : Continuous fun r : (ℝ × Sx) × ℝ => q r.1.2 :=
    D.q_cont.comp (continuous_snd.comp continuous_fst)
  have hA : Continuous fun r : (ℝ × Sx) × ℝ => r.1.1 := continuous_fst.comp continuous_fst
  have hb : Continuous fun r : (ℝ × Sx) × ℝ => msSecB c q B r.1.1 r.1.2 r.2 :=
    continuous_const.add (continuous_snd.mul (continuous_const.max
      (((hc.add hA).div hq fun r => (D.q_pos _).ne').sub continuous_const)))
  unfold msFObj
  exact (D.U_cont.comp ((hc.add hA).sub (hq.mul hb))).add (continuous_const.mul
    ((msFE_continuous D w).comp ((continuous_snd.comp continuous_fst).prodMk hb)))

omit [CompactSpace Z] in
/-- The objective is bounded by `M + β ‖w‖`. -/
theorem msFObj_abs_le (D : MsFellerData U c q R Q nxt B β) {M : ℝ} (hM : ∀ x, |U x| ≤ M)
    (w : ℝ × Sx →ᵇ ℝ) (A : ℝ) (s : Sx) (b : ℝ) :
    |msFObj U c q R Q nxt β w A s b| ≤ M + β * ‖w‖ := by
  have h0 : |msFE R Q nxt w s b| ≤ ‖w‖ := by
    have := norm_integral_le_of_norm_le_const (μ := (Q s : Measure Z))
      (f := fun z' => w (b * R s z', nxt s z')) (C := ‖w‖)
      (Eventually.of_forall fun z' => w.norm_coe_le_norm _)
    simpa [probReal_univ, msFE] using this
  unfold msFObj
  calc |U (c s + A - q s * b) + β * msFE R Q nxt w s b|
      ≤ |U (c s + A - q s * b)| + |β * msFE R Q nxt w s b| := abs_add_le _ _
    _ ≤ M + β * ‖w‖ := by
        rw [abs_mul, abs_of_pos D.beta_pos]
        exact add_le_add (hM _) (mul_le_mul_of_nonneg_left h0 D.beta_pos.le)

/-- The maximum defining `Tw` is attained. -/
theorem msFellerT_attained (D : MsFellerData U c q R Q nxt B β) (w : ℝ × Sx →ᵇ ℝ)
    (p : ℝ × Sx) : ∃ r ∈ Icc (0 : ℝ) 1, msFellerT U c q R Q nxt B β w p =
      msFObj U c q R Q nxt β w p.1 p.2 (msSecB c q B p.1 p.2 r) :=
  isCompact_Icc.exists_sSup_image_eq (nonempty_Icc.2 zero_le_one)
    ((msFObj_continuous D w).comp (continuous_const.prodMk continuous_id)).continuousOn

/-- `Tw` dominates the objective at every `r ∈ [0, 1]`. -/
theorem msFellerT_ge (D : MsFellerData U c q R Q nxt B β) (w : ℝ × Sx →ᵇ ℝ) (p : ℝ × Sx)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    msFObj U c q R Q nxt β w p.1 p.2 (msSecB c q B p.1 p.2 r) ≤ msFellerT U c q R Q nxt B β w p :=
  le_csSup (isCompact_Icc.image ((msFObj_continuous D w).comp
    (continuous_const.prodMk continuous_id))).bddAbove (mem_image_of_mem _ hr)

omit [TopologicalSpace Sx] in
/-- On `D` every feasible purchase is `msSecB A s r` for some `r ∈ [0, 1]`. -/
theorem msFB_surj (hq : ∀ s, 0 < q s) {A : ℝ} {s : Sx} (hp : q s * B - c s ≤ A) {b : ℝ}
    (hb : B ≤ b) (hf : q s * b ≤ c s + A) : ∃ r ∈ Icc (0 : ℝ) 1, msSecB c q B A s r = b := by
  have hq := hq s
  have hgap : 0 ≤ (c s + A) / q s - B := by
    rw [sub_nonneg, le_div_iff₀ hq]; linarith
  have hbB : b ≤ (c s + A) / q s := by rw [le_div_iff₀ hq]; linarith
  rcases hgap.lt_or_eq with hlt | heq
  · refine ⟨(b - B) / ((c s + A) / q s - B), ⟨div_nonneg (by linarith) hlt.le,
      (div_le_one hlt).2 (by linarith)⟩, ?_⟩
    rw [msSecB, max_eq_right hlt.le, div_mul_cancel₀ _ hlt.ne']
    ring
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [msSecB, zero_mul, add_zero]
    linarith

omit [TopologicalSpace Sx] in
/-- On `D`, `msSecB A s r` is feasible for `r ∈ [0, 1]`. -/
theorem msFB_feasible (hq : ∀ s, 0 < q s) {A : ℝ} {s : Sx} (hp : q s * B - c s ≤ A) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) : B ≤ msSecB c q B A s r ∧ q s * msSecB c q B A s r ≤ c s + A := by
  have hq := hq s
  have hgap : 0 ≤ (c s + A) / q s - B := by
    rw [sub_nonneg, le_div_iff₀ hq]; linarith
  simp only [msSecB, max_eq_right hgap]
  refine ⟨by nlinarith [hr.1], ?_⟩
  have h1 : B + r * ((c s + A) / q s - B) ≤ (c s + A) / q s := by nlinarith [hr.2]
  rw [le_div_iff₀ hq] at h1
  linarith

/-- The operator of (1) on bounded continuous functions on `ℝ × S`. -/
noncomputable def msFellerTB (D : MsFellerData U c q R Q nxt B β) (w : ℝ × Sx →ᵇ ℝ) :
    ℝ × Sx →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (msFellerT U c q R Q nxt B β w)
    (isCompact_Icc.continuous_sSup (msFObj_continuous D w))
    (Classical.choose D.U_bdd + β * ‖w‖) fun p => by
      rw [Real.norm_eq_abs]
      obtain ⟨r, -, e⟩ := msFellerT_attained D w p
      rw [e]
      exact msFObj_abs_le D (Classical.choose_spec D.U_bdd) w _ _ _

/-- Values of `msFellerTB`. -/
theorem msFellerTB_apply (D : MsFellerData U c q R Q nxt B β) (w : ℝ × Sx →ᵇ ℝ) (p : ℝ × Sx) :
    msFellerTB D w p = msFellerT U c q R Q nxt B β w p := rfl

/-- **Blackwell**: the operator of (1) is a contraction of modulus `β`. -/
theorem ms_fellerTB_contracting (D : MsFellerData U c q R Q nxt B β) :
    ContractingWith ⟨β, D.beta_pos.le⟩ (msFellerTB D) := by
  refine ⟨D.beta_lt_one, LipschitzWith.of_dist_le_mul fun w w' => ?_⟩
  refine (BoundedContinuousFunction.dist_le (mul_nonneg D.beta_pos.le dist_nonneg)).2 fun p => ?_
  rw [Real.dist_eq, msFellerTB_apply, msFellerTB_apply]
  obtain ⟨r₁, hr₁, e₁⟩ := msFellerT_attained D w p
  obtain ⟨r₂, hr₂, e₂⟩ := msFellerT_attained D w' p
  have a1 := msFellerT_ge D w' p hr₁
  have a2 := msFellerT_ge D w p hr₂
  have hd : ∀ b, |msFE R Q nxt w p.2 b - msFE R Q nxt w' p.2 b| ≤ dist w w' := fun b =>
    ms_feller_sub_le D w w' p.2 b fun z' => by
      rw [← Real.dist_eq]; exact BoundedContinuousFunction.dist_coe_le_dist _
  have d1 := hd (msSecB c q B p.1 p.2 r₁)
  have d2 := hd (msSecB c q B p.1 p.2 r₂)
  simp only [msFObj] at e₁ e₂ a1 a2
  have hβ := D.beta_pos
  refine abs_le.2 ⟨?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d2).1 hβ.le]
  · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d1).2 hβ.le]

/-- A fixed point of the operator satisfies (1) on `D`. -/
theorem ms_fellerBellman_of_fixed (D : MsFellerData U c q R Q nxt B β) {w : ℝ × Sx →ᵇ ℝ}
    (hfix : msFellerTB D w = w) : MsFellerBellman U c q R Q nxt B β w := by
  intro A s hp
  have hwp : w (A, s) = msFellerT U c q R Q nxt B β w (A, s) := by
    rw [← msFellerTB_apply D w (A, s), hfix]
  refine ⟨fun b hb hf => ?_, ?_⟩
  · obtain ⟨r, hr, hrb⟩ := msFB_surj D.q_pos hp hb hf
    have := msFellerT_ge D w (A, s) hr
    rw [hrb] at this
    rw [hwp]
    exact this
  · obtain ⟨r, hr, e⟩ := msFellerT_attained D w (A, s)
    obtain ⟨h1, h2⟩ := msFB_feasible D.q_pos hp hr
    exact ⟨_, h1, h2, hwp.trans e⟩

/-- **Exercise 16.2(c) for a Feller transition on a compact shock space** (given `q`, with the
domain condition): there is exactly one bounded continuous `w` satisfying (1) on `D`. -/
theorem ex_16_2c_feller (D : MsFellerData U c q R Q nxt B β) :
    ∃ w : ℝ × Sx →ᵇ ℝ, MsFellerBellman U c q R Q nxt B β w ∧
      ∀ w' : ℝ × Sx →ᵇ ℝ, MsFellerBellman U c q R Q nxt B β w' →
        ∀ p ∈ msSecDom c q B, w' p = w p := by
  set w := ContractingWith.fixedPoint (α := ℝ × Sx →ᵇ ℝ) (msFellerTB D)
    (ms_fellerTB_contracting D)
  have hfix : msFellerTB D w = w := (ms_fellerTB_contracting D).fixedPoint_isFixedPt
  exact ⟨w, ms_fellerBellman_of_fixed D hfix, fun w' hw' =>
    ms_fellerBellman_unique D hw' (ms_fellerBellman_of_fixed D hfix)⟩

end StokeyLucasPrescott.EquilibriumApplications

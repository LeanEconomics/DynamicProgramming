/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.WeightedRDP
import RecursiveDecisionProcesses.SavingsFeller
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Examples of recursive decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.1.1.2–§7.1.1.8 (pp. 209–212) and
§7.1.2.1 (p. 213).

* **Exercise 7.1.1**: a finite MDP is an RDP with `V = ℝ^X`; its Bellman operator is (1.19).
* §7.1.1.3: the firm valuation problem (7.4) with `A = Γ(x) = {0, 1}` and `V = bX`; its Bellman
  operator is `max{s, π(x) + β ∫ v(x')P(x, dx')}` (Theorem 1.1.1).
* **Exercise 7.1.2**: with unbounded profits, `|π| ≤ ηℓ + δ` and `∫ ℓ dP(x) ≤ αℓ(x)`, (7.4) is an
  RDP on `bℓX`. The book's (7.5) bounds `π` above only; the solution uses `|π| ≤ ηℓ + δ`.
* §7.1.1.5: optimal savings, as the LDP of Example 6.1.5 (via (7.9)).
* **Exercise 7.1.3**: savings with Kreps–Porteus expectations (7.6) is an RDP on the measurable
  `v : X → [u̲, ū]`.
* §7.1.1.7: MDPs with rewards depending on the next state (7.7).
* **Exercise 7.1.4**: the risk-sensitive aggregator (7.8) gives an RDP for every `θ ≠ 0`.
* §7.1.2.1: every LDP is an RDP (7.9), with the same policy operators.

The state space of the savings problems is `ℝ` with `Γ(w) = [0, max(w, 0)]`, as in Chapter 6.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-! ### Finite MDPs -/

/-- The finite MDP aggregator `B(x, a, v) = r(x, a) + β ∑_{x'} v(x')P(x, a, x')` (§7.1.1.2). -/
def mdpAgg [Fintype X] (r : X → A → ℝ) (β : ℝ) (Pm : X → A → X → ℝ) : X → A → (X → ℝ) → ℝ :=
  fun x a v => r x a + β * ∑ y, v y * Pm x a y

omit [MeasurableSpace X] [MeasurableSpace A] in
/-- **Exercise 7.1.1** (p. 209): the finite MDP aggregator satisfies the monotonicity condition
(7.2); consistency (7.3) is automatic with `V = ℝ^X`. -/
theorem exercise_7_1_1 [Fintype X] (r : X → A → ℝ) {β : ℝ} (hβ : 0 ≤ β) {Pm : X → A → X → ℝ}
    (hP : ∀ x a y, 0 ≤ Pm x a y) (x : X) (a : A) {v w : X → ℝ} (h : v ≤ w) :
    mdpAgg r β Pm x a v ≤ mdpAgg r β Pm x a w :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_right (h y) (hP x a y)) hβ)

/-- The finite MDP as an RDP with `V = ℝ^X` (§7.1.1.2). -/
def finiteMDP [Fintype X] (Γ : X → Set A) (r : X → A → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {Pm : X → A → X → ℝ} (hP : ∀ x a y, 0 ≤ Pm x a y)
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) : RDP X A (X → ℝ) where
  ev := id
  ev_le_iff _ _ := Iff.rfl
  Γ := Γ
  B := mdpAgg r β Pm
  mono x a _ _ _ h := exercise_7_1_1 r hβ hP x a h
  consistent _ _ _ _ := ⟨_, rfl⟩
  exists_policy := hΓ

/-- For finite `X` and `A`, the Bellman operator of the finite MDP is (1.19),
`(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑_{x'} v(x')P(x, a, x')}` (Lemma 7.1.1). -/
theorem finiteMDP_bellman [Fintype X] [MeasurableSingletonClass X] [Finite A]
    (Γ : X → Set A) (r : X → A → ℝ) {β : ℝ} (hβ : 0 ≤ β) {Pm : X → A → X → ℝ}
    (hP : ∀ x a y, 0 ≤ Pm x a y) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x)
    (v : X → ℝ) (x : X) :
    IsGreatest ((fun a => mdpAgg r β Pm x a v) '' Γ x)
      ((finiteMDP Γ r hβ hP hΓ).adp.bellman v x) :=
  ((finiteMDP Γ r hβ hP hΓ).lemma_7_1_1 (fun _ => (Set.toFinite _).measurableSet) v
    fun _ => measurable_of_finite _).2.2 x

/-- MDPs with modified rewards (7.7): `B(x, a, v) = ∑_{x'} {r(x, a, x') + βv(x')}P(x, a, x')`. -/
def modifiedMDP [Fintype X] (Γ : X → Set A) (r : X → A → X → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {Pm : X → A → X → ℝ} (hP : ∀ x a y, 0 ≤ Pm x a y)
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) : RDP X A (X → ℝ) where
  ev := id
  ev_le_iff _ _ := Iff.rfl
  Γ := Γ
  B x a v := ∑ y, (r x a y + β * v y) * Pm x a y
  mono x a _ _ _ h := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (h y) hβ)) (hP x a y)
  consistent _ _ _ _ := ⟨_, rfl⟩
  exists_policy := hΓ

/-- The risk-sensitive aggregator (7.8):
`B(x, a, v) = r(x, a) + (β/θ) ln ∑_{x'} exp(θv(x'))P(x, a, x')`. -/
noncomputable def rsAgg [Fintype X] (r : X → A → ℝ) (β θ : ℝ) (Pm : X → A → X → ℝ) :
    X → A → (X → ℝ) → ℝ :=
  fun x a v => r x a + β / θ * Real.log (∑ y, Real.exp (θ * v y) * Pm x a y)

omit [MeasurableSpace X] [MeasurableSpace A] in
/-- **Exercise 7.1.4** (p. 212): for every `θ ≠ 0`, the risk-sensitive aggregator (7.8) satisfies
the monotonicity condition (7.2); consistency (7.3) is automatic with `V = ℝ^X`. -/
theorem exercise_7_1_4 [Fintype X] (r : X → A → ℝ) {β θ : ℝ} (hβ : 0 ≤ β) (hθ : θ ≠ 0)
    {Pm : X → A → X → ℝ} (hP : ∀ x a y, 0 ≤ Pm x a y) (hP1 : ∀ x a, ∑ y, Pm x a y = 1)
    (x : X) (a : A) {v w : X → ℝ} (h : v ≤ w) :
    rsAgg r β θ Pm x a v ≤ rsAgg r β θ Pm x a w := by
  have hpos : ∀ u : X → ℝ, 0 < ∑ y, Real.exp (θ * u y) * Pm x a y := fun u => by
    obtain ⟨y, hy⟩ : ∃ y, 0 < Pm x a y := by
      by_contra hcon
      have : ∑ y, Pm x a y = 0 := Finset.sum_eq_zero fun y _ =>
        le_antisymm (not_lt.1 fun hy => hcon ⟨y, hy⟩) (hP x a y)
      rw [hP1] at this
      exact one_ne_zero this
    exact Finset.sum_pos' (fun y _ => mul_nonneg (Real.exp_pos _).le (hP x a y))
      ⟨y, Finset.mem_univ _, mul_pos (Real.exp_pos _) hy⟩
  refine add_le_add le_rfl ?_
  rcases lt_or_gt_of_ne hθ with hneg | hθpos
  · have hle : ∑ y, Real.exp (θ * w y) * Pm x a y ≤ ∑ y, Real.exp (θ * v y) * Pm x a y :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (h y) hneg.le)) (hP x a y)
    exact mul_le_mul_of_nonpos_left (Real.log_le_log (hpos w) hle)
      (div_nonpos_of_nonneg_of_nonpos hβ hneg.le)
  · have hle : ∑ y, Real.exp (θ * v y) * Pm x a y ≤ ∑ y, Real.exp (θ * w y) * Pm x a y :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (h y) hθpos.le)) (hP x a y)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (hpos v) hle) (div_nonneg hβ hθpos.le)

/-- The risk-sensitive MDP of §7.1.1.8 as an RDP with `V = ℝ^X`. -/
noncomputable def riskSensitiveMDP [Fintype X] (Γ : X → Set A) (r : X → A → ℝ) {β θ : ℝ}
    (hβ : 0 ≤ β) (hθ : θ ≠ 0) {Pm : X → A → X → ℝ} (hP : ∀ x a y, 0 ≤ Pm x a y)
    (hP1 : ∀ x a, ∑ y, Pm x a y = 1) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) :
    RDP X A (X → ℝ) where
  ev := id
  ev_le_iff _ _ := Iff.rfl
  Γ := Γ
  B := rsAgg r β θ Pm
  mono x a _ _ _ h := exercise_7_1_4 r hβ hθ hP hP1 x a h
  consistent _ _ _ _ := ⟨_, rfl⟩
  exists_policy := hΓ

/-! ### LDPs are RDPs -/

/-- (7.9), §7.1.2.1 (p. 213): an LDP `(Γ, r, K)` is the RDP `(Γ, bX, B)` with
`B(x, a, v) = r(x, a) + ∫ v(x')K(x, a, dx')`. -/
noncomputable def LDP.toRDP (M : LDP X A) : RDP X A (BM X) where
  ev := BM.toFun
  ev_le_iff _ _ := Iff.rfl
  Γ := M.Γ
  B x a v := M.r.toFun (x, a) + M.β.toFun (x, a) * ∫ x', v x' ∂(M.P (x, a))
  mono x a _ v w h := by
    have := M.P_markov
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ fun y =>
      BM.le_def.1 h y) (M.β_nonneg (x, a)))
    · exact Integrable.of_bound v.measurable'.aestronglyMeasurable ‖v‖
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v y)
    · exact Integrable.of_bound w.measurable'.aestronglyMeasurable ‖w‖
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm w y)
  consistent σ hσ hσΓ v := ⟨M.adp.T ⟨σ, hσ, hσΓ⟩ v, rfl⟩
  exists_policy := M.exists_policy

/-- The RDP of an LDP has the LDP's policy operators (7.9). -/
theorem LDP.toRDP_T (M : LDP X A) (σ : M.Policy) (v : BM X) :
    M.toRDP.adp.T σ v = M.adp.T σ v :=
  BM.ext fun x => M.toRDP.ev_adp_T σ v x

/-- §7.1.1.5 (p. 210): the optimal savings problem is an RDP (through the LDP of Example 6.1.5)
with `B(w, c, v) = u(c) + β ∫ v(R(w − c) + y)φ(dy)`. -/
theorem savings_B (u : ℝ → ℝ) (hu : Continuous u) (hub : ∃ C, ∀ c, |u c| ≤ C) {β : ℝ}
    (hβ0 : 0 ≤ β) (R : ℝ) (φ : Measure ℝ) [IsProbabilityMeasure φ] (w c : ℝ) (v : BM ℝ) :
    (Savings.ldp u hu hub hβ0 R φ).toRDP.B w c v.toFun =
      u c + β * ∫ y, v.toFun (R * (w - c) + y) ∂φ := by
  change u c + β * ∫ x', v.toFun x' ∂(Savings.P R φ (w, c)) = _
  rw [Savings.P, integral_shockKernel _ _ _ v.measurable']

/-! ### The firm valuation problem -/

/-- The firm valuation aggregator (7.4): `B(x, a, v) = as + (1 − a)[π(x) + β ∫ v(x')P(x, dx')]`. -/
noncomputable def firmAgg (P : Kernel X X) (s : ℝ) (π : X → ℝ) (β : ℝ) :
    X → ℝ → (X → ℝ) → ℝ :=
  fun x a v => a * s + (1 - a) * (π x + β * ∫ x', v x' ∂(P x))

/-- §7.1.1.3 (p. 209): the firm valuation problem as an RDP with `A = ℝ`, `Γ(x) = {0, 1}` and
`V = bX`. -/
noncomputable def firmRDP (P : Kernel X X) [IsMarkovKernel P] (s : ℝ) (π : BM X) {β : ℝ}
    (hβ : 0 ≤ β) : RDP X ℝ (BM X) where
  ev := BM.toFun
  ev_le_iff _ _ := Iff.rfl
  Γ _ := {0, 1}
  B := firmAgg P s π.toFun β
  mono x a ha v w h := by
    have h1 : 0 ≤ 1 - a := by rcases ha with rfl | rfl <;> norm_num
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (markovOp_mono P (BM.mem_bX v) (BM.mem_bX w) h x) hβ)) h1)
  consistent σ hσ hσΓ v := by
    refine ⟨⟨fun x => firmAgg P s π.toFun β x (σ x) v.toFun, ?_, |s| + ‖π‖ + β * ‖v‖,
      fun x => ?_⟩, rfl⟩
    · exact (hσ.mul measurable_const).add ((measurable_const.sub hσ).mul
        (π.measurable'.add ((measurable_markovOp P v.measurable').const_mul β)))
    · have hint := abs_markovOp_le P (BM.abs_le_norm v) x
      have hπ := BM.abs_le_norm π x
      change |σ x * s + (1 - σ x) * (π.toFun x + β * markovOp P v.toFun x)| ≤ _
      rcases hσΓ x with h | h <;> rw [h]
      · simp only [zero_mul, sub_zero, one_mul, zero_add]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hβ]
        nlinarith [abs_nonneg s, mul_le_mul_of_nonneg_left hint hβ]
      · simp only [one_mul, sub_self, zero_mul, add_zero]
        nlinarith [norm_nonneg π, norm_nonneg v, mul_nonneg hβ (norm_nonneg v)]
  exists_policy := ⟨fun _ => 0, measurable_const, fun _ => Or.inl rfl⟩

/-- §7.1.1.3 (p. 210): the RDP Bellman operator of the firm valuation problem is
`(Tv)(x) = max{s, π(x) + β ∫ v(x')P(x, dx')}`, as in Theorem 1.1.1. -/
theorem firmRDP_bellman (P : Kernel X X) [IsMarkovKernel P] (s : ℝ) (π : BM X) {β : ℝ}
    (hβ : 0 ≤ β) (v : BM X) (x : X) :
    ((firmRDP P s π hβ).adp.bellman v).toFun x =
      max s (π.toFun x + β * ∫ x', v.toFun x' ∂(P x)) := by
  let c : X → ℝ := fun x => π.toFun x + β * ∫ x', v.toFun x' ∂(P x)
  have hc : Measurable c := π.measurable'.add ((measurable_markovOp P v.measurable').const_mul β)
  let σ : X → ℝ := fun x => if c x ≤ s then 1 else 0
  have hσm : Measurable σ := Measurable.ite (measurableSet_le hc measurable_const)
    measurable_const measurable_const
  have hσΓ : ∀ x, σ x ∈ (firmRDP P s π hβ).Γ x := fun x => by
    change σ x ∈ ({0, 1} : Set ℝ)
    by_cases h : c x ≤ s
    · simp [σ, h]
    · simp [σ, h]
  have hval : ∀ x, firmAgg P s π.toFun β x (σ x) v.toFun = max s (c x) := fun x => by
    by_cases h : c x ≤ s
    · simp only [σ, firmAgg, h, ↓reduceIte]
      rw [max_eq_left h]
      ring
    · simp only [σ, firmAgg, h, ↓reduceIte]
      rw [max_eq_right (not_le.1 h).le]
      ring
  have hσ : (firmRDP P s π hβ).IsArgmax v ⟨σ, hσm, hσΓ⟩ := fun x a ha => by
    change firmAgg P s π.toFun β x a v.toFun ≤ firmAgg P s π.toFun β x (σ x) v.toFun
    rw [hval]
    rcases ha with rfl | rfl
    · simp only [firmAgg, zero_mul, sub_zero, one_mul, zero_add]
      exact le_max_right _ _
    · simp only [firmAgg, one_mul, sub_self, zero_mul, add_zero]
      exact le_max_left _ _
  rw [show ((firmRDP P s π hβ).adp.bellman v).toFun x =
    (firmRDP P s π hβ).ev ((firmRDP P s π hβ).adp.bellman v) x from rfl,
    ((firmRDP P s π hβ).bellman_of_isArgmax hσ).2.1 x]
  exact hval x

/-- `v ∈ bℓX` is `ℓh` for `h = v / ℓ ∈ bX`. -/
theorem exists_wevB_eq {ℓ : X → ℝ} (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x) {v : X → ℝ}
    (hv : v ∈ bl ℓ) : ∃ h : BM X, wevB ℓ h = v := by
  obtain ⟨hm, C, hC⟩ := hv
  refine ⟨⟨fun x => v x / ℓ x, hm.div hℓm, C, fun x => ?_⟩, funext fun x => ?_⟩
  · have hpos : 0 < ℓ x := zero_lt_one.trans_le (hℓ1 x)
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact hC x
  · exact mul_div_cancel₀ _ (zero_lt_one.trans_le (hℓ1 x)).ne'

/-- **Exercise 7.1.2** (p. 210): firm valuation with unbounded profits. If `ℓ ≥ 1` is a weight
function, `|π| ≤ ηℓ + δ` and `∫ ℓ dP(x) ≤ αℓ(x)` (with `ℓ` integrable under each `P(x)`), then the
aggregator (7.4) is monotone on `bℓX` (7.2) and maps `bℓX` into `bℓX` along every policy (7.3). -/
theorem exercise_7_1_2 (P : Kernel X X) [IsMarkovKernel P] (s : ℝ) {π ℓ : X → ℝ}
    (hπm : Measurable π) (hℓ1 : ∀ x, 1 ≤ ℓ x)
    (hℓi : ∀ x, Integrable ℓ (P x)) {η δ α β : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hπ : ∀ x, |π x| ≤ η * ℓ x + δ) (hP : ∀ x, ∫ x', ℓ x' ∂(P x) ≤ α * ℓ x) :
    (∀ x, ∀ a ∈ ({0, 1} : Set ℝ), ∀ v ∈ bl ℓ, ∀ w ∈ bl ℓ, v ≤ w →
      firmAgg P s π β x a v ≤ firmAgg P s π β x a w) ∧
    ∀ σ : X → ℝ, Measurable σ → (∀ x, σ x ∈ ({0, 1} : Set ℝ)) → ∀ v ∈ bl ℓ,
      (fun x => firmAgg P s π β x (σ x) v) ∈ bl ℓ := by
  have hint : ∀ v ∈ bl ℓ, ∀ x, Integrable v (P x) := fun v hv x => by
    obtain ⟨hm, C, hC⟩ := hv
    refine ((hℓi x).const_mul |C|).mono' hm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact (hC y).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
      (zero_le_one.trans (hℓ1 y)))
  refine ⟨fun x a ha v hv w hw h => ?_, fun σ hσ hσΓ v hv => ⟨?_, ?_⟩⟩
  · have h1 : 0 ≤ 1 - a := by rcases ha with rfl | rfl <;> norm_num
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (integral_mono (hint v hv x) (hint w hw x) h) hβ)) h1)
  · exact (hσ.mul measurable_const).add ((measurable_const.sub hσ).mul (hπm.add
      ((hv.1.stronglyMeasurable.integral_kernel (κ := P)).measurable.const_mul β)))
  · obtain ⟨hvm, C, hC⟩ := hv
    refine ⟨|s| + δ + η + β * (|C| * α), fun x => ?_⟩
    have hl : 1 ≤ ℓ x := hℓ1 x
    have hI : |∫ x', v x' ∂(P x)| ≤ |C| * (α * ℓ x) := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ x', |v x'| ∂(P x) ≤ ∫ x', |C| * ℓ x' ∂(P x) :=
            integral_mono (hint v ⟨hvm, C, hC⟩ x).abs ((hℓi x).const_mul _) fun y =>
              (hC y).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
                (zero_le_one.trans (hℓ1 y)))
        _ = |C| * ∫ x', ℓ x' ∂(P x) := integral_const_mul _ _
        _ ≤ |C| * (α * ℓ x) := mul_le_mul_of_nonneg_left (hP x) (abs_nonneg C)
    have hπx := hπ x
    change |σ x * s + (1 - σ x) * (π x + β * ∫ x', v x' ∂(P x))| ≤ _
    rcases hσΓ x with h | h <;> rw [h]
    · simp only [zero_mul, sub_zero, one_mul, zero_add]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hβ]
      have := mul_le_mul_of_nonneg_left hI hβ
      nlinarith [abs_nonneg s, abs_nonneg C, mul_nonneg hβ (mul_nonneg (abs_nonneg C) hα)]
    · simp only [one_mul, sub_self, zero_mul, add_zero]
      nlinarith [abs_nonneg s, abs_nonneg C, mul_nonneg hβ (mul_nonneg (abs_nonneg C) hα)]

/-- The firm valuation problem with unbounded profits as an RDP on `bℓX` (Exercise 7.1.2), with
`bℓX` represented as `bX` through `v = ℓh`. -/
noncomputable def firmWeighted (P : Kernel X X) [IsMarkovKernel P] (s : ℝ) {π ℓ : X → ℝ}
    (hπm : Measurable π) (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x)
    (hℓi : ∀ x, Integrable ℓ (P x)) {η δ α β : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hπ : ∀ x, |π x| ≤ η * ℓ x + δ) (hP : ∀ x, ∫ x', ℓ x' ∂(P x) ≤ α * ℓ x) :
    RDP X ℝ (BM X) where
  ev := wevB ℓ
  ev_le_iff h h' := by
    change (∀ x, h.toFun x ≤ h'.toFun x) ↔ ∀ x, ℓ x * h.toFun x ≤ ℓ x * h'.toFun x
    exact forall_congr' fun x =>
      (mul_le_mul_iff_of_pos_left (zero_lt_one.trans_le (hℓ1 x))).symm
  Γ _ := {0, 1}
  B := firmAgg P s π β
  mono x a ha v w h := (exercise_7_1_2 P s hπm hℓ1 hℓi hη hδ hα hβ hπ hP).1 x a ha _
    (wevB_mem hℓm hℓ1 v) _ (wevB_mem hℓm hℓ1 w) fun y =>
      mul_le_mul_of_nonneg_left (BM.le_def.1 h y) (zero_le_one.trans (hℓ1 y))
  consistent σ hσ hσΓ v := exists_wevB_eq hℓm hℓ1
    ((exercise_7_1_2 P s hπm hℓ1 hℓi hη hδ hα hβ hπ hP).2 σ hσ hσΓ _ (wevB_mem hℓm hℓ1 v))
  exists_policy := ⟨fun _ => 0, measurable_const, fun _ => Or.inl rfl⟩

/-! ### Savings with Kreps–Porteus expectations -/

/-- The value space of §7.1.1.6: measurable `v : ℝ → [u̲, ū]`. -/
abbrev KPValues (lo hi : ℝ) : Type := {v : ℝ → ℝ // Measurable v ∧ ∀ x, v x ∈ Icc lo hi}

/-- The Kreps–Porteus expectation `(∫ v(s + y)^{1−γ} φ(dy))^{1/(1−γ)}` of continuation values. -/
noncomputable def kpCont (γ : ℝ) (φ : Measure ℝ) (v : ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫ y, v (s + y) ^ (1 - γ) ∂φ) ^ (1 - γ)⁻¹

/-- The aggregator of (7.6):
`B(w, c, v) = (1 − β)u(c) + β (∫ v(R(w − c) + y)^{1−γ} φ(dy))^{1/(1−γ)}`. -/
noncomputable def kpAgg (u : ℝ → ℝ) (β R γ : ℝ) (φ : Measure ℝ) : ℝ → ℝ → (ℝ → ℝ) → ℝ :=
  fun w c v => (1 - β) * u c + β * kpCont γ φ v (R * (w - c))

/-- The Kreps–Porteus expectation is monotone on functions with values in `[u̲, ū] ⊆ (0, ∞)`. -/
theorem kpCont_mono {γ : ℝ} (hγ : γ ≠ 1) (φ : Measure ℝ) [IsProbabilityMeasure φ] {lo hi : ℝ}
    (hlo : 0 < lo) {v w : ℝ → ℝ} (hvm : Measurable v) (hwm : Measurable w)
    (hv : ∀ x, v x ∈ Icc lo hi) (hw : ∀ x, w x ∈ Icc lo hi) (h : v ≤ w) (s : ℝ) :
    kpCont γ φ v s ≤ kpCont γ φ w s := by
  have hpos : ∀ {g : ℝ → ℝ}, (∀ x, g x ∈ Icc lo hi) → ∀ x, 0 < g x := fun hg x =>
    hlo.trans_le (hg x).1
  -- `g^{1−γ}` is bounded and measurable, hence integrable
  have hint : ∀ {g : ℝ → ℝ}, Measurable g → (∀ x, g x ∈ Icc lo hi) →
      Integrable (fun y => g (s + y) ^ (1 - γ)) φ := fun hgm hg => by
    refine Integrable.of_bound
      ((hgm.comp (measurable_const_add s)).pow_const _).aestronglyMeasurable
      (lo ^ (1 - γ) + hi ^ (1 - γ)) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hpos hg _) _)]
    rcases le_total 0 (1 - γ) with hp | hp
    · exact (Real.rpow_le_rpow (hpos hg _).le (hg _).2 hp).trans
        (le_add_of_nonneg_left (Real.rpow_pos_of_pos hlo _).le)
    · exact (Real.rpow_le_rpow_of_nonpos hlo (hg _).1 hp).trans
        (le_add_of_nonneg_right
          (Real.rpow_pos_of_pos (hlo.trans_le ((hg 0).1.trans (hg 0).2)) _).le)
  have hIpos : ∀ {g : ℝ → ℝ}, Measurable g → (∀ x, g x ∈ Icc lo hi) →
      0 < ∫ y, g (s + y) ^ (1 - γ) ∂φ := fun {g} hgm hg =>
    integral_pos_iff_support_of_nonneg (fun y => (Real.rpow_pos_of_pos (hpos hg _) _).le)
      (hint hgm hg) |>.2 (by
        have : Function.support (fun y => g (s + y) ^ (1 - γ)) = univ :=
          eq_univ_of_forall fun y => (Real.rpow_pos_of_pos (hpos hg _) _).ne'
        rw [this, measure_univ]
        exact one_pos)
  rcases lt_or_gt_of_ne (sub_ne_zero.2 hγ.symm) with hp | hp
  · -- `1 − γ < 0`: both powers reverse the order
    have hle : ∫ y, w (s + y) ^ (1 - γ) ∂φ ≤ ∫ y, v (s + y) ^ (1 - γ) ∂φ :=
      integral_mono (hint hwm hw) (hint hvm hv) fun y =>
        Real.rpow_le_rpow_of_nonpos (hpos hv _) (h _) hp.le
    exact Real.rpow_le_rpow_of_nonpos (hIpos hwm hw) hle (inv_nonpos.2 hp.le)
  · have hle : ∫ y, v (s + y) ^ (1 - γ) ∂φ ≤ ∫ y, w (s + y) ^ (1 - γ) ∂φ :=
      integral_mono (hint hvm hv) (hint hwm hw) fun y =>
        Real.rpow_le_rpow (hpos hv _).le (h _) hp.le
    exact Real.rpow_le_rpow (hIpos hvm hv).le hle (inv_nonneg.2 hp.le)

theorem kpCont_const {γ : ℝ} (hγ : γ ≠ 1) (φ : Measure ℝ) [IsProbabilityMeasure φ] {c : ℝ}
    (hc : 0 < c) (s : ℝ) : kpCont γ φ (fun _ => c) s = c := by
  rw [kpCont, integral_const, probReal_univ, one_smul,
    Real.rpow_rpow_inv hc.le (sub_ne_zero.2 hγ.symm)]

/-- **Exercise 7.1.3** (p. 211): for `γ ≠ 1`, `0 ≤ β ≤ 1`, `u` measurable with values in
`[u̲, ū] ⊆ (0, ∞)`, the Kreps–Porteus savings aggregator is monotone (7.2) and maps the measurable
`v : ℝ → [u̲, ū]` into themselves along every policy (7.3). -/
theorem exercise_7_1_3 {u : ℝ → ℝ} (hum : Measurable u) {lo hi : ℝ} (hlo : 0 < lo)
    (hu : ∀ c, u c ∈ Icc lo hi) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (R : ℝ) {γ : ℝ}
    (hγ : γ ≠ 1) (φ : Measure ℝ) [IsProbabilityMeasure φ] :
    (∀ w c, ∀ v w' : ℝ → ℝ, Measurable v → Measurable w' → (∀ x, v x ∈ Icc lo hi) →
      (∀ x, w' x ∈ Icc lo hi) → v ≤ w' → kpAgg u β R γ φ w c v ≤ kpAgg u β R γ φ w c w') ∧
    ∀ σ : ℝ → ℝ, Measurable σ → ∀ v : ℝ → ℝ, Measurable v → (∀ x, v x ∈ Icc lo hi) →
      Measurable (fun w => kpAgg u β R γ φ w (σ w) v) ∧
        ∀ w, kpAgg u β R γ φ w (σ w) v ∈ Icc lo hi := by
  refine ⟨fun w c v w' hv hw' hvI hwI h => add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (kpCont_mono hγ φ hlo hv hw' hvI hwI h _) hβ0), fun σ hσ v hvm hvI => ⟨?_, fun w => ?_⟩⟩
  · have hm : Measurable fun p : ℝ × ℝ => v (R * (p.1 - σ p.1) + p.2) ^ (1 - γ) :=
      (hvm.comp ((measurable_const.mul (measurable_fst.sub (hσ.comp measurable_fst))).add
        measurable_snd)).pow_const _
    exact ((measurable_const.mul (hum.comp hσ))).add (measurable_const.mul
      ((hm.stronglyMeasurable.integral_prod_right' (ν := φ)).measurable.pow_const _))
  · have hconst : ∀ c, 0 < c → c ∈ Icc lo hi → ∀ x, (fun _ : ℝ => c) x ∈ Icc lo hi :=
      fun c _ hc _ => hc
    have hlohi : lo ≤ hi := (hvI 0).1.trans (hvI 0).2
    have h1 := kpCont_mono hγ φ hlo measurable_const hvm (hconst lo hlo ⟨le_rfl, hlohi⟩) hvI
      (fun x => (hvI x).1) (R * (w - σ w))
    have h2 := kpCont_mono hγ φ hlo hvm measurable_const hvI
      (hconst hi (hlo.trans_le hlohi) ⟨hlohi, le_rfl⟩) (fun x => (hvI x).2) (R * (w - σ w))
    rw [kpCont_const hγ φ hlo] at h1
    rw [kpCont_const hγ φ (hlo.trans_le hlohi)] at h2
    have hu1 := hu (σ w)
    change (1 - β) * u (σ w) + β * kpCont γ φ v (R * (w - σ w)) ∈ Icc lo hi
    constructor <;> nlinarith [hu1.1, hu1.2]

/-- Savings with Kreps–Porteus expectations (7.6) as an RDP (Exercise 7.1.3), `Γ(w) = [0, w⁺]`. -/
noncomputable def kpSavings {u : ℝ → ℝ} (hum : Measurable u) {lo hi : ℝ} (hlo : 0 < lo)
    (hu : ∀ c, u c ∈ Icc lo hi) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (R : ℝ) {γ : ℝ}
    (hγ : γ ≠ 1) (φ : Measure ℝ) [IsProbabilityMeasure φ] : RDP ℝ ℝ (KPValues lo hi) where
  ev v := v.1
  ev_le_iff _ _ := Iff.rfl
  Γ w := Icc 0 (max w 0)
  B := kpAgg u β R γ φ
  mono w c _ v v' h := (exercise_7_1_3 hum hlo hu hβ0 hβ1 R hγ φ).1 w c v.1 v'.1 v.2.1 v'.2.1
    v.2.2 v'.2.2 h
  consistent σ hσ _ v := by
    obtain ⟨hm, hI⟩ := (exercise_7_1_3 hum hlo hu hβ0 hβ1 R hγ φ).2 σ hσ v.1 v.2.1 v.2.2
    exact ⟨⟨_, hm, hI⟩, rfl⟩
  exists_policy := ⟨fun _ => 0, measurable_const, fun w => ⟨le_rfl, le_max_right _ _⟩⟩

end SargentStachurski.RecursiveDecisionProcesses

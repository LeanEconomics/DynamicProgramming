/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.LSFiniteHorizon
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Filtration

/-!
# The controlled linear state-space system (Miao §9.1)

Miao, §9.1, pp. 291–294.

* **Assumption 9.1.1** (`LSAssumption911`): `E[ε_{t+1} | F_t] = 0`, `E[ε_{t+1}ε'_{t+1} | F_t] = I`;
  and the computation of p. 296 in this setting (`ls_condExp_quad`):
  `E_t(y + Cε_{t+1})'P(y + Cε_{t+1}) = y'Py + tr(PCC')` for `F_t`-measurable `y`.
* The state transition equation (9.1) (`ls_state`; deterministic `ls_traj`) and the measurement
  equation (9.2) (`ls_output`).
* **Definition 9.1.1** (`ls_Stabilizable`) with its motivation: under `u_t = Hx_t`,
  `x_{t+1} = (A + BH)x_t + Cε_{t+1}` and the deterministic steady state `0` is stable iff `A + BH`
  is stable (`definition_9_1_1_closed_loop`, `definition_9_1_1_steady_state`).
* **Definition 9.1.2** (`ls_Controllable`: `∑_{j<nₓ} AʲBB'A'ʲ > 0`) and its equivalence with
  reachability (`definition_9_1_2_iff`): every state can be steered to every target in `r` steps
  for every `r ≥ nₓ` — but not "for any `r > 0`" as printed (`ls_controllable_not_reach_one`).
* Stabilizable does not imply controllable (`ls_stabilizable_not_controllable`, the book's
  example: `A` stable, `B = 0`); controllable implies stabilizable is
  `controllable_stabilizable` in `LSInfiniteHorizon`.
* **Definition 9.1.3** (`ls_Observable`: `∑_{j<nₓ} A'ʲG'GAʲ > 0`) and its equivalence with the
  determination of `x₀` from `y₀, …, y_r` (knowing the inputs and shocks) for every
  `r ≥ nₓ − 1` (`definition_9_1_3_iff`), not for every `r > 0` (`ls_observable_not_two_outputs`).
* **Definition 9.1.4** (`ls_Detectable`) and its motivation (9.3): the estimation error obeys
  `Δ_{t+1} = (A − AKG)Δ_t + Cε_{t+1} − AKDε_t` (`eq_9_3_error`; the book prints `Δ_{t−1}` and
  `+AKDε_t`), and if `A − AKG` is stable the noise-free error vanishes (`eq_9_3_tendsto`); for
  invertible `A` a detecting `J` gives such a `K = A⁻¹J` (`definition_9_1_4_rule`).
-/

open Filter Topology Matrix MeasureTheory

namespace Miao.LinearQuadratic

variable {X U : Type*} [Fintype X] [DecidableEq X] [Fintype U]

/-! ### Assumption 9.1.1 -/

variable {Ω E : Type*} {m0 : MeasurableSpace Ω} [DecidableEq E] (μ : Measure Ω)
  (ℱ : Filtration ℕ m0) (ε : ℕ → Ω → E → ℝ) in
/-- **Assumption 9.1.1** (Miao, p. 291): (i) `E[ε_{t+1} | F_t] = 0`;
(ii) `E[ε_{t+1}ε'_{t+1} | F_t] = I`. -/
structure LSAssumption911 : Prop where
  /-- (i) -/
  mean : ∀ t k, μ[fun ω => ε (t + 1) ω k | ℱ t] =ᵐ[μ] 0
  /-- (ii) -/
  cov : ∀ t k l, μ[fun ω => ε (t + 1) ω k * ε (t + 1) ω l | ℱ t] =ᵐ[μ]
    fun _ => if k = l then 1 else 0

omit [DecidableEq X] [Fintype U] in
/-- Miao, p. 296, in the setting of Assumption 9.1.1: for `F_t`-measurable square-integrable `y`
and square-integrable `ε_{t+1}`, `E_t[(y + Cε_{t+1})'P(y + Cε_{t+1})] = y'Py + tr(PCC')`. -/
theorem ls_condExp_quad {Ω E : Type*} {m0 : MeasurableSpace Ω} [Fintype E] [DecidableEq E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {ε : ℕ → Ω → E → ℝ}
    (hA : LSAssumption911 μ ℱ ε) {t : ℕ} (hε : ∀ k, MemLp (fun ω => ε (t + 1) ω k) 2 μ)
    {y : Ω → X → ℝ} (hym : ∀ i, Measurable[ℱ t] fun ω => y ω i)
    (hy : ∀ i, MemLp (fun ω => y ω i) 2 μ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    μ[fun ω => (y ω + C *ᵥ ε (t + 1) ω) ⬝ᵥ (P *ᵥ (y ω + C *ᵥ ε (t + 1) ω)) | ℱ t] =ᵐ[μ]
      fun ω => y ω ⬝ᵥ (P *ᵥ y ω) + trace (P * C * Cᵀ) := by
  set W : Matrix X E ℝ := P * C + Pᵀ * C
  set M : Matrix E E ℝ := Cᵀ * P * C
  have hm := ℱ.le t
  -- the linear coefficients
  have ha : ∀ (z : X → ℝ) k, (z ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ z)) k = ∑ i, W i k * z i := by
    intro z k
    simp only [W, Pi.add_apply, vecMul, mulVec, dotProduct, Matrix.add_apply, add_mul,
      Finset.sum_add_distrib, transpose_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun j i => C j k * (P j i * z i))]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hexp : (fun ω => (y ω + C *ᵥ ε (t + 1) ω) ⬝ᵥ (P *ᵥ (y ω + C *ᵥ ε (t + 1) ω))) =
      (fun ω => ∑ i, ∑ j, P i j * (y ω i * y ω j)) +
      (fun ω => ∑ k, ∑ i, W i k * (y ω i * ε (t + 1) ω k)) +
      (fun ω => ∑ k, ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) := by
    funext ω
    rw [ls_quad_shock_expand]
    simp only [Pi.add_apply, ha, Finset.sum_mul]
    congr 2
    · simp only [dotProduct, mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  -- integrability
  have hyy : ∀ i j, Integrable (fun ω => y ω i * y ω j) μ := fun i j =>
    (hy i).integrable_mul (hy j)
  have hye : ∀ i k, Integrable (fun ω => y ω i * ε (t + 1) ω k) μ := fun i k =>
    (hy i).integrable_mul (hε k)
  have hee : ∀ k l, Integrable (fun ω => ε (t + 1) ω k * ε (t + 1) ω l) μ := fun k l =>
    (hε k).integrable_mul (hε l)
  have hi1 : Integrable (fun ω => ∑ i, ∑ j, P i j * (y ω i * y ω j)) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hyy i j).const_mul _
  have hi2 : ∀ k, Integrable (fun ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k)) μ := fun k =>
    integrable_finsetSum _ fun i _ => (hye i k).const_mul _
  have hi2' : Integrable (fun ω => ∑ k, ∑ i, W i k * (y ω i * ε (t + 1) ω k)) μ :=
    integrable_finsetSum _ fun k _ => hi2 k
  have hi3 : ∀ k, Integrable (fun ω => ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) μ :=
    fun k => integrable_finsetSum _ fun l _ => (hee k l).const_mul _
  have hi3' : Integrable (fun ω => ∑ k, ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) μ :=
    integrable_finsetSum _ fun k _ => hi3 k
  -- the constant term is `F_t`-measurable
  have hc : μ[fun ω => ∑ i, ∑ j, P i j * (y ω i * y ω j) | ℱ t] =
      fun ω => ∑ i, ∑ j, P i j * (y ω i * y ω j) := by
    refine condExp_of_stronglyMeasurable hm ?_ hi1
    refine Measurable.stronglyMeasurable ?_
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      ((hym i).mul (hym j)).const_mul _
  -- the linear terms vanish
  have hlin : ∀ k, μ[fun ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k) | ℱ t] =ᵐ[μ] 0 := by
    intro k
    have hfac : (fun ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k)) =
        (fun ω => ∑ i, W i k * y ω i) * fun ω => ε (t + 1) ω k := by
      funext ω
      simp only [Pi.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsm : StronglyMeasurable[ℱ t] fun ω => ∑ i, W i k * y ω i :=
      (Finset.measurable_sum _ fun i _ => (hym i).const_mul _).stronglyMeasurable
    rw [hfac]
    refine (condExp_mul_of_stronglyMeasurable_left hsm (hfac ▸ hi2 k)
      ((hε k).integrable one_le_two)).trans ?_
    filter_upwards [hA.mean t k] with ω hω
    simp [hω]
  have hlin' : μ[fun ω => ∑ k, ∑ i, W i k * (y ω i * ε (t + 1) ω k) | ℱ t] =ᵐ[μ] 0 := by
    have h1 := condExp_finsetSum (s := Finset.univ)
      (f := fun k ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k)) (fun k _ => hi2 k) (ℱ t)
    have h2 : ∀ᵐ ω ∂μ, ∀ k, (μ[fun ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k) | ℱ t]) ω = 0 :=
      ae_all_iff.2 fun k => hlin k
    have heq : (∑ k, fun ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k)) =
        fun ω => ∑ k, ∑ i, W i k * (y ω i * ε (t + 1) ω k) := by
      funext ω; simp
    rw [heq] at h1
    filter_upwards [h1, h2] with ω h1ω h2ω
    rw [h1ω, Finset.sum_apply]
    simp [h2ω]
  -- the quadratic terms give the trace
  have hq : ∀ k, μ[fun ω => ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l) | ℱ t] =ᵐ[μ]
      fun _ => M k k := by
    intro k
    have h1 := condExp_finsetSum (s := Finset.univ)
      (f := fun l ω => M k l * (ε (t + 1) ω k * ε (t + 1) ω l))
      (fun l _ => (hee k l).const_mul _) (ℱ t)
    have heq : (∑ l, fun ω => M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) =
        fun ω => ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l) := by
      funext ω; simp
    rw [heq] at h1
    have h2 : ∀ l, μ[fun ω => M k l * (ε (t + 1) ω k * ε (t + 1) ω l) | ℱ t] =ᵐ[μ]
        fun _ => M k l * (if k = l then 1 else 0) := by
      intro l
      have := condExp_smul (μ := μ) (M k l) (fun ω => ε (t + 1) ω k * ε (t + 1) ω l) (ℱ t)
      refine this.trans ?_
      filter_upwards [hA.cov t k l] with ω hω
      simp only [Pi.smul_apply, smul_eq_mul, hω]
    have h3 := ae_all_iff.2 h2
    filter_upwards [h1, h3] with ω h1ω h3ω
    rw [h1ω, Finset.sum_apply]
    simp only [h3ω, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
  have hq' : μ[fun ω => ∑ k, ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l) | ℱ t] =ᵐ[μ]
      fun _ => trace (P * C * Cᵀ) := by
    have h1 := condExp_finsetSum (s := Finset.univ)
      (f := fun k ω => ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) (fun k _ => hi3 k) (ℱ t)
    have heq : (∑ k, fun ω => ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) =
        fun ω => ∑ k, ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l) := by
      funext ω; simp
    rw [heq] at h1
    have h3 := ae_all_iff.2 hq
    have htr : trace (Cᵀ * P * C) = trace (P * C * Cᵀ) := by
      rw [Matrix.mul_assoc, trace_mul_comm]
    filter_upwards [h1, h3] with ω h1ω h3ω
    rw [h1ω, Finset.sum_apply]
    simp only [h3ω]
    rw [← htr]
    rfl
  rw [hexp]
  refine (condExp_add (hi1.add hi2') hi3' _).trans ?_
  have h12 := condExp_add hi1 hi2' (ℱ t)
  filter_upwards [h12, hlin', hq'] with ω h12ω hlω hqω
  rw [Pi.add_apply, h12ω, Pi.add_apply, hc, hlω, hqω]
  simp only [Pi.zero_apply, add_zero]
  congr 1
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### The state-space system -/

/-- The state transition equation (9.1): `x_{t+1} = Ax_t + Bu_t + Cε_{t+1}`, `x₀` given. -/
def ls_state {E : Type*} [Fintype E] (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ)
    (x₀ : X → ℝ) (u : ℕ → U → ℝ) (ε : ℕ → E → ℝ) : ℕ → X → ℝ
  | 0 => x₀
  | t + 1 => A *ᵥ ls_state A B C x₀ u ε t + B *ᵥ u t + C *ᵥ ε (t + 1)

/-- The deterministic transition `x_{t+1} = Ax_t + Bu_t`. -/
def ls_traj (A : Matrix X X ℝ) (B : Matrix X U ℝ) (x₀ : X → ℝ) (u : ℕ → U → ℝ) : ℕ → X → ℝ
  | 0 => x₀
  | t + 1 => A *ᵥ ls_traj A B x₀ u t + B *ᵥ u t

/-- The measurement equation (9.2): `y_t = Gx_t + Hu_{t−1} + Dε_t`, with `w t` standing for
`u_{t−1}` (so `w 0` is a given `u_{−1}`). -/
def ls_output {Y W E : Type*} [Fintype W] [Fintype E] (G : Matrix Y X ℝ) (H : Matrix Y W ℝ)
    (D : Matrix Y E ℝ) (x : ℕ → X → ℝ) (w : ℕ → W → ℝ) (ε : ℕ → E → ℝ) (t : ℕ) : Y → ℝ :=
  G *ᵥ x t + H *ᵥ w t + D *ᵥ ε t

/-! ### Definition 9.1.1: stabilizability -/

/-- **Definition 9.1.1** (Miao, p. 292): `(A, B)` is stabilizable if `A + BH` is stable for some
`H`. -/
def ls_Stabilizable (A : Matrix X X ℝ) (B : Matrix X U ℝ) : Prop :=
  ∃ H : Matrix U X ℝ, ls_Stable (A + B * H)

omit [DecidableEq X] in
/-- Miao, p. 292: under the control `u_t = Hx_t` the transition (9.1) becomes
`x_{t+1} = (A + BH)x_t + Cε_{t+1}`. -/
theorem definition_9_1_1_closed_loop {E : Type*} [Fintype E] (A : Matrix X X ℝ)
    (B : Matrix X U ℝ) (C : Matrix X E ℝ) (H : Matrix U X ℝ) {x : ℕ → X → ℝ}
    {u : ℕ → U → ℝ} {ε : ℕ → E → ℝ} (hx : ∀ t, x (t + 1) = A *ᵥ x t + B *ᵥ u t + C *ᵥ ε (t + 1))
    (hu : ∀ t, u t = H *ᵥ x t) (t : ℕ) :
    x (t + 1) = (A + B * H) *ᵥ x t + C *ᵥ ε (t + 1) := by
  rw [hx, hu, add_mulVec, mulVec_mulVec]

/-- Miao, pp. 292–293: the deterministic steady state `x̄ = 0` of the closed loop
`x_{t+1} = (A + BH)x_t` is (globally asymptotically) stable iff `A + BH` is stable. -/
theorem definition_9_1_1_steady_state (A : Matrix X X ℝ) (B : Matrix X U ℝ) (H : Matrix U X ℝ) :
    ls_Stable (A + B * H) ↔ ∀ (x : ℕ → X → ℝ), (∀ t, x (t + 1) = (A + B * H) *ᵥ x t) →
      Tendsto x atTop (𝓝 0) := by
  rw [ls_stable_iff_tendsto]
  constructor
  · intro h x hx
    have : ∀ t, x t = ((A + B * H) ^ t) *ᵥ x 0 := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [hx, ih, mulVec_mulVec, pow_succ']
    simpa only [← this] using h (x 0)
  · intro h v
    exact h (fun t => ((A + B * H) ^ t) *ᵥ v) fun t => by rw [mulVec_mulVec, pow_succ']

/-! ### Definition 9.1.2: controllability -/

/-- The controllability Gramian `∑_{j<r} AʲBB'A'ʲ`. -/
def ls_gram (A : Matrix X X ℝ) (B : Matrix X U ℝ) (r : ℕ) : Matrix X X ℝ :=
  ∑ j ∈ Finset.range r, A ^ j * B * Bᵀ * Aᵀ ^ j

/-- **Definition 9.1.2** (Miao, p. 293): `(A, B)` is controllable if
`∑_{j=0}^{nₓ−1} AʲBB'A'ʲ > 0`. -/
def ls_Controllable (A : Matrix X X ℝ) (B : Matrix X U ℝ) : Prop :=
  (ls_gram A B (Fintype.card X)).PosDef

/-- The quadratic form of the Gramian: `v'W_rv = ∑_{j<r} |B'A'ʲv|²`. -/
theorem ls_gram_quad (A : Matrix X X ℝ) (B : Matrix X U ℝ) (r : ℕ) (v : X → ℝ) :
    v ⬝ᵥ (ls_gram A B r *ᵥ v) =
      ∑ j ∈ Finset.range r, ((Bᵀ * Aᵀ ^ j) *ᵥ v) ⬝ᵥ ((Bᵀ * Aᵀ ^ j) *ᵥ v) := by
  classical
  simp only [ls_gram, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : A ^ j * B * Bᵀ * Aᵀ ^ j = (Bᵀ * Aᵀ ^ j)ᵀ * (1 : Matrix U U ℝ) * (Bᵀ * Aᵀ ^ j) := by
    rw [transpose_mul, transpose_pow, transpose_transpose, transpose_transpose, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [this, SS.LQProblem.dotProduct_transpose_mul_mul, one_mulVec]

theorem ls_gram_posSemidef (A : Matrix X X ℝ) (B : Matrix X U ℝ) (r : ℕ) :
    (ls_gram A B r).PosSemidef := by
  classical
  induction r with
  | zero => simpa [ls_gram] using PosSemidef.zero
  | succ r ih =>
    rw [ls_gram, Finset.sum_range_succ]
    refine ih.add ?_
    have : A ^ r * B * Bᵀ * Aᵀ ^ r = (Bᵀ * Aᵀ ^ r)ᵀ * (1 : Matrix U U ℝ) * (Bᵀ * Aᵀ ^ r) := by
      rw [transpose_mul, transpose_pow, transpose_transpose, transpose_transpose, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    rw [this]
    exact SS.LQProblem.posSemidef_transpose_mul_mul PosSemidef.one _

omit [DecidableEq X] in
theorem ls_dot_self_nonneg (v : X → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- The Gramian is positive definite iff every `v ≠ 0` has `B'A'ʲv ≠ 0` for some `j < r`. -/
theorem ls_gram_posDef_iff (A : Matrix X X ℝ) (B : Matrix X U ℝ) (r : ℕ) :
    (ls_gram A B r).PosDef ↔ ∀ v : X → ℝ, v ≠ 0 → ∃ j < r, (Bᵀ * Aᵀ ^ j) *ᵥ v ≠ 0 := by
  have hs := (SS.LQProblem.posSemidef_iff_real.1 (ls_gram_posSemidef A B r)).1
  rw [SS.LQProblem.posDef_iff_real]
  constructor
  · rintro ⟨-, h⟩ v hv
    by_contra hne
    push Not at hne
    have := h hv
    rw [ls_gram_quad, Finset.sum_eq_zero fun j hj => by
      rw [hne j (Finset.mem_range.1 hj), dotProduct_zero]] at this
    exact lt_irrefl _ this
  · intro h
    refine ⟨hs, fun v hv => ?_⟩
    obtain ⟨j, hj, hne⟩ := h v hv
    rw [ls_gram_quad]
    refine Finset.sum_pos' (fun i _ => ls_dot_self_nonneg _) ⟨j, Finset.mem_range.2 hj, ?_⟩
    exact lt_of_le_of_ne (ls_dot_self_nonneg _) (Ne.symm (mt dotProduct_self_eq_zero.1 hne))

omit [DecidableEq X] in
/-- The deterministic path: `x_r = Aʳx₀ + ∑_{j<r} AʲBu_{r−1−j}`. -/
theorem ls_traj_eq [DecidableEq X] (A : Matrix X X ℝ) (B : Matrix X U ℝ) (x₀ : X → ℝ)
    (u : ℕ → U → ℝ) (r : ℕ) :
    ls_traj A B x₀ u r = (A ^ r) *ᵥ x₀ + ∑ j ∈ Finset.range r, (A ^ j) *ᵥ (B *ᵥ u (r - 1 - j)) :=
  backward_sol_eq A (g := fun t => B *ᵥ u t) (fun _ => rfl) r

/-- With a positive definite Gramian `W_r`, any `x₀` can be steered to any `x̄` in `r` steps (with
`u_j = B'A'^{r−1−j}W_r⁻¹(x̄ − Aʳx₀)`, and `u_t = 0` from `r` on). -/
theorem ls_reach_of_gram {A : Matrix X X ℝ} {B : Matrix X U ℝ} {r : ℕ}
    (h : (ls_gram A B r).PosDef) (x₀ xbar : X → ℝ) :
    ∃ u : ℕ → U → ℝ, (∀ t, r ≤ t → u t = 0) ∧ ls_traj A B x₀ u r = xbar := by
  set W := ls_gram A B r
  have hW : IsUnit W.det := (isUnit_iff_isUnit_det _).1 h.isUnit
  set w := W⁻¹ *ᵥ (xbar - (A ^ r) *ᵥ x₀)
  refine ⟨fun j => if j < r then (Bᵀ * Aᵀ ^ (r - 1 - j)) *ᵥ w else 0,
    fun t ht => by simp [not_lt.2 ht], ?_⟩
  rw [ls_traj_eq]
  have hsum : ∑ j ∈ Finset.range r, (A ^ j) *ᵥ (B *ᵥ
      (if r - 1 - j < r then (Bᵀ * Aᵀ ^ (r - 1 - (r - 1 - j))) *ᵥ w else 0)) = W *ᵥ w := by
    simp only [W, ls_gram, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    simp only [show r - 1 - j < r by omega, ↓reduceIte, show r - 1 - (r - 1 - j) = j by omega,
      mulVec_mulVec, Matrix.mul_assoc]
  rw [hsum, mulVec_mulVec, mul_nonsing_inv _ hW, one_mulVec, add_sub_cancel]

/-- **Definition 9.1.2** and the reachability characterisation (Miao, p. 293, Whittle (1982),
Theorem 4.3.1): `(A, B)` is controllable iff from every initial state every target can be reached
in `r` steps, for every `r ≥ nₓ`. -/
theorem definition_9_1_2_iff (A : Matrix X X ℝ) (B : Matrix X U ℝ) :
    ls_Controllable A B ↔ ∀ r, Fintype.card X ≤ r → ∀ x₀ xbar : X → ℝ,
      ∃ u : ℕ → U → ℝ, ls_traj A B x₀ u r = xbar := by
  constructor
  · intro h r hr x₀ xbar
    have hr' : (ls_gram A B r).PosDef := by
      rw [ls_Controllable, ls_gram_posDef_iff] at h
      rw [ls_gram_posDef_iff]
      intro v hv
      obtain ⟨j, hj, hne⟩ := h v hv
      exact ⟨j, by omega, hne⟩
    obtain ⟨u, -, hu⟩ := ls_reach_of_gram hr' x₀ xbar
    exact ⟨u, hu⟩
  · intro h
    rw [ls_Controllable, ls_gram_posDef_iff]
    intro v hv
    by_contra hne
    push Not at hne
    obtain ⟨u, hu⟩ := h _ le_rfl 0 v
    rw [ls_traj_eq, mulVec_zero, zero_add] at hu
    have hvv : v ⬝ᵥ v = 0 := by
      nth_rewrite 1 [← hu]
      rw [sum_dotProduct]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [mulVec_mulVec, SS.LQProblem.mulVec_dotProduct, transpose_mul, transpose_pow,
        hne j (Finset.mem_range.1 hj), dotProduct_zero]
    exact hv (dotProduct_self_eq_zero.1 hvv)

/-- Miao, p. 293, "for any `r > 0`" is false: the shift `A = [[0, 0], [1, 0]]`, `B = e₁` is
controllable, but not every target can be reached in one step. -/
theorem ls_controllable_not_reach_one :
    ls_Controllable (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) ∧
      ¬ ∀ x₀ xbar : Fin 2 → ℝ, ∃ u : ℕ → Fin 1 → ℝ,
        ls_traj (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) !![1; 0] x₀ u 1 = xbar := by
  refine ⟨?_, fun h => ?_⟩
  · have : ls_gram (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)
        (Fintype.card (Fin 2)) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ls_gram, Finset.sum_range_succ, vecMul, dotProduct, Matrix.mul_apply,
          Fin.sum_univ_two]
    rw [ls_Controllable, this]
    exact PosDef.one
  · obtain ⟨u, hu⟩ := h 0 (Pi.single 1 1)
    have := congrFun hu 1
    simp [ls_traj, dotProduct] at this

/-- Miao, p. 293: stabilizable does not imply controllable. If `A` is stable and `B = 0`, then
`(A, B)` is stabilizable but (for `nₓ ≥ 1`) not controllable. -/
theorem ls_stabilizable_not_controllable [Nonempty X] {A : Matrix X X ℝ} (hA : ls_Stable A) :
    ls_Stabilizable A (0 : Matrix X U ℝ) ∧ ¬ ls_Controllable A (0 : Matrix X U ℝ) := by
  refine ⟨⟨0, by simpa using hA⟩, fun h => ?_⟩
  obtain ⟨i⟩ := ‹Nonempty X›
  have h1 := (SS.LQProblem.posDef_iff_real.1 h).2 (x := Pi.single i 1) (by simp)
  simp [ls_gram] at h1

/-! ### Definition 9.1.3: observability -/

variable {Y : Type*} [Fintype Y]

/-- **Definition 9.1.3** (Miao, p. 293): `(A, G)` is observable if
`∑_{j=0}^{nₓ−1} A'ʲG'GAʲ > 0`, i.e. `(A', G')` is controllable. -/
def ls_Observable (A : Matrix X X ℝ) (G : Matrix Y X ℝ) : Prop :=
  (ls_gram Aᵀ Gᵀ (Fintype.card X)).PosDef

theorem ls_observable_gram (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (r : ℕ) :
    ls_gram Aᵀ Gᵀ r = ∑ j ∈ Finset.range r, Aᵀ ^ j * Gᵀ * G * A ^ j := by
  simp only [ls_gram, transpose_transpose]

/-- Two paths of (9.1) with the same inputs and shocks differ by `Aᵗ(x₀ − x₀')`. -/
theorem ls_state_sub {E : Type*} [Fintype E] (A : Matrix X X ℝ) (B : Matrix X U ℝ)
    (C : Matrix X E ℝ) (x₀ x₀' : X → ℝ) (u : ℕ → U → ℝ) (ε : ℕ → E → ℝ) (t : ℕ) :
    ls_state A B C x₀ u ε t - ls_state A B C x₀' u ε t = (A ^ t) *ᵥ (x₀ - x₀') := by
  induction t with
  | zero => simp [ls_state]
  | succ t ih =>
    simp only [ls_state]
    rw [pow_succ', ← mulVec_mulVec, ← ih, mulVec_sub]
    abel

/-- **Definition 9.1.3** and its characterisation (Miao, p. 293, Whittle (1982), Theorem 4.4.1):
`(A, G)` is observable iff, for every `r ≥ nₓ − 1`, `x₀` is determined by `y₀, …, y_r` of
(9.1)–(9.2) given the inputs `u` and shocks `ε`. -/
theorem definition_9_1_3_iff {E W : Type*} [Fintype E] [Fintype W] (A : Matrix X X ℝ)
    (B : Matrix X U ℝ) (C : Matrix X E ℝ) (G : Matrix Y X ℝ) (H : Matrix Y W ℝ)
    (D : Matrix Y E ℝ) :
    ls_Observable A G ↔ ∀ r, Fintype.card X - 1 ≤ r → ∀ (u : ℕ → U → ℝ) (w : ℕ → W → ℝ)
      (ε : ℕ → E → ℝ) (x₀ x₀' : X → ℝ),
      (∀ t ≤ r, ls_output G H D (ls_state A B C x₀ u ε) w ε t =
        ls_output G H D (ls_state A B C x₀' u ε) w ε t) → x₀ = x₀' := by
  have hdiff : ∀ (u : ℕ → U → ℝ) (w : ℕ → W → ℝ) (ε : ℕ → E → ℝ) (x₀ x₀' : X → ℝ) t,
      ls_output G H D (ls_state A B C x₀ u ε) w ε t -
        ls_output G H D (ls_state A B C x₀' u ε) w ε t = (G * A ^ t) *ᵥ (x₀ - x₀') := by
    intro u w ε x₀ x₀' t
    simp only [ls_output]
    rw [← mulVec_mulVec, ← ls_state_sub A B C x₀ x₀' u ε t, mulVec_sub]
    abel
  have hgen : ∀ j, (Gᵀᵀ * Aᵀᵀ ^ j) = G * A ^ j := fun j => by simp only [transpose_transpose]
  rw [ls_Observable, ls_gram_posDef_iff]
  simp only [hgen]
  constructor
  · intro h r hr u w ε x₀ x₀' hy
    by_contra hne
    obtain ⟨j, hj, hj0⟩ := h (x₀ - x₀') (sub_ne_zero.2 hne)
    apply hj0
    rw [← hdiff u w ε, hy j (by omega), sub_self]
  · intro h v hv
    by_contra hne
    push Not at hne
    have hpos : 0 < Fintype.card X := by
      by_contra h0
      have : IsEmpty X := Fintype.card_eq_zero_iff.1 (by omega)
      exact hv (Subsingleton.elim _ _)
    have := h (Fintype.card X - 1) le_rfl 0 0 0 v 0 fun t ht => by
      rw [← sub_eq_zero, hdiff, sub_zero, hne t (by omega)]
    exact hv this

/-- Miao, p. 293, "for any `r > 0`" is false: with the shift `A` (`e₀ ↦ e₁ ↦ e₂ ↦ 0`) and
`G = e₂'`, `(A, G)` is observable, but `y₀, y₁` do not determine `x₀` (here `nₓ = 3`). -/
theorem ls_observable_not_two_outputs :
    ls_Observable (!![0, 0, 0; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ)
        (!![0, 0, 1] : Matrix (Fin 1) (Fin 3) ℝ) ∧
      ∃ x₀ x₀' : Fin 3 → ℝ, x₀ ≠ x₀' ∧ ∀ t ≤ 1,
        ls_output (!![0, 0, 1] : Matrix (Fin 1) (Fin 3) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
          (0 : Matrix (Fin 1) (Fin 1) ℝ)
          (ls_state (!![0, 0, 0; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ)
            (0 : Matrix (Fin 3) (Fin 1) ℝ) (0 : Matrix (Fin 3) (Fin 1) ℝ) x₀ 0 0) 0 0 t =
        ls_output (!![0, 0, 1] : Matrix (Fin 1) (Fin 3) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
          (0 : Matrix (Fin 1) (Fin 1) ℝ)
          (ls_state (!![0, 0, 0; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ)
            (0 : Matrix (Fin 3) (Fin 1) ℝ) (0 : Matrix (Fin 3) (Fin 1) ℝ) x₀' 0 0) 0 0 t := by
  refine ⟨?_, Pi.single 0 1, 0, fun h => by simpa using congrFun h 0, fun t ht => ?_⟩
  · have : ls_gram (!![0, 0, 0; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ
        (!![0, 0, 1] : Matrix (Fin 1) (Fin 3) ℝ)ᵀ (Fintype.card (Fin 3)) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ls_gram, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_three, pow_succ]
    rw [ls_Observable, this]
    exact PosDef.one
  · interval_cases t <;> funext i <;> fin_cases i <;>
      simp [ls_output, ls_state, dotProduct, Fin.sum_univ_three]

/-! ### Definition 9.1.4: detectability -/

/-- **Definition 9.1.4** (Miao, p. 294): `(A, G)` is detectable if `A − JG` is stable for some
`J`. -/
def ls_Detectable (A : Matrix X X ℝ) (G : Matrix Y X ℝ) : Prop :=
  ∃ J : Matrix X Y ℝ, ls_Stable (A - J * G)

omit [DecidableEq X] in
/-- (9.3) and the error equation (Miao, p. 294), corrected: if `x̂_{t+1} = Ax̂_t + Bu_t + AKa_t`
with `a_t = G(x_t − x̂_t) + Dε_t`, then `Δ_t = x_t − x̂_t` satisfies
`Δ_{t+1} = (A − AKG)Δ_t + Cε_{t+1} − AKDε_t`. -/
theorem eq_9_3_error {E : Type*} [Fintype E] (A : Matrix X X ℝ) (B : Matrix X U ℝ)
    (C : Matrix X E ℝ) (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (K : Matrix X Y ℝ)
    {x xh : ℕ → X → ℝ} {u : ℕ → U → ℝ} {ε : ℕ → E → ℝ}
    (hx : ∀ t, x (t + 1) = A *ᵥ x t + B *ᵥ u t + C *ᵥ ε (t + 1))
    (hxh : ∀ t, xh (t + 1) = A *ᵥ xh t + B *ᵥ u t + (A * K) *ᵥ (G *ᵥ (x t - xh t) + D *ᵥ ε t))
    (t : ℕ) :
    x (t + 1) - xh (t + 1) =
      (A - A * K * G) *ᵥ (x t - xh t) + C *ᵥ ε (t + 1) - (A * K * D) *ᵥ ε t := by
  rw [hx, hxh]
  simp only [sub_mulVec, mulVec_add, mulVec_sub, mulVec_mulVec]
  abel

/-- Miao, p. 294: if `A − AKG` is stable, the noise-free estimation error `Δ_t` tends to zero. -/
theorem eq_9_3_tendsto (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (K : Matrix X Y ℝ)
    (hK : ls_Stable (A - A * K * G)) {Δ : ℕ → X → ℝ}
    (hΔ : ∀ t, Δ (t + 1) = (A - A * K * G) *ᵥ Δ t) : Tendsto Δ atTop (𝓝 0) := by
  have : ∀ t, Δ t = ((A - A * K * G) ^ t) *ᵥ Δ 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [hΔ, ih, mulVec_mulVec, pow_succ']
  simpa only [← this] using (ls_stable_iff_tendsto _).1 hK (Δ 0)

/-- The printed error equation `Δ_{t+1} = (A − AKG)Δ_{t−1} + Cε_{t+1} + AKDε_t` is false: with
`A = 2`, all other matrices zero, `x₀ = 1`, `x̂₀ = 0`, (9.1) and (9.3) give `Δ_t = 2ᵗ`, so
`Δ₂ = 4 ≠ 2 = (A − AKG)Δ₀`. -/
theorem eq_9_3_misprint :
    ∃ (x xh : ℕ → Fin 1 → ℝ), (∀ t, x (t + 1) = (2 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x t) ∧
      (∀ t, xh (t + 1) = (2 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ xh t) ∧
      x 2 - xh 2 ≠ (2 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (x 0 - xh 0) := by
  refine ⟨fun t _ => 2 ^ t, fun _ _ => 0, fun t => ?_, fun t => ?_, ?_⟩
  · funext i
    fin_cases i
    simp [mulVec, dotProduct, pow_succ, Matrix.ofNat_apply, mul_comm]
  · funext i
    simp [mulVec, dotProduct]
  · intro h
    have := congrFun h 0
    norm_num [mulVec, dotProduct, Matrix.ofNat_apply] at this

/-- Miao, p. 294: for invertible `A`, detectability gives an updating rule (9.3) whose error
matrix `A − AKG` is stable (`K = A⁻¹J`). -/
theorem definition_9_1_4_rule {A : Matrix X X ℝ} {G : Matrix Y X ℝ} (hA : IsUnit A.det)
    (hd : ls_Detectable A G) : ∃ K : Matrix X Y ℝ, ls_Stable (A - A * K * G) := by
  obtain ⟨J, hJ⟩ := hd
  refine ⟨A⁻¹ * J, ?_⟩
  rwa [mul_nonsing_inv_cancel_left _ _ hA]

end Miao.LinearQuadratic

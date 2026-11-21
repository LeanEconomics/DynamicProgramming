/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.LinearSystems
import LinearQuadratic.CondExpL1
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Moments.Variance
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Block

/-!
# First-order linear stochastic systems: moments

Copied from `EconomicDynamics/RationalExpectations` (module `VARMoments`), namespace renamed.

Miao, §2.1, pp. 45–48, and the white-noise claims of p. 56. Concrete probability: a probability
measure `μ` on `(Ω, m0)`, a filtration `ℱ`, processes `z : ℕ → Ω → n → ℝ`, `ε : ℕ → Ω → k → ℝ`,
conditional expectations `μ[·|ℱ t]`, moments as integrals.

* (2.1) `z_{t+1} = Φz_t + Σε_{t+1}` and (2.2) `E_tε_{t+1} = 0`, `E_tε_{t+1}ε'_{t+1} = I` are the
  fields of `var_Model` (with `ε` adapted and square integrable, `z₀` `ℱ₀`-measurable and square
  integrable); `var_Model.z_memLp`, `var_Model.z_meas`: every `z_t` is square integrable and
  `ℱ_t`-measurable.
* Examples 2.1.1–2.1.3 as pathwise equivalences (`example_2_1_1`, `example_2_1_2`,
  `example_2_1_3`).
* Definition 2.1.1 (`var_IsCovStationary`). The book's "covariance depends only on `|t − s|`" is
  stated for the lag `t − s ≥ 0`: for vector processes `E(X_t − m)(X_s − m)'` with `t < s` is the
  transpose `Γ(s − t)'`, and `Γ(j)` need not be symmetric (`definition_2_1_1_not_symmetric`).
* Means: `μ_{t+1} = Φμ_t` (`var_mean_rec`), `μ_t = Φᵗμ₀ → 0` for stable `Φ`
  (`var_mean_tendsto_zero`), `μ_t = 0` if `μ₀ = 0`.
* The Lyapunov equation `C = ΦCΦ' + ΣΣ'`: for stable `Φ` its unique solution is
  `∑ⱼΦʲΣΣ'Φ'ʲ` (`var_lyapSol`, `lyap_fixed`, `lyap_unique`) and successive iteration converges to
  it from any start (`lyap_iterate_tendsto`); the second moments of every solution of (2.1)–(2.2)
  satisfy `E z_{t+1}z'_{t+1} = Φ E z_tz'_t Φ' + ΣΣ'` (`var_mom_rec`) and converge to it
  (`var_mom_tendsto`); a covariance-stationary solution has mean `0`, `C_z(0) = ∑ⱼΦʲΣΣ'Φ'ʲ` and
  `C_z(j) = ΦʲC_z(0)` (`var_stationary_moments`), and conversely `z₀` with these moments makes `z`
  covariance stationary (`var_stationary_of_initial`): the stationary first and second moments
  are unique. `C_z(j) = ΦʲC_z(0)` (`var_autocov`).
* Impulse responses: `z_{t+j} = Φʲz_t + ∑_{i<j}ΦⁱΣε_{t+j−i}` (`var_ma_shift`), the
  finite-horizon MA representation `z_{t+1} = Φ^{t+1}z₀ + ∑_{j≤t}ΦʲΣε_{t+1−j}` (`var_ma`), the
  initial-condition term vanishes for stable `Φ` (`var_ma_initial_tendsto`), and `ΦʲΣ` is the
  response of `z_{t+1+j}` to a shock to `ε_{t+1}` (`var_impulse_response`).
* White noise (Definition 2.3.3, `var_IsWhiteNoise`): it is stable since
  `E|X| ≤ (EX²)^{1/2}` (`whiteNoise_stable`, `whiteNoise_stable_L1`); `{ε_{t+1}}` satisfying
  (2.2) is a white noise with `Σ = I` (`mds_whiteNoise`). (A white noise that violates (2.2), and
  the failure of "unique stationary distribution", are in `VARExamples`.)

Departure: "unique stationary distribution" (p. 47) is not implied by (2.1)–(2.2), which pin down
only the first two conditional moments of `ε`; what is proved is uniqueness of the stationary
first and second moments (a counterexample to the distributional claim is in `VARExamples`).
-/

open MeasureTheory Filter Topology

namespace Miao.LinearQuadratic

open scoped Matrix

/-! ### Examples 2.1.1–2.1.3 (pathwise) -/

/-- **Example 2.1.1** (Miao, p. 46): with `b ≠ 1` and `z_t = y_t − d/(1 − b)`,
`y_{t+1} = by_t + d + σε_{t+1}` iff `z_{t+1} = bz_t + σε_{t+1}`. -/
theorem example_2_1_1 {b d σ : ℝ} (hb : 1 - b ≠ 0) (y e : ℕ → ℝ) :
    (∀ t, y (t + 1) = b * y t + d + σ * e (t + 1)) ↔
      ∀ t, y (t + 1) - d / (1 - b) = b * (y t - d / (1 - b)) + σ * e (t + 1) := by
  refine forall_congr' fun t => ?_
  have h : d = (1 - b) * (d / (1 - b)) := by field_simp
  constructor
  · intro h1
    linear_combination h1 + h
  · intro h1
    linear_combination h1 - h

/-- **Example 2.1.2** (Miao, p. 46): `y_{t+1} = by_t + ε_{t+1} + cε_t` iff the state
`(y_t, ε_t)` follows `(y_{t+1}, ε_{t+1})' = [b c; 0 0](y_t, ε_t)' + (1, 1)'ε_{t+1}`. -/
theorem example_2_1_2 {b c : ℝ} (y e : ℕ → ℝ) :
    (∀ t, y (t + 1) = b * y t + e (t + 1) + c * e t) ↔
      ∀ t, ![y (t + 1), e (t + 1)] =
        !![b, c; 0, 0] *ᵥ ![y t, e t] + e (t + 1) • (![1, 1] : Fin 2 → ℝ) := by
  refine forall_congr' fun t => ?_
  constructor
  · intro h
    ext i
    fin_cases i
    · simp [h]
      ring
    · simp
  · intro h
    have := congrFun h 0
    simp at this
    linarith
/-- **Example 2.1.3** (Miao, p. 46): the VAR(2) `y_{t+1} = A₁y_t + A₂y_{t−1} + Cε_{t+1}` (dates
`t ≥ 1`) iff the stacked state `(y_t, y_{t−1})` follows the first-order system with
`[A₁ A₂; I 0]` and `[C; 0]`. -/
theorem example_2_1_3 {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]
    (A₁ A₂ : Matrix n n ℝ) (C : Matrix n k ℝ) (y : ℕ → n → ℝ) (e : ℕ → k → ℝ) :
    (∀ t, y (t + 2) = A₁ *ᵥ y (t + 1) + A₂ *ᵥ y t + C *ᵥ e (t + 2)) ↔
      ∀ t, Sum.elim (y (t + 2)) (y (t + 1)) =
        Matrix.fromBlocks A₁ A₂ 1 0 *ᵥ Sum.elim (y (t + 1)) (y t) +
          Matrix.fromRows C 0 *ᵥ e (t + 2) := by
  refine forall_congr' fun t => ?_
  rw [Matrix.fromBlocks_mulVec, Matrix.fromRows_mulVec]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, Sum.elim_comp_inl,
    Sum.elim_comp_inr]
  rw [← Sum.elim_add_add, add_zero]
  constructor
  · intro h
    rw [h]
  · intro h
    have := congrArg (fun v : n ⊕ n → ℝ => v ∘ Sum.inl) h
    simpa only [Sum.elim_comp_inl] using this

/-! ### Matrix lemmas: powers with geometric decay -/

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem var_pow_entry_le {Φ : Matrix n n ℝ} {K a : ℝ} (hΦ : HasGeomDecay Φ K a) (k : ℕ)
    (i j : n) : |(Φ ^ k) i j| ≤ K * a ^ k := by
  have h := hΦ.2.2.2 k (Pi.single j 1)
  have e : ((Φ ^ k) *ᵥ Pi.single j 1) i = (Φ ^ k) i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hs : ‖(Pi.single j 1 : n → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hK : 0 ≤ K * a ^ k := mul_nonneg hΦ.2.2.1 (pow_nonneg hΦ.1 k)
  calc |(Φ ^ k) i j| = ‖((Φ ^ k) *ᵥ Pi.single j 1) i‖ := by rw [e, Real.norm_eq_abs]
    _ ≤ ‖(Φ ^ k) *ᵥ Pi.single j 1‖ := norm_le_pi_norm _ i
    _ ≤ K * a ^ k * ‖(Pi.single j 1 : n → ℝ)‖ := h
    _ ≤ K * a ^ k * 1 := by gcongr
    _ = K * a ^ k := mul_one _

/-- The `ℓ¹` size of a matrix, `∑ᵢⱼ|Yᵢⱼ|`. -/
def var_l1 (Y : Matrix n n ℝ) : ℝ := ∑ c, ∑ d, |Y c d|

omit [DecidableEq n] in
theorem var_l1_nonneg (Y : Matrix n n ℝ) : 0 ≤ var_l1 Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq n] in
theorem var_sandwich_apply (A Y B : Matrix n n ℝ) (i j : n) :
    (A * Y * Bᵀ) i j = ∑ c, ∑ d, A i c * Y c d * B j d := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- `|(ΦᵏYΦ'ᵏ)ᵢⱼ| ≤ (Kaᵏ)²∑|Y|`. -/
theorem var_sandwich_le {Φ : Matrix n n ℝ} {K a : ℝ} (hΦ : HasGeomDecay Φ K a) (k : ℕ)
    (Y : Matrix n n ℝ) (i j : n) :
    |(Φ ^ k * Y * (Φ ^ k)ᵀ) i j| ≤ (K * a ^ k) ^ 2 * var_l1 Y := by
  rw [var_sandwich_apply, var_l1, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 := var_pow_entry_le hΦ k i c
  have h2 := var_pow_entry_le hΦ k j d
  have hK : 0 ≤ K * a ^ k := mul_nonneg hΦ.2.2.1 (pow_nonneg hΦ.1 k)
  calc |(Φ ^ k) i c| * |Y c d| * |(Φ ^ k) j d| ≤ (K * a ^ k) * |Y c d| * (K * a ^ k) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2 (abs_nonneg _)
          (mul_nonneg hK (abs_nonneg _))
    _ = (K * a ^ k) ^ 2 * |Y c d| := by ring

/-! ### The Lyapunov equation -/

/-- The Lyapunov map `C ↦ ΦCΦ' + Q` (Miao, p. 47). -/
def var_lyapMap (Φ Q : Matrix n n ℝ) (X : Matrix n n ℝ) : Matrix n n ℝ := Φ * X * Φᵀ + Q

/-- The candidate solution `∑ⱼΦʲQΦ'ʲ` of the Lyapunov equation, entrywise. -/
noncomputable def var_lyapSol (Φ Q : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => ∑' k : ℕ, (Φ ^ k * Q * (Φ ^ k)ᵀ) i j

theorem var_lyap_summable {Φ : Matrix n n ℝ} {K a : ℝ} (hΦ : HasGeomDecay Φ K a)
    (Q : Matrix n n ℝ) (i j : n) : Summable fun k : ℕ => (Φ ^ k * Q * (Φ ^ k)ᵀ) i j := by
  have ha : a ^ 2 < 1 := by nlinarith [hΦ.1, hΦ.2.1]
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (sq_nonneg a) ha).mul_left (K ^ 2 * var_l1 Q)) fun k => ?_
  rw [Real.norm_eq_abs]
  refine (var_sandwich_le hΦ k Q i j).trans (le_of_eq ?_)
  rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
  ring

/-- Iterating the Lyapunov map: `Lᵏ(X₀) = ΦᵏX₀Φ'ᵏ + ∑_{j<k}ΦʲQΦ'ʲ`. -/
theorem var_lyap_iterate (Φ Q X0 : Matrix n n ℝ) (k : ℕ) :
    (var_lyapMap Φ Q)^[k] X0 =
      Φ ^ k * X0 * (Φ ^ k)ᵀ + ∑ j ∈ Finset.range k, Φ ^ j * Q * (Φ ^ j)ᵀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, var_lyapMap, Finset.sum_range_succ']
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul, pow_succ',
      Matrix.transpose_mul, pow_zero, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one,
      Matrix.mul_assoc]
    abel

/-- Miao, p. 47: "It can be solved numerically by successive iteration": for stable `Φ` the
iterates of `C ↦ ΦCΦ' + Q` converge (entrywise) to `∑ⱼΦʲQΦ'ʲ` from any start. -/
theorem lyap_iterate_tendsto (Φ : Matrix n n ℝ) (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom))
    (Q X0 : Matrix n n ℝ) (i j : n) :
    Tendsto (fun k => ((var_lyapMap Φ Q)^[k] X0) i j) atTop (𝓝 (var_lyapSol Φ Q i j)) := by
  obtain ⟨K, a, hd⟩ := hasGeomDecay_of_isStableMatrix Φ hΦ
  simp only [var_lyap_iterate, Matrix.add_apply, Matrix.sum_apply]
  rw [← zero_add (var_lyapSol Φ Q i j)]
  refine Tendsto.add ?_ ?_
  · have ha : (fun k : ℕ => (K * a ^ k) ^ 2 * var_l1 X0) = fun k => K ^ 2 * var_l1 X0 * (a ^ 2) ^ k
      := by funext k; rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]; ring
    have hlim : Tendsto (fun k : ℕ => (K * a ^ k) ^ 2 * var_l1 X0) atTop (𝓝 0) := by
      rw [ha]
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg a)
        (by nlinarith [hd.1, hd.2.1])).const_mul (K ^ 2 * var_l1 X0)
    refine squeeze_zero_norm (fun k => ?_) hlim
    rw [Real.norm_eq_abs]
    exact var_sandwich_le hd k X0 i j
  · exact (var_lyap_summable hd Q i j).hasSum.tendsto_sum_nat

omit [DecidableEq n] in
theorem var_lyapMap_apply (Φ Q X : Matrix n n ℝ) (i j : n) :
    var_lyapMap Φ Q X i j = ∑ c, ∑ d, Φ i c * X c d * Φ j d + Q i j := by
  rw [var_lyapMap, Matrix.add_apply, var_sandwich_apply]

omit [DecidableEq n] in
theorem var_lyapMap_continuous (Φ Q : Matrix n n ℝ) {X : ℕ → Matrix n n ℝ}
    {Y : Matrix n n ℝ} (h : ∀ i j, Tendsto (fun k => X k i j) atTop (𝓝 (Y i j))) (i j : n) :
    Tendsto (fun k => var_lyapMap Φ Q (X k) i j) atTop (𝓝 (var_lyapMap Φ Q Y i j)) := by
  simp only [var_lyapMap_apply]
  refine Tendsto.add ?_ tendsto_const_nhds
  refine tendsto_finsetSum _ fun c _ => tendsto_finsetSum _ fun d _ => ?_
  exact ((h c d).const_mul _).mul_const _

/-- Miao, p. 47 (the discrete Lyapunov equation): for stable `Φ`, `∑ⱼΦʲQΦ'ʲ` solves
`C = ΦCΦ' + Q`. -/
theorem lyap_fixed (Φ : Matrix n n ℝ) (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom))
    (Q : Matrix n n ℝ) : var_lyapMap Φ Q (var_lyapSol Φ Q) = var_lyapSol Φ Q := by
  ext i j
  have h1 := lyap_iterate_tendsto Φ hΦ Q 0
  have h2 := var_lyapMap_continuous Φ Q h1 i j
  have h3 : Tendsto (fun k => ((var_lyapMap Φ Q)^[k + 1] 0) i j) atTop
      (𝓝 (var_lyapSol Φ Q i j)) := (tendsto_add_atTop_iff_nat 1).2 (h1 i j)
  simp only [Function.iterate_succ_apply'] at h3
  exact tendsto_nhds_unique h2 h3

/-- Miao, p. 47: for stable `Φ` the Lyapunov equation `C = ΦCΦ' + Q` has exactly one solution. -/
theorem lyap_unique (Φ : Matrix n n ℝ) (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom))
    (Q C : Matrix n n ℝ) (hC : var_lyapMap Φ Q C = C) : C = var_lyapSol Φ Q := by
  ext i j
  have hfix : ∀ k, (var_lyapMap Φ Q)^[k] C = C := fun k =>
    Function.iterate_fixed hC k
  have h := lyap_iterate_tendsto Φ hΦ Q C i j
  simp only [hfix] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

/-! ### The model (2.1)–(2.2) -/

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {k : Type*} [DecidableEq k]

/-- The shock conditions (2.2) (Miao, p. 46), with `ε` adapted and square integrable:
`E_tε_{t+1} = 0`, `E_tε_{t+1}ε'_{t+1} = I`. -/
structure var_ShockMDS (μ : Measure Ω) (ℱ : Filtration ℕ m0) (ε : ℕ → Ω → k → ℝ) : Prop where
  /-- `ε_t` is square integrable. -/
  memLp : ∀ t i, MemLp (fun ω => ε t ω i) 2 μ
  /-- `ε_t` is `ℱ_t`-measurable. -/
  meas : ∀ t i, Measurable[ℱ t] fun ω => ε t ω i
  /-- `E_tε_{t+1} = 0`. -/
  mds : ∀ t i, μ[fun ω => ε (t + 1) ω i | ℱ t] =ᵐ[μ] 0
  /-- `E_tε_{t+1}ε'_{t+1} = I`. -/
  cvar : ∀ t i j, μ[fun ω => ε (t + 1) ω i * ε (t + 1) ω j | ℱ t] =ᵐ[μ]
    fun _ => if i = j then 1 else 0

variable [Fintype k]

variable (n) (μ : Measure Ω) (ℱ : Filtration ℕ m0) (Φ : Matrix n n ℝ) (Sg : Matrix n k ℝ)
  (z : ℕ → Ω → n → ℝ) (ε : ℕ → Ω → k → ℝ) in
/-- The model (2.1)–(2.2) (Miao, pp. 45–46): `z_{t+1} = Φz_t + Σε_{t+1}`, `z₀` given
(`ℱ₀`-measurable, square integrable), `ε` satisfying (2.2). -/
structure var_Model : Prop where
  /-- (2.1). -/
  eq21 : ∀ t ω, z (t + 1) ω = Φ *ᵥ z t ω + Sg *ᵥ ε (t + 1) ω
  /-- `z₀` is square integrable. -/
  z0_memLp : ∀ i, MemLp (fun ω => z 0 ω i) 2 μ
  /-- `z₀` is `ℱ₀`-measurable. -/
  z0_meas : ∀ i, Measurable[ℱ 0] fun ω => z 0 ω i
  /-- (2.2). -/
  shock : var_ShockMDS μ ℱ ε

/-- The mean vector `Ez`. -/
noncomputable def var_mean (μ : Measure Ω) (X : Ω → n → ℝ) : n → ℝ :=
  fun i => ∫ ω, X ω i ∂μ

/-- The second-moment matrix `EXY'`. -/
noncomputable def var_mom {p q : Type*} (μ : Measure Ω) (X : Ω → p → ℝ) (Y : Ω → q → ℝ) :
    Matrix p q ℝ :=
  Matrix.of fun i j => ∫ ω, X ω i * Y ω j ∂μ

omit [DecidableEq n] [DecidableEq k] in
theorem var_rec_apply {Φ : Matrix n n ℝ} {Sg : Matrix n k ℝ} {z : ℕ → Ω → n → ℝ}
    {ε : ℕ → Ω → k → ℝ} (hrec : ∀ t ω, z (t + 1) ω = Φ *ᵥ z t ω + Sg *ᵥ ε (t + 1) ω)
    (t : ℕ) (i : n) :
    (fun ω => z (t + 1) ω i) =
      fun ω => ∑ c, Φ i c * z t ω c + ∑ l, Sg i l * ε (t + 1) ω l := by
  funext ω
  rw [hrec]
  simp [Matrix.mulVec, dotProduct]

namespace var_Model

variable {μ : Measure Ω} {ℱ : Filtration ℕ m0} {Φ : Matrix n n ℝ} {Sg : Matrix n k ℝ}
  {z : ℕ → Ω → n → ℝ} {ε : ℕ → Ω → k → ℝ}

omit [DecidableEq n] in
theorem z_memLp (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) (i : n) :
    MemLp (fun ω => z t ω i) 2 μ := by
  induction t generalizing i with
  | zero => exact h.z0_memLp i
  | succ t ih =>
    rw [var_rec_apply h.eq21]
    refine MemLp.add ?_ ?_
    · exact memLp_finsetSum _ fun c _ => (ih c).const_mul _
    · exact memLp_finsetSum _ fun l _ => (h.shock.memLp (t + 1) l).const_mul _

omit [DecidableEq n] in
theorem z_meas (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) (i : n) :
    Measurable[ℱ t] fun ω => z t ω i := by
  induction t generalizing i with
  | zero => exact h.z0_meas i
  | succ t ih =>
    rw [var_rec_apply h.eq21]
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum _ fun c _ => ?_
      exact ((ih c).mono (ℱ.mono (Nat.le_succ t)) le_rfl).const_mul _
    · exact Finset.measurable_sum _ fun l _ => (h.shock.meas (t + 1) l).const_mul _

end var_Model

/-! ### Moments of the shocks -/

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}

omit [Fintype k] in
/-- `E[Xε_{t+1}] = 0` for `ℱ_t`-measurable square-integrable `X` (tower property). -/
theorem var_cross_zero {ε : ℕ → Ω → k → ℝ} (hε : var_ShockMDS μ ℱ ε) {t : ℕ} {X : Ω → ℝ}
    (hX : Measurable[ℱ t] X) (hX2 : MemLp X 2 μ) (i : k) :
    ∫ ω, X ω * ε (t + 1) ω i ∂μ = 0 := by
  have hεi : MemLp (fun ω => ε (t + 1) ω i) 2 μ := hε.memLp (t + 1) i
  have hprod : Integrable (X * fun ω => ε (t + 1) ω i) μ := hX2.integrable_mul hεi
  have h1 := condExp_mul_of_stronglyMeasurable_left hX.stronglyMeasurable hprod
    (hεi.integrable one_le_two)
  have h2 : ∫ ω, X ω * ε (t + 1) ω i ∂μ = ∫ ω, (μ[X * fun ω => ε (t + 1) ω i | ℱ t]) ω ∂μ :=
    (integral_condExp (ℱ.le t)).symm
  have h3 : X * μ[fun ω => ε (t + 1) ω i | ℱ t] =ᵐ[μ] 0 := by
    filter_upwards [hε.mds t i] with ω hω
    simp [hω]
  rw [h2, integral_congr_ae (h1.trans h3)]
  simp

omit [Fintype k] in
/-- `Eε_{t+1} = 0`. -/
theorem var_mean_eps_zero {ε : ℕ → Ω → k → ℝ} (hε : var_ShockMDS μ ℱ ε) (t : ℕ) (i : k) :
    ∫ ω, ε (t + 1) ω i ∂μ = 0 := by
  rw [← integral_condExp (ℱ.le t), integral_congr_ae (hε.mds t i)]
  simp

omit [Fintype k] in
/-- `Eε_{t+1}ε'_{t+1} = I`. -/
theorem var_mom_eps {ε : ℕ → Ω → k → ℝ} (hε : var_ShockMDS μ ℱ ε) (t : ℕ) (i j : k) :
    ∫ ω, ε (t + 1) ω i * ε (t + 1) ω j ∂μ = if i = j then 1 else 0 := by
  rw [← integral_condExp (ℱ.le t), integral_congr_ae (hε.cvar t i j)]
  simp

omit [IsProbabilityMeasure μ] in
/-- `∫(∑ₛ wₛfₛ)g = ∑ₛ wₛ∫fₛg` for square-integrable `fₛ, g`. -/
theorem var_integral_sum_mul {ι : Type*} [Fintype ι] (w : ι → ℝ) {f : ι → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ s, MemLp (f s) 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, (∑ s, w s * f s ω) * g ω ∂μ = ∑ s, w s * ∫ ω, f s ω * g ω ∂μ := by
  simp only [Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext ω
    ring
  · intro s _
    have := ((hf s).integrable_mul hg).const_mul (w s)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]
    ring

omit [IsProbabilityMeasure μ] in
/-- `∫g(∑ₛ wₛfₛ) = ∑ₛ wₛ∫gfₛ`. -/
theorem var_integral_mul_sum {ι : Type*} [Fintype ι] (w : ι → ℝ) {f : ι → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ s, MemLp (f s) 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, g ω * (∑ s, w s * f s ω) ∂μ = ∑ s, w s * ∫ ω, g ω * f s ω ∂μ := by
  have := var_integral_sum_mul w hf hg
  simp only [mul_comm (g _)] at this ⊢
  rw [← this]

/-! ### Means -/

variable {Φ : Matrix n n ℝ} {Sg : Matrix n k ℝ} {z : ℕ → Ω → n → ℝ} {ε : ℕ → Ω → k → ℝ}

omit [DecidableEq n] in
/-- Miao, p. 47: taking expectations of (2.1), `μ_{t+1} = Φμ_t`. -/
theorem var_mean_rec (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) :
    var_mean μ (z (t + 1)) = Φ *ᵥ var_mean μ (z t) := by
  funext i
  have hz := h.z_memLp t
  simp only [var_mean]
  rw [var_rec_apply h.eq21, integral_add, integral_finsetSum, integral_finsetSum]
  · simp only [integral_const_mul, var_mean_eps_zero h.shock, mul_zero, Finset.sum_const_zero,
      add_zero, Matrix.mulVec, dotProduct]
    rfl
  · exact fun l _ => ((h.shock.memLp (t + 1) l).integrable one_le_two).const_mul _
  · exact fun c _ => ((hz c).integrable one_le_two).const_mul _
  · exact integrable_finsetSum _ fun c _ => ((hz c).integrable one_le_two).const_mul _
  · exact integrable_finsetSum _ fun l _ =>
      ((h.shock.memLp (t + 1) l).integrable one_le_two).const_mul _

/-- Miao, p. 47: `μ_t = Φᵗμ₀`. -/
theorem var_mean_eq (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) :
    var_mean μ (z t) = (Φ ^ t) *ᵥ var_mean μ (z 0) := by
  induction t with
  | zero => rw [pow_zero, Matrix.one_mulVec]
  | succ t ih => rw [var_mean_rec h, ih, Matrix.mulVec_mulVec, pow_succ']

/-- Miao, p. 47: if all eigenvalues of `Φ` are inside the unit circle, `μ_t → 0`; with
`μ₀ = 0`, `μ_t = 0` for all `t`. -/
theorem var_mean_tendsto_zero (h : var_Model n μ ℱ Φ Sg z ε)
    (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom)) :
    Tendsto (fun t => var_mean μ (z t)) atTop (𝓝 0) ∧
      (var_mean μ (z 0) = 0 → ∀ t, var_mean μ (z t) = 0) := by
  refine ⟨?_, fun h0 t => by rw [var_mean_eq h, h0, Matrix.mulVec_zero]⟩
  rw [show (fun t => var_mean μ (z t)) = fun t => (Φ ^ t) *ᵥ var_mean μ (z 0) from
    funext (var_mean_eq h)]
  exact tendsto_of_isStableMatrix Φ hΦ _

/-! ### Second moments -/

/-- The state and shock of date `t + 1` as one family indexed by `n ⊕ k`. -/
def var_stack (z : ℕ → Ω → n → ℝ) (ε : ℕ → Ω → k → ℝ) (t : ℕ) : n ⊕ k → Ω → ℝ :=
  Sum.elim (fun c ω => z t ω c) (fun l ω => ε (t + 1) ω l)

omit [DecidableEq n] [DecidableEq k] in
theorem var_rec_stack (hrec : ∀ t ω, z (t + 1) ω = Φ *ᵥ z t ω + Sg *ᵥ ε (t + 1) ω)
    (t : ℕ) (i : n) :
    (fun ω => z (t + 1) ω i) = fun ω => ∑ s, Sum.elim (Φ i) (Sg i) s * var_stack z ε t s ω := by
  rw [var_rec_apply hrec]
  funext ω
  simp [var_stack, Fintype.sum_sum_type]

omit [DecidableEq n] [DecidableEq k] in
theorem var_rec_stack_apply (hrec : ∀ t ω, z (t + 1) ω = Φ *ᵥ z t ω + Sg *ᵥ ε (t + 1) ω)
    (t : ℕ) (i : n) (ω : Ω) :
    z (t + 1) ω i = ∑ s, Sum.elim (Φ i) (Sg i) s * var_stack z ε t s ω :=
  congrFun (var_rec_stack hrec t i) ω

omit [DecidableEq n] [IsProbabilityMeasure μ] in
theorem var_stack_memLp (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) (s : n ⊕ k) :
    MemLp (var_stack z ε t s) 2 μ := by
  rcases s with c | l
  · exact h.z_memLp t c
  · exact h.shock.memLp (t + 1) l

omit [DecidableEq n] in
/-- Miao, p. 47: the second moments satisfy `Ez_{t+1}z'_{t+1} = Φ(Ez_tz'_t)Φ' + ΣΣ'`. -/
theorem var_mom_rec (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) :
    var_mom μ (z (t + 1)) (z (t + 1)) = var_lyapMap Φ (Sg * Sgᵀ) (var_mom μ (z t) (z t)) := by
  ext i j
  have hst := var_stack_memLp h t
  have hzj : MemLp (fun ω => z (t + 1) ω j) 2 μ := h.z_memLp (t + 1) j
  have e1 : var_mom μ (z (t + 1)) (z (t + 1)) i j =
      ∑ s, Sum.elim (Φ i) (Sg i) s *
        ∫ ω, var_stack z ε t s ω * z (t + 1) ω j ∂μ := by
    simp only [var_mom, Matrix.of_apply]
    rw [show (fun ω => z (t + 1) ω i * z (t + 1) ω j) =
      fun ω => (∑ s, Sum.elim (Φ i) (Sg i) s * var_stack z ε t s ω) * z (t + 1) ω j from
        funext fun ω => by rw [var_rec_stack_apply h.eq21 t i ω]]
    exact var_integral_sum_mul _ hst hzj
  have e2 : ∀ s, ∫ ω, var_stack z ε t s ω * z (t + 1) ω j ∂μ =
      ∑ r, Sum.elim (Φ j) (Sg j) r * ∫ ω, var_stack z ε t s ω * var_stack z ε t r ω ∂μ := by
    intro s
    rw [show (fun ω => var_stack z ε t s ω * z (t + 1) ω j) =
      fun ω => var_stack z ε t s ω * ∑ r, Sum.elim (Φ j) (Sg j) r * var_stack z ε t r ω from
        funext fun ω => by rw [var_rec_stack_apply h.eq21 t j ω]]
    exact var_integral_mul_sum _ hst (hst s)
  have hzε : ∀ c l, ∫ ω, z t ω c * ε (t + 1) ω l ∂μ = 0 := fun c l =>
    var_cross_zero h.shock (h.z_meas t c) (h.z_memLp t c) l
  have hεz : ∀ l c, ∫ ω, ε (t + 1) ω l * z t ω c ∂μ = 0 := fun l c => by
    simp only [mul_comm (ε _ _ _)]; exact hzε c l
  rw [e1]
  simp only [e2]
  simp only [Fintype.sum_sum_type, var_stack, Sum.elim_inl, Sum.elim_inr]
  simp only [hzε, hεz, var_mom_eps h.shock, mul_zero, Finset.sum_const_zero, add_zero,
    zero_add, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [var_lyapMap_apply]
  simp only [var_mom, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

omit [DecidableEq n] in
/-- The second moments are the Lyapunov iterates: `Ez_tz'_t = Lᵗ(Ez₀z'₀)`. -/
theorem var_mom_iterate (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) :
    var_mom μ (z t) (z t) = (var_lyapMap Φ (Sg * Sgᵀ))^[t] (var_mom μ (z 0) (z 0)) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [var_mom_rec h, ih, Function.iterate_succ_apply']

/-- Miao, p. 47: for stable `Φ` the second moments of every solution converge to the solution
`∑ⱼΦʲΣΣ'Φ'ʲ` of the Lyapunov equation. -/
theorem var_mom_tendsto (h : var_Model n μ ℱ Φ Sg z ε)
    (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom)) (i j : n) :
    Tendsto (fun t => var_mom μ (z t) (z t) i j) atTop
      (𝓝 (var_lyapSol Φ (Sg * Sgᵀ) i j)) := by
  rw [show (fun t => var_mom μ (z t) (z t) i j) =
    fun t => ((var_lyapMap Φ (Sg * Sgᵀ))^[t] (var_mom μ (z 0) (z 0))) i j from
      funext fun t => by rw [var_mom_iterate h]]
  exact lyap_iterate_tendsto Φ hΦ _ _ i j

/-- Miao, p. 47: `C_z(j) = Ez_{t+j}z'_t = ΦʲEz_tz'_t` (the autocovariogram). -/
theorem var_autocov (h : var_Model n μ ℱ Φ Sg z ε) (t j : ℕ) :
    var_mom μ (z (t + j)) (z t) = Φ ^ j * var_mom μ (z t) (z t) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Matrix.mul_assoc, ← ih]
    ext a b
    have hst := var_stack_memLp h (t + j)
    have hzb : MemLp (fun ω => z t ω b) 2 μ := h.z_memLp t b
    have hmb : Measurable[ℱ (t + j)] fun ω => z t ω b :=
      (h.z_meas t b).mono (ℱ.mono (Nat.le_add_right t j)) le_rfl
    simp only [var_mom, Matrix.of_apply, Matrix.mul_apply]
    rw [show (fun ω => z (t + (j + 1)) ω a * z t ω b) =
      fun ω => (∑ s, Sum.elim (Φ a) (Sg a) s * var_stack z ε (t + j) s ω) * z t ω b from
        funext fun ω => by rw [← var_rec_stack_apply h.eq21 (t + j) a ω, Nat.add_assoc],
      var_integral_sum_mul _ hst hzb]
    simp only [Fintype.sum_sum_type, var_stack, Sum.elim_inl, Sum.elim_inr]
    have hz : ∀ l, ∫ ω, ε (t + j + 1) ω l * z t ω b ∂μ = 0 := fun l => by
      simp only [mul_comm (ε _ _ _)]; exact var_cross_zero h.shock hmb hzb l
    simp only [hz, mul_zero, Finset.sum_const_zero, add_zero]

/-- **Definition 2.1.1** (Miao, p. 47): `X` is covariance stationary: square integrable, constant
mean `m`, and `E(X_{t+j} − m)(X_t − m)'` depends only on the lag `j ≥ 0`. -/
def var_IsCovStationary (μ : Measure Ω) (X : ℕ → Ω → n → ℝ) : Prop :=
  (∀ t i, MemLp (fun ω => X t ω i) 2 μ) ∧ ∃ m : n → ℝ, ∃ Γ : ℕ → Matrix n n ℝ,
    (∀ t, var_mean μ (X t) = m) ∧
      ∀ t j, var_mom μ (fun ω => X (t + j) ω - m) (fun ω => X t ω - m) = Γ j

/-- **Definition 2.1.1** (Miao, p. 47), as printed ("depends only on `|t − s|`"), would force
`Γ(j)` to be symmetric, since `E(X_s − m)(X_t − m)' = (E(X_t − m)(X_s − m)')'`. For a vector
process that is false: for `Φ = [0 1/2; 0 0]`, `Σ = I`, the stationary `C(0) = I + ΦΦ'` solves
the Lyapunov equation but `C(1) = ΦC(0)` is not symmetric. -/
theorem definition_2_1_1_not_symmetric :
    let Φ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 / 2; 0, 0]
    let C : Matrix (Fin 2) (Fin 2) ℝ := !![5 / 4, 0; 0, 1]
    var_lyapMap Φ 1 C = C ∧ (Φ * C)ᵀ ≠ Φ * C := by
  intro Φ C
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Φ, C, var_lyapMap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
        dotProduct, Matrix.one_apply]
  · intro hs
    have := congrFun (congrFun hs 1) 0
    simp [Φ, C, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- Miao, p. 47 (corrected): for stable `Φ`, a covariance-stationary solution of (2.1)–(2.2) has
mean `0`, `C_z(0) = ∑ⱼΦʲΣΣ'Φ'ʲ` (the unique solution of the Lyapunov equation) and
`C_z(j) = ΦʲC_z(0)`: its stationary first and second moments are uniquely determined. -/
theorem var_stationary_moments (h : var_Model n μ ℱ Φ Sg z ε)
    (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom)) (hs : var_IsCovStationary μ z) :
    ∃ Γ : ℕ → Matrix n n ℝ, (∀ t, var_mean μ (z t) = 0) ∧
      (∀ t j, var_mom μ (z (t + j)) (z t) = Γ j) ∧
      Γ 0 = var_lyapSol Φ (Sg * Sgᵀ) ∧ ∀ j, Γ j = Φ ^ j * var_lyapSol Φ (Sg * Sgᵀ) := by
  obtain ⟨-, m, Γ, hm, hΓ⟩ := hs
  have hm0 : m = 0 := by
    have hfix : ∀ t, m = (Φ ^ t) *ᵥ m := fun t => by
      have := var_mean_eq h t
      rw [hm t, hm 0] at this
      exact this
    have hlim := tendsto_of_isStableMatrix Φ hΦ m
    simp only [← hfix] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  subst hm0
  have hΓ' : ∀ t j, var_mom μ (z (t + j)) (z t) = Γ j := fun t j => by
    have := hΓ t j
    simpa only [sub_zero] using this
  have e1 : var_mom μ (z 1) (z 1) = Γ 0 := by simpa using hΓ' 1 0
  have e0 : var_mom μ (z 0) (z 0) = Γ 0 := by simpa using hΓ' 0 0
  have hC : var_lyapMap Φ (Sg * Sgᵀ) (Γ 0) = Γ 0 := by
    rw [← e0, ← var_mom_rec h 0]
    simpa using e1.trans e0.symm
  have h0 := lyap_unique Φ hΦ _ _ hC
  refine ⟨Γ, hm, hΓ', h0, fun j => ?_⟩
  rw [← hΓ' 0 j, var_autocov h 0 j, ← h0, e0]

/-- Miao, p. 47, existence: "assume `z₀` is drawn from the stationary distribution": if `Ez₀ = 0`
and `Ez₀z'₀ = ∑ⱼΦʲΣΣ'Φ'ʲ`, then `z` is covariance stationary with `C_z(j) = ΦʲC_z(0)`. -/
theorem var_stationary_of_initial (h : var_Model n μ ℱ Φ Sg z ε)
    (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom)) (h0 : var_mean μ (z 0) = 0)
    (hC : var_mom μ (z 0) (z 0) = var_lyapSol Φ (Sg * Sgᵀ)) :
    var_IsCovStationary μ z ∧ ∀ t j,
      var_mom μ (z (t + j)) (z t) = Φ ^ j * var_lyapSol Φ (Sg * Sgᵀ) := by
  have hS : ∀ t, var_mom μ (z t) (z t) = var_lyapSol Φ (Sg * Sgᵀ) := fun t => by
    rw [var_mom_iterate h, hC]
    exact Function.iterate_fixed (lyap_fixed Φ hΦ _) t
  have hauto : ∀ t j, var_mom μ (z (t + j)) (z t) = Φ ^ j * var_lyapSol Φ (Sg * Sgᵀ) :=
    fun t j => by rw [var_autocov h, hS]
  refine ⟨⟨h.z_memLp, 0, fun j => Φ ^ j * var_lyapSol Φ (Sg * Sgᵀ),
    (var_mean_tendsto_zero h hΦ).2 h0, fun t j => ?_⟩, hauto⟩
  simpa only [sub_zero] using hauto t j

/-! ### Impulse responses -/

omit [DecidableEq k] in
/-- Miao, p. 47: `z_{t+j} = Φʲz_t + Σε_{t+j} + ΦΣε_{t+j−1} + ⋯ + Φ^{j−1}Σε_{t+1}`. -/
theorem var_ma_shift {x : ℕ → n → ℝ} {e : ℕ → k → ℝ}
    (hrec : ∀ t, x (t + 1) = Φ *ᵥ x t + Sg *ᵥ e (t + 1)) (t j : ℕ) :
    x (t + j) = (Φ ^ j) *ᵥ x t + ∑ i ∈ Finset.range j, (Φ ^ i * Sg) *ᵥ e (t + j - i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← Nat.add_assoc, hrec, ih, Finset.sum_range_succ', Matrix.mulVec_add,
      Matrix.mulVec_mulVec, ← pow_succ', Matrix.mulVec_sum]
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ', pow_zero, Matrix.one_mul]
    rw [Nat.sub_zero]
    have : ∀ i ∈ Finset.range j, (Φ ^ (i + 1) * Sg) *ᵥ e (t + j + 1 - (i + 1)) =
        (Φ ^ (i + 1) * Sg) *ᵥ e (t + j - i) := fun i _ => by
      rw [show t + j + 1 - (i + 1) = t + j - i by omega]
    rw [Finset.sum_congr rfl this]
    abel

omit [DecidableEq k] in
/-- Miao, p. 48: the finite-horizon moving-average representation
`z_{t+1} = Φ^{t+1}z₀ + ∑_{j≤t}ΦʲΣε_{t+1−j}`. -/
theorem var_ma {x : ℕ → n → ℝ} {e : ℕ → k → ℝ}
    (hrec : ∀ t, x (t + 1) = Φ *ᵥ x t + Sg *ᵥ e (t + 1)) (t : ℕ) :
    x (t + 1) = (Φ ^ (t + 1)) *ᵥ x 0 + ∑ j ∈ Finset.range (t + 1), (Φ ^ j * Sg) *ᵥ e (t + 1 - j)
    := by
  simpa using var_ma_shift hrec 0 (t + 1)

omit [DecidableEq k] in
/-- Miao, p. 48: for stable `Φ` the initial condition washes out, `Φ^{t+1}z₀ → 0`, so `z_{t+1}`
is asymptotically `∑ⱼΦʲΣε_{t+1−j}`. -/
theorem var_ma_initial_tendsto (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom)) (x0 : n → ℝ) :
    Tendsto (fun t => (Φ ^ (t + 1)) *ᵥ x0) atTop (𝓝 0) :=
  (tendsto_add_atTop_iff_nat 1).2 (tendsto_of_isStableMatrix Φ hΦ x0)

omit [DecidableEq k] in
/-- Miao, p. 48, the impulse response: if `ε'` differs from `ε` only by a shock `v` at date
`s + 1`, and `z, z'` solve (2.1) from the same `z₀`, then `z'_{s+1+j} − z_{s+1+j} = ΦʲΣv`; and
`z' = z` before date `s + 1`. -/
theorem var_impulse_response {x x' : ℕ → n → ℝ} {e e' : ℕ → k → ℝ}
    (hrec : ∀ t, x (t + 1) = Φ *ᵥ x t + Sg *ᵥ e (t + 1))
    (hrec' : ∀ t, x' (t + 1) = Φ *ᵥ x' t + Sg *ᵥ e' (t + 1)) (h0 : x' 0 = x 0) (s : ℕ)
    (v : k → ℝ) (he : ∀ t, e' t = if t = s + 1 then e t + v else e t) :
    (∀ t ≤ s, x' t = x t) ∧ ∀ j, x' (s + 1 + j) - x (s + 1 + j) = (Φ ^ j * Sg) *ᵥ v := by
  have hbefore : ∀ t ≤ s, x' t = x t := by
    intro t ht
    induction t with
    | zero => exact h0
    | succ t ih =>
      rw [hrec, hrec', ih (by omega), he]
      simp only [show t + 1 ≠ s + 1 by omega, ↓reduceIte]
  refine ⟨hbefore, fun j => ?_⟩
  induction j with
  | zero =>
    rw [add_zero, hrec, hrec', hbefore s le_rfl, he]
    simp [Matrix.mulVec_add]
  | succ j ih =>
    rw [← Nat.add_assoc, hrec, hrec', he]
    simp only [show s + 1 + j + 1 ≠ s + 1 by omega, ↓reduceIte]
    rw [show Φ *ᵥ x' (s + 1 + j) + Sg *ᵥ e (s + 1 + j + 1) -
        (Φ *ᵥ x (s + 1 + j) + Sg *ᵥ e (s + 1 + j + 1)) =
        Φ *ᵥ (x' (s + 1 + j) - x (s + 1 + j)) by rw [Matrix.mulVec_sub]; abel, ih,
      Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']

/-! ### White noise (Definition 2.3.3, p. 56) -/

/-- **Definition 2.3.3** (Miao, p. 56): `X` is a white noise with variance `Σ_w`: square
integrable, `EX_t = 0`, `EX_tX'_s = 0` for `s ≠ t` and `= Σ_w` for `s = t`. -/
def var_IsWhiteNoise (μ : Measure Ω) (X : ℕ → Ω → k → ℝ) (Sw : Matrix k k ℝ) : Prop :=
  (∀ t i, MemLp (fun ω => X t ω i) 2 μ) ∧ (∀ t i, ∫ ω, X t ω i ∂μ = 0) ∧
    ∀ t s, var_mom μ (X t) (X s) = if t = s then Sw else 0

omit [Fintype k] [DecidableEq k] in
/-- `E|X| ≤ (EX²)^{1/2}` on a probability space. -/
theorem var_integral_abs_le_sqrt {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    ∫ ω, |X ω| ∂μ ≤ Real.sqrt (∫ ω, X ω * X ω ∂μ) := by
  have habs : MemLp (fun ω => |X ω|) 2 μ := hX.abs
  have hv := ProbabilityTheory.variance_nonneg (fun ω => |X ω|) μ
  rw [ProbabilityTheory.variance_eq_sub habs] at hv
  have hsq : ∫ ω, ((fun ω => |X ω|) ^ 2) ω ∂μ = ∫ ω, X ω * X ω ∂μ := by
    congr 1
    funext ω
    simp [sq]
  rw [hsq] at hv
  exact Real.le_sqrt_of_sq_le (by linarith)

omit [Fintype k] [DecidableEq k] in
/-- Miao, p. 56: "a white noise process is stable" (Definition 2.3.1): `E|X_{t,i}| ≤ (Σ_w)ᵢᵢ^{1/2}`,
so `max_i E|X_{t,i}| < M` for all `t`. -/
theorem whiteNoise_stable [Finite k] {X : ℕ → Ω → k → ℝ} {Sw : Matrix k k ℝ}
    (hX : var_IsWhiteNoise μ X Sw) :
    ∃ M, 0 < M ∧ ∀ t i, ∫ ω, |X t ω i| ∂μ < M := by
  cases nonempty_fintype k
  refine ⟨∑ i, Real.sqrt (Sw i i) + 1, by positivity, fun t i => ?_⟩
  have hd : ∫ ω, X t ω i * X t ω i ∂μ = Sw i i := by
    have := congrFun (congrFun (hX.2.2 t t) i) i
    simpa [var_mom] using this
  have h1 := var_integral_abs_le_sqrt (hX.1 t i)
  rw [hd] at h1
  have h2 : Real.sqrt (Sw i i) ≤ ∑ j, Real.sqrt (Sw j j) :=
    Finset.single_le_sum (f := fun j => Real.sqrt (Sw j j)) (fun j _ => Real.sqrt_nonneg _)
      (Finset.mem_univ i)
  linarith

omit [Fintype k] [DecidableEq k] in
/-- Miao, p. 56, in the `L¹` setting: the classes of a white noise form a stable process
(`IsStableProc`, Definition 2.3.1). -/
theorem whiteNoise_stable_L1 [Finite k] {X : ℕ → Ω → k → ℝ} {Sw : Matrix k k ℝ}
    (hX : var_IsWhiteNoise μ X Sw) :
    IsStableProc fun t i => ((hX.1 t i).integrable one_le_two).toL1 (fun ω => X t ω i) := by
  obtain ⟨M, hM, hb⟩ := whiteNoise_stable hX
  refine ⟨M, hM, fun t i => ?_⟩
  rw [l1_norm_eq_integral_abs]
  refine lt_of_eq_of_lt (integral_congr_ae ?_) (hb t i)
  filter_upwards [Integrable.coeFn_toL1 ((hX.1 t i).integrable one_le_two)] with ω hω
  rw [hω]

omit [Fintype k] in
/-- Miao, p. 56: "the process `{ε_{t+1}}` satisfying (2.2) is a white noise" (with `Σ = I`):
`Eε_{t+1} = 0`, `Eε_{t+1}ε'_{s+1} = 0` for `s ≠ t` (tower property), `Eε_{t+1}ε'_{t+1} = I`. -/
theorem mds_whiteNoise {ε : ℕ → Ω → k → ℝ} (hε : var_ShockMDS μ ℱ ε) :
    var_IsWhiteNoise μ (fun t => ε (t + 1)) 1 := by
  refine ⟨fun t i => hε.memLp (t + 1) i, fun t i => var_mean_eps_zero hε t i, fun t s => ?_⟩
  ext i j
  simp only [var_mom, Matrix.of_apply]
  rcases lt_trichotomy t s with hts | hts | hts
  · have hm : Measurable[ℱ s] fun ω => ε (t + 1) ω i :=
      (hε.meas (t + 1) i).mono (ℱ.mono (by omega)) le_rfl
    rw [var_cross_zero hε hm (hε.memLp (t + 1) i) j]
    simp [hts.ne]
  · subst hts
    rw [var_mom_eps hε t i j]
    simp [Matrix.one_apply]
  · have hm : Measurable[ℱ t] fun ω => ε (s + 1) ω j :=
      (hε.meas (s + 1) j).mono (ℱ.mono (by omega)) le_rfl
    rw [show (fun ω => ε (t + 1) ω i * ε (s + 1) ω j) =
      fun ω => ε (s + 1) ω j * ε (t + 1) ω i by funext ω; ring,
      var_cross_zero hε hm (hε.memLp (s + 1) j) i]
    simp [hts.ne']

end Miao.LinearQuadratic

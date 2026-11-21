/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.GMBasic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The long-run covariance matrix and HAC estimators (Miao, §12.1, pp. 391–395)

Miao, pp. 391–395.

* `gm_integral_mul_shift`: for a stationary process,
  `E[φ(x_{s+n}) ψ(x_s)] = E[φ(x_n) ψ(x₀)]` ("the stationarity assumption implies that
  `E(h_t − Eh_t)(h_{t−j} − Eh_{t−j})' = Γ_j` for all `t`", p. 392).
* `gm_toeplitz_sum`, `gm_toeplitz_sum_Ico`: the double sum `Σ_{t,s<T} c_{t,s}` of a Toeplitz
  array (`c_{t,s} = a_{t−s}` for `s ≤ t`, `b_{s−t}` for `t < s`) equals
  `T a₀ + Σ_{j=1}^{T−1} (T − j)(a_j + b_j)`.
* `gm_longRunVar` (p. 392): `Var(√T g_T(θ₀))_{il} = Γ₀ + Σ_{j=1}^{T−1} ((T − j)/T)(Γ_j + Γ_j')`
  (entry `(i, l)`), for a stationary process with square-integrable (centred) moments.
* `gm_longRunVar_limit` (p. 392): if `Σ_j |Γ_j| < ∞` the limit is `S = Γ₀ + Σ_{i≥1}(Γ_i + Γ_i')`.
  The book writes the limit without a summability condition; absolute summability of the
  autocovariances is the standard sufficient condition and is made explicit.
* Table 12.1: the Bartlett, Parzen and quadratic spectral kernels (`gm_bartlett`, `gm_parzen`,
  `gm_qs`), with `ω(0) = 1`, values in `[0, 1]` and continuity of the first two; the sample
  autocovariances `Γ̂_j` and the HAC estimator `Ŝ_HAC = Γ̂₀ + Σ_i ω_{i,T}(Γ̂_i + Γ̂_i')`, which is
  symmetric (`gm_hac_isSymm`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- For a stationary process every `x_t` has the law of `x₀`. -/
theorem gm_map_eq {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    (hst : IsStationary P X) (t : ℕ) : P.map (X t) = P.map (X 0) := by
  have hc : ∀ s, X s = (fun y : Fin 1 → E => y 0) ∘ window X s 0 := fun s => by
    funext ω
    simp [window]
  rw [hc t, hc 0, ← Measure.map_map (measurable_pi_apply 0) (measurable_window hX t 0),
    ← Measure.map_map (measurable_pi_apply 0) (measurable_window hX 0 0), hst t 0]

/-- Miao, p. 392: for a stationary process `E[φ(x_{s+n}) ψ(x_s)] = E[φ(x_n) ψ(x₀)]`. -/
theorem gm_integral_mul_shift {P : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    (hst : IsStationary P X) {φ ψ : E → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) (s n : ℕ) :
    ∫ ω, φ (X (s + n) ω) * ψ (X s ω) ∂P = ∫ ω, φ (X n ω) * ψ (X 0 ω) ∂P := by
  set F : (Fin (n + 1) → E) → ℝ := fun y => φ (y (Fin.last n)) * ψ (y 0)
  have hF : Measurable F :=
    (hφ.comp (measurable_pi_apply _)).mul (hψ.comp (measurable_pi_apply _))
  have e : ∀ s', ∫ ω, φ (X (s' + n) ω) * ψ (X s' ω) ∂P =
      ∫ y, F y ∂(P.map (window X s' n)) := by
    intro s'
    rw [integral_map (measurable_window hX s' n).aemeasurable hF.aestronglyMeasurable]
    simp [F, window]
  have e0 := e 0
  simp only [zero_add] at e0
  rw [e s, e0, hst s n]

/-- Reflection: `Σ_{t<T} f(T − t) = Σ_{j<T} f(j + 1)`. -/
theorem gm_sum_range_reflect_sub (f : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, f (T - t) = ∑ j ∈ Finset.range T, f (j + 1) := by
  rw [← Finset.sum_range_reflect (fun j => f (j + 1)) T]
  exact Finset.sum_congr rfl fun t ht => by
    have := Finset.mem_range.1 ht
    congr 1
    omega

/-- The double sum of a Toeplitz array, range form:
`Σ_{t,s<T} c_{t,s} = Σ_{j<T} (T − j)(a_j + b_j) − T b₀`. -/
theorem gm_toeplitz_sum (a b : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, (if s ≤ t then a (t - s) else b (s - t)) =
      ∑ j ∈ Finset.range T, ((T : ℝ) - j) * (a j + b j) - T * b 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_congr rfl fun t ht => Finset.sum_range_succ _ T]
    rw [Finset.sum_add_distrib, ih]
    have h1 : ∑ t ∈ Finset.range T, (if T ≤ t then a (t - T) else b (T - t)) =
        ∑ t ∈ Finset.range T, b (T - t) := Finset.sum_congr rfl fun t ht => by
      have := Finset.mem_range.1 ht
      simp only [show ¬ T ≤ t by omega, ↓reduceIte]
    have h2 : ∑ s ∈ Finset.range (T + 1), (if s ≤ T then a (T - s) else b (s - T)) =
        ∑ s ∈ Finset.range T, a (T - s) + a 0 := by
      rw [Finset.sum_range_succ]
      simp only [le_refl, ↓reduceIte, Nat.sub_self]
      congr 1
      exact Finset.sum_congr rfl fun s hs => by
        have := Finset.mem_range.1 hs
        simp only [show s ≤ T by omega, ↓reduceIte]
    rw [h1, h2, gm_sum_range_reflect_sub, gm_sum_range_reflect_sub]
    have ha : ∑ j ∈ Finset.range (T + 1), a j = ∑ j ∈ Finset.range T, a (j + 1) + a 0 :=
      Finset.sum_range_succ' _ _
    have hb : ∑ j ∈ Finset.range (T + 1), b j = ∑ j ∈ Finset.range T, b (j + 1) + b 0 :=
      Finset.sum_range_succ' _ _
    have hw : ∑ j ∈ Finset.range (T + 1), (((T + 1 : ℕ) : ℝ) - j) * (a j + b j) =
        ∑ j ∈ Finset.range T, ((T : ℝ) - j) * (a j + b j) +
          ∑ j ∈ Finset.range (T + 1), (a j + b j) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => a j + b j)]
      push_cast
      have : ∑ j ∈ Finset.range T, (((T : ℝ) + 1) - j) * (a j + b j) =
          ∑ j ∈ Finset.range T, ((T : ℝ) - j) * (a j + b j) +
            ∑ j ∈ Finset.range T, (a j + b j) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      ring
    rw [hw, Finset.sum_add_distrib, ha, hb]
    push_cast
    ring

/-- The double sum of a Toeplitz array (Miao, p. 392):
`Σ_{t,s<T} c_{t,s} = T a₀ + Σ_{j=1}^{T−1} (T − j)(a_j + b_j)`. -/
theorem gm_toeplitz_sum_Ico (a b : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, (if s ≤ t then a (t - s) else b (s - t)) =
      T * a 0 + ∑ j ∈ Finset.Ico 1 T, ((T : ℝ) - j) * (a j + b j) := by
  rw [gm_toeplitz_sum]
  rcases Nat.eq_zero_or_pos T with h | h
  · subst h
    simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot h]
    push_cast
    ring

/-- `Γ_j` entry `(i, l)`: `E[u_i(x_j) u_l(x₀)]` (the autocovariance when `u` is centred). -/
noncomputable def gm_autocov {q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E) (u : E → Fin q → ℝ)
    (j : ℕ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun i l => ∫ ω, u (X j ω) i * u (X 0 ω) l ∂P

/-- Miao, p. 392 (the long-run variance): for a stationary process and square-integrable `u`
(e.g. `u = h(·, θ₀) − E h`), for `T ≥ 1`,
`E[(T^{−1/2} Σ_t u_i(x_t))(T^{−1/2} Σ_s u_l(x_s))]
  = Γ₀(i,l) + Σ_{j=1}^{T−1} ((T − j)/T)(Γ_j(i,l) + Γ_j'(i,l))`. -/
theorem gm_longRunVar {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hst : IsStationary P X) {q : ℕ} {u : E → Fin q → ℝ}
    (hu : Measurable u) (hL2 : ∀ i, MemLp (fun ω => u (X 0 ω) i) 2 P) (i l : Fin q) {T : ℕ}
    (hT : 0 < T) :
    ∫ ω, ((Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, u (X t ω) i) *
        ((Real.sqrt T)⁻¹ * ∑ s ∈ Finset.range T, u (X s ω) l) ∂P =
      gm_autocov P X u 0 i l + ∑ j ∈ Finset.Ico 1 T,
        (((T : ℝ) - j) / T) * (gm_autocov P X u j i l + (gm_autocov P X u j).transpose i l) := by
  have hui : ∀ i, Measurable fun x => u x i := fun i => measurable_pi_iff.1 hu i
  have hL2t : ∀ t i, MemLp (fun ω => u (X t ω) i) 2 P := by
    intro t i
    have h0 := (memLp_map_measure_iff (hui i).aestronglyMeasurable (hX 0).aemeasurable).2
      (hL2 i)
    rw [← gm_map_eq hX hst t] at h0
    exact (memLp_map_measure_iff (hui i).aestronglyMeasurable (hX t).aemeasurable).1 h0
  have hint : ∀ t s, Integrable (fun ω => u (X t ω) i * u (X s ω) l) P := fun t s =>
    (hL2t t i).integrable_mul (hL2t s l)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hsq : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ = (T : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hTpos.le]
  have hexp : (fun ω => ((Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, u (X t ω) i) *
      ((Real.sqrt T)⁻¹ * ∑ s ∈ Finset.range T, u (X s ω) l)) = fun ω =>
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, u (X t ω) i * u (X s ω) l := by
    funext ω
    rw [← hsq, mul_mul_mul_comm, Finset.sum_mul_sum]
  have hcell : ∀ t s, ∫ ω, u (X t ω) i * u (X s ω) l ∂P =
      if s ≤ t then gm_autocov P X u (t - s) i l
      else (gm_autocov P X u (s - t)).transpose i l := by
    intro t s
    split_ifs with hst'
    · have := gm_integral_mul_shift hX hst (hui i) (hui l) s (t - s)
      rw [Nat.add_sub_cancel' hst'] at this
      rw [this]
      rfl
    · have := gm_integral_mul_shift hX hst (hui l) (hui i) t (s - t)
      rw [Nat.add_sub_cancel' (by omega)] at this
      simp only [Matrix.transpose_apply, gm_autocov, Matrix.of_apply]
      rw [← this]
      exact integral_congr_ae (ae_of_all _ fun ω => mul_comm _ _)
  rw [hexp, integral_const_mul, integral_finsetSum _ fun t _ =>
    integrable_finsetSum _ fun s _ => hint t s]
  simp_rw [integral_finsetSum _ fun s _ => hint _ s, hcell]
  rw [gm_toeplitz_sum_Ico (fun j => gm_autocov P X u j i l)
    (fun j => (gm_autocov P X u j).transpose i l), mul_add, Finset.mul_sum]
  congr 1
  · field_simp
  · exact Finset.sum_congr rfl fun j _ => by field_simp

/-- Miao, p. 392: if the autocovariances are absolutely summable, the long-run variance
`Γ₀ + Σ_{j=1}^{T−1} ((T − j)/T)(Γ_j + Γ_j')` converges to `S = Γ₀ + Σ_{i≥1}(Γ_i + Γ_i')`
(entrywise; `a_j = Γ_j(i,l)`, `b_j = Γ_j'(i,l)`). -/
theorem gm_longRunVar_limit {a b : ℕ → ℝ} (ha : Summable fun j => |a j|)
    (hb : Summable fun j => |b j|) :
    Tendsto (fun T : ℕ => a 0 + ∑ j ∈ Finset.Ico 1 T, (((T : ℝ) - j) / T) * (a j + b j)) atTop
      (𝓝 (a 0 + ∑' j, (a (j + 1) + b (j + 1)))) := by
  refine tendsto_const_nhds.add ?_
  set F : ℕ → ℕ → ℝ := fun T j =>
    if j + 1 < T then (((T : ℝ) - (j + 1 : ℕ)) / T) * (a (j + 1) + b (j + 1)) else 0 with hF
  have hsum : ∀ T : ℕ, ∑ j ∈ Finset.Ico 1 T, (((T : ℝ) - j) / T) * (a j + b j) =
      ∑' j, F T j := by
    intro T
    rw [tsum_eq_sum (s := Finset.range (T - 1)) fun j hj => ?_, Finset.sum_Ico_eq_sum_range]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have := Finset.mem_range.1 hj
      simp only [hF, show j + 1 < T by omega, ↓reduceIte, add_comm 1 j]
    · have := Finset.mem_range.not.1 hj
      simp only [hF, show ¬ j + 1 < T by omega, ↓reduceIte]
  simp_rw [hsum]
  have hbound : Summable fun j => |a (j + 1)| + |b (j + 1)| :=
    ((summable_nat_add_iff 1).2 ha).add ((summable_nat_add_iff 1).2 hb)
  refine tendsto_tsum_of_dominated_convergence hbound (fun j => ?_) ?_
  · have hw : Tendsto (fun T : ℕ => (1 - ((j + 1 : ℕ) : ℝ) / T) * (a (j + 1) + b (j + 1)))
        atTop (𝓝 ((1 - 0) * (a (j + 1) + b (j + 1)))) :=
      (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)).mul tendsto_const_nhds
    rw [sub_zero, one_mul] at hw
    refine hw.congr' ?_
    filter_upwards [eventually_gt_atTop (j + 1)] with T hT
    have hT0 : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp only [hF, hT, ↓reduceIte]
    field_simp
  · refine Eventually.of_forall fun T j => ?_
    simp only [hF]
    split_ifs with hj
    · have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
      have hjT : ((j + 1 : ℕ) : ℝ) < T := by exact_mod_cast hj
      have hw0 : 0 ≤ ((T : ℝ) - (j + 1 : ℕ)) / T := div_nonneg (by linarith) hT.le
      have hw1 : ((T : ℝ) - (j + 1 : ℕ)) / T ≤ 1 := by
        rw [div_le_one hT]
        have : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
      calc ((T : ℝ) - (j + 1 : ℕ)) / T * |a (j + 1) + b (j + 1)|
          ≤ 1 * |a (j + 1) + b (j + 1)| := mul_le_mul_of_nonneg_right hw1 (abs_nonneg _)
        _ ≤ |a (j + 1)| + |b (j + 1)| := by rw [one_mul]; exact abs_add_le _ _
    · simp only [norm_zero]
      positivity

/-! ### Table 12.1: HAC kernels and the HAC estimator -/

/-- Table 12.1 (Newey and West 1987): the Bartlett kernel, `1 − a` for `a ≤ 1`, `0` for
`a > 1` (with `a_i = i/(b_T + 1)`). -/
noncomputable def gm_bartlett (a : ℝ) : ℝ := if a ≤ 1 then 1 - a else 0

/-- Table 12.1 (Gallant 1987): the Parzen kernel. -/
noncomputable def gm_parzen (a : ℝ) : ℝ :=
  if a ≤ 1 / 2 then 1 - 6 * a ^ 2 + 6 * a ^ 3 else if a ≤ 1 then 2 * (1 - a) ^ 3 else 0

/-- Table 12.1 (Andrews 1991): the quadratic spectral kernel, with `d_i = i/b_T` and
`m_i = 6πd_i/5`. -/
noncomputable def gm_qs (d : ℝ) : ℝ :=
  25 / (12 * Real.pi ^ 2 * d ^ 2) *
    (Real.sin (6 * Real.pi * d / 5) / (6 * Real.pi * d / 5) - Real.cos (6 * Real.pi * d / 5))

/-- Table 12.1: the argument `a_i = i/(b_T + 1)` of the Bartlett and Parzen kernels. -/
noncomputable def gm_kernelArg (i : ℕ) (bT : ℝ) : ℝ := i / (bT + 1)

theorem gm_bartlett_zero : gm_bartlett 0 = 1 := by simp [gm_bartlett]

theorem gm_parzen_zero : gm_parzen 0 = 1 := by norm_num [gm_parzen]

/-- The Bartlett kernel takes values in `[0, 1]` for `a ≥ 0`. -/
theorem gm_bartlett_mem_Icc {a : ℝ} (ha : 0 ≤ a) : gm_bartlett a ∈ Set.Icc (0 : ℝ) 1 := by
  unfold gm_bartlett
  split_ifs with h
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- The Parzen kernel takes values in `[0, 1]` for `a ≥ 0`. -/
theorem gm_parzen_mem_Icc {a : ℝ} (ha : 0 ≤ a) : gm_parzen a ∈ Set.Icc (0 : ℝ) 1 := by
  unfold gm_parzen
  split_ifs with h1 h2
  · constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 h1) (mul_nonneg ha ha), mul_nonneg ha ha,
        mul_nonneg (sub_nonneg.2 h1) ha]
    · have h1' : a ≤ 1 := h1.trans (by norm_num)
      nlinarith [mul_nonneg (mul_nonneg ha ha) (sub_nonneg.2 h1')]
  · have h0 : 0 ≤ 1 - a := by linarith
    have h3 : 1 - a ≤ 1 / 2 := by linarith
    constructor
    · positivity
    · nlinarith [pow_le_pow_left₀ h0 h3 3]
  · exact ⟨le_rfl, zero_le_one⟩

/-- The Bartlett kernel is continuous. -/
theorem gm_continuous_bartlett : Continuous gm_bartlett :=
  Continuous.if_le (continuous_const.sub continuous_id) continuous_const continuous_id
    continuous_const fun x hx => by rw [hx, sub_self]

/-- The Parzen kernel is continuous (its pieces agree at `a = 1/2` and `a = 1`). -/
theorem gm_continuous_parzen : Continuous gm_parzen := by
  refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const fun x hx => ?_
  · exact Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
      fun x hx => by rw [hx]; norm_num
  · rw [hx]
    norm_num

/-- Miao, p. 393: the sample autocovariance `Γ̂_j = T⁻¹ Σ_{t=j+1}^{T} h_t h_{t−j}'` (indices
shifted to `t = j, …, T − 1`). -/
noncomputable def gm_sampleAutocov {q : ℕ} (hs : ℕ → Fin q → ℝ) (T j : ℕ) :
    Matrix (Fin q) (Fin q) ℝ :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.Ico j T, Matrix.vecMulVec (hs t) (hs (t - j))

/-- Miao, p. 392: the HAC estimator `Ŝ_HAC = Γ̂₀ + Σ_{i=1}^{T−1} ω_{i,T}(Γ̂_i + Γ̂_i')`. -/
noncomputable def gm_hac {q : ℕ} (w : ℕ → ℝ) (hs : ℕ → Fin q → ℝ) (T : ℕ) :
    Matrix (Fin q) (Fin q) ℝ :=
  gm_sampleAutocov hs T 0 +
    ∑ i ∈ Finset.Ico 1 T, w i • (gm_sampleAutocov hs T i + (gm_sampleAutocov hs T i).transpose)

/-- The HAC estimator is symmetric for any kernel weights. -/
theorem gm_hac_isSymm {q : ℕ} (w : ℕ → ℝ) (hs : ℕ → Fin q → ℝ) (T : ℕ) :
    (gm_hac w hs T).IsSymm := by
  unfold Matrix.IsSymm gm_hac
  rw [Matrix.transpose_add, Matrix.transpose_sum]
  congr 1
  · simp only [gm_sampleAutocov, Matrix.transpose_smul, Matrix.transpose_sum,
      Matrix.transpose_vecMulVec, Nat.sub_zero]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

end Miao.StructuralEstimation

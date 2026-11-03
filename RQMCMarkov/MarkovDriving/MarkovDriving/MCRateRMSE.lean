/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.MCRateDriven

/-! # The root-mean-square rate of plain MC (post #3)

Post #3: "With MC of a Markov Chain the empirical transition matrix converges at `O(1/√T)`
(Meyn & Tweedie, Chpt 17)." `MCRate` and `MCRateDriven` show that **almost surely** this is
false: the error of `N_ij(T) − p_ij N_i(T)` is of exact order `√(T log log T)` (LIL), so the
empirical transition matrix converges at `√(log log T / T)`, not `O(1/√T)`
(`ae_frequently_transCount_driven_ge`, `ae_not_tendsto_transCount_driven`). This module proves
that the post's `O(1/√T)` is **right at the root-mean-square (RMSE) scale**, for the post's MC
construction: one i.i.d. uniform sequence `u ∼ iidUniform ℕ` driving `drivenPath P x₀ u`, any
stochastic `P`, any start `x₀`, every horizon `T`.

**Method.** `N_ij(T) − p_ij N_i(T) = Σ_{t<T} 1{x_t = i}(1{x_{t+1} = j} − p_ij)` is a sum of
martingale increments for the time filtration: the input `u T` is independent of the past
`(u 0, …, u (T−1))` (`indepFun_past_iidUniform`), which determines `x_0, …, x_T`
(`drivenPath_padPast`), and `x_{T+1} = step P x_T (u T)`. Hence
`E[G(x) F(x_T, x_{T+1})] = E[G(x) Σ_j p_{x_T j} F(x_T, j)]` for every bounded functional `G` of
`x_0, …, x_T` (`integral_mul_step_driven`): the increments are orthogonal, with conditional
variance `Σ_j p_{x_t j} f(x_t, j)²` (`integral_sq_incrementSum_driven`).

## Main results

* `integral_sq_transCount_sub_driven` (**exact**): `E[(N_ij(T) − p_ij N_i(T))²] =
  p_ij (1 − p_ij) E N_i(T)`; `integral_sq_transCount_sub_driven_le`: `≤ p_ij (1 − p_ij) T`;
  `integral_sq_transFreq_sub_driven_le`: `E[((N_ij − p_ij N_i)/T)²] ≤ p_ij (1 − p_ij)/T`.
* `integral_sq_departureDiscrepancy_driven`: `E[D_i(g, T)²] = σ_i²(g) E N_i(T)` and
  `integral_sq_sum_departureDiscrepancy_driven`: `E[(Σ_i D_i(g, T))²] = Σ_i σ_i²(g) E N_i(T)`,
  with `σ_i²(g) = rowVariance P g i` (`D_i` is `departureDiscrepancy`).
* Occupation error, with Poisson's `h − Ph = 1_{s} − c`, `|h| ≤ M` (as in
  `abs_occCount_sub_le`): `integral_sq_occCount_sub_driven_mem` (two-sided bounds through
  `V(T) = Σ_i σ_i²(h) E N_i(T)`), `integral_sq_occCount_sub_driven_le`:
  `E[(N_s(T) − T c)²] ≤ (2M + √(T Σ_i σ_i²(h)))²`, and `integral_sq_occFreq_sub_driven_le`:
  the RMSE of the frequency `N_s(T)/T` is `O(1/√T)`.
* `tendsto_integral_occCount_div_driven`: `E N_s(T)/T → c` (a consequence of the RMSE bound;
  no almost-sure law or dominated convergence is needed).
* **Lower bound** `eventually_integral_sq_occCount_sub_driven_ge`: if `E N_i(T)/T → w_i` and
  `Σ_i w_i σ_i²(h) > 0`, then `E[(N_s(T) − T c)²] ≥ κ T` eventually, for some `κ > 0`;
  `eventually_integral_sq_occCount_sub_driven_ge_of_irreducible`: the same for irreducible `P`
  with stationary `π`, under `Σ_i π_i σ_i²(h) > 0`. So the RMSE of the frequency is of exact
  order `1/√T`.
* `occCount_mse_twoStateStay78`: for the two-state chain with stay probability `7/8`
  (`twoStateStay78`), `h = (2, −2)`, `σ_0² = σ_1² = 7/4` (`rowVariance_twoStateStay78`), so
  `Σ_i π_i σ_i²(h) = 7/4 > 0`: both bounds hold and the lower bound is not vacuous.

**Correction** (post #3, "converges at `O(1/√T)`"). Read almost surely, the claim is false:
`ae_not_tendsto_transCount_driven` (`MCRateDriven`) shows the a.s. error is not
`o(√(N log log N))`. Read in root mean square, it is true and sharp: the RMSE of
`(N_ij(T) − p_ij N_i(T))/T` is `√(p_ij (1 − p_ij) E N_i(T))/T ≤ √(p_ij(1 − p_ij)/T)`
(`integral_sq_transCount_sub_driven`), and the RMSE of `N_s(T)/T` is of exact order `1/√T`
(`integral_sq_occFreq_sub_driven_le`, `eventually_integral_sq_occCount_sub_driven_ge`). The
`√T` scale is the CLT scale (`MCRateCLT`).
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Finset Matrix Topology

variable {n : ℕ}

/-- A measurable function bounded by `C` is integrable for a probability measure. -/
theorem integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {g : Ω → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ ω, |g ω| ≤ C) :
    Integrable g Q :=
  Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]
    exact hC ω)

/-- `|F a b| ≤ Σ_a Σ_b |F a b|`. -/
theorem abs_le_sum_sum_abs (F : Fin n → Fin n → ℝ) (a b : Fin n) :
    |F a b| ≤ ∑ a, ∑ b, |F a b| :=
  (single_le_sum (f := fun b => |F a b|) (fun _ _ => abs_nonneg _) (mem_univ b)).trans
    (single_le_sum (f := fun a => ∑ b, |F a b|) (fun _ _ => sum_nonneg fun _ _ =>
      abs_nonneg _) (mem_univ a))

/-- **The law of one step from a uniform input**: if `W ∼ U[0,1)`, then
`E φ(step P i W) = Σ_j p_ij φ_j`. -/
theorem integral_comp_step_of_map {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {W : Ω → ℝ} (hW : Measurable W) (hlaw : Q.map W = uniformIco)
    {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) (φ : Fin n → ℝ) :
    ∫ ω, φ (step P i (W ω)) ∂Q = ∑ j, P i j * φ j := by
  have hmeas : Measurable fun ω => step P i (W ω) := (measurable_step P i).comp hW
  rw [← integral_map hmeas.aemeasurable (measurable_of_finite φ).aestronglyMeasurable]
  rw [integral_fintype Integrable.of_finite]
  refine sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, measureReal_def, Measure.map_apply hmeas (measurableSet_singleton j)]
  have e : (fun ω => step P i (W ω)) ⁻¹' {j} = W ⁻¹' {u | step P i u = j} := rfl
  have hms : MeasurableSet {u | step P i u = j} :=
    (measurable_step P i) (measurableSet_singleton j)
  rw [e, ← Measure.map_apply hW hms, hlaw, uniformIco_step_eq hP i j,
    ENNReal.toReal_ofReal (hP.nonneg i j), mul_comm]

/-- **One step against an independent past.** If `W ∼ U[0,1)` is independent of `Z`, then for
bounded measurable `A` and any `a`, `F`:
`E[A(Z) F(a(Z), step P (a Z) W)] = E[A(Z) Σ_j p_{a(Z) j} F(a(Z), j)]`. -/
theorem integral_mul_comp_step_of_indepFun {Ω β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] {Q : Measure Ω} [IsProbabilityMeasure Q] {Z : Ω → β} {W : Ω → ℝ}
    (hZ : Measurable Z) (hW : Measurable W) (hind : IndepFun Z W Q)
    (hlaw : Q.map W = uniformIco) {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {A : β → ℝ} (hA : Measurable A) {C : ℝ} (hAC : ∀ b, |A b| ≤ C) {a : β → Fin n}
    (ha : Measurable a) (F : Fin n → Fin n → ℝ) :
    ∫ ω, A (Z ω) * F (a (Z ω)) (step P (a (Z ω)) (W ω)) ∂Q =
      ∫ ω, A (Z ω) * ∑ j, P (a (Z ω)) j * F (a (Z ω)) j ∂Q := by
  set CF := ∑ a, ∑ b, |F a b|
  set φ : Fin n → β → ℝ := fun b z => A z * if a z = b then 1 else 0 with hφ
  have hφm : ∀ b, Measurable (φ b) := fun b =>
    hA.mul (Measurable.ite (ha (measurableSet_singleton b)) measurable_const measurable_const)
  have hφb : ∀ b z, |φ b z| ≤ C := fun b z => by
    simp only [hφ]
    split_ifs
    · rw [mul_one]
      exact hAC z
    · rw [mul_zero, abs_zero]
      exact (abs_nonneg _).trans (hAC z)
  have e1 : ∀ ω, A (Z ω) * F (a (Z ω)) (step P (a (Z ω)) (W ω)) =
      ∑ b, φ b (Z ω) * F b (step P b (W ω)) := fun ω => by
    simp only [hφ, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [mem_univ, ite_true]
  have e2 : ∀ ω, A (Z ω) * ∑ j, P (a (Z ω)) j * F (a (Z ω)) j =
      ∑ b, φ b (Z ω) * ∑ j, P b j * F b j := fun ω => by
    simp only [hφ, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [mem_univ, ite_true]
  have hFm : ∀ b, Measurable fun ω => F b (step P b (W ω)) := fun b =>
    (measurable_of_finite (F b)).comp ((measurable_step P b).comp hW)
  have hint1 : ∀ b ∈ univ, Integrable (fun ω => φ b (Z ω) * F b (step P b (W ω))) Q :=
    fun b _ => integrable_of_abs_le (((hφm b).comp hZ).mul (hFm b)) (C := C * CF)
      fun ω => by
        rw [abs_mul]
        exact mul_le_mul (hφb b _) (abs_le_sum_sum_abs F _ _) (abs_nonneg _)
          ((abs_nonneg _).trans (hφb b (Z ω)))
  have hint2 : ∀ b ∈ univ, Integrable (fun ω => φ b (Z ω) * ∑ j, P b j * F b j) Q :=
    fun b _ => (integrable_of_abs_le ((hφm b).comp hZ) fun ω => hφb b (Z ω)).mul_const _
  rw [integral_congr_ae (Eventually.of_forall e1), integral_congr_ae (Eventually.of_forall e2),
    integral_finsetSum _ hint1, integral_finsetSum _ hint2]
  refine sum_congr rfl fun b _ => ?_
  have hindb : IndepFun (fun ω => φ b (Z ω)) (fun ω => F b (step P b (W ω))) Q :=
    hind.comp (hφm b) ((measurable_of_finite (F b)).comp (measurable_step P b))
  rw [hindb.integral_fun_mul_eq_mul_integral ((hφm b).comp hZ).aestronglyMeasurable
    (hFm b).aestronglyMeasurable, integral_mul_const, integral_comp_step_of_map hW hlaw hP b]

/-! ### The past of the driving sequence -/

/-- The first `T` driving inputs, padded with zeros: `padPast T p s = p s` for `s < T`. -/
noncomputable def padPast (T : ℕ) (p : range T → ℝ) : ℕ → ℝ :=
  fun s => if h : s ∈ range T then p ⟨s, h⟩ else 0

/-- `padPast T` is measurable. -/
theorem measurable_padPast (T : ℕ) : Measurable (padPast T) := by
  refine measurable_pi_iff.2 fun s => ?_
  by_cases h : s ∈ range T
  · simp only [padPast, h, dite_true]
    exact measurable_pi_apply _
  · simp only [padPast, h, dite_false]
    exact measurable_const

/-- **The path up to time `T` depends only on the first `T` inputs.** -/
theorem drivenPath_padPast (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (u : ℕ → ℝ) {T t : ℕ}
    (ht : t ≤ T) :
    drivenPath P x₀ (padPast T fun s : range T => u s) t = drivenPath P x₀ u t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step P (drivenPath P x₀ (padPast T fun s : range T => u s) t)
        (padPast T (fun s : range T => u s) t) = step P (drivenPath P x₀ u t) (u t)
    rw [ih (by omega)]
    have hs : t ∈ range T := mem_range.2 (by omega)
    simp only [padPast, hs, dite_true]

/-- Under `iidUniform ℕ`, the first `T` inputs are independent of the input `u T`. -/
theorem indepFun_past_iidUniform (T : ℕ) :
    IndepFun (fun (u : ℕ → ℝ) (s : range T) => u s) (fun u : ℕ → ℝ => u T)
      (iidUniform ℕ) := by
  have := isProbabilityMeasure_uniformIco
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => uniformIco) (X := fun _ x => x)
    (fun _ => measurable_id)
  have h2 := h.indepFun_finset (range T) {T} (by simp) (fun t => measurable_pi_apply t)
  exact h2.comp measurable_id (measurable_pi_apply (⟨T, mem_singleton_self T⟩ : ({T} : Finset ℕ)))

/-- Each input of `iidUniform ℕ` is uniform on `[0,1)`. -/
theorem map_eval_iidUniform (T : ℕ) :
    (iidUniform ℕ).map (fun u : ℕ → ℝ => u T) = uniformIco := by
  have := isProbabilityMeasure_uniformIco
  exact Measure.infinitePi_map_eval (μ := fun _ : ℕ => uniformIco) T

/-- The state at time `t` is a measurable function of the input sequence. -/
theorem measurable_drivenPath_apply (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (t : ℕ) :
    Measurable fun u => drivenPath P x₀ u t :=
  (measurable_pi_apply t).comp (measurable_drivenPath P x₀)

/-- **The one-step identity for MC driving.** If `G` is a bounded measurable path functional
that depends only on `x_0, …, x_T`, then
`E[G(x) F(x_T, x_{T+1})] = E[G(x) Σ_j p_{x_T j} F(x_T, j)]`. -/
theorem integral_mul_step_driven {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (T : ℕ) {G : (ℕ → Fin n) → ℝ} (hG : Measurable G) {C : ℝ} (hGC : ∀ x, |G x| ≤ C)
    (hGT : ∀ x y : ℕ → Fin n, (∀ t ≤ T, x t = y t) → G x = G y) (F : Fin n → Fin n → ℝ) :
    ∫ u, G (drivenPath P x₀ u) * F (drivenPath P x₀ u T) (drivenPath P x₀ u (T + 1))
        ∂iidUniform ℕ =
      ∫ u, G (drivenPath P x₀ u) *
        ∑ j, P (drivenPath P x₀ u T) j * F (drivenPath P x₀ u T) j ∂iidUniform ℕ := by
  have := isProbabilityMeasure_iidUniform ℕ
  set Z : (ℕ → ℝ) → (range T → ℝ) := fun u s => u s
  have hZ : Measurable Z := measurable_pi_iff.2 fun s => measurable_pi_apply _
  set A : (range T → ℝ) → ℝ := fun p => G (drivenPath P x₀ (padPast T p))
  set a : (range T → ℝ) → Fin n := fun p => drivenPath P x₀ (padPast T p) T
  have hA : Measurable A := hG.comp ((measurable_drivenPath P x₀).comp (measurable_padPast T))
  have ha : Measurable a := (measurable_drivenPath_apply P x₀ T).comp (measurable_padPast T)
  have eA : ∀ u, G (drivenPath P x₀ u) = A (Z u) := fun u =>
    hGT _ _ fun t ht => (drivenPath_padPast P x₀ u ht).symm
  have ea : ∀ u, drivenPath P x₀ u T = a (Z u) := fun u =>
    (drivenPath_padPast P x₀ u le_rfl).symm
  have hkey := integral_mul_comp_step_of_indepFun hZ (measurable_pi_apply T)
    (indepFun_past_iidUniform T) (map_eval_iidUniform T) hP hA (fun p => hGC _) ha F
  have e1 : ∀ u, G (drivenPath P x₀ u) * F (drivenPath P x₀ u T) (drivenPath P x₀ u (T + 1)) =
      A (Z u) * F (a (Z u)) (step P (a (Z u)) (u T)) := fun u => by
    rw [eA, show drivenPath P x₀ u (T + 1) = step P (drivenPath P x₀ u T) (u T) from rfl,
      ← ea]
  have e2 : ∀ u, G (drivenPath P x₀ u) *
      ∑ j, P (drivenPath P x₀ u T) j * F (drivenPath P x₀ u T) j =
      A (Z u) * ∑ j, P (a (Z u)) j * F (a (Z u)) j := fun u => by
    rw [eA, ← ea]
  simp only [e1, e2]
  exact hkey

/-! ### The martingale of increments -/

/-- The **increment sum** `Σ_{t<T} f(x_t, x_{t+1})` along a path. When every row average
`Σ_j p_aj f(a, j)` vanishes, it is a martingale for MC (`integral_sq_incrementSum_driven`). -/
noncomputable def incrementSum (f : Fin n → Fin n → ℝ) (x : ℕ → Fin n) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, f (x t) (x (t + 1))

/-- `x ↦ f(x_t, x_{t+1})` is measurable on the path space. -/
theorem measurable_pair_apply (f : Fin n → Fin n → ℝ) (t : ℕ) :
    Measurable fun x : ℕ → Fin n => f (x t) (x (t + 1)) := by
  have h := (measurable_of_finite fun p : Fin n × Fin n => f p.1 p.2).comp
    ((measurable_pi_apply (X := fun _ : ℕ => Fin n) t).prodMk (measurable_pi_apply (t + 1)))
  exact h

/-- The increment sum is measurable on the path space. -/
theorem measurable_incrementSum (f : Fin n → Fin n → ℝ) (T : ℕ) :
    Measurable fun x : ℕ → Fin n => incrementSum f x T :=
  Finset.measurable_sum _ fun t _ => measurable_pair_apply f t

/-- `|Σ_{t<T} f(x_t, x_{t+1})| ≤ T Σ_{a,b} |f a b|`. -/
theorem abs_incrementSum_le (f : Fin n → Fin n → ℝ) (x : ℕ → Fin n) (T : ℕ) :
    |incrementSum f x T| ≤ T * ∑ a, ∑ b, |f a b| := by
  unfold incrementSum
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have := sum_le_sum fun t (_ : t ∈ range T) => abs_le_sum_sum_abs f (x t) (x (t + 1))
  rwa [sum_const, card_range, nsmul_eq_mul] at this

/-- The increment sum up to `T` depends only on `x_0, …, x_T`. -/
theorem incrementSum_congr (f : Fin n → Fin n → ℝ) {x y : ℕ → Fin n} {T : ℕ}
    (h : ∀ t ≤ T, x t = y t) : incrementSum f x T = incrementSum f y T :=
  sum_congr rfl fun t ht => by
    have := mem_range.1 ht
    rw [h t (by omega), h (t + 1) (by omega)]

/-- **Orthogonality of martingale increments** (exact second moment). If every row average of
`f` vanishes, `Σ_j p_aj f(a, j) = 0`, then for MC driving
`E[(Σ_{t<T} f(x_t, x_{t+1}))²] = Σ_{t<T} E[Σ_j p_{x_t j} f(x_t, j)²]`. -/
theorem integral_sq_incrementSum_driven {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {f : Fin n → Fin n → ℝ} (hf : ∀ a, ∑ j, P a j * f a j = 0) (T : ℕ) :
    ∫ u, incrementSum f (drivenPath P x₀ u) T ^ 2 ∂iidUniform ℕ =
      ∑ t ∈ range T, ∫ u, ∑ j, P (drivenPath P x₀ u t) j * f (drivenPath P x₀ u t) j ^ 2
        ∂iidUniform ℕ := by
  have := isProbabilityMeasure_iidUniform ℕ
  set Cf := ∑ a, ∑ b, |f a b|
  have hCf : 0 ≤ Cf := sum_nonneg fun a _ => sum_nonneg fun b _ => abs_nonneg _
  induction T with
  | zero =>
    simp only [incrementSum, range_zero, sum_empty, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero]
  | succ T ih =>
    set M : (ℕ → ℝ) → ℝ := fun u => incrementSum f (drivenPath P x₀ u) T
    set d : (ℕ → ℝ) → ℝ := fun u => f (drivenPath P x₀ u T) (drivenPath P x₀ u (T + 1))
    have hMm : Measurable M := (measurable_incrementSum f T).comp (measurable_drivenPath P x₀)
    have hdm : Measurable d := (measurable_pair_apply f T).comp (measurable_drivenPath P x₀)
    have hMb : ∀ u, |M u| ≤ T * Cf := fun u => abs_incrementSum_le f _ T
    have hdb : ∀ u, |d u| ≤ Cf := fun u => abs_le_sum_sum_abs f _ _
    have e : ∀ u, incrementSum f (drivenPath P x₀ u) (T + 1) ^ 2 =
        M u ^ 2 + 2 * (M u * d u) + d u ^ 2 := fun u => by
      simp only [M, d, incrementSum, sum_range_succ]
      ring
    have hi1 : Integrable (fun u => M u ^ 2) (iidUniform ℕ) :=
      integrable_of_abs_le (hMm.pow_const 2) (C := (T * Cf) ^ 2) fun u => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hMb u) 2
    have hi2 : Integrable (fun u => 2 * (M u * d u)) (iidUniform ℕ) :=
      (integrable_of_abs_le (g := fun u => M u * d u) (hMm.mul hdm) (C := T * Cf * Cf) fun u => by
        rw [abs_mul]
        exact mul_le_mul (hMb u) (hdb u) (abs_nonneg _) (by positivity)).const_mul 2
    have hi3 : Integrable (fun u => d u ^ 2) (iidUniform ℕ) :=
      integrable_of_abs_le (hdm.pow_const 2) (C := Cf ^ 2) fun u => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hdb u) 2
    have hcross : ∫ u, M u * d u ∂iidUniform ℕ = 0 := by
      have h1 := integral_mul_step_driven hP x₀ T (measurable_incrementSum f T)
        (fun x => abs_incrementSum_le f x T) (fun x y hxy => incrementSum_congr f
          fun t ht => hxy t ht) f
      change ∫ u, M u * d u ∂iidUniform ℕ = _ at h1
      rw [h1]
      simp only [hf, mul_zero, integral_zero]
    have hsq : ∫ u, d u ^ 2 ∂iidUniform ℕ = ∫ u, ∑ j, P (drivenPath P x₀ u T) j *
        f (drivenPath P x₀ u T) j ^ 2 ∂iidUniform ℕ := by
      have h1 := integral_mul_step_driven hP x₀ T (G := fun _ => (1 : ℝ)) measurable_const
        (C := 1) (fun _ => by rw [abs_one]) (fun _ _ _ => rfl) (fun a b => f a b ^ 2)
      simp only [one_mul] at h1
      exact h1
    have hi12 : Integrable (fun u => M u ^ 2 + 2 * (M u * d u)) (iidUniform ℕ) := hi1.add hi2
    rw [integral_congr_ae (Eventually.of_forall e), integral_add hi12 hi3,
      integral_add hi1 hi2, integral_const_mul, hcross, hsq, ih, sum_range_succ]
    ring

/-! ### Exact second moments of the departure discrepancies -/

/-- The departure discrepancy of `i` is the increment sum of
`f(a, b) = 1{a = i} (g b − (Pg)(i))`. -/
theorem departureDiscrepancy_eq_incrementSum (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ)
    (x : ℕ → Fin n) (i : Fin n) (T : ℕ) :
    departureDiscrepancy P g x i T =
      incrementSum (fun a b => if a = i then g b - (P *ᵥ g) i else 0) x T := by
  unfold departureDiscrepancy incrementSum
  rw [sum_filter]

/-- The total departure discrepancy `Σ_i D_i(g, T)` is the increment sum of
`f(a, b) = g b − (Pg)(a)`. -/
theorem sum_departureDiscrepancy_eq_incrementSum (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ)
    (x : ℕ → Fin n) (T : ℕ) :
    ∑ i, departureDiscrepancy P g x i T = incrementSum (fun a b => g b - (P *ᵥ g) a) x T := by
  simp only [departureDiscrepancy_eq_incrementSum, incrementSum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [mem_univ, ite_true]

/-- `Σ_j p_ij (g_j − (Pg)(i)) = 0` for stochastic `P`. -/
theorem sum_mul_sub_mulVec_eq_zero {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (g : Fin n → ℝ) (i : Fin n) : ∑ j, P i j * (g j - (P *ᵥ g) i) = 0 := by
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hP.sum_eq_one i, one_mul]
  rw [sub_eq_zero]
  rfl

/-- **Occupation counts in mean**: for MC driving, `Σ_{t<T} E φ(x_t) = Σ_i φ_i E N_i(T)`. -/
theorem sum_integral_comp_driven (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (φ : Fin n → ℝ)
    (T : ℕ) : ∑ t ∈ range T, ∫ u, φ (drivenPath P x₀ u t) ∂iidUniform ℕ =
      ∑ i, φ i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ := by
  have := isProbabilityMeasure_iidUniform ℕ
  have hint : ∀ t ∈ range T, Integrable (fun u => φ (drivenPath P x₀ u t)) (iidUniform ℕ) :=
    fun t _ => integrable_of_abs_le ((measurable_of_finite φ).comp
      (measurable_drivenPath_apply P x₀ t)) (C := ∑ i, |φ i|) fun u =>
        single_le_sum (f := fun i => |φ i|) (fun _ _ => abs_nonneg _) (mem_univ _)
  have hintN : ∀ i ∈ univ, Integrable (fun u => φ i *
      (occCount (drivenPath P x₀ u) i T : ℝ)) (iidUniform ℕ) := fun i _ =>
    (integrable_of_abs_le ((measurable_occCount_real i T).comp (measurable_drivenPath P x₀))
      (C := T) fun u => by
        change |(occCount (drivenPath P x₀ u) i T : ℝ)| ≤ T
        rw [Nat.abs_cast]
        exact_mod_cast occCount_le _ i T).const_mul _
  have e : ∀ u, ∑ t ∈ range T, φ (drivenPath P x₀ u t) =
      ∑ i, φ i * (occCount (drivenPath P x₀ u) i T : ℝ) := fun u => by
    simp only [← sum_indicator_eq_occCount, mul_sum, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [mem_univ, ite_true]
  rw [← integral_finsetSum _ hint, integral_congr_ae (Eventually.of_forall e),
    integral_finsetSum _ hintN]
  simp only [integral_const_mul]

/-- **Exact MSE of the total departure discrepancy** (MC driving, any start, every `T`):
`E[(Σ_i D_i(g, T))²] = Σ_i σ_i²(g) E N_i(T)`, with `σ_i²(g) = rowVariance P g i`. -/
theorem integral_sq_sum_departureDiscrepancy_driven {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) (g : Fin n → ℝ) (T : ℕ) :
    ∫ u, (∑ i, departureDiscrepancy P g (drivenPath P x₀ u) i T) ^ 2 ∂iidUniform ℕ =
      ∑ i, rowVariance P g i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ := by
  simp only [sum_departureDiscrepancy_eq_incrementSum]
  rw [integral_sq_incrementSum_driven hP x₀ (fun a => sum_mul_sub_mulVec_eq_zero hP g a) T]
  exact sum_integral_comp_driven P x₀ (rowVariance P g) T

/-- **Exact MSE of one departure discrepancy**: `E[D_i(g, T)²] = σ_i²(g) E N_i(T)`. -/
theorem integral_sq_departureDiscrepancy_driven {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) (g : Fin n → ℝ) (i : Fin n) (T : ℕ) :
    ∫ u, departureDiscrepancy P g (drivenPath P x₀ u) i T ^ 2 ∂iidUniform ℕ =
      rowVariance P g i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ := by
  simp only [departureDiscrepancy_eq_incrementSum]
  have hf : ∀ a, ∑ j, P a j * (if a = i then g j - (P *ᵥ g) i else 0) = 0 := fun a => by
    by_cases ha : a = i
    · subst ha
      simp only [ite_true]
      exact sum_mul_sub_mulVec_eq_zero hP g a
    · simp only [ha, ite_false, mul_zero, sum_const_zero]
  rw [integral_sq_incrementSum_driven hP x₀ hf T]
  have e : ∀ a, ∑ j, P a j * (if a = i then g j - (P *ᵥ g) i else 0) ^ 2 =
      if a = i then rowVariance P g i else 0 := fun a => by
    by_cases ha : a = i
    · subst ha
      simp only [ite_true]
      rfl
    · simp only [ha, ite_false, mul_zero, sum_const_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
  simp only [e]
  rw [sum_integral_comp_driven P x₀ (fun a => if a = i then rowVariance P g i else 0) T]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [mem_univ, ite_true]

/-- **Exact MSE of the MC transition counts** (post #3's empirical transition matrix, at the
RMSE scale): for stochastic `P`, any start and every `T`,
`E[(N_ij(T) − p_ij N_i(T))²] = p_ij (1 − p_ij) E N_i(T)`. -/
theorem integral_sq_transCount_sub_driven {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ i j : Fin n) (T : ℕ) :
    ∫ u, ((transCount (drivenPath P x₀ u) i j T : ℝ) -
        P i j * occCount (drivenPath P x₀ u) i T) ^ 2 ∂iidUniform ℕ =
      P i j * (1 - P i j) * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ := by
  simp only [transCount_sub_eq_departureDiscrepancy (P : Matrix (Fin n) (Fin n) ℝ)]
  rw [integral_sq_departureDiscrepancy_driven hP x₀ _ i T, rowVariance_indicator hP i j]

/-- `0 ≤ E N_i(T) ≤ T`. -/
theorem integral_occCount_driven_mem_Icc (P : Fin n → Fin n → ℝ) (x₀ i : Fin n) (T : ℕ) :
    ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ ∈ Set.Icc (0 : ℝ) T := by
  have := isProbabilityMeasure_iidUniform ℕ
  refine ⟨integral_nonneg fun u => Nat.cast_nonneg _, ?_⟩
  have h := integral_mono_of_nonneg (μ := iidUniform ℕ)
    (f := fun u => (occCount (drivenPath P x₀ u) i T : ℝ)) (g := fun _ => (T : ℝ))
    (Eventually.of_forall fun u => Nat.cast_nonneg _) (integrable_const _)
    (Eventually.of_forall fun u => by
      change (occCount (drivenPath P x₀ u) i T : ℝ) ≤ T
      exact_mod_cast occCount_le _ i T)
  rwa [integral_const, probReal_univ, one_smul] at h

/-- **The `O(1/√T)` RMSE of the MC transition counts**:
`E[(N_ij(T) − p_ij N_i(T))²] ≤ p_ij (1 − p_ij) T`. -/
theorem integral_sq_transCount_sub_driven_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ i j : Fin n) (T : ℕ) :
    ∫ u, ((transCount (drivenPath P x₀ u) i j T : ℝ) -
        P i j * occCount (drivenPath P x₀ u) i T) ^ 2 ∂iidUniform ℕ ≤
      P i j * (1 - P i j) * T := by
  rw [integral_sq_transCount_sub_driven hP x₀ i j T]
  have h1 : 0 ≤ P i j * (1 - P i j) := by
    have := rowVariance_indicator hP i j
    rw [← this]
    exact sum_nonneg fun k _ => mul_nonneg (hP.nonneg i k) (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (integral_occCount_driven_mem_Icc P x₀ i T).2 h1

/-! ### The occupation error at the RMSE scale -/

/-- **Jensen for `|X|`**: `E|X| ≤ √(E X²)` for a bounded measurable `X`. -/
theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : Ω → ℝ} (hX : Measurable X) {C : ℝ} (hC : ∀ ω, |X ω| ≤ C) :
    ∫ ω, |X ω| ∂Q ≤ √(∫ ω, X ω ^ 2 ∂Q) := by
  set m := ∫ ω, |X ω| ∂Q
  have hm : 0 ≤ m := integral_nonneg fun ω => abs_nonneg _
  have hiA : Integrable (fun ω => |X ω|) Q :=
    integrable_of_abs_le (continuous_abs.measurable.comp hX) (C := C) fun ω => by
      rw [abs_abs]
      exact hC ω
  have hi2 : Integrable (fun ω => X ω ^ 2) Q :=
    integrable_of_abs_le (hX.pow_const 2) (C := C ^ 2) fun ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) 2
  have h0 : 0 ≤ ∫ ω, (|X ω| - m) ^ 2 ∂Q := integral_nonneg fun ω => sq_nonneg _
  have e : ∀ ω, (|X ω| - m) ^ 2 = X ω ^ 2 + (-(2 * m) * |X ω| + m ^ 2) := fun ω => by
    rw [sub_sq, sq_abs]
    ring
  have hi3 : Integrable (fun ω => -(2 * m) * |X ω| + m ^ 2) Q :=
    (hiA.const_mul _).add (integrable_const _)
  rw [integral_congr_ae (Eventually.of_forall e), integral_add hi2 hi3,
    integral_add (hiA.const_mul _) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul] at h0
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith

/-- The occupation error is measurable. -/
theorem measurable_occCount_sub_driven (P : Fin n → Fin n → ℝ) (x₀ s : Fin n) (c : ℝ)
    (T : ℕ) : Measurable fun u => (occCount (drivenPath P x₀ u) s T : ℝ) - T * c :=
  ((measurable_occCount_real s T).comp (measurable_drivenPath P x₀)).sub measurable_const

/-- **Two-sided MSE bounds for the occupation error.** Let `h − Ph = 1_{s} − c`, `|h| ≤ M`, and
`V(T) = Σ_i σ_i²(h) E N_i(T)` (the exact MSE of `Σ_i D_i(h, T)`). Then for MC driving
`√V (√V − 4M) ≤ E[(N_s(T) − T c)²] ≤ (2M + √V)²`. -/
theorem integral_sq_occCount_sub_driven_mem {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) :
    √(∑ i, rowVariance P h i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ) *
        (√(∑ i, rowVariance P h i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ)
          ∂iidUniform ℕ) - 4 * M) ≤
      ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ ∧
    ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ ≤
      (2 * M + √(∑ i, rowVariance P h i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ)
        ∂iidUniform ℕ)) ^ 2 := by
  have := isProbabilityMeasure_iidUniform ℕ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM s)
  set V := ∑ i, rowVariance P h i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ
  set D : (ℕ → ℝ) → ℝ := fun u => ∑ i, departureDiscrepancy P h (drivenPath P x₀ u) i T
  set E : (ℕ → ℝ) → ℝ := fun u => (occCount (drivenPath P x₀ u) s T : ℝ) - T * c
  set Ch := ∑ a, ∑ b, |(fun a b => h b - (P *ᵥ h) a) a b|
  have hDm : Measurable D := by
    have e : D = fun u => incrementSum (fun a b => h b - (P *ᵥ h) a) (drivenPath P x₀ u) T :=
      funext fun u => sum_departureDiscrepancy_eq_incrementSum P h _ T
    rw [e]
    have h1 := (measurable_incrementSum (fun a b => h b - (P *ᵥ h) a) T).comp
      (measurable_drivenPath P x₀)
    exact h1
  have hDb : ∀ u, |D u| ≤ T * Ch := fun u => by
    simp only [D, sum_departureDiscrepancy_eq_incrementSum]
    exact abs_incrementSum_le _ _ T
  have hEm : Measurable E := measurable_occCount_sub_driven P x₀ s c T
  have hED : ∀ u, ∃ B, |B| ≤ 2 * M ∧ E u = B + D u := fun u => by
    refine ⟨h (drivenPath P x₀ u 0) - h (drivenPath P x₀ u T), ?_,
      occCount_sub_eq_boundary_add P hh _ T⟩
    have := abs_sub (h (drivenPath P x₀ u 0)) (h (drivenPath P x₀ u T))
    linarith [hM (drivenPath P x₀ u 0), hM (drivenPath P x₀ u T)]
  have hEb : ∀ u, |E u| ≤ 2 * M + T * Ch := fun u => by
    obtain ⟨B, hB, hE⟩ := hED u
    rw [hE]
    exact (abs_add_le _ _).trans (add_le_add hB (hDb u))
  have hiE : Integrable (fun u => E u ^ 2) (iidUniform ℕ) :=
    integrable_of_abs_le (hEm.pow_const 2) (C := (2 * M + T * Ch) ^ 2) fun u => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hEb u) 2
  have hiD2 : Integrable (fun u => D u ^ 2) (iidUniform ℕ) :=
    integrable_of_abs_le (hDm.pow_const 2) (C := (T * Ch) ^ 2) fun u => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hDb u) 2
  have hiDa : Integrable (fun u => |D u|) (iidUniform ℕ) :=
    integrable_of_abs_le (continuous_abs.measurable.comp hDm) (C := T * Ch) fun u => by
      rw [abs_abs]
      exact hDb u
  have hD2 : ∫ u, D u ^ 2 ∂iidUniform ℕ = V :=
    integral_sq_sum_departureDiscrepancy_driven hP x₀ h T
  have hJ : ∫ u, |D u| ∂iidUniform ℕ ≤ √V := by
    rw [← hD2]
    exact integral_abs_le_sqrt_integral_sq hDm hDb
  have hV0 : 0 ≤ V := by
    rw [← hD2]
    exact integral_nonneg fun u => sq_nonneg _
  have hsqV : √V ^ 2 = V := Real.sq_sqrt hV0
  have hJ0 : 0 ≤ ∫ u, |D u| ∂iidUniform ℕ := integral_nonneg fun u => abs_nonneg _
  constructor
  · -- pointwise `E² ≥ D² − 4M|D|`
    have hle : ∀ u, D u ^ 2 + -(4 * M) * |D u| ≤ E u ^ 2 := fun u => by
      obtain ⟨B, hB, hE⟩ := hED u
      rw [hE]
      have h1 : -(2 * B * D u) ≤ 2 * (2 * M) * |D u| := by
        have := neg_abs_le (2 * B * D u)
        rw [abs_mul, abs_mul, abs_two] at this
        nlinarith [abs_nonneg (D u), abs_nonneg B]
      nlinarith [sq_nonneg B]
    have hi4 : Integrable (fun u => D u ^ 2 + -(4 * M) * |D u|) (iidUniform ℕ) :=
      hiD2.add (hiDa.const_mul _)
    have := integral_mono hi4 hiE hle
    rw [integral_add hiD2 (hiDa.const_mul _), integral_const_mul, hD2] at this
    nlinarith [Real.sqrt_nonneg V]
  · -- pointwise `E² ≤ 4M² + 4M|D| + D²`
    have hle : ∀ u, E u ^ 2 ≤ (2 * M) ^ 2 + (4 * M * |D u| + D u ^ 2) := fun u => by
      obtain ⟨B, hB, hE⟩ := hED u
      rw [hE]
      have h1 : 2 * B * D u ≤ 2 * (2 * M) * |D u| := by
        have := le_abs_self (2 * B * D u)
        rw [abs_mul, abs_mul, abs_two] at this
        nlinarith [abs_nonneg (D u), abs_nonneg B]
      have h2 : B ^ 2 ≤ (2 * M) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hB 2
      nlinarith
    have hi5 : Integrable (fun u => 4 * M * |D u| + D u ^ 2) (iidUniform ℕ) :=
      (hiDa.const_mul _).add hiD2
    have hi6 : Integrable (fun u => (2 * M) ^ 2 + (4 * M * |D u| + D u ^ 2)) (iidUniform ℕ) :=
      (integrable_const _).add hi5
    have := integral_mono hiE hi6 hle
    rw [integral_add (integrable_const _) hi5,
      integral_add (hiDa.const_mul _) hiD2, integral_const_mul, hD2, integral_const,
      probReal_univ, one_smul] at this
    nlinarith [Real.sqrt_nonneg V]

/-- **The RMSE of the MC occupation frequency is `O(1/√T)`** (post #3's rate, at the RMSE
scale): with `h − Ph = 1_{s} − c`, `|h| ≤ M`,
`E[(N_s(T) − T c)²] ≤ (2M + √(T Σ_i σ_i²(h)))²`. -/
theorem integral_sq_occCount_sub_driven_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) :
    ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ ≤
      (2 * M + √(T * ∑ i, rowVariance P h i)) ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM s)
  refine (integral_sq_occCount_sub_driven_mem hP x₀ hh hM T).2.trans ?_
  have hrv : ∀ i, 0 ≤ rowVariance P h i := fun i =>
    sum_nonneg fun k _ => mul_nonneg (hP.nonneg i k) (sq_nonneg _)
  have hV : ∑ i, rowVariance P h i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ)
      ∂iidUniform ℕ ≤ T * ∑ i, rowVariance P h i := by
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [mul_comm (T : ℝ)]
    exact mul_le_mul_of_nonneg_left (integral_occCount_driven_mem_Icc P x₀ i T).2 (hrv i)
  have := Real.sqrt_le_sqrt hV
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- **The mean occupation frequency converges**: with `h − Ph = 1_{s} − c`, `|h| ≤ M`,
`|E N_s(T) − T c| ≤ 2M + √(T Σ_i σ_i²(h))` (from the RMSE bound), hence `E N_s(T)/T → c`. -/
theorem abs_integral_occCount_sub_driven_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) :
    |∫ u, (occCount (drivenPath P x₀ u) s T : ℝ) ∂iidUniform ℕ - T * c| ≤
      2 * M + √(T * ∑ i, rowVariance P h i) := by
  have := isProbabilityMeasure_iidUniform ℕ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM s)
  have hEm := measurable_occCount_sub_driven P x₀ s c T
  have hEb : ∀ u, |(occCount (drivenPath P x₀ u) s T : ℝ) - T * c| ≤ T + T * |c| := fun u => by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [Nat.abs_cast]
      exact_mod_cast occCount_le _ s T
    · rw [abs_mul, Nat.abs_cast]
  have hiN : Integrable (fun u => (occCount (drivenPath P x₀ u) s T : ℝ)) (iidUniform ℕ) :=
    integrable_of_abs_le ((measurable_occCount_real s T).comp (measurable_drivenPath P x₀))
      (C := T) fun u => by
        rw [Nat.abs_cast]
        exact_mod_cast occCount_le _ s T
  have e : ∫ u, (occCount (drivenPath P x₀ u) s T : ℝ) ∂iidUniform ℕ - T * c =
      ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ∂iidUniform ℕ := by
    rw [integral_sub hiN (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [e]
  refine (abs_integral_le_integral_abs).trans ((integral_abs_le_sqrt_integral_sq hEm hEb).trans ?_)
  calc √(∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ)
      ≤ √((2 * M + √(T * ∑ i, rowVariance P h i)) ^ 2) :=
        Real.sqrt_le_sqrt (integral_sq_occCount_sub_driven_le hP x₀ hh hM T)
    _ = 2 * M + √(T * ∑ i, rowVariance P h i) := Real.sqrt_sq (by positivity)

/-- **The mean occupation frequency converges**: `E N_s(T)/T → c` for MC driving, whenever
Poisson's equation `h − Ph = 1_{s} − c` has a bounded solution. -/
theorem tendsto_integral_occCount_div_driven {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M) :
    Tendsto (fun T : ℕ => (∫ u, (occCount (drivenPath P x₀ u) s T : ℝ) ∂iidUniform ℕ) / T)
      atTop (𝓝 c) := by
  set R := ∑ i, rowVariance P h i
  have hR : 0 ≤ R := sum_nonneg fun i _ =>
    sum_nonneg fun k _ => mul_nonneg (hP.nonneg i k) (sq_nonneg _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun T : ℕ => 2 * M * (T : ℝ)⁻¹ + √R * (√(T : ℝ))⁻¹) atTop (𝓝 0) := by
    have h1 := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
      (2 * M)
    have h2 := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))).const_mul √R
    have := h1.add h2
    rw [mul_zero, mul_zero, add_zero] at this
    exact this
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hg
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have key := abs_integral_occCount_sub_driven_le hP x₀ hh hM T
  rw [Real.norm_eq_abs]
  have e : (∫ u, (occCount (drivenPath P x₀ u) s T : ℝ) ∂iidUniform ℕ) / T - c =
      (∫ u, (occCount (drivenPath P x₀ u) s T : ℝ) ∂iidUniform ℕ - T * c) / T := by
    field_simp
  rw [e, abs_div, abs_of_pos hT0, div_le_iff₀ hT0]
  have hsq : √(T * R) = √(T : ℝ) * √R := Real.sqrt_mul hT0.le R
  have hsT : √(T : ℝ) * √(T : ℝ) = T := Real.mul_self_sqrt hT0.le
  have hsT0 : 0 < √(T : ℝ) := Real.sqrt_pos.2 hT0
  have e2 : (2 * M * (T : ℝ)⁻¹ + √R * (√(T : ℝ))⁻¹) * T = 2 * M + √(T * R) := by
    have h1 : (√(T : ℝ))⁻¹ * T = √(T : ℝ) := by
      rw [inv_mul_eq_div, div_eq_iff hsT0.ne']
      exact hsT.symm
    rw [hsq, add_mul, mul_assoc (2 * M), inv_mul_cancel₀ hT0.ne', mul_assoc √R, h1]
    ring
  rw [e2]
  exact key

/-- **The RMSE of the MC occupation frequency is of exact order `1/√T`** (lower bound). Let
`h − Ph = 1_{s} − c`, `|h| ≤ M`, suppose the mean frequencies converge, `E N_i(T)/T → w_i`,
and the **nondegeneracy** `Σ_i w_i σ_i²(h) > 0` (the asymptotic variance of `N_s`). Then
there is `κ > 0` with `E[(N_s(T) − T c)²] ≥ κ T` for all large `T`. -/
theorem eventually_integral_sq_occCount_sub_driven_ge {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    {w : Fin n → ℝ}
    (hfreq : ∀ i, Tendsto (fun T : ℕ =>
      (∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ) / T) atTop (𝓝 (w i)))
    (hpos : 0 < ∑ i, w i * rowVariance P h i) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℕ in atTop,
      κ * T ≤ ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ := by
  set σ2 := ∑ i, w i * rowVariance P h i
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM s)
  set V : ℕ → ℝ := fun T => ∑ i, rowVariance P h i *
    ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ
  have hVt : Tendsto (fun T : ℕ => V T / T) atTop (𝓝 σ2) := by
    have e : ∀ T : ℕ, V T / T = ∑ i, rowVariance P h i *
        ((∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ) / T) := fun T => by
      simp only [V, sum_div, mul_div_assoc]
    simp only [e]
    have := tendsto_finsetSum (univ : Finset (Fin n)) fun i _ => (hfreq i).const_mul
      (rowVariance P h i)
    simp only [σ2, mul_comm (w _)]
    exact this
  refine ⟨σ2 / 4, by positivity, ?_⟩
  filter_upwards [hVt.eventually (lt_mem_nhds (show σ2 / 2 < σ2 by linarith)),
    eventually_ge_atTop (⌈128 * M ^ 2 / σ2⌉₊ + 1)] with T hV hT
  have hT1 : (⌈128 * M ^ 2 / σ2⌉₊ : ℝ) + 1 ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith [Nat.cast_nonneg (α := ℝ) ⌈128 * M ^ 2 / σ2⌉₊]
  have hTM : 128 * M ^ 2 / σ2 ≤ T := by linarith [Nat.le_ceil (128 * M ^ 2 / σ2)]
  have hVT : σ2 / 2 * T < V T := by rwa [lt_div_iff₀ hT0] at hV
  have hV64 : 64 * M ^ 2 ≤ V T := by
    have : 128 * M ^ 2 ≤ σ2 * T := by
      rw [div_le_iff₀ hpos] at hTM
      linarith
    nlinarith
  have hV0 : 0 ≤ V T := le_trans (by positivity) hV64
  have hs8 : 8 * M ≤ √(V T) := by
    rw [show 8 * M = √((8 * M) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsq : √(V T) * √(V T) = V T := Real.mul_self_sqrt hV0
  have hlow := (integral_sq_occCount_sub_driven_mem hP x₀ hh hM T).1
  change √(V T) * (√(V T) - 4 * M) ≤ _ at hlow
  nlinarith

/-- **The RMSE of the MC occupation frequency** in frequency units: for `T > 0`,
`E[(N_s(T)/T − c)²] ≤ (2M + √(T Σ_i σ_i²(h)))² / T²`, i.e. `RMSE = O(1/√T)`. -/
theorem integral_sq_occFreq_sub_driven_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    {T : ℕ} (hT : 0 < T) :
    ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) / T - c) ^ 2 ∂iidUniform ℕ ≤
      (2 * M + √(T * ∑ i, rowVariance P h i)) ^ 2 / T ^ 2 := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have e : ∀ u, ((occCount (drivenPath P x₀ u) s T : ℝ) / T - c) ^ 2 =
      ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 / T ^ 2 := fun u => by
    field_simp
  rw [integral_congr_ae (Eventually.of_forall e), integral_div]
  exact div_le_div_of_nonneg_right (integral_sq_occCount_sub_driven_le hP x₀ hh hM T)
    (by positivity)

/-- **The RMSE of the MC transition counts** in frequency units:
`E[((N_ij(T) − p_ij N_i(T))/T)²] ≤ p_ij (1 − p_ij)/T`. -/
theorem integral_sq_transFreq_sub_driven_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ i j : Fin n) {T : ℕ} (hT : 0 < T) :
    ∫ u, (((transCount (drivenPath P x₀ u) i j T : ℝ) -
        P i j * occCount (drivenPath P x₀ u) i T) / T) ^ 2 ∂iidUniform ℕ ≤
      P i j * (1 - P i j) / T := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  simp only [div_pow]
  rw [integral_div, div_le_div_iff₀ (by positivity) hT0]
  have := integral_sq_transCount_sub_driven_le hP x₀ i j T
  have e : P i j * (1 - P i j) * (T : ℝ) ^ 2 = P i j * (1 - P i j) * T * T := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right this hT0.le

/-- `μ ⬝ᵥ 1_{k} = μ k`. -/
theorem dotProduct_indicator (μ : Fin n → ℝ) (k : Fin n) :
    μ ⬝ᵥ (fun i => if i = k then (1 : ℝ) else 0) = μ k := by
  simp only [dotProduct, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [mem_univ, ite_true]

/-- **Exact order `1/√T` for irreducible chains.** For an irreducible stochastic `P` with
stationary distribution `π`, the mean frequencies converge, `E N_i(T)/T → π_i`
(`tendsto_integral_occCount_div_driven` with the Poisson solutions of `exists_poisson`), so
under the nondegeneracy `Σ_i π_i σ_i²(h) > 0` there is `κ > 0` with
`E[(N_s(T) − T c)²] ≥ κ T` for all large `T`. -/
theorem eventually_integral_sq_occCount_sub_driven_ge_of_irreducible
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsStochastic P) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j)
    {μ : Fin n → ℝ} (hμ : IsStationaryDistribution P μ) (x₀ : Fin n) {h : Fin n → ℝ}
    {s : Fin n} {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) (hpos : 0 < ∑ i, μ i * rowVariance P h i) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℕ in atTop,
      κ * T ≤ ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ := by
  have : Nonempty (Fin n) := ⟨x₀⟩
  refine eventually_integral_sq_occCount_sub_driven_ge hP x₀ hh hM (fun i => ?_) hpos
  obtain ⟨hi, hhi⟩ := exists_poisson hP.nonneg hP.sum_eq_one hirr hμ
    (fun k => if k = i then (1 : ℝ) else 0)
  rw [dotProduct_indicator] at hhi
  exact tendsto_integral_occCount_div_driven hP x₀ hhi (M := ∑ k, |hi k|) fun k =>
    single_le_sum (f := fun k => |hi k|) (fun _ _ => abs_nonneg _) (mem_univ k)

/-! ### A non-degenerate instance: the two-state chain with stay probability `7/8` -/

/-- The `7/8`-chain is stochastic. -/
theorem isStochastic_twoStateStay78 : IsStochastic twoStateStay78 := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [twoStateStay78]
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_two]
    fin_cases i <;> simp only [twoStateStay78] <;> norm_num

/-- The `7/8`-chain is irreducible (all entries are positive). -/
theorem irreducible_twoStateStay78 : ∀ i j, ∃ k, 0 < (twoStateStay78 ^ k) i j := fun i j =>
  ⟨1, by
    rw [pow_one]
    simp only [twoStateStay78]
    split_ifs <;> norm_num⟩

/-- Poisson's equation for the `7/8`-chain and `s = 0`: `h = (2, −2)` solves
`h − Ph = 1_{0} − 1/2`. -/
theorem poisson_twoStateStay78 (i : Fin 2) :
    (fun k : Fin 2 => if k = 0 then (2 : ℝ) else -2) i -
        (twoStateStay78 *ᵥ fun k : Fin 2 => if k = 0 then (2 : ℝ) else -2) i =
      (if i = 0 then 1 else 0) - 1 / 2 := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i <;> simp only [twoStateStay78] <;> norm_num

/-- For the `7/8`-chain and `h = (2, −2)`, both row variances are `σ_i²(h) = 7/4`. -/
theorem rowVariance_twoStateStay78 (i : Fin 2) :
    rowVariance twoStateStay78 (fun k : Fin 2 => if k = 0 then (2 : ℝ) else -2) i = 7 / 4 := by
  simp only [rowVariance, mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i <;> simp only [twoStateStay78] <;> norm_num

/-- **The lower bound is not vacuous** (two-state chain, stay probability `7/8`, any start).
The MC occupation error of state `0` satisfies, for every `T`,
`E[(N_0(T) − T/2)²] ≤ (4 + √(7T/2))²`, and `E[(N_0(T) − T/2)²] ≥ κ T` for all large `T`, for
some `κ > 0`: the RMSE of the frequency `N_0(T)/T` is of exact order `1/√T`. -/
theorem occCount_mse_twoStateStay78 (x₀ : Fin 2) :
    (∀ T : ℕ, ∫ u, ((occCount (drivenPath twoStateStay78 x₀ u) 0 T : ℝ) - T * (1 / 2)) ^ 2
        ∂iidUniform ℕ ≤ (4 + √(7 * T / 2)) ^ 2) ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℕ in atTop,
        κ * T ≤ ∫ u, ((occCount (drivenPath twoStateStay78 x₀ u) 0 T : ℝ) - T * (1 / 2)) ^ 2
          ∂iidUniform ℕ := by
  have hM : ∀ i : Fin 2, |(fun k : Fin 2 => if k = 0 then (2 : ℝ) else -2) i| ≤ 2 := fun i => by
    fin_cases i <;> norm_num
  have hrv : ∑ i, rowVariance twoStateStay78 (fun k : Fin 2 => if k = 0 then (2 : ℝ) else -2) i
      = 7 / 2 := by
    rw [Fin.sum_univ_two, rowVariance_twoStateStay78, rowVariance_twoStateStay78]
    norm_num
  refine ⟨fun T => ?_, eventually_integral_sq_occCount_sub_driven_ge_of_irreducible
    isStochastic_twoStateStay78 irreducible_twoStateStay78
    isStationaryDistribution_twoStateStay78 x₀ poisson_twoStateStay78 hM ?_⟩
  · have := integral_sq_occCount_sub_driven_le isStochastic_twoStateStay78 x₀
      poisson_twoStateStay78 hM T
    rw [hrv] at this
    convert this using 3
    · norm_num
    · ring_nf
  · rw [Fin.sum_univ_two, rowVariance_twoStateStay78, rowVariance_twoStateStay78]
    norm_num

end RQMCMarkov.MarkovDriving

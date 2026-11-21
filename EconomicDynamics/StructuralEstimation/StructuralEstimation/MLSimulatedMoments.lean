/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.MLSandwich
import StructuralEstimation.MLExercises

/-!
# The simulated method of moments (§12.3.1)

Miao, §12.3.1, pp. 400–403, equation (12.5) and the asymptotic properties of SMM. Data
`x₁, …, x_T`; for each `θ`, `S` simulated paths `x_t^s(θ)`; moments `m(x) ∈ ℝ^q`.

* `ml_smmObjective`, `eq_12_5`: the SMM objective
  `[∑ₜ (m(xₜ) − (1/S)∑ₛ m(xₜˢ(θ)))]ᵀ W [∑ₜ (…)]` is `T² g_T(θ)ᵀ W g_T(θ)` for the GMM moment
  function `h(xₜ, θ) = m(xₜ) − (1/S)∑ₛ m(xₜˢ(θ))` of (12.5), so SMM is the GMM estimator with
  this `h` (`ml_smm_isMinOn_iff`).
* `ml_smm_moment_mean_zero`: `E h(xₜ, θ₀) = 0` when the simulated moments have the data's mean.
* `ml_variance_linear_comb`: `Var(∑ aᵢYᵢ) = ∑ aᵢ² Var Yᵢ` for independent `Yᵢ`;
  `ml_smm_variance_factor`: for independent `Y₀, Y₁, …, Y_S` with common variance `σ²`,
  `Var(Y₀ − (1/S)∑ₛ Yₛ) = (1 + 1/S)σ²` — the source of the factor `1 + 1/S` in `Q_S`.
* `ml_smm_Q`, `ml_smm_optimal_weight` (p. 402): `Q_S(W) = (1 + 1/S)(BᵀWB)⁻¹BᵀWΣWB(BᵀWB)⁻¹`;
  at `W = ((1 + 1/S)Σ)⁻¹`, `Q_S = (1 + 1/S)(BᵀΣ⁻¹B)⁻¹`, and `Q_S(W) − Q_S(W*)` is positive
  semidefinite for every symmetric `W`. `ml_smm_Q_tendsto` (p. 403): as `S → ∞` the optimal
  `Q_S` tends to the GMM variance `(BᵀΣ⁻¹B)⁻¹`.
* A concrete SMM model in which every claim of p. 402 is proved: the location model
  `xₜ = θ₀ + ωₜ`, `xₜˢ(θ) = θ + ωₜˢ`, `m(x) = x`, `W = 1`. `ml_smm_location_objective`: the SMM
  objective is `T²(θ̂ − θ)²` with `θ̂ = x̄ − (1/(TS))∑ₜ∑ₛ ωₜˢ`, the unique minimiser;
  `ml_smm_location_consistent`: `θ̂_T → θ₀` a.s. for fixed `S` (consistency);
  `ml_smm_location_variance`: `Var(√T(θ̂_T − θ₀)) = (1 + 1/S)σ²` exactly;
  `ml_smm_location_asymptotic`: `√T(θ̂_T − θ₀) ⇒ N(0, (1 + 1/S)σ²) = N(0, Q_S)`.

The J-test (12.6) and its `χ²(q − k)` limit are §12.1 GMM results (not formalised here).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology Matrix

/-- The SMM objective (Miao, p. 401): with `v(θ) = ∑ₜ (m(xₜ) − (1/S)∑ₛ m(xₜˢ(θ)))`,
`J(θ) = v(θ)ᵀ W v(θ)`. -/
noncomputable def ml_smmObjective {X Θ : Type*} {q S T : ℕ} (m : X → Fin q → ℝ)
    (x : Fin T → X) (xs : Θ → Fin S → Fin T → X) (W : Matrix (Fin q) (Fin q) ℝ) (θ : Θ) : ℝ :=
  (∑ t, (m (x t) - (1 / (S : ℝ)) • ∑ s, m (xs θ s t))) ⬝ᵥ
    (W *ᵥ ∑ t, (m (x t) - (1 / (S : ℝ)) • ∑ s, m (xs θ s t)))

/-- The SMM moment function (12.5): `h(xₜ, θ) = m(xₜ) − (1/S)∑ₛ m(xₜˢ(θ))`. -/
noncomputable def ml_smmMoment {X : Type*} {q S : ℕ} (m : X → Fin q → ℝ) (x : X)
    (xs : Fin S → X) : Fin q → ℝ :=
  m x - (1 / (S : ℝ)) • ∑ s, m (xs s)

/-- Miao, (12.5), p. 401: the SMM objective is `T² g_T(θ)ᵀ W g_T(θ)` with
`g_T(θ) = (1/T)∑ₜ h(xₜ, θ)`, so SMM is a special case of GMM. -/
theorem eq_12_5 {X Θ : Type*} {q S T : ℕ} (hT : 0 < T) (m : X → Fin q → ℝ) (x : Fin T → X)
    (xs : Θ → Fin S → Fin T → X) (W : Matrix (Fin q) (Fin q) ℝ) (θ : Θ) :
    let g := (1 / (T : ℝ)) • ∑ t, ml_smmMoment m (x t) (fun s => xs θ s t)
    ml_smmObjective m x xs W θ = (T : ℝ) ^ 2 * (g ⬝ᵥ (W *ᵥ g)) := by
  intro g
  have hT' : (T : ℝ) ≠ 0 := by positivity
  have hv : ∑ t, (m (x t) - (1 / (S : ℝ)) • ∑ s, m (xs θ s t)) = (T : ℝ) • g := by
    simp only [g, ml_smmMoment, smul_smul]
    rw [mul_one_div_cancel hT', one_smul]
  unfold ml_smmObjective
  rw [hv, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- Miao, p. 401: `θ̂_ST` minimises the SMM objective iff it minimises the GMM criterion
`g_T(θ)ᵀ W g_T(θ)` with the moment function (12.5). -/
theorem ml_smm_isMinOn_iff {X Θ : Type*} {q S T : ℕ} (hT : 0 < T) (m : X → Fin q → ℝ)
    (x : Fin T → X) (xs : Θ → Fin S → Fin T → X) (W : Matrix (Fin q) (Fin q) ℝ) (Θ₀ : Set Θ)
    (θhat : Θ) :
    IsMinOn (ml_smmObjective m x xs W) Θ₀ θhat ↔
      IsMinOn (fun θ => ((1 / (T : ℝ)) • ∑ t, ml_smmMoment m (x t) (fun s => xs θ s t)) ⬝ᵥ
        (W *ᵥ ((1 / (T : ℝ)) • ∑ t, ml_smmMoment m (x t) (fun s => xs θ s t)))) Θ₀ θhat := by
  have hT2 : (0 : ℝ) < (T : ℝ) ^ 2 := by positivity
  constructor
  · intro h θ hθ
    have := h hθ
    simp only [Set.mem_ofPred_eq, eq_12_5 hT] at this ⊢
    exact le_of_mul_le_mul_left this hT2
  · intro h θ hθ
    have := h hθ
    simp only [Set.mem_ofPred_eq, eq_12_5 hT] at this ⊢
    exact mul_le_mul_of_nonneg_left this hT2.le

/-- Miao, p. 401: the population moment condition of SMM. If the simulated moments
`Yₛ = m(xₜˢ(θ₀))` have the mean of the data moment `Y₀ = m(xₜ)`, then
`E h(xₜ, θ₀) = E[Y₀ − (1/S)∑ₛ Yₛ] = 0`. -/
theorem ml_smm_moment_mean_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S : ℕ}
    (hS : 0 < S) (Y₀ : Ω → ℝ) (Y : Fin S → Ω → ℝ) (h0 : Integrable Y₀ P)
    (hY : ∀ s, Integrable (Y s) P) (hmean : ∀ s, ∫ ω, Y s ω ∂P = ∫ ω, Y₀ ω ∂P) :
    ∫ ω, (Y₀ ω - (1 / (S : ℝ)) * ∑ s, Y s ω) ∂P = 0 := by
  rw [integral_sub h0 ((integrable_finsetSum _ fun s _ => hY s).const_mul _),
    integral_const_mul, integral_finsetSum _ fun s _ => hY s]
  simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (S : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `Var(∑ᵢ aᵢYᵢ) = ∑ᵢ aᵢ² Var(Yᵢ)` for independent square-integrable `Yᵢ`. -/
theorem ml_variance_linear_comb {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype ι] (Y : ι → Ω → ℝ) (a : ι → ℝ) (hindep : iIndepFun Y P)
    (hY : ∀ i, MemLp (Y i) 2 P) :
    Var[fun ω => ∑ i, a i * Y i ω; P] = ∑ i, a i ^ 2 * Var[Y i; P] := by
  have hfun : (fun ω => ∑ i, a i * Y i ω) = ∑ i, fun ω => a i * Y i ω := by
    funext ω; simp [Finset.sum_apply]
  rw [hfun, IndepFun.variance_sum (fun i _ => (hY i).const_mul (a i))]
  · exact Finset.sum_congr rfl fun i _ => variance_const_mul _ _ _
  · intro i _ j _ hij
    exact (hindep.indepFun hij).comp (measurable_const_mul (a i)) (measurable_const_mul (a j))

/-- Miao, p. 402 (the factor `1 + 1/S`): if the data moment `Y₀` and the `S` simulated moments
`Y₁, …, Y_S` are independent with common variance `σ²`, then
`Var(Y₀ − (1/S)∑ₛ Yₛ) = (1 + 1/S)σ²`. -/
theorem ml_smm_variance_factor {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : ℕ} (hS : 0 < S) (Y : Option (Fin S) → Ω → ℝ)
    (hindep : iIndepFun Y P) (hY : ∀ i, MemLp (Y i) 2 P) (σ2 : ℝ)
    (hvar : ∀ i, Var[Y i; P] = σ2) :
    Var[fun ω => Y none ω - (1 / (S : ℝ)) * ∑ s, Y (some s) ω; P] = (1 + 1 / S) * σ2 := by
  let a : Option (Fin S) → ℝ := fun i => Option.elim i 1 fun _ => -(1 / (S : ℝ))
  have hfun : (fun ω => Y none ω - (1 / (S : ℝ)) * ∑ s, Y (some s) ω) =
      fun ω => ∑ i, a i * Y i ω := by
    funext ω
    rw [Fintype.sum_option]
    simp only [a, Option.elim_none, Option.elim_some, one_mul, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hfun, ml_variance_linear_comb Y a hindep hY, Fintype.sum_option]
  simp only [a, Option.elim_none, Option.elim_some, hvar, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (S : ℝ) ≠ 0 := by positivity
  field_simp

/-- The asymptotic variance of SMM (Miao, p. 402):
`Q_S(W) = (1 + 1/S)(BᵀWB)⁻¹BᵀWΣWB(BᵀWB)⁻¹`. -/
noncomputable def ml_smm_Q {q k : ℕ} (S : ℕ) (B : Matrix (Fin q) (Fin k) ℝ)
    (Sig W : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (1 + 1 / (S : ℝ)) • ml_sandwich B Sig W

/-- **Optimal weighting matrix** of SMM (Miao, p. 402): at `W* = ((1 + 1/S)Σ)⁻¹`,
`Q_S(W*) = (1 + 1/S)(BᵀΣ⁻¹B)⁻¹`, and `Q_S(W) − Q_S(W*)` is positive semidefinite for every
symmetric `W` with `BᵀWB` invertible. -/
theorem ml_smm_optimal_weight {q k : ℕ} (S : ℕ) (B : Matrix (Fin q) (Fin k) ℝ)
    (Sig W : Matrix (Fin q) (Fin q) ℝ) (hSig : Sig.PosSemidef) (hSigu : IsUnit Sig.det)
    (hM : IsUnit (Bᵀ * Sig⁻¹ * B).det) (hW : Wᵀ = W) (hA : IsUnit (Bᵀ * W * B).det) :
    ml_smm_Q S B Sig ((1 + 1 / (S : ℝ)) • Sig)⁻¹ = (1 + 1 / (S : ℝ)) • (Bᵀ * Sig⁻¹ * B)⁻¹ ∧
      (ml_smm_Q S B Sig W - ml_smm_Q S B Sig ((1 + 1 / (S : ℝ)) • Sig)⁻¹).PosSemidef := by
  have hc : (0 : ℝ) < 1 + 1 / (S : ℝ) := by positivity
  have h1 : ml_smm_Q S B Sig ((1 + 1 / (S : ℝ)) • Sig)⁻¹ =
      (1 + 1 / (S : ℝ)) • (Bᵀ * Sig⁻¹ * B)⁻¹ := by
    unfold ml_smm_Q
    rw [ml_sandwich_inv B Sig hSigu hM hc.ne']
  refine ⟨h1, ?_⟩
  rw [h1, ml_smm_Q, ← smul_sub]
  exact (ml_sandwich_optimal B Sig W hSig hSigu hW hA hM).smul hc.le

/-- Miao, p. 403: as `S → ∞` the optimal SMM variance `(1 + 1/S)(BᵀΣ⁻¹B)⁻¹` tends to the GMM
variance `(BᵀΣ⁻¹B)⁻¹`. -/
theorem ml_smm_Q_tendsto {k : ℕ} (V : Matrix (Fin k) (Fin k) ℝ) :
    Tendsto (fun S : ℕ => (1 + 1 / (S : ℝ)) • V) atTop (𝓝 V) := by
  have h : Tendsto (fun S : ℕ => 1 + 1 / (S : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h2 : Tendsto (fun S : ℕ => (1 + 1 / (S : ℝ)) • V) atTop (𝓝 ((1 : ℝ) • V)) :=
    Tendsto.smul h (tendsto_const_nhds (x := V))
  rwa [one_smul] at h2

/-- The SMM estimator in the location model (`m(x) = x`, `xₜˢ(θ) = θ + ωₜˢ`):
`θ̂ = (1/T)∑ₜ xₜ − (1/(TS))∑ₜ∑ₛ ωₜˢ`. -/
noncomputable def ml_smmLocationEstimator {S T : ℕ} (x : Fin T → ℝ) (ω : Fin S → Fin T → ℝ) :
    ℝ :=
  (∑ t, x t) / T - (∑ t, ∑ s, ω s t) / (T * S)

/-- Miao, p. 401, in the location model `xₜˢ(θ) = θ + ωₜˢ` with `m(x) = x` and `W = 1`: the SMM
objective is `(∑ₜ (xₜ − (1/S)∑ₛ (θ + ωₜˢ)))² = T²(θ̂ − θ)²`, so `θ̂` is its unique minimiser. -/
theorem ml_smm_location_objective {S T : ℕ} (hS : 0 < S) (hT : 0 < T) (x : Fin T → ℝ)
    (ω : Fin S → Fin T → ℝ) (θ : ℝ) :
    (∑ t, (x t - (1 / (S : ℝ)) * ∑ s, (θ + ω s t))) ^ 2 =
      (T : ℝ) ^ 2 * (ml_smmLocationEstimator x ω - θ) ^ 2 ∧
      (∀ θ' : ℝ, (∑ t, (x t - (1 / (S : ℝ)) * ∑ s, (θ' + ω s t))) ^ 2 = 0 ↔
        θ' = ml_smmLocationEstimator x ω) := by
  have hS' : (S : ℝ) ≠ 0 := by positivity
  have hT' : (T : ℝ) ≠ 0 := by positivity
  have key : ∀ θ' : ℝ, ∑ t, (x t - (1 / (S : ℝ)) * ∑ s, (θ' + ω s t)) =
      T * (ml_smmLocationEstimator x ω - θ') := fun θ' => by
    unfold ml_smmLocationEstimator
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    field_simp
    ring
  refine ⟨by rw [key]; ring, fun θ' => ?_⟩
  rw [key, mul_pow, mul_eq_zero, pow_eq_zero_iff two_ne_zero, pow_eq_zero_iff two_ne_zero,
    sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hT'
    · exact h.symm
  · intro h; exact Or.inr h.symm

/-- **Consistency of SMM** (Miao, p. 402, `θ̂_ST → θ₀` as `T → ∞` for fixed `S`), in the
location model: data `xₜ = θ₀ + ωₜ` and simulation shocks `ωₜˢ`, each sequence i.i.d. (pairwise
independent and identically distributed) and integrable with the common mean `E ωₜˢ = E ωₜ`.
Then `θ̂_T = (1/T)∑_{t<T} xₜ − (1/(TS))∑_{t<T}∑ₛ ωₜˢ → θ₀` almost surely. -/
theorem ml_smm_location_consistent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : ℕ} (hS : 0 < S) (θ₀ : ℝ) (ω : ℕ → Ω → ℝ)
    (ωs : Fin S → ℕ → Ω → ℝ) (hint : Integrable (ω 0) P)
    (hindep : Pairwise fun i j => IndepFun (ω i) (ω j) P)
    (hident : ∀ i, IdentDistrib (ω i) (ω 0) P P) (hint' : ∀ s, Integrable (ωs s 0) P)
    (hindep' : ∀ s, Pairwise fun i j => IndepFun (ωs s i) (ωs s j) P)
    (hident' : ∀ s i, IdentDistrib (ωs s i) (ωs s 0) P P)
    (hmean : ∀ s, ∫ a, ωs s 0 a ∂P = ∫ a, ω 0 a ∂P) :
    ∀ᵐ a ∂P, Tendsto (fun T : ℕ => (∑ t ∈ Finset.range T, (θ₀ + ω t a)) / T -
      (∑ t ∈ Finset.range T, ∑ s, ωs s t a) / (T * S)) atTop (𝓝 θ₀) := by
  have h0 := strong_law_ae_real ω hint hindep hident
  have hs : ∀ᵐ a ∂P, ∀ s, Tendsto (fun T : ℕ => (∑ t ∈ Finset.range T, ωs s t a) / T) atTop
      (𝓝 (∫ a, ωs s 0 a ∂P)) :=
    ae_all_iff.2 fun s => strong_law_ae_real (ωs s) (hint' s) (hindep' s) (hident' s)
  filter_upwards [h0, hs] with a ha hsa
  simp only [hmean] at hsa
  have hS' : (S : ℝ) ≠ 0 := by positivity
  -- the estimator is `θ₀ + ω̄_T − (1/S)∑ₛ ω̄ˢ_T` for `T ≥ 1`
  have hrep : ∀ᶠ T : ℕ in atTop, (∑ t ∈ Finset.range T, (θ₀ + ω t a)) / T -
      (∑ t ∈ Finset.range T, ∑ s, ωs s t a) / (T * S) =
      θ₀ + (∑ t ∈ Finset.range T, ω t a) / T -
        (1 / (S : ℝ)) * ∑ s, (∑ t ∈ Finset.range T, ωs s t a) / T := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hT' : (T : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ T := by exact_mod_cast hT
      linarith
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_comm, ← Finset.sum_div]
    field_simp
  have hlim : Tendsto (fun T : ℕ => θ₀ + (∑ t ∈ Finset.range T, ω t a) / T -
      (1 / (S : ℝ)) * ∑ s, (∑ t ∈ Finset.range T, ωs s t a) / T) atTop
      (𝓝 (θ₀ + ∫ a, ω 0 a ∂P - (1 / (S : ℝ)) * ∑ _s : Fin S, ∫ a, ω 0 a ∂P)) :=
    ((tendsto_const_nhds.add ha).sub
      (tendsto_const_nhds.mul (tendsto_finsetSum _ fun s _ => hsa s)))
  have hval : θ₀ + ∫ a, ω 0 a ∂P - (1 / (S : ℝ)) * ∑ _s : Fin S, ∫ a, ω 0 a ∂P = θ₀ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [hval] at hlim
  exact hlim.congr' (hrep.mono fun T hT => hT.symm)

/-- **The variance of SMM** (Miao, p. 402) in the location model, exactly at every `T ≥ 1`: if
the shocks `ωₜ` (data) and `ωₜˢ` (simulations), `t < T`, are all independent with common
variance `σ²`, then `Var(√T(θ̂_T − θ₀)) = (1 + 1/S)σ²` (here `B = 1`, `W = 1`, `Σ = σ²`, so
`Q_S = (1 + 1/S)σ²`). The shocks are indexed by `(i, t)`, `i = none` for the data and
`i = some s` for simulation `s`. -/
theorem ml_smm_location_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S T : ℕ} (hS : 0 < S) (hT : 0 < T) (θ₀ : ℝ)
    (Y : Option (Fin S) × Fin T → Ω → ℝ) (hindep : iIndepFun Y P)
    (hY : ∀ i, MemLp (Y i) 2 P) (σ2 : ℝ) (hvar : ∀ i, Var[Y i; P] = σ2) :
    Var[fun a => Real.sqrt T * (ml_smmLocationEstimator (fun t => θ₀ + Y (none, t) a)
      (fun s t => Y (some s, t) a) - θ₀); P] = (1 + 1 / S) * σ2 := by
  have hS' : (S : ℝ) ≠ 0 := by positivity
  have hT' : (T : ℝ) ≠ 0 := by positivity
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (Nat.cast_nonneg T)
  let c : Option (Fin S) → ℝ := fun i => Option.elim i 1 fun _ => -(1 / (S : ℝ))
  let a : Option (Fin S) × Fin T → ℝ := fun p => c p.1 / Real.sqrt T
  have hfun : (fun a' => Real.sqrt T * (ml_smmLocationEstimator (fun t => θ₀ + Y (none, t) a')
      (fun s t => Y (some s, t) a') - θ₀)) = fun a' => ∑ p, a p * Y p a' := by
    funext a'
    unfold ml_smmLocationEstimator
    rw [Fintype.sum_prod_type, Fintype.sum_option]
    simp only [a, c, Option.elim_none, Option.elim_some, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_comm (f := fun (i : Fin S) (y : Fin T) =>
      -(1 / (S : ℝ)) / Real.sqrt T * Y (some i, y) a')]
    simp only [← Finset.mul_sum]
    set s := Real.sqrt (T : ℝ)
    rw [← hsq]
    field_simp
    ring
  rw [hfun, ml_variance_linear_comb Y a hindep hY, Fintype.sum_prod_type,
    Fintype.sum_option]
  simp only [a, c, Option.elim_none, Option.elim_some, hvar, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, div_pow, Real.sq_sqrt (Nat.cast_nonneg T)]
  field_simp

/-- **Asymptotic normality of SMM** (Miao, p. 402, `√T(θ̂_ST − θ₀) ⇒ N(0, Q_S)` for fixed `S`),
in the location model. Write `ξₜ = ωₜ − (1/S)∑ₛ ωₜˢ` (`ml_smmLocationEstimator` gives
`θ̂_T − θ₀ = (1/T)∑_{t<T} ξₜ`); if the `ξₜ` are i.i.d. and, at each date, the data shock and the
`S` simulation shocks are independent with mean `μ` and variance `σ²`, then
`√T(θ̂_T − θ₀) ⇒ N(0, (1 + 1/S)σ²)`. Mathlib's central limit theorem. -/
theorem ml_smm_location_asymptotic {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {S : ℕ} (hS : 0 < S) (θ₀ μ σ2 : ℝ) (ω : ℕ → Ω → ℝ) (ωs : Fin S → ℕ → Ω → ℝ)
    (Z : Ω' → ℝ) (hZ : HasLaw Z (gaussianReal 0 ((1 + 1 / (S : ℝ)) * σ2).toNNReal) P')
    (hξindep : iIndepFun (fun t a => ω t a - (1 / (S : ℝ)) * ∑ s, ωs s t a) P)
    (hξident : ∀ t, IdentDistrib (fun a => ω t a - (1 / (S : ℝ)) * ∑ s, ωs s t a)
      (fun a => ω 0 a - (1 / (S : ℝ)) * ∑ s, ωs s 0 a) P P)
    (h0indep : iIndepFun (fun i : Option (Fin S) => Option.elim i (ω 0) fun s => ωs s 0) P)
    (h0L2 : ∀ i : Option (Fin S), MemLp (Option.elim i (ω 0) fun s => ωs s 0) 2 P)
    (h0mean : ∀ i : Option (Fin S), ∫ a, (Option.elim i (ω 0) fun s => ωs s 0) a ∂P = μ)
    (h0var : ∀ i : Option (Fin S), Var[Option.elim i (ω 0) fun s => ωs s 0; P] = σ2) :
    TendstoInDistribution (fun (T : ℕ) a => Real.sqrt T *
      ((∑ t ∈ Finset.range T, (θ₀ + ω t a)) / T -
        (∑ t ∈ Finset.range T, ∑ s, ωs s t a) / (T * S) - θ₀)) atTop Z (fun _ => P) P' := by
  set ξ : ℕ → Ω → ℝ := fun t a => ω t a - (1 / (S : ℝ)) * ∑ s, ωs s t a with hξ
  have hS' : (S : ℝ) ≠ 0 := by positivity
  -- moments of `ξ₀`
  have hvar0 : Var[ξ 0; P] = (1 + 1 / (S : ℝ)) * σ2 := by
    have := ml_smm_variance_factor hS _ h0indep h0L2 σ2 h0var
    exact this
  have hL2 : MemLp (ξ 0) 2 P := by
    have h1 : MemLp (ω 0) 2 P := by simpa using h0L2 none
    have h2 : ∀ s, MemLp (ωs s 0) 2 P := fun s => by simpa using h0L2 (some s)
    exact h1.sub ((memLp_finsetSum _ fun s _ => h2 s).const_mul _)
  have hmean0 : P[ξ 0] = 0 := by
    have hω : ∫ a, ω 0 a ∂P = μ := by simpa using h0mean none
    have hωs : ∀ s, ∫ a, ωs s 0 a ∂P = μ := fun s => by simpa using h0mean (some s)
    have := ml_smm_moment_mean_zero (P := P) hS (ω 0) (fun s => ωs s 0)
      ((by simpa using h0L2 none : MemLp (ω 0) 2 P).integrable one_le_two)
      (fun s => (by simpa using h0L2 (some s) : MemLp (ωs s 0) 2 P).integrable one_le_two)
      (fun s => by rw [hωs s, hω])
    simpa [hξ] using this
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (P := P) (P' := P') (X := ξ)
    (Y := Z) (by rw [hvar0]; exact hZ) hL2 hξindep hξident
  rw [hmean0] at hclt
  simp only [mul_zero, sub_zero] at hclt
  have hfun : (fun (T : ℕ) a => Real.sqrt T * ((∑ t ∈ Finset.range T, (θ₀ + ω t a)) / T -
      (∑ t ∈ Finset.range T, ∑ s, ωs s t a) / (T * S) - θ₀)) =
      fun (T : ℕ) a => (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T, ξ t a := by
    funext T a
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · simp
    have hT' : (T : ℝ) ≠ 0 := by positivity
    have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 (by exact_mod_cast hT)
    have hsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (Nat.cast_nonneg T)
    simp only [hξ, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_comm (f := fun t s => ωs s t a)]
    set s := Real.sqrt (T : ℝ)
    rw [← hsq]
    field_simp
    ring
  rw [hfun]
  exact hclt

end Miao.StructuralEstimation

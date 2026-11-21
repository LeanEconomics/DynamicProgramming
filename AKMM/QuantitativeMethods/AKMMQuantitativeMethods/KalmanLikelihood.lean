/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.KFExamples

/-!
# The Kalman-filter likelihood of the linearised model

AKMM, §8.7, (8.21)–(8.22) and the likelihood, pp. 232–233, with footnote 9.

The linearised model `X̂ₜ₊₁ = AX̂ₜ + Bεₜ₊₁`, `Ŷₜ = CX̂ₜ` is Miao's time-invariant Kalman system
(`KFSystem.const`) with no controls, no measurement input and no measurement noise
(`kl_system`, `kl_model`). Miao's filter is proved as recursive linear projection from second
moments; the Gaussian reading of the book (conditional laws are normal) is not formalised.

* The innovation `Yₜ − CX_{t|t−1}` has mean zero and covariance `CP_{t|t−1}C'` (`kl_innovations`,
  `kl_Om`): the book's "mean `CX_{t|t−1}` and covariance `CP_{t|t−1}C'`".
* **The prediction-error decomposition**: the joint density is the product of the one-step
  conditional densities (`kl_chain_rule`), and the log of the Gaussian likelihood
  `∏ₜ N(Yₜ | CX_{t|t−1}, CP_{t|t−1}C')` is
  `−(n_YT/2)log 2π − ½Σ log|CPC'| − ½Σ aₜ'(CPC')⁻¹aₜ` (`kl_likelihood`, from Miao's
  Example 10.1.4).
* **Footnote 9**: for stable `A` the invariant initial covariance `P = APA' + BB'` exists and is
  unique (`fn_9`, from Miao's `kf_step1_cov`).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Matrix Miao.PartialInformation

variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y]

/-- **(8.21)–(8.22)** (AKMM, p. 233) as a Kalman system: transition `A`, shock loading `B`,
measurement `C`, no controls (`Fin 0`), no measurement input or noise, initial mean `x₀` and
covariance `P₀`. -/
def kl_system (A : Matrix X X ℝ) (B : Matrix X E ℝ) (C : Matrix Y X ℝ) (x0 : X → ℝ)
    (P0 : Matrix X X ℝ) : KFSystem X (Fin 0) Y E :=
  KFSystem.const A 0 B C 0 0 x0 P0

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- AKMM, (8.21)–(8.22): the book's model `X̂ₜ₊₁ = AX̂ₜ + Bεₜ₊₁`, `Ŷₜ = CX̂ₜ` gives the state and
measurement equations (10.1)–(10.2) of the Kalman system with zero controls and input. -/
theorem kl_model {Ω : Type*} {A : Matrix X X ℝ} {B : Matrix X E ℝ} {C : Matrix Y X ℝ}
    {x0 : X → ℝ} {P0 : Matrix X X ℝ} {x : ℕ → Ω → X → ℝ} {yv : ℕ → Ω → Y → ℝ}
    {ε : ℕ → Ω → E → ℝ} (hx : ∀ t, x (t + 1) = kf_app A (x t) + kf_app B (ε (t + 1)))
    (hy : ∀ t, yv t = kf_app C (x t)) :
    (∀ t, x (t + 1) = kf_app ((kl_system A B C x0 P0).A t) (x t) +
      kf_app ((kl_system A B C x0 P0).B t) (0 : Ω → Fin 0 → ℝ) +
      kf_app ((kl_system A B C x0 P0).C t) (ε (t + 1))) ∧
    (∀ t, yv t = kf_app ((kl_system A B C x0 P0).G t) (x t) + 0 +
      kf_app ((kl_system A B C x0 P0).D t) (ε t)) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [hx t]
    simp only [kl_system, KFSystem.const, kf_app_zero_mat, add_zero]
  · rw [hy t]
    simp only [kl_system, KFSystem.const, kf_app_zero_mat, add_zero]

omit [DecidableEq X] in
/-- AKMM, p. 233: with no measurement noise the innovation covariance (10.8) is
`Ω_{t|t−1} = CP_{t|t−1}C'`. -/
theorem kl_Om (A : Matrix X X ℝ) (B : Matrix X E ℝ) (C : Matrix Y X ℝ) (x0 : X → ℝ)
    (P0 : Matrix X X ℝ) [DecidableEq X] (t : ℕ) :
    (kl_system A B C x0 P0).Om t = C * (kl_system A B C x0 P0).Spred t * Cᵀ := by
  simp [KFSystem.Om, kf_Om, kl_system, KFSystem.const]

/-- **The predictive distribution of `Yₜ`** (AKMM, p. 233), second-moment version: under
(8.21)–(8.22) with white-noise shocks (`E εₜ = 0`, `E εₛεₜ' = δₛₜI`) uncorrelated with the
initial state, the innovation `Yₜ − CX_{t|t−1}` is square integrable with mean zero and
`E aₜaₜ' = CP_{t|t−1}C'`. -/
theorem kl_innovations {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [DecidableEq E] {A : Matrix X X ℝ} {B : Matrix X E ℝ}
    {C : Matrix Y X ℝ} {x0 : X → ℝ} {P0 : Matrix X X ℝ} {x : ℕ → Ω → X → ℝ}
    {yv : ℕ → Ω → Y → ℝ} {ε : ℕ → Ω → E → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app A (x t) + kf_app B (ε (t + 1)))
    (hy : ∀ t, yv t = kf_app C (x t))
    (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t)) (hm0 : kf_mean μ (x 0) = x0)
    (hmε : ∀ t, kf_mean μ (ε t) = 0)
    (hS0 : var_mom μ (x 0 - fun _ => x0) (x 0 - fun _ => x0) = P0)
    (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
    (h0ε : ∀ t, var_mom μ (x 0 - fun _ => x0) (ε t) = 0)
    (hΩ : ∀ t, IsUnit ((kl_system A B C x0 P0).Om t).det) (t : ℕ) :
    (kl_system A B C x0 P0).innov yv 0 0 t =
        yv t - kf_app C ((kl_system A B C x0 P0).xpred yv 0 0 t) ∧
      kf_L2 μ ((kl_system A B C x0 P0).innov yv 0 0 t) ∧
      kf_mean μ ((kl_system A B C x0 P0).innov yv 0 0 t) = 0 ∧
      var_mom μ ((kl_system A B C x0 P0).innov yv 0 0 t)
        ((kl_system A B C x0 P0).innov yv 0 0 t) =
        C * (kl_system A B C x0 P0).Spred t * Cᵀ := by
  obtain ⟨hx', hy'⟩ := kl_model (x0 := x0) (P0 := P0) hx hy
  have h1 := (kl_system A B C x0 P0).kf_innov_L2 μ (h := 0) (u := 0) hx' hy' hL0 hLε hm0 hmε
    hS0 hεε h0ε hΩ t
  have h2 := ((kl_system A B C x0 P0).eq_10_8 μ (h := 0) (u := 0) hx' hy' hL0 hLε hm0 hmε hS0
    hεε h0ε hΩ t).1
  refine ⟨?_, h1.1, h1.2, by rw [h2, kl_Om]⟩
  simp only [KFSystem.innov, Pi.zero_apply, sub_zero]
  rfl

/-- AKMM, p. 233: the density `N(Y | m, Σ)` of the multivariate normal at `Y`. -/
noncomputable def kl_normal (m : Y → ℝ) (S : Matrix Y Y ℝ) (yv : Y → ℝ) : ℝ :=
  kf_gaussDens S (yv - m)

/-- **The prediction-error decomposition** (AKMM, p. 233): if `pₜ > 0` is the joint density of
`(Y₁, …, Yₜ)` at the data, `p₀ = 1`, and `pₜ₊₁/pₜ` is the conditional density of `Yₜ₊₁` given
`Y₁, …, Yₜ`, the product of the conditional densities is the joint density. -/
theorem kl_chain_rule (p : ℕ → ℝ) (hp : ∀ t, 0 < p t) (h0 : p 0 = 1) (T : ℕ) :
    ∏ t ∈ Finset.range T, (p (t + 1) / p t) = p T := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [(hp T).ne']

omit [DecidableEq X] in
/-- **The likelihood** (AKMM, p. 233): for data `Y₁, …, Y_T`, predictions `X_{t|t−1}` and
covariances `P_{t|t−1}` with `|CPC'| > 0`, the log of
`∏_{t=1}^T N(Yₜ | CX_{t|t−1}, CP_{t|t−1}C')` is
`−(n_YT/2) log 2π − ½Σₜ log|CPₜC'| − ½Σₜ aₜ'(CPₜC')⁻¹aₜ` with `aₜ = Yₜ − CX_{t|t−1}`. -/
theorem kl_likelihood (C : Matrix Y X ℝ) (P : ℕ → Matrix X X ℝ) (xhat : ℕ → X → ℝ)
    (yv : ℕ → Y → ℝ) (T : ℕ) (hdet : ∀ t, 0 < (C * P t * Cᵀ).det) :
    Real.log (∏ t ∈ Finset.Icc 1 T, kl_normal (C *ᵥ xhat t) (C * P t * Cᵀ) (yv t)) =
      -(Fintype.card Y * T / 2) * Real.log (2 * Real.pi) -
        1 / 2 * ∑ t ∈ Finset.Icc 1 T, Real.log (C * P t * Cᵀ).det -
        1 / 2 * ∑ t ∈ Finset.Icc 1 T,
          (yv t - C *ᵥ xhat t) ⬝ᵥ ((C * P t * Cᵀ)⁻¹ *ᵥ (yv t - C *ᵥ xhat t)) := by
  have hpos : ∀ t, 0 < kl_normal (C *ᵥ xhat t) (C * P t * Cᵀ) (yv t) := by
    intro t
    unfold kl_normal kf_gaussDens
    have h2 : 0 < 2 * Real.pi := by positivity
    have := Real.rpow_pos_of_pos h2 (-(Fintype.card Y : ℝ) / 2)
    have := Real.rpow_pos_of_pos (hdet t) (-(1 : ℝ) / 2)
    positivity
  rw [Real.log_prod (fun t _ => (hpos t).ne')]
  exact (example_10_1_4 (fun t => C * P t * Cᵀ) (fun t => yv t - C *ᵥ xhat t) T hdet).2

omit [Fintype Y] [DecidableEq Y] in
/-- **Footnote 9** (AKMM, p. 233): drawing `X₁` from the invariant distribution. For stable `A`,
the invariant covariance `P_{1|0} = AP_{1|0}A' + BB'` exists and is unique (Miao's
`kf_step1_cov`), and the invariant mean is `X_{1|0} = 0` (`kf_step1_mean`). -/
theorem fn_9 {A : Matrix X X ℝ} (hA : ls_Stable A) (B : Matrix X E ℝ) :
    var_lyapSol A (B * Bᵀ) = A * var_lyapSol A (B * Bᵀ) * Aᵀ + B * Bᵀ ∧
      (∀ P : Matrix X X ℝ, P = A * P * Aᵀ + B * Bᵀ → P = var_lyapSol A (B * Bᵀ)) ∧
      ∀ m : X → ℝ, A *ᵥ m = m → m = 0 := by
  obtain ⟨h1, h2, -, -⟩ := kf_step1_cov hA (B * Bᵀ)
  exact ⟨h1, h2, fun m hm => kf_step1_mean hA hm⟩

end AKMM.QuantitativeMethods

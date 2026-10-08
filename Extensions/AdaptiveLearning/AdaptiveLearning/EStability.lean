/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdaptiveLearning.Cobweb

/-!
# E-stability and learnability of linear models

Evans and Honkapohja (2001); Marcet and Sargent (1989).

In a linear model whose actual law of motion given forecasts `θ` is `T(θ) = μ + Bθ`, the REE is a
fixed point `θ̄ = μ + Bθ̄`. It is **E-stable** when the ODE `θ̇ = T(θ) − θ` is stable at `θ̄`. We
use the quadratic Lyapunov form: there is a symmetric coercive `Q` with
`⟪Qx, Bx − x⟫ ≤ −κ‖x‖²` (`IsEStable`). For matrices this is implied by, and by Lyapunov's
theorem equivalent to, every eigenvalue of `B` having real part below `1`.

* `estable_learning`: steady-state learning `θ_{k+1} = θ_k + γ_k(μ + Bθ_k − θ_k + W_k)`
  converges to the REE almost surely when `B` is E-stable.
* `isEStable_of_inner_le`, `isEStable_of_opNorm_lt_one`: `⟪x, Bx⟫ ≤ λ‖x‖²` with `λ < 1`
  (in particular `‖B‖ < 1`) gives E-stability with `Q = I`.
* `isEStable_smul_iff`: `B = βI` (on a nontrivial space) is E-stable iff `β < 1`.
* `not_isEStable_of_eigen`: a real eigenvalue `λ ≥ 1` rules out E-stability, and
  `learning_diverges_of_eigen` shows that noiseless learning then moves away from the REE
  along the eigenvector when `λ > 1`.
* `ree_unique`, `ree_existsUnique`: E-stability makes the REE unique, and in finite dimensions it
  exists for every `μ`.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace DPExtensions.AdaptiveLearning

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- E-stability of the linear map `θ ↦ μ + Bθ`, in quadratic Lyapunov form. -/
def IsEStable (B : E →L[ℝ] E) : Prop :=
  ∃ (Q : E →L[ℝ] E) (m κ : ℝ), 0 < m ∧ 0 < κ ∧ (∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y)) ∧
    (∀ x, m * ‖x‖ ^ 2 ≤ inner ℝ (Q x) x) ∧ ∀ x, inner ℝ (Q x) (B x - x) ≤ -κ * ‖x‖ ^ 2

/-- `⟪x, Bx⟫ ≤ λ‖x‖²` with `λ < 1` gives E-stability with `Q = I`. -/
theorem isEStable_of_inner_le {B : E →L[ℝ] E} {lam : ℝ} (hlam : lam < 1)
    (h : ∀ x, inner ℝ x (B x) ≤ lam * ‖x‖ ^ 2) : IsEStable B := by
  refine ⟨ContinuousLinearMap.id ℝ E, 1, 1 - lam, one_pos, by linarith, fun x y => rfl,
    fun x => ?_, fun x => ?_⟩
  · simp
  · rw [ContinuousLinearMap.id_apply, inner_sub_right, real_inner_self_eq_norm_sq]
    linarith [h x]

/-- A contraction `‖B‖ < 1` is E-stable. -/
theorem isEStable_of_opNorm_lt_one {B : E →L[ℝ] E} (hB : ‖B‖ < 1) : IsEStable B :=
  isEStable_of_inner_le hB fun x =>
    calc inner ℝ x (B x) ≤ ‖x‖ * ‖B x‖ := real_inner_le_norm x (B x)
      _ ≤ ‖x‖ * (‖B‖ * ‖x‖) := mul_le_mul_of_nonneg_left (B.le_opNorm x) (norm_nonneg _)
      _ = ‖B‖ * ‖x‖ ^ 2 := by ring

/-- A real eigenvalue `λ ≥ 1` rules out E-stability. -/
theorem not_isEStable_of_eigen {B : E →L[ℝ] E} {lam : ℝ} (hlam : 1 ≤ lam) {v : E}
    (hv : B v = lam • v) (hv0 : v ≠ 0) : ¬ IsEStable B := by
  rintro ⟨Q, m, κ, hm, hκ, -, hQpos, hL⟩
  have h1 := hL v
  rw [hv, show lam • v - v = (lam - 1) • v by rw [sub_smul, one_smul],
    real_inner_smul_right] at h1
  have h2 := hQpos v
  have h3 : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hlam) ((mul_nonneg hm.le h3.le).trans h2)]

/-- `B = βI` on a nontrivial space is E-stable iff `β < 1`: the scalar condition of the cobweb
model. -/
theorem isEStable_smul_iff [Nontrivial E] (β : ℝ) :
    IsEStable (β • ContinuousLinearMap.id ℝ E) ↔ β < 1 := by
  constructor
  · intro h
    by_contra hβ
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    exact not_isEStable_of_eigen (not_lt.1 hβ) (v := v) (by simp) hv h
  · intro hβ
    refine isEStable_of_inner_le hβ fun x => ?_
    simp [real_inner_smul_right]

/-- E-stability makes the REE unique. -/
theorem ree_unique {B : E →L[ℝ] E} (hB : IsEStable B) {μ x y : E} (hx : μ + B x = x)
    (hy : μ + B y = y) : x = y := by
  obtain ⟨Q, m, κ, hm, hκ, -, -, hL⟩ := hB
  have e1 : B x - x = -μ := calc
    B x - x = B x - (μ + B x) := by rw [hx]
    _ = -μ := by abel
  have e2 : B y - y = -μ := calc
    B y - y = B y - (μ + B y) := by rw [hy]
    _ = -μ := by abel
  have hd : B (x - y) - (x - y) = 0 := by
    rw [map_sub, show B x - B y - (x - y) = (B x - x) - (B y - y) by abel, e1, e2, sub_self]
  have h1 := hL (x - y)
  rw [hd, inner_zero_right] at h1
  have h2 : ‖x - y‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖x - y‖]
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
    (le_antisymm h2 (sq_nonneg _))))

/-- In finite dimensions an E-stable model has a unique REE for every intercept `μ`. -/
theorem ree_existsUnique [FiniteDimensional ℝ E] {B : E →L[ℝ] E} (hB : IsEStable B) (μ : E) :
    ∃! x, μ + B x = x := by
  set D : E →ₗ[ℝ] E := LinearMap.id - (B : E →ₗ[ℝ] E)
  have hinj : Injective D := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (0 : E) + B x = x := by
      have : x - B x = 0 := hx
      rw [zero_add]
      exact (sub_eq_zero.1 this).symm
    have h2 : (0 : E) + B 0 = 0 := by simp
    exact ree_unique hB h1 h2
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.1 hinj) μ
  refine ⟨x, ?_, fun y hy => ree_unique hB hy ?_⟩
  · have : x - B x = μ := hx
    rw [← this]
    abel
  · have : x - B x = μ := hx
    rw [← this]
    abel

/-- **E-instability**: if `Bv = λv` with `λ > 1`, noiseless learning started at `θ̄ + v` with
`∑ γ_k = ∞` moves away from the REE: `θ_k − θ̄ = ∏_{s<k}(1 + γ_s(λ − 1)) v`, unbounded. -/
theorem learning_diverges_of_eigen {B : E →L[ℝ] E} {μ θbar : E} (hfix : μ + B θbar = θbar)
    {lam : ℝ} (hlam : 1 < lam) {v : E} (hv : B v = lam • v) (hv0 : v ≠ 0) {γ : ℕ → ℝ}
    (hγ0 : ∀ k, 0 ≤ γ k) (hdiv : ¬ Summable γ) {θ : ℕ → E} (hθ0 : θ 0 = θbar + v)
    (hrec : ∀ k, θ (k + 1) = θ k + γ k • (μ + B (θ k) - θ k)) :
    Tendsto (fun k => ‖θ k - θbar‖) atTop atTop := by
  have hform : ∀ k, θ k - θbar = (∏ s ∈ Finset.range k, (1 + γ s * (lam - 1))) • v := by
    intro k
    induction k with
    | zero => simp [hθ0]
    | succ k ih =>
      have e1 : θ k = θbar + (∏ s ∈ Finset.range k, (1 + γ s * (lam - 1))) • v := by
        rw [← ih]
        abel
      rw [hrec, Finset.prod_range_succ, e1, map_add, map_smul, hv]
      have e2 : μ + (B θbar + (∏ s ∈ Finset.range k, (1 + γ s * (lam - 1))) • lam • v) -
          (θbar + (∏ s ∈ Finset.range k, (1 + γ s * (lam - 1))) • v) =
          ((∏ s ∈ Finset.range k, (1 + γ s * (lam - 1))) * (lam - 1)) • v := by
        rw [← add_assoc, hfix, smul_smul, mul_sub, mul_one, sub_smul]
        abel
      have e3 : ∀ a b c : E, a + b + c - a = b + c := fun a b c => by abel
      rw [e2, smul_smul, e3, ← add_smul]
      congr 1
      ring
  have hx : ∀ s, 0 ≤ γ s * (lam - 1) := fun s => mul_nonneg (hγ0 s) (by linarith)
  have hS : Tendsto (fun t => ∑ s ∈ Finset.range t, γ s * (lam - 1)) atTop atTop := by
    have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hγ0).1 hdiv
    have e : (fun t => ∑ s ∈ Finset.range t, γ s * (lam - 1)) =
        fun t => (∑ s ∈ Finset.range t, γ s) * (lam - 1) :=
      funext fun t => (Finset.sum_mul _ _ _).symm
    rw [e]
    exact h.atTop_mul_const (by linarith)
  have hprod : Tendsto (fun t => ∏ s ∈ Finset.range t, (1 + γ s * (lam - 1))) atTop atTop :=
    tendsto_atTop_mono (fun t => (one_add_sum_le_prod hx t).trans' (by linarith))
      (tendsto_atTop_add_const_left _ 1 hS)
  have e : (fun k => ‖θ k - θbar‖) =
      fun k => (∏ s ∈ Finset.range k, (1 + γ s * (lam - 1))) * ‖v‖ := by
    funext k
    rw [hform, norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg fun s _ => by
      linarith [hx s])]
  rw [e]
  exact hprod.atTop_mul_const (norm_pos_iff.2 hv0)

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℕ m0}

/-- **Learnability of E-stable REE** (Marcet and Sargent, 1989; Evans and Honkapohja,
2001, for steady-state learning): if `B` is E-stable and `θ̄ = μ + Bθ̄`, steady-state learning
`θ_{k+1} = θ_k + γ_k(μ + Bθ_k − θ_k + W_k)` converges to `θ̄` almost surely under the
Robbins–Monro conditions on `γ` and martingale-difference noise with
`𝔼[‖W_k‖² | ℱ_k] ≤ C(1 + ‖θ_k‖²)`. -/
theorem estable_learning [CompleteSpace E] {B : E →L[ℝ] E} (hB : IsEStable B) {μ θbar : E}
    (hfix : μ + B θbar = θbar) {γ : ℕ → ℝ} (hγ0 : ∀ k, 0 ≤ γ k) (hdiv : ¬ Summable γ)
    (hsq : Summable fun k => γ k ^ 2) {θ W : ℕ → Ω → E}
    (hrec : ∀ k ω, θ (k + 1) ω = θ k ω + γ k • (μ + B (θ k ω) - θ k ω + W k ω))
    (hθ0m : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0 : MemLp (θ 0) 2 P)
    (hWm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (W k)) (hW2 : ∀ k, MemLp (W k) 2 P)
    (hW0 : ∀ k, P[W k | ℱ k] =ᵐ[P] 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k, P[fun ω => ‖W k ω‖ ^ 2 | ℱ k] ≤ᵐ[P] fun ω => C * (1 + ‖θ k ω‖ ^ 2)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => θ k ω) atTop (𝓝 θbar) := by
  obtain ⟨Q, m, κ, hm, hκ, hQsym, hQpos, hL⟩ := hB
  have hh : ∀ x, μ + B x - x = B (x - θbar) - (x - θbar) := fun x => by
    rw [map_sub, eq_sub_of_add_eq hfix]
    abel
  refine sa_lyapunov (ℱ := ℱ) (h := fun x => μ + B x - x) (by fun_prop) hQsym hm hκ hQpos
    (fun x => ?_) (L := ‖B‖ + 1) (fun x => ?_) hγ0 hdiv hsq (W := W) (fun k ω => ?_) hθ0m hθ0
    hWm hW2 hW0 hC0 hC
  · rw [hh]
    exact hL _
  · rw [hh, add_mul, one_mul]
    exact (norm_sub_le _ _).trans (add_le_add (B.le_opNorm _) le_rfl)
  · exact hrec k ω

end DPExtensions.AdaptiveLearning

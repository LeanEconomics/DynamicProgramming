/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TemporalDifference.ErrorBound
import TemporalDifference.LyapunovSA

/-!
# Convergence of TD(0) with linear features

Sutton (1988); Tsitsiklis and Van Roy (1997), here with i.i.d. sampling of transitions.

At step `k` a transition `(X_k, X'_k)` is drawn — `X_k` from the stationary distribution `d`
and `X'_k` from `P(X_k, ·)` — independently of the past given `ℱ_k`, and
`θ_{k+1} = θ_k + α_k(r(X_k) + βV_θ(X'_k) − V_θ(X_k))φ(X_k)`.

* `meanField_eq_sum`: the expected increment is the mean field `h(θ)`.
* `td_converges`: if `d > 0`, the features span `E`, `0 ≤ β < 1`, and `∑ α_k = ∞`,
  `∑ α_k² < ∞`, then `θ_k → θ*` almost surely, where `θ*` is the TD fixed point; with
  `tvr_bound`, the limit approximates the value function within `‖ΠV − V‖_d / √(1 − β²)`.

The proof applies `sa_lyapunov` with `Q = I`: the mean field is strongly monotone
(`meanField_lyapunov`) and Lipschitz, and the noise is a martingale difference whose conditional
variance grows at most quadratically in `θ_k`.
-/

open Finset Filter Topology MeasureTheory ProbabilityTheory

namespace DPExtensions.TemporalDifference

variable {X : Type*} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The TD(0) increment after the transition `x → x'`. -/
noncomputable def tdStep (r : X → ℝ) (β : ℝ) (φ : X → E) (θ : E) (x x' : X) : E :=
  (r x + β * vθ φ θ x' - vθ φ θ x) • φ x

/-- **The expected TD increment is the mean field.** -/
theorem meanField_eq_sum {P : X → X → ℝ} (hP1 : ∀ x, ∑ y, P x y = 1) (d r : X → ℝ) (β : ℝ)
    (φ : X → E) (θ : E) :
    meanField P d r β φ θ = ∑ p : X × X, (d p.1 * P p.1 p.2) • tdStep r β φ θ p.1 p.2 := by
  rw [Fintype.sum_prod_type]
  simp only [meanField, tdStep, smul_smul]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_smul]
  congr 1
  have h : ∀ x', d x * P x x' * (r x + β * vθ φ θ x' - vθ φ θ x) =
      (d x * (r x - vθ φ θ x)) * P x x' + (d x * β) * (P x x' * vθ φ θ x') := fun x' => by ring
  rw [sum_congr rfl fun x' _ => h x', sum_add_distrib, ← mul_sum, ← mul_sum, hP1 x]
  simp only [applyP]
  ring

omit [Fintype X] in
theorem continuous_tdStep (r : X → ℝ) (β : ℝ) (φ : X → E) (x x' : X) :
    Continuous fun θ => tdStep r β φ θ x x' := by
  unfold tdStep vθ
  fun_prop

theorem continuous_meanField (P : X → X → ℝ) (d r : X → ℝ) (β : ℝ) (φ : X → E) :
    Continuous (meanField P d r β φ) := by
  unfold meanField applyP vθ
  fun_prop

theorem norm_tdStep_le {β : ℝ} (hβ0 : 0 ≤ β) (r : X → ℝ) (φ : X → E) (θ : E) (x x' : X) :
    ‖tdStep r β φ θ x x'‖ ≤
      (∑ y, ‖φ y‖) * (∑ y, |r y|) + (∑ y, ‖φ y‖) * ((β + 1) * (∑ y, ‖φ y‖)) * ‖θ‖ := by
  set Φ := ∑ y, ‖φ y‖
  have hφ : ∀ y, ‖φ y‖ ≤ Φ := fun y =>
    single_le_sum (f := fun y => ‖φ y‖) (fun y _ => norm_nonneg _) (mem_univ y)
  have hr : |r x| ≤ ∑ y, |r y| :=
    single_le_sum (f := fun y => |r y|) (fun y _ => abs_nonneg _) (mem_univ x)
  have hu : ∀ y, |vθ φ θ y| ≤ Φ * ‖θ‖ := fun y =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hφ y) (norm_nonneg _))
  have hΦ : 0 ≤ Φ := sum_nonneg fun y _ => norm_nonneg _
  have hc : |r x + β * vθ φ θ x' - vθ φ θ x| ≤ ∑ y, |r y| + (β + 1) * (Φ * ‖θ‖) := by
    have h1 := abs_add_le (r x + β * vθ φ θ x') (-vθ φ θ x)
    have h2 := abs_add_le (r x) (β * vθ φ θ x')
    rw [abs_mul, abs_of_nonneg hβ0] at h2
    rw [abs_neg, ← sub_eq_add_neg] at h1
    nlinarith [mul_le_mul_of_nonneg_left (hu x') hβ0, hu x]
  rw [tdStep, norm_smul, Real.norm_eq_abs]
  calc |r x + β * vθ φ θ x' - vθ φ θ x| * ‖φ x‖
      ≤ (∑ y, |r y| + (β + 1) * (Φ * ‖θ‖)) * Φ :=
        mul_le_mul hc (hφ x) (norm_nonneg _) (by positivity)
    _ = Φ * (∑ y, |r y|) + Φ * ((β + 1) * Φ) * ‖θ‖ := by ring

variable [DecidableEq X] [FiniteDimensional ℝ E]
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}

/-- **TD(0) converges** almost surely to the TD fixed point. -/
theorem td_converges {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {d : X → ℝ} (hd : ∀ x, 0 < d x) (hstat : ∀ y, ∑ x, d x * P x y = d y) (r : X → ℝ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {φ : X → E}
    (hspan : ∀ z, (∀ x, inner ℝ (φ x) z = 0) → z = 0) {θs : E}
    (hθs : meanField P d r β φ θs = 0) {α : ℕ → ℝ} (hα0 : ∀ k, 0 ≤ α k)
    (hdiv : ¬ Summable α) (hsq : Summable fun k => α k ^ 2) {θ : ℕ → Ω → E} {θ0 : E}
    {S : ℕ → Ω → X × X} (hθ0 : ∀ ω, θ 0 ω = θ0)
    (hSm : ∀ k p, MeasurableSet[ℱ (k + 1)] {ω | S k ω = p})
    (hlaw : ∀ k p, μ[fun ω => if S k ω = p then (1 : ℝ) else 0 | ℱ k] =ᵐ[μ]
      fun _ => d p.1 * P p.1 p.2)
    (hrec : ∀ k ω, θ (k + 1) ω = θ k ω + α k • tdStep r β φ (θ k ω) (S k ω).1 (S k ω).2) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => θ k ω) atTop (𝓝 θs) := by
  have hd0 : ∀ x, 0 ≤ d x := fun x => (hd x).le
  obtain ⟨m, hm, hgram⟩ := exists_gram_lower hd hspan
  set Φ := ∑ y, ‖φ y‖
  set Rr := ∑ y, |r y|
  have hΦ : 0 ≤ Φ := sum_nonneg fun y _ => norm_nonneg _
  have hRr : 0 ≤ Rr := sum_nonneg fun y _ => abs_nonneg _
  set L := (β + 1) * Φ * Φ * ∑ x, d x
  have hL0 : 0 ≤ L := mul_nonneg (by positivity) (sum_nonneg fun x _ => hd0 x)
  set h := meanField P d r β φ with hhdef
  have hlin : ∀ x, ‖h x‖ ≤ L * ‖x - θs‖ := fun x => by
    have := meanField_lipschitz hP0 hP1 hd0 r hβ0 φ x θs
    rw [← hhdef, hθs, sub_zero] at this
    exact this
  have hdrift : ∀ x, inner ℝ ((ContinuousLinearMap.id ℝ E) (x - θs)) (h x) ≤
      -((1 - β) * m) * ‖x - θs‖ ^ 2 := fun x => by
    have h1 := meanField_lyapunov hP0 hP1 hd0 hstat r hβ0 φ x θs
    rw [← hhdef, hθs, sub_zero] at h1
    have h2 := mul_le_mul_of_nonneg_left (hgram (x - θs)) (sub_pos.2 hβ1).le
    rw [ContinuousLinearMap.id_apply]
    nlinarith
  -- the noise
  set g : ℕ → X × X → Ω → E := fun k p ω => tdStep r β φ (θ k ω) p.1 p.2 with hgdef
  set ind : ℕ → X × X → Ω → ℝ := fun k p ω => if S k ω = p then 1 else 0 with hinddef
  have hrep : ∀ k ω, tdStep r β φ (θ k ω) (S k ω).1 (S k ω).2 = ∑ p, ind k p ω • g k p ω :=
    fun k ω => by
      simp only [hinddef, hgdef, ite_smul, one_smul, zero_smul]
      rw [sum_ite_eq]
      simp
  set W : ℕ → Ω → E := fun k ω => tdStep r β φ (θ k ω) (S k ω).1 (S k ω).2 - h (θ k ω)
    with hWdef
  have hrec' : ∀ k ω, θ (k + 1) ω = θ k ω + α k • (h (θ k ω) + W k ω) := fun k ω => by
    rw [hrec]
    simp only [hWdef, add_sub_cancel]
  -- measurability
  have hindm : ∀ k p, StronglyMeasurable[ℱ (k + 1)] (ind k p) := fun k p =>
    (Measurable.ite (hSm k p) measurable_const measurable_const).stronglyMeasurable
  have hθm : ∀ k, StronglyMeasurable[ℱ k] (θ k) := by
    intro k
    induction k with
    | zero =>
      rw [show θ 0 = fun _ => θ0 from funext hθ0]
      exact stronglyMeasurable_const
    | succ k ih =>
      have ih' := ih.mono (ℱ.mono k.le_succ)
      have e : θ (k + 1) = fun ω => θ k ω + α k • ∑ p, ind k p ω • g k p ω :=
        funext fun ω => by rw [hrec, hrep]
      rw [e]
      exact ih'.add ((Finset.stronglyMeasurable_fun_sum _ fun p _ => (hindm k p).smul
        ((continuous_tdStep r β φ p.1 p.2).comp_stronglyMeasurable ih')).const_smul (α k))
  have hgm : ∀ k p, StronglyMeasurable[ℱ k] (g k p) := fun k p =>
    (continuous_tdStep r β φ p.1 p.2).comp_stronglyMeasurable (hθm k)
  have hstepm : ∀ k, StronglyMeasurable[ℱ (k + 1)]
      fun ω => tdStep r β φ (θ k ω) (S k ω).1 (S k ω).2 := fun k => by
    rw [show (fun ω => tdStep r β φ (θ k ω) (S k ω).1 (S k ω).2) =
      fun ω => ∑ p, ind k p ω • g k p ω from funext (hrep k)]
    exact Finset.stronglyMeasurable_fun_sum _ fun p _ =>
      (hindm k p).smul ((hgm k p).mono (ℱ.mono k.le_succ))
  have hhm : ∀ k, StronglyMeasurable[ℱ k] fun ω => h (θ k ω) := fun k =>
    (continuous_meanField P d r β φ).comp_stronglyMeasurable (hθm k)
  have hWm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (W k) := fun k =>
    (hstepm k).sub ((hhm k).mono (ℱ.mono k.le_succ))
  -- bounds
  have hstepb : ∀ (θ' : E) (x x' : X),
      ‖tdStep r β φ θ' x x'‖ ≤ Φ * Rr + Φ * ((β + 1) * Φ) * ‖θ'‖ :=
    fun θ' x x' => norm_tdStep_le hβ0 r φ θ' x x'
  have hhb : ∀ x, ‖h x‖ ≤ L * ‖θs‖ + L * ‖x‖ := fun x => by
    have h1 := hlin x
    have h2 := mul_le_mul_of_nonneg_left (norm_sub_le x θs) hL0
    linarith
  set c0 := Φ * Rr + L * ‖θs‖
  set c1 := Φ * ((β + 1) * Φ) + L
  have hWb : ∀ k ω, ‖W k ω‖ ≤ c0 + c1 * ‖θ k ω‖ := fun k ω => by
    refine (norm_sub_le _ _).trans ?_
    have h1 := hstepb (θ k ω) (S k ω).1 (S k ω).2
    have h2 := hhb (θ k ω)
    simp only [c0, c1]
    linarith
  -- square integrability
  have hθL : ∀ k, MemLp (θ k) 2 μ := by
    intro k
    induction k with
    | zero =>
      rw [show θ 0 = fun _ => θ0 from funext hθ0]
      exact memLp_const θ0
    | succ k ih =>
      have hstepL : MemLp (fun ω => tdStep r β φ (θ k ω) (S k ω).1 (S k ω).2) 2 μ :=
        ((memLp_const (Φ * Rr)).add (ih.norm.const_mul (Φ * ((β + 1) * Φ)))).mono'
          ((hstepm k).mono (ℱ.le (k + 1))).aestronglyMeasurable
          (Eventually.of_forall fun ω => by
            simp only [Pi.add_apply]
            exact hstepb _ _ _)
      rw [show θ (k + 1) = fun ω => θ k ω + α k • tdStep r β φ (θ k ω) (S k ω).1 (S k ω).2
        from funext (hrec k)]
      exact ih.add (hstepL.const_smul (α k))
  have hW2 : ∀ k, MemLp (W k) 2 μ := fun k =>
    ((memLp_const c0).add ((hθL k).norm.const_mul c1)).mono'
      ((hWm k).mono (ℱ.le (k + 1))).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        simp only [Pi.add_apply]
        exact hWb k ω)
  -- the noise has conditional mean zero
  have hW0 : ∀ k, μ[W k | ℱ k] =ᵐ[μ] 0 := by
    intro k
    have hgL : ∀ p, MemLp (g k p) 2 μ := fun p =>
      ((memLp_const (Φ * Rr)).add ((hθL k).norm.const_mul (Φ * ((β + 1) * Φ)))).mono'
        ((hgm k p).mono (ℱ.le k)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          simp only [Pi.add_apply]
          exact hstepb _ _ _)
    have hindI : ∀ p, Integrable (ind k p) μ := fun p =>
      Integrable.of_bound ((hindm k p).mono (ℱ.le (k + 1))).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by
          simp only [hinddef]
          split_ifs <;> norm_num)
    have hprodI : ∀ p, Integrable (ind k p • g k p) μ := fun p =>
      ((hgL p).integrable one_le_two).bdd_smul 1
        ((hindm k p).mono (ℱ.le (k + 1))).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          simp only [hinddef]
          split_ifs <;> norm_num)
    have hhI : Integrable (fun ω => h (θ k ω)) μ :=
      (((memLp_const (L * ‖θs‖)).add ((hθL k).norm.const_mul L)).mono'
        ((hhm k).mono (ℱ.le k)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          simp only [Pi.add_apply]
          exact hhb _)).integrable one_le_two
    have hsum : W k = (∑ p, ind k p • g k p) - fun ω => h (θ k ω) := funext fun ω => by
      simp only [hWdef, Pi.sub_apply, Finset.sum_apply, hrep]
      rfl
    rw [hsum]
    have e1 := condExp_sub (integrable_finsetSum' univ fun p _ => hprodI p) hhI (ℱ k)
    have e2 := condExp_finsetSum (μ := μ) (s := univ) (fun p _ => hprodI p) (ℱ k)
    have e3 : ∀ p, μ[ind k p • g k p | ℱ k] =ᵐ[μ] μ[ind k p | ℱ k] • g k p := fun p =>
      condExp_smul_of_aestronglyMeasurable_right (hindI p) (hprodI p)
        (hgm k p).aestronglyMeasurable
    have e4 := condExp_of_stronglyMeasurable (ℱ.le k) (hhm k) hhI
    filter_upwards [e1, e2, ae_all_iff.2 e3, ae_all_iff.2 (hlaw k)] with ω h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, e4, Finset.sum_apply, Pi.zero_apply]
    have e5 : ∀ p, (μ[ind k p • g k p | ℱ k]) ω = (d p.1 * P p.1 p.2) • g k p ω := fun p => by
      rw [h3 p, Pi.smul_apply', h4 p]
    rw [sum_congr rfl fun p _ => e5 p, hhdef]
    dsimp only
    rw [meanField_eq_sum hP1 d r β φ (θ k ω)]
    exact sub_self _
  -- the conditional variance grows at most quadratically
  set C := 2 * (c0 ^ 2 + c1 ^ 2)
  have hC0 : 0 ≤ C := by positivity
  have hC : ∀ k, μ[fun ω => ‖W k ω‖ ^ 2 | ℱ k] ≤ᵐ[μ] fun ω => C * (1 + ‖θ k ω‖ ^ 2) := by
    intro k
    have hpt : ∀ ω, ‖W k ω‖ ^ 2 ≤ C * (1 + ‖θ k ω‖ ^ 2) := fun ω => by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hWb k ω) 2
      have hc0 : 0 ≤ c0 := by positivity
      have hc1 : 0 ≤ c1 := by positivity
      nlinarith [sq_nonneg (c0 - c1 * ‖θ k ω‖), sq_nonneg ‖θ k ω‖, sq_nonneg c0, sq_nonneg c1,
        mul_nonneg (sq_nonneg c0) (sq_nonneg ‖θ k ω‖)]
    have hWsqI : Integrable (fun ω => ‖W k ω‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm (hW2 k).aestronglyMeasurable).1 (hW2 k)
    have hθsqI : Integrable (fun ω => ‖θ k ω‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm (hθL k).aestronglyMeasurable).1 (hθL k)
    have hbI : Integrable (fun ω => C * (1 + ‖θ k ω‖ ^ 2)) μ :=
      ((integrable_const 1).add hθsqI).const_mul C
    have hbm : StronglyMeasurable[ℱ k] fun ω => C * (1 + ‖θ k ω‖ ^ 2) :=
      stronglyMeasurable_const.mul (stronglyMeasurable_const.add ((hθm k).norm.pow 2))
    have h1 := condExp_mono (m := ℱ k) hWsqI hbI (Eventually.of_forall hpt)
    rwa [condExp_of_stronglyMeasurable (ℱ.le k) hbm hbI] at h1
  exact sa_lyapunov (ℱ := ℱ) (h := h) (continuous_meanField P d r β φ)
    (Q := ContinuousLinearMap.id ℝ E) (fun x y => rfl) (m := 1) (κ := (1 - β) * m) one_pos
    (mul_pos (sub_pos.2 hβ1) hm) (fun x => by simp) hdrift hlin
    hα0 hdiv hsq hrec' (hθm 0) (hθL 0) hWm hW2 hW0 hC0 hC

end DPExtensions.TemporalDifference

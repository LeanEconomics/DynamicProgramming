import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
/-!
# The Robbins–Siegmund lemma

Robbins and Siegmund (1971), "A convergence theorem for non negative almost supermartingales
and some applications". Copied from the `Extensions/AdaptiveLearning` project.

* `robbins_siegmund`: a nonnegative adapted process with
  `𝔼[Y_{k+1} | ℱ_k] ≤ (1 + a_k)Y_k + b_k − c_k`, `∑ a_k, ∑ b_k < ∞`, converges almost surely and
  `∑ c_k < ∞` almost surely, by the martingale convergence theorem applied to a rescaled
  supermartingale.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace DPExtensions.TemporalDifference

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℕ m0}

/-- **Robbins–Siegmund lemma**: if `Y, c ≥ 0` are adapted and integrable, `a, b ≥ 0` are summable
and `𝔼[Y_{k+1} | ℱ_k] ≤ (1 + a_k)Y_k + b_k − c_k`, then almost surely `Y_k` converges and
`∑ c_k < ∞`. -/
theorem robbins_siegmund {Y c : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (hY : StronglyAdapted ℱ Y) (hc : StronglyAdapted ℱ c)
    (hYi : ∀ k, Integrable (Y k) P) (hci : ∀ k, Integrable (c k) P)
    (hY0 : ∀ k ω, 0 ≤ Y k ω) (hc0 : ∀ k ω, 0 ≤ c k ω) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hsa : Summable a) (hsb : Summable b)
    (hstep : ∀ k, P[Y (k + 1) | ℱ k] ≤ᵐ[P] fun ω => (1 + a k) * Y k ω + b k - c k ω) :
    ∀ᵐ ω ∂P, (∃ L, Tendsto (fun k => Y k ω) atTop (𝓝 L)) ∧ Summable fun k => c k ω := by
  -- the products `π_k = ∏_{j<k} (1 + a_j)`
  set π : ℕ → ℝ := fun k => ∏ j ∈ Finset.range k, (1 + a j) with hπdef
  have hπsucc : ∀ k, π (k + 1) = π k * (1 + a k) := fun k => Finset.prod_range_succ _ _
  have hπ1 : ∀ k, 1 ≤ π k := by
    intro k
    induction k with
    | zero => simp [hπdef]
    | succ k ih =>
      rw [hπsucc]
      nlinarith [ha k]
  have hπpos : ∀ k, 0 < π k := fun k => one_pos.trans_le (hπ1 k)
  have hπmono : Monotone π := monotone_nat_of_le_succ fun k => by
    rw [hπsucc]
    nlinarith [ha k, hπ1 k]
  have hπbdd : ∀ k, π k ≤ Real.exp (∑' j, a j) := by
    have h : ∀ k, π k ≤ Real.exp (∑ j ∈ Finset.range k, a j) := by
      intro k
      induction k with
      | zero => simp [hπdef]
      | succ k ih =>
        rw [hπsucc, Finset.sum_range_succ, Real.exp_add]
        have h1 : 1 + a k ≤ Real.exp (a k) := by linarith [Real.add_one_le_exp (a k)]
        exact mul_le_mul ih h1 (by linarith [ha k]) (Real.exp_pos _).le
    exact fun k => (h k).trans (Real.exp_le_exp.2 (hsa.sum_le_tsum _ fun j _ => ha j))
  -- partial sums
  set S : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range k, c j ω with hSdef
  set Bs : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, b j / π (j + 1) with hBsdef
  have hSm : ∀ k i, k ≤ i → StronglyMeasurable[ℱ i] (S k) := fun k i hki => by
    have h := Finset.stronglyMeasurable_sum (f := c) (Finset.range k) fun j hj =>
      (hc j).mono (ℱ.mono (show j ≤ i by have := Finset.mem_range.1 hj; omega))
    convert h using 1
    funext ω
    simp [hSdef, Finset.sum_apply]
  have hSm' : ∀ k, StronglyMeasurable[ℱ k] (S (k + 1)) := fun k => by
    have h := Finset.stronglyMeasurable_sum (f := c) (Finset.range (k + 1)) fun j hj =>
      (hc j).mono (ℱ.mono (show j ≤ k by have := Finset.mem_range.1 hj; omega))
    convert h using 1
    funext ω
    simp [hSdef, Finset.sum_apply]
  have hSi : ∀ k, Integrable (S k) P := fun k => integrable_finsetSum _ fun j _ => hci j
  have hS0 : ∀ k ω, 0 ≤ S k ω := fun k ω => Finset.sum_nonneg fun j _ => hc0 j ω
  set Btot := ∑' j, b j
  have hB0 : 0 ≤ Btot := tsum_nonneg hb
  have hBs : ∀ k, Bs k ≤ Btot := fun k =>
    (Finset.sum_le_sum fun j _ => div_le_self (hb j) (hπ1 (j + 1))).trans
      (hsb.sum_le_tsum _ fun j _ => hb j)
  -- the supermartingale `Z_k = π_k⁻¹(Y_k + S_k) − B_k`
  set Z : ℕ → Ω → ℝ := fun k ω => (π k)⁻¹ * (Y k ω + S k ω) - Bs k with hZdef
  have hZad : StronglyAdapted ℱ Z := fun k =>
    (stronglyMeasurable_const.mul ((hY k).add (hSm k k le_rfl))).sub stronglyMeasurable_const
  have hZi : ∀ k, Integrable (Z k) P := fun k =>
    (((hYi k).add (hSi k)).const_mul _).sub (integrable_const _)
  have hsup : Supermartingale Z ℱ P := supermartingale_nat hZad hZi fun k => by
    set R : Ω → ℝ := fun ω => (π (k + 1))⁻¹ * S (k + 1) ω - Bs (k + 1)
    have hRm : StronglyMeasurable[ℱ k] R :=
      (stronglyMeasurable_const.mul (hSm' k)).sub stronglyMeasurable_const
    have hRi : Integrable R P := ((hSi (k + 1)).const_mul _).sub (integrable_const _)
    have hsplit : Z (k + 1) = (π (k + 1))⁻¹ • Y (k + 1) + R := by
      funext ω
      simp only [hZdef, R, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsplit]
    filter_upwards [condExp_add ((hYi (k + 1)).smul ((π (k + 1))⁻¹)) hRi (ℱ k),
      condExp_smul ((π (k + 1))⁻¹) (Y (k + 1)) (ℱ k), hstep k] with ω h1 h2 h3
    rw [h1, Pi.add_apply, h2, condExp_of_stronglyMeasurable (ℱ.le k) hRm hRi, Pi.smul_apply,
      smul_eq_mul]
    have hpk := hπpos k
    have ha1 : 0 < 1 + a k := by linarith [ha k]
    have hS1 : S (k + 1) ω = S k ω + c k ω := Finset.sum_range_succ _ _
    have hB1 : Bs (k + 1) = Bs k + b k / π (k + 1) := Finset.sum_range_succ _ _
    have hinv : (π (k + 1))⁻¹ * (1 + a k) = (π k)⁻¹ := by
      rw [hπsucc]
      field_simp
    have hinvle : (π (k + 1))⁻¹ ≤ (π k)⁻¹ := inv_anti₀ hpk (hπmono (Nat.le_succ k))
    simp only [R, hS1, hB1, hZdef]
    calc (π (k + 1))⁻¹ * P[Y (k + 1)|ℱ k] ω +
          ((π (k + 1))⁻¹ * (S k ω + c k ω) - (Bs k + b k / π (k + 1)))
        ≤ (π (k + 1))⁻¹ * ((1 + a k) * Y k ω + b k - c k ω) +
          ((π (k + 1))⁻¹ * (S k ω + c k ω) - (Bs k + b k / π (k + 1))) :=
          add_le_add (mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 (hπpos _).le)) le_rfl
      _ = (π (k + 1))⁻¹ * (1 + a k) * Y k ω + (π (k + 1))⁻¹ * S k ω - Bs k := by ring
      _ ≤ (π k)⁻¹ * (Y k ω + S k ω) - Bs k := by
          rw [hinv]
          nlinarith [mul_le_mul_of_nonneg_right hinvle (hS0 k ω)]
  -- `L¹` bound
  have hZlow : ∀ k ω, -Btot ≤ Z k ω := fun k ω => by
    have := mul_nonneg (inv_nonneg.2 (hπpos k).le) (add_nonneg (hY0 k ω) (hS0 k ω))
    simp only [hZdef]
    linarith [hBs k]
  have hint : ∀ k, ∫ ω, Z k ω ∂P ≤ ∫ ω, Z 0 ω ∂P := fun k => by
    have := hsup.setIntegral_le (Nat.zero_le k) MeasurableSet.univ
    simpa only [Measure.restrict_univ] using this
  have hbdd : ∀ k, eLpNorm ((-Z) k) 1 P ≤ ENNReal.ofReal (∫ ω, Z 0 ω ∂P + 2 * Btot) := by
    intro k
    rw [Pi.neg_apply, eLpNorm_neg, eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hZi k)]
    · refine ENNReal.ofReal_le_ofReal ?_
      calc ∫ ω, ‖Z k ω‖ ∂P ≤ ∫ ω, (Z k ω + 2 * Btot) ∂P := integral_mono (hZi k).norm
            ((hZi k).add (integrable_const _)) fun ω => by
            rw [Real.norm_eq_abs, abs_le]
            constructor <;> linarith [hZlow k ω]
        _ = ∫ ω, Z k ω ∂P + 2 * Btot := by
            rw [integral_add (hZi k) (integrable_const _)]
            simp
        _ ≤ _ := by linarith [hint k]
    · exact (hZi k).aestronglyMeasurable
  have hconv := hsup.neg.ae_tendsto_limitProcess hbdd
  -- the deterministic limits
  have hπlim : ∃ l, Tendsto π atTop (𝓝 l) :=
    ⟨_, tendsto_atTop_ciSup hπmono ⟨_, by rintro _ ⟨k, rfl⟩; exact hπbdd k⟩⟩
  obtain ⟨πl, hπl⟩ := hπlim
  have hsB : Summable fun j => b j / π (j + 1) :=
    Summable.of_nonneg_of_le (fun j => div_nonneg (hb j) (hπpos _).le)
      (fun j => div_le_self (hb j) (hπ1 (j + 1))) hsb
  have hBlim : Tendsto Bs atTop (𝓝 (∑' j, b j / π (j + 1))) := hsB.hasSum.tendsto_sum_nat
  filter_upwards [hconv] with ω hω
  have hZω : Tendsto (fun k => Z k ω) atTop (𝓝 (-ℱ.limitProcess (-Z) P ω)) := by
    have := hω.neg
    simpa using this
  -- `W_k = Y_k + S_k = π_k(Z_k + B_k)` converges
  have hW : Tendsto (fun k => Y k ω + S k ω) atTop
      (𝓝 (πl * (-ℱ.limitProcess (-Z) P ω + ∑' j, b j / π (j + 1)))) := by
    have e : (fun k => Y k ω + S k ω) = fun k => π k * (Z k ω + Bs k) := funext fun k => by
      simp only [hZdef]
      field_simp [(hπpos k).ne']
      ring
    rw [e]
    exact hπl.mul (hZω.add hBlim)
  obtain ⟨M, hM⟩ := hW.bddAbove_range
  have hcs : Summable fun k => c k ω :=
    summable_of_sum_range_le (fun k => hc0 k ω) fun n =>
      le_trans (le_add_of_nonneg_left (hY0 n ω)) (hM ⟨n, rfl⟩)
  have hSlim : Tendsto (fun k => S k ω) atTop (𝓝 (∑' j, c j ω)) := hcs.hasSum.tendsto_sum_nat
  have hYlim : Tendsto (fun k => Y k ω) atTop
      (𝓝 (πl * (-ℱ.limitProcess (-Z) P ω + ∑' j, b j / π (j + 1)) - ∑' j, c j ω)) := by
    have := hW.sub hSlim
    simpa using this
  exact ⟨⟨_, hYlim⟩, hcs⟩

end DPExtensions.TemporalDifference

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stochastic approximation with a quadratic Lyapunov function

The Robbins–Monro iteration `θ_{k+1} = θ_k + α_k(h(θ_k) + W_k)` in a real Hilbert space
converges almost surely to the zero `θ̄` of the mean dynamics `h` when there is a quadratic
Lyapunov function `V(x) = ⟪Q(x − θ̄), x − θ̄⟫` along which `h` points inwards:
`⟪Q(x − θ̄), h(x)⟫ ≤ −κ‖x − θ̄‖²`, with `Q` symmetric and coercive and `h` growing at most
linearly away from `θ̄`. This is the classical ODE (Lyapunov) criterion of stochastic
approximation (Ljung, 1977; Benveniste, Métivier and Priouret, 1990) in its
quadratic form, and the convergence criterion behind E-stability (Evans and Honkapohja, 2001).

* `sa_lyapunov`: the convergence theorem. `V(θ_k)` satisfies the Robbins–Siegmund inequality
  with `c_k = 2κα_k‖θ_k − θ̄‖²`, so `V(θ_k)` converges and `∑ α_k‖θ_k − θ̄‖² < ∞`, which with
  `∑ α_k = ∞` forces the limit to be `0`.

No contraction is assumed, and the step sizes need not be below `1`. Copied from the
`Extensions/AdaptiveLearning` project.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace DPExtensions.TemporalDifference

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℕ m0}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Stochastic approximation with a quadratic Lyapunov function.** Let
`θ_{k+1} = θ_k + α_k(h(θ_k) + W_k)` with `h` continuous, `‖h(x)‖ ≤ L‖x − θ̄‖`, and a bounded
symmetric operator `Q` with `⟪Qx, x⟫ ≥ m‖x‖²` (`m > 0`) and
`⟪Q(x − θ̄), h(x)⟫ ≤ −κ‖x − θ̄‖²` (`κ > 0`). If `θ₀` and the `W_k` are square integrable,
`θ₀` is `ℱ₀`-measurable, `W_k` is `ℱ_{k+1}`-measurable with `𝔼[W_k | ℱ_k] = 0` and
`𝔼[‖W_k‖² | ℱ_k] ≤ C(1 + ‖θ_k‖²)`, and `α_k ≥ 0` with `∑ α_k = ∞` and `∑ α_k² < ∞`, then
`θ_k → θ̄` almost surely. -/
theorem sa_lyapunov {h : E → E} (hhc : Continuous h) {θbar : E} {Q : E →L[ℝ] E}
    (hQsym : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y)) {m κ L : ℝ} (hm : 0 < m) (hκ : 0 < κ)
    (hQpos : ∀ x, m * ‖x‖ ^ 2 ≤ inner ℝ (Q x) x)
    (hdrift : ∀ x, inner ℝ (Q (x - θbar)) (h x) ≤ -κ * ‖x - θbar‖ ^ 2)
    (hlin : ∀ x, ‖h x‖ ≤ L * ‖x - θbar‖)
    {α : ℕ → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hdiv : ¬ Summable α) (hsq : Summable fun k => α k ^ 2)
    {θ W : ℕ → Ω → E}
    (hrec : ∀ k ω, θ (k + 1) ω = θ k ω + α k • (h (θ k ω) + W k ω))
    (hθ0m : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0 : MemLp (θ 0) 2 P)
    (hWm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (W k)) (hW2 : ∀ k, MemLp (W k) 2 P)
    (hW0 : ∀ k, P[W k | ℱ k] =ᵐ[P] 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k, P[fun ω => ‖W k ω‖ ^ 2 | ℱ k] ≤ᵐ[P] fun ω => C * (1 + ‖θ k ω‖ ^ 2)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => θ k ω) atTop (𝓝 θbar) := by
  set M := ‖Q‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  have hQb : ∀ x y, |inner ℝ (Q x) y| ≤ M * (‖x‖ * ‖y‖) := fun x y =>
    (abs_real_inner_le_norm _ _).trans (by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (Q.le_opNorm x) (norm_nonneg _))
  have hQsq : ∀ x, |inner ℝ (Q x) x| ≤ M * ‖x‖ ^ 2 := fun x => by
    have := hQb x x
    rwa [← sq] at this
  have hhsq : ∀ x, ‖h x‖ ^ 2 ≤ L ^ 2 * ‖x - θbar‖ ^ 2 := fun x => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hlin x) 2
  -- adaptedness and square integrability of the iterates
  have hhL : ∀ {f : Ω → E}, MemLp f 2 P → MemLp (fun ω => h (f ω)) 2 P := fun {f} hf =>
    ((hf.sub (memLp_const θbar)).norm.const_mul L).mono'
      (hhc.comp_aestronglyMeasurable hf.aestronglyMeasurable) (Eventually.of_forall fun ω => by
        simp only [Pi.sub_apply]
        exact hlin _)
  have hθ : ∀ k, StronglyMeasurable[ℱ k] (θ k) ∧ MemLp (θ k) 2 P := by
    intro k
    induction k with
    | zero => exact ⟨hθ0m, hθ0⟩
    | succ k ih =>
      obtain ⟨hm', hL⟩ := ih
      have he : θ (k + 1) = fun ω => θ k ω + α k • (h (θ k ω) + W k ω) := funext (hrec k)
      have hm'' : StronglyMeasurable[ℱ (k + 1)] (θ k) := hm'.mono (ℱ.mono k.le_succ)
      rw [he]
      exact ⟨hm''.add (((hhc.comp_stronglyMeasurable hm'').add (hWm k)).const_smul (α k)),
        hL.add (((hhL hL).add (hW2 k)).const_smul (α k))⟩
  have hesq : ∀ k, Integrable (fun ω => ‖θ k ω - θbar‖ ^ 2) P := fun k =>
    (memLp_two_iff_integrable_sq_norm
      ((hθ k).2.sub (memLp_const θbar)).aestronglyMeasurable).1
      ((hθ k).2.sub (memLp_const θbar))
  have hesm : ∀ k, StronglyMeasurable[ℱ k] fun ω => ‖θ k ω - θbar‖ ^ 2 := fun k =>
    ((hθ k).1.sub stronglyMeasurable_const).norm.pow 2
  -- `Y_k = V(θ_k)`
  set Y : ℕ → Ω → ℝ := fun k ω => inner ℝ (Q (θ k ω - θbar)) (θ k ω - θbar) with hYdef
  have hYm : StronglyAdapted ℱ Y := fun k =>
    (Q.continuous.comp_stronglyMeasurable ((hθ k).1.sub stronglyMeasurable_const)).inner
      ((hθ k).1.sub stronglyMeasurable_const)
  have hYlow : ∀ k ω, m * ‖θ k ω - θbar‖ ^ 2 ≤ Y k ω := fun k ω => hQpos _
  have hYup : ∀ k ω, Y k ω ≤ M * ‖θ k ω - θbar‖ ^ 2 := fun k ω =>
    (le_abs_self _).trans (hQsq _)
  have hY0 : ∀ k ω, 0 ≤ Y k ω := fun k ω =>
    (mul_nonneg hm.le (sq_nonneg _)).trans (hYlow k ω)
  have hYi : ∀ k, Integrable (Y k) P := fun k =>
    ((hesq k).const_mul M).mono' ((hYm k).mono (ℱ.le k)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact hQsq _)
  set c : ℕ → Ω → ℝ := fun k ω => 2 * κ * α k * ‖θ k ω - θbar‖ ^ 2 with hcdef
  set a : ℕ → ℝ := fun k => α k ^ 2 * ((M * L ^ 2 + 2 * M * C) / m) with hadef
  set b : ℕ → ℝ := fun k => α k ^ 2 * (M * C * (1 + 2 * ‖θbar‖ ^ 2)) with hbdef
  have hstep : ∀ k, P[Y (k + 1) | ℱ k] ≤ᵐ[P] fun ω => (1 + a k) * Y k ω + b k - c k ω := by
    intro k
    set u : Ω → E := fun ω => θ k ω - θbar + α k • h (θ k ω)
    have hum : StronglyMeasurable[ℱ k] u :=
      ((hθ k).1.sub stronglyMeasurable_const).add
        ((hhc.comp_stronglyMeasurable (hθ k).1).const_smul (α k))
    have huL : MemLp u 2 P :=
      ((hθ k).2.sub (memLp_const θbar)).add ((hhL (hθ k).2).const_smul (α k))
    have hQum : StronglyMeasurable[ℱ k] fun ω => Q (u ω) := Q.continuous.comp_stronglyMeasurable hum
    have hsplit : ∀ ω, θ (k + 1) ω - θbar = u ω + α k • W k ω := fun ω => by
      rw [hrec]
      simp only [u, smul_add]
      abel
    set U : Ω → ℝ := fun ω => inner ℝ (Q (u ω)) (u ω)
    set I : Ω → ℝ := fun ω => innerSL ℝ (Q (u ω)) (W k ω)
    set N : Ω → ℝ := fun ω => inner ℝ (Q (W k ω)) (W k ω)
    have hYsplit : Y (k + 1) = U + (2 * α k) • I + (α k ^ 2) • N := by
      funext ω
      simp only [hYdef, U, I, N, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsplit,
        innerSL_apply_apply, map_add, map_smul, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hQsym (W k ω) (u ω), real_inner_comm (Q (u ω)) (W k ω)]
      ring
    have huq : Integrable (fun ω => ‖u ω‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm huL.aestronglyMeasurable).1 huL
    have hwq : Integrable (fun ω => ‖W k ω‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm (hW2 k).aestronglyMeasurable).1 (hW2 k)
    have hUm : StronglyMeasurable[ℱ k] U := hQum.inner hum
    have hUi : Integrable U P :=
      (huq.const_mul M).mono' (hUm.mono (ℱ.le k)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]
          exact hQsq _)
    have hNm : StronglyMeasurable N :=
      (Q.continuous.comp_stronglyMeasurable ((hWm k).mono (ℱ.le (k + 1)))).inner
        ((hWm k).mono (ℱ.le (k + 1)))
    have hNi : Integrable N P :=
      (hwq.const_mul M).mono' hNm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]
          exact hQsq _)
    have hIi : Integrable I P := by
      refine ((huq.add hwq).const_mul M).mono' ?_ (Eventually.of_forall fun ω => ?_)
      · exact ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous₂.comp_aestronglyMeasurable₂
          (hQum.mono (ℱ.le k)).aestronglyMeasurable (hW2 k).aestronglyMeasurable)
      · simp only [I, Pi.add_apply, innerSL_apply_apply, Real.norm_eq_abs]
        refine (hQb _ _).trans (mul_le_mul_of_nonneg_left ?_ hM0)
        nlinarith [sq_nonneg (‖u ω‖ - ‖W k ω‖), norm_nonneg (u ω), norm_nonneg (W k ω)]
    have hcI : P[I | ℱ k] =ᵐ[P] 0 := by
      have h1 := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
        hQum.aestronglyMeasurable hIi ((hW2 k).integrable one_le_two)
      filter_upwards [h1, hW0 k] with ω h1 h2
      rw [h1, h2]
      simp
    have hcN : P[N | ℱ k] ≤ᵐ[P] fun ω => M * (C * (1 + ‖θ k ω‖ ^ 2)) := by
      have h1 := condExp_mono (m := ℱ k) hNi (hwq.const_mul M)
        (Eventually.of_forall fun ω => (le_abs_self _).trans (hQsq _))
      have h2 := condExp_smul (μ := P) M (fun ω => ‖W k ω‖ ^ 2) (ℱ k)
      filter_upwards [h1, h2, hC k] with ω e1 e2 e3
      have e2' : P[fun ω => M * ‖W k ω‖ ^ 2 | ℱ k] ω = M * P[fun ω => ‖W k ω‖ ^ 2 | ℱ k] ω := e2
      exact e1.trans (e2'.le.trans (mul_le_mul_of_nonneg_left e3 hM0))
    rw [hYsplit]
    have hsum := condExp_add (hUi.add (hIi.smul (2 * α k))) (hNi.smul (α k ^ 2)) (ℱ k)
    have hsum2 := condExp_add hUi (hIi.smul (2 * α k)) (ℱ k)
    have hs1 := condExp_smul (μ := P) (2 * α k) I (ℱ k)
    have hs2 := condExp_smul (μ := P) (α k ^ 2) N (ℱ k)
    have hU := condExp_of_stronglyMeasurable (ℱ.le k) hUm hUi
    filter_upwards [hsum, hsum2, hs1, hs2, hcI, hcN] with ω e1 e2 e3 e4 e5 e6
    rw [e1, Pi.add_apply, e2, Pi.add_apply, hU, e3, e4, Pi.smul_apply, Pi.smul_apply, e5,
      smul_eq_mul, smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
    -- the deterministic part
    set e := θ k ω - θbar with hedef
    have hUexp : U ω = Y k ω + 2 * α k * inner ℝ (Q e) (h (θ k ω)) +
        α k ^ 2 * inner ℝ (Q (h (θ k ω))) (h (θ k ω)) := by
      simp only [U, u, hYdef, map_add, map_smul, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hQsym (h (θ k ω)) e, real_inner_comm (Q e) (h (θ k ω))]
      ring
    have hd := hdrift (θ k ω)
    have hhh : inner ℝ (Q (h (θ k ω))) (h (θ k ω)) ≤ M * (L ^ 2 * ‖e‖ ^ 2) :=
      (le_abs_self _).trans ((hQsq _).trans (mul_le_mul_of_nonneg_left (hhsq _) hM0))
    have hθsq : ‖θ k ω‖ ^ 2 ≤ 2 * ‖e‖ ^ 2 + 2 * ‖θbar‖ ^ 2 := by
      have h1 : ‖θ k ω‖ ≤ ‖e‖ + ‖θbar‖ := by
        have := norm_add_le e θbar
        rwa [hedef, sub_add_cancel] at this
      nlinarith [sq_nonneg (‖e‖ - ‖θbar‖), norm_nonneg (θ k ω), norm_nonneg e,
        norm_nonneg θbar]
    have hey : ‖e‖ ^ 2 ≤ Y k ω / m := by
      rw [le_div_iff₀ hm, mul_comm]
      exact hYlow k ω
    have hK0 : 0 ≤ M * L ^ 2 + 2 * M * C := by positivity
    have hα2 : 0 ≤ α k ^ 2 := sq_nonneg _
    have hA : α k ^ 2 * ((M * L ^ 2 + 2 * M * C) * ‖e‖ ^ 2) ≤ a k * Y k ω := by
      have h1 : (M * L ^ 2 + 2 * M * C) * ‖e‖ ^ 2 ≤ (M * L ^ 2 + 2 * M * C) * (Y k ω / m) :=
        mul_le_mul_of_nonneg_left hey hK0
      have h2 : a k * Y k ω = α k ^ 2 * ((M * L ^ 2 + 2 * M * C) * (Y k ω / m)) := by
        simp only [hadef]
        ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 hα2
    have hN' : α k ^ 2 * (M * (C * (1 + ‖θ k ω‖ ^ 2))) ≤
        α k ^ 2 * (2 * M * C * ‖e‖ ^ 2) + b k := by
      simp only [hbdef]
      have : M * (C * (1 + ‖θ k ω‖ ^ 2)) ≤ 2 * M * C * ‖e‖ ^ 2 + M * C * (1 + 2 * ‖θbar‖ ^ 2) := by
        have hMC : 0 ≤ M * C := mul_nonneg hM0 hC0
        nlinarith [mul_le_mul_of_nonneg_left hθsq hMC]
      nlinarith [mul_le_mul_of_nonneg_left this hα2]
    have hα := hα0 k
    have hcdrift : 2 * α k * inner ℝ (Q e) (h (θ k ω)) ≤ -c k ω := by
      simp only [hcdef]
      have := mul_le_mul_of_nonneg_left hd (mul_nonneg zero_le_two hα)
      linarith
    have hhh' : α k ^ 2 * inner ℝ (Q (h (θ k ω))) (h (θ k ω)) ≤
        α k ^ 2 * (M * L ^ 2 * ‖e‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hhh hα2
      linarith
    have hcomb : α k ^ 2 * (M * L ^ 2 * ‖e‖ ^ 2) + α k ^ 2 * (2 * M * C * ‖e‖ ^ 2) =
        α k ^ 2 * ((M * L ^ 2 + 2 * M * C) * ‖e‖ ^ 2) := by ring
    have hN'' : α k ^ 2 * P[N | ℱ k] ω ≤ α k ^ 2 * (M * (C * (1 + ‖θ k ω‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left e6 hα2
    rw [hUexp]
    nlinarith
  -- Robbins–Siegmund
  have hcad : StronglyAdapted ℱ c := fun k => stronglyMeasurable_const.mul (hesm k)
  have hci : ∀ k, Integrable (c k) P := fun k => (hesq k).const_mul _
  have hc0 : ∀ k ω, 0 ≤ c k ω := fun k ω =>
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hκ.le) (hα0 k)) (sq_nonneg _)
  have ha : ∀ k, 0 ≤ a k := fun k =>
    mul_nonneg (sq_nonneg _) (div_nonneg (by positivity) hm.le)
  have hb : ∀ k, 0 ≤ b k := fun k => mul_nonneg (sq_nonneg _) (by positivity)
  have hRS := robbins_siegmund hYm hcad hYi hci hY0 hc0 ha hb (hsq.mul_right _)
    (hsq.mul_right _) hstep
  filter_upwards [hRS] with ω hω
  obtain ⟨⟨Lim, hLim⟩, hcs⟩ := hω
  have hLim0 : Lim = 0 := by
    have hLnn : 0 ≤ Lim := ge_of_tendsto' hLim fun k => hY0 k ω
    by_contra hne
    have hLpos : 0 < Lim := lt_of_le_of_ne hLnn (Ne.symm hne)
    have hev : ∀ᶠ k in atTop, Lim / 2 < Y k ω :=
      hLim.eventually (lt_mem_nhds (half_lt_self hLpos))
    apply hdiv
    refine Summable.of_norm_bounded_eventually (hcs.mul_left (M / (κ * Lim))) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with k hk
    rw [Real.norm_eq_abs, abs_of_nonneg (hα0 k), div_mul_eq_mul_div,
      le_div_iff₀ (mul_pos hκ hLpos)]
    simp only [hcdef]
    have h1 := mul_le_mul_of_nonneg_left hk.le (hα0 k)
    have h2 := mul_le_mul_of_nonneg_left (hYup k ω) (hα0 k)
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hκ.le]
  rw [hLim0] at hLim
  have hsq0 : Tendsto (fun k => ‖θ k ω - θbar‖ ^ 2) atTop (𝓝 0) := by
    have hup : Tendsto (fun k => Y k ω / m) atTop (𝓝 0) := by
      simpa using hLim.div_const m
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => sq_nonneg _) fun k => ?_
    rw [le_div_iff₀ hm, mul_comm]
    exact hYlow k ω
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : (fun k => ‖θ k ω - θbar‖) = fun k => Real.sqrt (‖θ k ω - θbar‖ ^ 2) :=
    funext fun k => (Real.sqrt_sq (norm_nonneg _)).symm
  rw [e]
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq0
  rw [Real.sqrt_zero] at h
  exact h

end DPExtensions.TemporalDifference

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stationary-distribution norm

Tsitsiklis and Van Roy (1997).

For a Markov matrix `P` on a finite state space with stationary distribution `d`, the weighted
norm `‖v‖_d² = ∑_x d(x)v(x)²` makes `P` nonexpansive (`dsq_applyP_le`), by Jensen's inequality
row by row (`jensen_sq`) and stationarity. So the Bellman operator `Tv = r + βPv` of a Markov
reward process is a `β`-contraction for `‖·‖_d` (`dsq_bellman_sub_le`), and
`⟨v, Pv⟩_d ≤ ‖v‖_d²` (`dinner_applyP_le`), the inequality behind the convergence of TD learning.
-/

open Finset

namespace DPExtensions.TemporalDifference

variable {X : Type*} [Fintype X]

/-- The squared weighted norm `‖v‖_d² = ∑_x d(x)v(x)²`. -/
def dsq (d v : X → ℝ) : ℝ := ∑ x, d x * v x ^ 2

/-- The weighted inner product `⟨v, w⟩_d = ∑_x d(x)v(x)w(x)`. -/
def dinner (d v w : X → ℝ) : ℝ := ∑ x, d x * v x * w x

/-- `(Pv)(x) = ∑_y P(x, y)v(y)`. -/
def applyP (P : X → X → ℝ) (v : X → ℝ) (x : X) : ℝ := ∑ y, P x y * v y

theorem dsq_nonneg {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (v : X → ℝ) : 0 ≤ dsq d v :=
  sum_nonneg fun x _ => mul_nonneg (hd x) (sq_nonneg _)

theorem dinner_self (d v : X → ℝ) : dinner d v v = dsq d v :=
  sum_congr rfl fun x _ => by ring

theorem dinner_comm (d v w : X → ℝ) : dinner d v w = dinner d w v :=
  sum_congr rfl fun x _ => by ring

theorem dsq_add (d v w : X → ℝ) :
    dsq d (fun x => v x + w x) = dsq d v + 2 * dinner d v w + dsq d w := by
  simp only [dsq, dinner, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by ring

theorem dsq_smul (d v : X → ℝ) (c : ℝ) : dsq d (fun x => c * v x) = c ^ 2 * dsq d v := by
  simp only [dsq, mul_sum]
  exact sum_congr rfl fun x _ => by ring

theorem dinner_le {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (v w : X → ℝ) :
    2 * dinner d v w ≤ dsq d v + dsq d w := by
  simp only [dsq, dinner, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  nlinarith [mul_nonneg (hd x) (sq_nonneg (v x - w x))]

/-- **Jensen's inequality for a probability row**: `(∑ p_y v_y)² ≤ ∑ p_y v_y²`. -/
theorem jensen_sq {p v : X → ℝ} (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1) :
    (∑ y, p y * v y) ^ 2 ≤ ∑ y, p y * v y ^ 2 := by
  set m := ∑ y, p y * v y
  have h : 0 ≤ ∑ y, p y * (v y - m) ^ 2 := sum_nonneg fun y _ => mul_nonneg (hp y) (sq_nonneg _)
  have e : ∑ y, p y * (v y - m) ^ 2 = ∑ y, p y * v y ^ 2 - 2 * m * m + m ^ 2 * ∑ y, p y := by
    have hy : ∀ y, p y * (v y - m) ^ 2 = p y * v y ^ 2 - 2 * m * (p y * v y) + m ^ 2 * p y :=
      fun y => by ring
    simp only [hy, sum_add_distrib, sum_sub_distrib, ← mul_sum]
    rfl
  rw [e, h1] at h
  nlinarith

/-- **`P` is nonexpansive for `‖·‖_d`** when `d` is stationary. -/
theorem dsq_applyP_le {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (hstat : ∀ y, ∑ x, d x * P x y = d y) (v : X → ℝ) :
    dsq d (applyP P v) ≤ dsq d v := by
  calc dsq d (applyP P v) ≤ ∑ x, d x * ∑ y, P x y * v y ^ 2 :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (jensen_sq (hP0 x) (hP1 x)) (hd x)
    _ = dsq d v := by
        simp only [mul_sum, dsq]
        rw [sum_comm]
        refine sum_congr rfl fun y _ => ?_
        rw [← hstat y, sum_mul]
        exact sum_congr rfl fun x _ => by ring

/-- `⟨v, Pv⟩_d ≤ ‖v‖_d²`. -/
theorem dinner_applyP_le {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (hstat : ∀ y, ∑ x, d x * P x y = d y) (v : X → ℝ) :
    dinner d v (applyP P v) ≤ dsq d v := by
  linarith [dinner_le hd v (applyP P v), dsq_applyP_le hP0 hP1 hd hstat v]

/-- **The Bellman operator is a `β`-contraction for `‖·‖_d`**: with `Tv = r + βPv`,
`‖Tv − Tw‖_d² ≤ β²‖v − w‖_d²`. -/
theorem dsq_bellman_sub_le {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y)
    (hP1 : ∀ x, ∑ y, P x y = 1) {d : X → ℝ} (hd : ∀ x, 0 ≤ d x)
    (hstat : ∀ y, ∑ x, d x * P x y = d y) (r : X → ℝ) (β : ℝ) (v w : X → ℝ) :
    dsq d (fun x => (r x + β * applyP P v x) - (r x + β * applyP P w x)) ≤
      β ^ 2 * dsq d (fun x => v x - w x) := by
  have e : (fun x => (r x + β * applyP P v x) - (r x + β * applyP P w x)) =
      fun x => β * applyP P (fun y => v y - w y) x := by
    funext x
    simp only [applyP, mul_sub, sum_sub_distrib]
    ring
  rw [e, dsq_smul]
  exact mul_le_mul_of_nonneg_left (dsq_applyP_le hP0 hP1 hd hstat _) (sq_nonneg β)

end DPExtensions.TemporalDifference

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear value-function approximation and the TD fixed point

Tsitsiklis and Van Roy (1997); Sutton (1988).

Values are approximated by `V_θ(x) = ⟪φ(x), θ⟫` with features `φ : X → E` in a finite-dimensional
real inner product space. TD(0) moves `θ` along `φ(x)(r(x) + βV_θ(x') − V_θ(x))`, whose mean under
the stationary distribution `d` and the transitions `P` is the **mean field**
`h(θ) = ∑_x d(x)(r(x) + β(PV_θ)(x) − V_θ(x))φ(x)`.

* `exists_gram_lower`: if `d > 0` and the features span `E`, `‖V_z‖_d² ≥ m‖z‖²` for some `m > 0`.
* `inner_meanField_sub`, `meanField_lyapunov`: `⟪θ − θ', h(θ) − h(θ')⟫ ≤ −(1 − β)‖V_{θ−θ'}‖_d²`
  — the mean field is strongly monotone, although TD is not the gradient of any objective.
* `meanField_lipschitz`: `h` is Lipschitz.
* `exists_unique_fixedPoint`: the TD fixed point `h(θ*) = 0` exists and is unique.
-/

open Finset

namespace DPExtensions.TemporalDifference

variable {X : Type*} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear approximation `V_θ(x) = ⟪φ(x), θ⟫`. -/
def vθ (φ : X → E) (θ : E) (x : X) : ℝ := inner ℝ (φ x) θ

omit [Fintype X] in
theorem vθ_sub (φ : X → E) (θ θ' : E) : vθ φ (θ - θ') = fun x => vθ φ θ x - vθ φ θ' x :=
  funext fun _ => inner_sub_right _ _ _

omit [Fintype X] in
theorem vθ_smul (φ : X → E) (c : ℝ) (θ : E) : vθ φ (c • θ) = fun x => c * vθ φ θ x :=
  funext fun _ => real_inner_smul_right _ _ _

/-- With `d > 0` and spanning features, `‖V_z‖_d² > 0` for `z ≠ 0`. -/
theorem dsq_vθ_pos {d : X → ℝ} (hd : ∀ x, 0 < d x) {φ : X → E}
    (hspan : ∀ z, (∀ x, inner ℝ (φ x) z = 0) → z = 0) {z : E} (hz : z ≠ 0) :
    0 < dsq d (vθ φ z) := by
  refine lt_of_le_of_ne (dsq_nonneg (fun x => (hd x).le) _) fun h => hz (hspan z fun x => ?_)
  have h0 := (sum_eq_zero_iff_of_nonneg fun x _ =>
    mul_nonneg (hd x).le (sq_nonneg (vθ φ z x))).1 h.symm x (mem_univ x)
  have : vθ φ z x ^ 2 = 0 := by
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 (hd x).ne'
    · exact h1
  exact pow_eq_zero_iff two_ne_zero |>.1 this

/-- **The Gram form is coercive**: `‖V_z‖_d² ≥ m‖z‖²` with `m > 0`. -/
theorem exists_gram_lower [FiniteDimensional ℝ E] {d : X → ℝ} (hd : ∀ x, 0 < d x)
    {φ : X → E} (hspan : ∀ z, (∀ x, inner ℝ (φ x) z = 0) → z = 0) :
    ∃ m > 0, ∀ z, m * ‖z‖ ^ 2 ≤ dsq d (vθ φ z) := by
  have hq0 : ∀ z, 0 ≤ dsq d (vθ φ z) := fun z => dsq_nonneg (fun x => (hd x).le) _
  by_cases hE : ∃ z : E, z ≠ 0
  · obtain ⟨z1, hz1⟩ := hE
    set q : E → ℝ := fun z => dsq d (vθ φ z)
    have hqc : Continuous q :=
      continuous_finsetSum _ fun x _ =>
        continuous_const.mul ((continuous_const.inner continuous_id).pow 2)
    have hne : (Metric.sphere (0 : E) 1).Nonempty :=
      ⟨‖z1‖⁻¹ • z1, by simp [norm_smul, norm_ne_zero_iff.2 hz1]⟩
    obtain ⟨z0, hz0, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne hqc.continuousOn
    have hz0ne : z0 ≠ 0 := by
      intro h
      simp [h] at hz0
    refine ⟨q z0, dsq_vθ_pos hd hspan hz0ne, fun z => ?_⟩
    rcases eq_or_ne z 0 with h | h
    · simp [h, hq0]
    · have hw : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
        simp [norm_smul, norm_ne_zero_iff.2 h]
      have h1 := hmin hw
      have e : q z = ‖z‖ ^ 2 * q (‖z‖⁻¹ • z) := by
        simp only [q, vθ_smul, dsq_smul]
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_pow, one_mul]
      change q z0 * ‖z‖ ^ 2 ≤ q z
      rw [e, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · push Not at hE
    exact ⟨1, one_pos, fun z => by simp [hE z, hq0]⟩

/-- The mean field of TD(0), `h(θ) = ∑_x d(x)(r(x) + β(PV_θ)(x) − V_θ(x))φ(x)`. -/
noncomputable def meanField (P : X → X → ℝ) (d r : X → ℝ) (β : ℝ) (φ : X → E) (θ : E) : E :=
  ∑ x, (d x * (r x + β * applyP P (vθ φ θ) x - vθ φ θ x)) • φ x

/-- The linear part of the mean field. -/
noncomputable def meanFieldLin (P : X → X → ℝ) (d : X → ℝ) (β : ℝ) (φ : X → E) : E →ₗ[ℝ] E where
  toFun z := ∑ x, (d x * (β * applyP P (vθ φ z) x - vθ φ z x)) • φ x
  map_add' z w := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← add_smul]
    congr 1
    simp only [vθ, applyP, inner_add_right, mul_add, sum_add_distrib]
    ring
  map_smul' c z := by
    simp only [RingHom.id_apply, smul_sum, smul_smul]
    refine sum_congr rfl fun x _ => ?_
    congr 1
    simp only [vθ, applyP, real_inner_smul_right]
    rw [show ∑ i, P x i * (c * inner ℝ (φ i) z) = c * ∑ i, P x i * inner ℝ (φ i) z by
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by ring]
    ring

theorem meanField_sub (P : X → X → ℝ) (d r : X → ℝ) (β : ℝ) (φ : X → E) (θ θ' : E) :
    meanField P d r β φ θ - meanField P d r β φ θ' = meanFieldLin P d β φ (θ - θ') := by
  simp only [meanField, meanFieldLin, LinearMap.coe_mk, AddHom.coe_mk, ← sum_sub_distrib,
    ← sub_smul]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  simp only [vθ, applyP, inner_sub_right, mul_sub, sum_sub_distrib]
  ring

theorem inner_meanFieldLin (P : X → X → ℝ) (d : X → ℝ) (β : ℝ) (φ : X → E) (z : E) :
    inner ℝ z (meanFieldLin P d β φ z) =
      β * dinner d (vθ φ z) (applyP P (vθ φ z)) - dsq d (vθ φ z) := by
  simp only [meanFieldLin, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, real_inner_smul_right,
    dinner, dsq, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  have : inner ℝ z (φ x) = vθ φ z x := real_inner_comm _ _
  rw [this]
  ring

/-- **The TD mean field is strongly monotone**:
`⟪θ − θ', h(θ) − h(θ')⟫ ≤ −(1 − β)‖V_{θ−θ'}‖_d²`. -/
theorem meanField_lyapunov {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y)
    (hP1 : ∀ x, ∑ y, P x y = 1) {d : X → ℝ} (hd : ∀ x, 0 ≤ d x)
    (hstat : ∀ y, ∑ x, d x * P x y = d y) (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (φ : X → E)
    (θ θ' : E) :
    inner ℝ (θ - θ') (meanField P d r β φ θ - meanField P d r β φ θ') ≤
      -(1 - β) * dsq d (vθ φ (θ - θ')) := by
  rw [meanField_sub, inner_meanFieldLin]
  have := dinner_applyP_le hP0 hP1 hd hstat (vθ φ (θ - θ'))
  nlinarith

/-- **The mean field is Lipschitz.** -/
theorem meanField_lipschitz {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y)
    (hP1 : ∀ x, ∑ y, P x y = 1) {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (r : X → ℝ) {β : ℝ}
    (hβ0 : 0 ≤ β) (φ : X → E) (θ θ' : E) :
    ‖meanField P d r β φ θ - meanField P d r β φ θ'‖ ≤
      ((β + 1) * (∑ y, ‖φ y‖) * (∑ y, ‖φ y‖) * ∑ x, d x) * ‖θ - θ'‖ := by
  rw [meanField_sub]
  set z := θ - θ'
  set Φ := ∑ y, ‖φ y‖
  have hφ : ∀ y, ‖φ y‖ ≤ Φ := fun y =>
    single_le_sum (f := fun y => ‖φ y‖) (fun y _ => norm_nonneg _) (mem_univ y)
  have hu : ∀ y, |vθ φ z y| ≤ Φ * ‖z‖ := fun y =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hφ y) (norm_nonneg _))
  have hPu : ∀ x, |applyP P (vθ φ z) x| ≤ Φ * ‖z‖ := fun x => by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ y, |P x y * vθ φ z y| ≤ ∑ y, P x y * (Φ * ‖z‖) := sum_le_sum fun y _ => by
          rw [abs_mul, abs_of_nonneg (hP0 x y)]
          exact mul_le_mul_of_nonneg_left (hu y) (hP0 x y)
      _ = Φ * ‖z‖ := by rw [← sum_mul, hP1 x, one_mul]
  simp only [meanFieldLin, LinearMap.coe_mk, AddHom.coe_mk]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖(d x * (β * applyP P (vθ φ z) x - vθ φ z x)) • φ x‖
      ≤ ∑ x, d x * ((β + 1) * (Φ * ‖z‖)) * Φ := sum_le_sum fun x _ => by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd x)]
        refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (hd x)) (hφ x) (norm_nonneg _)
          (mul_nonneg (hd x) (by positivity))
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hβ0]
        have h1 := mul_le_mul_of_nonneg_left (hPu x) hβ0
        have h2 := hu x
        linarith
    _ = ((β + 1) * Φ * Φ * ∑ x, d x) * ‖z‖ := by
        rw [← sum_mul, ← sum_mul]
        simp only [sum_mul, mul_sum]
        exact sum_congr rfl fun x _ => by ring

/-- **The TD fixed point exists and is unique**: if `d > 0`, the features span `E` and `β < 1`,
there is exactly one `θ*` with `h(θ*) = 0`. -/
theorem exists_unique_fixedPoint [FiniteDimensional ℝ E] {P : X → X → ℝ}
    (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1) {d : X → ℝ} (hd : ∀ x, 0 < d x)
    (hstat : ∀ y, ∑ x, d x * P x y = d y) (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {φ : X → E} (hspan : ∀ z, (∀ x, inner ℝ (φ x) z = 0) → z = 0) :
    ∃! θs, meanField P d r β φ θs = 0 := by
  obtain ⟨m, hm, hgram⟩ := exists_gram_lower hd hspan
  have hd0 : ∀ x, 0 ≤ d x := fun x => (hd x).le
  set A := meanFieldLin P d β φ
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h1 := meanField_lyapunov hP0 hP1 hd0 hstat r hβ0 φ z 0
    rw [meanField_sub, sub_zero] at h1
    change inner ℝ z (A z) ≤ _ at h1
    rw [hz, inner_zero_right] at h1
    have h2 := hgram z
    have h4 : dsq d (vθ φ z) ≤ 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_pos (sub_pos.2 hβ1) h]
    have h3 : ‖z‖ ^ 2 ≤ 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_pos hm h]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _)))
  obtain ⟨θs, hθs⟩ := (LinearMap.injective_iff_surjective.1 hinj) (-meanField P d r β φ 0)
  have hfix : meanField P d r β φ θs = 0 := by
    have := meanField_sub P d r β φ θs 0
    rw [sub_zero] at this
    change _ = A θs at this
    rw [hθs] at this
    rw [sub_eq_iff_eq_add] at this
    rw [this, neg_add_cancel]
  refine ⟨θs, hfix, fun θ hθ => hinj ?_⟩
  have h1 := meanField_sub P d r β φ θ θs
  rw [hθ, hfix, sub_zero, map_sub] at h1
  exact sub_eq_zero.1 h1.symm

end DPExtensions.TemporalDifference

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# How good is the TD fixed point?

Tsitsiklis and Van Roy (1997).

Let `V = r + βPV` be the true value. The best approximation in the span of the features for
`‖·‖_d` is the projection `ΠV = V_θ̂`, characterized by the normal equations
`⟨V_θ̂ − V, V_z⟩_d = 0` for all `z` (`exists_best_approx`, `best_approx`). The TD fixed point
`V_θ*` is instead the fixed point of `ΠT`: `h(θ*) = 0` says exactly that `TV_θ* − V_θ*` is
orthogonal to the features (`inner_meanField`).

* `tvr_bound`: `(1 − β²)‖V_θ* − V‖_d² ≤ ‖ΠV − V‖_d²`, i.e.
  `‖V_θ* − V‖_d ≤ ‖ΠV − V‖_d / √(1 − β²)`: TD learning is never much worse than the best linear
  approximation when `β` is not close to `1`, and it is exact when the value function lies in the
  span of the features. Tsitsiklis and Van Roy bound the error by `1/(1 − β)` times the
  projection error; the Pythagorean argument used here sharpens the factor to `1/√(1 − β²)`.
-/

open Finset

namespace DPExtensions.TemporalDifference

variable {X : Type*} [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dinner_add_left (d v w u : X → ℝ) :
    dinner d (fun x => v x + w x) u = dinner d v u + dinner d w u := by
  simp only [dinner, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by ring

/-- `⟪z, h(θ)⟫ = ⟨TV_θ − V_θ, V_z⟩_d`. -/
theorem inner_meanField (P : X → X → ℝ) (d r : X → ℝ) (β : ℝ) (φ : X → E) (θ z : E) :
    inner ℝ z (meanField P d r β φ θ) =
      dinner d (fun x => r x + β * applyP P (vθ φ θ) x - vθ φ θ x) (vθ φ z) := by
  simp only [meanField, inner_sum, real_inner_smul_right, dinner]
  refine sum_congr rfl fun x _ => ?_
  have : inner ℝ z (φ x) = vθ φ z x := real_inner_comm _ _
  rw [this]

/-- Solutions of the normal equations are best approximations. -/
theorem best_approx {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) {φ : X → E} {V : X → ℝ} {θh : E}
    (hθh : ∀ z, dinner d (fun x => vθ φ θh x - V x) (vθ φ z) = 0) (θ : E) :
    dsq d (fun x => vθ φ θh x - V x) ≤ dsq d (fun x => vθ φ θ x - V x) := by
  have e : (fun x => vθ φ θ x - V x) = fun x => (vθ φ θh x - V x) + vθ φ (θ - θh) x := by
    funext x
    rw [vθ_sub]
    ring
  rw [e, dsq_add, hθh, mul_zero, add_zero]
  linarith [dsq_nonneg hd (vθ φ (θ - θh))]

/-- **The projection exists**: if `d > 0` and the features span `E`, the normal equations have a
solution. -/
theorem exists_best_approx [FiniteDimensional ℝ E] {d : X → ℝ} (hd : ∀ x, 0 < d x) {φ : X → E}
    (hspan : ∀ z, (∀ x, inner ℝ (φ x) z = 0) → z = 0) (V : X → ℝ) :
    ∃ θh, ∀ z, dinner d (fun x => vθ φ θh x - V x) (vθ φ z) = 0 := by
  obtain ⟨m, hm, hgram⟩ := exists_gram_lower hd hspan
  let G : E →ₗ[ℝ] E :=
    { toFun := fun z => ∑ x, (d x * vθ φ z x) • φ x
      map_add' := fun z w => by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun x _ => ?_
        rw [← add_smul]
        congr 1
        simp only [vθ, inner_add_right]
        ring
      map_smul' := fun c z => by
        simp only [RingHom.id_apply, smul_sum, smul_smul]
        refine sum_congr rfl fun x _ => ?_
        congr 1
        simp only [vθ, real_inner_smul_right]
        ring }
  have hG : ∀ z w, inner ℝ w (G z) = dinner d (vθ φ z) (vθ φ w) := fun z w => by
    simp only [G, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, real_inner_smul_right, dinner]
    refine sum_congr rfl fun x _ => ?_
    have : inner ℝ w (φ x) = vθ φ w x := real_inner_comm _ _
    rw [this]
  have hinj : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h1 := hG z z
    rw [hz, inner_zero_right, dinner_self] at h1
    have h2 := hgram z
    have h3 : ‖z‖ ^ 2 ≤ 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_pos hm h]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _)))
  obtain ⟨θh, hθh⟩ := (LinearMap.injective_iff_surjective.1 hinj) (∑ x, (d x * V x) • φ x)
  refine ⟨θh, fun z => ?_⟩
  have h1 := hG θh z
  rw [hθh] at h1
  have h2 : inner ℝ z (∑ x, (d x * V x) • φ x) = dinner d V (vθ φ z) := by
    simp only [inner_sum, real_inner_smul_right, dinner]
    refine sum_congr rfl fun x _ => ?_
    have : inner ℝ z (φ x) = vθ φ z x := real_inner_comm _ _
    rw [this]
  have e : dinner d (fun x => vθ φ θh x - V x) (vθ φ z) =
      dinner d (vθ φ θh) (vθ φ z) - dinner d V (vθ φ z) := by
    simp only [dinner, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  rw [e, ← h1, ← h2, sub_self]

/-- **The TD error bound** (after Tsitsiklis and Van Roy, 1997):
`(1 − β²)‖V_θ* − V‖_d² ≤ ‖ΠV − V‖_d²`. -/
theorem tvr_bound {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (hstat : ∀ y, ∑ x, d x * P x y = d y) {r : X → ℝ} {β : ℝ}
    {φ : X → E} {V : X → ℝ} (hV : ∀ x, V x = r x + β * applyP P V x) {θs : E}
    (hθs : meanField P d r β φ θs = 0) {θh : E}
    (hθh : ∀ z, dinner d (fun x => vθ φ θh x - V x) (vθ φ z) = 0) :
    (1 - β ^ 2) * dsq d (fun x => vθ φ θs x - V x) ≤ dsq d (fun x => vθ φ θh x - V x) := by
  set a : X → ℝ := fun x => vθ φ θh x - V x
  set s : X → ℝ := vθ φ (θs - θh)
  set e : X → ℝ := fun x => vθ φ θs x - V x
  have hs : ∀ x, s x = vθ φ θs x - vθ φ θh x := fun x => by simp [s, vθ_sub]
  have hes : e = fun x => s x + a x := funext fun x => by simp only [e, a, hs]; ring
  -- `TV_θ* − V_θ*` is orthogonal to the features
  have horth : ∀ z, dinner d (fun x => r x + β * applyP P (vθ φ θs) x - vθ φ θs x)
      (vθ φ z) = 0 := fun z => by
    rw [← inner_meanField, hθs, inner_zero_right]
  -- `w = TV_θ* − TV = βPe`
  set w : X → ℝ := fun x => β * applyP P e x
  have hw : ∀ x, w x - s x =
      (r x + β * applyP P (vθ φ θs) x - vθ φ θs x) + a x := fun x => by
    simp only [w, a, hs, e, applyP, mul_sub, sum_sub_distrib]
    rw [hV x]
    simp only [applyP]
    ring
  have hws : ∀ z, dinner d (fun x => w x - s x) (vθ φ z) = 0 := fun z => by
    rw [show (fun x => w x - s x) = fun x =>
      (r x + β * applyP P (vθ φ θs) x - vθ φ θs x) + a x from funext hw, dinner_add_left,
      horth, hθh, add_zero]
  -- Pythagoras twice
  have h1 : dsq d e = dsq d s + dsq d a := by
    rw [hes, dsq_add, dinner_comm, hθh, mul_zero, add_zero]
  have h2 : dsq d s ≤ dsq d w := by
    have e2 : w = fun x => s x + (w x - s x) := funext fun x => by ring
    have h3 := dsq_add d s (fun x => w x - s x)
    rw [← e2, dinner_comm, hws, mul_zero, add_zero] at h3
    rw [h3]
    linarith [dsq_nonneg hd (fun x => w x - s x)]
  have h4 : dsq d w ≤ β ^ 2 * dsq d e := by
    simp only [w]
    rw [dsq_smul]
    exact mul_le_mul_of_nonneg_left (dsq_applyP_le hP0 hP1 hd hstat e) (sq_nonneg β)
  nlinarith

end DPExtensions.TemporalDifference

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

set_option linter.style.longLine false
#print axioms DPExtensions.TemporalDifference.robbins_siegmund
#print axioms DPExtensions.TemporalDifference.sa_lyapunov
#print axioms DPExtensions.TemporalDifference.dsq
#print axioms DPExtensions.TemporalDifference.dinner
#print axioms DPExtensions.TemporalDifference.applyP
#print axioms DPExtensions.TemporalDifference.dsq_nonneg
#print axioms DPExtensions.TemporalDifference.dinner_self
#print axioms DPExtensions.TemporalDifference.dinner_comm
#print axioms DPExtensions.TemporalDifference.dsq_add
#print axioms DPExtensions.TemporalDifference.dsq_smul
#print axioms DPExtensions.TemporalDifference.dinner_le
#print axioms DPExtensions.TemporalDifference.jensen_sq
#print axioms DPExtensions.TemporalDifference.dsq_applyP_le
#print axioms DPExtensions.TemporalDifference.dinner_applyP_le
#print axioms DPExtensions.TemporalDifference.dsq_bellman_sub_le
#print axioms DPExtensions.TemporalDifference.vθ
#print axioms DPExtensions.TemporalDifference.vθ_sub
#print axioms DPExtensions.TemporalDifference.vθ_smul
#print axioms DPExtensions.TemporalDifference.dsq_vθ_pos
#print axioms DPExtensions.TemporalDifference.exists_gram_lower
#print axioms DPExtensions.TemporalDifference.meanField
#print axioms DPExtensions.TemporalDifference.meanFieldLin
#print axioms DPExtensions.TemporalDifference.meanField_sub
#print axioms DPExtensions.TemporalDifference.inner_meanFieldLin
#print axioms DPExtensions.TemporalDifference.meanField_lyapunov
#print axioms DPExtensions.TemporalDifference.meanField_lipschitz
#print axioms DPExtensions.TemporalDifference.exists_unique_fixedPoint
#print axioms DPExtensions.TemporalDifference.dinner_add_left
#print axioms DPExtensions.TemporalDifference.inner_meanField
#print axioms DPExtensions.TemporalDifference.best_approx
#print axioms DPExtensions.TemporalDifference.exists_best_approx
#print axioms DPExtensions.TemporalDifference.tvr_bound
#print axioms DPExtensions.TemporalDifference.tdStep
#print axioms DPExtensions.TemporalDifference.meanField_eq_sum
#print axioms DPExtensions.TemporalDifference.continuous_tdStep
#print axioms DPExtensions.TemporalDifference.continuous_meanField
#print axioms DPExtensions.TemporalDifference.norm_tdStep_le
#print axioms DPExtensions.TemporalDifference.td_converges

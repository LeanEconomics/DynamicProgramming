import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.PSeries
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
/-!
# The Robbins–Siegmund lemma

Robbins and Siegmund (1971), "A convergence theorem for non negative almost supermartingales
and some applications". Copied from the `GeneralStates/ApproximationAndLearning` project.

* `robbins_siegmund`: a nonnegative adapted process with
  `𝔼[Y_{k+1} | ℱ_k] ≤ (1 + a_k)Y_k + b_k − c_k`, `∑ a_k, ∑ b_k < ∞`, converges almost surely and
  `∑ c_k < ∞` almost surely, by the martingale convergence theorem applied to a rescaled
  supermartingale.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace DPExtensions.AdaptiveLearning

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

end DPExtensions.AdaptiveLearning

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

No contraction is assumed, and the step sizes need not be below `1`.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace DPExtensions.AdaptiveLearning

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

end DPExtensions.AdaptiveLearning

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Learning in the cobweb model

Muth (1961), Bray and Savin (1986), Evans and Honkapohja (2001, Ch. 2).

The reduced form of a market whose supply depends on the expected price is
`p_t = μ + βp^e_t + η_t`. The rational expectations equilibrium (REE) forecast is
`p̄ = μ/(1 − β)`. Agents who do not know `μ` and `β` forecast with the sample mean of past prices,
recursively `a_{t+1} = a_t + γ_t(p_t − a_t)` with `p^e_t = a_t` (steady-state learning). With the
decreasing gain `γ_t = 1/(t + 1)` this is least squares on a constant.

* `cobweb_learning`: if `β < 1` (E-stability), the forecasts `a_t → p̄` almost surely, for any
  step sizes with `∑ γ_t = ∞`, `∑ γ_t² < ∞`. The map `a ↦ μ + βa` need not be a contraction: for
  `β < −1` it expands distances, and learning still converges.
* `learning_eq`, `learning_diverges`: without noise, the forecast error is multiplied by
  `1 + γ_t(β − 1)` each period, so for `β > 1` (E-instability) learning moves away from the REE
  from any other start.
* `harmonic_gain`, `recursive_mean`: the gain `1/(t + 1)` satisfies the Robbins–Monro conditions,
  and with it `a_{t+1}` is the sample mean of `p_0, …, p_t`.
* `naive_eq`, `naive_diverges`: under naive expectations `p^e_t = p_{t−1}` the deviation from the
  REE is `β^t(p_0 − p̄)`, which explodes for `|β| > 1`.
* `cobweb_market`: from primitives — demand `q = A − b p`, supply `q = s₀ + s p^e + ε`, with
  `b, s > 0` — the reduced form has `β = −s/b < 0`, so least-squares learning always converges to
  the REE, while naive expectations diverge whenever `s > b` (the cobweb theorem).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace DPExtensions.AdaptiveLearning

/-! ### Deterministic dynamics -/

/-- Naive expectations: `p_{t+1} = μ + βp_t` gives `p_t − p̄ = β^t(p_0 − p̄)`. -/
theorem naive_eq {μ β : ℝ} (hβ : β ≠ 1) {p : ℕ → ℝ} (hrec : ∀ t, p (t + 1) = μ + β * p t)
    (t : ℕ) : p t - μ / (1 - β) = β ^ t * (p 0 - μ / (1 - β)) := by
  have h1 : (1 - β) ≠ 0 := sub_ne_zero.2 (Ne.symm hβ)
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hrec, pow_succ]
    have e : μ + β * p t - μ / (1 - β) = β * (p t - μ / (1 - β)) := by
      field_simp
      ring
    rw [e, ih]
    ring

/-- Under naive expectations the cobweb explodes when `|β| > 1`, from any start other than the
REE. -/
theorem naive_diverges {μ β : ℝ} (hβ : 1 < |β|) {p : ℕ → ℝ}
    (hrec : ∀ t, p (t + 1) = μ + β * p t) (hp0 : p 0 ≠ μ / (1 - β)) :
    Tendsto (fun t => |p t - μ / (1 - β)|) atTop atTop := by
  have hβ1 : β ≠ 1 := fun h => by rw [h, abs_one] at hβ; exact lt_irrefl _ hβ
  have e : (fun t => |p t - μ / (1 - β)|) = fun t => |β| ^ t * |p 0 - μ / (1 - β)| :=
    funext fun t => by rw [naive_eq hβ1 hrec, abs_mul, abs_pow]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hβ).atTop_mul_const
    (abs_pos.2 (sub_ne_zero.2 hp0))

/-- Without noise, steady-state learning multiplies the forecast error by `1 + γ_t(β − 1)`. -/
theorem learning_eq {μ β : ℝ} (hβ : β ≠ 1) {γ a : ℕ → ℝ}
    (hrec : ∀ t, a (t + 1) = a t + γ t * (μ + β * a t - a t)) (t : ℕ) :
    a t - μ / (1 - β) = (∏ s ∈ Finset.range t, (1 + γ s * (β - 1))) * (a 0 - μ / (1 - β)) := by
  have h1 : (1 - β) ≠ 0 := sub_ne_zero.2 (Ne.symm hβ)
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hrec, Finset.prod_range_succ]
    have e : a t + γ t * (μ + β * a t - a t) - μ / (1 - β) =
        (1 + γ t * (β - 1)) * (a t - μ / (1 - β)) := by
      field_simp
      ring
    rw [e, ih]
    ring

/-- `∏ (1 + x_s) ≥ 1 + ∑ x_s` for `x_s ≥ 0`. -/
theorem one_add_sum_le_prod {x : ℕ → ℝ} (hx : ∀ s, 0 ≤ x s) (t : ℕ) :
    1 + ∑ s ∈ Finset.range t, x s ≤ ∏ s ∈ Finset.range t, (1 + x s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have h0 : 0 ≤ ∑ s ∈ Finset.range t, x s := Finset.sum_nonneg fun s _ => hx s
    nlinarith [hx t]

/-- **E-instability**: for `β > 1` and `∑ γ_t = ∞`, noiseless learning moves away from the REE
from any other start: `|a_t − p̄| → ∞`. -/
theorem learning_diverges {μ β : ℝ} (hβ : 1 < β) {γ a : ℕ → ℝ} (hγ0 : ∀ t, 0 ≤ γ t)
    (hdiv : ¬ Summable γ) (hrec : ∀ t, a (t + 1) = a t + γ t * (μ + β * a t - a t))
    (ha0 : a 0 ≠ μ / (1 - β)) :
    Tendsto (fun t => |a t - μ / (1 - β)|) atTop atTop := by
  have hβ1 : β ≠ 1 := ne_of_gt hβ
  have hx : ∀ s, 0 ≤ γ s * (β - 1) := fun s => mul_nonneg (hγ0 s) (by linarith)
  have hS : Tendsto (fun t => ∑ s ∈ Finset.range t, γ s * (β - 1)) atTop atTop := by
    have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hγ0).1 hdiv
    have e : (fun t => ∑ s ∈ Finset.range t, γ s * (β - 1)) =
        fun t => (∑ s ∈ Finset.range t, γ s) * (β - 1) :=
      funext fun t => (Finset.sum_mul _ _ _).symm
    rw [e]
    exact h.atTop_mul_const (by linarith)
  have hprod : Tendsto (fun t => ∏ s ∈ Finset.range t, (1 + γ s * (β - 1))) atTop atTop :=
    tendsto_atTop_mono (fun t => (one_add_sum_le_prod hx t).trans' (by linarith))
      (tendsto_atTop_add_const_left _ 1 hS)
  have e : (fun t => |a t - μ / (1 - β)|) =
      fun t => (∏ s ∈ Finset.range t, (1 + γ s * (β - 1))) * |a 0 - μ / (1 - β)| := by
    funext t
    rw [learning_eq hβ1 hrec, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun s _ => by
      linarith [hx s])]
  rw [e]
  exact hprod.atTop_mul_const (abs_pos.2 (sub_ne_zero.2 ha0))

/-- The least-squares gain `γ_t = 1/(t + 1)` satisfies the Robbins–Monro conditions. -/
theorem harmonic_gain : (∀ t : ℕ, 0 ≤ 1 / ((t : ℝ) + 1)) ∧
    (¬ Summable fun t : ℕ => 1 / ((t : ℝ) + 1)) ∧
    Summable fun t : ℕ => (1 / ((t : ℝ) + 1)) ^ 2 := by
  refine ⟨fun t => by positivity, fun hs => ?_, ?_⟩
  · exact not_tendsto_atTop_of_tendsto_nhds hs.hasSum.tendsto_sum_nat
      Real.tendsto_sum_range_one_div_nat_succ_atTop
  · have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    refine h.congr fun t => ?_
    push_cast
    rw [div_pow, one_pow]

/-- With the gain `1/(t + 1)`, steady-state learning is least squares on a constant: the forecast
`a_{t+1}` is the sample mean of `p_0, …, p_t`. -/
theorem recursive_mean {a p : ℕ → ℝ}
    (hrec : ∀ t, a (t + 1) = a t + 1 / ((t : ℝ) + 1) * (p t - a t)) (t : ℕ) :
    a (t + 1) = (∑ s ∈ Finset.range (t + 1), p s) / ((t : ℝ) + 1) := by
  induction t with
  | zero => rw [hrec]; simp
  | succ t ih =>
    rw [hrec, ih, Finset.sum_range_succ _ (t + 1)]
    push_cast
    field_simp
    ring

/-! ### Stochastic learning -/

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℕ m0}

/-- **Learnability of the cobweb REE** (Bray and Savin, 1986; Evans and Honkapohja, 2001):
with `p_t = μ + βa_t + η_t`, `a_{t+1} = a_t + γ_t(p_t − a_t)`, `β < 1`, noise `η_t` that is
`ℱ_{t+1}`-measurable, square integrable, with `𝔼[η_t | ℱ_t] = 0` and `𝔼[η_t² | ℱ_t] ≤ σ²`, and
`γ_t ≥ 0` with `∑ γ_t = ∞`, `∑ γ_t² < ∞`, the forecasts converge to `μ/(1 − β)` almost
surely. -/
theorem cobweb_learning {μ β : ℝ} (hβ : β < 1) {γ : ℕ → ℝ} (hγ0 : ∀ t, 0 ≤ γ t)
    (hdiv : ¬ Summable γ) (hsq : Summable fun t => γ t ^ 2) {a p η : ℕ → Ω → ℝ}
    (hp : ∀ t ω, p t ω = μ + β * a t ω + η t ω)
    (hrec : ∀ t ω, a (t + 1) ω = a t ω + γ t * (p t ω - a t ω))
    (ha0m : StronglyMeasurable[ℱ 0] (a 0)) (ha0 : MemLp (a 0) 2 P)
    (hηm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (η t)) (hη2 : ∀ t, MemLp (η t) 2 P)
    (hη0 : ∀ t, P[η t | ℱ t] =ᵐ[P] 0) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    (hησ : ∀ t, P[fun ω => η t ω ^ 2 | ℱ t] ≤ᵐ[P] fun _ => σ2) :
    ∀ᵐ ω ∂P, Tendsto (fun t => a t ω) atTop (𝓝 (μ / (1 - β))) := by
  have h1 : (1 - β) ≠ 0 := by linarith
  have hh : ∀ x : ℝ, μ + β * x - x = (β - 1) * (x - μ / (1 - β)) := fun x => by
    field_simp
    ring
  refine sa_lyapunov (ℱ := ℱ) (h := fun x : ℝ => μ + β * x - x) (by fun_prop)
    (Q := ContinuousLinearMap.id ℝ ℝ) (fun x y => rfl) (m := 1) (κ := 1 - β)
    (L := |β - 1|) one_pos (by linarith) (fun x => ?_) (fun x => ?_) (fun x => ?_) hγ0 hdiv hsq
    (W := η) (fun t ω => ?_) ha0m ha0 hηm hη2 hη0 hσ (fun t => ?_)
  · simp
  · simp only [ContinuousLinearMap.id_apply, hh x, Real.norm_eq_abs]
    have : inner ℝ (x - μ / (1 - β)) ((β - 1) * (x - μ / (1 - β))) =
        (β - 1) * (x - μ / (1 - β)) ^ 2 := by
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    rw [this, sq_abs]
    linarith
  · rw [hh x, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  · rw [hrec, hp, smul_eq_mul]
    ring
  · filter_upwards [hησ t] with ω hω
    have e : (fun ω => ‖η t ω‖ ^ 2) = fun ω => η t ω ^ 2 :=
      funext fun ω => by rw [Real.norm_eq_abs, sq_abs]
    rw [e]
    refine hω.trans ?_
    nlinarith [sq_nonneg ‖a t ω‖]

/-- **The cobweb model from primitives.** Demand `q = A − b p` and supply
`q = s₀ + s a_t + ε_t` (`b, s > 0`), with market clearing, give `p_t = μ + βa_t + η_t` with
`β = −s/b < 0`. So least-squares learning converges to the REE almost surely, while naive
expectations diverge when `s > b`. -/
theorem cobweb_market {A s₀ b s : ℝ} (hb : 0 < b) (hs : 0 < s) {γ : ℕ → ℝ}
    (hγ0 : ∀ t, 0 ≤ γ t) (hdiv : ¬ Summable γ) (hsq : Summable fun t => γ t ^ 2)
    {a p ε : ℕ → Ω → ℝ} (hclear : ∀ t ω, A - b * p t ω = s₀ + s * a t ω + ε t ω)
    (hrec : ∀ t ω, a (t + 1) ω = a t ω + γ t * (p t ω - a t ω))
    (ha0m : StronglyMeasurable[ℱ 0] (a 0)) (ha0 : MemLp (a 0) 2 P)
    (hεm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (ε t)) (hε2 : ∀ t, MemLp (ε t) 2 P)
    (hε0 : ∀ t, P[ε t | ℱ t] =ᵐ[P] 0) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    (hεσ : ∀ t, P[fun ω => ε t ω ^ 2 | ℱ t] ≤ᵐ[P] fun _ => σ2) :
    (∀ᵐ ω ∂P, Tendsto (fun t => a t ω) atTop (𝓝 ((A - s₀) / b / (1 - -(s / b))))) ∧
      (b < s → ∀ q : ℕ → ℝ, (∀ t, q (t + 1) = (A - s₀) / b + -(s / b) * q t) →
        q 0 ≠ (A - s₀) / b / (1 - -(s / b)) →
        Tendsto (fun t => |q t - (A - s₀) / b / (1 - -(s / b))|) atTop atTop) := by
  have hb0 : b ≠ 0 := hb.ne'
  refine ⟨?_, fun hbs q hq hq0 => naive_diverges ?_ hq hq0⟩
  · refine cobweb_learning (β := -(s / b)) (by have := div_pos hs hb; linarith) hγ0 hdiv hsq
      (η := fun t ω => -b⁻¹ * ε t ω) (fun t ω => ?_) hrec ha0m ha0
      (fun t => stronglyMeasurable_const.mul (hεm t)) (fun t => (hε2 t).const_mul _)
      (fun t => ?_) (σ2 := b⁻¹ ^ 2 * σ2) (by positivity) (fun t => ?_)
    · field_simp
      linarith [hclear t ω]
    · have e : (fun ω => -b⁻¹ * ε t ω) = (-b⁻¹) • ε t := rfl
      rw [e]
      filter_upwards [condExp_smul (μ := P) (-b⁻¹) (ε t) (ℱ t), hε0 t] with ω h1 h2
      rw [h1, Pi.smul_apply, h2, Pi.zero_apply, smul_zero]
    · have e : (fun ω => (-b⁻¹ * ε t ω) ^ 2) = (b⁻¹ ^ 2) • fun ω => ε t ω ^ 2 := by
        funext ω
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      filter_upwards [condExp_smul (μ := P) (b⁻¹ ^ 2) (fun ω => ε t ω ^ 2) (ℱ t), hεσ t]
        with ω h1 h2
      rw [h1, Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  · rw [abs_neg, abs_div, abs_of_pos hs, abs_of_pos hb, one_lt_div hb]
    exact hbs

end DPExtensions.AdaptiveLearning

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

set_option linter.style.longLine false
#print axioms DPExtensions.AdaptiveLearning.robbins_siegmund
#print axioms DPExtensions.AdaptiveLearning.sa_lyapunov
#print axioms DPExtensions.AdaptiveLearning.naive_eq
#print axioms DPExtensions.AdaptiveLearning.naive_diverges
#print axioms DPExtensions.AdaptiveLearning.learning_eq
#print axioms DPExtensions.AdaptiveLearning.one_add_sum_le_prod
#print axioms DPExtensions.AdaptiveLearning.learning_diverges
#print axioms DPExtensions.AdaptiveLearning.harmonic_gain
#print axioms DPExtensions.AdaptiveLearning.recursive_mean
#print axioms DPExtensions.AdaptiveLearning.cobweb_learning
#print axioms DPExtensions.AdaptiveLearning.cobweb_market
#print axioms DPExtensions.AdaptiveLearning.IsEStable
#print axioms DPExtensions.AdaptiveLearning.isEStable_of_inner_le
#print axioms DPExtensions.AdaptiveLearning.isEStable_of_opNorm_lt_one
#print axioms DPExtensions.AdaptiveLearning.not_isEStable_of_eigen
#print axioms DPExtensions.AdaptiveLearning.isEStable_smul_iff
#print axioms DPExtensions.AdaptiveLearning.ree_unique
#print axioms DPExtensions.AdaptiveLearning.ree_existsUnique
#print axioms DPExtensions.AdaptiveLearning.learning_diverges_of_eigen
#print axioms DPExtensions.AdaptiveLearning.estable_learning

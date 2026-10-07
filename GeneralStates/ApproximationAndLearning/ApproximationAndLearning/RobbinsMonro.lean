/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The Robbins–Monro algorithm

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.1.3.2–9.1.3.3 (pp. 305–306).

The Robbins–Monro iteration (9.14) is `θ_{k+1} = θ_k + α_k(Tθ_k + W_{k+1} − θ_k)`.
Theorem 9.1.8 (from Tsitsiklis, 1994) asserts almost sure convergence to the fixed point of an
order-preserving contraction `T` on `Θ ⊆ ℝⁿ` under (i) `𝔼[W_{k+1} | ℱ_k] = 0`,
(ii) `𝔼[‖W_{k+1}‖² | ℱ_k] ≤ C(1 + ‖θ_k‖²)` and (iii) the Robbins–Monro conditions
`∑ α_k = ∞`, `∑ α_k² < ∞`.

We prove the theorem when `T` is a contraction of a real Hilbert space for its own norm (for
`ℝⁿ`, the Euclidean norm), with `Θ` the whole space; order preservation is then not needed.
The proof is the classical one:

* `robbins_siegmund`: a nonnegative adapted process with
  `𝔼[Y_{k+1} | ℱ_k] ≤ (1 + a_k)Y_k + b_k − c_k`, `∑ a_k, ∑ b_k < ∞`, converges almost surely and
  `∑ c_k < ∞` almost surely (Robbins and Siegmund, 1971), by the martingale convergence theorem
  applied to a rescaled supermartingale;
* `robbins_monro`: `Y_k = ‖θ_k − θ̄‖²` satisfies this with `a_k = 2Cα_k²`, `b_k ∝ α_k²` and
  `c_k = (1 − β)α_kY_k`, so `Y_k → Y_∞` and `∑ α_kY_k < ∞`, which forces `Y_∞ = 0`.

The supremum-norm case, which the book's applications need, is `theorem_9_1_8` in `Tsitsiklis`.

The asynchronous version (Remark 9.1.3) and contractions for the supremum norm (as in the
asset pricing and Q-learning applications) are not covered.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ApproximationAndLearning

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Theorem 9.1.8** (p. 306) for contractions of a real Hilbert space: let `T` be a contraction
of modulus `β < 1` with fixed point `θ̄`, and let `θ_{k+1} = θ_k + α_k(Tθ_k + W_{k+1} − θ_k)`
(9.14) with `θ₀` and the `W_k` square integrable and adapted. If (i) `𝔼[W_{k+1} | ℱ_k] = 0`,
(ii) `𝔼[‖W_{k+1}‖² | ℱ_k] ≤ C(1 + ‖θ_k‖²)` and (iii) `α_k ∈ [0, 1]`, `∑ α_k = ∞`,
`∑ α_k² < ∞`, then `θ_k → θ̄` almost surely. -/
theorem robbins_monro {T : E → E} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hT : ∀ x y, ‖T x - T y‖ ≤ β * ‖x - y‖) {θbar : E} (hfix : T θbar = θbar)
    {α : ℕ → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hα1 : ∀ k, α k ≤ 1) (hdiv : ¬ Summable α)
    (hsq : Summable fun k => α k ^ 2) {θ W : ℕ → Ω → E}
    (hrec : ∀ k ω, θ (k + 1) ω = θ k ω + α k • (T (θ k ω) + W (k + 1) ω - θ k ω))
    (hθ0m : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0 : MemLp (θ 0) 2 P)
    (hWm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (W (k + 1))) (hW2 : ∀ k, MemLp (W (k + 1)) 2 P)
    (hW0 : ∀ k, P[W (k + 1) | ℱ k] =ᵐ[P] 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k, P[fun ω => ‖W (k + 1) ω‖ ^ 2 | ℱ k] ≤ᵐ[P] fun ω => C * (1 + ‖θ k ω‖ ^ 2)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => θ k ω) atTop (𝓝 θbar) := by
  have hTc : Continuous T := (LipschitzWith.of_dist_le_mul (K := ⟨β, hβ0⟩) fun x y => by
    rw [dist_eq_norm, dist_eq_norm]
    exact hT x y).continuous
  have hTb : ∀ x, ‖T x‖ ≤ ‖T 0‖ + β * ‖x‖ := fun x => by
    have := hT x 0
    rw [sub_zero] at this
    linarith [norm_le_norm_add_norm_sub' (T x) (T 0), norm_sub_rev (T x) (T 0)]
  -- adaptedness and square integrability of the iterates
  have hθ : ∀ k, StronglyMeasurable[ℱ k] (θ k) ∧ MemLp (θ k) 2 P := by
    intro k
    induction k with
    | zero => exact ⟨hθ0m, hθ0⟩
    | succ k ih =>
      obtain ⟨hm, hL⟩ := ih
      have he : θ (k + 1) = fun ω => θ k ω + α k • (T (θ k ω) + W (k + 1) ω - θ k ω) :=
        funext (hrec k)
      have hm' : StronglyMeasurable[ℱ (k + 1)] (θ k) := hm.mono (ℱ.mono k.le_succ)
      have hTm : StronglyMeasurable[ℱ (k + 1)] fun ω => T (θ k ω) :=
        hTc.comp_stronglyMeasurable hm'
      have hTL : MemLp (fun ω => T (θ k ω)) 2 P :=
        ((memLp_const ‖T 0‖).add (hL.norm.const_mul β)).mono'
          (hTc.comp_aestronglyMeasurable hL.aestronglyMeasurable) (Eventually.of_forall fun ω => by
            simp only [Pi.add_apply]
            exact hTb _)
      rw [he]
      exact ⟨hm'.add (((hTm.add (hWm k)).sub hm').const_smul (α k)),
        hL.add (((hTL.add (hW2 k)).sub hL).const_smul (α k))⟩
  -- `Y_k = ‖θ_k − θ̄‖²`
  set Y : ℕ → Ω → ℝ := fun k ω => ‖θ k ω - θbar‖ ^ 2 with hYdef
  have hYm : StronglyAdapted ℱ Y := fun k =>
    ((hθ k).1.sub stronglyMeasurable_const).norm.pow 2
  have hYi : ∀ k, Integrable (Y k) P := fun k =>
    (memLp_two_iff_integrable_sq_norm
      ((hθ k).2.sub (memLp_const θbar)).aestronglyMeasurable).1
      ((hθ k).2.sub (memLp_const θbar))
  have hY0 : ∀ k ω, 0 ≤ Y k ω := fun k ω => sq_nonneg _
  set c : ℕ → Ω → ℝ := fun k ω => (1 - β) * α k * Y k ω with hcdef
  set a : ℕ → ℝ := fun k => 2 * C * α k ^ 2
  set b : ℕ → ℝ := fun k => C * (1 + 2 * ‖θbar‖ ^ 2) * α k ^ 2
  have hstep : ∀ k, P[Y (k + 1) | ℱ k] ≤ᵐ[P] fun ω => (1 + a k) * Y k ω + b k - c k ω := by
    intro k
    set u : Ω → E := fun ω => θ k ω - θbar + α k • (T (θ k ω) - θ k ω)
    have hum : StronglyMeasurable[ℱ k] u :=
      ((hθ k).1.sub stronglyMeasurable_const).add
        (((hTc.comp_stronglyMeasurable (hθ k).1).sub (hθ k).1).const_smul (α k))
    have huL : MemLp u 2 P := by
      have hTL : MemLp (fun ω => T (θ k ω)) 2 P :=
        ((memLp_const ‖T 0‖).add ((hθ k).2.norm.const_mul β)).mono'
          (hTc.comp_aestronglyMeasurable (hθ k).2.aestronglyMeasurable)
          (Eventually.of_forall fun ω => by
            simp only [Pi.add_apply]
            exact hTb _)
      exact ((hθ k).2.sub (memLp_const θbar)).add ((hTL.sub (hθ k).2).const_smul (α k))
    have hsplit : ∀ ω, θ (k + 1) ω - θbar = u ω + α k • W (k + 1) ω := fun ω => by
      rw [hrec]
      simp only [u, smul_sub, smul_add]
      abel
    -- the three pieces of `Y_{k+1}`
    set U : Ω → ℝ := fun ω => ‖u ω‖ ^ 2
    set I : Ω → ℝ := fun ω => innerSL ℝ (u ω) (W (k + 1) ω)
    set N : Ω → ℝ := fun ω => ‖W (k + 1) ω‖ ^ 2
    have hYsplit : Y (k + 1) = U + (2 * α k) • I + (α k ^ 2) • N := by
      funext ω
      simp only [hYdef, U, I, N, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsplit,
        innerSL_apply_apply]
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have hUi : Integrable U P := (memLp_two_iff_integrable_sq_norm huL.aestronglyMeasurable).1 huL
    have hNi : Integrable N P := (memLp_two_iff_integrable_sq_norm (hW2 k).aestronglyMeasurable).1
      (hW2 k)
    have hIi : Integrable I P := by
      refine (hUi.add hNi).mono' ?_ (Eventually.of_forall fun ω => ?_)
      · exact ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous₂.comp_aestronglyMeasurable₂
          huL.aestronglyMeasurable (hW2 k).aestronglyMeasurable)
      · simp only [I, Pi.add_apply, U, N, innerSL_apply_apply, Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        nlinarith [sq_nonneg (‖u ω‖ - ‖W (k + 1) ω‖), norm_nonneg (u ω),
          norm_nonneg (W (k + 1) ω)]
    have hUm : StronglyMeasurable[ℱ k] U := hum.norm.pow 2
    have hcI : P[I | ℱ k] =ᵐ[P] 0 := by
      have h1 := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
        hum.aestronglyMeasurable hIi ((hW2 k).integrable one_le_two)
      filter_upwards [h1, hW0 k] with ω h1 h2
      rw [h1, h2]
      simp
    rw [hYsplit]
    have hsum := condExp_add (hUi.add (hIi.smul (2 * α k))) (hNi.smul (α k ^ 2)) (ℱ k)
    have hsum2 := condExp_add hUi (hIi.smul (2 * α k)) (ℱ k)
    have hs1 := condExp_smul (μ := P) (2 * α k) I (ℱ k)
    have hs2 := condExp_smul (μ := P) (α k ^ 2) N (ℱ k)
    have hU := condExp_of_stronglyMeasurable (ℱ.le k) hUm hUi
    filter_upwards [hsum, hsum2, hs1, hs2, hcI, hC k] with ω e1 e2 e3 e4 e5 e6
    have e6' : P[N | ℱ k] ω ≤ C * (1 + ‖θ k ω‖ ^ 2) := e6
    rw [e1, Pi.add_apply, e2, Pi.add_apply, hU, e3, e4, Pi.smul_apply, Pi.smul_apply, e5,
      smul_eq_mul, smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
    -- `‖u‖ ≤ (1 − α(1 − β))‖θ_k − θ̄‖`
    have hq0 : 0 ≤ 1 - α k * (1 - β) := by nlinarith [hα1 k, hα0 k]
    have hq1 : 1 - α k * (1 - β) ≤ 1 := by nlinarith [hα0 k]
    have hu : ‖u ω‖ ≤ (1 - α k * (1 - β)) * ‖θ k ω - θbar‖ := by
      have e : u ω = (1 - α k) • (θ k ω - θbar) + α k • (T (θ k ω) - T θbar) := by
        rw [hfix]
        simp only [u, smul_sub, sub_smul, one_smul]
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hα1 k]),
        Real.norm_of_nonneg (hα0 k)]
      nlinarith [mul_le_mul_of_nonneg_left (hT (θ k ω) θbar) (hα0 k),
        norm_nonneg (θ k ω - θbar)]
    have hU' : U ω ≤ (1 - α k * (1 - β)) * Y k ω := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hu 2
      simp only [U, hYdef]
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hq0 hq1)
        (sq_nonneg ‖θ k ω - θbar‖), sq_nonneg (1 - α k * (1 - β))]
    have hθsq : ‖θ k ω‖ ^ 2 ≤ 2 * Y k ω + 2 * ‖θbar‖ ^ 2 := by
      have h1 : ‖θ k ω‖ ≤ ‖θ k ω - θbar‖ + ‖θbar‖ := by
        have := norm_add_le (θ k ω - θbar) θbar
        rwa [sub_add_cancel] at this
      simp only [hYdef]
      nlinarith [sq_nonneg (‖θ k ω - θbar‖ - ‖θbar‖), norm_nonneg (θ k ω),
        norm_nonneg (θ k ω - θbar), norm_nonneg θbar]
    simp only [a, b, hcdef]
    nlinarith [mul_le_mul_of_nonneg_left e6' (sq_nonneg (α k)),
      mul_le_mul_of_nonneg_left hθsq (mul_nonneg (sq_nonneg (α k)) hC0)]
  -- Robbins–Siegmund
  have hcad : StronglyAdapted ℱ c := fun k => stronglyMeasurable_const.mul (hYm k)
  have hci : ∀ k, Integrable (c k) P := fun k => (hYi k).const_mul _
  have hc0 : ∀ k ω, 0 ≤ c k ω := fun k ω =>
    mul_nonneg (mul_nonneg (sub_nonneg.2 hβ1.le) (hα0 k)) (hY0 k ω)
  have ha : ∀ k, 0 ≤ a k := fun k => mul_nonneg (mul_nonneg zero_le_two hC0) (sq_nonneg _)
  have hb : ∀ k, 0 ≤ b k := fun k =>
    mul_nonneg (mul_nonneg hC0 (by positivity)) (sq_nonneg _)
  have hRS := robbins_siegmund hYm hcad hYi hci hY0 hc0 ha hb (hsq.mul_left (2 * C))
    (hsq.mul_left _) hstep
  filter_upwards [hRS] with ω hω
  obtain ⟨⟨L, hL⟩, hcs⟩ := hω
  have hL0 : L = 0 := by
    have hLnn : 0 ≤ L := ge_of_tendsto' hL fun k => hY0 k ω
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hLnn (Ne.symm hne)
    have hev : ∀ᶠ k in atTop, L / 2 < Y k ω := hL.eventually (lt_mem_nhds (half_lt_self hLpos))
    have h1b : 0 < 1 - β := sub_pos.2 hβ1
    apply hdiv
    refine Summable.of_norm_bounded_eventually (hcs.mul_left (2 / ((1 - β) * L))) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with k hk
    rw [Real.norm_eq_abs, abs_of_nonneg (hα0 k), div_mul_eq_mul_div,
      le_div_iff₀ (mul_pos h1b hLpos)]
    simp only [hcdef]
    nlinarith [mul_le_mul_of_nonneg_left hk.le (mul_nonneg h1b.le (hα0 k))]
  rw [hL0] at hL
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : (fun k => ‖θ k ω - θbar‖) = fun k => Real.sqrt (Y k ω) :=
    funext fun k => (Real.sqrt_sq (norm_nonneg _)).symm
  rw [e]
  have h := (Real.continuous_sqrt.tendsto 0).comp hL
  rw [Real.sqrt_zero] at h
  exact h

end SargentStachurski.ApproximationAndLearning

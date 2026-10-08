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

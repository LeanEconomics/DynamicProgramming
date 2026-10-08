/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ApproximationAndLearning.RobbinsMonro

/-!
# Stochastic approximation for max-norm contractions (Tsitsiklis, 1994)

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Theorem 9.1.8 and Remark 9.1.3
(p. 306), following Tsitsiklis (1994), "Asynchronous stochastic approximation and Q-learning".

The iterates live in `ℝ^ι` (`ι` finite) with the supremum norm, and each component is updated
with its own adapted step size (zero when the component is not updated):
`x_i(t + 1) = x_i(t) + α_i(t)(F_i(x(t)) − x_i(t) + w_i(t))`.

* `robbins_siegmund_rand`: a Robbins–Siegmund lemma with random adapted perturbations `b_k` whose
  partial sums are bounded by a constant.
* `tendsto_prod_one_sub`: `∏_{τ=s}^{t−1}(1 − α_τ) → 0` when `∑ α = ∞`.
* `noiseAverage_tendsto_zero`: the noise average `W(t + 1) = (1 − α_t)W(t) + α_t w_t` tends to `0`
  almost surely when `𝔼[w_t | ℱ_t] = 0`, `𝔼[w_t² | ℱ_t] ≤ A`, `∑ α_t = ∞` and `∑ α_t² ≤ C`.
* `det_converge`: along a path with bounded iterates and vanishing noise averages, a
  pseudo-contraction's iterates converge, by shrinking the box `‖x − x*‖ ≤ D` by `(1 + β)/2`.
* `det_bounded`: if the averages of the noise rescaled by the scale `G(t)` (`scale`) vanish, the
  iterates are bounded.
* `tsitsiklis`: almost sure boundedness and convergence when
  `𝔼[w_i(t)² | ℱ_t] ≤ A + B‖x(t)‖²`, with the rescaled noise for boundedness and the noise
  truncated at `M(t) ≤ K` (`runMax`) for convergence.
* `theorem_9_1_8`: Theorem 9.1.8 for supremum-norm contractions.
* `sampled_tsitsiklis`: updates towards sampled targets with a known conditional law, the form of
  (9.15), (9.16) and Q-learning.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ApproximationAndLearning

/-- The noise average `W(0) = 0`, `W(t + 1) = (1 − α_t)W(t) + α_t w_t` along a path. -/
def navg (a w : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (1 - a t) * navg a w t + a t * w t

@[simp] theorem navg_zero (a w : ℕ → ℝ) : navg a w 0 = 0 := rfl

theorem navg_succ (a w : ℕ → ℝ) (t : ℕ) :
    navg a w (t + 1) = (1 - a t) * navg a w t + a t * w t := rfl

/-- `∏_{τ=s}^{t−1}(1 − a_τ) → 0` when `a_τ ∈ [0, 1]` and `∑ a = ∞`. -/
theorem tendsto_prod_one_sub {a : ℕ → ℝ} (h0 : ∀ t, 0 ≤ a t) (h1 : ∀ t, a t ≤ 1)
    (hdiv : ¬ Summable a) (s : ℕ) :
    Tendsto (fun t => ∏ τ ∈ Finset.Ico s t, (1 - a τ)) atTop (𝓝 0) := by
  have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg h0).1 hdiv
  have hIco : Tendsto (fun t => ∑ τ ∈ Finset.Ico s t, a τ) atTop atTop := by
    have : Tendsto (fun t => ∑ τ ∈ Finset.range t, a τ - ∑ τ ∈ Finset.range s, a τ) atTop
        atTop := tendsto_atTop_add_const_right _ _ hsum
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop s] with t ht
    rw [Finset.sum_Ico_eq_sub _ ht]
  have hexp : Tendsto (fun t => Real.exp (-∑ τ ∈ Finset.Ico s t, a τ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hIco
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
    (fun t => Finset.prod_nonneg fun τ _ => sub_nonneg.2 (h1 τ)) fun t => ?_
  calc ∏ τ ∈ Finset.Ico s t, (1 - a τ) ≤ ∏ τ ∈ Finset.Ico s t, Real.exp (-a τ) :=
        Finset.prod_le_prod₀ (fun τ _ => sub_nonneg.2 (h1 τ)) fun τ _ => by
          linarith [Real.add_one_le_exp (-a τ)]
    _ = Real.exp (-∑ τ ∈ Finset.Ico s t, a τ) := by
        rw [← Real.exp_sum, Finset.sum_neg_distrib]

theorem prod_one_sub_mem {a : ℕ → ℝ} (h0 : ∀ t, 0 ≤ a t) (h1 : ∀ t, a t ≤ 1) (s t : ℕ) :
    0 ≤ ∏ τ ∈ Finset.Ico s t, (1 - a τ) ∧ ∏ τ ∈ Finset.Ico s t, (1 - a τ) ≤ 1 :=
  ⟨Finset.prod_nonneg fun τ _ => sub_nonneg.2 (h1 τ),
    Finset.prod_le_one₀ (fun τ _ => sub_nonneg.2 (h1 τ)) fun τ _ => by linarith [h0 τ]⟩

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℕ m0}

/-- The partial sums of an adapted process up to `k − 1` are `ℱ_i`-measurable for `k ≤ i + 1`. -/
theorem stronglyMeasurable_partialSum {f : ℕ → Ω → ℝ} (hf : StronglyAdapted ℱ f) {k i : ℕ}
    (hki : k ≤ i + 1) : StronglyMeasurable[ℱ i] fun ω => ∑ j ∈ Finset.range k, f j ω := by
  have h := Finset.stronglyMeasurable_sum (f := f) (Finset.range k) fun j hj =>
    (hf j).mono (ℱ.mono (show j ≤ i by have := Finset.mem_range.1 hj; omega))
  convert h using 1
  funext ω
  simp [Finset.sum_apply]

/-- **Robbins–Siegmund lemma** with random perturbations: if `Y, b, c ≥ 0` are adapted and
integrable, `∑_{k<T} b_k ≤ B` everywhere and `𝔼[Y_{k+1} | ℱ_k] ≤ Y_k + b_k − c_k`, then almost
surely `Y_k` converges and `∑ c_k < ∞`. -/
theorem robbins_siegmund_rand {Y b c : ℕ → Ω → ℝ} {B : ℝ}
    (hY : StronglyAdapted ℱ Y) (hb : StronglyAdapted ℱ b) (hc : StronglyAdapted ℱ c)
    (hYi : ∀ k, Integrable (Y k) P) (hbi : ∀ k, Integrable (b k) P)
    (hci : ∀ k, Integrable (c k) P) (hY0 : ∀ k ω, 0 ≤ Y k ω) (hb0 : ∀ k ω, 0 ≤ b k ω)
    (hc0 : ∀ k ω, 0 ≤ c k ω) (hB : ∀ ω T, ∑ k ∈ Finset.range T, b k ω ≤ B)
    (hstep : ∀ k, P[Y (k + 1) | ℱ k] ≤ᵐ[P] fun ω => Y k ω + b k ω - c k ω) :
    ∀ᵐ ω ∂P, (∃ L, Tendsto (fun k => Y k ω) atTop (𝓝 L)) ∧ Summable fun k => c k ω := by
  set Sc : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range k, c j ω with hScdef
  set Sb : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range k, b j ω with hSbdef
  have hSci : ∀ k, Integrable (Sc k) P := fun k => integrable_finsetSum _ fun j _ => hci j
  have hSbi : ∀ k, Integrable (Sb k) P := fun k => integrable_finsetSum _ fun j _ => hbi j
  have hSc0 : ∀ k ω, 0 ≤ Sc k ω := fun k ω => Finset.sum_nonneg fun j _ => hc0 j ω
  -- the supermartingale `Z_k = Y_k + ∑_{j<k} c_j − ∑_{j<k} b_j`
  set Z : ℕ → Ω → ℝ := fun k ω => Y k ω + Sc k ω - Sb k ω with hZdef
  have hZad : StronglyAdapted ℱ Z := fun k =>
    ((hY k).add (stronglyMeasurable_partialSum hc (by omega))).sub
      (stronglyMeasurable_partialSum hb (by omega))
  have hZi : ∀ k, Integrable (Z k) P := fun k => ((hYi k).add (hSci k)).sub (hSbi k)
  have hsup : Supermartingale Z ℱ P := supermartingale_nat hZad hZi fun k => by
    set R : Ω → ℝ := fun ω => Sc (k + 1) ω - Sb (k + 1) ω
    have hRm : StronglyMeasurable[ℱ k] R :=
      (stronglyMeasurable_partialSum hc le_rfl).sub (stronglyMeasurable_partialSum hb le_rfl)
    have hRi : Integrable R P := (hSci (k + 1)).sub (hSbi (k + 1))
    have hsplit : Z (k + 1) = Y (k + 1) + R := by
      funext ω
      simp only [hZdef, R, Pi.add_apply]
      ring
    rw [hsplit]
    filter_upwards [condExp_add (hYi (k + 1)) hRi (ℱ k), hstep k] with ω h1 h2
    rw [h1, Pi.add_apply, condExp_of_stronglyMeasurable (ℱ.le k) hRm hRi]
    simp only [R, hScdef, hSbdef, hZdef, Finset.sum_range_succ]
    linarith
  have hZlow : ∀ k ω, -B ≤ Z k ω := fun k ω => by
    simp only [hZdef]
    linarith [hY0 k ω, hSc0 k ω, hB ω k]
  have hint : ∀ k, ∫ ω, Z k ω ∂P ≤ ∫ ω, Z 0 ω ∂P := fun k => by
    have := hsup.setIntegral_le (Nat.zero_le k) MeasurableSet.univ
    simpa only [Measure.restrict_univ] using this
  have hbdd : ∀ k, eLpNorm ((-Z) k) 1 P ≤ ENNReal.ofReal (∫ ω, Z 0 ω ∂P + 2 * B) := by
    intro k
    rw [Pi.neg_apply, eLpNorm_neg, eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hZi k)]
    · refine ENNReal.ofReal_le_ofReal ?_
      calc ∫ ω, ‖Z k ω‖ ∂P ≤ ∫ ω, (Z k ω + 2 * B) ∂P := integral_mono (hZi k).norm
            ((hZi k).add (integrable_const _)) fun ω => by
            have hB0 : 0 ≤ B := by simpa using hB ω 0
            rw [Real.norm_eq_abs, abs_le]
            constructor <;> linarith [hZlow k ω]
        _ = ∫ ω, Z k ω ∂P + 2 * B := by
            rw [integral_add (hZi k) (integrable_const _)]
            simp
        _ ≤ _ := by linarith [hint k]
    · exact (hZi k).aestronglyMeasurable
  filter_upwards [hsup.neg.ae_tendsto_limitProcess hbdd] with ω hω
  have hZω : Tendsto (fun k => Z k ω) atTop (𝓝 (-ℱ.limitProcess (-Z) P ω)) := by
    have := hω.neg
    simpa using this
  -- `∑_{j<k} b_j` converges (monotone and bounded)
  have hSbmono : Monotone fun k => Sb k ω := monotone_nat_of_le_succ fun k => by
    simp only [hSbdef, Finset.sum_range_succ]
    linarith [hb0 k ω]
  obtain ⟨lb, hlb⟩ : ∃ l, Tendsto (fun k => Sb k ω) atTop (𝓝 l) :=
    ⟨_, tendsto_atTop_ciSup hSbmono ⟨B, by rintro _ ⟨k, rfl⟩; exact hB ω k⟩⟩
  have hW : Tendsto (fun k => Y k ω + Sc k ω) atTop
      (𝓝 (-ℱ.limitProcess (-Z) P ω + lb)) := by
    have e : (fun k => Y k ω + Sc k ω) = fun k => Z k ω + Sb k ω := funext fun k => by
      simp only [hZdef]
      ring
    rw [e]
    exact hZω.add hlb
  obtain ⟨M, hM⟩ := hW.bddAbove_range
  have hcs : Summable fun k => c k ω :=
    summable_of_sum_range_le (fun k => hc0 k ω) fun n =>
      le_trans (le_add_of_nonneg_left (hY0 n ω)) (hM ⟨n, rfl⟩)
  have hSclim : Tendsto (fun k => Sc k ω) atTop (𝓝 (∑' j, c j ω)) := hcs.hasSum.tendsto_sum_nat
  have hYlim : Tendsto (fun k => Y k ω) atTop
      (𝓝 (-ℱ.limitProcess (-Z) P ω + lb - ∑' j, c j ω)) := by
    have := hW.sub hSclim
    simpa using this
  exact ⟨⟨_, hYlim⟩, hcs⟩

/-- **Noise averaging** (Tsitsiklis, 1994, Lemma 1): if `α_t ∈ [0, 1]` is adapted with
`∑_{t<T} α_t² ≤ C` everywhere and `∑ α_t = ∞` almost surely, and the noise `w_t` is
`ℱ_{t+1}`-measurable, square integrable, with `𝔼[w_t | ℱ_t] = 0` and `𝔼[w_t² | ℱ_t] ≤ A`, then
the noise average `W(t + 1) = (1 − α_t)W(t) + α_t w_t`, `W(0) = 0`, tends to `0` almost surely. -/
theorem noiseAverage_tendsto_zero {α w : ℕ → Ω → ℝ} {A C : ℝ} (hA : 0 ≤ A)
    (hαm : ∀ t, StronglyMeasurable[ℱ t] (α t)) (hα0 : ∀ t ω, 0 ≤ α t ω)
    (hα1 : ∀ t ω, α t ω ≤ 1) (hαsq : ∀ ω T, ∑ t ∈ Finset.range T, α t ω ^ 2 ≤ C)
    (hαdiv : ∀ᵐ ω ∂P, ¬ Summable fun t => α t ω)
    (hwm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (w t)) (hw2 : ∀ t, MemLp (w t) 2 P)
    (hw0 : ∀ t, P[w t | ℱ t] =ᵐ[P] 0)
    (hwA : ∀ t, P[fun ω => w t ω ^ 2 | ℱ t] ≤ᵐ[P] fun _ => A) :
    ∀ᵐ ω ∂P, Tendsto (navg (fun t => α t ω) (fun t => w t ω)) atTop (𝓝 0) := by
  set W : ℕ → Ω → ℝ := fun t ω => navg (fun t => α t ω) (fun t => w t ω) t with hWdef
  have hWsucc : ∀ t, W (t + 1) = fun ω => (1 - α t ω) * W t ω + α t ω * w t ω := fun t => rfl
  have hWm : ∀ t, StronglyMeasurable[ℱ t] (W t) := by
    intro t
    induction t with
    | zero => exact stronglyMeasurable_const
    | succ t ih =>
      rw [hWsucc]
      exact ((stronglyMeasurable_const.sub ((hαm t).mono (ℱ.mono t.le_succ))).mul
        (ih.mono (ℱ.mono t.le_succ))).add (((hαm t).mono (ℱ.mono t.le_succ)).mul (hwm t))
  have hWL : ∀ t, MemLp (W t) 2 P := by
    intro t
    induction t with
    | zero => exact memLp_const 0
    | succ t ih =>
      refine (ih.norm.add (hw2 t).norm).mono' ((hWm (t + 1)).mono (ℱ.le _)).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [hWsucc]
      simp only [Pi.add_apply, Real.norm_eq_abs]
      have h1 := hα0 t ω
      have h2 := hα1 t ω
      calc |(1 - α t ω) * W t ω + α t ω * w t ω|
          ≤ |(1 - α t ω) * W t ω| + |α t ω * w t ω| := abs_add_le _ _
        _ = (1 - α t ω) * |W t ω| + α t ω * |w t ω| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg h1]
        _ ≤ |W t ω| + |w t ω| := by nlinarith [abs_nonneg (W t ω), abs_nonneg (w t ω)]
  have hsqint : ∀ {f : Ω → ℝ}, MemLp f 2 P → Integrable (fun ω => f ω ^ 2) P := fun hf => by
    have := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
    simpa [Real.norm_eq_abs, sq_abs] using this
  -- `Y = W²`, `b = α²A`, `c = αW²`
  set Y : ℕ → Ω → ℝ := fun t ω => W t ω ^ 2
  set b : ℕ → Ω → ℝ := fun t ω => α t ω ^ 2 * A
  set c : ℕ → Ω → ℝ := fun t ω => α t ω * W t ω ^ 2
  have hstep : ∀ t, P[Y (t + 1) | ℱ t] ≤ᵐ[P] fun ω => Y t ω + b t ω - c t ω := by
    intro t
    set U : Ω → ℝ := fun ω => (1 - α t ω) ^ 2 * W t ω ^ 2
    set f1 : Ω → ℝ := fun ω => 2 * α t ω * (1 - α t ω) * W t ω
    set f2 : Ω → ℝ := fun ω => α t ω ^ 2
    set w2 : Ω → ℝ := fun ω => w t ω ^ 2
    have hsplit : Y (t + 1) = U + f1 * w t + f2 * w2 := by
      funext ω
      simp only [Y, U, f1, f2, w2, Pi.add_apply, Pi.mul_apply, hWsucc]
      ring
    have hUm : StronglyMeasurable[ℱ t] U :=
      ((stronglyMeasurable_const.sub (hαm t)).pow 2).mul ((hWm t).pow 2)
    have hf1m : StronglyMeasurable[ℱ t] f1 :=
      ((stronglyMeasurable_const.mul (hαm t)).mul (stronglyMeasurable_const.sub (hαm t))).mul
        (hWm t)
    have hf2m : StronglyMeasurable[ℱ t] f2 := (hαm t).pow 2
    have hWi := hsqint (hWL t)
    have hwi := hsqint (hw2 t)
    have hUi : Integrable U P := hWi.mono' (hUm.mono (ℱ.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        simp only [U, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        have h1 := hα0 t ω
        have h2 := hα1 t ω
        have : (1 - α t ω) ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg (W t ω)])
    have hf1i : Integrable (f1 * w t) P := (hWi.add hwi).mono'
      ((hf1m.mono (ℱ.le t)).mul ((hwm t).mono (ℱ.le _))).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        simp only [f1, Pi.mul_apply, Real.norm_eq_abs, Pi.add_apply]
        have h1 := hα0 t ω
        have h2 := hα1 t ω
        have hk : 0 ≤ 2 * α t ω * (1 - α t ω) ∧ 2 * α t ω * (1 - α t ω) ≤ 1 :=
          ⟨by nlinarith, by nlinarith [sq_nonneg (2 * α t ω - 1)]⟩
        rw [abs_mul, abs_mul, abs_of_nonneg hk.1]
        nlinarith [abs_nonneg (W t ω), abs_nonneg (w t ω), sq_abs (W t ω), sq_abs (w t ω),
          sq_nonneg (|W t ω| - |w t ω|), mul_nonneg hk.1 (mul_nonneg (abs_nonneg (W t ω))
            (abs_nonneg (w t ω)))])
    have hf2i : Integrable (f2 * w2) P := hwi.mono'
      (hf2m.mono (ℱ.le t) |>.aestronglyMeasurable.mul hwi.aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        simp only [f2, w2, Pi.mul_apply, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        have h1 := hα0 t ω
        have h2 := hα1 t ω
        have : α t ω ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg (w t ω)])
    rw [hsplit]
    filter_upwards [condExp_add (hUi.add hf1i) hf2i (ℱ t), condExp_add hUi hf1i (ℱ t),
      condExp_mul_of_stronglyMeasurable_left hf1m hf1i ((hw2 t).integrable one_le_two),
      condExp_mul_of_stronglyMeasurable_left hf2m hf2i hwi, hw0 t, hwA t]
      with ω e1 e2 e3 e4 e5 e6
    rw [e1, Pi.add_apply, e2, Pi.add_apply, condExp_of_stronglyMeasurable (ℱ.le t) hUm hUi,
      e3, e4, Pi.mul_apply, Pi.mul_apply, e5, Pi.zero_apply, mul_zero, add_zero]
    have h1 := hα0 t ω
    have h2 := hα1 t ω
    have e6' : P[w2 | ℱ t] ω ≤ A := e6
    simp only [U, f2, Y, b, c]
    nlinarith [mul_le_mul_of_nonneg_left e6' (sq_nonneg (α t ω)), sq_nonneg (W t ω),
      mul_le_mul_of_nonneg_right (show α t ω ^ 2 ≤ α t ω by nlinarith) (sq_nonneg (W t ω))]
  have hYad : StronglyAdapted ℱ Y := fun t => (hWm t).pow 2
  have hbad : StronglyAdapted ℱ b := fun t => ((hαm t).pow 2).mul stronglyMeasurable_const
  have hcad : StronglyAdapted ℱ c := fun t => (hαm t).mul ((hWm t).pow 2)
  have hbi : ∀ t, Integrable (b t) P := fun t =>
    (integrable_const A).mono' ((hbad t).mono (ℱ.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        simp only [b, Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hA)]
        have : α t ω ^ 2 ≤ 1 := by nlinarith [hα0 t ω, hα1 t ω]
        nlinarith)
  have hci : ∀ t, Integrable (c t) P := fun t =>
    (hsqint (hWL t)).mono' ((hcad t).mono (ℱ.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        simp only [c, Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (hα0 t ω) (sq_nonneg _))]
        nlinarith [hα1 t ω, sq_nonneg (W t ω)])
  have hRS := robbins_siegmund_rand (B := C * A) hYad hbad hcad (fun t => hsqint (hWL t)) hbi
    hci (fun t ω => sq_nonneg _) (fun t ω => mul_nonneg (sq_nonneg _) hA)
    (fun t ω => mul_nonneg (hα0 t ω) (sq_nonneg _)) (fun ω T => by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hαsq ω T) hA) hstep
  filter_upwards [hRS, hαdiv] with ω hω hdiv
  obtain ⟨⟨L, hL⟩, hcs⟩ := hω
  have hL0 : L = 0 := by
    have hLnn : 0 ≤ L := ge_of_tendsto' hL fun t => sq_nonneg _
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hLnn (Ne.symm hne)
    have hev : ∀ᶠ t in atTop, L / 2 < Y t ω := hL.eventually (lt_mem_nhds (half_lt_self hLpos))
    apply hdiv
    refine Summable.of_norm_bounded_eventually (hcs.mul_left (2 / L)) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hα0 t ω), div_mul_eq_mul_div, le_div_iff₀ hLpos]
    simp only [c]
    nlinarith [mul_le_mul_of_nonneg_left ht.le (hα0 t ω)]
  rw [hL0] at hL
  have h := (Real.continuous_sqrt.tendsto 0).comp hL
  rw [Real.sqrt_zero] at h
  have e : (fun t => Real.sqrt (Y t ω)) = fun t => |W t ω| :=
    funext fun t => Real.sqrt_sq_eq_abs _
  have h' : Tendsto (fun t => |W t ω|) atTop (𝓝 0) := by
    rw [← e]
    exact h
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h'

/-! ### Deterministic path arguments -/

/-- The restarted noise average: `navg(t) − ∏_{τ=s}^{t−1}(1 − a_τ) navg(s)` obeys the same
recursion from `0` at time `s`. -/
theorem navg_restart (a w : ℕ → ℝ) {s t : ℕ} (hst : s ≤ t) :
    navg a w (t + 1) - (∏ τ ∈ Finset.Ico s (t + 1), (1 - a τ)) * navg a w s =
      (1 - a t) * (navg a w t - (∏ τ ∈ Finset.Ico s t, (1 - a τ)) * navg a w s) +
        a t * w t := by
  rw [Finset.prod_Ico_succ_top hst, navg_succ]
  ring

variable {ι : Type*} [Fintype ι]

/-- Convergence once bounded (Tsitsiklis, 1994, §4): along a path where every component is
updated with `∑_t a_i(t) = ∞`, the iterates are bounded and the noise averages tend to `0`, the
iterates of a pseudo-contraction `‖F(y) − x*‖ ≤ β‖y − x*‖` converge to `x*`. The proof shrinks
the box `‖x(t) − x*‖ ≤ D` by the factor `(1 + β)/2` at each stage. -/
theorem det_converge {F : (ι → ℝ) → ι → ℝ} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {xs : ι → ℝ} (hF : ∀ y, ‖F y - xs‖ ≤ β * ‖y - xs‖) {x : ℕ → ι → ℝ} {a w : ι → ℕ → ℝ}
    (ha0 : ∀ i t, 0 ≤ a i t) (ha1 : ∀ i t, a i t ≤ 1) (hdiv : ∀ i, ¬ Summable (a i))
    (hrec : ∀ t i, x (t + 1) i = x t i + a i t * (F (x t) i - x t i + w i t))
    {K : ℝ} (hK : ∀ t, ‖x t - xs‖ ≤ K) (hW : ∀ i, Tendsto (navg (a i) (w i)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 xs) := by
  set K' := max K 1
  have hK'pos : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set γ := (1 + β) / 2
  have hγ0 : 0 ≤ γ := by positivity
  have hγ1 : γ < 1 := by simp only [γ]; linarith
  have hβγ : β < γ := by simp only [γ]; linarith
  have hstage : ∀ k : ℕ, ∃ T, ∀ t, T ≤ t → ‖x t - xs‖ ≤ γ ^ k * K' := by
    intro k
    induction k with
    | zero => exact ⟨0, fun t _ => by rw [pow_zero, one_mul]; exact (hK t).trans (le_max_left _ _)⟩
    | succ k ih =>
      obtain ⟨T, hT⟩ := ih
      set D := γ ^ k * K'
      have hD : 0 < D := mul_pos (pow_pos (lt_of_le_of_lt hβ0 hβγ) k) hK'pos
      have hcomp : ∀ i, ∀ᶠ t in atTop, |x t i - xs i| ≤ γ * D := by
        intro i
        set pr : ℕ → ℝ := fun t => ∏ τ ∈ Finset.Ico T t, (1 - a i τ)
        set V : ℕ → ℝ := fun t => navg (a i) (w i) t - pr t * navg (a i) (w i) T
        have hu : ∀ t, T ≤ t → |(x t i - xs i) - V t| ≤ β * D + pr t * (D - β * D) := by
          intro t ht
          induction t, ht using Nat.le_induction with
          | base =>
            simp only [V, pr, Finset.Ico_self, Finset.prod_empty, one_mul, sub_self, sub_zero]
            have := (norm_le_pi_norm (x T - xs) i).trans (hT T le_rfl)
            rw [Pi.sub_apply, Real.norm_eq_abs] at this
            linarith
          | succ t ht ih =>
            have hpr : pr (t + 1) = pr t * (1 - a i t) := Finset.prod_Ico_succ_top ht _
            have hV : V (t + 1) = (1 - a i t) * V t + a i t * w i t := navg_restart _ _ ht
            have hFi : |F (x t) i - xs i| ≤ β * D := by
              have h1 := (norm_le_pi_norm (F (x t) - xs) i).trans (hF (x t))
              rw [Pi.sub_apply, Real.norm_eq_abs] at h1
              exact h1.trans (mul_le_mul_of_nonneg_left (hT t ht) hβ0)
            have e : (x (t + 1) i - xs i) - V (t + 1) =
                (1 - a i t) * ((x t i - xs i) - V t) + a i t * (F (x t) i - xs i) := by
              rw [hV, hrec]
              ring
            rw [e, hpr]
            have h1 := ha0 i t
            have h2 := ha1 i t
            calc |(1 - a i t) * ((x t i - xs i) - V t) + a i t * (F (x t) i - xs i)|
                ≤ (1 - a i t) * |(x t i - xs i) - V t| + a i t * |F (x t) i - xs i| := by
                  refine (abs_add_le _ _).trans ?_
                  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - a i t),
                    abs_of_nonneg h1]
              _ ≤ (1 - a i t) * (β * D + pr t * (D - β * D)) + a i t * (β * D) :=
                  add_le_add (mul_le_mul_of_nonneg_left ih (by linarith))
                    (mul_le_mul_of_nonneg_left hFi h1)
              _ = β * D + pr t * (1 - a i t) * (D - β * D) := by ring
        have hprlim : Tendsto pr atTop (𝓝 0) :=
          tendsto_prod_one_sub (ha0 i) (ha1 i) (hdiv i) T
        have hVlim : Tendsto V atTop (𝓝 0) := by
          have := (hW i).sub (hprlim.mul_const (navg (a i) (w i) T))
          simpa using this
        have hbound : Tendsto (fun t => β * D + pr t * (D - β * D) + |V t|) atTop
            (𝓝 (β * D + 0 * (D - β * D) + |0|)) :=
          (tendsto_const_nhds.add (hprlim.mul_const _)).add hVlim.abs
        rw [zero_mul, add_zero, abs_zero, add_zero] at hbound
        have hlt : β * D < γ * D := mul_lt_mul_of_pos_right hβγ hD
        filter_upwards [hbound.eventually (gt_mem_nhds hlt), eventually_ge_atTop T] with t h1 h2
        have h3 := hu t h2
        have h4 : |x t i - xs i| ≤ |(x t i - xs i) - V t| + |V t| := by
          have := abs_add_le ((x t i - xs i) - V t) (V t)
          rwa [sub_add_cancel] at this
        linarith
      obtain ⟨T', hT'⟩ := eventually_atTop.1 (Filter.eventually_all.2 hcomp)
      refine ⟨T', fun t ht => ?_⟩
      have hγD : 0 ≤ γ ^ (k + 1) * K' := by positivity
      refine (pi_norm_le_iff_of_nonneg hγD).2 fun i => ?_
      rw [Pi.sub_apply, Real.norm_eq_abs, pow_succ, mul_comm (γ ^ k) γ, mul_assoc]
      exact hT' t ht i
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hK'pos) hγ1
  obtain ⟨T, hT⟩ := hstage k
  refine ⟨T, fun t ht => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (hT t ht) ?_
  rwa [lt_div_iff₀ hK'pos] at hk

/-- The running maximum `M(t) = max_{τ ≤ t} ‖x(τ)‖`. -/
noncomputable def runMax (x : ℕ → ι → ℝ) : ℕ → ℝ
  | 0 => ‖x 0‖
  | t + 1 => max (runMax x t) ‖x (t + 1)‖

/-- The scale `G(t)` of Tsitsiklis (1994, §3): `G(0) = max(G₀, ‖x(0)‖)`, kept fixed while
`M(t + 1) ≤ (1 + ε)G(t)` and reset to `M(t + 1)` otherwise. -/
noncomputable def scale (ε G0 : ℝ) (x : ℕ → ι → ℝ) : ℕ → ℝ
  | 0 => max G0 ‖x 0‖
  | t + 1 => if runMax x (t + 1) ≤ (1 + ε) * scale ε G0 x t then scale ε G0 x t
      else runMax x (t + 1)

theorem norm_le_runMax (x : ℕ → ι → ℝ) (t : ℕ) : ‖x t‖ ≤ runMax x t := by
  cases t with
  | zero => exact le_rfl
  | succ t => exact le_max_right _ _

theorem runMax_le_succ (x : ℕ → ι → ℝ) (t : ℕ) : runMax x t ≤ runMax x (t + 1) :=
  le_max_left _ _

theorem runMax_nonneg (x : ℕ → ι → ℝ) (t : ℕ) : 0 ≤ runMax x t :=
  (norm_nonneg _).trans (norm_le_runMax x t)

theorem runMax_le {x : ℕ → ι → ℝ} {K : ℝ} (h : ∀ t, ‖x t‖ ≤ K) (t : ℕ) : runMax x t ≤ K := by
  induction t with
  | zero => exact h 0
  | succ t ih => exact max_le ih (h (t + 1))

theorem scale_succ (ε G0 : ℝ) (x : ℕ → ι → ℝ) (t : ℕ) :
    scale ε G0 x (t + 1) = if runMax x (t + 1) ≤ (1 + ε) * scale ε G0 x t then scale ε G0 x t
      else runMax x (t + 1) := rfl

theorem le_scale {ε G0 : ℝ} (hε : 0 ≤ ε) (hG0 : 0 ≤ G0) (x : ℕ → ι → ℝ) (t : ℕ) :
    G0 ≤ scale ε G0 x t ∧ scale ε G0 x t ≤ scale ε G0 x (t + 1) ∧
      runMax x t ≤ (1 + ε) * scale ε G0 x t := by
  induction t with
  | zero =>
    refine ⟨le_max_left _ _, ?_, ?_⟩
    · rw [scale_succ]
      split_ifs with h
      · exact le_rfl
      · have : 0 ≤ scale ε G0 x 0 := hG0.trans (le_max_left _ _)
        nlinarith
    · have h1 : runMax x 0 ≤ scale ε G0 x 0 := le_max_right _ _
      have : 0 ≤ scale ε G0 x 0 := hG0.trans (le_max_left _ _)
      nlinarith
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have h4 : runMax x (t + 1) ≤ (1 + ε) * scale ε G0 x (t + 1) := by
      rw [scale_succ]
      split_ifs with h
      · exact h
      · have := runMax_nonneg x (t + 1)
        nlinarith
    refine ⟨h1.trans h2, ?_, h4⟩
    rw [scale_succ ε G0 x (t + 1)]
    split_ifs with h
    · exact le_rfl
    · have : 0 ≤ scale ε G0 x (t + 1) := hG0.trans (h1.trans h2)
      nlinarith

/-- Boundedness (Tsitsiklis, 1994, Lemma 2), deterministic part: if the noise averages
`W̃_i` of the rescaled noise `w_i(t)/G(t)` tend to `0`, the iterates are bounded. After the
time `t₀` from which `|W̃_i| ≤ ε/2`, the scale `G` can be reset at most once more: once
`‖x(s)‖ ≤ G(s) = g` with `s ≥ t₀`, `|x_i(t) − gV_i(t)| ≤ g` for the restarted averages `V_i`,
so `‖x(t)‖ ≤ (1 + ε)g` and `G(t) = g` for all `t ≥ s`. -/
theorem det_bounded {F : (ι → ℝ) → ι → ℝ} {β : ℝ} (hβ0 : 0 ≤ β) {xs : ι → ℝ}
    (hF : ∀ y, ‖F y - xs‖ ≤ β * ‖y - xs‖) {x : ℕ → ι → ℝ} {a w : ι → ℕ → ℝ}
    (ha0 : ∀ i t, 0 ≤ a i t) (ha1 : ∀ i t, a i t ≤ 1)
    (hrec : ∀ t i, x (t + 1) i = x t i + a i t * (F (x t) i - x t i + w i t))
    {ε G0 : ℝ} (hε : 0 < ε) (hG0 : 0 < G0) (hβε : β * (1 + ε) * G0 + (1 + β) * ‖xs‖ ≤ G0)
    (hW : ∀ i, Tendsto (navg (a i) fun t => w i t / scale ε G0 x t) atTop (𝓝 0)) :
    ∃ K, ∀ t, ‖x t‖ ≤ K := by
  set G := scale ε G0 x
  have hGp := le_scale hε.le hG0.le x
  have hGmono : Monotone G := monotone_nat_of_le_succ fun t => (hGp t).2.1
  have hFb : ∀ y, ‖F y‖ ≤ β * ‖y‖ + (1 + β) * ‖xs‖ := by
    intro y
    have h1 : ‖F y‖ ≤ ‖F y - xs‖ + ‖xs‖ := norm_le_norm_sub_add _ _
    have h2 : ‖y - xs‖ ≤ ‖y‖ + ‖xs‖ := norm_sub_le _ _
    nlinarith [hF y]
  have hβε' : 0 ≤ 1 - β * (1 + ε) := by
    have := norm_nonneg xs
    by_contra h
    push Not at h
    nlinarith
  have hW' : ∀ i, ∀ᶠ t in atTop, |navg (a i) (fun t => w i t / G t) t| < ε / 2 := by
    intro i
    have := (hW i).abs
    rw [abs_zero] at this
    exact this.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨t0, ht0⟩ := eventually_atTop.1 (Filter.eventually_all.2 hW')
  -- once `‖x(s)‖ ≤ G(s)` after `t₀`, `G` stays at `G(s)`
  have key : ∀ s, t0 ≤ s → ‖x s‖ ≤ G s → ∀ t, s ≤ t → G t = G s := by
    intro s hs hxs
    set g := G s
    have hg : 0 < g := lt_of_lt_of_le hG0 (hGp s).1
    set V : ι → ℕ → ℝ := fun i t => navg (a i) (fun t => w i t / G t) t -
      (∏ τ ∈ Finset.Ico s t, (1 - a i τ)) * navg (a i) (fun t => w i t / G t) s
    have hVb : ∀ i t, s ≤ t → |V i t| ≤ ε := by
      intro i t ht
      obtain ⟨hp0, hp1⟩ := prod_one_sub_mem (ha0 i) (ha1 i) s t
      have h1 := ht0 t (hs.trans ht) i
      have h2 := ht0 s hs i
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hp0]
      nlinarith [abs_nonneg (navg (a i) (fun t => w i t / G t) s)]
    have hxb : ∀ t, s ≤ t → (∀ i, |x t i - g * V i t| ≤ g) → ‖x t‖ ≤ (1 + ε) * g := by
      intro t ht h
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      have h1 : |x t i| ≤ |x t i - g * V i t| + |g * V i t| := by
        have := abs_add_le (x t i - g * V i t) (g * V i t)
        rwa [sub_add_cancel] at this
      rw [abs_mul, abs_of_pos hg] at h1
      nlinarith [h i, hVb i t ht]
    have hinv : ∀ t, s ≤ t → G t = g ∧ ∀ i, |x t i - g * V i t| ≤ g := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base =>
        refine ⟨rfl, fun i => ?_⟩
        simp only [V, Finset.Ico_self, Finset.prod_empty, one_mul, sub_self, mul_zero, sub_zero]
        have := norm_le_pi_norm (x s) i
        rw [Real.norm_eq_abs] at this
        exact this.trans hxs
      | succ t ht ih =>
        obtain ⟨hGt, hcomp⟩ := ih
        have hxt := hxb t ht hcomp
        have hcomp' : ∀ i, |x (t + 1) i - g * V i (t + 1)| ≤ g := by
          intro i
          have hV : V i (t + 1) = (1 - a i t) * V i t + a i t * (w i t / G t) :=
            navg_restart _ _ ht
          have hFi : |F (x t) i| ≤ g := by
            have h1 := (norm_le_pi_norm (F (x t)) i).trans (hFb (x t))
            rw [Real.norm_eq_abs] at h1
            have h2 : β * ‖x t‖ ≤ β * ((1 + ε) * g) := mul_le_mul_of_nonneg_left hxt hβ0
            have h3 : G0 ≤ g := (hGp s).1
            nlinarith
          have e : x (t + 1) i - g * V i (t + 1) =
              (1 - a i t) * (x t i - g * V i t) + a i t * F (x t) i := by
            rw [hV, hrec, hGt]
            field_simp
            ring
          rw [e]
          have h1 := ha0 i t
          have h2 := ha1 i t
          calc |(1 - a i t) * (x t i - g * V i t) + a i t * F (x t) i|
              ≤ (1 - a i t) * |x t i - g * V i t| + a i t * |F (x t) i| := by
                refine (abs_add_le _ _).trans ?_
                rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - a i t),
                  abs_of_nonneg h1]
            _ ≤ (1 - a i t) * g + a i t * g :=
                add_le_add (mul_le_mul_of_nonneg_left (hcomp i) (by linarith))
                  (mul_le_mul_of_nonneg_left hFi h1)
            _ = g := by ring
        refine ⟨?_, hcomp'⟩
        have hx1 := hxb (t + 1) (ht.trans (Nat.le_succ t)) hcomp'
        have hM : runMax x (t + 1) ≤ (1 + ε) * G t := by
          rw [hGt]
          refine max_le ?_ hx1
          have := (hGp t).2.2
          change runMax x t ≤ (1 + ε) * G t at this
          rwa [hGt] at this
        change scale ε G0 x (t + 1) = g
        rw [scale_succ]
        split_ifs with h
        · exact hGt
        · exact absurd hM h
    exact fun t ht => (hinv t ht).1
  -- `G` is eventually constant
  have hconst : ∃ s, ∀ t, s ≤ t → G t = G s := by
    by_cases hS : ∃ s, t0 ≤ s ∧ ‖x s‖ ≤ G s
    · obtain ⟨s, hs, hxs⟩ := hS
      exact ⟨s, key s hs hxs⟩
    · push Not at hS
      refine ⟨t0, fun t ht => ?_⟩
      induction t, ht using Nat.le_induction with
      | base => rfl
      | succ t ht ih =>
        rw [← ih]
        change scale ε G0 x (t + 1) = G t
        rw [scale_succ]
        split_ifs with h
        · rfl
        · exfalso
          have h1 := hS (t + 1) (ht.trans (Nat.le_succ t))
          have h2 : scale ε G0 x (t + 1) = runMax x (t + 1) := by
            rw [scale_succ]
            exact ite_eq_right_iff.2 fun hh => absurd hh h
          have h3 := norm_le_runMax x (t + 1)
          change ‖x (t + 1)‖ > scale ε G0 x (t + 1) at h1
          linarith
  obtain ⟨s, hs⟩ := hconst
  refine ⟨(1 + ε) * G s, fun t => ?_⟩
  have h1 := (norm_le_runMax x t).trans (hGp t).2.2
  have h2 : G t ≤ G s := by
    rcases le_total t s with h | h
    · exact hGmono h
    · exact (hs t h).le
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))

/-! ### The stochastic theorem -/

omit [IsProbabilityMeasure P] in
/-- `noiseAverage_tendsto_zero` for the noise `c_t w_t` multiplied by a bounded adapted factor
`c_t`, when `c_t² v_t ≤ A'` for a conditional-variance bound `𝔼[w_t² | ℱ_t] ≤ v_t`. -/
theorem noiseAverage_mul_tendsto_zero [IsProbabilityMeasure P] {α w c v : ℕ → Ω → ℝ}
    {A' C L : ℝ} (hA' : 0 ≤ A')
    (hαm : ∀ t, StronglyMeasurable[ℱ t] (α t)) (hα0 : ∀ t ω, 0 ≤ α t ω)
    (hα1 : ∀ t ω, α t ω ≤ 1) (hαsq : ∀ ω T, ∑ t ∈ Finset.range T, α t ω ^ 2 ≤ C)
    (hαdiv : ∀ᵐ ω ∂P, ¬ Summable fun t => α t ω)
    (hwm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (w t)) (hw2 : ∀ t, MemLp (w t) 2 P)
    (hw0 : ∀ t, P[w t | ℱ t] =ᵐ[P] 0)
    (hwv : ∀ t, P[fun ω => w t ω ^ 2 | ℱ t] ≤ᵐ[P] v t)
    (hcm : ∀ t, StronglyMeasurable[ℱ t] (c t)) (hcL : ∀ t ω, |c t ω| ≤ L)
    (hcv : ∀ t ω, c t ω ^ 2 * v t ω ≤ A') :
    ∀ᵐ ω ∂P, Tendsto (navg (fun t => α t ω) (fun t => c t ω * w t ω)) atTop (𝓝 0) := by
  have hcm0 : ∀ t, StronglyMeasurable[m0] (c t) := fun t => (hcm t).mono (ℱ.le t)
  have hcw2 : ∀ t, MemLp (fun ω => c t ω * w t ω) 2 P := by
    intro t
    refine MemLp.of_le ((hw2 t).const_mul L)
      ((hcm0 t).aestronglyMeasurable.mul (hw2 t).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    have hL : 0 ≤ L := (abs_nonneg _).trans (hcL t ω)
    rw [abs_of_nonneg hL]
    exact mul_le_mul_of_nonneg_right (hcL t ω) (abs_nonneg _)
  refine noiseAverage_tendsto_zero hA' hαm hα0 hα1 hαsq hαdiv
    (fun t => ((hcm t).mono (ℱ.mono (Nat.le_succ t))).mul (hwm t)) hcw2 (fun t => ?_)
    (fun t => ?_)
  · have h := condExp_mul_of_stronglyMeasurable_left (μ := P) (hcm t)
      ((hcw2 t).integrable one_le_two) ((hw2 t).integrable one_le_two)
    filter_upwards [h, hw0 t] with ω h1 h2
    change P[c t * w t | ℱ t] ω = 0
    rw [h1, Pi.mul_apply, h2, Pi.zero_apply, mul_zero]
  · have e : (fun ω => (c t ω * w t ω) ^ 2) = c t ^ 2 * fun ω => w t ω ^ 2 := by
      funext ω
      simp only [Pi.mul_apply, Pi.pow_apply]
      ring
    have hint : Integrable (c t ^ 2 * fun ω => w t ω ^ 2) P := by
      rw [← e]
      exact (hcw2 t).integrable_sq
    have h := condExp_mul_of_stronglyMeasurable_left (μ := P) ((hcm t).pow 2) hint
      (hw2 t).integrable_sq
    filter_upwards [h, hwv t] with ω h1 h2
    rw [e, h1, Pi.mul_apply, Pi.pow_apply]
    exact (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)).trans (hcv t ω)

/-- **Tsitsiklis (1994), Theorems 1–3**: asynchronous stochastic approximation for a
max-norm pseudo-contraction. Let `F : ℝ^ι → ℝ^ι` be measurable with
`‖F(y) − x*‖_∞ ≤ β‖y − x*‖_∞`, `β < 1`, and let
`x_i(t + 1) = x_i(t) + α_i(t)(F_i(x(t)) − x_i(t) + w_i(t))`, where `x(0)` is `ℱ₀`-measurable,
`α_i(t) ∈ [0, 1]` is `ℱ_t`-measurable with `∑_t α_i(t) = ∞` almost surely and
`∑_t α_i(t)² ≤ C`, and `w_i(t)` is `ℱ_{t+1}`-measurable and square integrable with
`𝔼[w_i(t) | ℱ_t] = 0` and `𝔼[w_i(t)² | ℱ_t] ≤ A + B‖x(t)‖²`. Then almost surely the iterates
are bounded and converge to `x*`. Setting `α_i(t) = 0` when component `i` is not updated
gives the asynchronous algorithm of Remark 9.1.3. -/
theorem tsitsiklis {F : (ι → ℝ) → ι → ℝ} (hFm : Measurable F) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {xs : ι → ℝ} (hF : ∀ y, ‖F y - xs‖ ≤ β * ‖y - xs‖)
    {x : ℕ → Ω → ι → ℝ} {α w : ι → ℕ → Ω → ℝ} {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx0 : Measurable[ℱ 0] (x 0))
    (hαm : ∀ i t, Measurable[ℱ t] (α i t)) (hα0 : ∀ i t ω, 0 ≤ α i t ω)
    (hα1 : ∀ i t ω, α i t ω ≤ 1) (hαsq : ∀ i ω T, ∑ t ∈ Finset.range T, α i t ω ^ 2 ≤ C)
    (hαdiv : ∀ i, ∀ᵐ ω ∂P, ¬ Summable fun t => α i t ω)
    (hwm : ∀ i t, Measurable[ℱ (t + 1)] (w i t)) (hw2 : ∀ i t, MemLp (w i t) 2 P)
    (hw0 : ∀ i t, P[w i t | ℱ t] =ᵐ[P] 0)
    (hwv : ∀ i t, P[fun ω => w i t ω ^ 2 | ℱ t] ≤ᵐ[P] fun ω => A + B * ‖x t ω‖ ^ 2)
    (hrec : ∀ t ω i, x (t + 1) ω i = x t ω i + α i t ω * (F (x t ω) i - x t ω i + w i t ω)) :
    ∀ᵐ ω ∂P, (∃ K, ∀ t, ‖x t ω‖ ≤ K) ∧ Tendsto (fun t => x t ω) atTop (𝓝 xs) := by
  -- measurability of the iterates
  have hxm : ∀ t, Measurable[ℱ t] (x t) := by
    intro t
    induction t with
    | zero => exact hx0
    | succ t ih =>
      have ih' : Measurable[ℱ (t + 1)] (x t) := ih.mono (ℱ.mono (Nat.le_succ t)) le_rfl
      have e : x (t + 1) = fun ω i => x t ω i + α i t ω * (F (x t ω) i - x t ω i + w i t ω) :=
        funext fun ω => funext fun i => hrec t ω i
      rw [e]
      refine @Measurable.of_eval _ _ _ (ℱ (t + 1)) _ _ fun i => ?_
      have hxi : Measurable[ℱ (t + 1)] fun ω => x t ω i := (measurable_pi_apply i).comp ih'
      have hFi : Measurable[ℱ (t + 1)] fun ω => F (x t ω) i :=
        (measurable_pi_apply i).comp (hFm.comp ih')
      exact hxi.add (((hαm i t).mono (ℱ.mono (Nat.le_succ t)) le_rfl).mul
        ((hFi.sub hxi).add (hwm i t)))
  have hRm : ∀ t, Measurable[ℱ t] fun ω => runMax (fun t => x t ω) t := by
    intro t
    induction t with
    | zero => exact measurable_norm.comp (hxm 0)
    | succ t ih =>
      exact (ih.mono (ℱ.mono (Nat.le_succ t)) le_rfl).max (measurable_norm.comp (hxm (t + 1)))
  -- the rescaling constants
  set ε := (1 - β) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set q := 1 - β * (1 + ε) with hqdef
  have hq : 0 < q := by rw [hqdef, hεdef]; nlinarith
  set G0 := (1 + β) * ‖xs‖ / q + 1 with hG0def
  have hG0 : 0 < G0 := by positivity
  have hβε : β * (1 + ε) * G0 + (1 + β) * ‖xs‖ ≤ G0 := by
    have : (1 + β) * ‖xs‖ / q * q = (1 + β) * ‖xs‖ := div_mul_cancel₀ _ hq.ne'
    have h2 : G0 * q = (1 + β) * ‖xs‖ + q := by rw [hG0def, add_mul, this, one_mul]
    rw [hqdef] at h2
    nlinarith
  have hGm : ∀ t, Measurable[ℱ t] fun ω => scale ε G0 (fun t => x t ω) t := by
    intro t
    induction t with
    | zero => exact measurable_const.max (measurable_norm.comp (hxm 0))
    | succ t ih =>
      have ih' := ih.mono (ℱ.mono (Nat.le_succ t)) le_rfl
      exact Measurable.ite (measurableSet_le (hRm (t + 1)) (measurable_const.mul ih')) ih'
        (hRm (t + 1))
  have hGp := fun ω => le_scale hε.le hG0.le (fun t => x t ω)
  -- boundedness: the rescaled noise averages tend to `0`
  have hresc : ∀ i, ∀ᵐ ω ∂P, Tendsto (navg (fun t => α i t ω)
      (fun t => (scale ε G0 (fun t => x t ω) t)⁻¹ * w i t ω)) atTop (𝓝 0) := by
    intro i
    refine noiseAverage_mul_tendsto_zero (v := fun t ω => A + B * ‖x t ω‖ ^ 2)
      (A' := A * G0⁻¹ ^ 2 + B * (1 + ε) ^ 2) (L := G0⁻¹) (by positivity)
      (fun t => (hαm i t).stronglyMeasurable) (hα0 i) (hα1 i) (hαsq i) (hαdiv i)
      (fun t => (hwm i t).stronglyMeasurable) (hw2 i) (hw0 i) (hwv i)
      (fun t => (hGm t).inv.stronglyMeasurable) (fun t ω => ?_) (fun t ω => ?_)
    · have hG := (hGp ω t).1
      rw [abs_of_pos (inv_pos.2 (hG0.trans_le hG))]
      exact inv_anti₀ hG0 hG
    · have hG := (hGp ω t).1
      have hGpos : 0 < scale ε G0 (fun t => x t ω) t := hG0.trans_le hG
      have h1 : (scale ε G0 (fun t => x t ω) t)⁻¹ ^ 2 ≤ G0⁻¹ ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.2 hGpos.le) (inv_anti₀ hG0 hG) 2
      have h2 : ‖x t ω‖ * (scale ε G0 (fun t => x t ω) t)⁻¹ ≤ 1 + ε := by
        rw [← div_eq_mul_inv, div_le_iff₀ hGpos]
        exact (norm_le_runMax (fun t => x t ω) t).trans (hGp ω t).2.2
      have h3 : (‖x t ω‖ * (scale ε G0 (fun t => x t ω) t)⁻¹) ^ 2 ≤ (1 + ε) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
      calc (scale ε G0 (fun t => x t ω) t)⁻¹ ^ 2 * (A + B * ‖x t ω‖ ^ 2)
          = A * (scale ε G0 (fun t => x t ω) t)⁻¹ ^ 2 +
              B * (‖x t ω‖ * (scale ε G0 (fun t => x t ω) t)⁻¹) ^ 2 := by ring
        _ ≤ A * G0⁻¹ ^ 2 + B * (1 + ε) ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left h1 hA) (mul_le_mul_of_nonneg_left h3 hB)
  have hbdd : ∀ᵐ ω ∂P, ∃ K, ∀ t, ‖x t ω‖ ≤ K := by
    filter_upwards [ae_all_iff.2 hresc] with ω hω
    refine det_bounded hβ0 hF (fun i t => hα0 i t ω) (fun i t => hα1 i t ω)
      (fun t i => hrec t ω i) hε hG0 hβε fun i => ?_
    have e : (fun t => w i t ω / scale ε G0 (fun t => x t ω) t) =
        fun t => (scale ε G0 (fun t => x t ω) t)⁻¹ * w i t ω :=
      funext fun t => by rw [div_eq_inv_mul]
    rw [e]
    exact hω i
  -- convergence: the truncated noise averages tend to `0`
  have htrunc : ∀ K : ℕ, ∀ i, ∀ᵐ ω ∂P, Tendsto (navg (fun t => α i t ω)
      (fun t => (if runMax (fun t => x t ω) t ≤ K then (1 : ℝ) else 0) * w i t ω)) atTop
      (𝓝 0) := by
    intro K i
    refine noiseAverage_mul_tendsto_zero (v := fun t ω => A + B * ‖x t ω‖ ^ 2)
      (A' := A + B * (K : ℝ) ^ 2) (L := 1) (by positivity)
      (fun t => (hαm i t).stronglyMeasurable) (hα0 i) (hα1 i) (hαsq i) (hαdiv i)
      (fun t => (hwm i t).stronglyMeasurable) (hw2 i) (hw0 i) (hwv i)
      (fun t => (Measurable.ite (measurableSet_le (hRm t) measurable_const) measurable_const
        measurable_const).stronglyMeasurable) (fun t ω => ?_) (fun t ω => ?_)
    · split_ifs <;> norm_num
    · split_ifs with h
      · have h1 := (norm_le_runMax (fun t => x t ω) t).trans h
        have h2 : ‖x t ω‖ ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        nlinarith
      · rw [zero_pow two_ne_zero, zero_mul]
        positivity
  filter_upwards [hbdd, ae_all_iff.2 fun K => ae_all_iff.2 (htrunc K),
    ae_all_iff.2 hαdiv] with ω hb ht hd
  refine ⟨hb, ?_⟩
  obtain ⟨K0, hK0⟩ := hb
  obtain ⟨K, hK⟩ := exists_nat_ge K0
  have hR : ∀ t, runMax (fun t => x t ω) t ≤ K := fun t => (runMax_le hK0 t).trans hK
  refine det_converge hβ0 hβ1 hF (fun i t => hα0 i t ω) (fun i t => hα1 i t ω) hd
    (fun t i => hrec t ω i) (K := K0 + ‖xs‖)
    (fun t => (norm_sub_le _ _).trans (add_le_add (hK0 t) le_rfl)) fun i => ?_
  have := ht K i
  simp only [hR, ↓reduceIte, one_mul] at this
  exact this

/-- **Theorem 9.1.8** (p. 306) in the supremum norm: let `T` be a contraction of modulus
`β < 1` on `ℝ^ι` for `‖·‖_∞` with fixed point `θ̄`, and let
`θ_{k+1} = θ_k + α_k(Tθ_k + W_{k+1} − θ_k)` (9.14) (`W k` is `W_{k+1}`, `ℱ_{k+1}`-measurable).
If (i) `𝔼[W_{k+1} | ℱ_k] = 0`, (ii) `𝔼[‖W_{k+1}‖² | ℱ_k] ≤ C(1 + ‖θ_k‖²)` and (iii)
`∑ α_k = ∞`, `∑ α_k² < ∞` with `α_k ∈ [0, 1]`, then `θ_k → θ̄` almost surely. Order preservation
of `T` is not needed. -/
theorem theorem_9_1_8 {T : (ι → ℝ) → ι → ℝ} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hT : ∀ y z, ‖T y - T z‖ ≤ β * ‖y - z‖) {θbar : ι → ℝ} (hfix : T θbar = θbar)
    {θ W : ℕ → Ω → ι → ℝ} {α : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hθ0 : Measurable[ℱ 0] (θ 0)) (hWm : ∀ k, Measurable[ℱ (k + 1)] (W k))
    (hW2 : ∀ k, MemLp (W k) 2 P)
    (hW0 : ∀ k i, P[fun ω => W k ω i | ℱ k] =ᵐ[P] 0)
    (hWC : ∀ k, P[fun ω => ‖W k ω‖ ^ 2 | ℱ k] ≤ᵐ[P] fun ω => C * (1 + ‖θ k ω‖ ^ 2))
    (hα0 : ∀ k, 0 ≤ α k) (hα1 : ∀ k, α k ≤ 1) (hαdiv : ¬ Summable α)
    (hαsq : Summable fun k => α k ^ 2)
    (hrec : ∀ k ω, θ (k + 1) ω = θ k ω + α k • (T (θ k ω) + W k ω - θ k ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => θ k ω) atTop (𝓝 θbar) := by
  have hTm : Measurable T := by
    have hL : LipschitzWith ⟨β, hβ0⟩ T := LipschitzWith.of_dist_le_mul fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact hT y z
    exact hL.continuous.measurable
  have hw2 : ∀ i k, MemLp (fun ω => W k ω i) 2 P := fun i k =>
    MemLp.of_le (hW2 k)
      ((continuous_apply i).comp_aestronglyMeasurable (hW2 k).aestronglyMeasurable)
      (ae_of_all _ fun ω => norm_le_pi_norm (W k ω) i)
  refine Filter.Eventually.mono (tsitsiklis (ℱ := ℱ) (P := P) hTm hβ0 hβ1 (xs := θbar)
    (fun y => by have := hT y θbar; rwa [hfix] at this)
    (α := fun _ k _ => α k) (w := fun i k ω => W k ω i) (A := C) (B := C)
    (C := ∑' k, α k ^ 2) hC hC hθ0 (fun _ _ => measurable_const) (fun _ k _ => hα0 k)
    (fun _ k _ => hα1 k) (fun _ _ n => hαsq.sum_le_tsum _ fun _ _ => sq_nonneg _)
    (fun _ => ae_of_all _ fun _ => hαdiv) (fun i k => (measurable_pi_apply i).comp (hWm k))
    hw2 (fun i k => hW0 k i) (fun i k => ?_) (fun k ω i => ?_)) fun ω hω => hω.2
  · have hint : Integrable (fun ω => ‖W k ω‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm (hW2 k).aestronglyMeasurable).1 (hW2 k)
    have hmono := condExp_mono (m := ℱ k) (hw2 i k).integrable_sq hint
      (ae_of_all _ fun ω => by
        have := norm_le_pi_norm (W k ω) i
        rw [Real.norm_eq_abs] at this
        exact (sq_abs (W k ω i)).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) this 2))
    filter_upwards [hmono, hWC k] with ω h1 h2
    exact h1.trans (h2.trans (le_of_eq (by ring)))
  · rw [hrec k ω]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- Asynchronous stochastic approximation with **sampled updates** (the setting of (9.15),
(9.16) and Q-learning): component `i` moves towards a sample `h(x, i, Y_i)` whose
next-observation `Y_i(t)` has conditional law `K(i, ·)` whenever `α_i(t) ≠ 0`, and
`F_i(x) = ∑_y h(x, i, y)K(i, y)`. With `|h(z, i, y)| ≤ R + β‖z‖` the iterates stay bounded, the
noise `h − F` is bounded, and `tsitsiklis` gives `x(t) → x*` almost surely. -/
theorem sampled_tsitsiklis {Y : Type*} [Fintype Y] [DecidableEq Y]
    {F : (ι → ℝ) → ι → ℝ} (hFm : Measurable F) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {xs : ι → ℝ} (hF : ∀ z, ‖F z - xs‖ ≤ β * ‖z - xs‖)
    {h : (ι → ℝ) → ι → Y → ℝ} (hhm : ∀ i y, Measurable fun z => h z i y)
    {K : ι → Y → ℝ} (hK : ∀ z i, F z i = ∑ y, h z i y * K i y) (hK1 : ∀ i, ∑ y, K i y = 1)
    {R : ℝ} (hR : ∀ z i y, |h z i y| ≤ R + β * ‖z‖)
    {x : ℕ → Ω → ι → ℝ} {x0 : ι → ℝ} {α : ι → ℕ → Ω → ℝ} {Ys : ℕ → Ω → ι → Y} {C : ℝ}
    (hαm : ∀ i t, Measurable[ℱ t] (α i t)) (hα0 : ∀ i t ω, 0 ≤ α i t ω)
    (hα1 : ∀ i t ω, α i t ω ≤ 1) (hαsq : ∀ i ω T, ∑ t ∈ Finset.range T, α i t ω ^ 2 ≤ C)
    (hαdiv : ∀ i, ∀ᵐ ω ∂P, ¬ Summable fun t => α i t ω)
    (hYm : ∀ t i y, MeasurableSet[ℱ (t + 1)] {ω | Ys t ω i = y})
    (hYK : ∀ t i y, ∀ᵐ ω ∂P, α i t ω ≠ 0 →
      P[fun ω => if Ys t ω i = y then (1 : ℝ) else 0 | ℱ t] ω = K i y)
    (hx0 : ∀ ω, x 0 ω = x0)
    (hrec : ∀ t ω i, x (t + 1) ω i = x t ω i + α i t ω * (h (x t ω) i (Ys t ω i) - x t ω i)) :
    ∀ᵐ ω ∂P, Tendsto (fun t => x t ω) atTop (𝓝 xs) := by
  -- the iterates are bounded by `Q`
  set Q := max ‖x0‖ (R / (1 - β)) with hQdef
  have hβ' : 0 < 1 - β := by linarith
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (le_max_left _ _)
  have hRQ : R + β * Q ≤ Q := by
    have : R / (1 - β) ≤ Q := le_max_right _ _
    rw [div_le_iff₀ hβ'] at this
    linarith
  have hxb : ∀ t ω, ‖x t ω‖ ≤ Q := by
    intro t
    induction t with
    | zero => intro ω; rw [hx0]; exact le_max_left _ _
    | succ t ih =>
      intro ω
      refine (pi_norm_le_iff_of_nonneg hQ0).2 fun i => ?_
      rw [Real.norm_eq_abs, hrec]
      have h1 := hα0 i t ω
      have h2 := hα1 i t ω
      have h3 : |x t ω i| ≤ Q := by
        have := norm_le_pi_norm (x t ω) i
        rw [Real.norm_eq_abs] at this
        exact this.trans (ih ω)
      have h4 : |h (x t ω) i (Ys t ω i)| ≤ R + β * Q :=
        (hR _ _ _).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (ih ω) hβ0))
      have e : x t ω i + α i t ω * (h (x t ω) i (Ys t ω i) - x t ω i) =
          (1 - α i t ω) * x t ω i + α i t ω * h (x t ω) i (Ys t ω i) := by ring
      rw [e]
      calc |(1 - α i t ω) * x t ω i + α i t ω * h (x t ω) i (Ys t ω i)|
          ≤ (1 - α i t ω) * |x t ω i| + α i t ω * |h (x t ω) i (Ys t ω i)| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - α i t ω),
              abs_of_nonneg h1]
        _ ≤ (1 - α i t ω) * Q + α i t ω * (R + β * Q) :=
            add_le_add (mul_le_mul_of_nonneg_left h3 (by linarith))
              (mul_le_mul_of_nonneg_left h4 h1)
        _ ≤ Q := by nlinarith
  -- the noise `w = h − F` (zero when the component is not updated) is bounded by `Wb`
  have hFb : ∀ z, ‖F z‖ ≤ β * ‖z‖ + (1 + β) * ‖xs‖ := by
    intro z
    have h1 : ‖F z‖ ≤ ‖F z - xs‖ + ‖xs‖ := norm_le_norm_sub_add _ _
    have h2 : ‖z - xs‖ ≤ ‖z‖ + ‖xs‖ := norm_sub_le _ _
    nlinarith [hF z]
  set Wb := R + β * Q + (β * Q + (1 + β) * ‖xs‖) with hWb
  have hgb : ∀ t ω i y, |h (x t ω) i y - F (x t ω) i| ≤ Wb := by
    intro t ω i y
    have h1 := (hR (x t ω) i y).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (hxb t ω) hβ0))
    have h2 := (norm_le_pi_norm (F (x t ω)) i).trans (hFb (x t ω))
    rw [Real.norm_eq_abs] at h2
    have h3 : β * ‖x t ω‖ ≤ β * Q := mul_le_mul_of_nonneg_left (hxb t ω) hβ0
    exact (abs_sub _ _).trans (by linarith)
  set w : ι → ℕ → Ω → ℝ := fun i t ω =>
    if α i t ω = 0 then 0 else h (x t ω) i (Ys t ω i) - F (x t ω) i with hwdef
  have hwb : ∀ i t ω, |w i t ω| ≤ Wb := by
    intro i t ω
    simp only [hwdef]
    split_ifs
    · rw [abs_zero]
      exact (abs_nonneg _).trans (hgb t ω i (Ys t ω i))
    · exact hgb t ω i (Ys t ω i)
  -- measurability
  have hsample : ∀ t i, Measurable[ℱ t] (x t) →
      Measurable[ℱ (t + 1)] fun ω => h (x t ω) i (Ys t ω i) := by
    intro t i hx
    have hx' : Measurable[ℱ (t + 1)] (x t) := hx.mono (ℱ.mono (Nat.le_succ t)) le_rfl
    have e : (fun ω => h (x t ω) i (Ys t ω i)) =
        fun ω => ∑ y, if Ys t ω i = y then h (x t ω) i y else 0 :=
      funext fun ω => by simp
    rw [e]
    exact Finset.measurable_sum _ fun y _ =>
      Measurable.ite (hYm t i y) ((hhm i y).comp hx') measurable_const
  have hxm : ∀ t, Measurable[ℱ t] (x t) := by
    intro t
    induction t with
    | zero =>
      have e : x 0 = fun _ => x0 := funext hx0
      rw [e]
      exact measurable_const
    | succ t ih =>
      have ih' : Measurable[ℱ (t + 1)] (x t) := ih.mono (ℱ.mono (Nat.le_succ t)) le_rfl
      have e : x (t + 1) = fun ω i => x t ω i + α i t ω * (h (x t ω) i (Ys t ω i) - x t ω i) :=
        funext fun ω => funext fun i => hrec t ω i
      rw [e]
      refine @Measurable.of_eval _ _ _ (ℱ (t + 1)) _ _ fun i => ?_
      have hxi : Measurable[ℱ (t + 1)] fun ω => x t ω i := (measurable_pi_apply i).comp ih'
      exact hxi.add (((hαm i t).mono (ℱ.mono (Nat.le_succ t)) le_rfl).mul
        ((hsample t i ih).sub hxi))
  have hFxm : ∀ t i, Measurable[ℱ t] fun ω => F (x t ω) i := fun t i =>
    (measurable_pi_apply i).comp (hFm.comp (hxm t))
  have hwm : ∀ i t, Measurable[ℱ (t + 1)] (w i t) := by
    intro i t
    exact Measurable.ite (measurableSet_eq_fun ((hαm i t).mono (ℱ.mono (Nat.le_succ t)) le_rfl)
      measurable_const) measurable_const ((hsample t i (hxm t)).sub
        ((hFxm t i).mono (ℱ.mono (Nat.le_succ t)) le_rfl))
  have hwm0 : ∀ i t, Measurable (w i t) := fun i t => (hwm i t).mono (ℱ.le (t + 1)) le_rfl
  have hw2 : ∀ i t, MemLp (w i t) 2 P := fun i t =>
    MemLp.of_bound (hwm0 i t).aestronglyMeasurable Wb
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hwb i t ω)
  -- `𝔼[w | ℱ_t] = 0`
  have hw0 : ∀ i t, P[w i t | ℱ t] =ᵐ[P] 0 := by
    intro i t
    set g : Y → Ω → ℝ := fun y ω =>
      if α i t ω = 0 then 0 else h (x t ω) i y - F (x t ω) i with hgdef
    set ind : Y → Ω → ℝ := fun y ω => if Ys t ω i = y then 1 else 0 with hinddef
    have hgm : ∀ y, StronglyMeasurable[ℱ t] (g y) := fun y =>
      (Measurable.ite (measurableSet_eq_fun (hαm i t) measurable_const) measurable_const
        (((hhm i y).comp (hxm t)).sub (hFxm t i))).stronglyMeasurable
    have hindm : ∀ y, Measurable (ind y) := fun y =>
      (Measurable.ite (hYm t i y) measurable_const measurable_const).mono (ℱ.le (t + 1)) le_rfl
    have hind_int : ∀ y, Integrable (ind y) P := fun y =>
      Integrable.of_bound (hindm y).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
        simp only [hinddef]
        split_ifs <;> norm_num)
    have hgi_int : ∀ y, Integrable (g y * ind y) P := fun y =>
      Integrable.of_bound (((hgm y).mono (ℱ.le t)).measurable.mul (hindm y)).aestronglyMeasurable
        Wb (ae_of_all _ fun ω => by
          simp only [hgdef, hinddef, Pi.mul_apply, Real.norm_eq_abs]
          split_ifs
          · simp only [zero_mul, abs_zero]
            exact (abs_nonneg _).trans (hwb i t ω)
          · simp only [zero_mul, abs_zero]
            exact (abs_nonneg _).trans (hwb i t ω)
          · rw [mul_one]
            exact hgb t ω i y
          · simp only [mul_zero, abs_zero]
            exact (abs_nonneg _).trans (hwb i t ω))
    have e : w i t = ∑ y, g y * ind y := by
      funext ω
      simp only [hwdef, hgdef, hinddef, Finset.sum_apply, Pi.mul_apply]
      split_ifs with ha
      · simp
      · simp [mul_ite]
    rw [e]
    have hsum := condExp_finsetSum (μ := P) (s := Finset.univ) (fun y _ => hgi_int y) (ℱ t)
    have hpull : ∀ y, P[g y * ind y | ℱ t] =ᵐ[P] g y * P[ind y | ℱ t] := fun y =>
      condExp_mul_of_stronglyMeasurable_left (hgm y) (hgi_int y) (hind_int y)
    filter_upwards [hsum, ae_all_iff.2 hpull, ae_all_iff.2 (hYK t i)] with ω h1 h2 h3
    rw [h1, Finset.sum_apply, Pi.zero_apply]
    simp only [h2, Pi.mul_apply]
    by_cases ha : α i t ω = 0
    · simp [hgdef, ha]
    · have e2 : ∀ y, P[ind y | ℱ t] ω = K i y := fun y => h3 y ha
      simp only [hgdef, ha, ↓reduceIte, e2, sub_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hK1, mul_one]
      rw [hK]
      ring
  -- `𝔼[w² | ℱ_t] ≤ Wb²`
  have hwv : ∀ i t, P[fun ω => w i t ω ^ 2 | ℱ t] ≤ᵐ[P] fun ω => Wb ^ 2 + 0 * ‖x t ω‖ ^ 2 := by
    intro i t
    have hmono := condExp_mono (m := ℱ t) (hw2 i t).integrable_sq (integrable_const (Wb ^ 2))
      (ae_of_all _ fun ω => by
        have := hwb i t ω
        exact (sq_abs (w i t ω)).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) this 2))
    rw [condExp_const (ℱ.le t)] at hmono
    filter_upwards [hmono] with ω hω
    rw [zero_mul, add_zero]
    exact hω
  refine Filter.Eventually.mono (tsitsiklis (ℱ := ℱ) (P := P) hFm hβ0 hβ1 hF (x := x) (α := α)
    (w := w) (sq_nonneg Wb) le_rfl (hxm 0) hαm hα0 hα1 hαsq hαdiv hwm hw2 hw0 hwv
    fun t ω i => ?_) fun ω hω => hω.2
  rw [hrec t ω i]
  simp only [hwdef]
  split_ifs with ha
  · rw [ha]
    ring
  · ring

end SargentStachurski.ApproximationAndLearning

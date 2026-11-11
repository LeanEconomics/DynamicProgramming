/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.BRSetting
import Applications.ODBasic

/-!
# McCall's job search model with Markov wage offers

Miao, **Exercise 8.1**, p. 288. The wage offer follows a Markov process on a space `W` with
transition function `Q`; the offer `w` pays the wage `wage(w)` forever if accepted, worth
`wage(w)/(1 − β)`; rejecting it pays `c` and the next offer is drawn from `Q(w, ·)`. The Bellman
equation is (`od_MarkovSearchBellman`)
`V(w) = max(c + β ∫ V(w′) Q(w, dw′), wage(w)/(1 − β))`.

We work in the setting of §7.3.1: `W` is a topological space with its Borel structure, `wage` is
bounded and continuous, and `Q` has the Feller property (Assumption 7.2.3: `w ↦ ∫ f dQ(w)` is
continuous for bounded continuous `f`).

* `ex_8_1`: the Bellman operator `od_msT` is a contraction of modulus `β` on `C(W)` (Blackwell's
  conditions, `br_blackwell`), so the Bellman equation has exactly one bounded continuous solution
  `V`, and `Tⁿ v₀ → V` geometrically (`br_theorem_3_2`).
* `ex_8_1_policy`: with the continuation value `Ψ(w) = c + β ∫ V dQ(w)`,
  `V = max(Ψ, wage/(1 − β))`, and the worker accepts `w` iff `wage(w) ≥ w̄(w) = (1 − β)Ψ(w)`: the
  reservation wage now depends on the current offer, because the offer predicts future offers.
* `ex_8_1_mono`: if `W` is preordered, `wage` is increasing and `Q` is monotone (it maps increasing
  functions to increasing functions), then `V` and `Ψ` are increasing (Closed Subspace Theorem,
  `br_corollary_1`).
* `ex_8_1_iid`: with i.i.d. offers (`Q(w, ·) = F`) the continuation value is a constant `Q*`
  and the worker accepts iff `wage(w) ≥ (1 − β)Q*`, McCall's reservation wage (§8.1).
-/

namespace Miao.Applications

open MeasureTheory ProbabilityTheory BoundedContinuousFunction

/-- The Bellman equation of **Exercise 8.1**. -/
def od_MarkovSearchBellman {W : Type*} [MeasurableSpace W] (Q : Kernel W W) (c β : ℝ)
    (wage : W → ℝ) (V : W → ℝ) : Prop :=
  ∀ w, V w = max (c + β * ∫ x, V x ∂(Q w)) (wage w / (1 - β))

variable {W : Type*} [TopologicalSpace W] [MeasurableSpace W] [OpensMeasurableSpace W]
  {Q : Kernel W W} [IsMarkovKernel Q]

omit [OpensMeasurableSpace W] in
theorem od_ms_abs_integral_le (f : W →ᵇ ℝ) (w : W) : |∫ x, f x ∂(Q w)| ≤ ‖f‖ :=
  br_abs_integral_le fun x => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x

theorem od_ms_integrable (f : W →ᵇ ℝ) (w : W) : Integrable f (Q w) :=
  integrable_of_abs_le f.continuous.measurable fun x => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x

/-- The Bellman operator of Exercise 8.1 on `C(W)`, for a Feller kernel `Q`. -/
noncomputable def od_msT (hQ : ∀ f : W →ᵇ ℝ, Continuous fun w => ∫ x, f x ∂(Q w)) (c β : ℝ)
    (wage : W →ᵇ ℝ) (f : W →ᵇ ℝ) : W →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun w => max (c + β * ∫ x, f x ∂(Q w)) (wage w / (1 - β)))
    ((continuous_const.add (continuous_const.mul (hQ f))).max
      (wage.continuous.div_const _))
    (|c| + |β| * ‖f‖ + ‖wage‖ / |1 - β|) fun w => by
      rw [Real.norm_eq_abs]
      have h1 : |c + β * ∫ x, f x ∂(Q w)| ≤ |c| + |β| * ‖f‖ := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (od_ms_abs_integral_le f w) (abs_nonneg _)
      have h2 : |wage w / (1 - β)| ≤ ‖wage‖ / |1 - β| := by
        rw [abs_div]
        exact div_le_div_of_nonneg_right (by rw [← Real.norm_eq_abs]; exact wage.norm_coe_le_norm w)
          (abs_nonneg _)
      have h3 : 0 ≤ ‖wage‖ / |1 - β| := div_nonneg (norm_nonneg _) (abs_nonneg _)
      have h4 : 0 ≤ |c| + |β| * ‖f‖ := by positivity
      rcases le_total (c + β * ∫ x, f x ∂(Q w)) (wage w / (1 - β)) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith

omit [OpensMeasurableSpace W] in
theorem od_msT_apply (hQ : ∀ f : W →ᵇ ℝ, Continuous fun w => ∫ x, f x ∂(Q w)) (c β : ℝ)
    (wage : W →ᵇ ℝ) (f : W →ᵇ ℝ) (w : W) :
    od_msT hQ c β wage f w = max (c + β * ∫ x, f x ∂(Q w)) (wage w / (1 - β)) := rfl

/-- The operator of Exercise 8.1 is a contraction of modulus `β` (Blackwell's conditions). -/
theorem od_msT_contraction (hQ : ∀ f : W →ᵇ ℝ, Continuous fun w => ∫ x, f x ∂(Q w)) {c β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (wage : W →ᵇ ℝ) :
    br_IsContraction (od_msT hQ c β wage) β := by
  refine ⟨hβ0, hβ1, br_blackwell hβ0.le (fun f g hfg w => ?_) (fun f a ha w => ?_)⟩
  · change od_msT hQ c β wage f w ≤ od_msT hQ c β wage g w
    rw [od_msT_apply, od_msT_apply]
    refine max_le_max (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hβ0.le)) le_rfl
    exact integral_mono (od_ms_integrable f w) (od_ms_integrable g w) fun x => hfg x
  · change od_msT hQ c β wage (f + const W a) w ≤ od_msT hQ c β wage f w + β * a
    rw [od_msT_apply, od_msT_apply]
    have hint : ∫ x, (f + const W a) x ∂(Q w) = ∫ x, f x ∂(Q w) + a := by
      simp only [BoundedContinuousFunction.add_apply, const_apply]
      rw [integral_add (od_ms_integrable f w) (integrable_const a)]
      simp
    rw [hint]
    have hβa : 0 ≤ β * a := mul_nonneg hβ0.le ha
    rcases le_total (c + β * ∫ x, f x ∂(Q w)) (wage w / (1 - β)) with h | h
    · rw [max_eq_right h]
      exact max_le (by nlinarith) (by linarith)
    · rw [max_eq_left h]
      exact max_le (by nlinarith) (by linarith)

/-- **Exercise 8.1** (Miao, p. 288): with a Feller transition function `Q`, a bounded continuous
wage and `β ∈ (0, 1)`, the Bellman equation `V(w) = max(c + β ∫ V dQ(w), wage(w)/(1 − β))` has
exactly one bounded continuous solution `V`, and value iteration converges to it:
`‖Tⁿv₀ − V‖ ≤ βⁿ‖v₀ − V‖`. -/
theorem ex_8_1 [Nonempty W] (hQ : ∀ f : W →ᵇ ℝ, Continuous fun w => ∫ x, f x ∂(Q w)) {c β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (wage : W →ᵇ ℝ) :
    ∃ V : W →ᵇ ℝ, od_MarkovSearchBellman Q c β wage V ∧
      (∀ V' : W →ᵇ ℝ, od_MarkovSearchBellman Q c β wage V' → V' = V) ∧
      ∀ (v₀ : W →ᵇ ℝ) (n : ℕ), dist ((od_msT hQ c β wage)^[n] v₀) V ≤ β ^ n * dist v₀ V := by
  obtain ⟨V, hV, huniq, hrate⟩ := br_theorem_3_2 (od_msT_contraction hQ (c := c) hβ0 hβ1 wage)
  refine ⟨V, fun w => ?_, fun V' hV' => huniq V' (ext fun w => (hV' w).symm), hrate⟩
  rw [← od_msT_apply hQ c β wage V w, hV]

omit [TopologicalSpace W] [OpensMeasurableSpace W] [IsMarkovKernel Q] in
/-- **Exercise 8.1** (Miao, p. 288): characterisation of the optimal decision. With the
continuation value `Ψ(w) = c + β ∫ V dQ(w)`, `V(w) = max(Ψ(w), wage(w)/(1 − β))`, so
`V ≥ wage/(1 − β)` and `V ≥ Ψ`; the worker accepts `w` iff `wage(w) ≥ (1 − β)Ψ(w)`, a reservation
wage that depends on the current offer, and then `V(w) = wage(w)/(1 − β)`; otherwise
`V(w) = Ψ(w)`. -/
theorem ex_8_1_policy {c β : ℝ} (hβ1 : β < 1) {wage V : W → ℝ}
    (hV : od_MarkovSearchBellman Q c β wage V) (w : W) :
    wage w / (1 - β) ≤ V w ∧ c + β * ∫ x, V x ∂(Q w) ≤ V w ∧
      (c + β * ∫ x, V x ∂(Q w) ≤ wage w / (1 - β) ↔
        (1 - β) * (c + β * ∫ x, V x ∂(Q w)) ≤ wage w) ∧
      ((1 - β) * (c + β * ∫ x, V x ∂(Q w)) ≤ wage w → V w = wage w / (1 - β)) ∧
      (wage w ≤ (1 - β) * (c + β * ∫ x, V x ∂(Q w)) → V w = c + β * ∫ x, V x ∂(Q w)) := by
  have hpos : 0 < 1 - β := by linarith
  have hiff : ∀ {x y : ℝ}, x ≤ y / (1 - β) ↔ (1 - β) * x ≤ y := fun {x y} => by
    rw [le_div_iff₀ hpos, mul_comm]
  have hiff' : ∀ {x y : ℝ}, y / (1 - β) ≤ x ↔ y ≤ (1 - β) * x := fun {x y} => by
    rw [div_le_iff₀ hpos, mul_comm]
  refine ⟨by rw [hV w]; exact le_max_right _ _, by rw [hV w]; exact le_max_left _ _, hiff,
    fun h => ?_, fun h => ?_⟩
  · rw [hV w, max_eq_right (hiff.2 h)]
  · rw [hV w, max_eq_left (hiff'.2 h)]

/-- **Exercise 8.1** (Miao, p. 288): if `W` is preordered, the wage is increasing and `Q` is
monotone (`w ↦ ∫ f dQ(w)` is increasing for increasing bounded continuous `f`), then the value
function `V` and the continuation value `Ψ(w) = c + β ∫ V dQ(w)` are increasing. -/
theorem ex_8_1_mono [Preorder W] [Nonempty W]
    (hQ : ∀ f : W →ᵇ ℝ, Continuous fun w => ∫ x, f x ∂(Q w))
    (hQm : ∀ f : W →ᵇ ℝ, Monotone f → Monotone fun w => ∫ x, f x ∂(Q w)) {c β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) {wage : W →ᵇ ℝ} (hwage : Monotone wage) {V : W →ᵇ ℝ}
    (hV : od_MarkovSearchBellman Q c β wage V) :
    Monotone V ∧ Monotone fun w => c + β * ∫ x, V x ∂(Q w) := by
  have hT := od_msT_contraction hQ (c := c) hβ0 hβ1 wage
  have hfix : od_msT hQ c β wage V = V := ext fun w => (hV w).symm
  set S' : Set (W →ᵇ ℝ) := {f | Monotone f}
  have hclosed : IsClosed S' := by
    have : S' = ⋂ x, ⋂ y, ⋂ (_ : x ≤ y), {f : W →ᵇ ℝ | f x ≤ f y} := by
      ext f; simp [S', Monotone]
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_le (continuous_eval_const x) (continuous_eval_const y)
  have hne : S'.Nonempty := ⟨0, fun _ _ _ => le_rfl⟩
  have hmaps : Set.MapsTo (od_msT hQ c β wage) S' S' := fun f hf x y hxy => by
    rw [od_msT_apply, od_msT_apply]
    refine max_le_max (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hQm f hf hxy) hβ0.le))
      (div_le_div_of_nonneg_right (hwage hxy) (by linarith))
  have hVm : Monotone V := (br_corollary_1 hT hfix hne hclosed hmaps hmaps).1
  exact ⟨hVm, fun x y hxy =>
    add_le_add le_rfl (mul_le_mul_of_nonneg_left (hQm V hVm hxy) hβ0.le)⟩

omit [TopologicalSpace W] [OpensMeasurableSpace W] [IsMarkovKernel Q] in
/-- **Exercise 8.1** (Miao, p. 288), the i.i.d. case of §8.1: if `Q(w, ·) = F` for every `w`,
the continuation value is the constant `Q* = c + β ∫ V dF` and the worker accepts `w` iff
`wage(w) ≥ (1 − β)Q*`, McCall's reservation wage rule. -/
theorem ex_8_1_iid {F : Measure W} {c β : ℝ} (hβ1 : β < 1) {wage V : W → ℝ}
    (hV : od_MarkovSearchBellman (Kernel.const W F) c β wage V) (w : W) :
    V w = max (c + β * ∫ x, V x ∂F) (wage w / (1 - β)) ∧
      (c + β * ∫ x, V x ∂F ≤ wage w / (1 - β) ↔ (1 - β) * (c + β * ∫ x, V x ∂F) ≤ wage w) := by
  have h := ex_8_1_policy hβ1 hV w
  simp only [Kernel.const_apply] at h
  exact ⟨by simpa using hV w, h.2.2.1⟩

end Miao.Applications

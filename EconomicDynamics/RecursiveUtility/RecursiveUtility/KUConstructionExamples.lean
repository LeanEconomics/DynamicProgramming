/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.KUConstruction
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Examples for §20.1.2

Miao §20.1.2, pp. 680–683.

* `example_20_1_1_exists`: Uzawa's utility with bounded continuous `u` and `0 ≤ β(·) ≤ b < 1`
  satisfies (W1)–(W2), so Theorem 20.1.1 constructs it.
* `ku_additive_not_W1` (p. 680): `W(x, y) = x^{1−γ}/(1 − γ) + βy` violates (W1) on `ℝ₊`, so the
  time-additive power utility is outside Lucas and Stokey's framework.
* The weighted example on p. 682: `W(x, y) = x^{1−γ} + βy` with `0 < γ, β < 1`, `βθ^{1−γ} < 1`,
  `ϕ(c) = 1 + |c|_θ^{1−γ}` on `ℓ^∞_θ ⊆ ℝ₊^ℕ`:
  `ku_example_682_W0` (`W(c₀, 0) = c₀^{1−γ} ≤ |c|_θ^{1−γ} < ϕ(c)`; the printed strict first
  inequality fails at `c = 0`, `ku_example_682_misprint`), `ku_example_682_ratio`
  (`βϕ(₁c) ≤ max(β, βθ^{1−γ})ϕ(c)`), `ku_example_682_sup` (`β sup ϕ(₁c)/ϕ(c) < 1`),
  `ku_example_682` (Theorem 20.1.2 applies) and `ku_example_682_series` (the solution is
  `U(c) = ∑ βᵗc_t^{1−γ}`). The book derives the sup bound from the pointwise strict inequality
  `βϕ(₁c) < ϕ(c)`, which by itself does not bound the supremum (`ku_pointwise_not_sup`); the
  uniform constant `max(β, βθ^{1−γ})` does.
-/

namespace Miao.RecursiveUtility

open Filter Topology
open scoped BoundedContinuousFunction

/-- Uzawa's utility constructed by **Theorem 20.1.1** (Miao, Example 20.1.1, p. 679, and p. 680):
for `u` continuous and bounded on `K` and `β(·)` continuous with `0 ≤ β ≤ b < 1`,
`W(x, y) = u(x) + β(u(x))y` satisfies (W1)–(W2), so there is a unique bounded continuous `U` on
`L` with `U(c) = u(c₀) + β(u(c₀))U(₁c)`. -/
theorem example_20_1_1_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    {u : E → ℝ} (hu : ContinuousOn u K) {M : ℝ} (huM : ∀ x ∈ K, |u x| ≤ M) {β : ℝ → ℝ}
    (hβ : Continuous β) {b : ℝ} (hb0 : ∀ a, 0 ≤ β a) (hb : ∀ a, β a ≤ b) (hb1 : b < 1) :
    ∃! U : ku_Lθ 1 K →ᵇ ℝ, ∀ c, U c = u (c.1 0) + β (u (c.1 0)) * U (ku_σθ c) := by
  have hu' : ContinuousOn (fun p : E × ℝ => u p.1) (K ×ˢ Set.univ) :=
    hu.comp continuousOn_fst fun p hp => hp.1
  have hWc : ContinuousOn (fun p : E × ℝ => u p.1 + β (u p.1) * p.2) (K ×ˢ Set.univ) :=
    hu'.add ((hβ.comp_continuousOn hu').mul continuousOn_snd)
  refine theorem_20_1_1 (W := fun x y => u x + β (u x) * y) hWc
    (fun z _ => ⟨M + b * |z|, fun x hx => ?_⟩) ((hb0 0).trans (hb 0))
    hb1 fun x _ z z' => ?_
  · calc |u x + β (u x) * z| ≤ |u x| + |β (u x) * z| := abs_add_le _ _
      _ ≤ M + b * |z| := by
          rw [abs_mul, abs_of_nonneg (hb0 _)]
          exact add_le_add (huM x hx) (mul_le_mul_of_nonneg_right (hb _) (abs_nonneg z))
  · rw [show u x + β (u x) * z - (u x + β (u x) * z') = β (u x) * (z - z') by ring, abs_mul,
      abs_of_nonneg (hb0 _)]
    exact mul_le_mul_of_nonneg_right (hb _) (abs_nonneg _)

/-- Miao, p. 680: the aggregator `W(x, y) = x^{1−γ}/(1 − γ) + βy` (`γ ≠ 1`) violates (W1): `W(·, 0)`
is unbounded on `ℝ₊`. -/
theorem ku_additive_not_W1 {γ : ℝ} (hγ : γ ≠ 1) (β : ℝ) :
    ¬ ∃ B, ∀ x : ℝ, 0 ≤ x → |x ^ (1 - γ) / (1 - γ) + β * 0| ≤ B := by
  rintro ⟨B, hB⟩
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have ha : 0 < |1 - γ| := abs_pos.2 h1
  have hy : 0 ≤ (|B| + 1) * |1 - γ| := by positivity
  have hx := hB (((|B| + 1) * |1 - γ|) ^ (1 - γ)⁻¹) (Real.rpow_nonneg hy _)
  rw [Real.rpow_inv_rpow hy h1, mul_zero, add_zero, abs_div, abs_mul, abs_abs,
    abs_of_pos (by positivity : (0 : ℝ) < |B| + 1), mul_div_cancel_right₀ _ ha.ne'] at hx
  linarith [le_abs_self B]

/-- Miao, p. 682: a pointwise strict inequality `f < 1` does not bound the supremum away from
`1`: `f(n) = 1 − 1/(n + 1)`. -/
theorem ku_pointwise_not_sup :
    ∃ f : ℕ → ℝ, (∀ n, f n < 1) ∧ BddAbove (Set.range f) ∧ ¬ (⨆ n, f n) < 1 := by
  refine ⟨fun n => 1 - 1 / ((n : ℝ) + 1), fun n => by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith, ⟨1, ?_⟩, fun h => ?_⟩
  · rintro _ ⟨n, rfl⟩
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
    have hb : BddAbove (Set.range fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) := ⟨1, by
      rintro _ ⟨n, rfl⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith⟩
    have := le_ciSup hb n
    linarith

/-! ### The example on p. 682 -/

/-- The aggregator `W(x, y) = x^{1−γ} + βy` of the example on p. 682. -/
noncomputable def ku_exW (γ β : ℝ) (x y : ℝ) : ℝ := x ^ (1 - γ) + β * y

/-- The weight `ϕ(c) = 1 + |c|_θ^{1−γ}` of the example on p. 682 (`|c|_θ = ‖b‖`). -/
noncomputable def ku_exϕ {θ : ℝ} (γ : ℝ) (b : ku_Lθ θ (Set.Ici (0 : ℝ))) : ℝ :=
  1 + ‖b.1‖ ^ (1 - γ)

theorem ku_exϕ_pos {θ γ : ℝ} (b : ku_Lθ θ (Set.Ici (0 : ℝ))) : 0 < ku_exϕ γ b := by
  have := Real.rpow_nonneg (norm_nonneg b.1) (1 - γ)
  unfold ku_exϕ
  linarith

theorem ku_head_le_norm {θ : ℝ} (b : ku_Lθ θ (Set.Ici (0 : ℝ))) : b.1 0 ≤ ‖b.1‖ :=
  (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact b.1.norm_coe_le_norm 0)

/-- Miao, p. 682 (corrected): `W(c₀, 0) = c₀^{1−γ} ≤ |c|_θ^{1−γ} < ϕ(c)`, so `W(c₀, 0)` is bounded
in the `ϕ`-norm. -/
theorem ku_example_682_W0 {θ γ β : ℝ} (hθ : 0 < θ) (hγ : γ < 1)
    (b : ku_Lθ θ (Set.Ici (0 : ℝ))) :
    b.1 0 ^ (1 - γ) ≤ ku_thetaNorm θ (ku_seqθ θ b.1) ^ (1 - γ) ∧
      |ku_exW γ β (b.1 0) 0| ≤ 1 * ku_exϕ γ b := by
  have h0 : (0 : ℝ) ≤ b.1 0 := ku_head_mem b
  have h1 : b.1 0 ^ (1 - γ) ≤ ‖b.1‖ ^ (1 - γ) :=
    Real.rpow_le_rpow h0 (ku_head_le_norm b) (by linarith)
  refine ⟨by rw [ku_thetaNorm_seqθ hθ]; exact h1, ?_⟩
  have h2 := Real.rpow_nonneg h0 (1 - γ)
  rw [ku_exW, mul_zero, add_zero, abs_of_nonneg h2, one_mul, ku_exϕ]
  linarith

/-- The zero stream lies in `ℓ^∞_θ`. -/
def ku_zeroθ (θ : ℝ) : ku_Lθ θ (Set.Ici (0 : ℝ)) :=
  ⟨0, fun t => by simp [ku_seqθ]⟩

/-- Miao, p. 682 (misprint): the printed strict inequality `c₀^{1−γ} < |c|_θ^{1−γ}` fails at
`c = 0`. -/
theorem ku_example_682_misprint {θ γ : ℝ} (hθ : 0 < θ) :
    ¬ ∀ b : ku_Lθ θ (Set.Ici (0 : ℝ)),
      b.1 0 ^ (1 - γ) < ku_thetaNorm θ (ku_seqθ θ b.1) ^ (1 - γ) := by
  intro h
  have := h (ku_zeroθ θ)
  rw [ku_thetaNorm_seqθ hθ] at this
  simp [ku_zeroθ] at this

/-- Miao, p. 682: `|₁c|_θ ≤ θ|c|_θ`, in the encoding `‖θ · (b_{t+1})‖ ≤ θ‖b‖`. -/
theorem ku_norm_σθ_le {θ : ℝ} (hθ : 0 < θ) (b : ku_Lθ θ (Set.Ici (0 : ℝ))) :
    ‖(ku_σθ b).1‖ ≤ θ * ‖b.1‖ := by
  have h : ‖ku_bshift b.1‖ ≤ ‖b.1‖ :=
    (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun t => b.1.norm_coe_le_norm (t + 1)
  change ‖θ • ku_bshift b.1‖ ≤ θ * ‖b.1‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ]
  exact mul_le_mul_of_nonneg_left h hθ.le

/-- Miao, p. 682 (corrected): `βϕ(₁c) = β + β|₁c|_θ^{1−γ} ≤ β + βθ^{1−γ}|c|_θ^{1−γ}
≤ max(β, βθ^{1−γ})ϕ(c)`. -/
theorem ku_example_682_ratio {θ γ β : ℝ} (hθ : 0 < θ) (hγ : γ < 1) (hβ : 0 ≤ β)
    (b : ku_Lθ θ (Set.Ici (0 : ℝ))) :
    β * ku_exϕ γ (ku_σθ b) ≤ max β (β * θ ^ (1 - γ)) * ku_exϕ γ b := by
  have hg : 0 ≤ 1 - γ := by linarith
  have h1 : ‖(ku_σθ b).1‖ ^ (1 - γ) ≤ θ ^ (1 - γ) * ‖b.1‖ ^ (1 - γ) := by
    rw [← Real.mul_rpow hθ.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (ku_norm_σθ_le hθ b) hg
  have h2 := Real.rpow_nonneg (norm_nonneg b.1) (1 - γ)
  have h3 : β ≤ max β (β * θ ^ (1 - γ)) := le_max_left _ _
  have h4 : β * θ ^ (1 - γ) ≤ max β (β * θ ^ (1 - γ)) := le_max_right _ _
  unfold ku_exϕ
  calc β * (1 + ‖(ku_σθ b).1‖ ^ (1 - γ)) ≤ β + β * θ ^ (1 - γ) * ‖b.1‖ ^ (1 - γ) := by
        have := mul_le_mul_of_nonneg_left h1 hβ
        linarith
    _ ≤ max β (β * θ ^ (1 - γ)) + max β (β * θ ^ (1 - γ)) * ‖b.1‖ ^ (1 - γ) :=
        add_le_add h3 (mul_le_mul_of_nonneg_right h4 h2)
    _ = max β (β * θ ^ (1 - γ)) * (1 + ‖b.1‖ ^ (1 - γ)) := by ring

/-- Miao, p. 682: `β sup_c ϕ(₁c)/ϕ(c) ≤ max(β, βθ^{1−γ}) < 1`. -/
theorem ku_example_682_sup {θ γ β : ℝ} (hθ : 0 < θ) (hγ : γ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβθ : β * θ ^ (1 - γ) < 1) :
    BddAbove (Set.range fun b : ku_Lθ θ (Set.Ici (0 : ℝ)) =>
        ku_exϕ γ (ku_σθ b) / ku_exϕ γ b) ∧
      β * ⨆ b : ku_Lθ θ (Set.Ici (0 : ℝ)), ku_exϕ γ (ku_σθ b) / ku_exϕ γ b < 1 := by
  have hr : ∀ b : ku_Lθ θ (Set.Ici (0 : ℝ)),
      ku_exϕ γ (ku_σθ b) / ku_exϕ γ b ≤ max β (β * θ ^ (1 - γ)) / β := fun b => by
    rw [div_le_div_iff₀ (ku_exϕ_pos b) hβ0]
    have := ku_example_682_ratio hθ hγ hβ0.le b
    linarith
  have hbdd : BddAbove (Set.range fun b : ku_Lθ θ (Set.Ici (0 : ℝ)) =>
      ku_exϕ γ (ku_σθ b) / ku_exϕ γ b) := ⟨_, by rintro _ ⟨b, rfl⟩; exact hr b⟩
  refine ⟨hbdd, ?_⟩
  have : Nonempty (ku_Lθ θ (Set.Ici (0 : ℝ))) := ⟨ku_zeroθ θ⟩
  have h1 := ciSup_le hr
  have h2 : β * ⨆ b : ku_Lθ θ (Set.Ici (0 : ℝ)), ku_exϕ γ (ku_σθ b) / ku_exϕ γ b ≤
      max β (β * θ ^ (1 - γ)) := by
    have := mul_le_mul_of_nonneg_left h1 hβ0.le
    rwa [mul_div_cancel₀ _ hβ0.ne'] at this
  exact h2.trans_lt (max_lt hβ1 hβθ)

theorem ku_exW_continuousOn {γ β : ℝ} (hγ : γ < 1) :
    ContinuousOn (fun p : ℝ × ℝ => ku_exW γ β p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) :=
  (((Real.continuous_rpow_const (by linarith)).comp continuous_fst).add
    (continuous_const.mul continuous_snd)).continuousOn

theorem ku_exW_lipschitz (γ β : ℝ) (hβ : 0 ≤ β) (x y y' : ℝ) :
    |ku_exW γ β x y - ku_exW γ β x y'| ≤ β * |y - y'| := by
  rw [ku_exW, ku_exW, show x ^ (1 - γ) + β * y - (x ^ (1 - γ) + β * y') = β * (y - y') by ring,
    abs_mul, abs_of_nonneg hβ]

theorem ku_exϕ_continuous {θ γ : ℝ} (hγ : γ < 1) :
    Continuous (ku_exϕ (θ := θ) γ) :=
  continuous_const.add ((Real.continuous_rpow_const (by linarith)).comp
    (continuous_norm.comp continuous_subtype_val))

/-- Miao, p. 682: the example satisfies the hypotheses of **Theorem 20.1.2**, so
`W(x, y) = x^{1−γ} + βy` defines a unique recursive utility `U ∈ C_ϕ(ℓ^∞_θ)`. -/
theorem ku_example_682 {θ γ β : ℝ} (hθ : 0 < θ) (hγ : γ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβθ : β * θ ^ (1 - γ) < 1) :
    ∃! U, ku_InC (ku_exϕ γ) U ∧
      ∀ b : ku_Lθ θ (Set.Ici (0 : ℝ)), ku_exW γ β (b.1 0) (U (ku_σθ b)) = U b :=
  (theorem_20_1_2 (ku_exW_continuousOn hγ) hβ0.le (fun x _ => ku_exW_lipschitz γ β hβ0.le x)
    (ku_exϕ_continuous hγ) ku_exϕ_pos ⟨1, fun b => (ku_example_682_W0 hθ hγ b).2⟩
    (ku_example_682_sup hθ hγ hβ0 hβ1 hβθ).1 (ku_example_682_sup hθ hγ hβ0 hβ1 hβθ).2).1

/-- Miao, p. 680 and p. 682: the solution of the example is the discounted sum
`U(c) = ∑ βᵗc_t^{1−γ}`. -/
theorem ku_example_682_series {θ γ β : ℝ} (hθ : 0 < θ) (hγ : γ < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβθ : β * θ ^ (1 - γ) < 1) {U : ku_Lθ θ (Set.Ici (0 : ℝ)) → ℝ}
    (hU : ku_InC (ku_exϕ γ) U)
    (hfix : ∀ b : ku_Lθ θ (Set.Ici (0 : ℝ)), ku_exW γ β (b.1 0) (U (ku_σθ b)) = U b)
    (b : ku_Lθ θ (Set.Ici (0 : ℝ))) :
    U b = ∑' t, β ^ t * ku_seqθ θ b.1 t ^ (1 - γ) := by
  have hg : 0 ≤ 1 - γ := by linarith
  set r := β * θ ^ (1 - γ)
  have hr0 : 0 ≤ r := mul_nonneg hβ0.le (Real.rpow_nonneg hθ.le _)
  -- the series and its bounds
  let V : ku_Lθ θ (Set.Ici (0 : ℝ)) → ℝ := fun b => ∑' t, β ^ t * ku_seqθ θ b.1 t ^ (1 - γ)
  have hterm : ∀ (b : ku_Lθ θ (Set.Ici (0 : ℝ))) t,
      0 ≤ β ^ t * ku_seqθ θ b.1 t ^ (1 - γ) ∧
        β ^ t * ku_seqθ θ b.1 t ^ (1 - γ) ≤ r ^ t * ‖b.1‖ ^ (1 - γ) := by
    intro b t
    have hc0 : (0 : ℝ) ≤ ku_seqθ θ b.1 t := b.2 t
    have hct : ku_seqθ θ b.1 t ≤ θ ^ t * ‖b.1‖ := by
      have h := le_abs_self (ku_seqθ θ b.1 t)
      have h2 : |ku_seqθ θ b.1 t| = θ ^ t * ‖b.1 t‖ := by
        rw [← Real.norm_eq_abs, ku_seqθ, norm_smul, Real.norm_eq_abs,
          abs_of_pos (pow_pos hθ t)]
      have h3 := mul_le_mul_of_nonneg_left (b.1.norm_coe_le_norm t) (pow_pos hθ t).le
      linarith
    have hpow : (θ ^ t * ‖b.1‖) ^ (1 - γ) = (θ ^ (1 - γ)) ^ t * ‖b.1‖ ^ (1 - γ) := by
      rw [Real.mul_rpow (pow_nonneg hθ.le t) (norm_nonneg _), Real.rpow_pow_comm hθ.le]
    refine ⟨mul_nonneg (pow_nonneg hβ0.le t) (Real.rpow_nonneg hc0 _), ?_⟩
    calc β ^ t * ku_seqθ θ b.1 t ^ (1 - γ) ≤ β ^ t * (θ ^ t * ‖b.1‖) ^ (1 - γ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc0 hct hg) (pow_nonneg hβ0.le t)
      _ = r ^ t * ‖b.1‖ ^ (1 - γ) := by rw [hpow, mul_pow]; ring
  have hsum : ∀ b : ku_Lθ θ (Set.Ici (0 : ℝ)),
      Summable fun t => β ^ t * ku_seqθ θ b.1 t ^ (1 - γ) := fun b =>
    Summable.of_nonneg_of_le (fun t => (hterm b t).1) (fun t => (hterm b t).2)
      ((summable_geometric_of_lt_one hr0 hβθ).mul_right _)
  have hVb : ∀ b, |V b| ≤ (1 - r)⁻¹ * ku_exϕ γ b := by
    intro b
    have h0 : 0 ≤ V b := tsum_nonneg fun t => (hterm b t).1
    have h1 : V b ≤ ∑' t, r ^ t * ‖b.1‖ ^ (1 - γ) :=
      Summable.tsum_le_tsum (fun t => (hterm b t).2) (hsum b)
        ((summable_geometric_of_lt_one hr0 hβθ).mul_right _)
    rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hβθ] at h1
    have h2 : ‖b.1‖ ^ (1 - γ) ≤ ku_exϕ γ b := by unfold ku_exϕ; linarith
    have h3 : 0 < (1 - r)⁻¹ := inv_pos.2 (by linarith)
    rw [abs_of_nonneg h0]
    calc V b ≤ (1 - r)⁻¹ * ‖b.1‖ ^ (1 - γ) := h1
      _ ≤ (1 - r)⁻¹ * ku_exϕ γ b := mul_le_mul_of_nonneg_left h2 h3.le
  have hVfix : ku_TW (fun b => b.1 0) ku_σθ (ku_exW γ β) V = V := by
    funext b
    simp only [ku_TW, ku_exW, V]
    rw [(hsum b).tsum_eq_zero_add, ← tsum_mul_left, ku_seqθ_zero, pow_zero, one_mul]
    congr 1
    refine tsum_congr fun t => ?_
    rw [ku_seqθ_σθ, pow_succ]
    ring
  have hκ := ku_example_682_ratio hθ hγ hβ0.le
  have e := ku_TW_unique_of_bound (hd := fun b : ku_Lθ θ (Set.Ici (0 : ℝ)) => b.1 0)
    (σ := ku_σθ) (W := ku_exW γ β) ku_exϕ_pos (fun c => ku_exW_lipschitz γ β hβ0.le _)
    hβ0.le (le_max_of_le_left hβ0.le) (max_lt hβ1 hβθ) hκ hU (funext hfix) hVb hVfix
  rw [← e]

end Miao.RecursiveUtility

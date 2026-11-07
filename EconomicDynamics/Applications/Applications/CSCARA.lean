/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.CSDeterministic

/-!
# Exercises 6.9–6.10: exponential (CARA) utility

Copied from `EconomicDynamics/FiniteHorizonDP` (module `CSCARA`), namespace renamed.

Miao, Exercises 9–10, pp. 190–191.

**Exercise 6.9** (Schechtman–Escudero 1977). Utility `−e^{−γc}`, iid income `y` with
distribution `μ` concentrated on `[y_min, y_max]`, no constraint on `c` or `a`. Without a
terminal condition the problem is unbounded (utility is bounded above by `0`), so we impose
`a_{T+1} = 0`; then with cash on hand `x = Ra + y` the time-to-go problem is
`v_0(x) = −e^{−γx}`, `v_{n+1}(x) = sup_{s ∈ ℝ} −e^{−γ(x−s)} + β E v_n(Rs + y)` (`cs_cara_v`).
`ex_6_9`: `v_n(x) = −A_n e^{−α_n x}` with `α_n = γ / Σ_{k=0}^n R^{−k}`, `A_n > 0` given
recursively (`cs_caraA`), the unique optimal saving is
`s_{n+1}(x) = (γx + L_n)/(γ + α_n R)`, `L_n = log(β A_n M_n α_n R/γ)`, `M_n = E e^{−α_n y}`, and
consumption `c_{n+1}(x) = (α_n R x − L_n)/(γ + α_n R)` is linear in `x` with the certainty
marginal propensity `1/Σ_{k=0}^{n+1} R^{−k}`. The one-step problem is `cs_cara_step`.

**Exercise 6.10** (Levhari–Mirman–Zilcha 1980). Add `c ≥ 0`, `a_{t+1} ≥ 0`: this is §6.6.2 with
`u(c) = −e^{−γc}`, `b = 0` (`bookModel`). The Inada condition fails (`u′(0) = γ`), so only the
derivative-free results apply (`ex_6_10`): `v_n` strictly increasing and strictly concave, a
unique continuous saving policy, `s_n` and `g_n` increasing in `x`, and **threshold structure**:
`{x : s_n(x) = 0}` and `{x : g_n(x) = 0}` are initial segments of `[0, ∞)`. With one period to go
the policy is explicit (`ex_6_10_one`): **the Exercise 6.9 saving clamped to `[0, x]`**,
`s_1(x) = max(0, min(x, (γx + L_0)/(γ + γR)))`, `L_0 = log(βR E e^{−γy})`. For `n ≥ 2` the
continuation value `v_{n−1}` is no longer exponential, so the policy is not of the Exercise 6.9
form; we prove the structure only (not formalised: a closed form, which does not exist).
-/

namespace Miao.Applications

open MeasureTheory Real

/-- **The one-step CARA problem** (Exercises 9–10): with `γ, α, R, K > 0` and
`(γ + αR) s₀ = γx + L`, `L = log(KαR/γ)`, the function
`f(s) = −e^{−γ(x − s)} − K e^{−αRs}` has the strict global maximum `s₀`, and
`f(s₀) = −(1 + γ/(αR)) e^{γL/(γ + αR)} e^{−(γαR/(γ + αR)) x}`. -/
theorem cs_cara_step {γ α R K : ℝ} (hγ : 0 < γ) (hα : 0 < α) (hR : 0 < R) (hK : 0 < K)
    (x s₀ : ℝ) (hs₀ : (γ + α * R) * s₀ = γ * x + Real.log (K * α * R / γ)) :
    (∀ s, s ≠ s₀ → -Real.exp (-(γ * (x - s))) - K * Real.exp (-(α * R * s)) <
        -Real.exp (-(γ * (x - s₀))) - K * Real.exp (-(α * R * s₀))) ∧
      -Real.exp (-(γ * (x - s₀))) - K * Real.exp (-(α * R * s₀)) =
        -((1 + γ / (α * R)) * Real.exp (γ * Real.log (K * α * R / γ) / (γ + α * R))) *
          Real.exp (-(γ * α * R / (γ + α * R) * x)) := by
  set L := Real.log (K * α * R / γ)
  have hαR : 0 < α * R := mul_pos hα hR
  have hKL : Real.exp L = K * α * R / γ := Real.exp_log (by positivity)
  -- the first-order condition `γ E₁(s₀) = K α R E₂(s₀)`
  have hE1 : Real.exp (-(γ * (x - s₀))) = Real.exp L * Real.exp (-(α * R * s₀)) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have hfoc : K * Real.exp (-(α * R * s₀)) = γ / (α * R) * Real.exp (-(γ * (x - s₀))) := by
    rw [hE1, hKL]
    field_simp
  refine ⟨fun s hs => ?_, ?_⟩
  · have hd : s - s₀ ≠ 0 := sub_ne_zero.2 hs
    have h1 : Real.exp (-(γ * (x - s))) =
        Real.exp (-(γ * (x - s₀))) * Real.exp (γ * (s - s₀)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-(α * R * s)) =
        Real.exp (-(α * R * s₀)) * Real.exp (-(α * R * (s - s₀))) := by
      rw [← Real.exp_add]; congr 1; ring
    have e1 := Real.add_one_lt_exp (mul_ne_zero hγ.ne' hd)
    have e2 := Real.add_one_lt_exp (neg_ne_zero.2 (mul_ne_zero hαR.ne' hd))
    have p1 := Real.exp_pos (-(γ * (x - s₀)))
    have p2 := Real.exp_pos (-(α * R * s₀))
    rw [h1, h2]
    have q1 := mul_lt_mul_of_pos_left e1 p1
    have q2 := mul_lt_mul_of_pos_left e2 (mul_pos hK p2)
    have hfoc' : K * Real.exp (-(α * R * s₀)) * (α * R) = γ * Real.exp (-(γ * (x - s₀))) := by
      rw [hfoc]; field_simp
    have hd' : K * Real.exp (-(α * R * s₀)) * (α * R * (s - s₀)) =
        Real.exp (-(γ * (x - s₀))) * (γ * (s - s₀)) := by
      rw [show K * Real.exp (-(α * R * s₀)) * (α * R * (s - s₀)) =
        K * Real.exp (-(α * R * s₀)) * (α * R) * (s - s₀) by ring, hfoc']
      ring
    have q1' : Real.exp (-(γ * (x - s₀))) * (γ * (s - s₀)) + Real.exp (-(γ * (x - s₀))) <
        Real.exp (-(γ * (x - s₀))) * Real.exp (γ * (s - s₀)) := by linarith [q1]
    have q2' : -(K * Real.exp (-(α * R * s₀)) * (α * R * (s - s₀))) +
        K * Real.exp (-(α * R * s₀)) <
        K * (Real.exp (-(α * R * s₀)) * Real.exp (-(α * R * (s - s₀)))) := by
      have : K * Real.exp (-(α * R * s₀)) * (-(α * R * (s - s₀)) + 1) =
          -(K * Real.exp (-(α * R * s₀)) * (α * R * (s - s₀))) + K * Real.exp (-(α * R * s₀)) := by
        ring
      rw [← this, ← mul_assoc]
      exact q2
    linarith
  · rw [hfoc]
    have h3 : Real.exp (-(γ * (x - s₀))) =
        Real.exp (γ * L / (γ + α * R)) * Real.exp (-(γ * α * R / (γ + α * R) * x)) := by
      rw [← Real.exp_add]
      congr 1
      have hden : 0 < γ + α * R := by positivity
      have hs : s₀ = (γ * x + L) / (γ + α * R) := by
        rw [eq_div_iff hden.ne']; linarith
      rw [hs]
      field_simp
      ring
    rw [h3]
    ring

/-- The value functions of Exercise 6.9: `v_0(x) = −e^{−γx}`,
`v_{n+1}(x) = sup_s −e^{−γ(x−s)} + β ∫ v_n(Rs + y) μ(dy)`. -/
noncomputable def cs_cara_v (γ β R : ℝ) (μ : Measure ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => -Real.exp (-(γ * x))
  | n + 1 => fun x => sSup (Set.range fun s =>
      -Real.exp (-(γ * (x - s))) + β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ)

/-- The exponent `α_n`: `α_0 = γ`, `α_{n+1} = γ α_n R/(γ + α_n R)`. -/
noncomputable def cs_caraAlpha (γ R : ℝ) : ℕ → ℝ
  | 0 => γ
  | n + 1 => γ * cs_caraAlpha γ R n * R / (γ + cs_caraAlpha γ R n * R)

/-- `M_n = ∫ e^{−α_n y} μ(dy)`. -/
noncomputable def cs_caraM (γ R : ℝ) (μ : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ y, Real.exp (-(cs_caraAlpha γ R n * y)) ∂μ

/-- The coefficient `A_n`: `A_0 = 1`,
`A_{n+1} = (1 + γ/(α_n R)) exp(γ L_n/(γ + α_n R))`, `L_n = log(β A_n M_n α_n R/γ)`. -/
noncomputable def cs_caraA (γ β R : ℝ) (μ : Measure ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 + γ / (cs_caraAlpha γ R n * R)) *
      Real.exp (γ * Real.log (β * cs_caraA γ β R μ n * cs_caraM γ R μ n * cs_caraAlpha γ R n *
        R / γ) / (γ + cs_caraAlpha γ R n * R))

/-- `L_n = log(β A_n M_n α_n R/γ)`. -/
noncomputable def cs_caraL (γ β R : ℝ) (μ : Measure ℝ) (n : ℕ) : ℝ :=
  Real.log (β * cs_caraA γ β R μ n * cs_caraM γ R μ n * cs_caraAlpha γ R n * R / γ)

/-- The optimal saving with `n + 1` periods to go: `s_{n+1}(x) = (γx + L_n)/(γ + α_n R)`. -/
noncomputable def cs_caraS (γ β R : ℝ) (μ : Measure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (γ * x + cs_caraL γ β R μ n) / (γ + cs_caraAlpha γ R n * R)

/-- `E e^{−αy} > 0` for `μ` concentrated on a bounded interval. -/
theorem cs_cara_M_pos {μ : Measure ℝ} [IsProbabilityMeasure μ] {ymin ymax α : ℝ} (hα : 0 < α)
    (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) : 0 < ∫ y, Real.exp (-(α * y)) ∂μ := by
  have hint : Integrable (fun y => Real.exp (-(α * y))) μ := by
    refine (integrable_const (Real.exp (-(α * ymin)))).mono'
      (by fun_prop : Continuous fun y => Real.exp (-(α * y))).aestronglyMeasurable ?_
    filter_upwards [hμ] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by nlinarith [hy.1])
  have hlow : ∫ _, Real.exp (-(α * ymax)) ∂μ ≤ ∫ y, Real.exp (-(α * y)) ∂μ := by
    refine integral_mono_ae (integrable_const _) hint ?_
    filter_upwards [hμ] with y hy
    exact Real.exp_le_exp.2 (by nlinarith [hy.2])
  rw [integral_const, probReal_univ, one_smul] at hlow
  exact lt_of_lt_of_le (Real.exp_pos _) hlow

/-- `∫ −A e^{−α(Rs + y)} μ(dy) = −A M e^{−αRs}` with `M = ∫ e^{−αy} μ(dy)`. -/
theorem cs_cara_integral (μ : Measure ℝ) (A α R s : ℝ) :
    ∫ y, -(A * Real.exp (-(α * (R * s + y)))) ∂μ =
      -(A * ∫ y, Real.exp (-(α * y)) ∂μ) * Real.exp (-(α * R * s)) := by
  have : ∀ y, -(A * Real.exp (-(α * (R * s + y)))) =
      -(A * Real.exp (-(α * R * s))) * Real.exp (-(α * y)) := fun y => by
    rw [show -(α * (R * s + y)) = -(α * R * s) + -(α * y) by ring, Real.exp_add]
    ring
  simp only [this, integral_const_mul]
  ring

/-- **Exercise 6.9** (Schechtman–Escudero 1977; Miao, p. 190). For `γ, β, R > 0` and iid income
concentrated on `[y_min, y_max]`, for every `n`:
* `v_n(x) = −A_n e^{−α_n x}` with `A_n > 0`, `α_n > 0` and `α_n = γ / Σ_{k=0}^n R^{−k}`;
* the objective of `v_{n+1}(x)` has the strict global maximum `s_{n+1}(x) =
  (γx + L_n)/(γ + α_n R)`, the **optimal saving**, and `v_{n+1}(x)` is its value;
* the **optimal consumption** `c_{n+1}(x) = x − s_{n+1}(x)` is
  `(α_n R x − L_n)/(γ + α_n R)`, linear with slope `1/Σ_{k=0}^{n+1} R^{−k}`. -/
theorem ex_6_9 {γ β R ymin ymax : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hγ : 0 < γ)
    (hβ : 0 < β) (hR : 0 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) (n : ℕ) :
    (0 < cs_caraAlpha γ R n ∧ 0 < cs_caraA γ β R μ n ∧
      cs_caraAlpha γ R n = γ / ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k ∧
      ∀ x, cs_cara_v γ β R μ n x = -(cs_caraA γ β R μ n * Real.exp (-(cs_caraAlpha γ R n * x)))) ∧
    ∀ x, (∀ s, s ≠ cs_caraS γ β R μ n x →
        -Real.exp (-(γ * (x - s))) + β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ <
          -Real.exp (-(γ * (x - cs_caraS γ β R μ n x))) +
            β * ∫ y, cs_cara_v γ β R μ n (R * cs_caraS γ β R μ n x + y) ∂μ) ∧
      cs_cara_v γ β R μ (n + 1) x = -Real.exp (-(γ * (x - cs_caraS γ β R μ n x))) +
            β * ∫ y, cs_cara_v γ β R μ n (R * cs_caraS γ β R μ n x + y) ∂μ ∧
      x - cs_caraS γ β R μ n x =
        (cs_caraAlpha γ R n * R * x - cs_caraL γ β R μ n) / (γ + cs_caraAlpha γ R n * R) ∧
      cs_caraAlpha γ R n * R / (γ + cs_caraAlpha γ R n * R) =
        1 / ∑ k ∈ Finset.range (n + 2), R⁻¹ ^ k := by
  -- the closed form, by induction
  have key : ∀ n, 0 < cs_caraAlpha γ R n ∧ 0 < cs_caraA γ β R μ n ∧
      cs_caraAlpha γ R n = γ / ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k ∧
      ∀ x, cs_cara_v γ β R μ n x =
        -(cs_caraA γ β R μ n * Real.exp (-(cs_caraAlpha γ R n * x))) := by
    intro n
    induction n with
    | zero =>
      refine ⟨hγ, one_pos, by simp [cs_caraAlpha], fun x => ?_⟩
      simp only [cs_cara_v, cs_caraA, cs_caraAlpha, one_mul]
    | succ n ih =>
      obtain ⟨hα, hA, hαS, hv⟩ := ih
      set α := cs_caraAlpha γ R n
      set A := cs_caraA γ β R μ n
      have hM := cs_cara_M_pos hα hμ
      set Mn := cs_caraM γ R μ n
      have hK : 0 < β * A * Mn := by positivity
      have hαR : 0 < α * R := mul_pos hα hR
      refine ⟨by simp only [cs_caraAlpha]; positivity, by simp only [cs_caraA]; positivity,
        ?_, fun x => ?_⟩
      · have hS : 0 < ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k :=
          Finset.sum_pos (fun k _ => pow_pos (inv_pos.2 hR) k) Finset.nonempty_range_add_one
        have hsum : ∑ k ∈ Finset.range (n + 1 + 1), R⁻¹ ^ k =
            R⁻¹ * ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k + 1 := by
          rw [Finset.sum_range_succ', Finset.mul_sum]
          simp only [pow_succ, pow_zero]
          congr 1
          exact Finset.sum_congr rfl fun k _ => by ring
        change γ * α * R / (γ + α * R) = _
        rw [hsum, hαS]
        field_simp
      · change sSup (Set.range fun s => -Real.exp (-(γ * (x - s))) +
          β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ) = _
        have hobj : ∀ s, -Real.exp (-(γ * (x - s))) +
            β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ =
            -Real.exp (-(γ * (x - s))) - β * A * Mn * Real.exp (-(α * R * s)) := fun s => by
          have hMn : ∫ y, Real.exp (-(α * y)) ∂μ = Mn := rfl
          simp only [hv, cs_cara_integral, hMn]
          ring
        set s₀ := (γ * x + Real.log (β * A * Mn * α * R / γ)) / (γ + α * R)
        have hs₀ : (γ + α * R) * s₀ = γ * x + Real.log (β * A * Mn * α * R / γ) := by
          simp only [s₀]; field_simp
        obtain ⟨hmax, hval⟩ := cs_cara_step hγ hα hR hK x s₀ hs₀
        have hgreat : IsGreatest (Set.range fun s => -Real.exp (-(γ * (x - s))) +
            β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ)
            (-Real.exp (-(γ * (x - s₀))) - β * A * Mn * Real.exp (-(α * R * s₀))) := by
          refine ⟨⟨s₀, hobj s₀⟩, ?_⟩
          rintro _ ⟨s, rfl⟩
          dsimp only
          rw [hobj s]
          rcases eq_or_ne s s₀ with h | h
          · rw [h]
          · exact (hmax s h).le
        rw [hgreat.csSup_eq, hval]
        simp only [cs_caraA, cs_caraAlpha]
        rw [neg_mul]
  refine ⟨key n, fun x => ?_⟩
  obtain ⟨hα, hA, hαS, hv⟩ := key n
  set α := cs_caraAlpha γ R n
  set A := cs_caraA γ β R μ n
  have hM := cs_cara_M_pos hα hμ
  set Mn := cs_caraM γ R μ n
  have hK : 0 < β * A * Mn := by positivity
  have hαR : 0 < α * R := mul_pos hα hR
  have hobj : ∀ s, -Real.exp (-(γ * (x - s))) + β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ =
      -Real.exp (-(γ * (x - s))) - β * A * Mn * Real.exp (-(α * R * s)) := fun s => by
    have hMn : ∫ y, Real.exp (-(α * y)) ∂μ = Mn := rfl
    simp only [hv, cs_cara_integral, hMn]
    ring
  have hden : 0 < γ + α * R := by positivity
  have hs₀ : (γ + α * R) * cs_caraS γ β R μ n x =
      γ * x + Real.log (β * A * Mn * α * R / γ) := by
    have e1 : cs_caraAlpha γ R n = α := rfl
    have e2 : cs_caraA γ β R μ n = A := rfl
    have e3 : cs_caraM γ R μ n = Mn := rfl
    simp only [cs_caraS, cs_caraL, e1, e2, e3]
    rw [mul_comm]
    exact div_mul_cancel₀ _ hden.ne'
  obtain ⟨hmax, -⟩ := cs_cara_step hγ hα hR hK x _ hs₀
  refine ⟨fun s hs => ?_, ?_, ?_, ?_⟩
  · rw [hobj, hobj]; exact hmax s hs
  · change sSup (Set.range fun s => -Real.exp (-(γ * (x - s))) +
      β * ∫ y, cs_cara_v γ β R μ n (R * s + y) ∂μ) = _
    refine IsGreatest.csSup_eq ⟨⟨_, rfl⟩, ?_⟩
    rintro _ ⟨s, rfl⟩
    dsimp only
    rcases eq_or_ne s (cs_caraS γ β R μ n x) with h | h
    · rw [h]
    · rw [hobj, hobj]; exact (hmax s h).le
  · have e1 : cs_caraAlpha γ R n = α := rfl
    simp only [cs_caraS, e1]
    rw [eq_div_iff hden.ne', sub_mul, div_mul_cancel₀ _ hden.ne']
    ring
  · have hS : 0 < ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k :=
      Finset.sum_pos (fun k _ => pow_pos (inv_pos.2 hR) k) Finset.nonempty_range_add_one
    have hsum : ∑ k ∈ Finset.range (n + 2), R⁻¹ ^ k =
        R⁻¹ * ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_succ, pow_zero]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum, hαS]
    field_simp

/-! ### Exercise 6.10: Levhari–Mirman–Zilcha (1980) -/

/-- The maximum of a concave function with global maximum `m` over `[a, b]` is attained at the
projection `max(a, min(b, m))` of `m` onto `[a, b]`. -/
theorem cs_clamp {f : ℝ → ℝ} (hf : ConcaveOn ℝ Set.univ f) {m a b : ℝ} (hab : a ≤ b)
    (hm : ∀ s, f s ≤ f m) : ∀ s ∈ Set.Icc a b, f s ≤ f (max a (min b m)) := by
  intro s hs
  rcases le_total m a with hma | hma
  · rw [max_eq_left ((min_le_right b m).trans hma)]
    have := hf.ge_on_segment (Set.mem_univ m) (Set.mem_univ s)
      (by rw [segment_eq_Icc (hma.trans hs.1)]; exact ⟨hma, hs.1⟩)
    rwa [min_eq_right (hm s)] at this
  · rcases le_total m b with hmb | hmb
    · rw [min_eq_right hmb, max_eq_right hma]
      exact hm s
    · rw [min_eq_left hmb, max_eq_right hab]
      have := hf.ge_on_segment (Set.mem_univ s) (Set.mem_univ m)
        (by rw [segment_eq_Icc (hs.2.trans hmb)]; exact ⟨hs.2, hmb⟩)
      rwa [min_eq_left (hm s)] at this

/-- **Exercise 6.10: the model** (Miao, p. 191): §6.6.2 with `u(c) = −e^{−γc}` and `b = 0`
satisfies the standing hypotheses when `γ, β, R > 0` and `y_min > 0`. -/
theorem cs_cara_basic {γ β R ymin ymax : ℝ} {μ : Measure (Set.Icc ymin ymax)}
    [IsProbabilityMeasure μ] (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (hy : 0 < ymin) :
    (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).Basic where
  β_pos := hβ
  u_cont := (by fun_prop : Continuous fun c : ℝ => -Real.exp (-(γ * c))).continuousOn
  u_mono := fun c _ c' _ h => by
    change -Real.exp (-(γ * c)) < -Real.exp (-(γ * c'))
    have := Real.exp_lt_exp.2 (by nlinarith : -(γ * c') < -(γ * c))
    linarith
  u_conc := by
    refine ⟨convex_Ici 0, fun c₁ _ c₂ _ hne θ η hθ hη hs => ?_⟩
    have hne' : -(γ * c₁) ≠ -(γ * c₂) := fun h => hne (by
      have := mul_left_cancel₀ hγ.ne' (neg_inj.1 h); exact this)
    have := strictConvexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) hne' hθ hη hs
    change θ • -Real.exp (-(γ * c₁)) + η • -Real.exp (-(γ * c₂)) <
      -Real.exp (-(γ * (θ • c₁ + η • c₂)))
    simp only [smul_eq_mul] at this ⊢
    rw [show θ * -(γ * c₁) + η * -(γ * c₂) = -(γ * (θ * c₁ + η * c₂)) by ring] at this
    linarith
  ρ_cont := continuous_const
  ρ_pos := fun _ => hR
  w_cont := continuous_subtype_val.sub continuous_const
  w_pos := fun y => by
    change 0 < y.1 - (R - 1) * 0
    linarith [y.2.1]
  feller := CSModel.isFeller_const μ

/-- **Exercise 6.10** (Levhari–Mirman–Zilcha 1980; Miao, p. 191): with `c ≥ 0`, `a_{t+1} ≥ 0` and
CARA utility, for every `n` and current shock `z`: `v_n` is strictly increasing and strictly
concave on `[0, ∞)`; the optimal saving `s_{n+1}` is the unique maximizer and continuous; `s_n`
and `g_n` are increasing in `x`; and there are **thresholds**: the sets where the saving
constraint binds (`s_n(x) = 0`) and where consumption is zero (`g_n(x) = 0`) are initial
segments of `[0, ∞)`. -/
theorem ex_6_10 {γ β R ymin ymax : ℝ} {μ : Measure (Set.Icc ymin ymax)} [IsProbabilityMeasure μ]
    (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (hy : 0 < ymin) (n : ℕ) (z : Set.Icc ymin ymax) :
    StrictMonoOn (fun x => (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).v n x z)
        (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0)
        (fun x => (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).v n x z) ∧
      (∀ x, 0 ≤ x → ∀ s ∈ Set.Icc 0 x,
        ((bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).obj n x z s =
            (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).v (n + 1) x z →
          s = (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav (n + 1) x z)) ∧
      ContinuousOn (fun p : ℝ × Set.Icc ymin ymax =>
        (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav n p.1 p.2)
        (Set.Ici 0 ×ˢ Set.univ) ∧
      MonotoneOn (fun x => (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav n x z)
        (Set.Ici 0) ∧
      MonotoneOn
        (fun x => (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).cons n x z)
        (Set.Ici 0) ∧
      (∀ x x', 0 ≤ x' → x' ≤ x →
        (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav n x z = 0 →
        (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav n x' z = 0) ∧
      ∀ x x', 0 ≤ x' → x' ≤ x →
        (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).cons n x z = 0 →
        (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).cons n x' z = 0 := by
  have := bookModel_isMarkovKernel (u := fun c => -Real.exp (-(γ * c))) (β := β) (R := R) (b := 0)
    (μ := μ)
  have h := cs_cara_basic (μ := μ) hγ hβ hR hy
  set M := bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ
  refine ⟨CSModel.strictMonoOn_v h n z, CSModel.strictConcaveOn_v h n z,
    fun x _ s hs hv => CSModel.sav_unique h n hs hv, CSModel.continuousOn_sav h n,
    CSModel.monotoneOn_sav h n z, CSModel.monotoneOn_cons h n z,
    fun x x' hx' hxx' h0 => ?_, fun x x' hx' hxx' h0 => ?_⟩
  · have h1 := CSModel.monotoneOn_sav h n z (Set.mem_Ici.2 hx') (Set.mem_Ici.2 (hx'.trans hxx'))
      hxx'
    have h2 := (CSModel.sav_mem' h n hx' z).1
    simp only at h1
    linarith
  · have h1 := CSModel.monotoneOn_cons h n z (Set.mem_Ici.2 hx') (Set.mem_Ici.2 (hx'.trans hxx'))
      hxx'
    have h2 := (CSModel.sav_mem' h n hx' z).2
    simp only [CSModel.cons] at h1 h0 ⊢
    linarith

/-- **Exercise 6.10 with one period to go** (Miao, p. 191): the optimal saving is the
Exercise 6.9 saving clamped to the feasible set,
`s_1(x) = max(0, min(x, (γx + L)/(γ + γR)))`, `L = log(β M γ R/γ)` with `M = E e^{−γy}`. The
saving constraint binds (`s_1 = 0`) where `γx + L ≤ 0`, and consumption is zero (`s_1 = x`)
where `(γx + L)/(γ + γR) ≥ x`. -/
theorem ex_6_10_one {γ β R ymin ymax : ℝ} {μ : Measure (Set.Icc ymin ymax)}
    [IsProbabilityMeasure μ] (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (hy : 0 < ymin)
    (z : Set.Icc ymin ymax) {x : ℝ} (hx : 0 ≤ x) :
    (bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ).sav 1 x z =
      max 0 (min x ((γ * x + Real.log (β * (∫ y, Real.exp (-(γ * y.1)) ∂μ) * γ * R / γ)) /
        (γ + γ * R))) := by
  have := bookModel_isMarkovKernel (u := fun c => -Real.exp (-(γ * c))) (β := β) (R := R) (b := 0)
    (μ := μ)
  have h := cs_cara_basic (μ := μ) hγ hβ hR hy
  set M := bookModel (fun c => -Real.exp (-(γ * c))) β R 0 ymin ymax μ
  set M₀ := ∫ y, Real.exp (-(γ * y.1)) ∂μ
  have hM₀ : 0 < M₀ := by
    have hc : Continuous fun y : Set.Icc ymin ymax => Real.exp (-(γ * y.1)) := by fun_prop
    have hint : Integrable (fun y : Set.Icc ymin ymax => Real.exp (-(γ * y.1))) μ :=
      integrable_of_abs_le hc.measurable fun y => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (by nlinarith [y.2.1] : -(γ * y.1) ≤ -(γ * ymin))
    have hlow : ∫ _, Real.exp (-(γ * ymax)) ∂μ ≤ M₀ :=
      integral_mono (integrable_const _) hint fun y =>
        Real.exp_le_exp.2 (by nlinarith [y.2.2] : -(γ * ymax) ≤ -(γ * y.1))
    rw [integral_const, probReal_univ, one_smul] at hlow
    exact lt_of_lt_of_le (Real.exp_pos _) hlow
  set K := β * M₀
  have hK : 0 < K := mul_pos hβ hM₀
  set g : ℝ → ℝ := fun s => -Real.exp (-(γ * (x - s))) - K * Real.exp (-(γ * R * s)) with hg
  set s₀ := (γ * x + Real.log (K * γ * R / γ)) / (γ + γ * R)
  have hden : 0 < γ + γ * R := by positivity
  have hs₀ : (γ + γ * R) * s₀ = γ * x + Real.log (K * γ * R / γ) := by
    rw [mul_comm]; exact div_mul_cancel₀ _ hden.ne'
  obtain ⟨hmax, -⟩ := cs_cara_step hγ hγ hR hK x s₀ hs₀
  have hgm : ∀ s, g s ≤ g s₀ := fun s => by
    rcases eq_or_ne s s₀ with e | e
    · rw [e]
    · exact (hmax s e).le
  -- `g` is concave
  have hconc : ConcaveOn ℝ Set.univ g := by
    refine ⟨convex_univ, fun s₁ _ s₂ _ θ η hθ hη hs => ?_⟩
    have h1 := convexOn_exp.2 (Set.mem_univ (-(γ * (x - s₁)))) (Set.mem_univ (-(γ * (x - s₂))))
      hθ hη hs
    have h2 := convexOn_exp.2 (Set.mem_univ (-(γ * R * s₁))) (Set.mem_univ (-(γ * R * s₂)))
      hθ hη hs
    simp only [smul_eq_mul, hg] at h1 h2 ⊢
    rw [show θ * -(γ * (x - s₁)) + η * -(γ * (x - s₂)) = -(γ * (x - (θ * s₁ + η * s₂))) by
      linear_combination (-(γ * x)) * hs] at h1
    rw [show θ * -(γ * R * s₁) + η * -(γ * R * s₂) = -(γ * R * (θ * s₁ + η * s₂)) by ring] at h2
    nlinarith [mul_le_mul_of_nonneg_left h2 hK.le]
  -- the objective on `[0, x]` is `g`
  have hobj : ∀ s ∈ Set.Icc 0 x, M.obj 0 x z s = g s := by
    intro s hs
    rw [M.obj_eq 0 z hs.2]
    change -Real.exp (-(γ * (x - s))) + β * ∫ y, -Real.exp (-(γ * (R * s + (y.1 - (R - 1) * 0))))
      ∂μ = _
    have : ∀ y : Set.Icc ymin ymax, -Real.exp (-(γ * (R * s + (y.1 - (R - 1) * 0)))) =
        -Real.exp (-(γ * R * s)) * Real.exp (-(γ * y.1)) := fun y => by
      rw [show -(γ * (R * s + (y.1 - (R - 1) * 0))) = -(γ * R * s) + -(γ * y.1) by ring,
        Real.exp_add]
      ring
    simp only [this, integral_const_mul, hg, K, M₀]
    ring
  set p := max 0 (min x s₀)
  have hp : p ∈ Set.Icc 0 x := ⟨le_max_left _ _, max_le hx (min_le_left _ _)⟩
  have hcl := cs_clamp hconc hx hgm
  obtain ⟨hm, hv⟩ := CSModel.sav_mem h 0 hx z
  have hpv : M.obj 0 x z p = M.v 1 x z := by
    refine le_antisymm (CSModel.obj_le h 0 hp) ?_
    rw [← hv, hobj _ hm, hobj _ hp]
    exact hcl _ hm
  rw [← CSModel.sav_unique h 0 hp hpv]

end Miao.Applications

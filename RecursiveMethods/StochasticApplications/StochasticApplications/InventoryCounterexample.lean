/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.InventoryFOC

/-!
# Production and inventory accumulation: counterexamples for Exercise 10.5g

SLP §10.5, Exercise 10.5g, p. 300. The instance: surplus `U(q) = 1 − e^{−q}` (demand
`D(q) = e^{−q}`, `D(0) = 1`), holding cost `φ(y) = y²`, input cost `c(n) = n²`, `β = 1/2`,
`Ū = 1`, `N̄ = 2` (`c(2) = 4 > Ū/(1 − β) = 2`), `Ω = [0, 1]` (`invEx_hyp`). It satisfies all of
the book's assumptions, including `φ′(0) = c′(0) = 0`, and with `ω′ = 1` for sure all of the
hypotheses of `ex_10_5g` (`invEx_hyps`).

**Correction** (Exercise 10.5g).
* `ex_10_5g_counterexample`: `x₂ > x₁ ⇒ N(x₂) < N(x₁)` is false. Since `U′(x) = e^{−x} > 1/2`
  for `x ∈ {1/4, 1/2}`, nothing is stored at either stock (`inv_Y_eq_zero`), so the input solves
  the same problem `max −c(n) + βE v(nω′)` at both, and `N(1/4) = N(1/2)`. The corrected claim
  is `ex_10_5g`: `N(x₂) < N(x₁)` exactly when `Y(x₂) > 0`.
* `ex_10_5g_mean_zero`: `N(x) > 0` needs `E ω′ > 0`. With `ω′ = 0` for sure, `N ≡ 0`
  (`inv_N_zero_of_dirac`).

**The book's question: what if `c′(0) > 0`?** `ex_10_5g_steep`: with `c(n) = n² + n`, so
`c′(0) = 1`, and `ω′ = 1` for sure, `N ≡ 0` (`inv_N_eq_zero`), because the marginal product of the
input, at most `β sup U′ ω₂ = 1/2`, never covers its marginal cost. Then `N(x) > 0` and the strict
decrease of `N` both fail. What survives is `inv_N_strict`: `N(x₂) < N(x₁)` whenever `Y(x₂) > 0`
and `N(x₁) > 0`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

/-! ### The instance -/

/-- Surplus `U(q) = 1 − e^{−q}`, the area under the demand curve `D(q) = e^{−q}`. -/
noncomputable def invExU (q : ℝ) : ℝ := 1 - Real.exp (-q)

/-- The cost `y ↦ y²`, used for holding and for the input. -/
def invExSq (y : ℝ) : ℝ := y ^ 2

/-- The steep input cost `c(n) = n² + n`, with `c′(0) = 1 > 0`. -/
def invExSteep (n : ℝ) : ℝ := n ^ 2 + n

/-- `0 ∈ [0, 1]`. -/
def invExω₀ : Icc (0 : ℝ) 1 := ⟨0, left_mem_Icc.2 zero_le_one⟩

/-- `1 ∈ [0, 1]`. -/
def invExω₁ : Icc (0 : ℝ) 1 := ⟨1, right_mem_Icc.2 zero_le_one⟩

/-- The harvest `ω′ = 1` for sure. -/
noncomputable abbrev invExμ : Measure (Icc (0 : ℝ) 1) := Measure.dirac invExω₁

/-- The harvest `ω′ = 0` for sure. -/
noncomputable abbrev invExμ₀ : Measure (Icc (0 : ℝ) 1) := Measure.dirac invExω₀

/-- `U′(q) = e^{−q}`. -/
theorem invExU_hasDerivAt (q : ℝ) : HasDerivAt invExU (Real.exp (-q)) q := by
  have := ((hasDerivAt_neg q).exp).const_sub 1
  have e : invExU = fun q => 1 - Real.exp (-q) := rfl
  rw [e]
  convert this using 1
  ring

/-- `(y²)′ = 2y`. -/
theorem invExSq_hasDerivAt (y : ℝ) : HasDerivAt invExSq (2 * y) y := by
  have e : invExSq = fun y => y ^ 2 := rfl
  rw [e]
  convert hasDerivAt_pow 2 y using 1
  norm_num

/-- `(n² + n)′ = 2n + 1`. -/
theorem invExSteep_hasDerivAt (n : ℝ) : HasDerivAt invExSteep (2 * n + 1) n := by
  have e : invExSteep = (fun x => x ^ 2) + id := rfl
  rw [e]
  convert (hasDerivAt_pow 2 n).add (hasDerivAt_id n) using 1
  norm_num

/-- `U(q) = 1 − e^{−q}` is strictly concave. -/
theorem invExU_strictConcave : StrictConcaveOn ℝ (Ici 0) invExU := by
  refine ⟨convex_Ici 0, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have := strictConvexOn_exp.2 (mem_univ (-x)) (mem_univ (-y)) (fun h => hxy (by linarith)) ha
    hb hab
  simp only [smul_eq_mul, invExU] at this ⊢
  rw [show a * -x + b * -y = -(a * x + b * y) by ring] at this
  linarith

/-- `y ↦ y²` is strictly increasing on `[0, ∞)`. -/
theorem invExSq_strictMono : StrictMonoOn invExSq (Ici 0) := fun a ha b _ hab => by
  simp only [invExSq]; nlinarith [mem_Ici.1 ha]

/-- The instance with `U(q) = 1 − e^{−q}`, `φ(y) = c(y) = y²`, `β = 1/2`, `Ū = 1`, `N̄ = 2` and
`Ω = [0, 1]`. -/
theorem invEx_hyp : InvHyp invExU invExSq invExSq (1 / 2) 1 2 0 1 where
  β_pos := by norm_num
  β_lt := by norm_num
  ω_nonneg := le_rfl
  ω_le := zero_le_one
  U_cont := (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousOn
  U_zero := by simp [invExU]
  U_mono := fun a _ b _ hab => by
    simp only [invExU]; linarith [Real.exp_lt_exp.2 (neg_lt_neg hab)]
  U_conc := invExU_strictConcave
  U_le := fun q _ => by simp only [invExU]; linarith [Real.exp_pos (-q)]
  H_cont := (continuous_pow 2).continuousOn
  H_zero := by simp [invExSq]
  H_mono := invExSq_strictMono
  H_conv := strictConvexOn_pow (by norm_num)
  c_cont := (continuous_pow 2).continuousOn
  c_zero := by simp [invExSq]
  c_mono := invExSq_strictMono
  c_conv := strictConvexOn_pow (by norm_num)
  N_nonneg := by norm_num
  N_big := by norm_num [invExSq]

/-- The instance with the steep input cost `c(n) = n² + n`. -/
theorem invExSteep_hyp : InvHyp invExU invExSq invExSteep (1 / 2) 1 2 0 1 where
  β_pos := by norm_num
  β_lt := by norm_num
  ω_nonneg := le_rfl
  ω_le := zero_le_one
  U_cont := (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousOn
  U_zero := by simp [invExU]
  U_mono := fun a _ b _ hab => by
    simp only [invExU]; linarith [Real.exp_lt_exp.2 (neg_lt_neg hab)]
  U_conc := invExU_strictConcave
  U_le := fun q _ => by simp only [invExU]; linarith [Real.exp_pos (-q)]
  H_cont := (continuous_pow 2).continuousOn
  H_zero := by simp [invExSq]
  H_mono := invExSq_strictMono
  H_conv := strictConvexOn_pow (by norm_num)
  c_cont := ((continuous_pow 2).add continuous_id).continuousOn
  c_zero := by simp [invExSteep]
  c_mono := fun a ha b _ hab => by simp only [invExSteep]; nlinarith [mem_Ici.1 ha]
  c_conv := (strictConvexOn_pow (by norm_num)).add_convexOn (convexOn_id (convex_Ici 0))
  N_nonneg := by norm_num
  N_big := by norm_num [invExSteep]

/-- The instance satisfies every hypothesis of `ex_10_5g`: `U`, `φ` and `c` are differentiable,
`c′(0) = 0`, and `E ω′ = 1 > 0`. Also `φ′(0) = 0` and `U′ = D` with `D(0) = 1 < ∞`. -/
theorem invEx_hyps :
    (∀ q, 0 < q → DifferentiableAt ℝ invExU q) ∧ (∀ y, 0 < y → DifferentiableAt ℝ invExSq y) ∧
      HasDerivWithinAt invExSq 0 (Ici 0) 0 ∧ HasDerivAt invExSq 0 0 ∧
      (∀ q, deriv invExU q = Real.exp (-q)) ∧ ∫ ω', ω'.1 ∂invExμ = 1 := by
  refine ⟨fun q _ => (invExU_hasDerivAt q).differentiableAt,
    fun y _ => (invExSq_hasDerivAt y).differentiableAt, ?_, ?_,
    fun q => (invExU_hasDerivAt q).deriv, ?_⟩
  · simpa using (invExSq_hasDerivAt 0).hasDerivWithinAt (s := Ici 0)
  · simpa using invExSq_hasDerivAt 0
  · rw [integral_dirac]; rfl

/-! ### The counterexamples -/

/-- **Exercise 10.5g, counterexample.** Take the instance `invEx_hyp` with `ω′ = 1` for sure. It
satisfies all of the book's assumptions and those of `ex_10_5g` (`invEx_hyps`). Nothing is stored
at `x = 1/4` or at `x = 1/2`, since `U′(x) = e^{−x} > 1/2 = β sup U′` (`inv_Y_eq_zero`). So
`N(1/4) = N(1/2)` (`inv_N_eq_of_Y_zero`), and `x₂ > x₁ ⇒ N(x₂) < N(x₁)` fails. -/
theorem ex_10_5g_counterexample :
    ∃ v : Ici (0 : ℝ) × Icc (0 : ℝ) 1 →ᵇ ℝ, truncT (invEx_hyp.upperDP invExμ) v = v ∧
      ¬ ∀ (x₁ x₂ : Ici (0 : ℝ)) (ω : Icc (0 : ℝ) 1) (P₁ P₂ : ℝ × ℝ), x₁.1 < x₂.1 →
        P₁ ∈ policy (invModel invExμ invExU invExSq invExSq (1 / 2) 2) v (x₁, ω) →
        P₂ ∈ policy (invModel invExμ invExU invExSq invExSq (1 / 2) 2) v (x₂, ω) →
        P₂.2 < P₁.2 := by
  obtain ⟨v, hv, -⟩ := upper_fixed (invEx_hyp.upperDP invExμ)
  refine ⟨v, hv, fun hall => ?_⟩
  obtain ⟨hUd, hHd, -, -, hdU, -⟩ := invEx_hyps
  have hL : ∀ q, 0 < q → deriv invExU q ≤ 1 := fun q hq => by
    rw [hdU]; exact Real.exp_le_one_iff.2 (by linarith)
  set x₁ : Ici (0 : ℝ) := ⟨1 / 4, mem_Ici.2 (by norm_num)⟩
  set x₂ : Ici (0 : ℝ) := ⟨1 / 2, mem_Ici.2 (by norm_num)⟩
  obtain ⟨P₁, hp₁, hv₁⟩ := (inv_max invEx_hyp hv (x₁, invExω₀)).1
  obtain ⟨P₂, hp₂, hv₂⟩ := (inv_max invEx_hyp hv (x₂, invExω₀)).1
  have hP₁ : P₁ ∈ policy (invModel invExμ invExU invExSq invExSq (1 / 2) 2) v (x₁, invExω₀) :=
    ⟨hp₁, hv₁⟩
  have hP₂ : P₂ ∈ policy (invModel invExμ invExU invExSq invExSq (1 / 2) 2) v (x₂, invExω₀) :=
    ⟨hp₂, hv₂⟩
  have hY₁ := inv_Y_eq_zero invEx_hyp hv hUd hHd hL hP₁ (by change (0 : ℝ) < 1 / 4; norm_num) (by
    rw [hdU]
    have := Real.add_one_lt_exp (by norm_num : (-(1 / 4) : ℝ) ≠ 0)
    change (1 / 2 : ℝ) * 1 < Real.exp (-(1 / 4))
    linarith)
  have hY₂ := inv_Y_eq_zero invEx_hyp hv hUd hHd hL hP₂ (by change (0 : ℝ) < 1 / 2; norm_num) (by
    rw [hdU]
    have := Real.add_one_lt_exp (by norm_num : (-(1 / 2) : ℝ) ≠ 0)
    change (1 / 2 : ℝ) * 1 < Real.exp (-(1 / 2))
    linarith)
  have heq := inv_N_eq_of_Y_zero invEx_hyp hv invExω₀ hP₁ hP₂ hY₁ hY₂
  have := hall x₁ x₂ invExω₀ P₁ P₂ (by change (1 / 4 : ℝ) < 1 / 2; norm_num) hP₁ hP₂
  linarith

/-- If the harvest is `0` for sure, the input is never used: `N(x) = 0`. -/
theorem inv_N_zero_of_dirac {U H c : ℝ → ℝ} {β Ubar Nbar ω₁ ω₂ : ℝ}
    (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {ω₀ : Icc ω₁ ω₂} (hω₀ : ω₀.1 = 0)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP (Measure.dirac ω₀)) v = v)
    {x : Ici (0 : ℝ)} {ω : Icc ω₁ ω₂} {P : ℝ × ℝ}
    (hP : P ∈ policy (invModel (Measure.dirac ω₀) U H c β Nbar) v (x, ω)) : P.2 = 0 := by
  rcases (hP.1.2.1 : 0 ≤ P.2).eq_or_lt with h0 | hpos
  · exact h0.symm
  exfalso
  have hfeas : ((P.1, 0) : ℝ × ℝ) ∈ invΓ Nbar (x, ω) := ⟨hP.1.1, le_rfl, h.N_nonneg⟩
  have hle := (inv_max h hv (x, ω)).2 _ hfeas
  have e := hP.2
  rw [inv_rhs, integral_dirac] at hle e
  have hφ : invφ (x, (P.1, 0), ω₀) = invφ (x, P, ω₀) := Subtype.ext (by simp [invφ, hω₀])
  rw [hφ] at hle
  have hc := h.c_mono (mem_Ici.2 le_rfl) (mem_Ici.2 hP.1.2.1) hpos
  rw [h.c_zero] at hc
  dsimp only at hle e
  rw [h.c_zero] at hle
  linarith

/-- **Exercise 10.5g: `N(x) > 0` needs `E ω′ > 0`.** In the instance `invEx_hyp` with `ω′ = 0`
for sure (allowed: `Ω = [0, 1]` and `μ` is any probability measure on `Ω`), `N(x) = 0` at every
stock. -/
theorem ex_10_5g_mean_zero :
    ∫ ω', ω'.1 ∂invExμ₀ = 0 ∧
      ∃ v : Ici (0 : ℝ) × Icc (0 : ℝ) 1 →ᵇ ℝ, truncT (invEx_hyp.upperDP invExμ₀) v = v ∧
        ∀ (x : Ici (0 : ℝ)) (ω : Icc (0 : ℝ) 1) (P : ℝ × ℝ),
          P ∈ policy (invModel invExμ₀ invExU invExSq invExSq (1 / 2) 2) v (x, ω) → P.2 = 0 := by
  obtain ⟨v, hv, -⟩ := upper_fixed (invEx_hyp.upperDP invExμ₀)
  refine ⟨by rw [integral_dirac]; rfl, v, hv, fun x ω P hP => ?_⟩
  exact inv_N_zero_of_dirac invEx_hyp (ω₀ := invExω₀) rfl hv hP

/-- **Exercise 10.5g with `c′(0) > 0`.** In `invExSteep_hyp` the input cost `c(n) = n² + n` has
`c′(0) = 1`. Since `U′ ≤ 1`, the marginal product of the input is at most `βω₂ = 1/2 < 1`, and
`N(x) = 0` at every stock (`inv_N_eq_zero`), although `E ω′ = 1 > 0`. So `N(x) > 0` fails, and
`N` is constant. -/
theorem ex_10_5g_steep :
    HasDerivAt invExSteep 1 0 ∧
      ∃ v : Ici (0 : ℝ) × Icc (0 : ℝ) 1 →ᵇ ℝ, truncT (invExSteep_hyp.upperDP invExμ) v = v ∧
        ∀ (x : Ici (0 : ℝ)) (ω : Icc (0 : ℝ) 1) (P : ℝ × ℝ),
          P ∈ policy (invModel invExμ invExU invExSq invExSteep (1 / 2) 2) v (x, ω) →
            P.2 = 0 := by
  obtain ⟨hUd, -, -, -, hdU, -⟩ := invEx_hyps
  have hL : ∀ q, 0 < q → deriv invExU q ≤ 1 := fun q hq => by
    rw [hdU]; exact Real.exp_le_one_iff.2 (by linarith)
  obtain ⟨v, hv, -⟩ := upper_fixed (invExSteep_hyp.upperDP invExμ)
  refine ⟨by simpa using invExSteep_hasDerivAt 0, v, hv, fun x ω P hP => ?_⟩
  exact inv_N_eq_zero invExSteep_hyp hv hUd hL (κ := 1) (by norm_num)
    (fun n hn => by simp only [invExSteep]; nlinarith) hP

end StokeyLucasPrescott.StochasticApplications

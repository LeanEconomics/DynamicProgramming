/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Bounds.Basic

/-!
# The deterministic cake-eating problem

AKMM, §10.5.1, pp. 273–274: an infinitely lived consumer with a cake `a₀`, utility
`∑ βᵗ√c_t`, and `a_{t+1} = a_t − c_t`; the Bellman equation is
`V(a) = max_{0 ≤ a′ ≤ a} √(a − a′) + βV(a′)`.

The book solves it numerically (Example 3). The problem has the closed form
`V(a) = √(a/(1 − β²))` with policy `a′ = β²a` (`c = (1 − β²)a`): it satisfies the Bellman
equation with the maximum attained at `β²a` (`cake_bellman`), the maximiser is unique
(`cake_policy_unique`), and it is the only solution bounded on `[0, ā]` (`cake_bellman_unique`,
the contraction argument of p. 272 on the continuous state space). The policy's consumption path
`c_t = (1 − β²)β^{2t}a₀` attains `V(a₀)` (`cake_path_value`). The value function is concave
(`cake_concave`), as the book notes ("the properties of a contraction mapping ensure the value
function is concave in this particular case").
-/

namespace AKMM.ComputationalTools

open Filter Topology

/-- The closed-form value `V(a) = √(a/(1 − β²))` of the cake-eating problem. -/
noncomputable def cakeV (β a : ℝ) : ℝ := √(a / (1 - β ^ 2))

/-- The right-hand side `√(a − a′) + βV(a′)` of the Bellman equation for a value `W`. -/
noncomputable def cakeRhs (β : ℝ) (W : ℝ → ℝ) (a a' : ℝ) : ℝ := √(a - a') + β * W a'

/-- The Cauchy–Schwarz bound behind the Bellman equation: for `k ≥ 0` with `k + β² = 1`,
`√k·u + βv ≤ √(u² + v²)` for all real `u`, `v`. -/
theorem cake_cauchy_schwarz {k β : ℝ} (hk : 0 ≤ k) (hkb : k + β ^ 2 = 1) (u v : ℝ) :
    √k * u + β * v ≤ √(u ^ 2 + v ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  have hs : √k ^ 2 = k := Real.sq_sqrt hk
  nlinarith [sq_nonneg (β * u - √k * v)]

/-- AKMM, §10.5.1, p. 273: `V(a) = √(a/(1 − β²))` solves the Bellman equation
`V(a) = max_{0 ≤ a′ ≤ a} √(a − a′) + βV(a′)` for `0 ≤ β < 1`, `a ≥ 0`, and the maximum is
attained at `a′ = β²a`, i.e. consumption `c = (1 − β²)a`. -/
theorem cake_bellman {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a : ℝ} (ha : 0 ≤ a) :
    IsGreatest (cakeRhs β (cakeV β) a '' Set.Icc 0 a) (cakeV β a) ∧
      cakeRhs β (cakeV β) a (β ^ 2 * a) = cakeV β a := by
  set k := 1 - β ^ 2 with hk_def
  have hk : 0 < k := by nlinarith
  have hsk : 0 < √k := Real.sqrt_pos.2 hk
  have hV : ∀ x, 0 ≤ x → cakeV β x = √x / √k := fun x _ => by
    unfold cakeV; rw [Real.sqrt_div' _ hk.le]
  have hβ2 : β ^ 2 ≤ 1 := by nlinarith
  have hattain : cakeRhs β (cakeV β) a (β ^ 2 * a) = cakeV β a := by
    unfold cakeRhs
    rw [hV _ (by positivity), hV _ ha]
    have h1 : a - β ^ 2 * a = k * a := by rw [hk_def]; ring
    rw [h1, Real.sqrt_mul hk.le, Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ0]
    field_simp
    have hs : √k ^ 2 = k := Real.sq_sqrt hk.le
    rw [hk_def] at hs ⊢
    rw [hs]
    ring
  refine ⟨⟨⟨β ^ 2 * a, ⟨by positivity, by nlinarith⟩, hattain⟩, ?_⟩, hattain⟩
  rintro _ ⟨a', ⟨ha'0, ha'a⟩, rfl⟩
  unfold cakeRhs
  rw [hV _ ha'0, hV _ ha, le_div_iff₀ hsk]
  have hcs := cake_cauchy_schwarz (β := β) hk.le (by rw [hk_def]; ring) (√(a - a')) (√a')
  rw [Real.sq_sqrt (by linarith), Real.sq_sqrt ha'0, show a - a' + a' = a by ring] at hcs
  calc (√(a - a') + β * (√a' / √k)) * √k = √k * √(a - a') + β * √a' := by field_simp
    _ ≤ √a := hcs

/-- AKMM, §10.5.1: the maximiser `a′ = β²a` is unique (for `a > 0`, `0 < β < 1`): any `a′` that
attains `V(a)` equals `β²a`. -/
theorem cake_policy_unique {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a a' : ℝ} (ha : 0 < a)
    (ha' : a' ∈ Set.Icc 0 a) (h : cakeRhs β (cakeV β) a a' = cakeV β a) : a' = β ^ 2 * a := by
  set k := 1 - β ^ 2 with hk_def
  have hk : 0 < k := by nlinarith
  have hsk : 0 < √k := Real.sqrt_pos.2 hk
  have hs : √k ^ 2 = k := Real.sq_sqrt hk.le
  unfold cakeRhs cakeV at h
  rw [Real.sqrt_div' _ hk.le, Real.sqrt_div' _ hk.le] at h
  -- `√k·u + βv = √(u² + v²)` with `u = √(a − a′)`, `v = √a′` forces `βu = √k v`
  set u := √(a - a') with hu
  set v := √a' with hv
  have hu2 : u ^ 2 = a - a' := Real.sq_sqrt (by linarith [ha'.2])
  have hv2 : v ^ 2 = a' := Real.sq_sqrt ha'.1
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have heq : √k * u + β * v = √a := by
    field_simp at h
    linarith
  have hsq : (√k * u + β * v) ^ 2 = a := by rw [heq, Real.sq_sqrt ha.le]
  have hzero : (β * u - √k * v) ^ 2 = 0 := by
    have : (β * u - √k * v) ^ 2 = (k + β ^ 2) * (u ^ 2 + v ^ 2) - (√k * u + β * v) ^ 2 := by
      nlinarith [hs]
    rw [this, hsq, hu2, hv2, hk_def]
    ring
  have hlin : β * u = √k * v := by nlinarith [sq_nonneg (β * u - √k * v)]
  have h2 : β ^ 2 * (a - a') = k * a' := by
    have := congrArg (· ^ 2) hlin
    simp only [mul_pow] at this
    rw [hu2, hv2, hs] at this
    exact this
  rw [hk_def] at h2
  nlinarith

/-- One step of the contraction argument: two solutions of the Bellman equation that differ by
at most `B` on `[0, ā]` differ by at most `βB` there. -/
theorem cake_bellman_step {β : ℝ} (hβ0 : 0 ≤ β) {abar B : ℝ} {U W : ℝ → ℝ}
    (hU : ∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β U a '' Set.Icc 0 a) (U a))
    (hW : ∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β W a '' Set.Icc 0 a) (W a))
    (hB : ∀ a ∈ Set.Icc 0 abar, |U a - W a| ≤ B) :
    ∀ a ∈ Set.Icc 0 abar, |U a - W a| ≤ β * B := by
  have key : ∀ {U W : ℝ → ℝ},
      (∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β U a '' Set.Icc 0 a) (U a)) →
      (∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β W a '' Set.Icc 0 a) (W a)) →
      (∀ a ∈ Set.Icc 0 abar, |U a - W a| ≤ B) → ∀ a ∈ Set.Icc 0 abar, U a ≤ W a + β * B := by
    intro U W hU hW hB a ha
    refine (hU a ha).2 ?_
    rintro _ ⟨a', ha', rfl⟩
    have ha'' : a' ∈ Set.Icc 0 abar := ⟨ha'.1, ha'.2.trans ha.2⟩
    have h1 : cakeRhs β W a a' ≤ W a := (hW a ha).1 ⟨a', ha', rfl⟩
    have h2 := (abs_le.1 (hB a' ha'')).2
    unfold cakeRhs at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_left h2 hβ0]
  intro a ha
  rw [abs_le]
  constructor
  · have := key hW hU (fun x hx => by rw [abs_sub_comm]; exact hB x hx) a ha
    linarith
  · have := key hU hW hB a ha
    linarith

/-- AKMM, p. 272 and §10.5.1: the Bellman equation has only one solution bounded on `[0, ā]`
(the contraction mapping theorem on the continuous state space): every bounded `W` with
`W(a) = sup_{0 ≤ a′ ≤ a} √(a − a′) + βW(a′)` on `[0, ā]` equals `√(a/(1 − β²))` there. -/
theorem cake_bellman_unique {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {abar : ℝ} {W : ℝ → ℝ}
    (hW : ∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β W a '' Set.Icc 0 a) (W a))
    (hWb : ∃ C, ∀ a ∈ Set.Icc 0 abar, |W a| ≤ C) :
    ∀ a ∈ Set.Icc 0 abar, W a = cakeV β a := by
  have hV : ∀ a ∈ Set.Icc 0 abar, IsLUB (cakeRhs β (cakeV β) a '' Set.Icc 0 a) (cakeV β a) :=
    fun a ha => (cake_bellman hβ0 hβ1 ha.1).1.isLUB
  obtain ⟨C, hC⟩ := hWb
  set B := C + cakeV β abar
  have hVmono : ∀ a ∈ Set.Icc 0 abar, |cakeV β a| ≤ cakeV β abar := by
    intro a ha
    unfold cakeV
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hk : 0 < 1 - β ^ 2 := by nlinarith
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ha.2 hk.le)
  have hB : ∀ a ∈ Set.Icc 0 abar, |W a - cakeV β a| ≤ B := fun a ha =>
    (abs_sub _ _).trans (add_le_add (hC a ha) (hVmono a ha))
  have hiter : ∀ n : ℕ, ∀ a ∈ Set.Icc 0 abar, |W a - cakeV β a| ≤ β ^ n * B := by
    intro n
    induction n with
    | zero => simpa using hB
    | succ n ih =>
      intro a ha
      have := cake_bellman_step hβ0 hW hV ih a ha
      calc |W a - cakeV β a| ≤ β * (β ^ n * B) := this
        _ = β ^ (n + 1) * B := by ring
  intro a ha
  have hlim : Tendsto (fun n : ℕ => β ^ n * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const B
  have h0 : |W a - cakeV β a| ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall fun n => hiter n a ha)
  have := abs_nonpos_iff.1 h0
  linarith

/-- AKMM, §10.5.1: the optimal path `a_t = β^{2t}a₀`, `c_t = (1 − β²)β^{2t}a₀` satisfies
`a_{t+1} = a_t − c_t` and attains lifetime utility `∑ βᵗ√c_t = √(a₀/(1 − β²)) = V(a₀)`. -/
theorem cake_path_value {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (a₀ : ℝ) :
    (∀ t : ℕ, β ^ (2 * (t + 1)) * a₀ = β ^ (2 * t) * a₀ - (1 - β ^ 2) * β ^ (2 * t) * a₀) ∧
      HasSum (fun t : ℕ => β ^ t * √((1 - β ^ 2) * β ^ (2 * t) * a₀)) (cakeV β a₀) := by
  have hk : 0 < 1 - β ^ 2 := by nlinarith
  refine ⟨fun t => by ring, ?_⟩
  have hterm : ∀ t : ℕ, β ^ t * √((1 - β ^ 2) * β ^ (2 * t) * a₀) =
      √((1 - β ^ 2) * a₀) * (β ^ 2) ^ t := by
    intro t
    rw [show (1 - β ^ 2) * β ^ (2 * t) * a₀ = (β ^ t) ^ 2 * ((1 - β ^ 2) * a₀) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hβ0 t)]
    ring
  simp only [hterm]
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg β) (by nlinarith : β ^ 2 < 1)).mul_left
    (√((1 - β ^ 2) * a₀))
  convert hg using 1
  unfold cakeV
  rw [Real.sqrt_mul hk.le, Real.sqrt_div' _ hk.le]
  have hs : √(1 - β ^ 2) ^ 2 = 1 - β ^ 2 := Real.sq_sqrt hk.le
  have hsk : 0 < √(1 - β ^ 2) := Real.sqrt_pos.2 hk
  field_simp
  rw [hs]

/-- AKMM, p. 273: the value function `V(a) = √(a/(1 − β²))` is concave on `[0, ∞)`. -/
theorem cake_concave {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : ConcaveOn ℝ (Set.Ici 0) (cakeV β) := by
  have hk : 0 < 1 - β ^ 2 := by nlinarith
  have h := (Real.strictConcaveOn_sqrt.concaveOn).smul (c := (√(1 - β ^ 2))⁻¹)
    (inv_nonneg.2 (Real.sqrt_nonneg _))
  refine h.congr fun a _ => ?_
  simp only [smul_eq_mul, cakeV]
  rw [Real.sqrt_div' _ hk.le, div_eq_inv_mul]

end AKMM.ComputationalTools

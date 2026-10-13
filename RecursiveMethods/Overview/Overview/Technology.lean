/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Overview.Basics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The neoclassical technology

SLP §2.1, pp. 9–10, and Exercise 2.1, pp. 10–11.

Output is `F(k, n)` with `F` homogeneous of degree one, `F(0, n) = 0`, strictly increasing in
each input, strictly quasi-concave, and satisfying the Inada conditions in `k`. With depreciation
`0 < δ ≤ 1` and labour normalized to one, the total supply of goods is
`f(k) = F(k, 1) + (1 − δ)k`.

* `Neoclassical`: the book's assumptions on `F` (with strict quasi-concavity on the open
  quadrant; see `docs/corrections.md`).
* `strictConcaveOn_F` and Ex 2.1: `f` is continuously differentiable, strictly increasing and
  strictly concave, with `f(0) = 0`, `f′ > 0`, `f′(0+) = ∞` and `f′(∞) = 1 − δ`
  (`f_zero`, `hasDerivAt_f`, `continuousOn_f'`, `f'_pos`, `strictMonoOn_f`, `strictConcaveOn_f`,
  `f'_tendsto_zero`, `f'_tendsto_atTop`).
* `cobbDouglas_neoclassical`: `F(k, n) = k^α n^{1−α}` satisfies the assumptions, so they are
  consistent.
-/

open Set Filter Topology Real

namespace StokeyLucasPrescott.Overview

/-- The book's assumptions on the production function `F`, with `Fk` the marginal product of
capital at `n = 1`. Strict quasi-concavity is assumed on the open quadrant: on `ℝ²₊` it would
contradict `F(0, n) = 0`. -/
structure Neoclassical (F : ℝ → ℝ → ℝ) (Fk : ℝ → ℝ) : Prop where
  hom : ∀ l k n : ℝ, 0 < l → 0 ≤ k → 0 ≤ n → F (l * k) (l * n) = l * F k n
  zero_left : F 0 1 = 0
  deriv_k : ∀ k, 0 < k → HasDerivAt (fun k => F k 1) (Fk k) k
  cont_Fk : ContinuousOn Fk (Ioi 0)
  cont_F : ContinuousOn (fun k => F k 1) (Ici 0)
  Fk_pos : ∀ k, 0 < k → 0 < Fk k
  mono_n : ∀ k, 0 < k → StrictMonoOn (F k) (Ioi 0)
  quasi : ∀ x₁ x₂ y₁ y₂ θ : ℝ, 0 < x₁ → 0 < x₂ → 0 < y₁ → 0 < y₂ → (x₁, x₂) ≠ (y₁, y₂) →
    0 < θ → θ < 1 → min (F x₁ x₂) (F y₁ y₂) < F (θ * x₁ + (1 - θ) * y₁) (θ * x₂ + (1 - θ) * y₂)
  inada_zero : Tendsto Fk (𝓝[>] 0) atTop
  inada_top : Tendsto Fk atTop (𝓝 0)

/-- Total supply of goods `f(k) = F(k, 1) + (1 − δ)k`. -/
def goods (F : ℝ → ℝ → ℝ) (δ k : ℝ) : ℝ := F k 1 + (1 - δ) * k

namespace Neoclassical

variable {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ} (hF : Neoclassical F Fk)
include hF

/-- `k ↦ F(k, 1)` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_F : StrictMonoOn (fun k => F k 1) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) hF.cont_F fun x hx => ?_
  rw [interior_Ici] at hx
  rw [(hF.deriv_k x hx).deriv]
  exact hF.Fk_pos x hx

theorem F_pos {k : ℝ} (hk : 0 < k) : 0 < F k 1 := by
  have := hF.strictMonoOn_F (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hk.le) hk
  simpa [hF.zero_left] using this

/-- **`k ↦ F(k, 1)` is strictly concave on `[0, ∞)`**: homogeneity turns strict quasi-concavity
into strict concavity along `n = 1`, and strict monotonicity in `n` handles the endpoint `k = 0`. -/
theorem strictConcaveOn_F : StrictConcaveOn ℝ (Ici 0) (fun k => F k 1) := by
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [Set.mem_Ici] at hx hy
  -- the endpoint case `x = 0` (and symmetrically `y = 0`)
  have hend : ∀ {y b : ℝ}, 0 < y → 0 < b → b < 1 → b * F y 1 < F (b * y) 1 := by
    intro y b hy hb hb1
    have h := hF.hom b y 1 hb hy.le zero_le_one
    rw [mul_one] at h
    rw [← h]
    exact hF.mono_n (b * y) (mul_pos hb hy) (Set.mem_Ioi.2 hb) (Set.mem_Ioi.2 one_pos) hb1
  rcases hx.eq_or_lt with rfl | hx0
  · have hy0 : 0 < y := lt_of_le_of_ne hy hxy
    simpa [hF.zero_left] using hend hy0 hb (by linarith)
  rcases hy.eq_or_lt with rfl | hy0
  · simpa [hF.zero_left] using hend hx0 ha (by linarith)
  -- the interior case, by normalizing both points to the unit isoquant
  set p := F x 1
  set q := F y 1
  have hp : 0 < p := hF.F_pos hx0
  have hq : 0 < q := hF.F_pos hy0
  set S := a * p + b * q
  have hS : 0 < S := by positivity
  set θ := a * p / S
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [div_lt_one hS]; simp only [S]; nlinarith
  have hX : F (x / p) (1 / p) = 1 := by
    have h := hF.hom (1 / p) x 1 (by positivity) hx0.le zero_le_one
    rw [show 1 / p * x = x / p by ring, mul_one] at h
    rw [h]
    field_simp
    rfl
  have hY : F (y / q) (1 / q) = 1 := by
    have h := hF.hom (1 / q) y 1 (by positivity) hy0.le zero_le_one
    rw [show 1 / q * y = y / q by ring, mul_one] at h
    rw [h]
    field_simp
    rfl
  have hne : (x / p, 1 / p) ≠ (y / q, 1 / q) := by
    intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hpq : p = q := by
      have := h2
      field_simp at this
      linarith
    rw [hpq] at h1
    exact hxy (by field_simp at h1; linarith)
  have hq' := hF.quasi (x / p) (1 / p) (y / q) (1 / q) θ (by positivity) (by positivity)
    (by positivity) (by positivity) hne hθ0 hθ1
  rw [hX, hY, min_self] at hq'
  have h1θ : 1 - θ = b * q / S := by simp only [θ, S]; field_simp; ring
  have e1 : θ * (x / p) + (1 - θ) * (y / q) = 1 / S * (a * x + b * y) := by
    rw [h1θ]; simp only [θ]; field_simp
  have e2 : θ * (1 / p) + (1 - θ) * (1 / q) = 1 / S * 1 := by
    rw [h1θ]; simp only [θ, S]; field_simp; linarith
  rw [e1, e2, hF.hom (1 / S) _ 1 (by positivity) (by positivity) zero_le_one] at hq'
  rw [one_div, inv_mul_eq_div, one_lt_div hS] at hq'
  simpa [S] using hq'

theorem f_zero (δ : ℝ) : goods F δ 0 = 0 := by simp [goods, hF.zero_left]

/-- **Ex 2.1.** `f′(k) = F_k(k, 1) + 1 − δ`. -/
theorem hasDerivAt_f (δ : ℝ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (goods F δ) (Fk k + (1 - δ)) k := by
  exact ((hF.deriv_k k hk).add ((hasDerivAt_id k).const_mul (1 - δ))).congr_deriv (by ring)

/-- **Ex 2.1.** `f` is continuously differentiable on `(0, ∞)`. -/
theorem continuousOn_f' (δ : ℝ) : ContinuousOn (fun k => Fk k + (1 - δ)) (Ioi 0) :=
  hF.cont_Fk.add continuousOn_const

/-- **Ex 2.1.** `f′ > 0`. -/
theorem f'_pos {δ : ℝ} (hδ1 : δ ≤ 1) {k : ℝ} (hk : 0 < k) : 0 < Fk k + (1 - δ) := by
  have := hF.Fk_pos k hk
  linarith

/-- **Ex 2.1.** `f` is strictly increasing. -/
theorem strictMonoOn_f {δ : ℝ} (hδ1 : δ ≤ 1) : StrictMonoOn (goods F δ) (Ici 0) := by
  intro x hx y hy hxy
  have h := hF.strictMonoOn_F hx hy hxy
  simp only [goods]
  rw [Set.mem_Ici] at hx
  nlinarith

/-- **Ex 2.1.** `f` is strictly concave. -/
theorem strictConcaveOn_f (δ : ℝ) : StrictConcaveOn ℝ (Ici 0) (goods F δ) := by
  have hlin : ConcaveOn ℝ (Ici 0) (fun k : ℝ => (1 - δ) * k) :=
    ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => by simp only [smul_eq_mul]; exact le_of_eq (by ring)⟩
  exact hF.strictConcaveOn_F.add_concaveOn hlin

/-- **Ex 2.1.** `f′(k) → ∞` as `k → 0+`. -/
theorem f'_tendsto_zero (δ : ℝ) : Tendsto (fun k => Fk k + (1 - δ)) (𝓝[>] 0) atTop :=
  tendsto_atTop_add_const_right _ _ hF.inada_zero

/-- **Ex 2.1.** `f′(k) → 1 − δ` as `k → ∞`. -/
theorem f'_tendsto_atTop (δ : ℝ) : Tendsto (fun k => Fk k + (1 - δ)) atTop (𝓝 (1 - δ)) := by
  simpa using hF.inada_top.add_const (1 - δ)

end Neoclassical

/-- The Cobb–Douglas technology `F(k, n) = k^α n^{1−α}`. -/
noncomputable def cobbDouglas (α : ℝ) (k n : ℝ) : ℝ := k ^ α * n ^ (1 - α)

/-- **The assumptions are consistent**: Cobb–Douglas with `0 < α < 1` is neoclassical, with
`F_k(k, 1) = αk^{α−1}`. -/
theorem cobbDouglas_neoclassical {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Neoclassical (cobbDouglas α) (fun k => α * k ^ (α - 1)) := by
  have h1α : 0 < 1 - α := sub_pos.2 hα1
  have hlogF : ∀ a b : ℝ, 0 < a → 0 < b →
      log (cobbDouglas α a b) = α * log a + (1 - α) * log b := fun a b ha hb => by
    unfold cobbDouglas
    rw [log_mul (rpow_pos_of_pos ha α).ne' (rpow_pos_of_pos hb _).ne', log_rpow ha, log_rpow hb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l k n hl hk hn
    unfold cobbDouglas
    rw [mul_rpow hl.le hk, mul_rpow hl.le hn]
    have : l ^ α * l ^ (1 - α) = l := by
      rw [← rpow_add hl]; simp
    calc l ^ α * k ^ α * (l ^ (1 - α) * n ^ (1 - α))
        = (l ^ α * l ^ (1 - α)) * (k ^ α * n ^ (1 - α)) := by ring
      _ = l * (k ^ α * n ^ (1 - α)) := by rw [this]
  · simp [cobbDouglas, zero_rpow hα.ne']
  · intro k hk
    have := (hasDerivAt_rpow_const (p := α) (Or.inl hk.ne')).mul_const ((1 : ℝ) ^ (1 - α))
    simpa [cobbDouglas] using this
  · exact continuousOn_const.mul fun x hx =>
      (continuousAt_rpow_const x _ (Or.inl (Set.mem_Ioi.1 hx).ne')).continuousWithinAt
  · have : (fun k => cobbDouglas α k 1) = fun k => k ^ α := by
      funext k; simp [cobbDouglas]
    rw [this]
    exact (continuous_rpow_const hα.le).continuousOn
  · intro k hk
    exact mul_pos hα (rpow_pos_of_pos hk _)
  · intro k hk n hn m hm hnm
    unfold cobbDouglas
    exact mul_lt_mul_of_pos_left (rpow_lt_rpow (Set.mem_Ioi.1 hn).le hnm h1α) (rpow_pos_of_pos hk α)
  · intro x₁ x₂ y₁ y₂ θ hx₁ hx₂ hy₁ hy₂ hne hθ0 hθ1
    have hm₁ : 0 < θ * x₁ + (1 - θ) * y₁ := by nlinarith
    have hm₂ : 0 < θ * x₂ + (1 - θ) * y₂ := by nlinarith
    -- concavity of the logarithm in each coordinate, strictly in one of them
    have c₁ : θ * log x₁ + (1 - θ) * log y₁ ≤ log (θ * x₁ + (1 - θ) * y₁) := by
      have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hx₁) (Set.mem_Ioi.2 hy₁) hθ0.le
        (by linarith : 0 ≤ 1 - θ) (by ring)
      simpa [smul_eq_mul] using this
    have c₂ : θ * log x₂ + (1 - θ) * log y₂ ≤ log (θ * x₂ + (1 - θ) * y₂) := by
      have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hx₂) (Set.mem_Ioi.2 hy₂) hθ0.le
        (by linarith : 0 ≤ 1 - θ) (by ring)
      simpa [smul_eq_mul] using this
    have hstrict : α * (θ * log x₁ + (1 - θ) * log y₁) + (1 - α) * (θ * log x₂ + (1 - θ) * log y₂)
        < α * log (θ * x₁ + (1 - θ) * y₁) + (1 - α) * log (θ * x₂ + (1 - θ) * y₂) := by
      by_cases h₁ : x₁ = y₁
      · have h₂ : x₂ ≠ y₂ := fun h => hne (by rw [h₁, h])
        have s₂ : θ * log x₂ + (1 - θ) * log y₂ < log (θ * x₂ + (1 - θ) * y₂) := by
          have := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 hx₂) (Set.mem_Ioi.2 hy₂) h₂ hθ0
            (by linarith : 0 < 1 - θ) (by ring)
          simpa [smul_eq_mul] using this
        nlinarith
      · have s₁ : θ * log x₁ + (1 - θ) * log y₁ < log (θ * x₁ + (1 - θ) * y₁) := by
          have := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 hx₁) (Set.mem_Ioi.2 hy₁) h₁ hθ0
            (by linarith : 0 < 1 - θ) (by ring)
          simpa [smul_eq_mul] using this
        nlinarith
    have hFx := hlogF x₁ x₂ hx₁ hx₂
    have hFy := hlogF y₁ y₂ hy₁ hy₂
    have hFm := hlogF _ _ hm₁ hm₂
    have hposx : 0 < cobbDouglas α x₁ x₂ :=
      mul_pos (rpow_pos_of_pos hx₁ _) (rpow_pos_of_pos hx₂ _)
    have hposy : 0 < cobbDouglas α y₁ y₂ :=
      mul_pos (rpow_pos_of_pos hy₁ _) (rpow_pos_of_pos hy₂ _)
    have hposm : 0 < cobbDouglas α (θ * x₁ + (1 - θ) * y₁) (θ * x₂ + (1 - θ) * y₂) :=
      mul_pos (rpow_pos_of_pos hm₁ _) (rpow_pos_of_pos hm₂ _)
    rw [← log_lt_log_iff (lt_min hposx hposy) hposm]
    have hmin : log (min (cobbDouglas α x₁ x₂) (cobbDouglas α y₁ y₂)) ≤
        θ * log (cobbDouglas α x₁ x₂) + (1 - θ) * log (cobbDouglas α y₁ y₂) := by
      have h1 := log_le_log (lt_min hposx hposy) (min_le_left _ _)
      have h2 := log_le_log (lt_min hposx hposy) (min_le_right _ _)
      nlinarith
    rw [hFx, hFy] at hmin
    rw [hFm]
    nlinarith
  · exact (tendsto_rpow_neg_nhdsGT_zero (by linarith : α - 1 < 0)).const_mul_atTop hα
  · have := (tendsto_rpow_neg_atTop h1α).const_mul α
    simpa [neg_sub] using this

end StokeyLucasPrescott.Overview

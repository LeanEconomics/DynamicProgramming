/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.FirmDynamics

/-!
# A constant-returns-to-scale industry (Exercise 6.9)

SLP §6.5, pp. 159–160. Output is `q = xφ(y/x)` (`crsQ`), the return is
`F(x, y) = S(xφ(y/x)) − θ[y − (1 − δ)x]` (`crsF`) and `Γ(x) = [0, αx]`, with `φ` strictly
decreasing and strictly concave on `[0, α]`, `φ(0) > 0 = φ(α)`, `φ'(u) → −∞` as `u → α`, and
`S` bounded, strictly increasing and strictly concave (`CRSHyp`).

This file works with any `V` concave on `[0, K]` that solves the functional equation there, with
`Γ(x) = [0, min{αx, K}]` (`CRSValue`).

* `V` is strictly increasing (`strictMonoOn`), since `F` is (`crsF_lt`): by concavity
  `x'φ(y/x') ≥ xφ(y/x) + (x' − x)φ(0)`.
* **Interior choices** (`argmax_lt`): at `x > 0` the maximizer is below `αx`, because
  `F_y → −∞` there while `V` has bounded slopes.
* **Unique maximizer** (`argmax_unique`): `y ↦ S(xφ(y/x))` is strictly concave.
* **Exercise 6.9a** (`hasDerivAt_V`):
  `v'(x) = S'[xφ(u)][φ(u) − uφ'(u)] + θ(1 − δ)`, `u = g(x)/x`.
* **Exercise 6.9b** (`argmax_mono`): `g` is nondecreasing. `z ↦ F(z, y) − F(z, y')` is strictly
  increasing for `y' < y`, because `S'` falls in output while `φ(u) − uφ'(u)` rises in `u`.
* **Exercise 6.9c** (`stationary_eq`, `stationary_unique`, `no_stationary`): an interior
  stationary point satisfies `S'(x̄φ(1))[βφ(1) + (1 − β)φ'(1)] = θ(1 − β(1 − δ))`. So there is at
  most one, and **none** when `βφ(1) + (1 − β)φ'(1) ≤ 0`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

/-- Output `q = xφ(y/x)`. -/
noncomputable def crsQ (φ : ℝ → ℝ) (x y : ℝ) : ℝ := x * φ (y / x)

/-- The return `F(x, y) = S(xφ(y/x)) − θ[y − (1 − δ)x]`. -/
noncomputable def crsF (S φ : ℝ → ℝ) (θ δ x y : ℝ) : ℝ := S (crsQ φ x y) - θ * (y - (1 - δ) * x)

/-- The hypotheses of Exercise 6.9. -/
structure CRSHyp (S φ S' φ' : ℝ → ℝ) (α θ δ β : ℝ) : Prop where
  α_gt : 1 < α
  θ_pos : 0 < θ
  δ_pos : 0 < δ
  δ_lt : δ < 1
  β_pos : 0 < β
  β_lt : β < 1
  φ_anti : StrictAntiOn φ (Icc 0 α)
  φ_conc : StrictConcaveOn ℝ (Icc 0 α) φ
  φ_zero : 0 < φ 0
  φ_α : φ α = 0
  φ_deriv : ∀ u ∈ Ico 0 α, HasDerivAt φ (φ' u) u
  φ'_lim : Tendsto φ' (𝓝[<] α) atBot
  S_mono : StrictMonoOn S (Ici 0)
  S_conc : StrictConcaveOn ℝ (Ici 0) S
  S_deriv : ∀ q, 0 ≤ q → HasDerivAt S (S' q) q

namespace CRSHyp

variable {S φ S' φ' : ℝ → ℝ} {α θ δ β : ℝ} (h : CRSHyp S φ S' φ' α θ δ β)
include h

theorem α_pos : 0 < α := by linarith [h.α_gt]

theorem φ_nonneg {u : ℝ} (hu : u ∈ Icc 0 α) : 0 ≤ φ u := by
  rcases eq_or_lt_of_le hu.2 with he | hlt
  · rw [he, h.φ_α]
  · rw [← h.φ_α]; exact (h.φ_anti hu ⟨h.α_pos.le, le_rfl⟩ hlt).le

theorem φ_le {u : ℝ} (hu : u ∈ Icc 0 α) : φ u ≤ φ 0 := by
  rcases eq_or_lt_of_le hu.1 with he | hlt
  · rw [← he]
  · exact (h.φ_anti ⟨le_rfl, h.α_pos.le⟩ hu hlt).le

theorem φ_pos {u : ℝ} (hu : u ∈ Ico 0 α) : 0 < φ u := by
  rw [← h.φ_α]; exact h.φ_anti ⟨hu.1, hu.2.le⟩ ⟨h.α_pos.le, le_rfl⟩ hu.2

/-- `S' > 0`. -/
theorem S'_pos {q : ℝ} (hq : 0 ≤ q) : 0 < S' q := by
  have h1 := tangent_le h.S_conc.concaveOn (a := q) (b := q + 1) (mem_Ici.2 hq)
    (mem_Ici.2 (by linarith)) (h.S_deriv q hq)
  have h2 := h.S_mono (mem_Ici.2 hq) (mem_Ici.2 (by linarith : 0 ≤ q + 1)) (by linarith)
  linarith

/-- `S'` falls strictly. -/
theorem S'_lt {q q' : ℝ} (hq : 0 ≤ q) (hqq' : q < q') : S' q' < S' q :=
  deriv_lt_of_strictConcave h.S_conc (mem_Ici.2 hq) (mem_Ici.2 (by linarith)) hqq'
    (h.S_deriv q hq) (h.S_deriv q' (by linarith))

omit h in
/-- `u ∈ [0, α]` for `0 ≤ y ≤ αx`, `x > 0`. -/
theorem ratio_mem {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ α * x) : y / x ∈ Icc 0 α :=
  ⟨div_nonneg hy hx.le, (div_le_iff₀ hx).2 (by linarith)⟩

theorem crsQ_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ α * x) :
    0 ≤ crsQ φ x y := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · simp [crsQ, ← h0]
  · exact mul_nonneg hx (h.φ_nonneg (ratio_mem hpos hy hyx))

/-- `x'φ(y/x') ≥ xφ(y/x) + (x' − x)φ(0)` for `x ≤ x'`. -/
theorem crsQ_mono {x x' y : ℝ} (hx : 0 ≤ x) (hxx' : x ≤ x') (hy : 0 ≤ y) (hyx : y ≤ α * x) :
    crsQ φ x y + (x' - x) * φ 0 ≤ crsQ φ x' y := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0
    have : y = 0 := by linarith
    subst this
    simp [crsQ]
  have hx'pos : 0 < x' := by linarith
  have hu := ratio_mem hpos hy hyx
  -- `y/x' = (x/x')(y/x) + (1 − x/x')·0`
  have hc := h.φ_conc.concaveOn.2 hu (show (0 : ℝ) ∈ Icc 0 α from ⟨le_rfl, h.α_pos.le⟩)
    (div_nonneg hx hx'pos.le) (sub_nonneg.2 ((div_le_one hx'pos).2 hxx'))
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero] at hc
  rw [show x / x' * (y / x) = y / x' by field_simp] at hc
  simp only [crsQ]
  have := mul_le_mul_of_nonneg_left hc hx'pos.le
  have e : x' * (x / x' * φ (y / x) + (1 - x / x') * φ 0) = x * φ (y / x) + (x' - x) * φ 0 := by
    field_simp
  linarith

/-- **`F` is strictly increasing in `x`.** -/
theorem crsF_lt {x x' y : ℝ} (hx : 0 ≤ x) (hxx' : x < x') (hy : 0 ≤ y) (hyx : y ≤ α * x) :
    crsF S φ θ δ x y < crsF S φ θ δ x' y := by
  have h1 := h.crsQ_mono hx hxx'.le hy hyx
  have h2 := h.crsQ_nonneg hx hy hyx
  have h3 : crsQ φ x y ≤ crsQ φ x' y := by nlinarith [h.φ_zero]
  have h4 : S (crsQ φ x y) ≤ S (crsQ φ x' y) :=
    h.S_mono.monotoneOn (mem_Ici.2 h2) (mem_Ici.2 (h2.trans h3)) h3
  have h5 : 0 < θ * ((1 - δ) * (x' - x)) := by
    have := h.θ_pos
    have : 0 < 1 - δ := by linarith [h.δ_lt]
    have : 0 < x' - x := by linarith
    positivity
  simp only [crsF]
  nlinarith

/-- **The perspective is concave**: `a·q(x, y) + b·q(x', y') ≤ q(ax + bx', ay + by')`. -/
theorem crsQ_concave {x x' y y' a b : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (hy : 0 ≤ y)
    (hyx : y ≤ α * x) (hy' : 0 ≤ y') (hyx' : y' ≤ α * x') (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    a * crsQ φ x y + b * crsQ φ x' y' ≤ crsQ φ (a * x + b * x') (a * y + b * y') := by
  rcases eq_or_lt_of_le hx with h0 | hxp
  · subst h0
    have : y = 0 := by linarith
    subst this
    simp only [crsQ, zero_mul, mul_zero, zero_add, zero_div]
    rcases eq_or_lt_of_le hb with hb0 | hbp
    · subst hb0; simp
    · rw [show b * y' / (b * x') = y' / x' by
        rcases eq_or_lt_of_le hx' with hx0 | hx'p
        · subst hx0; simp
        · field_simp]
      ring_nf; exact le_rfl
  rcases eq_or_lt_of_le hx' with h0 | hx'p
  · subst h0
    have : y' = 0 := by linarith
    subst this
    simp only [crsQ, zero_mul, mul_zero, add_zero, zero_div]
    rcases eq_or_lt_of_le ha with ha0 | hap
    · subst ha0; simp
    · rw [show a * y / (a * x) = y / x by field_simp]
      ring_nf; exact le_rfl
  rcases eq_or_lt_of_le ha with ha0 | hap
  · subst ha0; have : b = 1 := by linarith [hab]
    subst this; simp
  rcases eq_or_lt_of_le hb with hb0 | hbp
  · subst hb0; have : a = 1 := by linarith
    subst this; simp
  set z := a * x + b * x'
  have hz : 0 < z := by positivity
  have hu := ratio_mem hxp hy hyx
  have hu' := ratio_mem hx'p hy' hyx'
  have hc := h.φ_conc.concaveOn.2 hu hu' (div_nonneg (mul_nonneg ha hx) hz.le)
    (div_nonneg (mul_nonneg hb hx') hz.le) (by simp only [z]; field_simp)
  simp only [smul_eq_mul] at hc
  rw [show a * x / z * (y / x) + b * x' / z * (y' / x') = (a * y + b * y') / z by
    field_simp] at hc
  simp only [crsQ]
  have := mul_le_mul_of_nonneg_left hc hz.le
  have e : z * (a * x / z * φ (y / x) + b * x' / z * φ (y' / x')) =
      a * (x * φ (y / x)) + b * (x' * φ (y' / x')) := by field_simp
  linarith

/-- **Strictly so across rays**: if `x, x' > 0` and `y/x ≠ y'/x'`. -/
theorem crsQ_strict {x x' y y' a b : ℝ} (hx : 0 < x) (hx' : 0 < x') (hy : 0 ≤ y)
    (hyx : y ≤ α * x) (hy' : 0 ≤ y') (hyx' : y' ≤ α * x') (ha : 0 < a) (hb : 0 < b)
    (_hab : a + b = 1) (hne : y / x ≠ y' / x') :
    a * crsQ φ x y + b * crsQ φ x' y' < crsQ φ (a * x + b * x') (a * y + b * y') := by
  set z := a * x + b * x'
  have hz : 0 < z := by positivity
  have hu := ratio_mem hx hy hyx
  have hu' := ratio_mem hx' hy' hyx'
  have hc := h.φ_conc.2 hu hu' hne (div_pos (mul_pos ha hx) hz) (div_pos (mul_pos hb hx') hz)
    (by simp only [z]; field_simp)
  simp only [smul_eq_mul] at hc
  rw [show a * x / z * (y / x) + b * x' / z * (y' / x') = (a * y + b * y') / z by
    field_simp] at hc
  simp only [crsQ]
  have := mul_lt_mul_of_pos_left hc hz
  have e : z * (a * x / z * φ (y / x) + b * x' / z * φ (y' / x')) =
      a * (x * φ (y / x)) + b * (x' * φ (y' / x')) := by field_simp
  linarith

end CRSHyp

/-! ### Concave solutions of the functional equation -/

/-- `V` is concave on `[0, K]` and solves the functional equation there, with
`Γ(x) = [0, min{αx, K}]`. -/
structure CRSValue (S φ S' φ' : ℝ → ℝ) (α θ δ β K : ℝ) (V : ℝ → ℝ) : Prop where
  hyp : CRSHyp S φ S' φ' α θ δ β
  K_pos : 0 < K
  le : ∀ x ∈ Icc (0 : ℝ) K, ∀ y ∈ Icc (0 : ℝ) (min (α * x) K),
    crsF S φ θ δ x y + β * V y ≤ V x
  arg : ∀ x ∈ Icc (0 : ℝ) K, ∃ y ∈ Icc (0 : ℝ) (min (α * x) K),
    crsF S φ θ δ x y + β * V y = V x
  conc : ConcaveOn ℝ (Icc 0 K) V

namespace CRSValue

variable {S φ S' φ' : ℝ → ℝ} {α θ δ β K : ℝ} {V : ℝ → ℝ}
  (h : CRSValue S φ S' φ' α θ δ β K V)
include h

theorem mem_Γ_mono {x x' y : ℝ} (hxx' : x ≤ x') (hy : y ∈ Icc (0 : ℝ) (min (α * x) K)) :
    y ∈ Icc (0 : ℝ) (min (α * x') K) :=
  ⟨hy.1, hy.2.trans (min_le_min (mul_le_mul_of_nonneg_left hxx' h.hyp.α_pos.le) le_rfl)⟩

/-- **`V` is strictly increasing.** -/
theorem strictMonoOn : StrictMonoOn V (Icc 0 K) := by
  intro x hx x' hx' hxx'
  obtain ⟨y, hy, hyv⟩ := h.arg x hx
  have := h.hyp.crsF_lt hx.1 hxx' hy.1 (hy.2.trans (min_le_left _ _))
  have := h.le x' hx' y (h.mem_Γ_mono hxx'.le hy)
  linarith

/-- Concavity: `V(y) − V(y − s) ≤ (s/y)(V(y) − V(0))`. -/
theorem slope_le {y s : ℝ} (hy : 0 < y) (hyK : y ≤ K) (hs : 0 ≤ s) (hsy : s ≤ y) :
    V y - V (y - s) ≤ s / y * (V y - V 0) := by
  have := h.conc.2 (show (0 : ℝ) ∈ Icc 0 K from ⟨le_rfl, h.K_pos.le⟩)
    (show y ∈ Icc 0 K from ⟨hy.le, hyK⟩) (div_nonneg hs hy.le)
    (sub_nonneg.2 ((div_le_one hy).2 hsy)) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add] at this
  rw [show (1 - s / y) * y = y - s by field_simp] at this
  nlinarith

/-- **Interior choices**: at `x > 0` the maximizer is below `αx`. -/
theorem argmax_lt {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) K) (hx0 : 0 < x)
    (hy : y ∈ Icc (0 : ℝ) (min (α * x) K)) (hyv : crsF S φ θ δ x y + β * V y = V x) :
    y < α * x := by
  have H := h.hyp
  have hα := H.α_pos
  by_contra hge
  push Not at hge
  have hyeq : y = α * x := le_antisymm (hy.2.trans (min_le_left _ _)) hge
  have hyK : y ≤ K := hy.2.trans (min_le_right _ _)
  have hy0 : 0 < y := by rw [hyeq]; positivity
  set D := V y - V 0
  set c := S' (x * φ 0)
  have hc : 0 < c := H.S'_pos (by have := H.φ_zero; positivity)
  -- a slope of `φ` steep enough
  obtain ⟨u, hu1, hu2⟩ := ((H.φ'_lim.eventually (eventually_lt_atBot
    (-(β * |D| / (α * c * x) + 1)))).and (Ioo_mem_nhdsLT (show max 0 (α - 1) < α by
      simp [hα]))).exists
  have hu0 : 0 < u := (le_max_left _ _).trans_lt hu2.1
  set s := α - u
  have hs0 : 0 < s := by simp only [s]; linarith [hu2.2]
  have hs1 : s < 1 := by simp only [s]; linarith [(le_max_right 0 (α - 1)).trans_lt hu2.1]
  -- the alternative `y_s = x(α − s) = xu`
  have hys : x * u ∈ Icc (0 : ℝ) (min (α * x) K) :=
    ⟨by positivity, le_min (by nlinarith [hu2.2]) (by nlinarith [hu2.2])⟩
  have hle := h.le x hx (x * u) hys
  have hslope := h.slope_le hy0 hyK (s := x * s) (by positivity) (by rw [hyeq]; nlinarith)
  rw [show y - x * s = x * u by simp only [s]; rw [hyeq]; ring] at hslope
  -- `S(xφ(u)) − S(0) ≥ c·x·φ(u) ≥ c·x·s·(−φ'(u))`
  have huI : u ∈ Icc 0 α := ⟨hu0.le, hu2.2.le⟩
  have hφu := H.φ_nonneg huI
  have hq : 0 ≤ x * φ u := by positivity
  have htan := tangent_le H.S_conc.concaveOn (a := x * φ u) (b := 0) (mem_Ici.2 hq)
    (mem_Ici.2 le_rfl) (H.S_deriv _ hq)
  have hS'm : c ≤ S' (x * φ u) := by
    rcases eq_or_lt_of_le (mul_le_mul_of_nonneg_left (H.φ_le huI) hx0.le) with he | hlt
    · rw [he]
    · exact (H.S'_lt hq hlt).le
  have htanφ := tangent_le H.φ_conc.concaveOn (a := u) (b := α) huI ⟨hα.le, le_rfl⟩
    (H.φ_deriv u ⟨hu0.le, hu2.2⟩)
  rw [H.φ_α] at htanφ
  -- the comparison
  have hF : crsF S φ θ δ x (x * u) - crsF S φ θ δ x y =
      S (x * φ u) - S 0 + θ * (x * s) := by
    simp only [crsF, crsQ, hyeq]
    rw [show α * x / x = α by field_simp, H.φ_α, mul_zero,
      show x * u / x = u by field_simp]
    simp only [s]; ring
  have hA : crsF S φ θ δ x (x * u) - crsF S φ θ δ x y ≤ β * (V y - V (x * u)) := by
    linarith
  have hC : β * (V y - V (x * u)) ≤ β * (s / α) * |D| := by
    have h1 : x * s / y = s / α := by rw [hyeq]; field_simp
    rw [h1] at hslope
    have h2 : s / α * (V y - V 0) ≤ s / α * |D| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    have := mul_le_mul_of_nonneg_left (hslope.trans h2) H.β_pos.le
    linarith [show β * (s / α * |D|) = β * (s / α) * |D| by ring]
  have hD : c * (x * φ u) ≤ S (x * φ u) - S 0 := by
    have := mul_le_mul_of_nonneg_right hS'm hq
    linarith
  have hE : s * -φ' u ≤ φ u := by simp only [s]; linarith
  have hE' : c * x * (s * -φ' u) ≤ c * (x * φ u) := by
    have := mul_le_mul_of_nonneg_left hE (mul_pos hc hx0).le
    linarith [show c * x * φ u = c * (x * φ u) by ring]
  have hθ : 0 ≤ θ * (x * s) := by have := H.θ_pos; positivity
  have hmain : c * x * (s * -φ' u) ≤ β * (s / α) * |D| := by linarith
  have hφ' : β * |D| / (α * c * x) + 1 < -φ' u := by linarith
  have hpos : 0 < c * x * s := by positivity
  have h1 := mul_lt_mul_of_pos_left hφ' hpos
  have e : c * x * s * (β * |D| / (α * c * x) + 1) = β * (s / α) * |D| + c * x * s := by
    field_simp
  rw [e] at h1
  nlinarith

/-- **The maximizer is unique**: `y ↦ S(xφ(y/x))` is strictly concave. -/
theorem argmax_unique {x y₁ y₂ : ℝ} (hx : x ∈ Icc (0 : ℝ) K)
    (hy₁ : y₁ ∈ Icc (0 : ℝ) (min (α * x) K)) (hy₂ : y₂ ∈ Icc (0 : ℝ) (min (α * x) K))
    (h₁ : crsF S φ θ δ x y₁ + β * V y₁ = V x) (h₂ : crsF S φ θ δ x y₂ + β * V y₂ = V x) :
    y₁ = y₂ := by
  have H := h.hyp
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst hx0
    have e1 : y₁ = 0 := le_antisymm (by simpa using hy₁.2.trans (min_le_left _ _)) hy₁.1
    have e2 : y₂ = 0 := le_antisymm (by simpa using hy₂.2.trans (min_le_left _ _)) hy₂.1
    rw [e1, e2]
  by_contra hne
  set m := (y₁ + y₂) / 2
  have hmΓ : m ∈ Icc (0 : ℝ) (min (α * x) K) :=
    ⟨by simp only [m]; linarith [hy₁.1, hy₂.1], by simp only [m]; linarith [hy₁.2, hy₂.2]⟩
  have hu₁ := CRSHyp.ratio_mem hx0 hy₁.1 (hy₁.2.trans (min_le_left _ _))
  have hu₂ := CRSHyp.ratio_mem hx0 hy₂.1 (hy₂.2.trans (min_le_left _ _))
  have hune : y₁ / x ≠ y₂ / x := fun he => hne (by field_simp at he; linarith)
  have hφ := H.φ_conc.2 hu₁ hu₂ hune (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hφ
  rw [show 1 / 2 * (y₁ / x) + 1 / 2 * (y₂ / x) = m / x by simp only [m]; ring] at hφ
  -- output at the midpoint exceeds the average output
  have hq : (crsQ φ x y₁ + crsQ φ x y₂) / 2 < crsQ φ x m := by
    simp only [crsQ]; nlinarith
  have hq₁ := H.crsQ_nonneg hx.1 hy₁.1 (hy₁.2.trans (min_le_left _ _))
  have hq₂ := H.crsQ_nonneg hx.1 hy₂.1 (hy₂.2.trans (min_le_left _ _))
  have hS1 : S ((crsQ φ x y₁ + crsQ φ x y₂) / 2) < S (crsQ φ x m) :=
    H.S_mono (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) hq
  have hS2 := H.S_conc.concaveOn.2 (mem_Ici.2 hq₁) (mem_Ici.2 hq₂)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hS2
  rw [show 1 / 2 * crsQ φ x y₁ + 1 / 2 * crsQ φ x y₂ = (crsQ φ x y₁ + crsQ φ x y₂) / 2 by ring]
    at hS2
  have hV := h.conc.2 (show y₁ ∈ Icc 0 K from ⟨hy₁.1, hy₁.2.trans (min_le_right _ _)⟩)
    (show y₂ ∈ Icc 0 K from ⟨hy₂.1, hy₂.2.trans (min_le_right _ _)⟩)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hV
  rw [show 1 / 2 * y₁ + 1 / 2 * y₂ = m by simp only [m]; ring] at hV
  have := h.le x hx m hmΓ
  simp only [crsF] at this h₁ h₂
  have hβV := mul_le_mul_of_nonneg_left hV H.β_pos.le
  have hθ : θ * (m - (1 - δ) * x) =
      (θ * (y₁ - (1 - δ) * x) + θ * (y₂ - (1 - δ) * x)) / 2 := by simp only [m]; ring
  linarith

/-- The derivative of `F` in `x`: `S'[xφ(u)][φ(u) − uφ'(u)] + θ(1 − δ)`, `u = y/x`. -/
theorem hasDerivAt_crsF_x {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyx : y < α * x) :
    HasDerivAt (fun x' => crsF S φ θ δ x' y)
      (S' (crsQ φ x y) * (φ (y / x) - y / x * φ' (y / x)) + θ * (1 - δ)) x := by
  have H := h.hyp
  have hu : y / x ∈ Ico 0 α := ⟨div_nonneg hy hx.le, (div_lt_iff₀ hx).2 (by linarith)⟩
  have hdiv : HasDerivAt (fun x' : ℝ => y / x') (-(y / x ^ 2)) x := by
    have := (hasDerivAt_inv hx.ne').const_mul y
    convert this using 1
    · funext x'; rw [div_eq_mul_inv]
    · rw [div_eq_mul_inv]; ring
  have hφc : HasDerivAt (fun x' : ℝ => φ (y / x')) (φ' (y / x) * -(y / x ^ 2)) x :=
    (H.φ_deriv _ hu).comp x hdiv
  have hq : HasDerivAt (fun x' : ℝ => x' * φ (y / x'))
      (1 * φ (y / x) + x * (φ' (y / x) * -(y / x ^ 2))) x := (hasDerivAt_id' x).mul hφc
  have hq0 : 0 ≤ crsQ φ x y := H.crsQ_nonneg hx.le hy hyx.le
  have hS := (H.S_deriv _ hq0).comp x hq
  have hlin : HasDerivAt (fun x' : ℝ => θ * (y - (1 - δ) * x')) (θ * (0 - (1 - δ) * 1)) x :=
    ((hasDerivAt_const x y).sub ((hasDerivAt_id' x).const_mul (1 - δ))).const_mul θ
  have := hS.sub hlin
  have hx' : x ≠ 0 := hx.ne'
  convert this using 1
  · funext x'; rfl
  · field_simp; ring

/-- **Exercise 6.9a: the envelope condition.** On `(0, K)`, `V` is differentiable with
`V'(x) = S'[xφ(u)][φ(u) − uφ'(u)] + θ(1 − δ)`, `u = g(x)/x`. -/
theorem hasDerivAt_V {x y : ℝ} (hx : x ∈ Ioo 0 K) (hy : y ∈ Icc (0 : ℝ) (min (α * x) K))
    (hyv : crsF S φ θ δ x y + β * V y = V x) :
    HasDerivAt V (S' (crsQ φ x y) * (φ (y / x) - y / x * φ' (y / x)) + θ * (1 - δ)) x := by
  have H := h.hyp
  have hxI : x ∈ Icc (0 : ℝ) K := ⟨hx.1.le, hx.2.le⟩
  have hlt := h.argmax_lt hxI hx.1 hy hyv
  set W : ℝ → ℝ := fun x' => crsF S φ θ δ x' y + β * V y
  have hW : HasDerivAt W _ x := (h.hasDerivAt_crsF_x hx.1 hy.1 hlt).add_const (β * V y)
  have hX : Icc (0 : ℝ) K ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  have hle : ∀ᶠ x' in 𝓝 x, W x' ≤ V x' := by
    have hball : Ioi (y / α) ∈ 𝓝 x := Ioi_mem_nhds ((div_lt_iff₀ H.α_pos).2 (by linarith))
    filter_upwards [hX, hball] with x' hx' hx'α
    refine h.le x' hx' y ⟨hy.1, le_min ?_ (hy.2.trans (min_le_right _ _))⟩
    rw [mem_Ioi, div_lt_iff₀ H.α_pos] at hx'α; linarith
  have := (theorem_4_10 h.conc hX hW.hasFDerivAt hyv hle).hasDerivAt
  simpa using this

/-- **The first-order condition** at an interior maximizer: `S'[xφ(u)]φ'(u) − θ + βV'(y) = 0`. -/
theorem foc {x y d : ℝ} (hx : x ∈ Icc (0 : ℝ) K) (hx0 : 0 < x) (hy0 : 0 < y)
    (hyK : y < K) (hy : y ∈ Icc (0 : ℝ) (min (α * x) K))
    (hyv : crsF S φ θ δ x y + β * V y = V x) (hd : HasDerivAt V d y) :
    S' (crsQ φ x y) * φ' (y / x) - θ + β * d = 0 := by
  have H := h.hyp
  have hlt := h.argmax_lt hx hx0 hy hyv
  have hu : y / x ∈ Ico 0 α := ⟨div_nonneg hy0.le hx0.le, (div_lt_iff₀ hx0).2 (by linarith)⟩
  have hdiv : HasDerivAt (fun z : ℝ => z / x) (1 / x) y := by
    simpa using (hasDerivAt_id' y).div_const x
  have hq : HasDerivAt (fun z : ℝ => x * φ (z / x)) (x * (φ' (y / x) * (1 / x))) y :=
    ((H.φ_deriv _ hu).comp y hdiv).const_mul x
  have hS := (H.S_deriv _ (H.crsQ_nonneg hx0.le hy0.le hlt.le)).comp y hq
  have hΦ : HasDerivAt (fun z => crsF S φ θ δ x z + β * V z)
      (S' (crsQ φ x y) * (x * (φ' (y / x) * (1 / x))) - θ * (1 - 0) + β * d) y := by
    have hlin : HasDerivAt (fun z : ℝ => θ * (z - (1 - δ) * x)) (θ * (1 - 0)) y :=
      ((hasDerivAt_id' y).sub (hasDerivAt_const y _)).const_mul θ
    exact (hS.sub hlin).add (hd.const_mul β)
  have hloc : IsLocalMax (fun z => crsF S φ θ δ x z + β * V z) y := by
    have hlt' : y < min (α * x) K := lt_min hlt hyK
    filter_upwards [Ioo_mem_nhds hy0 hlt'] with z hz
    rw [hyv]
    exact h.le x hx z ⟨hz.1.le, hz.2.le⟩
  have := hloc.hasDerivAt_eq_zero hΦ
  rw [← this]
  field_simp
  ring

/-- `ψ(w) = φ(w) − wφ'(w)` is at least `φ(0)` and nondecreasing on `[0, α)`. -/
theorem psi_props {u u' : ℝ} (hu' : u' ∈ Ico 0 α) (hu : u ∈ Ico 0 α) (huu' : u' ≤ u) :
    φ 0 ≤ φ u' - u' * φ' u' ∧ φ u' - u' * φ' u' ≤ φ u - u * φ' u := by
  have H := h.hyp
  have hI' : u' ∈ Icc 0 α := ⟨hu'.1, hu'.2.le⟩
  have hI : u ∈ Icc 0 α := ⟨hu.1, hu.2.le⟩
  have h0 := tangent_le H.φ_conc.concaveOn (a := u') (b := 0) hI' ⟨le_rfl, H.α_pos.le⟩
    (H.φ_deriv u' hu')
  have h1 := tangent_le H.φ_conc.concaveOn (a := u) (b := u') hI hI' (H.φ_deriv u hu)
  have h2 := deriv_le_of_concave H.φ_conc.concaveOn hI' hI huu' (H.φ_deriv u' hu')
    (H.φ_deriv u hu)
  refine ⟨by linarith, ?_⟩
  nlinarith [hu'.1]

/-- **Exercise 6.9b: the policy is nondecreasing.** -/
theorem argmax_mono {x x' y y' : ℝ} (hx : x ∈ Icc (0 : ℝ) K) (hx' : x' ∈ Icc (0 : ℝ) K)
    (hxx' : x ≤ x') (hy : y ∈ Icc (0 : ℝ) (min (α * x) K))
    (hyv : crsF S φ θ δ x y + β * V y = V x) (hy' : y' ∈ Icc (0 : ℝ) (min (α * x') K))
    (hyv' : crsF S φ θ δ x' y' + β * V y' = V x') : y ≤ y' := by
  have H := h.hyp
  by_contra hlt
  push Not at hlt
  have hx0 : 0 < x := by
    rcases eq_or_lt_of_le hx.1 with he | hpos
    · subst he; have := hy.2.trans (min_le_left _ _); simp at this; linarith [hy'.1]
    · exact hpos
  have hxlt : x < x' := by
    rcases eq_or_lt_of_le hxx' with he | hlt'
    · subst he; exact absurd (h.argmax_unique hx hy hy' hyv hyv') hlt.ne'
    · exact hlt'
  have hyα := h.argmax_lt hx hx0 hy hyv
  -- the two optimality conditions
  have hA := h.le x hx y' ⟨hy'.1, hlt.le.trans hy.2⟩
  have hB := h.le x' hx' y (h.mem_Γ_mono hxx' hy)
  -- `D(z) = F(z, y) − F(z, y')` is strictly increasing on `[x, x']`
  set D : ℝ → ℝ := fun z => crsF S φ θ δ z y - crsF S φ θ δ z y'
  have hDd : ∀ z ∈ Icc x x', HasDerivAt D
      ((S' (crsQ φ z y) * (φ (y / z) - y / z * φ' (y / z)) + θ * (1 - δ)) -
        (S' (crsQ φ z y') * (φ (y' / z) - y' / z * φ' (y' / z)) + θ * (1 - δ))) z :=
    fun z hz => by
      have hz0 : 0 < z := hx0.trans_le hz.1
      have hyz : y < α * z := hyα.trans_le (mul_le_mul_of_nonneg_left hz.1 H.α_pos.le)
      exact (h.hasDerivAt_crsF_x hz0 hy.1 hyz).sub
        (h.hasDerivAt_crsF_x hz0 hy'.1 (hlt.trans hyz))
  have hpos : ∀ z ∈ Icc x x',
      0 < (S' (crsQ φ z y) * (φ (y / z) - y / z * φ' (y / z)) + θ * (1 - δ)) -
        (S' (crsQ φ z y') * (φ (y' / z) - y' / z * φ' (y' / z)) + θ * (1 - δ)) := fun z hz => by
    have hz0 : 0 < z := hx0.trans_le hz.1
    have hyz : y < α * z := hyα.trans_le (mul_le_mul_of_nonneg_left hz.1 H.α_pos.le)
    have hu : y / z ∈ Ico 0 α := ⟨div_nonneg hy.1 hz0.le, (div_lt_iff₀ hz0).2 (by linarith)⟩
    have hu' : y' / z ∈ Ico 0 α :=
      ⟨div_nonneg hy'.1 hz0.le, (div_lt_iff₀ hz0).2 (by linarith)⟩
    have huu' : y' / z < y / z := div_lt_div_of_pos_right hlt hz0
    obtain ⟨hψ0, hψ⟩ := h.psi_props hu' hu huu'.le
    have hq : crsQ φ z y < crsQ φ z y' := by
      simp only [crsQ]
      exact mul_lt_mul_of_pos_left (H.φ_anti ⟨hu'.1, hu'.2.le⟩ ⟨hu.1, hu.2.le⟩ huu') hz0
    have hq0 := H.crsQ_nonneg hz0.le hy.1 hyz.le
    have hS := H.S'_lt hq0 hq
    have hSp := H.S'_pos hq0
    have hφ0 := H.φ_zero
    nlinarith [mul_le_mul_of_nonneg_left hψ hSp.le]
  have hmono : StrictMonoOn D (Icc x x') := by
    refine strictMonoOn_of_deriv_pos (convex_Icc x x')
      (fun z hz => (hDd z hz).continuousAt.continuousWithinAt) fun z hz => ?_
    rw [interior_Icc] at hz
    rw [(hDd z ⟨hz.1.le, hz.2.le⟩).deriv]
    exact hpos z ⟨hz.1.le, hz.2.le⟩
  have := hmono ⟨le_rfl, hxx'⟩ ⟨hxx', le_rfl⟩ hxlt
  simp only [D] at this
  linarith

/-- **Exercise 6.9c: the stationary equation.** An interior stationary point satisfies
`S'(x̄φ(1))[βφ(1) + (1 − β)φ'(1)] = θ(1 − β(1 − δ))`. -/
theorem stationary_eq {x : ℝ} (hx : x ∈ Ioo 0 K) (hfix : crsF S φ θ δ x x + β * V x = V x) :
    S' (x * φ 1) * (β * φ 1 + (1 - β) * φ' 1) = θ * (1 - β * (1 - δ)) := by
  have H := h.hyp
  have hxI : x ∈ Icc (0 : ℝ) K := ⟨hx.1.le, hx.2.le⟩
  have hy : x ∈ Icc (0 : ℝ) (min (α * x) K) :=
    ⟨hx.1.le, le_min (by nlinarith [H.α_gt, hx.1]) hx.2.le⟩
  have hd := h.hasDerivAt_V hx hy hfix
  have hfoc := h.foc hxI hx.1 hx.1 hx.2 hy hfix hd
  have e : x / x = 1 := div_self hx.1.ne'
  simp only [crsQ, e] at hfoc
  nlinarith

/-- **Exercise 6.9c: at most one stationary point.** -/
theorem stationary_unique {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ Ioo 0 K) (hx₂ : x₂ ∈ Ioo 0 K)
    (h₁ : crsF S φ θ δ x₁ x₁ + β * V x₁ = V x₁) (h₂ : crsF S φ θ δ x₂ x₂ + β * V x₂ = V x₂) :
    x₁ = x₂ := by
  have H := h.hyp
  have e₁ := h.stationary_eq hx₁ h₁
  have e₂ := h.stationary_eq hx₂ h₂
  have hφ1 : 0 < φ 1 := H.φ_pos ⟨zero_le_one, H.α_gt⟩
  have hκ : 0 < θ * (1 - β * (1 - δ)) := by
    have := H.θ_pos; have : 0 < 1 - β * (1 - δ) := by nlinarith [H.β_lt, H.δ_pos, H.β_pos]
    positivity
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := H.S'_lt (mul_nonneg hx₁.1.le hφ1.le) (mul_lt_mul_of_pos_right hlt hφ1)
    have hb : 0 < β * φ 1 + (1 - β) * φ' 1 := by
      by_contra hb; push Not at hb
      nlinarith [H.S'_pos (mul_nonneg hx₁.1.le hφ1.le)]
    nlinarith
  · have := H.S'_lt (mul_nonneg hx₂.1.le hφ1.le) (mul_lt_mul_of_pos_right hlt hφ1)
    have hb : 0 < β * φ 1 + (1 - β) * φ' 1 := by
      by_contra hb; push Not at hb
      nlinarith [H.S'_pos (mul_nonneg hx₂.1.le hφ1.le)]
    nlinarith

/-- **Exercise 6.9c (correction): no stationary point** when `βφ(1) + (1 − β)φ'(1) ≤ 0`. -/
theorem no_stationary (hb : β * φ 1 + (1 - β) * φ' 1 ≤ 0) {x : ℝ} (hx : x ∈ Ioo 0 K) :
    crsF S φ θ δ x x + β * V x ≠ V x := by
  have H := h.hyp
  intro hfix
  have e := h.stationary_eq hx hfix
  have hφ1 : 0 < φ 1 := H.φ_pos ⟨zero_le_one, H.α_gt⟩
  have hS := H.S'_pos (mul_nonneg hx.1.le hφ1.le)
  have hκ : 0 < θ * (1 - β * (1 - δ)) := by
    have := H.θ_pos; have : 0 < 1 - β * (1 - δ) := by nlinarith [H.β_lt, H.δ_pos, H.β_pos]
    positivity
  nlinarith

/-- **Exercise 6.9e** (from (b)–(d)). Let `g` be the policy, continuous, with an interior
stationary point `x̄` that is locally stable (orbits from a neighborhood converge to it, which is
what (d) and Theorem 6.9 provide). Then from every `x₀ ∈ (0, K)` capital converges
monotonically to `x̄`. -/
theorem ex_6_9e {g : ℝ → ℝ}
    (hg : ∀ x ∈ Icc (0 : ℝ) K, g x ∈ Icc (0 : ℝ) (min (α * x) K) ∧
      crsF S φ θ δ x (g x) + β * V (g x) = V x)
    (hgc : ContinuousOn g (Icc 0 K)) {xbar : ℝ} (hxbar : xbar ∈ Ioo 0 K) (hfix : g xbar = xbar)
    (hloc : ∃ ε > 0, ∀ x₀ ∈ Ioo (xbar - ε) (xbar + ε),
      Tendsto (fun t => g^[t] x₀) atTop (𝓝 xbar)) :
    ∀ x₀ ∈ Ioo 0 K, (Monotone (fun t => g^[t] x₀) ∨ Antitone (fun t => g^[t] x₀)) ∧
      Tendsto (fun t => g^[t] x₀) atTop (𝓝 xbar) := by
  obtain ⟨ε, hε, hloc⟩ := hloc
  have hmaps : MapsTo g (Icc 0 K) (Icc 0 K) := fun x hx =>
    ⟨(hg x hx).1.1, (hg x hx).1.2.trans (min_le_right _ _)⟩
  have hmono : MonotoneOn g (Icc 0 K) := fun x hx x' hx' hxx' =>
    h.argmax_mono hx hx' hxx' (hg x hx).1 (hg x hx).2 (hg x' hx').1 (hg x' hx').2
  -- the only interior fixed point is `x̄`
  have honly : ∀ z ∈ Ioo 0 K, g z = z → z = xbar := fun z hz hgz => by
    have h1 := (hg z ⟨hz.1.le, hz.2.le⟩).2
    rw [hgz] at h1
    have h2 := (hg xbar ⟨hxbar.1.le, hxbar.2.le⟩).2
    rw [hfix] at h2
    exact h.stationary_unique hz hxbar h1 h2
  have hφc : ContinuousOn (fun k => g k - k) (Icc 0 K) := hgc.sub continuousOn_id
  -- orbits stay in `[0, K]`
  have horb : ∀ x₀ ∈ Icc (0 : ℝ) K, ∀ t, g^[t] x₀ ∈ Icc (0 : ℝ) K := fun x₀ hx₀ t => by
    induction t with
    | zero => exact hx₀
    | succ t ih => rw [Function.iterate_succ_apply']; exact hmaps ih
  -- below `x̄`, `g(k) > k`
  have hbelow : ∀ k ∈ Ioo 0 xbar, k < g k := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k₁, hk₁, hk₁le⟩ := hcon
    have hk₁K : k₁ ∈ Ioo 0 K := ⟨hk₁.1, hk₁.2.trans hxbar.2⟩
    have hlt₁ : g k₁ < k₁ := lt_of_le_of_ne hk₁le fun he => absurd (honly k₁ hk₁K he) hk₁.2.ne
    -- then `g(k) < k` on all of `(0, x̄)`
    have hall : ∀ k ∈ Ioo 0 xbar, g k < k := fun k hk => by
      by_contra hge
      push Not at hge
      have hkK : k ∈ Ioo 0 K := ⟨hk.1, hk.2.trans hxbar.2⟩
      have hne : g k ≠ k := fun he => absurd (honly k hkK he) hk.2.ne
      have hgt : k < g k := lt_of_le_of_ne hge (Ne.symm hne)
      obtain ⟨z, hz, hz0⟩ : ∃ z ∈ Icc (min k k₁) (max k k₁), g z - z = 0 := by
        have hsub : Icc (min k k₁) (max k k₁) ⊆ Icc 0 K := Icc_subset_Icc
          (le_min hk.1.le hk₁.1.le) (max_le hkK.2.le hk₁K.2.le)
        rcases le_total k k₁ with hkk | hkk
        · rw [min_eq_left hkk, max_eq_right hkk] at hsub ⊢
          exact intermediate_value_Icc' hkk (hφc.mono hsub) ⟨by linarith, by linarith⟩
        · rw [min_eq_right hkk, max_eq_left hkk] at hsub ⊢
          exact intermediate_value_Icc hkk (hφc.mono hsub) ⟨by linarith, by linarith⟩
      have hz0' : 0 < z := lt_of_lt_of_le (lt_min hk.1 hk₁.1) hz.1
      have hzx : z < xbar := lt_of_le_of_lt hz.2 (max_lt hk.2 hk₁.2)
      exact absurd (honly z ⟨hz0', hzx.trans hxbar.2⟩ (by linarith)) hzx.ne
    -- an orbit starting just below `x̄` never comes back up
    set x₀ := max (xbar - ε / 2) (xbar / 2)
    have hx₀ : x₀ ∈ Ioo 0 xbar := ⟨lt_max_of_lt_right (by linarith [hxbar.1]),
      max_lt (by linarith) (by linarith [hxbar.1])⟩
    have hx₀ε : x₀ ∈ Ioo (xbar - ε) (xbar + ε) :=
      ⟨lt_max_of_lt_left (by linarith), by linarith [hx₀.2]⟩
    have hx₀I : x₀ ∈ Icc (0 : ℝ) K := ⟨hx₀.1.le, (hx₀.2.trans hxbar.2).le⟩
    have hle : ∀ t, g^[t] x₀ ≤ x₀ := fun t => by
      induction t with
      | zero => exact le_rfl
      | succ t ih =>
        rw [Function.iterate_succ_apply']
        exact (hmono (horb x₀ hx₀I t) hx₀I ih).trans (hall x₀ hx₀).le
    have := le_of_tendsto' (hloc x₀ hx₀ε) hle
    linarith [hx₀.2]
  -- above `x̄`, `g(k) < k`
  have habove : ∀ k ∈ Ioo xbar K, g k < k := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k₁, hk₁, hk₁le⟩ := hcon
    have hk₁K : k₁ ∈ Ioo 0 K := ⟨hxbar.1.trans hk₁.1, hk₁.2⟩
    have hlt₁ : k₁ < g k₁ := lt_of_le_of_ne hk₁le fun he =>
      absurd (honly k₁ hk₁K he.symm) hk₁.1.ne'
    have hall : ∀ k ∈ Ioo xbar K, k < g k := fun k hk => by
      by_contra hge
      push Not at hge
      have hkK : k ∈ Ioo 0 K := ⟨hxbar.1.trans hk.1, hk.2⟩
      have hne : g k ≠ k := fun he => absurd (honly k hkK he) hk.1.ne'
      have hlt : g k < k := lt_of_le_of_ne hge hne
      obtain ⟨z, hz, hz0⟩ : ∃ z ∈ Icc (min k k₁) (max k k₁), g z - z = 0 := by
        have hsub : Icc (min k k₁) (max k k₁) ⊆ Icc 0 K := Icc_subset_Icc
          (le_min hkK.1.le hk₁K.1.le) (max_le hkK.2.le hk₁K.2.le)
        rcases le_total k k₁ with hkk | hkk
        · rw [min_eq_left hkk, max_eq_right hkk] at hsub ⊢
          exact intermediate_value_Icc hkk (hφc.mono hsub) ⟨by linarith, by linarith⟩
        · rw [min_eq_right hkk, max_eq_left hkk] at hsub ⊢
          exact intermediate_value_Icc' hkk (hφc.mono hsub) ⟨by linarith, by linarith⟩
      have hzx : xbar < z := lt_of_lt_of_le (lt_min hk.1 hk₁.1) hz.1
      have hzK : z < K := lt_of_le_of_lt hz.2 (max_lt hk.2 hk₁.2)
      exact absurd (honly z ⟨hxbar.1.trans hzx, hzK⟩ (by linarith)) hzx.ne'
    set x₀ := min (xbar + ε / 2) ((xbar + K) / 2)
    have hx₀ : x₀ ∈ Ioo xbar K := ⟨lt_min (by linarith) (by linarith [hxbar.2]),
      min_lt_of_right_lt (by linarith [hxbar.2])⟩
    have hx₀ε : x₀ ∈ Ioo (xbar - ε) (xbar + ε) :=
      ⟨by linarith [hx₀.1], min_lt_of_left_lt (by linarith)⟩
    have hx₀I : x₀ ∈ Icc (0 : ℝ) K := ⟨(hxbar.1.trans hx₀.1).le, hx₀.2.le⟩
    have hge : ∀ t, x₀ ≤ g^[t] x₀ := fun t => by
      induction t with
      | zero => exact le_rfl
      | succ t ih =>
        rw [Function.iterate_succ_apply']
        exact (hall x₀ hx₀).le.trans (hmono hx₀I (horb x₀ hx₀I t) ih)
    have := ge_of_tendsto' (hloc x₀ hx₀ε) hge
    linarith [hx₀.1]
  -- monotone convergence on `[x₀, x̄]` or `[x̄, x₀]`
  intro x₀ hx₀
  rcases le_total x₀ xbar with hle | hle
  · refine orbit_tendsto_of_crossing (lo := x₀) (hi := xbar)
      (hgc.mono (Icc_subset_Icc hx₀.1.le hxbar.2.le))
      (hmono.mono (Icc_subset_Icc hx₀.1.le hxbar.2.le)) (fun k hk => ⟨?_, ?_⟩)
      ⟨hle, le_rfl⟩ hfix (fun k hk hkx => hbelow k ⟨hx₀.1.trans_le hk.1, hkx⟩)
      (fun k hk hkx => absurd hk.2 (not_le.2 hkx)) ⟨le_rfl, hle⟩
    · rcases eq_or_lt_of_le hk.2 with he | hlt
      · rw [he, hfix]; exact hle
      · exact hk.1.trans (hbelow k ⟨hx₀.1.trans_le hk.1, hlt⟩).le
    · rw [← hfix]
      exact hmono ⟨hx₀.1.le.trans hk.1, hk.2.trans hxbar.2.le⟩
        ⟨hxbar.1.le, hxbar.2.le⟩ hk.2
  · refine orbit_tendsto_of_crossing (lo := xbar) (hi := x₀)
      (hgc.mono (Icc_subset_Icc hxbar.1.le hx₀.2.le))
      (hmono.mono (Icc_subset_Icc hxbar.1.le hx₀.2.le)) (fun k hk => ⟨?_, ?_⟩)
      ⟨le_rfl, hle⟩ hfix (fun k hk hkx => absurd hk.1 (not_le.2 hkx))
      (fun k hk hkx => habove k ⟨hkx, hk.2.trans_lt hx₀.2⟩) ⟨hle, le_rfl⟩
    · rw [← hfix]
      exact hmono ⟨hxbar.1.le, hxbar.2.le⟩ ⟨hxbar.1.le.trans hk.1, hk.2.trans hx₀.2.le⟩ hk.1
    · rcases eq_or_lt_of_le hk.1 with he | hlt
      · rw [← he, hfix]; exact hle
      · exact (habove k ⟨hlt, hk.2.trans_lt hx₀.2⟩).le.trans hk.2

/-- **Exercise 6.9a: `V` is strictly concave**, although Assumption 4.7 fails on the ray
`y = αx` (where `F` is linear): optimal choices stay off that ray. -/
theorem strictConcaveOn : StrictConcaveOn ℝ (Icc 0 K) V := by
  have H := h.hyp
  refine ⟨convex_Icc 0 K, fun x hx x' hx' hne a b ha hb hab => ?_⟩
  obtain ⟨y, hy, hyv⟩ := h.arg x hx
  obtain ⟨y', hy', hyv'⟩ := h.arg x' hx'
  have hyx : y ≤ α * x := hy.2.trans (min_le_left _ _)
  have hyx' : y' ≤ α * x' := hy'.2.trans (min_le_left _ _)
  set z := a * x + b * x'
  set w := a * y + b * y'
  have hzI : z ∈ Icc (0 : ℝ) K := (convex_Icc 0 K) hx hx' ha.le hb.le hab
  have hw0 : 0 ≤ w := add_nonneg (mul_nonneg ha.le hy.1) (mul_nonneg hb.le hy'.1)
  have hwΓ : w ∈ Icc (0 : ℝ) (min (α * z) K) := by
    refine ⟨hw0, le_min ?_ ?_⟩
    · have h1 := mul_le_mul_of_nonneg_left hyx ha.le
      have h2 := mul_le_mul_of_nonneg_left hyx' hb.le
      simp only [w, z]; linarith [show α * (a * x + b * x') = a * (α * x) + b * (α * x') by ring]
    · have h1 := mul_le_mul_of_nonneg_left (hy.2.trans (min_le_right _ _)) ha.le
      have h2 := mul_le_mul_of_nonneg_left (hy'.2.trans (min_le_right _ _)) hb.le
      have : a * K + b * K = K := by rw [← add_mul, hab, one_mul]
      simp only [w]; linarith
  have hwI : w ∈ Icc (0 : ℝ) K := ⟨hwΓ.1, hwΓ.2.trans (min_le_right _ _)⟩
  -- output at the mixture beats the mixture of outputs, strictly after `S`
  have hq₁ := H.crsQ_nonneg hx.1 hy.1 hyx
  have hq₂ := H.crsQ_nonneg hx'.1 hy'.1 hyx'
  have hqc := H.crsQ_concave hx.1 hx'.1 hy.1 hyx hy'.1 hyx' ha.le hb.le hab
  have hmix : 0 ≤ a * crsQ φ x y + b * crsQ φ x' y' :=
    add_nonneg (mul_nonneg ha.le hq₁) (mul_nonneg hb.le hq₂)
  have hS : a * S (crsQ φ x y) + b * S (crsQ φ x' y') < S (crsQ φ z w) := by
    by_cases hqq : crsQ φ x y = crsQ φ x' y'
    · -- then both `x, x' > 0`, on different rays, and the mixture is strictly better
      have hpos : ∀ {x y : ℝ}, x ∈ Icc (0 : ℝ) K → y ∈ Icc (0 : ℝ) (min (α * x) K) →
          crsF S φ θ δ x y + β * V y = V x → 0 < x → 0 < crsQ φ x y := fun hx hy hyv hx0 =>
        mul_pos hx0 (H.φ_pos ⟨div_nonneg hy.1 hx0.le,
          (div_lt_iff₀ hx0).2 (by linarith [h.argmax_lt hx hx0 hy hyv])⟩)
      have hx0 : 0 < x := by
        rcases eq_or_lt_of_le hx.1 with he | hp
        · have hx'0 : 0 < x' := lt_of_le_of_ne hx'.1 (fun he' => hne (by rw [← he, ← he']))
          have := hpos hx' hy' hyv' hx'0
          have : crsQ φ x y = 0 := by simp only [crsQ, ← he, zero_mul]
          linarith
        · exact hp
      have hx'0 : 0 < x' := by
        rcases eq_or_lt_of_le hx'.1 with he | hp
        · have := hpos hx hy hyv hx0
          have : crsQ φ x' y' = 0 := by simp only [crsQ, ← he, zero_mul]
          linarith
        · exact hp
      have hrays : y / x ≠ y' / x' := fun hr => by
        have hφ : 0 < φ (y / x) := H.φ_pos ⟨div_nonneg hy.1 hx0.le,
          (div_lt_iff₀ hx0).2 (by linarith [h.argmax_lt hx hx0 hy hyv])⟩
        have : x * φ (y / x) = x' * φ (y / x) := by
          have h2 := hqq
          simp only [crsQ] at h2
          rw [← hr] at h2
          exact h2
        exact hne (mul_right_cancel₀ hφ.ne' this)
      have hst := H.crsQ_strict hx0 hx'0 hy.1 hyx hy'.1 hyx' ha hb hab hrays
      have hmono := H.S_mono (mem_Ici.2 hmix) (mem_Ici.2 (by linarith : 0 ≤ crsQ φ z w)) hst
      have e : a * crsQ φ x y + b * crsQ φ x' y' = crsQ φ x y := by
        rw [← hqq, ← add_mul, hab, one_mul]
      rw [e] at hmono
      rw [← hqq]
      linarith [show a * S (crsQ φ x y) + b * S (crsQ φ x y) = S (crsQ φ x y) by
        rw [← add_mul, hab, one_mul]]
    · have h1 := H.S_conc.2 (mem_Ici.2 hq₁) (mem_Ici.2 hq₂) hqq ha hb hab
      simp only [smul_eq_mul] at h1
      have h2 := H.S_mono.monotoneOn (mem_Ici.2 hmix)
        (mem_Ici.2 (by linarith : 0 ≤ crsQ φ z w)) hqc
      linarith
  have hV := h.conc.2 (show y ∈ Icc 0 K from ⟨hy.1, hy.2.trans (min_le_right _ _)⟩)
    (show y' ∈ Icc 0 K from ⟨hy'.1, hy'.2.trans (min_le_right _ _)⟩) ha.le hb.le hab
  simp only [smul_eq_mul] at hV ⊢
  have hle := h.le z hzI w hwΓ
  have hβV := mul_le_mul_of_nonneg_left hV H.β_pos.le
  simp only [crsF] at hle hyv hyv'
  have hlin : θ * (w - (1 - δ) * z) =
      a * (θ * (y - (1 - δ) * x)) + b * (θ * (y' - (1 - δ) * x')) := by
    simp only [w, z]; ring
  have e1 : a * V x = a * (S (crsQ φ x y) - θ * (y - (1 - δ) * x) + β * V y) := by rw [hyv]
  have e2 : b * V x' = b * (S (crsQ φ x' y') - θ * (y' - (1 - δ) * x') + β * V y') := by
    rw [hyv']
  nlinarith

end CRSValue

/-- **Exercise 6.9d.** At the stationary point, with `q = xφ(y/x)`: `q_x = φ(1) − φ'(1)`,
`q_y = φ'(1)`, `q_xx = q_yy = −q_xy = φ''(1)/x̄`, and `F_xx = S''q_x² + S'q_xx`,
`F_xy = S''q_xq_y + S'q_xy`, `F_yy = S''q_y² + S'q_yy`. If `S' > 0 > S''`, `φ(1) > 0 > φ'(1)`,
`φ''(1) ≤ 0` and `βφ(1) + (1 − β)φ'(1) > 0` (which (c) requires of a stationary point), then
`βF_xx + (1 + β)F_xy + F_yy = S''[βq_x + q_y][q_x + q_y] < 0` and `F_xy > 0`: the roots of the
linearized Euler equation are real, one in `(0, 1)` and one above `1`. -/
theorem ex_6_9d {S₁ S₂ φ₀ φ₁ φ₂ x β : ℝ} (hS₁ : 0 < S₁) (hS₂ : S₂ < 0) (hφ₀ : 0 < φ₀)
    (hφ₁ : φ₁ < 0) (hφ₂ : φ₂ ≤ 0) (hx : 0 < x) (hβ0 : 0 < β)
    (hb : 0 < β * φ₀ + (1 - β) * φ₁) :
    let Fxx := S₂ * (φ₀ - φ₁) ^ 2 + S₁ * (φ₂ / x)
    let Fxy := S₂ * ((φ₀ - φ₁) * φ₁) + S₁ * (-(φ₂ / x))
    let Fyy := S₂ * φ₁ ^ 2 + S₁ * (φ₂ / x)
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ < 1 ∧ 1 < μ₂ ∧
      quadRoot (-(Fyy + β * Fxx) / (β * Fxy)) (1 / β) μ₁ ∧
      quadRoot (-(Fyy + β * Fxx) / (β * Fxy)) (1 / β) μ₂ ∧
      ∀ μ, quadRoot (-(Fyy + β * Fxx) / (β * Fxy)) (1 / β) μ → μ = μ₁ ∨ μ = μ₂ := by
  intro Fxx Fxy Fyy
  have hxy : 0 < Fxy := by
    have h1 : 0 < S₂ * ((φ₀ - φ₁) * φ₁) := by
      have : (φ₀ - φ₁) * φ₁ < 0 := mul_neg_of_pos_of_neg (by linarith) hφ₁
      nlinarith
    have h2 : 0 ≤ S₁ * (-(φ₂ / x)) :=
      mul_nonneg hS₁.le (neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg hφ₂ hx.le))
    simp only [Fxy]; linarith
  refine roots_split (by positivity) ?_
  have hsum : β * Fxx + (1 + β) * Fxy + Fyy = S₂ * (β * φ₀ + (1 - β) * φ₁) * φ₀ := by
    simp only [Fxx, Fxy, Fyy]; ring
  have hneg : S₂ * (β * φ₀ + (1 - β) * φ₁) * φ₀ < 0 := by
    have := mul_pos hb hφ₀
    nlinarith
  have e : 1 - -(Fyy + β * Fxx) / (β * Fxy) + 1 / β =
      (β * Fxx + (1 + β) * Fxy + Fyy) / (β * Fxy) := by
    field_simp; ring
  rw [e, hsum]
  exact div_neg_of_neg_of_pos hneg (by positivity)

end StokeyLucasPrescott.DeterministicDynamics

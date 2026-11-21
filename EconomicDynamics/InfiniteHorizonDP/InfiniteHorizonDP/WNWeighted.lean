/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.WNSpace

/-!
# The Weighted Contraction Mapping Theorem (Theorem 7.3.6)

Miao §7.3.2, pp. 212–213. An operator `T` on `C_ϕ(S)` that is monotone (a), discounts in the
weighted sense `T(f + aϕ) ≤ Tf + θaϕ` for `a > 0` (b), and has `T0 ∈ C_ϕ(S)` (c) is a contraction
with modulus `θ` for `‖·‖_ϕ` and has a unique fixed point in `C_ϕ(S)`.

* `wn_le_add_of_disc`: the core estimate `Tf ≤ Tg + θ‖f − g‖_ϕ ϕ` of the proof. The book writes
  `f ≤ g + ‖f − g‖_ϕ ϕ` and applies (b) with `a = ‖f − g‖_ϕ`, but (b) is only assumed for
  `a > 0`; when `‖f − g‖_ϕ = 0` we use `f = g` instead.
* `theorem_7_3_6`: the theorem as stated, `T : C_ϕ(S) → C_ϕ(S)`. Then (c) is part of the
  hypothesis that `T` maps `C_ϕ(S)` into itself (`theorem_7_3_6_c`), so it is not listed.
* `wn_theorem_7_3_6_selfMap`, `wn_theorem_7_3_6_of_continuous`: what the book's proof actually
  shows from (c): (a)–(c) give `‖Tf‖_ϕ ≤ ‖T0‖_ϕ + θ‖f‖_ϕ < ∞`, but not continuity of `Tf`; so if `T`
  is only known to map `C_ϕ(S)` into continuous functions, (a)–(c) make it a self-map of
  `C_ϕ(S)`, and the conclusion follows. The bound uses both `Tf ≤ T0 + θ‖f‖_ϕϕ` (the book's line)
  and `T0 ≤ Tf + θ‖f‖_ϕϕ`, since `‖Tf‖_ϕ` bounds `|Tf|`.
-/

namespace Miao.InfiniteHorizonDP

variable {S : Type*} [TopologicalSpace S] {ϕ : S → ℝ}

/-- Miao, proof of Theorem 7.3.6, p. 213: from (a) and (b),
`Tf ≤ Tg + θ‖f − g‖_ϕ ϕ` for `f, g ∈ C_ϕ(S)`. -/
theorem wn_le_add_of_disc (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {T : (S → ℝ) → S → ℝ}
    (hmono : ∀ f g, wn_InC ϕ f → wn_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ}
    (hdisc : ∀ f, wn_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    {f g : S → ℝ} (hf : wn_InC ϕ f) (hg : wn_InC ϕ g) (s : S) :
    T f s ≤ T g s + θ * wn_norm ϕ (f - g) * ϕ s := by
  have hfg := wn_abs_le hϕ (wn_inC_sub hf hg)
  rcases (wn_norm_nonneg (ϕ := ϕ) (f - g)).eq_or_lt with h0 | hpos
  · have hle : f ≤ g := fun t => by
      have h1 := hfg t
      rw [← h0, zero_mul] at h1
      have h2 := le_abs_self ((f - g) t)
      simp only [Pi.sub_apply] at h1 h2
      linarith
    rw [← h0, mul_zero, zero_mul, add_zero]
    exact hmono f g hf hg hle s
  · set a := wn_norm ϕ (f - g)
    have hle : f ≤ g + a • ϕ := fun t => by
      have h1 := hfg t
      have h2 := le_abs_self ((f - g) t)
      simp only [Pi.sub_apply] at h1 h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    have h1 := hmono f (g + a • ϕ) hf (wn_inC_add hg (wn_inC_smul (wn_inC_self hϕc hϕ) a)) hle s
    have h2 := hdisc g hg a hpos s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
    linarith

/-- Miao, proof of Theorem 7.3.6, p. 213: (a) and (b) make `T` a contraction with modulus `θ`,
`‖Tf − Tg‖_ϕ ≤ θ‖f − g‖_ϕ` on `C_ϕ(S)`. -/
theorem wn_theorem_7_3_6_contraction (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hmono : ∀ f g, wn_InC ϕ f → wn_InC ϕ g → f ≤ g → T f ≤ T g)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hdisc : ∀ f, wn_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    {f g : S → ℝ} (hf : wn_InC ϕ f) (hg : wn_InC ϕ g) :
    wn_norm ϕ (T f - T g) ≤ θ * wn_norm ϕ (f - g) := by
  refine wn_norm_le hϕ (mul_nonneg hθ0.le (wn_norm_nonneg _)) fun s => ?_
  have h1 := wn_le_add_of_disc hϕc hϕ hmono hdisc hf hg s
  have h2 := wn_le_add_of_disc hϕc hϕ hmono hdisc hg hf s
  rw [wn_norm_sub_comm g f] at h2
  simp only [Pi.sub_apply]
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- **Theorem 7.3.6** (Weighted Contraction Mapping Theorem, Miao, p. 212). Let
`T : C_ϕ(S) → C_ϕ(S)` be (a) monotone and (b) discounting, `T(f + aϕ) ≤ Tf + θaϕ` for some
`θ ∈ (0, 1)` and all `a > 0`. Then `T` is a contraction with modulus `θ` and has a unique fixed
point in `C_ϕ(S)`. Condition (c), `T0 ∈ C_ϕ(S)`, is part of `T : C_ϕ(S) → C_ϕ(S)`
(`theorem_7_3_6_c`). -/
theorem theorem_7_3_6 (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {T : (S → ℝ) → S → ℝ}
    (hT : ∀ f, wn_InC ϕ f → wn_InC ϕ (T f))
    (hmono : ∀ f g, wn_InC ϕ f → wn_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
    (hdisc : ∀ f, wn_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ) :
    (∀ f g, wn_InC ϕ f → wn_InC ϕ g → wn_norm ϕ (T f - T g) ≤ θ * wn_norm ϕ (f - g)) ∧
      ∃! V, wn_InC ϕ V ∧ T V = V := by
  have hcon : ∀ f g, wn_InC ϕ f → wn_InC ϕ g →
      wn_norm ϕ (T f - T g) ≤ θ * wn_norm ϕ (f - g) := fun f g hf hg =>
    wn_theorem_7_3_6_contraction hϕc hϕ hmono hθ0 hdisc hf hg
  exact ⟨hcon, wn_exists_unique_fixedPoint hϕc hϕ hT hθ0.le hθ1 hcon⟩

/-- **Theorem 7.3.6 (c)** (Miao, p. 213). For `T : C_ϕ(S) → C_ϕ(S)`, (c) `T0 ∈ C_ϕ(S)` holds. -/
theorem theorem_7_3_6_c {T : (S → ℝ) → S → ℝ} (hT : ∀ f, wn_InC ϕ f → wn_InC ϕ (T f)) :
    wn_InC ϕ (T 0) :=
  hT 0 wn_inC_zero

/-- Miao, proof of Theorem 7.3.6, p. 213 ("Condition (c) ensures that `‖Tf‖_ϕ < ∞`"). If `T`
maps `C_ϕ(S)` into continuous functions and satisfies (a)–(c), then `T` maps `C_ϕ(S)` into
itself, with `‖Tf‖_ϕ ≤ ‖T0‖_ϕ + θ‖f‖_ϕ`. -/
theorem wn_theorem_7_3_6_selfMap (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hTc : ∀ f, wn_InC ϕ f → Continuous (T f))
    (hmono : ∀ f g, wn_InC ϕ f → wn_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ}
    (hdisc : ∀ f, wn_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    (h0 : wn_InC ϕ (T 0)) {f : S → ℝ} (hf : wn_InC ϕ f) :
    wn_InC ϕ (T f) ∧ ∀ s, |T f s| ≤ (wn_norm ϕ (T 0) + θ * wn_norm ϕ f) * ϕ s := by
  have hb : ∀ s, |T f s| ≤ (wn_norm ϕ (T 0) + θ * wn_norm ϕ f) * ϕ s := fun s => by
    have h1 := wn_le_add_of_disc hϕc hϕ hmono hdisc hf wn_inC_zero s
    have h2 := wn_le_add_of_disc hϕc hϕ hmono hdisc wn_inC_zero hf s
    have h3 := wn_abs_le hϕ h0 s
    rw [sub_zero] at h1
    rw [wn_norm_sub_comm, sub_zero] at h2
    rw [abs_le] at h3 ⊢
    constructor <;> nlinarith
  exact ⟨⟨hTc f hf, _, hb⟩, hb⟩

/-- **Theorem 7.3.6** in the form its proof establishes (Miao, pp. 212–213): if `T` maps
`C_ϕ(S)` into continuous functions and satisfies (a) monotonicity, (b) discounting with
`θ ∈ (0, 1)`, and (c) `T0 ∈ C_ϕ(S)`, then `T` maps `C_ϕ(S)` into itself, is a contraction with
modulus `θ`, and has a unique fixed point in `C_ϕ(S)`. -/
theorem wn_theorem_7_3_6_of_continuous (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hTc : ∀ f, wn_InC ϕ f → Continuous (T f))
    (hmono : ∀ f g, wn_InC ϕ f → wn_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
    (hdisc : ∀ f, wn_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    (h0 : wn_InC ϕ (T 0)) :
    (∀ f, wn_InC ϕ f → wn_InC ϕ (T f)) ∧
      (∀ f g, wn_InC ϕ f → wn_InC ϕ g → wn_norm ϕ (T f - T g) ≤ θ * wn_norm ϕ (f - g)) ∧
      ∃! V, wn_InC ϕ V ∧ T V = V := by
  have hT : ∀ f, wn_InC ϕ f → wn_InC ϕ (T f) := fun f hf =>
    (wn_theorem_7_3_6_selfMap hϕc hϕ hTc hmono hdisc h0 hf).1
  exact ⟨hT, theorem_7_3_6 hϕc hϕ hT hmono hθ0 hθ1 hdisc⟩

end Miao.InfiniteHorizonDP

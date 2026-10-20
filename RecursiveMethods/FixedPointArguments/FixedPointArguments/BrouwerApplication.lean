/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.Brouwer

/-!
# Applications of the Brouwer fixed-point theorem (SLP §17.3)

SLP §17.3, pp. 516–519, together with the parts of the overlapping-generations set-up of §17.1
(pp. 502–508) that Propositions 3 and 4 use. Brouwer's theorem itself is `theorem_17_3`
(`FixedPointArguments.Brouwer`).

**OLG primitives (§17.1).** `FPAssumption17_1` is **Assumption 17.1** (p. 503): `H : [0, L) → ℝ₊`
is `C²` (derivatives `H'`, `H''` taken within `[0, L)`, so one-sided at `0`), strictly increasing
and strictly convex with `H'(0) = 0` and `H'(l) → ∞` as `l → L`; `V : ℝ₊ → ℝ₊` is `C²`
(derivatives within `[0, ∞)`), strictly increasing and strictly concave. The names carry the
prefix `fp` to keep them apart from the §17.1 module.
* `fpZeta` `ζ(l) = l H'(l)` and `fpPhi` `φ(y) = y V'(y)` (p. 504); `fpZetaInv` is `ζ⁻¹`.
* `fpZeta_strictMonoOn`, `fpZeta_surjOn`, `fpZetaInv_strictMonoOn`, `fpZetaInv_continuousOn`
  (p. 507): `ζ` is a continuous increasing bijection `[0, L) → ℝ₊` and `ζ⁻¹ : ℝ₊ → [0, L)` is
  continuous and strictly increasing.
* `fp_bounds` (the bounds (7) of Proposition 2, used again in Propositions 3 and 4): for
  `X ⊆ [a, b] ⊂ ℝ₊₊` there are `0 < ε < B` with `0 ≤ φ(x′ζ⁻¹(y)) ≤ B` for all `y ≥ 0` and
  `ε < φ(x′ζ⁻¹(y))` for all `y ≥ ε`. The book takes `ε = ε_K = min {ε > 0 : ζ⁻¹(ε) = Kε}` with
  `K > 1/(aV′(bL))`; any `ε = ζ(l)` with `H′(l) < aV′(bL)` does the same job, which is what we use.

**§17.3.**
* `brouwer_finite_state` (p. 517): for a stochastic matrix `Π`, a nonempty closed bounded convex
  `D ⊆ ℝ` and `G(xᵢ, xⱼ, ·) : D → D` continuous, `(Tf)ᵢ = Σⱼ G(xᵢ, xⱼ, fⱼ) πᵢⱼ` has a fixed point
  in `Dᵐ`.
* `brouwer_log_transform_fixedPoint_iff`, `log_image_isCompact_convex`, `exp_image_log_image`
  (p. 518, "logarithms do not help"): for `D ⊆ ℝ₊₊`, `f` is a fixed point of `T` iff `ln f` is a
  fixed point of `T̂`, and `ln D` is compact and convex whenever `D` is (with `exp (ln D) = D`).
* `proposition_3` (**Proposition 3**, p. 518): with finitely many states `X ⊂ ℝ₊₊`, a stochastic
  matrix and Assumption 17.1, there is `f* ∈ ℝᵐ₊₊` with `f*ᵢ = Σⱼ φ[xⱼ ζ⁻¹(f*ⱼ)] πᵢⱼ`.
* `proposition_3_zero_fixedPoint` (p. 518 remark): `f ≡ 0` always solves the same system
  (`φ(0) = 0 = ζ⁻¹(0)`), which is why Proposition 3 must, and does, ask for a strictly positive
  solution.

No correction to the book is needed in §17.3: Proposition 3 is true as stated (the proof's
`F = [ε_K, B]ᵐ` excludes the trivial fixed point).
-/

namespace StokeyLucasPrescott.FixedPointArguments

open Set Filter Topology

/-! ### Assumption 17.1 and the functions `ζ`, `φ`, `ζ⁻¹` -/

/-- **Assumption 17.1** (p. 503). `H : [0, L) → ℝ₊` is twice continuously differentiable
(derivatives `H'`, `H''` within `[0, L)`), strictly increasing and strictly convex, with
`H'(0) = 0` and `H'(l) → +∞` as `l → L`; `V : ℝ₊ → ℝ₊` is twice continuously differentiable
(derivatives `V'`, `V''` within `[0, ∞)`), strictly increasing and strictly concave; and labour
lies in `[0, L)` with `0 < L < ∞`. -/
structure FPAssumption17_1 (L : ℝ) (H H' H'' V V' V'' : ℝ → ℝ) : Prop where
  L_pos : 0 < L
  H_nonneg : ∀ l ∈ Ico 0 L, 0 ≤ H l
  H_deriv : ∀ l ∈ Ico 0 L, HasDerivWithinAt H (H' l) (Ico 0 L) l
  H'_deriv : ∀ l ∈ Ico 0 L, HasDerivWithinAt H' (H'' l) (Ico 0 L) l
  H''_cont : ContinuousOn H'' (Ico 0 L)
  H_mono : StrictMonoOn H (Ico 0 L)
  H_conv : StrictConvexOn ℝ (Ico 0 L) H
  H'_zero : H' 0 = 0
  H'_tendsto : Tendsto H' (𝓝[<] L) atTop
  V_nonneg : ∀ y, 0 ≤ y → 0 ≤ V y
  V_deriv : ∀ y, 0 ≤ y → HasDerivWithinAt V (V' y) (Ici 0) y
  V'_deriv : ∀ y, 0 ≤ y → HasDerivWithinAt V' (V'' y) (Ici 0) y
  V''_cont : ContinuousOn V'' (Ici 0)
  V_mono : StrictMonoOn V (Ici 0)
  V_conc : StrictConcaveOn ℝ (Ici 0) V

/-- `ζ(l) = l H'(l)` (p. 504). -/
def fpZeta (H' : ℝ → ℝ) (l : ℝ) : ℝ := l * H' l

/-- `φ(y) = y V'(y)` (p. 504). -/
def fpPhi (V' : ℝ → ℝ) (y : ℝ) : ℝ := y * V' y

/-- `ζ⁻¹ : ℝ₊ → [0, L)`, the inverse of `ζ` on `[0, L)` (p. 507). -/
noncomputable def fpZetaInv (L : ℝ) (H' : ℝ → ℝ) (y : ℝ) : ℝ :=
  Function.invFunOn (fpZeta H') (Ico 0 L) y

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- `H'` is strictly increasing on `[0, L)` (strict convexity of `H`). -/
theorem fpA_H'_strictMonoOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    StrictMonoOn H' (Ico 0 L) := fun _ hx _ hy hxy =>
  (hA.H_conv.lt_slope_of_hasDerivWithinAt hx hy hxy (hA.H_deriv _ hx)).trans
    (hA.H_conv.slope_lt_of_hasDerivWithinAt hx hy hxy (hA.H_deriv _ hy))

/-- `H'(l) > 0` for `0 < l < L`. -/
theorem fpA_H'_pos (hA : FPAssumption17_1 L H H' H'' V V' V'') {l : ℝ} (hl : l ∈ Ioo 0 L) :
    0 < H' l := by
  have := fpA_H'_strictMonoOn hA (left_mem_Ico.2 hA.L_pos) (Ioo_subset_Ico_self hl) hl.1
  rwa [hA.H'_zero] at this

/-- `H' ≥ 0` on `[0, L)`. -/
theorem fpA_H'_nonneg (hA : FPAssumption17_1 L H H' H'' V V' V'') {l : ℝ} (hl : l ∈ Ico 0 L) :
    0 ≤ H' l := by
  rcases hl.1.eq_or_lt with h | h
  · rw [← h, hA.H'_zero]
  · exact (fpA_H'_pos hA ⟨h, hl.2⟩).le

/-- `H'` is continuous on `[0, L)`. -/
theorem fpA_H'_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    ContinuousOn H' (Ico 0 L) := fun l hl => (hA.H'_deriv l hl).continuousWithinAt

/-- `V'(y) > 0` for `y ≥ 0`. -/
theorem fpA_V'_pos (hA : FPAssumption17_1 L H H' H'' V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    0 < V' y := by
  have hy' : y ∈ Ici (0 : ℝ) := hy
  have hy1 : y + 1 ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have h1 := hA.V_conc.slope_lt_of_hasDerivWithinAt hy' hy1 (by linarith) (hA.V_deriv y hy)
  have h2 : 0 < slope V y (y + 1) := by
    rw [slope_def_field]
    exact div_pos (sub_pos.2 (hA.V_mono hy' hy1 (by linarith))) (by linarith)
  linarith

/-- `V'` is strictly decreasing on `[0, ∞)` (strict concavity of `V`). -/
theorem fpA_V'_strictAntiOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    StrictAntiOn V' (Ici 0) := fun _ hx _ hy hxy =>
  (hA.V_conc.slope_lt_of_hasDerivWithinAt hx hy hxy (hA.V_deriv _ hx)).trans'
    (hA.V_conc.lt_slope_of_hasDerivWithinAt hx hy hxy (hA.V_deriv _ hy))

/-- `V'` is continuous on `[0, ∞)`. -/
theorem fpA_V'_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    ContinuousOn V' (Ici 0) := fun y hy => (hA.V'_deriv y hy).continuousWithinAt

/-- `ζ(0) = 0`. -/
theorem fpZeta_zero : fpZeta H' 0 = 0 := by simp [fpZeta]

/-- `ζ ≥ 0` on `[0, L)`. -/
theorem fpZeta_nonneg (hA : FPAssumption17_1 L H H' H'' V V' V'') {l : ℝ} (hl : l ∈ Ico 0 L) :
    0 ≤ fpZeta H' l :=
  mul_nonneg hl.1 (fpA_H'_nonneg hA hl)

/-- `ζ` is strictly increasing on `[0, L)` (p. 505, step 1 of Proposition 1). -/
theorem fpZeta_strictMonoOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    StrictMonoOn (fpZeta H') (Ico 0 L) := by
  intro l₁ hl₁ l₂ hl₂ hlt
  have h1 : H' l₁ < H' l₂ := fpA_H'_strictMonoOn hA hl₁ hl₂ hlt
  have h2 : 0 < H' l₂ := fpA_H'_pos hA ⟨hl₁.1.trans_lt hlt, hl₂.2⟩
  have h3 : l₁ * H' l₁ ≤ l₁ * H' l₂ := mul_le_mul_of_nonneg_left h1.le hl₁.1
  have h4 : l₁ * H' l₂ < l₂ * H' l₂ := mul_lt_mul_of_pos_right hlt h2
  simp only [fpZeta]
  linarith

/-- `ζ` is continuous on `[0, L)`. -/
theorem fpZeta_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    ContinuousOn (fpZeta H') (Ico 0 L) :=
  continuousOn_id.mul (fpA_H'_continuousOn hA)

/-- `ζ` is unbounded on `[0, L)`: for every `y` some `l ∈ (0, L)` has `y < ζ(l)`. -/
theorem fpZeta_exists_gt (hA : FPAssumption17_1 L H H' H'' V V' V'') (y : ℝ) :
    ∃ l ∈ Ioo 0 L, y < fpZeta H' l := by
  have hL := hA.L_pos
  have h1 : ∀ᶠ l in 𝓝[<] L, 2 * |y| / L < H' l :=
    hA.H'_tendsto.eventually (eventually_gt_atTop _)
  have h2 : ∀ᶠ l in 𝓝[<] L, l ∈ Ioo (L / 2) L := Ioo_mem_nhdsLT (by linarith)
  obtain ⟨l, hl1, hl2⟩ := (h1.and h2).exists
  have hl0 : 0 < l := by linarith [hl2.1]
  refine ⟨l, ⟨hl0, hl2.2⟩, ?_⟩
  have hH : 0 < H' l := lt_of_le_of_lt (by positivity) hl1
  have e1 : L / 2 * H' l < l * H' l := mul_lt_mul_of_pos_right hl2.1 hH
  have e2 : L / 2 * (2 * |y| / L) ≤ L / 2 * H' l :=
    mul_le_mul_of_nonneg_left hl1.le (by linarith)
  have e3 : L / 2 * (2 * |y| / L) = |y| := by field_simp
  simp only [fpZeta]
  linarith [le_abs_self y]

/-- `ζ` maps `[0, L)` onto `ℝ₊` (p. 507). -/
theorem fpZeta_surjOn (hA : FPAssumption17_1 L H H' H'' V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    ∃ l ∈ Ico 0 L, fpZeta H' l = y := by
  obtain ⟨l₁, hl₁, hgt⟩ := fpZeta_exists_gt hA y
  have hsub : Icc 0 l₁ ⊆ Ico 0 L := fun z hz => ⟨hz.1, hz.2.trans_lt hl₁.2⟩
  have := intermediate_value_Icc hl₁.1.le ((fpZeta_continuousOn hA).mono hsub)
  obtain ⟨l, hl, hly⟩ := this ⟨by rw [fpZeta_zero]; exact hy, hgt.le⟩
  exact ⟨l, hsub hl, hly⟩

/-- `ζ⁻¹(y) ∈ [0, L)` for `y ≥ 0`. -/
theorem fpZetaInv_mem (hA : FPAssumption17_1 L H H' H'' V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    fpZetaInv L H' y ∈ Ico 0 L := by
  obtain ⟨l, hl, hly⟩ := fpZeta_surjOn hA hy
  exact Function.invFunOn_mem ⟨l, hl, hly⟩

/-- `ζ(ζ⁻¹(y)) = y` for `y ≥ 0`. -/
theorem fpZeta_zetaInv (hA : FPAssumption17_1 L H H' H'' V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    fpZeta H' (fpZetaInv L H' y) = y := by
  obtain ⟨l, hl, hly⟩ := fpZeta_surjOn hA hy
  exact Function.invFunOn_eq ⟨l, hl, hly⟩

/-- `ζ⁻¹(ζ(l)) = l` for `l ∈ [0, L)`. -/
theorem fpZetaInv_zeta (hA : FPAssumption17_1 L H H' H'' V V' V'') {l : ℝ} (hl : l ∈ Ico 0 L) :
    fpZetaInv L H' (fpZeta H' l) = l :=
  (fpZeta_strictMonoOn hA).injOn (fpZetaInv_mem hA (fpZeta_nonneg hA hl)) hl
    (fpZeta_zetaInv hA (fpZeta_nonneg hA hl))

/-- `ζ⁻¹(0) = 0`. -/
theorem fpZetaInv_zero (hA : FPAssumption17_1 L H H' H'' V V' V'') : fpZetaInv L H' 0 = 0 := by
  have := fpZetaInv_zeta hA (left_mem_Ico.2 hA.L_pos)
  rwa [fpZeta_zero] at this

/-- `ζ⁻¹` is strictly increasing on `ℝ₊` (p. 507). -/
theorem fpZetaInv_strictMonoOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    StrictMonoOn (fpZetaInv L H') (Ici 0) := by
  intro y₁ hy₁ y₂ hy₂ hlt
  by_contra hle
  have := (fpZeta_strictMonoOn hA).monotoneOn (fpZetaInv_mem hA hy₂) (fpZetaInv_mem hA hy₁)
    (not_lt.1 hle)
  rw [fpZeta_zetaInv hA hy₁, fpZeta_zetaInv hA hy₂] at this
  linarith

/-- `ζ⁻¹` is continuous on `ℝ₊` (p. 507): extended by the identity on `(−∞, 0)` it is monotone
on `ℝ` with image the open set `(−∞, L)`. -/
theorem fpZetaInv_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    ContinuousOn (fpZetaInv L H') (Ici 0) := by
  classical
  set ψ : ℝ → ℝ := fun y => if 0 ≤ y then fpZetaInv L H' y else y with hψ
  have hmono : MonotoneOn ψ univ := by
    intro y₁ _ y₂ _ hle
    simp only [hψ]
    by_cases h₁ : 0 ≤ y₁
    · have h₂ : 0 ≤ y₂ := h₁.trans hle
      simp only [h₁, h₂, ↓reduceIte]
      exact (fpZetaInv_strictMonoOn hA).monotoneOn h₁ h₂ hle
    · by_cases h₂ : 0 ≤ y₂
      · simp only [h₁, h₂, ↓reduceIte]
        exact (lt_of_not_ge h₁).le.trans (fpZetaInv_mem hA h₂).1
      · simp only [h₁, h₂, ↓reduceIte]
        exact hle
  have himg : ψ '' univ = Iio L := by
    ext z
    constructor
    · rintro ⟨y, -, rfl⟩
      simp only [hψ]
      by_cases h : 0 ≤ y
      · simp only [h, ↓reduceIte]
        exact (fpZetaInv_mem hA h).2
      · simp only [h, ↓reduceIte, mem_Iio]
        linarith [hA.L_pos, lt_of_not_ge h]
    · intro hz
      by_cases h : 0 ≤ z
      · refine ⟨fpZeta H' z, mem_univ _, ?_⟩
        have h0 : 0 ≤ fpZeta H' z := fpZeta_nonneg hA ⟨h, hz⟩
        simp only [hψ, h0, ↓reduceIte]
        exact fpZetaInv_zeta hA ⟨h, hz⟩
      · exact ⟨z, mem_univ _, by simp only [hψ, h, ↓reduceIte]⟩
  have hcont : Continuous ψ := continuous_iff_continuousAt.2 fun y => by
    refine continuousAt_of_monotoneOn_of_image_mem_nhds hmono univ_mem ?_
    have hy : ψ y ∈ ψ '' univ := ⟨y, mem_univ _, rfl⟩
    rw [himg] at hy ⊢
    exact Iio_mem_nhds hy
  refine hcont.continuousOn.congr fun y hy => ?_
  have hy' : (0 : ℝ) ≤ y := hy
  simp only [hψ, hy', ↓reduceIte]

/-- `φ` is continuous on `ℝ₊`. -/
theorem fpPhi_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') :
    ContinuousOn (fpPhi V') (Ici 0) :=
  continuousOn_id.mul (fpA_V'_continuousOn hA)

/-- `φ(0) = 0`. -/
theorem fpPhi_zero : fpPhi V' 0 = 0 := by simp [fpPhi]

/-- `φ ≥ 0` on `ℝ₊`. -/
theorem fpPhi_nonneg (hA : FPAssumption17_1 L H H' H'' V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ fpPhi V' y :=
  mul_nonneg hy (fpA_V'_pos hA hy).le

/-- `y ↦ φ(x′ ζ⁻¹(y))` is continuous on `ℝ₊` for `x′ ≥ 0`. -/
theorem fpPhi_comp_continuousOn (hA : FPAssumption17_1 L H H' H'' V V' V'') {x' : ℝ}
    (hx' : 0 ≤ x') : ContinuousOn (fun y => fpPhi V' (x' * fpZetaInv L H' y)) (Ici 0) :=
  (fpPhi_continuousOn hA).comp (continuousOn_const.mul (fpZetaInv_continuousOn hA))
    fun _ hy => mul_nonneg hx' (fpZetaInv_mem hA hy).1

/-- **The bounds of Propositions 2–4** ((7) on p. 514, (4)–(5) on p. 523). For states in
`[a, b] ⊂ ℝ₊₊` there are `0 < ε < B` with `0 ≤ φ(x′ζ⁻¹(y)) ≤ B` for all `y ≥ 0` and
`ε < φ(x′ζ⁻¹(y))` for all `y ≥ ε`. -/
theorem fp_bounds (hA : FPAssumption17_1 L H H' H'' V V' V'') {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ∃ ε > 0, ∃ B, ε < B ∧
      (∀ x' ∈ Icc a b, ∀ y, 0 ≤ y →
        0 ≤ fpPhi V' (x' * fpZetaInv L H' y) ∧ fpPhi V' (x' * fpZetaInv L H' y) ≤ B) ∧
      ∀ x' ∈ Icc a b, ∀ y, ε ≤ y → ε < fpPhi V' (x' * fpZetaInv L H' y) := by
  have hL := hA.L_pos
  have hb : 0 < b := ha.trans_le hab
  have hbL : 0 ≤ b * L := by positivity
  set c := a * V' (b * L) with hc
  have hc0 : 0 < c := mul_pos ha (fpA_V'_pos hA hbL)
  -- a small `l > 0` with `H'(l) < a V'(bL)`
  have hcw : ContinuousWithinAt H' (Ico 0 L) 0 :=
    fpA_H'_continuousOn hA 0 (left_mem_Ico.2 hL)
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Ico 0 L] 0 :=
    nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsGT hL) Ioo_subset_Ico_self)
  have hev : ∀ᶠ l in 𝓝[>] (0 : ℝ), H' l < c := by
    have := hcw.eventually (gt_mem_nhds (by rw [hA.H'_zero]; exact hc0))
    exact hle this
  obtain ⟨l, hl1, hl2⟩ := (hev.and (Ioo_mem_nhdsGT hL)).exists
  set ε := fpZeta H' l with hε
  have hε0 : 0 < ε := mul_pos hl2.1 (fpA_H'_pos hA hl2)
  -- the upper bound `B`
  obtain ⟨y₀, hy₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hbL)
    ((fpPhi_continuousOn hA).mono fun z hz => hz.1)
  set B := fpPhi V' y₀ with hB
  have hup : ∀ x' ∈ Icc a b, ∀ y, 0 ≤ y →
      0 ≤ fpPhi V' (x' * fpZetaInv L H' y) ∧ fpPhi V' (x' * fpZetaInv L H' y) ≤ B := by
    intro x' hx' y hy
    have hn := fpZetaInv_mem hA hy
    have hx'0 : 0 ≤ x' := ha.le.trans hx'.1
    have hmem : x' * fpZetaInv L H' y ∈ Icc 0 (b * L) :=
      ⟨mul_nonneg hx'0 hn.1, mul_le_mul hx'.2 hn.2.le hn.1 hb.le⟩
    exact ⟨fpPhi_nonneg hA hmem.1, hmax hmem⟩
  have hlow : ∀ x' ∈ Icc a b, ∀ y, ε ≤ y → ε < fpPhi V' (x' * fpZetaInv L H' y) := by
    intro x' hx' y hy
    have hy0 : 0 ≤ y := hε0.le.trans hy
    have hn := fpZetaInv_mem hA hy0
    have hnl : l ≤ fpZetaInv L H' y := by
      have := (fpZetaInv_strictMonoOn hA).monotoneOn (mem_Ici.2 hε0.le) (mem_Ici.2 hy0) hy
      rwa [hε, fpZetaInv_zeta hA (Ioo_subset_Ico_self hl2)] at this
    have hx'0 : 0 ≤ x' := ha.le.trans hx'.1
    set n := fpZetaInv L H' y
    have hxn : a * l ≤ x' * n := mul_le_mul hx'.1 hnl hl2.1.le hx'0
    have hxnb : x' * n ≤ b * L := mul_le_mul hx'.2 hn.2.le hn.1 hb.le
    have hV : V' (b * L) ≤ V' (x' * n) :=
      (fpA_V'_strictAntiOn hA).antitoneOn (mem_Ici.2 (mul_nonneg hx'0 hn.1)) (mem_Ici.2 hbL)
        hxnb
    have hVpos : 0 < V' (b * L) := fpA_V'_pos hA hbL
    have h1 : a * l * V' (b * L) ≤ x' * n * V' (x' * n) :=
      mul_le_mul hxn hV hVpos.le (mul_nonneg hx'0 hn.1)
    have h2 : l * H' l < l * c := mul_lt_mul_of_pos_left hl1 hl2.1
    have h3 : a * l * V' (b * L) = l * c := by rw [hc]; ring
    simp only [fpPhi, hε, fpZeta]
    linarith
  refine ⟨ε, hε0, B, ?_, hup, hlow⟩
  have h1 := hlow a ⟨le_rfl, hab⟩ ε le_rfl
  have h2 := (hup a ⟨le_rfl, hab⟩ ε hε0.le).2
  linarith

/-! ### Brouwer for finite-state functional equations (p. 517) -/

/-- **Finite-state application of Brouwer** (p. 517). Let `Π = [πᵢⱼ]` be an `m × m` stochastic
matrix, `D ⊆ ℝ` nonempty, closed, bounded and convex, and `G(xᵢ, xⱼ, ·) : D → D` continuous.
Then `(Tf)ᵢ = Σⱼ G(xᵢ, xⱼ, fⱼ) πᵢⱼ` has a fixed point in `F = Dᵐ`. -/
theorem brouwer_finite_state {m : ℕ} (π : Fin m → Fin m → ℝ) (hπ0 : ∀ i j, 0 ≤ π i j)
    (hπ1 : ∀ i, ∑ j, π i j = 1) {D : Set ℝ} (hDne : D.Nonempty) (hDcl : IsClosed D)
    (hDb : Bornology.IsBounded D) (hDc : Convex ℝ D) (G : Fin m → Fin m → ℝ → ℝ)
    (hG : ∀ i j, ContinuousOn (G i j) D) (hGD : ∀ i j y, y ∈ D → G i j y ∈ D) :
    ∃ f : Fin m → ℝ, (∀ i, f i ∈ D) ∧ ∀ i, f i = ∑ j, G i j (f j) * π i j := by
  set K : Set (Fin m → ℝ) := univ.pi fun _ => D with hK
  set T : (Fin m → ℝ) → Fin m → ℝ := fun f i => ∑ j, G i j (f j) * π i j with hT
  have hKc : IsCompact K :=
    isCompact_univ_pi fun _ => Metric.isCompact_of_isClosed_isBounded hDcl hDb
  have hKconv : Convex ℝ K := convex_pi fun _ _ => hDc
  have hKne : K.Nonempty := by
    obtain ⟨d, hd⟩ := hDne
    exact ⟨fun _ => d, fun _ _ => hd⟩
  have hTc : ContinuousOn T K := by
    refine continuousOn_pi.2 fun i => ?_
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact ((hG i j).comp (continuous_apply j).continuousOn
      fun f (hf : f ∈ K) => hf j (mem_univ j)).mul
      continuousOn_const
  have hTm : MapsTo T K K := by
    intro f hf i _
    have := hDc.sum_mem (t := Finset.univ) (w := fun j => π i j) (z := fun j => G i j (f j))
      (fun j _ => hπ0 i j) (hπ1 i) fun j _ => hGD i j _ (hf j (mem_univ j))
    simpa only [hT, smul_eq_mul, mul_comm] using this
  obtain ⟨f, hf, hTf⟩ := brouwer hKc hKconv hKne hTc hTm
  exact ⟨f, fun i => hf i (mem_univ i), fun i => (congrFun hTf i).symm⟩

/-- **Logarithms do not help with Brouwer** (p. 518), fixed points. For `D ⊆ ℝ₊₊` convex and
`G(xᵢ, xⱼ, ·) : D → D`, a vector `f ∈ Dᵐ` is a fixed point of `T` iff `g = ln f` is a fixed
point of `(T̂g)ᵢ = ln Σⱼ G(xᵢ, xⱼ, e^{gⱼ}) πᵢⱼ`. -/
theorem brouwer_log_transform_fixedPoint_iff {m : ℕ} (π : Fin m → Fin m → ℝ)
    (hπ0 : ∀ i j, 0 ≤ π i j) (hπ1 : ∀ i, ∑ j, π i j = 1) {D : Set ℝ} (hDpos : D ⊆ Ioi 0)
    (hDc : Convex ℝ D) (G : Fin m → Fin m → ℝ → ℝ) (hGD : ∀ i j y, y ∈ D → G i j y ∈ D)
    {f : Fin m → ℝ} (hf : ∀ j, f j ∈ D) :
    (∀ i, f i = ∑ j, G i j (f j) * π i j) ↔
      ∀ i, Real.log (f i) = Real.log (∑ j, G i j (Real.exp (Real.log (f j))) * π i j) := by
  have hexp : ∀ j, Real.exp (Real.log (f j)) = f j := fun j => Real.exp_log (hDpos (hf j))
  simp only [hexp]
  have hTpos : ∀ i, (0 : ℝ) < ∑ j, G i j (f j) * π i j := by
    intro i
    have := hDc.sum_mem (t := Finset.univ) (w := fun j => π i j) (z := fun j => G i j (f j))
      (fun j _ => hπ0 i j) (hπ1 i) fun j _ => hGD i j _ (hf j)
    have h2 : 0 < ∑ j, π i j • G i j (f j) := hDpos this
    simpa only [smul_eq_mul, mul_comm] using h2
  refine forall_congr' fun i => ⟨fun h => by rw [← h], fun h => ?_⟩
  exact Real.log_injOn_pos (hDpos (hf i)) (hTpos i) h

/-- **Logarithms do not help with Brouwer** (p. 518), sets. If `D ⊆ ℝ₊₊` is compact and convex,
so is `D̂ = ln D`. -/
theorem log_image_isCompact_convex {D : Set ℝ} (hDpos : D ⊆ Ioi 0) (hDk : IsCompact D)
    (hDc : Convex ℝ D) : IsCompact (Real.log '' D) ∧ Convex ℝ (Real.log '' D) := by
  have hlog : ContinuousOn Real.log D :=
    Real.continuousOn_log.mono fun y hy => (ne_of_gt (hDpos hy))
  refine ⟨hDk.image_of_continuousOn hlog, ?_⟩
  rw [convex_iff_ordConnected, ← isPreconnected_iff_ordConnected]
  exact (isPreconnected_iff_ordConnected.2 (convex_iff_ordConnected.1 hDc)).image _ hlog

/-- `exp` maps `ln D` back onto `D` for `D ⊆ ℝ₊₊`, so `F` and `F̂` determine each other. -/
theorem exp_image_log_image {D : Set ℝ} (hDpos : D ⊆ Ioi 0) :
    Real.exp '' (Real.log '' D) = D := by
  rw [image_image]
  conv_rhs => rw [← image_id D]
  exact image_congr fun y hy => Real.exp_log (hDpos hy)

/-! ### Proposition 3 -/

/-- Finitely many strictly positive states lie in some `[a, b] ⊂ ℝ₊₊`. -/
theorem fp_finite_states_bounds {m : ℕ} (x : Fin m → ℝ) (hx : ∀ i, 0 < x i) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ i, x i ∈ Icc a b := by
  classical
  set s : Finset ℝ := insert 1 (Finset.univ.image x) with hs
  have hne : s.Nonempty := Finset.insert_nonempty _ _
  have hmem : ∀ i, x i ∈ s := fun i =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem x (Finset.mem_univ i))
  refine ⟨s.min' hne, s.max' hne, ?_, Finset.min'_le _ _ (Finset.max'_mem _ _),
    fun i => ⟨Finset.min'_le _ _ (hmem i), Finset.le_max' _ _ (hmem i)⟩⟩
  have h := Finset.min'_mem s hne
  rcases Finset.mem_insert.1 h with h | h
  · rw [h]; exact one_pos
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
  rw [← hi]; exact hx i

/-- **Proposition 3** (p. 518). Let `X = {x₁, …, x_m} ⊂ ℝ₊₊`, `Π = [πᵢⱼ]` a stochastic matrix and
`H`, `V` satisfy Assumption 17.1. Then some strictly positive `f* ∈ ℝᵐ₊₊` satisfies
`f*ᵢ = Σⱼ φ[xⱼ ζ⁻¹(f*ⱼ)] πᵢⱼ` for all `i`. -/
theorem proposition_3 (hA : FPAssumption17_1 L H H' H'' V V' V'') {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (π : Fin m → Fin m → ℝ) (hπ0 : ∀ i j, 0 ≤ π i j)
    (hπ1 : ∀ i, ∑ j, π i j = 1) :
    ∃ f : Fin m → ℝ, (∀ i, 0 < f i) ∧
      ∀ i, f i = ∑ j, fpPhi V' (x j * fpZetaInv L H' (f j)) * π i j := by
  obtain ⟨a, b, ha, hab, hxab⟩ := fp_finite_states_bounds x hx
  obtain ⟨ε, hε, B, hεB, hup, hlow⟩ := fp_bounds hA ha hab
  have hGc : ∀ (_ : Fin m) (j : Fin m),
      ContinuousOn (fun y => fpPhi V' (x j * fpZetaInv L H' y)) (Icc ε B) :=
    fun _ j => (fpPhi_comp_continuousOn hA (hx j).le).mono fun y hy => hε.le.trans hy.1
  have hGD : ∀ (i j : Fin m) y, y ∈ Icc ε B → fpPhi V' (x j * fpZetaInv L H' y) ∈ Icc ε B :=
    fun _ j y hy => ⟨(hlow (x j) (hxab j) y hy.1).le, (hup (x j) (hxab j) y
      (hε.le.trans hy.1)).2⟩
  obtain ⟨f, hfD, hf⟩ := brouwer_finite_state π hπ0 hπ1 (nonempty_Icc.2 hεB.le) isClosed_Icc
    (Metric.isBounded_Icc ε B) (convex_Icc ε B)
    (fun (_ : Fin m) (j : Fin m) (y : ℝ) => fpPhi V' (x j * fpZetaInv L H' y))
    hGc hGD
  exact ⟨f, fun i => hε.trans_le (hfD i).1, hf⟩

/-- **The trivial solution** (p. 518 remark). Under Assumption 17.1 the zero vector solves the
system of Proposition 3, since `ζ⁻¹(0) = 0` and `φ(0) = 0`; Proposition 3 is about strictly
positive solutions. -/
theorem proposition_3_zero_fixedPoint (hA : FPAssumption17_1 L H H' H'' V V' V'') {m : ℕ}
    (x : Fin m → ℝ) (π : Fin m → Fin m → ℝ) (i : Fin m) :
    (0 : ℝ) = ∑ j, fpPhi V' (x j * fpZetaInv L H' 0) * π i j := by
  simp [fpZetaInv_zero hA, fpPhi_zero]

end StokeyLucasPrescott.FixedPointArguments

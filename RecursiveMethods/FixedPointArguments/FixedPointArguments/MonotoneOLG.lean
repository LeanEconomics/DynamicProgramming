/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.MonotoneKernel

/-!
# The OLG model by monotone iteration: Assumption 17.4 and Proposition 5

SLP §17.1 (pp. 502–507) and §17.5 (pp. 529–531).

* **Assumption 17.1** (p. 503): `MonoAssumption17_1H` (disutility of labour `H` on `[0, L)`),
  `MonoAssumption17_1V` (utility `V` on `ℝ₊`), bundled in `MonoAssumption17_1`. Derivatives are
  given explicitly (`H', H''`, `V', V''`), one-sided at `0`.
* `monoZeta` (`ζ(l) = l H'(l)`), `monoPhi` (`φ(y) = y V'(y)`) and `monoZetaInv` (`ζ⁻¹`, p. 507),
  with (all `MonoAssumption17_1H.*`): `ζ` continuous, strictly increasing from `[0, L)` onto `ℝ₊`
  (`surjOn_zeta`); `ζ⁻¹` continuous and increasing (`zetaInv_continuous`, `zetaInv_monotone`);
  `ζ⁻¹(y)/y → ∞` as `y ↓ 0` (`exists_lt_zetaInv`).
* `monoEpsK` (`ε_K = min{ε > 0 : ζ⁻¹(ε) = Kε}`, proof of Proposition 2, p. 514) with
  `MonoAssumption17_1H.epsK_spec`: the minimum exists, and `ζ⁻¹(y) > Ky` on `(0, ε_K)`.
  `monoB` (`B = max φ` on `[aζ⁻¹(ε_K), bL]`, proof of Proposition 4, p. 523).
* **Assumption 17.4** (`MonoAssumption17_4`, p. 530): `−yV″(y)/V′(y) ≤ 1` on `ℝ₊`; under
  Assumption 17.1 it makes `φ` nondecreasing (`MonoAssumption17_1V.monotoneOn_phi`).
* `monoOLGOp` : `C(X) → C(X)`, `(Tf)(x) = ∫ φ[x' ζ⁻¹(f(x'))] π(x, dx')` on `X = [a, b]`
  (§17.1 (9)), with `monoOLGOp_apply` (the formula, for every `f`, under Assumptions 17.1 and
  17.3).
* **Proposition 5** (`proposition_5`, p. 530): with `F = {f : ε_K ≤ f ≤ B}`, the iterates of `T`
  from `f₀ ≡ ε_K` and `g₀ ≡ B` converge in `C(X)` to fixed points `f ≤ g` in `F` that bracket
  every fixed point in `F`; if `f = g` it is the only fixed point of `T` in `F`.
* `monoOLGOp_zero` and `proposition_5_literal_false`: the zero function is always a fixed point,
  so the book's "this function is the unique fixed point of `T`" is false whenever `f = g`.
* `monoOLG_fixedPoint_mem` and `proposition_5_corrected`, `proposition_5_corrected'`: every
  fixed point with `inf h > 0` (equivalently, every strictly positive continuous fixed point)
  lies in `F`; so if `f = g`, `f` is the unique fixed point with `inf > 0`.

The concrete instance showing that `f = g` does occur (so the literal claim is genuinely false,
not vacuous) is in `FixedPointArguments.MonotoneOLGExamples`.

**Correction (Proposition 5, "at least one fixed point" / "the unique fixed point of T",
p. 530).** (i) `T` is not defined on all of `C(X)`, since `ζ⁻¹` is defined only on `ℝ₊`; here
`ζ⁻¹(y) := ζ⁻¹(max y 0)`, which leaves `T` unchanged on nonnegative functions. (ii) Since
`φ(0) = 0` and `ζ⁻¹(0) = 0`, `T0 = 0` (`monoOLGOp_zero`): "at least one fixed point" is trivial,
and when `f = g` the zero function is a second fixed point, so `f` is not "the unique fixed point
of `T`" (`proposition_5_literal_false`). The proof only gives uniqueness in `F`. Corrected
statement (`proposition_5_corrected`): if `f = g`, then `f` is the unique fixed point `h` of `T`
with `inf h > 0`. The proof: with `m = inf h`, `ζ⁻¹(y) > Ky` on `(0, ε_K)` and `φ ≥ KCε_K` above
`ε_K` give `m ≥ KC min(m, ε_K)`, and `KC > 1` forces `m ≥ ε_K`; then `h ≤ B`, so `h ∈ F`.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

/-! ### Assumption 17.1 -/

/-- **Assumption 17.1**, labour (SLP p. 503): `H : [0, L) → ℝ₊` is twice continuously
differentiable (one-sided at `0`), strictly increasing and strictly convex, with `H'(0) = 0` and
`H'(l) → +∞` as `l → L`; `0 < L < ∞`. -/
structure MonoAssumption17_1H (H H' H'' : ℝ → ℝ) (L : ℝ) : Prop where
  L_pos : 0 < L
  hasDeriv_H : ∀ l ∈ Ico 0 L, HasDerivWithinAt H (H' l) (Ici 0) l
  hasDeriv_H' : ∀ l ∈ Ico 0 L, HasDerivWithinAt H' (H'' l) (Ici 0) l
  continuousOn_H'' : ContinuousOn H'' (Ico 0 L)
  nonneg : ∀ l ∈ Ico 0 L, 0 ≤ H l
  strictMonoOn : StrictMonoOn H (Ico 0 L)
  strictConvexOn : StrictConvexOn ℝ (Ico 0 L) H
  deriv_zero : H' 0 = 0
  tendsto_deriv : Tendsto H' (𝓝[<] L) atTop

/-- **Assumption 17.1**, utility (SLP p. 503): `V : ℝ₊ → ℝ₊` is twice continuously
differentiable (one-sided at `0`), strictly increasing and strictly concave. -/
structure MonoAssumption17_1V (V V' V'' : ℝ → ℝ) : Prop where
  hasDeriv_V : ∀ y ∈ Ici (0 : ℝ), HasDerivWithinAt V (V' y) (Ici 0) y
  hasDeriv_V' : ∀ y ∈ Ici (0 : ℝ), HasDerivWithinAt V' (V'' y) (Ici 0) y
  continuousOn_V'' : ContinuousOn V'' (Ici 0)
  nonneg : ∀ y ∈ Ici (0 : ℝ), 0 ≤ V y
  strictMonoOn : StrictMonoOn V (Ici 0)
  strictConcaveOn : StrictConcaveOn ℝ (Ici 0) V

/-- **Assumption 17.1** (SLP p. 503), both halves. -/
structure MonoAssumption17_1 (H H' H'' V V' V'' : ℝ → ℝ) (L : ℝ) : Prop where
  hH : MonoAssumption17_1H H H' H'' L
  hV : MonoAssumption17_1V V V' V''

/-- `ζ(l) = l H'(l)` (SLP p. 504). -/
def monoZeta (H' : ℝ → ℝ) (l : ℝ) : ℝ := l * H' l

/-- `φ(y) = y V'(y)` (SLP p. 504). -/
def monoPhi (V' : ℝ → ℝ) (y : ℝ) : ℝ := y * V' y

/-- `ζ⁻¹ : ℝ₊ → [0, L)` (SLP p. 507), extended to `ℝ` by `ζ⁻¹(y) = ζ⁻¹(max y 0)`. -/
noncomputable def monoZetaInv (H' : ℝ → ℝ) (L y : ℝ) : ℝ :=
  Function.invFunOn (monoZeta H') (Ico 0 L) (max y 0)

/-- Relative risk aversion `−yV″(y)/V′(y)`. -/
noncomputable def monoRRA (V' V'' : ℝ → ℝ) (y : ℝ) : ℝ := -y * V'' y / V' y

/-- **Assumption 17.4** (SLP p. 530): `−yV″(y)/V′(y) ≤ 1` for all `y ∈ ℝ₊`. -/
def MonoAssumption17_4 (V' V'' : ℝ → ℝ) : Prop := ∀ y, 0 ≤ y → monoRRA V' V'' y ≤ 1

/-! ### Consequences of Assumption 17.1 for `H` and `ζ` -/

variable {H H' H'' : ℝ → ℝ} {L : ℝ}

/-- `H'` is continuous on `[0, L)`. -/
theorem MonoAssumption17_1H.continuousOn_H' (hA : MonoAssumption17_1H H H' H'' L) :
    ContinuousOn H' (Ico 0 L) := fun l hl =>
  ((hA.hasDeriv_H' l hl).continuousWithinAt).mono Ico_subset_Ici_self

/-- `H'` is strictly increasing on `[0, L)` (strict convexity). -/
theorem MonoAssumption17_1H.strictMonoOn_H' (hA : MonoAssumption17_1H H H' H'' L) :
    StrictMonoOn H' (Ico 0 L) := fun x hx y hy hxy =>
  (hA.strictConvexOn.lt_slope_of_hasDerivWithinAt hx hy hxy
    ((hA.hasDeriv_H x hx).mono Ico_subset_Ici_self)).trans
    (hA.strictConvexOn.slope_lt_of_hasDerivWithinAt hx hy hxy
      ((hA.hasDeriv_H y hy).mono Ico_subset_Ici_self))

/-- `H'(l) > 0` for `l ∈ (0, L)`. -/
theorem MonoAssumption17_1H.H'_pos (hA : MonoAssumption17_1H H H' H'' L) {l : ℝ}
    (hl : l ∈ Ioo 0 L) : 0 < H' l := by
  have h0 : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, hA.L_pos⟩
  have hl' : l ∈ Ico 0 L := Ioo_subset_Ico_self hl
  refine lt_trans ?_ (hA.strictConvexOn.slope_lt_of_hasDerivWithinAt h0 hl' hl.1
    ((hA.hasDeriv_H l hl').mono Ico_subset_Ici_self))
  rw [slope_def_field]
  exact div_pos (sub_pos.2 (hA.strictMonoOn h0 hl' hl.1)) (sub_pos.2 hl.1)

/-- `H' ≥ 0` on `[0, L)`. -/
theorem MonoAssumption17_1H.H'_nonneg (hA : MonoAssumption17_1H H H' H'' L) {l : ℝ}
    (hl : l ∈ Ico 0 L) : 0 ≤ H' l := by
  rcases hl.1.eq_or_lt with h | h
  · rw [← h, hA.deriv_zero]
  · exact (hA.H'_pos ⟨h, hl.2⟩).le

/-- `ζ(0) = 0`. -/
theorem monoZeta_zero : monoZeta H' 0 = 0 := by simp [monoZeta]

/-- `ζ` is continuous on `[0, L)`. -/
theorem MonoAssumption17_1H.continuousOn_zeta (hA : MonoAssumption17_1H H H' H'' L) :
    ContinuousOn (monoZeta H') (Ico 0 L) :=
  continuousOn_id.mul hA.continuousOn_H'

/-- `ζ` is strictly increasing on `[0, L)` (SLP p. 505, step 1). -/
theorem MonoAssumption17_1H.strictMonoOn_zeta (hA : MonoAssumption17_1H H H' H'' L) :
    StrictMonoOn (monoZeta H') (Ico 0 L) := fun x hx y hy hxy => by
  have hy0 : 0 < y := lt_of_le_of_lt hx.1 hxy
  calc monoZeta H' x = x * H' x := rfl
    _ ≤ x * H' y := mul_le_mul_of_nonneg_left (hA.strictMonoOn_H' hx hy hxy).le hx.1
    _ < y * H' y := mul_lt_mul_of_pos_right hxy (hA.H'_pos ⟨hy0, hy.2⟩)
    _ = monoZeta H' y := rfl

/-- `ζ ≥ 0` on `[0, L)`. -/
theorem MonoAssumption17_1H.zeta_nonneg (hA : MonoAssumption17_1H H H' H'' L) {l : ℝ}
    (hl : l ∈ Ico 0 L) : 0 ≤ monoZeta H' l :=
  mul_nonneg hl.1 (hA.H'_nonneg hl)

/-- `ζ` maps `[0, L)` onto `ℝ₊` (SLP p. 507). -/
theorem MonoAssumption17_1H.surjOn_zeta (hA : MonoAssumption17_1H H H' H'' L) :
    SurjOn (monoZeta H') (Ico 0 L) (Ici 0) := by
  intro y hy
  have ht : Tendsto (monoZeta H') (𝓝[<] L) atTop :=
    Tendsto.pos_mul_atTop hA.L_pos (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      hA.tendsto_deriv
  obtain ⟨l₁, hl₁, hl₁'⟩ :=
    ((ht.eventually (eventually_ge_atTop y)).and (Ioo_mem_nhdsLT hA.L_pos)).exists
  have hsub : Icc 0 l₁ ⊆ Ico 0 L := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hl₁'.2⟩
  obtain ⟨l, hl, hly⟩ := intermediate_value_Icc hl₁'.1.le (hA.continuousOn_zeta.mono hsub)
    ⟨by rw [monoZeta_zero]; exact hy, hl₁⟩
  exact ⟨l, hsub hl, hly⟩

/-! ### `ζ⁻¹` -/

/-- `ζ⁻¹(y) ∈ [0, L)` for every `y`. -/
theorem MonoAssumption17_1H.zetaInv_mem (hA : MonoAssumption17_1H H H' H'' L) (y : ℝ) :
    monoZetaInv H' L y ∈ Ico 0 L :=
  Function.invFunOn_mem (hA.surjOn_zeta (le_max_right y 0 : (0 : ℝ) ≤ max y 0))

/-- `ζ(ζ⁻¹(y)) = y` for `y ≥ 0`. -/
theorem MonoAssumption17_1H.zeta_zetaInv (hA : MonoAssumption17_1H H H' H'' L) {y : ℝ}
    (hy : 0 ≤ y) : monoZeta H' (monoZetaInv H' L y) = y := by
  have := Function.invFunOn_eq (hA.surjOn_zeta (le_max_right y 0 : (0 : ℝ) ≤ max y 0))
  rw [monoZetaInv, this, max_eq_left hy]

/-- `ζ⁻¹(ζ(l)) = l` for `l ∈ [0, L)`. -/
theorem MonoAssumption17_1H.zetaInv_zeta (hA : MonoAssumption17_1H H H' H'' L) {l : ℝ}
    (hl : l ∈ Ico 0 L) : monoZetaInv H' L (monoZeta H' l) = l :=
  hA.strictMonoOn_zeta.injOn (hA.zetaInv_mem _) hl (hA.zeta_zetaInv (hA.zeta_nonneg hl))

/-- `ζ⁻¹(y) = 0` for `y ≤ 0`; in particular `ζ⁻¹(0) = 0`. -/
theorem MonoAssumption17_1H.zetaInv_of_nonpos (hA : MonoAssumption17_1H H H' H'' L) {y : ℝ}
    (hy : y ≤ 0) : monoZetaInv H' L y = 0 := by
  have h0 : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, hA.L_pos⟩
  have := hA.zetaInv_zeta h0
  rw [monoZeta_zero] at this
  rw [← this, monoZetaInv, monoZetaInv, max_eq_right hy, max_self]

/-- `ζ⁻¹` is nondecreasing on `ℝ`. -/
theorem MonoAssumption17_1H.zetaInv_monotone (hA : MonoAssumption17_1H H H' H'' L) :
    Monotone (monoZetaInv H' L) := fun y₁ y₂ h => by
  have e : ∀ y, monoZetaInv H' L y = monoZetaInv H' L (max y 0) := fun y => by
    simp [monoZetaInv]
  rw [e y₁, e y₂, ← hA.strictMonoOn_zeta.le_iff_le (hA.zetaInv_mem _) (hA.zetaInv_mem _),
    hA.zeta_zetaInv (le_max_right _ _), hA.zeta_zetaInv (le_max_right _ _)]
  exact max_le_max h le_rfl

/-- `ζ⁻¹` is strictly increasing on `ℝ₊`. -/
theorem MonoAssumption17_1H.zetaInv_strictMonoOn (hA : MonoAssumption17_1H H H' H'' L) :
    StrictMonoOn (monoZetaInv H' L) (Ici 0) := fun y₁ h₁ y₂ h₂ h => by
  rw [← hA.strictMonoOn_zeta.lt_iff_lt (hA.zetaInv_mem _) (hA.zetaInv_mem _),
    hA.zeta_zetaInv h₁, hA.zeta_zetaInv h₂]
  exact h

/-- `ζ⁻¹` is continuous (SLP p. 507). -/
theorem MonoAssumption17_1H.zetaInv_continuous (hA : MonoAssumption17_1H H H' H'' L) :
    Continuous (monoZetaInv H' L) := by
  set g : ℝ → ℝ := fun y => if y < 0 then y else monoZetaInv H' L y with hg
  have hgm : Monotone g := fun y₁ y₂ h => by
    simp only [hg]
    split_ifs with h1 h2 h2
    · exact h
    · exact h1.le.trans (hA.zetaInv_mem _).1
    · exact absurd (lt_of_le_of_lt h h2) h1
    · exact hA.zetaInv_monotone h
  have hglt : ∀ y, g y < L := fun y => by
    simp only [hg]
    split_ifs with h1
    · exact h1.trans hA.L_pos
    · exact (hA.zetaInv_mem y).2
  have himg : Iio L ⊆ g '' univ := fun t ht => by
    rcases lt_or_ge t 0 with h | h
    · exact ⟨t, mem_univ _, by simp [hg, h]⟩
    · refine ⟨monoZeta H' t, mem_univ _, ?_⟩
      have hz := hA.zeta_nonneg ⟨h, ht⟩
      simp only [hg, not_lt.2 hz, ↓reduceIte]
      exact hA.zetaInv_zeta ⟨h, ht⟩
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun y =>
    continuousAt_of_monotoneOn_of_image_mem_nhds (hgm.monotoneOn univ) univ_mem
      (mem_of_superset (Iio_mem_nhds (hglt y)) himg)
  have e : monoZetaInv H' L = fun y => max (g y) 0 := by
    funext y
    simp only [hg]
    split_ifs with h
    · rw [hA.zetaInv_of_nonpos h.le, max_eq_right h.le]
    · rw [max_eq_left (hA.zetaInv_mem y).1]
  rw [e]
  exact hgc.max continuous_const

/-- `ζ⁻¹(y)/y → ∞` as `y ↓ 0`: for every `K > 0` there is `ε₀ > 0` with `Ky < ζ⁻¹(y)` on
`(0, ε₀]` (from `H'(0) = 0`; SLP p. 514, Figure 17.2). -/
theorem MonoAssumption17_1H.exists_lt_zetaInv (hA : MonoAssumption17_1H H H' H'' L) {K : ℝ}
    (hK : 0 < K) : ∃ ε₀ > 0, ∀ y ∈ Ioc 0 ε₀, K * y < monoZetaInv H' L y := by
  have h0 : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, hA.L_pos⟩
  have hc : Tendsto H' (𝓝[≥] 0) (𝓝 0) := by
    have := (hA.hasDeriv_H' 0 h0).continuousWithinAt.tendsto
    rwa [hA.deriv_zero] at this
  have h1 : ∀ᶠ l in 𝓝[≥] (0 : ℝ), H' l < 1 / K :=
    hc.eventually_lt_const (by positivity)
  obtain ⟨l₀, hl₀, hl₀'⟩ :=
    ((h1.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)).and
      (Ioo_mem_nhdsGT hA.L_pos)).exists
  have hl₀m : l₀ ∈ Ico 0 L := Ioo_subset_Ico_self hl₀'
  refine ⟨monoZeta H' l₀, mul_pos hl₀'.1 (hA.H'_pos hl₀'), fun y hy => ?_⟩
  set l := monoZetaInv H' L y with hl_def
  have hlm : l ∈ Ico 0 L := hA.zetaInv_mem y
  have hyl : monoZeta H' l = y := hA.zeta_zetaInv hy.1.le
  have hll₀ : l ≤ l₀ := by
    have := hA.zetaInv_monotone hy.2
    rwa [hA.zetaInv_zeta hl₀m] at this
  have hlpos : 0 < l := by
    rcases hlm.1.eq_or_lt with h | h
    · rw [← h, monoZeta_zero] at hyl; exact absurd hyl hy.1.ne
    · exact h
  have hH'l : H' l ≤ H' l₀ := (hA.strictMonoOn_H'.monotoneOn) hlm hl₀m hll₀
  have : y < l * (1 / K) := by
    rw [← hyl]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hH'l hlpos.le)
      (mul_lt_mul_of_pos_left hl₀ hlpos)
  rw [mul_one_div, lt_div_iff₀ hK] at this
  linarith

/-! ### `ε_K` and `B` -/

/-- `ε_K = min{ε > 0 : ζ⁻¹(ε) = Kε}` (SLP p. 514, proof of Proposition 2, used again in
Propositions 4 and 5). -/
noncomputable def monoEpsK (H' : ℝ → ℝ) (L K : ℝ) : ℝ :=
  sInf {ε | 0 < ε ∧ monoZetaInv H' L ε = K * ε}

/-- The minimum defining `ε_K` exists (SLP p. 514, "well defined"): `ε_K > 0`,
`ζ⁻¹(ε_K) = Kε_K`, and `ζ⁻¹(y) > Ky` for `y ∈ (0, ε_K)`. -/
theorem MonoAssumption17_1H.epsK_spec (hA : MonoAssumption17_1H H H' H'' L) {K : ℝ}
    (hK : 0 < K) :
    0 < monoEpsK H' L K ∧ monoZetaInv H' L (monoEpsK H' L K) = K * monoEpsK H' L K ∧
      ∀ y ∈ Ioo 0 (monoEpsK H' L K), K * y < monoZetaInv H' L y := by
  obtain ⟨ε₀, hε₀, hε₀'⟩ := hA.exists_lt_zetaInv hK
  set S := {ε | 0 < ε ∧ monoZetaInv H' L ε = K * ε} with hS
  set h : ℝ → ℝ := fun y => monoZetaInv H' L y - K * y with hh
  have hhc : Continuous h := hA.zetaInv_continuous.sub (continuous_const.mul continuous_id)
  have hpos0 : 0 < h ε₀ := by simp only [hh]; linarith [hε₀' ε₀ ⟨hε₀, le_rfl⟩]
  have hLK : 0 < L / K := div_pos hA.L_pos hK
  have hneg : h (L / K) < 0 := by
    simp only [hh, mul_div_cancel₀ _ hK.ne']
    linarith [(hA.zetaInv_mem (L / K)).2]
  have hle : ε₀ ≤ L / K := by
    refine le_of_not_gt fun hc => ?_
    have := hε₀' (L / K) ⟨hLK, hc.le⟩
    rw [mul_div_cancel₀ _ hK.ne'] at this
    linarith [(hA.zetaInv_mem (L / K)).2]
  have hSsub : S = Icc ε₀ (L / K) ∩ h ⁻¹' {0} := by
    ext ε
    simp only [hS, hh, mem_ofPred_eq, mem_inter_iff, mem_Icc, mem_preimage, mem_singleton_iff,
      sub_eq_zero]
    constructor
    · rintro ⟨hε, he⟩
      refine ⟨⟨?_, ?_⟩, he⟩
      · refine le_of_not_gt fun hc => ?_
        linarith [hε₀' ε ⟨hε, hc.le⟩]
      · have := (hA.zetaInv_mem ε).2
        rw [he] at this
        rw [le_div_iff₀ hK]
        linarith
    · rintro ⟨⟨h1, _⟩, he⟩
      exact ⟨lt_of_lt_of_le hε₀ h1, he⟩
  have hScpt : IsCompact S := by
    rw [hSsub]
    exact isCompact_Icc.inter_right (isClosed_singleton.preimage hhc)
  have hSne : S.Nonempty := by
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hle hhc.continuousOn ⟨hneg.le, hpos0.le⟩
    refine ⟨c, ?_⟩
    rw [hSsub]
    exact ⟨hc, hc0⟩
  have hmem : monoEpsK H' L K ∈ S := hScpt.sInf_mem hSne
  refine ⟨hmem.1, hmem.2, fun y hy => lt_of_not_ge fun hc => ?_⟩
  have hy0 : h y ≤ 0 := by simp only [hh]; linarith
  have hyε : ε₀ < y := by
    refine lt_of_not_ge fun hc' => ?_
    linarith [hε₀' y ⟨hy.1, hc'⟩]
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hyε.le hhc.continuousOn ⟨hy0, hpos0.le⟩
  have hcS : c ∈ S := ⟨lt_of_lt_of_le hε₀ hc.1, by
    have : h c = 0 := hc0
    simp only [hh, sub_eq_zero] at this
    exact this⟩
  have : monoEpsK H' L K ≤ c := csInf_le ⟨0, fun ε hε => hε.1.le⟩ hcS
  linarith [hc.2, hy.2]

/-! ### Consequences of Assumption 17.1 for `V` and `φ`; Assumption 17.4 -/

variable {V V' V'' : ℝ → ℝ}

/-- `V'` is continuous on `ℝ₊`. -/
theorem MonoAssumption17_1V.continuousOn_V' (hV : MonoAssumption17_1V V V' V'') :
    ContinuousOn V' (Ici 0) := fun y hy => (hV.hasDeriv_V' y hy).continuousWithinAt

/-- `V'(y) > 0` for `y ≥ 0` (SLP p. 503, derived consequence of Assumption 17.1). -/
theorem MonoAssumption17_1V.V'_pos (hV : MonoAssumption17_1V V V' V'') {y : ℝ} (hy : 0 ≤ y) :
    0 < V' y := by
  have hy' : y ∈ Ici (0 : ℝ) := hy
  have hy1 : y + 1 ∈ Ici (0 : ℝ) := by rw [mem_Ici]; linarith
  refine lt_trans ?_ (hV.strictConcaveOn.slope_lt_of_hasDerivWithinAt hy' hy1 (lt_add_one y)
    (hV.hasDeriv_V y hy'))
  rw [slope_def_field]
  exact div_pos (sub_pos.2 (hV.strictMonoOn hy' hy1 (lt_add_one y))) (by linarith)

/-- `V'` is strictly decreasing on `ℝ₊` (strict concavity). -/
theorem MonoAssumption17_1V.strictAntiOn_V' (hV : MonoAssumption17_1V V V' V'') :
    StrictAntiOn V' (Ici 0) := fun x hx y hy hxy =>
  (hV.strictConcaveOn.lt_slope_of_hasDerivWithinAt hx hy hxy (hV.hasDeriv_V y hy)).trans
    (hV.strictConcaveOn.slope_lt_of_hasDerivWithinAt hx hy hxy (hV.hasDeriv_V x hx))

/-- `φ(0) = 0`. -/
theorem monoPhi_zero : monoPhi V' 0 = 0 := by simp [monoPhi]

/-- `φ` is continuous on `ℝ₊`. -/
theorem MonoAssumption17_1V.continuousOn_phi (hV : MonoAssumption17_1V V V' V'') :
    ContinuousOn (monoPhi V') (Ici 0) :=
  continuousOn_id.mul hV.continuousOn_V'

/-- Under Assumption 17.1, Assumption 17.4 makes `φ(y) = yV'(y)` nondecreasing on `ℝ₊`
(SLP p. 530: `φ'(y) = V'(y)[1 − (−yV''(y)/V'(y))] ≥ 0`). -/
theorem MonoAssumption17_1V.monotoneOn_phi (hV : MonoAssumption17_1V V V' V'')
    (h4 : MonoAssumption17_4 V' V'') : MonotoneOn (monoPhi V') (Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => V' y + y * V'' y) (convex_Ici 0)
    hV.continuousOn_phi (fun y hy => ?_) (fun y hy => ?_)
  · rw [interior_Ici] at hy
    have hd : HasDerivAt V' (V'' y) y :=
      (hV.hasDeriv_V' y (mem_Ici.2 (le_of_lt hy))).hasDerivAt (Ici_mem_nhds hy)
    have : HasDerivAt (monoPhi V') (V' y + y * V'' y) y := by
      have h' := (hasDerivAt_id' y).mul hd
      rw [one_mul] at h'
      exact h'
    exact this.hasDerivWithinAt
  · rw [interior_Ici] at hy
    have hpos := hV.V'_pos hy.le
    have := h4 y hy.le
    simp only [monoRRA] at this
    rw [div_le_iff₀ hpos] at this
    linarith

/-! ### The operator `T` of (9) on `X = [a, b]` -/

variable {a b : ℝ}

/-- The kernel `G[x, x', y] = φ[x' ζ⁻¹(y)]` of the OLG operator (SLP §17.1 (9)). -/
noncomputable def monoOLGKernel (H' V' : ℝ → ℝ) (L a b : ℝ) : Icc a b → Icc a b → ℝ → ℝ :=
  fun _ x' y => monoPhi V' (x'.1 * monoZetaInv H' L y)

/-- The OLG operator `(Tf)(x) = ∫ φ[x' ζ⁻¹(f(x'))] π(x, dx')` (SLP §17.1 (9) and §17.5,
Proposition 5) as a map `C(X) → C(X)` on `X = [a, b]`. -/
noncomputable def monoOLGOp (π : Kernel (Icc a b) (Icc a b)) (H' V' : ℝ → ℝ) (L : ℝ) :
    (Icc a b →ᵇ ℝ) → (Icc a b →ᵇ ℝ) :=
  kernelOp π (monoOLGKernel H' V' L a b)

/-- `B = max{φ(y) : y ∈ [aζ⁻¹(ε_K), bL]}` (SLP p. 523, proof of Proposition 4). -/
noncomputable def monoB (a b : ℝ) (H' V' : ℝ → ℝ) (L K : ℝ) : ℝ :=
  sSup (monoPhi V' '' Icc (a * monoZetaInv H' L (monoEpsK H' L K)) (b * L))

/-- The set `F = {f ∈ C(X) : ε_K ≤ f ≤ B}` of Propositions 4 and 5. -/
def monoF (a b : ℝ) (H' V' : ℝ → ℝ) (L K : ℝ) : Set (Icc a b →ᵇ ℝ) :=
  {f | ∀ x, f x ∈ Icc (monoEpsK H' L K) (monoB a b H' V' L K)}

/-- The argument `x' ζ⁻¹(y)` of `φ` lies in `[0, bL]`. -/
theorem MonoAssumption17_1H.arg_mem (hA : MonoAssumption17_1H H H' H'' L) (ha : 0 < a)
    (x' : Icc a b) (y : ℝ) : x'.1 * monoZetaInv H' L y ∈ Icc 0 (b * L) :=
  ⟨mul_nonneg (ha.le.trans x'.2.1) (hA.zetaInv_mem y).1,
    mul_le_mul x'.2.2 (hA.zetaInv_mem y).2.le (hA.zetaInv_mem y).1
      ((ha.le.trans x'.2.1).trans x'.2.2)⟩

/-- `φ` is bounded on `[0, bL]`. -/
theorem MonoAssumption17_1V.exists_bound_phi (hV : MonoAssumption17_1V V V' V'') (c : ℝ) :
    ∃ M, ∀ t ∈ Icc 0 c, |monoPhi V' t| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hV.continuousOn_phi.mono Icc_subset_Ici_self)
  exact ⟨M, fun t ht => by rw [← Real.norm_eq_abs]; exact hM t ht⟩

/-- The integrand `x' ↦ φ[x' ζ⁻¹(f(x'))]` is continuous for every `f ∈ C(X)`. -/
theorem monoOLG_integrand_continuous (hA : MonoAssumption17_1 H H' H'' V V' V'' L)
    (ha : 0 < a) (f : Icc a b →ᵇ ℝ) :
    Continuous fun x' : Icc a b => monoPhi V' (x'.1 * monoZetaInv H' L (f x')) :=
  hA.hV.continuousOn_phi.comp_continuous
    (continuous_subtype_val.mul (hA.hH.zetaInv_continuous.comp f.continuous))
    fun x' => (hA.hH.arg_mem ha x' (f x')).1

/-- Under Assumptions 17.1 and 17.3, `T` is given by its formula on all of `C(X)`. -/
theorem monoOLGOp_apply (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π] (hπ : MonoAssumption17_3 π)
    (f : Icc a b →ᵇ ℝ) (x : Icc a b) :
    monoOLGOp π H' V' L f x = ∫ x', monoPhi V' (x'.1 * monoZetaInv H' L (f x')) ∂(π x) := by
  obtain ⟨M, hM⟩ := hA.hV.exists_bound_phi (b * L)
  have hb : ∀ x', |monoPhi V' (x'.1 * monoZetaInv H' L (f x'))| ≤ M :=
    fun x' => hM _ (hA.hH.arg_mem ha x' (f x'))
  refine kernelOp_apply_of_continuous (G := monoOLGKernel H' V' L a b)
    (continuous_integral_of_assumption17_3 hπ (monoOLG_integrand_continuous hA ha f).measurable
      hb) (B := M) (fun x => ?_) x
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := M) (Eventually.of_forall fun x' => ?_)).trans
    (by simp)
  rw [Real.norm_eq_abs]
  exact hb x'

/-- **The zero function is a fixed point of `T`** (NOTE to Proposition 5, p. 530):
`φ(0) = 0` and `ζ⁻¹(0) = 0`. -/
theorem monoOLGOp_zero (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π] (hπ : MonoAssumption17_3 π) :
    monoOLGOp π H' V' L 0 = 0 := by
  ext x
  rw [monoOLGOp_apply hA ha hπ]
  simp [hA.hH.zetaInv_of_nonpos le_rfl, monoPhi]

/-- The bounds (4)–(5) of the proof of Proposition 4 (SLP p. 523): for `x' ∈ [a, b]` and
`y ≥ ε_K`, `x' ζ⁻¹(y) ∈ [aζ⁻¹(ε_K), bL]`, `φ[x'ζ⁻¹(y)] ≥ KCε_K` with `C = aV'(bL)`, and
`φ[x'ζ⁻¹(y)] ≤ B`. -/
theorem monoOLG_bounds (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    {K : ℝ} (hK : 0 < K) {t y : ℝ} (ht : t ∈ Icc a b) (hy : monoEpsK H' L K ≤ y) :
    t * monoZetaInv H' L y ∈ Icc (a * monoZetaInv H' L (monoEpsK H' L K)) (b * L) ∧
      K * (a * V' (b * L)) * monoEpsK H' L K ≤ monoPhi V' (t * monoZetaInv H' L y) ∧
      monoPhi V' (t * monoZetaInv H' L y) ≤ monoB a b H' V' L K := by
  obtain ⟨hε, hεK, -⟩ := hA.hH.epsK_spec hK
  have hmono := hA.hH.zetaInv_monotone hy
  have hmemy := hA.hH.zetaInv_mem y
  have hmemε := hA.hH.zetaInv_mem (monoEpsK H' L K)
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  have hlow : a * monoZetaInv H' L (monoEpsK H' L K) ≤ t * monoZetaInv H' L y :=
    mul_le_mul ht.1 hmono hmemε.1 ht0.le
  have hup : t * monoZetaInv H' L y ≤ b * L :=
    mul_le_mul ht.2 hmemy.2.le hmemy.1 (ht0.le.trans ht.2)
  have hs0 : 0 ≤ t * monoZetaInv H' L y := mul_nonneg ht0.le hmemy.1
  refine ⟨⟨hlow, hup⟩, ?_, ?_⟩
  · have hbL : (0 : ℝ) ≤ b * L := hs0.trans hup
    have hV'le : V' (b * L) ≤ V' (t * monoZetaInv H' L y) :=
      hA.hV.strictAntiOn_V'.antitoneOn hs0 hbL hup
    have hVpos := hA.hV.V'_pos hbL
    calc K * (a * V' (b * L)) * monoEpsK H' L K
        = (a * monoZetaInv H' L (monoEpsK H' L K)) * V' (b * L) := by rw [hεK]; ring
      _ ≤ (t * monoZetaInv H' L y) * V' (b * L) := mul_le_mul_of_nonneg_right hlow hVpos.le
      _ ≤ (t * monoZetaInv H' L y) * V' (t * monoZetaInv H' L y) :=
          mul_le_mul_of_nonneg_left hV'le hs0
      _ = monoPhi V' (t * monoZetaInv H' L y) := rfl
  · have hbdd : BddAbove (monoPhi V' '' Icc (a * monoZetaInv H' L (monoEpsK H' L K)) (b * L)) :=
      (isCompact_Icc.image_of_continuousOn (hA.hV.continuousOn_phi.mono fun s hs =>
        (mul_nonneg ha.le hmemε.1).trans hs.1)).bddAbove
    exact le_csSup hbdd ⟨_, ⟨hlow, hup⟩, rfl⟩

/-- `K > 0` follows from `KC > 1`, `C = aV'(bL)`. -/
theorem monoOLG_K_pos (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    (hab : a ≤ b) {K : ℝ} (hK : 1 < K * (a * V' (b * L))) : 0 < K := by
  have hC : 0 < a * V' (b * L) :=
    mul_pos ha (hA.hV.V'_pos (mul_nonneg (ha.le.trans hab) hA.hH.L_pos.le))
  by_contra h
  have : K * (a * V' (b * L)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) hC.le
  linarith

/-- **Proposition 5** (SLP p. 530). Let `X = [a, b] ⊂ ℝ₊₊`, `π` satisfy Assumption 17.3, and
`H, V` satisfy Assumptions 17.1 and 17.4. Let `K C > 1` with `C = aV'(bL)`, `ε_K`, `B` as in
Proposition 4, and `F = {f ∈ C(X) : ε_K ≤ f ≤ B}`. Then `F` is closed and bounded, `T` maps `F`
into itself and is continuous and monotone there, and `T(F)` is equicontinuous. The iterates
`Tⁿf₀`, `f₀ ≡ ε_K`, and `Tⁿg₀`, `g₀ ≡ B`, converge in `C(X)` to fixed points `f ≤ g` in `F`
(so `T` has a fixed point), every fixed point `h ∈ F` satisfies `f ≤ h ≤ g`, and if `f = g` it
is the unique fixed point of `T` **in `F`** (see `proposition_5_literal_false` for why "in `F`"
cannot be dropped, and `proposition_5_corrected` for the correct global statement). -/
theorem proposition_5 (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a) (hab : a ≤ b)
    {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π] (hπ : MonoAssumption17_3 π)
    (h4 : MonoAssumption17_4 V' V'') {K : ℝ} (hK : 1 < K * (a * V' (b * L))) :
    0 < monoEpsK H' L K ∧ monoEpsK H' L K ≤ monoB a b H' V' L K ∧
      IsClosed (monoF a b H' V' L K) ∧ Bornology.IsBounded (monoF a b H' V' L K) ∧
      MapsTo (monoOLGOp π H' V' L) (monoF a b H' V' L K) (monoF a b H' V' L K) ∧
      ContinuousOn (monoOLGOp π H' V' L) (monoF a b H' V' L K) ∧
      MonotoneOn (monoOLGOp π H' V' L) (monoF a b H' V' L K) ∧
      UniformEquicontinuous (fun f : monoF a b H' V' L K => ⇑(monoOLGOp π H' V' L f)) ∧
      ∃ f ∈ monoF a b H' V' L K, ∃ g ∈ monoF a b H' V' L K,
        monoOLGOp π H' V' L f = f ∧ monoOLGOp π H' V' L g = g ∧
        Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoEpsK H' L K))) atTop
          (𝓝 f) ∧
        Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoB a b H' V' L K))) atTop
          (𝓝 g) ∧
        (∀ h ∈ monoF a b H' V' L K, monoOLGOp π H' V' L h = h → f ≤ h ∧ h ≤ g) ∧
        (f = g → ∀ h ∈ monoF a b H' V' L K, monoOLGOp π H' V' L h = h → h = f) := by
  have hK0 := monoOLG_K_pos hA ha hab hK
  obtain ⟨hε, -, -⟩ := hA.hH.epsK_spec hK0
  set ε := monoEpsK H' L K with hε_def
  set B := monoB a b H' V' L K with hB_def
  have hεKC : ε ≤ K * (a * V' (b * L)) * ε := by nlinarith
  have hb := fun {t y : ℝ} (ht : t ∈ Icc a b) (hy : ε ≤ y) => monoOLG_bounds hA ha hK0 ht hy
  have hεB : ε ≤ B := hεKC.trans ((hb ⟨le_rfl, hab⟩ le_rfl).2.1.trans (hb ⟨le_rfl, hab⟩ le_rfl).2.2)
  have hX : TotallyBounded (univ : Set (Icc a b)) := isCompact_univ.totallyBounded
  set Φ : ℝ × ℝ → ℝ := fun q => monoPhi V' (q.1 * monoZetaInv H' L q.2) with hΦ
  have hΦc : ContinuousOn Φ (Icc a b ×ˢ Icc ε B) :=
    hA.hV.continuousOn_phi.comp (continuous_fst.mul
      (hA.hH.zetaInv_continuous.comp continuous_snd)).continuousOn fun q hq =>
        mul_nonneg (ha.le.trans hq.1.1) (hA.hH.zetaInv_mem _).1
  have hGc : ContinuousOn (fun p : Icc a b × Icc a b × ℝ =>
      monoOLGKernel H' V' L a b p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ Icc ε B) :=
    (hA.hV.continuousOn_phi.comp_continuous
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).mul
        (hA.hH.zetaInv_continuous.comp (continuous_snd.comp continuous_snd)))
      fun p => (hA.hH.arg_mem ha p.2.1 p.2.2).1).continuousOn
  have hGD : ∀ x x' y, y ∈ Icc ε B → monoOLGKernel H' V' L a b x x' y ∈ Icc ε B :=
    fun x x' y hy => ⟨hεKC.trans (hb x'.2 hy.1).2.1, (hb x'.2 hy.1).2.2⟩
  have hG1 : ∀ e > 0, ∃ δ > 0, ∀ x z : Icc a b, dist x z < δ → ∀ x' y, y ∈ Icc ε B →
      |monoOLGKernel H' V' L a b x x' y - monoOLGKernel H' V' L a b z x' y| < e :=
    fun e he => ⟨1, one_pos, fun x z _ x' y _ => by simpa [monoOLGKernel] using he⟩
  have hG3 : ∀ e > 0, ∃ δ > 0, ∀ x x' y y', y ∈ Icc ε B → y' ∈ Icc ε B → |y - y'| < δ →
      |monoOLGKernel H' V' L a b x x' y - monoOLGKernel H' V' L a b x x' y'| < e := by
    intro e he
    have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hΦc
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc e he
    refine ⟨δ, hδ, fun x x' y y' hy hy' hyy => ?_⟩
    have := hδ' (x'.1, y) ⟨x'.2, hy⟩ (x'.1, y') ⟨x'.2, hy'⟩ (by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]; exact hyy)
    rwa [Real.dist_eq] at this
  have hGmono : ∀ x x' y y', y ∈ Icc ε B → y' ∈ Icc ε B → y ≤ y' →
      monoOLGKernel H' V' L a b x x' y ≤ monoOLGKernel H' V' L a b x x' y' :=
    fun x x' y y' _ _ hyy => (hA.hV.monotoneOn_phi h4) (hA.hH.arg_mem ha x' y).1
      (hA.hH.arg_mem ha x' y').1
      (mul_le_mul_of_nonneg_left (hA.hH.zetaInv_monotone hyy) (ha.le.trans x'.2.1))
  obtain ⟨hFc, hFb, hmaps, hcont, hmono, hequi, -, -, f, hf, g, hg, hTf, hTg, hfl, hgl, hbr⟩ :=
    kernelOp_monotone_fixedPoints hX hπ hεB hGc hGD hG1 hG3 hGmono
  refine ⟨hε, hεB, hFc, hFb, hmaps, hcont, hmono, hequi, f, hf, g, hg, hTf, hTg, hfl, hgl, hbr,
    fun hfg h hh hTh => ?_⟩
  subst hfg
  exact le_antisymm (hbr h hh hTh).2 (hbr h hh hTh).1

/-- **Every fixed point bounded away from zero lies in `F`** (NOTE to Proposition 5, p. 530;
derived). If `Th = h` and `h ≥ m > 0`, then `ε_K ≤ h ≤ B`. With `m₀ = inf h`: on `(0, ε_K)`
`ζ⁻¹(y) > Ky`, so `φ[x'ζ⁻¹(y)] ≥ KCy`; above `ε_K`, `φ[x'ζ⁻¹(y)] ≥ KCε_K`. Hence
`m₀ ≥ KC min(m₀, ε_K)`, and `KC > 1` forces `m₀ ≥ ε_K`; then `h ≤ B` by (5) of §17.4. -/
theorem monoOLG_fixedPoint_mem (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    (hab : a ≤ b) {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) {K : ℝ} (hK : 1 < K * (a * V' (b * L)))
    {h : Icc a b →ᵇ ℝ} (hfix : monoOLGOp π H' V' L h = h) (hpos : ∃ m > 0, ∀ x, m ≤ h x) :
    h ∈ monoF a b H' V' L K := by
  have hK0 := monoOLG_K_pos hA ha hab hK
  obtain ⟨hε, -, hbelow⟩ := hA.hH.epsK_spec hK0
  have hbL : (0 : ℝ) ≤ b * L := mul_nonneg (ha.le.trans hab) hA.hH.L_pos.le
  have hVpos := hA.hV.V'_pos hbL
  obtain ⟨m, hm, hmh⟩ := hpos
  have hne : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  have hbdd : BddBelow (range h) := ⟨m, by rintro _ ⟨x, rfl⟩; exact hmh x⟩
  have hm₀le : ∀ x, ⨅ x, h x ≤ h x := fun x => ciInf_le hbdd x
  have hm₀pos : 0 < ⨅ x, h x := lt_of_lt_of_le hm (le_ciInf hmh)
  have hfixx : ∀ x, h x = ∫ x', monoPhi V' (x'.1 * monoZetaInv H' L (h x')) ∂(π x) :=
    fun x => by
      conv_lhs => rw [← hfix]
      exact monoOLGOp_apply hA ha hπ h x
  obtain ⟨M, hM⟩ := hA.hV.exists_bound_phi (b * L)
  have hint : ∀ x, Integrable (fun x' => monoPhi V' (x'.1 * monoZetaInv H' L (h x'))) (π x) :=
    fun x => Integrable.of_bound
      (monoOLG_integrand_continuous hA ha h).measurable.aestronglyMeasurable
      M (Eventually.of_forall fun x' => by
        rw [Real.norm_eq_abs]; exact hM _ (hA.hH.arg_mem ha x' _))
  have hKC : 0 < K * (a * V' (b * L)) := by linarith
  have hlow : ∀ x' : Icc a b, K * (a * V' (b * L)) * min (⨅ x, h x) (monoEpsK H' L K) ≤
      monoPhi V' (x'.1 * monoZetaInv H' L (h x')) := by
    intro x'
    rcases le_or_gt (monoEpsK H' L K) (h x') with hy | hy
    · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hKC.le).trans
        (monoOLG_bounds hA ha hK0 x'.2 hy).2.1
    · have hy0 : 0 < h x' := lt_of_lt_of_le hm₀pos (hm₀le x')
      have hz := hbelow (h x') ⟨hy0, hy⟩
      have ht := hA.hH.arg_mem ha x' (h x')
      have hV'le : V' (b * L) ≤ V' (x'.1 * monoZetaInv H' L (h x')) :=
        hA.hV.strictAntiOn_V'.antitoneOn ht.1 hbL ht.2
      calc K * (a * V' (b * L)) * min (⨅ x, h x) (monoEpsK H' L K)
          ≤ K * (a * V' (b * L)) * h x' :=
            mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (hm₀le x')) hKC.le
        _ = (a * (K * h x')) * V' (b * L) := by ring
        _ ≤ (x'.1 * monoZetaInv H' L (h x')) * V' (b * L) :=
            mul_le_mul_of_nonneg_right (mul_le_mul x'.2.1 hz.le (by positivity)
              (ha.le.trans x'.2.1)) hVpos.le
        _ ≤ (x'.1 * monoZetaInv H' L (h x')) * V' (x'.1 * monoZetaInv H' L (h x')) :=
            mul_le_mul_of_nonneg_left hV'le ht.1
        _ = monoPhi V' (x'.1 * monoZetaInv H' L (h x')) := rfl
  have hm₀ge : K * (a * V' (b * L)) * min (⨅ x, h x) (monoEpsK H' L K) ≤ ⨅ x, h x :=
    le_ciInf fun x => by
      rw [hfixx x]
      calc K * (a * V' (b * L)) * min (⨅ x, h x) (monoEpsK H' L K)
          = ∫ _, K * (a * V' (b * L)) * min (⨅ x, h x) (monoEpsK H' L K) ∂(π x) := by simp
        _ ≤ _ := integral_mono (integrable_const _) (hint x) hlow
  have hεm : monoEpsK H' L K ≤ ⨅ x, h x := by
    refine le_of_not_gt fun hc => ?_
    rw [min_eq_left hc.le] at hm₀ge
    nlinarith
  intro x
  refine ⟨hεm.trans (hm₀le x), ?_⟩
  rw [hfixx x]
  calc ∫ x', monoPhi V' (x'.1 * monoZetaInv H' L (h x')) ∂(π x)
      ≤ ∫ _, monoB a b H' V' L K ∂(π x) :=
        integral_mono (hint x) (integrable_const _) fun x' =>
          (monoOLG_bounds hA ha hK0 x'.2 (hεm.trans (hm₀le x'))).2.2
    _ = monoB a b H' V' L K := by simp

/-- **Proposition 5, corrected** (SLP p. 530; see the NOTE). If the iterates from `f₀ ≡ ε_K` and
from `g₀ ≡ B` have the same limit `f`, then `f` is a fixed point of `T` with `f ≥ ε_K > 0`, and
it is the unique fixed point `h` of `T` with `inf h > 0`. -/
theorem proposition_5_corrected (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    (hab : a ≤ b) {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) (h4 : MonoAssumption17_4 V' V'') {K : ℝ}
    (hK : 1 < K * (a * V' (b * L))) {f : Icc a b →ᵇ ℝ}
    (hfl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoEpsK H' L K))) atTop (𝓝 f))
    (hgl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoB a b H' V' L K))) atTop
      (𝓝 f)) :
    monoOLGOp π H' V' L f = f ∧ f ∈ monoF a b H' V' L K ∧
      ∀ h, monoOLGOp π H' V' L h = h → (∃ m > 0, ∀ x, m ≤ h x) → h = f := by
  obtain ⟨-, -, -, -, -, -, -, -, f', hf', g', -, hTf', -, hf'l, hg'l, -, huniq⟩ :=
    proposition_5 hA ha hab hπ h4 hK
  have e1 : f' = f := tendsto_nhds_unique hf'l hfl
  have e2 : g' = f := tendsto_nhds_unique hg'l hgl
  subst e1
  subst e2
  exact ⟨hTf', hf', fun h hTh hpos =>
    huniq rfl h (monoOLG_fixedPoint_mem hA ha hab hπ hK hTh hpos) hTh⟩

/-- **Proposition 5, corrected**, strictly positive form: on the compact `X = [a, b]`, if
`f = g` then `f` is the unique strictly positive (continuous) fixed point of `T`. -/
theorem proposition_5_corrected' (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    (hab : a ≤ b) {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) (h4 : MonoAssumption17_4 V' V'') {K : ℝ}
    (hK : 1 < K * (a * V' (b * L))) {f : Icc a b →ᵇ ℝ}
    (hfl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoEpsK H' L K))) atTop (𝓝 f))
    (hgl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoB a b H' V' L K))) atTop
      (𝓝 f)) {h : Icc a b →ᵇ ℝ} (hTh : monoOLGOp π H' V' L h = h) (hpos : ∀ x, 0 < h x) :
    h = f := by
  have hne : (univ : Set (Icc a b)).Nonempty := ⟨⟨a, le_rfl, hab⟩, mem_univ _⟩
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn hne h.continuous.continuousOn
  exact (proposition_5_corrected hA ha hab hπ h4 hK hfl hgl).2.2 h hTh
    ⟨h x₀, hpos x₀, fun x => hx₀ (mem_univ x)⟩

/-- **Proposition 5 as stated is false whenever its hypothesis `f = g` holds** (SLP p. 530):
if `Tⁿε_K → f` and `TⁿB → f`, then `f` is *not* the unique fixed point of `T`, because the
zero function is another one. (`proposition_5_counterexample`, in `MonotoneOLGExamples`, shows
that the hypothesis `f = g` is satisfied in a concrete economy.) -/
theorem proposition_5_literal_false (hA : MonoAssumption17_1 H H' H'' V V' V'' L) (ha : 0 < a)
    (hab : a ≤ b) {π : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel π]
    (hπ : MonoAssumption17_3 π) (h4 : MonoAssumption17_4 V' V'') {K : ℝ}
    (hK : 1 < K * (a * V' (b * L))) {f : Icc a b →ᵇ ℝ}
    (hfl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoEpsK H' L K))) atTop (𝓝 f))
    (hgl : Tendsto (fun n => (monoOLGOp π H' V' L)^[n] (const _ (monoB a b H' V' L K))) atTop
      (𝓝 f)) :
    ¬ ∀ h, monoOLGOp π H' V' L h = h → h = f := by
  intro H
  have h0 := H 0 (monoOLGOp_zero hA ha hπ)
  obtain ⟨-, hf, -⟩ := proposition_5_corrected hA ha hab hπ h4 hK hfl hgl
  obtain ⟨hε, -, -⟩ := hA.hH.epsK_spec (monoOLG_K_pos hA ha hab hK)
  have := (hf ⟨a, le_rfl, hab⟩).1
  rw [← h0] at this
  simp only [coe_zero, Pi.zero_apply] at this
  linarith

end StokeyLucasPrescott.FixedPointArguments

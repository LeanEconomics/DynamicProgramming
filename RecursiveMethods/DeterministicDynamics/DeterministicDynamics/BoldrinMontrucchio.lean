/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.Concavity

/-!
# Every smooth map is an optimal policy: Boldrin and Montrucchio

SLP Theorem 6.1, p. 138: let `X ⊆ ℝ` be compact and `g : X → X` twice continuously
differentiable, with `Γ(x) = X`. Then there are a return function `F` and a discount factor `β`
such that `(X, Γ, F, β)` satisfies Assumptions 4.3–4.4 and 4.7–4.9, and `g` is the optimal policy
function.

The book does not prove the theorem. The proof here uses the telescoping return
`F(x, y) = U(x) − βU(y) − (y − g(x))²/2` with `U(x) = −Kx²/2` and `β = 1/(2K)` (`bmF`):
`F(x, y) + βU(y) = U(x) − (y − g(x))²/2`. So `v = U` solves (FE) and the maximum is attained
exactly at `y = g(x)` (`bellman_bm`, `argmax_bm`). For `K` large, `F` is strictly concave
(`bm_assumption47`). Its concavity gap is
`θ(1 − θ)[KΔx²/2 − Δy²/4 + (Δy − Δg)²/2] + He − e²/2`, where `e` is the error of `g` against its
chord. That error is at most `(M₂/2)θ(1 − θ)Δx²`, because `g ± M₂x²/2` is convex
(`chord_error_le`).

`X` is a compact interval `[a, b]`, as the convexity of `X` in Assumption 4.3 requires. "Twice
continuously differentiable" is used only through bounds `|g'| ≤ M₁` and `|g''| ≤ M₂` on
`(a, b)`, which a `C²` map on `[a, b]` satisfies (`theorem_6_1`).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

/-- The return function `F(x, y) = −Kx²/2 + y²/4 − (y − g(x))²/2`; with `β = 1/(2K)` this is
`U(x) − βU(y) − (y − g(x))²/2` for `U(x) = −Kx²/2`. -/
noncomputable def bmF (g : ℝ → ℝ) (K x y : ℝ) : ℝ :=
  -(K * x ^ 2 / 2) + y ^ 2 / 4 - (y - g x) ^ 2 / 2

variable {a b : ℝ} {g g' g'' : ℝ → ℝ} {M₁ M₂ : ℝ}

/-- `|g(θx + (1 − θ)x') − θg(x) − (1 − θ)g(x')| ≤ (M₂/2)θ(1 − θ)(x − x')²`: `g ± M₂x²/2` is
convex. -/
theorem chord_error_le (hgc : ContinuousOn g (Icc a b))
    (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg'' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x)
    (hM₂ : ∀ x ∈ Ioo a b, |g'' x| ≤ M₂) {x x' θ : ℝ} (hx : x ∈ Icc a b) (hx' : x' ∈ Icc a b)
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |g (θ * x + (1 - θ) * x') - θ * g x - (1 - θ) * g x'| ≤
      M₂ / 2 * (θ * (1 - θ)) * (x - x') ^ 2 := by
  have hint : interior (Icc a b) = Ioo a b := interior_Icc
  -- `ψ_s(z) = s·g(z) + M₂z²/2` is convex for `s = ±1`
  have hconv : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      ConvexOn ℝ (Icc a b) (fun z => s * g z + M₂ / 2 * z ^ 2) := by
    intro s hs
    refine convexOn_of_hasDerivWithinAt2_nonneg (f' := fun z => s * g' z + M₂ * z)
      (f'' := fun z => s * g'' z + M₂) (convex_Icc a b)
      ((continuousOn_const.mul hgc).add (continuousOn_const.mul (continuousOn_pow 2)))
      (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_)
    · rw [hint] at hz
      have := ((hg' z hz).const_mul s).add ((hasDerivAt_pow 2 z).const_mul (M₂ / 2))
      convert this.hasDerivWithinAt using 1
      push_cast
      ring
    · rw [hint] at hz
      have := ((hg'' z hz).const_mul s).add ((hasDerivAt_id' z).const_mul M₂)
      convert this.hasDerivWithinAt using 1
      ring
    · rw [hint] at hz
      have := hM₂ z hz
      rw [abs_le] at this
      rcases hs with rfl | rfl <;> linarith [this.1, this.2]
  have key : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      s * (g (θ * x + (1 - θ) * x') - θ * g x - (1 - θ) * g x') ≤
        M₂ / 2 * (θ * (1 - θ)) * (x - x') ^ 2 := by
    intro s hs
    have := (hconv s hs).2 hx hx' h0 (by linarith : 0 ≤ 1 - θ) (by ring)
    simp only [smul_eq_mul] at this
    nlinarith
  rw [abs_le]
  constructor
  · have := key (-1) (Or.inr rfl); linarith
  · have := key 1 (Or.inl rfl); linarith

/-- `|g(x) − g(x')| ≤ M₁|x − x'|`. -/
theorem lipschitz_of_deriv_le (hgc : ContinuousOn g (Icc a b))
    (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hM₁ : ∀ x ∈ Ioo a b, |g' x| ≤ M₁) {x x' : ℝ}
    (hx : x ∈ Icc a b) (hx' : x' ∈ Icc a b) : |g x - g x'| ≤ M₁ * |x - x'| := by
  wlog hle : x' ≤ x generalizing x x'
  · rw [abs_sub_comm, abs_sub_comm x]
    exact this hx' hx (le_of_not_ge hle)
  rcases eq_or_lt_of_le hle with rfl | hlt
  · simp
  have hsub : Icc x' x ⊆ Icc a b := Icc_subset_Icc hx'.1 hx.2
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g g' hlt (hgc.mono hsub) fun z hz =>
    hg' z ⟨lt_of_le_of_lt hx'.1 hz.1, lt_of_lt_of_le hz.2 hx.2⟩
  have hcI : c ∈ Ioo a b := ⟨lt_of_le_of_lt hx'.1 hc.1, lt_of_lt_of_le hc.2 hx.2⟩
  have hpos : 0 < x - x' := sub_pos.2 hlt
  rw [eq_div_iff hpos.ne'] at hcd
  rw [← hcd, abs_mul]
  exact mul_le_mul_of_nonneg_right (hM₁ c hcI) (abs_nonneg _)

/-- The concavity gap of `F`, written out. -/
theorem bmF_gap (K θ x y x' y' : ℝ) :
    bmF g K (θ * x + (1 - θ) * x') (θ * y + (1 - θ) * y') - θ * bmF g K x y -
        (1 - θ) * bmF g K x' y' =
      θ * (1 - θ) * (K / 2 * (x - x') ^ 2 - (y - y') ^ 2 / 4 +
        ((y - g x) - (y' - g x')) ^ 2 / 2) +
      (θ * (y - g x) + (1 - θ) * (y' - g x')) *
          (g (θ * x + (1 - θ) * x') - θ * g x - (1 - θ) * g x') -
        (g (θ * x + (1 - θ) * x') - θ * g x - (1 - θ) * g x') ^ 2 / 2 := by
  simp only [bmF]
  ring

/-- `K = M₁² + DM₂ + M₂²D²/16 + 1` with `D = b − a`. -/
noncomputable def bmK (a b M₁ M₂ : ℝ) : ℝ := M₁ ^ 2 + (b - a) * M₂ + M₂ ^ 2 * (b - a) ^ 2 / 16 + 1

theorem one_le_bmK (hab : a < b) (hM₂ : 0 ≤ M₂) : 1 ≤ bmK a b M₁ M₂ := by
  have : 0 ≤ (b - a) * M₂ := mul_nonneg (by linarith) hM₂
  simp only [bmK]
  nlinarith [sq_nonneg M₁, sq_nonneg (M₂ * (b - a))]

/-- **The concavity gap.** For `x, y, x', y' ∈ [a, b]`, the gap of `F` is at least
`θ(1 − θ)(x − x')²/2`. -/
theorem bm_gap_ge (hab : a < b) (hmaps : MapsTo g (Icc a b) (Icc a b))
    (hgc : ContinuousOn g (Icc a b)) (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg'' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x) (hM₁ : ∀ x ∈ Ioo a b, |g' x| ≤ M₁)
    (hM₂ : ∀ x ∈ Ioo a b, |g'' x| ≤ M₂) {x y x' y' θ : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc a b) (hx' : x' ∈ Icc a b) (hy' : y' ∈ Icc a b) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * (1 - θ) * (x - x') ^ 2 / 2 ≤
      bmF g (bmK a b M₁ M₂) (θ * x + (1 - θ) * x') (θ * y + (1 - θ) * y') -
        θ * bmF g (bmK a b M₁ M₂) x y - (1 - θ) * bmF g (bmK a b M₁ M₂) x' y' := by
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hM₁0 : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ _ hmid)
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ _ hmid)
  rw [bmF_gap]
  set D := b - a
  set T := θ * (1 - θ)
  set X2 := (x - x') ^ 2
  set e := g (θ * x + (1 - θ) * x') - θ * g x - (1 - θ) * g x'
  set H := θ * (y - g x) + (1 - θ) * (y' - g x')
  have hT : 0 ≤ T := mul_nonneg h0 (by linarith)
  have hT4 : T ≤ 1 / 4 := by simp only [T]; nlinarith [sq_nonneg (2 * θ - 1)]
  have hX2 : 0 ≤ X2 := sq_nonneg _
  have hXD : X2 ≤ D ^ 2 := by
    simp only [X2, D]
    nlinarith [hx.1, hx.2, hx'.1, hx'.2]
  have he : |e| ≤ M₂ / 2 * T * X2 := chord_error_le hgc hg' hg'' hM₂ hx hx' h0 h1
  have hgx := hmaps hx
  have hgx' := hmaps hx'
  have hH : |H| ≤ D := by
    rw [abs_le]
    simp only [H, D]
    constructor <;> nlinarith [hy.1, hy.2, hy'.1, hy'.2, hgx.1, hgx.2, hgx'.1, hgx'.2]
  have hE0 : 0 ≤ M₂ / 2 * T * X2 := by positivity
  have hHe : -(D * (M₂ / 2 * T * X2)) ≤ H * e := by
    have : |H * e| ≤ D * (M₂ / 2 * T * X2) := by
      rw [abs_mul]
      exact mul_le_mul hH he (abs_nonneg _) (by simp only [D]; linarith)
    linarith [neg_abs_le (H * e)]
  have hEE : M₂ / 2 * T * X2 ≤ M₂ / 8 * D ^ 2 := by
    have := mul_le_mul hT4 hXD hX2 (by norm_num)
    nlinarith
  have he2 : e ^ 2 ≤ (M₂ / 2 * T * X2) * (M₂ / 8 * D ^ 2) := by
    have h1' : e ^ 2 ≤ (M₂ / 2 * T * X2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) he 2
    nlinarith
  have hlip := lipschitz_of_deriv_le hgc hg' hM₁ hx hx'
  have hΔg : (g x - g x') ^ 2 ≤ M₁ ^ 2 * X2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hlip 2
    rw [sq_abs, mul_pow, sq_abs] at this
    exact this
  have hsq : -((g x - g x') ^ 2 / 2) ≤
      -((y - y') ^ 2 / 4) + ((y - g x) - (y' - g x')) ^ 2 / 2 := by
    nlinarith [sq_nonneg ((y - y') / 2 - (g x - g x'))]
  have m1 := mul_le_mul_of_nonneg_left hsq hT
  have m2 := mul_le_mul_of_nonneg_left hΔg hT
  rw [show bmK a b M₁ M₂ = M₁ ^ 2 + D * M₂ + M₂ ^ 2 * D ^ 2 / 16 + 1 from rfl]
  linarith

/-! ### The dynamic program on `[a, b]` -/

/-- `F` on `X × X`, `X = [a, b]`. -/
noncomputable def bmFs (g : ℝ → ℝ) (K : ℝ) (p : Icc a b × Icc a b) : ℝ := bmF g K p.1.1 p.2.1

theorem bm_assumption43 (hab : a < b) : Assumption43 (fun _ : Icc a b => (univ : Set (Icc a b))) :=
  have hne : (univ : Set (Icc a b)).Nonempty := ⟨⟨a, left_mem_Icc.2 hab.le⟩, mem_univ _⟩
  ⟨fun _ => hne, fun _ => isCompact_univ, fun _ => ⟨hne, fun y _ _ _ =>
    ⟨0, fun _ => y, fun _ _ => mem_univ _, tendsto_const_nhds⟩⟩,
    fun _ => ⟨hne, fun _ _ ys _ => by
      obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
      exact ⟨y, mem_univ _, φ, hφ, hlim⟩⟩⟩

theorem continuous_bmFs (hgc : ContinuousOn g (Icc a b)) (K : ℝ) :
    Continuous (bmFs (a := a) (b := b) g K) := by
  have hg : Continuous fun x : Icc a b => g x.1 :=
    hgc.comp_continuous continuous_subtype_val fun x => x.2
  have h1 : Continuous fun p : Icc a b × Icc a b => p.1.1 :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun p : Icc a b × Icc a b => p.2.1 :=
    continuous_subtype_val.comp continuous_snd
  have h3 : Continuous fun p : Icc a b × Icc a b => g p.1.1 := hg.comp continuous_fst
  unfold bmFs bmF
  exact ((continuous_const.mul (h1.pow 2)).div_const _).neg.add ((h2.pow 2).div_const _) |>.sub
    (((h2.sub h3).pow 2).div_const _)

theorem bm_assumption44 (hab : a < b) (hgc : ContinuousOn g (Icc a b)) (hM₂ : 0 ≤ M₂) :
    Assumption44 (fun _ : Icc a b => (univ : Set (Icc a b))) (bmFs g (bmK a b M₁ M₂))
      (1 / (2 * bmK a b M₁ M₂)) := by
  have hK := one_le_bmK (M₁ := M₁) hab hM₂
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_bmFs (a := a) (b := b) hgc (bmK a b M₁ M₂)).continuousOn
  refine ⟨(continuous_bmFs hgc _).continuousOn, ⟨B, fun p _ => hB p (mem_univ _)⟩,
    by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  linarith

/-- **Assumption 4.7** for `F` (strict concavity, with the strict gap when `x ≠ x'`). -/
theorem bm_assumption47 (hab : a < b) (hmaps : MapsTo g (Icc a b) (Icc a b))
    (hgc : ContinuousOn g (Icc a b)) (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg'' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x) (hM₁ : ∀ x ∈ Ioo a b, |g' x| ≤ M₁)
    (hM₂ : ∀ x ∈ Ioo a b, |g'' x| ≤ M₂) :
    Assumption47 (convex_Icc a b) (fun _ : Icc a b => (univ : Set (Icc a b)))
      (bmFs g (bmK a b M₁ M₂)) := by
  intro x y x' y' _ _ θ h0 h1
  have hgap := bm_gap_ge hab hmaps hgc hg' hg'' hM₁ hM₂ x.2 y.2 x'.2 y'.2 h0.le h1.le
  have e : bmFs g (bmK a b M₁ M₂) (cmb (convex_Icc a b) h0.le h1.le x x',
      cmb (convex_Icc a b) h0.le h1.le y y') =
      bmF g (bmK a b M₁ M₂) (θ * x.1 + (1 - θ) * x'.1) (θ * y.1 + (1 - θ) * y'.1) := by
    simp [bmFs, cmb, smul_eq_mul]
  rw [e]
  simp only [bmFs]
  have hT : 0 < θ * (1 - θ) := mul_pos h0 (by linarith)
  refine ⟨by nlinarith [sq_nonneg (x.1 - x'.1)], fun hne => ?_⟩
  have hx : x.1 ≠ x'.1 := fun h => hne (Subtype.ext h)
  have : 0 < (x.1 - x'.1) ^ 2 := by positivity
  nlinarith

/-- **Assumption 4.8**: `Γ(x) = X` has a convex graph. -/
theorem bm_assumption48 :
    Assumption48 (convex_Icc a b) (fun _ : Icc a b => (univ : Set (Icc a b))) :=
  fun _ _ _ _ _ _ _ _ _ => mem_univ _

/-- **Assumption 4.9**: `F` is continuously differentiable on the interior of `A`. -/
theorem bm_assumption49 (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg'' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x) (K : ℝ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => bmF g K p.1 p.2) (Ioo a b ×ˢ Ioo a b) := by
  have hgC : ContDiffOn ℝ 1 g (Ioo a b) := by
    have h := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := 0) (f := g)
      (isOpen_Ioo (a := a) (b := b))).2
    refine h ⟨fun x hx => (hg' x hx).differentiableAt.differentiableWithinAt,
      fun h0 => by simp at h0, ?_⟩
    refine contDiffOn_zero.2 ?_
    refine ContinuousOn.congr (f := g') (fun x hx => (hg'' x hx).continuousAt.continuousWithinAt)
      fun x hx => (hg' x hx).deriv
  have hgfst : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => g p.1) (Ioo a b ×ˢ Ioo a b) :=
    hgC.comp contDiffOn_fst fun p hp => hp.1
  unfold bmF
  exact (((contDiffOn_const.mul (contDiffOn_fst.pow 2)).div_const _).neg.add
    ((contDiffOn_snd.pow 2).div_const _)).sub (((contDiffOn_snd.sub hgfst).pow 2).div_const _)

/-- `v = U`, `U(x) = −Kx²/2`, as a bounded continuous function on `[a, b]`. -/
noncomputable def bmV (a b K : ℝ) : Icc a b →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => -(K * x.1 ^ 2 / 2), by fun_prop⟩

/-- The objective telescopes: `F(x, y) + βU(y) = U(x) − (y − g(x))²/2`. -/
theorem bm_obj {K : ℝ} (hK : 0 < K) (x y : Icc a b) :
    obj (bmFs g K) (1 / (2 * K)) (bmV a b K) (x, y) =
      -(K * x.1 ^ 2 / 2) - (y.1 - g x.1) ^ 2 / 2 := by
  simp only [obj, bmFs, bmF, bmV, mkOfCompact_apply, ContinuousMap.coe_mk]
  field_simp
  ring

/-- `U` solves (FE), and the maximum is attained exactly at `y = g(x)`. -/
theorem bellman_bm (hab : a < b) (hmaps : MapsTo g (Icc a b) (Icc a b))
    (hgc : ContinuousOn g (Icc a b)) (hM₂ : 0 ≤ M₂) :
    bellman (bm_assumption43 hab) (bm_assumption44 (M₁ := M₁) hab hgc hM₂)
        (bmV a b (bmK a b M₁ M₂)) = bmV a b (bmK a b M₁ M₂) ∧
      ∀ x, argmax (obj (bmFs g (bmK a b M₁ M₂)) (1 / (2 * bmK a b M₁ M₂))
        (bmV a b (bmK a b M₁ M₂))) (fun _ : Icc a b => (univ : Set (Icc a b))) x =
          {⟨g x.1, hmaps x.2⟩} := by
  have hK : 0 < bmK a b M₁ M₂ := lt_of_lt_of_le one_pos (one_le_bmK hab hM₂)
  -- the maximum value is `U(x)`, attained at `g(x)`
  have hgr : ∀ x : Icc a b, IsGreatest ((fun y => obj (bmFs g (bmK a b M₁ M₂))
      (1 / (2 * bmK a b M₁ M₂)) (bmV a b (bmK a b M₁ M₂)) (x, y)) '' (univ : Set (Icc a b)))
      (-(bmK a b M₁ M₂ * x.1 ^ 2 / 2)) := fun x => by
    refine ⟨⟨⟨g x.1, hmaps x.2⟩, mem_univ _, ?_⟩, ?_⟩
    · simp only [bm_obj hK, sub_self]; ring
    · rintro _ ⟨y, -, rfl⟩
      simp only [bm_obj hK]
      nlinarith [sq_nonneg (y.1 - g x.1)]
  have hmax : ∀ x : Icc a b, maxValue (obj (bmFs g (bmK a b M₁ M₂)) (1 / (2 * bmK a b M₁ M₂))
      (bmV a b (bmK a b M₁ M₂))) (fun _ => univ) x = -(bmK a b M₁ M₂ * x.1 ^ 2 / 2) :=
    fun x => (hgr x).csSup_eq
  refine ⟨?_, fun x => ?_⟩
  · ext x
    rw [bellman_apply, hmax]
    simp [bmV]
  · ext y
    rw [mem_singleton_iff]
    change (y ∈ univ ∧ _ = _) ↔ _
    rw [hmax, bm_obj hK]
    constructor
    · rintro ⟨-, hy⟩
      have h0 : (y.1 - g x.1) ^ 2 = 0 := by linarith
      exact Subtype.ext (sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0))
    · rintro rfl
      exact ⟨mem_univ _, by simp⟩

/-- **Theorem 6.1 (Boldrin and Montrucchio).** Let `X = [a, b]` and let `g : X → X` be twice
differentiable on `(a, b)`, continuous on `X`, with `|g'| ≤ M₁` and `|g''| ≤ M₂`. With
`F(x, y) = −Kx²/2 + y²/4 − (y − g(x))²/2` and `β = 1/(2K)`, `K = bmK a b M₁ M₂`, and `Γ(x) = X`,
Assumptions 4.3–4.4 and 4.7–4.9 hold, and for the fixed point `v` of `T` (Theorem 4.6) the policy
correspondence is `G(x) = {g(x)}`: `g` is the optimal policy function. -/
theorem theorem_6_1 (hab : a < b) (hmaps : MapsTo g (Icc a b) (Icc a b))
    (hgc : ContinuousOn g (Icc a b)) (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg'' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x) (hM₁ : ∀ x ∈ Ioo a b, |g' x| ≤ M₁)
    (hM₂ : ∀ x ∈ Ioo a b, |g'' x| ≤ M₂) :
    ∃ (h43 : Assumption43 (fun _ : Icc a b => (univ : Set (Icc a b))))
      (h44 : Assumption44 (fun _ : Icc a b => (univ : Set (Icc a b))) (bmFs g (bmK a b M₁ M₂))
        (1 / (2 * bmK a b M₁ M₂))),
      Assumption47 (convex_Icc a b) (fun _ : Icc a b => (univ : Set (Icc a b)))
          (bmFs g (bmK a b M₁ M₂)) ∧
        Assumption48 (convex_Icc a b) (fun _ : Icc a b => (univ : Set (Icc a b))) ∧
        ContDiffOn ℝ 1 (fun p : ℝ × ℝ => bmF g (bmK a b M₁ M₂) p.1 p.2) (Ioo a b ×ˢ Ioo a b) ∧
        ∀ v, bellman h43 h44 v = v → ∀ x,
          argmax (obj (bmFs g (bmK a b M₁ M₂)) (1 / (2 * bmK a b M₁ M₂)) v)
            (fun _ : Icc a b => (univ : Set (Icc a b))) x = {⟨g x.1, hmaps x.2⟩} := by
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ _ hmid)
  have : Nonempty (Icc a b) := ⟨⟨a, left_mem_Icc.2 hab.le⟩⟩
  obtain ⟨hfix, hargmax⟩ := bellman_bm (M₁ := M₁) hab hmaps hgc hM₂0
  obtain ⟨v₀, -, huniq, -⟩ := theorem_4_6 (bm_assumption43 hab)
    (bm_assumption44 (M₁ := M₁) hab hgc hM₂0)
  refine ⟨bm_assumption43 hab, bm_assumption44 hab hgc hM₂0,
    bm_assumption47 hab hmaps hgc hg' hg'' hM₁ hM₂, bm_assumption48,
    bm_assumption49 hg' hg'' _, fun v hv x => ?_⟩
  rw [(huniq v hv).trans (huniq _ hfix).symm]
  exact hargmax x

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.WNSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Example 7.3.1: the deterministic AK model with `u = C^γ`

Miao §7.3.2, pp. 213–214. The Bellman operator
`Tf(K) = max_{y ∈ [0, AK]} (AK − y)^γ + βf(y)` acts on the continuous functions
`f : ℝ₊ → ℝ` that are homogeneous of degree `γ` (`wn_IsHomog`), with the weight `ϕ(K) = K^γ`
and the footnote convention at `K = 0`. Functions are `ℝ → ℝ`, of which only the values on
`[0, ∞)` matter.

* `wn_homog_eq`: a homogeneous `f` is `f(K) = f(1)K^γ`; `example_7_3_1_norm`:
  `‖f‖_ϕ = sup_{K ≥ 0} |f(K)/K^γ| = |f(1)|` (with `f(0)/0^γ = 0/0 = 0`, `f(0) = 0`).
* `wn_akT_eq`, `example_7_3_1_selfMap`: `Tf(K) = Tf(1)K^γ`, so `T` maps the space into itself.
* `example_7_3_1_monotone`, `example_7_3_1_discount`, `example_7_3_1_T0`: monotonicity,
  `T(f + aϕ) ≤ Tf + βA^γaϕ` (for every `a ≥ 0`: the book's step uses `a ≥ 0` and `y ≤ AK`), and
  `T0 = A^γϕ`.
* `example_7_3_1_contraction`: `‖Tf − Tg‖_ϕ ≤ βA^γ‖f − g‖_ϕ`.
* `example_7_3_1`: if `βA^γ < 1`, `T` has a unique fixed point in the space.
* `example_7_3_1_no_fixedPoint`: conversely, if `βA^γ ≥ 1` (and `γ < 1`) there is no fixed
  point at all in the space, so `βA^γ < 1` is necessary as well as sufficient.
-/

namespace Miao.InfiniteHorizonDP

open Filter Topology

/-- Miao, p. 214: `f : ℝ₊ → ℝ` is continuous and homogeneous of degree `γ`. -/
def wn_IsHomog (γ : ℝ) (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧ ∀ K, 0 ≤ K → ∀ l, 0 ≤ l → f (l * K) = l ^ γ * f K

/-- Miao, p. 214: the weighted sup norm `‖f‖_ϕ = sup_{K ≥ 0} |f(K)/K^γ|`. -/
noncomputable def wn_akNorm (γ : ℝ) (f : ℝ → ℝ) : ℝ := ⨆ K : Set.Ici (0 : ℝ), |f K / (K : ℝ) ^ γ|

/-- Miao, p. 214: the Bellman operator `Tf(K) = max_{y ∈ [0, AK]} (AK − y)^γ + βf(y)`. -/
noncomputable def wn_akT (A β γ : ℝ) (f : ℝ → ℝ) (K : ℝ) : ℝ :=
  ⨆ y : Set.Icc (0 : ℝ) (A * K), (A * K - y) ^ γ + β * f y

variable {A β γ : ℝ}

/-- A homogeneous function of degree `γ` is `f(K) = f(1)K^γ` on `ℝ₊`. -/
theorem wn_homog_eq {f : ℝ → ℝ} (hf : wn_IsHomog γ f) {K : ℝ} (hK : 0 ≤ K) :
    f K = f 1 * K ^ γ := by
  have h := hf.2 1 zero_le_one K hK
  rw [mul_one] at h
  rw [h, mul_comm]

/-- `K ↦ cK^γ` is continuous and homogeneous of degree `γ` (`γ > 0`). -/
theorem wn_homog_of_eq (hγ : 0 < γ) {f : ℝ → ℝ} (c : ℝ) (hf : ∀ K, 0 ≤ K → f K = c * K ^ γ) :
    wn_IsHomog γ f := by
  refine ⟨ContinuousOn.congr (continuous_const.mul (Real.continuous_rpow_const hγ.le)).continuousOn
    fun K hK => hf K hK, fun K hK l hl => ?_⟩
  rw [hf _ (mul_nonneg hl hK), hf K hK, Real.mul_rpow hl hK]
  ring

theorem wn_homog_sub (hγ : 0 < γ) {f g : ℝ → ℝ} (hf : wn_IsHomog γ f) (hg : wn_IsHomog γ g) :
    wn_IsHomog γ (f - g) :=
  wn_homog_of_eq hγ (f 1 - g 1) fun K hK => by
    simp only [Pi.sub_apply, wn_homog_eq hf hK, wn_homog_eq hg hK]
    ring

/-- **Example 7.3.1** (Miao, p. 214): on homogeneous functions of degree `γ`,
`‖f‖_ϕ = sup_{K ≥ 0} |f(K)/K^γ| = |f(1)| < ∞` (at `K = 0`, `f(0) = 0` and `0/0 = 0`). -/
theorem example_7_3_1_norm (hγ : 0 < γ) {f : ℝ → ℝ} (hf : wn_IsHomog γ f) :
    wn_akNorm γ f = |f 1| := by
  have hle : ∀ K : Set.Ici (0 : ℝ), |f K / (K : ℝ) ^ γ| ≤ |f 1| := fun K => by
    have hK0 : (0 : ℝ) ≤ K := K.2
    rcases hK0.eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow hγ.ne', div_zero, abs_zero]
      exact abs_nonneg _
    · rw [wn_homog_eq hf K.2, mul_div_assoc, div_self (Real.rpow_pos_of_pos hpos γ).ne', mul_one]
  refine le_antisymm (Real.iSup_le hle (abs_nonneg _)) ?_
  have h1 : |f 1 / (1 : ℝ) ^ γ| ≤ wn_akNorm γ f :=
    le_ciSup (f := fun K : Set.Ici (0 : ℝ) => |f K / (K : ℝ) ^ γ|)
      ⟨|f 1|, by rintro _ ⟨K, rfl⟩; exact hle K⟩
      (⟨1, Set.mem_Ici.2 zero_le_one⟩ : Set.Ici (0 : ℝ))
  rwa [Real.one_rpow, div_one] at h1

/-- The Bellman objective is bounded above on `[0, AK]` for homogeneous `f`. -/
theorem wn_ak_bdd (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {f : ℝ → ℝ} (hf : wn_IsHomog γ f) (K : ℝ) :
    BddAbove (Set.range fun y : Set.Icc (0 : ℝ) (A * K) => (A * K - y) ^ γ + β * f y) := by
  refine ⟨(A * K) ^ γ + β * |f 1| * (A * K) ^ γ, ?_⟩
  rintro _ ⟨y, rfl⟩
  have hy0 : (0 : ℝ) ≤ y := y.2.1
  have h1 : (A * K - y) ^ γ ≤ (A * K) ^ γ :=
    Real.rpow_le_rpow (sub_nonneg.2 y.2.2) (by linarith) hγ
  have h2 : f y ≤ |f 1| * (A * K) ^ γ := by
    rw [wn_homog_eq hf hy0]
    calc f 1 * (y : ℝ) ^ γ ≤ |f 1| * (y : ℝ) ^ γ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hy0 _)
      _ ≤ |f 1| * (A * K) ^ γ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy0 y.2.2 hγ) (abs_nonneg _)
  have h3 := mul_le_mul_of_nonneg_left h2 hβ
  dsimp only
  nlinarith

theorem wn_ak_nonempty (hA : 0 ≤ A) {K : ℝ} (hK : 0 ≤ K) : Nonempty (Set.Icc (0 : ℝ) (A * K)) :=
  ⟨⟨0, le_rfl, mul_nonneg hA hK⟩⟩

/-- `T` depends only on the values of `f` on `ℝ₊`. -/
theorem wn_akT_congr {f g : ℝ → ℝ} (h : ∀ y, 0 ≤ y → f y = g y) : wn_akT A β γ f = wn_akT A β γ g :=
  funext fun K => by
    simp only [wn_akT]
    congr 1
    funext y
    rw [h y y.2.1]

/-- Miao, p. 214 (homogeneity of the Bellman operator): `Tf(K) = Tf(1)K^γ` for `K ≥ 0`. -/
theorem wn_akT_eq (hA : 0 ≤ A) (hβ : 0 ≤ β) (hγ : 0 < γ) {f : ℝ → ℝ} (hf : wn_IsHomog γ f)
    {K : ℝ} (hK : 0 ≤ K) : wn_akT A β γ f K = wn_akT A β γ f 1 * K ^ γ := by
  have hKγ : 0 ≤ K ^ γ := Real.rpow_nonneg hK γ
  -- every `y ∈ [0, AK]` is `Ks` with `s ∈ [0, A]`, and the objective scales by `K^γ`
  have hscale : ∀ s : ℝ, 0 ≤ s → s ≤ A * 1 →
      (A * K - K * s) ^ γ + β * f (K * s) = K ^ γ * ((A * 1 - s) ^ γ + β * f s) := by
    intro s hs0 hs1
    have hAs : 0 ≤ A * 1 - s := by linarith
    have he : A * K - K * s = K * (A * 1 - s) := by ring
    rw [he, Real.mul_rpow hK hAs, hf.2 s hs0 K hK]
    ring
  have hb1 := wn_ak_bdd (A := A) hβ hγ.le hf 1
  have hbK := wn_ak_bdd (A := A) hβ hγ.le hf K
  have := wn_ak_nonempty hA hK
  have := wn_ak_nonempty hA zero_le_one
  refine le_antisymm (ciSup_le fun y => ?_) ?_
  · obtain ⟨s, hs0, hs1, hys⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ A * 1 ∧ (y : ℝ) = K * s := by
      rcases hK.eq_or_lt with h0 | hpos
      · subst h0
        refine ⟨0, le_rfl, by linarith, ?_⟩
        have h1 : (y : ℝ) ≤ A * 0 := y.2.2
        have h2 : (0 : ℝ) ≤ y := y.2.1
        exact le_antisymm (by linarith) (by linarith)
      · refine ⟨y / K, div_nonneg y.2.1 hK, ?_, by rw [mul_div_cancel₀ _ hpos.ne']⟩
        rw [div_le_iff₀ hpos, mul_one]
        exact y.2.2
    rw [hys, hscale s hs0 hs1, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (le_ciSup hb1 (⟨s, hs0, hs1⟩ : Set.Icc (0 : ℝ) (A * 1))) hKγ
  · rw [wn_akT, Real.iSup_mul_of_nonneg hKγ]
    refine ciSup_le fun s => ?_
    have hmem : K * (s : ℝ) ∈ Set.Icc (0 : ℝ) (A * K) := ⟨mul_nonneg hK s.2.1, by
      have h1 := mul_le_mul_of_nonneg_left s.2.2 hK
      linarith⟩
    rw [mul_comm, ← hscale s s.2.1 s.2.2]
    exact le_ciSup hbK (⟨K * s, hmem⟩ : Set.Icc (0 : ℝ) (A * K))

/-- **Example 7.3.1** (Miao, p. 214): `T` maps the continuous functions homogeneous of degree `γ`
into themselves. -/
theorem example_7_3_1_selfMap (hA : 0 ≤ A) (hβ : 0 ≤ β) (hγ : 0 < γ) {f : ℝ → ℝ}
    (hf : wn_IsHomog γ f) : wn_IsHomog γ (wn_akT A β γ f) :=
  wn_homog_of_eq hγ _ fun _ hK => wn_akT_eq hA hβ hγ hf hK

/-- **Example 7.3.1** (Miao, p. 214): monotonicity, `f ≤ g` on `ℝ₊` implies `Tf ≤ Tg` on `ℝ₊`. -/
theorem example_7_3_1_monotone (hA : 0 ≤ A) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {f g : ℝ → ℝ}
    (hg : wn_IsHomog γ g) (hfg : ∀ K, 0 ≤ K → f K ≤ g K) {K : ℝ} (hK : 0 ≤ K) :
    wn_akT A β γ f K ≤ wn_akT A β γ g K := by
  have := wn_ak_nonempty hA hK
  refine ciSup_le fun y => ?_
  have h1 := mul_le_mul_of_nonneg_left (hfg y y.2.1) hβ
  exact (add_le_add_right h1 _).trans (le_ciSup (wn_ak_bdd hβ hγ hg K) y)

/-- **Example 7.3.1** (Miao, p. 214): discounting,
`T(f + aϕ)(K) ≤ Tf(K) + βA^γ a ϕ(K)` with `ϕ(K) = K^γ`, for every `a ≥ 0`. -/
theorem example_7_3_1_discount (hA : 0 ≤ A) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {f : ℝ → ℝ}
    (hf : wn_IsHomog γ f) {a : ℝ} (ha : 0 ≤ a) {K : ℝ} (hK : 0 ≤ K) :
    wn_akT A β γ (fun y => f y + a * y ^ γ) K ≤ wn_akT A β γ f K + β * A ^ γ * a * K ^ γ := by
  have := wn_ak_nonempty hA hK
  refine ciSup_le fun y => ?_
  have hy : (y : ℝ) ^ γ ≤ (A * K) ^ γ := Real.rpow_le_rpow y.2.1 y.2.2 hγ
  have h1 := mul_le_mul_of_nonneg_left hy (mul_nonneg hβ ha)
  have h2 : (A * K - y) ^ γ + β * f y ≤ wn_akT A β γ f K := le_ciSup (wn_ak_bdd hβ hγ hf K) y
  rw [Real.mul_rpow hA hK] at h1
  dsimp only
  nlinarith

/-- **Example 7.3.1** (Miao, p. 214): `T0(K) = max_{C ∈ [0, AK]} C^γ = A^γK^γ = A^γϕ(K)`. -/
theorem example_7_3_1_T0 (hA : 0 ≤ A) (hγ : 0 ≤ γ) {K : ℝ} (hK : 0 ≤ K) :
    wn_akT A β γ (fun _ => 0) K = A ^ γ * K ^ γ := by
  rw [← Real.mul_rpow hA hK]
  have := wn_ak_nonempty hA hK
  have hb : BddAbove (Set.range fun y : Set.Icc (0 : ℝ) (A * K) => (A * K - y) ^ γ + β * 0) :=
    ⟨(A * K) ^ γ, by
      rintro _ ⟨y, rfl⟩
      simpa using Real.rpow_le_rpow (sub_nonneg.2 y.2.2) (by linarith [y.2.1]) hγ⟩
  refine le_antisymm (ciSup_le fun y => ?_) ?_
  · simpa using Real.rpow_le_rpow (sub_nonneg.2 y.2.2) (by linarith [y.2.1]) hγ
  · have h : (A * K - 0) ^ γ + β * 0 ≤ wn_akT A β γ (fun _ => 0) K :=
      le_ciSup hb ⟨0, le_rfl, mul_nonneg hA hK⟩
    rwa [sub_zero, mul_zero, add_zero] at h

/-- **Example 7.3.1** (Miao, p. 214): `T` is a contraction with modulus `βA^γ`,
`‖Tf − Tg‖_ϕ ≤ βA^γ‖f − g‖_ϕ`, by monotonicity and discounting applied to
`f ≤ g + ‖f − g‖_ϕ ϕ`. -/
theorem example_7_3_1_contraction (hA : 0 ≤ A) (hβ : 0 ≤ β) (hγ : 0 < γ) {f g : ℝ → ℝ}
    (hf : wn_IsHomog γ f) (hg : wn_IsHomog γ g) :
    wn_akNorm γ (wn_akT A β γ f - wn_akT A β γ g) ≤ β * A ^ γ * wn_akNorm γ (f - g) := by
  rw [example_7_3_1_norm hγ (wn_homog_sub hγ (example_7_3_1_selfMap hA hβ hγ hf)
    (example_7_3_1_selfMap hA hβ hγ hg)), example_7_3_1_norm hγ (wn_homog_sub hγ hf hg)]
  simp only [Pi.sub_apply]
  -- one side: `Tf(1) ≤ Tg(1) + βA^γ|f(1) − g(1)|`
  have one : ∀ f g : ℝ → ℝ, wn_IsHomog γ f → wn_IsHomog γ g →
      wn_akT A β γ f 1 ≤ wn_akT A β γ g 1 + β * A ^ γ * |f 1 - g 1| := by
    intro f g hf hg
    set a := |f 1 - g 1|
    have hga : wn_IsHomog γ fun y => g y + a * y ^ γ :=
      wn_homog_of_eq hγ (g 1 + a) fun K hK => by rw [wn_homog_eq hg hK]; ring
    have hle : ∀ K, 0 ≤ K → f K ≤ g K + a * K ^ γ := fun K hK => by
      rw [wn_homog_eq hf hK, wn_homog_eq hg hK]
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (f 1 - g 1)) (Real.rpow_nonneg hK γ)
      linarith
    have h1 := example_7_3_1_monotone hA hβ hγ.le hga hle zero_le_one
    have h2 := example_7_3_1_discount hA hβ hγ.le hg (abs_nonneg (f 1 - g 1)) zero_le_one
    rw [Real.one_rpow, mul_one] at h2
    exact h1.trans h2
  have h1 := one f g hf hg
  have h2 := one g f hg hf
  rw [abs_sub_comm (g 1)] at h2
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- **Example 7.3.1** (Miao, p. 214): if `βA^γ < 1`, the Bellman operator has a unique fixed
point among the continuous functions on `ℝ₊` homogeneous of degree `γ` (unique as a function on
`ℝ₊`). -/
theorem example_7_3_1 (hA : 0 < A) (hβ : 0 < β) (hγ : 0 < γ) (hθ : β * A ^ γ < 1) :
    ∃ V, wn_IsHomog γ V ∧ (∀ K, 0 ≤ K → wn_akT A β γ V K = V K) ∧
      ∀ W, wn_IsHomog γ W → (∀ K, 0 ≤ K → wn_akT A β γ W K = W K) →
        ∀ K, 0 ≤ K → W K = V K := by
  have hθ0 : 0 ≤ β * A ^ γ := mul_nonneg hβ.le (Real.rpow_nonneg hA.le γ)
  have hcK : ∀ c : ℝ, wn_IsHomog γ fun K => c * K ^ γ := fun c => wn_homog_of_eq hγ c fun _ _ => rfl
  let G : ℝ → ℝ := fun c => wn_akT A β γ (fun K => c * K ^ γ) 1
  have hG : ContractingWith ⟨β * A ^ γ, hθ0⟩ G := by
    refine ⟨by exact_mod_cast hθ, LipschitzWith.of_dist_le_mul fun c d => ?_⟩
    have h := example_7_3_1_contraction hA.le hβ.le hγ (hcK c) (hcK d)
    rw [example_7_3_1_norm hγ (wn_homog_sub hγ (example_7_3_1_selfMap hA.le hβ.le hγ (hcK c))
      (example_7_3_1_selfMap hA.le hβ.le hγ (hcK d))),
      example_7_3_1_norm hγ (wn_homog_sub hγ (hcK c) (hcK d))] at h
    simp only [Pi.sub_apply, Real.one_rpow, mul_one] at h
    rw [Real.dist_eq, Real.dist_eq]
    exact h
  set c := ContractingWith.fixedPoint G hG
  have hc : G c = c := ContractingWith.fixedPoint_isFixedPt (f := G) hG
  refine ⟨fun K => c * K ^ γ, hcK c, fun K hK => ?_, fun W hW hWfix K hK => ?_⟩
  · rw [wn_akT_eq hA.le hβ.le hγ (hcK c) hK]
    exact congrArg (· * K ^ γ) hc
  · have hW1 : G (W 1) = W 1 := by
      have h := hWfix 1 zero_le_one
      rwa [wn_akT_congr (fun y hy => wn_homog_eq hW hy)] at h
    have := ContractingWith.fixedPoint_unique (f := G) hG (x := W 1) hW1
    rw [wn_homog_eq hW hK, this]

/-- **Example 7.3.1, converse** (Miao, p. 214, which gives only "if"). If `βA^γ ≥ 1` and
`γ < 1`, the Bellman operator has no fixed point among the homogeneous functions of degree `γ`:
a fixed point `V = cK^γ` would satisfy `c ≥ A^γ > 0` (take `y = 0`) and, taking
`y = A(1 − ε)`, `cε ≥ A^γε^γ`, i.e. `c ≥ A^γε^{γ−1}` for all small `ε > 0`. -/
theorem example_7_3_1_no_fixedPoint (hA : 0 < A) (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ : 1 ≤ β * A ^ γ) :
    ¬ ∃ V, wn_IsHomog γ V ∧ ∀ K, 0 ≤ K → wn_akT A β γ V K = V K := by
  rintro ⟨V, hV, hfix⟩
  set c := V 1
  have hAγ : 0 < A ^ γ := Real.rpow_pos_of_pos hA γ
  have hb := wn_ak_bdd (A := A) hβ.le hγ0.le hV 1
  have hc1 : wn_akT A β γ V 1 = c := hfix 1 zero_le_one
  -- the objective at `y` is a lower bound for `c`
  have hlow : ∀ y : ℝ, 0 ≤ y → y ≤ A → (A * 1 - y) ^ γ + β * (c * y ^ γ) ≤ c := by
    intro y hy0 hy1
    have h : (A * 1 - y) ^ γ + β * V y ≤ wn_akT A β γ V 1 :=
      le_ciSup hb (⟨y, hy0, by linarith⟩ : Set.Icc (0 : ℝ) (A * 1))
    have hVy : V y = c * y ^ γ := wn_homog_eq hV hy0
    rwa [hVy, hc1] at h
  -- `y = 0`: `c ≥ A^γ`
  have hcA : A ^ γ ≤ c := by
    have h := hlow 0 le_rfl hA.le
    rw [sub_zero, mul_one, Real.zero_rpow hγ0.ne', mul_zero, mul_zero, add_zero] at h
    exact h
  have hc : 0 < c := hAγ.trans_le hcA
  -- choose `ε ∈ (0, 1)` with `ε^{1−γ} ≤ A^γ/(2c)`
  set δ := A ^ γ / (2 * c)
  have hδ : 0 < δ := div_pos hAγ (by linarith)
  have h1γ : 0 < 1 - γ := by linarith
  set ε := min (δ ^ (1 / (1 - γ))) (1 / 2)
  have hε0 : 0 < ε := lt_min (Real.rpow_pos_of_pos hδ _) (by norm_num)
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hεδ : ε ^ (1 - γ) ≤ δ := by
    calc ε ^ (1 - γ) ≤ (δ ^ (1 / (1 - γ))) ^ (1 - γ) :=
          Real.rpow_le_rpow hε0.le (min_le_left _ _) h1γ.le
      _ = δ := by rw [← Real.rpow_mul hδ.le, one_div_mul_cancel h1γ.ne', Real.rpow_one]
  have hεsplit : ε = ε ^ γ * ε ^ (1 - γ) := by
    rw [← Real.rpow_add hε0, add_sub_cancel, Real.rpow_one]
  -- `y = A(1 − ε)`
  have h := hlow (A * (1 - ε)) (mul_nonneg hA.le (by linarith)) (by nlinarith)
  have he1 : A * 1 - A * (1 - ε) = A * ε := by ring
  rw [he1, Real.mul_rpow hA.le hε0.le, Real.mul_rpow hA.le (by linarith)] at h
  have hbern : 1 - ε ≤ (1 - ε) ^ γ := by
    have h2 := Real.rpow_le_rpow_of_exponent_ge (by linarith : (0 : ℝ) < 1 - ε)
      (by linarith : 1 - ε ≤ 1) hγ1.le
    rwa [Real.rpow_one] at h2
  have hεγ : 0 < ε ^ γ := Real.rpow_pos_of_pos hε0 γ
  -- `c(1 − ε) ≤ βA^γ c (1 − ε)^γ`, hence `A^γ ε^γ ≤ cε`
  have h3 : c * (1 - ε) ≤ β * (c * (A ^ γ * (1 - ε) ^ γ)) := by
    have h4 : c * (1 - ε) ≤ c * (1 - ε) ^ γ := mul_le_mul_of_nonneg_left hbern hc.le
    have h5 : 0 ≤ c * (1 - ε) ^ γ := mul_nonneg hc.le (Real.rpow_nonneg (by linarith) _)
    nlinarith
  have h6 : A ^ γ * ε ^ γ ≤ c * ε := by nlinarith
  rw [hεsplit] at h6
  have h7 : A ^ γ ≤ c * ε ^ (1 - γ) := by
    have h8 : ε ^ γ * A ^ γ ≤ ε ^ γ * (c * ε ^ (1 - γ)) := by nlinarith
    exact le_of_mul_le_mul_left h8 hεγ
  have h9 : c * ε ^ (1 - γ) ≤ c * δ := mul_le_mul_of_nonneg_left hεδ hc.le
  have h10 : c * δ = A ^ γ / 2 := by
    simp only [δ]
    field_simp
  linarith

end Miao.InfiniteHorizonDP

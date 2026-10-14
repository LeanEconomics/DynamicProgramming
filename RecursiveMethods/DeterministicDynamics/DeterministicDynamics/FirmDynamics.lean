/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.AdjustmentCosts
import DeterministicDynamics.GrowthStability
import DeterministicDynamics.EulerScalar

/-!
# A firm with adjustment costs (Exercise 6.8)

SLP §6.5, pp. 158–159. The firm of §5.9 (`AdjustmentCosts`):
`v(k) = max_y {pf(k) − c[y − (1 − δ)k] + βv(y)}`, `β = 1/(1 + r)`, on the compact state space
`[0, K]` used there.

* `orbit_tendsto_of_crossing` (the method of §6.1): if `g` is continuous and nondecreasing on
  an interval it maps into itself, with a fixed point `k̄`, `g(k) > k` below `k̄` and `g(k) < k`
  above, then every orbit converges monotonically to `k̄`.
* **Exercise 6.8a** (`ex_6_8a_unique`, `ex_6_8`): an interior stationary point satisfies
  `c'(δk̄)(1 − β(1 − δ)) = βpf'(k̄)`, that is `(r + δ)c'(δk̄) = pf'(k̄)`. The left side rises and
  the right side falls in `k̄`, so there is at most one.
* **Exercise 6.8b** (`ex_6_8`): with `f(0) = 0`, `f'(0+) = ∞`, `c(0) = 0`, `c` nondecreasing and
  strictly convex, and `K` beyond the steady state (`βpf'(K) < c'(δK)(1 − β(1 − δ))`):
  `g(0) > 0` (investing at `k = 0` pays, because `f(ε)/ε → ∞`), `g(K) < K` (a first-order
  argument at the upper end), so `g` has exactly one fixed point `k̄`, interior, and from every
  `k₀ ∈ [0, K]` capital converges monotonically to `k̄`.
* **Exercise 6.8c** (`ex_6_8c`): at `k̄`, `F_xx = pf'' − (1 − δ)²c''`, `F_xy = (1 − δ)c''`,
  `F_yy = −c''`. With `f'' ≤ 0` and `c'' > 0` the characteristic roots of the linearized Euler
  equation are real, one in `(0, 1)` and one above `1` (`p(1) = −[δ(1 − β(1 − δ))c'' − βpf'']
  /(β(1 − δ)c'') < 0`), so `k̄` is saddle-path stable (`roots_split`).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

/-! ### Monotone convergence -/

/-- **The method of §6.1.** -/
theorem orbit_tendsto_of_crossing {g : ℝ → ℝ} {lo hi ks : ℝ}
    (hgc : ContinuousOn g (Icc lo hi)) (hgm : MonotoneOn g (Icc lo hi))
    (hmaps : MapsTo g (Icc lo hi) (Icc lo hi)) (hks : ks ∈ Icc lo hi) (hfix : g ks = ks)
    (hbelow : ∀ k ∈ Icc lo hi, k < ks → k < g k) (habove : ∀ k ∈ Icc lo hi, ks < k → g k < k)
    {k₀ : ℝ} (hk₀ : k₀ ∈ Icc lo hi) :
    (Monotone (fun t => g^[t] k₀) ∨ Antitone (fun t => g^[t] k₀)) ∧
      Tendsto (fun t => g^[t] k₀) atTop (𝓝 ks) := by
  set x : ℕ → ℝ := fun t => g^[t] k₀
  have hstep : ∀ t, x (t + 1) = g (x t) := fun t => Function.iterate_succ_apply' g t k₀
  have hmem : ∀ t, x t ∈ Icc lo hi := fun t => by
    induction t with
    | zero => exact hk₀
    | succ t ih => rw [hstep]; exact hmaps ih
  -- a limit `L` of the orbit is a fixed point
  have hfixL : ∀ L ∈ Icc lo hi, Tendsto x atTop (𝓝 L) → g L = L := fun L hL hlim => by
    have h1 : Tendsto (fun t => g (x t)) atTop (𝓝 (g L)) :=
      (hgc L hL).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hmem⟩)
    have h2 : Tendsto (fun t => g (x t)) atTop (𝓝 L) := by
      have := hlim.comp (tendsto_add_atTop_nat 1)
      simp only [Function.comp_def, hstep] at this
      exact this
    exact tendsto_nhds_unique h1 h2
  rcases le_or_gt k₀ ks with hle | hgt
  · have hub : ∀ t, x t ≤ ks := fun t => by
      induction t with
      | zero => exact hle
      | succ t ih => rw [hstep, ← hfix]; exact hgm (hmem t) hks ih
    have hmono : Monotone x := monotone_nat_of_le_succ fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hub t) with he | hlt
      · rw [he, hfix]
      · exact (hbelow _ (hmem t) hlt).le
    have hbdd : BddAbove (range x) := ⟨ks, by rintro _ ⟨t, rfl⟩; exact hub t⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    have hL : (⨆ t, x t) ∈ Icc lo hi := ⟨(hmem 0).1.trans (le_ciSup hbdd 0),
      (ciSup_le hub).trans hks.2⟩
    have hgL := hfixL _ hL hlim
    have heq : (⨆ t, x t) = ks := by
      by_contra hne
      have hlt : (⨆ t, x t) < ks := lt_of_le_of_ne (ciSup_le hub) hne
      have := hbelow _ hL hlt
      rw [hgL] at this
      exact lt_irrefl _ this
    rw [heq] at hlim
    exact ⟨Or.inl hmono, hlim⟩
  · have hlb : ∀ t, ks ≤ x t := fun t => by
      induction t with
      | zero => exact hgt.le
      | succ t ih => rw [hstep, ← hfix]; exact hgm hks (hmem t) ih
    have hanti : Antitone x := antitone_nat_of_succ_le fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hlb t) with he | hlt
      · rw [← he, hfix]
      · exact (habove _ (hmem t) hlt).le
    have hbdd : BddBelow (range x) := ⟨ks, by rintro _ ⟨t, rfl⟩; exact hlb t⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hL : (⨅ t, x t) ∈ Icc lo hi := ⟨hks.1.trans (le_ciInf hlb),
      (ciInf_le hbdd 0).trans (hmem 0).2⟩
    have hgL := hfixL _ hL hlim
    have heq : (⨅ t, x t) = ks := by
      by_contra hne
      have hlt : ks < (⨅ t, x t) := lt_of_le_of_ne (le_ciInf hlb) (Ne.symm hne)
      have := habove _ hL hlt
      rw [hgL] at this
      exact lt_irrefl _ this
    rw [heq] at hlim
    exact ⟨Or.inr hanti, hlim⟩

/-! ### Saddle-path roots -/

/-- If `p > 0` and `1 − s + p < 0`, the roots of `λ² − sλ + p` are real, one in `(0, 1)` and one
greater than `1`. -/
theorem roots_split {s p : ℝ} (hp : 0 < p) (h1 : 1 - s + p < 0) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ < 1 ∧ 1 < μ₂ ∧ quadRoot s p μ₁ ∧ quadRoot s p μ₂ ∧
      ∀ μ, quadRoot s p μ → μ = μ₁ ∨ μ = μ₂ := by
  have hd : 4 * p ≤ s ^ 2 := by nlinarith [sq_nonneg (1 - p)]
  set q := Real.sqrt (s ^ 2 - 4 * p)
  have hq : q ^ 2 = s ^ 2 - 4 * p := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqc : (q : ℂ) ^ 2 = (s : ℂ) ^ 2 - 4 * p := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hq
    push_cast at this
    exact this
  have hroot : ∀ r : ℝ, r = (s + q) / 2 ∨ r = (s - q) / 2 → quadRoot s p r := by
    rintro r (rfl | rfl) <;> simp only [quadRoot] <;> push_cast <;>
      linear_combination (1 / 4 : ℂ) * hqc
  have hfact : (1 - (s - q) / 2) * (1 - (s + q) / 2) = 1 - s + p := by nlinarith
  have hqs : q < s := by
    have : q ^ 2 < s ^ 2 := by rw [hq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by linarith) this
  refine ⟨(s - q) / 2, (s + q) / 2, by linarith, ?_, ?_, hroot _ (Or.inr rfl),
    hroot _ (Or.inl rfl), fun μ hμ => ?_⟩
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith
  · obtain ⟨r, rfl, hr⟩ := quadRoot_real hd hμ
    rcases hr with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- **Exercise 6.8c.** With `F_xx = pf'' − (1 − δ)²c''`, `F_xy = (1 − δ)c''`, `F_yy = −c''`,
`f'' ≤ 0 < c''`, `p > 0`, `0 < β < 1` and `0 < δ < 1`, the characteristic roots of the
linearized Euler equation, `λ² − Jλ + 1/β` with `J = −(F_yy + βF_xx)/(βF_xy)`, are real, one in
`(0, 1)` and one above `1`. -/
theorem ex_6_8c {p β δ f₂ c₂ : ℝ} (hp : 0 < p) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hf₂ : f₂ ≤ 0) (hc₂ : 0 < c₂) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ < 1 ∧ 1 < μ₂ ∧
      quadRoot (-(-c₂ + β * (p * f₂ - (1 - δ) ^ 2 * c₂)) / (β * ((1 - δ) * c₂))) (1 / β) μ₁ ∧
      quadRoot (-(-c₂ + β * (p * f₂ - (1 - δ) ^ 2 * c₂)) / (β * ((1 - δ) * c₂))) (1 / β) μ₂ ∧
      ∀ μ, quadRoot (-(-c₂ + β * (p * f₂ - (1 - δ) ^ 2 * c₂)) / (β * ((1 - δ) * c₂))) (1 / β) μ →
        μ = μ₁ ∨ μ = μ₂ := by
  refine roots_split (by positivity) ?_
  have hD : 0 < β * ((1 - δ) * c₂) := mul_pos hβ0 (mul_pos (by linarith) hc₂)
  -- `p(1)·β(1 − δ)c'' = −δ(1 − β(1 − δ))c'' + βpf'' < 0`
  have e : 1 - -(-c₂ + β * (p * f₂ - (1 - δ) ^ 2 * c₂)) / (β * ((1 - δ) * c₂)) + 1 / β =
      (-(δ * (1 - β * (1 - δ)) * c₂) + β * p * f₂) / (β * ((1 - δ) * c₂)) := by
    have h1δ : (1 - δ) ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  refine div_neg_of_neg_of_pos ?_ hD
  have h1 : 0 < 1 - β * (1 - δ) := by nlinarith
  have h2 : β * p * f₂ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hf₂
  have h3 : 0 < δ * (1 - β * (1 - δ)) * c₂ := by positivity
  linarith

/-! ### The firm -/

variable {f c f' c' : ℝ → ℝ} {p δ β K : ℝ}

/-- The hypotheses of Exercise 6.8 on `[0, K]`, on top of those of Exercise 5.9b. -/
structure FirmDyn (f c f' c' : ℝ → ℝ) (p δ β K : ℝ) : Prop where
  adj : AdjHyp f c p δ β K
  f_zero : f 0 = 0
  f_deriv : ∀ k, 0 < k → HasDerivAt f (f' k) k
  inada : Tendsto f' (𝓝[>] 0) atTop
  c_zero : c 0 = 0
  c_mono : Monotone c
  c_strict : StrictConvexOn ℝ univ c
  c_deriv : ∀ x, HasDerivAt c (c' x) x
  K_big : β * p * f' K < c' (δ * K) * (1 - β * (1 - δ))

/-- The policy `g`, extended by zero off `[0, K]`. -/
noncomputable def fpol (f c : ℝ → ℝ) (p δ β K : ℝ) [Nonempty (Icc (0 : ℝ) K)]
    (v : Icc (0 : ℝ) K →ᵇ ℝ) (k : ℝ) : ℝ := by
  classical exact if hk : k ∈ Icc 0 K then
    (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) ⟨k, hk⟩).1 else 0

theorem fpol_of_mem [Nonempty (Icc (0 : ℝ) K)] (v : Icc (0 : ℝ) K →ᵇ ℝ) {k : ℝ}
    (hk : k ∈ Icc 0 K) :
    fpol f c p δ β K v k = (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) ⟨k, hk⟩).1 := by
  simp only [fpol, hk, ↓reduceDIte]

namespace FirmDyn

variable {v : Icc (0 : ℝ) K →ᵇ ℝ} [Nonempty (Icc (0 : ℝ) K)] (h : FirmDyn f c f' c' p δ β K)
  (hv : bellman h.adj.h43 h.adj.h44 v = v)
include h hv

/-- `v(x) = pf(x) − c(g(x) − (1 − δ)x) + βv(g(x))`. -/
theorem v_eq (x : Icc (0 : ℝ) K) :
    v x = obj (adjF f c p δ K) β v (x, argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) x) := by
  obtain ⟨-, hUA, -⟩ := ex_5_9b h.adj hv
  have e := bellman_apply h.adj.h43 h.adj.h44 v x
  rw [hv] at e
  rw [e]
  exact (hUA.argmaxFn_mem x).2.symm

omit [Nonempty (Icc (0 : ℝ) K)] in
/-- Every choice does at most as well as `v`. -/
theorem obj_le (x y : Icc (0 : ℝ) K) : obj (adjF f c p δ K) β v (x, y) ≤ v x := by
  have e := bellman_apply h.adj.h43 h.adj.h44 v x
  rw [hv] at e
  rw [e]
  exact le_maxValue (continuousOn_obj h.adj.h44 v.continuous) (h.adj.h43.compact _)
    (mem_fullΓ x y)

omit h hv in
theorem fpol_mem {k : ℝ} (hk : k ∈ Icc 0 K) : fpol f c p δ β K v k ∈ Icc 0 K := by
  rw [fpol_of_mem v hk]; exact Subtype.mem _

theorem continuousOn_fpol : ContinuousOn (fpol f c p δ β K v) (Icc 0 K) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (Icc (0 : ℝ) K).domRestrict (fpol f c p δ β K v) =
      fun k => (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 := by
    funext k
    simp only [Set.domRestrict_apply]
    rw [fpol_of_mem v k.2]
  rw [e]
  exact continuous_subtype_val.comp (ex_5_9b h.adj hv).2.2

theorem monotoneOn_fpol : MonotoneOn (fpol f c p δ β K v) (Icc 0 K) := fun k hk k' hk' hkk' => by
  rw [fpol_of_mem v hk, fpol_of_mem v hk']
  exact ex_5_9b_mono h.adj hv (show (⟨k, hk⟩ : Icc (0 : ℝ) K) ≤ ⟨k', hk'⟩ from hkk')

/-- **Investing at `k = 0` pays**: `g(0) > 0`. If `g(0) = 0`, then `v(0) = 0` and
`βpf(ε) ≤ β[v(ε) − v(0)] ≤ c(ε)` for small `ε`, but `f(ε)/ε ≥ f'(ε) → ∞` while `c(ε)/ε → c'(0)`. -/
theorem fpol_zero_pos : 0 < fpol f c p δ β K v 0 := by
  have hK := h.adj.K_pos
  have hβ := h.adj.β_pos
  have hp := h.adj.p_pos
  have h0 : (0 : ℝ) ∈ Icc 0 K := ⟨le_rfl, hK.le⟩
  rw [fpol_of_mem v h0]
  by_contra hle
  push Not at hle
  set z0 : Icc (0 : ℝ) K := ⟨0, h0⟩
  have hg0 : argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) z0 = z0 :=
    Subtype.ext (le_antisymm hle (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) z0).2.1)
  have hv0 : v z0 = 0 := by
    have := h.v_eq hv z0
    rw [hg0] at this
    simp only [obj, adjF, z0, mul_zero, sub_zero, h.f_zero, h.c_zero] at this
    nlinarith [h.adj.β_lt]
  have hbound : ∀ ε, 0 < ε → ε ≤ K → β * p * f ε ≤ c ε := fun ε hε hεK => by
    set zε : Icc (0 : ℝ) K := ⟨ε, hε.le, hεK⟩
    have hA := h.obj_le hv z0 zε
    have hB := h.obj_le hv zε z0
    have hc : c (0 - (1 - δ) * ε) ≤ 0 := by
      have := h.c_mono (show 0 - (1 - δ) * ε ≤ 0 by nlinarith [h.adj.δ_lt])
      rwa [h.c_zero] at this
    simp only [obj, adjF, z0, zε, h.f_zero, mul_zero, sub_zero, hv0] at hA hB
    have hB' := mul_le_mul_of_nonneg_left hB hβ.le
    nlinarith
  have htan : ∀ ε, 0 < ε → ε ≤ K → ε * f' ε ≤ f ε := fun ε hε hεK => by
    have := tangent_le h.adj.f_concave.concaveOn (a := ε) (b := 0) ⟨hε.le, hεK⟩ h0
      (h.f_deriv ε hε)
    rw [h.f_zero] at this
    linarith
  have hslope := (h.c_deriv 0).tendsto_slope_zero_right
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε⁻¹ • (c (0 + ε) - c 0) < c' 0 + 1 :=
    hslope.eventually (gt_mem_nhds (by linarith))
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (c' 0 + 1) / (β * p) < f' ε :=
    h.inada.eventually (eventually_gt_atTop _)
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 K := Ioo_mem_nhdsGT hK
  obtain ⟨ε, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  simp only [zero_add, h.c_zero, sub_zero, smul_eq_mul] at h1
  have hε := h3.1
  have h1' : c ε < (c' 0 + 1) * ε := by
    rw [inv_mul_lt_iff₀ hε] at h1; linarith
  rw [div_lt_iff₀ (by positivity)] at h2
  have := hbound ε hε h3.2.le
  have := htan ε hε h3.2.le
  have h4 : (c' 0 + 1) * ε < β * p * (ε * f' ε) := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ β * p)
  linarith

/-- **The upper end is not a steady state**: `g(K) < K`. Otherwise, comparing `y = K − ε` at
`K` and `y = K` at `K − ε`, `φ(ε) = β[p(f(K) − f(K − ε)) + c(δK + (1 − δ)ε) − c(δK)]
− [c(δK) − c(δK − ε)] ≥ 0`, while `φ(0) = 0` and `φ'(0) = βpf'(K) − c'(δK)(1 − β(1 − δ)) < 0`. -/
theorem fpol_K_lt : fpol f c p δ β K v K < K := by
  have hK := h.adj.K_pos
  have hβ := h.adj.β_pos
  have hK1 : K ∈ Icc 0 K := ⟨hK.le, le_rfl⟩
  rw [fpol_of_mem v hK1]
  by_contra hle
  push Not at hle
  set zK : Icc (0 : ℝ) K := ⟨K, hK1⟩
  have hgK : argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) zK = zK :=
    Subtype.ext (le_antisymm (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) zK).2.2 hle)
  have hvK := h.v_eq hv zK
  rw [hgK] at hvK
  simp only [obj, adjF, zK] at hvK
  rw [show K - (1 - δ) * K = δ * K by ring] at hvK
  set φ : ℝ → ℝ := fun ε => β * (p * (f K - f (K - ε)) + c (δ * K + (1 - δ) * ε) - c (δ * K)) -
    (c (δ * K) - c (δ * K - ε))
  have hφ : ∀ ε, 0 < ε → ε ≤ K → 0 ≤ φ ε := fun ε hε hεK => by
    set zε : Icc (0 : ℝ) K := ⟨K - ε, by linarith, by linarith⟩
    have hA := h.obj_le hv zK zε
    have hB := h.obj_le hv zε zK
    simp only [obj, adjF, zK, zε] at hA hB
    rw [show K - ε - (1 - δ) * K = δ * K - ε by ring] at hA
    rw [show K - (1 - δ) * (K - ε) = δ * K + (1 - δ) * ε by ring] at hB
    have hB' := mul_le_mul_of_nonneg_left hB hβ.le
    simp only [φ]
    nlinarith
  -- `φ'(0) < 0`
  have hf1 : HasDerivAt (fun ε => f (K - ε)) (-f' K) 0 :=
    HasDerivAt.comp_const_sub K 0 (by rw [sub_zero]; exact h.f_deriv K hK)
  have hc2 : HasDerivAt (fun ε => c (δ * K - ε)) (-c' (δ * K)) 0 :=
    HasDerivAt.comp_const_sub (δ * K) 0 (by rw [sub_zero]; exact h.c_deriv _)
  have hc1 : HasDerivAt (fun ε => c (δ * K + (1 - δ) * ε)) (c' (δ * K) * (1 - δ)) 0 := by
    have hin : HasDerivAt (fun ε : ℝ => δ * K + (1 - δ) * ε) (1 - δ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 - δ)).const_add (δ * K)
    have := (h.c_deriv (δ * K + (1 - δ) * 0)).comp 0 hin
    simpa [Function.comp_def] using this
  have hφ' : HasDerivAt φ (β * (p * (0 - -f' K) + c' (δ * K) * (1 - δ) - 0) -
      (0 - -c' (δ * K))) 0 :=
    ((((hasDerivAt_const 0 (f K)).sub hf1).const_mul p).add hc1 |>.sub
      (hasDerivAt_const 0 (c (δ * K))) |>.const_mul β).sub
      ((hasDerivAt_const 0 (c (δ * K))).sub hc2)
  have hd : β * (p * (0 - -f' K) + c' (δ * K) * (1 - δ) - 0) - (0 - -c' (δ * K)) < 0 := by
    have := h.K_big
    nlinarith
  have hφ0 : φ 0 = 0 := by simp [φ]
  have e1 := hφ'.tendsto_slope_zero_right.eventually (gt_mem_nhds hd)
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 K := Ioo_mem_nhdsGT hK
  obtain ⟨ε, h1, h2⟩ := (e1.and e2).exists
  simp only [zero_add, hφ0, sub_zero, smul_eq_mul] at h1
  have := hφ ε h2.1 h2.2.le
  have : 0 ≤ ε⁻¹ * φ ε := mul_nonneg (inv_nonneg.2 h2.1.le) this
  linarith

/-- An interior steady state satisfies `c'(δk)(1 − β(1 − δ)) = βpf'(k)`. -/
theorem steady_eq {k : ℝ} (hk : k ∈ Ioo 0 K) (hfix : fpol f c p δ β K v k = k) :
    c' (δ * k) * (1 - β * (1 - δ)) = β * p * f' k := by
  have hkI : k ∈ Icc 0 K := ⟨hk.1.le, hk.2.le⟩
  rw [fpol_of_mem v hkI] at hfix
  exact ex_5_9b_steady h.adj hv (k := ⟨k, hkI⟩) (Subtype.ext hfix) hk (h.f_deriv k hk.1)
    (h.c_deriv _)

end FirmDyn

/-- **Exercise 6.8a: at most one stationary capital stock.** `k ↦ c'(δk)(1 − β(1 − δ))` rises
and `k ↦ βpf'(k)` falls. -/
theorem ex_6_8a_unique (h : FirmDyn f c f' c' p δ β K) {k₁ k₂ : ℝ} (hk₁ : k₁ ∈ Ioc 0 K)
    (hk₂ : k₂ ∈ Ioc 0 K) (e₁ : c' (δ * k₁) * (1 - β * (1 - δ)) = β * p * f' k₁)
    (e₂ : c' (δ * k₂) * (1 - β * (1 - δ)) = β * p * f' k₂) : k₁ = k₂ := by
  have hβp : 0 < β * p := mul_pos h.adj.β_pos h.adj.p_pos
  have h1 : 0 < 1 - β * (1 - δ) := by nlinarith [h.adj.β_lt, h.adj.δ_pos, h.adj.δ_lt]
  have key : ∀ a b : ℝ, a ∈ Ioc 0 K → b ∈ Ioc 0 K → a < b →
      c' (δ * a) * (1 - β * (1 - δ)) = β * p * f' a →
      c' (δ * b) * (1 - β * (1 - δ)) = β * p * f' b → False := fun a b ha hb hab ea eb => by
    have hf := deriv_lt_of_strictConcave h.adj.f_concave ⟨ha.1.le, ha.2⟩ ⟨hb.1.le, hb.2⟩ hab
      (h.f_deriv a ha.1) (h.f_deriv b hb.1)
    have hc := deriv_lt_of_strictConcave h.c_strict.neg (mem_univ (δ * a)) (mem_univ (δ * b))
      (mul_lt_mul_of_pos_left hab h.adj.δ_pos) (h.c_deriv _).neg (h.c_deriv _).neg
    nlinarith
  rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · exact (key _ _ hk₁ hk₂ hlt e₁ e₂).elim
  · exact heq
  · exact (key _ _ hk₂ hk₁ hgt e₂ e₁).elim

/-- **Exercise 6.8a–b.** The policy has exactly one fixed point `k̄` in `[0, K]`; it is interior
and solves `c'(δk̄)(1 − β(1 − δ)) = βpf'(k̄)`; and from every `k₀ ∈ [0, K]` the capital stock
converges monotonically to `k̄`. -/
theorem ex_6_8 [Nonempty (Icc (0 : ℝ) K)] (h : FirmDyn f c f' c' p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ} (hv : bellman h.adj.h43 h.adj.h44 v = v) :
    ∃ kbar ∈ Ioo 0 K, c' (δ * kbar) * (1 - β * (1 - δ)) = β * p * f' kbar ∧
      (∀ k ∈ Icc 0 K, fpol f c p δ β K v k = k ↔ k = kbar) ∧
      ∀ k₀ ∈ Icc 0 K,
        (Monotone (fun t => (fpol f c p δ β K v)^[t] k₀) ∨
          Antitone (fun t => (fpol f c p δ β K v)^[t] k₀)) ∧
        Tendsto (fun t => (fpol f c p δ β K v)^[t] k₀) atTop (𝓝 kbar) := by
  set g := fpol f c p δ β K v
  have hK := h.adj.K_pos
  have hgc := h.continuousOn_fpol hv
  have hφc : ContinuousOn (fun k => g k - k) (Icc 0 K) := hgc.sub continuousOn_id
  have hg0 := h.fpol_zero_pos hv
  have hgK := h.fpol_K_lt hv
  -- a fixed point is interior, so it solves the steady-state equation
  have hfix_int : ∀ k ∈ Icc 0 K, g k = k → k ∈ Ioo 0 K := fun k hk hgk => by
    refine ⟨lt_of_le_of_ne hk.1 fun he => ?_, lt_of_le_of_ne hk.2 fun he => ?_⟩
    · rw [← he] at hgk; linarith
    · rw [he] at hgk; linarith
  obtain ⟨kbar, hkbar, hφ⟩ := intermediate_value_Icc' hK.le hφc
    (show (0 : ℝ) ∈ Icc (g K - K) (g 0 - 0) from ⟨by linarith, by linarith⟩)
  have hfix : g kbar = kbar := by simp only at hφ; linarith
  have hkI := hfix_int kbar hkbar hfix
  have heq := h.steady_eq hv hkI hfix
  have hiff : ∀ k ∈ Icc 0 K, g k = k ↔ k = kbar := fun k hk => ⟨fun hgk => by
      have hki := hfix_int k hk hgk
      exact ex_6_8a_unique h ⟨hki.1, hki.2.le⟩ ⟨hkI.1, hkI.2.le⟩
        (h.steady_eq hv hki hgk) heq, fun he => he ▸ hfix⟩
  have hbelow : ∀ k ∈ Icc 0 K, k < kbar → k < g k := fun k hk hlt => by
    by_contra hle
    push Not at hle
    obtain ⟨k', hk', hφ'⟩ := intermediate_value_Icc' hk.1 (hφc.mono (Icc_subset_Icc le_rfl hk.2))
      (show (0 : ℝ) ∈ Icc (g k - k) (g 0 - 0) from ⟨by linarith, by linarith⟩)
    have hk'I : k' ∈ Icc 0 K := ⟨hk'.1, hk'.2.trans hk.2⟩
    have := (hiff k' hk'I).1 (by simp only at hφ'; linarith)
    linarith [hk'.2]
  have habove : ∀ k ∈ Icc 0 K, kbar < k → g k < k := fun k hk hlt => by
    by_contra hle
    push Not at hle
    obtain ⟨k', hk', hφ'⟩ := intermediate_value_Icc' hk.2 (hφc.mono (Icc_subset_Icc hk.1 le_rfl))
      (show (0 : ℝ) ∈ Icc (g K - K) (g k - k) from ⟨by linarith, by linarith⟩)
    have hk'I : k' ∈ Icc 0 K := ⟨hk.1.trans hk'.1, hk'.2⟩
    have := (hiff k' hk'I).1 (by simp only at hφ'; linarith)
    linarith [hk'.1]
  refine ⟨kbar, hkI, heq, hiff, fun k₀ hk₀ => ?_⟩
  exact orbit_tendsto_of_crossing hgc (h.monotoneOn_fpol hv)
    (fun k hk => FirmDyn.fpol_mem hk) hkbar hfix hbelow habove hk₀

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.LocalApproach

/-!
# The local implicit function `H` of §18.2 (7)

SLP §18.2, p. 549. Since `F₂* > 0`, the book applies the Implicit Function Theorem to get an open
interval `I ∋ k*` and a `C¹` function `H : I × I → ℝ` with `F[x, H(x, z), z] = 0` (§18.2 (7)),
`H(k*, k*) = k*`, and partial derivatives `H₁* = −F₁*/F₂* > 0`, `H₂* = −F₃*/F₂* > 0` at
`(k*, k*)`. The later proofs use `H` only through: (7); the uniqueness of the root near `k*`;
continuity; monotonicity in each argument; and, for every `m₁ > H₁*`, `m₂ > H₂*`, the bound
`|H(x, z) − H(x′, z′)| ≤ m₁|x − x′| + m₂|z − z′|` on a small square `I_ε × I_ε` (which the book
gets from the continuity of `H₁, H₂` and the mean value theorem). These properties are collected
in `LocalSolution`, and `exists_localSolution` constructs such an `H` directly: the middle
argument of `F` is solved by the intermediate value theorem, and the Lipschitz bounds come from
bounds on the partial derivatives of `F` near `(k*, k*, k*)`.

* `Jint p ρ = [p − ρ, p + ρ]`; `clampI` is the nearest-point map onto it.
* `abs_sub_le_of_hasDerivAt`, `mul_sub_le_of_hasDerivAt`: mean value inequalities.
* `root_sep`: if `∂_y G ≥ a > 0`, `|∂_x G| ≤ b₁`, `|∂_z G| ≤ b₃` on a cube and
  `G(x, y, z) = G(x′, y′, z′) = 0` there, then `a|y − y′| ≤ b₁|x − x′| + b₃|z − z′|`.
* `root_exists`: solvability of `G(x, ·, z) = 0` near `(p, p, p)`.
* `implicitRoot`: the root, chosen by `Classical.epsilon`, of `G(clamp x, ·, clamp z) = 0`.
* `LocalHyp.exists_cube`: bounds on `F₁, F₂, F₃` near `(k*, k*, k*)`.
* `LocalSolution`, `exists_localSolution` (**§18.2 (7)**).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- The closed interval `[p − ρ, p + ρ]`. -/
abbrev Jint (p ρ : ℝ) : Set ℝ := Icc (p - ρ) (p + ρ)

/-- Nearest-point map onto `[p − δ, p + δ]`. -/
noncomputable def clampI (p δ x : ℝ) : ℝ := max (p - δ) (min (p + δ) x)

/-- `clampI` maps into `[p − δ, p + δ]` when `δ ≥ 0`. -/
theorem clampI_mem {p δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : clampI p δ x ∈ Jint p δ :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- `clampI` is the identity on `[p − δ, p + δ]`. -/
theorem clampI_of_mem {p δ x : ℝ} (hx : x ∈ Jint p δ) : clampI p δ x = x := by
  simp only [clampI, min_eq_right hx.2, max_eq_right hx.1]

/-- `clampI` is `1`-Lipschitz. -/
theorem abs_clampI_sub_le (p δ x x' : ℝ) : |clampI p δ x - clampI p δ x'| ≤ |x - x'| := by
  simp only [clampI]
  rw [max_comm (p - δ), max_comm (p - δ)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

/-- Membership in a smaller interval. -/
theorem Jint_mono {p δ ρ x : ℝ} (h : δ ≤ ρ) (hx : x ∈ Jint p δ) : x ∈ Jint p ρ :=
  ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The centre lies in `[p − ρ, p + ρ]` for `ρ ≥ 0`. -/
theorem center_mem_Jint {p ρ : ℝ} (h : 0 ≤ ρ) : p ∈ Jint p ρ := ⟨by linarith, by linarith⟩

/-- `x ∈ [p − ρ, p + ρ] ↔ |x − p| ≤ ρ`. -/
theorem mem_Jint_iff {p ρ x : ℝ} : x ∈ Jint p ρ ↔ |x - p| ≤ ρ := by
  rw [abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### Mean value inequalities -/

/-- **Mean value inequality.** If `φ′ = φ'` with `|φ'| ≤ C` on an interval `s`, then
`|φ(v) − φ(u)| ≤ C |v − u|` for `u, v ∈ s`. -/
theorem abs_sub_le_of_hasDerivAt {φ φ' : ℝ → ℝ} {s : Set ℝ} {C u v : ℝ} (hs : Convex ℝ s)
    (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t) (hb : ∀ t ∈ s, |φ' t| ≤ C) (hu : u ∈ s)
    (hv : v ∈ s) : |φ v - φ u| ≤ C * |v - u| :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun t ht => (hφ t ht).hasDerivWithinAt)
    hb hu hv

/-- **Lower mean value inequality.** If `φ′ = φ' ≥ a` on a closed interval `s`, then
`a (v − u) ≤ φ(v) − φ(u)` for `u ≤ v` in `s`. -/
theorem mul_sub_le_of_hasDerivAt {φ φ' : ℝ → ℝ} {c d a u v : ℝ}
    (hφ : ∀ t ∈ Icc c d, HasDerivAt φ (φ' t) t) (hb : ∀ t ∈ Icc c d, a ≤ φ' t)
    (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (huv : u ≤ v) : a * (v - u) ≤ φ v - φ u := by
  refine (convex_Icc c d).mul_sub_le_image_sub_of_le_deriv
    (fun t ht => (hφ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hφ t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => ?_) u hu v hv huv
  rw [(hφ t (interior_subset ht)).deriv]
  exact hb t (interior_subset ht)

/-! ### Roots of `G(x, ·, z) = 0` -/

/-- **Separation of roots.** Let `G` have partial derivatives `G₁, G₂, G₃` everywhere, with
`G₂ ≥ a`, `|G₁| ≤ b₁`, `|G₃| ≤ b₃` on the cube `J³`, `J = [p − ρ, p + ρ]`. If `G(x, y, z) = 0` and
`G(x′, y′, z′) = 0` with all coordinates in `J`, then `a|y − y′| ≤ b₁|x − x′| + b₃|z − z′|`. -/
theorem root_sep {G G1 G2 G3 : ℝ → ℝ → ℝ → ℝ} {p ρ a b1 b3 : ℝ}
    (h1 : ∀ x y z, HasDerivAt (fun x => G x y z) (G1 x y z) x)
    (h2 : ∀ x y z, HasDerivAt (fun y => G x y z) (G2 x y z) y)
    (h3 : ∀ x y z, HasDerivAt (fun z => G x y z) (G3 x y z) z)
    (ha : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, a ≤ G2 x y z)
    (hb1 : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, |G1 x y z| ≤ b1)
    (hb3 : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, |G3 x y z| ≤ b3)
    {x x' y y' z z' : ℝ} (hx : x ∈ Jint p ρ) (hx' : x' ∈ Jint p ρ) (hy : y ∈ Jint p ρ)
    (hy' : y' ∈ Jint p ρ) (hz : z ∈ Jint p ρ) (hz' : z' ∈ Jint p ρ)
    (h0 : G x y z = 0) (h0' : G x' y' z' = 0) :
    a * |y - y'| ≤ b1 * |x - x'| + b3 * |z - z'| := by
  have e1 : |G x' y' z' - G x y' z'| ≤ b1 * |x' - x| :=
    abs_sub_le_of_hasDerivAt (φ := fun t => G t y' z') (convex_Icc _ _)
      (fun t _ => h1 t y' z') (fun t ht => hb1 t ht y' hy' z' hz') hx hx'
  have e3 : |G x y' z' - G x y' z| ≤ b3 * |z' - z| :=
    abs_sub_le_of_hasDerivAt (φ := fun t => G x y' t) (convex_Icc _ _)
      (fun t _ => h3 x y' t) (fun t ht => hb3 x hx y' hy' t ht) hz hz'
  rw [abs_sub_comm x' x] at e1
  rw [abs_sub_comm z' z] at e3
  have e1' := abs_le.1 e1
  have e3' := abs_le.1 e3
  rcases le_total y' y with hle | hle
  · have e2 := mul_sub_le_of_hasDerivAt (φ := fun t => G x t z) (fun t _ => h2 x t z)
      (fun t ht => ha x hx t ht z hz) hy' hy hle
    rw [abs_of_nonneg (by linarith : 0 ≤ y - y')]
    linarith
  · have e2 := mul_sub_le_of_hasDerivAt (φ := fun t => G x t z) (fun t _ => h2 x t z)
      (fun t ht => ha x hx t ht z hz) hy hy' hle
    rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ y' - y)]
    linarith

/-- **Existence of a root.** Under the hypotheses of `root_sep`, with `G(p, p, p) = 0`, `a > 0`,
`0 < r ≤ ρ`, `0 ≤ δ ≤ ρ` and `(b₁ + b₃)δ < a r`: for `x, z ∈ [p − δ, p + δ]` there is
`y ∈ [p − r, p + r]` with `G(x, y, z) = 0`. -/
theorem root_exists {G G1 G2 G3 : ℝ → ℝ → ℝ → ℝ} {p ρ a b1 b3 r δ : ℝ}
    (h1 : ∀ x y z, HasDerivAt (fun x => G x y z) (G1 x y z) x)
    (h2 : ∀ x y z, HasDerivAt (fun y => G x y z) (G2 x y z) y)
    (h3 : ∀ x y z, HasDerivAt (fun z => G x y z) (G3 x y z) z)
    (ha : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, a ≤ G2 x y z)
    (hb1 : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, |G1 x y z| ≤ b1)
    (hb3 : ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, |G3 x y z| ≤ b3)
    (hG0 : G p p p = 0) (hr : 0 < r) (hrρ : r ≤ ρ) (hδρ : δ ≤ ρ)
    (hsmall : (b1 + b3) * δ < a * r) {x z : ℝ} (hx : x ∈ Jint p δ) (hz : z ∈ Jint p δ) :
    ∃ y ∈ Jint p r, G x y z = 0 := by
  have hρ : 0 ≤ ρ := by linarith
  have hp := center_mem_Jint (p := p) hρ
  have hpr : p + r ∈ Jint p ρ := ⟨by linarith, by linarith⟩
  have hmr : p - r ∈ Jint p ρ := ⟨by linarith, by linarith⟩
  have hxρ := Jint_mono hδρ hx
  have hzρ := Jint_mono hδρ hz
  have hb1n : 0 ≤ b1 := (abs_nonneg _).trans (hb1 p hp p hp p hp)
  have hb3n : 0 ≤ b3 := (abs_nonneg _).trans (hb3 p hp p hp p hp)
  have hxd : |x - p| ≤ δ := mem_Jint_iff.1 hx
  have hzd : |z - p| ≤ δ := mem_Jint_iff.1 hz
  -- bounds at `y = p ± r`
  have hup : a * r ≤ G p (p + r) p - G p p p := by
    have := mul_sub_le_of_hasDerivAt (φ := fun t => G p t p) (fun t _ => h2 p t p)
      (fun t ht => ha p hp t ht p hp) hp hpr (by linarith)
    simpa using this
  have hdn : a * r ≤ G p p p - G p (p - r) p := by
    have := mul_sub_le_of_hasDerivAt (φ := fun t => G p t p) (fun t _ => h2 p t p)
      (fun t ht => ha p hp t ht p hp) hmr hp (by linarith)
    simpa using this
  have hmove : ∀ w ∈ Jint p ρ, |G x w z - G p w p| ≤ (b1 + b3) * δ := by
    intro w hw
    have e1 : |G x w z - G p w z| ≤ b1 * |x - p| :=
      abs_sub_le_of_hasDerivAt (φ := fun t => G t w z) (convex_Icc _ _)
        (fun t _ => h1 t w z) (fun t ht => hb1 t ht w hw z hzρ) hp hxρ
    have e3 : |G p w z - G p w p| ≤ b3 * |z - p| :=
      abs_sub_le_of_hasDerivAt (φ := fun t => G p w t) (convex_Icc _ _)
        (fun t _ => h3 p w t) (fun t ht => hb3 p hp w hw t ht) hp hzρ
    calc |G x w z - G p w p| = |(G x w z - G p w z) + (G p w z - G p w p)| := by ring_nf
      _ ≤ |G x w z - G p w z| + |G p w z - G p w p| := abs_add_le _ _
      _ ≤ b1 * δ + b3 * δ := add_le_add ((e1.trans (mul_le_mul_of_nonneg_left hxd hb1n)))
          (e3.trans (mul_le_mul_of_nonneg_left hzd hb3n))
      _ = (b1 + b3) * δ := by ring
  have hpos : 0 < G x (p + r) z := by
    have := (abs_le.1 (hmove _ hpr)).1
    linarith
  have hneg : G x (p - r) z < 0 := by
    have := (abs_le.1 (hmove _ hmr)).2
    linarith
  have hcont : ContinuousOn (fun y => G x y z) (Icc (p - r) (p + r)) :=
    fun y _ => (h2 x y z).continuousAt.continuousWithinAt
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc (by linarith : p - r ≤ p + r) hcont
    ⟨hneg.le, hpos.le⟩
  exact ⟨y, hy, hy0⟩

/-- The implicit root: a `y ∈ [p − r, p + r]` with `G(clamp x, y, clamp z) = 0`, chosen by
`Classical.epsilon` (clamping to `[p − δ, p + δ]`). -/
noncomputable def implicitRoot (G : ℝ → ℝ → ℝ → ℝ) (p r δ x z : ℝ) : ℝ :=
  Classical.epsilon fun y => y ∈ Jint p r ∧ G (clampI p δ x) y (clampI p δ z) = 0

/-! ### Bounds on the partial derivatives of `F` near the steady state -/

/-- From an eventual property at `(p, p, p)` to a property on a cube `J³`. -/
theorem exists_cube_of_eventually {P : ℝ × ℝ × ℝ → Prop} {p : ℝ}
    (h : ∀ᶠ q in 𝓝 ((p, p, p) : ℝ × ℝ × ℝ), P q) :
    ∃ ρ > 0, ∀ x ∈ Jint p ρ, ∀ y ∈ Jint p ρ, ∀ z ∈ Jint p ρ, P (x, y, z) := by
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨ε / 2, by linarith, fun x hx y hy z hz => hP ?_⟩
  have hx' := mem_Jint_iff.1 hx
  have hy' := mem_Jint_iff.1 hy
  have hz' := mem_Jint_iff.1 hz
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt (by linarith) (max_lt (by linarith) (by linarith))

/-- **Bounds near `(k*, k*, k*)`.** For `a < F₂*`, `b₁ > −F₁*`, `b₃ > −F₃*` there is a cube on
which `F₂ > a`, `|F₁| < b₁`, `|F₃| < b₃`, `F₁ < 0` and `F₃ < 0`. -/
theorem LocalHyp.exists_cube {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) {a b1 b3 : ℝ}
    (ha : a < F2s β θ U f ks) (hb1 : -F1s β θ U f ks < b1) (hb3 : -F3s U θ f ks < b3) :
    ∃ ρ > 0, ∀ x ∈ Jint ks ρ, ∀ y ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ,
      a < F2f β θ U f x y z ∧ |F1f θ U f x y| < b1 ∧ |F3f β θ U f y z| < b3 ∧
        F1f θ U f x y < 0 ∧ F3f β θ U f y z < 0 := by
  have hU1 := continuous_deriv_of_C2 L.U_contDiff
  have hU2 := continuous_deriv2_of_C2 L.U_contDiff
  have hf0 := (differentiable_of_C2 L.f_contDiff).continuous
  have hf1 := continuous_deriv_of_C2 L.f_contDiff
  have hf2 := continuous_deriv2_of_C2 L.f_contDiff
  have c1 : Continuous fun q : ℝ × ℝ × ℝ => F1f θ U f q.1 q.2.1 := by
    simp only [F1f, psi, dpsi]
    fun_prop
  have c2 : Continuous fun q : ℝ × ℝ × ℝ => F2f β θ U f q.1 q.2.1 q.2.2 := by
    simp only [F2f, psi, dpsi]
    fun_prop
  have c3 : Continuous fun q : ℝ × ℝ × ℝ => F3f β θ U f q.2.1 q.2.2 := by
    simp only [F3f, psi]
    fun_prop
  have v1 : F1f θ U f ks ks = F1s β θ U f ks := F1f_star L.beta_pos L.euler
  have v2 : F2f β θ U f ks ks ks = F2s β θ U f ks := F2f_star L.beta_pos L.euler
  have v3 : F3f β θ U f ks ks = F3s U θ f ks := F3f_star L.euler
  have hF1 := L.F1s_neg
  have hF3 := L.F3s_neg
  have e2' : ∀ᶠ q in 𝓝 ((ks, ks, ks) : ℝ × ℝ × ℝ), a < F2f β θ U f q.1 q.2.1 q.2.2 :=
    c2.continuousAt.eventually (lt_mem_nhds (by
      change a < F2f β θ U f ks ks ks
      rw [v2]
      exact ha))
  have e1 : ∀ᶠ q in 𝓝 ((ks, ks, ks) : ℝ × ℝ × ℝ), |F1f θ U f q.1 q.2.1| < b1 :=
    (continuous_abs.comp c1).continuousAt.eventually
      (gt_mem_nhds (by simp only [Function.comp_apply]; rw [v1, abs_of_neg hF1]; exact hb1))
  have e3 : ∀ᶠ q in 𝓝 ((ks, ks, ks) : ℝ × ℝ × ℝ), |F3f β θ U f q.2.1 q.2.2| < b3 :=
    (continuous_abs.comp c3).continuousAt.eventually
      (gt_mem_nhds (by simp only [Function.comp_apply]; rw [v3, abs_of_neg hF3]; exact hb3))
  have e4 : ∀ᶠ q in 𝓝 ((ks, ks, ks) : ℝ × ℝ × ℝ), F1f θ U f q.1 q.2.1 < 0 :=
    c1.continuousAt.eventually (gt_mem_nhds (by
      change F1f θ U f ks ks < 0
      rw [v1]
      exact hF1))
  have e5 : ∀ᶠ q in 𝓝 ((ks, ks, ks) : ℝ × ℝ × ℝ), F3f β θ U f q.2.1 q.2.2 < 0 :=
    c3.continuousAt.eventually (gt_mem_nhds (by
      change F3f β θ U f ks ks < 0
      rw [v3]
      exact hF3))
  obtain ⟨ρ, hρ, hP⟩ := exists_cube_of_eventually (e2'.and (e1.and (e3.and (e4.and e5))))
  exact ⟨ρ, hρ, fun x hx y hy z hz => hP x hx y hy z hz⟩

/-! ### The local solution `H` -/

/-- **The local solution `H` of §18.2 (7)** on `I = [k* − ε₀, k* + ε₀]`, with the properties the
book derives from the Implicit Function Theorem: (7), local uniqueness of the root,
`H(k*, k*) = k*`, continuity, a Lipschitz bound, strict monotonicity in each argument, and
Lipschitz constants arbitrarily close to `H₁* = −F₁*/F₂*` and `H₂* = −F₃*/F₂*` near `(k*, k*)`. -/
structure LocalSolution (β θ : ℝ) (U f : ℝ → ℝ) (ks ε₀ : ℝ) (H : ℝ → ℝ → ℝ) : Prop where
  eps_pos : 0 < ε₀
  eq7 : ∀ x ∈ Jint ks ε₀, ∀ z ∈ Jint ks ε₀, Feq β θ U f x (H x z) z = 0
  unique : ∀ x ∈ Jint ks ε₀, ∀ z ∈ Jint ks ε₀, ∀ y ∈ Jint ks ε₀, Feq β θ U f x y z = 0 →
    y = H x z
  center : H ks ks = ks
  continuous : Continuous fun q : ℝ × ℝ => H q.1 q.2
  lipschitz : ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧ ∀ x x' z z' : ℝ,
    |H x z - H x' z'| ≤ B₁ * |x - x'| + B₂ * |z - z'|
  strictMono_left : ∀ x ∈ Jint ks ε₀, ∀ x' ∈ Jint ks ε₀, ∀ z ∈ Jint ks ε₀, x < x' →
    H x z < H x' z
  strictMono_right : ∀ x ∈ Jint ks ε₀, ∀ z ∈ Jint ks ε₀, ∀ z' ∈ Jint ks ε₀, z < z' →
    H x z < H x z'
  lip_near : ∀ m₁ m₂ : ℝ, -F1s β θ U f ks / F2s β θ U f ks < m₁ →
    -F3s U θ f ks / F2s β θ U f ks < m₂ → ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ x ∈ Jint ks ε, ∀ x' ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
        |H x z - H x' z'| ≤ m₁ * |x - x'| + m₂ * |z - z'|

/-- **§18.2 (7): existence of the local solution `H`.** Under `LocalHyp` (Assumption 18.1 near
the steady state, with `U″(c*) < 0` and `f″(k*) < 0`) there are `ε₀ > 0` and `H` with all the
properties of `LocalSolution`. -/
theorem exists_localSolution {β θ ks : ℝ} {U f : ℝ → ℝ} (L : LocalHyp β θ U f ks) :
    ∃ ε₀ H, LocalSolution β θ U f ks ε₀ H := by
  set F1 := F1s β θ U f ks with hF1
  set F2 := F2s β θ U f ks with hF2
  set F3 := F3s U θ f ks with hF3
  have hF1n : F1 < 0 := L.F1s_neg
  have hF2p : 0 < F2 := L.F2s_pos
  have hF3n : F3 < 0 := L.F3s_neg
  have hd1 := hasDerivAt_Feq_x (β := β) (θ := θ) L.U_contDiff L.f_contDiff
  have hd2 := hasDerivAt_Feq_y (β := β) (θ := θ) L.U_contDiff L.f_contDiff
  have hd3 := hasDerivAt_Feq_z (β := β) (θ := θ) (f := f) L.U_contDiff
  have hG0 : Feq β θ U f ks ks ks = 0 := by
    rw [Feq_diag, L.euler, sub_self, mul_zero]
  -- the big cube
  set a0 := F2 / 2 with ha0
  set b10 := -F1 + 1 with hb10
  set b30 := -F3 + 1 with hb30
  have ha0p : 0 < a0 := by linarith
  have hb10p : 0 < b10 := by linarith
  have hb30p : 0 < b30 := by linarith
  obtain ⟨ρ, hρ, hcube⟩ := L.exists_cube (a := a0) (b1 := b10) (b3 := b30) (by linarith)
    (by linarith) (by linarith)
  have hA : ∀ x ∈ Jint ks ρ, ∀ y ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ, a0 ≤ F2f β θ U f x y z :=
    fun x hx y hy z hz => (hcube x hx y hy z hz).1.le
  have hB1 : ∀ x ∈ Jint ks ρ, ∀ y ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ,
      |(fun x y (_ : ℝ) => F1f θ U f x y) x y z| ≤ b10 :=
    fun x hx y hy z hz => (hcube x hx y hy z hz).2.1.le
  have hB3 : ∀ x ∈ Jint ks ρ, ∀ y ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ,
      |(fun (_ : ℝ) y z => F3f β θ U f y z) x y z| ≤ b30 :=
    fun x hx y hy z hz => (hcube x hx y hy z hz).2.2.1.le
  set δ := min ρ (a0 * ρ / (2 * (b10 + b30))) with hδ
  have hδp : 0 < δ := lt_min hρ (div_pos (mul_pos ha0p hρ) (by linarith))
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hsmall : (b10 + b30) * δ < a0 * ρ := by
    have h1 : δ ≤ a0 * ρ / (2 * (b10 + b30)) := min_le_right _ _
    have h2 : (b10 + b30) * δ ≤ a0 * ρ / 2 := by
      calc (b10 + b30) * δ ≤ (b10 + b30) * (a0 * ρ / (2 * (b10 + b30))) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = a0 * ρ / 2 := by field_simp
    linarith [mul_pos ha0p hρ]
  set H := implicitRoot (Feq β θ U f) ks ρ δ with hH
  have hspec : ∀ x z, H x z ∈ Jint ks ρ ∧
      Feq β θ U f (clampI ks δ x) (H x z) (clampI ks δ z) = 0 := fun x z =>
    Classical.epsilon_spec (root_exists (G := Feq β θ U f) hd1 hd2 hd3 hA hB1 hB3 hG0 hρ le_rfl
      hδρ hsmall (clampI_mem hδp.le x) (clampI_mem hδp.le z))
  have hmemρ : ∀ x, clampI ks δ x ∈ Jint ks ρ := fun x => Jint_mono hδρ (clampI_mem hδp.le x)
  -- global Lipschitz bound
  have hglob : ∀ x x' z z', a0 * |H x z - H x' z'| ≤
      b10 * |x - x'| + b30 * |z - z'| := by
    intro x x' z z'
    have := root_sep (G := Feq β θ U f) hd1 hd2 hd3 hA hB1 hB3 (hmemρ x) (hmemρ x')
      (hspec x z).1 (hspec x' z').1 (hmemρ z) (hmemρ z') (hspec x z).2 (hspec x' z').2
    refine this.trans (add_le_add (mul_le_mul_of_nonneg_left (abs_clampI_sub_le _ _ _ _)
      hb10p.le) (mul_le_mul_of_nonneg_left (abs_clampI_sub_le _ _ _ _) hb30p.le))
  have hglob' : ∀ x x' z z', |H x z - H x' z'| ≤
      b10 / a0 * |x - x'| + b30 / a0 * |z - z'| := by
    intro x x' z z'
    have := hglob x x' z z'
    rw [show b10 / a0 * |x - x'| + b30 / a0 * |z - z'| =
      (b10 * |x - x'| + b30 * |z - z'|) / a0 by ring, le_div_iff₀ ha0p]
    linarith
  have heq7 : ∀ x ∈ Jint ks δ, ∀ z ∈ Jint ks δ, Feq β θ U f x (H x z) z = 0 := by
    intro x hx z hz
    have := (hspec x z).2
    rwa [clampI_of_mem hx, clampI_of_mem hz] at this
  have huniq : ∀ x ∈ Jint ks δ, ∀ z ∈ Jint ks δ, ∀ y ∈ Jint ks ρ, Feq β θ U f x y z = 0 →
      y = H x z := by
    intro x hx z hz y hy hy0
    have hxρ := Jint_mono hδρ hx
    have hzρ := Jint_mono hδρ hz
    have := root_sep (G := Feq β θ U f) hd1 hd2 hd3 hA hB1 hB3 hxρ hxρ hy (hspec x z).1 hzρ
      hzρ hy0 (heq7 x hx z hz)
    simp only [sub_self, abs_zero, mul_zero, add_zero] at this
    have h0 : |y - H x z| ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos ha0p hc
      linarith
    exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)
  have hks := center_mem_Jint (p := ks) hδp.le
  have hcenter : H ks ks = ks :=
    (huniq ks hks ks hks ks (center_mem_Jint hρ.le) hG0).symm
  -- strict monotonicity of `F` on the big cube
  have hFy : ∀ x ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ, StrictMonoOn (fun y => Feq β θ U f x y z)
      (Jint ks ρ) := by
    intro x hx z hz
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun y _ => (hd2 x y z).continuousAt.continuousWithinAt) fun y hy => ?_
    rw [(hd2 x y z).deriv]
    exact ha0p.trans (hcube x hx y (interior_subset hy) z hz).1
  have hFx : ∀ y ∈ Jint ks ρ, ∀ z ∈ Jint ks ρ, StrictAntiOn (fun x => Feq β θ U f x y z)
      (Jint ks ρ) := by
    intro y hy z hz
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun x _ => (hd1 x y z).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [(hd1 x y z).deriv]
    exact (hcube x (interior_subset hx) y hy z hz).2.2.2.1
  have hFz : ∀ x ∈ Jint ks ρ, ∀ y ∈ Jint ks ρ, StrictAntiOn (fun z => Feq β θ U f x y z)
      (Jint ks ρ) := by
    intro x hx y hy
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun z _ => (hd3 x y z).continuousAt.continuousWithinAt) fun z hz => ?_
    rw [(hd3 x y z).deriv]
    exact (hcube x hx y hy z (interior_subset hz)).2.2.2.2
  refine ⟨δ, H, ⟨hδp, heq7, fun x hx z hz y hy hy0 => huniq x hx z hz y (Jint_mono hδρ hy) hy0,
    hcenter, ?_, ⟨b10 / a0, b30 / a0, (div_pos hb10p ha0p).le, (div_pos hb30p ha0p).le, hglob'⟩,
    ?_, ?_, ?_⟩⟩
  · -- continuity
    have hB : 0 ≤ b10 / a0 + b30 / a0 := by positivity
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (b10 / a0 + b30 / a0))
      fun q q' => ?_).continuous
    rw [Real.coe_toNNReal _ hB, Real.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    refine (hglob' _ _ _ _).trans ?_
    have h1 := mul_le_mul_of_nonneg_left (le_max_left |q.1 - q'.1| |q.2 - q'.2|)
      (div_pos hb10p ha0p).le
    have h2 := mul_le_mul_of_nonneg_left (le_max_right |q.1 - q'.1| |q.2 - q'.2|)
      (div_pos hb30p ha0p).le
    linarith
  · -- strictly increasing in `x`
    intro x hx x' hx' z hz hxx
    have hy := (hspec x z).1
    have hy' := (hspec x' z).1
    have h1 : Feq β θ U f x' (H x z) z < Feq β θ U f x (H x z) z :=
      hFx _ hy z (Jint_mono hδρ hz) (Jint_mono hδρ hx) (Jint_mono hδρ hx') hxx
    rw [heq7 x hx z hz, ← heq7 x' hx' z hz] at h1
    exact (hFy x' (Jint_mono hδρ hx') z (Jint_mono hδρ hz)).lt_iff_lt hy hy' |>.1 h1
  · -- strictly increasing in `z`
    intro x hx z hz z' hz' hzz
    have hy := (hspec x z).1
    have hy' := (hspec x z').1
    have h1 : Feq β θ U f x (H x z) z' < Feq β θ U f x (H x z) z :=
      hFz x (Jint_mono hδρ hx) _ hy (Jint_mono hδρ hz) (Jint_mono hδρ hz') hzz
    rw [heq7 x hx z hz, ← heq7 x hx z' hz'] at h1
    exact (hFy x (Jint_mono hδρ hx) z' (Jint_mono hδρ hz')).lt_iff_lt hy hy' |>.1 h1
  · -- Lipschitz constants close to `H₁*`, `H₂*`
    intro m₁ m₂ hm₁ hm₂
    have hH1 : 0 < -F1 / F2 := div_pos (by linarith) hF2p
    have hH2 : 0 < -F3 / F2 := div_pos (by linarith) hF2p
    have hm₁p : 0 < 1 + m₁ := by linarith
    have hm₂p : 0 < 1 + m₂ := by linarith
    have hg₁ : 0 < F2 * m₁ + F1 := by
      have := (div_lt_iff₀ hF2p).1 hm₁
      linarith
    have hg₂ : 0 < F2 * m₂ + F3 := by
      have := (div_lt_iff₀ hF2p).1 hm₂
      linarith
    set s := min (F2 / 2) (min ((F2 * m₁ + F1) / (1 + m₁)) ((F2 * m₂ + F3) / (1 + m₂)))
      with hs
    have hsp : 0 < s := lt_min (by linarith) (lt_min (div_pos hg₁ hm₁p) (div_pos hg₂ hm₂p))
    have hs1 : s ≤ F2 / 2 := min_le_left _ _
    have hs2 : s * (1 + m₁) ≤ F2 * m₁ + F1 :=
      (le_div_iff₀ hm₁p).1 ((min_le_right _ _).trans (min_le_left _ _))
    have hs3 : s * (1 + m₂) ≤ F2 * m₂ + F3 :=
      (le_div_iff₀ hm₂p).1 ((min_le_right _ _).trans (min_le_right _ _))
    set a := F2 - s with ha
    have hap : 0 < a := by linarith
    obtain ⟨ρ₁, hρ₁, hcube₁⟩ := L.exists_cube (a := a) (b1 := -F1 + s) (b3 := -F3 + s)
      (by linarith) (by linarith) (by linarith)
    have hb1m : -F1 + s ≤ m₁ * a := by
      rw [ha]
      linarith
    have hb3m : -F3 + s ≤ m₂ * a := by
      rw [ha]
      linarith
    set B := b10 / a0 + b30 / a0 with hBdef
    have hB : 0 ≤ B := by positivity
    set ε := min δ (min ρ₁ (ρ₁ / (B + 1))) with hε
    have hεp : 0 < ε := lt_min hδp (lt_min hρ₁ (div_pos hρ₁ (by linarith)))
    have hεδ : ε ≤ δ := min_le_left _ _
    have hερ₁ : ε ≤ ρ₁ := (min_le_right _ _).trans (min_le_left _ _)
    have hεB : ε ≤ ρ₁ / (B + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have hnear : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, H x z ∈ Jint ks ρ₁ := by
      intro x hx z hz
      rw [mem_Jint_iff]
      have h := hglob' x ks z ks
      rw [hcenter] at h
      have hx' := mem_Jint_iff.1 hx
      have hz' := mem_Jint_iff.1 hz
      have h2 : B * ε ≤ ρ₁ := by
        calc B * ε ≤ (B + 1) * ε := by linarith
          _ ≤ (B + 1) * (ρ₁ / (B + 1)) := mul_le_mul_of_nonneg_left hεB (by linarith)
          _ = ρ₁ := by field_simp
      have h3 : b10 / a0 * |x - ks| + b30 / a0 * |z - ks| ≤ B * ε := by
        have h4 := mul_le_mul_of_nonneg_left hx' (div_pos hb10p ha0p).le
        have h5 := mul_le_mul_of_nonneg_left hz' (div_pos hb30p ha0p).le
        rw [hBdef]
        linarith
      linarith
    refine ⟨ε, hεp, hεδ, fun x hx x' hx' z hz z' hz' => ?_⟩
    have hA₁ : ∀ x ∈ Jint ks ρ₁, ∀ y ∈ Jint ks ρ₁, ∀ z ∈ Jint ks ρ₁,
        a ≤ F2f β θ U f x y z := fun x hx y hy z hz => (hcube₁ x hx y hy z hz).1.le
    have hB1₁ : ∀ x ∈ Jint ks ρ₁, ∀ y ∈ Jint ks ρ₁, ∀ z ∈ Jint ks ρ₁,
        |(fun x y (_ : ℝ) => F1f θ U f x y) x y z| ≤ -F1 + s :=
      fun x hx y hy z hz => (hcube₁ x hx y hy z hz).2.1.le
    have hB3₁ : ∀ x ∈ Jint ks ρ₁, ∀ y ∈ Jint ks ρ₁, ∀ z ∈ Jint ks ρ₁,
        |(fun (_ : ℝ) y z => F3f β θ U f y z) x y z| ≤ -F3 + s :=
      fun x hx y hy z hz => (hcube₁ x hx y hy z hz).2.2.1.le
    have key := root_sep (G := Feq β θ U f) hd1 hd2 hd3 hA₁ hB1₁ hB3₁ (Jint_mono hερ₁ hx)
      (Jint_mono hερ₁ hx') (hnear x hx z hz) (hnear x' hx' z' hz') (Jint_mono hερ₁ hz)
      (Jint_mono hερ₁ hz') (heq7 x (Jint_mono hεδ hx) z (Jint_mono hεδ hz))
      (heq7 x' (Jint_mono hεδ hx') z' (Jint_mono hεδ hz'))
    have h1 : a * |H x z - H x' z'| ≤ a * (m₁ * |x - x'| + m₂ * |z - z'|) := by
      have h2 := mul_le_mul_of_nonneg_right hb1m (abs_nonneg (x - x'))
      have h3 := mul_le_mul_of_nonneg_right hb3m (abs_nonneg (z - z'))
      linarith
    exact le_of_mul_le_mul_left h1 hap

end StokeyLucasPrescott.EquilibriaWithDistortions

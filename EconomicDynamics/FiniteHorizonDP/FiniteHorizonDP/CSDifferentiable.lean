/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.CSProperties

/-!
# §6.6.2: the Inada condition, the envelope and first-order conditions, and comparisons

Miao, §6.6.2, pp. 188–189 and Exercise 5, p. 189. Add to `CSModel.Basic` that `u` is
differentiable on `(0, ∞)` with `u′(0+) = ∞` (`CSModel.Smooth`). Then for `x > 0`:

* `cons_pos`: `g_n(x, z) > 0` (the Inada condition; `w > 0` bounds the continuation slope);
* `hasDerivAt_v`, `continuousOn_deriv_v`: **`v_n(·, z)` is `C¹` on `(0, ∞)`** with the envelope
  condition `v_n′(x) = u′(g_n(x))` (Benveniste–Scheinkman, `theorem_4_10`);
* `hasDerivAt_ev`: the continuation value has derivative
  `evd = ∫ v_n′(ρ(z′)s + w(z′), z′) ρ(z′) Q(z, dz′)` for `s ≥ 0`
  (`oc_hasDerivAt_integral_concave`);
* `foc`: **the first-order condition** `u′(g_{n+1}(x)) ≥ β evd_n(s_{n+1}(x))`, with equality if
  `s_{n+1}(x) > 0`; for `ρ ≡ R` this is the book's
  `v_n′(x) = u′(g_n(x)) ≥ βR E v_{n−1}′(Rs_n(x) + y − rb)`;
* `strictMonoOn_cons`: `g_n(·, z)` is **strictly** increasing; `s_n(·, z)` is only weakly
  increasing: `exists_sav_eq_zero` (the constraint binds for small `x`) and
  `not_strictMonoOn_sav`;
* `cons_succ_le`, `sav_le_sav_succ`, `deriv_v_le`: **`g_n` is decreasing in `n`, `s_n` and
  `v_n′` are increasing in `n`** (weakly; `exists_cons_succ_eq` shows strictness fails);
* `cons_ge_low`, `cons_le_high`: **`c_t(x; y_max) ≥ c_t(x) ≥ c_t(x; y_min)`** (p. 189), for
  `ρ ≡ R`, where `detModel z₀` is the model whose shock is `z₀` every period; this holds for
  Markov shocks too, and needs no assumption on `u′′′`.

`cs_compare` is the comparison lemma behind the last two items.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology Metric

/-- **Comparison of first-order conditions.** Let `du` be antitone on `(0, ∞)`, `s₁, s₂ < x`,
`du(x − s₁) = D₁(s₁)` if `s₁ > 0`, `D₂(s₂) ≤ du(x − s₂)`, `D₁(s₁) ≤ D₂(s₁)` and `D₂` strictly
decreasing on `[0, ∞)`. Then `s₁ ≤ s₂`. -/
theorem cs_compare {du D₁ D₂ : ℝ → ℝ} (hdu : AntitoneOn du (Set.Ioi 0)) {x s₁ s₂ : ℝ}
    (hs₁ : s₁ < x) (hs₂ : 0 ≤ s₂) (hs₂x : s₂ < x) (hfoc₁ : 0 < s₁ → du (x - s₁) = D₁ s₁)
    (hfoc₂ : D₂ s₂ ≤ du (x - s₂)) (hD : D₁ s₁ ≤ D₂ s₁) (hanti : StrictAntiOn D₂ (Set.Ici 0)) :
    s₁ ≤ s₂ := by
  by_contra hcon
  push Not at hcon
  have h1 : 0 < s₁ := hs₂.trans_lt hcon
  have h2 := hanti (Set.mem_Ici.2 hs₂) (Set.mem_Ici.2 h1.le) hcon
  have h3 := hdu (Set.mem_Ioi.2 (sub_pos.2 hs₁)) (Set.mem_Ioi.2 (sub_pos.2 hs₂x))
    (by linarith : x - s₁ ≤ x - s₂)
  have h4 := hfoc₁ h1
  linarith

namespace CSModel

variable {Z : Type*} [MeasurableSpace Z] (M : CSModel Z)

/-- Differentiability and the **Inada condition** (Miao, p. 187): `u` is differentiable on
`(0, ∞)` and `u′(c) → ∞` as `c → 0+`. -/
structure Smooth : Prop where
  u_diff : ∀ c, 0 < c → DifferentiableAt ℝ M.u c
  inada : Tendsto (deriv M.u) (𝓝[>] 0) atTop

/-- The derivative of the continuation value:
`∫ v_n′(ρ(z′)s + w(z′), z′) ρ(z′) Q(z, dz′)`. -/
noncomputable def evd (n : ℕ) (z : Z) (s : ℝ) : ℝ :=
  ∫ z', deriv (fun y => M.v n y z') (M.ρ z' * s + M.w z') * M.ρ z' ∂M.Q z

/-- The model whose shock is `z₀` in every period (`Q(z, ·) = δ_{z₀}`): for §6.6.2 with
`z₀ = y_min` or `y_max`, the deterministic problems behind `c_t(x; y_min)`, `c_t(x; y_max)`. -/
noncomputable def detModel (z₀ : Z) : CSModel Z :=
  { M with Q := Kernel.const Z (Measure.dirac z₀) }

variable {M} [MetricSpace Z]

/-- `u′` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_deriv_u (h : M.Basic) (hs : M.Smooth) :
    StrictAntiOn (deriv M.u) (Set.Ioi 0) :=
  (h.u_conc.subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    fun c hc => hs.u_diff c hc

variable [CompactSpace Z] [BorelSpace Z] [IsMarkovKernel M.Q]

/-- **The Inada condition makes consumption interior** (Miao, p. 188): `g_n(x, z) > 0` for
`x > 0`. -/
theorem cons_pos (h : M.Basic) (hs : M.Smooth) (n : ℕ) {x : ℝ} (hx : 0 < x) (z : Z) :
    0 < M.cons n x z := by
  cases n with
  | zero => simpa [cons, sav] using hx
  | succ n =>
    obtain ⟨hm, hv⟩ := sav_mem h n hx.le z
    simp only [cons]
    set s := M.sav (n + 1) x z
    rcases hm.2.lt_or_eq with hlt | heq
    · exact sub_pos.2 hlt
    exfalso
    have hev := (strictConcaveOn_ev h (strictConcaveOn_v h n) z).concaveOn
    set K := (M.ev n z (x / 2) - M.ev n z 0) / (x / 2 - 0)
    have hβ := h.β_pos
    obtain ⟨ε, hεu, hε⟩ : ∃ ε, M.β * K < deriv M.u ε ∧ ε ∈ Set.Ioo 0 (x / 2) :=
      ((hs.inada.eventually (eventually_gt_atTop (M.β * K))).and
        (Ioo_mem_nhdsGT (half_pos hx))).exists
    have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 le_rfl
    have hx2 : x / 2 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (half_pos hx).le
    have hxε : x - ε ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith [hε.2])
    have h1 := hev.slope_anti_adjacent hx2 (Set.mem_Ici.2 hx.le) (by linarith [hε.2] :
      x / 2 < x - ε) (by linarith [hε.1] : x - ε < x)
    have h2 := hev.slope_anti_adjacent h0 hxε (half_pos hx) (by linarith [hε.2] :
      x / 2 < x - ε)
    have hxx : x - (x - ε) = ε := by ring
    rw [hxx] at h1
    have hslope : M.ev n z x - M.ev n z (x - ε) ≤ K * ε :=
      (div_le_iff₀ hε.1).1 (h1.trans h2)
    have hu := h.u_conc.concaveOn.deriv_le_slope h0 (Set.mem_Ici.2 hε.1.le) hε.1
      (hs.u_diff ε hε.1)
    rw [slope_def_field, sub_zero] at hu
    have hu' : ε * deriv M.u ε ≤ M.u ε - M.u 0 := by
      rw [le_div_iff₀ hε.1] at hu
      linarith
    have hfeas : x - ε ∈ Set.Icc 0 x := ⟨hxε, by linarith [hε.1]⟩
    have hle := obj_le h n (z := z) hfeas
    rw [← hv, M.obj_eq_ev _ _ hfeas.2, M.obj_eq_ev _ _ hm.2, hxx, heq, sub_self] at hle
    have e1 : M.β * (M.ev n z x - M.ev n z (x - ε)) ≤ M.β * (K * ε) :=
      mul_le_mul_of_nonneg_left hslope hβ.le
    have e2 : ε * (M.β * K) < ε * deriv M.u ε := mul_lt_mul_of_pos_left hεu hε.1
    nlinarith

/-- **The envelope condition** (Miao, p. 188): for `x > 0`, `v_n(·, z)` is differentiable at `x`
with `v_n′(x) = u′(g_n(x))`. -/
theorem hasDerivAt_v (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => M.v n y z) (deriv M.u (M.cons n x z)) x := by
  cases n with
  | zero =>
    have : M.cons 0 x z = x := sub_zero x
    rw [this]
    exact (hs.u_diff x hx).hasDerivAt
  | succ n =>
    obtain ⟨hm, hv⟩ := sav_mem h n hx.le z
    have hc := cons_pos h hs (n + 1) hx z
    simp only [cons] at hc ⊢
    set s := M.sav (n + 1) x z
    have hsx : s < x := by linarith
    have hW : HasDerivAt (fun y => M.u (y - s) + M.β * M.ev n z s) (deriv M.u (x - s)) x := by
      have h1 := (hs.u_diff (x - s) hc).hasDerivAt.comp x ((hasDerivAt_id' x).sub_const s)
      have h2 := h1.add_const (M.β * M.ev n z s)
      rw [mul_one] at h2
      exact h2
    have heq : M.u (x - s) + M.β * M.ev n z s = M.v (n + 1) x z := by
      rw [← hv, M.obj_eq_ev _ _ hm.2]
    have hle : ∀ᶠ y in 𝓝 x, M.u (y - s) + M.β * M.ev n z s ≤ M.v (n + 1) y z := by
      filter_upwards [eventually_gt_nhds hsx] with y hy
      have hfeas : s ∈ Set.Icc 0 y := ⟨hm.1, hy.le⟩
      have := obj_le h n (z := z) hfeas
      rwa [M.obj_eq_ev _ _ hy.le] at this
    rw [hasDerivAt_iff_hasFDerivAt] at hW ⊢
    exact theorem_4_10 (strictConcaveOn_v h (n + 1) z).concaveOn (Ici_mem_nhds hx) hW heq hle

/-- `v_n′(x) = u′(g_n(x))` for `x > 0`. -/
theorem deriv_v (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) {x : ℝ} (hx : 0 < x) :
    deriv (fun y => M.v n y z) x = deriv M.u (M.cons n x z) :=
  (hasDerivAt_v h hs n z hx).deriv

/-- **`v_n(·, z)` is continuously differentiable on `(0, ∞)`** (Miao, p. 188). -/
theorem continuousOn_deriv_v (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    ContinuousOn (deriv fun y => M.v n y z) (Set.Ioi 0) :=
  oc_continuousOn_deriv_of_concave isOpen_Ioi
    ((strictConcaveOn_v h n z).concaveOn.subset Set.Ioi_subset_Ici_self (convex_Ioi 0))
    fun _ hx => (hasDerivAt_v h hs n z hx).differentiableAt

/-- `v_n′(·, z)` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_deriv_v (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    StrictAntiOn (deriv fun y => M.v n y z) (Set.Ioi 0) :=
  ((strictConcaveOn_v h n z).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    fun _ hx => (hasDerivAt_v h hs n z hx).differentiableAt

/-- **Differentiating the continuation value** under `∫ Q(z, dz′)` at `s ≥ 0`. -/
theorem hasDerivAt_ev (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) {s : ℝ} (hs0 : 0 ≤ s) :
    Integrable (fun z' => deriv (fun y => M.v n y z') (M.ρ z' * s + M.w z') * M.ρ z') (M.Q z) ∧
      HasDerivAt (M.ev n z) (M.evd n z s) s := by
  have : Nonempty Z := ⟨z⟩
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn h.ρ_cont.continuousOn
  obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty h.w_cont.continuousOn
  set m := M.w z₀
  have hm : 0 < m := h.w_pos z₀
  set B' := max B 1
  have hB' : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set r := m / (2 * B')
  have hr : 0 < r := by positivity
  have hBr : B' * r = m / 2 := by simp only [r]; field_simp
  have key : ∀ y, |y - s| ≤ r → ∀ z', m / 2 ≤ M.ρ z' * y + M.w z' := by
    intro y hy z'
    have hρ := h.ρ_pos z'
    have hρB : M.ρ z' ≤ B' := by
      have := hB z' (Set.mem_univ _)
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    have hlo : -r ≤ y - s := (abs_le.1 hy).1
    have e1 : M.ρ z' * (-r) ≤ M.ρ z' * (y - s) := mul_le_mul_of_nonneg_left hlo hρ.le
    have e2 : M.ρ z' * r ≤ B' * r := mul_le_mul_of_nonneg_right hρB hr.le
    have e4 : 0 ≤ M.ρ z' * s := mul_nonneg hρ.le hs0
    have e5 : M.ρ z' * y = M.ρ z' * s + M.ρ z' * (y - s) := by ring
    have e6 : M.ρ z' * (-r) = -(M.ρ z' * r) := mul_neg _ _
    have hw : m ≤ M.w z' := (isMinOn_iff.1 hz₀) z' (Set.mem_univ _)
    linarith
  have hball : ∀ y ∈ ball s r, ∀ z', 0 ≤ M.ρ z' * y + M.w z' := fun y hy z' => by
    have : |y - s| ≤ r := by rw [mem_ball, Real.dist_eq] at hy; exact hy.le
    linarith [key y this z']
  -- the uniform bound
  set K := closedBall s r ×ˢ (Set.univ : Set Z)
  have hK : IsCompact K := (isCompact_closedBall s r).prod isCompact_univ
  have hcK : ContinuousOn (fun q : ℝ × Z => M.v n (M.ρ q.2 * q.1 + M.w q.2) q.2) K := by
    refine ContinuousOn.comp (g := fun p : ℝ × Z => M.v n p.1 p.2)
      (f := fun q : ℝ × Z => (M.ρ q.2 * q.1 + M.w q.2, q.2)) (contV h n)
      (Continuous.continuousOn ?_) fun q hq => ⟨?_, Set.mem_univ _⟩
    · exact ((h.ρ_cont.comp continuous_snd).mul continuous_fst |>.add
        (h.w_cont.comp continuous_snd)).prodMk continuous_snd
    · have : |q.1 - s| ≤ r := by
        have := hq.1
        rw [mem_closedBall, Real.dist_eq] at this
        exact this
      exact Set.mem_Ici.2 (by linarith [key q.1 this q.2])
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcK
  have hres := oc_hasDerivAt_integral_concave (μ := M.Q z)
    (F := fun y z' => M.v n (M.ρ z' * y + M.w z') z')
    (F' := fun z' => deriv (fun y => M.v n y z') (M.ρ z' * s + M.w z') * M.ρ z') (C := C) hr
    (fun z' => ?_) (fun y hy z' => ?_) (fun y hy => integrable_next h n (hball y hy) z)
    (fun z' => ?_)
  · exact hres
  · refine ⟨convex_ball s r, fun y₁ hy₁ y₂ hy₂ a b ha hb hab => ?_⟩
    have := (strictConcaveOn_v h n z').concaveOn.2 (Set.mem_Ici.2 (hball y₁ hy₁ z'))
      (Set.mem_Ici.2 (hball y₂ hy₂ z')) ha hb hab
    simp only [smul_eq_mul] at this ⊢
    have heq : a * (M.ρ z' * y₁ + M.w z') + b * (M.ρ z' * y₂ + M.w z') =
        M.ρ z' * (a * y₁ + b * y₂) + M.w z' := by linear_combination M.w z' * hab
    rwa [heq] at this
  · have := hC (y, z') ⟨ball_subset_closedBall hy, Set.mem_univ _⟩
    rwa [Real.norm_eq_abs] at this
  · have hp : 0 < M.ρ z' * s + M.w z' := by
      have := key s (by rw [sub_self, abs_zero]; exact hr.le) z'
      linarith
    have hlin : HasDerivAt (fun y => M.ρ z' * y + M.w z') (M.ρ z') s := by
      have := ((hasDerivAt_id' s).const_mul (M.ρ z')).add_const (M.w z')
      rwa [mul_one] at this
    exact (hasDerivAt_v h hs n z' hp).differentiableAt.hasDerivAt.comp s hlin

/-- The derivative of the continuation value is strictly decreasing on `[0, ∞)`. -/
theorem strictAntiOn_evd (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    StrictAntiOn (M.evd n z) (Set.Ici 0) := by
  intro s₁ hs₁ s₂ hs₂ hlt
  refine integral_lt_integral_of_lt (hasDerivAt_ev h hs n z hs₂).1 (hasDerivAt_ev h hs n z hs₁).1
    fun z' => ?_
  have hρ := h.ρ_pos z'
  have hp₁ : 0 < M.ρ z' * s₁ + M.w z' := by
    have := mul_nonneg hρ.le (Set.mem_Ici.1 hs₁); linarith [h.w_pos z']
  have hp₂ : 0 < M.ρ z' * s₂ + M.w z' := by
    have := mul_nonneg hρ.le (Set.mem_Ici.1 hs₂); linarith [h.w_pos z']
  have hpp : M.ρ z' * s₁ + M.w z' < M.ρ z' * s₂ + M.w z' := by
    have := mul_lt_mul_of_pos_left hlt hρ; linarith
  exact mul_lt_mul_of_pos_right (strictAntiOn_deriv_v h hs n z' hp₁ hp₂ hpp) hρ

/-- **The first-order condition** (Miao, p. 188): for `x > 0`,
`u′(g_{n+1}(x)) ≥ β ∫ v_n′(ρ(z′)s_{n+1}(x) + w(z′), z′) ρ(z′) Q(z, dz′)`, with equality if
`s_{n+1}(x) > 0`. -/
theorem foc (h : M.Basic) (hs : M.Smooth) (n : ℕ) {x : ℝ} (hx : 0 < x) (z : Z) :
    M.β * M.evd n z (M.sav (n + 1) x z) ≤ deriv M.u (M.cons (n + 1) x z) ∧
      (0 < M.sav (n + 1) x z →
        deriv M.u (M.cons (n + 1) x z) = M.β * M.evd n z (M.sav (n + 1) x z)) := by
  obtain ⟨hm, hv⟩ := sav_mem h n hx.le z
  have hc := cons_pos h hs (n + 1) hx z
  simp only [cons] at hc ⊢
  set s := M.sav (n + 1) x z
  have hsx : s < x := by linarith
  have hf : HasDerivAt (fun s' => M.u (x - s') + M.β * M.ev n z s')
      (deriv M.u (x - s) * -1 + M.β * M.evd n z s) s := by
    have h1 := (hs.u_diff (x - s) hc).hasDerivAt.comp s ((hasDerivAt_id' s).const_sub x)
    exact h1.add ((hasDerivAt_ev h hs n z hm.1).2.const_mul M.β)
  have hmax : ∀ s' ∈ Set.Icc 0 x,
      M.u (x - s') + M.β * M.ev n z s' ≤ M.u (x - s) + M.β * M.ev n z s := fun s' hs' => by
    have := obj_le h n (z := z) hs'
    rw [← hv, M.obj_eq_ev _ _ hs'.2, M.obj_eq_ev _ _ hm.2] at this
    exact this
  refine ⟨?_, fun hpos => ?_⟩
  · have hsl := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left (nhdsGT_le_nhdsNE s)
    have hle : deriv M.u (x - s) * -1 + M.β * M.evd n z s ≤ 0 := by
      refine le_of_tendsto hsl ?_
      filter_upwards [Ioo_mem_nhdsGT hsx] with y hy
      rw [slope_def_field]
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.2 (hmax y ⟨hm.1.trans hy.1.le, hy.2.le⟩)) (sub_pos.2 hy.1).le
    linarith
  · have hloc : IsLocalMax (fun s' => M.u (x - s') + M.β * M.ev n z s') s := by
      filter_upwards [Ioo_mem_nhds hpos hsx] with y hy
      exact hmax y ⟨hy.1.le, hy.2.le⟩
    have := hloc.hasDerivAt_eq_zero hf
    linarith

/-- **`g_n(·, z)` is strictly increasing** on `[0, ∞)` (Miao, p. 188). -/
theorem strictMonoOn_cons (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    StrictMonoOn (fun x => M.cons n x z) (Set.Ici 0) := by
  intro x hx x' hx' hlt
  change M.cons n x z < M.cons n x' z
  have hx'0 : 0 < x' := lt_of_le_of_lt hx hlt
  rcases (Set.mem_Ici.1 hx).lt_or_eq with hx0 | hx0
  swap
  · subst hx0
    have h0 : M.sav n 0 z = 0 := by
      have := sav_mem' h n le_rfl z
      exact le_antisymm this.2 this.1
    have := cons_pos h hs n hx'0 z
    simp only [cons, h0, sub_zero]
    exact this
  cases n with
  | zero => simpa [cons, sav] using hlt
  | succ n =>
    by_contra hcon
    push Not at hcon
    have hc := cons_pos h hs (n + 1) hx0 z
    have hc' := cons_pos h hs (n + 1) hx'0 z
    obtain ⟨f1, -⟩ := foc h hs n hx0 z
    obtain ⟨-, f2⟩ := foc h hs n hx'0 z
    have hm := sav_mem h n hx z
    simp only [cons] at hcon hc hc' f1 f2
    have hss : M.sav (n + 1) x z < M.sav (n + 1) x' z := by linarith
    have hpos : 0 < M.sav (n + 1) x' z := lt_of_le_of_lt hm.1.1 hss
    have e := strictAntiOn_evd h hs n z (Set.mem_Ici.2 hm.1.1) (Set.mem_Ici.2 hpos.le) hss
    have e' := mul_lt_mul_of_pos_left e h.β_pos
    have hu : deriv M.u (x - M.sav (n + 1) x z) ≤ deriv M.u (x' - M.sav (n + 1) x' z) :=
      (strictAntiOn_deriv_u h hs).antitoneOn (Set.mem_Ioi.2 hc') (Set.mem_Ioi.2 hc) hcon
    linarith [f2 hpos]

/-- **The borrowing constraint binds near `0`** (Miao, p. 188): for each `n` there is `x̄ > 0`
with `s_{n+1}(x) = 0` on `(0, x̄]`. -/
theorem exists_sav_eq_zero (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    ∃ xb > 0, ∀ x ∈ Set.Ioc 0 xb, M.sav (n + 1) x z = 0 := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hs.inada.eventually (eventually_gt_atTop (M.β * M.evd n z 0)))
  have hδ0 : 0 < δ := hδ
  refine ⟨δ / 2, half_pos hδ0, fun x hx => ?_⟩
  have hx0 : 0 < x := hx.1
  obtain ⟨hm, -⟩ := sav_mem h n hx0.le z
  by_contra hne
  have hpos : 0 < M.sav (n + 1) x z := lt_of_le_of_ne hm.1 (Ne.symm hne)
  have hc := cons_pos h hs (n + 1) hx0 z
  have f := (foc h hs n hx0 z).2 hpos
  simp only [cons] at hc f
  have e := strictAntiOn_evd h hs n z (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hpos.le) hpos
  have e' := mul_lt_mul_of_pos_left e h.β_pos
  have hux : M.β * M.evd n z 0 < deriv M.u x := hsub ⟨hx0, by linarith [hx.2]⟩
  have hu : deriv M.u x ≤ deriv M.u (x - M.sav (n + 1) x z) :=
    (strictAntiOn_deriv_u h hs).antitoneOn (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hx0)
      (by linarith : x - M.sav (n + 1) x z ≤ x)
  linarith

/-- **`s_n(·, z)` is not strictly increasing** for `n ≥ 1` (correction to "increasing",
p. 188): it vanishes on an interval `[0, x̄]`. -/
theorem not_strictMonoOn_sav (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    ¬ StrictMonoOn (fun x => M.sav (n + 1) x z) (Set.Ici 0) := by
  intro hmono
  obtain ⟨xb, hxb, hzero⟩ := exists_sav_eq_zero h hs n z
  have := hmono (Set.mem_Ici.2 (half_pos hxb).le) (Set.mem_Ici.2 hxb.le) (half_lt_self hxb)
  simp only [hzero (xb / 2) ⟨half_pos hxb, (half_lt_self hxb).le⟩,
    hzero xb ⟨hxb, le_rfl⟩, lt_self_iff_false] at this

/-- The continuation derivatives are ordered when the value derivatives are. -/
theorem evd_le_evd (h : M.Basic) (hs : M.Smooth) {n k : ℕ} (z : Z) {s : ℝ} (hs0 : 0 ≤ s)
    (hd : ∀ z', ∀ p, 0 < p → deriv (fun y => M.v n y z') p ≤ deriv (fun y => M.v k y z') p) :
    M.evd n z s ≤ M.evd k z s := by
  refine integral_mono (hasDerivAt_ev h hs n z hs0).1 (hasDerivAt_ev h hs k z hs0).1
    fun z' => ?_
  have hp : 0 < M.ρ z' * s + M.w z' := by
    have := mul_nonneg (h.ρ_pos z').le hs0; linarith [h.w_pos z']
  exact mul_le_mul_of_nonneg_right (hd z' _ hp) (h.ρ_pos z').le

/-- **`g_n(x)` is decreasing in `n`** (Miao, p. 188): `g_{n+1}(x, z) ≤ g_n(x, z)` for `x > 0`. -/
theorem cons_succ_le (h : M.Basic) (hs : M.Smooth) :
    ∀ n, ∀ z, ∀ x, 0 < x → M.cons (n + 1) x z ≤ M.cons n x z := by
  intro n
  induction n with
  | zero =>
    intro z x hx
    have := (sav_mem h 0 hx.le z).1.1
    simp only [cons, sav] at this ⊢
    linarith
  | succ n ih =>
    intro z x hx
    have hu : AntitoneOn (deriv M.u) (Set.Ioi 0) := (strictAntiOn_deriv_u h hs).antitoneOn
    have hd : ∀ z', ∀ p, 0 < p →
        deriv (fun y => M.v n y z') p ≤ deriv (fun y => M.v (n + 1) y z') p := by
      intro z' p hp
      rw [deriv_v h hs n z' hp, deriv_v h hs (n + 1) z' hp]
      exact hu (Set.mem_Ioi.2 (cons_pos h hs (n + 1) hp z')) (Set.mem_Ioi.2 (cons_pos h hs n hp z'))
        (ih z' p hp)
    have hc₁ := cons_pos h hs (n + 1) hx z
    have hc₂ := cons_pos h hs (n + 2) hx z
    have hm₂ := (sav_mem h (n + 1) hx.le z).1
    have f1 := (foc h hs n hx z).2
    have f2 := (foc h hs (n + 1) hx z).1
    simp only [cons] at hc₁ hc₂ f1 f2 ⊢
    have key := cs_compare (du := deriv M.u) (D₁ := fun s => M.β * M.evd n z s)
      (D₂ := fun s => M.β * M.evd (n + 1) z s) hu (by linarith) hm₂.1 (by linarith) f1 f2
      (mul_le_mul_of_nonneg_left (evd_le_evd h hs z (sav_mem h n hx.le z).1.1 hd) h.β_pos.le)
      (fun a ha b hb hab => mul_lt_mul_of_pos_left (strictAntiOn_evd h hs (n + 1) z ha hb hab)
        h.β_pos)
    linarith

/-- **`s_n(x)` is increasing in `n`** (Miao, p. 188). -/
theorem sav_le_sav_succ (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) {x : ℝ} (hx : 0 < x) :
    M.sav n x z ≤ M.sav (n + 1) x z := by
  have := cons_succ_le h hs n z x hx
  simp only [cons] at this
  linarith

/-- **`v_n′(x)` is increasing in `n`** (Miao, p. 188). -/
theorem deriv_v_le (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) {x : ℝ} (hx : 0 < x) :
    deriv (fun y => M.v n y z) x ≤ deriv (fun y => M.v (n + 1) y z) x := by
  rw [deriv_v h hs n z hx, deriv_v h hs (n + 1) z hx]
  exact (strictAntiOn_deriv_u h hs).antitoneOn (Set.mem_Ioi.2 (cons_pos h hs (n + 1) hx z))
    (Set.mem_Ioi.2 (cons_pos h hs n hx z)) (cons_succ_le h hs n z x hx)

/-- **The monotonicity in `n` is not strict** (correction to "decreasing", p. 188): there is
`x > 0` with `g_{n+2}(x, z) = g_{n+1}(x, z)`, and `g_1(x, z) = g_0(x, z) = x`. -/
theorem exists_cons_succ_eq (h : M.Basic) (hs : M.Smooth) (n : ℕ) (z : Z) :
    (∃ x > 0, M.cons (n + 2) x z = M.cons (n + 1) x z) ∧ ∃ x > 0, M.cons 1 x z = M.cons 0 x z := by
  obtain ⟨a, ha, hza⟩ := exists_sav_eq_zero h hs n z
  obtain ⟨b, hb, hzb⟩ := exists_sav_eq_zero h hs (n + 1) z
  obtain ⟨c, hc, hzc⟩ := exists_sav_eq_zero h hs 0 z
  refine ⟨⟨min a b, lt_min ha hb, ?_⟩, ⟨c, hc, ?_⟩⟩
  · simp only [cons, hza (min a b) ⟨lt_min ha hb, min_le_left _ _⟩,
      hzb (min a b) ⟨lt_min ha hb, min_le_right _ _⟩]
  · have h1 : M.sav 1 c z = 0 := hzc c ⟨hc, le_rfl⟩
    change c - M.sav 1 c z = c - M.sav 0 c z
    rw [h1]
    rfl


omit [CompactSpace Z] [BorelSpace Z] [IsMarkovKernel M.Q] in
/-- The deterministic model `detModel z₀` satisfies the standing hypotheses. -/
theorem Basic.detModel (h : M.Basic) (z₀ : Z) : (M.detModel z₀).Basic :=
  ⟨h.β_pos, h.u_cont, h.u_mono, h.u_conc, h.ρ_cont, h.ρ_pos, h.w_cont, h.w_pos,
    isFeller_const (Measure.dirac z₀)⟩

omit [MetricSpace Z] [CompactSpace Z] [BorelSpace Z] [IsMarkovKernel M.Q] in
/-- The deterministic model's kernel is Markov. -/
theorem isMarkovKernel_detModel (z₀ : Z) : IsMarkovKernel (M.detModel z₀).Q := by
  change IsMarkovKernel (Kernel.const Z (Measure.dirac z₀))
  infer_instance

omit [CompactSpace Z] [IsMarkovKernel M.Q] in
/-- For the deterministic model the continuation derivative is evaluated at the shock `z₀`. -/
theorem evd_detModel (z₀ : Z) (n : ℕ) (z : Z) (s : ℝ) :
    (M.detModel z₀).evd n z s =
      deriv (fun y => (M.detModel z₀).v n y z₀) (M.ρ z₀ * s + M.w z₀) * M.ρ z₀ := by
  change ∫ z', deriv (fun y => (M.detModel z₀).v n y z') (M.ρ z' * s + M.w z') * M.ρ z'
    ∂(Kernel.const Z (Measure.dirac z₀) z) = _
  rw [Kernel.const_apply, integral_dirac]

/-- **The comparison with the lowest income** (Miao, p. 189), for `ρ ≡ R`:
`c_t(x) ≥ c_t(x; y_min)`, where `c_t(x; y_min)` is consumption in the model whose shock is `z₀`
every period and `w(z₀) ≤ w(z′)` for all `z′` (for §6.6.2, `z₀ = y_min`). It holds for every
current shock `z` of the stochastic model (so also for Markov shocks, Exercise 6). -/
theorem cons_ge_low (h : M.Basic) (hs : M.Smooth) {R : ℝ} (hR : ∀ z, M.ρ z = R) {z₀ : Z}
    (hw : ∀ z', M.w z₀ ≤ M.w z') :
    ∀ n, ∀ z z'', ∀ x, 0 < x → (M.detModel z₀).cons n x z'' ≤ M.cons n x z := by
  have := isMarkovKernel_detModel (M := M) z₀
  have hD := h.detModel z₀
  have hDs : (M.detModel z₀).Smooth := ⟨hs.u_diff, hs.inada⟩
  have hu : AntitoneOn (deriv M.u) (Set.Ioi 0) := (strictAntiOn_deriv_u h hs).antitoneOn
  have hR0 : 0 < R := hR z₀ ▸ h.ρ_pos z₀
  intro n
  induction n with
  | zero => intro z z'' x _; exact le_rfl
  | succ n ih =>
    intro z z'' x hx
    have hc₁ := cons_pos h hs (n + 1) hx z
    have hc₂ := cons_pos hD hDs (n + 1) hx z''
    have hm₁ := (sav_mem h n hx.le z).1
    have hm₂ := (sav_mem hD n hx.le z'').1
    have f1 := (foc h hs n hx z).2
    have f2 := (foc hD hDs n hx z'').1
    simp only [cons] at hc₁ hc₂ f1 f2 ⊢
    set s₁ := M.sav (n + 1) x z
    have hp₀ : 0 < R * s₁ + M.w z₀ := by
      have := mul_nonneg hR0.le hm₁.1; linarith [h.w_pos z₀]
    set c := deriv (fun y => (M.detModel z₀).v n y z₀) (R * s₁ + M.w z₀) * R
    have hle : M.evd n z s₁ ≤ (M.detModel z₀).evd n z'' s₁ := by
      rw [evd_detModel, hR z₀]
      change M.evd n z s₁ ≤ c
      have hpt : ∀ z', deriv (fun y => M.v n y z') (M.ρ z' * s₁ + M.w z') * M.ρ z' ≤ c := by
        intro z'
        rw [hR z']
        refine mul_le_mul_of_nonneg_right ?_ hR0.le
        have hp' : 0 < R * s₁ + M.w z' := by linarith [hw z']
        have e1 := (strictAntiOn_deriv_v h hs n z').antitoneOn (Set.mem_Ioi.2 hp₀)
          (Set.mem_Ioi.2 hp') (by linarith [hw z'] : R * s₁ + M.w z₀ ≤ R * s₁ + M.w z')
        refine e1.trans ?_
        rw [deriv_v h hs n z' hp₀, deriv_v hD hDs n z₀ hp₀]
        exact hu (Set.mem_Ioi.2 (cons_pos hD hDs n hp₀ z₀)) (Set.mem_Ioi.2 (cons_pos h hs n hp₀ z'))
          (ih z' z₀ _ hp₀)
      calc M.evd n z s₁ ≤ ∫ _, c ∂M.Q z :=
            integral_mono (hasDerivAt_ev h hs n z hm₁.1).1 (integrable_const c) hpt
        _ = c := by simp only [integral_const, probReal_univ, one_smul]
    have key := cs_compare (du := deriv M.u) (D₁ := fun s => M.β * M.evd n z s)
      (D₂ := fun s => M.β * (M.detModel z₀).evd n z'' s) hu (by linarith) hm₂.1 (by linarith)
      f1 f2 (mul_le_mul_of_nonneg_left hle h.β_pos.le)
      (fun a ha b hb hab => mul_lt_mul_of_pos_left (strictAntiOn_evd hD hDs n z'' ha hb hab)
        h.β_pos)
    linarith

/-- **The comparison with the highest income** (Miao, p. 189), for `ρ ≡ R`:
`c_t(x; y_max) ≥ c_t(x)`, where `c_t(x; y_max)` is consumption in the model whose shock is `z₁`
every period and `w(z′) ≤ w(z₁)` for all `z′` (for §6.6.2, `z₁ = y_max`). -/
theorem cons_le_high (h : M.Basic) (hs : M.Smooth) {R : ℝ} (hR : ∀ z, M.ρ z = R) {z₁ : Z}
    (hw : ∀ z', M.w z' ≤ M.w z₁) :
    ∀ n, ∀ z z'', ∀ x, 0 < x → M.cons n x z ≤ (M.detModel z₁).cons n x z'' := by
  have := isMarkovKernel_detModel (M := M) z₁
  have hD := h.detModel z₁
  have hDs : (M.detModel z₁).Smooth := ⟨hs.u_diff, hs.inada⟩
  have hu : AntitoneOn (deriv M.u) (Set.Ioi 0) := (strictAntiOn_deriv_u h hs).antitoneOn
  have hR0 : 0 < R := hR z₁ ▸ h.ρ_pos z₁
  intro n
  induction n with
  | zero => intro z z'' x _; exact le_rfl
  | succ n ih =>
    intro z z'' x hx
    have hc₁ := cons_pos hD hDs (n + 1) hx z''
    have hc₂ := cons_pos h hs (n + 1) hx z
    have hm₁ := (sav_mem hD n hx.le z'').1
    have hm₂ := (sav_mem h n hx.le z).1
    have f1 := (foc hD hDs n hx z'').2
    have f2 := (foc h hs n hx z).1
    simp only [cons] at hc₁ hc₂ f1 f2 ⊢
    set s₁ := (M.detModel z₁).sav (n + 1) x z''
    have hp₁ : 0 < R * s₁ + M.w z₁ := by
      have := mul_nonneg hR0.le hm₁.1; linarith [h.w_pos z₁]
    set c := deriv (fun y => (M.detModel z₁).v n y z₁) (R * s₁ + M.w z₁) * R
    have hle : (M.detModel z₁).evd n z'' s₁ ≤ M.evd n z s₁ := by
      rw [evd_detModel, hR z₁]
      change c ≤ M.evd n z s₁
      have hpt : ∀ z', c ≤ deriv (fun y => M.v n y z') (M.ρ z' * s₁ + M.w z') * M.ρ z' := by
        intro z'
        rw [hR z']
        refine mul_le_mul_of_nonneg_right ?_ hR0.le
        have hp' : 0 < R * s₁ + M.w z' := by
          have := mul_nonneg hR0.le hm₁.1; linarith [h.w_pos z']
        have e1 := (strictAntiOn_deriv_v h hs n z').antitoneOn (Set.mem_Ioi.2 hp')
          (Set.mem_Ioi.2 hp₁) (by linarith [hw z'] : R * s₁ + M.w z' ≤ R * s₁ + M.w z₁)
        refine le_trans ?_ e1
        rw [deriv_v h hs n z' hp₁, deriv_v hD hDs n z₁ hp₁]
        exact hu (Set.mem_Ioi.2 (cons_pos h hs n hp₁ z')) (Set.mem_Ioi.2 (cons_pos hD hDs n hp₁ z₁))
          (ih z' z₁ _ hp₁)
      calc c = ∫ _, c ∂M.Q z := by simp only [integral_const, probReal_univ, one_smul]
        _ ≤ M.evd n z s₁ := integral_mono (integrable_const c) (hasDerivAt_ev h hs n z hm₁.1).1 hpt
    have key := cs_compare (du := deriv M.u) (D₁ := fun s => M.β * (M.detModel z₁).evd n z'' s)
      (D₂ := fun s => M.β * M.evd n z s) hu (by linarith) hm₂.1 (by linarith)
      f1 f2 (mul_le_mul_of_nonneg_left hle h.β_pos.le)
      (fun a ha b hb hab => mul_lt_mul_of_pos_left (strictAntiOn_evd h hs n z ha hb hab)
        h.β_pos)
    linarith

end CSModel

end Miao.FiniteHorizonDP

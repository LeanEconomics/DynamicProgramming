/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.GrowthCertaintyDDOneSectorGrowth

/-!
# Exercise 5.1c with a weakly concave technology

Copied unchanged (apart from imports and the namespace `GrowthCertaintyDD`) from the Chapter 6
project `DeterministicDynamics` (module `DeterministicDynamics.WeakConcavity`),
for Exercise 16.1(e)–(g).

SLP §5.1, p. 104: Exercise 5.1c asks to show that under (U1)–(U4) and (T1)–(T4) the hypotheses
of Theorem 4.8 hold. They do not: with `f` only weakly concave, Assumption 4.7 can fail
(`ex_5_1c_weak_counterexample`). The conclusions of Theorem 4.8 nevertheless hold, and this
module proves them directly.

* `growthF_concave`: `F(x, y) = U(f(x) − y)` is concave on the graph (the weak half of
  Assumption 4.7), and `bellman_concave_growth`: `T` preserves concavity, so `v` is concave
  (`growth_concave`).
* `chord_step`: if `v` is affine along the chord between `a ≠ a'`, then the optimal
  consumptions at `a` and `a'` are equal (strict concavity of `U`), the optimal savings
  `b ≠ b'` again give an affine chord, and `v(a) − v(a') = β(v(b) − v(b'))`.
* `growth_strictConcave`: iterating, `v(x) − v(x') = βⁿ(v(bₙ) − v(bₙ'))` for every `n`, so
  `v(x) = v(x')`; this contradicts strict monotonicity. Hence `v` is strictly concave.
* `ex_5_1c_weak`: under (U1)–(U4) and (T1)–(T4), `v` is strictly concave and the optimal policy
  is a continuous function, as the book claims.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

namespace GrowthCertaintyDD

open Set Filter Topology BoundedContinuousFunction

variable {U f : ℝ → ℝ} {β xbar : ℝ}

/-- `F(x, y) = U(f(x) − y)` is concave on the graph when `U` is concave and `f` is concave. -/
theorem growthF_concave (h : GrowthHyp U f β xbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {x y x' y' : Icc (0 : ℝ) xbar} (hy : y ∈ growthΓ f xbar x)
    (hy' : y' ∈ growthΓ f xbar x') {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * growthF U f xbar (x, y) + (1 - θ) * growthF U f xbar (x', y') ≤
      growthF U f xbar (cmb (convex_Icc 0 xbar) h0 h1 x x',
        cmb (convex_Icc 0 xbar) h0 h1 y y') := by
  set c := f x.1 - y.1
  set c' := f x'.1 - y'.1
  have hc : 0 ≤ c := sub_nonneg.2 hy
  have hc' : 0 ≤ c' := sub_nonneg.2 hy'
  have h1' : 0 ≤ 1 - θ := by linarith
  have hUc := hU.2 (mem_Ici.2 hc) (mem_Ici.2 hc') h0 h1' (by ring)
  simp only [smul_eq_mul] at hUc
  have hcomb : 0 ≤ θ * c + (1 - θ) * c' := by positivity
  have hfw := hf.2 (mem_Ici.2 x.2.1) (mem_Ici.2 x'.2.1) h0 h1' (by ring)
  simp only [smul_eq_mul] at hfw
  have harg : θ * c + (1 - θ) * c' ≤
      f (θ * x.1 + (1 - θ) * x'.1) - (θ * y.1 + (1 - θ) * y'.1) := by
    simp only [c, c']; linarith
  have hmono := h.U_mono.monotoneOn (mem_Ici.2 hcomb) (mem_Ici.2 (hcomb.trans harg)) harg
  simp only [growthF, cmb, smul_eq_mul]
  exact hUc.trans hmono

/-- `T` preserves concavity when `U` and `f` are concave. -/
theorem bellman_concave_growth (h : GrowthHyp U f β xbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {g : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hg : IsConcaveS (convex_Icc 0 xbar) g) :
    IsConcaveS (convex_Icc 0 xbar)
      (bellman (growth_assumption43 h) (growth_assumption44 h) g) := by
  intro x x' θ h0 h1
  obtain ⟨y, hy, hyv, -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) g x
  obtain ⟨y', hy', hyv', -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) g x'
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax (growth_assumption43 h)
    (growth_assumption44 h) g (cmb (convex_Icc 0 xbar) h0 h1 x x')
  have hm := hmax _ (growth_a48 hf x y x' y' hy hy' θ h0 h1)
  have hF := growthF_concave h hU hf hy hy' h0 h1
  have hgc := mul_le_mul_of_nonneg_left (hg y y' θ h0 h1) h.β_pos.le
  rw [hyv, hyv']
  nlinarith

/-- With `U` and `f` concave the fixed point `v` is concave. -/
theorem growth_concave (h : GrowthHyp U f β xbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    IsConcaveS (convex_Icc 0 xbar) v :=
  have : Nonempty (Icc (0 : ℝ) xbar) := ⟨⟨0, le_rfl, h.xbar_pos.le⟩⟩
  (corollary_1 (S' := {g | IsConcaveS (convex_Icc 0 xbar) g})
    (S'' := {g | IsConcaveS (convex_Icc 0 xbar) g})
    (bellman_contraction (growth_assumption43 h) (growth_assumption44 h)) hv
    ⟨0, fun x x' θ _ _ => by simp⟩ (isClosed_concave _)
    (fun _ hg => bellman_concave_growth h hU hf hg)
    (fun _ hg => bellman_concave_growth h hU hf hg)).1

/-- **The chord step.** If `v` is affine along the chord between `a ≠ a'`, so is it between the
optimal savings `b ≠ b'`, and `v(a) − v(a') = β(v(b) − v(b'))`. -/
theorem chord_step (h : GrowthHyp U f β xbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v)
    (hvc : IsConcaveS (convex_Icc 0 xbar) v) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    {a a' : Icc (0 : ℝ) xbar} (hne : a ≠ a')
    (hchord : v (cmb (convex_Icc 0 xbar) h0.le h1.le a a') ≤ θ * v a + (1 - θ) * v a') :
    ∃ b b' : Icc (0 : ℝ) xbar, b ≠ b' ∧
      v (cmb (convex_Icc 0 xbar) h0.le h1.le b b') ≤ θ * v b + (1 - θ) * v b' ∧
      v a - v a' = β * (v b - v b') := by
  obtain ⟨b, hb, hbv, -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) v a
  obtain ⟨b', hb', hbv', -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) v a'
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax (growth_assumption43 h)
    (growth_assumption44 h) v (cmb (convex_Icc 0 xbar) h0.le h1.le a a')
  rw [hv] at hbv hbv' hmax
  have hm := hmax _ (growth_a48 hf a b a' b' hb hb' θ h0.le h1.le)
  have hF := growthF_concave h hU.concaveOn hf hb hb' h0.le h1.le
  have hvb := mul_le_mul_of_nonneg_left (hvc b b' θ h0.le h1.le) h.β_pos.le
  have e : θ * v a + (1 - θ) * v a' = θ * growthF U f xbar (a, b) +
      (1 - θ) * growthF U f xbar (a', b') + β * (θ * v b + (1 - θ) * v b') := by
    rw [hbv, hbv']; ring
  have hb₁ : b.1 ≤ f a.1 := hb
  have hb₁' : b'.1 ≤ f a'.1 := hb'
  -- equal consumption, by strict concavity of `U`
  have hcc : f a.1 - b.1 = f a'.1 - b'.1 := by
    by_contra hcne
    have hc0 : 0 ≤ f a.1 - b.1 := sub_nonneg.2 hb
    have hc0' : 0 ≤ f a'.1 - b'.1 := sub_nonneg.2 hb'
    have hs := hU.2 (mem_Ici.2 hc0) (mem_Ici.2 hc0') hcne h0
      (show (0 : ℝ) < 1 - θ by linarith) (show θ + (1 - θ) = 1 by ring)
    simp only [smul_eq_mul] at hs
    have hfw := hf.2 (mem_Ici.2 a.2.1) (mem_Ici.2 a'.2.1) h0.le
      (show (0 : ℝ) ≤ 1 - θ by linarith) (by ring)
    simp only [smul_eq_mul] at hfw
    have hcomb : 0 ≤ θ * (f a.1 - b.1) + (1 - θ) * (f a'.1 - b'.1) := by
      have : (0 : ℝ) ≤ 1 - θ := by linarith
      positivity
    have harg : θ * (f a.1 - b.1) + (1 - θ) * (f a'.1 - b'.1) ≤
        f (θ * a.1 + (1 - θ) * a'.1) - (θ * b.1 + (1 - θ) * b'.1) := by linarith
    have hmono := h.U_mono.monotoneOn (mem_Ici.2 hcomb) (mem_Ici.2 (hcomb.trans harg)) harg
    have hFc : growthF U f xbar (cmb (convex_Icc 0 xbar) h0.le h1.le a a',
        cmb (convex_Icc 0 xbar) h0.le h1.le b b') =
        U (f (θ * a.1 + (1 - θ) * a'.1) - (θ * b.1 + (1 - θ) * b'.1)) := by
      simp [growthF, cmb]
    simp only [growthF] at e
    rw [hFc] at hm
    linarith
  refine ⟨b, b', fun heq => hne (Subtype.ext ?_), ?_, ?_⟩
  · have hfe : f a.1 = f a'.1 := by rw [heq] at hcc; linarith
    exact h.f_mono.injOn (mem_Ici.2 a.2.1) (mem_Ici.2 a'.2.1) hfe
  · refine le_of_mul_le_mul_left ?_ h.β_pos
    linarith
  · have hFe : growthF U f xbar (a, b) = growthF U f xbar (a', b') := by
      simp only [growthF]; rw [hcc]
    rw [hbv, hbv', hFe]; ring

/-- Under (U1)–(U4) and (T1)–(T4) the fixed point `v` is strictly concave. -/
theorem growth_strictConcave (h : GrowthHyp U f β xbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    IsStrictConcaveS (convex_Icc 0 xbar) v := by
  have hvc := growth_concave h hU.concaveOn hf hv
  have hvm : StrictMono v := by
    obtain ⟨u, -, huniq, -, hmono, -⟩ := ex_5_1ab h
    rw [huniq v hv]
    exact hmono
  intro x x' hne θ h0 h1
  by_contra hle
  push Not at hle
  -- the chord stays affine along the optimal paths
  have hiter : ∀ n : ℕ, ∃ b b' : Icc (0 : ℝ) xbar, b ≠ b' ∧
      v (cmb (convex_Icc 0 xbar) h0.le h1.le b b') ≤ θ * v b + (1 - θ) * v b' ∧
      v x - v x' = β ^ n * (v b - v b') := by
    intro n
    induction n with
    | zero => exact ⟨x, x', hne, hle, by ring⟩
    | succ n ih =>
      obtain ⟨b, b', hbb, hch, he⟩ := ih
      obtain ⟨c, c', hcc, hch', he'⟩ := chord_step h hU hf hv hvc h0 h1 hbb hch
      exact ⟨c, c', hcc, hch', by rw [he, he']; ring⟩
  -- so `|v(x) − v(x')| ≤ 2βⁿ‖v‖ → 0`
  have hbound : ∀ n : ℕ, |v x - v x'| ≤ β ^ n * (2 * ‖v‖) := fun n => by
    obtain ⟨b, b', -, -, he⟩ := hiter n
    rw [he, abs_mul, abs_of_nonneg (pow_nonneg h.β_pos.le n)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h.β_pos.le n)
    have := v.norm_coe_le_norm b
    have := v.norm_coe_le_norm b'
    rw [Real.norm_eq_abs] at *
    linarith [abs_sub (v b) (v b')]
  have hlim : Tendsto (fun n : ℕ => β ^ n * (2 * ‖v‖)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.β_pos.le h.β_lt).mul_const (2 * ‖v‖)
  have hzero : |v x - v x'| ≤ 0 := ge_of_tendsto' hlim hbound
  have heq : v x = v x' := sub_eq_zero.1 (abs_nonpos_iff.1 hzero)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (hvm hlt).ne heq
  · exact (hvm hlt).ne heq.symm

/-- **Exercise 5.1c, as the book states it.** Under (U1)–(U4) and (T1)–(T4), with `f` only
weakly concave, `v` is strictly concave, the policy correspondence is single-valued and the
policy function is continuous, although Assumption 4.7 can fail. -/
theorem ex_5_1c_weak [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    IsStrictConcaveS (convex_Icc 0 xbar) v ∧
      UniqueArgmax (growthΓ f xbar) (obj (growthF U f xbar) β v) ∧
      Continuous (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v)) := by
  have hvs := growth_strictConcave h hU hf hv
  have h43 := growth_assumption43 h
  have huniq : ∀ x, ∀ y₁ ∈ argmax (obj (growthF U f xbar) β v) (growthΓ f xbar) x,
      ∀ y₂ ∈ argmax (obj (growthF U f xbar) β v) (growthΓ f xbar) x, y₁ = y₂ := by
    intro x y₁ hy₁ y₂ hy₂
    by_contra hne
    have hh : (0 : ℝ) < 1 / 2 := by norm_num
    have hh1 : (1 / 2 : ℝ) < 1 := by norm_num
    have hmem := growth_a48 (xbar := xbar) hf x y₁ x y₂ hy₁.1 hy₂.1 (1 / 2) hh.le hh1.le
    rw [cmb_self] at hmem
    have hF := growthF_concave h hU.concaveOn hf hy₁.1 hy₂.1 hh.le hh1.le
    rw [cmb_self] at hF
    have hvs' := mul_lt_mul_of_pos_left (hvs y₁ y₂ hne (1 / 2) hh hh1) h.β_pos
    have hle := le_maxValue (continuousOn_obj (growth_assumption44 h) v.continuous)
      (h43.compact x) hmem
    have e1 := hy₁.2
    have e2 := hy₂.2
    simp only [obj] at hle e1 e2
    linarith
  have hUA : UniqueArgmax (growthΓ f xbar) (obj (growthF U f xbar) β v) :=
    ⟨h43.nonempty, h43.compact, h43.lhc, h43.uhc,
      continuousOn_obj (growth_assumption44 h) v.continuous, huniq⟩
  exact ⟨hvs, hUA, hUA.continuous_argmaxFn⟩

end GrowthCertaintyDD

end StokeyLucasPrescott.EquilibriumApplications

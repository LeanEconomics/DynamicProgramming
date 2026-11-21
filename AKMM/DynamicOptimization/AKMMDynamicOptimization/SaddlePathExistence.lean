/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.SaddlePath

/-!
# The saddle path exists: the optimal policy

AKMM, App. 4.A.4, p. 834: "the social planner has to choose `c₀` so that `(k₀, c₀)` is on the
saddle path". The book asserts that the saddle path exists. Here it is the optimal consumption
policy, and `saddle_path_iff` then gives convergence iff `c₀` is on it.

* For `δ = 1` in SLP's §6.1 setting (`f` total resources, `U` continuous on `[0, ∞)`, Inada
  conditions, `f'(∞) = 0`), the saddle path is `c = f(k) − g(k)` for the optimal capital policy
  `g` on `(0, k̄_max]`, with steady state `k*`, `βf'(k*) = 1` (`saddle_path_slp`).
* For log utility, `f(k) = Ak^α` and `δ = 1`, the saddle path is `c = (1 − αβ)Ak^α` on all of
  `(0, ∞)`; a path converges iff it starts on it, a path above it has capital becoming
  nonpositive in finite time, and a path below it has `c_t → 0` and violates the TVC
  (`saddle_logCobbDouglas`). This is a concrete instance of every hypothesis of the general
  results.
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real BoundedContinuousFunction StokeyLucasPrescott.DeterministicDynamics

/-- **AKMM, p. 834: the saddle path is the optimal policy (`δ = 1`).** In SLP's §6.1 setting
(`f` total resources, so `δ = 1` in (4.A.8)), with `k* > 0`, `f'(k*) = 1/β`: a path of
(4.A.8)–(4.A.9) with positive `k`, `c` and `k₀ ≤ k̄` converges to `(k*, f(k*) − k*)` iff
`c₀ = f(k₀) − g(k₀)`, where `g` is the optimal capital policy. -/
theorem saddle_path_slp {U f U' f' : ℝ → ℝ} {β kbar : ℝ} [Nonempty (Set.Icc (0 : ℝ) kbar)]
    {v : Set.Icc (0 : ℝ) kbar →ᵇ ℝ} (S : Setting61 U f U' f' β kbar v) {kstar : ℝ}
    (hks0 : 0 < kstar) (hks : f' kstar = 1 / β) {k c : ℕ → ℝ}
    (hs : saddleSystem f f' U' β 1 k c) (hk : ∀ t, 0 < k t) (hc : ∀ t, 0 < c t)
    (hk0 : k 0 ≤ kbar) :
    (Tendsto k atTop (𝓝 kstar) ∧ Tendsto c atTop (𝓝 (f kstar - kstar))) ↔
      c 0 = f (k 0) - gpol U f β kbar v (k 0) := by
  have hβ := S.dyn.β_pos
  have hfconc : ConcaveOn ℝ (Set.Ici 0) f := S.dyn.f_conc.concaveOn
  have hf'pos : ∀ x, 0 < x → 0 < f' x := by
    intro x hx
    have h1 := tangent_le hfconc (Set.mem_Ici.2 hx.le)
      (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ x + 1)) (S.dyn.f_deriv x hx)
    have h2 := S.dyn.f_mono (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ x + 1))
      (by linarith : x < x + 1)
    nlinarith
  have hU' : StrictAntiOn U' (Set.Ioi 0) := fun a ha b _ hab => S.dyn.U'_lt ha hab
  have h411 : 1 = β * (f' kstar + 1 - 1) := by
    rw [hks, add_sub_cancel_right]; field_simp
  set g := gpol U f β kbar v
  refine saddle_path_iff (g := fun x => f x - g x) (K := Set.Ioc 0 kbar) hβ S.dyn.β_lt le_rfl
    hfconc S.dyn.f_deriv hf'pos (fun x hx => S.dyn.U'_pos hx) hU' h411
    (S.dyn.f'_cont.continuousAt (Ioi_mem_nhds hks0)) ?_ hs hk hc ⟨hk 0, hk0⟩
  rintro x ⟨hx0, hxb⟩
  set ks : ℕ → ℝ := fun t => g^[t] x
  have hstep : ∀ t, ks (t + 1) = g (ks t) := fun t => Function.iterate_succ_apply' _ _ _
  have hpos : ∀ t, 0 < ks t ∧ ks t ≤ kbar := by
    intro t
    induction t with
    | zero => exact ⟨hx0, hxb⟩
    | succ t ih =>
      rw [hstep]
      exact ⟨(S.gpol_interior ih.1 ih.2).1, (S.gpol_lt_kbar ih.1 ih.2).le⟩
  have hksc : Tendsto ks atTop (𝓝 kstar) := ((prop_6_1 S hks0 hks).2.2 x hx0 hxb).2
  refine ⟨ks, fun t => f (ks t) - ks (t + 1), fun t => ⟨by ring, ?_⟩, fun t => (hpos t).1,
    fun t => ?_, rfl, by simp only [hstep]; rfl, hksc, ?_⟩
  · have he := ((ex_6_1a S).2.2.2 (ks t) (hpos t).1 (hpos t).2).2
    simp only [hstep (t + 1), hstep t]
    rw [he]
    ring
  · have := (S.gpol_interior (hpos t).1 (hpos t).2).2
    change 0 < f (ks t) - ks (t + 1)
    rw [hstep]
    linarith
  · have h1 : Tendsto (fun t => f (ks t)) atTop (𝓝 (f kstar)) :=
      (S.dyn.f_deriv kstar hks0).continuousAt.tendsto.comp hksc
    exact h1.sub (hksc.comp (tendsto_add_atTop_nat 1))

/-- **AKMM, pp. 112 and 834: log utility, Cobb–Douglas, `δ = 1`.** With `u = log`, `f(k) = Ak^α`
(`A > 0`, `0 < α < 1`), `0 < β < 1` and `δ = 1`, the saddle path is `c = (1 − αβ)Ak^α`, the
steady state `k̄ = (αβA)^{1/(1−α)}`, `c̄ = (1 − αβ)Ak̄^α`. For a solution of (4.A.8)–(4.A.9) with
positive consumption and `k₀ > 0`: if `k` stays positive, it converges iff `c₀ = (1 − αβ)Ak₀^α`;
if `c₀` is above, capital becomes nonpositive in finite time; if `c₀` is below (and `k` stays
positive), `c_t → 0` and the TVC expression tends to `+∞`. -/
theorem saddle_logCobbDouglas {A α β : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) {k c : ℕ → ℝ}
    (hs : saddleSystem (fun x => A * x ^ α) (fun x => α * A * x ^ (α - 1)) (fun x => 1 / x)
      β 1 k c) (hc : ∀ t, 0 < c t) (hk0 : 0 < k 0) :
    ((∀ t, 0 < k t) → ((Tendsto k atTop (𝓝 ((α * β * A) ^ (1 / (1 - α)))) ∧
        Tendsto c atTop (𝓝 ((1 - α * β) * A * ((α * β * A) ^ (1 / (1 - α))) ^ α))) ↔
        c 0 = (1 - α * β) * A * k 0 ^ α)) ∧
      ((1 - α * β) * A * k 0 ^ α < c 0 → ∃ T, (∀ s, s ≤ T → 0 < k s) ∧ k (T + 1) ≤ 0) ∧
      ((∀ t, 0 < k t) → c 0 < (1 - α * β) * A * k 0 ^ α →
        Tendsto c atTop (𝓝 0) ∧
        Tendsto (fun t => β ^ (t + 1) * (1 / c (t + 1)) *
          (α * A * k (t + 1) ^ (α - 1) + 1 - 1) * k (t + 1)) atTop atTop) := by
  have hab : α * β < 1 := by nlinarith
  have hq : 0 < α * β * A := mul_pos (mul_pos hα0 hβ0) hA
  set kb := (α * β * A) ^ (1 / (1 - α)) with hkbdef
  have hkb : 0 < kb := rpow_pos_of_pos hq _
  set cb := (1 - α * β) * A * kb ^ α with hcbdef
  have hcb : 0 < cb := mul_pos (mul_pos (by linarith) hA) (rpow_pos_of_pos hkb α)
  have hf : ConcaveOn ℝ (Set.Ici 0) (fun x => A * x ^ α) :=
    (concaveOn_rpow hα0.le hα1.le).smul hA.le
  have hfd : ∀ x, 0 < x → HasDerivAt (fun x => A * x ^ α) (α * A * x ^ (α - 1)) x := by
    intro x hx
    have := (hasDerivAt_rpow_const (p := α) (Or.inl hx.ne')).const_mul A
    convert this using 1; ring
  have hf'pos : ∀ x, 0 < x → 0 < α * A * x ^ (α - 1) := fun x hx =>
    mul_pos (mul_pos hα0 hA) (rpow_pos_of_pos hx _)
  have hf' : StrictAntiOn (fun x => α * A * x ^ (α - 1)) (Set.Ioi 0) := by
    intro x hx y _ hxy
    exact mul_lt_mul_of_pos_left (rpow_lt_rpow_of_neg hx hxy (by linarith)) (mul_pos hα0 hA)
  have hu'pos : ∀ x : ℝ, 0 < x → 0 < 1 / x := fun x hx => one_div_pos.2 hx
  have hu' : StrictAntiOn (fun x : ℝ => 1 / x) (Set.Ioi 0) := fun x hx _ _ hxy =>
    one_div_lt_one_div_of_lt hx hxy
  have hsteady := example_4_5_steady hA hα0 hα1 hβ0
  have h411 : 1 = β * (α * A * kb ^ (α - 1) + 1 - 1) := by
    rw [add_sub_cancel_right]; exact hsteady.2
  have hf'c : ContinuousAt (fun x => α * A * x ^ (α - 1)) kb :=
    continuousAt_const.mul (continuousAt_rpow_const _ _ (Or.inl hkb.ne'))
  -- the saddle path from every `x > 0`
  have hg : ∀ x ∈ Set.Ioi (0 : ℝ), ∃ ks cs : ℕ → ℝ,
      saddleSystem (fun x => A * x ^ α) (fun x => α * A * x ^ (α - 1)) (fun x => 1 / x) β 1
        ks cs ∧ (∀ t, 0 < ks t) ∧ (∀ t, 0 < cs t) ∧ ks 0 = x ∧
      cs 0 = (1 - α * β) * A * x ^ α ∧ Tendsto ks atTop (𝓝 kb) ∧ Tendsto cs atTop (𝓝 cb) := by
    intro x hx
    have hx0 : 0 < x := hx
    set ks : ℕ → ℝ := fun t => (fun y => α * β * A * y ^ α)^[t] x
    have hplan : ∀ t, ks (t + 1) = α * β * A * ks t ^ α := fun t =>
      Function.iterate_succ_apply' _ _ _
    have hpos : ∀ t, 0 < ks t := by
      intro t
      induction t with
      | zero => exact hx0
      | succ t ih => rw [hplan]; exact mul_pos hq (rpow_pos_of_pos ih α)
    have hksc : Tendsto ks atTop (𝓝 kb) :=
      (example_4_5_convergence hA hα0 hα1 hβ0 hx0 hplan).2
    refine ⟨ks, fun t => (1 - α * β) * A * ks t ^ α, fun t => ⟨?_, ?_⟩, hpos,
      fun t => mul_pos (mul_pos (by linarith) hA) (rpow_pos_of_pos (hpos t) α), rfl, rfl,
      hksc, ?_⟩
    · rw [hplan]; ring
    · have hy := hpos (t + 1)
      have hP := rpow_pos_of_pos (hpos t) α
      simp only
      rw [rpow_sub_one hy.ne', add_sub_cancel_right]
      generalize hQ : ks (t + 1) ^ α = Q
      have hQ0 : 0 < Q := hQ ▸ rpow_pos_of_pos hy α
      rw [hplan t]
      have h1 : (1 - α * β) ≠ 0 := by linarith
      field_simp
    · exact (continuousAt_const.mul (continuousAt_rpow_const _ _ (Or.inl hkb.ne'))).tendsto.comp
        hksc
  refine ⟨fun hk => saddle_path_iff hβ0 hβ1 le_rfl hf hfd hf'pos hu'pos hu' h411 hf'c hg hs hk hc
    (Set.mem_Ioi.2 hk0), fun habove => ?_, fun hk hbelow => ?_⟩
  · obtain ⟨ks, cs, hss, hks, hcs, hks0, hcs0, hksc, -⟩ := hg (k 0) hk0
    exact saddle_above_infeasible hβ0 hβ1 le_rfl hf hfd hf'pos hu'pos hu' h411 hf'c hs hss hc
      hks hcs hksc hks0.symm (hcs0 ▸ habove)
  · obtain ⟨ks, cs, hss, hks, hcs, hks0, hcs0, hksc, hcsc⟩ := hg (k 0) hk0
    -- the golden rule `k^G = (αA)^{1/(1−α)}`
    have hαA : 0 < α * A := mul_pos hα0 hA
    set kG := (α * A) ^ (1 / (1 - α)) with hkGdef
    have hkG0 : 0 < kG := rpow_pos_of_pos hαA _
    have h1α : (1 - α) ≠ 0 := by linarith
    have hG : α * A * kG ^ (α - 1) = 1 := by
      rw [hkGdef, ← rpow_mul hαA.le, show 1 / (1 - α) * (α - 1) = -1 by field_simp; ring,
        rpow_neg_one]
      field_simp
    have hbar : α * A * kb ^ (α - 1) = 1 + 1 / β - 1 := by
      have := hsteady.2
      field_simp
      linarith
    have hkG : kb < kG := steady_below_golden hβ0 hβ1 hf' hkb hkG0 hbar hG
    have hf0 : A * (0 : ℝ) ^ α = 0 := by rw [zero_rpow hα0.ne', mul_zero]
    obtain ⟨-, h2, -, h4⟩ := saddle_below (f := fun x => A * x ^ α) hβ0 hβ1 le_rfl hf0 hf hfd
      hf'pos hf' hu'pos hu' hkb h411 hcb (continuousAt_const.div continuousAt_id hcb.ne')
      (by rw [hG]) hkG hs hss hk hc hks hcs hksc hcsc hks0.symm (hcs0 ▸ hbelow)
    exact ⟨h2, h4⟩

end AKMM.DynamicOptimization

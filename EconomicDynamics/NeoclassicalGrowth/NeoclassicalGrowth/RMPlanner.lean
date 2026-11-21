/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RMBasics
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The social planner's problem of the basic Ramsey model

Miao, §14.1.1, "Social Planner's Problem", pp. 464–465. The planner maximises
`∑ βᵗ gₙᵗ u(c_t, n_t)` subject to `gₙᵗc_t + gₙᵗi_t = F(gₙᵗk_t, A_tgₙᵗn_t)` and
`gₙk_{t+1} = (1 − δ)k_t + i_t`, with `A_t = g_aᵗ`. Since `F` is homogeneous of degree one the
per-capita resource constraint is `c_t + i_t = F(k_t, A_tn_t)` (`rm_planner_resource`), and
eliminating `i_t` gives `c_t = F(k_t, A_tn_t) + (1 − δ)k_t − gₙk_{t+1}` (`rmPlanC`).

Optimality is used in the weakest form the first-order conditions need: no feasible plan that
agrees with the plan from some date `T` on gives a higher discounted utility over dates `< T`
(`RMPlanNFI`). A plan that maximises the infinite sum among feasible plans with summable utility
has this property (`rm_planner_nfi_of_optimal`).

* The Euler equation `u_c(c_t, n_t) = βu_c(c_{t+1}, n_{t+1})[F_K(k_{t+1}, A_{t+1}n_{t+1}) + 1 − δ]`
  is necessary (`rm_planner_euler`), by the variation of `k_{t+1}` alone.
* The intratemporal condition is necessary in the form
  `−u_n(c_t, n_t)/u_c(c_t, n_t) = A_tF_N(k_t, A_tn_t)` (`rm_planner_intratemporal`), by the
  variation of `n_t` alone.

**Correction.** The book prints `−u_n/u_c = F_N(k_t, A_tn_t)`, without the factor `A_t` (the
detrended version on p. 465 is right). With `F_N ≠ 0` the printed equation and the true one
together force `A_t = 1` (`rm_planner_intratemporal_misprint`), so the printed one fails at every
date `t ≥ 1` when `g_a ≠ 1`.
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-- Miao, p. 464: the aggregate resource constraint `gₙᵗc_t + gₙᵗi_t = F(gₙᵗk_t, A_tgₙᵗn_t)` is
equivalent to the per-capita one `c_t + i_t = F(k_t, A_tn_t)` when `F` is homogeneous of degree
one. -/
theorem rm_planner_resource {F : ℝ → ℝ → ℝ} (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    {gn A c i k n : ℝ} (hgn : 0 < gn) (t : ℕ) :
    gn ^ t * c + gn ^ t * i = F (gn ^ t * k) (A * (gn ^ t * n)) ↔ c + i = F k (A * n) := by
  have hs : (0 : ℝ) < gn ^ t := pow_pos hgn t
  rw [show A * (gn ^ t * n) = gn ^ t * (A * n) by ring, hhom _ _ _ hs]
  constructor
  · intro h
    have : gn ^ t * (c + i) = gn ^ t * F k (A * n) := by linarith
    exact mul_left_cancel₀ hs.ne' this
  · intro h; rw [← h]; ring

/-- Per-capita consumption from the resource constraint and (14.2):
`c_t = F(k_t, g_aᵗn_t) + (1 − δ)k_t − gₙk_{t+1}`. -/
def rmPlanC (F : ℝ → ℝ → ℝ) (ga gn δ : ℝ) (k n : ℕ → ℝ) (t : ℕ) : ℝ :=
  F (k t) (ga ^ t * n t) + (1 - δ) * k t - gn * k (t + 1)

/-- The gain in discounted utility over dates `< T` from switching from `(k, n)` to `(k', n')`. -/
def rmPlanGain (U F : ℝ → ℝ → ℝ) (β ga gn δ : ℝ) (k n k' n' : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, β ^ t * gn ^ t *
    (U (rmPlanC F ga gn δ k' n' t) (n' t) - U (rmPlanC F ga gn δ k n t) (n t))

/-- A feasible plan from `k₀`: positive capital, labour and consumption at every date. -/
def RMPlanFeasible (F : ℝ → ℝ → ℝ) (ga gn δ k0 : ℝ) (k n : ℕ → ℝ) : Prop :=
  k 0 = k0 ∧ ∀ t, 0 < k t ∧ 0 < n t ∧ 0 < rmPlanC F ga gn δ k n t

/-- No finite improvement: no feasible plan agreeing with `(k, n)` from some date `T` on does
better over the dates `< T`. -/
def RMPlanNFI (U F : ℝ → ℝ → ℝ) (β ga gn δ : ℝ) (k n : ℕ → ℝ) : Prop :=
  ∀ (T : ℕ) (k' n' : ℕ → ℝ), RMPlanFeasible F ga gn δ (k 0) k' n' →
    (∀ t, T ≤ t → k' t = k t ∧ n' t = n t) → rmPlanGain U F β ga gn δ k n k' n' T ≤ 0

/-- Miao, p. 464: a plan maximising `∑ βᵗgₙᵗu(c_t, n_t)` among feasible plans (all of which have
summable discounted utility) admits no finite improvement. -/
theorem rm_planner_nfi_of_optimal {U F : ℝ → ℝ → ℝ} {β ga gn δ : ℝ} {k n : ℕ → ℝ}
    (hsum : ∀ k' n', RMPlanFeasible F ga gn δ (k 0) k' n' →
      Summable (fun t => β ^ t * gn ^ t * U (rmPlanC F ga gn δ k' n' t) (n' t)))
    (hk : RMPlanFeasible F ga gn δ (k 0) k n)
    (hopt : ∀ k' n', RMPlanFeasible F ga gn δ (k 0) k' n' →
      ∑' t, β ^ t * gn ^ t * U (rmPlanC F ga gn δ k' n' t) (n' t) ≤
        ∑' t, β ^ t * gn ^ t * U (rmPlanC F ga gn δ k n t) (n t)) :
    RMPlanNFI U F β ga gn δ k n := by
  intro T k' n' hf hagree
  have hc : ∀ t, T ≤ t → rmPlanC F ga gn δ k' n' t = rmPlanC F ga gn δ k n t := by
    intro t ht
    simp only [rmPlanC, (hagree t ht).1, (hagree t ht).2, (hagree (t + 1) (by omega)).1]
  have h1 := (hsum k' n' hf).sum_add_tsum_nat_add T
  have h2 := (hsum k n hk).sum_add_tsum_nat_add T
  have htail : (∑' t, β ^ (t + T) * gn ^ (t + T) *
      U (rmPlanC F ga gn δ k' n' (t + T)) (n' (t + T))) =
      ∑' t, β ^ (t + T) * gn ^ (t + T) * U (rmPlanC F ga gn δ k n (t + T)) (n (t + T)) := by
    congr 1; ext t
    rw [hc (t + T) (by omega), (hagree (t + T) (by omega)).2]
  have := hopt k' n' hf
  simp only [rmPlanGain, mul_sub, Finset.sum_sub_distrib]
  linarith

/-- Evaluation of the derivative `u_c • fst + u_n • snd` at `(x, y)`. -/
theorem rm_clm_apply (a b x y : ℝ) :
    (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y) =
      a * x + b * y := by
  simp

/-- The capital stock with `k_{t+1}` replaced by `x`. -/
theorem rm_planC_update_k_ne {F : ℝ → ℝ → ℝ} {ga gn δ : ℝ} (k n : ℕ → ℝ) {t s : ℕ} (x : ℝ)
    (h1 : s ≠ t) (h2 : s ≠ t + 1) :
    rmPlanC F ga gn δ (Function.update k (t + 1) x) n s = rmPlanC F ga gn δ k n s := by
  simp only [rmPlanC, Function.update_of_ne h2, Function.update_of_ne (show s + 1 ≠ t + 1 by omega)]

theorem rm_planC_update_k_t {F : ℝ → ℝ → ℝ} {ga gn δ : ℝ} (k n : ℕ → ℝ) (t : ℕ) (x : ℝ) :
    rmPlanC F ga gn δ (Function.update k (t + 1) x) n t =
      F (k t) (ga ^ t * n t) + (1 - δ) * k t - gn * x := by
  simp only [rmPlanC, Function.update_of_ne (show t ≠ t + 1 by omega), Function.update_self]

theorem rm_planC_update_k_succ {F : ℝ → ℝ → ℝ} {ga gn δ : ℝ} (k n : ℕ → ℝ) (t : ℕ) (x : ℝ) :
    rmPlanC F ga gn δ (Function.update k (t + 1) x) n (t + 1) =
      F x (ga ^ (t + 1) * n (t + 1)) + (1 - δ) * x - gn * k (t + 2) := by
  simp only [rmPlanC, Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega), Function.update_self]

/-- **The planner's Euler equation** (Miao, p. 464): a feasible plan with no finite improvement
satisfies `u_c(c_t, n_t) = βu_c(c_{t+1}, n_{t+1})[F_K(k_{t+1}, A_{t+1}n_{t+1}) + 1 − δ]`,
`A_t = g_aᵗ`. Here `U` is Fréchet differentiable at each `(c_t, n_t)` with partials `u_c, u_n`
and `F` has partial derivative `F_K` in capital on the positive quadrant. -/
theorem rm_planner_euler {U F uc un FK : ℝ → ℝ → ℝ} {β ga gn δ : ℝ} {k n : ℕ → ℝ}
    (hβ : 0 < β) (hgn : 0 < gn) (hga : 0 < ga)
    (hU : ∀ t, HasFDerivAt (fun p : ℝ × ℝ => U p.1 p.2)
      (uc (rmPlanC F ga gn δ k n t) (n t) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        un (rmPlanC F ga gn δ k n t) (n t) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (rmPlanC F ga gn δ k n t, n t))
    (hFK : ∀ x y, 0 < x → 0 < y → HasDerivAt (fun z => F z y) (FK x y) x)
    (hfeas : RMPlanFeasible F ga gn δ (k 0) k n) (hnfi : RMPlanNFI U F β ga gn δ k n) (t : ℕ) :
    uc (rmPlanC F ga gn δ k n t) (n t) = β * uc (rmPlanC F ga gn δ k n (t + 1)) (n (t + 1)) *
      (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + 1 - δ) := by
  set c0 := rmPlanC F ga gn δ k n t with hc0
  set c1 := rmPlanC F ga gn δ k n (t + 1) with hc1
  have hy : 0 < ga ^ (t + 1) * n (t + 1) := mul_pos (pow_pos hga _) (hfeas.2 (t + 1)).2.1
  -- consumption at dates `t` and `t + 1` as functions of `k_{t+1} = x`
  set f0 : ℝ → ℝ := fun x => F (k t) (ga ^ t * n t) + (1 - δ) * k t - gn * x with hf0
  set f1 : ℝ → ℝ := fun x => F x (ga ^ (t + 1) * n (t + 1)) + (1 - δ) * x - gn * k (t + 1 + 1)
    with hf1
  have hd0 : HasDerivAt f0 (-gn) (k (t + 1)) := by
    have := ((hasDerivAt_id (k (t + 1))).const_mul gn).const_sub
      (F (k t) (ga ^ t * n t) + (1 - δ) * k t)
    simpa [hf0] using this
  have hd1 : HasDerivAt f1 (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + (1 - δ)) (k (t + 1)) := by
    have := (((hFK (k (t + 1)) _ (hfeas.2 (t + 1)).1 hy).add
      ((hasDerivAt_id (k (t + 1))).const_mul (1 - δ))).sub_const (gn * k (t + 1 + 1)))
    simpa [hf1] using this
  have hf0x : f0 (k (t + 1)) = c0 := rfl
  have hf1x : f1 (k (t + 1)) = c1 := rfl
  -- the objective
  set φ : ℝ → ℝ := fun x => β ^ t * gn ^ t * (U (f0 x) (n t) - U c0 (n t)) +
    β ^ (t + 1) * gn ^ (t + 1) * (U (f1 x) (n (t + 1)) - U c1 (n (t + 1))) with hφ
  have hg0 : HasDerivAt (fun x => U (f0 x) (n t)) (uc c0 (n t) * (-gn)) (k (t + 1)) := by
    have hγ : HasDerivAt (fun x => (f0 x, n t)) ((-gn), (0 : ℝ)) (k (t + 1)) :=
      hd0.prodMk (hasDerivAt_const _ _)
    have := HasFDerivAt.comp_hasDerivAt (x := k (t + 1)) (hU t) hγ
    convert this using 1
    · rfl
    · rw [rm_clm_apply, hc0]; ring
  have hg1 : HasDerivAt (fun x => U (f1 x) (n (t + 1)))
      (uc c1 (n (t + 1)) * (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + (1 - δ))) (k (t + 1)) := by
    have hγ : HasDerivAt (fun x => (f1 x, n (t + 1)))
        ((FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + (1 - δ)), (0 : ℝ)) (k (t + 1)) :=
      hd1.prodMk (hasDerivAt_const _ _)
    have := HasFDerivAt.comp_hasDerivAt (x := k (t + 1)) (hU (t + 1)) hγ
    convert this using 1
    · rfl
    · rw [rm_clm_apply, hc1]; ring
  have hφd : HasDerivAt φ (β ^ t * gn ^ t * (uc c0 (n t) * (-gn)) + β ^ (t + 1) * gn ^ (t + 1) *
      (uc c1 (n (t + 1)) * (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + (1 - δ)))) (k (t + 1)) := by
    have := ((hg0.sub_const (U c0 (n t))).const_mul (β ^ t * gn ^ t)).add
      ((hg1.sub_const (U c1 (n (t + 1)))).const_mul (β ^ (t + 1) * gn ^ (t + 1)))
    exact this.congr_deriv (by ring)
  -- local maximum
  have hmax : IsLocalMax φ (k (t + 1)) := by
    have e1 : ∀ᶠ x in 𝓝 (k (t + 1)), 0 < x := lt_mem_nhds (hfeas.2 (t + 1)).1
    have e2 : ∀ᶠ x in 𝓝 (k (t + 1)), 0 < f0 x :=
      continuousAt_const.eventually_lt hd0.continuousAt (by rw [hf0x]; exact (hfeas.2 t).2.2)
    have e3 : ∀ᶠ x in 𝓝 (k (t + 1)), 0 < f1 x :=
      continuousAt_const.eventually_lt hd1.continuousAt
        (by rw [hf1x]; exact (hfeas.2 (t + 1)).2.2)
    filter_upwards [e1, e2, e3] with x h1 h2 h3
    have hφ0 : φ (k (t + 1)) = 0 := by simp [hφ, hf0x, hf1x]
    rw [hφ0]
    have hfe : RMPlanFeasible F ga gn δ (k 0) (Function.update k (t + 1) x) n := by
      refine ⟨Function.update_of_ne (by omega) _ _, fun s => ?_⟩
      by_cases hs1 : s = t
      · subst hs1
        refine ⟨?_, (hfeas.2 s).2.1, ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact (hfeas.2 s).1
        · rw [rm_planC_update_k_t]; exact h2
      by_cases hs2 : s = t + 1
      · subst hs2
        refine ⟨by rw [Function.update_self]; exact h1, (hfeas.2 _).2.1, ?_⟩
        rw [rm_planC_update_k_succ]; exact h3
      refine ⟨?_, (hfeas.2 s).2.1, ?_⟩
      · rw [Function.update_of_ne hs2]; exact (hfeas.2 s).1
      · rw [rm_planC_update_k_ne k n x hs1 hs2]; exact (hfeas.2 s).2.2
    have hg := hnfi (t + 2) (Function.update k (t + 1) x) n hfe (fun s hs =>
      ⟨Function.update_of_ne (by omega) _ _, rfl⟩)
    have hsum : rmPlanGain U F β ga gn δ k n (Function.update k (t + 1) x) n (t + 2) = φ x := by
      simp only [rmPlanGain, Finset.sum_range_succ]
      rw [Finset.sum_eq_zero (fun s hs => by
        rw [rm_planC_update_k_ne k n x (by simp at hs; omega) (by simp at hs; omega)]; ring)]
      rw [rm_planC_update_k_t, rm_planC_update_k_succ]
      simp only [hφ, hf0, hf1, hc0, hc1]
      ring
    linarith
  have h0 := hmax.hasDerivAt_eq_zero hφd
  have hpos : 0 < β ^ t * gn ^ t * gn := by positivity
  have : β ^ t * gn ^ t * gn * (uc c0 (n t) - β * uc c1 (n (t + 1)) *
      (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + 1 - δ)) = 0 := by
    linear_combination -h0
  have := (mul_eq_zero.1 this).resolve_left hpos.ne'
  linarith

/-- **The planner's intratemporal condition** (Miao, p. 464, corrected): a feasible plan with no
finite improvement satisfies `u_n(c_t, n_t) + u_c(c_t, n_t)A_tF_N(k_t, A_tn_t) = 0`, i.e.
`−u_n/u_c = A_tF_N(k_t, A_tn_t)`. -/
theorem rm_planner_intratemporal {U F uc un FN : ℝ → ℝ → ℝ} {β ga gn δ : ℝ} {k n : ℕ → ℝ}
    (hβ : 0 < β) (hgn : 0 < gn) (hga : 0 < ga)
    (hU : ∀ t, HasFDerivAt (fun p : ℝ × ℝ => U p.1 p.2)
      (uc (rmPlanC F ga gn δ k n t) (n t) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        un (rmPlanC F ga gn δ k n t) (n t) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (rmPlanC F ga gn δ k n t, n t))
    (hFN : ∀ x y, 0 < x → 0 < y → HasDerivAt (fun z => F x z) (FN x y) y)
    (hfeas : RMPlanFeasible F ga gn δ (k 0) k n) (hnfi : RMPlanNFI U F β ga gn δ k n) (t : ℕ) :
    un (rmPlanC F ga gn δ k n t) (n t) +
      uc (rmPlanC F ga gn δ k n t) (n t) * (ga ^ t * FN (k t) (ga ^ t * n t)) = 0 := by
  set c0 := rmPlanC F ga gn δ k n t with hc0
  set x0 := n t with hx0
  have hA : 0 < ga ^ t := pow_pos hga t
  set f0 : ℝ → ℝ := fun x => F (k t) (ga ^ t * x) + (1 - δ) * k t - gn * k (t + 1) with hf0
  have hd0 : HasDerivAt f0 (FN (k t) (ga ^ t * x0) * ga ^ t) x0 := by
    have hl : HasDerivAt (fun x => ga ^ t * x) (ga ^ t) x0 := by
      simpa using (hasDerivAt_id x0).const_mul (ga ^ t)
    have := (((hFN (k t) (ga ^ t * x0) (hfeas.2 t).1 (mul_pos hA (hfeas.2 t).2.1)).comp x0
      hl).add_const ((1 - δ) * k t)).sub_const (gn * k (t + 1))
    exact this
  have hf0x : f0 x0 = c0 := rfl
  set φ : ℝ → ℝ := fun x => β ^ t * gn ^ t * (U (f0 x) x - U c0 x0) with hφ
  have hg : HasDerivAt (fun x => U (f0 x) x)
      (uc c0 x0 * (FN (k t) (ga ^ t * x0) * ga ^ t) + un c0 x0) x0 := by
    have hγ : HasDerivAt (fun x => (f0 x, x)) ((FN (k t) (ga ^ t * x0) * ga ^ t), (1 : ℝ)) x0 :=
      hd0.prodMk (hasDerivAt_id x0)
    have := HasFDerivAt.comp_hasDerivAt (f := fun x => (f0 x, x)) (x := x0) (hU t) hγ
    convert this using 1
    · rfl
    · rw [rm_clm_apply, hc0, hx0]; ring
  have hφd : HasDerivAt φ (β ^ t * gn ^ t *
      (uc c0 x0 * (FN (k t) (ga ^ t * x0) * ga ^ t) + un c0 x0)) x0 := by
    simpa [hφ] using (hg.sub_const (U c0 x0)).const_mul (β ^ t * gn ^ t)
  have hmax : IsLocalMax φ x0 := by
    have e1 : ∀ᶠ x in 𝓝 x0, 0 < x := lt_mem_nhds (hfeas.2 t).2.1
    have e2 : ∀ᶠ x in 𝓝 x0, 0 < f0 x :=
      continuousAt_const.eventually_lt hd0.continuousAt (by rw [hf0x]; exact (hfeas.2 t).2.2)
    filter_upwards [e1, e2] with x h1 h2
    have hφ0 : φ x0 = 0 := by simp [hφ, hf0x]
    rw [hφ0]
    have hcs : ∀ s, s ≠ t → rmPlanC F ga gn δ k (Function.update n t x) s =
        rmPlanC F ga gn δ k n s := fun s hs => by
      simp only [rmPlanC, Function.update_of_ne hs]
    have hct : rmPlanC F ga gn δ k (Function.update n t x) t = f0 x := by
      simp only [rmPlanC, Function.update_self, hf0]
    have hfe : RMPlanFeasible F ga gn δ (k 0) k (Function.update n t x) := by
      refine ⟨rfl, fun s => ?_⟩
      by_cases hs : s = t
      · subst hs
        exact ⟨(hfeas.2 s).1, by rw [Function.update_self]; exact h1, by rw [hct]; exact h2⟩
      · refine ⟨(hfeas.2 s).1, by rw [Function.update_of_ne hs]; exact (hfeas.2 s).2.1, ?_⟩
        rw [hcs s hs]; exact (hfeas.2 s).2.2
    have hgain := hnfi (t + 1) k (Function.update n t x) hfe (fun s hs =>
      ⟨rfl, Function.update_of_ne (by omega) _ _⟩)
    have hsum : rmPlanGain U F β ga gn δ k n k (Function.update n t x) (t + 1) = φ x := by
      simp only [rmPlanGain, Finset.sum_range_succ]
      rw [Finset.sum_eq_zero (fun s hs => by
        have hs' : s ≠ t := by simp at hs; omega
        rw [hcs s hs', Function.update_of_ne hs']; ring)]
      rw [hct, Function.update_self]
      simp only [hφ, hc0, hx0]
      ring
    linarith
  have h0 := hmax.hasDerivAt_eq_zero hφd
  have hpos : 0 < β ^ t * gn ^ t := by positivity
  have := (mul_eq_zero.1 h0).resolve_left hpos.ne'
  linarith

/-- Correction to Miao, p. 464: the printed intratemporal condition `−u_n/u_c = F_N(k_t, A_tn_t)`
and the true one `−u_n/u_c = A_tF_N(k_t, A_tn_t)` together force `A_t = 1` when `F_N ≠ 0`. -/
theorem rm_planner_intratemporal_misprint {ucv unv FNv A : ℝ} (huc : ucv ≠ 0) (hFN : FNv ≠ 0)
    (htrue : unv + ucv * (A * FNv) = 0) (hprinted : -unv / ucv = FNv) : A = 1 := by
  have h1 : -unv = FNv * ucv := by field_simp at hprinted; linarith
  have : ucv * FNv * (A - 1) = 0 := by linear_combination htrue + h1
  have := (mul_eq_zero.1 this).resolve_left (mul_ne_zero huc hFN)
  linarith

end Miao.NeoclassicalGrowth

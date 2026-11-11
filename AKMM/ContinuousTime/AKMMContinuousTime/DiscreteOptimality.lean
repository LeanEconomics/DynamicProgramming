/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.DiscreteHamiltonian

/-!
# Necessity and the infinite horizon for the discrete Hamiltonian

AKMM, §9.2 (pp. 244–246). The first-order conditions of the discrete consumption–saving
problem are derived in the book from the Kuhn–Tucker theorem without proof. Here:

* **Necessity** by a direct perturbation: moving `ε` of consumption from period `t` to period
  `t + 1` (`c_t − ε`, `a_{t+1} + ε`, `c_{t+1} + (1 + r)ε`) keeps the path feasible
  (`discreteOptimality_perturb_budget`) and changes lifetime utility only in two terms
  (`discreteOptimality_perturb_sum`), so at an optimum the Euler equation (9.14) holds, both in
  the finite horizon (`discreteHamiltonian_euler_necessary`) and for catching-up optimality in
  the infinite horizon (`discreteHamiltonian_euler_necessary_infinite`); and `a_{T+1} = 0` at a
  finite-horizon optimum when `u` is strictly increasing (`discreteHamiltonian_tvc_necessary`).
* **Infinite horizon** (p. 246): the TVC `lim β^T u'(c_T)a_{T+1} = 0` is equivalent to
  `lim a_{T+1}/(1 + r)^T = 0` (`discreteHamiltonian_tvc_infinite_iff`); the Euler equation and
  the TVC are sufficient for catching-up optimality against every path satisfying the no-Ponzi
  condition (9.15) (`discreteHamiltonian_infinite_sufficient`), using the finite-horizon bound
  `EulerTransversality.finite_horizon_bound`; and an instance: with `β(1 + r) = 1`, keeping the
  asset constant is optimal (`discreteHamiltonian_constant_path_optimal`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- The perturbed consumption path: `c_t − ε` at `t`, `c_{t+1} + (1 + r)ε` at `t + 1`. -/
noncomputable def discreteOptimality_pc (r : ℝ) (c : ℕ → ℝ) (t : ℕ) (ε : ℝ) (s : ℕ) : ℝ :=
  if s = t then c t - ε else if s = t + 1 then c (t + 1) + (1 + r) * ε else c s

/-- The perturbed asset path: `a_{t+1} + ε`. -/
noncomputable def discreteOptimality_pa (a : ℕ → ℝ) (t : ℕ) (ε : ℝ) (s : ℕ) : ℝ :=
  if s = t + 1 then a (t + 1) + ε else a s

/-- The perturbation keeps the budget (9.6): moving `ε` of consumption from `t` to `t + 1` is
financed by saving `ε` more at `t`. -/
theorem discreteOptimality_perturb_budget {r w : ℝ} {a c : ℕ → ℝ}
    (hb : ∀ s, a (s + 1) = w + (1 + r) * a s - c s) (t : ℕ) (ε : ℝ) (s : ℕ) :
    discreteOptimality_pa a t ε (s + 1) =
      w + (1 + r) * discreteOptimality_pa a t ε s - discreteOptimality_pc r c t ε s := by
  simp only [discreteOptimality_pa, discreteOptimality_pc]
  by_cases h1 : s = t
  · subst h1
    simp only [↓reduceIte, show s ≠ s + 1 by omega]
    rw [hb s]
    ring
  · by_cases h2 : s = t + 1
    · subst h2
      simp only [↓reduceIte, h1, show t + 1 + 1 ≠ t + 1 by omega]
      rw [hb (t + 1)]
      ring
    · simp only [show s + 1 ≠ t + 1 by omega, h1, h2, ↓reduceIte]
      exact hb s

/-- The perturbation changes lifetime utility over any horizon `N > t + 1` only through the two
perturbed periods. -/
theorem discreteOptimality_perturb_sum (β r : ℝ) (u : ℝ → ℝ) (c : ℕ → ℝ) {t N : ℕ}
    (hN : t + 1 < N) (ε : ℝ) :
    ∑ s ∈ Finset.range N, β ^ s * u (discreteOptimality_pc r c t ε s) =
      ∑ s ∈ Finset.range N, β ^ s * u (c s) +
        ((β ^ t * u (c t - ε) + β ^ (t + 1) * u (c (t + 1) + (1 + r) * ε)) -
          (β ^ t * u (c t) + β ^ (t + 1) * u (c (t + 1)))) := by
  have hsub : ({t, t + 1} : Finset ℕ) ⊆ Finset.range N := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    simp only [Finset.mem_range]
    omega
  have hz : ∀ s ∈ Finset.range N, s ∉ ({t, t + 1} : Finset ℕ) →
      β ^ s * u (discreteOptimality_pc r c t ε s) - β ^ s * u (c s) = 0 := by
    intro s _ hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    simp [discreteOptimality_pc, hs.1, hs.2]
  have h := Finset.sum_subset hsub hz
  have e1 : discreteOptimality_pc r c t ε t = c t - ε := by simp [discreteOptimality_pc]
  have e2 : discreteOptimality_pc r c t ε (t + 1) = c (t + 1) + (1 + r) * ε := by
    simp [discreteOptimality_pc]
  rw [Finset.sum_pair (show t ≠ t + 1 by omega), e1, e2] at h
  rw [Finset.sum_sub_distrib] at h
  linarith

/-- The two-period perturbation value `g(ε) = β^t u(c_t − ε) + β^{t+1}u(c_{t+1} + (1 + r)ε)` has
a local maximum at `0` only if the Euler equation `u'(c_t) = β(1 + r)u'(c_{t+1})` holds. -/
theorem discreteOptimality_euler_of_localMax {β r : ℝ} {u u' : ℝ → ℝ} {x y : ℝ} {t : ℕ}
    (hβ : β ≠ 0) (hx : HasDerivAt u (u' x) x) (hy : HasDerivAt u (u' y) y)
    (hmax : ∀ᶠ ε in 𝓝 (0 : ℝ), β ^ t * u (x - ε) + β ^ (t + 1) * u (y + (1 + r) * ε) ≤
      β ^ t * u x + β ^ (t + 1) * u y) :
    u' x = β * (1 + r) * u' y := by
  set g : ℝ → ℝ := fun ε => β ^ t * u (x - ε) + β ^ (t + 1) * u (y + (1 + r) * ε)
  have hg1 : HasDerivAt (fun ε : ℝ => u (x - ε)) (u' x * (-1)) 0 := by
    have hin : HasDerivAt (fun ε : ℝ => x - ε) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub x
    exact hx.comp_of_eq (0 : ℝ) hin (by simp)
  have hg2 : HasDerivAt (fun ε : ℝ => u (y + (1 + r) * ε)) (u' y * (1 + r)) 0 := by
    have hin : HasDerivAt (fun ε : ℝ => y + (1 + r) * ε) (1 + r) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + r)).const_add y
    exact hy.comp_of_eq (0 : ℝ) hin (by simp)
  have hg : HasDerivAt g (β ^ t * (u' x * (-1)) + β ^ (t + 1) * (u' y * (1 + r))) 0 :=
    (hg1.const_mul _).add (hg2.const_mul _)
  have hloc : IsLocalMax g 0 := by
    filter_upwards [hmax] with ε hε
    simpa [g] using hε
  have h0 := hloc.hasDerivAt_eq_zero hg
  have hp : β ^ t ≠ 0 := pow_ne_zero _ hβ
  apply mul_left_cancel₀ hp
  rw [pow_succ] at h0
  linear_combination -h0

/-- Positivity of the perturbed consumption for small `ε`. -/
theorem discreteOptimality_perturb_pos {r : ℝ} {c : ℕ → ℝ} (hc : ∀ s, 0 < c s) (t : ℕ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, 0 < discreteOptimality_pc r c t ε s := by
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - ε := by
    have : Tendsto (fun ε : ℝ => c t - ε) (𝓝 0) (𝓝 (c t - 0)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at this
    exact this.eventually (lt_mem_nhds (hc t))
  have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c (t + 1) + (1 + r) * ε := by
    have : Tendsto (fun ε : ℝ => c (t + 1) + (1 + r) * ε) (𝓝 0) (𝓝 (c (t + 1) + (1 + r) * 0)) :=
      tendsto_const_nhds.add (tendsto_id.const_mul _)
    rw [mul_zero, add_zero] at this
    exact this.eventually (lt_mem_nhds (hc (t + 1)))
  filter_upwards [h1, h2] with ε e1 e2 s
  simp only [discreteOptimality_pc]
  split_ifs
  · exact e1
  · exact e2
  · exact hc s

/-- AKMM, (9.14), p. 245, **necessity** in the finite horizon: if a path with positive
consumption maximizes `Σ_{s≤T} β^s u(c_s)` over all paths from `a_0` with positive consumption
satisfying (9.6) and `a_{T+1} ≥ 0`, then the Euler equation holds for every `t < T`. -/
theorem discreteHamiltonian_euler_necessary {β r w : ℝ} {u u' : ℝ → ℝ} {T : ℕ} (hβ : β ≠ 0)
    (hu : ∀ x, 0 < x → HasDerivAt u (u' x) x) {a c : ℕ → ℝ} (hc : ∀ s, 0 < c s)
    (hb : ∀ s, a (s + 1) = w + (1 + r) * a s - c s) (hT : 0 ≤ a (T + 1))
    (hopt : ∀ a' c' : ℕ → ℝ, a' 0 = a 0 → (∀ s, a' (s + 1) = w + (1 + r) * a' s - c' s) →
      (∀ s, 0 < c' s) → 0 ≤ a' (T + 1) →
      ∑ s ∈ Finset.range (T + 1), β ^ s * u (c' s) ≤ ∑ s ∈ Finset.range (T + 1), β ^ s * u (c s))
    {t : ℕ} (ht : t < T) : u' (c t) = β * (1 + r) * u' (c (t + 1)) := by
  refine discreteOptimality_euler_of_localMax (t := t) hβ (hu _ (hc t)) (hu _ (hc (t + 1))) ?_
  filter_upwards [discreteOptimality_perturb_pos (r := r) hc t] with ε hε
  have h := hopt (discreteOptimality_pa a t ε) (discreteOptimality_pc r c t ε)
    (by simp [discreteOptimality_pa]) (discreteOptimality_perturb_budget hb t ε) hε
    (by simpa [discreteOptimality_pa, show T ≠ t by omega] using hT)
  rw [discreteOptimality_perturb_sum β r u c (by omega) ε] at h
  linarith

/-- AKMM, p. 245, **necessity** of `a_{T+1} = 0`: at a finite-horizon optimum, with `u` strictly
increasing on `(0, ∞)`, the terminal asset is zero (otherwise consume it in period `T`). -/
theorem discreteHamiltonian_tvc_necessary {β r w : ℝ} {u : ℝ → ℝ} {T : ℕ} (hβ : 0 < β)
    (hmono : StrictMonoOn u (Set.Ioi 0)) {a c : ℕ → ℝ} (hc : ∀ s, 0 < c s)
    (hb : ∀ s, a (s + 1) = w + (1 + r) * a s - c s) (hT : 0 ≤ a (T + 1))
    (hopt : ∀ a' c' : ℕ → ℝ, a' 0 = a 0 →
      (∀ s, s ≤ T → a' (s + 1) = w + (1 + r) * a' s - c' s) →
      (∀ s, s ≤ T → 0 < c' s) → 0 ≤ a' (T + 1) →
      ∑ s ∈ Finset.range (T + 1), β ^ s * u (c' s) ≤ ∑ s ∈ Finset.range (T + 1), β ^ s * u (c s)) :
    a (T + 1) = 0 := by
  by_contra hne
  have hpos : 0 < a (T + 1) := lt_of_le_of_ne hT (Ne.symm hne)
  set c' : ℕ → ℝ := fun s => if s = T then c T + a (T + 1) else c s
  set a' : ℕ → ℝ := fun s => if s = T + 1 then 0 else a s
  have hb' : ∀ s, s ≤ T → a' (s + 1) = w + (1 + r) * a' s - c' s := by
    intro s hs
    simp only [a', c']
    by_cases h : s = T
    · subst h
      simp only [↓reduceIte, show s ≠ s + 1 by omega]
      rw [hb s]
      ring
    · simp only [show s + 1 ≠ T + 1 by omega, h, show s ≠ T + 1 by omega, ↓reduceIte]
      exact hb s
  have hc' : ∀ s, s ≤ T → 0 < c' s := by
    intro s _
    simp only [c']
    split_ifs
    · linarith [hc T]
    · exact hc s
  have h := hopt a' c' (by simp [a']) hb' hc' (by simp [a'])
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
  have hsame : ∑ s ∈ Finset.range T, β ^ s * u (c' s) = ∑ s ∈ Finset.range T, β ^ s * u (c s) :=
    Finset.sum_congr rfl fun s hs => by
      simp [c', (Finset.mem_range.mp hs).ne]
  rw [hsame] at h
  have hlt : u (c T) < u (c' T) := by
    simp only [c', ↓reduceIte]
    exact hmono (Set.mem_Ioi.mpr (hc T)) (Set.mem_Ioi.mpr (by linarith [hc T])) (by linarith)
  have := mul_lt_mul_of_pos_left hlt (pow_pos hβ T)
  linarith

/-- AKMM, p. 246: given the Euler equation for every `t` and `u'(c_0) ≠ 0`, the TVC
`lim β^T u'(c_T)a_{T+1} = 0` is equivalent to `lim a_{T+1}/(1 + r)^T = 0`. -/
theorem discreteHamiltonian_tvc_infinite_iff {β r : ℝ} {mu a : ℕ → ℝ} (hr : 0 < 1 + r)
    (hmu : mu 0 ≠ 0) (heuler : ∀ t, mu t = β * (1 + r) * mu (t + 1)) :
    Tendsto (fun T => β ^ T * mu T * a (T + 1)) atTop (𝓝 0) ↔
      Tendsto (fun T => a (T + 1) / (1 + r) ^ T) atTop (𝓝 0) := by
  have hm : ∀ T, β ^ T * mu T * a (T + 1) = mu 0 * (a (T + 1) / (1 + r) ^ T) := fun T => by
    rw [discreteHamiltonian_marginal (T := T) hr (fun t _ => heuler t) T le_rfl]
    ring
  simp only [hm]
  constructor
  · intro h
    have := h.const_mul (mu 0)⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hmu] using this
  · intro h
    simpa using h.const_mul (mu 0)

/-- AKMM, p. 246, **sufficiency** in the infinite horizon. If `u` is concave on `(0, ∞)`, `β ≥ 0`,
`1 + r > 0`, and a path with positive consumption satisfies (9.6), the Euler equation (9.14) for
every `t`, and the TVC `lim a_{T+1}/(1 + r)^T = 0`, then it is catching-up optimal against every
path from `a_0` with positive consumption that satisfies the no-Ponzi condition (9.15), stated as
`liminf a'_{T+1}/(1 + r)^T ≥ 0`: for every `δ > 0`, eventually
`Σ_{t≤T} β^t u(c'_t) ≤ Σ_{t≤T} β^t u(c_t) + δ`. -/
theorem discreteHamiltonian_infinite_sufficient {β r w : ℝ} {u u' : ℝ → ℝ} (hβ : 0 ≤ β)
    (hr : 0 < 1 + r) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ x, 0 < x → HasDerivAt u (u' x) x) {a c : ℕ → ℝ} (hc : ∀ t, 0 < c t)
    (hb : ∀ t, a (t + 1) = w + (1 + r) * a t - c t)
    (heuler : ∀ t, u' (c t) = β * (1 + r) * u' (c (t + 1))) (hpos : 0 ≤ u' (c 0))
    (htvc : Tendsto (fun T => a (T + 1) / (1 + r) ^ T) atTop (𝓝 0))
    {a' c' : ℕ → ℝ} (h0 : a' 0 = a 0) (hc' : ∀ t, 0 < c' t)
    (hb' : ∀ t, a' (t + 1) = w + (1 + r) * a' t - c' t)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ a' (T + 1) / (1 + r) ^ T) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1), β ^ t * u (c' t) ≤
      ∑ t ∈ Finset.range (T + 1), β ^ t * u (c t) + δ := by
  set G : Set (ℝ × ℝ) := {p | 0 < w + (1 + r) * p.1 - p.2}
  set F : ℝ → ℝ → ℝ := fun x y => u (w + (1 + r) * x - y)
  set p : ℕ → ℝ →ₗ[ℝ] ℝ := fun t => ((1 + r) * u' (c t)) • LinearMap.id
  set q : ℕ → ℝ →ₗ[ℝ] ℝ := fun t => (-u' (c t)) • LinearMap.id
  have hcx : ∀ t, w + (1 + r) * a t - a (t + 1) = c t := fun t => by rw [hb t]; ring
  have hsup : ∀ t, ∀ x y, (x, y) ∈ G →
      F x y ≤ F (a t) (a (t + 1)) + p t (x - a t) + q t (y - a (t + 1)) := by
    intro t x y hxy
    have hs := RamseyCassKoopmans.concave_support hconc (Set.mem_Ioi.mpr (hc t))
      (Set.mem_Ioi.mpr hxy) (hu (c t) (hc t))
    simp only at hs
    simp only [F, p, q, hcx, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    have e : w + (1 + r) * x - y - c t = (1 + r) * (x - a t) - (y - a (t + 1)) := by
      rw [← hcx t]; ring
    rw [e] at hs
    linarith [hs, show u' (c t) * ((1 + r) * (x - a t) - (y - a (t + 1))) =
      (1 + r) * u' (c t) * (x - a t) + -u' (c t) * (y - a (t + 1)) by ring]
  have hE : ∀ t v, q t v + β * p (t + 1) v = 0 := by
    intro t v
    simp only [p, q, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    rw [heuler t]
    ring
  have hfeas : DPExtensions.EulerTransversality.Feasible G (a 0) a' := by
    refine ⟨h0, fun t => ?_⟩
    change 0 < w + (1 + r) * a' t - a' (t + 1)
    have := hc' t
    rw [hb' t] at *
    linarith
  have hbound := DPExtensions.EulerTransversality.finite_horizon_bound hβ hsup hE hfeas
  have hpv : ∀ (x y : ℕ → ℝ), (∀ t, x (t + 1) = w + (1 + r) * x t - y t) → ∀ T,
      DPExtensions.EulerTransversality.partialValue F β x T =
        ∑ t ∈ Finset.range T, β ^ t * u (y t) := by
    intro x y hxy T
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [F]
    rw [hxy t]
    ring_nf
  have hm := fun T => discreteHamiltonian_marginal (mu := fun t => u' (c t)) (T := T) hr
    (fun t _ => heuler t) T le_rfl
  intro δ hδ
  set K := u' (c 0)
  set η := δ / (2 * (K + 1))
  have hη : 0 < η := div_pos hδ (by positivity)
  filter_upwards [hnpg η hη, (htvc.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < η by
    simpa using hη)))] with T hT1 hT2
  have h := hbound (T + 1)
  rw [hpv a' c' hb', hpv a c hb] at h
  simp only [p, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at h
  have hk : ∀ x, β ^ (T + 1) * ((1 + r) * u' (c (T + 1)) * x) = K * (x / (1 + r) ^ T) := by
    intro x
    have e := hm (T + 1)
    have hp := pow_pos hr T
    rw [show β ^ (T + 1) * ((1 + r) * u' (c (T + 1)) * x) =
        (β ^ (T + 1) * u' (c (T + 1))) * (1 + r) * x by ring, e, pow_succ]
    field_simp
  rw [hk, hk] at h
  have habs := abs_lt.mp hT2
  have hK : K * (a (T + 1) / (1 + r) ^ T) - K * (a' (T + 1) / (1 + r) ^ T) ≤ K * (2 * η) := by
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (by linarith [habs.2]) hpos
  have hKη : K * (2 * η) ≤ δ := by
    have e : K * (2 * η) = δ * (K / (K + 1)) := by
      simp only [η]
      field_simp
    rw [e]
    exact mul_le_of_le_one_right hδ.le ((div_le_one (by linarith)).mpr (by linarith))
  linarith

/-- AKMM, p. 246, an instance of the infinite-horizon sufficiency theorem: if `β(1 + r) = 1` with
`r > 0`, the path that keeps the asset constant, `a_t = a_0` and `c_t = w + ra_0 > 0`, is
catching-up optimal against every no-Ponzi path. -/
theorem discreteHamiltonian_constant_path_optimal {β r w a₀ : ℝ} {u u' : ℝ → ℝ}
    (hr : 0 < r) (hβr : β * (1 + r) = 1) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ x, 0 < x → HasDerivAt u (u' x) x) (hc0 : 0 < w + r * a₀)
    (hpos : 0 ≤ u' (w + r * a₀)) {a' c' : ℕ → ℝ} (h0 : a' 0 = a₀) (hc' : ∀ t, 0 < c' t)
    (hb' : ∀ t, a' (t + 1) = w + (1 + r) * a' t - c' t)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ a' (T + 1) / (1 + r) ^ T) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1), β ^ t * u (c' t) ≤
      ∑ t ∈ Finset.range (T + 1), β ^ t * u (w + r * a₀) + δ := by
  have hβ : 0 ≤ β := by
    by_contra h
    have : β * (1 + r) < 0 := mul_neg_of_neg_of_pos (not_le.mp h) (by linarith)
    linarith
  have htvc : Tendsto (fun T : ℕ => a₀ / (1 + r) ^ T) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 + r)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ (by linarith))).const_mul a₀
    simpa [div_eq_mul_inv, inv_pow] using h
  exact discreteHamiltonian_infinite_sufficient (a := fun _ => a₀) (c := fun _ => w + r * a₀)
    hβ (by linarith) hconc hu (fun _ => hc0) (fun _ => by ring)
    (fun _ => by rw [hβr, one_mul]) hpos htvc h0 hc' hb' hnpg

/-- AKMM, (9.14), p. 246, **necessity** in the infinite horizon: if a path with positive
consumption is catching-up optimal against every path from `a_0` with positive consumption that
satisfies the no-Ponzi condition, and itself satisfies it, then the Euler equation holds at every
`t`. -/
theorem discreteHamiltonian_euler_necessary_infinite {β r w : ℝ} {u u' : ℝ → ℝ} (hβ : β ≠ 0)
    (hu : ∀ x, 0 < x → HasDerivAt u (u' x) x) {a c : ℕ → ℝ} (hc : ∀ s, 0 < c s)
    (hb : ∀ s, a (s + 1) = w + (1 + r) * a s - c s)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ a (T + 1) / (1 + r) ^ T)
    (hopt : ∀ a' c' : ℕ → ℝ, a' 0 = a 0 → (∀ s, a' (s + 1) = w + (1 + r) * a' s - c' s) →
      (∀ s, 0 < c' s) → (∀ η > 0, ∀ᶠ T in atTop, -η ≤ a' (T + 1) / (1 + r) ^ T) →
      ∀ δ > 0, ∀ᶠ T in atTop, ∑ s ∈ Finset.range (T + 1), β ^ s * u (c' s) ≤
        ∑ s ∈ Finset.range (T + 1), β ^ s * u (c s) + δ)
    (t : ℕ) : u' (c t) = β * (1 + r) * u' (c (t + 1)) := by
  refine discreteOptimality_euler_of_localMax (t := t) hβ (hu _ (hc t)) (hu _ (hc (t + 1))) ?_
  filter_upwards [discreteOptimality_perturb_pos (r := r) hc t] with ε hε
  have hnpg' : ∀ η > 0, ∀ᶠ T in atTop,
      -η ≤ discreteOptimality_pa a t ε (T + 1) / (1 + r) ^ T := by
    intro η hη
    filter_upwards [hnpg η hη, eventually_gt_atTop t] with T hT hT'
    simpa [discreteOptimality_pa, show T ≠ t by omega] using hT
  have h := hopt (discreteOptimality_pa a t ε) (discreteOptimality_pc r c t ε)
    (by simp [discreteOptimality_pa]) (discreteOptimality_perturb_budget hb t ε) hε hnpg'
  set D := (β ^ t * u (c t - ε) + β ^ (t + 1) * u (c (t + 1) + (1 + r) * ε)) -
    (β ^ t * u (c t) + β ^ (t + 1) * u (c (t + 1)))
  have hD : ∀ δ > 0, D ≤ δ := by
    intro δ hδ
    obtain ⟨T, hT⟩ := ((h δ hδ).and (eventually_gt_atTop (t + 1))).exists
    rw [discreteOptimality_perturb_sum β r u c (by omega) ε] at hT
    linarith [hT.1]
  have : D ≤ 0 := le_of_forall_pos_le_add fun δ hδ => by linarith [hD δ hδ]
  linarith

end AKMM.ContinuousTime

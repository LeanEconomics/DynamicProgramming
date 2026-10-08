/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EulerTransversality.GrowthModel

/-!
# The Euler equation alone is not sufficient

With linear utility `u(c) = c` and linear technology `f(k) = k/β`, every interior path satisfies
the Euler equation `u'(c_t) = βu'(c_{t+1})f'(k_{t+1})`, since `1 = β · 1 · (1/β)`. The path that
never consumes, `k_t = k₀/βᵗ`, satisfies it but violates the transversality condition
(`β^tu'(c_t)f'(k_t)k_t = k₀/β` for every `t`), and it is not optimal: consuming everything at
date `0` yields `k₀/β > 0`. The transversality condition cannot be dropped from
`growth_sufficient`.
-/

open Filter Topology Set

namespace DPExtensions.EulerTransversality

/-- The growth model with `u(c) = c` and `f(k) = k/β`. -/
noncomputable def linearModel (β : ℝ) (hβ : 0 < β) : GrowthModel where
  u := id
  f := fun k => k / β
  β := β
  β_pos := hβ
  u_concave := concaveOn_id (convex_Ici 0)
  u_mono := monotone_id.monotoneOn _
  f_concave := ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => le_of_eq (by
    simp only [smul_eq_mul]
    ring)⟩

/-- The path that never consumes. -/
noncomputable def hoarding (β k₀ : ℝ) (t : ℕ) : ℝ := k₀ / β ^ t

/-- **Euler without transversality is not sufficient.** -/
theorem euler_not_sufficient {β k₀ : ℝ} (hβ : 0 < β) (hk₀ : 0 < k₀) :
    (∀ t, (hoarding β k₀ t, hoarding β k₀ (t + 1)) ∈ (linearModel β hβ).G) ∧
    (∀ t, HasDerivAt (linearModel β hβ).u 1 ((linearModel β hβ).c (hoarding β k₀) t)) ∧
    (∀ t, HasDerivAt (linearModel β hβ).f (1 / β) (hoarding β k₀ t)) ∧
    (1 : ℝ) = β * 1 * (1 / β) ∧
    ¬ Tendsto (fun t => β ^ t * (1 * (1 / β) * hoarding β k₀ t)) atTop (𝓝 0) ∧
    ¬ CatchingUp (linearModel β hβ).G (linearModel β hβ).F β (hoarding β k₀) := by
  have hβ0 : β ≠ 0 := hβ.ne'
  have hnext : ∀ t, hoarding β k₀ (t + 1) = hoarding β k₀ t / β := fun t => by
    simp only [hoarding, pow_succ]
    field_simp
  have hpos : ∀ t, 0 < hoarding β k₀ t := fun t => div_pos hk₀ (pow_pos hβ t)
  refine ⟨fun t => ⟨(hpos t).le, (hpos (t + 1)).le, ?_⟩, fun t => hasDerivAt_id _,
    fun t => (hasDerivAt_id' _).div_const β, by field_simp,
    fun h => ?_, fun h => ?_⟩
  · simp only [linearModel, hnext t]
    exact le_rfl
  · have hc : (fun t => β ^ t * (1 * (1 / β) * hoarding β k₀ t)) = fun _ => k₀ / β := by
      funext t
      simp only [hoarding]
      field_simp
    rw [hc] at h
    have := tendsto_nhds_unique tendsto_const_nhds h
    exact (div_pos hk₀ hβ).ne' this
  · -- consume everything at date `0`
    set x : ℕ → ℝ := fun t => if t = 0 then k₀ else 0 with hxdef
    have hfeas : Feasible (linearModel β hβ).G (hoarding β k₀ 0) x := by
      refine ⟨by simp [hxdef, hoarding], fun t => ?_⟩
      rcases t with _ | t
      · simp only [hxdef, linearModel, GrowthModel.G]
        simp only [↓reduceIte, Nat.add_one_ne_zero]
        exact ⟨hk₀.le, le_rfl, div_nonneg hk₀.le hβ.le⟩
      · simp only [hxdef, linearModel, GrowthModel.G, Nat.add_one_ne_zero, ↓reduceIte]
        exact ⟨le_rfl, le_rfl, by simp⟩
    have hPVx : ∀ T, partialValue (linearModel β hβ).F β x (T + 1) = k₀ / β := by
      intro T
      induction T with
      | zero =>
        simp [partialValue, GrowthModel.F, linearModel, hxdef]
      | succ T ih =>
        rw [partialValue_succ, ih]
        simp [GrowthModel.F, linearModel, hxdef]
    have hPVs : ∀ T, partialValue (linearModel β hβ).F β (hoarding β k₀) T = 0 := by
      intro T
      refine Finset.sum_eq_zero fun t _ => ?_
      simp only [GrowthModel.F, linearModel, id, hnext t, sub_self, mul_zero]
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h x hfeas (k₀ / β / 2) (by positivity))
    have := hN (N + 1) (by omega)
    rw [hPVx, hPVs] at this
    have : 0 < k₀ / β := div_pos hk₀ hβ
    linarith

end DPExtensions.EulerTransversality

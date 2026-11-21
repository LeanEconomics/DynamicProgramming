/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.LeftRightNhds

/-!
# The existence of an aggregate production function (box, pp. 49–50)

AKMM, box "The existence of an aggregate production function", pp. 49–50, and its footnote a.
A static economy produces two goods from capital and labour, freely allocated across sectors:
`x₁ = G(k₁, ℓ₁)` and `x₂ = aG(k₂, ℓ₂)` with `a > 0` ("identical isoquants — one is a scalar
multiplication of the other"), `k₁ + k₂ = K`, `ℓ₁ + ℓ₂ = L`, with `G` concave and of constant
returns on the positive quadrant. The footnote's exercise: a relative price is implied by the
technologies alone, and there is a price-independent mapping from inputs to output.

* `G` is superadditive (`agg_superadditive`), so every interior allocation satisfies
  `x₁ + x₂/a ≤ G(K, L)` (`agg_frontier_bound`), and every point of that linear frontier with both
  goods produced is attained by a proportional allocation (`agg_frontier_attained`).
* If an interior allocation maximises the value `px₁ + x₂` of output at relative price `p > 0`
  among interior allocations, then `p = a` (`agg_price_implied`): the price is pinned by the
  technologies.
* At `p = a` the maximal value of output is `aG(K, L)`, and output measured in units of good 1,
  `x₁ + x₂/a`, equals `G(K, L)` at every value-maximising allocation: the aggregate production
  function is `G`, independent of prices and preferences (`agg_aggregate_production`).

The box's other statements (the general two-sector mapping depends on `p`; the Cambridge
controversy) are narrative and are not formalised.
-/

namespace AKMM.Framework

open Filter Topology

/-- The positive quadrant of input pairs `(k, ℓ)`. -/
def aggPosQuadrant : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2}

/-- AKMM, box p. 50 (used for the exercise in footnote a): a concave function with constant
returns on the positive quadrant is superadditive, `G(k₁ + k₂, ℓ₁ + ℓ₂) ≥ G(k₁, ℓ₁) + G(k₂, ℓ₂)`. -/
theorem agg_superadditive {G : ℝ → ℝ → ℝ}
    (hconc : ConcaveOn ℝ aggPosQuadrant (fun q => G q.1 q.2))
    (hcrs : ∀ s x y, 0 < s → 0 < x → 0 < y → G (s * x) (s * y) = s * G x y)
    {k₁ ℓ₁ k₂ ℓ₂ : ℝ} (hk₁ : 0 < k₁) (hl₁ : 0 < ℓ₁) (hk₂ : 0 < k₂) (hl₂ : 0 < ℓ₂) :
    G k₁ ℓ₁ + G k₂ ℓ₂ ≤ G (k₁ + k₂) (ℓ₁ + ℓ₂) := by
  have hc := hconc.2 (show ((k₁, ℓ₁) : ℝ × ℝ) ∈ aggPosQuadrant from ⟨hk₁, hl₁⟩)
    (show ((k₂, ℓ₂) : ℝ × ℝ) ∈ aggPosQuadrant from ⟨hk₂, hl₂⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at hc
  have hh := hcrs 2 (1 / 2 * k₁ + 1 / 2 * k₂) (1 / 2 * ℓ₁ + 1 / 2 * ℓ₂) two_pos
    (by positivity) (by positivity)
  rw [show 2 * (1 / 2 * k₁ + 1 / 2 * k₂) = k₁ + k₂ by ring,
    show 2 * (1 / 2 * ℓ₁ + 1 / 2 * ℓ₂) = ℓ₁ + ℓ₂ by ring] at hh
  linarith

/-- AKMM, box p. 50: with `x₂ = aG(k₂, ℓ₂)`, every interior allocation of `(K, L)` lies on or
below the linear frontier `x₁ + x₂/a ≤ G(K, L)`. -/
theorem agg_frontier_bound {G : ℝ → ℝ → ℝ}
    (hconc : ConcaveOn ℝ aggPosQuadrant (fun q => G q.1 q.2))
    (hcrs : ∀ s x y, 0 < s → 0 < x → 0 < y → G (s * x) (s * y) = s * G x y)
    {a K L k₁ ℓ₁ : ℝ} (ha : 0 < a) (hk₁ : 0 < k₁) (hl₁ : 0 < ℓ₁) (hk₂ : k₁ < K)
    (hl₂ : ℓ₁ < L) :
    G k₁ ℓ₁ + a * G (K - k₁) (L - ℓ₁) / a ≤ G K L := by
  have h := agg_superadditive hconc hcrs hk₁ hl₁ (sub_pos.2 hk₂) (sub_pos.2 hl₂)
  rw [add_sub_cancel, add_sub_cancel] at h
  rw [mul_div_cancel_left₀ _ ha.ne']
  exact h

/-- AKMM, box p. 50: the proportional allocation `k₁ = θK`, `ℓ₁ = θL`, `θ ∈ (0, 1)`, produces
`x₁ = θG(K, L)` and `x₂ = (1 − θ)aG(K, L)`: every point of the frontier `x₁ + x₂/a = G(K, L)`
with both goods produced is attained. -/
theorem agg_frontier_attained {G : ℝ → ℝ → ℝ}
    (hcrs : ∀ s x y, 0 < s → 0 < x → 0 < y → G (s * x) (s * y) = s * G x y)
    {a K L θ : ℝ} (ha : 0 < a) (hK : 0 < K) (hL : 0 < L) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    G (θ * K) (θ * L) = θ * G K L ∧
      a * G (K - θ * K) (L - θ * L) = (1 - θ) * (a * G K L) ∧
      G (θ * K) (θ * L) + a * G (K - θ * K) (L - θ * L) / a = G K L := by
  have h1 := hcrs θ K L hθ0 hK hL
  have h2 := hcrs (1 - θ) K L (sub_pos.2 hθ1) hK hL
  rw [show (1 - θ) * K = K - θ * K by ring, show (1 - θ) * L = L - θ * L by ring] at h2
  refine ⟨h1, by rw [h2]; ring, ?_⟩
  rw [h1, h2]
  field_simp
  ring

/-- AKMM, box p. 50, footnote a ("a relative price `p` is implied from the production
technologies alone"): if an interior allocation `(k₁, ℓ₁)` maximises the value
`pG(k₁, ℓ₁) + aG(K − k₁, L − ℓ₁)` of output at relative price `p > 0` over all interior
allocations, and `G > 0` on the positive quadrant, then `p = a`. -/
theorem agg_price_implied {G : ℝ → ℝ → ℝ}
    (hconc : ConcaveOn ℝ aggPosQuadrant (fun q => G q.1 q.2))
    (hcrs : ∀ s x y, 0 < s → 0 < x → 0 < y → G (s * x) (s * y) = s * G x y)
    (hpos : ∀ x y, 0 < x → 0 < y → 0 < G x y)
    {a p K L k₁ ℓ₁ : ℝ} (ha : 0 < a) (hp : 0 < p) (hK : 0 < K) (hL : 0 < L)
    (hk₁ : 0 < k₁) (hl₁ : 0 < ℓ₁) (hk₂ : k₁ < K) (hl₂ : ℓ₁ < L)
    (hmax : ∀ k ℓ, 0 < k → 0 < ℓ → k < K → ℓ < L →
      p * G k ℓ + a * G (K - k) (L - ℓ) ≤ p * G k₁ ℓ₁ + a * G (K - k₁) (L - ℓ₁)) :
    p = a := by
  set V := p * G k₁ ℓ₁ + a * G (K - k₁) (L - ℓ₁) with hV
  -- the value along proportional allocations is `G(K, L)(a + θ(p − a))`
  have hprop : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, G K L * (a + θ * (p - a)) ≤ V := by
    intro θ hθ
    obtain ⟨h1, h2, -⟩ := agg_frontier_attained hcrs ha hK hL hθ.1 hθ.2
    have := hmax (θ * K) (θ * L) (mul_pos hθ.1 hK) (mul_pos hθ.1 hL)
      (by nlinarith [hθ.2]) (by nlinarith [hθ.2])
    rw [h1, h2] at this
    linarith
  have hcont : Continuous fun θ : ℝ => G K L * (a + θ * (p - a)) := by fun_prop
  -- letting `θ → 1` and `θ → 0`
  have hpG : G K L * p ≤ V := by
    have ht : Tendsto (fun θ : ℝ => G K L * (a + θ * (p - a))) (𝓝[<] 1)
        (𝓝 (G K L * (a + 1 * (p - a)))) := hcont.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have hle := le_of_tendsto ht (by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
      exact hprop θ hθ)
    linarith
  have haG : G K L * a ≤ V := by
    have ht : Tendsto (fun θ : ℝ => G K L * (a + θ * (p - a))) (𝓝[>] 0)
        (𝓝 (G K L * (a + 0 * (p - a)))) := hcont.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have hle := le_of_tendsto ht (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
      exact hprop θ hθ)
    linarith
  have hfr := agg_frontier_bound hconc hcrs ha hk₁ hl₁ hk₂ hl₂
  rw [mul_div_cancel_left₀ _ ha.ne'] at hfr
  have hx₁ := hpos k₁ ℓ₁ hk₁ hl₁
  have hx₂ := hpos (K - k₁) (L - ℓ₁) (sub_pos.2 hk₂) (sub_pos.2 hl₂)
  -- `p ≤ a`: from `p(x₁ + x₂/a) ≤ pG ≤ px₁ + x₂` with `x₂ = aG(K − k₁, L − ℓ₁) > 0`
  have h1 : p ≤ a := by
    by_contra hlt'
    have hlt := lt_of_not_ge hlt'
    nlinarith [mul_lt_mul_of_pos_right hlt hx₂]
  -- `a ≤ p`: from `a(x₁ + x₂/a) ≤ aG ≤ px₁ + x₂` with `x₁ > 0`
  have h2 : a ≤ p := by
    by_contra hlt'
    have hlt := lt_of_not_ge hlt'
    nlinarith [mul_lt_mul_of_pos_right hlt hx₁]
  exact le_antisymm h1 h2

/-- AKMM, box p. 50, footnote a (the price-independent mapping): at the implied price `p = a`,
the value of output is maximised exactly by the allocations with
`x₁ + x₂/a = G(K, L)` — in particular by every proportional allocation — and its maximal value is
`aG(K, L)`. So output in units of good 1, `x₁ + x₂/a`, is `G(K, L)` at every value-maximising
allocation: an aggregate production function independent of prices and preferences. -/
theorem agg_aggregate_production {G : ℝ → ℝ → ℝ}
    (hconc : ConcaveOn ℝ aggPosQuadrant (fun q => G q.1 q.2))
    (hcrs : ∀ s x y, 0 < s → 0 < x → 0 < y → G (s * x) (s * y) = s * G x y)
    {a K L : ℝ} (ha : 0 < a) (hK : 0 < K) (hL : 0 < L) :
    (∀ k ℓ, 0 < k → 0 < ℓ → k < K → ℓ < L → a * G k ℓ + a * G (K - k) (L - ℓ) ≤ a * G K L) ∧
      (∀ θ, 0 < θ → θ < 1 →
        a * G (θ * K) (θ * L) + a * G (K - θ * K) (L - θ * L) = a * G K L) ∧
      (∀ k ℓ, 0 < k → 0 < ℓ → k < K → ℓ < L →
        (a * G k ℓ + a * G (K - k) (L - ℓ) = a * G K L ↔
          G k ℓ + a * G (K - k) (L - ℓ) / a = G K L)) := by
  refine ⟨fun k ℓ hk hl hkK hlL => ?_, fun θ h0 h1 => ?_, fun k ℓ hk hl hkK hlL => ?_⟩
  · have := agg_frontier_bound hconc hcrs ha hk hl hkK hlL
    rw [mul_div_cancel_left₀ _ ha.ne'] at this
    nlinarith
  · obtain ⟨-, -, h⟩ := agg_frontier_attained hcrs ha hK hL h0 h1
    rw [mul_div_cancel_left₀ _ ha.ne'] at h
    rw [← h]
    ring
  · rw [mul_div_cancel_left₀ _ ha.ne', ← mul_add]
    exact ⟨fun h => mul_left_cancel₀ ha.ne' h, fun h => by rw [h]⟩

end AKMM.Framework

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.RDEuler
import Mathlib.Analysis.Convex.Deriv

/-!
# Exercise 13.4: first-order and transversality conditions

Miao, Exercise 13.4, p. 452, for the discounted expected utility (13.1) with a differentiable
utility `u` (derivative `u′`) satisfying the gradient inequality of concavity
`u(x′) ≤ u(x) + u′(x)(x′ − x)` (`x > 0`, `x′ ≥ 0`; `rd_gradIneq_of_concave` derives it from
`ConcaveOn` and differentiability, and `rd_sqrt_gradIneq` checks it for `√·`).

Necessity of the first-order conditions (Kuhn–Tucker form, at a node with positive
consumption there and at the successors):
* borrowing constraints (13.14): `u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + μₜ pₜ`, `μₜ ≥ 0`,
  `μₜ (pₜ · θₜ + B̄ₜ) = 0` (`ex_13_4_BC_foc`);
* short-sales constraints (13.15): `u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + νₜ`, `νₜ ≥ 0`,
  `νₜⱼ (θₜⱼ + h̄ₜⱼ) = 0` (`ex_13_4_SC_foc`);
* debt constraints (13.13), when the payoff matrix has rank `S` at the node:
  `u′(cₜ) pₜ = ∑ₛ (β Pr(s|sᵗ) u′(c_{t+1}) + ηₛ) f_{t+1}`, `ηₛ ≥ 0`,
  `ηₛ (f_{t+1} · θₜ + D̄_{t+1}) = 0` (`ex_13_4_DC_foc`). Without rank `S` this needs Farkas'
  lemma and is not formalised.

Sufficiency: the budget equalities, the first-order conditions and the transversality condition
(13.39) (`ex_13_4_BC_suff`), (13.40) (`ex_13_4_SC_suff`, read as
`lim E βᵀ u′(c_T) p_T · (θ_T + h̄_T) = 0`, the book's `p_T · θ_T + h̄_T` mixing a scalar and a
vector) or (13.38) (`ex_13_4_DC_suff`) imply optimality; with market clearing they characterise
an equilibrium (`ex_13_4_BC_eqm`). The proof telescopes the budget constraints weighted by
`ξ = βᵗ Pr u′(c)` (`rd_telescope`). Necessity of the transversality conditions is not
formalised.
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J : Type*} [Fintype S] [Fintype J]

/-- The gradient inequality of a concave differentiable utility on `[0, ∞)`. -/
def rd_GradIneq (u u' : ℝ → ℝ) : Prop := ∀ x, 0 < x → ∀ x', 0 ≤ x' → u x' ≤ u x + u' x * (x' - x)

/-- A concave utility on `[0, ∞)`, differentiable on `(0, ∞)`, satisfies the gradient
inequality. -/
theorem rd_gradIneq_of_concave {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ici 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) : rd_GradIneq u u' := by
  intro x hx x' hx'
  rcases lt_trichotomy x' x with hlt | heq | hgt
  · have := ConcaveOn.le_slope_of_hasDerivAt hc (Set.mem_Ici.2 hx') (Set.mem_Ici.2 hx.le) hlt
      (hd x hx)
    rw [slope_def_field] at this
    have hpos : 0 < x - x' := by linarith
    rw [le_div_iff₀ hpos] at this
    nlinarith
  · rw [heq]
    simp
  · have := ConcaveOn.slope_le_of_hasDerivAt hc (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 hx') hgt
      (hd x hx)
    rw [slope_def_field] at this
    have hpos : 0 < x' - x := by linarith
    rw [div_le_iff₀ hpos] at this
    nlinarith

/-- `√·` satisfies the gradient inequality with `u′(x) = 1/(2√x)`. -/
theorem rd_sqrt_gradIneq : rd_GradIneq Real.sqrt fun x => 1 / (2 * Real.sqrt x) := by
  intro x hx x' hx'
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 := Real.sq_sqrt hx.le
  have h2 := Real.sq_sqrt hx'
  rw [show 1 / (2 * Real.sqrt x) * (x' - x) = (x' - x) / (2 * Real.sqrt x) by ring,
    ← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt x' - Real.sqrt x), Real.sqrt_nonneg x']

/-- Over date-`T` nodes, a factor `β^{len}` is the constant `β^T`. -/
theorem rd_dsum_pow (β : ℝ) (F : List S → ℝ) (T : ℕ) :
    rd_dsum (fun g => β ^ g.length * F g) [] T = β ^ T * rd_dsum F [] T := by
  rw [rd_dsum, rd_dsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [rd_mem_paths] at hl
  simp [hl]

omit [Fintype S] in
/-- The net cash flows of two strategies differ by the net cash flow of their difference. -/
theorem rd_net_sub (p f : List S → J → ℝ) (θm1 : J → ℝ) (θ θ' : List S → J → ℝ)
    (g : List S) : rd_net p f θm1 θ' g - rd_net p f θm1 θ g = rd_net p f 0 (θ' - θ) g := by
  cases g with
  | nil => simp [rd_net, rd_prev, dotProduct_sub]
  | cons s g => simp [rd_net, rd_prev, rd_fz, dotProduct_sub]; ring

/-- Telescoping the cash flows of a strategy `Δ` (with `Δ_{−1} = 0`) weighted by `ξ`. -/
theorem rd_telescope (p f : List S → J → ℝ) (ξ : List S → ℝ) (Δ : List S → J → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), rd_dsum (fun g => ξ g * rd_net p f 0 Δ g) [] t =
      ∑ t ∈ Finset.range T, rd_dsum (fun g => ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ Δ g) -
        ξ g * (p g ⬝ᵥ Δ g)) [] t - rd_dsum (fun g => ξ g * (p g ⬝ᵥ Δ g)) [] T := by
  induction T with
  | zero => simp [rd_dsum_zero, rd_net, rd_prev]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have e : rd_dsum (fun g => ξ g * rd_net p f 0 Δ g) [] (T + 1) =
        rd_dsum (fun g => ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ Δ g)) [] T -
          rd_dsum (fun g => ξ g * (p g ⬝ᵥ Δ g)) [] (T + 1) := by
      have h1 : rd_dsum (fun g => ξ g * (rd_fz p f g ⬝ᵥ rd_prev Δ 0 g)) [] (T + 1) =
          rd_dsum (fun g => ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ Δ g)) [] T := rd_dsum_succ' _ _ _
      rw [← h1, ← rd_dsum_sub]
      exact rd_dsum_congr (fun g => by simp only [rd_net]; ring) _ _
    rw [e, rd_dsum_sub]
    ring

/-- The first-order condition with a multiplier vector `e`, multiplied by `ξ = βᵗ Pr u′(c)` and
applied to a portfolio `v`: `ξₜ (pₜ · v) = ∑ₛ ξ_{t+1} (f_{t+1} · v) + βᵗ Pr (e · v)`. -/
theorem rd_foc_xi (T : RDTree S) (β : ℝ) (u' : ℝ → ℝ) (p f : List S → J → ℝ)
    (c : List S → ℝ) (g : List S) (e : J → ℝ)
    (hfoc : ∀ j, u' (c g) * p g j =
      β * ∑ s, rd_condPr T g s * (u' (c (s :: g)) * f (s :: g) j) + e j) (v : J → ℝ) :
    β ^ g.length * T.Pr g * u' (c g) * (p g ⬝ᵥ v) =
      ∑ s, β ^ (s :: g).length * T.Pr (s :: g) * u' (c (s :: g)) * (f (s :: g) ⬝ᵥ v) +
        β ^ g.length * T.Pr g * (e ⬝ᵥ v) := by
  have hP := (T.pos g).ne'
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := hfoc j
  have e1 : β ^ g.length * T.Pr g * u' (c g) * (p g j * v j) =
      β ^ g.length * T.Pr g * (u' (c g) * p g j) * v j := by ring
  rw [e1, this]
  simp only [rd_condPr, Finset.mul_sum, mul_add, add_mul, Finset.sum_mul, List.length_cons,
    pow_succ]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    field_simp
  · ring

/-- The core of the sufficiency argument: if the weighted consumption gains are bounded by a
sequence with a nonpositive limit, the plan `c′` is no better than `c`. -/
theorem rd_suff_core (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : MonotoneOn u (Set.Ici 0)) (hgrad : rd_GradIneq u u') {c c' : List S → ℝ}
    (hc : rd_LinfPos c) (hc' : rd_LinfPos c') (hcpos : ∀ g, 0 < c g) {τ : ℕ → ℝ} {L : ℝ}
    (hτ : Tendsto τ atTop (𝓝 L)) (hL : L ≤ 0)
    (hbound : ∀ n, ∑ t ∈ Finset.range (n + 1),
      rd_dsum (fun g => β ^ g.length * T.Pr g * u' (c g) * (c' g - c g)) [] t ≤ τ n) :
    rd_EU T β u c' ≤ rd_EU T β u c := by
  obtain ⟨K, hK⟩ := rd_abs_u_le hu hc
  obtain ⟨K', hK'⟩ := rd_abs_u_le hu hc'
  have hs := (rd_EU_summable T hβ0.le hβ1 u hK').sub (rd_EU_summable T hβ0.le hβ1 u hK)
  have hA := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hle : rd_EU T β u c' - rd_EU T β u c ≤ L := by
    rw [rd_EU, rd_EU, ← Summable.tsum_sub (rd_EU_summable T hβ0.le hβ1 u hK')
      (rd_EU_summable T hβ0.le hβ1 u hK)]
    refine le_of_tendsto_of_tendsto' hA hτ fun n => ?_
    refine le_trans ?_ (hbound n)
    simp only [Function.comp_apply]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [← mul_sub, ← rd_dsum_sub, ← rd_dsum_pow]
    refine rd_dsum_mono (fun g => ?_) _ _
    have := hgrad (c g) (hcpos g) (c' g) (hc'.2 g)
    have hw : 0 ≤ β ^ g.length * T.Pr g := mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le
    have := mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.2 this) hw
    calc β ^ g.length * (T.Pr g * u (c' g) - T.Pr g * u (c g))
        = β ^ g.length * T.Pr g * (u (c' g) - u (c g)) := by ring
      _ ≤ β ^ g.length * T.Pr g * (u' (c g) * (c' g - c g)) := this
      _ = β ^ g.length * T.Pr g * u' (c g) * (c' g - c g) := by ring
  linarith

/-- The weighted consumption gain is bounded by the weighted net cash flow of `θ′ − θ`. -/
theorem rd_gain_le (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) {u' : ℝ → ℝ}
    (hu'0 : ∀ x, 0 < x → 0 ≤ u' x) {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ}
    {c c' : List S → ℝ} {θ θ' : List S → J → ℝ} (hcpos : ∀ g, 0 < c g)
    (hB : rd_BudgetEq p f y θm1 c θ) (hB' : rd_Budget p f y θm1 c' θ') (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1),
        rd_dsum (fun g => β ^ g.length * T.Pr g * u' (c g) * (c' g - c g)) [] t ≤
      ∑ t ∈ Finset.range (n + 1), rd_dsum (fun g => β ^ g.length * T.Pr g * u' (c g) *
        rd_net p f 0 (θ' - θ) g) [] t := by
  apply Finset.sum_le_sum
  intro t _
  apply rd_dsum_mono
  intro g
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le) (hu'0 _ (hcpos g)))
  rw [← rd_net_sub p f θm1 θ θ' g]
  have h1 := (rd_budget_iff_net p f y θm1 c' θ').1 hB' g
  have h2 := hB g
  simp only [rd_net] at h1 ⊢
  linarith

/-- **Exercise 13.4** (Miao, p. 452), borrowing constraints: sufficiency. Budget equalities, the
first-order conditions `u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + μₜ pₜ` with `μ ≥ 0` and
`μₜ (pₜ · θₜ + B̄ₜ) = 0`, and the transversality condition (13.39)
`lim E[βᵀ u′(c_T)(p_T · θ_T + B̄_T)] = 0` imply that `(c, θ)` is optimal. -/
theorem ex_13_4_BC_suff (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : MonotoneOn u (Set.Ici 0)) (hgrad : rd_GradIneq u u') (hu'0 : ∀ x, 0 < x → 0 ≤ u' x)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Bbar : List S → ℝ}
    {c : List S → ℝ} {θ : List S → J → ℝ} (hc : rd_LinfPos c) (hcpos : ∀ g, 0 < c g)
    (hB : rd_BudgetEq p f y θm1 c θ) (hθ : θ ∈ rd_ThetaBC p Bbar) {μ : List S → ℝ}
    (hμ0 : ∀ h, 0 ≤ μ h) (hcs : ∀ h, μ h * (p h ⬝ᵥ θ h + Bbar h) = 0)
    (hfoc : ∀ h j, u' (c h) * p h j =
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j) + μ h * p h j)
    (htvc : Tendsto (fun n => β ^ n * rd_dsum (fun g => T.Pr g * (u' (c g) *
      (p g ⬝ᵥ θ g + Bbar g))) [] n) atTop (𝓝 0)) :
    rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaBC p Bbar)) c θ := by
  refine ⟨⟨hc, fun h => (hB h).le, hθ⟩, fun c' θ' ⟨hc', hB', hθ'⟩ => ?_⟩
  set ξ : List S → ℝ := fun g => β ^ g.length * T.Pr g * u' (c g)
  have hξ : ∀ g, 0 ≤ ξ g := fun g =>
    mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le) (hu'0 _ (hcpos g))
  refine rd_suff_core T hβ0 hβ1 hu hgrad hc hc' hcpos htvc le_rfl fun n => ?_
  refine (rd_gain_le T hβ0 hu'0 hcpos hB hB' n).trans ?_
  rw [rd_telescope]
  have hX : ∀ g, ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g) ≤ 0 := by
    intro g
    have := rd_foc_xi T β u' p f c g (μ g • p g) (fun j => by
      rw [hfoc g j]; simp) ((θ' - θ) g)
    simp only [ξ]
    rw [this]
    have hm : 0 ≤ β ^ g.length * T.Pr g * (μ g • p g ⬝ᵥ (θ' - θ) g) := by
      refine mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le) ?_
      simp only [smul_dotProduct, smul_eq_mul, Pi.sub_apply, dotProduct_sub]
      have := hcs g
      have := mul_nonneg (hμ0 g) (by linarith [hθ' g] : 0 ≤ p g ⬝ᵥ θ' g + Bbar g)
      nlinarith
    linarith
  have hterm : -rd_dsum (fun g => ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] n ≤
      β ^ n * rd_dsum (fun g => T.Pr g * (u' (c g) * (p g ⬝ᵥ θ g + Bbar g))) [] n := by
    rw [← rd_dsum_pow, ← rd_dsum_neg]
    refine rd_dsum_mono (fun g => ?_) _ _
    simp only [ξ, Pi.sub_apply, dotProduct_sub]
    have := mul_nonneg (hξ g) (by linarith [hθ' g] : 0 ≤ p g ⬝ᵥ θ' g + Bbar g)
    simp only [ξ] at this
    nlinarith
  have hsum : ∑ t ∈ Finset.range n, rd_dsum (fun g => ∑ s, ξ (s :: g) *
      (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] t ≤ 0 :=
    Finset.sum_nonpos fun t _ => by
      have := rd_dsum_mono hX [] t
      simpa [rd_dsum] using this
  linarith

/-- **Exercise 13.4** (Miao, p. 452), short-sales constraints: sufficiency. Budget equalities,
`u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + νₜ` with `ν ≥ 0`, `νₜⱼ (θₜⱼ + h̄ₜⱼ) = 0`, nonnegative
prices, and the transversality condition (13.40) `lim E[βᵀ u′(c_T) p_T · (θ_T + h̄_T)] = 0`
imply that `(c, θ)` is optimal. -/
theorem ex_13_4_SC_suff (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : MonotoneOn u (Set.Ici 0)) (hgrad : rd_GradIneq u u') (hu'0 : ∀ x, 0 < x → 0 ≤ u' x)
    {p f : List S → J → ℝ} (hp0 : ∀ h j, 0 ≤ p h j) {y : List S → ℝ} {θm1 : J → ℝ}
    {hbar : List S → J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ} (hc : rd_LinfPos c)
    (hcpos : ∀ g, 0 < c g) (hB : rd_BudgetEq p f y θm1 c θ) (hθ : θ ∈ rd_ThetaSC hbar)
    {ν : List S → J → ℝ} (hν0 : ∀ h j, 0 ≤ ν h j) (hcs : ∀ h j, ν h j * (θ h j + hbar h j) = 0)
    (hfoc : ∀ h j, u' (c h) * p h j =
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j) + ν h j)
    (htvc : Tendsto (fun n => β ^ n * rd_dsum (fun g => T.Pr g * (u' (c g) *
      (p g ⬝ᵥ (θ g + hbar g)))) [] n) atTop (𝓝 0)) :
    rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaSC hbar)) c θ := by
  refine ⟨⟨hc, fun h => (hB h).le, hθ⟩, fun c' θ' ⟨hc', hB', hθ'⟩ => ?_⟩
  set ξ : List S → ℝ := fun g => β ^ g.length * T.Pr g * u' (c g)
  have hξ : ∀ g, 0 ≤ ξ g := fun g =>
    mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le) (hu'0 _ (hcpos g))
  refine rd_suff_core T hβ0 hβ1 hu hgrad hc hc' hcpos htvc le_rfl fun n => ?_
  refine (rd_gain_le T hβ0 hu'0 hcpos hB hB' n).trans ?_
  rw [rd_telescope]
  have hX : ∀ g, ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g) ≤ 0 := by
    intro g
    have := rd_foc_xi T β u' p f c g (ν g) (hfoc g) ((θ' - θ) g)
    simp only [ξ]
    rw [this]
    have hm : 0 ≤ ν g ⬝ᵥ (θ' - θ) g := by
      refine Finset.sum_nonneg fun j _ => ?_
      simp only [Pi.sub_apply]
      have := hcs g j
      have := mul_nonneg (hν0 g j) (by linarith [hθ' g j] : 0 ≤ θ' g j + hbar g j)
      nlinarith
    have := mul_nonneg (mul_nonneg (pow_nonneg hβ0.le g.length) (T.pos g).le) hm
    linarith
  have hterm : -rd_dsum (fun g => ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] n ≤
      β ^ n * rd_dsum (fun g => T.Pr g * (u' (c g) * (p g ⬝ᵥ (θ g + hbar g)))) [] n := by
    rw [← rd_dsum_pow, ← rd_dsum_neg]
    refine rd_dsum_mono (fun g => ?_) _ _
    have hpos : 0 ≤ p g ⬝ᵥ (θ' g + hbar g) := Finset.sum_nonneg fun j _ =>
      mul_nonneg (hp0 g j) (by simp only [Pi.add_apply]; linarith [hθ' g j])
    have e : p g ⬝ᵥ (θ' - θ) g = p g ⬝ᵥ (θ' g + hbar g) - p g ⬝ᵥ (θ g + hbar g) := by
      simp only [Pi.sub_apply, dotProduct_sub, dotProduct_add]
      ring
    rw [e]
    have := mul_nonneg (hξ g) hpos
    simp only [ξ] at this ⊢
    nlinarith
  have hsum : ∑ t ∈ Finset.range n, rd_dsum (fun g => ∑ s, ξ (s :: g) *
      (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] t ≤ 0 :=
    Finset.sum_nonpos fun t _ => by
      have := rd_dsum_mono hX [] t
      simpa [rd_dsum] using this
  linarith

/-- **Exercise 13.4** (Miao, p. 452), debt constraints: sufficiency. Budget equalities,
`u′(cₜ) pₜ = ∑ₛ (β Pr(s|sᵗ) u′(c_{t+1}) + η_{t+1}) f_{t+1}` with `η ≥ 0`,
`η_{t+1} (f_{t+1} · θₜ + D̄_{t+1}) = 0`, and the transversality condition (13.38)
`lim E[β^{T+1} u′(c_{T+1})(f_{T+1} · θ_T + D̄_{T+1})] = 0` imply that `(c, θ)` is optimal.
The multiplier `η (s :: h)` belongs to the debt constraint at the successor `(sᵗ, s)`. -/
theorem ex_13_4_DC_suff (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : MonotoneOn u (Set.Ici 0)) (hgrad : rd_GradIneq u u') (hu'0 : ∀ x, 0 < x → 0 ≤ u' x)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Dbar : List S → ℝ}
    {c : List S → ℝ} {θ : List S → J → ℝ} (hc : rd_LinfPos c) (hcpos : ∀ g, 0 < c g)
    (hB : rd_BudgetEq p f y θm1 c θ) (hθ : θ ∈ rd_ThetaDC f Dbar) {η : List S → ℝ}
    (hη0 : ∀ h, 0 ≤ η h) (hcs : ∀ h s, η (s :: h) * (f (s :: h) ⬝ᵥ θ h + Dbar (s :: h)) = 0)
    (hfoc : ∀ h j, u' (c h) * p h j =
      ∑ s, (β * rd_condPr T h s * u' (c (s :: h)) + η (s :: h)) * f (s :: h) j)
    (htvc : Tendsto (fun n => rd_dsum (fun g => ∑ s, β ^ (n + 1) * T.Pr (s :: g) *
      u' (c (s :: g)) * (f (s :: g) ⬝ᵥ θ g + Dbar (s :: g))) [] n) atTop (𝓝 0)) :
    rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaDC f Dbar)) c θ := by
  refine ⟨⟨hc, fun h => (hB h).le, hθ⟩, fun c' θ' ⟨hc', hB', hθ'⟩ => ?_⟩
  set ξ : List S → ℝ := fun g => β ^ g.length * T.Pr g * u' (c g)
  have hξ : ∀ g, 0 ≤ ξ g := fun g =>
    mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le) (hu'0 _ (hcpos g))
  have hfoc' : ∀ g j, u' (c g) * p g j = β * ∑ s, rd_condPr T g s *
      (u' (c (s :: g)) * f (s :: g) j) + ∑ s, η (s :: g) * f (s :: g) j := by
    intro g j
    rw [hfoc g j, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hdotη : ∀ g (v : J → ℝ), (fun j => ∑ s, η (s :: g) * f (s :: g) j) ⬝ᵥ v =
      ∑ s, η (s :: g) * (f (s :: g) ⬝ᵥ v) := by
    intro g v
    simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring
  have hηΔ : ∀ g, 0 ≤ ∑ s, η (s :: g) * (f (s :: g) ⬝ᵥ (θ' - θ) g) := by
    intro g
    refine Finset.sum_nonneg fun s _ => ?_
    simp only [Pi.sub_apply, dotProduct_sub]
    have := hcs g s
    have := mul_nonneg (hη0 (s :: g)) (by linarith [hθ' g s] :
      0 ≤ f (s :: g) ⬝ᵥ θ' g + Dbar (s :: g))
    nlinarith
  have hxi : ∀ g (v : J → ℝ), ξ g * (p g ⬝ᵥ v) = ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ v) +
      β ^ g.length * T.Pr g * ∑ s, η (s :: g) * (f (s :: g) ⬝ᵥ v) := by
    intro g v
    have := rd_foc_xi T β u' p f c g _ (hfoc' g) v
    rw [hdotη] at this
    exact this
  refine rd_suff_core T hβ0 hβ1 hu hgrad hc hc' hcpos htvc le_rfl fun n => ?_
  refine (rd_gain_le T hβ0 hu'0 hcpos hB hB' n).trans ?_
  rw [rd_telescope]
  have hX : ∀ g, ∑ s, ξ (s :: g) * (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g) ≤ 0 := by
    intro g
    rw [hxi]
    have := mul_nonneg (mul_nonneg (pow_nonneg hβ0.le g.length) (T.pos g).le) (hηΔ g)
    linarith
  have hterm : -rd_dsum (fun g => ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] n ≤
      rd_dsum (fun g => ∑ s, β ^ (n + 1) * T.Pr (s :: g) * u' (c (s :: g)) *
        (f (s :: g) ⬝ᵥ θ g + Dbar (s :: g))) [] n := by
    rw [← rd_dsum_neg]
    unfold rd_dsum
    refine Finset.sum_le_sum fun l hl => ?_
    rw [rd_mem_paths] at hl
    simp only [List.append_nil]
    rw [hxi]
    have h1 := mul_nonneg (mul_nonneg (pow_nonneg hβ0.le l.length) (T.pos l).le) (hηΔ l)
    have h2 : -∑ s, ξ (s :: l) * (f (s :: l) ⬝ᵥ (θ' - θ) l) ≤ ∑ s, β ^ (n + 1) *
        T.Pr (s :: l) * u' (c (s :: l)) * (f (s :: l) ⬝ᵥ θ l + Dbar (s :: l)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      have hpos := mul_nonneg (hξ (s :: l)) (by linarith [hθ' l s] :
        0 ≤ f (s :: l) ⬝ᵥ θ' l + Dbar (s :: l))
      simp only [ξ, List.length_cons, hl, Pi.sub_apply, dotProduct_sub] at hpos ⊢
      nlinarith
    linarith
  have hsum : ∑ t ∈ Finset.range n, rd_dsum (fun g => ∑ s, ξ (s :: g) *
      (f (s :: g) ⬝ᵥ (θ' - θ) g) - ξ g * (p g ⬝ᵥ (θ' - θ) g)) [] t ≤ 0 :=
    Finset.sum_nonpos fun t _ => by
      have := rd_dsum_mono hX [] t
      simpa [rd_dsum] using this
  linarith

/-- **Exercise 13.4**, borrowing constraints: the conditions of `ex_13_4_BC_suff` for every
agent, with market clearing, characterise a Radner equilibrium with borrowing constraints. -/
theorem ex_13_4_BC_eqm {ι : Type*} [Fintype ι] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {u u' : ι → ℝ → ℝ} (hu : ∀ i, MonotoneOn (u i) (Set.Ici 0))
    (hgrad : ∀ i, rd_GradIneq (u i) (u' i)) (hu'0 : ∀ i x, 0 < x → 0 ≤ u' i x)
    {p f : List S → J → ℝ} {y : ι → List S → ℝ} {θm1 : ι → J → ℝ} {Bbar : ι → List S → ℝ}
    {c : ι → List S → ℝ} {θ : ι → List S → J → ℝ} {μ : ι → List S → ℝ}
    (hc : ∀ i, rd_LinfPos (c i)) (hcpos : ∀ i g, 0 < c i g)
    (hB : ∀ i, rd_BudgetEq p f (y i) (θm1 i) (c i) (θ i))
    (hθ : ∀ i, θ i ∈ rd_ThetaBC p (Bbar i)) (hμ0 : ∀ i h, 0 ≤ μ i h)
    (hcs : ∀ i h, μ i h * (p h ⬝ᵥ θ i h + Bbar i h) = 0)
    (hfoc : ∀ i h j, u' i (c i h) * p h j =
      β * ∑ s, rd_condPr T h s * (u' i (c i (s :: h)) * f (s :: h) j) + μ i h * p h j)
    (htvc : ∀ i, Tendsto (fun n => β ^ n * rd_dsum (fun g => T.Pr g * (u' i (c i g) *
      (p g ⬝ᵥ θ i g + Bbar i g))) [] n) atTop (𝓝 0))
    (hclear : ∀ h, ∑ i, θ i h = ∑ i, θm1 i) :
    rd_RadnerBC (fun i => rd_EU T β (u i)) y θm1 p f Bbar c θ :=
  ⟨fun i => ex_13_4_BC_suff T hβ0 hβ1 (hu i) (hgrad i) (hu'0 i) (hc i) (hcpos i) (hB i) (hθ i)
    (hμ0 i) (hcs i) (hfoc i) (htvc i), rd_goods_clearing p f y θm1 c θ hB hclear, hclear⟩

omit [Fintype S] in
/-- Feasibility of a perturbed borrowing-constrained strategy. -/
theorem rd_BC_feas [DecidableEq S] {p : List S → J → ℝ} {Bbar : List S → ℝ}
    {θ : List S → J → ℝ} (hθ : θ ∈ rd_ThetaBC p Bbar) (h : List S) (d : J → ℝ) (ε : ℝ)
    (hε : -Bbar h ≤ p h ⬝ᵥ θ h + ε * (p h ⬝ᵥ d)) : θ + ε • rd_loc d h ∈ rd_ThetaBC p Bbar := by
  intro g
  by_cases hg : g = h
  · subst hg
    simpa [rd_loc, dotProduct_add, dotProduct_smul] using hε
  · simpa [rd_loc, hg] using hθ g

/-- **Exercise 13.4** (Miao, p. 452), borrowing constraints: the first-order conditions are
necessary. At a node with positive consumption there and at the successors, and a nonzero price
vector, there is `μ ≥ 0` with `μ (pₜ · θₜ + B̄ₜ) = 0` and
`u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + μ pₜ`. -/
theorem ex_13_4_BC_foc (T : RDTree S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0))
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {p f : List S → J → ℝ} {y : List S → ℝ}
    {θm1 : J → ℝ} {Bbar : List S → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hsol : rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaBC p Bbar)) c θ)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h)) (hp : ∃ j0, p h j0 ≠ 0) :
    ∃ μ, 0 ≤ μ ∧ μ * (p h ⬝ᵥ θ h + Bbar h) = 0 ∧ ∀ j, u' (c h) * p h j =
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j) + μ * p h j := by
  classical
  have hθ := hsol.1.2.2
  set w : J → ℝ := fun j => -(u' (c h) * p h j) +
    β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j)
  have hΦ : ∀ d, rd_Phi T β u' p f c h d = w ⬝ᵥ d := fun d => rd_Phi_eq T β u' p f c h d
  -- one-sided feasibility for directions with `p · d ≥ 0`
  have hdir : ∀ d, 0 ≤ p h ⬝ᵥ d → w ⬝ᵥ d ≤ 0 := by
    intro d hd0
    rw [← hΦ]
    refine rd_euler_dir T hβ0 hβ1 hu hd hsol h hch hcs d ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact rd_BC_feas hθ h d ε (by nlinarith [hθ h, mul_nonneg (le_of_lt hε) hd0])
  have horth : ∀ d, p h ⬝ᵥ d = 0 → w ⬝ᵥ d = 0 := by
    intro d hd0
    have h1 := hdir d hd0.ge
    have h2 := hdir (-d) (by rw [dotProduct_neg, hd0, neg_zero])
    rw [dotProduct_neg] at h2
    linarith
  obtain ⟨j0, hj0⟩ := hp
  have hwj : ∀ j, w j * p h j0 = w j0 * p h j := by
    intro j
    have := horth (p h j0 • Pi.single j 1 - p h j • Pi.single j0 1) (by
      simp only [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
      ring)
    simp only [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at this
    linarith
  set lam := w j0 / p h j0
  have hw : ∀ j, w j = lam * p h j := fun j => by
    simp only [lam]
    field_simp
    linarith [hwj j]
  have hpp : 0 < p h ⬝ᵥ p h := by
    refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨j0, Finset.mem_univ _, ?_⟩
    exact mul_self_pos.2 hj0
  have hwp : w ⬝ᵥ p h = lam * (p h ⬝ᵥ p h) := by
    simp only [dotProduct, hw, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlam : lam ≤ 0 := by
    have := hdir (p h) hpp.le
    rw [hwp] at this
    by_contra hc
    push Not at hc
    exact absurd this (not_le.2 (mul_pos hc hpp))
  refine ⟨-lam, by linarith, ?_, fun j => ?_⟩
  · by_cases hbind : p h ⬝ᵥ θ h + Bbar h = 0
    · rw [hbind, mul_zero]
    · have hslack : -Bbar h < p h ⬝ᵥ θ h := by
        have := hθ h
        rcases lt_or_eq_of_le this with hlt | heq
        · exact hlt
        · exact absurd (by linarith) hbind
      have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), θ + ε • rd_loc (-p h) h ∈ rd_ThetaBC p Bbar := by
        have : Tendsto (fun ε : ℝ => p h ⬝ᵥ θ h + ε * (p h ⬝ᵥ -p h)) (𝓝 0)
            (𝓝 (p h ⬝ᵥ θ h)) := by
          simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (p h ⬝ᵥ -p h)).const_add _
        filter_upwards [this.eventually (lt_mem_nhds hslack)] with ε hε
        exact rd_BC_feas hθ h _ ε hε.le
      have := rd_euler_eq T hβ0 hβ1 hu hd hsol h hch hcs (-p h) hev
      rw [hΦ, dotProduct_neg, hwp] at this
      have : lam = 0 := by
        rcases mul_eq_zero.1 (neg_eq_zero.1 this) with h1 | h1
        · exact h1
        · exact absurd h1 hpp.ne'
      rw [this, neg_zero, zero_mul]
  · have := hw j
    simp only [w] at this
    linarith

/-- **Exercise 13.4** (Miao, p. 452), short-sales constraints: the first-order conditions are
necessary. At a node with positive consumption there and at the successors there is `ν ≥ 0`
with `νⱼ (θₜⱼ + h̄ₜⱼ) = 0` and `u′(cₜ) pₜ = β Eₜ[u′(c_{t+1}) f_{t+1}] + ν`. -/
theorem ex_13_4_SC_foc (T : RDTree S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0))
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {p f : List S → J → ℝ} {y : List S → ℝ}
    {θm1 : J → ℝ} {hbar : List S → J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hsol : rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaSC hbar)) c θ)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h)) :
    ∃ ν : J → ℝ, (∀ j, 0 ≤ ν j) ∧ (∀ j, ν j * (θ h j + hbar h j) = 0) ∧ ∀ j, u' (c h) * p h j =
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j) + ν j := by
  classical
  have hθ := hsol.1.2.2
  have hfeas : ∀ j (ε : ℝ), -hbar h j ≤ θ h j + ε →
      θ + ε • rd_loc (Pi.single j 1) h ∈ rd_ThetaSC hbar := by
    intro j ε hε g k
    by_cases hg : g = h
    · subst hg
      by_cases hk : k = j
      · subst hk
        simpa [rd_loc] using hε
      · simpa [rd_loc, hk] using hθ g k
    · simpa [rd_loc, hg] using hθ g k
  set ν : J → ℝ := fun j => -rd_Phi T β u' p f c h (Pi.single j 1)
  have hν : ∀ j, 0 ≤ ν j := by
    intro j
    have := rd_euler_dir T hβ0 hβ1 hu hd hsol h hch hcs (Pi.single j 1) (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hfeas j ε (by linarith [hθ h j, (le_of_lt hε : (0 : ℝ) ≤ ε)]))
    simp only [ν]
    unfold rd_Phi
    linarith
  refine ⟨ν, hν, fun j => ?_, fun j => ?_⟩
  · by_cases hbind : θ h j + hbar h j = 0
    · rw [hbind, mul_zero]
    · have hslack : -hbar h j < θ h j := by
        rcases lt_or_eq_of_le (hθ h j) with hlt | heq
        · exact hlt
        · exact absurd (by linarith) hbind
      have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), θ + ε • rd_loc (Pi.single j 1) h ∈ rd_ThetaSC hbar := by
        have : Tendsto (fun ε : ℝ => θ h j + ε) (𝓝 0) (𝓝 (θ h j)) := by
          simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_add (θ h j)
        filter_upwards [this.eventually (lt_mem_nhds hslack)] with ε hε
        exact hfeas j ε hε.le
      have := rd_euler_eq T hβ0 hβ1 hu hd hsol h hch hcs _ hev
      simp only [ν, this, neg_zero, zero_mul]
  · simp only [ν, rd_Phi, dotProduct_single, mul_one]
    ring

/-- **Exercise 13.4** (Miao, p. 452), debt constraints: the first-order conditions are necessary
when the payoff matrix has rank `S` at the node. There are `ηₛ ≥ 0` with
`ηₛ (f_{t+1}(sᵗ, s) · θₜ + D̄_{t+1}(sᵗ, s)) = 0` and
`u′(cₜ) pₜ = ∑ₛ (β Pr(s|sᵗ) u′(c_{t+1}) + ηₛ) f_{t+1}(sᵗ, s)`. -/
theorem ex_13_4_DC_foc (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Dbar : List S → ℝ}
    {c : List S → ℝ} {θ : List S → J → ℝ}
    (hsol : rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 (rd_ThetaDC f Dbar)) c θ)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h))
    (hrank : (rd_payoffMatrix f h).rank = Fintype.card S) :
    ∃ η : S → ℝ, (∀ s, 0 ≤ η s) ∧ (∀ s, η s * (f (s :: h) ⬝ᵥ θ h + Dbar (s :: h)) = 0) ∧
      ∀ j, u' (c h) * p h j =
        ∑ s, (β * rd_condPr T h s * u' (c (s :: h)) + η s) * f (s :: h) j := by
  classical
  have hθ := hsol.1.2.2
  set w : J → ℝ := fun j => -(u' (c h) * p h j) +
    β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j)
  have hΦ : ∀ d, rd_Phi T β u' p f c h d = w ⬝ᵥ d := fun d => rd_Phi_eq T β u' p f c h d
  have hfeas : ∀ d (ε : ℝ), (∀ s, -Dbar (s :: h) ≤ f (s :: h) ⬝ᵥ θ h + ε * (f (s :: h) ⬝ᵥ d)) →
      θ + ε • rd_loc d h ∈ rd_ThetaDC f Dbar := by
    intro d ε hε g s
    by_cases hg : g = h
    · subst hg
      simpa [rd_loc, dotProduct_add, dotProduct_smul] using hε s
    · simpa [rd_loc, hg] using hθ g s
  -- the spanning portfolios `d s` with `f(sᵗ, s′) · d s = δ_{s s′}`
  have hspan := (rd_rank_iff_span f h).1 hrank
  choose dd hdd using fun s : S => hspan fun s' => if s' = s then 1 else 0
  -- slackness is an open condition
  have hslack_ev : ∀ d, ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h →
      -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h + ε * (f (s :: h) ⬝ᵥ d) := by
    intro d
    refine Filter.eventually_all.2 fun s => ?_
    by_cases hs : -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h
    · have : Tendsto (fun ε : ℝ => f (s :: h) ⬝ᵥ θ h + ε * (f (s :: h) ⬝ᵥ d)) (𝓝 0)
          (𝓝 (f (s :: h) ⬝ᵥ θ h)) := by
        simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (f (s :: h) ⬝ᵥ d)).const_add _
      filter_upwards [this.eventually (lt_mem_nhds hs)] with ε hε _
      exact hε
    · exact Filter.Eventually.of_forall fun ε h' => absurd h' hs
  -- directions in the kernel have zero marginal value
  have hker : ∀ d, (∀ s, f (s :: h) ⬝ᵥ d = 0) → w ⬝ᵥ d = 0 := by
    intro d hd0
    rw [← hΦ]
    refine rd_euler_eq T hβ0 hβ1 hu hd hsol h hch hcs d (Filter.Eventually.of_forall
      fun ε => hfeas d ε fun s => ?_)
    rw [hd0 s, mul_zero, add_zero]
    exact hθ h s
  set η : S → ℝ := fun s => -(w ⬝ᵥ dd s)
  have hη : ∀ s, 0 ≤ η s := by
    intro s
    have := rd_euler_dir T hβ0 hβ1 hu hd hsol h hch hcs (dd s) (by
      filter_upwards [nhdsWithin_le_nhds (hslack_ev (dd s)), self_mem_nhdsWithin] with ε hε hpos
      refine hfeas _ ε fun s' => ?_
      by_cases hs' : -Dbar (s' :: h) < f (s' :: h) ⬝ᵥ θ h
      · exact (hε s' hs').le
      · rw [hdd s s']
        have := hθ h s'
        split_ifs <;> nlinarith [(le_of_lt hpos : (0 : ℝ) ≤ ε)])
    have this : rd_Phi T β u' p f c h (dd s) ≤ 0 := this
    rw [hΦ] at this
    simp only [η]
    linarith
  have hηs : ∀ s, η s * (f (s :: h) ⬝ᵥ θ h + Dbar (s :: h)) = 0 := by
    intro s
    by_cases hbind : f (s :: h) ⬝ᵥ θ h + Dbar (s :: h) = 0
    · rw [hbind, mul_zero]
    · have hs : -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h := by
        rcases lt_or_eq_of_le (hθ h s) with hlt | heq
        · exact hlt
        · exact absurd (by linarith) hbind
      have := rd_euler_eq T hβ0 hβ1 hu hd hsol h hch hcs (dd s) (by
        filter_upwards [hslack_ev (dd s)] with ε hε
        refine hfeas _ ε fun s' => ?_
        by_cases hs' : -Dbar (s' :: h) < f (s' :: h) ⬝ᵥ θ h
        · exact (hε s' hs').le
        · have hne : s' ≠ s := fun e => hs' (e ▸ hs)
          simp only [hdd s s', hne, ↓reduceIte, mul_zero, add_zero]
          exact hθ h s')
      rw [hΦ] at this
      simp only [η, this, neg_zero, zero_mul]
  refine ⟨η, hη, hηs, fun j => ?_⟩
  -- `e_j − ∑ₛ f_j(sᵗ, s) dd s` lies in the kernel
  have hk := hker (Pi.single j 1 - ∑ s, f (s :: h) j • dd s) (fun s' => by
    simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, dotProduct_single, mul_one,
      smul_eq_mul, hdd, mul_ite, mul_zero]
    simp)
  simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, dotProduct_single, mul_one,
    smul_eq_mul] at hk
  have hwj : w j = -∑ s, f (s :: h) j * η s := by
    simp only [η, mul_neg, Finset.sum_neg_distrib, neg_neg]
    linarith
  simp only [w] at hwj
  have e : ∑ s, (β * rd_condPr T h s * u' (c (s :: h)) + η s) * f (s :: h) j =
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j) + ∑ s, f (s :: h) j * η s := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  linarith

end Miao.CompleteMarkets

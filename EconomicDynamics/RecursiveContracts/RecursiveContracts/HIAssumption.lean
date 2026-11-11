/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.HIBasics
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# Assumption 22.3.1 and the DARA step of Proposition 22.3.1

Miao, §22.3, pp. 788 and 791–793.

* `assumption_22_3_1 u u' u''` (Assumption 22.3.1): `u' > 0`, `u'' < 0`, `sup u < ∞`,
  `inf u = −∞`, `u' → ∞` at the lower end of the domain, and decreasing absolute risk aversion
  `−u''/u'`. The domain is `ℝ` (the book's `a = −∞`, see `HIBasics`).
* `hi_cara_assumption_22_3_1`: the CARA utility of Exercise 22.4 satisfies it (so the assumption
  is not vacuous); `hi_modelOfAssumption` builds an `HIModel` from any utility satisfying it.
* `hi_dara_ratio_mono`: under DARA the ratio `u'(x + d)/u'(x)` is increasing in `x` (`d ≥ 0`).
* `hi_dara_ce`: the key DARA inequality of p. 792. If `u(x*) = δu(x⁰) + (1 − δ)u(x¹)` then
  `u(x* + d) ≤ δu(x⁰ + d) + (1 − δ)u(x¹ + d)` for `d ≥ 0` (the risk premium decreases with
  income). It is proved from the ratio monotonicity with Cauchy's mean value theorem.
* The averaged contract of p. 792: `hi_exists_mix` (the transfer `c*ᵢ` exists),
  `hi_mix_c_le` (`c*ᵢ ≤ δc⁰ᵢ + (1 − δ)c¹ᵢ`), `hi_mix_agentValue` (it delivers
  `δv⁰ + (1 − δ)v¹`), `hi_mix_principal_ge` (the principal gets at least the average against a
  concave continuation), `hi_mix_C_eq` (the displayed identity for `C*ᵢ,ᵢ₋₁`), and
  `hi_mix_downward` (all downward constraints of the averaged contract hold).
-/

namespace Miao.RecursiveContracts

open Finset Filter

/-- **Assumption 22.3.1** (Miao, p. 788). `u' > 0`, `u'' < 0`, `sup u < ∞`, `inf u = −∞`,
`lim u' = ∞` at the lower end of the domain (here `−∞`), and `−u''/u'` is decreasing (DARA);
`u'` and `u''` are the first two derivatives of `u`. -/
def assumption_22_3_1 (u u' u'' : ℝ → ℝ) : Prop :=
  (∀ x, HasDerivAt u (u' x) x) ∧ (∀ x, HasDerivAt u' (u'' x) x) ∧ (∀ x, 0 < u' x) ∧
    (∀ x, u'' x < 0) ∧ BddAbove (Set.range u) ∧ ¬ BddBelow (Set.range u) ∧
    Tendsto u' atBot atTop ∧ Antitone (fun x => -u'' x / u' x)

/-- The CARA utility `−exp(−γc)`, `γ > 0`, satisfies Assumption 22.3.1, with
`u' = γ exp(−γc)`, `u'' = −γ² exp(−γc)` and constant absolute risk aversion `γ`. -/
theorem hi_cara_assumption_22_3_1 {γ : ℝ} (hγ : 0 < γ) :
    assumption_22_3_1 (hi_cara γ) (fun x => γ * Real.exp (-γ * x))
      (fun x => -(γ ^ 2) * Real.exp (-γ * x)) := by
  have hd : ∀ x, HasDerivAt (fun x => -γ * x) (-γ) x := fun x => by
    simpa using (hasDerivAt_id x).const_mul (-γ)
  refine ⟨fun x => ?_, fun x => ?_, fun x => by positivity, fun x => ?_, ⟨0, ?_⟩,
    hi_cara_not_bddBelow hγ, ?_, ?_⟩
  · have := ((hd x).exp).neg
    unfold hi_cara
    convert this using 1; ring
  · have := ((hd x).exp).const_mul γ
    convert this using 1; ring
  · have := Real.exp_pos (-γ * x); nlinarith [sq_pos_of_pos hγ]
  · rintro _ ⟨x, rfl⟩; unfold hi_cara; linarith [Real.exp_pos (-γ * x)]
  · have h1 : Tendsto (fun x : ℝ => -γ * x) atBot atTop := by
      have := tendsto_neg_atBot_atTop.const_mul_atTop hγ
      simpa [neg_mul, mul_neg] using this
    exact (Real.tendsto_exp_atTop.comp h1).const_mul_atTop hγ
  · intro x y _
    have e : ∀ z, -(-(γ ^ 2) * Real.exp (-γ * z)) / (γ * Real.exp (-γ * z)) = γ := fun z => by
      have := Real.exp_pos (-γ * z); field_simp
    simp only [e, le_refl]

/-- An `HIModel` built from a utility satisfying Assumption 22.3.1. -/
noncomputable def hi_modelOfAssumption {u u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 u u' u'')
    (N : ℕ) (θ prob : Fin (N + 1) → ℝ) (β : ℝ) (hθ : StrictMono θ) (hp : ∀ i, 0 < prob i)
    (hs : ∑ i, prob i = 1) (hβ0 : 0 < β) (hβ1 : β < 1) : HIModel where
  N := N
  θ := θ
  prob := prob
  β := β
  u := u
  θ_strictMono := hθ
  prob_pos := hp
  prob_sum := hs
  β_pos := hβ0
  β_lt_one := hβ1
  u_cont := continuous_iff_continuousAt.2 fun x => (hu.1 x).continuousAt
  u_strictMono := strictMono_of_deriv_pos fun x => by rw [(hu.1 x).deriv]; exact hu.2.2.1 x
  u_strictConcave := by
    have hder : deriv u = u' := funext fun x => (hu.1 x).deriv
    refine StrictAnti.strictConcaveOn_univ_of_deriv
      (continuous_iff_continuousAt.2 fun x => (hu.1 x).continuousAt) ?_
    rw [hder]
    exact strictAnti_of_deriv_neg fun x => by rw [(hu.2.1 x).deriv]; exact hu.2.2.2.1 x
  u_bddAbove := hu.2.2.2.2.1
  u_not_bddBelow := hu.2.2.2.2.2.1

/-- Miao, p. 792 (DARA): under Assumption 22.3.1 the ratio `u'(x + d)/u'(x)` is increasing in
`x` for every `d ≥ 0`. -/
theorem hi_dara_ratio_mono {u u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 u u' u'') {d : ℝ}
    (hd : 0 ≤ d) : Monotone fun x => u' (x + d) / u' x := by
  obtain ⟨-, h2, h3, -, -, -, -, h8⟩ := hu
  have hder : ∀ x, HasDerivAt (fun x => u' (x + d) / u' x)
      ((u'' (x + d) * u' x - u' (x + d) * u'' x) / u' x ^ 2) x := fun x => by
    have ha : HasDerivAt (fun x => u' (x + d)) (u'' (x + d)) x :=
      (h2 (x + d)).comp_add_const x d
    exact ha.div (h2 x) (h3 x).ne'
  refine monotone_of_deriv_nonneg (fun x => (hder x).differentiableAt) fun x => ?_
  rw [(hder x).deriv]
  have hA := h8 (show x ≤ x + d by linarith)
  simp only at hA
  have p1 := h3 x
  have p2 := h3 (x + d)
  rw [div_le_div_iff₀ p2 p1] at hA
  apply div_nonneg _ (sq_nonneg _)
  nlinarith

/-- Miao, p. 792 (DARA, "the risk premium is a decreasing function of income"): if
`u(x*) = δu(x⁰) + (1 − δ)u(x¹)` with `δ ∈ (0, 1)` and `d ≥ 0`, then
`u(x* + d) ≤ δu(x⁰ + d) + (1 − δ)u(x¹ + d)`. -/
theorem hi_dara_ce {u u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 u u' u'') {d δ x0 x1 xs : ℝ}
    (hd : 0 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hxs : u xs = δ * u x0 + (1 - δ) * u x1) :
    u (xs + d) ≤ δ * u (x0 + d) + (1 - δ) * u (x1 + d) := by
  have hmono : StrictMono u :=
    strictMono_of_deriv_pos fun x => by rw [(hu.1 x).deriv]; exact hu.2.2.1 x
  have hρ := hi_dara_ratio_mono hu hd
  have hpos := hu.2.2.1
  have hderu := hu.1
  have hderh : ∀ x, HasDerivAt (fun x => u (x + d)) (u' (x + d)) x := fun x => by
    exact (hderu (x + d)).comp_add_const x d
  have hcu : Continuous u := continuous_iff_continuousAt.2 fun x => (hderu x).continuousAt
  have hch : Continuous fun x => u (x + d) := hcu.comp (continuous_id.add continuous_const)
  -- the core case `a < s < b`, with `u s = t u a + (1 − t) u b`
  have core : ∀ a b s t : ℝ, a < b → 0 < t → t < 1 → u s = t * u a + (1 - t) * u b →
      u (s + d) ≤ t * u (a + d) + (1 - t) * u (b + d) := by
    intro a b s t hab ht0 ht1 hs
    have hua := hmono hab
    have has : a < s := hmono.lt_iff_lt.1 (by rw [hs]; nlinarith)
    have hsb : s < b := hmono.lt_iff_lt.1 (by rw [hs]; nlinarith)
    obtain ⟨ξ, hξ, e1⟩ := exists_ratio_hasDerivAt_eq_ratio_slope (fun x => u (x + d))
      (fun x => u' (x + d)) has hch.continuousOn (fun x _ => hderh x) u u' hcu.continuousOn
      (fun x _ => hderu x)
    obtain ⟨η, hη, e2⟩ := exists_ratio_hasDerivAt_eq_ratio_slope (fun x => u (x + d))
      (fun x => u' (x + d)) hsb hch.continuousOn (fun x _ => hderh x) u u' hcu.continuousOn
      (fun x _ => hderu x)
    have hξη : ξ ≤ η := by linarith [hξ.2, hη.1]
    have hr := hρ hξη
    simp only at hr
    have pξ := hpos ξ
    have pη := hpos η
    rw [div_le_div_iff₀ pξ pη] at hr
    -- slopes: `h(s) − h(a) = ρ(ξ)(u s − u a)`, `h(b) − h(s) = ρ(η)(u b − u s)`
    have k1 : u s - u a = (1 - t) * (u b - u a) := by rw [hs]; ring
    have k2 : u b - u s = t * (u b - u a) := by rw [hs]; ring
    rw [k1] at e1
    rw [k2] at e2
    have hD : 0 < u b - u a := by linarith
    -- goal: `t (h s − h a) ≤ (1 − t)(h b − h s)`
    have key : t * (u (s + d) - u (a + d)) * (u' ξ * u' η) ≤
        (1 - t) * (u (b + d) - u (s + d)) * (u' ξ * u' η) := by
      have q1 : (u (s + d) - u (a + d)) * u' ξ = (1 - t) * (u b - u a) * u' (ξ + d) := by
        linarith
      have q2 : (u (b + d) - u (s + d)) * u' η = t * (u b - u a) * u' (η + d) := by linarith
      calc t * (u (s + d) - u (a + d)) * (u' ξ * u' η)
          = t * (1 - t) * (u b - u a) * (u' (ξ + d) * u' η) := by
            rw [show t * (u (s + d) - u (a + d)) * (u' ξ * u' η) =
              t * ((u (s + d) - u (a + d)) * u' ξ) * u' η by ring, q1]; ring
        _ ≤ t * (1 - t) * (u b - u a) * (u' (η + d) * u' ξ) := by
            apply mul_le_mul_of_nonneg_left hr
            have : 0 < t * (1 - t) := by nlinarith
            positivity
        _ = (1 - t) * (u (b + d) - u (s + d)) * (u' ξ * u' η) := by
            rw [show (1 - t) * (u (b + d) - u (s + d)) * (u' ξ * u' η) =
              (1 - t) * ((u (b + d) - u (s + d)) * u' η) * u' ξ by ring, q2]; ring
    have hpp : 0 < u' ξ * u' η := mul_pos pξ pη
    have := le_of_mul_le_mul_right key hpp
    nlinarith
  rcases lt_trichotomy x0 x1 with h01 | h01 | h01
  · exact core x0 x1 xs δ h01 hδ0 hδ1 hxs
  · subst h01
    have : xs = x0 := hmono.injective (by rw [hxs]; ring)
    subst this; linarith
  · have := core x1 x0 xs (1 - δ) h01 (by linarith) (by linarith) (by rw [hxs]; ring)
    linarith

/-- Miao, p. 792: the transfer `c*ᵢ` of the averaged contract exists:
`u(θᵢ + c*ᵢ) = δu(θᵢ + c⁰ᵢ) + (1 − δ)u(θᵢ + c¹ᵢ)` has a solution for `δ ∈ [0, 1]`. -/
theorem hi_exists_mix (M : HIModel) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (c0 c1 : Fin (M.N + 1) → ℝ) : ∃ cs : Fin (M.N + 1) → ℝ, ∀ i,
      M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i) := by
  have : ∀ i, ∃ x, M.u (M.θ i + x) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i) := by
    intro i
    set y := δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i)
    set lo := min (M.θ i + c0 i) (M.θ i + c1 i)
    set hi := max (M.θ i + c0 i) (M.θ i + c1 i)
    have hlo : M.u lo ≤ y := by
      have a1 : M.u lo ≤ M.u (M.θ i + c0 i) := M.u_strictMono.monotone (min_le_left _ _)
      have a2 : M.u lo ≤ M.u (M.θ i + c1 i) := M.u_strictMono.monotone (min_le_right _ _)
      nlinarith
    have hhi : y ≤ M.u hi := by
      have a1 : M.u (M.θ i + c0 i) ≤ M.u hi := M.u_strictMono.monotone (le_max_left _ _)
      have a2 : M.u (M.θ i + c1 i) ≤ M.u hi := M.u_strictMono.monotone (le_max_right _ _)
      nlinarith
    obtain ⟨x, hx⟩ := intermediate_value_univ lo hi M.u_cont ⟨hlo, hhi⟩
    exact ⟨x - M.θ i, by simp only [add_sub_cancel]; exact hx⟩
  choose cs hcs using this
  exact ⟨cs, hcs⟩

/-- Miao, p. 792: "the concavity of `u` implies `c*ᵢ ≤ δc⁰ᵢ + (1 − δ)c¹ᵢ`". -/
theorem hi_mix_c_le (M : HIModel) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {c0 c1 cs : Fin (M.N + 1) → ℝ}
    (hcs : ∀ i, M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i))
    (i : Fin (M.N + 1)) : cs i ≤ δ * c0 i + (1 - δ) * c1 i := by
  have hc := M.u_strictConcave.concaveOn.2 (Set.mem_univ (M.θ i + c0 i))
    (Set.mem_univ (M.θ i + c1 i)) hδ0 (by linarith : 0 ≤ 1 - δ) (by ring)
  simp only [smul_eq_mul] at hc
  rw [← hcs i] at hc
  have e : δ * (M.θ i + c0 i) + (1 - δ) * (M.θ i + c1 i) = M.θ i + (δ * c0 i + (1 - δ) * c1 i) :=
    by ring
  rw [e] at hc
  have := M.u_strictMono.le_iff_le.1 hc
  linarith

/-- Miao, p. 792: the averaged contract `(c*, δw⁰ + (1 − δ)w¹)` gives the agent the promised
utility `δv⁰ + (1 − δ)v¹`. -/
theorem hi_mix_agentValue (M : HIModel) {δ : ℝ} {c0 c1 cs w0 w1 : Fin (M.N + 1) → ℝ}
    (hcs : ∀ i, M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i)) :
    hi_agentValue M cs (fun i => δ * w0 i + (1 - δ) * w1 i) =
      δ * hi_agentValue M c0 w0 + (1 - δ) * hi_agentValue M c1 w1 := by
  unfold hi_agentValue
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [hcs i]; ring

/-- Miao, p. 792: against a continuation `f` concave on `(−∞, vmax)`, the averaged contract
gives the principal at least `δ` times the value of the first contract plus `1 − δ` times the
value of the second. -/
theorem hi_mix_principal_ge (M : HIModel) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) {c0 c1 cs w0 w1 : Fin (M.N + 1) → ℝ}
    (hcs : ∀ i, M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i))
    (hw0 : ∀ i, w0 i < hi_vmax M) (hw1 : ∀ i, w1 i < hi_vmax M) :
    δ * hi_principalValue M f c0 w0 + (1 - δ) * hi_principalValue M f c1 w1 ≤
      hi_principalValue M f cs (fun i => δ * w0 i + (1 - δ) * w1 i) := by
  unfold hi_principalValue
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hc := hi_mix_c_le M hδ0 hδ1 hcs i
  have hfc := hf.2 (hw0 i) (hw1 i) hδ0 (by linarith : 0 ≤ 1 - δ) (by ring)
  simp only [smul_eq_mul] at hfc
  have hp := M.prob_pos i
  have hβ := M.β_pos
  have h3 : δ * (-c0 i + M.β * f (w0 i)) + (1 - δ) * (-c1 i + M.β * f (w1 i)) ≤
      -cs i + M.β * f (δ * w0 i + (1 - δ) * w1 i) := by
    nlinarith [mul_le_mul_of_nonneg_left hfc hβ.le]
  have h4 := mul_le_mul_of_nonneg_left h3 hp.le
  simp only
  linarith

/-- Miao, p. 792: for the averaged contract,
`C*ᵢₖ = δC⁰ᵢₖ + (1 − δ)C¹ᵢₖ + [δu(θᵢ + c⁰ₖ) + (1 − δ)u(θᵢ + c¹ₖ) − u(θᵢ + c*ₖ)]`. -/
theorem hi_mix_C_eq (M : HIModel) {δ : ℝ} {c0 c1 cs w0 w1 : Fin (M.N + 1) → ℝ}
    (hcs : ∀ i, M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i))
    (i k : Fin (M.N + 1)) :
    hi_C M cs (fun i => δ * w0 i + (1 - δ) * w1 i) i k =
      δ * hi_C M c0 w0 i k + (1 - δ) * hi_C M c1 w1 i k +
        (δ * M.u (M.θ i + c0 k) + (1 - δ) * M.u (M.θ i + c1 k) - M.u (M.θ i + cs k)) := by
  unfold hi_C
  rw [hcs i]; ring

/-- Miao, p. 792: under Assumption 22.3.1 (DARA), if both contracts satisfy the downward
constraint `Cᵢₖ ≥ 0` (`k ≤ i`), so does the averaged contract. -/
theorem hi_mix_downward (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {c0 c1 cs w0 w1 : Fin (M.N + 1) → ℝ}
    (hcs : ∀ i, M.u (M.θ i + cs i) = δ * M.u (M.θ i + c0 i) + (1 - δ) * M.u (M.θ i + c1 i))
    {i k : Fin (M.N + 1)} (hki : k ≤ i) (h0 : 0 ≤ hi_C M c0 w0 i k)
    (h1 : 0 ≤ hi_C M c1 w1 i k) :
    0 ≤ hi_C M cs (fun i => δ * w0 i + (1 - δ) * w1 i) i k := by
  rw [hi_mix_C_eq M hcs]
  have hθ : M.θ k ≤ M.θ i := M.θ_strictMono.monotone hki
  have key := hi_dara_ce hu (d := M.θ i - M.θ k) (by linarith) hδ0 hδ1 (hcs k)
  rw [show M.θ k + cs k + (M.θ i - M.θ k) = M.θ i + cs k by ring,
    show M.θ k + c0 k + (M.θ i - M.θ k) = M.θ i + c0 k by ring,
    show M.θ k + c1 k + (M.θ i - M.θ k) = M.θ i + c1 k by ring] at key
  nlinarith

end Miao.RecursiveContracts

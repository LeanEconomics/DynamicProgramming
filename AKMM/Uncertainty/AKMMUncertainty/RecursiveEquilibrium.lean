/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.Recursive
import AKMMCompetitiveEquilibrium.ADConsumer

/-!
# Recursive competitive equilibrium of the stochastic growth model

AKMM, Appendix 7.A.1, Definition 16, p. 840, and §7.5, p. 212 ("in Appendix 7.A we formulate a
recursive competitive equilibrium and derive the exact same functional Euler equation").

The aggregate state is `(K, ω)`, with `ω` a Markov chain `P(ω, ω′)` and TFP `A(ω)`. Definition 16
(`definition_16`): the household's Bellman equation in `k` given the aggregate law `G`, with the
continuation value **in expectation over `ω′` given `ω`** (as `rb_Bellman` on the exogenous state
`(K, ω) ↦ (G(K, ω), ω′)`); competitive prices `r = A(ω)F_K(K, 1)`, `w = A(ω)F_L(K, 1)`; and
consistency `G(K, ω) = g(K, K, ω)`.

* **The equilibrium satisfies the planner's functional Euler equation (7.16)** with `g = G`,
  `f(A, K) = AF(K, 1) + (1 − δ)K` and `f₂ = AF_K + 1 − δ` (`definition_16_euler`), using
  Euler's theorem `F(K, 1) = F_KK + F_L` (Chapter 5's `euler_crs`).
* Definition 16 is not vacuous: the log economy with `δ = 1`, `F(K, L) = K/β + bL` and one
  shock state has the equilibrium `G(K) = K`, `g(k, K) = k` (`definition_16_example`).

Departures: the printed Bellman equation `V(k, K, ω) = max u(…) + βV(k′, G(K, ω), ω′)` leaves `ω′`
free; the expectation `Σ_{ω′} P(ω, ω′)V(k′, G(K, ω), ω′)` is used, and "∀(k, K)" is read as
"∀(k, K, ω)"; the endogenous state is `k > 0` and choices are interior.
-/

namespace AKMM.Uncertainty

open Real AKMM.CompetitiveEquilibrium

variable {S : Type*} [Fintype S]

/-- **AKMM, Definition 16, p. 840 (corrected).** `(r, w, G, V, g)` is a recursive competitive
equilibrium: (1) `V(k, K, ω)` solves the household's Bellman equation
`V(k, K, ω) = max_{k′} u((1 − δ + r(K, ω))k + w(K, ω) − k′) + β Σ_{ω′} P(ω, ω′)V(k′, G(K, ω), ω′)`
and `g` attains the maximum; (2) `r = A(ω)F_K(K, 1)`, `w = A(ω)F_L(K, 1)`;
(3) `G(K, ω) = g(K, K, ω)`. -/
def definition_16 (u : ℝ → ℝ) (β δ : ℝ) (P : S → S → ℝ) (A : S → ℝ) (FK FL : ℝ → ℝ)
    (r w G : ℝ → S → ℝ) (V g : ℝ → ℝ → S → ℝ) : Prop :=
  rb_Bellman u β (fun x s => P x.2 s) (fun x s => (G x.1 x.2, s))
      (fun x k => (1 - δ + r x.1 x.2) * k + w x.1 x.2) (fun x k => V k x.1 x.2)
      (fun x k => g k x.1 x.2) ∧
    (∀ K ω, r K ω = A ω * FK K ∧ w K ω = A ω * FL K) ∧ ∀ K ω, G K ω = g K K ω

/-- **AKMM, pp. 212, 840: the recursive equilibrium satisfies the planner's functional Euler
equation (7.16).** Let `u` be differentiable on `(0, ∞)` with derivative `u′`, `V(·, K, ω)`
differentiable on `(0, ∞)`, and `F(K, 1) = F_K(K)K + F_L(K)` for `K > 0` (Euler's theorem). Then
for `K > 0`, with `f(ω, K) = A(ω)F(K, 1) + (1 − δ)K`,
`u′(f(ω, K) − G(K, ω)) = β Σ_{ω′} P(ω, ω′)u′(f(ω′, K′) − G(K′, ω′))(A(ω′)F_K(K′) + 1 − δ)`,
`K′ = G(K, ω)`. -/
theorem definition_16_euler {u u' : ℝ → ℝ} {β δ : ℝ} {P : S → S → ℝ} {A : S → ℝ}
    {F FK FL : ℝ → ℝ} {r w G : ℝ → S → ℝ} {V g V1 : ℝ → ℝ → S → ℝ}
    (h16 : definition_16 u β δ P A FK FL r w G V g) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hV : ∀ K ω k, 0 < k → HasDerivAt (fun k => V k K ω) (V1 k K ω) k)
    (hEuler : ∀ K, 0 < K → F K = FK K * K + FL K) {K : ℝ} (hK : 0 < K) (ω : S) :
    u' (A ω * F K + (1 - δ) * K - G K ω) = β * ∑ ω', P ω ω' *
      (u' (A ω' * F (G K ω) + (1 - δ) * G K ω - G (G K ω) ω') *
        (A ω' * FK (G K ω) + 1 - δ)) := by
  obtain ⟨hB, hp, hG⟩ := h16
  have hf : ∀ (x : ℝ × S) k, 0 < k → HasDerivAt (fun k => (1 - δ + r x.1 x.2) * k + w x.1 x.2)
      (1 - δ + r x.1 x.2) k := fun x k _ => by
    simpa using ((hasDerivAt_id' k).const_mul (1 - δ + r x.1 x.2)).add_const (w x.1 x.2)
  have he := rb_euler (x := (K, ω)) hB hu (fun x k hk => hV x.1 x.2 k hk) hf hK
  have hG0 : 0 < G K ω := by rw [hG]; exact ((hB (K, ω) K hK).1).1
  have hres : ∀ K ω, 0 < K → (1 - δ + r K ω) * K + w K ω = A ω * F K + (1 - δ) * K :=
    fun K ω hK => by rw [(hp K ω).1, (hp K ω).2, hEuler K hK]; ring
  simp only [← hG] at he
  rw [hres K ω hK] at he
  rw [he]
  congr 1
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [hres _ ω' hG0, (hp _ ω').1]
  ring

/-- **AKMM, Definition 16: an example.** With one shock state, `A = 1`, log utility, `δ = 1`,
`0 < β < 1`, `b > 0` and `F(K, L) = K/β + bL` (so `r = 1/β`, `w = b`), the household value
`V(k) = (log(k/β + b/(1 − β)) + log(1 − β))/(1 − β)`, the policy `g(k, K) = k` and the law
`G(K) = K` form a recursive competitive equilibrium. -/
theorem definition_16_example {β b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hb : 0 < b) :
    definition_16 Real.log β 1 (fun _ _ : Unit => 1) (fun _ => 1) (fun _ => 1 / β) (fun _ => b)
      (fun _ _ => 1 / β) (fun _ _ => b) (fun K _ => K)
      (fun k _ _ => (Real.log (k / β + b / (1 - β)) + Real.log (1 - β)) / (1 - β))
      (fun k _ _ => k) := by
  have h1β : 0 < 1 - β := by linarith
  refine ⟨fun x k hk => ?_, fun _ _ => ⟨by ring, by ring⟩, fun _ _ => rfl⟩
  simp only [Fintype.univ_unit, Finset.sum_singleton, one_mul, sub_self, zero_add]
  set Om := k / β + b / (1 - β) with hOm
  have hOm0 : 0 < Om := by positivity
  have hfk : 1 / β * k + b - k = (1 - β) * Om := by rw [hOm]; field_simp; ring
  refine ⟨⟨hk, ?_⟩, ?_, fun k' hk' hk'f => ?_⟩
  · have : k < k / β := by rw [lt_div_iff₀ hβ0]; nlinarith
    have : k / β ≤ 1 / β * k := by rw [div_eq_inv_mul, one_div]
    linarith
  · rw [hfk, Real.log_mul h1β.ne' hOm0.ne']
    field_simp
    ring
  · set Om' := k' / β + b / (1 - β) with hOm'
    have hOm'0 : 0 < Om' := by positivity
    have hx1 : 1 / β * k + b - k' = Om - β * Om' := by rw [hOm, hOm']; field_simp; ring
    have hx1pos : 0 < Om - β * Om' := by rw [← hx1]; linarith
    -- tangent inequalities for `log` at `Ω`
    have t1 := ce_log_tangent hOm0 (div_pos hx1pos h1β)
    have t2 := ce_log_tangent hOm0 hOm'0
    rw [Real.log_div hx1pos.ne' h1β.ne'] at t1
    rw [hx1]
    have key : (1 - β) * Real.log (Om - β * Om') + β * Real.log Om' ≤
        Real.log Om + (1 - β) * Real.log (1 - β) := by
      have e : (1 - β) * ((Om - β * Om') / (1 - β) - Om) + β * (Om' - Om) = 0 := by
        field_simp; ring
      have := mul_le_mul_of_nonneg_left t1 h1β.le
      have := mul_le_mul_of_nonneg_left t2 hβ0.le
      have e2 : (1 - β) * (Om⁻¹ * ((Om - β * Om') / (1 - β) - Om)) + β * (Om⁻¹ * (Om' - Om)) =
          0 := by
        rw [show (1 - β) * (Om⁻¹ * ((Om - β * Om') / (1 - β) - Om)) + β * (Om⁻¹ * (Om' - Om)) =
          Om⁻¹ * ((1 - β) * ((Om - β * Om') / (1 - β) - Om) + β * (Om' - Om)) by ring, e,
          mul_zero]
      nlinarith
    rw [le_div_iff₀ h1β]
    have e3 : (Real.log (Om - β * Om') + β * ((Real.log Om' + Real.log (1 - β)) / (1 - β))) *
        (1 - β) = (1 - β) * Real.log (Om - β * Om') + β * Real.log Om' +
          β * Real.log (1 - β) := by
      field_simp; ring
    rw [e3]
    nlinarith

end AKMM.Uncertainty

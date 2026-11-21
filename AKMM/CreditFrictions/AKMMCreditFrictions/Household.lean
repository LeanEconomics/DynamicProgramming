/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCreditFrictions.Firm

/-!
# The household's first-order conditions

AKMM, §19.4.2, the household's problem (19.7) and its first-order conditions (19.8)–(19.10),
p. 576, with Appendix 19.A.2, pp. 877–878.

The household chooses `(c, ℓ, a′, b′)` subject to `(d + q)a + b + wℓ = c + qa′ + b′/R + T` to
maximise `u(c, ℓ) + βE[V(S′; a′, b′)]`.

* **Envelope conditions** (p. 877): `V_b = γ` and `V_a = γ(d + q)` with `γ = u_c(c, ℓ)`, from
  the Benveniste–Scheinkman lemma `Miao.InfiniteHorizonDP.theorem_4_10` when `V` is concave
  (`hh_envelope`).
* **First-order conditions** (p. 877), derived from optimality along budget-preserving
  directions (`hh_dir`): `u_ℓ + γw = 0`, `βE[V_b′] − γ/R = 0`, `βE[V_a′] − γq = 0`
  (`appendix_19_A_2_focs`).
* **(19.8)–(19.10)**: `u₁w = −u₂` (`eq_19_8`), `1/R = E[βu₁′/u₁]` (`eq_19_9`) and
  `q = E[(βu₁′/u₁)(d′ + q′)]` (`eq_19_10`), chained from optimality in `household_focs`.
* The lump-sum tax `T = B′/R̃ − B′/R = τB′/R` and `R > R̃` iff `τ > 0` (`hh_tax`,
  `hh_R_gt_Rt_iff`); the firm and household budgets with `A = A′ = 1` and this tax give the
  resource constraint `C + p[K′ − (1 − δ)K] + κ(D − φ)² = F` (`hh_resource`).
-/

namespace AKMM.CreditFrictions

open Filter Topology

/-! ### Envelope conditions -/

open Miao.InfiniteHorizonDP in
/-- **Appendix 19.A.2, envelope conditions** (AKMM, p. 877). Fix the optimal `(ℓ₀, a′, b′)`;
`cont = βE[V(S′; a′, b′)]`. If `V` is concave on a neighbourhood of `(a₀, b₀)`, every plan
keeping `(ℓ₀, a′, b′)` and consuming what the budget leaves is worth at most `V`, the optimum is
attained there, and `u(·, ℓ₀)` has derivative `γ` at the optimal consumption, then
`V` is differentiable at `(a₀, b₀)` with `V_a = γ(d + q)` and `V_b = γ`. -/
theorem hh_envelope {u : ℝ → ℝ} {γ : ℝ} {V : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {d q w ℓ₀ a' b' R T cont a₀ b₀ : ℝ} (hV : ConcaveOn ℝ U V) (hU : U ∈ 𝓝 (a₀, b₀))
    (hu : HasDerivAt u γ ((d + q) * a₀ + b₀ + w * ℓ₀ - q * a' - b' / R - T))
    (hle : ∀ a b, u ((d + q) * a + b + w * ℓ₀ - q * a' - b' / R - T) + cont ≤ V (a, b))
    (heq : V (a₀, b₀) = u ((d + q) * a₀ + b₀ + w * ℓ₀ - q * a' - b' / R - T) + cont) :
    HasFDerivAt V (γ • ((d + q) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ContinuousLinearMap.snd ℝ ℝ ℝ)) (a₀, b₀) := by
  set c : ℝ × ℝ → ℝ := fun x => (d + q) * x.1 + x.2 + w * ℓ₀ - q * a' - b' / R - T with hc
  have hcd : HasFDerivAt c ((d + q) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ContinuousLinearMap.snd ℝ ℝ ℝ) (a₀, b₀) := by
    have h1 : HasFDerivAt (fun x : ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (a₀, b₀) :=
      hasFDerivAt_fst
    have h2 : HasFDerivAt (fun x : ℝ × ℝ => x.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (a₀, b₀) :=
      hasFDerivAt_snd
    have h := ((h1.const_mul (d + q)).add h2).add_const (w * ℓ₀ - q * a' - b' / R - T)
    convert h using 1
    funext x
    simp only [hc, Pi.add_apply]
    ring
  have hW := (hu.comp_hasFDerivAt (a₀, b₀) hcd).add_const cont
  exact theorem_4_10 hV hU hW heq.symm (Eventually.of_forall fun x => hle x.1 x.2)

/-! ### First-order conditions from optimality -/

/-- AKMM, Appendix 19.A.2, p. 877: at an optimum of (19.7), moving `(c, ℓ, a′, b′)` in any
direction `(ac, aℓ, aa, ab)` that preserves the budget, `waℓ = ac + qaa + ab/R`, does not change
the objective to first order: `u′(ac, aℓ) + C′(aa, ab) = 0`, where `C = βE[V(S′; ·, ·)]`. -/
theorem hh_dir {u : ℝ × ℝ → ℝ} {u' : ℝ × ℝ →L[ℝ] ℝ} {C : ℝ × ℝ → ℝ} {C' : ℝ × ℝ →L[ℝ] ℝ}
    {d q w R T a b c₀ ℓ₀ a₀ b₀ : ℝ} (hu : HasFDerivAt u u' (c₀, ℓ₀))
    (hC : HasFDerivAt C C' (a₀, b₀))
    (hopt : ∀ c ℓ a' b', (d + q) * a + b + w * ℓ = c + q * a' + b' / R + T →
      u (c, ℓ) + C (a', b') ≤ u (c₀, ℓ₀) + C (a₀, b₀))
    (hbud : (d + q) * a + b + w * ℓ₀ = c₀ + q * a₀ + b₀ / R + T)
    (ac aℓ aa ab : ℝ) (hdir : w * aℓ = ac + q * aa + ab / R) :
    u' (ac, aℓ) + C' (aa, ab) = 0 := by
  have hlin : ∀ (x e : ℝ), HasDerivAt (fun t : ℝ => x + e * t) e 0 := fun x e => by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul e).const_add x
  have hf := (hu.comp_hasDerivAt_of_eq 0 ((hlin c₀ ac).prodMk (hlin ℓ₀ aℓ)) (by simp)).add
    (hC.comp_hasDerivAt_of_eq 0 ((hlin a₀ aa).prodMk (hlin b₀ ab)) (by simp))
  refine IsLocalMax.hasDerivAt_eq_zero (Eventually.of_forall fun t => ?_) hf
  change u (c₀ + ac * t, ℓ₀ + aℓ * t) + C (a₀ + aa * t, b₀ + ab * t) ≤
    u (c₀ + ac * 0, ℓ₀ + aℓ * 0) + C (a₀ + aa * 0, b₀ + ab * 0)
  simp only [mul_zero, add_zero]
  refine hopt _ _ _ _ ?_
  have : (b₀ + ab * t) / R = b₀ / R + ab / R * t := by ring
  rw [this]
  linear_combination hbud + t * hdir

/-- **Appendix 19.A.2, first-order conditions** (AKMM, p. 877), from optimality. With
`γ = u_c(c, ℓ) = u′(1, 0)`, `u_ℓ = u′(0, 1)` and the continuation `C = βE[V(S′; ·, ·)]` with
partial derivatives `C_a = C′(1, 0)`, `C_b = C′(0, 1)`: `u_ℓ + γw = 0`, `C_b − γ/R = 0` and
`C_a − γq = 0`. -/
theorem appendix_19_A_2_focs {u : ℝ × ℝ → ℝ} {u' : ℝ × ℝ →L[ℝ] ℝ} {C : ℝ × ℝ → ℝ}
    {C' : ℝ × ℝ →L[ℝ] ℝ} {d q w R T a b c₀ ℓ₀ a₀ b₀ : ℝ} (hR : R ≠ 0)
    (hu : HasFDerivAt u u' (c₀, ℓ₀)) (hC : HasFDerivAt C C' (a₀, b₀))
    (hopt : ∀ c ℓ a' b', (d + q) * a + b + w * ℓ = c + q * a' + b' / R + T →
      u (c, ℓ) + C (a', b') ≤ u (c₀, ℓ₀) + C (a₀, b₀))
    (hbud : (d + q) * a + b + w * ℓ₀ = c₀ + q * a₀ + b₀ / R + T) :
    u' (0, 1) + u' (1, 0) * w = 0 ∧ C' (0, 1) - u' (1, 0) * (1 / R) = 0 ∧
      C' (1, 0) - u' (1, 0) * q = 0 := by
  have hl := hh_dir hu hC hopt hbud w 1 0 0 (by ring)
  have hb := hh_dir hu hC hopt hbud (-(1 / R)) 0 0 1 (by field_simp; ring)
  have ha := hh_dir hu hC hopt hbud (-q) 0 1 0 (by ring)
  rw [kkt_clm_apply u', kkt_clm_apply C'] at hl hb ha
  refine ⟨by linear_combination hl, by linear_combination hb, by linear_combination ha⟩

/-- **(19.8)** (AKMM, p. 576): from `u_c = γ` and `u_ℓ + γw = 0`, `u₁(c, ℓ)w = −u₂(c, ℓ)`. -/
theorem eq_19_8 {u1 u2 γ w : ℝ} (hc : u1 = γ) (hl : u2 + γ * w = 0) : u1 * w = -u2 := by
  rw [hc]
  linarith

variable {S : Type*} [Fintype S]

/-- **(19.9)** (AKMM, p. 576, via Appendix 19.A.2). From `βE[V_b′] − γ/R = 0` with the updated
envelope condition `V_b(s) = γₛ = u₁(c′ₛ, ℓ′ₛ)` and `γ = u₁(c, ℓ) ≠ 0`:
`1/R = E[βu₁(c′, ℓ′)/u₁(c, ℓ)]`. -/
theorem eq_19_9 (pr γs Vb : S → ℝ) (β γ R : ℝ) (hγ : γ ≠ 0)
    (hfoc : β * ∑ s, pr s * Vb s - γ * (1 / R) = 0) (henv : ∀ s, Vb s = γs s) :
    1 / R = ∑ s, pr s * (β * γs s / γ) := by
  have e : ∑ s, pr s * (β * γs s / γ) = β * (∑ s, pr s * Vb s) / γ := by
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by rw [henv]; ring
  rw [e, eq_div_iff hγ]
  linear_combination -hfoc

/-- **(19.10)** (AKMM, p. 576, via Appendix 19.A.2). From `βE[V_a′] − γq = 0` with the updated
envelope condition `V_a(s) = γₛ(d′ₛ + q′ₛ)` and `γ ≠ 0`:
`q = E[(βu₁(c′, ℓ′)/u₁(c, ℓ))(d′ + q′)]`. -/
theorem eq_19_10 (pr γs Va d' q' : S → ℝ) (β γ q : ℝ) (hγ : γ ≠ 0)
    (hfoc : β * ∑ s, pr s * Va s - γ * q = 0) (henv : ∀ s, Va s = γs s * (d' s + q' s)) :
    q = ∑ s, pr s * (β * γs s / γ * (d' s + q' s)) := by
  have e : ∑ s, pr s * (β * γs s / γ * (d' s + q' s)) = β * (∑ s, pr s * Va s) / γ := by
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by rw [henv]; field_simp
  rw [e, eq_div_iff hγ]
  linear_combination -hfoc

/-- **(19.8)–(19.10) from optimality** (AKMM, p. 576 and 877–878). Let `(c₀, ℓ₀, a₀′, b₀′)` solve
(19.7) (every budget-feasible plan is worth at most it), `u` be differentiable at `(c₀, ℓ₀)`
with `u₁ = u′(1, 0) ≠ 0`, `u₂ = u′(0, 1)`, and the continuation be `βΣₛπₛVₛ`, where each
next-period value `Vₛ` is differentiable at `(a₀′, b₀′)` with the envelope derivative of
`hh_envelope`, `γₛ((d′ₛ + q′ₛ)da + db)`. Then (19.8), (19.9) and (19.10) hold. -/
theorem household_focs {u : ℝ × ℝ → ℝ} {u' : ℝ × ℝ →L[ℝ] ℝ} {V : S → ℝ × ℝ → ℝ}
    (pr γs d' q' : S → ℝ) {β d q w R T a b c₀ ℓ₀ a₀ b₀ : ℝ} (hR : R ≠ 0)
    (hu : HasFDerivAt u u' (c₀, ℓ₀)) (hγ : u' (1, 0) ≠ 0)
    (hV : ∀ s, HasFDerivAt (V s) (γs s • ((d' s + q' s) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ContinuousLinearMap.snd ℝ ℝ ℝ)) (a₀, b₀))
    (hopt : ∀ c ℓ a' b', (d + q) * a + b + w * ℓ = c + q * a' + b' / R + T →
      u (c, ℓ) + β * ∑ s, pr s * V s (a', b') ≤ u (c₀, ℓ₀) + β * ∑ s, pr s * V s (a₀, b₀))
    (hbud : (d + q) * a + b + w * ℓ₀ = c₀ + q * a₀ + b₀ / R + T) :
    u' (1, 0) * w = -u' (0, 1) ∧ 1 / R = ∑ s, pr s * (β * γs s / u' (1, 0)) ∧
      q = ∑ s, pr s * (β * γs s / u' (1, 0) * (d' s + q' s)) := by
  set L : S → ℝ × ℝ →L[ℝ] ℝ := fun s => γs s • ((d' s + q' s) •
      ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) with hL
  have hC : HasFDerivAt (fun x => β * ∑ s, pr s * V s x) (β • ∑ s, pr s • L s) (a₀, b₀) := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun s _ => (hV s).const_mul (pr s))
    exact this.const_mul β
  obtain ⟨hl, hb, ha⟩ := appendix_19_A_2_focs hR hu hC hopt hbud
  have hLb : (β • ∑ s, pr s • L s) (0, 1) = β * ∑ s, pr s * γs s := by
    simp only [hL]
    simp
  have hLa : (β • ∑ s, pr s • L s) (1, 0) = β * ∑ s, pr s * (γs s * (d' s + q' s)) := by
    simp only [hL]
    simp
  rw [hLb] at hb
  rw [hLa] at ha
  refine ⟨eq_19_8 rfl hl, ?_, ?_⟩
  · exact eq_19_9 pr γs γs β (u' (1, 0)) R hγ hb (fun _ => rfl)
  · exact eq_19_10 pr γs (fun s => γs s * (d' s + q' s)) d' q' β (u' (1, 0)) q hγ ha
      (fun _ => rfl)

/-! ### Taxes and the resource constraint -/

/-- AKMM, p. 576: with `R̃ = R/(1 + τ)` (Assumption 19.4.1, p. 572), the lump-sum tax that
finances the interest subsidy is `T = B′/R̃ − B′/R = τB′/R`. -/
theorem hh_tax {R τ B' : ℝ} (hR : R ≠ 0) :
    B' / (R / (1 + τ)) - B' / R = τ * B' / R := by
  field_simp
  ring

/-- AKMM, p. 576: "Notice that `R > R̃` since `R̃ = R/(1 + τ)` and `τ` is positive": for
`R > 0`, `τ > −1`, `R > R̃` iff `τ > 0`. -/
theorem hh_R_gt_Rt_iff {R τ : ℝ} (hR : 0 < R) (hτ : -1 < τ) : R / (1 + τ) < R ↔ 0 < τ := by
  have h1 : 0 < 1 + τ := by linarith
  rw [div_lt_iff₀ h1]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- AKMM, pp. 574–576: the firm's budget `F − wL + B′/R̃ = B + p[K′ − (1 − δ)K] + ϕ(D)`, the
household's budget with `A = A′ = 1`, `(D + q) + B + wL = C + q + B′/R + T`, and the tax
`T = B′/R̃ − B′/R` give the resource constraint `C + p[K′ − (1 − δ)K] + κ(D − φ)² = F`. -/
theorem hh_resource {F w L B' Rt B p K' δ K D C q R T κ φ : ℝ}
    (hfirm : F - w * L + B' / Rt = B + p * (K' - (1 - δ) * K) + cfPhi κ φ D)
    (hhh : (D + q) * 1 + B + w * L = C + q * 1 + B' / R + T) (hT : T = B' / Rt - B' / R) :
    C + p * (K' - (1 - δ) * K) + κ * (D - φ) ^ 2 = F := by
  unfold cfPhi at hfirm
  rw [hT] at hhh
  linarith

end AKMM.CreditFrictions

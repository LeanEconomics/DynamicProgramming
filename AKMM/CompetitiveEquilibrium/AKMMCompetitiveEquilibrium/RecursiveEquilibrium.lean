/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCompetitiveEquilibrium.SteadyState

/-!
# Recursive competitive equilibrium and aggregation

AKMM, §5.4.2, pp. 149–152, and Appendix 5.A, pp. 836–837. The household takes the price
functions `r(K)`, `w(K)` and the law of motion `K′ = G(K)` as given and solves (5.23); in a
recursive competitive equilibrium (Definition 9) `r(K) = F₁(K, 1)`, `w(K) = F₂(K, 1)` and
`G(K) = g(K, K)`.

* The resource constraint is implied (p. 150): consumption at `k = K` is
  `F(K, 1) + (1 − δ)K − G(K)` whenever `F(K, 1) = F₁K + F₂` (Euler's theorem, `euler_crs`)
  (`definition_9_resource`).
* The aggregate functional Euler equation (p. 151): evaluating the household's functional Euler
  equation at `k = K` gives the planner's equation (4.26),
  `u′((1 − δ)K + F(K, 1) − G(K)) = βu′((1 − δ)G(K) + F(G(K), 1) − G(G(K)))(1 − δ + F₁(G(K), 1))`
  (`definition_9_aggregate_euler`). The book prints `K(1 − δ)K` on the left; at a steady state
  with `δ ≠ 1`, `K ∉ {0, 1}` the printed equation fails
  (`definition_9_aggregate_euler_printed`, with the instance
  `definition_9_aggregate_euler_printed_instance`).
* Aggregation (p. 151, Appendix 5.A): with `u = c^{1−σ}/(1 − σ)` the Euler equation is
  equivalent to the linear equation `A + Bk + Cg(k, K) + Dg(g(k, K), G(K)) = 0`
  (`appendix_5A_power`, `appendix_5A_linear`); for `g = μ + λk` it splits into a constant term
  and a coefficient of `k` (`appendix_5A_split`), so the two functional equations make the
  Euler equation hold for all `k` (`appendix_5A_mu_lambda`). The book has the roles of the two
  equations reversed (`appendix_5A_printed_attribution_counterexample`).
* With linear policies `gᵢ(k, K) = μᵢ(K) + λ(K)k`, aggregate saving depends on the distribution
  only through `K` (`aggregation_linear`).
* Appendix 5.A closed form: log utility, `F = AK^α`, `δ = 1`: `G(K) = αβAK^α` and
  `g(k, K) = βr(K)k` satisfy the household's functional Euler equation for every `(k, K)` and
  consistency (`appendix_5A_closed_form`), with `μ = 0`, `λ = βr` solving the two functional
  equations (`appendix_5A_closed_form_mu_lambda`).
* Definition 10 (valued leisure, p. 152): at `k = K` the household's intratemporal condition is
  the planner's, and consumption is output plus undepreciated capital minus investment
  (`definition_10_planner`).

Not formalised: existence of `V` in (5.23) (the book does not construct it); condition 1 of
Definition 9 enters through its functional Euler equation, as in the book's characterisation.
-/

namespace AKMM.CompetitiveEquilibrium

open MeasureTheory Filter Topology

variable {I : Type*} [MeasurableSpace I]

/-- **AKMM, p. 150: Definition 9 implies the resource constraint.** If `r(K) = F₁(K, 1)`,
`w(K) = F₂(K, 1)`, `G(K) = g(K, K)` and `F(K, 1) = F₁(K, 1)K + F₂(K, 1)`, then the
representative consumer's consumption `K(1 − δ + r(K)) + w(K) − G(K)` equals
`F(K, 1) + (1 − δ)K − G(K)`. -/
theorem definition_9_resource {F F1 F2 r w G : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {δ K : ℝ}
    (hr : r K = F1 K) (hw : w K = F2 K) (hG : G K = g K K) (heuler : F K = F1 K * K + F2 K) :
    K * (1 - δ + r K) + w K - g K K = F K + (1 - δ) * K - G K := by
  rw [hr, hw, hG, heuler]; ring

/-- **AKMM, p. 151, corrected: the aggregate functional Euler equation.** If the household's
functional Euler equation
`u′((1 − δ + r(K))k + w(K) − g(k, K)) =
  βu′(g(k, K)(1 − δ + r(G(K))) + w(G(K)) − g(g(k, K), G(K)))(1 − δ + r(G(K)))`
holds at `k = K` for all `K`, with `r = F₁`, `w = F₂`, `G(K) = g(K, K)` and Euler's identity
`F = F₁K + F₂`, then
`u′(K(1 − δ) + F(K) − G(K)) = βu′(G(K)(1 − δ) + F(G(K)) − G(G(K)))(1 − δ + F₁(G(K)))`, the
planner's (4.26). -/
theorem definition_9_aggregate_euler {du F F1 F2 r w G : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {β δ : ℝ}
    (heul : ∀ k K, du ((1 - δ + r K) * k + w K - g k K) =
      β * du (g k K * (1 - δ + r (G K)) + w (G K) - g (g k K) (G K)) * (1 - δ + r (G K)))
    (hr : ∀ K, r K = F1 K) (hw : ∀ K, w K = F2 K) (hG : ∀ K, G K = g K K)
    (heuler : ∀ K, F K = F1 K * K + F2 K) (K : ℝ) :
    du (K * (1 - δ) + F K - G K) =
      β * du (G K * (1 - δ) + F (G K) - G (G K)) * (1 - δ + F1 (G K)) := by
  have h := heul K K
  rw [← hG K, ← hG (G K), hr, hw, hr, hw] at h
  have e1 : (1 - δ + F1 K) * K + F2 K - G K = K * (1 - δ) + F K - G K := by
    rw [heuler]; ring
  have e2 : G K * (1 - δ + F1 (G K)) + F2 (G K) - G (G K) =
      G K * (1 - δ) + F (G K) - G (G K) := by rw [heuler]; ring
  rw [e1, e2] at h
  exact h

/-- **AKMM, p. 151: the printed aggregate equation is wrong.** The book prints the left side as
`u′(K(1 − δ)K + F(K, 1) − G(K))`. If `u′` is injective, `δ ≠ 1` and `K ∉ {0, 1}`, the printed
and the correct equations cannot both hold at `K`. -/
theorem definition_9_aggregate_euler_printed {du F F1 G : ℝ → ℝ} {β δ K : ℝ}
    (hinj : Function.Injective du) (hδ : δ ≠ 1) (hK0 : K ≠ 0) (hK1 : K ≠ 1)
    (hcorrect : du (K * (1 - δ) + F K - G K) =
      β * du (G K * (1 - δ) + F (G K) - G (G K)) * (1 - δ + F1 (G K))) :
    du (K * (1 - δ) * K + F K - G K) ≠
      β * du (G K * (1 - δ) + F (G K) - G (G K)) * (1 - δ + F1 (G K)) := by
  intro hprinted
  have := hinj (hprinted.trans hcorrect.symm)
  have h : (1 - δ) * K * (K - 1) = 0 := by linarith
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact hδ (by linarith)
    · exact hK0 h
  · exact hK1 (by linarith)

/-- **AKMM, p. 151: an instance.** With `u = log` (`u′(c) = 1/c`), `F(K) = 6K^{1/2}`,
`δ = β = 1/2`, the steady state is `K̄ = 4`: for any law of motion with `G(4) = 4` the correct
aggregate equation holds at `K = 4` and the printed one fails. -/
theorem definition_9_aggregate_euler_printed_instance {G : ℝ → ℝ} (hG : G 4 = 4) :
    let F : ℝ → ℝ := fun K => 6 * K ^ (1 / 2 : ℝ)
    let F1 : ℝ → ℝ := fun K => 1 / 2 * 6 * K ^ (1 / 2 - 1 : ℝ)
    (4 * (1 - 1 / 2) + F 4 - G 4)⁻¹ =
        1 / 2 * (G 4 * (1 - 1 / 2) + F (G 4) - G (G 4))⁻¹ * (1 - 1 / 2 + F1 (G 4)) ∧
      (4 * (1 - 1 / 2) * 4 + F 4 - G 4)⁻¹ ≠
        1 / 2 * (G 4 * (1 - 1 / 2) + F (G 4) - G (G 4))⁻¹ * (1 - 1 / 2 + F1 (G 4)) := by
  intro F F1
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have h4' : (4 : ℝ) ^ (1 / 2 - 1 : ℝ) = 1 / 2 := by
    rw [Real.rpow_sub (by norm_num), h4, Real.rpow_one]; norm_num
  simp only [F, F1, hG, h4, h4']
  norm_num

/-- **AKMM, Appendix 5.A, p. 836: raising the power Euler equation to `−1/σ`.** For `σ > 0`,
consumptions `c, c′ > 0` and a gross return with `βR′ > 0`,
`c^{−σ} = βc′^{−σ}R′` iff `c = (βR′)^{−1/σ}c′`. -/
theorem appendix_5A_power {σ β R' c c' : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hc' : 0 < c')
    (hR : 0 < β * R') :
    c ^ (-σ) = β * c' ^ (-σ) * R' ↔ c = (β * R') ^ (-σ⁻¹) * c' := by
  have hσ' : σ ≠ 0 := hσ.ne'
  constructor
  · intro h
    have h1 : c ^ (-σ) = (β * R') * c' ^ (-σ) := by rw [h]; ring
    have h2 := congrArg (fun x => x ^ (-σ⁻¹)) h1
    rw [← Real.rpow_mul hc.le, Real.mul_rpow hR.le (Real.rpow_nonneg hc'.le _),
      ← Real.rpow_mul hc'.le] at h2
    have e : -σ * -σ⁻¹ = 1 := by field_simp
    rw [e, Real.rpow_one, Real.rpow_one] at h2
    exact h2
  · intro h
    rw [h, Real.mul_rpow (Real.rpow_nonneg hR.le _) hc'.le, ← Real.rpow_mul hR.le]
    have e : -σ⁻¹ * -σ = 1 := by field_simp
    rw [e, Real.rpow_one]
    ring

/-- **AKMM, Appendix 5.A, p. 836: the linear form.** With `R = 1 − δ + r(K)`,
`R′ = 1 − δ + r(G(K))`, `φ = (βR′)^{−1/σ}`, the equation
`Rk + w − g = φ(gR′ + w′ − g′)` is `A + Bk + Cg + Dg′ = 0` with `A = w − φw′`, `B = R`,
`C = −(1 + φR′)` and `D = φ`. -/
theorem appendix_5A_linear {R R' w w' φ k g g' : ℝ} :
    R * k + w - g = φ * (g * R' + w' - g') ↔
      (w - φ * w') + R * k + (-(1 + φ * R')) * g + φ * g' = 0 := by
  constructor <;> intro h <;> linarith

/-- **AKMM, Appendix 5.A, p. 836: the split.** For `g = μ + λk` and `g′ = μ′ + λ′g`,
`A + Bk + Cg + Dg′` equals `[A + Cμ + D(μ′ + λ′μ)] + k[B + Cλ + Dλ′λ]`: the first of the book's
two functional equations is the constant term, the second the coefficient of `k`. -/
theorem appendix_5A_split (A B C D μ lam μ' lam' k : ℝ) :
    A + B * k + C * (μ + lam * k) + D * (μ' + lam' * (μ + lam * k)) =
      (A + C * μ + D * (μ' + lam' * μ)) + k * (B + C * lam + D * lam' * lam) := by
  ring

/-- **AKMM, Appendix 5.A, p. 836: linear policies solve the Euler equation.** If `μ(K)` and
`λ(K)` satisfy `A(K) + C(K)μ(K) + D(K)(μ(G(K)) + λ(G(K))μ(K)) = 0` and
`B(K) + C(K)λ(K) + D(K)λ(G(K))λ(K) = 0` for all `K`, then `g(k, K) = μ(K) + λ(K)k` satisfies
`A(K) + B(K)k + C(K)g(k, K) + D(K)g(g(k, K), G(K)) = 0` for all `(k, K)`. -/
theorem appendix_5A_mu_lambda {A B C D μ lam G : ℝ → ℝ}
    (h1 : ∀ K, A K + C K * μ K + D K * (μ (G K) + lam (G K) * μ K) = 0)
    (h2 : ∀ K, B K + C K * lam K + D K * lam (G K) * lam K = 0) (k K : ℝ) :
    let g : ℝ → ℝ → ℝ := fun k K => μ K + lam K * k
    A K + B K * k + C K * g k K + D K * g (g k K) (G K) = 0 := by
  intro g
  simp only [g]
  rw [appendix_5A_split, h1, h2]
  ring

/-- **AKMM, Appendix 5.A, p. 836: the printed attribution is reversed.** The book says the first
equation makes the coefficient of `k` vanish. With `A = C = D = 0`, `B = 1`, `λ = 0`, the first
equation holds for every `μ` while the coefficient of `k`, `B + Cλ + Dλ′λ = 1`, does not
vanish. -/
theorem appendix_5A_printed_attribution_counterexample (μ μ' : ℝ) :
    (0 : ℝ) + 0 * μ + 0 * (μ' + 0 * μ) = 0 ∧ (1 : ℝ) + 0 * 0 + 0 * 0 * 0 ≠ 0 := by
  norm_num

/-- **AKMM, p. 151: aggregation with linear policies.** If `gᵢ(k, K) = μᵢ(K) + λ(K)k` with the
same slope for all consumers, `μᵢ(K)` and `kᵢ` are integrable and `∫ kᵢ di = K`, then aggregate
saving `∫ gᵢ(kᵢ, K) di = ∫ μᵢ(K) di + λ(K)K` depends on the distribution only through `K`. -/
theorem aggregation_linear {μm : Measure I} {μ : I → ℝ} {lam K : ℝ} {k : I → ℝ}
    (hμ : Integrable μ μm) (hk : Integrable k μm) (hK : ∫ i, k i ∂μm = K) :
    ∫ i, (μ i + lam * k i) ∂μm = ∫ i, μ i ∂μm + lam * K := by
  rw [integral_add hμ (hk.const_mul lam), integral_const_mul, hK]

/-- **AKMM, Appendix 5.A, pp. 836–837: the closed form.** With log utility (`u′(c) = 1/c`),
`F(K, 1) = AK^α`, `δ = 1`, `r(K) = αAK^{α−1}`, `w(K) = (1 − α)AK^α`, `G(K) = αβAK^α` and
`g(k, K) = βr(K)k`: consistency `G(K) = g(K, K)` holds, and for every `K > 0` and `k ≥ 0` the
household's functional Euler equation
`1/(r(K)k + w(K) − g(k, K)) = β r(G(K))/(r(G(K))g(k, K) + w(G(K)) − g(g(k, K), G(K)))` holds,
with positive consumption. -/
theorem appendix_5A_closed_form {A α β : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    let r : ℝ → ℝ := fun K => α * A * K ^ (α - 1)
    let w : ℝ → ℝ := fun K => (1 - α) * A * K ^ α
    let G : ℝ → ℝ := fun K => α * β * A * K ^ α
    let g : ℝ → ℝ → ℝ := fun k K => β * r K * k
    (∀ K, 0 < K → G K = g K K) ∧
      ∀ k K, 0 ≤ k → 0 < K →
        0 < r K * k + w K - g k K ∧
        0 < r (G K) * g k K + w (G K) - g (g k K) (G K) ∧
        (r K * k + w K - g k K)⁻¹ =
          β * (r (G K) * g k K + w (G K) - g (g k K) (G K))⁻¹ * r (G K) := by
  intro r w G g
  have hKa : ∀ K : ℝ, 0 < K → K ^ (α - 1) = K ^ α / K := fun K hK => Real.rpow_sub_one hK.ne' α
  refine ⟨fun K hK => ?_, fun k K hk hK => ?_⟩
  · simp only [G, g, r]; rw [hKa K hK]; field_simp
  have hGpos : 0 < G K := by
    simp only [G]; exact mul_pos (mul_pos (mul_pos hα0 hβ0) hA) (Real.rpow_pos_of_pos hK _)
  have hrpos : ∀ K : ℝ, 0 < K → 0 < r K := fun K hK =>
    mul_pos (mul_pos hα0 hA) (Real.rpow_pos_of_pos hK _)
  have hwpos : ∀ K : ℝ, 0 < K → 0 < w K := fun K hK =>
    mul_pos (mul_pos (by linarith) hA) (Real.rpow_pos_of_pos hK _)
  -- the key identity `w(G(K)) = βr(G(K))w(K)`
  have hwG : w (G K) = β * r (G K) * w K := by
    simp only [w, r]
    rw [hKa (G K) hGpos]
    have hG' : G K = α * β * A * K ^ α := rfl
    have := hGpos.ne'
    field_simp
    rw [hG']
    ring
  have hc : r K * k + w K - g k K = (1 - β) * r K * k + w K := by simp only [g]; ring
  have hc' : r (G K) * g k K + w (G K) - g (g k K) (G K) =
      β * r (G K) * ((1 - β) * r K * k + w K) := by
    simp only [g]; rw [hwG]; ring
  have hcpos : 0 < (1 - β) * r K * k + w K := by
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - β) (hrpos K hK).le) hk
    linarith [hwpos K hK]
  have hrG := hrpos (G K) hGpos
  refine ⟨by rw [hc]; exact hcpos, by rw [hc']; positivity, ?_⟩
  rw [hc, hc']
  have := hcpos.ne'
  have := hrG.ne'
  have := hβ0.ne'
  field_simp

/-- **AKMM, Appendix 5.A, p. 837: `μ(K) = 0`, `λ(K) = βr(K)`.** In the closed-form economy
(`σ = 1`, so `φ = 1/(βR′)` with `R′ = r(G(K))`; `A = w − φw′`, `B = r(K)`, `C = −(1 + φR′)`,
`D = φ`), `μ = 0` and `λ = βr` solve both functional equations. -/
theorem appendix_5A_closed_form_mu_lambda {A α β K : ℝ} (hA : 0 < A) (hα0 : 0 < α)
    (hβ0 : 0 < β) (hK : 0 < K) :
    let r : ℝ → ℝ := fun K => α * A * K ^ (α - 1)
    let w : ℝ → ℝ := fun K => (1 - α) * A * K ^ α
    let G : ℝ → ℝ := fun K => α * β * A * K ^ α
    let φ := (β * r (G K))⁻¹
    (w K - φ * w (G K)) + (-(1 + φ * r (G K))) * 0 + φ * (0 + β * r (G K) * 0) = 0 ∧
      r K + (-(1 + φ * r (G K))) * (β * r K) + φ * (β * r (G K)) * (β * r K) = 0 := by
  intro r w G φ
  have hGpos : 0 < G K := by
    simp only [G]; exact mul_pos (mul_pos (mul_pos hα0 hβ0) hA) (Real.rpow_pos_of_pos hK _)
  have hrG : 0 < r (G K) := mul_pos (mul_pos hα0 hA) (Real.rpow_pos_of_pos hGpos _)
  have hwG : w (G K) = β * r (G K) * w K := by
    simp only [w, r]
    rw [Real.rpow_sub_one hGpos.ne']
    have hG' : G K = α * β * A * K ^ α := rfl
    have := hGpos.ne'
    field_simp
    rw [hG']
    ring
  have hφ : φ * (β * r (G K)) = 1 := inv_mul_cancel₀ (mul_pos hβ0 hrG).ne'
  constructor
  · rw [hwG]
    have : φ * (β * r (G K) * w K) = w K := by rw [← mul_assoc, hφ, one_mul]
    linarith
  · have e : φ * r (G K) * (β * r K) = r K := by
      rw [show φ * r (G K) * (β * r K) = φ * (β * r (G K)) * r K by ring, hφ, one_mul]
    have e2 : φ * (β * r (G K)) * (β * r K) = β * r K := by rw [hφ, one_mul]
    linear_combination (-1 : ℝ) * e + e2

/-- **AKMM, Definition 10, p. 152, and the remark after it.** With valued leisure, if
`r(K) = F₁(K, H(K))`, `w(K) = F₂(K, H(K))`, `G(K) = g(K, K)`, `H(K) = h(K, K)` and Euler's
identity `F(K, H) = F₁K + F₂H` holds, then at `k = K` (i) consumption is
`F(K, H(K)) + (1 − δ)K − G(K)` and (ii) the household's intratemporal condition
`v′(h) = w(K)u′(c)` is the planner's `v′(L) = F₂(K, L)u′(C)`. -/
theorem definition_10_planner {du dv : ℝ → ℝ} {F F1 F2 : ℝ → ℝ → ℝ} {r w G H : ℝ → ℝ}
    {g h : ℝ → ℝ → ℝ} {δ K : ℝ} (hr : r K = F1 K (H K)) (hw : w K = F2 K (H K))
    (hG : G K = g K K) (hH : H K = h K K)
    (heuler : F K (H K) = F1 K (H K) * K + F2 K (H K) * H K)
    (hintra : dv (h K K) = w K * du ((1 - δ + r K) * K + w K * h K K - g K K)) :
    (1 - δ + r K) * K + w K * h K K - g K K = F K (H K) + (1 - δ) * K - G K ∧
      dv (H K) = F2 K (H K) * du (F K (H K) + (1 - δ) * K - G K) := by
  have hc : (1 - δ + r K) * K + w K * h K K - g K K = F K (H K) + (1 - δ) * K - G K := by
    rw [hr, hw, ← hH, ← hG, heuler]; ring
  refine ⟨hc, ?_⟩
  calc dv (H K) = dv (h K K) := by rw [hH]
    _ = w K * du ((1 - δ + r K) * K + w K * h K K - g K K) := hintra
    _ = F2 K (H K) * du (F K (H K) + (1 - δ) * K - G K) := by rw [hc, hw]

end AKMM.CompetitiveEquilibrium

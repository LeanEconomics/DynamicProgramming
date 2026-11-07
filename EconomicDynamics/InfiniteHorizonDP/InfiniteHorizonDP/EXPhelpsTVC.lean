/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.EXPhelps

/-!
# Exercise 7.10: the transversality conditions (7.4) and (7.35) in Example 7.5.1

Miao, §7.6, Exercise 10, p. 230, in the setting of `EUPhelps` (a filtered probability space, the
return process `R` with `R_0 = 1`, cash on hand `x_t` under `c_t = Ax_t` (`eu_phelpsCash`), the
Euler-class state `y_t` = saving carried into `t` (`eu_phelpsState`)).

* `ex_7_10_envelope`: `V(x) = A^{−γ}u(x)` has `V′(x) = A^{−γ}x^{−γ} = u′(Ax)` (the envelope
  condition) and, being homogeneous of degree `1 − γ`, `V(x) = xV′(x)/(1 − γ)`.
* `ex_7_10_pathwise`: along the plan, `u_a(t) · y_{t+1} = −u′(c_t)(1 − A)x_t =
  −(1 − γ)(1 − A) V(x_t)` pathwise.
* **Exercise 7.10** (`ex_7_10`): hence, along the optimal plan, (7.35) holds iff the
  transversality condition (7.4) `βᵀ E V(x_T) → 0` holds (`γ ≠ 1`), with no integrability
  assumptions; both hold (`example_7_5_1_tvc`).
* `ex_7_10_log` (`γ = 1`, `A = 1 − β`, `V = b ln x + a`): the (7.35) term is the constant
  `−βᵀ β/(1 − β)`, so (7.35) always holds, while (7.4) is `βᵀ(b(ln x₀ + T(ln β + E ln R)) + a) → 0`,
  which holds when `E ln R_{t+1}` is a finite constant. Here (7.4) and (7.35) are not
  proportional (`ln` is not homogeneous), but both hold.
* (7.4) along **all** plans holds for `γ < 1` and fails for `γ > 1`: `ex_7_10_all_plans` in
  `EXPhelpsMDP`.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Exercise 7.10, the envelope condition and homogeneity** (Miao, p. 230), `γ ≠ 1`,
`0 < A`: `V(x) = A^{−γ}u(x)` has derivative `A^{−γ}x^{−γ} = u′(Ax)` at `x > 0`, and
`V(x) = x V′(x)/(1 − γ)`. -/
theorem ex_7_10_envelope {γ A x : ℝ} (hγ1 : γ ≠ 1) (hA : 0 < A) (hx : 0 < x) :
    HasDerivAt (fun y => A ^ (-γ) * cs_crra γ y) (A ^ (-γ) * x ^ (-γ)) x ∧
      A ^ (-γ) * x ^ (-γ) = (A * x) ^ (-γ) ∧
      A ^ (-γ) * cs_crra γ x = x * (A ^ (-γ) * x ^ (-γ)) / (1 - γ) := by
  refine ⟨(eu_crra_hasDerivAt hx).const_mul _, (Real.mul_rpow hA.le hx.le).symm, ?_⟩
  simp only [cs_crra, hγ1, ↓reduceIte]
  have e : x * x ^ (-γ) = x ^ (1 - γ) := by
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add_one hx.ne']; ring
  rw [mul_left_comm, e]
  ring

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- **Exercise 7.10, pathwise** (Miao, p. 230), `γ ≠ 1`: along the plan `c_t = Ax_t`,
`u_a(y_t, R_t, y_{t+1}) · y_{t+1} = −(1 − γ)(1 − A) A^{−γ} u(x_t)`. -/
theorem ex_7_10_pathwise {R : ℕ → Ω → ℝ} {γ β A x₀ : ℝ} (hγ1 : γ ≠ 1)
    (hR : ∀ t ω, 0 < R t ω) (hR0 : ∀ ω, R 0 ω = 1) (hA0 : 0 < A) (hA1 : A < 1) (hx₀ : 0 < x₀)
    (t : ℕ) (ω : Ω) :
    eu_dot ((eu_phelpsModel γ β).ua (eu_phelpsState R A x₀ t ω) (R t ω)
        (eu_phelpsState R A x₀ (t + 1) ω)) (eu_phelpsState R A x₀ (t + 1) ω) =
      -((1 - γ) * (1 - A)) * (A ^ (-γ) * cs_crra γ (eu_phelpsCash R A x₀ t ω)) := by
  have hc := eu_phelpsCash_pos hR hA1 hx₀ t ω
  obtain ⟨-, -, hua, -⟩ := eu_phelps_derivs (γ := γ) (β := β) hR hR0 hA0 hA1 hx₀ t ω
  simp only [eu_dot, Fin.sum_univ_one, hua]
  obtain ⟨-, h2, h3⟩ := ex_7_10_envelope hγ1 hA0 hc
  have hp : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  rw [h3, ← h2]
  simp only [eu_phelpsState]
  field_simp

/-- **Exercise 7.10** (Miao, p. 230), `γ ≠ 1`: along the optimal plan of Example 7.5.1, the
transversality condition (7.35) of §7.5 holds if and only if the transversality condition (7.4)
of §7.1, `lim βᵀ E V(x_T) = 0` with `V = A^{−γ}u`, holds: the two sequences are proportional,
with factor `−(1 − γ)(1 − A) ≠ 0`. -/
theorem ex_7_10 {R : ℕ → Ω → ℝ} {γ β A x₀ : ℝ} (hγ1 : γ ≠ 1)
    (hR : ∀ t ω, 0 < R t ω) (hR0 : ∀ ω, R 0 ω = 1) (hA0 : 0 < A) (hA1 : A < 1) (hx₀ : 0 < x₀) :
    (eu_phelpsModel γ β).TVC735 P R (eu_phelpsState R A x₀) ↔
      Tendsto (fun T : ℕ => β ^ T *
        ∫ ω, A ^ (-γ) * cs_crra γ (eu_phelpsCash R A x₀ T ω) ∂P) atTop (𝓝 0) := by
  have hk : -((1 - γ) * (1 - A)) ≠ 0 := by
    have : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
    have : 1 - A ≠ 0 := by linarith
    exact neg_ne_zero.2 (mul_ne_zero ‹_› ‹_›)
  have heq : ∀ T : ℕ, (eu_phelpsModel γ β).β ^ T * ∫ ω, eu_dot ((eu_phelpsModel γ β).ua
      (eu_phelpsState R A x₀ T ω) (R T ω) (eu_phelpsState R A x₀ (T + 1) ω))
      (eu_phelpsState R A x₀ (T + 1) ω) ∂P =
      -((1 - γ) * (1 - A)) * (β ^ T *
        ∫ ω, A ^ (-γ) * cs_crra γ (eu_phelpsCash R A x₀ T ω) ∂P) := fun T => by
    simp only [ex_7_10_pathwise (β := β) hγ1 hR hR0 hA0 hA1 hx₀ T, integral_const_mul]
    change β ^ T * _ = _
    ring
  unfold eu_EulerModel.TVC735
  simp only [heq]
  constructor
  · intro h
    have := h.const_mul (-((1 - γ) * (1 - A)))⁻¹
    rw [mul_zero] at this
    exact this.congr fun T => by rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  · intro h
    simpa using h.const_mul (-((1 - γ) * (1 - A)))

/-- The log of cash on hand under `c_t = (1 − β)x_t`:
`ln x_t = ln x₀ + t ln β + Σ_{s<t} ln R_{s+1}`. -/
theorem ex7_log_cash {R : ℕ → Ω → ℝ} {β x₀ : ℝ} (hβ : 0 < β) (hR : ∀ t ω, 0 < R t ω)
    (hx₀ : 0 < x₀) (t : ℕ) (ω : Ω) :
    Real.log (eu_phelpsCash R (1 - β) x₀ t ω) =
      Real.log x₀ + t * Real.log β + ∑ s ∈ Finset.range t, Real.log (R (s + 1) ω) := by
  have hA : 1 - β < 1 := by linarith
  induction t with
  | zero => simp [eu_phelpsCash]
  | succ t ih =>
    have hc := eu_phelpsCash_pos hR hA hx₀ t ω
    have e : eu_phelpsCash R (1 - β) x₀ (t + 1) ω =
        R (t + 1) ω * ((1 - (1 - β)) * eu_phelpsCash R (1 - β) x₀ t ω) := rfl
    rw [e, show 1 - (1 - β) = β by ring, Real.log_mul (hR _ ω).ne' (mul_pos hβ hc).ne',
      Real.log_mul hβ.ne' hc.ne', ih, Finset.sum_range_succ]
    push_cast
    ring

/-- **Exercise 7.10, `γ = 1`** (Miao, p. 230): with `A = 1 − β`, the (7.35) term along the plan
is `βᵀ · (−β/(1 − β))`, so (7.35) holds; and if `ln R_{t+1}` is integrable with
`E ln R_{t+1} = mℓ` for all `t`, then `βᵀ E[b ln x_T + a] = βᵀ(b(ln x₀ + T(ln β + mℓ)) + a) → 0`
for all constants `a, b`: (7.4) holds too. -/
theorem ex_7_10_log [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} {β x₀ mℓ a b : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hR : ∀ t ω, 0 < R t ω) (hR0 : ∀ ω, R 0 ω = 1) (hx₀ : 0 < x₀)
    (hl : ∀ t, Integrable (fun ω => Real.log (R (t + 1) ω)) P)
    (hml : ∀ t, ∫ ω, Real.log (R (t + 1) ω) ∂P = mℓ) :
    (∀ T, (eu_phelpsModel 1 β).β ^ T * ∫ ω, eu_dot ((eu_phelpsModel 1 β).ua
      (eu_phelpsState R (1 - β) x₀ T ω) (R T ω) (eu_phelpsState R (1 - β) x₀ (T + 1) ω))
      (eu_phelpsState R (1 - β) x₀ (T + 1) ω) ∂P = -(β ^ T * (β / (1 - β)))) ∧
    (eu_phelpsModel 1 β).TVC735 P R (eu_phelpsState R (1 - β) x₀) ∧
    Tendsto (fun T : ℕ => β ^ T *
      ∫ ω, (b * Real.log (eu_phelpsCash R (1 - β) x₀ T ω) + a) ∂P) atTop (𝓝 0) := by
  have hA0 : 0 < 1 - β := by linarith
  have hA1 : 1 - β < 1 := by linarith
  have hdot : ∀ T ω, eu_dot ((eu_phelpsModel 1 β).ua (eu_phelpsState R (1 - β) x₀ T ω) (R T ω)
      (eu_phelpsState R (1 - β) x₀ (T + 1) ω)) (eu_phelpsState R (1 - β) x₀ (T + 1) ω) =
      -(β / (1 - β)) := fun T ω => by
    have hc := eu_phelpsCash_pos hR hA1 hx₀ T ω
    obtain ⟨-, -, hua, -⟩ := eu_phelps_derivs (γ := 1) (β := β) hR hR0 hA0 hA1 hx₀ T ω
    simp only [eu_dot, Fin.sum_univ_one, hua, Real.rpow_neg_one]
    simp only [eu_phelpsState, show 1 - (1 - β) = β by ring]
    field_simp
  have h1 : ∀ T, (eu_phelpsModel 1 β).β ^ T * ∫ ω, eu_dot ((eu_phelpsModel 1 β).ua
      (eu_phelpsState R (1 - β) x₀ T ω) (R T ω) (eu_phelpsState R (1 - β) x₀ (T + 1) ω))
      (eu_phelpsState R (1 - β) x₀ (T + 1) ω) ∂P = -(β ^ T * (β / (1 - β))) := fun T => by
    simp only [hdot, integral_const, probReal_univ, one_smul]
    change β ^ T * _ = _
    ring
  have hgeo := tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1
  refine ⟨h1, ?_, ?_⟩
  · unfold eu_EulerModel.TVC735
    simp only [h1]
    simpa using (hgeo.mul_const (β / (1 - β))).neg
  · have hint : ∀ T, ∫ ω, (b * Real.log (eu_phelpsCash R (1 - β) x₀ T ω) + a) ∂P =
        b * (Real.log x₀ + T * (Real.log β + mℓ)) + a := fun T => by
      have hs : ∀ ω, b * Real.log (eu_phelpsCash R (1 - β) x₀ T ω) + a =
          (b * (Real.log x₀ + T * Real.log β) + a) +
            ∑ s ∈ Finset.range T, b * Real.log (R (s + 1) ω) := fun ω => by
        rw [ex7_log_cash hβ hR hx₀, ← Finset.mul_sum]; ring
      simp only [hs]
      rw [integral_add (integrable_const _) (integrable_finsetSum _ fun s _ => (hl s).const_mul b),
        integral_const, probReal_univ, one_smul, integral_finsetSum _ fun s _ => (hl s).const_mul b]
      simp only [integral_const_mul, hml, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    simp only [hint]
    have hT : Tendsto (fun T : ℕ => (T : ℝ) * β ^ T) atTop (𝓝 0) :=
      tendsto_self_mul_const_pow_of_lt_one hβ.le hβ1
    have := (hgeo.mul_const (b * Real.log x₀ + a)).add (hT.mul_const (b * (Real.log β + mℓ)))
    simp only [zero_mul, add_zero] at this
    exact this.congr fun T => by ring

end Miao.InfiniteHorizonDP

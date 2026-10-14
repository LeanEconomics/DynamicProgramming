/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.LinearSystems

/-!
# Local stability of nonlinear systems

SLP Theorem 6.5, p. 147: let `x̄` be a stationary point of `x_{t+1} = h(x_t)`, with `h`
differentiable at `x̄` and Jacobian `A`. If every characteristic root of `A` is less than one in
absolute value, then `x_t → x̄` from every `x₀` near `x̄`.

The book cites Scheinkman (1973) and does not prove the theorem. Only differentiability of `h` at
`x̄` is used; the book assumes continuous differentiability on a neighbourhood and that `I − A` is
nonsingular, which follows from the root condition.

The proof:
* by Theorem 6.3, `Aᵗz → 0` for every `z`, so `‖Aᵗ‖ → 0` (`tendsto_opNorm_pow`) and
  `‖Aᵏ‖ ≤ 1/4` for some `k`;
* the `k`-step map `hᵏ` has derivative `Aᵏ` at `x̄`, so it halves distances to `x̄` nearby;
* continuity of `h, …, hᵏ⁻¹` at `x̄` carries convergence along multiples of `k` to all `t`.
-/

open Set Filter Topology Module
open scoped Matrix

namespace StokeyLucasPrescott.DeterministicDynamics

/-- With every characteristic root inside the unit disc, `Aᵗz → 0` for every real `z`. -/
theorem tendsto_pow_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (h : ∀ μ : ℂ, (A.charpoly.map Complex.ofRealHom).IsRoot μ → ‖μ‖ < 1) (z : ι → ℝ) :
    Tendsto (fun t => (A ^ t) *ᵥ z) atTop (𝓝 0) := by
  have htop := stable_eq_top (cplxEnd A) fun μ hμ => h μ ((hasEigenvalue_cplxEnd_iff A μ).1 hμ)
  have := (tendsto_iff_mem_stable (cplxEnd A) (cplx z)).2 (by rw [htop]; exact Submodule.mem_top)
  simp only [cplxEnd_pow_cplx] at this
  exact tendsto_cplx_iff.1 this

variable {n : ℕ}

/-- `A` as a continuous linear map on `ℝⁿ`. -/
noncomputable def matCLM (A : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

theorem matCLM_pow_apply (A : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) (z : Fin n → ℝ) :
    (matCLM A ^ t) z = (A ^ t) *ᵥ z := by
  induction t generalizing z with
  | zero => simp
  | succ t ih =>
    rw [pow_succ']
    change matCLM A ((matCLM A ^ t) z) = _
    rw [ih, pow_succ', ← Matrix.mulVec_mulVec]
    rfl

/-- Pointwise convergence to zero of powers gives convergence of operator norms. -/
theorem tendsto_opNorm_pow (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ μ : ℂ, (A.charpoly.map Complex.ofRealHom).IsRoot μ → ‖μ‖ < 1) :
    Tendsto (fun t => ‖matCLM A ^ t‖) atTop (𝓝 0) := by
  set e : Fin n → Fin n → ℝ := fun i => Pi.single i 1
  have hsum : Tendsto (fun t => ∑ i, ‖(matCLM A ^ t) (e i)‖) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ i : Fin n, ‖(0 : Fin n → ℝ)‖ by simp]
    refine tendsto_finsetSum _ fun i _ => ?_
    simp only [matCLM_pow_apply]
    exact (tendsto_pow_mulVec A h (e i)).norm
  -- `‖L‖ ≤ Σᵢ ‖L eᵢ‖`
  have hbound : ∀ t, ‖matCLM A ^ t‖ ≤ ∑ i, ‖(matCLM A ^ t) (e i)‖ := fun t => by
    refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      fun z => ?_
    have hz : z = ∑ i, z i • e i := by
      funext j; simp [e, Pi.single_apply]
    calc ‖(matCLM A ^ t) z‖ = ‖∑ i, z i • (matCLM A ^ t) (e i)‖ := by
          conv_lhs => rw [hz]
          rw [map_sum]; simp only [map_smul]
      _ ≤ ∑ i, ‖z i • (matCLM A ^ t) (e i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖z‖ * ‖(matCLM A ^ t) (e i)‖ := Finset.sum_le_sum fun i _ => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (norm_le_pi_norm z i) (norm_nonneg _)
      _ = (∑ i, ‖(matCLM A ^ t) (e i)‖) * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]
  exact squeeze_zero (fun t => norm_nonneg _) hbound hsum

/-- **Theorem 6.5.** Let `h(x̄) = x̄`, with `h` differentiable at `x̄` and Jacobian `A` there. If
every characteristic root of `A` is less than one in absolute value, there is a neighbourhood `U`
of `x̄` such that `x_t → x̄` whenever `x₀ ∈ U`. -/
theorem theorem_6_5 (h : (Fin n → ℝ) → (Fin n → ℝ)) {xbar : Fin n → ℝ} (hfix : h xbar = xbar)
    (A : Matrix (Fin n) (Fin n) ℝ) (hd : HasFDerivAt h (matCLM A) xbar)
    (hroots : ∀ μ : ℂ, (A.charpoly.map Complex.ofRealHom).IsRoot μ → ‖μ‖ < 1) :
    ∃ U ∈ 𝓝 xbar, ∀ x₀ ∈ U, Tendsto (fun t => h^[t] x₀) atTop (𝓝 xbar) := by
  -- a power `Aᵏ` of norm at most `1/4`, with `k ≥ 1`
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_opNorm_pow A hroots).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  set k := k₀ + 1
  have hk : ‖matCLM A ^ k‖ < 1 / 4 := hk₀ k (by omega)
  -- `hᵏ` has derivative `Aᵏ` at `x̄`
  have hdk : HasFDerivAt h^[k] (matCLM A ^ k) xbar := hd.iterate hfix k
  obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1
    (hdk.isLittleO.def (show (0 : ℝ) < 1 / 4 by norm_num))
  have hfixk : ∀ j, h^[j] xbar = xbar := fun j => Function.iterate_fixed hfix j
  -- the `k`-step map halves distances to `x̄` on the `δ`-ball
  have hhalf : ∀ y, dist y xbar < δ → dist (h^[k] y) xbar ≤ 1 / 2 * dist y xbar := by
    intro y hy
    have h1 := hδs hy
    rw [hfixk k] at h1
    rw [dist_eq_norm, dist_eq_norm]
    have h2 : ‖(matCLM A ^ k) (y - xbar)‖ ≤ 1 / 4 * ‖y - xbar‖ :=
      ((matCLM A ^ k).le_opNorm _).trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _))
    calc ‖h^[k] y - xbar‖ = ‖(h^[k] y - xbar - (matCLM A ^ k) (y - xbar)) +
          (matCLM A ^ k) (y - xbar)‖ := by congr 1; abel
      _ ≤ 1 / 4 * ‖y - xbar‖ + 1 / 4 * ‖y - xbar‖ := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = 1 / 2 * ‖y - xbar‖ := by ring
  -- each `hʲ`, `j < k`, is continuous at `x̄`
  have hcont : ∀ j, ContinuousAt h^[j] xbar := fun j =>
    (hd.iterate hfix j).continuousAt
  refine ⟨Metric.ball xbar δ, Metric.ball_mem_nhds _ hδ, fun x₀ hx₀ => ?_⟩
  -- along multiples of `k`: `dist ≤ (1/2)ʲ dist(x₀, x̄)`
  have hgeom : ∀ j, dist (h^[k * j] x₀) xbar ≤ (1 / 2) ^ j * dist x₀ xbar := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hin : dist (h^[k * j] x₀) xbar < δ := ih.trans_lt (by
        have : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have := Metric.mem_ball.1 hx₀
        nlinarith [dist_nonneg (x := x₀) (y := xbar)])
      rw [show k * (j + 1) = k + k * j by ring, Function.iterate_add_apply]
      calc dist (h^[k] (h^[k * j] x₀)) xbar ≤ 1 / 2 * dist (h^[k * j] x₀) xbar := hhalf _ hin
        _ ≤ 1 / 2 * ((1 / 2) ^ j * dist x₀ xbar) := by gcongr
        _ = (1 / 2) ^ (j + 1) * dist x₀ xbar := by ring
  have hmul : Tendsto (fun j => h^[k * j] x₀) atTop (𝓝 xbar) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) hgeom ?_)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_const (dist x₀ xbar)
  -- every `t` is `k(t/k) + t % k`
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hη : ∀ r, ∃ η > 0, ∀ y, dist y xbar < η → dist (h^[r] y) xbar < ε := fun r => by
    obtain ⟨η, hη, hηs⟩ := Metric.continuousAt_iff.1 (hcont r) ε hε
    exact ⟨η, hη, fun y hy => by rw [← hfixk r]; exact hηs hy⟩
  choose η hηpos hηs using hη
  set η₀ := (Finset.range k).inf' ⟨0, by simp [k]⟩ η
  have hη₀ : 0 < η₀ := (Finset.lt_inf'_iff _).2 fun r _ => hηpos r
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hmul η₀ hη₀
  refine ⟨k * J, fun t ht => ?_⟩
  have hdecomp : t = t % k + k * (t / k) := (Nat.mod_add_div t k).symm
  rw [hdecomp, Function.iterate_add_apply]
  have hJt : J ≤ t / k := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact ht)
  have hr : t % k ∈ Finset.range k := Finset.mem_range.2 (Nat.mod_lt _ (by omega))
  exact hηs (t % k) _ ((hJ _ hJt).trans_le (Finset.inf'_le _ hr))

end StokeyLucasPrescott.DeterministicDynamics

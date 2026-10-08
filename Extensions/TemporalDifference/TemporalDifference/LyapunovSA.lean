/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TemporalDifference.RobbinsSiegmund

/-!
# Stochastic approximation with a quadratic Lyapunov function

The Robbins–Monro iteration `θ_{k+1} = θ_k + α_k(h(θ_k) + W_k)` in a real Hilbert space
converges almost surely to the zero `θ̄` of the mean dynamics `h` when there is a quadratic
Lyapunov function `V(x) = ⟪Q(x − θ̄), x − θ̄⟫` along which `h` points inwards:
`⟪Q(x − θ̄), h(x)⟫ ≤ −κ‖x − θ̄‖²`, with `Q` symmetric and coercive and `h` growing at most
linearly away from `θ̄`. This is the classical ODE (Lyapunov) criterion of stochastic
approximation (Ljung, 1977; Benveniste, Métivier and Priouret, 1990) in its
quadratic form, and the convergence criterion behind E-stability (Evans and Honkapohja, 2001).

* `sa_lyapunov`: the convergence theorem. `V(θ_k)` satisfies the Robbins–Siegmund inequality
  with `c_k = 2κα_k‖θ_k − θ̄‖²`, so `V(θ_k)` converges and `∑ α_k‖θ_k − θ̄‖² < ∞`, which with
  `∑ α_k = ∞` forces the limit to be `0`.

No contraction is assumed, and the step sizes need not be below `1`. Copied from the
`Extensions/AdaptiveLearning` project.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace DPExtensions.TemporalDifference

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℕ m0}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Stochastic approximation with a quadratic Lyapunov function.** Let
`θ_{k+1} = θ_k + α_k(h(θ_k) + W_k)` with `h` continuous, `‖h(x)‖ ≤ L‖x − θ̄‖`, and a bounded
symmetric operator `Q` with `⟪Qx, x⟫ ≥ m‖x‖²` (`m > 0`) and
`⟪Q(x − θ̄), h(x)⟫ ≤ −κ‖x − θ̄‖²` (`κ > 0`). If `θ₀` and the `W_k` are square integrable,
`θ₀` is `ℱ₀`-measurable, `W_k` is `ℱ_{k+1}`-measurable with `𝔼[W_k | ℱ_k] = 0` and
`𝔼[‖W_k‖² | ℱ_k] ≤ C(1 + ‖θ_k‖²)`, and `α_k ≥ 0` with `∑ α_k = ∞` and `∑ α_k² < ∞`, then
`θ_k → θ̄` almost surely. -/
theorem sa_lyapunov {h : E → E} (hhc : Continuous h) {θbar : E} {Q : E →L[ℝ] E}
    (hQsym : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y)) {m κ L : ℝ} (hm : 0 < m) (hκ : 0 < κ)
    (hQpos : ∀ x, m * ‖x‖ ^ 2 ≤ inner ℝ (Q x) x)
    (hdrift : ∀ x, inner ℝ (Q (x - θbar)) (h x) ≤ -κ * ‖x - θbar‖ ^ 2)
    (hlin : ∀ x, ‖h x‖ ≤ L * ‖x - θbar‖)
    {α : ℕ → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hdiv : ¬ Summable α) (hsq : Summable fun k => α k ^ 2)
    {θ W : ℕ → Ω → E}
    (hrec : ∀ k ω, θ (k + 1) ω = θ k ω + α k • (h (θ k ω) + W k ω))
    (hθ0m : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0 : MemLp (θ 0) 2 P)
    (hWm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (W k)) (hW2 : ∀ k, MemLp (W k) 2 P)
    (hW0 : ∀ k, P[W k | ℱ k] =ᵐ[P] 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k, P[fun ω => ‖W k ω‖ ^ 2 | ℱ k] ≤ᵐ[P] fun ω => C * (1 + ‖θ k ω‖ ^ 2)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => θ k ω) atTop (𝓝 θbar) := by
  set M := ‖Q‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  have hQb : ∀ x y, |inner ℝ (Q x) y| ≤ M * (‖x‖ * ‖y‖) := fun x y =>
    (abs_real_inner_le_norm _ _).trans (by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (Q.le_opNorm x) (norm_nonneg _))
  have hQsq : ∀ x, |inner ℝ (Q x) x| ≤ M * ‖x‖ ^ 2 := fun x => by
    have := hQb x x
    rwa [← sq] at this
  have hhsq : ∀ x, ‖h x‖ ^ 2 ≤ L ^ 2 * ‖x - θbar‖ ^ 2 := fun x => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hlin x) 2
  -- adaptedness and square integrability of the iterates
  have hhL : ∀ {f : Ω → E}, MemLp f 2 P → MemLp (fun ω => h (f ω)) 2 P := fun {f} hf =>
    ((hf.sub (memLp_const θbar)).norm.const_mul L).mono'
      (hhc.comp_aestronglyMeasurable hf.aestronglyMeasurable) (Eventually.of_forall fun ω => by
        simp only [Pi.sub_apply]
        exact hlin _)
  have hθ : ∀ k, StronglyMeasurable[ℱ k] (θ k) ∧ MemLp (θ k) 2 P := by
    intro k
    induction k with
    | zero => exact ⟨hθ0m, hθ0⟩
    | succ k ih =>
      obtain ⟨hm', hL⟩ := ih
      have he : θ (k + 1) = fun ω => θ k ω + α k • (h (θ k ω) + W k ω) := funext (hrec k)
      have hm'' : StronglyMeasurable[ℱ (k + 1)] (θ k) := hm'.mono (ℱ.mono k.le_succ)
      rw [he]
      exact ⟨hm''.add (((hhc.comp_stronglyMeasurable hm'').add (hWm k)).const_smul (α k)),
        hL.add (((hhL hL).add (hW2 k)).const_smul (α k))⟩
  have hesq : ∀ k, Integrable (fun ω => ‖θ k ω - θbar‖ ^ 2) P := fun k =>
    (memLp_two_iff_integrable_sq_norm
      ((hθ k).2.sub (memLp_const θbar)).aestronglyMeasurable).1
      ((hθ k).2.sub (memLp_const θbar))
  have hesm : ∀ k, StronglyMeasurable[ℱ k] fun ω => ‖θ k ω - θbar‖ ^ 2 := fun k =>
    ((hθ k).1.sub stronglyMeasurable_const).norm.pow 2
  -- `Y_k = V(θ_k)`
  set Y : ℕ → Ω → ℝ := fun k ω => inner ℝ (Q (θ k ω - θbar)) (θ k ω - θbar) with hYdef
  have hYm : StronglyAdapted ℱ Y := fun k =>
    (Q.continuous.comp_stronglyMeasurable ((hθ k).1.sub stronglyMeasurable_const)).inner
      ((hθ k).1.sub stronglyMeasurable_const)
  have hYlow : ∀ k ω, m * ‖θ k ω - θbar‖ ^ 2 ≤ Y k ω := fun k ω => hQpos _
  have hYup : ∀ k ω, Y k ω ≤ M * ‖θ k ω - θbar‖ ^ 2 := fun k ω =>
    (le_abs_self _).trans (hQsq _)
  have hY0 : ∀ k ω, 0 ≤ Y k ω := fun k ω =>
    (mul_nonneg hm.le (sq_nonneg _)).trans (hYlow k ω)
  have hYi : ∀ k, Integrable (Y k) P := fun k =>
    ((hesq k).const_mul M).mono' ((hYm k).mono (ℱ.le k)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact hQsq _)
  set c : ℕ → Ω → ℝ := fun k ω => 2 * κ * α k * ‖θ k ω - θbar‖ ^ 2 with hcdef
  set a : ℕ → ℝ := fun k => α k ^ 2 * ((M * L ^ 2 + 2 * M * C) / m) with hadef
  set b : ℕ → ℝ := fun k => α k ^ 2 * (M * C * (1 + 2 * ‖θbar‖ ^ 2)) with hbdef
  have hstep : ∀ k, P[Y (k + 1) | ℱ k] ≤ᵐ[P] fun ω => (1 + a k) * Y k ω + b k - c k ω := by
    intro k
    set u : Ω → E := fun ω => θ k ω - θbar + α k • h (θ k ω)
    have hum : StronglyMeasurable[ℱ k] u :=
      ((hθ k).1.sub stronglyMeasurable_const).add
        ((hhc.comp_stronglyMeasurable (hθ k).1).const_smul (α k))
    have huL : MemLp u 2 P :=
      ((hθ k).2.sub (memLp_const θbar)).add ((hhL (hθ k).2).const_smul (α k))
    have hQum : StronglyMeasurable[ℱ k] fun ω => Q (u ω) := Q.continuous.comp_stronglyMeasurable hum
    have hsplit : ∀ ω, θ (k + 1) ω - θbar = u ω + α k • W k ω := fun ω => by
      rw [hrec]
      simp only [u, smul_add]
      abel
    set U : Ω → ℝ := fun ω => inner ℝ (Q (u ω)) (u ω)
    set I : Ω → ℝ := fun ω => innerSL ℝ (Q (u ω)) (W k ω)
    set N : Ω → ℝ := fun ω => inner ℝ (Q (W k ω)) (W k ω)
    have hYsplit : Y (k + 1) = U + (2 * α k) • I + (α k ^ 2) • N := by
      funext ω
      simp only [hYdef, U, I, N, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsplit,
        innerSL_apply_apply, map_add, map_smul, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hQsym (W k ω) (u ω), real_inner_comm (Q (u ω)) (W k ω)]
      ring
    have huq : Integrable (fun ω => ‖u ω‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm huL.aestronglyMeasurable).1 huL
    have hwq : Integrable (fun ω => ‖W k ω‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm (hW2 k).aestronglyMeasurable).1 (hW2 k)
    have hUm : StronglyMeasurable[ℱ k] U := hQum.inner hum
    have hUi : Integrable U P :=
      (huq.const_mul M).mono' (hUm.mono (ℱ.le k)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]
          exact hQsq _)
    have hNm : StronglyMeasurable N :=
      (Q.continuous.comp_stronglyMeasurable ((hWm k).mono (ℱ.le (k + 1)))).inner
        ((hWm k).mono (ℱ.le (k + 1)))
    have hNi : Integrable N P :=
      (hwq.const_mul M).mono' hNm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]
          exact hQsq _)
    have hIi : Integrable I P := by
      refine ((huq.add hwq).const_mul M).mono' ?_ (Eventually.of_forall fun ω => ?_)
      · exact ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous₂.comp_aestronglyMeasurable₂
          (hQum.mono (ℱ.le k)).aestronglyMeasurable (hW2 k).aestronglyMeasurable)
      · simp only [I, Pi.add_apply, innerSL_apply_apply, Real.norm_eq_abs]
        refine (hQb _ _).trans (mul_le_mul_of_nonneg_left ?_ hM0)
        nlinarith [sq_nonneg (‖u ω‖ - ‖W k ω‖), norm_nonneg (u ω), norm_nonneg (W k ω)]
    have hcI : P[I | ℱ k] =ᵐ[P] 0 := by
      have h1 := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
        hQum.aestronglyMeasurable hIi ((hW2 k).integrable one_le_two)
      filter_upwards [h1, hW0 k] with ω h1 h2
      rw [h1, h2]
      simp
    have hcN : P[N | ℱ k] ≤ᵐ[P] fun ω => M * (C * (1 + ‖θ k ω‖ ^ 2)) := by
      have h1 := condExp_mono (m := ℱ k) hNi (hwq.const_mul M)
        (Eventually.of_forall fun ω => (le_abs_self _).trans (hQsq _))
      have h2 := condExp_smul (μ := P) M (fun ω => ‖W k ω‖ ^ 2) (ℱ k)
      filter_upwards [h1, h2, hC k] with ω e1 e2 e3
      have e2' : P[fun ω => M * ‖W k ω‖ ^ 2 | ℱ k] ω = M * P[fun ω => ‖W k ω‖ ^ 2 | ℱ k] ω := e2
      exact e1.trans (e2'.le.trans (mul_le_mul_of_nonneg_left e3 hM0))
    rw [hYsplit]
    have hsum := condExp_add (hUi.add (hIi.smul (2 * α k))) (hNi.smul (α k ^ 2)) (ℱ k)
    have hsum2 := condExp_add hUi (hIi.smul (2 * α k)) (ℱ k)
    have hs1 := condExp_smul (μ := P) (2 * α k) I (ℱ k)
    have hs2 := condExp_smul (μ := P) (α k ^ 2) N (ℱ k)
    have hU := condExp_of_stronglyMeasurable (ℱ.le k) hUm hUi
    filter_upwards [hsum, hsum2, hs1, hs2, hcI, hcN] with ω e1 e2 e3 e4 e5 e6
    rw [e1, Pi.add_apply, e2, Pi.add_apply, hU, e3, e4, Pi.smul_apply, Pi.smul_apply, e5,
      smul_eq_mul, smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
    -- the deterministic part
    set e := θ k ω - θbar with hedef
    have hUexp : U ω = Y k ω + 2 * α k * inner ℝ (Q e) (h (θ k ω)) +
        α k ^ 2 * inner ℝ (Q (h (θ k ω))) (h (θ k ω)) := by
      simp only [U, u, hYdef, map_add, map_smul, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hQsym (h (θ k ω)) e, real_inner_comm (Q e) (h (θ k ω))]
      ring
    have hd := hdrift (θ k ω)
    have hhh : inner ℝ (Q (h (θ k ω))) (h (θ k ω)) ≤ M * (L ^ 2 * ‖e‖ ^ 2) :=
      (le_abs_self _).trans ((hQsq _).trans (mul_le_mul_of_nonneg_left (hhsq _) hM0))
    have hθsq : ‖θ k ω‖ ^ 2 ≤ 2 * ‖e‖ ^ 2 + 2 * ‖θbar‖ ^ 2 := by
      have h1 : ‖θ k ω‖ ≤ ‖e‖ + ‖θbar‖ := by
        have := norm_add_le e θbar
        rwa [hedef, sub_add_cancel] at this
      nlinarith [sq_nonneg (‖e‖ - ‖θbar‖), norm_nonneg (θ k ω), norm_nonneg e,
        norm_nonneg θbar]
    have hey : ‖e‖ ^ 2 ≤ Y k ω / m := by
      rw [le_div_iff₀ hm, mul_comm]
      exact hYlow k ω
    have hK0 : 0 ≤ M * L ^ 2 + 2 * M * C := by positivity
    have hα2 : 0 ≤ α k ^ 2 := sq_nonneg _
    have hA : α k ^ 2 * ((M * L ^ 2 + 2 * M * C) * ‖e‖ ^ 2) ≤ a k * Y k ω := by
      have h1 : (M * L ^ 2 + 2 * M * C) * ‖e‖ ^ 2 ≤ (M * L ^ 2 + 2 * M * C) * (Y k ω / m) :=
        mul_le_mul_of_nonneg_left hey hK0
      have h2 : a k * Y k ω = α k ^ 2 * ((M * L ^ 2 + 2 * M * C) * (Y k ω / m)) := by
        simp only [hadef]
        ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 hα2
    have hN' : α k ^ 2 * (M * (C * (1 + ‖θ k ω‖ ^ 2))) ≤
        α k ^ 2 * (2 * M * C * ‖e‖ ^ 2) + b k := by
      simp only [hbdef]
      have : M * (C * (1 + ‖θ k ω‖ ^ 2)) ≤ 2 * M * C * ‖e‖ ^ 2 + M * C * (1 + 2 * ‖θbar‖ ^ 2) := by
        have hMC : 0 ≤ M * C := mul_nonneg hM0 hC0
        nlinarith [mul_le_mul_of_nonneg_left hθsq hMC]
      nlinarith [mul_le_mul_of_nonneg_left this hα2]
    have hα := hα0 k
    have hcdrift : 2 * α k * inner ℝ (Q e) (h (θ k ω)) ≤ -c k ω := by
      simp only [hcdef]
      have := mul_le_mul_of_nonneg_left hd (mul_nonneg zero_le_two hα)
      linarith
    have hhh' : α k ^ 2 * inner ℝ (Q (h (θ k ω))) (h (θ k ω)) ≤
        α k ^ 2 * (M * L ^ 2 * ‖e‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hhh hα2
      linarith
    have hcomb : α k ^ 2 * (M * L ^ 2 * ‖e‖ ^ 2) + α k ^ 2 * (2 * M * C * ‖e‖ ^ 2) =
        α k ^ 2 * ((M * L ^ 2 + 2 * M * C) * ‖e‖ ^ 2) := by ring
    have hN'' : α k ^ 2 * P[N | ℱ k] ω ≤ α k ^ 2 * (M * (C * (1 + ‖θ k ω‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left e6 hα2
    rw [hUexp]
    nlinarith
  -- Robbins–Siegmund
  have hcad : StronglyAdapted ℱ c := fun k => stronglyMeasurable_const.mul (hesm k)
  have hci : ∀ k, Integrable (c k) P := fun k => (hesq k).const_mul _
  have hc0 : ∀ k ω, 0 ≤ c k ω := fun k ω =>
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hκ.le) (hα0 k)) (sq_nonneg _)
  have ha : ∀ k, 0 ≤ a k := fun k =>
    mul_nonneg (sq_nonneg _) (div_nonneg (by positivity) hm.le)
  have hb : ∀ k, 0 ≤ b k := fun k => mul_nonneg (sq_nonneg _) (by positivity)
  have hRS := robbins_siegmund hYm hcad hYi hci hY0 hc0 ha hb (hsq.mul_right _)
    (hsq.mul_right _) hstep
  filter_upwards [hRS] with ω hω
  obtain ⟨⟨Lim, hLim⟩, hcs⟩ := hω
  have hLim0 : Lim = 0 := by
    have hLnn : 0 ≤ Lim := ge_of_tendsto' hLim fun k => hY0 k ω
    by_contra hne
    have hLpos : 0 < Lim := lt_of_le_of_ne hLnn (Ne.symm hne)
    have hev : ∀ᶠ k in atTop, Lim / 2 < Y k ω :=
      hLim.eventually (lt_mem_nhds (half_lt_self hLpos))
    apply hdiv
    refine Summable.of_norm_bounded_eventually (hcs.mul_left (M / (κ * Lim))) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with k hk
    rw [Real.norm_eq_abs, abs_of_nonneg (hα0 k), div_mul_eq_mul_div,
      le_div_iff₀ (mul_pos hκ hLpos)]
    simp only [hcdef]
    have h1 := mul_le_mul_of_nonneg_left hk.le (hα0 k)
    have h2 := mul_le_mul_of_nonneg_left (hYup k ω) (hα0 k)
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hκ.le]
  rw [hLim0] at hLim
  have hsq0 : Tendsto (fun k => ‖θ k ω - θbar‖ ^ 2) atTop (𝓝 0) := by
    have hup : Tendsto (fun k => Y k ω / m) atTop (𝓝 0) := by
      simpa using hLim.div_const m
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => sq_nonneg _) fun k => ?_
    rw [le_div_iff₀ hm, mul_comm]
    exact hYlow k ω
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : (fun k => ‖θ k ω - θbar‖) = fun k => Real.sqrt (‖θ k ω - θbar‖ ^ 2) :=
    funext fun k => (Real.sqrt_sq (norm_nonneg _)).symm
  rw [e]
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq0
  rw [Real.sqrt_zero] at h
  exact h

end DPExtensions.TemporalDifference

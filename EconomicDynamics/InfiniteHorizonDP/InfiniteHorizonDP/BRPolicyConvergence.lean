/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.BRConcave

/-!
# Theorem 7.3.5: convergence of the policy functions

Miao, §7.3.1, pp. 210–211; the proof is SLP's Theorem 9.9 (Exercise 9.7e), whose argument is
followed: for `n ≥ 1`, `vₙ = Tⁿv₀` is strictly concave and strictly increasing in `x`, so the
objective `u + β ∫ vₙ(φ(·), ·) dQ` has a unique maximizer `gₙ`; the objectives converge uniformly
on the graph of `Γ` (`br_abs_obj_sub_le`, (7.17)); and SLP Theorem 3.8 (`theorem_3_8`,
`theorem_3_8_uniform`) gives `gₙ → g` pointwise, uniformly when `X × Z` is compact.

* **Theorem 7.3.5** (`theorem_7_3_5`).
* `p211`: the remark `Tⁿ0 = V_{N−n}^N = V₀ⁿ`, and `gₙ` (the maximizer for `vₙ = Tⁿ0`) is the
  initial decision rule of an optimal plan of the **`(n + 1)`-horizon** problem.

**Corrections.** (1) As for Theorem 7.3.3, the hypotheses need Assumption 6.4.11 and the
injectivity of `φ(x, ·, z, z′)`, and the starting function `v₀` must be concave *and*
nondecreasing in `x` (the book's `C′(S)` is the functions concave on `X`): `T` preserves
concavity of `f(φ(·), ·)` only for nondecreasing `f`. (2) The book says `gₙ` is "the initial
policy function" of the `n`-horizon problem. The `n`-horizon problem's initial decision maximizes
`u + β ∫ V₀^{n−1}`, with `V₀^{n−1} = T^{n−1}0`, whereas `gₙ` maximizes `u + β ∫ Tⁿ0`: `gₙ` is the
initial policy of the `(n + 1)`-horizon problem (`p211`).
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

/-- `|br_obj f − br_obj g| ≤ β‖f − g‖` (`β ≥ 0`). -/
theorem br_abs_obj_sub_le {S A : Type*} [MetricSpace S] [MetricSpace A] [MeasurableSpace S]
    [MeasurableSpace A] [OpensMeasurableSpace S] {M : MDP S A} (h : br_Standing M)
    (hβ : 0 ≤ M.β) (f g : S →ᵇ ℝ) (p : S × A) :
    |br_obj M f p - br_obj M g p| ≤ M.β * dist f g := by
  have := h.markov 0
  have e : br_obj M f p - br_obj M g p = M.β * ∫ s', (f s' - g s') ∂M.P 0 p := by
    simp only [br_obj]
    rw [integral_sub (br_integrable h f p) (br_integrable h g p)]
    ring
  rw [e, abs_mul, abs_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left (br_abs_integral_le fun s => by
    rw [← Real.dist_eq]; exact dist_coe_le_dist s) hβ

variable {E F Z : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MetricSpace Z] [MeasurableSpace E] [MeasurableSpace F]
  [BorelSpace E] [BorelSpace F] [BorelSpace Z] [SecondCountableTopology F]
  [SecondCountableTopology Z] {M : OCModel E F Z}

/-- The iterates `Tⁿv₀` of a function concave and nondecreasing in `x` stay concave and
nondecreasing, and are strictly concave and strictly increasing for `n ≥ 1`. -/
theorem br_iterate_concave [IsMarkovKernel M.Q] [PartialOrder E] (h641 : M.Assumption641)
    (h642 : M.Assumption642) (h644 : M.Assumption644) (h645 : M.Assumption645)
    (h648 : M.Assumption648) (h649 : M.Assumption649) (h6411 : M.Assumption6411)
    (h6412 : M.Assumption6412) (h732 : Assumption732 M) (h733 : Assumption733 M) (hβ : 0 ≤ M.β)
    (h : br_Standing (br_ctrlMDP M h645.1)) {v₀ : ↥M.X × Z →ᵇ ℝ}
    (hv₀ : ∀ z, ConcaveOn ℝ M.X (fun x => br_ext v₀ x z) ∧ Monotone fun x : ↥M.X => v₀ (x, z))
    (n : ℕ) (z : Z) :
    StrictConcaveOn ℝ M.X (fun x => br_ext ((br_T h)^[n + 1] v₀) x z) ∧
      StrictMono fun x : ↥M.X => (br_T h)^[n + 1] v₀ (x, z) := by
  have hmaps : ∀ f : ↥M.X × Z →ᵇ ℝ, (∀ z, ConcaveOn ℝ M.X (fun x => br_ext f x z) ∧
      Monotone fun x : ↥M.X => f (x, z)) → ∀ z,
      StrictConcaveOn ℝ M.X (fun x => br_ext (br_T h f) x z) ∧
        StrictMono fun x : ↥M.X => br_T h f (x, z) := fun f hf z =>
    ⟨br_T_strictConcave h641 h644 h645 h6411 h733 hβ h
      (br_compConcave_of_mono h641 h642 h645 h6412 (fun z => (hf z).1)
        fun z => br_monotoneOn_ext (hf z).2) z,
      br_T_strictMono h645 h648 h649 h732 hβ h (fun z => (hf z).2) z⟩
  have hall : ∀ n : ℕ, ∀ z, ConcaveOn ℝ M.X (fun x => br_ext ((br_T h)^[n] v₀) x z) ∧
      Monotone fun x : ↥M.X => (br_T h)^[n] v₀ (x, z) := by
    intro n
    induction n with
    | zero => exact hv₀
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply']
      exact ⟨(hmaps _ ih z).1.concaveOn, (hmaps _ ih z).2.monotone⟩
  rw [Function.iterate_succ_apply']
  exact hmaps _ (hall n) z

/-- **Theorem 7.3.5 (Convergence)** (Miao, p. 211), corrected. Under the hypotheses of
`theorem_7_3_3` (with Assumption 6.4.11 and `φ(x, ·, z, z′)` one-to-one), let `v₀ ∈ C(S)` be
concave and nondecreasing in `x`, `vₙ = Tⁿv₀` and `gₙ` the maximizer of
`u(x, z, a) + β ∫ vₙ(φ(x, a, z, z′), z′) Q(z, dz′)` over `Γ(x, z)` (unique for `n ≥ 1`). Then
`gₙ → g` pointwise, and uniformly if `X` and `Z` are compact. -/
theorem theorem_7_3_5 [IsMarkovKernel M.Q] [PartialOrder E] [Nonempty ↥M.A]
    (h641 : M.Assumption641) (h642 : M.Assumption642) (h644 : M.Assumption644)
    (h645 : M.Assumption645) (h648 : M.Assumption648) (h649 : M.Assumption649)
    (h6411 : M.Assumption6411) (h6412 : M.Assumption6412) (h732 : Assumption732 M)
    (h733 : Assumption733 M) (hinj : M.PhiInjA) (h512 : 0 < M.β ∧ M.β < 1)
    (h : br_Standing (br_ctrlMDP M h645.1)) {v : ↥M.X × Z →ᵇ ℝ} (hv : br_T h v = v)
    {v₀ : ↥M.X × Z →ᵇ ℝ}
    (hv₀ : ∀ z, ConcaveOn ℝ M.X (fun x => br_ext v₀ x z) ∧ Monotone fun x : ↥M.X => v₀ (x, z)) :
    (∀ s, Tendsto (fun n => br_policy h645 ((br_T h)^[n] v₀) s) atTop
      (𝓝 (br_policy h645 v s))) ∧
    (IsCompact M.X → CompactSpace Z →
      TendstoUniformly (fun n => br_policy h645 ((br_T h)^[n] v₀)) (br_policy h645 v) atTop) := by
  set T := br_T h
  set M' := br_ctrlMDP M h645.1
  have hU : ∀ n, UniqueArgmax M'.Γ (br_obj M' (T^[n + 1] v₀)) := fun n =>
    (br_policy_spec h645 h (br_G_unique h645 h642 h6411 h733 h512.1 h
      (br_compStrict_of_mono h641 h642 h645 h6412 hinj
        (fun z => (br_iterate_concave h641 h642 h644 h645 h648 h649 h6411 h6412 h732 h733
          h512.1.le h hv₀ n z).1)
        fun z => br_monotoneOn_ext (br_iterate_concave h641 h642 h644 h645 h648 h649 h6411
          h6412 h732 h733 h512.1.le h hv₀ n z).2.monotone))).1
  have hV := theorem_7_3_3 h641 h642 h644 h645 h648 h649 h6411 h6412 h732 h733 h512 h hv
  have hUv : UniqueArgmax M'.Γ (br_obj M' v) :=
    (br_policy_spec h645 h (br_G_unique h645 h642 h6411 h733 h512.1 h
      (br_compStrict_of_mono h641 h642 h645 h6412 hinj hV.1
        fun z => br_monotoneOn_ext (hV.2.1 z).monotone))).1
  have hunif : TendstoUniformlyOn (fun n => br_obj M' (T^[n + 1] v₀)) (br_obj M' v) atTop
      (graph M'.Γ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => M.β * (M.β ^ (n + 1) * dist v₀ v)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h512.1.le h512.2).comp
        (tendsto_add_atTop_nat 1)).mul_const (dist v₀ v) |>.const_mul M.β
      simpa using this
    filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn p _
    rw [Real.dist_eq]
    refine lt_of_le_of_lt ((br_abs_obj_sub_le h h512.1.le v (T^[n + 1] v₀) p).trans ?_) hn
    refine mul_le_mul_of_nonneg_left ?_ h512.1.le
    rw [dist_comm]
    exact eq_7_17 h h512 hv v₀ (n + 1)
  refine ⟨fun s => ?_, fun hXc hZc => ?_⟩
  · exact (tendsto_add_atTop_iff_nat 1).1 (theorem_3_8 hUv hU hunif s)
  · have : CompactSpace ↥M.X := isCompact_iff_compactSpace.1 hXc
    have := theorem_3_8_uniform hUv hU hunif
    rw [Metric.tendstoUniformly_iff] at this ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (this ε hε)
    refine eventually_atTop.2 ⟨N + 1, fun n hn x => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact hN k (by omega) x

/-- Miao, p. 211, the remark after Theorem 7.3.5, for actions in `A ⊆ ℝᵐ` (corrected).
`Tⁿ0 = V₀ⁿ`, the value of the `n`-horizon problem with terminal reward `0`, and for `n ≥ 1` the
maximizer `gₙ` for `vₙ = Tⁿ0` is the initial decision rule of an optimal Markov plan of the
`(n + 1)`-horizon problem: every optimal plan generated by measurable selections of the
Bellman maximizers starts with `gₙ`, and such plans exist. -/
theorem p211 {m : ℕ} {M : OCModel E (Fin m → ℝ) Z} [IsMarkovKernel M.Q] [PartialOrder E]
    [Nonempty ↥M.A] (h641 : M.Assumption641) (h642 : M.Assumption642) (h644 : M.Assumption644)
    (h645 : M.Assumption645) (h648 : M.Assumption648) (h649 : M.Assumption649)
    (h6411 : M.Assumption6411) (h6412 : M.Assumption6412) (h732 : Assumption732 M)
    (h733 : Assumption733 M) (hinj : M.PhiInjA) (h512 : 0 < M.β ∧ M.β < 1)
    (h : br_Standing (br_ctrlMDP M h645.1)) (n : ℕ) :
    (∀ s, V0 (br_ctrlMDP M h645.1) n s = (((br_T h)^[n] 0 s : ℝ) : EReal)) ∧
      ∃ σ : ℕ → ↥M.X × Z → ↥M.A, σ 0 = br_policy h645 ((br_T h)^[n + 1] 0) ∧
        ∀ s, IsOptimalPlan0 (br_ctrlMDP M h645.1) (n + 2) s (po_genPlan σ s) ∧
          V0 (br_ctrlMDP M h645.1) (n + 2) s = (((br_T h)^[n + 2] 0 s : ℝ) : EReal) := by
  have hst := br_ctrl_stationary M h645.1
  have hT0 : ∀ s, (br_ctrlMDP M h645.1).uT s = 0 := fun _ => rfl
  have hv₀ : ∀ z, ConcaveOn ℝ M.X (fun x => br_ext (0 : ↥M.X × Z →ᵇ ℝ) x z) ∧
      Monotone fun x : ↥M.X => (0 : ↥M.X × Z →ᵇ ℝ) (x, z) := fun z => by
    refine ⟨?_, fun _ _ _ => le_rfl⟩
    simp only [br_ext_zero]
    exact concaveOn_const 0 h641.1
  obtain ⟨V, hV, -, -⟩ := br_theorem_3_2 (br_T_contraction h h512)
  refine ⟨(theorem_7_2_2 h h512 hst hT0 hV).2.2.1 n, ?_⟩
  obtain ⟨g, hg⟩ := br_exists_policy h (n + 2)
  have huniq := br_G_unique h645 h642 h6411 h733 h512.1 h
    (br_compStrict_of_mono h641 h642 h645 h6412 hinj
      (fun z => (br_iterate_concave h641 h642 h644 h645 h648 h649 h6411 h6412 h732 h733
        h512.1.le h hv₀ n z).1)
      fun z => br_monotoneOn_ext (br_iterate_concave h641 h642 h644 h645 h648 h649 h6411 h6412
        h732 h733 h512.1.le h hv₀ n z).2.monotone)
  have hspec := (br_policy_spec h645 h huniq).2.1
  refine ⟨g, funext fun s => ?_, fun s => ?_⟩
  · have := (hg 0 (by omega)).2 s
    rw [show n + 2 - (0 + 1) = n + 1 by omega, hspec s] at this
    exact this
  · have := br_V0_eq h h512.1.le hst hT0 (n + 2) (fun t ht => (hg t ht).1)
      (fun t ht => (hg t ht).2) s
    exact ⟨this.2, this.1⟩

end Miao.InfiniteHorizonDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDP.Theorem94

/-!
# Exercise 9.2: returns bounded on one side

SLP §9.1, p. 253. Let `F` be bounded above or below (not necessarily by zero) and `0 ≤ β < 1`.

* **Exercise 9.2a** (`ex_9_2a`): `u(π, s₀) = lim uₙ(π, s₀)` exists in `[−∞, +∞]`: `uₙ` is a
  monotone sequence plus the convergent `C Σ_{t ≤ n} βᵗ`. (That `v*` is then defined on the
  nonempty `Π(s₀)` is Lemma 9.1.)
* **Exercise 9.2b**: Theorem 9.2 holds with Exercise 9.2a in place of Assumption 9.2
  (`ex_9_2b_theorem_9_2`); Lemma 9.3 holds in the form of the book's solution — `u` is the
  difference `u⁺ − u⁻` of the values of the positive and negative parts of the returns, one of
  which is finite, and each satisfies the recursion (9) by monotone convergence
  (`ex_9_2b_lemma_9_3`); and Theorem 9.4 holds: for bounded `F` Assumption 9.3 holds with
  `L_t = sup |F|` (`ex_9_2b_theorem_9_4`), and for one-sided bounds the optimal plan has
  `Σ βᵗ ∫ |F| dμᵗ < ∞`, which is enough (`ex_9_2b_theorem_9_4'`).
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (M : Model X Y Z)

/-- A monotone real sequence plus a convergent one converges in `[−∞, +∞]`. -/
theorem exists_tendsto_ereal_of_monotone {a c : ℕ → ℝ} (ha : Monotone a) {c₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) :
    ∃ L : EReal, Tendsto (fun n => ((a n + c n : ℝ) : EReal)) atTop (𝓝 L) := by
  by_cases hb : BddAbove (range a)
  · exact ⟨((⨆ n, a n) + c₀ : ℝ),
      (continuous_coe_real_ereal.tendsto _).comp ((tendsto_atTop_ciSup ha hb).add hc)⟩
  · refine ⟨⊤, EReal.tendsto_nhds_top_iff_real.2 fun x => ?_⟩
    have h2 := (tendsto_atTop_atTop_of_monotone' ha hb).atTop_add hc
    filter_upwards [h2.eventually_gt_atTop x] with n hn
    exact EReal.coe_lt_coe_iff.2 hn

/-- An antitone real sequence plus a convergent one converges in `[−∞, +∞]`. -/
theorem exists_tendsto_ereal_of_antitone {a c : ℕ → ℝ} (ha : Antitone a) {c₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) :
    ∃ L : EReal, Tendsto (fun n => ((a n + c n : ℝ) : EReal)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_ereal_of_monotone (a := fun n => -a n) (c := fun n => -c n)
    (fun m n hmn => neg_le_neg (ha hmn)) hc.neg
  refine ⟨-L, ((continuous_neg.tendsto L).comp hL).congr fun n => ?_⟩
  simp only [Function.comp_apply, ← EReal.coe_neg]
  congr 1
  ring

variable [IsMarkovKernel M.Q]

/-- **Exercise 9.2a.** If `F` is bounded above or below and `0 ≤ β < 1`, `uₙ(π, s₀)` converges in
`[−∞, +∞]` along every plan with integrable returns. -/
theorem ex_9_2a (hβ : 0 ≤ M.β) (hβ1 : M.β < 1) {C : ℝ} (hC : (∀ p, M.F p ≤ C) ∨ ∀ p, C ≤ M.F p)
    (s₀ : X × Z) (π : Plan Y Z) (hI : ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2)) :
    ∃ L, Tendsto (fun n => (uN M s₀ π n : EReal)) atTop (𝓝 L) := by
  set c : ℕ → ℝ := fun n => C * ∑ t ∈ Finset.range (n + 1), M.β ^ t with hcdef
  have hc : Tendsto c atTop (𝓝 (C * (1 - M.β)⁻¹)) :=
    ((hasSum_geometric_of_lt_one hβ hβ1).tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)).const_mul C
  have hstep : ∀ n, (uN M s₀ π (n + 1) - c (n + 1)) - (uN M s₀ π n - c n) =
      M.β ^ (n + 1) * (∫ h, ret M s₀ π (n + 1) h ∂hist M.Q (n + 1) s₀.2 - C) := fun n => by
    simp only [uN, hcdef, Finset.sum_range_succ (n := n + 1)]
    ring
  have hconst : ∀ t, ∫ _h, C ∂hist M.Q t s₀.2 = C := fun t => by
    have := ex_8_8a M.Q t
    simp
  have hpow : ∀ n, 0 ≤ M.β ^ (n + 1) := fun n => pow_nonneg hβ _
  have hfin : ∀ L, Tendsto (fun n => ((uN M s₀ π n - c n + c n : ℝ) : EReal)) atTop (𝓝 L) →
      Tendsto (fun n => (uN M s₀ π n : EReal)) atTop (𝓝 L) := fun L hL =>
    hL.congr fun n => by rw [sub_add_cancel]
  rcases hC with hC | hC
  · obtain ⟨L, hL⟩ := exists_tendsto_ereal_of_antitone
      (a := fun n => uN M s₀ π n - c n) (antitone_nat_of_succ_le fun n => by
        have := ex_8_8a M.Q (n + 1)
        have hle : ∫ h, ret M s₀ π (n + 1) h ∂hist M.Q (n + 1) s₀.2 ≤ C :=
          (integral_mono (hI _) (integrable_const C) fun h => hC _).trans (hconst _).le
        nlinarith [hstep n, hpow n]) hc
    exact ⟨L, hfin L hL⟩
  · obtain ⟨L, hL⟩ := exists_tendsto_ereal_of_monotone
      (a := fun n => uN M s₀ π n - c n) (monotone_nat_of_le_succ fun n => by
        have := ex_8_8a M.Q (n + 1)
        have hle : C ≤ ∫ h, ret M s₀ π (n + 1) h ∂hist M.Q (n + 1) s₀.2 :=
          (hconst _).symm.le.trans (integral_mono (integrable_const C) (hI _) fun h => hC _)
        nlinarith [hstep n, hpow n]) hc
    exact ⟨L, hfin L hL⟩

/-- **Exercise 9.2b: Theorem 9.2** for `F` bounded above or below and `β < 1`, with Exercise 9.2a
in place of the convergence part of Assumption 9.2. -/
theorem ex_9_2b_theorem_9_2 (hφ : Measurable M.φ) (hβ : 0 ≤ M.β) (hβ1 : M.β < 1) {C : ℝ}
    (hC : (∀ p, M.F p ≤ C) ∨ ∀ p, C ≤ M.F p) {v : X × Z → ℝ} (hFE : SolvesFE M v)
    (s₀ : X × Z)
    (hint : ∀ π, IsFeasible M s₀ π → ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2) ∧
      Integrable (fun h => v (state M s₀ π t h)) (hist M.Q t s₀.2))
    (h7 : ∀ π, IsFeasible M s₀ π →
      Tendsto (fun t => M.β ^ t * ∫ h, v (state M s₀ π t h) ∂hist M.Q t s₀.2) atTop (𝓝 0))
    {g : ℕ → X × Z → Y} (hg : ∀ t, Measurable (g t)) (hgG : ∀ t s, g t s ∈ policy M v s) :
    (∀ π, IsFeasible M s₀ π → planValue M s₀ π ≤ v s₀) ∧
      planValue M s₀ (genPlan M s₀ g) = v s₀ ∧ vStar M s₀ = v s₀ :=
  ex_9_4 M hφ hβ hFE s₀ hint
    (fun π hπ => ex_9_2a M hβ hβ1 hC s₀ π fun t => (hint π hπ t).1) h7 hg hgG

/-- The model with returns `−F`. -/
abbrev Model.negF (M : Model X Y Z) : Model X Y Z := { M with F := fun p => -M.F p }

omit [IsMarkovKernel M.Q] in
theorem xState_negF (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) :
    xState M.negF s₀ π t = xState M s₀ π t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext h
    simp only [xState, ih]

omit [IsMarkovKernel M.Q] in
theorem ret_negF (s₀ : X × Z) (π : Plan Y Z) (t : ℕ) :
    ret M.negF s₀ π t = fun h => -ret M s₀ π t h := by
  funext h
  simp only [ret, state, xState_negF]

/-- With `F ≤ C` and `0 ≤ β < 1`, the value of the positive part of the returns is finite. -/
theorem planValuePos_ne_top (hβ : 0 ≤ M.β) (hβ1 : M.β < 1) {C : ℝ} (hC : ∀ p, M.F p ≤ C)
    (s₀ : X × Z) (π : Plan Y Z) : planValuePos M s₀ π ≠ ⊤ := by
  have hle : planValuePos M s₀ π ≤ ∑' t, ENNReal.ofReal M.β ^ t * ENNReal.ofReal C := by
    refine ENNReal.tsum_le_tsum fun t => ?_
    have := ex_8_8a M.Q t
    rw [← ENNReal.ofReal_pow hβ]
    gcongr
    calc ∫⁻ h, ENNReal.ofReal (ret M s₀ π t h) ∂hist M.Q t s₀.2
        ≤ ∫⁻ _h, ENNReal.ofReal C ∂hist M.Q t s₀.2 :=
          lintegral_mono fun h => ENNReal.ofReal_le_ofReal (hC _)
      _ = ENNReal.ofReal C := by simp
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric] at hle
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top) hle
  exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hβ1)).ne'

/-- **Exercise 9.2b: Lemma 9.3** for `F` bounded above or below and `0 ≤ β < 1` (the book's
solution). `u(π, s₀) = u⁺ − u⁻`, where `u^±` are the values in `[0, +∞]` of the positive and
negative parts of the returns; one of them is finite; and each satisfies the recursion (9). -/
theorem ex_9_2b_lemma_9_3 (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 ≤ M.β)
    (hβ1 : M.β < 1) {C : ℝ} (hC : (∀ p, M.F p ≤ C) ∨ ∀ p, C ≤ M.F p) (s₀ : X × Z)
    {π : Plan Y Z} (hπ : ∀ t, Measurable (π t))
    (hI : ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2)) :
    planValue M s₀ π = (planValuePos M s₀ π : EReal) - planValuePos M.negF s₀ π ∧
      (planValuePos M s₀ π ≠ ⊤ ∨ planValuePos M.negF s₀ π ≠ ⊤) ∧
      planValuePos M s₀ π = ENNReal.ofReal (ret M s₀ π 0 Fin.elim0) +
        ENNReal.ofReal M.β * ∫⁻ z₁, planValuePos M (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 ∧
      planValuePos M.negF s₀ π = ENNReal.ofReal (-ret M s₀ π 0 Fin.elim0) +
        ENNReal.ofReal M.β *
          ∫⁻ z₁, planValuePos M.negF (start₁ M s₀ π z₁) (cont π z₁) ∂M.Q s₀.2 := by
  have hfin : planValuePos M s₀ π ≠ ⊤ ∨ planValuePos M.negF s₀ π ≠ ⊤ := by
    rcases hC with hC | hC
    · exact Or.inl (planValuePos_ne_top M hβ hβ1 hC s₀ π)
    · exact Or.inr (planValuePos_ne_top M.negF hβ hβ1 (C := -C)
        (fun p => neg_le_neg (hC p)) s₀ π)
  refine ⟨?_, hfin, lemma_9_3_nonneg M hφ hF hβ s₀ hπ,
    lemma_9_3_nonneg M.negF hφ hF.neg hβ s₀ hπ⟩
  set A : ℕ → ℝ≥0∞ := fun n => ∑ t ∈ Finset.range (n + 1),
    ENNReal.ofReal (M.β ^ t) * ∫⁻ h, ENNReal.ofReal (ret M s₀ π t h) ∂hist M.Q t s₀.2 with hAdef
  set B : ℕ → ℝ≥0∞ := fun n => ∑ t ∈ Finset.range (n + 1),
    ENNReal.ofReal (M.β ^ t) * ∫⁻ h, ENNReal.ofReal (ret M.negF s₀ π t h) ∂hist M.Q t s₀.2
    with hBdef
  have hA : Tendsto (fun n => (A n : EReal)) atTop (𝓝 (planValuePos M s₀ π : EReal)) :=
    (continuous_coe_ennreal_ereal.tendsto _).comp
      ((ENNReal.tendsto_nat_tsum _).comp (tendsto_add_atTop_nat 1))
  have hB : Tendsto (fun n => (B n : EReal)) atTop (𝓝 (planValuePos M.negF s₀ π : EReal)) :=
    (continuous_coe_ennreal_ereal.tendsto _).comp
      ((ENNReal.tendsto_nat_tsum _).comp (tendsto_add_atTop_nat 1))
  have hAt : ∀ t, ENNReal.ofReal (M.β ^ t) *
      ∫⁻ h, ENNReal.ofReal (ret M s₀ π t h) ∂hist M.Q t s₀.2 ≠ ⊤ := fun t =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI t).lintegral_lt_top.ne
  have hBt : ∀ t, ENNReal.ofReal (M.β ^ t) *
      ∫⁻ h, ENNReal.ofReal (ret M.negF s₀ π t h) ∂hist M.Q t s₀.2 ≠ ⊤ := fun t => by
    rw [ret_negF]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI t).neg.lintegral_lt_top.ne
  have heq : ∀ n, (uN M s₀ π n : EReal) = (A n : EReal) + -(B n : EReal) := fun n => by
    rw [← EReal.coe_ennreal_toReal (ENNReal.sum_ne_top.2 fun t _ => hAt t),
      ← EReal.coe_ennreal_toReal (ENNReal.sum_ne_top.2 fun t _ => hBt t), ← EReal.coe_neg,
      ← EReal.coe_add, EReal.coe_eq_coe_iff, ENNReal.toReal_sum fun t _ => hAt t,
      ENNReal.toReal_sum fun t _ => hBt t, uN, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ret_negF, integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hI t), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hβ t)]
    ring
  refine planValue_eq M ?_
  simp_rw [heq, sub_eq_add_neg]
  refine ((EReal.continuousAt_add ?_ ?_).tendsto).comp
    (hA.prodMk_nhds ((continuous_neg.tendsto _).comp hB))
  · rcases hfin with h | h
    · exact Or.inl fun h' => h (EReal.coe_ennreal_eq_top_iff.1 h')
    · exact Or.inr fun h' => h (EReal.coe_ennreal_eq_top_iff.1 (EReal.neg_eq_bot_iff.1 h'))
  · exact Or.inl (EReal.coe_ennreal_ne_bot _)

/-- **Exercise 9.2b: Theorem 9.4** for bounded `F` and `0 < β < 1`: Assumption 9.3 holds with
`L_t = sup |F|`. -/
theorem ex_9_2b_theorem_9_4 (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (hβ1 : M.β < 1) {C : ℝ} (hC : ∀ p, |M.F p| ≤ C)
    (hΓ : MeasurableSet {p : (X × Z) × Y | p.2 ∈ M.Γ p.1}) {v : X × Z → ℝ} (hv : Measurable v)
    (hvstar : ∀ s, vStar M s = v s) (hFE : SolvesFE M v)
    (hIv : ∀ s, ∀ y ∈ M.Γ s, Integrable (fun z' => v (M.φ (s.1, y, z'), z')) (M.Q s.2))
    {s₀ : X × Z} {π : Plan Y Z} (hπ : IsFeasible M s₀ π)
    (hπopt : planValue M s₀ π = vStar M s₀) :
    π 0 Fin.elim0 ∈ policy M v s₀ ∧
      ∀ t, ∀ᵐ h ∂hist M.Q t s₀.2, π t h ∈ policy M v (state M s₀ π t h) :=
  theorem_9_4 M hφ hF hβ hΓ hv hvstar hFE hIv hπ hπopt (L := fun _ => C) (fun _ _ => hC _)
    ((summable_geometric_of_lt_one hβ.le hβ1).mul_right C)

theorem ofReal_abs_eq (x : ℝ) :
    ENNReal.ofReal |x| = ENNReal.ofReal x + ENNReal.ofReal (-x) := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.2 h), add_zero]
  · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]

omit [IsMarkovKernel M.Q] in
/-- `Σ βᵗ ∫ |F| dμᵗ = u⁺ + u⁻`. -/
theorem planAbs_eq_add (hφ : Measurable M.φ) (hF : Measurable M.F) (s₀ : X × Z) {π : Plan Y Z}
    (hπ : ∀ t, Measurable (π t)) :
    planAbs M s₀ π = planValuePos M s₀ π + planValuePos M.negF s₀ π := by
  rw [planAbs_eq, planValuePos, planValuePos, ← ENNReal.tsum_add]
  refine tsum_congr fun t => ?_
  rw [← mul_add, ret_negF, ← lintegral_add_left (measurable_ret M hφ hF s₀ hπ t).ennreal_ofReal]
  congr 1
  exact lintegral_congr fun h => ofReal_abs_eq _

/-- **Exercise 9.2b: Theorem 9.4** for `F` bounded above *or* below and `0 < β < 1` (with the
returns of the optimal plan integrable, Assumption 9.2). Since `v*(s₀)` is finite and one of
`u⁺`, `u⁻` is finite (`ex_9_2b_lemma_9_3`), both are, so `Σ βᵗ ∫ |F| dμᵗ = u⁺ + u⁻ < ∞` and
Theorem 9.4 applies in its general form (`theorem_9_4_abs`). -/
theorem ex_9_2b_theorem_9_4' (hφ : Measurable M.φ) (hF : Measurable M.F) (hβ : 0 < M.β)
    (hβ1 : M.β < 1) {C : ℝ} (hC : (∀ p, M.F p ≤ C) ∨ ∀ p, C ≤ M.F p)
    (hΓ : MeasurableSet {p : (X × Z) × Y | p.2 ∈ M.Γ p.1}) {v : X × Z → ℝ} (hv : Measurable v)
    (hvstar : ∀ s, vStar M s = v s) (hFE : SolvesFE M v)
    (hIv : ∀ s, ∀ y ∈ M.Γ s, Integrable (fun z' => v (M.φ (s.1, y, z'), z')) (M.Q s.2))
    {s₀ : X × Z} {π : Plan Y Z} (hπ : IsFeasible M s₀ π)
    (hπopt : planValue M s₀ π = vStar M s₀)
    (hI : ∀ t, Integrable (ret M s₀ π t) (hist M.Q t s₀.2)) :
    π 0 Fin.elim0 ∈ policy M v s₀ ∧
      ∀ t, ∀ᵐ h ∂hist M.Q t s₀.2, π t h ∈ policy M v (state M s₀ π t h) := by
  obtain ⟨hdec, hfin1, -, -⟩ := ex_9_2b_lemma_9_3 M hφ hF hβ.le hβ1 hC s₀ hπ.1 hI
  have hval : (planValuePos M s₀ π : EReal) - planValuePos M.negF s₀ π = (v s₀ : EReal) := by
    rw [← hdec, hπopt, hvstar]
  have hP : planValuePos M s₀ π ≠ ⊤ ∧ planValuePos M.negF s₀ π ≠ ⊤ := by
    rcases hfin1 with h | h
    · refine ⟨h, fun h' => ?_⟩
      rw [h', ← EReal.coe_ennreal_toReal h, EReal.coe_ennreal_top] at hval
      simp at hval
    · refine ⟨fun h' => ?_, h⟩
      rw [h', ← EReal.coe_ennreal_toReal h, EReal.coe_ennreal_top] at hval
      simp at hval
  refine theorem_9_4_abs M hφ hF hβ hΓ hv hvstar hFE hIv hπ hπopt ?_
  rw [planAbs_eq_add M hφ hF s₀ hπ.1]
  exact ENNReal.add_ne_top.2 hP

end StokeyLucasPrescott.StochasticDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.WelfareSecond

/-!
# Figure 15.3 and the p. 458 overstatement

SLP §15.2–15.3, pp. 457–458.

**Figure 15.3** (pp. 457–458) is drawn, not specified. `fig153X`, `fig153U`, `fig153Y` give a
concrete two-consumer, two-good exchange economy in `ℝ²` with the same features (the endowment
`ω = (1, 0)` is modelled as a single firm with `Y = {ω}`):
* consumer `0` has the half-plane `X₀ = {v : v₁ ≥ 0}` and `u₀(v) = v₂`;
* consumer `1` has `X₁ = ℝ²` and the smooth, strictly concave in good 2, `u₁(v) = v₁ − v₂²`;
* the allocation `E`: `x₀ = (0, 0)`, `x₁ = (1, 0)`.

Results:
* `fig153_assumptions`: Assumptions 15.1–15.5 and local nonsatiation hold.
* `fig153_paretoOptimal`: `E` is Pareto optimal.
* `fig153_supported`: `φ(v) = v₁` is a nonzero supporting price (Theorem 15.4's conclusion) at
  which consumer `0` has no cheaper point, so the Remark does not apply; and consumer `0`
  strictly prefers `E′ = (0, 1)` on her budget line.
* `fig153_not_competitiveEq`: no price system whatever makes `E` a competitive equilibrium.

**Correction** (p. 458). The book says that under Assumptions 15.1–15.5 "the set of competitive
equilibrium allocations and the set of Pareto-optimal allocations coincide exactly". Both
inclusions fail:
* `paretoOptimal_not_ce_counterexample`: the Figure 15.3 economy above satisfies 15.1–15.5 (and
  local nonsatiation) and has a Pareto optimum that is not a competitive equilibrium allocation
  (PO ⇒ CE needs the cheaper-point condition of the Remark);
* `ce_not_paretoOptimal_counterexample`: two consumers with `u(v) = min(v, 0)` on `ℝ` and endowment
  `0`; Assumptions 15.1–15.5 hold, `x = (1, −1)` with `φ = id` is a competitive equilibrium, and it
  is not Pareto optimal (CE ⇒ PO needs local nonsatiation, which fails at the satiated consumer).
The correct statement is `welfare_theorems_corrected` (`WelfareSecond`).
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Set

/-- If there is one firm whose production set is a single point `ω` (an endowment), the aggregate
technology is `{ω}`. -/
theorem aggTech_singleton {S : Type*} [NormedAddCommGroup S] (e : S) :
    aggTech (fun _ : Unit => ({e} : Set S)) = {e} := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy ()
  · rintro rfl
    exact ⟨fun _ => w, fun _ => rfl, by simp⟩

/-! ### The Figure 15.3 economy -/

/-- Consumption sets of the Figure 15.3 economy: `X₀ = {v : v₁ ≥ 0}`, `X₁ = ℝ²`. -/
def fig153X : Fin 2 → Set (ℝ × ℝ) := ![{v | 0 ≤ v.1}, univ]

/-- Utilities of the Figure 15.3 economy: `u₀(v) = v₂`, `u₁(v) = v₁ − v₂²`. -/
def fig153U : Fin 2 → ℝ × ℝ → ℝ := ![fun v => v.2, fun v => v.1 - v.2 ^ 2]

/-- The single "firm" of the Figure 15.3 economy is the endowment `ω = (1, 0)`. -/
def fig153Y : Unit → Set (ℝ × ℝ) := fun _ => {(1, 0)}

/-- The allocation `E` of the Figure 15.3 economy: `x₀ = (0, 0)`, `x₁ = (1, 0)`. -/
def fig153x : Fin 2 → ℝ × ℝ := ![(0, 0), (1, 0)]

/-- The endowment `y = ω = (1, 0)` of the Figure 15.3 economy. -/
def fig153y : Unit → ℝ × ℝ := fun _ => (1, 0)

/-- The supporting price of the Figure 15.3 economy: `φ(v) = v₁` (good 2 is free). -/
noncomputable def fig153φ : StrongDual ℝ (ℝ × ℝ) := ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The Figure 15.3 economy satisfies Assumptions 15.1–15.5 and local nonsatiation. -/
theorem fig153_assumptions :
    Assumption15_1 fig153X ∧ Assumption15_2 fig153X fig153U ∧ Assumption15_3 fig153X fig153U ∧
    Assumption15_4 fig153Y ∧ Assumption15_5 (ℝ × ℝ) fig153Y ∧
    LocalNonsatiation fig153X fig153U := by
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨?_, ?_, ?_, ?_, Or.inr inferInstance, ?_⟩
  · rw [Assumption15_1, Fin.forall_fin_two]
    refine ⟨?_, convex_univ⟩
    intro v hv w hw a b ha hb _
    simp only [fig153X, Matrix.cons_val_zero, mem_ofPred_eq, Prod.fst_add, Prod.smul_fst,
      smul_eq_mul] at hv hw ⊢
    positivity
  · rw [Assumption15_2, Fin.forall_fin_two]
    constructor
    · intro z _ z' _ hlt θ hθ0 hθ1
      simp only [fig153U, Matrix.cons_val_zero, Prod.snd_add, Prod.smul_snd,
        smul_eq_mul] at hlt ⊢
      nlinarith
    · intro z _ z' _ hlt θ hθ0 hθ1
      simp only [fig153U, Matrix.cons_val_one, Matrix.cons_val_zero, Prod.fst_add,
        Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hlt ⊢
      nlinarith [mul_nonneg (mul_nonneg hθ0.le (sub_nonneg.2 hθ1.le))
        (sq_nonneg (z.2 - z'.2))]
  · rw [Assumption15_3, Fin.forall_fin_two]
    exact ⟨by simp only [fig153U, Matrix.cons_val_zero]; exact continuous_snd.continuousOn,
      by simp only [fig153U, Matrix.cons_val_one, Matrix.cons_val_zero]
         exact (continuous_fst.sub (continuous_snd.pow 2)).continuousOn⟩
  · change Convex ℝ (aggTech (fun _ : Unit => ({((1 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ))))
    rw [aggTech_singleton]
    exact convex_singleton _
  · rw [LocalNonsatiation, Fin.forall_fin_two]
    constructor
    · intro z hz
      refine ⟨fun n => z + (0, 1 / ((n : ℝ) + 1)), fun n => ?_, ?_, fun n => ?_⟩
      · simpa [fig153X] using hz
      · have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z)).add
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).prodMk_nhds hlim)
        simpa [Prod.mk_zero_zero] using this
      · simp only [fig153U, Matrix.cons_val_zero, Prod.snd_add]
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    · intro z _
      refine ⟨fun n => z + (1 / ((n : ℝ) + 1), 0), fun n => by simp [fig153X], ?_,
        fun n => ?_⟩
      · have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z)).add
          (hlim.prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
        simpa [Prod.mk_zero_zero] using this
      · simp only [fig153U, Matrix.cons_val_one, Matrix.cons_val_zero, Prod.fst_add,
          Prod.snd_add, add_zero]
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith

/-- The allocation `E` of the Figure 15.3 economy is Pareto optimal. -/
theorem fig153_paretoOptimal : ParetoOptimal fig153X fig153U fig153Y fig153x fig153y := by
  refine ⟨⟨?_, fun _ => rfl, ?_⟩, ?_⟩
  · rw [Fin.forall_fin_two]
    exact ⟨by simp [fig153X, fig153x], by simp [fig153X]⟩
  · simp [fig153x, fig153y, Fin.sum_univ_two]
  · rintro ⟨x', y', ⟨hx', hy', hsum⟩, hge, i, hi⟩
    have hy0 : y' () = (1, 0) := hy' ()
    have h0 : 0 ≤ (x' 0).1 := hx' 0
    simp only [Fin.sum_univ_two, Finset.univ_unique, PUnit.default_eq_unit,
      Finset.sum_singleton, hy0] at hsum
    have e1 := congrArg Prod.fst hsum
    have e2 := congrArg Prod.snd hsum
    simp only [Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add, Prod.fst_zero,
      Prod.snd_zero] at e1 e2
    have g0 := hge 0
    have g1 := hge 1
    simp only [fig153U, fig153x, Matrix.cons_val_zero, Matrix.cons_val_one] at g0 g1
    have hb : (x' 1).2 = -(x' 0).2 := by linarith
    have ha : (x' 1).1 = 1 - (x' 0).1 := by linarith
    rw [hb, ha] at g1
    have hzero : (x' 0).2 = 0 := by nlinarith [sq_nonneg (x' 0).2]
    fin_cases i
    · simp only [fig153U, fig153x, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hi
      linarith
    · simp only [fig153U, fig153x, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero] at hi
      rw [hb, ha] at hi
      nlinarith [sq_nonneg (x' 0).2]

/-- At `E`, `φ(v) = v₁` is a nonzero supporting price ((3) and (4) hold), consumer `0` has no
cheaper point at `φ`, and consumer `0` strictly prefers `E′ = (0, 1)`, which costs the same. -/
theorem fig153_supported :
    fig153φ ≠ 0 ∧ SupportsAllocation fig153X fig153U fig153Y fig153x fig153y fig153φ ∧
    (∀ z ∈ fig153X 0, fig153φ (fig153x 0) ≤ fig153φ z) ∧
    ((0, 1) : ℝ × ℝ) ∈ fig153X 0 ∧ fig153φ (0, 1) ≤ fig153φ (fig153x 0) ∧
    fig153U 0 (fig153x 0) < fig153U 0 (0, 1) := by
  have hφ : ∀ v : ℝ × ℝ, fig153φ v = v.1 := fun v => rfl
  refine ⟨fun h => by simpa [hφ] using congrArg (fun f => f ((1, 0) : ℝ × ℝ)) h,
    ⟨?_, ?_⟩, ?_, by simp [fig153X], by simp [hφ, fig153x], by simp [fig153U, fig153x]⟩
  · rw [Fin.forall_fin_two]
    constructor
    · intro z hz _
      simpa [hφ, fig153x, fig153X] using hz
    · intro z _ hle
      simp only [fig153U, fig153x, Matrix.cons_val_one, Matrix.cons_val_zero] at hle
      simp only [hφ, fig153x, Matrix.cons_val_one, Matrix.cons_val_zero]
      nlinarith [sq_nonneg z.2]
  · intro j w hw
    rw [show w = (1, 0) from hw]
    exact le_rfl
  · intro z hz
    simpa [hφ, fig153x, fig153X] using hz

/-- **No price system supports `E` as a competitive equilibrium** (Figure 15.3). If `φ` were an
equilibrium price, consumer `0`'s optimality would force `φ(0, 1) > 0`, and then consumer `1` could
afford a strictly better bundle. -/
theorem fig153_not_competitiveEq :
    ¬ ∃ φ, CompetitiveEq fig153X fig153U fig153Y fig153x fig153y φ := by
  rintro ⟨φ, -, hE2, -⟩
  set p1 := φ (1, 0) with hp1
  set p2 := φ (0, 1) with hp2
  have hφ : ∀ a b : ℝ, φ (a, b) = a * p1 + b * p2 := by
    intro a b
    have : ((a, b) : ℝ × ℝ) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  -- consumer `0`: the bundle `(0, 1)` must be unaffordable, so `p2 > 0`
  have hp2pos : 0 < p2 := by
    by_contra hle
    push Not at hle
    have := hE2 0 (0, 1) (by simp [fig153X]) (by simp [fig153x, hφ, hle])
    norm_num [fig153U, fig153x] at this
  -- consumer `1`
  have h1 := fun z => hE2 1 z (by simp [fig153X])
  simp only [fig153U, fig153x, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
  rcases le_or_gt p1 0 with hp1n | hp1p
  · have := h1 (2, 0) (by rw [hφ, hφ]; nlinarith)
    norm_num at this
  · set a := p2 / (2 * p1) with ha
    have hapos : 0 < a := div_pos hp2pos (by linarith)
    have hrel : 2 * p1 * a = p2 := by
      rw [ha]
      field_simp
    have := h1 (1 + 2 * a ^ 2, -a) (by rw [hφ, hφ]; nlinarith)
    nlinarith

/-- **Counterexample** to the p. 458 claim "PO ⇒ CE under Assumptions 15.1–15.5": the Figure 15.3
economy satisfies Assumptions 15.1–15.5 and local nonsatiation, but its Pareto optimum `E` is not
a competitive equilibrium allocation for any price system. -/
theorem paretoOptimal_not_ce_counterexample :
    Assumption15_1 fig153X ∧ Assumption15_2 fig153X fig153U ∧ Assumption15_3 fig153X fig153U ∧
    Assumption15_4 fig153Y ∧ Assumption15_5 (ℝ × ℝ) fig153Y ∧
    LocalNonsatiation fig153X fig153U ∧
    ¬ ∀ x y, ParetoOptimal fig153X fig153U fig153Y x y →
      ∃ φ, CompetitiveEq fig153X fig153U fig153Y x y φ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := fig153_assumptions
  exact ⟨h1, h2, h3, h4, h5, h6, fun h =>
    fig153_not_competitiveEq (h fig153x fig153y fig153_paretoOptimal)⟩

/-! ### A competitive equilibrium that is not Pareto optimal -/

/-- Utilities of the satiation example: both consumers have `u(v) = min(v, 0)` on `ℝ`. -/
noncomputable def satU : Fin 2 → ℝ → ℝ := fun _ v => min v 0

/-- **Counterexample** to the p. 458 claim "CE ⇒ PO under Assumptions 15.1–15.5". Two consumers
with `X = ℝ`, `u(v) = min(v, 0)`, endowment `0` (one firm, `Y = {0}`). Assumptions 15.1–15.5 hold;
the allocation `x = (1, −1)` with the price `φ = id` is a competitive equilibrium, but it is not
Pareto optimal (`(0, 0)` makes consumer `1` better off and consumer `0` no worse off); local
nonsatiation fails at consumer `0`'s satiated bundle `1`. -/
theorem ce_not_paretoOptimal_counterexample :
    Assumption15_1 (fun _ : Fin 2 => (univ : Set ℝ)) ∧
    Assumption15_2 (fun _ : Fin 2 => (univ : Set ℝ)) satU ∧
    Assumption15_3 (fun _ : Fin 2 => (univ : Set ℝ)) satU ∧
    Assumption15_4 (fun _ : Unit => ({0} : Set ℝ)) ∧
    Assumption15_5 ℝ (fun _ : Unit => ({0} : Set ℝ)) ∧
    CompetitiveEq (fun _ : Fin 2 => (univ : Set ℝ)) satU (fun _ : Unit => ({0} : Set ℝ))
      ![1, -1] (fun _ => 0) (ContinuousLinearMap.id ℝ ℝ) ∧
    ¬ ParetoOptimal (fun _ : Fin 2 => (univ : Set ℝ)) satU (fun _ : Unit => ({0} : Set ℝ))
      ![1, -1] (fun _ => 0) ∧
    ¬ LocalNonsatiation (fun _ : Fin 2 => (univ : Set ℝ)) satU := by
  refine ⟨fun _ => convex_univ, ?_, fun _ => (continuous_id.min continuous_const).continuousOn,
    by rw [Assumption15_4, aggTech_singleton]; exact convex_singleton _, Or.inr inferInstance,
    ⟨⟨fun _ => mem_univ _, fun _ => rfl, by simp [Fin.sum_univ_two]⟩,
      fun i z _ hz => min_le_min_right 0 hz, fun j w hw => by rw [show w = 0 from hw]⟩,
    ?_, ?_⟩
  · intro i z _ z' _ hlt θ hθ0 hθ1
    simp only [satU, smul_eq_mul] at hlt ⊢
    have hz' : z' < 0 := by
      by_contra hge
      push Not at hge
      rw [min_eq_right hge] at hlt
      linarith [min_le_right z 0]
    have hzz : z' < z := by
      by_contra hge
      push Not at hge
      linarith [min_le_min_right 0 hge]
    rw [min_eq_left hz'.le]
    exact lt_min (by nlinarith) hz'
  · rintro ⟨-, hno⟩
    refine hno ⟨![0, 0], fun _ => 0, ⟨fun _ => mem_univ _, fun _ => rfl, by simp⟩, ?_, 1, ?_⟩
    · rw [Fin.forall_fin_two]
      norm_num [satU]
    · norm_num [satU]
  · intro hLNS
    obtain ⟨zs, -, -, hzs⟩ := hLNS 0 1 (mem_univ _)
    have := hzs 0
    simp only [satU] at this
    linarith [min_le_right (zs 0) 0, show min (1 : ℝ) 0 = 0 from min_eq_right zero_le_one]

end StokeyLucasPrescott.ParetoOptimaEquilibria

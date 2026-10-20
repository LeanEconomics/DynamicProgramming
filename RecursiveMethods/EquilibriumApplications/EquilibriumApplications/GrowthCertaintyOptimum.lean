/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.GrowthCertainty

/-!
# The one-sector model under certainty: the optimum and its equilibrium prices

SLP §16.1, pp. 476–478, Exercises 16.1(a)–(c).

* `gc_symmetric_paretoOptimal_iff` (NOTE on the framing of §16.1): with `I` identical consumers
  `(X, u)` and `I` identical firms `Y` (convex `X`, `Y`, concave `u`), a symmetric allocation is
  Pareto optimal iff `x = y` and `x` maximises `u` on `X ∩ Y` — the averaging argument the book
  leaves implicit.
* `gc_exists_optimum` (the hint "Exercise 5.1"): `u` attains its maximum on `X ∩ Y`. Proof by
  compactness of feasible (output, capital) pairs in the product topology (Tychonoff) and
  continuity of `u` there.
* `gc_optimum_unique`: the maximiser is unique (strict concavity of `U`).
* **Exercise 16.1(a)** (`ex_16_1a`, p. 477): there is exactly one symmetric Pareto-optimal
  allocation; by Theorem 15.3 (with local nonsatiation) every symmetric competitive equilibrium
  allocation is that allocation, so there is at most one.
* **Exercise 16.1(b)** (`ex_16_1b`, p. 477): by Theorem 15.4 and the cheaper point `0`, the optimum
  is a competitive equilibrium allocation for some `φ ≠ 0`.
* **Exercise 16.1(c)** (`ex_16_1c`, p. 477): by Theorem 15.6 the regular part `ψ` of any such `φ` is
  an equilibrium price system with `ψ(x) = Σ_t p_t x_t`, `p ∈ ℓ₁` (`Σ_t |p_t| ≤ ‖φ‖`) and every
  `p_t > 0`.

**Corrections.**
* The book never fixes the numbers of consumers and firms; "symmetric Pareto optima = planner
  solutions" needs convexity of `X`, `Y` and concavity of `u` (`gc_symmetric_paretoOptimal_iff`).
* The solutions manual's 16.1(c) stops at "the price system has an inner product representation";
  the precise conclusion (`p ∈ ℓ₁`, `p_t > 0`, and `(x⁰, x⁰, ψ)` is a competitive equilibrium
  because `ψ(x⁰) = φ(x⁰) > 0 = ψ(0)`) is `ex_16_1c`.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped ENNReal

/-! ### Symmetric Pareto optima -/

/-- **Symmetric Pareto optima are planner solutions** (NOTE on the framing of §16.1). With `I`
identical consumers `(X, u)` and `I` identical firms with production set `Y`, `X` and `Y` convex and
`u` concave on `X`, the symmetric allocation `xᵢ = x`, `yⱼ = y` is Pareto optimal iff `x = y`,
`x ∈ X ∩ Y` and `x` maximises `u` on `X ∩ Y`. "⇐" is the averaging argument:
`x̄ = (1/I) Σᵢ xᵢ′ ∈ X ∩ Y` and `u(x̄) ≥ (1/I) Σᵢ u(xᵢ′)` by Jensen's inequality. -/
theorem gc_symmetric_paretoOptimal_iff {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {ι : Type*} [Fintype ι] [Nonempty ι] {X Y : Set S} {u : S → ℝ} (hX : Convex ℝ X)
    (hY : Convex ℝ Y) (hu : ConcaveOn ℝ X u) (x y : S) :
    ParetoOptimal (fun _ : ι => X) (fun _ => u) (fun _ : ι => Y) (fun _ => x) (fun _ => y) ↔
      x = y ∧ x ∈ X ∧ x ∈ Y ∧ ∀ z ∈ X, z ∈ Y → u z ≤ u x := by
  classical
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hsum : ∀ w : S, ∑ _i : ι, w = (Fintype.card ι : ℝ) • w := fun w => by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
  constructor
  · rintro ⟨⟨hxX, hyY, hxy⟩, hno⟩
    have hxy' : x = y := by
      rw [hsum, hsum, ← smul_sub] at hxy
      exact sub_eq_zero.1 ((smul_eq_zero.1 hxy).resolve_left hcard.ne')
    subst hxy'
    refine ⟨rfl, hxX (Classical.arbitrary ι), hyY (Classical.arbitrary ι), fun z hz hzY => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hno ⟨fun _ => z, fun _ => z, ⟨fun _ => hz, fun _ => hzY, by simp⟩,
      fun _ => hlt.le, Classical.arbitrary ι, hlt⟩
  · rintro ⟨rfl, hxX, hxY, hmax⟩
    refine ⟨⟨fun _ => hxX, fun _ => hxY, by simp⟩, ?_⟩
    rintro ⟨x', y', ⟨hx'X, hy'Y, hfeas⟩, hge, i₀, hi₀⟩
    set w : ι → ℝ := fun _ => 1 / (Fintype.card ι : ℝ) with hw
    have hw0 : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i := fun _ _ => by positivity
    have hw1 : ∑ i ∈ (Finset.univ : Finset ι), w i = 1 := by
      simp only [hw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    have hbarX : ∑ i, w i • x' i ∈ X := hX.sum_mem hw0 hw1 fun i _ => hx'X i
    have hbar : ∑ i, w i • x' i = ∑ j, w j • y' j := by
      simp only [hw, ← Finset.smul_sum]
      rw [sub_eq_zero.1 hfeas]
    have hbarY : ∑ i, w i • x' i ∈ Y := hbar ▸ hY.sum_mem hw0 hw1 fun j _ => hy'Y j
    have hjensen := hu.le_map_sum hw0 hw1 fun i _ => hx'X i
    have hlt : u x < ∑ i, w i • u (x' i) := by
      have : ∑ i, w i • u x < ∑ i, w i • u (x' i) :=
        Finset.sum_lt_sum (fun i _ => smul_le_smul_of_nonneg_left (hge i) (hw0 i (by simp)))
          ⟨i₀, by simp, smul_lt_smul_of_pos_left hi₀ (by positivity)⟩
      rwa [← Finset.sum_smul, hw1, one_smul] at this
    linarith [hmax _ hbarX hbarY]

/-! ### Existence and uniqueness of the optimum -/

variable {U f : ℝ → ℝ} {β khat kbar : ℝ}

/-- **Existence of the optimum** (the hint "Exercise 5.1" of Ex 16.1a): `u` attains its maximum on
`X ∩ Y`. The feasible (output, capital) pairs form a closed subset of the compact box
`[0, k_max]^ℕ × [0, k_max]^ℕ` (product topology), on which `u` is continuous (uniform convergence
of the series, `U` bounded). -/
theorem gc_exists_optimum (h : GrowthCertaintyHyp U f β khat kbar) :
    ∃ x ∈ gcX, x ∈ gcY f khat ∧ ∀ z ∈ gcX, z ∈ gcY f khat → gcU β U z ≤ gcU β U x := by
  obtain ⟨M, hM⟩ := h.U_bdd
  set B := gcKmax khat kbar with hB
  have hB0 : 0 < B := gc_kmax_pos h
  set fe : ℝ → ℝ := fun s => f (max s 0) with hfe
  have hfec : Continuous fe :=
    h.f_cont.comp_continuous (continuous_id.max continuous_const) fun s => le_max_right s 0
  have hfe_eq : ∀ s, 0 ≤ s → fe s = f s := fun s hs => by simp [hfe, max_eq_left hs]
  set P : Set ((ℕ → ℝ) × (ℕ → ℝ)) := {p | (∀ t, 0 ≤ p.1 t) ∧ p.2 0 = khat ∧
    (∀ t, 0 ≤ p.2 t) ∧ ∀ t, p.2 (t + 1) + p.1 t ≤ fe (p.2 t)} with hP
  set box : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (univ.pi fun _ => Icc 0 B) ×ˢ (univ.pi fun _ => Icc 0 B) with hbox
  have hPbox : P ⊆ box := by
    rintro ⟨y, k⟩ ⟨hy, hk0, hk, hkf⟩
    have hkf' : ∀ t, k (t + 1) + y t ≤ f (k t) := fun t => (hfe_eq _ (hk t)) ▸ hkf t
    have hkB := gc_capital_le h hy hk0 hk hkf'
    refine ⟨fun t _ => ⟨hy t, ?_⟩, fun t _ => ⟨hk t, hkB t⟩⟩
    linarith [hkf' t, hk (t + 1), gc_f_le_kmax h (hk t) (hkB t)]
  have hPeq : P = (⋂ t, {p : (ℕ → ℝ) × (ℕ → ℝ) | 0 ≤ p.1 t}) ∩ ({p | p.2 0 = khat} ∩
      ((⋂ t, {p | 0 ≤ p.2 t}) ∩ ⋂ t, {p | p.2 (t + 1) + p.1 t ≤ fe (p.2 t)})) := by
    ext p
    simp [hP]
  have hPclosed : IsClosed P := by
    rw [hPeq]
    refine (isClosed_iInter fun t => isClosed_le continuous_const (by fun_prop)).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
      ((isClosed_iInter fun t => isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_iInter fun t => isClosed_le (by fun_prop)
        (hfec.comp ((continuous_apply t).comp continuous_snd)))))
  have hboxc : IsCompact box :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hPc : IsCompact P := hboxc.of_isClosed_subset hPclosed hPbox
  have hPne : P.Nonempty := ⟨(fun _ => 0, fun t => if t = 0 then khat else 0),
    fun _ => le_rfl, by simp, fun t => by
      dsimp only
      split_ifs
      exacts [h.khat_pos.le, le_rfl], fun t => by
      dsimp only
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      split_ifs with ht
      · rw [hfe_eq _ h.khat_pos.le]
        simpa using gc_f_nonneg h h.khat_pos.le
      · rw [hfe_eq _ le_rfl, h.f_zero]
        simp⟩
  set V : (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun p => ∑' t, β ^ t * U (p.1 t) with hV
  have hVc : ContinuousOn V box := by
    refine continuousOn_tsum (u := fun t => M * β ^ t) (fun t => ?_)
      ((summable_geometric_of_lt_one h.beta_pos.le h.beta_lt_one).mul_left M) (fun t p hp => ?_)
    · refine continuousOn_const.mul (h.U_cont.comp
        ((continuous_apply t).comp continuous_fst).continuousOn fun p hp => ?_)
      exact (hp.1 t (mem_univ t)).1
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h.beta_pos.le t), mul_comm]
      exact mul_le_mul_of_nonneg_right (hM _ (hp.1 t (mem_univ t)).1)
        (pow_nonneg h.beta_pos.le t)
  obtain ⟨p, hpP, hpmax⟩ := hPc.exists_isMaxOn hPne (hVc.mono hPbox)
  have hpB : ∀ t, ‖p.1 t‖ ≤ B := fun t => by
    have := (hPbox hpP).1 t (mem_univ t)
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2
  set x : BddSeq ℝ := BddSeq.mk p.1 B hpB with hx
  have hxX : x ∈ gcX := mem_gcX.2 hpP.1
  refine ⟨x, hxX, ⟨hpP.1, p.2, hpP.2.1, hpP.2.2.1, fun t => ?_⟩, fun z hz hzY => ?_⟩
  · rw [← hfe_eq _ (hpP.2.2.1 t)]
    exact hpP.2.2.2 t
  · obtain ⟨-, k, hk0, hk, hkf⟩ := hzY
    have hzP : ((z : ℕ → ℝ), k) ∈ P :=
      ⟨mem_gcX.1 hz, hk0, hk, fun t => (hfe_eq _ (hk t)).symm ▸ hkf t⟩
    exact hpmax hzP

/-- **Uniqueness of the optimum**: two maximisers of `u` on `X ∩ Y` coincide (their midpoint is in
`X ∩ Y` and is strictly better, by strict concavity of `U`). -/
theorem gc_optimum_unique (h : GrowthCertaintyHyp U f β khat kbar) {x x' : BddSeq ℝ}
    (hx : x ∈ gcX) (hxY : x ∈ gcY f khat)
    (hmax : ∀ z ∈ gcX, z ∈ gcY f khat → gcU β U z ≤ gcU β U x)
    (hx' : x' ∈ gcX) (hx'Y : x' ∈ gcY f khat)
    (hmax' : ∀ z ∈ gcX, z ∈ gcY f khat → gcU β U z ≤ gcU β U x') : x = x' := by
  by_contra hne
  have hmX : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x' ∈ gcX :=
    convex_seqSet (convex_Ici 0) hx hx' (by norm_num) (by norm_num) (by norm_num)
  have hmY : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x' ∈ gcY f khat :=
    gc_convex_Y h hxY hx'Y (by norm_num) (by norm_num) (by norm_num)
  have h1 := gc_utility_strict_midpoint h hx hx' hne
  have h2 := hmax _ hmX hmY
  have h3 := hmax x' hx' hx'Y
  have h4 := hmax' x hx hxY
  linarith

/-! ### Exercise 16.1(a) -/

/-- **Exercise 16.1(a)**: with `I ≥ 1` identical consumers and `I` identical firms, there is exactly
one symmetric Pareto-optimal allocation (every symmetric Pareto optimum has `x = y`); and, by
Theorem 15.3 (local nonsatiation, `gc_localNonsatiation`), any two symmetric competitive equilibrium
allocations coincide — there is at most one. -/
theorem ex_16_1a {ι : Type*} [Fintype ι] [Nonempty ι] (h : GrowthCertaintyHyp U f β khat kbar) :
    (∃! x : BddSeq ℝ, ParetoOptimal (fun _ : ι => gcX) (fun _ => gcU β U)
      (fun _ : ι => gcY f khat) (fun _ => x) (fun _ => x)) ∧
    (∀ x y : BddSeq ℝ, ParetoOptimal (fun _ : ι => gcX) (fun _ => gcU β U)
      (fun _ : ι => gcY f khat) (fun _ => x) (fun _ => y) → x = y) ∧
    ∀ (x y x' y' : BddSeq ℝ) (φ φ' : StrongDual ℝ (BddSeq ℝ)),
      CompetitiveEq (fun _ : ι => gcX) (fun _ => gcU β U) (fun _ : ι => gcY f khat)
        (fun _ => x) (fun _ => y) φ →
      CompetitiveEq (fun _ : ι => gcX) (fun _ => gcU β U) (fun _ : ι => gcY f khat)
        (fun _ => x') (fun _ => y') φ' → x = x' ∧ y = y' := by
  have hiff := fun x y => gc_symmetric_paretoOptimal_iff (ι := ι)
    gc_convex_X (gc_convex_Y h) (gc_utility_concave h) x y
  obtain ⟨x₀, hx₀, hx₀Y, hmax⟩ := gc_exists_optimum h
  have hPO : ∀ x y, ParetoOptimal (fun _ : ι => gcX) (fun _ => gcU β U)
      (fun _ : ι => gcY f khat) (fun _ => x) (fun _ => y) → x = x₀ ∧ y = x₀ := by
    intro x y hxy
    obtain ⟨rfl, hx, hxY, hxmax⟩ := (hiff x y).1 hxy
    have := gc_optimum_unique h hx hxY hxmax hx₀ hx₀Y hmax
    exact ⟨this, this⟩
  refine ⟨⟨x₀, (hiff x₀ x₀).2 ⟨rfl, hx₀, hx₀Y, hmax⟩, fun x hx => (hPO x x hx).1⟩,
    fun x y hxy => by rw [(hPO x y hxy).1, (hPO x y hxy).2], fun x y x' y' φ φ' hce hce' => ?_⟩
  have h1 := hPO x y (theorem_15_3 (gc_localNonsatiation h) hce)
  have h2 := hPO x' y' (theorem_15_3 (gc_localNonsatiation h) hce')
  exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩

/-! ### Exercise 16.1(b) -/

/-- The optimum is Pareto optimal in the one-consumer, one-firm economy. -/
theorem gc_paretoOptimal_of_max (h : GrowthCertaintyHyp U f β khat kbar) {x₀ : BddSeq ℝ}
    (hx₀ : x₀ ∈ gcX) (hx₀Y : x₀ ∈ gcY f khat)
    (hmax : ∀ z ∈ gcX, z ∈ gcY f khat → gcU β U z ≤ gcU β U x₀) :
    ParetoOptimal (fun _ : Unit => gcX) (fun _ => gcU β U) (fun _ : Unit => gcY f khat)
      (fun _ => x₀) (fun _ => x₀) :=
  (gc_symmetric_paretoOptimal_iff gc_convex_X (gc_convex_Y h)
    (gc_utility_concave h) x₀ x₀).2 ⟨rfl, hx₀, hx₀Y, hmax⟩

/-- **Exercise 16.1(b)**: Theorem 15.4 applies (Assumptions 15.1–15.5 by `ex_16_1b_assumptions`,
nonsatiation `u(x⁰ + 𝟙) > u(x⁰)`), and with the cheaper point `0` (`ex_16_1b_cheaper`) the Remark
after it makes the optimum `(x⁰, x⁰)` a competitive equilibrium for some `φ ≠ 0`. So a symmetric
competitive equilibrium exists. -/
theorem ex_16_1b (h : GrowthCertaintyHyp U f β khat kbar) :
    ∃ x₀ ∈ gcX, x₀ ∈ gcY f khat ∧ (∀ z ∈ gcX, z ∈ gcY f khat → gcU β U z ≤ gcU β U x₀) ∧
      ∃ φ : StrongDual ℝ (BddSeq ℝ), φ ≠ 0 ∧
        SupportsAllocation (fun _ : Unit => gcX) (fun _ => gcU β U) (fun _ : Unit => gcY f khat)
          (fun _ => x₀) (fun _ => x₀) φ ∧
        CompetitiveEq (fun _ : Unit => gcX) (fun _ => gcU β U) (fun _ : Unit => gcY f khat)
          (fun _ => x₀) (fun _ => x₀) φ := by
  obtain ⟨x₀, hx₀, hx₀Y, hmax⟩ := gc_exists_optimum h
  obtain ⟨h1, h2, h3, h4, h5⟩ := ex_16_1b_assumptions h
  have hPO := gc_paretoOptimal_of_max h hx₀ hx₀Y hmax
  have hsatX : x₀ + oneSeq ∈ gcX := mem_gcX.2 fun t => by
    rw [gc_coord_add, gc_coord_one]
    linarith [mem_gcX.1 hx₀ t]
  have hsat : gcU β U x₀ < gcU β U (x₀ + oneSeq) :=
    gc_utility_lt h hx₀ hsatX (fun t => by rw [gc_coord_add, gc_coord_one]; linarith) (t₀ := 0)
      (by rw [gc_coord_add, gc_coord_one]; linarith)
  obtain ⟨φ, hne, hsup⟩ := theorem_15_4 h1 h2 h3 h4 h5 hPO (h := ()) hsatX hsat
  have hcheap := ex_16_1b_cheaper h hx₀ hne hsup
  exact ⟨x₀, hx₀, hx₀Y, hmax, φ, hne, hsup, remark_cheaper_point h1 h3 hPO.1 hsup
    fun _ => ⟨0, mem_gcX.2 fun _ => le_rfl, hcheap⟩⟩

/-! ### Exercise 16.1(c) -/

/-- **Exercise 16.1(c)**: by Theorem 15.6 (Assumptions 15.6–15.7 by `ex_16_1c_assumptions`), for any
`φ ≠ 0` supporting the optimum, its regular part `ψ` (Lemma 15.5) is an equilibrium price system
with an `ℓ₁` representation: `ψ(x) = Σ_t p_t x_t` with `p_t = ψ(e_t) = φ(e_t)`,
`Σ_t |p_t| ≤ ‖φ‖`, every `p_t > 0`, and `(x⁰, x⁰, ψ)` a competitive equilibrium (the cheaper point
`0`: `ψ(x⁰) = φ(x⁰) > 0 = ψ(0)`). -/
theorem ex_16_1c (h : GrowthCertaintyHyp U f β khat kbar) {x₀ : BddSeq ℝ} (hx₀ : x₀ ∈ gcX)
    (hx₀Y : x₀ ∈ gcY f khat) {φ : StrongDual ℝ (BddSeq ℝ)} (hne : φ ≠ 0)
    (hsup : SupportsAllocation (fun _ : Unit => gcX) (fun _ => gcU β U)
      (fun _ : Unit => gcY f khat) (fun _ => x₀) (fun _ => x₀) φ) :
    CompetitiveEq (fun _ : Unit => gcX) (fun _ => gcU β U) (fun _ : Unit => gcY f khat)
        (fun _ => x₀) (fun _ => x₀) (seqRegularPart φ) ∧
      (∀ t, seqRegularPart φ (lp.single ∞ t 1) = φ (lp.single ∞ t 1)) ∧
      Summable (fun t => |seqRegularPart φ (lp.single ∞ t 1)|) ∧
      ∑' t, |seqRegularPart φ (lp.single ∞ t 1)| ≤ ‖φ‖ ∧
      (∀ x : BddSeq ℝ,
        HasSum (fun t => seqRegularPart φ (lp.single ∞ t 1) * x t) (seqRegularPart φ x)) ∧
      ∀ t, 0 < seqRegularPart φ (lp.single ∞ t 1) := by
  obtain ⟨h1, h2, h3, -, -⟩ := ex_16_1b_assumptions h
  obtain ⟨h6, h7⟩ := ex_16_1c_assumptions h
  have hfeas : Feasible (fun _ : Unit => gcX) (fun _ : Unit => gcY f khat) (fun _ => x₀)
      (fun _ => x₀) := ⟨fun _ => hx₀, fun _ => hx₀Y, by simp⟩
  have hsatX : x₀ + oneSeq ∈ gcX := mem_gcX.2 fun t => by
    rw [gc_coord_add, gc_coord_one]
    linarith [mem_gcX.1 hx₀ t]
  have hsat : gcU β U x₀ < gcU β U (x₀ + oneSeq) :=
    gc_utility_lt h hx₀ hsatX (fun t => by rw [gc_coord_add, gc_coord_one]; linarith) (t₀ := 0)
      (by rw [gc_coord_add, gc_coord_one]; linarith)
  have hns : ∀ i : Unit, ∃ xh ∈ gcX, gcU β U x₀ < gcU β U xh := fun _ => ⟨_, hsatX, hsat⟩
  obtain ⟨-, -, hψx, -⟩ := theorem_15_6 h1 h2 h6 h7 hfeas φ hsup.1 hsup.2 hns
  have hcheap := ex_16_1b_cheaper h hx₀ hne hsup
  have hCE := theorem_15_6_competitiveEq h1 h2 h3 h6 h7 hfeas φ hsup.1 hsup.2 hns
    fun _ => ⟨0, mem_gcX.2 fun _ => le_rfl, by rw [map_zero, hψx ()]; simpa using hcheap⟩
  obtain ⟨hs, hle, hrep⟩ := seqRegularPart_real (seqRegularPart φ)
  refine ⟨hCE, fun t => ?_, hs, hle.trans (norm_seqRegularPart_le φ), fun x => ?_,
    fun t => gc_price_pos h hCE () t⟩
  · refine seqRegularPart_eq_of_mem_seqC00 φ ((eventually_gt_atTop t).mono fun s hs => ?_)
    rw [gc_coord_single]
    simp [hs.ne']
  · simpa [seqRegularPart_seqRegularPart] using hrep x

end StokeyLucasPrescott.EquilibriumApplications

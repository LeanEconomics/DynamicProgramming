/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import AKMMSovereignDefault.Bellman

/-!
# Markov perfect equilibrium, the borrowing condition (24.13) and (24.A.3)

AKMM, §24.4.3, pp. 744–745; §24.4.4, (24.13), p. 748; Appendix 24.A.1, (24.A.3), p. 898.

* **Definition (§24.4.3)**: value functions `V, V^R, V^D`, a default rule `D̂`, a borrowing rule
  `B̂` and a price `q` with (a) (24.9)–(24.11) at `q`, (b) (24.12) given `D̂, B̂`, (c) `D̂, B̂`
  optimal (`IsMPE`, with a proved instance `mpe_example`).
* **As a fixed point** (`mpe_iff_fixedPt`): with `(V, V^D)` the unique Bellman solution at `q`,
  `D̂` its tie-repaying default rule and `B̂` a selection of maximisers, the tuple is an MPE iff
  `q` is a fixed point of `q ↦ T_{D̂(q), B̂(q)} q`; every MPE's values and default rule are
  those induced by its price (`mpe_values_eq`). The map is not a contraction (the induced rules
  jump in `q`); existence and uniqueness of an MPE are not formalised (beyond the text:
  Auclert–Rognlie, Aguiar–Amador, cited p. 901).
* In every MPE: `q ∈ [0, δ/(δ + r)]` (`mpe_price_mem`), `V` is nonincreasing in debt
  (`mpe_V_antitone`) and the default rule is nondecreasing in debt (`mpe_default_mono`).
* **(24.13)** (`eq_24_13`): at an interior optimum,
  `u′(C)[q + ∂q/∂B′ (B′ − (1 − δ)B)] = −βE[V₁(B′, Y′)]`; the printed equation lacks the minus
  sign and is false whenever `βE[V₁] ≠ 0` (`eq_24_13_printed_false`, with an explicit instance
  `eq_24_13_printed_counterexample`); with `V₁ ≤ 0` the marginal revenue is nonnegative
  (`eq_24_13_sign`).
* **(24.A.3)** (`eq_24_A_3`): `d q(B̂(B, Y), Y)/dY = q₁ ∂B̂/∂Y + q₂`.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

variable {Y Bd : Type*} [Fintype Y] [Fintype Bd]

variable (M : SDModel Y Bd) (r : ℝ) (V VR : Bd → Y → ℝ) (VD : Y → ℝ) (D : Bd → Y → ℝ)
  (Bh : Bd → Y → Bd) (q : Bd → Y → ℝ) in
/-- **AKMM, §24.4.3**, pp. 744–745: a Markov perfect equilibrium `(V, V^R, V^D, D̂, B̂, q)`. -/
structure IsMPE : Prop where
  /-- (a) (24.9). -/
  eq_24_9 : ∀ b y, V b y = max (VD y) (VR b y)
  /-- (a) (24.10). -/
  eq_24_10 : ∀ y, VD y = M.defaultValue V VD y
  /-- (a) (24.11). -/
  eq_24_11 : ∀ b y, VR b y = M.repayValue q V b y
  /-- (b) (24.12) given `D̂` and `B̂`. -/
  eq_24_12 : ∀ m y, q m y = bp_op12 M.P r M.δ D Bh q m y
  /-- (c) the default rule is optimal (ties repaid). -/
  default_opt : ∀ b y, D b y = if VR b y < VD y then 1 else 0
  /-- (c) the borrowing rule attains the maximum in (24.11). -/
  borrow_opt : ∀ b y, M.u (M.cons q y b (Bh b y)) + M.β * ∑ j, M.P y j * V (Bh b y) j = VR b y

/-- A Markov perfect equilibrium of the one-state, one-debt-level example `sd_example`
(with `r > −1`): `V = V^R = V^D = 2`, no default, and `q = 1/(1 + r)`. -/
theorem mpe_example {r : ℝ} (hr : -1 < r) :
    IsMPE sd_example r (fun _ _ => 2) (fun _ _ => 2) (fun _ => 2) (fun _ _ => 0)
      (fun _ _ => ()) (fun _ _ => (1 + r)⁻¹) where
  eq_24_9 := fun b y => ((sd_example_solution _).1 b y).trans
    (by rw [(sd_example_solution (fun _ _ => (1 + r)⁻¹)).1 b y |>.symm]; simp)
  eq_24_10 := (sd_example_solution (fun _ _ => (1 + r)⁻¹)).2
  eq_24_11 := fun b y => by
    have := (sd_example_solution (fun _ _ => (1 + r)⁻¹)).1 b y
    simp only [SDModel.repayValue, SDModel.cons, sd_example, univ_unique, sup'_singleton,
      sum_singleton, id] at this ⊢
    norm_num
  eq_24_12 := fun m y => by
    have : (1 + r) ≠ 0 := by linarith
    simp only [bp_op12, sd_example, univ_unique, sum_singleton]
    ring
  default_opt := fun b y => by simp
  borrow_opt := fun b y => by
    simp only [SDModel.cons, sd_example, univ_unique, sum_singleton, id]
    norm_num

/-- The unique solution `(V, V^D)` of (24.9)–(24.11) at the price `q`. -/
noncomputable def SDModel.bellmanSol (M : SDModel Y Bd) (q : Bd → Y → ℝ) :
    (Bd → Y → ℝ) × (Y → ℝ) :=
  (M.eq_24_9_to_24_11 q).choose

/-- The induced default rule (ties repaid). -/
noncomputable def SDModel.inducedDefault (M : SDModel Y Bd) (q : Bd → Y → ℝ) (b : Bd) (y : Y) :
    ℝ :=
  if M.repayValue q (M.bellmanSol q).1 b y < (M.bellmanSol q).2 y then 1 else 0

/-- A selection of maximisers in (24.11). -/
noncomputable def SDModel.inducedBorrow (M : SDModel Y Bd) (q : Bd → Y → ℝ) (b : Bd) (y : Y) :
    Bd :=
  (univ.exists_max_image (fun b' => M.u (M.cons q y b b') +
    M.β * ∑ j, M.P y j * (M.bellmanSol q).1 b' j) ⟨M.b₀, mem_univ _⟩).choose

/-- The equilibrium map `q ↦ T_{D̂(q), B̂(q)} q` of (24.A.1)–(24.A.2). -/
noncomputable def SDModel.mpeMap (M : SDModel Y Bd) (r : ℝ) (q : Bd → Y → ℝ) : Bd → Y → ℝ :=
  bp_op12 M.P r M.δ (M.inducedDefault q) (M.inducedBorrow q) q

/-- The selection attains the maximum: `u(C(B̂)) + βE V(B̂, Y′) = V^R(B, Y)`. -/
theorem SDModel.inducedBorrow_spec (M : SDModel Y Bd) (q : Bd → Y → ℝ) (b : Bd) (y : Y) :
    M.u (M.cons q y b (M.inducedBorrow q b y)) +
        M.β * ∑ j, M.P y j * (M.bellmanSol q).1 (M.inducedBorrow q b y) j =
      M.repayValue q (M.bellmanSol q).1 b y := by
  have h := (univ.exists_max_image (fun b' => M.u (M.cons q y b b') +
    M.β * ∑ j, M.P y j * (M.bellmanSol q).1 b' j) ⟨M.b₀, mem_univ _⟩).choose_spec
  refine le_antisymm (le_sup' (fun b' => M.u (M.cons q y b b') +
    M.β * ∑ j, M.P y j * (M.bellmanSol q).1 b' j) (mem_univ _)) ?_
  exact sup'_le _ _ fun b' _ => h.2 b' (mem_univ _)

/-- **AKMM, §24.4.3, the MPE as a fixed point**: with the Bellman solution, default rule and
borrowing selection induced by `q`, the tuple is a Markov perfect equilibrium iff `q` is a fixed
point of the equilibrium map. -/
theorem mpe_iff_fixedPt (M : SDModel Y Bd) (r : ℝ) (q : Bd → Y → ℝ) :
    Function.IsFixedPt (M.mpeMap r) q ↔
      IsMPE M r (M.bellmanSol q).1 (M.repayValue q (M.bellmanSol q).1) (M.bellmanSol q).2
        (M.inducedDefault q) (M.inducedBorrow q) q := by
  have hs := (M.eq_24_9_to_24_11 q).choose_spec.1
  constructor
  · intro hfix
    exact { eq_24_9 := hs.1
            eq_24_10 := hs.2
            eq_24_11 := fun _ _ => rfl
            eq_24_12 := fun m y => (congrFun (congrFun hfix m) y).symm
            default_opt := fun _ _ => rfl
            borrow_opt := M.inducedBorrow_spec q }
  · intro h
    funext m y
    exact (h.eq_24_12 m y).symm

/-- AKMM, §24.4.3: in every MPE the value functions and the default rule are those induced by
the price `q`: `(V, V^D)` is the unique Bellman solution at `q`, `V^R` is (24.11) and `D̂` the
tie-repaying rule. -/
theorem mpe_values_eq {M : SDModel Y Bd} {r : ℝ} {V VR : Bd → Y → ℝ} {VD : Y → ℝ}
    {D : Bd → Y → ℝ} {Bh : Bd → Y → Bd} {q : Bd → Y → ℝ} (h : IsMPE M r V VR VD D Bh q) :
    (V, VD) = M.bellmanSol q ∧ VR = M.repayValue q V ∧ D = M.inducedDefault q := by
  have hu := (M.eq_24_9_to_24_11 q).choose_spec.2
  have hVR : VR = M.repayValue q V := funext fun b => funext fun y => h.eq_24_11 b y
  have hW : (V, VD) = M.bellmanSol q :=
    hu (V, VD) ⟨fun b y => by
      change V b y = max (VD y) (M.repayValue q V b y)
      rw [h.eq_24_9, hVR], h.eq_24_10⟩
  refine ⟨hW, hVR, funext fun b => funext fun y => ?_⟩
  rw [h.default_opt, SDModel.inducedDefault, ← hW, hVR]

/-- AKMM, (24.12) in equilibrium: in every MPE (with `r > −1`, `δ + r > 0`) the price lies in
`[0, δ/(δ + r)]`. -/
theorem mpe_price_mem {M : SDModel Y Bd} {r : ℝ} {V VR : Bd → Y → ℝ} {VD : Y → ℝ}
    {D : Bd → Y → ℝ} {Bh : Bd → Y → Bd} {q : Bd → Y → ℝ} (h : IsMPE M r V VR VD D Bh q)
    (hr : -1 < r) (hδr : 0 < M.δ + r) (m : Bd) (y : Y) :
    0 ≤ q m y ∧ q m y ≤ M.δ / (M.δ + r) := by
  classical
  have hD : ∀ m j, D m j = 0 ∨ D m j = 1 := fun m j => by
    rw [h.default_opt]; split_ifs <;> simp
  have hA : BPAdmissible M.P r M.δ D (fun m j h => if Bh m j = h then 1 else 0) :=
    { markov := M.markov
      D_nonneg := fun m j => by rcases hD m j with h | h <;> simp [h]
      D_le_one := fun m j => by rcases hD m j with h | h <;> simp [h]
      B_nonneg := fun _ _ _ => by split_ifs <;> norm_num
      B_sum := fun m j => by simp
      δ_nonneg := M.δ_nonneg
      δ_le_one := M.δ_le_one
      r_gt := hr
      δr_pos := hδr }
  have hfix : Function.IsFixedPt (bp_op M.P r M.δ D (fun m j h => if Bh m j = h then 1 else 0))
      q := by
    rw [← bp_op12_eq]
    funext m y
    exact (h.eq_24_12 m y).symm
  have hc := bp_contracting hA
  obtain ⟨q', ⟨hfix', hb'⟩, -⟩ := eq_24_A_6 hA
  rw [hc.fixedPoint_unique hfix, ← hc.fixedPoint_unique hfix']
  exact hb' m y

/-- AKMM, p. 744: in every MPE (with `u` nondecreasing, `r > −1`, `δ + r > 0`) the value `V`
is nonincreasing in debt. -/
theorem mpe_V_antitone {M : SDModel Y Bd} {r : ℝ} {V VR : Bd → Y → ℝ} {VD : Y → ℝ}
    {D : Bd → Y → ℝ} {Bh : Bd → Y → Bd} {q : Bd → Y → ℝ} (h : IsMPE M r V VR VD D Bh q)
    (hu : Monotone M.u) (hr : -1 < r) (hδr : 0 < M.δ + r) {b b' : Bd}
    (hbb : M.bond b ≤ M.bond b') (y : Y) : V b' y ≤ V b y :=
  M.sd_V_antitone hu (fun m y => (mpe_price_mem h hr hδr m y).1)
    (fun b y => by rw [h.eq_24_9, h.eq_24_11]) hbb y

/-- AKMM, p. 744 and App. 24.A.3: in every MPE the default rule is nondecreasing in debt: if the
sovereign defaults at `(b, Y)` it defaults at `(b′, Y)` for `B(b′) ≥ B(b)`. -/
theorem mpe_default_mono {M : SDModel Y Bd} {r : ℝ} {V VR : Bd → Y → ℝ} {VD : Y → ℝ}
    {D : Bd → Y → ℝ} {Bh : Bd → Y → Bd} {q : Bd → Y → ℝ} (h : IsMPE M r V VR VD D Bh q)
    (hu : Monotone M.u) (hr : -1 < r) (hδr : 0 < M.δ + r) {b b' : Bd}
    (hbb : M.bond b ≤ M.bond b') (y : Y) : D b y ≤ D b' y := by
  have hVR := M.sd_VR_antitone hu (fun m y => (mpe_price_mem h hr hδr m y).1) V hbb y
  rw [h.default_opt, h.default_opt, h.eq_24_11, h.eq_24_11]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_le_of_lt hVR h1) h2
  · exact zero_le_one
  · exact le_rfl

/-- **AKMM, (24.13)**, p. 748, corrected: at an interior optimum `B′` of
`u(Y − δB + q(B′)[B′ − (1 − δ)B]) + βΣ_j p_j V(B′, Y_j)` with `u`, `q` and each `V(·, Y_j)`
differentiable, `u′(C)[q + q′(B′ − (1 − δ)B)] = −βΣ_j p_j V₁(B′, Y_j)`. -/
theorem eq_24_13 {u q : ℝ → ℝ} {Vn : Y → ℝ → ℝ} {p : Y → ℝ} {β δ B Yc Bp u₁ q₁ : ℝ}
    {V₁ : Y → ℝ} (hu : HasDerivAt u u₁ (Yc - δ * B + q Bp * (Bp - (1 - δ) * B)))
    (hq : HasDerivAt q q₁ Bp) (hV : ∀ j, HasDerivAt (Vn j) (V₁ j) Bp)
    (hmax : IsLocalMax (fun x => u (Yc - δ * B + q x * (x - (1 - δ) * B)) +
      β * ∑ j, p j * Vn j x) Bp) :
    u₁ * (q Bp + q₁ * (Bp - (1 - δ) * B)) = -(β * ∑ j, p j * V₁ j) := by
  have hC : HasDerivAt (fun x => Yc - δ * B + q x * (x - (1 - δ) * B))
      (q₁ * (Bp - (1 - δ) * B) + q Bp * 1) Bp := by
    have := hq.mul ((hasDerivAt_id Bp).sub_const ((1 - δ) * B))
    simpa using this.const_add (Yc - δ * B)
  have hS : HasDerivAt (fun x => ∑ j, p j * Vn j x) (∑ j, p j * V₁ j) Bp :=
    HasDerivAt.fun_sum fun j _ => (hV j).const_mul (p j)
  have hg := (HasDerivAt.comp Bp hu hC).add (hS.const_mul β)
  have := hmax.hasDerivAt_eq_zero hg
  linarith

/-- AKMM, (24.13), p. 748, **as printed** (`… = βE[V₁]`, without the minus sign) it is false
whenever `βE[V₁] ≠ 0`: it is inconsistent with the first-order condition `eq_24_13`. -/
theorem eq_24_13_printed_false {u q : ℝ → ℝ} {Vn : Y → ℝ → ℝ} {p : Y → ℝ}
    {β δ B Yc Bp u₁ q₁ : ℝ} {V₁ : Y → ℝ}
    (hu : HasDerivAt u u₁ (Yc - δ * B + q Bp * (Bp - (1 - δ) * B)))
    (hq : HasDerivAt q q₁ Bp) (hV : ∀ j, HasDerivAt (Vn j) (V₁ j) Bp)
    (hmax : IsLocalMax (fun x => u (Yc - δ * B + q x * (x - (1 - δ) * B)) +
      β * ∑ j, p j * Vn j x) Bp) (hne : β * ∑ j, p j * V₁ j ≠ 0) :
    u₁ * (q Bp + q₁ * (Bp - (1 - δ) * B)) ≠ β * ∑ j, p j * V₁ j := by
  intro h
  have := eq_24_13 hu hq hV hmax
  apply hne
  linarith

/-- AKMM, (24.13), p. 748: an explicit instance of the hypotheses where the printed equation
fails. One income state, `u = id`, a constant price `q = β`, `V(B′) = −B′` (so `V₁ = −1 < 0`):
the objective is constant, every `B′` is optimal, the corrected condition reads `β = β` and the
printed one `β = −β`. -/
theorem eq_24_13_printed_counterexample {β : ℝ} (hβ : 0 < β) (δ B Yc Bp : ℝ) :
    IsLocalMax (fun x => id (Yc - δ * B + (fun _ => β) x * (x - (1 - δ) * B)) +
      β * ∑ _j : Unit, (1 : ℝ) * (fun x : ℝ => -x) x) Bp ∧
      (1 : ℝ) * ((fun _ => β) Bp + 0 * (Bp - (1 - δ) * B)) = -(β * ∑ _j : Unit, (1 : ℝ) * (-1)) ∧
      (1 : ℝ) * ((fun _ => β) Bp + 0 * (Bp - (1 - δ) * B)) ≠ β * ∑ _j : Unit, (1 : ℝ) * (-1) := by
  refine ⟨Filter.Eventually.of_forall fun x => le_of_eq ?_, by simp, ?_⟩
  · simp only [id, univ_unique, sum_singleton, one_mul]
    ring
  · simp only [univ_unique, sum_singleton, one_mul, zero_mul, add_zero]
    linarith

/-- AKMM, p. 748: with `V` nonincreasing in debt (`V₁ ≤ 0`), nonnegative probabilities and
`β ≥ 0`, the right-hand side `−βE[V₁]` of (24.13) is nonnegative, so at an optimum with
`u′(C) > 0` the marginal revenue `q + q′(B′ − (1 − δ)B)` is nonnegative. -/
theorem eq_24_13_sign {u q : ℝ → ℝ} {Vn : Y → ℝ → ℝ} {p : Y → ℝ} {β δ B Yc Bp u₁ q₁ : ℝ}
    {V₁ : Y → ℝ} (hu : HasDerivAt u u₁ (Yc - δ * B + q Bp * (Bp - (1 - δ) * B)))
    (hq : HasDerivAt q q₁ Bp) (hV : ∀ j, HasDerivAt (Vn j) (V₁ j) Bp)
    (hmax : IsLocalMax (fun x => u (Yc - δ * B + q x * (x - (1 - δ) * B)) +
      β * ∑ j, p j * Vn j x) Bp) (hu₁ : 0 < u₁) (hβ : 0 ≤ β) (hp : ∀ j, 0 ≤ p j)
    (hV₁ : ∀ j, V₁ j ≤ 0) : 0 ≤ q Bp + q₁ * (Bp - (1 - δ) * B) := by
  have h := eq_24_13 hu hq hV hmax
  have hs : ∑ j, p j * V₁ j ≤ 0 := sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hp j)
    (hV₁ j)
  have : 0 ≤ u₁ * (q Bp + q₁ * (Bp - (1 - δ) * B)) := by
    rw [h]; nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hs]
  by_contra hneg
  rw [not_le] at hneg
  linarith [mul_neg_of_pos_of_neg hu₁ hneg]

/-- **AKMM, (24.A.3)**, p. 898: the total derivative of the equilibrium price with respect to
income, `d q(B̂(B, Y), Y)/dY = q₁(B̂, Y) ∂B̂/∂Y + q₂(B̂, Y)`, for `q` differentiable at
`(B̂(B, Y), Y)` with derivative `L` (`q₁ = L(1, 0)`, `q₂ = L(0, 1)`). -/
theorem eq_24_A_3 {q : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {Bh : ℝ → ℝ} {Yc b' : ℝ}
    (hq : HasFDerivAt q L (Bh Yc, Yc)) (hB : HasDerivAt Bh b' Yc) :
    HasDerivAt (fun y => q (Bh y, y)) (L (1, 0) * b' + L (0, 1)) Yc := by
  have h := HasFDerivAt.comp_hasDerivAt (f := fun y => (Bh y, y)) Yc hq
    (hB.prodMk (hasDerivAt_id' Yc))
  have : ((b', 1) : ℝ × ℝ) = b' • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hv : L (b', 1) = L (1, 0) * b' + L (0, 1) := by
    rw [this, map_add, map_smul, smul_eq_mul, mul_comm]
  rw [← hv]
  exact h

end AKMM.SovereignDefault

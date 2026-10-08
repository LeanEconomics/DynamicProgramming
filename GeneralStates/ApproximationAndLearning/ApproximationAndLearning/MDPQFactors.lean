/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ApproximationAndLearning.MDPADP
import ApproximationAndLearning.Pospace
import ApproximationAndLearning.BoundedMeasurable

/-!
# Discrete MDPs and Q-factors

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.2.1 (pp. 105–108).

* A sup-norm contraction of `ℝ^G` with `G` finite is globally stable for the product topology.
* §3.2.1.1: the finite MDP ADP is regular, globally stable and finite, so Corollary 3.1.3 and
  Theorem 2.2.6 give optimality, convergence of VFI, OPI and HPI, and finite termination of HPI.
* **Exercise 3.2.1**: the MDP with countable state space, finite feasible sets and bounded
  rewards, as an ADP on `bX`, via Theorems 3.1.5 and 3.1.2.
* The Q-factor model (3.6) on `ℝ^G`: **Exercise 3.2.2** (it is an ADP), **Exercise 3.2.3**
  (greedy policies), **Exercise 3.2.4** (the Bellman operator (3.7)), **Exercise 3.2.5**
  (contraction) and **Exercise 3.2.6** (optimality, convergence, HPI in finitely many steps).
* The "only if" half of Exercise 3.2.3 needs every state to be reachable and `β > 0`:
  `exercise_3_2_3_converse_fails` is a two-state counterexample.
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

/-- On a finite index set, a `β`-contraction of `ℝ^G` for the supremum distance is globally stable
for the product topology. -/
theorem globallyStable_of_supContraction {G : Type*} [Finite G] {T : (G → ℝ) → G → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hT : IsSupContraction univ T β) : GloballyStable T := by
  have hbdd : ∀ v ∈ (univ : Set (G → ℝ)), IsBdd v := fun v _ => FiniteMDP.isBdd_of_finite v
  obtain ⟨u, -, hu, huniq, hlim⟩ := hT.globallyStable hβ0 hβ1 hbdd
    (fun _ _ _ _ => trivial) (mapsTo_univ _ _) univ_nonempty
  exact ⟨u, hu, fun w hw => huniq w trivial hw, fun v =>
    tendsto_pi_nhds.2 fun x => (hlim v trivial).tendsto_at x⟩

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- Each MDP policy operator is globally stable on `ℝ^X` (Exercise 1.2.1). -/
theorem adp_isGloballyStable : M.adp.IsGloballyStable := fun σ =>
  globallyStable_of_supContraction M.β_nonneg M.β_lt_one fun _ _ _ _ _ h x =>
    M.abs_Q_sub_le (σ.2 x) h

/-- §3.2.1.1 (p. 106): via Corollary 3.1.3 and Theorem 2.2.6, the finite MDP ADP satisfies the
fundamental optimality properties, VFI, OPI and HPI all converge, and HPI converges in finitely
many steps. -/
theorem section_3_2_1_1 :
    M.adp.FundamentalOptimality M.adp_isGloballyStable.wellPosed ∧
      (∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧
          M.adp.HPIConverges M.adp_isGloballyStable.wellPosed g vstar) ∧
      ∀ g, M.adp.IsSelector g → ∀ v ∈ M.adp.VU,
        ∃ n, M.adp.IsValueFunction ((M.adp.howard M.adp_isGloballyStable.wellPosed g)^[n] v) := by
  have := M.finite_policy
  obtain ⟨h1, h2⟩ := ADP.corollary_3_1_3 M.adp_regular M.adp_isGloballyStable (finite_range _)
  exact ⟨h1, h2, (ADP.fundamentalOptimality_of_finite M.adp_isGloballyStable.isOrderStable
    M.adp_regular (finite_range _)).2⟩

/-! ### The Q-factor model -/

/-- The feasible state-action pairs `G`. -/
def G : Type _ := {p : X × A // p.2 ∈ M.Γ p.1}

theorem finite_G : Finite M.G := by
  have h : {p : X × A | p.2 ∈ M.Γ p.1} = ⋃ x, ({x} : Set X) ×ˢ (M.Γ x : Set A) := by
    ext ⟨x, a⟩
    simp
  have hfin : {p : X × A | p.2 ∈ M.Γ p.1}.Finite := by
    rw [h]
    exact finite_iUnion fun x => (finite_singleton x).prod (M.Γ x).finite_toSet
  exact hfin.to_subtype

/-- `(x', σ(x'))` as a feasible pair. -/
def pairOf (σ : M.Policy) (x : X) : M.G := ⟨(x, σ.1 x), σ.2 x⟩

/-- The Q-factor policy operator (3.6):
`(S_σ q)(x, a) = r(x, a) + β ∑_{x'} q(x', σ(x'))P(x, a, x')`. -/
def Sσ (σ : M.Policy) (q : M.G → ℝ) (p : M.G) : ℝ :=
  M.r p.1.1 p.1.2 + M.β * ∑ x', q (M.pairOf σ x') * M.P p.1.1 p.1.2 x'

theorem Sσ_mono (σ : M.Policy) : Monotone (M.Sσ σ) := fun _ _ h p =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x' _ =>
    mul_le_mul_of_nonneg_right (h _) (M.P_nonneg _ _ p.2 x')) M.β_nonneg)

/-- **Exercise 3.2.2** (p. 107): `(ℝ^G, 𝕊)` is an ADP. -/
def qadp : ADP (M.G → ℝ) M.Policy where
  T := M.Sσ
  mono := M.Sσ_mono
  nonempty := M.nonempty_policy

/-- **Exercise 3.2.3** (p. 107), "if": a policy choosing `σ(x) ∈ argmax_{a ∈ Γ(x)} q(x, a)` at
every state is `q`-greedy. -/
theorem exercise_3_2_3 (q : M.G → ℝ) (σ : M.Policy)
    (h : ∀ x, ∀ a (ha : a ∈ M.Γ x), q ⟨(x, a), ha⟩ ≤ q (M.pairOf σ x)) : M.qadp.IsGreedy q σ :=
  fun τ p => add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x' _ =>
    mul_le_mul_of_nonneg_right (h x' (τ.1 x') (τ.2 x')) (M.P_nonneg _ _ p.2 x')) M.β_nonneg)

/-- **Exercise 3.2.3** (p. 107), "only if", at the states it can see: if `β > 0` and `σ` is
`q`-greedy, then `σ(x')` maximizes `q(x', ·)` at every state `x'` reachable from a feasible pair. -/
theorem exercise_3_2_3_converse (hβ : 0 < M.β) (q : M.G → ℝ) (σ : M.Policy)
    (hσ : M.qadp.IsGreedy q σ) {x' : X} (hreach : ∃ p : M.G, 0 < M.P p.1.1 p.1.2 x') :
    ∀ a (ha : a ∈ M.Γ x'), q ⟨(x', a), ha⟩ ≤ q (M.pairOf σ x') := by
  classical
  intro a ha
  obtain ⟨p, hp⟩ := hreach
  by_contra hlt
  rw [not_le] at hlt
  let τ : M.Policy := ⟨fun y => if y = x' then a else σ.1 y, fun y => by
    change (if y = x' then a else σ.1 y) ∈ M.Γ y
    split_ifs with hy
    · rw [hy]
      exact ha
    · exact σ.2 y⟩
  have hτx : M.pairOf τ x' = ⟨(x', a), ha⟩ := Subtype.ext (by simp [pairOf, τ])
  have hτy : ∀ y, y ≠ x' → M.pairOf τ y = M.pairOf σ y := fun y hy =>
    Subtype.ext (by simp [pairOf, τ, hy])
  have h := hσ τ p
  simp only [qadp, Sσ, add_le_add_iff_left] at h
  have hlt' : ∑ y, q (M.pairOf σ y) * M.P p.1.1 p.1.2 y <
      ∑ y, q (M.pairOf τ y) * M.P p.1.1 p.1.2 y := by
    refine Finset.sum_lt_sum (fun y _ => ?_) ⟨x', Finset.mem_univ _, ?_⟩
    · rcases eq_or_ne y x' with rfl | hy
      · rw [hτx]
        exact mul_le_mul_of_nonneg_right hlt.le (M.P_nonneg _ _ p.2 y)
      · rw [hτy y hy]
    · rw [hτx]
      exact mul_lt_mul_of_pos_right hlt hp
  linarith [mul_lt_mul_of_pos_left hlt' hβ]

/-- The Q-factor `q`-greedy policy: `σ(x) ∈ argmax_{a ∈ Γ(x)} q(x, a)`. -/
theorem exists_qgreedy (q : M.G → ℝ) :
    ∃ σ : M.Policy, ∀ x, ∀ a (ha : a ∈ M.Γ x), q ⟨(x, a), ha⟩ ≤ q (M.pairOf σ x) := by
  classical
  choose f hf hmax using fun x => Finset.exists_max_image (M.Γ x)
    (fun a => if ha : a ∈ M.Γ x then q ⟨(x, a), ha⟩ else 0) (M.Γ_nonempty x)
  refine ⟨⟨f, hf⟩, fun x a ha => ?_⟩
  have := hmax x a ha
  simp only [ha, hf x, ↓reduceDIte] at this
  exact this

/-- The Q-factor ADP is regular. -/
theorem qadp_regular : M.qadp.Regular := fun q => by
  obtain ⟨σ, hσ⟩ := M.exists_qgreedy q
  exact ⟨σ, M.exercise_3_2_3 q σ hσ⟩

/-- **Exercise 3.2.4** (p. 107): the Bellman operator of `(ℝ^G, 𝕊)` is (3.7),
`(Sq)(x, a) = r(x, a) + β ∑_{x'} max_{a' ∈ Γ(x')} q(x', a') P(x, a, x')`. -/
theorem exercise_3_2_4 (q : M.G → ℝ) (p : M.G) :
    M.qadp.bellman q p = M.r p.1.1 p.1.2 + M.β * ∑ x',
      (M.Γ x').attach.sup' ((M.Γ_nonempty x').attach)
        (fun a => q ⟨(x', a.1), a.2⟩) * M.P p.1.1 p.1.2 x' := by
  obtain ⟨σ, hσ⟩ := M.exists_qgreedy q
  have hlub := M.qadp.isBellmanValue_bellman (M.qadp_regular q)
  have hgr : IsLUB (range fun τ => M.qadp.T τ q) (M.qadp.T σ q) :=
    ⟨by rintro _ ⟨τ, rfl⟩; exact M.exercise_3_2_3 q σ hσ τ, fun w hw => hw ⟨σ, rfl⟩⟩
  rw [hlub.unique hgr]
  simp only [qadp, Sσ]
  congr 2
  refine Finset.sum_congr rfl fun x' _ => ?_
  congr 1
  refine le_antisymm (Finset.le_sup' (fun a : M.Γ x' => q ⟨(x', a.1), a.2⟩)
    (Finset.mem_attach _ ⟨σ.1 x', σ.2 x'⟩)) (Finset.sup'_le _ _ fun a _ => hσ x' a.1 a.2)

/-- **Exercise 3.2.5** (p. 108): each `S_σ` is a contraction of modulus `β` for the supremum
norm on `ℝ^G`. -/
theorem exercise_3_2_5 (σ : M.Policy) : IsSupContraction univ (M.Sσ σ) M.β :=
  fun q _ q' _ c h p => by
    simp only [Sσ, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_nonneg]
    refine mul_le_mul_of_nonneg_left ?_ M.β_nonneg
    exact M.abs_sum_sub_le p.2 (v := fun x' => q (M.pairOf σ x'))
      (w := fun x' => q' (M.pairOf σ x')) fun y => h _

/-- The Q-factor ADP is globally stable. -/
theorem qadp_isGloballyStable : M.qadp.IsGloballyStable := fun σ => by
  have := M.finite_G
  exact globallyStable_of_supContraction M.β_nonneg M.β_lt_one (M.exercise_3_2_5 σ)

/-- **Exercise 3.2.6** (p. 108): the Q-factor ADP satisfies the fundamental optimality
properties, VFI, OPI and HPI all converge, and HPI converges in finitely many steps. -/
theorem exercise_3_2_6 :
    M.qadp.FundamentalOptimality M.qadp_isGloballyStable.wellPosed ∧
      (∃ vstar, M.qadp.IsValueFunction vstar ∧ M.qadp.VFIConverges vstar ∧
        ∀ g, M.qadp.IsSelector g → M.qadp.OPIConverges g vstar ∧
          M.qadp.HPIConverges M.qadp_isGloballyStable.wellPosed g vstar) ∧
      ∀ g, M.qadp.IsSelector g → ∀ v ∈ M.qadp.VU,
        ∃ n, M.qadp.IsValueFunction
          ((M.qadp.howard M.qadp_isGloballyStable.wellPosed g)^[n] v) := by
  have := M.finite_policy
  obtain ⟨h1, h2⟩ := ADP.corollary_3_1_3 M.qadp_regular M.qadp_isGloballyStable (finite_range _)
  exact ⟨h1, h2, (ADP.fundamentalOptimality_of_finite M.qadp_isGloballyStable.isOrderStable
    M.qadp_regular (finite_range _)).2⟩

end FiniteMDP

/-- **The converse in Exercise 3.2.3 fails at unreachable states.** Two states `x ∈ Bool`, two
actions, `β = 1/2`, `r = 0`, and every transition goes to state `false`. With
`q(true, true) = 1` and `q(x, a) = 0` otherwise, the policy choosing `false` everywhere is
`q`-greedy, yet at the state `true` it does not maximize `q(true, ·)`. -/
theorem exercise_3_2_3_converse_fails :
    ∃ (M : FiniteMDP Bool Bool) (q : M.G → ℝ) (σ : M.Policy), M.qadp.IsGreedy q σ ∧
      ∃ x a, ∃ ha : a ∈ M.Γ x, q (M.pairOf σ x) < q ⟨(x, a), ha⟩ := by
  let M : FiniteMDP Bool Bool :=
    { Γ := fun _ => Finset.univ
      Γ_nonempty := fun _ => Finset.univ_nonempty
      r := fun _ _ => 0
      β := 1 / 2
      β_nonneg := by norm_num
      β_lt_one := by norm_num
      P := fun _ _ x' => if x' = false then 1 else 0
      P_nonneg := fun _ _ _ _ => by split_ifs <;> norm_num
      P_sum := fun _ _ _ => by simp }
  let q : M.G → ℝ := fun p => if p.1 = (true, true) then 1 else 0
  let σ : M.Policy := ⟨fun _ => false, fun _ => Finset.mem_univ _⟩
  refine ⟨M, q, σ, fun τ p => ?_, true, true, Finset.mem_univ _, ?_⟩
  · simp [FiniteMDP.qadp, FiniteMDP.Sσ, FiniteMDP.pairOf, M, q, σ]
  · simp [FiniteMDP.pairOf, q, σ]

end SargentStachurski.ApproximationAndLearning

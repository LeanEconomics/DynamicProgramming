/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NPBellman
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Set.Finite.Basic

/-!
# Discrete approximation methods for dynamic programming

Miao, *Economic Dynamics in Discrete Time*, §11.6.1 (pp. 377–380).

The stochastic growth model (11.9) is discretised on a capital grid
`K = {k₁, …, k_{n_k}}` and a Markov chain `(s_i, π_ij)` for `s = ln z`; the
discretised problem (11.10) is a finite Markov decision process with state
`(k_m, s_i)`, action `k' ∈ K`, reward `u(f(k_m, exp s_i) − k')` and transition
`(k', s_j)` with probability `π_ij`. We build this MDP (`GrowthGrid.toMDP`) and
prove, using the Sargent–Stachurski finite-MDP theory copied into `NPBasics`,
`NPMDP`, `NPBellman`:

* (11.11): the Bellman operator `B` of the MDP is the book's operator; it is a
  contraction of modulus `β`, so (11.10) has a unique solution `V = BV`
  (`eq_11_10`, `eq_11_10_unique`);
* value function iteration: `Bⁿ V₀ → V` with `‖V − Vₙ‖ ≤ βⁿ‖V − V₀‖`, and with
  `V₀ = 0` the iterate `Bⁿ 0` is the value of the `n`-period problem solved by
  backward induction (`np_vfi_backward_induction`);
* policy iteration: the policy evaluation system (11.12) has the unique
  solution `V_g = (I − βP_g)⁻¹ r_g`; the improvement step is monotone; both
  stopping rules (`gₙ = gₙ₋₁` or `Vₙ = Vₙ₋₁`) certify optimality; the
  algorithm stops after finitely many steps; and each step is the
  Newton–Kantorovich step for `F(V) = (I − B)V` (Puterman–Brumelle);
* modified policy iteration: `B̂ = T_{g₀}` is a `β`-contraction whose iterates
  converge to the solution of (11.12).

Abstract bounds used for the "truncation" and "projection" remarks:
`np_residual_bound` (`‖v − V‖ ≤ ‖v − Bv‖/(1 − β)`), `np_vfi_aposteriori` and
`np_fixedPt_perturbation`.

Departures: the book maximises over `k' ∈ K` without restricting consumption to
be positive; we follow (11.10) literally, the utility `u` being any real
function (feasibility restrictions can be built into `u`, e.g. a large penalty).
-/

namespace Miao.NumericalMethods.NP

open Finset Matrix Filter Topology Function

/-! ### Abstract contraction bounds -/

/-- Projection residual bound (Miao, p. 381, residual `R = V̂ − BV̂`): if `B` is a contraction of
modulus `β` with fixed point `V`, then `‖v − V‖ ≤ ‖v − Bv‖/(1 − β)` for every `v`. In particular a
zero residual identifies the true value function. -/
theorem np_residual_bound {E : Type*} [NormedAddCommGroup E] {B : E → E} {β : ℝ}
    (hB : IsContractionOn B Set.univ β) {V : E} (hV : IsFixedPt B V) (v : E) :
    ‖v - V‖ ≤ ‖v - B v‖ / (1 - β) := by
  have h1 : 0 < 1 - β := by linarith [hB.lt_one]
  have h2 : ‖B v - V‖ ≤ β * ‖v - V‖ := by
    have := hB.norm_sub_le v (Set.mem_univ _) V (Set.mem_univ _)
    rwa [hV.eq] at this
  have h3 : ‖v - V‖ ≤ ‖v - B v‖ + ‖B v - V‖ := by
    have := norm_add_le (v - B v) (B v - V)
    rwa [sub_add_sub_cancel] at this
  rw [le_div_iff₀ h1]
  nlinarith

/-- Miao, p. 381: the residual `R = v − Bv` vanishes iff `v` is the fixed point `V`. -/
theorem np_residual_zero_iff {E : Type*} [NormedAddCommGroup E] {B : E → E} {β : ℝ}
    (hB : IsContractionOn B Set.univ β) {V : E} (hV : IsFixedPt B V) (v : E) :
    v - B v = 0 ↔ v = V := by
  constructor
  · intro h
    exact hB.fixedPt_unique (Set.mem_univ v) (Set.mem_univ V) (sub_eq_zero.1 h).symm hV
  · rintro rfl
    rw [hV.eq, sub_self]

/-- A posteriori bound for value function iteration: `‖Bv − V‖ ≤ β/(1 − β) ‖Bv − v‖`, which
justifies stopping when successive iterates are close. -/
theorem np_vfi_aposteriori {E : Type*} [NormedAddCommGroup E] {B : E → E} {β : ℝ}
    (hB : IsContractionOn B Set.univ β) {V : E} (hV : IsFixedPt B V) (v : E) :
    ‖B v - V‖ ≤ β / (1 - β) * ‖B v - v‖ := by
  have h := np_residual_bound hB hV (B v)
  have h2 : ‖B v - B (B v)‖ ≤ β * ‖v - B v‖ :=
    hB.norm_sub_le v (Set.mem_univ _) (B v) (Set.mem_univ _)
  have h1 : 0 < 1 - β := by linarith [hB.lt_one]
  rw [norm_sub_rev v] at h2
  calc ‖B v - V‖ ≤ ‖B v - B (B v)‖ / (1 - β) := h
    _ ≤ β * ‖B v - v‖ / (1 - β) := div_le_div_of_nonneg_right h2 h1.le
    _ = β / (1 - β) * ‖B v - v‖ := by ring

/-- Approximation of the Bellman operator (Miao, p. 377: "as long as the truncated state space is
sufficiently large, the truncated problem can approximate the original problem arbitrarily
closely"): if two `β`-contractions are uniformly within `ε`, their fixed points are within
`ε/(1 − β)`. -/
theorem np_fixedPt_perturbation {E : Type*} [NormedAddCommGroup E] {B B' : E → E} {β ε : ℝ}
    (hB : IsContractionOn B Set.univ β) (hB' : IsContractionOn B' Set.univ β)
    {V V' : E} (hV : IsFixedPt B V) (hV' : IsFixedPt B' V') (hε : ∀ v, ‖B v - B' v‖ ≤ ε) :
    ‖V - V'‖ ≤ ε / (1 - β) := by
  have h1 : 0 < 1 - β := by linarith [hB.lt_one]
  have h2 : ‖B' V - B' V'‖ ≤ β * ‖V - V'‖ :=
    hB'.norm_sub_le V (Set.mem_univ _) V' (Set.mem_univ _)
  have h3 : ‖B V - B' V'‖ ≤ ‖B V - B' V‖ + ‖B' V - B' V'‖ := by
    have := norm_add_le (B V - B' V) (B' V - B' V')
    rwa [sub_add_sub_cancel] at this
  have h4 : ‖V - V'‖ = ‖B V - B' V'‖ := by rw [hV.eq, hV'.eq]
  rw [le_div_iff₀ h1]
  nlinarith [hε V]

/-! ### Extra facts on finite MDPs: backward induction and termination of policy iteration -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The `k`-period payoff of the (possibly time-varying) plan `σ₀, σ₁, …` with zero terminal value,
computed by backward induction: `J₀ = 0`, `J_{k+1}(σ) = T_{σ₀} J_k(σ₁, σ₂, …)`. -/
noncomputable def np_horizonValue : ℕ → (ℕ → X → A) → X → ℝ
  | 0, _ => 0
  | k + 1, σ => M.Tσ (σ 0) (np_horizonValue k fun t => σ (t + 1))

/-- A stationary plan's `k`-period payoff is `T_σᵏ 0`. -/
theorem np_horizonValue_const (σ : X → A) (k : ℕ) :
    M.np_horizonValue k (fun _ => σ) = (M.Tσ σ)^[k] 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ← ih]
    rfl

/-- Backward induction: `Tᵏ 0` is the value of the `k`-period problem, i.e. it bounds the payoff of
every feasible plan and is attained by a feasible plan. -/
theorem np_iterate_T_zero_eq_max (k : ℕ) :
    (∀ σ : ℕ → X → A, (∀ t, M.IsFeasible (σ t)) → M.np_horizonValue k σ ≤ M.T^[k] 0) ∧
      ∃ σ : ℕ → X → A, (∀ t, M.IsFeasible (σ t)) ∧ M.np_horizonValue k σ = M.T^[k] 0 := by
  induction k with
  | zero =>
    refine ⟨fun σ _ => le_rfl, fun _ => M.defaultPolicy.1, fun _ => M.defaultPolicy.2, rfl⟩
  | succ k ih =>
    obtain ⟨hle, σ', hσ', heq⟩ := ih
    refine ⟨fun σ hσ => ?_, ?_⟩
    · rw [iterate_succ_apply']
      calc M.np_horizonValue (k + 1) σ
          = M.Tσ (σ 0) (M.np_horizonValue k fun t => σ (t + 1)) := rfl
        _ ≤ M.Tσ (σ 0) (M.T^[k] 0) := M.Tσ_monotone _ (hle _ fun t => hσ (t + 1))
        _ ≤ M.T (M.T^[k] 0) := M.Tσ_le_T ⟨σ 0, hσ 0⟩ _
    · let g := M.greedy (M.T^[k] 0)
      refine ⟨fun t => if t = 0 then g else σ' (t - 1), fun t => ?_, ?_⟩
      · by_cases ht : t = 0
        · simp only [ht, ↓reduceIte]
          exact M.greedy_mem _
        · simp only [ht, ↓reduceIte]
          exact hσ' _
      · have hshift : (fun t => (fun t => if t = 0 then g else σ' (t - 1)) (t + 1)) = σ' := by
          funext t
          simp
        rw [iterate_succ_apply', ← M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy (M.T^[k] 0))]
        change M.Tσ (if (0 : ℕ) = 0 then g else σ' (0 - 1)) (M.np_horizonValue k _) = _
        rw [hshift, heq]
        rfl

/-- Howard policy iteration started at `σ₀`: `σ_{n+1}` is `v_{σₙ}`-greedy. -/
noncomputable def np_hpi (σ0 : X → A) : ℕ → X → A
  | 0 => σ0
  | n + 1 => M.greedy (M.vσ (np_hpi σ0 n))

theorem np_hpi_feasible {σ0 : X → A} (h0 : M.IsFeasible σ0) (n : ℕ) :
    M.IsFeasible (M.np_hpi σ0 n) := by
  cases n with
  | zero => exact h0
  | succ n => exact M.greedy_mem _

/-- Policy iteration is monotone: `v_{σₙ} ≤ v_{σₙ₊₁}`. -/
theorem np_hpi_mono {σ0 : X → A} (h0 : M.IsFeasible σ0) (n : ℕ) :
    M.vσ (M.np_hpi σ0 n) ≤ M.vσ (M.np_hpi σ0 (n + 1)) :=
  M.vσ_le_vσ_of_isGreedy (M.np_hpi_feasible h0 n) (M.isGreedy_greedy _)

/-- Policy iteration stops after finitely many steps: some `n` has `v_{σₙ₊₁} = v_{σₙ}` (the
values increase and there are finitely many policies). -/
theorem np_hpi_terminates {σ0 : X → A} (h0 : M.IsFeasible σ0) :
    ∃ n, M.vσ (M.np_hpi σ0 (n + 1)) = M.vσ (M.np_hpi σ0 n) := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hsm : StrictMono fun n => M.vσ (M.np_hpi σ0 n) :=
    strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne (M.np_hpi_mono h0 n) (Ne.symm (hcon n))
  have hfin : (Set.range fun n => M.vσ (M.np_hpi σ0 n)).Finite :=
    (Set.finite_range fun p : M.Policy => M.vσ p.1).subset (by
      rintro _ ⟨n, rfl⟩
      exact ⟨⟨_, M.np_hpi_feasible h0 n⟩, rfl⟩)
  exact Set.infinite_range_of_injective hsm.injective hfin

end MDP

/-! ### The discretised stochastic growth model (11.10) -/

/-- The data of the discretised growth model (11.10), Miao p. 378: a capital grid `k_m`, a
Markov chain `(s_i, π_ij)` for `s = ln z`, utility `u`, technology `f(k, z)` and `β ∈ (0, 1)`. -/
structure GrowthGrid (nk nz : ℕ) where
  kgrid : Fin nk → ℝ
  sgrid : Fin nz → ℝ
  pz : Matrix (Fin nz) (Fin nz) ℝ
  pz_markov : IsMarkov pz
  u : ℝ → ℝ
  f : ℝ → ℝ → ℝ
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1

namespace GrowthGrid

variable {nk nz : ℕ} [NeZero nk] (G : GrowthGrid nk nz)

/-- The reward `u(f(k_m, exp s_i) − k')` of choosing grid point `k'` in state `(k_m, s_i)`. -/
noncomputable def reward (x : Fin nk × Fin nz) (a : Fin nk) : ℝ :=
  G.u (G.f (G.kgrid x.1) (Real.exp (G.sgrid x.2)) - G.kgrid a)

/-- The transition: next state `(k', s_j)` with probability `π_ij`. -/
def trans (x : Fin nk × Fin nz) (a : Fin nk) (y : Fin nk × Fin nz) : ℝ :=
  if y.1 = a then G.pz x.2 y.2 else 0

omit [NeZero nk] in
theorem trans_rowsum (x : Fin nk × Fin nz) (a : Fin nk) : ∑ y, G.trans x a y = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [trans]
  rw [Finset.sum_comm]
  simp [G.pz_markov.rowsum]

omit [NeZero nk] in
theorem trans_nonneg (x : Fin nk × Fin nz) (a : Fin nk) (y : Fin nk × Fin nz) :
    0 ≤ G.trans x a y := by
  unfold trans
  split_ifs
  · exact G.pz_markov.nonneg _ _
  · exact le_rfl

/-- The discretised dynamic programming problem (11.10) as a finite MDP on `K × S`. -/
noncomputable def toMDP : MDP (Fin nk × Fin nz) (Fin nk) where
  Γ := fun _ => Finset.univ
  Γ_nonempty := fun _ => Finset.univ_nonempty
  β := G.β
  β_pos := G.β_pos
  β_lt_one := G.β_lt_one
  r := G.reward
  P := G.trans
  P_nonneg := G.trans_nonneg
  P_rowsum := G.trans_rowsum

theorem toMDP_β : G.toMDP.β = G.β := rfl

/-- Every policy `g : K × S → K` is feasible. -/
theorem isFeasible (g : Fin nk × Fin nz → Fin nk) : G.toMDP.IsFeasible g :=
  fun _ => Finset.mem_univ _

/-- The action value of (11.10)–(11.11): the continuation is `∑_j π_ij v(k', s_j)`. -/
theorem B_apply (v : Fin nk × Fin nz → ℝ) (m : Fin nk) (i : Fin nz) (a : Fin nk) :
    G.toMDP.B v (m, i) a =
      G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid a) +
        G.β * ∑ j, G.pz i j * v (a, j) := by
  have h : ∑ y, v y * G.trans (m, i) a y = ∑ j, G.pz i j * v (a, j) := by
    rw [Fintype.sum_prod_type]
    simp only [trans]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  change G.reward (m, i) a + G.β * ∑ y, v y * G.trans (m, i) a y = _
  rw [h]
  rfl

/-- **(11.11)** (Miao, p. 378): the Bellman operator of the discretised problem is
`Bv(k_m, s_i) = max_{k' ∈ K} {u(f(k_m, exp s_i) − k') + β ∑_j π_ij v(k', s_j)}`. -/
theorem eq_11_11 (v : Fin nk × Fin nz → ℝ) (m : Fin nk) (i : Fin nz) :
    G.toMDP.T v (m, i) =
      Finset.univ.sup' Finset.univ_nonempty fun a : Fin nk =>
        G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid a) +
          G.β * ∑ j, G.pz i j * v (a, j) := by
  change Finset.univ.sup' _ (G.toMDP.B v (m, i)) = _
  congr 1
  funext a
  exact G.B_apply v m i a

/-- Miao, p. 378: the Bellman operator (11.11) is a contraction of modulus `β` in the supremum
norm ("the contraction mapping theorem ensures that there is a unique fixed point"). -/
theorem np_bellman_contraction : IsContractionOn G.toMDP.T Set.univ G.β :=
  G.toMDP.isContractionOn_T

variable [DecidableEq (Fin nk × Fin nz)]

/-- **(11.10)** (Miao, p. 378): the value function `V = v*` of the discretised problem satisfies
`V(k_m, s_i) = max_{k' ∈ K} {u(f(k_m, exp s_i) − k') + β ∑_j π_ij V(k', s_j)}`. -/
theorem eq_11_10 (m : Fin nk) (i : Fin nz) :
    G.toMDP.vstar (m, i) =
      Finset.univ.sup' Finset.univ_nonempty fun a : Fin nk =>
        G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid a) +
          G.β * ∑ j, G.pz i j * G.toMDP.vstar (a, j) := by
  rw [← eq_11_11]
  exact (congrFun G.toMDP.isFixedPt_T_vstar.eq (m, i)).symm

/-- (11.10), uniqueness (Miao, p. 378): any solution of (11.10) is `v*`. -/
theorem eq_11_10_unique {V : Fin nk × Fin nz → ℝ}
    (hV : ∀ m i, V (m, i) =
      Finset.univ.sup' Finset.univ_nonempty fun a : Fin nk =>
        G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid a) +
          G.β * ∑ j, G.pz i j * V (a, j)) :
    V = G.toMDP.vstar := by
  refine G.toMDP.eq_vstar_of_isFixedPt ?_
  funext x
  rw [eq_11_11, hV x.1 x.2]

/-- Value function iteration (Miao, p. 378): `Vₙ = Bⁿ V₀ → V` for any initial guess. -/
theorem np_vfi_tendsto (V0 : Fin nk × Fin nz → ℝ) :
    Tendsto (fun n : ℕ => G.toMDP.T^[n] V0) atTop (𝓝 G.toMDP.vstar) :=
  G.toMDP.tendsto_iterate_T V0

/-- Value function iteration converges at a geometric rate (Miao, p. 378):
`‖Vₙ − V‖ ≤ βⁿ ‖V₀ − V‖`. -/
theorem np_vfi_geometric (V0 : Fin nk × Fin nz → ℝ) (n : ℕ) :
    ‖G.toMDP.T^[n] V0 - G.toMDP.vstar‖ ≤ G.β ^ n * ‖V0 - G.toMDP.vstar‖ :=
  G.toMDP.norm_iterate_T_sub_vstar_le V0 n

omit [DecidableEq (Fin nk × Fin nz)] in
/-- Miao, p. 378: with `V₀ = 0`, value function iteration is backward induction on the
approximate finite-horizon problem: `Bⁿ 0` bounds the `n`-period payoff of every plan and is
attained by a plan. -/
theorem np_vfi_backward_induction (n : ℕ) :
    (∀ σ : ℕ → Fin nk × Fin nz → Fin nk, G.toMDP.np_horizonValue n σ ≤ G.toMDP.T^[n] 0) ∧
      ∃ σ : ℕ → Fin nk × Fin nz → Fin nk, G.toMDP.np_horizonValue n σ = G.toMDP.T^[n] 0 := by
  obtain ⟨h1, σ, -, h2⟩ := G.toMDP.np_iterate_T_zero_eq_max n
  exact ⟨fun σ => h1 σ fun t => G.isFeasible (σ t), σ, h2⟩

omit [DecidableEq (Fin nk × Fin nz)] in
/-- **(11.12)** (Miao, p. 379), policy evaluation: the value `V_g` of a stationary rule `g`
solves `V(k_m, s_i) = u(f(k_m, exp s_i) − g(k_m, s_i)) + β ∑_j π_ij V(g(k_m, s_i), s_j)`. -/
theorem eq_11_12 (g : Fin nk × Fin nz → Fin nk) (m : Fin nk) (i : Fin nz) :
    G.toMDP.vσ g (m, i) =
      G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid (g (m, i))) +
        G.β * ∑ j, G.pz i j * G.toMDP.vσ g (g (m, i), j) := by
  rw [← G.B_apply]
  exact (congrFun (G.toMDP.isFixedPt_vσ g).eq (m, i)).symm

omit [DecidableEq (Fin nk × Fin nz)] in
/-- (11.12), uniqueness: the linear system (11.12) has exactly one solution, `V_g`. -/
theorem eq_11_12_unique (g : Fin nk × Fin nz → Fin nk) {V : Fin nk × Fin nz → ℝ}
    (hV : ∀ m i, V (m, i) =
      G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid (g (m, i))) +
        G.β * ∑ j, G.pz i j * V (g (m, i), j)) :
    V = G.toMDP.vσ g := by
  refine G.toMDP.eq_vσ_of_isFixedPt g ?_
  funext x
  change G.toMDP.B V x (g x) = V x
  rw [G.B_apply, hV x.1 x.2]

/-- (11.12) solved as a linear system: `V_g = (I − βP_g)⁻¹ r_g`. -/
theorem eq_11_12_inv (g : Fin nk × Fin nz → Fin nk) :
    G.toMDP.vσ g = (1 - G.β • G.toMDP.Pσ g)⁻¹ *ᵥ G.toMDP.rσ g :=
  G.toMDP.vσ_eq_inv g

omit [DecidableEq (Fin nk × Fin nz)] in
/-- Policy improvement (Miao, p. 379): if `g₁` is greedy with respect to `V_{g₀}` (the arg max
step), then `V_{g₀} ≤ V_{g₁}`. -/
theorem np_pfi_improvement (g0 : Fin nk × Fin nz → Fin nk) :
    G.toMDP.vσ g0 ≤ G.toMDP.vσ (G.toMDP.greedy (G.toMDP.vσ g0)) :=
  G.toMDP.vσ_le_vσ_of_isGreedy (G.isFeasible g0) (G.toMDP.isGreedy_greedy _)

/-- Miao, p. 379, the stopping rule `gₙ = gₙ₋₁`: if `g` is greedy with respect to its own value
`V_g`, then `V_g` satisfies the Bellman equation (11.10), so `V_g = v*` and `g` is optimal. -/
theorem np_pfi_stop_policy {g : Fin nk × Fin nz → Fin nk}
    (hg : G.toMDP.IsGreedy (G.toMDP.vσ g) g) :
    G.toMDP.vσ g = G.toMDP.vstar ∧ G.toMDP.IsOptimal g :=
  ⟨(G.toMDP.isOptimal_of_hpi_fixed hg rfl).2, G.toMDP.isOptimal_of_hpi_fixed hg rfl⟩

/-- Miao, p. 379, the alternative stopping rule `Vₙ = Vₙ₋₁`: if `g'` is greedy with respect to
`V_g` and `V_{g'} = V_g`, then `g'` is optimal. -/
theorem np_pfi_stop_value {g g' : Fin nk × Fin nz → Fin nk}
    (hg' : G.toMDP.IsGreedy (G.toMDP.vσ g) g') (heq : G.toMDP.vσ g' = G.toMDP.vσ g) :
    G.toMDP.IsOptimal g' :=
  G.toMDP.isOptimal_of_hpi_fixed hg' heq

/-- Optimality (Miao, p. 379, "it is optimal"): the value `v*` dominates the value of every
stationary rule. -/
theorem np_vstar_ge (g : Fin nk × Fin nz → Fin nk) : G.toMDP.vσ g ≤ G.toMDP.vstar :=
  G.toMDP.vσ_le_vstar ⟨g, G.isFeasible g⟩

/-- Policy iteration terminates (Miao, p. 379, "until the first iteration `n` such that
`gₙ = gₙ₋₁` (or alternatively `Vₙ = Vₙ₋₁`)"): from any initial rule there is an `n` at which the
value stops changing, and the rule reached is optimal. -/
theorem np_pfi_terminates (g0 : Fin nk × Fin nz → Fin nk) :
    ∃ n, G.toMDP.vσ (G.toMDP.np_hpi g0 (n + 1)) = G.toMDP.vσ (G.toMDP.np_hpi g0 n) ∧
      G.toMDP.IsOptimal (G.toMDP.np_hpi g0 (n + 1)) := by
  obtain ⟨n, hn⟩ := G.toMDP.np_hpi_terminates (G.isFeasible g0)
  exact ⟨n, hn, G.toMDP.isOptimal_of_hpi_fixed (G.toMDP.isGreedy_greedy _) hn⟩

/-- Puterman–Brumelle (Miao, p. 379): policy iteration is the Newton–Kantorovich method for
`F(V) = (I − B)V`. If `g` is `V`-greedy, the next policy value is the Newton step with the
Jacobian `I − βP_g` of `F` along `g`: `V_g = V − (I − βP_g)⁻¹ (V − BV)`. -/
theorem np_pfi_newton {V : Fin nk × Fin nz → ℝ} {g : Fin nk × Fin nz → Fin nk}
    (hg : G.toMDP.IsGreedy V g) :
    G.toMDP.vσ g = V - (1 - G.β • G.toMDP.Pσ g)⁻¹ *ᵥ (V - G.toMDP.T V) := by
  rw [← toMDP_β]
  have hunit := G.toMDP.isUnit_one_sub_smul_Pσ g
  have hdet : IsUnit (1 - G.toMDP.β • G.toMDP.Pσ g).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 hunit
  have hV : V = (1 - G.toMDP.β • G.toMDP.Pσ g)⁻¹ *ᵥ ((1 - G.toMDP.β • G.toMDP.Pσ g) *ᵥ V) := by
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, one_mulVec]
  have key : (1 - G.toMDP.β • G.toMDP.Pσ g) *ᵥ V - (V - G.toMDP.T V) =
      G.toMDP.T V - G.toMDP.β • (G.toMDP.Pσ g *ᵥ V) := by
    rw [sub_mulVec, one_mulVec, smul_mulVec]
    abel
  rw [← G.toMDP.newton_step_eq_vσ hg, ← key, mulVec_sub, ← hV]

/-- Projection on the value function (Miao, p. 381): for any approximation `V̂` of the solution of
(11.10), `‖V̂ − V‖ ≤ ‖R‖/(1 − β)` with the residual `R = V̂ − BV̂`; a zero residual gives
`V̂ = V`. -/
theorem np_value_projection (Vh : Fin nk × Fin nz → ℝ) :
    ‖Vh - G.toMDP.vstar‖ ≤ ‖Vh - G.toMDP.T Vh‖ / (1 - G.β) ∧
      (Vh - G.toMDP.T Vh = 0 ↔ Vh = G.toMDP.vstar) :=
  ⟨np_residual_bound G.np_bellman_contraction G.toMDP.isFixedPt_T_vstar Vh,
    np_residual_zero_iff G.np_bellman_contraction G.toMDP.isFixedPt_T_vstar Vh⟩

omit [DecidableEq (Fin nk × Fin nz)] in
/-- Modified policy iteration (Miao, p. 379): the operator `B̂ V = r_{g₀} + βP_{g₀} V` is a
contraction of modulus `β` whose unique fixed point is the solution `V_{g₀}` of (11.12), and its
iterates converge to it. -/
theorem np_mpi (g0 : Fin nk × Fin nz → Fin nk) :
    IsContractionOn (G.toMDP.Tσ g0) Set.univ G.β ∧ IsFixedPt (G.toMDP.Tσ g0) (G.toMDP.vσ g0) ∧
      ∀ V0, Tendsto (fun n : ℕ => (G.toMDP.Tσ g0)^[n] V0) atTop (𝓝 (G.toMDP.vσ g0)) :=
  ⟨G.toMDP.isContractionOn_Tσ g0, G.toMDP.isFixedPt_vσ g0, G.toMDP.tendsto_iterate_Tσ g0⟩

end GrowthGrid

/-- A concrete discretised growth model (one grid point, one shock state, `β = 1/2`), showing the
data of `GrowthGrid` can be met. -/
noncomputable def np_growthGridExample : GrowthGrid 1 1 where
  kgrid := fun _ => 1
  sgrid := fun _ => 0
  pz := fun _ _ => 1
  pz_markov := ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
  u := id
  f := fun k z => z * k
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num

/-- The example's value function solves (11.10): `V = 0 + (1/2)V`, so `V = 0`. -/
theorem np_growthGridExample_vstar :
    np_growthGridExample.toMDP.vstar (0, 0) = 0 := by
  have h := GrowthGrid.eq_11_10 np_growthGridExample 0 0
  simp only [Finset.univ_unique, Finset.sup'_singleton, Fin.default_eq_zero,
    Finset.sum_singleton] at h
  generalize np_growthGridExample.toMDP.vstar (0, 0) = V at h ⊢
  simp [np_growthGridExample] at h
  linarith

end Miao.NumericalMethods.NP

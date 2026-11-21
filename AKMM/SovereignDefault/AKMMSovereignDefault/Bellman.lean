/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.Contracting
import AKMMSovereignDefault.BondPrice

/-!
# The sovereign's Bellman equations (24.9)–(24.11)

AKMM, §24.4.2, (24.9)–(24.11), pp. 743–744, and Appendix 24.A.1, (24.A.1), p. 897; Appendix
24.A.3, p. 904 (default regions).

For a given bond price function `q`, the sovereign's problem on a finite income grid (Markov
matrix `P`) and a finite debt grid (debt values `bond`, a zero-debt point `b₀`) is a recursive
decision process in the sense of Sargent and Stachurski (`RDP`, imported): states
`(y, b, excluded)`, actions `(b′, default)`. In good standing the sovereign either repays and
picks `b′`, with consumption `Y − δB + q(B′, Y)[B′ − (1 − δ)B]`, or defaults; while excluded
it consumes `Y − φ(Y)` and regains access with zero debt with probability `ψ`.

* The RDP satisfies Blackwell's conditions with modulus `β`, so its Bellman operator is a
  contraction (`sd_isContracting`); value function iteration (24.A.1) converges from any initial
  guess (`eq_24_A_1`).
* Its Bellman operator is (24.9) in good standing and (24.10) in exclusion (`sd_T_good`,
  `sd_T_excluded`); hence **(24.9)–(24.11) have exactly one solution `(V, V^D)`** with `V^R`
  given by (24.11) (`eq_24_9_to_24_11`).
* `V^R` is nonincreasing in debt for every continuation `V` (`sd_VR_antitone`), `V^D` does not
  depend on debt, so `V` is nonincreasing in debt (`sd_V_antitone`) and the default set
  `{Y : V^D(Y) > V^R(B, Y)}` grows with debt (`sd_default_set_mono`).

Sargent and Stachurski's own optimal-default RDP (Exercise 8.2.7) has one-period debt and a
constant price, so it is not reused; we build the book's RDP from their `RDP` structure and use
their Blackwell, contraction and global-stability theorems. Departure D4: finite grids.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

/-- The primitives of the quantitative model (§24.4.1, p. 742–743) on finite grids: income
levels `inc` with Markov matrix `P`, debt levels `bond` with a zero-debt point `b₀`, utility
`u`, default cost `φ(Y)`, discount factor `β ∈ [0, 1)`, re-entry probability `ψ ∈ [0, 1]` and
coupon decay `δ ∈ [0, 1]`. -/
structure SDModel (Y Bd : Type*) [Fintype Y] [Fintype Bd] where
  /-- Income levels. -/
  inc : Y → ℝ
  /-- The income transition matrix. -/
  P : Matrix Y Y ℝ
  /-- `P` is a Markov matrix. -/
  markov : IsMarkov P
  /-- Debt levels on the grid. -/
  bond : Bd → ℝ
  /-- The zero-debt grid point. -/
  b₀ : Bd
  /-- `B(b₀) = 0`. -/
  bond_b₀ : bond b₀ = 0
  /-- Utility. -/
  u : ℝ → ℝ
  /-- The income cost of default. -/
  φ : ℝ → ℝ
  /-- The discount factor. -/
  β : ℝ
  /-- `β ≥ 0`. -/
  β_nonneg : 0 ≤ β
  /-- `β < 1`. -/
  β_lt_one : β < 1
  /-- The re-entry probability. -/
  ψ : ℝ
  /-- `ψ ≥ 0`. -/
  ψ_nonneg : 0 ≤ ψ
  /-- `ψ ≤ 1`. -/
  ψ_le_one : ψ ≤ 1
  /-- The coupon decay rate. -/
  δ : ℝ
  /-- `δ ≥ 0`. -/
  δ_nonneg : 0 ≤ δ
  /-- `δ ≤ 1`. -/
  δ_le_one : δ ≤ 1

variable {Y Bd : Type*} [Fintype Y] [Fintype Bd]

namespace SDModel

variable (M : SDModel Y Bd)

/-- AKMM, (24.11), p. 744: consumption under repayment,
`C = Y − δB + q(B′, Y)[B′ − (1 − δ)B]`. -/
def cons (q : Bd → Y → ℝ) (y : Y) (b b' : Bd) : ℝ :=
  M.inc y - M.δ * M.bond b + q b' y * (M.bond b' - (1 - M.δ) * M.bond b)

/-- AKMM, (24.10), p. 744: the right-hand side of the default value,
`u(Y − φ(Y)) + βE[ψV(0, Y′) + (1 − ψ)V^D(Y′)]`, given `V` and `V^D`. -/
def defaultValue (V : Bd → Y → ℝ) (VD : Y → ℝ) (y : Y) : ℝ :=
  M.u (M.inc y - M.φ (M.inc y)) + M.β * ∑ j, M.P y j * (M.ψ * V M.b₀ j + (1 - M.ψ) * VD j)

/-- AKMM, (24.11), p. 744: the value of repaying,
`V^R(B, Y) = max_{B′} {u(C) + βE V(B′, Y′)}`, given the continuation value `V`. -/
noncomputable def repayValue (q : Bd → Y → ℝ) (V : Bd → Y → ℝ) (b : Bd) (y : Y) : ℝ :=
  univ.sup' ⟨M.b₀, mem_univ _⟩ fun b' => M.u (M.cons q y b b') + M.β * ∑ j, M.P y j * V b' j

/-- The sovereign's RDP for a given price `q`: states `(y, b, excluded)`, actions
`(b′, default)`. -/
noncomputable def rdp (q : Bd → Y → ℝ) : RDP (Y × Bd × Bool) (Bd × Bool) where
  Γ := fun s => bif s.2.2 then {(M.b₀, true)} else univ
  Γ_nonempty := fun s => ⟨(M.b₀, true), by rcases s with ⟨_, _, d⟩; cases d <;> simp⟩
  V := Set.univ
  B := fun s a v => bif a.2 then
      M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) s.1
    else M.u (M.cons q s.1 s.2.1 a.1) + M.β * ∑ j, M.P s.1 j * v (j, a.1, false)
  mono := fun s a _ v _ w _ hvw => by
    rcases a with ⟨b', d⟩
    cases d
    · refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hvw _) (M.markov.nonneg _ _)) M.β_nonneg)
    · refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (M.markov.nonneg _ _)) M.β_nonneg)
      · exact mul_le_mul_of_nonneg_left (hvw _) M.ψ_nonneg
      · exact mul_le_mul_of_nonneg_left (hvw _) (by linarith [M.ψ_le_one])
  consistent := fun _ _ _ _ => Set.mem_univ _

/-- The sovereign's RDP satisfies Blackwell's conditions with modulus `β`, so it is
contracting (Sargent–Stachurski, Exercise 8.2.3). -/
theorem sd_isContracting (q : Bd → Y → ℝ) : (M.rdp q).IsContracting M.β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨M.β_nonneg, M.β_lt_one,
    fun _ _ _ _ => Set.mem_univ _, fun s a _ v _ c _ => le_of_eq ?_⟩
  have hs : ∀ (f : Y → ℝ), ∑ j, M.P s.1 j * (f j + c) = ∑ j, M.P s.1 j * f j + c := fun f => by
    simp only [mul_add, sum_add_distrib, ← sum_mul, M.markov.rowsum, one_mul]
  rcases a with ⟨b', d⟩
  cases d
  · change M.u _ + M.β * ∑ j, M.P s.1 j * (v (j, b', false) + c) =
      M.u _ + M.β * ∑ j, M.P s.1 j * v (j, b', false) + M.β * c
    rw [hs]
    ring
  · change M.u _ + M.β * ∑ j, M.P s.1 j * (M.ψ * (v (j, M.b₀, false) + c) +
        (1 - M.ψ) * (v (j, M.b₀, true) + c)) =
      M.u _ + M.β * ∑ j, M.P s.1 j * (M.ψ * v (j, M.b₀, false) +
        (1 - M.ψ) * v (j, M.b₀, true)) + M.β * c
    have : ∀ j, M.ψ * (v (j, M.b₀, false) + c) + (1 - M.ψ) * (v (j, M.b₀, true) + c) =
        (M.ψ * v (j, M.b₀, false) + (1 - M.ψ) * v (j, M.b₀, true)) + c := fun j => by ring
    simp only [this]
    rw [hs]
    ring

/-- The Bellman operator in good standing is (24.9):
`(Tv)(y, b, 0) = max{V^D(y), V^R(b, y)}`. -/
theorem sd_T_good (q : Bd → Y → ℝ) (v : Y × Bd × Bool → ℝ) (y : Y) (b : Bd) :
    (M.rdp q).T v (y, b, false) = max
      (M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) y)
      (M.repayValue q (fun b j => v (j, b, false)) b y) := by
  change univ.sup' _ (fun a : Bd × Bool => bif a.2 then
      M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) y
    else M.u (M.cons q y b a.1) + M.β * ∑ j, M.P y j * v (j, a.1, false)) = _
  apply le_antisymm
  · refine sup'_le _ _ fun a _ => ?_
    rcases a with ⟨b', d⟩
    cases d
    · exact (le_sup' (fun b' => M.u (M.cons q y b b') + M.β * ∑ j, M.P y j * v (j, b', false))
        (mem_univ b')).trans (le_max_right _ _)
    · exact le_max_left _ _
  · refine max_le (le_sup'_of_le _ (mem_univ (M.b₀, true)) le_rfl) ?_
    exact sup'_le _ _ fun b' _ => le_sup'_of_le _ (mem_univ (b', false)) le_rfl

/-- The Bellman operator in exclusion is (24.10): `(Tv)(y, b, 1) = V^D(y)`. -/
theorem sd_T_excluded (q : Bd → Y → ℝ) (v : Y × Bd × Bool → ℝ) (y : Y) (b : Bd) :
    (M.rdp q).T v (y, b, true) =
      M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) y := by
  change ({(M.b₀, true)} : Finset (Bd × Bool)).sup' _ _ = _
  rw [sup'_singleton]
  rfl

/-- **AKMM, (24.A.1)**, p. 897: for a given price, value function iteration converges from any
initial guess to the unique fixed point of the Bellman operator (global stability). -/
theorem eq_24_A_1 (q : Bd → Y → ℝ) : GloballyStable (M.rdp q).T :=
  ((M.sd_isContracting q).isContractionOn_T).globallyStable_univ

/-- **AKMM, (24.9)–(24.11)**, pp. 743–744: for any bond price function `q`, there is exactly one
pair `(V, V^D)` such that `V(B, Y) = max{V^D(Y), V^R(B, Y)}` (24.9) and
`V^D(Y) = u(Y − φ(Y)) + βE[ψV(0, Y′) + (1 − ψ)V^D(Y′)]` (24.10), where
`V^R(B, Y) = max_{B′} {u(C) + βE V(B′, Y′)}` (24.11). -/
theorem eq_24_9_to_24_11 (q : Bd → Y → ℝ) :
    ∃! W : (Bd → Y → ℝ) × (Y → ℝ),
      (∀ b y, W.1 b y = max (W.2 y) (M.repayValue q W.1 b y)) ∧
        ∀ y, W.2 y = M.defaultValue W.1 W.2 y := by
  obtain ⟨v, hv, huniq, -⟩ := M.eq_24_A_1 q
  have hgood : ∀ y b, v (y, b, false) = max
      (M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) y)
      (M.repayValue q (fun b j => v (j, b, false)) b y) := fun y b => by
    rw [← M.sd_T_good q v y b, hv.eq]
  have hexc : ∀ y b, v (y, b, true) =
      M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) y := fun y b => by
    rw [← M.sd_T_excluded q v y b, hv.eq]
  refine ⟨((fun b y => v (y, b, false)), (fun y => v (y, M.b₀, true))), ⟨fun b y => ?_,
    fun y => hexc y M.b₀⟩, ?_⟩
  · simp only
    rw [hgood y b, ← hexc y M.b₀]
  · rintro ⟨V, VD⟩ ⟨h9, h10⟩
    set w : Y × Bd × Bool → ℝ := fun s => bif s.2.2 then VD s.1 else V s.2.1 s.1 with hw
    have hfix : Function.IsFixedPt (M.rdp q).T w := by
      funext s
      rcases s with ⟨y, b, d⟩
      cases d
      · rw [M.sd_T_good]
        change max (M.defaultValue V VD y) (M.repayValue q V b y) = V b y
        rw [← h10 y]
        exact (h9 b y).symm
      · rw [M.sd_T_excluded]
        change M.defaultValue V VD y = VD y
        exact (h10 y).symm
    have hwv := huniq w hfix
    have h1 : V = fun b y => v (y, b, false) := by
      funext b y; exact congrFun hwv (y, b, false)
    have h2 : VD = fun y => v (y, M.b₀, true) := by
      funext y; exact congrFun hwv (y, M.b₀, true)
    rw [h1, h2]

/-- AKMM, p. 745 and App. 24.A.3: **`V^R` is nonincreasing in debt.** For any continuation `V`,
if `u` is nondecreasing and `q ≥ 0`, more debt lowers the value of repaying:
`B(b) ≤ B(b′) ⇒ V^R(b′, Y) ≤ V^R(b, Y)`. -/
theorem sd_VR_antitone (hu : Monotone M.u) {q : Bd → Y → ℝ} (hq : ∀ b y, 0 ≤ q b y)
    (V : Bd → Y → ℝ) {b b' : Bd} (hbb : M.bond b ≤ M.bond b') (y : Y) :
    M.repayValue q V b' y ≤ M.repayValue q V b y := by
  refine sup'_le _ _ fun c _ => le_sup'_of_le _ (mem_univ c) ?_
  refine add_le_add (hu ?_) le_rfl
  unfold cons
  have hk : 0 ≤ M.δ + q c y * (1 - M.δ) :=
    add_nonneg M.δ_nonneg (mul_nonneg (hq c y) (by linarith [M.δ_le_one]))
  nlinarith [mul_le_mul_of_nonneg_left hbb hk]

/-- AKMM, p. 744: with `V^D` independent of debt, **`V` is nonincreasing in debt**: at the
solution of (24.9)–(24.11), `B(b) ≤ B(b′) ⇒ V(b′, Y) ≤ V(b, Y)`. -/
theorem sd_V_antitone (hu : Monotone M.u) {q : Bd → Y → ℝ} (hq : ∀ b y, 0 ≤ q b y)
    {V : Bd → Y → ℝ} {VD : Y → ℝ} (h9 : ∀ b y, V b y = max (VD y) (M.repayValue q V b y))
    {b b' : Bd} (hbb : M.bond b ≤ M.bond b') (y : Y) : V b' y ≤ V b y := by
  rw [h9 b' y, h9 b y]
  exact max_le_max le_rfl (M.sd_VR_antitone hu hq V hbb y)

/-- AKMM, p. 744 and App. 24.A.3, p. 904: **the default set grows with debt.** The sovereign
defaults when `V^D(Y) > V^R(B, Y)` (ties repaid); if it defaults with debt `b` it defaults with
any larger debt `b′`. -/
theorem sd_default_set_mono (hu : Monotone M.u) {q : Bd → Y → ℝ} (hq : ∀ b y, 0 ≤ q b y)
    (V : Bd → Y → ℝ) (VD : Y → ℝ) {b b' : Bd} (hbb : M.bond b ≤ M.bond b') :
    {y | M.repayValue q V b y < VD y} ⊆ {y | M.repayValue q V b' y < VD y} :=
  fun y hy => lt_of_le_of_lt (M.sd_VR_antitone hu hq V hbb y) hy

/-- AKMM, p. 744: the repayment set `{Y : V^R(B, Y) ≥ V^D(Y)}` shrinks with debt. -/
theorem sd_repay_set_antitone (hu : Monotone M.u) {q : Bd → Y → ℝ} (hq : ∀ b y, 0 ≤ q b y)
    (V : Bd → Y → ℝ) (VD : Y → ℝ) {b b' : Bd} (hbb : M.bond b ≤ M.bond b') :
    {y | VD y ≤ M.repayValue q V b' y} ⊆ {y | VD y ≤ M.repayValue q V b y} :=
  fun y hy => le_trans hy (M.sd_VR_antitone hu hq V hbb y)

end SDModel

/-- A concrete model: one income level, one debt level (`B = 0`), `u = id`, no default cost,
`β = 1/2`, `ψ = 1/2`, `δ = 1`. -/
noncomputable def sd_example : SDModel Unit Unit where
  inc := fun _ => 1
  P := fun _ _ => 1
  markov := ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
  bond := fun _ => 0
  b₀ := ()
  bond_b₀ := rfl
  u := id
  φ := fun _ => 0
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  ψ := 1 / 2
  ψ_nonneg := by norm_num
  ψ_le_one := by norm_num
  δ := 1
  δ_nonneg := zero_le_one
  δ_le_one := le_rfl

/-- In the example, with any price, `V = V^D = 2` solves (24.9)–(24.11). -/
theorem sd_example_solution (q : Unit → Unit → ℝ) :
    (∀ b y, (fun _ _ => (2 : ℝ)) b y =
        max ((fun _ => (2 : ℝ)) y) (sd_example.repayValue q (fun _ _ => 2) b y)) ∧
      ∀ y, (fun _ => (2 : ℝ)) y = sd_example.defaultValue (fun _ _ => 2) (fun _ => 2) y := by
  refine ⟨fun b y => ?_, fun y => ?_⟩
  · simp only [SDModel.repayValue, SDModel.cons, sd_example, univ_unique, sup'_singleton,
      sum_singleton, id]
    norm_num
  · simp only [SDModel.defaultValue, sd_example, univ_unique, sum_singleton, id]
    norm_num

end AKMM.SovereignDefault

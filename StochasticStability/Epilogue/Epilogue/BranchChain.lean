/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.MM1Spectrum

/-!
# A V-uniformly ergodic chain that is not L²-geometrically ergodic (Prop 20.1.2 (ii))

Meyn and Tweedie, Proposition 20.1.2 (ii), p. 515: *there is a Markov chain that is
`V`-uniformly ergodic but not geometrically ergodic in `L²(π)`*. The book cites Häggström's
example [150] of a `V`-uniformly ergodic chain and an `f ∈ L²(π)` with infinite asymptotic
variance. We prove the stated property directly with a simpler chain, the **branch chain** on
`ℕ × ℕ`. From the hub `(0, 0)` it jumps to `(k, k)` with probability `2^{−(k+1)}` (`k = 0`
staying at the hub), then walks deterministically down branch `k`,
`(k, j) → (k, j − 1) → ⋯ → (k, 1) → hub`.

* `branchKernel`, `isMarkovKernel_branchKernel`, `branchKernel_hub`, `branchKernel_of_ne`,
  `branchKernel_singleton`, `branchJump_singleton`.
* `branchPi`, `isProbabilityMeasure_branchPi`, `isInvariant_branchPi`: the invariant law
  `π(hub) = 1/2`, `π(i, j) = 2^{−(i+2)}` for `1 ≤ j ≤ i`. It is uniform along each branch.
* `branch_isPhiIrreducible`, `branch_reaches_hub`, `branch_driftV4` ((V4) for
  `V(i, j) = (3/2)ʲ`), `branchC_isSmallSet`, `branch_vUniform`: the chain is `V`-uniformly
  ergodic at a geometric rate (Theorem 16.1.2).
* `branchKernel_pow_branch`, `branchPi_branchSet`, `branchPi_branchSet_le`: along a branch,
  `Pⁿ((i, j), ·) = δ_{(i, j−n)}` for `n < j ≤ i`.
* **Proposition 20.1.2 (ii)** (`proposition_20_1_2_ii`): `V`-uniformly ergodic, but not
  `IsLpGeomErgodic` in `L²(π)`. For `g = 1_{branch 2n}` we have `|Pⁿg − π(g)| ≥ 1/2` on half of
  the branch, so `‖Pⁿg − π(g)‖₂² ≥ ‖g‖₂²/8` for every `n`. Since the squared form of (20.7) is
  the norm form with constants `√R`, `√r`, it fails as well.
-/
namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-! ### The branch chain -/

/-- The branch states: `(i, j)` with `1 ≤ j ≤ i` is the state of branch `i` with `j` steps left. -/
def IsBranchState (x : ℕ × ℕ) : Prop := 1 ≤ x.2 ∧ x.2 ≤ x.1

/-- The deterministic move: down the branch, `(i, j) ↦ (i, j − 1)` for `j ≥ 2`, else back to the
hub `(0, 0)`. -/
def branchNext (x : ℕ × ℕ) : ℕ × ℕ :=
  if 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ 2 ≤ x.2 then (x.1, x.2 - 1) else (0, 0)

/-- The jump law from the hub: branch `k` (entered at `(k, k)`) with probability `2^{−(k+1)}`
(`k = 0` is the hub itself). -/
noncomputable def branchJump : Measure (ℕ × ℕ) :=
  Measure.sum fun k : ℕ => ((2 : ℝ≥0∞)⁻¹ ^ (k + 1)) • Measure.dirac (k, k)

/-- **The branch chain**: from the hub `(0, 0)` jump to `(k, k)` with probability `2^{−(k+1)}`,
then walk deterministically down branch `k` back to the hub. -/
noncomputable def branchKernel : Kernel (ℕ × ℕ) (ℕ × ℕ) :=
  Kernel.ofFunOfCountable fun x => if x = (0, 0) then branchJump else Measure.dirac (branchNext x)

/-- `P(hub, ·)` is the jump law. -/
theorem branchKernel_hub : branchKernel (0, 0) = branchJump := by
  change (if ((0, 0) : ℕ × ℕ) = (0, 0) then branchJump
    else Measure.dirac (branchNext (0, 0))) = _
  exact ite_eq_left rfl

/-- Off the hub the chain moves deterministically. -/
theorem branchKernel_of_ne {x : ℕ × ℕ} (hx : x ≠ (0, 0)) :
    branchKernel x = Measure.dirac (branchNext x) := by
  change (if x = (0, 0) then branchJump else Measure.dirac (branchNext x)) = _
  exact ite_eq_right hx

/-- `J{y} = 2^{−(y₁+1)}` if `y` is a branch entrance `(k, k)`, else `0`. -/
theorem branchJump_singleton (y : ℕ × ℕ) :
    branchJump {y} = if y.1 = y.2 then (2 : ℝ≥0∞)⁻¹ ^ (y.1 + 1) else 0 := by
  rw [branchJump, Measure.sum_apply _ (measurableSet_singleton y)]
  simp_rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton y)]
  split_ifs with h
  · rw [tsum_eq_single y.1 fun k hk => by
      rw [indicator_of_notMem (fun h' => hk (by rw [mem_singleton_iff] at h'; rw [← h'])),
        mul_zero]]
    rw [indicator_of_mem (mem_singleton_iff.2 (show ((y.1, y.1) : ℕ × ℕ) = y from Prod.ext rfl h)),
      Pi.one_apply, mul_one]
  · refine ENNReal.tsum_eq_zero.2 fun k => ?_
    rw [indicator_of_notMem (fun h' => h (by rw [mem_singleton_iff] at h'; rw [← h'])),
      mul_zero]

/-- The jump law is a probability. -/
theorem branchJump_univ : branchJump univ = 1 := by
  rw [branchJump, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The branch chain is a Markov kernel. -/
theorem isMarkovKernel_branchKernel : IsMarkovKernel branchKernel := by
  refine ⟨fun x => ⟨?_⟩⟩
  by_cases hx : x = (0, 0)
  · rw [hx, branchKernel_hub, branchJump_univ]
  · rw [branchKernel_of_ne hx, measure_univ]

/-! ### The invariant law -/

/-- The weights of the invariant law: `π(hub) = 1/2`, `π(i, j) = 2^{−(i+2)}` on branch states. -/
noncomputable def branchW (x : ℕ × ℕ) : ℝ≥0∞ :=
  if x = (0, 0) then 2⁻¹ else if 1 ≤ x.2 ∧ x.2 ≤ x.1 then (2 : ℝ≥0∞)⁻¹ ^ (x.1 + 2) else 0

/-- **The invariant law** of the branch chain. -/
noncomputable def branchPi : Measure (ℕ × ℕ) :=
  Measure.sum fun x : ℕ × ℕ => branchW x • Measure.dirac x

/-- `π{y} = w(y)`. -/
theorem branchPi_singleton (y : ℕ × ℕ) : branchPi {y} = branchW y := by
  rw [branchPi, Measure.sum_apply _ (measurableSet_singleton y), tsum_eq_single y fun x hx => by
    rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton y),
      indicator_of_notMem (fun h => hx (mem_singleton_iff.1 h)), smul_zero],
    Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton y), smul_eq_mul, mul_one]

/-- `w(hub) = 1/2`. -/
theorem branchW_hub : branchW (0, 0) = 2⁻¹ := by
  unfold branchW; exact ite_eq_left rfl

/-- `w = 2^{−(i+2)}` on branch states. -/
theorem branchW_branch {x : ℕ × ℕ} (hx : 1 ≤ x.2 ∧ x.2 ≤ x.1) :
    branchW x = (2 : ℝ≥0∞)⁻¹ ^ (x.1 + 2) := by
  have hne : x ≠ (0, 0) := fun h => by rw [h] at hx; omega
  unfold branchW; rw [ite_eq_right hne]; exact ite_eq_left hx

/-- `w = 0` elsewhere. -/
theorem branchW_other {x : ℕ × ℕ} (hne : x ≠ (0, 0)) (hx : ¬ (1 ≤ x.2 ∧ x.2 ≤ x.1)) :
    branchW x = 0 := by
  unfold branchW; rw [ite_eq_right hne]; exact ite_eq_right hx

/-- The row sums of the weights: `Σⱼ w(i, j) = [i = 0]/2 + i 2^{−(i+2)}`. -/
theorem tsum_branchW_row (i : ℕ) :
    ∑' j, branchW (i, j) = (if i = 0 then 2⁻¹ else 0) + (i : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (i + 2) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [tsum_eq_single 0 fun j hj => branchW_other (fun h => hj (Prod.mk.inj h).2)
      (by intro h; have := h.1; have := h.2; simp only at *; omega), branchW_hub,
      ite_eq_left rfl, Nat.cast_zero, zero_mul, add_zero]
  · rw [ite_eq_right hi.ne', zero_add, tsum_eq_sum (s := Finset.Icc 1 i) fun j hj => by
      rw [Finset.mem_Icc] at hj
      exact branchW_other (fun h => by have := (Prod.mk.inj h).1; omega) hj]
    rw [Finset.sum_congr rfl (g := fun _ => (2 : ℝ≥0∞)⁻¹ ^ (i + 2)) fun j hj => by
      rw [Finset.mem_Icc] at hj
      exact branchW_branch hj]
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]

/-- `Σ i 2^{−i} = 2` in `[0, ∞]`. -/
theorem tsum_nat_mul_two_inv_pow : ∑' i : ℕ, (i : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ i = 2 := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have h := tsum_coe_mul_geometric_of_norm_lt_one hr
  have e : ∀ i : ℕ, (i : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ i = ENNReal.ofReal ((i : ℝ) * (1 / 2) ^ i) :=
    fun i => by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg i), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos,
        ENNReal.ofReal_ofNat]
  simp_rw [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
    ((summable_pow_mul_geometric_of_norm_lt_one 1 hr).congr fun i => by rw [pow_one]), h]
  norm_num

/-- `π` is a probability. -/
theorem isProbabilityMeasure_branchPi : IsProbabilityMeasure branchPi := by
  constructor
  rw [branchPi, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.tsum_prod', tsum_congr tsum_branchW_row, ENNReal.tsum_add, tsum_ite_eq]
  simp_rw [pow_add, ← mul_assoc]
  rw [ENNReal.tsum_mul_right, tsum_nat_mul_two_inv_pow]
  rw [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul,
    ENNReal.inv_two_add_inv_two]

/-- `P(x, {y})`. -/
theorem branchKernel_singleton (x y : ℕ × ℕ) :
    branchKernel x {y} = if x = (0, 0) then branchJump {y} else
      (if branchNext x = y then 1 else 0) := by
  by_cases hx : x = (0, 0)
  · rw [ite_eq_left hx, hx, branchKernel_hub]
  · rw [ite_eq_right hx, branchKernel_of_ne hx, Measure.dirac_apply' _ (measurableSet_singleton y)]
    by_cases h : branchNext x = y
    · rw [ite_eq_left h, indicator_of_mem (mem_singleton_iff.2 h), Pi.one_apply]
    · rw [ite_eq_right h, indicator_of_notMem (fun h' => h (mem_singleton_iff.1 h'))]

/-- The flow into `y` from row `i ≥ 1`. -/
theorem branch_flow_row {i : ℕ} (hi : 1 ≤ i) (y : ℕ × ℕ) (j : ℕ) :
    branchKernel (i, j) {y} * branchW (i, j) =
      if 1 ≤ j ∧ j ≤ i ∧ branchNext (i, j) = y then (2 : ℝ≥0∞)⁻¹ ^ (i + 2) else 0 := by
  have hne : ((i, j) : ℕ × ℕ) ≠ (0, 0) := fun h => by have := (Prod.mk.inj h).1; omega
  rw [branchKernel_singleton, ite_eq_right hne]
  by_cases hb : 1 ≤ j ∧ j ≤ i
  · rw [branchW_branch hb]
    by_cases hn : branchNext (i, j) = y
    · rw [ite_eq_left hn, one_mul, ite_eq_left ⟨hb.1, hb.2, hn⟩]
    · rw [ite_eq_right hn, zero_mul, ite_eq_right (fun h => hn h.2.2)]
  · rw [branchW_other hne hb, mul_zero, ite_eq_right (fun h => hb ⟨h.1, h.2.1⟩)]

/-- The flow into `y` from row `0` (the hub). -/
theorem branch_flow_row_zero (y : ℕ × ℕ) :
    ∑' j, branchKernel (0, j) {y} * branchW (0, j) = branchJump {y} * 2⁻¹ := by
  rw [tsum_eq_single 0 fun j hj => by
    rw [branchW_other (fun h => hj (Prod.mk.inj h).2) (by intro h; simp only at h; omega),
      mul_zero]]
  rw [branchKernel_hub, branchW_hub]

/-- `next(i, j)` on a branch state: down the branch for `j ≥ 2`, to the hub for `j = 1`. -/
theorem branchNext_branch {i j : ℕ} (hj : 1 ≤ j) (hji : j ≤ i) :
    branchNext (i, j) = if 2 ≤ j then (i, j - 1) else (0, 0) := by
  unfold branchNext
  by_cases h2 : 2 ≤ j
  · rw [ite_eq_left (show 1 ≤ (i, j).2 ∧ (i, j).2 ≤ (i, j).1 ∧ 2 ≤ (i, j).2 from ⟨hj, hji, h2⟩),
      ite_eq_left h2]
  · rw [ite_eq_right (fun h : 1 ≤ (i, j).2 ∧ (i, j).2 ≤ (i, j).1 ∧ 2 ≤ (i, j).2 => h2 h.2.2),
      ite_eq_right h2]

/-- **`π` is invariant** for the branch chain. -/
theorem isInvariant_branchPi : IsInvariant branchKernel branchPi := by
  have := isMarkovKernel_branchKernel
  rw [IsInvariant, Measure.ext_iff_singleton]
  intro y
  rw [Measure.bind_apply (measurableSet_singleton y) (Kernel.aemeasurable _),
    lintegral_countable', branchPi_singleton]
  simp_rw [branchPi_singleton]
  rw [ENNReal.tsum_prod', tsum_eq_zero_add' ENNReal.summable, branch_flow_row_zero,
    tsum_congr fun i => tsum_congr fun j => branch_flow_row (by omega) y j, branchJump_singleton]
  -- the predecessors of `y` on the branches
  have hnext : ∀ i j : ℕ, 1 ≤ j → j ≤ i + 1 → (branchNext (i + 1, j) = y ↔
      (j = 1 ∧ y = (0, 0)) ∨ (2 ≤ j ∧ y = (i + 1, j - 1))) := fun i j hj hji => by
    rw [branchNext_branch hj hji]
    by_cases h2 : 2 ≤ j
    · rw [ite_eq_left h2]
      constructor
      · intro h; exact Or.inr ⟨h2, h.symm⟩
      · rintro (⟨h1, -⟩ | ⟨-, h⟩)
        · omega
        · exact h.symm
    · rw [ite_eq_right h2]
      constructor
      · intro h; exact Or.inl ⟨by omega, h.symm⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h.symm
        · exact absurd h h2
  by_cases hy0 : y = (0, 0)
  · -- the hub
    subst hy0
    have hrow : ∀ i : ℕ, ∑' j, (if 1 ≤ j ∧ j ≤ i + 1 ∧ branchNext (i + 1, j) = (0, 0) then
        (2 : ℝ≥0∞)⁻¹ ^ (i + 1 + 2) else 0) = (2 : ℝ≥0∞)⁻¹ ^ (i + 3) := fun i => by
      rw [tsum_eq_single 1 fun j hj => ite_eq_right fun h => by
        rcases (hnext i j h.1 h.2.1).1 h.2.2 with ⟨h1, -⟩ | ⟨-, h⟩
        · exact hj h1
        · exact absurd (Prod.mk.inj h).1 (by omega)]
      rw [ite_eq_left ⟨le_rfl, by omega, (hnext i 1 le_rfl (by omega)).2 (Or.inl ⟨rfl, rfl⟩)⟩]
    rw [tsum_congr hrow, branchW_hub, ite_eq_left rfl]
    simp_rw [pow_add]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    have e : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
    rw [pow_zero, one_mul, pow_one, show (2 : ℝ≥0∞)⁻¹ ^ 3 = 2⁻¹ * 2⁻¹ * 2⁻¹ by ring,
      ← mul_assoc, ← mul_assoc, e, one_mul, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
  · obtain ⟨a, b⟩ := y
    have hrow : ∀ i : ℕ, ∑' j, (if 1 ≤ j ∧ j ≤ i + 1 ∧ branchNext (i + 1, j) = (a, b) then
        (2 : ℝ≥0∞)⁻¹ ^ (i + 1 + 2) else 0) =
          if i + 1 = a ∧ 1 ≤ b ∧ b < a then (2 : ℝ≥0∞)⁻¹ ^ (a + 2) else 0 := fun i => by
      by_cases hc : i + 1 = a ∧ 1 ≤ b ∧ b < a
      · rw [ite_eq_left hc, tsum_eq_single (b + 1) fun j hj => ite_eq_right fun h => by
          rcases (hnext i j h.1 h.2.1).1 h.2.2 with ⟨-, h'⟩ | ⟨h2, h'⟩
          · exact hy0 h'
          · have := (Prod.mk.inj h').2; omega]
        rw [ite_eq_left ⟨by omega, by omega, (hnext i (b + 1) (by omega) (by omega)).2
          (Or.inr ⟨by omega, by rw [← hc.1]; rfl⟩)⟩, hc.1]
      · rw [ite_eq_right hc]
        refine ENNReal.tsum_eq_zero.2 fun j => ite_eq_right fun h => ?_
        rcases (hnext i j h.1 h.2.1).1 h.2.2 with ⟨-, h'⟩ | ⟨h2, h'⟩
        · exact hy0 h'
        · have e1 := (Prod.mk.inj h').1
          have e2 := (Prod.mk.inj h').2
          exact hc ⟨e1.symm, by omega, by omega⟩
    rw [tsum_congr hrow]
    by_cases hb : 1 ≤ b ∧ b < a
    · rw [tsum_eq_single (a - 1) fun i hi => ite_eq_right fun h => hi (by omega),
        ite_eq_right (show ¬ (a, b).1 = (a, b).2 by change ¬ a = b; omega), zero_mul, zero_add,
        ite_eq_left (show a - 1 + 1 = a ∧ 1 ≤ b ∧ b < a from ⟨by omega, hb⟩),
        branchW_branch (show 1 ≤ (a, b).2 ∧ (a, b).2 ≤ (a, b).1 by
          change 1 ≤ b ∧ b ≤ a; omega)]
    · rw [ENNReal.tsum_eq_zero.2 fun i => ite_eq_right fun h => hb ⟨h.2.1, h.2.2⟩, add_zero]
      by_cases hab : 1 ≤ b ∧ b = a
      · rw [ite_eq_left (show (a, b).1 = (a, b).2 from hab.2.symm),
          branchW_branch (show 1 ≤ (a, b).2 ∧ (a, b).2 ≤ (a, b).1 by
            change 1 ≤ b ∧ b ≤ a; omega)]
        change (2 : ℝ≥0∞)⁻¹ ^ (a + 1) * 2⁻¹ = 2⁻¹ ^ (a + 2)
        rw [← pow_succ]
      · have hnb : ¬ (1 ≤ (a, b).2 ∧ (a, b).2 ≤ (a, b).1) := by
          change ¬ (1 ≤ b ∧ b ≤ a); omega
        have hne : ¬ (a, b).1 = (a, b).2 := by
          change ¬ a = b
          intro h; apply hy0; ext <;> change _ = 0 <;> omega
        rw [ite_eq_right hne, zero_mul, branchW_other hy0 hnb]

/-! ### `V`-uniform ergodicity -/

/-- `P(hub, ·) ≥ ½ δ_hub`. -/
theorem branchJump_ge : (2 : ℝ≥0∞)⁻¹ • Measure.dirac ((0, 0) : ℕ × ℕ) ≤ branchJump := by
  have := Measure.le_sum (fun k : ℕ => ((2 : ℝ≥0∞)⁻¹ ^ (k + 1)) • Measure.dirac ((k, k) : ℕ × ℕ)) 0
  rwa [zero_add, pow_one] at this

/-- `Pⁿ⁺¹(x, A) = Pⁿ(y, A)` when `P(x, ·) = δ_y`. -/
theorem branchKernel_pow_succ_of_ne {x : ℕ × ℕ} (hx : x ≠ (0, 0)) (n : ℕ) {A : Set (ℕ × ℕ)}
    (hA : MeasurableSet A) :
    (branchKernel ^ (n + 1)) x A = (branchKernel ^ n) (branchNext x) A := by
  rw [pow_succ_apply _ n x hA, branchKernel_of_ne hx,
    lintegral_dirac' _ ((branchKernel ^ n).measurable_coe hA)]

/-- Every state reaches the hub. -/
theorem branch_reaches_hub (x : ℕ × ℕ) : ∃ n, 0 < (branchKernel ^ (n + 1)) x {(0, 0)} := by
  induction h : x.2 using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    by_cases hx : x = (0, 0)
    · refine ⟨0, ?_⟩
      rw [zero_add, pow_one, hx, branchKernel_hub, branchJump_singleton, ite_eq_left rfl]
      exact ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _
    by_cases hb : 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ 2 ≤ x.2
    · have hnx : branchNext x = (x.1, x.2 - 1) := by unfold branchNext; exact ite_eq_left hb
      obtain ⟨n, hn⟩ := ih (x.2 - 1) (by omega) (x.1, x.2 - 1) rfl
      refine ⟨n + 1, ?_⟩
      rw [branchKernel_pow_succ_of_ne hx _ (measurableSet_singleton _), hnx]
      exact hn
    · have hnx : branchNext x = (0, 0) := by unfold branchNext; exact ite_eq_right hb
      refine ⟨0, ?_⟩
      rw [branchKernel_pow_succ_of_ne hx _ (measurableSet_singleton _), hnx, pow_zero]
      change 0 < Measure.dirac ((0, 0) : ℕ × ℕ) {(0, 0)}
      rw [Measure.dirac_apply_of_mem (mem_singleton _)]
      exact one_pos

/-- The branch chain is `δ_hub`-irreducible. -/
theorem branch_isPhiIrreducible :
    haveI := isMarkovKernel_branchKernel
    IsPhiIrreducible branchKernel (Measure.dirac (0, 0)) := by
  have := isMarkovKernel_branchKernel
  intro A hA hpos x
  have hmem : ((0, 0) : ℕ × ℕ) ∈ A := by
    by_contra h
    rw [Measure.dirac_apply' _ hA, indicator_of_notMem h] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨n, hn⟩ := branch_reaches_hub x
  exact (hitProb_pos_iff _ hA x).2 ⟨n, hn.trans_le (measure_mono (singleton_subset_iff.2 hmem))⟩

/-- The drift function `V(i, j) = (3/2)ʲ`. -/
noncomputable def branchV (x : ℕ × ℕ) : ℝ≥0∞ := ENNReal.ofReal ((3 / 2 : ℝ) ^ x.2)

/-- The set where the chain leaves its branch next: `C = {x : not (branch state with j ≥ 2)}`. -/
def branchC : Set (ℕ × ℕ) := {x | ¬ (1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ 2 ≤ x.2)}

/-- `PV(hub) = Σ 2^{−(k+1)} (3/2)ᵏ = 2`. -/
theorem lintegral_branchV_hub : ∫⁻ y, branchV y ∂branchKernel (0, 0) = 2 := by
  rw [branchKernel_hub, branchJump, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, lintegral_dirac, branchV, smul_eq_mul]
  have e : ∀ k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (k + 1) * ENNReal.ofReal ((3 / 2 : ℝ) ^ (k, k).2) =
      ENNReal.ofReal (1 / 2 * (3 / 4 : ℝ) ^ k) := fun k => by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos two_pos,
      ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    change (2⁻¹ : ℝ) ^ (k + 1) * (3 / 2) ^ k = _
    rw [pow_succ, show (3 / 4 : ℝ) = 2⁻¹ * (3 / 2) by norm_num, mul_pow]
    ring
  simp_rw [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _), tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- **(V4) for the branch chain**: `PV ≤ (2/3)V + 2·1_C`. -/
theorem branch_driftV4 :
    DriftV4 branchKernel branchV (ENNReal.ofReal (2 / 3)) 2 branchC := by
  intro x
  by_cases hx : x = (0, 0)
  · subst hx
    rw [lintegral_branchV_hub, indicator_of_mem (show ((0, 0) : ℕ × ℕ) ∈ branchC by
      change ¬ _; omega)]
    exact le_add_self
  by_cases hb : 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ 2 ≤ x.2
  · have hnx : branchNext x = (x.1, x.2 - 1) := by unfold branchNext; exact ite_eq_left hb
    rw [branchKernel_of_ne hx, lintegral_dirac, hnx,
      indicator_of_notMem (show x ∉ branchC from fun h => h hb),
      add_zero, branchV, branchV, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    change (3 / 2 : ℝ) ^ (x.2 - 1) = 2 / 3 * (3 / 2) ^ x.2
    obtain ⟨k, hk⟩ : ∃ k, x.2 = k + 1 := ⟨x.2 - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]
    ring
  · have hnx : branchNext x = (0, 0) := by unfold branchNext; exact ite_eq_right hb
    rw [branchKernel_of_ne hx, lintegral_dirac, hnx, indicator_of_mem (show x ∈ branchC from hb)]
    refine le_trans ?_ le_add_self
    rw [branchV]
    change ENNReal.ofReal ((3 / 2 : ℝ) ^ 0) ≤ 2
    rw [pow_zero, ENNReal.ofReal_one]
    exact one_le_two

/-- `C` is small: `P²(x, ·) ≥ ¼ δ_hub` on `C`. -/
theorem branchC_isSmallSet :
    IsSmallSet branchKernel 2 ((4 : ℝ≥0∞)⁻¹ • Measure.dirac (0, 0)) branchC := by
  have h4 : (4 : ℝ≥0∞)⁻¹ = 2⁻¹ * 2⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inr ENNReal.ofNat_ne_top) (Or.inl ENNReal.ofNat_ne_top)]; norm_num
  have hhubA : ∀ A, MeasurableSet A → (2 : ℝ≥0∞)⁻¹ * Measure.dirac ((0, 0) : ℕ × ℕ) A ≤
      branchKernel (0, 0) A := fun A hA => by
    rw [branchKernel_hub]
    have := branchJump_ge A
    rwa [Measure.smul_apply, smul_eq_mul] at this
  refine ⟨measurableSet_of_countable branchC, two_pos, ?_, fun x hx => ?_⟩
  · intro h
    have := congrArg (fun m : Measure (ℕ × ℕ) => m univ) h
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, Measure.coe_zero,
      Pi.zero_apply, ENNReal.inv_eq_zero, ENNReal.ofNat_ne_top] at this
  refine Measure.le_intro fun A hA _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, pow_succ_apply _ 1 x hA, pow_one, h4, mul_assoc]
  by_cases hx0 : x = (0, 0)
  · subst hx0
    rw [branchKernel_hub]
    calc (2 : ℝ≥0∞)⁻¹ * (2⁻¹ * Measure.dirac ((0, 0) : ℕ × ℕ) A)
        ≤ 2⁻¹ * branchKernel (0, 0) A := mul_le_mul' le_rfl (hhubA A hA)
      _ = ∫⁻ y, branchKernel y A ∂((2 : ℝ≥0∞)⁻¹ • Measure.dirac ((0, 0) : ℕ × ℕ)) := by
          rw [lintegral_smul_measure, lintegral_dirac' _ (branchKernel.measurable_coe hA),
            smul_eq_mul]
      _ ≤ ∫⁻ y, branchKernel y A ∂branchJump := lintegral_mono' branchJump_ge le_rfl
  · have hnx : branchNext x = (0, 0) := by unfold branchNext; exact ite_eq_right hx
    rw [branchKernel_of_ne hx0, hnx, lintegral_dirac' _ (branchKernel.measurable_coe hA)]
    calc (2 : ℝ≥0∞)⁻¹ * (2⁻¹ * Measure.dirac ((0, 0) : ℕ × ℕ) A)
        ≤ 1 * (2⁻¹ * Measure.dirac ((0, 0) : ℕ × ℕ) A) :=
          mul_le_mul' (ENNReal.inv_le_one.2 one_le_two) le_rfl
      _ ≤ branchKernel (0, 0) A := by rw [one_mul]; exact hhubA A hA

/-- **The branch chain is `V`-uniformly ergodic**, `V(i, j) = (3/2)ʲ`, at a geometric rate
(Theorem 16.1.2: irreducible, aperiodic, (V4) on a small set). -/
theorem branch_vUniform :
    IsVUniformlyErgodic branchV branchKernel branchPi ∧ ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞,
      R ≠ ∞ ∧ ∀ n, vErgDist branchV branchKernel branchPi n ≤ R * r⁻¹ ^ n := by
  have := isMarkovKernel_branchKernel
  have := isProbabilityMeasure_branchPi
  have hφ := branch_isPhiIrreducible
  have hψ := isMaximalIrreducibility_maxIrrMeasure _ hφ (IsProbabilityMeasure.ne_zero _)
  have hψC : 0 < maxIrrMeasure branchKernel (Measure.dirac (0, 0)) {(0, 0)} := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have := (hψ.2.2 _ hφ) h0
    rw [Measure.dirac_apply_of_mem (mem_singleton _)] at this
    exact one_ne_zero this
  let M : Minorization branchKernel :=
    { C := {(0, 0)}, δ := 2⁻¹, ν := Measure.dirac (0, 0),
      measurableSet_C := measurableSet_singleton _,
      δ_pos := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top,
      δ_lt_one := ENNReal.inv_lt_one.2 ENNReal.one_lt_two,
      isProbabilityMeasure_ν := inferInstance,
      le := fun x hx => by
        rw [mem_singleton_iff.1 hx, branchKernel_hub]; exact branchJump_ge }
  have hap : IsAperiodic branchKernel (maxIrrMeasure branchKernel (Measure.dirac (0, 0))) :=
    isAperiodic_of_minorization hψ M hψC (by
      change 0 < Measure.dirac ((0, 0) : ℕ × ℕ) {(0, 0)}
      rw [Measure.dirac_apply_of_mem (mem_singleton _)]; exact one_pos)
  have hV1 : ∀ x, 1 ≤ branchV x := fun x =>
    ENNReal.one_le_ofReal.2 (one_le_pow₀ (by norm_num))
  have hinv := isInvariant_branchPi
  obtain ⟨-, r, hr, -, R, hR, hb⟩ := vErgDist_le_of_driftV4 hψ hap (measurable_of_countable _)
    hV1 (fun _ => ENNReal.ofReal_ne_top) (ENNReal.ofReal_lt_one.2 (by norm_num))
    ENNReal.ofNat_ne_top ⟨_, _, proposition_5_5_3 branchC_isSmallSet⟩ branch_driftV4 branchPi
    hinv
  refine ⟨⟨hinv, ?_⟩, r, hr, R, hR, hb⟩
  have hr1 : r⁻¹ < 1 := ENNReal.inv_lt_one.2 hr
  have hlim : Tendsto (fun n => R * r⁻¹ ^ n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1)
      (Or.inr hR)
    rwa [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hb

/-! ### No geometric ergodicity in `L²(π)` -/

/-- The states of branch `i`. -/
def branchSet (i : ℕ) : Set (ℕ × ℕ) := {x | x.1 = i ∧ 1 ≤ x.2 ∧ x.2 ≤ i}

/-- Along a branch the chain is deterministic: `Pⁿ((i, j), ·) = δ_{(i, j − n)}` for `n < j ≤ i`. -/
theorem branchKernel_pow_branch (n : ℕ) : ∀ {i j : ℕ}, n < j → j ≤ i →
    (branchKernel ^ n) (i, j) = Measure.dirac (i, j - n) := by
  induction n with
  | zero => intro i j _ _; rw [pow_zero_apply, Nat.sub_zero]
  | succ n ih =>
    intro i j hnj hji
    have hne : ((i, j) : ℕ × ℕ) ≠ (0, 0) := fun h => by have := (Prod.mk.inj h).2; omega
    have hnx : branchNext (i, j) = (i, j - 1) := by
      unfold branchNext
      exact ite_eq_left (show 1 ≤ (i, j).2 ∧ (i, j).2 ≤ (i, j).1 ∧ 2 ≤ (i, j).2 from
        ⟨by change 1 ≤ j; omega, by change j ≤ i; omega, by change 2 ≤ j; omega⟩)
    rw [pow_succ]
    change ((branchKernel ^ n) ∘ₖ branchKernel) (i, j) = _
    rw [Kernel.comp_apply, branchKernel_of_ne hne, hnx,
      Measure.dirac_bind (Kernel.measurable _), ih (by omega) (by omega),
      show j - 1 - n = j - (n + 1) by omega]

/-- `π(branch i) = i 2^{−(i+2)}`. -/
theorem branchPi_branchSet (i : ℕ) :
    branchPi (branchSet i) = (i : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (i + 2) := by
  have hset : branchSet i = ↑((Finset.Icc 1 i).image fun j => (i, j)) := by
    ext ⟨a, b⟩
    simp only [branchSet, Finset.coe_image, Finset.coe_Icc, mem_image, mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, h1, h2⟩; exact ⟨b, ⟨h1, h2⟩, rfl, rfl⟩
    · rintro ⟨j, ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨rfl, h1, h2⟩
  rw [hset, ← sum_measure_singleton, Finset.sum_image fun a _ b _ h => (Prod.mk.inj h).2]
  rw [Finset.sum_congr rfl (g := fun _ => (2 : ℝ≥0∞)⁻¹ ^ (i + 2)) fun j hj => by
    rw [Finset.mem_Icc] at hj
    rw [branchPi_singleton, branchW_branch hj]]
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]

/-- `π(branch i) ≤ 1/2` (the hub carries `1/2`). -/
theorem branchPi_branchSet_le (i : ℕ) : branchPi (branchSet i) ≤ 2⁻¹ := by
  have := isProbabilityMeasure_branchPi
  have hdis : Disjoint (branchSet i) {(0, 0)} := by
    rw [disjoint_singleton_right]; intro h; have := h.2.1; change 1 ≤ 0 at this; omega
  have h := measure_union hdis (measurableSet_singleton ((0, 0) : ℕ × ℕ)) (μ := branchPi)
  rw [branchPi_singleton, branchW_hub] at h
  have h1 : branchPi (branchSet i) + 2⁻¹ ≤ 1 := h ▸ prob_le_one
  calc branchPi (branchSet i) = branchPi (branchSet i) + 2⁻¹ - 2⁻¹ :=
        (ENNReal.add_sub_cancel_right (ENNReal.inv_ne_top.2 two_ne_zero)).symm
    _ ≤ 1 - 2⁻¹ := tsub_le_tsub_right h1 _
    _ = 2⁻¹ := ENNReal.one_sub_inv_two

/-- `‖f‖₂² = ∫ ‖f‖²` in the form used here. -/
theorem eLpNorm_two_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
  norm_num

/-- **Proposition 20.1.2 (ii)** (MT p. 515): *there is a Markov chain that is `V`-uniformly
ergodic but not geometrically ergodic in `L²(π)`*. The branch chain is `V`-uniformly ergodic, but
the indicator `g` of branch `2n` satisfies `‖Pⁿg − π(g)‖₂ ≥ ‖g‖₂/(2√2)`, so no bound
`R r⁻ⁿ ‖g‖₂` with `r > 1` is possible. -/
theorem proposition_20_1_2_ii :
    IsVUniformlyErgodic branchV branchKernel branchPi ∧
      ¬ IsLpGeomErgodic branchKernel branchPi 2 := by
  have := isMarkovKernel_branchKernel
  have := isProbabilityMeasure_branchPi
  refine ⟨branch_vUniform.1, ?_⟩
  rintro ⟨r, hr, R, hR⟩
  -- choose `n ≥ 1` with `R r⁻ⁿ < 1/3`
  have hr1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have hlim : Tendsto (fun n : ℕ => |R| * r⁻¹ ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (by linarith)) hr1).const_mul
      |R|
    rwa [mul_zero] at this
  obtain ⟨n, hn, hn1⟩ := ((hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))).and
    (eventually_ge_atTop 1)).exists
  set i := 2 * n with hi
  set B := branchSet i with hB
  set g : ℕ × ℕ → ℝ := B.indicator fun _ => 1 with hg
  have hgm : Measurable g := measurable_of_countable g
  have hgb : ∀ x, ‖g x‖ ≤ 1 := fun x => by
    rw [hg, Real.norm_eq_abs]
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, abs_one]
    · rw [indicator_of_notMem hx, abs_zero]; exact zero_le_one
  have hgL : MemLp g 2 branchPi :=
    MemLp.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
  have h := hR n g hgL
  set F : ℕ × ℕ → ℝ := fun x => ∫ y, g y ∂(branchKernel ^ n) x - ∫ y, g y ∂branchPi with hF
  have hFm : Measurable F := measurable_of_countable F
  -- square both sides
  have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), eLpNorm_two_sq hFm.aestronglyMeasurable,
    eLpNorm_two_sq hgm.aestronglyMeasurable, ENNReal.rpow_two] at h2
  -- `∫ ‖g‖² = π(B) = 2n 2^{−(2n+2)}`
  have hg2 : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂branchPi = branchPi B := by
    rw [← lintegral_indicator_one (measurableSet_of_countable B)]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ B
    · rw [hg, indicator_of_mem hx, indicator_of_mem hx, enorm_one, ENNReal.one_rpow,
        Pi.one_apply]
    · rw [hg, indicator_of_notMem hx, indicator_of_notMem hx, enorm_zero,
        ENNReal.zero_rpow_of_pos (by norm_num)]
  -- on `(i, j)`, `n < j ≤ i`: `F = 1 − π(B) ≥ 1/2`
  have hπg : ∫ y, g y ∂branchPi ≤ 1 / 2 := by
    rw [hg, integral_indicator (measurableSet_of_countable B), setIntegral_const, smul_eq_mul,
      mul_one, measureReal_def]
    have := branchPi_branchSet_le i
    rw [← hB] at this
    have := ENNReal.toReal_mono (ENNReal.inv_ne_top.2 two_ne_zero) this
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at this
    linarith
  have hFj : ∀ j ∈ Finset.Ioc n i, (4 : ℝ≥0∞)⁻¹ ≤ ‖F (i, j)‖ₑ ^ (2 : ℝ) := fun j hj => by
    rw [Finset.mem_Ioc] at hj
    have hdir := branchKernel_pow_branch n (i := i) (j := j) hj.1 hj.2
    have hgij : g (i, j - n) = 1 := by
      rw [hg, indicator_of_mem]
      exact ⟨rfl, by change 1 ≤ j - n; omega, by change j - n ≤ i; omega⟩
    have hFv : 1 / 2 ≤ F (i, j) := by
      rw [hF]; dsimp only
      rw [hdir, integral_dirac, hgij]
      linarith
    rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs, abs_of_pos (by linarith),
      ← ENNReal.ofReal_pow (by linarith)]
    calc (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((1 / 2) ^ 2) := by
          rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos,
            ENNReal.ofReal_ofNat, ← ENNReal.inv_pow]; norm_num
      _ ≤ ENNReal.ofReal (F (i, j) ^ 2) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by norm_num) hFv 2)
  -- the lower bound on `∫ ‖F‖²`
  set w : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ (i + 2) with hw
  have hw0 : w ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
  have hwt : w ≠ ∞ := ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero)
  have hA : (n : ℝ≥0∞) * (4⁻¹ * w) ≤ ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂branchPi := by
    refine le_trans ?_ (setLIntegral_le_lintegral
      (↑((Finset.Ioc n i).image fun j => (i, j)) : Set (ℕ × ℕ)) _)
    rw [lintegral_finset, Finset.sum_image fun a _ b _ h => (Prod.mk.inj h).2]
    calc (n : ℝ≥0∞) * (4⁻¹ * w) = ∑ j ∈ Finset.Ioc n i, 4⁻¹ * w := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, hi]
          congr 2; omega
      _ ≤ ∑ j ∈ Finset.Ioc n i, ‖F (i, j)‖ₑ ^ (2 : ℝ) * branchPi {(i, j)} :=
          Finset.sum_le_sum fun j hj => by
            have hj' := Finset.mem_Ioc.1 hj
            rw [branchPi_singleton, branchW_branch (show 1 ≤ (i, j).2 ∧ (i, j).2 ≤ (i, j).1 by
              change 1 ≤ j ∧ j ≤ i; omega)]
            exact mul_le_mul' (hFj j hj) le_rfl
  have hB' : branchPi B = (2 * n : ℝ≥0∞) * w := by
    rw [hB, branchPi_branchSet, hi]; push_cast; rfl
  have hc : ENNReal.ofReal (R * r⁻¹ ^ n) ^ 2 ≤ ENNReal.ofReal (1 / 9) := by
    have hc1 : ENNReal.ofReal (R * r⁻¹ ^ n) ≤ ENNReal.ofReal (1 / 3) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_right (le_abs_self R)
        (pow_nonneg (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ r)) n)
      linarith
    calc ENNReal.ofReal (R * r⁻¹ ^ n) ^ 2 ≤ ENNReal.ofReal (1 / 3) ^ 2 := pow_le_pow_left' hc1 2
      _ = ENNReal.ofReal (1 / 9) := by rw [← ENNReal.ofReal_pow (by norm_num)]; norm_num
  have hfin : (n : ℝ≥0∞) * (4⁻¹ * w) ≤ ENNReal.ofReal (1 / 9) * ((2 * n : ℝ≥0∞) * w) :=
    hA.trans (h2.trans (by rw [hg2, hB']; exact mul_le_mul' hc le_rfl))
  have hN0 : (n : ℝ≥0∞) * w ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) hw0
  have hNt : (n : ℝ≥0∞) * w ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hwt
  have e1 : (n : ℝ≥0∞) * (4⁻¹ * w) = (n * w) * 4⁻¹ := by ring
  have e2 : ENNReal.ofReal (1 / 9) * ((2 * n : ℝ≥0∞) * w) =
      (n * w) * (ENNReal.ofReal (1 / 9) * 2) := by ring
  rw [e1, e2, ENNReal.mul_le_mul_iff_right hN0 hNt] at hfin
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofNat_ne_top) hfin
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofNat] at this
  norm_num at this

end MeynTweedie.Epilogue

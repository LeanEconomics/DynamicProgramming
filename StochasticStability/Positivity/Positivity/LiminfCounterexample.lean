/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.BoundedInProbability
import Mathlib.Topology.Instances.ENat

/-!
# Proposition 12.1.3 for `Pᵏ` is false (MT §12.1.2)

Meyn and Tweedie, Proposition 12.1.3, p. 291, states the result with
`liminf_k E_x[V(Φₖ)] < ∞`. The book's proof runs through (12.4), the Cesàro form of
Theorem 12.1.2 (i). A finite `liminf` of `E_x[V(Φₖ)]` gives `Pᵏ(x, C) ≥ 1/2` along a
subsequence, but this does not stop the Cesàro means `P̄ⁿ(x, C)` from tending to `0`. The
statement for `Pᵏ` is false.

**The counterexample** (`proposition_12_1_3_counterexample`). The space is `ℕ × ℕ∞`, with the
discrete topology on `ℕ` and the order topology on `ℕ∞`; `nat_prod_enat_standing` shows that it
meets the chapter's standing hypotheses (`borelSpace_nat_prod_enat`). The chain is the
deterministic map `liminfCexMap`.
* Loop `m` visits `(0, m), …, (m, m)` and then jumps to `(0, m + 1)`.
* Off the loops the first coordinate increases; the limit points `(k, ∞)` move to `(k + 1, ∞)`.
* The map is continuous (`continuous_liminfCexMap`), so the chain is weak Feller
  (`isWeakFeller_liminfCexKernel`), and `V(k, m) = k` is coercive (`isCoercive_liminfCex`).
* The orbit of `(0, 0)` comes back to `{V = 0}` at the start of every loop
  (`exists_iterate_liminfCexMap`), so `liminf_k E_{(0,0)}[V(Φₖ)] = 0`.
* No probability measure is invariant (`liminfCex_no_invariant`). Every point has at most one
  preimage, the orbits start at points with none, and so an invariant `π` puts mass `0` on every
  point.

**Corrected statement.** `proposition_12_1_3` (in `BoundedInProbability`) is the Cesàro form,
`liminf_n n⁻¹ Σ_{k ≤ n} E_x[V(Φₖ)] < ∞`, together with `proposition_12_1_3_of_eventually_le`.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-- The state space `ℕ × ℕ∞` of the counterexample is a Borel space: it is countable and `T₁`,
so its Borel σ-algebra is the power set. -/
theorem borelSpace_nat_prod_enat : BorelSpace (ℕ × ℕ∞) :=
  ⟨by
    rw [borel_eq_top_of_countable]
    exact top_unique fun s _ => .of_discrete⟩

/-- The standing hypotheses of Chapter 12 hold on `ℕ × ℕ∞` (with the discrete topology on `ℕ` and
the order topology on `ℕ∞`): it is a locally compact, σ-compact, second-countable, metrizable
Hausdorff space with its Borel σ-algebra. -/
theorem nat_prod_enat_standing :
    T2Space (ℕ × ℕ∞) ∧ LocallyCompactSpace (ℕ × ℕ∞) ∧ SigmaCompactSpace (ℕ × ℕ∞) ∧
      SecondCountableTopology (ℕ × ℕ∞) ∧ TopologicalSpace.MetrizableSpace (ℕ × ℕ∞) ∧
      BorelSpace (ℕ × ℕ∞) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    borelSpace_nat_prod_enat⟩

/-- The deterministic map of the counterexample to Proposition 12.1.3: loop `m` runs through
`(0, m), (1, m), …, (m, m)` and then jumps to `(0, m + 1)`; on `(k, m)` with `k ≠ m` the first
coordinate increases. The limit points `(k, ∞)` move to `(k + 1, ∞)`. -/
def liminfCexMap (p : ℕ × ℕ∞) : ℕ × ℕ∞ :=
  if (p.1 : ℕ∞) = p.2 then (0, p.2 + 1) else (p.1 + 1, p.2)

/-- The counterexample map is continuous: on each slice `{k} × ℕ∞` it is piecewise continuous on
the clopen set `{(k, k)}` and its complement. -/
theorem continuous_liminfCexMap : Continuous liminfCexMap := by
  refine continuous_prod_of_discrete_left.2 fun k => ?_
  have hset : {m : ℕ∞ | (k : ℕ∞) = m} = {(k : ℕ∞)} := by
    ext m
    simp [eq_comm]
  have hclopen : IsClopen {m : ℕ∞ | (k : ℕ∞) = m} := by
    rw [hset]
    exact ⟨isClosed_singleton, ENat.isOpen_singleton (ENat.natCast_ne_top k)⟩
  change Continuous fun m : ℕ∞ => if (k : ℕ∞) = m then ((0 : ℕ), m + 1) else (k + 1, m)
  refine Continuous.if (p := fun m : ℕ∞ => (k : ℕ∞) = m) ?_
    (continuous_const.prodMk (continuous_id.add continuous_const))
    (continuous_const.prodMk continuous_id)
  intro m hm
  rw [hclopen.frontier_eq] at hm
  exact absurd hm (notMem_empty m)

/-- The deterministic Markov kernel `δ_{T(x)}` of the counterexample. -/
noncomputable def liminfCexKernel : Kernel (ℕ × ℕ∞) (ℕ × ℕ∞) :=
  Kernel.deterministic liminfCexMap (.of_discrete)

/-- The `n`-step kernel is `δ_{Tⁿ(x)}`. -/
theorem liminfCexKernel_pow_apply (n : ℕ) (x : ℕ × ℕ∞) :
    (liminfCexKernel ^ n) x = Measure.dirac (liminfCexMap^[n] x) := by
  induction n generalizing x with
  | zero => rw [pow_zero_apply]; rfl
  | succ n ih =>
    rw [Kernel.pow_add, pow_one, Kernel.comp_apply,
      show liminfCexKernel x = Measure.dirac (liminfCexMap x) from Kernel.deterministic_apply _ _,
      Measure.dirac_bind (Kernel.measurable _), ih, Function.iterate_succ_apply]

/-- Along loop `m`: `Tʲ(0, m) = (j, m)` for `j ≤ m`. -/
theorem liminfCexMap_iterate_loop (m : ℕ) {j : ℕ} (hj : j ≤ m) :
    liminfCexMap^[j] (0, (m : ℕ∞)) = (j, (m : ℕ∞)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega), liminfCexMap]
    have : ((j : ℕ) : ℕ∞) ≠ (m : ℕ∞) := by exact_mod_cast (show j ≠ m by omega)
    simp [this]

/-- The orbit of `(0, 0)` returns to `(0, m)` at a time `n ≥ m`, for every `m`. -/
theorem exists_iterate_liminfCexMap (m : ℕ) :
    ∃ n ≥ m, liminfCexMap^[n] (0, 0) = (0, (m : ℕ∞)) := by
  induction m with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ m ih =>
    obtain ⟨n, hn, h⟩ := ih
    refine ⟨(m + 1) + n, by omega, ?_⟩
    rw [Function.iterate_add_apply, h, Function.iterate_succ_apply',
      liminfCexMap_iterate_loop m le_rfl, liminfCexMap]
    simp

/-- No probability measure is invariant for the counterexample: every point has at most one
preimage, which lies earlier on its orbit, and the orbits start at points without preimage, so
an invariant `π` gives every point mass `0`. -/
theorem liminfCex_no_invariant :
    ¬ ∃ π : Measure (ℕ × ℕ∞), IsProbabilityMeasure π ∧ IsInvariant liminfCexKernel π := by
  rintro ⟨π, hπ, hinv⟩
  have hpre : ∀ s, π s = π (liminfCexMap ⁻¹' s) := fun s => by
    have h := congrArg (fun ν => ν s) hinv
    simp only [liminfCexKernel] at h
    rw [Measure.deterministic_comp_eq_map, Measure.map_apply (.of_discrete) (.of_discrete)] at h
    exact h.symm
  have hle : ∀ y z, (∀ p, liminfCexMap p = y → p = z) → π {y} ≤ π {z} := fun y z h => by
    rw [hpre]
    exact measure_mono fun p hp => h p hp
  have hzero : ∀ y, (∀ p, liminfCexMap p ≠ y) → π {y} = 0 := fun y h => by
    rw [hpre]
    have : liminfCexMap ⁻¹' {y} = ∅ := eq_empty_of_forall_notMem fun p hp => h p hp
    rw [this, measure_empty]
  -- the points `(j, ∞)`
  have htop : ∀ j : ℕ, π {(j, ⊤)} = 0 := by
    intro j
    induction j with
    | zero =>
      refine hzero _ fun p hp => ?_
      simp only [liminfCexMap] at hp
      split_ifs at hp with h
      · have h2 := congrArg Prod.snd hp
        simp only at h2
        have h3 : p.2 = ⊤ := by simpa using h2
        exact ENat.natCast_ne_top p.1 (h.trans h3)
      · exact absurd (congrArg Prod.fst hp) (by simp)
    | succ j ih =>
      refine le_antisymm ((hle _ (j, ⊤) fun p hp => ?_).trans ih.le) zero_le
      simp only [liminfCexMap] at hp
      split_ifs at hp with h
      · exact absurd (congrArg Prod.fst hp) (by simp)
      · obtain ⟨h1, h2⟩ := Prod.mk.inj hp
        exact Prod.ext (by omega) h2
  -- the points `(j, n)`
  have hfin : ∀ n j : ℕ, π {(j, (n : ℕ∞))} = 0 := by
    intro n
    induction n with
    | zero =>
      intro j
      induction j with
      | zero =>
        refine hzero _ fun p hp => ?_
        simp only [liminfCexMap] at hp
        split_ifs at hp with h
        · have h2 := congrArg Prod.snd hp
          simp only [Nat.cast_zero] at h2
          exact absurd h2 (by simp)
        · exact absurd (congrArg Prod.fst hp) (by simp)
      | succ j ih =>
        refine le_antisymm ((hle _ (j, ((0 : ℕ) : ℕ∞)) fun p hp => ?_).trans ih.le) zero_le
        simp only [liminfCexMap] at hp
        split_ifs at hp with h
        · exact absurd (congrArg Prod.fst hp) (by simp)
        · obtain ⟨h1, h2⟩ := Prod.mk.inj hp
          exact Prod.ext (by omega) h2
    | succ n ihn =>
      intro j
      induction j with
      | zero =>
        refine le_antisymm ((hle _ (n, (n : ℕ∞)) fun p hp => ?_).trans (ihn n).le) zero_le
        simp only [liminfCexMap] at hp
        split_ifs at hp with h
        · obtain ⟨-, h2⟩ := Prod.mk.inj hp
          have h3 : p.2 = (n : ℕ∞) := by
            induction hp2 : p.2 using ENat.recTopCoe with
            | top =>
              rw [hp2] at h2
              exact absurd h2.symm (by exact_mod_cast ENat.natCast_ne_top (n + 1))
            | coe a =>
              rw [hp2] at h2
              have : a + 1 = n + 1 := by exact_mod_cast h2
              rw [show a = n by omega]
          refine Prod.ext ?_ h3
          exact_mod_cast h.trans h3
        · exact absurd (congrArg Prod.fst hp) (by simp)
      | succ j ih =>
        refine le_antisymm ((hle _ (j, ((n + 1 : ℕ) : ℕ∞)) fun p hp => ?_).trans ih.le) zero_le
        simp only [liminfCexMap] at hp
        split_ifs at hp with h
        · exact absurd (congrArg Prod.fst hp) (by simp)
        · obtain ⟨h1, h2⟩ := Prod.mk.inj hp
          exact Prod.ext (by omega) h2
  have hall : ∀ y : ℕ × ℕ∞, π {y} = 0 := by
    rintro ⟨j, m⟩
    induction m using ENat.recTopCoe with
    | top => exact htop j
    | coe n => exact hfin n j
  have h0 : π univ = 0 := by
    refine le_antisymm ?_ zero_le
    calc π univ = π (⋃ y : ℕ × ℕ∞, {y}) := by rw [iUnion_of_singleton]
      _ ≤ ∑' y, π {y} := measure_iUnion_le _
      _ = 0 := by simp [hall]
  simp at h0

/-- The counterexample kernel is weak Feller: `P(x, O) = 1_O(T x)` and `T` is continuous. -/
theorem isWeakFeller_liminfCexKernel : IsWeakFeller liminfCexKernel := by
  intro O hO
  have h : (fun x => liminfCexKernel x O) = (liminfCexMap ⁻¹' O).indicator 1 := by
    funext x
    rw [liminfCexKernel, Kernel.deterministic_apply' _ _ (.of_discrete)]
    by_cases hx : liminfCexMap x ∈ O
    · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ liminfCexMap ⁻¹' O from hx)]
      rfl
    · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ liminfCexMap ⁻¹' O from hx)]
  rw [h]
  exact (hO.preimage continuous_liminfCexMap).lowerSemicontinuous_indicator zero_le

/-- `V(k, m) = k` is coercive on `ℕ × ℕ∞`: `{V ≤ r} ⊆ {0, …, ⌊r⌋} × ℕ∞`, which is compact. -/
theorem isCoercive_liminfCex : IsCoercive fun p : ℕ × ℕ∞ => (p.1 : ℝ≥0) := fun r => by
  have hK : IsCompact (Iic ⌊r⌋₊ ×ˢ (univ : Set ℕ∞)) :=
    (finite_Iic _).isCompact.prod isCompact_univ
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal (fun p hp => ?_) hK.isClosed)
  exact ⟨Nat.le_floor hp, mem_univ _⟩

/-- **Counterexample to Proposition 12.1.3 as stated** (MT p. 291, with `Pᵏ`): the
deterministic chain `liminfCexKernel` on `ℕ × ℕ∞` (`nat_prod_enat_standing`) is weak Feller,
`V(k, m) = k` is coercive, and `liminf_k E_{(0,0)}[V(Φₖ)] = 0`, since the orbit of `(0, 0)` returns
to `{V = 0}` at the start of every loop. Yet there is no invariant probability. The returns are
too sparse for the Cesàro means to stay away from `0`, which is what Theorem 12.1.2 needs; the
Cesàro form of the proposition is `proposition_12_1_3`. -/
theorem proposition_12_1_3_counterexample :
    IsMarkovKernel liminfCexKernel ∧ IsWeakFeller liminfCexKernel ∧
      Measurable (fun p : ℕ × ℕ∞ => (p.1 : ℝ≥0)) ∧ IsCoercive (fun p : ℕ × ℕ∞ => (p.1 : ℝ≥0)) ∧
      atTop.liminf (fun k : ℕ => ∫⁻ y, ((y.1 : ℝ≥0) : ℝ≥0∞) ∂(liminfCexKernel ^ k) (0, 0)) = 0 ∧
      ¬ ∃ π : Measure (ℕ × ℕ∞), IsProbabilityMeasure π ∧ IsInvariant liminfCexKernel π := by
  refine ⟨by unfold liminfCexKernel; infer_instance, isWeakFeller_liminfCexKernel, .of_discrete,
    isCoercive_liminfCex, le_antisymm (liminf_le_of_frequently_le' ?_) zero_le,
    liminfCex_no_invariant⟩
  refine frequently_atTop.2 fun N => ?_
  obtain ⟨n, hn, h⟩ := exists_iterate_liminfCexMap N
  refine ⟨n, hn.trans' le_rfl, ?_⟩
  rw [liminfCexKernel_pow_apply, lintegral_dirac, h]
  simp

end MeynTweedie.Positivity

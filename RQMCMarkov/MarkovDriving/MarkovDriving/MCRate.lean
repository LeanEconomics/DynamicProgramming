/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.DrivingMC
import MarkovDriving.MCRateIIDLIL
import MarkovDriving.RotorRouter
import MarkovDriving.StackBound

/-! # The Monte Carlo baseline: the law of the iterated logarithm rate (post #3)

Post #3: "With MC of a Markov Chain the empirical transition matrix converges at `O(1/√T)`
(Meyn & Tweedie, Chpt 17)." In the stack representation with **i.i.d. uniform stacks**
(`IsIIDStacks`; by `DrivingMC` this is the law of MC driving by one i.i.d. sequence), the
departures from `i` are i.i.d. draws from the row `P(i, ·)`, so for a test function `g` the
departure discrepancy is a random-index partial sum `D_i(g, T) = S_{N_i(T)}` of the i.i.d.
centred bounded variables `ξ_k = g(step P i (V i k)) − (Pg)(i)`, with variance
`σ_i²(g) = Σ_j p_ij (g_j − (Pg)(i))²` (`rowVariance`; `= p_ij (1 − p_ij)` for `g = 1_{j}`,
`rowVariance_indicator`). The Hartman–Wintner LIL (copied from `StochasticStability`) gives the
precise almost-sure rate, with `lilScale m = √(2 m log log m)`:

* `hasLIL_mcDepartureSum`: a.s. `limsup S_m / √(2 m log log m) = σ_i(g)`, `liminf = −σ_i(g)`.
* `ae_abs_transCount_mc_le` (**upper rate**): a.s. for every `ε > 0` there is `K` with
  `|N_ij(T) − p_ij N_i(T)| ≤ K + (√(p_ij(1 − p_ij)) + ε) √(2 T log log T)` for all `T`
  (using the random index `N_i(T) ≤ T`); so the empirical transition matrix error is
  `O(√(log log T / T))` a.s.
* `ae_abs_occCount_mc_le`: the occupation error is a.s. `≤ K + C √(2 T log log T)`, with
  `C = Σ_i (σ_i(h) + 1)`; `ae_abs_occCount_mc_le_mul`: the occupation SLLN (`≤ K + ε T` for every
  `ε > 0`), and `ae_tendsto_occCount_mc`: every state with `π_i > 0` is visited infinitely
  often.
* `ae_frequently_transCount_mc_ge` (**lower rate**): if moreover `π_i > 0`, a.s. for every
  `ε > 0`, infinitely often `N_ij(T) − p_ij N_i(T) ≥ (σ − ε) √(2 N log log N)` and infinitely
  often `≤ −(σ − ε) √(2 N log log N)`, with `N = N_i(T)` and `σ = √(p_ij(1 − p_ij))`. So for
  `0 < p_ij < 1` the MC error is not `o(√(N log log N))` (`ae_not_tendsto_transCount_mc`), and MC
  is genuinely slower than the stacks' `O(log T)` and the rotors' `O(1)`.

**Reading of "`O(1/√T)`".** The a.s. error of the empirical transition matrix is of exact
order `√(log log T / T)` (LIL), slightly larger than `1/√T`; `1/√T` is the scale of the CLT
(the root-mean-square error), not an almost-sure bound.

**The unifying statement** (`occupation_error_ranking`, `departureDiscrepancy_ranking`): along
every path, occupation error `≤ 2‖h‖∞ + Σ_i |D_i(h, T)|`; the departure discrepancies are
`O(√(T log log T))` a.s. for MC, `O(log T)` for van der Corput stacks, and `O(1)` for rotors.

`isIIDStacks_iidUniform`: the canonical stack model (`iidUniform (Fin n × ℕ)`) satisfies
`IsIIDStacks`. The LIL itself is the `StochasticStability/LimitTheorems` closure, copied into
the `MCRate*` modules.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Finset Matrix

/-! ### Deterministic lemmas: random indices -/

/-- **Random index bound.** If eventually `|s m| ≤ f m` with `f ≥ 0` eventually monotone, then
there is `K ≥ 0` with `|s N| ≤ K + f T` whenever `N ≤ T`. -/
theorem exists_abs_le_add_of_eventually {s f : ℕ → ℝ} (hf0 : ∀ m, 0 ≤ f m)
    (h : ∀ᶠ m in atTop, |s m| ≤ f m ∧ ∀ m', m ≤ m' → f m ≤ f m') :
    ∃ K, 0 ≤ K ∧ ∀ T N, N ≤ T → |s N| ≤ K + f T := by
  obtain ⟨m0, hm0⟩ := eventually_atTop.1 h
  have hK := sum_nonneg fun m (_ : m ∈ range m0) => abs_nonneg (s m)
  refine ⟨∑ m ∈ range m0, |s m|, hK, fun T N hNT => ?_⟩
  by_cases hN : N < m0
  · have := single_le_sum (fun m _ => abs_nonneg (s m)) (mem_range.2 hN)
    linarith [hf0 T]
  · obtain ⟨h1, h2⟩ := hm0 N (not_lt.1 hN)
    have := h2 T hNT
    linarith

/-- `√(2 m log log m)` is eventually monotone. -/
theorem eventually_lilScale_mono :
    ∀ᶠ m : ℕ in atTop, ∀ m', m ≤ m' → lilScale m ≤ lilScale m' := by
  filter_upwards [lil_eventually_le_log 3] with m hm m' hmm' using lilScale_mono hm hmm'

/-- `√(2 m log log m) = o(m)`: eventually `lilScale m ≤ ε m`. -/
theorem eventually_lilScale_le_mul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, lilScale m ≤ ε * m := by
  have hlogo := Real.isLittleO_log_id_atTop.bound (c := ε ^ 2 / 2) (by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hlogo, eventually_ge_atTop 3]
    with m hm hm3
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hlogpos : 0 < Real.log m := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hlogpos,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ m)] at hm
  have hll : Real.log (Real.log m) ≤ Real.log m :=
    (Real.log_le_sub_one_of_pos hlogpos).trans (by linarith)
  unfold lilScale
  rw [show ε * (m : ℝ) = √((ε * m) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  have h1 : 2 * (m : ℝ) * Real.log (Real.log m) ≤ 2 * m * Real.log m :=
    mul_le_mul_of_nonneg_left hll (by positivity)
  have h2 : 2 * (m : ℝ) * Real.log m ≤ 2 * m * (ε ^ 2 / 2 * m) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  nlinarith

/-- **Discrete intermediate values**: a counter with unit up-steps takes every value between
`N a` and `N b`. -/
theorem exists_eq_of_le_of_le {N : ℕ → ℕ} (hN : ∀ T, N (T + 1) ≤ N T + 1) {a b v : ℕ}
    (hab : a ≤ b) (ha : N a ≤ v) (hb : v ≤ N b) : ∃ T, a ≤ T ∧ T ≤ b ∧ N T = v := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨a, le_rfl, le_rfl, le_antisymm ha hb⟩
  | succ b hab ih =>
    by_cases hv : v ≤ N b
    · obtain ⟨T, h1, h2, h3⟩ := ih hv
      exact ⟨T, h1, by omega, h3⟩
    · exact ⟨b + 1, by omega, le_rfl, by have := hN b; omega⟩

/-- **Transfer of "infinitely often" through a random index**: if `N` is monotone with unit
up-steps and unbounded, and `p m` holds for infinitely many `m`, then `p (N T)` holds for
infinitely many `T`. -/
theorem frequently_comp_of_unbounded {N : ℕ → ℕ} (hmono : Monotone N)
    (hN : ∀ T, N (T + 1) ≤ N T + 1) (hunb : ∀ v, ∃ T, v ≤ N T) {p : ℕ → Prop}
    (hp : ∃ᶠ m in atTop, p m) : ∃ᶠ T in atTop, p (N T) := by
  rw [frequently_atTop] at hp ⊢
  intro T0
  obtain ⟨m, hm, hpm⟩ := hp (N T0)
  obtain ⟨T1, hT1⟩ := hunb m
  obtain ⟨T, h1, -, h3⟩ := exists_eq_of_le_of_le hN (le_max_left T0 T1) hm
    (hT1.trans (hmono (le_max_right T0 T1)))
  exact ⟨T, h1, h3 ▸ hpm⟩

/-! ### i.i.d. stacks -/

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- **i.i.d. uniform stacks**: for each state `i`, the stack `k ↦ V i k` is an i.i.d. sequence
of uniforms on `[0,1)` (independence across states is not needed below). -/
structure IsIIDStacks (Q : Measure Ω) (V : Ω → Fin n → ℕ → ℝ) : Prop where
  measurable : ∀ i k, Measurable fun ω => V ω i k
  indep : ∀ i, iIndepFun (fun k ω => V ω i k) Q
  law : ∀ i k, Q.map (fun ω => V ω i k) = uniformIco

/-- **The canonical i.i.d. stacks** of `DrivingMC`: under `iidUniform (Fin n × ℕ)`, the stacks
`V w i k = w (i, k)` are i.i.d. uniform, so every result below applies to the stack model
`stackPath P x₀ (Function.curry w)` (whose finite-horizon path laws are those of MC driving by a
single i.i.d. sequence, `map_drivenPath_eq_map_stackPath`). -/
theorem isIIDStacks_iidUniform :
    IsIIDStacks (iidUniform (Fin n × ℕ)) (fun w => Function.curry w) := by
  have := isProbabilityMeasure_uniformIco
  refine ⟨fun i k => measurable_pi_apply (i, k), fun i => ?_, fun i k => ?_⟩
  · have h := iIndepFun_infinitePi (P := fun _ : Fin n × ℕ => uniformIco)
      (X := fun _ x => x) (fun _ => measurable_id)
    exact h.precomp (g := fun k => (i, k)) fun a b hab => (Prod.mk.inj hab).2
  · exact Measure.infinitePi_map_eval (μ := fun _ : Fin n × ℕ => uniformIco) (i, k)

/-- The **MC departure process** of state `i`: `S_m = Σ_{k < m} (g(step P i (V i k)) − (Pg)(i))`.
-/
noncomputable def mcDepartureSum (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ)
    (V : Ω → Fin n → ℕ → ℝ) (i : Fin n) (ω : Ω) (m : ℕ) : ℝ :=
  ∑ k ∈ range m, (g (step P i (V ω i k)) - (P *ᵥ g) i)

/-- The variance of `g` under the row `P(i, ·)`: `σ_i²(g) = Σ_j p_ij (g_j − (Pg)(i))²`. -/
noncomputable def rowVariance (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, P i j * (g j - (P *ᵥ g) i) ^ 2

/-- For an indicator, `σ_i²(1_{j}) = p_ij (1 − p_ij)`. -/
theorem rowVariance_indicator {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    rowVariance P (fun k => if k = j then 1 else 0) i = P i j * (1 - P i j) := by
  unfold rowVariance
  rw [mulVec_indicator (P : Matrix (Fin n) (Fin n) ℝ) i j]
  have e : ∀ k, P i k * ((if k = j then (1 : ℝ) else 0) - P i j) ^ 2 =
      (1 - 2 * P i j) * (P i k * if k = j then 1 else 0) + P i j ^ 2 * P i k := fun k => by
    split_ifs <;> ring
  rw [sum_congr rfl fun k _ => e k, sum_add_distrib, ← mul_sum, ← mul_sum, hP.sum_eq_one i]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ite_true]
  ring

/-- **The law of one departure**: `E φ(step P i (V i k)) = Σ_j p_ij φ_j`. -/
theorem integral_comp_step {Q : Measure Ω} [IsProbabilityMeasure Q] {V : Ω → Fin n → ℕ → ℝ}
    (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) (k : ℕ)
    (φ : Fin n → ℝ) : ∫ ω, φ (step P i (V ω i k)) ∂Q = ∑ j, P i j * φ j := by
  have hmeas : Measurable fun ω => step P i (V ω i k) :=
    (measurable_step P i).comp (hV.measurable i k)
  rw [← integral_map hmeas.aemeasurable (measurable_of_finite φ).aestronglyMeasurable]
  rw [integral_fintype Integrable.of_finite]
  refine sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, measureReal_def, Measure.map_apply hmeas (measurableSet_singleton j)]
  have e : (fun ω => step P i (V ω i k)) ⁻¹' {j} =
      (fun ω => V ω i k) ⁻¹' {u | step P i u = j} := rfl
  have hms : MeasurableSet {u | step P i u = j} :=
    (measurable_step P i) (measurableSet_singleton j)
  rw [e, ← Measure.map_apply (hV.measurable i k) hms, hV.law i k, uniformIco_step_eq hP i j,
    ENNReal.toReal_ofReal (hP.nonneg i j)]

/-- **The LIL for the MC departures**: almost surely the departure process of `i` obeys the LIL
with constant `σ_i(g) = √(rowVariance P g i)`. -/
theorem hasLIL_mcDepartureSum {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (g : Fin n → ℝ) (i : Fin n) :
    ∀ᵐ ω ∂Q, HasLIL (mcDepartureSum P g V i ω) (√(rowVariance P g i)) := by
  set c := (P *ᵥ g) i with hc
  set ψ : ℝ → ℝ := fun u => g (step P i u) - c with hψdef
  have hψ : Measurable ψ := (measurable_of_finite fun j => g j - c).comp (measurable_step P i)
  set X : ℕ → Ω → ℝ := fun k ω => ψ (V ω i k) with hX
  have hind : iIndepFun X Q := (hV.indep i).comp (fun _ => ψ) fun _ => hψ
  have hm : ∀ k, Measurable (X k) := fun k => hψ.comp (hV.measurable i k)
  have hident : ∀ k, IdentDistrib (X k) (X 0) Q Q := fun k =>
    (IdentDistrib.mk (hV.measurable i k).aemeasurable (hV.measurable i 0).aemeasurable
      (by rw [hV.law i k, hV.law i 0])).comp hψ
  have hL2 : MemLp (X 0) 2 Q := by
    refine MemLp.of_bound (hm 0).aestronglyMeasurable (∑ j, |g j - c|)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact single_le_sum (f := fun j => |g j - c|) (fun j _ => abs_nonneg _) (mem_univ _)
  have h0 : ∫ ω, X 0 ω ∂Q = 0 := by
    rw [integral_comp_step hV hP i 0 (fun j => g j - c)]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hP.sum_eq_one i, one_mul]
    rw [hc]
    simp only [mulVec, dotProduct]
    exact sub_self _
  have hvar : ∫ ω, X 0 ω ^ 2 ∂Q = rowVariance P g i :=
    integral_comp_step hV hP i 0 (fun j => (g j - c) ^ 2)
  have hlil := hasLIL_iid hind hm hident hL2 h0
  rw [hvar] at hlil
  exact hlil

omit [MeasurableSpace Ω] in
/-- The departure discrepancy of the MC stack path is the departure process at the random
index `N_i(T)`. -/
theorem departureDiscrepancy_mc_eq (P : Fin n → Fin n → ℝ) (x₀ : Fin n)
    (V : Ω → Fin n → ℕ → ℝ) (g : Fin n → ℝ) (i : Fin n) (ω : Ω) (T : ℕ) :
    departureDiscrepancy P g (stackPath P x₀ (V ω)) i T =
      mcDepartureSum P g V i ω (occCount (stackPath P x₀ (V ω)) i T) :=
  departureDiscrepancy_stackDrive P g (step P) x₀ (V ω) i T

/-- Under the LIL with constant `σ`, eventually `|s m| ≤ (σ + ε) √(2 m log log m)`. -/
theorem HasLIL.eventually_abs_le {s : ℕ → ℝ} {σ : ℝ} (h : HasLIL s σ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, |s m| ≤ (σ + ε) * lilScale m := by
  filter_upwards [(h.1 ε hε).1, (h.2 ε hε).1] with m h1 h2
  exact abs_le.2 ⟨by linarith, h1⟩

/-- **MC departure discrepancies are `O(√(T log log T))` a.s.**: for every `ε > 0` there is `K`
with `|D_i(g, T)| ≤ K + (σ_i(g) + ε) √(2 T log log T)` for all `T`. -/
theorem ae_abs_departureDiscrepancy_mc_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) (g : Fin n → ℝ) (i : Fin n) :
    ∀ᵐ ω ∂Q, ∀ ε > 0, ∃ K, ∀ T, |departureDiscrepancy P g (stackPath P x₀ (V ω)) i T| ≤
      K + (√(rowVariance P g i) + ε) * lilScale T := by
  filter_upwards [hasLIL_mcDepartureSum hV hP g i] with ω hω ε hε
  have hσε : 0 ≤ √(rowVariance P g i) + ε := by positivity
  obtain ⟨K, -, hK⟩ := exists_abs_le_add_of_eventually
    (f := fun m => (√(rowVariance P g i) + ε) * lilScale m)
    (fun m => mul_nonneg hσε (lilScale_nonneg m))
    ((hω.eventually_abs_le hε).and (eventually_lilScale_mono.mono fun m hm m' hmm' =>
      mul_le_mul_of_nonneg_left (hm m' hmm') hσε))
  exact ⟨K, fun T => by
    rw [departureDiscrepancy_mc_eq]
    exact hK T _ (occCount_le _ _ _)⟩

/-- **MC departure discrepancies are `o(T)` a.s.**: for every `ε > 0` there is `K` with
`|D_i(g, T)| ≤ K + ε T` for all `T`. -/
theorem ae_abs_departureDiscrepancy_mc_le_mul {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) (g : Fin n → ℝ) (i : Fin n) :
    ∀ᵐ ω ∂Q, ∀ ε > 0, ∃ K, ∀ T, |departureDiscrepancy P g (stackPath P x₀ (V ω)) i T| ≤
      K + ε * T := by
  filter_upwards [hasLIL_mcDepartureSum hV hP g i] with ω hω ε hε
  set σ := √(rowVariance P g i)
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hev : ∀ᶠ m in atTop, |mcDepartureSum P g V i ω m| ≤ ε * m := by
    filter_upwards [hω.eventually_abs_le one_pos,
      eventually_lilScale_le_mul (ε := ε / (σ + 1)) (by positivity)] with m h1 h2
    have h3 : (σ + 1) * lilScale m ≤ (σ + 1) * (ε / (σ + 1) * m) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (σ + 1) * (ε / (σ + 1) * m) = ε * m := by field_simp
    linarith
  obtain ⟨K, -, hK⟩ := exists_abs_le_add_of_eventually (f := fun m => ε * m)
    (fun m => mul_nonneg hε.le (Nat.cast_nonneg m))
    (hev.mono fun m hm => ⟨hm, fun m' hmm' => mul_le_mul_of_nonneg_left
      (by exact_mod_cast hmm') hε.le⟩)
  exact ⟨K, fun T => by
    rw [departureDiscrepancy_mc_eq]
    exact hK T _ (occCount_le _ _ _)⟩

/-- **MC transition counts, upper LIL rate** (post #3's "`O(1/√T)`", made precise): a.s., for
every `ε > 0` there is `K` with `|N_ij(T) − p_ij N_i(T)| ≤ K + (√(p_ij (1 − p_ij)) + ε)
√(2 T log log T)` for all `T`. -/
theorem ae_abs_transCount_mc_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) (i j : Fin n) :
    ∀ᵐ ω ∂Q, ∀ ε > 0, ∃ K, ∀ T,
      |(transCount (stackPath P x₀ (V ω)) i j T : ℝ) - P i j * occCount (stackPath P x₀ (V ω)) i T|
        ≤ K + (√(P i j * (1 - P i j)) + ε) * lilScale T := by
  filter_upwards [ae_abs_departureDiscrepancy_mc_le hV hP x₀ (fun k => if k = j then 1 else 0) i]
    with ω hω ε hε
  obtain ⟨K, hK⟩ := hω ε hε
  refine ⟨K, fun T => ?_⟩
  rw [transCount_sub_eq_departureDiscrepancy (P : Matrix (Fin n) (Fin n) ℝ) _ i j T,
    ← rowVariance_indicator hP i j]
  exact hK T

/-- **MC occupation error, LIL rate**: a.s. `|N_s(T) − T π_s| ≤ K + C √(2 T log log T)` for all
`T`, with `C = Σ_i (σ_i(h) + 1)`, where `h − Ph = 1_{s} − π_s` and `|h| ≤ M`. -/
theorem ae_abs_occCount_mc_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M) :
    ∀ᵐ ω ∂Q, ∃ K, ∀ T, |(occCount (stackPath P x₀ (V ω)) s T : ℝ) - T * μs| ≤
      K + (∑ i, (√(rowVariance P h i) + 1)) * lilScale T := by
  have hall := ae_all_iff.2 fun i => ae_abs_departureDiscrepancy_mc_le hV hP x₀ h i
  filter_upwards [hall] with ω hω
  choose K hK using fun i => hω i 1 one_pos
  refine ⟨2 * M + ∑ i, K i, fun T => ?_⟩
  refine (abs_occCount_sub_le P hh hM _ T).trans ?_
  have := sum_le_sum fun i (_ : i ∈ univ) => hK i T
  rw [sum_add_distrib, ← sum_mul] at this
  linarith

/-- **MC occupation SLLN**: a.s., for every `ε > 0` there is `K` with
`|N_s(T) − T π_s| ≤ K + ε T` for all `T`. -/
theorem ae_abs_occCount_mc_le_mul {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M) :
    ∀ᵐ ω ∂Q, ∀ ε > 0, ∃ K, ∀ T, |(occCount (stackPath P x₀ (V ω)) s T : ℝ) - T * μs| ≤
      K + ε * T := by
  have hall := ae_all_iff.2 fun i => ae_abs_departureDiscrepancy_mc_le_mul hV hP x₀ h i
  filter_upwards [hall] with ω hω ε hε
  choose K hK using fun i => hω i (ε / (n + 1)) (by positivity)
  refine ⟨2 * M + ∑ i, K i, fun T => ?_⟩
  refine (abs_occCount_sub_le P hh hM _ T).trans ?_
  have := sum_le_sum fun i (_ : i ∈ univ) => hK i T
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have hle : (n : ℝ) * (ε / (n + 1) * T) ≤ ε * T := by
    have hn1 : (n : ℝ) / (n + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have : (n : ℝ) * (ε / (n + 1) * T) = (n / (n + 1)) * (ε * T) := by ring
    rw [this]
    exact mul_le_of_le_one_left (by positivity) hn1
  linarith

/-- **MC visits every charged state infinitely often** (a.s.): if `π_s > 0` then
`N_s(T) → ∞`. -/
theorem ae_tendsto_occCount_mc {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M)
    (hμ : 0 < μs) :
    ∀ᵐ ω ∂Q, ∀ v : ℕ, ∃ T, v ≤ occCount (stackPath P x₀ (V ω)) s T := by
  filter_upwards [ae_abs_occCount_mc_le_mul hV hP x₀ hh hM] with ω hω v
  obtain ⟨K, hK⟩ := hω (μs / 2) (by positivity)
  obtain ⟨T, hT⟩ := exists_nat_gt (2 * (K + v) / μs)
  refine ⟨T, ?_⟩
  have h1 := (abs_le.1 (hK T)).1
  have h2 : 2 * (K + v) < T * μs := by rwa [div_lt_iff₀ hμ] at hT
  have : (v : ℝ) ≤ occCount (stackPath P x₀ (V ω)) s T := by nlinarith
  exact_mod_cast this

/-- **MC transition counts, lower LIL rate**: if `π_i > 0` (e.g. `P` irreducible), a.s. for
every `ε > 0`, infinitely often `N_ij(T) − p_ij N_i(T) ≥ (σ − ε) √(2 N log log N)`, and
infinitely often `N_ij(T) − p_ij N_i(T) ≤ −(σ − ε) √(2 N log log N)`, where `N = N_i(T)` and
`σ = √(p_ij (1 − p_ij))`. -/
theorem ae_frequently_transCount_mc_ge {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {i : Fin n} {μi M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - μi) (hM : ∀ k, |h k| ≤ M)
    (hμ : 0 < μi) (j : Fin n) :
    ∀ᵐ ω ∂Q, ∀ ε > 0,
      (∃ᶠ T in atTop, (√(P i j * (1 - P i j)) - ε) *
          lilScale (occCount (stackPath P x₀ (V ω)) i T) ≤
        (transCount (stackPath P x₀ (V ω)) i j T : ℝ) -
          P i j * occCount (stackPath P x₀ (V ω)) i T) ∧
      ∃ᶠ T in atTop, (transCount (stackPath P x₀ (V ω)) i j T : ℝ) -
          P i j * occCount (stackPath P x₀ (V ω)) i T ≤
        -((√(P i j * (1 - P i j)) - ε) * lilScale (occCount (stackPath P x₀ (V ω)) i T)) := by
  filter_upwards [hasLIL_mcDepartureSum hV hP (fun k => if k = j then 1 else 0) i,
    ae_tendsto_occCount_mc hV hP x₀ hh hM hμ] with ω hω hunb ε hε
  rw [rowVariance_indicator hP i j] at hω
  set x := stackPath P x₀ (V ω)
  have hmono : Monotone fun T => occCount x i T := fun _ _ hab => occCount_mono x i hab
  have hstep : ∀ T, occCount x i (T + 1) ≤ occCount x i T + 1 := fun T => by
    rw [occCount_succ]
    split_ifs <;> omega
  have e : ∀ T, (transCount x i j T : ℝ) - P i j * occCount x i T =
      mcDepartureSum P (fun k => if k = j then 1 else 0) V i ω (occCount x i T) := fun T => by
    rw [transCount_sub_eq_departureDiscrepancy (P : Matrix (Fin n) (Fin n) ℝ) x i j T,
      departureDiscrepancy_mc_eq]
  refine ⟨?_, ?_⟩
  · refine (frequently_comp_of_unbounded hmono hstep hunb (hω.1 ε hε).2).mono fun T hT => ?_
    rw [e T]
    exact hT
  · refine (frequently_comp_of_unbounded hmono hstep hunb (hω.2 ε hε).2).mono fun T hT => ?_
    rw [e T]
    linarith

/-- **MC is not `o(√(N log log N))`-accurate**: for `0 < p_ij < 1` and `π_i > 0`, almost surely
`(N_ij(T) − p_ij N_i(T)) / √(2 N_i(T) log log N_i(T))` does not tend to `0`. -/
theorem ae_not_tendsto_transCount_mc {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {i : Fin n} {μi M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - μi) (hM : ∀ k, |h k| ≤ M)
    (hμ : 0 < μi) {j : Fin n} (hp0 : 0 < P i j) (hp1 : P i j < 1) :
    ∀ᵐ ω ∂Q, ¬ Tendsto (fun T => ((transCount (stackPath P x₀ (V ω)) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ (V ω)) i T) /
          lilScale (occCount (stackPath P x₀ (V ω)) i T)) atTop (nhds 0) := by
  filter_upwards [ae_frequently_transCount_mc_ge hV hP x₀ hh hM hμ j,
    ae_tendsto_occCount_mc hV hP x₀ hh hM hμ] with ω hω hunb htend
  set x := stackPath P x₀ (V ω)
  set σ := √(P i j * (1 - P i j))
  have hσ : 0 < σ := Real.sqrt_pos.2 (mul_pos hp0 (by linarith))
  obtain ⟨hfr, -⟩ := hω (σ / 2) (by positivity)
  have hsmall := htend.eventually (gt_mem_nhds (show (0 : ℝ) < σ / 2 by positivity))
  have htop : Tendsto (fun T => occCount x i T) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ hab => occCount_mono x i hab) hunb
  have hpos : ∀ᶠ T in atTop, 0 < lilScale (occCount x i T) :=
    (htop.eventually (lil_eventually_le_log 3)).mono fun T hT => lilScale_pos hT
  obtain ⟨T, hT1, hT2, hT3⟩ := (hfr.and_eventually (hsmall.and hpos)).exists
  have h2 := hT2
  rw [div_lt_iff₀ hT3] at h2
  nlinarith

/-! ### The unifying statement -/

/-- **The ranking of post #3, for the departure discrepancies.** For a stochastic `P` and a test
function `g` with `|g| ≤ M`:
1. van der Corput stacks: `|D_i(g, T)| ≤ V(g) (⌊log₂ T⌋ + 1)`, i.e. `O(log T)`;
2. rotors (balanced cycles of lengths `L`): `|D_i(g, T)| ≤ 2 (L i − 1) M`, i.e. `O(1)`;
3. MC (i.i.d. uniform stacks): a.s., for every `ε > 0`, `|D_i(g, T)| ≤ K + (σ_i(g) + ε)
   √(2 T log log T)`, i.e. `O(√(T log log T))`. -/
theorem departureDiscrepancy_ranking {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    {g : Fin n → ℝ} {M : ℝ} (hM : ∀ j, |g j| ≤ M) (i : Fin n) :
    (∀ T, |departureDiscrepancy P g (stackPath P x₀ fun _ => vanDerCorput) i T| ≤
        stateVariation g * ((Nat.log 2 T : ℝ) + 1)) ∧
      (∀ (L : Fin n → ℕ) (c : Fin n → ℕ → Fin n), IsRotorCycle P L c → ∀ θ T,
        |departureDiscrepancy P g (rotorWalk L c θ x₀) i T| ≤ (L i - 1 : ℕ) * (2 * M)) ∧
      (IsIIDStacks Q V → ∀ᵐ ω ∂Q, ∀ ε > 0, ∃ K, ∀ T,
        |departureDiscrepancy P g (stackPath P x₀ (V ω)) i T| ≤
          K + (√(rowVariance P g i) + ε) * lilScale T) := by
  refine ⟨fun T => ?_, fun L c hc θ T => ?_,
    fun hV => ae_abs_departureDiscrepancy_mc_le hV hP x₀ g i⟩
  · exact (abs_departureDiscrepancy_stackPath_le hP x₀ (fun _ k => vanDerCorput_mem_Ico k) g i
      T).trans (mul_le_mul_of_nonneg_left (mul_starDiscrepancy_vdc_le (occCount_le _ _ _))
        (stateVariation_nonneg g))
  · exact abs_departureDiscrepancy_rotorWalk_le_two_mul hP.nonneg hP.sum_eq_one hc θ x₀ hM i T

/-- **The unifying theorem** (post #3's ranking of MC, QMC stacks and rotors). Let `h` solve
Poisson's equation `h − Ph = 1_{s} − π_s` with `|h| ≤ M`. Then:
0. along **every** path, `|N_s(T) − T π_s| ≤ 2M + Σ_i |D_i(h, T)|` (boundary + departure
   discrepancies);
1. van der Corput stacks: `|N_s(T) − T π_s| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)` (`O(log T)`);
2. rotors: `|N_s(T) − T π_s| ≤ 2M (1 + Σ_i (L i − 1))` (`O(1)`, Holroyd–Propp);
3. MC: a.s. `|N_s(T) − T π_s| ≤ K + C √(2 T log log T)` (`O(√(T log log T))`). -/
theorem occupation_error_ranking {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    {h : Fin n → ℝ} {s : Fin n} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M) :
    (∀ (x : ℕ → Fin n) T, |(occCount x s T : ℝ) - T * μs| ≤
        2 * M + ∑ i, |departureDiscrepancy P h x i T|) ∧
      (∀ T, |(occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) - T * μs| ≤
        2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1)) ∧
      (∀ (L : Fin n → ℕ) (c : Fin n → ℕ → Fin n), IsRotorCycle P L c → ∀ θ T,
        |(occCount (rotorWalk L c θ x₀) s T : ℝ) - T * μs| ≤
          2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ))) ∧
      (IsIIDStacks Q V → ∀ᵐ ω ∂Q, ∃ K, ∀ T,
        |(occCount (stackPath P x₀ (V ω)) s T : ℝ) - T * μs| ≤
          K + (∑ i, (√(rowVariance P h i) + 1)) * lilScale T) :=
  ⟨fun x T => abs_occCount_sub_le P hh hM x T, fun T => abs_occCount_vdc_sub_le hP x₀ hh hM T,
    fun _ _ hc θ T => abs_occCount_rotorWalk_sub_le hP.nonneg hP.sum_eq_one hc θ x₀ hh hM T,
    fun hV => ae_abs_occCount_mc_le hV hP x₀ hh hM⟩

end RQMCMarkov.MarkovDriving

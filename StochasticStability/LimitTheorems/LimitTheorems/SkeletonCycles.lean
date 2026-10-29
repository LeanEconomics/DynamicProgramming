/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.SkeletonSplit
import LimitTheorems.SkeletonOneDependent

/-!
# The cycle sums of a split `m`-skeleton (MT §17.3.1, Theorem 17.3.1)

Meyn and Tweedie, pp. 434–435. On the chain on blocks of `SkeletonSplit` (`skelKernel M`), the
visits of the split `m`-skeleton to `α̌ = C × {1}` are the visits to `skelAtom M`. The visit
times are the project's `renewalTime (skelAtom M) j = σ_α̌(j)`, and the path is restarted after
each visit by `restart`.

**The cycle sums.**
* `skelPreSum M f = s₋₁(f) = Σ_{t < m(σ_α̌(0)+1)} f(Φₜ)`, the sum up to the end of the block that
  follows the first visit; under `P̌_{ν*}` this is the variable of (17.22).
* `skelCycle M f j = sⱼ(f)`; `skelCycle_eq`: `sⱼ(f) = Σ f(Φₜ)` over
  `m(σ_α̌(j)+1) ≤ t < m(σ_α̌(j+1)+1)`, the book's definition (MT p. 434);
  `sum_range_renewal_eq`: the decomposition (17.24).
* `skelSeq M f ω = (s₋₁, s₀, s₁, …)`.

**Regeneration.** After a visit, the next block depends on the state at the visit (MT (17.21)),
but the skeleton state at the end of that block is fresh. `skelFresh` replaces the state at
time `0` by the virtual state with the same skeleton state, and `skelFreshLaw M = P̌_{λ_ν}` is
the law of the chain on blocks started afresh from `ν*`.
* `pathMeasure_map_skelFresh`, `pathKernel_map_skelFresh_shift`: from a state over `α̌` the fresh
  future after the next block has law `P̌_{λ_ν}`.
* `lintegral_mul_skelRestart` (the strong Markov property at `σ_α̌`) and
  `lintegral_mul_restart_succ` (at `σ_α̌ + 1`, for any chain).
* **`skel_regeneration`** (the induction behind MT p. 435): `(s₋₁, …, s_{k−2})` is independent of
  the future after the end of the block following the `(k+1)`-th visit, whose fresh law is
  `P̌_{λ_ν}`; `skel_box` is its box form.

**Theorem 17.3.1.**
* `skel_map_cycles`: `(s_c, s_{c+1}, …)` has, for every `c`, the law of `(s₋₁, s₀, …)` under
  `P̌_{λ_ν}`; `skel_isStationarySeq`, `skel_isOneDependent`, `skel_map_cycle` (17.22).
* **Theorem 17.3.1** (`theorem_17_3_1_general`, p. 435), for every `m ≥ 1`: the cycle sums are
  stationary and one-dependent, each has the law (17.22), and the even and the odd cycle sums
  are each i.i.d.
* **(17.23)** (`theorem_17_3_1_general_mean`): for a Harris `m`-skeleton, `C ∈ B⁺(X)` and an
  invariant `π` of `P` with `0 < π(C) < ∞`, `Ě[sⱼ(f)] = δ⁻¹ π(C)⁻¹ m ∫ f dπ` for `f ∈ L¹(π)`.
  The proof conditions each block on the skeleton state at its start (`lintegral_skelPreSumE`,
  `blockMeanE`), uses the cycle formula (17.10) of the split skeleton and its invariant measure
  `π* = π*(α̌) μ°_α̌` (Theorem 10.2.1), and the recovery of the original chain
  (`lintegral_blockMeanE_split`: `∫ blockMeanE dπ* = m ∫ f dπ`).

**Corrections.** The book's statement of Theorem 17.3.1 is garbled in print (the two index sets
`{0 ≤ j ≤ m − 2}` and `{j ≥ m}` use `m` for an index); its proof proves, and later uses, that
`(sⱼ)` is stationary and one-dependent, which is what is formalised. The common law of the `sⱼ`
holds for every `j ≥ 0`, including `j = 0` (the book's proof says `n ≥ 1`). The proof's remark
that, given `s₀, …, sₙ`, every `s_{n+j}` (`j ≥ 1`) has the unconditional law is only right for
`j ≥ 2`: `sₙ` and `s_{n+1}` both depend on the block that follows the visit at `σ_α̌(n+1)`, so
consecutive cycle sums are in general dependent, which is why the book (and `skel_isOneDependent`)
works with one-dependence.

**Hypotheses.** The book has a Harris recurrent split skeleton (§17.3.1); the regeneration
theorem only needs that the split skeleton reaches `α̌` almost surely from every state (the
first clause of (17.31)), and the mean (17.23) that the `m`-skeleton is Harris.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X} {m : ℕ}

/-! ### The atom of the split skeleton, read on the chain on blocks -/

/-- The states `(b, i)` of the chain on blocks whose skeleton state is in `α̌ = C × {1}`. -/
def skelAtom [NeZero m] (M : Minorization (P ^ m)) : Set ((Fin m → X) × Bool) :=
  skelState ⁻¹' M.checkAlpha

/-- `skelAtom` is measurable. -/
theorem measurableSet_skelAtom [NeZero m] (M : Minorization (P ^ m)) :
    MeasurableSet (skelAtom M) :=
  measurable_skelState M.measurableSet_checkAlpha

/-- The *fresh* path: the state at time `0` is replaced by the virtual state with the same
skeleton state; the rest of the path is kept. -/
def skelFresh [NeZero m] (ω : ℕ → (Fin m → X) × Bool) : ℕ → (Fin m → X) × Bool :=
  fun n => if n = 0 then skelVirt (skelState (ω 0)) else ω n

/-- `skelFresh` is measurable. -/
theorem measurable_skelFresh [NeZero m] : Measurable (skelFresh (X := X) (m := m)) := by
  refine measurable_pi_iff.2 fun n => ?_
  by_cases hn : n = 0
  · simp only [skelFresh, hn, ↓reduceIte]
    exact measurable_skelVirt.comp (measurable_skelState.comp (measurable_pi_apply 0))
  · simp only [skelFresh, hn, ↓reduceIte]
    exact measurable_pi_apply n

omit [MeasurableSpace X] in
/-- `skelFresh` keeps the skeleton states. -/
theorem skelState_skelFresh [NeZero m] (ω : ℕ → (Fin m → X) × Bool) (n : ℕ) :
    skelState (skelFresh ω n) = skelState (ω n) := by
  by_cases hn : n = 0
  · subst hn; rfl
  · simp [skelFresh, hn]

/-- `skelFresh` does not change the visits to the atom. -/
theorem firstHit_skelFresh [NeZero m] (M : Minorization (P ^ m))
    (ω : ℕ → (Fin m → X) × Bool) :
    firstHit (skelAtom M) (skelFresh ω) = firstHit (skelAtom M) ω := by
  have h : ∀ n, skelFresh ω n ∈ skelAtom M ↔ ω n ∈ skelAtom M := fun n => by
    simp only [skelAtom, mem_preimage, skelState_skelFresh]
  cases hω : firstHit (skelAtom M) ω with
  | top =>
    rw [firstHit, hittingAfter_eq_top_iff]
    intro j _ hj
    have : firstHit (skelAtom M) ω ≠ ⊤ := by
      rw [firstHit]
      exact ne_of_lt (lt_of_le_of_lt (hittingAfter_le_of_mem (Nat.zero_le j) ((h j).1 hj))
        (WithTop.coe_lt_top j))
    exact this hω
  | coe n =>
    have h2 := (firstHit_eq_coe_iff _ ω n).1 hω
    exact (firstHit_eq_coe_iff _ _ n).2 ⟨(h n).2 h2.1, fun j hj hjA => h2.2 j hj ((h j).1 hjA)⟩

/-- `hitNat ∘ skelFresh = hitNat`. -/
theorem hitNat_skelFresh [NeZero m] (M : Minorization (P ^ m)) (ω : ℕ → (Fin m → X) × Bool) :
    hitNat (skelAtom M) (skelFresh ω) = hitNat (skelAtom M) ω := by
  rw [hitNat, hitNat, firstHit_skelFresh]

/-- `restart ∘ skelFresh = restart`. -/
theorem restart_skelFresh [NeZero m] (M : Minorization (P ^ m)) (ω : ℕ → (Fin m → X) × Bool) :
    restart (skelAtom M) (skelFresh ω) = restart (skelAtom M) ω := by
  funext i
  simp only [restart, hitNat_skelFresh, shift_apply, skelFresh]
  simp

omit [MeasurableSpace X] in
/-- `skelRecover ∘ skelFresh = skelRecover`. -/
theorem skelRecover_skelFresh [NeZero m] (ω : ℕ → (Fin m → X) × Bool) :
    skelRecover (skelFresh ω) = skelRecover ω := by
  ext t
  by_cases ht : t = 0
  · subst ht; rfl
  · simp [skelRecover, unblock, ht, skelFresh]

omit [MeasurableSpace X] in
/-- Recovery commutes with the shift: `Φₜ(θⁿ V) = Φ_{mn+t}(V)`. -/
theorem skelRecover_shift [NeZero m] (ω : ℕ → (Fin m → X) × Bool) (n t : ℕ) :
    skelRecover (shift n ω) t = skelRecover ω (m * n + t) := by
  have hm := NeZero.pos m
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  by_cases ht : t = 0
  · subst ht
    simp only [skelRecover, unblock, ↓reduceIte, shift_apply, add_zero, blockLast]
    have h1 : m * n ≠ 0 := Nat.mul_ne_zero hm.ne' hn.ne'
    simp only [h1, ↓reduceIte]
    have h2 : (m * n - 1) / m + 1 = n := by
      have : m * n - 1 = m * (n - 1) + (m - 1) := by
        rcases n with _ | n
        · omega
        · rw [Nat.mul_succ]; simp only [Nat.add_sub_cancel]; omega
      rw [this, Nat.mul_add_div hm, Nat.div_eq_of_lt (by omega)]
      omega
    have h3 : (m * n - 1) % m = m - 1 := by
      have : m * n - 1 = m * (n - 1) + (m - 1) := by
        rcases n with _ | n
        · omega
        · rw [Nat.mul_succ]; simp only [Nat.add_sub_cancel]; omega
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    simp only [h2]
    exact congrArg _ (Fin.mk.inj_iff.2 h3.symm)
  · simp only [skelRecover, unblock, ht, ↓reduceIte, shift_apply]
    have h1 : m * n + t ≠ 0 := by omega
    simp only [h1, ↓reduceIte]
    have h2 : (m * n + t - 1) = m * n + (t - 1) := by omega
    have h3 : (m * n + t - 1) / m + 1 = n + ((t - 1) / m + 1) := by
      rw [h2, Nat.mul_add_div hm]; ring
    have h4 : (m * n + t - 1) % m = (t - 1) % m := by
      rw [h2, Nat.mul_add_mod]
    simp only [h3]
    exact congrArg _ (Fin.mk.inj_iff.2 h4.symm)

omit [MeasurableSpace X] in
/-- Recovery only uses the path up to block `n` for the times `t ≤ mn`. -/
theorem skelRecover_congr [NeZero m] {ω ω' : ℕ → (Fin m → X) × Bool} {n : ℕ}
    (h : ∀ i ≤ n, ω i = ω' i) {t : ℕ} (ht : t ≤ m * n) :
    skelRecover ω t = skelRecover ω' t := by
  have hm := NeZero.pos m
  by_cases ht0 : t = 0
  · subst ht0
    simp only [skelRecover, unblock, ↓reduceIte, h 0 (Nat.zero_le n)]
  · simp only [skelRecover, unblock, ht0, ↓reduceIte]
    have : (t - 1) / m + 1 ≤ n := by
      have h1 : (t - 1) / m < n := by
        rw [Nat.div_lt_iff_lt_mul hm]
        have := Nat.mul_comm m n
        omega
      omega
    rw [h _ this]


/-! ### The cycle sums `sᵢ(f)` -/

/-- The initial segment sum `Σ_{t < m(σ_α̌ + 1)} f(Φₜ)`: the sum of `f` over the original time
interval up to the end of the block that follows the first visit of the split skeleton to `α̌`.
Under `P̌_{ν*}` this is the variable of (17.22). -/
noncomputable def skelPreSum [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ)
    (ω : ℕ → (Fin m → X) × Bool) : ℝ :=
  ∑ t ∈ Finset.range (m * (hitNat (skelAtom M) ω + 1)), f (skelRecover ω t)

/-- **The cycle sums** `sⱼ(f)` (MT p. 434): the sum of `f(Φₜ)` over the original time interval
`m(σ_α̌(j) + 1) ≤ t < m(σ_α̌(j + 1) + 1)` between the ends of the blocks following the `(j + 1)`-th
and `(j + 2)`-th visits of the split skeleton to `α̌` (`skelCycle_eq`). -/
noncomputable def skelCycle [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ) (j : ℕ)
    (ω : ℕ → (Fin m → X) × Bool) : ℝ :=
  skelPreSum M f ((restart (skelAtom M))^[j + 1] ω)

omit [MeasurableSpace X] in
/-- The `(j + 1)`-th restart is the shift by `σ_α(j) + 1`. -/
theorem restart_iterate_succ {α : Set X} (j : ℕ) (ω : ℕ → X) :
    (restart α)^[j + 1] ω = shift (renewalTime α j ω + 1) ω := by
  induction j generalizing ω with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [renewalTime, restart, shift_shift, Nat.add_assoc]

/-- `skelPreSum ∘ skelFresh = skelPreSum`. -/
theorem skelPreSum_skelFresh [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ)
    (ω : ℕ → (Fin m → X) × Bool) : skelPreSum M f (skelFresh ω) = skelPreSum M f ω := by
  rw [skelPreSum, skelPreSum, hitNat_skelFresh, skelRecover_skelFresh]

/-- The restarts do not see `skelFresh`. -/
theorem restart_iterate_skelFresh [NeZero m] (M : Minorization (P ^ m)) (j : ℕ)
    (ω : ℕ → (Fin m → X) × Bool) :
    (restart (skelAtom M))^[j + 1] (skelFresh ω) = (restart (skelAtom M))^[j + 1] ω := by
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, restart_skelFresh]

/-- **The cycle sums in the book's form** (MT p. 434): `sⱼ(f) = Σ f(Φₜ)` over
`m(σ_α̌(j) + 1) ≤ t < m(σ_α̌(j + 1) + 1)`. -/
theorem skelCycle_eq [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ) (j : ℕ)
    (ω : ℕ → (Fin m → X) × Bool) :
    skelCycle M f j ω = ∑ t ∈ Finset.Ico (m * (renewalTime (skelAtom M) j ω + 1))
      (m * (renewalTime (skelAtom M) (j + 1) ω + 1)), f (skelRecover ω t) := by
  rw [skelCycle, skelPreSum, restart_iterate_succ, Finset.sum_Ico_eq_sum_range]
  have h1 : hitNat (skelAtom M) ((restart (skelAtom M))^[j + 1] ω) =
      hitNat (skelAtom M) (cycle (skelAtom M) (j + 1) ω) := by
    rw [cycle, hitNat_excursion]
  have h2 := renewalTime_succ (skelAtom M) j ω
  rw [← restart_iterate_succ, h1]
  have h3 : m * (renewalTime (skelAtom M) (j + 1) ω + 1) -
      m * (renewalTime (skelAtom M) j ω + 1) =
      m * (hitNat (skelAtom M) (cycle (skelAtom M) (j + 1) ω) + 1) := by
    rw [h2, ← Nat.mul_sub]
    congr 1
    omega
  rw [h3]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [restart_iterate_succ, skelRecover_shift]

/-- The partial sums up to the end of the block after the `(j + 1)`-th visit: the cycle
decomposition (17.24), `Σ_{t < m(σ_α̌(j)+1)} f(Φₜ) = s₋₁(f) + Σ_{i < j} sᵢ(f)`. -/
theorem sum_range_renewal_eq [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ) (j : ℕ)
    (ω : ℕ → (Fin m → X) × Bool) :
    ∑ t ∈ Finset.range (m * (renewalTime (skelAtom M) j ω + 1)), f (skelRecover ω t) =
      skelPreSum M f ω + ∑ i ∈ Finset.range j, skelCycle M f i ω := by
  induction j with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero]; rfl
  | succ j ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih, skelCycle_eq,
      Finset.sum_range_add_sum_Ico _ (Nat.mul_le_mul_left m (Nat.succ_le_succ
        (renewalTime_lt_succ _ j ω).le))]

/-- `skelPreSum` is measurable. -/
theorem measurable_skelPreSum [NeZero m] (M : Minorization (P ^ m)) {f : X → ℝ}
    (hf : Measurable f) : Measurable (skelPreSum M f) := by
  have hF : Measurable fun p : (ℕ → (Fin m → X) × Bool) × ℕ =>
      ∑ t ∈ Finset.range (m * (p.2 + 1)), f (skelRecover p.1 t) :=
    measurable_from_prod_countable_left fun n => by
      dsimp only
      exact Finset.measurable_sum _ fun t _ =>
        hf.comp ((measurable_pi_apply t).comp measurable_skelRecover)
  exact hF.comp (measurable_id.prodMk (measurable_hitNat (measurableSet_skelAtom M)))

/-- The cycle sums are measurable. -/
theorem measurable_skelCycle [NeZero m] (M : Minorization (P ^ m)) {f : X → ℝ}
    (hf : Measurable f) (j : ℕ) : Measurable (skelCycle M f j) :=
  (measurable_skelPreSum M hf).comp ((measurable_restart (measurableSet_skelAtom M)).iterate _)


/-! ### Stopped σ-algebras and the strong Markov property after a visit -/

variable {Y : Type*} [MeasurableSpace Y] in
/-- A measurable functional that only depends on the path up to a stopping time `ζ` is
`𝓕_ζ`-measurable. -/
theorem measurable_stoppedField_of_congr {β : Type*} [MeasurableSpace β]
    {τ : (ℕ → Y) → WithTop ℕ} (hτ : IsStoppingTime (natFilt (X := Y)) τ)
    {Z : (ℕ → Y) → β} (hZ : Measurable Z)
    (h : ∀ (n : ℕ) ω, τ ω = n → Z ω = Z fun i => ω (min n i)) :
    Measurable[hτ.measurableSpace] Z := by
  intro S hS
  rw [measurableSet_stoppedField_iff]
  refine ⟨hZ hS, fun n => ?_⟩
  set stop : (ℕ → Y) → ℕ → Y := fun ω i => ω (min n i) with hstop
  have hstopm : Measurable[natFilt n] stop := by
    refine (@measurable_pi_iff (ℕ → Y) ℕ (fun _ => Y) (natFilt n) _ stop).2 fun i => ?_
    exact (measurable_coord_natFilt (min n i)).mono ((natFilt (X := Y)).mono (min_le_left n i))
      le_rfl
  have : Z ⁻¹' S ∩ {ω | τ ω = n} = (Z ∘ stop) ⁻¹' S ∩ {ω | τ ω = n} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, Function.comp_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [← h n ω h2], h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [h n ω h2], h2⟩
  rw [this]
  exact ((hZ.comp hstopm) hS).inter (hτ.measurableSet_eq_of_countable n)


variable {Y : Type*} [MeasurableSpace Y] in
/-- The time just after the first visit, `σ_α + 1`, is a stopping time. -/
theorem isStoppingTime_firstHit_add_one {α : Set Y} (hα : MeasurableSet α) :
    IsStoppingTime (natFilt (X := Y)) fun ω => firstHit α ω + 1 :=
  (isStoppingTime_firstHit hα).add_const' 1

variable {Y : Type*} [MeasurableSpace Y] in
/-- **The strong Markov property just after the first visit**: for `𝓕_{σ_α+1}`-measurable `F ≥ 0`
and measurable `G ≥ 0`, if `α` is reached `P_ρ`-a.s.,
`E_ρ[F · G(θ^{σ_α+1}Φ)] = E_ρ[F · E_{Φ_{σ_α+1}}[G]]`. -/
theorem lintegral_mul_restart_succ (Q : Kernel Y Y) [IsMarkovKernel Q] {α : Set Y}
    (hα : MeasurableSet α) (ρ : Measure Y) [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ ω ∂pathMeasure Q ρ, firstHit α ω ≠ ⊤) {F : (ℕ → Y) → ℝ≥0∞}
    (hF : Measurable[(isStoppingTime_firstHit_add_one hα).measurableSpace] F)
    {G : (ℕ → Y) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, F ω * G (restart α ω) ∂pathMeasure Q ρ =
      ∫⁻ ω, F ω * ∫⁻ w, G w ∂pathKernel Q (ω (hitNat α ω + 1)) ∂pathMeasure Q ρ := by
  have hτ := isStoppingTime_firstHit_add_one hα
  have hset : {ω : ℕ → Y | firstHit α ω + 1 ≠ ⊤} = {ω | firstHit α ω ≠ ⊤} := by
    ext ω
    simp only [mem_ofPred_eq, ne_eq, WithTop.add_eq_top, WithTop.one_ne_top, or_false]
  have hfull : (pathMeasure Q ρ).restrict {ω | firstHit α ω + 1 ≠ ⊤} = pathMeasure Q ρ := by
    rw [hset]; exact Measure.restrict_eq_self_of_ae_mem hρ
  have hsm := strong_markov_lintegral_mul Q ρ hτ hF hG
  rw [hfull] at hsm
  have hval : ∀ ω, firstHit α ω ≠ ⊤ → firstHit α ω + 1 = ((hitNat α ω + 1 : ℕ) : WithTop ℕ) :=
    fun ω h => by rw [firstHit_eq_hitNat h]; rfl
  have hm : MeasurableSet {ω : ℕ → Y | firstHit α ω ≠ ⊤} :=
    measurableSet_ne_top (isStoppingTime_firstHit hα)
  have hfull' : (pathMeasure Q ρ).restrict {ω | firstHit α ω ≠ ⊤} = pathMeasure Q ρ :=
    Measure.restrict_eq_self_of_ae_mem hρ
  calc ∫⁻ ω, F ω * G (restart α ω) ∂pathMeasure Q ρ
      = ∫⁻ ω, F ω * G (shiftAt (fun ω => firstHit α ω + 1) ω) ∂pathMeasure Q ρ := by
        rw [← hfull', setLIntegral_congr_fun hm fun ω hω => ?_]
        rw [shiftAt_of_eq (τ := fun ω => firstHit α ω + 1) (hval ω hω)]; rfl
    _ = ∫⁻ ω, F ω * ∫⁻ w, G w ∂pathKernel Q (stoppedState (fun ω => firstHit α ω + 1) ω)
          ∂pathMeasure Q ρ := hsm
    _ = _ := by
        rw [← hfull', setLIntegral_congr_fun hm fun ω hω => ?_, hfull']
        rw [stoppedState_of_eq (τ := fun ω => firstHit α ω + 1) (hval ω hω)]

/-! ### The fresh start -/

variable [MeasurableSpace.CountablyGenerated X]

/-- The law `P̌_{λ_ν}` of the chain on blocks started afresh from `ν*`: the law of the future
after the end of the block following a visit of the split skeleton to `α̌`. -/
noncomputable def skelFreshLaw [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    Measure (ℕ → (Fin m → X) × Bool) :=
  @pathMeasure _ _ (skelKernel M) (isMarkovKernel_skelKernel M) (skelInit M M.ν)

/-- `P̌_{λ_ν}` is a probability measure. -/
theorem isProbabilityMeasure_skelFreshLaw [IsMarkovKernel P] [NeZero m]
    (M : Minorization (P ^ m)) : IsProbabilityMeasure (skelFreshLaw M) := by
  have := isMarkovKernel_skelKernel M
  have := M.isProbabilityMeasure_ν
  have := isProbabilityMeasure_skelInit M M.ν
  exact isProbabilityMeasure_pathMeasure _ _

/-- The cylinder functions do not see the block part of the state at time `0`. -/
theorem cylFn_skelFresh [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) (n : ℕ)
    (A : ℕ → Set ((Fin m → X) × Bool)) (v : (Fin m → X) × Bool) :
    cylFn (skelKernel M) n (fun i => if i = 0 then (skelVirt ∘ skelState) ⁻¹' A 0 else A i) v =
      cylFn (skelKernel M) n A (skelVirt (skelState v)) := by
  cases n with
  | zero =>
    simp only [cylFn, ↓reduceIte]
    by_cases hv : skelVirt (skelState v) ∈ A 0
    · rw [indicator_of_mem (show v ∈ (skelVirt ∘ skelState) ⁻¹' A 0 from hv),
        indicator_of_mem hv]
      rfl
    · rw [indicator_of_notMem (show v ∉ (skelVirt ∘ skelState) ⁻¹' A 0 from hv),
        indicator_of_notMem hv]
  | succ n =>
    simp only [cylFn, ↓reduceIte, Nat.add_one_ne_zero]
    have hQ : skelKernel M (skelVirt (skelState v)) = skelKernel M v := by
      rw [skelKernel_apply, skelKernel_apply, skelState_skelVirt]
    by_cases hv : skelVirt (skelState v) ∈ A 0
    · rw [indicator_of_mem (show v ∈ (skelVirt ∘ skelState) ⁻¹' A 0 from hv),
        indicator_of_mem hv, hQ]
    · rw [indicator_of_notMem (show v ∉ (skelVirt ∘ skelState) ⁻¹' A 0 from hv),
        indicator_of_notMem hv]

/-- **The fresh start does not change the law of the future**: replacing the state at time `0`
by the virtual state with the same skeleton state, `P_ρ ∘ skelFresh⁻¹ = P_{ρ ∘ (virt ∘ state)⁻¹}`
(the transition from a state depends only on its skeleton state). -/
theorem pathMeasure_map_skelFresh [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ] :
    haveI := isMarkovKernel_skelKernel M
    (pathMeasure (skelKernel M) ρ).map skelFresh =
      pathMeasure (skelKernel M) (ρ.map (skelVirt ∘ skelState)) := by
  have := isMarkovKernel_skelKernel M
  have := isProbabilityMeasure_pathMeasure (skelKernel M) ρ
  have hg : Measurable (skelVirt (X := X) (m := m) ∘ skelState (X := X) (m := m)) :=
    measurable_skelVirt.comp measurable_skelState
  have : IsProbabilityMeasure (ρ.map (skelVirt ∘ skelState)) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure ((pathMeasure (skelKernel M) ρ).map skelFresh) :=
    (Measure.isProbabilityMeasure_map_iff measurable_skelFresh.aemeasurable).2 inferInstance
  refine theorem_3_4_1_unique _ _ _ fun n A hA => ?_
  set A' : ℕ → Set ((Fin m → X) × Bool) :=
    fun i => if i = 0 then (skelVirt ∘ skelState) ⁻¹' A 0 else A i with hA'def
  have hA' : ∀ i, MeasurableSet (A' i) := fun i => by
    by_cases hi : i = 0
    · simp only [hA'def, hi, ↓reduceIte]; exact hg (hA 0)
    · simp only [hA'def, hi, ↓reduceIte]; exact hA i
  have hpre : skelFresh ⁻¹' boxSet n A = boxSet n A' := by
    ext ω
    simp only [boxSet, mem_preimage, mem_ofPred_eq, hA'def]
    refine forall_congr' fun i => imp_congr_right fun _ => ?_
    by_cases hi : i = 0
    · subst hi; simp [skelFresh]
    · simp [skelFresh, hi]
  rw [Measure.map_apply measurable_skelFresh (measurableSet_boxSet n hA), hpre,
    pathMeasure_boxSet _ _ n hA', lintegral_map (measurable_cylFn _ n hA) hg]
  exact lintegral_congr fun v => cylFn_skelFresh M n A v

/-- **Regeneration at the atom** (MT p. 434): from a state `v` whose skeleton state is in `α̌`,
the future after the next block, made fresh, has law `P̌_{λ_ν}`. -/
theorem pathKernel_map_skelFresh_shift [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {v : (Fin m → X) × Bool} (hv : v ∈ skelAtom M) :
    haveI := isMarkovKernel_skelKernel M
    (pathKernel (skelKernel M) v).map (skelFresh ∘ shift 1) = skelFreshLaw M := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_skelJ M
  rw [← Measure.map_map measurable_skelFresh (measurable_shift 1), pathKernel_map_shift_one,
    pathMeasure_map_skelFresh, ← Measure.map_map measurable_skelVirt measurable_skelState,
    skelKernel_map_skelState]
  have h2 : skelState v = ((skelState v).1, true) := Prod.ext rfl hv.2
  rw [h2, M.splitKernel_apply_true]
  rfl


omit [MeasurableSpace.CountablyGenerated X] in
/-- The visits of the chain on blocks to `skelAtom` are the visits of the split skeleton to
`α̌`. -/
theorem firstHit_skelAtom [NeZero m] (M : Minorization (P ^ m))
    (ω : ℕ → (Fin m → X) × Bool) :
    firstHit (skelAtom M) ω = firstHit M.checkAlpha fun n => skelState (ω n) := rfl

/-- If the split skeleton reaches `α̌` almost surely from every state (the hypothesis of the
CLT moment condition (17.31)), the chain on blocks reaches `skelAtom` almost surely from every
state. -/
theorem ae_firstHit_skelAtom [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    (v : (Fin m → X) × Bool) :
    haveI := isMarkovKernel_skelKernel M
    ∀ᵐ ω ∂pathKernel (skelKernel M) v, firstHit (skelAtom M) ω ≠ ⊤ := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have hπ : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (n : ℕ) => skelState (ω n) :=
    measurable_pi_iff.2 fun n => measurable_skelState.comp (measurable_pi_apply n)
  have h1 := ae_firstHit_ne_top_of_hitProb_eq_one M.splitKernel M.measurableSet_checkAlpha
    (hL (skelState v))
  rw [← pathKernel_map_lump _ _ measurable_skelState (skelKernel_map_skelState M) v] at h1
  have hE : MeasurableSet {ω : ℕ → X × Bool | firstHit M.checkAlpha ω ≠ ⊤} :=
    measurableSet_ne_top (isStoppingTime_firstHit M.measurableSet_checkAlpha)
  exact (ae_map_iff hπ.aemeasurable hE).1 h1

/-- The same from every initial law. -/
theorem ae_firstHit_skelAtom_measure [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    (ρ : Measure ((Fin m → X) × Bool)) :
    haveI := isMarkovKernel_skelKernel M
    ∀ᵐ ω ∂pathMeasure (skelKernel M) ρ, firstHit (skelAtom M) ω ≠ ⊤ := by
  have := isMarkovKernel_skelKernel M
  exact ae_pathMeasure_of_forall _ ρ (measurableSet_ne_top
    (isStoppingTime_firstHit (measurableSet_skelAtom M))) fun v => ae_firstHit_skelAtom M hL v

/-- **Regeneration at the first visit**: for `𝓕_{σ_α̌}`-measurable `F ≥ 0` and measurable
`H ≥ 0` that does not see the block part of the state at time `0`,
`E_ρ[F · H(θ^{σ+1}V)] = E_ρ[F] · Ě_{λ_ν}[H]`. -/
theorem lintegral_mul_skelRestart [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ]
    (hρ : haveI := isMarkovKernel_skelKernel M
      ∀ᵐ ω ∂pathMeasure (skelKernel M) ρ, firstHit (skelAtom M) ω ≠ ⊤)
    {F : (ℕ → (Fin m → X) × Bool) → ℝ≥0∞}
    (hF : Measurable[(isStoppingTime_firstHit (measurableSet_skelAtom M)).measurableSpace] F)
    {H : (ℕ → (Fin m → X) × Bool) → ℝ≥0∞} (hH : Measurable H)
    (hHf : ∀ ω, H (skelFresh ω) = H ω) :
    haveI := isMarkovKernel_skelKernel M
    ∫⁻ ω, F ω * H (restart (skelAtom M) ω) ∂pathMeasure (skelKernel M) ρ =
      (∫⁻ ω, F ω ∂pathMeasure (skelKernel M) ρ) * ∫⁻ ω, H ω ∂skelFreshLaw M := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pathKernel (skelKernel M)
  have hτ := isStoppingTime_firstHit (measurableSet_skelAtom M)
  have hfull : (pathMeasure (skelKernel M) ρ).restrict {ω | firstHit (skelAtom M) ω ≠ ⊤} =
      pathMeasure (skelKernel M) ρ := Measure.restrict_eq_self_of_ae_mem hρ
  have hKs : Measurable fun ω => H (shift 1 ω) := hH.comp (measurable_shift 1)
  have hsm := strong_markov_lintegral_mul (skelKernel M) ρ hτ hF hKs
  simp only [← restart_eq] at hsm
  rw [← hfull, hsm]
  have hconst : ∀ ω ∈ {ω | firstHit (skelAtom M) ω ≠ ⊤},
      F ω * ∫⁻ ω', H (shift 1 ω') ∂pathKernel (skelKernel M)
        (stoppedState (firstHit (skelAtom M)) ω) = F ω * ∫⁻ ω, H ω ∂skelFreshLaw M := by
    intro ω hω
    have hmem : stoppedState (firstHit (skelAtom M)) ω ∈ skelAtom M :=
      hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → (Fin m → X) × Bool) => ω n)
        (s := skelAtom M) (n := 0) hω
    have h1 : ∫⁻ ω', H (shift 1 ω') ∂pathKernel (skelKernel M)
        (stoppedState (firstHit (skelAtom M)) ω) = ∫⁻ ω', H (skelFresh (shift 1 ω'))
          ∂pathKernel (skelKernel M) (stoppedState (firstHit (skelAtom M)) ω) := by
      simp_rw [hHf]
    rw [h1, ← pathKernel_map_skelFresh_shift M hmem,
      lintegral_map hH (measurable_skelFresh.comp (measurable_shift 1))]
    rfl
  rw [setLIntegral_congr_fun (measurableSet_ne_top hτ) hconst, lintegral_mul_const _
    (hF.mono hτ.measurableSpace_le le_rfl)]


omit [MeasurableSpace.CountablyGenerated X] in
/-- `s₋₁(f)` only depends on the path up to the block after the first visit: it is
`𝓕_{σ_α̌+1}`-measurable. -/
theorem measurable_stoppedField_skelPreSum [NeZero m] (M : Minorization (P ^ m)) {f : X → ℝ}
    (hf : Measurable f) :
    Measurable[(isStoppingTime_firstHit_add_one (measurableSet_skelAtom M)).measurableSpace]
      (skelPreSum M f) := by
  refine measurable_stoppedField_of_congr _ (measurable_skelPreSum M hf) fun n ω h => ?_
  have hne : firstHit (skelAtom M) ω ≠ ⊤ := by
    intro htop; rw [htop] at h; simp at h
  have hk : hitNat (skelAtom M) ω + 1 = n := by
    have h' : ((hitNat (skelAtom M) ω + 1 : ℕ) : WithTop ℕ) = n := by
      rw [← h, firstHit_eq_hitNat hne]; rfl
    exact_mod_cast h' 
  have hagree : ∀ i ≤ n, (fun i => ω (min n i)) i = ω i := fun i hi => by
    simp only [min_eq_right hi]
  have hhit : hitNat (skelAtom M) (fun i => ω (min n i)) = hitNat (skelAtom M) ω := by
    have h1 := (firstHit_eq_coe_iff _ ω (hitNat (skelAtom M) ω)).1 (firstHit_eq_hitNat hne)
    have h2 : firstHit (skelAtom M) (fun i => ω (min n i)) = hitNat (skelAtom M) ω := by
      refine (firstHit_eq_coe_iff _ _ _).2 ⟨?_, fun j hj => ?_⟩
      · rw [min_eq_right (by omega)]; exact h1.1
      · rw [min_eq_right (by omega)]; exact h1.2 j hj
    rw [hitNat, h2]; rfl
  rw [skelPreSum, skelPreSum, hhit]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [skelRecover_congr (n := n) (fun i hi => (hagree i hi).symm)]
  have := Finset.mem_range.1 ht
  rw [← hk]; exact this.le

/-- The sequence `(s₋₁(f), s₀(f), s₁(f), …)`: `skelSeq M f ω 0 = s₋₁(f)` is the initial segment
sum and `skelSeq M f ω (j + 1) = sⱼ(f)`. -/
noncomputable def skelSeq [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ)
    (ω : ℕ → (Fin m → X) × Bool) (j : ℕ) : ℝ :=
  skelPreSum M f ((restart (skelAtom M))^[j] ω)

omit [MeasurableSpace.CountablyGenerated X] in
/-- `skelSeq (j + 1) = sⱼ`. -/
theorem skelSeq_succ [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ)
    (ω : ℕ → (Fin m → X) × Bool) (j : ℕ) : skelSeq M f ω (j + 1) = skelCycle M f j ω := rfl

omit [MeasurableSpace.CountablyGenerated X] in
/-- `skelSeq (j + 1) ω = skelSeq j (restart ω)`. -/
theorem skelSeq_succ_restart [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ)
    (ω : ℕ → (Fin m → X) × Bool) (j : ℕ) :
    skelSeq M f ω (j + 1) = skelSeq M f (restart (skelAtom M) ω) j := by
  rw [skelSeq, skelSeq, Function.iterate_succ_apply]

omit [MeasurableSpace.CountablyGenerated X] in
/-- `skelSeq` is measurable. -/
theorem measurable_skelSeq [NeZero m] (M : Minorization (P ^ m)) {f : X → ℝ}
    (hf : Measurable f) (j : ℕ) : Measurable fun ω => skelSeq M f ω j :=
  (measurable_skelPreSum M hf).comp ((measurable_restart (measurableSet_skelAtom M)).iterate _)

omit [MeasurableSpace.CountablyGenerated X] in
/-- `skelSeq` does not see the block part of the state at time `0`. -/
theorem skelSeq_skelFresh [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ)
    (ω : ℕ → (Fin m → X) × Bool) (j : ℕ) : skelSeq M f (skelFresh ω) j = skelSeq M f ω j := by
  cases j with
  | zero => exact skelPreSum_skelFresh M f ω
  | succ j => rw [skelSeq, skelSeq, restart_iterate_skelFresh]

variable {Y : Type*} [MeasurableSpace Y] in
/-- `ω ↦ Φ_{σ_α+1}` is measurable. -/
theorem measurable_coord_hitNat_succ {α : Set Y} (hα : MeasurableSet α) :
    Measurable fun ω : ℕ → Y => ω (hitNat α ω + 1) := by
  have hF : Measurable fun p : (ℕ → Y) × ℕ => p.1 (p.2 + 1) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply (n + 1)
  exact hF.comp (measurable_id.prodMk (measurable_hitNat hα))

omit [MeasurableSpace.CountablyGenerated X] in
/-- The product of indicators `∏_{j<k} 1_{Aⱼ}(skelSeq j)` is measurable. -/
theorem measurable_prod_indicator_skelSeq [NeZero m] (M : Minorization (P ^ m)) {f : X → ℝ}
    (hf : Measurable f) (k : ℕ) {A : ℕ → Set ℝ} (hA : ∀ j, MeasurableSet (A j)) :
    Measurable fun ω => ∏ j ∈ Finset.range k, (A j).indicator (1 : ℝ → ℝ≥0∞) (skelSeq M f ω j) :=
  Finset.measurable_prod _ fun j _ =>
    (measurable_one.indicator (hA j)).comp (measurable_skelSeq M hf j)

/-- **The regeneration theorem for the cycle sums** (MT p. 434–435): if the split skeleton
reaches `α̌` almost surely from every state, then from every state `v`, for measurable
`A₀, …, A_{k−1}` and measurable `H ≥ 0` that does not see the block part at time `0`,
`E_v[1{s₋₁ ∈ A₀, …, s_{k−2} ∈ A_{k−1}} · H(θ^{σ_α̌(k)+1}V)] =
  P_v(s₋₁ ∈ A₀, …, s_{k−2} ∈ A_{k−1}) · Ě_{λ_ν}[H]`: the first `k` terms of `(s₋₁, s₀, …)` are
independent of the future after the end of the block following the `(k + 1)`-th visit, whose law
is the fresh law `P̌_{λ_ν}`. -/
theorem skel_regeneration [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {f : X → ℝ} (hf : Measurable f) {H : (ℕ → (Fin m → X) × Bool) → ℝ≥0∞} (hH : Measurable H)
    (hHf : ∀ ω, H (skelFresh ω) = H ω) (k : ℕ) :
    haveI := isMarkovKernel_skelKernel M
    ∀ (v : (Fin m → X) × Bool) (A : ℕ → Set ℝ), (∀ j, MeasurableSet (A j)) →
    ∫⁻ ω, (∏ j ∈ Finset.range k, (A j).indicator 1 (skelSeq M f ω j)) *
        H ((restart (skelAtom M))^[k + 1] ω) ∂pathKernel (skelKernel M) v =
      (∫⁻ ω, ∏ j ∈ Finset.range k, (A j).indicator 1 (skelSeq M f ω j)
        ∂pathKernel (skelKernel M) v) * ∫⁻ ω, H ω ∂skelFreshLaw M := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pathKernel (skelKernel M)
  have hα := measurableSet_skelAtom M
  induction k with
  | zero =>
    intro v A _
    simp only [Finset.range_zero, Finset.prod_empty, one_mul, zero_add, Function.iterate_one,
      lintegral_one, measure_univ]
    have h := lintegral_mul_skelRestart M (Measure.dirac v)
      (by rw [pathMeasure_dirac]; exact ae_firstHit_skelAtom M hL v) (F := fun _ => 1)
      measurable_const hH hHf
    simp only [one_mul, lintegral_one, measure_univ, pathMeasure_dirac] at h
    exact h
  | succ k ih =>
    intro v A hA
    have hA' : ∀ j, MeasurableSet (A (j + 1)) := fun j => hA (j + 1)
    have hG'm := measurable_prod_indicator_skelSeq M hf k hA'
    have hGm : Measurable fun w => (∏ j ∈ Finset.range k,
        (A (j + 1)).indicator (1 : ℝ → ℝ≥0∞) (skelSeq M f w j)) *
          H ((restart (skelAtom M))^[k + 1] w) :=
      hG'm.mul (hH.comp ((measurable_restart hα).iterate _))
    have h0 := measurable_stoppedField_skelPreSum M hf
    have h1 : Measurable ((A 0).indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator (hA 0)
    have hFm : Measurable[(isStoppingTime_firstHit_add_one hα).measurableSpace]
        (fun ω => (A 0).indicator (1 : ℝ → ℝ≥0∞) (skelPreSum M f ω)) := by
      exact h1.comp h0
    have hρ : ∀ᵐ ω ∂pathMeasure (skelKernel M) (Measure.dirac v),
        firstHit (skelAtom M) ω ≠ ⊤ := by
      rw [pathMeasure_dirac]; exact ae_firstHit_skelAtom M hL v
    have e1 : ∀ ω, (∏ j ∈ Finset.range (k + 1), (A j).indicator 1 (skelSeq M f ω j)) =
        (A 0).indicator (1 : ℝ → ℝ≥0∞) (skelPreSum M f ω) * ∏ j ∈ Finset.range k,
          (A (j + 1)).indicator 1 (skelSeq M f (restart (skelAtom M) ω) j) := fun ω => by
      rw [Finset.prod_range_succ', mul_comm]
      simp only [skelSeq_succ_restart]
      rfl
    have e2 : ∀ ω, (∏ j ∈ Finset.range (k + 1), (A j).indicator 1 (skelSeq M f ω j)) *
        H ((restart (skelAtom M))^[k + 1 + 1] ω) =
        (A 0).indicator (1 : ℝ → ℝ≥0∞) (skelPreSum M f ω) *
          ((∏ j ∈ Finset.range k, (A (j + 1)).indicator 1
            (skelSeq M f (restart (skelAtom M) ω) j)) *
            H ((restart (skelAtom M))^[k + 1] (restart (skelAtom M) ω))) :=
      fun ω => by
        rw [e1, Function.iterate_succ_apply, mul_assoc]
    simp_rw [e2, e1]
    have hev := measurable_coord_hitNat_succ hα
    rw [← pathMeasure_dirac, lintegral_mul_restart_succ _ hα _ hρ hFm hGm,
      lintegral_mul_restart_succ _ hα _ hρ hFm hG'm]
    simp_rw [ih _ (fun j => A (j + 1)) hA', ← mul_assoc]
    exact lintegral_mul_const _ ((hFm.mono (isStoppingTime_firstHit_add_one hα).measurableSpace_le
      le_rfl).mul (hG'm.lintegral_kernel.comp hev))


/-- The regeneration theorem from every initial law `ρ`. -/
theorem skel_regeneration_measure [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {f : X → ℝ} (hf : Measurable f) {H : (ℕ → (Fin m → X) × Bool) → ℝ≥0∞} (hH : Measurable H)
    (hHf : ∀ ω, H (skelFresh ω) = H ω) (k : ℕ) (ρ : Measure ((Fin m → X) × Bool))
    (A : ℕ → Set ℝ) (hA : ∀ j, MeasurableSet (A j)) :
    haveI := isMarkovKernel_skelKernel M
    ∫⁻ ω, (∏ j ∈ Finset.range k, (A j).indicator 1 (skelSeq M f ω j)) *
        H ((restart (skelAtom M))^[k + 1] ω) ∂pathMeasure (skelKernel M) ρ =
      (∫⁻ ω, ∏ j ∈ Finset.range k, (A j).indicator 1 (skelSeq M f ω j)
        ∂pathMeasure (skelKernel M) ρ) * ∫⁻ ω, H ω ∂skelFreshLaw M := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pathKernel (skelKernel M)
  have hprod := measurable_prod_indicator_skelSeq M hf k hA
  have hfull : Measurable fun ω => (∏ j ∈ Finset.range k, (A j).indicator (1 : ℝ → ℝ≥0∞)
      (skelSeq M f ω j)) * H ((restart (skelAtom M))^[k + 1] ω) :=
    hprod.mul (hH.comp ((measurable_restart (measurableSet_skelAtom M)).iterate _))
  rw [pathMeasure_eq_comp, Measure.lintegral_bind (Kernel.aemeasurable _) hfull.aemeasurable,
    Measure.lintegral_bind (Kernel.aemeasurable _) hprod.aemeasurable]
  simp_rw [skel_regeneration M hL hf hH hHf k _ A hA]
  exact lintegral_mul_const _ hprod.lintegral_kernel

omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- A product of indicators is the indicator of the intersection. -/
theorem prod_indicator_eq (k : ℕ) (A : ℕ → Set ℝ) (x : ℕ → ℝ) :
    ∏ j ∈ Finset.range k, (A j).indicator (1 : ℝ → ℝ≥0∞) (x j) =
      {y : ℕ → ℝ | ∀ j < k, y j ∈ A j}.indicator 1 x := by
  classical
  by_cases h : ∀ j < k, x j ∈ A j
  · rw [indicator_of_mem (show x ∈ {y : ℕ → ℝ | ∀ j < k, y j ∈ A j} from h)]
    exact Finset.prod_eq_one fun j hj => by
      rw [indicator_of_mem (h j (Finset.mem_range.1 hj))]; rfl
  · rw [indicator_of_notMem (show x ∉ {y : ℕ → ℝ | ∀ j < k, y j ∈ A j} from h)]
    push Not at h
    obtain ⟨j, hj, hjA⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_range.2 hj) (indicator_of_notMem hjA _)

/-- The box form of the regeneration theorem: for measurable `A`, `B`,
`P_ρ(s₋₁ ∈ A₀, …, s_{k−2} ∈ A_{k−1}; s_k ∈ B₀, …, s_{k+n} ∈ Bₙ) =
  P_ρ(s₋₁ ∈ A₀, …, s_{k−2} ∈ A_{k−1}) · P̌_{λ_ν}(s₋₁ ∈ B₀, …, s_{n−1} ∈ Bₙ)`. -/
theorem skel_box [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {f : X → ℝ} (hf : Measurable f) (ρ : Measure ((Fin m → X) × Bool)) (k n : ℕ)
    {A B : ℕ → Set ℝ} (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j)) :
    haveI := isMarkovKernel_skelKernel M
    pathMeasure (skelKernel M) ρ ({ω | ∀ j < k, skelSeq M f ω j ∈ A j} ∩
        {ω | ∀ i ≤ n, skelSeq M f ω (k + 1 + i) ∈ B i}) =
      pathMeasure (skelKernel M) ρ {ω | ∀ j < k, skelSeq M f ω j ∈ A j} *
        skelFreshLaw M {w | ∀ i ≤ n, skelSeq M f w i ∈ B i} := by
  have := isMarkovKernel_skelKernel M
  have hseq : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (j : ℕ) => skelSeq M f ω j :=
    measurable_pi_iff.2 fun j => measurable_skelSeq M hf j
  have hEA : MeasurableSet {y : ℕ → ℝ | ∀ j < k, y j ∈ A j} := by
    have : {y : ℕ → ℝ | ∀ j < k, y j ∈ A j} = ⋂ j ∈ Finset.range k, {y | y j ∈ A j} := by
      ext y; simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun j _ => measurable_pi_apply j (hA j)
  have hEB : MeasurableSet {w : ℕ → (Fin m → X) × Bool | ∀ i ≤ n, skelSeq M f w i ∈ B i} := by
    have : {w : ℕ → (Fin m → X) × Bool | ∀ i ≤ n, skelSeq M f w i ∈ B i} =
        ⋂ i ∈ Finset.range (n + 1), {w | skelSeq M f w i ∈ B i} := by
      ext w; simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun i _ => measurable_skelSeq M hf i (hB i)
  set H := {w : ℕ → (Fin m → X) × Bool | ∀ i ≤ n, skelSeq M f w i ∈ B i}.indicator
    (1 : (ℕ → (Fin m → X) × Bool) → ℝ≥0∞) with hHdef
  have hH : Measurable H := measurable_one.indicator hEB
  have hmem : ∀ ω, skelFresh ω ∈ {w : ℕ → (Fin m → X) × Bool | ∀ i ≤ n, skelSeq M f w i ∈ B i}
      ↔ ω ∈ {w : ℕ → (Fin m → X) × Bool | ∀ i ≤ n, skelSeq M f w i ∈ B i} := fun ω => by
    simp only [mem_ofPred_eq, skelSeq_skelFresh]
  have hHf : ∀ ω, H (skelFresh ω) = H ω := fun ω => by
    by_cases h : ω ∈ {w : ℕ → (Fin m → X) × Bool | ∀ i ≤ n, skelSeq M f w i ∈ B i}
    · rw [hHdef, indicator_of_mem ((hmem ω).2 h), indicator_of_mem h]; rfl
    · rw [hHdef, indicator_of_notMem (fun h' => h ((hmem ω).1 h')), indicator_of_notMem h]
  have h := skel_regeneration_measure M hL hf hH hHf k ρ A hA
  simp_rw [prod_indicator_eq k A] at h
  have hpre1 : ∀ ω, {y : ℕ → ℝ | ∀ j < k, y j ∈ A j}.indicator (1 : (ℕ → ℝ) → ℝ≥0∞)
      (fun j => skelSeq M f ω j) =
      {ω | ∀ j < k, skelSeq M f ω j ∈ A j}.indicator 1 ω := fun ω => rfl
  have hpre2 : ∀ ω, H ((restart (skelAtom M))^[k + 1] ω) =
      {ω | ∀ i ≤ n, skelSeq M f ω (k + 1 + i) ∈ B i}.indicator 1 ω := fun ω => by
    simp only [hHdef, indicator, mem_ofPred_eq]
    congr 1
    apply propext
    refine forall_congr' fun i => imp_congr_right fun _ => ?_
    rw [skelSeq, skelSeq, ← Function.iterate_add_apply, add_comm i (k + 1)]
  simp_rw [hpre1, hpre2] at h
  have hmA : MeasurableSet {ω : ℕ → (Fin m → X) × Bool | ∀ j < k, skelSeq M f ω j ∈ A j} :=
    hseq hEA
  have hmB : MeasurableSet {ω : ℕ → (Fin m → X) × Bool |
      ∀ i ≤ n, skelSeq M f ω (k + 1 + i) ∈ B i} := by
    have : {ω : ℕ → (Fin m → X) × Bool | ∀ i ≤ n, skelSeq M f ω (k + 1 + i) ∈ B i} =
        ⋂ i ∈ Finset.range (n + 1), {ω | skelSeq M f ω (k + 1 + i) ∈ B i} := by
      ext w; simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun i _ => measurable_skelSeq M hf _ (hB i)
  have e1 : ∀ ω, {ω : ℕ → (Fin m → X) × Bool | ∀ j < k, skelSeq M f ω j ∈ A j}.indicator
      (1 : (ℕ → (Fin m → X) × Bool) → ℝ≥0∞) ω * {ω | ∀ i ≤ n, skelSeq M f ω (k + 1 + i) ∈
        B i}.indicator 1 ω = ({ω | ∀ j < k, skelSeq M f ω j ∈ A j} ∩
          {ω | ∀ i ≤ n, skelSeq M f ω (k + 1 + i) ∈ B i}).indicator 1 ω := fun ω => by
    rw [inter_indicator_one]; rfl
  simp_rw [e1] at h
  rw [lintegral_indicator_one (hmA.inter hmB), lintegral_indicator_one hmA, hHdef,
    lintegral_indicator_one hEB] at h
  exact h


/-- **The law of the cycle sums after the `c`-th one** (MT p. 435): under `P_ρ`, the sequence
`(s_c(f), s_{c+1}(f), …)` has the law of `(s₋₁(f), s₀(f), …)` under the fresh law `P̌_{λ_ν}`, for
every `c`. -/
theorem skel_map_cycles [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {f : X → ℝ} (hf : Measurable f) (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ]
    (c : ℕ) :
    haveI := isMarkovKernel_skelKernel M
    (pathMeasure (skelKernel M) ρ).map (fun ω j => skelCycle M f (c + j) ω) =
      (skelFreshLaw M).map fun w j => skelSeq M f w j := by
  have := isMarkovKernel_skelKernel M
  have := isProbabilityMeasure_pathMeasure (skelKernel M) ρ
  have hv1 : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (j : ℕ) => skelCycle M f (c + j) ω :=
    measurable_pi_iff.2 fun j => measurable_skelCycle M hf _
  have hv2 : Measurable fun (w : ℕ → (Fin m → X) × Bool) (j : ℕ) => skelSeq M f w j :=
    measurable_pi_iff.2 fun j => measurable_skelSeq M hf j
  have : IsFiniteMeasure ((pathMeasure (skelKernel M) ρ).map
      fun ω j => skelCycle M f (c + j) ω) := inferInstance
  refine measure_eq_of_boxSets fun n B hB => ?_
  rw [Measure.map_apply hv1 (measurableSet_boxSet n hB),
    Measure.map_apply hv2 (measurableSet_boxSet n hB)]
  have h := skel_box M hL hf ρ c n (A := fun _ => univ) (fun _ => MeasurableSet.univ) hB
  have e1 : {ω : ℕ → (Fin m → X) × Bool | ∀ j < c, skelSeq M f ω j ∈ (fun _ => univ) j} =
      univ := by ext; simp
  rw [e1, univ_inter, measure_univ, one_mul] at h
  have e2 : (fun (ω : ℕ → (Fin m → X) × Bool) (j : ℕ) => skelCycle M f (c + j) ω) ⁻¹'
      boxSet n B = {ω | ∀ i ≤ n, skelSeq M f ω (c + 1 + i) ∈ B i} := by
    ext ω
    simp only [boxSet, mem_preimage, mem_ofPred_eq]
    refine forall_congr' fun i => imp_congr_right fun _ => ?_
    rw [← skelSeq_succ, show c + i + 1 = c + 1 + i by ring]
  rw [e2, h]
  rfl

/-- **The one-dependence of the cycle sums** (MT p. 435): `(s₀(f), …, sₙ(f))` is independent of
`(s_{n+2}(f), s_{n+3}(f), …)` under every initial law. -/
theorem skel_isOneDependent [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {f : X → ℝ} (hf : Measurable f) (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ] :
    haveI := isMarkovKernel_skelKernel M
    IsOneDependent (fun j => skelCycle M f j) (pathMeasure (skelKernel M) ρ) := by
  have := isMarkovKernel_skelKernel M
  have := isProbabilityMeasure_pathMeasure (skelKernel M) ρ
  intro n
  have hU : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (i : Fin (n + 1)) =>
      skelCycle M f i ω := measurable_pi_iff.2 fun i => measurable_skelCycle M hf _
  have hW : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (i : ℕ) =>
      skelCycle M f (n + 2 + i) ω := measurable_pi_iff.2 fun i => measurable_skelCycle M hf _
  refine indepFun_of_boxes_nat hU hW fun A k B hA hB => ?_
  set A' : ℕ → Set ℝ := fun j => if h : 1 ≤ j ∧ j ≤ n + 1 then A ⟨j - 1, by omega⟩ else univ
    with hA'def
  have hA' : ∀ j, MeasurableSet (A' j) := fun j => by
    simp only [hA'def]; split_ifs
    · exact hA _
    · exact MeasurableSet.univ
  have eU : (fun (ω : ℕ → (Fin m → X) × Bool) (i : Fin (n + 1)) => skelCycle M f i ω) ⁻¹'
      univ.pi A = {ω | ∀ j < n + 2, skelSeq M f ω j ∈ A' j} := by
    ext ω
    simp only [mem_preimage, Set.mem_pi, mem_univ, true_imp_iff, mem_ofPred_eq, hA'def]
    constructor
    · intro h j hj
      split_ifs with hj'
      · have := h ⟨j - 1, by omega⟩
        rwa [← skelSeq_succ, show j - 1 + 1 = j by omega] at this
      · trivial
    · intro h i
      have := h (i + 1) (by omega)
      have hc : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ n + 1 := by omega
      simp only [hc, and_self, ↓reduceDIte, Nat.add_sub_cancel] at this
      simpa [skelSeq_succ] using this
  have eW : (fun (ω : ℕ → (Fin m → X) × Bool) (i : ℕ) => skelCycle M f (n + 2 + i) ω) ⁻¹'
      boxSet k B = {ω | ∀ i ≤ k, skelSeq M f ω (n + 2 + 1 + i) ∈ B i} := by
    ext ω
    simp only [boxSet, mem_preimage, mem_ofPred_eq]
    refine forall_congr' fun i => imp_congr_right fun _ => ?_
    rw [← skelSeq_succ, show n + 2 + i + 1 = n + 2 + 1 + i by ring]
  have h1 := skel_box M hL hf ρ (n + 2) k hA' hB
  have h2 := skel_box M hL hf ρ (n + 2) k (A := fun _ => univ) (fun _ => MeasurableSet.univ) hB
  have e1 : {ω : ℕ → (Fin m → X) × Bool | ∀ j < n + 2, skelSeq M f ω j ∈ (fun _ => univ) j} =
      univ := by ext; simp
  rw [e1, univ_inter, measure_univ, one_mul] at h2
  rw [eU, eW, h1, h2]

/-- **Stationarity of the cycle sums** (MT p. 435). -/
theorem skel_isStationarySeq [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {f : X → ℝ} (hf : Measurable f) (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ] :
    haveI := isMarkovKernel_skelKernel M
    IsStationarySeq (fun j => skelCycle M f j) (pathMeasure (skelKernel M) ρ) := by
  have := isMarkovKernel_skelKernel M
  intro c
  have h1 := skel_map_cycles M hL hf ρ c
  have h2 := skel_map_cycles M hL hf ρ 0
  simp only [zero_add] at h2
  exact ⟨(measurable_pi_iff.2 fun j => measurable_skelCycle M hf _).aemeasurable,
    (measurable_pi_iff.2 fun j => measurable_skelCycle M hf _).aemeasurable, h1.trans h2.symm⟩

/-- **(17.22)**: every cycle sum `sⱼ(f)` has the law of `s₋₁(f) = Σ_{t < m(σ_α̌+1)} f(Φₜ)` under the
fresh law `P̌_{λ_ν}` (the book's `P̌_{ν*}`). -/
theorem skel_map_cycle [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {f : X → ℝ} (hf : Measurable f) (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ]
    (j : ℕ) :
    haveI := isMarkovKernel_skelKernel M
    (pathMeasure (skelKernel M) ρ).map (skelCycle M f j) =
      (skelFreshLaw M).map (skelPreSum M f) := by
  have := isMarkovKernel_skelKernel M
  have h := congrArg (fun μ : Measure (ℕ → ℝ) => μ.map fun v => v 0) (skel_map_cycles M hL hf ρ j)
  have hv1 : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (i : ℕ) => skelCycle M f (j + i) ω :=
    measurable_pi_iff.2 fun i => measurable_skelCycle M hf _
  have hv2 : Measurable fun (w : ℕ → (Fin m → X) × Bool) (i : ℕ) => skelSeq M f w i :=
    measurable_pi_iff.2 fun i => measurable_skelSeq M hf i
  rw [Measure.map_map (measurable_pi_apply 0) hv1, Measure.map_map (measurable_pi_apply 0) hv2]
    at h
  exact h


/-- **Theorem 17.3.1** (MT p. 435), for a general `m`: if the split `m`-skeleton reaches `α̌`
almost surely from every state, then under every initial law of the chain on blocks the cycle
sums `sⱼ(f)` (`skelCycle`, the sums of `f(Φₜ)` over `m(σ_α̌(j)+1) ≤ t < m(σ_α̌(j+1)+1)`) form a
stationary one-dependent sequence; each has the law of `Σ_{t < m(σ_α̌+1)} f(Φₜ)` under
`P̌_{ν*}` (17.22); and the even terms `s₀, s₂, …` and the odd terms `s₁, s₃, …` are each
independent and identically distributed. The mean (17.23) is `theorem_17_3_1_general_mean`. -/
theorem theorem_17_3_1_general [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (hL : haveI := isMarkovKernel_pow P m; haveI := M.isMarkovKernel_splitKernel
      ∀ z, hitProb M.splitKernel M.checkAlpha z = 1)
    {f : X → ℝ} (hf : Measurable f) (ρ : Measure ((Fin m → X) × Bool)) [IsProbabilityMeasure ρ] :
    haveI := isMarkovKernel_skelKernel M
    IsStationarySeq (fun j => skelCycle M f j) (pathMeasure (skelKernel M) ρ) ∧
      IsOneDependent (fun j => skelCycle M f j) (pathMeasure (skelKernel M) ρ) ∧
      (∀ j, (pathMeasure (skelKernel M) ρ).map (skelCycle M f j) =
        (skelFreshLaw M).map (skelPreSum M f)) ∧
      iIndepFun (fun i => skelCycle M f (2 * i)) (pathMeasure (skelKernel M) ρ) ∧
      iIndepFun (fun i => skelCycle M f (2 * i + 1)) (pathMeasure (skelKernel M) ρ) := by
  have := isMarkovKernel_skelKernel M
  have := isProbabilityMeasure_pathMeasure (skelKernel M) ρ
  have hOD := skel_isOneDependent M hL hf ρ
  exact ⟨skel_isStationarySeq M hL hf ρ, hOD, skel_map_cycle M hL hf ρ, hOD.iIndepFun_even,
    hOD.iIndepFun_odd⟩


/-! ### The mean of the cycle sums (17.23) -/

/-- The sum of `f ≥ 0` over the first block of original times, `Σ_{k<m} f(Φₖ)`. -/
noncomputable def blockSumE [NeZero m] (f : X → ℝ≥0∞) (ω : ℕ → (Fin m → X) × Bool) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range m, f (skelRecover ω k)

omit [MeasurableSpace.CountablyGenerated X] in
/-- `blockSumE` is measurable. -/
theorem measurable_blockSumE [NeZero m] {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (blockSumE (m := m) f) :=
  Finset.measurable_sum _ fun k _ => hf.comp ((measurable_pi_apply k).comp measurable_skelRecover)

omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- `Σ_{t < mN} gₜ = Σ_{n<N} Σ_{k<m} g_{mn+k}`. -/
theorem skel_sum_range_mul {M' : Type*} [AddCommMonoid M'] (g : ℕ → M') (m N : ℕ) :
    ∑ t ∈ Finset.range (m * N), g t =
      ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range m, g (m * n + k) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ← ih, Nat.mul_succ, Finset.sum_range_add]

/-- The expected block sum from a state only depends on its skeleton state. -/
noncomputable def blockMeanE [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (f : X → ℝ≥0∞) (z : X × Bool) : ℝ≥0∞ :=
  ∫⁻ ω, blockSumE (m := m) f ω ∂@pathKernel _ _ (skelKernel M) (isMarkovKernel_skelKernel M)
    (skelVirt z)

/-- `blockMeanE` is measurable. -/
theorem measurable_blockMeanE [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {f : X → ℝ≥0∞} (hf : Measurable f) : Measurable (blockMeanE M f) := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pathKernel (skelKernel M)
  exact (measurable_blockSumE (m := m) hf).lintegral_kernel.comp measurable_skelVirt

/-- `E_v[Σ_{k<m} f(Φₖ)] = blockMeanE (skelState v)`. -/
theorem lintegral_blockSumE [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {f : X → ℝ≥0∞} (hf : Measurable f) (v : (Fin m → X) × Bool) :
    haveI := isMarkovKernel_skelKernel M
    ∫⁻ ω, blockSumE f ω ∂pathKernel (skelKernel M) v = blockMeanE M f (skelState v) := by
  have := isMarkovKernel_skelKernel M
  have h := pathMeasure_map_skelFresh M (Measure.dirac v)
  rw [pathMeasure_dirac, Measure.map_dirac' (measurable_skelVirt.comp measurable_skelState),
    pathMeasure_dirac] at h
  simp only [Function.comp_apply] at h
  have e : ∀ ω : ℕ → (Fin m → X) × Bool, blockSumE f (skelFresh ω) = blockSumE f ω :=
    fun ω => by simp only [blockSumE, skelRecover_skelFresh]
  rw [blockMeanE, ← h, lintegral_map (measurable_blockSumE (m := m) hf) measurable_skelFresh]
  simp_rw [e]

/-- **The mean of `f` over a block, averaged over the split** (MT p. 435): integrating the block
mean against `π* = split π` gives `Σ_{k<m} ∫ f d(πPᵏ) = m ∫ f dπ` for an invariant `π`. -/
theorem lintegral_blockMeanE_split [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {f : X → ℝ≥0∞} (hf : Measurable f) {π : Measure X} (hπ : IsInvariant P π) :
    ∫⁻ z, blockMeanE M f z ∂M.split π = m * ∫⁻ x, f x ∂π := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pathKernel (skelKernel M)
  have := M.isMarkovKernel_splitK
  have hpt : ∀ x, ∫⁻ z, blockMeanE M f z ∂M.splitK x =
      ∑ k ∈ Finset.range m, ∫⁻ y, f y ∂(P ^ k) x := by
    intro x
    have h1 : ∫⁻ z, blockMeanE M f z ∂M.splitK x =
        ∫⁻ ω, blockSumE f ω ∂pathMeasure (skelKernel M) (skelInit M (Measure.dirac x)) := by
      rw [pathMeasure_eq_comp, Measure.lintegral_bind (Kernel.aemeasurable _)
        (measurable_blockSumE hf).aemeasurable, skelInit, Minorization.split,
        Measure.dirac_bind M.splitK.measurable, lintegral_map
        (measurable_blockSumE hf).lintegral_kernel measurable_skelVirt]
      rfl
    have h2 : (fun ω => blockSumE f ω) = (fun φ : ℕ → X => ∑ k ∈ Finset.range m, f (φ k)) ∘
        skelRecover := rfl
    have hφ : Measurable fun φ : ℕ → X => ∑ k ∈ Finset.range m, f (φ k) :=
      Finset.measurable_sum _ fun k _ => hf.comp (measurable_pi_apply k)
    have h3 := lintegral_map (μ := pathMeasure (skelKernel M) (skelInit M (Measure.dirac x))) hφ
      measurable_skelRecover
    rw [h1, h2]
    erw [← h3]
    rw [skel_map_recover M (Measure.dirac x),
      pathMeasure_dirac, lintegral_finsetSum (f := fun k (a : ℕ → X) => f (a k)) _
        fun k _ => hf.comp (measurable_pi_apply k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← lintegral_map hf (measurable_pi_apply k), pathKernel_map_coord]
  rw [Minorization.split, Measure.lintegral_bind M.splitK.aemeasurable
    (measurable_blockMeanE M hf).aemeasurable]
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun k _ => hf.lintegral_kernel]
  have hk : ∀ k, ∫⁻ x, ∫⁻ y, f y ∂(P ^ k) x ∂π = ∫⁻ x, f x ∂π := by
    intro k
    have := isMarkovKernel_pow P k
    rw [← Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
    change ∫⁻ y, f y ∂((P ^ k) ∘ₘ π) = _
    rw [hπ.pow k]
  simp_rw [hk]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-- The initial segment sum `s₋₁(f)` for `f ≥ 0`, with values in `[0, ∞]`. -/
noncomputable def skelPreSumE [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ≥0∞)
    (ω : ℕ → (Fin m → X) × Bool) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range (m * (hitNat (skelAtom M) ω + 1)), f (skelRecover ω t)

omit [MeasurableSpace.CountablyGenerated X] in
/-- `s₋₁(f)` is the sum of the block sums up to the first visit. -/
theorem skelPreSumE_eq [NeZero m] (M : Minorization (P ^ m)) (f : X → ℝ≥0∞)
    (ω : ℕ → (Fin m → X) × Bool) :
    skelPreSumE M f ω =
      ∑ n ∈ Finset.range (hitNat (skelAtom M) ω + 1), blockSumE f (shift n ω) := by
  rw [skelPreSumE, skel_sum_range_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [blockSumE, skelRecover_shift]

omit [MeasurableSpace X] in
/-- A finite sum up to the first visit as a series over the times not after it. -/
theorem sum_range_hitNat_eq_tsum {Y : Type*} {α : Set Y} {ω : ℕ → Y}
    (h : firstHit α ω ≠ ⊤) (a : ℕ → ℝ≥0∞) :
    ∑ n ∈ Finset.range (hitNat α ω + 1), a n =
      ∑' n : ℕ, {ω : ℕ → Y | WithTop.some n ≤ firstHit α ω}.indicator (fun _ => a n) ω := by
  have hσ := firstHit_eq_hitNat h
  rw [tsum_eq_sum (s := Finset.range (hitNat α ω + 1))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ hitNat α ω := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    rw [indicator_of_mem]
    change WithTop.some n ≤ firstHit α ω
    rw [hσ]; exact WithTop.coe_le_coe.2 hn'
  · intro n hn
    rw [indicator_of_notMem]
    change ¬ WithTop.some n ≤ firstHit α ω
    rw [hσ]
    intro h'
    have := WithTop.coe_le_coe.1 h'
    simp only [Finset.mem_range] at hn
    omega

omit [MeasurableSpace.CountablyGenerated X] in
/-- `{n ≤ σ_α̂} ∈ 𝓕ₙ`. -/
theorem measurableSet_le_firstHit_natFilt [NeZero m] (M : Minorization (P ^ m)) (n : ℕ) :
    MeasurableSet[natFilt n]
      {ω : ℕ → (Fin m → X) × Bool | WithTop.some n ≤ firstHit (skelAtom M) ω} := by
  have : {ω : ℕ → (Fin m → X) × Bool | WithTop.some n ≤ firstHit (skelAtom M) ω} =
      ⋂ j ∈ Finset.range n, {ω | ω j ∈ (skelAtom M)ᶜ} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_compl_iff]
    exact le_firstHit_iff _ ω n
  rw [this]
  exact Finset.measurableSet_biInter _ fun j hj =>
    measurableSet_coord_natFilt (Finset.mem_range.1 hj).le (measurableSet_skelAtom M).compl

/-- **The mean of `s₋₁(f)` through the skeleton** (MT p. 435): conditioning each block on the
skeleton state at its start, `E_ρ[s₋₁(f)] = E_ρ[Σ_{n ≤ σ_α̌} blockMeanE(Φ_{nm}, Yₙ)]`. -/
theorem lintegral_skelPreSumE [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {f : X → ℝ≥0∞} (hf : Measurable f) (ρ : Measure ((Fin m → X) × Bool))
    [IsProbabilityMeasure ρ]
    (hρ : haveI := isMarkovKernel_skelKernel M
      ∀ᵐ ω ∂pathMeasure (skelKernel M) ρ, firstHit (skelAtom M) ω ≠ ⊤) :
    haveI := isMarkovKernel_skelKernel M
    ∫⁻ ω, skelPreSumE M f ω ∂pathMeasure (skelKernel M) ρ =
      ∫⁻ ω, cycleSumE M.checkAlpha (blockMeanE M f) (fun n => skelState (ω n))
        ∂pathMeasure (skelKernel M) ρ := by
  have := isMarkovKernel_skelKernel M
  set G : ℕ → Set (ℕ → (Fin m → X) × Bool) :=
    fun n => {ω | WithTop.some n ≤ firstHit (skelAtom M) ω} with hG
  have hGm : ∀ n, MeasurableSet (G n) := fun n =>
    (natFilt (X := (Fin m → X) × Bool)).le n _ (measurableSet_le_firstHit_natFilt M n)
  have hb : ∀ n, Measurable fun ω : ℕ → (Fin m → X) × Bool => blockSumE f (shift n ω) :=
    fun n => (measurable_blockSumE hf).comp (measurable_shift n)
  have hh : ∀ n, Measurable fun ω : ℕ → (Fin m → X) × Bool =>
      blockMeanE M f (skelState (ω n)) :=
    fun n => (measurable_blockMeanE M hf).comp (measurable_skelState.comp (measurable_pi_apply n))
  calc ∫⁻ ω, skelPreSumE M f ω ∂pathMeasure (skelKernel M) ρ
      = ∫⁻ ω, ∑' n, (G n).indicator (fun ω => blockSumE f (shift n ω)) ω
          ∂pathMeasure (skelKernel M) ρ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hρ] with ω hω
        rw [skelPreSumE_eq, sum_range_hitNat_eq_tsum hω]
        exact tsum_congr fun n => by simp only [hG, Set.indicator_apply]
    _ = ∑' n, ∫⁻ ω in G n, blockSumE f (shift n ω) ∂pathMeasure (skelKernel M) ρ := by
        rw [lintegral_tsum fun n => ((hb n).indicator (hGm n)).aemeasurable]
        exact tsum_congr fun n => lintegral_indicator (hGm n) _
    _ = ∑' n, ∫⁻ ω in G n, blockMeanE M f (skelState (ω n)) ∂pathMeasure (skelKernel M) ρ := by
        refine tsum_congr fun n => ?_
        rw [markov_lintegral _ ρ (measurableSet_le_firstHit_natFilt M n)
          (measurable_blockSumE hf)]
        exact setLIntegral_congr_fun (hGm n) fun ω _ => lintegral_blockSumE M hf (ω n)
    _ = _ := by
        rw [← tsum_congr fun n => lintegral_indicator (hGm n) _, ← lintegral_tsum fun n =>
          ((hh n).indicator (hGm n)).aemeasurable]
        refine lintegral_congr_ae ?_
        filter_upwards [hρ] with ω hω
        symm
        rw [cycleSumE, show hitNat M.checkAlpha (fun n => skelState (ω n)) =
          hitNat (skelAtom M) ω from rfl, sum_range_hitNat_eq_tsum hω]
        exact tsum_congr fun n => by simp only [hG, Set.indicator_apply]


omit [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] in
/-- `cycleSumE ∘ excursion = cycleSumE`. -/
theorem cycleSumE_excursion {Y : Type*} (α : Set Y) (g : Y → ℝ≥0∞) (ω : ℕ → Y) :
    cycleSumE α g (excursion α ω) = cycleSumE α g ω := by
  unfold cycleSumE
  rw [hitNat_excursion]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [excursion_apply_of_le_hitNat (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

/-- **The mean of the cycle sums (17.23)** in `[0, ∞]` (MT p. 435): if the `m`-skeleton is
Harris, `C ∈ B⁺(X)`, and `π` is invariant for `P` with `0 < π(C) < ∞`, then for measurable
`f ≥ 0`, `Ě_{ν*}[s₋₁(f)] = δ⁻¹ π(C)⁻¹ m ∫ f dπ`. -/
theorem lintegral_skelPreSumE_fresh [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {ψ : Measure X} (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ)
    (hψC : 0 < ψ M.C) {π : Measure X} (hπ : IsInvariant P π) (hπ0 : π M.C ≠ 0)
    (hπC : π M.C ≠ ∞) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, skelPreSumE M f ω ∂skelFreshLaw M = (M.δ * π M.C)⁻¹ * (m * ∫⁻ x, f x ∂π) := by
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have := isMarkovKernel_skelKernel M
  have := M.isProbabilityMeasure_ν
  have := isProbabilityMeasure_skelInit M M.ν
  have hL : ∀ z, hitProb M.splitKernel M.checkAlpha z = 1 :=
    M.hitProb_checkAlpha_eq_one (hH.hitProb_eq_one M.measurableSet_C hψC)
  have hρ := ae_firstHit_skelAtom_measure M hL (skelInit M M.ν)
  obtain ⟨c, hc⟩ : M.C.Nonempty := nonempty_of_measure_ne_zero hπ0
  have ha : (c, true) ∈ M.checkAlpha := ⟨hc, rfl⟩
  have hacc := ((M.theorem_5_1_3_ii ψ).2 hH.1.2.1 hψC).2.2 _ (M.isMaximalIrreducibility_split hH.1)
  have hrec := M.isRecurrentChain_split_of_isRecurrentChain hH.isRecurrentChain
  have hπs : IsInvariant M.splitKernel (M.split π) := (proposition_10_4_1_ii M).2 (hπ.pow m)
  have hα : M.split π M.checkAlpha = M.δ * π M.C := by
    rw [Minorization.checkAlpha, M.split_apply_true π M.measurableSet_C, inter_self]
  have hα0 : M.split π M.checkAlpha ≠ 0 := by rw [hα]; exact mul_ne_zero M.δ_pos.ne' hπ0
  have hαtop : M.split π M.checkAlpha ≠ ∞ := by rw [hα]; exact ENNReal.mul_ne_top M.δ_ne_top hπC
  have hπeq := theorem_10_2_1_ii_smul hacc hrec ha hπs.isSubinvariant hα0 hαtop
  have hg := measurable_blockMeanE M hf
  have hcyc : Measurable (cycleSumE M.checkAlpha (blockMeanE M f)) :=
    measurable_cycleSumE M.measurableSet_checkAlpha hg
  have hπ' : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (n : ℕ) => skelState (ω n) :=
    measurable_pi_iff.2 fun n => measurable_skelState.comp (measurable_pi_apply n)
  rw [skelFreshLaw, lintegral_skelPreSumE M hf _ hρ]
  rw [← lintegral_map hcyc hπ', skel_map_skelState M M.ν, ← M.splitKernel_apply_true c]
  have h1 := lintegral_cycleSumE M.splitKernel M.isAtom_checkAlpha (hL (c, true)) hg
  rw [cycleLaw, lintegral_map hcyc (measurable_excursion M.measurableSet_checkAlpha)] at h1
  simp_rw [cycleSumE_excursion] at h1
  rw [h1]
  have h2 : ∫⁻ z, blockMeanE M f z ∂M.split π =
      M.split π M.checkAlpha * ∫⁻ z, blockMeanE M f z
        ∂atomMeasure M.splitKernel M.isAtom_checkAlpha.1 (c, true) := by
    conv_lhs => rw [hπeq]
    rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_blockMeanE_split M hf hπ, hα] at h2
  rw [h2, ← mul_assoc, ENNReal.inv_mul_cancel (hα ▸ hα0) (hα ▸ hαtop), one_mul]


omit [MeasurableSpace.CountablyGenerated X] in
/-- `ofReal ∘ s₋₁ = s₋₁ ∘ ofReal` for `f ≥ 0`. -/
theorem ofReal_skelPreSum [NeZero m] (M : Minorization (P ^ m)) {f : X → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (ω : ℕ → (Fin m → X) × Bool) :
    ENNReal.ofReal (skelPreSum M f ω) = skelPreSumE M (fun x => ENNReal.ofReal (f x)) ω := by
  rw [skelPreSum, skelPreSumE, ENNReal.ofReal_sum_of_nonneg fun t _ => hf0 _]

omit [MeasurableSpace.CountablyGenerated X] in
/-- `s₋₁` is linear. -/
theorem skelPreSum_sub [NeZero m] (M : Minorization (P ^ m)) (f g : X → ℝ)
    (ω : ℕ → (Fin m → X) × Bool) :
    skelPreSum M (fun x => f x - g x) ω = skelPreSum M f ω - skelPreSum M g ω := by
  simp only [skelPreSum, Finset.sum_sub_distrib]

/-- (17.23) for `f ≥ 0`. -/
theorem integral_skelPreSum_of_nonneg [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {ψ : Measure X} (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ)
    (hψC : 0 < ψ M.C) {π : Measure X} (hπ : IsInvariant P π) (hπ0 : π M.C ≠ 0)
    (hπC : π M.C ≠ ∞) {f : X → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f π) :
    Integrable (skelPreSum M f) (skelFreshLaw M) ∧
      ∫ ω, skelPreSum M f ω ∂skelFreshLaw M = m * (∫ x, f x ∂π) / (M.δ * π M.C).toReal := by
  have hE := lintegral_skelPreSumE_fresh M hH hψC hπ hπ0 hπC
    (f := fun x => ENNReal.ofReal (f x)) (ENNReal.measurable_ofReal.comp hf)
  have hc0 : M.δ * π M.C ≠ 0 := mul_ne_zero M.δ_pos.ne' hπ0
  have hctop : M.δ * π M.C ≠ ∞ := ENNReal.mul_ne_top M.δ_ne_top hπC
  have hπf : ∫⁻ x, ENNReal.ofReal (f x) ∂π = ENNReal.ofReal (∫ x, f x ∂π) :=
    (ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hf0)).symm
  have hlin : ∫⁻ ω, ENNReal.ofReal (skelPreSum M f ω) ∂skelFreshLaw M =
      (M.δ * π M.C)⁻¹ * (m * ENNReal.ofReal (∫ x, f x ∂π)) := by
    simp_rw [ofReal_skelPreSum M hf0]
    rw [hE, hπf]
  have hfin : ∫⁻ ω, ENNReal.ofReal (skelPreSum M f ω) ∂skelFreshLaw M ≠ ∞ := by
    rw [hlin]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) ENNReal.ofReal_ne_top)
  have hm := (measurable_skelPreSum M hf).aestronglyMeasurable (μ := skelFreshLaw M)
  have h0 : 0 ≤ᵐ[skelFreshLaw M] skelPreSum M f :=
    Eventually.of_forall fun ω => Finset.sum_nonneg fun t _ => hf0 _
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hm h0).1 hfin, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0 hm, hlin]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (integral_nonneg hf0)]
  rw [div_eq_inv_mul]

/-- **(17.23)** (MT p. 435), the mean of the cycle sums for a general `m`: if the `m`-skeleton
is Harris, `C ∈ B⁺(X)`, `π` is invariant for `P` with `0 < π(C) < ∞` and `f ∈ L¹(π)`, then
`s₋₁(f)` is integrable under `P̌_{ν*}` with `Ě_{ν*}[s₋₁(f)] = δ⁻¹ π(C)⁻¹ m ∫ f dπ`; every cycle
sum `sⱼ(f)` has this law (`skel_map_cycle`), hence this mean. -/
theorem theorem_17_3_1_general_mean [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    {ψ : Measure X} (hH : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ)
    (hψC : 0 < ψ M.C) {π : Measure X} (hπ : IsInvariant P π) (hπ0 : π M.C ≠ 0)
    (hπC : π M.C ≠ ∞) {f : X → ℝ} (hf : Measurable f) (hfi : Integrable f π) :
    Integrable (skelPreSum M f) (skelFreshLaw M) ∧
      ∫ ω, skelPreSum M f ω ∂skelFreshLaw M = m * (∫ x, f x ∂π) / (M.δ * π M.C).toReal := by
  set fp : X → ℝ := fun x => max (f x) 0 with hfp
  set fn : X → ℝ := fun x => max (-f x) 0 with hfn
  have hpm : Measurable fp := hf.max measurable_const
  have hnm : Measurable fn := hf.neg.max measurable_const
  obtain ⟨hpi, hpe⟩ := integral_skelPreSum_of_nonneg M hH hψC hπ hπ0 hπC hpm
    (fun x => le_max_right _ _) (hfi.pos_part)
  obtain ⟨hni, hne⟩ := integral_skelPreSum_of_nonneg M hH hψC hπ hπ0 hπC hnm
    (fun x => le_max_right _ _) (hfi.neg_part)
  have hdec : skelPreSum M f = fun ω => skelPreSum M fp ω - skelPreSum M fn ω := by
    funext ω
    rw [← skelPreSum_sub]
    congr 1
    funext x
    change _ = max (f x) 0 - max (-f x) 0
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hfx : ∫ x, f x ∂π = ∫ x, fp x ∂π - ∫ x, fn x ∂π := by
    rw [← integral_sub hfi.pos_part hfi.neg_part]
    congr 1
    funext x
    change _ = max (f x) 0 - max (-f x) 0
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  refine ⟨by rw [hdec]; exact hpi.sub hni, ?_⟩
  rw [hdec, integral_sub hpi hni, hpe, hne, hfx]
  ring

end MeynTweedie.LimitTheorems

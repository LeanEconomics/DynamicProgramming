/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeometricErgodicity.SplitDichotomy
import GeometricErgodicity.ForwardRecurrence

/-!
# Classifying chains on countable spaces (MT §8.1)

Meyn and Tweedie, §8.1, pp. 173–177. `X` is countable with measurable singletons.

* `IsTransientState P α`, `IsRecurrentState P α` (p. 173): `U(α, α) < ∞`, resp. `= ∞`; by
  (8.5) (`potKernel_eq_lintegral_occTime`), `U(x, y) = E_x[η_y]`.
* **Proposition 8.1.1** (`proposition_8_1_1`, p. 173): for an irreducible chain, either
  `U(x, y) = ∞` for all `x, y`, or `U(x, y) < ∞` for all `x, y`.
* **Theorem 8.1.2** (`theorem_8_1_2`, p. 174): an irreducible chain is transient (every state
  transient) or recurrent (every state recurrent). `isRecurrentChain_count_iff`,
  `isTransientChain_count_iff`: these agree with the general definitions of §8.2.3 for counting
  measure.
* (8.7), the countable first-entrance decomposition (`firstEntrance_countable`, p. 174):
  `Pⁿ(x, α) = P_x(τ_α = n) + Σ_{j<n} P_x(τ_α = j) Pⁿ⁻ʲ(α, α)`.
* **Proposition 8.1.3** (`proposition_8_1_3`, p. 174): `U(x, x) = ∞` iff `L(x, x) = 1`.
* `one_sub_hitProb_ge_taboo`: `1 − L(x, A) ≥ ∫_E _APⁿ⁺¹(x, dz) (1 − L(z, A))` for `E ⊆ Aᶜ`.
* **Proposition 8.1.4** (`proposition_8_1_4`, p. 175): for an irreducible chain, either
  `L(x, y) = 1` for all `x, y`, or `L(x, x) < 1` for all `x`; `hitProb_eq_one_of_recurrent`
  (p. 175): recurrent countable chains are Harris recurrent, `L(x, A) ≡ 1` for `A ≠ ∅`.
* The forward recurrence time chain (p. 175): `fwdRec_hitProb_zero` (`L(0, 0) = 1`, the book's
  `L(1, 1) = 1` with states shifted by one) and `fwdRec_isRecurrentState_zero`.
* Renewal sequences (p. 175): `renewalPow p k = p^{∗k}`, `renewalSeq p = u`,
  `renewal_equation` (`u = δ₀ + u ∗ p`), `genFun`, `genFun_renewalSeq` (8.12):
  `U(z) = [1 − P(z)]⁻¹`, and `renewalSeq_genFun_one` (`U(1) = ∞` for a proper `p`).

**Corrections.**
* The renewal equation on p. 175, `u(n) = 1 + u ∗ p(n)`, holds only at `n = 0`; in general
  `u(n) = δ₀(n) + u ∗ p(n)`, which is what (8.12) encodes. For `p = δ₁`, `u ≡ 1` but
  `1 + u ∗ p(1) = 2` (`renewal_equation_counterexample`).
-/

namespace MeynTweedie.GeometricErgodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### A lower bound for escape probabilities -/

/-- **Escape through a taboo path.** If `E ⊆ Aᶜ`, then
`1 − L(x, A) ≥ ∫_E _APⁿ⁺¹(x, dz) (1 − L(z, A))`: the chain may avoid `A` up to time `n + 1`, be
in `E` at that time, and avoid `A` afterwards. -/
theorem one_sub_hitProb_ge_taboo (P : Kernel X X) [IsMarkovKernel P] {A E : Set X}
    (hA : MeasurableSet A) (hE : MeasurableSet E) (hEA : E ⊆ Aᶜ) (n : ℕ) (x : X) :
    ∫⁻ z in E, (1 - hitProb P A z) ∂tabooKernel P hA n x ≤ 1 - hitProb P A x := by
  have := isMarkovKernel_pathKernel P
  set G : Set (ℕ → X) := {ω | WithTop.some (n + 1) ≤ firstReturn A ω} ∩ {ω | ω (n + 1) ∈ E}
    with hGdef
  have hG : MeasurableSet[natFilt (n + 1)] G :=
    (measurableSet_natFilt_le_firstReturn hA (n + 1)).inter
      (measurableSet_coord_natFilt le_rfl hE)
  have hTop : MeasurableSet {ω : ℕ → X | firstReturn A ω = ⊤} := by
    convert (measurableSet_firstReturn_ne_top hA).compl using 1
    ext ω; simp
  have hsub : G ∩ shift (n + 1) ⁻¹' {ω | firstReturn A ω = ⊤} ⊆ {ω | firstReturn A ω = ⊤} := by
    rintro ω ⟨⟨h1, h2⟩, h3⟩
    simp only [mem_ofPred_eq, mem_preimage] at h1 h2 h3
    rw [mem_ofPred_eq, firstReturn_eq_top_iff]
    intro t ht htA
    rcases lt_trichotomy t (n + 1) with htn | htn | htn
    · exact (le_firstReturn_iff A ω (n + 1)).1 h1 t ht htn htA
    · rw [htn] at htA; exact hEA h2 htA
    · have := (firstReturn_eq_top_iff A _).1 h3 (t - (n + 1)) (by omega)
      rw [shift_apply, show n + 1 + (t - (n + 1)) = t by omega] at this
      exact this htA
  have hc : ∀ y, pathKernel P y {ω | firstReturn A ω = ⊤} = 1 - hitProb P A y := fun y => by
    have h := prob_compl_eq_one_sub (μ := pathKernel P y) (measurableSet_firstReturn_ne_top hA)
    have hset : {ω : ℕ → X | firstReturn A ω ≠ ⊤}ᶜ = {ω | firstReturn A ω = ⊤} := by
      ext ω; simp
    rwa [hset] at h
  rw [← hc x]
  refine le_trans ?_ (measure_mono hsub)
  rw [pathKernel_inter_shift P x hG hTop, hGdef, inter_comm,
    ← Measure.restrict_restrict (s := {ω : ℕ → X | ω (n + 1) ∈ E})
      (measurable_pi_apply (n + 1) hE),
    ← lintegral_indicator (s := {ω : ℕ → X | ω (n + 1) ∈ E}) (measurable_pi_apply (n + 1) hE)]
  have e : ({ω : ℕ → X | ω (n + 1) ∈ E}.indicator fun ω =>
      pathKernel P (ω (n + 1)) {ω | firstReturn A ω = ⊤}) =
      fun ω => E.indicator (fun y => pathKernel P y {ω | firstReturn A ω = ⊤}) (ω (n + 1)) := by
    ext ω; by_cases h : ω (n + 1) ∈ E <;> simp [h]
  rw [e, setLIntegral_le_firstReturn P hA n x ((Kernel.measurable_coe _ hTop).indicator hE),
    lintegral_indicator hE]
  exact le_of_eq (setLIntegral_congr_fun hE fun y _ => (hc y).symm)

variable [MeasurableSingletonClass X]

/-! ### States -/

/-- A state `α` is **transient** (MT p. 173) if `E_α[η_α] = U(α, α) < ∞`. -/
def IsTransientState (P : Kernel X X) (α : X) : Prop := potKernel P α {α} ≠ ∞

/-- A state `α` is **recurrent** (MT p. 173) if `E_α[η_α] = U(α, α) = ∞`. -/
def IsRecurrentState (P : Kernel X X) (α : X) : Prop := potKernel P α {α} = ∞

/-- `U(u, v) ≥ Pʳ(u, x) U(x, y) Pˢ(y, v)`, the bound (8.6). -/
theorem potKernel_singleton_ge (P : Kernel X X) (r s : ℕ) (u x y v : X) :
    (P ^ r) u {x} * potKernel P x {y} * (P ^ s) y {v} ≤ potKernel P u {v} := by
  rw [potKernel_apply P x (measurableSet_singleton y), potKernel_apply P u
    (measurableSet_singleton v), ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  calc ∑' n, (P ^ r) u {x} * (P ^ (n + 1)) x {y} * (P ^ s) y {v}
      ≤ ∑' n, (P ^ ((n + (r + s)) + 1)) u {v} := ENNReal.tsum_le_tsum fun n => by
        calc (P ^ r) u {x} * (P ^ (n + 1)) x {y} * (P ^ s) y {v}
            ≤ (P ^ (r + (n + 1))) u {y} * (P ^ s) y {v} :=
              mul_le_mul' (pow_add_singleton_ge P r (n + 1) u x y) le_rfl
          _ ≤ (P ^ (r + (n + 1) + s)) u {v} := pow_add_singleton_ge P _ s u y v
          _ = _ := by rw [show r + (n + 1) + s = n + (r + s) + 1 by omega]
    _ ≤ ∑' n, (P ^ (n + 1)) u {v} :=
        ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective (r + s))
          fun n => (P ^ (n + 1)) u {v}

/-- **Proposition 8.1.1** (MT p. 173): for an irreducible chain on a countable space, either
`U(x, y) = ∞` for all `x, y`, or `U(x, y) < ∞` for all `x, y`. -/
theorem proposition_8_1_1 [Countable X] (P : Kernel X X) [IsMarkovKernel P]
    (h : IsIrreducibleChain P) :
    (∀ x y, potKernel P x {y} = ∞) ∨ (∀ x y, potKernel P x {y} ≠ ∞) := by
  by_cases hex : ∃ x y, potKernel P x {y} = ∞
  · left
    obtain ⟨x, y, hxy⟩ := hex
    have : Nonempty X := ⟨x⟩
    have hc := (isIrreducibleChain_iff P).1 h
    intro u v
    obtain ⟨r, hr⟩ := (leads_iff_exists_pow P u x).1 (hc u x).1
    obtain ⟨s, hs⟩ := (leads_iff_exists_pow P y v).1 (hc y v).1
    refine top_le_iff.1 ((?_ : ∞ ≤ _).trans (potKernel_singleton_ge P r s u x y v))
    rw [hxy, ENNReal.mul_top hr.ne', ENNReal.top_mul hs.ne']
  · right
    push Not at hex
    exact hex

/-- **Theorem 8.1.2** (MT p. 174): an irreducible chain on a countable space is either transient
(every state transient) or recurrent (every state recurrent). -/
theorem theorem_8_1_2 [Countable X] (P : Kernel X X) [IsMarkovKernel P]
    (h : IsIrreducibleChain P) : (∀ x, IsTransientState P x) ∨ (∀ x, IsRecurrentState P x) := by
  rcases proposition_8_1_1 P h with h' | h'
  · exact Or.inr fun x => h' x x
  · exact Or.inl fun x => h' x x

/-- For an irreducible chain on a countable space, recurrence in the sense of §8.2.3 for
counting measure is recurrence of every state. -/
theorem isRecurrentChain_count_iff [Countable X] [Nonempty X] (P : Kernel X X)
    [IsMarkovKernel P] (h : IsIrreducibleChain P) :
    IsRecurrentChain P Measure.count ↔ ∀ x, IsRecurrentState P x := by
  have hmax := isMaximalIrreducibility_count P h
  constructor
  · intro hr x
    exact hr.2 {x} (measurableSet_singleton x) (by simp) x
  · intro hr
    refine ⟨hmax, fun A hA hpos x => ?_⟩
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hpos.ne'
    rcases proposition_8_1_1 P h with h' | h'
    · exact top_le_iff.1 ((h' x y).symm.le.trans (measure_mono (singleton_subset_iff.2 hy)))
    · exact absurd (hr y) (h' y y)

/-- For an irreducible chain on a countable space, transience in the sense of §8.2.3 for
counting measure is transience of every state. -/
theorem isTransientChain_count_iff [Countable X] [Nonempty X] (P : Kernel X X)
    [IsMarkovKernel P] (h : IsIrreducibleChain P) :
    IsTransientChain P Measure.count ↔ ∀ x, IsTransientState P x := by
  have hmax := isMaximalIrreducibility_count P h
  constructor
  · intro ht x hx
    exact ht.not_isRecurrentChain ((isRecurrentChain_count_iff P h).2 fun y => by
      rcases proposition_8_1_1 P h with h' | h'
      · exact h' y y
      · exact absurd hx (h' x x))
  · intro ht
    obtain ⟨f, hf⟩ := exists_surjective_nat X
    refine ⟨hmax, fun n => {f n}, fun n => ⟨measurableSet_singleton _, _, ht (f n),
      fun x hx => by rw [mem_singleton_iff.1 hx]⟩, fun x _ => ?_⟩
    obtain ⟨n, rfl⟩ := hf x
    exact mem_iUnion.2 ⟨n, rfl⟩

/-- (8.7), MT p. 174, the first-entrance decomposition on a countable space:
`Pⁿ⁺¹(x, α) = P_x(τ_α = n + 1) + Σ_{j<n} P_x(τ_α = j + 1) Pⁿ⁻ʲ(α, α)`. -/
theorem firstEntrance_countable (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) (x α : X) :
    (P ^ (n + 1)) x {α} = pathKernel P x {ω | firstReturn {α} ω = WithTop.some (n + 1)} +
      ∑ j ∈ Finset.range n, pathKernel P x {ω | firstReturn {α} ω = WithTop.some (j + 1)} *
        (P ^ (n - j)) α {α} := by
  have hα := measurableSet_singleton α
  rw [firstEntrance_decomposition P hα n x hα, firstReturn_eq_tabooProb]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_singleton, firstReturn_eq_tabooKernel P hα j x, mul_comm]

/-- **Proposition 8.1.3** (MT p. 174): `U(x, x) = ∞` iff `L(x, x) = 1`. -/
theorem proposition_8_1_3 (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    potKernel P x {x} = ∞ ↔ hitProb P {x} x = 1 :=
  (isAtom_singleton P x).potKernel_eq_top_iff (mem_singleton x)

/-- **Proposition 8.1.4** (MT p. 175): for an irreducible chain on a countable space, either
`L(x, y) = 1` for all `x, y`, or `L(x, x) < 1` for all `x`. -/
theorem proposition_8_1_4 [Countable X] (P : Kernel X X) [IsMarkovKernel P]
    (h : IsIrreducibleChain P) :
    (∀ x y, hitProb P {y} x = 1) ∨ (∀ x, hitProb P {x} x < 1) := by
  rcases proposition_8_1_1 P h with h' | h'
  · left
    have hLL : ∀ x, hitProb P {x} x = 1 := fun x => (proposition_8_1_3 P x).1 (h' x x)
    intro x y
    by_cases hxy : x = y
    · rw [hxy]; exact hLL y
    by_contra hne
    have hlt : hitProb P {y} x < 1 := lt_of_le_of_ne (hitProb_le_one P _ x) hne
    have : Nonempty X := ⟨x⟩
    have hc := (isIrreducibleChain_iff P).1 h
    have hy := measurableSet_singleton y
    have hx := measurableSet_singleton x
    -- `U_y(y, {x}) > 0`: otherwise `U(y, x) = 0` by the last-exit decomposition
    have hUpos : 0 < potKernel P y {x} := by
      rcases (hc y x).1 with h1 | h1
      · exact absurd h1.symm hxy
      · exact (potKernel_pos_iff P hx y).2 ((hitProb_pos_iff P hx y).1 h1)
    have hUy : tabooPotKernel P hy y {x} ≠ 0 := by
      intro h0
      refine hUpos.ne' (potKernel_eq_zero_of_lastExit P hy y hx h0 ?_)
      rw [lintegral_singleton, h0, zero_mul]
    obtain ⟨n, hn⟩ : ∃ n, tabooKernel P hy n y {x} ≠ 0 := by
      by_contra hc'
      push Not at hc'
      exact hUy (by rw [tabooPotKernel, Kernel.sum_apply' _ _ hx]; simp [hc'])
    have hesc := one_sub_hitProb_ge_taboo P hy hx (by
      intro z hz; rw [mem_singleton_iff.1 hz]; exact fun h => hxy (mem_singleton_iff.1 h)) n y
    rw [lintegral_singleton, hLL y, tsub_self, nonpos_iff_eq_zero, mul_eq_zero] at hesc
    rcases hesc with h1 | h1
    · exact (tsub_pos_of_lt hlt).ne' h1
    · exact hn h1
  · right
    intro x
    exact lt_of_le_of_ne (hitProb_le_one P _ x) fun h1 => h' x x ((proposition_8_1_3 P x).2 h1)

/-- MT p. 175: on a countable space a recurrent irreducible chain is Harris recurrent:
`L(x, A) = 1` for every `x` and every non-empty `A`. -/
theorem hitProb_eq_one_of_recurrent [Countable X] (P : Kernel X X) [IsMarkovKernel P]
    (h : IsIrreducibleChain P) (hrec : ∀ x, IsRecurrentState P x) {A : Set X}
    (hA : A.Nonempty) (x : X) : hitProb P A x = 1 := by
  obtain ⟨y, hy⟩ := hA
  rcases proposition_8_1_4 P h with h' | h'
  · exact le_antisymm (hitProb_le_one P A x)
      ((h' x y).symm.le.trans (hitProb_mono P (singleton_subset_iff.2 hy) x))
  · exact absurd ((proposition_8_1_3 P y).1 (hrec y)) (h' y).ne

/-! ### The forward recurrence time chain -/

/-- The forward recurrence time chain returns to `0` surely (MT p. 175, where the state `0`
here is the book's state `1`): `L(0, 0) = 1` when `p` is a probability. -/
theorem fwdRec_hitProb_zero (p : Measure ℕ) [IsProbabilityMeasure p] :
    haveI := isMarkovKernel_fwdRecKernel p; ∀ j, hitProb (fwdRecKernel p) {0} j = 1 := by
  have := isMarkovKernel_fwdRecKernel p
  have h0 := measurableSet_singleton (0 : ℕ)
  have hpos : ∀ j, j ≠ 0 → hitProb (fwdRecKernel p) {0} j = 1 := fun j hj => by
    refine le_antisymm (hitProb_le_one _ _ j) ?_
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    calc (1 : ℝ≥0∞) = (fwdRecKernel p ^ (k + 1)) (k + 1) {0} := by
          rw [fwdRec_pow_self, Measure.dirac_apply_of_mem (mem_singleton 0)]
      _ ≤ _ := pow_le_hitProb _ h0 k (k + 1)
  intro j
  by_cases hj : j = 0
  · rw [hj, hitProb_first_step _ h0 0, setLIntegral_congr_fun h0.compl fun y hy => hpos y hy,
      setLIntegral_const, one_mul, measure_add_measure_compl h0, measure_univ]
  · exact hpos j hj

/-- The forward recurrence time chain is recurrent at `0` (MT p. 175): `U(0, 0) = ∞`. -/
theorem fwdRec_isRecurrentState_zero (p : Measure ℕ) [IsProbabilityMeasure p] :
    haveI := isMarkovKernel_fwdRecKernel p; IsRecurrentState (fwdRecKernel p) 0 := by
  have := isMarkovKernel_fwdRecKernel p
  exact (proposition_8_1_3 _ 0).2 (fwdRec_hitProb_zero p 0)

/-- An irreducible forward recurrence time chain is recurrent: every state is recurrent. -/
theorem fwdRec_isRecurrentState (p : Measure ℕ) [IsProbabilityMeasure p]
    (h : haveI := isMarkovKernel_fwdRecKernel p; IsIrreducibleChain (fwdRecKernel p)) :
    haveI := isMarkovKernel_fwdRecKernel p; ∀ j, IsRecurrentState (fwdRecKernel p) j := by
  have := isMarkovKernel_fwdRecKernel p
  rcases theorem_8_1_2 _ h with h' | h'
  · exact absurd (fwdRec_isRecurrentState_zero p) (h' 0)
  · exact h'

/-! ### Renewal sequences -/

/-- The convolution powers `p^{∗k}` of a sequence `p` on `ℤ₊` (`p^{∗0} = δ₀`): the law of the
renewal time `Z_k` of a zero-delayed renewal process with increment law `p` (MT §2.4). -/
noncomputable def renewalPow (p : ℕ → ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞
  | 0 => diracDist 0
  | k + 1 => sampleConv (renewalPow p k) p

/-- The renewal sequence `u(n) = Σ_{k ≥ 0} P(Z_k = n) = Σ_k p^{∗k}(n)` (MT p. 175). -/
noncomputable def renewalSeq (p : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ := ∑' k, renewalPow p k n

/-- The generating function `A(z) = Σₙ a(n) zⁿ`. -/
noncomputable def genFun (a : ℕ → ℝ≥0∞) (z : ℝ≥0∞) : ℝ≥0∞ := ∑' n, a n * z ^ n

/-- The generating function of a convolution is the product of the generating functions. -/
theorem genFun_sampleConv (a b : ℕ → ℝ≥0∞) (z : ℝ≥0∞) :
    genFun (sampleConv a b) z = genFun a z * genFun b z := by
  unfold genFun sampleConv
  have : ∀ n, (∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2) * z ^ n =
      ∑ p ∈ Finset.antidiagonal n, a p.1 * z ^ p.1 * (b p.2 * z ^ p.2) := fun n => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.mem_antidiagonal.1 hp, pow_add]
    ring
  simp_rw [this]
  rw [tsum_sum_antidiagonal (fun p => a p.1 * z ^ p.1 * (b p.2 * z ^ p.2)),
    ← ENNReal.tsum_mul_right]
  exact tsum_congr fun i => by dsimp only; exact ENNReal.tsum_mul_left

/-- **The renewal equation**, MT p. 175 (corrected): `u = δ₀ + u ∗ p`. -/
theorem renewal_equation (p : ℕ → ℝ≥0∞) (n : ℕ) :
    renewalSeq p n = diracDist 0 n + sampleConv (renewalSeq p) p n := by
  rw [renewalSeq, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  unfold sampleConv renewalSeq
  simp only [renewalPow, sampleConv]
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  exact Finset.sum_congr rfl fun q _ => ENNReal.tsum_mul_right

/-- **(8.12)**, MT p. 176: the generating function of the renewal sequence is
`U(z) = [1 − P(z)]⁻¹`. -/
theorem genFun_renewalSeq (p : ℕ → ℝ≥0∞) (z : ℝ≥0∞) :
    genFun (renewalSeq p) z = (1 - genFun p z)⁻¹ := by
  have hpow : ∀ k, genFun (renewalPow p k) z = genFun p z ^ k := fun k => by
    induction k with
    | zero =>
      rw [pow_zero, renewalPow, genFun, tsum_eq_single 0 fun n hn => by simp [diracDist, hn]]
      simp [diracDist]
    | succ k ih => rw [renewalPow, genFun_sampleConv, ih, pow_succ]
  unfold genFun renewalSeq
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_geometric]
  exact tsum_congr fun k => (hpow k)

/-- A renewal process with a proper increment law is recurrent (MT p. 176): `U(1) = ∞`. -/
theorem renewalSeq_genFun_one {p : ℕ → ℝ≥0∞} (hp : ∑' n, p n = 1) :
    genFun (renewalSeq p) 1 = ∞ := by
  rw [genFun_renewalSeq]
  have : genFun p 1 = 1 := by simp [genFun, hp]
  rw [this, tsub_self, ENNReal.inv_zero]

/-- **Correction to the renewal equation of MT p. 175**: `u(n) = 1 + u ∗ p(n)` fails for
`n ≥ 1`. For `p = δ₁` the renewal times are `Z_k = k`, so `u ≡ 1`, but `1 + u ∗ p(1) = 2`. -/
theorem renewal_equation_counterexample :
    renewalSeq (diracDist 1) 1 = 1 ∧
      1 + sampleConv (renewalSeq (diracDist 1)) (diracDist 1) 1 = 2 := by
  have hpow : ∀ k, renewalPow (diracDist 1) k = diracDist k := fun k => by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [renewalPow, ih]
      funext n
      unfold sampleConv diracDist
      by_cases hn : n = k + 1
      · subst hn
        rw [Finset.sum_eq_single (k, 1)]
        · simp
        · intro b hb hne
          rw [Finset.mem_antidiagonal] at hb
          by_cases h1 : b.1 = k
          · exact absurd (Prod.ext h1 (by omega)) hne
          · simp [h1]
        · intro h
          exact absurd (Finset.mem_antidiagonal.2 (show (k, 1).1 + (k, 1).2 = k + 1 from rfl)) h
      · have hz : (if n = k + 1 then (1 : ℝ≥0∞) else 0) = 0 := by simp [hn]
        rw [hz]
        refine Finset.sum_eq_zero fun b hb => ?_
        rw [Finset.mem_antidiagonal] at hb
        by_cases h1 : b.1 = k
        · have : b.2 ≠ 1 := by omega
          simp [h1, this]
        · simp [h1]
  have hu : ∀ n, renewalSeq (diracDist 1) n = 1 := fun n => by
    rw [renewalSeq]
    simp_rw [hpow]
    unfold diracDist
    rw [tsum_eq_single n fun k hk => by simp [Ne.symm hk]]
    simp
  refine ⟨hu 1, ?_⟩
  unfold sampleConv
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  simp [hu, diracDist]
  norm_num

end MeynTweedie.GeometricErgodicity

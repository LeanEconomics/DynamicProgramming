/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.MinimalInvariant
import FErgodicity.SplitDichotomy

/-!
# The existence of π: chains with atoms (MT §10.2)

Meyn and Tweedie, §10.2, pp. 234–236.

**Return times and taboo potentials.**
* `meanReturnTime P A x = E_x[τ_A]` (with `τ_A = ∞` counted as `∞`), and (10.12)
  `meanReturnTime_eq_tabooPotKernel`: `E_x[τ_A] = Σ_{n ≥ 1} P_x(τ_A ≥ n) = U_A(x, X)`;
  `coe_eq_tsum_le`: `e = Σ_{n ≥ 0} 1{n + 1 ≤ e}` in `[0, ∞]`.
* (10.13) `tabooPotKernel_eq_lintegral`: `U_A(x, B) = E_x[Σ_{n=1}^{τ_A} 1{Φₙ ∈ B}]`.
* `IsAtom.tabooKernel_eq`, `IsAtom.tabooPotKernel_eq`: on an atom, `_αPⁿ(y, ·)` and `U_α(y, ·)`
  do not depend on `y ∈ α`; `IsAccessibleAtom.isRecurrentChain_iff`: the chain is recurrent iff
  `L(a, α) = 1`.

**The invariant measure of an atom.** `atomMeasure P hα a = μ°_α = U_α(a, ·)` (10.10), for a point
`a ∈ α`. With `ν = P(a, ·)` and `S = Σ_{n ≥ 2} _αPⁿ(a, ·)`, the two identities
`atomMeasure_eq` (`μ°_α = ν + S`) and `comp_atomMeasure` (`μ°_αP = L(a, α) ν + S`) are (10.11).
`minimalMeasure_atom`: for every `μ`, the minimal measure of §10.4.2 is `μ°_A = μ(α) μ°_α`.

**Results.**
* **Theorem 10.2.1** (p. 234), for an accessible atom `α` and `a ∈ α`:
  (i) `theorem_10_2_1_i`, `μ°_α` is a subinvariant measure, invariant iff the chain is recurrent;
  (ii) `theorem_10_2_1_ii`, `μ ≥ μ°_α` for every subinvariant `μ` with `μ(α) = 1`, and
  `theorem_10_2_1_ii_unique`, if the chain is recurrent such a `μ` equals `μ°_α`;
  `theorem_10_2_1_ii_smul`: every subinvariant `μ` with `0 < μ(α) < ∞` is `μ(α) μ°_α`, and
  `IsSubinvariantMeasure.eq_smul_atomMeasure`: every subinvariant measure (σ-finite) is a
  multiple of `μ°_α`;
  (iii) `theorem_10_2_1_iii`, `μ°_α(X) = E_a[τ_α]`, so `μ°_α` is finite iff `E_a[τ_α] < ∞`, and
  then it is invariant.
* **Theorem 10.2.2** (Kac's theorem, `theorem_10_2_2`, p. 236): the chain is positive iff
  `E_a[τ_α] < ∞`, and every invariant probability `π` has `π(α) = E_a[τ_α]⁻¹` (10.14).
* **Proposition 10.2.3** (`proposition_10_2_3`, p. 236): on a countable space, for a positive
  chain whose maximal irreducibility measure charges every point, every invariant probability is
  `π(x) = E_x[τ_x]⁻¹`; in particular it is unique (`proposition_10_2_3_unique`).
* `IsSubinvariantMeasure.exists_finite_pos` and `IsSubinvariantMeasure.measure_lt_top_of_petite`:
  a subinvariant measure of a `ψ`-irreducible chain is finite on petite sets, and on atoms
  (`IsSubinvariantMeasure.measure_atom_lt_top`).

**Corrections.** None. The uniqueness in Theorem 10.2.1 (ii) is proved without σ-finiteness of
`μ`, by comparing `∫ μ(dx) K_{a_{1/2}}(x, α)` with `∫ μ°_α(dx) K_{a_{1/2}}(x, α)`
(`eq_of_le_of_lintegral_le`); the book's choice of a set `A` on which `Pⁿ(·, α)` is positive
needs an extra exhaustion step.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Mean return times -/

/-- The mean return time `E_x[τ_A]` (MT p. 234), with `τ_A = ∞` counted as `∞`. -/
noncomputable def meanReturnTime (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) :
    ℝ≥0∞ :=
  ∫⁻ ω, ENat.toENNReal (firstReturn A ω) ∂pathKernel P x

/-- `e = Σ_{n ≥ 0} 1{n + 1 ≤ e}` for `e ∈ ℕ ∪ {∞}`. -/
theorem coe_eq_tsum_le (e : WithTop ℕ) :
    ENat.toENNReal e = ∑' n : ℕ, {n : ℕ | WithTop.some (n + 1) ≤ e}.indicator 1 n := by
  cases e with
  | top =>
    have : ∀ n : ℕ, {n : ℕ | WithTop.some (n + 1) ≤ (⊤ : WithTop ℕ)}.indicator
        (1 : ℕ → ℝ≥0∞) n = 1 :=
      fun n => indicator_of_mem (s := {n : ℕ | WithTop.some (n + 1) ≤ (⊤ : WithTop ℕ)})
        (le_top : WithTop.some (n + 1) ≤ (⊤ : WithTop ℕ)) 1
    rw [tsum_congr this, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
    exact ENat.toENNReal_top
  | coe k =>
    rw [tsum_eq_sum (s := Finset.range k) (fun n hn => by
      have : ¬ (WithTop.some (n + 1) ≤ (k : WithTop ℕ)) := by
        simp only [Finset.mem_range, not_lt] at hn
        intro h
        have h' : n + 1 ≤ k := WithTop.coe_le_coe.1 h
        omega
      exact indicator_of_notMem (s := {n : ℕ | WithTop.some (n + 1) ≤ (k : WithTop ℕ)}) this 1)]
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞)) (fun n hn => by
      have : WithTop.some (n + 1) ≤ (k : WithTop ℕ) := by
        simp only [Finset.mem_range] at hn
        exact WithTop.coe_le_coe.2 hn
      exact indicator_of_mem (s := {n : ℕ | WithTop.some (n + 1) ≤ (k : WithTop ℕ)}) this 1)]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact ENat.toENNReal_coe k

/-- (10.12), MT p. 235: `E_x[τ_A] = Σ_{n ≥ 1} P_x(τ_A ≥ n) = U_A(x, X)`. -/
theorem meanReturnTime_eq_tabooPotKernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) : meanReturnTime P A x = tabooPotKernel P hA x univ := by
  rw [meanReturnTime, tabooPotKernel_apply P hA x MeasurableSet.univ]
  have h : ∀ ω : ℕ → X, ENat.toENNReal (firstReturn A ω) =
      ∑' n : ℕ, {ω : ℕ → X | WithTop.some (n + 1) ≤ firstReturn A ω}.indicator 1 ω := by
    intro ω
    refine (coe_eq_tsum_le _).trans (tsum_congr fun n => ?_)
    by_cases hn : WithTop.some (n + 1) ≤ firstReturn A ω
    · rw [indicator_of_mem (s := {n : ℕ | WithTop.some (n + 1) ≤ firstReturn A ω}) hn,
        indicator_of_mem (s := {ω : ℕ → X | WithTop.some (n + 1) ≤ firstReturn A ω}) hn]
      rfl
    · rw [indicator_of_notMem (s := {n : ℕ | WithTop.some (n + 1) ≤ firstReturn A ω}) hn,
        indicator_of_notMem (s := {ω : ℕ → X | WithTop.some (n + 1) ≤ firstReturn A ω}) hn]
  simp_rw [h]
  rw [lintegral_tsum fun n => (measurable_one.indicator
    (measurableSet_le_firstReturn hA (n + 1))).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [lintegral_indicator_one (measurableSet_le_firstReturn hA (n + 1)), tabooProb]
  congr 1
  ext ω
  simp

/-- (10.13), MT p. 236: `U_A(x, B) = E_x[Σ_{n=1}^{τ_A} 1{Φₙ ∈ B}]`, the expected number of
visits to `B` up to and including the first return to `A`. -/
theorem tabooPotKernel_eq_lintegral (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) {B : Set X} (hB : MeasurableSet B) :
    tabooPotKernel P hA x B = ∫⁻ ω, ∑' n : ℕ, ({ω : ℕ → X | ω (n + 1) ∈ B} ∩
      {ω | WithTop.some (n + 1) ≤ firstReturn A ω}).indicator 1 ω ∂pathKernel P x := by
  rw [tabooPotKernel_apply P hA x hB, lintegral_tsum]
  · refine tsum_congr fun n => ?_
    rw [tabooProb]
    exact (lintegral_indicator_one (s := {ω : ℕ → X | ω (n + 1) ∈ B} ∩
      {ω | WithTop.some (n + 1) ≤ firstReturn A ω}) ((measurable_pi_apply (n + 1) hB).inter
      (measurableSet_le_firstReturn hA (n + 1)))).symm
  · exact fun n => (measurable_one.indicator ((measurable_pi_apply (n + 1) hB).inter
      (measurableSet_le_firstReturn hA (n + 1)))).aemeasurable

/-! ### Taboo kernels on an atom -/

/-- `(P I_{Aᶜ})ⁿ⁺¹ P = [(P I_{Aᶜ})ⁿ P] ∘ (P I_{Aᶜ})`: the first step is by `P`. -/
theorem tabooKernel_succ_eq' (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    tabooKernel P hA (n + 1) = tabooKernel P hA n ∘ₖ (indKernel hA.compl ∘ₖ P) := by
  unfold tabooKernel
  rw [show n + 1 = 1 + n from add_comm n 1, pow_add_eq _ 1 n, pow_one]
  simp only [Kernel.comp_assoc]

/-- On an atom, `_αPⁿ⁺¹(y, ·)` does not depend on `y ∈ α`. -/
theorem IsAtom.tabooKernel_eq {P : Kernel X X} {α : Set X} (hα : IsAtom P α) {x y : X}
    (hx : x ∈ α) (hy : y ∈ α) (n : ℕ) : tabooKernel P hα.1 n x = tabooKernel P hα.1 n y := by
  obtain ⟨ν, hν⟩ := hα.2
  cases n with
  | zero => rw [tabooKernel_zero, hν x hx, hν y hy]
  | succ n => simp only [tabooKernel_succ_eq', Kernel.comp_apply, hν x hx, hν y hy]

/-- On an atom, `U_α(y, ·)` does not depend on `y ∈ α`. -/
theorem IsAtom.tabooPotKernel_eq {P : Kernel X X} {α : Set X} (hα : IsAtom P α) {x y : X}
    (hx : x ∈ α) (hy : y ∈ α) : tabooPotKernel P hα.1 x = tabooPotKernel P hα.1 y := by
  rw [tabooPotKernel, Kernel.sum_apply, Kernel.sum_apply]
  congr 1
  funext n
  exact hα.tabooKernel_eq hx hy n

/-- For an accessible atom and `a ∈ α`, the chain is recurrent iff `L(a, α) = 1`. -/
theorem IsAccessibleAtom.isRecurrentChain_iff {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} {α : Set X} (h : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) :
    IsRecurrentChain P ψ ↔ hitProb P α a = 1 := by
  obtain ⟨hat, hψ, hψα⟩ := h
  constructor
  · intro hr
    exact (hat.potKernel_eq_top_iff ha).1 (hr.2 α hat.1 hψα a)
  · intro hL
    refine theorem_8_2_1_i P hψ hat hψα fun y hy => ?_
    rw [hat.potKernel_eq hy ha hat.1]
    exact (hat.potKernel_eq_top_iff ha).2 hL

/-! ### The measure `μ°_α` -/

/-- The measure `μ°_α(A) = U_α(a, A) = Σ_{n ≥ 1} _αPⁿ(a, A)` (10.10), MT p. 234, for a point
`a` of the atom `α`. -/
noncomputable def atomMeasure (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (a : X) :
    Measure X :=
  tabooPotKernel P hα a

/-- `μ°_α(α) = L(a, α)`. -/
theorem atomMeasure_self (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) : atomMeasure P hα a α = hitProb P α a :=
  tabooPotKernel_self P hα a

/-- (10.12): `μ°_α(X) = E_a[τ_α]`. -/
theorem atomMeasure_univ (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) : atomMeasure P hα a univ = meanReturnTime P α a :=
  (meanReturnTime_eq_tabooPotKernel P hα a).symm

/-- `μ°_α` is the image of `δ_a` under `U_α`. -/
theorem atomMeasure_eq_comp (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (a : X) :
    atomMeasure P hα a = tabooPotKernel P hα ∘ₘ Measure.dirac a :=
  (dirac_kernel _ a).symm

/-- On an atom with `P(y, ·) = ν`, `(m restricted to α) P = m(α) ν`. -/
theorem comp_restrict_atom {P : Kernel X X} {α : Set X} (hα : MeasurableSet α) {ν : Measure X}
    (hν : ∀ y ∈ α, P y = ν) (m : Measure X) : P ∘ₘ m.restrict α = m α • ν := by
  ext B hB
  rw [measure_kernel_apply _ _ hB, setLIntegral_congr_fun hα (fun y hy => by rw [hν y hy]),
    setLIntegral_const, Measure.smul_apply, smul_eq_mul, mul_comm]

/-- The sum `S = Σ_{n ≥ 2} _αPⁿ(a, ·)`. -/
noncomputable def atomTail (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (a : X) :
    Measure X :=
  Measure.sum fun n => tabooSeq P hα (Measure.dirac a) (n + 1)

/-- `μ°_α = P(a, ·) + S`. -/
theorem atomMeasure_eq (P : Kernel X X) {α : Set X} (hα : MeasurableSet α) (a : X) :
    atomMeasure P hα a = P a + atomTail P hα a := by
  rw [atomMeasure_eq_comp, tabooPotKernel_comp_eq, dirac_kernel]
  rfl

/-- (10.11): on an atom, `μ°_αP = L(a, α) P(a, ·) + S`. -/
theorem comp_atomMeasure {P : Kernel X X} [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {a : X} (ha : a ∈ α) :
    P ∘ₘ atomMeasure P hα.1 a = hitProb P α a • P a + atomTail P hα.1 a := by
  obtain ⟨ν, hν⟩ := hα.2
  rw [atomMeasure_eq_comp, comp_tabooPotKernel_comp, comp_restrict_atom hα.1 hν,
    ← atomMeasure_eq_comp, atomMeasure_self, hν a ha]
  rfl

/-- For an atom, the minimal measure of §10.4.2 is `μ°_A = μ(α) μ°_α`. -/
theorem minimalMeasure_atom {P : Kernel X X} {α : Set X} (hα : IsAtom P α) {a : X}
    (ha : a ∈ α) (μ : Measure X) :
    minimalMeasure P hα.1 μ = μ α • atomMeasure P hα.1 a := by
  ext B hB
  rw [minimalMeasure_apply P hα.1 μ hB, setLIntegral_congr_fun hα.1
    (fun y hy => by rw [hα.tabooPotKernel_eq hy ha]), setLIntegral_const, Measure.smul_apply,
    smul_eq_mul, mul_comm]
  rfl

/-- `μ°_α` is subinvariant (first part of (10.11)). -/
theorem isSubinvariant_atomMeasure {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) : IsSubinvariant P (atomMeasure P hα.1 a) := by
  unfold IsSubinvariant
  rw [comp_atomMeasure hα ha, atomMeasure_eq]
  refine add_le_add_left (Measure.le_intro fun B _ _ => ?_) _
  rw [Measure.smul_apply, smul_eq_mul]
  exact mul_le_of_le_one_left zero_le (hitProb_le_one P α a)

/-- If `L(a, α) = 1`, then `μ°_α` is invariant. -/
theorem isInvariant_atomMeasure {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) (hL : hitProb P α a = 1) :
    IsInvariant P (atomMeasure P hα.1 a) := by
  unfold IsInvariant
  rw [comp_atomMeasure hα ha, hL, one_smul, ← atomMeasure_eq]

/-! ### Theorem 10.2.1 -/

/-- **Theorem 10.2.1 (i)** (MT p. 234): for an accessible atom `α` and `a ∈ α`, `μ°_α` is a
(σ-finite) subinvariant measure, and it is invariant iff the chain is recurrent. -/
theorem theorem_10_2_1_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (h : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) :
    IsSubinvariantMeasure P (atomMeasure P h.1.1 a) ∧
      (IsInvariant P (atomMeasure P h.1.1 a) ↔ IsRecurrentChain P ψ) := by
  obtain ⟨hat, hψ, hψα⟩ := h
  have hsub := isSubinvariant_atomMeasure hat ha
  have hfinα : atomMeasure P hat.1 a α ≠ ∞ := by
    rw [atomMeasure_self]; exact ne_top_of_le_ne_top ENNReal.one_ne_top (hitProb_le_one P α a)
  refine ⟨⟨proposition_10_1_2_i hψ.2.1 hsub hat.1 hψα hfinα, hsub⟩, ?_⟩
  rw [IsAccessibleAtom.isRecurrentChain_iff ⟨hat, hψ, hψα⟩ ha]
  refine ⟨fun hinv => ?_, fun hL => isInvariant_atomMeasure hat ha hL⟩
  -- find `B` with `P(a, B) > 0` and `μ°_α(B) < ∞`
  have hνu : 0 < P a (⋃ j, resolventLevel P α j) := by
    rw [iUnion_resolventLevel hψ.2.1 hat.1 hψα]; simp
  obtain ⟨j, hj⟩ := exists_measure_pos_of_iUnion hνu
  have hfin : atomMeasure P hat.1 a (resolventLevel P α j) < ∞ :=
    lt_of_le_of_lt (measure_resolventLevel_le hsub hat.1 j)
      (ENNReal.mul_lt_top (by simp) hfinα.lt_top)
  have e := congrArg (fun m : Measure X => m (resolventLevel P α j)) hinv
  rw [comp_atomMeasure hat ha] at e
  conv_rhs at e => rw [atomMeasure_eq]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at e
  have hSfin : atomTail P hat.1 a (resolventLevel P α j) ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin.ne ?_
    rw [atomMeasure_eq, Measure.add_apply]
    exact le_add_self
  have e' := (ENNReal.add_left_inj hSfin).1 e
  exact (ENNReal.mul_eq_right hj.ne' (prob_le_one.trans_lt ENNReal.one_lt_top).ne).1 e'

/-- **Theorem 10.2.1 (ii)**, minimality (MT p. 234): every subinvariant `μ` with `μ(α) = 1`
satisfies `μ ≥ μ°_α`. -/
theorem theorem_10_2_1_ii {P : Kernel X X} {α : Set X} (hα : IsAtom P α) {a : X} (ha : a ∈ α)
    {μ : Measure X} (h : IsSubinvariant P μ) (h1 : μ α = 1) : atomMeasure P hα.1 a ≤ μ := by
  have := proposition_10_4_6_minimal h hα.1
  rwa [minimalMeasure_atom hα ha, h1, one_smul] at this

/-- **Theorem 10.2.1 (ii)**, uniqueness (MT p. 234): for a recurrent chain with an accessible
atom, `μ°_α` is the unique subinvariant measure with `μ(α) = 1`. -/
theorem theorem_10_2_1_ii_unique {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {α : Set X} (h : IsAccessibleAtom P ψ α) (hrec : IsRecurrentChain P ψ) {a : X} (ha : a ∈ α)
    {μ : Measure X} (hμ : IsSubinvariant P μ) (h1 : μ α = 1) : μ = atomMeasure P h.1.1 a := by
  have hinv := ((theorem_10_2_1_i h ha).2).2 hrec
  obtain ⟨hat, hψ, hψα⟩ := h
  have hK : (1 : ℝ≥0∞) / 2 < 1 := by norm_num
  have hhalf : (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have := isMarkovKernel_resolventHalf P
  refine eq_of_le_of_lintegral_le (theorem_10_2_1_ii hat ha hμ h1)
    (f := fun x => resolventHalf P x α) (Kernel.measurable_coe _ hat.1)
    (fun x => (((proposition_4_2_1 P ψ).2.2.1 hψ.2.1) α hat.1 hψα x).ne')
    (fun x => (prob_le_one.trans_lt ENNReal.one_lt_top).ne) ?_ ?_
  · rw [← measure_kernel_apply _ _ hat.1, ← measure_kernel_apply _ _ hat.1]
    calc (resolventHalf P ∘ₘ μ) α ≤ μ α := (hμ.resolvent hhalf) α
      _ = 1 := h1
      _ = atomMeasure P hat.1 a α := by
          rw [atomMeasure_self]
          exact ((IsAccessibleAtom.isRecurrentChain_iff ⟨hat, hψ, hψα⟩ ha).1 hrec).symm
      _ = (resolventHalf P ∘ₘ atomMeasure P hat.1 a) α := by
          rw [show resolventHalf P ∘ₘ atomMeasure P hat.1 a = atomMeasure P hat.1 a from
            hinv.resolvent hhalf]
  · rw [← measure_kernel_apply _ _ hat.1,
      show resolventHalf P ∘ₘ atomMeasure P hat.1 a = atomMeasure P hat.1 a from
        hinv.resolvent hhalf, atomMeasure_self]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (hitProb_le_one P α a)

/-- Theorem 10.2.1 (ii), up to scaling: for a recurrent chain with an accessible atom, every
subinvariant `μ` with `0 < μ(α) < ∞` is `μ(α) μ°_α`. -/
theorem theorem_10_2_1_ii_smul {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {α : Set X} (h : IsAccessibleAtom P ψ α) (hrec : IsRecurrentChain P ψ) {a : X} (ha : a ∈ α)
    {μ : Measure X} (hμ : IsSubinvariant P μ) (h0 : μ α ≠ 0) (htop : μ α ≠ ∞) :
    μ = μ α • atomMeasure P h.1.1 a := by
  have h1 : ((μ α)⁻¹ • μ) α = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]
  have := theorem_10_2_1_ii_unique h hrec ha (hμ.smul _) h1
  rw [← this, smul_smul, ENNReal.mul_inv_cancel h0 htop, one_smul]

/-! ### Subinvariant measures are finite on petite sets -/

/-- A σ-finite measure gives finite mass to some set of `B⁺(X)`. -/
theorem exists_finite_pos_of_sigmaFinite {μ ψ : Measure X} [SigmaFinite μ] (hψ : ψ ≠ 0) :
    ∃ A, MeasurableSet A ∧ 0 < ψ A ∧ μ A ≠ ∞ := by
  have hu : 0 < ψ (⋃ n, spanningSets μ n) := by
    rw [iUnion_spanningSets]
    exact pos_iff_ne_zero.2 fun h => hψ (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion hu
  exact ⟨_, measurableSet_spanningSets μ n, hn, (measure_spanningSets_lt_top μ n).ne⟩

/-- A subinvariant measure gives finite mass to some set of `B⁺(X)`. -/
theorem IsSubinvariantMeasure.exists_finite_pos {P : Kernel X X} {μ ψ : Measure X}
    (h : IsSubinvariantMeasure P μ) (hψ : ψ ≠ 0) :
    ∃ A, MeasurableSet A ∧ 0 < ψ A ∧ μ A ≠ ∞ := by
  have := h.1
  exact exists_finite_pos_of_sigmaFinite hψ

/-- Proposition 10.1.2 (iii) for a subinvariant measure of a `ψ`-irreducible chain: petite sets
have finite measure. -/
theorem IsSubinvariantMeasure.measure_lt_top_of_petite {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {μ : Measure X}
    (h : IsSubinvariantMeasure P μ) {C : Set X} (hC : IsPetite P C) : μ C < ∞ := by
  obtain ⟨A, hA, hψA, hμA⟩ := h.exists_finite_pos hψ.1
  exact proposition_10_1_2_iii hψ.2.1 h.2 hA hψA hμA hC

/-- A subinvariant measure of a `ψ`-irreducible chain gives finite mass to every atom. -/
theorem IsSubinvariantMeasure.measure_atom_lt_top {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {μ : Measure X}
    (h : IsSubinvariantMeasure P μ) {α : Set X} (hα : IsAtom P α) : μ α < ∞ := by
  by_cases hne : α.Nonempty
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨ν, hν⟩ := hα.2
    have h0 : ν ≠ 0 := by
      rw [← hν a ha]; exact IsProbabilityMeasure.ne_zero _
    exact h.measure_lt_top_of_petite hψ
      ⟨_, _, proposition_5_5_3 (isSmallSet_of_atom P hα.1 hν h0)⟩
  · rw [not_nonempty_iff_eq_empty.1 hne]; simp

/-- **Uniqueness through an atom**: for a recurrent chain with an accessible atom, every
subinvariant measure (σ-finite) is the multiple `μ(α) μ°_α` of `μ°_α`. -/
theorem IsSubinvariantMeasure.eq_smul_atomMeasure {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} {α : Set X} (h : IsAccessibleAtom P ψ α) (hrec : IsRecurrentChain P ψ)
    {a : X} (ha : a ∈ α) {μ : Measure X} (hμ : IsSubinvariantMeasure P μ) :
    μ = μ α • atomMeasure P h.1.1 a := by
  by_cases h0 : μ α = 0
  · by_cases hμ0 : μ = 0
    · rw [hμ0]; simp
    · exact absurd h0 (hμ.2.pos_of_pos h.2.1.2.1 hμ0 h.1.1 h.2.2).ne'
  · exact theorem_10_2_1_ii_smul h hrec ha hμ.2 h0 (hμ.measure_atom_lt_top h.2.1 h.1).ne

/-- **Theorem 10.2.1 (iii)** (MT p. 234), (10.12): `μ°_α(X) = E_a[τ_α]`; so `μ°_α` is finite
iff `E_a[τ_α] < ∞`, and then `μ°_α` is invariant. -/
theorem theorem_10_2_1_iii {P : Kernel X X} [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {a : X} (ha : a ∈ α) :
    atomMeasure P hα.1 a univ = meanReturnTime P α a ∧
      (meanReturnTime P α a ≠ ∞ → IsInvariant P (atomMeasure P hα.1 a)) := by
  refine ⟨atomMeasure_univ P hα.1 a, fun hfin => ?_⟩
  refine proposition_10_1_2_iv (isSubinvariant_atomMeasure hα ha) ?_
  rwa [atomMeasure_univ]

/-! ### Kac's theorem -/

/-- `E_a[τ_α] ≥ 1`. -/
theorem one_le_atomMeasure_univ (P : Kernel X X) [IsMarkovKernel P] {α : Set X}
    (hα : MeasurableSet α) (a : X) : 1 ≤ atomMeasure P hα a univ := by
  rw [atomMeasure_eq, Measure.add_apply, measure_univ]
  exact le_self_add

/-- **Theorem 10.2.2** (Kac's theorem, MT p. 236): for an accessible atom `α` and `a ∈ α`, the
chain is positive iff `E_a[τ_α] < ∞`; and then every invariant probability measure `π`
satisfies `π(α) = E_a[τ_α]⁻¹` (10.14). -/
theorem theorem_10_2_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (h : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) :
    (IsPositive P ψ ↔ meanReturnTime P α a ≠ ∞) ∧
      ∀ π : Measure X, IsProbabilityMeasure π → IsInvariant P π →
        π α = (meanReturnTime P α a)⁻¹ := by
  have key : ∀ π : Measure X, IsProbabilityMeasure π → IsInvariant P π →
      meanReturnTime P α a ≠ ∞ ∧ π α = (meanReturnTime P α a)⁻¹ := by
    intro π hπ hinv
    have hrec := proposition_10_1_1 ⟨h.2.1, π, hπ, hinv⟩
    have hsub : IsSubinvariantMeasure P π := ⟨inferInstance, hinv.isSubinvariant⟩
    have he := hsub.eq_smul_atomMeasure h hrec ha
    have hu := congrArg (fun m : Measure X => m univ) he
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, atomMeasure_univ] at hu
    have hπα : π α ≠ 0 := (hinv.isSubinvariant.pos_of_pos h.2.1.2.1
      (IsProbabilityMeasure.ne_zero π) h.1.1 h.2.2).ne'
    have hfin : meanReturnTime P α a ≠ ∞ := by
      intro ht; rw [ht, ENNReal.mul_top hπα] at hu; exact ENNReal.one_ne_top hu
    exact ⟨hfin, (ENNReal.eq_inv_of_mul_eq_one_left hu.symm)⟩
  refine ⟨⟨fun ⟨_, π, hπ, hinv⟩ => (key π hπ hinv).1, fun hfin => ?_⟩,
    fun π hπ hinv => (key π hπ hinv).2⟩
  have hinv := (theorem_10_2_1_iii h.1 ha).2 hfin
  set M := atomMeasure P h.1.1 a
  have hM1 : 1 ≤ M univ := one_le_atomMeasure_univ P h.1.1 a
  have hMfin : M univ ≠ ∞ := by rw [atomMeasure_univ]; exact hfin
  have hM0 : M univ ≠ 0 := (lt_of_lt_of_le one_pos hM1).ne'
  refine ⟨h.2.1, (M univ)⁻¹ • M, ⟨?_⟩, hinv.smul _⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hM0 hMfin]

/-- **Proposition 10.2.3** (MT p. 236): on a countable space, for a positive chain whose maximal
irreducibility measure charges every point, every invariant probability measure is given by
`π(x) = E_x[τ_x]⁻¹` for every `x`. -/
theorem proposition_10_2_3 [Countable X] [MeasurableSingletonClass X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hpos : IsPositive P ψ) (hψx : ∀ x, 0 < ψ {x})
    (π : Measure X) [IsProbabilityMeasure π] (hinv : IsInvariant P π) (x : X) :
    π {x} = (meanReturnTime P {x} x)⁻¹ :=
  (theorem_10_2_2 ⟨isAtom_singleton P x, hpos.1, hψx x⟩ (mem_singleton x)).2 π inferInstance hinv

/-- Proposition 10.2.3, uniqueness: under the same hypotheses there is exactly one invariant
probability measure. -/
theorem proposition_10_2_3_unique [Countable X] [MeasurableSingletonClass X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hpos : IsPositive P ψ) (hψx : ∀ x, 0 < ψ {x})
    (π π' : Measure X) [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hinv : IsInvariant P π) (hinv' : IsInvariant P π') : π = π' := by
  refine Measure.ext_of_singleton fun x => ?_
  rw [proposition_10_2_3 hpos hψx π hinv x, proposition_10_2_3 hpos hψx π' hinv' x]

end MeynTweedie.FErgodicity

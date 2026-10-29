/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.GeometricModels

/-!
# Theorem 15.4.2 without an atom

Meyn and Tweedie, Theorem 15.4.2, pp. 386–387, in the general case: the chain need not have an
atom. `GeometricConverse` treats chains with an accessible atom.

**The gap in the book's reduction.** The book applies the atom argument to the split chain of a
skeleton at its atom `α̌`. That needs `Σ rⁿ ‖P̌ⁿ(α̌, ·) − π̌‖_f < ∞`, and `P̌(α̌, ·)` is built from
the minorizing measure `ν`. So it needs a `ν`-average of `x ↦ Σ rⁿ ‖Pⁿ(x, ·) − π‖_f`, which is
finite at each point but need not be `ν`-integrable (nor measurable).

**The route taken here.**
* `atom_geomTaboo_ne_top`: the atom argument uses only two test functions. Hypotheses on
  `|Pᵏ(a, α) − π(α)|` (the test function `1_α`) and on `(π(f) − Pⁿ⁺¹(a, f))⁺` (the test function
  `f`) replace the `f`-norm (`atom_tail_le_tsub` is the corresponding tail bound).
* For a small set `C` these two quantities give measurable functions
  `D(x) = Σⱼ rʲ |Pʲ(x, C) − π(C)|` and `E(x) = Σⱼ rʲ (π(f) − Pʲ(x, f))⁺`. Both are bounded by
  multiples of `Σ rʲ ‖Pʲ(x, ·) − π‖_f`, so they are finite on `C`.
* The minorization `Pᵐ(x, ·) ≥ δν` on `C` is kept on `C`, but `ν` is replaced by its restriction
  to `C₁ = C ∩ {D + E ≤ ℓ}`, where `ν(C₁) > 0`. Then `∫ D dν₁` and `∫ E dν₁` are at most `ℓ`, and
  the split chain's atom satisfies the two hypotheses for `f^{(m)}` (by Jensen's inequality for
  the positive parts, `tsub_lintegral_le` and `lintegral_tsub_le`).
* `IsAtom.driftV4_geomG`: once `U_{α̌}^{(s)}(α̌, f̌) < ∞`, `G_{α̌}^{(s)}(·, f̌)` satisfies (V4)
  at the atom with no bound on `f̌` over `α̌`. `Minorization.driftV4_of_split_drift` carries (V4)
  to the skeleton through `V(x) = ∫ x*(dz) G(z) ≥ f^{(m)}(x)`.
* Theorem 15.3.3 makes the skeleton `V`-geometrically regular, hence `f^{(m)}`-geometrically
  regular. Theorem 15.3.7 (`IsFGeomRegularOn.of_skeleton`) gives an `f`-Kendall petite set for
  the chain, and Proposition 15.3.2 gives the full absorbing set.

**Results.**
* **Theorem 15.4.2** (`theorem_15_4_2`, p. 386): for a `ψ`-irreducible aperiodic chain on a
  countably generated space with invariant probability `π`, `f ≥ 1`, `π(f) < ∞`, and
  `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f < ∞` for `x` in a full measurable set, the chain is `f`-geometrically
  regular on a full absorbing set. `theorem_15_4_2_univ` is the book's form, with the sums finite
  everywhere (15.7).

So the statement of Theorem 15.4.2 is true; only the book's proof of the general case is
incomplete.

**Hypotheses.** Aperiodicity is assumed: the book uses it to find a strongly aperiodic skeleton,
and it follows from the convergence, but that is not derived here. Positivity (an invariant
probability) replaces positive Harris recurrence. The sums are needed only on a full set.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### Elementary bounds -/

/-- `π(f) − μ(f) ≤ ‖μ − π‖_f` (in `[0, ∞]`, truncated subtraction) when `π(f) < ∞`. -/
theorem tsub_lintegral_le_fNorm {f : X → ℝ≥0∞} (hf : Measurable f) {μ π : Measure X}
    (hπf : ∫⁻ y, f y ∂π ≠ ∞) : ∫⁻ y, f y ∂π - ∫⁻ y, f y ∂μ ≤ fNorm f μ π := by
  by_cases hμ : ∫⁻ y, f y ∂μ = ∞
  · rw [hμ, tsub_eq_zero_of_le le_top]
    exact bot_le
  · exact tsub_le_iff_left.2 (lintegral_le_add_fNorm hf hμ hπf)

/-- `a − b ≤ |a − b|` for finite `a`, `b`. -/
theorem tsub_le_ofReal_abs {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    a - b ≤ ENNReal.ofReal |a.toReal - b.toReal| := by
  calc a - b = ENNReal.ofReal a.toReal - ENNReal.ofReal b.toReal := by
        rw [ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]
    _ = ENNReal.ofReal (a.toReal - b.toReal) := (ENNReal.ofReal_sub _ ENNReal.toReal_nonneg).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (le_abs_self _)

/-- `|a − b| ≤ (a − b) + (b − a)` for finite `a`, `b`. -/
theorem ofReal_abs_le_tsub_add_tsub {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    ENNReal.ofReal |a.toReal - b.toReal| ≤ (a - b) + (b - a) := by
  have e1 : ENNReal.ofReal (a.toReal - b.toReal) = a - b := by
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha,
      ENNReal.ofReal_toReal hb]
  have e2 : ENNReal.ofReal (b.toReal - a.toReal) = b - a := by
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha,
      ENNReal.ofReal_toReal hb]
  rw [abs_eq_max_neg, neg_sub, ENNReal.ofReal_max, e1, e2]
  exact max_le le_self_add le_add_self

/-- **Jensen for the positive part**: `(c − ∫ g dν)⁺ ≤ ∫ (c − g)⁺ dν` for a probability `ν`. -/
theorem tsub_lintegral_le {ν : Measure X} [IsProbabilityMeasure ν] (c : ℝ≥0∞) {g : X → ℝ≥0∞}
    (hg : Measurable g) : c - ∫⁻ x, g x ∂ν ≤ ∫⁻ x, (c - g x) ∂ν := by
  refine tsub_le_iff_left.2 ?_
  calc c = ∫⁻ _, c ∂ν := by rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ x, (g x + (c - g x)) ∂ν := lintegral_mono fun x => le_add_tsub
    _ = _ := lintegral_add_left hg _

/-- **Jensen for the other positive part**: `(∫ g dν − c)⁺ ≤ ∫ (g − c)⁺ dν` for a probability
`ν`. -/
theorem lintegral_tsub_le {ν : Measure X} [IsProbabilityMeasure ν] (c : ℝ≥0∞) (g : X → ℝ≥0∞) :
    ∫⁻ x, g x ∂ν - c ≤ ∫⁻ x, (g x - c) ∂ν := by
  refine tsub_le_iff_left.2 ?_
  calc ∫⁻ x, g x ∂ν ≤ ∫⁻ x, (c + (g x - c)) ∂ν := lintegral_mono fun x => le_add_tsub
    _ = c + ∫⁻ x, (g x - c) ∂ν := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- `(Σ aᵢ − Σ bᵢ)⁺ ≤ Σ (aᵢ − bᵢ)⁺`. -/
theorem sum_tsub_le_sum_tsub (s : Finset ℕ) (a b : ℕ → ℝ≥0∞) :
    ∑ i ∈ s, a i - ∑ i ∈ s, b i ≤ ∑ i ∈ s, (a i - b i) := by
  refine tsub_le_iff_left.2 ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => le_add_tsub

/-- A series in `[0, ∞]` is finite if its first term and its tail are. -/
theorem tsum_ne_top_of_succ {g : ℕ → ℝ≥0∞} (h0 : g 0 ≠ ∞) (h : ∑' n, g (n + 1) ≠ ∞) :
    ∑' n, g n ≠ ∞ := by
  rw [← Summable.sum_add_tsum_nat_add' (f := g) (k := 1) ENNReal.summable, Finset.sum_range_one]
  exact ENNReal.add_ne_top.2 ⟨h0, h⟩

/-- `∫ Pⁱ f d(Pᵏ(x, ·)) = P^{k+i}(x, f)`. -/
theorem lintegral_lintegral_pow (P : Kernel X X) {f : X → ℝ≥0∞} (hf : Measurable f) (k i : ℕ)
    (x : X) :
    ∫⁻ y, ∫⁻ z, f z ∂(P ^ i : Kernel X X) y ∂(P ^ k : Kernel X X) x =
      ∫⁻ z, f z ∂(P ^ (k + i) : Kernel X X) x := by
  rw [lintegral_comp_kernel _ _ hf, add_comm, pow_add]
  rfl

/-- `Pᵏ f^{(m)}(x) = Σ_{i<m} P^{k+i} f(x)`. -/
theorem lintegral_fSkel_pow (P : Kernel X X) {f : X → ℝ≥0∞} (hf : Measurable f) (m k : ℕ)
    (x : X) :
    ∫⁻ y, fSkel P m f y ∂(P ^ k : Kernel X X) x =
      ∑ i ∈ range m, ∫⁻ z, f z ∂(P ^ (k + i) : Kernel X X) x := by
  unfold fSkel
  rw [lintegral_finsetSum _ fun i _ => hf.lintegral_kernel]
  exact Finset.sum_congr rfl fun i _ => lintegral_lintegral_pow P hf k i x

/-! ### The split chain at its atom -/

/-- `P̌ⁿ⁺¹(α̌, α̌) = δ ∫ ν(dx) Pⁿ(x, C)`, in `[0, ∞]`. -/
theorem Minorization.splitKernel_pow_succ_checkAlpha {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) (c : X) (n : ℕ) :
    (M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) (c, true) M.checkAlpha =
      M.δ * ∫⁻ x, (P ^ n : Kernel X X) x M.C ∂M.ν := by
  rw [M.splitKernel_pow_succ_apply, Minorization.checkAlpha,
    M.split_apply_true _ M.measurableSet_C, inter_self, M.baseK_apply_true,
    Measure.bind_apply M.measurableSet_C (Kernel.aemeasurable _)]

/-- `P̌ⁿ⁺¹(α̌, f̌) = ∫ ν(dx) Pⁿ(x, f)`. -/
theorem Minorization.lintegral_splitKernel_pow_succ {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) {f : X → ℝ≥0∞} (hf : Measurable f) (c : X) (n : ℕ) :
    ∫⁻ z, f z.1 ∂(M.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) (c, true) =
      ∫⁻ x, ∫⁻ y, f y ∂(P ^ n : Kernel X X) x ∂M.ν := by
  rw [M.splitKernel_pow_succ_apply, M.lintegral_split_comp_fst _ hf, M.baseK_apply_true,
    Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]

/-- `∫ f̌ d(x*) = f(x)`. -/
theorem Minorization.lintegral_splitK_fst {P : Kernel X X} (M : Minorization P) {f : X → ℝ≥0∞}
    (hf : Measurable f) (x : X) : ∫⁻ z, f z.1 ∂M.splitK x = f x := by
  rw [M.lintegral_splitK x (f := fun z => f z.1) (hf.comp measurable_fst)]
  dsimp only
  rw [← add_mul, tsub_add_cancel_of_le (M.splitProb_le_one x), one_mul]

/-- **(V4) at an atom from a finite `U^{(s)}`**: if `α` is an atom with `U_α^{(s)}(a, f) < ∞`,
`a ∈ α`, then `G = G_α^{(s)}(·, f)` satisfies `PG ≤ s⁻¹ G + s⁻¹ U_α^{(s)}(a, f) 1_α`. No bound on
`f` over `α` is needed. -/
theorem IsAtom.driftV4_geomG {P : Kernel X X} [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α)
    {a : X} (ha : a ∈ α) {s : ℝ≥0∞} (hs0 : s ≠ 0) (hst : s ≠ ∞) {f : X → ℝ≥0∞}
    (hf : Measurable f) :
    DriftV4 P (geomG P α s f) s⁻¹ (s⁻¹ * geomTaboo P α s f a) α := by
  intro z
  have hPG : ∫⁻ y, geomG P α s f y ∂P z = s⁻¹ * geomTaboo P α s f z := by
    rw [geomTaboo_eq P hα.1 s hf z, ← mul_assoc, ENNReal.inv_mul_cancel hs0 hst, one_mul]
  rw [hPG]
  by_cases hz : z ∈ α
  · rw [indicator_of_mem hz, hα.geomTaboo_const s hf hz ha]
    exact le_add_self
  · rw [indicator_of_notMem hz, add_zero, geomG_eq P hα.1 s hf z,
      indicator_of_mem (show z ∈ αᶜ from hz)]
    exact mul_le_mul' le_rfl le_add_self

/-- **(V4) for the chain from (V4) for the split chain at `α̌`**: if `W ≥ 1` on `X × {0, 1}` is
finite somewhere and `P̌W ≤ ρW + b 1_{α̌}`, `ρ < 1`, then `V(x) = ∫ x*(dz) W(z)` satisfies
`PV ≤ ρV + b 1_C` and is finite somewhere. -/
theorem Minorization.driftV4_of_split_drift {P : Kernel X X} [IsMarkovKernel P]
    (M : Minorization P) {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {W : X × Bool → ℝ≥0∞} (hWm : Measurable W) {z₀ : X × Bool} (hWz₀ : W z₀ ≠ ∞) {ρ b : ℝ≥0∞}
    (hρ : ρ < 1) (hb : b ≠ ∞)
    (hdrift : haveI := M.isMarkovKernel_splitKernel; DriftV4 M.splitKernel W ρ b M.checkAlpha) :
    (∃ x₀, ∫⁻ z, W z ∂M.splitK x₀ ≠ ∞) ∧
      DriftV4 P (fun x => ∫⁻ z, W z ∂M.splitK x) ρ b M.C := by
  have := M.isMarkovKernel_splitKernel
  have := M.isMarkovKernel_splitK
  have hC := M.measurableSet_C
  have hαm := M.measurableSet_checkAlpha
  refine ⟨?_, fun x => ?_⟩
  · have hψs := M.isMaximalIrreducibility_split hψ
    have hfull := (lemma_15_2_2_i hψs.2.1 hWm hρ.le hb hdrift).2 ⟨z₀, hWz₀⟩
    set N := {z | W z ≠ ∞}ᶜ with hN
    have hNm : MeasurableSet N := ((measurableSet_singleton ∞).compl.preimage hWm).compl
    have h0 : ∫⁻ x, M.splitK x N ∂ψ = 0 := by
      rw [← Measure.bind_apply hNm M.splitK.aemeasurable]; exact hfull
    have hae := (lintegral_eq_zero_iff (Kernel.measurable_coe _ hNm)).1 h0
    have : (ae ψ).NeBot := ae_neBot.2 hψ.1
    obtain ⟨x, hx⟩ := hae.exists
    have hx' : (1 - M.splitProb x) * N.indicator 1 (x, false) +
        M.splitProb x * N.indicator 1 (x, true) = 0 := by
      have := M.lintegral_splitK x (f := N.indicator 1) (measurable_one.indicator hNm)
      rw [lintegral_indicator_one hNm] at this
      rw [← this]; exact hx
    obtain ⟨h1, h2⟩ := add_eq_zero.1 hx'
    have hr1 : 1 - M.splitProb x ≠ 0 := (tsub_pos_iff_lt.2 ((M.splitProb_le x).trans_lt
      M.δ_lt_one)).ne'
    have hfalse : W (x, false) ≠ ∞ := by
      have := (mul_eq_zero.1 h1).resolve_left hr1
      by_contra hW
      rw [indicator_of_mem (show (x, false) ∈ N from by simpa [hN] using hW)] at this
      exact one_ne_zero this
    refine ⟨x, ?_⟩
    rw [M.lintegral_splitK x hWm]
    rcases mul_eq_zero.1 h2 with hr | hind
    · rw [hr, zero_mul, add_zero]
      exact ENNReal.mul_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top) hfalse
    · have htrue : W (x, true) ≠ ∞ := by
        by_contra hW
        rw [indicator_of_mem (show (x, true) ∈ N from by simpa [hN] using hW)] at hind
        exact one_ne_zero hind
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)
        hfalse, ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
          (M.splitProb_le_one x)) htrue⟩
  · have hsd : M.split (Measure.dirac x) = M.splitK x := Measure.dirac_bind M.splitK.measurable x
    calc ∫⁻ y, ∫⁻ z, W z ∂M.splitK y ∂P x = ∫⁻ z, W z ∂M.split (P x) :=
          (Measure.lintegral_bind M.splitK.aemeasurable hWm.aemeasurable).symm
      _ = ∫⁻ z, W z ∂(M.splitKernel ∘ₘ M.split (Measure.dirac x)) := by
          rw [M.split_comp_splitKernel, dirac_kernel]
      _ = ∫⁻ z, ∫⁻ w, W w ∂M.splitKernel z ∂M.split (Measure.dirac x) :=
          Measure.lintegral_bind (Kernel.aemeasurable _) hWm.aemeasurable
      _ ≤ ∫⁻ z, (ρ * W z + M.checkAlpha.indicator (fun _ => b) z)
            ∂M.split (Measure.dirac x) := lintegral_mono fun z => hdrift z
      _ = ρ * ∫⁻ z, W z ∂M.split (Measure.dirac x) +
            b * M.split (Measure.dirac x) M.checkAlpha := by
          rw [lintegral_add_left (hWm.const_mul _), lintegral_const_mul _ hWm,
            lintegral_indicator_const hαm]
      _ ≤ ρ * ∫⁻ z, W z ∂M.splitK x + M.C.indicator (fun _ => b) x := by
          rw [hsd]
          refine add_le_add le_rfl ?_
          rw [← hsd, Minorization.checkAlpha, M.split_apply_true _ hC, inter_self,
            Measure.dirac_apply' x hC]
          by_cases hx : x ∈ M.C
          · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, mul_one]
            exact mul_le_of_le_one_right' (M.δ_lt_one.le)
          · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero, mul_zero]

/-! ### The atom argument with two test functions -/

/-- **The tail bound behind (15.44)**, with the positive part of `π(f) − Pⁿ⁺¹(a, f)` in place
of the `f`-norm: `c Σ_{j > n} t_j ≤ (π(f) − Pⁿ⁺¹(a, f))⁺ + Σ_{k ≤ n} |u(k) − c| t_{n−k}`. -/
theorem atom_tail_le_tsub {P : Kernel X X} [IsMarkovKernel P] {α : Set X} (hα : IsAtom P α) {a : X}
    (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π] (hπ : π = π α • atomMeasure P hα.1 a)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hπf : ∫⁻ y, f y ∂π ≠ ∞)
    (n : ℕ) :
    π α * ∑' i, ∫⁻ y, f y ∂tabooKernel P hα.1 (i + n + 1) a ≤
      (∫⁻ y, f y ∂π - ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a) + ∑ k ∈ range (n + 1),
        ENNReal.ofReal |((P ^ k : Kernel X X) a α).toReal - (π α).toReal| *
          ∫⁻ y, f y ∂tabooKernel P hα.1 (n - k) a := by
  set t : ℕ → ℝ≥0∞ := fun j => ∫⁻ y, f y ∂tabooKernel P hα.1 j a with ht
  set c := π α with hc
  have hct : c ≠ ∞ := measure_ne_top π α
  have hU : ∑' j, t j = tabooPotFn P α f a := tsum_lintegral_tabooKernel P hα.1 hf a
  have hUt : tabooPotFn P α f a ≠ ∞ := tabooPotFn_ne_top_of_rep P hα.1 a hπ hf hπf
  have htt : ∀ j, t j ≠ ∞ := fun j => ne_top_of_le_ne_top (hU ▸ hUt) (ENNReal.le_tsum j)
  have hπfeq : ∫⁻ y, f y ∂π = c * ∑' j, t j := by rw [hU]; exact lintegral_eq_atom P hα.1 a hπ hf
  have hPf := hα.lintegral_pow_succ_eq ha f n
  set w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal |((P ^ k : Kernel X X) a α).toReal - c.toReal|
    with hw
  have hu : ∀ k, (P ^ k : Kernel X X) a α ≤ c + w k := fun k => by
    have := isMarkovKernel_pow P k
    have hk : (P ^ k : Kernel X X) a α ≠ ∞ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hk, ← ENNReal.ofReal_toReal hct, hw, ← ENNReal.ofReal_add
      ENNReal.toReal_nonneg (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [le_abs_self (((P ^ k : Kernel X X) a α).toReal - c.toReal)]
  -- `c Σ_{j ≤ n} t_j + c Σ_{j > n} t_j = π(f) ≤ Pⁿ⁺¹(a, f) + e ≤ c Σ_{j ≤ n} t_j + E + e`
  have hsplit : c * ∑ j ∈ range (n + 1), t j + c * ∑' i, t (i + n + 1) = ∫⁻ y, f y ∂π := by
    have h := Summable.sum_add_tsum_nat_add' (f := t) (k := n + 1) ENNReal.summable
    rw [hπfeq, ← mul_add, ← h]
    rfl
  have hreflect : ∑ j ∈ range (n + 1), t j = ∑ k ∈ range (n + 1), t (n - k) :=
    (Finset.sum_range_reflect t (n + 1)).symm
  have hupper : ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a ≤
      c * ∑ j ∈ range (n + 1), t j + ∑ k ∈ range (n + 1), w k * t (n - k) := by
    rw [hPf, hreflect, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => by rw [← add_mul]; exact mul_le_mul' (hu k) le_rfl
  have hlow : ∫⁻ y, f y ∂π ≤ ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a +
      (∫⁻ y, f y ∂π - ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a) := le_add_tsub
  have hfin : c * ∑ j ∈ range (n + 1), t j ≠ ∞ :=
    ENNReal.mul_ne_top hct (ENNReal.sum_ne_top.2 fun j _ => htt j)
  have key : c * ∑ j ∈ range (n + 1), t j + c * ∑' i, t (i + n + 1) ≤
      c * ∑ j ∈ range (n + 1), t j + ((∫⁻ y, f y ∂π - ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a) +
        ∑ k ∈ range (n + 1), w k * t (n - k)) := by
    rw [hsplit]
    calc ∫⁻ y, f y ∂π ≤ ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a +
          (∫⁻ y, f y ∂π - ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a) := hlow
      _ ≤ c * ∑ j ∈ range (n + 1), t j + ∑ k ∈ range (n + 1), w k * t (n - k) +
          (∫⁻ y, f y ∂π - ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a) := add_le_add hupper le_rfl
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_left hfin).1 key

/-- **The atom argument of Theorem 15.4.2 with two test functions** (MT pp. 386–387): for an
accessible atom `α ∋ a`, an invariant probability `π` with `π(f) < ∞`, and `r > 1`, if
`Σₖ rᵏ |Pᵏ(a, α) − π(α)| < ∞` and `Σₙ rⁿ (π(f) − Pⁿ⁺¹(a, f))⁺ < ∞`, then
`U_α^{(s)}(a, f) < ∞` for some `s > 1`. Only the test functions `1_α` and `f` enter. -/
theorem atom_geomTaboo_ne_top {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (h : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hinv : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f) (hπf : ∫⁻ y, f y ∂π ≠ ∞)
    {r : ℝ≥0∞} (hr : 1 < r)
    (hDr : ∑' k, r ^ k * ENNReal.ofReal |((P ^ k : Kernel X X) a α).toReal - (π α).toReal| ≠ ∞)
    (hEr : ∑' n, r ^ n * (∫⁻ y, f y ∂π - ∫⁻ y, f y ∂(P ^ (n + 1) : Kernel X X) a) ≠ ∞) :
    ∃ s : ℝ≥0∞, 1 < s ∧ s ≠ ∞ ∧ geomTaboo P α s f a ≠ ∞ := by
  have hα := h.1
  obtain ⟨hπ, -⟩ := atom_rep_of_invariant h ha hinv
  have hc0 : π α ≠ 0 := measure_atom_ne_zero_of_rep P hα.1 a hπ
  have hct : π α ≠ ∞ := measure_ne_top π α
  have hU : ∑' j, ∫⁻ y, f y ∂tabooKernel P hα.1 j a ≠ ∞ := by
    rw [tsum_lintegral_tabooKernel P hα.1 hf a]
    exact tabooPotFn_ne_top_of_rep P hα.1 a hπ hf hπf
  set t : ℕ → ℝ≥0∞ := fun j => ∫⁻ y, f y ∂tabooKernel P hα.1 j a with ht
  set e : ℕ → ℝ≥0∞ := fun n => ∫⁻ y, f y ∂π - ∫⁻ y, f y ∂(P ^ n : Kernel X X) a with he
  set w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal |((P ^ k : Kernel X X) a α).toReal - (π α).toReal|
    with hw
  set R := ∑' k, r ^ k * w k + ∑' n, r ^ n * e (n + 1) with hRdef
  have hR : R ≠ ∞ := ENNReal.add_ne_top.2 ⟨hDr, hEr⟩
  set c := π α with hc
  have htt : ∀ j, t j ≠ ∞ := fun j => ne_top_of_le_ne_top hU (ENNReal.le_tsum j)
  -- the choice of `s`: `1 < s ≤ r` and `(s − 1) R ≤ c / 2`
  have hR1 : R + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hR, ENNReal.one_ne_top⟩
  have hR10 : R + 1 ≠ 0 := by simp
  have hc2 : c / 2 ≠ 0 := (ENNReal.div_pos hc0 ENNReal.ofNat_ne_top).ne'
  have hc2t : c / 2 ≠ ∞ := ENNReal.div_ne_top hct two_ne_zero
  set ε := c / 2 / (R + 1) with hε
  have hε0 : 0 < ε := ENNReal.div_pos hc2 hR1
  have hεt : ε ≠ ∞ := ENNReal.div_ne_top hc2t hR10
  have hεR : ε * R ≤ c / 2 := calc ε * R ≤ ε * (R + 1) := mul_le_mul' le_rfl le_self_add
      _ = c / 2 := ENNReal.div_mul_cancel hR10 hR1
  set s := min r (1 + ε) with hs
  have hs1 : 1 < s := lt_min hr (ENNReal.lt_add_right ENNReal.one_ne_top hε0.ne')
  have hsr : s ≤ r := min_le_left _ _
  have hst : s ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hεt⟩) (min_le_right _ _)
  have hs1ε : s - 1 ≤ ε := tsub_le_iff_left.2 (min_le_right _ _)
  have hsn : ∀ n, s ^ n ≤ r ^ n := fun n => pow_le_pow_left₀ bot_le hsr n
  have hD : ∑' k, s ^ k * w k ≤ R :=
    (ENNReal.tsum_le_tsum fun k => mul_le_mul' (hsn k) le_rfl).trans le_self_add
  have hE : ∑' n, s ^ n * e (n + 1) ≤ R :=
    (ENNReal.tsum_le_tsum fun n => mul_le_mul' (hsn n) le_rfl).trans le_add_self
  -- the truncated sums are bounded uniformly
  have hY : ∀ N, ∑ j ∈ range N, s ^ j * t j ≤ (c * ∑' j, t j + (s - 1) * R) / (c / 2) := by
    intro N
    set g : ℕ → ℝ≥0∞ := fun j => if j < N then t j else 0 with hg
    have hgt : ∀ j, g j ≤ t j := fun j => by
      simp only [hg]; split_ifs
      · exact le_rfl
      · exact bot_le
    have hYg : ∑' j, s ^ j * g j = ∑ j ∈ range N, s ^ j * t j := by
      rw [tsum_eq_sum (s := range N) fun j hj => by
        simp only [hg]; split_ifs with h
        · exact absurd (Finset.mem_range.2 h) hj
        · exact mul_zero _]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hg]; split_ifs with h
      · rfl
      · exact absurd (Finset.mem_range.1 hj) h
    have hYt : ∑ j ∈ range N, s ^ j * t j ≠ ∞ := ENNReal.sum_ne_top.2 fun j _ =>
      ENNReal.mul_ne_top (ENNReal.pow_ne_top hst) (htt j)
    have htail : ∀ n, c * ∑' i, g (i + n + 1) ≤
        e (n + 1) + ∑ k ∈ range (n + 1), w k * g (n - k) := by
      intro n
      by_cases hn : n < N
      · have hgk : ∀ k ∈ range (n + 1), w k * g (n - k) = w k * t (n - k) := fun k _ => by
          simp only [hg]; split_ifs with h
          · rfl
          · exact absurd (lt_of_le_of_lt (Nat.sub_le n k) hn) h
        rw [Finset.sum_congr rfl hgk]
        calc c * ∑' i, g (i + n + 1) ≤ c * ∑' i, t (i + n + 1) :=
              mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun i => hgt _)
          _ ≤ _ := atom_tail_le_tsub hα ha hπ hf hπf n
      · have h0 : ∀ i, g (i + n + 1) = 0 := fun i => by
          simp only [hg]; split_ifs with h
          · exact absurd h (by omega)
          · rfl
        simp only [h0, tsum_zero, mul_zero]
        exact bot_le
    have hmain : c * ∑' j, s ^ j * g j ≤
        c * ∑' j, t j + (s - 1) * R + c / 2 * ∑' j, s ^ j * g j := by
      calc c * ∑' j, s ^ j * g j
          = c * ∑' j, g j + (s - 1) * ∑' n, s ^ n * (c * ∑' i, g (i + n + 1)) := by
            rw [tsum_pow_mul_eq_add hs1.le g, mul_add]
            congr 1
            simp_rw [mul_left_comm (s ^ _) c, ENNReal.tsum_mul_left]
            ring
        _ ≤ c * ∑' j, t j + (s - 1) * ∑' n, s ^ n *
            (e (n + 1) + ∑ k ∈ range (n + 1), w k * g (n - k)) :=
            add_le_add (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum hgt))
              (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl (htail n)))
        _ = c * ∑' j, t j + (s - 1) * (∑' n, s ^ n * e (n + 1) +
            (∑' k, s ^ k * w k) * ∑' j, s ^ j * g j) := by
            congr 2
            rw [← tsum_sum_range_mul, ← ENNReal.tsum_add]
            refine tsum_congr fun n => ?_
            rw [mul_add, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun k hk => ?_
            have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
            calc s ^ n * (w k * g (n - k)) = s ^ (k + (n - k)) * (w k * g (n - k)) := by
                  rw [Nat.add_sub_cancel' hkn]
              _ = _ := by rw [pow_add]; ring
        _ ≤ c * ∑' j, t j + (s - 1) * R + c / 2 * ∑' j, s ^ j * g j := by
            rw [mul_add, ← mul_assoc, ← add_assoc]
            refine add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hE)) (mul_le_mul' ?_ le_rfl)
            exact (mul_le_mul' hs1ε hD).trans hεR
    rw [hYg] at hmain
    have hfin : c / 2 * ∑ j ∈ range N, s ^ j * t j ≠ ∞ := ENNReal.mul_ne_top hc2t hYt
    have h2 : c / 2 * ∑ j ∈ range N, s ^ j * t j + c / 2 * ∑ j ∈ range N, s ^ j * t j ≤
        c * ∑' j, t j + (s - 1) * R + c / 2 * ∑ j ∈ range N, s ^ j * t j := by
      rw [← add_mul, ENNReal.add_halves]; exact hmain
    have h3 := (ENNReal.add_le_add_iff_right hfin).1 h2
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc2) (Or.inl hc2t), mul_comm]
    exact h3
  have hK : (c * ∑' j, t j + (s - 1) * R) / (c / 2) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hct hU,
      ENNReal.mul_ne_top (ENNReal.sub_ne_top hst) hR⟩) hc2
  have hsum : ∑' j, s ^ j * t j ≠ ∞ := by
    rw [ENNReal.tsum_eq_iSup_nat]
    exact ne_top_of_le_ne_top hK (iSup_le hY)
  have hUa : geomTaboo P α s f a ≠ ∞ := by
    rw [← tsum_pow_lintegral_tabooKernel P hα.1 s hf a]
    simp_rw [pow_succ', mul_assoc]
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hst hsum
  exact ⟨s, hs1, hst, hUa⟩

/-! ### Theorem 15.4.2 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.4.2** (MT p. 386), for chains without an atom: for a `ψ`-irreducible aperiodic
chain with invariant probability `π`, `f ≥ 1` and `π(f) < ∞`, if
`Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f < ∞` for some `r > 1` and every `x` of a full measurable set `S₀`, then
there is a full absorbing set `S` on which the chain is `f`-geometrically regular. -/
theorem theorem_15_4_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ y, f y ∂π ≠ ∞) {r : ℝ≥0∞} (hr : 1 < r) {S₀ : Set X}
    (hS₀ : MeasurableSet S₀) (hS₀f : IsFull ψ S₀)
    (hge : ∀ x ∈ S₀, ∑' n, r ^ n * fNorm f ((P ^ n : Kernel X X) x) π ≠ ∞) :
    ∃ S : Set X, MeasurableSet S ∧ IsFull ψ S ∧ IsAbsorbing P S ∧ IsFGeomRegularOn P f S := by
  -- a finite rate `r₁ = min r 2`
  set r₁ := min r 2 with hr₁
  have hr₁1 : 1 < r₁ := lt_min hr (by norm_num)
  have hr₁t : r₁ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top (min_le_right _ _)
  have hge₁ : ∀ x ∈ S₀, ∑' n, r₁ ^ n * fNorm f ((P ^ n : Kernel X X) x) π ≠ ∞ := fun x hx =>
    ne_top_of_le_ne_top (hge x hx) (ENNReal.tsum_le_tsum fun n =>
      mul_le_mul' (pow_le_pow_left₀ bot_le (min_le_left _ _) n) le_rfl)
  -- a petite set inside `S₀` and a concentrated minorization of a skeleton `Q = Pᵐ`
  obtain ⟨C₀, hC₀, hψC₀⟩ := exists_petite_pos hψ
  have hC₀m : MeasurableSet C₀ := by obtain ⟨_, _, h⟩ := hC₀; exact h.1
  have hCpet : IsPetite P (C₀ ∩ S₀) := hC₀.subset (hC₀m.inter hS₀) inter_subset_left
  have hψC : 0 < ψ (C₀ ∩ S₀) := by rw [measure_inter_of_compl_null hS₀ hS₀f]; exact hψC₀
  obtain ⟨m, hm, M, hMC, hconc⟩ := exists_concentrated_minorization hψ hap hCpet hψC
  have := isMarkovKernel_pow P m
  have := M.isProbabilityMeasure_ν
  have hCS : M.C ⊆ S₀ := hMC ▸ inter_subset_right
  have hψMC : 0 < ψ M.C := hMC ▸ hψC
  have hνC : M.ν M.C = 1 := by
    rw [← prob_compl_eq_zero_iff M.measurableSet_C]; exact hconc
  have hCm := M.measurableSet_C
  -- the two measurable functions behind the atom argument
  set p := π M.C with hp
  have hpt : p ≠ ∞ := measure_ne_top π _
  set d : ℕ → X → ℝ≥0∞ := fun j x => ((P ^ j : Kernel X X) x M.C - p) +
    (p - (P ^ j : Kernel X X) x M.C) with hd
  set e : ℕ → X → ℝ≥0∞ := fun j x => ∫⁻ y, f y ∂π - ∫⁻ y, f y ∂(P ^ j : Kernel X X) x with he
  have hdm : ∀ j, Measurable (d j) := fun j =>
    ((Kernel.measurable_coe _ hCm).sub measurable_const).add
      (measurable_const.sub (Kernel.measurable_coe _ hCm))
  have hem : ∀ j, Measurable (e j) := fun j => measurable_const.sub hf.lintegral_kernel
  set Dfun : X → ℝ≥0∞ := fun x => ∑' j, r₁ ^ j * d j x with hDfun
  set Efun : X → ℝ≥0∞ := fun x => ∑' j, r₁ ^ j * e j x with hEfun
  have hDm : Measurable Dfun := Measurable.tsum fun j => measurable_const.mul (hdm j)
  have hEm : Measurable Efun := Measurable.tsum fun j => measurable_const.mul (hem j)
  set W : X → ℝ≥0∞ := fun x => Dfun x + Efun x with hW
  have hWm : Measurable W := hDm.add hEm
  have hWfin : ∀ x ∈ M.C, W x ≠ ∞ := fun x hx => by
    set T := ∑' n, r₁ ^ n * fNorm f ((P ^ n : Kernel X X) x) π with hT
    have hTt : T ≠ ∞ := hge₁ x (hCS hx)
    have hdj : ∀ j, d j x ≤ 2 * fNorm f ((P ^ j : Kernel X X) x) π := fun j => by
      have := isMarkovKernel_pow P j
      have hpj : (P ^ j : Kernel X X) x M.C ≠ ∞ := measure_ne_top _ _
      have h1 := ofReal_abs_measureReal_sub_le_fNorm hf1 (μ := (P ^ j : Kernel X X) x) (ν := π) hCm
      rw [measureReal_def, measureReal_def] at h1
      rw [two_mul]
      refine add_le_add ((tsub_le_ofReal_abs hpj hpt).trans h1) ?_
      refine (tsub_le_ofReal_abs hpt hpj).trans ?_
      rw [abs_sub_comm]
      exact h1
    have hej : ∀ j, e j x ≤ fNorm f ((P ^ j : Kernel X X) x) π := fun j =>
      tsub_lintegral_le_fNorm hf hπf
    have hDx : Dfun x ≤ 2 * T := by
      calc Dfun x ≤ ∑' j, 2 * (r₁ ^ j * fNorm f ((P ^ j : Kernel X X) x) π) :=
            ENNReal.tsum_le_tsum fun j => by
              rw [mul_left_comm]; exact mul_le_mul' le_rfl (hdj j)
        _ = 2 * T := ENNReal.tsum_mul_left
    have hEx : Efun x ≤ T := ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (hej j)
    exact ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hTt) hDx,
      ne_top_of_le_ne_top hTt hEx⟩
  -- a part `C₁` of `C` of positive `ν`-measure on which `W ≤ ℓ`
  obtain ⟨ℓ, hℓ⟩ := (eventually_measure_inter_sublevel_pos (μ := M.ν) (V := W) (C := M.C) (by
    rw [(inter_eq_left.2 fun x hx => hWfin x hx : M.C ∩ {x | W x ≠ ∞} = M.C), hνC]
    exact one_pos)).exists
  set C₁ := M.C ∩ {x | W x ≤ ℓ} with hC₁
  have hC₁m : MeasurableSet C₁ := hCm.inter (measurableSet_le hWm measurable_const)
  -- the minorization of `Q` on `C` by `ν` restricted to `C₁`
  set ν'' := (M.δ • M.ν).restrict C₁ with hν''
  have hle : ∀ x ∈ M.C, ν'' ≤ (P ^ m : Kernel X X) x := fun x hx =>
    Measure.restrict_le_self.trans (M.le x hx)
  have hν''C : ν'' M.C = M.δ * M.ν C₁ := by
    rw [hν'', Measure.restrict_apply hCm,
      (inter_eq_right.2 inter_subset_left : M.C ∩ C₁ = C₁), Measure.smul_apply, smul_eq_mul]
  have hpos : 0 < ν'' M.C := by rw [hν''C]; exact ENNReal.mul_pos M.δ_pos.ne' hℓ.ne'
  have hfin : ν'' M.C ≠ ∞ := by rw [hν''C]; exact ENNReal.mul_ne_top M.δ_ne_top (measure_ne_top _ _)
  set M' := Minorization.ofLe hCm hle hpos hfin with hM'
  have hM'C : M'.C = M.C := rfl
  have := M'.isProbabilityMeasure_ν
  have hν'C₁ : M'.ν C₁ᶜ = 0 := by
    change ((ν'' M.C)⁻¹ • ν''.restrict M.C) C₁ᶜ = 0
    rw [Measure.smul_apply, Measure.restrict_apply hC₁m.compl, hν'',
      Measure.restrict_apply (hC₁m.compl.inter hCm),
      show C₁ᶜ ∩ M.C ∩ C₁ = ∅ from Set.ext fun x => by
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false]; tauto,
      measure_empty, smul_eq_mul, mul_zero]
  have hWν : ∀ᵐ x ∂M'.ν, Dfun x ≤ ℓ ∧ Efun x ≤ ℓ := (ae_iff.2 hν'C₁).mono fun x hx =>
    ⟨le_self_add.trans hx.2, le_add_self.trans hx.2⟩
  -- the skeleton and its split chain
  have hψQ : IsMaximalIrreducibility (P ^ m : Kernel X X) ψ :=
    ((proposition_5_4_5_iii P hψ hap).1 m hm).1
  have hposQ : IsPositive (P ^ m : Kernel X X) ψ := ⟨hψQ, π, inferInstance, hπ.pow m⟩
  have := M'.isMarkovKernel_splitKernel
  obtain ⟨-, hatom, hπs, hinv⟩ := M'.split_positive hposQ hψMC (hπ.pow m)
  -- a point `c ∈ C` with `f^{(m)}(c) < ∞`
  have hFm : Measurable (fSkel P m f) := measurable_fSkel P m hf
  have hπF : ∫⁻ x, fSkel P m f x ∂π = m * ∫⁻ y, f y ∂π := lintegral_fSkel P hπ m hf
  have hπFt : ∫⁻ x, fSkel P m f x ∂π ≠ ∞ := by
    rw [hπF]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hπf
  have hpos' : IsPositive P ψ := ⟨hψ, π, inferInstance, hπ⟩
  have hequiv := theorem_10_4_9_equiv (proposition_10_1_1 hpos') ⟨inferInstance, hπ⟩
    (IsProbabilityMeasure.ne_zero π)
  have hFs : MeasurableSet {x | fSkel P m f x ≠ ∞} :=
    (measurableSet_singleton ∞).compl.preimage hFm
  have hFae : π {x | fSkel P m f x ≠ ∞}ᶜ = 0 := by
    have := ae_lt_top hFm hπFt
    rw [ae_iff] at this
    refine le_antisymm (le_of_le_of_eq (measure_mono fun x hx => ?_) this) bot_le
    simp only [mem_compl_iff, mem_ofPred_eq, not_not] at hx
    simp [hx]
  have hψF : 0 < ψ (M.C ∩ {x | fSkel P m f x ≠ ∞}) := by
    rw [measure_inter_of_compl_null hFs (hequiv.2 hFae)]
    exact hψMC
  obtain ⟨c, hcC, hcF⟩ := nonempty_of_measure_ne_zero hψF.ne'
  have ha : (c, true) ∈ M'.checkAlpha := ⟨hcC, rfl⟩
  have hFtm : Measurable fun z : X × Bool => fSkel P m f z.1 := hFm.comp measurable_fst
  have hπsF : ∫⁻ z, fSkel P m f z.1 ∂M'.split π = m * ∫⁻ y, f y ∂π := by
    rw [M'.lintegral_split_comp_fst π hFm, hπF]
  -- the renewal sequence of `α̌`: `Σₖ rᵏ |ǔ(k) − π̌(α̌)| < ∞`
  have hπα : M'.split π M'.checkAlpha = M'.δ * p := by
    rw [Minorization.checkAlpha, M'.split_apply_true _ M'.measurableSet_C, inter_self]
    rfl
  have hint_d : ∀ n, ENNReal.ofReal |((M'.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool))
      (c, true) M'.checkAlpha).toReal - (M'.split π M'.checkAlpha).toReal| ≤
      M'.δ * ∫⁻ x, d (m * n) x ∂M'.ν := fun n => by
    have := isMarkovKernel_pow (P ^ m : Kernel X X) n
    have hI : ∫⁻ x, ((P ^ m : Kernel X X) ^ n : Kernel X X) x M'.C ∂M'.ν ≠ ∞ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      calc ∫⁻ x, ((P ^ m : Kernel X X) ^ n : Kernel X X) x M'.C ∂M'.ν ≤ ∫⁻ _, 1 ∂M'.ν :=
            lintegral_mono fun x => prob_le_one
        _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
    rw [M'.splitKernel_pow_succ_checkAlpha c n, hπα]
    refine (ofReal_abs_le_tsub_add_tsub (ENNReal.mul_ne_top M'.δ_ne_top hI)
      (ENNReal.mul_ne_top M'.δ_ne_top hpt)).trans ?_
    rw [← ENNReal.mul_sub fun _ _ => M'.δ_ne_top, ← ENNReal.mul_sub fun _ _ => M'.δ_ne_top,
      ← mul_add]
    refine mul_le_mul' le_rfl ?_
    simp only [hd, ← pow_mul]
    exact (add_le_add (lintegral_tsub_le p _)
      (tsub_lintegral_le p (Kernel.measurable_coe _ hCm))).trans (le_of_eq
        (lintegral_add_left ((Kernel.measurable_coe _ hCm).sub measurable_const) _).symm)
  have hdD : ∀ x, ∑' n, r₁ ^ n * d (m * n) x ≤ Dfun x := fun x =>
    (ENNReal.tsum_le_tsum fun n => mul_le_mul' (pow_le_pow_right₀ hr₁1.le
      (Nat.le_mul_of_pos_left n (by omega))) le_rfl).trans
      (ENNReal.tsum_comp_le_tsum_of_injective (mul_right_injective₀ (by omega : m ≠ 0))
        (fun j => r₁ ^ j * d j x))
  have hDsum : Measurable fun x => ∑' n, r₁ ^ n * d (m * n) x :=
    Measurable.tsum fun n => measurable_const.mul (hdm (m * n))
  have hDae : ∀ n, AEMeasurable (fun x => r₁ ^ n * d (m * n) x) M'.ν := fun n =>
    (measurable_const.mul (hdm (m * n))).aemeasurable
  have hDr : ∑' k, r₁ ^ k * ENNReal.ofReal |((M'.splitKernel ^ k : Kernel (X × Bool) (X × Bool))
      (c, true) M'.checkAlpha).toReal - (M'.split π M'.checkAlpha).toReal| ≠ ∞ := by
    refine tsum_ne_top_of_succ (ENNReal.mul_ne_top (ENNReal.pow_ne_top hr₁t)
      ENNReal.ofReal_ne_top) (ne_top_of_le_ne_top (b := r₁ * M'.δ * ℓ) (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hr₁t M'.δ_ne_top) (ENNReal.natCast_ne_top ℓ)) ?_)
    calc _ ≤ ∑' n, r₁ ^ (n + 1) * (M'.δ * ∫⁻ x, d (m * n) x ∂M'.ν) :=
          ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl (hint_d n)
      _ = ∫⁻ x, r₁ * M'.δ * ∑' n, r₁ ^ n * d (m * n) x ∂M'.ν := by
          rw [lintegral_const_mul _ hDsum, lintegral_tsum hDae, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun n => ?_
          rw [lintegral_const_mul _ (hdm _), pow_succ]
          ring
      _ ≤ ∫⁻ _, r₁ * M'.δ * ℓ ∂M'.ν :=
          lintegral_mono_ae (hWν.mono fun x hx => mul_le_mul' le_rfl ((hdD x).trans hx.1))
      _ = r₁ * M'.δ * ℓ := by rw [lintegral_const, measure_univ, mul_one]
  -- the positive part `(π̌(f̌) − P̌ⁿ⁺¹(α̌, f̌))⁺`
  have he_int : ∀ n, ∫⁻ z, fSkel P m f z.1 ∂M'.split π - ∫⁻ z, fSkel P m f z.1
      ∂(M'.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) (c, true) ≤
      ∫⁻ x, ∑ i ∈ range m, e (m * n + i) x ∂M'.ν := fun n => by
    rw [M'.lintegral_splitKernel_pow_succ hFm c n, hπsF]
    refine (tsub_lintegral_le _ hFm.lintegral_kernel).trans (lintegral_mono fun x => ?_)
    rw [← pow_mul, lintegral_fSkel_pow P hf m (m * n) x]
    calc (m : ℝ≥0∞) * ∫⁻ y, f y ∂π - ∑ i ∈ range m, ∫⁻ z, f z ∂(P ^ (m * n + i) : Kernel X X) x
        = ∑ i ∈ range m, ∫⁻ y, f y ∂π -
            ∑ i ∈ range m, ∫⁻ z, f z ∂(P ^ (m * n + i) : Kernel X X) x := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := sum_tsub_le_sum_tsub _ _ _
  have heE : ∀ x, ∑' n, r₁ ^ n * ∑ i ∈ range m, e (m * n + i) x ≤ Efun x := fun x => by
    calc _ ≤ ∑' n, ∑ i ∈ range m, r₁ ^ (m * n + i) * e (m * n + i) x :=
          ENNReal.tsum_le_tsum fun n => by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun i _ => mul_le_mul' (pow_le_pow_right₀ hr₁1.le
              ((Nat.le_mul_of_pos_left n (by omega)).trans (Nat.le_add_right _ _))) le_rfl
      _ = Efun x := (tsum_eq_tsum_sum_block (fun j => r₁ ^ j * e j x) hm).symm
  have hsum_m : ∀ n, Measurable fun x => ∑ i ∈ range m, e (m * n + i) x := fun n =>
    Finset.measurable_sum _ fun i _ => hem _
  have hEae : ∀ n, AEMeasurable (fun x => r₁ ^ n * ∑ i ∈ range m, e (m * n + i) x) M'.ν :=
    fun n => (measurable_const.mul (hsum_m n)).aemeasurable
  have hEr : ∑' n, r₁ ^ n * (∫⁻ z, fSkel P m f z.1 ∂M'.split π - ∫⁻ z, fSkel P m f z.1
      ∂(M'.splitKernel ^ (n + 1) : Kernel (X × Bool) (X × Bool)) (c, true)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ℓ) (ENNReal.natCast_ne_top ℓ) ?_
    calc _ ≤ ∑' n, r₁ ^ n * ∫⁻ x, ∑ i ∈ range m, e (m * n + i) x ∂M'.ν :=
          ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl (he_int n)
      _ = ∫⁻ x, ∑' n, r₁ ^ n * ∑ i ∈ range m, e (m * n + i) x ∂M'.ν := by
          rw [lintegral_tsum hEae]
          exact tsum_congr fun n => (lintegral_const_mul _ (hsum_m n)).symm
      _ ≤ ∫⁻ _, (ℓ : ℝ≥0∞) ∂M'.ν := lintegral_mono_ae (hWν.mono fun x hx => (heE x).trans hx.2)
      _ = ℓ := by rw [lintegral_const, measure_univ, mul_one]
  -- the atom argument: `U_{α̌}^{(s)}((c, 1), f̌) < ∞`
  have := hπs
  obtain ⟨s, hs1, hst, hUa⟩ := atom_geomTaboo_ne_top hatom ha hinv hFtm
    (by rw [hπsF]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hπf) hr₁1 hDr hEr
  have hs0 : s ≠ 0 := (zero_lt_one.trans hs1).ne'
  have hαm := M'.measurableSet_checkAlpha
  have hGm := measurable_geomG M'.splitKernel hαm s hFtm
  have hdrG := hatom.1.driftV4_geomG ha hs0 hst hFtm
  have hGa : geomG M'.splitKernel M'.checkAlpha s (fun z => fSkel P m f z.1) (c, true) ≠ ∞ := by
    rw [geomG_of_mem _ hαm s hFtm ha]; exact hcF
  have hbG : s⁻¹ * geomTaboo M'.splitKernel M'.checkAlpha s (fun z => fSkel P m f z.1) (c, true)
      ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hs0) hUa
  have hρs : s⁻¹ < 1 := ENNReal.inv_lt_one.2 hs1
  -- (V4) for the skeleton with `V(x) = ∫ x*(dz) Ǧ(z) ≥ f^{(m)}(x)`
  obtain ⟨⟨x₀, hx₀⟩, hdriftQ⟩ := M'.driftV4_of_split_drift hψQ hGm hGa hρs hbG hdrG
  have hVm : Measurable fun x => ∫⁻ z, geomG M'.splitKernel M'.checkAlpha s
      (fun z => fSkel P m f z.1) z ∂M'.splitK x := hGm.lintegral_kernel
  have hFV : ∀ x, fSkel P m f x ≤ ∫⁻ z, geomG M'.splitKernel M'.checkAlpha s
      (fun z => fSkel P m f z.1) z ∂M'.splitK x := fun x => by
    rw [← M'.lintegral_splitK_fst hFm x]
    exact lintegral_mono fun z => le_geomG _ hαm s hFtm z
  have hV1 : ∀ x, 1 ≤ ∫⁻ z, geomG M'.splitKernel M'.checkAlpha s
      (fun z => fSkel P m f z.1) z ∂M'.splitK x := fun x =>
    (one_le_fSkel P hm hf hf1 x).trans (hFV x)
  -- the skeleton is `V`-geometrically regular, hence the chain is `f`-geometrically regular
  have hsm : IsSmallSet (P ^ m : Kernel X X) 1 (M'.δ • M'.ν) M'.C := ⟨M'.measurableSet_C, one_pos,
    smul_measure_ne_zero (IsProbabilityMeasure.ne_zero M'.ν) M'.δ_pos.ne', fun x hx =>
      Measure.le_intro fun A _ _ => by
        rw [pow_one, Measure.smul_apply, smul_eq_mul]; exact M'.le_apply hx A⟩
  obtain ⟨hreg, -⟩ := theorem_15_3_3 hψQ hVm hV1 hρs hbG ⟨_, _, proposition_5_5_3 hsm⟩ hdriftQ hx₀
  have hreg' := hreg.of_le_const_mul hVm ENNReal.one_ne_top (g := fSkel P m f) fun x => by
    rw [one_mul]; exact hFV x
  obtain ⟨C', hC', κ, hκ, hκt, hfin', Mb, hMb, hb'⟩ := hreg'.of_skeleton hf hm
  have hC'm : MeasurableSet C' := by obtain ⟨_, _, h⟩ := hC'; exact h.1
  have hne : C'.Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty] at h0
    subst h0
    exact hfin' x₀ hx₀ (top_le_iff.1 ((geomSum_empty_one P hκ.le x₀).symm.le.trans
      (geomSum_mono_f P ∅ κ (fun y => hf1 y) x₀)))
  have hK : IsFKendall P f C' κ := ⟨hC'm, hκ, hκt, Mb, hMb, hb'⟩
  obtain ⟨S, hSm, hSf, hSa, -, hS⟩ := proposition_15_3_2 hψ hf hf1 hC' hne hK
  exact ⟨S, hSm, hSf, hSa, hS⟩


variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 15.4.2** (MT p. 386) for the book's definition of `f`-geometric ergodicity (15.7),
with the sums finite at every `x`. -/
theorem theorem_15_4_2_univ {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ y, f y ∂π ≠ ∞) {r : ℝ≥0∞} (hr : 1 < r)
    (hge : ∀ x, ∑' n, r ^ n * fNorm f ((P ^ n : Kernel X X) x) π ≠ ∞) :
    ∃ S : Set X, MeasurableSet S ∧ IsFull ψ S ∧ IsAbsorbing P S ∧ IsFGeomRegularOn P f S :=
  theorem_15_4_2 hψ hap hπ hf hf1 hπf hr MeasurableSet.univ (by simp [IsFull])
    fun x _ => hge x

end MeynTweedie.Positivity

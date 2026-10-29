/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.DiscreteSpectrum
import Epilogue.MarkovProperty

/-!
# Multiplicative ergodic theory and quasi-stationarity (MT §20.1.5–20.1.6)

Meyn and Tweedie, pp. 518–520.

* `fkKernel` (`P_f(x, dy) = f(x)P(x, dy)`), `lintegral_fkKernel`, `lintegral_fkKernel_pow_succ`.
* `feynmanKac`, `feynmanKac_apply` (**(20.13)**, p. 519): `P_fⁿ(x, A) = E_x[Πₖ<ₙ f(Φₖ) 1{Φₙ ∈ A}]`
  on the path space of Chapter 3 (with `f = e^F` this is `E_x[exp(Sₙ(F))1{Φₙ ∈ A}]`, and
  `A = X` gives `λₙ,ₓ(F)` (20.12)).
* `killedKernel_apply` (**(20.16)**, p. 520, corrected): with `f = 1_M`,
  `P_Mⁿ(x, A) = P_x{Φ₀, …, Φₙ₋₁ ∈ M, Φₙ ∈ A}`.
* `twistedKernel`, `isMarkovKernel_twistedKernel` (p. 519): the twisted kernel of a positive
  eigenfunction `P_f f̌ = λf̌` is a Markov kernel.
* `nonlinGen_log_eigen` (p. 519, corrected): the eigenvector equation is the multiplicative
  Poisson equation `H(F̌) = Λ − F`, i.e. `log Pe^{F̌} = F̌ − F + Λ`.

**Corrections.**
* p. 519 writes the multiplicative Poisson equation as `H(F̌) = F̌ − F + Λ(F)`; with `H` as in
  (20.10) it is `H(F̌) = Λ − F` (the printed right-hand side is `log Pe^{F̌}`).
  `nonlinGen_book_counterexample`: identity kernel on a point, `f = 1`, `f̌ = e`.
* (20.16) states `P_Mⁿ(x, A) = P_x{Φₙ ∈ A and τ_M > n}`. With `τ_M` the return time to `M` of
  p. 525 this is false (`killedKernel_returnTime_counterexample`); the identity holds with the
  event "`Φₖ ∈ M` for `k < n`" (`killedKernel_apply`), i.e. `τ_M` read as the exit time from `M`
  (which also gives `{τ_M > n}` exactly when `A ⊆ M`).

**Not formalised** (results quoted from [17, 218, 219, 140, 118, 166, 276]): the multiplicative
ergodic theorems (20.14) (existence of the Perron–Frobenius eigenfunction, convergence of
`λ⁻ⁿλₙ,ₓ(F)`), the large-deviation limit (20.15), Sobolev-inequality bounds, the existence of
quasi-stationary laws and their continuous-time versions. These need the spectral theory of
positive operators (Perron–Frobenius on `L∞_V`) and the twisted-kernel ergodicity arguments of the
cited papers, which are not developed in the book.
-/
namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### The Feynman–Kac semigroup -/

/-- **The positive kernel** `P_f(x, dy) = f(x)P(x, dy)` (MT p. 519), whose iterates form the
Feynman–Kac semigroup. -/
noncomputable def fkKernel (P : Kernel X X) [IsSFiniteKernel P] (f : X → ℝ≥0∞) : Kernel X X :=
  Kernel.withDensity P fun x _ => f x

/-- `P_f h(x) = f(x) Ph(x)`. -/
theorem lintegral_fkKernel (P : Kernel X X) [IsSFiniteKernel P] {f : X → ℝ≥0∞}
    (hf : Measurable f) (x : X) {h : X → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ y, h y ∂fkKernel P f x = f x * ∫⁻ y, h y ∂P x := by
  rw [fkKernel, Kernel.lintegral_withDensity (f := fun x (_ : X) => f x) _
    (hf.comp measurable_fst) x hh,
    lintegral_const_mul _ hh]

/-- `P_f^{n+1}h = P_f^n(P_f h)`. -/
theorem lintegral_fkKernel_pow_succ (P : Kernel X X) [IsSFiniteKernel P] {f : X → ℝ≥0∞}
    (n : ℕ) (x : X) {h : X → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ y, h y ∂(fkKernel P f ^ (n + 1)) x =
      ∫⁻ y, (∫⁻ z, h z ∂fkKernel P f y) ∂(fkKernel P f ^ n) x := by
  rw [pow_succ']
  exact Kernel.lintegral_comp _ _ _ hh

/-- **The Feynman–Kac representation** (20.13), MT p. 519, for every initial law and every
measurable `h ≥ 0`: `∫ E_x[Πₖ<ₙ f(Φₖ) h(Φₙ)] μ(dx) = ∫ P_fⁿh dμ`. -/
theorem feynmanKac (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ≥0∞} (hf : Measurable f)
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) {h : X → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ ω, (∏ k ∈ Finset.range n, f (ω k)) * h (ω n) ∂pathMeasure P μ =
      ∫⁻ x, ∫⁻ y, h y ∂(fkKernel P f ^ n) x ∂μ := by
  induction n generalizing h with
  | zero =>
    have := isProbabilityMeasure_pathMeasure P μ
    simp_rw [Finset.range_zero, Finset.prod_empty, one_mul, pow_zero_apply]
    rw [← lintegral_map hh (measurable_pi_apply 0), pathMeasure_map_zero]
    exact lintegral_congr fun x => (lintegral_dirac' x hh).symm
  | succ n ih =>
    have hF : Measurable[natFilt (X := X) n] fun ω : ℕ → X =>
        (∏ k ∈ Finset.range n, f (ω k)) * f (ω n) := by
      refine Measurable.mul (Finset.measurable_prod _ fun k hk => ?_) ?_
      · exact (hf.comp (measurable_coord_natFilt k)).mono
          ((natFilt (X := X)).mono (le_of_lt (Finset.mem_range.1 hk))) le_rfl
      · exact hf.comp (measurable_coord_natFilt n)
    have hH : Measurable fun ω' : ℕ → X => h (ω' 1) := hh.comp (measurable_pi_apply 1)
    have hstep := markov_lintegral_mul P μ hF hH
    have hint : ∀ y, ∫⁻ ω', h (ω' 1) ∂pathKernel P y = ∫⁻ z, h z ∂P y := fun y => by
      rw [← lintegral_map hh (measurable_pi_apply 1), pathKernel_map_coord, pow_one]
    simp_rw [hint] at hstep
    have hlhs : ∀ ω : ℕ → X, (∏ k ∈ Finset.range (n + 1), f (ω k)) * h (ω (n + 1)) =
        (∏ k ∈ Finset.range n, f (ω k)) * f (ω n) * h (shift n ω 1) := fun ω => by
      rw [Finset.prod_range_succ]; rfl
    simp_rw [hlhs]
    rw [hstep]
    have hmeas' : Measurable fun y => ∫⁻ z, h z ∂fkKernel P f y := hh.lintegral_kernel
    calc ∫⁻ ω, (∏ k ∈ Finset.range n, f (ω k)) * f (ω n) * ∫⁻ z, h z ∂P (ω n)
          ∂pathMeasure P μ
        = ∫⁻ ω, (∏ k ∈ Finset.range n, f (ω k)) * ∫⁻ z, h z ∂fkKernel P f (ω n)
            ∂pathMeasure P μ :=
          lintegral_congr fun ω => by rw [mul_assoc, lintegral_fkKernel P hf _ hh]
      _ = ∫⁻ x, ∫⁻ y, (∫⁻ z, h z ∂fkKernel P f y) ∂(fkKernel P f ^ n) x ∂μ := ih hmeas'
      _ = _ := lintegral_congr fun x => (lintegral_fkKernel_pow_succ P n x hh).symm

/-- **(20.13) at a point** (MT p. 519): `P_fⁿ(x, A) = E_x[Πₖ<ₙ f(Φₖ) 1{Φₙ ∈ A}]`; with
`f = e^F` this is `E_x[exp(Sₙ(F)) 1{Φₙ ∈ A}]`, and `A = X` gives `λₙ,ₓ(F)` (20.12). -/
theorem feynmanKac_apply (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ≥0∞} (hf : Measurable f)
    (x : X) (n : ℕ) {A : Set X} (hA : MeasurableSet A) :
    (fkKernel P f ^ n) x A =
      ∫⁻ ω, (∏ k ∈ Finset.range n, f (ω k)) * A.indicator 1 (ω n) ∂pathKernel P x := by
  have h := feynmanKac P hf (Measure.dirac x) n (measurable_one.indicator hA)
  rw [pathMeasure_dirac, lintegral_dirac' x (Measurable.lintegral_kernel
    (measurable_one.indicator hA))] at h
  rw [h, lintegral_indicator_one hA]

/-- **The killed semigroup (20.16)** (MT p. 520): with `f = 1_M`,
`P_Mⁿ(x, A) = P_x{Φ₀, …, Φₙ₋₁ ∈ M, Φₙ ∈ A}`, the probability of staying in `M` up to time
`n − 1` and being in `A` at time `n`. -/
theorem killedKernel_apply (P : Kernel X X) [IsMarkovKernel P] {M : Set X}
    (hM : MeasurableSet M) (x : X) (n : ℕ) {A : Set X} (hA : MeasurableSet A) :
    (fkKernel P (M.indicator 1) ^ n) x A =
      pathKernel P x {ω | (∀ k < n, ω k ∈ M) ∧ ω n ∈ A} := by
  have hE : MeasurableSet {ω : ℕ → X | (∀ k < n, ω k ∈ M) ∧ ω n ∈ A} := by
    have : {ω : ℕ → X | (∀ k < n, ω k ∈ M) ∧ ω n ∈ A} =
        (⋂ k ∈ Finset.range n, {ω | ω k ∈ M}) ∩ {ω | ω n ∈ A} := by
      ext ω; simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_range]
    rw [this]
    exact (Finset.measurableSet_biInter _ fun k _ => measurable_pi_apply k hM).inter
      (measurable_pi_apply n hA)
  rw [feynmanKac_apply P (measurable_one.indicator hM) x n hA, ← lintegral_indicator_one hE]
  refine lintegral_congr fun ω => ?_
  by_cases h1 : ∀ k < n, ω k ∈ M
  · rw [Finset.prod_eq_one fun k hk => by
      rw [indicator_of_mem (h1 k (Finset.mem_range.1 hk)), Pi.one_apply], one_mul]
    by_cases h2 : ω n ∈ A
    · rw [indicator_of_mem h2, indicator_of_mem (show ω ∈ {ω : ℕ → X | (∀ k < n, ω k ∈ M) ∧
        ω n ∈ A} from ⟨h1, h2⟩), Pi.one_apply, Pi.one_apply]
    · rw [indicator_of_notMem h2, indicator_of_notMem (fun h => h2 h.2)]
  · push Not at h1
    obtain ⟨k, hk, hkM⟩ := h1
    rw [Finset.prod_eq_zero (Finset.mem_range.2 hk) (indicator_of_notMem hkM _), zero_mul,
      indicator_of_notMem (fun h => hkM (h.1 k hk))]

/-- **(20.16) is not about the return time `τ_M`.** On `Bool` with the identity kernel and
`M = {true}`, `P_M¹(true, {true}) = 1`, while the event `{Φ₁ ∈ {true}, τ_M > 1}` for the return
time `τ_M = min{n ≥ 1 : Φₙ ∈ M}` (MT p. 525) is empty. In (20.16) `τ_M` must be read as the exit
time from `M` (`killedKernel_apply`). -/
theorem killedKernel_returnTime_counterexample :
    (fkKernel (Kernel.id : Kernel Bool Bool) (({true} : Set Bool).indicator 1) ^ 1) true
        {true} = 1 ∧
      {ω : ℕ → Bool | ω 1 ∈ ({true} : Set Bool) ∧ ∀ k, 1 ≤ k → k ≤ 1 → ω k ∉ ({true} : Set Bool)}
        = ∅ := by
  refine ⟨?_, ?_⟩
  · rw [pow_one, ← lintegral_indicator_one (measurableSet_singleton true),
      lintegral_fkKernel _ (measurable_one.indicator (measurableSet_singleton true)) _
        (measurable_one.indicator (measurableSet_singleton true)),
      Kernel.id_apply, lintegral_dirac, indicator_of_mem (mem_singleton true), Pi.one_apply,
      one_mul]
  · ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    exact h2 1 le_rfl le_rfl h1

/-! ### The twisted kernel and the multiplicative Poisson equation -/

/-- **The twisted kernel** (MT p. 519): `P̌(x, A) = f(x)/(λf̌(x)) ∫_A P(x, dy) f̌(y)`. -/
noncomputable def twistedKernel (P : Kernel X X) [IsSFiniteKernel P] (f fc : X → ℝ≥0∞)
    (lam : ℝ≥0∞) : Kernel X X :=
  Kernel.withDensity P fun x y => f x * fc y / (lam * fc x)

/-- **The twisted kernel is a Markov kernel** when `f̌` is a positive eigenfunction,
`P_f f̌ = λf̌` (MT p. 519). -/
theorem isMarkovKernel_twistedKernel (P : Kernel X X) [IsSFiniteKernel P] {f fc : X → ℝ≥0∞}
    (hf : Measurable f) (hfc : Measurable fc) {lam : ℝ≥0∞} (hl0 : lam ≠ 0) (hlt : lam ≠ ∞)
    (hfc0 : ∀ x, fc x ≠ 0) (hfct : ∀ x, fc x ≠ ∞)
    (heig : ∀ x, f x * ∫⁻ y, fc y ∂P x = lam * fc x) :
    IsMarkovKernel (twistedKernel P f fc lam) := by
  have hm : Measurable (Function.uncurry fun x y => f x * fc y / (lam * fc x)) :=
    ((hf.comp measurable_fst).mul (hfc.comp measurable_snd)).div
      (measurable_const.mul (hfc.comp measurable_fst))
  refine ⟨fun x => ⟨?_⟩⟩
  rw [twistedKernel, Kernel.withDensity_apply' _ hm, Measure.restrict_univ]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (mul_ne_zero hl0 (hfc0 x))),
    lintegral_const_mul _ hfc, heig x, ENNReal.mul_inv_cancel (mul_ne_zero hl0 (hfc0 x))
      (ENNReal.mul_ne_top hlt (hfct x))]

/-- **The multiplicative Poisson equation, corrected** (MT p. 519): for positive `f`, `f̌`, `λ`
with `f(x) Pf̌(x) = λf̌(x)`, the nonlinear generator (20.10) satisfies
`H(F̌) = Λ − F` with `F = log f`, `F̌ = log f̌`, `Λ = log λ`; equivalently
`log Pe^{F̌} = F̌ − F + Λ`. -/
theorem nonlinGen_log_eigen (P : Kernel X X) {f fc : X → ℝ} {lam : ℝ} (hl : 0 < lam)
    (hf : ∀ x, 0 < f x) (hfc : ∀ x, 0 < fc x)
    (heig : ∀ x, f x * ∫ y, fc y ∂P x = lam * fc x) (x : X) :
    nonlinGen P (fun y => Real.log (fc y)) x = Real.log lam - Real.log (f x) ∧
      Real.log (∫ y, Real.exp (Real.log (fc y)) ∂P x) =
        Real.log (fc x) - Real.log (f x) + Real.log lam := by
  have hexp : ∀ y, Real.exp (Real.log (fc y)) = fc y := fun y => Real.exp_log (hfc y)
  have hP : ∫ y, fc y ∂P x = lam * fc x / f x := by
    rw [eq_div_iff (hf x).ne', mul_comm]; exact heig x
  simp_rw [hexp]
  refine ⟨?_, ?_⟩
  · rw [nonlinGen]
    simp_rw [hexp]
    have e : lam * fc x / f x / fc x = lam / f x := by
      have := (hfc x).ne'; have := (hf x).ne'; field_simp
    rw [hP, e, Real.log_div hl.ne' (hf x).ne']
  · rw [hP, Real.log_div (mul_pos hl (hfc x)).ne' (hf x).ne', Real.log_mul hl.ne' (hfc x).ne']
    ring

/-- **The multiplicative Poisson equation as printed fails** (MT p. 519 writes
`H(F̌) = F̌ − F + Λ(F)`): for the identity kernel on a point, `f = 1`, `λ = 1` and the
eigenfunction `f̌ = e`, `H(F̌) = 0` but `F̌ − F + Λ = 1`. -/
theorem nonlinGen_book_counterexample :
    (1 : ℝ) * ∫ _y, Real.exp 1 ∂(Kernel.id : Kernel Unit Unit) () = 1 * Real.exp 1 ∧
      nonlinGen (Kernel.id : Kernel Unit Unit) (fun _ => Real.log (Real.exp 1)) () ≠
        Real.log (Real.exp 1) - Real.log 1 + Real.log 1 := by
  have h1 : ∫ _y, Real.exp 1 ∂(Kernel.id : Kernel Unit Unit) () = Real.exp 1 := by
    rw [Kernel.id_apply, integral_dirac]
  refine ⟨by rw [h1], ?_⟩
  rw [nonlinGen, Real.log_exp, Real.log_one, Kernel.id_apply, integral_dirac, div_self
    (Real.exp_pos _).ne', Real.log_one]
  norm_num

end MeynTweedie.Epilogue

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.BoundedInProbability
import InvarianceTightness.MinimalInvariant
import InvarianceTightness.HarrisDefinitions
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Generalized sampling and invariant measures (MT §12.2)

Meyn and Tweedie, §12.2, pp. 292–297. `P` is a transition kernel on a measurable space `X` and
`h : X → [0, 1]` is measurable. No topology is used in this module.

**The kernels** (12.13)–(12.14).
* `killOp P w u = P I_w u`, `(P I_w u)(x) = ∫ P(x, dy) w(y) u(y)`, and
  `geomOp P w φ = Σₖ (P I_w)ᵏ φ`, with additivity, countable additivity and the minimality
  principle `geomOp_le`
  (`φ + P I_w G ≤ G` implies `Σₖ (P I_w)ᵏ φ ≤ G`).
* `killKernel P h = P I_{1−h}`, `genPotKernel P h = U_h = Σₖ (P I_{1−h})ᵏ P` (12.14),
  `genPotDensity P h w = U_h I_w` and `balayage P h = P_h = U_h I_h` (p. 295);
  `lintegral_genPotKernel`: `U_h f = Σₖ (P I_{1−h})ᵏ P f`.
* Special cases (p. 294): `genPotKernel_one` (`U_1 = P`), `genPotKernel_zero` (`U_0 = U`),
  `genPotKernel_indicator` (`U_{1_B} = U_B`).

**Theorem 12.2.1** (`theorem_12_2_1`, the resolvent equation, p. 294): for `g ≤ h`,
`U_g = U_h + U_h I_{h−g} U_g = U_h + U_g I_{h−g} U_h`; `geomOp_resolvent` is the operator form.

**The functions `L` and `Q`** (p. 296).
* `genL P h x = U_h(x, h)`, `balayage_univ` (`P_h(x, X) = L(x, h)`, (12.17)),
  `sum_iterate_killOp_add` and `genL_add_iInf` (`L(x, h) = 1 − inf_n (P I_{1−h})ⁿ 1`),
  `genL_le_one`, `genL_mono`, `genL_indicator` (`L(x, 1_B) = L(x, B)`),
  `isMarkovKernel_balayage` (`P_h` is Markov when `L ≡ 1`).
* `genQ P h x = P_x{Σ_{k ≥ 1} h(Φₖ) = ∞}`, `genQ_indicator` (`Q(x, 1_B) = Q(x, B)`);
  `iterate_killOp_one_eq` (`(P I_w)ⁿ 1 (x) = E_x[∏_{i=1}^{n} w(Φᵢ)]`, (12.12)).

**Theorem 12.2.2** (p. 296).
* (i) `theorem_12_2_2_i`: for the bivariate chain `Ψₖ = (Φₖ, Yₖ)`, `Yₖ` i.i.d. uniform on
  `[0, 1]` and independent of `Φ` (path law `P_x ⊗ (uniform)^ℕ`),
  `P_x{Ψₖ ∈ A_h i.o.} = Q(x, h)` (both Borel–Cantelli lemmas, conditionally on `Φ`).
* (ii) `theorem_12_2_2_ii`: `L(x, h) ≥ Q(x, h)`; `genL_add_lintegral_iInf` is the identity
  `L(x, h) = 1 − E_x[∏_{i ≥ 1} (1 − h(Φᵢ))]`, the path form of `P_x{τ_h < ∞} = L(x, h)`.
* (iii) `theorem_12_2_2_iii`: if `h ≤ e < 1` then `L(x, h) = 1` iff `Q(x, h) = 1`.

**Theorem 12.2.3** (p. 297).
* (i) `theorem_12_2_3_i`, corrected: for `L ≡ 1` and a subinvariant `μ` with `∫ h dμ < ∞`,
  `μ = μ I_h U_h` and `μ` is invariant; `lintegral_mul_genPot_le` is the minimality step
  `μ I_h U_h ≤ μ`.
* (ii) `theorem_12_2_3_ii`: if `ν P_h = ν`, then `μ = ν U_h` is invariant, `ε μ(C_ε) ≤ ν(X)` for
  `C_ε = {K_{1/2}(·, h) ≥ ε}` (`resolventH`), and the `C_ε` cover `X` when `L > 0`
  (`resolventH_pos`).

**Corrections.**
* Theorem 12.2.3 (i) is false for a σ-finite subinvariant `μ` with `∫ h dμ = ∞`:
  `theorem_12_2_3_i_counterexample` (the successor chain on `ℕ`, counting measure, `h ≡ 1`, so
  that `U_h = P` and the claimed representation is `μ = μP`). The book's proof applies
  Theorem 10.4.7 to the set `A_h` of the bivariate chain, which needs `μ(A_h) = ∫ h dμ < ∞`; the
  theorem is proved with that hypothesis (and needs no σ-finiteness).
* Theorem 12.2.3 (ii) assumes "`ν(B) = νU_hI_h(B)` for `B ⊆ A`" for an unspecified `A`; it is
  proved for `νP_h = ν`, which is how it is used in Theorem 12.3.2.

**Method.** The book proves Theorems 12.2.1 and 12.2.3 with the strong Markov property of the
bivariate chain. Here Theorem 12.2.1 is proved from the series (12.14) by the minimality of
`Σₖ (P I_w)ᵏ φ` (Neveu's operator argument, mentioned on p. 308), and Theorem 12.2.3 by the
test-function computations that underlie Theorem 10.4.7. The bivariate chain is used only in
Theorem 12.2.2 (i), where it is the statement.
-/

namespace MeynTweedie.InvarianceTightness

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal unitInterval

variable {X : Type*} [MeasurableSpace X]

/-! ### The operators `P I_w` and `Σₖ (P I_w)ᵏ` -/

/-- The operator `P I_w`: `(P I_w u)(x) = ∫ P(x, dy) w(y) u(y)` (MT p. 294, with `I_w` the
multiplication by `w`). -/
noncomputable def killOp (P : Kernel X X) (w u : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∫⁻ y, w y * u y ∂P x

/-- The series `Σₖ (P I_w)ᵏ φ`. -/
noncomputable def geomOp (P : Kernel X X) (w φ : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∑' k, (killOp P w)^[k] φ x

variable {P : Kernel X X} {w : X → ℝ≥0∞}

/-- `P I_w` preserves measurability. -/
theorem measurable_killOp (hw : Measurable w) {u : X → ℝ≥0∞} (hu : Measurable u) :
    Measurable (killOp P w u) :=
  (hw.mul hu).lintegral_kernel

/-- `(P I_w)ᵏ` preserves measurability. -/
theorem measurable_iterate_killOp (hw : Measurable w) (k : ℕ) {u : X → ℝ≥0∞}
    (hu : Measurable u) : Measurable ((killOp P w)^[k] u) := by
  induction k generalizing u with
  | zero => exact hu
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (measurable_killOp hw hu)

/-- `Σₖ (P I_w)ᵏ` preserves measurability. -/
theorem measurable_geomOp (hw : Measurable w) {φ : X → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (geomOp P w φ) :=
  Measurable.tsum fun k => measurable_iterate_killOp hw k hφ

/-- `P I_w` is monotone. -/
theorem killOp_mono {u v : X → ℝ≥0∞} (huv : u ≤ v) : killOp P w u ≤ killOp P w v :=
  fun x => lintegral_mono fun y => by gcongr; exact huv y

/-- `P I_w` is additive. -/
theorem killOp_add (hw : Measurable w) {u v : X → ℝ≥0∞} (hu : Measurable u) :
    killOp P w (u + v) = killOp P w u + killOp P w v := by
  ext x
  simp only [killOp, Pi.add_apply, mul_add]
  exact lintegral_add_left (hw.mul hu) _

/-- `P I_{w₁ + w₂} = P I_{w₁} + P I_{w₂}`. -/
theorem killOp_weight_add {w₁ w₂ : X → ℝ≥0∞} (hw₁ : Measurable w₁) {u : X → ℝ≥0∞}
    (hu : Measurable u) : killOp P (w₁ + w₂) u = killOp P w₁ u + killOp P w₂ u := by
  ext x
  simp only [killOp, Pi.add_apply, add_mul]
  exact lintegral_add_left (hw₁.mul hu) _

/-- `P I_w` commutes with countable sums. -/
theorem killOp_tsum (hw : Measurable w) {u : ℕ → X → ℝ≥0∞} (hu : ∀ n, Measurable (u n)) :
    killOp P w (fun x => ∑' n, u n x) = fun x => ∑' n, killOp P w (u n) x := by
  ext x
  simp only [killOp, ← ENNReal.tsum_mul_left]
  exact lintegral_tsum fun n => (hw.mul (hu n)).aemeasurable

/-- `P I_w` commutes with finite sums. -/
theorem killOp_finsetSum (hw : Measurable w) {u : ℕ → X → ℝ≥0∞} (hu : ∀ n, Measurable (u n))
    (s : Finset ℕ) :
    killOp P w (fun x => ∑ n ∈ s, u n x) = fun x => ∑ n ∈ s, killOp P w (u n) x := by
  ext x
  simp only [killOp, Finset.mul_sum]
  exact lintegral_finsetSum' s fun n _ => (hw.mul (hu n)).aemeasurable

/-- `(P I_w)ᵏ` is additive. -/
theorem iterate_killOp_add (hw : Measurable w) (k : ℕ) {u v : X → ℝ≥0∞} (hu : Measurable u)
    (hv : Measurable v) :
    (killOp P w)^[k] (u + v) = (killOp P w)^[k] u + (killOp P w)^[k] v := by
  induction k generalizing u v with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply]
    rw [killOp_add hw hu]
    exact ih (measurable_killOp hw hu) (measurable_killOp hw hv)

/-- `Σₖ (P I_w)ᵏ φ = φ + P I_w (Σₖ (P I_w)ᵏ φ)`. -/
theorem geomOp_eq (hw : Measurable w) {φ : X → ℝ≥0∞} (hφ : Measurable φ) :
    geomOp P w φ = φ + killOp P w (geomOp P w φ) := by
  have hdef : geomOp P w φ = fun x => ∑' k, (killOp P w)^[k] φ x := rfl
  rw [hdef, killOp_tsum hw fun k => measurable_iterate_killOp hw k hφ]
  ext x
  rw [Pi.add_apply, tsum_eq_zero_add' ENNReal.summable, Function.iterate_zero, id_eq]
  simp only [Function.iterate_succ_apply']

/-- **Minimality**: if `φ + P I_w G ≤ G`, then `Σₖ (P I_w)ᵏ φ ≤ G`. -/
theorem geomOp_le (hw : Measurable w) {φ G : X → ℝ≥0∞} (hφ : Measurable φ)
    (hG : φ + killOp P w G ≤ G) : geomOp P w φ ≤ G := by
  have hpart : ∀ n, (fun x => ∑ k ∈ Finset.range n, (killOp P w)^[k] φ x) ≤ G := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      have heq : (fun x => ∑ k ∈ Finset.range (n + 1), (killOp P w)^[k] φ x) =
          φ + killOp P w (fun x => ∑ k ∈ Finset.range n, (killOp P w)^[k] φ x) := by
        rw [killOp_finsetSum hw fun k => measurable_iterate_killOp hw k hφ]
        ext x
        rw [Finset.sum_range_succ', Pi.add_apply, add_comm]
        simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
      rw [heq]
      exact le_trans (add_le_add_right (killOp_mono ih) φ) hG
  intro x
  exact ENNReal.tsum_le_of_sum_range_le fun n => hpart n x

/-- `Σₖ (P I_w)ᵏ` is additive. -/
theorem geomOp_add (hw : Measurable w) {u v : X → ℝ≥0∞} (hu : Measurable u)
    (hv : Measurable v) : geomOp P w (u + v) = geomOp P w u + geomOp P w v := by
  ext x
  simp only [geomOp, Pi.add_apply, iterate_killOp_add hw _ hu hv]
  exact ENNReal.tsum_add

/-- **The resolvent equation** (Theorem 12.2.1, MT p. 294), operator form: for measurable
`0 ≤ g ≤ h ≤ 1` and `φ ≥ 0`, with `S_w = Σₖ (P I_w)ᵏ` and `R = P I_{h−g}`,
`S_{1−g} φ = S_{1−h} φ + S_{1−h} R S_{1−g} φ = S_{1−h} φ + S_{1−g} R S_{1−h} φ`. Both are proved
by the minimality of the series (`geomOp_le`), since `P I_{1−g} = P I_{1−h} + R`. -/
theorem geomOp_resolvent {g h : X → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h)
    (hgh : g ≤ h) (h1 : h ≤ 1) {φ : X → ℝ≥0∞} (hφ : Measurable φ) :
    geomOp P (1 - g) φ = geomOp P (1 - h) φ +
        geomOp P (1 - h) (killOp P (h - g) (geomOp P (1 - g) φ)) ∧
      geomOp P (1 - g) φ = geomOp P (1 - h) φ +
        geomOp P (1 - g) (killOp P (h - g) (geomOp P (1 - h) φ)) := by
  have hmg : Measurable (1 - g) := measurable_const.sub hg
  have hmh : Measurable (1 - h) := measurable_const.sub hh
  have hmhg : Measurable (h - g) := hh.sub hg
  have hsplit : (1 - g) = (1 - h) + (h - g) := by
    ext x; exact (tsub_add_tsub_cancel (h1 x) (hgh x)).symm
  have hT : ∀ u, Measurable u → killOp P (1 - g) u = killOp P (1 - h) u + killOp P (h - g) u :=
    fun u hu => by rw [hsplit, killOp_weight_add hmh hu]
  set F := geomOp P (1 - g) φ
  set H := geomOp P (1 - h) φ
  have hFm : Measurable F := measurable_geomOp hmg hφ
  have hHm : Measurable H := measurable_geomOp hmh hφ
  have hRFm : Measurable (killOp P (h - g) F) := measurable_killOp hmhg hFm
  have hF : F = φ + (killOp P (1 - h) F + killOp P (h - g) F) := by
    rw [← hT F hFm]; exact geomOp_eq hmg hφ
  -- the first form
  set G := geomOp P (1 - h) (φ + killOp P (h - g) F)
  have hGm : Measurable G := measurable_geomOp hmh (hφ.add hRFm)
  have hGF : G ≤ F := geomOp_le hmh (hφ.add hRFm) (le_of_eq (by conv_rhs => rw [hF]
                                                                ac_rfl))
  have hFG : F ≤ G := by
    refine geomOp_le hmg hφ ?_
    rw [hT G hGm]
    have hG : G = φ + killOp P (h - g) F + killOp P (1 - h) G := geomOp_eq hmh (hφ.add hRFm)
    calc φ + (killOp P (1 - h) G + killOp P (h - g) G)
        ≤ φ + (killOp P (1 - h) G + killOp P (h - g) F) := by
          gcongr; exact killOp_mono hGF
      _ = G := by conv_rhs => rw [hG]
                  ac_rfl
  have hfirst : F = H + geomOp P (1 - h) (killOp P (h - g) F) :=
    (le_antisymm hFG hGF).trans (geomOp_add hmh hφ hRFm)
  refine ⟨hfirst, ?_⟩
  -- the second form
  set D := geomOp P (1 - h) (killOp P (h - g) F)
  have hDm : Measurable D := measurable_geomOp hmh hRFm
  have hRHm : Measurable (killOp P (h - g) H) := measurable_killOp hmhg hHm
  have hD : D = killOp P (h - g) F + killOp P (1 - h) D := geomOp_eq hmh hRFm
  have hRF : killOp P (h - g) F = killOp P (h - g) H + killOp P (h - g) D := by
    rw [hfirst]; exact killOp_add hmhg hHm
  set S₂ := geomOp P (1 - g) (killOp P (h - g) H)
  have hS₂m : Measurable S₂ := measurable_geomOp hmg hRHm
  have hDS : S₂ ≤ D := by
    refine geomOp_le hmg hRHm (le_of_eq ?_)
    rw [hT D hDm]
    conv_rhs => rw [hD, hRF]
    ac_rfl
  have hle1 : H + S₂ ≤ F := by rw [hfirst]; gcongr
  have hle2 : F ≤ H + S₂ := by
    refine geomOp_le hmg hφ (le_of_eq ?_)
    have hS : S₂ = killOp P (h - g) H + killOp P (1 - g) S₂ := geomOp_eq hmg hRHm
    have hH : H = φ + killOp P (1 - h) H := geomOp_eq hmh hφ
    rw [killOp_add hmg hHm, hT H hHm]
    conv_rhs => rw [hH, hS]
    ac_rfl
  exact le_antisymm hle2 hle1


/-! ### The kernels `U_h` and `P_h` -/

omit [MeasurableSpace X] in
/-- A function of the second variable is jointly measurable. -/
theorem measurable_uncurry_snd [MeasurableSpace X] {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (Function.uncurry fun (_ : X) (y : X) => f y) :=
  hf.comp measurable_snd

/-- The kernel `P I_{1−h}`: move by `P`, then multiply by `1 − h` at the new state. -/
noncomputable def killKernel (P : Kernel X X) [IsSFiniteKernel P] (h : X → ℝ≥0∞) :
    Kernel X X :=
  P.withDensity fun _ y => 1 - h y

/-- Powers of a finite kernel are finite. -/
theorem isFiniteKernel_pow (K : Kernel X X) [IsFiniteKernel K] (n : ℕ) :
    IsFiniteKernel (K ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsFiniteKernel Kernel.id)
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsFiniteKernel ((K ^ n) ∘ₖ K))

/-- `P I_{1−h}` is a finite kernel. -/
theorem isFiniteKernel_killKernel (P : Kernel X X) [IsFiniteKernel P] (h : X → ℝ≥0∞) :
    IsFiniteKernel (killKernel P h) :=
  Kernel.isFiniteKernel_withDensity_of_bounded P (f := fun _ y => 1 - h y) ENNReal.one_ne_top
    fun _ _ => tsub_le_self

/-- The **generalized potential kernel** `U_h = Σₖ (P I_{1−h})ᵏ P` (12.14), MT p. 293. -/
noncomputable def genPotKernel (P : Kernel X X) [IsSFiniteKernel P] (h : X → ℝ≥0∞) :
    Kernel X X :=
  Kernel.sum fun k => P ∘ₖ (killKernel P h ^ k)

/-- `U_h` is s-finite. -/
theorem isSFiniteKernel_genPotKernel (P : Kernel X X) [IsFiniteKernel P] (h : X → ℝ≥0∞) :
    IsSFiniteKernel (genPotKernel P h) := by
  have := isFiniteKernel_killKernel P h
  exact Kernel.isSFiniteKernel_sum (hκs := fun k => by
    have := isFiniteKernel_pow (killKernel P h) k; infer_instance)

/-- The kernel `U_h I_w`: `(U_h I_w)(x, A) = ∫_A w dU_h(x)`. -/
noncomputable def genPotDensity (P : Kernel X X) [IsFiniteKernel P] (h w : X → ℝ≥0∞) :
    Kernel X X :=
  @Kernel.withDensity X X _ _ (genPotKernel P h) (isSFiniteKernel_genPotKernel P h)
    fun _ y => w y

/-- The **balayage kernel** `P_h = U_h I_h` (MT p. 295): `P_h(x, A) = ∫_A h dU_h(x)`. -/
noncomputable abbrev balayage (P : Kernel X X) [IsFiniteKernel P] (h : X → ℝ≥0∞) : Kernel X X :=
  genPotDensity P h h

/-- `∫ u d(P I_{1−h})(x) = (P I_{1−h} u)(x)`. -/
theorem lintegral_killKernel (P : Kernel X X) [IsSFiniteKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (x : X) {u : X → ℝ≥0∞} (hu : Measurable u) :
    ∫⁻ y, u y ∂killKernel P h x = killOp P (1 - h) u x :=
  Kernel.lintegral_withDensity P (measurable_uncurry_snd (measurable_const.sub hh)) x hu

/-- `∫ u d(P I_{1−h})ᵏ(x) = ((P I_{1−h})ᵏ u)(x)`. -/
theorem lintegral_killKernel_pow (P : Kernel X X) [IsSFiniteKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (k : ℕ) (x : X) {u : X → ℝ≥0∞} (hu : Measurable u) :
    ∫⁻ y, u y ∂(killKernel P h ^ k) x = (killOp P (1 - h))^[k] u x := by
  induction k generalizing x with
  | zero =>
    rw [pow_zero, Function.iterate_zero, id_eq]
    change ∫⁻ y, u y ∂Kernel.id x = u x
    rw [Kernel.id_apply, lintegral_dirac' _ hu]
  | succ k ih =>
    rw [Kernel.pow_add, pow_one, Kernel.lintegral_comp _ _ _ hu, Function.iterate_succ_apply']
    simp_rw [ih]
    exact lintegral_killKernel P hh x (measurable_iterate_killOp (measurable_const.sub hh) k hu)

/-- `U_h f = Σₖ (P I_{1−h})ᵏ P f` (12.14). -/
theorem lintegral_genPotKernel (P : Kernel X X) [IsSFiniteKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (x : X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂genPotKernel P h x = geomOp P (1 - h) (kfun P f) x := by
  rw [genPotKernel, Kernel.sum_apply, lintegral_sum_measure]
  exact tsum_congr fun k => (Kernel.lintegral_comp P _ x hf).trans
    (lintegral_killKernel_pow P hh k x (measurable_kfun P hf))

/-- `∫ u d(U_h I_w)(x) = U_h(w u)(x)`; in particular `∫ u dP_h(x) = U_h(h u)(x)`. -/
theorem lintegral_genPotDensity (P : Kernel X X) [IsFiniteKernel P] (h : X → ℝ≥0∞)
    {w : X → ℝ≥0∞} (hw : Measurable w) (x : X) {u : X → ℝ≥0∞} (hu : Measurable u) :
    ∫⁻ y, u y ∂genPotDensity P h w x = ∫⁻ y, w y * u y ∂genPotKernel P h x := by
  have := isSFiniteKernel_genPotKernel P h
  exact Kernel.lintegral_withDensity _ (measurable_uncurry_snd hw) x hu

/-- **Theorem 12.2.1** (the resolvent equation, MT p. 294): for measurable `0 ≤ g ≤ h ≤ 1`,
`U_g = U_h + U_h I_{h−g} U_g = U_h + U_g I_{h−g} U_h`. In Mathlib's order of composition
(`η ∘ₖ κ` is "first `κ`, then `η`"), `U_h I_{h−g} U_g` is `U_g ∘ₖ (U_h I_{h−g})`. -/
theorem theorem_12_2_1 (P : Kernel X X) [IsFiniteKernel P] {g h : X → ℝ≥0∞} (hg : Measurable g)
    (hh : Measurable h) (hgh : g ≤ h) (h1 : h ≤ 1) :
    genPotKernel P g = genPotKernel P h + genPotKernel P g ∘ₖ genPotDensity P h (h - g) ∧
      genPotKernel P g = genPotKernel P h + genPotKernel P h ∘ₖ genPotDensity P g (h - g) := by
  constructor
  · refine Kernel.ext_fun fun x f hf => ?_
    rw [_root_.add_apply, lintegral_add_measure, Kernel.lintegral_comp _ _ _ hf,
      lintegral_genPotDensity P h (hh.sub hg) x hf.lintegral_kernel]
    simp_rw [lintegral_genPotKernel P hg _ hf]
    rw [lintegral_genPotKernel P hh x hf,
      lintegral_genPotKernel P hh x (f := fun y => (h - g) y * geomOp P (1 - g) (kfun P f) y)
        ((hh.sub hg).mul (measurable_geomOp (measurable_const.sub hg) (measurable_kfun P hf)))]
    exact congrFun (geomOp_resolvent hg hh hgh h1 (measurable_kfun P hf)).1 x
  · refine Kernel.ext_fun fun x f hf => ?_
    rw [_root_.add_apply, lintegral_add_measure, Kernel.lintegral_comp _ _ _ hf,
      lintegral_genPotDensity P g (hh.sub hg) x hf.lintegral_kernel]
    simp_rw [lintegral_genPotKernel P hh _ hf]
    rw [lintegral_genPotKernel P hg x hf,
      lintegral_genPotKernel P hg x (f := fun y => (h - g) y * geomOp P (1 - h) (kfun P f) y)
        ((hh.sub hg).mul (measurable_geomOp (measurable_const.sub hh) (measurable_kfun P hf)))]
    exact congrFun (geomOp_resolvent hg hh hgh h1 (measurable_kfun P hf)).2 x


/-! ### Special cases -/

/-- `U_h = P` for `h ≡ 1` (MT p. 294). -/
theorem genPotKernel_one (P : Kernel X X) [IsFiniteKernel P] : genPotKernel P 1 = P := by
  refine Kernel.ext_fun fun x f hf => ?_
  rw [lintegral_genPotKernel P (h := 1) measurable_one x hf, geomOp,
    tsum_eq_zero_add' ENNReal.summable]
  have h0 : ∀ k, (killOp P (1 - 1))^[k + 1] (kfun P f) x = 0 := fun k => by
    rw [Function.iterate_succ_apply']
    simp [killOp]
  simp_rw [h0, tsum_zero, add_zero, Function.iterate_zero, id_eq]
  rfl

/-- `U_h = U = Σ_{n ≥ 1} Pⁿ` for `h ≡ 0` (MT p. 294). -/
theorem genPotKernel_zero (P : Kernel X X) [IsFiniteKernel P] : genPotKernel P 0 = potKernel P := by
  refine Kernel.ext_fun fun x f hf => ?_
  rw [lintegral_genPotKernel P (h := 0) measurable_zero x hf, potKernel, Kernel.sum_apply,
    lintegral_sum_measure, geomOp]
  have hA : ∀ u : X → ℝ≥0∞, killOp P (1 - 0) u = kfun P u := fun u => by
    ext y; simp [killOp, kfun]
  have hk : ∀ k, (killOp P (1 - 0))^[k] (kfun P f) = kfun (P ^ (k + 1)) f := fun k => by
    induction k with
    | zero => rw [Function.iterate_zero, id_eq, pow_one]
    | succ k ih => rw [Function.iterate_succ_apply', ih, hA, ← kfun_pow_succ P (k + 1) hf]
  exact tsum_congr fun k => by rw [hk]; rfl


/-- `U_h = U_B`, the taboo potential kernel, for `h = 1_B` (MT p. 294). -/
theorem genPotKernel_indicator (P : Kernel X X) [IsFiniteKernel P] {B : Set X}
    (hB : MeasurableSet B) : genPotKernel P (B.indicator 1) = tabooPotKernel P hB := by
  have hK : killKernel P (B.indicator 1) = indKernel hB.compl ∘ₖ P := by
    ext x A hA
    have h1 : (fun y => 1 - B.indicator (1 : X → ℝ≥0∞) y) = Bᶜ.indicator 1 := by
      ext y; by_cases hy : y ∈ B <;> simp [hy]
    rw [comp_indKernel_eq_restrict, killKernel,
      Kernel.withDensity_apply P (f := fun _ y => 1 - B.indicator (1 : X → ℝ≥0∞) y)
        (measurable_uncurry_snd (f := fun y => 1 - B.indicator (1 : X → ℝ≥0∞) y)
          (measurable_const.sub (measurable_one.indicator hB))), h1,
      withDensity_indicator_one hB.compl]
  rw [genPotKernel, tabooPotKernel, hK]
  rfl

/-! ### The function `L(x, h)` -/

/-- `L(x, h) = U_h(x, h)` (MT p. 296); `L(x, 1_B) = L(x, B)` (`genL_indicator`). -/
noncomputable def genL (P : Kernel X X) [IsFiniteKernel P] (h : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∫⁻ y, h y ∂genPotKernel P h x

/-- `P_h(x, X) = L(x, h)` (12.17). -/
theorem balayage_univ (P : Kernel X X) [IsFiniteKernel P] {h : X → ℝ≥0∞} (hh : Measurable h)
    (x : X) : balayage P h x univ = genL P h x := by
  rw [← lintegral_one, lintegral_genPotDensity P h hh x (u := fun _ => 1) measurable_const]
  simp [genL]

/-- `P h + P I_{1−h} 1 = 1` for a Markov kernel and `h ≤ 1`. -/
theorem kfun_add_killOp_one (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (h1 : h ≤ 1) : kfun P h + killOp P (1 - h) 1 = 1 := by
  ext x
  change ∫⁻ y, h y ∂P x + ∫⁻ y, (1 - h y) * 1 ∂P x = 1
  simp_rw [mul_one]
  rw [← lintegral_add_left hh,
    lintegral_congr fun y => add_tsub_cancel_of_le (show h y ≤ 1 from h1 y)]
  simp

/-- **The telescoping identity** behind (12.17): `Σ_{k<n} (P I_{1−h})ᵏ P h + (P I_{1−h})ⁿ 1 = 1`.
In path terms, `P_x(τ_h ≤ n) + P_x(τ_h > n) = 1`. -/
theorem sum_iterate_killOp_add (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (h1 : h ≤ 1) (n : ℕ) (x : X) :
    ∑ k ∈ Finset.range n, (killOp P (1 - h))^[k] (kfun P h) x + (killOp P (1 - h))^[n] 1 x = 1 := by
  have hm : Measurable (1 - h) := measurable_const.sub hh
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Function.iterate_succ_apply, add_assoc]
    have := congrFun (iterate_killOp_add (P := P) hm n (measurable_kfun P hh)
      (measurable_killOp (P := P) hm measurable_one)) x
    rw [Pi.add_apply] at this
    rw [← this, kfun_add_killOp_one P hh h1]
    exact ih x

/-- `L(x, h) + inf_n (P I_{1−h})ⁿ 1 (x) = 1`, i.e. `L(x, h) = 1 − P_x(τ_h = ∞)`. -/
theorem genL_add_iInf (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞} (hh : Measurable h)
    (h1 : h ≤ 1) (x : X) : genL P h x + ⨅ n, (killOp P (1 - h))^[n] 1 x = 1 := by
  have hpart : ∀ n, ∑ k ∈ Finset.range n, (killOp P (1 - h))^[k] (kfun P h) x =
      1 - (killOp P (1 - h))^[n] 1 x := fun n => by
    have h2 := sum_iterate_killOp_add P hh h1 n x
    have hne : (killOp P (1 - h))^[n] 1 x ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_of_le_of_eq le_add_self h2)
    exact ENNReal.eq_sub_of_add_eq hne h2
  have hle : ⨅ n, (killOp P (1 - h))^[n] 1 x ≤ 1 := (iInf_le _ 0).trans (by simp)
  rw [genL, lintegral_genPotKernel P hh x hh, geomOp, ENNReal.tsum_eq_iSup_nat]
  simp_rw [hpart, ← ENNReal.sub_iInf]
  exact tsub_add_cancel_of_le hle

/-- `L(x, h) ≤ 1`. -/
theorem genL_le_one (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞} (hh : Measurable h)
    (h1 : h ≤ 1) (x : X) : genL P h x ≤ 1 :=
  le_of_le_of_eq le_self_add (genL_add_iInf P hh h1 x)

/-- `L(·, h)` is monotone in `h`. -/
theorem genL_mono (P : Kernel X X) [IsMarkovKernel P] {h h' : X → ℝ≥0∞} (hh : Measurable h)
    (hh' : Measurable h') (hhh : h ≤ h') (h1 : h' ≤ 1) (x : X) : genL P h x ≤ genL P h' x := by
  have hit : ∀ n, (killOp P (1 - h'))^[n] 1 ≤ (killOp P (1 - h))^[n] 1 := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      intro y
      exact lintegral_mono fun z => by
        gcongr
        · exact tsub_le_tsub_left (hhh z) 1
        · exact ih z
  have e1 := genL_add_iInf P hh (hhh.trans h1) x
  have e2 := genL_add_iInf P hh' h1 x
  have hinf : ⨅ n, (killOp P (1 - h'))^[n] 1 x ≤ ⨅ n, (killOp P (1 - h))^[n] 1 x :=
    iInf_mono fun n => hit n x
  have hfin1 : ⨅ n, (killOp P (1 - h))^[n] 1 x ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_le_of_eq le_add_self e1)
  have hfin2 : ⨅ n, (killOp P (1 - h'))^[n] 1 x ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_le_of_eq le_add_self e2)
  rw [ENNReal.eq_sub_of_add_eq hfin1 e1, ENNReal.eq_sub_of_add_eq hfin2 e2]
  exact tsub_le_tsub_left hinf 1

/-- `L(x, 1_B) = L(x, B) = P_x(τ_B < ∞)` (MT p. 296). -/
theorem genL_indicator (P : Kernel X X) [IsMarkovKernel P] {B : Set X} (hB : MeasurableSet B)
    (x : X) : genL P (B.indicator 1) x = hitProb P B x := by
  rw [genL, genPotKernel_indicator P hB, lintegral_indicator_one hB, tabooPotKernel_self]

/-- `P_h` is a transition kernel when `L(x, h) = 1` for every `x` (MT p. 295). -/
theorem isMarkovKernel_balayage (P : Kernel X X) [IsFiniteKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (hL : ∀ x, genL P h x = 1) : IsMarkovKernel (balayage P h) :=
  ⟨fun x => ⟨by rw [balayage_univ P hh x, hL x]⟩⟩


/-! ### Products and exponentials -/

/-- `1 − t ≤ exp(−t)` in `[0, ∞]`, for `t ≤ 1`. -/
theorem one_sub_le_ofReal_exp {t : ℝ≥0∞} (ht : t ≤ 1) :
    1 - t ≤ ENNReal.ofReal (Real.exp (-t.toReal)) := by
  rw [← ENNReal.ofReal_toReal (a := 1 - t) (by finiteness),
    ENNReal.toReal_sub_of_le ht ENNReal.one_ne_top, ENNReal.toReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (-t.toReal)])

/-- `∏_{i<n} (1 − tᵢ) ≤ exp(−Σ_{i<n} tᵢ)` for `tᵢ ≤ 1`. -/
theorem prod_one_sub_le_ofReal_exp (t : ℕ → ℝ≥0∞) (ht : ∀ i, t i ≤ 1) (n : ℕ) :
    ∏ i ∈ Finset.range n, (1 - t i) ≤
      ENNReal.ofReal (Real.exp (-∑ i ∈ Finset.range n, (t i).toReal)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, neg_add, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_le_mul' ih (one_sub_le_ofReal_exp (ht n))

/-- For `0 ≤ s ≤ e < 1`, `exp(−s/(1 − e)) ≤ 1 − s`. -/
theorem exp_neg_div_le_one_sub {s e : ℝ} (hs : 0 ≤ s) (hse : s ≤ e) (he : e < 1) :
    Real.exp (-(s / (1 - e))) ≤ 1 - s := by
  have h1s : 0 < 1 - s := by linarith
  have h1e : 0 < 1 - e := by linarith
  have hk : s / (1 - s) ≤ s / (1 - e) := div_le_div_of_nonneg_left hs h1e (by linarith)
  have hexp : 1 / (1 - s) ≤ Real.exp (s / (1 - s)) := by
    have := Real.add_one_le_exp (s / (1 - s))
    calc 1 / (1 - s) = s / (1 - s) + 1 := by field_simp; ring
      _ ≤ _ := this
  calc Real.exp (-(s / (1 - e))) ≤ Real.exp (-(s / (1 - s))) :=
        Real.exp_le_exp.2 (neg_le_neg hk)
    _ = (Real.exp (s / (1 - s)))⁻¹ := Real.exp_neg _
    _ ≤ (1 / (1 - s))⁻¹ := inv_anti₀ (by positivity) hexp
    _ = 1 - s := by rw [one_div, inv_inv]

/-- `∏_{i<n} (1 − tᵢ) ≥ exp(−Σ_{i<n} tᵢ/(1 − e))` for `tᵢ ≤ e < 1`. -/
theorem ofReal_exp_le_prod_one_sub (t : ℕ → ℝ≥0∞) {e : ℝ} (he : e < 1)
    (ht : ∀ i, (t i).toReal ≤ e) (ht1 : ∀ i, t i ≤ 1) (n : ℕ) :
    ENNReal.ofReal (Real.exp (-(∑ i ∈ Finset.range n, (t i).toReal / (1 - e)))) ≤
      ∏ i ∈ Finset.range n, (1 - t i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, neg_add, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine mul_le_mul' ih ?_
    rw [← ENNReal.ofReal_toReal (a := 1 - t n) (by finiteness),
      ENNReal.toReal_sub_of_le (ht1 n) ENNReal.one_ne_top, ENNReal.toReal_one]
    exact ENNReal.ofReal_le_ofReal (exp_neg_div_le_one_sub ENNReal.toReal_nonneg (ht n) he)

/-- If `Σ tᵢ = ∞` (with `tᵢ ≤ 1`), then `inf_n ∏_{i<n} (1 − tᵢ) = 0`. -/
theorem iInf_prod_one_sub_eq_zero (t : ℕ → ℝ≥0∞) (ht : ∀ i, t i ≤ 1) (hsum : ∑' i, t i = ∞) :
    ⨅ n, ∏ i ∈ Finset.range n, (1 - t i) = 0 := by
  have hsum_eq : ∀ n, ∑ i ∈ Finset.range n, t i =
      ENNReal.ofReal (∑ i ∈ Finset.range n, (t i).toReal) := fun n => by
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
    exact Finset.sum_congr rfl fun i _ =>
      (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (ht i))).symm
  have hpart : ∀ M : ℝ, ∃ n, M ≤ ∑ i ∈ Finset.range n, (t i).toReal := fun M => by
    by_contra h
    push Not at h
    have : ∑' i, t i ≤ ENNReal.ofReal M := ENNReal.tsum_le_of_sum_range_le fun n => by
      rw [hsum_eq n]; exact ENNReal.ofReal_le_ofReal (h n).le
    rw [hsum] at this
    exact ENNReal.ofReal_ne_top (top_le_iff.1 this)
  have hbound : ∀ k : ℕ, ⨅ n, ∏ i ∈ Finset.range n, (1 - t i) ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ))) := fun k => by
    obtain ⟨n, hn⟩ := hpart k
    exact iInf_le_of_le n ((prod_one_sub_le_ofReal_exp t ht n).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg hn))))
  have ht0 : Tendsto (fun k : ℕ => ENNReal.ofReal (Real.exp (-(k : ℝ)))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)
  exact le_antisymm (ge_of_tendsto' ht0 hbound) bot_le

/-- If `Σ tᵢ < ∞` with `tᵢ ≤ e < 1`, then `inf_n ∏_{i<n} (1 − tᵢ) > 0`. -/
theorem iInf_prod_one_sub_pos (t : ℕ → ℝ≥0∞) {e : ℝ} (he : e < 1)
    (ht : ∀ i, (t i).toReal ≤ e) (ht1 : ∀ i, t i ≤ 1) (hsum : ∑' i, t i ≠ ∞) :
    0 < ⨅ n, ∏ i ∈ Finset.range n, (1 - t i) := by
  set S := (∑' i, t i).toReal
  have hpart : ∀ n, ∑ i ∈ Finset.range n, (t i).toReal ≤ S := fun n => by
    have hfin : ∀ i ∈ Finset.range n, t i ≠ ∞ := fun i _ =>
      ne_top_of_le_ne_top ENNReal.one_ne_top (ht1 i)
    rw [← ENNReal.toReal_sum hfin]
    exact ENNReal.toReal_mono hsum (ENNReal.sum_le_tsum _)
  have h1e : 0 < 1 - e := by linarith
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos (-(S / (1 - e)))))
    (le_iInf fun n => ?_)
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    (ofReal_exp_le_prod_one_sub t he ht ht1 n)
  rw [neg_le_neg_iff, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right (hpart n) h1e.le


/-! ### Theorem 12.2.2 -/

/-- **Path form of `(P I_w)ⁿ 1`**: `((P I_w)ⁿ 1)(x) = E_x[∏_{i=1}^{n} w(Φᵢ)]`, from the Markov
property at time `1`. For `w = 1 − h` this is `P_x(τ_h > n)` given `Φ` (12.12). -/
theorem iterate_killOp_one_eq (P : Kernel X X) [IsMarkovKernel P] {w : X → ℝ≥0∞}
    (hw : Measurable w) (n : ℕ) (x : X) :
    (killOp P w)^[n] 1 x = ∫⁻ ω, ∏ i ∈ Finset.range n, w (ω (i + 1)) ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    set H : (ℕ → X) → ℝ≥0∞ := fun ω => ∏ i ∈ Finset.range n, w (ω (i + 1))
    have hH : Measurable H := Finset.measurable_prod _ fun i _ =>
      hw.comp (measurable_pi_apply _)
    have hsplit : ∀ ω : ℕ → X, ∏ i ∈ Finset.range (n + 1), w (ω (i + 1)) =
        w (ω 1) * H (shift 1 ω) := fun ω => by
      rw [Finset.prod_range_succ', mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [shift_apply]
      congr 2
      omega
    simp_rw [hsplit]
    have hF : Measurable[natFilt 1] fun ω : ℕ → X => w (ω 1) :=
      hw.comp (measurable_coord_natFilt 1)
    have hm := markov_lintegral_mul P (Measure.dirac x) hF hH
    rw [pathMeasure_dirac] at hm
    rw [hm, Function.iterate_succ_apply']
    have hg : Measurable fun y => w y * ∫⁻ ω', H ω' ∂pathKernel P y :=
      hw.mul hH.lintegral_kernel
    have hmap := lintegral_map hg (measurable_pi_apply 1 : Measurable fun ω : ℕ → X => ω 1)
      (μ := pathKernel P x)
    rw [pathKernel_map_coord, pow_one] at hmap
    rw [← hmap]
    simp only [killOp]
    refine lintegral_congr fun y => ?_
    rw [ih y]

/-- The function `Q(x, h) = P_x{Σ_{k ≥ 1} h(Φₖ) = ∞}` (MT p. 296); `genQ_indicator`:
`Q(x, 1_B) = Q(x, B)`. -/
noncomputable def genQ (P : Kernel X X) [IsMarkovKernel P] (h : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  pathKernel P x {ω | ∑' i, h (ω (i + 1)) = ∞}

/-- `Q(x, 1_B) = Q(x, B)`, the probability of infinitely many visits to `B`. -/
theorem genQ_indicator (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (x : X) :
    genQ P (B.indicator 1) x = harrisQ P B x := by
  rw [harrisQ_eq_occTime]; rfl

/-- `L(x, h) = 1 − E_x[∏_{i ≥ 1} (1 − h(Φᵢ))]`, the identity behind Theorem 12.2.2 (ii). -/
theorem genL_add_lintegral_iInf (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (h1 : h ≤ 1) (x : X) :
    genL P h x + ∫⁻ ω, ⨅ n, ∏ i ∈ Finset.range n, (1 - h (ω (i + 1))) ∂pathKernel P x = 1 := by
  have := isMarkovKernel_pathKernel P
  have hm : Measurable (1 - h) := measurable_const.sub hh
  have key : ∀ n, ∫⁻ ω, ∏ i ∈ Finset.range n, (1 - h (ω (i + 1))) ∂pathKernel P x =
      (killOp P (1 - h))^[n] 1 x := fun n => (iterate_killOp_one_eq P hm n x).symm
  rw [lintegral_iInf (μ := pathKernel P x)
      (f := fun (n : ℕ) (ω : ℕ → X) => ∏ i ∈ Finset.range n, (1 - h (ω (i + 1))))
      (fun n => Finset.measurable_prod _ fun i _ =>
        (show Measurable fun ω : ℕ → X => 1 - h (ω (i + 1)) from
          measurable_const.sub (hh.comp (measurable_pi_apply (i + 1)))))
      (fun m n hmn ω => Finset.prod_le_prod_of_subset_of_le_one (Finset.range_mono hmn)
        fun i _ _ => tsub_le_self)
      (by simp)]
  simp_rw [key]
  exact genL_add_iInf P hh h1 x

/-- Preimages of measurable sets under independent random variables are independent events. -/
theorem iIndepSet_preimage_of_iIndepFun {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {μ : Measure Ω} {f : ℕ → Ω → β} (hf : iIndepFun f μ) {A : ℕ → Set β}
    (hA : ∀ i, MeasurableSet (A i)) : iIndepSet (fun i => f i ⁻¹' A i) μ := by
  rw [iIndepSet_iff]
  intro S g H
  have hB : ∀ i, ∃ B : Set β, MeasurableSet B ∧ (i ∈ S → f i ⁻¹' B = g i) := fun i => by
    by_cases hi : i ∈ S
    · have hle : MeasurableSpace.generateFrom {f i ⁻¹' A i} ≤
          MeasurableSpace.comap (f i) inferInstance :=
        MeasurableSpace.generateFrom_le fun t ht => by
          rw [mem_singleton_iff.1 ht]; exact ⟨A i, hA i, rfl⟩
      obtain ⟨B, hBm, hBg⟩ := MeasurableSpace.measurableSet_comap.1 (hle _ (H i hi))
      exact ⟨B, hBm, fun _ => hBg⟩
    · exact ⟨univ, MeasurableSet.univ, fun h => absurd h hi⟩
  choose B hBm hBg using hB
  have h1 : (⋂ i ∈ S, g i) = ⋂ i ∈ S, f i ⁻¹' B i :=
    iInter₂_congr fun i hi => (hBg i hi).symm
  rw [h1, hf.measure_inter_preimage_eq_mul S fun i _ => hBm i]
  exact Finset.prod_congr rfl fun i hi => by rw [hBg i hi]

/-- The uniform law of `[0, 1]` gives `{v ≤ t}` mass `t`. -/
theorem volume_unitInterval_le {t : ℝ} (ht1 : t ≤ 1) :
    (volume : Measure I) {v : I | (v : ℝ) ≤ t} = ENNReal.ofReal t := by
  rw [unitInterval.volume_apply]
  have : (Subtype.val '' {v : I | (v : ℝ) ≤ t}) = Icc 0 t := by
    ext s
    simp only [mem_image, mem_ofPred_eq, Subtype.exists, mem_Icc, exists_and_right,
      exists_eq_right]
    constructor
    · rintro ⟨hs, hst⟩; exact ⟨hs.1, hst⟩
    · rintro ⟨hs0, hst⟩; exact ⟨⟨hs0, hst.trans ht1⟩, hst⟩
  rw [this, Real.volume_Icc, sub_zero]

/-- **Theorem 12.2.2 (i)** (MT p. 296). Adjoin to the chain an independent i.i.d. sequence
`Yₖ` of uniform variables on `[0, 1]`: the bivariate chain `Ψₖ = (Φₖ, Yₖ)` has path law
`P_x ⊗ (uniform)^ℕ`, and `A_h = {(x, u) : u ≤ h(x)}`. Then
`P_x{Ψₖ ∈ A_h i.o.} = Q(x, h)`: given the path of `Φ`, the events `{Yₖ ≤ h(Φₖ)}` are independent
with probabilities `h(Φₖ)`, so by the two Borel–Cantelli lemmas they occur infinitely often with
probability `1` or `0` according as `Σ h(Φₖ)` diverges or converges. -/
theorem theorem_12_2_2_i (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞} (hh : Measurable h)
    (h1 : h ≤ 1) (x : X) :
    ((pathKernel P x).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I)))
      {p : (ℕ → X) × (ℕ → I) | ∀ N, ∃ k, N ≤ k ∧ ((p.2 k : I) : ℝ) ≤ (h (p.1 k)).toReal} =
      genQ P h x := by
  have := isMarkovKernel_pathKernel P
  set lam := Measure.infinitePi fun _ : ℕ => (volume : Measure I)
  set E := {p : (ℕ → X) × (ℕ → I) | ∀ N, ∃ k, N ≤ k ∧ ((p.2 k : I) : ℝ) ≤ (h (p.1 k)).toReal}
  have hset : ∀ k, MeasurableSet {p : (ℕ → X) × (ℕ → I) |
      ((p.2 k : I) : ℝ) ≤ (h (p.1 k)).toReal} := fun k =>
    measurableSet_le (continuous_subtype_val.measurable.comp
      ((measurable_pi_apply k).comp measurable_snd))
      (ENNReal.measurable_toReal.comp (hh.comp ((measurable_pi_apply k).comp measurable_fst)))
  have hE : MeasurableSet E := by
    have : E = ⋂ N, ⋃ k, ⋃ (_ : N ≤ k), {p : (ℕ → X) × (ℕ → I) |
        ((p.2 k : I) : ℝ) ≤ (h (p.1 k)).toReal} := by
      ext p; simp [E]
    rw [this]
    exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun k =>
      MeasurableSet.iUnion fun _ => hset k
  set F := {ω : ℕ → X | ∑' k, h (ω k) = ∞}
  have hFm : MeasurableSet F :=
    (Measurable.tsum fun k => hh.comp (measurable_pi_apply k)) (measurableSet_singleton ∞)
  have hindep : iIndepFun (fun k (u : ℕ → I) => u k) lam :=
    iIndepFun_infinitePi (X := fun _ (v : I) => v) fun _ => measurable_id
  have hsec : ∀ ω : ℕ → X, lam (Prod.mk ω ⁻¹' E) = F.indicator 1 ω := fun ω => by
    set s : ℕ → Set (ℕ → I) := fun k =>
      (fun u : ℕ → I => u k) ⁻¹' {v : I | (v : ℝ) ≤ (h (ω k)).toReal}
    have hsm : ∀ k, MeasurableSet (s k) := fun k =>
      measurable_pi_apply k (measurableSet_le continuous_subtype_val.measurable measurable_const)
    have hlim : Prod.mk ω ⁻¹' E = limsup s atTop := by
      ext u
      simp only [mem_preimage, mem_ofPred_eq, E, mem_limsup_iff_frequently_mem,
        frequently_atTop, s]
    have hs : ∀ k, lam (s k) = h (ω k) := fun k => by
      have hmap := Measure.infinitePi_map_eval (μ := fun _ : ℕ => (volume : Measure I)) k
      rw [← Measure.map_apply (measurable_pi_apply k)
        (measurableSet_le continuous_subtype_val.measurable measurable_const), hmap,
        volume_unitInterval_le ((ENNReal.toReal_mono ENNReal.one_ne_top (h1 _)).trans_eq
          ENNReal.toReal_one), ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
          (h1 _))]
    rw [hlim]
    by_cases hω : ω ∈ F
    · rw [indicator_of_mem hω, Pi.one_apply]
      refine measure_limsup_eq_one hsm (iIndepSet_preimage_of_iIndepFun hindep fun k =>
        measurableSet_le continuous_subtype_val.measurable measurable_const) ?_
      simp_rw [hs]; exact hω
    · rw [indicator_of_notMem hω]
      refine measure_limsup_atTop_eq_zero ?_
      simp_rw [hs]; exact hω
  rw [Measure.prod_apply hE]
  simp_rw [hsec]
  rw [lintegral_indicator_one hFm, genQ]
  congr 1
  ext ω
  simp only [F, mem_ofPred_eq]
  rw [tsum_eq_zero_add' ENNReal.summable, ENNReal.add_eq_top]
  have : h (ω 0) ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (h1 _)
  simp [this]

/-- **Theorem 12.2.2 (ii)** (MT p. 296), the inequality: `L(x, h) ≥ Q(x, h)`. On
`{Σ h(Φᵢ) = ∞}` the product `∏ (1 − h(Φᵢ))` vanishes, so `E_x[∏ (1 − h(Φᵢ))] ≤ 1 − Q(x, h)`. -/
theorem theorem_12_2_2_ii (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (h1 : h ≤ 1) (x : X) : genQ P h x ≤ genL P h x := by
  have := isMarkovKernel_pathKernel P
  set E := {ω : ℕ → X | ∑' i, h (ω (i + 1)) = ∞}
  have hE : MeasurableSet E :=
    (Measurable.tsum fun i => hh.comp (measurable_pi_apply (i + 1)))
      (measurableSet_singleton ∞)
  have hle : ∫⁻ ω, ⨅ n, ∏ i ∈ Finset.range n, (1 - h (ω (i + 1))) ∂pathKernel P x ≤
      pathKernel P x Eᶜ := by
    rw [← lintegral_indicator_one hE.compl]
    refine lintegral_mono fun ω => ?_
    by_cases hω : ω ∈ E
    · rw [iInf_prod_one_sub_eq_zero (fun i => h (ω (i + 1))) (fun i => h1 _) hω]
      exact zero_le
    · rw [indicator_of_mem (show ω ∈ Eᶜ from hω), Pi.one_apply]
      exact (iInf_le _ 0).trans (by simp)
  have he := genL_add_lintegral_iInf P hh h1 x
  rw [prob_compl_eq_one_sub hE] at hle
  have hfin : ∫⁻ ω, ⨅ n, ∏ i ∈ Finset.range n, (1 - h (ω (i + 1))) ∂pathKernel P x ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_le_of_eq le_add_self he)
  rw [ENNReal.eq_sub_of_add_eq hfin he]
  calc genQ P h x = 1 - (1 - pathKernel P x E) :=
        (ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one).symm
    _ ≤ _ := tsub_le_tsub_left hle 1

/-- **Theorem 12.2.2 (iii)** (MT p. 296): if `h ≤ e < 1`, then `L(x, h) = 1` iff `Q(x, h) = 1`.
If `L(x, h) = 1` then `∏ (1 − h(Φᵢ)) = 0` almost surely, and with `h ≤ e` the product is at
least `exp(−Σ h(Φᵢ)/(1 − e))`, so `Σ h(Φᵢ) = ∞` almost surely. -/
theorem theorem_12_2_2_iii (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) {e : ℝ} (he : e < 1) (hhe : ∀ x, (h x).toReal ≤ e) (h1 : h ≤ 1)
    (x : X) : genL P h x = 1 ↔ genQ P h x = 1 := by
  have := isMarkovKernel_pathKernel P
  constructor
  · intro hL
    have hz := genL_add_lintegral_iInf P hh h1 x
    rw [hL] at hz
    have h0 : ∫⁻ ω, ⨅ n, ∏ i ∈ Finset.range n, (1 - h (ω (i + 1))) ∂pathKernel P x = 0 :=
      (ENNReal.add_right_inj ENNReal.one_ne_top).1 (hz.trans (add_zero 1).symm)
    have hmeas : Measurable fun ω : ℕ → X => ⨅ n, ∏ i ∈ Finset.range n, (1 - h (ω (i + 1))) :=
      Measurable.iInf fun n => Finset.measurable_prod _ fun i _ =>
        (show Measurable fun ω : ℕ → X => 1 - h (ω (i + 1)) from
          measurable_const.sub (hh.comp (measurable_pi_apply (i + 1))))
    have hae := (lintegral_eq_zero_iff hmeas).1 h0
    set E := {ω : ℕ → X | ∑' i, h (ω (i + 1)) = ∞}
    have hE : MeasurableSet E :=
      (Measurable.tsum fun i => hh.comp (measurable_pi_apply (i + 1)))
        (measurableSet_singleton ∞)
    have hnull : pathKernel P x Eᶜ = 0 := by
      refine ae_iff.1 ?_
      filter_upwards [hae] with ω hω
      by_contra hωE
      exact (iInf_prod_one_sub_pos (fun i => h (ω (i + 1))) he (fun i => hhe _)
        (fun i => h1 _) hωE).ne' hω
    rw [prob_compl_eq_one_sub hE, tsub_eq_zero_iff_le] at hnull
    exact le_antisymm prob_le_one hnull
  · intro hQ
    exact le_antisymm (genL_le_one P hh h1 x) (hQ ▸ theorem_12_2_2_ii P hh h1 x)


/-! ### Theorem 12.2.3 -/

/-- `Σₖ (P I_w)ᵏ φ = φ + Σₖ (P I_w)ᵏ (P I_w φ)`. -/
theorem geomOp_eq' {φ : X → ℝ≥0∞} : geomOp P w φ = φ + geomOp P w (killOp P w φ) := by
  ext x
  rw [Pi.add_apply, geomOp, tsum_eq_zero_add' ENNReal.summable, Function.iterate_zero, id_eq]
  rfl

/-- `(P I_{1−h})ᵏ P f = P (I_{1−h} P)ᵏ f`. -/
theorem iterate_killOp_kfun (P : Kernel X X) (h f : X → ℝ≥0∞) (k : ℕ) :
    (killOp P (1 - h))^[k] (kfun P f) =
      kfun P ((fun u x => (1 - h x) * kfun P u x)^[k] f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    rfl

/-- `∫ f d(U_h ∘ μ I_h) = ∫ h U_h f dμ`. -/
theorem lintegral_genPotKernel_comp_withDensity (P : Kernel X X) [IsFiniteKernel P]
    {h : X → ℝ≥0∞} (hh : Measurable h) (μ : Measure X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(genPotKernel P h ∘ₘ μ.withDensity h) =
      ∫⁻ x, h x * ∫⁻ y, f y ∂genPotKernel P h x ∂μ := by
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hh hf.lintegral_kernel]
  rfl

/-- For a subinvariant `μ`, `∫ Pu dμ ≤ ∫ u dμ`. -/
theorem IsSubinvariant.lintegral_kfun_le {μ : Measure X} (hsub : IsSubinvariant P μ)
    {u : X → ℝ≥0∞} (hu : Measurable u) : ∫⁻ x, kfun P u x ∂μ ≤ ∫⁻ x, u x ∂μ := by
  rw [lintegral_kfun μ P hu]
  exact lintegral_mono' hsub le_rfl

/-- `∫ v dμ = ∫ h v dμ + ∫ (1 − h) v dμ` for `h ≤ 1`. -/
theorem lintegral_eq_mul_add_one_sub_mul {μ : Measure X} {h : X → ℝ≥0∞} (hh : Measurable h)
    (h1 : h ≤ 1)
    {v : X → ℝ≥0∞} (hv : Measurable v) :
    ∫⁻ x, v x ∂μ = ∫⁻ x, h x * v x ∂μ + ∫⁻ x, (1 - h x) * v x ∂μ := by
  rw [← lintegral_add_left (f := fun x => h x * v x) (hh.mul hv)]
  refine lintegral_congr fun x => ?_
  rw [← add_mul, add_tsub_cancel_of_le (show h x ≤ 1 from h1 x), one_mul]


/-- `U_h f = Σₖ P (I_{1−h} P)ᵏ f`, written with the operator `u ↦ (1 − h) Pu`. -/
theorem lintegral_genPotKernel_eq_tsum (P : Kernel X X) [IsFiniteKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (x : X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂genPotKernel P h x =
      ∑' k, kfun P ((fun u x => (1 - h x) * kfun P u x)^[k] f) x := by
  rw [lintegral_genPotKernel P hh x hf, geomOp]
  simp_rw [iterate_killOp_kfun]

/-- `(I_{1−h} P)ᵏ f` is measurable. -/
theorem measurable_iterate_killKfun (P : Kernel X X) [IsSFiniteKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (k : ℕ) {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable ((fun u x => (1 - h x) * kfun P u x)^[k] f) := by
  induction k generalizing f with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih ((measurable_const.sub hh).mul (measurable_kfun P hf))

/-- **The minimality step** of Theorem 12.2.3 (i) (the analogue of Proposition 10.4.6): for a
subinvariant `μ`, `μ I_h U_h ≤ μ`, i.e. `∫ h U_h f dμ ≤ ∫ f dμ`. Iterating `μ ≥ μP = μ I_h P +
μ I_{1−h} P` gives `μ ≥ Σ_{k<n} μ I_h P (I_{1−h} P)ᵏ + μ (I_{1−h} P)ⁿ`. -/
theorem lintegral_mul_genPot_le (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (h1 : h ≤ 1) {μ : Measure X} (hsub : IsSubinvariant P μ)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, h x * ∫⁻ y, f y ∂genPotKernel P h x ∂μ ≤ ∫⁻ x, f x ∂μ := by
  set B : (X → ℝ≥0∞) → X → ℝ≥0∞ := fun u x => (1 - h x) * kfun P u x
  have hBm : ∀ k, Measurable (B^[k] f) := fun k => measurable_iterate_killKfun P hh k hf
  have hE : ∀ n, ∑ k ∈ Finset.range n, ∫⁻ x, h x * kfun P (B^[k] f) x ∂μ +
      ∫⁻ x, B^[n] f x ∂μ ≤ ∫⁻ x, f x ∂μ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Function.iterate_succ_apply', add_assoc]
      calc ∑ k ∈ Finset.range n, ∫⁻ x, h x * kfun P (B^[k] f) x ∂μ +
            (∫⁻ x, h x * kfun P (B^[n] f) x ∂μ + ∫⁻ x, B (B^[n] f) x ∂μ)
          = ∑ k ∈ Finset.range n, ∫⁻ x, h x * kfun P (B^[k] f) x ∂μ +
            ∫⁻ x, kfun P (B^[n] f) x ∂μ := by
            rw [lintegral_eq_mul_add_one_sub_mul hh h1 (measurable_kfun P (hBm n))]
        _ ≤ ∑ k ∈ Finset.range n, ∫⁻ x, h x * kfun P (B^[k] f) x ∂μ +
            ∫⁻ x, B^[n] f x ∂μ := add_le_add le_rfl (hsub.lintegral_kfun_le (hBm n))
        _ ≤ ∫⁻ x, f x ∂μ := ih
  simp_rw [lintegral_genPotKernel_eq_tsum P hh _ hf, ← ENNReal.tsum_mul_left]
  rw [lintegral_tsum (f := fun k x => h x * kfun P ((fun u x => (1 - h x) * kfun P u x)^[k] f) x)
    fun k => (hh.mul (measurable_kfun P (hBm k))).aemeasurable]
  exact ENNReal.tsum_le_of_sum_range_le fun n => le_self_add.trans (hE n)

/-- `∫ h U_h h dμ = ∫ h dμ` when `L ≡ 1`. -/
theorem lintegral_mul_genL (P : Kernel X X) [IsFiniteKernel P] {h : X → ℝ≥0∞}
    (hL : ∀ x, genL P h x = 1) (μ : Measure X) :
    ∫⁻ x, h x * ∫⁻ y, h y ∂genPotKernel P h x ∂μ = ∫⁻ x, h x ∂μ := by
  refine lintegral_congr fun x => ?_
  change h x * genL P h x = h x
  rw [hL x, mul_one]

/-- `(P I_{1−h})ᵏ P h ≤ Pᵏ⁺¹ h`. -/
theorem iterate_killOp_le_pow (P : Kernel X X) {h : X → ℝ≥0∞} (hh : Measurable h) (k : ℕ) :
    (killOp P (1 - h))^[k] (kfun P h) ≤ kfun (P ^ (k + 1)) h := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', kfun_pow_succ P (k + 1) hh]
    intro x
    calc killOp P (1 - h) ((killOp P (1 - h))^[k] (kfun P h)) x
        ≤ kfun P ((killOp P (1 - h))^[k] (kfun P h)) x :=
          lintegral_mono fun y => mul_le_of_le_one_left' tsub_le_self
      _ ≤ kfun P (kfun (P ^ (k + 1)) h) x := kfun_mono P ih x


/-- `K_{1/2}(x, h) = ∫ h dK_{1/2}(x)`, the function defining the sets `C_ε` of Theorem 12.2.3. -/
noncomputable def resolventH (P : Kernel X X) (h : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∫⁻ y, h y ∂resolvent P 2⁻¹ x

/-- `∫ u dK_ε(x) = Σₙ (1 − ε) εⁿ ∫ u dPⁿ(x)`. -/
theorem lintegral_resolvent (P : Kernel X X) (ε : ℝ≥0∞) (x : X) (u : X → ℝ≥0∞) :
    ∫⁻ y, u y ∂resolvent P ε x = ∑' n, (1 - ε) * ε ^ n * ∫⁻ y, u y ∂(P ^ n) x := by
  change ∫⁻ y, u y ∂(Measure.sum fun n => ((1 - ε) * ε ^ n) • (P ^ n) x) = _
  rw [lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul]

/-- If `L(x, h) > 0` then `K_{1/2}(x, h) > 0` (MT p. 297: the sets `C_ε` cover `X`). -/
theorem resolventH_pos (P : Kernel X X) [IsFiniteKernel P] {h : X → ℝ≥0∞} (hh : Measurable h)
    {x : X} (hL : genL P h x ≠ 0) : 0 < resolventH P h x := by
  rw [genL, lintegral_genPotKernel P hh x hh, geomOp] at hL
  obtain ⟨k, hk⟩ : ∃ k, (killOp P (1 - h))^[k] (kfun P h) x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hL (ENNReal.tsum_eq_zero.2 hc)
  have h1 : kfun (P ^ (k + 1)) h x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hk) (iterate_killOp_le_pow P hh k x))
  rw [resolventH, lintegral_resolvent]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum (k + 1))
  refine ENNReal.mul_pos (ENNReal.mul_pos ?_ (by simp)).ne' h1
  rw [ENNReal.one_sub_inv_two]; simp

/-- `K_{1/2}(x, h) ≤ 1` for `h ≤ 1`. -/
theorem resolventH_le_one (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞} (h1 : h ≤ 1)
    (x : X) : resolventH P h x ≤ 1 := by
  have := isMarkovKernel_resolvent P (ε := 2⁻¹) (by simp)
  calc resolventH P h x ≤ ∫⁻ _, 1 ∂resolvent P 2⁻¹ x := lintegral_mono fun y => h1 y
    _ = 1 := by simp

/-- **Theorem 12.2.3 (i)** (MT p. 297), corrected: let `0 ≤ h ≤ 1` with `L(x, h) = 1` for every
`x` and let `μ` be subinvariant with `∫ h dμ < ∞`. Then `μ = μ I_h U_h`, i.e.
`μ(A) = ∫ μ(dx) h(x) U_h(x, A)`, and `μ` is invariant. The book assumes only that `μ` is
σ-finite; `theorem_12_2_3_i_counterexample` shows that the integrability of `h` cannot be
dropped. The proof: `ν = μ I_h U_h ≤ μ` (`lintegral_mul_genPot_le`), `ν(h) = μ(h) < ∞` forces
`ν I_h = μ I_h`, which makes `ν` invariant, and the strictly positive `K_{1/2} h` then gives
`ν = μ` (`eq_of_le_of_lintegral_le`). -/
theorem theorem_12_2_3_i (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞} (hh : Measurable h)
    (h1 : h ≤ 1) {μ : Measure X} (hsub : IsSubinvariant P μ) (hfin : ∫⁻ x, h x ∂μ ≠ ∞)
    (hL : ∀ x, genL P h x = 1) :
    genPotKernel P h ∘ₘ μ.withDensity h = μ ∧ IsInvariant P μ := by
  set ν := genPotKernel P h ∘ₘ μ.withDensity h
  have hν : ∀ f, Measurable f → ∫⁻ y, f y ∂ν = ∫⁻ x, h x * ∫⁻ y, f y ∂genPotKernel P h x ∂μ :=
    fun f hf => lintegral_genPotKernel_comp_withDensity P hh μ hf
  have hle : ν ≤ μ := Measure.le_iff.2 fun A hA => by
    rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
      hν _ (measurable_one.indicator hA)]
    exact lintegral_mul_genPot_le P hh h1 hsub (measurable_one.indicator hA)
  have hνh : ∫⁻ x, h x ∂ν = ∫⁻ x, h x ∂μ := by rw [hν h hh, lintegral_mul_genL P hL]
  have hwd : ν.withDensity h = μ.withDensity h := by
    ext A hA
    rw [withDensity_apply _ hA, withDensity_apply _ hA]
    refine eq_of_add_eq_of_le (lintegral_mono' (Measure.restrict_mono le_rfl hle) le_rfl)
      (lintegral_mono' (Measure.restrict_mono le_rfl hle) le_rfl) (b := ∫⁻ x in Aᶜ, h x ∂ν)
      (d := ∫⁻ x in Aᶜ, h x ∂μ) ?_ ?_
    · rw [lintegral_add_compl _ hA, lintegral_add_compl _ hA, hνh]
    · exact ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral _ _)
  have hhu : ∀ u, Measurable u → ∫⁻ x, h x * u x ∂ν = ∫⁻ x, h x * u x ∂μ := fun u hu => by
    have e1 := lintegral_withDensity_eq_lintegral_mul ν hh hu
    have e2 := lintegral_withDensity_eq_lintegral_mul μ hh hu
    simp only [Pi.mul_apply] at e1 e2
    rw [← e1, ← e2, hwd]
  have hkey : ∀ f, Measurable f → ∫⁻ x, kfun P f x ∂ν = ∫⁻ x, f x ∂ν := fun f hf => by
    set g : X → ℝ≥0∞ := fun y => (1 - h y) * kfun P f y
    have hg : Measurable g := (measurable_const.sub hh).mul (measurable_kfun P hf)
    have hU : ∀ x, ∫⁻ y, f y ∂genPotKernel P h x = kfun P f x + ∫⁻ y, g y ∂genPotKernel P h x :=
      fun x => by
        rw [lintegral_genPotKernel P hh x hf, lintegral_genPotKernel P hh x hg, geomOp_eq']
        rfl
    rw [hν f hf]
    simp_rw [hU, mul_add]
    rw [lintegral_add_left (f := fun x => h x * kfun P f x) (hh.mul (measurable_kfun P hf)),
      ← hν g hg,
      lintegral_eq_mul_add_one_sub_mul hh h1 (measurable_kfun P hf), hhu _ (measurable_kfun P hf)]
  have hinv : IsInvariant P ν := by
    ext A hA
    rw [measure_kernel_apply _ _ hA, ← lintegral_indicator_one hA]
    simp_rw [← kfun_indicator P hA]
    exact hkey _ (measurable_one.indicator hA)
  have hKν := hinv.resolvent (ε := 2⁻¹) (by simp)
  have hKμ := hsub.resolvent (ε := 2⁻¹) (by simp)
  have hint : ∫⁻ x, resolventH P h x ∂μ ≤ ∫⁻ x, resolventH P h x ∂ν := by
    change ∫⁻ x, kfun (resolvent P 2⁻¹) h x ∂μ ≤ ∫⁻ x, kfun (resolvent P 2⁻¹) h x ∂ν
    rw [lintegral_kfun μ _ hh, lintegral_kfun ν _ hh]
    unfold IsInvariant at hKν
    rw [hKν, hνh]
    exact lintegral_mono' hKμ le_rfl
  have heq : μ = ν := eq_of_le_of_lintegral_le hle hh.lintegral_kernel
    (fun x => (resolventH_pos P hh (by rw [hL x]; exact one_ne_zero)).ne')
    (fun x => ne_top_of_le_ne_top ENNReal.one_ne_top (resolventH_le_one P h1 x)) hint
    (by
      change ∫⁻ x, kfun (resolvent P 2⁻¹) h x ∂ν ≠ ∞
      rw [lintegral_kfun ν _ hh]
      unfold IsInvariant at hKν
      rw [hKν, hνh]; exact hfin)
  exact ⟨heq.symm, heq ▸ hinv⟩


/-- **Theorem 12.2.3 (i) fails for σ-finite `μ` with `∫ h dμ = ∞`** (MT p. 297). For the
successor chain on `ℕ`, `h ≡ 1` (so `U_h = P` and `L ≡ Q ≡ 1`), counting measure is σ-finite and
subinvariant but not invariant; the claimed representation `μ = μ I_h U_h = μP` fails at `{0}`. -/
theorem theorem_12_2_3_i_counterexample :
    ∃ _ : IsMarkovKernel succKernel,
      IsSubinvariant succKernel Measure.count ∧ SigmaFinite (Measure.count : Measure ℕ) ∧
      (∀ x, genL succKernel 1 x = 1) ∧ (∀ x, genQ succKernel 1 x = 1) ∧
      ¬ IsInvariant succKernel Measure.count := by
  have hM := isMarkovKernel_succKernel
  have hcomp : ∀ A : Set ℕ, (succKernel ∘ₘ Measure.count) A = ∑' x, A.indicator 1 (x + 1) :=
    fun A => by
      rw [measure_kernel_apply _ _ (MeasurableSet.of_discrete), lintegral_count]
      refine tsum_congr fun x => ?_
      have : succKernel x = Measure.dirac (x + 1) := Kernel.deterministic_apply _ _
      rw [this, Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
  refine ⟨hM, Measure.le_iff.2 fun A hA => ?_, inferInstance, fun x => ?_, fun x => ?_, ?_⟩
  · rw [hcomp, ← lintegral_indicator_one hA, lintegral_count]
    exact ENNReal.tsum_comp_le_tsum_of_injective (fun a b h => Nat.succ_injective h) _
  · rw [genL, genPotKernel_one]; simp
  · have huniv : {ω : ℕ → ℕ | ∑' i, (1 : ℕ → ℝ≥0∞) (ω (i + 1)) = ∞} = univ := by
      ext ω; simp
    have := isMarkovKernel_pathKernel succKernel
    rw [genQ, huniv, measure_univ]
  · intro h
    have h0 := congrArg (fun m : Measure ℕ => m {0}) h
    simp only [hcomp] at h0
    simp [indicator] at h0

/-- **Theorem 12.2.3 (ii)** (MT p. 297): if `ν` is invariant for `P_h = U_h I_h`, then
`μ = ν U_h` is invariant for `P`; the sets `C_ε = {x : K_{1/2}(x, h) ≥ ε}` have
`ε μ(C_ε) ≤ ν(X)`, and they cover `X` when `L(x, h) > 0` for every `x` (in particular when
`Q(x, h) = 1`, by Theorem 12.2.2 (ii)). The book's hypothesis "`ν(B) = νU_hI_h(B)` for `B ⊆ A`"
is read as invariance of `ν` for `P_h`, the form used in Theorem 12.3.2; finiteness of `ν` is
needed only for the σ-finiteness of `μ`. -/
theorem theorem_12_2_3_ii (P : Kernel X X) [IsMarkovKernel P] {h : X → ℝ≥0∞}
    (hh : Measurable h) (h1 : h ≤ 1) {ν : Measure X} (hν : balayage P h ∘ₘ ν = ν) :
    IsInvariant P (genPotKernel P h ∘ₘ ν) ∧
      (∀ ε : ℝ≥0∞, ε * (genPotKernel P h ∘ₘ ν) {x | ε ≤ resolventH P h x} ≤ ν univ) ∧
      ((∀ x, genL P h x ≠ 0) → ∀ x, 0 < resolventH P h x) := by
  set μ := genPotKernel P h ∘ₘ ν
  have hμ : ∀ f, Measurable f → ∫⁻ y, f y ∂μ = ∫⁻ x, ∫⁻ y, f y ∂genPotKernel P h x ∂ν :=
    fun f hf => Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable
  have hhu : ∀ u, Measurable u → ∫⁻ x, h x * u x ∂μ = ∫⁻ x, u x ∂ν := fun u hu => by
    rw [hμ (fun x => h x * u x) (hh.mul hu)]
    simp_rw [← lintegral_genPotDensity P h hh _ hu]
    conv_rhs => rw [← hν]
    exact (Measure.lintegral_bind (Kernel.aemeasurable _) hu.aemeasurable).symm
  have hkey : ∀ f, Measurable f → ∫⁻ x, kfun P f x ∂μ = ∫⁻ x, f x ∂μ := fun f hf => by
    set g : X → ℝ≥0∞ := fun y => (1 - h y) * kfun P f y
    have hg : Measurable g := (measurable_const.sub hh).mul (measurable_kfun P hf)
    have hU : ∀ x, ∫⁻ y, f y ∂genPotKernel P h x = kfun P f x + ∫⁻ y, g y ∂genPotKernel P h x :=
      fun x => by
        rw [lintegral_genPotKernel P hh x hf, lintegral_genPotKernel P hh x hg, geomOp_eq']
        rfl
    rw [hμ f hf]
    simp_rw [hU]
    rw [lintegral_add_left (f := fun x => kfun P f x) (measurable_kfun P hf), ← hμ g hg,
      lintegral_eq_mul_add_one_sub_mul hh h1 (measurable_kfun P hf), hhu _ (measurable_kfun P hf)]
  have hinv : IsInvariant P μ := by
    ext A hA
    rw [measure_kernel_apply _ _ hA, ← lintegral_indicator_one hA]
    simp_rw [← kfun_indicator P hA]
    exact hkey _ (measurable_one.indicator hA)
  refine ⟨hinv, fun ε => ?_, fun hL x => resolventH_pos P hh (hL x)⟩
  have hKμ := hinv.resolvent (ε := 2⁻¹) (by simp)
  calc ε * μ {x | ε ≤ resolventH P h x} ≤ ∫⁻ x, resolventH P h x ∂μ :=
        mul_meas_ge_le_lintegral hh.lintegral_kernel ε
    _ = ∫⁻ x, h x ∂μ := by
        change ∫⁻ x, kfun (resolvent P 2⁻¹) h x ∂μ = _
        rw [lintegral_kfun μ _ hh]
        unfold IsInvariant at hKμ
        rw [hKμ]
    _ = ∫⁻ x, genL P h x ∂ν := hμ h hh
    _ ≤ ∫⁻ _, 1 ∂ν := lintegral_mono fun x => genL_le_one P hh h1 x
    _ = ν univ := lintegral_one

end MeynTweedie.InvarianceTightness

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.SearchValue

/-!
# An equilibrium search economy: invariant measures (SLP §13.8)

SLP §13.8, pp. 409–411, Exercise 13.8d and the [Derived] facts and NOTEs about it, and
Exercise 13.8f.

* The state space `X × Z` is the rectangle `[(0, z̲), (x̄, z̄)] ⊆ ℝ × ℝ` (`searchToR`,
  `searchOfR`). `searchKernel`: the transition function `P(s, A × B) = 1{G(s) ∈ A} Q(z, B)` of a
  law of motion `G` (Theorem 9.13); it is monotone (`isMonotoneTF_searchKernel`) and Feller
  (`isFeller_searchKernel`, Theorem 9.14) when `G` is; its `z`-marginals are `Qⁿ`
  (`kpow_searchKernel_snd`).
* `SearchMixing`: condition (2) of §13.4. With `Q` monotone and Feller it gives positive one-step
  probabilities near the endpoints (`exists_searchQ_pos_upper`, `_lower`), and
  `searchKernel_assumption`/`searchKernel_unique`: Assumption 12.1 for `P` (in `N + 1` steps,
  mixing point `(c_x, (z̲ + z̄)/2)`), hence Theorem 12.12 (`theorem_12_12_prod`).
  `searchQ_unique`: `Q` itself has a unique invariant measure `μ`.
* `searchW`, `SearchAssumption6`: the no-migration value `w` and assumption (6) (p. 410).
  `searchNoCaseB`: under (6) no `x ∈ [0, x̄)` is in Case B at both `z̲` and `z̄` (the manual's
  argument `v(x, ·) = w(x, ·)` made valid: such an `x` is in Case B at every `z`).
* `searchP`, `ex_13_8d_process` (pp. 409–410): `P` is a monotone Feller transition function with
  an invariant measure (Theorem 12.10).
* `searchThetaBar` `θ̄ = f(0, z̄)/(1 − β)`; `ex_13_8d_seven_iff`: (7) `v ≡ θ` holds iff `θ ≥ θ̄`;
  `ex_13_8d_seven`: then `g ≡ 0`; `ex_13_8d_large`: and (with mixing) the unique invariant
  measure is `δ₀ × μ`.
* **`ex_13_8d`** (p. 410): under (6) and mixing, for **every** `θ > 0`, `P` has a unique invariant
  measure `λ_θ` and `T*ⁿλ₀ ⇒ λ_θ` for all `λ₀`. If Case C occurs, `g_A(z̲) < g_C(z̄)` by (6) and the
  mixing point is interior; if Case C never occurs, `0` is absorbing near `z̲` by (6)
  (`ex_13_8d_caseA_zlo`) and the mixing point is the corner `c_x = 0`.
* `searchD` (p. 411): `D(θ) = ∫ x λ_θ(dx × dz)`; `searchD_mem`: `0 ≤ D ≤ x̄`.
* **`ex_13_8f_zero`**, **`ex_13_8f_large`** (Ex. 13.8f, p. 411): `D(0) = x̄` (at `θ = 0`, `g ≡ x̄`,
  `searchG_theta_zero`) and `D(θ) = 0` for `θ ≥ θ̄`; `ex_13_8d_delta`: under (6), for `θ ≥ βθ̄`,
  `λ_θ = δ₀ × μ` and `D(θ) = 0`.

**Corrections.**
* (NOTE p. 410, hint of Ex. 13.8d) "(2a) and (2c) each hold on some region for every
  `θ ∈ (0, θ̄)`" is false: for `θ ≥ βθ̄`, `β∫v dQ ≤ β(f(0, z̄) + θ) ≤ θ`, so Case C never occurs
  (`ex_13_8d_noCaseC`); since `θ̄ > 0`, `[βθ̄, θ̄)` is never empty, so the hint fails in every
  instance of the model (`ex_13_8d_hint_counterexample`; a concrete instance is
  `ex_13_8d_hint_counterexample_concrete` in `SearchDemand`). Corrected:
  `ex_13_8d_hint_corrected` (Case A always occurs; Case C only for `θ < βθ̄`). The conclusion of
  Ex. 13.8d still holds there (`ex_13_8d`, `ex_13_8d_delta`).
* (hint of Ex. 13.8d) "(6) implies (7) for large `θ`": (6) is not needed (`ex_13_8d_seven`).
* (NOTE p. 411) `θ = 0` lies outside Ex. 13.8a,d (`θ > 0`) but is needed for Ex. 13.8f,g; it is
  covered here (`searchG_theta_zero`, `ex_13_8f_zero`).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

variable {zlo zhi xbar : ℝ}

/-! ### The state space as a rectangle -/

/-- `X × Z` as the rectangle `[(0, z̲), (x̄, z̄)] ⊆ ℝ × ℝ`. -/
def searchToR (p : Icc (0 : ℝ) xbar × Icc zlo zhi) : Icc ((0 : ℝ), zlo) (xbar, zhi) :=
  ⟨(p.1, p.2), ⟨p.1.2.1, p.2.2.1⟩, ⟨p.1.2.2, p.2.2.2⟩⟩

/-- The rectangle `[(0, z̲), (x̄, z̄)]` as `X × Z`. -/
def searchOfR (s : Icc ((0 : ℝ), zlo) (xbar, zhi)) : Icc (0 : ℝ) xbar × Icc zlo zhi :=
  (⟨s.1.1, s.2.1.1, s.2.2.1⟩, ⟨s.1.2, s.2.1.2, s.2.2.2⟩)

/-- `searchToR` is continuous. -/
theorem continuous_searchToR : Continuous (searchToR (zlo := zlo) (zhi := zhi) (xbar := xbar)) := by
  unfold searchToR; fun_prop

/-- `searchOfR` is continuous. -/
theorem continuous_searchOfR : Continuous (searchOfR (zlo := zlo) (zhi := zhi) (xbar := xbar)) := by
  unfold searchOfR; fun_prop

/-- `searchToR` is measurable. -/
theorem measurable_searchToR : Measurable (searchToR (zlo := zlo) (zhi := zhi) (xbar := xbar)) :=
  continuous_searchToR.measurable

/-- `searchOfR` is measurable. -/
theorem measurable_searchOfR : Measurable (searchOfR (zlo := zlo) (zhi := zhi) (xbar := xbar)) :=
  continuous_searchOfR.measurable

/-- `searchOfR` inverts `searchToR`. -/
theorem searchOfR_toR (p : Icc (0 : ℝ) xbar × Icc zlo zhi) : searchOfR (searchToR p) = p := rfl

/-- `searchToR` is monotone (coordinatewise order). -/
theorem searchToR_mono {p q : Icc (0 : ℝ) xbar × Icc zlo zhi} (h : p ≤ q) :
    searchToR p ≤ searchToR q :=
  ⟨h.1, h.2⟩

/-- `searchOfR` is monotone (coordinatewise order). -/
theorem searchOfR_mono {s t : Icc ((0 : ℝ), zlo) (xbar, zhi)} (h : s ≤ t) :
    searchOfR s ≤ searchOfR t :=
  ⟨h.1, h.2⟩

/-! ### The transition function `P((x, z), A × B) = 1{g(x, z) ∈ A} Q(z, B)` -/

/-- The transition function on `S = X × Z` of a law of motion `G : S → X` for the work force and
the shock kernel `Q` (Theorem 9.13): `P(s, ·)` is the law of `(G(s), z′)` with `z′ ~ Q(z, ·)`. -/
noncomputable def searchKernel (Q : Kernel (Icc zlo zhi) (Icc zlo zhi))
    (G : Icc ((0 : ℝ), zlo) (xbar, zhi) → Icc (0 : ℝ) xbar) (hG : Measurable G) :
    Kernel (Icc ((0 : ℝ), zlo) (xbar, zhi)) (Icc ((0 : ℝ), zlo) (xbar, zhi)) :=
  Kernel.map (Kernel.deterministic G hG ×ₖ
    Q.comap (fun s => (searchOfR s).2) (measurable_snd.comp measurable_searchOfR)) searchToR

variable (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) [IsMarkovKernel Q]
  {G : Icc ((0 : ℝ), zlo) (xbar, zhi) → Icc (0 : ℝ) xbar} (hG : Measurable G)

/-- `z′ ↦ (G(s), z′)` is measurable. -/
theorem measurable_searchSlice (s : Icc ((0 : ℝ), zlo) (xbar, zhi)) :
    Measurable fun z' : Icc zlo zhi => searchToR (G s, z') :=
  measurable_searchToR.comp measurable_prodMk_left

/-- `P(s, ·)` is the law of `(G(s), z′)` with `z′ ~ Q(z, ·)`. -/
theorem searchKernel_apply (s : Icc ((0 : ℝ), zlo) (xbar, zhi)) :
    searchKernel Q G hG s = (Q (searchOfR s).2).map fun z' => searchToR (G s, z') := by
  rw [searchKernel, Kernel.map_apply _ measurable_searchToR, Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.comap_apply, Measure.dirac_prod,
    Measure.map_map measurable_searchToR measurable_prodMk_left]
  rfl

/-- `P` is a transition function (Theorem 9.13). -/
theorem isMarkovKernel_searchKernel : IsMarkovKernel (searchKernel Q G hG) :=
  Kernel.IsMarkovKernel.map _ measurable_searchToR

/-- `(Tφ)(s) = ∫ φ(G(s), z′) Q(z, dz′)`. -/
theorem integral_searchKernel {φ : Icc ((0 : ℝ), zlo) (xbar, zhi) → ℝ} (hφ : Measurable φ)
    (s : Icc ((0 : ℝ), zlo) (xbar, zhi)) :
    ∫ s', φ s' ∂searchKernel Q G hG s = ∫ z', φ (searchToR (G s, z')) ∂Q (searchOfR s).2 := by
  rw [searchKernel_apply, integral_map (measurable_searchSlice s).aemeasurable
    hφ.aestronglyMeasurable]

/-- `P` is monotone when `G` is nondecreasing and `Q` is monotone. -/
theorem isMonotoneTF_searchKernel (hM : IsMonotoneTF Q) (hGm : Monotone G) :
    IsMonotoneTF (searchKernel Q G hG) := by
  intro φ hφ ⟨B, hB⟩ hmono s s' hss'
  simp only [markovOpR, integral_searchKernel Q hG hφ]
  have hb : ∀ t : Icc ((0 : ℝ), zlo) (xbar, zhi), ∀ z', |φ (searchToR (G t, z'))| ≤ B :=
    fun _ _ => hB _
  refine (integral_mono (integrable_of_bounded (hφ.comp (measurable_searchSlice s)) (hb s))
    (integrable_of_bounded (hφ.comp (measurable_searchSlice s')) (hb s'))
    fun z' => hmono (searchToR_mono ⟨hGm hss', le_rfl⟩)).trans ?_
  exact hM _ (hφ.comp (measurable_searchSlice s')) ⟨B, hb s'⟩
    (fun z₁ z₂ h => hmono (searchToR_mono ⟨le_rfl, h⟩)) (searchOfR_mono hss').2

/-- `P` is Feller when `G` is continuous and `Q` is Feller (Theorem 9.14). -/
theorem isFeller_searchKernel (hF : IsFeller Q) (hGc : Continuous G) :
    IsFeller (searchKernel Q G hG) := by
  intro φ hφ _
  have : markovOpR (searchKernel Q G hG) φ = fun s =>
      ∫ z', (mkOfCompact ⟨φ ∘ searchToR, hφ.comp continuous_searchToR⟩ :
        Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ) ((G s, (searchOfR s).2).1, z') ∂Q
          (G s, (searchOfR s).2).2 :=
    funext fun s => integral_searchKernel Q hG hφ.measurable s
  rw [this]
  exact (lemma_12_14_cont Q hF _).1.comp
    (hGc.prodMk (continuous_snd.comp continuous_searchOfR))

/-! ### Iterates of `P` -/

/-- The `z`-marginal of `Pⁿ(s, ·)` is `Qⁿ(z, ·)`. -/
theorem kpow_searchKernel_snd (n : ℕ) {B : Set (Icc zlo zhi)} (hB : MeasurableSet B)
    (s : Icc ((0 : ℝ), zlo) (xbar, zhi)) :
    kpow (searchKernel Q G hG) n s ((fun s' => (searchOfR s').2) ⁻¹' B) =
      kpow Q n (searchOfR s).2 B := by
  have hzm : Measurable fun s' : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s').2 :=
    measurable_snd.comp measurable_searchOfR
  induction n generalizing s with
  | zero =>
    simp only [kpow, Kernel.id_apply]
    rw [Measure.dirac_apply' _ (hzm hB), Measure.dirac_apply' _ hB]
    rfl
  | succ n ih =>
    simp only [kpow]
    rw [Kernel.comp_apply' _ _ _ (hzm hB), Kernel.comp_apply' _ _ _ hB]
    simp_rw [ih]
    have hm : Measurable fun b : Icc ((0 : ℝ), zlo) (xbar, zhi) => kpow Q n (searchOfR b).2 B :=
      (Kernel.measurable_coe _ hB).comp hzm
    rw [searchKernel_apply, lintegral_map hm (measurable_searchSlice s)]
    rfl

/-- One step of `P` from `s` with `G(s) ∈ A` lands in `A × B` with probability `Q(z, B)`. -/
theorem searchKernel_rect {A : Set (Icc (0 : ℝ) xbar)} {B : Set (Icc zlo zhi)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (s : Icc ((0 : ℝ), zlo) (xbar, zhi))
    (hs : G s ∈ A) :
    searchKernel Q G hG s ((fun s' => (searchOfR s').1) ⁻¹' A ∩ (fun s' => (searchOfR s').2) ⁻¹' B)
      = Q (searchOfR s).2 B := by
  have hm : MeasurableSet ((fun s' : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s').1) ⁻¹' A ∩
      (fun s' : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s').2) ⁻¹' B) :=
    ((measurable_fst.comp measurable_searchOfR) hA).inter
      ((measurable_snd.comp measurable_searchOfR) hB)
  rw [searchKernel_apply, Measure.map_apply (measurable_searchSlice s) hm]
  congr 1
  ext z'
  simp [searchOfR_toR, hs]

/-- Chapman–Kolmogorov lower bound: if `Pⁿ(s, A) ≥ ε₁` and `Pᵐ(s′, B) ≥ ε₂` on `A`, then
`Pⁿ⁺ᵐ(s, B) ≥ ε₁ε₂`. -/
theorem searchKpow_add_ge {S : Type*} [MeasurableSpace S] (κ : Kernel S S) [IsMarkovKernel κ]
    {n m : ℕ} {A B : Set S} (hA : MeasurableSet A) (hB : MeasurableSet B) {ε₁ ε₂ : ℝ} {s : S}
    (hε₁ : 0 ≤ ε₁) (h1 : ε₁ ≤ (kpow κ n s).real A)
    (h2 : ∀ s' ∈ A, ε₂ ≤ (kpow κ m s').real B) : ε₁ * ε₂ ≤ (kpow κ (n + m) s).real B := by
  have := ex_8_4a κ n
  have := ex_8_4a κ m
  have := ex_8_4a κ (n + m)
  have e1 : ENNReal.ofReal ε₁ ≤ kpow κ n s A :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 h1
  have e2 : ∀ s' ∈ A, ENNReal.ofReal ε₂ ≤ kpow κ m s' B := fun s' hs' =>
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 (h2 s' hs')
  have key : ENNReal.ofReal ε₁ * ENNReal.ofReal ε₂ ≤ kpow κ (n + m) s B := by
    rw [kpow_add, Kernel.comp_apply' _ _ _ hB]
    calc ENNReal.ofReal ε₁ * ENNReal.ofReal ε₂ ≤ kpow κ n s A * ENNReal.ofReal ε₂ :=
          mul_le_mul_left e1 _
      _ = ∫⁻ s', A.indicator (fun _ => ENNReal.ofReal ε₂) s' ∂kpow κ n s := by
          rw [lintegral_indicator_const hA, mul_comm]
      _ ≤ ∫⁻ s', kpow κ m s' B ∂kpow κ n s := lintegral_mono fun s' => by
          by_cases hs : s' ∈ A
          · rw [indicator_of_mem hs]; exact e2 s' hs
          · rw [indicator_of_notMem hs]; exact zero_le
  rw [← ENNReal.ofReal_mul hε₁] at key
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 key

/-- A monotone `Q` gives more mass to an upper set from a higher state. -/
theorem searchQ_upper_mono (hM : IsMonotoneTF Q) {U : Set (Icc zlo zhi)}
    (hU : MeasurableSet U) (hup : IsUpperSet U) {z z' : Icc zlo zhi} (h : z ≤ z') :
    (Q z).real U ≤ (Q z').real U :=
  ((ex_12_11 Q).2.1 hM z' z h).real_le hU hup

/-- A monotone `Q` gives more mass to a lower set from a lower state. -/
theorem searchQ_lower_mono (hM : IsMonotoneTF Q) {L : Set (Icc zlo zhi)}
    (hL : MeasurableSet L) (hlow : IsLowerSet L) {z z' : Icc zlo zhi} (h : z ≤ z') :
    (Q z').real L ≤ (Q z).real L := by
  have := searchQ_upper_mono Q hM hL.compl hlow.compl h
  rw [probReal_compl_eq_one_sub hL, probReal_compl_eq_one_sub hL] at this
  linarith

/-- For `N ≥ 1` and an upper set `U`, `Qᴺ(z, U) ≤ Q(z̄, U)`. -/
theorem searchKpow_upper_le (hM : IsMonotoneTF Q) (hz : zlo ≤ zhi) {N : ℕ} (hN : 1 ≤ N)
    {U : Set (Icc zlo zhi)} (hU : MeasurableSet U) (hup : IsUpperSet U) (z : Icc zlo zhi) :
    (kpow Q N z).real U ≤ (Q ⟨zhi, hz, le_rfl⟩).real U := by
  have := ex_8_4a Q (N - 1)
  have := ex_8_4a Q N
  have key : kpow Q N z U ≤ Q ⟨zhi, hz, le_rfl⟩ U := by
    rw [show N = (N - 1) + 1 by omega, kpow_add, kpow_one, Kernel.comp_apply' _ _ _ hU]
    calc ∫⁻ z', Q z' U ∂kpow Q (N - 1) z ≤ ∫⁻ _, Q ⟨zhi, hz, le_rfl⟩ U ∂kpow Q (N - 1) z :=
          lintegral_mono fun z' => (ENNReal.toReal_le_toReal (measure_ne_top _ _)
            (measure_ne_top _ _)).1 (searchQ_upper_mono Q hM hU hup z'.2.2)
      _ = Q ⟨zhi, hz, le_rfl⟩ U := by rw [lintegral_const, measure_univ, mul_one]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 key

/-- For `N ≥ 1` and a lower set `L`, `Qᴺ(z, L) ≤ Q(z̲, L)`. -/
theorem searchKpow_lower_le (hM : IsMonotoneTF Q) (hz : zlo ≤ zhi) {N : ℕ} (hN : 1 ≤ N)
    {L : Set (Icc zlo zhi)} (hL : MeasurableSet L) (hlow : IsLowerSet L) (z : Icc zlo zhi) :
    (kpow Q N z).real L ≤ (Q ⟨zlo, le_rfl, hz⟩).real L := by
  have := ex_8_4a Q (N - 1)
  have := ex_8_4a Q N
  have key : kpow Q N z L ≤ Q ⟨zlo, le_rfl, hz⟩ L := by
    rw [show N = (N - 1) + 1 by omega, kpow_add, kpow_one, Kernel.comp_apply' _ _ _ hL]
    calc ∫⁻ z', Q z' L ∂kpow Q (N - 1) z ≤ ∫⁻ _, Q ⟨zlo, le_rfl, hz⟩ L ∂kpow Q (N - 1) z :=
          lintegral_mono fun z' => (ENNReal.toReal_le_toReal (measure_ne_top _ _)
            (measure_ne_top _ _)).1 (searchQ_lower_mono Q hM hL hlow z'.2.1)
      _ = Q ⟨zlo, le_rfl, hz⟩ L := by rw [lintegral_const, measure_univ, mul_one]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 key

/-- The mixing condition (2) of §13.4: `Qᴺ(z, (a, b]) ≥ α(b − a)` for all `z` and
`z̲ ≤ a ≤ b ≤ z̄`, with `N ≥ 1`, `α > 0`. -/
def SearchMixing (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) (N : ℕ) (α : ℝ) : Prop :=
  1 ≤ N ∧ 0 < α ∧ ∀ (z : Icc zlo zhi) (a b : ℝ), zlo ≤ a → a ≤ b → b ≤ zhi →
    α * (b - a) ≤ (kpow Q N z).real {z' | a < (z' : ℝ) ∧ (z' : ℝ) ≤ b}
/-- Monotone + Feller + mixing: from states close to `z̄`, `Q` reaches `(c, z̄]` in one step with
positive probability. (Mixing gives `Q(z̄, (c′, z̄]) ≥ Qᴺ(z̄, (c′, z̄]) > 0`; the Feller property
spreads this to a neighbourhood of `z̄`.) -/
theorem exists_searchQ_pos_upper (hzlt : zlo < zhi) (hF : IsFeller Q) (hM : IsMonotoneTF Q)
    {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α) {c : ℝ} (hc : c < zhi) :
    ∃ z₁ : Icc zlo zhi, (z₁ : ℝ) < zhi ∧ 0 < (Q z₁).real {z' | c < (z' : ℝ)} := by
  set a := max c zlo
  have ha : a < zhi := max_lt hc hzlt
  set c' := (a + zhi) / 2
  have hac' : a < c' := by simp only [c']; linarith
  have hc'z : c' < zhi := by simp only [c']; linarith
  have hcc' : c < c' := (le_max_left c zlo).trans_lt hac'
  have hzc' : zlo ≤ c' := (le_max_right c zlo).trans hac'.le
  set top : Icc zlo zhi := ⟨zhi, hzlt.le, le_rfl⟩
  have hU : ∀ d : ℝ, MeasurableSet {z' : Icc zlo zhi | d < (z' : ℝ)} := fun d =>
    measurableSet_lt measurable_const measurable_subtype_coe
  have hup : IsUpperSet {z' : Icc zlo zhi | c' < (z' : ℝ)} :=
    fun x y (hxy : x ≤ y) (hx : c' < (x : ℝ)) => show c' < (y : ℝ) from lt_of_lt_of_le hx hxy
  have h1 : 0 < (Q top).real {z' : Icc zlo zhi | c' < (z' : ℝ)} := by
    have hm := hmix.2.2 top c' zhi hzc' hc'z.le le_rfl
    have := ex_8_4a Q N
    have h2 := measureReal_mono (μ := kpow Q N top)
      (show {z' : Icc zlo zhi | c' < (z' : ℝ) ∧ (z' : ℝ) ≤ zhi} ⊆ {z' | c' < (z' : ℝ)} from
        fun _ h => h.1)
    have h3 := searchKpow_upper_le Q hM hzlt.le hmix.1 (hU c') hup top
    nlinarith [mul_pos hmix.2.1 (sub_pos.2 hc'z)]
  set φ : Icc zlo zhi → ℝ := fun z' => min 1 (max 0 (((z' : ℝ) - c) / (c' - c)))
  have hφc : Continuous φ := by fun_prop
  have hφ0 : ∀ z', 0 ≤ φ z' := fun _ => le_min zero_le_one (le_max_left _ _)
  have hφb : ∀ z', |φ z'| ≤ 1 := fun z' => by
    rw [abs_of_nonneg (hφ0 z')]; exact min_le_left _ _
  have hint : ∀ z, Integrable φ (Q z) := fun _ => integrable_of_bounded hφc.measurable hφb
  have hlowφ : ∀ z', {z' : Icc zlo zhi | c' < (z' : ℝ)}.indicator 1 z' ≤ φ z' := fun z' => by
    by_cases h : c' < (z' : ℝ)
    · rw [indicator_of_mem (show z' ∈ {z' : Icc zlo zhi | c' < (z' : ℝ)} from h)]
      have : 1 ≤ ((z' : ℝ) - c) / (c' - c) := by
        rw [le_div_iff₀ (sub_pos.2 hcc')]; linarith
      simp only [φ, Pi.one_apply]
      rw [max_eq_right (by linarith), min_eq_left this]
    · rw [indicator_of_notMem (show z' ∉ {z' : Icc zlo zhi | c' < (z' : ℝ)} from h)]
      exact hφ0 z'
  have hupφ : ∀ z', φ z' ≤ {z' : Icc zlo zhi | c < (z' : ℝ)}.indicator 1 z' := fun z' => by
    by_cases h : c < (z' : ℝ)
    · rw [indicator_of_mem (show z' ∈ {z' : Icc zlo zhi | c < (z' : ℝ)} from h)]
      exact min_le_left _ _
    · rw [indicator_of_notMem (show z' ∉ {z' : Icc zlo zhi | c < (z' : ℝ)} from h)]
      have : ((z' : ℝ) - c) / (c' - c) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.1 h]) (sub_pos.2 hcc').le
      simp only [φ]
      rw [max_eq_left this, min_eq_right zero_le_one]
  have hF0 : 0 < markovOpR Q φ top := by
    calc 0 < (Q top).real {z' : Icc zlo zhi | c' < (z' : ℝ)} := h1
      _ = ∫ z', {z' : Icc zlo zhi | c' < (z' : ℝ)}.indicator 1 z' ∂Q top :=
          (integral_indicator_one (hU c')).symm
      _ ≤ markovOpR Q φ top :=
          integral_mono ((integrable_const (1 : ℝ)).indicator (hU c')) (hint top) hlowφ
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (((hF φ hφc ⟨1, hφb⟩).tendsto top).eventually (lt_mem_nhds hF0))
  set z₁ : Icc zlo zhi := ⟨max zlo (zhi - δ / 2), le_max_left _ _,
    max_le hzlt.le (by linarith)⟩
  have hz₁ : (z₁ : ℝ) < zhi := max_lt hzlt (by linarith)
  have hd : dist z₁ top < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_lt_iff]
    constructor
    · change max zlo (zhi - δ / 2) - zhi < δ
      linarith
    · change zhi - max zlo (zhi - δ / 2) < δ
      linarith [le_max_right zlo (zhi - δ / 2)]
  refine ⟨z₁, hz₁, (hball hd).trans_le ?_⟩
  calc markovOpR Q φ z₁ ≤ ∫ z', {z' : Icc zlo zhi | c < (z' : ℝ)}.indicator 1 z' ∂Q z₁ :=
        integral_mono (hint z₁) ((integrable_const (1 : ℝ)).indicator (hU c)) hupφ
    _ = (Q z₁).real {z' : Icc zlo zhi | c < (z' : ℝ)} := integral_indicator_one (hU c)

/-- The mirror image of `exists_searchQ_pos_upper`: from states close to `z̲`, `Q` reaches
`[z̲, c)` in one step with positive probability. -/
theorem exists_searchQ_pos_lower (hzlt : zlo < zhi) (hF : IsFeller Q) (hM : IsMonotoneTF Q)
    {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α) {c : ℝ} (hc : zlo < c) :
    ∃ z₂ : Icc zlo zhi, zlo < (z₂ : ℝ) ∧ 0 < (Q z₂).real {z' | (z' : ℝ) < c} := by
  set b := min c zhi
  have hb : zlo < b := lt_min hc hzlt
  set c' := (zlo + b) / 2
  have hc'b : c' < b := by simp only [c']; linarith
  have hzc' : zlo < c' := by simp only [c']; linarith
  have hc'c : c' < c := hc'b.trans_le (min_le_left c zhi)
  have hc'z : c' ≤ zhi := hc'b.le.trans (min_le_right c zhi)
  set bot : Icc zlo zhi := ⟨zlo, le_rfl, hzlt.le⟩
  have hU : ∀ d : ℝ, MeasurableSet {z' : Icc zlo zhi | (z' : ℝ) < d} := fun d =>
    measurableSet_lt measurable_subtype_coe measurable_const
  have hL : MeasurableSet {z' : Icc zlo zhi | (z' : ℝ) ≤ c'} :=
    measurableSet_le measurable_subtype_coe measurable_const
  have hlow : IsLowerSet {z' : Icc zlo zhi | (z' : ℝ) ≤ c'} :=
    fun x y (hxy : y ≤ x) (hx : (x : ℝ) ≤ c') => show (y : ℝ) ≤ c' from le_trans hxy hx
  have h1 : 0 < (Q bot).real {z' : Icc zlo zhi | (z' : ℝ) ≤ c'} := by
    have hm := hmix.2.2 bot zlo c' le_rfl hzc'.le hc'z
    have := ex_8_4a Q N
    have h2 := measureReal_mono (μ := kpow Q N bot)
      (show {z' : Icc zlo zhi | zlo < (z' : ℝ) ∧ (z' : ℝ) ≤ c'} ⊆ {z' | (z' : ℝ) ≤ c'} from
        fun _ h => h.2)
    have h3 := searchKpow_lower_le Q hM hzlt.le hmix.1 hL hlow bot
    nlinarith [mul_pos hmix.2.1 (sub_pos.2 hzc')]
  set φ : Icc zlo zhi → ℝ := fun z' => min 1 (max 0 ((c - (z' : ℝ)) / (c - c')))
  have hφc : Continuous φ := by fun_prop
  have hφ0 : ∀ z', 0 ≤ φ z' := fun _ => le_min zero_le_one (le_max_left _ _)
  have hφb : ∀ z', |φ z'| ≤ 1 := fun z' => by
    rw [abs_of_nonneg (hφ0 z')]; exact min_le_left _ _
  have hint : ∀ z, Integrable φ (Q z) := fun _ => integrable_of_bounded hφc.measurable hφb
  have hlowφ : ∀ z', {z' : Icc zlo zhi | (z' : ℝ) ≤ c'}.indicator 1 z' ≤ φ z' := fun z' => by
    by_cases h : (z' : ℝ) ≤ c'
    · rw [indicator_of_mem (show z' ∈ {z' : Icc zlo zhi | (z' : ℝ) ≤ c'} from h)]
      have : 1 ≤ (c - (z' : ℝ)) / (c - c') := by
        rw [le_div_iff₀ (sub_pos.2 hc'c)]; linarith
      simp only [φ, Pi.one_apply]
      rw [max_eq_right (by linarith), min_eq_left this]
    · rw [indicator_of_notMem (show z' ∉ {z' : Icc zlo zhi | (z' : ℝ) ≤ c'} from h)]
      exact hφ0 z'
  have hupφ : ∀ z', φ z' ≤ {z' : Icc zlo zhi | (z' : ℝ) < c}.indicator 1 z' := fun z' => by
    by_cases h : (z' : ℝ) < c
    · rw [indicator_of_mem (show z' ∈ {z' : Icc zlo zhi | (z' : ℝ) < c} from h)]
      exact min_le_left _ _
    · rw [indicator_of_notMem (show z' ∉ {z' : Icc zlo zhi | (z' : ℝ) < c} from h)]
      have : (c - (z' : ℝ)) / (c - c') ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.1 h]) (sub_pos.2 hc'c).le
      simp only [φ]
      rw [max_eq_left this, min_eq_right zero_le_one]
  have hF0 : 0 < markovOpR Q φ bot := by
    calc 0 < (Q bot).real {z' : Icc zlo zhi | (z' : ℝ) ≤ c'} := h1
      _ = ∫ z', {z' : Icc zlo zhi | (z' : ℝ) ≤ c'}.indicator 1 z' ∂Q bot :=
          (integral_indicator_one hL).symm
      _ ≤ markovOpR Q φ bot :=
          integral_mono ((integrable_const (1 : ℝ)).indicator hL) (hint bot) hlowφ
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (((hF φ hφc ⟨1, hφb⟩).tendsto bot).eventually (lt_mem_nhds hF0))
  set z₂ : Icc zlo zhi := ⟨min zhi (zlo + δ / 2), le_min hzlt.le (by linarith),
    min_le_left _ _⟩
  have hz₂ : zlo < (z₂ : ℝ) := lt_min hzlt (by linarith)
  have hd : dist z₂ bot < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_lt_iff]
    constructor
    · change min zhi (zlo + δ / 2) - zlo < δ
      linarith [min_le_right zhi (zlo + δ / 2)]
    · change zlo - min zhi (zlo + δ / 2) < δ
      linarith
  refine ⟨z₂, hz₂, (hball hd).trans_le ?_⟩
  calc markovOpR Q φ z₂ ≤ ∫ z', {z' : Icc zlo zhi | (z' : ℝ) < c}.indicator 1 z' ∂Q z₂ :=
        integral_mono (hint z₂) ((integrable_const (1 : ℝ)).indicator (hU c)) hupφ
    _ = (Q z₂).real {z' : Icc zlo zhi | (z' : ℝ) < c} := integral_indicator_one (hU c)
omit [IsMarkovKernel Q] in
/-- A property holding near `z̲` holds at some `z > z̲`. -/
theorem exists_searchNear_bot (hzlt : zlo < zhi) {p : Icc zlo zhi → Prop}
    (h : ∀ᶠ z in 𝓝 (⟨zlo, le_rfl, hzlt.le⟩ : Icc zlo zhi), p z) :
    ∃ z : Icc zlo zhi, zlo < (z : ℝ) ∧ p z := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨⟨min zhi (zlo + δ / 2), le_min hzlt.le (by linarith), min_le_left _ _⟩,
    lt_min hzlt (by linarith), hball ?_⟩
  rw [Subtype.dist_eq, Real.dist_eq, abs_sub_lt_iff]
  constructor
  · change min zhi (zlo + δ / 2) - zlo < δ
    linarith [min_le_right zhi (zlo + δ / 2)]
  · change zlo - min zhi (zlo + δ / 2) < δ
    linarith [le_min hzlt.le (show zlo ≤ zlo + δ / 2 by linarith)]

omit [IsMarkovKernel Q] in
/-- A property holding near `z̄` holds at some `z < z̄`. -/
theorem exists_searchNear_top (hzlt : zlo < zhi) {p : Icc zlo zhi → Prop}
    (h : ∀ᶠ z in 𝓝 (⟨zhi, hzlt.le, le_rfl⟩ : Icc zlo zhi), p z) :
    ∃ z : Icc zlo zhi, (z : ℝ) < zhi ∧ p z := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨⟨max zlo (zhi - δ / 2), le_max_left _ _, max_le hzlt.le (by linarith)⟩,
    max_lt hzlt (by linarith), hball ?_⟩
  rw [Subtype.dist_eq, Real.dist_eq, abs_sub_lt_iff]
  constructor
  · change max zlo (zhi - δ / 2) - zhi < δ
    linarith [max_le hzlt.le (show zhi - δ / 2 ≤ zhi by linarith)]
  · change zhi - max zlo (zhi - δ / 2) < δ
    linarith [le_max_right zlo (zhi - δ / 2)]

/-- **Assumption 12.1 for `P`.** Suppose `G(s) ≤ c_x` whenever `z ≤ z₂` and `G(s) ≥ c_x` whenever
`z ≥ z₁`, with `z̲ < z₂`, `z₁ < z̄`. Then with `c = (c_x, (z̲ + z̄)/2)` and `N + 1` steps,
`Pᴺ⁺¹((0, z̲), [c, ·)) ≥ ε` and `Pᴺ⁺¹((x̄, z̄), (·, c]) ≥ ε` for some `ε > 0`: in `N` steps the
shock enters `[z₁, z̄]` (resp. `[z̲, z₂]`) with probability `≥ α(z̄ − z₁)` by mixing, and then
in one more step the work force passes `c_x` while the shock passes the midpoint. -/
theorem searchKernel_assumption (hzlt : zlo < zhi) (hF : IsFeller Q) (hM : IsMonotoneTF Q)
    {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α) (hab : ((0 : ℝ), zlo) ≤ (xbar, zhi))
    (cx : Icc (0 : ℝ) xbar) {z₁ z₂ : Icc zlo zhi} (hz₁ : (z₁ : ℝ) < zhi) (hz₂ : zlo < (z₂ : ℝ))
    (hlow : ∀ s, (searchOfR s).2 ≤ z₂ → G s ≤ cx)
    (hhigh : ∀ s, z₁ ≤ (searchOfR s).2 → cx ≤ G s) :
    ∃ (c : Icc ((0 : ℝ), zlo) (xbar, zhi)) (ε : ℝ), 0 < ε ∧
      ε ≤ (kpow (searchKernel Q G hG) (N + 1) ⟨((0 : ℝ), zlo), left_mem_Icc.2 hab⟩).real
        (Ici c) ∧
      ε ≤ (kpow (searchKernel Q G hG) (N + 1) ⟨(xbar, zhi), right_mem_Icc.2 hab⟩).real
        (Iic c) := by
  have := isMarkovKernel_searchKernel Q hG
  have := ex_8_4a (searchKernel Q G hG) N
  have := ex_8_4a Q N
  set cz : ℝ := (zlo + zhi) / 2
  set cZ : Icc zlo zhi := ⟨cz, by simp only [cz]; linarith, by simp only [cz]; linarith⟩
  set c : Icc ((0 : ℝ), zlo) (xbar, zhi) := searchToR (cx, cZ)
  obtain ⟨w₁, hw₁, hq₁⟩ := exists_searchQ_pos_upper Q hzlt hF hM hmix (c := cz)
    (by simp only [cz]; linarith)
  obtain ⟨w₂, hw₂, hq₂⟩ := exists_searchQ_pos_lower Q hzlt hF hM hmix (c := cz)
    (by simp only [cz]; linarith)
  set y₁ : Icc zlo zhi := max z₁ w₁
  set y₂ : Icc zlo zhi := min z₂ w₂
  have hy₁ : (y₁ : ℝ) < zhi := by
    rcases le_total z₁ w₁ with h | h
    · rw [show y₁ = w₁ from max_eq_right h]; exact hw₁
    · rw [show y₁ = z₁ from max_eq_left h]; exact hz₁
  have hy₂ : zlo < (y₂ : ℝ) := by
    rcases le_total z₂ w₂ with h | h
    · rw [show y₂ = z₂ from min_eq_left h]; exact hz₂
    · rw [show y₂ = w₂ from min_eq_right h]; exact hw₂
  have hzm : Measurable fun s' : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s').2 :=
    measurable_snd.comp measurable_searchOfR
  have hxm : Measurable fun s' : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s').1 :=
    measurable_fst.comp measurable_searchOfR
  set q₁ := (Q w₁).real {z' : Icc zlo zhi | cz < (z' : ℝ)}
  set q₂ := (Q w₂).real {z' : Icc zlo zhi | (z' : ℝ) < cz}
  -- from the bottom
  have hbot : α * (zhi - y₁) * q₁ ≤
      (kpow (searchKernel Q G hG) (N + 1) ⟨((0 : ℝ), zlo), left_mem_Icc.2 hab⟩).real (Ici c) := by
    refine searchKpow_add_ge _ (hzm (measurableSet_Ici (a := y₁))) measurableSet_Ici
      (mul_nonneg hmix.2.1.le (sub_pos.2 hy₁).le) ?_ fun s' hs' => ?_
    · rw [measureReal_def, kpow_searchKernel_snd Q hG N measurableSet_Ici, ← measureReal_def]
      exact (hmix.2.2 _ y₁ zhi y₁.2.1 hy₁.le le_rfl).trans
        (measureReal_mono fun z' h => le_of_lt h.1)
    · rw [kpow_one]
      have hs'' : y₁ ≤ (searchOfR s').2 := hs'
      have hrect := searchKernel_rect Q hG measurableSet_Ici (measurableSet_Ici (a := cZ)) s'
        (hhigh s' ((le_max_left z₁ w₁).trans hs''))
      have hsub : (fun s' => (searchOfR s').1) ⁻¹' Ici cx ∩
          (fun s' => (searchOfR s').2) ⁻¹' Ici cZ ⊆ Ici c := fun t ht => ⟨ht.1, ht.2⟩
      calc q₁ ≤ (Q (searchOfR s').2).real {z' : Icc zlo zhi | cz < (z' : ℝ)} :=
            searchQ_upper_mono Q hM (measurableSet_lt measurable_const measurable_subtype_coe)
              (fun x y (hxy : x ≤ y) (hx : cz < (x : ℝ)) => show cz < (y : ℝ) from
                lt_of_lt_of_le hx hxy) ((le_max_right z₁ w₁).trans hs'')
        _ ≤ (Q (searchOfR s').2).real (Ici cZ) :=
            measureReal_mono fun z' (h : cz < (z' : ℝ)) => show cz ≤ (z' : ℝ) from h.le
        _ = (searchKernel Q G hG s').real ((fun s' => (searchOfR s').1) ⁻¹' Ici cx ∩
              (fun s' => (searchOfR s').2) ⁻¹' Ici cZ) := by
            rw [measureReal_def, measureReal_def, hrect]
        _ ≤ (searchKernel Q G hG s').real (Ici c) := measureReal_mono hsub
  -- from the top
  have htop : α * (y₂ - zlo) * q₂ ≤
      (kpow (searchKernel Q G hG) (N + 1) ⟨(xbar, zhi), right_mem_Icc.2 hab⟩).real (Iic c) := by
    refine searchKpow_add_ge _ (hzm (measurableSet_Iic (a := y₂))) measurableSet_Iic
      (mul_nonneg hmix.2.1.le (sub_pos.2 hy₂).le) ?_ fun s' hs' => ?_
    · rw [measureReal_def, kpow_searchKernel_snd Q hG N measurableSet_Iic, ← measureReal_def]
      exact (hmix.2.2 _ zlo y₂ le_rfl hy₂.le y₂.2.2).trans
        (measureReal_mono fun z' h => h.2)
    · rw [kpow_one]
      have hs'' : (searchOfR s').2 ≤ y₂ := hs'
      have hrect := searchKernel_rect Q hG measurableSet_Iic (measurableSet_Iic (a := cZ)) s'
        (hlow s' (hs''.trans (min_le_left z₂ w₂)))
      have hsub : (fun s' => (searchOfR s').1) ⁻¹' Iic cx ∩
          (fun s' => (searchOfR s').2) ⁻¹' Iic cZ ⊆ Iic c := fun t ht => ⟨ht.1, ht.2⟩
      calc q₂ ≤ (Q (searchOfR s').2).real {z' : Icc zlo zhi | (z' : ℝ) < cz} :=
            searchQ_lower_mono Q hM (measurableSet_lt measurable_subtype_coe measurable_const)
              (fun x y (hxy : y ≤ x) (hx : (x : ℝ) < cz) => show (y : ℝ) < cz from
                lt_of_le_of_lt hxy hx) (hs''.trans (min_le_right z₂ w₂))
        _ ≤ (Q (searchOfR s').2).real (Iic cZ) :=
            measureReal_mono fun z' (h : (z' : ℝ) < cz) => show (z' : ℝ) ≤ cz from h.le
        _ = (searchKernel Q G hG s').real ((fun s' => (searchOfR s').1) ⁻¹' Iic cx ∩
              (fun s' => (searchOfR s').2) ⁻¹' Iic cZ) := by
            rw [measureReal_def, measureReal_def, hrect]
        _ ≤ (searchKernel Q G hG s').real (Iic c) := measureReal_mono hsub
  refine ⟨c, min (α * (zhi - y₁) * q₁) (α * (y₂ - zlo) * q₂), lt_min ?_ ?_,
    (min_le_left _ _).trans hbot, (min_le_right _ _).trans htop⟩
  · exact mul_pos (mul_pos hmix.2.1 (sub_pos.2 hy₁)) hq₁
  · exact mul_pos (mul_pos hmix.2.1 (sub_pos.2 hy₂)) hq₂

/-- **Theorem 12.12 for `P`**: under the hypotheses of `searchKernel_assumption`, with `G`
continuous and nondecreasing, `P` has a unique invariant probability measure and
`T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem searchKernel_unique (hzlt : zlo < zhi) (hF : IsFeller Q) (hM : IsMonotoneTF Q)
    {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α) (hab : ((0 : ℝ), zlo) ≤ (xbar, zhi))
    (hGm : Monotone G) (hGc : Continuous G)
    (cx : Icc (0 : ℝ) xbar) {z₁ z₂ : Icc zlo zhi} (hz₁ : (z₁ : ℝ) < zhi) (hz₂ : zlo < (z₂ : ℝ))
    (hlow : ∀ s, (searchOfR s).2 ≤ z₂ → G s ≤ cx)
    (hhigh : ∀ s, z₁ ≤ (searchOfR s).2 → cx ≤ G s) :
    ∃ μ : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)), IsProbabilityMeasure μ ∧
      adjointOp (searchKernel Q G hG) μ = μ ∧
      (∀ ν, IsProbabilityMeasure ν → adjointOp (searchKernel Q G hG) ν = ν → ν = μ) ∧
      ∀ lam₀, IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp (searchKernel Q G hG))^[n] lam₀) μ := by
  have := isMarkovKernel_searchKernel Q hG
  obtain ⟨c, ε, hε, hbot, htop⟩ :=
    searchKernel_assumption Q hG hzlt hF hM hmix hab cx hz₁ hz₂ hlow hhigh
  exact theorem_12_12_prod hab _ (isMonotoneTF_searchKernel Q hG hM hGm)
    (isFeller_searchKernel Q hG hF hGc) hε (by omega) hbot htop
/-! ### The search economy's transition function -/

variable {β θ : ℝ} {f : ℝ → ℝ → ℝ}

omit [IsMarkovKernel Q] in
/-- Bounded measurable solutions of `u(z) = a(z) + β ∫ u(z′) Q(z, dz′)` are unique. -/
theorem searchSection_unique [IsMarkovKernel Q] (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u₁ u₂ : Icc zlo zhi → ℝ} (hm₁ : Measurable u₁) (hm₂ : Measurable u₂) {M : ℝ}
    (hb₁ : ∀ z, |u₁ z| ≤ M) (hb₂ : ∀ z, |u₂ z| ≤ M) (a : Icc zlo zhi → ℝ)
    (h₁ : ∀ z, u₁ z = a z + β * ∫ z', u₁ z' ∂Q z)
    (h₂ : ∀ z, u₂ z = a z + β * ∫ z', u₂ z' ∂Q z) : u₁ = u₂ := by
  have key : ∀ n : ℕ, ∀ z, |u₁ z - u₂ z| ≤ β ^ n * (2 * M) := by
    intro n
    induction n with
    | zero =>
      intro z
      rw [pow_zero, one_mul]
      linarith [abs_sub (u₁ z) (u₂ z), hb₁ z, hb₂ z]
    | succ n ih =>
      intro z
      have e : u₁ z - u₂ z = β * ∫ z', (u₁ z' - u₂ z') ∂Q z := by
        rw [integral_sub (integrable_of_bounded hm₁ hb₁) (integrable_of_bounded hm₂ hb₂)]
        conv_lhs => rw [h₁ z, h₂ z]
        ring
      have hb := norm_integral_le_of_norm_le_const (μ := Q z) (C := β ^ n * (2 * M))
        (f := fun z' => u₁ z' - u₂ z') (Eventually.of_forall fun z' => by
          rw [Real.norm_eq_abs]; exact ih z')
      rw [probReal_univ, mul_one, Real.norm_eq_abs] at hb
      rw [e, abs_mul, abs_of_nonneg hβ0, pow_succ]
      nlinarith
  funext z
  have hlim : Tendsto (fun n : ℕ => β ^ n * (2 * M)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (2 * M)
  have := ge_of_tendsto' hlim fun n => key n z
  have h0 := abs_nonneg (u₁ z - u₂ z)
  have : u₁ z - u₂ z = 0 := abs_eq_zero.1 (le_antisymm this h0)
  linarith

variable (xbar) in
/-- The no-migration value `w = f + β ∫ w dQ` (p. 410): the expected discounted wage stream of an
island worker if the population stays at `x`. -/
noncomputable def searchW (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) (f : ℝ → ℝ → ℝ) (β : ℝ) :
    Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ :=
  Classical.epsilon fun w => ∀ p, w p = f p.1 p.2 + β * ∫ z', w (p.1, z') ∂Q p.2

/-- `w` solves `w(x, z) = f(x, z) + β ∫ w(x, z′) Q(z, dz′)` (a contraction of modulus `β`). -/
theorem searchW_eq (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    searchW xbar Q f β p = f p.1 p.2 + β * ∫ z', searchW xbar Q f β (p.1, z') ∂Q p.2 := by
  have hc : ∀ w : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ,
      Continuous fun p : Icc (0 : ℝ) xbar × Icc zlo zhi =>
        f p.1 p.2 + β * ∫ z', w (p.1, z') ∂Q p.2 :=
    fun w => hP.continuous_f.add (continuous_const.mul (lemma_12_14_cont Q hF w).1)
  set T : (Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ) → (Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ) :=
    fun w => mkOfCompact ⟨_, hc w⟩
  have hC : IsContraction T β := ⟨hP.hβ0, hP.hβ1, fun v w => by
    refine (dist_le (mul_nonneg hP.hβ0.le dist_nonneg)).2 fun p => ?_
    simp only [T, mkOfCompact_apply, ContinuousMap.coe_mk, Real.dist_eq]
    rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos hP.hβ0]
    exact mul_le_mul_of_nonneg_left (abs_integral_searchSection_sub_le Q v w p.1 p.2)
      hP.hβ0.le⟩
  obtain ⟨w, hw, -⟩ := theorem_3_2 hC
  exact Classical.epsilon_spec (p := fun w : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ =>
    ∀ p, w p = f p.1 p.2 + β * ∫ z', w (p.1, z') ∂Q p.2)
    ⟨w, fun p => by
      have := congrArg (fun u => u p) hw
      simp only [T, mkOfCompact_apply, ContinuousMap.coe_mk] at this
      exact this.symm⟩ p

/-- **Assumption (6)** (p. 410): `w(x, z̲) < β ∫ w(x, z′) Q(z̄, dz′)` for all `x ∈ [0, x̄)`. -/
def SearchAssumption6 (hz : zlo ≤ zhi) (xbar : ℝ) (Q : Kernel (Icc zlo zhi) (Icc zlo zhi))
    (f : ℝ → ℝ → ℝ) (β : ℝ) : Prop :=
  ∀ x : Icc (0 : ℝ) xbar, (x : ℝ) < xbar →
    searchW xbar Q f β (x, ⟨zlo, le_rfl, hz⟩) <
      β * ∫ z', searchW xbar Q f β (x, z') ∂Q ⟨zhi, hz, le_rfl⟩

/-- **[Derived] fact behind Ex. 13.8d.** Under (6), no `x ∈ [0, x̄)` has
`β ∫ v(x, z′) Q(z̄, dz′) ≤ θ ≤ f(x, z̲) + β ∫ v(x, z′) Q(z̲, dz′)`. (Otherwise `x` is in Case B at
every `z`, so `v(x, ·) = w(x, ·)`, and (6) gives `w(x, z̲) < θ ≤ w(x, z̲)`.) -/
theorem searchNoCaseB (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (h6 : SearchAssumption6 hP.hz xbar Q f β) {x : Icc (0 : ℝ) xbar}
    (hx : (x : ℝ) < xbar) :
    ¬ (searchEV xbar Q f β θ (x, ⟨zhi, hP.hz, le_rfl⟩) ≤ θ ∧
      θ ≤ searchPhi xbar Q f β θ (x, ⟨zlo, le_rfl, hP.hz⟩)) := by
  rintro ⟨h1, h2⟩
  have hB : ∀ z : Icc zlo zhi, searchV xbar Q f β θ (x, z) = searchPhi xbar Q f β θ (x, z) :=
    fun z => (searchV_cases Q hP hF (x, z)).2.1
      ((searchEV_mono Q hP hF hM x (show z ≤ ⟨zhi, hP.hz, le_rfl⟩ from z.2.2)).trans h1)
      (h2.trans (searchPhi_mono Q hP hF hM x (show ⟨zlo, le_rfl, hP.hz⟩ ≤ z from z.2.1)))
  have hvw : (fun z => searchV xbar Q f β θ (x, z)) = fun z => searchW xbar Q f β (x, z) := by
    refine searchSection_unique Q hP.hβ0.le hP.hβ1 (measurable_searchSection _ x)
      (measurable_searchSection _ x) (M := ‖searchV xbar Q f β θ‖ + ‖searchW xbar Q f β‖)
      (fun z => ?_) (fun z => ?_) (fun z => f x z) (fun z => ?_)
      (fun z => searchW_eq Q hP hF (x, z))
    · rw [← Real.norm_eq_abs]
      linarith [(searchV xbar Q f β θ).norm_coe_le_norm (x, z), norm_nonneg (searchW xbar Q f β)]
    · rw [← Real.norm_eq_abs]
      linarith [(searchW xbar Q f β).norm_coe_le_norm (x, z), norm_nonneg (searchV xbar Q f β θ)]
    · rw [hB]; rfl
  have h6x := h6 x hx
  have e1 : searchEV xbar Q f β θ (x, ⟨zhi, hP.hz, le_rfl⟩) =
      β * ∫ z', searchW xbar Q f β (x, z') ∂Q ⟨zhi, hP.hz, le_rfl⟩ := by
    simp only [searchEV]
    exact congrArg (β * ·) (integral_congr_ae (Eventually.of_forall (congrFun hvw)))
  have e2 : searchW xbar Q f β (x, ⟨zlo, le_rfl, hP.hz⟩) =
      searchPhi xbar Q f β θ (x, ⟨zlo, le_rfl, hP.hz⟩) := by
    rw [← hB]; exact (congrFun hvw _).symm
  linarith

variable [Nonempty (Icc (0 : ℝ) xbar)]

variable (xbar) in
/-- The transition function of §13.8, `P((x, z), A × B) = 1{g(x, z) ∈ A} Q(z, B)`, on the
rectangle `X × Z = [(0, z̲), (x̄, z̄)]`. -/
noncomputable def searchP (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) (f : ℝ → ℝ → ℝ) (β θ : ℝ)
    (hg : Measurable (searchG xbar Q f β θ)) :
    Kernel (Icc ((0 : ℝ), zlo) (xbar, zhi)) (Icc ((0 : ℝ), zlo) (xbar, zhi)) :=
  searchKernel Q (fun s => searchG xbar Q f β θ (searchOfR s)) (hg.comp measurable_searchOfR)

/-- `g` is nondecreasing on `X × Z` (coordinatewise order), by Ex. 13.8b. -/
theorem searchG_monotone (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) : Monotone (searchG xbar Q f β θ) := fun p q hpq => by
  have hb := ex_13_8b Q hP hF hM hθ
  exact (hb.2.2.2.1 p.2 hpq.1).trans (hb.2.2.2.2.1 q.1 hpq.2)

/-- **Exercise 13.8d** (the process). `P` is a monotone Feller transition function on the compact
rectangle `X × Z` (Theorems 9.13–9.14), so it has an invariant probability measure (Theorem
12.10). -/
theorem ex_13_8d_process (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) (hg : Measurable (searchG xbar Q f β θ)) :
    IsMarkovKernel (searchP xbar Q f β θ hg) ∧ IsMonotoneTF (searchP xbar Q f β θ hg) ∧
      IsFeller (searchP xbar Q f β θ hg) ∧
      ∃ μ, IsProbabilityMeasure μ ∧ adjointOp (searchP xbar Q f β θ hg) μ = μ := by
  have hmk : IsMarkovKernel (searchP xbar Q f β θ hg) :=
    isMarkovKernel_searchKernel Q (hg.comp measurable_searchOfR)
  have hFP := isFeller_searchKernel Q (hg.comp measurable_searchOfR) hF
    ((ex_13_8c Q hP hF hM hθ).comp continuous_searchOfR)
  have hne : Nonempty (Icc ((0 : ℝ), zlo) (xbar, zhi)) :=
    ⟨⟨((0 : ℝ), zlo), left_mem_Icc.2 ⟨hP.hx.le, hP.hz⟩⟩⟩
  exact ⟨hmk, isMonotoneTF_searchKernel Q _ hM fun s t hst =>
    searchG_monotone Q hP hF hM hθ (searchOfR_mono hst), hFP, theorem_12_10 hFP⟩
/-- `g_A(z) = 0` when `f(0, z) + β ∫ v(0, z′) Q(z, dz′) ≤ θ`. -/
theorem searchGA_eq_zero (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) {z : Icc zlo zhi}
    (h : searchPhi xbar Q f β θ (⟨0, le_rfl, hP.hx.le⟩, z) ≤ θ) :
    (searchGA xbar Q f β θ z : ℝ) = 0 := by
  have H := searchPhi_hyps Q hP hF hM hθ
  unfold searchGA
  rw [searchCutoff_eq H.2.1 H.2.2.1 (isSearchCutoff_of_le_zero H.2.1 (fun x => x.2.1)
    (by linarith))]

/-- `g_C(z) = 0` when `β ∫ v(0, z′) Q(z, dz′) ≤ θ`. -/
theorem searchGC_eq_zero (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) {z : Icc zlo zhi}
    (h : searchEV xbar Q f β θ (⟨0, le_rfl, hP.hx.le⟩, z) ≤ θ) :
    (searchGC xbar Q f β θ z : ℝ) = 0 := by
  have H := searchEV_hyps Q hP hF hM hθ
  unfold searchGC
  rw [searchCutoff_eq H.2.1 H.2.2.1 (isSearchCutoff_of_le_zero H.2.1 (fun x => x.2.1)
    (by linarith))]

omit [IsMarkovKernel Q] in
/-- `g(x, z) ≤ g_A(z)`. -/
theorem searchG_le_searchGA (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    searchG xbar Q f β θ p ≤ searchGA xbar Q f β θ p.2 :=
  min_le_right _ _

/-- `g_C(z) ≤ g(x, z)`. -/
theorem searchGC_le_searchG (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    searchGC xbar Q f β θ p.2 ≤ searchG xbar Q f β θ p :=
  le_min (le_max_right _ _) (searchGC_le_searchGA Q hP hF hM hθ p.2)

/-! ### The case `θ ≥ θ̄`, and the corrections to the hint of Ex. 13.8d -/

/-- `θ̄ = f(0, z̄)/(1 − β)`. -/
noncomputable def searchThetaBar (zhi β : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  f 0 zhi / (1 - β)

omit [Nonempty (Icc (0 : ℝ) xbar)] in
/-- `θ̄ > 0`, since `f(0, z̄) > f(x̄, z̄) = 0`; so `[βθ̄, θ̄)` is never empty. -/
theorem searchThetaBar_pos (hP : SearchPrimitives zlo zhi xbar β f) :
    0 < searchThetaBar zhi β f := by
  have h := hP.F1 zhi (right_mem_Icc.2 hP.hz) (left_mem_Icc.2 hP.hx.le)
    (right_mem_Icc.2 hP.hx.le) hP.hx
  simp only [hP.F1top zhi (right_mem_Icc.2 hP.hz)] at h
  exact div_pos h (sub_pos.2 hP.hβ1)

omit [Nonempty (Icc (0 : ℝ) xbar)] in
/-- **[Derived] (7) holds iff `θ ≥ θ̄`**: `v ≡ θ` if and only if `f(0, z̄) + βθ ≤ θ`. -/
theorem ex_13_8d_seven_iff (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hθ : 0 ≤ θ) :
    (∀ p, searchV xbar Q f β θ p = θ) ↔ searchThetaBar zhi β f ≤ θ := by
  have h1β : 0 < 1 - β := sub_pos.2 hP.hβ1
  have hEVc : ∀ (v : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ), (∀ p, v p = θ) →
      ∀ p : Icc (0 : ℝ) xbar × Icc zlo zhi, β * ∫ z', v (p.1, z') ∂Q p.2 = β * θ :=
    fun v hv p => by
    simp only [hv, integral_const, probReal_univ, one_smul]
  have hmin : min θ (β * θ) = β * θ := min_eq_right (by nlinarith [hP.hβ1])
  constructor
  · intro hv
    have := searchV_eq Q hP hF θ (⟨0, le_rfl, hP.hx.le⟩, ⟨zhi, hP.hz, le_rfl⟩)
    rw [hv, searchRHS, hEVc _ hv, hmin] at this
    have h2 : f 0 zhi + β * θ ≤ θ := by
      have := le_max_right θ (f 0 zhi + β * θ); linarith
    rw [searchThetaBar, div_le_iff₀ h1β]
    linarith
  · intro hθ'
    rw [searchThetaBar, div_le_iff₀ h1β] at hθ'
    have hfix : ∀ p, (const _ θ : Icc (0 : ℝ) xbar × Icc zlo zhi →ᵇ ℝ) p =
        searchRHS Q f β θ (const _ θ) p := fun p => by
      rw [searchRHS, hEVc _ (fun _ => rfl), hmin, const_apply]
      refine (max_eq_left ?_).symm
      linarith [hP.f_le p]
    intro p
    rw [← searchV_unique Q hP hF θ _ hfix, const_apply]

/-- **[Derived] (7) for `θ ≥ θ̄`**: `v ≡ θ` and `g ≡ 0` (everybody leaves). (6) is not needed:
**correction** to the hint of Ex. 13.8d. -/
theorem ex_13_8d_seven (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : searchThetaBar zhi β f ≤ θ) :
    (∀ p, searchV xbar Q f β θ p = θ) ∧ ∀ p, (searchG xbar Q f β θ p : ℝ) = 0 := by
  have hθ0 : 0 ≤ θ := (searchThetaBar_pos hP).le.trans hθ
  have hv := (ex_13_8d_seven_iff Q hP hF hθ0).2 hθ
  refine ⟨hv, fun p => le_antisymm ?_ (searchG xbar Q f β θ p).2.1⟩
  have hθ' := hθ
  rw [searchThetaBar, div_le_iff₀ (sub_pos.2 hP.hβ1)] at hθ'
  have hA : (searchGA xbar Q f β θ p.2 : ℝ) = 0 := by
    refine searchGA_eq_zero Q hP hF hM hθ0 ?_
    have : searchEV xbar Q f β θ (⟨0, le_rfl, hP.hx.le⟩, p.2) = β * θ := by
      simp only [searchEV, hv, integral_const, probReal_univ, one_smul]
    rw [searchPhi, this]
    linarith [hP.f_le (⟨0, le_rfl, hP.hx.le⟩, p.2)]
  exact (show (searchG xbar Q f β θ p : ℝ) ≤ searchGA xbar Q f β θ p.2 from
    searchG_le_searchGA Q p).trans hA.le

/-- **Correction (NOTE p. 410).** For `θ ≥ βθ̄`, `β ∫ v dQ ≤ β(f(0, z̄) + θ) ≤ θ` everywhere, so
Case C (2c) never occurs and `g_C ≡ 0`: nobody ever immigrates. -/
theorem ex_13_8d_noCaseC (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : β * searchThetaBar zhi β f ≤ θ) :
    (∀ p, searchEV xbar Q f β θ p ≤ θ) ∧ ∀ z, (searchGC xbar Q f β θ z : ℝ) = 0 := by
  have hθ0 : 0 ≤ θ := (mul_pos hP.hβ0 (searchThetaBar_pos hP)).le.trans hθ
  have h1β : 0 < 1 - β := sub_pos.2 hP.hβ1
  have hθ' : β * f 0 zhi ≤ (1 - β) * θ := by
    rw [searchThetaBar, mul_div_assoc', div_le_iff₀ h1β] at hθ
    linarith
  have hEV : ∀ p, searchEV xbar Q f β θ p ≤ θ := fun p => by
    linarith [(searchEV_bounds Q hP hF (θ := θ) p).2]
  exact ⟨hEV, fun z => searchGC_eq_zero Q hP hF hM hθ0 (hEV _)⟩

/-- **Correction (NOTE p. 410): the hint of Ex. 13.8d is false.** It claims that for every
`θ ∈ (0, θ̄)` both (2a) and (2c) hold on nonempty regions. In every instance of the model,
`θ = βθ̄ ∈ (0, θ̄)` (the interval `[βθ̄, θ̄)` is never empty, as `θ̄ > 0`) has no state in
Case C. -/
theorem ex_13_8d_hint_counterexample (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) :
    ¬ ∀ θ ∈ Ioo 0 (searchThetaBar zhi β f),
      (∃ p, searchPhi xbar Q f β θ p < θ) ∧ ∃ p, θ < searchEV xbar Q f β θ p := by
  intro h
  have hpos := searchThetaBar_pos hP
  obtain ⟨-, p, hp⟩ := h (β * searchThetaBar zhi β f) ⟨mul_pos hP.hβ0 hpos,
    by nlinarith [hP.hβ1]⟩
  linarith [(ex_13_8d_noCaseC Q hP hF hM le_rfl).1 p]

/-- The corrected hint: for every `θ > 0`, Case A (2a) occurs (at `x = x̄`), and Case C (2c)
occurs only if `θ < βθ̄`. -/
theorem ex_13_8d_hint_corrected (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 < θ) :
    (∀ z, searchPhi xbar Q f β θ (⟨xbar, hP.hx.le, le_rfl⟩, z) < θ) ∧
      ((∃ p, θ < searchEV xbar Q f β θ p) → θ < β * searchThetaBar zhi β f) := by
  refine ⟨fun z => by rw [searchPhi_top Q hP hF]; nlinarith [hP.hβ1], fun ⟨p, hp⟩ => ?_⟩
  by_contra hle
  rw [not_lt] at hle
  linarith [(ex_13_8d_noCaseC Q hP hF hM hle).1 p]

/-! ### Exercise 13.8d: uniqueness of the invariant measure -/

/-- **Exercise 13.8d.** Under (6) (and the mixing condition (2) of §13.4 on `Q`), for every
`θ > 0` the transition function `P` has a unique invariant probability measure `λ`, and
`T*ⁿλ₀ ⇒ λ` for every `λ₀`. The proof verifies Assumption 12.1 and applies Theorem 12.12:
* if Case C occurs (`g_C(z̄) > 0`), then `g_A(z̲) < g_C(z̄)` by (6) (`searchNoCaseB`), and
  `c_x ∈ (g_A(z̲), g_C(z̄))` is the `x`-coordinate of the mixing point;
* if Case C never occurs (`g_C ≡ 0`, e.g. for `θ ≥ βθ̄`), then `f(0, z̲) + β∫v(0, ·)dQ(z̲) < θ`
  by (6), so `g ≡ 0` near `z̲`, `0` is absorbing, and the mixing point is the corner `c_x = 0`
  (the corrected hint: the invariant measure is `δ₀ × μ`, `ex_13_8d_delta`). -/
theorem ex_13_8d (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (h6 : SearchAssumption6 hP.hz xbar Q f β) (hθ : 0 < θ)
    (hg : Measurable (searchG xbar Q f β θ)) :
    ∃ μ : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)), IsProbabilityMeasure μ ∧
      adjointOp (searchP xbar Q f β θ hg) μ = μ ∧
      (∀ ν, IsProbabilityMeasure ν → adjointOp (searchP xbar Q f β θ hg) ν = ν → ν = μ) ∧
      ∀ lam₀, IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp (searchP xbar Q f β θ hg))^[n] lam₀) μ := by
  have hθ0 := hθ.le
  have hab : ((0 : ℝ), zlo) ≤ (xbar, zhi) := ⟨hP.hx.le, hP.hz⟩
  set botZ : Icc zlo zhi := ⟨zlo, le_rfl, hP.hz⟩
  set topZ : Icc zlo zhi := ⟨zhi, hP.hz, le_rfl⟩
  set x0 : Icc (0 : ℝ) xbar := ⟨0, le_rfl, hP.hx.le⟩
  have key : ∃ (cx : Icc (0 : ℝ) xbar) (z₁ z₂ : Icc zlo zhi), (z₁ : ℝ) < zhi ∧
      zlo < (z₂ : ℝ) ∧ (∀ z, z ≤ z₂ → searchGA xbar Q f β θ z ≤ cx) ∧
      ∀ z, z₁ ≤ z → cx ≤ searchGC xbar Q f β θ z := by
    by_cases hC : 0 < (searchGC xbar Q f β θ topZ : ℝ)
    · set xc := searchGC xbar Q f β θ topZ
      have hEV : searchEV xbar Q f β θ (xc, topZ) = θ :=
        (searchGC_spec Q hP hF hM hθ0 topZ).2 hC
      have hxc : (xc : ℝ) < xbar := by
        refine lt_of_le_of_ne xc.2.2 fun h => ?_
        have : xc = ⟨xbar, hP.hx.le, le_rfl⟩ := Subtype.ext h
        rw [this, searchEV_top Q hP hF] at hEV
        nlinarith [hP.hβ1]
      have hlt : searchGA xbar Q f β θ botZ < xc := by
        by_contra hle
        rw [not_lt] at hle
        refine searchNoCaseB Q hP hF hM h6 hxc ⟨hEV.le, ?_⟩
        rcases eq_or_lt_of_le hle with heq | hlt'
        · have hspec := (searchGA_spec Q hP hF hM hθ0 botZ).2 (heq ▸ hC)
          rw [← heq] at hspec
          exact hspec.ge
        · have := (searchGA_isCutoff Q hP hF hM hθ0 botZ).pos_of_lt
            (searchPhi_hyps Q hP hF hM hθ0).2.2.1 hlt'
          linarith
      obtain ⟨cx, h1, h2⟩ := exists_between hlt
      obtain ⟨z₂, hz₂, hz₂'⟩ := exists_searchNear_bot hzlt
        (((continuous_searchGA Q hP hF hM hθ0).tendsto botZ).eventually (gt_mem_nhds h1))
      obtain ⟨z₁, hz₁, hz₁'⟩ := exists_searchNear_top hzlt
        (((continuous_searchGC Q hP hF hM hθ0).tendsto topZ).eventually (lt_mem_nhds h2))
      exact ⟨cx, z₁, z₂, hz₁, hz₂, fun z hz => (searchGA_mono Q hP hF hM hθ0 hz).trans hz₂'.le,
        fun z hz => hz₁'.le.trans (searchGC_mono Q hP hF hM hθ0 hz)⟩
    · have hx0 : searchGC xbar Q f β θ topZ = x0 :=
        Subtype.ext (le_antisymm (not_lt.1 hC) (searchGC xbar Q f β θ topZ).2.1)
      have hEV : searchEV xbar Q f β θ (x0, topZ) ≤ θ := by
        have := (searchGC_spec Q hP hF hM hθ0 topZ).1
        rwa [hx0] at this
      have hPhi : searchPhi xbar Q f β θ (x0, botZ) < θ := by
        by_contra hge
        rw [not_lt] at hge
        exact searchNoCaseB Q hP hF hM h6 (x := x0) hP.hx ⟨hEV, hge⟩
      obtain ⟨z₂, hz₂, hz₂'⟩ := exists_searchNear_bot hzlt
        ((((continuous_searchPhi Q hP hF).comp (continuous_const.prodMk continuous_id)).tendsto
          botZ).eventually (gt_mem_nhds hPhi))
      refine ⟨x0, botZ, z₂, hzlt, hz₂, fun z hz => ?_, fun z _ => (searchGC xbar Q f β θ z).2.1⟩
      have hle : searchPhi xbar Q f β θ (x0, z) ≤ θ :=
        ((searchPhi_mono Q hP hF hM x0 hz).trans hz₂'.le)
      exact le_of_eq (Subtype.ext (searchGA_eq_zero Q hP hF hM hθ0 hle))
  obtain ⟨cx, z₁, z₂, hz₁, hz₂, hA, hC⟩ := key
  exact searchKernel_unique Q _ hzlt hF hM hmix hab
    (fun s t hst => searchG_monotone Q hP hF hM hθ0 (searchOfR_mono hst))
    ((ex_13_8c Q hP hF hM hθ0).comp continuous_searchOfR) cx hz₁ hz₂
    (fun s hs => (searchG_le_searchGA Q _).trans (hA _ hs))
    (fun s hs => (hC _ hs).trans (searchGC_le_searchG Q hP hF hM hθ0 _))
/-- **NOTE (p. 410), Case A at `z̲`.** Under (6), for `θ ≥ βθ̄` every `x` is in Case A at `z̲`:
`f(x, z̲) + β ∫ v(x, z′) Q(z̲, dz′) < θ`, so `g(·, z) ≡ 0` near `z̲` and `0` is absorbing. -/
theorem ex_13_8d_caseA_zlo (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (h6 : SearchAssumption6 hP.hz xbar Q f β)
    (hθ : β * searchThetaBar zhi β f ≤ θ) (x : Icc (0 : ℝ) xbar) :
    searchPhi xbar Q f β θ (x, ⟨zlo, le_rfl, hP.hz⟩) < θ := by
  have hEV := (ex_13_8d_noCaseC Q hP hF hM hθ).1
  have h0 : searchPhi xbar Q f β θ (⟨0, le_rfl, hP.hx.le⟩, ⟨zlo, le_rfl, hP.hz⟩) < θ := by
    by_contra hge
    rw [not_lt] at hge
    exact searchNoCaseB Q hP hF hM h6 (x := ⟨0, le_rfl, hP.hx.le⟩) hP.hx ⟨hEV _, hge⟩
  exact lt_of_le_of_lt (searchPhi_anti Q hP hF hM _ (show (⟨0, le_rfl, hP.hx.le⟩ :
    Icc (0 : ℝ) xbar) ≤ x from x.2.1)) h0

/-! ### Invariant measures of the form `δ_{x₀} × μ`, and the mean work force -/

omit [Nonempty (Icc (0 : ℝ) xbar)] in
/-- For an invariant `λ`, the mean work force is the mean of `G`: `∫ x dλ = ∫ G dλ`. -/
theorem searchKernel_integral_fst (lam : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)))
    [IsProbabilityMeasure lam] (hinv : adjointOp (searchKernel Q G hG) lam = lam) :
    ∫ s, (s : ℝ × ℝ).1 ∂lam = ∫ s, (G s : ℝ) ∂lam := by
  have := isMarkovKernel_searchKernel Q hG
  have hφ : Measurable fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (s : ℝ × ℝ).1 :=
    measurable_fst.comp measurable_subtype_coe
  have hb : ∀ s : Icc ((0 : ℝ), zlo) (xbar, zhi), |(s : ℝ × ℝ).1| ≤ xbar := fun s => by
    rw [abs_of_nonneg s.2.1.1]; exact s.2.2.1
  have h := theorem_8_3_cor (searchKernel Q G hG) lam hφ hb
  rw [hinv] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [markovOpR]
  rw [integral_searchKernel Q hG hφ s]
  simp [searchToR]

/-- `δ_{x₀} × μ` as a measure on the rectangle. -/
noncomputable def searchDiracProd (x₀ : Icc (0 : ℝ) xbar) (μ : Measure (Icc zlo zhi)) :
    Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)) :=
  μ.map fun z => searchToR (x₀, z)

omit [Nonempty (Icc (0 : ℝ) xbar)] in
/-- If `x₀` is absorbing (`G(x₀, z) = x₀` for all `z`) and `μ` is invariant for `Q`, then
`δ_{x₀} × μ` is invariant for `P`. -/
theorem searchDiracProd_invariant (x₀ : Icc (0 : ℝ) xbar)
    (hG0 : ∀ z, G (searchToR (x₀, z)) = x₀) (μ : Measure (Icc zlo zhi))
    (hμ : adjointOp Q μ = μ) :
    adjointOp (searchKernel Q G hG) (searchDiracProd x₀ μ) = searchDiracProd x₀ μ := by
  have hm : Measurable fun z : Icc zlo zhi => searchToR (x₀, z) :=
    measurable_searchToR.comp measurable_prodMk_left
  ext A hA
  rw [adjointOp_apply _ _ hA, searchDiracProd, lintegral_map (Kernel.measurable_coe _ hA) hm,
    Measure.map_apply hm hA]
  have : ∀ z, searchKernel Q G hG (searchToR (x₀, z)) A =
      Q z ((fun z' => searchToR (x₀, z')) ⁻¹' A) := fun z => by
    rw [searchKernel_apply, Measure.map_apply (measurable_searchSlice _) hA, hG0]
    rfl
  simp_rw [this]
  rw [← adjointOp_apply _ _ (hm hA), hμ]

omit [IsMarkovKernel Q] [Nonempty (Icc (0 : ℝ) xbar)] in
/-- The mean work force under `δ_{x₀} × μ` is `x₀`. -/
theorem integral_fst_searchDiracProd (x₀ : Icc (0 : ℝ) xbar) (μ : Measure (Icc zlo zhi))
    [IsProbabilityMeasure μ] : ∫ s, (s : ℝ × ℝ).1 ∂searchDiracProd x₀ μ = x₀ := by
  have hm : Measurable fun z : Icc zlo zhi => searchToR (x₀, z) :=
    measurable_searchToR.comp measurable_prodMk_left
  have hφ : Measurable fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (s : ℝ × ℝ).1 :=
    measurable_fst.comp measurable_subtype_coe
  rw [searchDiracProd, integral_map hm.aemeasurable hφ.aestronglyMeasurable]
  simp [searchToR]

omit [Nonempty (Icc (0 : ℝ) xbar)] in
/-- `Q` has an invariant probability measure `μ` (Theorem 12.10; unique by Theorem 12.12 under
the mixing condition, `searchQ_unique`). -/
theorem exists_searchQ_invariant (hz : zlo ≤ zhi) (hF : IsFeller Q) :
    ∃ μ : Measure (Icc zlo zhi), IsProbabilityMeasure μ ∧ adjointOp Q μ = μ := by
  have : Nonempty (Icc zlo zhi) := ⟨⟨zlo, le_rfl, hz⟩⟩
  exact theorem_12_10 hF

omit [Nonempty (Icc (0 : ℝ) xbar)] in
/-- Under the mixing condition (2) of §13.4, `Q` has a unique invariant probability measure. -/
theorem searchQ_unique (hzlt : zlo < zhi) (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ}
    {α : ℝ} (hmix : SearchMixing Q N α) :
    ∃ μ : Measure (Icc zlo zhi), IsProbabilityMeasure μ ∧ adjointOp Q μ = μ ∧
      ∀ ν, IsProbabilityMeasure ν → adjointOp Q ν = ν → ν = μ := by
  set cz : Icc zlo zhi := ⟨(zlo + zhi) / 2, by linarith, by linarith⟩
  have := ex_8_4a Q N
  have h1 := hmix.2.2 ⟨zlo, le_rfl, hzlt.le⟩ ((zlo + zhi) / 2) zhi (by linarith) (by linarith)
    le_rfl
  have h2 := hmix.2.2 ⟨zhi, hzlt.le, le_rfl⟩ zlo ((zlo + zhi) / 2) le_rfl (by linarith)
    (by linarith)
  obtain ⟨μ, hμ, hfix, huniq, -⟩ := theorem_12_12_real hzlt.le Q hM hF (c := cz)
    (ε := α * ((zhi - zlo) / 2)) (mul_pos hmix.2.1 (by linarith)) hmix.1
    ((by linarith : α * ((zhi - zlo) / 2) = α * (zhi - (zlo + zhi) / 2)) ▸ h1.trans
      (measureReal_mono fun z' (h : _ ∧ _) => show cz ≤ z' from h.1.le))
    ((by linarith : α * ((zhi - zlo) / 2) = α * ((zlo + zhi) / 2 - zlo)) ▸ h2.trans
      (measureReal_mono fun z' (h : _ ∧ _) => show z' ≤ cz from h.2))
  exact ⟨μ, hμ, hfix, huniq⟩

open Classical in
variable (xbar) in
/-- `D(θ) = ∫ x λ_θ(dx × dz)`, the mean work force under (a chosen) invariant measure `λ_θ` of
`P_θ` (the unique one wherever it is unique). -/
noncomputable def searchD (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) (f : ℝ → ℝ → ℝ) (β θ : ℝ) :
    ℝ :=
  if hg : Measurable (searchG xbar Q f β θ) then
    ∫ s, (s : ℝ × ℝ).1 ∂(Classical.epsilon fun μ : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)) =>
      IsProbabilityMeasure μ ∧ adjointOp (searchP xbar Q f β θ hg) μ = μ)
  else 0

/-- `D(θ)` is the mean work force under any invariant measure when that mean does not depend on
the invariant measure. -/
theorem searchD_eq_of_forall (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) (hg : Measurable (searchG xbar Q f β θ)) {d : ℝ}
    (h : ∀ lam, IsProbabilityMeasure lam → adjointOp (searchP xbar Q f β θ hg) lam = lam →
      ∫ s, (s : ℝ × ℝ).1 ∂lam = d) : searchD xbar Q f β θ = d := by
  simp only [searchD, hg, ↓reduceDIte]
  have hspec := Classical.epsilon_spec (ex_13_8d_process Q hP hF hM hθ hg).2.2.2
  exact h _ hspec.1 hspec.2

/-- `D(θ)` is the mean work force under the unique invariant measure. -/
theorem searchD_eq (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) (hg : Measurable (searchG xbar Q f β θ))
    {lam : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi))}
    (huniq : ∀ ν, IsProbabilityMeasure ν → adjointOp (searchP xbar Q f β θ hg) ν = ν → ν = lam) :
    searchD xbar Q f β θ = ∫ s, (s : ℝ × ℝ).1 ∂lam :=
  searchD_eq_of_forall Q hP hF hM hθ hg fun ν hν hfix => by rw [huniq ν hν hfix]

/-- `0 ≤ D(θ) ≤ x̄`. -/
theorem searchD_mem (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : 0 ≤ θ) : searchD xbar Q f β θ ∈ Icc 0 xbar := by
  have hg := (ex_13_8c Q hP hF hM hθ).measurable
  simp only [searchD, hg, ↓reduceDIte]
  set lam := Classical.epsilon fun μ : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)) =>
    IsProbabilityMeasure μ ∧ adjointOp (searchP xbar Q f β θ hg) μ = μ
  have hspec : IsProbabilityMeasure lam :=
    (Classical.epsilon_spec (ex_13_8d_process Q hP hF hM hθ hg).2.2.2).1
  have hφ : Measurable fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (s : ℝ × ℝ).1 :=
    measurable_fst.comp measurable_subtype_coe
  constructor
  · exact integral_nonneg fun s => s.2.1.1
  · have := integral_mono (integrable_of_bounded (μ := lam) hφ (M := xbar)
      fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => by
        rw [abs_of_nonneg s.2.1.1]; exact s.2.2.1) (integrable_const xbar)
      fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => s.2.2.1
    simpa using this

/-! ### Exercise 13.8f: `D(0) = x̄` and `D(θ) = 0` for large `θ` -/

/-- At `θ = 0` (outside Ex. 13.8a,d, which take `θ > 0`), every state is in Case C or at `x̄`:
`g ≡ x̄`. -/
theorem searchG_theta_zero (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (p : Icc (0 : ℝ) xbar × Icc zlo zhi) :
    (searchG xbar Q f β 0 p : ℝ) = xbar := by
  have H := searchEV_hyps Q hP hF hM (θ := 0) le_rfl
  set top : Icc (0 : ℝ) xbar := ⟨xbar, hP.hx.le, le_rfl⟩
  have hC : searchGC xbar Q f β 0 p.2 = top := by
    unfold searchGC
    refine searchCutoff_eq H.2.1 H.2.2.1 ⟨fun x _ => ?_, fun x hx => absurd hx (not_lt.2 x.2.2)⟩
    have := (searchEV_bounds Q hP hF (θ := 0) (x, p.2)).1
    simp only [mul_zero] at this
    linarith
  have hA : searchGA xbar Q f β 0 p.2 = top :=
    le_antisymm (searchGA xbar Q f β 0 p.2).2.2
      (hC ▸ searchGC_le_searchGA Q hP hF hM le_rfl p.2)
  rw [searchG_coe, hC, hA]
  simp [top, p.1.2.2]

/-- **Exercise 13.8f** (`θ = 0`). At `θ = 0`, `g ≡ x̄`, every invariant measure has mean work force
`x̄`, and `D(0) = x̄`. -/
theorem ex_13_8f_zero (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) : searchD xbar Q f β 0 = xbar := by
  have hg := (ex_13_8c Q hP hF hM (θ := 0) le_rfl).measurable
  refine searchD_eq_of_forall Q hP hF hM le_rfl hg fun lam hlam hinv => ?_
  rw [searchKernel_integral_fst Q _ lam hinv]
  simp only [searchG_theta_zero Q hP hF hM, integral_const, probReal_univ, one_smul]

/-- **Exercise 13.8f** (`θ ≥ θ̄`). For `θ ≥ θ̄`, `g ≡ 0`, every invariant measure has mean work
force `0`, and `D(θ) = 0`. (6) is not needed. -/
theorem ex_13_8f_large (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (hθ : searchThetaBar zhi β f ≤ θ) : searchD xbar Q f β θ = 0 := by
  have hθ0 : 0 ≤ θ := (searchThetaBar_pos hP).le.trans hθ
  have hg := (ex_13_8c Q hP hF hM hθ0).measurable
  refine searchD_eq_of_forall Q hP hF hM hθ0 hg fun lam hlam hinv => ?_
  rw [searchKernel_integral_fst Q _ lam hinv]
  simp only [(ex_13_8d_seven Q hP hF hM hθ).2, integral_const, smul_zero]

/-- **[Derived] fact for `θ ≥ θ̄`.** With the mixing condition, the unique invariant measure of `P`
is `δ₀ × μ` (`μ` the invariant measure of `Q`); (6) is not needed. -/
theorem ex_13_8d_large (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (hθ : searchThetaBar zhi β f ≤ θ) (hg : Measurable (searchG xbar Q f β θ))
    (μ : Measure (Icc zlo zhi)) [IsProbabilityMeasure μ] (hμ : adjointOp Q μ = μ) :
    adjointOp (searchP xbar Q f β θ hg) (searchDiracProd ⟨0, le_rfl, hP.hx.le⟩ μ) =
        searchDiracProd ⟨0, le_rfl, hP.hx.le⟩ μ ∧
      ∀ ν, IsProbabilityMeasure ν → adjointOp (searchP xbar Q f β θ hg) ν = ν →
        ν = searchDiracProd ⟨0, le_rfl, hP.hx.le⟩ μ := by
  have hθ0 : 0 ≤ θ := (searchThetaBar_pos hP).le.trans hθ
  have hG0 : ∀ s, searchG xbar Q f β θ (searchOfR s) = ⟨0, le_rfl, hP.hx.le⟩ := fun s =>
    Subtype.ext ((ex_13_8d_seven Q hP hF hM hθ).2 _)
  have hinv := searchDiracProd_invariant Q (hg.comp measurable_searchOfR) ⟨0, le_rfl, hP.hx.le⟩
    (fun z => hG0 _) μ hμ
  have : IsProbabilityMeasure (searchDiracProd (⟨0, le_rfl, hP.hx.le⟩ : Icc (0 : ℝ) xbar) μ) :=
    by unfold searchDiracProd; infer_instance
  obtain ⟨lam, -, -, huniq, -⟩ := searchKernel_unique Q (hg.comp measurable_searchOfR) hzlt hF hM
    hmix ⟨hP.hx.le, hP.hz⟩
    (fun s t hst => searchG_monotone Q hP hF hM hθ0 (searchOfR_mono hst))
    ((ex_13_8c Q hP hF hM hθ0).comp continuous_searchOfR) ⟨0, le_rfl, hP.hx.le⟩
    (z₁ := ⟨zlo, le_rfl, hP.hz⟩) (z₂ := ⟨zhi, hP.hz, le_rfl⟩) hzlt hzlt
    (fun s _ => (hG0 s).le) (fun s _ => (hG0 s).ge)
  refine ⟨hinv, fun ν hν hνfix => ?_⟩
  rw [huniq ν hν hνfix, huniq _ this hinv]

/-- **Correction (NOTE p. 410), and Ex. 13.8f for `θ ≥ βθ̄`.** Under (6) and the mixing
condition, for every `θ ≥ βθ̄` (not only `θ ≥ θ̄`) nobody immigrates, `0` is absorbing, the unique
invariant measure is `δ₀ × μ`, and `D(θ) = 0`. -/
theorem ex_13_8d_delta (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (h6 : SearchAssumption6 hP.hz xbar Q f β) (hθ : β * searchThetaBar zhi β f ≤ θ)
    (hg : Measurable (searchG xbar Q f β θ)) (μ : Measure (Icc zlo zhi))
    [IsProbabilityMeasure μ] (hμ : adjointOp Q μ = μ) :
    (∀ ν, IsProbabilityMeasure ν → adjointOp (searchP xbar Q f β θ hg) ν = ν →
        ν = searchDiracProd ⟨0, le_rfl, hP.hx.le⟩ μ) ∧ searchD xbar Q f β θ = 0 := by
  have hθ0 : 0 < θ := (mul_pos hP.hβ0 (searchThetaBar_pos hP)).trans_le hθ
  have hC := (ex_13_8d_noCaseC Q hP hF hM hθ).2
  have hG0 : ∀ z, searchG xbar Q f β θ (searchOfR (searchToR (⟨0, le_rfl, hP.hx.le⟩, z))) =
      ⟨0, le_rfl, hP.hx.le⟩ := fun z => by
    refine Subtype.ext ?_
    rw [searchOfR_toR, searchG_coe, hC z]
    simp only [max_self]
    exact min_eq_left ((hC z).symm.le.trans (searchGC_le_searchGA Q hP hF hM hθ0.le z))
  have hinv := searchDiracProd_invariant Q (hg.comp measurable_searchOfR) ⟨0, le_rfl, hP.hx.le⟩
    hG0 μ hμ
  have : IsProbabilityMeasure (searchDiracProd (⟨0, le_rfl, hP.hx.le⟩ : Icc (0 : ℝ) xbar) μ) :=
    by unfold searchDiracProd; infer_instance
  obtain ⟨lam, -, -, huniq, -⟩ := ex_13_8d Q hP hzlt hF hM hmix h6 hθ0 hg
  have hl : ∀ ν, IsProbabilityMeasure ν → adjointOp (searchP xbar Q f β θ hg) ν = ν →
      ν = searchDiracProd ⟨0, le_rfl, hP.hx.le⟩ μ := fun ν hν hνfix => by
    rw [huniq ν hν hνfix, huniq _ this hinv]
  refine ⟨hl, ?_⟩
  rw [searchD_eq Q hP hF hM hθ0.le hg hl, integral_fst_searchDiracProd]

end StokeyLucasPrescott.ConvergenceApplications

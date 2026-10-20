/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.SearchDemand

/-!
# An equilibrium search economy: `D` is strictly decreasing where it is positive (SLP §13.8)

SLP §13.8, p. 412, Exercise 13.8h ("How can this argument be strengthened to show that `D(θ)` is
strictly decreasing when `θ > 0`?"), under (6) and the mixing condition, the hypotheses of
Ex. 13.8d,g,h.

* `searchG_theta_lt`: for `0 ≤ θ < θ′`, `g_θ′(s) < g_θ(s)` at every state where `g_θ(s) > 0` and
  `g_θ(s) ≠ x` (the island's work force is pushed to a positive cutoff `g_A` or `g_C`, both
  strictly decreasing in `θ`, `searchCutoffs_theta_strict`).
* `searchFrozen_rect_ge`: if `λ` is invariant for `P` and the work force is frozen `λ`-a.e.
  (`G(s) = x`), then `B ↦ λ(A × B)` is `Q`-invariant, so `λ(A × B) ≥ c · λ(A × Z)` whenever
  `Qᴺ(z, B) ≥ c` for all `z`.
* `searchFrozen_false`: under (6) and mixing, for `θ > 0` an invariant `λ_θ` cannot have a frozen
  work force with `λ_θ{x > 0} > 0`. (By (6), every `x ∈ (0, x̄]` is either below `g_C(z̄)` or
  above `g_A(z̲)` (`searchNoCaseB`); by mixing the shock reaches a neighbourhood of `z̄`, resp.
  `z̲`, where `x` is moved.)
* `searchD_dominance`: for `0 ≤ θ ≤ θ′`, `λ_θ′` is stochastically dominated by `λ_θ` (for
  bounded continuous nondecreasing `φ`, `∫ φ dλ_θ′ ≤ ∫ φ dλ_θ`), the argument of Ex. 13.8h.
* **`ex_13_8h_strict`** (p. 412, corrected): for `0 < θ < θ′` with `D(θ) > 0`,
  `D(θ′) < D(θ)`. Proof: `D(θ′) = ∫ g_θ′ dλ_θ′ ≤ ∫ g_θ′ dλ_θ ≤ ∫ g_θ dλ_θ = D(θ)`; equality forces
  `g_θ′ = g_θ` `λ_θ`-a.e., hence (`searchG_theta_lt` and `∫ x dλ_θ = ∫ g_θ dλ_θ`) a frozen work
  force, contradicting `searchFrozen_false`.
* **`ex_13_8h_corrected`**: `D` is strictly decreasing on `{θ > 0 : D(θ) > 0}`; with
  `ex_13_8h_zero`, `D` is strictly decreasing until it reaches `0` and is `0` from then on.
* **`ex_13_8g_unique`** (p. 412, "at most one positive equilibrium value for `θ`"): for `N > 0`
  there is at most one `θ ≥ 0` with `D(θ) = N`.

**Correction** (NOTE p. 412). The book's "`D` is strictly decreasing for `θ > 0`" is false
(`ex_13_8h_counterexample`); the corrected claim, strict decrease wherever `D > 0`, holds under the
book's own hypotheses (6) and mixing, with no extra condition (`ex_13_8h_corrected`). The strict
decrease of the cutoffs alone does not suffice (in Case B, `g_θ′ = g_θ = x`): the proof also needs
that the stationary work force is not frozen, which is where (6) and mixing enter.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

variable {zlo zhi xbar β : ℝ} {f : ℝ → ℝ → ℝ}
  (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) [IsMarkovKernel Q]

/-! ### Pointwise strict decrease of `g` off Case B -/

variable [Nonempty (Icc (0 : ℝ) xbar)] in
/-- For `0 ≤ θ < θ′`: at a state where `g_θ(s) > 0` and `g_θ(s) ≠ x` (the work force is moved to a
positive cutoff), `g_θ′(s) < g_θ(s)`. -/
theorem searchG_theta_lt (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) {θ θ' : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < θ')
    (p : Icc (0 : ℝ) xbar × Icc zlo zhi) (hpos : 0 < (searchG xbar Q f β θ p : ℝ))
    (hne : (searchG xbar Q f β θ p : ℝ) ≠ p.1) :
    (searchG xbar Q f β θ' p : ℝ) < searchG xbar Q f β θ p := by
  have hs := searchCutoffs_theta_strict Q hP hF hM hθ0 hθ p.2
  have hCA : (searchGC xbar Q f β θ p.2 : ℝ) ≤ searchGA xbar Q f β θ p.2 :=
    searchGC_le_searchGA Q hP hF hM hθ0 p.2
  rw [searchG_coe] at hpos hne ⊢
  rw [searchG_coe]
  rcases lt_or_ge (p.1 : ℝ) (searchGC xbar Q f β θ p.2) with hxC | hxC
  · have hC' : (searchGC xbar Q f β θ' p.2 : ℝ) < searchGC xbar Q f β θ p.2 :=
      hs.2 (lt_of_le_of_lt p.1.2.1 hxC)
    rw [max_eq_right hxC.le, min_eq_left hCA]
    exact (min_le_left _ _).trans_lt (max_lt hxC hC')
  · rw [max_eq_left hxC] at hpos hne ⊢
    have hAx : (searchGA xbar Q f β θ p.2 : ℝ) < p.1 := by
      by_contra h
      exact hne (min_eq_left (not_lt.1 h))
    rw [min_eq_right hAx.le] at hpos ⊢
    exact (min_le_right _ _).trans_lt (hs.1 hpos)

/-! ### A frozen work force -/

/-- If `λ` is invariant for `P` and the work force is frozen `λ`-a.e. (`G(s) = x`), then
`B ↦ λ(A × B)` is `Q`-invariant; hence `λ(A × B) ≥ c · λ(A × Z)` whenever `Qᴺ(z, B) ≥ c` for
every `z`. -/
theorem searchFrozen_rect_ge {G : Icc ((0 : ℝ), zlo) (xbar, zhi) → Icc (0 : ℝ) xbar}
    (hG : Measurable G) {lam : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi))}
    (hinv : adjointOp (searchKernel Q G hG) lam = lam)
    (hfz : ∀ᵐ s ∂lam, G s = (searchOfR s).1) {A : Set (Icc (0 : ℝ) xbar)}
    (hA : MeasurableSet A) {B : Set (Icc zlo zhi)} (hB : MeasurableSet B) (N : ℕ) {c : ℝ≥0∞}
    (hc : ∀ z, c ≤ kpow Q N z B) :
    c * lam ((fun s => (searchOfR s).1) ⁻¹' A) ≤
      lam ((fun s => (searchOfR s).1) ⁻¹' A ∩ (fun s => (searchOfR s).2) ⁻¹' B) := by
  set xs := fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s).1
  set zs := fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s).2
  have hxs : Measurable xs := measurable_fst.comp measurable_searchOfR
  have hzs : Measurable zs := measurable_snd.comp measurable_searchOfR
  set ν := (lam.restrict (xs ⁻¹' A)).map zs
  have hν : ∀ B', MeasurableSet B' → ν B' = lam (xs ⁻¹' A ∩ zs ⁻¹' B') := fun B' hB' => by
    rw [Measure.map_apply hzs hB', Measure.restrict_apply (hzs hB'), Set.inter_comm]
  have hfix : adjointOp Q ν = ν := by
    ext B' hB'
    rw [adjointOp_apply _ _ hB', hν B' hB', lintegral_map (Kernel.measurable_coe _ hB') hzs,
      ← lintegral_indicator (hxs hA)]
    conv_rhs => rw [← hinv]
    rw [adjointOp_apply _ _ ((hxs hA).inter (hzs hB'))]
    refine lintegral_congr_ae (hfz.mono fun s hs => ?_)
    dsimp only
    rw [searchKernel_apply, Measure.map_apply (measurable_searchSlice s)
      ((hxs hA).inter (hzs hB'))]
    by_cases hsA : s ∈ xs ⁻¹' A
    · rw [indicator_of_mem hsA]
      congr 1
      ext z'
      simp only [mem_preimage, mem_inter_iff, searchOfR_toR, xs, zs]
      exact ⟨fun hz => ⟨hs ▸ hsA, hz⟩, fun hz => hz.2⟩
    · rw [indicator_of_notMem hsA]
      symm
      convert measure_empty (μ := Q (searchOfR s).2)
      ext z'
      simp only [mem_preimage, mem_inter_iff, searchOfR_toR, xs, zs, mem_empty_iff_false,
        iff_false, not_and]
      intro h
      exact (hsA (show (searchOfR s).1 ∈ A by rw [← hs]; exact h)).elim
  have hN : adjointOp (kpow Q N) ν = ν := by
    rw [← adjointOp_iterate]
    exact Function.iterate_fixed hfix N
  have huniv : ν univ = lam (xs ⁻¹' A) := by
    rw [hν univ MeasurableSet.univ, preimage_univ, inter_univ]
  rw [← hν B hB, ← huniv]
  calc c * ν univ = ∫⁻ _, c ∂ν := (lintegral_const c).symm
    _ ≤ ∫⁻ z, kpow Q N z B ∂ν := lintegral_mono hc
    _ = adjointOp (kpow Q N) ν B := (adjointOp_apply _ _ hB).symm
    _ = ν B := by rw [hN]

variable [Nonempty (Icc (0 : ℝ) xbar)]

/-- For `θ > 0`, `g_A(z) < x̄`: at `x = x̄`, `f(x̄, z) + β ∫ v(x̄, ·) dQ = βθ < θ`. -/
theorem searchGA_lt_xbar (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) {θ : ℝ} (hθ : 0 < θ) (z : Icc zlo zhi) :
    (searchGA xbar Q f β θ z : ℝ) < xbar := by
  by_contra h
  have heq : (searchGA xbar Q f β θ z : ℝ) = xbar := le_antisymm (searchGA xbar Q f β θ z).2.2
    (not_lt.1 h)
  have hspec := (searchGA_spec Q hP hF hM hθ.le z).2 (by rw [heq]; exact hP.hx)
  have htop : searchGA xbar Q f β θ z = ⟨xbar, hP.hx.le, le_rfl⟩ := Subtype.ext heq
  rw [htop, searchPhi, searchEV_top Q hP hF] at hspec
  have hf : f (⟨xbar, hP.hx.le, le_rfl⟩ : Icc (0 : ℝ) xbar) z = 0 := hP.f_top z
  rw [hf, zero_add] at hspec
  nlinarith [hP.hβ1]

/-- **Under (6), every positive work force is moved somewhere.** For `θ > 0` and `x ∈ (0, x̄]`,
`x < g_C(z̄)` or `x > g_A(z̲)`. -/
theorem searchMoved (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) (h6 : SearchAssumption6 hP.hz xbar Q f β) {θ : ℝ} (hθ : 0 < θ)
    (x : Icc (0 : ℝ) xbar) (hx : 0 < (x : ℝ)) :
    (x : ℝ) < searchGC xbar Q f β θ ⟨zhi, hP.hz, le_rfl⟩ ∨
      (searchGA xbar Q f β θ ⟨zlo, le_rfl, hP.hz⟩ : ℝ) < x := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hxb : (x : ℝ) < xbar := h2.trans_lt (searchGA_lt_xbar Q hP hF hM hθ _)
  refine searchNoCaseB Q hP hF hM h6 (θ := θ) hxb ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le h1 with heq | hlt
    · have hx' : x = searchGC xbar Q f β θ ⟨zhi, hP.hz, le_rfl⟩ := Subtype.ext heq.symm
      rw [hx']
      exact (searchGC_spec Q hP hF hM hθ.le _).1
    · have := (searchGC_isCutoff Q hP hF hM hθ.le ⟨zhi, hP.hz, le_rfl⟩).2 x hlt
      simp only at this
      linarith
  · rcases eq_or_lt_of_le h2 with heq | hlt
    · have hx' : x = searchGA xbar Q f β θ ⟨zlo, le_rfl, hP.hz⟩ := Subtype.ext heq
      rw [hx', (searchGA_spec Q hP hF hM hθ.le _).2 (hx'.symm ▸ hx)]
    · have := (searchGA_isCutoff Q hP hF hM hθ.le ⟨zlo, le_rfl, hP.hz⟩).1 x hlt
      simp only at this
      linarith

/-- **No frozen invariant measure.** Under (6) and mixing, for `θ > 0` an invariant measure `λ`
of `P_θ` with `λ{x > 0} > 0` cannot have `g_θ(s) = x` for `λ`-a.e. `s`. -/
theorem searchFrozen_false (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (h6 : SearchAssumption6 hP.hz xbar Q f β) {θ : ℝ} (hθ : 0 < θ)
    (hg : Measurable (searchG xbar Q f β θ)) {lam : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi))}
    (hinv : adjointOp (searchP xbar Q f β θ hg) lam = lam)
    (hfz : ∀ᵐ s ∂lam, searchG xbar Q f β θ (searchOfR s) = (searchOfR s).1)
    (hpos : 0 < lam {s | 0 < (s : ℝ × ℝ).1}) : False := by
  set topZ : Icc zlo zhi := ⟨zhi, hP.hz, le_rfl⟩
  set botZ : Icc zlo zhi := ⟨zlo, le_rfl, hP.hz⟩
  set γ : ℝ := (searchGC xbar Q f β θ topZ : ℝ)
  set δ : ℝ := (searchGA xbar Q f β θ botZ : ℝ)
  set xs := fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s).1
  set zs := fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s).2
  have hxs : Measurable xs := measurable_fst.comp measurable_searchOfR
  have hzs : Measurable zs := measurable_snd.comp measurable_searchOfR
  have hGm := hg.comp measurable_searchOfR
  -- the set where the work force moves is `λ`-null
  have hnull : lam {s | searchG xbar Q f β θ (searchOfR s) ≠ (searchOfR s).1} = 0 :=
    ae_iff.1 hfz
  -- the frozen-rectangle bound, for `A` an `x`-set and `B = (a, b]` a `z`-interval
  have hrect : ∀ {A : Set (Icc (0 : ℝ) xbar)}, MeasurableSet A → ∀ a b : ℝ, zlo ≤ a → a < b →
      b ≤ zhi → 0 < lam (xs ⁻¹' A) →
      0 < lam (xs ⁻¹' A ∩ zs ⁻¹' {z' : Icc zlo zhi | a < (z' : ℝ) ∧ (z' : ℝ) ≤ b}) := by
    intro A hA a b ha hab hb hApos
    have hBm : MeasurableSet {z' : Icc zlo zhi | a < (z' : ℝ) ∧ (z' : ℝ) ≤ b} :=
      (measurableSet_lt measurable_const measurable_subtype_coe).inter
        (measurableSet_le measurable_subtype_coe measurable_const)
    have hc : ∀ z, ENNReal.ofReal (α * (b - a)) ≤
        kpow Q N z {z' : Icc zlo zhi | a < (z' : ℝ) ∧ (z' : ℝ) ≤ b} := fun z => by
      have := ex_8_4a Q N
      exact ENNReal.ofReal_le_of_le_toReal (hmix.2.2 z a b ha hab.le hb)
    have hcpos : 0 < ENNReal.ofReal (α * (b - a)) :=
      ENNReal.ofReal_pos.2 (mul_pos hmix.2.1 (sub_pos.2 hab))
    exact lt_of_lt_of_le (ENNReal.mul_pos hcpos.ne' hApos.ne')
      (searchFrozen_rect_ge Q hGm hinv hfz hA hBm N hc)
  -- every positive work force is below `γ` or above `δ`
  have hsplit : {s : Icc ((0 : ℝ), zlo) (xbar, zhi) | 0 < (s : ℝ × ℝ).1} ⊆
      {s | (s : ℝ × ℝ).1 < γ} ∪ {s | δ < (s : ℝ × ℝ).1} := fun s hs =>
    searchMoved Q hP hF hM h6 hθ (searchOfR s).1 hs
  have hcases : 0 < lam {s | (s : ℝ × ℝ).1 < γ} ∨ 0 < lam {s | δ < (s : ℝ × ℝ).1} := by
    by_contra h
    push Not at h
    have h0 := (measure_mono (μ := lam) hsplit).trans (measure_union_le _ _)
    rw [nonpos_iff_eq_zero.1 h.1, nonpos_iff_eq_zero.1 h.2, add_zero] at h0
    exact hpos.ne' (nonpos_iff_eq_zero.1 h0)
  rcases hcases with hlow | hhigh
  · -- below `g_C(z̄)`: some `t < γ` has `λ{x < t} > 0`
    have hU : {s : Icc ((0 : ℝ), zlo) (xbar, zhi) | (s : ℝ × ℝ).1 < γ} =
        ⋃ n : ℕ, {s : Icc ((0 : ℝ), zlo) (xbar, zhi) |
          (s : ℝ × ℝ).1 < γ - 1 / ((n : ℝ) + 1)} := by
      ext s
      simp only [mem_ofPred_eq, mem_iUnion]
      refine ⟨fun h => ?_, fun ⟨n, hn⟩ => hn.trans_le (by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith)⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      exact ⟨n, by linarith⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < lam {s | (s : ℝ × ℝ).1 < γ - 1 / ((n : ℝ) + 1)} := by
      by_contra h
      push Not at h
      rw [hU, measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (h n)] at hlow
      exact lt_irrefl _ hlow
    set t := γ - 1 / ((n : ℝ) + 1)
    have ht : t < γ := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [t]; linarith
    obtain ⟨z₁, hz₁, hz₁'⟩ := exists_searchNear_top hzlt
      (((continuous_subtype_val.comp (continuous_searchGC Q hP hF hM hθ.le)).tendsto
        topZ).eventually (lt_mem_nhds ht))
    have hA : MeasurableSet {x : Icc (0 : ℝ) xbar | (x : ℝ) < t} :=
      measurableSet_lt measurable_subtype_coe measurable_const
    have hpos' := hrect hA z₁ zhi z₁.2.1 hz₁ le_rfl hn
    refine hpos'.ne' (measure_mono_null (fun s hs => ?_) hnull)
    obtain ⟨hsx, hsz⟩ := hs
    have hxt : ((searchOfR s).1 : ℝ) < t := hsx
    have hC : t < (searchGC xbar Q f β θ (searchOfR s).2 : ℝ) :=
      hz₁'.trans_le (searchGC_mono Q hP hF hM hθ.le (show z₁ ≤ (searchOfR s).2 from hsz.1.le))
    have hle := searchGC_le_searchG Q hP hF hM hθ.le (searchOfR s)
    intro heq
    rw [heq] at hle
    have : (searchGC xbar Q f β θ (searchOfR s).2 : ℝ) ≤ (searchOfR s).1 := hle
    linarith
  · -- above `g_A(z̲)`: some `t > δ` has `λ{x > t} > 0`
    have hU : {s : Icc ((0 : ℝ), zlo) (xbar, zhi) | δ < (s : ℝ × ℝ).1} =
        ⋃ n : ℕ, {s : Icc ((0 : ℝ), zlo) (xbar, zhi) |
          δ + 1 / ((n : ℝ) + 1) < (s : ℝ × ℝ).1} := by
      ext s
      simp only [mem_ofPred_eq, mem_iUnion]
      refine ⟨fun h => ?_, fun ⟨n, hn⟩ => lt_of_le_of_lt (by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith) hn⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      exact ⟨n, by linarith⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < lam {s | δ + 1 / ((n : ℝ) + 1) < (s : ℝ × ℝ).1} := by
      by_contra h
      push Not at h
      rw [hU, measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (h n)] at hhigh
      exact lt_irrefl _ hhigh
    set t := δ + 1 / ((n : ℝ) + 1)
    have ht : δ < t := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [t]; linarith
    obtain ⟨z₂, hz₂, hz₂'⟩ := exists_searchNear_bot hzlt
      (((continuous_subtype_val.comp (continuous_searchGA Q hP hF hM hθ.le)).tendsto
        botZ).eventually (gt_mem_nhds ht))
    have hA : MeasurableSet {x : Icc (0 : ℝ) xbar | t < (x : ℝ)} :=
      measurableSet_lt measurable_const measurable_subtype_coe
    have hpos' := hrect hA zlo z₂ le_rfl hz₂ z₂.2.2 hn
    refine hpos'.ne' (measure_mono_null (fun s hs => ?_) hnull)
    obtain ⟨hsx, hsz⟩ := hs
    have hxt : t < ((searchOfR s).1 : ℝ) := hsx
    have hA' : (searchGA xbar Q f β θ (searchOfR s).2 : ℝ) < t :=
      lt_of_le_of_lt (searchGA_mono Q hP hF hM hθ.le (show (searchOfR s).2 ≤ z₂ from hsz.2))
        hz₂'
    have hle := searchG_le_searchGA Q (f := f) (β := β) (θ := θ) (searchOfR s)
    intro heq
    rw [heq] at hle
    have : ((searchOfR s).1 : ℝ) ≤ searchGA xbar Q f β θ (searchOfR s).2 := hle
    linarith

/-! ### Stochastic dominance and strict decrease of `D` -/

/-- **Stochastic dominance** (the argument of Ex. 13.8h for a general `φ`). For `0 ≤ θ ≤ θ′`, if
`T_θ*ⁿλ₀ ⇒ λ` and `T_θ′*ⁿλ₀ ⇒ λ′` for every `λ₀`, then `∫ φ dλ′ ≤ ∫ φ dλ` for every bounded
continuous nondecreasing `φ`. -/
theorem searchD_dominance (hP : SearchPrimitives zlo zhi xbar β f) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) {θ θ' : ℝ} (hθ : 0 ≤ θ) (hθθ' : θ ≤ θ')
    (hg : Measurable (searchG xbar Q f β θ)) (hg' : Measurable (searchG xbar Q f β θ'))
    {lam lam' : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi))}
    (hconv : ∀ lam₀, IsProbabilityMeasure lam₀ →
      ConvWeak (fun n => (adjointOp (searchP xbar Q f β θ hg))^[n] lam₀) lam)
    (hconv' : ∀ lam₀, IsProbabilityMeasure lam₀ →
      ConvWeak (fun n => (adjointOp (searchP xbar Q f β θ' hg'))^[n] lam₀) lam')
    (φ : Icc ((0 : ℝ), zlo) (xbar, zhi) →ᵇ ℝ) (hφ : Monotone φ) :
    ∫ s, φ s ∂lam' ≤ ∫ s, φ s ∂lam := by
  set s₀ : Icc ((0 : ℝ), zlo) (xbar, zhi) := ⟨((0 : ℝ), zlo), left_mem_Icc.2 ⟨hP.hx.le, hP.hz⟩⟩
  have h1 := hconv (Measure.dirac s₀) inferInstance φ
  have h2 := hconv' (Measure.dirac s₀) inferInstance φ
  simp only [iterate_dirac] at h1 h2
  refine le_of_tendsto_of_tendsto' h2 h1 fun n => ?_
  exact searchKernel_kpow_le Q hM _ _
    (fun s t hst => searchG_monotone Q hP hF hM hθ (searchOfR_mono hst))
    (fun s => searchG_theta_anti Q hP hF hM hθ hθθ' _) n φ.continuous.measurable (M := ‖φ‖)
    (fun s => by rw [← Real.norm_eq_abs]; exact φ.norm_coe_le_norm s) hφ s₀

/-- **Exercise 13.8h, corrected (p. 412).** Under (6) and the mixing condition, for
`0 < θ < θ′` with `D(θ) > 0`, `D(θ′) < D(θ)`. -/
theorem ex_13_8h_strict (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (h6 : SearchAssumption6 hP.hz xbar Q f β) {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ < θ')
    (hD : 0 < searchD xbar Q f β θ) : searchD xbar Q f β θ' < searchD xbar Q f β θ := by
  have hθ' : 0 < θ' := hθ.trans hθθ'
  have hg := (ex_13_8c Q hP hF hM hθ.le).measurable
  have hg' := (ex_13_8c Q hP hF hM hθ'.le).measurable
  obtain ⟨lam, hlam, hfix, huniq, hconv⟩ := ex_13_8d Q hP hzlt hF hM hmix h6 hθ hg
  obtain ⟨lam', hlam', hfix', huniq', hconv'⟩ := ex_13_8d Q hP hzlt hF hM hmix h6 hθ' hg'
  rw [searchD_eq Q hP hF hM hθ.le hg huniq] at hD ⊢
  rw [searchD_eq Q hP hF hM hθ'.le hg' huniq']
  set G : Icc ((0 : ℝ), zlo) (xbar, zhi) → ℝ := fun s => (searchG xbar Q f β θ (searchOfR s) : ℝ)
  set G' : Icc ((0 : ℝ), zlo) (xbar, zhi) → ℝ :=
    fun s => (searchG xbar Q f β θ' (searchOfR s) : ℝ)
  have hGc : Continuous G' :=
    continuous_subtype_val.comp ((ex_13_8c Q hP hF hM hθ'.le).comp continuous_searchOfR)
  have hGm : Measurable G := measurable_subtype_coe.comp (hg.comp measurable_searchOfR)
  have hGm' : Measurable G' := hGc.measurable
  have hb : ∀ (u : Icc (0 : ℝ) xbar), |(u : ℝ)| ≤ xbar := fun u => by
    rw [abs_of_nonneg u.2.1]; exact u.2.2
  have hint : Integrable G lam := integrable_of_bounded hGm fun s => hb _
  have hint' : Integrable G' lam := integrable_of_bounded hGm' fun s => hb _
  have hφx : Measurable fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (s : ℝ × ℝ).1 :=
    measurable_fst.comp measurable_subtype_coe
  have hintx : Integrable (fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (s : ℝ × ℝ).1) lam :=
    integrable_of_bounded hφx fun s => hb (searchOfR s).1
  have e1 : ∫ s, (s : ℝ × ℝ).1 ∂lam = ∫ s, G s ∂lam := searchKernel_integral_fst Q _ lam hfix
  have e1' : ∫ s, (s : ℝ × ℝ).1 ∂lam' = ∫ s, G' s ∂lam' :=
    searchKernel_integral_fst Q _ lam' hfix'
  have e2 : ∫ s, G' s ∂lam' ≤ ∫ s, G' s ∂lam :=
    searchD_dominance Q hP hF hM hθ.le hθθ'.le hg hg' hconv hconv' (mkOfCompact ⟨G', hGc⟩)
      fun s t hst => searchG_monotone Q hP hF hM hθ'.le (searchOfR_mono hst)
  have hGG : ∀ s, G' s ≤ G s := fun s => searchG_theta_anti Q hP hF hM hθ.le hθθ'.le _
  have e3 : ∫ s, G' s ∂lam ≤ ∫ s, G s ∂lam := integral_mono hint' hint hGG
  rw [e1, e1']
  refine lt_of_le_of_ne (e2.trans e3) fun heq => ?_
  have heq' : ∫ s, G' s ∂lam = ∫ s, G s ∂lam := le_antisymm e3 (heq ▸ e2)
  -- `g_θ′ = g_θ` a.e.
  have hae : ∀ᵐ s ∂lam, G s - G' s = 0 := by
    have h0 : ∫ s, (G s - G' s) ∂lam = 0 := by rw [integral_sub hint hint', heq', sub_self]
    exact (integral_eq_zero_iff_of_nonneg (fun s => sub_nonneg.2 (hGG s)) (hint.sub hint')).1 h0
  -- hence `g_θ ≤ x` a.e.
  have hle : ∀ᵐ s ∂lam, G s ≤ (s : ℝ × ℝ).1 := hae.mono fun s hs => by
    by_contra h
    push Not at h
    have hpos : 0 < G s := lt_of_le_of_lt s.2.1.1 h
    have := searchG_theta_lt Q hP hF hM hθ.le hθθ' (searchOfR s) hpos h.ne'
    have : G' s < G s := this
    linarith
  -- hence `g_θ = x` a.e.: the work force is frozen
  have hX : ∫ s, ((s : ℝ × ℝ).1 - G s) ∂lam = 0 := by rw [integral_sub hintx hint, e1, sub_self]
  have hfz0 := (integral_eq_zero_iff_of_nonneg_ae (hle.mono fun s hs => sub_nonneg.2 hs)
    (hintx.sub hint)).1 hX
  have hfz : ∀ᵐ s ∂lam, searchG xbar Q f β θ (searchOfR s) = (searchOfR s).1 :=
    hfz0.mono fun s hs => Subtype.ext (by
      have : (s : ℝ × ℝ).1 - G s = 0 := hs
      change G s = (s : ℝ × ℝ).1
      linarith)
  -- and `λ{x > 0} > 0` since `D(θ) > 0`
  have hpos : 0 < lam {s : Icc ((0 : ℝ), zlo) (xbar, zhi) | 0 < (s : ℝ × ℝ).1} := by
    rw [pos_iff_ne_zero]
    intro h0
    have hz : ∀ᵐ s ∂lam, ((s : Icc ((0 : ℝ), zlo) (xbar, zhi)) : ℝ × ℝ).1 = 0 := by
      rw [ae_iff]
      refine measure_mono_null (fun s hs => ?_) h0
      exact lt_of_le_of_ne s.2.1.1 (Ne.symm hs)
    rw [integral_congr_ae hz, integral_zero] at hD
    exact lt_irrefl _ hD
  exact searchFrozen_false Q hP hzlt hF hM hmix h6 hθ hg hfix hfz hpos

/-- **Exercise 13.8h, corrected statement.** Under (6) and the mixing condition, `D` is strictly
decreasing on `{θ > 0 : D(θ) > 0}`. (With `ex_13_8h_antitoneOn` and `ex_13_8h_zero`: `D` falls
strictly from `D(0) = x̄` until it reaches `0`, at some `θ ≤ βθ̄`, and is `0` from then on.) -/
theorem ex_13_8h_corrected (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (h6 : SearchAssumption6 hP.hz xbar Q f β) :
    StrictAntiOn (searchD xbar Q f β) {θ | 0 < θ ∧ 0 < searchD xbar Q f β θ} :=
  fun _ hθ _ _ hlt => ex_13_8h_strict Q hP hzlt hF hM hmix h6 hθ.1 hlt hθ.2

/-- **At most one positive equilibrium `θ` (p. 412).** Under (6) and the mixing condition, for
`n > 0` there is at most one `θ ≥ 0` with `D(θ) = n` (existence for `n ≤ x̄` is
`ex_13_8g_existence`). -/
theorem ex_13_8g_unique (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi)
    (hF : IsFeller Q) (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α)
    (h6 : SearchAssumption6 hP.hz xbar Q f β) {n θ₁ θ₂ : ℝ} (hn : 0 < n) (hθ₁ : 0 ≤ θ₁)
    (hθ₂ : 0 ≤ θ₂) (h₁ : searchD xbar Q f β θ₁ = n) (h₂ : searchD xbar Q f β θ₂ = n) :
    θ₁ = θ₂ := by
  -- for `0 ≤ a < b` with `D(b) > 0`, `D(b) < D(a)`
  have key : ∀ a b : ℝ, 0 ≤ a → a < b → 0 < searchD xbar Q f β b →
      searchD xbar Q f β b < searchD xbar Q f β a := by
    intro a b ha hab hb
    have hb0 : 0 < b := ha.trans_lt hab
    have hmid : 0 < b / 2 := by positivity
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · -- `a = 0`: compare through `b / 2`
      have hanti := ex_13_8h_antitoneOn Q hP hzlt hF hM hmix h6
      have h1 : searchD xbar Q f β b ≤ searchD xbar Q f β (b / 2) :=
        hanti (mem_Ici.2 hmid.le) (mem_Ici.2 hb0.le) (by linarith)
      have h2 : searchD xbar Q f β (b / 2) ≤ searchD xbar Q f β a :=
        hanti (mem_Ici.2 ha) (mem_Ici.2 hmid.le) (by rw [← ha0]; exact hmid.le)
      exact lt_of_lt_of_le
        (ex_13_8h_strict Q hP hzlt hF hM hmix h6 hmid (by linarith) (hb.trans_le h1)) h2
    · exact ex_13_8h_strict Q hP hzlt hF hM hmix h6 hapos hab
        (hb.trans_le (ex_13_8h Q hP hzlt hF hM hmix h6 hapos hab.le))
  rcases lt_trichotomy θ₁ θ₂ with h | h | h
  · have := key θ₁ θ₂ hθ₁ h (h₂ ▸ hn)
    rw [h₁, h₂] at this
    exact absurd this (lt_irrefl _)
  · exact h
  · have := key θ₂ θ₁ hθ₂ h (h₁ ▸ hn)
    rw [h₁, h₂] at this
    exact absurd this (lt_irrefl _)

end StokeyLucasPrescott.ConvergenceApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.SearchInvariant

/-!
# An equilibrium search economy with exogenous leavers (SLP Exercise 13.8e)

SLP §13.8, p. 411, Exercise 13.8e: each period a fraction `γ ∈ (0, 1)` of the island's workers
leave for idiosyncratic reasons; the invariant measure is then unique without (6).

* `searchGLeave`: the modified law of motion `x′ = (1 − γ) min{max{x, c(z)}, a(z)}` for cutoffs
  `c ≤ a` (after migration, a fraction `γ` of the work force leaves).
* `searchKernel_stay`, `searchLeave_reach`: sets of work forces that `P` never leaves, and the
  deterministic decay `x_t ≤ max{(1 − γ)ᵗ x̄, (1 − γ) c(z̄)}` from `(x̄, z̄)`.
* `searchKernel_assumption_stay`, `searchKernel_unique_stay`: Assumption 12.1 after a burn-in,
  hence Theorem 12.12.
* `searchKernel_unique_decay`: if `x′ ≤ (1 − γ) x`, the unique invariant measure is `δ₀ × μ`
  (`∫ x dλ ≤ (1 − γ) ∫ x dλ`); Theorem 12.12 does not apply there (`0` is absorbing).
* **`searchLeave_unique`**: for any continuous nondecreasing cutoffs `c ≤ a` the modified process
  has a unique invariant measure. **`ex_13_8e`**: in particular with `c = g_C`, `a = g_A` from (4),
  for every `θ ≥ 0`, with no assumption (6).

**Remarks on the manual.** The manual's argument ("`g_C(z̲) < g_C(z̄)` follows without (6)") is
incomplete: e.g. for `θ ≥ θ̄`, `g_C ≡ 0`; uniqueness still holds, by the decay argument
(`searchKernel_unique_decay`) when `c(z̄) = 0` and by a burn-in argument when `c` is constant.
The manual also lets the departures enter the value function (`v((1 − γ)x, z′)` in (4)); then
the cutoffs of (5a), (5c) need not lie in `[0, x̄]` (`β ∫ v((1 − γ)x̄, z′) Q(z, dz′)` can exceed
`θ`), so `X` would have to be enlarged; that variant is not formalised, but `searchLeave_unique`
applies to any cutoffs it produces in `X`. Here the departures are not anticipated in (4).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

variable {zlo zhi xbar : ℝ} (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) [IsMarkovKernel Q]
  {G : Icc ((0 : ℝ), zlo) (xbar, zhi) → Icc (0 : ℝ) xbar} (hG : Measurable G)

/-! ### Staying in a set of work forces -/

omit [IsMarkovKernel Q] in
/-- One step lands in `{x ∈ U}` for sure when `G(s) ∈ U`. -/
theorem searchKernel_fst_mem [IsMarkovKernel Q] {U : Set (Icc (0 : ℝ) xbar)}
    (hU : MeasurableSet U) (s : Icc ((0 : ℝ), zlo) (xbar, zhi)) (hs : G s ∈ U) :
    (searchKernel Q G hG s).real ((fun s' => (searchOfR s').1) ⁻¹' U) = 1 := by
  have := searchKernel_rect Q hG hU MeasurableSet.univ s hs
  rw [preimage_univ, inter_univ, measure_univ] at this
  rw [measureReal_def, this, ENNReal.toReal_one]

/-- If `G` maps `{x ∈ U}` into `U`, then `Pⁿ(s, {x ∈ U}) = 1` for `s` with `x ∈ U`. -/
theorem searchKernel_stay {U : Set (Icc (0 : ℝ) xbar)} (hU : MeasurableSet U)
    (hstay : ∀ s, (searchOfR s).1 ∈ U → G s ∈ U) (n : ℕ) (s : Icc ((0 : ℝ), zlo) (xbar, zhi))
    (hs : (searchOfR s).1 ∈ U) :
    1 ≤ (kpow (searchKernel Q G hG) n s).real ((fun s' => (searchOfR s').1) ⁻¹' U) := by
  have := isMarkovKernel_searchKernel Q hG
  have hXU : MeasurableSet ((fun s' : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s').1) ⁻¹' U) :=
    (measurable_fst.comp measurable_searchOfR) hU
  induction n generalizing s with
  | zero =>
    simp only [kpow, Kernel.id_apply]
    rw [measureReal_def, Measure.dirac_apply_of_mem (show s ∈ _ from hs), ENNReal.toReal_one]
  | succ n ih =>
    have := searchKpow_add_ge (searchKernel Q G hG) (n := n) (m := 1) hXU hXU zero_le_one
      (ih s hs) fun s' hs' => by
        rw [kpow_one, searchKernel_fst_mem Q hG hU s' (hstay s' hs')]
    simpa using this

/-! ### Assumption 12.1 after a burn-in -/

omit [IsMarkovKernel Q] in
/-- `λ(A ∩ B) ≥ λ(A) + λ(B) − 1` for a probability measure. -/
theorem searchProb_inter_ge {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] {A B : Set S} (hB : MeasurableSet B) :
    μ.real A + μ.real B - 1 ≤ μ.real (A ∩ B) := by
  have h := measureReal_union_add_inter (μ := μ) (s := A) hB
  have h1 : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
  linarith

/-- **Assumption 12.1 for `P` after a burn-in.** As `searchKernel_assumption`, but the upper
bound `G(s) ≤ c_x` (for `z ≤ z₂`) is only required on a set `{x ∈ U}` that `P` never leaves and
that the process started at `(x̄, z̄)` has entered by time `T₀`. -/
theorem searchKernel_assumption_stay (hzlt : zlo < zhi) (hF : IsFeller Q) (hM : IsMonotoneTF Q)
    {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α) (hab : ((0 : ℝ), zlo) ≤ (xbar, zhi))
    (cx : Icc (0 : ℝ) xbar) {z₁ z₂ : Icc zlo zhi} (hz₁ : (z₁ : ℝ) < zhi) (hz₂ : zlo < (z₂ : ℝ))
    {U : Set (Icc (0 : ℝ) xbar)} (hU : MeasurableSet U) {T₀ : ℕ}
    (hreach : 1 ≤ (kpow (searchKernel Q G hG) T₀ ⟨(xbar, zhi), right_mem_Icc.2 hab⟩).real
      ((fun s => (searchOfR s).1) ⁻¹' U))
    (hstay : ∀ s, (searchOfR s).1 ∈ U → G s ∈ U)
    (hlow : ∀ s, (searchOfR s).1 ∈ U → (searchOfR s).2 ≤ z₂ → G s ≤ cx)
    (hhigh : ∀ s, z₁ ≤ (searchOfR s).2 → cx ≤ G s) :
    ∃ (c : Icc ((0 : ℝ), zlo) (xbar, zhi)) (ε : ℝ), 0 < ε ∧
      ε ≤ (kpow (searchKernel Q G hG) (T₀ + N + 1) ⟨((0 : ℝ), zlo), left_mem_Icc.2 hab⟩).real
        (Ici c) ∧
      ε ≤ (kpow (searchKernel Q G hG) (T₀ + N + 1) ⟨(xbar, zhi), right_mem_Icc.2 hab⟩).real
        (Iic c) := by
  have := isMarkovKernel_searchKernel Q hG
  have := ex_8_4a (searchKernel Q G hG) (T₀ + N)
  have := ex_8_4a Q (T₀ + N)
  have := ex_8_4a Q T₀
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
  -- `Qᵀ⁰⁺ᴺ` satisfies the mixing bound
  have hmixT : ∀ (z : Icc zlo zhi) {B : Set (Icc zlo zhi)}, MeasurableSet B → ∀ {e : ℝ}, 0 ≤ e →
      (∀ z', e ≤ (kpow Q N z').real B) → e ≤ (kpow Q (T₀ + N) z).real B := fun z B hB e he h => by
    have := searchKpow_add_ge Q (n := T₀) (m := N) (s := z) MeasurableSet.univ hB zero_le_one
      (by rw [probReal_univ]) fun z' _ => h z'
    simpa using this
  set q₁ := (Q w₁).real {z' : Icc zlo zhi | cz < (z' : ℝ)}
  set q₂ := (Q w₂).real {z' : Icc zlo zhi | (z' : ℝ) < cz}
  have hbot : α * (zhi - y₁) * q₁ ≤
      (kpow (searchKernel Q G hG) (T₀ + N + 1) ⟨((0 : ℝ), zlo), left_mem_Icc.2 hab⟩).real
        (Ici c) := by
    refine searchKpow_add_ge _ (hzm (measurableSet_Ici (a := y₁))) measurableSet_Ici
      (mul_nonneg hmix.2.1.le (sub_pos.2 hy₁).le) ?_ fun s' hs' => ?_
    · rw [measureReal_def, kpow_searchKernel_snd Q hG _ measurableSet_Ici, ← measureReal_def]
      exact hmixT _ measurableSet_Ici (mul_nonneg hmix.2.1.le (sub_pos.2 hy₁).le) fun z' =>
        (hmix.2.2 z' y₁ zhi y₁.2.1 hy₁.le le_rfl).trans
          (measureReal_mono fun z'' h => le_of_lt h.1)
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
  have htop : α * (y₂ - zlo) * q₂ ≤
      (kpow (searchKernel Q G hG) (T₀ + N + 1) ⟨(xbar, zhi), right_mem_Icc.2 hab⟩).real
        (Iic c) := by
    have hXU := hxm hU
    have hZ := hzm (measurableSet_Iic (a := y₂))
    refine searchKpow_add_ge _ (hXU.inter hZ) measurableSet_Iic
      (mul_nonneg hmix.2.1.le (sub_pos.2 hy₂).le) ?_ fun s' hs' => ?_
    · have hU1 : 1 ≤ (kpow (searchKernel Q G hG) (T₀ + N) ⟨(xbar, zhi), right_mem_Icc.2 hab⟩).real
          ((fun s => (searchOfR s).1) ⁻¹' U) := by
        have := searchKpow_add_ge (searchKernel Q G hG) (n := T₀) (m := N) hXU hXU zero_le_one
          hreach fun s' hs' => searchKernel_stay Q hG hU hstay N s' hs'
        simpa using this
      have hZ1 : α * (y₂ - zlo) ≤
          (kpow (searchKernel Q G hG) (T₀ + N) ⟨(xbar, zhi), right_mem_Icc.2 hab⟩).real
            ((fun s => (searchOfR s).2) ⁻¹' Iic y₂) := by
        rw [measureReal_def, kpow_searchKernel_snd Q hG _ measurableSet_Iic, ← measureReal_def]
        exact hmixT _ measurableSet_Iic (mul_nonneg hmix.2.1.le (sub_pos.2 hy₂).le) fun z' =>
          (hmix.2.2 z' zlo y₂ le_rfl hy₂.le y₂.2.2).trans (measureReal_mono fun z'' h => h.2)
      linarith [searchProb_inter_ge (kpow (searchKernel Q G hG) (T₀ + N)
        ⟨(xbar, zhi), right_mem_Icc.2 hab⟩) (A := (fun s => (searchOfR s).1) ⁻¹' U) hZ]
    · rw [kpow_one]
      have hs'' : (searchOfR s').2 ≤ y₂ := hs'.2
      have hrect := searchKernel_rect Q hG measurableSet_Iic (measurableSet_Iic (a := cZ)) s'
        (hlow s' hs'.1 (hs''.trans (min_le_left z₂ w₂)))
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

/-- **Theorem 12.12 for `P` after a burn-in** (`searchKernel_assumption_stay`). -/
theorem searchKernel_unique_stay (hzlt : zlo < zhi) (hF : IsFeller Q) (hM : IsMonotoneTF Q)
    {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α) (hab : ((0 : ℝ), zlo) ≤ (xbar, zhi))
    (hGm : Monotone G) (hGc : Continuous G)
    (cx : Icc (0 : ℝ) xbar) {z₁ z₂ : Icc zlo zhi} (hz₁ : (z₁ : ℝ) < zhi) (hz₂ : zlo < (z₂ : ℝ))
    {U : Set (Icc (0 : ℝ) xbar)} (hU : MeasurableSet U) {T₀ : ℕ}
    (hreach : 1 ≤ (kpow (searchKernel Q G hG) T₀ ⟨(xbar, zhi), right_mem_Icc.2 hab⟩).real
      ((fun s => (searchOfR s).1) ⁻¹' U))
    (hstay : ∀ s, (searchOfR s).1 ∈ U → G s ∈ U)
    (hlow : ∀ s, (searchOfR s).1 ∈ U → (searchOfR s).2 ≤ z₂ → G s ≤ cx)
    (hhigh : ∀ s, z₁ ≤ (searchOfR s).2 → cx ≤ G s) :
    ∃ μ : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)), IsProbabilityMeasure μ ∧
      adjointOp (searchKernel Q G hG) μ = μ ∧
      ∀ ν, IsProbabilityMeasure ν → adjointOp (searchKernel Q G hG) ν = ν → ν = μ := by
  have := isMarkovKernel_searchKernel Q hG
  obtain ⟨c, ε, hε, hbot, htop⟩ := searchKernel_assumption_stay Q hG hzlt hF hM hmix hab cx hz₁
    hz₂ hU hreach hstay hlow hhigh
  obtain ⟨μ, hμ, hfix, huniq, -⟩ := theorem_12_12_prod hab _
    (isMonotoneTF_searchKernel Q hG hM hGm) (isFeller_searchKernel Q hG hF hGc) hε (by omega)
    hbot htop
  exact ⟨μ, hμ, hfix, huniq⟩

/-- **Uniqueness when the work force decays.** If `G(s) ≤ (1 − γ) x` with `γ > 0`, every
invariant measure has `∫ x dλ = ∫ G dλ ≤ (1 − γ) ∫ x dλ`, so it lives on `{x = 0}`; it is then
`δ₀ × ν` with `ν` invariant for `Q`, hence unique under the mixing condition. (Assumption 12.1
fails here when `0` is absorbing, so Theorem 12.12 does not apply.) -/
theorem searchKernel_unique_decay (hzlt : zlo < zhi) (hF : IsFeller Q) (hM : IsMonotoneTF Q)
    {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α) (hx : 0 ≤ xbar) {γ : ℝ} (hγ : 0 < γ)
    (hdecay : ∀ s, (G s : ℝ) ≤ (1 - γ) * (searchOfR s).1) :
    ∃ μ : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)), IsProbabilityMeasure μ ∧
      adjointOp (searchKernel Q G hG) μ = μ ∧
      ∀ ν, IsProbabilityMeasure ν → adjointOp (searchKernel Q G hG) ν = ν → ν = μ := by
  have := isMarkovKernel_searchKernel Q hG
  obtain ⟨μQ, hμQ, hfixQ, huniqQ⟩ := searchQ_unique Q hzlt hF hM hmix
  set x0 : Icc (0 : ℝ) xbar := ⟨0, le_rfl, hx⟩
  have hG0 : ∀ z, G (searchToR (x0, z)) = x0 := fun z => by
    refine Subtype.ext (le_antisymm ?_ (G _).2.1)
    have := hdecay (searchToR (x0, z))
    simp only [searchOfR_toR, x0, mul_zero] at this
    exact this
  have hinv := searchDiracProd_invariant Q hG x0 hG0 μQ hfixQ
  have : IsProbabilityMeasure (searchDiracProd x0 μQ) := by
    unfold searchDiracProd; infer_instance
  refine ⟨_, this, hinv, fun ν hν hνfix => ?_⟩
  have hφ : Measurable fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (s : ℝ × ℝ).1 :=
    measurable_fst.comp measurable_subtype_coe
  have hφi : Integrable (fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (s : ℝ × ℝ).1) ν :=
    integrable_of_bounded hφ (M := xbar) fun s => by
      rw [abs_of_nonneg s.2.1.1]; exact s.2.2.1
  have hGi : Integrable (fun s => (G s : ℝ)) ν :=
    integrable_of_bounded (measurable_subtype_coe.comp hG) (M := xbar) fun s => by
      rw [abs_of_nonneg (G s).2.1]; exact (G s).2.2
  have hmean := searchKernel_integral_fst Q hG ν hνfix
  have hle : ∫ s, (G s : ℝ) ∂ν ≤ (1 - γ) * ∫ s, (s : ℝ × ℝ).1 ∂ν := by
    rw [← integral_const_mul]
    exact integral_mono hGi (hφi.const_mul _) fun s => hdecay s
  have hnn : 0 ≤ fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (s : ℝ × ℝ).1 := fun s => s.2.1.1
  have h0 : ∫ s, (s : ℝ × ℝ).1 ∂ν = 0 := by
    have := integral_nonneg hnn (μ := ν)
    nlinarith
  have hae := (integral_eq_zero_iff_of_nonneg hnn hφi).1 h0
  have hzm : Measurable fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s).2 :=
    measurable_snd.comp measurable_searchOfR
  have hm : Measurable fun z : Icc zlo zhi => searchToR (x0, z) :=
    measurable_searchToR.comp measurable_prodMk_left
  -- `ν = δ₀ × ν_z`
  have hν : ν = searchDiracProd x0 (ν.map fun s => (searchOfR s).2) := by
    rw [searchDiracProd, Measure.map_map hm hzm]
    conv_lhs => rw [← Measure.map_id (μ := ν)]
    refine Measure.map_congr ?_
    filter_upwards [hae] with s hs
    refine Subtype.ext (Prod.ext ?_ rfl)
    change (s : ℝ × ℝ).1 = 0
    simpa using hs
  -- `ν_z` is invariant for `Q`
  have hνz : adjointOp Q (ν.map fun s => (searchOfR s).2) = ν.map fun s => (searchOfR s).2 := by
    ext B hB
    rw [adjointOp_apply _ _ hB, lintegral_map (Kernel.measurable_coe _ hB) hzm,
      Measure.map_apply hzm hB]
    have : ∀ s, Q (searchOfR s).2 B = searchKernel Q G hG s ((fun s => (searchOfR s).2) ⁻¹' B) :=
      fun s => by
        have := kpow_searchKernel_snd Q hG 1 hB s
        rw [kpow_one, kpow_one] at this
        exact this.symm
    simp_rw [this]
    rw [← adjointOp_apply _ _ (hzm hB), hνfix]
  have : IsProbabilityMeasure (ν.map fun s => (searchOfR s).2) := inferInstance
  rw [hν, huniqQ _ this hνz]

/-! ### The modified law of motion -/

/-- `x ↦ (1 − γ) x` on `X = [0, x̄]`. -/
def searchShrink (γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) (x : Icc (0 : ℝ) xbar) : Icc (0 : ℝ) xbar :=
  ⟨(1 - γ) * x, mul_nonneg (sub_nonneg.2 hγ.2) x.2.1,
    (mul_le_of_le_one_left x.2.1 (by linarith [hγ.1])).trans x.2.2⟩

/-- **Exercise 13.8e** (the modified law of motion): after migration the work force is
`min{max{x, c(z)}, a(z)}` (cutoffs `c ≤ a`), and then a fraction `γ` leaves for idiosyncratic
reasons, so next period's work force is `(1 − γ) min{max{x, c(z)}, a(z)}`. -/
def searchGLeave (γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) (c a : Icc zlo zhi → Icc (0 : ℝ) xbar)
    (s : Icc ((0 : ℝ), zlo) (xbar, zhi)) : Icc (0 : ℝ) xbar :=
  searchShrink γ hγ (min (max (searchOfR s).1 (c (searchOfR s).2)) (a (searchOfR s).2))

/-- The modified law of motion in coordinates. -/
theorem searchGLeave_coe (γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) (c a : Icc zlo zhi → Icc (0 : ℝ) xbar)
    (s : Icc ((0 : ℝ), zlo) (xbar, zhi)) :
    (searchGLeave γ hγ c a s : ℝ) =
      (1 - γ) * min (max ((searchOfR s).1 : ℝ) (c (searchOfR s).2)) (a (searchOfR s).2) := by
  simp [searchGLeave, searchShrink]

/-- The modified law of motion is continuous when the cutoffs are. -/
theorem continuous_searchGLeave (γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1)
    {c a : Icc zlo zhi → Icc (0 : ℝ) xbar} (hc : Continuous c) (ha : Continuous a) :
    Continuous (searchGLeave γ hγ c a) := by
  have h : Continuous fun s : Icc ((0 : ℝ), zlo) (xbar, zhi) =>
      min (max (searchOfR s).1 (c (searchOfR s).2)) (a (searchOfR s).2) :=
    ((continuous_fst.comp continuous_searchOfR).max
      (hc.comp (continuous_snd.comp continuous_searchOfR))).min
      (ha.comp (continuous_snd.comp continuous_searchOfR))
  exact Continuous.subtype_mk (continuous_const.mul (continuous_subtype_val.comp h)) _

/-- The modified law of motion is nondecreasing when the cutoffs are. -/
theorem monotone_searchGLeave (γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1)
    {c a : Icc zlo zhi → Icc (0 : ℝ) xbar} (hc : Monotone c) (ha : Monotone a) :
    Monotone (searchGLeave γ hγ c a) := fun s t hst => by
  have h1 := searchOfR_mono hst
  change (searchGLeave γ hγ c a s : ℝ) ≤ searchGLeave γ hγ c a t
  rw [searchGLeave_coe, searchGLeave_coe]
  refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 hγ.2)
  exact min_le_min (max_le_max h1.1 (hc h1.2)) (ha h1.2)

omit [IsMarkovKernel Q] in
/-- From `(x̄, z̄)`, if `G(s) ≤ (1 − γ) max{x, c*}`, then after `t` periods
`x ≤ max{(1 − γ)ᵗ x̄, (1 − γ) c*}` for sure. -/
theorem searchLeave_reach [IsMarkovKernel Q] {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) {cs : ℝ}
    (hcs : 0 ≤ cs) (hle : ∀ s, (G s : ℝ) ≤ (1 - γ) * max ((searchOfR s).1 : ℝ) cs)
    (hab : ((0 : ℝ), zlo) ≤ (xbar, zhi)) (t : ℕ) :
    1 ≤ (kpow (searchKernel Q G hG) t ⟨(xbar, zhi), right_mem_Icc.2 hab⟩).real
      ((fun s => (searchOfR s).1) ⁻¹'
        {x : Icc (0 : ℝ) xbar | (x : ℝ) ≤ max ((1 - γ) ^ t * xbar) ((1 - γ) * cs)}) := by
  have := isMarkovKernel_searchKernel Q hG
  have ha : 0 ≤ 1 - γ := sub_nonneg.2 hγ.2
  have hU : ∀ b : ℝ, MeasurableSet {x : Icc (0 : ℝ) xbar | (x : ℝ) ≤ b} := fun b =>
    measurableSet_le measurable_subtype_coe measurable_const
  have hxm : Measurable fun s' : Icc ((0 : ℝ), zlo) (xbar, zhi) => (searchOfR s').1 :=
    measurable_fst.comp measurable_searchOfR
  induction t with
  | zero =>
    have hmem : (⟨(xbar, zhi), right_mem_Icc.2 hab⟩ : Icc ((0 : ℝ), zlo) (xbar, zhi)) ∈
        (fun s => (searchOfR s).1) ⁻¹'
          {x : Icc (0 : ℝ) xbar | (x : ℝ) ≤ max ((1 - γ) ^ 0 * xbar) ((1 - γ) * cs)} := by
      change xbar ≤ max ((1 - γ) ^ 0 * xbar) ((1 - γ) * cs)
      rw [pow_zero, one_mul]
      exact le_max_left _ _
    simp only [kpow, Kernel.id_apply]
    rw [measureReal_def, Measure.dirac_apply_of_mem hmem, ENNReal.toReal_one]
  | succ t ih =>
    have := searchKpow_add_ge (searchKernel Q G hG) (n := t) (m := 1) (hxm (hU _)) (hxm (hU _))
      zero_le_one ih fun s' hs' => by
        have hs'' : ((searchOfR s').1 : ℝ) ≤ max ((1 - γ) ^ t * xbar) ((1 - γ) * cs) := hs'
        have hmem : G s' ∈ {x : Icc (0 : ℝ) xbar |
            (x : ℝ) ≤ max ((1 - γ) ^ (t + 1) * xbar) ((1 - γ) * cs)} := by
          change (G s' : ℝ) ≤ _
          refine (hle s').trans ?_
          rw [pow_succ, mul_comm ((1 - γ) ^ t) (1 - γ), mul_assoc, ← mul_max_of_nonneg _ _ ha]
          refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) ha
          · refine hs''.trans (max_le (le_max_left _ _) ?_)
            exact (mul_le_of_le_one_left hcs (by linarith [hγ.1])).trans (le_max_right _ _)
          · exact le_max_right _ _
        rw [kpow_one, searchKernel_fst_mem Q hG (hU _) s' hmem]
    simpa using this

/-- **Exercise 13.8e** (general form). Let `c ≤ a` be continuous nondecreasing cutoffs and
`0 < γ < 1`. The law of motion `x′ = (1 − γ) min{max{x, c(z)}, a(z)}` has a unique invariant
measure, with no assumption like (6). With `c* = c(z̄)`:
* `c* = 0`: no immigration ever, `x′ ≤ (1 − γ)x`, and the invariant measure is `δ₀ × μ`
  (`searchKernel_unique_decay`);
* `c* > 0`: after a burn-in `x ≤ b < c*` for sure, so Assumption 12.1 holds with the mixing point
  `c_x = (1 − γ) b` (`searchKernel_unique_stay`), where `b = c*` if `c` is constant and
  `b ∈ (c(z̲), c*)` otherwise. -/
theorem searchLeave_unique (hzlt : zlo < zhi) (hF : IsFeller Q) (hM : IsMonotoneTF Q)
    {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α) (hx : 0 < xbar) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1)
    {c a : Icc zlo zhi → Icc (0 : ℝ) xbar} (hc : Continuous c) (ha : Continuous a)
    (hcm : Monotone c) (ham : Monotone a) (hca : ∀ z, c z ≤ a z)
    (hG : Measurable (searchGLeave γ ⟨hγ.1.le, hγ.2.le⟩ c a)) :
    ∃ μ : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)), IsProbabilityMeasure μ ∧
      adjointOp (searchKernel Q (searchGLeave γ ⟨hγ.1.le, hγ.2.le⟩ c a) hG) μ = μ ∧
      ∀ ν, IsProbabilityMeasure ν →
        adjointOp (searchKernel Q (searchGLeave γ ⟨hγ.1.le, hγ.2.le⟩ c a) hG) ν = ν → ν = μ := by
  set G := searchGLeave γ ⟨hγ.1.le, hγ.2.le⟩ c a
  have hab : ((0 : ℝ), zlo) ≤ (xbar, zhi) := ⟨hx.le, hzlt.le⟩
  have h1γ : 0 < 1 - γ := sub_pos.2 hγ.2
  set botZ : Icc zlo zhi := ⟨zlo, le_rfl, hzlt.le⟩
  set topZ : Icc zlo zhi := ⟨zhi, hzlt.le, le_rfl⟩
  set cs : ℝ := (c topZ : ℝ)
  have hcs0 : 0 ≤ cs := (c topZ).2.1
  have hcle : ∀ z, (c z : ℝ) ≤ cs := fun z => hcm z.2.2
  have hcoe : ∀ s, (G s : ℝ) =
      (1 - γ) * min (max ((searchOfR s).1 : ℝ) (c (searchOfR s).2)) (a (searchOfR s).2) :=
    fun s => searchGLeave_coe γ _ c a s
  have hGle : ∀ s, (G s : ℝ) ≤ (1 - γ) * max ((searchOfR s).1 : ℝ) (c (searchOfR s).2) :=
    fun s => by
      rw [hcoe]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) h1γ.le
  have hGge : ∀ s, (1 - γ) * (c (searchOfR s).2 : ℝ) ≤ G s := fun s => by
    rw [hcoe]
    exact mul_le_mul_of_nonneg_left (le_min (le_max_right _ _) (hca _)) h1γ.le
  have hGle' : ∀ s, (G s : ℝ) ≤ (1 - γ) * max ((searchOfR s).1 : ℝ) cs := fun s =>
    (hGle s).trans (mul_le_mul_of_nonneg_left (max_le_max le_rfl (hcle _)) h1γ.le)
  have hGm := monotone_searchGLeave γ ⟨hγ.1.le, hγ.2.le⟩ hcm ham
  have hGc := continuous_searchGLeave γ ⟨hγ.1.le, hγ.2.le⟩ hc ha
  have hU : ∀ b : ℝ, MeasurableSet {x : Icc (0 : ℝ) xbar | (x : ℝ) ≤ b} := fun b =>
    measurableSet_le measurable_subtype_coe measurable_const
  -- burn-in: from `(x̄, z̄)` the work force falls below any `b > (1 − γ) c*`, `b > 0`
  have hreach : ∀ b : ℝ, 0 < b → (1 - γ) * cs ≤ b → ∃ T₀ : ℕ,
      1 ≤ (kpow (searchKernel Q G hG) T₀ ⟨(xbar, zhi), right_mem_Icc.2 hab⟩).real
        ((fun s => (searchOfR s).1) ⁻¹' {x : Icc (0 : ℝ) xbar | (x : ℝ) ≤ b}) := by
    intro b hb hcb
    obtain ⟨T₀, hT₀⟩ := exists_pow_lt_of_lt_one (div_pos hb hx) (show 1 - γ < 1 by linarith [hγ.1])
    have := isMarkovKernel_searchKernel Q hG
    have := ex_8_4a (searchKernel Q G hG) T₀
    refine ⟨T₀, (searchLeave_reach Q hG ⟨hγ.1.le, hγ.2.le⟩ hcs0 hGle' hab T₀).trans
      (measureReal_mono fun s hs => ?_)⟩
    change ((searchOfR s).1 : ℝ) ≤ b
    have hs' : ((searchOfR s).1 : ℝ) ≤ max ((1 - γ) ^ T₀ * xbar) ((1 - γ) * cs) := hs
    refine hs'.trans (max_le ?_ hcb)
    rw [lt_div_iff₀ hx] at hT₀
    exact hT₀.le
  by_cases hpos : 0 < cs
  · by_cases hconst : (c botZ : ℝ) = cs
    · -- `c` is constant: `b = c*`
      have hcz : ∀ z, (c z : ℝ) = cs := fun z =>
        le_antisymm (hcle z) (hconst ▸ hcm (show botZ ≤ z from z.2.1))
      obtain ⟨T₀, hT₀⟩ := hreach cs hpos (mul_le_of_le_one_left hcs0 (by linarith [hγ.1]))
      set cx : Icc (0 : ℝ) xbar := ⟨(1 - γ) * cs, mul_nonneg h1γ.le hcs0,
        (mul_le_of_le_one_left hcs0 (by linarith [hγ.1])).trans (c topZ).2.2⟩
      refine searchKernel_unique_stay Q hG hzlt hF hM hmix hab hGm hGc cx (z₁ := botZ)
        (z₂ := topZ) hzlt hzlt (hU cs) hT₀ (fun s hs => ?_) (fun s hs _ => ?_) (fun s _ => ?_)
      · have hs' : ((searchOfR s).1 : ℝ) ≤ cs := hs
        change (G s : ℝ) ≤ cs
        refine (hGle' s).trans ?_
        rw [max_eq_right hs']
        exact mul_le_of_le_one_left hcs0 (by linarith [hγ.1])
      · have hs' : ((searchOfR s).1 : ℝ) ≤ cs := hs
        change (G s : ℝ) ≤ (1 - γ) * cs
        refine (hGle' s).trans ?_
        rw [max_eq_right hs']
      · change (1 - γ) * cs ≤ (G s : ℝ)
        rw [← hcz (searchOfR s).2]
        exact hGge s
    · -- `c(z̲) < c*`: `b ∈ (c(z̲), c*)`
      have hlt : (c botZ : ℝ) < cs := lt_of_le_of_ne (hcle botZ) hconst
      set ε := min (γ * cs) (cs - c botZ) / 2
      have hε : 0 < ε := by
        have : 0 < min (γ * cs) (cs - c botZ) := lt_min (mul_pos hγ.1 hpos) (sub_pos.2 hlt)
        simp only [ε]; linarith
      have hε1 : ε ≤ γ * cs / 2 := by
        simp only [ε]; linarith [min_le_left (γ * cs) (cs - c botZ)]
      have hε2 : ε ≤ (cs - c botZ) / 2 := by
        simp only [ε]; linarith [min_le_right (γ * cs) (cs - c botZ)]
      set b := cs - ε
      have hb1 : (c botZ : ℝ) < b := by simp only [b]; linarith
      have hb2 : b < cs := by simp only [b]; linarith
      have hb3 : (1 - γ) * cs ≤ b := by simp only [b]; nlinarith [hγ.1]
      have hb0 : 0 < b := lt_of_le_of_lt (c botZ).2.1 hb1
      obtain ⟨T₀, hT₀⟩ := hreach b hb0 hb3
      obtain ⟨z₂, hz₂, hz₂'⟩ := exists_searchNear_bot hzlt
        (((continuous_subtype_val.comp hc).tendsto botZ).eventually (gt_mem_nhds hb1))
      obtain ⟨z₁, hz₁, hz₁'⟩ := exists_searchNear_top hzlt
        (((continuous_subtype_val.comp hc).tendsto topZ).eventually (lt_mem_nhds hb2))
      set cx : Icc (0 : ℝ) xbar := ⟨(1 - γ) * b, mul_nonneg h1γ.le hb0.le,
        (mul_le_of_le_one_left hb0.le (by linarith [hγ.1])).trans
          (hb2.le.trans (c topZ).2.2)⟩
      refine searchKernel_unique_stay Q hG hzlt hF hM hmix hab hGm hGc cx hz₁ hz₂ (hU b) hT₀
        (fun s hs => ?_) (fun s hs hz => ?_) (fun s hz => ?_)
      · have hs' : ((searchOfR s).1 : ℝ) ≤ b := hs
        change (G s : ℝ) ≤ b
        refine (hGle' s).trans ?_
        rw [max_eq_right (hs'.trans hb2.le)]
        exact hb3
      · have hs' : ((searchOfR s).1 : ℝ) ≤ b := hs
        change (G s : ℝ) ≤ (1 - γ) * b
        refine (hGle s).trans (mul_le_mul_of_nonneg_left (max_le hs' ?_) h1γ.le)
        exact (show (c (searchOfR s).2 : ℝ) ≤ c z₂ from hcm hz).trans hz₂'.le
      · change (1 - γ) * b ≤ (G s : ℝ)
        refine le_trans ?_ (hGge s)
        exact mul_le_mul_of_nonneg_left
          (hz₁'.le.trans (show (c z₁ : ℝ) ≤ c (searchOfR s).2 from hcm hz)) h1γ.le
  · -- `c* = 0`: no immigration, the work force decays to `0`
    have hcs : cs = 0 := le_antisymm (not_lt.1 hpos) hcs0
    refine searchKernel_unique_decay Q hG hzlt hF hM hmix hx.le hγ.1 fun s => ?_
    refine (hGle' s).trans ?_
    rw [hcs, max_eq_left ((searchOfR s).1.2.1)]

variable {β : ℝ} {f : ℝ → ℝ → ℝ} [Nonempty (Icc (0 : ℝ) xbar)]

/-- **Exercise 13.8e.** In the model of §13.8 modified so that, each period after migration, a
fraction `γ ∈ (0, 1)` of the island's workers leave for idiosyncratic reasons
(`x′ = (1 − γ) g_θ(x, z)`), the invariant measure is unique for every `θ ≥ 0`, without (6). -/
theorem ex_13_8e (hP : SearchPrimitives zlo zhi xbar β f) (hzlt : zlo < zhi) (hF : IsFeller Q)
    (hM : IsMonotoneTF Q) {N : ℕ} {α : ℝ} (hmix : SearchMixing Q N α) {θ : ℝ} (hθ : 0 ≤ θ)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hG : Measurable (searchGLeave γ ⟨hγ.1.le, hγ.2.le⟩ (searchGC xbar Q f β θ)
      (searchGA xbar Q f β θ))) :
    ∃ μ : Measure (Icc ((0 : ℝ), zlo) (xbar, zhi)), IsProbabilityMeasure μ ∧
      adjointOp (searchKernel Q _ hG) μ = μ ∧
      ∀ ν, IsProbabilityMeasure ν → adjointOp (searchKernel Q _ hG) ν = ν → ν = μ :=
  searchLeave_unique Q hzlt hF hM hmix hP.hx hγ (continuous_searchGC Q hP hF hM hθ)
    (continuous_searchGA Q hP hF hM hθ) (searchGC_mono Q hP hF hM hθ)
    (searchGA_mono Q hP hF hM hθ) (searchGC_le_searchGA Q hP hF hM hθ) hG

end StokeyLucasPrescott.ConvergenceApplications

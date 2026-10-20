/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.IndustryModel
import EquilibriumApplications.LinftyTimeState

/-!
# Assumption 15.8′ fails for the industry production set (NOTE to Exercise 16.4(e))

SLP §16.4, p. 491, and §15.4, p. 470. Theorem 15.9 (`theorem_15_9`) would give `L¹` prices for
the industry economy if Assumptions 15.8′ and 15.9′ held. This module shows that **Assumption
15.8′ fails** for the production set `Y` of (1), in the project's formulation
`Assumption15_8'` on the time–state space `LinftyTimeState`.

* The example: every period's shock space is `[0, 1]` with Lebesgue measure (`indLinftyMeasure`);
  the filtration `indFiltration` is trivial at `t = 0` (so `q₀, I₀, k₁` are constants, as in the
  book) and Borel afterwards; `k₀ = 1`.
* Two goods per period are encoded as consecutive coordinates of `LinftyTimeState`:
  coordinate `2t` is `q_t` and coordinate `2t + 1` is `I_t`. `indLinftyTech c δ` is the set of
  elements having a representative `(q, I) ∈ Y` (`IndustryTech`), i.e. `Y` read on equivalence
  classes ("all `z^t`" read as "a.e.").
* `indLinftyPlan`: the plan `k ≡ 1`, `q ≡ 1`, `I ≡ c(1)`; it lies in `Y`.
* `indNullSeq`: `A_n = [0, 1/(n+1)] ↓ 0`, and `μ(A_n) > 0`.
* `industry_trunc_not_mem`: for every `n`, truncating investment `I₁` on `A_n` (coordinate 3)
  leaves `Y`: on `A_n`, `I₁ = 0` forces `k₂ = (1 − δ)k₁ = 1 − δ < 1 = q₂`, on a set of positive
  measure.
* **Counterexample** `industry_not_assumption15_8'`: `¬ Assumption15_8' μ X Y` for every `X`.

So Theorems 15.4–15.6 together with Theorem 15.9 cannot be used to obtain the inner-product
prices `p_t ∈ L¹` of Exercise 16.4(c) (`IndustryWelfare`, module docstring). The same plan also
refutes the book's two-goods-at-once reading of 15.8′ (zeroing `(q₁, I₁)` on `A_n`), by the same
computation.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set

/-- The per-period probability `μ^t`: Lebesgue measure on `[0, 1]`. -/
noncomputable abbrev indLinftyMeasure : ℕ → Measure ℝ := fun _ => volume.restrict (Icc 0 1)

/-- The filtration: trivial at `t = 0`, Borel afterwards. -/
noncomputable def indFiltration : Filtration ℕ (inferInstance : MeasurableSpace ℝ) :=
  ⟨fun t => if t = 0 then ⊥ else inferInstance, fun i j hij => by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      simp only [↓reduceIte]
      exact bot_le
    · have hj : j ≠ 0 := by omega
      simp only [hi.ne', hj, ↓reduceIte]
      exact le_rfl, fun t => by
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      simp only [↓reduceIte]
      exact bot_le
    · simp only [ht.ne', ↓reduceIte]
      exact le_rfl⟩

/-- The production set `Y` on equivalence classes: `x ∈ L` (coordinate `2t` = `q_t`, `2t + 1` =
`I_t`) with a representative `(q, I) ∈ Y`, `k₀ = 1`. -/
def indLinftyTech (c : ℝ → ℝ) (δ : ℝ) : Set (LinftyTimeState indLinftyMeasure) :=
  {x | ∃ q I : ℕ → ℝ → ℝ, (q, I) ∈ IndustryTech indFiltration c δ 1 ∧
    ∀ t, (x (2 * t) : ℝ → ℝ) =ᵐ[volume.restrict (Icc 0 1)] q t ∧
      (x (2 * t + 1) : ℝ → ℝ) =ᵐ[volume.restrict (Icc 0 1)] I t}

/-- The constant `L∞` class of `a`. -/
noncomputable def indConstLp (a : ℝ) : Lp ℝ ⊤ (volume.restrict (Icc (0 : ℝ) 1)) :=
  MemLp.toLp (fun _ => a) (memLp_top_const a)

/-- The plan `q ≡ 1`, `I ≡ c(1)` as an element of `LinftyTimeState`. -/
noncomputable def indLinftyPlan (c : ℝ → ℝ) : LinftyTimeState indLinftyMeasure :=
  ⟨fun n => indConstLp (if n % 2 = 0 then 1 else c 1), memℓp_infty ⟨max 1 |c 1|, by
    rintro _ ⟨n, rfl⟩
    refine norm_linfty_le_of_ae_abs_le (le_trans zero_le_one (le_max_left _ _)) ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_top_const (μ := volume.restrict (Icc (0 : ℝ) 1))
      (if n % 2 = 0 then (1 : ℝ) else c 1))] with ω hω
    rw [indConstLp, hω]
    split_ifs
    · simp
    · exact le_max_right _ _⟩⟩

variable {c : ℝ → ℝ} {δ : ℝ}

/-- The plan `k ≡ 1`, `q ≡ 1`, `I ≡ c(1)` lies in `Y`. -/
theorem indLinftyPlan_mem (hc : IndustryCost c δ) : indLinftyPlan c ∈ indLinftyTech c δ := by
  have h1 := hc.one_pos
  refine ⟨fun _ _ => 1, fun _ _ => c 1, ⟨⟨fun _ => ⟨stronglyMeasurable_const,
    stronglyMeasurable_const⟩, max 1 (c 1), fun _ _ => ⟨by simp, by
      rw [abs_of_pos h1]; exact le_max_right _ _⟩⟩, fun _ _ => ⟨zero_le_one, h1.le⟩,
    fun _ _ => 1, fun _ => rfl, fun _ => stronglyMeasurable_const, ⟨1, fun _ _ => by simp⟩,
    fun _ _ => ⟨by linarith [hc.delta_pos], le_rfl, by simp⟩⟩, fun t => ⟨?_, ?_⟩⟩
  · change (indConstLp (if 2 * t % 2 = 0 then 1 else c 1) : ℝ → ℝ) =ᵐ[_] _
    simp only [Nat.mul_mod_right, ↓reduceIte]
    exact MemLp.coeFn_toLp _
  · change (indConstLp (if (2 * t + 1) % 2 = 0 then 1 else c 1) : ℝ → ℝ) =ᵐ[_] _
    have : (2 * t + 1) % 2 = 1 := by omega
    simp only [this, one_ne_zero, ↓reduceIte]
    exact MemLp.coeFn_toLp _

/-- The events `A_n = [0, 1/(n+1)]`. -/
def indNullSets (n : ℕ) : Set ℝ := Icc 0 (1 / ((n : ℝ) + 1))

/-- `A_n ↓ 0` (in period 3, as in every period). -/
theorem indNullSeq : LinftyNullSeq (indLinftyMeasure 3) indNullSets := by
  refine ⟨fun _ => measurableSet_Icc, fun m n hmn => Icc_subset_Icc le_rfl ?_, ?_⟩
  · have : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    gcongr
  · have hle : ∀ n : ℕ, indLinftyMeasure 3 (indNullSets n) = ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      fun n => by
        simp only [indLinftyMeasure, indNullSets]
        rw [Measure.restrict_apply measurableSet_Icc, Icc_inter_Icc, max_self,
          min_eq_left (by rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n :
            (0 : ℝ) ≤ n)]), Real.volume_Icc, sub_zero]
    simp_rw [hle]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat

/-- `μ(A_n) > 0`. -/
theorem indNullSets_pos (n : ℕ) : 0 < volume.restrict (Icc (0 : ℝ) 1) (indNullSets n) := by
  simp only [indNullSets]
  rw [Measure.restrict_apply measurableSet_Icc, Icc_inter_Icc, max_self,
    min_eq_left (by rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n :
      (0 : ℝ) ≤ n)]), Real.volume_Icc, sub_zero]
  exact ENNReal.ofReal_pos.2 (by positivity)

/-- **Truncating investment `I₁` on `A_n` leaves `Y`**, for every `n`. -/
theorem industry_trunc_not_mem (hc : IndustryCost c δ) (n : ℕ) :
    linftyPeriodTrunc 3 (indNullSets n) (indLinftyPlan c) ∉ indLinftyTech c δ := by
  rintro ⟨q, I, ⟨-, -, k, hk0, -, -, hk⟩, hx⟩
  dsimp only at hk
  set ν := volume.restrict (Icc (0 : ℝ) 1)
  have hδ := hc.delta_pos
  have hδ1 := hc.delta_lt_one
  -- coordinate 1 (`I₀`), 3 (`I₁`, truncated) and 4 (`q₂`)
  have hI0 : ∀ᵐ ω ∂ν, I 0 ω = c 1 := by
    have h := (hx 0).2
    rw [linftyPeriodTrunc_apply_of_ne (by norm_num)] at h
    filter_upwards [h, MemLp.coeFn_toLp (memLp_top_const (μ := ν) (c 1))] with ω h1 h2
    rw [← h1]
    change (indConstLp (if (2 * 0 + 1) % 2 = 0 then 1 else c 1) : ℝ → ℝ) ω = c 1
    simp only [Nat.mul_zero, zero_add, Nat.one_mod, one_ne_zero, ↓reduceIte]
    exact h2
  have hq2 : ∀ᵐ ω ∂ν, q 2 ω = 1 := by
    have h := (hx 2).1
    rw [linftyPeriodTrunc_apply_of_ne (by norm_num)] at h
    filter_upwards [h, MemLp.coeFn_toLp (memLp_top_const (μ := ν) (1 : ℝ))] with ω h1 h2
    rw [← h1]
    change (indConstLp (if 2 * 2 % 2 = 0 then 1 else c 1) : ℝ → ℝ) ω = 1
    simp only [Nat.mul_mod_right, ↓reduceIte]
    exact h2
  have hI1 : ∀ᵐ ω ∂ν, ω ∈ indNullSets n → I 1 ω = 0 := by
    have h := (hx 1).2
    rw [linftyPeriodTrunc_apply_self] at h
    filter_upwards [h, coeFn_linftyRestrict (μ := ν) (B := (indNullSets n)ᶜ)
      measurableSet_Icc.compl (indLinftyPlan c 3)] with ω h1 h2 hω
    rw [← h1]
    change (linftyRestrict ν (indNullSets n)ᶜ (indLinftyPlan c 3) : ℝ → ℝ) ω = 0
    rw [h2, indicator_of_notMem (by simpa using hω)]
  have hnull : ∀ᵐ ω ∂ν, ω ∉ indNullSets n := by
    filter_upwards [hI0, hq2, hI1] with ω h0 h2 h1 hω
    have e1 := (hk 0 ω).2.2
    have e2 := (hk 1 ω).2.2
    have d1 := (hk 0 ω).1
    have d2 := (hk 1 ω).1
    have q2 := (hk 2 ω).2.1
    rw [hk0] at e1 d1
    rw [h0, one_mul, div_one] at e1
    have hk1 : k 1 ω = 1 := hc.strictMono.injOn (mem_Ici.2 (by linarith))
      (mem_Ici.2 (by linarith)) e1.symm
    rw [h1 hω, hk1, one_mul, div_one] at e2
    rw [hk1] at d2
    have hk2 : k 2 ω = 1 - δ := hc.strictMono.injOn (mem_Ici.2 (by linarith))
      (mem_Ici.2 le_rfl) (by rw [← e2, hc.at_one_sub])
    rw [h2, hk2] at q2
    linarith
  have := indNullSets_pos n
  rw [measure_eq_zero_iff_ae_notMem.2 hnull] at this
  exact lt_irrefl _ this

/-- **Counterexample** (NOTE to Ex 16.4(e)): **Assumption 15.8′ fails** for the industry
production set, for any consumption sets `X`. -/
theorem industry_not_assumption15_8' (hc : IndustryCost c δ)
    (X : Unit → Set (LinftyTimeState indLinftyMeasure)) :
    ¬ Assumption15_8' indLinftyMeasure X fun _ : Unit => indLinftyTech c δ := by
  rintro ⟨-, hY⟩
  obtain ⟨n, hn⟩ := (hY () 3 (indLinftyPlan c) (indLinftyPlan_mem hc) indNullSets
    indNullSeq).exists
  exact industry_trunc_not_mem hc n hn

end StokeyLucasPrescott.EquilibriumApplications

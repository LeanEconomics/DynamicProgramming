/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.LILLower

/-!
# The law of the iterated logarithm for i.i.d. sequences (Hartman–Wintner)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/IIDLIL.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

The LIL of MT p. 422: a real sequence `sₙ` obeys the LIL with constant `γ ≥ 0` when the limit
superior of `sₙ/√(2 n log log n)` is `γ` and the limit inferior is `−γ`. It is stated here in the
`ε`-form, which needs no boundedness side conditions (`LILBound`, `HasLIL`): for every `ε > 0`,
eventually `sₙ ≤ (γ + ε) √(2 n log log n)` and frequently `sₙ ≥ (γ − ε) √(2 n log log n)`, and the
same for `−sₙ`. The book normalises by `√(2 γ² n log log n)` and asks the limits `±1`, which is the
same statement when `γ > 0`.

* **The Hartman–Wintner LIL** (`hasLIL_iid`): for i.i.d. centred `Xⱼ ∈ L²` with `σ² = E[X₀²]`,
  almost surely `Sₙ = Σ_{j<n} Xⱼ` obeys the LIL with constant `σ` (including `σ = 0`). This is the
  i.i.d. LIL that MT uses (via the cycle sums) for Theorems 17.2.2 and 17.3.6.
* `lilBound_iid`: one half, `LILBound S σ` almost surely.
* `HasLIL.limsup_eq`, `HasLIL.liminf_eq`: the `Filter.limsup`/`Filter.liminf` form of `HasLIL`;
  `limsup_liminf_iid`: almost surely `limsup Sₙ/√(2 n log log n) = σ` and `liminf = −σ`.

The upper half is `lil_upper` (`LILUpper`), the lower half `lil_lower_normalized` (`LILLower`).
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-- One half of the LIL with constant `γ`: for every `ε > 0`, eventually
`sₙ ≤ (γ + ε) √(2 n log log n)`, and frequently `sₙ ≥ (γ − ε) √(2 n log log n)`. -/
def LILBound (s : ℕ → ℝ) (γ : ℝ) : Prop :=
  ∀ ε > 0, (∀ᶠ n in atTop, s n ≤ (γ + ε) * lilScale n) ∧
    ∃ᶠ n in atTop, (γ - ε) * lilScale n ≤ s n

/-- **The LIL** with constant `γ` (MT p. 422, in `ε`-form): `LILBound s γ` and
`LILBound (−s) γ`, that is `limsup sₙ/√(2 n log log n) = γ` and `liminf = −γ`. -/
def HasLIL (s : ℕ → ℝ) (γ : ℝ) : Prop :=
  LILBound s γ ∧ LILBound (fun n => -s n) γ

/-- `LILBound` follows from its instances along `ε = 1/(k + 1)`. -/
theorem lilBound_of_nat {s : ℕ → ℝ} {γ : ℝ}
    (h : ∀ k : ℕ, (∀ᶠ n in atTop, s n ≤ (γ + 1 / ((k : ℝ) + 1)) * lilScale n) ∧
      ∃ᶠ n in atTop, (γ - 1 / ((k : ℝ) + 1)) * lilScale n ≤ s n) :
    LILBound s γ := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨h1, h2⟩ := h k
  refine ⟨h1.mono fun n hn => hn.trans ?_, h2.mono fun n hn => le_trans ?_ hn⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (lilScale_nonneg n)
  · exact mul_le_mul_of_nonneg_right (by linarith) (lilScale_nonneg n)

/-- **One half of the Hartman–Wintner LIL**: for i.i.d. centred `Xⱼ ∈ L²` with
`σ = √(E[X₀²])`, almost surely `Sₙ = Σ_{j<n} Xⱼ` satisfies `LILBound S σ`. -/
theorem lilBound_iid {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hm : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q) (hL2 : MemLp (X 0) 2 Q)
    (h0 : ∫ ω, X 0 ω ∂Q = 0) :
    ∀ᵐ ω ∂Q, LILBound (fun n => ∑ j ∈ Finset.range n, X j ω) (√(∫ ω, X 0 ω ^ 2 ∂Q)) := by
  set σ := √(∫ ω, X 0 ω ^ 2 ∂Q) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = ∫ ω, X 0 ω ^ 2 ∂Q := Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)
  -- the upper halves for `X` and `−X`
  have hup : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∀ᶠ n in atTop,
      ∑ j ∈ Finset.range n, X j ω ≤ (σ + 1 / ((k : ℝ) + 1)) * lilScale n :=
    ae_all_iff.2 fun k => lil_upper hind hm hident hL2 h0 (by positivity)
  have hind' : iIndepFun (fun j ω => -X j ω) Q := hind.comp (fun _ x => -x) fun _ => measurable_neg
  have hident' : ∀ j, IdentDistrib (fun ω => -X j ω) (fun ω => -X 0 ω) Q Q := fun j =>
    (hident j).comp measurable_neg
  have h0' : ∫ ω, -X 0 ω ∂Q = 0 := by rw [integral_neg, h0, neg_zero]
  have hsq : √(∫ ω, (-X 0 ω) ^ 2 ∂Q) = σ := by simp_rw [neg_sq]; exact hσ.symm
  have hupneg : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∀ᶠ n in atTop,
      ∑ j ∈ Finset.range n, -X j ω ≤ (σ + 1 / ((k : ℝ) + 1)) * lilScale n := by
    refine ae_all_iff.2 fun k => ?_
    have h := lil_upper (X := fun j ω => -X j ω) hind' (fun j => (hm j).neg) hident' hL2.neg h0'
      (ε := 1 / ((k : ℝ) + 1)) (by positivity)
    rwa [hsq] at h
  rcases eq_or_lt_of_le hσ0 with hσz | hσpos
  · -- `σ = 0`: the upper half for `−X` gives the lower half
    filter_upwards [hup, hupneg] with ω hω1 hω2
    refine lilBound_of_nat fun k => ⟨hω1 k, ?_⟩
    refine ((hω2 k).mono fun n hn => ?_).frequently
    rw [Finset.sum_neg_distrib] at hn
    rw [← hσz] at hn ⊢
    have : (0 - 1 / ((k : ℝ) + 1)) * lilScale n = -((0 + 1 / ((k : ℝ) + 1)) * lilScale n) := by
      ring
    rw [this]
    linarith
  · -- `σ > 0`: the lower half for `X/σ`
    set Y : ℕ → Ω → ℝ := fun j ω => σ⁻¹ * X j ω with hY
    have hYind : iIndepFun Y Q :=
      hind.comp (fun _ x => σ⁻¹ * x) fun _ => measurable_id.const_mul σ⁻¹
    have hYm : ∀ j, Measurable (Y j) := fun j => (hm j).const_mul σ⁻¹
    have hYident : ∀ j, IdentDistrib (Y j) (Y 0) Q Q := fun j =>
      (hident j).comp (measurable_id.const_mul σ⁻¹)
    have hY0 : ∫ ω, Y 0 ω ∂Q = 0 := by
      simp only [hY]; rw [integral_const_mul, h0, mul_zero]
    have hY1 : ∫ ω, Y 0 ω ^ 2 ∂Q = 1 := by
      simp only [hY, mul_pow]
      rw [integral_const_mul, ← hσ2, inv_pow, inv_mul_cancel₀ (by positivity)]
    have hlow : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∃ᶠ n in atTop,
        (1 - 1 / ((k : ℝ) + 2)) * lilScale n ≤ ∑ j ∈ Finset.range n, Y j ω := by
      refine ae_all_iff.2 fun k => ?_
      have hk : 1 / ((k : ℝ) + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; have := Nat.cast_nonneg (α := ℝ) k; linarith
      exact lil_lower_normalized hYind hYm hYident (hL2.const_mul σ⁻¹) hY0 hY1 (by positivity) hk
    filter_upwards [hup, hlow] with ω hω1 hω2
    intro ε hε
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      refine (hω1 k).mono fun n hn => hn.trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (lilScale_nonneg n)
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε / σ by positivity)
      refine (hω2 k).mono fun n hn => ?_
      have hsum : ∑ j ∈ Finset.range n, X j ω = σ * ∑ j ∈ Finset.range n, Y j ω := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hY]; field_simp
      change (σ - ε) * lilScale n ≤ ∑ j ∈ Finset.range n, X j ω
      rw [hsum]
      have h1 : σ * (1 / ((k : ℝ) + 2)) ≤ ε := by
        have h2 : 1 / ((k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        have h3 : 1 / ((k : ℝ) + 1) < ε / σ := hk
        rw [lt_div_iff₀ hσpos] at h3
        nlinarith
      calc (σ - ε) * lilScale n ≤ σ * ((1 - 1 / ((k : ℝ) + 2)) * lilScale n) := by
            have := lilScale_nonneg n
            nlinarith
        _ ≤ σ * ∑ j ∈ Finset.range n, Y j ω := mul_le_mul_of_nonneg_left hn hσpos.le

/-- **The Hartman–Wintner law of the iterated logarithm**: for i.i.d. centred `Xⱼ ∈ L²` with
`σ² = E[X₀²]`, almost surely `limsup Sₙ/√(2 n log log n) = σ` and `liminf = −σ`
(in `ε`-form, `HasLIL`). -/
theorem hasLIL_iid {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hm : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q) (hL2 : MemLp (X 0) 2 Q)
    (h0 : ∫ ω, X 0 ω ∂Q = 0) :
    ∀ᵐ ω ∂Q, HasLIL (fun n => ∑ j ∈ Finset.range n, X j ω) (√(∫ ω, X 0 ω ^ 2 ∂Q)) := by
  have h1 := lilBound_iid hind hm hident hL2 h0
  have h2 := lilBound_iid (X := fun j ω => -X j ω)
    (hind.comp (fun _ x => -x) fun _ => measurable_neg) (fun j => (hm j).neg)
    (fun j => (hident j).comp measurable_neg) hL2.neg (by rw [integral_neg, h0, neg_zero])
  have hsq : √(∫ ω, (-X 0 ω) ^ 2 ∂Q) = √(∫ ω, X 0 ω ^ 2 ∂Q) := by simp_rw [neg_sq]
  rw [hsq] at h2
  filter_upwards [h1, h2] with ω hω1 hω2
  refine ⟨hω1, ?_⟩
  simpa only [Finset.sum_neg_distrib] using hω2

/-! ### The `limsup`/`liminf` form -/

/-- Under `LILBound s γ`, eventually `sₙ/√(2 n log log n) ≤ γ + ε`, and frequently
`sₙ/√(2 n log log n) ≥ γ − ε`. -/
theorem LILBound.div {s : ℕ → ℝ} {γ : ℝ} (h : LILBound s γ) {ε : ℝ} (hε : 0 < ε) :
    (∀ᶠ n in atTop, s n / lilScale n ≤ γ + ε) ∧ ∃ᶠ n in atTop, γ - ε ≤ s n / lilScale n := by
  obtain ⟨h1, h2⟩ := h ε hε
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < lilScale n := by
    filter_upwards [eventually_le_log 3] with n hn using lilScale_pos hn
  refine ⟨?_, ?_⟩
  · filter_upwards [h1, hpos] with n hn hp
    rwa [div_le_iff₀ hp]
  · refine (h2.and_eventually hpos).mono fun n hn => ?_
    rw [le_div_iff₀ hn.2]; exact hn.1

/-- **The LIL in `limsup` form**: under `HasLIL s γ`, `limsup sₙ/√(2 n log log n) = γ`. -/
theorem HasLIL.limsup_eq {s : ℕ → ℝ} {γ : ℝ} (h : HasLIL s γ) :
    limsup (fun n => s n / lilScale n) atTop = γ := by
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => s n / lilScale n) :=
    isBoundedUnder_of_eventually_le (h.1.div one_pos).1
  have hcb : IsCoboundedUnder (· ≤ ·) atTop (fun n => s n / lilScale n) := by
    refine IsBoundedUnder.isCoboundedUnder_le (isBoundedUnder_of_eventually_ge
      (a := -(γ + 1)) ?_)
    filter_upwards [(h.2.div one_pos).1] with n hn
    rw [neg_div] at hn
    linarith
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_of_forall_pos_le_add fun ε hε => ?_)
  · exact limsup_le_of_le hcb (h.1.div hε).1
  · have := le_limsup_of_frequently_le (h.1.div hε).2 hb
    linarith

/-- **The LIL in `liminf` form**: under `HasLIL s γ`, `liminf sₙ/√(2 n log log n) = −γ`. -/
theorem HasLIL.liminf_eq {s : ℕ → ℝ} {γ : ℝ} (h : HasLIL s γ) :
    liminf (fun n => s n / lilScale n) atTop = -γ := by
  have hlow : ∀ ε > 0, ∀ᶠ n in atTop, -γ - ε ≤ s n / lilScale n := fun ε hε => by
    filter_upwards [(h.2.div hε).1] with n hn
    rw [neg_div] at hn
    linarith
  have hfr : ∀ ε > 0, ∃ᶠ n in atTop, s n / lilScale n ≤ -γ + ε := fun ε hε =>
    (h.2.div hε).2.mono fun n hn => by
      rw [neg_div] at hn
      linarith
  have hb : IsBoundedUnder (· ≥ ·) atTop (fun n => s n / lilScale n) :=
    isBoundedUnder_of_eventually_ge (hlow 1 one_pos)
  have hcb : IsCoboundedUnder (· ≥ ·) atTop (fun n => s n / lilScale n) :=
    IsBoundedUnder.isCoboundedUnder_ge (isBoundedUnder_of_eventually_le (h.1.div one_pos).1)
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_of_forall_pos_le_add fun ε hε => ?_)
  · exact liminf_le_of_frequently_le (hfr ε hε) hb
  · have := le_liminf_of_le hcb (hlow ε hε)
    linarith

/-- **The Hartman–Wintner LIL in `limsup`/`liminf` form**: for i.i.d. centred `Xⱼ ∈ L²` with
`σ² = E[X₀²]`, almost surely `limsup Sₙ/√(2 n log log n) = σ` and
`liminf Sₙ/√(2 n log log n) = −σ`. -/
theorem limsup_liminf_iid {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (hL2 : MemLp (X 0) 2 Q) (h0 : ∫ ω, X 0 ω ∂Q = 0) :
    ∀ᵐ ω ∂Q, limsup (fun n => (∑ j ∈ Finset.range n, X j ω) / lilScale n) atTop =
        √(∫ ω, X 0 ω ^ 2 ∂Q) ∧
      liminf (fun n => (∑ j ∈ Finset.range n, X j ω) / lilScale n) atTop =
        -√(∫ ω, X 0 ω ^ 2 ∂Q) := by
  filter_upwards [hasLIL_iid hind hm hident hL2 h0] with ω hω
  exact ⟨hω.limsup_eq, hω.liminf_eq⟩

end MeynTweedie.GeneralizedDrift

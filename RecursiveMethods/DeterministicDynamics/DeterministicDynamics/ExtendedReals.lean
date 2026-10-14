/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Extended real numbers for the sequence problem

SLP §4.1 lets the supremum function `v*` and the objective `u` take the values `±∞`. They take
values in `EReal`, where the needed algebra is collected here.

* `addIso`, `mulIso`: `z ↦ c + z` and `z ↦ βz` (`β > 0`) are order isomorphisms of `EReal`, so
  they commute with suprema and are continuous.
* `add_mul_biSup`: `c + β ⨆ᵢ gᵢ = ⨆ᵢ (c + βgᵢ)` for real `c`, `β ≥ 0` and a nonempty index set.
* `coe_mul_add`: `b(d + e) = bd + be` for real `b ≥ 0` and `d`.
* `le_of_le_add_limsup`, `le_of_add_le_liminf`: passing to the limit in `a ≤ sₙ + wₙ` and
  `sₙ + wₙ ≤ a` when `sₙ` converges and `wₙ` is asymptotically `≤ 0` (resp. `≥ 0`).
* `eq_biSup_iff`: the book's description of a supremum in `R̄` through the three cases
  "finite", `+∞` and `−∞` (SLP (2)–(3) and (4)–(7), pp. 70–71).
-/

open Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

/-- `z ↦ c + z` is an order isomorphism of `EReal`. -/
noncomputable def addIso (c : ℝ) : EReal ≃o EReal where
  toFun z := (c : EReal) + z
  invFun z := ((-c : ℝ) : EReal) + z
  left_inv z := by
    induction z with
    | bot => simp
    | top => simp
    | coe z => simp only [← EReal.coe_add]; congr 1; ring
  right_inv z := by
    induction z with
    | bot => simp
    | top => simp
    | coe z => simp only [← EReal.coe_add]; congr 1; ring
  map_rel_iff' {x y} := by
    simp only [Equiv.coe_fn_mk]
    constructor
    · intro h
      have := add_le_add (le_refl ((-c : ℝ) : EReal)) h
      rwa [← add_assoc, ← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add,
        zero_add] at this
    · exact fun h => add_le_add (le_refl _) h

theorem addIso_apply (c : ℝ) (z : EReal) : addIso c z = (c : EReal) + z := rfl

/-- `z ↦ βz` is an order isomorphism of `EReal` for `β > 0`. -/
noncomputable def mulIso (β : ℝ) (hβ : 0 < β) : EReal ≃o EReal where
  toFun z := (β : EReal) * z
  invFun z := ((β⁻¹ : ℝ) : EReal) * z
  left_inv z := by
    simp only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hβ.ne', EReal.coe_one, one_mul]
  right_inv z := by
    simp only [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hβ.ne', EReal.coe_one, one_mul]
  map_rel_iff' {x y} := by
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_left h (show (0 : EReal) ≤ ((β⁻¹ : ℝ) : EReal) from
        EReal.coe_nonneg.2 (inv_nonneg.2 hβ.le))
      simpa only [Equiv.coe_fn_mk, ← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hβ.ne',
        EReal.coe_one, one_mul] using this
    · intro h
      exact mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.2 hβ.le)

theorem mulIso_apply (β : ℝ) (hβ : 0 < β) (z : EReal) : mulIso β hβ z = (β : EReal) * z := rfl

/-- `c + β ⨆_{i ∈ s} gᵢ = ⨆_{i ∈ s} (c + βgᵢ)` for real `c`, `β ≥ 0`, `s` nonempty. -/
theorem add_mul_biSup {ι : Type*} (c β : ℝ) (hβ : 0 ≤ β) {s : Set ι} (hs : s.Nonempty)
    (g : ι → EReal) :
    (c : EReal) + (β : EReal) * ⨆ i ∈ s, g i = ⨆ i ∈ s, ((c : EReal) + (β : EReal) * g i) := by
  rcases hβ.eq_or_lt with h0 | hpos
  · subst h0
    simp only [EReal.coe_zero, zero_mul, add_zero]
    exact (biSup_const hs).symm
  · have h1 : (β : EReal) * ⨆ i ∈ s, g i = ⨆ i ∈ s, (β : EReal) * g i :=
      map_iSup₂ (mulIso β hpos) fun i _ => g i
    have h2 : (c : EReal) + ⨆ i ∈ s, (β : EReal) * g i =
        ⨆ i ∈ s, ((c : EReal) + (β : EReal) * g i) :=
      map_iSup₂ (addIso c) fun i _ => (β : EReal) * g i
    rw [h1, h2]

/-- `z ↦ c + βz` is continuous on `EReal` for real `c` and `β ≥ 0`. -/
theorem continuous_add_mul (c β : ℝ) (hβ : 0 ≤ β) :
    Continuous fun z : EReal => (c : EReal) + (β : EReal) * z := by
  rcases hβ.eq_or_lt with h0 | hpos
  · subst h0
    simp only [EReal.coe_zero, zero_mul, add_zero]
    exact continuous_const
  · exact (addIso c).continuous.comp (mulIso β hpos).continuous

/-- `b(d + e) = bd + be` for real `b ≥ 0` and real `d`. -/
theorem coe_mul_add (b d : ℝ) (hb : 0 ≤ b) (e : EReal) :
    (b : EReal) * ((d : EReal) + e) = (b : EReal) * d + (b : EReal) * e := by
  rcases hb.eq_or_lt with h0 | hpos
  · subst h0; simp
  · induction e with
    | bot => simp [EReal.coe_mul_bot_of_pos hpos]
    | top => simp [EReal.coe_mul_top_of_pos hpos, ← EReal.coe_mul]
    | coe e => simp only [← EReal.coe_add, ← EReal.coe_mul]; congr 1; ring

/-- If `a ≤ sₙ + wₙ` for all `n`, `sₙ → L` and `limsup wₙ ≤ 0`, then `a ≤ L`. -/
theorem le_of_le_add_limsup {a L : EReal} {s w : ℕ → EReal} (h : ∀ n, a ≤ s n + w n)
    (hs : Tendsto s atTop (𝓝 L)) (hw : limsup w atTop ≤ 0) : a ≤ L := by
  by_contra hlt
  push Not at hlt
  obtain ⟨p, hLp, hpa⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  obtain ⟨q, hpq, hqa⟩ := EReal.lt_iff_exists_real_btwn.1 hpa
  have hpq' : p < q := EReal.coe_lt_coe_iff.1 hpq
  have h1 : ∀ᶠ n in atTop, s n < p := hs.eventually (gt_mem_nhds hLp)
  have h2 : ∀ᶠ n in atTop, w n < ((q - p : ℝ) : EReal) :=
    eventually_lt_of_limsup_lt (hw.trans_lt (EReal.coe_lt_coe_iff.2 (by linarith)))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have := EReal.add_lt_add hn1 hn2
  rw [← EReal.coe_add, show p + (q - p) = q by ring] at this
  exact absurd ((h n).trans_lt (this.trans hqa)) (lt_irrefl a)

/-- If `sₙ + wₙ ≤ a` for all `n`, `sₙ → L` and `liminf wₙ ≥ 0`, then `L ≤ a`. -/
theorem le_of_add_le_liminf {a L : EReal} {s w : ℕ → EReal} (h : ∀ n, s n + w n ≤ a)
    (hs : Tendsto s atTop (𝓝 L)) (hw : 0 ≤ liminf w atTop) : L ≤ a := by
  by_contra hlt
  push Not at hlt
  obtain ⟨p, hap, hpL⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  obtain ⟨q, hpq, hqL⟩ := EReal.lt_iff_exists_real_btwn.1 hpL
  have hpq' : p < q := EReal.coe_lt_coe_iff.1 hpq
  have h1 : ∀ᶠ n in atTop, (q : EReal) < s n := hs.eventually (lt_mem_nhds hqL)
  have h2 : ∀ᶠ n in atTop, ((p - q : ℝ) : EReal) < w n :=
    eventually_lt_of_lt_liminf ((EReal.coe_lt_coe_iff.2 (by linarith)).trans_le hw)
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have := EReal.add_lt_add hn1 hn2
  rw [← EReal.coe_add, show q + (p - q) = p by ring] at this
  exact absurd ((hap.trans this).trans_le (h n)) (lt_irrefl a)

/-- `v ≤ w` as soon as every real `a < v` satisfies `a ≤ w`. -/
theorem le_of_forall_coe_lt_le {v w : EReal} (h : ∀ a : ℝ, (a : EReal) < v → (a : EReal) ≤ w) :
    v ≤ w := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, hwa, hav⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  exact absurd (h a hav) (not_le.2 hwa)

/-- **The book's description of a supremum** (SLP (2)–(3), (4)–(7), pp. 70–71):
`v = ⨆_{i ∈ s} fᵢ` iff (a) when `v` is finite, `fᵢ ≤ v` for all `i ∈ s` and `v ≤ fᵢ + ε` for
some `i ∈ s`, for every `ε > 0`; (b) when `v = +∞`, some sequence in `s` has `f → +∞`; and
(c) when `v = −∞`, every `fᵢ = −∞`. -/
theorem eq_biSup_iff {ι : Type*} {s : Set ι} {f : ι → EReal} {v : EReal} :
    v = ⨆ i ∈ s, f i ↔
      (∀ r : ℝ, v = r → (∀ i ∈ s, f i ≤ r) ∧ ∀ ε > (0 : ℝ), ∃ i ∈ s, (r : EReal) ≤ f i + ε) ∧
      (v = ⊤ → ∃ i : ℕ → ι, (∀ k, i k ∈ s) ∧ Tendsto (fun k => f (i k)) atTop (𝓝 ⊤)) ∧
      (v = ⊥ → ∀ i ∈ s, f i = ⊥) := by
  constructor
  · rintro rfl
    refine ⟨fun r hr => ⟨fun i hi => hr ▸ le_biSup f hi, fun ε hε => ?_⟩, fun htop => ?_,
      fun hbot i hi => le_bot_iff.1 (hbot ▸ le_biSup f hi)⟩
    · have hlt : ((r - ε : ℝ) : EReal) < ⨆ i ∈ s, f i := by
        rw [hr]; exact EReal.coe_lt_coe_iff.2 (by linarith)
      obtain ⟨i, hi, hfi⟩ := lt_biSup_iff.1 hlt
      refine ⟨i, hi, ?_⟩
      have := add_le_add hfi.le (le_refl (ε : EReal))
      rwa [← EReal.coe_add, sub_add_cancel] at this
    · have hk : ∀ k : ℕ, ∃ i ∈ s, ((k : ℝ) : EReal) < f i := fun k =>
        lt_biSup_iff.1 (htop ▸ EReal.coe_lt_top (k : ℝ))
      choose i hi hfi using hk
      refine ⟨i, hi, EReal.tendsto_nhds_top_iff_real.2 fun x => ?_⟩
      obtain ⟨k, hk⟩ := exists_nat_gt x
      filter_upwards [eventually_ge_atTop k] with m hm
      exact (EReal.coe_lt_coe_iff.2 (hk.trans_le (Nat.cast_le.2 hm))).trans (hfi m)
  · rintro ⟨hfin, htop, hbot⟩
    induction v with
    | bot => exact (le_bot_iff.1 (iSup₂_le fun i hi => (hbot rfl i hi).le)).symm
    | top =>
      obtain ⟨i, hi, hlim⟩ := htop rfl
      refine (top_le_iff.1 ?_).symm
      refine le_of_tendsto' hlim fun k => le_biSup f (hi k)
    | coe r =>
      obtain ⟨hle, happ⟩ := hfin r rfl
      refine le_antisymm ?_ (iSup₂_le hle)
      refine le_of_forall_coe_lt_le fun a ha => ?_
      have hε : (0 : ℝ) < r - a := sub_pos.2 (EReal.coe_lt_coe_iff.1 ha)
      obtain ⟨i, hi, hri⟩ := happ (r - a) hε
      have h1 : f i ≤ ⨆ j ∈ s, f j := le_biSup f hi
      by_contra hS
      push Not at hS
      -- `f i ≤ S < a`, so `f i + (r − a) < r`
      have h2 := EReal.add_lt_add_right_coe (h1.trans_lt hS) (r - a)
      rw [← EReal.coe_add, add_sub_cancel] at h2
      exact absurd (hri.trans_lt h2) (lt_irrefl _)

end StokeyLucasPrescott.DeterministicDynamics

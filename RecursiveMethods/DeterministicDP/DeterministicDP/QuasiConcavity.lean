/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.ConstantReturns
import DeterministicDP.Concavity

/-!
# Homogeneous quasi-concave functions

SLP Exercise 4.8a–b, pp. 91–92. `X` is a convex cone in a real normed space.

* `IsQuasiConcaveS`, `IsStrictQuasiConcaveS`: the book's definitions (p. 91).
* `ex_4_8a`: a homogeneous quasi-concave function that is positive off the origin is concave.
  `ex_4_8a_counterexample`: positivity cannot be dropped. On `ℝ²₊`,
  `f(x, y) = max{x − y, 2(x − y)}` is homogeneous of degree one and quasi-concave, but not
  concave.
* `ex_4_8b`: if `f` is also strictly quasi-concave, then
  `f(θx + (1 − θ)x′) > θf(x) + (1 − θ)f(x′)` for `x, x′` that are not proportional.
-/

open Set

namespace StokeyLucasPrescott.DeterministicDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E}

/-- `f` is quasi-concave (p. 91): `x ≠ x′`, `f(x) ≥ f(x′)` and `θ ∈ (0, 1)` imply
`f(θx + (1 − θ)x′) ≥ f(x′)`. -/
def IsQuasiConcaveS (hC : Convex ℝ X) (f : X → ℝ) : Prop :=
  ∀ x x', x ≠ x' → f x' ≤ f x → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    f x' ≤ f (cmb hC h0.le h1.le x x')

/-- `f` is strictly quasi-concave: the last inequality is strict. -/
def IsStrictQuasiConcaveS (hC : Convex ℝ X) (f : X → ℝ) : Prop :=
  ∀ x x', x ≠ x' → f x' ≤ f x → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    f x' < f (cmb hC h0.le h1.le x x')

variable {hX : IsCone X} {hC : Convex ℝ X}

/-- The scaling behind Exercise 4.8: for `f(x) = a > 0` and `f(x′) = b > 0`,
`θx + (1 − θ)x′ = s(λx/a + (1 − λ)x′/b)` with `s = θa + (1 − θ)b`, `λ = θa/s`. -/
theorem cmb_eq_csmul_cmb (θ a b : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (x x' : X) :
    let s := θ * a + (1 - θ) * b
    let lam := θ * a / s
    ∃ (hs : 0 ≤ s) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1),
      cmb hC h0 h1 x x' = csmul hX hs (cmb hC hl0 hl1 (csmul hX (inv_nonneg.2 ha.le) x)
        (csmul hX (inv_nonneg.2 hb.le) x')) := by
  intro s lam
  have hs : 0 < s := by
    rcases h0.eq_or_lt with rfl | h0'
    · simp only [s]; nlinarith
    · simp only [s]; nlinarith
  have hl0 : 0 ≤ lam := div_nonneg (mul_nonneg h0 ha.le) hs.le
  have hl1 : lam ≤ 1 := by
    rw [div_le_one hs]; simp only [s]; nlinarith
  refine ⟨hs.le, hl0, hl1, Subtype.ext ?_⟩
  simp only [cmb, csmul, smul_add, smul_smul]
  congr 1
  · congr 1; simp only [lam]; field_simp
  · congr 1; simp only [lam]; field_simp; ring

/-- **Exercise 4.8a.** On a convex cone, a function that is homogeneous of degree one,
quasi-concave, and positive at every `x ≠ 0` is concave. -/
theorem ex_4_8a {f : X → ℝ} (hhom : ∀ x (a : ℝ) (ha : 0 ≤ a), f (csmul hX ha x) = a * f x)
    (hq : IsQuasiConcaveS hC f) (hpos : ∀ x : X, x.1 ≠ 0 → 0 < f x) : IsConcaveS hC f := by
  -- `f(0) = 0`
  have hzero : ∀ x : X, x.1 = 0 → f x = 0 := fun x hx => by
    have : x = csmul hX le_rfl x := Subtype.ext (by simp [csmul, hx])
    rw [this, hhom]; ring
  intro x x' θ h0 h1
  by_cases hx : x.1 = 0
  · have e : cmb hC h0 h1 x x' = csmul hX (by linarith : (0 : ℝ) ≤ 1 - θ) x' :=
      Subtype.ext (by simp [cmb, csmul, hx])
    rw [e, hhom, hzero x hx]; ring_nf; rfl
  by_cases hx' : x'.1 = 0
  · have e : cmb hC h0 h1 x x' = csmul hX h0 x := Subtype.ext (by simp [cmb, csmul, hx'])
    rw [e, hhom, hzero x' hx']; ring_nf; rfl
  set a := f x
  set b := f x'
  have ha := hpos x hx
  have hb := hpos x' hx'
  obtain ⟨hs, hl0, hl1, e⟩ := cmb_eq_csmul_cmb (hX := hX) (hC := hC) θ a b h0 h1 ha hb x x'
  rw [e, hhom]
  set u := csmul hX (inv_nonneg.2 ha.le) x
  set u' := csmul hX (inv_nonneg.2 hb.le) x'
  have hu : f u = 1 := by simp only [u, hhom]; field_simp
  have hu' : f u' = 1 := by simp only [u', hhom]; field_simp
  -- `f(λu + (1 − λ)u′) ≥ 1`
  have hge : 1 ≤ f (cmb hC hl0 hl1 u u') := by
    by_cases huu : u = u'
    · rw [huu, cmb_self, hu']
    rcases hl0.eq_or_lt with h | hl0'
    · have : cmb hC hl0 hl1 u u' = u' := Subtype.ext (by simp [cmb, ← h])
      rw [this, hu']
    rcases hl1.eq_or_lt with h | hl1'
    · have : cmb hC hl0 hl1 u u' = u := Subtype.ext (by simp [cmb, h])
      rw [this, hu]
    have := hq u u' huu (by rw [hu, hu']) _ hl0' hl1'
    rwa [hu'] at this
  nlinarith

/-- **Exercise 4.8a: positivity is needed.** On `ℝ²₊`, `f(x, y) = max{x − y, 2(x − y)}` is
homogeneous of degree one and quasi-concave (a nondecreasing function of `x − y`), but not
concave: `f(1, 0) = 2`, `f(0, 1) = −1`, `f(½, ½) = 0 < ½`. -/
theorem ex_4_8a_counterexample :
    let X : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2}
    let f : ℝ × ℝ → ℝ := fun p => max (p.1 - p.2) (2 * (p.1 - p.2))
    (∀ p ∈ X, ∀ a : ℝ, 0 ≤ a → a • p ∈ X) ∧ Convex ℝ X ∧
      (∀ p ∈ X, ∀ a : ℝ, 0 ≤ a → f (a • p) = a * f p) ∧
      (∀ p ∈ X, ∀ q ∈ X, f q ≤ f p → ∀ θ : ℝ, 0 < θ → θ < 1 → f q ≤ f (θ • p + (1 - θ) • q)) ∧
      ¬ ConcaveOn ℝ X f := by
  intro X f
  have hmono : ∀ s t : ℝ, s ≤ t → max s (2 * s) ≤ max t (2 * t) := fun s t h =>
    max_le_max h (by linarith)
  refine ⟨fun p hp a ha => ⟨mul_nonneg ha hp.1, mul_nonneg ha hp.2⟩, ?_, fun p _ a ha => ?_,
    fun p _ q _ hpq θ h0 h1 => ?_, fun hconc => ?_⟩
  · intro p hp q hq a b ha hb _
    exact ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1),
      add_nonneg (mul_nonneg ha hp.2) (mul_nonneg hb hq.2)⟩
  · simp only [f, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [← mul_sub, mul_left_comm, mul_max_of_nonneg _ _ ha]
  · -- `x − y` of the combination lies between those of `p` and `q`
    simp only [f, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hpq ⊢
    rcases le_total (q.1 - q.2) (p.1 - p.2) with h | h
    · exact hmono _ _ (by nlinarith)
    · -- then `f(p) ≤ f(q)`, so all three values agree
      have := hmono _ _ h
      have hle : (p.1 - p.2) ≤ θ * p.1 + (1 - θ) * q.1 - (θ * p.2 + (1 - θ) * q.2) := by nlinarith
      have hfeq : max (q.1 - q.2) (2 * (q.1 - q.2)) = max (p.1 - p.2) (2 * (p.1 - p.2)) :=
        le_antisymm hpq this
      rw [hfeq]
      exact hmono _ _ hle
  · have := hconc.2 (show ((1 : ℝ), (0 : ℝ)) ∈ X from ⟨zero_le_one, le_rfl⟩)
      (show ((0 : ℝ), (1 : ℝ)) ∈ X from ⟨le_rfl, zero_le_one⟩) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [f, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at this
    norm_num at this

/-- **Exercise 4.8b.** If in addition `f` is strictly quasi-concave, then
`f(θx + (1 − θ)x′) > θf(x) + (1 − θ)f(x′)` for `θ ∈ (0, 1)` and `x, x′` neither of which is a
multiple of the other. (The book asks only `x ≠ αx′`; with `x′ = 0` that allows
`f(θx) = θf(x)`, so `x′ ≠ αx` is needed as well.) -/
theorem ex_4_8b {f : X → ℝ} (hhom : ∀ x (a : ℝ) (ha : 0 ≤ a), f (csmul hX ha x) = a * f x)
    (hq : IsStrictQuasiConcaveS hC f) (hpos : ∀ x : X, x.1 ≠ 0 → 0 < f x) {x x' : X}
    (hxx' : ∀ a : ℝ, x.1 ≠ a • x'.1) (hx'x : ∀ a : ℝ, x'.1 ≠ a • x.1) {θ : ℝ} (h0 : 0 < θ)
    (h1 : θ < 1) : θ * f x + (1 - θ) * f x' < f (cmb hC h0.le h1.le x x') := by
  have hx : x.1 ≠ 0 := fun h => hxx' 0 (by simp [h])
  have hx' : x'.1 ≠ 0 := fun h => hx'x 0 (by simp [h])
  set a := f x
  set b := f x'
  have ha := hpos x hx
  have hb := hpos x' hx'
  obtain ⟨hs, hl0, hl1, e⟩ := cmb_eq_csmul_cmb (hX := hX) (hC := hC) θ a b h0.le h1.le ha hb x x'
  rw [e, hhom]
  set u := csmul hX (inv_nonneg.2 ha.le) x
  set u' := csmul hX (inv_nonneg.2 hb.le) x'
  have hu : f u = 1 := by simp only [u, hhom]; field_simp
  have hu' : f u' = 1 := by simp only [u', hhom]; field_simp
  have huu : u ≠ u' := fun h => hxx' (a / b) (by
    have := congrArg Subtype.val h
    simp only [u, u', csmul] at this
    calc x.1 = a • (a⁻¹ • x.1) := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
      _ = a • (b⁻¹ • x'.1) := by rw [this]
      _ = (a / b) • x'.1 := by rw [smul_smul, div_eq_mul_inv])
  have hs' : 0 < θ * a + (1 - θ) * b := by nlinarith
  have hl0' : 0 < θ * a / (θ * a + (1 - θ) * b) := div_pos (by positivity) hs'
  have hl1' : θ * a / (θ * a + (1 - θ) * b) < 1 := by
    rw [div_lt_one hs']; nlinarith
  have hgt := hq u u' huu (by rw [hu, hu']) _ hl0' hl1'
  rw [hu'] at hgt
  nlinarith

end StokeyLucasPrescott.DeterministicDP

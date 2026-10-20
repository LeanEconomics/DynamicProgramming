/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.SequenceSupport

/-!
# Truncation: a generalization (§16.5)

SLP §16.5, pp. 491–493. The commodity space is `S = BddSeq E` (bounded sequences in a real normed
space `E`; the book takes `E = ℝ`, `S = ℓ∞`, and indexes time from `t = 1`, here from `t = 0`).
For `φ ∈ S*`, `ψ = seqRegularPart φ` is the regular part of Lemma 15.5,
(1) `ψ(x) = lim_T φ(xᵀ)` (p. 491). Instead of truncating to zero, truncate to a point `a`:
`seqTruncTo T a x = (x₀, …, x_T, a_{T+1}, a_{T+2}, …)`.

* **Exercise 16.5(a)** (`ex_16_5a`, (2), p. 492):
  `lim_T φ(x₀, …, x_T, a_{T+1}, …) − ψ(x) = φ(a) − ψ(a)`, for all `x, a ∈ S`.
* **Assumption 16.1** (`Assumption16_1`, p. 492): an allocation `[(aᵢ), (bⱼ)]` with
  (a) `x ∈ Xᵢ ⇒ x^{T,aᵢ} ∈ Xᵢ` for all large `T`; (b) `y ∈ Yⱼ ⇒ y^{T,bⱼ} ∈ Yⱼ` for all large `T`;
  (c) `Σᵢ aᵢ = Σⱼ bⱼ`; (d) `uᵢ(x) > uᵢ(x̂) ⇒ uᵢ(x^{T,aᵢ}) > uᵢ(x̂)` for all large `T`.
  With `a = 0`, `b = 0` it is exactly Assumptions 15.6 + 15.7 (`assumption16_1_zero_iff`), and it
  is strictly weaker (`assumption16_1_not_assumption15_6`).
* Standing hypotheses (p. 492): 15.1, 15.2, 16.1, a feasible `[(xᵢ⁰), (yⱼ⁰)]`, `φ ∈ S*` with
  (3) `x ∈ Xᵢ, uᵢ(x) ≥ uᵢ(xᵢ⁰) ⇒ φ(x) ≥ φ(xᵢ⁰)` and (4) `y ∈ Yⱼ ⇒ φ(y) ≤ φ(yⱼ⁰)`, and a point
  `x̂ᵢ ∈ Xᵢ` with `uᵢ(x̂ᵢ) > uᵢ(xᵢ⁰)` for every `i`. Write `χ = φ − ψ`.
* **Exercise 16.5(b)** (`ex_16_5b`): `uᵢ(x) ≥ uᵢ(xᵢ⁰) ⇒ ψ(x) + χ(aᵢ) ≥ φ(xᵢ⁰)`, and
  `y ∈ Yⱼ ⇒ ψ(y) + χ(bⱼ) ≤ φ(yⱼ⁰)` (one-agent steps `truncation_step_consumer`,
  `truncation_step_firm`).
* **Exercise 16.5(c)** (`ex_16_5c`): `χ(Σᵢ xᵢ⁰) = χ(Σᵢ aᵢ)` and `χ(Σⱼ yⱼ⁰) = χ(Σⱼ bⱼ)`.
* **Exercise 16.5(d)** (`ex_16_5d`): `φ(xᵢ⁰) = ψ(xᵢ⁰) + χ(aᵢ)` and `φ(yⱼ⁰) = ψ(yⱼ⁰) + χ(bⱼ)`.
* **Exercise 16.5(e)** (`ex_16_5e`): (3) and (4) hold with `ψ` in place of `φ`.
* `theorem_16_5_competitiveEq`: with 15.3 and a `ψ`-cheaper point for every consumer,
  `[(xᵢ⁰), (yⱼ⁰), ψ]` is a competitive equilibrium. `theorem_15_6_of_ex_16_5e`: the special
  case `a = b = 0` recovers the support part of Theorem 15.6.

**Corrections and remarks.**
* Assumption 16.1(d) and the nonsatiation hypothesis below it write `u` for `uᵢ` (typo).
* (b)–(e) use only 15.1, 15.2, 16.1 and the continuity and linearity of `φ`; 15.3–15.5 serve
  only to produce `φ` through Theorem 15.4, and are not hypotheses here.
* In (b), the case `uᵢ(x) = uᵢ(xᵢ⁰)` needs the nonsatiation point and 15.2; the case
  `uᵢ(x) > uᵢ(xᵢ⁰)` needs no mixing. This case split avoids the tacit step of the book's proof of
  Theorem 15.6 (p. 466), which applies 15.2 to `(x̂ᵢ, x)` also when `uᵢ(x) = uᵢ(x̂ᵢ)`.
  (Verified: the NOTE in the transcription is correct.)
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Truncation to `a`** (p. 492): `x^{T,a} = (x₀, …, x_T, a_{T+1}, a_{T+2}, …)`, written as
`xᵀ + (a − aᵀ)`. -/
noncomputable def seqTruncTo (T : ℕ) (a x : BddSeq E) : BddSeq E :=
  seqTrunc T x + (a - seqTrunc T a)

/-- Coordinates of the truncation to `a`. -/
theorem seqTruncTo_apply (T : ℕ) (a x : BddSeq E) (t : ℕ) :
    seqTruncTo T a x t = if t ≤ T then x t else a t := by
  simp only [seqTruncTo, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply, seqTrunc_apply]
  split_ifs <;> simp

/-- Truncating to `0` is the ordinary truncation of §15.4. -/
theorem seqTruncTo_zero (T : ℕ) (x : BddSeq E) : seqTruncTo T 0 x = seqTrunc T x := by
  simp [seqTruncTo]

/-- `φ(x^{T,a}) = φ(xᵀ) + φ(a) − φ(aᵀ)`. -/
theorem apply_seqTruncTo (φ : StrongDual ℝ (BddSeq E)) (T : ℕ) (a x : BddSeq E) :
    φ (seqTruncTo T a x) = φ (seqTrunc T x) + (φ a - φ (seqTrunc T a)) := by
  rw [seqTruncTo, map_add, map_sub]

/-- `φ(x^{T,a}) → ψ(x) + φ(a) − ψ(a)` (the limit form of (2)). -/
theorem tendsto_apply_seqTruncTo (φ : StrongDual ℝ (BddSeq E)) (a x : BddSeq E) :
    Tendsto (fun T => φ (seqTruncTo T a x)) atTop
      (𝓝 (seqRegularPart φ x + (φ a - seqRegularPart φ a))) := by
  simp only [apply_seqTruncTo]
  exact (tendsto_apply_seqTrunc φ x).add (tendsto_const_nhds.sub (tendsto_apply_seqTrunc φ a))

/-- **Exercise 16.5(a)**, (2) (p. 492): for all `x, a ∈ S`,
`lim_T φ(x₀, …, x_T, a_{T+1}, a_{T+2}, …) − ψ(x) = φ(a) − ψ(a)`. -/
theorem ex_16_5a (φ : StrongDual ℝ (BddSeq E)) (a x : BddSeq E) :
    Tendsto (fun T => φ (seqTruncTo T a x) - seqRegularPart φ x) atTop
      (𝓝 (φ a - seqRegularPart φ a)) := by
  have := (tendsto_apply_seqTruncTo φ a x).sub_const (seqRegularPart φ x)
  simpa using this

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable (X : ι → Set (BddSeq E)) (u : ι → BddSeq E → ℝ) (Y : κ → Set (BddSeq E))
    (a : ι → BddSeq E) (b : κ → BddSeq E) in
/-- **Assumption 16.1** (p. 492): an allocation `[(aᵢ), (bⱼ)]` (not necessarily feasible) such that
(a) truncations of consumption plans to `aᵢ` far enough out are consumption plans; (b) the same for
production plans and `bⱼ`; (c) `Σᵢ aᵢ = Σⱼ bⱼ`; (d) a strict preference survives truncation to
`aᵢ` far enough out. -/
structure Assumption16_1 : Prop where
  cons_mem : ∀ i, ∀ x ∈ X i, ∀ᶠ T in atTop, seqTruncTo T (a i) x ∈ X i
  firm_mem : ∀ j, ∀ y ∈ Y j, ∀ᶠ T in atTop, seqTruncTo T (b j) y ∈ Y j
  sum_eq : ∑ i, a i = ∑ j, b j
  tail : ∀ i, ∀ x ∈ X i, ∀ x' ∈ X i, u i x' < u i x →
    ∀ᶠ T in atTop, u i x' < u i (seqTruncTo T (a i) x)

/-- With `aᵢ = 0` and `bⱼ = 0`, Assumption 16.1 is exactly Assumptions 15.6 and 15.7 (p. 492). -/
theorem assumption16_1_zero_iff (X : ι → Set (BddSeq E)) (u : ι → BddSeq E → ℝ)
    (Y : κ → Set (BddSeq E)) :
    Assumption16_1 X u Y 0 0 ↔ Assumption15_6 X Y ∧ Assumption15_7 X u := by
  have hz : ∀ (i : ι) (T : ℕ) (x : BddSeq E), seqTruncTo T ((0 : ι → BddSeq E) i) x =
      seqTrunc T x := fun _ T x => seqTruncTo_zero T x
  have hz' : ∀ (j : κ) (T : ℕ) (x : BddSeq E), seqTruncTo T ((0 : κ → BddSeq E) j) x =
      seqTrunc T x := fun _ T x => seqTruncTo_zero T x
  constructor
  · intro h
    refine ⟨⟨fun i x hx => ?_, fun j y hy => ?_⟩, fun i x hx x' hx' hlt => ?_⟩
    · simpa only [hz] using h.cons_mem i x hx
    · simpa only [hz'] using h.firm_mem j y hy
    · exact (h.tail i x hx x' hx' hlt).mono fun T hT _ => by simpa only [hz] using hT
  · rintro ⟨h6, h7⟩
    refine ⟨fun i x hx => ?_, fun j y hy => ?_, by simp, fun i x hx x' hx' hlt => ?_⟩
    · simpa only [hz] using h6.1 i x hx
    · simpa only [hz'] using h6.2 j y hy
    · exact ((h7 i).eventually (h6.1 i) hx hx' hlt).mono fun T hT => by
        simpa only [hz] using hT.2

/-- **Exercise 16.5(b), one consumer** (p. 492): under 15.1, 15.2 and 16.1(a), (d) for `(A, v, a)`,
(3) at `x⁰` and a point `x̂` with `v(x̂) > v(x⁰)`: `v(x) ≥ v(x⁰) ⇒ ψ(x) + [φ(a) − ψ(a)] ≥ φ(x⁰)`. -/
theorem truncation_step_consumer {A : Set (BddSeq E)} {v : BddSeq E → ℝ}
    {φ : StrongDual ℝ (BddSeq E)} {x₀ a : BddSeq E} (hA : Convex ℝ A) (hqc : SeqSemistrictQC A v)
    (hmem : ∀ x ∈ A, ∀ᶠ T in atTop, seqTruncTo T a x ∈ A)
    (htail : ∀ x ∈ A, ∀ x' ∈ A, v x' < v x → ∀ᶠ T in atTop, v x' < v (seqTruncTo T a x))
    (hx₀ : x₀ ∈ A) (hsup : ∀ z ∈ A, v x₀ ≤ v z → φ x₀ ≤ φ z) {xh : BddSeq E} (hxh : xh ∈ A)
    (hns : v x₀ < v xh) :
    ∀ z ∈ A, v x₀ ≤ v z → φ x₀ ≤ seqRegularPart φ z + (φ a - seqRegularPart φ a) := by
  have key : ∀ w ∈ A, v x₀ < v w → φ x₀ ≤ seqRegularPart φ w + (φ a - seqRegularPart φ a) :=
    fun w hw hlt => ge_of_tendsto (tendsto_apply_seqTruncTo φ a w)
      (((hmem w hw).and (htail w hw x₀ hx₀ hlt)).mono fun _ hT => hsup _ hT.1 hT.2.le)
  intro z hz hle
  rcases hle.lt_or_eq with hlt | heq
  · exact key z hz hlt
  · have hzxh : v z < v xh := heq ▸ hns
    set c := φ a - seqRegularPart φ a
    have hlim : Tendsto (fun θ : ℝ => θ * seqRegularPart φ xh + (1 - θ) * seqRegularPart φ z + c)
        (𝓝[>] 0) (𝓝 (seqRegularPart φ z + c)) := by
      have hc : Continuous fun θ : ℝ =>
          θ * seqRegularPart φ xh + (1 - θ) * seqRegularPart φ z + c := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with θ hθ
    have hmemθ : θ • xh + (1 - θ) • z ∈ A := hA hxh hz hθ.1.le (by linarith [hθ.2]) (by ring)
    have hv : v x₀ < v (θ • xh + (1 - θ) • z) := heq ▸ hqc xh hxh z hz hzxh θ hθ.1 hθ.2
    have := key _ hmemθ hv
    rwa [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this

/-- **Exercise 16.5(b), one firm** (p. 492): under 16.1(b) for `(B, b)` and (4) at `y⁰`:
`y ∈ B ⇒ ψ(y) + [φ(b) − ψ(b)] ≤ φ(y⁰)`. -/
theorem truncation_step_firm {B : Set (BddSeq E)} {φ : StrongDual ℝ (BddSeq E)}
    {y₀ b : BddSeq E} (hmem : ∀ y ∈ B, ∀ᶠ T in atTop, seqTruncTo T b y ∈ B)
    (hsup : ∀ w ∈ B, φ w ≤ φ y₀) :
    ∀ w ∈ B, seqRegularPart φ w + (φ b - seqRegularPart φ b) ≤ φ y₀ := fun w hw =>
  le_of_tendsto (tendsto_apply_seqTruncTo φ b w) ((hmem w hw).mono fun _ hT => hsup _ hT)

/-- **Exercise 16.5(b)** (pp. 492–493). Under 15.1, 15.2 and 16.1, with (3), (4) for `φ` and a
nonsatiation point for every consumer: `uᵢ(x) ≥ uᵢ(xᵢ⁰) ⇒ ψ(x) + [φ(aᵢ) − ψ(aᵢ)] ≥ φ(xᵢ⁰)`, and
`y ∈ Yⱼ ⇒ ψ(y) + [φ(bⱼ) − ψ(bⱼ)] ≤ φ(yⱼ⁰)`. (Feasibility is not needed for (b).) -/
theorem ex_16_5b {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ} {Y : κ → Set (BddSeq E)}
    {a : ι → BddSeq E} {b : κ → BddSeq E} {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (h16 : Assumption16_1 X u Y a b)
    (hx₀ : ∀ i, x₀ i ∈ X i) (φ : StrongDual ℝ (BddSeq E))
    (h3 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h4 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh) :
    (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z →
      φ (x₀ i) ≤ seqRegularPart φ z + (φ (a i) - seqRegularPart φ (a i))) ∧
    ∀ j, ∀ w ∈ Y j, seqRegularPart φ w + (φ (b j) - seqRegularPart φ (b j)) ≤ φ (y₀ j) := by
  refine ⟨fun i => ?_, fun j => truncation_step_firm (h16.firm_mem j) (h4 j)⟩
  obtain ⟨xh, hxh, hlt⟩ := hns i
  exact truncation_step_consumer (h1 i) (h2 i) (h16.cons_mem i) (h16.tail i) (hx₀ i) (h3 i) hxh
    hlt

/-- The weight-at-infinity inequalities `χ(xᵢ⁰) ≤ χ(aᵢ)` and `χ(bⱼ) ≤ χ(yⱼ⁰)`, `χ = φ − ψ`, from
Exercise 16.5(b) at `x = xᵢ⁰` and `y = yⱼ⁰`. -/
theorem truncation_chi_le {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ}
    {Y : κ → Set (BddSeq E)} {a : ι → BddSeq E} {b : κ → BddSeq E} {x₀ : ι → BddSeq E}
    {y₀ : κ → BddSeq E} (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u)
    (h16 : Assumption16_1 X u Y a b) (hfeas : Feasible X Y x₀ y₀) (φ : StrongDual ℝ (BddSeq E))
    (h3 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h4 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh) :
    (∀ i, (φ - seqRegularPart φ) (x₀ i) ≤ (φ - seqRegularPart φ) (a i)) ∧
    ∀ j, (φ - seqRegularPart φ) (b j) ≤ (φ - seqRegularPart φ) (y₀ j) := by
  obtain ⟨hb1, hb2⟩ := ex_16_5b h1 h2 h16 hfeas.1 φ h3 h4 hns
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have := hb1 i _ (hfeas.1 i) le_rfl
    simp only [sub_apply]
    linarith
  · have := hb2 j _ (hfeas.2.1 j)
    simp only [sub_apply]
    linarith

/-- The equality step behind (c) and (d): `Σᵢ χ(xᵢ⁰) = Σᵢ χ(aᵢ)` and `Σⱼ χ(yⱼ⁰) = Σⱼ χ(bⱼ)`. -/
theorem truncation_sum_chi_eq {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ}
    {Y : κ → Set (BddSeq E)} {a : ι → BddSeq E} {b : κ → BddSeq E} {x₀ : ι → BddSeq E}
    {y₀ : κ → BddSeq E} (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u)
    (h16 : Assumption16_1 X u Y a b) (hfeas : Feasible X Y x₀ y₀) (φ : StrongDual ℝ (BddSeq E))
    (h3 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h4 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh) :
    ∑ i, (φ - seqRegularPart φ) (x₀ i) = ∑ i, (φ - seqRegularPart φ) (a i) ∧
    ∑ j, (φ - seqRegularPart φ) (y₀ j) = ∑ j, (φ - seqRegularPart φ) (b j) := by
  set χ := φ - seqRegularPart φ
  obtain ⟨hx, hy⟩ := truncation_chi_le h1 h2 h16 hfeas φ h3 h4 hns
  have hsx : ∑ i, χ (x₀ i) ≤ ∑ i, χ (a i) := Finset.sum_le_sum fun i _ => hx i
  have hsy : ∑ j, χ (b j) ≤ ∑ j, χ (y₀ j) := Finset.sum_le_sum fun j _ => hy j
  have hab : ∑ i, χ (a i) = ∑ j, χ (b j) := by rw [← map_sum, ← map_sum, h16.sum_eq]
  have hxy : ∑ i, χ (x₀ i) = ∑ j, χ (y₀ j) := by
    rw [← map_sum, ← map_sum, sub_eq_zero.1 hfeas.2.2]
  constructor <;> linarith

/-- **Exercise 16.5(c)** (p. 493): `φ(Σᵢ xᵢ⁰) − ψ(Σᵢ xᵢ⁰) = φ(Σᵢ aᵢ) − ψ(Σᵢ aᵢ)` and
`φ(Σⱼ yⱼ⁰) − ψ(Σⱼ yⱼ⁰) = φ(Σⱼ bⱼ) − ψ(Σⱼ bⱼ)`. -/
theorem ex_16_5c {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ} {Y : κ → Set (BddSeq E)}
    {a : ι → BddSeq E} {b : κ → BddSeq E} {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (h16 : Assumption16_1 X u Y a b)
    (hfeas : Feasible X Y x₀ y₀) (φ : StrongDual ℝ (BddSeq E))
    (h3 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h4 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh) :
    φ (∑ i, x₀ i) - seqRegularPart φ (∑ i, x₀ i) = φ (∑ i, a i) - seqRegularPart φ (∑ i, a i) ∧
    φ (∑ j, y₀ j) - seqRegularPart φ (∑ j, y₀ j) =
      φ (∑ j, b j) - seqRegularPart φ (∑ j, b j) := by
  obtain ⟨hx, hy⟩ := truncation_sum_chi_eq h1 h2 h16 hfeas φ h3 h4 hns
  rw [← map_sum, ← map_sum] at hx hy
  simpa only [sub_apply] using And.intro hx hy

/-- **Exercise 16.5(d)** (p. 493): `φ(xᵢ⁰) = ψ(xᵢ⁰) + [φ(aᵢ) − ψ(aᵢ)]` for every `i` and
`φ(yⱼ⁰) = ψ(yⱼ⁰) + [φ(bⱼ) − ψ(bⱼ)]` for every `j`. -/
theorem ex_16_5d {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ} {Y : κ → Set (BddSeq E)}
    {a : ι → BddSeq E} {b : κ → BddSeq E} {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (h16 : Assumption16_1 X u Y a b)
    (hfeas : Feasible X Y x₀ y₀) (φ : StrongDual ℝ (BddSeq E))
    (h3 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h4 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh) :
    (∀ i, φ (x₀ i) = seqRegularPart φ (x₀ i) + (φ (a i) - seqRegularPart φ (a i))) ∧
    ∀ j, φ (y₀ j) = seqRegularPart φ (y₀ j) + (φ (b j) - seqRegularPart φ (b j)) := by
  set χ := φ - seqRegularPart φ with hχ
  obtain ⟨hx, hy⟩ := truncation_chi_le h1 h2 h16 hfeas φ h3 h4 hns
  obtain ⟨hsx, hsy⟩ := truncation_sum_chi_eq h1 h2 h16 hfeas φ h3 h4 hns
  have ex : ∀ i, χ (x₀ i) = χ (a i) := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ χ (a i) - χ (x₀ i) := fun i _ => sub_nonneg.2 (hx i)
    have h0 : ∑ i, (χ (a i) - χ (x₀ i)) = 0 := by rw [Finset.sum_sub_distrib, hsx, sub_self]
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (Finset.mem_univ i)
    linarith
  have ey : ∀ j, χ (y₀ j) = χ (b j) := by
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ χ (y₀ j) - χ (b j) := fun j _ => sub_nonneg.2 (hy j)
    have h0 : ∑ j, (χ (y₀ j) - χ (b j)) = 0 := by rw [Finset.sum_sub_distrib, hsy, sub_self]
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
    linarith
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have := ex i
    simp only [hχ, sub_apply] at this
    linarith
  · have := ey j
    simp only [hχ, sub_apply] at this
    linarith

/-- **Exercise 16.5(e)** (p. 493), the generalization of Theorem 15.6: under 15.1, 15.2 and 16.1,
if `φ` satisfies (3), (4) at a feasible allocation and every consumer is nonsatiated, then (3) and
(4) hold with `ψ = seqRegularPart φ` in place of `φ`. -/
theorem ex_16_5e {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ} {Y : κ → Set (BddSeq E)}
    {a : ι → BddSeq E} {b : κ → BddSeq E} {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (h16 : Assumption16_1 X u Y a b)
    (hfeas : Feasible X Y x₀ y₀) (φ : StrongDual ℝ (BddSeq E))
    (h3 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h4 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh) :
    (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → seqRegularPart φ (x₀ i) ≤ seqRegularPart φ z) ∧
    ∀ j, ∀ w ∈ Y j, seqRegularPart φ w ≤ seqRegularPart φ (y₀ j) := by
  obtain ⟨hb1, hb2⟩ := ex_16_5b h1 h2 h16 hfeas.1 φ h3 h4 hns
  obtain ⟨hd1, hd2⟩ := ex_16_5d h1 h2 h16 hfeas φ h3 h4 hns
  refine ⟨fun i z hz hle => ?_, fun j w hw => ?_⟩
  · have := hb1 i z hz hle
    rw [hd1 i] at this
    linarith
  · have := hb2 j w hw
    rw [hd2 j] at this
    linarith

/-- **§16.5 with the Remark after Theorem 15.4**: under the hypotheses of `ex_16_5e`,
Assumption 15.3, and a `ψ`-cheaper point for every consumer, `[(xᵢ⁰), (yⱼ⁰), ψ]` is a competitive
equilibrium whose price system has no weight at infinity. -/
theorem theorem_16_5_competitiveEq {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ}
    {Y : κ → Set (BddSeq E)} {a : ι → BddSeq E} {b : κ → BddSeq E} {x₀ : ι → BddSeq E}
    {y₀ : κ → BddSeq E} (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u)
    (h3c : Assumption15_3 X u) (h16 : Assumption16_1 X u Y a b) (hfeas : Feasible X Y x₀ y₀)
    (φ : StrongDual ℝ (BddSeq E))
    (h3 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h4 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh)
    (hcheap : ∀ i, ∃ w ∈ X i, seqRegularPart φ w < seqRegularPart φ (x₀ i)) :
    CompetitiveEq X u Y x₀ y₀ (seqRegularPart φ) ∧
      ∀ x, Tendsto (fun T => seqRegularPart φ (seqTrunc T x)) atTop
        (𝓝 (seqRegularPart φ x)) := by
  obtain ⟨r3, r4⟩ := ex_16_5e h1 h2 h16 hfeas φ h3 h4 hns
  refine ⟨⟨hfeas, fun i => ?_, r4⟩, fun x => ?_⟩
  · obtain ⟨w, hw, hlt⟩ := hcheap i
    exact seq_budget_max_of_cheaper (h1 i) (h3c i) (r3 i) hw hlt
  · simpa [seqRegularPart_seqRegularPart] using tendsto_apply_seqTrunc (seqRegularPart φ) x

/-- The case `a = b = 0` of Exercise 16.5(e) is the support part of Theorem 15.6. -/
theorem theorem_15_6_of_ex_16_5e {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ}
    {Y : κ → Set (BddSeq E)} {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E} (h1 : Assumption15_1 X)
    (h2 : Assumption15_2 X u) (h6 : Assumption15_6 X Y) (h7 : Assumption15_7 X u)
    (hfeas : Feasible X Y x₀ y₀) (φ : StrongDual ℝ (BddSeq E))
    (h3 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h4 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh) :
    (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → seqRegularPart φ (x₀ i) ≤ seqRegularPart φ z) ∧
    ∀ j, ∀ w ∈ Y j, seqRegularPart φ w ≤ seqRegularPart φ (y₀ j) :=
  ex_16_5e h1 h2 ((assumption16_1_zero_iff X u Y).2 ⟨h6, h7⟩) hfeas φ h3 h4 hns

/-! ### Assumption 16.1 is strictly weaker than 15.6–15.7 -/

/-- **Assumption 16.1 is strictly more general than Assumptions 15.6–15.7.** On `ℓ∞`, take one
consumer with `X = {x : x_t ≥ 1 ∀ t}` (so `0 ∉ X`) and `u = σ`, `σ(x) = Σ_t (1/2)ᵗ x_t`, and one
firm with `Y = {y : y_t ≤ 1 ∀ t}`. Assumption 16.1 holds with `a = b = 𝟙`, but Assumption 15.6
fails: no truncation `xᵀ` of `x ∈ X` is in `X`. -/
theorem assumption16_1_not_assumption15_6 :
    ∃ (X : Unit → Set (BddSeq ℝ)) (u : Unit → BddSeq ℝ → ℝ) (Y : Unit → Set (BddSeq ℝ))
      (a : Unit → BddSeq ℝ) (b : Unit → BddSeq ℝ),
      Assumption15_1 X ∧ Assumption15_2 X u ∧ Assumption16_1 X u Y a b ∧
      ¬ Assumption15_6 X Y := by
  set X1 : Set (BddSeq ℝ) := {x | ∀ t, 1 ≤ x t} with hX1
  set Y1 : Set (BddSeq ℝ) := {y | ∀ t, y t ≤ 1} with hY1
  have hone : ∀ t, oneSeq t = 1 := fun t => rfl
  refine ⟨fun _ => X1, fun _ => halfSum, fun _ => Y1, fun _ => oneSeq, fun _ => oneSeq,
    fun _ => ?_, fun _ z _ z' _ hlt θ h0 h1 => ?_, ⟨fun _ x hx => ?_, fun _ y hy => ?_, rfl,
    fun _ x _ x' _ hlt => ?_⟩, ?_⟩
  · intro x hx x' hx' p q hp hq hpq t
    rw [seq_coord_combo, smul_eq_mul, smul_eq_mul]
    nlinarith [hx t, hx' t]
  · change halfSum z' < halfSum (θ • z + (1 - θ) • z')
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    nlinarith
  · refine Eventually.of_forall fun T t => ?_
    rw [seqTruncTo_apply]
    split_ifs
    · exact hx t
    · exact (hone t).ge
  · refine Eventually.of_forall fun T t => ?_
    rw [seqTruncTo_apply]
    split_ifs
    · exact hy t
    · exact (hone t).le
  · have hlim : Tendsto (fun T => halfSum (seqTruncTo T oneSeq x)) atTop (𝓝 (halfSum x)) := by
      simp only [apply_seqTruncTo]
      have := (tendsto_halfSum_seqTrunc x).add
        ((tendsto_const_nhds (x := halfSum oneSeq)).sub (tendsto_halfSum_seqTrunc oneSeq))
      simpa using this
    exact hlim.eventually (lt_mem_nhds hlt)
  · rintro ⟨hX, -⟩
    obtain ⟨T, hT⟩ := ((hX () oneSeq fun t => (hone t).ge)).exists
    have := hT (T + 1)
    simp only [seqTrunc_apply, show ¬ (T + 1 ≤ T) by omega, ↓reduceIte] at this
    norm_num at this

end StokeyLucasPrescott.EquilibriumApplications

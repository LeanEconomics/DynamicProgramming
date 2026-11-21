/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weighting functions and weighted inner products (Definition 11.3.1)

Miao, §11.3.1, pp. 356–357. A weighting function `w` on a set `s` of reals is positive on `s`
and integrable over `s`; it defines the inner product `⟨f, g⟩_w = ∫_s f g w` and orthogonality.

* `ni_IsWeightingFunction w s`, `ni_inner w s f g`, `ni_Orthogonal w s φ` (Definition 11.3.1).
* `definition_11_3_1`: the constant weight `1` on `(a, b)` is a weighting function.
* bilinearity, symmetry and positivity of `⟨·,·⟩_w`; Cauchy–Schwarz (`ni_inner_sq_le`).
* The induced norm is `‖f‖_w = √⟨f, f⟩_w` (`ni_wnorm`): it is absolutely homogeneous and
  satisfies the triangle inequality, so `‖f − g‖_w` is a (pseudo)metric.

Departures from the book.
* The book's definition is for a bounded interval `[a, b]`; positivity is required on the set
  `s` itself, which is taken to be the open interval `(a, b)` for the Chebyshev weight
  `(1 − x²)^{−1/2}` (undefined at `±1`) and `[0, ∞)`, `ℝ` for Laguerre and Hermite, which the
  book also uses with this definition.
* The book writes the induced norm as `‖f‖_w = ⟨f, f⟩_w`; this is not a norm
  (`ni_inner_self_not_homogeneous`): the norm is its square root.
-/

open MeasureTheory

namespace Miao.NumericalMethods

/-- **Definition 11.3.1** (weighting function, Miao, p. 356). `w` is positive on `s` and has a
finite integral over `s`. -/
def ni_IsWeightingFunction (w : ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∀ x ∈ s, 0 < w x) ∧ IntegrableOn w s

/-- **Definition 11.3.1** (weighted inner product, Miao, p. 356): `⟨f, g⟩_w = ∫_s f g w`. -/
noncomputable def ni_inner (w : ℝ → ℝ) (s : Set ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ x in s, f x * g x * w x

/-- **Definition 11.3.1** (mutual orthogonality, Miao, p. 356): `⟨φᵢ, φⱼ⟩_w = 0` for `i ≠ j`. -/
def ni_Orthogonal {ι : Type*} (w : ℝ → ℝ) (s : Set ℝ) (φ : ι → ℝ → ℝ) : Prop :=
  ∀ i j, i ≠ j → ni_inner w s (φ i) (φ j) = 0

/-- The norm induced by the weighted inner product, `‖f‖_w = √⟨f, f⟩_w` (Miao, p. 356, with the
square root restored). -/
noncomputable def ni_wnorm (w : ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : ℝ :=
  Real.sqrt (ni_inner w s f f)

/-- **Definition 11.3.1** (Miao, p. 356): the weight `w = 1` on a bounded interval `(a, b)` is a
weighting function (the Legendre weight). -/
theorem definition_11_3_1 (a b : ℝ) :
    ni_IsWeightingFunction (fun _ => 1) (Set.Ioo a b) :=
  ⟨fun _ _ => one_pos, integrableOn_const (by simp) (by simp)⟩

/-- Miao, p. 356: the inner product is symmetric. -/
theorem ni_inner_comm (w : ℝ → ℝ) (s : Set ℝ) (f g : ℝ → ℝ) :
    ni_inner w s f g = ni_inner w s g f := by
  unfold ni_inner
  congr 1
  funext x
  ring

/-- Miao, p. 356: the inner product is additive in its first argument. -/
theorem ni_inner_add_left (w : ℝ → ℝ) (s : Set ℝ) (f₁ f₂ g : ℝ → ℝ)
    (h₁ : IntegrableOn (fun x => f₁ x * g x * w x) s)
    (h₂ : IntegrableOn (fun x => f₂ x * g x * w x) s) :
    ni_inner w s (fun x => f₁ x + f₂ x) g = ni_inner w s f₁ g + ni_inner w s f₂ g := by
  unfold ni_inner
  rw [← integral_add h₁ h₂]
  congr 1
  funext x
  ring

/-- Miao, p. 356: the inner product is homogeneous in its first argument. -/
theorem ni_inner_smul_left (w : ℝ → ℝ) (s : Set ℝ) (c : ℝ) (f g : ℝ → ℝ) :
    ni_inner w s (fun x => c * f x) g = c * ni_inner w s f g := by
  unfold ni_inner
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- Miao, p. 356: `⟨f, f⟩_w ≥ 0` for a weighting function. -/
theorem ni_inner_self_nonneg {w : ℝ → ℝ} {s : Set ℝ} (hw : ni_IsWeightingFunction w s)
    (hs : MeasurableSet s) (f : ℝ → ℝ) : 0 ≤ ni_inner w s f f := by
  unfold ni_inner
  refine setIntegral_nonneg hs fun x hx => ?_
  exact mul_nonneg (mul_self_nonneg _) (hw.1 x hx).le

/-- Cauchy–Schwarz for the weighted inner product (Miao, p. 356, needed for the norm):
`⟨f, g⟩_w² ≤ ⟨f, f⟩_w ⟨g, g⟩_w`. -/
theorem ni_inner_sq_le {w : ℝ → ℝ} {s : Set ℝ} (hw : ni_IsWeightingFunction w s)
    (hs : MeasurableSet s) (f g : ℝ → ℝ)
    (hff : IntegrableOn (fun x => f x * f x * w x) s)
    (hfg : IntegrableOn (fun x => f x * g x * w x) s)
    (hgg : IntegrableOn (fun x => g x * g x * w x) s) :
    ni_inner w s f g ^ 2 ≤ ni_inner w s f f * ni_inner w s g g := by
  have key : ∀ t : ℝ, 0 ≤ ni_inner w s g g * (t * t) + 2 * ni_inner w s f g * t
      + ni_inner w s f f := by
    intro t
    have h0 := ni_inner_self_nonneg hw hs (fun x => f x + t * g x)
    have heq : ni_inner w s (fun x => f x + t * g x) (fun x => f x + t * g x)
        = ni_inner w s g g * (t * t) + 2 * ni_inner w s f g * t + ni_inner w s f f := by
      unfold ni_inner
      have e : (fun x => (f x + t * g x) * (f x + t * g x) * w x) = fun x =>
          (t * t) * (g x * g x * w x) + (2 * t) * (f x * g x * w x) + f x * f x * w x := by
        funext x; ring
      rw [e, integral_add (f := fun x => t * t * (g x * g x * w x) + 2 * t * (f x * g x * w x))
        ((hgg.const_mul _).add (hfg.const_mul _)) hff,
        integral_add (f := fun x => t * t * (g x * g x * w x))
          (hgg.const_mul _) (hfg.const_mul _), integral_const_mul, integral_const_mul]
      ring
    rw [heq] at h0
    exact h0
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith

/-- Miao, p. 356 (correction): `⟨f, f⟩_w` itself is not a norm, since it is not absolutely
homogeneous: for `w = 1` on `(0, 1)`, `⟨2, 2⟩_w = 4 ≠ 2 = 2 ⟨1, 1⟩_w`. -/
theorem ni_inner_self_not_homogeneous :
    ni_inner (fun _ => 1) (Set.Ioo 0 1) (fun _ => 2 * 1) (fun _ => 2 * 1) ≠
      2 * ni_inner (fun _ => 1) (Set.Ioo 0 1) (fun _ => 1) (fun _ => 1) := by
  unfold ni_inner
  simp only [mul_one, integral_const, smul_eq_mul]
  rw [measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le zero_le_one]
  norm_num

/-- Miao, p. 356: the induced norm `‖f‖_w = √⟨f, f⟩_w` is absolutely homogeneous. -/
theorem ni_wnorm_smul (w : ℝ → ℝ) (s : Set ℝ) (c : ℝ) (f : ℝ → ℝ) :
    ni_wnorm w s (fun x => c * f x) = |c| * ni_wnorm w s f := by
  unfold ni_wnorm
  have e : ni_inner w s (fun x => c * f x) (fun x => c * f x)
      = c ^ 2 * ni_inner w s f f := by
    rw [ni_inner_smul_left, ni_inner_comm, ni_inner_smul_left, ni_inner_comm]
    ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- Miao, p. 356: the induced norm satisfies the triangle inequality, so it induces "a natural
metric" `‖f − g‖_w`. -/
theorem ni_wnorm_add_le {w : ℝ → ℝ} {s : Set ℝ} (hw : ni_IsWeightingFunction w s)
    (hs : MeasurableSet s) (f g : ℝ → ℝ)
    (hff : IntegrableOn (fun x => f x * f x * w x) s)
    (hfg : IntegrableOn (fun x => f x * g x * w x) s)
    (hgg : IntegrableOn (fun x => g x * g x * w x) s) :
    ni_wnorm w s (fun x => f x + g x) ≤ ni_wnorm w s f + ni_wnorm w s g := by
  unfold ni_wnorm
  have e : ni_inner w s (fun x => f x + g x) (fun x => f x + g x)
      = ni_inner w s f f + 2 * ni_inner w s f g + ni_inner w s g g := by
    unfold ni_inner
    have e' : (fun x => (f x + g x) * (f x + g x) * w x) = fun x =>
        f x * f x * w x + 2 * (f x * g x * w x) + g x * g x * w x := by
      funext x; ring
    rw [e', integral_add (f := fun x => f x * f x * w x + 2 * (f x * g x * w x))
      (hff.add (hfg.const_mul _)) hgg,
      integral_add (f := fun x => f x * f x * w x) hff (hfg.const_mul _), integral_const_mul]
  have hA := ni_inner_self_nonneg hw hs f
  have hC := ni_inner_self_nonneg hw hs g
  have hCS := ni_inner_sq_le hw hs f g hff hfg hgg
  rw [e]
  rw [Real.sqrt_le_left]
  · have hsA := Real.sq_sqrt hA
    have hsC := Real.sq_sqrt hC
    have hB : ni_inner w s f g ≤ Real.sqrt (ni_inner w s f f) * Real.sqrt (ni_inner w s g g) := by
      rw [← Real.sqrt_mul hA]
      exact Real.le_sqrt_of_sq_le hCS
    nlinarith [Real.sqrt_nonneg (ni_inner w s f f), Real.sqrt_nonneg (ni_inner w s g g)]
  · positivity

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalStopping.Monotonicity

/-!
# Dimensionality reduction through continuation values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.4.2–§4.1.4.3
(pp. 118–119).

When the state is `x = (w, z)` with `w` IID with distribution `φ` and `z`
`Q`-Markov, the transition matrix is `P((w, z), (w', z')) = φ(w')Q(z, z')`. If
the continuation reward depends only on `z`, the continuation value function
`h*(w, z)` does not depend on `w`, and it is the unique fixed point of the
reduced operator (4.15) acting on `ℝ^Z`. Example 4.1.6 embeds IID job search
(`Z` a point), where the reduced operator is the scalar map of Vol. 1 (1.33).

§4.1.4.3 treats a firm whose scrap value is IID. Exercise 4.1.13 is formalised
with scrap values on a finite set `W ⊂ ℝ₊`, the discretised form the section
itself recommends: if `φ_a ≼_F φ_b` then the optimal policies satisfy
`σ*_a ≥ σ*_b` pointwise.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

variable {W Z : Type*} [Fintype W] [Fintype Z]

/-- The product kernel `P((w, z), (w', z')) = φ(w')Q(z, z')` of p. 118. -/
def productKernel (φ : W → ℝ) (Q : Matrix Z Z ℝ) : Matrix (W × Z) (W × Z) ℝ :=
  Matrix.of fun x x' => φ x'.1 * Q x.2 x'.2

omit [Fintype W] [Fintype Z] in
theorem productKernel_apply (φ : W → ℝ) (Q : Matrix Z Z ℝ) (x x' : W × Z) :
    productKernel φ Q x x' = φ x'.1 * Q x.2 x'.2 := rfl

/-- The product kernel is Markov when `φ` is a distribution and `Q` is Markov (p. 118). -/
theorem isMarkov_productKernel {φ : W → ℝ} (hφ : IsDistribution φ) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) : IsMarkov (productKernel φ Q) where
  nonneg x x' := mul_nonneg (hφ.nonneg _) (hQ.nonneg _ _)
  rowsum x := by
    simp only [productKernel_apply]
    rw [Fintype.sum_prod_type, sum_comm]
    simp only [← sum_mul, hφ.sum_eq_one, one_mul]
    exact hQ.rowsum _

/-- `(Pv)(w, z) = ∑_{z'} (∑_{w'} v(w', z')φ(w')) Q(z, z')` does not depend on `w`. -/
theorem productKernel_mulVec (φ : W → ℝ) (Q : Matrix Z Z ℝ) (v : W × Z → ℝ) (w : W) (z : Z) :
    (productKernel φ Q *ᵥ v) (w, z) = ∑ z', (∑ w', v (w', z') * φ w') * Q z z' := by
  rw [mulVec_apply_eq, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun z' _ => ?_
  rw [sum_mul]
  exact sum_congr rfl fun w' _ => by rw [productKernel_apply]; ring

/-- A stopping problem on `W × Z` with product transitions and a continuation reward depending
only on `z` (p. 118). -/
noncomputable def productProblem {φ : W → ℝ} (hφ : IsDistribution φ) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) (c : Z → ℝ) (e : W × Z → ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    StoppingProblem (W × Z) where
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  P := productKernel φ Q
  P_markov := isMarkov_productKernel hφ hQ
  c := fun x => c x.2
  e := e

namespace productProblem

variable {φ : W → ℝ} (hφ : IsDistribution φ) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (c : Z → ℝ)
  (e : W × Z → ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)

/-- The Bellman operator (4.14):
`(Tv)(w, z) = max{e(w, z), c(z) + β ∑_{w'} ∑_{z'} v(w', z')φ(w')Q(z, z')}`. -/
theorem T_apply (v : W × Z → ℝ) (w : W) (z : Z) :
    (productProblem hφ hQ c e hβ0 hβ1).T v (w, z) =
      max (e (w, z)) (c z + β * ∑ z', (∑ w', v (w', z') * φ w') * Q z z') := by
  rw [StoppingProblem.T, StoppingProblem.cont, productProblem, productKernel_mulVec]

/-- The reduced continuation value operator (4.15) on `ℝ^Z`:
`(C̃h)(z) = c(z) + β ∑_{w'} ∑_{z'} max{e(w', z'), h(z')} φ(w')Q(z, z')`. -/
noncomputable def reducedC (h : Z → ℝ) : Z → ℝ := fun z =>
  c z + β * ∑ z', (∑ w', max (e (w', z')) (h z') * φ w') * Q z z'

include hφ hQ hβ0 in
/-- `C̃` is order preserving. -/
theorem reducedC_monotone : Monotone (reducedC (φ := φ) (Q := Q) c e (β := β)) := by
  intro h h' hhh' z
  unfold reducedC
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun z' _ => ?_) hβ0.le)
  refine mul_le_mul_of_nonneg_right (sum_le_sum fun w' _ => ?_) (hQ.nonneg z z')
  exact mul_le_mul_of_nonneg_right (max_le_max le_rfl (hhh' z')) (hφ.nonneg w')

include hφ hQ hβ0 hβ1 in
/-- `C̃` is a contraction of modulus `β` on `ℝ^Z`. -/
theorem isContractionOn_reducedC :
    IsContractionOn (reducedC (φ := φ) (Q := Q) c e (β := β)) Set.univ β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := hβ0.le
  lt_one := hβ1
  norm_sub_le h _ h' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ0.le (norm_nonneg _))]
    intro z
    rw [Pi.sub_apply, Real.norm_eq_abs]
    unfold reducedC
    rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ0.le]
    refine mul_le_mul_of_nonneg_left ?_ hβ0.le
    have hb : ∀ z', |h z' - h' z'| ≤ ‖h - h'‖ := fun z' => by
      have := norm_le_pi_norm (h - h') z'
      simpa [Real.norm_eq_abs] using this
    calc |∑ z', (∑ w', max (e (w', z')) (h z') * φ w') * Q z z' -
          ∑ z', (∑ w', max (e (w', z')) (h' z') * φ w') * Q z z'|
        = |∑ z', (∑ w', (max (e (w', z')) (h z') - max (e (w', z')) (h' z')) * φ w') * Q z z'| := by
          rw [← sum_sub_distrib]
          congr 1
          refine sum_congr rfl fun z' _ => ?_
          rw [← sub_mul, ← sum_sub_distrib]
          congr 1
          exact sum_congr rfl fun w' _ => by ring
      _ ≤ ∑ z', (∑ w', |max (e (w', z')) (h z') - max (e (w', z')) (h' z')| * φ w') * Q z z' := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun z' _ => ?_)
          rw [abs_mul, abs_of_nonneg (hQ.nonneg z z')]
          refine mul_le_mul_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans
            (sum_le_sum fun w' _ => ?_)) (hQ.nonneg z z')
          rw [abs_mul, abs_of_nonneg (hφ.nonneg w')]
      _ ≤ ∑ z', (∑ w', ‖h - h'‖ * φ w') * Q z z' := by
          refine sum_le_sum fun z' _ => mul_le_mul_of_nonneg_right (sum_le_sum fun w' _ =>
            mul_le_mul_of_nonneg_right ?_ (hφ.nonneg w')) (hQ.nonneg z z')
          rw [max_comm (e (w', z')) (h z'), max_comm (e (w', z')) (h' z')]
          exact (abs_max_sub_max_le_abs _ _ _).trans (hb z')
      _ = ‖h - h'‖ := by
          simp only [← mul_sum, hφ.sum_eq_one, mul_one]
          rw [hQ.rowsum, mul_one]

/-- The reduced continuation value: the unique fixed point of `C̃` in `ℝ^Z`. -/
noncomputable def reducedH : Z → ℝ :=
  Classical.choose ((isContractionOn_reducedC hφ hQ c e hβ0 hβ1).exists_fixedPt isClosed_univ
    ⟨0, Set.mem_univ 0⟩)

theorem isFixedPt_reducedH :
    IsFixedPt (reducedC (φ := φ) (Q := Q) c e (β := β)) (reducedH hφ hQ c e hβ0 hβ1) :=
  (Classical.choose_spec ((isContractionOn_reducedC hφ hQ c e hβ0 hβ1).exists_fixedPt isClosed_univ
    ⟨0, Set.mem_univ 0⟩)).2

theorem eq_reducedH_of_isFixedPt {h : Z → ℝ}
    (hh : IsFixedPt (reducedC (φ := φ) (Q := Q) c e (β := β)) h) : h = reducedH hφ hQ c e hβ0 hβ1 :=
  (isContractionOn_reducedC hφ hQ c e hβ0 hβ1).fixedPt_unique (Set.mem_univ h) (Set.mem_univ _) hh
    (isFixedPt_reducedH hφ hQ c e hβ0 hβ1)

theorem tendsto_iterate_reducedC (h : Z → ℝ) :
    Tendsto (fun k : ℕ => (reducedC (φ := φ) (Q := Q) c e (β := β))^[k] h) atTop
      (𝓝 (reducedH hφ hQ c e hβ0 hβ1)) :=
  (isContractionOn_reducedC hφ hQ c e hβ0 hβ1).tendsto_iterate_fixedPt (Set.mem_univ h)
    (Set.mem_univ _) (isFixedPt_reducedH hφ hQ c e hβ0 hβ1)

variable [DecidableEq W] [DecidableEq Z]

/-- The continuation value does not depend on the IID component (p. 118). -/
theorem hstar_indep (w w' : W) (z : Z) :
    (productProblem hφ hQ c e hβ0 hβ1).hstar (w, z) =
      (productProblem hφ hQ c e hβ0 hβ1).hstar (w', z) := by
  simp only [StoppingProblem.hstar, StoppingProblem.cont, productProblem, productKernel_mulVec]

/-- The continuation value function of the full problem is the reduced one (p. 118):
`h*(w, z) = h̃(z)`. -/
theorem hstar_eq_reducedH (w : W) (z : Z) :
    (productProblem hφ hQ c e hβ0 hβ1).hstar (w, z) = reducedH hφ hQ c e hβ0 hβ1 z := by
  set S := productProblem hφ hQ c e hβ0 hβ1 with hS
  -- `z ↦ h*(w, z)` is a fixed point of `C̃`
  have hfix : IsFixedPt (reducedC (φ := φ) (Q := Q) c e (β := β)) fun z => S.hstar (w, z) := by
    funext z
    have h1 := congrFun S.isFixedPt_C_hstar.eq (w, z)
    rw [StoppingProblem.C, StoppingProblem.cont] at h1
    rw [← h1]
    have hind : ∀ w' z', S.hstar (w', z') = S.hstar (w, z') := fun w' z' =>
      hstar_indep hφ hQ c e hβ0 hβ1 w' w z'
    have hP : S.P = productKernel φ Q := rfl
    have hc : ∀ x, S.c x = c x.2 := fun _ => rfl
    have he : ∀ x, S.e x = e x := fun _ => rfl
    have hβ : S.β = β := rfl
    rw [hP, productKernel_mulVec]
    simp only [reducedC, hc, he, hβ, hind]
  have := eq_reducedH_of_isFixedPt hφ hQ c e hβ0 hβ1 hfix
  exact congrFun this z

/-- The optimal policy in reduced form: stop at `(w, z)` iff `e(w, z) ≥ h̃(z)`. -/
theorem sigmaStar_eq_true_iff (w : W) (z : Z) :
    (productProblem hφ hQ c e hβ0 hβ1).sigmaStar (w, z) = true ↔
      reducedH hφ hQ c e hβ0 hβ1 z ≤ e (w, z) := by
  rw [StoppingProblem.sigmaStar_eq_true_iff, hstar_eq_reducedH]
  exact Iff.rfl

end productProblem

/-- Example 4.1.6 (p. 118): with `Z` a single point, the reduced operator on `ℝ^Z ≅ ℝ` is the
scalar map `h ↦ c + β ∑_{w'} max{e(w'), h} φ(w')` of Vol. 1 (1.33), which is why IID job search
reduces to a one-dimensional problem. -/
theorem reducedC_unit {φ : W → ℝ} (c : ℝ) (e : W → ℝ) (β : ℝ) (h : Unit → ℝ) :
    productProblem.reducedC (φ := φ) (Q := (1 : Matrix Unit Unit ℝ)) (fun _ => c)
      (fun x => e x.1) (β := β) h () = c + β * ∑ w', max (e w') (h ()) * φ w' := by
  simp [productProblem.reducedC]

/-! ### Application to firm value with IID scrap values (§4.1.4.3) -/

/-- The firm of §4.1.2 whose scrap value `s(w)` is drawn IID from `φ` each period: exit reward
`s(w)`, continuation reward `π(z)` (p. 119). -/
noncomputable def scrapFirm {φ : W → ℝ} (hφ : IsDistribution φ) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) (π : Z → ℝ) (s : W → ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    StoppingProblem (W × Z) :=
  productProblem hφ hQ π (fun x => s x.1) hβ0 hβ1

/-- Exercise 4.1.12 (p. 119): the continuation value operator of the scrap-value firm, as a
self-map of `ℝ^Z`: `(C̃h)(z) = π(z) + β ∑_{z'} ∑_{w'} max{s(w'), h(z')} φ(w') Q(z, z')`. -/
theorem scrapFirm_reducedC {φ : W → ℝ} {Q : Matrix Z Z ℝ} (π : Z → ℝ) (s : W → ℝ) (β : ℝ)
    (h : Z → ℝ) (z : Z) :
    productProblem.reducedC (φ := φ) (Q := Q) π (fun x : W × Z => s x.1) (β := β) h z =
      π z + β * ∑ z', (∑ w', max (s w') (h z') * φ w') * Q z z' := rfl

variable [DecidableEq W] [DecidableEq Z] [PartialOrder W]

omit [DecidableEq W] [DecidableEq Z] in
/-- A higher scrap distribution raises the reduced operator: if `φ_a ≼_F φ_b` and `s` is
increasing, then `C̃_a h ≤ C̃_b h` for every `h`. -/
theorem scrapFirm_reducedC_le {φa φb : W → ℝ} (hab : FOSD φa φb) {Q : Matrix Z Z ℝ}
    (hQ : IsMarkov Q) (π : Z → ℝ) {s : W → ℝ} (hs : Monotone s) {β : ℝ} (hβ0 : 0 < β)
    (h : Z → ℝ) :
    productProblem.reducedC (φ := φa) (Q := Q) π (fun x : W × Z => s x.1) (β := β) h ≤
      productProblem.reducedC (φ := φb) (Q := Q) π (fun x : W × Z => s x.1) (β := β) h := by
  intro z
  simp only [scrapFirm_reducedC]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun z' _ => ?_) hβ0.le)
  refine mul_le_mul_of_nonneg_right ?_ (hQ.nonneg z z')
  exact hab (fun w' => max (s w') (h z')) fun a b hab' => max_le_max (hs hab') le_rfl

/-- Exercise 4.1.13 (p. 119), finite-support version: if `φ_a ≼_F φ_b` then the reduced
continuation values satisfy `h̃_a ≤ h̃_b`, so the optimal policies satisfy `σ*_a ≥ σ*_b` pointwise:
a firm facing stochastically larger scrap values exits in fewer states. -/
theorem scrapFirm_sigmaStar_ge {φa φb : W → ℝ} (hφa : IsDistribution φa) (hφb : IsDistribution φb)
    (hab : FOSD φa φb) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (π : Z → ℝ) {s : W → ℝ}
    (hs : Monotone s) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (w : W) (z : Z) :
    (scrapFirm hφb hQ π s hβ0 hβ1).sigmaStar (w, z) = true →
      (scrapFirm hφa hQ π s hβ0 hβ1).sigmaStar (w, z) = true := by
  simp only [scrapFirm, productProblem.sigmaStar_eq_true_iff]
  intro hb
  refine le_trans ?_ hb
  exact fixedPt_le_of_le (scrapFirm_reducedC_le hab hQ π hs hβ0)
    (productProblem.reducedC_monotone hφb hQ π _ hβ0)
    (productProblem.isFixedPt_reducedH hφa hQ π _ hβ0 hβ1)
    (productProblem.tendsto_iterate_reducedC hφb hQ π _ hβ0 hβ1 _) z

end SargentStachurski.OptimalStopping

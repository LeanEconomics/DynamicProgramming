/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalStopping.Reduction

/-!
# Research and development

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.2.2 (pp. 122–126).

A firm develops a product worth `π(Xₜ)` when marketed, paying a flow cost
while it continues. With constant cost `c`, this is a stopping problem with
exit reward `π` and continuation reward `−c`, Bellman equation (4.17);
Exercise 4.2.1 gives the continuation value operator and shows `h*` is
increasing when `π` is and `P` is monotone increasing; Exercise 4.2.2 shows
the optimal policy is increasing when `π` is increasing and `(Xₜ)` is IID.

With IID costs `Cₜ ∼ φ` the state is `(c, x)` and the continuation value still
depends on `c`; the expected value function `g(x) = ∑ v*(c', x')φ(c')P(x, x')`,
(4.19), solves the functional equation (4.20) on `ℝ^X`. Exercise 4.2.3: the
operator `R` of (4.20) is a contraction of modulus `β`, so `g*` is unique and
computable by successive approximation, and
`σ*(c, x) = 1{π(x) ≥ −c + βg*(x)}` is optimal.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Constant R&D costs (§4.2.2.1) -/

/-- R&D with constant cost `c₀` (p. 125): exit reward `π`, continuation reward `−c₀`,
`β = 1/(1 + r)`. -/
noncomputable def rdConstant {P : Matrix X X ℝ} (hP : IsMarkov P) (π : X → ℝ) (c₀ : ℝ) {r : ℝ}
    (hr : 0 < r) : StoppingProblem X where
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  P := P
  P_markov := hP
  c := fun _ => -c₀
  e := π

namespace rdConstant

variable {P : Matrix X X ℝ} (hP : IsMarkov P) (π : X → ℝ) (c₀ : ℝ) {r : ℝ} (hr : 0 < r)

/-- The Bellman equation (4.17): `v*(x) = max{π(x), −c₀ + β ∑ v*(x')P(x, x')}`. -/
theorem bellman_equation (x : X) :
    (rdConstant hP π c₀ hr).vstar x =
      max (π x) (-c₀ + 1 / (1 + r) * ∑ x', (rdConstant hP π c₀ hr).vstar x' * P x x') := by
  rw [StoppingProblem.bellman_equation]
  rfl

omit [DecidableEq X] in
/-- Exercise 4.2.1 (p. 125): the continuation value operator is
`(Ch)(x) = −c₀ + β ∑ max{π(x'), h(x')} P(x, x')`. -/
theorem C_apply (h : X → ℝ) (x : X) :
    (rdConstant hP π c₀ hr).C h x = -c₀ + 1 / (1 + r) * ∑ x', max (π x') (h x') * P x x' := by
  rw [StoppingProblem.C_apply]
  rfl

/-- Exercise 4.2.1 (p. 125): `h*` is increasing whenever `π` is increasing and `P` is monotone
increasing (Lemma 4.1.4 with a constant continuation reward). -/
theorem monotone_hstar [PartialOrder X] (hπ : Monotone π) (hPm : MonotoneIncreasing P) :
    Monotone (rdConstant hP π c₀ hr).hstar :=
  StoppingProblem.monotone_hstar _ hπ (fun _ _ _ => le_rfl) hPm

/-- Exercise 4.2.2 (p. 125): the optimal policy is increasing whenever `π` is increasing and `(Xₜ)`
is IID, i.e. all rows of `P` are identical: then `h*` is constant and Exercise 4.1.11 applies. A
higher state means a more valuable product to market now, while the prospects of waiting do not
depend on the state. -/
theorem monotone_sigmaStar [PartialOrder X] (hπ : Monotone π) (hiid : ∀ x y, P x = P y) :
    Monotone (rdConstant hP π c₀ hr).sigmaStar :=
  StoppingProblem.monotone_sigmaStar_of_iid _ hπ hiid fun _ _ => rfl

end rdConstant

/-! ### IID R&D costs (§4.2.2.2) -/

variable {Wc : Type*} [Fintype Wc] [DecidableEq Wc]

/-- R&D with IID costs (p. 125): the state is `(c, x)` with `c ∼ φ` IID and `x` `P`-Markov, exit
reward `π(x)`, continuation reward `−cost(c)`. -/
noncomputable def rdIID {φ : Wc → ℝ} (hφ : IsDistribution φ) {P : Matrix X X ℝ} (hP : IsMarkov P)
    (cost : Wc → ℝ) (π : X → ℝ) {r : ℝ} (hr : 0 < r) : StoppingProblem (Wc × X) where
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  P := productKernel φ P
  P_markov := isMarkov_productKernel hφ hP
  c := fun x => -cost x.1
  e := fun x => π x.2

namespace rdIID

variable {φ : Wc → ℝ} (hφ : IsDistribution φ) {P : Matrix X X ℝ} (hP : IsMarkov P)
  (cost : Wc → ℝ) (π : X → ℝ) {r : ℝ} (hr : 0 < r)

/-- The Bellman equation (4.18):
`v*(c, x) = max{π(x), −c + β ∑_{x'} ∑_{c'} v*(c', x') φ(c') P(x, x')}`. -/
theorem bellman_equation (c : Wc) (x : X) :
    (rdIID hφ hP cost π hr).vstar (c, x) =
      max (π x) (-cost c + 1 / (1 + r) *
        ∑ x', (∑ c', (rdIID hφ hP cost π hr).vstar (c', x') * φ c') * P x x') := by
  have := congrFun (rdIID hφ hP cost π hr).isFixedPt_T_vstar.eq (c, x)
  rw [← this, StoppingProblem.T, StoppingProblem.cont, rdIID, productKernel_mulVec]

/-- The expected value function (4.19): `g(x) = ∑_{x'} ∑_{c'} v*(c', x') φ(c') P(x, x')`. -/
noncomputable def g : X → ℝ := fun x =>
  ∑ x', (∑ c', (rdIID hφ hP cost π hr).vstar (c', x') * φ c') * P x x'

/-- `v*(c', x') = max{π(x'), −c' + βg(x')}` (p. 126). -/
theorem vstar_eq (c : Wc) (x : X) :
    (rdIID hφ hP cost π hr).vstar (c, x) =
      max (π x) (-cost c + 1 / (1 + r) * g hφ hP cost π hr x) :=
  bellman_equation hφ hP cost π hr c x

/-- The operator `R` of p. 126:
`(Rg)(x) = ∑_{x'} ∑_{c'} max{π(x'), −c' + βg(x')} φ(c') P(x, x')`. -/
noncomputable def R (φ : Wc → ℝ) (P : Matrix X X ℝ) (cost : Wc → ℝ) (π : X → ℝ) (r : ℝ)
    (g : X → ℝ) : X → ℝ := fun x =>
  ∑ x', (∑ c', max (π x') (-cost c' + 1 / (1 + r) * g x') * φ c') * P x x'

/-- (4.20), p. 126: `g` is a fixed point of `R`. -/
theorem isFixedPt_R_g : IsFixedPt (R φ P cost π r) (g hφ hP cost π hr) := by
  funext x
  unfold R
  conv_rhs => rw [g]
  refine sum_congr rfl fun x' _ => ?_
  congr 1
  refine sum_congr rfl fun c' _ => ?_
  rw [vstar_eq]

omit [DecidableEq X] [DecidableEq Wc] in
include hφ hP hr in
/-- Exercise 4.2.3 (p. 126): `R` is a contraction of modulus `β` on `ℝ^X`. -/
theorem isContractionOn_R : IsContractionOn (R φ P cost π r) Set.univ (1 / (1 + r)) where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := by positivity
  lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  norm_sub_le g _ g' _ := by
    have hβ : (0 : ℝ) ≤ 1 / (1 + r) := by positivity
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    have hb : ∀ x', |g x' - g' x'| ≤ ‖g - g'‖ := fun x' => by
      have := norm_le_pi_norm (g - g') x'
      simpa [Real.norm_eq_abs] using this
    unfold R
    calc |∑ x', (∑ c', max (π x') (-cost c' + 1 / (1 + r) * g x') * φ c') * P x x' -
          ∑ x', (∑ c', max (π x') (-cost c' + 1 / (1 + r) * g' x') * φ c') * P x x'|
        = |∑ x', (∑ c', (max (π x') (-cost c' + 1 / (1 + r) * g x') -
            max (π x') (-cost c' + 1 / (1 + r) * g' x')) * φ c') * P x x'| := by
          rw [← sum_sub_distrib]
          congr 1
          refine sum_congr rfl fun x' _ => ?_
          rw [← sub_mul, ← sum_sub_distrib]
          congr 1
          exact sum_congr rfl fun c' _ => by ring
      _ ≤ ∑ x', (∑ c', |max (π x') (-cost c' + 1 / (1 + r) * g x') -
            max (π x') (-cost c' + 1 / (1 + r) * g' x')| * φ c') * P x x' := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => ?_)
          rw [abs_mul, abs_of_nonneg (hP.nonneg x x')]
          refine mul_le_mul_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans
            (sum_le_sum fun c' _ => ?_)) (hP.nonneg x x')
          rw [abs_mul, abs_of_nonneg (hφ.nonneg c')]
      _ ≤ ∑ x', (∑ c', (1 / (1 + r) * ‖g - g'‖) * φ c') * P x x' := by
          refine sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (sum_le_sum fun c' _ =>
            mul_le_mul_of_nonneg_right ?_ (hφ.nonneg c')) (hP.nonneg x x')
          rw [max_comm (π x'), max_comm (π x')]
          refine (abs_max_sub_max_le_abs _ _ _).trans ?_
          rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ]
          exact mul_le_mul_of_nonneg_left (hb x') hβ
      _ = 1 / (1 + r) * ‖g - g'‖ := by
          simp only [← mul_sum, hφ.sum_eq_one, mul_one]
          rw [hP.rowsum, mul_one]

/-- `g` is the unique solution of (4.20) in `ℝ^X`, and successive approximation with `R` converges
to it from any starting point (p. 126). -/
theorem eq_g_of_isFixedPt {g' : X → ℝ} (hg' : IsFixedPt (R φ P cost π r) g') :
    g' = g hφ hP cost π hr :=
  (isContractionOn_R hφ hP cost π hr).fixedPt_unique (Set.mem_univ _) (Set.mem_univ _) hg'
    (isFixedPt_R_g hφ hP cost π hr)

theorem tendsto_iterate_R (g₀ : X → ℝ) :
    Tendsto (fun k : ℕ => (R φ P cost π r)^[k] g₀) atTop (𝓝 (g hφ hP cost π hr)) :=
  (isContractionOn_R hφ hP cost π hr).tendsto_iterate_fixedPt (Set.mem_univ _) (Set.mem_univ _)
    (isFixedPt_R_g hφ hP cost π hr)

/-- The optimal policy (p. 126): `σ*(c, x) = 1{π(x) ≥ −c + βg*(x)}`. -/
theorem sigmaStar_eq_true_iff (c : Wc) (x : X) :
    (rdIID hφ hP cost π hr).sigmaStar (c, x) = true ↔
      -cost c + 1 / (1 + r) * g hφ hP cost π hr x ≤ π x := by
  rw [StoppingProblem.sigmaStar_eq_true_iff]
  have : (rdIID hφ hP cost π hr).hstar (c, x) = -cost c + 1 / (1 + r) * g hφ hP cost π hr x := by
    rw [StoppingProblem.hstar, StoppingProblem.cont, rdIID, productKernel_mulVec]
    rfl
  rw [this]
  rfl

end rdIID

end SargentStachurski.OptimalStopping

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalStopping.Monotonicity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Firm valuation with exit

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.2 (pp. 111–114)
and Examples 4.1.3–4.1.4 (pp. 115).

A firm with `Q`-Markov productivity earns `π(Zₜ)` while operating and may exit
for scrap value `s`, discounting at `β = 1/(1 + r)`. This is a stopping problem
with constant exit reward, so Propositions 4.1.2–4.1.3 apply. The no-exit value
`w = (I − βQ)⁻¹π` is the value of the policy that never exits, hence `w ≤ v*`
(p. 114); Exercise 4.1.7: if `Q ≫ 0` and `s > w(z)` somewhere, then `w ≪ v*`.
Examples 4.1.3–4.1.4: `v*` and `h*` are increasing and the optimal policy is
decreasing when `π` is increasing and `Q` monotone increasing. Exercise 4.1.8:
with stochastic prices and profit `max_ℓ (pℓ^{1/2} − wℓ) = p²/(4w)`, the
Bellman equation takes the stated form.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- The firm with an exit option (p. 111): productivity `Q`-Markov, profit `π`, scrap value `s`,
discount factor `β = 1/(1 + r)`. -/
noncomputable def firmExit {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (π : Z → ℝ) (s : ℝ) {r : ℝ}
    (hr : 0 < r) : StoppingProblem Z where
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  P := Q
  P_markov := hQ
  c := π
  e := fun _ => s

namespace firmExit

variable {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (π : Z → ℝ) (s : ℝ) {r : ℝ} (hr : 0 < r)

omit [DecidableEq Z] in
/-- The policy operator (p. 111): `(T_σ v)(z) = σ(z)s + (1 − σ(z))[π(z) + β ∑ v(z')Q(z, z')]`. -/
theorem Tσ_apply (σ : Policy Z) (v : Z → ℝ) (z : Z) :
    (firmExit hQ π s hr).Tσ σ v z =
      if σ z then s else π z + 1 / (1 + r) * ∑ z', v z' * Q z z' := by
  rw [StoppingProblem.Tσ, StoppingProblem.cont_apply]
  rfl

omit [DecidableEq Z] in
/-- The Bellman operator (p. 111): `(Tv)(z) = max{s, π(z) + β ∑ v(z')Q(z, z')}`. -/
theorem T_apply (v : Z → ℝ) (z : Z) :
    (firmExit hQ π s hr).T v z = max s (π z + 1 / (1 + r) * ∑ z', v z' * Q z z') := by
  rw [StoppingProblem.T_apply]
  rfl

/-- The Bellman equation for the firm (p. 112): `v*(z) = max{s, π(z) + β ∑ v*(z')Q(z, z')}`, with
`v*` its unique solution. -/
theorem bellman_equation (z : Z) :
    (firmExit hQ π s hr).vstar z =
      max s (π z + 1 / (1 + r) * ∑ z', (firmExit hQ π s hr).vstar z' * Q z z') := by
  rw [StoppingProblem.bellman_equation]
  rfl

/-- `v* = s ∨ h*` (p. 112): the value is the larger of the scrap value and the continuation
value `h* = π + βQv*`. -/
theorem vstar_eq_max (z : Z) :
    (firmExit hQ π s hr).vstar z = max s ((firmExit hQ π s hr).hstar z) :=
  StoppingProblem.vstar_eq_max_hstar _ z

/-- The `v*`-greedy policy exits when the continuation value falls below the scrap value
(p. 112): `σ*(z) = 1 ⟺ h*(z) ≤ s`. -/
theorem sigmaStar_eq_true_iff (z : Z) :
    (firmExit hQ π s hr).sigmaStar z = true ↔ (firmExit hQ π s hr).hstar z ≤ s :=
  StoppingProblem.sigmaStar_eq_true_iff _ z

/-! ### Exit versus no-exit (§4.1.2.2) -/

/-- The no-exit value `w` (p. 112): the value of the policy `σ ≡ 0` that never exits. -/
noncomputable def noExitValue : Z → ℝ := (firmExit hQ π s hr).vσ fun _ => false

omit [DecidableEq Z] in
/-- `w = π + βQw` (p. 114). -/
theorem noExitValue_eq (z : Z) :
    noExitValue hQ π s hr z = π z + 1 / (1 + r) * ∑ z', noExitValue hQ π s hr z' * Q z z' := by
  unfold noExitValue
  rw [StoppingProblem.vσ_of_continue _ _ rfl]
  rfl

/-- `w = (I − βQ)⁻¹π` (p. 114, by Lemma 3.2.1): `L_σ = βQ` and `r_σ = π` for `σ ≡ 0`. -/
theorem noExitValue_eq_inv :
    noExitValue hQ π s hr = (1 - (1 / (1 + r)) • Q)⁻¹ *ᵥ π := by
  unfold noExitValue
  rw [StoppingProblem.vσ_eq_inv]
  have hL : (firmExit hQ π s hr).L (fun _ => false) = (1 / (1 + r)) • Q := by
    ext z z'
    simp [StoppingProblem.L_apply, firmExit]
  have hr' : (firmExit hQ π s hr).r (fun _ => false) = π := by
    funext z
    simp [StoppingProblem.r, firmExit]
  rw [hL, hr']

/-- p. 114: `w ≤ v*`, since never exiting is a feasible policy. -/
theorem noExitValue_le_vstar : noExitValue hQ π s hr ≤ (firmExit hQ π s hr).vstar :=
  StoppingProblem.vσ_le_vstar _ _

/-- Exercise 4.1.7 (p. 114): if `Q ≫ 0` and `s > w(z₀)` for some `z₀`, then `w ≪ v*`: the option
to exit is strictly valuable everywhere, because every state reaches `z₀` next period with positive
probability, where exiting beats continuing. -/
theorem noExitValue_lt_vstar (hQpos : ∀ z z', 0 < Q z z') {z₀ : Z}
    (hz₀ : noExitValue hQ π s hr z₀ < s) (z : Z) :
    noExitValue hQ π s hr z < (firmExit hQ π s hr).vstar z := by
  set S := firmExit hQ π s hr with hS
  have hle := noExitValue_le_vstar hQ π s hr
  -- at `z₀` the value function is strictly above `w`
  have h0 : noExitValue hQ π s hr z₀ < S.vstar z₀ := by
    have := S.bellman_equation z₀
    rw [hS] at this
    calc noExitValue hQ π s hr z₀ < s := hz₀
      _ ≤ S.vstar z₀ := by rw [bellman_equation]; exact le_max_left _ _
  -- hence the expectation under any row of `Q ≫ 0` is strictly larger
  have hsum : ∑ z', noExitValue hQ π s hr z' * Q z z' < ∑ z', S.vstar z' * Q z z' := by
    refine sum_lt_sum (fun z' _ => mul_le_mul_of_nonneg_right (hle z') (hQpos z z').le)
      ⟨z₀, mem_univ _, mul_lt_mul_of_pos_right h0 (hQpos z z₀)⟩
  have hβ : (0 : ℝ) < 1 / (1 + r) := by positivity
  calc noExitValue hQ π s hr z = π z + 1 / (1 + r) * ∑ z', noExitValue hQ π s hr z' * Q z z' :=
        noExitValue_eq hQ π s hr z
    _ < π z + 1 / (1 + r) * ∑ z', S.vstar z' * Q z z' := by
        linarith [mul_lt_mul_of_pos_left hsum hβ]
    _ ≤ S.vstar z := by rw [bellman_equation]; exact le_max_right _ _

/-! ### Monotonicity (Examples 4.1.3–4.1.4) -/

variable [PartialOrder Z]

/-- Example 4.1.3 (p. 115): `v*` and `h*` are increasing when `π` is increasing and `Q` is monotone
increasing, since the scrap value is constant. -/
theorem monotone_vstar_hstar (hπ : Monotone π) (hQm : MonotoneIncreasing Q) :
    Monotone (firmExit hQ π s hr).vstar ∧ Monotone (firmExit hQ π s hr).hstar :=
  ⟨StoppingProblem.monotone_vstar _ (fun _ _ _ => le_rfl) hπ hQm,
    StoppingProblem.monotone_hstar _ (fun _ _ _ => le_rfl) hπ hQm⟩

/-- Example 4.1.4 (p. 115): under the same conditions the optimal policy is decreasing: exit is
optimal when the state is small and continuing when it is large. -/
theorem antitone_sigmaStar (hπ : Monotone π) (hQm : MonotoneIncreasing Q) :
    Antitone (firmExit hQ π s hr).sigmaStar :=
  StoppingProblem.antitone_sigmaStar_of_const _ (fun _ _ => rfl) hπ hQm

end firmExit

/-! ### Exercise 4.1.8: stochastic prices -/

/-- Exercise 4.1.8 (p. 114): with price `p ≥ 0` and wage `w > 0`, the one-period profit
`max_{ℓ ≥ 0} (p√ℓ − wℓ)` equals `p²/(4w)`, attained at `ℓ = (p/(2w))²`. -/
theorem isGreatest_profit {p w : ℝ} (hp : 0 ≤ p) (hw : 0 < w) :
    IsGreatest ((fun ℓ => p * Real.sqrt ℓ - w * ℓ) '' Set.Ici 0) (p ^ 2 / (4 * w)) := by
  constructor
  · refine ⟨(p / (2 * w)) ^ 2, Set.mem_Ici.2 (sq_nonneg _), ?_⟩
    have hsq : Real.sqrt ((p / (2 * w)) ^ 2) = p / (2 * w) :=
      Real.sqrt_sq (div_nonneg hp (by positivity))
    simp only [hsq]
    field_simp
    ring
  · rintro y ⟨ℓ, hℓ, rfl⟩
    have hℓ' : 0 ≤ ℓ := hℓ
    have hsq : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ'
    have hs0 : 0 ≤ Real.sqrt ℓ := Real.sqrt_nonneg ℓ
    change p * Real.sqrt ℓ - w * ℓ ≤ p ^ 2 / (4 * w)
    rw [le_div_iff₀ (by positivity)]
    set t := Real.sqrt ℓ with ht
    rw [← hsq]
    nlinarith [sq_nonneg (p - 2 * w * t)]

/-- Exercise 4.1.8 (p. 114): the firm with constant productivity, `Q`-Markov prices, profit
`π(p) = p²/(4w)` from the optimal labour choice, scrap value `s` and interest rate `r`. -/
noncomputable def priceFirm {Pm : Type*} [Fintype Pm] {Q : Matrix Pm Pm ℝ} (hQ : IsMarkov Q)
    (price : Pm → ℝ) (w s : ℝ) {r : ℝ} (hr : 0 < r) : StoppingProblem Pm :=
  firmExit hQ (fun p => price p ^ 2 / (4 * w)) s hr

/-- Exercise 4.1.8 (p. 114), the Bellman equation:
`v*(p) = max{s, p²/(4w) + β ∑ v*(p')Q(p, p')}` with `β = 1/(1 + r)`. -/
theorem priceFirm_bellman {Pm : Type*} [Fintype Pm] [DecidableEq Pm] {Q : Matrix Pm Pm ℝ}
    (hQ : IsMarkov Q) (price : Pm → ℝ) (w s : ℝ) {r : ℝ} (hr : 0 < r) (p : Pm) :
    (priceFirm hQ price w s hr).vstar p =
      max s (price p ^ 2 / (4 * w) +
        1 / (1 + r) * ∑ p', (priceFirm hQ price w s hr).vstar p' * Q p p') :=
  firmExit.bellman_equation hQ _ s hr p

end SargentStachurski.OptimalStopping

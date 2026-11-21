# Corrections and conventions

Places where a Lean statement differs from Miao's Chapter 5 (draft of 21 April 2013): a claim
corrected, a hypothesis made explicit, or a convention chosen.

## Corrections

| Where | Book | Lean |
| --- | --- | --- |
| p. 145 | The stopping problem as an MDP with `Γ(ŝ) = ∅` at the absorbing state. | Then `Γ` has no selection and no plan is feasible for `T ≥ 2` (`bookΓ_infeasible`). With `Γ(ŝ) = A` the MDP is well posed and its values equal the stopping values (`toMDP`, `V0_toMDP`, `V_toMDP`). |
| p. 144 | The transition "densities" `1 − exp(−λ(·))` of the Rust model. | They are distribution functions (`rust_cdf_keep`, `rust_cdf_replace`). |
| p. 150 | `P_{t+1}(s, i; B) = 0` for all other `B`. | False: `B = S` has probability one (`bandit_book_false`). What holds is `P(B) = 0` for measurable `B` disjoint from the frozen fibre (`bandit_P_frozen`). |
| p. 154 | The control kernel, with a free `z_{t+1}`. | `P((x, z), a; B₁ × B₂) = ∫_{B₂} 1_{B₁}(φ(x, a, z, z′)) Q(z, dz′)` (`controlKernel_rect`); the book's product form holds when `φ` does not depend on `z′` (`controlKernel_rect_of_indep`). |
| Example 5.1.1(a), p. 141 | `V₀ = 1/s + s` on `(0, 2)` and `+∞` for `s < 0`. | `V₀ = 1/s + s` on `(0, 2]`, `+∞` for `s ≤ 0`, and `−∞` for `s > 2`, where `Γ = ∅` (`example_5_1_1a_pos`, `example_5_1_1a_nonpos`, `example_5_1_1a_empty`). |
| p. 142 | Randomized plans with "`Γ(s) ∈ A`". | `Γ(s) ∈ 𝒜`, i.e. `Γ(s)` measurable (`IsFeasibleR`). |
| Ex 5, p. 156 | `F : ℝ₊ → ℝ`. | `F(K, N)`; capital lives in `ℝ≥0` (`ramsey1`, `ramsey2`). |

## Conventions and departures

| Where | Book | Lean |
| --- | --- | --- |
| (5.1) | `P_{t+1}`; the horizon `T`. | The field `P t` is the book's `P_{t+1}`; `T : ℕ∞` is an argument. |
| p. 139 | The measure on infinite histories. | Built with Mathlib's Ionescu Tulcea (`Kernel.traj`); histories include `s₀`, which is a.s. the given state (`muInf`). |
| §5.2.2 | `β ∈ (0, 1]` for stopping problems, but `β ∈ (0, 1)` in Assumption 5.1.2. | The equivalence theorems hold for every `β`; the finite-horizon assumptions are proved without `β < 1` (the secretary problem needs `β = 1`). |
| (5.7), Ex 2 | Payoffs in the price `z`. | A bounded payoff `y(z)`, as the boundedness assumptions need. |
| pp. 147–149 | The secretary problem's dates and payoffs. | Dates are shifted by one and payoffs past the horizon capped with `min`; only the marginal probabilities of the relative-rank process are proved (`secretary_prob`), not its Markov property. Exercise 3's reward formulas are derived in the docstring, not proved. |
| p. 151 | A two-armed bandit with one constant arm is a stopping problem. | Proved for a deterministic risky arm over `T` periods (`ex_bandit_constant_arm`); the stochastic case needs the dynamic programming of Chapters 6–7. |
| Ex 4 | Pandora's boxes with box-specific discount factors. | A common `β`; "collect" is retiring on an open box. |
| §5.2.1 | Mileage in `ℝ₊`. | The model is set on `ℝ` with `ℝ₊` invariant (`rust_nonneg`). |
| pp. 142–143 | Randomized plans on infinite histories. | Only finite horizons (`rmu`); the infinite-horizon measure is the same construction as `muInf`. |

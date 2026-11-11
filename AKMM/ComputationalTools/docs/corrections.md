# Corrections and departures: AKMM Chapter 10

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 10, Computational tools, pp. 261–283. Lean names are relative to
`AKMM.ComputationalTools`. Every book item is located in the [source map](source-map.md).

## Departures

1. **p. 264, the bisection test.** The book compares `sign(f(c))` with `sign(f(a))`. The Lean
   step tests `0 < f(a)f(c)`; the two agree whenever `f(a) ≠ 0` (`bisect_sign_eq_iff`), and the
   invariant kept is `f(a_k)f(b_k) ≤ 0` (`bisect_bracket`), which also covers a root hit exactly.

2. **p. 267, the length of the golden-section bracket.** The book: starting from
   `(c − b)/(c − a) = ω*`, "after iterating `n` times … the length of the remaining bracket … is
   `(1 − ω*)ⁿ(c − b)`". Each step multiplies the whole bracket length by `1 − ω*`
   (`goldenStep_spec`), so the length is `(1 − ω*)ⁿ(c − a)` (`golden_length`); the printed value is
   strictly smaller for every `n` (`golden_printed_length_counterexample`). The step also keeps the
   golden proportion and the bracket property, and every bracket contains a local maximiser
   (`golden_iterate_max`); the bracket property is kept in its weak form `F(a) ≤ F(b) ≥ F(c)`, since
   the strict form is lost when `F(x) = F(b)`.

3. **p. 269, "about one-third".** Golden-section search removes the fraction `ω* ≈ 0.382` of the
   bracket per step (`golden_removed_fraction`), not one third; the comparison with bisection's
   one half stands.

4. **p. 271, the Rouwenhorst recursion.** The book prints
   `Π_N = p[Π 0; 0′ 0] + (1 − p)[0 Π; 0 0′] + p[0′ 0; Π 0] + (1 − p)[0 0′; 0 Π]`. The weights of the
   last two matrices are swapped: the recursion of Rouwenhorst (1995) and Kopecky–Suen (2010) is
   `p[Π 0; 0′ 0] + (1 − p)[0 Π; 0 0′] + (1 − p)[0′ 0; Π 0] + p[0 0′; 0 Π]`. With the printed weights the
   method fails: for `N = 3`, `p = 3/4` (`ρ = 1/2`) the binomial law `(1/4, 1/2, 1/4)` is not
   invariant and the conditional mean at the top state of the grid `z̄_j = j − 1` is `0` instead of
   `ρz̄ = 1/2` (`rouwenhorstPrinted`, `rouwenhorst_printed_counterexample`). With the corrected weights
   row `i` of `Π_N` has generating polynomial `(p + (1 − p)X)^{N−1−i}((1 − p) + pX)^i`
   (`rouwenhorst_eq_coeff`), the invariant law is `Binomial(N − 1, 1/2)` (`rouwenhorst_invariant`), and
   `p = (1 + ρ)/2`, `m = √(N − 1)` give mean `0`, variance `σ_z²` and autocorrelation `ρ`
   (`rouwenhorst_matches_ar1`). The Lean recursion starts from `Π₁ = [1]`, which reproduces the book's
   `Π₂` (`rouwenhorst_two`).

5. **p. 271, Tauchen's interior probabilities.** For `j = 2, …, N − 1` the book prints
   `π_{ij} = F((z̄ʲ − ρz̄ⁱ − ω/2)/σ_ε) − F((z̄ʲ − ρz̄ⁱ + ω/2)/σ_ε)`, the negative of the probability
   of `[z̄ʲ − ω/2, z̄ʲ + ω/2]` that the text describes. For a strictly increasing `F` these entries
   are negative (`tauchen_printed_neg`) and the rows sum to `1 + 2(F(u₁) − F(u_{N−1})) < 1`
   (`tauchen_printed_row_sum`; the Cauchy distribution function is a concrete such `F`,
   `tauchenCauchyCdf_strictMono`). With the two terms swapped (`tauchenProb`) every row is a
   probability vector for any distribution function `F` (`tauchen_stochastic`).

6. **(10.17), p. 278, and the vector `E` of (10.27), p. 281.** The coefficient of `z_t` is printed as
   `β(1 + θ(1 − α))K̄^{α−1}H̄^{1−α}ρ`. Substituting `h_{t+1} = θ(z_{t+1} + αk_{t+1} − c_{t+1})` into the
   log-linearised Euler equation `−c_t = E_t[βαK̄^{α−1}H̄^{1−α}(z_{t+1} + (α − 1)k_{t+1} + (1 − α)h_{t+1}) − c_{t+1}]`
   gives `βα(1 + θ(1 − α))K̄^{α−1}H̄^{1−α}ρ`: the factor `α` is missing, as it is present in the
   `k_{t+1}` and `E_t c_{t+1}` coefficients (`eq_10_17`; the printed value differs for every
   `α ∈ (0, 1)`, `eq_10_17_printed_counterexample`). The second entry of `E` in (10.27) is
   corrected the same way (`rbcE`, `eq_10_27`). The survey's numerical check: with `α` restored,
   Example 5's printed solution `c = 0.5691k + 0.3920z`, `k′ = 0.9537k + 0.1132z`,
   `h = −0.2431k + 0.7070z` is reproduced, so the error is in the display only (numerical, not
   formalised).

7. **p. 262, "the approximated function is not differentiable at the grid points".** This holds at a
   grid point where the slopes of the two adjacent linear pieces differ
   (`linInterp_kink_not_differentiable`); where they agree (for example when `f` is affine near the
   point) the interpolant is differentiable there (`linInterp_kink_differentiable_of_eq`).

## Precisions (not errors)

8. **p. 266, Newton–Raphson "can be much faster … if `x₀` is close to the true solution".** Proved as
   local quadratic convergence for `C²` `f` with a simple root (`newton_local_quadratic`,
   `newton_converges`); the book states no hypotheses.

9. **p. 271, "the invariant distribution … converges to a normal distribution as `N → ∞`".** Proved:
   the invariant distribution is exactly `Binomial(N − 1, 1/2)` on the grid (`rouwenhorst_invariant`);
   the normal limit (de Moivre–Laplace) is cited and not formalised.

10. **p. 272, value-function iteration.** The contraction argument is formalised for the grid
    algorithm the chapter actually runs (finite state space, choices on the grid, any Markov
    transition: `GridDP.vfi`) and, for the continuous cake-eating problem, by a direct contraction
    argument on bounded solutions of the Bellman equation (`cake_bellman_unique`). The closed form
    `V(a) = √(a/(1 − β²))`, policy `a′ = β²a`, is not in the book (`cake_bellman`).

11. **pp. 278–279, "finite" limits.** The book requires `lim_{T→∞} y_{t+T}` (or
    `lim E_t[y_{t+T}]`) to "remain finite"; the Lean statements use boundedness of the sequence in
    `T`, which is what the argument uses (for `λ > 1` and `y_t ≠ 0` the sequence is unbounded; for
    `λ ≤ 1` it is bounded, though for `λ = −1`-type cases it need not converge). `eq_10_20`,
    `eq_10_23`, `bk_fn8`.

12. **p. 281, the Blanchard–Kahn condition.** "Unique if `h = m`" needs also that `H̃₂₂` (the block of
    `H⁻¹` linking the unstable directions to the jump variables) is invertible, which the book uses
    when it writes `H̃₂₂⁻¹`; `bk_condition` assumes both (Miao's Theorem 1.4.2), in the
    certainty-equivalent form `[x_{t+1}; y_{t+1}] = F[x_t; y_t] + Ga_t`.

13. **(10.26), p. 280.** `E` denotes both the shock-loading matrix and the expectation operator; the
    Lean names are `rbcE` and `CondExpSystem.E`.

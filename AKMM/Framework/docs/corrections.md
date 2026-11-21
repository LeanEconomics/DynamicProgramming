# Corrections and departures: AKMM Chapter 2

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 2, A framework for macroeconomics, pp. 43–69. Lean names are relative to
`AKMM.Framework`. Every book item is located in the [source map](source-map.md).

## Corrections

1. **p. 64, Boppart–Krusell growth rates.** The book: "With technology and output growth
   proceeding at a net rate γ, we then have hours grow at `(1 + γ)^{−ν}` and consumption at
   `(1 + γ)^{1−ν}`. Wages now grow slightly faster than output, and the labor share remains a
   constant share of output." This is inconsistent. With labour-augmenting technology growing at
   `λ = 1 + γ`, hours at `λ^{−ν}` and the capital–effective-labour ratio constant, output grows at
   `λ^{1−ν}`, the wage at `λ`, and the labour share is constant (`ls_bk_production`); together with
   the household side (`ls_bk_balanced_growth`), consumption grows at `λ^{1−ν}` as output does.
   Output does not grow at `γ`: for `λ > 1`, `ν > 0`, `λ^{1−ν} < λ`, and if output grew at `λ`
   with a constant consumption share, consumption would grow at `λ`, never at `λ^{1−ν}`
   (`ls_p64_output_growth_correction`). The words "and output" should be deleted: technology and
   the wage grow at `γ`. This reading is the one under which "wages now grow slightly faster than
   output" holds.
2. **p. 64, "`g(·)` is a decreasing function".** For `u(c, 1 − ℓ) = (c^{1−σ}g(x) − 1)/(1 − σ)`,
   `x = c^{ν/(1−ν)}ℓ`, the marginal utility of hours is `c^{1−σ}c^{ν/(1−ν)}g′(x)/(1 − σ)`. With
   `g′ < 0` this is negative (hours are a bad) only when `σ < 1`; when `σ > 1` it is positive
   (`ls_bk_hours_marginal_sign`). Counterexample: `σ = 2`, `ν = 1/2`, `g(x) = 2 − x`, at `c = 1`,
   `ℓ = 1/2` (where `g > 0`), `∂u/∂ℓ = 1 > 0` (`ls_bk_decreasing_g_counterexample`). The
   restriction should be "`g` decreasing if `σ < 1`, increasing if `σ > 1`" (equivalently, write
   the utility as `((c ĝ(x))^{1−σ} − 1)/(1 − σ)` with `ĝ` decreasing). It is also what the book's
   own `ν = 0` collapse requires: there `g(ℓ) = v(1 − ℓ)^{1−σ}` (`ls_bk_nu_zero`), which for `v`
   increasing in leisure is decreasing in `ℓ` exactly when `σ < 1`. The "if" direction proved
   here does not use the sign of `g′`.
3. **p. 52, the derivation of (2.3): "(∂F/∂t)dt = (∂F/∂ℓ)ℓ dz" (checked: notation, not an
   error).** The book writes `F(k, ℓ, t) = F(k, zℓ)` with the same letter for both functions.
   With `G` the time-independent function, `∂F/∂t = G₂ ℓ ż` and the wage is `w = zG₂`, so the
   printed identity holds with `∂F/∂ℓ` read as `G₂ = w/z`, which is how the book then uses it
   ("replaced ∂F/∂ℓ by w/z") (`ga_labour_augmenting_partials`); (2.3) is correct (`eq_2_3`).
   Read as the partial of `F(k, ℓ, t)` in `ℓ`, i.e. `zG₂`, the identity is off by the factor `z`:
   for `G(a, b) = b`, `z(t) = 2t`, `ℓ = 1` at `t = 1`, `F_t = 2` but `F_ℓ ℓ ż = 4`
   (`ga_eq_2_3_partial_misreading`).

## Departures

4. **Growth accounting, (2.1)–(2.3).** The book's "assume differentiability" is made precise as
   Fréchet differentiability of `F` in `(k, ℓ, t)` at the current point (for (2.2), (2.3): of
   `G` in `(k, ℓ)` and of `z`, `k`, `ℓ` in `t`); `α` is defined as `rk/y`, and `y, k, ℓ, z ≠ 0`
   are assumed so that the growth rates exist. Constant returns are only used along the ray
   through the current input pair (Euler's theorem, Miao's `rm_euler_homogeneous`). The factor
   prices are hypotheses `r = F_k`, `w = F_ℓ`; that they follow from profit maximisation is
   `ga_profit_foc`. (2.2) and (2.3) are derived from (2.1) as in the book.
5. **The dynamic system.** The ratio `k/y = s/(γ + δ)` needs `γ + δ ≠ 0` and `y > 0`. The
   "minimal conditions" for the constant solution are EconomicGrowth's: `F(·, ℓ)` neoclassical
   (`Technology`: continuous, `F(0, ℓ) = 0`, differentiable with continuous derivative, strictly
   concave, increasing, Inada), `s > 0`, `δ ≤ 1`, `γ > −1`, `γ + δ > 0`; detrending uses constant
   returns on the nonnegative quadrant and `ℓ ≥ 0`. The book's steady state and convergence claims
   are proved by connecting the detrended system to EconomicGrowth's discrete-time Solow map
   (`Solow1956.DiscreteTime.next`) rather than reproved. Uzawa's theorem is not formalised.
6. **The Euler equation (p. 62).** The book obtains it by equating the marginal rate of
   substitution along an indifference curve to the relative price `R`; here it is the
   first-order condition of `max u(c₀) + βu(R(W − c₀))` at an interior local maximum, which is
   the same condition.
7. **KPR and Boppart–Krusell, the "if" directions.** "Balanced growth is consistent with the
   derived equations" is stated as: if the hours condition holds at the initial point, then along
   the balanced path (consumption and wage growing at `λ` with constant hours for KPR;
   consumption at `λ^{1−ν}`, hours at `λ^{−ν}`, wage at `λ` for Boppart–Krusell) the hours
   condition holds every period and the Euler equation holds with a constant interest rate
   (`λ^σ/β`, resp. `λ^{(1−ν)σ}/β`). KPR needs `σ ≠ 1` for its partials (the log case is Miao's
   (14.6)); Boppart–Krusell needs `ν ≠ 1` and `u_c ≠ 0` at the initial point. The hours
   condition for Boppart–Krusell is written with hours as the argument, `−u_ℓ/u_c = w`, which is
   the book's `u₂/u₁ = w` since `u₂ = −u_ℓ`.
8. **The aggregation box (footnote a).** The exercise is formalised for interior allocations
   with `G` concave, of constant returns and positive on the positive quadrant, and `a > 0`.
   "A relative price is implied" is proved as: an interior value-maximising allocation exists
   only at `p = a`.
9. **Not formalised** (cited, not proved in the book): Uzawa's theorem (p. 56, Appendix 3.A),
   the "only if" part for CRRA (p. 63, Appendix 4.A.2), the King–Plosser–Rebelo and
   Boppart–Krusell "only if" characterisations (p. 64).

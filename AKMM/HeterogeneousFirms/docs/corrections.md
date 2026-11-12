# Corrections and departures: AKMM Chapter 22

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 22, Heterogeneous firms (T. Mukoyama), pp. 663–692, and Appendix 22.A,
pp. 888–896. Lean names are relative to `AKMM.HeterogeneousFirms`. Every book item is located in
the [source map](source-map.md).

## Corrections

1. **p. 893, App. 22.A.4, the Bertrand first-order condition.** Printed: "`(1 − (q/p̂)/(∂q/∂p̂))p̂
   = M`" and "`(q/p̂)/(∂q/∂p̂) = 1/ε(s)`". Since demand slopes down, `∂q/∂p̂ = −εq/p̂`
   (`bertrand_demand_deriv`), so `(q/p̂)/(∂q/∂p̂) = −1/ε` (`bertrand_ratio`; the printed `1/ε` is false, `bertrand_ratio_printed_false`), and dividing the
   first-order condition `p̂ ∂q/∂p̂ + q = M ∂q/∂p̂` by `∂q/∂p̂` gives `(1 + (q/p̂)/(∂q/∂p̂))p̂ = M`
   (`bertrand_markup`). The two sign slips cancel, so the final pricing rule
   `p̂ = ε/(ε−1)·M` is right.
2. **p. 892, (22.A.2) and the line above it.** `p̂ᵢⱼ = λᵢqᵢⱼ^{−1/η}yᵢⱼ^{1/η}` should have the sector
   output `yᵢ`, not `yᵢⱼ`, as in (22.24) (`eq_22_24`, `eq_22_25`).

## Departures

1. **The continuum of firms.** The unit mass of firms is a probability space `(Ω, P)` and the
   book's "law of large numbers" (`∫ · di = E[·]`, pp. 888–889) is the identification of the
   cross-section integral with `∫ · ∂P`. The lognormal and bivariate-normal assumptions are
   stated as laws of `log a` (and `log(1 − τ)`) under `P` (`eq_22_8`, `eq_22_11`).
2. **Misallocation for general distributions.** The book shows that wedge dispersion lowers `A`
   only for the bivariate lognormal case (22.11). We prove it for every distribution
   (`wedge_A_le`), from the planner bound `simple_planner_A`, and that `A ≥ ∫ a` for every
   distribution (`aggTFP_ge_mean`).
3. **Hopenhayn–Rogerson on a grid.** The firm problem (22.13) is posed on finite grids of
   productivity and employment. Strict monotonicity of the entry value in the wage (hence
   uniqueness of the free-entry wage) uses the extra hypothesis that every employment level on
   the grid is at least some `m > 0` (`hr_entry_strictAnti`); the book does not argue existence
   or uniqueness. The stationary distribution for a given entry mass uses a survivor matrix with
   row sums at most `q < 1` (positive exit probability everywhere).
4. **Monopolistic competition.** The monopolist's problem is well posed exactly when
   `γ(σ−1)/σ < 1`, which we assume (`eq_22_19`); this includes constant returns `γ = 1`, as the
   book remarks.

## Further corrections

3. **p. 896, App. 22.A.6, the inner summation bound.** In the equation for `M_{k,t+1}` the firms
   that grow from `k − h` to `k` lines lose `i` and gain `i + h ≤ k − h` lines, so `i` runs from
   `0` to `k − 2h`, not to `⌊k/2 − h⌋` (`fsd_from_below`). For `k = 4`, `h = 1` the printed sum
   stops at `i = 1` and omits `P_μ(3,2)P_η(3,3) = 3μ²(1−μ)η³ > 0` (`fsd_printed_bound_false`).
   The outer bound `⌊k/2⌋` is right (`fsd_below_zero`). Also on p. 896: a `+` is missing before
   the second line of the `M_{k,t+1}` equation, and `P_μ(a, b)` is described as "the probability of
   losing `i` product lines when starting from `k` lines" (read `b` and `a`).
4. **p. 690, (22.46), entry labour.** Each entrant hires `c_e` units of labour (p. 689), so entry
   uses `c_eν`, not `ν`: the labour market is `C₀/λ + R(η) + c_eν = L`. `kk_equilibrium` solves the
   corrected system. The printed form is right only if `c_e = 1` (`kk_labour_printed_false`).
5. **p. 689, (22.41).** The innovation cost is written `w_t c(η)`; everywhere else (and in (22.42))
   it is `w_tR(η)`. Notation slip.
6. **p. 690, growth calculation.** "The next inequality uses" should read "equality". The step
   `E[J_t] = μt` presumes `J₀ = 0`, while the normalisation `q₀ = λ` makes `J₀ = 1`; only the
   difference `E[J_{t+1}] − E[J_t] = μ` matters (`kk_growth`). The book's `γ ≈ μ log λ` is exact
   for `log(1 + γ)`: `w_{t+1}/w_t = λ^μ` (`kk_growth`).
7. **p. 677, Table 22.2.** The first column is headed `τ = 0`; it is the `κ = 0` baseline
   (with `τ = 0` throughout). Not formalised (table).
8. **p. 684, footnote 20.** "the time period for Figure 22.1 is 2019", but Figure 22.1 is titled
   2022. Not formalised (data).
9. **p. 682, footnote 18.** "Gabaix (2011) estimates GDP volatility to be 12%". The surrounding
   argument (`σ` between 10% and 20% and `1/√N = 0.001` give an aggregate effect "two orders of
   magnitude smaller than the volatility of GDP") requires GDP volatility of about 1–2%, so the 12%
   is inconsistent with the text; it matches the coefficient `0.12` on `σ` reported on p. 685 (or
   firm-level volatility). Moderate confidence; not formalised (data).
10. **pp. 671, 672, 678, cross-references.** "In Section 22.1, we have seen", "consider the model of
    Section 22.1" and "Consider the setting in Section 22.1" refer to the simple model of
    Section 22.2.
11. **p. 682, indexing.** Firms are indexed `i = 0, 1, …, N` but the sums in (22.30) run from
    `i = 1` to `N`; with `N` firms `σ_Y = σ/√N` (`granular_equal_sizes`).

## Further departures

5. **Hulten's theorem.** The book applies "the envelope theorem" to the planner's problem. We
   prove the theorem in the competitive economy, using the First Welfare Theorem of SLP Chapter 15
   (imported) to identify the equilibrium utility with the planner's value, and assume that the
   planner's value is differentiable in `aᵢ` (the envelope theorem presumes it). The consumer's
   first-order condition (22.A.5) with the book's normalisation `λ = 1` is a hypothesis (the
   gradient of `U` at `c` is the price functional). Instead of Lagrange multipliers, the proof uses
   the feasible perturbation that sends the extra output of sector `i` to consumption, a lower bound
   for the planner's value touching it at `aᵢ` (`hulten`). A one-sector economy satisfies all the
   hypotheses (`hulten_one_sector`). Factors are a finite set (labour in the
   appendix; capital and labour in the text and example).
6. **Granularity.** (22.30) uses only that the shocks have unit variance and are uncorrelated
   (the book assumes i.i.d.) (`eq_22_30`). Gabaix's limit under Zipf's law is not formalised
   (decision 5).
7. **Klette–Kortum.** Expected growth of `J_t` and of a firm's lines uses Bernoulli indicators with
   the stated means and linearity of expectation (`kk_growth`, `kk_gibrat`); the first-order
   condition (22.43) is shown sufficient for convex `R` (`eq_22_43`); the equilibrium is solved for
   `(C₀, μ)` given `η` (`kk_equilibrium`).

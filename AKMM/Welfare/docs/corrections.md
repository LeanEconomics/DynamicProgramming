# Corrections and departures: AKMM Chapter 6

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 6, Welfare, pp. 159–186, and Appendix 6.A, pp. 838–839. Lean names are
relative to `AKMM.Welfare`. Every book item is located in the [source map](source-map.md).

## Corrections

1. **p. 161, Theorem 6.1 needs nonnegative prices.** The last step of the proof multiplies the
   resource constraint (6.1), an inequality, by `p`. Without `p ≥ 0` the theorem is false. One
   consumer, two goods, `x ≿ y` iff `x₀ − x₁ ≥ y₀ − y₁` (good 1 is a bad), `X = ℝ²₊`,
   endowment `(1, 1)`, `Y = {0}`: the prices `(1, −1)` and the allocation `(1, 1)` form a
   competitive equilibrium with transitive, locally nonsatiated preferences, but `(1, 0)` (dispose
   of the bad, which (6.1) allows) is feasible and strictly preferred
   (`theorem_6_1_counterexample`). The theorem is proved with `p ≥ 0` (`theorem_6_1`,
   `fwt_lump_sum`). `p ≥ 0` holds automatically when some consumer can add a unit of any good and
   strictly prefers to (`fw_price_nonneg`).

2. **p. 171, the consumption possibility set with a borrowing constraint.** The book prints
   `q₀c₁ ≤ ω₀ + a₀ − c₀ − q₀ω₁`. From `c₀ + q₀a₁ = ω₀ + a₀`, `c₁ + q₁a₂ = ω₁ + a₁` and
   `a₂ ≥ 0` the constraint is `q₀c₁ ≤ ω₀ + a₀ − c₀ + q₀ω₁` (`borrow_possibility_set`).
   Counterexample to the printed one: autarky with `ω₀ = ω₁ = 1`, `q₀ = 1`, `a = 0`, `c = 1`
   satisfies every constraint but the printed inequality reads `1 ≤ −1`
   (`borrow_possibility_set_printed_counterexample`).

3. **p. 179, "optimal if and only if the limit net real interest rate is equal to or above 0".**
   False at 0. In the log economy with `ω_{y,t} = 1`, `ω_{o,t} = ((t + 1)/(t + 2))²` the unique
   equilibrium (autarky) has gross rate `((t + 2)/(t + 3))² → 1`, yet transfers
   `δₜ = 1/(2(t + 2))` from young to old make the initial old strictly and every generation weakly
   better off (`og_limit_rate_one_counterexample`); the `(2, 2)` economy has gross rate `1` and is
   optimal (`og_example_2_2`). What holds: a limit gross rate above one gives optimality for any
   utilities strictly increasing in `c_y` and bounded young endowments (`og_limit_rate_gt_one`);
   a limit below one gives inefficiency, proved for log utility with young endowments bounded
   below (`og_limit_rate_lt_one_log`). Fn. 11 ("equal to or above `g`") and the conclusion of
   §6.4.2 (p. 183, "non-negative") have the same boundary problem; the growing economy is not
   formalised.

4. **p. 181, the storage problem.** "Setting `qₜ = χ > 1/3` in (6.5)–(6.6)": the bond price `qₜ`
   is the price of one unit tomorrow, so storage with gross return `χ` is the bond problem at
   `qₜ = 1/χ` (`storage_saving`; the threshold `χ > 1/3` and the `χ = 1` allocation `(2, 2)` are
   those of `q = 1/χ`). Counterexample to the printed price: at `(3, 1)`, `χ = 2`, the printed
   `q = 2` gives `(5/2, 5/4)`, which is not on the storage budget line and has lower utility
   than the optimum `(7/4, 7/2)` (`storage_printed_counterexample`).

5. **p. 838, Appendix 6.A, the definition of `f`.** "Let us denote `F(k, ω_y + ω_o) + 1 − δ` by
   `f(k)`": it must be `F(k, ω_y + ω_o) + (1 − δ)k`, so that `c⋆ = f(k⋆) − k⋆` and
   `f′(k⋆) = 1 − δ + F₁ = R⋆` as in Theorem 6.2. With the printed `f` the criterion misclassifies:
   `F(k) = 2√k`, `δ = 1/2`, `k⋆ = 4` give `f′(4) = 1` for the correct `f` (efficient by Theorem .5)
   but `1/2 < 1` for the printed one (`appendix_6A_printed_f`).

6. **p. 839, the proof of Theorem .5(ii).** With `k₁ = k⋆ − ε₁`, the text defines
   `ε₂ = k₂ − k⋆ < 0` and writes `c_∞ = f(k⋆ − ε_∞) − (k⋆ − ε_∞)` with `ε_∞ ∈ [−k⋆, 0)`: the sign
   convention flips, and the step "the deficits grow without bound" is only sketched (a
   decreasing bounded sequence need not leave the feasible set). The proof here
   (`theorem_A5_efficient`) uses `εₜ = k⋆ − k′ₜ ≥ 0` throughout and shows the increments are at
   least `η = h(k⋆) − h(k⋆ − ε_{T+1}) > 0`, `h(k) = f(k) − k`, from strict concavity, so `εₜ`
   would exceed `k⋆`. It also handles alternative paths that first differ at any date, not only
   at date 0.

7. **p. 183, two steady states in the warm-glow model.** "There are two positive steady states"
   needs `c̄ < max_k [F(k, 1) − δk]` (and `F − δk < c̄` far out); the book does not state it
   (`warmglow_two_steady_states` with the hypotheses). For `c̄` above the maximum there is no
   steady state: `F = 2√k`, `δ = 1/2`, `c̄ = 3` (`warmglow_no_steady_state`).

## Departures

8. **Preferences.** Theorem 6.1 uses weak preference relations `Rᵢ` with the transitivity the
   proof needs; local nonsatiation is "within `ε` in every good". The OG and dynastic results use
   utility functions. In the OG economy the initial old's welfare is their consumption `c_{o,0}`
   (`log c` is strictly increasing).

9. **Infinite horizon (p. 162).** The dynastic First Welfare Theorem (`fwt_dynastic`) is stated
   for Chapter 5's date-0 problem (`ADOptimal`: positive consumption, convergent budget, plans with
   convergent utility series) with finitely many consumers, and requires the endowments to have
   finite value, the condition the book stresses.

10. **Theorem 6.2.** The book suppresses the assumptions; fn. 12 gives `Rₜ` bounded above and away
    from zero and `0 < a ≤ −f″ₜ ≤ M`. They are stated as quadratic bounds around the path:
    `fₜ(y) ≤ fₜ(kₜ) + Rₜ(y − kₜ) − (a/2)(y − kₜ)²` and
    `fₜ(y) ≥ fₜ(kₜ) + Rₜ(y − kₜ) − (M/2)(y − kₜ)²` for `0 ≤ y ≤ kₜ`, with `Rₜ` a supergradient of
    `fₜ` at `kₜ` (these follow from the second-derivative bounds by Taylor's theorem; global
    `−f″ ≥ a > 0` on `[0, ∞)` is incompatible with `f′ > 0`, so the bound is used only on
    `[0, kₜ]`). The efficiency half also needs the path bounded above, and the inefficiency half
    `kₜ ≥ k_low > 0` (to have room to reduce capital); neither is in the book. The theorem is
    about any feasible path, of which the Diamond equilibrium is one.

11. **Theorem .5(i)** needs only `f′(k⋆) < 1` (no concavity): the slope
    `(f(k⋆) − f(k⋆ − ε))/ε` is below one for small `ε` (`theorem_A5_inefficient`).

12. **Monopolistic competition.** The continuum of goods carries an arbitrary measure (`[0, 1]`
    with Lebesgue measure is an instance). The first-order condition (6.4) is the hypothesis of the
    price-index and demand results, as in the book's derivation; that `P` is the minimal cost of a
    unit of `C` (Hölder's inequality) is not formalised. Uniqueness of `C` in
    `A(1 − 1/ε) = Cv′(C/A)` is proved; existence is not claimed by the book.

13. **Consumption equivalents.** The dynamic `∆` is formalised for log utility, in closed form;
    the book's claim for general utilities is not formalised.

14. **The borrowing-constraint example.** The two agents are indexed `0, 1` (the book's agents 1
    and 2) with endowments `ω/2 − (ω/6)(−1)^{i+t}`. The no-borrowing optimum is taken among plans
    with convergent utility series; no transversality condition is needed.

# AKMM Chapter 24: Sovereign debt and default risk, in Lean

This is the `AKMM/SovereignDefault` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 24 (Sovereign debt and default risk, by J. C. Hatchondo and L. Martinez) of Marina
Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), pp. 729–748, with Appendix 24.A (pp. 897–908), cited by the draft's pages. Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 24 builds the Eaton–Gersovitz model of strategic sovereign default: a two-period model
with an explicit default rule, bond price and default-adjusted Euler equation, and the
infinite-horizon quantitative model with long-term debt, exclusion after default, Markov
perfect equilibrium and the computational methods of its appendix. The infinite-horizon model is
formalised on finite debt and income grids (the setting of Appendix 24.A.1). Imported results:
Sargent and Stachurski's recursive decision processes (`RecursiveDecisionProcesses`: Markov
matrices, Blackwell's conditions, contraction and global stability), and Obstfeld and Rogoff's
debt Laffer curve and scalar implicit-function helpers (`CapitalMarketImperfections`). Not
formalised: the data, facts, tables and figures, the calibration and simulations, the
computational methods other than extreme-value smoothing, the cited results, and existence and
uniqueness of the infinite-horizon Markov perfect equilibrium (beyond the text). Eight printed
errors are corrected and nine departures recorded in [corrections](docs/corrections.md); every
book item is located in the [source map](docs/source-map.md). The library contains
**117 theorems**, all new.

* **The two-period model** (§24.3): the default rule (24.4) with ties repaid and its optimality
  (`eq_24_3`, `eq_24_4`, `tp_defaultRule_optimal`); the price (24.5), whose printed middle term
  is the default probability (`eq_24_5`, `eq_24_5_printed_false`), zero profit
  (`tp_zero_profit`) and its properties (`tp_price_antitone`, `tp_price_strictAntiOn`,
  `tp_price_continuous`, `tp_price_tendsto_zero`, `tp_price_hasDerivAt`); footnote 8, contingent
  debt (`fn_8`); footnote 14, FOSD (`fn_14`).
* **Optimal borrowing** (§24.3): existence of an optimal `B₂` (`tp_exists_optimal`); the optimum
  is on the increasing side of the Laffer curve (`tp_laffer_side`); the Leibniz rule
  `d/dB₂ E u(Ĉ₂) = −E[u′(Ĉ₂)(1 − D̂₂)]` (`tp_hasDerivAt_expectedUtility`); the Euler
  equation (24.6) (`eq_24_6`).
* **Long-term debt** (§24.4.1, App. 24.A.2): (24.7) and `B_t` as a sufficient state
  (`eq_24_7`, `ltd_payments_sufficient`); (24.8) (`eq_24_8`); the risk-free value `δ/(δ + r)`,
  yield, Macaulay duration `(1 + i)/(δ + i)` and spread (`ltd_pv_bond`, `ltd_yield`,
  `ltd_duration`, `ltd_spread_pos_iff`); the haircut (24.2) (`eq_24_2`).
* **The bond price** (24.12), (24.A.2), (24.A.6): a contraction of modulus `(1 − δ)/(1 + r)`
  (`bp_contracting`), a unique price in `[0, δ/(δ + r)]` (`eq_24_12`, `eq_24_A_6`), convergent
  iteration (`eq_24_A_2`); with one-period debt the price ignores future borrowing
  (`bp_one_period_independent`), with long-term debt it does not
  (`bp_long_term_depends_on_borrowing`).
* **The Bellman equations** (24.9)–(24.11): the sovereign's problem as a Sargent–Stachurski RDP
  satisfying Blackwell's conditions (`SDModel.sd_isContracting`), a unique solution
  (`SDModel.eq_24_9_to_24_11`), convergent value iteration (`SDModel.eq_24_A_1`), values
  decreasing and default sets growing in debt (`SDModel.sd_VR_antitone`,
  `SDModel.sd_default_set_mono`).
* **Markov perfect equilibrium** (§24.4.3): the definition (`IsMPE`, `mpe_example`), as a fixed
  point (`mpe_iff_fixedPt`), equilibrium bounds and monotonicity (`mpe_price_mem`,
  `mpe_default_mono`); the borrowing condition (24.13), whose printed sign is wrong
  (`eq_24_13`, `eq_24_13_printed_false`); the total derivative (24.A.3) (`eq_24_A_3`).
* **Extreme-value smoothing** (App. 24.A.1, Method 3): logit choice probabilities derived from
  i.i.d. Gumbel shocks (`ev_logit_of_gumbel`, `ev_logit`), conditional borrowing probabilities
  (`ev_conditional_borrow`) and the price (24.A.6) with logit probabilities
  (`eq_24_A_6_logit`).
* **Calibration formulas** (App. 24.A.2–24.A.3): CRRA (`cal_crra_hasDerivAt`), the default cost
  (24.A.7) (`cal_phi_div_monotone`, `cal_phi_lam1`), the mean of log income, misprinted in Table
  24.A.1 (`cal_mean_one_iff`, `cal_table_mu_printed_false`), and footnote 44's iso-moment slope
  by the implicit function theorem (`fn_44`, `fn_44_exists`).

All names are in the namespace `AKMM.SovereignDefault`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [TwoPeriod](AKMMSovereignDefault/TwoPeriod.lean) | 29 | Two-period default rule (24.3)–(24.4), price (24.5), footnotes 8 and 14 |
| [TwoPeriodOptimum](AKMMSovereignDefault/TwoPeriodOptimum.lean) | 7 | Existence of optimal borrowing, the Laffer side, Leibniz rule, (24.6) |
| [LongTermDebt](AKMMSovereignDefault/LongTermDebt.lean) | 13 | (24.7)–(24.8), sufficiency of `B_t`, present value, yield, duration, spread, haircut (24.2) |
| [BondPrice](AKMMSovereignDefault/BondPrice.lean) | 12 | The price recursion (24.12), (24.A.2), (24.A.6) as a contraction; one-period vs long-term debt |
| [Bellman](AKMMSovereignDefault/Bellman.lean) | 10 | (24.9)–(24.11) as an RDP, uniqueness, (24.A.1), monotonicity and default sets |
| [MarkovPerfect](AKMMSovereignDefault/MarkovPerfect.lean) | 12 | Markov perfect equilibrium, fixed-point form, (24.13) corrected, (24.A.3) |
| [ExtremeValue](AKMMSovereignDefault/ExtremeValue.lean) | 10 | Gumbel integrals, logit choice probabilities, (24.A.6) with logit probabilities |
| [GumbelProduct](AKMMSovereignDefault/GumbelProduct.lean) | 9 | The Gumbel law; logit from the product of i.i.d. Gumbel laws |
| [Calibration](AKMMSovereignDefault/Calibration.lean) | 15 | CRRA, (24.A.7), the mean of log income (Table 24.A.1 corrected), footnote 44 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.

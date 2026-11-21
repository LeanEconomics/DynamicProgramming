# Corrections and departures: AKMM Chapter 19

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 19, Credit market frictions (Vincenzo Quadrini), pp. 561–591, and
Appendix 19.A, pp. 877–878. Lean names are relative to `AKMM.CreditFrictions`. Every book item
is located in the [source map](source-map.md).

## Corrections

1. **p. 584, (19.17), the working-capital limit.** Printed `wℓ + b′/R ≤ ξpk′`, with the
   household rate `R`, followed by "The optimality conditions for capital and intertemporal
   borrowing are (19.5) and (19.6), which are the same as before". Assumption 19.4.2, (19.3) and
   (19.12) use `b′/R̃`. With `b′/R̃` (19.6) is indeed unchanged (`sys_wc_19_6_tilde`); with the
   printed `b′/R` the bond condition becomes `E[m′ϕ′(d)/ϕ′(d′)]R̃ = 1 − µ/(1 + τ)`
   (`sys_wc_19_6_printed`), which differs from (19.6) whenever `µ ≠ 0` and `τ ≠ 0`
   (`sys_wc_19_6_printed_ne`). (19.5) and (19.18) hold either way (`sys_wc_19_5`, `eq_19_18`).
   The limit should read `wℓ + b′/R̃ ≤ ξpk′`. PDF page rendered.

2. **p. 586, the equation number of the household's bond condition.** "while the first-order
   condition for the households' bonds' choice, equation (19.6), is `1/R = E[βu₁′/u₁]`": the
   household's condition is (19.9); (19.6) is the firm's (`eq_19_22` from `eq_19_9`).

3. **p. 582, Property 19.5.3's argument.** "Keeping `ξ` unchanged, the decline in the left-hand
   side induced by the lower value of `µ`": the text has just argued that `µ` rises, and
   `(1 − µξ)p` falls only when `µ` rises; read "higher value of `µ`". The property itself is
   proved without this heuristic (`property_19_5_3`).

4. **p. 590, the simulation of the credit boom.** "The draw of productivity, instead, remains at
   its mean value `ξ = 0.185`": the productivity draw is `z = 0.185` (Table 19.1; `ξ`'s mean is
   0.500). No theorem (simulation description).

5. **p. 581, figure reference.** "Figure 19.2 showed that bank credit standards are very
   cyclical": credit standards are in Figure 19.1, panel B (Figure 19.2 shows spreads and new
   debt). No theorem.

6. **p. 587, "Proposition 19.4.2".** "even if there is a borrowing limit as assumed in
   Proposition 19.4.2": it is Assumption 19.4.2. No theorem.

7. **p. 877, the envelope conditions of Appendix 19.A.** "we differentiate the value function
   with respect to `k′` and `b′`" (19.A.1) and "with respect to `b′` and `a′`" (19.A.2): the
   envelope conditions `Ω_k(S; k, b)`, `Ω_b(S; k, b)`, `V_b(S; a, b)`, `V_a(S; a, b)` are
   derivatives in the current state `(k, b)`, `(a, b)`, which is what `env_firm`,
   `appendix_19_A_1_envelope` and `hh_envelope` prove (under concavity of the value function,
   via the Benveniste–Scheinkman lemma). PDF page rendered.

8. **p. 580, the hypothesis of Property 19.5.2.** "If the borrowing constraint is binding and the
   firm starts with positive debt `B > 0`, a positive price change … has a positive impact on
   capital accumulation." `B > 0` is exactly the condition for net worth `pK − B` to have
   elasticity above one in `p` (`property_19_5_2_networth`), but the response of the rearranged
   `K′` to `p` (holding `D` fixed, as the text does) is `−N/(p²(1 − ξ))`,
   `N = αF − B − D − κ(D − φ)²`, positive iff `N < 0` (`sys_hasDerivAt_Kprime`,
   `property_19_5_2`); the text's "Typically, this term is negative" is the needed hypothesis.
   `B > 0` does not imply it: `αF = 2`, `B = 1`, `D = κ = 0` gives `N = 1 > 0`
   (`sys_B_pos_not_sufficient`).

9. **p. 586, "when, in expectation, the term `u₁(C′, L′)/u₁(C, L)` is higher".** With `R`
   determined by (19.22), scaling the discount factor `m′` by any `c > 0` leaves (19.21)–(19.22)
   satisfied with the same `µ` (`gm_mu_scale`); without uncertainty
   `µ = 1 − ϕ′(D)/((1 + τ)ϕ′(D′))` whatever `u₁′/u₁` is (`gm_mu_det`). The precise condition is on
   the `m′`-weighted mean of `ϕ′(D)/ϕ′(D′)`: `µ > 0` iff `E[m′ϕ′(D)/ϕ′(D′)] < (1 + τ)E[m′]`
   (`gm_mu_pos_iff`, `gm_not_binding`), which also makes "sufficiently larger than 1" precise
   (the threshold is `1 + τ`).

## Hypotheses added to the book's claims

10. **p. 577, monotonicity of labour and output.** The text does not sign `α + ν − 1`. Labour
    and output increase in `z` and `K` when `α + ν > 1` (`tp_L_strictMono_z`,
    `tp_L_strictMono_K`, `tp_Y_strictMono_z`, `tp_Y_strictMono_K`); for `α + ν < 1` labour
    strictly decreases in `z` (`tp_L_strictAnti_z_of_neg`). `F_k` decreasing in `K` needs
    `ν > 1` (`tp_Fk_strictAnti_K`).

11. **p. 577, `g` increasing "at least in the relevant range".** `L′^ν = (1 − α)Y′/ν`, so
    `g = (1 − δ)K′ + ((α + ν − 1)/ν)Y′` (`tp_L_pow_nu`, `tp_g_eq`), increasing in `z′` and `K′`
    on the whole positive orthant when `α + ν > 1` and `δ ≤ 1` (`tp_g_strictMono_z`,
    `tp_g_strictMono_K`).

12. **Properties 19.5.1, 19.5.3, 19.5.5 (pp. 579–583) are heuristic in the book** ("keeping other
    things unchanged"). They are proved as comparative statics of the firm's conditions (19.11),
    (19.15) and the budget (19.12)–(19.13) at given prices `R` and `Λ = β(C − L^ν)/g`, with every
    sign condition explicit:
    * Property 19.5.3 (`property_19_5_3`): binding at the initial `ξ₀` (`µ₀ > 0`), `ξ₁ < ξ₀ ≤ 1`,
      `κ ≥ 0`, `ϕ′(D) > 0`, `F_k` strictly decreasing. In general equilibrium with `κ = 0` and
      `τ > 0` (`property_19_5_3_ge`), with `g` increasing, `F_k` decreasing,
      `1 − δ + F_k > 0` and `C − L^ν = W − pK′ > 0`.
    * Property 19.5.1 (`property_19_5_1`, `property_19_5_1_slack`): `z′` rises, current profits
      `αF` do not fall, `ξ ≤ 1`; "smaller if the borrowing constraint is binding" is proved for
      proportional responses of `K′` with the closed-form `F_k` (`ν > 1`), under the book's own
      step that dividends fall (`property_19_5_1_dampening`; automatic when only `z′` changes,
      `cs_div_falls`), with `κ > 0`, `ξ < 1`. The comparison is with the same economy when the
      limit is slack.
    * Property 19.5.5 (`property_19_5_5`): "sufficiently large" is made precise as
      `ξ₁pK₀′ < B₀′/R̃` (the old plan violates the new limit); with `κ > 0` and `ξ₁ < 1`, the
      new Kuhn–Tucker solution has a binding limit and lower `K′`.

13. **Property 19.5.4 (p. 582)** is proved for the equilibrium conditions (with `µ = 0`, the
    system does not involve `ξ`, `property_19_5_4`) and, for the optimisation problem, under
    concavity of the objective (`property_19_5_4_opt`).

14. **Appendix 19.A, the first-order conditions.** The book states the Lagrangian conditions.
    They are derived here from optimality along feasible directions (`kkt_firm`,
    `appendix_19_A_2_focs`), assuming differentiability of the continuation values and
    `ϕ′(d) > 0`; the envelope conditions assume concavity of the value function (the
    Benveniste–Scheinkman hypotheses).

## Departures

15. **Proposition 19.1 (p. 586)** is proved in the deterministic model, by comparing the
    equilibrium first-order and market-clearing conditions with Miao's neoclassical growth model,
    as the book's proof does (`proposition_19_1`, `proposition_19_1_planner`); transversality
    conditions are not compared. "Debt is indeterminate" is proved as: every debt path with the
    same initial debt, with dividends from the firm's budget, gives an equilibrium with the same
    allocation (`proposition_19_1_debt`), and lower debt paths satisfying the limit exist
    (`proposition_19_1_indeterminate`).

16. **Footnote 6 (p. 572)** compares the loan `b′/R̃` with the recovery `ξpk′`, as the book does;
    the timing of repayment is not modelled. The repayment rule is the Obstfeld–Rogoff one
    (`fn6_repayment_eq`).

17. **Expectations** are finite sums over next-period states with probabilities `πₛ`.

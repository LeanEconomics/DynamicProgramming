# AKMM Chapter 19: Credit market frictions, in Lean

This is the `AKMM/CreditFrictions` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 19 (Credit market frictions, by Vincenzo Quadrini) of Marina Azzimonti, Per Krusell,
Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025), pp. 561–591,
with Appendix 19.A (pp. 877–878), cited by the draft's pages. Run the commands below from this
directory. [Return to the library index](../../README.md).

Chapter 19 adds financial frictions to the neoclassical growth model: firms accumulate capital
and finance it with debt and equity, debt is cheaper (a tax subsidy `R̃ = R/(1 + τ)`), borrowing
is limited by collateral (`b′/R̃ ≤ ξpk′`) and dividends are costly to adjust
(`ϕ(d) = d + κ(d − φ)²`). Every derivation of the text is proved in the book's setting: the
Modigliani–Miller principle (19.1)–(19.2) and its converse; the collateral limit from limited
enforcement (footnote 6); the firm's and the household's first-order conditions (19.4)–(19.10),
derived from optimality, with the envelope conditions of Appendix 19.A from the
Benveniste–Scheinkman lemma; the closed forms of the two-period model and the system
(19.11)–(19.16); Properties 19.5.1–19.5.6 as signed comparative statics with explicit hypotheses
(the book's arguments are heuristic); working capital (19.17)–(19.18); (19.19)–(19.22); and
Proposition 19.1, with the allocation satisfying the neoclassical growth model's conditions as
formalised in Miao Chapter 14 and debt indeterminate. Not formalised: history, data, figures,
the calibration and the simulations of §19.7. Nine printed errors are corrected, among them the
interest rate in the working-capital limit (19.17) (`b′/R̃`, not `b′/R`, or (19.6) changes), the
hypothesis of Property 19.5.2 (`B > 0` does not sign the response of `K′` to `p`) and the role
of `u₁′/u₁` in whether the limit binds, as recorded in [corrections](docs/corrections.md); every
book item is located in the [source map](docs/source-map.md). The library contains
**115 theorems**.

* **Modigliani–Miller and the collateral limit** (§19.3.1, §19.4): `mm_obj_diff`, `eq_19_2`,
  `mm_isMax_iff`, `mm_indeterminate`, `mm_no_max`; footnote 6 via Obstfeld–Rogoff's repayment
  rule (`fn6_repayment_eq`, `fn6_full_iff`, `fn6_lender_iff`, `assumption_19_4_2_of_fn6`); the
  box on p. 587 (`mm_box_gain`, `mm_box_gain_zero_iff`, `gm_box`).
* **The dividend cost** (Assumption 19.4.3): `cfPhi`, `cfDiv` and its derivative `1/ϕ′`
  (`div_phi_div`, `div_div_phi`, `div_le_div_of_phi`, `div_hasDerivAt_div`).
* **Firms** (§19.4.1, App. 19.A.1): envelope conditions (`env_firm`,
  `appendix_19_A_1_envelope`), Kuhn–Tucker conditions from optimality (`kkt_dir`, `kkt_firm`),
  (19.4)–(19.6) (`eq_19_5`, `eq_19_6`, `firm_focs`).
* **Households** (§19.4.2, App. 19.A.2): `hh_envelope`, `hh_dir`, `appendix_19_A_2_focs`,
  (19.8)–(19.10) (`eq_19_8`, `eq_19_9`, `eq_19_10`, `household_focs`), the tax and the resource
  constraint (`hh_tax`, `hh_R_gt_Rt_iff`, `hh_resource`).
* **The two-period model** (§19.5): closed forms of `L′`, `Y′`, `F_k`, `g` and their
  monotonicity (`tp_foc_iff`, `tp_labour`, `tp_Y_eq`, `tp_Fk_eq`, `tp_g_eq`,
  `tp_g_strictMono_K`, …); (19.11)–(19.16) (`system_19_11_to_19_16`).
* **Properties 19.5.1–19.5.6**: `property_19_5_1`, `property_19_5_1_slack`,
  `property_19_5_1_dampening`, `property_19_5_2_networth`, `property_19_5_2`,
  `property_19_5_3`, `property_19_5_3_ge`, `property_19_5_4`, `property_19_5_4_opt`,
  `property_19_5_5`, `property_19_5_6`; working capital (`eq_19_18`, `tp_wc_labour`,
  `sys_wc_19_6_tilde`, `sys_wc_19_6_printed`).
* **The general model** (§19.6): `eq_19_19`–`eq_19_22`, `gm_kappa_zero`, `gm_binding_iff`,
  `gm_mu_pos_iff`, `gm_not_binding`, `gm_mu_scale`; Proposition 19.1 (`proposition_19_1`,
  `proposition_19_1_planner`, `proposition_19_1_debt`, `proposition_19_1_indeterminate`).

All names are in the namespace `AKMM.CreditFrictions`. The project imports
[EconomicDynamics/InfiniteHorizonDP](../../EconomicDynamics/InfiniteHorizonDP/README.md)
(the Benveniste–Scheinkman lemma `Miao.InfiniteHorizonDP.theorem_4_10`),
[EconomicDynamics/NeoclassicalGrowth](../../EconomicDynamics/NeoclassicalGrowth/README.md)
(Miao Chapter 14: `RMHHFOC`, `RMFirmFOC`, `RMClear`, `RMPlannerFOC`, `rm_ce_planner`) and
InternationalEconomics/CapitalMarketImperfections (Obstfeld–Rogoff:
`DebtCeiling.repayment`, `repayment_eq_full_iff`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [MM](AKMMCreditFrictions/MM.lean) | 11 | (19.1)–(19.2), footnote 6, the box (AKMM §19.3.1, p. 572, p. 587) |
| [Dividend](AKMMCreditFrictions/Dividend.lean) | 12 | `ϕ(d) = d + κ(d − φ)²` and the payable dividend (AKMM Assumption 19.4.3, pp. 573–574) |
| [Firm](AKMMCreditFrictions/Firm.lean) | 9 | Envelope and Kuhn–Tucker conditions, (19.4)–(19.6) (AKMM §19.4.1, App. 19.A.1, pp. 574–575, 877) |
| [Household](AKMMCreditFrictions/Household.lean) | 10 | (19.7)–(19.10), taxes, resource constraint (AKMM §19.4.2, App. 19.A.2, pp. 576, 877–878) |
| [TwoPeriod](AKMMCreditFrictions/TwoPeriod.lean) | 29 | Closed forms of the two-period model, Property 19.5.6 (AKMM §19.5, pp. 576–578, 584–585) |
| [System](AKMMCreditFrictions/System.lean) | 17 | (19.11)–(19.16), Properties 19.5.2 and 19.5.4, (19.17)–(19.18) (AKMM pp. 577–584) |
| [Statics](AKMMCreditFrictions/Statics.lean) | 12 | Properties 19.5.1, 19.5.3, 19.5.5 (AKMM §19.5.1–19.5.4, pp. 579–583) |
| [General](AKMMCreditFrictions/General.lean) | 15 | (19.19)–(19.22), Proposition 19.1, the box (AKMM §19.6, pp. 585–587) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.

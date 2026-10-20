# Corrections and conventions

Places where a Lean statement differs from the book or the solutions manual (Irigoyen,
Rossi-Hansberg and Wright): a claim corrected, a hypothesis made explicit, a gap in a proof closed,
or a convention chosen. Every false claim below is refuted in Lean, by a counterexample or a proof
of inconsistency. Misprints that change no statement are listed under Conventions and are not
formalised. The last section lists what is not proved.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Assumptions 17.1 and 17.2, pp. 503, 513 | `V` is `C²` on `ℝ₊`, and `1 − β ≤ −yV″(y)/V′(y) ≤ 1 + β` for all `y ∈ ℝ₊`, some `β ∈ [0, 1)`. | Inconsistent. At `y = 0` the middle term is `0 < 1 − β`, so Assumption 17.2 never holds (`assumption17_2_counterexample`, `not_monoAssumption17_2`), and Propositions 2 and 6 are vacuous as stated. Restricting (5) to `y > 0` does not help: the lower bound forces `V′(y) ≥ V′(1) y^{−(1−β)} → ∞` as `y ↓ 0`, while Assumption 17.1 bounds `V′` by `V′(0)` (`assumption17_2R_inconsistent`). Repair: `V` continuous on `ℝ₊` and `C²` on `(0, ∞)` (`Assumption17_1VR`), with (5) for `y > 0` (`Assumption17_2R`). The book's Assumption 17.1 implies the repaired one (`shocks_assumption17_1VR_of_V`); `V(y) = y^{1−σ}/(1 − σ)`, `0 < σ < 1`, satisfies both repaired assumptions (`crra_assumption17_1VR`, `crra_assumption17_2R`, `repaired_assumptions_nonvacuous`). Proposition 1 (`proposition_1_repaired`), Proposition 2 (`proposition_2`) and Proposition 6 (`proposition_6`, `proposition_6_islands`) are proved under the repair. |
| Exercises 17.2(a) and 17.4(a), pp. 509, 511 | With `D` convex, `G` continuous and `π` Feller, `T` maps `F` into `F` (and `T̂` maps `F̂` into `F̂`). The manual adds "because `X` is bounded". | False: `Tf` need not be bounded. `X = D = ℝ`, `G = x`, `π(x, ·) = δ_x` gives `Tf(x) = x` (`ex_17_2a_counterexample`); `X = (0, 1]`, `G = 1/x` gives `Tf(x) = 1/x` (`ex_17_2a_counterexample_bounded`); `X = ℝ`, `D = [1, ∞)`, `G = e^{\|x\|}` gives `T̂0(x) = \|x\|` (`ex_17_4a_counterexample`). Corrected for compact `X`, as in all the book's applications (`ex_17_2a`, `ex_17_4a`). |
| Exercise 17.5(a), p. 520 | If `f` is continuous, `x′ = f(x)`, `x(0) = c` has a solution on `[0, 1]`. | False: for `f(x) = x²`, `c = 2` there is no solution on `[0, 1]`, even with one-sided derivatives at the end points (`ex_17_5a_counterexample`, `ex_17_5a_false`); the local solution `2/(1 − 2t)` blows up at `t = 1/2` (`ex_17_5a_blowup_solution`). Corrected: a solution on some `[0, t₀]`, `t₀ ∈ (0, 1]` (`ex_17_5a_local`, the manual's result), and on all of `[0, 1]` when `f` is also bounded (`ex_17_5a_of_bounded`). |
| Proposition 5, p. 530 | `T` on `C(X)` has at least one fixed point; if the iterates from `ε_K` and from `B` have the same limit, it is "the unique fixed point of `T`". | `T` is not defined on all of `C(X)`, since `ζ⁻¹` is defined only on `ℝ₊`. `T0 = 0` (`monoOLGOp_zero`), so existence is trivial and, whenever the two limits agree, the zero function is a second fixed point (`proposition_5_literal_false`). The claim is false, not vacuous: an economy with `H(l) = −l − log(1 − l)`, `V(y) = log(1 + y)` and one state satisfies every hypothesis and the two limits agree (`proposition_5_counterexample`). The proof gives uniqueness in `F` (`proposition_5`). Corrected: if the limits agree, the limit is the unique fixed point `h` with `inf h > 0` (`monoOLG_fixedPoint_mem`, `proposition_5_corrected`, `proposition_5_corrected'`). |
| Proposition 6, p. 535 | `T` of (4) has a unique fixed point in `C(Z)`. | `T0 = 0` (`shocksOpT_zero`, `proposition_6_zero_fixedPoint`), so `T` has two fixed points in `C(Z)` (`proposition_6_counterexample`); `T` is also not defined on functions with negative values. Corrected: exactly one strictly positive continuous fixed point (`proposition_6`, `proposition_6_islands`), under the repaired assumptions. |
| Exercise 17.7, p. 525, and Proposition 7, p. 536 | The labour operator `n ↦ ζ⁻¹[∫ φ(x′ n(x′)) π(x, dx′)]` has a fixed point; `T` of (4) has a fixed point in `C(Z)`. | Trivial as stated: `n ≡ 0` and `f ≡ 0` are fixed points (`ex_17_7_zero`, `proposition_6_zero_fixedPoint`). The manual's Schauder set `D ⊆ [0, L)` contains `0` and does not exclude it. Corrected: a continuous fixed point bounded away from zero (`ex_17_7`, `proposition_7`, `proposition_7_islands`). |
| Exercise 17.12, p. 536 | Under Assumptions 17.5–17.6, `G(·\|z)` is the uniform distribution on `[a(z), b(z)]`. | False: its density is `2θ/(b(z)² − a(z)²)` on `[a(z), b(z)]` (`ex_17_12`), proportional to `θ`, the Jacobian of `x = zθ` (the book's own `π(z)` contains it). With `x ~ U[1, 2]`, `θ ~ U[1, 3/2]` and `h = θ·1{z ∈ [1, 4/3]}`, the uniform family gives `25/48` instead of `19/36` (`ex_17_12_counterexample`). The manual's proof treats `x` as uniform on the null set `{x = zθ}`, a Borel–Kolmogorov-type error. The support `[a(z), b(z)]` in (5) is correct. So (6a), (7) and `J` in Proposition 8 need the weights `2θ/(b² − a²)`: (6a) is `shocksUnif_integral_condLaw`, (7) is `eq7_corrected`. Proposition 7 (`proposition_7`) and Exercise 17.14(d) (`ex_17_14d`) hold with these weights. |
| Exercise 17.8(a), p. 534 | For each `z ∈ int Z`, `G(·\|z)` has a continuous density. The manual's density is `g(θ)ψ(θz)/π(z)`. | (i) The manual's density omits the factor `θ` and does not integrate to `1` (`4/5` in the example at `z = 1`, `ex_17_8a_manual_counterexample`); the conditional density is `g(θ) θ ψ(zθ)/π(z)` (`shocksCondDens`, `ShocksAssumption17_5.ex_17_8a_disintegration`). (ii) The density need not be continuous on `Θ` when `ψ` and `g` are continuous only on `X` and `Θ`, as with the uniform densities of Assumption 17.6: at `z = 4/5` it jumps from `0` to `40/11` at `θ = a(z) = 5/4 ∈ int Θ`, and no function continuous on `Θ` agrees with it almost everywhere (`ex_17_8a_continuity_counterexample`). It is continuous on `[a(z), b(z)]` (`ShocksAssumption17_5.ex_17_8a`). (iii) It needs `π(z) > 0`; see below. |
| Exercise 17.14(a), p. 540 | `ρ` is strictly increasing if and only if `zη′(z)/η(z) < 1`. | The "only if" is false: `ρ(z) = 1 + (z − 1)³` is strictly increasing on `[1/2, 3/2]` and `zη′/η = 1` at `z = 1` (`ex_17_14a_counterexample`). True: `ρ′ = (1/η)(1 − zη′/η)` (`ex_17_14a_deriv`), and `zη′/η < 1` on an interval implies `ρ` strictly increasing there (`ex_17_14a`). |
| (6), p. 505; manual for Exercise 17.14(b) | `l ζ′(l)/ζ(l) ≥ 1` "with equality only at `l = 0`"; the manual's (b) uses `ηζ′(η)/ζ(η) > 1`. | Strict convexity allows `H″(l₀) = 0` at `l₀ > 0`, where the elasticity is exactly `1`: `olgExH` satisfies Assumption 17.1 (`olgExH_assumption`) and has elasticity `1` at `l = 1` (`proposition_1_elasticity_counterexample`). True: elasticity `≥ 1` on `(0, L)` (`zeta_elasticity_ge_one`), which suffices for Exercise 17.14(b) as stated (`ex_17_14b`). At `l = 0` the ratio is `0/0`. |
| Proof of Proposition 1, step 4, p. 506 | Two cases: `φ(0) > 0` (top panel of Figure 17.1) and `φ(0) = 0`. | Under Assumption 17.1, `φ(0) = 0 · V′(0) = 0`, so the first case cannot occur (`proposition_1_phi_zero_counterexample`). The second case is `exists_unique_foc`. |
| pp. 515 and 530 | Strict monotonicity and strict concavity of `V` imply `0 < −yV″(y)/V′(y)` for all `y ∈ ℝ₊`. | False: the ratio is `0` at `y = 0` for every `V` (`monoRRA_zero`, `monoRRA_not_forall_pos`, `rra_pos_counterexample`, `monoRRA_pos_counterexample`), and `V(y) = 3 − e^{−y}(y² + 2y + 3)` satisfies Assumption 17.1 with `V″(1) = 0` (`monoCexW_assumption17_1V`, `monoRRA_interior_zero_counterexample`). True: the ratio is `≥ 0` on `ℝ₊` (`MonoAssumption17_1V.rra_nonneg`) and `> 0` somewhere in every open interval (`MonoAssumption17_1V.exists_rra_pos`). |
| p. 541 | Assumption 17.2 is "a very mild strengthening" of Assumption 17.4. | As stated, 17.2 implies 17.4 only vacuously (`monoAssumption17_2_imp_17_4`), and 17.4 does not imply 17.2 (`assumption17_4_not_imp_17_2_counterexample`). In the repaired forms on `ℝ₊₊` (`MonoAssumption17_2Pos`, `MonoAssumption17_4Pos`) neither implies the other: `V(y) = 2 arctan √y` has relative risk aversion `(1 + 3y)/(2(1 + y)) ∈ [1/2, 3/2)`, so it satisfies 17.2 with `β = 1/2` and violates 17.4 (`monoArcV_repaired_utility`, `assumption17_2Pos_not_imp_17_4Pos_counterexample`), and `V(y) = log(1 + y)` satisfies 17.4 but not 17.2 (`assumption17_4Pos_not_imp_17_2Pos_counterexample`). True: 17.4 with a uniform lower bound `ε ≤ −yV″/V′` implies 17.2 with `β = 1 − ε` (`monoAssumption17_2Pos_of_17_4Pos`). |
| p. 533 | Equal prices imply equal ratios `x/θ`, so any equilibrium has the form `p(x, θ) = ρ(x/θ)`, `n(x, θ) = η(x/θ)`. | The argument proves only that `x/θ` is a function of the price (`p533_ratio_of_price`). For a continuous equilibrium price it does follow, for any beliefs indexed by the price (`islands_eqm_price_of_ratio`, from the uniqueness of the optimum `islands_obj_max_unique` and the intermediate value theorem on nearby rays); `ρ` is then automatically invertible. Without continuity the argument fails: on `[1, 2] × [1, 3/2]`, `p(x, θ) = x/θ + 10·1{θ > 5/4}` and `n = (x/θ)/p` satisfy every premise used (`n` a function of `p`, and (2)), and `p` is not a function of `x/θ` (`p533_counterexample`). The existence results that follow concern equilibria of the form `ρ(x/θ)` only. |
| Exercise 17.5(b) (manual) | The second solution of `x′ = √x`, `x(0) = 0` is `x(t) = t²/2`. | `t²/2` is not a solution (`ex_17_5b_manual_counterexample`). The solutions include `0` and `t²/4` (`ex_17_5b`), and `((t − s)⁺)²/4` for every `s ∈ [0, 1]` (`ex_17_5b_family`). |
| Proposition 8, p. 540 | Under Assumptions 17.1, 17.4 and 17.5, the price function `ρ` is strictly increasing. | False (*Lean*: `proposition_8_false`, `proposition_8_counterexample_book`). With `x ~ U[1, 2]`, a bimodal `g` on `Θ = [1, 3/2]`, `H′ = l/(1 − l)` and CRRA utility (`V = A y^{1−σ}/(1 − σ)`, `σ = 1/20`, modified below a small `y₀` to have the book's finite `V′(0)`), `T` has exactly one strictly positive continuous fixed point, and its `ρ` has `ρ(10/7) < ρ(4/3)` and `ρ(1) < ρ(4/3)`, so it is not invertible. As `z` passes `x̄/θ = 10/7`, `G(·\|z)` loses the upper bump of `g`. Since continuous equilibria correspond exactly to such fixed points with invertible `ρ` (`islands_fixedPoint_of_eqm`, `islands_eqm_of_fixedPoint`), the economy has no equilibrium with a continuous price function (`proposition_8_eqm_counterexample`, `shocksP8W_no_continuous_eqm`). The book's proof step (d) fails for the same `g` (`proposition_8_general_counterexample`). The corrected `proposition_8` adds Assumption 17.6 and uses the correct weights. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| p. 504 | A strictly positive measurable `n` satisfying (3) gives an equilibrium with `p = M/(x n)`. | `n` must take values in `(0, L)`: `H′(n)` is defined only there, and `n < L` gives `p ≥ M/(bL) > 0`, which Exercise 17.1 needs (`isStationaryEqm_of_eq3`). |
| Exercise 17.1, p. 504 | `p` measurable and bounded away from zero. | As in the book; no upper bound on `p` is needed (`ex_17_1`). Differentiation under the integral is justified by the bound on `V′` (`hasDerivAt_utility`). |
| Lemmas 17.1 and 17.2, pp. 509, 511 | `G(x, x′, ·)` continuously differentiable on `D`. | Only differentiability within `D` is used; continuity of `G₃` is not (`lemma_17_1`, `lemma_17_2`). The corrected Exercises 17.2(a) and 17.4(a) supply compactness of `X`. |
| Proposition 2, p. 513 | Assumptions 17.1 and 17.2. | The repaired assumptions (see above). `π` is Feller (`IsFellerKernel`), as the book assumes; p. 525 says Proposition 2 "did not require any restrictions on `π`", which should read "none beyond the Feller property". |
| Exercise 17.6, p. 522 | The hypotheses of Lemma 17.5, and `G` uniformly continuous in its third argument. | Assumption 17.3 is not needed, only that each `π(x, ·)` is a probability measure; uniform continuity in the third argument is uniform over `(x, x′)`, as the manual reads it (`ex_17_6`, `kernelIntegral_dist_le`). |
| Lemma 17.5, p. 521 | `D` nonempty, closed, bounded and convex; `G` continuous and uniformly continuous in its first argument. | Only boundedness of `D` is used, and joint continuity of `G` only to make `x′ ↦ G[x, x′, f(x′)]` measurable (`lemma_17_5`). The §17.5 copy assumes `G` bounded (`kernelIntegral_uniformEquicontinuous`). |
| Theorem 17.4, Lemma 17.6, Theorem 17.7, pp. 520–528 | `X` a bounded subset of `ℝˡ`. | The proofs use only that `X` is totally bounded. `theorem_17_4` is stated for bounded `X ⊆ ℝˡ`, which need not be closed; `lemma_17_6` and `theorem_17_7` for any pseudometric space with `TotallyBounded univ`, and `theorem_17_7_of_isBounded` for a bounded subset of a proper space (`totallyBounded_univ_of_isBounded`). No convexity is used in Theorem 17.7. |
| Exercise 17.8, p. 534 | `G(·\|z)` has a density for `z ∈ int Z`; `G(·\|z_n) → G(·\|z)` weakly. | The density needs `π(z) > 0`, which Assumption 17.5 does not give at interior points: `π(3/4) = 0` with `Z = [2/3, 2]` (`ex_17_8a_pi_zero_counterexample`). `ψ > 0` on `X` and `g > 0` on `Θ` suffice (`ShocksAssumption17_5.pi_pos`). Part (b) assumes `π > 0` on `int Z` and the endpoint convention `G(·\|z̲) = δ_{θ̄}`, `G(·\|z̄) = δ_{θ̲}`, the only possible weak limits (`shocksCondLaw`, `ShocksAssumption17_5.ex_17_8b`). |
| Proposition 6, p. 535 | Continuity of `Tf` "as before". | It is the weak continuity of `G(·\|z)`, Exercise 17.8(b), including at the end points of `Z` (`ShocksBounds.opT_mem`). `proposition_6_islands` therefore assumes `ψ > 0` on `X` and `g > 0` on `Θ`. |
| Exercise 17.14(a), p. 540 | `ρ′` and `η′` are used. | Differentiability of `η` is a hypothesis (`ex_17_14a_deriv`, `ex_17_14a`); the book does not show it. `proposition_8` needs no derivatives. |

## Gaps in proofs closed

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 17.3, p. 517 | Brouwer's theorem is stated without proof (references in §17.7). | Proved, without Mathlib support. Rogers's lemma: there is no C¹ map `g` on a neighbourhood of the closed unit ball `B` with `‖g‖ = 1` on `B` and `g x = x` on the sphere (`no_C1_retraction`). For `f_t = id + t(g − id)` and small `t > 0`, `f_t` maps the open ball injectively onto itself, so `V(t) = ∫ det Df_t = vol(B°)` by the change of variables formula; `V` is a polynomial in `t` (`exists_polynomial_det_id_add_smul`, `integral_eq_of_polynomial_of_eq_on_Ioc`), so `V(1) = vol(B°) > 0`, but `Dg` is singular on `B°`, so `V(1) = 0`. A fixed-point-free continuous self-map of the ball is approximated by C¹ maps (Stone–Weierstrass, `exists_C1_approx_real`, `exists_C1_approx`) and turned into such a retraction (`brouwer_closedBall`). The general case follows by a nearest-point retraction and rescaling (`exists_lipschitz_retraction`, `brouwer_inner`) and transport to Euclidean space (`brouwer`); `theorem_17_3` is the book's form. |
| Theorem 17.4, p. 520 | Schauder's theorem is stated without proof. | Proved from `brouwer`. A continuous self-map of a compact convex set has `ε`-fixed points, through a Schauder projection onto the convex hull of a finite `ε`-net (`exists_approx_fixed_point`), hence a fixed point (`schauder`); a map of a closed convex set with relatively compact image has one by Mazur's theorem (`schauder_closed`). A bounded equicontinuous family on a totally bounded `X` is totally bounded in `X →ᵇ ℝ` (`totallyBounded_of_equicontinuous`, one half of Arzelà–Ascoli, proved directly since `X` need not be compact), which gives `theorem_17_4`. The statement is correct as given. |
| Proof of Proposition 1, step 5, pp. 506–507 | By (6) and (7), `ζ` crosses `E φ(x′ l)` from below at every intersection, so they meet once. | The strict inequalities fail where `H″ = 0` and `V″ = 0` (see above), so the pointwise argument breaks at such points. The log-ratio `log ζ(l) − log ∫ φ(x′ l) dμ = log H′(l) − log ∫ x′ V′(x′ l) dμ` is strictly increasing on `(0, L)` (`proposition_1_logRatio_strictMonoOn`), which gives uniqueness (`proposition_1`). |
| Proof of Proposition 2, step 6, p. 515 | "Since any `K > 1/C` could have been used", the solution is unique. | Needs `ε_k → 0`, which the book does not state. It is true: `ζ⁻¹(ε_k) = k ε_k < L` (`epsK_exists`, `epsK_tendsto_zero`). `proposition_2` uses instead the sets `[ζ(l), ∞)`, `0 < l ≤ l₀`, which exhaust `(0, ∞)`; a strictly positive continuous solution has a positive minimum on compact `X` and so lies in one of them. |
| Proof of Lemma 17.2, p. 512; manual for Exercise 17.9 | `≤ β sup_{x′} [g(x′) − h(x′)]`; the manual's last lines drop `β` and write `sup(g − h)`. | The bound is `β sup \|g − h\|`, since `G₃` may be negative. The weighted-average step is replaced by the equivalent pointwise bound `G(e^g) ≤ e^{β‖g − h‖} G(e^h)` (`abs_log_G_sub_le`, `olgThatF_lipschitz`; for §17.6 `ShocksBounds.abs_log_integrand_sub_le`, `ShocksBounds.opT_exp_le`, `ShocksBounds.ex_17_9`). |
| Manual, Exercise 17.3 | `G₃ = x′ φ′[x′ ζ⁻¹(y)]/ζ′(y)`. | The denominator is `ζ′(ζ⁻¹(y))`. The proof here needs no derivative: (2) would make `G(x, x′, ·)` `β`-Lipschitz, but `G(x, x′, 0) = 0` while `G(x, x′, ζ(l)) > ζ(l)` for small `l > 0` (`ex_17_3`). |
| Proof of Lemma 17.6, (4), (8b), (9), p. 527 | Letting `Δ → 0` in `\|f(x′) − f(x)\| < ε + Δ` gives `< ε`; (9) is `< 3ε`. | It gives `≤ ε`, and (9) is `≤ 3ε`; harmless. The proof here is a Cauchy estimate through a finite `δ`-net (`cauchySeq_of_uniformEquicontinuous`), which avoids the uniform continuity of the limit, and uses completeness of `C(X)` (`lemma_17_6`). |
| Manual, Exercise 17.5(a) | Schauder on the closed `δ`-ball "about zero" in `C[0, t₀]`. | The ball must be centred at the constant function `c` (`fp_ode_exists`). |
| Manual, Exercise 17.7 | Schauder on `F = C(X, D)`, `D ⊆ [0, L)`; "Why?" is not answered. | The answer: `n* = ζ⁻¹ ∘ f*` and `f* = ζ ∘ n*` (`ex_17_7_why_of_f`, `ex_17_7_why_of_n`). The fixed point bounded away from zero is obtained from Proposition 4 through this correspondence (`ex_17_7`). |
| Proof of Proposition 4, p. 523 | `Tf` is continuous because `π` is Feller. | Lemma 17.5 makes each `Tf` uniformly continuous directly (`lemma_17_5`, `proposition_4`). |
| Exercise 17.10, p. 536 | No answer in the manual. | With `x ~ U[1, 2]`, `θ ~ U[1, 3/2]` and `z_n ↓ z̲ = 2/3`, `G(·\|z_n) → δ_{3/2}` weakly, but `‖G(·\|z_n) − G(·\|z̲)‖_TV ≥ 1` for all `n`, and `G(·\|z_n)` has no total-variation limit (`ex_17_10`). |
| Step 4 of Proposition 7, pp. 537–539 | L'Hôpital at `z̲`: `L = φ_f′(θ̄) a′(z̲) − L` for `L = lim (Tf)′`, then bounds on each subinterval. | Circular: it presupposes that the limit exists, and a limit value is not a uniform bound. Replaced by a direct estimate: `\|φ_f(θ) − Tf(z)\| ≤ K(b − a)` and `∫_a^b θ dθ ≥ θ̲(b − a)` give `\|wavg(a, b) − wavg(a′, b′)\| ≤ (θ̄/θ̲) K (\|a − a′\| + \|b − b′\|)` (`shocksWAvg_lipschitz`), so every `Tf` is Lipschitz with constant `(θ̄/θ̲) K (x̲ + x̄)/z̲²` (`shocksUnif_opT_lipschitz`), across the kinks of `a`, `b` and at the end points, with no differentiability. |
| Exercise 17.14, (d) ⇒ (b) ⇒ (a), p. 540 | The chain proves Proposition 8. | (d) gives `zJ′/J ≤ 1` (`ex_17_14d_deriv`) while (b) assumes `zJ′/J < 1`; with `≤` one gets only `zη′/η ≤ 1` (`ex_17_14b_le`), so the chain does not close. `proposition_8` closes it without derivatives: `J(z)/z = (η(z)/z) H′(η(z))` is nonincreasing (`ex_17_14d`), and since `H′` is strictly increasing, `η(z)/z` is strictly decreasing. |
| Exercise 17.14(c)–(d) (manual) | (c) by differentiating `ξ`; (d) by four cases with the uniform weights. | (c) is proved by differentiating under the integral (`ShocksBounds.ex_17_13_deriv`, `ShocksBounds.ex_17_14c`), and in monotone form (`ShocksBounds.phiF_antitoneOn`, `ShocksBounds.phiF_mul_monotoneOn`). (d) is proved with the correct weights by one monotonicity argument after the substitution `θ = x/z` (`shocksWAvg_div`, `ex_17_14d`). |

## Conventions

* State spaces are subtypes such as `Icc a b`, transition functions are Markov kernels, and the
  Feller property is `IsFellerKernel`. `C(X)` is `X →ᵇ ℝ` with the sup norm, ordered pointwise.
* The derivatives `H′`, `H″`, `V′`, `V″` are explicit functions, derivatives within `[0, L)` and
  `[0, ∞)`, so one-sided at `0`. In `MonotoneOLG`, `ζ⁻¹(y)` is `ζ⁻¹(max y 0)`
  (`MonoAssumption17_1H.zetaInv_of_nonpos`), which leaves `T` unchanged on nonnegative functions.
* Assumption 17.1 has three copies so that the modules for §§17.3–17.4 and §17.5 are
  self-contained: `Assumption17_1` (§§17.1–17.2, §17.6), `FPAssumption17_1` (§§17.3–17.4, names
  prefixed `fp`) and `MonoAssumption17_1` (§17.5, names prefixed `mono`). Likewise
  Assumption 17.3 (`FPAssumption17_3`, `MonoAssumption17_3`), Lemma 17.5 (`lemma_17_5`,
  `kernelIntegral_uniformEquicontinuous`) and Exercise 17.6 (`ex_17_6`, `kernelIntegral_dist_le`),
  Assumption 17.2 (`Assumption17_2`, `MonoAssumption17_2`; repaired `Assumption17_2R`,
  `MonoAssumption17_2Pos`) and Assumption 17.4 (`MonoAssumption17_4`, on `ℝ₊₊`
  `MonoAssumption17_4Pos`).
* The lower bound `ε_K` of Propositions 2–4. `proposition_5` uses the book's
  `ε_K = min{ε > 0 : ζ⁻¹(ε) = Kε}` (`monoEpsK`). Elsewhere any `ε = ζ(l)` with `H′(l) < aV′(bL)`
  does the same job (`fp_bounds`), and Propositions 2, 6 and 7 use the sets `[ζ(l), ∞)` or
  `[ζ(l₀), B]`.
* Equicontinuity is uniform equicontinuity, as on p. 520. `theorem_17_4` states it in the book's
  `ε`–`δ` form; §17.5 uses Mathlib's `UniformEquicontinuous`. The total-variation norm is the
  supremum over finite measurable partitions, as in §11.3 (`fpTVNorm`, `TVDistLE`); the book's
  `< ε` for all `ε` is equivalent to `≤ ε` for all `ε`.
* In §17.6 the densities `ψ`, `g` are functions on `ℝ` vanishing off `X`, `Θ`, and integrals are
  Lebesgue integrals on `ℝ`. The double integral `∫_Z ∫_Θ h(θ′, z′) G(dθ′|z′) π(dz′)` in (4) is the
  expectation under the joint law `μ` of `(θ′, z′)` (`shocksJointLaw`), so (4) is
  `(Tf)(z) = ∫ φ_f dG(·|z)` with `φ_f` from `shocksPhiF`. `proposition_6`, `proposition_7` and
  `shocks_finite_Z` hold for any compact metric `Z`, any probability law `μ` and (for
  Proposition 6) any weakly continuous family `G(·|z)`; `θ′`, `θ̃` are clamped to `Θ`
  (`shocksClamp`), which changes nothing on the supports. `proposition_6_islands` and
  `proposition_7_islands` are the islands model itself. `proposition_8` assumes the repaired
  Assumption 17.1 for `V` and Assumption 17.4 on `ℝ₊₊`, both weaker than the book's.
* In §17.6, `G` is the distribution of `θ`, not the kernel `G(x, x′, y)` of §§17.2–17.5, and `π`
  is the density of `z`, not a transition function. `G` is taken as the law of the parameter of
  the agent's own market, as in the book; with shares `θ/2` and `1 − θ/2` the law a given young
  agent faces would be size-biased. This modelling point is not formalised.
* Misprints, not formalised: in Exercise 17.5(c), "Exercise 3.8" should be "Exercise 3.10", the
  Lipschitz ODE exercise on p. 53 (`ex_17_5c` proves that `√·` violates its Lipschitz condition).
  In Step 4 of Proposition 7: (7) holds on `Ẑ`, not "all `z ∈ Z`" (`eq7_corrected` is stated on
  `Ẑ`); "`z → x̲/z̄`" should be "`z → x̲/θ̄`"; "the numerator in (8)" should be "(7)"; the
  left-derivative formula at `x̲/θ̲` has lost the minus sign of (7).
* Proposition 3 is true as stated: the proof's `F = [ε_K, B]ᵐ` excludes the zero solution
  (`proposition_3`, `proposition_3_zero_fixedPoint`). Proposition 4 is likewise stated for
  strictly positive solutions (`proposition_4`, `proposition_4_zero_fixedPoint`).
* Theorem 17.7 is a monotone-iteration theorem, not Tarski's: `F` need not be a complete lattice.
* Figures 17.1–17.5 are not formalised as pictures; the facts they show are (see the
  [source map](source-map.md)). The concrete economies and functions (`olgExH`, `monoCexH`,
  `monoCexV`, `monoCexW`, `monoArcV`, `shocksEx_assumption`, `shocksExBimodal`, `shocksEtaEx`) are
  not in the book.

## Not proved

* **Discontinuous prices** (p. 533). Every equilibrium with a continuous price function has the
  form `p = ρ(x/θ)` with `ρ` continuous and strictly monotone, for any price-indexed beliefs
  (`islands_eqm_price_of_ratio`), so no continuous equilibrium price is fully revealing
  (`islands_eqm_not_injOn`). Continuity is needed for the argument (`p533_counterexample`).
  Whether a discontinuous price can reveal more than `x/θ` in an equilibrium, with suitable
  off-path beliefs, is not settled.
* **Monotone iteration for the operator (4)** (p. 539). Monotonicity of `T` is proved
  (`ShocksBounds.opT_monotone`); the analogue of Proposition 5 for (4) is not carried out.
* **The §17.1 economy beyond (1)–(2)**: the book's question why Chapter 15 does not apply
  (p. 503) is not formalised.
* **Misprints** listed under Conventions are not formalised.
* **The chapter introduction, the discussions on pp. 512–513, 515–516, 519, 524–525, 535–536 and
  541, and §17.7** (bibliographic notes) are not formalised, except for the mathematical claims in
  them recorded above.

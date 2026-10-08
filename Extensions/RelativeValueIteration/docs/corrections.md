# Departures from the sources

Places where a Lean statement differs from the published one: a hypothesis made explicit, a
special case proved, or a definition chosen among equivalent ones.

| Where | Published | How it is stated |
| --- | --- | --- |
| Convergence rates (Bray, 2019a, Prop 3; 2019b, Prop 4) | Asymptotic: the relative (endogenous) value error is `O⁺(βⁿλⁿ)` with `λ` the spectral subradius of `F(p*)` (of `ΛF(p*)`). | Non-asymptotic: if `α` bounds the Dobrushin coefficient over all feasible state–action pairs (`α_y` the coefficient of the endogenous transitions within each exogenous state), the error in span is at most `(βα)ⁿ` (`(βα_y)ⁿ`) times the initial one, at every `n`. The Dobrushin coefficient bounds the spectral subradius, so these rates are weaker but hold uniformly. |
| Relative value iteration | Subtract `v(x₁)`. | Subtract `v(s₀)` for any reference state `s₀`. |
| Endogenous value iteration | `Λ = I_X ⊗ (I_Y − ιι′/Y)`. | `Λv(x, y) = v(x, y) − mean_{y'} v(x, y')` (`endo`); the action space may depend on the state. |
| Stopping rule (Bray, 2019a) | Stop when `‖V_n − V_{n−1}‖ < ε(1 − β)/(2β)`; return the policy greedy for `V_n`. | The policy greedy for `V_n` is `ε`-optimal once `|V_{n+1} − V_n| ≤ ε(1 − β)/(2β)` (`stopping_rule_sup`), via the sharper span criterion `β/(1 − β)·sp(V_{n+1} − V_n) ≤ ε` (`stopping_rule`). |
| Endogenous `ε`-optimality (Bray, 2019b, Prop 3) | Stopping rule on endogenous iterates. | An a priori bound: the policy greedy for `ΛTⁿV₀` is within `2β/(1 − β)·spy(TⁿV₀ − v*)` of optimal (`endo_policy_error`), combined with `spy(TⁿV₀ − v*) ≤ (βα_y)ⁿ spy(V₀ − v*)`. |
| Average reward (White, 1963) | Unichain, aperiodic. | The Dobrushin coefficient over all feasible state–action pairs is below `1`, which implies both. |

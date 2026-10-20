# Departures from the sources

Places where a Lean statement differs from the published one: a hypothesis made explicit, a
special case proved, or a definition chosen among equivalent ones.

| Where | Published | How it is stated |
| --- | --- | --- |
| Topkis's theorem | Actions in a lattice, objective supermodular in the action and with increasing differences in (state, action); the argmax is a sublattice ascending in the state. | Actions in a linear order, with finite feasible sets (`Γ : X → Finset A`); on a chain supermodularity in the action is automatic. The state space is any preorder, so the theorem covers parameters as well as states. |
| Monotone optimal policies (Stokey and Lucas, 1989, Ch. 9) | General state and action spaces with continuity and compactness. | Finitely many states, finite feasible sets, rewards and transitions without continuity assumptions. Optimal means: value at least that of every feasible policy, at every state. |
| Savings problem | A continuum of asset levels, often differentiable utility. | Assets on a finite grid, any concave utility (no differentiability, no Inada conditions), i.i.d. income, a borrowing limit at a grid point affordable in every state. Saving is the greatest optimal choice; with ties other optimal rules may fail to be monotone. |

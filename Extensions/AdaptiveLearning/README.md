# Adaptive learning in Lean

This is the `Extensions/AdaptiveLearning/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd Extensions/AdaptiveLearning` from the
repository root. [Return to the library index](../../README.md).

An extension beyond Sargent and Stachurski's *Dynamic Programming*: which rational expectations
equilibria can agents *learn*? It builds on the stochastic approximation of Volume 2, Chapter 9
(`GeneralStates/ApproximationAndLearning`), following Bray and Savin (1986), Marcet and Sargent
(1989) and Evans and Honkapohja (2001). The library contains **19 theorems**.

* **Stochastic approximation with a Lyapunov function**: the Robbins–Siegmund lemma, and almost
  sure convergence of `θ_{k+1} = θ_k + α_k(h(θ_k) + W_k)` in a Hilbert space whenever a quadratic
  Lyapunov function `⟪Q(x − θ̄), x − θ̄⟫` decreases along `h` (`sa_lyapunov`). No contraction is
  needed.
* **The cobweb model**: least-squares learning of the price converges almost surely to the REE iff
  `β < 1` (E-stability), even for `β < −1`, where the expectations map is not a contraction and
  naive expectations explode (`cobweb_learning`, `learning_diverges`, `naive_diverges`). From
  demand and supply primitives, `β = −s/b < 0`: the cobweb is always learnable, though it
  explodes under naive expectations when supply is more price-responsive than demand
  (`cobweb_market`). The gain `1/(t + 1)` is the sample mean (`harmonic_gain`, `recursive_mean`).
* **E-stability of linear models**: E-stability in Lyapunov form (`IsEStable`), sufficient
  conditions (`⟪x, Bx⟫ ≤ λ‖x‖²` with `λ < 1`, `‖B‖ < 1`), the scalar case `β < 1`, the
  eigenvalue obstruction and divergence along an eigenvector with eigenvalue above `1`,
  uniqueness and finite-dimensional existence of the REE, and almost sure convergence of
  steady-state learning to an E-stable REE (`estable_learning`).

The main entry points are `robbins_siegmund`, `sa_lyapunov`, `cobweb_learning`,
`learning_diverges`, `naive_diverges`, `cobweb_market`, `IsEStable`, `isEStable_smul_iff`,
`not_isEStable_of_eigen`, `learning_diverges_of_eigen`, `ree_existsUnique` and
`estable_learning`, all in the namespace `DPExtensions.AdaptiveLearning`.

See the [source map](docs/source-map.md) for the correspondence with the literature, and
[departures from the sources](docs/corrections.md) for where the Lean statements differ:

* E-stability is stated in quadratic Lyapunov form; its equivalence with the eigenvalue
  condition (Lyapunov's theorem) is not formalised;
* learning is steady-state learning (least squares on a constant), not recursive least squares
  with regressors.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [RobbinsSiegmund](AdaptiveLearning/RobbinsSiegmund.lean) | 1 | Robbins–Siegmund lemma (copied from Vol 2 Ch 9) |
| [LyapunovSA](AdaptiveLearning/LyapunovSA.lean) | 1 | Stochastic approximation with a quadratic Lyapunov function |
| [Cobweb](AdaptiveLearning/Cobweb.lean) | 9 | Learning in the cobweb model, naive expectations, E-instability |
| [EStability](AdaptiveLearning/EStability.lean) | 8 | E-stability of linear models, REE existence, learnability |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.

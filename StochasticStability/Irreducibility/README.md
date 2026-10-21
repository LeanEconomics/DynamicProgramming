# Meyn and Tweedie, Chapter 4: Irreducibility, in Lean

This is the `StochasticStability/Irreducibility` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 4 of Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge
University Press, 2009), pp. 75–95. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 4 is about irreducibility, the property that every part of the space can be reached from
every starting point. On a countable space, two states communicate when each leads to the other.
The communicating classes partition the space, and a chain is irreducible when there is only one
class (§4.1). A general space has no such relation. Its analogue is φ-irreducibility: every set
of positive φ-measure is reached from every state. Theorem 4.0.1 gives an essentially unique
maximal irreducibility measure `ψ`. Sets that are `ψ`-null are avoided from `ψ`-almost every
state, and every full set contains an absorbing set. Uniform accessibility `A ⇝ B` is a
quantitative form of reaching a set (§4.2). The rest of the chapter verifies irreducibility for
the book's models: random walk on a half line and storage models through the atom `{0}`,
unrestricted random walk through a density (§4.3), and the linear models. For the linear models,
controllability of LCM(F, G) gives Lebesgue irreducibility of LSS(F, G) (§4.4).

Every numbered result is formalised: Theorem 4.0.1, Propositions 4.1.1–4.1.2, 4.2.1–4.2.4, 4.3.1
and 4.4.1–4.4.3, and Lemmas 4.2.5–4.2.6, together with the claims the text makes about its
examples. Seven claims are false as printed. Each is refuted in Lean by a counterexample, and a
corrected statement is proved: Proposition 4.2.2 and Theorem 4.0.1 need a nonzero irreducibility
measure; Proposition 4.2.3 (i) needs a non-empty absorbing set; the dichotomy "`L(x, 0) > 0` for
all states or for none" (p. 77) fails at `x = 0`; the GI/M/1 chain is not irreducible for every
interarrival law (p. 80); the M/G/1 chain is not always irreducible (p. 80); the controllability
Gramian (4.17) need not converge; and the constant in the density (4.18) is wrong. No result needs a countably generated σ-algebra or a σ-finite irreducibility measure.
Proposition 4.4.3 holds for any noise law equivalent to Lebesgue measure, not only for Gaussian
noise. Two claims the book states without proof are also formalised. When `(F, G)` is not
controllable, LSS(F, G) restricted to its controllable subspace is a controllable linear model,
and it is Lebesgue-irreducible there (p. 93). The content-dependent storage model is
δ₀-irreducible when the store empties in a finite time (§4.3.2). The following are not
formalised: the heuristic of pp. 79–80, the AR(k) explosion heuristics of p. 90, (4.15)–(4.16)
as moments, the Lebesgue irreducibility of the storage model with `R = ∞`, the Doeblin
decomposition (4.8) on a general space (its countable version is formalised), and the commentary
of §4.5. See [corrections](docs/corrections.md). The library contains **452 theorems**. Of these,
207 are in the Chapter 4 modules and 245 in the modules carried from Chapters 1–3.

* **Communication on a countable space** (§4.1.2). `x → y`, `x ↔ y` and Proposition 4.1.1; the
  communicating classes `C(x)` partition `X`. A chain is irreducible when `C(x) = X`, and
  irreducibility is equivalent to all states communicating. `C(x)` is not absorbing exactly when
  some state outside it is reached. The decomposition (4.5) splits `X` into the absorbing classes
  and the rest `D`. Proposition 4.1.2: an absorbing class carries an irreducible chain, given by
  the kernel restricted to its states.
* **Countable models** (§4.1.1, §4.1.3). Random walk on the half line `ℤ₊`: under (4.4), `{0}` is
  reached from every state. If the increments are nonnegative, it is reached from no state other
  than `0`. Increments on the even integers split the space into even and odd states. The
  forward recurrence time chain is irreducible on `{1, …, r}`. GI/M/1 and M/G/1 are irreducible
  under explicit conditions on the laws. Random walk on `ℤ` has the cosets of `dℤ` as its
  communicating classes, finitely many of them; the walk on `ℚ` with integer increments has
  infinitely many. On a countable space, (4.5) is a Doeblin decomposition with countably many
  absorbing classes.
* **φ-irreducibility** (§4.2.1). The definition, the kernel `K_{a_{1/2}}` of (4.9) and its
  equivalence with `I + U`, and Proposition 4.2.1. Restrictions and absolutely continuous
  measures are again irreducibility measures. `δ_{x*}`-irreducibility. On a countable space,
  irreducibility is irreducibility for counting measure.
* **Maximal irreducibility measures** (§4.0, §4.2.2). An exhaustion lemma gives every nonzero
  irreducibility measure an equivalent probability measure. The measure `ψ` of (4.10) and
  Proposition 4.2.2. Theorem 4.0.1, with the essential uniqueness of `ψ`. `B⁺(X)`, full and
  absorbing sets, Proposition 4.2.3, and Proposition 4.2.4 for the chain restricted to an
  absorbing set. Counting measure is maximal for an irreducible countable chain.
* **Accessibility** (§4.2.3). Accessible and uniformly accessible sets (4.11). Lemma 4.2.5 is
  proved from the strong Markov property at the first return time. The sets `Ā`, `Ā(m)` and
  `A⁰`, Lemma 4.2.6 with its bound `L(x, A) ≥ m⁻²`, and the countable cover of `X` for a
  φ-irreducible chain. `⇝` is not reflexive.
* **Random walk and storage models** (§4.3, §4.4.1). Proposition 4.3.1 for random walk on
  `[0, ∞)`, with `C ⇝ {0}` for compact `C` and the maximal measure `Σₙ Pⁿ(0, ·) 2⁻ⁿ`. The
  content-dependent storage model: δ₀-irreducible when the store empties in finite time, and not
  δ₀-irreducible when it never empties. Unrestricted random walk and AR(1) with `|α| ≤ 1` are
  Lebesgue-irreducible near `0` under a local density, and so is a random walk with spread-out
  increments. A random walk with rational increments has uncountably many absorbing sets. AR(1)
  with bounded noise and `|α| > 1` explodes and is irreducible for no nonzero measure.
* **Linear models** (§4.4.2–§4.4.3). The controllability matrix (4.13) and the closed form (4.14).
  Proposition 4.4.1, and the Cayley–Hamilton consequences: controllability is equivalent to
  (LCM3), and to `rank C_k = n` for some `k`. Proposition 4.4.2 for AR(k), with the triangular
  structure of `C_n`. The variance `Σ_k = C_k C_kᵀ`, with the same rank and range as `C_k`.
  Proposition 4.4.3, and its Gaussian case (LSS3). AR(k) with an innovation law equivalent to
  Lebesgue measure is Lebesgue-irreducible for all coefficients, and so is LSS(F, G) with a
  square `G` of full rank. The controllable subspace `X₀` is absorbing, of dimension
  `rank C_n`, which is less than `n` when `(F, G)` is not controllable. On `X₀`, the restricted
  chain is LSS(F₀, G₀) with `(F₀, G₀)` controllable, and Lebesgue measure on `X₀` is a maximal
  irreducibility measure.

All names are in the namespace `MeynTweedie.Irreducibility`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Communication](Irreducibility/Communication.lean) | 33 | Reaching sets, absorbing sets, `P_A`; `→`, `↔`, Proposition 4.1.1, (4.5), Proposition 4.1.2 |
| [CountableIrreducibility](Irreducibility/CountableIrreducibility.lean) | 32 | §4.1.1, §4.1.3: random walk on `ℤ₊`, recurrence times, GI/M/1, M/G/1, random walk on `ℤ` and `ℚ` |
| [PsiIrreducibility](Irreducibility/PsiIrreducibility.lean) | 13 | φ-irreducibility, `K_{a_{1/2}}` (4.9), Proposition 4.2.1, `δ_{x*}` and counting measure |
| [MaximalIrreducibility](Irreducibility/MaximalIrreducibility.lean) | 30 | (4.10), Proposition 4.2.2, Theorem 4.0.1, `B⁺(X)`, full sets, Propositions 4.2.3–4.2.4 |
| [Accessibility](Irreducibility/Accessibility.lean) | 9 | (4.11), Lemmas 4.2.5–4.2.6, the countable cover |
| [RandomWalkIrreducibility](Irreducibility/RandomWalkIrreducibility.lean) | 20 | Proposition 4.3.1, §4.3.3, the scalar AR(1) model of §4.4.1 |
| [StorageIrreducibility](Irreducibility/StorageIrreducibility.lean) | 7 | §4.3.2: the content-dependent storage model |
| [LinearControllability](Irreducibility/LinearControllability.lean) | 26 | (LCM3), (4.13)–(4.14), Propositions 4.4.1–4.4.2, `Σ_k`, (4.17) |
| [LinearIrreducibility](Irreducibility/LinearIrreducibility.lean) | 14 | Proposition 4.4.3, the Gaussian case, `X₀` absorbing, (4.18) |
| [LinearRestriction](Irreducibility/LinearRestriction.lean) | 13 | p. 93: LSS(F, G) restricted to its controllable subspace |
| [IrreducibilityExtras](Irreducibility/IrreducibilityExtras.lean) | 10 | Further text claims: AR(k) (p. 89), full-rank `G` (p. 92), the Gramian's range and `dim X₀` (p. 93), (4.5) as a Doeblin decomposition, `⇝` not reflexive (p. 86) |

Carried from the Chapter 3 project `TransitionProbabilities` (169 theorems), identical except for
the namespace and, in `SpecificMatrices`, a module-docstring cross-reference to modules that are
not carried:

* `StateSpaces` (2): the three kinds of state space of §3.1.
* `PathSpace` (23), `Kernels` (32): the path measures `Pₓ`, `n`-step kernels, the resolvent and
  the potential kernel `U`.
* `MarkovProperty` (22), `StrongMarkov` (20): the Markov and strong Markov properties. The strong
  Markov property is used in Lemma 4.2.5.
* `HittingTimes` (36): `τ_A`, `L(x, A)` and the first-step identity, used in Proposition 4.2.1.
* `CountableChains` (13), `SpecificMatrices` (21): transition matrices and the matrices of §3.3
  (recurrence times, random walk on `ℤ` and `ℤ₊`, GI/M/1, M/G/1, the linear model on `ℚ`). They
  are used in §4.1.

Carried from the Chapters 1–2 project `MarkovModels` (76 theorems), identical except for the
namespace, the module names and a note in each module docstring:

* `ModelRecursion` (18): the kernel of a random recursion and its `n`-step law.
* `ModelRandomWalk` (19): random walk, convolution powers and random walk on a half line, used in
  §4.3.
* `ModelLinearModels` (39): LSS(F, G), LCM(F, G) and controllability, AR(1) and AR(k), used in
  §4.4.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.

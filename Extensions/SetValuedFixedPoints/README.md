# Set-valued fixed points in Lean

This is the `Extensions/SetValuedFixedPoints/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd Extensions/SetValuedFixedPoints` from the
repository root. [Return to the library index](../../README.md).

An extension beyond the books: the fixed-point theorems for **correspondences** on which the
existence theory of equilibrium rests, from Kakutani's theorem to the theorems used for
heterogeneous-agent economies with aggregate risk (Duffie, Geanakoplos, Mas-Colell and McLennan
1994; Miao 2006; Cao 2020). Mathlib has Banach's and Tarski's fixed-point theorems but not
Brouwer's, Schauder's or Kakutani's; Brouwer and Schauder were proved in
`RecursiveMethods/FixedPointArguments` (Stokey, Lucas and Prescott, Theorems 17.3–17.4) and are
carried here. The library contains **29 theorems**.

* **Brouwer and Schauder** (carried): a continuous self-map of a nonempty compact convex set has
  a fixed point, in finite dimensions by Rogers's analytic proof and in any real normed space by
  Schauder projections (`brouwer`, `schauder`, `schauder_closed`).
* **Schauder–Tychonoff**: a continuous self-map of a nonempty compact convex subset of a real
  locally convex Hausdorff space has a fixed point (`schauderTychonoff`). Gauges of convex
  neighbourhoods of zero replace the norm in the Schauder projection, Brouwer is applied on a
  standard simplex, and every convex neighbourhood of zero then contains `x − f x` for some
  `x ∈ K` (`exists_approx_fixedPoint_nhds`); the finite intersection property and compactness
  give a single `x` with `x − f x` in the closure of every such neighbourhood, hence zero.
* **Kakutani's theorem in normed spaces**: a correspondence on a nonempty compact convex subset
  `K` of a real normed space, with nonempty convex values in `K` and a closed graph over `K`, has
  a fixed point (`kakutani`; the usual form in `ℝⁿ` is `kakutani_euclidean`). The proof is by
  approximate continuous selections: a tent-function partition of unity on a finite `ε`-net gives
  a continuous self-map of `K` whose Schauder fixed points are approximate fixed points of the
  correspondence (`exists_approx_fixedPoint`), and the closed graph into a compact set gives upper
  hemicontinuity (`exists_uhc`), which passes to the limit through convex thickenings of the
  values.

The main entry points are `kakutani`, `kakutani_euclidean`, `exists_approx_fixedPoint`,
`exists_uhc`, `schauderTychonoff`, `exists_approx_fixedPoint_nhds`, `schauder` and `brouwer`, all in the namespace `DPExtensions.SetValuedFixedPoints`.

See the [source map](docs/source-map.md) for the correspondence with the literature, and
[departures from the sources](docs/corrections.md) for where the Lean statements differ.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [BrouwerRetraction](SetValuedFixedPoints/BrouwerRetraction.lean) | 4 | No C¹ retraction of the ball onto the sphere (carried from SLP Ch. 17) |
| [BrouwerBall](SetValuedFixedPoints/BrouwerBall.lean) | 4 | Brouwer for the closed unit ball (carried) |
| [Brouwer](SetValuedFixedPoints/Brouwer.lean) | 5 | Brouwer for compact convex sets in finite dimensions (carried) |
| [Schauder](SetValuedFixedPoints/Schauder.lean) | 5 | Schauder in real normed and Banach spaces (carried) |
| [Kakutani](SetValuedFixedPoints/Kakutani.lean) | 8 | Approximate fixed points, upper hemicontinuity from a closed graph, Kakutani |
| [SchauderTychonoff](SetValuedFixedPoints/SchauderTychonoff.lean) | 3 | Approximate fixed points up to a convex neighbourhood of zero, Schauder–Tychonoff |

## Roadmap

The project is the base for proving existence of equilibrium in Krusell–Smith economies. Planned
modules, in order:

1. **Schauder–Tychonoff** in locally convex Hausdorff spaces (done: `SchauderTychonoff`).
2. **Fan–Glicksberg**: Kakutani in locally convex Hausdorff spaces, by the same approximate
   selections with convex neighbourhoods in place of balls. This is the theorem the existence
   proofs for economies with a continuum of agents use, on spaces of measures with the weak
   topology.
3. **Economic applications**: Nash equilibrium in mixed strategies via Berge's maximum theorem;
   the Gale–Nikaido–Debreu lemma and competitive equilibrium of an exchange economy.
4. **Measurable selection** (Kuratowski–Ryll-Nardzewski), if the finite-dimensional selection
   theorem of `RecursiveMethods/StochasticDP` proves insufficient for policy correspondences on
   spaces of distributions.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.

# Source map

Lean names are relative to `DPExtensions.SetValuedFixedPoints`. Where a Lean statement departs
from the published one, see [departures from the sources](corrections.md).

## Carried from Stokey, Lucas and Prescott, Chapter 17

The modules `BrouwerRetraction`, `BrouwerBall`, `Brouwer` and `Schauder` are copies of the
modules of the same names in `RecursiveMethods/FixedPointArguments`, with the namespace changed.

| Source | Claim | Lean |
| --- | --- | --- |
| Rogers (1980); Milnor (1965) | No C¹ retraction of the closed unit ball onto the sphere | `no_C1_retraction` |
| SLP Theorem 17.3, p. 517 | Brouwer's fixed-point theorem | `brouwer_closedBall`, `brouwer_ball`, `brouwer`, `brouwer_subtype` |
| SLP Theorem 17.4, p. 520 | Schauder's fixed-point theorem | `schauder`, `schauder_subtype`, `schauder_closed`, `schauder_closed_subtype` |

## The Schauder–Tychonoff theorem

| Source | Claim | Lean |
| --- | --- | --- |
| Tychonoff (1935) | A continuous self-map of a nonempty compact convex subset of a locally convex Hausdorff space has a fixed point | `schauderTychonoff`, `schauderTychonoff_subtype` |
| Aliprantis and Border (2006), Ch. 17 (Schauder projections in locally convex spaces) | Approximate fixed points up to any convex neighbourhood of zero | `exists_approx_fixedPoint_nhds` (in any real topological vector space) |

## Kakutani's theorem

| Source | Claim | Lean |
| --- | --- | --- |
| Kakutani (1941), Theorem 1 | An upper hemicontinuous correspondence from a simplex into itself with nonempty closed convex values has a fixed point | `kakutani_euclidean` (closed graph over a compact convex `K ⊆ ℝⁿ`) |
| Bohnenblust and Karlin (1950); Glicksberg (1952) | Kakutani in Banach and in locally convex spaces | `kakutani` (any real normed space; the locally convex case is planned) |
| Cellina (1969); Aliprantis and Border (2006), Ch. 17 | Approximate continuous selections of a correspondence with convex values | `exists_approx_fixedPoint` |
| Aliprantis and Border (2006), Ch. 17 (closed graph theorem) | A correspondence with closed graph into a compact space is upper hemicontinuous | `exists_uhc` (in the thickening form) |
| Aliprantis and Border (2006), Ch. 17 | A correspondence with closed graph has closed values | `isClosed_apply_of_isClosed_graphOn` |

## References

* C. Aliprantis and K. Border, *Infinite Dimensional Analysis*, 3rd ed., Springer (2006).
* H. F. Bohnenblust and S. Karlin, "On a theorem of Ville", in *Contributions to the Theory of
  Games I*, Princeton (1950).
* A. Cellina, "Approximation of set valued functions and fixed point theorems", *Annali di
  Matematica Pura ed Applicata* 82 (1969).
* I. L. Glicksberg, "A further generalization of the Kakutani fixed point theorem, with
  application to Nash equilibrium points", *Proceedings of the AMS* 3 (1952).
* S. Kakutani, "A generalization of Brouwer's fixed point theorem", *Duke Mathematical Journal*
  8 (1941).
* C. A. Rogers, "A less strange version of Milnor's proof of Brouwer's fixed-point theorem",
  *American Mathematical Monthly* 87 (1980).
* N. Stokey and R. Lucas with E. Prescott, *Recursive Methods in Economic Dynamics*, Harvard
  (1989).
* A. Tychonoff, "Ein Fixpunktsatz", *Mathematische Annalen* 111 (1935).

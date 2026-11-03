# Departures from the sources

* **Schauder–Tychonoff: the map need only be continuous on `K`.** `schauderTychonoff` takes
  `f : E → E` continuous on `K` with `f(K) ⊆ K`, as `schauder` does; `schauderTychonoff_subtype`
  is Tychonoff's form `f : K → K`. The proof follows the Schauder-projection route of Aliprantis
  and Border rather than Tychonoff's original one, and works with the standard simplex on a
  finite cover of `K` instead of the finite-dimensional span of its centres, so Brouwer is applied
  in a normed space even though `E` carries no norm.
* **Closed graph in place of upper hemicontinuity.** Kakutani (1941) assumes an upper
  hemicontinuous correspondence with closed values. `kakutani` assumes instead that the graph of
  the correspondence over `K` is closed. For a correspondence into a compact set the two are
  equivalent; the closed-graph form is the one that is easy to check in applications, and the
  implication used in the proof is `exists_uhc`.
* **Domain.** The theorem is stated for a nonempty compact convex subset of a real normed space,
  which covers Kakutani's simplex and Bohnenblust and Karlin's Banach-space version (a compact
  convex set rather than a convex set with compact image). Fan and Glicksberg's locally convex
  version is `fanGlicksberg`, with the same closed-graph hypothesis.
* **Fan–Glicksberg: proof route.** Fan and Glicksberg reduce to finite-dimensional fixed-point
  theorems; `fanGlicksberg` instead repeats the
  approximate-selection proof of `kakutani` in the locally convex space itself, on top of
  `schauderTychonoff`, and replaces the convergent subsequence by a finite cover of `K` and a
  proof by contradiction.
* **Proof route.** Kakutani's proof uses simplicial subdivisions; the proof here uses approximate
  continuous selections and Schauder's theorem, and needs no Carathéodory argument: the limit of
  approximate fixed points lies in every closed convex thickening of its value.

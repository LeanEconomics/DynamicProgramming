# Departures from the sources

* **Closed graph in place of upper hemicontinuity.** Kakutani (1941) assumes an upper
  hemicontinuous correspondence with closed values. `kakutani` assumes instead that the graph of
  the correspondence over `K` is closed. For a correspondence into a compact set the two are
  equivalent; the closed-graph form is the one that is easy to check in applications, and the
  implication used in the proof is `exists_uhc`.
* **Domain.** The theorem is stated for a nonempty compact convex subset of a real normed space,
  which covers Kakutani's simplex and Bohnenblust and Karlin's Banach-space version (a compact
  convex set rather than a convex set with compact image). Glicksberg's locally convex version is
  not yet formalised.
* **Proof route.** Kakutani's proof uses simplicial subdivisions; the proof here uses approximate
  continuous selections and Schauder's theorem, and needs no Carathéodory argument: the limit of
  approximate fixed points lies in every closed convex thickening of its value.

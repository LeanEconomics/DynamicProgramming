/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.MinimalSets
import InvarianceTightness.Period

/-!
# Periodicity for control models (MT §7.3.1)

Meyn and Tweedie, §7.3.1, pp. 157–160. `X` and `W` are finite-dimensional real normed spaces;
for the rank condition `F` is `C¹` and the control set `O` is open.

* `IsKAccessible.mono`: `B →ⁿ C` passes to smaller `B` and `C`.
* **Proposition 7.3.1** (p. 158): `proposition_7_3_1`, under the rank condition (CM3) (forward
  accessibility) every `x` lies in an open `B` with `B →ᵏ C` for a non-empty open `C`, `k ≥ 1`.
* **Lemma 7.3.2** (p. 158): `lemma_7_3_2`, a minimal set contains a non-empty open `E` with
  `E →ⁿ E` for some `n ≥ 1`.
* `returnTimes F O E = I` ((7.17)), additively closed (`returnTimes_isAddClosed`), and
  `orbitClass F O M E d i = Gᵢ` ((7.18), indexed by `i ∈ ZMod d`).
* `OrbitData` and its lemmas (`OrbitData.iUnion_eq`, `OrbitData.disjoint`, `OrbitData.isClosed`,
  `OrbitData.step`, `OrbitData.subset_zero`, `OrbitData.unique`): for `d = g.c.d. I`, the `Gᵢ` are
  disjoint closed sets covering `M` with `A₊¹(Gᵢ) ⊆ Gᵢ₊₁`, `E ⊆ G₀`; and every periodic orbit `H`
  of period `d'` with union `M` has `d' ∣ d` and `Gⱼ ⊆ H_{a + j}` for some `a`.
* **Theorem 7.3.3** (p. 158): `theorem_7_3_3`, the cyclic decomposition of a minimal set, with
  uniqueness: each `Hᵢ` is a union of `Gⱼ` (`theorem_7_3_3_union`). `IsPeriodOf F O M d`: `d` is
  the period of `M` (the largest period of a periodic orbit with union `M`; every other period
  divides it), and `exists_isPeriodOf`.
* **Proposition 7.3.4** (p. 160): `proposition_7_3_4`, if `O` is connected, each `Gᵢ` is
  connected and is the connected component in `M` of each of its points; and
  `M` is aperiodic iff it is connected (`OrbitData.isConnected_of_isPeriodOf_one`; the direction
  "connected ⇒ aperiodic" needs no connectedness of `O`, and holds for any non-empty minimal set:
  `isPeriodOf_one_of_isConnected`).

**Hypotheses and proof differences.** In the proof of Proposition 7.3.4 the book writes
`G_d = ⋃_{k ≥ N₀} A₊^{kd}(v)` and `G₁ = A₊¹(G_d)`; what is proved here is that `Gⱼ` is the
closure of `A₊^{j}(⋃_{k ≥ N₀} A₊^{kd}(v))`, which is what the connectedness argument uses.
-/

namespace MeynTweedie.InvarianceTightness

open Filter Set Topology

variable {Y W : Type*}

/-- `B →ⁿ C` passes to smaller sets. -/
theorem IsKAccessible.mono {F : Y × W → Y} {O : Set W} {n : ℕ} {B C B' C' : Set Y}
    (h : IsKAccessible F O n B C) (hB : B' ⊆ B) (hC : C' ⊆ C) : IsKAccessible F O n B' C' :=
  fun y hy => hC.trans (h y (hB hy))

/-- The return times `I = {n ≥ 1 : E →ⁿ E}` of (7.17). -/
def returnTimes (F : Y × W → Y) (O : Set W) (E : Set Y) : Set ℕ :=
  {n | 0 < n ∧ IsKAccessible F O n E E}

/-- `I` is closed under addition (MT p. 159). -/
theorem returnTimes_isAddClosed (F : Y × W → Y) (O : Set W) (E : Set Y) :
    IsAddClosed (returnTimes F O E) := by
  rintro i ⟨hi0, hi⟩ j ⟨-, hj⟩
  refine ⟨by omega, fun y hy z hz => ?_⟩
  rw [reachK_add]
  exact mem_biUnion (hi y hy hy) (hj y hy hz)

/-- The cyclic classes (7.18): `Gᵢ = {x ∈ M : A₊ⁿ(x) ∩ E ≠ ∅ for some n with n + i ≡ 0}`. -/
def orbitClass (F : Y × W → Y) (O : Set W) (M E : Set Y) (d : ℕ) (i : ZMod d) : Set Y :=
  {x | x ∈ M ∧ ∃ n : ℕ, (n : ZMod d) + i = 0 ∧ (reachK F O n x ∩ E).Nonempty}

variable [TopologicalSpace Y]

/-- The period of a minimal set (MT p. 159): `d ≥ 1` is the period of a periodic orbit with
union `M`, and the period of every other such orbit divides `d`. `M` is **aperiodic** when
`d = 1`. -/
def IsPeriodOf (F : Y × W → Y) (O : Set W) (M : Set Y) (d : ℕ) : Prop :=
  0 < d ∧ (∃ G : ZMod d → Set Y, IsPeriodicOrbit F O d G ∧ ⋃ i, G i = M) ∧
    ∀ d' (H : ZMod d' → Set Y), 0 < d' → IsPeriodicOrbit F O d' H → ⋃ i, H i = M → d' ∣ d

/-- The period of a minimal set is unique. -/
theorem IsPeriodOf.unique {F : Y × W → Y} {O : Set W} {M : Set Y} {d d' : ℕ}
    (h : IsPeriodOf F O M d) (h' : IsPeriodOf F O M d') : d = d' := by
  obtain ⟨hd, ⟨G, hG, hGM⟩, hmax⟩ := h
  obtain ⟨hd', ⟨G', hG', hGM'⟩, hmax'⟩ := h'
  exact Nat.dvd_antisymm (hmax' d G hd hG hGM) (hmax d' G' hd' hG' hGM')

/-- Hypotheses shared by the lemmas on the classes `Gᵢ`: `M` minimal, `E ⊆ M` open and
non-empty, `n₀ ∈ I`, `d = g.c.d. I`. -/
structure OrbitData (F : Y × W → Y) (O : Set W) (M E : Set Y) (d : ℕ) : Prop where
  /-- Each `F(·, w)`, `w ∈ O`, is continuous. -/
  cont : ∀ w ∈ O, Continuous fun x => F (x, w)
  /-- The control set is non-empty. -/
  ne : O.Nonempty
  /-- `M` is minimal. -/
  minimal : IsMinimal F O M
  /-- `E` is open. -/
  isOpen : IsOpen E
  /-- `E` is non-empty. -/
  nonempty : E.Nonempty
  /-- `E ⊆ M`. -/
  subset : E ⊆ M
  /-- Some `n₀ ≥ 1` has `E →^{n₀} E`. -/
  ret : (returnTimes F O E).Nonempty
  /-- `d` is the g.c.d. of the return times. -/
  gcd : d = setGcd (returnTimes F O E)

omit [TopologicalSpace Y] in
/-- Chaining `E →^{n₀} E` through a point: if `v ∈ E`, `y ∈ A₊ᵐ(v)` and `A₊ⁿ(y)` meets `E`, then
`n₀ + m + n + n₀` is a return time. -/
theorem mem_returnTimes_chain {F : Y × W → Y} {O : Set W} {E : Set Y} {n₀ : ℕ}
    (hn₀ : n₀ ∈ returnTimes F O E)
    {v y e : Y} (hv : v ∈ E) {m n : ℕ} (hy : y ∈ reachK F O m v) (he : e ∈ reachK F O n y)
    (heE : e ∈ E) : n₀ + m + n + n₀ ∈ returnTimes F O E := by
  refine ⟨by have := hn₀.1; omega, fun z hz w hw => ?_⟩
  have h1 : v ∈ reachK F O n₀ z := hn₀.2 z hz hv
  exact reachK_trans (reachK_trans (reachK_trans h1 hy) he) (hn₀.2 e heE hw)

namespace OrbitData

variable {F : Y × W → Y} {O : Set W} {M E : Set Y} {d : ℕ}

/-- `d > 0`. -/
theorem d_pos (h : OrbitData F O M E d) : 0 < d := by
  obtain ⟨n, hn⟩ := h.ret
  rw [h.gcd]
  exact setGcd_pos (returnTimes_isAddClosed F O E) hn hn.1

/-- `d` divides every return time. -/
theorem dvd (h : OrbitData F O M E d) {n : ℕ} (hn : n ∈ returnTimes F O E) : d ∣ n := by
  obtain ⟨n₀, hn₀⟩ := h.ret
  rw [h.gcd]
  exact setGcd_dvd (returnTimes_isAddClosed F O E) hn₀ hn₀.1 hn

/-- For `x ∈ M`, `closure A₊(x) = M`. -/
theorem closure_reach (h : OrbitData F O M E d) {x : Y} (hx : x ∈ M) :
    closure (reach F O x) = M :=
  ((proposition_7_2_3 h.cont h.ne h.minimal.1).1.1 h.minimal) x hx

/-- The set `{x : A₊ⁿ(x) ∩ E ≠ ∅}` is open. -/
theorem isOpen_meets (h : OrbitData F O M E d) (n : ℕ) :
    IsOpen {x | (reachK F O n x ∩ E).Nonempty} :=
  isOpen_setOf_reachK_inter h.cont n h.isOpen

/-- From every point of `M` the control model reaches `E`. -/
theorem exists_meets (h : OrbitData F O M E d) {x : Y} (hx : x ∈ M) :
    ∃ n, (reachK F O n x ∩ E).Nonempty := by
  obtain ⟨e, he⟩ := h.nonempty
  have he' : e ∈ closure (reach F O x) := by rw [h.closure_reach hx]; exact h.subset he
  obtain ⟨z, hzE, hz⟩ := mem_closure_iff.1 he' E h.isOpen he
  obtain ⟨n, hn⟩ := mem_reach_iff.1 hz
  exact ⟨n, z, hn, hzE⟩

/-- The classes cover `M`. -/
theorem iUnion_eq (h : OrbitData F O M E d) : ⋃ i, orbitClass F O M E d i = M := by
  refine Subset.antisymm (iUnion_subset fun i x hx => hx.1) fun x hx => ?_
  obtain ⟨n, hn⟩ := h.exists_meets hx
  exact mem_iUnion.2 ⟨-(n : ZMod d), hx, n, by ring, hn⟩

/-- `E ⊆ G₀`. -/
theorem subset_zero (h : OrbitData F O M E d) : E ⊆ orbitClass F O M E d 0 :=
  fun x hx => ⟨h.subset hx, 0, by simp, x, by simp, hx⟩

/-- **The classes are disjoint** (MT p. 159). -/
theorem disjoint (h : OrbitData F O M E d) {i j : ZMod d} (hij : i ≠ j) :
    Disjoint (orbitClass F O M E d i) (orbitClass F O M E d j) := by
  refine Set.disjoint_left.2 fun x hxi hxj => hij ?_
  obtain ⟨hxM, ni, hni, hmi⟩ := hxi
  obtain ⟨-, nj, hnj, hmj⟩ := hxj
  obtain ⟨n₀, hn₀⟩ := h.ret
  obtain ⟨v, hv⟩ := h.nonempty
  set O' := {y | (reachK F O ni y ∩ E).Nonempty} ∩ {y | (reachK F O nj y ∩ E).Nonempty}
  have hO' : IsOpen O' := (h.isOpen_meets ni).inter (h.isOpen_meets nj)
  have hxcl : x ∈ closure (reach F O v) := by rw [h.closure_reach (h.subset hv)]; exact hxM
  obtain ⟨y, ⟨⟨ei, hei, heiE⟩, ⟨ej, hej, hejE⟩⟩, hy⟩ := mem_closure_iff.1 hxcl O' hO' ⟨hmi, hmj⟩
  obtain ⟨m, hm⟩ := mem_reach_iff.1 hy
  have h1 := h.dvd (mem_returnTimes_chain hn₀ hv hm hei heiE)
  have h2 := h.dvd (mem_returnTimes_chain hn₀ hv hm hej hejE)
  rw [← ZMod.natCast_eq_zero_iff] at h1 h2
  push_cast at h1 h2
  linear_combination hni - hnj - h1 + h2

/-- The set `Uⱼ = ⋃_{n + j ≡ 0} {x : A₊ⁿ(x) ∩ E ≠ ∅}`, open, with `Gⱼ = M ∩ Uⱼ`. -/
def meetSet (F : Y × W → Y) (O : Set W) (E : Set Y) (d : ℕ) (j : ZMod d) : Set Y :=
  ⋃ n ∈ {n : ℕ | (n : ZMod d) + j = 0}, {x | (reachK F O n x ∩ E).Nonempty}

/-- `Uⱼ` is open. -/
theorem isOpen_meetSet (h : OrbitData F O M E d) (j : ZMod d) : IsOpen (meetSet F O E d j) :=
  isOpen_biUnion fun n _ => h.isOpen_meets n

omit [TopologicalSpace Y] in
/-- `Gⱼ = M ∩ Uⱼ`. -/
theorem orbitClass_eq (j : ZMod d) : orbitClass F O M E d j = M ∩ meetSet F O E d j := by
  ext x
  simp [orbitClass, meetSet]

/-- **The classes are closed** (MT p. 159): `Gⱼ = M ∖ ⋃_{i ≠ j} Uᵢ`. -/
theorem isClosed (h : OrbitData F O M E d) (j : ZMod d) : IsClosed (orbitClass F O M E d j) := by
  have heq : orbitClass F O M E d j = M ∩ (⋃ i ∈ {i | i ≠ j}, meetSet F O E d i)ᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, fun hU => ?_⟩
      obtain ⟨i, hij, hi⟩ := mem_iUnion₂.1 hU
      have hxi : x ∈ orbitClass F O M E d i := by rw [orbitClass_eq]; exact ⟨hx.1, hi⟩
      exact Set.disjoint_left.1 (h.disjoint hij) hxi hx
    · rintro ⟨hxM, hU⟩
      have : x ∈ ⋃ i, orbitClass F O M E d i := by rw [h.iUnion_eq]; exact hxM
      obtain ⟨i, hi⟩ := mem_iUnion.1 this
      by_cases hij : i = j
      · rwa [← hij]
      · rw [orbitClass_eq] at hi
        exact absurd (mem_iUnion₂.2 ⟨i, hij, hi.2⟩) hU
  rw [heq]
  exact h.minimal.2.1.inter (isOpen_biUnion fun i _ => h.isOpen_meetSet i).isClosed_compl

/-- **One step moves `Gᵢ` into `Gᵢ₊₁`** (MT p. 159). -/
theorem step (h : OrbitData F O M E d) {i : ZMod d} {x : Y} (hx : x ∈ orbitClass F O M E d i)
    {w : W} (hw : w ∈ O) : F (x, w) ∈ orbitClass F O M E d (i + 1) := by
  have hyM : F (x, w) ∈ M := isCMInvariant_iff_step.1 h.minimal.2.2.1 x hx.1 w hw
  have : F (x, w) ∈ ⋃ j, orbitClass F O M E d j := by rw [h.iUnion_eq]; exact hyM
  obtain ⟨j, hj⟩ := mem_iUnion.1 this
  have hxj : x ∈ orbitClass F O M E d (j - 1) := by
    obtain ⟨-, n, hn, z, hz, hzE⟩ := hj
    refine ⟨hx.1, n + 1, ?_, z, (mem_reachK_succ' F O n x z).2 ⟨w, hw, hz⟩, hzE⟩
    push_cast
    linear_combination hn
  by_cases hij : j - 1 = i
  · rwa [show j = i + 1 by rw [← hij]; ring] at hj
  · exact absurd hx (Set.disjoint_left.1 (h.disjoint hij) hxj)

/-- The classes form a periodic orbit of period `d`. -/
theorem isPeriodicOrbit (h : OrbitData F O M E d) :
    IsPeriodicOrbit F O d (orbitClass F O M E d) :=
  ⟨h.isClosed, fun _ _ hij => h.disjoint hij, fun _ _ hx _ hw => h.step hx hw⟩

/-- **Uniqueness** (MT p. 158): if `H` is a periodic orbit of period `d' ≥ 1` with union `M`,
then `d' ∣ d` (`d' ≥ 1` is not needed), and there is `a` with `Gⱼ ⊆ H_{a + j}` for every `j`. -/
theorem unique (h : OrbitData F O M E d) {d' : ℕ} {H : ZMod d' → Set Y}
    (hH : IsPeriodicOrbit F O d' H) (hHM : ⋃ i, H i = M) :
    d' ∣ d ∧ ∃ a : ZMod d', ∀ j : ZMod d, orbitClass F O M E d j ⊆ H (a + (j.val : ZMod d')) := by
  have hd := h.d_pos
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨e₀, he₀⟩ := h.nonempty
  have he₀M : e₀ ∈ ⋃ i, H i := by rw [hHM]; exact h.subset he₀
  obtain ⟨a, ha⟩ := mem_iUnion.1 he₀M
  have hI : ∀ n ∈ returnTimes F O E, ((n : ℕ) : ZMod d') = 0 := by
    intro n hn
    have h1 : e₀ ∈ H (a + n) := hH.reachK_subset n ha (hn.2 e₀ he₀ he₀)
    by_contra hne
    exact Set.disjoint_left.1 (hH.disjoint (a + n) a (by intro h'; exact hne (by
      linear_combination h'))) h1 ha
  have hdvd : d' ∣ d := by
    obtain ⟨n₀, hn₀⟩ := h.ret
    rw [h.gcd]
    exact dvd_setGcd (returnTimes_isAddClosed F O E) hn₀ hn₀.1 fun n hn =>
      (ZMod.natCast_eq_zero_iff n d').1 (hI n hn)
  have hEa : E ⊆ H a := by
    obtain ⟨n₀, hn₀⟩ := h.ret
    intro z hz
    have := hH.reachK_subset n₀ ha (hn₀.2 e₀ he₀ hz)
    rwa [hI n₀ hn₀, add_zero] at this
  refine ⟨hdvd, a, fun j x hx => ?_⟩
  obtain ⟨hxM, n, hn, z, hz, hzE⟩ := hx
  have hxH : x ∈ ⋃ i, H i := by rw [hHM]; exact hxM
  obtain ⟨b, hb⟩ := mem_iUnion.1 hxH
  have hzb : z ∈ H (b + n) := hH.reachK_subset n hb hz
  have hab : b + n = a := by
    by_contra hne
    exact Set.disjoint_left.1 (hH.disjoint _ _ hne) hzb (hEa hzE)
  have hnj : ((n + j.val : ℕ) : ZMod d') = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    refine dvd_trans hdvd ((ZMod.natCast_eq_zero_iff _ d).1 ?_)
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hn
  push_cast at hnj
  have : b = a + (j.val : ZMod d') := by linear_combination hab - hnj
  rwa [← this]

end OrbitData

/-- **Theorem 7.3.3** (MT p. 158), from a set `E` as in Lemma 7.3.2: the classes `Gᵢ` of (7.18)
form a periodic orbit of period `d = g.c.d. I` whose union is `M`, `d` is the period of `M`, and
every periodic orbit `H` with union `M` has period dividing `d`, each `Gⱼ` lying in one `Hᵢ`. -/
theorem theorem_7_3_3_of_orbitData {F : Y × W → Y} {O : Set W} {M E : Set Y} {d : ℕ}
    (h : OrbitData F O M E d) :
    IsPeriodicOrbit F O d (orbitClass F O M E d) ∧ ⋃ i, orbitClass F O M E d i = M ∧
      IsPeriodOf F O M d ∧
      ∀ d' (H : ZMod d' → Set Y), 0 < d' → IsPeriodicOrbit F O d' H → ⋃ i, H i = M →
        d' ∣ d ∧ ∃ a : ZMod d', ∀ j : ZMod d,
          orbitClass F O M E d j ⊆ H (a + (j.val : ZMod d')) :=
  ⟨h.isPeriodicOrbit, h.iUnion_eq, ⟨h.d_pos, ⟨_, h.isPeriodicOrbit, h.iUnion_eq⟩,
    fun _ _ _ hH hHM => (h.unique hH hHM).1⟩, fun _ _ _ hH hHM => h.unique hH hHM⟩

/-- **Theorem 7.3.3**, uniqueness in the book's form: each `Hᵢ` of a periodic orbit with union `M`
is the union of the classes `Gⱼ` it contains. -/
theorem theorem_7_3_3_union {F : Y × W → Y} {O : Set W} {M E : Set Y} {d : ℕ}
    (h : OrbitData F O M E d) {d' : ℕ} {H : ZMod d' → Set Y}
    (hH : IsPeriodicOrbit F O d' H) (hHM : ⋃ i, H i = M) (i : ZMod d') :
    H i = ⋃ j ∈ {j | orbitClass F O M E d j ⊆ H i}, orbitClass F O M E d j := by
  obtain ⟨-, a, ha⟩ := h.unique hH hHM
  refine Subset.antisymm (fun x hx => ?_) (iUnion₂_subset fun j hj => hj)
  have hxM : x ∈ ⋃ i, H i := mem_iUnion.2 ⟨i, hx⟩
  rw [hHM, ← h.iUnion_eq] at hxM
  obtain ⟨j, hj⟩ := mem_iUnion.1 hxM
  have hji : a + (j.val : ZMod d') = i := by
    by_contra hne
    exact Set.disjoint_left.1 (hH.disjoint _ _ hne) (ha j hj) hx
  exact mem_iUnion₂.2 ⟨j, (hji ▸ ha j : orbitClass F O M E d j ⊆ H i), hj⟩

/-- A preconnected set covered by finitely many disjoint closed sets `G i` lies in the one it
meets. -/
theorem subset_of_isPreconnected_of_closed_partition {d : ℕ} [NeZero d] {G : ZMod d → Set Y}
    (hc : ∀ i, IsClosed (G i)) (hd : ∀ i j, i ≠ j → Disjoint (G i) (G j)) {s : Set Y}
    (hs : IsPreconnected s) (hsG : s ⊆ ⋃ i, G i) {x : Y} {j : ZMod d} (hx : x ∈ s)
    (hxj : x ∈ G j) : s ⊆ G j := by
  have hv : IsClosed (⋃ i ∈ {i | i ≠ j}, G i) :=
    (Set.toFinite _).isClosed_biUnion fun i _ => hc i
  have hcov : s ⊆ G j ∪ ⋃ i ∈ {i | i ≠ j}, G i := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hsG hy)
    by_cases hij : i = j
    · exact Or.inl (hij ▸ hi)
    · exact Or.inr (mem_iUnion₂.2 ⟨i, hij, hi⟩)
  have hdisj : s ∩ (G j ∩ ⋃ i ∈ {i | i ≠ j}, G i) = ∅ := by
    refine eq_empty_of_forall_notMem fun y ⟨_, hyj, hyv⟩ => ?_
    obtain ⟨i, hij, hi⟩ := mem_iUnion₂.1 hyv
    exact Set.disjoint_left.1 (hd i j hij) hi hyj
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hs _ _ (hc j) hv hcov hdisj with h | h
  · exact h
  · obtain ⟨i, hij, hi⟩ := mem_iUnion₂.1 (h hx)
    exact absurd hxj (Set.disjoint_left.1 (hd i j hij) hi)

/-- On a periodic orbit with non-empty union, every class is non-empty (if `O ≠ ∅`). -/
theorem IsPeriodicOrbit.nonempty {F : Y × W → Y} {O : Set W} (hO : O.Nonempty) {d : ℕ}
    [NeZero d] {H : ZMod d → Set Y} (hH : IsPeriodicOrbit F O d H) (hne : (⋃ i, H i).Nonempty)
    (i : ZMod d) : (H i).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨a, ha⟩ := mem_iUnion.1 hx
  obtain ⟨y, hy⟩ := reachK_nonempty (F := F) hO (i - a).val x
  have := hH.reachK_subset (i - a).val ha hy
  rw [ZMod.natCast_zmod_val, add_sub_cancel] at this
  exact ⟨y, this⟩

/-- **A connected minimal set is aperiodic** (MT Proposition 7.3.4, p. 160, the "if" half of
"aperiodic iff connected"; it needs no connectedness of the control set). -/
theorem isPeriodOf_one_of_isConnected {F : Y × W → Y} {O : Set W} (hO : O.Nonempty) {M : Set Y}
    (hM : IsMinimal F O M) (hconn : IsConnected M) : IsPeriodOf F O M 1 := by
  refine ⟨one_pos, ⟨fun _ => M, ⟨fun _ => hM.2.1, fun i j hij => absurd (Subsingleton.elim i j)
    hij, fun _ x hx w hw => isCMInvariant_iff_step.1 hM.2.2.1 x hx w hw⟩, iUnion_const M⟩,
    fun d' H hd' hH hHM => ?_⟩
  by_contra hne
  have hd2 : 1 < d' := by
    rcases Nat.lt_or_ge 1 d' with h | h
    · exact h
    · exact absurd (by rw [show d' = 1 by omega]) hne
  have : NeZero d' := ⟨hd'.ne'⟩
  have : Fact (1 < d') := ⟨hd2⟩
  have hne' : (⋃ i, H i).Nonempty := by rw [hHM]; exact hM.1
  obtain ⟨x, hx⟩ := hH.nonempty hO hne' 0
  have hsub := subset_of_isPreconnected_of_closed_partition hH.isClosed hH.disjoint
    hconn.isPreconnected hHM.symm.subset (by rw [← hHM]; exact mem_iUnion.2 ⟨0, hx⟩) hx
  obtain ⟨y, hy⟩ := hH.nonempty hO hne' 1
  have hyM : y ∈ M := by rw [← hHM]; exact mem_iUnion.2 ⟨1, hy⟩
  exact Set.disjoint_left.1 (hH.disjoint 1 0 one_ne_zero) hy (hsub hyM)

/-! ### Connected classes -/

/-- The control maps are jointly continuous when `F` is. -/
theorem continuous_controlMap_joint [TopologicalSpace W] {F : Y × W → Y} (hF : Continuous F)
    (k : ℕ) : Continuous fun p : Y × (Fin k → W) => controlMap F k p.1 p.2 := by
  induction k with
  | zero => exact continuous_fst
  | succ k ih =>
    have hi : Continuous fun p : Y × (Fin (k + 1) → W) => (p.1, Fin.init p.2) :=
      continuous_fst.prodMk ((continuous_pi fun i => continuous_apply _).comp continuous_snd)
    exact hF.comp ((ih.comp hi).prodMk ((continuous_apply _).comp continuous_snd))

omit [TopologicalSpace Y] in
/-- `A₊ᵏ(S)` is the image of `S × Oᵏ` under the control map. -/
theorem reachKSet_eq_image (F : Y × W → Y) (O : Set W) (k : ℕ) (S : Set Y) :
    reachKSet F O k S =
      (fun p : Y × (Fin k → W) => controlMap F k p.1 p.2) '' (S ×ˢ {u | ∀ i, u i ∈ O}) := by
  ext z
  simp only [reachKSet, reachK, mem_iUnion, mem_ofPred_eq, exists_prop, mem_image, mem_prod,
    Prod.exists]
  constructor
  · rintro ⟨x, hx, u, hu, rfl⟩
    exact ⟨x, u, ⟨hx, hu⟩, rfl⟩
  · rintro ⟨x, u, ⟨hx, hu⟩, rfl⟩
    exact ⟨x, hx, u, hu, rfl⟩

/-- `Oᵏ` is preconnected when `O` is. -/
theorem isPreconnected_controls [TopologicalSpace W] {O : Set W} (hO : IsPreconnected O)
    (k : ℕ) : IsPreconnected {u : Fin k → W | ∀ i, u i ∈ O} := by
  have : {u : Fin k → W | ∀ i, u i ∈ O} = Set.pi univ fun _ => O := by ext u; simp
  rw [this]
  exact isPreconnected_univ_pi fun _ => hO

namespace OrbitData

variable {F : Y × W → Y} {O : Set W} {M E : Set Y} {d : ℕ}

/-- **The classes are connected** (MT Proposition 7.3.4, p. 160): if `F` is jointly continuous and
`O` is connected, each `Gⱼ` is the closure of `A₊ʲ(⋃_{q ≥ N₀} A₊^{qd}(v))` for a point `v ∈ E`,
a connected set. -/
theorem isConnected_class [TopologicalSpace W] (h : OrbitData F O M E d) (hF : Continuous F)
    (hOc : IsPreconnected O) (j : ZMod d) : IsConnected (orbitClass F O M E d j) := by
  have hd := h.d_pos
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨v, hv⟩ := h.nonempty
  obtain ⟨n₀, hn₀⟩ := h.ret
  obtain ⟨N₀, hN₀⟩ := lemma_D_7_4 (returnTimes_isAddClosed F O E) hn₀ hn₀.1
  rw [← h.gcd] at hN₀
  have hv0 : v ∈ orbitClass F O M E d 0 := h.subset_zero hv
  have hcm : ∀ n x, Continuous fun u : Fin n → W => controlMap F n x u := fun n x =>
    (continuous_controlMap_joint hF n).comp (continuous_const.prodMk continuous_id)
  set S0 : Set Y := ⋃ q ∈ Ici N₀, reachK F O (q * d) v with hS0
  have hS0c : IsPreconnected S0 := by
    have : S0 = ⋃₀ ((fun q => reachK F O (q * d) v) '' Ici N₀) := by rw [sUnion_image]
    rw [this]
    refine isPreconnected_sUnion v _ ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact (hN₀ q hq).2 v hv hv
    · rintro _ ⟨q, -, rfl⟩
      change IsPreconnected (reachK F O (q * d) v)
      rw [reachK_eq_image]
      exact (isPreconnected_controls hOc _).image _ (hcm _ v).continuousOn
  set S : Set Y := reachKSet F O j.val S0 with hS
  have hSc : IsPreconnected S := by
    rw [hS, reachKSet_eq_image]
    exact (hS0c.prod (isPreconnected_controls hOc _)).image _
      (continuous_controlMap_joint hF _).continuousOn
  have hSG : S ⊆ orbitClass F O M E d j := by
    intro z hz
    obtain ⟨y, hy, hz⟩ := mem_iUnion₂.1 hz
    obtain ⟨q, -, hy⟩ := mem_iUnion₂.1 hy
    have := h.isPeriodicOrbit.reachK_subset _ hv0 (reachK_trans hy hz)
    rwa [zero_add, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add,
      ZMod.natCast_zmod_val] at this
  have hSne : S.Nonempty := by
    obtain ⟨y, hy⟩ := reachK_nonempty (F := F) h.ne j.val v
    refine ⟨y, mem_iUnion₂.2 ⟨v, mem_iUnion₂.2 ⟨N₀, mem_Ici.2 le_rfl, ?_⟩, hy⟩⟩
    exact (hN₀ N₀ le_rfl).2 v hv hv
  have hclos : orbitClass F O M E d j ⊆ closure S := by
    intro y hy
    rw [mem_closure_iff]
    intro U hU hyU
    set V : Set Y := ⋃ i ∈ {i | i ≠ j}, orbitClass F O M E d i
    have hV : IsClosed V := (Set.toFinite _).isClosed_biUnion fun i _ => h.isClosed i
    have hyV : y ∉ V := fun hyV => by
      obtain ⟨i, hij, hi⟩ := mem_iUnion₂.1 hyV
      exact Set.disjoint_left.1 (h.disjoint hij) hi hy
    obtain ⟨z₀, hz₀⟩ := reachK_nonempty (F := F) h.ne (N₀ * d) v
    have hz₀M : z₀ ∈ M := h.minimal.2.2.1.reachK_subset (h.subset hv) _ hz₀
    have hycl : y ∈ closure (reach F O z₀) := by rw [h.closure_reach hz₀M]; exact hy.1
    obtain ⟨p, ⟨hpU, hpV⟩, hp⟩ := mem_closure_iff.1 hycl (U ∩ Vᶜ) (hU.inter hV.isOpen_compl)
      ⟨hyU, hyV⟩
    obtain ⟨m, hm⟩ := mem_reach_iff.1 hp
    have hpv : p ∈ reachK F O (N₀ * d + m) v := reachK_trans hz₀ hm
    have hpM : p ∈ M := h.minimal.2.2.1.reachK_subset (h.subset hv) _ hpv
    have hpG := h.isPeriodicOrbit.reachK_subset _ hv0 hpv
    rw [zero_add] at hpG
    have hcls : ((N₀ * d + m : ℕ) : ZMod d) = j := by
      by_contra hne
      exact hpV (mem_iUnion₂.2 ⟨_, hne, hpG⟩)
    refine ⟨p, hpU, ?_⟩
    set n := N₀ * d + m
    have hr : n % d = j.val := by rw [← hcls, ZMod.val_natCast]
    have hq : N₀ ≤ n / d := (Nat.le_div_iff_mul_le hd).2 (Nat.le_add_right _ _)
    have hsplit : n = n / d * d + j.val := by rw [← hr, Nat.div_add_mod']
    rw [hsplit, reachK_add] at hpv
    obtain ⟨y', hy', hpy'⟩ := mem_iUnion₂.1 hpv
    exact mem_iUnion₂.2 ⟨y', mem_iUnion₂.2 ⟨n / d, mem_Ici.2 hq, hy'⟩, hpy'⟩
  have heq : orbitClass F O M E d j = closure S :=
    Subset.antisymm hclos (closure_minimal hSG (h.isClosed j))
  rw [heq]
  exact ⟨hSne.mono subset_closure, hSc.closure⟩

/-- **The classes are the connected components of `M`** (MT Proposition 7.3.4, p. 160). -/
theorem connectedComponentIn_eq [TopologicalSpace W] (h : OrbitData F O M E d)
    (hF : Continuous F) (hOc : IsPreconnected O) {j : ZMod d} {x : Y}
    (hx : x ∈ orbitClass F O M E d j) : connectedComponentIn M x = orbitClass F O M E d j := by
  have : NeZero d := ⟨h.d_pos.ne'⟩
  refine Subset.antisymm ?_
    ((h.isConnected_class hF hOc j).isPreconnected.subset_connectedComponentIn hx
      fun y hy => hy.1)
  exact subset_of_isPreconnected_of_closed_partition h.isClosed (fun i j hij => h.disjoint hij)
    isPreconnected_connectedComponentIn
    ((connectedComponentIn_subset M x).trans h.iUnion_eq.symm.subset)
    (mem_connectedComponentIn hx.1) hx

/-- **An aperiodic minimal set is connected** when `O` is connected (MT Proposition 7.3.4,
p. 160). -/
theorem isConnected_of_isPeriodOf_one [TopologicalSpace W] (h : OrbitData F O M E d)
    (hF : Continuous F) (hOc : IsPreconnected O) (h1 : IsPeriodOf F O M 1) : IsConnected M := by
  have hd1 : d = 1 := Nat.dvd_one.1 (h1.2.2 d _ h.d_pos h.isPeriodicOrbit h.iUnion_eq)
  subst hd1
  have : M = orbitClass F O M E 1 0 := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => hx.1
    have hx' : x ∈ ⋃ i, orbitClass F O M E 1 i := by rw [h.iUnion_eq]; exact hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx'
    rwa [Subsingleton.elim i 0] at hi
  rw [this]
  exact h.isConnected_class hF hOc 0

/-- Shrinking `E` to an open `E ∩ N`, `N` open meeting `E`, keeps the hypotheses (with the
g.c.d. of the new return times). -/
theorem shrink (h : OrbitData F O M E d) {N : Set Y} (hN : IsOpen N) (hNE : (E ∩ N).Nonempty) :
    OrbitData F O M (E ∩ N) (setGcd (returnTimes F O (E ∩ N))) := by
  obtain ⟨n₀, hn₀⟩ := h.ret
  exact ⟨h.cont, h.ne, h.minimal, h.isOpen.inter hN, hNE, inter_subset_left.trans h.subset,
    ⟨n₀, hn₀.1, hn₀.2.mono inter_subset_left inter_subset_left⟩, rfl⟩

end OrbitData

/-! ### Propositions 7.3.1, Lemma 7.3.2, Theorem 7.3.3 and Proposition 7.3.4 -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
/-- `Oᵏ` is open when `O` is. -/
theorem isOpen_controls {O : Set W} (hO : IsOpen O) (k : ℕ) :
    IsOpen {u : Fin k → W | ∀ i, u i ∈ O} := by
  have : {u : Fin k → W | ∀ i, u i ∈ O} = Set.pi univ fun _ => O := by ext u; simp
  rw [this]
  exact isOpen_set_pi finite_univ fun _ _ => hO

/-- **Proposition 7.3.1** (MT p. 158): if CM(F) satisfies the rank condition (CM3) (forward
accessibility), with `F` of class `C¹` and `O` open, every `x` has an open neighbourhood `B` with
`B →ᵏ C` for some non-empty open `C` and `k ≥ 1`. -/
theorem proposition_7_3_1 {F : X × W → X} (hF : ContDiff ℝ 1 F) {O : Set W} (hO : IsOpen O)
    (h : RankCondition F O) (x : X) :
    ∃ B C : Set X, ∃ k, 0 < k ∧ IsOpen B ∧ x ∈ B ∧ IsOpen C ∧ C.Nonempty ∧
      IsKAccessible F O k B C := by
  obtain ⟨k, u, hk⟩ := h x
  have hG := (contDiff_controlMap hF k).contDiffAt (x := (x, u))
  have hsurj := hk.2.2
  rw [← fderiv_controlMap_comp_inr hF k x u] at hsurj
  have hV : (univ ×ˢ {v : Fin k → W | ∀ i, v i ∈ O}) ∈ 𝓝 (x, u) :=
    (isOpen_univ.prod (isOpen_controls hO k)).mem_nhds ⟨mem_univ _, hk.2.1⟩
  obtain ⟨B, C, hB, hxB, hC, hCne, hBC⟩ := exists_uniform_reach hG hsurj hV
  refine ⟨B, C, k, hk.1, hB, hxB, hC, hCne, fun y hy z hz => ?_⟩
  obtain ⟨v, hv, rfl⟩ := hBC y hy z hz
  exact ⟨v, hv.2, rfl⟩

/-- **Lemma 7.3.2** (MT p. 158): under the rank condition (forward accessibility), every minimal
set `M` contains a non-empty open `E` with `E →ⁿ E` for some `n ≥ 1`. -/
theorem lemma_7_3_2 {F : X × W → X} (hF : ContDiff ℝ 1 F) {O : Set W} (hO : IsOpen O)
    (h : RankCondition F O) {M : Set X} (hM : IsMinimal F O M) :
    ∃ E : Set X, IsOpen E ∧ E.Nonempty ∧ E ⊆ M ∧ ∃ n, 0 < n ∧ IsKAccessible F O n E E := by
  have hFx : ∀ w ∈ O, Continuous fun x => F (x, w) := fun w _ =>
    hF.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨x₀, hx₀⟩ := hM.1
  have hOne : O.Nonempty := by
    obtain ⟨k, u, hk⟩ := h x₀
    exact ⟨u ⟨0, hk.1⟩, hk.2.1 _⟩
  obtain ⟨B, C, k, hk, hB, hxB, hC, ⟨c, hc⟩, hBC⟩ := proposition_7_3_1 hF hO h x₀
  have hCM : C ⊆ M := (hBC x₀ hxB).trans (hM.2.2.1.reachK_subset hx₀ k)
  have hcl : closure (reach F O c) = M :=
    ((proposition_7_2_3 hFx hOne hM.1).1.1 hM) c (hCM hc)
  have hx₀cl : x₀ ∈ closure (reach F O c) := by rw [hcl]; exact hx₀
  obtain ⟨z, hzB, hz⟩ := mem_closure_iff.1 hx₀cl B hB hxB
  obtain ⟨m, v, hv, rfl⟩ := mem_reach_iff.1 hz
  refine ⟨C ∩ (fun x => controlMap F m x v) ⁻¹' B,
    hC.inter (hB.preimage (controlMap_continuous hFx m hv)), ⟨c, hc, hzB⟩,
    inter_subset_left.trans hCM, m + k, by omega, fun y hy z hz => ?_⟩
  have h1 : controlMap F m y v ∈ reachK F O m y := ⟨v, hv, rfl⟩
  exact reachK_trans h1 (hBC _ hy.2 (inter_subset_left hz))

/-- Lemma 7.3.2 gives the data of Theorem 7.3.3. -/
theorem exists_orbitData {F : X × W → X} (hF : ContDiff ℝ 1 F) {O : Set W} (hO : IsOpen O)
    (h : RankCondition F O) {M : Set X} (hM : IsMinimal F O M) :
    ∃ E : Set X, OrbitData F O M E (setGcd (returnTimes F O E)) := by
  obtain ⟨E, hE, hEne, hEM, n, hn, hnE⟩ := lemma_7_3_2 hF hO h hM
  have hOne : O.Nonempty := by
    obtain ⟨x₀, -⟩ := hM.1
    obtain ⟨k, u, hk⟩ := h x₀
    exact ⟨u ⟨0, hk.1⟩, hk.2.1 _⟩
  exact ⟨E, ⟨fun w _ => hF.continuous.comp (continuous_id.prodMk continuous_const), hOne, hM,
    hE, hEne, hEM, ⟨n, hn, hnE⟩, rfl⟩⟩

/-- **Theorem 7.3.3** (MT p. 158): if `F` is `C¹`, `O` is open and CM(F) satisfies the rank
condition (forward accessibility), every minimal set `M` has a period `d ≥ 1` and is the union
of a periodic orbit `G` of period `d`; every periodic orbit `H` with union `M` has period dividing
`d`, and each `Hᵢ` is a union of sets `Gⱼ`. -/
theorem theorem_7_3_3 {F : X × W → X} (hF : ContDiff ℝ 1 F) {O : Set W} (hO : IsOpen O)
    (h : RankCondition F O) {M : Set X} (hM : IsMinimal F O M) :
    ∃ d, IsPeriodOf F O M d ∧ ∃ G : ZMod d → Set X, IsPeriodicOrbit F O d G ∧ ⋃ i, G i = M ∧
      ∀ d' (H : ZMod d' → Set X), 0 < d' → IsPeriodicOrbit F O d' H → ⋃ i, H i = M →
        d' ∣ d ∧ ∀ i, H i = ⋃ j ∈ {j | G j ⊆ H i}, G j := by
  obtain ⟨E, hE⟩ := exists_orbitData hF hO h hM
  obtain ⟨hG, hGM, hper, -⟩ := theorem_7_3_3_of_orbitData hE
  exact ⟨_, hper, _, hG, hGM, fun d' H _ hH hHM =>
    ⟨(hE.unique hH hHM).1, theorem_7_3_3_union hE hH hHM⟩⟩

/-- **Proposition 7.3.4** (MT p. 160): if moreover the control set `O` is connected, the sets of
the periodic orbit constructed in Theorem 7.3.3 are connected, and each is the connected component
in `M` of each of its points; and `M` is aperiodic iff it is connected. -/
theorem proposition_7_3_4 {F : X × W → X} (hF : ContDiff ℝ 1 F) {O : Set W} (hO : IsOpen O)
    (hOc : IsPreconnected O) (h : RankCondition F O) {M : Set X} (hM : IsMinimal F O M) :
    ∃ (E : Set X) (d : ℕ), OrbitData F O M E d ∧ IsPeriodOf F O M d ∧
      (∀ j, IsConnected (orbitClass F O M E d j) ∧
        ∀ x ∈ orbitClass F O M E d j, connectedComponentIn M x = orbitClass F O M E d j) ∧
      (IsPeriodOf F O M 1 ↔ IsConnected M) := by
  obtain ⟨E, hE⟩ := exists_orbitData hF hO h hM
  refine ⟨E, _, hE, (theorem_7_3_3_of_orbitData hE).2.2.1, fun j =>
    ⟨hE.isConnected_class hF.continuous hOc j, fun x hx =>
      hE.connectedComponentIn_eq hF.continuous hOc hx⟩, ⟨fun h1 =>
      hE.isConnected_of_isPeriodOf_one hF.continuous hOc h1, fun hc =>
      isPeriodOf_one_of_isConnected hE.ne hM hc⟩⟩

/-- `IsPeriodOf` exists under the rank condition. -/
theorem exists_isPeriodOf {F : X × W → X} (hF : ContDiff ℝ 1 F) {O : Set W} (hO : IsOpen O)
    (h : RankCondition F O) {M : Set X} (hM : IsMinimal F O M) : ∃ d, IsPeriodOf F O M d := by
  obtain ⟨d, hd, -⟩ := theorem_7_3_3 hF hO h hM
  exact ⟨d, hd⟩

end MeynTweedie.InvarianceTightness

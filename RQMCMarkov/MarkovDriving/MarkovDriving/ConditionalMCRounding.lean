/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.ConditionalMC

/-!
# Rounding the expected transition counts to balanced integer counts (post #3)

Post #3's conditional MC: "we want to get counts `n_ij = T π_i p_ij`, rounded so that every state
is entered as often as it is left (allowing for the first and last states)", then sample a path
with those counts. Reading: `π` is a stationary distribution of the stochastic matrix `P`, the
real matrix `x_ij = T π_i p_ij` (`expectedCounts`) is to be rounded entrywise (`⌊x_ij⌋ ≤ n_ij ≤
⌈x_ij⌉`) to an integer matrix with equal row and column sums (a circulation), and a path is
then a closed path realising `n`.

## Main results

* `IsCirculation`, `netFlow`, `sum_netFlow_eq_cut` (the cut identity).
* `isCirculation_expectedCounts`, `sum_expectedCounts`: `x_ij = T π_i p_ij` is a circulation
  (row `i` and column `i` both sum to `T π_i`) with total `T`.
* `exists_cycle_direction`: a fractional entry of a real circulation lies on a cycle of
  fractional entries (proved by a cut argument on the states reachable through fractional arcs).
* `exists_int_circulation_rounding`: **circulation rounding** — every real circulation has an
  integer circulation rounding `⌊x_ij⌋ ≤ n_ij ≤ ⌈x_ij⌉` (cycle cancelling on the fractional
  entries).
* `exists_rounding_expectedCounts`: post #3's rounding exists, with `|n_ij − T π_i p_ij| < 1` and
  `Σ ⌊x_ij⌋ ≤ Σ n_ij ≤ Σ ⌈x_ij⌉`.
* `exists_closed_path_of_rounding`: for irreducible `P` and `T π_i p_ij ≥ 1` on the support of
  `P`, the rounded counts have the support of `P`, are balanced at every state, and are realised
  by a closed path from any `x₀` (Euler, `exists_path_of_balanced`).
* `conditionalMC_wellDefined`: the conditioning event of post #3's conditional MC then has
  positive MC probability, and the conditional law is uniform over the paths with the counts.

**Correction.** The total of the rounded circulation cannot always be made `⌊T⌋` or `⌈T⌉`, so the
balanced path may have to have length `Σ n ≠ T`: `not_exists_rounding_flipChain_total_three`
(the flip chain `[[0,1],[1,0]]`, `π = (1/2, 1/2)`, `T = 3`: every integer circulation has
`n_01 = n_10`, so an even total). The post's "allowing for the first and last states" (open
paths, counts balanced from the first to the last state) is what can repair the length; that
version is `ConditionalMCRoundingOpen`. The BEST count of the paths is not formalised.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S : Type*} [Fintype S]

/-! ### Circulations -/

/-- Net outflow `Σ_j z v j − Σ_j z j v` of a real matrix at the state `v`. -/
def netFlow (z : S → S → ℝ) (v : S) : ℝ := ∑ j, z v j - ∑ j, z j v

/-- A real matrix is a **circulation** when every row sum equals the column sum ("every state is
entered as often as it is left"). -/
def IsCirculation (z : S → S → ℝ) : Prop := ∀ v, ∑ j, z v j = ∑ j, z j v

/-- Circulations are the matrices with zero net outflow everywhere. -/
theorem isCirculation_iff_netFlow (z : S → S → ℝ) : IsCirculation z ↔ ∀ v, netFlow z v = 0 :=
  forall_congr' fun _ ↦ sub_eq_zero.symm

/-- `netFlow` is additive. -/
theorem netFlow_add (z z' : S → S → ℝ) (v : S) :
    netFlow (fun i j ↦ z i j + z' i j) v = netFlow z v + netFlow z' v := by
  unfold netFlow
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- `netFlow` is subtractive. -/
theorem netFlow_sub (z z' : S → S → ℝ) (v : S) :
    netFlow (fun i j ↦ z i j - z' i j) v = netFlow z v - netFlow z' v := by
  unfold netFlow
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

/-- `netFlow` is homogeneous. -/
theorem netFlow_mul (t : ℝ) (z : S → S → ℝ) (v : S) :
    netFlow (fun i j ↦ t * z i j) v = t * netFlow z v := by
  unfold netFlow
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

variable [DecidableEq S]

/-- The net outflow of a single arc `a → b` carrying `c`. -/
theorem netFlow_single (a b : S) (c : ℝ) (v : S) :
    netFlow (fun i j ↦ if i = a ∧ j = b then c else 0) v =
      (if v = a then c else 0) - if v = b then c else 0 := by
  unfold netFlow
  congr 1
  · by_cases hva : v = a
    · simp only [hva, true_and, ↓reduceIte]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
    · simp only [hva, false_and, ↓reduceIte, Finset.sum_const_zero]
  · by_cases hvb : v = b
    · simp only [hvb, and_true, ↓reduceIte]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
    · simp only [hvb, and_false, ↓reduceIte, Finset.sum_const_zero]

/-- **The cut identity**: the total net outflow of a set `R` of states is the flow on arcs
leaving `R` minus the flow on arcs entering `R`. -/
theorem sum_netFlow_eq_cut (z : S → S → ℝ) (R : Finset S) :
    ∑ v ∈ R, netFlow z v = ∑ v ∈ R, ∑ j ∈ Rᶜ, z v j - ∑ v ∈ R, ∑ j ∈ Rᶜ, z j v := by
  unfold netFlow
  rw [Finset.sum_sub_distrib]
  have h1 : ∀ v, ∑ j, z v j = ∑ j ∈ R, z v j + ∑ j ∈ Rᶜ, z v j := fun v ↦
    (Finset.sum_add_sum_compl R _).symm
  have h2 : ∀ v, ∑ j, z j v = ∑ j ∈ R, z j v + ∑ j ∈ Rᶜ, z j v := fun v ↦
    (Finset.sum_add_sum_compl R _).symm
  simp only [h1, h2, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := R) (t := R) (f := fun v j ↦ z v j)]
  ring

/-! ### Integer points and the fractional-arc graph -/

/-- The integers inside `ℝ`, as an additive subgroup. -/
noncomputable abbrev intLattice : AddSubgroup ℝ := (Int.castAddHom ℝ).range

/-- Membership in `intLattice`. -/
theorem mem_intLattice {z : ℝ} : z ∈ intLattice ↔ ∃ k : ℤ, (k : ℝ) = z := by
  rw [AddMonoidHom.mem_range]
  rfl

/-- Integers lie in `intLattice`. -/
theorem intCast_mem_intLattice (k : ℤ) : (k : ℝ) ∈ intLattice := mem_intLattice.2 ⟨k, rfl⟩

/-- Adjacency through **fractional arcs other than `e`**, in either direction. -/
def fracAdj (y : S → S → ℝ) (e : S × S) (u v : S) : Prop :=
  ((u, v) ≠ e ∧ y u v ∉ intLattice) ∨ ((v, u) ≠ e ∧ y v u ∉ intLattice)

/-- A chain of fractional arcs from `u` to `w` carries a flow with net outflow `1{u} − 1{w}`,
supported on fractional arcs other than `e`. -/
theorem exists_pathFlow (y : S → S → ℝ) (e : S × S) {u w : S}
    (h : Relation.ReflTransGen (fracAdj y e) u w) :
    ∃ d : S → S → ℝ, (∀ v, netFlow d v = (if v = u then 1 else 0) - if v = w then 1 else 0) ∧
      ∀ i j, d i j ≠ 0 → (i, j) ≠ e ∧ y i j ∉ intLattice := by
  induction h with
  | refl =>
    refine ⟨fun _ _ ↦ 0, fun v ↦ ?_, fun i j h ↦ (h rfl).elim⟩
    unfold netFlow
    rw [Finset.sum_const_zero, sub_self, sub_self]
  | @tail v w _ hvw ih =>
    obtain ⟨d, hd, hs⟩ := ih
    rcases hvw with ⟨hne, hfr⟩ | ⟨hne, hfr⟩
    · refine ⟨fun i j ↦ d i j + if i = v ∧ j = w then 1 else 0, fun z ↦ ?_, fun i j h ↦ ?_⟩
      · rw [netFlow_add, hd, netFlow_single]
        ring
      · by_cases hij : i = v ∧ j = w
        · obtain ⟨rfl, rfl⟩ := hij
          exact ⟨hne, hfr⟩
        · simp only [hij, ↓reduceIte, add_zero] at h
          exact hs i j h
    · refine ⟨fun i j ↦ d i j - if i = w ∧ j = v then 1 else 0, fun z ↦ ?_, fun i j h ↦ ?_⟩
      · rw [netFlow_sub, hd, netFlow_single]
        ring
      · by_cases hij : i = w ∧ j = v
        · obtain ⟨rfl, rfl⟩ := hij
          exact ⟨hne, hfr⟩
        · simp only [hij, ↓reduceIte, sub_zero] at h
          exact hs i j h

omit [DecidableEq S] in
/-- **The cut argument**: for a fractional arc `a → b` of a circulation, `a` is reachable from `b`
through fractional arcs other than `a → b` (otherwise the net outflow of the reachable set would
be an integer minus `y a b`, yet it is `0`). -/
theorem reflTransGen_fracAdj_of_notMem {y : S → S → ℝ} (hy : IsCirculation y) {a b : S}
    (he : y a b ∉ intLattice) : Relation.ReflTransGen (fracAdj y (a, b)) b a := by
  classical
  by_contra hna
  set R := univ.filter fun v ↦ Relation.ReflTransGen (fracAdj y (a, b)) b v with hR
  have hbR : b ∈ R := Finset.mem_filter.2 ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
  have haR : a ∉ R := fun h ↦ hna (Finset.mem_filter.1 h).2
  have hreachR : ∀ {v j}, v ∈ R → fracAdj y (a, b) v j → j ∈ R := fun hv hvj ↦
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hv).2.tail hvj⟩
  set z : S → S → ℝ := fun i j ↦ y i j - if i = a ∧ j = b then y a b else 0 with hz
  have hnet : ∀ v,
      netFlow z v = 0 - ((if v = a then y a b else 0) - if v = b then y a b else 0) := fun v ↦ by
      rw [hz, netFlow_sub, netFlow_single, (isCirculation_iff_netFlow y).1 hy v]
  have hsum : ∑ v ∈ R, netFlow z v = y a b := by
    simp only [hnet, Finset.sum_sub_distrib, Finset.sum_const_zero, Finset.sum_ite_eq',
      haR, hbR, ↓reduceIte]
    ring
  have hzint : ∀ i j, ¬ (i = a ∧ j = b) → z i j = y i j := fun i j h ↦ by
    simp only [hz, h, ↓reduceIte, sub_zero]
  have hmem : ∑ v ∈ R, ∑ j ∈ Rᶜ, z v j - ∑ v ∈ R, ∑ j ∈ Rᶜ, z j v ∈ intLattice := by
    refine sub_mem (sum_mem fun v hv ↦ sum_mem fun j hj ↦ ?_)
      (sum_mem fun v hv ↦ sum_mem fun j hj ↦ ?_)
    · have hjR : j ∉ R := Finset.mem_compl.1 hj
      have hab : ¬ (v = a ∧ j = b) := fun h ↦ haR (h.1 ▸ hv)
      rw [hzint v j hab]
      by_contra hfr
      exact hjR (hreachR hv (Or.inl ⟨fun h ↦ hab (Prod.mk.inj h), hfr⟩))
    · have hjR : j ∉ R := Finset.mem_compl.1 hj
      by_cases hab : j = a ∧ v = b
      · simp only [hz, hab, and_self, ↓reduceIte, sub_self]
        exact zero_mem _
      · rw [hzint j v hab]
        by_contra hfr
        exact hjR (hreachR hv (Or.inr ⟨fun h ↦ hab (Prod.mk.inj h), hfr⟩))
  rw [← sum_netFlow_eq_cut, hsum] at hmem
  exact he hmem

omit [DecidableEq S] in
/-- **A fractional arc of a circulation lies on a cycle of fractional arcs**: there is a
circulation `D` with `D a b = 1`, supported on the fractional arcs of `y`. (Cut argument: if `a`
were not reachable from `b` through fractional arcs avoiding `a → b`, the net outflow of the
reachable set would be an integer minus `y a b`, yet it is `0`.) -/
theorem exists_cycle_direction {y : S → S → ℝ} (hy : IsCirculation y) {a b : S}
    (he : y a b ∉ intLattice) :
    ∃ D : S → S → ℝ, IsCirculation D ∧ D a b = 1 ∧ ∀ i j, D i j ≠ 0 → y i j ∉ intLattice := by
  classical
  have hreach := reflTransGen_fracAdj_of_notMem hy he
  obtain ⟨d, hd, hs⟩ := exists_pathFlow y (a, b) hreach
  have hdab : d a b = 0 := by
    by_contra h
    exact (hs a b h).1 rfl
  refine ⟨fun i j ↦ d i j + if i = a ∧ j = b then 1 else 0, ?_, ?_, fun i j h ↦ ?_⟩
  · rw [isCirculation_iff_netFlow]
    intro v
    rw [netFlow_add, hd, netFlow_single]
    ring
  · simp only [and_self, ↓reduceIte, hdab, zero_add]
  · by_cases hij : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hij
      exact he
    · simp only [hij, ↓reduceIte, add_zero] at h
      exact (hs i j h).2

/-! ### The circulation-rounding theorem -/

omit [DecidableEq S] in
/-- A non-integer real lies strictly between its floor and its ceiling. -/
theorem floor_lt_lt_ceil_of_notMem {z : ℝ} (hz : z ∉ intLattice) :
    (⌊z⌋ : ℝ) < z ∧ z < ⌈z⌉ := by
  refine ⟨lt_of_le_of_ne (Int.floor_le z) fun h ↦ hz (h ▸ intCast_mem_intLattice _),
    lt_of_le_of_ne (Int.le_ceil z) fun h ↦ hz (h ▸ intCast_mem_intLattice _)⟩

omit [DecidableEq S] in
/-- **Circulation rounding**: every real circulation `x` has an integer rounding
`⌊x_ij⌋ ≤ n_ij ≤ ⌈x_ij⌉` that is again a circulation. Proof by cycle cancelling: while some
entry is fractional, push along a cycle of fractional arcs (`exists_cycle_direction`) until one
more entry becomes an integer; floors and ceilings of the entries are respected throughout. -/
theorem exists_int_circulation_rounding {x : S → S → ℝ} (hx : IsCirculation x) :
    ∃ n : S → S → ℤ, IsCirculation (fun i j ↦ (n i j : ℝ)) ∧
      ∀ i j, ⌊x i j⌋ ≤ n i j ∧ n i j ≤ ⌈x i j⌉ := by
  classical
  let Inv : (S → S → ℝ) → Prop := fun y ↦
    IsCirculation y ∧ ∀ i j, (⌊x i j⌋ : ℝ) ≤ y i j ∧ y i j ≤ ⌈x i j⌉
  let F : (S → S → ℝ) → Finset (S × S) := fun y ↦ univ.filter fun q ↦ y q.1 q.2 ∉ intLattice
  have key : ∀ k, ∀ y, Inv y → (F y).card = k → ∃ n : S → S → ℤ,
      IsCirculation (fun i j ↦ (n i j : ℝ)) ∧ ∀ i j, ⌊x i j⌋ ≤ n i j ∧ n i j ≤ ⌈x i j⌉ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro y hy hk
    by_cases hF : F y = ∅
    · have hint : ∀ i j, (⌊y i j⌋ : ℝ) = y i j := fun i j ↦ by
        have : y i j ∈ intLattice := by
          by_contra h
          have hm : (i, j) ∈ F y := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
          rw [hF] at hm
          exact Finset.notMem_empty _ hm
        obtain ⟨m, hm⟩ := mem_intLattice.1 this
        rw [← hm, Int.floor_intCast]
      refine ⟨fun i j ↦ ⌊y i j⌋, fun v ↦ ?_, fun i j ↦ ⟨?_, ?_⟩⟩
      · simp only [hint]
        exact hy.1 v
      · exact Int.le_floor.2 (hy.2 i j).1
      · have h := (hy.2 i j).2
        rw [← hint i j] at h
        exact_mod_cast h
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hF
      have hpfr : y p.1 p.2 ∉ intLattice := (Finset.mem_filter.1 hp).2
      obtain ⟨D, hDc, hDab, hDs⟩ := exists_cycle_direction hy.1 hpfr
      set A := univ.filter fun q : S × S ↦ D q.1 q.2 ≠ 0 with hA
      have hpA : p ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hDab]; exact one_ne_zero⟩
      let r : S × S → ℝ := fun q ↦ if 0 < D q.1 q.2 then (⌈y q.1 q.2⌉ - y q.1 q.2) / D q.1 q.2
        else (y q.1 q.2 - ⌊y q.1 q.2⌋) / (-D q.1 q.2)
      obtain ⟨q₀, hq₀A, hmin⟩ := Finset.exists_min_image A r ⟨p, hpA⟩
      set t := r q₀ with ht
      have hDne : ∀ q ∈ A, D q.1 q.2 ≠ 0 := fun q hq ↦ (Finset.mem_filter.1 hq).2
      have ht0 : 0 ≤ t := by
        have hfr := floor_lt_lt_ceil_of_notMem (hDs _ _ (hDne q₀ hq₀A))
        simp only [ht, r]
        split_ifs with hpos
        · exact div_nonneg (by linarith) hpos.le
        · have : D q₀.1 q₀.2 < 0 := lt_of_le_of_ne (not_lt.1 hpos) (hDne q₀ hq₀A)
          exact div_nonneg (by linarith) (by linarith)
      set y' : S → S → ℝ := fun i j ↦ y i j + t * D i j with hy'
      have hbox : ∀ i j, (⌊y i j⌋ : ℝ) ≤ y' i j ∧ y' i j ≤ ⌈y i j⌉ := by
        intro i j
        by_cases hD : D i j = 0
        · simp only [hy', hD, mul_zero, add_zero]
          exact ⟨Int.floor_le _, Int.le_ceil _⟩
        · have hq : (i, j) ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hD⟩
          have hfr := floor_lt_lt_ceil_of_notMem (hDs i j hD)
          have hle : t ≤ r (i, j) := hmin (i, j) hq
          simp only [r] at hle
          simp only [hy']
          split_ifs at hle with hpos
          · rw [le_div_iff₀ hpos] at hle
            constructor <;> nlinarith
          · have hneg : D i j < 0 := lt_of_le_of_ne (not_lt.1 hpos) hD
            rw [le_div_iff₀ (by linarith)] at hle
            constructor <;> nlinarith
      have hInv : Inv y' := by
        refine ⟨(isCirculation_iff_netFlow _).2 fun v ↦ ?_, fun i j ↦ ⟨?_, ?_⟩⟩
        · rw [hy', netFlow_add, netFlow_mul, (isCirculation_iff_netFlow _).1 hy.1 v,
            (isCirculation_iff_netFlow _).1 hDc v, mul_zero, add_zero]
        · have h1 : (⌊x i j⌋ : ℝ) ≤ ⌊y i j⌋ := by exact_mod_cast Int.le_floor.2 (hy.2 i j).1
          linarith [(hbox i j).1]
        · have h1 : (⌈y i j⌉ : ℝ) ≤ ⌈x i j⌉ := by exact_mod_cast Int.ceil_le.2 (hy.2 i j).2
          linarith [(hbox i j).2]
      have hsub : F y' ⊆ (F y).erase q₀ := by
        intro q hq
        have hq' := (Finset.mem_filter.1 hq).2
        have hqF : q ∈ F y := by
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hyq ↦ hq' ?_⟩
          have hD : D q.1 q.2 = 0 := by
            by_contra hD
            exact hDs _ _ hD hyq
          simp only [hy', hD, mul_zero, add_zero]
          exact hyq
        refine Finset.mem_erase.2 ⟨fun hqq ↦ hq' ?_, hqF⟩
        subst hqq
        have hD := hDne q hq₀A
        simp only [hy', ht, r]
        split_ifs with hpos
        · rw [div_mul_cancel₀ _ hD, add_sub_cancel]
          exact intCast_mem_intLattice _
        · have h : y q.1 q.2 + (y q.1 q.2 - ⌊y q.1 q.2⌋) / -D q.1 q.2 * D q.1 q.2 =
              ⌊y q.1 q.2⌋ := by
            field_simp
            ring
          rw [h]
          exact intCast_mem_intLattice _
      have hlt : (F y').card < k := by
        rw [← hk]
        exact lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hDs _ _ (hDne q₀ hq₀A)⟩))
      exact ih _ hlt y' hInv rfl
  exact key _ x ⟨hx, fun i j ↦ ⟨Int.floor_le _, Int.le_ceil _⟩⟩ rfl

omit [DecidableEq S] in
/-- An integer between `⌊z⌋` and `⌈z⌉` is within `1` of `z`. -/
theorem abs_sub_lt_one_of_floor_le_le_ceil {z : ℝ} {k : ℤ} (h1 : ⌊z⌋ ≤ k) (h2 : k ≤ ⌈z⌉) :
    |(k : ℝ) - z| < 1 := by
  have h1' : (⌊z⌋ : ℝ) ≤ k := by exact_mod_cast h1
  have h2' : (k : ℝ) ≤ ⌈z⌉ := by exact_mod_cast h2
  have h3 := Int.ceil_lt_add_one z
  have h4 := Int.lt_floor_add_one z
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-! ### The expected counts `T π_i p_ij` -/

/-- `w` is a **stationary distribution** of `P` (as a row vector): `Σ_i w_i P i j = w_j`. -/
def IsStationaryRow (P : S → S → ℝ) (w : S → ℝ) : Prop := ∀ j, ∑ i, w i * P i j = w j

/-- Post #3's **expected transition counts** `x_ij = T π_i p_ij`. -/
def expectedCounts (P : S → S → ℝ) (w : S → ℝ) (T : ℝ) (i j : S) : ℝ := T * w i * P i j

omit [DecidableEq S] in
/-- **The expected counts form a circulation**: row `i` and column `i` both sum to `T π_i`. -/
theorem isCirculation_expectedCounts {P : S → S → ℝ} (hP : IsStochastic P) {w : S → ℝ}
    (hw : IsStationaryRow P w) (T : ℝ) : IsCirculation (expectedCounts P w T) := by
  intro v
  unfold expectedCounts
  rw [← Finset.mul_sum, hP.sum_eq_one v, mul_one]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, hw v]

omit [DecidableEq S] in
/-- The expected counts add up to `T` (for a probability vector `w`). -/
theorem sum_expectedCounts {P : S → S → ℝ} (hP : IsStochastic P) {w : S → ℝ}
    (hw1 : ∑ i, w i = 1) (T : ℝ) : ∑ i, ∑ j, expectedCounts P w T i j = T := by
  unfold expectedCounts
  simp only [← Finset.mul_sum, hP.sum_eq_one, mul_one]
  rw [hw1, mul_one]

omit [DecidableEq S] in
/-- **Post #3's rounding exists** ("counts `n_ij = T π_i p_ij`, rounded so that every state is
entered as often as it is left"): there is an integer circulation `n` with
`⌊T π_i p_ij⌋ ≤ n_ij ≤ ⌈T π_i p_ij⌉`, hence `|n_ij − T π_i p_ij| < 1`, and with total between
`Σ ⌊T π_i p_ij⌋` and `Σ ⌈T π_i p_ij⌉`. -/
theorem exists_rounding_expectedCounts {P : S → S → ℝ} (hP : IsStochastic P) {w : S → ℝ}
    (hw : IsStationaryRow P w) (T : ℝ) :
    ∃ n : S → S → ℤ, IsCirculation (fun i j ↦ (n i j : ℝ)) ∧
      (∀ i j, ⌊expectedCounts P w T i j⌋ ≤ n i j ∧ n i j ≤ ⌈expectedCounts P w T i j⌉) ∧
      (∀ i j, |(n i j : ℝ) - expectedCounts P w T i j| < 1) ∧
      ∑ i, ∑ j, ⌊expectedCounts P w T i j⌋ ≤ ∑ i, ∑ j, n i j ∧
      ∑ i, ∑ j, n i j ≤ ∑ i, ∑ j, ⌈expectedCounts P w T i j⌉ := by
  obtain ⟨n, hc, hb⟩ := exists_int_circulation_rounding (isCirculation_expectedCounts hP hw T)
  exact ⟨n, hc, hb, fun i j ↦ abs_sub_lt_one_of_floor_le_le_ceil (hb i j).1 (hb i j).2,
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ (hb i j).1,
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ (hb i j).2⟩

/-! ### Correction: the total cannot always be rounded to `T` -/

/-- The two-state flip chain `P = [[0, 1], [1, 0]]`. -/
def flipChain (i j : Fin 2) : ℝ := if i = j then 0 else 1

/-- The flip chain is stochastic. -/
theorem isStochastic_flipChain : IsStochastic flipChain := by
  refine ⟨fun i j ↦ ?_, fun i ↦ ?_⟩
  · unfold flipChain
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_two]
    unfold flipChain
    fin_cases i <;> norm_num

/-- `(1/2, 1/2)` is stationary for the flip chain. -/
theorem isStationaryRow_flipChain : IsStationaryRow flipChain fun _ ↦ 1 / 2 := by
  intro j
  rw [Fin.sum_univ_two]
  unfold flipChain
  fin_cases j <;> norm_num

/-- **Correction** (post #3, conditional MC): the rounded counts cannot always have total `T`.
For the flip chain with `π = (1/2, 1/2)` and `T = 3`, `x_01 = x_10 = 3/2` and `x_00 = x_11 = 0`,
and no integer circulation with `⌊x⌋ ≤ n ≤ ⌈x⌉` has total `3` (a circulation has
`n_01 = n_10`, so its total is even). So a path with exactly balanced counts may have to have
length `Σ n ≠ T`; `exists_rounding_expectedCounts` gives the correct statement, total between
`Σ ⌊x⌋` and `Σ ⌈x⌉`. (With "allowing for the first and last states", i.e. open paths, the length
`3` path `0 → 1 → 0 → 1` does exist here.) -/
theorem not_exists_rounding_flipChain_total_three :
    ¬ ∃ n : Fin 2 → Fin 2 → ℤ, IsCirculation (fun i j ↦ (n i j : ℝ)) ∧
      (∀ i j, ⌊expectedCounts flipChain (fun _ ↦ 1 / 2) 3 i j⌋ ≤ n i j ∧
        n i j ≤ ⌈expectedCounts flipChain (fun _ ↦ 1 / 2) 3 i j⌉) ∧
      ∑ i, ∑ j, n i j = 3 := by
  rintro ⟨n, hc, hb, hs⟩
  have hdiag : ∀ i, expectedCounts flipChain (fun _ ↦ 1 / 2) 3 i i = 0 := fun i ↦ by
    simp only [expectedCounts, flipChain, eq_self, ↓reduceIte, mul_zero]
  have h00 := hb 0 0
  have h11 := hb 1 1
  rw [hdiag, Int.floor_zero, Int.ceil_zero] at h00 h11
  have h0 := hc 0
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h0
  beta_reduce at h0
  have h0' : n 0 0 + n 0 1 = n 0 0 + n 1 0 := by exact_mod_cast h0
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at hs
  omega

/-! ### The conditional MC of post #3 is well defined -/

omit [DecidableEq S] in
/-- **A closed path realising the rounded counts**: for an irreducible stochastic `P` with
stationary `π` and a horizon `T` large enough that `T π_i p_ij ≥ 1` on the support of `P`, there
are counts `N` within `1` of `T π_i p_ij`, with the same support as `P`, balanced at every state,
and a closed path from any `x₀` of length `Σ N` with exactly these transition counts (Euler,
`exists_path_of_balanced`). -/
theorem exists_closed_path_of_rounding [DecidableEq S] {P : S → S → ℝ} (hP : IsStochastic P)
    {w : S → ℝ} (hw : IsStationaryRow P w) {T : ℝ}
    (hT : ∀ i j, 0 < P i j → 1 ≤ expectedCounts P w T i j)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b ↦ 0 < P a b) i j) (x₀ : S) :
    ∃ N : S → S → ℕ, (∀ i j, |(N i j : ℝ) - expectedCounts P w T i j| < 1) ∧
      (∀ i j, N i j ≠ 0 ↔ 0 < P i j) ∧ BalancedCounts N x₀ x₀ ∧
      ∃ s : ℕ → S, s 0 = x₀ ∧ s (∑ i, ∑ j, N i j) = x₀ ∧
        ∀ i j, transCount s i j (∑ i, ∑ j, N i j) = N i j := by
  obtain ⟨n, hc, hb, habs, -⟩ := exists_rounding_expectedCounts hP hw T
  have hzero : ∀ i j, P i j = 0 → expectedCounts P w T i j = 0 := fun i j h ↦ by
    rw [expectedCounts, h, mul_zero]
  have hn0 : ∀ i j, 0 ≤ n i j := fun i j ↦ by
    rcases (hP.nonneg i j).lt_or_eq with h | h
    · exact le_trans (Int.floor_nonneg.2 (le_trans zero_le_one (hT i j h))) (hb i j).1
    · exact le_trans (by rw [hzero i j h.symm, Int.floor_zero]) (hb i j).1
  set N : S → S → ℕ := fun i j ↦ (n i j).toNat with hN
  have hNz : ∀ i j, ((N i j : ℕ) : ℤ) = n i j := fun i j ↦ Int.toNat_of_nonneg (hn0 i j)
  have hNr : ∀ i j, ((N i j : ℕ) : ℝ) = n i j := fun i j ↦ by
    rw [← Int.cast_natCast, hNz]
  have hsupp : ∀ i j, N i j ≠ 0 ↔ 0 < P i j := by
    intro i j
    constructor
    · intro h
      rcases (hP.nonneg i j).lt_or_eq with hp | hp
      · exact hp
      · exfalso
        have := hb i j
        rw [hzero i j hp.symm, Int.floor_zero, Int.ceil_zero] at this
        have h' := hNz i j
        omega
    · intro hp
      have h1 : 1 ≤ n i j := le_trans (Int.le_floor.2 (by exact_mod_cast hT i j hp)) (hb i j).1
      have h' := hNz i j
      omega
  have hbal : BalancedCounts N x₀ x₀ := by
    intro i
    have hci : ∑ j, n i j = ∑ j, n j i := by
      have := hc i
      beta_reduce at this
      exact_mod_cast this
    simp only [hNz]
    rw [hci, sub_self, sub_self]
  have hconn : ∀ i j, N i j ≠ 0 → Relation.ReflTransGen (fun a b ↦ N a b ≠ 0) x₀ i :=
    fun i _ _ ↦ Relation.ReflTransGen.mono (fun a b h ↦ (hsupp a b).2 h) x₀ i (hirr x₀ i)
  obtain ⟨s, hs0, hsT, hsN⟩ := exists_path_of_balanced hbal hconn
  exact ⟨N, fun i j ↦ by rw [hNr]; exact habs i j, hsupp, hbal, s, hs0, hsT, hsN⟩

/-- **Post #3's conditional MC is well defined**: with the rounded counts `N` of
`exists_closed_path_of_rounding` and `L = Σ N`, the event "MC from `x₀` has transition counts
`N` over `L` steps" has positive probability, and conditionally on it the MC path is uniform
over the paths with these counts (`cond_mcLaw_countClass`). -/
theorem conditionalMC_wellDefined {m : ℕ} {P : Fin m → Fin m → ℝ} (hP : IsStochastic P)
    {w : Fin m → ℝ} (hw : IsStationaryRow P w) {T : ℝ}
    (hT : ∀ i j, 0 < P i j → 1 ≤ expectedCounts P w T i j)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b ↦ 0 < P a b) i j) (x₀ : Fin m) :
    ∃ N : Fin m → Fin m → ℕ, (∀ i j, |(N i j : ℝ) - expectedCounts P w T i j| < 1) ∧
      BalancedCounts N x₀ x₀ ∧
      mcLaw P x₀ (∑ i, ∑ j, N i j) (countClass x₀ N (∑ i, ∑ j, N i j) : Set _) ≠ 0 ∧
      (mcLaw P x₀ (∑ i, ∑ j, N i j))[|(countClass x₀ N (∑ i, ∑ j, N i j) : Set _)] =
        uniformOn (countClass x₀ N (∑ i, ∑ j, N i j) : Set _) := by
  obtain ⟨N, habs, hsupp, hbal, s, hs0, -, hsN⟩ := exists_closed_path_of_rounding hP hw hT hirr x₀
  set L := ∑ i, ∑ j, N i j with hL
  set sv : Fin (L + 1) → Fin m := fun t ↦ s t with hsv
  have hagree : ∀ t ≤ L, s t = extendPath sv t := (extendPath_eq_iff s sv).1 rfl
  have hmem : sv ∈ countClass x₀ N L := by
    rw [mem_countClass]
    refine ⟨(hagree 0 (Nat.zero_le L)).symm.trans hs0, fun i j ↦ ?_⟩
    rw [← transCount_congr hagree i j]
    exact hsN i j
  have hpos : 0 < mcLaw P x₀ L {sv} := by
    rw [mcLaw_singleton_of_mem hP x₀ N L hmem, ENNReal.ofReal_pos]
    refine Finset.prod_pos fun i _ ↦ Finset.prod_pos fun j _ ↦ ?_
    by_cases h : N i j = 0
    · rw [h, pow_zero]
      exact one_pos
    · exact pow_pos ((hsupp i j).1 h) _
  have hC : mcLaw P x₀ L (countClass x₀ N L : Set _) ≠ 0 :=
    (lt_of_lt_of_le hpos (measure_mono (Set.singleton_subset_iff.2 (Finset.mem_coe.2 hmem)))).ne'
  exact ⟨N, habs, hbal, hC, cond_mcLaw_countClass hP x₀ N L hC⟩

end RQMCMarkov.MarkovDriving

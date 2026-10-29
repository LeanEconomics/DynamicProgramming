/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.ConditionalMCRounding

/-!
# Rounding with exactly `T` transitions, allowing for the first and last states (post #3)

Post #3 asks for counts `n_ij = T π_i p_ij`, "rounded so that every state is entered as often as
it is left (allowing for the first and last states)". Reading: integer counts `N` with total
exactly `T` (a path of `T` transitions), entrywise roundings `⌊T π_i p_ij⌋ ≤ N_ij ≤
⌈T π_i p_ij⌉` (so `|N_ij − T π_i p_ij| < 1`, the strict bound — no weakening needed), and
balanced except at a first state `a` and a last state `b`: out-count minus in-count equals
`1{a} − 1{b}`. `ConditionalMCRounding` shows that closed (circulation) roundings cannot always
have total `T`; open ones always can.

## Main results

* `exists_walk_of_reflTransGen`, `exists_injOn_walk`: chains are walks, and can be taken
  without repeated states.
* `prefCount`, `netFlow_prefCount`, `sum_prefCount`, `prefCount_ne_zero`: flows of the prefixes
  of a walk with distinct arcs.
* `exists_simple_cycle`: every fractional arc of a real circulation lies on a simple cycle of
  fractional arcs (walk of distinct states closing through the arc).
* `fracSet`, `exists_push`: pushing along a circulation supported on the fractional entries
  makes one more entry an integer (inside the box `[⌊x⌋, ⌈x⌉]`).
* `exists_eq_of_unit_steps`: the discrete intermediate value theorem.
* `exists_open_rounding`: **open rounding with exact total** — a real circulation with integer
  total `T` has an integer rounding `⌊x⌋ ≤ N ≤ ⌈x⌉` with total `T` balanced from some `a` to some
  `b`.
* `exists_path_exact_length`: for irreducible `P`, stationary probability `π`, and integer `T`
  with `T π_i p_ij ≥ 1` on the support of `P`: counts within `1` of `T π_i p_ij` with total `T`,
  the support of `P`, balanced from `a` to `b`, and a path `a = s_0, …, s_T = b` with exactly
  these counts.
* `conditionalMC_exact_wellDefined`: post #3's conditional MC with exactly `T` transitions is
  well defined (positive conditioning probability; conditional law uniform on the paths).
* `flipChain_open_path_three`: the open path `0 → 1 → 0 → 1` for the flip chain at `T = 3`.

The start and end states `a`, `b` are produced by the rounding, not prescribed.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S : Type*}

/-! ### Walks without repeated states -/

/-- A chain `u →* v` of a relation is a walk `W 0 = u, …, W k = v`. -/
theorem exists_walk_of_reflTransGen {r : S → S → Prop} {u v : S}
    (h : Relation.ReflTransGen r u v) :
    ∃ W : ℕ → S, ∃ k, W 0 = u ∧ W k = v ∧ ∀ s < k, r (W s) (W (s + 1)) := by
  induction h with
  | refl => exact ⟨fun _ ↦ u, 0, rfl, rfl, fun s hs ↦ absurd hs (Nat.not_lt_zero s)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨W, k, h0, hk, hs⟩ := ih
    refine ⟨Function.update W (k + 1) c, k + 1, ?_, Function.update_self _ _ _, fun s hs' ↦ ?_⟩
    · rw [Function.update_of_ne (by omega)]
      exact h0
    · rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs' with hs' | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hs s hs'
      · rw [Function.update_self, hk]
        exact hbc

/-- A chain `u →* v` is realised by a walk **without repeated states**. -/
theorem exists_injOn_walk {r : S → S → Prop} {u v : S} (h : Relation.ReflTransGen r u v) :
    ∃ W : ℕ → S, ∃ k, W 0 = u ∧ W k = v ∧ (∀ s < k, r (W s) (W (s + 1))) ∧
      ∀ i ≤ k, ∀ j ≤ k, W i = W j → i = j := by
  classical
  have hQ : ∃ k, ∃ W : ℕ → S, W 0 = u ∧ W k = v ∧ ∀ s < k, r (W s) (W (s + 1)) := by
    obtain ⟨W, k, h0, hk, hs⟩ := exists_walk_of_reflTransGen h
    exact ⟨k, W, h0, hk, hs⟩
  obtain ⟨W, h0, hk, hs⟩ := Nat.find_spec hQ
  set k := Nat.find hQ with hkdef
  have hshort : ∀ i j, i < j → j ≤ k → W i = W j → False := by
    intro i j hij hjk hW
    set W' : ℕ → S := fun t ↦ if t ≤ i then W t else W (t + (j - i)) with hW'
    have hlt : k - (j - i) < k := by omega
    refine Nat.find_min hQ hlt ⟨W', ?_, ?_, fun t ht ↦ ?_⟩
    · simp only [hW', Nat.zero_le, ↓reduceIte]
      exact h0
    · by_cases hki : k - (j - i) ≤ i
      · simp only [hW', hki, ↓reduceIte]
        rw [show k - (j - i) = i by omega, hW, show j = k by omega]
        exact hk
      · simp only [hW', hki, ↓reduceIte]
        rw [show k - (j - i) + (j - i) = k by omega]
        exact hk
    · by_cases h1 : t + 1 ≤ i
      · simp only [hW', h1, show t ≤ i by omega, ↓reduceIte]
        exact hs t (by omega)
      · by_cases h2 : t ≤ i
        · simp only [hW', h1, h2, ↓reduceIte]
          rw [show t = i by omega, hW, show i + 1 + (j - i) = j + 1 by omega]
          exact hs j (by omega)
        · simp only [hW', h1, h2, ↓reduceIte]
          rw [show t + 1 + (j - i) = t + (j - i) + 1 by omega]
          exact hs (t + (j - i)) (by omega)
  refine ⟨W, k, h0, hk, hs, fun i hi j hj hW ↦ ?_⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hshort i j hij hj hW).elim
  · exact hij
  · exact (hshort j i hij hi hW.symm).elim

/-! ### Prefix flows of a cycle -/

variable [DecidableEq S]

/-- The integer flow of the first `m` steps of a walk with arcs `arc s` and signs `sg s`
(`+1` for a step along its arc, `−1` against it). -/
def prefCount (arc : ℕ → S × S) (sg : ℕ → ℤ) (m : ℕ) (i j : S) : ℤ :=
  ∑ s ∈ range m, if arc s = (i, j) then sg s else 0

omit [DecidableEq S] in
/-- Rewriting an arc indicator. -/
theorem ite_prod_eq [DecidableEq S] (p : S × S) (i j : S) (c : ℝ) :
    (if p = (i, j) then c else 0) = if i = p.1 ∧ j = p.2 then c else 0 := by
  obtain ⟨p1, p2⟩ := p
  by_cases h : i = p1 ∧ j = p2
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ↓reduceIte]
  · have h' : (p1, p2) ≠ (i, j) := fun hh ↦ h ⟨(Prod.mk.inj hh).1.symm, (Prod.mk.inj hh).2.symm⟩
    simp only [h, h', ↓reduceIte]

variable [Fintype S]

/-- **Net outflow of a prefix flow**: `1{v = C 0} − 1{v = C m}`, whatever the orientations. -/
theorem netFlow_prefCount {L : ℕ} {C : ℕ → S} {arc : ℕ → S × S} {sg : ℕ → ℤ}
    (h2 : ∀ s < L, (sg s = 1 ∧ arc s = (C s, C (s + 1))) ∨
      (sg s = -1 ∧ arc s = (C (s + 1), C s))) {m : ℕ} (hm : m ≤ L) (v : S) :
    netFlow (fun i j ↦ (prefCount arc sg m i j : ℝ)) v =
      (if v = C 0 then 1 else 0) - if v = C m then 1 else 0 := by
  induction m with
  | zero =>
    unfold netFlow prefCount
    simp only [Finset.range_zero, Finset.sum_empty, Int.cast_zero, Finset.sum_const_zero,
      sub_self]
  | succ m ih =>
    have hf : (fun i j ↦ (prefCount arc sg (m + 1) i j : ℝ)) = fun i j ↦
        (prefCount arc sg m i j : ℝ) + if i = (arc m).1 ∧ j = (arc m).2 then (sg m : ℝ) else 0 := by
      funext i j
      unfold prefCount
      rw [Finset.sum_range_succ, Int.cast_add, ← ite_prod_eq]
      push_cast
      rfl
    rw [hf, netFlow_add, ih (by omega), netFlow_single]
    rcases h2 m (by omega) with ⟨hs, ha⟩ | ⟨hs, ha⟩
    · rw [hs, ha]
      push_cast
      ring
    · rw [hs, ha]
      push_cast
      split_ifs <;> ring

/-- The total of a prefix flow is the sum of the signs. -/
theorem sum_prefCount (arc : ℕ → S × S) (sg : ℕ → ℤ) (m : ℕ) :
    ∑ i, ∑ j, prefCount arc sg m i j = ∑ s ∈ range m, sg s := by
  unfold prefCount
  calc ∑ i, ∑ j, ∑ s ∈ range m, (if arc s = (i, j) then sg s else 0)
      = ∑ i, ∑ s ∈ range m, ∑ j, (if arc s = (i, j) then sg s else 0) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
    _ = ∑ s ∈ range m, ∑ i, ∑ j, (if arc s = (i, j) then sg s else 0) := Finset.sum_comm
    _ = ∑ s ∈ range m, sg s := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [← Fintype.sum_prod_type' (f := fun i j ↦ if arc s = (i, j) then sg s else 0)]
        simp only [Prod.mk.eta]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, ↓reduceIte]

omit [Fintype S] in
/-- With distinct arcs, a nonzero entry of a prefix flow is the sign of the unique step using
that arc, and equals the entry of the full flow. -/
theorem prefCount_ne_zero {L : ℕ} {arc : ℕ → S × S} {sg : ℕ → ℤ}
    (h4 : ∀ s < L, ∀ s' < L, arc s = arc s' → s = s') {m : ℕ} (hm : m ≤ L) {i j : S}
    (h : prefCount arc sg m i j ≠ 0) :
    ∃ s₀ < m, arc s₀ = (i, j) ∧ prefCount arc sg m i j = sg s₀ ∧
      prefCount arc sg L i j = sg s₀ := by
  obtain ⟨s₀, hs₀, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hs₀m := Finset.mem_range.1 hs₀
  have harc : arc s₀ = (i, j) := by
    by_contra hc
    simp only [hc, ↓reduceIte, ne_eq, not_true_eq_false] at hne
  have hsum : ∀ M, s₀ < M → M ≤ L → prefCount arc sg M i j = sg s₀ := fun M hM hML ↦ by
    unfold prefCount
    rw [Finset.sum_eq_single_of_mem s₀ (Finset.mem_range.2 hM)]
    · simp only [harc, ↓reduceIte]
    · intro s hs hss
      have : arc s ≠ (i, j) := fun has ↦
        hss (h4 s (by have := Finset.mem_range.1 hs; omega) s₀ (by omega) (has.trans harc.symm))
      simp only [this, ↓reduceIte]
  exact ⟨s₀, hs₀m, harc, hsum m hs₀m hm, hsum L (by omega) le_rfl⟩

/-! ### A simple cycle through a fractional arc -/

omit [DecidableEq S] in
/-- **A fractional arc of a circulation lies on a simple cycle of fractional arcs**: a closed
walk `C 0 = a, C 1 = b, …, C L = a` whose steps use distinct fractional arcs `arc s`, the first
being `a → b`, each traversed along (`sg s = 1`) or against (`sg s = −1`) its direction. -/
theorem exists_simple_cycle {y : S → S → ℝ} (hy : IsCirculation y) {a b : S}
    (he : y a b ∉ intLattice) :
    ∃ L : ℕ, ∃ C : ℕ → S, ∃ arc : ℕ → S × S, ∃ sg : ℕ → ℤ, 1 ≤ L ∧ C 0 = a ∧ C L = a ∧
      (∀ s < L, (sg s = 1 ∧ arc s = (C s, C (s + 1))) ∨
        (sg s = -1 ∧ arc s = (C (s + 1), C s))) ∧
      (∀ s < L, y (arc s).1 (arc s).2 ∉ intLattice) ∧
      (∀ s < L, ∀ s' < L, arc s = arc s' → s = s') ∧ arc 0 = (a, b) ∧ sg 0 = 1 := by
  classical
  obtain ⟨W, k, hW0, hWk, hWs, hWinj⟩ := exists_injOn_walk (reflTransGen_fracAdj_of_notMem hy he)
  let fwd : ℕ → Prop := fun i ↦ (W i, W (i + 1)) ≠ (a, b) ∧ y (W i) (W (i + 1)) ∉ intLattice
  let C : ℕ → S := fun t ↦ if t = 0 then a else W (t - 1)
  let arc : ℕ → S × S := fun s ↦ if s = 0 then (a, b) else
    if fwd (s - 1) then (W (s - 1), W s) else (W s, W (s - 1))
  let sg : ℕ → ℤ := fun s ↦ if s = 0 then 1 else if fwd (s - 1) then 1 else -1
  have hC : ∀ i, C (i + 1) = W i := fun i ↦ by
    simp only [C, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  -- the arc of step `i + 1` and its properties
  have harc : ∀ i < k, (arc (i + 1) = (W i, W (i + 1)) ∨ arc (i + 1) = (W (i + 1), W i)) ∧
      arc (i + 1) ≠ (a, b) ∧ y (arc (i + 1)).1 (arc (i + 1)).2 ∉ intLattice ∧
      ((sg (i + 1) = 1 ∧ arc (i + 1) = (C (i + 1), C (i + 1 + 1))) ∨
        (sg (i + 1) = -1 ∧ arc (i + 1) = (C (i + 1 + 1), C (i + 1)))) := by
    intro i hi
    have hadj := hWs i hi
    by_cases hf : fwd i
    · have e1 : arc (i + 1) = (W i, W (i + 1)) := by
        simp only [arc, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hf]
      have e2 : sg (i + 1) = 1 := by
        simp only [sg, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hf]
      refine ⟨Or.inl e1, e1 ▸ hf.1, e1 ▸ hf.2, Or.inl ⟨e2, ?_⟩⟩
      rw [e1, hC, hC]
    · have e1 : arc (i + 1) = (W (i + 1), W i) := by
        simp only [arc, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hf]
      have e2 : sg (i + 1) = -1 := by
        simp only [sg, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hf]
      have hb : (W (i + 1), W i) ≠ (a, b) ∧ y (W (i + 1)) (W i) ∉ intLattice := by
        rcases hadj with hl | hr
        · exact absurd hl hf
        · exact hr
      refine ⟨Or.inr e1, e1 ▸ hb.1, e1 ▸ hb.2, Or.inr ⟨e2, ?_⟩⟩
      rw [e1, hC, hC]
  have harc0 : arc 0 = (a, b) := by simp only [arc, ↓reduceIte]
  have hsg0 : sg 0 = 1 := by simp only [sg, ↓reduceIte]
  have hC0 : C 0 = a := by simp only [C, ↓reduceIte]
  refine ⟨k + 1, C, arc, sg, by omega, hC0, by rw [hC, hWk], fun s hs ↦ ?_, fun s hs ↦ ?_,
    fun s hs s' hs' hss ↦ ?_, harc0, hsg0⟩
  · rcases s with _ | i
    · left
      rw [hsg0, harc0, hC0, hC, hW0]
      exact ⟨rfl, rfl⟩
    · exact (harc i (by omega)).2.2.2
  · rcases s with _ | i
    · rw [harc0]
      exact he
    · exact (harc i (by omega)).2.2.1
  · rcases s with _ | i <;> rcases s' with _ | i'
    · rfl
    · exact absurd (hss.symm.trans harc0) (harc i' (by omega)).2.1
    · exact absurd (hss.trans harc0) (harc i (by omega)).2.1
    · have h1 := (harc i (by omega)).1
      have h2 := (harc i' (by omega)).1
      have key : i = i' := by
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at hss <;>
          obtain ⟨hp1, hp2⟩ := Prod.mk.inj hss
        · exact hWinj i (by omega) i' (by omega) hp1
        · have := hWinj i (by omega) (i' + 1) (by omega) hp1
          have := hWinj (i + 1) (by omega) i' (by omega) hp2
          omega
        · have := hWinj (i + 1) (by omega) i' (by omega) hp1
          have := hWinj i (by omega) (i' + 1) (by omega) hp2
          omega
        · exact hWinj i (by omega) i' (by omega) hp2
      rw [key]

/-! ### The push step -/

omit [DecidableEq S] in
/-- The fractional entries of a real matrix. -/
noncomputable def fracSet (y : S → S → ℝ) : Finset (S × S) := by
  classical
  exact univ.filter fun q ↦ y q.1 q.2 ∉ intLattice

omit [DecidableEq S] in
/-- Membership in `fracSet`. -/
theorem mem_fracSet {y : S → S → ℝ} {q : S × S} : q ∈ fracSet y ↔ y q.1 q.2 ∉ intLattice := by
  classical
  unfold fracSet
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ q)

omit [DecidableEq S] in
/-- **Push step**: moving a circulation `y` (inside the box `[⌊x⌋, ⌈x⌉]`) along a nonzero
circulation `D` supported on its fractional entries, as far as the box `[⌊y⌋, ⌈y⌉]` allows,
keeps it a circulation inside the box and makes at least one more entry an integer. -/
theorem exists_push {x y D : S → S → ℝ} (hyc : IsCirculation y)
    (hyb : ∀ i j, (⌊x i j⌋ : ℝ) ≤ y i j ∧ y i j ≤ ⌈x i j⌉) (hDc : IsCirculation D)
    {p : S × S} (hp : D p.1 p.2 ≠ 0) (hDs : ∀ i j, D i j ≠ 0 → y i j ∉ intLattice) :
    ∃ t : ℝ, IsCirculation (fun i j ↦ y i j + t * D i j) ∧
      (∀ i j, (⌊x i j⌋ : ℝ) ≤ y i j + t * D i j ∧ y i j + t * D i j ≤ ⌈x i j⌉) ∧
      (fracSet fun i j ↦ y i j + t * D i j).card < (fracSet y).card := by
  classical
  set A := univ.filter fun q : S × S ↦ D q.1 q.2 ≠ 0 with hA
  have hpA : p ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩
  let r : S × S → ℝ := fun q ↦ if 0 < D q.1 q.2 then (⌈y q.1 q.2⌉ - y q.1 q.2) / D q.1 q.2
    else (y q.1 q.2 - ⌊y q.1 q.2⌋) / (-D q.1 q.2)
  obtain ⟨q₀, hq₀A, hmin⟩ := Finset.exists_min_image A r ⟨p, hpA⟩
  set t := r q₀ with ht
  have hDne : ∀ q ∈ A, D q.1 q.2 ≠ 0 := fun q hq ↦ (Finset.mem_filter.1 hq).2
  set y' : S → S → ℝ := fun i j ↦ y i j + t * D i j with hy'
  have hbox : ∀ i j, (⌊y i j⌋ : ℝ) ≤ y' i j ∧ y' i j ≤ ⌈y i j⌉ := by
    intro i j
    by_cases hD : D i j = 0
    · simp only [hy', hD, mul_zero, add_zero]
      exact ⟨Int.floor_le _, Int.le_ceil _⟩
    · have hq : (i, j) ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hD⟩
      have hfr := floor_lt_lt_ceil_of_notMem (hDs i j hD)
      have hle : t ≤ r (i, j) := hmin (i, j) hq
      have ht0 : 0 ≤ t := by
        have hfr0 := floor_lt_lt_ceil_of_notMem (hDs _ _ (hDne q₀ hq₀A))
        simp only [ht, r]
        split_ifs with hpos
        · exact div_nonneg (by linarith) hpos.le
        · have : D q₀.1 q₀.2 < 0 := lt_of_le_of_ne (not_lt.1 hpos) (hDne q₀ hq₀A)
          exact div_nonneg (by linarith) (by linarith)
      simp only [r] at hle
      simp only [hy']
      split_ifs at hle with hpos
      · rw [le_div_iff₀ hpos] at hle
        constructor <;> nlinarith
      · have hneg : D i j < 0 := lt_of_le_of_ne (not_lt.1 hpos) hD
        rw [le_div_iff₀ (by linarith)] at hle
        constructor <;> nlinarith
  refine ⟨t, (isCirculation_iff_netFlow _).2 fun v ↦ ?_, fun i j ↦ ⟨?_, ?_⟩, ?_⟩
  · rw [netFlow_add, netFlow_mul, (isCirculation_iff_netFlow _).1 hyc v,
      (isCirculation_iff_netFlow _).1 hDc v, mul_zero, add_zero]
  · have h1 : (⌊x i j⌋ : ℝ) ≤ ⌊y i j⌋ := by exact_mod_cast Int.le_floor.2 (hyb i j).1
    linarith [(hbox i j).1]
  · have h1 : (⌈y i j⌉ : ℝ) ≤ ⌈x i j⌉ := by exact_mod_cast Int.ceil_le.2 (hyb i j).2
    linarith [(hbox i j).2]
  · have hsub : fracSet y' ⊆ (fracSet y).erase q₀ := by
      intro q hq
      have hq' := mem_fracSet.1 hq
      have hqF : q ∈ fracSet y := by
        refine mem_fracSet.2 fun hyq ↦ hq' ?_
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
    exact lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem
      (mem_fracSet.2 (hDs _ _ (hDne q₀ hq₀A))))

/-! ### Rounding with an exact total, open at the ends -/

omit [DecidableEq S] [Fintype S] in
/-- **Discrete intermediate value theorem**: a walk on `ℤ` with unit steps hits every integer
between its endpoints. -/
theorem exists_eq_of_unit_steps (f : ℕ → ℤ) (L : ℕ)
    (hstep : ∀ m < L, f (m + 1) = f m + 1 ∨ f (m + 1) = f m - 1) (z : ℤ)
    (hz : (f 0 ≤ z ∧ z ≤ f L) ∨ (f L ≤ z ∧ z ≤ f 0)) : ∃ m ≤ L, f m = z := by
  induction L with
  | zero => exact ⟨0, le_rfl, by omega⟩
  | succ L ih =>
    by_cases h : (f 0 ≤ z ∧ z ≤ f L) ∨ (f L ≤ z ∧ z ≤ f 0)
    · obtain ⟨m, hm, hfm⟩ := ih (fun m hm ↦ hstep m (by omega)) h
      exact ⟨m, by omega, hfm⟩
    · refine ⟨L + 1, le_rfl, ?_⟩
      have := hstep L (by omega)
      omega

/-- **Open rounding with an exact total** (post #3's rounding "allowing for the first and last
states"): a real circulation `x` with integer total `T` has an integer rounding
`⌊x_ij⌋ ≤ N_ij ≤ ⌈x_ij⌉` with total exactly `T` that is balanced from some state `a` to some
state `b` (net outflow `1{a} − 1{b}`; `a = b` allowed).

Proof by induction on the number of fractional entries of `y` (a circulation in the box with
total `T`): take a simple cycle `D` of fractional arcs (`exists_simple_cycle`) and a circulation
rounding `n` of `y`. If `Σ D = 0`, or `y − n` is not a multiple of `D`, a total-preserving push
(`exists_push`) removes a fractional entry. Otherwise `y = n + θ D`, and adding `± 1` along the
first `m` arcs of the cycle, with `m` chosen by the discrete intermediate value theorem so that
the total becomes `T`, gives the rounding. -/
theorem exists_open_rounding [Nonempty S] {x : S → S → ℝ} (hx : IsCirculation x) {T : ℤ}
    (hT : ∑ i, ∑ j, x i j = T) :
    ∃ N : S → S → ℤ, ∃ a b : S,
      (∀ v, netFlow (fun i j ↦ (N i j : ℝ)) v = (if v = a then 1 else 0) - if v = b then 1 else 0) ∧
      (∀ i j, ⌊x i j⌋ ≤ N i j ∧ N i j ≤ ⌈x i j⌉) ∧ ∑ i, ∑ j, N i j = T := by
  classical
  have key : ∀ k, ∀ y : S → S → ℝ, IsCirculation y →
      (∀ i j, (⌊x i j⌋ : ℝ) ≤ y i j ∧ y i j ≤ ⌈x i j⌉) → ∑ i, ∑ j, y i j = T →
      (fracSet y).card = k → ∃ N : S → S → ℤ, ∃ a b : S,
      (∀ v, netFlow (fun i j ↦ (N i j : ℝ)) v = (if v = a then 1 else 0) - if v = b then 1 else 0) ∧
      (∀ i j, ⌊x i j⌋ ≤ N i j ∧ N i j ≤ ⌈x i j⌉) ∧ ∑ i, ∑ j, N i j = T := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro y hyc hyb hyT hk
    have hfloor : ∀ i j, ⌊x i j⌋ ≤ ⌊y i j⌋ := fun i j ↦ Int.le_floor.2 (hyb i j).1
    have hceil : ∀ i j, ⌈y i j⌉ ≤ ⌈x i j⌉ := fun i j ↦ Int.ceil_le.2 (hyb i j).2
    by_cases hF : fracSet y = ∅
    · have hint : ∀ i j, (⌊y i j⌋ : ℝ) = y i j := fun i j ↦ by
        have : y i j ∈ intLattice := by
          by_contra h
          have hm : (i, j) ∈ fracSet y := mem_fracSet.2 h
          rw [hF] at hm
          exact Finset.notMem_empty _ hm
        obtain ⟨m, hm⟩ := mem_intLattice.1 this
        rw [← hm, Int.floor_intCast]
      obtain ⟨a⟩ := ‹Nonempty S›
      refine ⟨fun i j ↦ ⌊y i j⌋, a, a, fun v ↦ ?_, fun i j ↦ ⟨hfloor i j, ?_⟩, ?_⟩
      · simp only [hint]
        rw [(isCirculation_iff_netFlow y).1 hyc v, sub_self]
      · have h := (hyb i j).2
        rw [← hint i j] at h
        exact_mod_cast h
      · have : ((∑ i, ∑ j, ⌊y i j⌋ : ℤ) : ℝ) = T := by
          push_cast
          simp only [hint]
          exact hyT
        exact_mod_cast this
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hF
    obtain ⟨n, hnc, hnb⟩ := exists_int_circulation_rounding hyc
    obtain ⟨L, C, arc, sg, hL1, hC0, hCL, h2, h3, h4, harc0, hsg0⟩ :=
      exists_simple_cycle hyc (mem_fracSet.1 hp)
    set D : S → S → ℝ := fun i j ↦ (prefCount arc sg L i j : ℝ) with hD
    have hDc : IsCirculation D := (isCirculation_iff_netFlow D).2 fun v ↦ by
      rw [hD, netFlow_prefCount h2 le_rfl v, hC0, hCL, sub_self]
    have hDs : ∀ i j, D i j ≠ 0 → y i j ∉ intLattice := fun i j h ↦ by
      have h' : prefCount arc sg L i j ≠ 0 := fun h0 ↦ h (by rw [hD]; simp only [h0, Int.cast_zero])
      obtain ⟨s₀, hs₀, harc, -, -⟩ := prefCount_ne_zero h4 le_rfl h'
      have := h3 s₀ hs₀
      rw [harc] at this
      exact this
    have hDab : prefCount arc sg L p.1 p.2 = 1 := by
      unfold prefCount
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hL1)]
      · simp only [harc0, ↓reduceIte, hsg0]
      · intro s hs hs0
        have : arc s ≠ (p.1, p.2) := fun has ↦
          hs0 (h4 s (Finset.mem_range.1 hs) 0 hL1 (has.trans harc0.symm))
        simp only [this, ↓reduceIte]
    have hDp : D p.1 p.2 ≠ 0 := by
      rw [hD]
      simp only [hDab, Int.cast_one]
      exact one_ne_zero
    set σ : ℤ := ∑ s ∈ range L, sg s with hσ
    have hDsum : ∑ i, ∑ j, D i j = σ := by
      rw [hD]
      have := sum_prefCount arc sg L
      rw [← hσ] at this
      rw [← this]
      push_cast
      rfl
    -- push along a total-preserving direction and recurse
    have hpush : ∀ E : S → S → ℝ, IsCirculation E → ∀ q : S × S, E q.1 q.2 ≠ 0 →
        (∀ i j, E i j ≠ 0 → y i j ∉ intLattice) → ∑ i, ∑ j, E i j = 0 →
        ∃ N : S → S → ℤ, ∃ a b : S,
        (∀ v, netFlow (fun i j ↦ (N i j : ℝ)) v =
          (if v = a then 1 else 0) - if v = b then 1 else 0) ∧
        (∀ i j, ⌊x i j⌋ ≤ N i j ∧ N i j ≤ ⌈x i j⌉) ∧ ∑ i, ∑ j, N i j = T := by
      intro E hEc q hq hEs hEsum
      obtain ⟨t, htc, htb, htcard⟩ := exists_push hyc hyb hEc hq hEs
      refine ih _ (hk ▸ htcard) _ htc htb ?_ rfl
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hEsum, mul_zero, add_zero]
      exact hyT
    by_cases hσ0 : σ = 0
    · exact hpush D hDc p hDp hDs (by rw [hDsum, hσ0, Int.cast_zero])
    set Δ : S → S → ℝ := fun i j ↦ y i j - n i j with hΔ
    have hΔc : IsCirculation Δ := (isCirculation_iff_netFlow Δ).2 fun v ↦ by
      rw [hΔ, netFlow_sub, (isCirculation_iff_netFlow y).1 hyc v,
        (isCirculation_iff_netFlow _).1 hnc v, sub_self]
    have hΔint : ∀ i j, y i j ∈ intLattice → Δ i j = 0 := fun i j hy ↦ by
      obtain ⟨m, hm⟩ := mem_intLattice.1 hy
      have h1 := (hnb i j).1
      have h2 := (hnb i j).2
      rw [← hm, Int.floor_intCast] at h1
      rw [← hm, Int.ceil_intCast] at h2
      have : n i j = m := le_antisymm h2 h1
      simp only [hΔ, ← hm, this, sub_self]
    have hΔs : ∀ i j, Δ i j ≠ 0 → y i j ∉ intLattice := fun i j h hy ↦ h (hΔint i j hy)
    set δ : ℤ := T - ∑ i, ∑ j, n i j with hδ
    have hΔsum : ∑ i, ∑ j, Δ i j = δ := by
      simp only [hΔ, Finset.sum_sub_distrib, hyT, hδ]
      push_cast
      rfl
    by_cases hmult : ∃ θ : ℝ, ∀ i j, Δ i j = θ * D i j
    · -- the finishing step: round along a prefix of the cycle
      obtain ⟨θ, hθ⟩ := hmult
      have hθp : Δ p.1 p.2 = θ := by
        rw [hθ, hD]
        simp only [hDab, Int.cast_one, mul_one]
      have hθ0 : θ ≠ 0 := by
        rw [← hθp]
        intro h0
        have hy := mem_fracSet.1 hp
        apply hy
        have : y p.1 p.2 = n p.1 p.2 := by
          have := h0
          simp only [hΔ, sub_eq_zero] at this
          exact this
        rw [this]
        exact intCast_mem_intLattice _
      have hθ1 : |θ| < 1 := by
        rw [← hθp]
        have := abs_sub_lt_one_of_floor_le_le_ceil (hnb p.1 p.2).1 (hnb p.1 p.2).2
        rw [abs_sub_comm] at this
        exact this
      have hδθ : (δ : ℝ) = θ * σ := by
        rw [← hΔsum, ← hDsum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ hθ i j
      set ε : ℤ := if 0 < θ then 1 else -1 with hε
      have hεθ : 0 < (ε : ℝ) * θ := by
        rw [hε]
        split_ifs with h
        · push_cast
          linarith
        · push_cast
          have : θ < 0 := lt_of_le_of_ne (not_lt.1 h) hθ0
          linarith
      have hεθ1 : (ε : ℝ) * θ < 1 := by
        rw [hε]
        split_ifs with h
        · push_cast
          linarith [abs_lt.1 hθ1]
        · push_cast
          linarith [abs_lt.1 hθ1]
      have hε2 : ε * ε = 1 := by
        rw [hε]
        split_ifs <;> norm_num
      -- the walk of partial sums
      let f : ℕ → ℤ := fun m ↦ ∑ s ∈ range m, sg s
      have hfstep : ∀ m < L, f (m + 1) = f m + 1 ∨ f (m + 1) = f m - 1 := fun m hm ↦ by
        simp only [f, Finset.sum_range_succ]
        rcases h2 m hm with ⟨hs, -⟩ | ⟨hs, -⟩
        · left
          rw [hs]
        · right
          rw [hs]
          ring
      have hεδ : ((ε * δ : ℤ) : ℝ) = ((ε : ℝ) * θ) * σ := by
        push_cast
        rw [hδθ]
        ring
      have hz : (f 0 ≤ ε * δ ∧ ε * δ ≤ f L) ∨ (f L ≤ ε * δ ∧ ε * δ ≤ f 0) := by
        have hf0 : f 0 = 0 := by simp only [f, Finset.range_zero, Finset.sum_empty]
        have hfL : f L = σ := rfl
        rw [hf0, hfL]
        rcases lt_or_gt_of_ne hσ0 with hneg | hpos
        · right
          have hσr : (σ : ℝ) < 0 := by exact_mod_cast hneg
          constructor
          · have : (σ : ℝ) ≤ ((ε * δ : ℤ) : ℝ) := by rw [hεδ]; nlinarith
            exact_mod_cast this
          · have : ((ε * δ : ℤ) : ℝ) ≤ 0 := by rw [hεδ]; nlinarith
            exact_mod_cast this
        · left
          have hσr : (0 : ℝ) < σ := by exact_mod_cast hpos
          constructor
          · have : (0 : ℝ) ≤ ((ε * δ : ℤ) : ℝ) := by rw [hεδ]; nlinarith
            exact_mod_cast this
          · have : ((ε * δ : ℤ) : ℝ) ≤ σ := by rw [hεδ]; nlinarith
            exact_mod_cast this
      obtain ⟨m, hmL, hfm⟩ := exists_eq_of_unit_steps f L hfstep (ε * δ) hz
      set N : S → S → ℤ := fun i j ↦ n i j + ε * prefCount arc sg m i j with hN
      have hnet : ∀ v, netFlow (fun i j ↦ (N i j : ℝ)) v =
          (ε : ℝ) * ((if v = C 0 then 1 else 0) - if v = C m then 1 else 0) := fun v ↦ by
        have hfun : (fun i j ↦ (N i j : ℝ)) = fun i j ↦
            (n i j : ℝ) + (ε : ℝ) * (prefCount arc sg m i j : ℝ) := by
          funext i j
          simp only [hN]
          push_cast
          rfl
        rw [hfun, netFlow_add, netFlow_mul, (isCirculation_iff_netFlow _).1 hnc v,
          netFlow_prefCount h2 hmL v, zero_add]
      have hbox : ∀ i j, ⌊x i j⌋ ≤ N i j ∧ N i j ≤ ⌈x i j⌉ := by
        intro i j
        by_cases h0 : prefCount arc sg m i j = 0
        · simp only [hN, h0, mul_zero, add_zero]
          exact ⟨le_trans (hfloor i j) (hnb i j).1, le_trans (hnb i j).2 (hceil i j)⟩
        · obtain ⟨s₀, hs₀, -, hm₀, hL₀⟩ := prefCount_ne_zero h4 hmL h0
          have hsg : sg s₀ = 1 ∨ sg s₀ = -1 := by
            rcases h2 s₀ (by omega) with ⟨hs, -⟩ | ⟨hs, -⟩
            · exact Or.inl hs
            · exact Or.inr hs
          have hΔij : Δ i j = θ * sg s₀ := by
            rw [hθ i j, hD]
            simp only [hL₀]
          have hNij : N i j = n i j + ε * sg s₀ := by simp only [hN, hm₀]
          have hc : (ε * sg s₀ = 1 ∧ 0 < Δ i j) ∨ (ε * sg s₀ = -1 ∧ Δ i j < 0) := by
            rw [hΔij]
            rcases hsg with hs | hs <;> rw [hs] <;>
              rcases (show ε = 1 ∨ ε = -1 by rw [hε]; split_ifs <;> simp only [true_or, or_true])
                with he | he <;> rw [he] at hεθ ⊢ <;> push_cast at hεθ ⊢
            · left; exact ⟨by norm_num, by linarith⟩
            · right; exact ⟨by norm_num, by linarith⟩
            · right; exact ⟨by norm_num, by linarith⟩
            · left; exact ⟨by norm_num, by linarith⟩
          rcases hc with ⟨hc1, hpos⟩ | ⟨hc1, hneg⟩
          · rw [hNij, hc1]
            have hlt : (n i j : ℝ) < y i j := by
              have := hpos
              simp only [hΔ, sub_pos] at this
              exact this
            have h1 : n i j < ⌈y i j⌉ := Int.lt_ceil.2 hlt
            constructor
            · have := le_trans (hfloor i j) (hnb i j).1
              omega
            · have := hceil i j
              omega
          · rw [hNij, hc1]
            have hlt : y i j < n i j := by
              have := hneg
              simp only [hΔ, sub_neg] at this
              exact this
            have h1 : ⌊y i j⌋ < n i j := Int.floor_lt.2 hlt
            constructor
            · have := hfloor i j
              omega
            · have := le_trans (hnb i j).2 (hceil i j)
              omega
      have htot : ∑ i, ∑ j, N i j = T := by
        simp only [hN, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [sum_prefCount, show (∑ s ∈ range m, sg s) = f m from rfl, hfm, ← mul_assoc, hε2,
          one_mul, hδ]
        ring
      rcases (show ε = 1 ∨ ε = -1 by rw [hε]; split_ifs <;> simp only [true_or, or_true])
        with he | he
      · refine ⟨N, C 0, C m, fun v ↦ ?_, hbox, htot⟩
        rw [hnet, he]
        push_cast
        ring
      · refine ⟨N, C m, C 0, fun v ↦ ?_, hbox, htot⟩
        rw [hnet, he]
        push_cast
        ring
    · -- two independent directions: combine them into a total-preserving one
      push Not at hmult
      set E : S → S → ℝ := fun i j ↦ (σ : ℝ) * Δ i j - (δ : ℝ) * D i j with hE
      have hEc : IsCirculation E := (isCirculation_iff_netFlow E).2 fun v ↦ by
        rw [hE, netFlow_sub, netFlow_mul, netFlow_mul, (isCirculation_iff_netFlow _).1 hΔc v,
          (isCirculation_iff_netFlow _).1 hDc v, mul_zero, mul_zero, sub_self]
      have hEs : ∀ i j, E i j ≠ 0 → y i j ∉ intLattice := fun i j h ↦ by
        by_contra hy
        apply h
        have h1 := hΔint i j hy
        have h2 : D i j = 0 := by
          by_contra hd
          exact hDs i j hd hy
        simp only [hE, h1, h2, mul_zero, sub_zero]
      have hEsum : ∑ i, ∑ j, E i j = 0 := by
        simp only [hE, Finset.sum_sub_distrib, ← Finset.mul_sum, hΔsum, hDsum]
        ring
      have hσr : (σ : ℝ) ≠ 0 := by exact_mod_cast hσ0
      obtain ⟨i, j, hij⟩ := hmult ((δ : ℝ) / σ)
      have hEij : E i j ≠ 0 := by
        intro h0
        apply hij
        simp only [hE, sub_eq_zero] at h0
        field_simp
        linarith
      exact hpush E hEc (i, j) hEij hEs hEsum
  exact key _ x hx (fun i j ↦ ⟨Int.floor_le _, Int.le_ceil _⟩) hT rfl

/-! ### Exactly `T` transitions: post #3's conditional MC -/

omit [Fintype S] in
/-- `if v = a` versus `if a = v`, cast from `ℤ`. -/
theorem ite_eq_intCast_ite (v a : S) :
    (if v = a then (1 : ℝ) else 0) = ((if a = v then (1 : ℤ) else 0 : ℤ) : ℝ) := by
  by_cases h : v = a
  · subst h
    simp only [↓reduceIte, Int.cast_one]
  · simp only [h, Ne.symm h, ↓reduceIte, Int.cast_zero]

/-- Net outflows `1{a} − 1{b}` of an integer matrix are `BalancedCounts` from `a` to `b`. -/
theorem balancedCounts_of_netFlow {N₀ : S → S → ℤ} {N : S → S → ℕ}
    (hNz : ∀ i j, ((N i j : ℕ) : ℤ) = N₀ i j) {a b : S}
    (h : ∀ v, netFlow (fun i j ↦ (N₀ i j : ℝ)) v =
      (if v = a then 1 else 0) - if v = b then 1 else 0) :
    BalancedCounts N a b := by
  intro i
  simp only [hNz]
  have hi := h i
  unfold netFlow at hi
  beta_reduce at hi
  rw [ite_eq_intCast_ite, ite_eq_intCast_ite] at hi
  have hz : (∑ j, N₀ i j) - ∑ j, N₀ j i =
      (if a = i then (1 : ℤ) else 0) - if b = i then 1 else 0 := by
    exact_mod_cast hi
  rw [hz]

/-- **A path with exactly `T` transitions realising rounded counts** (post #3, conditional MC,
"allowing for the first and last states"): for an irreducible stochastic `P` with stationary
probability vector `π`, an integer `T` with `T π_i p_ij ≥ 1` on the support of `P`, there are
states `a`, `b` and counts `N` with `|N_ij − T π_i p_ij| < 1`, the support of `P`, total exactly
`T`, balanced from `a` to `b`, and a path `a = s_0, …, s_T = b` with exactly these transition
counts. -/
theorem exists_path_exact_length [Nonempty S] {P : S → S → ℝ} (hP : IsStochastic P)
    {w : S → ℝ} (hw : IsStationaryRow P w) (hw1 : ∑ i, w i = 1) {T : ℕ}
    (hT : ∀ i j, 0 < P i j → 1 ≤ expectedCounts P w T i j)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b ↦ 0 < P a b) i j) :
    ∃ N : S → S → ℕ, ∃ a b : S, (∀ i j, |(N i j : ℝ) - expectedCounts P w T i j| < 1) ∧
      (∀ i j, N i j ≠ 0 ↔ 0 < P i j) ∧ BalancedCounts N a b ∧ ∑ i, ∑ j, N i j = T ∧
      ∃ s : ℕ → S, s 0 = a ∧ s T = b ∧ ∀ i j, transCount s i j T = N i j := by
  have hsum : ∑ i, ∑ j, expectedCounts P w T i j = ((T : ℤ) : ℝ) := by
    rw [sum_expectedCounts hP hw1, Int.cast_natCast]
  obtain ⟨N₀, a, b, hnet, hb, htot⟩ :=
    exists_open_rounding (isCirculation_expectedCounts hP hw T) hsum
  have hzero : ∀ i j, P i j = 0 → expectedCounts P w T i j = 0 := fun i j h ↦ by
    rw [expectedCounts, h, mul_zero]
  have hn0 : ∀ i j, 0 ≤ N₀ i j := fun i j ↦ by
    rcases (hP.nonneg i j).lt_or_eq with h | h
    · exact le_trans (Int.floor_nonneg.2 (le_trans zero_le_one (hT i j h))) (hb i j).1
    · exact le_trans (by rw [hzero i j h.symm, Int.floor_zero]) (hb i j).1
  set N : S → S → ℕ := fun i j ↦ (N₀ i j).toNat with hN
  have hNz : ∀ i j, ((N i j : ℕ) : ℤ) = N₀ i j := fun i j ↦ Int.toNat_of_nonneg (hn0 i j)
  have hNr : ∀ i j, ((N i j : ℕ) : ℝ) = N₀ i j := fun i j ↦ by
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
      have h1 : 1 ≤ N₀ i j := le_trans (Int.le_floor.2 (by exact_mod_cast hT i j hp)) (hb i j).1
      have h' := hNz i j
      omega
  have hbal : BalancedCounts N a b := balancedCounts_of_netFlow hNz hnet
  have hNT : ∑ i, ∑ j, N i j = T := by
    have : ((∑ i, ∑ j, N i j : ℕ) : ℤ) = (T : ℤ) := by
      push_cast
      simp only [hNz]
      exact htot
    exact_mod_cast this
  have hconn : ∀ i j, N i j ≠ 0 → Relation.ReflTransGen (fun a b ↦ N a b ≠ 0) a i :=
    fun i _ _ ↦ Relation.ReflTransGen.mono (fun a b h ↦ (hsupp a b).2 h) a i (hirr a i)
  obtain ⟨s, hs0, hsT, hsN⟩ := exists_path_of_balanced hbal hconn
  rw [hNT] at hsT hsN
  have habs : ∀ i j, |(N i j : ℝ) - expectedCounts P w T i j| < 1 := fun i j ↦ by
    rw [hNr]
    exact abs_sub_lt_one_of_floor_le_le_ceil (hb i j).1 (hb i j).2
  exact ⟨N, a, b, habs, hsupp, hbal, hNT, s, hs0, hsT, hsN⟩

/-- **Post #3's conditional MC with exactly `T` transitions is well defined**: with the counts
`N` and start `a` of `exists_path_exact_length`, the event "MC from `a` has transition counts `N`
over `T` steps" has positive probability, and conditionally on it the MC path is uniform over
the paths with these counts. -/
theorem conditionalMC_exact_wellDefined {m : ℕ} [Nonempty (Fin m)] {P : Fin m → Fin m → ℝ}
    (hP : IsStochastic P) {w : Fin m → ℝ} (hw : IsStationaryRow P w) (hw1 : ∑ i, w i = 1)
    {T : ℕ} (hT : ∀ i j, 0 < P i j → 1 ≤ expectedCounts P w T i j)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b ↦ 0 < P a b) i j) :
    ∃ N : Fin m → Fin m → ℕ, ∃ a b : Fin m,
      (∀ i j, |(N i j : ℝ) - expectedCounts P w T i j| < 1) ∧ BalancedCounts N a b ∧
      ∑ i, ∑ j, N i j = T ∧ mcLaw P a T (countClass a N T : Set _) ≠ 0 ∧
      (mcLaw P a T)[|(countClass a N T : Set _)] = uniformOn (countClass a N T : Set _) := by
  obtain ⟨N, a, b, habs, hsupp, hbal, hNT, s, hs0, -, hsN⟩ :=
    exists_path_exact_length hP hw hw1 hT hirr
  set sv : Fin (T + 1) → Fin m := fun t ↦ s t with hsv
  have hagree : ∀ t ≤ T, s t = extendPath sv t := (extendPath_eq_iff s sv).1 rfl
  have hmem : sv ∈ countClass a N T := by
    rw [mem_countClass]
    refine ⟨(hagree 0 (Nat.zero_le T)).symm.trans hs0, fun i j ↦ ?_⟩
    rw [← transCount_congr hagree i j]
    exact hsN i j
  have hpos : 0 < mcLaw P a T {sv} := by
    rw [mcLaw_singleton_of_mem hP a N T hmem, ENNReal.ofReal_pos]
    refine Finset.prod_pos fun i _ ↦ Finset.prod_pos fun j _ ↦ ?_
    by_cases h : N i j = 0
    · rw [h, pow_zero]
      exact one_pos
    · exact pow_pos ((hsupp i j).1 h) _
  have hC : mcLaw P a T (countClass a N T : Set _) ≠ 0 :=
    (lt_of_lt_of_le hpos (measure_mono (Set.singleton_subset_iff.2 (Finset.mem_coe.2 hmem)))).ne'
  exact ⟨N, a, b, habs, hbal, hNT, hC, cond_mcLaw_countClass hP a N T hC⟩

/-- The flip chain at `T = 3`: the open path `0 → 1 → 0 → 1` has the counts `n_01 = 2`,
`n_10 = 1`, within `1` of `x_01 = x_10 = 3/2`, total `3`, balanced from `0` to `1` (the open
rounding of `exists_open_rounding` that the closed one of
`not_exists_rounding_flipChain_total_three` cannot provide). -/
theorem flipChain_open_path_three :
    let s : ℕ → Fin 2 := fun t ↦ if t % 2 = 0 then 0 else 1
    transCount s 0 1 3 = 2 ∧ transCount s 1 0 3 = 1 ∧ transCount s 0 0 3 = 0 ∧
      transCount s 1 1 3 = 0 := by
  intro s
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

end RQMCMarkov.MarkovDriving

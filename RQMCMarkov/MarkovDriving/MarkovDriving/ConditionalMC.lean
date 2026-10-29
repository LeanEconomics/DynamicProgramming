/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.DrivingMC

/-!
# Conditional MC: given its transition counts, the MC path is uniform (post #3)

Post #3's "conditional MC" fixes the transition counts `n_ij` and samples "uniformly among all
paths with those counts", noting that "these paths are Eulerian trails"; its approach (v), a
uniformly random path with the counts of the rotor path, "is exactly MC conditional on the
counts". Reading: for MC from a fixed start `x₀`, conditioning the law of `(x_0, …, x_T)` on the
event "transition counts equal `N`" gives the uniform distribution on the paths that start at
`x₀` and have counts `N` (the start is part of the conditioning: the counts determine the end
state but, for a circulation, not the start).

## Main results

* `prod_eq_prod_pow_transCount`, `pathProb_eq_prod_pow`, `pathProb_eq_of_transCount_eq`: a
  path's MC probability is `1{s_0 = x₀} ∏_{i,j} P i j ^ transCount s i j T`, so it depends only
  on the start and the transition counts.
* `countClass x₀ N T`, `mem_countClass`: the finite paths with start `x₀` and counts `N`;
  `mcLaw P x₀ T`, the MC law of `(x_0, …, x_T)`; `mcLaw_singleton_of_mem`.
* `cond_mcLaw_countClass`: **MC conditional on the counts is uniform**,
  `(mcLaw P x₀ T)[| countClass x₀ N T] = uniformOn (countClass x₀ N T)` whenever the conditioning
  event has positive probability. (By `map_drivenPath_eq_map_stackPath` the same holds for i.i.d.
  stacks.)
* `BalancedCounts N a b` (out-count − in-count `= 1{a = i} − 1{b = i}`), `balanced_transCount`.
* `exists_path_of_balanced`: **Euler's theorem** for directed multigraphs — balanced counts
  whose support is reachable from `x₀` are the transition counts of some path from `x₀` to `b`
  of length `Σ N` (an Eulerian trail). Proof: a longest trail ends at `b` and leaves a
  circulation (`IsCountTrail.end_eq`); if anything is unused, a closed trail of the circulation
  (`exists_closed_trail`) can be spliced in at a visited state (`transCount_splice`),
  contradicting maximality.
* `reachable_of_transCount_ne_zero`, `exists_path_iff`: conversely, the counts of any path are
  balanced and connected, so these conditions characterise the realisable count matrices.

Not formalised: the BEST theorem (counting Eulerian trails via spanning trees) and the exact
sampler built on it (post #3: "the BEST theorem with a random spanning tree gives an exact
sampler"). The rounding of `T π_i p_ij` to balanced integer counts is in `ConditionalMCRounding`
and `ConditionalMCRoundingOpen`.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- One transition, as a product of powers: `∏_{i,j} f i j ^ 1{a = i ∧ b = j} = f a b`. -/
theorem prod_prod_pow_ite_eq (f : S → S → ℝ) (a b : S) :
    ∏ i, ∏ j, f i j ^ (if a = i ∧ b = j then 1 else 0) = f a b := by
  rw [Fintype.prod_eq_single a fun i hi ↦ Finset.prod_eq_one fun j _ ↦ by
    simp only [Ne.symm hi, false_and, ↓reduceIte, pow_zero]]
  rw [Fintype.prod_eq_single b fun j hj ↦ by simp only [Ne.symm hj, and_false, ↓reduceIte,
    pow_zero]]
  simp only [and_self, ↓reduceIte, pow_one]

/-- **The path probability depends only on the transition counts** (post #3, conditional MC):
`∏_{t<T} P (s t) (s (t+1)) = ∏_{i,j} P i j ^ transCount s i j T`. -/
theorem prod_eq_prod_pow_transCount (P : S → S → ℝ) (s : ℕ → S) (T : ℕ) :
    ∏ t ∈ range T, P (s t) (s (t + 1)) = ∏ i, ∏ j, P i j ^ transCount s i j T := by
  induction T with
  | zero =>
    rw [Finset.prod_range_zero]
    exact (Finset.prod_eq_one fun i _ ↦ Finset.prod_eq_one fun j _ ↦ pow_zero _).symm
  | succ T ih =>
    rw [Finset.prod_range_succ, ih]
    simp only [transCount_succ, pow_add]
    rw [← prod_prod_pow_ite_eq P (s T) (s (T + 1)), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ (Finset.prod_mul_distrib).symm

/-- `pathProb` through the transition counts. -/
theorem pathProb_eq_prod_pow (P : S → S → ℝ) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    pathProb P x₀ s T = if s 0 = x₀ then ∏ i, ∏ j, P i j ^ transCount s i j T else 0 := by
  unfold pathProb
  rw [prod_eq_prod_pow_transCount]

omit [Fintype S] in
/-- Two paths with the same start and the same transition counts have the same probability
under MC. -/
theorem pathProb_eq_of_transCount_eq [Finite S] (P : S → S → ℝ) (x₀ : S) {s s' : ℕ → S}
    {T : ℕ} (h0 : s 0 = s' 0) (hN : ∀ i j, transCount s i j T = transCount s' i j T) :
    pathProb P x₀ s T = pathProb P x₀ s' T := by
  have := Fintype.ofFinite S
  rw [pathProb_eq_prod_pow, pathProb_eq_prod_pow, h0]
  simp only [hN]

/-- The finite paths `(s_0, …, s_T)` that start at `x₀` and have transition counts `N`. -/
noncomputable def countClass (x₀ : S) (N : S → S → ℕ) (T : ℕ) : Finset (Fin (T + 1) → S) :=
  univ.filter fun s ↦ extendPath s 0 = x₀ ∧ ∀ i j, transCount (extendPath s) i j T = N i j

/-- Membership in `countClass`. -/
theorem mem_countClass {x₀ : S} {N : S → S → ℕ} {T : ℕ} {s : Fin (T + 1) → S} :
    s ∈ countClass x₀ N T ↔
      extendPath s 0 = x₀ ∧ ∀ i j, transCount (extendPath s) i j T = N i j := by
  unfold countClass
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ s)

variable {n : ℕ}

/-- The law of the first `T + 1` states of MC: `drivenPath` under i.i.d. uniforms. -/
noncomputable def mcLaw (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (T : ℕ) :
    Measure (Fin (T + 1) → Fin n) :=
  (iidUniform ℕ).map fun u t ↦ drivenPath P x₀ u (t : Fin (T + 1))

/-- Under MC, every path of `countClass x₀ N T` has probability `∏_{i,j} P i j ^ N i j`. -/
theorem mcLaw_singleton_of_mem {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (N : Fin n → Fin n → ℕ) (T : ℕ) {s : Fin (T + 1) → Fin n} (hs : s ∈ countClass x₀ N T) :
    mcLaw P x₀ T {s} = ENNReal.ofReal (∏ i, ∏ j, P i j ^ N i j) := by
  unfold mcLaw
  rw [map_drivenPath_singleton hP, pathProb_eq_prod_pow]
  rw [mem_countClass] at hs
  simp only [hs.1, hs.2, ↓reduceIte]

/-- **MC conditional on the counts is uniform** (post #3: the uniformly random path with fixed
counts "is exactly MC conditional on the counts"): conditioned on starting at `x₀` and having
transition counts `N` (an event of positive probability), the law of the MC path
`(x_0, …, x_T)` is the uniform distribution on the paths with those counts. -/
theorem cond_mcLaw_countClass {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (N : Fin n → Fin n → ℕ) (T : ℕ) (hC : mcLaw P x₀ T (countClass x₀ N T : Set _) ≠ 0) :
    (mcLaw P x₀ T)[|(countClass x₀ N T : Set _)] = uniformOn (countClass x₀ N T : Set _) := by
  set C := countClass x₀ N T with hCdef
  set m := ENNReal.ofReal (∏ i, ∏ j, P i j ^ N i j) with hm
  have hμC : mcLaw P x₀ T (C : Set _) = (C.card : ℝ≥0∞) * m := by
    rw [← sum_measure_singleton, Finset.sum_congr rfl fun s hs ↦
      mcLaw_singleton_of_mem hP x₀ N T hs, Finset.sum_const, nsmul_eq_mul]
  have hm0 : m ≠ 0 := by
    intro h
    rw [hμC, h, mul_zero] at hC
    exact hC rfl
  have hk0 : (C.card : ℝ≥0∞) ≠ 0 := by
    intro h
    rw [hμC, h, zero_mul] at hC
    exact hC rfl
  refine Measure.ext_of_singleton fun s ↦ ?_
  rw [cond_apply C.measurableSet, ← Finset.coe_singleton, uniformOn_apply_finset]
  by_cases hs : s ∈ C
  · rw [Finset.inter_singleton_of_mem hs, Finset.coe_singleton, Set.inter_eq_right.2
      (Set.singleton_subset_iff.2 hs), mcLaw_singleton_of_mem hP x₀ N T hs, hμC, ← hm,
      Finset.card_singleton, Nat.cast_one, one_div,
      ENNReal.mul_inv (Or.inl hk0) (Or.inr hm0), mul_assoc,
      ENNReal.inv_mul_cancel hm0 ENNReal.ofReal_ne_top, mul_one]
  · rw [Finset.inter_singleton_of_notMem hs, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div,
      Finset.coe_singleton, Set.inter_singleton_eq_empty.2 hs, measure_empty, mul_zero]

/-! ### Euler's theorem for count matrices -/

/-- A count matrix `N` is **balanced from `a` to `b`**: at every state, out-count minus
in-count is `1{a = i} − 1{b = i}` (post #3, "every state is entered as often as it is left
(allowing for the first and last states)"). With `a = b` this is a circulation. -/
def BalancedCounts (N : S → S → ℕ) (a b : S) : Prop :=
  ∀ i, (∑ j, (N i j : ℤ)) - ∑ j, (N j i : ℤ) = (if a = i then 1 else 0) - if b = i then 1 else 0

/-- The transition counts of any path are balanced from its start to its end. -/
theorem balanced_transCount (s : ℕ → S) (T : ℕ) :
    BalancedCounts (fun i j ↦ transCount s i j T) (s 0) (s T) := by
  intro i
  have := flowBalance s i T
  push_cast at this
  exact this

omit [Fintype S] in
/-- A **trail** of length `L` from `x₀` in the count matrix `N`: a path from `x₀` whose first
`L` transitions use each `i → j` at most `N i j` times. -/
def IsCountTrail (N : S → S → ℕ) (x₀ : S) (s : ℕ → S) (L : ℕ) : Prop :=
  s 0 = x₀ ∧ ∀ i j, transCount s i j L ≤ N i j

omit [Fintype S] in
/-- The empty trail. -/
theorem isCountTrail_zero (N : S → S → ℕ) (x₀ : S) : IsCountTrail N x₀ (fun _ ↦ x₀) 0 :=
  ⟨rfl, fun i j ↦ (transCount_zero _ i j).symm ▸ Nat.zero_le _⟩

/-- A trail is no longer than the total count. -/
theorem IsCountTrail.le_sum {N : S → S → ℕ} {x₀ : S} {s : ℕ → S} {L : ℕ}
    (h : IsCountTrail N x₀ s L) : L ≤ ∑ i, ∑ j, N i j := by
  rw [← sum_sum_transCount s L]
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ h.2 i j

omit [Fintype S] in
/-- A trail can be extended by any unused transition out of its endpoint. -/
theorem IsCountTrail.extend {N : S → S → ℕ} {x₀ : S} {s : ℕ → S} {L : ℕ} (h : IsCountTrail N x₀ s L)
    (z : S) (hz : transCount s (s L) z L < N (s L) z) :
    IsCountTrail N x₀ (Function.update s (L + 1) z) (L + 1) := by
  have hagree : ∀ t ≤ L, Function.update s (L + 1) z t = s t := fun t ht ↦
    Function.update_of_ne (by omega) _ _
  refine ⟨?_, fun i j ↦ ?_⟩
  · rw [hagree 0 (Nat.zero_le L)]
    exact h.1
  · rw [transCount_succ, transCount_congr hagree, hagree L le_rfl, Function.update_self]
    by_cases hij : s L = i ∧ z = j
    · obtain ⟨rfl, rfl⟩ := hij
      simp only [and_self, ↓reduceIte]
      omega
    · simp only [hij, ↓reduceIte, add_zero]
      exact h.2 i j

omit [Fintype S] in
/-- A trail of maximal length exists (finite state space). -/
theorem exists_maximal_trail [Finite S] (N : S → S → ℕ) (x₀ : S) :
    ∃ L s, IsCountTrail N x₀ s L ∧ ∀ L' s', IsCountTrail N x₀ s' L' → L' ≤ L := by
  classical
  have := Fintype.ofFinite S
  let Q : ℕ → Prop := fun L ↦ ∃ s, IsCountTrail N x₀ s L
  have hQ0 : Q 0 := ⟨_, isCountTrail_zero N x₀⟩
  obtain ⟨s, hs⟩ := Nat.findGreatest_spec (P := Q) (Nat.zero_le (∑ i, ∑ j, N i j)) hQ0
  exact ⟨_, s, hs, fun L' s' h' ↦ Nat.le_findGreatest h'.le_sum ⟨s', h'⟩⟩

/-- **A trail that cannot be extended ends at `b`**, for counts balanced from `a` to `b`, and
the unused counts form a circulation. -/
theorem IsCountTrail.end_eq {N : S → S → ℕ} {x₀ y : S} (hbal : BalancedCounts N x₀ y) {s : ℕ → S}
    {L : ℕ} (h : IsCountTrail N x₀ s L) (hmax : ∀ z, N (s L) z ≤ transCount s (s L) z L) :
    s L = y ∧ ∀ a, BalancedCounts (fun i j ↦ N i j - transCount s i j L) a a := by
  have hcast : ∀ i j, ((N i j - transCount s i j L : ℕ) : ℤ) = N i j - transCount s i j L :=
    fun i j ↦ Nat.cast_sub (h.2 i j)
  have hdiff : ∀ v, (∑ j, ((N v j - transCount s v j L : ℕ) : ℤ)) -
      ∑ j, ((N j v - transCount s j v L : ℕ) : ℤ) =
        (if s L = v then 1 else 0) - if y = v then 1 else 0 := by
    intro v
    simp only [hcast, Finset.sum_sub_distrib]
    have h1 := hbal v
    have h2 := balanced_transCount s L v
    rw [h.1] at h2
    linarith
  have hout : ∑ j, ((N (s L) j - transCount s (s L) j L : ℕ) : ℤ) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ by rw [Nat.sub_eq_zero_of_le (hmax j), Nat.cast_zero]
  have hin : 0 ≤ ∑ j, ((N j (s L) - transCount s j (s L) L : ℕ) : ℤ) :=
    Finset.sum_nonneg fun j _ ↦ Nat.cast_nonneg _
  have hend : s L = y := by
    by_contra hne
    have := hdiff (s L)
    rw [hout] at this
    simp only [↓reduceIte, Ne.symm hne] at this
    linarith
  refine ⟨hend, fun a v ↦ ?_⟩
  rw [hdiff v, hend, sub_self, sub_self]

/-- **A circulation with an edge out of `v` contains a closed trail at `v`.** -/
theorem exists_closed_trail {R : S → S → ℕ} {v : S} (hbal : BalancedCounts R v v) {j : S}
    (hj : R v j ≠ 0) : ∃ K c, 1 ≤ K ∧ IsCountTrail R v c K ∧ c K = v := by
  obtain ⟨L, c, hc, hmax⟩ := exists_maximal_trail R v
  have hnext : ∀ z, R (c L) z ≤ transCount c (c L) z L := fun z ↦ by
    by_contra hz
    have := hmax _ _ (hc.extend z (not_le.1 hz))
    omega
  have h1 : 1 ≤ L := hmax 1 _ ((isCountTrail_zero R v).extend j (by
    rw [transCount_zero]
    exact Nat.pos_of_ne_zero hj))
  exact ⟨L, c, h1, hc, (hc.end_eq hbal hnext).1⟩

omit [Fintype S] in
/-- **Splicing** a path `c` into `s` at time `t₀`: follow `s` up to `t₀`, then `c` for `K`
steps, then the rest of `s`. -/
def splice (s c : ℕ → S) (t₀ K : ℕ) (t : ℕ) : S :=
  if t ≤ t₀ then s t else if t ≤ t₀ + K then c (t - t₀) else s (t - K)

omit [Fintype S] in
/-- Splicing a closed path `c` at a visit of `s` to its base point adds the counts. -/
theorem transCount_splice {s c : ℕ → S} {t₀ K L : ℕ} (hc0 : c 0 = s t₀) (hcK : c K = s t₀)
    (ht₀ : t₀ ≤ L) (i j : S) :
    transCount (splice s c t₀ K) i j (L + K) = transCount s i j L + transCount c i j K := by
  have hL : L + K = t₀ + (K + (L - t₀)) := by omega
  have h1 : transCount (splice s c t₀ K) i j t₀ = transCount s i j t₀ :=
    transCount_congr (fun t ht ↦ by simp only [splice, ht, ↓reduceIte]) i j
  have h2 : transCount (fun t ↦ splice s c t₀ K (t₀ + t)) i j K = transCount c i j K := by
    refine transCount_congr (fun t ht ↦ ?_) i j
    unfold splice
    split_ifs with h h'
    · rw [show t = 0 by omega, add_zero, hc0]
    · rw [Nat.add_sub_cancel_left]
    · omega
  have h3 : transCount (fun t ↦ splice s c t₀ K (t₀ + (K + t))) i j (L - t₀) =
      transCount (fun t ↦ s (t₀ + t)) i j (L - t₀) := by
    refine transCount_congr (fun t _ ↦ ?_) i j
    unfold splice
    split_ifs with h h'
    · rw [show t = 0 by omega, show K = 0 by omega]
    · rw [show t = 0 by omega, add_zero, Nat.add_sub_cancel_left, hcK, add_zero]
    · congr 1
      omega
  have h4 := transCount_add s i j t₀ (L - t₀)
  rw [Nat.add_sub_cancel' ht₀] at h4
  rw [hL, transCount_add, transCount_add (fun t ↦ splice s c t₀ K (t₀ + t)), h1, h2, h3, h4]
  ring

/-- **Euler's theorem for directed multigraphs** (post #3: "these paths are Eulerian trails"):
if the count matrix `N` is balanced from `x₀` to `y` and every state with an outgoing count is
reachable from `x₀` through positive counts, then some path from `x₀` to `y` of length
`T = Σ N` realises exactly the counts `N`. -/
theorem exists_path_of_balanced {N : S → S → ℕ} {x₀ y : S} (hbal : BalancedCounts N x₀ y)
    (hconn : ∀ i j, N i j ≠ 0 → Relation.ReflTransGen (fun a b ↦ N a b ≠ 0) x₀ i) :
    ∃ s : ℕ → S, s 0 = x₀ ∧ s (∑ i, ∑ j, N i j) = y ∧
      ∀ i j, transCount s i j (∑ i, ∑ j, N i j) = N i j := by
  obtain ⟨L, s, hs, hmax⟩ := exists_maximal_trail N x₀
  have hnext : ∀ z, N (s L) z ≤ transCount s (s L) z L := fun z ↦ by
    by_contra hz
    have := hmax _ _ (hs.extend z (not_le.1 hz))
    omega
  obtain ⟨hend, hR⟩ := hs.end_eq hbal hnext
  by_cases hzero : ∀ i j, N i j - transCount s i j L = 0
  · have hC : ∀ i j, transCount s i j L = N i j := fun i j ↦
      le_antisymm (hs.2 i j) (Nat.sub_eq_zero_iff_le.1 (hzero i j))
    have hLT : L = ∑ i, ∑ j, N i j := by
      rw [← sum_sum_transCount s L]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hC i j
    rw [← hLT]
    exact ⟨s, hs.1, hend, hC⟩
  · exfalso
    push Not at hzero
    obtain ⟨a, b, hab⟩ := hzero
    have hon : ∃ t₀ ≤ L, ∃ j, N (s t₀) j - transCount s (s t₀) j L ≠ 0 := by
      by_contra hno
      push Not at hno
      have key : ∀ v, Relation.ReflTransGen (fun a b ↦ N a b ≠ 0) x₀ v → ∃ t ≤ L, s t = v := by
        intro v hv
        induction hv with
        | refl => exact ⟨0, Nat.zero_le L, hs.1⟩
        | @tail b' c' _ hbc ih =>
          obtain ⟨t, ht, rfl⟩ := ih
          have hpos : transCount s (s t) c' L ≠ 0 := by
            have := hno t ht c'
            omega
          obtain ⟨t', ht'⟩ := Finset.card_ne_zero.1 hpos
          rw [Finset.mem_filter, Finset.mem_range] at ht'
          exact ⟨t' + 1, ht'.1, ht'.2.2⟩
      obtain ⟨t, ht, hst⟩ := key a (hconn a b (by omega))
      exact hab (hst ▸ hno t ht b)
    obtain ⟨t₀, ht₀, j, hj⟩ := hon
    obtain ⟨K, c, hK, hc, hcK⟩ := exists_closed_trail (hR (s t₀)) hj
    have htrail : IsCountTrail N x₀ (splice s c t₀ K) (L + K) := by
      refine ⟨by simp only [splice, Nat.zero_le, ↓reduceIte, hs.1], fun i j ↦ ?_⟩
      rw [transCount_splice hc.1 hcK ht₀]
      have h1 := hc.2 i j
      have h2 := hs.2 i j
      beta_reduce at h1
      omega
    have := hmax _ _ htrail
    omega

omit [Fintype S] in
/-- **Converse of Euler's theorem**: the support of the transition counts of a path is
reachable from its start. -/
theorem reachable_of_transCount_ne_zero (s : ℕ → S) (T : ℕ) {i j : S}
    (h : transCount s i j T ≠ 0) :
    Relation.ReflTransGen (fun a b ↦ transCount s a b T ≠ 0) (s 0) i := by
  obtain ⟨t, ht⟩ := Finset.card_ne_zero.1 h
  rw [Finset.mem_filter, Finset.mem_range] at ht
  rw [← ht.2.1]
  have key : ∀ t' ≤ t, Relation.ReflTransGen (fun a b ↦ transCount s a b T ≠ 0) (s 0) (s t') := by
    intro t' ht'
    induction t' with
    | zero => exact Relation.ReflTransGen.refl
    | succ t' ih =>
      refine (ih (by omega)).tail ?_
      refine Finset.card_ne_zero.2 ⟨t', ?_⟩
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, rfl, rfl⟩
  exact key t le_rfl

/-- **Paths with given counts exist iff the counts are balanced and connected**: there is a
path of length `T = Σ N` from `x₀` to `y` with transition counts exactly `N` iff `N` is
balanced from `x₀` to `y` and its support is reachable from `x₀`. -/
theorem exists_path_iff {N : S → S → ℕ} {x₀ y : S} :
    (∃ s : ℕ → S, s 0 = x₀ ∧ s (∑ i, ∑ j, N i j) = y ∧
      ∀ i j, transCount s i j (∑ i, ∑ j, N i j) = N i j) ↔
    BalancedCounts N x₀ y ∧
      ∀ i j, N i j ≠ 0 → Relation.ReflTransGen (fun a b ↦ N a b ≠ 0) x₀ i := by
  constructor
  · rintro ⟨s, h0, hT, hN⟩
    have hfun : N = fun i j ↦ transCount s i j (∑ i, ∑ j, N i j) :=
      funext fun i ↦ funext fun j ↦ (hN i j).symm
    constructor
    · have := balanced_transCount s (∑ i, ∑ j, N i j)
      rw [h0, hT, ← hfun] at this
      exact this
    · intro i j hij
      have := reachable_of_transCount_ne_zero s (∑ i, ∑ j, N i j) (i := i) (j := j)
        (by rw [hN]; exact hij)
      have hr : (fun a b ↦ transCount s a b (∑ i, ∑ j, N i j) ≠ 0) = fun a b ↦ N a b ≠ 0 := by
        funext a b
        rw [hN]
      rw [h0, hr] at this
      exact this
  · rintro ⟨hbal, hconn⟩
    exact exists_path_of_balanced hbal hconn

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.FiniteErgodic

/-!
# Finite Markov chains: the block form of `Q`

SLP §11.1, Exercise 11.1, pp. 329–330. Let `G` (`recSet`) be the union of the ergodic sets; by
Theorem 11.1a its complement is the transient set `F`.

* `tendsto_tail`: the probability `Πⁿ(i, F)` of still being in `F` after `n` steps tends to `0`.
  Every state reaches `G` with positive probability within `n₀` steps, so `Πⁿ⁰(i, F) ≤ 1 − δ`
  for all `i`, and `G` is closed, so `Π^{kn₀}(i, F) ≤ (1 − δ)ᵏ`.
* **Exercise 11.1** (`ex_11_1`):
  * the columns of `Q` for transient states are zero;
  * the rows of `Q` for an ergodic set `E` vanish outside `E`, and are all equal;
  * the absorption probabilities `w_E(i) = lim Πⁿ(i, E)` exist and sum to one over the ergodic
    sets, and `Qᵢⱼ = Σ_E w_E(i) q_E(j)`, with `q_E` the common row of `Q` on `E`.

  The book writes the transient block as `w_j Q_j`, an outer product of the column `w_j` and the
  common row of `Q_j`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- The ergodic sets. -/
noncomputable def ergSets (P : Matrix S S ℝ) : Finset (Finset S) := by
  classical exact univ.filter (IsErgodic P)

/-- The recurrent states: the union `G` of the ergodic sets. -/
noncomputable def recSet (P : Matrix S S ℝ) : Finset S := (ergSets P).biUnion id

omit [DecidableEq S] in
theorem mem_ergSets {E : Finset S} : E ∈ ergSets P ↔ IsErgodic P E := by
  classical simp [ergSets]

theorem mem_recSet {i : S} : i ∈ recSet P ↔ ∃ E, IsErgodic P E ∧ i ∈ E := by
  simp [recSet, mem_ergSets]

theorem recSet_closed (hP : P ∈ rowStochastic ℝ S) : IsClosedSet P (recSet P) :=
  isClosedSet_of hP fun i hi j hj => by
    obtain ⟨E, hE, hiE⟩ := mem_recSet.1 hi
    exact mem_recSet.2 ⟨E, hE, hE.2.1.mem_of_pow_pos hP hiE 1 (by rwa [pow_one])⟩

theorem ergSets_pairwiseDisjoint (hP : P ∈ rowStochastic ℝ S) :
    (ergSets P : Set (Finset S)).PairwiseDisjoint id := by
  intro E hE E' hE' hne
  refine disjoint_left.2 fun i hi hi' => hne ?_
  exact ((mem_ergSets.1 hE).eq_consSet hP hi).trans ((mem_ergSets.1 hE').eq_consSet hP hi').symm

/-- The probability `Πⁿ(i, E)` of being in `E` after `n` steps. -/
def mass (P : Matrix S S ℝ) (n : ℕ) (i : S) (E : Finset S) : ℝ := ∑ k ∈ E, (P ^ n) i k

theorem mass_nonneg (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i : S) (E : Finset S) :
    0 ≤ mass P n i E :=
  sum_nonneg fun k _ => pow_nonneg' hP n i k

theorem mass_le_one (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i : S) (E : Finset S) :
    mass P n i E ≤ 1 := by
  rw [← pow_row_sum hP n i, mass]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ E) fun k _ _ => pow_nonneg' hP n i k

theorem mass_add_compl (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i : S) (E : Finset S) :
    mass P n i E + mass P n i Eᶜ = 1 := by
  rw [mass, mass, sum_add_sum_compl, pow_row_sum hP]

/-- `Πⁿ⁺ᵐ(i, A) = Σₗ Πⁿ(i, l) Πᵐ(l, A)`. -/
theorem mass_add (n m : ℕ) (i : S) (A : Finset S) :
    mass P (n + m) i A = ∑ l, (P ^ n) i l * mass P m l A := by
  simp only [mass, pow_add, mul_apply]
  rw [sum_comm]
  exact sum_congr rfl fun l _ => by rw [mul_sum]

/-- From a closed set, the mass outside it stays zero. -/
theorem mass_compl_eq_zero (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsClosedSet P E)
    {l : S} (hl : l ∈ E) (m : ℕ) : mass P m l Eᶜ = 0 :=
  sum_eq_zero fun k hk => le_antisymm (not_lt.1 fun hp => mem_compl.1 hk
    (hE.mem_of_pow_pos hP hl m hp)) (pow_nonneg' hP m l k)

/-- The mass in a closed set is nondecreasing in time. -/
theorem mass_mono (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsClosedSet P E) (i : S) :
    Monotone fun n => mass P n i E := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [mass_add]
  calc mass P n i E = ∑ l ∈ E, (P ^ n) i l * mass P 1 l E := by
        refine sum_congr rfl fun l hl => ?_
        have h0 := mass_compl_eq_zero hP hE hl 1
        have h1 := mass_add_compl hP 1 l E
        rw [show mass P 1 l E = 1 by linarith, mul_one]
    _ ≤ ∑ l, (P ^ n) i l * mass P 1 l E :=
        sum_le_sum_of_subset_of_nonneg (subset_univ E) fun l _ _ =>
          mul_nonneg (pow_nonneg' hP n i l) (mass_nonneg hP 1 l E)

/-- Every state reaches the recurrent states with positive probability. -/
theorem exists_mass_recSet_pos (hP : P ∈ rowStochastic ℝ S) (i : S) :
    ∃ n, 0 < mass P n i (recSet P) := by
  obtain ⟨E, hE, k, hk, n, -, hn⟩ := exists_ergodic_reach hP i
  refine ⟨n, lt_of_lt_of_le hn ?_⟩
  exact single_le_sum (f := fun k => (P ^ n) i k) (fun k _ => pow_nonneg' hP n i k)
    (mem_recSet.2 ⟨E, hE, hk⟩)

/-- The probability of still being transient after `n` steps tends to zero. -/
theorem tendsto_tail [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (i : S) :
    Tendsto (fun n => mass P n i (recSet P)ᶜ) atTop (𝓝 0) := by
  set G := recSet P
  have hG := recSet_closed (P := P) hP
  choose nn hnn using exists_mass_recSet_pos hP
  set n₀ := univ.sup nn + 1
  have hmono : ∀ l, mass P (nn l) l G ≤ mass P n₀ l G := fun l =>
    mass_mono hP hG l ((le_sup (f := nn) (mem_univ l)).trans (Nat.le_succ _))
  obtain ⟨l₀, -, hl₀⟩ := exists_min_image univ (fun l => mass P n₀ l G) univ_nonempty
  set δ := mass P n₀ l₀ G
  have hδ : 0 < δ := lt_of_lt_of_le (hnn l₀) (hmono l₀)
  have hδ1 : δ ≤ 1 := mass_le_one hP n₀ l₀ G
  -- one block of `n₀` steps multiplies the transient mass by at most `1 − δ`
  have hstep : ∀ m l, mass P (m * n₀ + n₀) l Gᶜ ≤ (1 - δ) * mass P (m * n₀) l Gᶜ := by
    intro m l
    rw [mass_add, mass, mul_sum]
    rw [← sum_add_sum_compl G]
    have h1 : ∑ k ∈ G, (P ^ (m * n₀)) l k * mass P n₀ k Gᶜ = 0 :=
      sum_eq_zero fun k hk => by rw [mass_compl_eq_zero hP hG hk, mul_zero]
    rw [h1, zero_add]
    refine sum_le_sum fun k _ => ?_
    have h2 := mass_add_compl hP n₀ k G
    have h3 := hl₀ k (mem_univ k)
    have h4 := pow_nonneg' hP (m * n₀) l k
    nlinarith
  have hgeo : ∀ m l, mass P (m * n₀) l Gᶜ ≤ (1 - δ) ^ m := by
    intro m
    induction m with
    | zero => intro l; simpa using mass_le_one hP 0 l Gᶜ
    | succ m ih =>
      intro l
      rw [Nat.succ_mul, pow_succ]
      calc mass P (m * n₀ + n₀) l Gᶜ ≤ (1 - δ) * mass P (m * n₀) l Gᶜ := hstep m l
        _ ≤ (1 - δ) * (1 - δ) ^ m := mul_le_mul_of_nonneg_left (ih l) (by linarith)
        _ = (1 - δ) ^ m * (1 - δ) := mul_comm _ _
  have hanti : Antitone fun n => mass P n i Gᶜ := fun a b hab => by
    have := mass_mono hP hG i hab
    have h1 := mass_add_compl hP a i G
    have h2 := mass_add_compl hP b i G
    dsimp only; linarith
  have hn₀ : 0 < n₀ := Nat.succ_pos _
  refine squeeze_zero (fun n => mass_nonneg hP n i Gᶜ) (fun n => ?_)
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - δ) (by linarith) (by linarith)).comp
      (Nat.tendsto_div_const_atTop hn₀.ne'))
  dsimp only [Function.comp_apply]
  exact (hanti (Nat.div_mul_le_self n n₀)).trans (hgeo (n / n₀) i)

theorem cesaro_apply (n : ℕ) (i j : S) :
    cesaro P n i j = (n : ℝ)⁻¹ * ∑ k ∈ range n, (P ^ k) i j := by
  simp [cesaro, Matrix.smul_apply, Matrix.sum_apply]

/-- If `Πᵏᵢⱼ → a` then `Qᵢⱼ = a`. -/
theorem Q_apply_of_tendsto {Q : Matrix S S ℝ} (hQ : Tendsto (cesaro P) atTop (𝓝 Q)) {i j : S}
    {a : ℝ} (h : Tendsto (fun k => (P ^ k) i j) atTop (𝓝 a)) : Q i j = a := by
  have h1 := tendsto_matrix_iff.1 hQ i j
  simp_rw [cesaro_apply] at h1
  exact tendsto_nhds_unique h1 h.cesaro

theorem not_mem_recSet_iff [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {j : S} :
    j ∉ recSet P ↔ IsTransient P j := by
  rw [(theorem_11_1a hP).2.2.2.2 j, mem_recSet]
  simp only [not_exists, not_and]

/-- **Exercise 11.1.** The limit `Q` of the averages has the block form of p. 330: the columns
for transient states vanish; the rows for an ergodic set `E` vanish outside `E` and are all
equal; and with the absorption probabilities `w_E(i) = lim Πⁿ(i, E)`, which sum to one over the
ergodic sets, `Qᵢⱼ = Σ_E w_E(i) q_E(j)`, where `q_E = Q_{σ(E)}` is the common row on `E`. -/
theorem ex_11_1 [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {Q : Matrix S S ℝ}
    (hQ : Tendsto (cesaro P) atTop (𝓝 Q)) :
    (∀ i j, IsTransient P j → Q i j = 0) ∧
      (∀ E, IsErgodic P E → ∀ i ∈ E, ∀ j ∉ E, Q i j = 0) ∧
      (∀ E, IsErgodic P E → ∀ i ∈ E, ∀ i' ∈ E, Q i = Q i') ∧
      ∀ i, ∃ w : Finset S → ℝ,
        (∀ E, IsErgodic P E → Tendsto (fun n => mass P n i E) atTop (𝓝 (w E))) ∧
          ∑ E ∈ ergSets P, w E = 1 ∧
          ∀ σ : Finset S → S, (∀ E, IsErgodic P E → σ E ∈ E) →
            ∀ j, Q i j = ∑ E ∈ ergSets P, w E * Q (σ E) j := by
  obtain ⟨-, hPQ⟩ := limit_mul hP tendsto_id hQ
  have hQs : Q ∈ rowStochastic ℝ S :=
    isClosed_rowStochastic.mem_of_tendsto hQ
      (eventually_atTop.2 ⟨1, fun n hn => cesaro_mem hP hn⟩)
  -- rows within an ergodic set
  have hrows : ∀ E, IsErgodic P E → ∀ i ∈ E, ∀ i' ∈ E, Q i = Q i' := by
    intro E hE i hi i' hi'
    funext c
    exact harmonic_const hP hE.2.1 (fun k _ => column_harmonic hPQ c k)
      (fun k hk _ => mem_consSet.1 (hE.eq_consSet hP hk ▸ hi')) i hi
  refine ⟨fun i j hj => ?_, fun E hE i hi j hj => ?_, hrows, fun i => ?_⟩
  · -- transient columns
    apply Q_apply_of_tendsto hQ
    have hj' := (not_mem_recSet_iff hP).2 hj
    refine squeeze_zero (fun k => pow_nonneg' hP k i j) (fun k => ?_) (tendsto_tail hP i)
    exact single_le_sum (f := fun l => (P ^ k) i l) (fun l _ => pow_nonneg' hP k i l)
      (mem_compl.2 hj')
  · -- rows of an ergodic set vanish outside it
    apply Q_apply_of_tendsto hQ
    refine tendsto_const_nhds.congr fun k => ?_
    exact (le_antisymm (not_lt.1 fun hp => hj (hE.2.1.mem_of_pow_pos hP hi k hp))
      (pow_nonneg' hP k i j)).symm
  · -- absorption probabilities
    have hconv : ∀ E, IsErgodic P E →
        Tendsto (fun n => mass P n i E) atTop (𝓝 (⨆ n, mass P n i E)) := fun E hE =>
      tendsto_atTop_ciSup (mass_mono hP hE.2.1 i) ⟨1, by
        rintro _ ⟨n, rfl⟩; exact mass_le_one hP n i E⟩
    set w : Finset S → ℝ := fun E => ⨆ n, mass P n i E
    have hsumE : ∀ n, ∑ E ∈ ergSets P, mass P n i E = mass P n i (recSet P) := fun n => by
      rw [recSet, mass, sum_biUnion (ergSets_pairwiseDisjoint hP)]
      rfl
    have hwlim : Tendsto (fun n => ∑ E ∈ ergSets P, mass P n i E) atTop
        (𝓝 (∑ E ∈ ergSets P, w E)) :=
      tendsto_finsetSum _ fun E hE => hconv E (mem_ergSets.1 hE)
    have hone : Tendsto (fun n => mass P n i (recSet P)) atTop (𝓝 1) := by
      have := (tendsto_tail hP i).const_sub 1
      rw [sub_zero] at this
      refine this.congr fun n => ?_
      have := mass_add_compl hP n i (recSet P)
      linarith
    simp_rw [hsumE] at hwlim
    refine ⟨w, hconv, tendsto_nhds_unique hwlim hone, fun σ hσ j => ?_⟩
    -- `Qᵢⱼ = Σₖ Πⁿᵢₖ Qₖⱼ`, split into the ergodic sets and the transient set
    have hsplit : ∀ n, Q i j = ∑ E ∈ ergSets P, mass P n i E * Q (σ E) j +
        ∑ k ∈ (recSet P)ᶜ, (P ^ n) i k * Q k j := fun n => by
      have e := congrFun (congrFun (pow_mul_eq hPQ n) i) j
      rw [mul_apply] at e
      rw [← e, ← sum_add_sum_compl (recSet P), recSet, sum_biUnion (ergSets_pairwiseDisjoint hP)]
      congr 1
      refine sum_congr rfl fun E hE => ?_
      rw [mass, sum_mul]
      refine sum_congr rfl fun k hk => ?_
      rw [hrows E (mem_ergSets.1 hE) k hk (σ E) (hσ E (mem_ergSets.1 hE))]
    have hrest : Tendsto (fun n => ∑ k ∈ (recSet P)ᶜ, (P ^ n) i k * Q k j) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (tendsto_tail hP i)
      rw [Real.norm_eq_abs, mass]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
      rw [abs_mul, abs_of_nonneg (pow_nonneg' hP n i k),
        abs_of_nonneg (nonneg_of_mem_rowStochastic hQs)]
      exact mul_le_of_le_one_right (pow_nonneg' hP n i k) (le_one_of_mem_rowStochastic hQs)
    have hlim : Tendsto (fun n => ∑ E ∈ ergSets P, mass P n i E * Q (σ E) j +
        ∑ k ∈ (recSet P)ᶜ, (P ^ n) i k * Q k j) atTop
        (𝓝 (∑ E ∈ ergSets P, w E * Q (σ E) j + 0)) :=
      (tendsto_finsetSum _ fun E hE => (hconv E (mem_ergSets.1 hE)).mul_const _).add hrest
    rw [add_zero] at hlim
    exact tendsto_nhds_unique (tendsto_const_nhds.congr hsplit) hlim

end StokeyLucasPrescott.StrongConvergence

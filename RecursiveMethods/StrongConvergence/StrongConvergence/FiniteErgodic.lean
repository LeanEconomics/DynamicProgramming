/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.FiniteAverages

/-!
# Finite Markov chains: ergodic sets and the limit `Q`

SLP §11.1, Exercise 11.1 and Theorem 11.2, pp. 329–331.

* `harmonic_const` (a maximum principle): a function `h` with `h = Πh` on a closed set `E`, in
  which some state `j` is reachable from every state, is constant on `E`. The columns of `Q`
  satisfy `h = Πh` because `Q = ΠQ`.
* `exists_ergodic_reach`: from every state some ergodic set is reached.
* **Theorem 11.2** (`theorem_11_2`): `Π` has a unique ergodic set iff some state `sⱼ` is a
  consequent of every state. Then all rows of `Q` equal `Qⱼ = p*`, the unique invariant
  distribution, and `p₀Q = p*` for every `p₀ ∈ Δ`. The book derives the second half from
  Theorem 11.1; here it comes from the maximum principle.
-/

namespace StokeyLucasPrescott.StrongConvergence

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- On a closed set, `h = Πh` gives `h = Πⁿh`. -/
theorem harmonic_pow (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsClosedSet P E)
    {h : S → ℝ} (hh : ∀ i ∈ E, h i = ∑ k, P i k * h k) :
    ∀ n, ∀ i ∈ E, h i = ∑ k, (P ^ n) i k * h k := by
  intro n
  induction n with
  | zero => intro i _; simp [one_apply]
  | succ n ih =>
    intro i hi
    have e : ∀ k, (P ^ (n + 1)) i k * h k = ∑ l, P i l * ((P ^ n) l k * h k) := fun k => by
      rw [pow_succ', mul_apply, sum_mul]
      exact sum_congr rfl fun l _ => by ring
    simp_rw [e]
    rw [sum_comm, hh i hi]
    refine sum_congr rfl fun l _ => ?_
    rw [← mul_sum]
    by_cases hl : l ∈ E
    · rw [← ih l hl]
    · rw [hE.apply_eq_zero hP hi hl, zero_mul, zero_mul]

/-- If `h = Πh` on a closed set `E`, `i ∈ E` maximizes `h` over `E`, and `π⁽ⁿ⁾ᵢⱼ > 0`, then `j`
also maximizes `h`. -/
theorem harmonic_max_spread (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsClosedSet P E)
    {h : S → ℝ} (hh : ∀ i ∈ E, h i = ∑ k, P i k * h k) {i : S} (hi : i ∈ E)
    (hmax : ∀ k ∈ E, h k ≤ h i) {n : ℕ} {j : S} (hj : 0 < (P ^ n) i j) : h j = h i := by
  have hjE : j ∈ E := hE.mem_of_pow_pos hP hi n hj
  have hsum : ∑ k, (P ^ n) i k * (h i - h k) = 0 := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, pow_row_sum hP, one_mul]
    rw [← harmonic_pow hP hE hh n i hi, sub_self]
  have hnn : ∀ k ∈ univ, 0 ≤ (P ^ n) i k * (h i - h k) := fun k _ => by
    by_cases hk : k ∈ E
    · exact mul_nonneg (pow_nonneg' hP n i k) (sub_nonneg.2 (hmax k hk))
    · have : (P ^ n) i k = 0 := le_antisymm
        (not_lt.1 fun hp => hk (hE.mem_of_pow_pos hP hi n hp)) (pow_nonneg' hP n i k)
      rw [this, zero_mul]
  have := (sum_eq_zero_iff_of_nonneg hnn).1 hsum j (mem_univ j)
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hj.ne'
  · linarith

/-- **Maximum principle.** If `h = Πh` on a closed set `E` and `j ∈ E` is a consequent of every
other state of `E`, then `h` is constant on `E`. -/
theorem harmonic_const (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsClosedSet P E)
    {h : S → ℝ} (hh : ∀ i ∈ E, h i = ∑ k, P i k * h k) {j : S}
    (hj : ∀ i ∈ E, i ≠ j → Cons P i j) : ∀ i ∈ E, h i = h j := by
  intro i₀ hi₀
  have hne : E.Nonempty := ⟨i₀, hi₀⟩
  obtain ⟨a, ha, hamax⟩ := exists_max_image E h hne
  obtain ⟨b, hb, hbmin⟩ := exists_min_image E h hne
  have hreach : ∀ i ∈ E, ∃ n, 0 < (P ^ n) i j := fun i hi => by
    by_cases hij : i = j
    · exact ⟨0, by rw [hij, pow_zero, one_apply_eq]; exact one_pos⟩
    · obtain ⟨n, -, hn⟩ := hj i hi hij; exact ⟨n, hn⟩
  obtain ⟨n, hn⟩ := hreach a ha
  obtain ⟨m, hm⟩ := hreach b hb
  have hja : h j = h a := harmonic_max_spread hP hE hh ha hamax hn
  have hneg : ∀ i ∈ E, -h i = ∑ k, P i k * -h k := fun i hi => by
    rw [hh i hi, ← sum_neg_distrib]
    simp
  have hjb : -h j = -h b := harmonic_max_spread hP hE hneg hb
    (fun k hk => neg_le_neg (hbmin k hk)) hm
  have h1 := hamax i₀ hi₀
  have h2 := hbmin i₀ hi₀
  linarith

/-- From every state some ergodic set is reached. -/
theorem exists_ergodic_reach (hP : P ∈ rowStochastic ℝ S) (i : S) :
    ∃ E, IsErgodic P E ∧ ∃ k ∈ E, Cons P i k := by
  obtain ⟨F, hF, hFe⟩ := exists_ergodic_subset (consSet_nonempty hP i) (consSet_closed hP i)
  obtain ⟨k, hk⟩ := hFe.1
  exact ⟨F, hFe, k, hk, mem_consSet.1 (hF hk)⟩

omit [DecidableEq S] in
/-- The columns of a matrix `B` with `ΠB = B` satisfy `h = Πh`. -/
theorem column_harmonic {B : Matrix S S ℝ} (hB : P * B = B) (c : S) :
    ∀ i, B i c = ∑ k, P i k * B k c := fun i => by
  conv_lhs => rw [← hB]
  rfl

/-- **Theorem 11.2.** `Π` has a unique ergodic set iff some state `sⱼ` is a consequent of every
state. In that case every row of `Q` is `Qⱼ`, the unique invariant distribution `p*`, and
`p₀Q = p*` for every `p₀ ∈ Δ`. -/
theorem theorem_11_2 [Nonempty S] (hP : P ∈ rowStochastic ℝ S) :
    ((∃! E, IsErgodic P E) ↔ ∃ j, ∀ i, Cons P i j) ∧
      ∀ {Q : Matrix S S ℝ}, Tendsto (cesaro P) atTop (𝓝 Q) → ∀ j, (∀ i, Cons P i j) →
        (∀ i, Q i = Q j) ∧ (∀ r, IsInvariantDist P r ↔ r = Q j) ∧
          ∀ p₀ ∈ simplex S, p₀ ᵥ* Q = Q j := by
  obtain ⟨⟨E₀, hE₀⟩, -, -, -, -⟩ := theorem_11_1a hP
  refine ⟨⟨fun ⟨E, hE, huniq⟩ => ?_, fun ⟨j, hj⟩ => ?_⟩, fun {Q} hQ j hj => ?_⟩
  · obtain ⟨j, hjE⟩ := hE.1
    refine ⟨j, fun i => ?_⟩
    obtain ⟨F, hF, k, hkF, hik⟩ := exists_ergodic_reach hP i
    have hFE := huniq F hF
    subst hFE
    exact hik.trans hP (mem_consSet.1 (hF.eq_consSet hP hkF ▸ hjE))
  · have hall : ∀ E, IsErgodic P E → E = consSet P j := fun E hE => by
      obtain ⟨i, hi⟩ := hE.1
      have hjE : j ∈ E := hE.eq_consSet hP hi ▸ mem_consSet.2 (hj i)
      exact hE.eq_consSet hP hjE
    exact ⟨E₀, hE₀, fun E hE => (hall E hE).trans (hall E₀ hE₀).symm⟩
  · obtain ⟨-, hPQ⟩ := limit_mul hP tendsto_id hQ
    have hrows : ∀ i, Q i = Q j := fun i => funext fun c =>
      harmonic_const hP (isClosedSet_univ hP) (fun i _ => column_harmonic hPQ c i)
        (fun i _ _ => hj i) i (mem_univ i)
    have hrQ : ∀ r : S → ℝ, r ∈ simplex S → r ᵥ* Q = Q j := fun r hr => by
      funext c
      simp only [vecMul, dotProduct]
      simp_rw [hrows]
      rw [← sum_mul, hr.2, one_mul]
    have hc := (theorem_11_1c hP hQ)
    refine ⟨hrows, fun r => ⟨fun hr => ?_, fun hr => ?_⟩, hrQ⟩
    · rw [← hc.2.2 r hr, hrQ r hr.1]
    · rw [hr]; exact hc.1 j

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.FiniteBlockForm
import StrongConvergence.NumericalSemigroup

/-!
# Finite Markov chains: convergence of `p₀Πⁿ`

SLP §11.1, Lemma 11.3 and Theorem 11.4, pp. 331–333. With `‖x‖_Δ = Σⱼ |xⱼ|` (`l1`), let
`εⱼ = minᵢ πᵢⱼ` and `ε = Σⱼ εⱼ` (`epsSum`).

* **Lemma 11.3** (`lemma_11_3`): `‖pΠ − qΠ‖_Δ ≤ (1 − ε)‖p − q‖_Δ` whenever `Σ p = Σ q`; in
  particular `p ↦ pΠ` is a contraction of modulus `1 − ε` on `Δ`.
* **Theorem 11.4** (`theorem_11_4`). The book states: `S` has a unique ergodic set with no
  cyclically moving subsets iff `ε⁽ᴺ⁾ > 0` for some `N ≥ 1`; then `p₀Πⁿ → p*` geometrically,
  uniformly in `p₀`. The book never defines cyclically moving subsets, and its proof of the
  converse assumes convergence rather than the stated hypothesis. Here `HasCyclicSubsets`
  defines them (a split of an ergodic set into `d ≥ 2` nonempty sets visited in turn, as in
  Example 3), and three conditions are proved equivalent:
  1. `ε⁽ᴺ⁾ > 0` for some `N ≥ 1`;
  2. there is a unique ergodic set, and it has no cyclically moving subsets;
  3. `p₀Πⁿ` converges, to the same limit for every `p₀ ∈ Δ`.

  Under them the invariant distribution `p*` is unique and
  `‖p₀Πⁿ − p*‖_Δ ≤ 2(1 − ε⁽ᴺ⁾)^⌊n/N⌋` (`theorem_11_4_rate`). That (2) implies (1) uses
  aperiodicity: the return times of a state of the ergodic set have greatest common divisor
  `d`. If `d ≥ 2`, the residues mod `d` of the times at which states are reached split the set
  into cyclically moving subsets. If `d = 1`, the return times include all large integers
  (`eventually_mem_of_add_closed`).
-/

namespace StokeyLucasPrescott.StrongConvergence

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- The norm `‖x‖_Δ = Σⱼ |xⱼ|`. -/
def l1 (x : S → ℝ) : ℝ := ∑ j, |x j|

/-- `εⱼ = minᵢ πᵢⱼ`. -/
noncomputable def epsMin [Nonempty S] (P : Matrix S S ℝ) (j : S) : ℝ :=
  univ.inf' univ_nonempty fun i => P i j

/-- `ε = Σⱼ minᵢ πᵢⱼ`. -/
noncomputable def epsSum [Nonempty S] (P : Matrix S S ℝ) : ℝ := ∑ j, epsMin P j

omit [DecidableEq S] in
theorem epsMin_le [Nonempty S] (i j : S) : epsMin P j ≤ P i j :=
  inf'_le _ (mem_univ i)

theorem epsSum_nonneg [Nonempty S] (hP : P ∈ rowStochastic ℝ S) : 0 ≤ epsSum P :=
  sum_nonneg fun _ _ => (le_inf'_iff _ _).2 fun _ _ => nonneg_of_mem_rowStochastic hP

theorem epsSum_le_one [Nonempty S] (hP : P ∈ rowStochastic ℝ S) : epsSum P ≤ 1 := by
  obtain ⟨i⟩ := ‹Nonempty S›
  rw [← sum_row_of_mem_rowStochastic hP i]
  exact sum_le_sum fun j _ => epsMin_le i j

/-- **Lemma 11.3.** If `Σ p = Σ q`, then `‖pΠ − qΠ‖_Δ ≤ (1 − ε)‖p − q‖_Δ`. -/
theorem lemma_11_3 [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {p q : S → ℝ}
    (hpq : ∑ i, p i = ∑ i, q i) : l1 (p ᵥ* P - q ᵥ* P) ≤ (1 - epsSum P) * l1 (p - q) := by
  set d := p - q
  have hd : ∑ i, d i = 0 := by simp [d, sum_sub_distrib, hpq]
  have hcol : ∀ j, (p ᵥ* P - q ᵥ* P) j = ∑ i, d i * (P i j - epsMin P j) := fun j => by
    have e1 : ∑ i, d i * (P i j - epsMin P j) = ∑ i, d i * P i j - (∑ i, d i) * epsMin P j := by
      rw [sum_mul, ← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring
    rw [e1, hd, zero_mul, sub_zero]
    simp only [Pi.sub_apply, vecMul, dotProduct, d, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  calc l1 (p ᵥ* P - q ᵥ* P) = ∑ j, |∑ i, d i * (P i j - epsMin P j)| := by
        simp only [l1, hcol]
    _ ≤ ∑ j, ∑ i, |d i| * (P i j - epsMin P j) := sum_le_sum fun j _ =>
        (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ => by
          rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (epsMin_le i j))]))
    _ = ∑ i, |d i| * (1 - epsSum P) := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [← mul_sum, sum_sub_distrib, sum_row_of_mem_rowStochastic hP]
        rfl
    _ = (1 - epsSum P) * l1 (p - q) := by rw [l1, ← sum_mul, mul_comm]

omit [DecidableEq S] in
theorem l1_sub_le_two {p q : S → ℝ} (hp : p ∈ simplex S) (hq : q ∈ simplex S) :
    l1 (p - q) ≤ 2 := by
  calc l1 (p - q) ≤ ∑ j, (p j + q j) := sum_le_sum fun j _ => by
        rw [Pi.sub_apply, abs_le]; constructor <;> linarith [hp.1 j, hq.1 j]
    _ = 2 := by rw [sum_add_distrib, hp.2, hq.2]; norm_num

/-- Iterating Lemma 11.3. -/
theorem l1_pow_le [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {p q : S → ℝ} (hp : p ∈ simplex S)
    (hq : q ∈ simplex S) (k : ℕ) :
    l1 (p ᵥ* P ^ k - q ᵥ* P ^ k) ≤ (1 - epsSum P) ^ k * l1 (p - q) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpk := simplex_vecMul (pow_mem_rowStochastic hP k) hp
    have hqk := simplex_vecMul (pow_mem_rowStochastic hP k) hq
    rw [pow_succ, ← vecMul_vecMul, ← vecMul_vecMul, pow_succ, mul_comm _ (1 - epsSum P),
      mul_assoc]
    exact (lemma_11_3 hP (hpk.2.trans hqk.2.symm)).trans
      (mul_le_mul_of_nonneg_left ih (sub_nonneg.2 (epsSum_le_one hP)))

omit [DecidableEq S] in
theorem isClosed_simplex : IsClosed (simplex S) := by
  have : simplex S = (⋂ i, {p : S → ℝ | 0 ≤ p i}) ∩ {p | ∑ i, p i = 1} := by
    ext p; simp [simplex]
  rw [this]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

omit [DecidableEq S] in
theorem abs_le_l1 (x : S → ℝ) (j : S) : |x j| ≤ l1 x :=
  single_le_sum (f := fun j => |x j|) (fun _ _ => abs_nonneg _) (mem_univ j)

omit [DecidableEq S] in
theorem eq_of_l1_le {x y : S → ℝ} (h : l1 (x - y) ≤ 0) : x = y := by
  funext j
  have := (abs_le_l1 (x - y) j).trans h
  rw [Pi.sub_apply] at this
  linarith [abs_nonneg (x j - y j), abs_sub_lt_iff.1 (lt_of_le_of_lt this zero_lt_one),
    abs_nonpos_iff.1 this]

/-- Positive transitions from `i` into `A` exhaust row `i` when `A` captures all of them. -/
theorem sum_eq_one_of_pos_mem (hP : P ∈ rowStochastic ℝ S) {i : S} {A : Finset S}
    (h : ∀ l, 0 < P i l → l ∈ A) : ∑ l ∈ A, P i l = 1 := by
  have hsum := sum_row_of_mem_rowStochastic hP i
  rw [← sum_add_sum_compl A] at hsum
  have h0 : ∑ k ∈ Aᶜ, P i k = 0 := sum_eq_zero fun k hk =>
    le_antisymm (not_lt.1 fun hp => mem_compl.1 hk (h k hp)) (nonneg_of_mem_rowStochastic hP)
  linarith

theorem apply_eq_zero_of_sum_eq_one (hP : P ∈ rowStochastic ℝ S) {i l : S} {A : Finset S}
    (h : ∑ k ∈ A, P i k = 1) (hl : l ∉ A) : P i l = 0 := by
  have hsum := sum_row_of_mem_rowStochastic hP i
  rw [← sum_add_sum_compl A, h] at hsum
  have h0 : ∑ k ∈ Aᶜ, P i k = 0 := by linarith
  exact (sum_eq_zero_iff_of_nonneg fun k _ => nonneg_of_mem_rowStochastic hP).1 h0 l
    (mem_compl.2 hl)

/-- An ergodic set `E` has **cyclically moving subsets** (p. 323) if it splits into `d ≥ 2`
nonempty disjoint sets `C₀, …, C_{d−1}` (indexed periodically, `C_{k+d} = C_k`) such that from
`C_k` the chain moves to `C_{k+1}` with probability one. -/
def HasCyclicSubsets (P : Matrix S S ℝ) (E : Finset S) : Prop :=
  ∃ d, 2 ≤ d ∧ ∃ C : ℕ → Finset S, (∀ k, C (k + d) = C k) ∧ (∀ k, (C k).Nonempty) ∧
    (∀ k k', k < d → k' < d → k ≠ k' → Disjoint (C k) (C k')) ∧ (∀ k, C k ⊆ E) ∧
    (∀ i ∈ E, ∃ k, i ∈ C k) ∧ ∀ k, ∀ i ∈ C k, ∑ l ∈ C (k + 1), P i l = 1

omit [Fintype S] [DecidableEq S] in
theorem periodic_mod {d : ℕ} {C : ℕ → Finset S} (hC : ∀ k, C (k + d) = C k) (k : ℕ) :
    C k = C (k % d) := by
  conv_lhs => rw [← Nat.mod_add_div k d]
  induction k / d with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, ← add_assoc, hC, ih]

/-- Along cyclically moving subsets, `n` steps from `C_k` land in `C_{k+n}`. -/
theorem cyclic_pow (hP : P ∈ rowStochastic ℝ S) {C : ℕ → Finset S}
    (hstep : ∀ k, ∀ i ∈ C k, ∑ l ∈ C (k + 1), P i l = 1) :
    ∀ n k, ∀ i ∈ C k, ∀ l, 0 < (P ^ n) i l → l ∈ C (k + n) := by
  intro n
  induction n with
  | zero =>
    intro k i hi l hl
    rw [pow_zero, one_apply] at hl
    split_ifs at hl with h
    · exact h ▸ hi
    · exact absurd hl (lt_irrefl 0)
  | succ n ih =>
    intro k i hi l hl
    rw [pow_succ, mul_apply] at hl
    obtain ⟨m, hm⟩ := exists_pos_of_sum_pos hl
    have hm1 : 0 < (P ^ n) i m := lt_of_le_of_ne (pow_nonneg' hP n i m) fun h => by
      rw [← h, zero_mul] at hm; exact lt_irrefl 0 hm
    have hm2 : 0 < P m l := lt_of_le_of_ne (nonneg_of_mem_rowStochastic hP) fun h => by
      rw [← h, mul_zero] at hm; exact lt_irrefl 0 hm
    have hmC := ih k i hi m hm1
    by_contra hlC
    rw [← add_assoc] at hlC
    exact (apply_eq_zero_of_sum_eq_one hP (hstep _ m hmC) hlC ▸ hm2).false

/-- If `ε⁽ᴺ⁾ > 0`, some column of `Πᴺ` is positive. -/
theorem exists_pos_column [Nonempty S] {N : ℕ} (h : 0 < epsSum (P ^ N)) :
    ∃ j, ∀ i, 0 < (P ^ N) i j := by
  obtain ⟨j, hj⟩ := exists_pos_of_sum_pos h
  exact ⟨j, fun i => lt_of_lt_of_le hj (epsMin_le i j)⟩

/-- A positive column of `Πᴺ` gives `ε⁽ᴺ⁾ > 0`. -/
theorem epsSum_pos_of_column [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {N : ℕ} {j : S}
    (h : ∀ i, 0 < (P ^ N) i j) : 0 < epsSum (P ^ N) := by
  have hj : 0 < epsMin (P ^ N) j := (lt_inf'_iff _).2 fun i _ => h i
  have hnn : ∀ k ∈ univ, 0 ≤ epsMin (P ^ N) k := fun k _ =>
    (le_inf'_iff _ _).2 fun i _ => pow_nonneg' hP N i k
  exact lt_of_lt_of_le hj (single_le_sum hnn (mem_univ j))

/-- **Theorem 11.4** (the rate). If `ε⁽ᴺ⁾ > 0`, there is a unique invariant distribution `p*`
and `‖p₀Πⁿ − p*‖_Δ ≤ 2(1 − ε⁽ᴺ⁾)^⌊n/N⌋` for every `p₀ ∈ Δ`. -/
theorem theorem_11_4_rate [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {N : ℕ} (hN : 1 ≤ N)
    (hε : 0 < epsSum (P ^ N)) :
    ∃ p, IsInvariantDist P p ∧ (∀ r, IsInvariantDist P r → r = p) ∧
      ∀ p₀ ∈ simplex S, ∀ n, l1 (p₀ ᵥ* P ^ n - p) ≤ 2 * (1 - epsSum (P ^ N)) ^ (n / N) := by
  obtain ⟨Q, -, hQ, -⟩ := theorem_11_1b hP
  obtain ⟨i₀⟩ := ‹Nonempty S›
  set p := Q i₀
  have hp : IsInvariantDist P p := (theorem_11_1c hP hQ).1 i₀
  have hPN := pow_mem_rowStochastic hP N
  have hfix : ∀ {r}, IsInvariantDist P r → ∀ m, r ᵥ* P ^ m = r := fun {r} hr m => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← vecMul_vecMul, ih, hr.2]
  have hrate : ∀ p₀ ∈ simplex S, ∀ n,
      l1 (p₀ ᵥ* P ^ n - p) ≤ 2 * (1 - epsSum (P ^ N)) ^ (n / N) := by
    intro p₀ hp₀ n
    have hsplit : P ^ n = P ^ (n % N) * (P ^ N) ^ (n / N) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    have hq := simplex_vecMul (pow_mem_rowStochastic hP (n % N)) hp₀
    have hpk : p = p ᵥ* (P ^ N) ^ (n / N) := by rw [← pow_mul, hfix hp]
    rw [hsplit, ← vecMul_vecMul]
    conv_lhs => rw [hpk]
    calc _ ≤ (1 - epsSum (P ^ N)) ^ (n / N) * l1 (p₀ ᵥ* P ^ (n % N) - p) :=
          l1_pow_le hPN hq hp.1 _
      _ ≤ (1 - epsSum (P ^ N)) ^ (n / N) * 2 :=
          mul_le_mul_of_nonneg_left (l1_sub_le_two hq hp.1)
            (pow_nonneg (sub_nonneg.2 (epsSum_le_one hPN)) _)
      _ = _ := mul_comm _ _
  refine ⟨p, hp, fun r hr => eq_of_l1_le ?_, hrate⟩
  have hlim : Tendsto (fun n => 2 * (1 - epsSum (P ^ N)) ^ (n / N)) atTop (𝓝 (2 * 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.2 (epsSum_le_one hPN))
      (by linarith)).comp (Nat.tendsto_div_const_atTop (by omega))).const_mul 2
  rw [mul_zero] at hlim
  refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  have := hrate r hr.1 n
  rwa [hfix hr] at this

omit [DecidableEq S] in
theorem tendsto_of_l1 {u : ℕ → S → ℝ} {p : S → ℝ}
    (h : Tendsto (fun n => l1 (u n - p)) atTop (𝓝 0)) : Tendsto u atTop (𝓝 p) := by
  refine tendsto_pi_nhds.2 fun j => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun n => ?_) h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  exact abs_le_l1 (u n - p) j

/-- (1) ⇒ (3): `ε⁽ᴺ⁾ > 0` gives convergence of `p₀Πⁿ` to the same limit for all `p₀ ∈ Δ`. -/
theorem conv_of_eps [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {N : ℕ} (hN : 1 ≤ N)
    (hε : 0 < epsSum (P ^ N)) :
    ∃ p, ∀ p₀ ∈ simplex S, Tendsto (fun n => p₀ ᵥ* P ^ n) atTop (𝓝 p) := by
  obtain ⟨p, -, -, hrate⟩ := theorem_11_4_rate hP hN hε
  have hPN := pow_mem_rowStochastic hP N
  refine ⟨p, fun p₀ hp₀ => tendsto_of_l1 ?_⟩
  have hlim : Tendsto (fun n => 2 * (1 - epsSum (P ^ N)) ^ (n / N)) atTop (𝓝 (2 * 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.2 (epsSum_le_one hPN))
      (by linarith)).comp (Nat.tendsto_div_const_atTop (by omega))).const_mul 2
  rw [mul_zero] at hlim
  refine squeeze_zero (fun n => sum_nonneg fun j _ => abs_nonneg _) (fun n => ?_) hlim
  exact hrate p₀ hp₀ n

/-- (3) ⇒ (1): the book's converse. -/
theorem eps_of_conv [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {p : S → ℝ}
    (h : ∀ p₀ ∈ simplex S, Tendsto (fun n => p₀ ᵥ* P ^ n) atTop (𝓝 p)) :
    ∃ N, 1 ≤ N ∧ 0 < epsSum (P ^ N) := by
  obtain ⟨i₀⟩ := ‹Nonempty S›
  have he : ∀ i, (Pi.single i 1 : S → ℝ) ∈ simplex S := fun i =>
    ⟨fun k => by by_cases h : k = i <;> simp [h], by simp⟩
  have hps : p ∈ simplex S := isClosed_simplex.mem_of_tendsto (h _ (he i₀))
    (Eventually.of_forall fun n => simplex_vecMul (pow_mem_rowStochastic hP n) (he i₀))
  obtain ⟨j, hj⟩ := exists_pos_of_sum_pos (hps.2 ▸ one_pos : 0 < ∑ i, p i)
  have hev : ∀ᶠ n in atTop, ∀ i, 0 < (P ^ n) i j := by
    rw [eventually_all]
    intro i
    have := (tendsto_pi_nhds.1 (h _ (he i))) j
    simp only [single_one_vecMul] at this
    exact this.eventually (lt_mem_nhds hj)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact ⟨N + 1, by omega, epsSum_pos_of_column hP (hN (N + 1) (by omega))⟩

/-- (1) ⇒ (2): a positive column of `Πᴺ` gives a unique ergodic set, without cyclically moving
subsets. -/
theorem uniqueErgodic_of_eps [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {N : ℕ} (hN : 1 ≤ N)
    (hε : 0 < epsSum (P ^ N)) :
    ∃ E, (IsErgodic P E ∧ ∀ E', IsErgodic P E' → E' = E) ∧ ¬ HasCyclicSubsets P E := by
  obtain ⟨j, hj⟩ := exists_pos_column hε
  have hcons : ∀ i, Cons P i j := fun i => ⟨N, hN, hj i⟩
  obtain ⟨E, hE, huniq⟩ := (theorem_11_2 hP).1.2 ⟨j, hcons⟩
  refine ⟨E, ⟨hE, huniq⟩, ?_⟩
  rintro ⟨d, hd, C, hper, hne, hdisj, -, -, hstep⟩
  obtain ⟨i₀, hi₀⟩ := hne 0
  obtain ⟨i₁, hi₁⟩ := hne 1
  have h0 : j ∈ C (0 + N) := cyclic_pow hP hstep N 0 i₀ hi₀ j (hj i₀)
  have h1 : j ∈ C (1 + N) := cyclic_pow hP hstep N 1 i₁ hi₁ j (hj i₁)
  rw [periodic_mod hper] at h0 h1
  have hne' : (0 + N) % d ≠ (1 + N) % d := by
    intro heq
    have h' : 0 + N ≡ 1 + N [MOD d] := heq
    have := Nat.ModEq.add_right_cancel' N h'
    have hd1 := (Nat.modEq_iff_dvd' (Nat.zero_le 1)).1 this
    have := Nat.le_of_dvd one_pos hd1
    omega
  exact disjoint_left.1 (hdisj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hne') h0 h1

/-- Splitting a positive `(m+n)`-step transition: some intermediate state `l` has
`π⁽ᵐ⁾ᵢₗ > 0` and `π⁽ⁿ⁾ₗₖ > 0`. -/
theorem exists_mid (hP : P ∈ rowStochastic ℝ S) {m n : ℕ} {i k : S}
    (h : 0 < (P ^ (m + n)) i k) : ∃ l, 0 < (P ^ m) i l ∧ 0 < (P ^ n) l k := by
  rw [pow_add, mul_apply] at h
  obtain ⟨l, hl⟩ := exists_pos_of_sum_pos h
  refine ⟨l, lt_of_le_of_ne (pow_nonneg' hP m i l) fun h0 => ?_,
    lt_of_le_of_ne (pow_nonneg' hP n l k) fun h0 => ?_⟩
  · rw [← h0, zero_mul] at hl; exact lt_irrefl 0 hl
  · rw [← h0, mul_zero] at hl; exact lt_irrefl 0 hl

/-- If all return times of `j` to itself are multiples of `d ≥ 2`, the ergodic set containing
`j` has cyclically moving subsets: `C_k` is the set of states reached from `j` at times
`≡ k (mod d)`. -/
theorem hasCyclicSubsets_of_period (hP : P ∈ rowStochastic ℝ S) {E : Finset S}
    (hE : IsErgodic P E) {j : S} (hj : j ∈ E) {d : ℕ} (hd : 2 ≤ d)
    (hdvd : ∀ n, 1 ≤ n → 0 < (P ^ n) j j → d ∣ n) : HasCyclicSubsets P E := by
  classical
  have hEj : E = consSet P j := hE.eq_consSet hP hj
  have hrec : ∀ i ∈ E, Cons P i j := fun i hi =>
    mem_consSet.1 (hE.eq_consSet hP hi ▸ hj)
  -- times of reaching a state are well defined mod `d`
  have hcong : ∀ i ∈ E, ∀ a b, 0 < (P ^ a) j i → 0 < (P ^ b) j i → a % d = b % d := by
    intro i hi a b ha hb
    obtain ⟨c, hc, hc'⟩ := hrec i hi
    have h1 := hdvd (a + c) (by omega) (pow_add_pos hP ha hc')
    have h2 := hdvd (b + c) (by omega) (pow_add_pos hP hb hc')
    have : a + c ≡ b + c [MOD d] :=
      ((Nat.modEq_zero_iff_dvd.2 h1).trans (Nat.modEq_zero_iff_dvd.2 h2).symm)
    exact Nat.ModEq.add_right_cancel' c this
  set C : ℕ → Finset S := fun k => E.filter fun i => ∃ n, 0 < (P ^ n) j i ∧ n % d = k % d
  have hmemC : ∀ {k i}, i ∈ C k ↔ i ∈ E ∧ ∃ n, 0 < (P ^ n) j i ∧ n % d = k % d := by
    intro k i; simp [C]
  obtain ⟨n₁, hn₁, hn₁'⟩ := hrec j hj
  have hdn₁ := hdvd n₁ hn₁ hn₁'
  have hn₁d : d ≤ n₁ := Nat.le_of_dvd (by omega) hdn₁
  refine ⟨d, hd, C, fun k => ?_, fun k => ?_, fun k k' hk hk' hne => ?_, fun k => filter_subset _ _,
    fun i hi => ?_, fun k i hi => ?_⟩
  · ext i; simp only [hmemC, Nat.add_mod_right]
  · -- a state reached at time `k % d`, on the way back to `j`
    have hlt : k % d < d := Nat.mod_lt _ (by omega)
    have hsplit : 0 < (P ^ (k % d + (n₁ - k % d))) j j := by
      rwa [Nat.add_sub_cancel' (by omega)]
    obtain ⟨l, hl, -⟩ := exists_mid hP hsplit
    exact ⟨l, hmemC.2 ⟨hE.2.1.mem_of_pow_pos hP hj _ hl, k % d, hl, Nat.mod_mod _ _⟩⟩
  · refine disjoint_left.2 fun i hi hi' => hne ?_
    obtain ⟨hiE, n, hn, hnk⟩ := hmemC.1 hi
    obtain ⟨-, n', hn', hnk'⟩ := hmemC.1 hi'
    have := hcong i hiE n n' hn hn'
    rw [hnk, hnk', Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at this
    exact this
  · obtain ⟨n, -, hn⟩ := mem_consSet.1 (hEj ▸ hi)
    exact ⟨n, hmemC.2 ⟨hi, n, hn, rfl⟩⟩
  · obtain ⟨hiE, n, hn, hnk⟩ := hmemC.1 hi
    refine sum_eq_one_of_pos_mem hP fun l hl => hmemC.2 ⟨?_, n + 1, ?_, ?_⟩
    · exact hE.2.1.mem_of_pow_pos hP hiE 1 (by rwa [pow_one])
    · exact pow_add_pos hP hn (by rwa [pow_one])
    · exact Nat.ModEq.add_right 1 hnk

/-- (2) ⇒ (1): a unique ergodic set without cyclically moving subsets gives `ε⁽ᴺ⁾ > 0`. The
return times of a state `j` of the ergodic set are closed under addition; by
`hasCyclicSubsets_of_period` they have no common divisor `d ≥ 2`, so they contain all large
integers, and `Πᴺ` has a positive `j`-th column for large `N`. -/
theorem eps_of_uniqueErgodic [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {E : Finset S}
    (hE : IsErgodic P E) (huniq : ∀ E', IsErgodic P E' → E' = E)
    (hcyc : ¬ HasCyclicSubsets P E) : ∃ N, 1 ≤ N ∧ 0 < epsSum (P ^ N) := by
  obtain ⟨j, hj⟩ := (theorem_11_2 hP).1.1 ⟨E, hE, huniq⟩
  have hjE : j ∈ E := by
    obtain ⟨i, hi⟩ := hE.1
    exact hE.eq_consSet hP hi ▸ mem_consSet.2 (hj i)
  set R : Set ℕ := {n | 1 ≤ n ∧ 0 < (P ^ n) j j}
  have hadd : ∀ a ∈ R, ∀ b ∈ R, a + b ∈ R := fun a ha b hb =>
    ⟨by have := ha.1; omega, pow_add_pos hP ha.2 hb.2⟩
  obtain ⟨n₁, hn₁, hn₁'⟩ := hj j
  have hgcd : ∀ d, (∀ n ∈ R, d ∣ n) → d = 1 := by
    intro d hd
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · rcases Nat.lt_or_ge d 1 with hd1 | hd1
      · have := hd n₁ ⟨hn₁, hn₁'⟩
        rw [show d = 0 by omega, zero_dvd_iff] at this
        omega
      · omega
    · exact absurd (hasCyclicSubsets_of_period hP hE hjE hd2 fun n hn hpos => hd n ⟨hn, hpos⟩)
        hcyc
  obtain ⟨n₀, hn₀⟩ := eventually_mem_of_add_closed hadd ⟨n₁, ⟨hn₁, hn₁'⟩, by omega⟩ hgcd
  choose m hm1 hm using hj
  set N := univ.sup m + n₀ + 1
  refine ⟨N, by omega, epsSum_pos_of_column (j := j) hP fun i => ?_⟩
  have hmi : m i ≤ univ.sup m := le_sup (f := m) (mem_univ i)
  have hrest : N - m i ∈ R := hn₀ _ (by omega)
  have := pow_add_pos hP (hm i) hrest.2
  rwa [Nat.add_sub_cancel' (by omega)] at this

/-- **Theorem 11.4.** For a finite chain the following are equivalent: (1) `ε⁽ᴺ⁾ > 0` for some
`N ≥ 1`; (2) there is a unique ergodic set and it has no cyclically moving subsets; (3) `p₀Πⁿ`
converges, to the same limit for every `p₀ ∈ Δ`. The rate of convergence is in
`theorem_11_4_rate`. -/
theorem theorem_11_4 [Nonempty S] (hP : P ∈ rowStochastic ℝ S) :
    ((∃ N, 1 ≤ N ∧ 0 < epsSum (P ^ N)) ↔
      ∃ E, (IsErgodic P E ∧ ∀ E', IsErgodic P E' → E' = E) ∧ ¬ HasCyclicSubsets P E) ∧
    ((∃ N, 1 ≤ N ∧ 0 < epsSum (P ^ N)) ↔
      ∃ p, ∀ p₀ ∈ simplex S, Tendsto (fun n => p₀ ᵥ* P ^ n) atTop (𝓝 p)) :=
  ⟨⟨fun ⟨_, hN, hε⟩ => uniqueErgodic_of_eps hP hN hε,
      fun ⟨_, ⟨hE, huniq⟩, hcyc⟩ => eps_of_uniqueErgodic hP hE huniq hcyc⟩,
    ⟨fun ⟨_, hN, hε⟩ => conv_of_eps hP hN hε, fun ⟨_, h⟩ => eps_of_conv hP h⟩⟩

end StokeyLucasPrescott.StrongConvergence

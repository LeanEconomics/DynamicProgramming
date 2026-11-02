/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.ScrambleHaar

/-!
# Gain coefficients of scrambled `(0,m,s)`-nets (Owen 1997)

For a `(0,m,s)`-net in base `b` (digit points with `D ≥ m` digits), Owen's gain coefficient of a
Haar component `ℓ ≠ 0` depends only on the number `p` of active coordinates (`ℓ_j ≠ 0`) and on the
total resolution `|κ| = Σ_j ℓ_j - p`: `Γ_ℓ = G(p, (m - |κ|)₊)` (`gainCoeff_net`), where the gain
sequence `gainSeq` is `G(0, L) = b^L`, `G(p+1, 0) = 1`,
`G(p+1, L+1) = -G(p, L+1)/(b-1) + b G(p, L)/(b-1)`.

## Main results

* Net counts: `card_agree_net` — every point of a `(0,m,s)`-net has exactly `b^{(m - |r|)₊}` net
  points in its level-`r` elementary box (`card_agree_net_eq_one`, `card_agree_net_of_le`,
  `card_agree_net_of_ge`; `exists_le_sum_eq`).
* `partialGain_empty`, `partialGain_insert`, `partialGain_eq_gainSeq`, `gainCoeff_net`: the gain
  coefficients of a scrambled `(0,m,s)`-net, by induction over the active coordinates.
* `gainSeq_eq_altSum`: the closed form `G(p, L) = (b/(b-1))^L Σ_{j < p-L} C(L-1+j, j)(-1/(b-1))^j`
  (`1 ≤ L`), hence `gainSeq_eq_zero`: `G(p, L) = 0` for `L ≥ p ≥ 1`.
* `alt_sum_mem_Icc`, `antitone_choose_div`, `gainAltSum_mem_Icc`, `gainSeq_mem_Icc`:
  `0 ≤ G(p, L) ≤ (b/(b-1))^{p-1}` for `1 ≤ p ≤ b + 1`.
* `gainCoeff_net_eq_zero` (**exactness**): `Γ_ℓ = 0` for every nonzero component with
  `Σ_j ℓ_j ≤ m`; `gainCoeff_net_mem_Icc` (**Owen's bound**): `0 ≤ Γ_ℓ ≤ (b/(b-1))^{s-1}` for
  `s ≤ b + 1`.

**Hypotheses.** `t = 0`. For `t > 0` the counts `card_agree_net` fail (boxes of volume below
`b^{t-m}` can hold up to `b^t` points) and Owen's `(t,m,s)` bounds are not formalised here; the
general variance formula of `ScrambleVariance` holds for any point set. `s ≤ b + 1` covers every
`(0,m,s)`-net with `m ≥ 2` (they exist only for `s ≤ b + 1`, Niederreiter 1992); where the
alternating terms stop decreasing (`L ≥ b`, possible only for `p ≥ b + 2`) the bound fails:
`gainSeq_two_four_two` gives `G(4, 2) = -4` in base `2`.
-/

namespace RQMCMarkov.OwenScrambling

open Finset

variable {b D : ℕ}

/-- `#{A < N q : ⌊A / q⌋ = K} = q` for `K < N`. -/
theorem card_filter_range_div {q N K : ℕ} (hq : 0 < q) (hK : K < N) :
    ((Finset.range (N * q)).filter fun A ↦ A / q = K).card = q := by
  calc ((Finset.range (N * q)).filter fun A ↦ A / q = K).card = (Finset.range q).card := by
        refine Finset.card_bij (fun A _ ↦ A - K * q) ?_ ?_ ?_
        · intro A hA
          rw [Finset.mem_filter, Finset.mem_range] at hA
          rw [Finset.mem_range]
          have h1 := Nat.div_add_mod A q
          have h2 := Nat.mod_lt A hq
          rw [hA.2] at h1
          have : q * K = K * q := mul_comm _ _
          omega
        · intro A₁ h₁ A₂ h₂ h12
          rw [Finset.mem_filter] at h₁ h₂
          have e1 := Nat.div_add_mod A₁ q
          have e2 := Nat.div_add_mod A₂ q
          rw [h₁.2] at e1
          rw [h₂.2] at e2
          have : q * K = K * q := mul_comm _ _
          omega
        · intro t ht
          rw [Finset.mem_range] at ht
          refine ⟨K * q + t, ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_range]
            constructor
            · calc K * q + t < K * q + q := by omega
                _ = (K + 1) * q := by ring
                _ ≤ N * q := Nat.mul_le_mul_right _ hK
            · rw [add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt ht, zero_add]
          · simp only [Nat.add_sub_cancel_left]
    _ = q := Finset.card_range q

/-- The box index of a digit point (remainder `0`) at levels `r ≤ D` is the vector of prefix
values. -/
theorem boxIndex_digitPoint (hb : 0 < b) {s : ℕ} {r : Fin s → ℕ} (hr : ∀ j, r j ≤ D)
    (c : Fin s → Fin D → Fin b) :
    boxIndex b r (fun j ↦ digitPoint (c j) 0) = fun j ↦ prefixVal (c j) (r j) :=
  funext fun j ↦ floor_pow_mul_digitPoint hb _ ⟨le_rfl, one_pos⟩ (hr j)

/-- Two digit points lie in the same level-`r` box iff their coordinates agree on `r_j` digits. -/
theorem boxIndex_digitPoint_eq_iff (hb : 0 < b) {s : ℕ} {r : Fin s → ℕ} (hr : ∀ j, r j ≤ D)
    (c c' : Fin s → Fin D → Fin b) :
    boxIndex b r (fun j ↦ digitPoint (c' j) 0) = (fun j ↦ prefixVal (c j) (r j)) ↔
      ∀ j, Agree (r j) (c j) (c' j) := by
  rw [boxIndex_digitPoint hb hr, funext_iff]
  refine forall_congr' fun j ↦ ?_
  rw [eq_comm, prefixVal_eq_iff_agree hb (hr j)]

/-- **Points of a `(0,m,s)`-net in a box of volume `b^{-m}`**: exactly one. -/
theorem card_agree_net_eq_one (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {r : Fin s → ℕ}
    (hr : ∑ j, r j = m) (i : Fin n) :
    (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)).card = 1 := by
  have hrD : ∀ j, r j ≤ D := fun j ↦ le_trans (le_trans
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (r j)) (Finset.mem_univ j)) hr.le) hmD
  have h := hnet.2.2.2 r (fun j ↦ prefixVal (d i j) (r j)) (by rw [hr, Nat.sub_zero])
    (fun j ↦ prefixVal_lt hb _ _)
  rw [pow_zero] at h
  rw [← h]
  congr 1
  exact Finset.filter_congr fun i' _ ↦ (boxIndex_digitPoint_eq_iff hb hrD (d i) (d i')).symm

/-- **Points of a `(0,m,s)`-net in a box of volume `b^{-|r|} ≥ b^{-m}`**: exactly
`b^{m - |r|}`. -/
theorem card_agree_net_of_le (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {r : Fin s → ℕ}
    (hr : ∑ j, r j ≤ m) (i : Fin n) :
    (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)).card =
      b ^ (m - ∑ j, r j) := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have : (Finset.univ.filter fun i' : Fin n ↦ ∀ j : Fin 0, Agree (r j) (d i j) (d i' j)) =
        Finset.univ := Finset.filter_true_of_mem fun i' _ j ↦ j.elim0
    rw [this, Finset.card_univ, Fintype.card_fin, hnet.2.1, Finset.univ_eq_empty,
      Finset.sum_empty, Nat.sub_zero]
  set j₀ : Fin s := ⟨0, hs⟩
  set e := m - ∑ j, r j with he
  set r' : Fin s → ℕ := Function.update r j₀ (r j₀ + e) with hr'
  have hsplit : ∀ g : Fin s → ℕ, ∑ j, g j = g j₀ + ∑ j ∈ Finset.univ \ {j₀}, g j := fun g ↦ by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), Finset.sdiff_singleton_eq_erase]
  have hr'sum : ∑ j, r' j = m := by
    rw [hsplit r', hr', Function.update_self]
    have : ∑ j ∈ Finset.univ \ {j₀}, Function.update r j₀ (r j₀ + e) j =
        ∑ j ∈ Finset.univ \ {j₀}, r j := Finset.sum_congr rfl fun j hj ↦
      Function.update_of_ne (Finset.notMem_singleton.1 (Finset.mem_sdiff.1 hj).2) _ _
    rw [this]
    have := hsplit r
    omega
  have hr'D : ∀ j, r' j ≤ D := fun j ↦ le_trans (le_trans
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (r' j)) (Finset.mem_univ j)) hr'sum.le) hmD
  have hrD : ∀ j, r j ≤ D := fun j ↦ by
    have h1 := hr'D j
    by_cases hj : j = j₀
    · subst hj
      rw [hr', Function.update_self] at h1
      omega
    · rw [hr', Function.update_of_ne hj] at h1
      exact h1
  have hj₀D : r j₀ + e ≤ D := by
    have := hr'D j₀
    rwa [hr', Function.update_self] at this
  set S := Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j) with hS
  set f : Fin n → ℕ := fun i' ↦ prefixVal (d i' j₀) (r j₀ + e) with hf
  set T := (Finset.range (b ^ r j₀ * b ^ e)).filter fun A ↦ A / b ^ e = prefixVal (d i j₀) (r j₀)
    with hT
  have hdiv : ∀ i' : Fin n, prefixVal (d i' j₀) (r j₀ + e) / b ^ e = prefixVal (d i' j₀) (r j₀) :=
    fun i' ↦ by
      have := prefixVal_div hb (d i' j₀) (Nat.le_add_right (r j₀) e)
      rwa [Nat.add_sub_cancel_left] at this
  have hmaps : (S : Set (Fin n)).MapsTo f T := by
    intro i' hi'
    rw [Finset.mem_coe, hS, Finset.mem_filter] at hi'
    rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_range, ← pow_add, hf]
    refine ⟨prefixVal_lt hb _ _, ?_⟩
    rw [hdiv i']
    exact ((prefixVal_eq_iff_agree hb (hrD j₀) _ _).2 (hi'.2 j₀)).symm
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ A ∈ T, (S.filter fun i' ↦ f i' = A).card = 1 := by
    intro A hA
    rw [hT, Finset.mem_filter, Finset.mem_range] at hA
    have h := hnet.2.2.2 r' (Function.update (fun j ↦ prefixVal (d i j) (r j)) j₀ A)
      (by rw [hr'sum, Nat.sub_zero]) (by
        intro j
        by_cases hj : j = j₀
        · subst hj
          rw [Function.update_self, hr', Function.update_self, pow_add]
          exact hA.1
        · rw [Function.update_of_ne hj, hr', Function.update_of_ne hj]
          exact prefixVal_lt hb _ _)
    rw [pow_zero] at h
    rw [← h, hS, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun i' _ ↦ ?_
    rw [boxIndex_digitPoint hb hr'D, funext_iff]
    constructor
    · rintro ⟨hag, hfA⟩ j
      by_cases hj : j = j₀
      · subst hj
        rw [Function.update_self, hr', Function.update_self]
        exact hfA
      · rw [Function.update_of_ne hj, hr', Function.update_of_ne hj]
        exact ((prefixVal_eq_iff_agree hb (hrD j) _ _).2 (hag j)).symm
    · intro hall
      have h0 := hall j₀
      rw [Function.update_self, hr', Function.update_self] at h0
      refine ⟨fun j ↦ ?_, h0⟩
      by_cases hj : j = j₀
      · subst hj
        rw [← prefixVal_eq_iff_agree hb (hrD _), ← hdiv i', h0, hA.2]
      · have hj' := hall j
        rw [Function.update_of_ne hj, hr', Function.update_of_ne hj] at hj'
        exact (prefixVal_eq_iff_agree hb (hrD j) _ _).1 hj'.symm
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_one, hT,
    card_filter_range_div (Nat.pow_pos hb) (prefixVal_lt hb _ _)]

/-- Below any level vector of total `≥ m` there is one of total exactly `m`. -/
theorem exists_le_sum_eq {s : ℕ} {m : ℕ} :
    ∀ (k : ℕ) (r : Fin s → ℕ), ∑ j, r j = m + k → ∃ r' : Fin s → ℕ, (∀ j, r' j ≤ r j) ∧
      ∑ j, r' j = m := by
  intro k
  induction k with
  | zero => exact fun r hr ↦ ⟨r, fun _ ↦ le_rfl, hr⟩
  | succ k ih =>
    intro r hr
    obtain ⟨j, hj⟩ : ∃ j, r j ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [Finset.sum_eq_zero fun j _ ↦ hc j] at hr
      omega
    have hsum : ∑ i, Function.update r j (r j - 1) i = m + k := by
      have h1 := Finset.add_sum_erase Finset.univ r (Finset.mem_univ j)
      have h2 := Finset.add_sum_erase Finset.univ (Function.update r j (r j - 1))
        (Finset.mem_univ j)
      have h3 : ∑ i ∈ Finset.univ.erase j, Function.update r j (r j - 1) i =
          ∑ i ∈ Finset.univ.erase j, r i := Finset.sum_congr rfl fun i hi ↦
        Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
      rw [Function.update_self, h3] at h2
      omega
    obtain ⟨r', hle, hr'⟩ := ih _ hsum
    refine ⟨r', fun i ↦ le_trans (hle i) ?_, hr'⟩
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self]
      omega
    · rw [Function.update_of_ne hi]

/-- **Points of a `(0,m,s)`-net in a box of volume `b^{-|r|} ≤ b^{-m}`**: only the point
itself. -/
theorem card_agree_net_of_ge (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {r : Fin s → ℕ}
    (hr : m ≤ ∑ j, r j) (i : Fin n) :
    (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)).card = 1 := by
  obtain ⟨r', hle, hr'⟩ := exists_le_sum_eq (m := m) (∑ j, r j - m) r (by omega)
  have hsub : (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)) ⊆
      Finset.univ.filter fun i' ↦ ∀ j, Agree (r' j) (d i j) (d i' j) := by
    intro i' hi'
    rw [Finset.mem_filter] at hi' ⊢
    exact ⟨hi'.1, fun j ↦ agree_mono (hle j) (hi'.2 j)⟩
  have h1 := Finset.card_le_card hsub
  rw [card_agree_net_eq_one hb hmD hnet hr' i] at h1
  have h2 : 0 < (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)).card :=
    Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j l _ ↦ rfl⟩⟩
  omega

/-- **Pair counts of a `(0,m,s)`-net** (`m ≤ D`, levels `r_j ≤ D`): every point has exactly
`b^{(m - |r|)₊}` net points (itself included) in its level-`r` elementary box. -/
theorem card_agree_net (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (r : Fin s → ℕ)
    (i : Fin n) :
    (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)).card =
      b ^ (m - ∑ j, r j) := by
  rcases le_total (∑ j, r j) m with h | h
  · exact card_agree_net_of_le hb hmD hnet h i
  · rw [card_agree_net_of_ge hb hmD hnet h i, Nat.sub_eq_zero_of_le h, pow_zero]

/-- **Owen's gain sequence** `G(p, L)`, the gain coefficient of a `(0,m,s)`-net for a Haar
component with `p` active coordinates and `L = (m - |κ|)₊` (`|κ|` the total resolution):
`G(0, L) = b^L`, `G(p+1, 0) = 1` and `G(p+1, L+1) = -G(p, L+1)/(b-1) + b G(p, L)/(b-1)`. -/
noncomputable def gainSeq (b : ℕ) : ℕ → ℕ → ℝ
  | 0, L => (b : ℝ) ^ L
  | _ + 1, 0 => 1
  | p + 1, L + 1 =>
      -1 / ((b : ℝ) - 1) * gainSeq b p (L + 1) + (b : ℝ) / ((b : ℝ) - 1) * gainSeq b p L

/-- `G(p, 0) = 1`. -/
theorem gainSeq_zero_right (b p : ℕ) : gainSeq b p 0 = 1 := by
  cases p with
  | zero => exact pow_zero _
  | succ p => rfl

/-- The recursion of the gain sequence, for every `L` (with `L - 1 = 0` when `L = 0`). -/
theorem gainSeq_succ (hb : 1 < b) (p L : ℕ) :
    gainSeq b (p + 1) L =
      -1 / ((b : ℝ) - 1) * gainSeq b p L + (b : ℝ) / ((b : ℝ) - 1) * gainSeq b p (L - 1) := by
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  cases L with
  | zero =>
    rw [gainSeq_zero_right, Nat.zero_sub, gainSeq_zero_right]
    field_simp
    ring
  | succ L => rfl

/-- The closed-form alternating sum `S(p, L'+1) = Σ_{j < p - L' - 1} C(L'+j, j) (-1/(b-1))^j`. -/
noncomputable def gainAltSum (b : ℕ) (p L' : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (p - (L' + 1)), ((L' + j).choose j : ℝ) * (-1 / ((b : ℝ) - 1)) ^ j

/-- Pascal recursion of the alternating sum, `S(p+1, L'+2) = S(p, L'+1) - S(p, L'+2)/(b-1)`. -/
theorem gainAltSum_succ (b p L' : ℕ) :
    gainAltSum b (p + 1) (L' + 1) =
      gainAltSum b p L' + -1 / ((b : ℝ) - 1) * gainAltSum b p (L' + 1) := by
  unfold gainAltSum
  set c : ℝ := -1 / ((b : ℝ) - 1)
  rw [show p + 1 - (L' + 1 + 1) = p - (L' + 1) by omega]
  rcases Nat.eq_zero_or_pos (p - (L' + 1)) with h | h
  · rw [h, show p - (L' + 1 + 1) = 0 by omega, Finset.sum_range_zero, Finset.sum_range_zero,
      mul_zero, add_zero]
  obtain ⟨N, hN⟩ : ∃ N, p - (L' + 1) = N + 1 := ⟨p - (L' + 1) - 1, by omega⟩
  rw [hN, show p - (L' + 1 + 1) = N by omega, Finset.sum_range_succ', Finset.sum_range_succ']
  have hpas : ∀ j, ((L' + 1 + (j + 1)).choose (j + 1) : ℝ) =
      ((L' + 1 + j).choose j : ℝ) + ((L' + (j + 1)).choose (j + 1) : ℝ) := by
    intro j
    rw [show L' + 1 + (j + 1) = (L' + 1 + j) + 1 by ring, Nat.choose_succ_succ',
      show L' + 1 + j = L' + (j + 1) by ring, Nat.cast_add]
  simp only [hpas, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, add_zero, pow_succ]
  have e : ∀ j, ((L' + 1 + j).choose j : ℝ) * (c ^ j * c) = c * (((L' + 1 + j).choose j : ℝ) *
      c ^ j) := fun j ↦ by ring
  simp only [e]
  ring

/-- **Closed form of the gain sequence**: for `p ≥ 1` and `L = L' + 1 ≥ 1`,
`G(p, L) = (b/(b-1))^L S(p, L)`. In particular `G(p, L) = 0` for `L ≥ p`. -/
theorem gainSeq_eq_altSum (hb : 1 < b) {p : ℕ} (hp : 1 ≤ p) (L' : ℕ) :
    gainSeq b p (L' + 1) = ((b : ℝ) / ((b : ℝ) - 1)) ^ (L' + 1) * gainAltSum b p L' := by
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  induction p, hp using Nat.le_induction generalizing L' with
  | base =>
    unfold gainAltSum
    rw [show 1 - (L' + 1) = 0 by omega, Finset.sum_range_zero, mul_zero]
    change -1 / ((b : ℝ) - 1) * (b : ℝ) ^ (L' + 1) + (b : ℝ) / ((b : ℝ) - 1) * (b : ℝ) ^ L' = 0
    rw [pow_succ]
    field_simp
    ring
  | succ p hp ih =>
    change -1 / ((b : ℝ) - 1) * gainSeq b p (L' + 1) + (b : ℝ) / ((b : ℝ) - 1) *
      gainSeq b p L' = _
    rw [ih L']
    cases L' with
    | zero =>
      rw [gainSeq_zero_right]
      unfold gainAltSum
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [show q + 1 - (0 + 1) = q by omega, show q + 1 + 1 - (0 + 1) = q + 1 by omega,
        Finset.sum_range_succ']
      simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul, pow_zero,
        pow_succ, Finset.mul_sum]
      have e : ∀ j, (-1 / ((b : ℝ) - 1)) ^ j * (-1 / ((b : ℝ) - 1)) =
          (-1 / ((b : ℝ) - 1)) * (-1 / ((b : ℝ) - 1)) ^ j := fun j ↦ by ring
      simp only [e, ← Finset.mul_sum]
      ring
    | succ L' =>
      rw [ih L', gainAltSum_succ]
      ring

/-- The gain sequence vanishes for `L ≥ p ≥ 1`. -/
theorem gainSeq_eq_zero (hb : 1 < b) {p L : ℕ} (hp : 1 ≤ p) (hpL : p ≤ L) : gainSeq b p L = 0 := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [gainSeq_eq_altSum hb hp, gainAltSum, show p - (L' + 1) = 0 by omega,
    Finset.sum_range_zero, mul_zero]

/-- **Alternating sums of a nonincreasing nonnegative sequence** lie between `0` and the first
term. -/
theorem alt_sum_mem_Icc : ∀ (N : ℕ) (t : ℕ → ℝ), (∀ j, 0 ≤ t j) → Antitone t →
    0 ≤ ∑ j ∈ Finset.range N, (-1) ^ j * t j ∧ ∑ j ∈ Finset.range N, (-1) ^ j * t j ≤ t 0 := by
  intro N
  induction N with
  | zero =>
    intro t ht _
    rw [Finset.sum_range_zero]
    exact ⟨le_rfl, ht 0⟩
  | succ N ih =>
    intro t ht hmono
    have hshift := ih (fun j ↦ t (j + 1)) (fun j ↦ ht (j + 1)) fun i j hij ↦ hmono (by omega)
    rw [Finset.sum_range_succ']
    have e : ∑ j ∈ Finset.range N, (-1 : ℝ) ^ (j + 1) * t (j + 1) =
        -∑ j ∈ Finset.range N, (-1) ^ j * t (j + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [pow_succ]
      ring
    rw [e, pow_zero, one_mul]
    have h01 : t 1 ≤ t 0 := hmono (Nat.zero_le 1)
    constructor <;> linarith [hshift.1, hshift.2]

/-- The terms `C(L'+j, j) (b-1)^{-j}` are nonincreasing in `j` when `L' + 1 ≤ b - 1`. -/
theorem antitone_choose_div (hb : 1 < b) {L' : ℕ} (hL : L' + 1 ≤ b - 1) :
    Antitone fun j : ℕ ↦ ((L' + j).choose j : ℝ) * (1 / ((b : ℝ) - 1)) ^ j := by
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  refine antitone_nat_of_succ_le fun j ↦ ?_
  have hc := Nat.add_one_mul_choose_eq (L' + j) j
  have hc' : ((L' + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
      ((L' + j : ℕ) + 1 : ℝ) * ((L' + j).choose j : ℝ) := by
    rw [show L' + (j + 1) = L' + j + 1 by ring]
    exact_mod_cast hc.symm
  have hbL : ((L' : ℝ) + 1) ≤ (b : ℝ) - 1 := by
    have : ((L' + 1 : ℕ) : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := Nat.cast_le.2 hL
    rw [Nat.cast_sub hb.le, Nat.cast_one] at this
    push_cast at this
    exact this
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hC : (0 : ℝ) ≤ ((L' + j).choose j : ℝ) := Nat.cast_nonneg _
  have hpow : (0 : ℝ) < (1 / ((b : ℝ) - 1)) ^ j := pow_pos (by positivity) j
  rw [pow_succ]
  have key : ((L' + (j + 1)).choose (j + 1) : ℝ) * (1 / ((b : ℝ) - 1)) ≤
      ((L' + j).choose j : ℝ) := by
    rw [mul_one_div, div_le_iff₀ hb1]
    have h2 : ((L' + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1) ≤
        ((L' + j).choose j : ℝ) * (((b : ℝ) - 1) * ((j : ℝ) + 1)) := by
      rw [hc']
      have hk : ((L' + j : ℕ) : ℝ) + 1 ≤ ((b : ℝ) - 1) * ((j : ℝ) + 1) := by
        push_cast
        nlinarith [hbL, hj]
      rw [mul_comm _ ((L' + j).choose j : ℝ)]
      exact mul_le_mul_of_nonneg_left hk hC
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    nlinarith
  calc ((L' + (j + 1)).choose (j + 1) : ℝ) * ((1 / ((b : ℝ) - 1)) ^ j * (1 / ((b : ℝ) - 1)))
      = (((L' + (j + 1)).choose (j + 1) : ℝ) * (1 / ((b : ℝ) - 1))) * (1 / ((b : ℝ) - 1)) ^ j
        := by ring
    _ ≤ ((L' + j).choose j : ℝ) * (1 / ((b : ℝ) - 1)) ^ j :=
        mul_le_mul_of_nonneg_right key hpow.le

/-- `0 ≤ S(p, L) ≤ 1` when `L ≤ b - 1`. -/
theorem gainAltSum_mem_Icc (hb : 1 < b) (p : ℕ) {L' : ℕ} (hL : L' + 1 ≤ b - 1) :
    0 ≤ gainAltSum b p L' ∧ gainAltSum b p L' ≤ 1 := by
  have h := alt_sum_mem_Icc (p - (L' + 1))
    (fun j ↦ ((L' + j).choose j : ℝ) * (1 / ((b : ℝ) - 1)) ^ j)
    (fun j ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by
      have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
      have : (0 : ℝ) < (b : ℝ) - 1 := by linarith
      positivity) j))
    (antitone_choose_div hb hL)
  have e : gainAltSum b p L' = ∑ j ∈ Finset.range (p - (L' + 1)),
      (-1) ^ j * (((L' + j).choose j : ℝ) * (1 / ((b : ℝ) - 1)) ^ j) := by
    unfold gainAltSum
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [div_eq_mul_one_div (-1 : ℝ), mul_pow]
    ring
  rw [e]
  refine ⟨h.1, ?_⟩
  have := h.2
  simp only [add_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at this
  exact this

/-- **Owen's bound on the gain sequence**: for `1 ≤ p ≤ b + 1`,
`0 ≤ G(p, L) ≤ (b/(b-1))^{p-1}` for every `L`. -/
theorem gainSeq_mem_Icc (hb : 1 < b) {p : ℕ} (hp : 1 ≤ p) (hpb : p ≤ b + 1) (L : ℕ) :
    0 ≤ gainSeq b p L ∧ gainSeq b p L ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (p - 1) := by
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have ha : (1 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := by
    rw [one_le_div hb1]
    linarith
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    rw [gainSeq_zero_right]
    exact ⟨zero_le_one, one_le_pow₀ ha⟩
  rcases le_or_gt p L with hpL | hpL
  · rw [gainSeq_eq_zero hb hp hpL]
    exact ⟨le_rfl, pow_nonneg (le_trans zero_le_one ha) _⟩
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [gainSeq_eq_altSum hb hp]
  have hS : 0 ≤ gainAltSum b p L' ∧ gainAltSum b p L' ≤ 1 := by
    by_cases hLp : L' + 2 = p
    · unfold gainAltSum
      rw [show p - (L' + 1) = 1 by omega, Finset.sum_range_one, add_zero,
        Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
      exact ⟨zero_le_one, le_rfl⟩
    · exact gainAltSum_mem_Icc hb p (L' := L') (by omega)
  have hapos : (0 : ℝ) ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (L' + 1) :=
    pow_nonneg (le_trans zero_le_one ha) _
  refine ⟨mul_nonneg hapos hS.1, ?_⟩
  calc ((b : ℝ) / ((b : ℝ) - 1)) ^ (L' + 1) * gainAltSum b p L'
      ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (L' + 1) * 1 := mul_le_mul_of_nonneg_left hS.2 hapos
    _ = ((b : ℝ) / ((b : ℝ) - 1)) ^ (L' + 1) := mul_one _
    _ ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (p - 1) := pow_le_pow_right₀ ha (by omega)

/-- **The gain bound needs `p ≤ b + 1`**: in base `2` with `p = 4` active coordinates and
`L = 2`, `G(4, 2) = -4 < 0`, outside `[0, (b/(b-1))^{p-1}]`. (No `(0,m,4)`-net in base `2` exists
for `m ≥ 2`, so this does not contradict Owen; it shows the bound is not a property of the gain
recursion alone.) -/
theorem gainSeq_two_four_two : gainSeq 2 4 2 = -4 := by
  simp only [gainSeq]
  norm_num

/-- The indicator that two strings agree on their first `r` digits. -/
noncomputable def agreeInd (r : ℕ) (x y : Fin D → Fin b) : ℝ := if Agree r x y then 1 else 0

/-- The gain factor of one active coordinate:
`(b/(b-1)) [agree on ℓ digits] - (1/(b-1)) [agree on ℓ - 1 digits]`. -/
noncomputable def gainFactor (b : ℕ) (ℓ : ℕ) (x y : Fin D → Fin b) : ℝ :=
  (b : ℝ) / ((b : ℝ) - 1) * agreeInd ℓ x y + -1 / ((b : ℝ) - 1) * agreeInd (ℓ - 1) x y

/-- The gain weight of a pair is its gain factor. -/
theorem gainWeight_commonPrefix (hb : 1 < b) {ℓ : ℕ} (hℓ : ℓ ≤ D) (x y : Fin D → Fin b) :
    gainWeight b (commonPrefix x y) ℓ = gainFactor b ℓ x y := by
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have h1 : ℓ ≤ commonPrefix x y ↔ Agree ℓ x y := (agree_iff_le_commonPrefix hℓ x y).symm
  have h2 : ℓ ≤ commonPrefix x y + 1 ↔ Agree (ℓ - 1) x y := by
    rw [agree_iff_le_commonPrefix (by omega) x y]
    omega
  unfold gainWeight gainFactor agreeInd
  by_cases a1 : Agree ℓ x y <;> by_cases a2 : Agree (ℓ - 1) x y
  · rw [ite_eq_left (h1.2 a1), ite_eq_left (h2.2 a2), ite_eq_left a1, ite_eq_left a2]
    field_simp
    ring
  · rw [ite_eq_left (h1.2 a1), ite_eq_right (fun h ↦ a2 (h2.1 h)), ite_eq_left a1,
      ite_eq_right a2]
    field_simp
    ring
  · rw [ite_eq_right (fun h ↦ a1 (h1.1 h)), ite_eq_left (h2.2 a2), ite_eq_right a1,
      ite_eq_left a2]
    field_simp
    ring
  · rw [ite_eq_right (fun h ↦ a1 (h1.1 h)), ite_eq_right (fun h ↦ a2 (h2.1 h)), ite_eq_right a1,
      ite_eq_right a2]
    ring

/-- The partial gain: coordinates in `u` carry the gain factor of level `ℓ_j`, the others the
agreement indicator of level `ℓ_j`. -/
noncomputable def partialGain (b : ℕ) {s n : ℕ} (d : Fin n → Fin s → Fin D → Fin b)
    (u : Finset (Fin s)) (ℓ : Fin s → ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ∑ i', ∏ j,
    (if j ∈ u then gainFactor b (ℓ j) (d i j) (d i' j) else agreeInd (ℓ j) (d i j) (d i' j))

/-- The gain coefficient is the partial gain with all coordinates active. -/
theorem gainCoeff_eq_partialGain (hb : 1 < b) {s n : ℕ} (d : Fin n → Fin s → Fin D → Fin b)
    (ℓ : Fin s → Fin (D + 1)) :
    gainCoeff b d ℓ = partialGain b d Finset.univ fun j ↦ (ℓ j : ℕ) := by
  unfold gainCoeff partialGain
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun i' _ ↦
    Finset.prod_congr rfl fun j _ ↦ ?_
  rw [ite_eq_left (Finset.mem_univ j)]
  exact gainWeight_commonPrefix hb (Nat.lt_succ_iff.1 (ℓ j).isLt) _ _

/-- With no active coordinate the partial gain is the normalised pair count `b^{(m - |ℓ|)₊}`
of the net. -/
theorem partialGain_empty (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (ℓ : Fin s → ℕ) :
    partialGain b d ∅ ℓ = (b : ℝ) ^ (m - ∑ j, ℓ j) := by
  unfold partialGain agreeInd
  have hn : (n : ℝ) ≠ 0 := by
    rw [hnet.2.1, Nat.cast_pow]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hb.ne')
  have h1 : ∀ i, ∑ i', ∏ j, (if j ∈ (∅ : Finset (Fin s)) then gainFactor b (ℓ j) (d i j) (d i' j)
      else if Agree (ℓ j) (d i j) (d i' j) then (1 : ℝ) else 0) = (b : ℝ) ^ (m - ∑ j, ℓ j) := by
    intro i
    simp only [Finset.notMem_empty, ↓reduceIte]
    rw [Finset.sum_congr rfl fun i' _ ↦ Fintype.prod_boole]
    have h2 : (∑ i', if ∀ j, Agree (ℓ j) (d i j) (d i' j) then (1 : ℝ) else 0) =
        (b : ℝ) ^ (m - ∑ j, ℓ j) := by
      rw [← Finset.natCast_card_filter, card_agree_net hb hmD hnet ℓ i, Nat.cast_pow]
    convert h2
  rw [Finset.sum_congr rfl fun i _ ↦ h1 i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- **Recursion of the partial gain** in one more active coordinate `j ∉ u`. -/
theorem partialGain_insert {s n : ℕ} (d : Fin n → Fin s → Fin D → Fin b) {u : Finset (Fin s)}
    {j : Fin s} (hj : j ∉ u) (ℓ : Fin s → ℕ) :
    partialGain b d (insert j u) ℓ =
      (b : ℝ) / ((b : ℝ) - 1) * partialGain b d u ℓ +
        -1 / ((b : ℝ) - 1) * partialGain b d u (Function.update ℓ j (ℓ j - 1)) := by
  unfold partialGain
  have key : ∀ i i', ∏ j', (if j' ∈ insert j u then gainFactor b (ℓ j') (d i j') (d i' j')
      else agreeInd (ℓ j') (d i j') (d i' j')) =
      (b : ℝ) / ((b : ℝ) - 1) * ∏ j', (if j' ∈ u then gainFactor b (ℓ j') (d i j') (d i' j')
        else agreeInd (ℓ j') (d i j') (d i' j')) +
      -1 / ((b : ℝ) - 1) * ∏ j', (if j' ∈ u then
        gainFactor b (Function.update ℓ j (ℓ j - 1) j') (d i j') (d i' j')
        else agreeInd (Function.update ℓ j (ℓ j - 1) j') (d i j') (d i' j')) := by
    intro i i'
    rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j,
      Fintype.prod_eq_mul_prod_compl j, ite_eq_left (Finset.mem_insert_self j u),
      ite_eq_right hj, ite_eq_right hj, Function.update_self]
    have hrest1 : ∏ j' ∈ {j}ᶜ, (if j' ∈ insert j u then gainFactor b (ℓ j') (d i j') (d i' j')
        else agreeInd (ℓ j') (d i j') (d i' j')) = ∏ j' ∈ {j}ᶜ,
          (if j' ∈ u then gainFactor b (ℓ j') (d i j') (d i' j')
          else agreeInd (ℓ j') (d i j') (d i' j')) := by
      refine Finset.prod_congr rfl fun j' hj' ↦ ?_
      have hne : j' ≠ j := by
        rw [Finset.mem_compl, Finset.mem_singleton] at hj'
        exact hj'
      simp only [Finset.mem_insert, hne, false_or]
    have hrest2 : ∏ j' ∈ {j}ᶜ, (if j' ∈ u then
        gainFactor b (Function.update ℓ j (ℓ j - 1) j') (d i j') (d i' j')
        else agreeInd (Function.update ℓ j (ℓ j - 1) j') (d i j') (d i' j')) = ∏ j' ∈ {j}ᶜ,
          (if j' ∈ u then gainFactor b (ℓ j') (d i j') (d i' j')
          else agreeInd (ℓ j') (d i j') (d i' j')) := by
      refine Finset.prod_congr rfl fun j' hj' ↦ ?_
      have hne : j' ≠ j := by
        rw [Finset.mem_compl, Finset.mem_singleton] at hj'
        exact hj'
      rw [Function.update_of_ne hne]
    rw [hrest1, hrest2]
    unfold gainFactor
    ring
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Coordinates with nonzero level contribute at least one each to the total level. -/
theorem card_filter_add_le_sum {s : ℕ} (ℓ : Fin s → ℕ) {u : Finset (Fin s)} {j : Fin s}
    (hj : j ∉ u) : (u.filter fun j' ↦ ℓ j' ≠ 0).card + ℓ j ≤ ∑ j', ℓ j' := by
  have hj' : j ∉ u.filter fun j' ↦ ℓ j' ≠ 0 := fun h ↦ hj (Finset.mem_filter.1 h).1
  calc (u.filter fun j' ↦ ℓ j' ≠ 0).card + ℓ j
      ≤ ∑ j' ∈ u.filter (fun j' ↦ ℓ j' ≠ 0), ℓ j' + ℓ j := by
        refine Nat.add_le_add_right ?_ _
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum fun j' hj'' ↦ Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 hj'').2
    _ = ∑ j' ∈ insert j (u.filter fun j' ↦ ℓ j' ≠ 0), ℓ j' := by
        rw [Finset.sum_insert hj', add_comm]
    _ ≤ ∑ j', ℓ j' := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **The partial gain of a `(0,m,s)`-net is Owen's gain sequence**: with `p` the number of active
coordinates of nonzero level, `partialGain u ℓ = G(p, (m - (|ℓ| - p))₊)`. -/
theorem partialGain_eq_gainSeq (hb : 1 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (u : Finset (Fin s)) :
    ∀ ℓ : Fin s → ℕ, partialGain b d u ℓ =
      gainSeq b (u.filter fun j ↦ ℓ j ≠ 0).card
        (m - (∑ j, ℓ j - (u.filter fun j ↦ ℓ j ≠ 0).card)) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  induction u using Finset.induction_on with
  | empty =>
    intro ℓ
    rw [partialGain_empty hb0 hmD hnet, Finset.filter_empty, Finset.card_empty, Nat.sub_zero]
    rfl
  | insert j u hj ih =>
    intro ℓ
    rw [partialGain_insert d hj ℓ, Finset.filter_insert]
    by_cases hℓ : ℓ j = 0
    · rw [ite_eq_right (not_not.2 hℓ), show ℓ j - 1 = ℓ j by omega, Function.update_eq_self, ih ℓ]
      field_simp
      ring
    · rw [ite_eq_left hℓ]
      have hj' : j ∉ u.filter fun j' ↦ ℓ j' ≠ 0 := fun h ↦ hj (Finset.mem_filter.1 h).1
      rw [Finset.card_insert_of_notMem hj']
      set ℓ' := Function.update ℓ j (ℓ j - 1) with hℓ'
      have hfil : (u.filter fun j' ↦ ℓ' j' ≠ 0) = u.filter fun j' ↦ ℓ j' ≠ 0 := by
        refine Finset.filter_congr fun j' hj'' ↦ ?_
        have hne : j' ≠ j := fun h ↦ hj (h ▸ hj'')
        rw [hℓ', Function.update_of_ne hne]
      have hsum : ∑ j', ℓ' j' + 1 = ∑ j', ℓ j' := by
        have h1 := Finset.add_sum_erase Finset.univ ℓ (Finset.mem_univ j)
        have h2 := Finset.add_sum_erase Finset.univ ℓ' (Finset.mem_univ j)
        have h3 : ∑ i ∈ Finset.univ.erase j, ℓ' i = ∑ i ∈ Finset.univ.erase j, ℓ i :=
          Finset.sum_congr rfl fun i hi ↦ Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
        rw [hℓ', Function.update_self] at h2
        rw [h3] at h2
        rw [hℓ']
        omega
      have hle := card_filter_add_le_sum ℓ hj
      rw [ih ℓ, ih ℓ', hfil, gainSeq_succ hb]
      set p := (u.filter fun j' ↦ ℓ j' ≠ 0).card
      rw [show m - (∑ j', ℓ' j' - p) = m - (∑ j', ℓ j' - (p + 1)) by omega,
        show m - (∑ j', ℓ j' - p) = m - (∑ j', ℓ j' - (p + 1)) - 1 by omega]
      ring

/-- **Gain coefficients of a scrambled `(0,m,s)`-net** (Owen 1997): for `m ≤ D` digits,
`Γ_ℓ = G(p, (m - |κ|)₊)` with `p = #{j : ℓ_j ≠ 0}` the number of active coordinates and
`|κ| = Σ_j ℓ_j - p` the total resolution of the Haar component. -/
theorem gainCoeff_net (hb : 1 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (ℓ : Fin s → Fin (D + 1)) :
    gainCoeff b d ℓ = gainSeq b (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card
      (m - (∑ j, (ℓ j : ℕ) - (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card)) := by
  rw [gainCoeff_eq_partialGain hb, partialGain_eq_gainSeq hb hmD hnet]

/-- The number of active coordinates of a nonzero component is at least `1`. -/
theorem one_le_card_active {s : ℕ} {ℓ : Fin s → Fin (D + 1)} (hℓ : ℓ ≠ 0) :
    1 ≤ (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card := by
  obtain ⟨j, hj⟩ : ∃ j, ℓ j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hℓ (funext hc)
  refine Finset.card_pos.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
  intro h
  exact hj (Fin.ext h)

/-- **Scrambled `(0,m,s)`-nets integrate low-resolution components exactly** (Owen 1997):
`Γ_ℓ = 0` for every nonzero component with `|ℓ| ≤ m`. -/
theorem gainCoeff_net_eq_zero (hb : 1 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {ℓ : Fin s → Fin (D + 1)} (hℓ : ℓ ≠ 0) (hsum : ∑ j, (ℓ j : ℕ) ≤ m) :
    gainCoeff b d ℓ = 0 := by
  rw [gainCoeff_net hb hmD hnet]
  have h1 := one_le_card_active hℓ
  have h2 : (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card ≤ ∑ j, (ℓ j : ℕ) := by
    rw [Finset.card_eq_sum_ones]
    calc ∑ j ∈ Finset.univ.filter (fun j ↦ (ℓ j : ℕ) ≠ 0), 1
        ≤ ∑ j ∈ Finset.univ.filter (fun j ↦ (ℓ j : ℕ) ≠ 0), (ℓ j : ℕ) :=
          Finset.sum_le_sum fun j hj ↦ Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 hj).2
      _ ≤ ∑ j, (ℓ j : ℕ) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  exact gainSeq_eq_zero hb h1 (by omega)

/-- **Owen's gain bound for scrambled `(0,m,s)`-nets with `s ≤ b + 1`** (Owen 1997): every
nonzero component has `0 ≤ Γ_ℓ ≤ (b/(b-1))^{s-1}`. (For `m ≥ 2`, `(0,m,s)`-nets in base `b`
exist only for `s ≤ b + 1`.) -/
theorem gainCoeff_net_mem_Icc (hb : 1 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (hsb : s ≤ b + 1)
    {ℓ : Fin s → Fin (D + 1)} (hℓ : ℓ ≠ 0) :
    0 ≤ gainCoeff b d ℓ ∧ gainCoeff b d ℓ ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) := by
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have ha : (1 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := by
    rw [one_le_div hb1]
    linarith
  rw [gainCoeff_net hb hmD hnet]
  have h1 := one_le_card_active hℓ
  have hps : (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card ≤ s := by
    calc (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card ≤ Finset.univ.card :=
          Finset.card_filter_le _ _
      _ = s := by rw [Finset.card_univ, Fintype.card_fin]
  have h := gainSeq_mem_Icc hb h1 (le_trans hps hsb)
    (m - (∑ j, (ℓ j : ℕ) - (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card))
  exact ⟨h.1, le_trans h.2 (pow_le_pow_right₀ ha (by omega))⟩

end RQMCMarkov.OwenScrambling

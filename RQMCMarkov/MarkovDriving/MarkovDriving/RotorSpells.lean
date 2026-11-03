/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.RotorRouter

/-! # Rotor walks have too-regular spells (post #3)

Post #3: "Rotors perform poorly in terms of spell lengths because their balanced ordering makes
the path too regular … Under the Markov chain spell lengths in state `i` are geometric with stay
probability `p_ii` … in the two-state chain every spell lasts exactly 8 periods, rather than
being geometric with mean 8."

**General facts.**
* `occCount_add_of_stay`: while the path stays in `i`, each period is one more departure.
* `rotorWalk_shift` (in `RotorRouter`): the rotor walk after any time is the rotor walk started
  from the current state and rotor positions, so a spell's length is a deterministic function
  of the rotor position at its start.
* `rotorWalk_not_stay`, `runLength_rotorWalk_le`: if the cycle of `i` contains an entry
  `≠ i` (e.g. `p_ii < 1` for a balanced cycle, `exists_ne_of_lt_one`), the walk never spends
  more than `L i` consecutive periods in `i`: every spell in `i` has length `≤ L i`.
* `sum_geomPMF`: under the Markov chain, the spell length is geometric,
  `P(len = k) = p^{k−1}(1 − p)` (`geomPMF`), and `P(len > L) = p^L > 0`. So the empirical
  distribution of rotor spell lengths, which puts no mass above `L i`, stays at distance
  `≥ p_ii^{L i}` from the geometric law for every `T` (`rotor_spells_not_geometric`).

**The two-state chain with `p_ii = 7/8`** (`twoStateStay78`, balanced cycle `cycle78`: seven
stays then a switch, length `8`):
* `rotorWalk78_canonical`: with zero offsets the walk is `x_t = x₀` for `⌊t/8⌋` even and the
  other state for `⌊t/8⌋` odd: every spell, including the first, lasts exactly `8` periods.
* `rotorWalk78_eventually_canonical`, `runLength_rotorWalk78`: for **any** offsets (in
  particular for the randomized rotor) there is `τ ≤ 16` after which the walk is the canonical
  one: after the first spell in each state, every spell lasts exactly `8` periods, and the spell
  starts after `τ` are exactly `τ + 8k`.
* `rotor78_spells_not_geometric`: at most `16` spells ever have a length other than `8`, while
  the geometric law gives `P(len = 8) = (7/8)^7/8 < 1/16`.

**Reading.** "Every spell lasts exactly 8 periods" is exact for the rotor started at the
beginning of both cycles, and holds after the first spell in each state for arbitrary starting
points of the cycles.
-/

namespace RQMCMarkov.MarkovDriving

open Finset

variable {S : Type*} [DecidableEq S]

/-- While the path stays in `i` during `t, …, t + m − 1`, the visit count grows by one per
period. -/
theorem occCount_add_of_stay {x : ℕ → S} {i : S} {t m : ℕ} (h : ∀ k < m, x (t + k) = i) :
    occCount x i (t + m) = occCount x i t + m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, occCount_succ, ih fun k hk => h k (by omega), h m (by omega)]
    simp only [ite_true]
    ring

/-- **No overlong stays in a rotor walk**: if the cycle of `i` has an entry `≠ i`, the walk
never spends `L i + 1` consecutive periods in `i`. -/
theorem rotorWalk_not_stay {L : S → ℕ} {c : S → ℕ → S} (θ : S → ℕ) (x₀ : S) {i : S}
    (hne : ∃ m < L i, c i m ≠ i) (t : ℕ) : ∃ m ≤ L i, rotorWalk L c θ x₀ (t + m) ≠ i := by
  by_contra hcon
  push Not at hcon
  set x := rotorWalk L c θ x₀ with hx
  set a := θ i + occCount x i t with ha
  -- every departure in the window stays in `i`
  have hstay : ∀ m < L i, c i ((a + m) % L i) = i := by
    intro m hm
    have h1 := rotorWalk_succ L c θ x₀ (t + m)
    rw [← hx, hcon m hm.le, occCount_add_of_stay fun k hk => hcon k (by omega)] at h1
    rw [ha, add_assoc, ← h1, add_assoc]
    exact hcon (m + 1) hm
  obtain ⟨m₀, hm₀, hcm₀⟩ := hne
  have hper : ∀ k, (fun m => if c i (m % L i) = i then (0 : ℤ) else 1) (k + L i) =
      (fun m => if c i (m % L i) = i then (0 : ℤ) else 1) k := fun k => by
    simp only [Nat.add_mod_right]
  have hsum := sum_range_add_periodic
    (F := fun m => if c i (m % L i) = i then (0 : ℤ) else 1) (L := L i) hper a
  have hleft : ∑ m ∈ range (L i), (fun m => if c i (m % L i) = i then (0 : ℤ) else 1) (a + m) =
      0 := sum_eq_zero fun m hm => by simp only [hstay m (mem_range.1 hm), ite_true]
  have hright : (1 : ℤ) ≤
      ∑ m ∈ range (L i), (fun m => if c i (m % L i) = i then (0 : ℤ) else 1) m := by
    refine le_trans ?_ (single_le_sum (f := fun m => if c i (m % L i) = i then (0 : ℤ) else 1)
      (fun m _ => by split_ifs <;> norm_num) (mem_range.2 hm₀))
    simp only [Nat.mod_eq_of_lt hm₀, hcm₀, ite_false, le_refl]
  beta_reduce at hsum hleft hright
  rw [hleft] at hsum
  rw [← hsum] at hright
  exact absurd hright (by norm_num)

/-- **Rotor spells are bounded**: if the cycle of `i` has an entry `≠ i`, every run of the rotor
walk in state `i` has length at most `L i` (whatever the horizon). -/
theorem runLength_rotorWalk_le {L : S → ℕ} {c : S → ℕ → S} (θ : S → ℕ) (x₀ : S) {i : S}
    (hne : ∃ m < L i, c i m ≠ i) {t : ℕ} (ht : rotorWalk L c θ x₀ t = i) (T : ℕ) :
    runLength (rotorWalk L c θ x₀) t T ≤ L i := by
  unfold runLength
  obtain ⟨m, hm, hmne⟩ := rotorWalk_not_stay θ x₀ hne t
  calc ((range (T - t)).filter fun k => ∀ m ≤ k,
        rotorWalk L c θ x₀ (t + m) = rotorWalk L c θ x₀ t).card ≤ (range (L i)).card := by
        refine card_le_card fun k hk => ?_
        rw [mem_filter] at hk
        rw [mem_range]
        by_contra hkL
        exact hmne ((hk.2 m (by omega)).trans ht)
    _ = L i := card_range _

/-- For a balanced cycle (`IsRotorCycle`) and `p_ii < 1`, the cycle of `i` has an entry `≠ i`. -/
theorem exists_ne_of_lt_one {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S}
    (hc : IsRotorCycle P L c) {i : S} (hlt : P i i < 1) : ∃ m < L i, c i m ≠ i := by
  by_contra hcon
  push Not at hcon
  have hall : (range (L i)).filter (fun m => c i m = i) = range (L i) :=
    filter_true_of_mem fun m hm => hcon m (mem_range.1 hm)
  have h := hc.card_eq i i
  rw [hall, card_range] at h
  have hL : (0 : ℝ) < L i := by exact_mod_cast hc.len_pos i
  nlinarith

/-- The **geometric law of spell lengths** under the Markov chain with stay probability `p`:
`P(len = k) = p^{k−1} (1 − p)` for `k ≥ 1`. -/
noncomputable def geomPMF (p : ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else p ^ (k - 1) * (1 - p)

/-- `P(len ≤ L) = 1 − p^L`, i.e. the geometric tail is `P(len > L) = p^L`. -/
theorem sum_geomPMF (p : ℝ) (L : ℕ) : ∑ k ∈ range (L + 1), geomPMF p k = 1 - p ^ L := by
  induction L with
  | zero => simp only [zero_add, sum_range_one, geomPMF, ite_true, pow_zero, sub_self]
  | succ L ih =>
    rw [sum_range_succ, ih]
    simp only [geomPMF, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    ring

/-- **Correction: rotor paths are not representative in spell lengths.** If `0 < p_ii` and the
cycle of `i` has an entry `≠ i`, every rotor spell in `i` has length `≤ L i`, whereas the
geometric law gives positive probability `p_ii^{L i}` to longer spells: the empirical spell
length distribution of the rotor walk never comes closer than `p_ii^{L i}` to the geometric
law. -/
theorem rotor_spells_not_geometric {L : S → ℕ} {c : S → ℕ → S} (θ : S → ℕ) (x₀ : S) {i : S}
    (hne : ∃ m < L i, c i m ≠ i) {p : ℝ} (hp : 0 < p) :
    (∀ t T, rotorWalk L c θ x₀ t = i → runLength (rotorWalk L c θ x₀) t T ≤ L i) ∧
      0 < 1 - ∑ k ∈ range (L i + 1), geomPMF p k := by
  refine ⟨fun t T ht => runLength_rotorWalk_le θ x₀ hne ht T, ?_⟩
  rw [sum_geomPMF, sub_sub_cancel]
  exact pow_pos hp _

/-! ### The two-state chain with stay probability `7/8` -/

/-- The cycle length `8` of the `7/8` chain. -/
def len78 : Fin 2 → ℕ := fun _ => 8

/-- The balanced cycle of the `7/8` chain: seven stays, then a switch. -/
def cycle78 : Fin 2 → ℕ → Fin 2 :=
  fun i m => if m % 8 = 7 then (if i = 0 then 1 else 0) else i

/-- The other state of a two-state chain. -/
def otherState (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- `cycle78` is a balanced cycle for `twoStateStay78`: `7` stays and `1` switch out of `8`. -/
theorem isRotorCycle78 : IsRotorCycle twoStateStay78 len78 cycle78 := by
  have hcard : ∀ i j : Fin 2, ((range 8).filter fun m => cycle78 i m = j).card =
      if i = j then 7 else 1 := by decide +kernel
  refine ⟨fun _ => Nat.succ_pos 7, fun i j => ?_⟩
  change (((range 8).filter fun m => cycle78 i m = j).card : ℝ) = twoStateStay78 i j * (8 : ℕ)
  rw [hcard i j]
  simp only [twoStateStay78]
  split_ifs <;> norm_num

/-- The canonical walk on its first two spells (checked by evaluation). -/
theorem rotorWalk78_lt_sixteen :
    ∀ x₀ : Fin 2, ∀ t < 16, rotorWalk len78 cycle78 (fun _ => 0) x₀ t =
      if t / 8 % 2 = 0 then x₀ else otherState x₀ := by
  decide +kernel

/-- After `16` periods the canonical walk is back at its start, with both rotors at the start of
their cycles. -/
theorem rotorWalk78_sixteen :
    ∀ x₀ : Fin 2, rotorWalk len78 cycle78 (fun _ => 0) x₀ 16 = x₀ ∧
      ∀ i : Fin 2, occCount (rotorWalk len78 cycle78 (fun _ => 0) x₀) i 16 = 8 := by
  decide +kernel

/-- **Every spell lasts exactly 8 periods** (post #3), for the rotor started at the beginning of
both cycles: `x_t = x₀` when `⌊t/8⌋` is even and the other state when it is odd. -/
theorem rotorWalk78_canonical (x₀ : Fin 2) (t : ℕ) :
    rotorWalk len78 cycle78 (fun _ => 0) x₀ t = if t / 8 % 2 = 0 then x₀ else otherState x₀ := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 16
    · exact rotorWalk78_lt_sixteen x₀ t ht
    · obtain ⟨t', rfl⟩ : ∃ t', t = 16 + t' := ⟨t - 16, by omega⟩
      obtain ⟨h16, hocc⟩ := rotorWalk78_sixteen x₀
      rw [rotorWalk_shift, h16]
      have hmod : rotorWalk len78 cycle78 (fun i => 0 +
          occCount (rotorWalk len78 cycle78 (fun _ => 0) x₀) i 16) x₀ =
          rotorWalk len78 cycle78 (fun _ => 0) x₀ :=
        rotorWalk_congr_mod len78 cycle78 (fun i => by
          rw [hocc i]
          simp only [len78, Nat.zero_add, Nat.mod_self, Nat.zero_mod]) x₀
      rw [hmod, ih t' (by omega)]
      have e : (16 + t') / 8 % 2 = t' / 8 % 2 := by omega
      rw [e]

/-- Offsets reduced modulo `8`. -/
def offsets78 (a b : ℕ) : Fin 2 → ℕ := fun i => if i = 0 then a else b

/-- From offsets `(a, b)`, the walk reaches its start with both rotors at the start of their
cycles at time `16 − a − b` (checked by evaluation for all `a, b < 8`). -/
theorem rotorWalk78_return :
    ∀ a < 8, ∀ b < 8, ∀ x₀ : Fin 2,
      rotorWalk len78 cycle78 (offsets78 a b) x₀ (16 - a - b) = x₀ ∧
      ∀ i : Fin 2, (offsets78 a b i +
        occCount (rotorWalk len78 cycle78 (offsets78 a b) x₀) i (16 - a - b)) % len78 i = 0 := by
  decide +kernel

/-- **For any starting points of the cycles** (e.g. the randomized rotor), the `7/8` rotor walk
is the canonical walk after some time `τ ≤ 16`, i.e. after the first spell in each state. -/
theorem rotorWalk78_eventually_canonical (θ : Fin 2 → ℕ) (x₀ : Fin 2) :
    ∃ τ ≤ 16, ∀ t, rotorWalk len78 cycle78 θ x₀ (τ + t) =
      if t / 8 % 2 = 0 then x₀ else otherState x₀ := by
  have hθ : rotorWalk len78 cycle78 θ x₀ =
      rotorWalk len78 cycle78 (offsets78 (θ 0 % 8) (θ 1 % 8)) x₀ :=
    rotorWalk_congr_mod len78 cycle78 (fun i => by
      fin_cases i
      · exact (Nat.mod_mod (θ 0) 8).symm
      · exact (Nat.mod_mod (θ 1) 8).symm) x₀
  obtain ⟨hret, hpos⟩ := rotorWalk78_return (θ 0 % 8) (Nat.mod_lt _ (by norm_num))
    (θ 1 % 8) (Nat.mod_lt _ (by norm_num)) x₀
  refine ⟨16 - θ 0 % 8 - θ 1 % 8, by omega, fun t => ?_⟩
  rw [hθ, rotorWalk_shift, hret]
  rw [rotorWalk_congr_mod len78 cycle78 (θ' := fun _ => 0) (fun i => by
    rw [hpos i, Nat.zero_mod]) x₀]
  exact rotorWalk78_canonical x₀ t

/-- The other state differs. -/
theorem otherState_ne (i : Fin 2) : otherState i ≠ i := by
  fin_cases i <;> decide

/-- **Spells of the `7/8` rotor walk**: for any offsets there is `τ ≤ 16` such that the spells
starting at `τ + 8k` last exactly `8` periods (`k = 0, 1, …`), and no other spell starts after
`τ`. -/
theorem runLength_rotorWalk78 (θ : Fin 2 → ℕ) (x₀ : Fin 2) :
    ∃ τ ≤ 16, (∀ k T, τ + 8 * k + 8 < T →
        runLength (rotorWalk len78 cycle78 θ x₀) (τ + 8 * k) T = 8) ∧
      ∀ t, τ < t → IsSpellStart (rotorWalk len78 cycle78 θ x₀) t → ∃ k, t = τ + 8 * k := by
  obtain ⟨τ, hτ, hx⟩ := rotorWalk78_eventually_canonical θ x₀
  set x := rotorWalk len78 cycle78 θ x₀
  refine ⟨τ, hτ, fun k T hT => ?_, fun t ht hs => ?_⟩
  · refine runLength_eq_of_exit hT (fun m hm => ?_) ?_
    · rw [add_assoc, hx, hx]
      have e : (8 * k + m) / 8 = 8 * k / 8 := by omega
      rw [e]
    · rw [add_assoc, hx, hx]
      by_cases h0 : 8 * k / 8 % 2 = 0
      · have h1 : ¬ ((8 * k + 8) / 8 % 2 = 0) := by omega
        simp only [h0, h1, ite_true, ite_false]
        exact otherState_ne x₀
      · have h1 : (8 * k + 8) / 8 % 2 = 0 := by omega
        simp only [h0, h1, ite_true, ite_false]
        exact (otherState_ne x₀).symm
  · rcases hs with h0 | hne
    · omega
    obtain ⟨s, rfl⟩ : ∃ s, t = τ + (s + 1) := ⟨t - τ - 1, by omega⟩
    have e1 : τ + (s + 1) - 1 = τ + s := by omega
    rw [e1, hx, hx] at hne
    refine ⟨(s + 1) / 8, ?_⟩
    by_contra hcon
    have hdiv : s / 8 = (s + 1) / 8 := by omega
    rw [hdiv] at hne
    exact hne rfl

/-- **The `7/8` rotor walk is not representative in spell lengths** (post #3): for any offsets,
at most `16` spells ever have a length other than `8` (counting the spells that end before
the horizon), whereas under the Markov chain a spell has length `8` with probability only
`(7/8)^7 (1/8) < 1/16`. -/
theorem rotor78_spells_not_geometric (θ : Fin 2 → ℕ) (x₀ : Fin 2) :
    (∀ T, ((range T).filter fun t => IsSpellStart (rotorWalk len78 cycle78 θ x₀) t ∧
        t + 8 < T ∧ runLength (rotorWalk len78 cycle78 θ x₀) t T ≠ 8).card ≤ 16) ∧
      geomPMF (7 / 8) 8 < 1 / 16 := by
  refine ⟨fun T => ?_, ?_⟩
  · obtain ⟨τ, hτ, hlen, hstart⟩ := runLength_rotorWalk78 θ x₀
    calc _ ≤ (range τ).card := by
          refine card_le_card fun t ht => ?_
          rw [mem_filter] at ht
          rw [mem_range]
          by_contra hτt
          rcases lt_or_eq_of_le (not_lt.1 hτt) with hlt | heq
          · obtain ⟨k, rfl⟩ := hstart t hlt ht.2.1
            exact ht.2.2.2 (hlen k T (by omega))
          · subst heq
            exact ht.2.2.2 (by simpa only [mul_zero, add_zero] using hlen 0 T (by omega))
      _ ≤ 16 := by rw [card_range]; exact hτ
  · simp only [geomPMF]
    norm_num

end RQMCMarkov.MarkovDriving
